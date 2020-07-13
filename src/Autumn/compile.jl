"Compilation to Julia (and other targets, if you want)"
module Compile

using ..AExpressions, ..CompileUtils
import MacroTools: striplines

export compiletojulia, runprogram

"compile `aexpr` into Expr"
function compiletojulia(aexpr::AExpr)::Expr

  data = Dict([("historyVars" => []),
               ("externalVars" => []),
               ("initnextVars" => []),
               ("liftedVars" => []),
               ("types" => Dict())])

  if (aexpr.head == :program)
    # handle AExpression lines
    lines = filter(x -> x !== :(), map(arg -> compile(arg, data, aexpr), aexpr.args))
    
    # construct STATE struct and initialize state::STATE
    stateStruct = compilestatestruct(data)
    initStateStruct = compileinitstate(data)
    
    # handle init, next, prev, and built-in functions
    initnextFunctions = compileinitnext(data)
    prevFunctions = compileprevfuncs(data)
    builtinFunctions = compilebuiltin()

    # remove empty lines
    lines = filter(x -> x != :(), 
            vcat(builtinFunctions, lines, stateStruct, initStateStruct, prevFunctions, initnextFunctions))

    # construct module
    expr = quote
      module CompiledProgram
        export init, next
        import Base.min
        using Distributions
        using MLStyle: @match 
        $(lines...)
      end
    end  
    expr.head = :toplevel
    striplines(expr) 
  else
    throw(AutumnCompileError("AExpr Head != :program"))
  end
end

"Run `prog` for finite number of time steps"
function runprogram(prog::Expr, n::Int)
  mod = eval(prog)
  state = mod.init(mod.Click(5, 5))

  for i in 1:n
    externals = [nothing, mod.Click(rand([1:10;]), rand([1:10;]))]
    state = mod.next(mod.next(state, externals[rand(Categorical([0.7, 0.3]))]))
  end
  state
end

end