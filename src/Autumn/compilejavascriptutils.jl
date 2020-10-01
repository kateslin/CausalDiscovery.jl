module CompileJavascriptUtils

using ..AExpressions
using MLStyle: @match

export compile_js, compileinit_js, compilestate_js, compilenext_js, compileprev_js, compilelibrary_js, compileharnesses_js, compilegenerators_js, compile_builtin

"Autumn Compile Error"
struct AutumnCompileError <: Exception
  msg
end
AutumnCompileError() = AutumnCompileError("")

# binary operators
binaryOperators = map(string, [:+, :-, :/, :*, :&, :|, :>=, :<=, :>, :<, :(==), :!=, :%, :&&])

# ----- Begin Exported Functions ----- #

function compile_js(expr::AExpr, data::Dict{String, Any}, parent::Union{AExpr, Nothing}=nothing)
  arr = [expr.head, expr.args...]
  print(expr)
  res = @match arr begin
    [:if, args...] => compileif(expr, data, parent)
    [:assign, args...] => compileassign(expr, data, parent)
    [:let, args...] => compilelet(expr, data, parent)
    [:typealias, args...] => compiletypealias(expr, data, parent)
    [:lambda, args...] => compilelambda(expr, data, parent)
    [:list, args...] => compilelist(expr, data, parent)
    [:call, args...] => compilecall(expr, data, parent)
    [:field, args...] => compilefield(expr, data, parent)
    [:object, args...] => compileobject(expr, data, parent)
    [:on, args...] => compileon(expr, data, parent)
    [:typedecl, args...] => compiletypedecl(expr, data, parent)
    [:external, args...] => compileexternal(expr, data, parent)
    [:case, args...] => compilecase(expr, data, parent)
    [args...] => throw(AutumnCompileError(string("Invalid AExpr Head: ", expr.head))) # if expr head is not one of the above, throw error
  end
end

function compile_js(expr::String, data::Dict{String, Any}, parent::Union{AExpr, Nothing}=nothing)
  return """\"$(expr)\""""
end

function compile_js(expr, data::Dict{String, Any}, parent::Union{AExpr, Nothing}=nothing)
  if expr in [:left, :right, :up, :down]
    "occurred($(string(expr)))"
  elseif expr == :clicked
    "occurred(click)"
  elseif expr == :Bool
    "bit"
  elseif expr == :String
    "char[STR_BND]"
  elseif expr == :Int
    "int"
  else
    string(expr)
  end
end

function compilestate_js(data)
  stateHistories = map(expr -> "this.$(compile_js(expr.args[1], data))History = {};",
  vcat(data["initnext"], data["lifted"]))
  GRID_SIZE = filter(x -> x.args[1] == :GRID_SIZE, data["lifted"])[1].args[2]
  """
  GRID_SIZE = $(GRID_SIZE);
  function State() {
    this.time = {};
    $(join(stateHistories, "\n"))
    this.clickHistory = {};
    this.leftHistory = {};
    this.rightHistory = {};
    this.upHistory = {};
    this.downHistory = {};
    this.scene = {};
  }
  """
end

function compileinit_js(data)
  objectInstances = filter(x -> data["varTypes"][x] in vcat(data["objects"], map(o -> [:List, o], data["objects"])),
                          collect(keys(data["varTypes"])))
  historyInitNextDeclarations = map(x -> "$(compile_js(x.args[1], data)) = $(compile_js(x.args[2].args[1], data));",
                                     data["initnext"])
  historyLiftedDeclarations = map(x -> "$(compile_js(x.args[1], data)) = $(compile_js(x.args[2], data));",
                           data["lifted"])
  historyInits = map(x -> "state.$(compile_js(x.args[1], data))History[0] = $(compile_js(x.args[1], data));",
                     vcat(data["initnext"], data["lifted"]))
  """
  state = State();
  function init() {
    $(join(historyInitNextDeclarations, "\n"))
    state.time = 0;
    $(join(historyInits, "\n"))
    state.clickHistory[0] = null;
    state.leftHistory[0] = null;
    state.rightHistory[0] = null;
    state.upHistory[0] = null;
    state.downHistory[0] = null;
    state.scene = new Scene(objects={$(join(map(obj -> data["varTypes"][obj] isa Array ? compile_js(obj, data) : "{$(compile_js(obj, data))}", objectInstances), ", "))}, background=\"transparent\");
    return state;
  }
  """
end

function compilenext_js(data)
  objectInstances = filter(x -> data["varTypes"][x] in vcat(data["objects"], map(o -> [:List, o], data["objects"])),
                           collect(keys(data["varTypes"])))
  currHistValues = map(x -> "$(compile_js(x.args[1], data)) = state.$(compile_js(x.args[1], data))History[state.time];",
                       vcat(data["initnext"], data["lifted"]))
  nextHistValues = map(x -> "state.$(compile_js(x.args[1], data))History[state.time] = $(compile_js(x.args[1], data));",
                       vcat(data["initnext"], data["lifted"]))
  onClauses = map(x -> """if ($(compile_js(x[1], data))) {
                            $(compile_js(x[2], data))
                          }""", data["on"])
  """
  function next(state, click, left, right, up, down) {
    $(join(currHistValues, "\n"))

    $(join(onClauses, "\n"))
    state.time = state.time + 1;
    $(join(nextHistValues, "\n"))
    state.clickHistory[state.time] = click;
    state.leftHistory[state.time] = left;
    state.rightHistory[state.time] = right;
    state.upHistory[state.time] = up;
    state.downHistory[state.time] = down;
    state.scene = new Scene(objects={$(join(map(obj -> data["varTypes"][obj] isa Array ? compile_js(obj, data) : "{$(compile_js(obj, data))}", objectInstances), ", "))}, background=\"transparent\");
    return state;
  }
  """
end

function compileprev_js(data)
  objectInstances = filter(x -> data["varTypes"][x] in vcat(data["objects"], map(o -> [:List, o], data["objects"])),
                           collect(keys(data["varTypes"])))
  prevFunctions = map(x -> """$(compile_js(data["varTypes"][x] in data["objects"] ?
                                  :Object
                                  :
                                  data["varTypes"][x] in map(x -> [:List, x], data["objects"]) ?
                                  [:List, :Object]
                                  :
                                  data["varTypes"][x], data)) $(compile_js(x, data))PrevN(State state, int n) {
                                return state.$(compile_js(x, data))History[state.time - n >= 0 ? state.time - n : 0];
                           }""", objectInstances)

  prevFunctionsNoArgs = map(x -> """$(compile_js(data["varTypes"][x] in data["objects"] ?
  :Object
  :
  data["varTypes"][x] in map(x -> [:List, x], data["objects"]) ?
  [:List, :Object]
  :
  data["varTypes"][x], data)) $(compile_js(x, data))Prev(State state) {
      return state.$(compile_js(x, data))History[state.time];
  }""", objectInstances)
  """
  $(join(prevFunctions, "\n"))
  $(join(prevFunctionsNoArgs, "\n"))
  """
end

function compilelibrary_js(data)

  """
  Object updateObjOrigin(Object object, Position origin) {
    $(join(map(x ->
              """
              if (object.type == \"$(compile_js(x, data))\") {
                return new $(compile_js(x, data))($(join(vcat("origin=origin", "alive=object.alive", "type=object.type", "render=object.render", map(y -> "$(y)=object.$(y)", data["customFields"][x])),", ")));
              }
              """, data["objects"]), "\n"))
  }
  Object updateObjAlive(Object object, bit alive) {
    $(join(map(x ->
              """
              if (object.type == \"$(compile_js(x, data))\") {
                return new $(compile_js(x, data))($(join(vcat("origin=object.origin", "alive=alive", "type=object.type", "render=object.render", map(y -> "$(y)=object.$(y)", data["customFields"][x])), ", ")));
              }
              """, data["objects"]), "\n"))
  }
  Object updateObjRender(Object object, Cell[ARR_BND] render) {
    $(join(map(x ->
              """
              if (object.type == \"$(compile_js(x, data))\") {
                return new $(compile_js(x, data))($(join(vcat("origin=object.origin", "alive=object.alive", "type=object.type", "render=render", map(y -> "$(y)=object.$(y)", data["customFields"][x])),", ")));
              }
              """, data["objects"]), "\n"))
  }
  $(library)
  """
end
function compile_builtin()
  """class Position {
  constructor(x, y){
    this.x = x;
    this.y = y;
  }
}
class Cell{
  constructor(position, color){
    this.position = position;
    this.color = color;
  }
}
"""
end

#=
observations: list of ((Click, Left, Right, Up, Down), [list of cells])
=#

function compileharnesses_js(data)

end

function compilegenerators_js(data)

end

# ----- End Exported Functions -----#

function compileif(expr, data, parent)
  if expr.args[2] isa AExpr && (expr.args[2].head in [:assign, :let])
    statement = (
      """if ($(compile_js(expr.args[1], data))) {
      $(compile_js(expr.args[2], data))
    } else {
      $(compile_js(expr.args[3], data))
    }""")
    return statement
  else
    return "$(compile_js(expr.args[1], data)) ? $(compile_js(expr.args[2], data)) : $(compile_js(expr.args[3], data))"
  end
end

function compileassign(expr, data, parent)
  # get type
  type = typeof(expr.args[1])
  # type = data["types"][expr.args[1]]
  if (typeof(expr.args[2]) == AExpr && expr.args[2].head == :fn)
    args = map(x -> compile_js(x, data), expr.args[2].args[1].args) # function args
    # argtypes = map(x -> compile_js(x in data["objects"] ?
    #                     :Object
    #                     :
    #                     (x in data["objects"]) ?
    #                     [:List, :Object]
    #                     :
    #                     x, data), type.args[1:(end-1)]) # function arg types
    # tuples = [(args[i], argtypes[i]) for i in [1:length(args);]]
    # typedargs = map(x -> "$(x[2]) $(x[1])", tuples)
    # returntype = compile_js(type.args[end] in data["objects"] ?
    #                         :Object
    #                         :
    #                         (type.args[end] in data["objects"]) ?
    #                         [:List, :Object]
    #                         :
    #                         type.args[end], data)
    """
     $(compile_js(expr.args[1], data))($(join(args, ", "))) {
      $(compile_js(expr.args[2].args[2], data));
    }
    """
  else # handle non-function assignments
    # handle global assignments
    if parent !== nothing && (parent.head == :program)
      if (typeof(expr.args[2]) == AExpr && expr.args[2].head == :initnext)
        push!(data["initnext"], expr)
      else
        # push!(data["varTypes"], expr.args[1] => compile_js(expr.args[2], data))
        print(expr)
        print(expr.args)
        push!(data["lifted"], expr)
      end
      ""
    # handle non-global assignments
    else
      push!(data["objects"], expr.args[1])
      "$(compile_js(expr.args[1], data)) = $(compile_js(expr.args[2], data));"
    end
  end
end

function compiletypedecl(expr, data, parent)
  push!(data["varTypes"], expr.args[1] => expr.args[2])
  compile_js(expr.args[1], data)
end

function compilelet(expr, data, parent)
  assignments = map(x -> compile_js(x, data), expr.args)
  let_statements = ["let " * string(x) for x in assignments[1:end-1]]
  output = join(vcat(let_statements, string("return ", assignments[end], ";")), "\n")
  return output
end

function compilefieldalias(expr, data, parent)
  obj = compile_js(expr.args[1], data)
  fieldname = compile_js(expr.args[2], data)
  "$(obj).$(fieldname)"
end

function compiletypealias(expr, data, parent)
  name = string(expr.args[1]);
  constructor = map(field -> "$(compile_js(field.args[1], data))", expr.args[2].args)
  fields = map(field -> "this.$(compile_js(field.args[1], data)) = $(compile_js(field.args[1], data));",
           expr.args[2].args)
  print(expr.args[2])
  print("\n")
  push!(data["varTypes"], expr.args[1] => name)
  """
  class $(name) {
    constructor ($(join(constructor, ", "))){
    $(join(fields, "\n"))
    }
  }
  """
end

function compilelambda(expr, data, parent)
  "$(compile_js(expr.args[1], data)) => $(compile_js(expr.args[2], data))"
end

function compilelist(expr, data, parent)
  "[$(join(map(x -> compile_js(x, data), expr.args), ", "))]"
end

# TODO: Confirm this makes sense for all test cases
function compilecall(expr, data, parent)
  name = compile_js(expr.args[1], data);

  args = map(x -> compile_js(x, data), expr.args[2:end]);
  objectNames = map(x -> compile_js(x, data), data["objects"])
  # print("OBJECT NAMES: ", objectNames, "\n")
  if name == "clicked"
    "clicked(click, $(join(args, ", ")))"
  elseif name == "Position"
    "new $(name)(x=$(args[1]), y=$(args[2]))"
  elseif name == "Cell"
    if length(args) == 2
      "new $(name)(position=$(args[1]), color=$(args[2]))"
    elseif length(args) == 3
      "new $(name)(position=new Position(x=$(args[1]), y=$(args[2])), color=$(args[3]))"
    end
  elseif name in objectNames
    "$(lowercase(name[1]))$(name[2:end])($(join(args, "\n")))"
  elseif name == "object"
    "$(compileobject(expr, data, parent))"
  elseif !(name in binaryOperators) && name != "prev"
    print("name not in binaryops and is not prev\n")
    "$(name)($(join(args, ", ")))"
  elseif name == "prev"
    "$(compile_js(expr.args[2], data))Prev($(join(["state", map(x -> compile_js(x, data), expr.args[3:end])...], ", ")))"
  elseif name in binaryOperators
    "$(compile_js(expr.args[2], data)) $(name) $(compile_js(expr.args[3], data))"
  elseif name != "=="
    print("Going into other\n")
    "$(name)($(compile_js(expr.args[2], data)), $(compile_js(expr.args[3], data)))"
  else
    "$(compile_js(expr.args[2], data)) == $(compile_js(expr.args[3], data))"
  end
end

function compilefield(expr, data, parent)
  obj = compile_js(expr.args[1], data)
  fieldname = compile_js(expr.args[2], data)
  "$(obj).$(fieldname)"
end

# TODO: Figure out how to deal with typedecl since there's not typedecl in javascript
function compileobject(expr, data, parent)
  name = String.(expr.args[2])
  custom_fields = map(field ->
                      "$(compile_js(field.args[1], data))",
                      filter(x -> (typeof(x) == AExpr && x.head == :typedecl), expr.args[3:end]))
  custom_field_names = map(field -> "$(compile_js(field.args[1], data))",
                           filter(x -> (x isa AExpr && x.head == :typedecl), expr.args[3:end]))
  data["customFields"][expr.args[1]] = custom_field_names;
  custom_field_assgns = map(field -> "$(compile_js(field.args[1], data))=$(compile_js(field.args[1], data))",
                            filter(x -> (typeof(x) == AExpr && x.head == :typedecl), expr.args[3:end]))
  rendering = compile_js(filter(x -> (typeof(x) != AExpr) || (x.head != :typedecl), expr.args[3:end])[1], data)
  renderingIsList = filter(x -> (typeof(x) != AExpr) || (x.head != :typedecl), expr.args[3:end])[1].head == :list
  rendering = renderingIsList ? rendering : "[$(rendering)]"

  # compile updateObj functions, and move/rotate/nextWater/nextLiquid
  update_obj_fields = map(x -> [compile_js(x.args[2], data), compile_js(x.args[1], data)],
                               filter(x -> (typeof(x) == AExpr && x.head == :typedecl), expr.args[3:end]))
  update_obj_field_assigns = map(x -> "$(x[2])=object.$(x[2])", update_obj_fields)
  update_obj_functions = map(x -> """
                                  function updateObj$(name)$(string(uppercase(x[2][1]), x[2][2:end]))(object, $(x[2])) {
                                    return new $(name)($(join(vcat(string(x[2]), filter(y -> split(y, "=")[1] != x[2], update_obj_field_assigns)), ", ")), object.origin);
                                  }
                                  """, update_obj_fields)
  """
  class $(name){
    constructor($(length(custom_fields) == 0 ? "origin" : join(custom_fields, ", ") * ", origin")){
    $(join(map(x -> string("this.", x, " = ", x, ";"), custom_field_names), "\n"))$(length(custom_field_names) == 1 ? "\n" : "")this.origin = origin;
    this.type = $(name);
    this.alive = true;
    this.render = $(rendering);

    }
  }

  function $(string(lowercase(name[1]), name[2:end]))($(join([custom_fields..., "origin"], ", "))) {
    return new $(name)($(join([custom_fields..., "origin"], ", ")));
  }

  $(join(update_obj_functions, "\n"))
  """
end

function compileon(expr, data, parent)
  event = expr.args[1]
  response = expr.args[2]
  onData = (event, response)
  push!(data["on"], onData)
  "got here"
end

function compileexternal(expr, data, parent)
  print(data)
  if !(expr.args[1] in data["external"])
    push!(data["external"], expr.args[1])
  end
  compiletypedecl(expr.args[1], data, expr)
end

end
