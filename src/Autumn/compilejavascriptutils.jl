module CompileJavascriptUtils

using ..AExpressions
using MLStyle: @match

export compile_js, compileinit_js, compilestate_js, compilenext_js, compileprev_js, compilelibrary_js, compileharnesses_js, compilegenerators_js, compilebuiltin_js

"Autumn Compile Error"
struct AutumnCompileError <: Exception
  msg
end
AutumnCompileError() = AutumnCompileError("")

# binary operators
binaryOperators = map(string, [:+, :-, :/, :*, :&, :|, :>=, :<=, :>, :<, :(==), :!=, :%, :&&])

# ----- Begin Exported Functions ----- #

function compile_js(expr::AExpr, data::Dict{String,Any}, parent::Union{AExpr,Nothing}=nothing)
  arr = [expr.head, expr.args...]
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

function compile_js(expr::String, data::Dict{String,Any}, parent::Union{AExpr,Nothing}=nothing)
  return """\"$(expr)\""""
end

function compile_js(expr, data::Dict{String,Any}, parent::Union{AExpr,Nothing}=nothing)
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
    $(join(stateHistories, "\n  "))
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
    $(join(historyInits, "\n  "))
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
    $(join(currHistValues, "\n  "))

    $(join(onClauses, "\n"))
    state.time = state.time + 1;
    $(join(nextHistValues, "\n  "))
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
                return new $(compile_js(x, data))($(join(vcat("origin=origin", "alive=object.alive", "type=object.type", "render=object.render", map(y -> "$(y)=object.$(y)", data["customFields"][x])), ", ")));
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
                return new $(compile_js(x, data))($(join(vcat("origin=object.origin", "alive=object.alive", "type=object.type", "render=render", map(y -> "$(y)=object.$(y)", data["customFields"][x])), ", ")));
              }
              """, data["objects"]), "\n"))
  }
  $(library)
  """
end
# function compile_builtin()
#   """class Position {
#   constructor(x, y){
#     this.x = x;
#     this.y = y;
#   }
# }
# class Cell{
#   constructor(position, color){
#     this.position = position;
#     this.color = color;
#   }
# }
# """
# end

#=
observations: list of ((Click, Left, Right, Up, Down), [list of cells]) =#

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
  let_statements = ["let " * string(x) for x in assignments[1:end - 1]]
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
    "$(name)($(join(args, ", ")))"
  elseif name == "prev"
    "$(compile_js(expr.args[2], data))Prev($(join(["state", map(x -> compile_js(x, data), expr.args[3:end])...], ", ")))"
  elseif name in binaryOperators
    "$(compile_js(expr.args[2], data)) $(name) $(compile_js(expr.args[3], data))"
  elseif name != "=="
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
  print("\n reached compileon!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! \n")
  event = expr.args[1]
  response = expr.args[2]
  onData = (event, response)
  push!(data["on"], onData)
end

function compileexternal(expr, data, parent)
  if !(expr.args[1] in data["external"])
    push!(data["external"], expr.args[1])
  end
  compiletypedecl(expr.args[1], data, expr)
end

function compilebuiltin_js()
  occurredFunction = builtInDict["occurred"]
  uniformChoiceFunction = builtInDict["uniformChoice"]
  uniformChoiceFunction2 = builtInDict["uniformChoice2"]
  minFunction = builtInDict["min"]
  clickType = builtInDict["clickType"]
  rangeFunction = builtInDict["range"]
  utilFunctions = builtInDict["utils"]
  [occurredFunction, uniformChoiceFunction, uniformChoiceFunction2, minFunction, clickType, rangeFunction, utilFunctions]
end

const builtInDict = Dict([
"occurred"        =>  "function occurred(click){
  return click !== null;
}
",
"uniformChoice"   =>  "function uniformChoice(freePositions){
  return freePositions[Math.floor(Math.random()*freePositions.length)];
}
",
"uniformChoice2"   =>  "function uniformChoice2(freePositions, n){
  newPositions = [];
  used = [];
  if (n > newPositions.size()){
    throw 'too many positions requested!';
  }
  for (i=0; i<n; i++){
    while (true){
      index = Math.floor(Math.random()*freePositions.length);
      if (! used.contains(index)){
        newPositions.add(freePositions[index]);
        used.add(index);
        break;
      }
    }
  }
  return freePositions
}
",
"min"              => "function min(arr) {
  return Math.min(...arr)
}
",
"clickType"       =>  "class Click{
  constructor(x, y){
    this.x = x;
    this.y = y;
  }
}
",
"range"           => "function range(start, stop){
  let arr = [];
  for(let i = start; i <= stop; i += 1){
     arr.push(i);
  }
  return arr;
}
",
"utils"           =>
                        # abstract type Object end
                        # abstract type KeyPress end
                        #
                        # struct Left <: KeyPress end
                        # struct Right <: KeyPress end
                        # struct Up <: KeyPress end
                        # struct Down <: KeyPress end
    "
    class Position {
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
    #javascript is not polymorphic
    Cell(position::Position, color::String) = Cell(position, color, 0.8)
    Cell(x::Int, y::Int, color::String) = Cell(Position(floor(Int, x), floor(Int, y)), color, 0.8)
    Cell(x::Int, y::Int, color::String, opacity::Float64) = Cell(Position(floor(Int, x), floor(Int, y)), color, opacity)

    class Scene{
      constructor(objects, background){
        this.objects = objects;
        this.background = background;
      }
    }

    function objClicked(click, objects){
      objects.filter(obj => clicked(click, obj))[1];
      }

    function filter_fallback(obj){
        return true;
      }


    function adjPositions(position){
        return [Position(position.x, position.y + 1), Position(position.x, position.y - 1), Position(position.x + 1, position.y), Position(position.x - 1, position.y)].filter(isWithinBounds);
      }

    function rotateNoCollision(object){
      return (isWithinBounds(rotate(object)) && isFree(rotate(object), object)) ? rotate(object) : object;
      }

    function randomPositions(GRID_SIZE, n){
      nums = uniformChoice([0:(GRID_SIZE * GRID_SIZE - 1)], n);
      return nums.map(num => Position(num % GRID_SIZE, floor(num/GRID_SIZE)));
      }

    function updateOrigin(object, new_origin){
      new_object = JSON.parse(JSON.stringify(object));
      new_object.origin = new_origin;
      return new_object;
      }

    function updateAlive(object, new_alive){
      new_object = JSON.parse(JSON.stringify(object));
      new_object.alive = new_alive;
      return new_object;
      }"
##################################################################################################################
#     #polymorphic
#     Scene(objects::AbstractArray) = Scene(objects, "#ffffff00")
#
#     #polymorphic
#     function render(scene::Scene)::Array{Cell}
#       vcat(map(obj -> render(obj), filter(obj -> obj.alive && !obj.hidden, scene.objects))...)
#     end
#
#     function render(obj::Object)::Array{Cell}
#       map(cell -> Cell(move(cell.position, obj.origin), cell.color), obj.render)
#     end
#
#     #polymorphic
#     function isWithinBounds(obj)
#       length(filter(cell -> !isWithinBounds(cell.position), render(obj))) == 0
#     end
#
#     function isWithinBounds(position::Position)::Bool
#       (position.x >= 0) && (position.x < state.GRID_SIZEHistory[0]) && (position.y >= 0) && (position.y < state.GRID_SIZEHistory[0])
#     end
#
#     #polymorphic
#     function clicked(click::Union{Click, Nothing}, object::Object)::Bool
#       if click == nothing
#         false
#       else
#         GRID_SIZE = state.GRID_SIZEHistory[0]
#         nums = map(cell -> GRID_SIZE*cell.position.y + cell.position.x, render(object))
#         (GRID_SIZE * click.y + click.x) in nums
#       end
#     end
#
#     function clicked(click::Union{Click, Nothing}, objects::AbstractArray)
#       # println("LOOK AT ME")
#       # println(reduce(&, map(obj -> clicked(click, obj), objects)))
#       reduce(|, map(obj -> clicked(click, obj), objects))
#     end
#
#     function clicked(click::Union{Click, Nothing}, x::Int, y::Int)::Bool
#       if click == nothing
#         false
#       else
#         click.x == x && click.y == y
#       end
#     end
#
#     function clicked(click::Union{Click, Nothing}, pos::Position)::Bool
#       if click == nothing
#         false
#       else
#         click.x == pos.x && click.y == pos.y
#       end
#     end
#
#     #_______________________________________________________
#
#     #polymorphic
#     function intersects(obj1::Object, obj2::Object)::Bool
#       nums1 = map(cell -> state.GRID_SIZEHistory[0]*cell.position.y + cell.position.x, render(obj1))
#       nums2 = map(cell -> state.GRID_SIZEHistory[0]*cell.position.y + cell.position.x, render(obj2))
#       length(intersect(nums1, nums2)) != 0
#     end
#
#     function intersects(obj1::Object, obj2::Array{<:Object})::Bool
#       nums1 = map(cell -> state.GRID_SIZEHistory[0]*cell.position.y + cell.position.x, render(obj1))
#       nums2 = map(cell -> state.GRID_SIZEHistory[0]*cell.position.y + cell.position.x, vcat(map(render, obj2)...))
#       length(intersect(nums1, nums2)) != 0
#     end
#
#     function intersects(list1, list2)::Bool
#       length(intersect(list1, list2)) != 0
#     end
#
#     function intersects(object::Object)::Bool
#       objects = state.scene.objects
#       intersects(object, objects)
#     end
#     #_____________________________________________
#
#
#     function addObj(list::Array{<:Object}, obj::Object)
#       new_list = vcat(list, obj)
#       new_list
#     end
#
#     function addObj(list::Array{<:Object}, objs::Array{<:Object})
#       new_list = vcat(list, objs)
#       new_list
#     end
#
#     function removeObj(list::Array{<:Object}, obj::Object)
#       filter(x -> x.id != obj.id, list)
#     end
#
#     function removeObj(list::Array{<:Object}, fn)
#       orig_list = filter(obj -> !fn(obj), list)
#     end
#
#     function removeObj(obj::Object)
#       obj.alive = false
#       deepcopy(obj)
#     end
#
#     function updateObj(obj::Object, field::String, value)
#       fields = fieldnames(typeof(obj))
#       custom_fields = fields[5:end-1]
#       origin_field = (fields[2],)
#
#       constructor_fields = (custom_fields..., origin_field...)
#       constructor_values = map(x -> x == Symbol(field) ? value : getproperty(obj, x), constructor_fields)
#
#       new_obj = typeof(obj)(constructor_values...)
#       setproperty!(new_obj, :id, obj.id)
#       setproperty!(new_obj, :alive, obj.alive)
#       setproperty!(new_obj, :hidden, obj.hidden)
#
#       setproperty!(new_obj, Symbol(field), value)
#       new_obj
#     end
#
#
#     function updateObj(list::Array{<:Object}, map_fn, filter_fn=filter_fallback)
#       orig_list = filter(obj -> !filter_fn(obj), list)
#       filtered_list = filter(filter_fn, list)
#       new_filtered_list = map(map_fn, filtered_list)
#       vcat(orig_list, new_filtered_list)
#     end
#
#
#     function isFree(position::Position)::Bool
#       length(filter(cell -> cell.position.x == position.x && cell.position.y == position.y, render(state.scene))) == 0
#     end
#
#     function isFree(click::Union{Click, Nothing})::Bool
#       if click == nothing
#         false
#       else
#         isFree(Position(click.x, click.y))
#       end
#     end
#
#     function unitVector(position1::Position, position2::Position)::Position
#       deltaX = position2.x - position1.x
#       deltaY = position2.y - position1.y
#       if (floor(Int, abs(sign(deltaX))) == 1 && floor(Int, abs(sign(deltaY))) == 1)
#         uniformChoice([Position(sign(deltaX), 0), Position(0, sign(deltaY))])
#       else
#         Position(sign(deltaX), sign(deltaY))
#       end
#     end
#
#     function unitVector(object1::Object, object2::Object)::Position
#       position1 = object1.origin
#       position2 = object2.origin
#       unitVector(position1, position2)
#     end
#
#     function unitVector(object::Object, position::Position)::Position
#       unitVector(object.origin, position)
#     end
#
#     function unitVector(position::Position, object::Object)::Position
#       unitVector(position, object.origin)
#     end
#
#     function unitVector(position::Position)::Position
#       unitVector(Position(0,0), position)
#     end
#
#     function displacement(position1::Position, position2::Position)::Position
#       Position(floor(Int, position2.x - position1.x), floor(Int, position2.y - position1.y))
#     end
#
#     function displacement(cell1::Cell, cell2::Cell)::Position
#       displacement(cell1.position, cell2.position)
#     end
#
#     function adjacent(position1::Position, position2::Position):Bool
#       displacement(position1, position2) in [Position(0,1), Position(1, 0), Position(0, -1), Position(-1, 0)]
#     end
#
#     function adjacent(cell1::Cell, cell2::Cell)::Bool
#       adjacent(cell1.position, cell2.position)
#     end
#
#     function adjacent(cell::Cell, cells::Array{Cell})
#       length(filter(x -> adjacent(cell, x), cells)) != 0
#     end
#
#     function rotate(object::Object)::Object
#       new_object = deepcopy(object)
#       new_object.render = map(x -> Cell(rotate(x.position), x.color), new_object.render)
#       new_object
#     end
#
#     function rotate(position::Position)::Position
#       Position(-position.y, position.x)
#      end
#
#
#     function move(position1::Position, position2::Position)
#       Position(position1.x + position2.x, position1.y + position2.y)
#     end
#
#     function move(position::Position, cell::Cell)
#       Position(position.x + cell.position.x, position.y + cell.position.y)
#     end
#
#     function move(cell::Cell, position::Position)
#       Position(position.x + cell.position.x, position.y + cell.position.y)
#     end
#
#     function move(object::Object, position::Position)
#       new_object = deepcopy(object)
#       new_object.origin = move(object.origin, position)
#       new_object
#     end
#
#     function move(object::Object, x::Int, y::Int)::Object
#       move(object, Position(x, y))
#     end
#
#     function moveNoCollision(object::Object, position::Position)::Object
#       (isWithinBounds(move(object, position)) && isFree(move(object, position.x, position.y), object)) ? move(object, position.x, position.y) : object
#     end
#
#     function moveNoCollision(object::Object, x::Int, y::Int)
#       (isWithinBounds(move(object, x, y)) && isFree(move(object, x, y), object)) ? move(object, x, y) : object
#     end
#
#     function moveWrap(object::Object, position::Position)::Object
#       new_object = deepcopy(object)
#       new_object.position = moveWrap(object.origin, position.x, position.y)
#       new_object
#     end
#
#     function moveWrap(cell::Cell, position::Position)
#       moveWrap(cell.position, position.x, position.y)
#     end
#
#     function moveWrap(position::Position, cell::Cell)
#       moveWrap(cell.position, position)
#     end
#
#     function moveWrap(object::Object, x::Int, y::Int)::Object
#       new_object = deepcopy(object)
#       new_object.position = moveWrap(object.origin, x, y)
#       new_object
#     end
#
#     function moveWrap(position1::Position, position2::Position)::Position
#       moveWrap(position1, position2.x, position2.y)
#     end
#
#     function moveWrap(position::Position, x::Int, y::Int)::Position
#       GRID_SIZE = state.GRID_SIZEHistory[0]
#       # println("hello")
#       # println(Position((position.x + x + GRID_SIZE) % GRID_SIZE, (position.y + y + GRID_SIZE) % GRID_SIZE))
#       Position((position.x + x + GRID_SIZE) % GRID_SIZE, (position.y + y + GRID_SIZE) % GRID_SIZE)
#     end
#
#
#     function distance(position1::Position, position2::Position)::Int
#       abs(position1.x - position2.x) + abs(position1.y - position2.y)
#     end
#
#     function distance(object1::Object, object2::Object)::Int
#       position1 = object1.origin
#       position2 = object2.origin
#       distance(position1, position2)
#     end
#
#     function distance(object::Object, position::Position)::Int
#       distance(object.origin, position)
#     end
#
#     function distance(position::Position, object::Object)::Int
#       distance(object.origin, position)
#     end
#
#     function closest(object::Object, type::DataType)::Position
#       objects_of_type = filter(obj -> (obj isa type) && (obj.alive), state.scene.objects)
#       if length(objects_of_type) == 0
#         object.origin
#       else
#         min_distance = min(map(obj -> distance(object, obj), objects_of_type))
#         filter(obj -> distance(object, obj) == min_distance, objects_of_type)[1].origin
#       end
#     end
#
#     function mapPositions(constructor, GRID_SIZE::Int, filterFunction, args...)::Union{Object, Array{<:Object}}
#       map(pos -> constructor(args..., pos), filter(filterFunction, allPositions(GRID_SIZE)))
#     end
#
#     function allPositions(GRID_SIZE::Int)
#       nums = [0:(GRID_SIZE * GRID_SIZE - 1);]
#       map(num -> Position(num % GRID_SIZE, floor(Int, num / GRID_SIZE)), nums)
#     end
#
#
#     function nextLiquid(object::Object)::Object
#       # println("nextLiquid")
#       GRID_SIZE = state.GRID_SIZEHistory[0]
#       new_object = deepcopy(object)
#       if object.origin.y != GRID_SIZE - 1 && isFree(move(object.origin, Position(0, 1)))
#         new_object.origin = move(object.origin, Position(0, 1))
#       else
#         leftHoles = filter(pos -> (pos.y == object.origin.y + 1)
#                                    && (pos.x < object.origin.x)
#                                    && isFree(pos), allPositions())
#         rightHoles = filter(pos -> (pos.y == object.origin.y + 1)
#                                    && (pos.x > object.origin.x)
#                                    && isFree(pos), allPositions())
#         if (length(leftHoles) != 0) || (length(rightHoles) != 0)
#           if (length(leftHoles) == 0)
#             closestHole = closest(object, rightHoles)
#             if isFree(move(closestHole, Position(0, -1)), move(object.origin, Position(1, 0)))
#               new_object.origin = move(object.origin, unitVector(object, move(closestHole, Position(0, -1))))
#             end
#           elseif (length(rightHoles) == 0)
#             closestHole = closest(object, leftHoles)
#             if isFree(move(closestHole, Position(0, -1)), move(object.origin, Position(-1, 0)))
#               new_object.origin = move(object.origin, unitVector(object, move(closestHole, Position(0, -1))))
#             end
#           else
#             closestLeftHole = closest(object, leftHoles)
#             closestRightHole = closest(object, rightHoles)
#             if distance(object.origin, closestLeftHole) > distance(object.origin, closestRightHole)
#               if isFree(move(object.origin, Position(1, 0)), move(closestRightHole, Position(0, -1)))
#                 new_object.origin = move(object.origin, unitVector(new_object, move(closestRightHole, Position(0, -1))))
#               elseif isFree(move(closestLeftHole, Position(0, -1)), move(object.origin, Position(-1, 0)))
#                 new_object.origin = move(object.origin, unitVector(new_object, move(closestLeftHole, Position(0, -1))))
#               end
#             else
#               if isFree(move(closestLeftHole, Position(0, -1)), move(object.origin, Position(-1, 0)))
#                 new_object.origin = move(object.origin, unitVector(new_object, move(closestLeftHole, Position(0, -1))))
#               elseif isFree(move(object.origin, Position(1, 0)), move(closestRightHole, Position(0, -1)))
#                 new_object.origin = move(object.origin, unitVector(new_object, move(closestRightHole, Position(0, -1))))
#               end
#             end
#           end
#         end
#       end
#       new_object
#     end
#
#     function nextSolid(object::Object)::Object
#       # println("nextSolid")
#       GRID_SIZE = state.GRID_SIZEHistory[0]
#       new_object = deepcopy(object)
#       if (isWithinBounds(move(object, Position(0, 1))) && reduce(&, map(x -> isFree(x, object), map(cell -> move(cell.position, Position(0, 1)), render(object)))))
#         new_object.origin = move(object.origin, Position(0, 1))
#       end
#       new_object
#     end
#
#     function closest(object::Object, positions::Array{Position})::Position
#       closestDistance = sort(map(pos -> distance(pos, object.origin), positions))[1]
#       closest = filter(pos -> distance(pos, object.origin) == closestDistance, positions)[1]
#       closest
#     end
#
#     function isFree(start::Position, stop::Position)::Bool
#       GRID_SIZE = state.GRID_SIZEHistory[0]
#       nums = [(GRID_SIZE * start.y + start.x):(GRID_SIZE * stop.y + stop.x);]
#       reduce(&, map(num -> isFree(Position(num % GRID_SIZE, floor(Int, num / GRID_SIZE))), nums))
#     end
#
#     function isFree(start::Position, stop::Position, object::Object)::Bool
#       GRID_SIZE = state.GRID_SIZEHistory[0]
#       nums = [(GRID_SIZE * start.y + start.x):(GRID_SIZE * stop.y + stop.x);]
#       reduce(&, map(num -> isFree(Position(num % GRID_SIZE, floor(Int, num / GRID_SIZE)), object), nums))
#     end
#
#     function isFree(position::Position, object::Object)
#       length(filter(cell -> cell.position.x == position.x && cell.position.y == position.y,
#       filter(x -> !(x in render(object)), render(state.scene)))) == 0
#     end
#
#     function isFree(object::Object, orig_object::Object)::Bool
#       reduce(&, map(x -> isFree(x, orig_object), map(cell -> cell.position, render(object))))
#     end
#
#     function allPositions()
#       GRID_SIZE = state.GRID_SIZEHistory[0]
#       nums = [1:GRID_SIZE*GRID_SIZE - 1;]
#       map(num -> Position(num % GRID_SIZE, floor(Int, num / GRID_SIZE)), nums)
#     end
#
# end

])

end
