using Test
using CausalDiscovery

function construct_data()
  Dict([("external" => []),
        ("initnext" => []),
        ("lifted" => []),
        ("types" => Dict()),
        ("on" => []),
        ("objects" => []),
        ("customFields" =>  Dict())])
end

mod = nothing

function isinferred(f, args...; allow = Union{})
  ret = f(args...)
  inftypes = Base.return_types(f, Base.typesof(args...))
  rettype = ret isa Type ? Type{ret} : typeof(ret)
  rettype <: allow || rettype == Test.typesubtract(inftypes[1], allow)
end


function test_compile_if()
  data = construct_data()
  aexpr = au"""(if (== x 3) then (= y 4) else (= y 5))"""
  @test string(compile_js(aexpr, data)) == "if (x == 3) {\n  y = 4;\n} else {\n  y = 5;\n}"
end


function test_compile_assign()
  data = construct_data()
  aexpr = au"""(= x 3)"""
  @test compile_js(aexpr, data) == "x = 3;"
end

function test_compile_external()
  data = construct_data()
  aexpr = au"""(external (: click Click))"""
  @test compile_js(aexpr, data) == :()
end

function test_compile_let()
  data = construct_data()
  aexpr = au"""(let ((= y 3) (= x y)) x)"""

  @test compile_js(aexpr, data) == "let y = 3;\nlet x = y;\nreturn x;"
end

function test_compile_list()
  data = construct_data()
  aexpr = au"""(list 1 2 3 4 5)"""
  @test compile_js(aexpr, data) == "[1, 2, 3, 4, 5]"
end

function test_compile_call()
  data = construct_data()
  aexpr = au"""(f 1 2 3) """
  @test compile_js(aexpr, data) == "f(1, 2, 3)"

  data = construct_data()
  aexpr = au"""(== 1 2)"""
  @test compile_js(aexpr, data) == "1 == 2"

  data = construct_data()
  aexpr = au"""(+ 1 2)"""
  @test compile_js(aexpr, data) == "1 + 2"

end

function test_compile_field()
  data = construct_data()
  aexpr = au"""(.. position x)"""
  @test compile_js(aexpr, data) == "position.x"
end

#seems like the issue is with (+ x 1) not being compiled correctly
#lambda part works
function test_compile_lambda()
  data = construct_data()
  aexpr = au"""(--> x (+ x 1))"""
  @test compile_js(aexpr, data) == "x => x + 1"
end

#
function test_compile_typealias()
  data = construct_data()
  aexpr = au"""(type alias Position ((: x Int) (: y Int)))"""
  @test compile_js(aexpr, data) == """class Position {
  constructor (x, y){
  this.x = x;
this.y = y;
  }
}
"""
end

function test_compile_object()
  data = construct_data()
  aexpr = au"""(object Food (Cell 0 0 "red"))"""
  expected = """class Food{
  constructor(origin){
  this.origin = origin;
  this.type = Food;
  this.alive = true;
  this.render = {new Cell(position=new Position(x=0, y=0), color="red")};

  }
}

function food(origin) {
  return new Food(origin);
}


"""
  @test expected == compile_js(aexpr, data)
  data = construct_data()
  aexpr = au"""(object Light (: on Bool) (Cell 0 0 (if on then "yellow" else "black")))"""
  expected = """class Light{
  constructor(on, origin){
  this.on = on;
this.origin = origin;
  this.type = Light;
  this.alive = true;
  this.render = {new Cell(position=new Position(x=0, y=0), color=on ? "yellow" : "black")};

  }
}

function light(on, origin) {
  return new Light(on, origin);
}

function updateObjLightOn(object, on) {
  return new Light(on, object.origin);
}

"""
  @test expected == compile_js(aexpr, data)
end
# (type alias Position ((: x Int) (: y Int)))
#(external (: click Click))
function test_compile_particles()
  a = au"""(program
  (= GRID_SIZE 16)

  (object Particle (Cell 0 0 "blue"))

  (: particles (List Particle))
  (= particles
     (initnext (list)
               (updateObj (prev particles) (--> obj (Particle (uniformChoice (adjPositions (.. obj origin))))))))

  (on clicked (= particles (addObj (prev particles) (Particle (Position (.. click x) (.. click y))))))
  )"""
  print(compiletojavascript(a, construct_data()))
end


function test_compile_ants()
  a = au"""(program
  (= GRID_SIZE 16)

  (object Ant (Cell 0 0 "gray"))
  (object Food (Cell 0 0 "red"))

  (: ants (List Ant))
  (= ants (initnext (map Ant (randomPositions GRID_SIZE 6))
                    (updateObj (prev ants) nextAnt)))

  (: foods (List Food))
  (= foods (initnext (list)
                     (updateObj (prev foods) (--> obj (if (== (distance obj (closest obj Ant)) 0)
					                                   then (removeObj obj)
		  									           else obj)))))

  (on clicked (= foods (addObj (prev foods) (map Food (randomPositions GRID_SIZE 4)))))

  (: nextAnt (-> Ant Ant))
  (= nextAnt (fn (ant) (move ant (unitVector ant (closest ant Food))))))"""
  print("\nFINAL OUTPUT: \n", compiletojavascript(a, construct_data()))
end


function test_compile_types_inferred()
  @test isinferred(mod.init, nothing)
  @test isinferred(mod.init, mod.Click(5,5))
  state = mod.init(nothing)
  @test isinferred(mod.next, state, mod.Click(5,5))
  @test isinferred(mod.next, state, nothing)
end

function test_compile_builtin()
  expected = "function occurred(click){\n  return click !== null;\n}\n"
  @test compilebuiltin_js()[1] == expected
end

@testset "compile" begin
  # test_compile_if()
  # test_compile_assign()
  # # compile external was removed from the code because it uses compile_type_decl
  # # test_compile_external()
  # test_compile_let()
  # test_compile_list()
  # test_compile_call()
  # test_compile_field()
  # test_compile_lambda()
  # test_compile_typealias()
  # test_compile_object()
  test_compile_particles()
  # test_compile_ants()
  # test_compile_types_inferred()
  # test_compile_builtin()
end
