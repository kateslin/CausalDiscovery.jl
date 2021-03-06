module Engine exposing (..)

import List
import Color exposing (..)

-- An object is a body
type Object
  = Circle
  | Box Position Int Int Color -- Origin Width Height Color (Scene -> Object)

-- A Scalar field 
type Field = FieldA | FieldB

type alias Particles = List Float

-- An Entity is one of the many kinds of thing that can exist
type Entity = ObjectTag Object | FieldTag Field | ParticlesTag Particles

-- A Scene is simply a collection of entities
type alias Scene = List Entity

transparent = fromRgba {red = 0.0, green = 0.0, blue = 0.0, alpha = 0.0}

type alias Pixel =
  { 
    rgba : Color,
    pos : Position
  }

alphacompose : Color -> Color -> Color
alphacompose p_ q_ = 
  let
    p = toRgba p_
    q = toRgba q_
    pacompl = 1 - p.alpha
    f = \ca cb -> ca + cb * pacompl
  in 
  fromRgba
    {
      red = f p.red q.red,
      green = f p.green q.green,
      blue = f p.blue q.blue,
      alpha = p.alpha + q.alpha * pacompl
    }
  

-- Alpha composition of multiple objects
alphacomposeMany : List Color -> Color
alphacomposeMany rgbs = 
  case rgbs of
    [] -> Color.red
    [x] -> x
    [x1, x2] -> alphacompose x1 x2
    [x1, x2, x3] -> alphacompose (alphacompose x1 x2) x3
    a::b::c -> List.foldl alphacompose a (b::c)



-- An Image is a collection of Pixels
type alias Image = {pixels : List Pixel, width : Int, height : Int }

type alias Width = Int
type alias Height = Int

-- Cartesian product
cartesian : List a -> List b -> List (a, b)
cartesian xs ys =
  List.concatMap
    (\x -> List.map ( \y -> (x, y) ) ys )
    xs

-- Grid of pixels
grid width height = cartesian (List.range 0 width) (List.range 0 height)

-- Render object 
render : Scene -> Width -> Height -> Image 
render scene width height = 
  {
    pixels = List.map (\pos -> renderpixel scene pos) (grid width height),
    width = width,
    height = height
  }

-- A Position is an (x, y) pair
type alias Position = (Int, Int)

-- A Position `pos` what is the rgb of `entity`
field : Entity -> Position -> Color
field entity pos =
  case entity of
    ObjectTag object -> fieldObject object pos
    FieldTag fieldtag -> Color.yellow
    ParticlesTag particletag -> transparent

-- Is position within box?
posInBox : Position -> Position -> Int -> Int  -> Bool
posInBox (x, y) (origx, origy) boxwidth boxheight =
  let
    xlb = origx
    xub = origx + boxwidth
    ylb = origy
    yub = origy + boxheight
  in
  x >= xlb && x <= xub && y >= ylb && y <= yub

fieldObject : Object -> Position -> Color
fieldObject object (x, y) = 
  case object of
    Box orig boxx boxy color -> if (posInBox (x, y) orig boxx boxy) then color else transparent
    Circle -> red
      

renderpixel : Scene -> Position -> Pixel
renderpixel scene pos =
  let
    colors = List.map (\entity -> field entity pos) scene
  in
    { 
      rgba = alphacomposeMany colors,
      pos = pos
    }

-- --  Update an object
-- updateObject : Object -> Scene -> Object
-- updateObject object scene =
--   case object of
--     Box num f -> object
--     Door num f -> object
--     Circle -> Circle
--     Switch t -> Circle

-- --- Update a scene
-- update msg scene = List.map updateObject scene

-- Questions
-- How can the tank origin be tied to the box origin?
-- Where to store internal state?
-- How to make the shape a function of the internal state

-- Light switch model
-- switch = Switch True
  
-- car = Box {origin = (1, 1), 0.3 (\scene -> List.head scene)
-- car = Shape {origin = (1, 1), cells = [(0, 0), (0, 1), (0, 2), (0, 3), (1, 3), (2, 3), (2, 2), (2, 1), (2, 0), (1, 0)]}  

-- -- This is invalid!
-- type alias tank_size = Int  
-- tank = Box {origin = Box.origin} 0
