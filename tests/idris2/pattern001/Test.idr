FOO : String
FOO = "Foo"
%pattern_synonym FOO

BAR : String
BAR = "Bar"
%pattern_synonym BAR

foobar : String -> Bool
foobar FOO = True
foobar BAR = True
foobar _ = False

JustPair : a -> b -> Maybe (a, b)
JustPair x y = Just (x, y)
%pattern_synonym JustPair

first : Maybe (a, b) -> Maybe a
first (JustPair x _) = Just x
first _ = Nothing

data Typ = App String (List Typ)

arrow1 : Typ -> Typ -> Typ
arrow1 t1 t2 = App "->" [t1, t2]
%pattern_synonym arrow1

collectArgs1 : Typ -> List Typ
collectArgs1 (arrow1 t1 t2) = t1 :: (collectArgs1 t2)
collectArgs1 t = [t]

arrow2 : Typ -> Typ -> Typ
arrow2 (App "F" [t1]) t2 = App "->" [t1, t2]
%pattern_synonym arrow2

arrow3 : Typ -> Typ -> Typ
arrow3 t1 t2 = App "->" [t1, t2]
arrow3 t1 t2 = App "->" [t1, t2]
%pattern_synonym arrow3

arrow4 : Typ -> Typ -> Typ
arrow4 (App s t1) t2 = App "->" (t2 :: t1)
%pattern_synonym arrow4
