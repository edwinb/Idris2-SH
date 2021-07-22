f : (Int -> Bool) -> Int
f p = case (p 0, p 1) of
        (False, False) => 0
        (False, True)  => 1
        (True , False) => 2
        (True , True)  => 4

il : Int
il = f $ \x => x > 0

lc : Int
lc = f $ \case 0 => True ; _ => False

ilc : Int
ilc = f (\case 0 => True; _ => False)
