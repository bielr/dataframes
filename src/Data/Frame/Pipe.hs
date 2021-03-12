{-# language RebindableSyntax #-}
{-# language NoImplicitPrelude #-}
module Data.Frame.Pipe where


type family M df i j a where
   M df i j () = (df i -> df j)


-- fmap :: (() -> ()) -> M df i j () -> M df i j ()
-- fmap _ fi = fi
--
--
-- (<*>) :: M df i j (() -> ()) -> M df j k () -> M df i k ()
-- (<*>) = (>>)
--
--
-- join :: M df i j ()
-- join mma = mma



-- T
(>>=) :: M df i j () -> (df j -> M df j k ()) -> M df i k ()
(>>=) f g !a = let !b = f a in g b b


-- --
(>>) :: M df i j () -> M df j k () -> M df i k ()
(>>) f g !a = let !b = f a in g b


pure :: () -> M df i i ()
pure () !a = a


return :: () -> M df i i ()
return = pure
