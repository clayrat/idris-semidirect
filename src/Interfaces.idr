module Interfaces 

%access public export

interface Monoid m => Action m a where
  act : m -> a -> a

Semigroup () where
  () <+> () = ()
  
Monoid () where
  neutral = ()

Action () l where
  act () = id

Action m s => Action (Maybe m) s where
  act Nothing  s = s
  act (Just m) s = act m s  

data Semidirect s m = MkSemi s m

(Show s, Show m) => Show (Semidirect s m) where
  show (MkSemi a b) = show a ++ " *| " ++ show b

(Semigroup m, Semigroup s, Action m s) => Semigroup (Semidirect s m) where
  (MkSemi s1 m1) <+> (MkSemi s2 m2) = MkSemi (s1 <+> act m1 s2) (m1 <+> m2) 

(Monoid m, Monoid s, Action m s) => Monoid (Semidirect s m) where
  neutral = MkSemi neutral neutral
  