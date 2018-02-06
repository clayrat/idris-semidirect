module Interfaces 

import Interfaces.Verified
import Syntax.PreorderReasoning

%access public export

interface Monoid m => Action m a where
  act : m -> a -> a

-- coherence-proving machinery  
A2M : Action m a => Monoid m
A2M = %implementation

VM2M : VerifiedMonoid m => Monoid m
VM2M = %implementation

a2m : Action m a -> Monoid m
a2m ama = %implementation

vm2m : VerifiedMonoid m -> Monoid m
vm2m vmm = %implementation

interface (VerifiedMonoid m, Action m a) => VerifiedAction m a where
  monoidMCoherence : A2M {m} {a} = VM2M {m}
  actOp : (x, y : m) -> (z : a) -> act (x <+> y) z = act x (act y z)
  actNeutral : (x : a) -> act (neutral {ty=m}) x = x

va2a : VerifiedAction m a -> Action m a
va2a vama = %implementation

va2vm : VerifiedAction m a -> VerifiedMonoid m
va2vm vama = %implementation
  
interface (VerifiedMonoid a, VerifiedAction m a) => DistributiveAction m a where
  actDistributes : (x : m) -> (y, z : a) -> act x (y <+> z) = act x y <+> act x z
  actUnitary : (x : m) -> act x (neutral {ty=a}) = neutral {ty=a}

da2va : DistributiveAction m a -> VerifiedAction m a
da2va dama = %implementation

-- Unit

Semigroup () where
  () <+> () = ()
  
Monoid () where
  neutral = ()

Action () a where
  act () = id

VerifiedSemigroup () where
  semigroupOpIsAssociative () () () = Refl

VerifiedMonoid () where
  monoidNeutralIsNeutralL () = Refl
  monoidNeutralIsNeutralR () = Refl

VerifiedAction () a where
  monoidMCoherence = Refl
  actOp () () _ = Refl
  actNeutral _ = Refl

VerifiedMonoid a => DistributiveAction () a where
  actDistributes () _ _ = Refl
  actUnitary () = Refl

-- Maybe  

Action m s => Action (Maybe m) s where
  act Nothing  s = s
  act (Just m) s = act m s    

VerifiedSemigroup a => VerifiedSemigroup (Maybe a) using collectJust where
  semigroupOpIsAssociative Nothing  _        _        = Refl
  semigroupOpIsAssociative (Just _) Nothing  _        = Refl
  semigroupOpIsAssociative (Just _) (Just _) Nothing  = Refl
  semigroupOpIsAssociative (Just x) (Just y) (Just z) = cong $ semigroupOpIsAssociative x y z

-- technically we don't need `VerifiedMonoid a` here but somehow the search is lost without it
VerifiedMonoid a => VerifiedMonoid (Maybe a) using collectJust where
  monoidNeutralIsNeutralL Nothing  = Refl
  monoidNeutralIsNeutralL (Just _) = Refl
  monoidNeutralIsNeutralR Nothing  = Refl
  monoidNeutralIsNeutralR (Just _) = Refl

VerifiedAction m s => VerifiedAction (Maybe m) s using collectJust where
  monoidMCoherence = Refl
  actOp  Nothing  Nothing _ = Refl
  actOp  Nothing (Just _) _ = Refl
  actOp (Just _)  Nothing _ = Refl
  actOp (Just x) (Just y) z = actOp x y z
  actNeutral z = Refl

DistributiveAction m a => DistributiveAction (Maybe m) a where
  actDistributes Nothing  _ _ = Refl
  actDistributes (Just x) y z = actDistributes x y z 
  actUnitary Nothing  = Refl
  actUnitary (Just x) = actUnitary x

-- Semidirect product 

data Semidirect s m = MkSemi s m

(Show s, Show m) => Show (Semidirect s m) where
  show (MkSemi a b) = show a ++ " *| " ++ show b

-- `Semigroup m` is redundant here, but if we remove it, we end up with a double diamond: 
-- VerifiedAction -> {VerifiedMonoid -> VerifiedSemigroup | Action -> Monoid} -> Semigroup
-- for which I don't really know a solution
(Semigroup m, Semigroup s, Action m s) => Semigroup (Semidirect s m) where
  (MkSemi s1 m1) <+> (MkSemi s2 m2) = MkSemi (s1 <+> act m1 s2) (m1 <+> m2) 

(Monoid s, Action m s) => Monoid (Semidirect s m) where
  neutral = MkSemi neutral neutral

DistributiveAction m s => VerifiedSemigroup (Semidirect s m) where
  semigroupOpIsAssociative (MkSemi a1 m1) (MkSemi a2 m2) (MkSemi a3 m3) = 
    rewrite actDistributes m1 a2 (act m2 a3) in
    rewrite sym $ actOp m1 m2 a3 in  
    rewrite semigroupOpIsAssociative a1 (act m1 a2) (act (m1 <+> m2) a3) in
    rewrite semigroupOpIsAssociative m1 m2 m3 in 
    Refl

-- we have a diamond here: VerifiedAction -> {Action|VerifiedMonoid} -> Monoid
-- hence the usage of the explicit preorder reasoning syntax and coherence rewrites
DistributiveAction m s => VerifiedMonoid (Semidirect s m) where
  monoidNeutralIsNeutralL @{da} (MkSemi al ml) = 
    (MkSemi (al <+> act ml neutral) (ml <+> neutral))
      ={ cong {f=\z=>MkSemi (al <+> z) (ml <+> neutral)} $ 
         actUnitary {a=s} ml }=
    (MkSemi (al <+> neutral) (ml <+> neutral))
      ={ cong {f=\z=>MkSemi z (ml <+> neutral)} $ 
         monoidNeutralIsNeutralL al }=
    (MkSemi al (ml <+> neutral))
      ={ rewrite monoidMCoherence {m} {a=s} in Refl }=
    (MkSemi al (ml <+> neutral @{vm2m $ va2vm $ da2va da}))
      ={ cong {f=\z=>MkSemi al z} $ 
         monoidNeutralIsNeutralL ml }=
    (MkSemi al ml) 
      QED
  monoidNeutralIsNeutralR @{da} (MkSemi ar mr) =
    (MkSemi (neutral <+> act neutral ar) (neutral @{a2m $ va2a $ da2va da} <+> mr))
      ={ cong {f=\z=>MkSemi (neutral <+> z) (neutral <+> mr)} $
         actNeutral @{da2va da} ar }=
    (MkSemi (neutral <+> ar) (neutral @{a2m $ va2a $ da2va da} <+> mr))
      ={ cong {f=\z=>MkSemi z (neutral <+> mr)} $
         monoidNeutralIsNeutralR ar }=
    (MkSemi ar (neutral @{a2m $ va2a $ da2va da} <+> mr))
      ={ rewrite monoidMCoherence {m} {a=s} in Refl }=
    (MkSemi ar (neutral @{vm2m $ va2vm $ da2va da} <+> mr))
      ={ cong {f=\z=>MkSemi ar z} $ 
         monoidNeutralIsNeutralR mr }=
    (MkSemi ar mr)
      QED
