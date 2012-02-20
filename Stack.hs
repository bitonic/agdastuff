{-# LANGUAGE DataKinds
           , GADTs
           , KindSignatures
           , TypeOperators
           , TypeFamilies
           , Rank2Types
           , PolyKinds
           , MultiParamTypeClasses
           , FlexibleInstances
           , ScopedTypeVariables
 #-}

import Prelude hiding (drop)

infixr 5 :>

data Stack (a :: [*]) where
  Nil  :: Stack '[]
  (:>) :: a -> Stack tys -> Stack (a ': tys)

head :: Stack (a ': tys) -> a
head (x :> _) = x

push :: a -> Stack tys -> Stack (a ': tys)
push = (:>)

type (ts1 :: [*]) :=> (ts2 :: [*]) = Stack ts1 -> Stack ts2

data Nat = Zero | Suc Nat

type family Drop (n :: Nat) (a :: [*]) :: [*] 
type instance Drop Zero     a          = a
type instance Drop (Suc n) (ty ': tys) = Drop n tys

data DropN (p :: Nat) (tys1 :: [*]) (tys2 :: [*]) where
    Base   :: DropN Zero tys tys
    Induct :: DropN n tys1 tys2 -> DropN (Suc n) (ty ': tys1) tys2

dropN :: forall (p :: Nat) (tys1 :: [*]) (tys2 :: [*]) .
         DropN p tys1 tys2 -> (tys1 :=> tys2)
dropN Base       s        = s
dropN (Induct d) (_ :> s) = dropN d s
dropN _          _        = error "This won't happen"

data Proxy p = Proxy

class BuildDropN (p :: Nat) (tys1 :: [*]) (tys2 :: [*]) where
    buildDropN :: DropN p tys1 tys2
instance BuildDropN 'Zero tys tys where
    buildDropN = Base
instance BuildDropN p tys1 tys2 => BuildDropN ('Suc p) (ty ': tys1) tys2 where
    buildDropN = Induct buildDropN

drop :: forall (p :: Nat) (tys1 :: [*]) (tys2 :: [*]) .
        BuildDropN p tys1 tys2 =>
        Stack (Proxy p ': tys1) -> Stack tys2
drop (_ :> s) = dropN (buildDropN :: DropN p tys1 tys2) s

zero :: Proxy 'Zero
zero = Proxy

one :: Proxy ('Suc 'Zero)
one = Proxy

two :: Proxy ('Suc ('Suc 'Zero))
two = Proxy

three :: Proxy ('Suc ('Suc ('Suc 'Zero)))
three = Proxy

type family Add (n :: Nat) (m :: Nat) :: Nat
type instance Add Zero    m = m
type instance Add (Suc n) m = Suc (Add n m)

add :: forall (n :: Nat) (m :: Nat) (tys :: [*]).
       (Proxy n ': Proxy m ': tys) :=> (Proxy (Add n m) ': tys)
add (_ :> _ :> s) = Proxy :> s
add _             = error "This won't happen"

test2 :: forall (tys :: [*]) a b . (a ': b ': tys) :=> tys
test2 = drop . add . push three . push one . push two . push three
