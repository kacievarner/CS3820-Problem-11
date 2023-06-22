{-# LANGUAGE DataKinds, FlexibleInstances, GADTs, KindSignatures #-}
module Problem11 where
import Data.Bits (Bits(xor))

{-------------------------------------------------------------------------------

CS:3820 Fall 2021 Problem of the Week #11
=========================================

This problem continues our exploration of derivations and their representation
in Haskell.  As in the last problem, we're going to be considering the reflexive
transitive closure of relations.  Unlike last week, however, we're going to look
at a generic formulation of the reflexive transitive closure in Haskell.  We'll
start with two single-step relations (even if they're not particularly
surprising).

-------------------------------------------------------------------------------}

data Nat = Z | S Nat

-- To avoid the series of strangely named "finiteness" functions from P10---you
-- can safely ignore this part.
class Proof p where
    finite :: p -> () 

data Lt1 :: Nat -> Nat -> * where
    Lt1 :: Lt1 m (S m)

instance Proof (Lt1 m n) where
    finite Lt1 = ()

data Gt1 :: Nat -> Nat -> * where
    Gt1 :: Gt1 (S m) m

instance Proof (Gt1 m n) where
    finite Gt1 = ()

{-------------------------------------------------------------------------------

As we discussed last problem, there are two ways to think about the reflexive
transitive closure of relation R: either as a (possibly 0-length) sequence of
instances of R (`RTC1`) or in terms of explicit reflexive and transitive cases
(`RTC2`).  Unlike last time, however, this time our construction is parametric
over the relation in question.  As examples, we give proofs for both <₁* and >₁*
using each representation of the reflexive transitive closure.

>>> Step Lt1 (Step Lt1 Done) :: RTC1 Lt1 (S Z) (S (S (S Z)))
proved!

>>> Step Gt1 (Step Gt1 Done) :: RTC1 Gt1 (S (S (S Z))) (S Z)
proved!

>>> Trans (Inst Lt1) (Inst Lt1) :: RTC2 Lt1 (S Z) (S (S (S Z)))
proved!

>>> Trans (Inst Gt1) (Inst Gt1) :: RTC2 Gt1 (S (S (S Z))) (S Z)
proved!

-------------------------------------------------------------------------------}

data RTC1 :: (Nat -> Nat -> *) -> Nat -> Nat -> * where
    Done :: RTC1 r m m
    Step :: r m n -> RTC1 r n p -> RTC1 r m p

instance Proof (RTC1 Lt1 m n) where
    finite Done = ()
    finite (Step p r) = finite p `seq` finite r

instance Show (RTC1 Lt1 m n) where
    show p = finite p `seq` "proved!"

instance Proof (RTC1 Gt1 m n) where
    finite Done = ()
    finite (Step p r) = finite p `seq` finite r

instance Show (RTC1 Gt1 m n) where
    show p = finite p `seq` "proved!"

data RTC2 :: (Nat -> Nat -> *) -> Nat -> Nat -> * where
    Refl  :: RTC2 r m m
    Inst  :: r m n -> RTC2 r m n
    Trans :: RTC2 r m n -> RTC2 r n p -> RTC2 r m p

instance Proof (RTC2 Lt1 m n) where
    finite Refl = ()
    finite (Inst p) = finite p
    finite (Trans p q) = finite p `seq` finite q

instance Show (RTC2 Lt1 m n) where
    show p = finite p `seq` "proved!"

instance Proof (RTC2 Gt1 m n) where
    finite Refl = ()
    finite (Inst p) = finite p
    finite (Trans p q) = finite p `seq` finite q

instance Show (RTC2 Gt1 m n) where
    show p = finite p `seq` "proved!"

{-------------------------------------------------------------------------------

Problem 11-1
------------

Your first task is to show that >₁* is the converse of <₁*; that is, to show
that if

    m <₁* n

then

    n >₁* m

You'll do this by writing a function `conv2` that maps from values in `RTC2 Lt1
m n` (that is to say: proofs of m <₁* n) to values in `RTC2 Gt1 n m` (that is to
say: proofs of n >₁* m).

This is *much* easier to do with the `RTC2` representation of the reflexive
transitive closure.  (If you don't believe me, try the other one yourself.)
We'll return to the `RTC1` representation at the end of of the problem.

-------------------------------------------------------------------------------}

conv2 :: RTC2 Lt1 m n -> RTC2 Gt1 n m
conv2 Refl = Refl --Base case
conv2 (Inst x) = Inst (conv2Helper x) --Case for flip with inst
conv2 (Trans x y) = Trans (conv2 y) (conv2 x) --Trans and flip

conv2Helper :: Lt1 m n -> Gt1 n m --Helper function for flipping terms
conv2Helper Lt1 = Gt1

-- >>> conv2 (Trans (Inst Lt1) (Inst Lt1)) :: RTC2 Gt1 (S (S (S Z))) (S Z)
-- proved!

{-------------------------------------------------------------------------------

Problem 11-2
------------

The two representations of the reflexive transitive closure should be
equivalent.  I've asserted that they are, but in this problem you'll demonstrate
it.  To do so, you'll write two functions, `oneToTwo` and `twoToOne` that
convert between the representations.

In writing `twoToOne`, you might find yourself at a bit of an impasse in the
`Trans` case.  If so, consider writing a helper function with the type

    RTC1 r m n -> RTC1 r n p -> RTC1 r m p

-------------------------------------------------------------------------------}

oneToTwo :: RTC1 r m p -> RTC2 r m p
oneToTwo Done = Refl --Base case
oneToTwo (Step x Done) = Inst x --Case for instances of x
oneToTwo (Step x y) = Trans (Inst x)(oneToTwo y) --Transitive single representation case

-- >>> oneToTwo (Step Lt1 (Step Lt1 Done)) :: RTC2 Lt1 Z (S (S Z))
-- proved!

twoToOne :: RTC2 r m p -> RTC1 r m p
twoToOne Refl = Done --Base case
twoToOne (Inst x) = Step x Done --Case for instances of x
twoToOne (Trans x y) = twoToOneHelper(twoToOne x)(twoToOne y) --Transitive second representation case

twoToOneHelper :: RTC1 r m n -> RTC1 r n p -> RTC1 r m p --Helper function as defined above
twoToOneHelper m n = case m of --Definition of second representation
    Done -> n --Done as n
    Step x y -> Step x (twoToOneHelper y n) --Step of the second representation

-- >>> twoToOne (Trans (Inst Gt1) (Inst Gt1)) :: RTC1 Gt1 (S (S Z)) Z
-- proved!

{-------------------------------------------------------------------------------

Problem 11-3
------------

Now that we can map between the representations of reflexive transitive
closures, we can finish the converse argument we started in 11-1.  For your
final task, you'll write a function `conv1` that shows that >₁* is the converse
of <₁* with the RTC1 representation of the reflexive transitive closure as well.

Note: you should *not* have to do any pattern matching in writing your solution.

-------------------------------------------------------------------------------}

conv1 :: RTC1 Lt1 m n -> RTC1 Gt1 n m 
conv1 x = twoToOne(conv2(oneToTwo x)) --Proves converse

-- >>> conv1 (Step Lt1 (Step Lt1 Done)) :: RTC1 Gt1 (S (S (S Z))) (S Z)
-- proved!
