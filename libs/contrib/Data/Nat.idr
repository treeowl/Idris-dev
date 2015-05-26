||| Extra utilities for working with Nats
module Data.Nat

import Data.Fin
import Data.So

import Control.Relations.Basics
import Control.Relations.ClosureOperators
import Control.Relations.TransitiveClosure
import Control.WellFounded

%default total
%access public

||| A strict less-than relation on `Nat`.
|||
||| @ n the smaller number
||| @ m the larger number
data LT' : (n,m : Nat) -> Type where
  ||| n < 1 + n
  LTSucc : LT' n (S n)
  ||| n < m implies that n < m + 1
  LTStep : LT' n m -> LT' n (S m)

%name LT' lt, lt'

||| Nothing is strictly less than zero
instance Uninhabited (LT' n 0) where
  uninhabited LTSucc impossible

||| Zero is less than any non-zero number.
LTZeroLeast : LT' Z (S n)
LTZeroLeast {n = Z}   = LTSucc
LTZeroLeast {n = S n} = LTStep LTZeroLeast

||| If n < m, then 1 + n < 1 + m
ltSuccSucc : LT' n m -> LT' (S n) (S m)
ltSuccSucc LTSucc      = LTSucc
ltSuccSucc (LTStep lt) = LTStep $ ltSuccSucc lt

||| If n + 1 < m, then n < m
lteToLt' : LTE (S n) m -> LT' n m
lteToLt' {n = Z}   (LTESucc x) = LTZeroLeast
lteToLt' {n = S k} (LTESucc x) = ltSuccSucc $ lteToLt' x

||| Convert from LT' to LTE
ltToLTE : LT' n m -> LTE (S n) m
ltToLTE LTSucc      = lteRefl
ltToLTE (LTStep lt) = lteSuccRight $ ltToLTE lt

lt'EquivLT : LT' `Equivalent` LT
lt'EquivLT = MkEquivalent (\x,y => ltToLTE) (\x,y=> lteToLt')

||| Subtraction gives a result that is actually smaller.
minusLT' : (x,y : Nat) -> x - y `LT'` S x
minusLT' Z     y = LTSucc
minusLT' (S k) Z = LTSucc
minusLT' (S k) (S j) = LTStep (minusLT' k j)

||| Strict less-than is well-founded, with the cascade stopping at
||| zero (because there's nothing less than zero). This can't be done
||| for LTE, because that one doesn't stop at zero (because `LTE 0 0`
||| is inhabited).
lt'WellFounded : WellFounded LT'
lt'WellFounded x = Access (acc x)
    where
      ||| Show accessibility by induction on the structure of the LT' witness
      acc : (x, y : Nat) -> LT' y x -> Accessible LT' y
      -- Zero is vacuously accessible: there's nothing smaller to check
      acc Z     y lt = absurd lt
      -- If the element being accessed is one smaller, we're done
      acc (S y) y LTSucc = Access (acc y)
      -- If the element is more than one smaller, we need to go further
      acc (S k) y (LTStep smaller) = acc k y smaller

||| `LT`, the strict less-than operator based on `LTE`, is also well-founded.
ltWellFounded : WellFounded LT
ltWellFounded = coarserWF LT LT' (\n, m => lteToLt' {n} {m}) lt'WellFounded

{-
-- A somewhat more direct but rather longer proof that LT is well-founded.
-- It might pay to try to figure out if the different proofs lead to
-- different performance for recursion.

lteTrans : LTE x y -> LTE y z -> LTE x z
lteTrans LTEZero yz = LTEZero
lteTrans (LTESucc x) (LTESucc y) = LTESucc (lteTrans x y)

lemmyh : a `LT` b -> b `LT` S c -> a `LT` c
lemmyh (LTESucc LTEZero) (LTESucc (LTESucc x)) = LTESucc LTEZero
lemmyh (LTESucc (LTESucc x)) (LTESucc (LTESucc (LTESucc y))) = LTESucc (LTESucc (lteTrans x y))

ltWellFounded : WellFounded LT
ltWellFounded a = Access (acc a)
  where
    acc : (x, y : Nat) -> LT y x -> Accessible LT y
    acc Z y yx = absurd yx
    acc (S k) Z yx = Access (\q, r => absurd r)
    acc (S k) (S j) (LTESucc x) with (acc k j x)
      acc (S k) (S j) (LTESucc x) | (Access acc') = Access (\y, ysm => Access (\w,q => acc' w (lemmyh q ysm)))
-}

||| The immediate predecessor relation
data ImmediatelyPrecedes : Rel Nat where
  PrecStep : n `ImmediatelyPrecedes` S n

immediatelyPrecedesWF : WellFounded ImmediatelyPrecedes
immediatelyPrecedesWF x = Access the_acc
  where
    the_acc : (y : Nat) -> ImmediatelyPrecedes y x -> Accessible ImmediatelyPrecedes y
    the_acc y ip with (x)
      the_acc y PrecStep | Z impossible
      the_acc y PrecStep | (S y) = immediatelyPrecedesWF y

lt'Transitive : Transitive LT'
lt'Transitive x y (S y) xy LTSucc = LTStep xy
lt'Transitive x y (S m) xy (LTStep lt) = let foo = lt'Transitive x y m xy lt in (LTStep foo)

||| `LT'` is the transitive closure of `ImmediatelyPrecedes`
lt'IsTransitiveClosureOfIP : LT' `IsTransitiveClosureOf` ImmediatelyPrecedes
lt'IsTransitiveClosureOfIP =
  MkIsClosureUnderPredOf
    incl lt'Transitive coarse
  where
    incl : (x, y : Nat) -> ImmediatelyPrecedes x y -> LT' x y
    incl x (S x) PrecStep = LTSucc
    coarse : (rel : Rel Nat) -> ImmediatelyPrecedes `Coarser` rel ->
            Transitive rel -> LT' `Coarser` rel
    coarse rel f g x (S x) LTSucc = f x (S x) PrecStep
    coarse rel f g x (S m) (LTStep lt) with (coarse rel f g x m lt)
      | relxm = g x m (S m) relxm (f m (S m) PrecStep)

||| `LT` is the transitive closure of `ImmediatelyPrecedes`
ltIsTransitiveClosureOfIP : LT `IsTransitiveClosureOf` ImmediatelyPrecedes
ltIsTransitiveClosureOfIP = isTransitiveClosureOfRespEq LT' LT lt'IsTransitiveClosureOfIP lt'EquivLT


||| The result of division on natural numbers.
|||
||| @ dividend the dividend
||| @ divisor the divisor
data DivMod : (dividend, divisor : Nat) -> Type where
  ||| The result of division, with a quotient and a remainder.
  |||
  ||| @ dividend the dividend
  ||| @ divisor the divisor
  ||| @ quotient the quotient
  ||| @ remainder the remainder (bounded by the divisor)
  ||| @ ok the fact that this is, in fact, a result of division
  DivModRes : {dividend, divisor : Nat} ->
              (quotient : Nat) -> (remainder : Fin divisor) ->
              (ok : dividend = finToNat remainder + quotient * divisor) ->
              DivMod dividend divisor


||| Any natural number can be a `Fin` where the bound is itself plus some difference.
private
toFin : (x : Nat) -> (diff : Nat) -> Fin (plus x (S diff))
toFin Z diff = FZ
toFin (S k) diff = FS $ toFin k diff

||| Converting to a `Fin` and back to `Nat` preserves the input. This is a correctness proof for `toFin`.
private
toFinAndBack : (x : Nat) -> (diff : Nat) -> finToNat (toFin x diff) = x
toFinAndBack Z diff = Refl
toFinAndBack (S k) diff = cong (toFinAndBack k diff)


||| The accessibilty predicate used for division.
private
accPlusLT' : LT' (S j) (S (plus k (S j)))
accPlusLT' {j = Z}   {k = Z}   = LTSucc
accPlusLT' {j = Z}   {k = S k} = LTStep (accPlusLT' {j = Z} {k = k})
accPlusLT' {j = S j} {k = k}   = rewrite sym $ plusSuccRightSucc k (S j) in
                                 ltSuccSucc accPlusLT'


||| Division and modulus on `Nat`, inspired by the definition in the
||| Agda standard library.
|||
||| This uses well-founded recursion on `LT'`.
|||
||| @ dividend the dividend
||| @ divisor the divisor
||| @ nonzero division by zero is nonsense
total -- yay!
divMod : (dividend, divisor : Nat) ->
         {auto nonzero : So (not (decAsBool (decEq divisor Z)))} ->
         DivMod dividend divisor
divMod _     Z     {nonzero} = absurd nonzero
divMod Z     (S k)           = DivModRes 0 FZ Refl
divMod (S j) (S k) {nonzero} = wfInd {P=P} lt'WellFounded stepDiv (S j) (S k) nonzero
  where
    ||| The goal passed to the accessibility eliminator.
    |||
    ||| This is responsible for generating the goal in the
    ||| well-founded fixed point.
    |||
    ||| @ dividend the dividend to recurse over
    P : (dividend : Nat) -> Type
    P dividend = (divisor : Nat) -> (nonzero : So (not (decAsBool (decEq divisor Z)))) -> DivMod dividend divisor


    ||| Well-founded recursion needs a recursion operator.
    |||
    ||| @ dividend the dividend we are recursing over
    ||| @ rec the recursive call provided by the well-founded induction operator
    stepDiv : (dividend : Nat) -> (rec : (d' : Nat) -> LT' d' dividend -> P d') -> P dividend
    -- We need not consider division by zero
    stepDiv dividend rec   Z     nonzero = absurd nonzero
    -- Dividing zero by anyting else gives 0, with 0 remainder
    stepDiv Z rec (S k) nonzero = DivModRes 0 0 Refl
    -- To divide two non-zero values, we must know which is larger
    stepDiv (S j) rec (S k) nonzero with (cmp j k)
      -- n / n = 1 remainder 0
      stepDiv (S j)                 rec (S j)                 nonzero | CmpEQ      =
        DivModRes 1 0 (sym $ cong (plusZeroRightNeutral j))
      -- if n < m, then m = n + r, and the quotient is 0 with remainder r
      stepDiv (S j)                 rec (S (plus j (S diff))) nonzero | CmpLT diff =
        DivModRes 0 (toFin (S j) diff) $
          rewrite toFinAndBack j diff
          in sym $ cong (plusZeroRightNeutral j)
      -- if n > m, then n = m + d, and the quotient is 1 + ((n - m) / m) with the same remainder
      stepDiv (S (plus k (S diff))) rec (S k)                 nonzero | CmpGT diff =
        let res = rec (S diff) accPlusLT' (S k) Oh
        in case res of
             DivModRes quotient remainder ok =>
               DivModRes (S quotient) remainder $
                 rewrite plusAssociative (finToNat remainder) (S k) (mult quotient (S k)) in
                 rewrite plusCommutative (finToNat remainder) (S k) in
                 rewrite sym $ plusAssociative (S k) (finToNat remainder) (mult quotient (S k)) in
                 rewrite ok in Refl

