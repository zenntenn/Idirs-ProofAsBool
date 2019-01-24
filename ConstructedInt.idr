module ConstructedInt

import MoreNatProofs

%access public export
%default total

data ConsInt : Type where
  Negative : (n : Nat) -> ConsInt
  Positive : (n : Nat) -> ConsInt

castIntegerToConsInt : Integer -> ConsInt
castIntegerToConsInt x = case x < 0 of
                              False => Positive (toNat x)
                              True => Negative (toNat (abs x))

addConsInt : ConsInt -> ConsInt -> ConsInt
addConsInt (Negative n) (Negative k) = Negative (n + k)
addConsInt (Negative n) (Positive k) = case isLTE n k of
                                            (Yes prf) => Positive (k - n)
                                            (No contra) => Negative ((-) n k {smaller = notLTEFlips contra})
addConsInt (Positive n) (Negative k) = ?addConsInt_rhs_1
addConsInt (Positive n) (Positive k) = Positive (n + k)


multConsInt : ConsInt -> ConsInt -> ConsInt
multConsInt (Negative n) (Negative k) = Positive (n * k)
multConsInt (Positive n) (Positive k) = Positive (n * k)
multConsInt (Negative n) (Positive k) = Negative (n * k)
multConsInt (Positive n) (Negative k) = Negative (n * k)


Num ConsInt where
  (+) = addConsInt
  (*) = multConsInt

  fromInteger = castIntegerToConsInt

Abs ConsInt where
  abs (Negative n) = Positive n
  abs (Positive n) = Positive n

negateConsInt : ConsInt -> ConsInt -> ConsInt
negateConsInt x y = ?negateConsInt_rhs

Neg ConsInt where
  negate x = negateConsInt (fromInteger 0) x
  (-) = negateConsInt
