module ConstructedInt

import MoreNatProofs
import NonZeroNat

%access public export
%default total

data ConsInt : Type where
  Negative : (n : Nat) -> ConsInt
  Positive : (n : Nat) -> ConsInt

%name ConsInt h, i, j, k, l

getSign : (i : ConsInt) -> (Nat -> ConsInt)
getSign (Negative n) = Negative
getSign (Positive n) = Positive

castIntegerToConsInt : Integer -> ConsInt
castIntegerToConsInt x = case x < 0 of
                              False => Positive (toNat x)
                              True => Negative (toNat (abs x))

negPlusPos : Nat -> Nat -> ConsInt
negPlusPos n k = case isLTE n k of
                      (Yes prf) => Positive (k - n)
                      (No contra) => Negative ((-) n k {smaller = notLTEFlips contra})

addConsInt : ConsInt -> ConsInt -> ConsInt
addConsInt (Negative n) (Negative k) = Negative (n + k)
addConsInt (Negative n) (Positive k) = negPlusPos n k
addConsInt (Positive n) (Positive k) = Positive (n + k)
addConsInt (Positive n) (Negative k) = negPlusPos k n


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
negateConsInt x (Negative n) = x + (Positive n)
negateConsInt x (Positive n) = x + (Negative n)

Neg ConsInt where
  negate x = negateConsInt (fromInteger 0) x
  (-) = negateConsInt

equalConsInt : ConsInt -> ConsInt -> Bool
equalConsInt (Negative n) (Negative k) = n == k
equalConsInt (Negative Z) (Positive Z) = True
equalConsInt (Negative Z) (Positive (S k)) = False
equalConsInt (Negative (S j)) (Positive Z) = False
equalConsInt (Negative (S j)) (Positive (S k)) = False
equalConsInt (Positive Z) (Negative Z) = True
equalConsInt (Positive Z) (Negative (S k)) = False
equalConsInt (Positive (S j)) (Negative k) = False
equalConsInt (Positive n) (Positive k) = n == k

Eq ConsInt where
  (==) = equalConsInt

Cast Integer ConsInt where
  cast = castIntegerToConsInt

castConsIntToInteger : (orig : ConsInt) -> Integer
castConsIntToInteger (Positive n) = cast n
castConsIntToInteger (Negative n) = -(cast n)


Cast ConsInt Integer where
  cast = castConsIntToInteger

castNatToConsInt : (orig : Nat) -> ConsInt
castNatToConsInt orig = Positive orig

Cast Nat ConsInt where
  cast = castNatToConsInt

castConsIntToString : (orig : ConsInt) -> String
castConsIntToString orig = cast (castConsIntToInteger orig)

Cast ConsInt String where
  cast = castConsIntToString

Show ConsInt where
  show = castConsIntToString

-- Proofs
negSameNumberEq : {m : Nat} -> Negative m = Negative m
negSameNumberEq {m = Z} = Refl
negSameNumberEq {m = (S k)} = Refl

sameSignSameAbsValueEq : {sign : (Nat -> ConsInt)} -> {auto n : Nat} -> (sign m) = (sign m)
sameSignSameAbsValueEq {sign = sign} {n = n} = Refl

negativeZNotEqNegSk : {auto n : Nat} -> ((Negative Z) = (Negative (S n)) -> Void)
negativeZNotEqNegSk Refl impossible

negEqImpliesNegSuccEq : (prf : k = j) -> Negative (S k) = Negative (S j)
negEqImpliesNegSuccEq Refl = Refl

notEqNegativeImpliesNotEq : (contra : (k = j) -> Void) -> (Negative (S k) = Negative (S j)) -> Void
notEqNegativeImpliesNotEq contra Refl = contra Refl

data Eq : (m, n : ConsInt) -> Type where
  EqZeroBothNeg : Eq (Negative Z) (Negative Z)
  EqZeroFirstPos : Eq (Positive Z) (Negative Z)
  EqZeroFirstNeg : Eq (Negative Z) (Positive Z)
  EqZeroBothPos : Eq (Positive Z) (Positive Z)
  EqSuccPos : Eq (Positive (S k)) (Positive (S k))
  EqSuccNeg : Eq (Negative (S l)) (Negative (S l))

NegZeroNotEqSucc : Eq (Negative 0) (Negative (S k)) -> Void
NegZeroNotEqSucc EqZeroBothNeg impossible
NegZeroNotEqSucc EqZeroFirstPos impossible
NegZeroNotEqSucc EqZeroFirstNeg impossible
NegZeroNotEqSucc EqZeroBothPos impossible
NegZeroNotEqSucc EqSuccPos impossible
NegZeroNotEqSucc EqSuccNeg impossible

NegSuccNotEqZero : Eq (Negative (S j)) (Negative 0) -> Void
NegSuccNotEqZero EqZeroBothNeg impossible
NegSuccNotEqZero EqZeroFirstPos impossible
NegSuccNotEqZero EqZeroFirstNeg impossible
NegSuccNotEqZero EqZeroBothPos impossible
NegSuccNotEqZero EqSuccPos impossible
NegSuccNotEqZero EqSuccNeg impossible

NegSuccEq : (prf : j = k) -> Eq (Negative (S j)) (Negative (S k))
NegSuccEq Refl = EqSuccNeg

NegSuccNotEq : (contra : (j = k) -> Void) -> Eq (Negative (S j)) (Negative (S k)) -> Void
NegSuccNotEq contra EqSuccNeg = contra Refl

negZeroNotEqPositiveSucc : Eq (Negative 0) (Positive (S k)) -> Void
negZeroNotEqPositiveSucc EqZeroBothNeg impossible
negZeroNotEqPositiveSucc EqZeroFirstPos impossible
negZeroNotEqPositiveSucc EqZeroFirstNeg impossible
negZeroNotEqPositiveSucc EqZeroBothPos impossible
negZeroNotEqPositiveSucc EqSuccPos impossible
negZeroNotEqPositiveSucc EqSuccNeg impossible

negSuccNotEqPositiveZero : Eq (Negative (S j)) (Positive 0) -> Void
negSuccNotEqPositiveZero EqZeroBothNeg impossible
negSuccNotEqPositiveZero EqZeroFirstPos impossible
negSuccNotEqPositiveZero EqZeroFirstNeg impossible
negSuccNotEqPositiveZero EqZeroBothPos impossible
negSuccNotEqPositiveZero EqSuccPos impossible
negSuccNotEqPositiveZero EqSuccNeg impossible

negSuccNotEqPosSucc : Eq (Negative (S j)) (Positive (S k)) -> Void
negSuccNotEqPosSucc EqZeroBothNeg impossible
negSuccNotEqPosSucc EqZeroFirstPos impossible
negSuccNotEqPosSucc EqZeroFirstNeg impossible
negSuccNotEqPosSucc EqZeroBothPos impossible
negSuccNotEqPosSucc EqSuccPos impossible
negSuccNotEqPosSucc EqSuccNeg impossible

posZeroNotEqNegSucc : Eq (Positive 0) (Negative (S k)) -> Void
posZeroNotEqNegSucc EqZeroBothNeg impossible
posZeroNotEqNegSucc EqZeroFirstPos impossible
posZeroNotEqNegSucc EqZeroFirstNeg impossible
posZeroNotEqNegSucc EqZeroBothPos impossible
posZeroNotEqNegSucc EqSuccPos impossible
posZeroNotEqNegSucc EqSuccNeg impossible

posSuccNotEqNegZero : Eq (Positive (S j)) (Negative 0) -> Void
posSuccNotEqNegZero EqZeroBothNeg impossible
posSuccNotEqNegZero EqZeroFirstPos impossible
posSuccNotEqNegZero EqZeroFirstNeg impossible
posSuccNotEqNegZero EqZeroBothPos impossible
posSuccNotEqNegZero EqSuccPos impossible
posSuccNotEqNegZero EqSuccNeg impossible

posSuccNotEqNegSucc : Eq (Positive (S j)) (Negative (S k)) -> Void
posSuccNotEqNegSucc EqZeroBothNeg impossible
posSuccNotEqNegSucc EqZeroFirstPos impossible
posSuccNotEqNegSucc EqZeroFirstNeg impossible
posSuccNotEqNegSucc EqZeroBothPos impossible
posSuccNotEqNegSucc EqSuccPos impossible
posSuccNotEqNegSucc EqSuccNeg impossible

posZeroNotEqSucc : Eq (Positive 0) (Positive (S k)) -> Void
posZeroNotEqSucc EqZeroBothNeg impossible
posZeroNotEqSucc EqZeroFirstPos impossible
posZeroNotEqSucc EqZeroFirstNeg impossible
posZeroNotEqSucc EqZeroBothPos impossible
posZeroNotEqSucc EqSuccPos impossible
posZeroNotEqSucc EqSuccNeg impossible

posSuccNotEqZero : Eq (Positive (S j)) (Positive 0) -> Void
posSuccNotEqZero EqZeroBothNeg impossible
posSuccNotEqZero EqZeroFirstPos impossible
posSuccNotEqZero EqZeroFirstNeg impossible
posSuccNotEqZero EqZeroBothPos impossible
posSuccNotEqZero EqSuccPos impossible
posSuccNotEqZero EqSuccNeg impossible

posSuccEq : (prf : j = k) -> Eq (Positive (S j)) (Positive (S k))
posSuccEq Refl = EqSuccPos

posSuccNotEq : (contra : (j = k) -> Void) -> Eq (Positive (S j)) (Positive (S k)) -> Void
posSuccNotEq contra EqSuccPos = contra Refl

-- I really wish I could find a way to make proofs here more concise.
isEq : (i, j : ConsInt) -> Dec (i `Eq` j)
isEq (Negative Z) (Negative Z) = Yes EqZeroBothNeg
isEq (Negative Z) (Negative (S k)) = No NegZeroNotEqSucc
isEq (Negative (S j)) (Negative Z) = No NegSuccNotEqZero
isEq (Negative (S j)) (Negative (S k)) = case isEq j k of
                                              (Yes prf) => Yes (NegSuccEq prf)
                                              (No contra) => No (NegSuccNotEq contra)
isEq (Negative Z) (Positive Z) = Yes EqZeroFirstNeg
isEq (Negative Z) (Positive (S k)) = No negZeroNotEqPositiveSucc
isEq (Negative (S j)) (Positive Z) = No negSuccNotEqPositiveZero
isEq (Negative (S j)) (Positive (S k)) = No negSuccNotEqPosSucc
isEq (Positive Z) (Negative Z) = Yes EqZeroFirstPos
isEq (Positive Z) (Negative (S k)) = No posZeroNotEqNegSucc
isEq (Positive (S j)) (Negative Z) = No posSuccNotEqNegZero
isEq (Positive (S j)) (Negative (S k)) = No posSuccNotEqNegSucc
isEq (Positive Z) (Positive Z) = Yes EqZeroBothPos
isEq (Positive Z) (Positive (S k)) = No posZeroNotEqSucc
isEq (Positive (S j)) (Positive Z) = No posSuccNotEqZero
isEq (Positive (S j)) (Positive (S k)) = case isEq j k of
                                              (Yes prf) => Yes (posSuccEq prf)
                                              (No contra) => No (posSuccNotEq contra)

||| Proofs that `m` is not equal to `n`
||| @ m the first number
||| @ n the second number
NotEq : (m, n : ConsInt) -> Type
NotEq m n = Not (m `Eq` n)

eQImplNotNotEq : (prf : Eq h i) -> (Eq h i -> Void) -> Void
eQImplNotNotEq prf f = f prf

notEqImplNotEq : (contra : Eq h i -> Void) -> Eq h i -> Void
notEqImplNotEq contra x = contra x

isNotEq : (h, i : ConsInt) -> Dec (h `NotEq` i)
isNotEq h i = case isEq h i of
                   (Yes prf) => No (eQImplNotNotEq prf)
                   (No contra) => Yes (notEqImplNotEq contra)

data LTE : (j, k : ConsInt) -> Type where
  ||| -m <= +n
  LTENegPos : LTE (Negative m) (Positive n)
  ||| -(m + 1) <= -0
  LTEBothNegWZero : LTE (Negative (S m)) (Negative Z)
  ||| +0 <= +(n + 1)
  LTEBothPosWZero : LTE (Positive Z) (Positive (S n))
  ||| left >= right -> -left <= -right
  LTEBothNegLTE : LTE right left -> LTE (Negative left) (Negative right)
  ||| left >= right -> +left >= + right
  LTEBothPosLTE : Nat.LTE left right -> LTE (Positive left) (Positive right)
  ||| j = k -> j <= k
  LTEBothEq : Eq j k -> LTE j k


negZeroNotLTENegSucc : LTE (Negative 0) (Negative (S k)) -> Void
negZeroNotLTENegSucc (LTEBothEq EqZeroBothNeg) impossible
negZeroNotLTENegSucc (LTEBothEq EqZeroFirstPos) impossible
negZeroNotLTENegSucc (LTEBothEq EqZeroFirstNeg) impossible
negZeroNotLTENegSucc (LTEBothEq EqZeroBothPos) impossible
negZeroNotLTENegSucc (LTEBothEq EqSuccPos) impossible
negZeroNotLTENegSucc (LTEBothEq EqSuccNeg) impossible


posZeroNotLTENegSucc : LTE (Positive 0) (Negative (S k)) -> Void
posZeroNotLTENegSucc (LTEBothEq EqZeroBothNeg) impossible
posZeroNotLTENegSucc (LTEBothEq EqZeroFirstPos) impossible
posZeroNotLTENegSucc (LTEBothEq EqZeroFirstNeg) impossible
posZeroNotLTENegSucc (LTEBothEq EqZeroBothPos) impossible
posZeroNotLTENegSucc (LTEBothEq EqSuccPos) impossible
posZeroNotLTENegSucc (LTEBothEq EqSuccNeg) impossible

posSuccNotLTENeg : LTE (Positive (S j)) (Negative k) -> Void
posSuccNotLTENeg (LTEBothEq EqZeroBothNeg) impossible
posSuccNotLTENeg (LTEBothEq EqZeroFirstPos) impossible
posSuccNotLTENeg (LTEBothEq EqZeroFirstNeg) impossible
posSuccNotLTENeg (LTEBothEq EqZeroBothPos) impossible
posSuccNotLTENeg (LTEBothEq EqSuccPos) impossible
posSuccNotLTENeg (LTEBothEq EqSuccNeg) impossible


posSuccNotLTEZero : LTE (Positive (S j)) (Positive 0) -> Void
posSuccNotLTEZero (LTEBothPosLTE LTEZero) impossible
posSuccNotLTEZero (LTEBothPosLTE (LTESucc _)) impossible
posSuccNotLTEZero (LTEBothEq EqZeroBothNeg) impossible
posSuccNotLTEZero (LTEBothEq EqZeroFirstPos) impossible
posSuccNotLTEZero (LTEBothEq EqZeroFirstNeg) impossible
posSuccNotLTEZero (LTEBothEq EqZeroBothPos) impossible
posSuccNotLTEZero (LTEBothEq EqSuccPos) impossible
posSuccNotLTEZero (LTEBothEq EqSuccNeg) impossible

negSuccNotGTEImposs : (contra : GTE l k -> Void) -> LTE (Negative (S l)) (Negative (S k)) -> Void
negSuccNotGTEImposs contra (LTEBothNegLTE (LTESucc x)) = contra x
negSuccNotGTEImposs {l = l} {k = l} contra (LTEBothEq EqSuccNeg) = contra lteRefl

posSuccNotLTEImposs : (contra : LTE l k -> Void) -> LTE (Positive (S l)) (Positive (S k)) -> Void
posSuccNotLTEImposs contra (LTEBothPosLTE (LTESucc x)) = contra x
posSuccNotLTEImposs {l = l} {k = l} contra (LTEBothEq EqSuccPos) = contra lteRefl

isLTE : (i, j : ConsInt) -> Dec (i `LTE` j)
isLTE (Negative Z) (Negative Z) = Yes (LTEBothEq EqZeroBothNeg)
isLTE (Negative Z) (Negative (S k)) = No negZeroNotLTENegSucc
isLTE (Negative (S j)) (Negative Z) = Yes LTEBothNegWZero
isLTE (Negative (S l)) (Negative (S k)) = case isGTE l k of
                                               (Yes prf) => Yes (LTEBothNegLTE (LTESucc prf))
                                               (No contra) => No (negSuccNotGTEImposs contra)
isLTE (Negative n) (Positive k) = Yes LTENegPos
isLTE (Positive Z) (Negative Z) = Yes (LTEBothEq EqZeroFirstPos)
isLTE (Positive Z) (Negative (S k)) = No posZeroNotLTENegSucc
isLTE (Positive (S j)) (Negative k) = No posSuccNotLTENeg
isLTE (Positive Z) (Positive Z) = Yes (LTEBothEq EqZeroBothPos)
isLTE (Positive Z) (Positive (S k)) = Yes LTEBothPosWZero
isLTE (Positive (S j)) (Positive Z) = No posSuccNotLTEZero
isLTE (Positive (S l)) (Positive (S k)) = case isLTE l k of
                                               (Yes prf) => Yes (LTEBothPosLTE (LTESucc prf))
                                               (No contra) => No (posSuccNotLTEImposs contra)

GTE : ConsInt -> ConsInt -> Type
GTE h i = LTE i h

isGTE : (h, i : ConsInt) -> Dec (h `GTE` i)
isGTE h i = isLTE i h

data LT : (h, i : ConsInt) -> Type where
  LTPosZeroPosSucc : LT (Positive Z) (Positive (S m))
  LTNegPosSucc : LT (Negative (S m)) (Positive i)
  LTNegLTSwap : Nat.LT m n -> LT (Negative n) (Negative m)
  LTPosLT : Nat.LT m n -> LT (Positive m) (Positive n)
  LTNotEqLTE : ConstructedInt.NotEq h i -> LTE h i -> LT h i



notLTEImplNotEq : (contra : ConstructedInt.LTE h i -> Void) -> NotEq h i
notLTEImplNotEq {h} {i} contra = case ConstructedInt.isEq h i of
                                      (Yes prf) => void (contra (LTEBothEq prf))
                                      (No contra1) => contra1

-- Basically a computer generated proof, with lots of case splits and searches.  Hopefully Idris 2 will do this sort of thing better.  Alternatively, maybe I can find out what I'm doing wrong.
isLTAndIsEqImposs : (prf1 : Eq h i) -> (prf : LT h i) -> NotEq h i
isLTAndIsEqImposs EqZeroBothNeg (LTNegLTSwap LTEZero) impossible
isLTAndIsEqImposs EqZeroBothNeg (LTNegLTSwap (LTESucc _)) impossible
isLTAndIsEqImposs EqZeroBothNeg (LTNotEqLTE f (LTEBothNegLTE LTEZero)) = \__pi_arg => f EqZeroBothNeg
isLTAndIsEqImposs EqZeroBothNeg (LTNotEqLTE f (LTEBothEq EqZeroBothNeg)) = \__pi_arg => f EqZeroBothNeg
isLTAndIsEqImposs EqZeroFirstPos (LTNotEqLTE f (LTEBothEq EqZeroFirstPos)) = \__pi_arg => f EqZeroFirstPos
isLTAndIsEqImposs EqZeroFirstNeg (LTNotEqLTE f LTENegPos) = \__pi_arg => f EqZeroFirstNeg
isLTAndIsEqImposs EqZeroFirstNeg (LTNotEqLTE f (LTEBothEq EqZeroFirstNeg)) = \__pi_arg => f EqZeroFirstNeg
isLTAndIsEqImposs EqZeroBothPos (LTPosLT LTEZero) impossible
isLTAndIsEqImposs EqZeroBothPos (LTPosLT (LTESucc _)) impossible
isLTAndIsEqImposs EqZeroBothPos (LTNotEqLTE f (LTEBothPosLTE LTEZero)) = \__pi_arg => f EqZeroBothPos
isLTAndIsEqImposs EqZeroBothPos (LTNotEqLTE f (LTEBothEq EqZeroBothPos)) = \__pi_arg => f EqZeroBothPos
isLTAndIsEqImposs EqSuccPos (LTPosLT (LTESucc x)) = \__pi_arg => lTELeftNotSuccOfRight x
isLTAndIsEqImposs EqSuccPos (LTNotEqLTE f (LTEBothPosLTE (LTESucc x))) = \__pi_arg => f EqSuccPos
isLTAndIsEqImposs EqSuccPos (LTNotEqLTE f (LTEBothEq EqSuccPos)) = \__pi_arg => f EqSuccPos
isLTAndIsEqImposs EqSuccNeg (LTNegLTSwap (LTESucc x)) = \__pi_arg => lTELeftNotSuccOfRight x
isLTAndIsEqImposs EqSuccNeg (LTNotEqLTE f (LTEBothNegLTE x)) = \__pi_arg => f EqSuccNeg
isLTAndIsEqImposs EqSuccNeg (LTNotEqLTE f (LTEBothEq EqSuccNeg)) = \__pi_arg => f EqSuccNeg

lTImplNotEq : (prf : ConstructedInt.LT h i) -> NotEq h i
lTImplNotEq {h} {i} prf = case isEq h i of
                               (Yes prf1) => isLTAndIsEqImposs prf1 prf
                               (No contra) => contra


lTEAndLTImplNotEq : (prf : ConstructedInt.LTE h i) -> (x : LT h i) -> NotEq h i
lTEAndLTImplNotEq {h} {i} prf x = case isLTE h i of
                               (Yes prf) => ?lTEAndLTImplNotEq_rhs_1
                               (No contra) => notLTEImplNotEq contra

makeNotEq : (contra : NotEq h i -> Void) -> (prf : LTE h i) -> (x : LT h i) -> Eq h i -> Void
makeNotEq contra prf x y = contra (lTEAndLTImplNotEq prf x)

lteLtImplNotEq : (prf : ConstructedInt.LTE h i) -> (x : LT h i) -> NotEq h i
lteLtImplNotEq {h} {i} prf x = case isNotEq h i of
                            (Yes prf1) => prf1
                            (No contra) => makeNotEq contra prf x

lTNotNotEq : (contra : ConstructedInt.NotEq h i -> Void) -> (prf : LTE h i) -> LT h i -> Void
lTNotNotEq contra prf x = contra (lteLtImplNotEq prf x)


isLT : (h, i : ConsInt) -> Dec (h `LT` i)
isLT h i = case isLTE h i of
                (Yes prf) => (case isNotEq h i of
                                   (Yes prf1) => Yes (LTNotEqLTE prf1 prf)
                                   (No contra) => No (lTNotNotEq contra prf))
                (No contra) => ?hole_2

-- Testing with types

%access private

fourMinusTenIsNegativeSix : Eq ((Positive 4) - (Positive 10)) (Negative 6)
fourMinusTenIsNegativeSix = EqSuccNeg

fourMinusNegativeTenIsNotNegativeSix : Eq ((Positive 4) - (Negative 10)) (Negative 6) -> Void
fourMinusNegativeTenIsNotNegativeSix EqZeroBothNeg impossible
fourMinusNegativeTenIsNotNegativeSix EqZeroFirstPos impossible
fourMinusNegativeTenIsNotNegativeSix EqZeroFirstNeg impossible
fourMinusNegativeTenIsNotNegativeSix EqZeroBothPos impossible
fourMinusNegativeTenIsNotNegativeSix EqSuccPos impossible
fourMinusNegativeTenIsNotNegativeSix EqSuccNeg impossible

fourMinusTenIsLessThanNegativeTwo : LTE ((Positive 4) - (Positive 10)) (Negative 2)
fourMinusTenIsLessThanNegativeTwo = LTEBothNegLTE (LTESucc (LTESucc LTEZero))

fourMinusTenIsNotLessThanNegativeFour : LTE ((Positive 4) - (Positive 5)) (Negative 4) -> Void
fourMinusTenIsNotLessThanNegativeFour (LTEBothNegLTE (LTESucc LTEZero)) impossible
fourMinusTenIsNotLessThanNegativeFour (LTEBothNegLTE (LTESucc (LTESucc _))) impossible
fourMinusTenIsNotLessThanNegativeFour (LTEBothEq EqZeroBothNeg) impossible
fourMinusTenIsNotLessThanNegativeFour (LTEBothEq EqZeroFirstPos) impossible
fourMinusTenIsNotLessThanNegativeFour (LTEBothEq EqZeroFirstNeg) impossible
fourMinusTenIsNotLessThanNegativeFour (LTEBothEq EqZeroBothPos) impossible
fourMinusTenIsNotLessThanNegativeFour (LTEBothEq EqSuccPos) impossible
fourMinusTenIsNotLessThanNegativeFour (LTEBothEq EqSuccNeg) impossible

aNegativeTimesANegativeIsAPositive : LTE (Positive Z) ((Negative n) * (Negative m))
aNegativeTimesANegativeIsAPositive = LTEBothPosLTE LTEZero
