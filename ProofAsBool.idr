module ProofAsBool

%access public export
%default total

zeroGTEzero : Type -> GTE 0 0
zeroGTEzero x = LTEZero

GTEZero : LTE (S k) 0 -> Void
GTEZero LTEZero impossible
GTEZero (LTESucc _) impossible

GTESucc : (prf : LTE j k) -> LTE (S j) (S k)
GTESucc LTEZero = LTESucc LTEZero
GTESucc (LTESucc x) = LTESucc (LTESucc x)

fromGteSucc : (contra : LTE j k -> Void) -> LTE (S j) (S k) -> LTE j k
fromGteSucc contra (LTESucc x) = x

succNotGTEzero : LTE 0 (S k)
succNotGTEzero = LTEZero

isGTE : (m : Nat) -> (n : Nat) -> Dec (GTE m n)
isGTE Z Z = Yes (zeroGTEzero (GTE 0 0))
isGTE Z (S k) = No GTEZero
isGTE (S k) Z = Yes succNotGTEzero
isGTE (S k) (S j) with (isGTE k j)
  isGTE (S k) (S j) | (Yes prf) = Yes (GTESucc prf)
  isGTE (S k) (S j) | (No contra) = No (contra . (fromGteSucc contra))


GTSucc : (prf : LTE j k) -> LTE (S j) (S k)
GTSucc prf = LTESucc prf

fromGtSucc : (contra : LTE j k -> Void) -> LTE (S j) (S k) -> LTE j k
fromGtSucc contra (LTESucc x) = x

zeroNotLTZero : LT 0 0 -> Void
zeroNotLTZero LTEZero impossible
zeroNotLTZero (LTESucc _) impossible

succNotGTzero : LTE 1 (S k)
succNotGTzero = LTESucc LTEZero

isGT : (m : Nat) -> (n : Nat) -> Dec (GT m n)
isGT Z Z = No zeroNotLTZero
isGT Z (S k) = No GTEZero
isGT (S k) Z = Yes succNotGTzero
isGT (S k) (S j) with (isGT k j)
  isGT (S k) (S j) | (Yes prf) = Yes (GTSucc prf)
  isGT (S k) (S j) | (No contra) = No (contra . (fromGtSucc contra))


succNotLTzero : LTE (S (S k)) 0 -> Void
succNotLTzero LTEZero impossible
succNotLTzero (LTESucc _) impossible

LTSucc : (prf : LTE (S k) j) -> LTE (S (S k)) (S j)
LTSucc (LTESucc x) = LTESucc (LTESucc x)

fromLtSucc : (contra : LTE (S k) j -> Void) -> LTE (S (S k)) (S j) -> LTE (S k) j
fromLtSucc contra (LTESucc x) = x

isLT : (m : Nat) -> (n : Nat) -> Dec (LT m n)
isLT Z Z = No zeroNotLTZero
isLT Z (S k) = Yes (LTESucc LTEZero)
isLT (S k) Z = No succNotLTzero
isLT (S k) (S j) with (isLT k j)
  isLT (S k) (S j) | (Yes prf) = Yes (LTSucc prf)
  isLT (S k) (S j) | (No contra) = No (contra . (fromLtSucc contra))


ifThenElse : Dec prop -> Lazy a -> Lazy a -> a
ifThenElse (Yes prf) y z = y
ifThenElse (No contra) y z = z
