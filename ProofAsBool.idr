module ProofAsBool

%access public export
%default total

zeroGTEzero : Type -> GTE 0 0
zeroGTEzero x = LTEZero

||| If n >= m, then n + 1 >= m + 1
GTESucc : (prf : LTE j k) -> LTE (S j) (S k)
GTESucc LTEZero = LTESucc LTEZero
GTESucc (LTESucc x) = LTESucc (LTESucc x)

||| If two numbers are ordered, their predecessors are too
fromGteSucc : (contra : LTE j k -> Void) -> LTE (S j) (S k) -> LTE j k
fromGteSucc contra (LTESucc x) = x

||| A successor is always greater than or equal zero
succGTEzero : LTE 0 (S k)
succGTEzero = LTEZero

||| Zero cannot be greater than or equal to a successor
zeroNotGTESucc : LTE (S k) 0 -> Void
zeroNotGTESucc LTEZero impossible
zeroNotGTESucc (LTESucc _) impossible

||| A decision procedure for `GTE`
isGTE : (m : Nat) -> (n : Nat) -> Dec (GTE m n)
isGTE Z Z = Yes (zeroGTEzero (GTE 0 0))
isGTE Z (S k) = No zeroNotGTESucc
isGTE (S k) Z = Yes succGTEzero
isGTE (S k) (S j) with (isGTE k j)
  isGTE (S k) (S j) | (Yes prf) = Yes (GTESucc prf)
  isGTE (S k) (S j) | (No contra) = No (contra . (fromGteSucc contra))

||| If n > m, then n + 1 > m + 1
GTSucc : (prf : LTE j k) -> LTE (S j) (S k)
GTSucc prf = LTESucc prf


fromGtSucc : (contra : LTE j k -> Void) -> LTE (S j) (S k) -> LTE j k
fromGtSucc contra (LTESucc x) = x

zeroNotLTZero : LT 0 0 -> Void
zeroNotLTZero LTEZero impossible
zeroNotLTZero (LTESucc _) impossible

succNotGTzero : LTE 1 (S k)
succNotGTzero = LTESucc LTEZero

||| A decision procedure for `GT`
isGT : (m : Nat) -> (n : Nat) -> Dec (GT m n)
isGT Z Z = No zeroNotLTZero
isGT Z (S k) = No zeroNotGTESucc
isGT (S k) Z = Yes succNotGTzero
isGT (S k) (S j) with (isGT k j)
  isGT (S k) (S j) | (Yes prf) = Yes (GTSucc prf)
  isGT (S k) (S j) | (No contra) = No (contra . (fromGtSucc contra))


succNotLTzero : LT (S k) 0 -> Void




LTSucc : (prf : LTE (S k) j) -> LTE (S (S k)) (S j)
LTSucc (LTESucc x) = LTESucc (LTESucc x)

fromLtSucc : (contra : LTE (S k) j -> Void) -> LTE (S (S k)) (S j) -> LTE (S k) j
fromLtSucc contra (LTESucc x) = x

||| A decision procedure for `LT`
isLT : (m : Nat) -> (n : Nat) -> Dec (LT m n)
isLT Z Z = No zeroNotLTZero
isLT Z (S k) = Yes (LTESucc LTEZero)
isLT (S k) Z = No succNotLTzero
isLT (S k) (S j) with (isLT k j)
  isLT (S k) (S j) | (Yes prf) = Yes (LTSucc prf)
  isLT (S k) (S j) | (No contra) = No (contra . (fromLtSucc contra))

||| Proof based underlying implementation of the if ... then ... else ... syntax
||| @ b the condition on the if
||| @ t the value if b is Yes
||| @ e the falue if b is No
ifThenElse : (b : Dec prop) -> (t : Lazy a) -> (e : Lazy a) -> a
ifThenElse (Yes prf) t e = t
ifThenElse (No contra) t e = e
