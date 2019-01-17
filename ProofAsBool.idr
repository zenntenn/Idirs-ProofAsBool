module ProofAsBool

%access public export
%default total

||| A successor is always greater than or equal zero
succGTEzero : GTE (S k) Z
succGTEzero = LTEZero

||| Zero cannot be greater than or equal to a successor
zeroNotGTESucc : LTE (S k) 0 -> Void
zeroNotGTESucc LTEZero impossible
zeroNotGTESucc (LTESucc _) impossible

||| A decision procedure for `GTE`
isGTE : (m : Nat) -> (n : Nat) -> Dec (GTE m n)
isGTE Z Z = Yes LTEZero
isGTE Z (S k) = No zeroNotGTESucc
isGTE (S k) Z = Yes succGTEzero
isGTE (S k) (S j) with (isGTE k j)
  isGTE (S k) (S j) | (Yes prf) = Yes (LTESucc prf)
  isGTE (S k) (S j) | (No contra) = No (contra . fromLteSucc)

||| If n > m, then n + 1 > m + 1
GTSucc : (prf : LTE j k) -> LTE (S j) (S k)
GTSucc prf = LTESucc prf

||| Zero cannot be less than itself
zeroNotLTZero : LT 0 0 -> Void
zeroNotLTZero LTEZero impossible
zeroNotLTZero (LTESucc _) impossible

||| If 1 <= n + 1, then n + 1 > 0
succGTZero : LTE 1 (S k)
succGTZero = LTESucc LTEZero

||| A decision procedure for `GT`
isGT : (m : Nat) -> (n : Nat) -> Dec (GT m n)
isGT Z Z = No zeroNotLTZero
isGT Z (S k) = No zeroNotGTESucc
isGT (S k) Z = Yes succGTZero
isGT (S k) (S j) with (isGT k j)
  isGT (S k) (S j) | (Yes prf) = Yes (GTSucc prf)
  isGT (S k) (S j) | (No contra) = No (contra . fromLteSucc)

||| A decision procedure for `LT`
isLT : (m : Nat) -> (n : Nat) -> Dec (LT m n)
isLT Z Z = No zeroNotLTZero
isLT Z (S k) = Yes (LTESucc LTEZero)
isLT (S k) Z = No succNotLTEzero
isLT (S k) (S j) with (isLT k j)
  isLT (S k) (S j) | (Yes prf) = Yes (LTESucc prf)
  isLT (S k) (S j) | (No contra) = No (contra . fromLteSucc)

||| Proof based underlying implementation of the if ... then ... else ... syntax
||| @ b the condition on the if
||| @ t the value if b is Yes
||| @ e the falue if b is No
ifThenElse : (b : Dec prop) -> (t : Lazy a) -> (e : Lazy a) -> a
ifThenElse (Yes prf) t e = t
ifThenElse (No contra) t e = e
