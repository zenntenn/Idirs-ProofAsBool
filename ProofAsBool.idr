module ProofAsBool

%access public export
%default total

||| Proof based underlying implementation of the if ... then ... else ... syntax
||| @ b the condition on the if
||| @ t the value if b is Yes
||| @ e the falue if b is No
ifThenElse : (b : Dec prop) -> (t : Lazy a) -> (e : Lazy a) -> a
ifThenElse (Yes prf) t e = t
ifThenElse (No contra) t e = e


||| Proof based logical AND
||| @ a the first proof
||| @ b the second proof
AND : (a : Dec prop) -> (b : Dec prop) -> Dec prop
AND (Yes prf1) (Yes _) = Yes prf1
AND _ (No contra) = No contra
AND (No contra) _ = No contra

||| Proof based logical OR
||| @ a the first proof
||| @ b the second proof
OR : (a : Dec prop) -> (b : Dec prop) -> Dec prop
OR (Yes prf) _ = Yes prf
OR _ (Yes prf) = Yes prf
OR (No contra) (No _) = No contra

-- I'm prety sure that a logical NOT in this fashion would violate intuitionistic logic, so I've given up on trying to do NOT or XOR or whatnot

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


||| A decision procedure for `DecEq Nat`
||| @ m the first number
||| @ n the second number
isEqNat : (m : Nat) -> (n : Nat) -> Dec (m = n)
isEqNat m n = decEq m n

||| Proofs that `m` is not equal to `n`
||| @ m the first number
||| @ n the second number
data NotEq : (m, n : Nat) -> Type where
  ||| Zero is the smallest Nat
  NotEqZeroRight : NotEq Z    (S right)
  NotEqZeroLeft : NotEq (S left) Z
  ||| If n /= m, then n + 1 /= m + 1
  NotEqSucc : NotEq left right -> NotEq (S left) (S right)

||| Not (Z /= Z)
zeroNotNotEqZero : NotEq 0 0 -> Void
zeroNotNotEqZero NotEqZeroRight impossible
zeroNotNotEqZero (NotEqSucc _) impossible

||| If two numbers are not equal, then neither are their predecessors
fromNotEqSucc : NotEq (S k) (S j) -> NotEq k j
fromNotEqSucc (NotEqSucc x) = x

||| A decision procedure for `NotEq`
||| @ m the first number
||| @ n the second number
isNotEq : (m : Nat) -> (n : Nat) -> Dec (NotEq m n)
isNotEq Z Z = No zeroNotNotEqZero
isNotEq Z (S k) = Yes NotEqZeroRight
isNotEq (S k) Z = Yes NotEqZeroLeft
isNotEq (S k) (S j) with (isNotEq k j)
  isNotEq (S k) (S j) | (Yes prf) = Yes (NotEqSucc prf)
  isNotEq (S k) (S j) | (No contra) = No (contra . fromNotEqSucc)
