module MoreNatProofs

%access public export
%default total

||| A decision procedure for `DecEq Nat`
||| @ m the first number
||| @ n the second number
isEq : (m : Nat) -> (n : Nat) -> Dec (m = n)
isEq m n = decEq m n

eQImpliesEq : {m, n : Nat} -> (m = n) -> (n = m)
eQImpliesEq {m = n} {n = n} Refl = Refl

eQAndNotEqImpossible : {n, k : Nat} -> (contra1 : (n = k) -> Void) -> (n = k) -> a
eQAndNotEqImpossible {n} {k} contra1 prf = void (contra1 prf)

||| Proofs that `m` is not equal to `n`
||| @ m the first number
||| @ n the second number
NotEq : (m, n : Nat) -> Type
NotEq m n = Not (m=n)

||| Not (m = n) implies m /= n
notEqImpliesNotEq : (contra : (m = n) -> Void) -> ((m = n) -> Void)
notEqImpliesNotEq contra Refl = contra Refl

||| (m = n) implies Not (m /= n)
eqImpliesNotNotEq : (prf : m = n) -> (((m = n) -> Void) -> Void)
eqImpliesNotNotEq Refl f = f Refl

||| A decision procedure for `NotEq`
isNotEq : (m : Nat) -> (n : Nat) -> Dec (NotEq m n)
isNotEq m n = case (isEq m n) of
                   (Yes prf) => No (eqImpliesNotNotEq prf)
                   (No contra) => Yes (notEqImpliesNotEq contra)


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

eqImpliesLTE : (n = k) -> LTE n k
eqImpliesLTE {n = Z} Refl = LTEZero
eqImpliesLTE {n = (S (S (S k)))} Refl = LTESucc (LTESucc (LTESucc (eqImpliesLTE Refl)))

eqABImpliesEqBA : (prf : n = k) -> k = n
eqABImpliesEqBA Refl = Refl

notLTEandEqImpossible : (contra : LTE n k -> Void) -> (prf : n = k) -> LTE k n
notLTEandEqImpossible contra prf = eqImpliesLTE (eqABImpliesEqBA prf)


gTImpliesLTE : (prf : GT n k) -> LTE k n
gTImpliesLTE {n = (S left)} {k = (S right)} (LTESucc x) = LTESucc (gTImpliesLTE x)

notGTImpliesLTE : Not (GT a b) -> LTE a b
notGTImpliesLTE {a = Z} _ = LTEZero
notGTImpliesLTE {b = Z} {a = S k} notGt = absurd (notGt (LTESucc LTEZero))
notGTImpliesLTE {b = S k} {a = S j} notGt = LTESucc (notLTImpliesGTE (notGt . LTESucc))

notLTEFlips : (contra : LTE n k -> Void) -> LTE k n
notLTEFlips {n} {k} contra = case isEq n k of
                                  (Yes prf) => notLTEandEqImpossible contra prf
                                  (No contra1) => (case isGT n k of
                                                        (Yes prf) => gTImpliesLTE prf
                                                        (No contra2) => gTImpliesLTE (void (contra (notGTImpliesLTE contra2))))
