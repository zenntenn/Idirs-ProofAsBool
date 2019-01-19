module IntegerProofs

%access public export
%default total

||| A decision procedure for `DecEq Integer`
||| @ m the first number
||| @ n the second number
isEq : (m : Integer) -> (n : Integer) -> Dec (m = n)
isEq m n = decEq m n

||| Proofs that `m` is not equal to `n`
||| @ m the first number
||| @ n the second number
NotEq : (m, n : Integer) -> Type
NotEq m n = Not (m=n)

||| Not (m = n) implies m /= n
notEqImpliesNotEq : (contra : (m = n) -> Void) -> ((m = n) -> Void)
notEqImpliesNotEq contra Refl = contra Refl

||| (m = n) implies Not (m /= n)
eqImpliesNotNotEq : (prf : m = n) -> (((m = n) -> Void) -> Void)
eqImpliesNotNotEq Refl f = f Refl

||| A decision procedure for `NotEq`
isNotEq : (m : Integer) -> (n : Integer) -> Dec (NotEq m n)
isNotEq m n = case (isEq m n) of
                   (Yes prf) => No (eqImpliesNotNotEq prf)
                   (No contra) => Yes (notEqImpliesNotEq contra)

smaller : (m : Integer) -> (n : Integer) -> Integer
smaller m n = case m <= n of
                   False => n
                   True => m

sameIntegerCheckPrf : (prf : m = n) -> (n : Integer) -> Integer
sameIntegerCheckPrf Refl n = n


sameInteger : (m : Integer) -> (n : Integer) -> (m=n) -> Integer
sameInteger m n prf = sameIntegerCheckPrf prf n

isTrue : (b : Bool) -> Dec (b = True)
isTrue b = decEq b True

isFalse : (b : Bool) -> Dec (b = False)
isFalse b = decEq b False

LT : (m : Integer) -> (n : Integer) -> Type
LT m n = case isTrue (m < n) of
               (Yes prf) => LT m n
               (No contra) => assert_unreachable

isLT : (m : Integer) -> (n : Integer) -> Dec (LT m n)
isLT m n = case LT of
                case_val => ?isLT_rhs
