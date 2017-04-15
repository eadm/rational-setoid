module SInt
import Setoid

%access public export

record SInt where
    constructor MkInt
    a : Nat
    b : Nat


implementation Num SInt where
    (+) (MkInt a1 b1) (MkInt a2 b2) = MkInt (a1 + a2) (b1 + b2)

    (*) (MkInt a1 b1) (MkInt a2 b2) = MkInt (a1 * a2 + b1 * b2) (a1 * b2 + a2 * b1)

    fromInteger x = if (x > 0)
        then MkInt (fromIntegerNat x) 0
        else MkInt 0 (fromIntegerNat (abs x))

fromIntegerSInt : Integer -> SInt
fromIntegerSInt x = fromInteger x

toIntegerSInt : SInt -> Integer
toIntegerSInt (MkInt a b) = (toIntegerNat a) - (toIntegerNat b)

Show SInt where
    show x = show (toIntegerSInt x)


data SIntEq : SInt -> SInt -> Type where
    SRefl : (eq : (a1 + b2) = (a2 + b1)) -> SIntEq (MkInt a1 b1) (MkInt a2 b2)


summRefl : (a1 = b1) -> (a2 = b2) -> (a1 + a2) = (b1 + b2)
summRefl e1 e2 = rewrite e1 in rewrite e2 in Refl


reflxSIntEq : Reflx SIntEq
reflxSIntEq (MkInt a b) = SRefl Refl


symmSIntEq : Symm SIntEq
symmSIntEq (MkInt a1 b1) (MkInt a2 b2) (SRefl e) = SRefl (sym e)


transSIntEq : Trans SIntEq
transSIntEq (MkInt a1 b1) (MkInt a2 b2) (MkInt a3 b3) (SRefl e1) (SRefl e2) = SRefl trs where
    trs : (a1 + b3) = (a3 + b1)
    trs = ?trs_rhs1


SIntSetoid : Setoid
SIntSetoid = MkSetoid SInt SIntEq (EqProof SIntEq reflxSIntEq symmSIntEq transSIntEq)
