module Rational

import Setoid
import SInt

%access public export

record Rational where
    constructor MkRat
    num: SInt
    den: SInt
    -- isNotDivisionByZero : (Not (SIntEq den 0))


implementation Num Rational where
    (*) (MkRat num1 den1) (MkRat num2 den2) = MkRat (num1 * num2) (den1 * den2)

    (+) (MkRat num1 den1) (MkRat num2 den2) = MkRat (num1 * den2 + num2 * den1) (den1 * den2)

    fromInteger x = MkRat (fromInteger x) (fromInteger 1)


implementation Neg Rational where
    negate (MkRat num den) = MkRat (negate num) den

    (-) r1 r2 = r1 + (negate r2)

    abs (MkRat num den) = MkRat (abs num) (abs den)


data RatEq : Rational -> Rational -> Type where
    RatRefl : (eq : SIntEq (num1 * den2) (num2 * den1)) -> RatEq (MkRat num1 den1) (MkRat num2 den2)



reflxRatEq : Reflx RatEq
reflxRatEq (MkRat a b) = RatRefl (reflxSIntEq (a * b))


symmRatEq : Symm RatEq
symmRatEq (MkRat a1 b1) (MkRat a2 b2) (RatRefl e) = RatRefl (symmSIntEq (a1 * b2) (a2 * b1) e)


transRatEq : Trans RatEq
transRatEq (MkRat a1 b1) (MkRat a2 b2) (MkRat a3 b3) (RatRefl e1) (RatRefl e2) = RatRefl trs where
    trs : SIntEq (a1 * b3) (a3 * b1)
    trs = ?trs_rhs1


RationalSetoid : Setoid
RationalSetoid = MkSetoid Rational RatEq (EqProof RatEq reflxRatEq symmRatEq transRatEq)
