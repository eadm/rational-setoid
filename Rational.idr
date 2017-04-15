module Rational

import Setoid
import SInt

%access public export

record Rational where
    constructor MkRat
    num: SInt
    den: SInt
    -- isNotDivisionByZero : (Not (SIntEq den 0))

data RatEq : Rational -> Rational -> Type where
    RatRefl : (eq : (num1 * den2) = (num2 * den1)) -> RatEq (MkRat num1 den1) (MkRat num2 den2)


reflxRatEq : Reflx RatEq
reflxRatEq (MkRat a b) = RatRefl Refl


symmRatEq : Symm RatEq
symmRatEq (MkRat a1 b1) (MkRat a2 b2) (RatRefl e) = RatRefl (sym e)


transRatEq : Trans RatEq
transRatEq (MkRat a1 b1) (MkRat a2 b2) (MkRat a3 b3) (RatRefl e1) (RatRefl e2) = RatRefl trs where
    trs : (a1 * b3) = (a3 * b1)
    trs = ?trs_rhs1


RationalSetoid : Setoid
RationalSetoid = MkSetoid Rational RatEq (EqProof RatEq reflxRatEq symmRatEq transRatEq)
