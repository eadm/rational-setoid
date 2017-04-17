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
    RatRefl : (eq : (num1 * den2) $= (num2 * den1)) -> RatEq (MkRat num1 den1) (MkRat num2 den2)



reflxRatEq : Reflx RatEq
reflxRatEq (MkRat a b) = RatRefl (reflxSIntEq (a * b))


symmRatEq : Symm RatEq
symmRatEq (MkRat a1 b1) (MkRat a2 b2) (RatRefl e) = RatRefl (symmSIntEq (a1 * b2) (a2 * b1) e)





mulRefl : {u : SInt} -> {v : SInt} -> {x: SInt} -> {y: SInt} -> (u $= v) -> (x $= y) -> (u * x) $= (v * y)
mulRefl (SRefl eq1) (SRefl eq2) = let

    in SRefl ?xxx1_1



transRatEq : Trans RatEq
transRatEq (MkRat a1 b1) (MkRat a2 b2) (MkRat a3 b3) (RatRefl e1) (RatRefl e2) = RatRefl trs where

    -- (a1 * b2) * (a2 * b3) = (a2 * b1) * (a3 * b2)
    e3 : (a1 * b2) * (a2 * b3) $= (a2 * b1) * (a3 * b2)
    e3 = mulRefl e1 e2

    trs : (a1 * b3) $= (a3 * b1)
    trs = ?trs_rhs1


RationalSetoid : Setoid
RationalSetoid = MkSetoid Rational RatEq (EqProof RatEq reflxRatEq symmRatEq transRatEq)
