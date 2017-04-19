module Rational

import Setoid
import SInt
import SIntImplementation

%access public export

record Rational where
    constructor MkRat
    num: SInt
    den: SInt
    isNotDivisionByZero : (Not (den $= 0))


mulNotZero : {a : SInt} -> {b: SInt} -> (Not (a $= 0)) -> (Not (b $= 0)) -> (Not (a * b $= 0))
mulNotZero x y = ?mulNotZero_rhs_1

oneNotZero : Not (1 $= 0)
oneNotZero = nn where
    ee : (Z = (S Z))
    ee = ?xx

    nn : Not (1 $= 0)
    nn = absurd ee

absNotZero : Not (den $= 0) -> Not ((abs den) $= 0)
absNotZero x = ?aabsurd


implementation Num Rational where
    (*) (MkRat num1 den1 p1) (MkRat num2 den2 p2) = MkRat (num1 * num2) (den1 * den2) (mulNotZero p1 p2)

    (+) (MkRat num1 den1 p1) (MkRat num2 den2 p2) = MkRat (num1 * den2 + num2 * den1) (den1 * den2) (mulNotZero p1 p2)

    fromInteger x = MkRat (fromInteger x) (fromInteger 1) oneNotZero


implementation Neg Rational where
    negate (MkRat num den p1) = MkRat (negate num) den p1

    (-) r1 r2 = r1 + (negate r2)

    abs (MkRat num den p1) = MkRat (abs num) (abs den) (absNotZero p1)


data RatEq : Rational -> Rational -> Type where
    RatRefl : (eq : (num1 * den2) $= (num2 * den1)) -> RatEq (MkRat num1 den1 p1) (MkRat num2 den2 p2)



reflxRatEq : Reflx RatEq
reflxRatEq (MkRat a b p1) = RatRefl (reflxSIntEq (a * b))


symmRatEq : Symm RatEq
symmRatEq (MkRat a1 b1 p1) (MkRat a2 b2 p2) (RatRefl e) = RatRefl (symmSIntEq (a1 * b2) (a2 * b1) e)





mulRefl : {a : SInt} -> {b : SInt} -> {c: SInt} -> {d: SInt} -> (a $= b) -> (c $= d) -> (a * c) $= (b * d)
mulRefl (SRefl eq1) (SRefl eq2) = let

    in SRefl ?xxx1_1



transRatEq : Trans RatEq
transRatEq (MkRat a1 b1 p1) (MkRat a2 b2 p2) (MkRat a3 b3 p3) (RatRefl e1) (RatRefl e2) = RatRefl trs where

    -- (a1 * b2) * (a2 * b3) = (a2 * b1) * (a3 * b2)
    e3 : (a1 * b2) * (a2 * b3) $= (a2 * b1) * (a3 * b2)
    e3 = mulRefl e1 e2

    -- Trim b2 from right side of e3
    tr_b2_r : (a2 * b1) * (a3 * b2) $= ((a2 * b1) * a3) * b2
    tr_b2_r = SIntMultAssociative (a2 * b1) a3 b2

    -- reverse left side of e3
    tr_b2_comm : (a1 * b2) * (a2 * b3) $= (a2 * b3) * (a1 * b2)
    tr_b2_comm = SIntMultCommutative (a1 * b2) (a2 * b3)


    -- ~ from left side of e3
    tr_b2_l : (a2 * b3) * (a1 * b2) $= ((a2 * b3) * a1) * b2
    tr_b2_l = SIntMultAssociative  (a2 * b3) a1 b2


    -- match left and right side
    tr_b2_match : ((a2 * b3) * a1) * b2 $= ((a2 * b1) * a3) * b2
    tr_b2_match = transSIntEq (((a2 * b3) * a1) * b2) ((a1 * b2) * (a2 * b3)) (((a2 * b1) * a3) * b2)
        (transSIntEq (((a2 * b3) * a1) * b2) ((a2 * b3) * (a1 * b2)) ((a1 * b2) * (a2 * b3))
            (symmSIntEq ((a2 * b3) * (a1 * b2)) (((a2 * b3) * a1) * b2) tr_b2_l)
            (symmSIntEq ((a1 * b2) * (a2 * b3)) ((a2 * b3) * (a1 * b2)) tr_b2_comm)
        )
        (transSIntEq ((a1 * b2) * (a2 * b3)) ((a2 * b1) * (a3 * b2)) (((a2 * b1) * a3) * b2) e3 tr_b2_r)


    -- trim b2
    tr_b2 : (a2 * b3) * a1 $= (a2 * b1) * a3
    tr_b2 = SIntMultRightCancel ((a2 * b3) * a1) ((a2 * b1) * a3) b2 tr_b2_match




    trs : (a1 * b3) $= (a3 * b1)
    trs = ?trs_rhs1


RationalSetoid : Setoid
RationalSetoid = MkSetoid Rational RatEq (EqProof RatEq reflxRatEq symmRatEq transRatEq)
