module Rational


import Setoid
import SInt

%default total
%access public export

record Rational where
    constructor MkRat
    num: SInt
    den: Nat
    isNotDivisionByZero : (NatNZ den)


mulNotZero : {a : Nat} -> {b: Nat} -> (NatNZ a) -> (NatNZ b) -> (NatNZ (a * b))
mulNotZero (NNZ f) (NNZ g) = (NNZ (mnz f g)) where
    mnz : {a, b : Nat} -> Not (a = Z) -> Not (c = Z) -> Not (a * b = Z)
    mnz f' g' Relf impossible


oneNotZero : NatNZ (S Z)
oneNotZero = NNZ oneNotZero' where
    oneNotZero' : Not ((S Z) = Z)
    oneNotZero' Refl impossible


implementation Num Rational where
    (*) (MkRat num1 den1 p1) (MkRat num2 den2 p2) = MkRat (num1 * num2) (den1 * den2) (mulNotZero p1 p2)

    (+) (MkRat num1 den1 p1) (MkRat num2 den2 p2) = MkRat ((num1 $* den2) + (num2 $* den1)) (den1 * den2) (mulNotZero p1 p2)

    fromInteger x = MkRat (fromInteger x) (fromInteger 1) oneNotZero


implementation Neg Rational where
    negate (MkRat num den p1) = MkRat (negate num) den p1

    (-) r1 r2 = r1 + (negate r2)

    abs (MkRat num den p1) = MkRat (abs num) den p1


data RatEq : Rational -> Rational -> Type where
    RatRefl : (eq : (num1 $* den2) $= (num2 $* den1)) -> RatEq (MkRat num1 den1 p1) (MkRat num2 den2 p2)



reflxRatEq : Reflx RatEq
reflxRatEq (MkRat a b p1) = RatRefl (reflxSIntEq (a $* b))


symmRatEq : Symm RatEq
symmRatEq (MkRat a1 b1 p1) (MkRat a2 b2 p2) (RatRefl e) = RatRefl (symmSIntEq (a1 $* b2) (a2 $* b1) e)




transRatEq : Trans RatEq
transRatEq
(MkRat (MkInt a1 b1) d1 (NNZ p1))
(MkRat (MkInt a2 b2) d2 (NNZ p2))
(MkRat (MkInt a3 b3) d3 (NNZ p3))
(RatRefl (SRefl e1))
(RatRefl (SRefl e2)) = RatRefl (SRefl trs) where

    mlt3 : (a1 * d2 + b2 * d1) * d3  =  (a2 * d1 + b1 * d2) * d3
    mlt3 = rewrite e1 in Refl

    mlt3_distr : a1 * d2 * d3  +  b2 * d1 * d3  =  a2 * d1 * d3  + b1 * d2 * d3
    mlt3_distr =
        rewrite sym (multDistributesOverPlusLeft (a1 * d2) (b2 * d1) d3) in
        rewrite sym (multDistributesOverPlusLeft (a2 * d1) (b1 * d2) d3) in
        rewrite mlt3 in Refl

    mlt1 : (a2 * d3 + b3 * d2) * d1  =  (a3 * d2 + b2 * d3) * d1
    mlt1 = rewrite e2 in Refl

    mlt1_distr : a2 * d3 * d1  +  b3 * d2 * d1  =  a3 * d2 * d1  + b2 * d3 * d1
    mlt1_distr =
        rewrite sym (multDistributesOverPlusLeft (a2 * d3) (b3 * d2) d1) in
        rewrite sym (multDistributesOverPlusLeft (a3 * d2) (b2 * d3) d1) in
        rewrite mlt1 in Refl


    summ_1 : (a1 * d2 * d3  +  b2 * d1 * d3)  +  (a2 * d3 * d1  +  b3 * d2 * d1)  =  (a2 * d1 * d3  +  b1 * d2 * d3)  +  (a3 * d2 * d1  + b2 * d3 * d1)
    summ_1 = summRefl mlt3_distr mlt1_distr

    summ_r1 : (a1 * d2 * d3  +  b2 * d1 * d3  +  b3 * d2 * d1)  +  a2 * (d3 * d1)  =  (a3 * d2 * d1  + b2 * d3 * d1  +  b1 * d2 * d3)  +  a2 * (d1 * d3)
    summ_r1 =
        rewrite sym (plusAssociative (a3 * d2 * d1  + b2 * d3 * d1) (b1 * d2 * d3) (a2 * (d1 * d3))) in
        rewrite plusCommutative (b1 * d2 * d3) (a2 * (d1 * d3)) in

        rewrite sym (plusAssociative (a1 * d2 * d3  +  b2 * d1 * d3) (b3 * d2 * d1) (a2 * (d3 * d1))) in
        rewrite plusCommutative (b3 * d2 * d1) (a2 * (d3 * d1)) in

        rewrite plusCommutative (a3 * d2 * d1  +  b2 * d3 * d1) (a2 * (d1 * d3)  +  b1 * d2 * d3) in

        rewrite (multAssociative a2 d1 d3) in
        rewrite (multAssociative a2 d3 d1) in
        rewrite summ_1 in Refl

    summ_r1_5 : (a1 * d2 * d3  +  b2 * d1 * d3  +  b3 * d2 * d1)  +  a2 * (d3 * d1) = (a1 * d2 * d3  +  b2 * d1 * d3  +  b3 * d2 * d1)  +  a2 * (d1 * d3)
    summ_r1_5 = rewrite multCommutative d3 d1 in Refl

    summ_r2 : (a1 * d2 * d3  +  b2 * d1 * d3  +  b3 * d2 * d1)  +  a2 * (d1 * d3)  =  (a3 * d2 * d1  +  b2 * d3 * d1  +  b1 * d2 * d3)  +  a2 * (d1 * d3)
    summ_r2 = trans (sym summ_r1_5) summ_r1

    summ_2 : (a1 * d2 * d3  +  b2 * d1 * d3  +  b3 * d2 * d1)  =  (a3 * d2 * d1  +  b2 * d3 * d1  +  b1 * d2 * d3)
    summ_2 = plusRightCancel (a1 * d2 * d3  +  b2 * d1 * d3  +  b3 * d2 * d1)  (a3 * d2 * d1  +  b2 * d3 * d1  +  b1 * d2 * d3) (a2 * (d1 * d3)) summ_r2


    summ_2_l1 : (a1 * d2 * d3  +  b2 * d1 * d3  +  b3 * d2 * d1) = (a1 * d2 * d3  +  b3 * d2 * d1  +  b2 * (d1 * d3))
    summ_2_l1 =
        rewrite sym (plusAssociative (a1 * d2 * d3) (b3 * d2 * d1) (b2 * (d1 * d3))) in
        rewrite plusCommutative (b3 * d2 * d1) (b2 * (d1 * d3)) in
        rewrite plusAssociative (a1 * d2 * d3) (b2 * (d1 * d3)) (b3 * d2 * d1) in
        rewrite multAssociative b2 d1 d3 in Refl


    summ_2_r1 : (a3 * d2 * d1  +  b2 * d3 * d1  +  b1 * d2 * d3) = (a3 * d2 * d1  +  b1 * d2 * d3  +  b2 * (d1 * d3))
    summ_2_r1 =
        rewrite sym (plusAssociative (a3 * d2 * d1) (b1 * d2 * d3) (b2 * (d1 * d3))) in
        rewrite plusCommutative (b1 * d2 * d3) (b2 * (d1 * d3)) in
        rewrite plusAssociative (a3 * d2 * d1) (b2 * (d1 * d3)) (b1 * d2 * d3) in
        rewrite multCommutative d1 d3 in
        rewrite multAssociative b2 d3 d1 in Refl

    summ_2_r : (a1 * d2 * d3  +  b3 * d2 * d1  +  b2 * (d1 * d3))  =  (a3 * d2 * d1  +  b1 * d2 * d3  +  b2 * (d1 * d3))
    summ_2_r = trans (trans (sym summ_2_l1) summ_2) summ_2_r1


    summ_3 : a1 * d2 * d3  +  b3 * d2 * d1  =  a3 * d2 * d1  +  b1 * d2 * d3
    summ_3 = plusRightCancel (a1 * d2 * d3  +  b3 * d2 * d1) (a3 * d2 * d1  +  b1 * d2 * d3) (b2 * (d1 * d3)) summ_2_r


    summ_3_l1 : a1 * d2 * d3  +  b3 * d2 * d1  =  (a1 * d3 + b3 * d1)  *  d2
    summ_3_l1 =
        rewrite multDistributesOverPlusLeft (a1 * d3) (b3 * d1) d2 in

        rewrite sym (multAssociative b3 d1 d2) in
        rewrite multCommutative d1 d2 in
        rewrite multAssociative b3 d2 d1 in

        rewrite sym (multAssociative a1 d3 d2) in
        rewrite multCommutative d3 d2 in
        rewrite multAssociative a1 d2 d3 in Refl


    summ_3_r1 : a3 * d2 * d1  +  b1 * d2 * d3  =  (a3 * d1  +  b1 * d3)  *  d2
    summ_3_r1 =
        rewrite multDistributesOverPlusLeft (a3 * d1) (b1 * d3) d2 in

        rewrite sym (multAssociative b1 d3 d2) in
        rewrite multCommutative d3 d2 in
        rewrite multAssociative b1 d2 d3 in

        rewrite sym (multAssociative a3 d1 d2) in
        rewrite multCommutative d1 d2 in
        rewrite multAssociative a3 d2 d1 in Refl


    summ_4 : (a1 * d3  +  b3 * d1)  *  d2  =  (a3 * d1  +  b1 * d3)  *  d2
    summ_4 = trans (trans (sym summ_3_l1) summ_3) summ_3_r1


    trs : a1 * d3 + b3 * d1  =  a3 * d1 + b1 * d3
    trs = multRightCancel (a1 * d3 + b3 * d1) (a3 * d1 + b1 * d3) d2 p2 summ_4


RationalSetoid : Setoid
RationalSetoid = MkSetoid Rational RatEq (EqProof RatEq reflxRatEq symmRatEq transRatEq)
