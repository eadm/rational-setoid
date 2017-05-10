module Rational


import Setoid
import SInt
import SIntImplementation

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



    trs : a1 * (S d3) + b3 * (S d1) = a3 * (S d1) + b1 * (S d3)
    trs = ?trs_rhs1


RationalSetoid : Setoid
RationalSetoid = MkSetoid Rational RatEq (EqProof RatEq reflxRatEq symmRatEq transRatEq)
