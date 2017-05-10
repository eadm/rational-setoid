module SInt
import Setoid

%default total
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


implementation Neg SInt where
    negate (MkInt a b) = MkInt b a

    (-) s1 s2 = s1 + (negate s2)

    abs s@(MkInt a b) = if a > b then s else (MkInt b a)


mulSIntByNat : SInt -> Nat -> SInt
mulSIntByNat (MkInt a b) k = MkInt (a * k) (b * k)

infix 9 $*

($*) : SInt -> Nat -> SInt
($*) = mulSIntByNat

data NatNZ : Nat -> Type where
    NNZ : (Not (a = 0)) -> NatNZ a


fromIntegerSInt : Integer -> SInt
fromIntegerSInt x = fromInteger x

toIntegerSInt : SInt -> Integer
toIntegerSInt (MkInt a b) = (toIntegerNat a) - (toIntegerNat b)


Show SInt where
    show x = show (toIntegerSInt x)


data SIntEq : SInt -> SInt -> Type where
    SRefl : (eq : (a1 + b2) = (a2 + b1)) -> SIntEq (MkInt a1 b1) (MkInt a2 b2)


infix 5 $=

($=) : SInt -> SInt -> Type
($=) = SIntEq

summRefl : {a1 : Nat} -> {b1 : Nat} -> {a2: Nat} -> {b2: Nat} -> (a1 = b1) -> (a2 = b2) -> (a1 + a2) = (b1 + b2)
summRefl e1 e2 = rewrite e1 in rewrite e2 in Refl


multRightCancel : (a, b, c : Nat)  ->  (Not (c = 0))  ->  (a * c) = (b * c)  ->  a = b
multRightCancel a b Z nz p = void (nz Refl)
multRightCancel Z Z (S k) nz p = Refl
multRightCancel Z (S j) (S k) nz p = absurd p
multRightCancel (S j) Z (S k) nz p = absurd (sym p)
multRightCancel (S j) (S i) (S k) nz p =
    plusConstantLeft j i (S Z) (multRightCancel j i (S k) nz p2) where

    p1 : (1 * (S k) + j * (S k)) = (1 * (S k) + i * (S k))
    p1 =
        rewrite sym (multDistributesOverPlusLeft 1 j (S k)) in
        rewrite sym (multDistributesOverPlusLeft 1 i (S k)) in
        p

    p2 : j * (S k) = i * (S k)
    p2 = plusLeftCancel (1 * (S k)) (j * (S k)) (i * (S k)) p1


reflxSIntEq : Reflx SIntEq
reflxSIntEq (MkInt a b) = SRefl Refl


symmSIntEq : Symm SIntEq
symmSIntEq (MkInt a1 b1) (MkInt a2 b2) (SRefl e) = SRefl (sym e)


transSIntEq : Trans SIntEq
transSIntEq (MkInt a1 b1) (MkInt a2 b2) (MkInt a3 b3) (SRefl e1) (SRefl e2) = SRefl trs where
    e3 : (a1 + b2) + (a2 + b3) = (a2 + b1) + (a3 + b2)
    e3 = summRefl e1 e2

    -- Need to trim b2 and a2 then we get (a1 + b3) = (a3 + b1)


    -- Trim b2 from right side of e3
    tr_b2_r : (a2 + b1) + (a3 + b2) = ((a2 + b1) + a3) + b2
    tr_b2_r = plusAssociative (a2 + b1) a3 b2


    -- reverse left side of e3
    tr_b2_comm : (a1 + b2) + (a2 + b3) = (a2 + b3) + (a1 + b2)
    tr_b2_comm = plusCommutative (a1 + b2) (a2 + b3)

    -- ~ from left side of e3
    tr_b2_l : (a2 + b3) + (a1 + b2) = ((a2 + b3) + a1) + b2
    tr_b2_l = plusAssociative  (a2 + b3) a1 b2

    -- match left and right side
    tr_b2_match : ((a2 + b3) + a1) + b2 = ((a2 + b1) + a3) + b2
    tr_b2_match = trans (trans (sym tr_b2_l) (sym tr_b2_comm)) (trans e3 tr_b2_r)

    -- trim b2
    tr_b2 : (a2 + b3) + a1 = (a2 + b1) + a3
    tr_b2 = plusRightCancel ((a2 + b3) + a1) ((a2 + b1) + a3) b2 tr_b2_match


    -- trim a2 from left side of tr_b2
    tr_a2_l : (b3 + a1) + a2 = (a2 + b3) + a1
    tr_a2_l = trans (plusCommutative (b3 + a1) a2) (plusAssociative a2 b3 a1)

    -- ~ from right side of tr_b2
    tr_a2_r : (a2 + b1) + a3 = (b1 + a3) + a2
    tr_a2_r = sym (trans (plusCommutative (b1 + a3) a2) (plusAssociative a2 b1 a3))

    -- match left and right side of tr_b2
    tr_a2_match : (b3 + a1) + a2 = (b1 + a3) + a2
    tr_a2_match = trans (trans tr_a2_l tr_b2) tr_a2_r


    -- trim a2
    tr_a2 : (b3 + a1) = (b1 + a3)
    tr_a2 = plusRightCancel (b3 + a1) (b1 + a3) a2 tr_a2_match


    -- time for some commutativity
    comm_l : (a1 + b3) = (b3 + a1)
    comm_l = sym (plusCommutative b3 a1)

    comm_r : (b1 + a3) = (a3 + b1)
    comm_r = plusCommutative b1 a3

    -- last trans
    trs : (a1 + b3) = (a3 + b1)
    trs = trans (trans comm_l tr_a2) comm_r


SIntSetoid : Setoid
SIntSetoid = MkSetoid SInt SIntEq (EqProof SIntEq reflxSIntEq symmSIntEq transSIntEq)
