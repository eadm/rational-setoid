module SIntImplementation

import SInt
import Setoid

-- Proof of some properties of $= and SInt

SIntPlusCommutative : (a, b : SInt) -> (a + b) $= (b + a)
SIntPlusCommutative (MkInt a1 b1) (MkInt a2 b2) = SRefl (
    rewrite (plusCommutative a1 a2) in rewrite (plusCommutative b2 b1) in Refl
)


SIntPlusAssociative : (left, center, right : SInt) -> left + (center + right) $= left + center + right
SIntPlusAssociative (MkInt a1 b1) (MkInt a2 b2) (MkInt a3 b3) = SRefl (
    rewrite (plusAssociative a1 a2 a3) in rewrite (plusAssociative b1 b2 b3) in Refl
)


SIntMultCommutative : (a, b : SInt) -> (a * b $= b * a)
SIntMultCommutative (MkInt a1 b1) (MkInt a2 b2) = SRefl (
    rewrite multCommutative a1 a2 in
    rewrite multCommutative b1 b2 in
    rewrite multCommutative a2 b1 in
    rewrite plusCommutative (b1 * a2) (a1 * b2) in Refl
)
