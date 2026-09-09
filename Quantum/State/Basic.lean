import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

import Quantum.Lib

@[simp]
abbrev SpaceSize (n : ℕ) := (2 ^ n)

namespace SpaceSize

@[simp]
lemma sizeAdd {n m}
  : (SpaceSize n) * (SpaceSize m) = SpaceSize (n + m)
  := by ring_nf

lemma monotonic
  : SpaceSize (n) <= SpaceSize (n + m)
  := by
    simp
    apply Nat.pow_le_pow_of_le
    <;> simp

end SpaceSize

@[simp]
abbrev QSpace (n : ℕ) := Fin (SpaceSize n)

namespace QSpace

def castLE (x : QSpace n) : QSpace (n + m)
  := Fin.castLE SpaceSize.monotonic x

instance {n m : ℕ} : Coe (QSpace n) (QSpace (n+m)) where
  coe x := x.castLE

def coprod_equiv : QSpace n ⊕ QSpace n ≃ QSpace (n + 1)
  := by
    simp
    suffices 2 ^ (n + 1) = 2^n + 2^n by
      rw [this]
      exact finSumFinEquiv
    ring

instance : Coe (QSpace n ⊕ QSpace n) (QSpace (n + 1)) where
  coe := coprod_equiv

end QSpace
