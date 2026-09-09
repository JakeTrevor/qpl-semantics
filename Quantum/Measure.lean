import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic

import Quantum.Gate
import Quantum.State.DensityOp

open scoped Matrix

variable {α} [CommRing α] [StarRing α]

/-
Standard basis projector  (|0><0|)
-/
def MFalse : Gate 1 α :=
  !![1, 0;
     0, 0]

/-
Standard basis projector  (|1><1|)
-/
def MTrue : Gate 1 α :=
  !![0, 0;
     0, 1]


def MTrueLeft (n : ℕ) (h : n >= 1) : Gate n α :=
  MTrue.LiftLeft h

def MFalseLeft (n : ℕ) (h : n >= 1) : Gate n α :=
  MFalse.LiftLeft h


@[simp]
def DensityOp.measureLeft
  (x : DensityOp (n +1) α)
  : DensityOp (n + 1) α
  :=
  let x' : Matrix (Fin (2^n + 2^n)) (Fin (2^n + 2^n)) α
    := cast (by
      unfold DensityOp
      congr
      <;> {
        unfold QSpace
        simp
        ring_nf
      }
    ) x;
  let topLeft := x'.subUp.subLeft;
  let bottomRight := x'.subDown.subRight;
  (Matrix.fromBlocks topLeft 0 0 bottomRight).reindex QSpace.coprod_equiv QSpace.coprod_equiv

namespace DensityOp.measureLeft

@[simp]
def alt1
  (x : DensityOp (n +1) α)
  : DensityOp (n + 1) α
  := fun i j =>
      if i < 2^n ∧ j < 2^n then x i j else
      if i > 2^n ∧ j > 2^n then x i j
      else 0

def equiv1
  (x : DensityOp (n + 1) α)
  : x.measureLeft = alt1 x
  := by
    ext i j
    simp only [alt1 ]
    by_cases h : i < 2 ^n ∧ j < 2 ^ n
    case pos => sorry
    case neg => sorry


lemma meas_idem
  :  ∀ (x : DensityOp (n +1) α),
    x.measureLeft = x.measureLeft.measureLeft
  := by
      intros x
      ext i j
      unfold DensityOp.measureLeft
      congr
      simp_all --(this is basically unreadable. I should probably look into better definitions for this.)
      sorry


lemma trace_meas
  :  ∀ (x : DensityOp (n +1) α),
    x.traceLeft = x.measureLeft.traceLeft
  := by
      intros x
      ext i j
      unfold DensityOp.traceLeft
      congr
      . sorry
      . sorry

end DensityOp.measureLeft
