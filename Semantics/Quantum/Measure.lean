import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic

import Semantics.Quantum.QuantumState

open scoped Matrix

def MFalse : DensityOp 1 :=
  !![1, 0;
     0, 0]

def MTrue : DensityOp 1 :=
  !![0, 0;
     0, 1]

@[simp]
def DensityOp.measureLeft (x : DensityOp (n +1))  : DensityOp (n + 1) :=
  let x' : Matrix (Fin (2^n + 2^n)) (Fin (2^n + 2^n)) ℂ := cast (by
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
  (Matrix.fromBlocks topLeft 0 0 bottomRight).reindex QSpace.equiv QSpace.equiv

namespace DensityOp.measureLeft

@[simp]
def alt1 (x : DensityOp (n +1))  : DensityOp (n + 1) :=
  fun i j =>
    if i < 2^n ∧ j < 2^n then x i j else
    if i > 2^n ∧ j > 2^n then x i j
    else 0

def equiv1 (x : DensityOp (n + 1))
  : x.measureLeft = alt1 x
  := by
    ext i j
    simp only [alt1 ]
    by_cases h : i < 2 ^n ∧ j < 2 ^ n
    case pos => sorry
    case neg => sorry


lemma trace
  :  ∀ (x : DensityOp (n +1)), x.traceLeft = x.measureLeft.traceLeft
  := by
      intros x
      ext i j
      unfold DensityOp.traceLeft
      congr
      . sorry
      . sorry

end DensityOp.measureLeft
