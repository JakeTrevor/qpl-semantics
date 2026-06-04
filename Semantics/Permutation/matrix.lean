import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases


def Matrix.isPerm {n : Nat} (m: Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i,
    (∃ k, ∀ j, m i j = if j == k then 1 else 0) /\
    (∃ k, ∀ j, m j i = if j == k then 1 else 0)

theorem Fin.nbeq_neq {n} {a b : Fin n}: (a == b) = false -> ¬(a = b)
  := by simp

namespace Matrix.isPerm

theorem trans_inv {n} {x : Matrix (Fin n) (Fin n) ℂ} :
  x.isPerm -> x * x.transpose = 1 := by
    intro isPermX
    ext i j
    simp [Matrix.mul_apply]
    cases p : i == j
    case a.false =>
      suffices ∀ q, x i q * x j q = 0 by
        simp [this, Fin.nbeq_neq p]
      intros q
      apply (isPermX q).right.elim
      intro k h
      rw [h i, h j]
      cases p2 : i == k
      <;> simp
      simp at p2
      subst p2
      simp at p
      intro z
      exact p z.symm
    case a.true =>
      simp at p
      simp [Matrix.one_apply]
      subst p
      simp_all
      apply (isPermX i).left.elim
      intro k h
      simp_all only [beq_iff_eq, mul_ite, ↓reduceIte, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]

end Matrix.isPerm
