-- This file contains some basic proofs that we need
-- Aren't really directly quantum information theory related
-- And don't ship with matlib
-- Perhaps in the future, we could look at getting these merged in
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic

open Complex
open scoped Matrix Kronecker

@[simp]
def Matrix.kronecker_flat {m n p q : ℕ} {α : Type u} [Mul α]
    (A : Matrix (Fin m) (Fin n) α)
    (B : Matrix (Fin p) (Fin q) α)
    : Matrix (Fin (m * p)) (Fin (n * q)) α
  :=
    (A ⊗ₖ B).reindex finProdFinEquiv finProdFinEquiv

namespace Matrix.kronecker_flat
scoped infix:60 " ⨂f " => Matrix.kronecker_flat

lemma mul_distrib {α} {x x' y y' z z'} [CommSemiring α]
  (A : Matrix (Fin x ) (Fin y ) α)
  (B : Matrix (Fin x') (Fin y') α)
  (C : Matrix (Fin y ) (Fin z ) α)
  (D : Matrix (Fin y') (Fin z') α)
  : (A ⨂f B) * (C ⨂f D) = (A * C) ⨂f (B * D)
  := by
    simp
    suffices ((Matrix.kroneckerMap (fun x1 x2 ↦ x1 * x2) A B) * (Matrix.kroneckerMap (fun x1 x2 ↦ x1 * x2) C D)) = (Matrix.kroneckerMap (fun x1 x2 ↦ x1 * x2) (A * C) (B * D)) by
      rw [this]
    rw [Matrix.mul_kronecker_mul A C B D]

end Matrix.kronecker_flat

lemma Matrix.cast_apply {α β : T} {χ : Type} {F : T -> Type}
  (i j : F β) (proof : α = β)
  {M : Matrix (F α) (F α) χ}
  : (proof ▸ M) i j = M (proof ▸ i) (proof ▸ j)
  := by cases proof; simp


instance : Star ℤ where
  star x := x

class HTensor (A B C : Type) where
  tens : A -> B -> C

attribute [simp] HTensor.tens

namespace HTensor
scoped infix:1000 " ⨂ " => HTensor.tens
end HTensor
