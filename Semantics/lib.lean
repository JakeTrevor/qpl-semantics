import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

set_option pp.proofs true

open Complex
open scoped Matrix Kronecker


-- forMathlib:

-- unused
-- Weird that these aren't builtins...
lemma Nat.div_lt
  : ∀ (a b : ℕ), a < b -> a / b = 0
  := by
    intros a b h
    simp
    right
    exact h

-- lemma Nat.mod_lt
--   : ∀ (a b : ℕ), a < b → a % b = a
--   := by
--     intros a b h
--     rw [Nat.mod_def]
--     rw [Nat.div_lt a b h]
--     simp

lemma Fin.up_subst {x : n = m} (val : Nat) {p : val < n}
  : ↑((x ▸ (Fin.mk val p ) : Fin m)) = val
  := by cases x; simp

--
@[simp]
def Fin.castMul {n : ℕ} (m : ℕ) (h : m > 0): Fin n → Fin (n * m)
  := Fin.castLE <| Nat.le_mul_of_pos_right n h

@[simp]
def Fin.castMul' {n : ℕ} (m : ℕ) (h : m > 0): Fin n → Fin (m * n)
  := Fin.castLE <| Nat.le_mul_of_pos_left n h

lemma Fin.div_add_mod
  {hn : n > 0}
  {hm : m > 1}
  :
  ∀ (i : Fin (m * n)),
  i = ((Fin.castMul _ hn i.divNat) * (Fin.mk n (by simp_all))) +
    Fin.castMul' _ (by
      simp_all [←Nat.lt_eq, Nat.lt]
      apply Nat.le_trans _ hm
      simp
      ) (i.modNat)
  := by
    intros i
    simp_all [Fin.mul_def, Fin.add_def]
    cases i
    case mk v h =>
    simp [Nat.div_add_mod', Nat.mod_eq_of_lt h]

lemma distinct
  {hn : n > 0}
  {hm : m > 1}
  : ∀ (i j : Fin (m * n)), i != j -> i.divNat != j.divNat ∨ i.modNat != j.modNat
  := by
    intros i j h
    by_cases i.divNat == j.divNat
      <;> by_cases i.modNat = j.modNat
      <;> simp_all
    case pos hdiv hmod =>
      suffices i = j by apply h; exact this
      have p := @Fin.div_add_mod n m hn hm
      rw [p i, p j, hdiv, hmod]

lemma gen
    {hn : n > 0}
    {hm : m > 1}
    {i j : Fin (m * n)}
  : i != j ->
    (bif i.divNat == j.divNat then 1 else 0) = (0 : ℂ)
  ∨ (bif i.modNat == j.modNat then 1 else 0) = (0 : ℂ)
  := by
      intros ineqj
      have p := @distinct n m hn hm i j ineqj
      cases p <;> simp_all [not_beq_of_ne]

@[simp]
def Matrix.kronecker_flat {m n p q : ℕ} {α : Type u} [Mul α]
    (A : Matrix (Fin m) (Fin n) α)
    (B : Matrix (Fin p) (Fin q) α)
    : Matrix (Fin (m * p)) (Fin (n * q)) α
  :=
    (A ⊗ₖ B).reindex finProdFinEquiv finProdFinEquiv


lemma Matrix.cast_apply {α β : T} {χ : Type} {F : T -> Type}
  (i j : F β) (proof : α = β)
  {M : Matrix (F α) (F α) χ}
  : (proof ▸ M) i j = M (proof ▸ i) (proof ▸ j)
  := by cases proof; simp


infix:60 " ⨂f " => Matrix.kronecker_flat
--- end forMathlib
