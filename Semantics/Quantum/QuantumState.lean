import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

import Semantics.lib

open Complex

@[simp]
abbrev SpaceSize (n : ℕ) := (2 ^ n)

class HTensor (A B C : Type) where
  tens : A -> B -> C

attribute [simp] HTensor.tens
namespace HTensor
scoped infix:1000 " ⨂ " => HTensor.tens
end HTensor

namespace SpaceSize

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

/-
  A vector representation of quantum state
  Parametric over the type of amplitudes
-/
@[simp]
abbrev QuantumState (n : ℕ) (X : Type) := QSpace n -> X

namespace QuantumState
variable {α : Type}

@[simp]
def size {n} (_ : QuantumState n α) := n

/-
  Standardized states (like |1>, |0> and |.>)
-/
namespace StdStates

@[simp]
def Trivial α [One α] : QuantumState 0 α := ![1]

@[simp]
def Zero α [Zero α] [One α]: QuantumState 1 α := ![1, 0]

@[simp]
def One α [_root_.Zero α] [One α]: QuantumState 1 α := ![0, 1]

end StdStates


/-
  Scale a quantum state by some constant factor c
-/
def scale {n} [Mul α] (q : QuantumState n α) (c : α) : QuantumState n α
  := fun i => c * q i

/-
  Take the kronecker product of two quantum states
-/
@[simp]
def kronecker_flat {α : Type _} [Mul α] {n m : ℕ}
  (p : Fin n → α) (q : Fin m → α)
  : Fin (n * m) → α
  := fun i =>
    let i₁ : Fin n := ⟨i.val / m, by
      apply Nat.div_lt_of_lt_mul
      rw [(Nat.mul_comm m n)]
      apply Fin.isLt i
      ⟩
    let i₂ : Fin m := ⟨i.val % m, by
      apply Nat.mod_lt
      cases m
      case zero =>
        cases i
        contradiction
      case succ => simp
      ⟩
    (p i₁) * (q i₂)


/-
  The Tensor product of two quantum states
-/
@[simp]
def Tensor {n m} [Mul α] (p : QuantumState n α) (q : QuantumState m α)
  : QuantumState (n + m) α
  := @Eq.ndrec _ _ (fun i => Fin i -> α) (kronecker_flat p q ) _ SpaceSize.sizeAdd

instance {n m} [Mul α] : HTensor
    (QuantumState n α)
    (QuantumState m α)
    (QuantumState (n + m) α)
  where
    tens := Tensor

/--
  Extend the quantum state `q` with a fresh qubit (allocation) on the right
  `|a> -> |a0>`
-/
@[simp]
def extendRight {n} [Mul α] [Zero α] [One α]
  (q : QuantumState n α)
  : QuantumState (n+1) α
  := kronecker_flat q (StdStates.Zero α)

/-
  Extend the quantum state `q` with a fresh qubit (allocation) on the left
  `|a> -> |0a>`
-/
@[simp]
def extendLeft {n} [Mul α] [Zero α] [One α]
  (q : QuantumState n α)
  : QuantumState (n+1) α
  := cast (by
    rw [QuantumState, QSpace, SpaceSize]
    repeat rw [SpaceSize]
    suffices (2 ^ 1 * 2 ^ n) = 2^ (n + 1) by rw [this]
    ring
  ) (kronecker_flat (StdStates.Zero α) q)


/-
  Extend `q` with `k` fresh qubits on the right
-/
@[simp]
def extendRightBy {n} [Mul α] [Zero α] [One α]
  (q : QuantumState n α)  (k : Nat)
  : QuantumState (n + k) α
  := match k with
  | 0 => q
  | k' + 1 => (extendRightBy q k').extendRight

/-
  Extend `q` with `k` fresh qubits on the left
-/
@[simp]
def extendLeftBy {n} [Mul α] [Zero α] [One α]
  (q : QuantumState n α)  (k : Nat)
  : QuantumState (n + k) α
  := match k with
  | 0 => q
  | k' + 1 => (extendLeftBy q k').extendLeft


/-
  Convert a quantum state vector in matrix-column form
-/
@[simp]
def toCol {n} (q : QuantumState n α)
  : Matrix (Fin (2^n)) (Fin 1) α
  := fun i _ => q i

/-
  Convert a matrix-column form quantum state back into a quantum state vector
-/
@[simp]
def fromCol {n}
  (q : Matrix (Fin (2^n)) (Fin 1) α)
  : QuantumState n α
  := fun i => q i 1

/-
  These two are inverses:
-/
lemma toCol_invert_fromCol : ∀ n,
  Function.LeftInverse (@toCol α n) (@fromCol α n) /\ Function.RightInverse (@toCol α n) (@fromCol α n)
  := by
    intro n
    apply And.intro
    case left =>
      rw [Function.leftInverse_iff_comp]
      ext m i j
      fin_cases j
      simp
    case right =>
      rw [Function.rightInverse_iff_comp]
      ext m i
      simp

/-
  Convert a quantum state vector in matrix-row form
-/
@[simp]
def toRow {n}
  (q : QuantumState n α)
  : Matrix (Fin 1) (Fin (2^n)) α
  := fun _ i => q i

/-
  Convert a matrix-row form quantum state back into a quantum state vector
-/
@[simp]
def fromRow {n}
  (q : Matrix (Fin 1) (Fin (2^n)) α)
  : QuantumState n α
  := fun i => q 1 i


/-
  These two are inverses
-/
lemma toRow_invert_fromRow : ∀ n,
  Function.LeftInverse (@toRow α n) (@fromRow α n) /\ Function.RightInverse (@toRow α n) (@fromRow α n)
  := by
    intro n
    apply And.intro
    case left =>
      rw [Function.leftInverse_iff_comp]
      ext m i j
      fin_cases i
      simp
    case right =>
      rw [Function.rightInverse_iff_comp]
      ext m i
      simp

end QuantumState

@[simp]
abbrev DensityOp n X := Matrix (QSpace n) (QSpace n) X

namespace DensityOp
variable {α : Type}

def scale {i} [Mul α]
  (p : DensityOp i α) (c : α)
  : DensityOp i α
  := fun i j => c * p i j

@[simp]
def mk {n} [NonUnitalNonAssocSemiring α]
  (q : QuantumState n α)
  : DensityOp n α
  := q.toCol * q.toRow

namespace StdStates
variable [NonAssocSemiring α]

@[simp]
def Trivial : DensityOp 0 α := mk (QuantumState.StdStates.Trivial α)

@[simp]
def Zero : DensityOp 1 α := mk (QuantumState.StdStates.Zero α)

@[simp]
def One : DensityOp 1 α := mk (QuantumState.StdStates.One α)

end StdStates


@[simp]
def Tensor {n m} [Mul α]
  (m1 : DensityOp n α) (m2 : DensityOp m α)
  : DensityOp (n + m) α
  := @Eq.ndrec _ _ (fun i => Matrix (Fin i) (Fin i) α)
    (Matrix.kronecker_flat m1 m2) _ SpaceSize.sizeAdd

instance {n m} [Mul α] : HTensor
    (DensityOp n α)
    (DensityOp m α)
    (DensityOp (n + m) α)
  where
    tens := Tensor

open scoped HTensor
-- We really want to prove this
-- So I know I'm not going crazy
lemma tensor_agree {n m} [NonUnitalNonAssocSemiring α]
  : ∀ (p : QuantumState n α) (q : QuantumState m α),
      @mk α (n + m) _ (p ⨂ q) = (mk p) ⨂ (mk q)
  := by
    intros p q
    simp only [HTensor.tens, DensityOp.Tensor, QuantumState.Tensor, DensityOp.mk]
    set a := QuantumState.kronecker_flat p q
    ext i j

    sorry


@[simp]
def extendRight {n} [Mul α] [Zero α]
  (q : DensityOp n α)
  : DensityOp (n+1) α
  :=
    let blocks
      := (@Matrix.fromBlocks (QSpace n) (QSpace n) (QSpace n) (QSpace n) α q 0 0 0);
    let reindexed
      : Matrix (QSpace (n+1)) (QSpace (n+1)) α
      := blocks.reindex (QSpace.coprod_equiv) (QSpace.coprod_equiv);
    cast (by simp) reindexed

lemma extendRight_agree {i} [NonAssocSemiring α]
  : ∀ (q : QuantumState i α),
    mk (q.extendRight) = (mk q).extendRight
  := by
    intro q
    ext i j
    simp
    unfold QuantumState.kronecker_flat
    simp
    sorry


def extendLeft {n} [Mul α] [Zero α]
  (q : DensityOp n α)
  : DensityOp (n+1) α
  :=
    let blocks
      := (@Matrix.fromBlocks (QSpace n) (QSpace n) (QSpace n) (QSpace n) α 0 0 0 q);
    let reindexed
      : Matrix (QSpace (n+1)) (QSpace (n+1)) α
      := blocks.reindex (QSpace.coprod_equiv) (QSpace.coprod_equiv);
    cast (by rw [DensityOp]) reindexed


def extendRightBy {n} [Mul α] [Zero α]
  (q : DensityOp n α)
  : (k : ℕ) -> DensityOp (n + k) α
  | 0 => q
  | x + 1 => (q.extendRightBy x).extendRight

def extendLeftBy {n} [Mul α] [Zero α]
  (q : DensityOp n α)
  : (k : ℕ) -> DensityOp (n + k) α
  | 0 => q
  | x + 1 => (q.extendLeftBy x).extendLeft

/-
  Trace out the leftmost qubit
-/
def traceLeft {n} [Mul α]
  (q : DensityOp (n + 1) α)
  : DensityOp n α :=
  fun i j  => (q i j) * (q (i + (2^n)) (j + (2^n)))

end DensityOp
