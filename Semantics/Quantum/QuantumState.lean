import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

import Semantics.lib

open Complex

@[simp]
abbrev SpaceSize (n : ℕ) := (2 ^ n)

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

def equiv : QSpace n ⊕ QSpace n ≃ QSpace (n + 1)
  := by
    simp
    suffices 2 ^ (n + 1) = 2^n + 2^n by
      rw [this]
      exact finSumFinEquiv
    ring

instance : Coe (QSpace n ⊕ QSpace n) (QSpace (n + 1)) where
  coe := equiv

end QSpace

/--
A vector representation of quantum state
-/
@[simp]
abbrev QuantumState (n : ℕ) := QSpace n -> ℂ

namespace QuantumState

@[simp]
def size {n} (_ : QuantumState n) := n

@[simp]
def Trivial : QuantumState 0 := ![1]

@[simp]
def Zero : QuantumState 1 := ![1, 0]

@[simp]
def One : QuantumState 1 := ![0, 1]

/-
Take the kronecker product of two quantum states
-/
@[simp]
def kronecker_flat {α : Type _} [Mul α]
    {n m : ℕ} (p : Fin n → α) (q : Fin m → α) : Fin (n * m) → α :=
  fun i =>
    let i₁ : Fin n := ⟨i.val / m, by
      apply Nat.div_lt_of_lt_mul
      rw [(Nat.mul_comm m n)]
      apply Fin.isLt i
      ⟩
    let i₂ : Fin m := ⟨i.val % m, by
      apply Nat.mod_lt
      cases m
      case hy.zero =>
        cases i
        contradiction
      case hy.succ => simp
      ⟩
    (p i₁) * (q i₂)

@[simp]
def Tensor {n m} (p : QuantumState n) (q : QuantumState m)
  : QuantumState (n + m)
  := @Eq.ndrec _ _ (fun i => Fin i -> ℂ) (kronecker_flat p q ) _ SpaceSize.sizeAdd


infix:60 " S⨂ " => Tensor

/--
Extend the quantum state `q` with a fresh qubit (allocation) on the right
-/
@[simp]
def extendRight {n} (q : QuantumState n ) : QuantumState (n+1) :=
  kronecker_flat q QuantumState.Zero


/--
Extend the quantum state `q` with a fresh qubit (allocation) on the left
-/
@[simp]
def extendLeft {n} (q : QuantumState n ) : QuantumState (n+1) :=
  cast (by
    rw [QuantumState, QSpace, SpaceSize]
    repeat rw [SpaceSize]
    suffices (2 ^ 1 * 2 ^ n) = 2^ (n + 1) by rw [this]
    ring
  ) (kronecker_flat QuantumState.Zero q)


/--
Extend `q` with `k` fresh qubits on the right
-/
@[simp]
def extendRightBy {n} (q : QuantumState n )  (k : Nat) : QuantumState (n + k) := match k with
  | 0 => q
  | k' + 1 => (extendRightBy q k').extendRight


/--
Extend `q` with `k` fresh qubits on the left
-/
@[simp]
def extendLeftBy {n} (q : QuantumState n )  (k : Nat) : QuantumState (n + k) := match k with
  | 0 => q
  | k' + 1 => (extendLeftBy q k').extendLeft


/--
Convert a quantum state vector in matrix-column form
-/
@[simp]
def toCol (q : QuantumState n) : Matrix (Fin (2^n)) (Fin 1) ℂ :=
  fun i _ => q i

/--
Convert a matrix-column form quantum state back into a quantum state vector
-/
@[simp]
def fromCol (q : Matrix (QSpace n) (Fin 1) ℂ) : (QuantumState n) :=
  fun i => q i 1


/--
Convert a quantum state vector in matrix-row form
-/
@[simp]
def toRow (q : QuantumState n) : Matrix (Fin 1) (Fin (2^n)) ℂ :=
  fun _ i => q i

/--
Convert a matrix-row form quantum state back into a quantum state vector
-/
@[simp]
def fromRow (q : Matrix (Fin 1) (QSpace n) ℂ) : (QuantumState n) :=
  fun i => q 1 i


end QuantumState

@[simp]
abbrev DensityOp n := Matrix (QSpace n) (QSpace n) ℂ

namespace DensityOp

@[simp]
def mk (q : QuantumState n) : DensityOp n :=
  q.toCol * q.toRow

@[simp]
def Trivial := mk QuantumState.Trivial

@[simp]
def Zero := mk QuantumState.Zero

@[simp]
def One := mk QuantumState.One

@[simp]
def Tensor (m1 : DensityOp n) (m2 : DensityOp m)
  : DensityOp (n + m)
  := @Eq.ndrec _ _ (fun i => Matrix (Fin i) (Fin i) ℂ) (Matrix.kronecker_flat m1 m2) _ SpaceSize.sizeAdd


-- We really want to prove this
-- So I know I'm not going crazy
lemma DensityOp.tensorAgree :
  ∀ (p : QuantumState n) (q : QuantumState m),
  mk (p.Tensor q) = (mk p).Tensor (mk q)
  := by
    intros p q
    ext i j
    simp [HMul.hMul, dotProduct, Matrix.submatrix, Matrix.cast_apply,Matrix.of_apply]
    sorry


@[simp]
def extendRight (q : DensityOp n) : DensityOp (n+1) :=
  let blocks
    := (@Matrix.fromBlocks (QSpace n) (QSpace n) (QSpace n) (QSpace n) ℂ q 0 0 0);
  let reindexed
    : Matrix (QSpace (n+1)) (QSpace (n+1)) ℂ
    := blocks.reindex (QSpace.equiv) (QSpace.equiv);
  cast (by rw [DensityOp]) reindexed

def extendLeft (q : DensityOp n) : DensityOp (n+1) :=
  let blocks
    := (@Matrix.fromBlocks (QSpace n) (QSpace n) (QSpace n) (QSpace n) ℂ 0 0 0 q);
  let reindexed
    : Matrix (QSpace (n+1)) (QSpace (n+1)) ℂ
    := blocks.reindex (QSpace.equiv) (QSpace.equiv);
  cast (by rw [DensityOp]) reindexed


def extendRightBy (q : DensityOp n) : (k : ℕ) -> DensityOp (n + k)
  | 0 => q
  | x + 1 => (q.extendRightBy x).extendRight

def extendLeftBy (q : DensityOp n) : (k : ℕ) -> DensityOp (n + k)
  | 0 => q
  | x + 1 => (q.extendLeftBy x).extendLeft

/-
Trace out the leftmost qubit
-/
def traceLeft (q : DensityOp (n + 1)) : DensityOp n :=
  fun i j  => (q i j) * (q (i + (2^n)) (j + (2^n)))

end DensityOp
