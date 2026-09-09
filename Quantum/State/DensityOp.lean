import Quantum.State.Vector

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
