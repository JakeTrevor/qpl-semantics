import Quantum.State.Basic

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
