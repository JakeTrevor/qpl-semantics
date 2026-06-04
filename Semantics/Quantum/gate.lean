import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.SetTheory.Ordinal.Arithmetic

import Semantics.Quantum.QuantumState
import Semantics.lib

set_option pp.proofs true

open Complex
open scoped Matrix Kronecker




@[simp]
abbrev Gate (n : ℕ) := Matrix (QSpace n) (QSpace n) ℂ


lemma kronecker_flat.mul
  [CommSemiring α]
  (A : Matrix (Fin x) (Fin y) α)
  (B : Matrix (Fin x') (Fin y') α)
  (C : Matrix (Fin y) (Fin z) α)
  (D : Matrix (Fin y') (Fin z') α)
  : (A ⨂f B) * (C ⨂f D) = (A * C) ⨂f (B * D)
  := by
    simp
    suffices ((Matrix.kroneckerMap (fun x1 x2 ↦ x1 * x2) A B) * (Matrix.kroneckerMap (fun x1 x2 ↦ x1 * x2) C D)) = (Matrix.kroneckerMap (fun x1 x2 ↦ x1 * x2) (A * C) (B * D)) by
      rw [this]
    rw [Matrix.mul_kronecker_mul A C B D]


namespace Gate

@[simp]
def size {n} : Gate n -> ℕ := n

@[simp]
def App {n} (g : Gate n) (v : QuantumState n) : QuantumState n := Matrix.mulVec g v

scoped notation a " @ " b => App a b

@[simp]
def inv (g : Gate n) : Gate n := g.conjTranspose

scoped notation g "† " => Gate.inv g

@[simp]
def AppDens {n} (g : Gate n) (ρ : DensityOp n) : DensityOp n :=
  g * ρ * g†

@[simp]
def Compose {n} (g1 g2 : Gate n) : Gate n := g1 * g2

@[simp]
def isID (g : Gate n) : Prop := ∀σ, (g.App σ) = σ


@[simp]
def Tensor {n m} (g : Gate n)  (h : Gate m) : Gate (n + m) := @Eq.ndrec _ _ (fun i => Matrix (Fin i) (Fin i) ℂ) (Matrix.kronecker_flat g h) _ SpaceSize.sizeAdd

infix:60 " ⨂ " => Tensor

end Gate
namespace StdGates

@[simp]
def Trivial : Gate 0 := !![1]

namespace Trivial


lemma tensor_apply (x : Gate n)
  : (x ⨂ Trivial) = x
  := by
    ext i j
    simp_all [Trivial, Matrix.kroneckerMap, Matrix.submatrix, Matrix.cast_apply]
    congr <;> {
      apply Fin.val_inj.mp
      simp
      congr
      ring_nf
      simp
    }

lemma Fin.cast_val  { p : n = m}
  : ∀(i : Fin n), (p ▸ i).val = i.val
  := by cases p; simp

lemma apply_tensor (x : Gate n)
  : (Trivial ⨂ x) = (Nat.zero_add n).symm ▸ x
  := by
    ext i j
    simp [Trivial, Matrix.kroneckerMap, Matrix.submatrix, Matrix.cast_apply]
    congr <;> {
      apply Fin.val_inj.mp
      simp
      rw [Nat.mod_eq_of_lt, Fin.cast_val]
      congr
      . ring
      . simp
      set pi := (@Eq.rec ℕ (2 ^ (0 + n)) (fun x h ↦ Fin x) _ (1 * 2 ^ n) (SpaceSize.sizeAdd.symm)).isLt
      simp at pi
      exact pi
    }

end Trivial

@[simp]
def ID : Gate 1 :=
      !![1, 0;
          0, 1]

namespace ID

lemma is1 : ID = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i, j <;> simp

lemma is_id : ID.isID := by
  intros σ
  ext i
  simp [ID, Gate.App, Matrix.mulVec, dotProduct]
  fin_cases i <;> simp

lemma dagger : ID = Gate.inv ID := by
  ext i j
  rw [Gate.inv, Matrix.conjTranspose_apply]
  fin_cases i, j <;> simp


@[simp]
def mk (n : ℕ) : Gate n := 1

namespace mk

lemma is_id : (ID.mk x).isID := by
  exact Matrix.one_mulVec

lemma dagger : ID.mk x = Gate.inv (ID.mk x) := by
  simp

lemma zero_trivial: ID.mk 0 = Trivial := by
  simp [Trivial]
  ext i j
  fin_cases i, j
  simp


lemma mk_tens_mk_absorb :
  ID.mk m ⨂ ID.mk n = ID.mk (m + n)
  := by ext i j; simp [Matrix.cast_apply, Matrix.one_apply]


end mk
end ID
end StdGates


namespace Gate

namespace isID
@[simp]
def alt1 (g : Gate n) := g = StdGates.ID.mk n

@[simp]
def onDensity (g : Gate n) := ∀ ρ, g.AppDens ρ = ρ

lemma equiv1 {n} :
∀ (g : Gate n), g.isID <-> alt1 g
:= by
  intros g
  apply Iff.intro
  case mp =>
    simp
    intros h
    rw [Matrix.ext_iff_mulVec]
    intros σ
    rw [h σ, Matrix.one_mulVec]
  case mpr =>
    simp
    intros h
    rw [h]
    exact Matrix.one_mulVec

lemma implDensity {n} :
  ∀ (g : Gate n), g.isID -> onDensity g
  := by
    intros g
    rw [equiv1]
    simp_all

end isID


@[simp]
def Involutive (g : Gate n) : Prop := (g.Compose g).isID

namespace Involutive

@[simp]
def alt1 (g : Gate n) : Prop := (g.Compose g) = StdGates.ID.mk n

@[simp]
def alt2 (g : Gate n) : Prop := ∀ σ, g.App (g.App σ) = σ

lemma equiv1 (g : Gate n) : g.Involutive <-> alt1 g := by
  apply Iff.intro
  case mp =>
    rw [Involutive, alt1, Gate.Compose, isID]
    intro h
    rw [Matrix.ext_iff_mulVec]
    intro σ
    simp_all
  case mpr =>
    rw [Involutive, alt1, Gate.Compose]
    intro h
    simp_all

lemma equiv2 (g : Gate n) : g.Involutive <-> alt2 g := by
  apply Iff.intro
  case mp =>
    rw [Involutive, alt2, Gate.Compose, isID]
    intro h σ
    simp_all only [App, Matrix.mulVec_mulVec]
  case mpr =>
    rw [Involutive, alt2, Gate.Compose, isID]
    intro h σ
    simp_all only [App, Matrix.mulVec_mulVec]


lemma equiv1_2 (g : Gate n) : alt1 g <-> alt2 g := by
  rw [←equiv1, equiv2]

end Involutive

/--
Given a gate of size `n`, extend the gate to operate on `m` extra qubits on the right
-/
@[simp]
def LiftRightBy {n} (g : Gate n) (k : ℕ) : Gate (n + k) := match k with
  | 0 => g
  | k' + 1 => cast (by ring_nf) ((g.LiftRightBy k') ⨂ StdGates.ID)

/--
Given a gate of size `n`, extend the gate to operate on `m` extra qubits on the left
-/
@[simp]
def LiftLeftBy {n} (g : Gate n) (k : ℕ) : Gate (n + k) :=
match k with
  | 0 => g
  | k' + 1 =>
    let p : (1 + (n + k')) = (n + (k' + 1)) := by ring;
    p ▸ (StdGates.ID ⨂ (LiftLeftBy g k'))

/--
Given a gate of size `n`, and a target width `m >= n`,
lift the gate (tensor in `ID`s) to the matching size
-/
def LiftRight {n} (g : Gate n) (h : n <= m) : Gate m :=
  cast (by
    suffices n + (m - n) = m by rw [this]
    apply Nat.add_sub_cancel' h
  ) (g.LiftRightBy (m - n))

def LiftLeft (g : Gate n) (h : n <= m) : Gate m :=
  cast (by
    suffices n + (m - n) = m by rw [this]
    apply Nat.add_sub_cancel' h
  ) (g.LiftRightBy (m - n))


def Controlled {n} (g : Gate n) : Gate (n + 1) :=
(Matrix.fromBlocks (StdGates.ID.mk n) 0 0 g).reindex QSpace.equiv QSpace.equiv

end Gate


namespace StdGates
open Gate

lemma ID.involutive: ID.Involutive := by
  rw [Gate.Involutive.equiv1, Gate.Involutive.alt1]
  ext i j
  fin_cases i, j <;> simp [Matrix.mul_apply]

lemma Trivial.involutive : Trivial.Involutive := by
  intros σ
  ext i
  fin_cases i
  simp [Matrix.vecHead]

@[simp]
def X : Gate 1 :=
  !![0, 1;
      1, 0]

lemma X.involutive : X.Involutive := by
  rw [Involutive.equiv2]
  intros σ
  ext i
  simp [X, Gate.App, Matrix.mulVec, Matrix.vecTail, Matrix.vecHead]
  fin_cases i <;> simp

@[simp]
def Y : Gate 1 :=
  !![0, -I;
      I,  0]

lemma Y.involutive : Y.Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, Y, Matrix.mul_apply]
  fin_cases i, j <;> simp

@[simp]
def Z : Gate 1 :=
      !![1,  0;
          0, -1]

lemma Z.involutive : Z.Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, Z, Matrix.mul_apply]
  fin_cases i, j <;> simp


@[simp]
noncomputable def Hadamard : Gate 1 :=
  let is2 := 1/√2;
    !![is2,  is2;
        is2, -is2]

lemma H.involutive : Hadamard.Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, Hadamard, Matrix.mul_apply]
  fin_cases i, j <;> simp <;> ring_nf <;> norm_num [←Complex.ofReal_pow]

@[simp]
def CX : Gate 2 :=
          !![1, 0, 0, 0;
              0, 1, 0, 0;
              0, 0, 0, 1;
              0, 0, 1, 0]

lemma CX.involutive : CX.Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, CX, Matrix.mul_apply]
  fin_cases i, j <;> simp [Fin.sum_univ_four]


lemma controlled_valid
: CX = @Gate.Controlled 1 StdGates.X
:= by
  ext i j
  fin_cases i, j <;> aesop


@[simp]
def SWAP : Gate 2 :=
          !![1, 0, 0, 0;
              0, 0, 1, 0;
              0, 1, 0, 0;
              0, 0, 0, 1]

lemma SWAP.involutive : SWAP.Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, SWAP, Matrix.mul_apply]
  fin_cases i, j <;> simp [Fin.sum_univ_four]


@[simp]
def SwapAdj (x : Nat) : Gate (2 + x) :=
  (StdGates.SWAP.LiftLeftBy x)


lemma kronecker_flat_mul_cast
  {h1 : SpaceSize n * SpaceSize m = SpaceSize (n + m)}
  : ∀ (a c : Gate n) (b d : Gate m),
    h1 ▸ (a ⨂f b) * h1 ▸ (c ⨂f d)
    = h1 ▸ ((a ⨂f b) * (c ⨂f d))
  := by
    intros a c b d
    grind


lemma mulTensComm {n m : ℕ}
  : ∀ (a c : Gate n) (b d : Gate m),
    (a ⨂ b) * (c ⨂ d) = (a * c) ⨂ (b * d)
  := by
    intros a c b d
    unfold Gate.Tensor
    suffices (a ⨂f b) * (c ⨂f d) = a * c ⨂f b * d by
      rw [←this, kronecker_flat_mul_cast]
    exact kronecker_flat.mul a b c d

lemma mulTensCommCast {n m : ℕ}
  {h1 : (n + m) = b }
  : ∀ (a c : Gate n) (b d : Gate m),
    (h1 ▸ (a ⨂ b)) * (h1 ▸ (c ⨂ d))
    = h1 ▸ ((a * c) ⨂ (b * d))
  := by
    intros a c b d
    cases h1
    case refl =>
      suffices (a ⨂ b) * (c ⨂ d) = (a * c) ⨂ (b * d) by
        rw [←this]
      exact mulTensComm a c b d

lemma ID.mk.castElim (p : m = n)
  : (p ▸ ID.mk m) = (ID.mk n)
  := by cases p; rfl


lemma tens_preserve_involutive {n m : ℕ}
  : ∀ (a : Gate n) (b : Gate m),
    a.Involutive -> b.Involutive -> (a ⨂ b).Involutive
  := by
    intros a b ha hb
    rw [Gate.Involutive, Gate.Compose, Gate.isID.equiv1, isID.alt1] at ha hb
    rw [Gate.Involutive, Gate.Compose, mulTensComm, ha, hb, ID.mk.mk_tens_mk_absorb]
    apply ID.mk.is_id

lemma swapAdj.involutive : ∀ x, (SwapAdj x).Involutive := by
  intros x
  induction x
  case zero =>
    rw [SwapAdj, LiftLeftBy]
    exact SWAP.involutive
  case succ k' h =>
    rw [SwapAdj, LiftLeftBy]
    suffices (ID ⨂ SWAP.LiftLeftBy k').Involutive by
      rw [Gate.Involutive.equiv1, Gate.Involutive.alt1, Gate.Compose, SwapAdj] at h
      have x := ID.involutive
      rw [Gate.Involutive.equiv1, Gate.Involutive.alt1, Gate.Compose] at x
      rw [Gate.Involutive, Gate.Compose, Gate.isID.equiv1, Gate.isID.alt1, mulTensCommCast, h, x, ID.mk.mk_tens_mk_absorb, ID.mk.castElim]
    apply tens_preserve_involutive
    case a => exact ID.involutive
    case a => exact h

@[simp]
def toffoli : Gate 3 := !![
    1,0,0,0,0,0,0,0;
    0,1,0,0,0,0,0,0;
    0,0,1,0,0,0,0,0;
    0,0,0,1,0,0,0,0;
    0,0,0,0,1,0,0,0;
    0,0,0,0,0,1,0,0;
    0,0,0,0,0,0,0,1;
    0,0,0,0,0,0,1,0;
  ]

lemma toffoli.involutive : toffoli.Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, toffoli, Matrix.mul_apply]
  fin_cases i, j <;> simp [Fin.sum_univ_eight]

end StdGates


open Gate

lemma application_is_composition :
  ∀ (G : Gate n) (s : QuantumState n),
  (G @ s) = QuantumState.fromCol (G * (s.toCol))
  := by
    intros g s
    ext i
    simp [HMul.hMul, Matrix.mulVec]

lemma helper3
  {a c : Type} {b : a -> Type}
  {p q : a} (h : q = p)
  (f : (b q) -> c)
  (x : b p) :
  (h ▸ f) x = f (h ▸ x)
  := by
    cases h
    simp


lemma helper4
  (h : α = β) (e : α ≃ γ) (p : β)
  : (h ▸ e) p = e (h ▸ p)
  := by cases h; simp


lemma helper5 (h : m = n)
  : ((congrArg (fun i => Fin i ≃ Fin n)) h ▸ Equiv.refl (Fin n)) x = h ▸ x
  := by cases h; simp

lemma separability :
  ∀ (G1 : Gate n) (G2 : Gate m)
  (p1 : QuantumState n) (p2 : QuantumState m),
  ((G1 ⨂ G2) @ (p1 S⨂ p2)) = (G1 @ p1) S⨂ (G2 @ p2)
  := by
  intros G1 G2 p1 p2
  ext i
  simp [Matrix.kroneckerMap, Matrix.submatrix, Matrix.kronecker_flat, QuantumState.Tensor, Matrix.mulVec, dotProduct, helper3, Matrix.cast_apply]
  simp [Finset.sum_mul_sum, ←Fintype.sum_prod_type']
  exact (Finset.sum_equiv
    (Equiv.trans (by rw [Nat.pow_add]) finProdFinEquiv.symm)
    (by simp)
    (by
      intros p hp
      rw [mul_mul_mul_comm]
      congr
        <;> simp [cast.eq_1, helper5 (Nat.pow_add 2 n m)]
    )
  )


lemma extending_is_tensor_zero : ∀ (σ : QuantumState n),
  σ.extendRight = σ.Tensor QuantumState.Zero
  := by simp

lemma weak_extension_application :
    ∀(g : Gate n) (σ : QuantumState n),
    (g @ σ).extendRight = (g ⨂ StdGates.ID) @ σ.extendRight
  := by
    intros g σ
    rw [extending_is_tensor_zero, extending_is_tensor_zero, separability, StdGates.ID.is_id]


-- an important lemma;
-- Essentially, this is a proof that a program's semantics are not changed
-- If we lift it onto a larger QC
lemma extension_application {n : Nat} :
  ∀(g : Gate n) (σ : QuantumState n) (x : Nat),
    (g @ σ).extendRightBy x =
    (g.LiftRightBy x) @ (σ.extendRightBy x)
  := by
    intros g σ x
    induction x
    case zero => simp [QuantumState.extendRightBy, Gate.LiftRightBy]
    case succ a h =>
      rw [QuantumState.extendRightBy, h]
      rw [Gate.LiftRightBy, QuantumState.extendRightBy,
      cast.eq_1, ←weak_extension_application]
