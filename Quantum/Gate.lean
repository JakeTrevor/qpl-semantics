import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.SetTheory.Ordinal.Arithmetic

import Quantum.Lib
import Quantum.State.DensityOp

open Complex
open scoped Matrix Kronecker HTensor
open scoped Matrix.kronecker_flat



@[simp]
abbrev Gate (n : ℕ) (X : Type) := Matrix (QSpace n) (QSpace n) X

variable {α} [instRα: CommRing α] [StarRing α]
set_option linter.unusedSectionVars false

namespace Gate

@[simp]
def size {n} : Gate n α -> ℕ := n

@[simp]
def App {n}
  (g : Gate n α) (v : QuantumState n α)
  : QuantumState n α
  := Matrix.mulVec g v

namespace App
scoped notation a " @ " b => App a b
end App
open scoped App


@[simp]
def Inv {n}
  (g : Gate n α)
  : Gate n α
  := g.conjTranspose

namespace Inv
scoped notation g "† " => Inv g
end Inv
open scoped Gate.Inv

@[simp]
def AppDens {n}
  (g : Gate n α) (ρ : DensityOp n α)
  : DensityOp n α
  := g * ρ * g†

@[simp]
def Compose {n}
  (g1 g2 : Gate n α) : Gate n α
  := g1 * g2
namespace Compose
scoped infixr:100 " ∘ " => Compose
end Compose

@[simp]
def isID {n}
  (g : Gate n α) : Prop
  := ∀σ, (g.App σ) = σ


@[simp]
def Tensor {n m}
  (g : Gate n α)  (h : Gate m α)
  : Gate (n + m) α
  := @Eq.ndrec _ _ (fun i => Matrix (Fin i) (Fin i) α) (Matrix.kronecker_flat g h) _ SpaceSize.sizeAdd


instance {n m} : HTensor
    (Gate n α)
    (Gate m α)
    (Gate (n + m) α)
  where
    tens := Tensor

end Gate


namespace StdGates

open scoped Gate.Inv

@[simp]
def Trivial α [One α] : Gate 0 α := !![1]
namespace Trivial


lemma tensor_apply {n}
  : ∀(g : Gate n α), (g ⨂ Trivial α : Gate (n + 0) α) = g
  := by
    intro g
    dsimp
    ext i j
    simp_all [Matrix.kroneckerMap, Matrix.submatrix, Matrix.cast_apply]
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

-- The statement of this is broken now
-- Fortunately, I don't seem to need it anywhere...
lemma apply_tensor {n}
  : ∀ (g : Gate n α),
    (Trivial α ⨂ g : Gate (0 + n) α) = (Nat.zero_add n).symm ▸ g
  := by
    intro g
    dsimp
    ext i j
    simp [Matrix.kroneckerMap, Matrix.submatrix, Matrix.cast_apply]
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
def ID (X) [Zero X] [One X]
  : Gate 1 X
  := !![1, 0;
        0, 1]

namespace ID

lemma is1 : ID α = (1 : Matrix (Fin 2) (Fin 2) α) := by
  ext i j
  fin_cases i, j <;> simp

lemma is_id : (@ID α).isID := by
  intros σ
  ext i
  simp [ID, Gate.App, Matrix.mulVec, dotProduct]
  fin_cases i <;> simp


lemma dagger
  : ID α = (ID α)†
  := by
    ext i j
    rw [Gate.Inv, Matrix.conjTranspose_apply]
    fin_cases i, j <;> simp

@[simp]
def mk (α) [Ring α] [StarRing α] (n : ℕ) : Gate n α := 1


namespace mk

lemma is_id : (ID.mk α x).isID := by
  exact Matrix.one_mulVec

lemma dagger : ID.mk α x = (ID.mk α x)†
  := by simp

lemma zero_trivial: ID.mk α 0 = Trivial α := by
  simp [Trivial]
  ext i j
  fin_cases i, j
  simp


lemma mk_tens_mk_absorb :
  ID.mk α m ⨂ ID.mk α n = ID.mk α (m + n)
  := by dsimp; ext i j; simp [Matrix.cast_apply, Matrix.one_apply]


end mk
end ID
end StdGates


namespace Gate

namespace isID

@[simp]
def alt1 (g : Gate n α) := g = StdGates.ID.mk α n

@[simp]
def onDensity
  (g : Gate n α) := ∀ ρ, g.AppDens ρ = ρ

lemma equiv1 {n} :
∀ (g : Gate n α), g.isID <-> alt1 g
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
  ∀ (g : Gate n α), g.isID -> onDensity g
  := by
    intros g
    rw [equiv1]
    simp_all

end isID


@[simp]
def Involutive (g : Gate n α) : Prop := (g.Compose g).isID

namespace Involutive

@[simp]
def alt1 (g : Gate n α) : Prop
  := (g.Compose g) = StdGates.ID.mk α n

@[simp]
def alt2 (g : Gate n α) : Prop
  := ∀ σ, g.App (g.App σ) = σ

lemma equiv1
  (g : Gate n α)
  : g.Involutive <-> alt1 g
  := by
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

lemma equiv2 (g : Gate n α)
  : g.Involutive <-> alt2 g
  := by
    apply Iff.intro
    case mp =>
      rw [Involutive, alt2, Gate.Compose, isID]
      intro h σ
      simp_all only [App, Matrix.mulVec_mulVec]
    case mpr =>
      rw [Involutive, alt2, Gate.Compose, isID]
      intro h σ
      simp_all only [App, Matrix.mulVec_mulVec]


lemma equiv1_2 (g : Gate n α) : alt1 g <-> alt2 g := by
  rw [←equiv1, equiv2]

end Involutive

/--
Given a gate of size `n`, extend the gate to operate on `m` extra qubits on the right
-/
@[simp]
def LiftRightBy {n} (k : ℕ) (g : Gate n α)
  : Gate (n + k) α
  := match k with
  | 0 => g
  | k' + 1 => (g.LiftRightBy k') ⨂ StdGates.ID α

/-
  Given a gate of size `n`, extend the gate to operate on `m` extra qubits on the left
-/
@[simp]
def LiftLeftBy {n} (k : ℕ) (g : Gate n α)
  : Gate (n + k) α
  := match k with
  | 0 => g
  | k' + 1 =>
    let p : (1 + (n + k')) = (n + (k' + 1)) := by ring;
    p ▸ (StdGates.ID α ⨂ (LiftLeftBy k' g))

/-
  Given a gate of size `n`, and a target width `m >= n`, lift the gate (tensor in `ID`s) to the matching size
-/
@[simp]
def LiftRight {n} (h : n <= m) (g : Gate n α) : Gate m α :=
  cast (by
    suffices n + (m - n) = m by rw [this]
    apply Nat.add_sub_cancel' h
  ) (g.LiftRightBy (m - n))

@[simp]
def LiftLeft (h : n <= m) (g : Gate n α) : Gate m α :=
  cast (by
    suffices n + (m - n) = m by rw [this]
    apply Nat.add_sub_cancel' h
  ) (g.LiftRightBy (m - n))

@[simp]
def Controlled {n} (g : Gate n α) : Gate (n + 1) α
  :=
    (
      Matrix.fromBlocks (StdGates.ID.mk α n) 0 0 g
    ).reindex QSpace.coprod_equiv QSpace.coprod_equiv

end Gate


namespace StdGates
open Gate

lemma ID.involutive: (ID α).Involutive := by
  rw [Gate.Involutive.equiv1, Gate.Involutive.alt1]
  ext i j
  fin_cases i, j <;> simp [Matrix.mul_apply]

lemma Trivial.involutive : (Trivial α).Involutive := by
  intros σ
  ext i
  fin_cases i
  simp [Matrix.vecHead]

@[simp]
def X α [Zero α] [One α] : Gate 1 α :=
  !![0, 1;
      1, 0]

lemma X.involutive : (X α).Involutive := by
  rw [Involutive.equiv2]
  intros σ
  ext i
  simp [X, Gate.App, Matrix.mulVec, Matrix.vecTail, Matrix.vecHead]
  fin_cases i <;> simp

-- TODO Is there a better version, that doesn't use ℂ?
@[simp]
def Y : Gate 1 ℂ :=
  !![0, -I;
      I,  0]

lemma Y.involutive : Y.Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, Y, Matrix.mul_apply]
  fin_cases i, j <;> simp

@[simp]
def Z α [Zero α] [One α] [Neg α] : Gate 1 α :=
      !![1,  0;
          0, -1]

lemma Z.involutive : (Z α).Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, Z, Matrix.mul_apply]
  fin_cases i, j <;> simp

-- Same here...
@[simp]
noncomputable def Hadamard : Gate 1 ℂ :=
  let is2 := 1/√2;
    !![is2,  is2;
        is2, -is2]

lemma H.involutive : Hadamard.Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, Hadamard, Matrix.mul_apply]
  fin_cases i, j <;> simp <;> ring_nf <;> norm_num [←Complex.ofReal_pow]

@[simp]
def CX α [Zero α] [One α] : Gate 2 α :=
          !![1, 0, 0, 0;
              0, 1, 0, 0;
              0, 0, 0, 1;
              0, 0, 1, 0]

lemma CX.involutive : (CX α).Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, CX, Matrix.mul_apply]
  fin_cases i, j <;> simp [Fin.sum_univ_four]


lemma controlled_valid
: CX α = Gate.Controlled (StdGates.X α)
:= by
  ext i j
  fin_cases i, j <;> aesop


@[simp]
def SWAP α [Zero α] [One α]
  : Gate 2 α :=
          !![1, 0, 0, 0;
              0, 0, 1, 0;
              0, 1, 0, 0;
              0, 0, 0, 1]

lemma SWAP.involutive : (SWAP α).Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, SWAP, Matrix.mul_apply]
  fin_cases i, j <;> simp [Fin.sum_univ_four]


@[simp]
def SwapAdj α [CommRing α] (x : Nat) : Gate (2 + x) α :=
  ((StdGates.SWAP α).LiftLeftBy x)


lemma kronecker_flat_mul_cast
  {h1 : SpaceSize n * SpaceSize m = SpaceSize (n + m)}
  : ∀ (a c : Gate n α) (b d : Gate m α),
    h1 ▸ (a ⨂f b) * h1 ▸ (c ⨂f d)
    = h1 ▸ ((a ⨂f b) * (c ⨂f d))
  := by
    intros a c b d
    grind

lemma mulTensComm {n m : ℕ}
  : ∀ (a c : Gate n α ) (b d : Gate m α),
    (a ⨂ b : Gate (n + m) α) * (c ⨂ d) = (a * c) ⨂ (b * d)
  := by
    intros a c b d
    simp only [HTensor.tens, Gate.Tensor]
    suffices (a ⨂f b) * (c ⨂f d) = a * c ⨂f b * d by
      rw [←this, kronecker_flat_mul_cast]
    exact Matrix.kronecker_flat.mul_distrib a b c d

lemma mulTensCommCast {n m : ℕ}
  {h1 : (n + m) = b }
  : ∀ (a c : Gate n α) (b d : Gate m α),
    (h1 ▸ (a ⨂ b : Gate (n + m) α)) * (h1 ▸ (c ⨂ d))
    = h1 ▸ ((a * c) ⨂ (b * d))
  := by
    intros a c b d
    cases h1
    case refl =>
      suffices (a ⨂ b) * (c ⨂ d) = (a * c) ⨂ (b * d) by
        rw [←this]
      exact mulTensComm a c b d

lemma ID.mk.castElim (p : m = n)
  : (p ▸ ID.mk α m) = (ID.mk α n)
  := by cases p; rfl


lemma tens_preserve_involutive {n m : ℕ}
  : ∀ (a : Gate n α) (b : Gate m α),
    a.Involutive -> b.Involutive -> Gate.Involutive (a ⨂ b : Gate (n + m) α )
  := by
    intros a b ha hb
    rw [Gate.Involutive, Gate.Compose, Gate.isID.equiv1, isID.alt1] at ha hb
    rw [Gate.Involutive, Gate.Compose, mulTensComm, ha, hb, ID.mk.mk_tens_mk_absorb]
    apply ID.mk.is_id

lemma swapAdj.involutive : ∀ x, (SwapAdj α x).Involutive := by
  intros x
  induction x
  case zero =>
    rw [SwapAdj, LiftLeftBy]
    exact SWAP.involutive
  case succ k' h =>
    rw [SwapAdj, LiftLeftBy]
    suffices Gate.Involutive (ID α ⨂ (SWAP α).LiftLeftBy k' : Gate (1 + (2 + k')) α) by
      rw [Gate.Involutive.equiv1, Gate.Involutive.alt1, Gate.Compose, SwapAdj] at h

      have x := @StdGates.ID.involutive α _ _
      rw [Gate.Involutive.equiv1, Gate.Involutive.alt1, Gate.Compose] at x
      rw [Gate.Involutive, Gate.Compose, Gate.isID.equiv1, Gate.isID.alt1, mulTensCommCast, h, x, ID.mk.mk_tens_mk_absorb, ID.mk.castElim]
    apply tens_preserve_involutive
    case a => exact ID.involutive
    case a => exact h

@[simp]
def toffoli α [Zero α] [One α]: Gate 3 α := !![
    1,0,0,0,0,0,0,0;
    0,1,0,0,0,0,0,0;
    0,0,1,0,0,0,0,0;
    0,0,0,1,0,0,0,0;
    0,0,0,0,1,0,0,0;
    0,0,0,0,0,1,0,0;
    0,0,0,0,0,0,0,1;
    0,0,0,0,0,0,1,0;
  ]

lemma toffoli.involutive : (toffoli α).Involutive := by
  rw [Involutive.equiv1]
  ext i j
  simp [Gate.Compose, toffoli, Matrix.mul_apply]
  fin_cases i, j <;> simp [Fin.sum_univ_eight]

end StdGates


open Gate
open scoped Gate.App

lemma application_is_composition :
  ∀ (G : Gate n α) (s : QuantumState n α),
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
  ∀ (G1 : Gate n α) (G2 : Gate m α)
  (p1 : QuantumState n α) (p2 : QuantumState m α),
  ((G1 ⨂ G2 : Gate (n + m) α) @ (p1 ⨂ p2))
    = (G1 @ p1) ⨂ (G2 @ p2)
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


lemma extending_is_tensor_zero : ∀ (σ : QuantumState n α),
  σ.extendRight = σ ⨂ QuantumState.StdStates.Zero α
  := by
    intro σ
    simp
    rfl

lemma weak_extension_application :
    ∀(g : Gate n α) (σ : QuantumState n α),
    (g @ σ).extendRight = (g ⨂ StdGates.ID α) @ σ.extendRight
  := by
    intros g σ
    rw [extending_is_tensor_zero, extending_is_tensor_zero, separability, StdGates.ID.is_id]


-- an important lemma;
-- Essentially, this is a proof that a program's semantics are not changed
-- If we lift it onto a larger QC
lemma extension_application {n : Nat} :
  ∀(g : Gate n α) (σ : QuantumState n α) (x : Nat),
    (g @ σ).extendRightBy x =
    (g.LiftRightBy x) @ (σ.extendRightBy x)
  := by
    intros g σ x
    induction x
    case zero => simp [QuantumState.extendRightBy, Gate.LiftRightBy]
    case succ a h =>
      rw [QuantumState.extendRightBy, h]
      rw [Gate.LiftRightBy, QuantumState.extendRightBy, ←weak_extension_application]
