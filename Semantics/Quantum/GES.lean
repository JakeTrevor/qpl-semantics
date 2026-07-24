import Mathlib.Analysis.Normed.Ring.Basic
import Semantics.Quantum.Measure
import Semantics.Permutation.gate

-- Big idea:
-- Drop $p$, the probability
-- This is captured instead by ||phi||
-- This let's us avoid having to do any normalisation
-- And we don't lose anything
structure GESc (X : Type) i α where
  s : X
  phi : QuantumState i α

def GES X i α := List (GESc X i α)

variable {X : Type} {i : ℕ}
  {α : Type} [CommRing α] [StarRing α]
set_option linter.unusedSectionVars false


namespace GESc
open scoped Gate.App

-- the basic idea:
def measureN (s : GESc X i α) (h : i >= 1) (n : Fin i)
  : GES X i α
  := match s with
  | .mk s phi =>
    let perm : PartialPerm 1 _
      := ⟨fun i : Fin 1 => n, by simp [Function.Injective]⟩
    let perm := perm.toComplete (by assumption)
    let perm := perm.toGate α
    let phi_t :=
      (perm.transpose * (MTrueLeft i h) * perm) @ phi

    let phi_f :=
      (perm.transpose * (MFalseLeft i h) * perm) @ phi
    [⟨s, phi_t⟩, ⟨s, phi_f⟩]

end GESc



-- /-
--   A GES is a "complete" description if it covers all outcomes
--   i.e. the sum of it's component probabilities is 1
-- -/
-- def GES.complete (xs : GES X i α) : Prop
--   := (xs.foldl (fun acc val => acc + val.p) 0) = 1


/-
  Apply a transformation to the quantum component of the state
-/
def GES.mapQuantum (xs : GES X i α)
  (f : QuantumState i α -> QuantumState o α)
  : GES X o α
  := xs.map (fun ⟨s, phi⟩ => ⟨s, f phi⟩)

/-
  Apply a transformation to the classical component of the state
-/
def GES.mapClassical (xs : GES X i α) (f : X -> Y)
  : GES Y i α
  := xs.map (fun ⟨s, phi⟩ => ⟨f s, phi⟩)

/-
  Apply a general transformation to the state component-wise
-/
def GES.mapGeneric (xs : GES X i α)
  (f : (X × QuantumState i α) -> (Y × QuantumState o α))
  : GES Y o α
  := xs.map (
    fun ⟨s, phi⟩ =>
      let ⟨s', phi'⟩ := f (s, phi);
      ⟨s', phi'⟩
  )

def GES.appGate (xs : GES X i α) (g : Gate i α)
  : GES X i α
  := xs.mapQuantum g.App

/-
  Measure the nth qubit in the GES
-/
noncomputable -- evil once more
def GES.measN (xs : GES X i α) (n : Fin i) {h : i >= 1}
  : (GES X i α)
  := xs.flatMap (fun s => GESc.measureN s h n)

-- Regular ensemble states are trivially embedded within this
-- when X = ()
def EnsembleState n := GES Unit n

def GES.toDensityOp (xs : GES X i α)
  : DensityOp i α
  := xs.foldl (
      fun acc ⟨_, phi⟩ => acc + (DensityOp.mk phi)
    ) 0
