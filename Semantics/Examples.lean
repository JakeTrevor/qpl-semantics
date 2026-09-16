import Semantics.fragments.done
import Semantics.fragments.unitary
import Semantics.fragments.meas

open Semantics
open scoped Container


-- These need to be abbrevs, so they are transparent to instance synth
abbrev UnitalSeq   := (ProgSeq :+: DoneC)
abbrev Unitary i α := UnitalSeq :+: (AppC i α)
abbrev Circuit i α := (Unitary i α) :+: (MeasC i α)

variable {α} [CommRing α] [StarRing α]

@[reducible, instance]
def appCSem : ∀ i, Semantics ((AppC i α).extension (Gate i α)) (Gate i α) := inferInstance

-- Instance synth sanity checks
#synth ∀ i, Semantics DoneC.fix (SuperOperator i α)

#synth ∀ i, Semantics (UnitalSeq.extension (SuperOperator i α)) (SuperOperator i α)

#synth ∀ i, Semantics UnitalSeq.fix (SuperOperator i α)

#synth ∀ i, Semantics ((Unitary i α).extension (Gate i α)) (Gate i α)

#synth ∀ i, Semantics (Unitary i α).fix (SuperOperator i α)

#synth ∀ i, Semantics (Circuit i α).fix (SuperOperator i α)

#synth Semantics (Unitary 1 α).fix (Gate 1 α)

def X0 : (Unitary 1 ℤ).fix := ⟨.inr <| App.app
    (by simp)
    (StdGates.X _)
    ⟨(fun _ => ⟨0, by omega⟩), by decide⟩,
  fun x => nomatch x⟩

def semicolon (A B : (Unitary 1 ℤ).fix): (Unitary 1 ℤ).fix :=
  ⟨.inl (.inl ProgSeq'.mk), fun x => match x with
    | ⟨0, _⟩ => A
    | ⟨1, _⟩ => B
  ⟩

infixr:51 " ;;; " => semicolon

def emptyProg : (Unitary 1 ℤ).fix := ⟨.inl (.inr Done.mk), fun x => nomatch x⟩

example : [Gate 1 ℤ]Sem⟦ X0 ;;; X0 ⟧ = Sem⟦emptyProg⟧ := by
  native_decide

-- Note that this doesn't work with superoperators:
-- example : [SuperOperator 1 ℤ]Sem⟦ X0 ;;; X0 ⟧ = Sem⟦emptyProg⟧ := by
--   native_decide
