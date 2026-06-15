import Semantics.Quantum.Measure
import Semantics.Permutation.Gate

namespace Circuit

inductive Command : (i o : ℕ) -> Type where
  | Done : Command i i
  | App : (h_size : n <= i) ->  Gate n -> PartialPerm n i -> Command i o -> Command i o
  | Meas : (Fin i) -> Command i o -> Command i o
  | Alloc : Command (i + 1) o -> Command i o
  | Free : (Fin i) -> Command (i - 1) o -> Command i o

-- we just need to assume these work
def perm (h_size : n <= i) (l : PartialPerm n i)
  : Gate i := (l.toComplete h_size).toGate
def permInv (h_size : n <= i) (l : PartialPerm n i )
  : Gate i := (l.toComplete h_size).toGate.transpose

notation:50 " π""⟦ " x ", " h_size " ⟧ " => Gate.AppDens <| perm h_size x
notation:50 " π⁻¹""⟦ " x ", " h_size " ⟧ " => Gate.AppDens <| permInv h_size x


def interpGate
  (h_size : n <= i)
  (g : Gate n) (targets : PartialPerm n i)
  (ρ : DensityOp i)
  : DensityOp i
  := π⁻¹⟦ targets, h_size ⟧ <| (g.LiftRight h_size).AppDens <| π⟦ targets, h_size ⟧ <| ρ

notation:50 " G""⟦ " g ", " l ", " h " ⟧" => interpGate h g l

/-
  A Denotational semantics for circuits
  Circuits have application, measurement, and memory management (alloc, free)
-/
def sem : (Command i o) -> DensityOp i -> DensityOp o
  | .Done, ρ => ρ
  | .App h_size g targets rest, ρ => sem rest <| G⟦ g, targets, h_size ⟧ <| ρ -- not finished
  | .Meas q rest, ρ =>
    match i with
    | 0 => nomatch q
    | i' + 1 =>
      let vec : PartialPerm 1 _ := ⟨fun i : Fin 1 => q, by
        simp [Function.Injective]⟩
      sem rest <| π⁻¹⟦ vec, (by simp) ⟧ <| DensityOp.measureLeft <| π⟦ vec, (by simp) ⟧ <| ρ
  | .Alloc rest, ρ => sem rest <| ρ.extendRight
  | .Free q rest, ρ =>
    match i with
    | 0 => nomatch q
    | i' + 1 =>
        let vec : PartialPerm 1 _ := ⟨fun i : Fin 1 => q, by
        simp [Function.Injective]⟩
      sem rest <| DensityOp.traceLeft <| π⟦ vec, (by simp) ⟧ <| ρ

end Circuit
