import Semantics.denotational

open scoped Gate.Compose


inductive App (i) (α)  where
  | app : (h_size : n <= i) ->  Gate n α -> PartialPerm n i -> App i α

variable {α} [CommRing α] [StarRing α]

def App.sem : App i α -> Gate i α
  | .app h_size g p =>
    let permGate := (p.toComplete h_size).toGate α
    (permGate.transpose) ∘ (g.LiftRight h_size) ∘ permGate


-- First we define the semantics of the constant part:
instance : Semantics (App i α) (Gate i α) where
  sem := App.sem

#synth Semantics (App 1 α) (Gate 1 α)

-- Then turn it into a command of arity 1
abbrev AppC i α := Command (App i α) 1


-- and we get the semantics for free:
#synth Semantics ((AppC 1 α).fix) (Gate 1 α)
