import Semantics.denotational

inductive Meas i (α : Type) where
  | meas : Fin i -> Meas i α


def Meas.sem {i X} {α} [CommRing α] [StarRing α]
  : Meas i α -> GES X i α -> GES X i α
  | ⟨x⟩, s => s.measN x

instance
  {α} [CommRing α] [StarRing α]
  : Semantics
    (Meas i α)
    (GES X i α -> GES X i α)
  where
    sem := Meas.sem

-- Then turn it into a command of arity 1
abbrev MeasC i α := Command (Meas i α) 1


variable {α} [CommRing α] [StarRing α]
-- and we get the semantics for free:
#synth ∀ X, Semantics (Meas 1 α) (GES X 1 α -> GES X 1 α)
#synth ∀ X, Semantics ((MeasC 1 α).fix) ( GES X 1 α -> GES X 1 α)
