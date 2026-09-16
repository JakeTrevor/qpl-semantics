import Quantum.Gate
import Quantum.GES
import Semantics.Container

open scoped Container

class Semantics α β where
  sem : α -> β

namespace Semantics

scoped notation:1000 "Sem""⟦ " x " ⟧" => Semantics.sem x
scoped notation:1000 "["B"]""Sem""⟦ " x " ⟧" => @Semantics.sem _ B _ x


instance Sum [Semantics α S] [Semantics β S]
    : Semantics (α ⊕ β) S
  where sem
    | .inl a => Sem⟦a⟧
    | .inr b => Sem⟦b⟧


/-
  We can use the recursor to give a semantics to the fixpoint
  given that we have semantics for the container extended into the domain.
-/
instance Container.fix (c : Container)
    [inst : Semantics (c.extension Y) Y]
    : Semantics (c.fix) Y
  where
    sem := c.recursor inst.sem


/-
  If we know the semantics of `a` and `b` in `Y`
  Then we can use a similar construction to the one above for
  Sum to define the semantics of the coproduct
-/
instance Container.coprod (a b : Container)
    [da : Semantics (a.extension Y) Y]
    [db : Semantics (b.extension Y) Y]
    : Semantics ((a :+: b).extension Y) Y
  where
    sem
      | ⟨.inl s, f⟩ => da.sem ⟨s, fun a' => f a'⟩
      | ⟨.inr s, f⟩ => db.sem ⟨s, fun b' => f b'⟩


/-
  The domain power relation
  read a ⊑ b as "a is weaker than b"

  'Weaker' is perhaps not the best term
  Some other potential contenders are:
    - a 'is dominated by' b
    - a 'is overcast by' b
-/
class Power α β where
  embed : α -> β
-- should also require:
--  prf : ∃ f, f ∘ embed = id

scoped infix:51 " ⊑ " => Power

@[instance_reducible]
def Power.strengthening
  (sem : Semantics A X) (str : X ⊑ Y)
  : Semantics A Y
  := {sem := str.embed ∘ sem.sem}


/-
  Superoperators are represented as endofunctions on density operators
-/
abbrev SuperOperator i α := Function.End <| DensityOp i α

/-
  An example of semantic power;
  A semantics as gates gives us a semantics as
  a super-operator (for free)
-/
instance Power.Gate_SuperOperator [CommRing α] [StarRing α]
    : (Gate i α) ⊑ (SuperOperator i α)
  where
    embed g := g.AppDens


@[instance_reducible, instance]
def Power.Gate_SuperOperator.str {α i}
  [inst : Semantics A (Gate i α)] [CommRing α] [StarRing α]
  : Semantics A (SuperOperator i α)
  := Power.strengthening inst Power.Gate_SuperOperator

end Semantics
