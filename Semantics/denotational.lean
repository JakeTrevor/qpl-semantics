import Semantics.Langs.common
import Semantics.container

class Semantics α β where
  sem : α -> β

notation "D""⟦ " x " ⟧" => Semantics.sem x

-- We can define the semantics of simple coproducts like so:
instance [Semantics α S] [Semantics β S]
    : Semantics (α ⊕ β) S
  where sem
    | .inl a => D⟦a⟧
    | .inr b => D⟦b⟧


-- For containers, we need a bit more machinery.

/-
  Instead of working directly on fixpoints,
  we work on extensions over some type Y

  If we know how to compress (a b : Container) over Ys to a single Y,
  then we can do it for their coproduct over Ys
-/
def innerSem_container_coprod
  (a b : Container)
  [da : Semantics (a.extension Y) Y]
  [db : Semantics (b.extension Y) Y]
  : ((a.coProd b).extension Y) -> Y
  | ⟨.inl s, f⟩ => da.sem ⟨s, fun a' => f a'⟩
  | ⟨.inr s, f⟩ => db.sem ⟨s, fun b' => f b'⟩


/- The type class variant of above: -/
instance (a b : Container)
    [Semantics (a.extension Y) Y]
    [Semantics (b.extension Y) Y]
    : Semantics ((a.coProd b).extension Y) Y
  where
    sem := innerSem_container_coprod a b

/- We can then use the recursor to give a semantics to the fixpoint: -/
instance (c : Container)
    [inst : Semantics (c.extension Y) Y]
    : Semantics (c.fix) Y
  where
    sem := c.recursor inst.sem


/-
  Define a type class that encapsulates the notion of
  'combining' elements of a semantics

  'semigroup' would be OK here,
  as would 'monoid'
  but both of those require more work
  and the pre-existing mathlib instances for matrices get in the way for gate.

  So this slightly hacky solution is easier

  A better way to handle this might be to make `Gate`
  a boxed Matrix, rather than an abbrev
-/
class Composable (X : Type) where
  compose : X -> X -> X

namespace Composable
scoped infix:100 " <> " => Composable.compose

/-
  And now we show that the various semantic styles for QC
  are indeed "composable"
-/
instance {i} : Composable (Gate i) where
  compose x y := x.Compose y

instance {α : Type} : Composable (α -> α) where
  compose f g a  := f <| g a


end Composable
open scoped Composable

abbrev SuperOperator q := (DensityOp q -> DensityOp q)

-- Sanity check:
-- the above generic instance should work for super-operators
#synth ∀ i, Composable (SuperOperator i)

/- Semantic subsumption:
  A semantics as gates gives us a semantics as
  a super-operator (for free)
-/
instance [Semantics A (Gate q)]
  : Semantics A (SuperOperator q)
where
    sem a ρ := Gate.AppDens D⟦a⟧ ρ

/-
  Some automation:

  If You give a semantics in terms of some carrier type X
  Then we can automate the generation of the semantics of the
  containerised versions.
-/

variable {X Y}

def innerSem_arity_0 [Semantics X Y]
  : ((Command X 0).extension Y) -> Y
  | ⟨x, _⟩ => D⟦@cast _ X (by simp) x⟧

instance [Semantics X Y]
  : Semantics ((Command X 0).extension Y) Y where
  sem := innerSem_arity_0

def innerSem_arity_1 [Semantics X Y] [Composable Y]
  : ((Command X 1).extension Y) -> Y
  | ⟨x, mkCont⟩ =>
    (mkCont<| Fin.mk 0 (by simp) )<> D⟦@cast _ X (by simp) x⟧

instance [Semantics X Y] [Composable Y]
    : Semantics ((Command X 1).extension Y) Y
  where
    sem := innerSem_arity_1
