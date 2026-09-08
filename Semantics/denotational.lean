import Semantics.Quantum.Gate
import Semantics.Quantum.GES
import Semantics.container


class Semantics α β where
  sem : α -> β

@[simp]
abbrev explicitSem {A} (B) := @Semantics.sem A B

notation "D""⟦ " x " ⟧" => Semantics.sem x
notation "D""⟦ " x " ⟧""@" B => explicitSem B x


/-
  read "A subsumes B"
  true if there's a semantics preserving function B -> A
-/
def Semantics.Subsumes (B A) {Y}
  [Semantics A Y] [Semantics B Y]
  : Prop
  := ∃ (f : B -> A), ∀x, (D⟦x⟧@Y) = D⟦f x⟧

infix:100 " ≺ " => Semantics.Subsumes
notation:100 B " ≺[" Y "] " A  => @Semantics.Subsumes B A Y _ _

-- We can define the semantics of simple coproducts like so:
instance coprodSem [Semantics α S] [Semantics β S]
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
@[simp]
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
instance semContainerFix (c : Container)
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

variable {α} [CommRing α] [StarRing α]

/-
  And now we show that the various semantic styles for QC
  are indeed "composable"
-/
instance {i}  : Composable (Gate i α) where
  compose x y := x.Compose y

/-
  Functions are composable
-/
instance {α : Type} : Composable (α -> α) where
  compose f g a  := f <| g a


end Composable
open scoped Composable

/-
  Super operators are just functions
-/
abbrev SuperOperator q α := (DensityOp q α -> DensityOp q α )

#synth ∀ i α, Composable (SuperOperator i α)

/- Semantic subsumption:
  A semantics as gates gives us a semantics as
  a super-operator (for free)
-/
instance {α} [CommRing α] [StarRing α] [Semantics A (Gate q α)]
  : Semantics A (SuperOperator q α)
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

instance autosem_a0 [Semantics X Y]
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

/-
  Obviously, there is a semantics-preserving function from any A into itself
-/
lemma subsume_refl [Semantics A Y]
  : A ≺[Y] A
  := by
    exists id
    intro x
    simp

@[simp]
def drop : a ⊕ a -> a
 | .inl a => a
 | .inr a => a

lemma subsume_coprod_self [Semantics A Y] :
  (A ⊕ A) ≺[Y] A
  := by
    exists drop
    intro x
    cases x
    <;> simp [Semantics.sem]

@[simp]
def strip {C : Container} : (C :+: C).fix -> C.fix
    := Container.recursor _ (fun a => match a with
    | .mk ⟨.inl x, f⟩ => ⟨x, fun a => (f a)⟩
    | .mk ⟨.inr x, f⟩ => ⟨x, fun a => (f a)⟩
    )

/-
  Taking a coproduct of a thing with itself does not give you any semantic power (as long as you use the usual Semantics instance for container coproducts)
-/
lemma self_subsume_coprod_self {Y} (C : Container)
  [CY_inst : Semantics (C.extension Y) Y]
  : (C :+: C).fix ≺[Y] C.fix
  := by
    exists strip
    intros x
    simp [Semantics.sem]
    induction x
    case mk s f ih =>
        rcases s with c | c
        <;> (
          simp [Container.recursor, innerSem_container_coprod];
          congr;
          ext a;
          apply ih
        )


@[simp]
def embed : C.fix -> (C :+: X).fix
  := Container.recursor _ (fun x => match x with
    | ⟨s, f⟩ => ⟨.inl s, fun a => f a⟩
  )

lemma coprod_any_subsume (C X: Container)
  [CY_inst : Semantics (C.extension Y) Y]
  [XY_inst : Semantics (X.extension Y) Y]
  : C.fix ≺[Y] (C :+: X).fix
  := by
    exists embed
    intro x
    induction x
    case mk s f ih =>
      simp [Semantics.sem, Container.recursor]
      congr
      ext
      apply ih
