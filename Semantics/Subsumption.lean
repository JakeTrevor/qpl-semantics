import Semantics.Denotational


namespace Semantics
open scoped Semantics
/-
  A function is semantics preserving if:
    1. its input and output have semantics in the same terms
    2. The semantics of the input are the same as the semantics of the output
-/
@[simp]
def Preserving
    (f: A -> B) (X)
    [Semantics A X] [Semantics B X]
  := ∀ (x : A), [X]Sem⟦x⟧ = Sem⟦f x⟧

/-
  The composition of two semantics preserving functions is itself semantics preserving
-/
lemma Preserving.comp
  [Semantics A X] [Semantics B X] [Semantics C X]
  {f : B -> C}
  {g : A -> B}
  (pf : Preserving f X)
  (pg : Preserving g X)
  : Preserving (f ∘ g) X
  := by
    intro x
    rw [Function.comp_apply]
    rw [←pf (g x)]
    apply pg

/-
  read "A is subsumed by B"
  there's a semantics preserving function A -> B
-/
def Subsumes (A B) {X}
  [Semantics A X] [Semantics B X]
  : Prop
  := ∃ (f : A -> B), Preserving f X

scoped infix:100 " ≺ " => Semantics.Subsumes
scoped notation:100 A " ≺[" Y "] " B  => @Semantics.Subsumes A B Y _ _



theorem Subsumes.trans {A B C X}
  [Semantics A X] [Semantics B X] [Semantics C X]
  (pf : A ≺[X] B) (pg : B ≺[X] C)
  : A ≺[X] C
  := by
    rcases pf with ⟨f, pf⟩
    rcases pg with ⟨g, pg⟩
    exists (g ∘ f)
    apply Preserving.comp pg pf

lemma Subsumes.refl [Semantics A X]
  : A ≺[X] A
  := by exists id; simp

end Semantics

open scoped Semantics

lemma id.semPres {X} [Semantics A X]
  : Semantics.Preserving (@id A) X
  := by simp

@[simp]
def drop : a ⊕ a -> a
 | .inl a => a
 | .inr a => a

lemma drop.semPres {X} [Semantics A X]
  : Semantics.Preserving (@drop A) X
  := by simp [Semantics.sem]


lemma subsume_coprod_self [Semantics A X] :
  (A ⊕ A) ≺[X] A
  := by
    exists drop
    exact drop.semPres

open scoped Container

@[simp]
def strip {C : Container} : (C :+: C).fix -> C.fix
    := Container.recursor _ (fun a => match a with
    | .mk ⟨.inl x, f⟩ => ⟨x, fun a => (f a)⟩
    | .mk ⟨.inr x, f⟩ => ⟨x, fun a => (f a)⟩
    )

lemma strip.semPres
  {X} (C : Container)
  [Semantics (C.extension X) X]
  : Semantics.Preserving (@strip C) X
  := by
    intros x
    simp [Semantics.sem]
    induction x
    case mk s f ih =>
        rcases s with c | c
        <;> (
          simp [Container.recursor];
          congr;
          ext a;
          apply ih
        )
/-
  Taking a coproduct of a thing with itself does not give you any semantic power (as long as you use the usual Semantics instance for container coproducts)
-/
lemma self_subsume_coprod_self {X} (C : Container)
  [Semantics (C.extension X) X]
  : (C :+: C).fix ≺[X] C.fix
  := by
    exists strip
    apply strip.semPres


@[simp]
def embed : C.fix -> (C :+: X).fix
  := Container.recursor _ (fun x => match x with
    | ⟨s, f⟩ => ⟨.inl s, fun a => f a⟩
  )

lemma embed.semPres {C B : Container}
  [Semantics (C.extension X) X]
  [Semantics (B.extension X) X]
  : Semantics.Preserving (@embed B C) X
  := by
    intro x
    induction x
    case mk s f ih =>
      simp [Semantics.sem, Container.recursor]
      congr
      ext
      apply ih

lemma coprod_any_subsume (C B: Container)
  [Semantics (C.extension X) X]
  [Semantics (B.extension X) X]
  : C.fix ≺[X] (C :+: B).fix
  := by
    exists embed
    apply embed.semPres

@[simp]
def swap (A B : Container)
  : (A :+: B).fix -> (B :+: A).fix
  := Container.recursor _ (fun x => match x with
    | ⟨(.inl a), f⟩ => ⟨.inr a, fun q => f q⟩
    | ⟨.inr b, f⟩ => ⟨.inl b, fun q => f q⟩
    )

lemma swap.semPres
  [Semantics (A.extension X) X]
  [Semantics (B.extension X) X]
  : Semantics.Preserving (swap A B) X
  := by
    intro x
    induction x
    case mk s children ih =>
      cases s
      case inl s =>
        simp [Container.recursor, Semantics.sem]
        congr
        ext a
        apply ih
      case inr s =>
        simp [Container.recursor, Semantics.sem]
        congr
        ext a
        apply ih

lemma coprod_subsume_comm (A B : Container)
  [Semantics (A.extension X) X]
  [Semantics (B.extension X) X]
  : (A :+: B).fix ≺[X] (B :+: A).fix
  := by
    exists swap A B
    apply swap.semPres

def embed_right {C X : Container} : C.fix -> (X :+: C).fix
  := swap _ _ ∘ embed

lemma any_coprod_subsume (C B: Container)
  [Semantics (C.extension X) X]
  [Semantics (B.extension X) X]
  : C.fix ≺[X] (B :+: C).fix
  := by
  exists embed_right
  apply Semantics.Preserving.comp
    (swap.semPres) (embed.semPres)
