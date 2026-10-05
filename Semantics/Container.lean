/--
  A Container is a dependent pair.

  The first element (`shape : Type`) defines the type of shapes for the container

  `pos` is a function `shape -> Type`. It defines the holes in the container.
-/
structure Container where
  shape : Type u
  pos : shape -> Type u

namespace Container
structure extension (c : Container) (X : Type) : Type where
  out : Σ s : c.shape, c.pos s -> X

-- Extension is a functor; so it also has an action on functions (fmap)
def extension.fun (c : Container) (f : A -> B) : c.extension A -> c.extension B
  | ⟨sh, ch⟩ => ⟨sh, f ∘ ch⟩

/--
  The fixpoint of a container
  This is equivalent to `c.extension (c.fix)`
  But lean isn't happy to unfold the definition, so we have to inline it.
-/
structure fix (c : Container) where
  shapeInst : c.shape
  children : c.pos shapeInst -> (c.fix)

/--
  A recursor for containers
  if we know how to compress a container over Ys to a single Y
  then we can do it for the fixpoint:
-/
@[simp]
def recursor (c : Container)
  (inst : c.extension Y -> Y)
  : c.fix -> Y
  | .mk s f =>
    let f' := fun idx => recursor c inst <| f idx
    inst ⟨s, f'⟩


-- We can add two container types together to get a new container type:
def coprod (a b : Container.{u}) : Container
  := {
    shape := a.shape ⊕ b.shape,
    pos := fun x => match x with
      | Sum.inl pa => a.pos pa
      | Sum.inr pb => b.pos pb
  }

scoped infixr:100 ":+:" => Container.coprod

end Container


structure IContainer (Idx : Type) where
  Shape : Idx -> Type
  Pos : {i : Idx} -> (Shape i) -> Type
  Response : {i : Idx} -> (sh : Shape i) -> (p : Pos sh) -> Idx

namespace IContainer

structure extension (c : IContainer I) (X : I -> Type) (i : I) where
  sh : c.Shape i
  children : ((p : c.Pos sh) -> X (c.Response sh p))

def extension.fun {X Y : I -> Type} (c : IContainer I) (f : ∀ i, X i -> Y i)
  : c.extension X i -> c.extension Y i
  | ⟨sh, ch⟩ => ⟨sh, fun p => f _ (ch p)⟩


inductive  fix {I : Type} (c : IContainer I) : (i : I) -> Type where
  | out
    (sh : c.Shape i)
    (children : (p : c.Pos sh) -> c.fix (c.Response sh p))
    : c.fix i

def coprod (a b : IContainer I) : IContainer I
  := {
    Shape i := a.Shape i ⊕ b.Shape i
    Pos sh := match sh with
      | .inl aSh => a.Pos aSh
      | .inr bSh => b.Pos bSh
    Response sh p := match sh with
      | .inl aSh => a.Response aSh p
      | .inr bSh => b.Response bSh p
  }

end IContainer
