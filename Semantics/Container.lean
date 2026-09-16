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
