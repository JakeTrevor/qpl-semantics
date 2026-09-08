/--
  A Container is a dependent pair.

  The first element (`shape : Type`) defines the type of shapes for the container

  `pos` is a function `shape -> Type`. It defines the holes in the container.
-/
structure Container where
  shape : Type u
  pos : shape -> Type v

structure Container.extension (c : Container) (X : Type) : Type where
  out : Σ s : c.shape, c.pos s -> X

/--
  The fixpoint of a container
  This is equivalent to `c.extension (c.fix)`
  But lean isn't happy to unfold the definition, so we have to inline it.
-/
structure Container.fix (c : Container) where
  shapeInst : c.shape
  children : c.pos shapeInst -> (c.fix)

/--
  A recursor for containers
  if we know how to compress a container over Ys to a single Y
  then we can do it for the fixpoint:
-/
def Container.recursor (c : Container)
  (inst : c.extension Y -> Y)
  : c.fix -> Y
  | .mk s f =>
    let f' := fun idx => recursor c inst <| f idx
    inst ⟨s, f'⟩


-- We can add two container types together to get a new container type:
def Container.coProd (a b : Container) : Container
  := {
    shape := a.shape ⊕ b.shape,
    pos := fun x => match x with
      | Sum.inl pa => a.pos pa
      | Sum.inr pb => b.pos pb
  }

infixr:100 ":+:" => Container.coProd

/--
  Now we can define the constructors for our language as containers:
-/
@[simp]
abbrev Command (data : Type) (arity : Nat) : Container
  := {shape:= data, pos := fun _ => Fin arity}


/-
-- Examples:
@[simp]
def list : Container := { shape := Nat, pos := fun n => Fin n }
def listEx : list.extension Nat  :=
  ⟨ cast (by simp) 1, fun x => 0⟩
-/

-- /--
--   Even worse than containers, we have indexed containers
--   If containers are complicated, these are even more so.
-- -/
-- structure IndexedContainer where
--   Idx : Type
--   Shape : Idx -> Type
--   Pos : {i : Idx} -> Shape i -> Type
--   -- n : {i : Idx} -> (s : Shape i) -> (r : Pos s ) -> S

-- -- God this is so awful
-- structure IndexedContainer.extension
--     (c : IndexedContainer) (Y : c.Idx -> Type) i : Type
--   where
--     out : Σ s : c.Shape i, (c.Pos s -> Y _)


-- inductive lam where
--   | app
--   | abs

-- def Lam : Container := {
--   shape := lam,
--   pos s := match s with
--     | .app => Fin 2
--     | .abs => ∀ T, Lam.extension T
-- }
