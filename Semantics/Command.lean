import Semantics.Subsumption

open scoped Semantics

/--
  Now we can define the constructors for our language as containers:
-/
@[simp]
abbrev Command (data : Type) (arity : Nat) : Container
  := {shape:= data, pos := fun _ => Fin arity}


/-
  We now distinguish two different kinds of features

  Some features have no children - their arity is 0.
  We call these "terminal" features
-/
abbrev Terminal A := Command A 0

/-
  For these, the semantics is totally determined by their shape;
  in practise, this means that we can define the semantics in α
  over an extension into any type β

  An intuition you might have is all extensions (including the fixpoint) are isomorphic.
-/
instance
    Terminal.semantics
    [inst : Semantics A α]
    : Semantics ((Terminal A).extension β) α
  where
  sem | ⟨x, _⟩ => inst.sem x


/-
  We can derive a strengthening rule on terminal features as so:
-/
@[instance_reducible]
def Command.Terminal.Strengthening
  [instα : Semantics ((Terminal A).extension α) α]
  [str : α ⊑ β]
  : Semantics ((Terminal A).extension β) β
  := { sem | ⟨x, _⟩ => str.embed (instα.sem ⟨x,
      fun i => nomatch i⟩
    )}


/-
  For non-terminal or _structural_ containers, with positive
  arity, the semantics is defined in terms of the semantics
  of the children. For this to work, it needs ot be
  _parametric_ over the domain of child semantics α
-/
instance Command.semantics
    [instA : Semantics A ((Fin n -> α) -> α)]
    : Semantics ((Command A n).extension α) α
  where
    sem | ⟨a, children⟩ => instA.sem a children


/-
  An example of a structural feature: Sequencing

  We can give this a semantics in any domain α so long as it's a semigroup (i.e. we have associativity)

  Recall 'then'-ordering reads right to left
  (think matrix multiplication, function application, etc.)
-/
inductive ProgSeq' where | mk : ProgSeq'

instance ProgSeq'.sem α [Semigroup α]
    : Semantics ProgSeq' ((Fin 2 -> α) -> α)
  where
    sem _ children := (children 1) * (children 0)

-- ';' is a command with 2 children
def ProgSeq := Command ProgSeq' 2

@[instance_reducible, instance]
def ProgSeq.ext.sem : ∀ α [Semigroup α], Semantics (ProgSeq.extension α) α
  := fun α  _ => @Command.semantics _ _ _ (ProgSeq'.sem α)

@[instance_reducible, instance]
def ProgSeq.fix.sem := fun α [Semigroup α] => @Semantics.Container.fix _ _ (ProgSeq.ext.sem α)

variable (α : Type) [Semigroup α]
#synth Semantics ProgSeq.fix α
