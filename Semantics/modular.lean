/-
  If we just blindly apply Swierstra's DTalC, we end
  up with a non-positive definition, which lean does not permit.
  So we need to find a way to deal with that.
  HOAS is another very powerful technique which is unfortunately non-positive
  PHOAS solves this by removing the need for a negative occurence
  and instead replacing it with a parameter of the type
  which we can instantiate with the type itself as and when.

  The positivity is broken here
-/
inductive Expr {X : Nat -> Type} (F : _ -> _)  where
  | mk : F X -> Expr F

inductive myProd (A B : (Nat -> Type) -> Type) : (Nat -> Type) -> Type where
  | left : A X -> myProd A B X
  | right : B X -> myProd A B X


infix:50 ":+:" => myProd

inductive Gate (n : Nat) where
inductive PartialPerm (n m : Nat) where

-- modular definition:
inductive pDone (X : Nat -> Type) : Type where
  | done : pDone X

inductive App (X : Nat -> Type) : Type where
  | app : (h_size : n <= i) ->  Gate n -> PartialPerm n i -> X i -> App X

inductive Meas (X : Nat -> Type) : Type where
  | meas : Fin i -> X i -> Meas X

inductive Classical {CInstr} (X : Nat -> Type) : Type where
  | instr : CInstr -> X i -> Classical X

inductive Cond {CAddr} (X : Nat -> Type) : Type where
  | if : CAddr -> X i -> X i -> Cond X

inductive CoCond {CAddr} (X : Nat -> Type) : Type where
  | mres : Fin i -> CAddr -> X i -> CoCond X


def Unitary {X} := @Expr X <| pDone :+: App


--- Attempt 3


structure Program Command where
  cmds : List Command
