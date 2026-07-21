
structure Program (Command : Type) where
  cmds : List Command


inductive Gate (n : Nat) where
inductive PartialPerm (n m : Nat) where

inductive App where
  | app : (h_size : n <= i) ->  Gate n -> PartialPerm n i -> App

inductive Meas where
  | meas : Fin i -> Meas

inductive Classical {CInstr} where
  | instr : CInstr -> Classical

inductive Cond {CAddr} Body where
  | if : CAddr -> Body -> Cond Body

inductive CoCond {CAddr} where
  | mres : Fin i -> CAddr -> CoCond

inductive Alloc i where
  | alloc :          Alloc i
  | Free  : Fin i -> Alloc i

/-
  Error:
-/
#guard_msgs(substring:=true) in
structure ExprBroken (f : Type -> Type) where
  data : f (ExprBroken f)


-- instance {C X : Type} [DenotSem C X] [Monoid X] [Zero X]: DenotSem (Program C) X where
--   sem c := c.cmds
--   -- sem .mk x::xs = D⟦x⟧ + D⟦xs⟧ --recurse
