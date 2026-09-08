inductive Alloc i where
  | alloc :          Alloc i
  | Free  : Fin i -> Alloc i
