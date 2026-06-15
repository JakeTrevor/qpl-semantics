import Semantics.Quantum.Gate
import Semantics.Permutation.Gate

namespace Unitary

inductive Command : (q : ℕ) -> Type where
  | Done : Command q
  | App : (h_size : n <= q) ->  Gate n -> PartialPerm n q -> Command q -> Command q


def interpretGate
 (h_size : n <= q) (g : Gate n) (p : PartialPerm n q)
 : Gate q
 :=
 Gate.Compose ((p.toComplete h_size).toGate.transpose)
  <| (g.LiftRight h_size).Compose
  (p.toComplete h_size).toGate

def sem : (Command q) -> Gate q
  | .Done => StdGates.ID.mk q
  | .App h_size g targets rest =>
    (sem rest).Compose (interpretGate h_size g targets)

end Unitary
