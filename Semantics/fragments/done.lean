import Semantics.denotational

variable {α} [CommRing α] [StarRing α]

instance {i} : Semantics Unit (Gate i α) where
  sem _ := StdGates.ID.mk α i

#synth Semantics Unit (Gate 1 α)


def DoneC := Command Unit 0

@[reducible]
def ex := @autosem_a0 Unit (Gate 1 α) _

@[reducible, instance]
def ex2 := @semContainerFix (Gate 1 α) DoneC ex

#synth Semantics DoneC.fix (Gate 1 α)
