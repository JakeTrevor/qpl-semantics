import Semantics.lens
import Semantics.denotational
import Semantics.container

def AddressLens {S : Type} := Lens S Bool

inductive Classical {CInstr} where
  | instr : CInstr -> Classical

-- cannot give semantics to this...
inductive Cond' (CAddr) where
  | if : CAddr -> Cond' CAddr

def Cond {CAddr : Type} := Command (Cond' CAddr) 2


instance : DenotSem Cond _ where
  sem

inductive CoCond' (CAddr) where
  | mres : Fin i -> CAddr -> CoCond' CAddr

def CoCond {CAddr : Type} := Command (Cond' CAddr) 1
