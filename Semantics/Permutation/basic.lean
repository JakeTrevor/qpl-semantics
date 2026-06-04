import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Vector.Basic


def PermList (n : ℕ) := { v : List.Vector (Fin n) n // v.toList.Nodup }

namespace PermList

def nil : PermList 0 := ⟨⟨[], by decide⟩, by decide⟩

lemma nil_univ : ∀ (l : PermList 0), l = PermList.nil
  := by
    intros l
    have h_nil : l.1.toList = [] := by simp
    simp [nil]
    have ⟨⟨x, p_size⟩, _⟩ := l
    congr


def Partial {n m : ℕ} (_ : m <= n)  : Type :=
  { v : List.Vector (Fin n) m // v.toList.Nodup }

namespace Partial

def mkSingleton {n} (h : 1 <= n) (x : Fin n) : Partial h
  := ⟨⟨[x], by simp⟩, by simp⟩

def toComplete {h : m <= n} (l : Partial h)
  : PermList n
  := sorry

end Partial

end PermList


inductive myPerm : (n : ℕ) -> Type where
  | nil : myPerm 0
  | insert : (Fin (n + 1)) -> myPerm n -> myPerm (n + 1)
