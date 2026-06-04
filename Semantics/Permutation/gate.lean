import Semantics.Permutation.Basic
import Semantics.Permutation.matrix
import Semantics.Quantum.Gate

namespace StdGates

lemma ID.isPerm : StdGates.ID.isPerm := by
  intro i
  apply And.intro
    <;> fin_cases i
    <;> simp [StdGates.ID]

lemma X.isPerm : StdGates.X.isPerm := by
  intro i
  apply And.intro
    <;> fin_cases i
    <;> simp [StdGates.X]

lemma CX.isPerm : StdGates.CX.isPerm := by
  intro i
  fin_cases i
    <;> apply And.intro
    <;> simp [StdGates.CX]
  next => exists 0; intro j; fin_cases j <;> simp
  next => exists 0; intro j; fin_cases j <;> simp
  next => exists 1; intro j; fin_cases j <;> simp
  next => exists 1; intro j; fin_cases j <;> simp
  next => exists 3; intro j; fin_cases j <;> simp
  next => exists 3; intro j; fin_cases j <;> simp
  next => exists 2; intro j; fin_cases j <;> simp
  next => exists 2; intro j; fin_cases j <;> simp

end StdGates

namespace PermList

def toGate (l : PermList n)
  : Gate n
  := sorry

theorem toGate_is_perm
  : ∀ (l : PermList n), l.toGate.isPerm
  := by sorry

end PermList
