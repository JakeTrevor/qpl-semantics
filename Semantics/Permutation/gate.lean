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


lemma SWAP.isPerm : StdGates.SWAP.isPerm := by
  intro i
  fin_cases i
    <;> apply And.intro
    <;> simp [StdGates.SWAP]
  next => exists 0; intro j; fin_cases j <;> simp
  next => exists 0; intro j; fin_cases j <;> simp
  next => exists 2; intro j; fin_cases j <;> simp
  next => exists 2; intro j; fin_cases j <;> simp
  next => exists 1; intro j; fin_cases j <;> simp
  next => exists 1; intro j; fin_cases j <;> simp
  next => exists 3; intro j; fin_cases j <;> simp
  next => exists 3; intro j; fin_cases j <;> simp

end StdGates

namespace Perm

-- -- swap i with i +1
-- def swizzle (x : Fin n) : Gate n :=
--   if h : x = n - 1 then
--     StdGates.ID.mk _
--   else
--     swizzle (x + 1) * (cast (by
--       suffices (↑x + 2 + (n - 2 - ↑x)) = n by rw [this]
--       rcases x with ⟨x, hx⟩
--       omega
--     ) (((StdGates.ID.mk x)
--       ⨂ (StdGates.SWAP))
--       ⨂ (StdGates.ID.mk (n - 2 - x ))))

lemma helper : ∀ (a b c : ℕ),
  a >= b ->
  b >= c ->
  a - b + c = a - (b - c)
  := by
    intro a b c
    omega

def swizzle (diff : Fin n) : Gate n :=
  match h : diff with
  | ⟨0, _⟩ => StdGates.ID.mk _
  | ⟨1, _⟩ => StdGates.ID.mk _
  | ⟨x+2, p⟩ => (swizzle ⟨x + 1, (by omega)⟩).Compose <|
    cast (by
      suffices (n - (x + 2) + 2 + (x + 2 - 2)) = n by
        rw [this]
      have h :
        n - (x + 2) + 2 + (x + 2 - 2)
        = n - (x + 2 - 2) + (x + 2 - 2)
        := by
          have p1 : n >= (x + 2) := by omega
          have p2 : (x + 2) >= 2 := by omega
          rw [helper _ _ _ p1 p2]
      rw [h]
      omega
    )
    (((StdGates.ID.mk (n - (x + 2)))
      ⨂ (StdGates.SWAP))
      ⨂ (StdGates.ID.mk (((x + 2) - 2))))

-- Convert L to a perm n-1
def toGate (p : Perm n)
  : Gate n
  := match n with
  | 0 => StdGates.Trivial
  | _ + 1 => ((toGate p.drop) ⨂ StdGates.ID).Compose (swizzle <| p.invert.1 (Fin.last _))

-- probably prove via
-- perm ⨂ perm = perm
-- perm ∘ perm = perm
theorem toGate_is_perm
  : ∀ (l : Perm n), l.toGate.isPerm
  := by sorry

end Perm

-- lemma Tensor.preservePerm : ∀ (p : Gate n) (q: Gate m),
--   p.isPerm -> q.isPerm -> (p ⨂ q).isPerm
--   := by
--     intro p q pperm qperm
--     simp_all [Matrix.isPerm]


-- lemma Compose.preservePerm : ∀ (p : Gate n) (q: Gate n),
--   p.isPerm -> q.isPerm -> (p.Compose q).isPerm
--   := by
--     intro p q pperm qper
--     simp_all [Matrix.isPerm]
--     intro i
--     apply And.intro
--     . simp
--     . sorry
