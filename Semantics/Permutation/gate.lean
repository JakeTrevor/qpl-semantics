import Semantics.Permutation.Basic
import Semantics.Permutation.matrix
import Semantics.Quantum.Gate

variable {α} [CommRing α] [StarRing α]
set_option linter.unusedSectionVars false
open scoped HTensor
namespace StdGates


lemma ID.isPerm : (StdGates.ID α).isPerm := by
  intro i
  apply And.intro
    <;> fin_cases i
    <;> simp [StdGates.ID]

lemma X.isPerm : (StdGates.X α).isPerm := by
  intro i
  apply And.intro
    <;> fin_cases i
    <;> simp [StdGates.X]

lemma CX.isPerm : (StdGates.CX α).isPerm := by
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


lemma SWAP.isPerm : (StdGates.SWAP α).isPerm := by
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

def swizzle (diff : Fin n) : Gate n α :=
  match h : diff with
  | ⟨0, _⟩ => StdGates.ID.mk α _
  | ⟨1, _⟩ => StdGates.ID.mk α _
  | ⟨x+2, p⟩ => (swizzle ⟨x + 1, (by omega)⟩).Compose <|
    cast (by
      suffices (n - (x + 2) + 2) + ((x + 2) - 2) = n by
        rw [this]
      have h :
        (n - (x + 2) + 2) + ((x + 2) - 2)
        = n - (x + 2 - 2) + (x + 2 - 2)
        := by
          have p1 : n >= (x + 2) := by omega
          have p2 : (x + 2) >= 2 := by omega
          omega
      rw [h]
      omega
    )
    (
      (
        (StdGates.ID.mk α (n - (x + 2)))
      ⨂
        (StdGates.SWAP α)
      : Gate ((n - (x + 2)) + 2) α
      )
    ⨂
      (StdGates.ID.mk α (((x + 2) - 2)))
    : Gate ((n - (x + 2) + 2) + ((x + 2) - 2)) α
    )

-- Convert L to a perm n-1
def toGate
  α [CommRing α] [StarRing α]
  (p : Perm n)
  : Gate n α
  := match n with
  | 0 => StdGates.Trivial α
  | _ + 1 => (
        (toGate α p.drop) ⨂ StdGates.ID α)
      *
        (swizzle <| p.invert.1 (Fin.last _)
      )

-- probably prove via
-- perm ⨂ perm = perm
-- perm ∘ perm = perm
theorem toGate_is_perm
  : ∀ (l : Perm n), (l.toGate α).isPerm
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
