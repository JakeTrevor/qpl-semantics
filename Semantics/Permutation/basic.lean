import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic
import Mathlib.Data.Vector.Basic

def PartialPerm (a n : ℕ) := { f : Fin a -> Fin n // f.Injective }

abbrev Perm (n : ℕ) := PartialPerm n n

namespace Perm

lemma bijective (p : Perm n) : p.1.Bijective := by
  rw [Fintype.bijective_iff_injective_and_card]
  apply And.intro
  case left => exact p.2
  case right => rfl

def List.mem_finIdxOf?_isSome [BEq α] [LawfulBEq α] {l : List α} {a : α}
  : a ∈ l -> (l.finIdxOf? a).isSome
  := by simp

@[simp]
def invert (p : Perm n) : Perm n
  := ⟨fun n =>
    cast (by simp) <| ((List.ofFn p.1).finIdxOf? n).get
      (by simp; apply p.bijective.2)
    , (by
      unfold Function.Injective
      intros a1 a2
      simp [Option.get_inj]

      have a1_some : ∃ i, List.finIdxOf? a1 (List.ofFn p.1)
        = some i
        := by
          rw [←Option.isSome_iff_exists]
          apply List.mem_finIdxOf?_isSome
          simp [List.mem_ofFn]
          apply p.bijective.2

      rcases a1_some with ⟨i, pi⟩

      have a2_some : ∃ j, List.finIdxOf? a2 (List.ofFn p.1)
        = some j
        := by
          rw [←Option.isSome_iff_exists]
          apply List.mem_finIdxOf?_isSome
          simp [List.mem_ofFn]
          apply p.bijective.2

      rcases a2_some with ⟨j, pj⟩
      rw [pi, pj]
      simp
      intro hij

      rw [List.finIdxOf?_eq_some_iff] at pi pj
      rcases pi with ⟨pi, _⟩
      rcases pj with ⟨pj, _⟩
      rw [hij] at pi
      rw [pi] at pj
      exact pj
      )⟩


-- annoying trivial cast lemma
lemma Fin.val_cast_invariant (x : m = n) (h : Fin m = Fin n) : (cast h v).val = v.val
  := by
    have p : h = congrArg Fin x := by simp
    rw [p]
    cases x
    simp


lemma helper34 (x : Fin n)
  (h : Fin n = Fin k) (h' : n = k)
  : (cast h x).val = x.val
  := by
      have p : h = (by rw [h]) := by simp
      rw [p]
      cases h'
      simp

lemma List.get_ofFn' {n : ℕ}
  (f : Fin n → α) (i : Fin n)
  : (List.ofFn f).get (cast (by simp) i) = f i
  := by
    simp
    conv =>
      lhs
      arg 1
      arg 1
      rw [helper34 i (by simp) (by simp)]


lemma helper99 {x : α} {y : β} (h : α = β): cast h x = y <-> x = cast h.symm y
  := by grind

lemma inv_is_inv (p : Perm n) : p.1 i = j <-> p.invert.1 j = i
  := by
  apply Iff.intro
  case mp =>
    intro h
    simp
    suffices List.finIdxOf? j (List.ofFn p.1)
      = (.some <| cast (by simp) i)
      by simp [this]

    rw [List.finIdxOf?_eq_some_iff]
    apply And.intro
    case left =>
      subst h
      simp
      apply congrArg
      simp [Fin.val_cast_invariant]
    case right =>
      intros k hk
      simp_all
      apply ne_of_lt at hk
      intros hkp
      subst hkp
      apply p.bijective.1 at h
      symm at h
      rcases i with ⟨i, pi⟩
      rcases k with ⟨k, pk⟩
      simp_all
      apply hk
      rw [Fin.eq_mk_iff_val_eq]
      simp [Fin.val_cast_invariant]
  case mpr =>
    simp
    rw [helper99]
    rw [←List.get_ofFn' p.1 i]
    intro h

    replace h : ∃ prf, (List.finIdxOf? j (List.ofFn p.1)).get prf = cast (by simp) i := by
      exists invert._proof_2 p j

    rw [←Option.eq_some_iff_get_eq,
        List.finIdxOf?_eq_some_iff,
    ] at h

    apply h.left



lemma inv_is_inv2 (p : Perm n) : p.1 (p.invert.1 x) = x
  := by rw [inv_is_inv]

def castLT_inj (n m : ℕ) (i j : Fin n) {hi : i < m} {hj : j < m}
  : i.castLT hi = j.castLT hj -> i = j
  := by
    simp [Fin.castLT, Fin.val_eq_val]


def drop (p : Perm (n + 1))
  : Perm n
  := ⟨fun i =>
  Fin.castLT (p.1 (Fin.succAbove (p.invert.1 (Fin.last _)) i)) (by
    set p_max := (p.1 ((p.invert.1 (Fin.last n)).succAbove i))
    suffices ¬(p_max = n) by
      rcases p_max with ⟨a, pa⟩
      omega
    subst p_max

    intro h

    set maxIdx := p.invert.1 (Fin.last n)

    replace h
      : p.1 (maxIdx.succAbove i) = p.1 maxIdx
      := by
        rw [←Fin.val_eq_val]
        have x : (p.1 maxIdx).val = n := by
          rw [inv_is_inv2]
          simp
        rw [x, h]

    apply Fin.succAbove_ne maxIdx i
    apply p.bijective.1
    exact h
  ), by
      unfold Function.Injective
      intro a1 a2 h
      simp only [] at h
      replace h
        : p.1 ((p.invert.1 (Fin.last n)).succAbove a1)
        = p.1 ((p.invert.1 (Fin.last n)).succAbove a2)
        := by
          apply castLT_inj (n + 1) n _ _ h
      set maxIdx := p.invert.val (Fin.last n)

      apply p.2 at h
      rwa [Fin.succAbove_inj] at h
  ⟩

end Perm

#print axioms Perm.drop

namespace PartialPerm

def increment (h : a < n) (p : PartialPerm a n)
  : PartialPerm (a+1) n
  := ⟨fun x =>
    let range := Finset.image p.1 Finset.univ
    let complement := (@Finset.univ (Fin n) _) \ range
    match finSumFinEquiv.symm x with
    | .inl x' => p.1 x'
    | .inr _ => complement.min' (by
      rcases p with ⟨f, pf⟩
      have pfr : range.card = a := by
        simp [range, Finset.card_image_of_injective _ pf]
      have pfc : complement.card = n - a := by
        simp [complement, Finset.card_sdiff_of_subset, pfr]
      simp [←Finset.card_pos, pfc, h]
    )
  , by
    rcases p with ⟨f, pf⟩
    unfold Function.Injective
    unfold Function.Injective at pf
    simp
    intros a1 a2
    set complement := (Finset.univ \ Finset.image f Finset.univ)

    have complement_nonempty : complement.Nonempty := by
      have pfr : (Finset.image f Finset.univ).card = a := by
        simp [Finset.card_image_of_injective _ pf]
      have pfc : complement.card = n - a := by
        simp [complement, Finset.card_sdiff_of_subset, pfr]
      simp [←Finset.card_pos, pfc, h]

    set x_new := complement.min' _


    by_cases h1 : a1 < a <;> by_cases h2 : a2 < a

    case pos =>
      simp [finSumFinEquiv, Fin.addCases, h1, h2]
      intro h
      have x := pf h
      suffices a1.val = a2.val
        by simp [←Fin.val_inj, this]
      simp_all [←Fin.val_inj]
    case neg =>
      simp [finSumFinEquiv, Fin.addCases, h1, h2]
      have px_new : x_new ∈ complement
        := Finset.min'_mem complement complement_nonempty

      intro aeq
      have px_image : x_new ∈ Finset.image f Finset.univ :=
        by
          rw [Finset.mem_image]
          set x := a1.castLT _
          exists x
          simp [aeq]

      subst complement

      rw [Finset.mem_sdiff] at px_new
      by_contra
      exact px_new.right px_image
    case pos =>
      simp [finSumFinEquiv, Fin.addCases, h1, h2]
      have px_new : x_new ∈ complement
        := Finset.min'_mem complement complement_nonempty


      intro aeq
      have px_image : x_new ∈ Finset.image f Finset.univ :=
        by
          rw [Finset.mem_image]
          set x := a2.castLT _
          exists x
          simp [aeq]
      subst complement

      rw [Finset.mem_sdiff] at px_new
      by_contra
      exact px_new.right px_image
    case neg =>
      simp [finSumFinEquiv, Fin.addCases, h1, h2]
      rcases a1 with ⟨a1', pa1⟩
      rcases a2 with ⟨a2', pa2⟩
      simp_all
      simp_all
      rw  [Nat.le_antisymm pa1 h1, Nat.le_antisymm pa2 h2]
  ⟩

def toComplete (hlt : a <= n) (p : PartialPerm a n)
  : Perm n
  := match h_diff : n - a with
    | 0 => cast (by
      have hna : n = a := by
        rw [Nat.sub_eq_zero_iff_le] at h_diff
        exact Nat.le_antisymm h_diff hlt
      rw [hna]
    ) p
    | x + 1 =>
      let hlt' : a + 1 <= n := by
        simp_all
        have hx : a = n - (x + 1) := by omega
        have ha : n = a + x + 1 := by omega
        rw [hx, ha]
        simp
      toComplete hlt' <| increment hlt' p

end PartialPerm


-- Here's a concrete example, to help convince you this works:
def perm1 : PartialPerm 2 6 := ⟨fun x => match x with
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3
  , by decide⟩

set_option maxRecDepth 2000
#reduce List.ofFn (PartialPerm.toComplete (by decide) perm1).1
#reduce List.ofFn (PartialPerm.toComplete (by decide) perm1).drop.1
#reduce List.ofFn (PartialPerm.toComplete (by decide) perm1).drop.drop.1
#reduce List.ofFn (PartialPerm.toComplete (by decide) perm1).drop.drop.drop.1
#reduce List.ofFn (PartialPerm.toComplete (by decide) perm1).drop.drop.drop.drop.1
#reduce List.ofFn (PartialPerm.toComplete (by decide) perm1).drop.drop.drop.drop.drop.1
#reduce List.ofFn (PartialPerm.toComplete (by decide) perm1).drop.drop.drop.drop.drop.drop.1
