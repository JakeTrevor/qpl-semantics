import mathlib

def PartialPerm (a n : ℕ) := { f : Fin a -> Fin n // f.Injective }

abbrev Perm (n : ℕ) := PartialPerm n n

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
        have hx : a = n - (x +1) := by omega
        have ha : n = a + x + 1 := by omega
        rw [hx, ha]
        simp
      toComplete hlt' <| increment hlt' p

end PartialPerm
