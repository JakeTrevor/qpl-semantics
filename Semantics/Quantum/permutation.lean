import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FinCases

import Semantics.Quantum.Gate

lemma List.nodup_card_bijective
  [Fintype α] (l : List α)
  (p_len : l.length = Fintype.card α )
  : l.Nodup <-> Function.Bijective l.get
  := by
    apply Iff.intro
    case mp =>
      intro p_nodup
      rw [List.nodup_iff_injective_get] at p_nodup
      rw [Fintype.bijective_iff_injective_and_card]
      apply And.intro
      case left => exact p_nodup
      case right => rw [Fintype.card_fin, p_len]
    case mpr =>
      intro p_bij
      rw [List.nodup_iff_injective_get]
      exact p_bij.1

namespace PermList


lemma get_bijective : ∀ (p : PermList n) (k : Fin n), k ∈ p.1.1
  := by
    intros p k
    rcases p with ⟨⟨p, p_size⟩, p_nodup⟩
    apply fundamental p p_nodup p_size

lemma helper1 {α} {i : ℕ} {x y : α} {l : List α}
  : x ≠ y -> x ∉ l -> x ∉ (l.insertIdx i y)
  := by
    intros a b h
    apply List.eq_or_mem_of_mem_insertIdx at h
    cases h with
    | inl a' => exact a a'
    | inr b' => exact b b'

lemma List.nodup_insertIdx {l : List α}
  : l.Nodup -> x ∉ l -> (l.insertIdx i x).Nodup
  := by
    intros h nin
    induction i with
    | zero => simp; exact And.intro nin h
    | succ n' ih => cases l with
      | nil => simp
      | cons head tail =>
        simp
        rw [List.nodup_cons] at h
        rcases h with ⟨head_tail, tail_nodup⟩
        simp [List.mem_cons] at nin
        rcases nin with ⟨x_nhead, x_ntail⟩
        apply And.intro
        . apply helper1
          . intros a'
            exact x_nhead a'.symm
          . exact head_tail
        . exact List.nodup_insertIdx tail_nodup x_ntail

def insert  (x : PermList n) (i : Fin (n + 1)) : PermList (n+ 1)
  := ⟨((x.1.map Fin.castSucc).insertIdx (Fin.last n) i), by
    set l' := x.1.map Fin.castSucc
    have l'_nodup : l'.1.Nodup := by
      subst l'
      have ⟨⟨x', px'⟩ , px''⟩ := x
      simp [List.Vector.map]
      simp at px''
      rw [List.nodup_map_iff (Fin.castSucc_injective _ )]
      exact px''
    simp [List.Vector.insertIdx]
    apply (List.nodup_insertIdx l'_nodup)
    suffices ∀ a ∈ l'.1, a < n by
      intros h
      have p := this _ h
      simp at p
    subst l'
    intros a h
    suffices ∃ x , a = Fin.castSucc x by
      apply this.elim
      intros x
      have ⟨x, px⟩ := x
      intros h
      rw [h]
      simp
      exact px
    simp [List.Vector.map] at h
    have ⟨⟨x, px_len⟩, px_nodup⟩ := x
    simp at h
    apply h.elim
    intros x h
    exists x
    exact h.right.symm
  ⟩

def List.nodup_erase
  [BEq α] [LawfulBEq α]
  {x : α} {l : List α}
  : l.Nodup -> x ∈ l -> x ∉ l.erase x
  := by
      intros l_nodup xl h
      rw [List.nodup_iff_count_eq_one] at l_nodup
      specialize l_nodup x xl
      have h2 := @List.count_erase  _ _ _ x x l
      have h3 : List.count x (l.erase x) = 0 := by simp_all
      have h4 :=  List.not_mem_of_count_eq_zero h3
      exact h4 h

def List.erase_nodup
  [BEq α] [LawfulBEq α]
  {x : α} {l : List α}
  : l.Nodup -> (l.erase x).Nodup
  := by
      intros h_nodup
      cases l
      case nil => simp
      case cons head tail =>
        rw [List.nodup_cons] at h_nodup
        rcases h_nodup with ⟨head_tail, tail_nodup⟩
        by_cases h : head = x
        case pos =>
          unfold List.erase
          simp [h]
          exact tail_nodup
        case neg =>
          simp [h]
          apply And.intro
          . exact head_tail
          . exact List.erase_nodup tail_nodup

lemma List.map_nodup {f : α → β} {l : List α}
  (hf : Function.Injective f) (nf : l.Nodup)
  : (List.map f l).Nodup
  := by
    simpa [List.nodup_map_iff hf]

def dropTop {n : ℕ} (p : PermList (n + 1))
  : (PermList n) × (Fin (n + 1))
  :=
    let idx : Fin (n + 1) := cast (by simp)
      ((p.1.1.finIdxOf? (Fin.last n)).get (by simp [get_bijective]));
    let l' : PermList n := ⟨⟨
        (p.1.1.erase (Fin.last n)).attach.map ((fun x => x.1.castPred (by
          rcases p with ⟨⟨p, p_size⟩, p_nodup⟩
          have h_last : Fin.last n ∈ p := by
            simp [fundamental p p_nodup p_size]

          have last_nin := List.nodup_erase p_nodup h_last
          simp_all
          intro contra
          have px := x.2
          rw [contra] at px
          apply last_nin px
        ))),
        (by
          rcases p with ⟨⟨p, p_size⟩, p_nodup⟩
          have h_last : Fin.last n ∈ p := by
            simp [fundamental p p_nodup p_size]
          simp [h_last, p_size]
        )⟩, (by
          cases p
          case mk p p_nodup =>
          simp at p_nodup
          cases p
          case mk p p_size =>
            simp_all [List.Vector.toList]
            suffices (p.erase (Fin.last n)).attach.Nodup by
              apply List.map_nodup
              case nf => exact this
              case hf =>
                -- stuck!
                change Function.Injective (fun x : {x // x ∈ p.erase (Fin.last n)} => x.1.castPred _ )
                simp [Function.Injective]
                intros a b a' b' assm

                -- here
            sorry
        )⟩
    ⟨l', idx⟩


def List.nodup_eraseIdx
  [BEq α] [LawfulBEq α]
  {x : α} {l : List α}
  {i : ℕ} {inBounds : i < l.length}
  : l.Nodup -> l[i] = x -> x ∉ l.eraseIdx i
  := by
      intros l_nodup xl h
      rw [List.nodup_iff_count_eq_one] at l_nodup
      have xmem : x ∈ l := by
        rw [List.mem_iff_get]
        exists ⟨i, inBounds⟩

      specialize l_nodup x xmem
      have h2 := @List.count_erase  _ _ _ x x l
      have h3 : List.count x (l.erase x) = 0 := by simp_all
      have h4 :=  List.not_mem_of_count_eq_zero h3

      exact h4 h

lemma kmn : ∀ (x : Fin (n +1)), ↑x < n  <-> x < Fin.last n
  := by
    intro ⟨x, p⟩
    simp [Fin.last]

@[simp]
def insert_uncurry {n : ℕ} := @Function.uncurry (PermList n) (Fin (n + 1)) _ insert


lemma insert_inj {n : ℕ}
  : Function.Injective (@insert_uncurry n)
  := by sorry

lemma insert_surj {n : ℕ}
  : Function.Surjective (@insert_uncurry n)
  := by
    sorry




lemma insert_covering :
  ∀ (x : PermList (n + 1)),
  ∃(p : PermList n), ∃ y,
    x = p.insert y
  := by
    intros x
    have h_last := permlist_fundamental x (Fin.last n)
    rcases x with ⟨⟨x, px_size⟩, px_nodup⟩
    simp at h_last

    exists ⟨⟨(x.eraseIdx ((x.idxOf (Fin.last n)))).attach.map
      (fun ⟨itm, h_itm⟩ => itm.castLT (by
        rw [kmn]
        suffices itm ≠ Fin.last n by
          simp_all [Fin.lt_last_iff_ne_last]
        intro contra
        rw [contra] at h_itm
        simp_all
        apply List.nodup_erase px_nodup h_last h_itm
      )), by
        simp [*]⟩, by
        -- suffices _
        simp [List.nodup_map_iff]
        sorry⟩

    exists cast (by congr)
      ((x.finIdxOf? (Fin.last n)).get (by simp [h_last]))

    congr
    simp [List.Vector.map, List.erase_eq_eraseIdx]
    have q : ∃ z, (List.idxOf? (Fin.last n) x) = .some z := by
      rw [List.mem_iff_get] at h_last
      apply h_last.elim
      intros k p
      exists k
      rw [List.idxOf?_eq_some_iff]

      simp [h_last]


    sorry



def casesOn : {m : ℕ}
  -> {motive : {n : ℕ} -> PermList n -> Sort}
  -> (v : PermList m)
  -> motive PermList.nil
  ->
    ({n : ℕ} -> (pos : Fin (n + 1) )
    -> (l : PermList n)
    -> motive (l.insert pos))
  -> motive v
  := by
    intros n motive v p_nil p_succ
    cases n with
    | zero =>
      rw [nil_univ v]
      exact p_nil
    | succ n =>
      rcases (insert_covering v) with ⟨l, ⟨pos, h⟩⟩
      rw [h]
      exact p_succ pos l

def toList (l : PermList n) : List (Fin n) := l.1.toList

instance (n : ℕ) : Membership (Fin n) (PermList n) where
  mem := fun x i => i ∈ x.toList


def Partial {n m : ℕ} (_ : m <= n) : Type :=
  { v : List.Vector (Fin n) m // v.toList.Nodup }

namespace Partial

def toList {h : m <= n} (l: Partial h) : List (Fin n)
  := l.1.toList

end Partial

instance (n : ℕ) (h : m <= n) : Membership (Fin n) (Incomplete h) where
  mem := fun x i => i ∈ x.toList

lemma is_complete (x : PermList n)
  : ∀ (i : Fin n), i ∈ x
  := by
    induction x.1


def Incomplete.completeTargets {h : m <= n} (l : Incomplete h) : PermList n
  := ⟨_, _⟩
    where
      base' := Vector.eraseMany (Vector.finRange n) l.1 (by
        intros x h
        apply Vector.finRange_mem x
      ) l.2
      p : m + (n - m) = n := by sorry
      h : Vector (Fin n) (m + (n - m))  = Vector (Fin n) n := sorry
      all : Vector (Fin n) n := h ▸ (l.1 ++ base')


end PermList

#check Vector.finRange

/--
Given a target list (possibly incomplete) and a size `N`,
fill in the missing indices from `0..N-1` in ascending order.
Example: `completeTargets 6 [1,5,4] = [1,5,4,0,2,3]`
-/
def completeTargets (N : Nat) (targets : List Nat) : List Nat  :=
  let base := List.range N
  let missing := base.filter (fun x => ¬ x ∈ targets)
  targets ++ missing


#check List.nodup_iff_count_le_one
#print List.Nodup
-- ShiftLast (n) :=

def makeMat (targets : Vector (Fin N) N) : Gate N :=
  sorry

/--
Generate a permutation matrix (over Nat) from a possibly incomplete
target list, filling in the rest automatically.
-/
def permMatrix (N : Nat) (targets : List (Fin N)) : Matrix (Fin N) (Fin N) Nat :=
  makeMat <| completeTargets N targets

def invPermMatrix (N : Nat) (targets : List (Fin N)) : Matrix (Fin N) (Fin N) Nat :=
  makeMat <| inversePerm <| completeTargets N targets

def IDn (n : Nat) : Matrix (Fin n) (Fin n) Nat := fun i j => if i == j then 1 else 0

theorem perm_inv_is_inv : ∀ N t, permMatrix N t * invPermMatrix N t = IDn N := by
  intros N t
  ext i j
  sorry

#eval completeTargets 6 [1, 5, 4]
#eval inversePerm <| completeTargets 6 [1, 5, 4]

#eval permMatrix 6 [1, 5, 4]


-- def unique {N α} (l : Vector α N) :=
--   ∀ (i j : (Fin N)), ¬(i = j) -> ¬(l[i] = l[j])

-- def PartialPermList (N : ℕ) (m : Fin N) := {x : Vector (Fin N) m // unique x}

-- def PermList (N : ℕ) := {x : Vector (Fin N) N // unique x}


-- def a : PermList 2 := ⟨⟨Array.mk [0,1], by decide⟩, by
--   intros i j h; fin_cases i <;> fin_cases j <;> aesop
-- ⟩


def completeTargets (N : Nat) (targets : List Nat) : List Nat  :=
  let base := List.range N
  let missing := base.filter (fun x => ¬ x ∈ targets)
  targets ++ missing

def Vector.FinRange (n) : Vector (Fin n) n :=
  match n with
  | 0 => ⟨Array.mk [], by decide⟩
  | .succ n' =>
    let l' := Vector.FinRange n'
    let new : Vector (Fin (n'+1)) 1 :=
      ⟨Array.mk [⟨n', _⟩], _⟩
    let p := l'.cast (Fin.castLT)
    (@cast _ (Vector (Fin (n'+1)) n') _ l').append new

def complete {n m} (l : PartialPermList n m) : PermList n :=
  let base  := List.range n
  let missing : Vector (Fin n) (n - m) := base.filter (fun x => ¬ x ∈ l)
  ⟨l.val ++ missing, sorry⟩
