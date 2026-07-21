structure Lens (Γ Δ : Type) where
  get : Γ -> Δ
  put : Δ × Γ -> Γ

namespace Lens

def putGet (l : Lens Γ Δ) : Prop :=
  ∀ x i, l.get (l.put (x, i)) = x

def getPut (l : Lens Γ Δ) : Prop :=
  ∀ i, l.put ((l.get i), i) = i

def idempotent (l : Lens Γ Δ) : Prop :=
  ∀ x i, l.put (x, l.put (x, i)) = l.put (x,i)

@[simp]
def wellBehaved (l : Lens Γ Δ) : Prop :=
  putGet l /\ getPut l

@[simp]
def veryWellBehaved (l : Lens Γ Δ) : Prop :=
  wellBehaved l /\ idempotent l

def Construction {a b c d e f : Type} :=
  (Lens a b) -> (Lens c d) -> (Lens e f )

@[simp]
def composition (l1 : Lens Γ Δ) (l2 : Lens Δ Θ)
  : Lens Γ Θ
  := {
    get := fun γ => l2.get (l1.get γ)
    put := fun (θ, γ) => l1.put (l2.put (θ, l1.get γ), γ)
  }


namespace composition
scoped infix:60 " ∘ " => composition

theorem putGet {l1 : Lens Γ Δ} {l2 : Lens Δ Θ}
  : (l1.putGet) -> (l2.putGet) -> (l1 ∘ l2).putGet
  := by
    repeat rw [Lens.putGet]
    intros h1 h2
    simp [h1, h2]

theorem getPut {l1 : Lens Γ Δ} {l2 : Lens Δ Θ}
  : (l1.getPut) -> (l2.getPut) -> (l1 ∘ l2).getPut
  := by
    repeat rw [Lens.getPut]
    intros h1 h2
    simp [h1, h2]

theorem wellBehaved {l1 : Lens Γ Δ} {l2 : Lens Δ Θ}
  : (l1.wellBehaved) -> (l2.wellBehaved) -> (l1 ∘ l2).wellBehaved
  := by
    intros h1 h2
    rw [Lens.wellBehaved]
    apply And.intro
    . case left => apply composition.putGet h1.left h2.left
    . case right => apply composition.getPut h1.right h2.right

theorem idempotent {l1 : Lens Γ Δ} {l2 : Lens Δ Θ}
  (l1pg : l1.putGet)
  : (l1.idempotent) -> (l2.idempotent) -> (l1 ∘ l2).idempotent
  := by
    repeat rw [Lens.idempotent]
    intros h1 h2
    intros x i
    simp [composition]
    rw [l1pg, h2, h1]

theorem veryWellBehaved {l1 : Lens Γ Δ} {l2 : Lens Δ Θ}
  : (l1.veryWellBehaved) -> (l2.veryWellBehaved) -> (l1 ∘ l2).veryWellBehaved
  := by
    intros h1 h2
    rw [Lens.veryWellBehaved]
    apply And.intro
    . case left => apply composition.wellBehaved h1.left h2.left
    . case right => apply composition.idempotent h1.left.left h1.right h2.right

end composition

@[simp]
def tensor {A B C D : Type}
  (l1 : Lens A B) (l2 : Lens C D)
  : Lens (A × C) (B × D)
  := {
    get := fun (a, c) => (l1.get a, l2.get c)
    put := fun ((b, d), (a, c)) => (l1.put (b, a), l2.put (d, c))
  }

namespace tensor
scoped infix:50 " ⊗ " => tensor

theorem putGet {l1 : Lens Γ Δ} {l2 : Lens Δ Θ}
  : (l1.putGet) -> (l2.putGet) -> (l1 ⊗ l2).putGet
  := by
    repeat rw [Lens.putGet]
    intros h1 h2
    simp [h1, h2]

theorem getPut {l1 : Lens Γ Δ} {l2 : Lens Δ Θ}
  : (l1.getPut) -> (l2.getPut) -> (l1 ⊗ l2).getPut
  := by
    repeat rw [Lens.getPut]
    intros h1 h2
    simp [h1, h2]

theorem wellBehaved {l1 : Lens Γ Δ} {l2 : Lens Δ Θ}
  : (l1.wellBehaved) -> (l2.wellBehaved) -> (l1 ⊗ l2).wellBehaved
  := by
    intros h1 h2
    rw [Lens.wellBehaved]
    apply And.intro
    . case left => apply tensor.putGet h1.left h2.left
    . case right => apply tensor.getPut h1.right h2.right

theorem idempotent {l1 : Lens Γ Δ} {l2 : Lens Δ Θ}
  : (l1.idempotent) -> (l2.idempotent) -> (l1 ⊗ l2).idempotent
  := by
    repeat rw [Lens.idempotent]
    intros h1 h2
    intros x i
    simp [tensor, h1, h2]

theorem veryWellBehaved {l1 : Lens Γ Δ} {l2 : Lens Δ Θ}
  : (l1.veryWellBehaved) -> (l2.veryWellBehaved) -> (l1 ⊗ l2).veryWellBehaved
  := by
    intros h1 h2
    rw [Lens.veryWellBehaved]
    apply And.intro
    . case left => apply tensor.wellBehaved h1.left h2.left
    . case right => apply tensor.idempotent h1.right h2.right

end tensor


@[simp]
def identity (A : Type) : Lens A A
  := {
    get := fun a => a
    put := fun (new, _)=> new
  }

namespace identity
theorem putGet : (Lens.identity A).putGet
  := by simp [Lens.putGet]

theorem getPut : (Lens.identity A).getPut
  := by simp [Lens.getPut]

theorem wellBehaved : (Lens.identity A).wellBehaved
  := by
    rw [Lens.wellBehaved]
    apply And.intro
    . case left => apply identity.putGet
    . case right => apply identity.getPut

theorem idempotent : (Lens.identity A).idempotent
  := by simp [Lens.idempotent]

theorem veryWellBehaved : (Lens.identity A).veryWellBehaved
  := by
    rw [Lens.veryWellBehaved]
    apply And.intro
    . case left => apply identity.wellBehaved
    . case right => apply identity.idempotent

end identity

-- This is a weird one.
@[simp]
def splitting_composition {A B C D : Type}
  (l1 : Lens A (B -> C))
  (l2 : Lens C D)
  : Lens A (B -> D)
  := {
    get := fun a b => l2.get ((l1.get a) b)
    put := fun (f, a) => l1.put (
      fun b => l2.put (f b, (l1.get a) b),
      a)
  }

namespace splitting_composition
scoped infix:50 "-<" => splitting_composition

theorem putGet {A B C D : Type}
  (l1 : Lens A (B -> C)) (l2 : Lens C D)
  (h1 : l1.putGet) (h2 : l2.putGet)
  : (l1 -< l2).putGet
  := by
    simp [Lens.putGet]
    intros x i
    ext b
    rw [h1, h2]


theorem getPut {A B C D : Type}
  (l1 : Lens A (B -> C)) (l2 : Lens C D)
  (h1 : l1.getPut) (h2 : l2.getPut)
  : (l1 -< l2).getPut
  := by
    simp [Lens.getPut]
    intros a
    suffices x : (
      (fun b ↦ l2.put (l2.get (l1.get a b), l1.get a b)) = (l1.get a)
      ) by rw [x, h1]
    ext b
    rw [h2]

theorem wellBehaved {A B C D : Type}
  (l1 : Lens A (B -> C)) (l2 : Lens C D)
  (h1 : l1.wellBehaved) (h2 : l2.wellBehaved)
  : (l1 -< l2).wellBehaved
  := by
    rw [Lens.wellBehaved]
    apply And.intro
    . case left => apply (splitting_composition.putGet l1 l2 h1.left h2.left)
    . case right => apply (splitting_composition.getPut l1 l2 h1.right h2.right)


theorem idempotent {A B C D : Type}
  (l1 : Lens A (B -> C)) (l2 : Lens C D)
  (h1 : l1.idempotent) (h2 : l2.idempotent)
  (h1' : l1.putGet)
  : (l1 -< l2).idempotent
  := by
    simp [Lens.idempotent]
    intros x a
    suffices h : (
      (fun b ↦ l2.put (x b, l1.get (l1.put (fun b ↦ l2.put (x b, l1.get a b), a)) b))
      = (fun b ↦ l2.put (x b, l1.get a b))
    ) by rw [h, h1]
    ext b
    rw [h1', h2]

theorem veryWellBehaved {A B C D : Type}
  (l1 : Lens A (B -> C)) (l2 : Lens C D)
  (h1 : l1.veryWellBehaved) (h2 : l2.veryWellBehaved)
  : (l1 -< l2).veryWellBehaved
  := by
    rw [Lens.veryWellBehaved]
    apply And.intro
    . case left => apply (splitting_composition.wellBehaved l1 l2 h1.left h2.left)
    . case right => apply (splitting_composition.idempotent l1 l2 h1.right h2.right h1.left.left)

end splitting_composition

-- Should rename
-- Something like "Product"
@[simp]
def concentrate {A B C : Type}
  : Lens ((A -> B) × (A -> C)) (A -> (B × C))
  := {
    get := fun (fb, fc) a => (fb a, fc a)
    put := fun (fbc, _old) => (fun a => (fbc a).fst, fun a => (fbc a).snd )
  }

namespace concentrate

theorem putGet {A B C : Type}
  : (@concentrate A B C).putGet
  := by simp [Lens.putGet]

theorem getPut {A B C : Type}
  : (@concentrate A B C).getPut
  := by simp [Lens.getPut]

theorem wellBehaved {A B C : Type}
  : (@concentrate A B C).wellBehaved
  := by
    rw [Lens.wellBehaved]
    apply And.intro
    . case left => apply concentrate.putGet
    . case right => apply concentrate.getPut


theorem idempotent {A B C : Type}
  : (@concentrate A B C).idempotent
  := by simp [Lens.idempotent]

theorem veryWellBehaved {A B C : Type}
  : (@concentrate A B C).veryWellBehaved
  := by
    rw [Lens.veryWellBehaved]
    apply And.intro
    . case left => apply concentrate.wellBehaved
    . case right => apply concentrate.idempotent

end concentrate


-- A raceless lens is one where all puts commute
-- ergo _race conditions_ are impossible
def raceless  (l : Lens Γ Δ) : Prop
  := ∀ (x y) (i), l.put (y, l.put (x, i)) = l.put (x, l.put (y, i))

namespace identity

theorem notRaceless : ∀ A, (∃ (a b : A), ¬(a = b)) ->   ¬((identity A).raceless) := by
  intro A h
  simp [raceless]
  rcases h with ⟨a, ⟨b, aneb⟩⟩
  exists b, a, a


end identity

end Lens
