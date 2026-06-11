/-
Cantor's theorem states that there cannot exist a surjection from a set to its power set.
-/

def Set (X: Type): Type :=
  X → Prop

def Surjective {X Y: Type} (f: X → Y): Prop :=
  ∀ y, ∃ x, f x = y

theorem CantorsTheorem (X: Type): ¬(∃ f: X → Set X, Surjective f) := by
  -- Assume towards contradiction we have some surjective f: X → 𝓟(X).
  intro ⟨f, hf⟩
  -- Define a set A := { x ∈ X | x ∉ f(x)}.
  let A: Set X := λ x ↦ ¬(f x) x
  -- Since f is surjective, and A ∈ 𝓟(X), we have some a ∈ X such that f(a) = A.
  have ⟨a, ha⟩ := hf A
  -- Definitionally, a ∈ A iff. a ∉ f(a).
  have h: A a ↔ ¬(f a) a := by rfl
  -- But f(a) = A, so this is a contradiction.
  rw [ha] at h
  exact iff_not_self h
