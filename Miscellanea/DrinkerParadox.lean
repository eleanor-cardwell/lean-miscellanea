/-
The drinker paradox is usually stated as follows:

"There is someone in the pub such that, if he is drinking, then everyone in the pub is drinking."

This claim is true formally, yet does not sound convincing when stated plainly. The paradox follows
from the difference between plain English and formal logic in the usage of "if ... then".

A caveat: the set of people in the pub must be nonempty for the claim to hold.
-/

theorem DrinkerParadox (person: Type) (h₀: Nonempty person) (drinking: person → Prop): ∃ P₀: person, drinking P₀ → ∀ P: person, drinking P := by
  by_cases h: ∀ P: person, drinking P
  · have P := Classical.choice h₀
    exists P
    intro _
    exact h
  · rw [Classical.not_forall] at h
    have ⟨P, _⟩ := h
    exists P
    intro _
    contradiction
