import logic.basic -- Needed for imp_false

section question2

variable R : Prop
variables S T : Prop
variable h : S ∧ T
variable h₁ : S → T
variable h₂ : S

end question2

section question5

variables P Q : Prop

example : ¬P ∨ ¬Q → ¬(P ∧ Q) :=
begin
  intros h₁ h₂, -- you can introduce off a ¬
  -- have h₃ : P, from h₂.1,
  -- have h₄ : Q, from h₂.2,
  cases h₁ with h₅ h₆, -- you can use cases to split an ∨
  { --apply h₅, exact h₃,
    exact h₅ h₂.1}, -- you can use dot notation to point at the part of the ∧ 
  { -- apply h₆, exact h₄,
    exact h₆ h₂.2}, -- you can compact `apply` `exact` into just `exact`.
end

end question5

section question8

variables N S I : Prop

open classical
local attribute [instance] prop_decidable

#check imp_false.mpr

example (h₁ : N ↔ (S ↔ I)) (h₂ : I ↔ S) (h₃ : S ↔ ¬N) : N ∧ (¬S ∧ ¬I) :=
begin
  by_cases h₄ : S,
  { exfalso,
    apply imp_false.mpr,
    { rw h₃ at h₄,
      apply h₄},
    { rw [h₂, iff_self, iff_true] at h₁,
      exact h₁,
    },
  },
  { 
    sorry},
end

example (h₁ : N ↔ (S ↔ I)) (h₂ : I ↔ S) (h₃ : S ↔ ¬N) : N ∧ (¬S ∧ ¬I) :=
begin
  by_cases h₄ : S,
  { exfalso,
    apply imp_false.mpr,
    { rw h₃ at h₄,
      exact h₄, },
    { rw [h₁, ←h₂], },
    },
  { have h₅ : N,
    { rw [h₁, ←h₂], },
    have h₆ : ¬I,
    { rwa h₂, },
    exact ⟨h₅, h₄, h₆⟩, },
end

end question8

