section question9

variables A B C : Prop

example (h : C → A ∨ B) : (C ∧ ¬A) → B :=
begin
  intro h₁, -- N.B. What happens if you try `split` instead of `intro`?
  cases h₁ with h₂ h₃,
  have h₄ : A ∨ B, from h h₂, -- What happens if you write `h h₂` instead?
  cases h₄ with h₅ h₅, -- Or elimination.
  { exfalso,
    exact h₃ h₅,
    -- contradiction, 
  },
  { exact h₅, },
end

end question9