import logic.basic -- Needed for imp_false

section question11

variables P Q R : Prop

example (h : P ∧ (Q ∧ R)) : (P ∧ Q) ∧ R :=
begin
  cases h with hp hqr,
  cases hqr with hq hr,
  split,
  { exact and.intro hp hq },
  { exact hr },
end


end question11