import logic.basic -- Needed for imp_false

section question11

variables P Q R : Prop

example (h : P ∧ (Q ∧ R)) : (P ∧ Q) ∧ R :=
begin
  sorry
end

end question11

section question6

variables P Q R : Prop

example : (P ∧ R) ∨ (Q ∧ R) → (P ∨ Q) ∧ R :=
begin
  sorry
end

end question6

section question9

variables A B C : Prop

example (h : C → A ∨ B) : (C ∧ ¬A) → B :=
begin
  sorry
end

-- HINT: for this question, you may find it useful to to use `exfalso, contradiction` somewhere in the proof

end question9