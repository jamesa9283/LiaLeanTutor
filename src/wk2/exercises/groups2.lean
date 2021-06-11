import tactic
import algebra.squarefree

namespace nat

-- this lemma may be useful to you `sq_mul_squarefree_of_pos`
-- in obtain you can use `-` to remove hypothesys
lemma sq_mul_squarefree' (n : ℕ) : ∃ a b : ℕ, b ^ 2 * a = n ∧ squarefree a :=
begin
  sorry
end

end nat

namespace finite_groups 

variables {G : Type*} [group G]

/- Use the lemma we proved in class to prove this one. This is more of a mathlib 
   search exercise than a maths one, decide how you are going to prove it and go 
   find the lemmas you need.
-/
lemma subgroup.fg_iff_add_fg (P : subgroup G) : P.fg ↔ P.to_add_subgroup.fg :=
begin
  sorry
end

end finite_groups