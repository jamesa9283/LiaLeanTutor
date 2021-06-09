import ring_theory.unique_factorization_domain ring_theory.int.basic number_theory.divisors algebra.squarefree

section squarefree

variables {R : Type*}

/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
def squarefree' [monoid R] (r : R) : Prop := ∀ x : R, x * x ∣ r → is_unit x

namespace multiplicity

variables [comm_monoid R] [decidable_rel (has_dvd.dvd : R → R → Prop)]

lemma squarefree_iff_multiplicity_le_one' (r : R) :
  squarefree r ↔ ∀ x : R, multiplicity x r ≤ 1 ∨ is_unit x :=
begin
  refine forall_congr (λ a, _),
  rw ← sq,
  rw pow_dvd_iff_le_multiplicity,
  rw or_iff_not_imp_left,
  rw not_le,
  rw imp_congr,
  { convert enat.add_one_le_iff_lt (enat.coe_ne_top _),
    norm_cast},
  { refl},
end

end multiplicity

open nat

lemma sq_mul_squarefree_of_pos' {n : ℕ} (h : 0 < n) :
  ∃ a b : ℕ, (b + 1) ^ 2 * (a + 1) = n ∧ squarefree (a + 1) :=
begin
  sorry
end

end squarefree

section finite_groups
/-!
# Finite Groups
-/

variables {G H : Type*} [group G] [add_group H]


-- This one is a beast

/-- A subgroup is finitely generated if and only if it is finitely generated as a submonoid. -/
lemma fg_iff_submonoid_fg' (P : subgroup G) : P.fg ↔ P.to_submonoid.fg :=
begin
  sorry
end

/-!
# NB!
What we just proved is extremely useful, we can use several variants of it, for
example;
-/

#check subgroup.fg_iff_submonoid_fg -- **
#check add_subgroup.fg_iff_add_submonoid.fg -- **

-- ** these two are the same as Lean knows that `add_groups` are `groups`


end finite_groups