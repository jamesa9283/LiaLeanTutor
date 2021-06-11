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

example : 1 + 1 = 2 := by linarith -- by norm_num

end multiplicity

open nat

#check sq_mul_squarefree_of_pos

lemma sq_mul_squarefree_of_pos' {n : ℕ} (h : 0 < n) :
  ∃ a b : ℕ, (b + 1) ^ 2 * (a + 1) = n ∧ squarefree (a + 1) :=
begin
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, ha₂⟩ := sq_mul_squarefree_of_pos h,
  refine ⟨a₁.pred, b₁.pred, _, _⟩;
  simpa only [add_one, succ_pred_eq_of_pos, ha₁, hb₁], 
end

end squarefree

section finite_groups
/-!
# Finite Groups
-/

variables {G : Type*} [group G]


-- This one is a beast

open subgroup

#check submonoid.fg_iff 
#check le_antisymm

/-- A subgroup is finitely generated if and only if it is finitely generated as a submonoid. -/
lemma fg_iff_submonoid_fg' (P : subgroup G) : P.fg ↔ P.to_submonoid.fg :=
begin
  split,
  { rintro ⟨S, rfl⟩,
    rw submonoid.fg_iff,
    refine ⟨S ∪ S⁻¹, (subgroup.closure_to_submonoid _).symm, S.finite_to_set.union S.finite_to_set.inv⟩,
  },
  { rintro ⟨S, hS⟩,
    refine ⟨S, le_antisymm _ _⟩,
    { rw [closure_le, ← coe_to_submonoid, ← hS],
      exact submonoid.subset_closure,
    },
    { rw [← subgroup.to_submonoid_le, ← hS, submonoid.closure_le],
      exact subgroup.subset_closure,
    }
  },
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