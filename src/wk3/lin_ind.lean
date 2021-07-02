import tactic linear_algebra.linear_independent

variables {ι : Type*} {R : Type*} {V' : Type*} {M : Type*}

section one

variables (a b : ℕ)
#check ({a} : set ℕ)
#check ({a, b} : set ℕ)


variables {v : ι → M} [semiring R] [add_comm_monoid M] [module R M] {a b : R}

#check false.elim
lemma linear_independent_empty_type' (h : ¬ nonempty ι) : linear_independent R v :=
begin
  rw linear_independent_iff,
  intros f hf,
  ext i,
  apply false.elim (h ⟨i⟩),
end

/-
variables (A : ({a} : set ℕ))
#check ⋃ (i : A), i
-/

lemma linear_independent_Union_of_directed' {η : Type*}
  {s : η → set M} (hs : directed (⊆) s)
  (h : ∀ i, linear_independent R (λ x, x : s i → M)) :
  linear_independent R (λ x, x : (⋃ i, s i) → M) :=
begin
  by_cases hη : nonempty η,
  { resetI,
    refine linear_independent_of_finite (⋃ i, s i) (λ t ht ft, _),
    rcases set.finite_subset_Union ft ht with ⟨I, fi, hI⟩,
    rcases hs.finset_le fi.to_finset with ⟨i, hi⟩,
    exact (h i).mono (set.subset.trans hI $ set.bUnion_subset $
      λ j hj, hi j (fi.mem_to_finset.2 hj)) },
  { refine (linear_independent_empty _ _).mono _,
    rintro _ ⟨_, ⟨i, _⟩, _⟩, exact hη ⟨i⟩ 
  }
end

end one

section two

open set module submodule

variables [ring R] [add_comm_group M] [module R M]

#check
#check

lemma exists_maximal_independent'' (s : ι → M) : ∃ I : set ι, linear_independent R (λ x : I, s x) ∧
  ∀ i ∉ I, ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I) :=
begin
  classical,
  sorry
end

end two
