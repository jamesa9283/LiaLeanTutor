import tactic linear_algebra.linear_independent

variables {ι : Type*} {R : Type*} {V' : Type*} {M : Type*}

section one

variables {v : ι → M} [semiring R] [add_comm_monoid M] [module R M] {a b : R}

lemma linear_independent_empty_type' (h : ¬ nonempty ι) : linear_independent R v :=
begin
 rw [linear_independent_iff],
 intros,
 ext i,
 exact false.elim (h ⟨i⟩)
end

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
    rintro _ ⟨_, ⟨i, _⟩, _⟩, exact hη ⟨i⟩ }
end

end one

section two

open set module submodule

variables [ring R] [add_comm_group M] [module R M]

lemma exists_maximal_independent'' (s : ι → M) : ∃ I : set ι, linear_independent R (λ x : I, s x) ∧
  ∀ i ∉ I, ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I) :=
begin
  classical,
  rcases exists_maximal_independent' R s with ⟨I, hIlinind, hImaximal⟩,
  use [I, hIlinind],
  intros i hi,
  specialize hImaximal (I ∪ {i}) (by simp),
  set J := I ∪ {i} with hJ,
  have memJ : ∀ {x}, x ∈ J ↔ x = i ∨ x ∈ I, by simp [hJ],
  have hiJ : i ∈ J := by simp,
  have h := mt hImaximal _, swap,
  { intro h2,
    rw h2 at hi,
    exact absurd hiJ hi },
  obtain ⟨f, supp_f, sum_f, f_ne⟩ := linear_dependent_comp_subtype.mp h,
  have hfi : f i ≠ 0,
  { contrapose hIlinind,
    refine linear_dependent_comp_subtype.mpr ⟨f, _, sum_f, f_ne⟩,
    simp only [finsupp.mem_supported, hJ] at ⊢ supp_f,
    rintro x hx,
    refine (memJ.mp (supp_f hx)).resolve_left _,
    rintro rfl,
    exact hIlinind (finsupp.mem_support_iff.mp hx) },
  use [f i, hfi],
  have hfi' : i ∈ f.support := finsupp.mem_support_iff.mpr hfi,
  rw [← finset.insert_erase hfi', finset.sum_insert (finset.not_mem_erase _ _),
      add_eq_zero_iff_eq_neg] at sum_f,
  rw sum_f,
  refine neg_mem _ (sum_mem _ (λ c hc, smul_mem _ _ (subset_span ⟨c, _, rfl⟩))),
  exact (memJ.mp (supp_f (finset.erase_subset _ _ hc))).resolve_left (finset.ne_of_mem_erase hc),
end

end two
