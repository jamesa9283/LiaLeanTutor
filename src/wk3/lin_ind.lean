import tactic linear_algebra.linear_independent

variables {ι : Type*} {R : Type*} {V' : Type*} {M : Type*}

section one

variables {v : ι → M} [semiring R] [add_comm_monoid M] [module R M] {a b : R}

lemma linear_independent_empty_type' (h : ¬ nonempty ι) : linear_independent R v :=
begin
  sorry
end

lemma linear_independent_Union_of_directed' {η : Type*}
  {s : η → set M} (hs : directed (⊆) s)
  (h : ∀ i, linear_independent R (λ x, x : s i → M)) :
  linear_independent R (λ x, x : (⋃ i, s i) → M) :=
begin
  sorry
end

end one

section two

open set module submodule

variables [ring R] [add_comm_group M] [module R M]

lemma exists_maximal_independent'' (s : ι → M) : ∃ I : set ι, linear_independent R (λ x : I, s x) ∧
  ∀ i ∉ I, ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I) :=
begin
  sorry
end

end two
