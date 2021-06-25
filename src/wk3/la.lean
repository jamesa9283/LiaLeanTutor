import algebra.module.basic linear_algebra.basis tactic

section one

variables (R : Type) (S : Type) [semiring R] [semiring S] (f : S →+* R)
variables (M : Type) [add_comm_monoid M] [module R M]

#check (•)
#check (•) ∘ f

/-

/-- Compose a `module` with a `ring_hom`, with action `f s • m` -/
def comp_hom [semiring S] (f : S →+* R) :
  module S M := 
  { smul := _,
  one_smul := _,
  mul_smul := _,
  smul_add := _,
  smul_zero := _,
  add_smul := _,
  zero_smul := _ }

-/

end one

section two

variables {ι : Type*} {ι' : Type*} {R : Type*} {K : Type*}
variables {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

open module

variables [semiring R]
variables [add_comm_monoid M] [module R M] [add_comm_monoid M'] [module R M']

variables (b b₁ : basis ι R M) (i : ι) (c : R) (x : M)

/-
  (by simp only [b.coord_apply, finsupp.ext_iff, finsupp.zero_apply])
  b.repr.map_eq_zero_iff
-/
#check basis.coord_apply
#check finsupp.ext_iff
#check finsupp.zero_apply

lemma forall_coord_eq_zero_iff {x : M} {i : ι} :
  (∀ i, b.coord i x = 0) ↔ x = 0 := 
iff.trans
  (by simp only [b.coord_apply, finsupp.ext_iff, finsupp.zero_apply])
  b.repr.map_eq_zero_iff



/-TODO

begin 
  split,
  { intros hi,
    specialize hi i,
    rw b.coord_apply at hi,
    rw ← finsupp.ext_iff at hi,
    sorry
  },
  { sorry},
end

-/



end two