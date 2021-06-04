import algebra.group.defs
import logic.function.basic
import algebra.group.basic

section group

variables {M : Type} [mul_one_class M]

lemma eq_one_iff_eq_one_of_mul_eq_one' {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 :=
  by split; { rintro rfl, simpa using h}

lemma one_mul_eq_id' : ((*) (1 : M)) = id := funext one_mul
/-
begin
  funext x,
  simp only [one_mul, id.def],
end
-/

variables {G : Type} [group G] {a b c : G}

lemma inv_mul_cancel_right' (a b : G) : a * b⁻¹ * b = a := -- by simp [mul_assoc]
begin
  simp [mul_assoc],
end

theorem mul_right_surjective' (a : G) : function.surjective (λ x, x * a) := 
  λ x, ⟨x * a⁻¹, inv_mul_cancel_right x a⟩


/-
begin
  intros x,
  use (x * a⁻¹),
  apply inv_mul_cancel_right,
end
-/

theorem inv_eq_one' : a⁻¹ = 1 ↔ a = 1 :=
begin
  rw [← @inv_inj _ _ a 1, one_inv],
end
-- by rw [← @inv_inj _ _ a 1, one_inv]


end group

section add_group

variables {G : Type} [add_group G] {a b c d : G}

lemma eq_of_sub_eq_zero' (h : a - b = 0) : a = b :=
calc a = a - b + b : (sub_add_cancel a b).symm
   ... = b         : by rw [h, zero_add]

#check (sub_add_cancel a b).symm

example : a = a - b + b :=
begin
  apply (sub_add_cancel a b).symm
end

lemma eq_of_sub_eq_zero'' (h : a - b = 0) : a = b :=
calc a = a - b + b : (sub_add_cancel a b).symm
  ...  = b         : by rw [h, zero_add]

end add_group