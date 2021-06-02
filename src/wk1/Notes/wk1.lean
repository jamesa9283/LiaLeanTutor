import data.real.basic

noncomputable theory -- hey, this isn't going to be actually numerically sound, 
                     -- don't calculate anything

notation `|`x`|` := abs x

def is_limit (f : ℝ → ℝ) (c L : ℝ):= ∀ ε > 0, ∃ δ > (0 : ℝ), ∀ (x : ℝ), |x - c| < δ → |f x - L| < ε 



/-
 `def` - defining mathematical things <- named
 `lemma` - stating less important statements (lemmas) <- named
 `theorem` - stating more important statements (theorems) <- named
 `example` - testing things and showing how things work
-/

-- (S : set ℝ).nonempty 
variables (S : set ℝ)
#check S.nonempty

lemma test (S : set ℝ) (hS : S.nonempty) (a : ℝ) : a ∈ S := sorry

def id' (x : ℝ) := x

example : is_limit id' 0 0 :=
begin
  unfold is_limit id',
  intros ε ε_pos,
  use ε,
  split,
  { exact ε_pos},
  { intros x hx,
    exact hx}
end

def one_over (x : ℝ) := 1/x

-- false
example : is_limit one_over 0 0 :=
begin
  unfold is_limit one_over,
  intros ε ε_pos,
  use (1/ε),
  split,
  { simp only [one_div, gt_iff_lt, inv_pos], linarith,},
  { intros x hx, simp at hx,
    simp,
    sorry
  }
end