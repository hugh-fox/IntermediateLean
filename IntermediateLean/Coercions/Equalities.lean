import Mathlib

example {n : ℕ} {i : ℤ} {r : ℝ} :
    n = i → i = r → n = r := by
  intro n_eq_i i_eq_r
  subst i_eq_r
  exact_mod_cast n_eq_i

example {n : ℕ} {i : ℤ} {r : ℝ} :
    n = i → i = r → n = r := by
  intro n_eq_i i_eq_r
  convert i_eq_r
  exact_mod_cast n_eq_i

-- Library search can suggest some wild stuff:
example {n : ℕ} {i : ℤ} {r : ℝ} :
    n = i → i = r → n = r := by
  intro n_eq_i i_eq_r
  convert i_eq_r
  -- exact? closes with:
  symm
  exact Real.ext_cauchy (congrArg (Real.cauchy ∘ Int.cast) (n_eq_i.symm))


example {n : ℕ} {k i : ℤ} {r : ℝ} :
    n + k = i → i = r + k → n = r := by
  intro n_eq_i i_eq_r
  have : n + k = r + k := by
    rw_mod_cast [n_eq_i]
    exact i_eq_r

  -- Sometimes you can use ↑, but sometimes only cast works:
  apply congrArg (· - k.cast) at this
  convert this <;> symm
  · exact_mod_cast add_sub_cancel_right ↑n k
  · exact add_sub_cancel_right r ↑k
