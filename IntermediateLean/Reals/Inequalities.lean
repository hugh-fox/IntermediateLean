import Mathlib


-- AM-GM for two variables
theorem am_hm_2_inequality (a b : ℝ) : (a + b)^2 / 2 ≤ a^2 + b^2 := by
  have h : 0 ≤ (a - b)^2 := pow_two_nonneg (a - b)
  linarith
