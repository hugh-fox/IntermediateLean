import Mathlib


-- AM-GM for two variables
theorem am_hm_2_inequality_n {a b : ℕ} : (a + b)^2 / 2 ≤ a^2 + b^2 := by
  rw [add_sq]
  suffices 2*a*b ≤ a^2 + b^2 by
    omega

  exact two_mul_le_add_sq a b

theorem le_mul_2_iff {a b : ℕ} : a ≤ b ↔ 2*a ≤ 2*b := by
  constructor
  · exact Nat.mul_le_mul_left 2
  · simp [mul_le_mul_left]

theorem le_mul_2 {a b : ℕ} : a ≤ b ↔ 2*a ≤ 2*b := by
  constructor
  · exact fun a_1 ↦ Nat.mul_le_mul_left 2 a_1
  · simp [mul_le_mul_left]
