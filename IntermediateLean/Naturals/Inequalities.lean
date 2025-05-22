import Mathlib

-- ### Algebra

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



-- ### Lists

-- theorem list_sum_partition : ∀ l : List ℕ

theorem exists_nat_of_pos {k : ℤ} (pos_k : 0 ≤ k) :
  ∃ n : ℕ, n = k := by
    exact CanLift.prf k pos_k

example {k : ℤ} (nonneg_k : 0 ≤ k) :
    ∃ n : ℕ, n = k := by
  lift k to ℕ using nonneg_k
  use k

example {r : ℝ} (nonneg_r : 0 ≤ r) :
    ∃ n : NNReal, n = r := by
  use ⟨r, nonneg_r⟩
  rfl

theorem exists_nat_of_sq {k : ℤ} :
  ∃ n : ℕ, n = k * k := by
    sorry


theorem eq_sq_iff_sqrt_abs {n : ℕ} {k : ℤ} :
    n = k * k ↔ √n = k.natAbs := by
  constructor
  ·
    intro eq
    have sqrt_eq := by
      rify at eq
      apply congrArg (√·) at eq
      exact eq

    convert sqrt_eq
    have := (Real.sqrt_mul_self_eq_abs k).symm
    convert this
    norm_cast
    exact Nat.cast_natAbs k

  ·
    intro eq
    apply congrArg (· ^ 2) at eq
    rw [sq_eq_sq_iff_abs_eq_abs] at eq
    convert eq
