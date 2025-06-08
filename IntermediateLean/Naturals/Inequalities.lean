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

-- Using mathlib: exact Nat.le_mul_self k
example {k : ℕ} : k ≤ k * k := by
  by_cases k = 0
  · subst k; rfl
  · conv_lhs => rw [<- mul_one k]
    gcongr
    suffices 0 < k from this
    positivity


theorem sum_sq_sub_mul_ne_one_of_ne {a b : ℕ}
  (pos_a : 0 < a) (pos_b : 0 < b) (ne : a ≠ b) :
    a^2 + b^2 - a*b ≠ 1 := by
  -- Apply a ≠ b to show the product is greater than one
  have : 1 < a * b := by
    by_cases a = 1
    · have : 1 < b := by omega
      exact Right.one_lt_mul_of_le_of_lt pos_a this
    · have : 1 < a := by omega
      exact Left.one_lt_mul_of_lt_of_le this pos_b

  -- Obtain the am-gm inequality for two naturals
  have am_gm := two_mul_le_add_sq a b
  rw [mul_assoc 2] at am_gm

  omega


-- The sum_sq_sub_mul_ne_one_of_ne theorem proved without the am-gm inequality
example {a b : ℕ} (pos_a : 0 < a) (pos_b : 0 < b) (ne : a ≠ b) :
    a^2 + b^2 - a*b ≠ 1 := by
  intro eq
  suffices a^2 + b^2 > 1 + a*b by
    omega

  wlog a_lt_b : a < b
  · rw [add_comm, mul_comm]
    apply @this b a pos_b pos_a ne.symm
    · convert eq using 1
      ring_nf
    · omega

  obtain ⟨ m, m_eq ⟩ : ∃ m, b = m + a := by
    use b - a
    omega

  subst b
  suffices 1 < a^2 +a*m + m^2 by
    linarith

  have : 0 < a^2 := by
    exact Nat.pow_pos pos_a

  have : 0 < m := by
    exact Nat.lt_add_left_iff_pos.mp a_lt_b

  have : 0 < m^2 := by
    exact Nat.pow_pos this

  omega
