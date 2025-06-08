import Mathlib

#check List.get

-- TODO
-- theorem list_partition : ∀ L : List ℝ ∃ L1 : List ℝ ∃ L2 : List ℝ : L1 :: L2 = L ∧ ∀ x ∈ L1 x < median L ∀ y ∈ L2 y >= median L

-- Quadratic with 2 real solutions
example {x : ℝ} : x^2 - x - 2 = 0 → x = 2 ∨ x = -1 := by
  intro eq
  replace eq : 1 * (x * x) + -1 * x + -2 = 0 := by
    linarith
  have discrim_eq : discrim 1 (-1) (-2) = (2 * 1 * x + (-1)) ^ 2 :=
    discrim_eq_sq_of_quadratic_eq_zero eq

  -- rw [sq] at discrim_eq
  -- rw [quadratic_eq_zero_iff (by simp) discrim_eq x] at eq

  have : 3 = |(2 * 1 * x + (-1))| := by
    have : 3^2 = (2 * 1 * x + (-1))^2 := by
      unfold discrim at discrim_eq
      linarith
    have := (sq_eq_sq_iff_abs_eq_abs 3 (2 * 1 * x + -1)).mp this
    simpa using this


  -- For the sake of example
  rcases abs_cases (2*1*x + -1) with (⟨pos, gt⟩ | ⟨neg, lt⟩)
  · rw [pos] at this
    have : 2 = x := by
      linear_combination this / 2

    simp [this.symm]

  · rw [neg] at this
    norm_num at this
    have : -1 = x := by
      linear_combination -this / 2

    simp [this.symm]



  ring_nf at this

  -- rw? at eq

-- Quadratic with imaginary solutions
example : ¬∃ x, x^2 - x + 2 = 0 := by
  -- use quadratic_ne_zero_of_discrim_ne_sq
  sorry
