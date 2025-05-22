import Mathlib


theorem square_inequality (a b : ℤ) (h₁ : a^2 < b^2) : |a| < |b| := by
  gcongr √h₁
    sorry
--   omega

theorem lt_of_pow_lt_pow2 (u : ℤ) (v : ℕ) :
    u ^ 2 < v ^ 2 → u < v := by
  exact lt_of_pow_lt_pow_left₀ 2 (by linarith)

theorem sq_upper_bounds {u v : ℤ } {n : ℕ} : u^2 + v^2 = n^2 - 1 → |u| < n ∧ |v| < n := by
  intro uv_eq
  have := sq_nonneg u
  have := sq_nonneg v
  have : |u| ^ 2 < n ^ 2 ∧ |v| ^ 2 < n ^ 2 := by
    simp [sq_abs]
    omega

  constructor <;>
    exact lt_of_pow_lt_pow_left₀ 2 (by linarith) (by linarith)


-- How to generalize a natural lemma to ints by finding integer expressions
-- that can be lifted to naturals. The proof splits on the positivity of x,
-- then we lift the integer expressions x and (-x) to naturals.
theorem Int.not_exists_sq_5 : ¬∃ k : ℤ, k ^ 2 = 5 := by
  -- This isn't necessary as we could just use Nat.not_exists_sq', but it is a
  -- good example of using conv inside an exists statement (which becomes a
  -- lambda after the second rhs)
  conv_rhs => rhs; intro k; rw [sq]
  -- Apply the lemma for naturals
  have ne_sq := Nat.not_exists_sq
    (show 2 * 2 < 5 by linarith)
    (show 3 * 3 > 5 by linarith)
  push_neg at *
  exact λ x => by
    by_cases h : 0 < x
    · lift x to ℕ using h.le
      exact_mod_cast ne_sq x
    · push_neg at h
      -- Show that x^2 = (-x)^2
      suffices ¬(-x * -x) = 5 by
        simpa [<- sq_abs (-x), sq] using this
      -- Lift (-x) to ℕ, first by generalizing to n, then showing positivity
      -- of -x
      lift (-x) to ℕ with n
      · simpa [Int.neg_le_zero_iff]
      exact_mod_cast ne_sq n

#check Nat.not_exists_sq'
theorem Int.not_exists_sq {k : ℤ} {n : ℕ} (hl : k * k < n)
  (hr : n < (k + 1) * (k + 1)) :
    ¬∃ (k : ℤ) (n : ℕ), k*k = n := by
  -- First lift k and k+1 to nat
  have k_nonneg : 0 ≤ k*k := mul_self_nonneg k
  have kn_nonneg : 0 ≤ (-k)*(-k) := mul_self_nonneg (-k)
  have k1_nonneg : 0 ≤ (k+1)*(k+1) := mul_self_nonneg (k+1)
  push_neg
  intro k' n' k_sq_n
  replace k_sq_n : k'.natAbs ^ 2 = n' := by
    rw [<- sq, <- sq_abs] at k_sq_n
    rw [abs_eq_natAbs k'] at k_sq_n
    exact_mod_cast k_sq_n

  sorry
  -- Apply the lemma for naturals
  have ne_sq := Nat.not_exists_sq
    (show k * k < n by

      linarith
    )
    (show (k + 1) * (k + 1) > n by

      linarith
    )
  sorry
