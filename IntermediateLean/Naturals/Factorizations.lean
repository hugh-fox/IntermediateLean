import Mathlib


theorem factorization_lcm_max {p : ℕ} {a b : ℕ}
  (ha : a ≠ 0) (hb : b ≠ 0) {prime_p : Prime p} :
  padicValNat p (a.lcm b) = padicValNat p a ⊔ padicValNat p b
    := by
  have := Nat.factorization_lcm ha hb
  apply congrArg (· p) at this
  simpa [<- Nat.factorization_def _ prime_p.nat_prime]


-- Proven by reducing to difference of squares
lemma factorization_4_2_4 (n p : ℕ) : n^4 + p^4 + (n * p)^2 =
  (n^2 + p^2 + n * p) * (n^2 + p^2 - n * p)
    := by
  calc n^4 + p^4 + (n * p)^2
  _ = (n^2 + p^2)^2 - (n * p)^2 := by
    ring_nf
    omega
  _ = (n^2 + p^2 + n * p) * (n^2 + p^2 - n * p) := by
    rw [Nat.sq_sub_sq]


theorem prod_padic_eq_sum {s : Finset ℕ} (n : ℕ) {p}
  (prime_p : Prime p) {f : ℕ → ℕ} (non_zero_f : ∀ x ≠ 0, f x ≠ 0)
  (no_zeros : ∀ x ∈ s, x ≠ 0) (le_range : ∀ x ∈ s, x ≤ n)
  : padicValNat p (s.prod f)
  = s.sum λ i => padicValNat p (f i)
  := by
  rw [<- Nat.prime_iff] at prime_p
  induction' s using Finset.induction_on with m s m_not_in ih
  case empty =>
    simp
  case insert =>
    simp_all
    obtain ⟨ m_ne_0, no_zeros ⟩ := no_zeros
    rw [padicValNat.mul (hp := Fact.mk prime_p)
      (by
        suffices 0 < (n + 1 - m) by
          simp_all

        omega
      )
      (by
        apply Finset.prod_ne_zero_iff.mpr
        intro a a_in
        have a_ne_0 : a ≠ 0 := by
          intro a_eq
          subst a
          exact no_zeros a_in
        suffices 0 < (n + 1 - a) by
          simp_all
        have := le_range.right a a_in
        omega
      )
    ]
    exact congrArg (HAdd.hAdd (padicValNat p (f m))) ih


theorem prod_padic_eq_sum_id {s : Finset ℕ} {p} (prime_p : Prime p)
  (no_zeroes : ∀ x ∈ s, x ≠ 0)
  : padicValNat p (s.prod id) = s.sum (padicValNat p) := by
  apply prod_padic_eq_sum p prime_p no_zeroes



lemma Nat.exists_eq_pow_two_of_prime_pow_two_dvd {n : ℕ} (h : n > 0)
  (h_even : ∀ p : ℕ, Prime p → Even (padicValNat p n)) :
  ∃ k : ℕ, n = k^2 := by
  have := Nat.prod_pow_prime_padicValNat n (by linarith : n ≠ 0) (n + 1) (by simp)
  have : (∏ p ∈ Finset.range (n + 1) with Prime p, p ^ (padicValNat p n / 2))^2 = n := by
    rw [sq]
    rw [<- Finset.prod_mul_distrib]
    simp [<- sq]

    convert this using 2 with p p_in
    simp at p_in
    specialize h_even p p_in.right
    obtain ⟨ j, j_eq ⟩ := h_even
    simp [j_eq, <- two_mul]
    ring

  rw [<- this]
  simp
