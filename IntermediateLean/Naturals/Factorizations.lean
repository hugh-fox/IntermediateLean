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
    (n^2 + p^2 + n * p) * (n^2 + p^2 - n * p) := by
  calc n^4 + p^4 + (n * p)^2
  _ = (n^2 + p^2)^2 - (n * p)^2 := by
    ring_nf
    omega
  _ = (n^2 + p^2 + n * p) * (n^2 + p^2 - n * p) := by
    rw [Nat.sq_sub_sq]


-- The p-adic valuation of the product of `s` is the sum of all p-adic
-- valuations of each element in `s`.
theorem prod_padic_eq_sum_padic {s : Finset ℕ} (n : ℕ) {p}
  (prime_p : Prime p) {f : ℕ → ℕ} (non_zero_f : ∀ x ≠ 0, f x ≠ 0)
  (no_zeros : ∀ x ∈ s, x ≠ 0) (le_range : ∀ x ∈ s, x ≤ n) :
    padicValNat p (s.prod f) = s.sum λ i => padicValNat p (f i) := by
  rw [<- Nat.prime_iff] at prime_p
  induction' s using Finset.induction_on with m s m_not_in ih
  case empty =>
    simp
  case insert =>
    simp_all
    obtain ⟨ m_ne_0, no_zeros ⟩ := no_zeros
    rw [padicValNat.mul (hp := Fact.mk prime_p)]
    · exact congrArg (HAdd.hAdd (padicValNat p (f m))) ih
    · suffices 0 < (n + 1 - m) by simp_all
      omega
    · apply Finset.prod_ne_zero_iff.mpr
      intro a a_in
      have a_ne_0 : a ≠ 0 := by
        intro a_eq
        subst a
        exact no_zeros a_in
      suffices 0 < (n + 1 - a) by
        simp_all

      have := le_range.right a a_in
      omega


theorem prod_padic_eq_sum_padic_id {s : Finset ℕ} {n p} (prime_p : Prime p)
  (no_zeroes : ∀ x ∈ s, x ≠ 0) (le_range : ∀ x ∈ s, x ≤ n)
  : padicValNat p (s.prod id) = s.sum (padicValNat p) := by
  exact prod_padic_eq_sum_padic n prime_p (by simp) no_zeroes le_range


theorem exists_sq_of_all_even_padic {n : ℕ} (pos_n : 0 < n)
  (h_even : ∀ p : ℕ, Prime p → Even (padicValNat p n)) :
  ∃ k : ℕ, n = k^2 := by
  have := Nat.prod_pow_prime_padicValNat n
    (by linarith : n ≠ 0) (n + 1) (by simp)

  have : (∏ p ∈ Finset.range (n + 1) with Nat.Prime p,
      p ^ (padicValNat p n / 2))^2 = n := by
    rw [sq]
    rw [<- Finset.prod_mul_distrib]
    simp [<- sq]

    convert this using 2 with p p_in
    simp at p_in
    specialize h_even p p_in.right.prime
    obtain ⟨ j, j_eq ⟩ := h_even
    simp [j_eq, <- two_mul]
    ring

  rw [<- this]
  simp


theorem even_padic_of_exists_sq (n : ℕ) (pos_n : 0 < n) :
  (∃ k : ℕ, n = k^2) → ∀ p, Prime p → Even (padicValNat p n) := by
  rintro ⟨ k, n_eq_k_sq ⟩ p prime_p
  rw [n_eq_k_sq]
  rw [padicValNat.pow (hp := Fact.mk prime_p.nat_prime)]
  · simp
  · intro eq
    subst eq
    simp [n_eq_k_sq] at pos_n


theorem exists_sq_iff_all_even_padic {n : ℕ} (pos_n : 0 < n) :
  (∀ p, Prime p → Even (padicValNat p n)) ↔ (∃ k : ℕ, n = k^2) := by
  constructor
  · exact exists_sq_of_all_even_padic pos_n
  · exact even_padic_of_exists_sq n pos_n


theorem coprime_of_sq_eq_sq_add_two_sq {p a b : ℕ} (prime_p : p.Prime)
  (eq : p^2 = a^2 + 2*b^2)
  (pos_b : b ≠ 0)
  : Nat.gcd a b = 1 := by
  rw [<- Nat.coprime_iff_gcd_eq_one]
  by_contra! not_coprime
  obtain ⟨ k, prime_k, k_dvd_a, k_dvd_b ⟩ := by
    rwa [Nat.Prime.not_coprime_iff_dvd] at not_coprime

  obtain ⟨ u, u_eq ⟩ := k_dvd_a
  obtain ⟨ j, j_eq ⟩ := k_dvd_b

  subst a b
  replace eq : p^2 = k ^ 2 * (u ^ 2 + j ^ 2 * 2) := by
    linear_combination eq

  have : k ∣ p := by
    have : k ∣ k ^ 2 * (u ^ 2 + j ^ 2 * 2) := by
      rw [sq k, mul_assoc]
      exact Nat.dvd_mul_right k (k * (u ^ 2 + j ^ 2 * 2))

    have : k ∣ p^2 := by rwa [<- eq] at this
    exact Nat.Prime.dvd_of_dvd_pow prime_k this

  have : k = p := by
    exact (Nat.prime_dvd_prime_iff_eq prime_k prime_p).mp this

  subst k
  simp_all
  have : 0 < j := by omega
  suffices  j ^ 2 > 0 by omega
  exact Nat.pow_pos this
