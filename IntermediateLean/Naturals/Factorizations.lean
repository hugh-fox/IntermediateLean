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
theorem prod_padic_eq_sum_padic {s : Finset ℕ} {n p : ℕ}
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

lemma padicValNat_one (n p i : ℕ) (n_lt_p_sq : n < p^2) (p_dvd_i : p ∣ i)
  (i_le_n : i ≤ n)
    (pos_i : 0 < i) (prime_p : p.Prime) : padicValNat p i = 1 := by
  have ⟨j, jeq⟩ := p_dvd_i

  subst jeq
  have pj_lt_p_sq : p * j < p^2 := by
    exact Nat.lt_of_le_of_lt i_le_n n_lt_p_sq

  have j_lt_p : j < p := by
    rw [sq] at pj_lt_p_sq
    have hjnot0 : j ≠ 0 := by
      intro eq
      subst j
      simp at pos_i

    exact (Nat.mul_lt_mul_left
      (by exact Nat.pos_of_dvd_of_pos p_dvd_i pos_i)).mp pj_lt_p_sq

  have pos_j : 0 < j := by
    exact Nat.pos_of_mul_pos_left pos_i

  have not_p_dvd_j : ¬ p ∣ j := by
    intro h_div
    have : j ≥ p := Nat.le_of_dvd pos_j h_div
    linarith

  have padic_self : padicValNat p p = 1 := by
    apply padicValNat.self
    exact Nat.Prime.one_lt prime_p

  have padic_sum : padicValNat p (p * j) =
      padicValNat p p + padicValNat p j := by
    have : Fact (Nat.Prime p) := by exact { out := prime_p }
    rw [padicValNat.mul] <;> linarith

  have padic_zero : padicValNat p j = 0 := by
    exact padicValNat.eq_zero_of_not_dvd not_p_dvd_j

  rw [padic_sum, padic_self, padic_zero]
#eval padicValNat 7 (∏ i ∈ Finset.Ico 1 (100+1), i.factorial)
#eval padicValNat 5 (∏ i ∈ Finset.Ico 1 (100+1), i.factorial)
#eval ∑ i ∈ Finset.range 12, (100 - 7 * i)

theorem padicValNat_superfactorial_eq_sum {p n : ℕ}
  (prime_p : Nat.Prime p) (kp_lt : p < n) (n_gt : 4 < n) :
  padicValNat p (∏ i ∈ Finset.Ico 1 (n+1), i.factorial) =
    ∑ i ∈ Finset.range p, (n + 1 - p * i) := by

  have factorial_eq_prod {j} : j.factorial = ∏ x ∈ Finset.Ico 1 (j+1), x := by
    symm
    exact Finset.prod_Ico_id_eq_factorial j

  have factorial_eq_pow : ∏ i ∈ Finset.Icc 1 n, i.factorial
    = ∏ i ∈ Finset.Icc 1 n, i^(n + 1 - i) := by
    conv_lhs => rhs; intro i; rw [factorial_eq_prod]

    have : ∏ i ∈ Finset.Icc 1 n, ∏ x ∈ Finset.Ico 1 (i+1), x
      = (∏ m ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Ico m (n+1), m)
      := by
      rw [Finset.prod_comm']
      simp
      intro x y
      omega

    rw [this]
    simp

  rw [show ∏ i ∈ Finset.Ico 1 (n + 1), i.factorial =
      ∏ i ∈ Finset.Icc 1 n, i.factorial by rfl
  ]

  simp [factorial_eq_pow]
  rw [prod_padic_eq_sum_padic prime_p.prime
    (s := Finset.Icc 1 n)
    (by simp; intro x _ _; subst x; contradiction)
    (by
      intro x x_in
      simp at x_in
      linarith
    )]

  replace : ∑ i ∈ Finset.Icc 1 n, padicValNat p (i ^ (n + 1 - i))
    = ∑ i ∈ Finset.Icc 1 n, (n + 1 - i) * padicValNat p i := by
    congr! 1 with i i_in
    rw [padicValNat.pow (hp := Fact.mk prime_p)]
    · intro i_eq
      subst i
      simp at i_in
  rw [this]
  replace : ∑ i ∈ Finset.Icc 1 n, (n + 1 - i) * padicValNat p i =
    (∑ i ∈ Finset.Icc 1 n with p ∣ i, (n + 1 - i) * padicValNat p i) +
    (∑ i ∈ Finset.Icc 1 n with ¬ p ∣ i, (n + 1 - i) * padicValNat p i) := by
    symm
    exact Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (Dvd.dvd p)
      fun x ↦ (n + 1 - x) * padicValNat p x
  rw [this]
  replace : ∑ i ∈ Finset.Icc 1 n with ¬p ∣ i,
      (n + 1 - i) * padicValNat p i = 0 := by
    simp
    intro i i_ge i_le not_dvd
    simp [not_dvd]
  simp [this]
  clear this
  have pos_p : 0 < p := by exact Nat.Prime.pos prime_p

  have filter_dvd_eq_mul : (Finset.Icc 1 n).filter (λ i => p ∣ i)
    = (Finset.Icc 1 k).image (· * p) := by
    ext i
    simp
    constructor
    · rintro ⟨ ⟨i_ge_1, i_le_n⟩, p_dvd_i ⟩
      use i / p
      field_simp [and_comm, mul_comm]
      split_ands
      · exact Nat.mul_div_cancel' p_dvd_i
      · suffices i ≤ k * p by
          replace : i / p ≤ k * p / p := by gcongr
          convert this
          field_simp [prime_p.pos]
        by_contra! h
        obtain ⟨ j, j_eq ⟩ := p_dvd_i
        subst i
        rw [mul_comm] at h

        replace h : n / p < j := by
          simp at k_max
          specialize k_max j (by exact (Nat.mul_lt_mul_left pos_p).mp h)
          exact (Nat.div_lt_iff_lt_mul pos_p).mpr k_max
          -- have : n / p ≤ j * p / p := by gcongr
          -- convert this
          -- simp [pos_p]

        have : p * j / p ≤ n / p := by
          exact Nat.div_le_div_right i_le_n
        field_simp [prime_p.pos] at this
        linarith
        -- suffices n / p ≠ j by omega
        -- intro eq
        -- subst eq
        -- simp_all
        -- omega

      · suffices 0 < i / p from this
        exact (Nat.lt_div_iff_mul_lt' p_dvd_i 0).mpr i_ge_1

    · rintro ⟨j, ⟨j_ge_1, j_le_k⟩, j_eq ⟩
      subst j_eq
      simp_all
      cases k_eq
      all_goals
        subst k
        specialize k_max 4
        interval_cases j <;> omega

  -- suffices ((Finset.Icc 1 n).filter ( p ∣ ·)).image λ i => (n + 1 - i) * padicValNat p i)
  --   = (Finset.Icc 1 k).image λ i => n - i * p + 1 by
  --   simp [this]

  -- have padic0 {x} (x_ne_0 : x ≠ 0) : padicValNat p x = 0 ↔ ¬p^1 ∣ x := by
  --   constructor
  --   · intro eq dvd
  --     rw [padicValNat_dvd_iff (hp := Fact.mk prime_p)] at dvd
  --     omega
  --   · intro dvd
  --     rw [padicValNat_dvd_iff (hp := Fact.mk prime_p)] at dvd
  --     omega

  have : ∑ i ∈ Finset.Icc 1 n with p ∣ i, (n + 1 - i) * padicValNat p i  =
      ∑ i ∈ Finset.Icc 1 n with p ∣ i, (n + 1 - i) := by
    congr! 1 with i i_in
    simp at i_in
    have : 0 < padicValNat p i := by
      have := i_in.right
      have := Fact.mk prime_p
      rw [dvd_iff_padicValNat_ne_zero (by linarith)] at i_in
      suffices padicValNat p i ≠ 0 by
        exact Nat.zero_lt_of_ne_zero this

      simp [i_in]

    have : n < p^2 := by
      simp_all
      specialize k_max 4 (by omega)
      have p_gt_4 : 4 < p := by omega
      have : 16 < p^2 := by exact Nat.sqrt_lt'.mp p_gt_4
      rw [show 16 = 4*4 by rfl] at n_gt this
      have : 4 * p < p ^ 2 := by
        rw [sq]
        gcongr

      exact Nat.lt_of_le_of_lt k_max.le this

    suffices padicValNat p i = 1 by simp_all
    obtain ⟨ ⟨i_ge, i_le⟩, p_dvd_i ⟩ := i_in
    exact vp1 n p i this p_dvd_i i_le i_ge prime_p


  simp_all
  rw [Finset.sum_image]

  intro x x_in y y_in eq
  have : p ≠ 0 := prime_p.ne_zero
  exact (Nat.mul_left_inj this).mp eq
