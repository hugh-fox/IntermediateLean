import Mathlib


theorem Nat.digits_sum_0 {n b : ℕ} : b ≠ 0 →
  (∀ x ∈ Nat.digits b n, x = 0) → n = 0 := by
  intro b_ne_0 digits_0
  have := List.sum_eq_zero digits_0
  let l := (b.digits n).length
  have repl : l = (b.digits n).length ∧ ∀ x ∈ b.digits n, x = 0 :=
    ⟨ by simp [l], digits_0 ⟩
  rw [<- List.eq_replicate_iff] at repl
  rw [repl] at this
  apply congrArg (Nat.ofDigits b) at repl
  convert repl
  · exact Eq.symm (ofDigits_digits b n)
  · induction' (b.digits n).length with m ih
    · simp
    · simp [List.replicate_add, b.ofDigits_append]
      exact ih


theorem base_mul_digits_sum_eq_digits_sum {n b} (b_gt : 1 < b) :
    (b.digits (n * b)).sum = (b.digits n).sum := by
  by_cases pos_n : n ≤ 0
  · push_neg at pos_n
    have : n = 0 := Nat.eq_zero_of_le_zero pos_n
    simp [this]

  push_neg at pos_n
  have digits_mul_base : b.digits (n * b) = 0 :: Nat.digits b n := by
    have := Nat.digits_base_pow_mul b_gt pos_n (k := 1)
    simp only [mul_comm, pow_one] at this
    exact this

  simp [digits_mul_base]


theorem ten_mul_digits_sum_eq_digits_sum {n} :
    (Nat.digits 10 (n * 10)).sum = (Nat.digits 10 n).sum := by
  exact base_mul_digits_sum_eq_digits_sum (by simp)


theorem sum_digits_pow_base_succ_eq_sum_pair_digits_pow_base {n b}
  (pos_b : 0 < b) :
  ∑ i ∈ Finset.range (b^(n+1)), (b.digits i).sum =
  ∑ p ∈ Finset.range (b^n) ×ˢ Finset.range b,
    (b.digits (b * p.fst + p.snd)).sum := by
  rw [Finset.sum_bij (fun x x_in => (x / b, x % b))]
  · intro x x_in
    simp_all [Nat.pow_add_one', Nat.mod_lt]
    exact Nat.div_lt_of_lt_mul x_in
  · simp
    intro i hi j j_lt f_eq mod_eq
    have i_eq := Nat.div_add_mod i b
    have j_eq := Nat.div_add_mod j b
    rw [<- i_eq, <- j_eq]
    simp_all
  · simp
    intro j k j_lt k_lt
    use b * j + k
    split_ands
    · rw [Nat.pow_add_one']
      suffices b * j + b ≤ b * b ^ n by omega
      suffices b * (j + 1) ≤ b * b ^ n by
        simp [mul_add] at this
        exact this

      exact (Nat.mul_le_mul_left_iff pos_b).mpr j_lt

    · rw [Nat.add_div pos_b]

      have : k % b < b := by
        exact Nat.mod_lt_of_lt k_lt

      replace : ¬k % b ≥ b := by
        exact Nat.not_le_of_lt this

      simp [Nat.add_div pos_b, this]
      simp [show k / b = 0 by exact Nat.div_eq_of_lt k_lt]
      exact Nat.mul_div_right j pos_b

    · simp only [Nat.mul_add_mod_self_left]
      exact Nat.mod_eq_of_lt k_lt
  · simp
    intro i i_in_s
    congr!
    exact Eq.symm (Nat.div_add_mod i b)


theorem sum_digits_pow_ten_succ_eq_sum_pair_digits_pow_ten {n} :
  ∑ i ∈ Finset.range (10^(n+1)), (Nat.digits 10 i).sum =
  ∑ p ∈ Finset.range (10^n) ×ˢ Finset.range 10,
    (Nat.digits 10 (10 * p.fst + p.snd)).sum := by
  exact sum_digits_pow_base_succ_eq_sum_pair_digits_pow_base (by simp)


-- Closed form formula for summing digits from up to powers of 10.
theorem digit_sum_ico_base_pow_eq {k : ℕ} (hk : 0 < k) :
    (∑ n ∈ Finset.Ico 1 (10^k), (Nat.digits 10 n).sum) = 45 * k * 10^(k-1) := by
  induction' k, (by linarith : 1 ≤ k) using Nat.le_induction with m ge ih
  · simp [show Finset.Ico 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9} by rfl]
  · specialize ih ge
    have pos_m : 0 < m := by positivity

    have digits_eq_cons := Nat.digits_eq_cons_digits_div
      (by simp : 1 < 10) (Nat.ne_zero_of_lt ge)

    have pos_n : ∀ n ∈ Finset.Ico 1 (10^m), 0 < n := by
      intro n n_in
      simp at n_in
      exact n_in.left

    have {n} : ∑ n ∈ Finset.Ico 1 (10 ^ n), (Nat.digits 10 n).sum =
        ∑ n ∈ Finset.range (10 ^ n), (Nat.digits 10 n).sum := by
      simp [Finset.sum_range_eq_add_Ico]

    rw [this] at ih ⊢
    clear this
    rw [sum_digits_pow_ten_succ_eq_sum_pair_digits_pow_ten]

    have : ∑ p ∈ Finset.range (10 ^ m) ×ˢ Finset.range 10, (Nat.digits 10 (10 * p.1 + p.2)).sum =
        ∑ p ∈ Finset.range (10 ^ m) ×ˢ Finset.range 10,
        ((Nat.digits 10 (10 * p.1)).sum + (Nat.digits 10 p.2).sum) := by
      apply Finset.sum_congr rfl
      intro p hp
      have h : p.2 < 10 := by
        rw [Finset.mem_product] at hp
        exact Finset.mem_range.mp hp.2

      have digit_sum_add_single_digit (n d : ℕ) (hd : d < 10) :
        (Nat.digits 10 (10 * n + d)).sum = (Nat.digits 10 (10 * n)).sum + (Nat.digits 10 d).sum := by
        -- For single digits, digits 10 d is either [] (if d = 0) or [d] (if d > 0)
        cases' d with d
        · simp [Nat.digits]
        · have hd' : d + 1 < 10 := hd
          simp [List.sum_cons, List.sum_nil]
          rw [show (d + 1) % 10 = d + 1 by exact Nat.mod_eq_of_lt hd]
          simp [add_comm]
          rw [Nat.add_div (by simp)]
          simp
          split_ifs with mod_le
          · simp_all
            omega
          · simp_all [Nat.div_eq_of_lt hd, Nat.mod_eq_of_lt hd]
            rw [<- ten_mul_digits_sum_eq_digits_sum, mul_comm]

      exact digit_sum_add_single_digit p.1 p.2 h

    rw [this]
    clear this
    rw [@Finset.sum_product]
    simp [Finset.sum_add_distrib]
    simp [show Finset.range 10 = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} by rfl]
    ring_nf
    congr
    conv_rhs => rw [show 10 ^ m = 10 * 10 ^ (m - 1) by
      rw [<- Nat.pow_add_one']
      simp
      omega
    ]
    simp [<- Finset.sum_mul]
    suffices ∑ i ∈ Finset.range (10^m), (Nat.digits 10 (i * 10)).sum = m * 10 ^ (m - 1) * 45 by
      linarith
    ring_nf at ih
    have : ∑ i ∈ Finset.range (10 ^ m), (Nat.digits 10 (i * 10)).sum =
      ∑ i ∈ Finset.range (10 ^ m), (Nat.digits 10 i).sum := by
      congr! 1 with i i_in
      simp at i_in
      exact ten_mul_digits_sum_eq_digits_sum

    rw [this]
    exact ih


theorem digit_sum_base_pow_eq {k : ℕ} (hk : 0 < k) :
  (∑ n ∈ Finset.range (10^k), (Nat.digits 10 n).sum) =
    45 * k * 10^(k-1) := by
  rw [Finset.range_eq_Ico]
  rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.pos_of_neZero (10 ^ k))]
  simp
  exact digit_sum_ico_base_pow_eq hk


theorem last_digit_of_div_five (n : ℕ) (pos_n : 0 < n) (h : 5 ∣ n) :
    (Nat.digits 10 n).head? = some 0 ∨ (Nat.digits 10 n).head? = some 5 := by
  -- First, prove that n % 10 is 0 or 5 (from previous theorem)
  have mod_lemma : n % 10 = 0 ∨ n % 10 = 5 := by
    omega

  simp_all
