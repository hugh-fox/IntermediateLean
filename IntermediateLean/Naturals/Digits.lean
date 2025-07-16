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


def fin_add_equiv_pair {b i j} : Fin (b ^ (i + j)) ≃ (Fin (b ^ i) × Fin (b ^ j)) :=
  (finCongr (Nat.pow_add b i j)).trans finProdFinEquiv.symm


theorem sum_add_eq_sum_pair {α : Type*}
  [AddCommMonoid α] {i j : ℕ} {f : ℕ → α} :
  ∑ x : Fin (i*j), f x =
  ∑ p : Fin i × Fin j,
    f (j * p.fst + p.snd : ℕ) := by
  have := @Equiv.sum_comp α _ _ _ (ι := Fin i × Fin j) (κ := Fin (i*j))
    (e := finProdFinEquiv) (g := λ x => f x)

  simp [<- this, add_comm]


theorem sum_range_mul_eq_sum_pair {α : Type*}
  [AddCommMonoid α] {f : ℕ → α} {i j : ℕ} :
  ∑ x ∈ Finset.range (i*j), f x =
  ∑ p ∈ Finset.range i ×ˢ Finset.range j,
    f (j * p.fst + p.snd) := by
  simp [sum_add_eq_sum_pair, Finset.sum_range, Fintype.sum_prod_type,
    Finset.sum_product
  ]


-- A more specific version of this was proven in episode 3, but a much
-- better method is shown above.
example {α : Type*}
  [AddCommMonoid α] {f : ℕ → α} {i j : ℕ} :
  ∑ x ∈ Finset.range (i*j), f x =
  ∑ p ∈ Finset.range (i) ×ˢ Finset.range (j),
    f (j * p.fst + p.snd) := by
  rw [Finset.sum_bij (fun x x_in => (x / j, x % j))]
  · intro x x_in
    simp [Nat.pow_add', Nat.mod_lt] at x_in ⊢
    rw [mul_comm] at x_in
    constructor
    · exact Nat.div_lt_of_lt_mul x_in
    · have : 0 < j := by
        exact Nat.pos_of_lt_mul_right x_in
      exact Nat.mod_lt x this
  · simp
    intro x hx y x_lt_y f_eq mod_eq
    have x_eq := Nat.div_add_mod x j
    have y_eq := Nat.div_add_mod y j
    rw [<- x_eq, <- y_eq, mod_eq, f_eq]
  · simp
    intro x y x_lt y_lt
    use j * x + y
    split_ands
    ·
      have : j ∣ i * j := by
        exact dvd_mul_left j i
      suffices (j * x + y) / j < (i * j) / j by
        apply Nat.lt_of_div_lt_div this
      have pos_j : 0 < j := by
        exact Nat.zero_lt_of_lt y_lt
      rw [Nat.mul_div_cancel i pos_j]
      have : j ∣ j * x := by
        exact Nat.dvd_mul_right j x
      rw [show (j * x + y) / j = x + y / j by
        exact Nat.mul_add_div pos_j x y
      ]
      rw [show y / j = 0 by exact Nat.div_eq_of_lt y_lt]
      exact x_lt
    · have pos_pow : 0 < j := by
        exact Nat.zero_lt_of_lt y_lt
      rw [Nat.add_div (pos_pow)]
      have : y % j < j := by
        exact Nat.mod_lt y pos_pow
      replace : ¬j ≤ y % j := by
        exact Nat.not_le_of_lt this
      simp [this]
      rw [show y / j = 0 by exact Nat.div_eq_of_lt y_lt]
      exact Nat.mul_div_right x pos_pow
    · simp only [Nat.mul_add_mod_self_left]
      exact Nat.mod_eq_of_lt y_lt
  · simp
    intro x x_in_s
    congr!
    rw_mod_cast [Nat.div_add_mod x j]


theorem sum_pow_add_eq_sum_pair {α : Type*}
  [AddCommMonoid α] {f : ℕ → α} {i j b : ℕ} :
  ∑ x ∈ Finset.range (b^(i+j)), f x =
  ∑ p ∈ Finset.range (b^i) ×ˢ Finset.range (b^j),
    f (b^j * p.fst + p.snd) := by
  have := @sum_range_mul_eq_sum_pair α _ f (i := b^i) (j := b^j)
  rw [<- Nat.pow_add] at this
  exact this


theorem sum_add_eq_sum_parts {α : Type*}
  [AddCommMonoid α] {f : ℕ → α} {i j b : ℕ} :
  ∑ x ∈ Finset.range (b^(i+j)), f x =
  ∑ x ∈ Finset.range (b^i), ∑ y ∈ Finset.range (b^j),
    f (b^j * x + y : ℕ) := by
  rw [sum_pow_add_eq_sum_pair]
  exact Finset.sum_product (Finset.range (b ^ i))
    (Finset.range (b ^ j)) fun x ↦ f (b ^ j * x.fst + x.snd : ℕ)


example {i j b : ℕ} :
  ∑ x ∈ Finset.range (b^(i+j)), (Nat.digits b x).sum =
  ∑ x ∈ Finset.range (b^i), ∑ y ∈ Finset.range (b^j),
    (Nat.digits b (b^j * x + y)).sum := by
  exact sum_add_eq_sum_parts


theorem digits_sum_eq_self {x b : ℕ} (hxb : x < b) : (b.digits x).sum = x := by
  by_cases x_eq : x = 0
  · simp_all
  simp [Nat.digits_of_lt b x x_eq hxb]


theorem digits_sum_mul {n b : ℕ} (hb : 1 < b) : (b.digits n).sum = (b.digits (b * n)).sum := by
  by_cases n_eq : n = 0
  · simp [n_eq]
  conv_rhs => rhs; rhs; rw [<- pow_one b]
  rw [Nat.digits_base_pow_mul hb (by omega)]
  simp


-- Closed form formula for summing digits from up to powers of 10.
theorem digit_sum_ico_base_pow_eq {k b : ℕ} (hk : 0 < k) (hb : 1 < b) :
    2 * ∑ n ∈ Finset.range (b^k), (Nat.digits b n).sum = (b-1) * k * b^k := by
  have pos_b : 0 < b := by
    exact Nat.zero_lt_of_lt hb

  have sum_sum_digits : 2 * ∑ x ∈ Finset.range b, (b.digits x).sum = b * (b - 1) := by
    rw [mul_comm, <- Finset.sum_range_id_mul_two]
    congr! with x x_in
    simp at x_in
    simp [digits_sum_eq_self x_in]

  induction' k, (by linarith : 1 ≤ k) using Nat.le_induction with m ge ih
  · simp [sum_sum_digits, mul_comm]
  · specialize ih ge
    have pos_m : 0 < m := by positivity

    have digits_eq_cons := Nat.digits_eq_cons_digits_div
      hb (Nat.ne_zero_of_lt ge)

    have pos_n : ∀ n ∈ Finset.Ico 1 (b^m), 0 < n := by
      intro n n_in
      simp at n_in
      exact n_in.left

    rw [sum_pow_add_eq_sum_pair]

    have : ∑ p ∈ Finset.range (b ^ m) ×ˢ Finset.range b, (Nat.digits b (b * p.fst + p.snd)).sum =
        ∑ p ∈ Finset.range (b ^ m) ×ˢ Finset.range b,
        ((Nat.digits b (b * p.fst)).sum + (Nat.digits b p.snd).sum) := by
      apply Finset.sum_congr rfl
      intro p hp
      have h : p.snd < b := by
        rw [Finset.mem_product] at hp
        exact Finset.mem_range.mp hp.right

      have digit_sum_add_single_digit (n d : ℕ) (hd : d < b) :
        (Nat.digits b (b * n + d)).sum = (Nat.digits b (b * n)).sum + (Nat.digits b d).sum := by
        cases' d with d
        · simp
        · have hd' : d + 1 < b := hd
          rw [add_comm, Nat.digits_add b hb _ _ hd (by omega)]
          simp [add_comm, List.sum_cons, List.sum_nil, digits_sum_eq_self hd]
          exact digits_sum_mul hb

      exact digit_sum_add_single_digit p.1 p.2 h

    simp [this]
    clear this
    rw [@Finset.sum_product]
    simp [Finset.sum_add_distrib, mul_add]
    simp [<- Finset.mul_sum]
    conv_lhs => rhs; rw [<- mul_assoc, mul_comm 2, mul_assoc, sum_sum_digits]
    simp [<- digits_sum_mul hb]
    rw [<- mul_assoc, mul_comm 2, mul_assoc]
    simp [ih]
    ring_nf


theorem digit_sum_base_pow_eq {k : ℕ} (hk : 0 < k) :
  (∑ n ∈ Finset.range (10^k), (Nat.digits 10 n).sum) =
    45 * k * 10^(k-1) := by
  -- simp
  have := digit_sum_ico_base_pow_eq hk (by simp : 1 < 10)
  have : ∑ n ∈ Finset.range (10 ^ k), (Nat.digits 10 n).sum = (10 - 1) * k * 10 ^ k / 2 := by
    omega

  rw [this]
  simp [show 10^k = 10 * 10^(k-1) by
    simp [<- Nat.pow_add_one']
    exact (Nat.sub_eq_iff_eq_add hk).mp rfl
  ]
  norm_num [<- Nat.mul_assoc, mul_comm]

  rw [show k * 9 * 10 * 10 ^ (k - 1) = 2 * k * 45 * 10 ^ (k - 1) by
    linarith
  ]
  field_simp [mul_assoc]
  omega


theorem last_digit_of_div_five (n : ℕ) (pos_n : 0 < n) (h : 5 ∣ n) :
    (Nat.digits 10 n).head? = some 0 ∨ (Nat.digits 10 n).head? = some 5 := by
  -- First, prove that n % 10 is 0 or 5 (from previous theorem)
  have mod_lemma : n % 10 = 0 ∨ n % 10 = 5 := by
    omega

  simp_all
