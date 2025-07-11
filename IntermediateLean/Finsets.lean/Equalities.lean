import Mathlib


theorem range_eq_range_succ_div (k : ℕ) :
  (Finset.range (10^(k))).image id =
  (Finset.range (10^(k+1))).image (λ n => (n / 10)) := by
  ext x
  simp
  constructor
  · intro x_lt
    use x * 10
    constructor
    ·
      rw [Nat.pow_add_one']
      linarith
    · simp
  ·
    by_contra! h
    obtain ⟨ ⟨ y, y_lt, y_eq ⟩, x_le ⟩ := h
    subst x
    omega


theorem range_mod_eq_range_succ_mod (k : ℕ) (pos_k : 0 < k) :
  (Finset.range (10^(k))).image (· % 10) =
  (Finset.range (10^(k+1))).image (· % 10) := by
  have h₁ : 10 ≤ 10^k := by
    rw [← pow_one 10]
    exact Nat.pow_le_pow_right (by norm_num) pos_k

  have h₂ : (Finset.range (10^k)).image (· % 10) = Finset.range 10 := by
    have : Finset.range 10 ⊆ Finset.range (10^k) := by
      exact GCongr.finset_range_subset_of_le h₁
    have : ∀ n, n % 10 ∈ Finset.range 10 := by
      intro n
      simp
      refine Nat.mod_lt n (by simp)
    ext x
    simp
    constructor
    · rintro ⟨ y, y_in, y_mod ⟩
      simp_all
      omega
    · intro x_lt
      use x
      omega

  have h₃ : 10 ≤ 10^(k+1) := by
    rw [pow_succ]
    linarith

  have h₄ : (Finset.range (10^(k+1))).image (· % 10) = Finset.range 10 := by
    have : Finset.range 10 ⊆ Finset.range (10^k) := by
      exact GCongr.finset_range_subset_of_le h₁

    rw [<- h₂]
    ext x
    simp_all
    constructor
    · rintro ⟨ y, y_lt, y_mod_eq_x ⟩
      rw [<- y_mod_eq_x]
      refine Nat.mod_lt y (by simp)

    · intro x_lt
      use x
      simp_all
      exact Nat.lt_of_lt_of_le x_lt h₃

  rw [h₂, h₄]
