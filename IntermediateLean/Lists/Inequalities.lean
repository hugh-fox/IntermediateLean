import Mathlib


theorem no_one_head_in_max_prod (n) (l : List ℕ) (no_zero : 0 ∉ l)
  : (1 :: n :: l).sum = ((n + 1) :: l).sum
  ∧ (1 :: n :: l).prod < ((n + 1) :: l).prod
    := by

  norm_num [<- add_assoc, add_comm]
  gcongr
  · suffices 0 ≠ l.prod from Nat.zero_lt_of_ne_zero this.symm
    intro zero_eq
    have : 0 ∈ l := List.prod_eq_zero_iff.mp zero_eq.symm
    contradiction
  · exact lt_add_one n


lemma no_ones_in_max_prod : ∀ optimal : List ℕ,
  0 ∉ optimal → 1 < optimal.sum  →
  (¬∃ candidate : List ℕ, candidate.sum = optimal.sum
    ∧ candidate.prod > optimal.prod)
  → ∀ n ∈ optimal, n > 1
    := by
  intro optimal no_zero pos_sum_gt2 not_exists n n_mem
  contrapose! not_exists with not_lt_of_gt
  replace n_gt : n = 1 := by
    by_contra! ne
    have : n = 0 := by omega
    subst n
    contradiction
  subst n_gt
  obtain ⟨ xs, ys, l_eq ⟩ := List.mem_iff_append.mp n_mem
  subst l_eq
  rw [show (xs ++ 1 :: ys).sum = (1 :: (xs ++ ys)).sum by
    simp only [List.sum_append, List.sum_cons, add_assoc, add_comm]
  ]
  rw [show (xs ++ 1 :: ys).prod = (xs ++ ys).prod by simp]
  cases h : (xs ++ ys)
  · simp_all
  · rename_i head tail
    have : 0 ∉ tail := by
      simp at no_zero
      have : 0 ∉ xs ++ ys := by
        simp [no_zero]
      rw [h] at this
      exact List.not_mem_of_not_mem_cons this

    have := no_one_head_in_max_prod head tail this
    simp [<- add_assoc] at this
    use (1 + head) :: tail
    simp
    constructor <;> linarith
