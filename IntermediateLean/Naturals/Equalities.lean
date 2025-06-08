import Mathlib

-- There is certainly a simpler proof for this one.
theorem Nat.sub_sq {a b : ℕ} (b_le_a : b ≤ a) :
    (a - b)^2 = (a^2 + b^2) - 2*a*b := by
  have b_sq_le_ba : b*b ≤ b*a := by
    exact mul_le_mul_left b b_le_a

  have ba_le_a_sq : b*a ≤ a*a := by
    exact mul_le_mul_right a b_le_a

  simp [sq]
  rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_sub]
  -- These two lines can be done by omega, but are left as documentation
  rw [Nat.sub_right_comm, tsub_tsub_assoc ba_le_a_sq b_sq_le_ba]
  rw [<- Nat.sub_add_comm ba_le_a_sq]

  suffices (a*a + b*b) - (b*a + a*b) = (a*a + b*b) - 2*a*b by
    omega

  ring_nf


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
