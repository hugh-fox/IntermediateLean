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
