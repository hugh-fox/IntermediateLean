import Mathlib

theorem factorization_lcm_max {p : ℕ} {a b : ℤ}
  (ha : a ≠ 0) (hb : b ≠ 0) {prime_p : Prime p} :
  padicValNat p (a.lcm b) = padicValInt p a ⊔ padicValInt p b
    := by
  have := @Nat.factorization_lcm a.natAbs b.natAbs
    (Int.natAbs_ne_zero.mpr ha)
    (Int.natAbs_ne_zero.mpr hb)
  apply congrArg (· p) at this
  unfold padicValInt
  simp [<- Nat.factorization_def _ prime_p.nat_prime]
  exact this
