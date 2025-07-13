import Mathlib

theorem sq_mod_four {x:ℤ} : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by
  mod_cases x^2 % 4
  · left
    assumption
  · right
    assumption
  · have := Int.sq_ne_two_mod_four x
    simp [← ZMod.intCast_eq_intCast_iff, <- sq] at this
    contradiction
  · rcases Int.even_or_odd x with (⟨k, eq⟩ | ⟨k, eq⟩)
    · subst eq
      ring_nf
      omega
    · right
      exact Int.sq_mod_four_eq_one_of_odd ⟨k, eq⟩

theorem sum_of_two_squares_not_three_mod_four :
    ¬ ∃ (a b : ℤ), a^2 + b^2 ≡ 3 [ZMOD 4] := by
  intro h
  obtain ⟨a, b, h : (a ^ 2 + b ^ 2) % 4 = 3 ⟩ := h
  cases @sq_mod_four a <;> cases @sq_mod_four b
    <;> omega


example {p q} (hp : p ≡ 11 [ZMOD 30]) (hq : q ≡ 11 [ZMOD 30]) :
    p - q ≡ 0 [ZMOD 30] := by
  have h₁ : 30 ∣ (p - 11) := by
    exact Int.dvd_self_sub_of_emod_eq hp

  have h₂ : 30 ∣ (q - 11) := by
    exact Int.dvd_self_sub_of_emod_eq hq

  have h₃ : 30 ∣ (p - 11 - (q - 11)) := Int.dvd_sub h₁ h₂
  simp only [sub_sub_sub_cancel_right] at h₃
  exact Dvd.dvd.modEq_zero_int h₃


example {p q} (hp : p ≡ 11 [ZMOD 30]) (hq : q ≡ 11 [ZMOD 30]) :
    p - q ≡ 0 [ZMOD 30] := by
  -- To give library search the best chances, don't simplify theorems:
  have : p - q ≡ 11 - 11 [ZMOD 30] := by
    exact Int.ModEq.sub hp hq

  exact this

theorem three_pow_congruent_one_mod_five_of_four_dvd {n} :
    4 ∣ n → 3^n ≡ 1 [MOD 5] := by
  rintro ⟨ k, k_eq ⟩
  subst n
  have : 3^0 ≡ 1 [MOD 5] := by rfl
  have : 81^k ≡ 1^k [MOD 5] := by
    exact Nat.ModEq.pow k this

  have : 3^0 * 81^k ≡ 1 [MOD 5] := by
    simpa

  convert this using 1
  ring_nf
  rw [show 81 = 3^4 by rfl]
  exact Nat.pow_mul' 3 k 4


example (n : ℕ) (h : n % 10 = 5) : 5 ∣ n := by
  omega


-- Previous theorem proven with modular congruence
example (n : ℕ) (h : n % 10 = 5) : 5 ∣ n := by
  use 2 * n / 10

  rw [<- Nat.mul_div_assoc _ (by
    suffices 5 ∣ n by exact Nat.mul_dvd_mul_left 2 this

    replace : n ≡ 5 [MOD 5 * 2] := by
      rwa [show 10 = 5 + 5 by rfl] at h

    replace : n ≡ 5 [MOD 5] := by
      exact Nat.ModEq.of_mul_right 2 this
    -- Sometimes exact does a non-trivial amount of work. Trying to naively
    -- combine this with the previous have statement doesn't work.
    replace : n ≡ 0 [MOD 5] := by
      exact this

    exact Nat.dvd_of_mod_eq_zero this
  )]
  simp [<- mul_assoc]


-- Previous theorem proven without omega
example (n : ℕ) (h : n % 10 = 5) : 5 ∣ n := by
  -- Any natural number can be expressed as 10*k + its last digit
  have : n = 10 * (n / 10) + n % 10 := by
    exact Eq.symm (Nat.div_add_mod n 10)
  -- Substitute our hypothesis about the last digit
  rw [h] at this
  rw [this]
  rw [show 10 = 5 * 2 by rfl]
  simp only [Nat.dvd_add_self_right, mul_assoc]
  exact Nat.dvd_mul_right 5 (2 * (n / (5 * 2)))


example (n : ℕ) (h : 5 ∣ n) :
    n % 10 = 0 ∨ n % 10 = 5 := by
  -- Since 5 divides n, there exists some k such that n = 5 * k
  rcases h with ⟨k, rfl⟩

  -- We can now rewrite n as 5 * k
  -- We consider the possible remainders of k modulo 2, since 10 = 5 * 2
  -- k % 2 can only be 0 or 1, since it's modulo 2
  mod_cases k % 2
  · apply Or.inl
    obtain ⟨ j, j_eq ⟩ : Even k := by
      exact Nat.even_iff.mpr H

    subst j_eq
    simp [<- two_mul, <- mul_assoc]

  · apply Or.inr
    obtain ⟨ j, j_eq ⟩ : Odd k := by
      exact Nat.odd_iff.mpr H

    subst j_eq
    simp [<- two_mul, mul_add, <- mul_assoc]


example (n : ℕ) (h : 5 ∣ n) : n % 10 = 0 ∨ n % 10 = 5 := by
  omega
