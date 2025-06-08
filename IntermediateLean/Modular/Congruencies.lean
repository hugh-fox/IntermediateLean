import Mathlib

theorem sq_mod_four {x:ℤ} : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by
    mod_cases h₁ : x^2 % 4
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


example {p q } (h₁₄ : p ≡ 11 [ZMOD 30]) (hq₁₄ : q ≡ 11 [ZMOD 30]) :
    p - q ≡ 0 [ZMOD 30] := by
  have h₁ : 30 ∣ (p - 11) := by
    -- have := h₁₄.dvd
    exact Int.dvd_self_sub_of_emod_eq h₁₄
  have h₂ : 30 ∣ (q - 11) := by
    exact Int.dvd_self_sub_of_emod_eq hq₁₄
  have h₃ : 30 ∣ (p - 11 - (q - 11)) := Int.dvd_sub h₁ h₂
  simp only [sub_sub_sub_cancel_right] at h₃
  exact Dvd.dvd.modEq_zero_int h₃

