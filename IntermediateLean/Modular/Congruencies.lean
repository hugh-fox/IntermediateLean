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

