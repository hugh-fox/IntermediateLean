import Mathlib


example (s : Finset ℕ) (h : s.card = 29) :
    ∃ t ⊆ s, t.card = 15 ∧ ∑ i ∈ t, i ≡ 0 [ZMOD 15] := by
  have egz := ZMod.erdos_ginzburg_ziv (n := 15)
    (λ x => x) (s := s) (by linarith)

  obtain ⟨ t, t_in, t_card, t_sum ⟩ := egz
  use t, t_in, t_card

  suffices ∑ i ∈ t, i ≡ 0 [MOD 15] by
    simp [Nat.modEq_iff_dvd] at this
    simp [Int.modEq_iff_dvd]
    exact this

  simp at t_sum
  have := ZMod.natCast_eq_natCast_iff (t.sum id) 0 15
  simp at this
  rwa [this] at t_sum
