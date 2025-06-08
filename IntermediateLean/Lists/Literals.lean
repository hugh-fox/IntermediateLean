/-
This file has examples of dealing with simple list literals (or lemmas that by
definition require a little brute force). These can can be
surprisingly tricky to work with. The general idea is to convert to a goal
that is decidable, e.g. with `List.contains_eq`, or compute everything
directly with simp_all.
-/

import Mathlib

example {a b : ℕ}
  (digits_in : [a, b] ∈ [1, 2].permutations)
  (b_eq : b = 2)
  : a = 1
    := by
  simp_all [List.cons_perm_iff_perm_erase]
  aesop

example {a b : ℕ}
  (digits_in : [a, b] ∈ [1, 2].permutations)
  : a = 1 ∨ a = 2
    := by
  simp_all [List.cons_perm_iff_perm_erase]

example {a b : ℕ}
  (digits_in : [a, b] ∈ [1, 2].permutations)
  : b = 1 ∨ b = 2
    := by
  simp_all
  have := List.Perm.contains_eq (l₁ := [a, b]) (l₂ := [1, 2]) (a := b) digits_in
  simpa using this

example {a b c : ℕ}
  (digits_in : [a, b, c] ∈ [1, 2, 3].permutations)
  (b_eq : b = 2)
  : a = 1 ∨ a = 3
    := by
  simp_all
  have : a ≠ 2 := by
    intro eq
    subst a b
    have := List.Perm.contains_eq (l₁ := [2, 2, c]) (l₂ := [1, 2, 3]) (a := 2) digits_in
    simp_all [List.cons_perm_iff_perm_erase]

  have := List.Perm.contains_eq (l₁ := [a, 2, c]) (l₂ := [1, 2, 3]) (a := a) digits_in
  simp at this
  omega
