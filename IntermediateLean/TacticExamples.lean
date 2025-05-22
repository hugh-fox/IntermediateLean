/-
# Tactics

### This file enumerates common tactics in lean4, specifically from Mathlib.
### They are ranked in order from most general/powerful to least. Common use
### cases are listed for each.

-/

import Mathlib


/-
Example of using wlog. The idea of wlog is to introduce an auxilary goal where
x and y are swapped, and you need to show that reduces to the original problem. In this case, max y x reduces to max y x using Nat.max_comm.
-/
example (x y : ℕ) : max x y = x ∨ max x y = y := by
  -- Without loss of generality, assume x ≤ y
  wlog h : x ≤ y with H
  · simp at h
    specialize H y x h.le
    rw [Or.comm] at H
    rwa [Nat.max_comm x y]

  right
  exact show max x y = y from Nat.max_eq_right h


example {a b : ℤ} (pos_a : a ≠ 0) (a_ne_b : a ≠ b) :
    (a-b)^2 > 0 ∧ (b-a)^2 > 0 := by
  wlog h : |a - b| = |b - a| with H
  · have : |a - b| = |b - a| := abs_sub_comm a b
    contradiction

  rw [<- sq_abs (a - b), <- sq_abs (b - a)]
  rw [<- h, and_self]
  apply Int.pow_pos
  rwa [<- abs_sub_pos] at a_ne_b
