/-
# Tactics

### This file enumerates common tactics in lean4, specifically from Mathlib.
### They are ranked in order from most general/powerful to least. Common use
### cases are listed for each.

-/

import Mathlib

/-
### aesop
-/

/-
### simp_all
-/

/-
### wlog
For when you want to:
- Show that it suffices to show one of two goals if both are equal symmetric
  versions of each other

-/

-- Example of using wlog. The idea of wlog is to introduce an auxilary goal
-- where x and y are swapped, and you need to show that reduces to the original
-- problem. In this case, max y x reduces to max y x using Nat.max_comm.
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

-- Incomplete proof, but contains a good use case for wlog
-- The sum_sq_sub_mul_ne_one_of_ne theorem proved without the am-gm inequality
example {a b : ℕ} (pos_a : 0 < a) (pos_b : 0 < b) (ne : a ≠ b) :
    a^2 + b^2 - a*b ≠ 1 := by
  intro eq
  -- We can impose an ordering without loss of generality
  wlog a_lt_b : a < b
  · rw [add_comm, mul_comm] at eq
    exact @this b a pos_b pos_a ne.symm eq (by omega)

  -- suffices 1 < a ^ 2 + b ^ 2 - a * b by
  --   exact?
  induction' a with m ih
  · contradiction
  · have pos_m : m ≠ 0 := by
      intro m_eq_zero
      subst m
      replace eq : b^2 - b = b * 0 := by
        omega

      rw [sq, <- Nat.mul_sub_one b b] at eq
      replace eq : b - 1 = 0 := by
        exact Nat.eq_of_mul_eq_mul_right pos_b (by linarith)

      omega

    replace pos_m : 0 < m := Nat.zero_lt_of_ne_zero pos_m
    have one_lt_prod : 1 < m * b := by
      by_cases m = 1
      · have : 1 < b := by omega
        exact Right.one_lt_mul_of_le_of_lt pos_m this
      · have : 1 < m := by omega
        exact Left.one_lt_mul_of_lt_of_le this pos_b
    specialize ih (by omega) (by linarith)
    apply ih ?_ (by omega)
    have : b ^ 2 > (m + 1) * b := by
      field_simp [sq]
      exact a_lt_b

    conv_lhs at eq => calc (m + 1) ^ 2 + b ^ 2 - (m + 1) * b
      _ = m^2 + 2*m + 1 + b ^ 2 - (m + 1) * b := by ring
      _ = 2*m + 1 + m^2 + b ^ 2 - (m * b + b) := by ring
      _ = 2*m + 1 + m^2 + b ^ 2 - m * b - b := by omega
      _ = 2*m + 1 + m^2 + b ^ 2 - m * b - b := by omega


/-
### Congruency
For when you want to:
- apply a function on both sides of an equation or inequality (or algebra)
- simplify a function being applied to two sides of an equation
- reduce a goal and a hypothesis that are partially equal to only their
  difference

There are a few ways to apply congruency in lean, some common ones are:
- gcongr - general congruency (both equalites and inequalities)
- convert, convert_to - general way to simplify using parts of a hypothesis
- congr, congr! - fairly general, only for equalities
- apply congrArg f at hypothesis - surgical

The congr! and convert tactics take a number (for convert, the syntax is `using
0` or `using n` where n is a literal number) which determines how many levels
of reduction are applied. For example, congr! 1 reduces `f(g(x)) = f(g(y))` to
`g(x) = g(y)`, instead of the default which would be `x = y`.

Extensionality is a similar, but different concept. See the section on the
`ext` tactic for more.
-/



/-
Most tactics can be blindly applied to a proof without fully understanding how
they work. Congr is not one of them. When using it, you should confirm that
the goal is still provable. At the end of the example below, proof is no longer
possible.
-/
example {n} : (Finset.Icc 0 n).card = (Finset.Icc 1 (n+1)).card := by
  -- `congr 0` doesn't work either, but its easier to see why. `congr 1` on
  -- the surface might look provable but really isn't.
  congr! 1
  admit


/-
This tactics attempts to find the fewest imports necessary. It must be at the
end of the file.
-/
#min_imports
