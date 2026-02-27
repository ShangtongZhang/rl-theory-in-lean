import Mathlib
import RLTheory.Tactic.NatFindLtIffSimp

-- Demonstrate nat_find_lt_iff_simp: close a goal of the form `Nat.find h > 3`
-- by automatically applying Nat.find_spec to the existence witness in context.
example (h : ∃ n : ℕ, n > 3) : Nat.find h > 3 := by
  nat_find_lt_iff_simp
