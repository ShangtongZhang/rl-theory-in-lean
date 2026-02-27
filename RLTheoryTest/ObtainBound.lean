import Mathlib
import RLTheory.Tactic.ObtainBound

-- Demonstrate `obtain_bound`: destruct a bound hypothesis `h : ∃ C, 0 ≤ C ∧ P C`
-- and re-export the same witness, leaving only the body `P C` as the remaining goal.
example (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ^ 2 ≤ C * x ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ^ 2 ≤ C * x ^ 2 := by
  obtain_bound h as C, hC_nonneg, hC_bound
  exact hC_bound
