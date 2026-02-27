import Mathlib
import RLTheory.Tactic.WeightedSqNonneg

-- Demonstrate `weighted_sq_nonneg` on a concrete sum where weights are squares (nonneg by positivity).
example (n : ℕ) (w : Fin n → ℝ) (v : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, w i ^ 2 * v i ^ 2 := by
  weighted_sq_nonneg
