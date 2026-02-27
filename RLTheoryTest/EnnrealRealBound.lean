import Mathlib
import RLTheory.Tactic.EnnrealRealBound

-- one example that uses `ennreal_real_bound` as a proof step
example (a b : ℝ) (h : a ≤ b) : ENNReal.ofReal a ≤ ENNReal.ofReal b := by
  ennreal_real_bound
