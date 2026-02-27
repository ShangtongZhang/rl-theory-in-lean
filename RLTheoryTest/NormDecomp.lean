import Mathlib
import RLTheory.Tactic.NormDecomp

-- one example that uses `norm_decomp` as a proof step
example (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) (r : ℝ) :
    ‖r • a + b‖ ≤ ‖r‖ * ‖a‖ + ‖b‖ := by
  norm_decomp
  linarith
