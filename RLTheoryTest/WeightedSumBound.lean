import Mathlib
import RLTheory.Tactic.WeightedSumBound

-- one example that uses `weighted_sum_bound` as a proof step
example (w : Fin 3 → NNReal) (f g : Fin 3 → ℝ) (hfg : ∀ i, f i ≤ g i) :
    ∑ i : Fin 3, (w i : ℝ) * f i ≤ ∑ i : Fin 3, (w i : ℝ) * g i := by
  weighted_sum_bound
