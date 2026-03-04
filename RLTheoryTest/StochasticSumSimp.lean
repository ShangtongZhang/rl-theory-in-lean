import Mathlib
import RLTheory.Tactic.StochasticSumSimp

-- Test that stochastic_sum_simp can distribute sums over addition and pull
-- scalar factors out of finite sums.
example (f g : Fin 3 → ℝ) :
    ∑ i : Fin 3, (f i + g i) = ∑ i : Fin 3, f i + ∑ i : Fin 3, g i := by
  stochastic_sum_simp
