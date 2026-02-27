import Mathlib
import RLTheory.Tactic.StochasticNonneg

open scoped BigOperators

-- Demonstrates stochastic_nonneg: closes `0 ≤ ∑ i, μ i * P i j` given StochasticVec and RowStochastic instances.
example {S : Type*} [Fintype S] (μ : S → ℝ) [StochasticMatrix.StochasticVec μ]
    (P : Matrix S S ℝ) [StochasticMatrix.RowStochastic P] (j : S) :
    0 ≤ ∑ i, μ i * P i j := by
  stochastic_nonneg
