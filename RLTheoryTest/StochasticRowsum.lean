import Mathlib
import RLTheory.Tactic.StochasticRowsum

open scoped BigOperators

-- Demonstrates stochastic_rowsum: closes `∑ s, μ s = 1` given a StochasticVec instance.
example {S : Type*} [Fintype S] (μ : S → ℝ) [StochasticMatrix.StochasticVec μ] :
    ∑ s, μ s = 1 := by
  stochastic_rowsum
