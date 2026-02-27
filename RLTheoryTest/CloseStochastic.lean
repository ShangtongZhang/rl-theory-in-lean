import Mathlib
import RLTheory.Tactic.CloseStochastic

open scoped BigOperators

-- Demonstrates close_stochastic: proves RowStochastic (P * Q) given two RowStochastic instances.
example {S : Type*} [Fintype S] [DecidableEq S] (P Q : Matrix S S ℝ)
    [StochasticMatrix.RowStochastic P] [StochasticMatrix.RowStochastic Q] :
    StochasticMatrix.RowStochastic (P * Q) := by
  close_stochastic
