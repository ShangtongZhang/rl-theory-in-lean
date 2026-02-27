import Mathlib
import RLTheory.Data.Matrix.Stochastic

/-- `close_stochastic` closes goals of the form `StochasticVec (μ ᵥ* P)` or
    `RowStochastic (P * Q)` by splitting into `nonneg` and `rowsum` subgoals and
    discharging each using `StochasticVec` and `RowStochastic` instances. -/
macro "close_stochastic" : tactic =>
  `(tactic|
    (first
     | (-- StochasticVec (μ ᵥ* P)
        refine ⟨fun j => ?_, ?_⟩
        · simp only [Matrix.vecMul, Matrix.dotProduct]
          apply Finset.sum_nonneg; intro i _
          apply mul_nonneg
          · exact (inferInstance : StochasticMatrix.StochasticVec _).nonneg _
          · exact (inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.nonneg _
        · simp only [Matrix.vecMul, Matrix.dotProduct]
          rw [Finset.sum_comm]
          simp only [(inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.rowsum,
                     (inferInstance : StochasticMatrix.StochasticVec _).rowsum])
     | (-- RowStochastic (P * Q)
        refine ⟨fun i => ⟨fun j => ?_, ?_⟩⟩
        · simp only [Matrix.mul_apply]
          apply Finset.sum_nonneg; intro k _
          apply mul_nonneg
          · exact (inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.nonneg _
          · exact (inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.nonneg _
        · simp only [Matrix.mul_apply]
          rw [Finset.sum_comm]
          simp_rw [← Finset.mul_sum,
                   (inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.rowsum,
                   mul_one]
          exact (inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.rowsum)))
