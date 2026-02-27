import Mathlib
import RLTheory.Data.Matrix.Stochastic

/-- `stochastic_rowsum` closes goals of the form `∑ s, f s = 1` or `∑ j, P i j = 1`
    by finding a `StochasticMatrix.StochasticVec` or `StochasticMatrix.RowStochastic`
    instance and discharging via the `.rowsum` field. -/
macro "stochastic_rowsum" : tactic =>
  `(tactic|
    (first
     | exact (inferInstance : StochasticMatrix.StochasticVec _).rowsum
     | (have _h := (inferInstance : StochasticMatrix.StochasticVec _).rowsum; linarith)
     | (simp only [Matrix.vecMul, Matrix.dotProduct, Matrix.mul_apply]
        simp only [(inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.rowsum,
                   (inferInstance : StochasticMatrix.StochasticVec _).rowsum])
     | (apply Finset.sum_congr rfl; intro _i _hi
        simp [(inferInstance : StochasticMatrix.RowStochastic _).stochastic _i |>.rowsum])
     | simp [(inferInstance : StochasticMatrix.StochasticVec _).rowsum]
     | simp [(inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.rowsum]))
