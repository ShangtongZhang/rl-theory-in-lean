import Mathlib
import RLTheory.Data.Matrix.Stochastic

/-- `stochastic_nonneg` closes `0 ≤ expr` goals where `expr` is a finite sum of products
    of stochastic vector entries, by repeatedly applying `Finset.sum_nonneg`, `mul_nonneg`,
    and the `.nonneg` fields of any `StochasticVec` or `RowStochastic` instances. -/
macro "stochastic_nonneg" : tactic =>
  `(tactic|
    (first
     | exact (inferInstance : StochasticMatrix.StochasticVec _).nonneg _
     | exact (inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.nonneg _
     | (apply Finset.sum_nonneg; intro _ _;
        first
        | exact (inferInstance : StochasticMatrix.StochasticVec _).nonneg _
        | exact (inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.nonneg _
        | (apply mul_nonneg
           · first
             | exact (inferInstance : StochasticMatrix.StochasticVec _).nonneg _
             | exact (inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.nonneg _
             | positivity
           · first
             | exact (inferInstance : StochasticMatrix.StochasticVec _).nonneg _
             | exact (inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.nonneg _
             | positivity))
     | (apply mul_nonneg <;>
        (first
         | exact (inferInstance : StochasticMatrix.StochasticVec _).nonneg _
         | exact (inferInstance : StochasticMatrix.RowStochastic _).stochastic _ |>.nonneg _
         | positivity))))
