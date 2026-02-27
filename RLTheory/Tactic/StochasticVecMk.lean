import Mathlib
import RLTheory.Data.Matrix.Stochastic

/-- `stochastic_vec_mk` closes a `StochasticVec f` goal by first trying `infer_instance`,
    then splitting into the nonnegativity and sum-to-one obligations and discharging each
    via `positivity`, `norm_num`, `simp`, `linarith`, or `assumption`. -/
macro "stochastic_vec_mk" : tactic =>
  `(tactic| (
    first
    | infer_instance
    | (constructor
       · intro _
         first | positivity | norm_num | simp | linarith
       · first
         | simp [Finset.sum_ite, Finset.filter_eq']
         | norm_num
         | (simp only []; ring_nf; norm_num)
         | assumption)))
