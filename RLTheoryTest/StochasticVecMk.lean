import Mathlib
import RLTheory.Tactic.StochasticVecMk

open StochasticMatrix

-- Demonstrates stochastic_vec_mk: closes a StochasticVec goal for a concrete constant function
-- on Fin 1, where nonneg is closed by norm_num and rowsum by simp.
example : StochasticVec (fun (_ : Fin 1) => (1 : ℝ)) := by
  stochastic_vec_mk
