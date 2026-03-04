import Mathlib

-- `stochastic_sum_simp` unfolds and collapses double sums weighted by
-- stochastic vectors / row-stochastic matrices.
--
-- It collects: Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
-- ← Finset.sum_smul, one_mul, mul_one, Finset.smul_sum, smul_smul
--
-- Usage:  `stochastic_sum_simp`

macro "stochastic_sum_simp" : tactic =>
  `(tactic|
    (simp only [
       Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
       ← Finset.sum_smul, one_mul, mul_one,
       Finset.smul_sum, smul_smul]
     try simp))
