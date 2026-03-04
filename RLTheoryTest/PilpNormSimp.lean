import Mathlib
import RLTheory.Tactic.PilpNormSimp

-- Demonstrate that `piLp_norm_simp` normalises the L∞ PiLp norm expression.
-- `PiLp.norm_eq_ciSup` rewrites ‖x‖ to ⨆ i, ‖x i‖,
-- then `Real.norm_eq_abs` converts the inner norm to absolute value.
example (x : PiLp ⊤ (fun _ : Fin 2 => ℝ)) :
    ‖x‖ = ⨆ i, |x i| := by
  piLp_norm_simp
