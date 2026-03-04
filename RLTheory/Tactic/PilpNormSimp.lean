import Mathlib

/-- A single-call simp macro that rewrites all PiLp norm heads in the goal.
    Handles the L∞ case via `PiLp.norm_eq_ciSup`, plus coercion/real-cast cleanup. -/
macro "piLp_norm_simp" : tactic =>
  `(tactic| simp only [
      PiLp.norm_eq_ciSup,
      PiLp.toLp_apply,
      Real.norm_eq_abs, ENNReal.toReal_ofNat,
      NNReal.coe_ofNat])
