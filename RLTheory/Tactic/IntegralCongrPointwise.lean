import Mathlib

/-- `integral_congr_pointwise` rewrites under an integral sign by a pointwise equality.
    It expands to:
      `rw [MeasureTheory.integral_congr_ae _]; rotate_right;
       apply Filter.Eventually.of_forall; intro`
    leaving the user with a pointwise goal.
    An optional term names the introduced variable. -/
syntax "integral_congr_pointwise" (ppSpace term:max)? : tactic

macro_rules
  | `(tactic| integral_congr_pointwise) =>
    `(tactic| (rw [MeasureTheory.integral_congr_ae _]
               rotate_right
               apply Filter.Eventually.of_forall
               intro))
  | `(tactic| integral_congr_pointwise $x:term) =>
    `(tactic| (rw [MeasureTheory.integral_congr_ae _]
               rotate_right
               apply Filter.Eventually.of_forall
               intro $x:term))
