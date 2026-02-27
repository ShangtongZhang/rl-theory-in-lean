import Mathlib

/-- `measurable_finset_smul_sum` closes `Measurable` goals of the form
    `Measurable (fun w => ∑ s ∈ S, ∑ s' ∈ S', c s s' • F w (s, s'))`
    by repeatedly peeling off `Finset.measurable_sum` layers and `Measurable.smul`
    decompositions, closing constant sub-goals with `measurable_const`.
    Any remaining inner `Measurable` goal is left for the user. -/
macro "measurable_finset_smul_sum" : tactic =>
  `(tactic| (
    repeat first
      | (apply Finset.measurable_sum; intro _ _)
      | (apply Measurable.smul; try apply measurable_const)
      | apply measurable_const))
