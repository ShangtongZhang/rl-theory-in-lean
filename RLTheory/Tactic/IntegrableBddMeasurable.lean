import Mathlib

/-- `integrable_bdd_measurable` closes `Integrable f μ` goals by applying
    `Integrable.mono'` with a constant bound witness from `integrable_const`,
    dispatching the AE strong measurability subgoal with `assumption` or
    `measurability`, and the norm-bound subgoal with `assumption` (handles both
    `∀ᵐ ω ∂μ, ‖f ω‖ ≤ C` and `∀ ω, ‖f ω‖ ≤ C` hypotheses in context). -/
macro "integrable_bdd_measurable" : tactic =>
  `(tactic| (
    apply MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const _)
    · apply Measurable.aestronglyMeasurable
      first | assumption | measurability
    · first
      | assumption
      | (apply Filter.Eventually.of_forall; intro; assumption)
      | (obtain ⟨C, _, hC⟩ := ‹_›
         exact Filter.Eventually.of_forall (fun ω => hC ω _))))
