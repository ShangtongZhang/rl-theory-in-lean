import Mathlib

/-- `measurable_piLE_weaken` closes goals of the form `Measurable[piLE n] f`
    when the required measurability follows from a finer `piLE m` (m ≤ n)
    by applying `Measurable.mono` and discharging the monotonicity side-goal
    with `piLE.mono` + `omega` or `linarith`. -/
macro "measurable_piLE_weaken" : tactic =>
  `(tactic| (
    apply Measurable.mono _ _ le_rfl
    · first
      | assumption
      | (apply Measurable.comp _ _; assumption; assumption)
    · first
      | (apply MeasureTheory.Filtration.piLE.mono; omega)
      | (apply MeasureTheory.Filtration.piLE.mono; linarith)
      | apply MeasureTheory.Filtration.piLE.le
      | rfl))
