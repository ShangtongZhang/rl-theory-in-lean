import Mathlib

/-- `filtration_le` closes goals of the form `ℱ i ≤ ℱ j` by combining
    `Filtration.mono` / `Filtration.le` with `omega` or `simp` to discharge
    the index ordering side-condition. -/
macro "filtration_le" : tactic =>
  `(tactic| first
    | assumption
    | exact le_rfl
    | (apply MeasureTheory.Filtration.le)
    | (apply MeasureTheory.Filtration.mono; omega)
    | (apply MeasureTheory.Filtration.mono; simp; omega)
    | (apply MeasureTheory.Filtration.mono; simp)
    | (apply MeasureTheory.Filtration.mono; norm_num))
