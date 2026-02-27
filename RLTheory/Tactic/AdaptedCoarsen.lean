import Mathlib
import RLTheory.Tactic.FiltrationLe

open MeasureTheory

/-- `adapted_coarsen` closes `Measurable[ℱ j] (f i)` goals by finding either
    * a hypothesis `hf : Measurable[ℱ i] (f i)` and coarsening via `Measurable.mono`, or
    * a hypothesis `hf : Adapted ℱ f` and applying `Adapted.measurable_le`,
    in each case discharging the ordering side-condition with `filtration_le` / `omega`. -/
macro "adapted_coarsen" : tactic =>
  `(tactic| (
    first
    | (apply Adapted.measurable_le <;>
        first | assumption | filtration_le | omega | simp)
    | (apply Measurable.mono (hf := by assumption) (by filtration_le) le_rfl)
    | (apply Measurable.mono (hf := by assumption) (by apply Filtration.mono; omega) le_rfl)
    | (apply Measurable.mono (hf := by assumption) (by apply Filtration.mono; simp; omega) le_rfl)))
