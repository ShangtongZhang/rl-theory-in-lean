import Mathlib
import RLTheory.Tactic.AdaptedCoarsen

open MeasureTheory

-- Example 1: `adapted_coarsen` proves `Measurable[ℱ (n + 1)] f` from `Measurable[ℱ n] f`
-- by applying `Measurable.mono` and discharging the ordering `ℱ n ≤ ℱ (n + 1)` via `filtration_le`.
example {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℕ ‹_›)
    (f : Ω → ℝ) (n : ℕ) (hf : Measurable[ℱ n] f) : Measurable[ℱ (n + 1)] f := by
  adapted_coarsen

-- Example 2: `adapted_coarsen` proves `Measurable[ℱ (n + 1)] (f n)` from `Adapted ℱ f`
-- by applying `Adapted.measurable_le` and discharging `n ≤ n + 1` via `omega`.
example {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℕ ‹_›)
    {E : Type*} [MeasurableSpace E] (f : ℕ → Ω → E)
    (hf : Adapted ℱ f) (n : ℕ) : Measurable[ℱ (n + 1)] (f n) := by
  adapted_coarsen
