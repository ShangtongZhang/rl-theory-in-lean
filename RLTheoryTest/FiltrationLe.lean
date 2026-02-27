import Mathlib
import RLTheory.Tactic.FiltrationLe

-- one example that uses `filtration_le` as a proof step
example {Ω : Type*} [MeasurableSpace Ω] (ℱ : MeasureTheory.Filtration ℕ ‹_›)
    (i j : ℕ) (h : i ≤ j) : ℱ i ≤ ℱ j := by
  filtration_le
