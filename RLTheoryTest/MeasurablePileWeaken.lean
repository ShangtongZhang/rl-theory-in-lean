import Mathlib
import RLTheory.Tactic.MeasurablePileWeaken

open MeasureTheory.Filtration

-- Demonstrates measurable_piLE_weaken: if f is measurable at level piLE m,
-- and m ≤ n, then f is measurable at the coarser level piLE n.
example {n m : ℕ} (h : m ≤ n) (f : (ℕ → ℕ) → ℕ)
    (hf : Measurable[piLE m] f) :
    Measurable[piLE n] f := by
  measurable_piLE_weaken
