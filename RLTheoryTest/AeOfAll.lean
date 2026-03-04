import Mathlib
import RLTheory.Tactic.AeOfAll

-- Demonstrate ae_of_all: close an ae-equality goal by pointwise ring equality
example (μ : MeasureTheory.Measure ℝ) :
    (fun x : ℝ => x + 1) =ᵐ[μ] (fun x : ℝ => 1 + x) := by
  ae_of_all
