import Mathlib
import RLTheory.Tactic.IntegrableBddMeasurable

-- Demonstrate `integrable_bdd_measurable` on a concrete instance:
-- a measurable real-valued function bounded AE by a constant C is integrable
-- on a probability space.
example {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ)
    (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C) :
    MeasureTheory.Integrable f μ := by
  integrable_bdd_measurable
