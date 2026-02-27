import Mathlib
import RLTheory.Tactic.LintegralNormToIntegral

-- one example that uses `lintegral_norm_to_integral` as a proof step
example {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (f : Ω → ℝ) (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (h : ∫ ω, ‖f ω‖ ∂μ ≤ 1) : (∫⁻ ω, ‖f ω‖ₑ ∂μ).toReal ≤ 1 := by
  lintegral_norm_to_integral
  exact h
