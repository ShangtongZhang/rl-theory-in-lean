import Mathlib
import RLTheory.Tactic.IntegralCongrPointwise

open MeasureTheory

-- Demonstrate integral_congr_pointwise: reduce an integral equality to a pointwise equality
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω, f ω = g ω) :
    ∫ ω, f ω ∂μ = ∫ ω, g ω ∂μ := by
  integral_congr_pointwise ω
  exact hfg ω
