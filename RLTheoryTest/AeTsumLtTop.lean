import Mathlib
import RLTheory.Tactic.AeTsumLtTop

open MeasureTheory ENNReal

-- Demonstrate ae_tsum_lt_top: for a summable NNReal sequence seen as ENNReal
-- constants, the tsum is a.e. finite w.r.t. any probability measure.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : ℕ → NNReal) (hc : Summable c) :
    ∀ᵐ ω ∂μ, ∑' n, (c n : ENNReal) < ⊤ := by
  ae_tsum_lt_top using hc
