import Mathlib

/-- `ae_tsum_lt_top` closes goals of the form `∀ᵐ ω ∂μ, ∑' n, g n ω < ⊤`
    for non-negative `g` by applying `MeasureTheory.ae_lt_top`,
    discharging the measurability sub-goal via `Measurable.ennreal_tsum`,
    and closing the lintegral finiteness sub-goal by rewriting with
    `lintegral_tsum` and using `ENNReal.tsum_coe_ne_top_iff_summable`. -/
syntax "ae_tsum_lt_top" (" using " term)? : tactic

macro_rules
  | `(tactic| ae_tsum_lt_top) =>
    `(tactic| (apply MeasureTheory.ae_lt_top
               case hf =>
                 apply Measurable.ennreal_tsum
                 intro; fun_prop
               case h2f =>
                 rw [MeasureTheory.lintegral_tsum (by intro; fun_prop)]
                 apply ENNReal.tsum_coe_ne_top_iff_summable.mpr
                 assumption))
  | `(tactic| ae_tsum_lt_top using $hsum:term) =>
    `(tactic| (apply MeasureTheory.ae_lt_top
               case hf =>
                 apply Measurable.ennreal_tsum
                 intro; fun_prop
               case h2f =>
                 rw [MeasureTheory.lintegral_tsum (by intro; fun_prop)]
                 simp only [MeasureTheory.lintegral_const, MeasureTheory.measure_univ,
                             mul_one]
                 exact ENNReal.tsum_coe_ne_top_iff_summable.mpr $hsum))
