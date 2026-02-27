import Mathlib

/-- `lintegral_norm_to_integral` rewrites a goal or hypothesis containing
    `(∫⁻ ω, ‖f ω‖ₑ ∂μ).toReal` into `∫ ω, ‖f ω‖ ∂μ` using
    `MeasureTheory.integral_norm_eq_lintegral_enorm`, and normalises `‖·‖`
    to `|·|` for real-valued functions. -/
syntax "lintegral_norm_to_integral" : tactic
syntax "lintegral_norm_to_integral" "at"
    (Lean.Parser.Tactic.locationWildcard <|> Lean.Parser.Tactic.locationHyp) : tactic

macro_rules
  | `(tactic| lintegral_norm_to_integral) =>
    `(tactic| (rw [←MeasureTheory.integral_norm_eq_lintegral_enorm (by assumption)]
               try simp only [Real.norm_eq_abs]))
  | `(tactic| lintegral_norm_to_integral at $loc) =>
    `(tactic| (rw [←MeasureTheory.integral_norm_eq_lintegral_enorm (by assumption)] at $loc
               try simp only [Real.norm_eq_abs] at $loc))
