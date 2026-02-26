import Mathlib
import RLTheory.Tactic.NormSumIntro

-- Demonstrates norm_sum_intro: reduces ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖
-- to per-element goals by chaining norm_sum_le and sum_le_sum.
example (f : Fin 3 → ℝ) (s : Finset (Fin 3)) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := by
  norm_sum_intro
  exact le_refl _
