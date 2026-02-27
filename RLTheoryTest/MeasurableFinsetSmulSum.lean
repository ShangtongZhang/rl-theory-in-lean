import Mathlib
import RLTheory.Tactic.MeasurableFinsetSmulSum

-- Demonstrates measurable_finset_smul_sum on a two-level finset sum with scalar:
-- `fun w => ∑ s ∈ S, ∑ s' ∈ S, c s s' • w`
-- The tactic peels off both sums and the scalar, leaving `Measurable id`.
example (S : Finset ℕ) (c : ℕ → ℕ → ℝ) :
    Measurable (fun w : ℝ => ∑ s ∈ S, ∑ s' ∈ S, c s s' • w) := by
  measurable_finset_smul_sum
  exact measurable_id
