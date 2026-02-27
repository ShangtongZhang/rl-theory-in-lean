import Mathlib
import RLTheory.Tactic.HasderivatZeroLittleo

-- hasDerivAt_zero_littleO reduces a `HasDerivAt f 0 x₀` goal to an ε-δ obligation.
-- We verify that the constant zero function has derivative 0 at any point.
example (x₀ : ℝ) : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x₀ := by
  hasDerivAt_zero_littleO
  rename_i c hc
  exact ⟨1, one_pos, fun y _ => by
    simp only [norm_zero]
    exact mul_nonneg (le_of_lt hc) (norm_nonneg _)⟩
