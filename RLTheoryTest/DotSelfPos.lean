import Mathlib
import RLTheory.Tactic.DotSelfPos

-- Demonstrate `dot_self_pos` on a concrete dot-product goal:
-- given a nonzero real vector x, prove 0 < x ⬝ᵥ x.
example (n : ℕ) (x : Fin n → ℝ) (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  dot_self_pos
