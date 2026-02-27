import Mathlib
import RLTheory.Tactic.NormSqInnerSimp

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Demonstrate norm_sq_inner_simp converting ‖x‖^2 to the real inner product ⟪x, x⟫_ℝ
example (x : E) : ‖x‖ ^ 2 = @inner ℝ E _ x x := by
  norm_sq_inner_simp
