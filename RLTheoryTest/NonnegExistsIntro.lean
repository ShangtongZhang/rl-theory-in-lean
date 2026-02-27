import Mathlib
import RLTheory.Tactic.NonnegExistsIntro

-- Demonstrate `nonneg_exists_intro` on a concrete goal: find a nonneg C
-- such that C ≥ 3, using 5 as the witness (nonnegativity discharged automatically).
example : ∃ C : ℝ, 0 ≤ C ∧ C ≥ 3 := by
  nonneg_exists_intro 5
  norm_num
