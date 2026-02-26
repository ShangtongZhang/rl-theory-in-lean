import Mathlib
import RLTheory.Tactic.ForallMemIcoLinarith

-- one example that uses `forall_mem_ico_linarith` as a proof step
example (f : ℕ → ℝ) (h : ∀ n ≥ 5, f n ≥ 0) : f 7 ≥ 0 := by
  forall_mem_ico_linarith
