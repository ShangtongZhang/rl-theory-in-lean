import Mathlib
import RLTheory.Tactic.CisupLeTac

-- Demonstrate that `ciSup_le_tac` reduces `⨆ i, f i ≤ c` to `f i ≤ c`
example (f : ℕ → ℝ) (c : ℝ) (h : ∀ i, f i ≤ c) : ⨆ i, f i ≤ c := by
  ciSup_le_tac
  exact h _
