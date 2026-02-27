import Mathlib
import RLTheory.Tactic.IcoOmega

-- one example that uses `ico_omega` as a proof step
example (n : ℕ) (h : n ∈ Finset.Ico 3 10) : n < 10 := by
  ico_omega
