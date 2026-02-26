import Mathlib
import RLTheory.Tactic.IcoSubsetOmega

-- one example that uses `ico_subset_omega` as a proof step
example : Finset.Ico 2 5 ⊆ Finset.Ico 2 10 := by
  ico_subset_omega
