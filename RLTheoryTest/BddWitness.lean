import Mathlib
import RLTheory.Tactic.BddWitness

-- Demonstrate `bdd_witness` on a concrete goal: find a nonneg bound C
-- such that C ≥ 3, using 5 as the witness (nonnegativity discharged automatically).
example : ∃ C : ℝ, 0 ≤ C ∧ C ≥ 3 := by
  bdd_witness 5
  norm_num
