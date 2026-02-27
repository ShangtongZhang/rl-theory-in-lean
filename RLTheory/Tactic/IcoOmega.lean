import Mathlib

/-- `ico_omega` unfolds `Finset.mem_Ico`, `Set.mem_Ico`, and `Finset.mem_range`
    membership in all hypotheses and the goal, then calls `omega` to close
    the resulting linear arithmetic goal. -/
macro "ico_omega" : tactic =>
  `(tactic| (
    simp only [Finset.mem_Ico, Set.mem_Ico, Finset.mem_range,
               Finset.mem_univ, Finset.mem_filter] at *
    omega))
