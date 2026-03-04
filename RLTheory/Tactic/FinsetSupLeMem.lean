import Mathlib

/-- Given a goal `c ≤ s.sup' hs f`, rewrites to `∃ b ∈ s, c ≤ f b` via
    `Finset.le_sup'_iff`, then introduces a witness using a membership hypothesis
    from the local context (or `Finset.mem_univ` / `simp`), leaving the single
    subgoal `c ≤ f b`. -/
macro "finset_sup_le_mem" : tactic =>
  `(tactic|
    (rw [Finset.le_sup'_iff]
     first
     | refine ⟨?_, by assumption, ?_⟩
     | refine ⟨?_, Finset.mem_univ _, ?_⟩
     | refine ⟨?_, by simp, ?_⟩))
