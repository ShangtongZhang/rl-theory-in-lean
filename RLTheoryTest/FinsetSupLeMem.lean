import Mathlib
import RLTheory.Tactic.FinsetSupLeMem

-- Demonstrate that `finset_sup_le_mem` reduces `c ≤ s.sup' hs f` to `c ≤ f j`
-- given a membership witness `hj : j ∈ s` in the local context.
example (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℕ) (j : ℕ) (hj : j ∈ s)
    (c : ℕ) (hcj : c ≤ f j) : c ≤ s.sup' hs f := by
  finset_sup_le_mem
  exact hcj
