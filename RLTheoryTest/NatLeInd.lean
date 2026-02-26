import Mathlib
import RLTheory.Tactic.NatLeInd

-- Demonstrate nat_le_ind: prove n ≤ m from n ≤ m using le_induction
-- The motive is fun k _ => n ≤ k; base is n ≤ n; succ follows by le_succ_of_le
example (n m : ℕ) (h : n ≤ m) : n ≤ m := by
  nat_le_ind m h
  case base => exact Nat.le_refl n
  case succ =>
    intro k _hk ih
    exact Nat.le_succ_of_le ih
