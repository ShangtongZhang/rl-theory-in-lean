import Mathlib
import RLTheory.Tactic.EqTransCong

-- Demonstrate `eq_trans_cong`: proves f a = f c given a = b and b = c.
-- After `eq_trans_cong [b]` the goals are (1) f b = f c  (2) a = b.
example (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : b = c) : f a = f c := by
  eq_trans_cong [b]
  · exact congrArg f h2
  · exact h1
