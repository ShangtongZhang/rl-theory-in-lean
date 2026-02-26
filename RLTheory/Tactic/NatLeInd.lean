import Mathlib

/-!
# `nat_le_ind` tactic

Sets up a proof by `Nat.le_induction` given an upper bound term and a proof that `n ≤ upper`,
automatically opening the `base` and `succ` subgoals.
-/

macro "nat_le_ind" upper:term:max hyp:term:max : tactic =>
  `(tactic| refine Nat.le_induction ?base ?succ $upper $hyp)
