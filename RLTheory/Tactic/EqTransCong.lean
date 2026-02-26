import Mathlib

/-!
# `eq_trans_cong` tactic

Handles the recurring proof pattern:
```
apply Eq.trans
apply congrArg (a₂ := t)
```
by accepting an optional explicit intermediate term and rotating goals so the
congruence obligation becomes the current goal.
-/

syntax (name := eqTransCong) "eq_trans_cong" ("[" term "]")? : tactic

macro_rules
  | `(tactic| eq_trans_cong) =>
    `(tactic| (apply Eq.trans; apply congrArg; rotate_left))
  | `(tactic| eq_trans_cong [$t]) =>
    `(tactic| (apply Eq.trans; apply congrArg (a₂ := $t); rotate_left))
