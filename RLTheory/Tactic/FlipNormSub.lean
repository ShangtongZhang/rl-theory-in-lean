import Mathlib

/-- `flip_norm_sub a b` rewrites `‖a - b‖` to `‖b - a‖` everywhere in the
    goal using `norm_sub_rev`. -/
syntax "flip_norm_sub" term "," term : tactic

macro_rules
  | `(tactic| flip_norm_sub $a:term , $b:term) =>
    `(tactic| simp only [show ‖$a - $b‖ = ‖$b - $a‖ from norm_sub_rev $a $b])
