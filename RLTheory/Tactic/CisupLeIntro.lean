import Mathlib

/-- `ciSup_le_intro x` reduces a goal `⨆ i, f i ≤ c` to `f x ≤ c` by applying
`ciSup_le` via `refine` with a lambda, introducing the index variable `x`.
If no variable name is given, the index is introduced anonymously. -/
syntax "ciSup_le_intro" (ppSpace ident)? : tactic

macro_rules
  | `(tactic| ciSup_le_intro $x:ident) =>
    `(tactic| refine ciSup_le (fun $x => ?_))
  | `(tactic| ciSup_le_intro) =>
    `(tactic| refine ciSup_le (fun _ => ?_))
