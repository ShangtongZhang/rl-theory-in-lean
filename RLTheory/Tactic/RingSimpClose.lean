import Mathlib

/-- `ring_simp_close` closes equality or weak-inequality goals that become trivial
    after alternating `simp` and `ring_nf` passes, optionally first reducing a `≤`
    goal to `=` via `le_of_eq`. The tactic tries several orderings of these
    combinators (including `ring` and `linarith`) so the user need not know which
    one works. --/
macro "ring_simp_close" : tactic =>
  `(tactic| first
    | rfl
    | ring
    | linarith
    | (apply le_of_eq; rfl)
    | (apply le_of_eq; ring)
    | (apply le_of_eq; simp; ring_nf; simp)
    | (apply le_of_eq; ring_nf; simp)
    | (apply le_of_eq; simp)
    | (simp; ring_nf; simp)
    | (ring_nf; linarith)
    | (ring_nf; simp))
