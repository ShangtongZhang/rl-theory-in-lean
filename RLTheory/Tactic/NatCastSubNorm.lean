import Mathlib

/-!
# `nat_cast_sub_norm` tactic

Normalises expressions of the form `(↑(n - k) : R)` (natural-number subtraction cast to a ring)
into `↑n - ↑k` by applying `Nat.cast_sub` with the side condition discharged by `omega`,
then calls `push_cast` and `ring_nf` to finish normalisation.
-/

/-- `nat_cast_sub_norm` rewrites every `(↑(a - b) : R)` subterm where
    `b ≤ a` is dischargeable by `omega` into `↑a - ↑b`, then calls
    `push_cast` and `ring_nf` to normalise the result. -/
macro "nat_cast_sub_norm" : tactic =>
  `(tactic| (
      simp only [Nat.cast_sub (by omega)]
      push_cast
      try ring_nf))
