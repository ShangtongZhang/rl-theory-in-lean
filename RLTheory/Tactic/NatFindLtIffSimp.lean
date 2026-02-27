import Mathlib

/-- `nat_find_lt_iff_simp` simplifies goals and hypotheses involving `Nat.find`
    by applying `Nat.find_spec`, `Nat.le_find_iff`, `Nat.find_eq_iff`, and `omega`.
    It first tries to close the goal directly via `exact Nat.find_spec ‹_›`,
    then falls back to unfolding with simp followed by `omega`. -/
macro "nat_find_lt_iff_simp" : tactic =>
  `(tactic| first
    | exact Nat.find_spec ‹_›
    | (simp only [Nat.le_find_iff, Nat.find_eq_iff] at * <;> omega)
    | (simp only [Nat.find_spec, Nat.le_find_iff, Nat.find_eq_iff] at * <;> try omega))
