import Mathlib

/-- `ico_sum_split b` rewrites `∑ i ∈ Finset.Ico a c, f i` by splitting at midpoint `b`,
    applying `←Ico_union_Ico_eq_Ico` and `sum_union`, then automatically discharging
    the `Disjoint` side-goal via `Ico_disjoint_Ico_consecutive` and the bound goals via `omega`. -/
syntax "ico_sum_split" (ppSpace term)? : tactic

macro_rules
  | `(tactic| ico_sum_split $b) =>
    `(tactic| (
        rw [← Finset.Ico_union_Ico_eq_Ico (b := $b), Finset.sum_union]
        all_goals (try (first | exact Finset.Ico_disjoint_Ico_consecutive _ _ _ | omega))))
  | `(tactic| ico_sum_split) =>
    `(tactic| (
        rw [← Finset.Ico_union_Ico_eq_Ico, Finset.sum_union]
        all_goals (try (first | exact Finset.Ico_disjoint_Ico_consecutive _ _ _ | omega))))
