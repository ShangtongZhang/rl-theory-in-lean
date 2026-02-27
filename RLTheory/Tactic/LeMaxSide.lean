import Mathlib

/-- `le_max_side` closes goals of the form `x ≤ max A B` (possibly nested)
    by searching through combinations of `le_max_left` and `le_max_right`
    up to depth 3. -/
macro "le_max_side" : tactic =>
  `(tactic|
    first
    | exact le_max_left _ _
    | exact le_max_right _ _
    | exact le_trans (le_max_left _ _) (le_max_left _ _)
    | exact le_trans (le_max_left _ _) (le_max_right _ _)
    | exact le_trans (le_max_right _ _) (le_max_left _ _)
    | exact le_trans (le_max_right _ _) (le_max_right _ _)
    | exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    | exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
    | exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
    | exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    | exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    | exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
    | exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
    | exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
