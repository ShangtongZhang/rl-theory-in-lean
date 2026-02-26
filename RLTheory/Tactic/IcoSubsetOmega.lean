import Mathlib

macro "ico_subset_omega" : tactic =>
  `(tactic| first
    | (apply Finset.Ico_subset_Ico_right; omega)
    | (apply Finset.Ico_subset_Ico_left; omega)
    | (apply Finset.Ico_subset_Ico <;> omega)
    | (simp only [Finset.Ico_subset_Ico_iff] <;> omega))
