import Mathlib

-- A curated simp set that normalises norm/abs expressions involving scalar multiplication.
-- Collects norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg, abs_of_pos,
-- inner_sub_right, inner_sub_left, and sub_sub_sub_comm so that callers need not
-- spell out every lemma individually.

macro "smul_norm_simp" : tactic =>
  `(tactic| simp only [norm_smul, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg, abs_of_pos,
      abs_real_inner_le_norm, inner_sub_right, inner_sub_left,
      sub_sub_sub_comm])
