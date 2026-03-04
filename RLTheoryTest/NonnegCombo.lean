import Mathlib
import RLTheory.Tactic.NonnegCombo

open Finset

-- Basic: nested addition
example (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 0 ≤ x + (y + z) := by
  nonneg_combo

-- Sum of natural number casts is nonneg
example (n : ℕ) : 0 ≤ ∑ i ∈ Finset.Ico 0 n, (i : ℝ) := by
  nonneg_combo

-- Mix of addition and sum
example (n : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x + ∑ i ∈ Finset.Ico 0 n, (i : ℝ) := by
  nonneg_combo

-- Multiplication of nonneg terms
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  nonneg_combo
