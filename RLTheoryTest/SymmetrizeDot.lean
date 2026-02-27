import Mathlib
import RLTheory.Tactic.SymmetrizeDot

open Matrix

-- Demonstrate symmetrize_dot: normalise x ⬝ᵥ ((A + Aᵀ) *ᵥ x) and close the goal
example {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x : n → ℝ)
    (h : 0 < x ⬝ᵥ (A *ᵥ x)) : 0 < x ⬝ᵥ ((A + Aᵀ) *ᵥ x) := by
  symmetrize_dot
  linarith
