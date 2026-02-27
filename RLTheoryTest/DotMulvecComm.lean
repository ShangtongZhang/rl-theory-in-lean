import Mathlib
import RLTheory.Tactic.DotMulvecComm

open Matrix

-- Demonstrate dot_mulvec_comm: normalise (A *ᵥ y) ⬝ᵥ x to (x ᵥ* A) ⬝ᵥ y
example {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x y : n → ℝ) :
    (A *ᵥ y) ⬝ᵥ x = (x ᵥ* A) ⬝ᵥ y := by
  dot_mulvec_comm
