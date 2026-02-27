import Mathlib
import RLTheory.Tactic.MatrixInvertibleOfPosDefAsymm

open Matrix

noncomputable example {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) [PosDefAsymm A] : Invertible A := by
  matrix_invertible_of_pos_def_asymm
