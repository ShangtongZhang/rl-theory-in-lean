import Mathlib
import RLTheory.Tactic.InfEigenvaluePos

-- one example that uses `inf_eigenvalue_pos` as a proof step
example (A : Matrix (Fin 2) (Fin 2) ℝ) (h : Matrix.PosDef A) :
    0 < (Finset.univ : Finset (Fin 2)).inf' (by simp) h.1.eigenvalues := by
  inf_eigenvalue_pos h
