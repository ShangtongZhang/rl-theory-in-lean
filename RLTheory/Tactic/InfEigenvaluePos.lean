import Mathlib

/-- Given a `PosDef` matrix `h` in scope, proves that the infimum of its
    eigenvalues over `Finset.univ` is strictly positive.  Locates the
    minimising index via `Finset.exists_mem_eq_inf'` and closes the goal
    with `Matrix.PosDef.eigenvalues_pos`. --/
macro "inf_eigenvalue_pos" h:ident : tactic =>
  `(tactic|
    (obtain ⟨i__, _, hi__⟩ :=
       Finset.exists_mem_eq_inf' (s := Finset.univ) (by simp) $h.1.eigenvalues;
     have hep__ := Matrix.PosDef.eigenvalues_pos $h i__;
     rw [hi__];
     exact hep__))
