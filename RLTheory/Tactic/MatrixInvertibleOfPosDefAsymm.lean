import Mathlib
import RLTheory.Data.Matrix.PosDef

/-- Closes `Invertible A` goals when a `PosDefAsymm A` instance is in scope,
    by reducing to a kernel-triviality argument. -/
macro "matrix_invertible_of_pos_def_asymm" : tactic =>
  `(tactic|
    (apply IsUnit.invertible;
     apply Matrix.isUnit_toLin'_iff.mp;
     apply (LinearMap.isUnit_iff_ker_eq_bot (Matrix.toLin' _)).mpr;
     apply Matrix.ker_toLin'_eq_bot_iff.mpr;
     intro x hx;
     by_contra hne;
     have hpos := Matrix.PosDefAsymm.pd x hne;
     rw [hx] at hpos;
     simp at hpos))
