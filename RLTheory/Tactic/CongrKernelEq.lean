import Mathlib

open Lean Elab Tactic in
macro "congr_kernel_eq" : tactic =>
  `(tactic|
      (ext
       first | rfl | simp_all
       first | rfl | assumption | ring))
