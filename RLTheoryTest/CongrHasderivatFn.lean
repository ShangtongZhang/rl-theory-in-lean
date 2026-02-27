import Mathlib
import RLTheory.Tactic.CongrHasderivatFn

open Filter Topology

-- Demonstrate congr_hasDerivAt_fn: replace a function by an eventuallyEqual
-- one in a HasDerivAt goal. Here f =ᶠ[𝓝 x] id, so HasDerivAt f 1 x reduces
-- to HasDerivAt id 1 x which is closed by hasDerivAt_id.
example (x : ℝ) (f : ℝ → ℝ) (h : f =ᶠ[𝓝 x] id) : HasDerivAt f 1 x := by
  congr_hasDerivAt_fn
  exact hasDerivAt_id x
