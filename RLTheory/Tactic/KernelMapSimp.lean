import Mathlib
import RLTheory.Probability.Kernel.Composition.MapComap

/-- Simp macro: normalize `ProbabilityTheory.Kernel` map/composition expressions.
    Simplifies goals involving `map_comp`, `map_comp_right`, identity kernel laws,
    and projection maps for product kernels. -/
macro "kernel_map_simp" : tactic =>
  `(tactic|
    simp only [
      ProbabilityTheory.Kernel.map_comp,
      ProbabilityTheory.Kernel.map_comp_right,
      ProbabilityTheory.Kernel.id_comp,
      ProbabilityTheory.Kernel.comp_id,
      ProbabilityTheory.Kernel.map_id,
      ProbabilityTheory.Kernel.prod_map_fst,
      ProbabilityTheory.Kernel.prod_map_snd,
      Function.comp_assoc
    ])
