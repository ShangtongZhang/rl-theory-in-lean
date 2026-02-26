import Mathlib
import RLTheory.Tactic.KernelSimp

open ProbabilityTheory

-- Demonstrate kernel_simp: map with identity function simplifies to identity kernel
example {α : Type*} [MeasurableSpace α] (κ : Kernel α α) :
    κ.map id = κ := by
  kernel_simp
