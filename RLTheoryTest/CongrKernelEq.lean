import Mathlib
import RLTheory.Tactic.CongrKernelEq

open MeasureTheory ProbabilityTheory

-- Test that congr_kernel_eq can prove a trivial kernel equality
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : ProbabilityTheory.Kernel α β) : κ = κ := by
  congr_kernel_eq
