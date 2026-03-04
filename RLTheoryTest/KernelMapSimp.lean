import Mathlib
import RLTheory.Tactic.KernelMapSimp

open ProbabilityTheory

-- Demonstrates kernel_map_simp: simplifies `κ.map id = κ` using Kernel.map_id
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) : κ.map id = κ := by
  kernel_map_simp
