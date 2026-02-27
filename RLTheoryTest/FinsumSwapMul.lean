import Mathlib
import RLTheory.Tactic.FinsumSwapMul

open scoped BigOperators

-- Demonstrates finsum_swap_mul: rewrites ∑ i, ∑ j, f i * g i j into ∑ i, f i * ∑ j, g i j
example {α β : Type*} [Fintype α] [Fintype β] (f : α → ℝ) (g : α → β → ℝ) :
    ∑ i : α, ∑ j : β, f i * g i j = ∑ i : α, f i * ∑ j : β, g i j := by
  finsum_swap_mul
