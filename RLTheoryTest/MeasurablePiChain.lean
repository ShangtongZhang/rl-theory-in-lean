import Mathlib
import RLTheory.Tactic.MeasurablePiChain

-- Demonstrates measurable_pi_chain on a two-level projection chain:
-- `fun x => x i j` where x : (i : ι) → (j : κ) → α i j
example {ι κ : Type*} {α : ι → κ → Type*} [∀ i j, MeasurableSpace (α i j)]
    (i : ι) (j : κ) :
    Measurable (fun x : (i : ι) → (j : κ) → α i j => x i j) := by
  measurable_pi_chain
