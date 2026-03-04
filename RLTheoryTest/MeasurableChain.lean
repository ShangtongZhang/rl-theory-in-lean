import Mathlib
import RLTheory.Tactic.MeasurableChain

-- Demonstrate measurable_chain: close a Measurable goal for a composition chain
example {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (f : β → γ) (g : α → β) (hf : Measurable f) (hg : Measurable g) :
    Measurable (f ∘ g) := by
  measurable_chain
