import Mathlib
import RLTheory.Tactic.AeForallBound

-- Demonstrate ae_forall_bound: reduce an almost-sure forall goal to a pointwise inequality
example {α : Type*} {f : Filter α} (g : ℕ → α → ℝ) :
    ∀ᶠ ω in f, ∀ n, g n ω ≤ g n ω := by
  ae_forall_bound
  exact le_refl _
