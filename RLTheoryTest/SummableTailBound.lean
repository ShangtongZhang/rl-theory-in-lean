import Mathlib
import RLTheory.Tactic.SummableTailBound

-- Demonstrate summable_tail_bound: given a summable sequence f and ε > 0,
-- we can find n₀ such that for all n ≥ n₀, |f n| < ε
example (f : ℕ → ℝ) (hf : Summable f) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, |f n| < ε := by
  summable_tail_bound hf hε n₀ hn₀
  simp only [Real.dist_eq, sub_zero] at hn₀
  exact ⟨n₀, hn₀⟩
