import Mathlib
import RLTheory.Tactic.TendstoSumGeOfLe

open Finset Filter

-- Demonstrate `tendsto_sum_ge_of_le`: if the partial sums of f diverge to +∞
-- and f ≤ g pointwise (with g nonneg), then the partial sums of g also diverge to +∞.
example (f g : ℕ → ℝ)
    (hf : Tendsto (fun n => ∑ i ∈ range n, f i) atTop atTop)
    (hle : ∀ n, f n ≤ g n)
    (hg : ∀ n, 0 ≤ g n) :
    Tendsto (fun n => ∑ i ∈ range n, g i) atTop atTop := by
  tendsto_sum_ge_of_le
