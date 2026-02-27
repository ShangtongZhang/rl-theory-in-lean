import Mathlib

open Finset Filter

/-- Proves `Tendsto (fun n => ∑ i ∈ range n, g i) atTop atTop` from a hypothesis
    `Tendsto (fun n => ∑ i ∈ range n, f i) atTop atTop` and a pointwise bound `∀ n, f n ≤ g n`,
    by unfolding via `Filter.tendsto_atTop_atTop` and applying `Finset.sum_le_sum`. --/
macro "tendsto_sum_ge_of_le" : tactic =>
  `(tactic| (
      apply Filter.tendsto_atTop_atTop.mpr
      intro b
      obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp
        (by assumption : Tendsto _ atTop atTop)) b
      refine ⟨N, fun n hn => le_trans (hN n hn) ?_⟩
      apply Finset.sum_le_sum
      intro i _
      first | assumption | solve_by_elim | linarith))
