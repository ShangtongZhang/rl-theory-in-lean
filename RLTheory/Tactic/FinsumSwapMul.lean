import Mathlib

/-- `finsum_swap_mul` rewrites a double finite sum `∑ i, ∑ j, f i * g i j` into
    `∑ i, f i * (∑ j, g i j)`, or exchanges summation order via `Finset.sum_comm`
    and then pulls the scalar outside with `Finset.mul_sum` / `Finset.sum_mul`. -/
macro "finsum_swap_mul" : tactic =>
  `(tactic|
    (first
     | (simp only [← Finset.mul_sum, ← Finset.sum_mul])
     | (rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, ← Finset.sum_mul])
     | (simp only [← Finset.mul_sum, ← Finset.sum_mul]
        rw [Finset.sum_comm])
     | (conv_lhs =>
          arg 2; ext i
          rw [← Finset.mul_sum])
     | (conv_lhs =>
          rw [Finset.sum_comm]
          arg 2; ext i
          rw [← Finset.mul_sum])))
