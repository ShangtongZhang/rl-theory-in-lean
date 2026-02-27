import Mathlib

/-- `summable_tail_bound hs hε n₀ hn₀` destructs `hs : Summable f` into a threshold
    `n₀` (named by the user) and a hypothesis `hn₀ : ∀ n ≥ n₀, dist (f n) 0 < ε`,
    which after `simp [Real.dist_eq]` becomes `∀ n ≥ n₀, |f n| < ε`. -/
macro "summable_tail_bound" hs:term:max hε:term:max n₀:ident hn₀:ident : tactic =>
  `(tactic| obtain ⟨$n₀, $hn₀⟩ :=
      Metric.tendsto_atTop.mp (Summable.tendsto_atTop_zero $hs) _ $hε)
