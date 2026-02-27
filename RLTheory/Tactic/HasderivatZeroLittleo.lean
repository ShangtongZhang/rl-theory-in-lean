import Mathlib

/-- `hasDerivAt_zero_littleO` unfolds a `HasDerivAt f 0 x₀` goal into a
    concrete ε-δ statement via `hasDerivAt_iff_isLittleO` and
    `Metric.eventually_nhds_iff`, leaving the user to supply a radius and
    bound the function. -/
macro "hasDerivAt_zero_littleO" : tactic =>
  `(tactic| (
      apply hasDerivAt_iff_isLittleO.mpr
      simp only [smul_zero, sub_zero, zero_add]
      apply Asymptotics.isLittleO_iff.mpr
      intro c hc
      apply Metric.eventually_nhds_iff.mpr
      simp only [dist_eq_norm]))
