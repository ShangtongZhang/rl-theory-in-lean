import Mathlib

/-- `ae_of_all` closes an `f =ᵐ[μ] g` goal by applying
    `Filter.Eventually.of_forall`, introducing the pointwise variable,
    then dispatching the resulting `f x = g x` goal with
    `rfl`, `ring`, `simp_all`, or `simp` in sequence. -/
macro "ae_of_all" : tactic =>
  `(tactic| (apply Filter.Eventually.of_forall; intro _ae_x;
             first | rfl | ring | simp_all | simp))
