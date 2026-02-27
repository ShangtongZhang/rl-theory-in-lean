import Mathlib

/-- `ae_forall_bound` reduces `∀ᵐ ω ∂μ, ∀ n, P n ω` to a pointwise goal
    by applying `Eventually.of_forall` and introducing both `ω` and `n`.
    If a hypothesis `h : ∀ᵐ ω ∂μ, Q ω` is provided via `using h`, it
    instead uses `Eventually.mono h` to transfer the almost-sure assumption. -/
syntax "ae_forall_bound" (" using " term)? : tactic

macro_rules
  | `(tactic| ae_forall_bound) =>
    `(tactic| (apply Filter.Eventually.of_forall; intro _ _))
  | `(tactic| ae_forall_bound using $h) =>
    `(tactic| (apply Filter.Eventually.mono $h; intro _ _))
