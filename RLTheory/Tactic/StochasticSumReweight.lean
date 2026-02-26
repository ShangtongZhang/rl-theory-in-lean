import Mathlib
open Lean Meta Elab Tactic

/-- Rewrites C as (∑ i, w i) * C using the supplied rowsum proof h,
    then calls Finset.sum_le_sum.
    Usage:  stochastic_sum_reweight hμ.rowsum --/
elab "stochastic_sum_reweight" h:term : tactic => do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  -- Extract the RHS of `lhs ≤ C` (appArg! gives the last argument of the application)
  let rhs := goalType.appArg!
  let rhsStx ← Lean.PrettyPrinter.delab rhs
  -- Step 1: Rewrite C → 1 * C → (∑ i, w i) * C, scoped to the RHS only
  evalTactic (← `(tactic|
    conv_rhs =>
      rw [show $rhsStx = 1 * $rhsStx from (one_mul $rhsStx).symm, ← $h]))
  -- Step 2: Distribute (∑ i, w i) * C → ∑ i, w i * C
  evalTactic (← `(tactic| rw [Finset.sum_mul]))
  -- Step 3: Apply sum_le_sum to reduce to per-element bounds
  evalTactic (← `(tactic| apply Finset.sum_le_sum))
