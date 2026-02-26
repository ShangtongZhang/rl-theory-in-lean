import Mathlib

open Lean Meta Elab Tactic in
/-- Finds a hypothesis of the form `∀ n ≥ n₀, P n` (or `∀ n ∈ Ico a b, P n`)
    in the local context and applies it to close the current goal, using
    `omega` or `linarith` to discharge the membership/inequality side-condition. -/
elab "forall_mem_ico_linarith" : tactic => do
  let goal ← getMainGoal
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    -- Only consider propositions that are universally quantified
    let ty ← instantiateMVars decl.type
    if !(← isProp ty) then continue
    if !ty.isForall then continue
    let s ← saveState
    let succeeded ← try
      evalTactic (← `(tactic| exact $(mkIdent decl.userName) _ (by first | omega | linarith | (simp only [Finset.mem_Ico, Finset.mem_range]; omega) | (simp only [Finset.mem_Ico, Finset.mem_range]; linarith))))
      pure true
    catch _ =>
      restoreState s
      pure false
    if succeeded then return
  throwTacticEx `forall_mem_ico_linarith goal "no matching universally-quantified hypothesis found"
