import Mathlib

open Lean Meta Elab Tactic in

/-- `congr_hasDerivAt_fn` looks for a hypothesis `h : f =ᶠ[𝓝 x] g` in the
    local context and rewrites a `HasDerivAt f f' x` goal to
    `HasDerivAt g f' x` (or vice-versa) via
    `HasDerivAt.congr_of_eventuallyEq`. -/
elab "congr_hasDerivAt_fn" : tactic => do
  let goal ← getMainGoal
  let goalTy ← instantiateMVars (← goal.getType)
  -- Expect goal shape: HasDerivAt ?f ?f' ?x
  unless goalTy.isAppOf ``HasDerivAt do
    throwTacticEx `congr_hasDerivAt_fn goal "goal is not HasDerivAt"
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    -- Check if hyp is EventuallyEq at nhds
    if ty.isAppOf ``Filter.EventuallyEq then
      let s ← saveState
      let hyp := mkIdent decl.userName
      let succeeded ← try
        evalTactic (← `(tactic|
          apply HasDerivAt.congr_of_eventuallyEq (h₁ := $hyp)))
        pure true
      catch _ =>
        s.restore
        try
          evalTactic (← `(tactic|
            apply HasDerivAt.congr_of_eventuallyEq (h₁ := $hyp |>.symm)))
          pure true
        catch _ => s.restore; pure false
      if succeeded then return
  throwTacticEx `congr_hasDerivAt_fn goal
    "no suitable EventuallyEq hypothesis found"
