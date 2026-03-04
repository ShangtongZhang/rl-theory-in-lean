import Mathlib

open Lean Elab Tactic

/-- `nonneg_combo` recursively decomposes a `0 ≤ e` goal using
    `add_nonneg`, `mul_nonneg`, and `sum_nonneg`, then closes
    atomic subgoals via `positivity`, `linarith`, or `assumption`
    after simplifying any Finset membership hypotheses. -/
partial def nonnegComboCore (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then
    evalTactic (← `(tactic| first | positivity | linarith | assumption))
    return
  -- Try add_nonneg
  try
    evalTactic (← `(tactic| apply add_nonneg))
    nonnegComboCore (fuel - 1)
    nonnegComboCore (fuel - 1)
    return
  catch _ => pure ()
  -- Match sum_nonneg shape: 0 ≤ ∑ i ∈ s, f i
  try
    evalTactic (← `(tactic| apply Finset.sum_nonneg))
    evalTactic (← `(tactic| intro _nc_i _nc_hi))
    evalTactic (← `(tactic| simp only [Finset.mem_Ico, Finset.mem_range, Finset.mem_Icc] at _nc_hi))
    nonnegComboCore (fuel - 1)
    return
  catch _ => pure ()
  -- Try mul_nonneg
  try
    evalTactic (← `(tactic| apply mul_nonneg))
    nonnegComboCore (fuel - 1)
    nonnegComboCore (fuel - 1)
    return
  catch _ => pure ()
  -- Leaf: use positivity / linarith / assumption
  evalTactic (← `(tactic| first | positivity | linarith | assumption | simpa))

elab "nonneg_combo" : tactic => nonnegComboCore 8
