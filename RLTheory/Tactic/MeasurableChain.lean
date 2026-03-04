import Mathlib

/-- `measurable_chain` handles `Measurable f` goals where `f` is a function composition
    or projection chain, by repeatedly trying `Measurable.comp`, `measurable_pi_apply`,
    `Measurable.fst`, `Measurable.snd`, and `measurability` to discharge each
    sub-component automatically. -/
macro "measurable_chain" : tactic =>
  `(tactic|
    repeat (
      first
      | assumption
      | apply Measurable.comp
      | apply measurable_pi_apply
      | apply Measurable.fst
      | apply Measurable.snd
      | measurability
      | apply measurable_id
    ))
