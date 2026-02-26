import Mathlib

-- Declare the syntax first so the recursive reference in macro_rules is valid.
syntax "measurable_pi_chain" : tactic

macro_rules
  | `(tactic| measurable_pi_chain) =>
    `(tactic| (
        first
        | apply Measurable.aemeasurable; measurable_pi_chain
        | (repeat (apply measurable_pi_apply)); measurability
        | measurability))
