import Mathlib

/-- `obtain_bound h as C, hnn, hb` destructs a hypothesis `h : ∃ C, 0 ≤ C ∧ P C`
    into named components `C`, `hnn : 0 ≤ C`, `hb : P C`, and immediately
    provides `C` and `hnn` as the existential witness and nonnegativity proof for
    the current goal `∃ C, 0 ≤ C ∧ Q C`, leaving only `Q C` as the remaining
    obligation.

    The unnamed form `obtain_bound h` uses auto-generated names `C_auto`,
    `h_nn_auto`, `h_bd_auto`. --/
syntax "obtain_bound" term (" as " ident " , " ident " , " ident)? : tactic

macro_rules
  | `(tactic| obtain_bound $h as $C , $hnn , $hb) =>
    `(tactic| (obtain ⟨$C, $hnn, $hb⟩ := $h; refine ⟨$C, $hnn, ?_⟩))
  | `(tactic| obtain_bound $h) =>
    `(tactic| (obtain ⟨C_auto, h_nn_auto, h_bd_auto⟩ := $h
               refine ⟨C_auto, h_nn_auto, ?_⟩))
