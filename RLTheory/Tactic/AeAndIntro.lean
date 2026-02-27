import Mathlib

/-- `ae_and_intro h₁, h₂, … with x` combines `Filter.Eventually` hypotheses pairwise
    using `Filter.Eventually.and`, applies `Filter.Eventually.mono`, introduces the
    pointwise variable `x`, and destructs the resulting nested conjunction into
    individual hypotheses. -/
syntax "ae_and_intro" term,+ "with" ident : tactic

macro_rules
  | `(tactic| ae_and_intro $h:term with $x:ident) =>
    `(tactic| (apply Filter.Eventually.mono $h; intro $x _))
  | `(tactic| ae_and_intro $h1:term, $h2:term with $x:ident) =>
    `(tactic| (apply Filter.Eventually.mono (Filter.Eventually.and $h1 $h2);
               intro $x hω__; obtain ⟨_, _⟩ := hω__))
  | `(tactic| ae_and_intro $h1:term, $h2:term, $hs:term,* with $x:ident) => do
    let andExpr ← `(Filter.Eventually.and $h1 $h2)
    `(tactic| ae_and_intro $andExpr, $hs,* with $x)
