import Mathlib
import RLTheory.Data.Matrix.Mul

/-- `symmetrize_dot` normalises goals containing `x ⬝ᵥ ((A + Aᵀ) *ᵥ x)` by unfolding
    `add_mulVec`, splitting `dotProduct_add`, and collapsing `dotProduct_transpose_mulVec`,
    optionally after clearing `star_trivial`. Works on the goal or a named hypothesis. -/
syntax "symmetrize_dot" : tactic
syntax "symmetrize_dot" "at" (Lean.Parser.Tactic.locationWildcard <|>
    Lean.Parser.Tactic.locationHyp) : tactic

macro_rules
  | `(tactic| symmetrize_dot) =>
    `(tactic|
      (try simp only [star_trivial];
       rw [Matrix.add_mulVec, Matrix.dotProduct_add,
           Matrix.dotProduct_transpose_mulVec]))
  | `(tactic| symmetrize_dot at $loc) =>
    `(tactic|
      (try simp only [star_trivial] at $loc;
       rw [Matrix.add_mulVec, Matrix.dotProduct_add,
           Matrix.dotProduct_transpose_mulVec] at $loc))
