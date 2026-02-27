import Mathlib

/-- `dot_mulvec_comm` normalises goals containing `dotProduct` and `mulVec`/`vecMul`
    by applying `dotProduct_comm` and `Matrix.dotProduct_mulVec` in a fixed canonical
    order so that all `dotProduct` calls have the row-vector on the left,
    eliminating the need to manually pick the right commutativity lemma each time. -/
macro "dot_mulvec_comm" : tactic =>
  `(tactic| (
    simp only [
      Matrix.dotProduct_mulVec,
      dotProduct_comm]
    try ring_nf))
