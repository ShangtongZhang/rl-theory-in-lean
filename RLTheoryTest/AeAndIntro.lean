import Mathlib
import RLTheory.Tactic.AeAndIntro

-- Demonstrate ae_and_intro: combine two Filter.Eventually hypotheses and destruct the conjunction
example {α : Type*} {f : Filter α} {p q : α → Prop}
    (hp : ∀ᶠ x in f, p x) (hq : ∀ᶠ x in f, q x) :
    ∀ᶠ x in f, p x ∧ q x := by
  ae_and_intro hp, hq with ω
  exact ⟨by assumption, by assumption⟩
