import Mathlib
import RLTheory.Tactic.CisupLeIntro

-- Demonstrate `ciSup_le_intro`: reduce `⨆ i : Fin n, f i ≤ c` to `∀ i, f i ≤ c`
example : ⨆ i : Fin 3, (i : ℝ) / 3 ≤ 1 := by
  ciSup_le_intro i
  simp only [div_le_one (by norm_num : (3 : ℝ) > 0)]
  exact_mod_cast i.isLt.le
