/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset Real Filter
open scoped BigOperators

namespace Filter

lemma EventuallyEq.finset_sum {α ι β: Type*} [AddCommGroup β] [DecidableEq ι] {l : Filter α}
  {s : Finset ι} {f g : ι → α → β} (hfg : ∀ i ∈ s, f i =ᶠ[l] g i) :
  ∑ i ∈ s, f i =ᶠ[l] ∑ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    apply EventuallyEq.add
    exact hfg a (Finset.mem_insert_self a s)
    exact ih (fun i hi => hfg i (Finset.mem_insert_of_mem hi))

end Filter
