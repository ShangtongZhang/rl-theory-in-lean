/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Bornology.Basic

open MeasureTheory MeasureTheory.Measure Filtration ProbabilityTheory.Kernel ProbabilityTheory Finset Bornology NNReal ENNReal Preorder Filter

namespace ProbabilityTheory.Kernel

variable {α β γ: Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

noncomputable def iter (κ : Kernel α α) : ℕ → Kernel α α
| 0       => Kernel.id
| (n + 1) => ((iter κ) n).comp κ

instance (n : ℕ) (κ : Kernel α α) [IsMarkovKernel κ] :
  IsMarkovKernel (κ.iter n) := by
  induction' n with n ih
  case zero =>
    simp [iter]
    infer_instance
  case succ =>
    simp [iter]
    infer_instance

lemma iter_comm (κ : Kernel α α) (n : ℕ) :
  κ ∘ₖ κ.iter n = κ.iter n ∘ₖ κ := by
  induction' n with n ih
  case zero =>
    simp [iter, Kernel.id_comp]
  case succ =>
    simp [iter]
    conv_rhs => rw [←ih]
    simp [comp_assoc]

lemma iter_comp (κ : Kernel α α) (m n : ℕ) :
  (κ.iter m).comp (κ.iter n) = κ.iter (m + n) := by
  induction' m with m ih
  case zero =>
    simp [iter, Kernel.id_comp]
  case succ =>
    have : m + 1 + n = (m + n) + 1 := by omega
    rw [this, iter, iter, ←ih]
    simp [comp_assoc]
    apply congrArg
    simp [iter_comm]

end ProbabilityTheory.Kernel
