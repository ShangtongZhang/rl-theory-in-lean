/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Defs

import RLTheory.Defs
import RLTheory.Probability.MarkovChain.Defs
import RLTheory.Data.Matrix.Stochastic
import RLTheory.Probability.Kernel.Basic

open MeasureTheory MeasureTheory.Measure Filtration ProbabilityTheory.Kernel ProbabilityTheory Finset NNReal ENNReal Preorder Function StochasticMatrix Filter

namespace ProbabilityTheory

namespace MarkovChain

namespace Finite

universe u
variable {S : Type u}
variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

def kernel_mat (M : HomMarkovChainSpec S)
  : Matrix S S ℝ :=
  Matrix.of (fun a b => (M.kernel a {b}).toReal)

def init_vec (M : HomMarkovChainSpec S)
  : S → ℝ :=
  fun s => (M.init {s}).toReal

lemma prob_sum_to_one
  (μ : Measure S) [IsProbabilityMeasure μ] :
  ∑ s, (μ {s}).toReal = 1 := by
  have : ∑ s, μ {s} = 1 := by simp
  have := congrArg ENNReal.toReal this
  rw [ENNReal.toReal_sum] at this
  exact this
  intro s hs; simp

instance (M : HomMarkovChainSpec S)
  : StochasticVec (init_vec M) := by
  constructor
  case nonneg =>
    intro s;
    unfold init_vec; simp
  case rowsum =>
    unfold init_vec
    apply prob_sum_to_one

instance (M : HomMarkovChainSpec S)
  : RowStochastic (kernel_mat M) := by
  constructor
  intro s
  constructor
  case nonneg =>
    intro j; unfold kernel_mat; simp
  case rowsum =>
    unfold kernel_mat
    simp
    have := (M.markov_kernel).isProbabilityMeasure s
    apply prob_sum_to_one

omit [Fintype S] [MeasurableSingletonClass S] in
lemma kernel_apply_eq_mat_apply
  (M : HomMarkovChainSpec S) (s s' : S) :
  (M.kernel s {s'}).toReal = kernel_mat M s s' := by
  simp [kernel_mat]

lemma integral_fintype_kernel_iter
  {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] [CompleteSpace α] [DecidableEq S] {s : S}
  (M : HomMarkovChainSpec S) (n : ℕ) (f : S → α):
  ∫ s, f s ∂ M.kernel.iter n s = ∑ s', ((kernel_mat M) ^ n) s s' • f s' := by
  have := M.markov_kernel
  rw [integral_fintype]
  apply sum_congr rfl
  intro s' hs'
  apply congr ?_ rfl
  apply congr rfl
  simp [Measure.real_def]
  have : ∀ s s',
    (((M.kernel.iter n) s) {s'}).toReal = (kernel_mat M ^ n) s s' := by
    induction' n with n ih
    case zero =>
      intro s s'
      simp [iter, Kernel.id_apply, Matrix.one_apply]
      by_cases h : s = s'
      case pos => simp [h]
      case neg => simp [h]
    case succ =>
      intro s s'
      rw [iter, Kernel.comp_apply, bind_apply]
      let f := fun s => ((M.kernel.iter n) s) {s'}
      let f' := fun s => (f s).toReal
      have : ∀ s, f s = ENNReal.ofReal (f' s) := by simp [f, f']
      simp [f] at this
      conv_lhs =>
        congr
        apply lintegral_congr this
      rw [←integral_eq_lintegral_of_nonneg_ae, integral_fintype, add_comm,
        pow_add]
      simp_rw [Measure.real_def, kernel_apply_eq_mat_apply, f', f]
      rw [Matrix.mul_apply]
      apply sum_congr rfl
      intro l hl
      simp [ih l s']
      simp
      apply Eventually.of_forall
      intro s
      simp [f']
      apply Measurable.aestronglyMeasurable
      apply measurable_of_countable
      apply MeasurableSingletonClass.measurableSet_singleton
      apply Measurable.aemeasurable
      apply Kernel.measurable
  apply this
  simp

end Finite

end MarkovChain

end ProbabilityTheory
