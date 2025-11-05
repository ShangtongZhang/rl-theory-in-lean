/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang shangtong.zhang.cs@gmail.com
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Bornology.Basic

import RLTheory.Defs
import RLTheory.MeasureTheory.MeasurableSpace.Constructions
import RLTheory.Probability.MarkovChain.Defs
import RLTheory.MeasureTheory.Function.L1Space.Integrable

open RLTheory
open MeasureTheory MeasureTheory.Measure Filtration
open ProbabilityTheory.Kernel
open ProbabilityTheory
open Finset Bornology
open NNReal ENNReal Preorder Filter


namespace ProbabilityTheory

namespace MarkovChain

universe u
variable {S : Type u} [MeasurableSpace S]

def X (S : Type u) : ℕ → Type u := fun _ => S

instance : ∀ n, MeasurableSpace (X (S := S) n) := by
  intro n; unfold X; infer_instance

noncomputable def kernel_comap_trivial
  (κ : Kernel S S) (n : ℕ):
  Kernel (Iic n → S) S := by
  let g : (Iic n → S) → S :=
    fun history => history ⟨n, by simp [mem_Iic]⟩
  have hg : Measurable g := by apply measurable_pi_apply
  exact κ.comap g hg

noncomputable def expand_kernel
  (M : HomMarkovChainSpec S):
  ∀ n : ℕ, Kernel (Iic n → S) S := by
    intro n
    let g : (Iic n → S) → S :=
      fun history => history ⟨n, by simp [mem_Iic]⟩
    have hg : Measurable g := by apply measurable_pi_apply
    exact M.kernel.comap g hg

instance (M : HomMarkovChainSpec S) :
  ∀ n, IsMarkovKernel (expand_kernel M n) := by
  intro n; unfold expand_kernel; simp
  have := M.markov_kernel
  apply IsMarkovKernel.comap

noncomputable def traj_prob₀
  (M : HomMarkovChainSpec S) (x₀ : Iic 0 → S)
  : ProbabilityMeasure (ℕ → S) := by
  let κ := traj (X := X S) (expand_kernel M) 0
  let prob := κ x₀
  constructor
  case val => exact prob
  case property =>
    constructor
    unfold prob
    apply IsProbabilityMeasure.measure_univ

noncomputable def traj_prob
  (M : HomMarkovChainSpec S) : ProbabilityMeasure (ℕ → S) := by
  let κ := traj (X := X S) (expand_kernel M) 0
  let f : S → (Iic 0 → S) := fun s => (fun _ : Iic 0 => s)
  have hf : Measurable f := by
    apply measurable_pi_iff.mpr
    intro x
    unfold f
    apply measurable_id
  let init := M.init.map hf.aemeasurable
  let prob := init.1.bind κ
  constructor
  case val => exact prob
  case property =>
    constructor
    unfold prob
    have := Measure.bind_apply (f := ⇑κ) (m := init.1) (s := Set.univ) ?_ ?_
    apply this.trans
    simp
    simp
    apply Measurable.aemeasurable
    apply Kernel.measurable

end MarkovChain

end ProbabilityTheory
