/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Real.StarOrdered

import RLTheory.Defs
import RLTheory.MeasureTheory.MeasurableSpace.Constructions
import RLTheory.Probability.MarkovChain.Defs
import RLTheory.Probability.MarkovChain.Finite.Defs
import RLTheory.Probability.MarkovChain.Trajectory
import RLTheory.Data.Matrix.PosDef
import RLTheory.MarkovDecisionProcess.MarkovRewardProcess

open ENNReal Real Finset Filter TopologicalSpace Filter MeasureTheory.Filtration MeasureTheory ProbabilityTheory MarkovChain MarkovChain.Finite StochasticMatrix Preorder RLTheory Matrix EuclideanSpace
open scoped ENNReal MeasureTheory ProbabilityTheory Topology InnerProductSpace RealInnerProductSpace

namespace ReinforcementLearning

universe u
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

structure MDPSpec where
  p₀ : ProbabilityMeasure S
  P : (S × A) → ProbabilityMeasure S
  r : S × A → ℝ
  γ : ℝ

variable {mdp_spec : MDPSpec (S := S) (A := A)}

noncomputable def MDPSpec.pi_kernel (pi : S → ProbabilityMeasure A) :
  Kernel S A := {
  toFun s := pi s,
  measurable' := by
    intro s hs
    rw [Set.preimage]
    apply Set.Finite.measurableSet
    apply Set.finite_univ.subset
    simp
}

instance (pi : S → ProbabilityMeasure A) :
  IsMarkovKernel (MDPSpec.pi_kernel pi):= by
  constructor
  intro s
  simp [MDPSpec.pi_kernel]
  infer_instance

noncomputable def MDPSpec.pi_kernel₁ (pi : S → ProbabilityMeasure A) :
  Kernel ((S × A) × S) A := by
  let g := fun sas : (S × A) × S => sas.2
  have hg : Measurable g := by simp [g]; apply measurable_snd
  exact (MDPSpec.pi_kernel pi).comap g hg

instance (pi : S → ProbabilityMeasure A) :
  IsMarkovKernel (MDPSpec.pi_kernel₁ pi):= by
  constructor
  intro s
  simp [MDPSpec.pi_kernel₁]
  infer_instance

noncomputable def MDPSpec.transition_kernel :
  Kernel (S × A) S := {
  toFun sa := mdp_spec.P sa,
  measurable' := by
    intro sa hs
    rw [Set.preimage]
    apply Set.Finite.measurableSet
    apply Set.finite_univ.subset
    simp
}

instance : IsMarkovKernel mdp_spec.transition_kernel := by
  constructor
  intro sa
  simp [MDPSpec.transition_kernel]
  infer_instance

noncomputable def MDPSpec.induced_chain (pi : S → ProbabilityMeasure A) :
  HomMarkovChainSpec (S := S × A) := by
  constructor
  case init =>
    exact ⟨mdp_spec.p₀ ⊗ₘ (pi_kernel pi), by infer_instance⟩
  case kernel =>
    exact mdp_spec.transition_kernel ⊗ₖ (pi_kernel₁ pi)
  case markov_kernel =>
    infer_instance

structure FiniteMDP extends MDPSpec (S := S) (A := A) where
  pi : S → ProbabilityMeasure A
  hM : StochasticMatrix.Irreducible (kernel_mat (MDPSpec.induced_chain pi)) ∧
    StochasticMatrix.Aperiodic (S := S × A) (kernel_mat (MDPSpec.induced_chain pi))
  hγ : 0 ≤ γ ∧ γ < 1

variable {MDP : FiniteMDP (S := S) (A := A)}

noncomputable def FiniteMDP.MRP : FiniteMRP (S := S × A) := {
  M := MDPSpec.induced_chain MDP.pi,
  hM := MDP.hM,
  γ := MDP.γ,
  hγ := MDP.hγ,
  r := MDP.r
}

omit [Nonempty S] [Nonempty A] in
lemma FiniteMDP.MRP.P_apply (y : S × A) (s : S) (a : A) :
  MDP.MRP.P y (s, a) = MDP.P y {s} * MDP.pi s {a} := by
  simp [FiniteMRP.P, kernel_mat, MRP, MDPSpec.induced_chain,
    Kernel.compProd_apply]
  simp [MDPSpec.pi_kernel₁, MDPSpec.pi_kernel, MDPSpec.transition_kernel]
  simp [Set.preimage, lintegral_fintype]
  have : ∀ x ∈ univ, ((MDP.pi x) : Measure A) {z | x = s ∧ z = a} *
    ((MDP.P y) : Measure S) {x} =
    if x = s then ((MDP.P y) {s} * (MDP.pi s) {a} : ℝ≥0∞) else (0 : ℝ≥0∞) := by
    intro x
    by_cases h : x = s
    simp [h]
    ring_nf
    simp [h]
  simp [sum_congr rfl this]
  exact_mod_cast rfl

end ReinforcementLearning
