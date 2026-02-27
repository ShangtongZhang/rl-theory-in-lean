/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

import RLTheory.Tactic.Tactics
import RLTheory.Defs
import RLTheory.MeasureTheory.MeasurableSpace.Constructions
import RLTheory.StochasticApproximation.MartingaleDifference
import RLTheory.StochasticApproximation.CondExp
import RLTheory.StochasticApproximation.Pathwise
import RLTheory.StochasticApproximation.StepSize
import RLTheory.Probability.MarkovChain.Defs
import RLTheory.Probability.MarkovChain.Finite.Defs
import RLTheory.Probability.MarkovChain.Trajectory
import RLTheory.MarkovDecisionProcess.MarkovRewardProcess

open Real Finset Filter TopologicalSpace Filter MeasureTheory.Filtration MeasureTheory ProbabilityTheory StochasticApproximation StochasticMatrix Preorder RLTheory Matrix MarkovChain ReinforcementLearning
open scoped MeasureTheory ProbabilityTheory Topology InnerProductSpace RealInnerProductSpace Gradient

namespace StochasticApproximation

universe u
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable {d : ℕ}

variable {F : E d → (S × S) → E d}
variable {f : E d → E d}
variable {fixed_point : E d}
variable {x : ℕ → (ℕ → S × S) → E d}
variable {x₀ : E d}
variable {α : ℕ → ℝ}
variable {mrp : FiniteMRP (S := S)}

theorem ae_tendsto_of_iterates_iid_samples
  (hx : IteratesOfResidual x x₀ α F)
  (hFm : Measurable F.uncurry)
  (hFlip : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖)
  (hf : fixed_point = f fixed_point)
  (hfF : ∀ w, f w = ∑ s, ∑ s', (mrp.μ s * mrp.P s s') • F w (s, s'))
  (hα : RobbinsMonro α)
  {φ : E d → ℝ}
  {φ' : E d → E d}
  (hφm : Measurable φ)
  (hgradφm : Measurable φ')
  [LyapunovFunction φ φ' f] :
  ∀ᵐ ω ∂ mrp.iid_samples,
    Tendsto (fun n => x n ω) atTop (𝓝 fixed_point) := by
    have hP : RowStochastic mrp.P := by infer_instance
    have hμ : StochasticVec mrp.μ := by infer_instance
    have hAdapted := hx.adaptedOnSamplePath

    have hflip := lipschitz_of_expectation hfF hFlip

    have hfm : Measurable f := by
      apply Measurable.congr (funext_iff.mpr hfF).symm
      measurable_finset_smul_sum
      apply Measurable.eval
      apply Measurable.of_uncurry
      exact hFm

    have hFgrowth := linear_growth_of_lipschitz' hFlip
    have hfgrowth := linear_growth_of_lipschitz hflip
    have hfLip' : ∃ L, LipschitzWith L f := by
      obtain ⟨C, hCnonneg, hC⟩ := hflip
      use ⟨C, by simp [hCnonneg]⟩
      apply lipschitzWith_iff_norm_sub_le.mpr
      intro x y
      exact_mod_cast hC x y

    let e₁ := fun n ω =>
      α (n - 1) • (F (x (n - 1) ω) (ω n) - f (x (n - 1) ω))
    have he₁bdd : ∃ C, 0 ≤ C ∧ ∀ ω n,
      ‖e₁ (n + 1) ω‖ ≤ C * α n * (‖x n ω‖ + 1) := by
      obtain ⟨C₁, _, hC₁⟩ := hFgrowth
      obtain ⟨C₂, _, hC₂⟩ := hfgrowth
      simp [e₁]
      refine ⟨?L, ?hLnonneg, ?hL⟩
      case L => exact C₁ + C₂
      case hLnonneg => positivity
      case hL =>
        intro ω n
        rw [norm_smul]
        grw [norm_sub_le]
        grw [hC₁, hC₂]
        rw [Real.norm_eq_abs, abs_of_nonneg (hα.pos n).le]
        apply le_of_eq
        ring

    let e₂ : ℕ → (ℕ → (S × S)) → E d := fun _ _ => 0

    have hxIterates : Iterates x x₀ f e₁ e₂ α := by
      constructor
      exact hx.init
      intro n ω
      simp [e₁, e₂]
      rw [add_assoc, ←smul_add, sub_add_sub_cancel']
      rw [hx.step]

    have : IsProbabilityMeasure mrp.iid_samples := by
      apply Subtype.property

    apply ae_tendsto_of_iterates_mds_noise
      (φ := φ) (φ' := φ') (f := f) (e₁ := e₁) (e₂ := e₂) (x₀ := x₀) (α := α)
      (ℱ := piLE) (hα := hα) (hfm := hfm) (hx := hxIterates)
      (hfLip := hfLip')
    case he₁ =>
      obtain_bound he₁bdd as C, hCnonneg, hC
      apply Eventually.of_forall
      exact hC
    case he₂ => use 0; simp [e₂]
    case he₂Adapted =>
      simp [e₂]
      intro n
      exact measurable_const
    case he₁Adapted =>
      simp [e₁]
      intro n
      obtain ⟨wn, hwnm, hwneq⟩ := hAdapted.property n
      have hwnm': Measurable[piLE (n + 1)] fun ω =>
        wn (frestrictLe («π» := X (S × S)) n ω) := by
        apply hwnm.comp
        apply Measurable.mono
        apply measurable_frestrictLe_piLE
        apply piLE.mono
        simp
        rfl
      apply Measurable.smul
      apply measurable_const
      simp [Filtration.shift]
      apply Measurable.sub
      let F₁ := fun ω => (x n ω, ω (n + 1))
      have : (fun ω => F (x n ω) (ω (n + 1))) = F.uncurry ∘ F₁ := by
        ext1 ω
        simp [F₁, Function.uncurry_def]
      rw [this]
      apply hFm.comp
      apply Measurable.prod
      simp [F₁]
      rw [funext_iff.mpr hwneq]
      simp
      exact hwnm'
      simp [F₁]
      apply measurable_pi_apply_piLE
      apply hfm.comp
      rw [funext_iff.mpr hwneq]
      exact hwnm'
    case he₁MDS =>
      intro n
      simp [e₁]
      obtain ⟨wn, hwnm, hwneq⟩ := hAdapted.property n
      let H : E d × (S × S) → E d :=
        fun xy => (α n) • (F xy.1 xy.2 - f xy.1)
      have hHm : Measurable H := by
        apply Measurable.smul
        apply measurable_const
        apply Measurable.sub
        rw [←Function.uncurry_def]
        exact hFm
        apply hfm.comp
        apply Measurable.fst
        apply measurable_id
      have : (fun ω => α n • (F (x n ω) (ω (n + 1)) - f (x n ω)))
        = iterates_update (Nat.le_succ _) H wn := by
        ext1 ω
        simp [iterates_update]
        have := frestrictLe₂_comp_frestrictLe
          («π» := fun _ : ℕ => S × S) (a := n) (b := n + 1) (by simp)
        have := congrFun this ω
        simp [frestrictLe] at this
        rw [this]
        have := hwneq ω
        simp [frestrictLe] at this
        rw [←this]
      rw [this]
      have hbdd : ∃ C, ∀ ω s,
        ‖H.curry (wn (frestrictLe («π» := X (S × S)) n ω)) s‖ ≤ C := by
        obtain ⟨C₁, _, hC₁⟩ := hFgrowth
        obtain ⟨C₂, _, hC₂⟩ := hfgrowth
        obtain ⟨C₃, _, hC₃⟩ := hx.bdd hFlip n
        refine ⟨?C, ?hC⟩
        case C => exact ‖α n‖ * (C₁ * (C₃ + 1) + C₂ * (C₃ + 1))
        case hC =>
          intro ω s
          rw [←hwneq ω]
          simp [H]
          rw [norm_smul]
          grw [norm_sub_le, hC₁, hC₂, hC₃]
          simp
      have := condExp_iterates_update (M := mrp.aug_chain_iid)
        (φ := H) (φ₁ := wn) (Nat.le_succ n) hHm hbdd hwnm ?hInt
      case hInt =>
        intro x₀
        apply integrable_iterates_update (M := mrp.aug_chain_iid)
          (hφm := hHm) (hbdd := hbdd) (hφ₁m := hwnm)
      apply this.trans
      apply Eventually.of_forall
      intro ω
      simp [Finite.integral_fintype_kernel_iter, Finite.kernel_mat]
      simp [-PMF.toMeasure_apply_fintype, FiniteMRP.aug_chain_iid]

      have : ∀ y : S × S, MeasurableSet {y} := by simp
      conv_lhs =>
        congr; rfl; ext y
        rw [PMF.toMeasure_apply_singleton]
        congr; congr;
        change (fun y => ENNReal.ofReal _) y; rfl; rfl
        apply this
      conv_lhs =>
        congr; rfl; ext y; congr; simp
        rw [ENNReal.toReal_ofReal]; rfl
        apply mul_nonneg
        apply hμ.nonneg
        apply (hP.stochastic y.1).nonneg
      simp [H, smul_sub, smul_smul, ←sum_smul, ←sum_mul]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp
      simp_rw [←mul_sum, (hP.stochastic ?_).rowsum]
      simp [hμ.rowsum]
      simp_rw [mul_comm (b := α n), ←smul_smul, ←smul_sum]
      simp [hfF]
      simp_rw [←smul_smul, ←smul_sum]
      simp
    case hφm => exact hφm
    case hgradφm => exact hgradφm
    case hz => exact hf

end StochasticApproximation
