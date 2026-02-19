/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
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
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

import RLTheory.Defs
import RLTheory.MeasureTheory.MeasurableSpace.Constructions
import RLTheory.MeasureTheory.Measure.GiryMonad
import RLTheory.MeasureTheory.Measure.Prod
import RLTheory.Probability.MarkovChain.Defs
import RLTheory.Probability.MarkovChain.Trajectory
import RLTheory.Probability.Kernel.Basic
import RLTheory.Probability.Kernel.Composition.MapComap
import RLTheory.MeasureTheory.Function.L1Space.Integrable

open RLTheory MeasureTheory MeasureTheory.Measure Filtration ProbabilityTheory.Kernel ProbabilityTheory Finset Bornology NNReal ENNReal Preorder Filter MarkovChain

namespace StochasticApproximation

universe u
variable {d : ℕ}
variable {S : Type u} [MeasurableSpace S]

noncomputable def iterates_update
  {α β : Type*}
  {n : ℕ}
  {m : ℕ}
  (hnm : n ≤ m)
  (φ : α × S → β)
  (φ₁ : (Iic n → S) → α)
  : (ℕ → S) → β := by
  let f₁ := (Iic m).restrict (π := X S)
  let last := fun x : Iic m → S => x ⟨m, by simp⟩
  let f₂ : (Iic m → S) → (α × S) := fun h =>
    ⟨φ₁ (frestrictLe₂ hnm (π := X S) h), last h⟩
  exact fun x => φ (f₂ (f₁ x))

lemma partialTraj_frestrictLe₂_eq_id
  {n m : ℕ} (hnm : n ≤ m) (κ : (n : ℕ) → Kernel (Iic n → S) S)
  [∀ i, IsMarkovKernel (κ i)] :
  (partialTraj (X := X S) κ n m).map (frestrictLe₂ hnm)
    = Kernel.id := by
    refine Nat.le_induction ?base ?succ m hnm
    case base =>
      unfold partialTraj
      simp
      rw [←Kernel.map_id Kernel.id]
      apply congr
      apply congr
      rfl
      simp [Kernel.id]
      apply congr
      rfl
      rfl
      rfl
    case succ =>
      intro m hnm ih
      rw [partialTraj_succ_of_le, ←Kernel.map_comp_right]
      apply Eq.trans
      apply congrArg
      case h₁.a₂ =>
        exact frestrictLe₂ (π := X S) hnm ∘ Prod.fst
      ext h x
      simp [IicProdIoc_def]
      have : ↑x ≤ m := by
        have := mem_Iic.mp x.property
        linarith
      simp [this]
      rw [Kernel.map_comp, Kernel.map_comp_right]
      have : IsMarkovKernel
        ((κ m).map (MeasurableEquiv.piSingleton (X := X S) m)) := by
        apply IsMarkovKernel.map
        exact (MeasurableEquiv.piSingleton m).measurable
      rw [Kernel.prod_map_fst, ←Kernel.map_comp, Kernel.id_comp]
      exact ih
      measurability
      measurability
      measurability
      measurability
      omega

lemma partialTraj_pi_eq_kernel
  (M : HomMarkovChainSpec S)
  {n m : ℕ} (hnm : n ≤ m) :
  (partialTraj (X := X S) (expand_kernel M) n m).map (fun x => x ⟨m, by simp⟩)
    = (M.kernel.iter (m - n)).comap_last n:= by
    refine Nat.le_induction ?base ?succ m hnm
    case base =>
      simp [partialTraj, iter, comap_last]
      apply Eq.trans
      apply congrFun
      apply congrArg (a₂ := Kernel.id)
      rfl
      rw [Kernel.id_map]
      rfl
    case succ =>
      intro m hnm ih
      rw [partialTraj_succ_of_le, ←map_comp_right]
      apply Eq.trans
      apply congrArg (a₂ := (fun x => x ⟨m + 1, by simp⟩) ∘ Prod.snd)
      ext h
      simp [IicProdIoc_def]
      rw [map_comp_right, Kernel.map_comp, prod_map_snd]
      simp [comap_last]
      ext1 x
      rw [Kernel.map_apply, Kernel.comap_apply, Kernel.comp_apply,
        Measure.map_comp, ←Kernel.map_comp_right]
      apply Eq.trans
      apply congrArg
      apply congrArg
      apply congrArg (a₂ := id)
      rfl
      simp
      have : m + 1 - n = 1 + (m - n) := by omega
      rw [this, ←iter_comp]
      simp [iter, comp_apply]
      have := Kernel.congrFun_apply ih x
      simp [comap_last] at this
      rw [←this, Kernel.map_apply, expand_kernel]
      ext s hs
      rw [bind_apply, bind_apply, ←Kernel.map_apply, lintegral_map]
      simp
      apply measurable_pi_apply
      apply measurable_measure.mp
      exact M.kernel.measurable
      exact hs
      apply measurable_pi_apply
      exact hs
      apply Measurable.aemeasurable
      exact M.kernel.measurable
      exact hs
      apply Measurable.aemeasurable
      simp
      apply Measurable.comp
      exact M.kernel.measurable
      apply measurable_pi_apply
      apply measurable_pi_apply
      measurability
      apply measurable_pi_apply
      apply measurable_pi_apply
      apply measurable_pi_apply
      apply Measurable.snd
      apply measurable_id
      apply measurable_pi_apply
      apply measurable_IicProdIoc
      apply measurable_pi_apply
      exact hnm

set_option maxHeartbeats 600000 in
lemma condExp_iterates_update_aux
  [MeasurableSingletonClass S]
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β] [BorelSpace β] [SecondCountableTopology β]
  (M : HomMarkovChainSpec S)
  {n m : ℕ}
  (hnm : n ≤ m)
  (x₀ : Iic 0 → S)
  (φ : α × S → β)
  (φ₁ : (Iic n → S) → α)
  (hφm : Measurable φ)
  (hφ₁m : Measurable φ₁)
  (hInt : Integrable
    (iterates_update hnm φ φ₁) (traj_prob₀ M x₀))
  : (traj_prob₀ M x₀).1[iterates_update hnm φ φ₁| piLE n]
  =ᵐ[(traj_prob₀ M x₀).1]
    fun x => ∫ s, φ ((φ₁ (frestrictLe n x)), s) ∂ M.kernel.iter (m - n) (x n)
  := by
  apply EventuallyEq.trans
  apply condExp_traj
  linarith
  case i_f => exact hInt
  apply Eventually.of_forall
  intro x; simp
  simp (config := {zeta := false}) [iterates_update, traj_apply]
  set f₁ := (Iic m).restrict (π := X S)
  set last := fun x : Iic m → S => x ⟨m, by simp⟩
  set φ₁' := fun x : Iic m → S => φ₁ (frestrictLe₂ hnm (π := X S) x)
  set f₂ : (Iic m → S) → (α × S) := fun h => ⟨φ₁' h, last h⟩
  set μ := (trajFun (expand_kernel M) n) (frestrictLe n x)
  simp [X]
  rw [←integral_map (μ := μ) (f := fun x => φ (f₂ x)) (φ := f₁)]

  have this := isProjectiveLimit_trajFun (expand_kernel M) n (frestrictLe n x)
  unfold IsProjectiveLimit at this
  have := this (Iic m)
  simp [inducedFamily_Iic] at this
  rw [this]
  rw [←integral_map]
  unfold f₂

  set xn := frestrictLe n x
  set κ := (partialTraj (X := X S) (expand_kernel M) n m)
  set μ := κ xn
  let C := φ₁ xn
  have hC : ∀ᵐ h ∂μ, φ₁' h = C := by
    simp [φ₁', C, xn]
    apply Eventually.mono
    rotate_left
    intro h
    apply congrArg

    let f := fun h : Iic m → S =>
      frestrictLe₂ (π := X S) hnm h
    let p := fun h : Iic n → S => h = frestrictLe (π := X S) n x
    apply (ae_map_iff (μ := μ) (p := p) ?_ ?_).mp
    simp [μ]
    rw [←Kernel.map_apply]
    simp [κ]
    simp [partialTraj_frestrictLe₂_eq_id]
    apply ae_iff.mpr
    apply Eq.trans
    apply congrFun
    apply congrArg
    apply Kernel.id_apply
    apply ae_iff.mp
    apply (ae_dirac_iff _).mpr
    simp [p, xn]

    measurability
    measurability
    measurability
    measurability

  have := MeasureTheory.Measure.map_prodMk_dirac
    (X := φ₁') (Y := last) (hC := hC) ?_
  have := congrArg (fun μ => ∫ y, φ y ∂ μ) this
  apply this.trans
  simp

  rw [dirac_prod]
  rw [integral_map]
  apply Eq.trans
  apply congrArg (fun μ => ∫ x, φ (C, x) ∂ μ)
  simp [μ]
  apply Eq.symm
  apply Kernel.map_apply
  measurability

  apply Eq.trans
  apply congrArg (fun μ => ∫ x, φ (C, x) ∂μ)
  apply congrFun
  apply congrArg
  simp [κ, last]
  apply partialTraj_pi_eq_kernel M hnm
  simp [C, xn, comap_last]

  measurability
  measurability
  measurability
  measurability
  measurability
  measurability
  -- AEStronglyMeasurable (fun x ↦ φ (f₂ x)) (Measure.map f₁ μ)
  apply Measurable.aestronglyMeasurable
  apply hφm.comp
  apply Measurable.prod
  · exact hφ₁m.comp (measurable_frestrictLe₂ hnm)
  · exact measurable_pi_apply _

lemma posPart_eq_ENNReal_toReal_ofReal (r : ℝ) :
  (r)⁺ = (ENNReal.ofReal r).toReal := by
  by_cases h : 0 ≤ r
  case pos =>
    simp [h]
  case neg =>
    have : r ≤ 0 := by linarith
    simp [this]
    rw [ENNReal.ofReal_of_nonpos this]
    simp

private lemma integrable_of_measure_lintegral
  {α β} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {κ : Kernel α β} {f : β → ℝ}
  (hfm : Measurable f)
  (hf : Integrable f (μ.bind κ)) :
  Integrable (fun a ↦ (∫⁻ (a : β), ENNReal.ofReal (f a) ∂κ a).toReal) μ := by
    apply integrable_toReal_of_lintegral_ne_top
    let f₁ := fun a => κ a
    have hf₁m : Measurable f₁ := κ.measurable
    let f₂ : Measure β → ℝ≥0∞ := fun x => ∫⁻ (x : β), ENNReal.ofReal (f x) ∂ x
    have hf₂m : Measurable f₂ := by
      apply measurable_lintegral
      apply Measurable.ennreal_ofReal
      exact hfm
    apply Measurable.aemeasurable
    exact hf₂m.comp hf₁m
    rw [←lintegral_bind]
    apply ne_of_lt
    apply Integrable.lintegral_lt_top
    exact hf
    exact κ.measurable.aemeasurable
    apply AEMeasurable.ennreal_ofReal
    exact hf.aemeasurable

theorem integral_bind_real
  {α β} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {κ : Kernel α β} {f : β → ℝ}
  (hfm : Measurable f)
  (hf : Integrable f (μ.bind κ))
  (hfκ : ∀ a, Integrable f (κ a)) :
  ∫ x, f x ∂ (μ.bind κ) = ∫ a, ∫ x, f x ∂ (κ a) ∂ μ := by
  have hdecomp :=
    (integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (μ := μ.bind κ) hf).trans rfl

  have hintpos := integrable_of_measure_lintegral hfm hf
  have hintneg := integrable_of_measure_lintegral hfm.neg hf.neg

  let f₁ := fun a => κ a
  have hf₁m : Measurable f₁ := κ.measurable
  let f₂ : Measure β → ℝ≥0∞ := fun x => ∫⁻ (x : β), ENNReal.ofReal (f x) ∂ x
  have hf₂m : Measurable f₂ := by
    apply measurable_lintegral
    apply Measurable.ennreal_ofReal
    exact hfm
  let f₃ : Measure β → ℝ≥0∞ := fun x => ∫⁻ (x : β), ENNReal.ofReal (-f x) ∂ x
  have hf₃m : Measurable f₃ := by
    apply measurable_lintegral
    apply Measurable.ennreal_ofReal
    exact hfm.neg

  rw [lintegral_bind] at hdecomp
  rw [lintegral_bind] at hdecomp
  rw [←integral_toReal] at hdecomp
  rw [←integral_toReal] at hdecomp
  rw [←integral_sub] at hdecomp
  rw [hdecomp]
  apply congrArg
  ext a
  rw [←integral_toReal]
  rw [←integral_toReal]
  rw [←integral_sub]
  apply congrArg
  ext a
  by_cases h : 0 ≤ f a
  case pos =>
    simp [h]
    rw [ENNReal.ofReal_of_nonpos]
    simp
    linarith
  case neg =>
    rw [ENNReal.ofReal_of_nonpos]
    have : -f a ≥ 0 := by linarith
    simp [this]
    linarith

  apply Integrable.congr
  rotate_left
  apply Eventually.of_forall
  intro x
  simp
  exact posPart_eq_ENNReal_toReal_ofReal (f x)

  apply Integrable.congr
  rotate_left
  apply Eventually.of_forall
  intro x
  simp
  exact posPart_eq_ENNReal_toReal_ofReal (-f x)

  apply AEMeasurable.ennreal_ofReal
  apply AEMeasurable.neg
  exact (hfκ a).aemeasurable

  apply Eventually.of_forall
  intro x
  simp

  apply AEMeasurable.ennreal_ofReal
  exact (hfκ a).aemeasurable

  apply Eventually.of_forall
  intro x
  simp

  apply integrable_of_measure_lintegral hfm hf
  apply integrable_of_measure_lintegral hfm.neg hf.neg

  exact (hf₃m.comp hf₁m).aemeasurable

  apply Eventually.of_forall
  intro a
  apply Integrable.lintegral_lt_top
  exact (hfκ a).neg

  exact (hf₂m.comp hf₁m).aemeasurable

  apply Eventually.of_forall
  intro a
  apply Integrable.lintegral_lt_top
  exact hfκ a

  exact κ.measurable.aemeasurable

  apply AEMeasurable.ennreal_ofReal
  exact hf.aemeasurable.neg

  exact κ.measurable.aemeasurable

  apply AEMeasurable.ennreal_ofReal
  exact hf.aemeasurable

  apply Integrable.pos_part
  exact hfκ a

  apply Integrable.pos_part
  exact (hfκ a).neg

theorem integrable_bind_real
  {α β} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {κ : Kernel α β} {f : β → ℝ}
  (hfm : Measurable f)
  (hf : Integrable f (μ.bind κ))
  (hfκ : ∀ a, Integrable f (κ a))
  : Integrable (fun a => ∫ b, f b ∂ κ a) μ := by

  apply Integrable.congr
  case h =>
    apply Eventually.of_forall
    intro a
    simp
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part]
    exact hfκ a

  apply Integrable.sub
  apply integrable_of_measure_lintegral hfm hf
  apply integrable_of_measure_lintegral hfm.neg hf.neg

theorem integrable_pi_iff_euclidean
  {α : Type*} [MeasurableSpace α]
  (f : α → E d)
  (μ : Measure α) :
  (∀ i, Integrable (fun x => f x i) μ) ↔ Integrable f μ := by
  constructor
  case mp =>
    intro h
    apply integrable_of_norm_sub_le
    case f₀ => exact fun x => 0
    case g =>
      exact fun x => ∑ i, |f x i|
    case h =>
      apply Eventually.of_forall
      intro x
      simp
      rw [PiLp.norm_eq_of_L2]
      apply le_of_sq_le_sq
      rw [Real.sq_sqrt]
      simp only [Real.norm_eq_abs]
      apply sum_sq_le_sq_sum_of_nonneg
      intro i hi
      simp
      apply sum_nonneg
      intro j hj
      simp [sq_nonneg]
      apply sum_nonneg
      intro j hj
      simp

    apply AEMeasurable.aestronglyMeasurable
    -- f : α → E d = PiLp 2 (fun _ : Fin d => ℝ)
    -- Need to show AEMeasurable f μ
    -- Strategy: show AEMeasurable (fun x => (f x).ofLp) μ using aemeasurable_pi_iff
    -- Then compose with MeasurableEquiv.toLp which is measurable
    have h_ae : AEMeasurable (fun x => (f x).ofLp) μ := by
      apply aemeasurable_pi_iff.mpr
      intro i
      exact (h i).aemeasurable
    -- Now use that toLp is measurable and ofLp ∘ toLp = id
    have : f = fun x => WithLp.toLp 2 ((f x).ofLp) := by
      ext x
      rfl
    rw [this]
    exact (WithLp.measurable_toLp 2 _).comp_aemeasurable h_ae

    simp

    apply integrable_finset_sum
    intro i hi
    exact (h i).abs
  case mpr =>
    intro h i
    apply integrable_of_norm_sub_le
    case f₀ => exact fun x => 0
    case g => exact fun x => ‖f x‖
    case h =>
      apply Eventually.of_forall
      intro x
      simp
      rw [PiLp.norm_eq_of_L2]
      apply le_of_sq_le_sq
      rw [Real.sq_sqrt]
      simp only [Real.norm_eq_abs]
      rw [←sum_erase_add (a := i)]
      apply sub_nonneg.mp
      rw [add_sub_cancel_right]
      apply sum_nonneg
      intro j hj
      simp [sq_nonneg]
      simp
      apply sum_nonneg
      intro j hj
      simp [sq_nonneg]
      simp [Real.sqrt_nonneg]

    apply AEMeasurable.aestronglyMeasurable
    -- Need: AEMeasurable (fun x => (f x).ofLp i) μ
    -- We have: AEMeasurable f μ (from h.aemeasurable)
    -- And: Measurable (fun y : E d => y.ofLp i) (it's measurable_pi_apply composed with measurable_ofLp)
    apply AEMeasurable.eval
    exact (WithLp.measurable_ofLp 2 _).comp_aemeasurable h.aemeasurable

    simp

    apply (integrable_norm_iff _).mpr h
    exact h.aemeasurable.aestronglyMeasurable

theorem integral_bind_euclidean
  {α β} [MeasurableSpace α] [MeasurableSpace β]
  (μ : Measure α) (κ : Kernel α β) {f : β → E d}
  (hf : Integrable f (μ.bind κ))
  (hfm : Measurable f)
  (hfκ : ∀ a, Integrable f (κ a)) :
  ∫ x, f x ∂ (μ.bind κ) = ∫ a, ∫ x, f x ∂ (κ a) ∂ μ := by
  ext i
  let idx := fun x : E d => x i
  have := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (L := EuclideanSpace.proj i) (φ := f) (μ := μ.bind κ) hf
  simp at this
  rw [←this]
  set g := fun a => ∫ x, f x ∂ (κ a)
  have hg : Integrable g μ := by
    apply (integrable_pi_iff_euclidean g μ).mp
    unfold g
    intro j
    have : (fun a => ∫ (b : β), f b j ∂κ a)
      = (fun a => (∫ b, f b ∂κ a) j) := by
      ext a
      apply ContinuousLinearMap.integral_comp_comm (L := EuclideanSpace.proj j) (φ := f) (μ := κ a) (hfκ a)
    rw [←this]
    have := integrable_pi_iff_euclidean f (μ.bind κ)
    have := this.mpr hf j
    apply integrable_bind_real ?_ this ?_

    let idx := fun x : E d => x j
    have : Measurable idx := (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)
    exact this.comp hfm
    intro a
    apply (integrable_pi_iff_euclidean f (κ a)).mpr
    exact hfκ a

  have := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (L := EuclideanSpace.proj i) (φ := g) (μ := μ) hg
  simp at this
  rw [←this]
  apply Eq.trans
  case h₂ =>
    apply integral_congr_ae
    apply Eventually.of_forall
    intro a
    simp [g]
    have := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (L := EuclideanSpace.proj i) (φ := f) (μ := κ a) (hfκ a)
    simp at this
    exact this
  apply integral_bind_real

  have : Measurable idx := (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)
  exact this.comp hfm

  exact ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (L := EuclideanSpace.proj i) hf

  intro a
  exact ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (L := EuclideanSpace.proj i) (hfκ a)

theorem Measurable.integral_kernel_prod_right
  {α β: Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {κ : Kernel α β} [IsSFiniteKernel κ] {f : α → β → E d}
  (hfm : Measurable f.uncurry)
  (hfInt : ∀ a, Integrable (f a) (κ a))
  : Measurable fun a => ∫ (b : β), f a b ∂κ a := by
    -- The result type is E d = PiLp 2 (...), not Pi.
    -- We show measurability via the measurable equivalence with Pi.
    have h_ofLp_meas : Measurable (fun a => (∫ (b : β), f a b ∂κ a).ofLp) := by
      apply measurable_pi_iff.mpr
      intro i
      have : (fun a => (∫ b, f a b ∂ κ a).ofLp i) =
        (fun a => (∫⁻ b, ENNReal.ofReal (f a b i) ∂ (κ a)).toReal) -
        fun a => (∫⁻ b, ENNReal.ofReal (-f a b i) ∂ κ a).toReal := by
        ext a
        simp
        have := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (L := EuclideanSpace.proj i) (φ := f a) (μ := κ a) ?_
        simp at this
        rw [←this]
        rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part]
        apply (integrable_pi_iff_euclidean (f a) (κ a)).mpr
        apply hfInt
        apply hfInt
      rw [this]
      -- hfm : Measurable f.uncurry where f.uncurry : α × β → E d
      -- We need measurability of (fun (a, b) => (f a b).ofLp i) : α × β → ℝ
      have hfm' : Measurable (fun p : α × β => ((f.uncurry p).ofLp) i) := by
        apply (measurable_pi_apply i).comp
        exact (WithLp.measurable_ofLp 2 _).comp hfm
      apply Measurable.sub
      · apply Measurable.ennreal_toReal
        apply Measurable.lintegral_kernel_prod_right
        apply Measurable.ennreal_ofReal
        exact hfm'
      · apply Measurable.ennreal_toReal
        apply Measurable.lintegral_kernel_prod_right
        apply Measurable.ennreal_ofReal
        exact hfm'.neg
    -- Now compose with toLp
    have h_eq : (fun a => ∫ (b : β), f a b ∂κ a) = fun a => WithLp.toLp 2 ((∫ (b : β), f a b ∂κ a).ofLp) := by
      ext a
      rfl
    rw [h_eq]
    exact (WithLp.measurable_toLp 2 _).comp h_ofLp_meas

theorem measurable_integral_kernel_euclidean
  {α β: Type*} [MeasurableSpace α] [MeasurableSpace β]
  {κ : Kernel α β}
  {f : β → E d} (hfm : Measurable f)
  (hf : ∀ a, Integrable f (κ a)):
  Measurable (fun a => ∫ x, f x ∂ κ a) := by
  -- The result type is E d = PiLp 2 (...), not Pi.
  -- We show measurability via the measurable equivalence with Pi.
  have h_ofLp_meas : Measurable (fun a => (∫ x, f x ∂ κ a).ofLp) := by
    apply measurable_pi_iff.mpr
    intro i
    have : (fun a => (∫ x, f x ∂ κ a).ofLp i) =
      (fun a => (∫⁻ x, ENNReal.ofReal (f x i) ∂ (κ a)).toReal) - fun a => (∫⁻ x, ENNReal.ofReal (-f x i) ∂ κ a).toReal := by
      ext a
      simp
      have := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (L := EuclideanSpace.proj i) (φ := f) (μ := κ a) ?_
      simp at this
      rw [←this]
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part]
      apply (integrable_pi_iff_euclidean f (κ a)).mpr
      exact hf a
      exact hf a
    rw [this]
    -- hfm : Measurable f where f : β → E d
    -- We need measurability of (fun b => (f b).ofLp i) : β → ℝ
    have hfm' : Measurable (fun b : β => ((f b).ofLp) i) := by
      apply (measurable_pi_apply i).comp
      exact (WithLp.measurable_ofLp 2 _).comp hfm
    apply Measurable.sub
    · apply Measurable.ennreal_toReal
      apply Measurable.lintegral_kernel
      apply Measurable.ennreal_ofReal
      exact hfm'
    · apply Measurable.ennreal_toReal
      apply Measurable.lintegral_kernel
      apply Measurable.ennreal_ofReal
      exact hfm'.neg
  -- Now compose with toLp
  have h_eq : (fun a => ∫ x, f x ∂ κ a) = fun a => WithLp.toLp 2 ((∫ x, f x ∂ κ a).ofLp) := by
    ext a
    rfl
  rw [h_eq]
  exact (WithLp.measurable_toLp 2 _).comp h_ofLp_meas

theorem bind_condExp_eq_of_condExp_eq
  {α β : Type*} [MeasurableSpace α] {m m₀ : MeasurableSpace β}
  (μ : Measure α) [IsFiniteMeasure μ]
  (κ : Kernel α β) [IsFiniteKernel κ]
  (f g : β → E d)
  (hfm : Measurable f)
  (hgm : Measurable[m] g)
  (hf : Integrable f (μ.bind κ))
  (hg : Integrable g (μ.bind κ))
  (hfκ : ∀ a, Integrable f (κ a))
  (hgκ : ∀ a, Integrable g (κ a))
  (hmm₀ : m ≤ m₀)
  (hfg : ∀ᵐ a ∂ μ, (κ a)[f | m] =ᵐ[κ a] g) :
  (μ.bind κ)[f | m] =ᵐ[μ.bind κ] g := by
    apply EventuallyEq.symm
    apply ae_eq_condExp_of_forall_setIntegral_eq
    case hg_eq =>
      intro s hms hs
      have hm₀s := hmm₀ s hms
      rw [←integral_indicator]
      apply Eq.trans
      apply integral_bind_euclidean
      case h₂ =>
        apply Eq.trans
        apply integral_congr_ae
        apply Eventually.mono hfg
        intro a ha
        simp
        apply Eq.trans
        apply integral_congr_ae
        apply Eventually.mono ha
        intro b hb
        have : s.indicator g b = s.indicator (κ a)[f|m] b := by
          by_cases hb' : b ∈ s
          case pos =>
            simp [hb']
            rw [hb]
          case neg =>
            simp [hb']
        exact this
        apply Eq.trans
        apply integral_indicator
        exact hm₀s
        exact setIntegral_condExp hmm₀ (hfκ a) hms
        rw [←integral_indicator]
        rw [integral_bind_euclidean]
        apply integral_congr_ae
        apply Eventually.of_forall
        intro a
        simp
        rw [integral_indicator]
        exact hm₀s
        apply (integrable_indicator_iff hm₀s).mpr
        exact hf.integrableOn (s := s)
        exact Measurable.indicator hfm hm₀s
        intro a
        apply (integrable_indicator_iff hm₀s).mpr
        exact (hfκ a).integrableOn (s := s)
        exact hm₀s
      apply (integrable_indicator_iff hm₀s).mpr
      exact hg.integrableOn (s := s)
      exact Measurable.indicator (hgm.mono hmm₀ (by simp)) hm₀s
      intro a
      apply (integrable_indicator_iff hm₀s).mpr
      exact (hgκ a).integrableOn (s := s)
      exact hm₀s
    exact hmm₀
    exact hf
    intro s hs hletop
    exact hg.integrableOn (s := s)
    exact hgm.aestronglyMeasurable (μ := μ.bind κ)

lemma measurable_pi_apply_piLE (n : ℕ):
  Measurable[piLE n] (fun x : ℕ → S => x n) := by
  apply measurable_iff_comap_le.mpr
  apply MeasurableSpace.comap_le_iff_le_map.mpr
  intro s hs
  unfold MeasurableSet
  unfold MeasurableSpace.MeasurableSet'
  unfold MeasurableSpace.map
  simp
  unfold MeasurableSet
  unfold MeasurableSpace.MeasurableSet'
  unfold piLE
  simp
  unfold MeasurableSpace.comap
  simp
  let idx : (↑(Set.Iic n) → S) → S := fun y => y ⟨n, by simp⟩
  refine ⟨idx ⁻¹' s, ?hm, ?heq⟩
  case hm =>
    have : Measurable idx := by apply measurable_pi_apply
    exact hs.preimage this
  case heq =>
    rw [←Set.preimage_comp]
    apply congrFun
    apply congrFun
    rfl

lemma measurable_frestrictLe_piLE
  (n : ℕ) :
  Measurable[piLE n]
  (frestrictLe (π := fun _ => S) n) := by
  apply measurable_iff_comap_le.mpr
  apply MeasurableSpace.comap_le_iff_le_map.mpr
  intro s hs
  unfold MeasurableSet
  unfold MeasurableSpace.MeasurableSet'
  unfold MeasurableSpace.map
  simp
  unfold MeasurableSet
  unfold MeasurableSpace.MeasurableSet'
  unfold piLE
  simp
  unfold MeasurableSpace.comap
  simp

  let reindex : (Set.Iic n → S) → (Finset.Iic n → S) :=
    fun x m => x ⟨m, by
      apply Set.mem_setOf_eq.mpr
      exact Finset.mem_Iic.mp m.2
      ⟩

  let s' := Set.preimage reindex s
  refine ⟨s', ?hm, ?heq⟩
  case hm =>
    have : Measurable reindex := by
      apply measurable_pi_iff.mpr
      intro m
      simp [reindex]
      apply measurable_pi_apply
    exact hs.preimage this
  case heq =>
    unfold s'
    rw [←Set.preimage_comp]
    apply congrFun
    apply congrFun
    rfl

private lemma measurable_φ_integral_kernel
  {M : HomMarkovChainSpec S}
  {Z : Type*} [MeasurableSpace Z]
  {n m : ℕ}
  {φ : Z × S → E d}
  {φ₁ : (Iic n → S) → Z}
  (hφm : Measurable φ)
  (hbdd : ∃ C, ∀ ω s, ‖φ.curry (φ₁ (frestrictLe (π := X S) n ω)) s‖ ≤ C)
  (hφ₁m : Measurable φ₁)
  : Measurable[piLE n] fun x =>
    ∫ (s : S), φ.curry (φ₁ (frestrictLe (π := X S) n x)) s ∂
      M.kernel.iter (m - n) (x n) := by
  let κ : Kernel[piLE n] (ℕ → S) S :=
    (M.kernel.iter (m - n)).comap (fun x : (ℕ → S) => x n)
    (by apply measurable_pi_apply_piLE)
  have := M.markov_kernel
  have : Measurable[piLE n] fun x =>
    ∫ (s : S), φ.curry (φ₁ (frestrictLe (π := fun _ => S) n x)) s ∂κ x := by
    apply Measurable.integral_kernel_prod_right (mα := piLE n) (κ := κ)
      (f := fun x s => φ.curry (φ₁ (frestrictLe (π := fun _ => S) n x)) s)
    simp
    apply hφm.comp
    apply Measurable.prod
    simp
    apply hφ₁m.comp
    apply (measurable_frestrictLe_piLE n).comp
    apply Measurable.fst
    apply measurable_id
    simp
    apply Measurable.snd
    apply measurable_id

    intro x
    apply integrable_of_norm_le
    apply Measurable.aestronglyMeasurable
    apply hφm.comp
    apply Measurable.prod
    simp
    simp
    apply measurable_id

    obtain ⟨C, hC⟩ := hbdd
    use C
    apply Eventually.of_forall
    intro y
    apply hC
  apply (Measurable.congr ?_) this
  ext1 x
  simp
  apply Integral.measure_congr
  simp [κ]

private lemma integrable_φ_integral_kernel
  {M : HomMarkovChainSpec S}
  {Z : Type*} [MeasurableSpace Z]
  {n m : ℕ}
  {φ : Z × S → E d}
  {φ₁ : (Iic n → S) → Z}
  (hφm : Measurable φ)
  (hbdd : ∃ C, ∀ ω s, ‖φ.curry (φ₁ (frestrictLe (π := X S) n ω)) s‖ ≤ C)
  (hφ₁m : Measurable φ₁)
  {μ : Measure (ℕ → S)} [IsFiniteMeasure μ]
  : Integrable (fun x =>
    ∫ s, φ (φ₁ (frestrictLe n x), s) ∂ M.kernel.iter (m - n) (x n)) μ := by
  have := M.markov_kernel
  apply Integrable.congr
  case h =>
    apply Eventually.of_forall
    intro x
    simp
    apply integral_congr_ae
    apply Eventually.of_forall
    intro s
    simp
    apply Function.curry_apply
  apply integrable_of_norm_le
  apply Measurable.aestronglyMeasurable
  apply Measurable.mono
  apply measurable_φ_integral_kernel hφm hbdd hφ₁m
  apply piLE.le
  rfl
  obtain ⟨C, hC⟩ := hbdd
  use C
  apply Eventually.of_forall
  intro x
  grw [norm_integral_le_of_norm_le (g := fun _ => C)]
  simp
  apply integrable_const
  apply Eventually.of_forall
  intro s
  apply hC

lemma measurable_iterates_update
  {M : HomMarkovChainSpec S}
  {Z : Type*} [MeasurableSpace Z]
  {n m : ℕ}
  (hnm : n ≤ m)
  {φ : Z × S → E d}
  {φ₁ : (Iic n → S) → Z}
  (hφm : Measurable φ)
  (hφ₁m : Measurable φ₁)
  : Measurable (iterates_update hnm φ φ₁) := by
  have := M.markov_kernel
  simp [iterates_update]
  apply hφm.comp
  apply Measurable.prod
  simp
  apply hφ₁m.comp
  apply Measurable.comp
  apply measurable_restrict₂
  apply measurable_restrict
  simp
  apply measurable_pi_apply

lemma integrable_iterates_update
  {M : HomMarkovChainSpec S}
  {Z : Type*} [MeasurableSpace Z]
  {n m : ℕ}
  (hnm : n ≤ m)
  {φ : Z × S → E d}
  {φ₁ : (Iic n → S) → Z}
  (hφm : Measurable φ)
  (hbdd : ∃ C, ∀ ω s, ‖φ.curry (φ₁ (frestrictLe (π := X S) n ω)) s‖ ≤ C)
  (hφ₁m : Measurable φ₁)
  {μ : Measure (ℕ → S)} [IsFiniteMeasure μ]
  : Integrable (iterates_update hnm φ φ₁) μ := by
  have := M.markov_kernel
  apply integrable_of_norm_le
  apply Measurable.aestronglyMeasurable
  apply measurable_iterates_update hnm hφm hφ₁m (M := M)
  obtain ⟨C, hC⟩ := hbdd
  use C
  apply Eventually.of_forall
  intro ω
  simp [iterates_update]
  apply hC

theorem condExp_iterates_update
  [MeasurableSingletonClass S]
  {Z : Type*} [MeasurableSpace Z]
  (M : HomMarkovChainSpec S)
  {n m : ℕ}
  (hnm : n ≤ m)
  (φ : Z × S → E d)
  (φ₁ : (Iic n → S) → Z)
  (hφm : Measurable φ)
  (hbdd : ∃ C, ∀ ω s, ‖φ.curry (φ₁ (frestrictLe (π := X S) n ω)) s‖ ≤ C)
  (hφ₁m : Measurable φ₁)
  (hInt : ∀ x₀, Integrable
    (iterates_update hnm φ φ₁) (traj_prob₀ M x₀))
  : (traj_prob M).1[iterates_update hnm φ φ₁| piLE n]
  =ᵐ[(traj_prob M).1]
    fun x => ∫ s, φ ((φ₁ (frestrictLe n x)), s) ∂ M.kernel.iter (m - n) (x n) := by
    have := M.markov_kernel
    simp [traj_prob]
    apply bind_condExp_eq_of_condExp_eq
    case hfg =>
      apply Eventually.of_forall
      intro x
      apply condExp_iterates_update_aux
      exact hφm
      exact hφ₁m
      exact hInt x
    apply measurable_iterates_update (M := M) hnm hφm hφ₁m
    apply measurable_φ_integral_kernel hφm hbdd hφ₁m
    apply integrable_iterates_update (M := M) hnm hφm hbdd hφ₁m
    apply integrable_φ_integral_kernel hφm hbdd hφ₁m
    intro x₀
    apply integrable_iterates_update (M := M) hnm hφm hbdd hφ₁m
    intro x₀
    apply integrable_φ_integral_kernel hφm hbdd hφ₁m
    apply piLE.le

end StochasticApproximation
