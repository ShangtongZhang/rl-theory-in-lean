/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

import RLTheory.Defs
import RLTheory.MeasureTheory.Group.Arithmetic
import RLTheory.StochasticApproximation.IIDSamples
import RLTheory.StochasticApproximation.MarkovSamples
import RLTheory.MarkovDecisionProcess.MarkovRewardProcess

open Real Finset Filter TopologicalSpace Filter MeasureTheory.Filtration MeasureTheory ProbabilityTheory StochasticApproximation StochasticMatrix Preorder RLTheory Matrix MarkovChain
open scoped MeasureTheory ProbabilityTheory Topology InnerProductSpace RealInnerProductSpace Gradient

namespace ReinforcementLearning.LinearTD

universe u
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

variable {d : ℕ}

structure LinearTDSpec extends FiniteMRP (S := S) where
  x : S → E d
  hx : LinearIndependent ℝ (fun i => fun s => x s i)
  α : ℕ → ℝ
  w₀ : E d

variable {spec : LinearTDSpec (S := S) (d := d)}

lemma LinearTDSpec.bdd_of_x :
  ∃ C, 0 ≤ C ∧ ∀ s, ‖spec.x s‖ ≤ C := by
  use Finset.univ.sup' (by simp) fun s => ‖spec.x s‖
  constructor
  simp
  intro s
  apply Finset.le_sup' fun s => ‖spec.x s‖
  simp

noncomputable def LinearTDSpec.update (w : E d) (y : S × S) : E d :=
  (spec.r y.1 + spec.γ * ⟪spec.x y.2, w⟫ - ⟪spec.x y.1, w⟫) • spec.x y.1

lemma LinearTDSpec.lipschitz_of_update :
  ∃ C, 0 ≤ C ∧ ∀ z z' y,
    ‖spec.update z y - spec.update z' y‖ ≤ C * ‖z - z'‖ := by
    obtain ⟨C, hCnonneg, hC⟩ := spec.bdd_of_x
    refine ⟨?L, ?hLnonneg, ?hL⟩
    case L => exact (|spec.γ| * C + C) * C
    case hLnonneg => positivity
    case hL =>
      unfold update
      intro z z' y
      rcases y with ⟨s, s'⟩
      rw [←sub_smul, norm_smul]
      rw [sub_sub_sub_comm, add_sub_add_comm]
      simp [-PiLp.inner_apply]
      rw [←mul_sub, ←inner_sub_right, ←inner_sub_right]
      grw [abs_sub_le (b := 0)]
      simp [-PiLp.inner_apply]
      rw [abs_mul]
      grw [abs_real_inner_le_norm, abs_real_inner_le_norm]
      rw [←mul_assoc]
      grw [hC, hC]
      apply le_of_eq
      ring

instance : MeasurableSpace (E d) := by infer_instance

omit [Nonempty S] in
lemma LinearTDSpec.measurable_of_udpate : Measurable (spec.update.uncurry) := by
      apply Measurable.smul
      apply Measurable.add
      apply Measurable.add
      apply Measurable.comp
      apply measurable_of_countable
      apply Measurable.fst
      apply Measurable.snd
      apply measurable_id
      apply Measurable.const_mul
      apply Measurable.inner
      apply Measurable.comp
      apply measurable_of_countable
      apply Measurable.snd
      apply measurable_snd
      apply measurable_fst
      apply measurable_neg_iff.mpr
      apply Measurable.inner
      apply Measurable.comp
      apply measurable_of_countable
      apply Measurable.fst
      apply measurable_snd
      apply measurable_fst
      apply Measurable.comp
      apply measurable_of_countable
      apply Measurable.fst
      apply measurable_snd

noncomputable def LinearTDSpec.expected_update (w : E d) : E d :=
  ∑ s, ∑ s', (spec.μ s * spec.P s s') • spec.update w ⟨s, s'⟩

lemma LinearTDSpec.lipschitz_of_expected_update :
  ∃ C, 0 ≤ C ∧ ∀ z z',
    ‖spec.expected_update z - spec.expected_update z'‖ ≤ C * ‖z - z'‖ := by
    have hP : RowStochastic spec.P := by infer_instance
    have hμ : StochasticVec spec.μ := by infer_instance
    obtain ⟨C, hCnonneg, hC⟩ := spec.lipschitz_of_update
    use C
    constructor
    exact hCnonneg
    intro z z'
    unfold expected_update
    simp_rw [←sum_sub_distrib, ←smul_sub]
    grw [norm_sum_le]
    rw [←one_mul C, ←hμ.rowsum, sum_mul, sum_mul]
    apply sum_le_sum
    intro s hs
    grw [norm_sum_le]
    simp_rw [norm_smul, norm_eq_abs, abs_mul, mul_assoc, ←mul_sum]
    rw [abs_of_nonneg]
    apply mul_le_mul_of_nonneg_left
    rw [←one_mul C, ←(hP.stochastic s).rowsum, sum_mul, sum_mul]
    apply sum_le_sum
    intro s' hs'
    grw [hC]
    rw [abs_of_nonneg]
    ring_nf
    rfl
    apply (hP.stochastic s).nonneg
    apply hμ.nonneg
    apply hμ.nonneg

lemma LinearTDSpec.measurable_of_expected_udpate :
  Measurable (spec.expected_update) := by
  apply Finset.measurable_sum
  intro s hs
  apply Finset.measurable_sum
  intro s' hs'
  apply Measurable.smul
  apply measurable_const
  apply measurable_pi_iff.mp
  apply spec.measurable_of_udpate.of_uncurry

noncomputable def LinearTDSpec.update_target (w : E d) (y : S × S) : E d :=
  spec.update w y + w

lemma LinearTDSpec.lipschitz_of_update_target :
  ∃ C, 0 ≤ C ∧ ∀ z z' y,
    ‖spec.update_target z y - spec.update_target z' y‖ ≤ C * ‖z - z'‖ := by
  obtain ⟨C, hCnonneg, hC⟩ := spec.lipschitz_of_update
  refine ⟨?L, ?hLnonneg, ?hL⟩
  case L => exact C + 1
  case hLnonneg => positivity
  case hL =>
    unfold update_target
    intro z z' y
    rw [add_sub_add_comm]
    grw [norm_add_le, hC]
    ring_nf
    rfl

omit [Nonempty S] in
lemma LinearTDSpec.measurable_of_udpate_target :
  Measurable (spec.update_target.uncurry) := by
  apply Measurable.add
  apply spec.measurable_of_udpate
  measurability

noncomputable def LinearTDSpec.expected_update_target :=
  spec.expected_update + id

lemma LinearTDSpec.unfold_expected_update_target (w : E d) :
  spec.expected_update_target w =
    ∑ s, ∑ s', (spec.μ s * spec.P s s') • spec.update_target w (s, s') := by
  have hP : RowStochastic spec.P := by infer_instance
  have hμ : StochasticVec spec.μ := by infer_instance
  simp [expected_update_target, update_target, expected_update]
  simp_rw [sum_add_distrib, ←sum_smul]
  simp
  simp_rw [←mul_sum, (hP.stochastic ?_).rowsum]
  simp [hμ.rowsum]

noncomputable def LinearTDSpec.X : Matrix S (Fin d) ℝ :=
  fun s i => spec.x s i

omit [Nonempty S] in
lemma LinearTDSpec.fullRank_of_X :
  ∀ z : E d, z ≠ 0 → spec.X *ᵥ z ≠ 0 := by
  intro z hz
  intro h
  apply hz
  ext i
  apply Fintype.linearIndependent_iff.mp spec.hx
  rw [←h]
  ext s'
  simp [mulVec, dotProduct]
  simp_rw [mul_comm]
  rfl

noncomputable def LinearTDSpec.A : Matrix (Fin d) (Fin d) ℝ :=
  spec.Xᵀ * spec.D * (spec.γ • spec.P - 1) * spec.X

noncomputable def LinearTDSpec.b : E d := (spec.Xᵀ * spec.D) *ᵥ spec.r

lemma LinearTDSpec.expected_update_in_matrix (w : E d) :
  spec.expected_update w = ↑(spec.A *ᵥ w) + spec.b := by
  have hP := (inferInstance : RowStochastic spec.P)
  simp [A, b]
  simp_rw [←mulVec_mulVec]
  rw [←mulVec_add, ←mulVec_add, sub_mulVec]
  rw [mulVec_mulVec, FiniteMRP.D]
  simp [mul_diagonal_mulVec, expected_update]
  apply sum_congr rfl
  intro s hs
  simp_rw [mulVec, dotProduct, X, Matrix.row, smul_apply,
    Matrix.mul_apply, ←smul_smul, ←smul_sum]
  apply congr rfl
  simp [update]
  simp_rw [X, smul_smul]
  simp_rw [mul_sub, mul_add]
  rw [←sum_smul]
  ext i
  simp
  conv_lhs =>
    congr; congr; rw [sum_add_distrib]; congr
    rw [←sum_mul, (hP.stochastic s).rowsum]
    rfl; congr; rfl; ext s'; rw [←mul_assoc, mul_comm (b := spec.γ)]; rfl
    rw [←sum_mul, (hP.stochastic s).rowsum]; rfl
  simp [X]
  apply Or.inl
  ring_nf
  simp
  apply congr
  apply congr
  rfl
  simp_rw [mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro s' hs'
  apply sum_congr rfl
  intro i hi
  ring
  apply sum_congr rfl
  intro i hi
  ring

instance : NegDefAsymm spec.A := by
  have hμpos := pos_of_stationary spec.μ spec.P
  constructor
  apply (posDefAsymm_iff (-spec.A)).mpr
  have : NegDefAsymm spec.K := by infer_instance
  have hK := (-spec.K).posDefAsymm_iff.mp this.nd
  constructor
  apply isHermitian_add_transpose_self
  intro x hx
  simp [add_mulVec, neg_mulVec, dotProduct_transpose_mulVec]
  have hK := hK.2 (spec.X *ᵥ x) (spec.fullRank_of_X x hx)
  simp [Matrix.add_mul, add_mulVec, neg_mulVec] at hK
  simp [←mulVec_mulVec, dotProduct_transpose_mulVec] at hK
  rw [LinearTDSpec.A, ←mulVec_mulVec, dotProduct_mulVec, Matrix.mul_assoc,
    ←vecMul_vecMul, ←dotProduct_mulVec, vecMul_transpose]
  exact hK

noncomputable def LinearTDSpec.td_fixed_point : E d := - spec.A⁻¹ *ᵥ spec.b

lemma LinearTDSpec.isFixedPoint_td_fixed_point :
  spec.expected_update spec.td_fixed_point = 0 := by
  simp [expected_update_in_matrix, td_fixed_point]
  simp [neg_mulVec]

instance : DecreaseAlong (half_sq_Lp (p := 2)) (half_sq_Lp' (p := 2))
  spec.expected_update_target := by
  constructor
  have : NegDefAsymm spec.A := by infer_instance
  obtain ⟨η, hηpos, hη⟩ := (posDefAsymm_iff' (-spec.A)).mp this.nd
  use η * 2
  constructor
  linarith
  intro z hz
  intro x
  have : half_sq_Lp' (x - z) = x - z := by
    unfold half_sq_Lp'
    ext i
    simp
  rw [this]
  unfold half_sq_Lp
  rw [LinearTDSpec.expected_update_target] at hz ⊢
  simp [-PiLp.inner_apply, LinearTDSpec.expected_update_in_matrix] at hz ⊢
  rw [←sub_zero (spec.b), ←hz, ←add_sub_assoc, add_sub_add_right_eq_sub,
    ←mulVec_sub]
  rw [←mul_assoc, mul_assoc (a := η), mul_inv_cancel₀]
  rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp, id, id]
  simp
  rw [dotProduct_comm]
  apply le_neg_of_le_neg
  rw [EuclideanSpace.norm_sq_eq]
  simp
  have := hη (x - z)
  simp [neg_mulVec, dotProduct_neg] at this
  rw [dotProduct] at this
  simp_rw [←pow_two] at this
  simp at this
  exact this
  simp

instance : LyapunovCandidate (d := d)
  (half_sq_Lp (p := 2)) (half_sq_Lp' (p := 2)) := by
  apply lyapunovCandidate_half_sq_Lp
  omega

instance : LyapunovFunction (half_sq_Lp (p := 2)) (half_sq_Lp' (p := 2))
  spec.expected_update_target := by
  apply LyapunovFunction.mk

variable {w : ℕ → (ℕ → (S × S)) → E d}

class LinearTDIterates where
  init : ∀ ω, w 0 ω = spec.w₀
  step : ∀ n ω, w (n + 1) ω =
    w n ω + spec.α n • spec.update (w n ω) (ω (n + 1))

theorem ae_tendsto_of_linearTD_iid
  (hw : LinearTDIterates (spec := spec) (w := w))
  (hα : RobbinsMonro spec.α) :
  ∀ᵐ ω ∂ spec.iid_samples,
    Tendsto (fun n => w n ω) atTop (𝓝 spec.td_fixed_point) := by
  have hw' : IteratesOfResidual w spec.w₀ spec.α spec.update_target := by
    constructor
    exact hw.init
    simp [LinearTDSpec.update_target]
    exact hw.step
  let φ : E d → ℝ := half_sq_Lp (p := 2)
  let φ' : E d → E d := half_sq_Lp' (p := 2)
  have : LyapunovFunction φ φ' spec.expected_update_target := by infer_instance
  have : IsProbabilityMeasure spec.iid_samples := by
      apply Subtype.property
  apply ae_tendsto_of_iterates_iid_samples
    (hx := hw')
    (hFm := spec.measurable_of_udpate_target)
    (hFlip := spec.lipschitz_of_update_target)
    (hfF := spec.unfold_expected_update_target)
    (hα := hα)
    (φ := φ) (φ' := φ')
    (f := spec.expected_update_target)
  case hf =>
    simp [LinearTDSpec.expected_update_target]
    exact spec.isFixedPoint_td_fixed_point
  case hφm =>
    apply measurable_of_half_sq_Lp
    simp
  case hgradφm =>
    apply measurable_of_gradient_half_sq_Lp
    simp

theorem ae_tendsto_of_linearTD_markov
  {ν : ℝ} (hν : ν ∈ Set.Ioo (2 / 3) 1)
  (hw : LinearTDIterates (spec := spec) (w := w))
  (hα : spec.α = fun n : ℕ => inv_poly ν 2 n) :
  ∀ᵐ ω ∂ spec.markov_samples,
    Tendsto (fun n => w n ω) atTop (𝓝 spec.td_fixed_point) := by
  have hw' : IteratesOfResidual w spec.w₀ spec.α spec.update_target := by
    constructor
    exact hw.init
    simp [LinearTDSpec.update_target]
    exact hw.step
  let φ : E d → ℝ := half_sq_Lp (p := 2)
  let φ' : E d → E d := half_sq_Lp' (p := 2)
  have : LyapunovFunction φ φ' spec.expected_update_target := by infer_instance
  have : IsProbabilityMeasure spec.iid_samples := by
      apply Subtype.property
  apply ae_tendsto_of_iterates_markov_samples_of_inv_poly
    (hν := hν)
    (hα := hα)
    (hx := hw')
    (hFm := spec.measurable_of_udpate_target)
    (hFlip := spec.lipschitz_of_update_target)
    (hfF := spec.unfold_expected_update_target)
    (φ := φ) (φ' := φ')
    (f := spec.expected_update_target)
  case hf =>
    simp [LinearTDSpec.expected_update_target]
    exact spec.isFixedPoint_td_fixed_point
  case hφm =>
    apply measurable_of_half_sq_Lp
    simp
  case hgradφm =>
    apply measurable_of_gradient_half_sq_Lp
    simp

end ReinforcementLearning.LinearTD
