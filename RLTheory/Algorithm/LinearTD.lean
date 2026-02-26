/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

import RLTheory.Tactic.Tactics
import RLTheory.Defs
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
      sub_smul_norm_expand
      rw [sub_sub_sub_comm, add_sub_add_comm]
      simp
      rw [←mul_sub, ←inner_sub_right, ←inner_sub_right]
      grw [abs_sub_le (b := 0)]
      simp
      grw [abs_real_inner_le_norm, abs_real_inner_le_norm]
      grw [hC, hC]
      ring_nf
      rfl

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
    rw [←one_mul C, ←hμ.rowsum, sum_mul, sum_mul]
    norm_sum_intro
    rename_i s hs
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
  ∀ z : E d, z ≠ 0 → spec.X *ᵥ z.ofLp ≠ 0 := by
  intro z hz hcontra
  apply hz
  have hli := spec.hx
  have heq : (fun i s => (spec.x s).ofLp i) = (fun i s => spec.X s i) := rfl
  rw [heq] at hli
  simp at hcontra
  have hcomb : ∑ i : Fin d, z.ofLp i • (fun s => spec.X s i) = 0 := by
    funext s
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hs := congrFun hcontra s
    simp only [Pi.zero_apply] at hs
    rw [←hs]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcoeffs := linearIndependent_iff'.mp hli (Finset.univ) (fun i => z.ofLp i) hcomb
  ext i
  exact hcoeffs i (Finset.mem_univ i)

noncomputable def LinearTDSpec.A : Matrix (Fin d) (Fin d) ℝ :=
  spec.Xᵀ * spec.D * (spec.γ • spec.P - 1) * spec.X

noncomputable def LinearTDSpec.b : Fin d → ℝ := (spec.Xᵀ * spec.D) *ᵥ spec.r

lemma LinearTDSpec.expected_update_in_matrix (w : E d) :
  spec.expected_update w = WithLp.toLp 2 ((spec.A *ᵥ w.ofLp) + spec.b) := by
  have hP := (inferInstance : RowStochastic spec.P)
  simp only [A, b]
  simp_rw [←mulVec_mulVec]
  rw [←mulVec_add, ←mulVec_add, sub_mulVec]
  rw [mulVec_mulVec, FiniteMRP.D]
  simp only [mul_diagonal_mulVec, expected_update]
  -- Both sides are in E d = PiLp 2 (Fin d → ℝ)
  -- We show they're equal by showing their underlying functions are equal
  ext k
  -- For PiLp 2, function application works component-wise
  -- First distribute .ofLp through the sums using WithLp.ofLp_sum
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.add_apply, Pi.sub_apply, mulVec, dotProduct]
  -- After simp, both sides should be sums of reals
  -- LHS: ∑ s, ∑ s', (μ s * P s s') * (update w (s, s')).ofLp k
  -- RHS: ∑ s, μ s * (... matrix computation ...)
  apply Finset.sum_congr rfl
  intro s _
  -- Goal: ∑ s', (μ s * P s s') * (update w (s, s')).ofLp k = μ s * (... matrix ...)
  -- Unfold update first to expose the inner structure
  simp only [update]
  -- Now update w (s, s') = (r s + γ⟪x s', w⟫ - ⟪x s, w⟫) • x s
  -- and (... • x s).ofLp k = (... ) * (x s).ofLp k
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  -- Now we can proceed with matrix manipulations
  simp_rw [X]
  -- The inner product ⟪x x', w⟫ = ∑ i, (x x').ofLp i * w.ofLp i
  -- And Xᵀ.col s k = (x s).ofLp k
  simp only [Matrix.transpose_apply, Matrix.col_apply]
  -- Rewrite LHS: ∑ x, μ s * P s x * ((r s + γ * ⟪x x, w⟫ - ⟪x s, w⟫) * (x s).ofLp k)
  -- First, rearrange the multiplications
  have hlhs : ∀ x', spec.μ s * spec.P s x' * ((spec.r s + spec.γ * ⟪spec.x x', w⟫ - ⟪spec.x s, w⟫) * (spec.x s).ofLp k) =
      spec.μ s * (spec.P s x' * (spec.r s + spec.γ * ⟪spec.x x', w⟫ - ⟪spec.x s, w⟫) * (spec.x s).ofLp k) := by
    intro x'; ring
  simp_rw [hlhs]
  rw [←Finset.mul_sum]
  -- Factor out (x s).ofLp k from inner sum
  have hinner : ∀ x', spec.P s x' * (spec.r s + spec.γ * ⟪spec.x x', w⟫ - ⟪spec.x s, w⟫) * (spec.x s).ofLp k =
      (spec.x s).ofLp k * (spec.P s x' * (spec.r s + spec.γ * ⟪spec.x x', w⟫ - ⟪spec.x s, w⟫)) := by
    intro x'; ring
  simp_rw [hinner]
  -- LHS: μ s * ∑ x, (x s).ofLp k * (P s x * (...))
  -- Use Finset.mul_sum to factor out (x s).ofLp k
  rw [←Finset.mul_sum]
  congr 1
  rw [mul_comm]
  congr 1
  -- Now: ∑ x, P s x * (r s + γ * ⟪x x, w⟫ - ⟪x s, w⟫) =
  --      ∑ x, (γ • P) s x * ⟪x x, w⟫ - ∑ x, 1 s x * ⟪x x, w⟫ + r s
  -- Goal: ∑ i, P s i * (r s + γ * ⟪x i, w⟫ - ⟪x s, w⟫) =
  --       ∑ x, (γ • P) s x * ∑ x_1, (x x).ofLp x_1 * w.ofLp x_1 - ∑ x, 1 s x * ∑ x_1, ... + r s
  -- First expand the inner product on the LHS to match RHS form
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  -- Now both sides have ∑ x_1, (x _).ofLp x_1 * w.ofLp x_1 form
  -- Expand LHS: P s i * (r s + γ * (∑ x_1, ...) - (∑ x_1, ...))
  conv_lhs =>
    arg 2; ext i
    rw [mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- Now: ∑ i, P s i * r s + ∑ i, P s i * (γ * ∑ ...) - ∑ i, P s i * (∑ ...) = RHS
  -- Use stochastic: ∑ i, P s i * r s = r s
  conv_lhs =>
    arg 1; arg 1
    rw [←Finset.sum_mul, (hP.stochastic s).rowsum, one_mul]
  -- ∑ i, P s i * (∑ ...) where the inner sum is over x s (constant in i) = ∑ ...
  conv_lhs =>
    arg 2
    rw [←Finset.sum_mul, (hP.stochastic s).rowsum, one_mul]
  -- Simplify matrix terms on RHS
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  -- Goal: r s + (∑ x, P s x * γ * ∑ x_1, w.ofLp x_1 * (x x).ofLp x_1 - ∑ x, w.ofLp x * (x s).ofLp x) =
  --       ∑ x, γ * P s x * ∑ x_1, (x x).ofLp x_1 * w.ofLp x_1 -
  --           ∑ x, (if s = x then 1 else 0) * ∑ x_1, (x x).ofLp x_1 * w.ofLp x_1 + r s
  -- Handle the identity matrix term: ∑ x, (if s = x then 1 else 0) * f x = f s
  have hident : ∑ x, (if s = x then (1 : ℝ) else 0) * ∑ x_1, (spec.x x).ofLp x_1 * w.ofLp x_1 =
      ∑ x_1, (spec.x s).ofLp x_1 * w.ofLp x_1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hs; exact absurd (Finset.mem_univ s) hs
  rw [hident]
  -- Now both sides have similar structure, use ring-like reasoning
  have hcomm1 : ∀ i, spec.P s i * (spec.γ * ∑ x_1, w.ofLp x_1 * (spec.x i).ofLp x_1) =
      spec.γ * spec.P s i * ∑ x_1, (spec.x i).ofLp x_1 * w.ofLp x_1 := by
    intro i
    have h1 : spec.P s i * (spec.γ * ∑ x_1, w.ofLp x_1 * (spec.x i).ofLp x_1) =
        spec.γ * spec.P s i * ∑ x_1, w.ofLp x_1 * (spec.x i).ofLp x_1 := by ring
    rw [h1]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hcomm1]
  have hcomm2 : ∑ x, w.ofLp x * (spec.x s).ofLp x = ∑ x, (spec.x s).ofLp x * w.ofLp x := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcomm2]
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
  simp
  -- x : Fin d →₀ ℝ (Finsupp), need to convert to E d for fullRank_of_X
  set x' : E d := WithLp.toLp 2 (fun i => x i) with hx'_def
  have hx' : x' ≠ 0 := by
    simp only [x', ne_eq, WithLp.toLp_eq_zero]
    intro h
    apply hx
    ext i
    have := congr_fun h i
    simp at this
    exact this
  have hK := hK.dotProduct_mulVec_pos (spec.fullRank_of_X x' hx')
  simp only [star_trivial, add_mulVec, neg_mulVec, dotProduct_add,
    dotProduct_neg, dotProduct_transpose_mulVec] at hK
  -- Convert goal from Finsupp.sum to dotProduct form
  have hx'_eq : x'.ofLp = fun i => x i := rfl
  -- The goal is: 0 < x.sum (fun i xi => x.sum (fun j xj => xi * (-A i j + -A j i) * xj))
  -- hK is: 0 < -(X *ᵥ x' ⬝ᵥ K *ᵥ X *ᵥ x') + -(X *ᵥ x' ⬝ᵥ K *ᵥ X *ᵥ x')
  -- We need to show the Finsupp sum equals -2 * (x' ⬝ᵥ A *ᵥ x')
  have goal_eq : (x.sum fun i xi => x.sum fun j xj => xi * (-spec.A i j + -spec.A j i) * xj) =
      (fun i => x i) ⬝ᵥ ((-spec.A + -spec.Aᵀ) *ᵥ (fun i => x i)) := by
    simp only [dotProduct, mulVec, add_apply, neg_apply, transpose_apply]
    rw [Finsupp.sum_fintype]
    · apply Finset.sum_congr rfl; intro i _
      rw [Finsupp.sum_fintype]
      · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      · intro j; ring
    · intro i
      rw [Finsupp.sum_fintype]
      · simp only [zero_mul, Finset.sum_const_zero]
      · intro j; ring
  rw [goal_eq]
  simp only [add_mulVec, neg_mulVec, dotProduct_add, dotProduct_neg,
    dotProduct_transpose_mulVec]
  -- Now goal: 0 < -(x ⬝ᵥ A *ᵥ x) + -(x ⬝ᵥ A *ᵥ x)
  -- hK: 0 < -(X *ᵥ x' ⬝ᵥ K *ᵥ X *ᵥ x') + -(X *ᵥ x' ⬝ᵥ K *ᵥ X *ᵥ x')
  -- A = Xᵀ * D * (γP - 1) * X, K = D * (γP - 1)
  -- so x ⬝ᵥ A *ᵥ x = (X *ᵥ x) ⬝ᵥ K *ᵥ (X *ᵥ x)
  have hA : ∀ v : Fin d → ℝ, v ⬝ᵥ spec.A *ᵥ v = (spec.X *ᵥ v) ⬝ᵥ spec.K *ᵥ (spec.X *ᵥ v) := by
    intro v
    -- A = Xᵀ * D * (γP - 1) * X = Xᵀ * K * X where K = D * (γP - 1)
    have hAK : spec.A = spec.Xᵀ * spec.K * spec.X := by
      simp only [LinearTDSpec.A, FiniteMRP.K, Matrix.mul_assoc]
    rw [hAK, ←mulVec_mulVec, ←mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [hA]
  convert hK using 2

noncomputable def LinearTDSpec.td_fixed_point : E d := WithLp.toLp 2 (- spec.A⁻¹ *ᵥ spec.b)

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
  intro z hz x
  have : half_sq_Lp' (x - z) = x - z := by
    unfold half_sq_Lp'
    ext i
    simp
  rw [this]
  unfold half_sq_Lp
  rw [LinearTDSpec.expected_update_target] at hz ⊢
  -- expected_update_target = expected_update + id
  -- expected_update w = WithLp.toLp 2 ((A *ᵥ w.ofLp) + b)
  simp only [LinearTDSpec.expected_update_in_matrix, Pi.add_apply, id] at hz ⊢
  -- hz : z = WithLp.toLp 2 (A *ᵥ z.ofLp + b) + z
  -- This means WithLp.toLp 2 (A *ᵥ z.ofLp + b) = 0
  have hz' : WithLp.toLp 2 (spec.A *ᵥ z.ofLp + spec.b) = 0 := by
    have h : WithLp.toLp 2 (spec.A *ᵥ z.ofLp + spec.b) + z = z := by rw [←hz]
    have := (add_eq_right).mp h
    exact this
  -- Goal: ⟪x - z, WithLp.toLp 2 (A *ᵥ x.ofLp + b) + x⟫ ≤ -(η * 2 * (1/2 * ‖x - z‖^2))
  -- Simplify: WithLp.toLp 2 (A *ᵥ x.ofLp + b) + x - x = WithLp.toLp 2 (A *ᵥ x.ofLp + b)
  simp only [add_sub_cancel_right]
  -- Rewrite using hz': A *ᵥ x.ofLp + b = A *ᵥ (x - z).ofLp + (A *ᵥ z.ofLp + b)
  -- Since A *ᵥ z.ofLp + b wraps to 0, we get A *ᵥ (x - z).ofLp
  have heq : WithLp.toLp 2 (spec.A *ᵥ x.ofLp + spec.b) =
      WithLp.toLp 2 (spec.A *ᵥ (x - z).ofLp) := by
    have h1 : spec.A *ᵥ x.ofLp + spec.b = spec.A *ᵥ (x - z).ofLp + (spec.A *ᵥ z.ofLp + spec.b) := by
      simp only [WithLp.ofLp_sub, mulVec_sub]
      ring
    rw [h1, WithLp.toLp_add, hz', add_zero]
  rw [heq]
  -- Goal: ⟪x - z, WithLp.toLp 2 (A *ᵥ (x - z).ofLp)⟫ ≤ -(η * 2) * (1/2 * ‖x - z‖^2)
  -- RHS = -η * ‖x - z‖^2
  have hrhs : -(η * 2) * (1 / 2 * ‖x - z‖ ^ 2) = -η * ‖x - z‖ ^ 2 := by ring
  rw [hrhs]
  -- Now use hη: η * v ⬝ᵥ v ≤ v ⬝ᵥ (-A) *ᵥ v
  -- which means ⟪v, A *ᵥ v⟫ ≤ -η * ‖v‖^2
  set v := x - z with hv
  -- ⟪v, toLp (A *ᵥ v.ofLp)⟫ = v.ofLp ⬝ᵥ (A *ᵥ v.ofLp)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  -- Now we have (A *ᵥ v.ofLp) ⬝ᵥ v.ofLp ≤ -η * ‖v‖^2
  have hη' := hη v.ofLp
  simp only [neg_mulVec, dotProduct_neg] at hη'
  -- hη' : η * (v.ofLp ⬝ᵥ v.ofLp) ≤ -(v.ofLp ⬝ᵥ A *ᵥ v.ofLp)
  -- i.e., v.ofLp ⬝ᵥ A *ᵥ v.ofLp ≤ -η * (v.ofLp ⬝ᵥ v.ofLp)
  have h1 : v.ofLp ⬝ᵥ spec.A *ᵥ v.ofLp ≤ -η * (v.ofLp ⬝ᵥ v.ofLp) := by linarith
  -- We need (A *ᵥ v.ofLp) ⬝ᵥ v.ofLp, use commutativity
  rw [dotProduct_comm]
  -- ‖v‖^2 = v.ofLp ⬝ᵥ v.ofLp for EuclideanSpace
  have hnorm : ‖v‖ ^ 2 = v.ofLp ⬝ᵥ v.ofLp := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.norm_eq_abs, sq_abs, sq]
  rw [hnorm]
  exact h1

instance : LyapunovCandidate (d := d)
  (half_sq_Lp (p := 2)) (half_sq_Lp' (p := 2)) :=
  lyapunovCandidate_half_sq_L2

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
