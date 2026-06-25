/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

import RLTheory.Defs
import RLTheory.MeasureTheory.MeasurableSpace.Constructions
import RLTheory.MeasureTheory.Group.Arithmetic
import RLTheory.StochasticApproximation.IIDSamples
import RLTheory.StochasticApproximation.MarkovSamples
import RLTheory.Probability.MarkovChain.Defs
import RLTheory.Probability.MarkovChain.Finite.Defs
import RLTheory.Probability.MarkovChain.Trajectory
import RLTheory.MarkovDecisionProcess.MarkovDecisionProcess

open ENNReal NNReal Real Finset Filter TopologicalSpace Filter MeasureTheory.Filtration MeasureTheory ProbabilityTheory StochasticApproximation StochasticMatrix Preorder RLTheory Matrix MarkovChain
open scoped MeasureTheory ProbabilityTheory Topology InnerProductSpace RealInnerProductSpace Gradient

lemma abs_sup'_sub_sup'_le_sup'
  {ι} {s : Finset ι} (hs : s.Nonempty) {x y : ι → ℝ} :
  |s.sup' hs x - s.sup' hs y| ≤ s.sup' hs (fun i => |x i - y i|) := by
  apply abs_le.mpr
  constructor
  case left =>
    simp
    intro i hi
    have : y i = x i + (y i - x i) := by ring_nf
    rw [this]
    apply add_le_add
    simp
    use i
    grw [le_abs_self (y i - x i)]
    rw [←neg_sub, abs_neg]
    simp
    use i
  case right =>
    simp
    obtain ⟨i, his, hi⟩ := exists_mem_eq_sup' hs fun i => |x i - y i|
    use i
    constructor
    exact his
    intro j hj
    have : x j = x j - y j + y j := by ring_nf
    rw [this]
    apply add_le_add
    grw [le_abs_self (x j - y j)]
    rw [←hi]
    apply (le_sup'_iff hs).mpr
    use j
    simp
    use j

lemma sum_probability_singleton {ι} [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]
  (μ : ProbabilityMeasure ι) :
  ∑ i, μ {i} = 1 := by
  have : ∑ i, μ.1 {i} = 1 := by simp
  have := congrArg ENNReal.toNNReal this
  conv_rhs at this => simp
  rw [ENNReal.toNNReal_sum] at this
  rw [←this]
  apply sum_congr rfl
  intro i hi
  exact_mod_cast rfl
  simp

namespace ReinforcementLearning.QLearning

universe u
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable {A: Type u} [Fintype A] [DecidableEq A] [Nonempty A]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

noncomputable def sa_to_fin (y : S × A) : Fin (Fintype.card (S × A)) :=
  Fintype.equivFin (S × A) y

noncomputable def fin_to_sa (y : Fin (Fintype.card (S × A))) : S × A :=
  (Fintype.equivFin (S × A)).symm y

variable {d : ℕ}
abbrev LinftySpace (d : ℕ) := PiLp ⊤ (fun _ : Fin d => ℝ)
def toLinfty (x : E d) : LinftySpace d := x
def toL2 (x : LinftySpace d) : E d := x
def ftoLinfty (f : E d → E d) : LinftySpace d → LinftySpace d :=
  toLinfty ∘ f ∘ toL2

local notation (priority := 2000) "‖" x "‖∞" =>
  @Norm.norm (PiLp ⊤ fun _ => ℝ) _ x

structure QLearningSpec extends FiniteMDP (S := S) (A := A) where
  α : ℕ → ℝ
  q₀ : E (Fintype.card (S × A))

variable {spec : QLearningSpec (S := S) (A := A)}

noncomputable def QLearningSpec.maxₐ
  (q : E (Fintype.card (S × A))) (s : S) : ℝ :=
  Finset.univ.sup' (by simp) (fun a => q (sa_to_fin (s, a)))

noncomputable def QLearningSpec.bellman_op
  (q : E (Fintype.card (S × A))) : E (Fintype.card (S × A)) :=
  fun i =>
    let sa := fin_to_sa i
    spec.r sa + spec.γ * ∑ s', spec.P sa {s'} * maxₐ q s'

lemma QLearningSpec.contraction_of_bellman_op :
  ContractingWith ⟨spec.γ, by exact spec.hγ.1⟩ (ftoLinfty spec.bellman_op)
  := by
  constructor
  exact_mod_cast spec.hγ.2
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro q q'
  unfold ftoLinfty
  simp [toL2, toLinfty]
  unfold bellman_op
  simp
  rw [Pi.sub_def]
  simp
  simp_rw [←mul_sub, ←sum_sub_distrib, ←mul_sub]
  conv_lhs => simp [Norm.norm]
  apply (ciSup_le_iff ?_).mpr
  intro i
  rw [abs_mul]
  grw [abs_sum_le_sum_abs]
  simp_rw [abs_mul]
  rw [abs_of_nonneg spec.hγ.1]
  apply mul_le_mul_of_nonneg_left
  have : ∀ s', |maxₐ q s' - maxₐ q' s'| ≤ ‖q - q'‖ := by
    intro s'
    simp [maxₐ]
    grw [abs_sup'_sub_sup'_le_sup' (by simp)]
    simp
    intro a'
    apply LE.le.trans
    rotate_left
    apply PiLp.norm_apply_le (p := ⊤) (q - q') (sa_to_fin (s', a'))
    simp
  grw [sum_le_sum]
  rotate_left
  intro s' hs'
  grw [this s']
  exact spec.hγ.1
  apply Set.Finite.bddAbove
  apply Finite.Set.finite_range
  rw [←sum_mul]
  conv_rhs => rw [←one_mul ‖q - q'‖]
  apply mul_le_mul_of_nonneg_right
  apply le_of_eq
  simp
  simp [←coe_sum, sum_probability_singleton]
  apply norm_nonneg

noncomputable def QLearningSpec.optimal_q :=
  toL2 (ContractingWith.fixedPoint (ftoLinfty spec.bellman_op)
    spec.contraction_of_bellman_op)

noncomputable def QLearningSpec.x (y : S × A) : E (Fintype.card (S × A)) :=
  fun i => if i = sa_to_fin y then 1 else 0

noncomputable def QLearningSpec.update
  (q : E (Fintype.card (S × A))) (y : (S × A) × (S × A)) :
  E (Fintype.card (S × A)) :=
  (spec.r y.1 + spec.γ * maxₐ q y.2.1 - q (sa_to_fin y.1)) • x y.1

omit [Nonempty S] in
lemma QLearningSpec.lipschitz_of_update :
  ∃ C, 0 ≤ C ∧ ∀ z z' y,
    ‖spec.update z y - spec.update z' y‖ ≤ C * ‖z - z'‖ := by
    refine ⟨?L, ?hLnonneg, ?hL⟩
    case L => exact (|spec.γ| + 1)
    case hLnonneg => positivity
    case hL =>
      unfold update
      intro z z' y
      rcases y with ⟨y, y'⟩
      rw [←sub_smul, norm_smul]
      rw [sub_sub_sub_comm, add_sub_add_comm]
      simp [-PiLp.inner_apply]
      rw [←mul_sub]
      grw [abs_sub_le (b := 0)]
      simp [-PiLp.inner_apply]
      rw [abs_mul]
      simp [maxₐ]
      grw [abs_sup'_sub_sup'_le_sup' (by simp)]
      have := PiLp.norm_apply_le (p := ⊤) (z' - z) (sa_to_fin y)
      simp at this
      grw [this]
      conv_lhs => simp [PiLp.norm_eq_sum, x]
      grw [sup'_le (a := ‖z - z'‖∞)]
      grw [Linfty_le_Lp, Linfty_le_Lp]
      apply le_of_eq
      rw [←neg_sub (b := z'), norm_neg (a := z - z')]
      ring_nf
      simp
      simp
      intro a' ha'
      have := PiLp.norm_apply_le (p := ⊤) (z - z') (sa_to_fin (y'.1, a'))
      simp at this
      exact this

omit [Nonempty S] in
lemma QLearningSpec.measurable_of_udpate : Measurable (spec.update.uncurry)
  := by
  apply Measurable.smul
  apply Measurable.add
  apply Measurable.add
  apply Measurable.comp
  apply measurable_of_countable
  apply Measurable.comp
  apply Measurable.fst
  apply measurable_id
  apply Measurable.snd
  apply measurable_id
  apply Measurable.mul
  apply measurable_const
  simp [maxₐ]
  apply Measurable.congr
  ext wy
  rw [sup'_univ_eq_ciSup]
  apply Measurable.iSup
  intro a'
  let f : E (Fintype.card (S × A)) → (S × A) × S × A → ℝ :=
    fun q y => q (sa_to_fin (y.2.1, a'))
  apply Measurable.congr (f := f.uncurry)
  rfl
  apply measurable_uncurry_of_continuous_of_measurable
  intro y
  simp [f]; apply continuous_pi_iff.mp; apply continuous_id
  intro q
  simp [f, sa_to_fin]
  apply Measurable.comp (by apply measurable_of_countable)
  apply Measurable.comp (by apply measurable_of_countable)
  apply Measurable.prodMk
  apply Measurable.fst
  apply Measurable.snd
  apply measurable_id
  apply measurable_const
  apply Measurable.neg
  let f : E (Fintype.card (S × A)) → (S × A) × S × A → ℝ :=
    fun q y => q (sa_to_fin y.1)
  apply Measurable.congr (f := f.uncurry)
  rfl
  apply measurable_uncurry_of_continuous_of_measurable
  intro y
  simp [f]; apply continuous_pi_iff.mp; apply continuous_id
  intro q
  simp [f, sa_to_fin]
  apply Measurable.comp (by apply measurable_of_countable)
  apply Measurable.comp (by apply measurable_of_countable)
  apply Measurable.fst
  apply measurable_id
  unfold QLearningSpec.x
  apply measurable_pi_iff.mpr
  intro q
  let f : E (Fintype.card (S × A)) → (S × A) × S × A → ℝ :=
    fun w y => if q = sa_to_fin y.1 then 1 else 0
  apply Measurable.congr (f := f.uncurry)
  rfl
  apply measurable_uncurry_of_continuous_of_measurable
  intro y
  simp [f]
  apply continuous_const
  intro w
  simp [f]
  apply measurable_of_countable

noncomputable def QLearningSpec.expected_update
  (q : E (Fintype.card (S × A))) : E (Fintype.card (S × A)) :=
  ∑ y, ∑ y', (spec.MRP.μ y * spec.MRP.P y y') • spec.update q (y, y')

noncomputable def QLearningSpec.update_target
  (q : E (Fintype.card (S × A))) (y : (S × A) × (S × A)) :
  E (Fintype.card (S × A)) :=
  spec.update q y + q

omit [Nonempty S] in
lemma QLearningSpec.lipschitz_of_update_target :
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
lemma QLearningSpec.measurable_of_udpate_target :
  Measurable (spec.update_target.uncurry) := by
  apply Measurable.add
  apply spec.measurable_of_udpate
  measurability

noncomputable def QLearningSpec.expected_update_target :=
  spec.expected_update + id

lemma QLearningSpec.expected_update_target_eq
  (q : E (Fintype.card (S × A))) :
  spec.expected_update_target q =
    fun i => spec.MRP.μ (fin_to_sa i) * (spec.bellman_op q - q) i + q i
  := by
  have hP : RowStochastic spec.MRP.P := by infer_instance
  simp [expected_update_target, expected_update, update]
  simp [←Pi.add_def]
  simp_rw [smul_smul, ←sum_smul, mul_assoc, ←mul_sum]
  let g := fun i =>
    let sa := fin_to_sa i
    (spec.MRP.μ sa * ∑ y, spec.MRP.P sa y *
      (spec.r sa + spec.γ * maxₐ q y.1 - q i)) • x sa
  rw [sum_equiv (s := univ) (t := univ) (Fintype.equivFin (S × A)) (g := g)]
  simp [g]
  ext i
  rw [Finset.sum_apply]
  simp [x]
  have : ∀ y, i = sa_to_fin (fin_to_sa y) ↔ i = y := by simp [sa_to_fin, fin_to_sa]
  conv_lhs =>
    congr; rfl; ext y; rw [if_congr (this y) (by rfl) (by rfl)]
  simp
  apply Or.inl
  simp_rw [mul_sub, sum_sub_distrib, ←sum_mul, mul_add, sum_add_distrib, ←sum_mul]
  simp [(hP.stochastic (fin_to_sa i)).rowsum, bellman_op]
  move_mul [spec.γ]
  simp [←sum_mul]
  apply Or.inl
  simp_rw [FiniteMDP.MRP.P_apply ?_]
  simp [Fintype.sum_prod_type]
  simp_rw [mul_assoc, ←mul_sum]
  apply sum_congr rfl
  intro s' hs'
  simp
  apply Or.inl
  simp [←sum_mul, ←coe_sum, sum_probability_singleton]
  simp
  intro y hy
  have : y = fin_to_sa (sa_to_fin y) := by simp [sa_to_fin, fin_to_sa]
  nth_rw 1 [this]
  nth_rw 2 [this]
  nth_rw 3 [this]
  nth_rw 5 [this]
  simp [sa_to_fin, g]

lemma QLearningSpec.unfold_expected_update_target
  (q : E (Fintype.card (S × A))) :
  spec.expected_update_target q =
    ∑ y, ∑ y', (spec.MRP.μ y * spec.MRP.P y y') • spec.update_target q (y, y')
    := by
  have hP : RowStochastic spec.MRP.P := by infer_instance
  have hμ : StochasticVec spec.MRP.μ := by infer_instance
  simp [expected_update_target, update_target, expected_update]
  simp_rw [sum_add_distrib, ←sum_smul]
  simp
  simp_rw [←mul_sum, (hP.stochastic ?_).rowsum]
  simp [hμ.rowsum]

lemma QLearningSpec.isFixedPoint_optimal_q :
  spec.expected_update_target spec.optimal_q = spec.optimal_q := by
  simp [expected_update_target_eq]
  ext i
  simp
  apply Or.inr
  have := ContractingWith.fixedPoint_isFixedPt spec.contraction_of_bellman_op
  simp [Function.IsFixedPt] at this
  have := congrFun this i
  simp [optimal_q, toL2]
  simp [←this]
  unfold ftoLinfty
  simp [toL2, toLinfty]

lemma QLearningSpec.contraction_of_expected_update_target :
  ∃ η, 0 ≤ η ∧ η < 1 ∧ ∀ q q',
    ‖spec.expected_update_target q - spec.expected_update_target q'‖∞ ≤
      η * ‖q - q'‖∞ := by
  have hμ : StochasticVec spec.MRP.μ := by infer_instance
  let μmin := Finset.inf' (s := univ) (by simp) spec.MRP.μ
  obtain ⟨ymin, _, _⟩ := exists_mem_eq_inf' (s := univ) (by simp) spec.MRP.μ
  have : 0 < μmin := by
    simp [μmin]
    intro s a
    apply pos_of_stationary spec.MRP.μ spec.MRP.P
  have : μmin ≤ 1 := by
    simp [μmin]
    use ymin.1
    use ymin.2
    apply hμ.le_one
  have := spec.hγ
  refine ⟨?η, ?hηnonneg, ?hηlt, ?hη⟩
  case η => exact 1 - μmin * (1 - spec.γ)
  case hηnonneg =>
    simp
    apply mul_le_one₀
    linarith
    linarith
    linarith
  case hηlt =>
    simp
    apply @_root_.mul_pos
    linarith
    linarith
  case hη =>
    intro q q'
    simp [expected_update_target_eq]
    conv_lhs => simp [Norm.norm]
    apply (ciSup_le_iff ?_).mpr
    intro i
    rw [add_sub_add_comm, ←mul_sub, sub_sub_sub_comm, mul_sub, sub_add,
      ←sub_one_mul, sub_eq_add_neg, ←neg_mul, neg_sub]
    grw [abs_add_le]
    simp_rw [abs_mul]
    have := PiLp.norm_apply_le (p := ⊤) (q - q') (i)
    simp at this
    grw [this]
    have := PiLp.norm_apply_le (p := ⊤)
      (spec.bellman_op q - spec.bellman_op q') (i)
    simp at this
    grw [this]
    have := spec.contraction_of_bellman_op
    have := lipschitzWith_iff_norm_sub_le.mp this.2 q q'
    unfold ftoLinfty at this
    simp [toL2, toLinfty] at this
    grw [this]
    rw [←mul_assoc, ←add_mul]
    apply mul_le_mul_of_nonneg_right
    rw [abs_of_nonneg, abs_of_nonneg, add_sub_assoc', add_comm,
      ←add_sub_assoc', ←mul_sub_one, ←neg_sub, mul_neg, ←sub_eq_add_neg]
    apply sub_le_sub_left
    apply mul_le_mul_of_nonneg_right
    apply inf'_le
    simp
    linarith [spec.hγ.2]
    simp
    rw [←hμ.rowsum]
    apply single_le_sum
    intro y hy
    apply hμ.nonneg
    simp
    apply hμ.nonneg
    apply norm_nonneg
    apply Set.Finite.bddAbove
    apply Finite.Set.finite_range

noncomputable def QLearningSpec.pmin_aux :=
  let η := spec.contraction_of_expected_update_target.choose
  1 / (log (1 / η) / log (Fintype.card (S × A)))

noncomputable def QLearningSpec.pmin : ℕ := max 2 (⌈spec.pmin_aux⌉₊ + 1)

variable {p : ℕ}

instance : DecreaseAlong (half_sq_Lp (p := spec.pmin))
  (half_sq_Lp' (p := spec.pmin)) spec.expected_update_target := by
  have : 2 ≤ spec.pmin := by simp [QLearningSpec.pmin]
  have : Fact (1 ≤ (spec.pmin : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  have : Fact (2 ≤ (spec.pmin : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  set η := spec.contraction_of_expected_update_target.choose with hηdef
  obtain ⟨hηnonneg, hηlt, hη⟩ :=
    spec.contraction_of_expected_update_target.choose_spec
  rw [←hηdef] at hηnonneg hηlt hη
  constructor
  refine ⟨?η, ?hηpos, ?hη⟩
  case η =>
    exact 2 * (1 - Fintype.card (S × A) ^ (spec.pmin : ℝ)⁻¹ * η)
  case hηpos =>
    by_cases hη0 : 0 = η
    simp [←hη0]
    by_cases hsa1 : (1 : ℝ) = Fintype.card (S × A)
    simp at hsa1 ⊢
    rw [←hsa1]
    simp [hηlt]
    have hcard : 1 < Fintype.card (S × A) := by
      apply lt_of_le_of_ne
      apply Nat.succ_le_of_lt
      apply Fintype.card_pos_iff.mpr
      infer_instance
      exact_mod_cast hsa1
    simp at hcard
    have : spec.pmin_aux < spec.pmin := by
      simp [QLearningSpec.pmin]
      apply Or.inr
      apply (Nat.le_ceil spec.pmin_aux).trans_lt
      linarith
    have : (↑spec.pmin)⁻¹ < (spec.pmin_aux)⁻¹ := by
      gcongr
      simp [QLearningSpec.pmin_aux]
      rw [←hηdef]
      apply div_pos
      apply log_pos
      exact_mod_cast hcard
      simp
      apply log_neg
      apply lt_of_le_of_ne hηnonneg hη0
      exact hηlt
    simp
    apply lt_of_lt_of_le (b := (Fintype.card (S × A) ^ spec.pmin_aux⁻¹ * η))
    simp
    gcongr
    apply Real.rpow_lt_rpow_of_exponent_lt
    exact_mod_cast hcard
    exact this
    rw [QLearningSpec.pmin_aux, ←hηdef]
    simp
    apply le_of_eq
    rw [div_eq_mul_inv, mul_comm (a := -log η), Real.rpow_mul,
      Real.rpow_inv_log]
    simp [←Real.log_inv]
    rw [Real.exp_log, inv_mul_cancel₀]
    intro h; exact hη0 h.symm
    apply inv_pos_of_pos
    apply lt_of_le_of_ne hηnonneg hη0
    apply LT.lt.trans (b := 1) (by simp) (by exact_mod_cast hcard)
    apply ne_of_gt
    exact_mod_cast hcard
    apply LE.le.trans (b := 1) (by simp)
    apply le_of_lt (by exact_mod_cast hcard)
  case hη =>
    intro y hy
    intro x
    set T := spec.expected_update_target
    have : T x - x = T x - T y + (y - x) := by
      rw [←hy]
      simp
    rw [this, inner_add_right, ←neg_sub x y, inner_neg_right]
    have := inner_gradient_half_sq_Lp_self
      (p := spec.pmin) (by linarith) (x - y)
    simp [-PiLp.inner_apply, StochasticApproximation.toL2] at this
    rw [this]
    apply LE.le.trans
    apply add_le_add
    apply le_of_abs_le
    simp
    grw [abs_sum_le_sum_abs]
    rfl
    conv_lhs =>
      congr; congr; rfl; ext i
      rw [abs_mul, mul_comm]
    grw [inner_abs_gradient_half_sq_Lp_le (p := spec.pmin) (by linarith),
      Lp_le_Linfty]
    rw [←Pi.sub_def]
    grw [hη, Linfty_le_Lp (p := spec.pmin)]
    simp [half_sq_Lp]
    ring_nf
    rfl
    linarith
    linarith

instance : LyapunovCandidate (d := d)
  (half_sq_Lp (p := spec.pmin)) (half_sq_Lp' (p := spec.pmin)) := by
  apply lyapunovCandidate_half_sq_Lp
  simp [QLearningSpec.pmin]

instance : LyapunovFunction
  (half_sq_Lp (p := spec.pmin)) (half_sq_Lp' (p := spec.pmin))
  spec.expected_update_target := by
  apply LyapunovFunction.mk

variable {q : ℕ → (ℕ → (S × A) × S × A) → E (Fintype.card (S × A))}

class QLearningIterates where
  init : ∀ ω, q 0 ω = spec.q₀
  step : ∀ n ω, q (n + 1) ω =
    q n ω + spec.α n • spec.update (q n ω) (ω (n + 1))

theorem ae_tendsto_of_QLearning_iid
  (hq : QLearningIterates (spec := spec) (q := q))
  (hα : RobbinsMonro spec.α) :
  ∀ᵐ ω ∂ spec.MRP.iid_samples,
    Tendsto (fun n => q n ω) atTop (𝓝 spec.optimal_q) := by
  have hq' : IteratesOfResidual q spec.q₀ spec.α spec.update_target := by
    constructor
    exact hq.init
    simp [QLearningSpec.update_target]
    exact hq.step
  let φ := half_sq_Lp (p := spec.pmin) (d := Fintype.card (S × A))
  let φ' := half_sq_Lp' (p := spec.pmin) (d := Fintype.card (S × A))
  have : LyapunovFunction φ φ' spec.expected_update_target := by infer_instance
  have : IsProbabilityMeasure spec.MRP.iid_samples := by
      apply Subtype.property
  apply ae_tendsto_of_iterates_iid_samples
    (hx := hq')
    (hFm := spec.measurable_of_udpate_target)
    (hFlip := spec.lipschitz_of_update_target)
    (hfF := spec.unfold_expected_update_target)
    (hα := hα)
    (φ := φ) (φ' := φ')
    (f := spec.expected_update_target)
    (hf := spec.isFixedPoint_optimal_q.symm)
  case hφm =>
    apply measurable_of_half_sq_Lp
    apply LE.le.trans ?_ (by apply le_max_left)
    simp
  case hgradφm =>
    apply measurable_of_gradient_half_sq_Lp
    apply le_max_left

theorem ae_tendsto_of_QLearning_markov
  {ν : ℝ} (hν : ν ∈ Set.Ioo (2 / 3) 1)
  (hq : QLearningIterates (spec := spec) (q := q))
  (hα : spec.α = fun n : ℕ => inv_poly ν 2 n) :
  ∀ᵐ ω ∂ spec.MRP.markov_samples,
    Tendsto (fun n => q n ω) atTop (𝓝 spec.optimal_q) := by
  have hq' : IteratesOfResidual q spec.q₀ spec.α spec.update_target := by
    constructor
    exact hq.init
    simp [QLearningSpec.update_target]
    exact hq.step
  let φ := half_sq_Lp (p := spec.pmin) (d := Fintype.card (S × A))
  let φ' := half_sq_Lp' (p := spec.pmin) (d := Fintype.card (S × A))
  have : LyapunovFunction φ φ' spec.expected_update_target := by infer_instance
  have : IsProbabilityMeasure spec.MRP.iid_samples := by
      apply Subtype.property
  apply ae_tendsto_of_iterates_markov_samples_of_inv_poly
    (hν := hν)
    (hx := hq')
    (hFm := spec.measurable_of_udpate_target)
    (hFlip := spec.lipschitz_of_update_target)
    (hfF := spec.unfold_expected_update_target)
    (hα := hα)
    (φ := φ) (φ' := φ')
    (f := spec.expected_update_target)
    (hf := spec.isFixedPoint_optimal_q.symm)
  case hφm =>
    apply measurable_of_half_sq_Lp
    apply LE.le.trans ?_ (by apply le_max_left)
    simp
  case hgradφm =>
    apply measurable_of_gradient_half_sq_Lp
    apply le_max_left

end ReinforcementLearning.QLearning
