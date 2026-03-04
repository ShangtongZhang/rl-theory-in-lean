/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import RLTheory.Tactic.Tactics
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

import RLTheory.Defs
import RLTheory.MeasureTheory.MeasurableSpace.Constructions
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

-- Convert between E d (= PiLp 2) and LinftySpace d (= PiLp ⊤)
-- These share the same underlying data but have different norms
def toLinfty (x : E d) : LinftySpace d := WithLp.toLp ⊤ (WithLp.ofLp x)
def toL2 (x : LinftySpace d) : E d := WithLp.toLp 2 (WithLp.ofLp x)
def ftoLinfty (f : E d → E d) : LinftySpace d → LinftySpace d :=
  toLinfty ∘ f ∘ toL2

local notation (priority := 2000) "‖" x "‖∞" =>
  @Norm.norm (PiLp ⊤ fun _ => ℝ) _ x

-- Key lemmas about the conversions
@[simp] lemma toL2_toLinfty (x : E d) : toL2 (toLinfty x) = x := rfl
@[simp] lemma toLinfty_sub (x y : E d) : toLinfty x - toLinfty y = toLinfty (x - y) := rfl

-- The L2 norm bounds the L∞ norm
lemma norm_toLinfty_le [Nonempty (Fin d)] (x : E d) : ‖toLinfty x‖ ≤ ‖x‖ := by
  simp only [toLinfty]
  rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_sum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  apply ciSup_le
  intro i
  simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat]
  -- Note: x i means (WithLp.ofLp x) i for x : PiLp p
  have h : |x i| ^ (2 : ℝ) ≤ ∑ j, |x j| ^ (2 : ℝ) := by
    apply Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
  have hrpow : |x i| = (|x i| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul (abs_nonneg _)]
    simp
  calc |x i| = (|x i| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hrpow
    _ ≤ (∑ j, |x j| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) h (by norm_num)

structure QLearningSpec extends FiniteMDP (S := S) (A := A) where
  α : ℕ → ℝ
  q₀ : E (Fintype.card (S × A))

variable {spec : QLearningSpec (S := S) (A := A)}

noncomputable def QLearningSpec.MRP (spec : QLearningSpec (S := S) (A := A)) :
    FiniteMRP (S := S × A) :=
  spec.toFiniteMDP.MRP

noncomputable def QLearningSpec.maxₐ
  (q : E (Fintype.card (S × A))) (s : S) : ℝ :=
  Finset.univ.sup' (by simp) (fun a => q (sa_to_fin (s, a)))

noncomputable def QLearningSpec.bellman_op (spec : QLearningSpec (S := S) (A := A))
  (q : E (Fintype.card (S × A))) : E (Fintype.card (S × A)) :=
  WithLp.toLp 2 fun i =>
    let sa := fin_to_sa i
    spec.r sa + spec.γ * ∑ s', spec.P sa {s'} * maxₐ q s'

lemma QLearningSpec.contraction_of_bellman_op (spec : QLearningSpec (S := S) (A := A)) :
  ContractingWith ⟨spec.γ, by exact spec.hγ.1⟩ (ftoLinfty spec.bellman_op)
  := by
  constructor
  exact_mod_cast spec.hγ.2
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro q q'
  unfold ftoLinfty
  simp only [Function.comp_apply, toLinfty_sub]
  unfold bellman_op toL2 toLinfty
  piLp_norm_simp
  ciSup_le_tac; rename_i i
  calc |spec.r (fin_to_sa i) + spec.γ * ∑ s', spec.P (fin_to_sa i) {s'} * maxₐ (WithLp.toLp 2 (WithLp.ofLp q)) s' -
        (spec.r (fin_to_sa i) + spec.γ * ∑ s', spec.P (fin_to_sa i) {s'} * maxₐ (WithLp.toLp 2 (WithLp.ofLp q')) s')|
      = |spec.γ * (∑ s', spec.P (fin_to_sa i) {s'} * maxₐ (WithLp.toLp 2 (WithLp.ofLp q)) s' -
                   ∑ s', spec.P (fin_to_sa i) {s'} * maxₐ (WithLp.toLp 2 (WithLp.ofLp q')) s')| := by ring_nf
    _ = spec.γ * |∑ s', spec.P (fin_to_sa i) {s'} * (maxₐ (WithLp.toLp 2 (WithLp.ofLp q)) s' -
                                                      maxₐ (WithLp.toLp 2 (WithLp.ofLp q')) s')| := by
        abs_nonneg_factor_simp
        simp only [abs_of_nonneg spec.hγ.1]
        rw [←Finset.sum_sub_distrib]
        simp_rw [←mul_sub]
    _ ≤ spec.γ * ∑ s', |spec.P (fin_to_sa i) {s'} * (maxₐ (WithLp.toLp 2 (WithLp.ofLp q)) s' -
                                                      maxₐ (WithLp.toLp 2 (WithLp.ofLp q')) s')| := by
        apply mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) spec.hγ.1
    _ = spec.γ * ∑ s', spec.P (fin_to_sa i) {s'} * |maxₐ (WithLp.toLp 2 (WithLp.ofLp q)) s' -
                                                    maxₐ (WithLp.toLp 2 (WithLp.ofLp q')) s'| := by
        congr 1
        apply Finset.sum_congr rfl
        intro s' _
        abs_nonneg_factor_simp
    _ ≤ spec.γ * ∑ s', spec.P (fin_to_sa i) {s'} * ‖q - q'‖ := by
        apply mul_le_mul_of_nonneg_left _ spec.hγ.1
        apply Finset.sum_le_sum
        intro s' _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simp only [maxₐ]
        have hab := abs_sup'_sub_sup'_le_sup' (s := Finset.univ) (by simp)
          (x := fun a => (WithLp.ofLp q) (sa_to_fin (s', a)))
          (y := fun a => (WithLp.ofLp q') (sa_to_fin (s', a)))
        refine le_trans hab ?_
        apply Finset.sup'_le (by simp)
        intro a _
        have h := PiLp.norm_apply_le (p := ⊤) (q - q') (sa_to_fin (s', a))
        simp only [WithLp.ofLp_sub, Pi.sub_apply, Real.norm_eq_abs] at h
        exact h
    _ = spec.γ * ‖q - q'‖ := by
        conv_lhs =>
          rw [← Finset.sum_mul]
          arg 2
          rw [← NNReal.coe_sum]
          rw [sum_probability_singleton (ι := S) (spec.P (fin_to_sa i))]
        simp

noncomputable def QLearningSpec.optimal_q (spec : QLearningSpec (S := S) (A := A)) :=
  toL2 (ContractingWith.fixedPoint (ftoLinfty spec.bellman_op)
    spec.contraction_of_bellman_op)

noncomputable def QLearningSpec.x (y : S × A) : E (Fintype.card (S × A)) :=
  WithLp.toLp 2 fun i => if i = sa_to_fin y then 1 else 0

noncomputable def QLearningSpec.update
  (q : E (Fintype.card (S × A))) (y : (S × A) × (S × A)) :
  E (Fintype.card (S × A)) :=
  (spec.r y.1 + spec.γ * maxₐ q y.2.1 - q (sa_to_fin y.1)) • x y.1

lemma QLearningSpec.lipschitz_of_update :
  ∃ C, 0 ≤ C ∧ ∀ z z' y,
    ‖spec.update z y - spec.update z' y‖ ≤ C * ‖z - z'‖ := by
    haveI : Nonempty (Fin (Fintype.card (S × A))) := Fin.pos_iff_nonempty.mp Fintype.card_pos
    refine ⟨?L, ?hLnonneg, ?hL⟩
    case L => exact (|spec.γ| + 1)
    case hLnonneg => positivity
    case hL =>
      unfold update
      intro z z' y
      rcases y with ⟨y, y'⟩
      rw [←sub_smul, norm_smul]
      rw [sub_sub_sub_comm, add_sub_add_comm]
      simp
      rw [←mul_sub]
      grw [abs_sub_le (b := 0)]
      simp only [sub_zero, abs_mul]
      simp [maxₐ]
      grw [abs_sup'_sub_sup'_le_sup' (by simp)]
      -- Key bounds using L∞ norm
      have hLinfty_le : ‖toLinfty (z - z')‖ ≤ ‖z - z'‖ := norm_toLinfty_le _
      -- Each coordinate difference is bounded by L∞ norm
      have hcoord : ∀ i, |z.ofLp i - z'.ofLp i| ≤ ‖toLinfty (z - z')‖ := fun i => by
        have h := PiLp.norm_apply_le (p := ⊤) (toLinfty (z - z')) i
        simp only [toLinfty, WithLp.ofLp_toLp, WithLp.ofLp_sub, Pi.sub_apply, Real.norm_eq_abs] at h
        exact h
      -- Bound the supremum term
      have hsup_le : Finset.univ.sup' (by simp) (fun a' => |z.ofLp (sa_to_fin (y'.1, a')) - z'.ofLp (sa_to_fin (y'.1, a'))|) ≤ ‖toLinfty (z - z')‖ := by
        apply Finset.sup'_le (by simp)
        intro a' _
        exact hcoord _
      -- Bound the single coordinate term
      have hsingle_le : |z'.ofLp (sa_to_fin y) - z.ofLp (sa_to_fin y)| ≤ ‖toLinfty (z - z')‖ := by
        rw [abs_sub_comm]
        exact hcoord _
      -- The norm of x y is at most 1 (it's an indicator)
      have hx_le : ‖x y‖ ≤ 1 := by
        simp only [x]
        rw [PiLp.norm_eq_sum (by simp : (0:ℝ) < (2:ℝ≥0∞).toReal)]
        simp only [ENNReal.toReal_ofNat]
        have hsum : (∑ i : Fin (Fintype.card (S × A)), ‖if i = sa_to_fin y then (1:ℝ) else 0‖ ^ (2:ℝ)) = 1 := by
          rw [Finset.sum_eq_single (sa_to_fin y)]
          · simp
          · intro b _ hb; simp [hb]
          · intro h; exact (h (Finset.mem_univ _)).elim
        rw [hsum]
        simp
      calc ((|spec.γ| * Finset.univ.sup' (by simp) fun a' => |z.ofLp (sa_to_fin (y'.1, a')) - z'.ofLp (sa_to_fin (y'.1, a'))|) +
              |z'.ofLp (sa_to_fin y) - z.ofLp (sa_to_fin y)|) * ‖x y‖
          ≤ ((|spec.γ| * ‖toLinfty (z - z')‖) + ‖toLinfty (z - z')‖) * 1 := by
              apply mul_le_mul _ hx_le (norm_nonneg _) (by positivity)
              apply add_le_add
              · apply mul_le_mul_of_nonneg_left hsup_le (abs_nonneg _)
              · exact hsingle_le
        _ = (|spec.γ| + 1) * ‖toLinfty (z - z')‖ := by ring
        _ ≤ (|spec.γ| + 1) * ‖z - z'‖ := by
              apply mul_le_mul_of_nonneg_left hLinfty_le (by positivity)

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
  simp [f]; exact Continuous.comp (continuous_apply _) (PiLp.continuous_ofLp _ _)
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
  simp [f]; exact Continuous.comp (continuous_apply _) (PiLp.continuous_ofLp _ _)
  intro q
  simp [f, sa_to_fin]
  apply Measurable.comp (by apply measurable_of_countable)
  apply Measurable.comp (by apply measurable_of_countable)
  apply Measurable.fst
  apply measurable_id
  unfold QLearningSpec.x
  -- WithLp.toLp 2 f is measurable if f is measurable for each component
  apply Measurable.comp
  · apply WithLp.measurable_toLp
  · apply measurable_pi_iff.mpr
    intro q
    let f : E (Fintype.card (S × A)) → (S × A) × S × A → ℝ :=
      fun w y => if q = sa_to_fin y.1 then 1 else 0
    apply Measurable.congr (f := f.uncurry)
    · rfl
    · apply measurable_uncurry_of_continuous_of_measurable
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
    ring_close

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
  have hμ : StochasticVec spec.MRP.μ := by infer_instance
  -- This proof shows expected_update_target q = fun i => μ(sa_i) * (bellman_op q - q) i + q i
  -- The key is that update uses indicator x, so only y = fin_to_sa i contributes
  ext i
  unfold expected_update_target expected_update update
  simp only [Pi.add_apply, id, WithLp.ofLp_add]
  congr 1
  -- The sum with indicator x simplifies
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul]
  simp only [x, WithLp.ofLp_toLp]
  -- Now we have (∑ x, ∑ x', (μ x * P x x') • (r x + γ * maxₐ q x'.1 - q (sa_to_fin x)) • indicator) i
  -- The indicator at i selects only x where i = sa_to_fin x
  -- After unfolding, the goal is:
  -- ∑ c, (∑ x, (μ c * P c x) • (r c + γ * maxₐ q x.1 - q (sa_to_fin c)) • indicator) i = ...
  -- First, apply the function to i inside the sum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- Now the if-then-else can be simplified
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  -- Now goal is: ∑ c, (∑ x, if i = sa_to_fin c then ... else 0) = μ(...) * (...)
  -- Use Finset.sum_ite_eq' to simplify: ∑ c, if c = a then f c else 0 = f a if a ∈ s
  -- But our condition is i = sa_to_fin c, not c = something
  -- First swap the condition using eq_comm
  simp_rw [show ∀ c : S × A, (i = sa_to_fin c) = (sa_to_fin c = i) by intros; exact propext eq_comm]
  -- Now we have ∑ x, ∑ x', if sa_to_fin x' = i then f(x, x') else 0
  -- Convert sa_to_fin x' = i to x' = fin_to_sa i
  simp_rw [show ∀ c : S × A, (sa_to_fin c = i) = (c = fin_to_sa i)
    by intro c; simp only [sa_to_fin, fin_to_sa, Equiv.apply_eq_iff_eq_symm_apply]]
  -- Use Finset.sum_ite_eq' on the inner sum: ∑ c, if c = a then f c else 0 = f a
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- Simplify sa_to_fin (fin_to_sa i) = i
  simp only [sa_to_fin, fin_to_sa, Equiv.apply_symm_apply]
  -- Reassociate: μ * P * (...) = μ * (P * (...))
  simp_rw [mul_assoc (spec.MRP.μ _)]
  -- Factor out μ (fin_to_sa i) from the sum
  rw [←Finset.mul_sum]
  congr 1
  -- Expand bellman_op on RHS: (bellman_op q - q).ofLp i
  simp only [WithLp.ofLp_sub]
  -- Now RHS is (bellman_op q).ofLp i - q.ofLp i
  -- Unfold bellman_op and use ofLp_toLp to simplify
  simp only [bellman_op, WithLp.ofLp_toLp, fin_to_sa]
  -- Now both sides have the same structure, use ring-like simplifications
  -- LHS: ∑ x, P (fin_to_sa i) x * (r (fin_to_sa i) + γ * maxₐ q x.1 - q.ofLp i)
  -- RHS: r (fin_to_sa i) + γ * ∑ s', P (fin_to_sa i) {s'} * maxₐ q s' - q.ofLp i
  simp_rw [mul_sub, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib]
  simp_rw [←Finset.sum_mul]
  -- Use rowsum: ∑ s, P (fin_to_sa i) s = 1
  have hrowsum : ∑ x : S × A, spec.MRP.P ((Fintype.equivFin (S × A)).symm i) x = 1 :=
    (hP.stochastic ((Fintype.equivFin (S × A)).symm i)).rowsum
  rw [hrowsum, one_mul, one_mul]
  -- Now goal: r + ∑ x, P x * (γ * maxₐ q x.1) - q.ofLp i = r + γ * ∑ s', P {s'} * maxₐ q s' - q.ofLp i
  -- Factor out γ from LHS sum
  simp_rw [mul_comm (spec.MRP.P _ _) (spec.γ * _), mul_assoc spec.γ, ←Finset.mul_sum]
  -- Now LHS has: r + γ * ∑ x, maxₐ q x.1 * P x - q.ofLp i
  -- Swap the multiplication order to match hP_sum
  simp_rw [mul_comm (maxₐ q _) (spec.MRP.P _ _)]
  -- Convert the sum over (S × A) to sum over S
  have hP_sum : ∑ y' : S × A, spec.MRP.P ((Fintype.equivFin (S × A)).symm i) y' * maxₐ q y'.1 =
      ∑ s' : S, spec.P ((Fintype.equivFin (S × A)).symm i) {s'} * maxₐ q s' := by
    rw [Fintype.sum_prod_type]
    -- Goal: ∑ s', ∑ a, P y (s', a) * maxₐ q s' = ∑ s', P y {s'} * maxₐ q s'
    apply Finset.sum_congr rfl
    intro s' _
    -- Simplify: (s', y).1 = s'
    simp only
    -- Goal: ∑ a, P y (s', a) * maxₐ q s' = P y {s'} * maxₐ q s'
    rw [←Finset.sum_mul]
    congr 1
    -- Goal: ∑ a, P y (s', a) = P y {s'}
    -- Use that MRP.P y (s',a) = P y {s'} * pi s' {a}
    have hP_eq : ∀ a : A, spec.MRP.P ((Fintype.equivFin (S × A)).symm i) (s', a) =
        spec.P ((Fintype.equivFin (S × A)).symm i) {s'} * spec.pi s' {a} := by
      intro a
      rw [QLearningSpec.MRP]
      exact FiniteMDP.MRP.P_apply _ _ _
    simp_rw [hP_eq, ←Finset.mul_sum]
    simp only [←NNReal.coe_sum, sum_probability_singleton (ι := A) (spec.pi s'), NNReal.coe_one, mul_one]
  rw [hP_sum]
  simp only [Pi.sub_apply]

lemma QLearningSpec.unfold_expected_update_target
  (q : E (Fintype.card (S × A))) :
  spec.expected_update_target q =
    ∑ y, ∑ y', (spec.MRP.μ y * spec.MRP.P y y') • spec.update_target q (y, y')
    := by
  have hP : RowStochastic spec.MRP.P := by infer_instance
  have hμ : StochasticVec spec.MRP.μ := by infer_instance
  simp [expected_update_target, update_target, expected_update]
  stochastic_sum_simp
  simp_rw [←mul_sum, (hP.stochastic ?_).rowsum]
  simp [hμ.rowsum]

lemma QLearningSpec.isFixedPoint_optimal_q :
  spec.expected_update_target spec.optimal_q = spec.optimal_q := by
  -- Use expected_update_target_eq which gives equality on .ofLp
  have heq := spec.expected_update_target_eq spec.optimal_q
  -- heq : (expected_update_target optimal_q).ofLp = fun i => μ * (bellman_op optimal_q - optimal_q).ofLp i + optimal_q.ofLp i
  -- First establish bellman_op optimal_q = optimal_q (fixed point property)
  have hfp := ContractingWith.fixedPoint_isFixedPt spec.contraction_of_bellman_op
  simp only [Function.IsFixedPt] at hfp
  have hbellman_eq : spec.bellman_op spec.optimal_q = spec.optimal_q := by
    unfold optimal_q toL2
    simp
    have := congrArg toL2 hfp
    simp only [ftoLinfty, Function.comp_apply, toL2_toLinfty] at this
    exact this
  -- Use extensionality to prove equality in E d
  ext i
  -- Goal: (expected_update_target optimal_q).ofLp i = optimal_q.ofLp i
  have hi := congrFun heq i
  simp only at hi
  rw [hi]
  simp only [hbellman_eq, sub_self, WithLp.ofLp_zero, Pi.zero_apply, mul_zero, zero_add]

lemma QLearningSpec.contraction_of_expected_update_target :
  ∃ η, 0 ≤ η ∧ η < 1 ∧ ∀ q q',
    ‖toLinfty (spec.expected_update_target q) - toLinfty (spec.expected_update_target q')‖∞ ≤
      η * ‖toLinfty (q - q')‖∞ := by
  -- expected_update_target q i = μ i * (bellman_op q - q) i + q i = μ i * bellman_op q i + (1-μ i) * q i
  -- The contraction factor at coordinate i is: μ i * γ + (1 - μ i) = 1 - μ i * (1 - γ)
  -- For this to be < 1, we need μ i > 0 for all i
  -- For an irreducible chain with stationary distribution μ, we have μ i > 0 for all i
  -- Use η = max over i of (1 - μ i * (1 - γ)) = 1 - min(μ) * (1 - γ)
  have hμ : StochasticVec spec.MRP.μ := inferInstance
  have hγ := spec.hγ
  have hbellman := spec.contraction_of_bellman_op
  -- For an irreducible chain, the stationary distribution is strictly positive
  have hμ_pos : ∀ sa : S × A, 0 < spec.MRP.μ sa :=
    pos_of_stationary spec.MRP.μ spec.MRP.P
  -- Define μ_min as the minimum of μ over all state-action pairs
  have huniv : (Finset.univ : Finset (S × A)).Nonempty := by simp
  let μ_min := Finset.univ.inf' huniv spec.MRP.μ
  have hμ_min_pos : 0 < μ_min := by
    rw [Finset.lt_inf'_iff]
    intro sa _
    exact hμ_pos sa
  have hμ_min_le : ∀ sa, μ_min ≤ spec.MRP.μ sa := fun sa =>
    Finset.inf'_le _ (Finset.mem_univ sa)
  -- Use η = 1 - μ_min * (1 - γ)
  use 1 - μ_min * (1 - spec.γ)
  refine ⟨?hnonneg, ?hlt1, ?hcontract⟩
  case hnonneg =>
    have h1 : μ_min ≤ 1 := by
      apply le_trans (hμ_min_le (Classical.arbitrary _))
      exact StochasticVec.le_one _ _
    have h2 : μ_min * (1 - spec.γ) ≤ 1 * (1 - spec.γ) := by
      apply mul_le_mul_of_nonneg_right h1
      linarith
    linarith
  case hlt1 =>
    have h1mγ : 0 < 1 - spec.γ := by linarith
    have : μ_min * (1 - spec.γ) > 0 := mul_pos hμ_min_pos h1mγ
    linarith
  case hcontract =>
    intro q q'
    have heq := spec.expected_update_target_eq q
    have heq' := spec.expected_update_target_eq q'
    simp only [PiLp.norm_eq_ciSup, toLinfty]
    ciSup_le_tac; rename_i i
    simp only [Real.norm_eq_abs, WithLp.ofLp_sub, Pi.sub_apply]
    have hi := congrFun heq i
    have hi' := congrFun heq' i
    simp only at hi hi'
    rw [hi, hi']
    -- Goal: |μ * (bellman q - q).ofLp i + q.ofLp i - (μ * (bellman q' - q').ofLp i + q'.ofLp i)| ≤ ...
    -- Transform to: |μ * bellman q.ofLp i - μ * bellman q'.ofLp i + (1-μ) * q.ofLp i - (1-μ) * q'.ofLp i|
    have hrw : spec.MRP.μ (fin_to_sa i) * (spec.bellman_op q - q).ofLp i + q.ofLp i -
               (spec.MRP.μ (fin_to_sa i) * (spec.bellman_op q' - q').ofLp i + q'.ofLp i) =
               spec.MRP.μ (fin_to_sa i) * (spec.bellman_op q).ofLp i -
               spec.MRP.μ (fin_to_sa i) * (spec.bellman_op q').ofLp i +
               (1 - spec.MRP.μ (fin_to_sa i)) * q.ofLp i -
               (1 - spec.MRP.μ (fin_to_sa i)) * q'.ofLp i := by
      simp only [WithLp.ofLp_sub, Pi.sub_apply]
      ring
    rw [hrw]
    have hμ_nonneg := hμ.nonneg (fin_to_sa i)
    have hμ_le_one := StochasticVec.le_one spec.MRP.μ (fin_to_sa i)
    have hbell_diff := PiLp.norm_apply_le (p := ⊤) (toLinfty (spec.bellman_op q - spec.bellman_op q')) i
    simp only [toLinfty, WithLp.ofLp_toLp, WithLp.ofLp_sub, Pi.sub_apply, Real.norm_eq_abs] at hbell_diff
    have hq_diff := PiLp.norm_apply_le (p := ⊤) (toLinfty (q - q')) i
    simp only [toLinfty, WithLp.ofLp_toLp, WithLp.ofLp_sub, Pi.sub_apply, Real.norm_eq_abs] at hq_diff
    have hcontr := lipschitzWith_iff_norm_sub_le.mp hbellman.2
    have hbell_contr := hcontr (toLinfty q) (toLinfty q')
    simp only [ftoLinfty, Function.comp_apply, toL2_toLinfty] at hbell_contr
    calc |spec.MRP.μ (fin_to_sa i) * (spec.bellman_op q).ofLp i -
           spec.MRP.μ (fin_to_sa i) * (spec.bellman_op q').ofLp i +
           (1 - spec.MRP.μ (fin_to_sa i)) * q.ofLp i -
           (1 - spec.MRP.μ (fin_to_sa i)) * q'.ofLp i|
        ≤ spec.MRP.μ (fin_to_sa i) * |(spec.bellman_op q).ofLp i - (spec.bellman_op q').ofLp i| +
           (1 - spec.MRP.μ (fin_to_sa i)) * |q.ofLp i - q'.ofLp i| := by
            have h1 : spec.MRP.μ (fin_to_sa i) * (spec.bellman_op q).ofLp i -
                      spec.MRP.μ (fin_to_sa i) * (spec.bellman_op q').ofLp i +
                      (1 - spec.MRP.μ (fin_to_sa i)) * q.ofLp i -
                      (1 - spec.MRP.μ (fin_to_sa i)) * q'.ofLp i =
                      spec.MRP.μ (fin_to_sa i) * ((spec.bellman_op q).ofLp i - (spec.bellman_op q').ofLp i) +
                      (1 - spec.MRP.μ (fin_to_sa i)) * (q.ofLp i - q'.ofLp i) := by ring
            rw [h1]
            have h1mμ_nonneg : 0 ≤ 1 - spec.MRP.μ (fin_to_sa i) := by linarith
            calc |spec.MRP.μ (fin_to_sa i) * ((spec.bellman_op q).ofLp i - (spec.bellman_op q').ofLp i) +
                  (1 - spec.MRP.μ (fin_to_sa i)) * (q.ofLp i - q'.ofLp i)|
                ≤ |spec.MRP.μ (fin_to_sa i) * ((spec.bellman_op q).ofLp i - (spec.bellman_op q').ofLp i)| +
                  |(1 - spec.MRP.μ (fin_to_sa i)) * (q.ofLp i - q'.ofLp i)| := abs_add_le _ _
              _ = spec.MRP.μ (fin_to_sa i) * |(spec.bellman_op q).ofLp i - (spec.bellman_op q').ofLp i| +
                  (1 - spec.MRP.μ (fin_to_sa i)) * |q.ofLp i - q'.ofLp i| := by
                    rw [abs_mul, abs_mul, abs_of_nonneg hμ_nonneg, abs_of_nonneg h1mμ_nonneg]
      _ ≤ spec.MRP.μ (fin_to_sa i) * (spec.γ * ‖toLinfty (q - q')‖) +
           (1 - spec.MRP.μ (fin_to_sa i)) * ‖toLinfty (q - q')‖ := by
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left _ hμ_nonneg
              calc |(spec.bellman_op q).ofLp i - (spec.bellman_op q').ofLp i|
                  ≤ ‖toLinfty (spec.bellman_op q - spec.bellman_op q')‖ := hbell_diff
                _ ≤ spec.γ * ‖toLinfty (q - q')‖ := hbell_contr
            · apply mul_le_mul_of_nonneg_left hq_diff
              linarith
      _ = (spec.MRP.μ (fin_to_sa i) * spec.γ + (1 - spec.MRP.μ (fin_to_sa i))) * ‖toLinfty (q - q')‖ := by ring
      _ = (1 - spec.MRP.μ (fin_to_sa i) * (1 - spec.γ)) * ‖toLinfty (q - q')‖ := by ring
      _ ≤ (1 - μ_min * (1 - spec.γ)) * ‖toLinfty (q - q')‖ := by
            -- Need: 1 - μ(i) * (1 - γ) ≤ 1 - μ_min * (1 - γ)
            -- i.e., μ_min * (1 - γ) ≤ μ(i) * (1 - γ)
            -- i.e., μ_min ≤ μ(i), which holds by definition of μ_min
            have h1mγ : 0 ≤ 1 - spec.γ := by linarith
            have hμi := hμ_min_le (fin_to_sa i)
            have hmul : μ_min * (1 - spec.γ) ≤ spec.MRP.μ (fin_to_sa i) * (1 - spec.γ) :=
              mul_le_mul_of_nonneg_right hμi h1mγ
            have hnorm_nonneg : 0 ≤ ‖toLinfty (q - q')‖ := norm_nonneg _
            apply mul_le_mul_of_nonneg_right _ hnorm_nonneg
            linarith

noncomputable def QLearningSpec.pmin_aux (spec : QLearningSpec (S := S) (A := A)) :=
  let η := spec.contraction_of_expected_update_target.choose
  1 / (log (1 / η) / log (Fintype.card (S × A)))

noncomputable def QLearningSpec.pmin (spec : QLearningSpec (S := S) (A := A)) : ℕ :=
  max 2 (⌈spec.pmin_aux⌉₊ + 1)

variable {p : ℕ}

-- Convert from E d to LpSpace p d (same underlying data, different norm)
def toLpSpace (x : E d) : LpSpace p d := WithLp.toLp p (WithLp.ofLp x)
def fromLpSpace (x : LpSpace p d) : E d := WithLp.toLp 2 (WithLp.ofLp x)

-- Lyapunov function and gradient adapted for E d (using Lp norm internally)
noncomputable def half_sq_Lp_E (p : ℕ) (d : ℕ) : E d → ℝ :=
  half_sq_Lp ∘ toLpSpace (p := p)

noncomputable def half_sq_Lp'_E (p : ℕ) (d : ℕ) : E d → E d :=
  fromLpSpace ∘ half_sq_Lp' ∘ toLpSpace (p := p)

-- Key lemmas: toLpSpace/fromLpSpace are just type coercions with same data
@[simp] lemma toLpSpace_apply (x : E d) (i : Fin d) : (toLpSpace (p := p) x) i = x i := rfl
@[simp] lemma fromLpSpace_apply (x : LpSpace p d) (i : Fin d) : (fromLpSpace x) i = x i := rfl
@[simp] lemma fromLpSpace_toLpSpace (x : E d) : fromLpSpace (toLpSpace (p := p) x) = x := rfl
@[simp] lemma toLpSpace_fromLpSpace (x : LpSpace p d) : toLpSpace (fromLpSpace x) = x := rfl
@[simp] lemma toLpSpace_sub (x y : E d) : toLpSpace (p := p) (x - y) = toLpSpace x - toLpSpace y := rfl

-- Measurability of toLpSpace and fromLpSpace
-- These are continuous (they preserve the underlying data) so they're measurable
lemma continuous_toLpSpace [Fact (1 ≤ (p : ℝ≥0∞))] : Continuous (toLpSpace (d := d) (p := p)) := by
  unfold toLpSpace
  apply Continuous.comp
  · apply PiLp.continuous_toLp
  · apply PiLp.continuous_ofLp

lemma continuous_fromLpSpace [Fact (1 ≤ (p : ℝ≥0∞))] : Continuous (fromLpSpace (d := d) (p := p)) := by
  unfold fromLpSpace
  apply Continuous.comp
  · apply PiLp.continuous_toLp
  · apply PiLp.continuous_ofLp

instance : DecreaseAlong (half_sq_Lp_E spec.pmin (Fintype.card (S × A)))
  (half_sq_Lp'_E spec.pmin (Fintype.card (S × A))) spec.expected_update_target := by
  have hpmin_ge_2 : 2 ≤ spec.pmin := by simp [QLearningSpec.pmin]
  haveI : Fact (1 ≤ (spec.pmin : ℝ≥0∞)) := ⟨by simp; linarith⟩
  haveI : Fact (2 ≤ (spec.pmin : ℝ≥0∞)) := ⟨by simp; linarith⟩
  set η := spec.contraction_of_expected_update_target.choose with hηdef
  obtain ⟨hηnonneg, hηlt, hη⟩ := spec.contraction_of_expected_update_target.choose_spec
  rw [←hηdef] at hηnonneg hηlt hη
  constructor
  refine ⟨?η_val, ?hηpos, ?hη_decrease⟩
  case η_val =>
    exact 2 * (1 - Fintype.card (S × A) ^ (spec.pmin : ℝ)⁻¹ * η)
  case hηpos =>
    by_cases hη0 : 0 = η
    · simp [←hη0]
    by_cases hsa1 : (1 : ℝ) = Fintype.card (S × A)
    · simp at hsa1 ⊢
      rw [←hsa1]
      simp [hηlt]
    have hcard : 1 < Fintype.card (S × A) := by
      apply lt_of_le_of_ne
      apply Nat.succ_le_of_lt
      apply Fintype.card_pos_iff.mpr
      infer_instance
      exact_mod_cast hsa1
    simp at hcard
    have hpmin_aux_lt : spec.pmin_aux < spec.pmin := by
      simp [QLearningSpec.pmin]
      apply Or.inr
      apply (Nat.le_ceil spec.pmin_aux).trans_lt
      linarith
    have hinv_lt : (↑spec.pmin)⁻¹ < (spec.pmin_aux)⁻¹ := by
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
    · simp
      gcongr
      apply Real.rpow_lt_rpow_of_exponent_lt
      exact_mod_cast hcard
      exact hinv_lt
    rw [QLearningSpec.pmin_aux, ←hηdef]
    simp
    apply le_of_eq
    rw [div_eq_mul_inv, mul_comm (a := -log η), Real.rpow_mul,
      Real.rpow_inv_log]
    simp [←Real.log_inv]
    rw [Real.exp_log, inv_mul_cancel₀]
    · intro h; exact hη0 h.symm
    · apply inv_pos_of_pos
      apply lt_of_le_of_ne hηnonneg hη0
    · apply LT.lt.trans (b := 1) (by simp) (by exact_mod_cast hcard)
    · apply ne_of_gt
      exact_mod_cast hcard
    · apply LE.le.trans (b := 1) (by simp)
      apply le_of_lt (by exact_mod_cast hcard)
  case hη_decrease =>
    intro y hy x
    set T := spec.expected_update_target
    have hrw : T x - x = T x - T y + (y - x) := by rw [←hy]; simp
    simp only [half_sq_Lp_E, half_sq_Lp'_E, Function.comp_apply]
    rw [hrw, inner_add_right, ←neg_sub x y, inner_neg_right]
    -- Use inner_gradient_half_sq_Lp_self: ⟪toL2 (half_sq_Lp' z), toL2 z⟫ = ‖z‖^2
    have hinner_self := inner_gradient_half_sq_Lp_self (p := spec.pmin) (by linarith) (toLpSpace (x - y))
    -- Note: StochasticApproximation.toL2 = fromLpSpace (same definition)
    have htoL2_eq : StochasticApproximation.toL2 = fromLpSpace (p := spec.pmin) (d := Fintype.card (S × A)) := rfl
    simp only [htoL2_eq] at hinner_self
    -- Key: ⟪fromLpSpace (half_sq_Lp' z), fromLpSpace z⟫ = ‖z‖^2
    -- We need to show that x - y = fromLpSpace (toLpSpace (x - y))
    have hfrom_to : fromLpSpace (toLpSpace (p := spec.pmin) (x - y)) = x - y :=
      fromLpSpace_toLpSpace (p := spec.pmin) _
    have hto_from : ∀ z : LpSpace spec.pmin (Fintype.card (S × A)), toLpSpace (fromLpSpace z) = z :=
      fun z => toLpSpace_fromLpSpace (p := spec.pmin) z
    rw [←hfrom_to]
    simp only [hto_from]
    -- First, bound the inner product with T x - T y
    have hinner_bound : |⟪fromLpSpace (half_sq_Lp' (toLpSpace (p := spec.pmin) (x - y))), T x - T y⟫| ≤
        (Fintype.card (S × A) : ℝ) ^ ((spec.pmin : ℝ)⁻¹) * η * ‖toLpSpace (p := spec.pmin) (x - y)‖ ^ 2 := by
      have habs_bound := inner_abs_gradient_half_sq_Lp_le (p := spec.pmin) (by linarith)
        (toLpSpace (x - y)) (toLpSpace (T x - T y))
      -- Step 1: Inner product to sum of abs
      have hstep1 : |⟪fromLpSpace (half_sq_Lp' (toLpSpace (p := spec.pmin) (x - y))), T x - T y⟫| ≤
          ∑ i, |fromLpSpace (half_sq_Lp' (toLpSpace (p := spec.pmin) (x - y))) i| * |(T x - T y) i| := by
        rw [PiLp.inner_apply]
        refine (abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum; intro i _
        simp only [RCLike.inner_apply, conj_trivial]
        rw [abs_mul, mul_comm]
      -- Step 2: Convert to Lp space form
      have hstep2 : ∑ i, |fromLpSpace (half_sq_Lp' (toLpSpace (p := spec.pmin) (x - y))) i| * |(T x - T y) i| =
          ∑ i, |(half_sq_Lp' (toLpSpace (p := spec.pmin) (x - y))).ofLp i| *
              |(toLpSpace (p := spec.pmin) (T x - T y)).ofLp i| := by
        apply Finset.sum_congr rfl; intro i _
        simp only [fromLpSpace_apply, toLpSpace_apply]
      -- Step 3: Apply inner_abs_gradient_half_sq_Lp_le
      have hstep3 : ∑ i, |(half_sq_Lp' (toLpSpace (p := spec.pmin) (x - y))).ofLp i| *
              |(toLpSpace (p := spec.pmin) (T x - T y)).ofLp i| ≤
          ‖toLpSpace (p := spec.pmin) (x - y)‖ * ‖toLpSpace (p := spec.pmin) (T x - T y)‖ := habs_bound
      -- Step 4: Lp_le_Linfty for T x - T y
      have hstep4 : ‖toLpSpace (p := spec.pmin) (T x - T y)‖ ≤
          (Fintype.card (S × A) : ℝ) ^ (1 / (spec.pmin : ℝ)) * ‖toLinfty (T x - T y)‖ := by
        have hLp_Linfty := Lp_le_Linfty (p := spec.pmin) (x := toLpSpace (T x - T y)) (by linarith)
        convert hLp_Linfty using 2
      -- Step 5: Contraction property
      have hstep5 : ‖toLinfty (T x - T y)‖ ≤ η * ‖toLinfty (x - y)‖ := by
        have hcontr' := hη x y
        simp only [T, ←toLinfty_sub] at hcontr' ⊢
        exact hcontr'
      -- Step 6: Linfty_le_Lp for x - y
      have hstep6 : ‖toLinfty (x - y)‖ ≤ ‖toLpSpace (p := spec.pmin) (x - y)‖ := by
        have hLinfty_Lp := Linfty_le_Lp (p := spec.pmin) (x := toLpSpace (x - y)) (by linarith)
        convert hLinfty_Lp using 2
      -- Combine all bounds
      calc |⟪fromLpSpace (half_sq_Lp' (toLpSpace (p := spec.pmin) (x - y))), T x - T y⟫|
          ≤ ∑ i, |fromLpSpace (half_sq_Lp' (toLpSpace (p := spec.pmin) (x - y))) i| * |(T x - T y) i| := hstep1
        _ = ∑ i, |(half_sq_Lp' (toLpSpace (p := spec.pmin) (x - y))).ofLp i| *
              |(toLpSpace (p := spec.pmin) (T x - T y)).ofLp i| := hstep2
        _ ≤ ‖toLpSpace (p := spec.pmin) (x - y)‖ * ‖toLpSpace (p := spec.pmin) (T x - T y)‖ := hstep3
        _ ≤ ‖toLpSpace (p := spec.pmin) (x - y)‖ *
            ((Fintype.card (S × A) : ℝ) ^ (1 / (spec.pmin : ℝ)) * ‖toLinfty (T x - T y)‖) := by
            gcongr
        _ ≤ ‖toLpSpace (p := spec.pmin) (x - y)‖ *
            ((Fintype.card (S × A) : ℝ) ^ (1 / (spec.pmin : ℝ)) * (η * ‖toLinfty (x - y)‖)) := by
            gcongr
        _ ≤ ‖toLpSpace (p := spec.pmin) (x - y)‖ *
            ((Fintype.card (S × A) : ℝ) ^ (1 / (spec.pmin : ℝ)) * (η * ‖toLpSpace (p := spec.pmin) (x - y)‖)) := by
            gcongr
        _ = (Fintype.card (S × A) : ℝ) ^ ((spec.pmin : ℝ)⁻¹) * η * ‖toLpSpace (p := spec.pmin) (x - y)‖ ^ 2 := by
            rw [one_div]; ring
    -- Now use the bound in the main goal
    rw [hinner_self]
    -- Goal: inner(..., T x - T y) - ‖toLpSpace (x - y)‖^2 ≤ -c * (1/2 * ‖toLpSpace (x - y)‖^2)
    -- The inner product bound gives us:
    -- ⟪..., T x - T y⟫ ≤ |⟪..., T x - T y⟫| ≤ c' * ‖...‖^2 where c' = card^(1/pmin) * η
    have hinner_le : ⟪fromLpSpace (half_sq_Lp' (toLpSpace (p := spec.pmin) (x - y))), T x - T y⟫ ≤
        (Fintype.card (S × A) : ℝ) ^ ((spec.pmin : ℝ)⁻¹) * η * ‖toLpSpace (p := spec.pmin) (x - y)‖ ^ 2 :=
      le_of_abs_le hinner_bound
    -- Combined goal: c' * ‖...‖^2 - ‖...‖^2 ≤ -c * (1/2 * ‖...‖^2)
    simp only [half_sq_Lp]
    have hcard_pow_nonneg : 0 ≤ (Fintype.card (S × A) : ℝ) ^ ((spec.pmin : ℝ)⁻¹) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hnorm_sq_nonneg : 0 ≤ ‖toLpSpace (p := spec.pmin) (x - y)‖ ^ 2 := sq_nonneg _
    have hnorm_nonneg : 0 ≤ ‖toLpSpace (p := spec.pmin) (x - y)‖ := norm_nonneg _
    have hη_nonneg : 0 ≤ η := hηnonneg
    -- Need: inner - ‖...‖^2 ≤ -c * (1/2 * ‖...‖^2)
    -- From hinner_le: inner ≤ c' * ‖...‖^2
    -- So: inner - ‖...‖^2 ≤ (c' - 1) * ‖...‖^2
    -- Need: (c' - 1) * ‖...‖^2 ≤ -(c * 1/2) * ‖...‖^2
    -- i.e., c' - 1 ≤ -c/2
    -- i.e., c' ≤ 1 - c/2 (where c = 2 * (1 - c' * η) = 2 - 2*c'*η when η is the contraction factor)
    -- Wait, c = 2 * (1 - card^(1/pmin) * η), so -c/2 = -(1 - card^(1/pmin) * η) = card^(1/pmin) * η - 1
    -- So we need: c' - 1 ≤ card^(1/pmin) * η - 1
    -- i.e., c' ≤ card^(1/pmin) * η ✓ (which holds by definition since c' = card^(1/pmin) * η)
    calc ⟪fromLpSpace (half_sq_Lp' (toLpSpace (p := spec.pmin) (x - y))), T x - T y⟫ -
        ‖toLpSpace (p := spec.pmin) (x - y)‖ ^ 2
        ≤ (Fintype.card (S × A) : ℝ) ^ ((spec.pmin : ℝ)⁻¹) * η * ‖toLpSpace (p := spec.pmin) (x - y)‖ ^ 2 -
            ‖toLpSpace (p := spec.pmin) (x - y)‖ ^ 2 := by linarith [hinner_le]
      _ = ((Fintype.card (S × A) : ℝ) ^ ((spec.pmin : ℝ)⁻¹) * η - 1) * ‖toLpSpace (p := spec.pmin) (x - y)‖ ^ 2 := by
          ring
      _ ≤ -(2 * (1 - (Fintype.card (S × A) : ℝ) ^ ((spec.pmin : ℝ)⁻¹) * η)) *
          (1 / 2 * ‖toLpSpace (p := spec.pmin) (x - y)‖ ^ 2) := by
          -- Need: (c' * η - 1) * ‖...‖^2 ≤ -(2 * (1 - c' * η)) * (1/2 * ‖...‖^2)
          -- RHS = -(1 - c' * η) * ‖...‖^2 = (c' * η - 1) * ‖...‖^2
          -- So this is equality!
          ring_close

instance : LyapunovCandidate (d := Fintype.card (S × A))
  (half_sq_Lp_E spec.pmin (Fintype.card (S × A)))
  (half_sq_Lp'_E spec.pmin (Fintype.card (S × A))) := by
  -- Use the LyapunovCandidateLp lemma and translate to E d
  -- half_sq_Lp_E = half_sq_Lp ∘ toLpSpace
  -- half_sq_Lp'_E = fromLpSpace ∘ half_sq_Lp' ∘ toLpSpace
  have hpmin_ge_2 : 2 ≤ spec.pmin := by
    simp only [QLearningSpec.pmin]
    exact Nat.le_max_left _ _
  haveI : Fact (1 ≤ (spec.pmin : ℝ≥0∞)) := ⟨by simp; linarith⟩
  have hLp := lyapunovCandidateLp_half_sq_Lp (d := Fintype.card (S × A)) hpmin_ge_2
  -- Translate properties from LpSpace to E d
  refine {
    nonneg := ?nonneg
    zero := ?zero
    smooth := ?smooth
    inner_grad_eq := ?inner_grad_eq
    inner_grad_le' := ?inner_grad_le'
    norm_le := ?norm_le
    le_norm := ?le_norm
  }
  case nonneg =>
    intro x
    simp only [half_sq_Lp_E, Function.comp_apply]
    exact hLp.nonneg _
  case zero =>
    intro z
    simp only [half_sq_Lp_E, Function.comp_apply]
    -- hLp.zero : toLpSpace z = 0 ↔ half_sq_Lp (toLpSpace z) = 0
    -- We need: z = 0 ↔ half_sq_Lp (toLpSpace z) = 0
    -- Since toLpSpace is an injection preserving 0, z = 0 ↔ toLpSpace z = 0
    have hz_equiv : z = 0 ↔ toLpSpace (p := spec.pmin) z = 0 := by
      constructor
      · intro hz; simp [hz, toLpSpace]
      · intro hz
        ext i
        have hi : (toLpSpace (p := spec.pmin) z) i = (0 : LpSpace spec.pmin _) i := by
          rw [hz]
        simp only [toLpSpace_apply, WithLp.ofLp_zero, Pi.zero_apply] at hi
        exact hi
    rw [hz_equiv]
    exact hLp.zero _
  case smooth =>
    -- From hLp.smooth, we have:
    -- half_sq_Lp y ≤ half_sq_Lp x + ⟪toL2 (half_sq_Lp' x), toL2 (y - x)⟫ + L / 2 * ‖toL2 (y - x)‖^2
    -- Need: half_sq_Lp_E y ≤ half_sq_Lp_E x + ⟪half_sq_Lp'_E x, y - x⟫_E + L / 2 * ‖y - x‖_E^2
    obtain ⟨L, hL_nonneg, hL⟩ := hLp.smooth
    use L, hL_nonneg
    intro x y
    simp only [half_sq_Lp_E, half_sq_Lp'_E, Function.comp_apply]
    have htoL2_eq : StochasticApproximation.toL2 = fromLpSpace (p := spec.pmin) (d := Fintype.card (S × A)) := rfl
    have hfrom_to_diff : fromLpSpace (toLpSpace (p := spec.pmin) (y - x)) = y - x := fromLpSpace_toLpSpace (p := spec.pmin) _
    -- Apply the Lp smoothness bound
    have hsmooth := hL (toLpSpace (p := spec.pmin) x) (toLpSpace (p := spec.pmin) y)
    -- toLpSpace y - toLpSpace x = toLpSpace (y - x) by toLpSpace_sub
    have hLp_sub_eq : toLpSpace (p := spec.pmin) y - toLpSpace (p := spec.pmin) x = toLpSpace (p := spec.pmin) (y - x) := by
      rw [←toLpSpace_sub]
    rw [hLp_sub_eq] at hsmooth
    -- Convert: toL2 z = fromLpSpace z, so ⟪toL2 a, toL2 b⟫ = ⟪fromLpSpace a, fromLpSpace b⟫
    -- And fromLpSpace (toLpSpace (y - x)) = y - x
    have hinner_eq : ⟪StochasticApproximation.toL2 (half_sq_Lp' (toLpSpace (p := spec.pmin) x)),
        StochasticApproximation.toL2 (toLpSpace (p := spec.pmin) (y - x))⟫ =
        ⟪fromLpSpace (half_sq_Lp' (toLpSpace (p := spec.pmin) x)), y - x⟫ := by
      rw [htoL2_eq, hfrom_to_diff]
    rw [hinner_eq] at hsmooth
    -- Now we need to relate the norm terms
    -- hsmooth: half_sq_Lp (toLpSpace y) ≤ ... + L / 2 * ‖toL2 (toLpSpace (y - x))‖^2
    -- We need: ... ≤ ... + L / 2 * ‖y - x‖_E^2
    -- Since toL2 = fromLpSpace, and ‖fromLpSpace z‖_E = ‖toL2 z‖ by definition
    have hnorm_eq : ‖StochasticApproximation.toL2 (toLpSpace (p := spec.pmin) (y - x))‖ = ‖y - x‖ := by
      rw [htoL2_eq, hfrom_to_diff]
    rw [hnorm_eq] at hsmooth
    exact hsmooth
  case inner_grad_eq =>
    obtain ⟨C, hC_nonneg, hC⟩ := hLp.inner_grad_eq
    use C, hC_nonneg
    intro x
    simp only [half_sq_Lp_E, half_sq_Lp'_E, Function.comp_apply]
    -- Need: ⟪fromLpSpace (half_sq_Lp' (toLpSpace x)), x⟫_E = C * half_sq_Lp (toLpSpace x)
    -- We have: ⟪toL2 (half_sq_Lp' z), toL2 z⟫ = C * half_sq_Lp z (from hLp.inner_grad_eq)
    -- And toL2 = fromLpSpace
    have htoL2_eq : StochasticApproximation.toL2 = fromLpSpace (p := spec.pmin) (d := Fintype.card (S × A)) := rfl
    have hfrom_to : fromLpSpace (toLpSpace (p := spec.pmin) x) = x := fromLpSpace_toLpSpace (p := spec.pmin) _
    rw [←hfrom_to]
    rw [←htoL2_eq]
    exact hC _
  case inner_grad_le' =>
    obtain ⟨C, hC_nonneg, hC⟩ := hLp.inner_grad_le'
    use C, hC_nonneg
    intro x y
    simp only [half_sq_Lp_E, half_sq_Lp'_E, Function.comp_apply]
    -- The sum of |φ' x i| * |y i| is the same since the underlying data is identical
    have heq : ∑ i, |(half_sq_Lp' (toLpSpace (p := spec.pmin) x)).ofLp i| * |(toLpSpace (p := spec.pmin) y).ofLp i| =
               ∑ i, |(fromLpSpace (half_sq_Lp' (toLpSpace (p := spec.pmin) x))) i| * |y i| := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [fromLpSpace_apply, toLpSpace_apply]
    rw [←heq]
    exact hC _ _
  case norm_le =>
    -- Need: ‖x‖_E ≤ C * √(half_sq_Lp_E x)
    -- where ‖x‖_E = ‖toL2 (toLpSpace x)‖ and half_sq_Lp_E x = 1/2 * ‖toLpSpace x‖_p^2
    -- So √(half_sq_Lp_E x) = ‖toLpSpace x‖_p / √2
    -- From L2_le_Lp: ‖toL2 z‖ ≤ C' * ‖z‖_p
    -- Thus: ‖x‖_E ≤ C' * ‖toLpSpace x‖_p = C' * √2 * √(half_sq_Lp_E x)
    obtain ⟨C', hC'_nonneg, hC'⟩ := L2_le_Lp (d := Fintype.card (S × A)) hpmin_ge_2
    use √2 * C'
    constructor
    · positivity
    intro x
    simp only [half_sq_Lp_E, Function.comp_apply]
    have htoL2_eq : StochasticApproximation.toL2 = fromLpSpace (p := spec.pmin) (d := Fintype.card (S × A)) := rfl
    have hfrom_to : fromLpSpace (toLpSpace (p := spec.pmin) x) = x := fromLpSpace_toLpSpace (p := spec.pmin) _
    -- ‖x‖_E = ‖fromLpSpace (toLpSpace x)‖ = ‖toL2 (toLpSpace x)‖
    have hnorm_x : ‖x‖ = ‖StochasticApproximation.toL2 (toLpSpace (p := spec.pmin) x)‖ := by
      rw [htoL2_eq, hfrom_to]
    rw [hnorm_x]
    -- Apply L2_le_Lp
    have hL2_Lp := hC' (toLpSpace (p := spec.pmin) x)
    -- √(half_sq_Lp z) = ‖z‖ / √2, so ‖z‖ = √2 * √(half_sq_Lp z)
    have hsqrt_eq : ‖toLpSpace (p := spec.pmin) x‖ = √2 * √(half_sq_Lp (toLpSpace (p := spec.pmin) x)) := by
      simp only [half_sq_Lp]
      have h1 : (1 : ℝ) / 2 * ‖toLpSpace (p := spec.pmin) x‖ ^ 2 = ‖toLpSpace (p := spec.pmin) x‖ ^ 2 / 2 := by ring
      rw [h1, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      have h2 : √2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
      field_simp
    rw [hsqrt_eq] at hL2_Lp
    calc ‖StochasticApproximation.toL2 (toLpSpace (p := spec.pmin) x)‖
        ≤ C' * (√2 * √(half_sq_Lp (toLpSpace (p := spec.pmin) x))) := hL2_Lp
      _ = √2 * C' * √(half_sq_Lp (toLpSpace (p := spec.pmin) x)) := by ring
  case le_norm =>
    -- Need: √(half_sq_Lp_E x) ≤ C * ‖x‖_E
    -- √(half_sq_Lp_E x) = ‖toLpSpace x‖_p / √2
    -- ‖x‖_E = ‖toL2 (toLpSpace x)‖
    -- For p ≥ 2, Lp_le_L2 gives: ‖z‖_p ≤ ‖toL2 z‖
    -- Thus: √(half_sq_Lp_E x) = ‖toLpSpace x‖_p / √2 ≤ ‖toL2 (toLpSpace x)‖ / √2 = ‖x‖_E / √2
    use (√2)⁻¹
    constructor
    · positivity
    intro x
    simp only [half_sq_Lp_E, Function.comp_apply]
    have htoL2_eq : StochasticApproximation.toL2 = fromLpSpace (p := spec.pmin) (d := Fintype.card (S × A)) := rfl
    have hfrom_to : fromLpSpace (toLpSpace (p := spec.pmin) x) = x := fromLpSpace_toLpSpace (p := spec.pmin) _
    -- √(half_sq_Lp z) = ‖z‖ / √2
    have hsqrt_eq : √(half_sq_Lp (toLpSpace (p := spec.pmin) x)) =
        ‖toLpSpace (p := spec.pmin) x‖ / √2 := by
      simp only [half_sq_Lp]
      have h1 : (1 : ℝ) / 2 * ‖toLpSpace (p := spec.pmin) x‖ ^ 2 = ‖toLpSpace (p := spec.pmin) x‖ ^ 2 / 2 := by ring
      rw [h1, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    rw [hsqrt_eq]
    -- Apply Lp_le_L2: ‖z‖_p ≤ ‖toL2 z‖
    have hLp_L2 := Lp_le_L2 (x := toLpSpace (p := spec.pmin) x) hpmin_ge_2
    -- ‖x‖_E = ‖toL2 (toLpSpace x)‖
    have hnorm_x : ‖x‖ = ‖StochasticApproximation.toL2 (toLpSpace (p := spec.pmin) x)‖ := by
      rw [htoL2_eq, hfrom_to]
    rw [←hnorm_x] at hLp_L2
    -- Need: ‖toLpSpace x‖_p / √2 ≤ (√2)⁻¹ * ‖x‖
    have hdiv_eq : ‖toLpSpace (p := spec.pmin) x‖ / √2 = (√2)⁻¹ * ‖toLpSpace (p := spec.pmin) x‖ := by
      rw [div_eq_mul_inv, mul_comm]
    rw [hdiv_eq]
    gcongr

instance : LyapunovFunction
  (half_sq_Lp_E spec.pmin (Fintype.card (S × A)))
  (half_sq_Lp'_E spec.pmin (Fintype.card (S × A)))
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
  let φ := half_sq_Lp_E spec.pmin (Fintype.card (S × A))
  let φ' := half_sq_Lp'_E spec.pmin (Fintype.card (S × A))
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
    -- half_sq_Lp_E = half_sq_Lp ∘ toLpSpace, both components are measurable
    have hfact : Fact (1 ≤ (spec.pmin : ℝ≥0∞)) := ⟨by simp [QLearningSpec.pmin]⟩
    apply Measurable.comp
    · apply measurable_of_half_sq_Lp
      simp [QLearningSpec.pmin]
    · exact continuous_toLpSpace.measurable
  case hgradφm =>
    -- half_sq_Lp'_E = fromLpSpace ∘ half_sq_Lp' ∘ toLpSpace
    have hfact : Fact (1 ≤ (spec.pmin : ℝ≥0∞)) := ⟨by simp [QLearningSpec.pmin]⟩
    apply Measurable.comp
    · exact continuous_fromLpSpace.measurable
    · apply Measurable.comp
      · apply measurable_of_gradient_half_sq_Lp
        simp [QLearningSpec.pmin]
      · exact continuous_toLpSpace.measurable

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
  let φ := half_sq_Lp_E spec.pmin (Fintype.card (S × A))
  let φ' := half_sq_Lp'_E spec.pmin (Fintype.card (S × A))
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
    have hfact : Fact (1 ≤ (spec.pmin : ℝ≥0∞)) := ⟨by simp [QLearningSpec.pmin]⟩
    apply Measurable.comp
    · apply measurable_of_half_sq_Lp
      simp [QLearningSpec.pmin]
    · exact continuous_toLpSpace.measurable
  case hgradφm =>
    have hfact : Fact (1 ≤ (spec.pmin : ℝ≥0∞)) := ⟨by simp [QLearningSpec.pmin]⟩
    apply Measurable.comp
    · exact continuous_fromLpSpace.measurable
    · apply Measurable.comp
      · apply measurable_of_gradient_half_sq_Lp
        simp [QLearningSpec.pmin]
      · exact continuous_toLpSpace.measurable

end ReinforcementLearning.QLearning
