/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.MoveAdd
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

import Mathlib.Data.Real.Sign
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

import RLTheory.Defs
import RLTheory.Data.Real.Basic
import RLTheory.Analysis.Normed.Group.Basic

open ENNReal NNReal Real Finset Filter Asymptotics RLTheory
open scoped Topology InnerProductSpace RealInnerProductSpace Gradient

lemma abs_eq_sign_mul_nhds
  {x : ℝ} (hx : x ≠ 0) :
  (fun y => |y|) =ᶠ[𝓝 x] fun y => x.sign * y := by
  have hfx : 0 < |x| := by simp [abs_pos.mpr hx]
  apply Metric.eventually_nhds_iff.mpr
  use |x| / 2
  constructor
  linarith
  intro y hy
  simp
  simp [dist] at hy
  by_cases hx0 : 0 < x
  case pos =>
    simp [Real.sign_of_pos hx0]
    simp [abs_of_pos hx0] at hy
    rw [←abs_neg, neg_sub] at hy
    have : x - y ≤ |x - y| := by
      apply le_abs_self
    linarith
  case neg =>
    simp at hx0
    have : x < 0 := by apply lt_of_le_of_ne hx0 hx
    simp [Real.sign_of_neg this]
    simp [abs_of_neg this] at hy
    have := le_abs_self (y - x)
    linarith

theorem hasDerivAt_abs_pow {x : ℝ} {n : ℕ} (hn : 2 ≤ n) :
  HasDerivAt (fun x => |x| ^ n)
  (n * |x| ^ (n - 2) * x) x := by
  by_cases hx : x ≠ 0
  case pos =>
    have := abs_eq_sign_mul_nhds hx
    have := EventuallyEq.pow_const this n
    apply HasDerivAt.congr_of_eventuallyEq (h₁ := this)
    have := ((hasDerivAt_id' x).const_mul (x.sign)).pow n
    apply HasDerivAt.congr_deriv this
    simp
    by_cases hx0 : 0 < x
    case pos =>
      simp [Real.sign_of_pos hx0, abs_of_pos hx0]
      rw [mul_assoc, ←pow_succ]
      simp
      apply Or.inl
      apply congrArg
      omega
    case neg =>
      simp at hx0
      have : x < 0 := by apply lt_of_le_of_ne hx0 hx
      simp [Real.sign_of_neg this, abs_of_neg this]
      conv_rhs =>
        rw [mul_assoc, ←neg_neg x, mul_neg, neg_neg, ←pow_succ, mul_neg]
      simp
      apply Or.inl
      have : n - 2 + 1 = n - 1 := by omega
      rw [this]
  case neg =>
    simp at hx
    simp [hx]
    apply hasDerivAt_iff_isLittleO.mpr
    simp
    apply isLittleO_iff.mpr
    simp
    intro c hc
    apply Metric.eventually_nhds_iff.mpr
    simp
    use min c 1
    constructor
    simp
    exact hc
    intro y hy
    rw [zero_pow (by linarith)]
    simp
    have : n = (n - 2) + 1 + 1 := by omega
    rw [this, pow_succ, pow_succ]
    grw [pow_le_one₀]
    rw [one_mul]
    apply mul_le_mul_of_nonneg_right
    apply le_of_lt
    exact hy.trans_le (by apply min_le_left)
    simp
    simp
    apply le_of_lt
    exact hy.trans_le (by apply min_le_right)

theorem hasDeriveAt_hasDerivAt_abs_pow {x : ℝ} {n : ℕ} (hn : 2 ≤ n) :
  HasDerivAt (fun x : ℝ => n * |x| ^ (n - 2) * x)
    (n * (n - 1) * |x| ^ (n - 2)) x := by
  by_cases hx : x ≠ 0
  case pos =>
    have := abs_eq_sign_mul_nhds hx
    have := (this.pow_const (n - 2)).const_smul (n : ℝ)
    have := this.mul (EventuallyEq.refl (𝓝 x) id)
    simp at this
    apply HasDerivAt.congr_of_eventuallyEq (h₁ := this)
    apply HasDerivAt.congr
    ext y
    rw [mul_pow, mul_assoc, mul_assoc, ←pow_succ]
    have : n - 2 + 1 = n - 1 := by omega
    rw [this]
    have := (((hasDerivAt_id' x).pow (n - 1)).const_mul
      (x.sign ^ (n - 2))).const_mul (n : ℝ)
    simp at this
    apply HasDerivAt.congr_deriv this
    by_cases hx0 : 0 < x
    case pos =>
      simp [Real.sign_of_pos hx0, abs_of_pos hx0]
      rw [mul_assoc]
      have : n - 1 - 1 = n - 2 := by omega
      rw [this]
      simp
      apply Or.inl
      apply Or.inl
      have : 1 ≤ n := by linarith
      simp [this]
    case neg =>
      simp at hx0
      have : x < 0 := by apply lt_of_le_of_ne hx0 hx
      simp [Real.sign_of_neg this, abs_of_neg this]
      conv_rhs =>
        rw [mul_assoc, neg_pow]
      have : n - 1 - 1 = n - 2 := by omega
      rw [this]
      simp
      apply Or.inl
      rw [←mul_assoc, mul_comm (a := (-1) ^ (n - 2)), mul_assoc]
      simp
      apply Or.inl
      have : 1 ≤ n := by linarith
      simp [this]
  case neg =>
    by_cases hn₁ : n = 2
    case pos =>
      simp [hn₁]
      have := (hasDerivAt_id' x).const_mul 2
      apply HasDerivAt.congr_deriv this
      linarith
    have hn₂ : 2 < n := by
      apply lt_of_le_of_ne hn
      by_contra h
      exact hn₁ h.symm
    simp at hx
    simp [hx]
    apply hasDerivAt_iff_isLittleO.mpr
    simp
    apply isLittleO_iff.mpr
    simp
    intro c hc
    apply Metric.eventually_nhds_iff.mpr
    rw [zero_pow (by omega)]
    simp
    refine ⟨?ε, ?hεpos, ?hε⟩
    case ε => exact (c / n) ^ (1 / ((n : ℝ) - 2))
    case hεpos => positivity
    case hε =>
      intro y hy
      rw [abs_mul, abs_mul, abs_of_nonneg, abs_of_nonneg]
      apply mul_le_mul_of_nonneg_right
      grw [hy]
      rw [←Real.rpow_mul_natCast, Nat.cast_sub]
      simp
      rw [inv_mul_cancel₀]
      simp
      rw [←mul_div_assoc, mul_div_cancel_left₀]
      simp
      linarith
      apply ne_of_gt
      simp
      exact hn₂
      linarith
      apply div_nonneg
      linarith
      simp
      apply abs_nonneg
      apply pow_nonneg
      apply abs_nonneg
      simp

namespace StochasticApproximation

variable {p : ℕ}
variable {d : ℕ}
abbrev LpSpace (p : ℕ) (d : ℕ) := PiLp p fun _ : Fin d => ℝ

def toL2 (x : LpSpace p d) : E d := x

noncomputable def half_sq_Lp : LpSpace p d → ℝ := fun x => 1 / 2 * ‖x‖ ^ 2

noncomputable def half_sq_Lp' : LpSpace p d → LpSpace p d :=
  fun x => fun i => ‖x‖ ^ (2 - (p : ℝ)) * |x i| ^ ((p : ℝ) - 2) * x i

section smooth

variable [Fact (1 ≤ (p : ℝ≥0∞))]

lemma continuous_half_sq_Lp :
  Continuous (@half_sq_Lp p d) := by
  apply Continuous.mul
  apply continuous_const
  apply Continuous.pow
  apply Continuous.norm
  apply continuous_id

noncomputable def path (x y : LpSpace p d) (t : ℝ) : LpSpace p d :=
  x + t • (y - x)

lemma continuousOn_path (x y : LpSpace p d) :
  ContinuousOn (path x y) (Set.Icc 0 1) := by
  apply ContinuousOn.add
  apply continuousOn_const
  apply ContinuousOn.smul
  apply continuousOn_id
  apply continuousOn_const

noncomputable def Lp_pow_p_path (x y : LpSpace p d) (t : ℝ) : ℝ :=
  ‖path x y t‖ ^ (p : ℝ)

lemma Lp_pow_p_path_ne_zero
  {x y : LpSpace p d} {t : ℝ} {ht : path x y t ≠ 0} :
  Lp_pow_p_path x y t ≠ 0 := by
  have hp : Fact (1 ≤ (p : ℝ≥0∞)) := by infer_instance
  have hp := hp.elim
  simp at hp
  unfold Lp_pow_p_path
  apply (rpow_ne_zero ?_ ?_).mpr
  simp [ht]
  apply norm_nonneg
  simp
  linarith

lemma continuousOn_Lp_pow_p_path {x y : LpSpace p d} :
  ContinuousOn (Lp_pow_p_path x y) (Set.Icc 0 1) := by
  intro _
  unfold Lp_pow_p_path
  have := (continuousOn_path x y).norm.pow p
  apply ContinuousOn.congr this
  intro t ht
  simp

lemma unfold_Lp_pow_p_path (x y : LpSpace p d) :
  Lp_pow_p_path x y =
    fun t => (∑ i, |x i + t * (y i - x i)| ^ (p : ℝ)) := by
  have hp : Fact (1 ≤ (p : ℝ≥0∞)) := by infer_instance
  have hp := hp.elim
  simp at hp

  ext t
  simp [Lp_pow_p_path]
  rw [PiLp.norm_eq_sum]
  simp
  rw [←Real.rpow_mul_natCast, inv_mul_cancel₀]
  simp [path]
  simp
  linarith
  apply sum_nonneg; intro i hi; apply pow_nonneg; apply abs_nonneg
  simp
  linarith

noncomputable def Lp_pow_p_path' (x y : LpSpace p d) : ℝ → ℝ :=
  fun t => ∑ i, p * |x i + t * (y i - x i)| ^ (p - 2)
    * (x i + t * (y i - x i)) * (y i - x i)

lemma continuousOn_Lp_pow_p_path' {x y : LpSpace p d} :
  ContinuousOn (Lp_pow_p_path' x y) (Set.Icc 0 1) := by
  unfold Lp_pow_p_path'
  have := continuousOn_path x y
  have := continuousOn_pi.mp this
  simp [path] at this

  apply continuousOn_finset_sum
  intro i hi
  apply ContinuousOn.mul
  apply ContinuousOn.mul
  apply ContinuousOn.mul
  apply continuousOn_const
  apply ContinuousOn.pow
  apply ContinuousOn.abs
  apply this
  apply this
  apply continuousOn_const

lemma hasDerivAt_Lp_pow_p_path (hp : 2 ≤ p) (x y : LpSpace p d) :
  ∀ t : ℝ,
    HasDerivAt (Lp_pow_p_path x y) (Lp_pow_p_path' x y t) t := by
  intro t
  simp [unfold_Lp_pow_p_path]
  apply HasDerivAt.fun_sum
  intro i hi
  set δ := y i - x i
  have h₁ : HasDerivAt (fun t => x i + t * δ) δ t := by
    apply HasDerivAt.const_add
    have := (hasDerivAt_id' t).mul_const δ
    simp at this
    exact this
  have h₂ := hasDerivAt_abs_pow (hn := hp) (x := x i + t * δ)
  have := HasDerivAt.comp t h₂ h₁
  apply HasDerivAt.congr ?_ this
  ext z
  simp

noncomputable def Lp_pow_p_path'' (x y : LpSpace p d) : ℝ → ℝ :=
  fun t => ∑ i, p * (p - 1) * |x i + t * (y i - x i)| ^ (p - 2)
    * (y i - x i) ^ 2

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
lemma hasDerivAt_Lp_pow_p_path' (hp : 2 ≤ p) (x y : LpSpace p d) :
  ∀ t : ℝ,
    HasDerivAt (Lp_pow_p_path' x y) (Lp_pow_p_path'' x y t) t := by
  intro t
  unfold Lp_pow_p_path'
  apply HasDerivAt.fun_sum
  intro i hi
  set δ := y i - x i
  let g₁ := fun y : ℝ => p * |y| ^ (p - 2) * y
  let g₁' := fun y : ℝ => p * (p - 1) * |y| ^ (p - 2)
  have hg₁ : ∀ y, HasDerivAt g₁ (g₁' y) y := by
    intro y
    apply hasDeriveAt_hasDerivAt_abs_pow
    linarith
  let g₂ := fun y : ℝ => δ
  have hg₂ : ∀ y, HasDerivAt g₂ 0 y := by
    intro y
    apply hasDerivAt_const
  let g₃ := fun t => x i + t * δ
  let g₃' := fun t : ℝ => δ
  have hg₃ : ∀ t, HasDerivAt g₃ (g₃' t) t := by
    intro t
    apply HasDerivAt.const_add
    have := (hasDerivAt_id' t).mul_const δ
    simp at this
    exact this

  apply HasDerivAt.congr (f := (g₁ ∘ g₃) * g₂)
  ext z
  simp [g₁, g₂, g₃]
  have := HasDerivAt.comp t (hg₁ (g₃ t)) (hg₃ t)
  have := HasDerivAt.mul this (hg₂ t)
  apply HasDerivAt.congr_deriv this
  simp [g₁, g₂, g₃, g₁', g₃']
  ring

lemma bdd_Lp_pow_path'' (x y : LpSpace p d) (t : ℝ) (hp : 2 < p) :
  Lp_pow_p_path'' x y t ≤
    p * (p - 1) * ‖path x y t‖ ^ (p - 2) * ‖y - x‖ ^ 2 := by
  simp [Lp_pow_p_path'']
  conv_lhs =>
    congr; rfl; ext i; rw [mul_assoc, mul_assoc]
  rw [←mul_sum, ←mul_sum, mul_assoc, mul_assoc]
  grw [Real.inner_le_Lp_mul_Lq (p := p / ↑(p - 2)) (q := p / (2 : ℕ))]
  apply le_of_eq
  simp
  apply Or.inl
  apply Or.inl
  have h₁ : ↑(p - 2) ≠ (0 : ℝ) := by apply ne_of_gt; simp; linarith
  have h₂ : ↑(2 : ℕ) ≠ (0 : ℝ) := by simp
  conv_lhs =>
    congr; congr; congr; rfl; ext i
    rw [←Real.rpow_natCast_mul, mul_div_cancel₀]
    rfl
    exact h₁
    apply abs_nonneg
    rw [div_eq_mul_inv, mul_comm]
    rfl
    congr; congr; rfl; ext i
    rw [←sq_abs, ←Real.rpow_natCast_mul]
    simp
    rw [mul_div_cancel₀]
    rfl
    exact h₂
    apply abs_nonneg
    rw [div_eq_mul_inv, mul_comm]
  rw [Real.rpow_mul, Real.rpow_mul]
  rw [PiLp.norm_eq_sum, PiLp.norm_eq_sum]
  simp [path]
  simp; linarith
  simp; linarith
  apply sum_nonneg; intro i hi; apply rpow_nonneg; apply abs_nonneg
  apply sum_nonneg; intro i hi; apply rpow_nonneg; apply abs_nonneg
  simp; linarith
  constructor
  simp
  rw [Nat.cast_sub]
  ring_nf
  apply mul_inv_cancel₀
  simp; linarith; linarith
  apply div_pos
  simp; linarith; simp; linarith
  apply div_pos
  simp; linarith; simp

lemma unfold_half_sq_Lp_path (x y : LpSpace p d) :
  half_sq_Lp ∘ path x y = (2⁻¹ : ℝ) • (Lp_pow_p_path x y) ^ (2 / (p : ℝ)) := by
  have hp : Fact (1 ≤ (p : ℝ≥0∞)) := by infer_instance
  have hp := hp.elim
  simp at hp

  ext t
  simp [half_sq_Lp, Lp_pow_p_path]
  rw [←Real.rpow_natCast_mul, mul_div_cancel₀]
  simp

  simp
  linarith
  apply norm_nonneg

lemma continuousOn_half_sq_Lp_path {x y : LpSpace p d} :
  ContinuousOn (half_sq_Lp ∘ path x y) (Set.Icc 0 1) := by
  rw [unfold_half_sq_Lp_path x y]
  apply ContinuousOn.mul
  apply continuousOn_const
  apply ContinuousOn.rpow_const
  apply continuousOn_Lp_pow_p_path
  intro t ht
  apply Or.inr
  apply div_nonneg
  simp
  simp

noncomputable def half_sq_Lp_path' (x y : LpSpace p d) : ℝ → ℝ :=
  (p⁻¹ : ℝ) • Lp_pow_p_path x y ^ (2 / (p : ℝ) - 1) * Lp_pow_p_path' x y

lemma continuousOn_half_sq_Lp_path' {x y : LpSpace p d} :
  (∀ t ∈ Set.Icc (0 : ℝ) 1, path x y t ≠ 0) →
  ContinuousOn (half_sq_Lp_path' x y) (Set.Icc 0 1) := by
  intro ht
  apply ContinuousOn.mul
  apply ContinuousOn.mul
  apply continuousOn_const
  apply ContinuousOn.rpow_const
  apply continuousOn_Lp_pow_p_path
  intro t ht'
  apply Or.inl
  apply Lp_pow_p_path_ne_zero
  apply ht t ht'
  apply continuousOn_Lp_pow_p_path'

lemma hasDerivAt_half_sq_Lp_path (hp : 2 ≤ p) (x y : LpSpace p d) :
  ∀ t : ℝ, path x y t ≠ 0 → HasDerivAt
    (half_sq_Lp ∘ path x y) (half_sq_Lp_path' x y t) t := by
  intro t ht
  rw [unfold_half_sq_Lp_path x y]
  have := (hasDerivAt_Lp_pow_p_path hp x y t)
  have := this.rpow_const (p := 2 / (p : ℝ)) ?_
  have := this.const_mul (2⁻¹ : ℝ)
  apply HasDerivAt.congr_congr this
  ext t
  simp
  rw [half_sq_Lp_path']
  simp
  ring
  apply Or.inl
  apply Lp_pow_p_path_ne_zero
  exact ht

noncomputable def half_sq_Lp_path'' (x y : LpSpace p d) : ℝ → ℝ :=
  (p⁻¹ : ℝ) • ((2 / (p : ℝ) - 1) • Lp_pow_p_path x y ^ (2 / (p : ℝ) - 2) * Lp_pow_p_path' x y ^ 2 + Lp_pow_p_path x y ^ (2 / (p : ℝ) - 1) * Lp_pow_p_path'' x y)

lemma hasDerivAt_half_sq_Lp_path' (hp : 2 ≤ p) (x y : LpSpace p d) :
  ∀ t, path x y t ≠ 0 → HasDerivAt
    (half_sq_Lp_path' x y) (half_sq_Lp_path'' x y t) t := by
  intro t ht
  unfold half_sq_Lp_path'
  apply HasDerivAt.congr_deriv
  apply HasDerivAt.mul
  apply HasDerivAt.const_mul
  apply HasDerivAt.rpow_const
  apply hasDerivAt_Lp_pow_p_path
  exact hp
  apply Or.inl
  apply Lp_pow_p_path_ne_zero
  exact ht
  apply hasDerivAt_Lp_pow_p_path'
  exact hp
  rw [half_sq_Lp_path'']
  simp
  rw [mul_add]
  nth_rw 4 [←mul_assoc]
  simp
  rw [mul_assoc]
  simp
  apply Or.inl
  ring_nf

lemma bdd_half_sq_Lp_path'' (x y : LpSpace p d) (t : ℝ) (hp : 2 < p) :
  path x y t ≠ 0 → half_sq_Lp_path'' x y t ≤
    (p - 1) * 2 * half_sq_Lp (x - y) := by
  intro hxy
  simp [half_sq_Lp_path'']
  rw [mul_add, add_comm]
  apply add_le_of_le_of_nonpos
  grw [bdd_Lp_pow_path'']
  apply le_of_eq
  move_mul [←(p : ℝ)]
  rw [mul_inv_cancel₀]
  move_mul [(p : ℝ) - 1]
  simp
  apply Or.inl
  simp [Lp_pow_p_path]
  rw [←Real.rpow_natCast_mul, mul_sub, mul_div_cancel₀, ←Real.rpow_add_natCast]
  simp
  rw [Nat.cast_sub, sub_add_sub_cancel]
  simp [half_sq_Lp]
  rw [←neg_sub, norm_neg]
  linarith
  simp [hxy]
  simp; linarith
  apply norm_nonneg
  simp; linarith
  unfold Lp_pow_p_path
  apply rpow_nonneg
  apply rpow_nonneg
  apply norm_nonneg
  linarith
  apply le_of_neg_le_neg
  rw [neg_mul_eq_mul_neg, neg_mul_eq_neg_mul, neg_sub]
  simp
  apply mul_nonneg
  simp
  apply mul_nonneg
  rw [sub_div']
  apply div_nonneg
  simp; linarith
  simp
  simp; linarith
  apply mul_nonneg
  apply rpow_nonneg
  unfold Lp_pow_p_path
  apply rpow_nonneg
  apply norm_nonneg
  apply sq_nonneg

lemma smooth_half_sq_Lp_ne (hp : 2 < p) :
  ∀ (x y : LpSpace p d), (∀ t ∈ Set.Icc (0 : ℝ) 1, path x y t ≠ 0) →
    half_sq_Lp y ≤
      half_sq_Lp x + ⟪toL2 (half_sq_Lp' x), toL2 (y - x)⟫ + (p - 1) * half_sq_Lp (y - x) := by
  intro x y hxy
  have :
    half_sq_Lp_path' x y 0 = ⟪toL2 (half_sq_Lp' x), toL2 (y - x)⟫ := by
    simp [half_sq_Lp_path', Lp_pow_p_path, path,
      toL2, half_sq_Lp']
    rw [←Real.rpow_natCast_mul, mul_sub, mul_div_cancel₀]
    conv_rhs =>
      congr; rfl; ext i;
      rw [mul_assoc, ←mul_assoc, mul_comm (a := y i - x i), mul_assoc]
    rw [←mul_sum]
    nth_rw 2 [mul_comm]
    rw [mul_assoc]
    simp
    apply Or.inl
    simp [Lp_pow_p_path']
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    simp_rw [mul_assoc]
    rw [←mul_assoc]
    rw [inv_mul_cancel₀]
    simp
    conv_rhs => rw [mul_comm]
    rw [mul_assoc]
    have : 2 ≤ p := by linarith
    exact_mod_cast rfl
    simp; linarith
    simp; linarith
    apply norm_nonneg
  rw [←this]

  let I := Set.Ioo (0 : ℝ) 1
  have hI : ∀ t ∈ I, path x y t ≠ 0 := by
    intro t ht
    apply hxy t ?_
    simp [I] at ht
    exact ⟨ht.1.le, ht.2.le⟩

  let φ := half_sq_Lp ∘ path x y
  let φ' := half_sq_Lp_path' x y
  let φ'' := half_sq_Lp_path'' x y
  let f := fun t => φ t - φ 0 - φ' 0 * t
  let f' := fun t => φ' t - φ' 0
  have hfDeriv : ∀ t ∈ I, HasDerivAt f (f' t) t := by
    intro t ht
    apply HasDerivAt.congr_deriv
    apply HasDerivAt.sub
    apply HasDerivAt.sub
    apply hasDerivAt_half_sq_Lp_path
    linarith
    apply hI t ht
    apply hasDerivAt_const
    apply HasDerivAt.const_mul
    apply hasDerivAt_id
    simp [f', φ']
  let C := φ 1 - φ 0 - φ' 0
  let g := fun t => f t - C * t ^2
  let g' := fun t => f' t - 2 * C * t
  have hgDeriv : ∀ t ∈ I, HasDerivAt g (g' t) t := by
    intro t ht
    apply HasDerivAt.congr_deriv
    apply HasDerivAt.sub
    apply hfDeriv t ht
    apply HasDerivAt.const_mul
    apply HasDerivAt.pow
    apply hasDerivAt_id
    simp [g', f', φ']
    ring

  have := exists_hasDerivAt_eq_slope g g' (a := 0) (b := 1) (by simp) ?_ hgDeriv
  obtain ⟨z₁, hz₁I, hz₁⟩ := this
  simp at hz₁I
  simp [g, f, C, g'] at hz₁

  let h := fun t => f' t - 2 * C * t
  let h' := fun t => φ'' t - 2 * C
  have hhDeriv : ∀ t ∈ Set.Ioo 0 z₁, HasDerivAt h (h' t) t := by
    intro t ht
    apply HasDerivAt.congr_deriv
    apply HasDerivAt.sub
    unfold f'
    apply HasDerivAt.sub
    apply hasDerivAt_half_sq_Lp_path'
    linarith
    apply hxy
    simp at ht ⊢
    constructor
    linarith
    linarith
    apply hasDerivAt_const
    apply HasDerivAt.const_mul
    apply hasDerivAt_id
    simp [h', φ'']

  have := exists_hasDerivAt_eq_slope h h' (a := 0) (b := z₁) hz₁I.1 ?_ hhDeriv
  obtain ⟨z₂, hz₂I, hz₂⟩ := this
  simp at hz₂I
  have : h 0 = 0 := by
    simp [h, f']
  rw [this] at hz₂
  have : h z₁ = 0 := by
    simp [h, C]
    exact hz₁
  rw [this] at hz₂
  simp at hz₂
  simp [h', C] at hz₂
  have := eq_of_sub_eq_zero hz₂
  have : φ 1 = φ 0 + φ' 0 * 1 + 1 / 2 * φ'' z₂ := by
    rw [this]
    ring
  simp [φ, φ', φ'', path] at this
  rw [this]
  apply add_le_add_three
  rfl
  rfl
  grw [bdd_half_sq_Lp_path'' x y z₂]
  unfold half_sq_Lp
  apply le_of_eq
  rw [←norm_neg, neg_sub]
  ring

  linarith
  apply hxy
  simp; constructor; linarith; linarith

  simp [h, f', φ']
  apply ContinuousOn.sub
  apply ContinuousOn.sub
  apply ContinuousOn.mono (by apply continuousOn_half_sq_Lp_path' hxy)
  intro t ht
  simp at ht ⊢
  constructor; linarith; linarith
  apply continuousOn_const
  apply ContinuousOn.mul
  apply continuousOn_const
  apply continuousOn_id
  simp [g, f, φ, φ']
  apply ContinuousOn.sub
  apply ContinuousOn.sub
  apply ContinuousOn.sub
  apply continuousOn_half_sq_Lp_path
  apply continuousOn_const
  apply ContinuousOn.mul
  apply continuousOn_const
  apply continuousOn_id
  apply ContinuousOn.mul
  apply continuousOn_const
  apply ContinuousOn.pow
  apply continuousOn_id

end smooth

theorem smooth_half_sq_Lp (hp : 2 ≤ p) :
  ∀ (x y : LpSpace p d),
    half_sq_Lp y ≤ half_sq_Lp x + ⟪toL2 (half_sq_Lp' x), toL2 (y - x)⟫ + (p - 1) * half_sq_Lp (y - x) := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  by_cases hp2 : 2 = p
  case pos =>
    intro x y
    subst hp2
    simp [half_sq_Lp, toL2, half_sq_Lp']
    apply (mul_le_mul_iff_of_pos_left (a := 2) (by simp)).mp
    simp_rw [mul_add]
    simp
    have := norm_add_sq_real (F := E d) (x := toL2 x) (y := toL2 (y - x))
    simp [toL2] at this
    rw [this]
    simp
    ring_nf
    rfl
  case neg =>
    have hp' : 2 < p := lt_of_le_of_ne hp hp2
    intro x y
    by_cases hxy : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (y - x) ≠ 0
    case pos =>
      apply smooth_half_sq_Lp_ne hp' x y hxy
    push_neg at hxy
    obtain ⟨t, htI, htx⟩ := hxy
    by_cases hx : x = 0
    case pos =>
      simp [half_sq_Lp, toL2, half_sq_Lp']
      rw [hx]
      simp
      apply le_mul_of_one_le_left
      positivity
      apply le_sub_iff_add_le.mpr
      rw [one_add_one_eq_two]
      simp
      linarith
    have htpos : 0 < t := by
      by_contra h
      simp at h
      simp at htI
      have := eq_of_le_of_ge htI.1 h
      simp [←this] at htx
      contradiction
    by_cases hd0 : d = 0
    case pos =>
      subst hd0
      simp [half_sq_Lp]
      rw [PiLp.norm_eq_sum]
      rw [PiLp.norm_eq_sum]
      rw [PiLp.norm_eq_sum]
      simp
      rw [pow_two, Real.zero_rpow]
      simp
      simp; linarith
      simp; linarith
      simp; linarith
      simp; linarith
    by_cases hd : d ≤ 1
    case pos =>
      have hd' : 1 = d := by omega
      simp [half_sq_Lp, toL2, half_sq_Lp']
      let i : Fin d := ⟨0, by linarith⟩
      have : ∀ z : LpSpace p d, ‖z‖ = |z i| := by
        intro z
        subst hd'
        rw [PiLp.norm_eq_sum]
        simp
        rw [←Real.rpow_natCast_mul, mul_inv_cancel₀]
        simp
        unfold i
        simp
        simp; linarith
        apply abs_nonneg
        simp
        linarith
      simp_rw [this]
      subst hd'
      rw [Fin.sum_univ_one]
      simp_rw [i]
      simp
      apply (mul_le_mul_iff_of_pos_left (a := 2) (by simp)).mp
      simp
      simp_rw [mul_add]
      simp
      rw [←Real.rpow_add]
      simp
      have : y 0 = x 0 + (y 0 - x 0) := by simp
      conv_lhs => rw [this]
      rw [add_sq]
      apply add_le_add_three
      rfl
      apply le_of_eq
      ring
      rw [←mul_assoc]
      move_mul [←2⁻¹]
      simp
      apply le_mul_of_one_le_left
      apply sq_nonneg
      apply le_sub_iff_add_le.mpr
      rw [one_add_one_eq_two]
      simp
      linarith
      by_contra h
      simp at h
      have : x = 0 := by
        ext j
        simp
        rw [Fin.eq_zero j]
        exact h
      exact hx this
    have : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      have : x = 0 := by
        ext i
        simp
        apply h
      contradiction
    obtain ⟨i, hi⟩ := this
    have : ∃ j, j ≠ i := by
      by_cases hi : (i : ℕ) = 0
      case pos =>
        let j := Fin.mk (n := d) 1 (by linarith)
        use j
        apply (Fin.ne_iff_vne j i).mpr
        simp [hi]
      case neg =>
        let j := Fin.mk (n := d) 0 (by linarith)
        use j
        apply (Fin.ne_iff_vne j i).mpr
        unfold j
        simp
        by_contra h
        exact hi h.symm
    obtain ⟨j, hj⟩ := this
    let u : LpSpace p d := fun k => if j = k then 1 else 0
    let y' := fun k : ℕ => y + (1 / ((k : ℝ) + 1)) • u
    have hxy' : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (y' k - x) ≠ 0 := by
      intro k
      by_contra h
      push_neg at h
      obtain ⟨t', ht'I, ht'⟩ := h
      have h₁ := congrFun ht' i
      simp at h₁
      simp [y', u, hj] at h₁
      have h₂ := congrFun htx i
      simp at h₂
      rw [mul_sub, add_sub, add_comm, sub_eq_iff_eq_add] at h₂
      simp at h₂
      have h₂ := (sub_eq_iff_eq_add.mpr h₂.symm).symm
      have := congrArg (fun x => t⁻¹ * x) h₂
      dsimp at this
      rw [←mul_assoc, inv_mul_cancel₀ (htpos.ne')] at this
      simp at this
      rw [this] at h₁
      rw [mul_sub (a := t⁻¹), ←mul_assoc, inv_mul_cancel₀ (htpos.ne')] at h₁
      simp at h₁
      rw [←mul_assoc, ←sub_eq_add_neg] at h₁
      nth_rw 1 [←one_mul (a := x i)] at h₁
      rw [←sub_mul] at h₁
      simp at h₁
      rcases h₁ with hl | hr
      case inr => contradiction
      case inl =>
        have := eq_of_sub_eq_zero hl
        have := congrArg (fun x => x * t) this
        dsimp at this
        simp [mul_assoc] at this
        rw [inv_mul_cancel₀ (htpos.ne')] at this
        simp at this
        rw [←this] at ht'
        rw [←ht'] at htx
        simp at htx
        have := sub_eq_zero.mpr htx
        rw [←smul_sub] at this
        rw [sub_sub_sub_cancel_right] at this
        simp at this
        rcases this with hl | hr
        case inl => exact htpos.ne' hl
        case inr =>
          simp [y'] at hr
          rcases hr with hl | hr
          case inl =>
            have := (add_eq_zero_iff_of_nonneg ?_ ?_).mp hl
            simp at this
            simp
            simp
          case inr =>
            have := congrFun hr j
            simp [u] at this
    have hy' : Tendsto y' atTop (𝓝 y) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simp [y']
      apply Tendsto.congr
      intro k
      rw [norm_smul, norm_eq_abs, abs_inv, abs_of_nonneg]
      linarith
      have := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖u‖
      simp at this
      exact this
    have hlhs := (continuous_half_sq_Lp.tendsto y).comp hy'
    have : Continuous fun y => half_sq_Lp x +
      ⟪toL2 (half_sq_Lp' x), toL2 (y - x)⟫ +
      (p - 1) * half_sq_Lp (y - x) := by
      apply Continuous.add
      apply Continuous.add
      apply continuous_const
      apply Continuous.inner
      apply continuous_const
      apply Continuous.sub
      apply continuous_id
      apply continuous_const
      apply Continuous.mul
      apply continuous_const
      apply continuous_half_sq_Lp.comp
      apply Continuous.sub
      apply continuous_id
      apply continuous_const
    have hrhs := (this.tendsto y).comp hy'
    apply le_of_tendsto_of_tendsto' hlhs hrhs
    intro k
    simp [-PiLp.inner_apply]
    apply smooth_half_sq_Lp_ne hp' x (y' k) (hxy' k)

section norm_equivalence

lemma Lp_le_L2 {x : LpSpace p d} (hp : 2 ≤ p) :
  ‖x‖ ≤ ‖toL2 x‖ := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  conv_rhs => rw [←one_mul (a := ‖toL2 x‖)]
  by_cases hx : ‖toL2 x‖ = 0
  case pos =>
    simp [toL2] at hx
    simp [hx]
  apply (inv_mul_le_iff₀' ?_).mp
  rw [PiLp.norm_eq_sum (p := p)]
  simp
  have : (‖toL2 x‖⁻¹ ^ p) ^ ((p : ℝ))⁻¹ = ‖toL2 x‖⁻¹ := by
    rw [←Real.rpow_natCast_mul, mul_inv_cancel₀]
    simp
    simp; linarith
    simp
  rw [←this]
  rw [←Real.mul_rpow, mul_sum]
  apply Real.rpow_le_one
  apply sum_nonneg; intro i hi; positivity
  conv_lhs => congr; rfl; ext i; rw [←mul_pow]

  have : ‖toL2 (‖toL2 x‖⁻¹ • x)‖ = 1 := by
    simp [toL2]
    rw [norm_smul]
    simp
    apply inv_mul_cancel₀
    simp [toL2] at hx
    simp [hx]
  rw [PiLp.norm_eq_sum] at this
  simp at this
  nth_rw 2 [←one_div] at this
  rw [←Real.sqrt_eq_rpow, Real.sqrt_eq_one] at this
  nth_rw 1 [toL2] at this

  rw [←this]
  apply sum_le_sum
  simp
  intro i
  rw [←sq_abs, abs_mul, abs_inv]
  simp
  apply pow_le_pow_of_le_one
  positivity
  apply (sq_le_one_iff₀ (by positivity)).mp
  rw [←this]
  conv_rhs =>
    congr; rfl; ext i; simp
    rw [←sq_abs, abs_mul, abs_inv]
    simp
  apply single_le_sum (f := fun i => (‖toL2 x‖⁻¹ * |x i|) ^ 2)
  intro i hi; positivity
  simp
  linarith
  simp
  positivity
  positivity
  positivity
  simp
  linarith
  simp
  simp at hx
  exact hx

lemma L2_le_Lp (hp : 2 ≤ p) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : LpSpace p d, ‖toL2 x‖ ≤ C * ‖x‖ := by
  use ((d : ℝ) ^ (((p : ℝ) - 2) / p)) ^ (2⁻¹ : ℝ)
  constructor
  positivity
  intro x
  simp [toL2]
  by_cases hp2 : 2 = p
  case pos =>
    subst hp2
    simp
  rw [PiLp.norm_eq_sum, PiLp.norm_eq_sum (p := 2)]
  simp
  have := Real.inner_le_Lp_mul_Lq
    (p := (p : ℝ) / 2) (q := (p : ℝ) / (p - 2))
    (f := fun i => |x i| ^ 2) (g := fun _ => 1) Finset.univ ?_
  simp at this
  grw [this]
  apply le_of_eq
  rw [Real.mul_rpow, mul_comm]
  simp
  apply Or.inl
  rw [←Real.rpow_mul]
  have h₁ : 2 ≠ (0 : ℝ) := by simp
  conv_lhs =>
    congr; congr; rfl; ext i
    rw [←sq_abs, ←Real.rpow_natCast_mul]
    simp
    rw [mul_div_cancel₀]
    rfl
    exact h₁
    apply abs_nonneg
    rw [div_eq_mul_inv, mul_comm, ←mul_assoc]
    simp
  exact_mod_cast rfl
  positivity
  positivity
  positivity
  constructor
  simp
  rw [div_add_div_same]
  simp
  rw [div_eq_mul_inv, mul_inv_cancel₀]
  simp; linarith
  positivity
  apply div_pos
  simp; linarith
  simp; apply lt_of_le_of_ne hp hp2
  simp
  simp; linarith

local notation (priority := 2000) "‖" x "‖∞" =>
  @Norm.norm (PiLp ⊤ fun _ => ℝ) _ x

lemma nnreal_toReal_sup_eq_sup'
  {ι} {s : Finset ι} (hs : s.Nonempty) {x : ι → ℝ≥0} :
  (s.sup x).toReal = s.sup' hs (fun i => (x i).toReal) := by
  obtain ⟨i, his, hi⟩ := exists_mem_eq_sup' hs x
  apply le_antisymm
  simp
  use i
  constructor
  exact his
  rw [←hi]
  intro j hj
  apply (le_sup'_iff hs).mpr
  use j
  simp
  intro j hj
  apply le_sup_of_le hj
  rfl

lemma infty_norm_eq_norm {α} [Fintype α] [Nonempty α] {f : α → ℝ} :
  @Norm.norm (PiLp ⊤ fun _ ↦ ℝ) _ f = ‖f‖ := by
  simp [Norm.norm, nnnorm, iSup]
  rw [nnreal_toReal_sup_eq_sup' (by simp)]
  simp [sup'_eq_csSup_image]

lemma Linfty_le_Lp {x : LpSpace p d} (hp : 1 ≤ p) :
  ‖x‖∞ ≤ ‖x‖ := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  by_cases hd : Nonempty (Fin d)
  case pos =>
    rw [infty_norm_eq_norm]
    conv_lhs =>
      simp [Norm.norm, nnreal_toReal_sup_eq_sup']
    simp
    intro i
    have := PiLp.norm_apply_le x i
    simp at this
    exact this
  case neg =>
    simp at hd
    simp [PiLp.norm_eq_ciSup]

lemma Lp_le_Linfty {x : LpSpace p d} (hp : 1 ≤ p) :
  ‖x‖ ≤ (d : ℝ) ^ (1 / (p : ℝ)) * ‖x‖∞ := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  rw [PiLp.norm_eq_sum]
  simp
  grw [Real.rpow_le_rpow]
  case h₁ =>
    grw [sum_le_sum]
    intro i hi
    have := PiLp.norm_apply_le (p := ⊤) x i
    simp at this
    grw [this]
  simp [Real.mul_rpow, ←Real.rpow_natCast_mul]
  rw [mul_inv_cancel₀]
  simp
  simp; linarith
  positivity
  simp
  simp; linarith

end norm_equivalence

section inner

lemma inner_gradient_half_sq_Lp_self (hp : 1 ≤ p) (x : LpSpace p d) :
  ⟪toL2 (half_sq_Lp' x), toL2 x⟫ = ‖x‖ ^ 2 := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  simp [toL2, half_sq_Lp']
  have h₁ : p - (2 : ℝ) + 2 ≠ 0 := by simp; linarith
  conv_lhs =>
    congr; rfl; ext i
    rw [mul_comm, mul_assoc, ←pow_two, ←sq_abs, mul_assoc,
      ←Real.rpow_add_natCast']
    simp
    rfl
    apply abs_nonneg
    exact h₁
  rw [←mul_sum]
  by_cases hx : x = 0
  case pos =>
    simp [hx]
    apply Or.inr
    apply Or.inr
    linarith
  have := PiLp.norm_eq_sum (p := p) (by simp; linarith) x
  simp at this
  have := congrArg (fun x => x ^ p) this
  simp at this
  rw [←Real.rpow_mul_natCast, inv_mul_cancel₀] at this
  simp at this
  rw [←this]
  rw [←Real.rpow_add_natCast']
  simp
  apply norm_nonneg
  simp
  simp; linarith
  positivity

lemma inner_abs_gradient_half_sq_Lp_le (hp : 2 ≤ p) (x y: LpSpace p d) :
  ∑ i, |half_sq_Lp' x i| * |y i| ≤ ‖x‖ * ‖y‖ := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  simp [half_sq_Lp']
  have h₁ : (p : ℝ) - 2 + 1 ≠ 0 := by ring_nf; apply ne_of_gt; simp; linarith
  conv_lhs =>
    congr; rfl; ext i
    rw [abs_mul, abs_mul, abs_rpow_of_nonneg, abs_rpow_of_nonneg]
    simp
    rw [mul_assoc, mul_assoc, ←mul_assoc (b := |x i|), ←Real.rpow_add_one']
    rfl
    apply abs_nonneg
    exact h₁
    apply abs_nonneg
    apply norm_nonneg
  rw [←mul_sum]
  grw [Real.inner_le_Lp_mul_Lq (p := p / (p - 1)) (q := p)]
  nth_rw 3 [PiLp.norm_eq_sum]
  simp
  apply le_of_eq
  rw [←mul_assoc]
  simp
  apply Or.inl
  simp_rw [div_eq_mul_inv]
  have : (p : ℝ) - 2 + 1 = (p : ℝ) - 1 := by ring
  rw [this]
  have h₂ : (p : ℝ) - 1 ≠ 0 := by apply ne_of_gt; simp; linarith
  conv_lhs =>
    congr; rfl; congr; congr; rfl; ext i
    rw [abs_rpow_of_nonneg, mul_comm, ←Real.rpow_mul, ←mul_assoc, mul_inv_cancel₀]
    simp
    rw [←Real.rpow_natCast]
    rfl
    exact h₂
    apply abs_nonneg
    apply abs_nonneg
    rw [mul_comm]
  rw [Real.rpow_mul, PiLp.norm_eq_sum]
  simp
  rw [←Real.rpow_add']
  ring_nf
  simp
  positivity
  simp; linarith
  simp; linarith
  positivity
  simp; linarith
  constructor
  simp
  ring_nf
  apply mul_inv_cancel₀
  simp; linarith
  apply div_pos
  simp; linarith; simp; linarith
  simp; linarith

end inner

section measurable

instance measurable_of_half_sq_Lp (hp : 1 ≤ p) : Measurable (half_sq_Lp : LpSpace p d → ℝ) := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  apply Continuous.measurable
  apply Continuous.mul
  apply continuous_const
  apply Continuous.pow
  apply Continuous.norm
  apply continuous_id

instance measurable_of_gradient_half_sq_Lp (hp : 2 ≤ p) :
  Measurable (half_sq_Lp' : LpSpace p d → LpSpace p d) := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  have hp2 : 2 - (p : ℝ) = (-1 : ℤ) * (p - 2 : ℕ) := by
    simp; rw [Nat.cast_sub]; simp; linarith
  apply measurable_pi_iff.mpr
  intro i
  apply Measurable.mul
  apply Measurable.mul
  apply Measurable.congr
  ext x
  rw [hp2, Real.rpow_mul, Real.rpow_natCast, Real.rpow_intCast]
  apply norm_nonneg
  apply Measurable.pow
  simp
  apply Measurable.norm
  apply measurable_id
  apply measurable_const
  apply Continuous.measurable
  apply Continuous.rpow_const
  apply Continuous.abs
  apply continuous_pi_iff.mp
  apply continuous_id
  intro x
  apply Or.inr
  simp; linarith
  apply measurable_pi_iff.mp
  apply measurable_id

end measurable

end StochasticApproximation
