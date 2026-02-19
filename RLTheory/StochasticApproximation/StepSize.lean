/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries

import RLTheory.Defs

open Real Finset Filter

lemma Finset.sum_Ico_sum_Ico {α : Type*}
  [AddCommMonoid α] {n m : ℕ} (hnm : n ≤ m)
  (f : ℕ → α) {t : ℕ → ℕ} (ht : Monotone t) :
  ∑ k ∈ Ico n m, ∑ i ∈ Ico (t k) (t (k + 1)), f i =
    ∑ i ∈ Ico (t n) (t m), f i := by
  refine Nat.le_induction ?base ?succ m hnm
  simp
  intro m hnm ih
  rw [←Ico_union_Ico_eq_Ico (b := m), sum_union, ih]
  simp
  nth_rw 3 [←Ico_union_Ico_eq_Ico (b := t m)]
  rw [sum_union]
  apply Ico_disjoint_Ico_consecutive
  apply ht hnm
  apply ht (Nat.le_succ m)
  apply Ico_disjoint_Ico_consecutive
  exact hnm
  simp

namespace StochasticApproximation

-- Local helper lemmas for rpow inequalities
private lemma rpow_le_of_le_rpow {a b : ℝ} {r : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ≤ b ^ r) : a ^ r⁻¹ ≤ b := by
  have := rpow_le_rpow ha h (inv_nonneg.mpr hr.le)
  rwa [←rpow_mul hb, mul_inv_cancel₀ (ne_of_gt hr), rpow_one] at this

private lemma rpow_neg_le_rpow_neg_of_le {a b : ℝ} {r : ℝ}
    (hr : 0 ≤ r) (ha : 0 < a) (_hb : 0 < b)
    (h : a ≤ b) : b ^ (-r) ≤ a ^ (-r) :=
  Real.rpow_le_rpow_of_nonpos ha h (neg_nonpos.mpr hr)

variable {α : ℕ → ℝ}

class RobbinsMonro (α : ℕ → ℝ) where
  pos : ∀ n, 0 < α n
  sum : Tendsto (fun n => ∑ k ∈ range n, α k) atTop atTop
  sqsum : Summable (fun n => (α n) ^ 2)

lemma RobbinsMonro.bdd (hα : RobbinsMonro α) :
  ∃ C, 0 ≤ C ∧ ∀ n, α n ≤ C := by
  have := (Summable.hasSum_iff_tendsto_nat hα.sqsum).mp hα.sqsum.hasSum
  have hmono := Monotone.ge_of_tendsto ?_ this
  refine ⟨?C, ?hCnonneg, ?hC⟩
  case C => exact max 1 (∑' n, (α n) ^ 2)
  case hCnonneg => simp
  case hC =>
    intro n
    by_cases h : α n ≤ 1
    apply h.trans (by apply le_max_left)
    simp at h
    calc
      α n
    _ ≤ α n ^ 2 := by
        rw [pow_two]
        conv_lhs => rw [←mul_one (α n)]
        apply mul_le_mul_of_nonneg_left
        linarith
        linarith
    _ ≤ ∑ i ∈ range (n + 1), α i ^ 2 := by
      apply single_le_sum (a := n)
      intro i hi
      positivity
      simp
    _ ≤ ∑' i, α i ^ 2 := by
      apply hmono
    _ ≤ max 1 (∑' n, (α n) ^ 2) := by
      apply le_max_right
  intro n m hnm
  simp
  apply sum_le_sum_of_subset_of_nonneg
  simp [hnm]
  intro i _ _
  positivity

structure Anchors where
  hα : RobbinsMonro α
  hα_mono : Antitone α
  T : ℕ → ℝ
  hT : RobbinsMonro T

section anchors

variable {anc : Anchors (α := α)}

def Anchors.le (m tm : ℕ) :=
  fun k => anc.T m ≤ ∑ i ∈ Ico tm k, α i

noncomputable instance {m tm : ℕ} : DecidablePred (anc.le m tm) := by
  intro k
  simp [Anchors.le]
  by_cases h : anc.T m ≤ ∑ i ∈ Ico tm k, α i
  case pos => exact isTrue h
  case neg => exact isFalse h

lemma Anchors.exists_le :
  ∀ m tm, ∃ k, anc.le m tm k := by
  intro m tm
  simp [le]
  have := (tendsto_add_atTop_iff_nat tm).mpr anc.hα.sum
  have := exists_le_of_tendsto_atTop this 0 (anc.T m + ∑ i ∈ range tm, α i)
  obtain ⟨k, ⟨_, hk⟩⟩ := this
  simp_rw [range_eq_Ico] at hk
  nth_rw 2 [←Ico_union_Ico_eq_Ico (b := tm)] at hk
  rw [sum_union, add_comm] at hk
  simp at hk
  use (k + tm)
  apply Ico_disjoint_Ico_consecutive
  simp
  simp

noncomputable def Anchors.t : ℕ → ℕ
| 0 => 0
| n + 1 =>
  let P := anc.le n (t n)
  let hP := anc.exists_le n (t n)
  Nat.find (p := P) hP

lemma Anchors.t_def : ∀ n, anc.t (n + 1) =
  Nat.find (p := anc.le n (anc.t n)) (anc.exists_le n (anc.t n)) :=
  by intro n; rfl

lemma Anchors.t_init : anc.t 0 = 0 := rfl

lemma Anchors.t_mono : ∀ n, anc.t n < anc.t (n + 1) := by
    intro n
    simp [t, le]
    intro m hm
    rw [Ico_eq_empty_iff.mpr]
    simp
    exact anc.hT.pos n
    simp
    exact hm

lemma Anchors.t_mono' : StrictMono anc.t := by
  intro n
  have : ∀ m, n ≤ m → n ≠ m → anc.t n < anc.t m := by
    apply Nat.le_induction
    simp
    intro m hm hnm _
    by_cases h : n = m
    rw [←h]
    apply t_mono
    have := hnm h
    have := anc.t_mono m
    linarith
  intro m hnm
  apply this m hnm.le hnm.ne

noncomputable def Anchors.β : ℕ → ℝ :=
  fun n => ∑ i ∈ Finset.Ico (anc.t n) (anc.t (n + 1)), α i

lemma Anchors.β_def : ∀ n,
  anc.β n = ∑ i ∈ Ico (anc.t n) (anc.t (n + 1)), α i := by
  intro n
  rfl

lemma Anchors.T_le_β :
  ∀ n, anc.T n ≤ anc.β n := by
  intro n
  simp [β]
  have := Nat.find_spec (p := anc.le n (anc.t n))
    (anc.exists_le n (anc.t n))
  simp [le] at this
  exact this

lemma Anchors.β_le_T_add_α :
  ∀ n, anc.β n ≤ anc.T n + α (anc.t (n + 1) - 1) := by
  intro n
  have := anc.t_mono n
  simp [Anchors.β]
  have := (Nat.le_find_iff (anc.exists_le n (anc.t n)) (anc.t (n + 1))).mp
    (anc.t_def n).le (anc.t (n + 1) - 1) ?_
  simp [Anchors.le] at this
  rw [←Ico_union_Ico_eq_Ico (b := anc.t (n + 1) - 1), sum_union]
  grw [this]
  rw [Nat.Ico_pred_singleton]
  simp
  omega
  apply Ico_disjoint_Ico_consecutive
  omega
  simp
  omega

lemma Anchors.sum_T_le_sum_α :
  ∀ m, ∑ k ∈ range m, anc.T k ≤ ∑ k ∈ range (anc.t m), α k := by
  intro m
  induction m with
  | zero =>
    simp
    apply sum_nonneg
    intro i hi
    exact (anc.hα.pos i).le
  | succ m ih =>
    simp_rw [range_eq_Ico] at *
    rw [←Ico_union_Ico_eq_Ico (b := m), sum_union]
    conv_rhs =>
      rw [←Ico_union_Ico_eq_Ico (b := t m) (by simp) ((anc.t_mono m).le)]
    rw [sum_union]
    grw [ih]
    simp
    exact T_le_β m
    apply Ico_disjoint_Ico_consecutive
    apply Ico_disjoint_Ico_consecutive
    simp
    simp

lemma Anchors.robbinsMonro_of_β : RobbinsMonro anc.β := by
  have hpos : ∀ n, 0 < anc.β n := by
    intro n
    simp [β]
    apply sum_pos
    intro i hi
    exact anc.hα.pos i
    simp
    apply t_mono
  constructor
  case pos => exact hpos
  case sum =>
    simp [β]
    apply Tendsto.congr
    intro n
    rw [range_eq_Ico, Finset.sum_Ico_sum_Ico, anc.t_init]
    simp
    exact anc.t_mono'.monotone
    rw [←range_eq_Ico]
    apply Tendsto.congr ?_ (anc.hα.sum.comp (anc.t_mono'.tendsto_atTop))
    intro n
    simp
  case sqsum =>
    apply Summable.of_nonneg_of_le
    intro n; positivity
    intro n
    grw [β_le_T_add_α, add_sq_le]
    exact (hpos n).le
    apply Summable.mul_left
    apply Summable.add
    exact anc.hT.sqsum
    let f := fun n => anc.t (n + 1) - 1
    have : Function.Injective f := by
      intro x y hxy
      simp [f] at hxy
      have : anc.t (x + 1) = anc.t (y + 1) := by
        have := anc.t_mono x
        have := anc.t_mono y
        omega
      have := anc.t_mono'.injective this
      simp at this
      exact this
    have := anc.hα.sqsum.comp_injective this
    apply Summable.congr this
    intro n
    simp [f]

noncomputable def SufficientlySparse (anc : Anchors (α := α)) : Prop :=
  ∃ C, 0 ≤ C ∧ ∀ n, α (anc.t n) ≤ C * anc.β n ^ 2

end anchors

noncomputable def inv_poly (ν : ℝ) (n₀ : ℕ) : ℝ → ℝ :=
  fun n => (n + n₀) ^ (-ν)

lemma robbinsMonro_of_inv_poly
  {ν : ℝ} (hν : 1 / 2 < ν ∧ ν ≤ 1) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
  RobbinsMonro fun n => inv_poly ν n₀ n := by
  constructor
  case pos =>
    intro n
    simp [inv_poly]
    positivity
  case sum =>
    simp [inv_poly]
    have := tendsto_sum_range_one_div_nat_succ_atTop
    have := (tendsto_add_atTop_iff_nat (n₀ - 1)).mpr this
    have := tendsto_atTop_add_const_right atTop
      (-∑ i ∈ range (n₀ - 1), 1 / ((i + 1) : ℝ)) this
    simp_rw [range_eq_Ico, ←sub_eq_add_neg] at this
    have h₁ : 0 ≤ n₀ - 1 := by linarith
    have h₂ : ∀ n, n₀ - 1 ≤ n + (n₀ - 1) := by intro n; linarith
    conv at this =>
      congr; ext n
      rw [←Ico_union_Ico_eq_Ico (b := n₀ - 1), sum_union, add_sub_cancel_left]
      rw [sum_Ico_eq_sum_range]
      simp
      rfl
      apply Ico_disjoint_Ico_consecutive
      exact h₁
      apply h₂
    apply tendsto_atTop_mono ?_ this
    intro n
    apply sum_le_sum
    intro k hk
    simp [Nat.cast_sub hn₀.ge]
    ring_nf
    rw [rpow_neg]
    apply (inv_le_inv₀ ?_ ?_).mpr
    grw [hν.2]
    simp
    rw [←add_zero 1]
    apply add_le_add
    exact_mod_cast hn₀
    simp
    positivity
    positivity
    positivity
  case sqsum =>
    simp [inv_poly]
    apply Summable.congr
    case hfg =>
      intro n
      rw [←rpow_mul_natCast]
      positivity
    have := summable_nat_rpow (p := -ν * (2 : ℕ)).mpr (by simp; linarith)
    obtain ⟨C, hC⟩ := this
    let C' := ∑ i ∈ range n₀, (i : ℝ) ^ (-ν * (2 : ℕ))
    rw [←sub_add_cancel (a := C)
      (b := C')] at hC
    have hC' := (hasSum_nat_add_iff n₀).mpr hC
    simp at *
    refine ⟨C - C', hC'⟩

set_option maxHeartbeats 400000 in
lemma anchors_of_inv_poly {ν : ℝ} (hν : ν ∈ Set.Ioo (2 / 3) 1) :
  ∃ anc : Anchors (α := fun n => inv_poly ν 2 n), SufficientlySparse anc:= by
  set α := fun n : ℕ => inv_poly ν 2 n
  simp at hν
  have h2ν : 2 - ν ≠ 0 := by linarith
  have h1ν : 0 < (1 - ν)⁻¹ := inv_pos_of_pos (by linarith)
  set zmin : ℝ := 1 / 2
  set zmax := ν / (2 - ν)
  have hzmax : zmax < 1 := by simp [zmax]; exact (div_lt_one₀ (by linarith)).mpr (by linarith)
  set z := 2⁻¹ * (zmin + zmax)
  have hzmaxgt : zmin < zmax := by
    simp [zmin, zmax]; ring_nf; exact (lt_mul_inv_iff₀ (by linarith)).mpr (by linarith)
  have hz : zmin < z ∧ z < zmax := by
    simp only [z]; ring_nf
    exact ⟨by apply lt_add_of_sub_left_lt; simp [←mul_one_sub]; ring_nf; simp [hzmaxgt],
           by apply add_lt_of_lt_sub_right; rw [←mul_one_sub]; ring_nf; simp [hzmaxgt]⟩
  have hzν : (1 - z) * -((1 - ν)⁻¹ * ν) ≤ -(z * 2) := by
    simp; rw [sub_mul]; apply le_add_of_sub_left_le; ring_nf
    apply sub_left_le_of_le_add; rw [←sub_eq_add_neg]; apply le_sub_left_of_add_le
    rw [mul_assoc, ←mul_add]; grw [hz.2.le]; simp [zmax]
    apply le_of_eq; rw [div_mul_eq_mul_div₀, mul_div_assoc]; simp
    refine Or.inl (div_eq_of_eq_mul (by linarith) (mul_right_cancel₀ (b := 1 - ν) (by linarith) ?_))
    rw [add_mul, mul_assoc, inv_mul_cancel₀, mul_comm (b := 2 - ν), mul_assoc, inv_mul_cancel₀]
    ring_nf; linarith; linarith
    apply add_nonneg; apply mul_nonneg; linarith; linarith; simp
  have hdiv_pos : 0 < (-ν + 1) / (-z + 1) := div_pos (by linarith) (by linarith)
  have hnrpow : ∀ n, 1 ≤ n → 0 < ((n : ℝ) + 1) ^ (1 - z) - 1 := fun n hn => by
    simp; exact one_lt_rpow (by simp; linarith) (by linarith)
  set η := 1 - (2 : ℝ) ^ (z - 1)
  have hη_pos : 0 < η := by
    simp only [η, sub_pos]
    have hz1 : z - 1 < 0 := by have : z < zmax := hz.2; linarith
    have := (rpow_lt_rpow_left_iff (by simp : (1 : ℝ) < 2)).mpr hz1
    simp at this; exact this
  have hη : ∀ n, 1 ≤ n → ((n : ℝ) + 1) ^ (1 - z) - 1 ≥ η * (n + 1) ^ (1 - z) := fun n hn => by
    simp; apply le_sub_right_of_add_le; apply add_le_of_le_sub_left; simp [←one_sub_mul, η]
    nth_rw 1 [←rpow_zero 2]; rw [show (0 : ℝ) = z - 1 + (1 - z) by ring, rpow_add (by simp)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h2n : 2 ≤ n + 1 := by linarith
    exact rpow_le_rpow (by linarith) h2n (by linarith)
  set T := fun n : ℕ => inv_poly z 1 n
  set anc : Anchors (α := α) := {
    T := T
    hα := robbinsMonro_of_inv_poly ⟨by linarith, by linarith⟩ (by simp)
    hα_mono := fun x y hxy => by
      simp [α, inv_poly]; exact rpow_le_rpow_of_nonpos (by linarith) (by simp [hxy]) (by linarith)
    hT := robbinsMonro_of_inv_poly ⟨hz.1, by linarith⟩ (le_refl 1)
  }
  have : ∃ C, 0 ≤ C ∧ ∀ (n : ℕ), α (anc.t n) ≤ C * anc.T n ^ 2 := by
    set C₁ := ((-ν + 1) / (-z + 1)) ^ (-((-ν + 1)⁻¹ * ν)) * η ^ (-((-ν + 1)⁻¹ * ν))
    refine ⟨max C₁ (α 0 / T 0 ^ 2), ?_, ?hC⟩
    · apply LE.le.trans _ (le_max_right _ _); simp [α, inv_poly, T]; positivity
    case hC =>
      intro n
      by_cases hn : n = 0
      case pos =>
        simp [hn, Anchors.t, anc]
        rw [max_mul_of_nonneg, div_mul_cancel₀]
        simp; simp [T]; simp [inv_poly]; positivity
      have hn : 1 ≤ n := by omega
      have := hnrpow n (by simp; linarith)
      have hineq := anc.sum_T_le_sum_α n
      simp [α] at hineq
      set f := fun n => inv_poly ν 2 (n - 1)
      have hf : AntitoneOn f (Set.Icc 0 (0 + ↑(anc.t n))) := fun x hx y hy hxy => by
        simp [f, inv_poly]; ring_nf
        exact rpow_le_rpow_of_nonpos (by simp at hx; linarith) (by linarith) (by linarith)
      have := AntitoneOn.sum_le_integral hf
      simp [f] at this
      conv_rhs at this =>
        simp [inv_poly]
      rw [intervalIntegral.integral_comp_add_right (f := fun x => x ^ (-ν)),
        integral_rpow] at this
      have hineq := hineq.trans this
      simp [anc, T] at hineq
      set f := fun n : ℝ => inv_poly z 1 n
      have hf : AntitoneOn f (Set.Icc 0 (0 + ↑n)) := fun x hx y hy hxy => by
        simp [f]; exact rpow_le_rpow_of_nonpos (by simp at hx; simp; linarith) (by linarith)
          (by have := hz.1; simp [zmin] at this; linarith)
      have := AntitoneOn.integral_le_sum hf
      simp [f, inv_poly] at this
      rw [intervalIntegral.integral_comp_add_right (f := fun x => x ^ (-z)),
        integral_rpow] at this
      simp at this
      simp [inv_poly] at hineq
      have hineq := this.trans hineq
      have this : -1 + 2 = (1 : ℝ) := by ring
      simp [this] at hineq
      have hineq := (mul_le_mul_of_nonneg_right hineq (by linarith : 0 ≤ -ν + 1)).trans_eq
        (div_mul_cancel₀ _ (by linarith : -ν + 1 ≠ 0))
      have hineq := hineq.trans (sub_le_self _ (by linarith : 0 ≤ (1 : ℝ)))
      have hineq := rpow_le_of_le_rpow (by linarith) ?_ ?_ hineq
      have hineq := hineq.trans (by linarith : (Anchors.t n : ℝ) - 1 + 2 ≤ (Anchors.t n : ℝ) + 2)
      have hineq := rpow_neg_le_rpow_neg_of_le (r := ν)
        (by linarith) ?_ ?_ hineq
      simp [α, inv_poly, anc, T]
      apply LE.le.trans
      apply le_of_eq_of_le (by simp) hineq
      rw [←Real.rpow_mul, ←Real.rpow_mul_natCast, div_mul_eq_mul_div,
        mul_div_assoc, mul_rpow]
      simp
      rw [mul_comm, max_mul_of_nonneg]
      apply LE.le.trans ?_ (by apply le_max_left)
      simp [C₁]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left
      simp_rw [neg_add_eq_sub]
      have := hη n (by simp; linarith)
      have := rpow_neg_le_rpow_neg_of_le
        (r := ((1 - ν)⁻¹ * ν)) ?_ ?_ ?_ this
      grw [this]
      rw [mul_rpow]
      apply mul_le_mul_of_nonneg_left
      rw [←Real.rpow_mul]
      apply (rpow_le_rpow_left_iff ?_).mpr
      exact hzν
      simp; linarith
      · positivity
      · positivity
      · positivity
      · positivity
      · apply mul_nonneg; apply le_of_lt; linarith; linarith
      · positivity
      · positivity
      · positivity
      · positivity
      · rw [neg_add_eq_sub]; positivity
      · apply div_nonneg; linarith; linarith
      · linarith
      · simp_rw [neg_add_eq_sub]; apply mul_nonneg; apply div_nonneg; linarith; linarith; linarith
      · apply rpow_pos_of_pos; simp_rw [neg_add_eq_sub]; apply mul_pos; apply div_pos; linarith; linarith; linarith
      · linarith
      · simp_rw [neg_add_eq_sub]; apply mul_nonneg; apply div_nonneg; linarith; linarith; linarith
      · linarith
      · simp; apply Or.inl; linarith
      · simp; apply Or.inl; linarith
  use anc
  obtain ⟨C, hCnonneg, hC⟩ := this
  refine ⟨C, hCnonneg, ?hC⟩
  intro n
  grw [hC]
  grw [anc.T_le_β]
  simp [anc, T, inv_poly]
  positivity

end StochasticApproximation
