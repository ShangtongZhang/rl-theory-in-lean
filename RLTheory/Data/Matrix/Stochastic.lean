/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp

import Mathlib.NumberTheory.FrobeniusNumber
import RLTheory.Data.Matrix.Mul

open Finset NNReal WithLp Matrix PiLp Nat ContractingWith Metric Bornology Filter Function
open scoped BigOperators
open scoped Topology

namespace StochasticMatrix

universe u
variable {S : Type u} [Fintype S]
abbrev l1Space (S : Type u) := WithLp 1 (S → ℝ)

local notation "‖"x"‖₁" => (nnnorm (E := l1Space S) x)
local notation "d₁("x","y")" => edist (α := l1Space S) x y

class StochasticVec (x : S → ℝ) where
  nonneg : ∀ s, 0 ≤ x s
  rowsum : ∑ s, x s = 1

lemma StochasticVec.le_one (x : S → ℝ) [StochasticVec x] (s : S) :
  x s ≤ 1 := by
  have hx : StochasticVec x := inferInstance
  rw [←hx.rowsum]
  apply single_le_sum
  intro z hz
  apply hx.nonneg
  simp

section simplex

abbrev Simplex (S : Type u) [Fintype S] := {x : l1Space S | StochasticVec x.ofLp}

instance (x : ↑(Simplex S)) : @StochasticVec S _ x.val.ofLp := x.property

instance : IsClosed (Simplex S) := by
  let l1Space := l1Space S
  have h1 : IsClosed {f : l1Space | ∀ s, 0 ≤ f.ofLp s} := by
    have hcl (s : S) : IsClosed {f : l1Space | 0 ≤ f.ofLp s} := by
      have hev : Continuous (fun f : l1Space => f.ofLp s) := by
        exact (continuous_apply s).comp (PiLp.continuous_ofLp 1 _)
      have half : IsClosed {x : ℝ | 0 ≤ x} :=
        isClosed_le continuous_const continuous_id
      simpa [Set.preimage] using half.preimage hev
    simpa [Set.setOf_forall] using isClosed_iInter hcl
  have h2 : IsClosed {f : l1Space | (∑ s, f.ofLp s) = 1} := by
    have hsum : Continuous (fun f : l1Space => ∑ s, f.ofLp s) := by
      apply continuous_finset_sum
      intro s _
      exact (continuous_apply s).comp (PiLp.continuous_ofLp 1 _)
    have htarget : IsClosed ({x : ℝ | x = 1} : Set ℝ) := by simp
    simpa [Set.preimage] using htarget.preimage hsum
  have h := IsClosed.inter h1 h2
  simp [←Set.setOf_and] at h
  have : {x : l1Space | StochasticVec x.ofLp} =
    {x | (∀ s, 0 ≤ x.ofLp s) ∧ (∑ s, x.ofLp s = 1)} := by
    ext1; simp; constructor
    · intro h; exact ⟨h.nonneg, h.rowsum⟩
    · intro h; exact ⟨h.1, h.2⟩
  unfold Simplex
  rw [this]
  exact h

instance : CompleteSpace (Simplex S) := IsClosed.completeSpace_coe

lemma l1_norm_eq_sum (f : l1Space S) : ‖f‖ = ∑ s, |f.ofLp s| := by
  simpa using (PiLp.norm_eq_sum (f := f))

lemma l1_norm_eq_one (x : l1Space S) [StochasticVec x.ofLp]
  : ‖x‖₊ = 1 := by
  apply NNReal.eq
  simp [l1_norm_eq_sum]
  have hx := (inferInstance : StochasticVec x.ofLp)
  rw [←hx.rowsum]
  apply sum_congr rfl
  intro s hs
  rw [abs_of_nonneg (hx.nonneg s)]

lemma simplex_subset_closedBall :
  (Simplex S) ⊆ closedBall (0 : l1Space S) 1 := by
  intro x hx
  simp only [mem_closedBall, dist_zero_right, l1_norm_eq_sum]
  rw [←hx.rowsum]
  apply sum_le_sum
  intro i _
  rw [abs_of_nonneg (hx.nonneg i)]

lemma simples_is_compact : IsCompact (Simplex S) := by
  apply isCompact_of_isClosed_isBounded
  case hc => infer_instance
  case hb =>
    apply (isBounded_iff_subset_closedBall (s := Simplex S) (0 : l1Space S)).mpr
    refine ⟨1, simplex_subset_closedBall⟩

end simplex

class RowStochastic (P : Matrix S S ℝ) where
  stochastic: ∀ s, StochasticVec (P s)

lemma sum_svec_mul_smat_eq_one
  (μ : S → ℝ) [StochasticVec μ] (P : Matrix S S ℝ) [RowStochastic P]
  : ∑ i, ∑ j, μ i * P i j = 1 := by
  have hμ := (inferInstance : StochasticVec μ)
  have hP := (inferInstance : RowStochastic P).stochastic
  rw [sum_congr rfl]
  rotate_left
  intro i hi
  apply Eq.trans
  rw [←mul_sum]
  simp [(hP i).rowsum]
  rfl
  simp [hμ.rowsum]

instance svec_mul_smat_is_svec
  (μ : S → ℝ) [StochasticVec μ] (P : Matrix S S ℝ) [RowStochastic P]:
  StochasticVec (μ ᵥ* P) := by
  have hμ := (inferInstance : StochasticVec μ)
  have hP := (inferInstance : RowStochastic P).stochastic
  constructor
  case nonneg =>
    intro j
    have : 0 ≤ ∑ i, μ i * P i j := by
      refine sum_nonneg ?_
      intro i _
      exact mul_nonneg (hμ.nonneg i) ((hP i).nonneg j)
    simpa [Matrix.vecMul] using this
  case rowsum =>
    simp [vecMul]
    simp [dotProduct]
    rw [sum_comm]
    apply sum_svec_mul_smat_eq_one

instance smat_mul_smat_is_smat
  (P Q : Matrix S S ℝ) [RowStochastic P] [RowStochastic Q] :
  RowStochastic (P * Q) := by
  have hP := (inferInstance : RowStochastic P).stochastic
  have hQ := (inferInstance : RowStochastic Q).stochastic
  constructor; intro i; constructor
  case nonneg =>
    intro j
    have : 0 ≤ ∑ k, P i k * Q k j := by
      refine sum_nonneg ?_
      intro k _
      exact mul_nonneg ((hP i).nonneg k) ((hQ k).nonneg j)
    simpa [Matrix.mul_apply] using this
  case rowsum =>
    calc
      ∑ j, (P * Q) i j
    _ = ∑ j, ∑ k, P i k * Q k j := by
        simp [Matrix.mul_apply]
    _ = ∑ k, ∑ j, P i k * Q k j := by
        simpa [mul_comm] using
          (sum_comm :
            ∑ j, ∑ k, P i k * Q k j = ∑ k, ∑ j, P i k * Q k j)
    _ = ∑ k, P i k * (∑ j, Q k j) := by
        simp [Finset.mul_sum]
    _ = ∑ k, P i k * 1 := by
        apply sum_congr rfl
        intro j _; simp [(inferInstance : StochasticVec (Q j)).rowsum]
    _ = ∑ k, P i k := by simp
    _ = 1 := (inferInstance : StochasticVec (P i)).rowsum

instance smat_pow_is_smat [DecidableEq S]
  (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ) :
  RowStochastic (P ^ n) := by
  induction n with
  | zero =>
    have hI : RowStochastic (1 : Matrix S S ℝ) := by
      constructor; intro i; constructor
      case nonneg =>
        intro j
        by_cases h : i = j
        · rw [h]; simp
        · exact (Matrix.one_apply_ne (α := ℝ) h).ge
      case rowsum =>
        simp [Matrix.one_apply]
    exact hI
  | succ n ih =>
    simp_rw [pow_add, pow_one]
    exact smat_mul_smat_is_smat (P ^ n) P

lemma chapman_kolmogorov_eq_ge [DecidableEq S]
  (P : Matrix S S ℝ) [RowStochastic P] (m n : ℕ) (i j : S) :
  ∀ k, (P ^ (m + n)) i j ≥ (P ^ m) i k * (P ^ n) k j := by
  have hP := (inferInstance : RowStochastic P).stochastic
  intro k
  rw [pow_add]
  simp [Matrix.mul_apply]
  rw [←sum_erase_add (a := k)]
  apply sub_nonneg.mp
  rw [add_sub_cancel_right]
  apply sum_nonneg
  intro l hl
  apply mul_nonneg
  · have hP := RowStochastic.stochastic (P := P ^ m)
    exact (hP i).nonneg l
  · have hP := RowStochastic.stochastic (P := P ^ n)
    exact (hP l).nonneg j
  · simp

section minorization

variable [DecidableEq S]

class Irreducible (P : Matrix S S ℝ) [RowStochastic P] where
  irreducible : ∀ i j, ∃ n : ℕ, 0 < (P ^ n) i j

/-- The set of positive return times for state i -/
noncomputable def return_times (P : Matrix S S ℝ) [RowStochastic P] (i : S)
  : Set ℕ := {n : ℕ | 1 ≤ n ∧ 0 < (P ^ n) i i}

/-- Return times are closed under addition (used via AddSubmonoid.closure) -/
lemma return_times_add_mem (P : Matrix S S ℝ) [RowStochastic P] (i : S)
    {a b : ℕ} (ha : a ∈ return_times P i) (hb : b ∈ return_times P i) :
    a + b ∈ return_times P i := by
  simp only [return_times, Set.mem_setOf_eq] at ha hb ⊢
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  constructor
  · linarith
  · calc
      0 < (P ^ a) i i * (P ^ b) i i := mul_pos ha2 hb2
    _ ≤ (P ^ (a + b)) i i := (chapman_kolmogorov_eq_ge P a b i i i).le

/-- A stochastic matrix is aperiodic if for each state, the GCD of return times is 1 -/
class Aperiodic (P : Matrix S S ℝ) [RowStochastic P] where
  aperiodic : ∀ i, Nat.setGcd (return_times P i) = 1

theorem eventually_positive [Nonempty S] (P : Matrix S S ℝ) [RowStochastic P]
  [Irreducible P] [Aperiodic P] :
  ∃ N, ∀ n i j, N ≤ n → 0 < (P ^ n) i j := by
  have h_ni : ∀ i, ∃ n₀, ∀ n, n₀ ≤ n → n ∈ return_times P i ∨ n = 0 := fun i => by
    have hcl : ∀ x, x ∈ AddSubmonoid.closure (return_times P i) → x ∈ return_times P i ∨ x = 0 := by
      intro x hx; induction hx using AddSubmonoid.closure_induction with
      | mem _ hy => exact Or.inl hy
      | zero => exact Or.inr rfl
      | add _ _ _ _ iha ihb =>
        rcases iha with ha | ha0 <;> rcases ihb with hb | hb0
        · exact Or.inl (return_times_add_mem P i ha hb)
        all_goals simp_all
    obtain ⟨n₀, hn₀⟩ := Nat.exists_mem_closure_of_ge (return_times P i)
    refine ⟨n₀, fun n hn => ?_⟩
    rcases eq_or_ne n 0 with rfl | hn0; · exact Or.inr rfl
    rcases hcl n (hn₀ n hn (by simp [Aperiodic.aperiodic (P := P) i])) with h | h
    · exact Or.inl h
    · exact (hn0 h).elim
  let ni := fun i => (h_ni i).choose
  let n₀ := sup' _ univ_nonempty ni + 1
  have hn₀ : ∀ n i, n₀ ≤ n → 0 < (P ^ n) i i := fun n i hn => by
    have hni : ni i ≤ n := by have := le_sup' ni (mem_univ i); omega
    rcases (h_ni i).choose_spec n hni with h | h
    · exact h.2
    · omega
  let nij := fun ij : S × S => (Irreducible.irreducible (P := P) ij.1 ij.2).choose
  let n₁ := sup' _ (by simp : (univ (α := S × S)).Nonempty) nij
  refine ⟨n₀ + n₁, fun n i j hn => ?_⟩
  have hnij_le : nij (i, j) ≤ n₁ := le_sup' nij (mem_univ (i, j))
  have hle : nij (i, j) ≤ n := by omega
  calc 0 < (P ^ nij (i,j)) i j * (P ^ (n - nij (i,j))) j j :=
        mul_pos (Irreducible.irreducible (P := P) i j).choose_spec (hn₀ _ j (by omega))
    _ ≤ (P ^ n) i j := by
      have := chapman_kolmogorov_eq_ge P (nij (i,j)) (n - nij (i,j)) i j j
      simp only [Nat.add_sub_cancel' hle] at this; exact this

class DoeblinMinorization (P : Matrix S S ℝ) [RowStochastic P] where
  minorize : ∃ (ε : ℝ) (ν : S → ℝ),
    0 < ε ∧ ε < 1 ∧ StochasticVec ν ∧ ∀ i j, P i j ≥ ε * ν j

theorem smat_minorizable_with_large_pow
  [Nonempty S] (P : Matrix S S ℝ)
  [RowStochastic P] [Irreducible P] [Aperiodic P] :
  ∃ N, 1 ≤ N ∧ DoeblinMinorization (P ^ N) := by
  obtain ⟨n₀, hn₀⟩ := eventually_positive P
  let n₁ := n₀ + 1
  have hn₀ := hn₀ n₁
  let hnij := fun ij : S × S => hn₀ ij.1 ij.2 (by unfold n₁; simp)
  have : (Finset.univ (α := S × S)).Nonempty := by simp
  let δij := fun ij : S × S => (P ^ n₁) ij.1 ij.2
  let δ := inf' (Finset.univ (α := S × S)) this δij
  have hδinf : ∀ ij, δ ≤ δij ij := by
    intro ij
    have : ij ∈ Finset.univ (α := S × S) := by simp
    have := inf'_le (f := δij) this
    exact this
  have hδrange : 0 < δ ∧ δ ≤ 1:= by
    obtain ⟨ij, hij, hijinf⟩ := exists_mem_eq_inf' this δij
    have hδdef : δ = δij ij := by unfold δ; simp [hijinf]
    unfold δij at this
    have := hnij ij
    constructor
    case left => linarith
    case right =>
      obtain ⟨nonneg, rowsum⟩ := RowStochastic.stochastic (P := P ^ n₁) (ij.1)
      rw [hδdef, ←rowsum, ←sum_erase_add (a := ij.2) (h := by simp)]
      unfold δij
      apply sub_nonneg.mp
      rw [add_sub_cancel_right]
      apply sum_nonneg
      · intro j hj; exact nonneg j
  let δ' := δ * 1 / 2 * 1 / Fintype.card S
  refine ⟨n₁, ?hNpos, ?hN⟩
  case hNpos => unfold n₁; simp
  case hN =>
    constructor
    let ν : S → ℝ := fun j => 1 / Fintype.card S
    refine ⟨?ε, ?ν, ?hεpos, ?hεlt1, ?hν, ?hP⟩
    case ε => exact δ' * Fintype.card S
    case hεlt1 => unfold δ'; simp; linarith
    case hεpos => unfold δ'; simp; linarith
    case ν => exact ν
    case hν =>
      constructor
      case nonneg => intro s; simp [ν]
      case rowsum =>
      simp [ν, Finset.sum_const, Finset.card_univ]
    case hP =>
      intro i j
      have := hδinf (i, j)
      simp [δij] at this
      simp [ν]
      unfold δ'
      have : δ * 1 / 2 * 1 / Fintype.card S ≤ δ := by
        simp
        rw [div_div]
        apply mul_le_of_le_one_right (ha := hδrange.1.le) _
        have : 0 < Fintype.card S := by
          apply Fintype.card_pos_iff.mpr inferInstance
        have : 1 ≤ 2 * Fintype.card S := by linarith [Nat.le_of_lt this]
        set z := (2 : ℝ) * Fintype.card S
        have h1lez : 1 ≤ z := by unfold z; exact_mod_cast this
        have hpos : 0 < z := by linarith
        apply (inv_le_comm₀ hpos (by simp)).mpr
        simp
        exact h1lez
      linarith

end minorization

section contraction

private def broadcast (ν : S → ℝ) : Matrix S S ℝ :=
  Matrix.of (fun _ s' => ν s')

private lemma vecMul_broadcast (v : S → ℝ) (ν : S → ℝ) [StochasticVec ν] :
    v ᵥ* broadcast ν = fun j => (∑ i, v i) * ν j := by
  classical
  funext j
  simp [broadcast, Matrix.vecMul, Finset.sum_mul, dotProduct]

theorem smat_nonexpansive_in_l1 (Q : Matrix S S ℝ) [RowStochastic Q] :
    ∀ (x y : S → ℝ),
      ‖WithLp.toLp 1 (x ᵥ* Q - y ᵥ* Q)‖₊ ≤ ‖WithLp.toLp 1 (x - y)‖₊ := by
  intro x y
  have hQ := (inferInstance : RowStochastic Q).stochastic
  have hxy : x ᵥ* Q - y ᵥ* Q = fun j => ∑ i, (x i - y i) * Q i j := by
    funext j
    simp [Matrix.vecMul, sub_eq_add_neg, sub_eq_add_neg, sum_add_distrib, add_mul, dotProduct]
  have hnorm : (‖WithLp.toLp 1 (x ᵥ* Q - y ᵥ* Q)‖₊ : ℝ) = ∑ j, |∑ i, (x i - y i) * Q i j| := by
    rw [coe_nnnorm]
    have h1 := l1_norm_eq_sum (WithLp.toLp 1 (x ᵥ* Q - y ᵥ* Q))
    simp only [Pi.sub_apply] at h1
    convert h1 using 2 with j
    congr 1
    have := congrFun hxy j
    simp at this
    exact this.symm
  have hnorm2 : (‖WithLp.toLp 1 (x - y)‖₊ : ℝ) = ∑ i, |x i - y i| := by
    rw [coe_nnnorm]
    have := l1_norm_eq_sum (WithLp.toLp 1 (x - y))
    simp only [Pi.sub_apply] at this
    exact this
  have : ∑ j, |∑ i, (x i - y i) * Q i j| ≤ ∑ i, |x i - y i| := by
    calc
      ∑ j, |∑ i, (x i - y i) * Q i j|
    _ ≤ ∑ j, ∑ i, |(x i - y i) * Q i j| := by
      apply sum_le_sum
      · intro j _; exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ i, |(x i - y i)| * Q i j := by
      apply sum_le_sum
      · intro j _; apply sum_le_sum;
        · intro i _; rw [abs_mul]; exact mul_le_mul_of_nonneg_left
            (le_of_eq (abs_of_nonneg ((hQ i).nonneg j))) (abs_nonneg _)
    _ = ∑ i, |x i - y i| * (∑ j, Q i j) := by
      conv_lhs => rw [Finset.sum_comm]
      simp [mul_comm, sum_mul]
    _ = ∑ i, |x i - y i| := by
      apply sum_congr rfl
      · intro i _; simp [(hQ i).rowsum]
  refine (NNReal.coe_le_coe.mp ?_)
  rw [hnorm, hnorm2]
  linarith

theorem smat_pow_nonexpansive_in_l1 [DecidableEq S] (Q : Matrix S S ℝ) [RowStochastic Q] :
    ∀ n (x y : S → ℝ),
      ‖WithLp.toLp 1 (x ᵥ* Q ^ n - y ᵥ* Q ^ n)‖₊ ≤ ‖WithLp.toLp 1 (x - y)‖₊ := by
  intro n x y
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [pow_succ, ←Matrix.vecMul_vecMul]
    have := smat_nonexpansive_in_l1 Q (x ᵥ* Q ^ n) (y ᵥ* Q ^ n)
    exact this.trans ih

def smat_as_operator (P : Matrix S S ℝ) [RowStochastic P] :
  ↑(Simplex S) → ↑(Simplex S) :=
  fun μ => ⟨WithLp.toLp 1 (μ.val.ofLp ᵥ* P), by
    exact svec_mul_smat_is_svec μ.val.ofLp P
  ⟩

lemma smat_as_operator_iter [DecidableEq S]
  (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ)
  : (smat_as_operator P)^[n] = fun μ => ⟨WithLp.toLp 1 (μ.val.ofLp ᵥ* (P ^ n)), by
    exact svec_mul_smat_is_svec μ.val.ofLp (P ^ n)
  ⟩ := by
  induction n with
  | zero => funext μ; simp only [Function.iterate_zero, id_eq, pow_zero, Matrix.vecMul_one]
  | succ n ih =>
    funext μ
    simp only [Function.iterate_succ, Function.comp_apply, ih, smat_as_operator]
    congr 1
    simp only [Matrix.vecMul_vecMul]
    rw [(pow_succ' P n).symm]

theorem smat_contraction_in_simplex
  (P : Matrix S S ℝ) [RowStochastic P] [DoeblinMinorization P] :
    ∃ K, 0 < K ∧ ContractingWith K (smat_as_operator P)
  := by
    have hP := (inferInstance : RowStochastic P).stochastic
    obtain ⟨ε, ν, hεpos, hεlt1, hν, h_minorization⟩
      := (inferInstance : DoeblinMinorization P).minorize
    have hnonzero: 1 - ε ≠ 0 := by linarith
    let Q := (1 - ε)⁻¹ • (P - ε • broadcast ν)
    have h_decomp : P = ε • (broadcast ν) + (1 - ε) • Q := by
      unfold Q; simp [hnonzero];
    have hε0 : 0 ≤ 1 - ε := by linarith

    have hQ : RowStochastic Q := by
      constructor; intro i; constructor
      case nonneg =>
        unfold Q
        intro j
        unfold broadcast
        simp
        have hinv_nonneg : 0 ≤ (1 - ε)⁻¹ := by
          exact inv_nonneg.mpr hε0
        have hdiff_nonneg : 0 ≤ P i j - ε * ν j := by
          have := h_minorization i j
          exact sub_nonneg.mpr this
        exact mul_nonneg hinv_nonneg hdiff_nonneg
      case rowsum =>
        unfold Q
        unfold broadcast
        simp
        simp [mul_sub]
        set a := (1 - ε)⁻¹
        calc
          ∑ x, a * P i x - ∑ x, a * (ε * ν x)
        _ = ∑ x, P i x * a - ∑ x, ν x * ε * a := by simp [mul_comm]
        _ = (∑ x, P i x) * a - (∑ x, ν x) * ε * a := by simp [sum_mul]
        _ = a - ε * a := by simp [(hP i).rowsum, hν.rowsum]
        _ = 1 * a - ε * a := by simp
        _ = (1 - ε) * a := by rw [sub_mul]
        _ = 1 := by unfold a; simp [hnonzero]

    let K : ℝ≥0 := ⟨1 - ε, hε0⟩
    refine ⟨?K, ?hKpos, ?hK⟩
    case K => exact K
    case hKpos =>
      unfold K;
      have : 0 < 1 - ε := by linarith
      exact_mod_cast this
    case hK =>
      unfold ContractingWith
      unfold LipschitzWith
      unfold smat_as_operator
      refine ⟨?hKlt1, ?hLip⟩
      case hLip =>
        intro x y
        simp
        have hx_sum : ∑ i, x.val.ofLp i = 1 := (x.property).rowsum
        have hy_sum : ∑ i, y.val.ofLp i = 1 := (y.property).rowsum
        have hxB : x.val.ofLp ᵥ* broadcast ν = ν := by
          funext j
          simp [vecMul_broadcast, hx_sum]
        have hyB : y.val.ofLp ᵥ* broadcast ν = ν := by
          funext j
          simp [vecMul_broadcast, hy_sum]
        have hxP : x.val.ofLp ᵥ* P =
          ε • (x.val.ofLp ᵥ* broadcast ν) + (1 - ε) • (x.val.ofLp ᵥ* Q) := by
          rw [h_decomp]
          simp [Matrix.vecMul_add, Matrix.vecMul_smul]
        have hyP : y.val.ofLp ᵥ* P =
          ε • (y.val.ofLp ᵥ* broadcast ν) + (1 - ε) • (y.val.ofLp ᵥ* Q) := by
          rw [h_decomp]
          simp [Matrix.vecMul_add, Matrix.vecMul_smul]
        have diff_eq :
            (x.val.ofLp ᵥ* P) - (y.val.ofLp ᵥ* P)
            = (1 - ε) • ((x.val.ofLp ᵥ* Q) - (y.val.ofLp ᵥ* Q)) := by
          calc
            (x.val.ofLp ᵥ* P) - (y.val.ofLp ᵥ* P)
          _ = (ε • (x.val.ofLp ᵥ* broadcast ν) + (1 - ε) • (x.val.ofLp ᵥ* Q))
              - (ε • (y.val.ofLp ᵥ* broadcast ν) + (1 - ε) • (y.val.ofLp ᵥ* Q)) := by
              simp [hxP, hyP]
          _ = ε • ((x.val.ofLp ᵥ* broadcast ν) - (y.val.ofLp ᵥ* broadcast ν))
              + (1 - ε) • ((x.val.ofLp ᵥ* Q) - (y.val.ofLp ᵥ* Q)) := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                    sub_eq_add_neg]
          _ = (1 - ε) • ((x.val.ofLp ᵥ* Q) - (y.val.ofLp ᵥ* Q)) := by
              simp [hxB, hyB]

        have hxynorm : ‖WithLp.toLp 1 (x.val.ofLp ᵥ* P - y.val.ofLp ᵥ* P)‖₊
          ≤ K * ‖x.val - y.val‖₊ := by
            have h : WithLp.toLp 1 (x.val.ofLp ᵥ* P - y.val.ofLp ᵥ* P)
              = (1 - ε) • WithLp.toLp 1 (x.val.ofLp ᵥ* Q - y.val.ofLp ᵥ* Q) := by
              simp only [diff_eq, ← WithLp.toLp_smul]
            rw [h, nnnorm_smul]
            have hK : ‖(1 - ε : ℝ)‖₊ = K := by rw [Real.nnnorm_of_nonneg hε0]
            rw [hK]
            have hLipQ := @smat_nonexpansive_in_l1 S _ Q hQ x.val.ofLp y.val.ofLp
            exact mul_le_mul_right hLipQ K

        calc
          edist (smat_as_operator P x) (smat_as_operator P y)
        _ = edist (WithLp.toLp 1 (x.val.ofLp ᵥ* P)) (WithLp.toLp 1 (y.val.ofLp ᵥ* P)) := rfl
        _ = ‖WithLp.toLp 1 (x.val.ofLp ᵥ* P - y.val.ofLp ᵥ* P)‖₊ := by
            rw [edist_nndist]
            simp only [nndist_eq_nnnorm, ← WithLp.toLp_sub]
        _ ≤ K * ‖x.val - y.val‖₊ := by exact_mod_cast hxynorm
        _ = K * edist x.val y.val := by
            simp [edist_nndist, nndist_eq_nnnorm]
        _ = K * edist x y := by rfl
      case hKlt1 =>
        unfold K
        have : 1 - ε < 1 := by linarith
        exact this

end contraction

section stationary_distribution

class Stationary (μ : S → ℝ) (P : Matrix S S ℝ) : Prop where
  stationary : μ ᵥ* P = μ

variable [DecidableEq S]

lemma multi_step_stationary
  (μ : S → ℝ) [StochasticVec μ]
  (P : Matrix S S ℝ) [RowStochastic P]
  (n : ℕ) [Stationary μ P] :
  Stationary μ (P ^ n) := by
  constructor
  induction n with
  | zero =>
    simp [Matrix.vecMul_one]
  | succ n ih =>
    have := (inferInstance : Stationary μ P).stationary
    rw [pow_succ, ←vecMul_vecMul, ih, this]

theorem pos_of_stationary
  (μ : S → ℝ) [StochasticVec μ]
  (P : Matrix S S ℝ) [RowStochastic P] [Irreducible P]
  [Stationary μ P] :
  ∀ s, 0 < μ s := by
  by_contra h
  push_neg at h
  set s := h.choose with hsdef
  have hμ := (inferInstance : StochasticVec μ)
  have hs : μ s = 0 := by
    have := hμ.nonneg s
    linarith [h.choose_spec]
  have hμ0 : ∀ s', μ s' = 0 := by
    intro s'
    have := (inferInstance : Irreducible P).irreducible s' s
    obtain ⟨n, hn⟩ := this
    obtain hPn := (multi_step_stationary μ P n).stationary
    have := congrFun hPn s
    simp [vecMul, dotProduct] at this
    rw [hs] at this
    have := (sum_eq_zero_iff_of_nonneg ?_).mp this s' ?_
    simp at this
    apply (or_iff_left ?_).mp this
    simp [hn.ne']
    intro i hi
    apply mul_nonneg
    apply hμ.nonneg
    have := (inferInstance : RowStochastic (P ^ n)).stochastic
    apply (this i).nonneg
    simp
  have := hμ.rowsum
  simp_rw [hμ0] at this
  simp at this


noncomputable def cesaro_average
  (x₀ : S → ℝ) [StochasticVec x₀]
  (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ)
  : S → ℝ :=
  (n + 1 : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), x₀ ᵥ* (P ^ k)

lemma cesaro_average_is_svec
  (x₀ : S → ℝ) [StochasticVec x₀]
  (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ)
  : StochasticVec (cesaro_average x₀ P n) := by
  constructor
  case nonneg =>
    intro i
    simp [cesaro_average]
    apply mul_nonneg
    case ha => exact inv_nonneg.mpr (by linarith)
    case hb =>
      apply sum_nonneg
      intro k hk
      exact (svec_mul_smat_is_svec x₀ (P ^ k)).nonneg i
  case rowsum =>
    unfold cesaro_average
    simp
    rw [←mul_sum]
    rw [Finset.sum_comm]
    have : ∑ k ∈ Finset.range (n + 1), ∑ i, (x₀ ᵥ* (P ^ k)) i = n + 1 := by calc
         ∑ k ∈ Finset.range (n + 1), ∑ i, (x₀ ᵥ* (P ^ k)) i
       _ = ∑ k ∈ Finset.range (n + 1), 1 := by
           apply sum_congr rfl
           intro k hk
           exact (svec_mul_smat_is_svec x₀ (P ^ k)).rowsum
       _ = n + 1 := by simp
    rw [this, mul_comm]
    apply mul_inv_cancel₀
    linarith

lemma cesaro_average_almost_invariant
  (x₀ : S → ℝ) [StochasticVec x₀] (P : Matrix S S ℝ) [RowStochastic P]
  : ∀ n, ‖WithLp.toLp 1 ((cesaro_average x₀ P n) ᵥ* P - cesaro_average x₀ P n)‖ ≤ 2 / (n + 1)  := by
    intro n
    unfold cesaro_average
    have hn : 0 < (n : ℝ) + 1 := by linarith
    have hstep : ∀ k, (x₀ ᵥ* P ^ k) ᵥ* P - x₀ ᵥ* P ^ k =
                      x₀ ᵥ* P ^ (k + 1) - x₀ ᵥ* P ^ k := by
      intro k
      rw [Matrix.vecMul_vecMul, ← pow_succ]
    calc
        ‖WithLp.toLp 1 (((n + 1 : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), x₀ ᵥ* P ^ k) ᵥ* P -
          (n + 1 : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), x₀ ᵥ* P ^ k)‖
      _ = ‖WithLp.toLp 1 ((n + 1 : ℝ)⁻¹ • ((∑ k ∈ Finset.range (n + 1), x₀ ᵥ* P ^ k) ᵥ* P) -
          (n + 1 : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), x₀ ᵥ* P ^ k)‖ := by
        rw [Matrix.smul_vecMul]
      _ = ‖WithLp.toLp 1 ((n + 1 : ℝ)⁻¹ • ((∑ k ∈ Finset.range (n + 1), x₀ ᵥ* P ^ k) ᵥ* P -
          ∑ k ∈ Finset.range (n + 1), x₀ ᵥ* P ^ k))‖ := by
        rw [smul_sub]
      _ = ‖WithLp.toLp 1 ((n + 1 : ℝ)⁻¹ • (∑ k ∈ Finset.range (n + 1),
          ((x₀ ᵥ* P ^ k) ᵥ* P - x₀ ᵥ* P ^ k)))‖ := by
        congr 3
        rw [Finset.sum_sub_distrib, Matrix.sum_vecMul]
      _ = ‖WithLp.toLp 1 ((n + 1 : ℝ)⁻¹ • (∑ k ∈ Finset.range (n + 1),
          (x₀ ᵥ* P ^ (k + 1) - x₀ ᵥ* P ^ k)))‖ := by
        congr 3
        apply Finset.sum_congr rfl
        intro k _
        exact hstep k
      _ = ‖WithLp.toLp 1 ((n + 1 : ℝ)⁻¹ • (x₀ ᵥ* P ^ (n + 1) - x₀ ᵥ* P ^ 0))‖ := by
        congr 2
        rw [← Finset.sum_range_sub (f := fun k => x₀ ᵥ* P ^ k)]
      _ = ‖(n + 1 : ℝ)⁻¹ • WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1) - x₀)‖ := by
        rw [← WithLp.toLp_smul]
        congr 2
        simp only [pow_zero, Matrix.vecMul_one]
      _ = |(n + 1 : ℝ)⁻¹| * ‖WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1) - x₀)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = (n + 1 : ℝ)⁻¹ * ‖WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1) - x₀)‖ := by
        rw [abs_of_pos (inv_pos.mpr hn)]
      _ ≤ (n + 1 : ℝ)⁻¹ * 2 := by
        gcongr
        have : ‖WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1) - x₀)‖₊ ≤ 2 := by calc
            ‖WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1) - x₀)‖₊
          _ = ‖WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1)) - WithLp.toLp 1 x₀‖₊ := by
            rw [← WithLp.toLp_sub]
          _ ≤ ‖WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1))‖₊ + ‖WithLp.toLp 1 x₀‖₊ := by
            exact nnnorm_sub_le _ _
          _ = 1 + 1 := by
            have h1 : ‖WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1))‖₊ = 1 :=
              l1_norm_eq_one (WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1)))
            have h2 : ‖WithLp.toLp 1 x₀‖₊ = 1 := l1_norm_eq_one (WithLp.toLp 1 x₀)
            simp only [h1, h2]
          _ = 2 := by ring
        exact_mod_cast this
      _ = 2 / (n + 1) := by ring

variable [Nonempty S]

noncomputable abbrev uniform_distribution : S → ℝ := fun _ => 1 / Fintype.card S

instance : StochasticVec (S := S) uniform_distribution := by
  constructor
  case nonneg => intro s; simp [uniform_distribution]
  case rowsum =>
    simp [uniform_distribution, Finset.sum_const, Finset.card_univ]

instance : Nonempty ↑(Simplex S) := by
  refine ⟨⟨WithLp.toLp 1 uniform_distribution, ?_⟩⟩
  show StochasticVec (WithLp.toLp 1 uniform_distribution).ofLp
  rw [WithLp.ofLp_toLp]
  infer_instance

theorem stationary_distribution_exists (P : Matrix S S ℝ) [RowStochastic P]
  : ∃ μ : S → ℝ, StochasticVec μ ∧ Stationary μ P := by
  let x₀ := uniform_distribution (S := S)
  let xn : ℕ → l1Space S := fun n => WithLp.toLp 1 (cesaro_average x₀ P n)
  have hs := simples_is_compact (S := S)
  have hx : ∀ n, xn n ∈ (Simplex S) := by
    intro n
    show StochasticVec (WithLp.toLp 1 (cesaro_average x₀ P n)).ofLp
    rw [WithLp.ofLp_toLp]
    exact cesaro_average_is_svec x₀ P n
  obtain ⟨μ, hμ, hstationary⟩ := IsCompact.tendsto_subseq hs hx
  refine ⟨?μ, ?hμ, ?hstationary⟩
  case μ => exact μ.ofLp
  case hμ => exact hμ
  case hstationary =>
    constructor
    obtain ⟨nk, hn_increasing, hn_lim⟩ := hstationary
    have ha : Tendsto (fun n => ‖xn (nk n) - μ‖) atTop (𝓝 0) := by
      have := tendsto_iff_norm_sub_tendsto_zero.mp hn_lim
      convert this using 2
    have halmostinv : ∀ n, ‖WithLp.toLp 1 ((xn n).ofLp ᵥ* P - (xn n).ofLp)‖₁ ≤ 2 / (n + 1) := by
      intro n
      unfold xn
      exact cesaro_average_almost_invariant x₀ P n
    have hb : Tendsto (fun n => ‖WithLp.toLp 1 ((xn (nk n)).ofLp ᵥ* P - (xn (nk n)).ofLp)‖₁)
      atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      case g => exact fun _ => 0
      case hg => exact tendsto_const_nhds
      case hgf => intro n; positivity
      case h => exact fun n => 2 / (nk n + 1)
      case hfh => exact fun n => halmostinv (nk n)
      case hh =>
        apply Metric.tendsto_atTop'.mpr
        intro ε hε
        obtain ⟨N, hN⟩ :=
          (hn_increasing.tendsto_atTop.eventually_ge_atTop
          (Nat.ceil (2 / ε))).exists
        refine ⟨N, ?_⟩
        intro n hnge
        have hnkn : 0 < (nk n + 1 : ℝ) := by
          have : (0 : ℝ) ≤ nk n := Nat.cast_nonneg _
          linarith
        have hpos : (0 : ℝ) < 2 / (nk n + 1) := div_pos two_pos hnkn
        show dist (2 / ((nk n : ℝ) + 1)) 0 < ε
        rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
        have := hn_increasing hnge
        have hNle : (nk N : ℝ) < nk n := by exact_mod_cast this
        have : 2 / ε ≤ nk n := by
          have := Nat.ceil_le.mp hN
          linarith
        exact (div_lt_comm₀ (a := 2) (hb := hnkn) hε.lt).mpr (by linarith)
    let f := fun v : l1Space S => WithLp.toLp 1 (v.ofLp ᵥ* P)
    have hfcont : Continuous f := by
      apply Continuous.comp (g := WithLp.toLp 1)
      · exact PiLp.continuous_toLp 1 _
      · apply Continuous.matrix_vecMul
        · exact PiLp.continuous_ofLp 1 _
        · exact continuous_const
    have hc : Tendsto (fun n => f (xn (nk n)) - xn (nk n))
      atTop (𝓝 (f μ - μ)) := by
      apply Filter.Tendsto.sub
      · exact (hfcont.tendsto μ).comp hn_lim
      · exact hn_lim
    have hd : Tendsto (fun n => ‖f (xn (nk n)) - xn (nk n)‖) atTop (𝓝 0) := by
      have hcoe : ∀ n, ‖f (xn (nk n)) - xn (nk n)‖ =
          (‖WithLp.toLp 1 ((xn (nk n)).ofLp ᵥ* P - (xn (nk n)).ofLp)‖₁ : ℝ) := fun n => by
        simp only [f]
        rfl
      simp_rw [hcoe]
      exact NNReal.tendsto_coe.mpr hb
    have he : ‖f μ - μ‖ = 0 := by
      have := tendsto_nhds_unique (continuous_norm.tendsto _|>.comp hc) hd
      exact this
    have : f μ = μ := by rwa [norm_eq_zero, sub_eq_zero] at he
    simp only [f] at this
    have := (WithLp.toLp_injective 1).eq_iff.mp this
    exact this

theorem stationary_distribution_uniquely_exists
  (P : Matrix S S ℝ) [RowStochastic P] [Aperiodic P] [Irreducible P]
  : ∃! μ : S → ℝ, StochasticVec μ ∧ Stationary μ P := by
  obtain ⟨μ, hμ, hμstationary⟩ := stationary_distribution_exists P
  refine ⟨μ, ?hμ, ?huniq⟩
  case hμ => exact ⟨hμ, hμstationary⟩
  case huniq =>
    intro ν hν
    obtain ⟨hν, hνstationary⟩ := hν
    obtain ⟨N, _, hN⟩ := smat_minorizable_with_large_pow P
    let f := smat_as_operator (P ^ N)
    obtain ⟨K, _, hf⟩ := smat_contraction_in_simplex (P ^ N)
    have : IsFixedPt f ⟨WithLp.toLp 1 μ, hμ⟩ := by
      simp only [IsFixedPt, f, smat_as_operator, Subtype.mk.injEq]
      exact (WithLp.toLp_injective 1).eq_iff.mpr (multi_step_stationary μ P N).stationary
    have hμfixed := fixedPoint_unique hf this
    have : IsFixedPt f ⟨WithLp.toLp 1 ν, hν⟩ := by
      simp only [IsFixedPt, f, smat_as_operator, Subtype.mk.injEq]
      exact (WithLp.toLp_injective 1).eq_iff.mpr (multi_step_stationary ν P N).stationary
    have hνfixed := fixedPoint_unique hf this
    have := hνfixed.trans hμfixed.symm
    simp only [Subtype.mk.injEq] at this
    exact (WithLp.toLp_injective 1).eq_iff.mp this

class GeometricMixing
  (P : Matrix S S ℝ) [RowStochastic P]
  : Prop where
  mixing : ∃ (C : ℝ) (ρ : ℝ) (μ : S → ℝ),
    0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ StochasticVec μ ∧ Stationary μ P ∧
    ∀ (x : S → ℝ) [StochasticVec x] (n : ℕ),
      ‖WithLp.toLp 1 (x ᵥ* (P ^ n) - μ)‖₁ ≤ C * ρ ^ n

instance (P : Matrix S S ℝ) [RowStochastic P] [Aperiodic P] [Irreducible P]
  : GeometricMixing P := by
  obtain ⟨μ, hμ, hμstationary⟩ := stationary_distribution_exists P
  obtain ⟨N, hNge1, hN⟩ := smat_minorizable_with_large_pow P
  have hNpos : 0 < N := by linarith
  let f := smat_as_operator (P ^ N)
  obtain ⟨K, hKpos, hf⟩ := smat_contraction_in_simplex (P ^ N)
  have : IsFixedPt f ⟨WithLp.toLp 1 μ, hμ⟩ := by
    simp only [IsFixedPt, f, smat_as_operator, Subtype.mk.injEq]
    exact (WithLp.toLp_injective 1).eq_iff.mpr (multi_step_stationary μ P N).stationary
  have hμfixed := fixedPoint_unique hf this

  have hKle1 := NNReal.coe_le_coe.mpr hf.1.le
  conv_rhs at hKle1 => simp

  constructor
  refine ⟨?C, ?ρ, ?μ, ?hCpos, ?hρpos, ?hρlt1, ?hμ, ?hμstationary, ?hmixing⟩
  case C => exact 2 / K / (1 - K)
  case ρ => exact K ^ (1 / (N : ℝ))
  case μ => exact μ
  case hCpos =>
    have h₁ : 0 < 1 - (K : ℝ) := by simp [hf.1]
    have h₂ : 0 < 2 / (K : ℝ) := by simp [hKpos]
    apply @_root_.mul_pos
    exact h₂
    simp [h₁]
  case hρpos => apply Real.rpow_pos_of_pos hKpos
  case hρlt1 =>
    have : (K : ℝ) < 1 := by simp [hf.1]
    apply Real.rpow_lt_one
    simp
    simp [hf.1]
    simp [hNpos]
  case hμ => exact hμ
  case hμstationary => exact hμstationary
  case hmixing =>
    intro x₀ hx₀ n
    have hrate := apriori_dist_iterate_fixedPoint_le hf
      ⟨WithLp.toLp 1 x₀, hx₀⟩ (n / N)
    rw [←hμfixed] at hrate
    simp only [smat_as_operator] at hrate
    rw [smat_as_operator_iter (P ^ N) (n / N)] at hrate

    calc
        toReal ‖WithLp.toLp 1 (x₀ ᵥ* P ^ n - μ)‖₁
      _ ≤ toReal ‖WithLp.toLp 1 (x₀ ᵥ* (P ^ N) ^ (n / N) - μ)‖₁ := by
        have hPn : P ^ n = (P ^ N) ^ (n / N) * P ^ (n % N) := by
          conv_lhs => rw [←Nat.div_add_mod n N, pow_add, pow_mul]
        conv_lhs =>
          rw [hPn, ←vecMul_vecMul]
          rw [←(multi_step_stationary μ P (n % N)).stationary]
        exact smat_nonexpansive_in_l1 (P ^ (n % N)) (x₀ ᵥ* (P ^ N) ^ (n / N)) μ
      _ ≤ toReal ‖WithLp.toLp 1 (x₀ - x₀ ᵥ* P ^ N)‖₁ * K ^ (n / N) / (1 - K) := by
        exact hrate
      _ ≤ 2 * K ^ (n / N) / (1 - K) := by
        have : ‖WithLp.toLp 1 (x₀ - x₀ ᵥ* P ^ N)‖₁ ≤ 2 := by calc
            ‖WithLp.toLp 1 (x₀ - x₀ ᵥ* P ^ N)‖₁
          _ = ‖WithLp.toLp 1 x₀ - WithLp.toLp 1 (x₀ ᵥ* P ^ N)‖₁ := by
            rw [← WithLp.toLp_sub]
          _ ≤ ‖WithLp.toLp 1 x₀‖₁ + ‖WithLp.toLp 1 (x₀ ᵥ* P ^ N)‖₁ := by
            exact norm_sub_le _ _
          _ = 1 + 1 := by
            have h1 := l1_norm_eq_one (WithLp.toLp 1 x₀)
            have h2 := l1_norm_eq_one (WithLp.toLp 1 (x₀ ᵥ* P ^ N))
            simp only [h1, h2]
          _ = 2 := by ring
        gcongr
        case hc => linarith
        case hab.hbc => exact_mod_cast this
      _ ≤ 2 * K ^ (((n : ℝ) / N) - 1) / (1 - K) := by
        set z : ℕ := n / N
        set z' : ℝ := (n : ℝ) / N
        have : z ≥ z' - 1 := by
          have : n < (z + 1) * N := by calc
              n
            _ = z * N + n % N := (Nat.div_add_mod' n N).symm
            _ < z * N + N := by
              have := Nat.mod_lt n hNpos.gt
              linarith
            _ = (z + 1) * N := by
              simp [Nat.succ_mul, Nat.add_comm]
          have : (n : ℝ) ≤ (z + 1) * (N : ℝ) := by
            exact_mod_cast (Nat.le_of_lt this)
          rw [mul_comm] at this
          have := (div_le_iff₀' (c := (N : ℝ)) (a := (z + 1 : ℝ)) (b := (n : ℝ)) (by exact_mod_cast hNpos)).mpr this
          linarith
        have : (K : ℝ) ^ z ≤ (K : ℝ) ^ (z' - 1) := by
          have := Real.rpow_le_rpow_of_exponent_le_or_ge
            (x := (K : ℝ)) (y := (z : ℝ)) (z := z' - 1) (h := by
            apply Or.inr; refine ⟨hKpos, hKle1, this.le⟩)
          exact_mod_cast this
        gcongr
        case hc => linarith
      _ = (2 / K / (1 - K)) * (K ^ (1 / (N : ℝ))) ^ n := by
        have := Real.rpow_sub hKpos ((n : ℝ) / N) 1
        simp at this
        rw [this, mul_div_assoc', mul_div_right_comm]
        rw [mul_div_right_comm]
        simp
        apply Or.inl
        rw [div_eq_mul_one_div, mul_comm]
        simp
        rw [Real.rpow_mul (hx := by simp)]
        simp

end stationary_distribution

end StochasticMatrix
