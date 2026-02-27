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

namespace MeasureTheory
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

namespace Filtration

def subsequence (ℱ : Filtration ℕ m₀) {t : ℕ → ℕ} (ht : ∀ n, t n < t (n + 1)) :
  Filtration ℕ m₀ := by
  constructor
  case seq => exact fun n => ℱ (t n)
  case le' =>
    intro i
    exact ℱ.le (t i)
  case mono' =>
    intro i j hij
    apply ℱ.mono
    refine Nat.le_induction ?base ?succ j hij
    rfl
    intro k hk ih
    have := ht k
    omega

def piLE' {X : ℕ → Type*}
  [(i : ℕ) → MeasurableSpace (X i)]
  : @Filtration (Π i, X i) ℕ _ MeasurableSpace.pi := by
  constructor
  case seq => exact fun n => if n = 0 then ⊥ else piLE (n - 1)
  case mono' =>
    intro i j hij
    simp
    by_cases hi : i = 0
    case pos =>
      simp [hi]
    case neg =>
      simp [hi]
      have : 1 ≤ i := by
        apply Nat.succ_le_of_lt
        rw [Nat.pos_iff_ne_zero]
        exact hi
      have : j ≠ 0 := by linarith
      simp [this]
      apply piLE.mono'
      apply Nat.pred_le_pred
      simp [hij]
  case le' =>
    intro n
    by_cases hn : n = 0
    case pos =>
      simp [hn]
    case neg =>
      simp [hn]
      apply piLE.le

end Filtration

end MeasureTheory

lemma fun_sum {α β γ : Type*} [AddCommMonoid β] [AddCommMonoid γ]
  (f : α → β → γ) (s : Finset β) :
  (fun a => (∑ b ∈ s, f a b)) = ∑ b ∈ s, fun a => f a b := by
  funext a
  simp

namespace StochasticApproximation

universe u
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable {d : ℕ}

structure Skeleton where
  F : E d → (S × S) → E d
  hFm : Measurable F.uncurry
  hFlip : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖
  f : E d → E d
  α : ℕ → ℝ
  anc : Anchors (α := α)
  hanc : SufficientlySparse anc
  x : ℕ → (ℕ → (S × S)) → E d
  x₀ : E d
  hx : IteratesOfResidual x x₀ α F
  mrp : FiniteMRP (S := S)
  hfF : ∀ x, f x = ∑ s, ∑ s', (mrp.μ s * mrp.P s s') • F x (s, s')

variable {sk : Skeleton (S := S) (d := d)}

noncomputable def Skeleton.G := fun x y => sk.F x y - x

lemma Skeleton.measurable_of_G_uncurry : Measurable sk.G.uncurry := by
  apply Measurable.sub
  apply sk.hFm
  apply measurable_fst

lemma Skeleton.lipschitz_of_G :
  ∃ C, 0 ≤ C ∧ ∀ x x' y, ‖sk.G x y - sk.G x' y‖ ≤ C * ‖x - x'‖ := by
  obtain ⟨C, hCnonneg, hC⟩ := sk.hFlip
  refine ⟨C + 1, by positivity, ?hC⟩
  case hC =>
    intro x x' y
    simp [G]
    rw [sub_sub_sub_comm]
    grw [norm_sub_le, hC]
    ring_nf
    simp

def Skeleton.growth_of_G :=
  linear_growth_of_lipschitz' sk.lipschitz_of_G

lemma Skeleton.measurable_of_x :
  ∀ n, Measurable[piLE (sk.anc.t n)] fun x ↦ sk.x (sk.anc.t n) x := by
  intro n
  obtain ⟨xn, hxnm, hxneq⟩ := sk.hx.adaptedOnSamplePath.property (sk.anc.t n)
  apply Measurable.congr (funext_iff.mpr hxneq).symm
  apply hxnm.comp
  apply measurable_frestrictLe_piLE

lemma Skeleton.measurable_of_G {f : (ℕ → S × S) → S × S} {n : ℕ}
  (hf : Measurable[piLE (sk.anc.t (n + 1))] f) :
  ∀ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)),
  Measurable[piLE (sk.anc.t (n + 1))] (fun ω => sk.G (sk.x i ω) (f ω))
  := by
  intro i hi
  simp at hi
  obtain ⟨xn, hxnm, hxneq⟩ := sk.hx.adaptedOnSamplePath.property i
  have hxm : Measurable[piLE (sk.anc.t (n + 1))] (sk.x i) := by
    rw [funext_iff.mpr hxneq]
    apply hxnm.comp
    apply Measurable.mono
    apply measurable_frestrictLe_piLE
    apply piLE.mono
    linarith
    rfl
  apply Measurable.sub
  let F₁ := fun ω => (sk.x i ω, f ω)
  apply Measurable.congr (f := sk.F.uncurry ∘ F₁)
  rfl
  apply sk.hFm.comp
  simp [F₁]
  apply Measurable.prod
  simp
  apply hxm.comp
  apply measurable_id
  simp
  exact hf
  exact hxm

lemma Skeleton.measurable_of_G₁ :
  ∀ n, ∀ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ∀ y,
  Measurable[piLE (sk.anc.t (n + 1))] (fun ω => sk.G (sk.x i ω) y)
  := by
  intro n i hi y
  apply sk.measurable_of_G
  apply measurable_const
  exact hi

lemma Skeleton.measurable_of_G₂ :
  ∀ n, ∀ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ∀ j ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)),
  Measurable[piLE (sk.anc.t (n + 1))] (fun ω => sk.G (sk.x i ω) (ω (j + 1)))
  := by
  intro n i hi j hj
  apply sk.measurable_of_G
  apply Measurable.mono
  apply measurable_pi_apply_piLE
  apply piLE.mono
  have := mem_Ico.mp hj; omega
  rfl
  exact hi

lemma Skeleton.bdd_of_G :
  ∀ n, ∃ C, 0 ≤ C ∧ ∀ ω i, ‖sk.G (sk.x (sk.anc.t n) ω) (ω (i + 1))‖ ≤ C := by
  intro n
  obtain ⟨C₁, _, hC₁⟩ := sk.growth_of_G
  obtain ⟨C₂, _, hC₂⟩ := sk.hx.bdd sk.hFlip (sk.anc.t n)
  use C₁ * (C₂ + 1)
  constructor
  positivity
  intro ω i
  grw [hC₁, hC₂]

lemma Skeleton.integrable_of_G (μ : Measure (ℕ → S × S)) [IsFiniteMeasure μ] :
  ∀ n, ∀ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)),
  Integrable (fun ω => sk.G (sk.x (sk.anc.t n) ω) (ω (i + 1))) μ := by
  intro n i hi
  apply integrable_of_norm_le
  apply Measurable.aestronglyMeasurable
  apply Measurable.mono
  apply sk.measurable_of_G₂ n (sk.anc.t n) ?_ i hi
  simp; apply sk.anc.t_mono
  apply piLE.le
  rfl
  obtain ⟨C, _, hC⟩ := sk.bdd_of_G n
  use C
  apply Eventually.of_forall
  intro ω
  exact hC ω i

lemma Skeleton.bdd_of_condExp_G :
  ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂sk.mrp.markov_samples,
    ∀ n, ∀ i : Ico (sk.anc.t n) (sk.anc.t (n + 1)), ‖sk.mrp.markov_samples[fun ω =>
    sk.G (sk.x (sk.anc.t n) ω) (ω (i + 1))|piLE (sk.anc.t n)] ω‖ ≤
    C * (‖sk.x (sk.anc.t n) ω‖ + 1) := by
  have : IsProbabilityMeasure sk.mrp.markov_samples := by
    simp [FiniteMRP.markov_samples]
    infer_instance
  obtain_bound sk.growth_of_G as C₁, hC₁nonneg, hC₁
  apply ae_all_iff.mpr
  intro n
  obtain ⟨C₂, _, hC₂⟩ := sk.bdd_of_G n
  have hm : Measurable[piLE (sk.anc.t n)] fun ω ↦ C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1) := by
    apply Measurable.const_mul
    apply Measurable.add_const
    have := (sk.measurable_of_x n)
    have := measurable_norm.comp this
    exact this
  have hi : Integrable (fun ω ↦ C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1))
    sk.mrp.markov_samples := by
    apply integrable_of_norm_le
    apply Measurable.aestronglyMeasurable
    apply Measurable.mono
    exact hm
    apply piLE.le
    rfl
    obtain ⟨C₃, _, hC₃⟩ := sk.hx.bdd sk.hFlip (sk.anc.t n)
    use C₁ * (C₃ + 1)
    apply Eventually.of_forall
    intro ω
    simp
    repeat rw [abs_of_nonneg]
    grw [hC₃]
    positivity
    positivity

  apply ae_all_iff.mpr
  intro i
  apply EventuallyLE.trans
  apply norm_condExp_le_condExp_norm
  apply sk.integrable_of_G
  exact i.prop
  apply Measurable.mono
  apply sk.measurable_of_G₂ n (sk.anc.t n) ?_ i i.prop
  simp; apply sk.anc.t_mono
  apply piLE.le
  rfl
  use C₂
  intro ω; exact hC₂ ω i
  apply piLE.le
  apply EventuallyLE.trans
  apply condExp_mono (g := fun ω => C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1))
  apply Integrable.norm
  apply sk.integrable_of_G
  exact i.prop
  exact hi
  apply Eventually.of_forall
  intro ω; simp; apply hC₁
  obtain ⟨xn, hxnm, hxneq⟩ := sk.hx.adaptedOnSamplePath.property (sk.anc.t n)
  apply Eventually.of_forall
  intro ω
  apply le_of_eq
  apply funext_iff.mp
  apply condExp_of_stronglyMeasurable
  apply hm.stronglyMeasurable
  exact hi

lemma Skeleton.bdd_of_condExp_G' :
  ∀ n, ∀ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ∃ C, 0 ≤ C ∧
    ∀ᵐ ω ∂sk.mrp.markov_samples, ‖sk.mrp.markov_samples[fun ω =>
    sk.G (sk.x (sk.anc.t n) ω) (ω (i + 1))|piLE (sk.anc.t n)] ω‖ ≤ C := by
  obtain ⟨C₁, hC₁nonneg, hC₁⟩ := sk.bdd_of_condExp_G
  intro n i hi
  obtain ⟨C₂, hC₂nonneg, hC₂⟩ := sk.hx.bdd sk.hFlip (sk.anc.t n)
  use C₁ * (C₂ + 1)
  constructor
  positivity
  apply Eventually.mono hC₁
  intro ω hω
  grw [hω n ⟨i, by simp [hi]⟩]
  grw [hC₂]

lemma Skeleton.integrable_of_condExp_G :
  ∀ n, ∀ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)),
  Integrable sk.mrp.markov_samples[
    fun ω' ↦ sk.G (sk.x (sk.anc.t n) ω') (ω' (i + 1))|piLE (sk.anc.t n)]
  sk.mrp.markov_samples := by
  have : IsProbabilityMeasure sk.mrp.markov_samples := by
    simp [FiniteMRP.markov_samples]
    infer_instance
  intro n i hi
  apply integrable_of_norm_le
  apply StronglyMeasurable.aestronglyMeasurable
  apply StronglyMeasurable.mono
  apply stronglyMeasurable_condExp
  apply piLE.le
  obtain ⟨C, _, hC⟩ := sk.bdd_of_condExp_G' n i hi
  use C

noncomputable def Skeleton.g := sk.f - id

lemma Skeleton.g_eq_expectation_G :
  ∀ x, sk.g x = ∑ s, ∑ s', (sk.mrp.μ s * sk.mrp.P s s') • sk.G x (s, s') := by
  have hP : RowStochastic sk.mrp.P := by infer_instance
  have hμ : StochasticVec sk.mrp.μ := by infer_instance
  intro x
  simp [g, G, sk.hfF]
  simp_rw [smul_sub, sum_sub_distrib]
  simp
  simp_rw [←sum_smul, ←mul_sum, (hP.stochastic ?_).rowsum]
  simp [hμ.rowsum]

noncomputable def Skeleton.e₁ :
  ℕ → (ℕ → (S × S)) → E d := fun n ω =>
  ∑ i ∈ Finset.Ico (sk.anc.t (n - 1)) (sk.anc.t n),
    sk.α i • (sk.G (sk.x (sk.anc.t (n - 1)) ω) (ω (i + 1)) -
    (sk.mrp.markov_samples[
      fun ω' => sk.G (sk.x (sk.anc.t (n - 1)) ω') (ω' (i + 1)) | piLE (sk.anc.t (n - 1))] ω))

noncomputable def Skeleton.e₂₁ :
  ℕ → (ℕ → (S × S)) → E d := fun n ω =>
  ∑ i ∈ Finset.Ico (sk.anc.t (n - 1)) (sk.anc.t n),
    sk.α i • (sk.G (sk.x i ω) (ω (i + 1)) - sk.G (sk.x (sk.anc.t (n - 1)) ω) (ω (i + 1)))

noncomputable def Skeleton.e₂₂ :
  ℕ → (ℕ → (S × S)) → E d := fun n ω =>
  ∑ i ∈ Finset.Ico (sk.anc.t (n - 1)) (sk.anc.t n),
    sk.α i • (sk.mrp.markov_samples[
      fun ω' => sk.G (sk.x (sk.anc.t (n - 1)) ω') (ω' (i + 1)) | piLE (sk.anc.t (n - 1))] ω
      - sk.g (sk.x (sk.anc.t (n - 1)) ω))

noncomputable def Skeleton.e₂ : ℕ → (ℕ → (S × S)) → E d :=
  fun n ω => sk.e₂₁ n ω + sk.e₂₂ n ω

lemma Skeleton.isIterates (hx : IteratesOfResidual sk.x sk.x₀ sk.α sk.F) :
  Iterates (sk.x ∘ sk.anc.t) sk.x₀ sk.f sk.e₁ sk.e₂ sk.anc.β := by
  constructor
  simp [hx.init, sk.anc.t_init]
  intro n ω
  simp
  have := sum_cancel_consecutive (f := sk.x) (sk.anc.t_mono n).le
  have := add_eq_of_eq_sub this
  rw [←this]
  conv_rhs => rw [add_assoc, add_assoc, add_comm]
  simp
  conv_rhs =>
    congr; rfl
    simp [e₂, ←add_assoc]
    simp [e₁, e₂₁, e₂₂, ←sum_add_distrib, ←smul_add]
  simp [Anchors.β, sum_smul, ←sum_add_distrib, ←smul_add, g]
  simp [←sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  simp [hx.step, G]

lemma Skeleton.bdd_of_e₂₁ :
  ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂ sk.mrp.markov_samples, ∀ n,
    ‖sk.e₂₁ (n + 1) ω‖ ≤ C * (sk.anc.β n) ^ 2 * (‖sk.x (sk.anc.t n) ω‖ + 1) := by
  obtain ⟨C₁, hC₁nonneg, hC₁⟩ := sk.anc.robbinsMonro_of_β.bdd
  have : ∀ n, 0 ≤ sk.α n := by intro n; exact (sk.anc.hα.pos n).le
  obtain ⟨C₂, hC₂nonneg, hC₂⟩ := sk.hx.growth this sk.hFlip
  obtain ⟨C₃, hC₃nonneg, hC₃⟩ := sk.lipschitz_of_G
  refine ⟨?C, ?hCnonneg, ?hC⟩
  case C => exact C₃ * C₂ * rexp (C₁ * C₂)
  case hCnonneg => positivity
  case hC =>
    apply ae_all_iff.mpr
    intro n
    apply Eventually.of_forall
    intro ω
    simp [e₂₁]
    grw [norm_sum_le]
    simp_rw [norm_smul]
    simp
    apply LE.le.trans; grw [sum_le_sum]; intro i hi
    apply LE.le.trans; grw [hC₃, hC₂ (n := sk.anc.t n) (m := sk.anc.t (n + 1)) ω]
    exact hi
    rw [abs_of_nonneg (by exact (sk.anc.hα.pos i).le)]
    simp_rw [←sum_mul, ←sk.anc.β_def]
    nth_grw 3 [hC₁]
    apply le_of_eq
    ring_nf
    apply le_of_lt ( sk.anc.robbinsMonro_of_β.pos n)
    have :=  sk.anc.robbinsMonro_of_β.pos n
    positivity

lemma Skeleton.bdd_of_e₂₂ :
  ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂ sk.mrp.markov_samples, ∀ n,
    ‖sk.e₂₂ (n + 1) ω‖ ≤ C * (sk.anc.β n) ^ 2 * (‖sk.x (sk.anc.t n) ω‖ + 1) := by
  have hP : RowStochastic sk.mrp.P := by infer_instance
  set μ := sk.mrp.markov_samples
  obtain ⟨C₁, hC₁nonneg, hC₁⟩ := sk.growth_of_G
  obtain ⟨ρ, C₂, _, _, _, hC₂⟩ := sk.mrp.mixing
  obtain ⟨C₃, hC₃nonneg, hC₃⟩ := sk.hanc
  refine ⟨?C, ?hCnonneg, ?hC⟩
  case C => exact C₃ * C₂ * 1 / (1 - ρ) * C₁
  case hCnonneg =>
    have : 1 - ρ > 0 := by linarith
    positivity
  case hC =>
    apply ae_all_iff.mpr
    intro n
    obtain ⟨C₄, hC₄nonneg, hC₄⟩ := sk.hx.bdd sk.hFlip (sk.anc.t n)
    obtain ⟨xn, hxnm, hxneq⟩ := sk.hx.adaptedOnSamplePath.property (sk.anc.t n)
    let G' : (i : ℕ) → (hi : sk.anc.t n ≤ i + 1) → (ℕ → (S × S)) → E d :=
      fun i hi => iterates_update hi sk.G.uncurry xn
    have hG' : ∀ i : Ico (sk.anc.t n) (sk.anc.t (n + 1)),
      G' i (Nat.le_succ_of_le (mem_Ico.mp i.prop).1) =
        fun ω => sk.G (sk.x (sk.anc.t n) ω) (ω (i + 1)) := by
      intro i
      ext1 ω
      simp [G', iterates_update]
      apply congr
      apply congr rfl
      rw [hxneq ω]
      apply congr rfl
      rfl
      rfl
    have : ∀ i : Ico (sk.anc.t n) (sk.anc.t (n + 1)),
      μ[fun ω => sk.G (sk.x (sk.anc.t n) ω) (ω (i + 1)) | piLE (sk.anc.t n)] =ᵐ[μ]
      fun ω => ∑ y, ((sk.mrp.P ^ (i - sk.anc.t n)) (ω (sk.anc.t n)).2 y.1 *
        sk.mrp.P y.1 y.2) • sk.G (xn (frestrictLe (sk.anc.t n) ω)) y
      := by
      intro i
      have hi := mem_Ico.mp i.prop
      apply EventuallyEq.trans
      apply condExp_congr_ae (g := G' i (Nat.le_succ_of_le hi.1))
      apply Eventually.of_forall
      intro ω
      simp [hG']
      apply EventuallyEq.trans; apply condExp_iterates_update
      exact sk.measurable_of_G_uncurry
      case hbdd =>
        use C₁ * (C₄ + 1)
        intro ω y
        simp [←hxneq]
        grw [hC₁, hC₄]
      exact hxnm
      case hInt =>
        intro x₀
        have := hG' i
        simp [G'] at this
        rw [this]
        apply sk.integrable_of_G
        simp
      simp_rw [Finite.integral_fintype_kernel_iter]
      apply Eventually.of_forall
      intro ω
      have : 1 ≤ i + 1 - sk.anc.t n := by omega
      simp_rw [FiniteMRP.aug_chain_markov_kmat_pow this]
      apply sum_congr rfl
      intro y hy
      have : i + 1 - sk.anc.t n - 1 = i - sk.anc.t n := by omega
      simp [this]
    apply Eventually.mono (ae_all_iff.mpr this)
    intro ω hω
    simp [←hxneq] at hω
    simp [e₂₂]
    grw [norm_sum_le]
    simp_rw [norm_smul]
    apply Eq.trans_le
    apply sum_congr rfl
    intro i hi
    simp at hi
    rw [hω i hi.1 hi.2]
    simp_rw [sk.g_eq_expectation_G, Fintype.sum_prod_type, ←sum_sub_distrib,
      ←sub_smul]
    -- Sum over s' gives ∑ |P s s'| = 1 (for stochastic matrix)
    have hPstoch : ∀ s : S, ∑ s' : S, |sk.mrp.P s s'| = 1 := fun s => by
      simp_rw [abs_of_nonneg ((hP.stochastic s).nonneg _)]
      exact (hP.stochastic s).rowsum

    -- Helper lemma for bounding the inner norm
    have hInnerBound : ∀ k ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)),
        ‖∑ s, ∑ s', ((sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s * sk.mrp.P s s' -
           sk.mrp.μ s * sk.mrp.P s s') • sk.G (sk.x (sk.anc.t n) ω) (s, s')‖
        ≤ C₂ * ρ ^ (k - sk.anc.t n) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by
      intro k hk
      calc ‖∑ s, ∑ s', ((sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s * sk.mrp.P s s' -
               sk.mrp.μ s * sk.mrp.P s s') • sk.G (sk.x (sk.anc.t n) ω) (s, s')‖
         ≤ ∑ s, ‖∑ s', ((sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s * sk.mrp.P s s' -
               sk.mrp.μ s * sk.mrp.P s s') • sk.G (sk.x (sk.anc.t n) ω) (s, s')‖ :=
           norm_sum_le _ _
       _ ≤ ∑ s, ∑ s', ‖((sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s * sk.mrp.P s s' -
               sk.mrp.μ s * sk.mrp.P s s') • sk.G (sk.x (sk.anc.t n) ω) (s, s')‖ := by
           gcongr with s _; exact norm_sum_le _ _
       _ = ∑ s, ∑ s', |(sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s - sk.mrp.μ s| *
               |sk.mrp.P s s'| * ‖sk.G (sk.x (sk.anc.t n) ω) (s, s')‖ := by
           congr 1; ext s; congr 1; ext s'
           rw [norm_smul, Real.norm_eq_abs, ←sub_mul, abs_mul]
       _ ≤ ∑ s, ∑ s', |(sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s - sk.mrp.μ s| *
               |sk.mrp.P s s'| * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by
           gcongr with s _ s' _; exact hC₁ _ _
       _ = ∑ s, |(sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s - sk.mrp.μ s| *
               (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by
           congr 1; ext s
           -- ∑ s', |a| * |P s s'| * C = |a| * (∑ s', |P s s'|) * C = |a| * 1 * C = |a| * C
           -- The constant a = |P^k s - μ s| doesn't depend on s', factor it out
           set ha := |(sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s - sk.mrp.μ s| with ha_def
           set hC := C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1) with hC_def
           calc ∑ s', ha * |sk.mrp.P s s'| * hC
             = (∑ s', ha * |sk.mrp.P s s'|) * hC := (Finset.sum_mul ..).symm
           _ = ha * (∑ s', |sk.mrp.P s s'|) * hC := by
               congr 1; rw [← Finset.mul_sum]
           _ = ha * 1 * hC := by rw [hPstoch s]
           _ = ha * hC := by ring
       _ = (∑ s, |(sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s - sk.mrp.μ s|) *
               (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by rw [sum_mul]
       _ ≤ C₂ * ρ ^ (k - sk.anc.t n) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by
           have := hC₂ (ω (sk.anc.t n)).2 (k - sk.anc.t n)
           calc (∑ s, |(sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s - sk.mrp.μ s|) *
                   (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1))
             ≤ (C₂ * ρ ^ (k - sk.anc.t n)) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by gcongr
           _ = C₂ * ρ ^ (k - sk.anc.t n) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by ring

    -- Bound each term in the outer sum using hInnerBound
    have hBound : ∀ k ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)),
        ‖sk.α k‖ * ‖∑ s, ∑ s', ((sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s * sk.mrp.P s s' -
           sk.mrp.μ s * sk.mrp.P s s') • sk.G (sk.x (sk.anc.t n) ω) (s, s')‖
        ≤ ‖sk.α k‖ * C₂ * ρ ^ (k - sk.anc.t n) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by
      intro k hk
      have hIB := hInnerBound k hk
      have hαnorm : 0 ≤ ‖sk.α k‖ := norm_nonneg _
      calc ‖sk.α k‖ * ‖∑ s, ∑ s', ((sk.mrp.P ^ (k - sk.anc.t n)) (ω (sk.anc.t n)).2 s *
               sk.mrp.P s s' - sk.mrp.μ s * sk.mrp.P s s') • sk.G (sk.x (sk.anc.t n) ω) (s, s')‖
         ≤ ‖sk.α k‖ * (C₂ * ρ ^ (k - sk.anc.t n) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1))) :=
           mul_le_mul_of_nonneg_left hIB hαnorm
       _ = ‖sk.α k‖ * C₂ * ρ ^ (k - sk.anc.t n) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by
           ring

    -- Apply the bound to the sum
    apply LE.le.trans (sum_le_sum hBound)
    -- Now goal is: ∑ k ∈ Ico, ‖α k‖ * C₂ * ρ^(k-tn) * (C₁ * (‖x‖+1)) ≤ C₃ * C₂ / (1-ρ) * C₁ * β² * (‖x‖+1)
    -- First convert ‖α k‖ = α k using positivity, then bound α k ≤ α tn ≤ C₃ * β²
    have hαpos : ∀ k, ‖sk.α k‖ = sk.α k := fun k => Real.norm_of_nonneg (sk.anc.hα.pos k).le
    simp_rw [hαpos]
    -- Now bound α k ≤ α (tn) ≤ C₃ * β² for k ≥ tn
    apply LE.le.trans
    · apply sum_le_sum
      intro i hi
      simp only [Finset.mem_Ico] at hi
      have hαmono : sk.α i ≤ sk.α (sk.anc.t n) := sk.anc.hα_mono hi.1
      have hαbdd : sk.α (sk.anc.t n) ≤ C₃ * sk.anc.β n ^ 2 := hC₃ n
      have h1 : sk.α i * C₂ * ρ ^ (i - sk.anc.t n) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1))
        ≤ sk.α (sk.anc.t n) * C₂ * ρ ^ (i - sk.anc.t n) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by
          gcongr
      have h2 : sk.α (sk.anc.t n) * C₂ * ρ ^ (i - sk.anc.t n) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1))
        ≤ (C₃ * sk.anc.β n ^ 2) * C₂ * ρ ^ (i - sk.anc.t n) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by
          gcongr
      exact le_trans h1 h2
    -- Now factor out and bound the geometric sum
    simp_rw [←mul_assoc, ←sum_mul]
    rw [← Finset.mul_sum]
    -- ∑ k ∈ Ico tn t(n+1), ρ^(k-tn) ≤ ∑ k, ρ^k ≤ 1/(1-ρ) for ρ < 1
    have hρpos : 0 < ρ := by linarith
    have hρ1 : ρ < 1 := by linarith
    -- The sum ∑_{k ∈ Ico tn t(n+1)} ρ^(k-tn) = ∑_{j=0}^{t(n+1)-tn-1} ρ^j ≤ ∑_{j=0}^∞ ρ^j = 1/(1-ρ)
    have hgeom : ∑ k ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ρ ^ (k - sk.anc.t n)
        ≤ (1 - ρ)⁻¹ := by
      -- Reindex the sum: k ↦ k - tn gives j in range (t(n+1) - tn)
      have hreindex : ∑ k ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ρ ^ (k - sk.anc.t n)
          = ∑ j ∈ range (sk.anc.t (n + 1) - sk.anc.t n), ρ ^ j := by
        refine Finset.sum_bij' (fun k _ => k - sk.anc.t n) (fun j _ => j + sk.anc.t n) ?_ ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_Ico] at hk; simp only [Finset.mem_range]; omega
        · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Ico]; omega
        · intro k hk
          simp only [Finset.mem_Ico] at hk
          simp only [Nat.sub_add_cancel hk.1]
        · intro j _; simp only [Nat.add_sub_cancel]
        · intro k _; rfl
      rw [hreindex]
      -- Use geom_sum_eq for finite geometric sum: ∑_{j<m} ρ^j = (ρ^m - 1)/(ρ - 1) = (1 - ρ^m)/(1 - ρ)
      rw [geom_sum_eq (ne_of_lt hρ1)]
      -- (ρ^m - 1)/(ρ - 1) = (1 - ρ^m)/(1 - ρ) since numerator and denominator both flip sign
      have hρne1 : ρ - 1 ≠ 0 := by linarith
      have h1mρne0 : 1 - ρ ≠ 0 := by linarith
      have heq : (ρ ^ (sk.anc.t (n + 1) - sk.anc.t n) - 1) / (ρ - 1)
          = (1 - ρ ^ (sk.anc.t (n + 1) - sk.anc.t n)) / (1 - ρ) := by
        rw [div_eq_div_iff hρne1 h1mρne0]
        ring
      rw [heq, inv_eq_one_div, div_le_div_iff_of_pos_right (by linarith : 0 < 1 - ρ)]
      simp only [sub_le_self_iff]
      exact pow_nonneg hρpos.le _
    -- Final bound: use hgeom to replace ∑ ρ^k by (1-ρ)⁻¹
    have hbound : C₃ * sk.anc.β n ^ 2 * C₂ *
        (∑ k ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ρ ^ (k - sk.anc.t n)) *
        C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)
        ≤ C₃ * sk.anc.β n ^ 2 * C₂ * (1 - ρ)⁻¹ * C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1) := by
      have h1 : 0 ≤ C₃ * sk.anc.β n ^ 2 * C₂ := by positivity
      have h2 : 0 ≤ C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1) := by positivity
      have h3 : 0 ≤ (1 - ρ)⁻¹ := by apply le_of_lt; apply inv_pos_of_pos; linarith
      calc C₃ * sk.anc.β n ^ 2 * C₂ *
          (∑ k ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ρ ^ (k - sk.anc.t n)) *
          C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)
        = C₃ * sk.anc.β n ^ 2 * C₂ *
          (∑ k ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ρ ^ (k - sk.anc.t n)) *
          (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by ring
      _ ≤ C₃ * sk.anc.β n ^ 2 * C₂ * (1 - ρ)⁻¹ * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by
          apply mul_le_mul_of_nonneg_right _ h2
          apply mul_le_mul_of_nonneg_left hgeom h1
      _ = C₃ * sk.anc.β n ^ 2 * C₂ * (1 - ρ)⁻¹ * C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1) := by ring
    exact calc C₃ * sk.anc.β n ^ 2 * C₂ * (∑ k ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ρ ^ (k - sk.anc.t n)) *
            C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)
      ≤ C₃ * sk.anc.β n ^ 2 * C₂ * (1 - ρ)⁻¹ * C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1) := hbound
    _ = C₃ * C₂ / (1 - ρ) * C₁ * sk.anc.β n ^ 2 * (‖sk.x (sk.anc.t n) ω‖ + 1) := by
        rw [inv_eq_one_div]; ring

theorem Skeleton.ae_tendsto
  {z : E d}
  (hz : z = sk.f z)
  {φ : E d → ℝ}
  {φ' : E d → E d}
  (hφm : Measurable φ)
  (hgradφm : Measurable φ')
  [LyapunovFunction φ φ' sk.f] :
  ∀ᵐ ω ∂ sk.mrp.markov_samples,
    Tendsto (fun n => sk.x (sk.anc.t n) ω) atTop (𝓝 z) := by

  have hP : RowStochastic sk.mrp.P := by infer_instance
  have hμ : StochasticVec sk.mrp.μ := by infer_instance

  have hAdapted := sk.hx.adaptedOnSamplePath

  have hIterates := sk.isIterates sk.hx
  have : IsProbabilityMeasure sk.mrp.markov_samples := by
    simp [FiniteMRP.markov_samples]
    infer_instance

  apply ae_tendsto_of_iterates_mds_noise
    (φ := φ) (φ' := φ') (f := sk.f) (e₁ := sk.e₁) (e₂ := sk.e₂)
    (x₀ := sk.x₀) (α := sk.anc.β) (hz := hz) (hφm := hφm) (hgradφm := hgradφm)
    (ℱ := piLE.subsequence sk.anc.t_mono) (hx := hIterates)
    (hα := sk.anc.robbinsMonro_of_β)

  case he₁ =>
    obtain ⟨C₁, hC₁nonneg, hC₁⟩ := sk.bdd_of_condExp_G
    obtain ⟨C₂, hC₂nonneg, hC₂⟩ := sk.growth_of_G
    refine ⟨?C, ?hCnonneg, ?hC⟩
    case C => exact C₁ + C₂
    case hCnonneg => positivity
    case hC =>
      apply Eventually.mono hC₁
      intro ω hC₁ n
      simp [e₁]
      grw [norm_sum_le]
      simp_rw [norm_smul]
      grw [sum_le_sum ?h]
      case h =>
        intro i hi
        grw [norm_sub_le, hC₂, hC₁ n ⟨i, by simp [hi]⟩]
      simp [←sum_mul]
      simp_rw [abs_of_nonneg (sk.anc.hα.pos ?_).le]
      apply le_of_eq
      unfold Anchors.β
      ring_nf
  case he₁Adapted =>
    intro n
    unfold e₁
    simp
    simp [subsequence, shift]
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.smul
    apply measurable_const
    apply Measurable.sub
    apply sk.measurable_of_G₂ n (sk.anc.t n) ?_  i hi
    simp; apply sk.anc.t_mono
    apply Measurable.mono
    apply StronglyMeasurable.measurable
    apply stronglyMeasurable_condExp
    apply piLE.mono
    exact (sk.anc.t_mono n).le
    rfl
  case he₁MDS =>
    intro n
    unfold e₁
    simp [subsequence]
    rw [fun_sum]
    apply EventuallyEq.trans
    apply condExp_finset_sum
    intro i hi
    set G' := fun ω => sk.G (sk.x (sk.anc.t n) ω) (ω (i + 1))
    simp_rw [smul_sub]
    apply Integrable.sub
    apply (integrable_fun_smul_iff ?_ G').mpr
    apply sk.integrable_of_G
    exact hi
    exact (sk.anc.hα.pos i).ne'
    apply (integrable_fun_smul_iff ?_ (fun ω =>
      sk.mrp.markov_samples[G'|piLE (sk.anc.t n)] ω)).mpr
    apply sk.integrable_of_condExp_G
    exact hi
    exact (sk.anc.hα.pos i).ne'
    apply EventuallyEq.trans
    apply EventuallyEq.finset_sum
    intro i hi
    simp [←Pi.smul_def]
    apply EventuallyEq.trans
    apply condExp_smul
    simp [←Pi.sub_def]
    simp [Pi.smul_def]
    apply EventuallyEq.trans
    apply (EventuallyEq.const_smul · (sk.α i))
    apply EventuallyEq.trans
    apply condExp_sub
    apply sk.integrable_of_G
    exact hi
    apply sk.integrable_of_condExp_G
    exact hi
    apply EventuallyEq.sub
    rfl
    apply condExp_condExp
    rfl
    rfl
    simp
  case he₂ =>
    obtain ⟨C₁, hC₁nonneg, hC₁⟩ := sk.bdd_of_e₂₁
    obtain ⟨C₂, hC₂nonneg, hC₂⟩ := sk.bdd_of_e₂₂
    use C₁ + C₂
    constructor
    positivity
    apply Eventually.mono (hC₁.and hC₂)
    intro ω hω n
    simp [e₂]
    grw [norm_add_le, hω.1 n, hω.2 n]
    apply le_of_eq
    ring_nf
  case he₂Adapted =>
    intro n
    unfold e₂ e₂₁ e₂₂
    simp [subsequence, shift]
    simp_rw [←sum_add_distrib, ←smul_add]
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.smul
    apply measurable_const
    apply Measurable.add
    apply Measurable.sub
    apply sk.measurable_of_G₂ n i hi
    exact hi
    apply sk.measurable_of_G₂ n (sk.anc.t n) ?_ i hi
    simp; apply sk.anc.t_mono
    apply Measurable.sub
    apply Measurable.mono
    apply StronglyMeasurable.measurable
    apply stronglyMeasurable_condExp
    apply piLE.mono
    exact (sk.anc.t_mono n).le
    rfl
    simp [sk.g_eq_expectation_G]
    measurable_finset_smul_sum
    apply sk.measurable_of_G₁
    simp; apply sk.anc.t_mono
  case hfm =>
    rw [funext_iff.mpr sk.hfF]
    measurable_finset_smul_sum
    apply Measurable.eval
    apply Measurable.of_uncurry
    exact sk.hFm
  case hfLip =>
    obtain ⟨C, hCnonneg, hC⟩ := lipschitz_of_expectation sk.hfF sk.hFlip
    use ⟨C, hCnonneg⟩
    apply lipschitzWith_iff_norm_sub_le.mpr
    exact_mod_cast hC

lemma Nat.exists_mem_Ico_of_mono
  {t : ℕ → ℕ} (htmono : ∀ n, t n < t (n + 1)) (ht0 : t 0 = 0) :
  ∀ n, ∃ m, n ∈ Ico (t m) (t (m + 1)) := by
  intro n
  set P := fun k => t k ≤ n
  set m := Nat.findGreatest P n with hmdef
  use m
  simp
  constructor
  case left =>
    change P m
    apply Nat.findGreatest_spec (m := 0)
    simp
    simp [P, ht0]
  case right =>
    by_contra h
    simp at h
    have : ∀ k, k ≤ t k := by
      intro k
      induction k with
      | zero => simp [ht0]
      | succ k ih =>
        have := htmono k
        omega
    have := (this (m + 1)).trans h
    have := Nat.le_findGreatest (P := P) this (by simp [P, h])
    rw [←hmdef] at this
    simp at this

theorem ae_tendsto_of_iterates_markov_samples
  {x : ℕ → (ℕ → (S × S)) → E d}
  {x₀ : E d}
  {α : ℕ → ℝ}
  {anc : Anchors (α := α)}
  (hanc : SufficientlySparse anc)
  {F : E d → (S × S) → E d}
  (hx : IteratesOfResidual x x₀ α F)
  (hFm : Measurable F.uncurry)
  (hFlip : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖)
  {fixed_point : E d}
  {f : E d → E d}
  (hf : fixed_point = f fixed_point)
  {mrp : FiniteMRP (S := S)}
  (hfF : ∀ w, f w = ∑ s, ∑ s', (mrp.μ s * mrp.P s s') • F w (s, s'))
  {φ : E d → ℝ}
  {φ' : E d → E d}
  (hφm : Measurable φ)
  (hgradφm : Measurable φ')
  [LyapunovFunction φ φ' f] :
  ∀ᵐ ω ∂ mrp.markov_samples,
    Tendsto (fun n => x n ω) atTop (𝓝 fixed_point) := by
  set sk : Skeleton (S := S) (d := d) := {
    F := F
    hFm := hFm
    hFlip := hFlip
    f := f
    α := α
    anc := anc
    hanc := hanc
    x := x
    x₀ := x₀
    hx := hx
    mrp := mrp
    hfF := hfF
  }
  have := sk.ae_tendsto hf hφm hgradφm
  apply Eventually.mono this
  intro ω hω
  apply tendsto_sub_nhds_zero_iff.mp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  obtain ⟨C₁, _, hC₁⟩ := sk.hx.growth (by intro n; exact (sk.anc.hα.pos n).le)
    sk.hFlip
  obtain ⟨C₂, _, hC₂⟩ := sk.anc.robbinsMonro_of_β.bdd
  set hn := fun n => Nat.exists_mem_Ico_of_mono sk.anc.t_mono sk.anc.t_init n
  set mn := fun n => (hn n).choose with hmndef
  have hmn_spec : ∀ n, n ∈ Ico (sk.anc.t (mn n)) (sk.anc.t (mn n + 1)) := by
    intro n
    rw [hmndef]
    exact (hn n).choose_spec

  have hmn_tendsto : Tendsto mn atTop atTop := by
    apply (tendsto_atTop_atTop_iff_of_monotone ?_).mpr
    intro l
    have := hmn_spec (sk.anc.t l)
    simp at this
    have : l < mn (sk.anc.t l) + 1 := by
      by_contra h
      simp at h
      have h := (anc.t_mono'.monotone h).trans_lt this.2
      simp at h
    use sk.anc.t l
    apply Nat.le_of_lt_succ this
    intro i j hij
    by_contra h
    simp at h
    have h := Nat.succ_le_of_lt h
    simp at h
    have h := sk.anc.t_mono'.monotone h
    have := sk.anc.t_mono (mn j + 1)
    have := hmn_spec j
    simp at this
    have h := this.2.trans_le h
    have := hmn_spec i
    simp at this
    have := (h.trans_le this.1).trans_le hij
    simp at this

  have hskx : sk.x = x := by rfl
  set h := fun n => sk.anc.β n * C₁ * (‖x (sk.anc.t n) ω‖ + 1) * rexp (C₂ * C₁)
    + ‖sk.x (sk.anc.t n) ω - fixed_point‖
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ => 0) (h := h ∘ mn)
  simp
  case hgf => intro n; simp
  case hfh =>
    intro n
    simp [h]
    grw [norm_sub_le_norm_sub_add_norm_sub (b := x (sk.anc.t (mn n)) ω)]
    have := hC₁ ω _ _ _ (hn n).choose_spec
    simp [hskx, mn] at this ⊢
    simp_rw [←sum_mul, ←sk.anc.β_def] at this
    grw [this]
    apply mul_le_mul_of_nonneg_left
    apply Real.exp_le_exp.mpr
    grw [hC₂]
    apply mul_nonneg
    apply mul_nonneg
    apply le_of_lt
    apply sk.anc.robbinsMonro_of_β.pos
    positivity
    positivity
  apply Tendsto.comp (hf := hmn_tendsto)
  have : 𝓝 (0 : ℝ) = 𝓝 (0 + 0) := by simp
  rw [this]
  apply Tendsto.add
  case hg =>
    apply tendsto_zero_iff_norm_tendsto_zero.mp
    apply tendsto_sub_nhds_zero_iff.mpr
    exact hω
  have := sk.anc.robbinsMonro_of_β.sqsum.tendsto_atTop_zero.sqrt.mul_const C₁
  have := (this.mul (hω.norm.add_const 1)).mul_const (rexp (C₂ * C₁))
  simp at this
  apply Tendsto.congr ?_ this
  intro n
  rw [sqrt_sq]
  ring_nf
  apply le_of_lt
  apply sk.anc.robbinsMonro_of_β.pos

theorem ae_tendsto_of_iterates_markov_samples_of_inv_poly
  {x : ℕ → (ℕ → (S × S)) → E d}
  {x₀ : E d}
  {ν : ℝ}
  (hν : ν ∈ Set.Ioo (2 / 3) 1)
  {α : ℕ → ℝ}
  (hα : α = fun n : ℕ => inv_poly ν 2 n)
  {F : E d → (S × S) → E d}
  (hx : IteratesOfResidual x x₀ α F)
  (hFm : Measurable F.uncurry)
  (hFlip : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖)
  {fixed_point : E d}
  {f : E d → E d}
  (hf : fixed_point = f fixed_point)
  {mrp : FiniteMRP (S := S)}
  (hfF : ∀ w, f w = ∑ s, ∑ s', (mrp.μ s * mrp.P s s') • F w (s, s'))
  {φ : E d → ℝ}
  {φ' : E d → E d}
  (hφm : Measurable φ)
  (hgradφm : Measurable φ')
  [LyapunovFunction φ φ' f] :
  ∀ᵐ ω ∂ mrp.markov_samples,
    Tendsto (fun n => x n ω) atTop (𝓝 fixed_point) := by
  obtain ⟨anc, hanc⟩ := anchors_of_inv_poly hν
  subst hα
  apply ae_tendsto_of_iterates_markov_samples
    hanc hx hFm hFlip hf hfF hφm hgradφm

end StochasticApproximation
