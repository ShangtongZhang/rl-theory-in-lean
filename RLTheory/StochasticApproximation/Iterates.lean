/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

import RLTheory.Defs
import RLTheory.MeasureTheory.MeasurableSpace.Constructions
import RLTheory.MeasureTheory.Group.Arithmetic
import RLTheory.Probability.MarkovChain.Defs
import RLTheory.Probability.MarkovChain.Finite.Defs
import RLTheory.Probability.MarkovChain.Trajectory
import RLTheory.MarkovDecisionProcess.MarkovRewardProcess
import RLTheory.StochasticApproximation.Lyapunov
import RLTheory.StochasticApproximation.DiscreteGronwall

open Real Finset Filter TopologicalSpace Filter MeasureTheory.Filtration MeasureTheory ProbabilityTheory StochasticMatrix Preorder RLTheory
open scoped MeasureTheory ProbabilityTheory Topology InnerProductSpace RealInnerProductSpace

namespace StochasticApproximation

variable {d : ℕ}
variable {x₀ : E d}
variable {α : ℕ → ℝ}
variable {f : E d → E d}

lemma linear_growth_of_lipschitz {f : E d → E d}
  (hf : ∃ C, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖) :
  ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * (‖x‖ + 1) := by
  obtain ⟨C, hCnonneg, hC⟩ := hf
  refine ⟨?L, ?hLnonneg, ?hL⟩
  case L => exact max C ‖f 0‖
  case hLnonneg => positivity
  case hL =>
    intro z
    have := hC z 0
    grw [norm_le_norm_sub_add (b := f 0)]
    grw [this]
    simp
    rw [mul_add]
    apply add_le_add
    have : C ≤ max C ‖f 0‖ := by apply le_max_left
    gcongr
    simp

lemma linear_growth_of_lipschitz'
  {α : Type*} [Nonempty α] [Fintype α] {f : E d → α → E d}
  (hf : ∃ C, 0 ≤ C ∧ ∀ x y z, ‖f x z - f y z‖ ≤ C * ‖x - y‖) :
  ∃ C, 0 ≤ C ∧ ∀ x z, ‖f x z‖ ≤ C * (‖x‖ + 1) := by
  obtain ⟨C, hCnonneg, hC⟩ := hf
  let CF := Finset.univ.sup' (by simp) fun z => ‖f 0 z‖
  refine ⟨?L, ?hLnonneg, ?hL⟩
  case L => exact max CF C
  case hLnonneg => positivity
  case hL =>
    intro y z
    grw [norm_le_norm_sub_add (b := f 0 z)]
    grw [hC y 0 z]
    simp
    rw [mul_add]
    apply add_le_add
    have : C ≤ max CF C := by apply le_max_right
    gcongr
    simp
    apply Or.inl
    apply Finset.le_sup' fun z => ‖f 0 z‖
    simp

section extraneous_errors

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {e₁ e₂ : ℕ → Ω → E d}

class Iterates (x : ℕ → Ω → E d)
  (x₀ : E d) (f : E d → E d) (e₁ e₂ : ℕ → Ω → E d) (α : ℕ → ℝ) where
  init : ∀ ω, x 0 ω = x₀
  step : ∀ n ω, x (n + 1) ω =
    x n ω + (α n) • (f (x n ω) - x n ω) + e₁ (n + 1) ω + e₂ (n + 1) ω

lemma bdd_of_iterates
  {x : ℕ → Ω → E d}
  (hx : Iterates x x₀ f e₁ e₂ α)
  (he₁ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₁ (n + 1) ω‖≤ C * (α n) * (‖x n ω‖ + 1))
  (he₂ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n,
    ‖e₂ (n + 1) ω‖≤ C * (α n) ^ 2 * (‖x n ω‖ + 1))
  (hfLip : ∃ L, LipschitzWith L f)
  (hαpos : ∀ n, 0 < α n) :
  ∀ n, ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ‖x n ω‖ ≤ C := by
  intro n
  induction' n with n hn
  case zero =>
    refine ⟨‖x₀‖, by simp, ?h⟩
    apply Eventually.of_forall
    intro ω
    rw [hx.init]
  case succ =>
    obtain ⟨Lf, hfLip⟩ := hfLip
    have hfLip := lipschitzWith_iff_norm_sub_le.mp hfLip
    obtain ⟨C₁, hC₁nonneg, hC₁⟩ := he₁
    obtain ⟨C₂, hC₂nonneg, hC₂⟩ := he₂
    obtain ⟨C₃, hC₃pos, hC₃⟩ := hn
    let C := C₃ + |α n| * (↑Lf * C₃ + ‖f 0‖ + C₃)
      + C₁ * α n * (C₃ + 1) + C₂ * α n ^ 2 * (C₃ + 1)
    refine ⟨C, ?hCnonneg, ?hC⟩
    case hC =>
      apply Eventually.mono ((hC₁.and hC₂).and hC₃)
      intro ω hω
      obtain ⟨⟨hC₁, hC₂⟩, hC₃⟩ := hω
      rw [hx.step]
      grw [norm_add_le]
      grw [norm_add_le]
      grw [norm_add_le]
      rw [norm_smul]
      grw [norm_sub_le]
      grw [hC₁ n]
      grw [hC₂ n]
      have := hfLip (x n ω) 0
      simp at this
      have := (norm_sub_norm_le (f (x n ω)) (f 0)).trans this
      have := sub_le_iff_le_add.mp this
      grw [this]
      simp
      grw [hC₃]
      apply mul_nonneg hC₁nonneg (hαpos n).le
    case hCnonneg =>
      have := hαpos n
      positivity

lemma bdd_of_φ
  {x : ℕ → Ω → E d}
  (hx : Iterates x x₀ f e₁ e₂ α)
  (he₁ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₁ (n + 1) ω‖≤ C * (α n) * (‖x n ω‖ + 1))
  (he₂ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n,
    ‖e₂ (n + 1) ω‖≤ C * (α n) ^ 2 * (‖x n ω‖ + 1))
  (hfLip : ∃ L, LipschitzWith L f)
  (hf : ∃ z, z = f z)
  (hαpos : ∀ n, 0 < α n)
  {φ : E d → ℝ}
  {φ' : E d → E d}
  [LyapunovFunction φ φ' f] :
  ∀ n, ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, φ (x n ω - hf.choose) ≤ C := by
    have hEnergy : LyapunovFunction φ φ' f := by infer_instance
    obtain ⟨C₁, hC₁nonneg, hC₁⟩ := hEnergy.le_norm
    intro n
    have := bdd_of_iterates hx he₁ he₂ hfLip hαpos n
    obtain ⟨C₂, hC₂nonneg, hC₂⟩ := this
    let C := (C₁ * (C₂ + ‖hf.choose‖)) ^ 2
    refine ⟨C, ?hCnonneg, ?hC⟩
    case hC =>
      apply Eventually.mono hC₂
      intro ω hC₂
      rw [←Real.sq_sqrt (hEnergy.nonneg (x n ω - hf.choose))]
      grw [hC₁ (x n ω - hf.choose)]
      grw [norm_sub_le]
      grw [hC₂]
    case hCnonneg =>
      positivity

lemma bdd_of_grad_φ_inner
  {x : ℕ → Ω → E d}
  (hx : Iterates x x₀ f e₁ e₂ α)
  (he₁ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₁ (n + 1) ω‖≤ C * (α n) * (‖x n ω‖ + 1))
  (he₂ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n,
    ‖e₂ (n + 1) ω‖≤ C * (α n) ^ 2 * (‖x n ω‖ + 1))
  (hfLip : ∃ L, LipschitzWith L f)
  (hf : ∃ z, z = f z)
  (hαpos : ∀ n, 0 < α n)
  {φ : E d → ℝ}
  {φ' : E d → E d}
  [LyapunovFunction φ φ' f] :
  ∀ n z, ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ⟪φ' (x n ω - hf.choose), z⟫ ≤ C * √(φ z) := by
    have hEnergy : LyapunovFunction φ φ' f := by infer_instance
    obtain ⟨C₁, hC₁nonneg, hC₁⟩ := hEnergy.le_norm
    intro n
    have := bdd_of_iterates hx he₁ he₂ hfLip hαpos n
    obtain ⟨C₂, hC₂nonneg, hC₂⟩ := this
    obtain ⟨C₃, hC₃pos, hC₃⟩ := hEnergy.inner_grad_le
    intro z
    let C := C₃ * √((C₁ * (C₂ + ‖hf.choose‖)) ^ 2)
    refine ⟨C, ?hCnonneg, ?hC⟩
    case hC =>
      apply Eventually.mono hC₂
      intro ω hC₂
      grw [hC₃ (x n ω - hf.choose) z]
      rw [←Real.sq_sqrt (hEnergy.nonneg (x n ω - hf.choose))]
      grw [hC₁ (x n ω - hf.choose)]
      grw [norm_sub_le]
      grw [hC₂]
    case hCnonneg =>
      positivity

end extraneous_errors

section adapted

variable {S Z: Type*} [MeasurableSpace S] [MeasurableSpace Z] [Norm Z]
instance : ∀ n : ℕ, MeasurableSpace (Iic n → S) := by infer_instance

class AdaptedOnSamplePath (x : ℕ → (ℕ → S) → Z) where
  property : ∀ n, ∃ xn : (Iic n → S) → Z, Measurable xn ∧ ∀ ω,
    x n ω = xn (frestrictLe (a := n) ω)

end adapted

section intravenous_errors

variable {S : Type*} [Fintype S] [Nonempty S]

variable {F : E d → (S × S) → E d}
variable {x : ℕ → (ℕ → S × S) → E d}

omit [Nonempty S] in
lemma lipschitz_of_expectation
  {f : E d → E d} {μ : S → ℝ} [StochasticVec μ]
  {P : Matrix S S ℝ} [RowStochastic P]
  (hfF : ∀ w, f w = ∑ s, ∑ s', (μ s * P s s') • F w (s, s'))
  (hFlip : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖) :
  ∃ C, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ := by
  have hP : RowStochastic P := by infer_instance
  have hμ : StochasticVec μ := by infer_instance
  obtain ⟨C, hCnonneg, hC⟩ := hFlip
  use C
  constructor
  exact hCnonneg
  intro w w'
  simp [hfF]
  simp_rw [←sum_sub_distrib, ←smul_sub]
  grw [norm_sum_le, sum_le_sum]
  rotate_left
  intro s hs
  grw [norm_sum_le]
  simp_rw [norm_smul, norm_mul]
  simp
  grw [sum_le_sum]
  rotate_left
  intro s hs
  grw [sum_le_sum]
  intro s' hs'
  apply LE.le.trans
  grw [hC]
  rw [abs_of_nonneg, abs_of_nonneg]
  apply (hP.stochastic s).nonneg
  apply hμ.nonneg
  simp_rw [mul_assoc, ←mul_sum, ←sum_mul, (hP.stochastic ?_).rowsum,
    ←sum_mul, hμ.rowsum]
  simp

class IteratesOfResidual (x : ℕ → (ℕ → (S × S)) → E d)
  (x₀ : E d) (α : ℕ → ℝ) (F : E d → (S × S) → E d) where
  init : ∀ ω, x 0 ω = x₀
  step : ∀ n ω,
    x (n + 1) ω = x n ω + α n • (F (x n ω) (ω (n + 1)) - x n ω)

lemma IteratesOfResidual.bdd
  (hx : IteratesOfResidual x x₀ α F)
  (hF : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖) :
  ∀ n, ∃ C, 0 ≤ C ∧ ∀ ω, ‖x n ω‖ ≤ C := by
  intro n
  induction' n with n hn
  case zero =>
    use ‖x₀‖
    constructor
    simp
    intro ω
    rw [hx.init]
  case succ =>
    obtain ⟨C₁, hC₁nonneg, hC₁⟩ := hn
    obtain ⟨C₂, hC₂nonneg, hC₂⟩ := linear_growth_of_lipschitz' hF
    refine ⟨?C, ?hCnonneg, ?hC⟩
    case C => exact C₁ + |α n| * (C₂ * (C₁ + 1) + C₁)
    case hCnonneg => positivity
    case hC =>
      intro ω
      rw [hx.step]
      grw [norm_add_le]
      rw [norm_smul]
      grw [norm_sub_le, hC₂, hC₁]
      simp

lemma IteratesOfResidual.growth
  (hx : IteratesOfResidual x x₀ α F)
  (hα : ∀ n, 0 ≤ α n)
  (hF : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖) :
  ∃ C, 0 ≤ C ∧ ∀ ω n m, ∀ i ∈ Ico n m, ‖x i ω - x n ω‖ ≤
    (∑ k ∈ Ico n m, α k * C * (‖x n ω‖ + 1)) * exp (∑ j ∈ Ico n m, α j * C)
    := by
  obtain ⟨C₁, hC₁nonneg, hC₁⟩ := linear_growth_of_lipschitz' hF
  obtain ⟨C₂, hC₂nonneg, hC₂⟩ := hF
  set C := C₁ + 1
  refine ⟨C, ?hCnonneg, ?hC⟩
  case hCnonneg => positivity
  case hC =>
    intro ω n
    have : ∀ i ≥ n, ‖x (i + 1) ω - x n ω‖ ≤
      (1 + α i * C) * ‖x i ω - x n ω‖ + α i * C * (‖x n ω‖ + 1) := by
      intro i hi
      rw [hx.step, ←sub_add_eq_add_sub]
      grw [norm_add_le]
      rw [norm_smul]
      nth_grw 2 [norm_sub_le]
      grw [hC₁]
      have : x i ω = x n ω + (x i ω - x n ω) := by simp
      nth_rw 2 [this]
      nth_rw 3 [this]
      grw [norm_add_le]
      simp [abs_of_nonneg (hα i), C]
      ring_nf
      simp
      exact hα i
    intro m i hi
    have := discrete_gronwall_Ico (n₁ := m) (hu := this)
      (u := fun k => ‖x k ω - x n ω‖) ?_ ?_ ?_ i hi
    simp at this
    exact this
    simp; intro j hi; simp; have := hα j; positivity
    simp; intro k hk; have := hα k; positivity

variable [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Nonempty S] in
lemma IteratesOfResidual.adaptedOnSamplePath
  (hx : IteratesOfResidual x x₀ α F) :
  AdaptedOnSamplePath x := by
  constructor
  intro n
  induction' n with n hn
  case zero =>
    use fun _ => x₀
    simp [hx.init]
  case succ =>
    obtain ⟨xn, hxn⟩ := hn
    use fun ω =>
      let ωn := frestrictLe₂ («π» := fun _ : ℕ => S × S)
        (a := n) (b := n + 1) (by simp) ω
      let m : Iic (n + 1) := ⟨n + 1, by simp⟩
      xn ωn + (α n) • (F (xn ωn) (ω m) - xn ωn)
    refine ⟨?hm, ?heq⟩
    case heq =>
      intro ω
      simp [hx.step, hxn]
      rfl
    case hm =>
      measurability

end intravenous_errors

end StochasticApproximation
