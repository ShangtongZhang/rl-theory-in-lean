/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Real.StarOrdered

import RLTheory.Defs
import RLTheory.MeasureTheory.MeasurableSpace.Constructions
import RLTheory.Probability.MarkovChain.Defs
import RLTheory.Probability.MarkovChain.Finite.Defs
import RLTheory.Probability.MarkovChain.Trajectory
import RLTheory.Data.Matrix.PosDef

open ENNReal Real Finset Filter TopologicalSpace Filter MeasureTheory.Filtration MeasureTheory ProbabilityTheory StochasticMatrix Preorder RLTheory Matrix EuclideanSpace
open scoped MeasureTheory ProbabilityTheory Topology InnerProductSpace RealInnerProductSpace

namespace ReinforcementLearning

universe u
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

variable {d : ℕ}

structure FiniteMRP where
  M : MarkovChain.HomMarkovChainSpec S
  hM : StochasticMatrix.Irreducible (MarkovChain.Finite.kernel_mat M) ∧
    StochasticMatrix.Aperiodic (MarkovChain.Finite.kernel_mat M)
  γ : ℝ
  hγ : 0 ≤ γ ∧ γ < 1
  r : S → ℝ

variable {MRP : FiniteMRP (S := S)}

noncomputable def FiniteMRP.P : Matrix S S ℝ :=
  MarkovChain.Finite.kernel_mat MRP.M

instance : RowStochastic MRP.P := by
  simp [FiniteMRP.P]
  infer_instance

instance : StochasticMatrix.Irreducible MRP.P := by
  simp [FiniteMRP.P]
  exact MRP.hM.1

noncomputable def FiniteMRP.p₀ : S → ℝ :=
  MarkovChain.Finite.init_vec MRP.M

instance : StochasticVec MRP.p₀ := by
  simp [FiniteMRP.p₀]
  infer_instance

noncomputable def FiniteMRP.μ : S → ℝ :=
  (stationary_distribution_exists MRP.P).choose

instance : StochasticVec MRP.μ :=
  (stationary_distribution_exists MRP.P).choose_spec.1

instance : Stationary MRP.μ MRP.P := by
  exact (stationary_distribution_exists MRP.P).choose_spec.2

lemma FiniteMRP.mixing :
  ∃ ρ C, 0 < ρ ∧ ρ < 1 ∧ 0 ≤ C ∧ ∀ s n,
    ∑ s', |(MRP.P ^ n) s s' - MRP.μ s'| ≤ C * ρ ^ n := by
  have : StochasticMatrix.Irreducible MRP.P := by infer_instance
  have : StochasticMatrix.Aperiodic MRP.P := by exact MRP.hM.2
  have hP : GeometricMixing MRP.P := by infer_instance
  obtain ⟨C, ρ, μ, _, _, _, hμ, hμP, hmix⟩ := hP
  use ρ, C
  constructor; simpa
  constructor; simpa
  constructor; linarith
  intro s n
  have : μ = MRP.μ := by
    have := stationary_distribution_uniquely_exists MRP.P
    obtain ⟨μ', hμ', huniq⟩ := this
    simp at huniq
    have h₁ := huniq μ hμ hμP
    have h₂ := huniq MRP.μ ?_ ?_
    exact h₁.trans h₂.symm
    infer_instance
    infer_instance
  rw [←this]
  let x : S → ℝ := fun s' => if s' = s then 1 else 0
  have hx : StochasticVec x := by
    constructor
    intro s'
    unfold x
    by_cases h : s' = s
    simp [h]
    simp [h]
    simp [x]
  have := hmix x n
  simp [nnnorm, Norm.norm, vecMul, dotProduct, x] at this
  exact this

noncomputable def FiniteMRP.D : Matrix S S ℝ :=
  Matrix.diagonal MRP.μ

noncomputable def FiniteMRP.K : Matrix S S ℝ :=
  MRP.D * (MRP.γ • MRP.P - 1)

lemma FiniteMRP.posDef_of_D : PosDef MRP.D := by
  have hμpos := pos_of_stationary MRP.μ MRP.P
  exact PosDef.diagonal hμpos

noncomputable def FiniteMRP.normedAddCommGroup :
  NormedAddCommGroup (S → ℝ) :=
  MRP.D.toNormedAddCommGroup MRP.posDef_of_D

noncomputable def FiniteMRP.seminormedAddCommGroup :
  SeminormedAddCommGroup (S → ℝ) :=
  MRP.normedAddCommGroup.toSeminormedAddCommGroup

noncomputable def FiniteMRP.innerProductSpace :
  @InnerProductSpace ℝ (S → ℝ) _ MRP.seminormedAddCommGroup :=
  MRP.D.toInnerProductSpace MRP.posDef_of_D.posSemidef

local notation "⟪" x ", " y "⟫" =>
  @Inner.inner ℝ (S → ℝ) MRP.innerProductSpace.toInner x y

local notation (priority := 2000) "‖" x "‖" =>
  @Norm.norm (S → ℝ) MRP.seminormedAddCommGroup.toNorm x

lemma FiniteMRP.innder_def (x y : S → ℝ) :
  ⟪x, y⟫ = x ᵥ* MRP.D ⬝ᵥ y := by
  -- The inner product from toInnerProductSpace is (M *ᵥ y) ⬝ᵥ star x = (D *ᵥ y) ⬝ᵥ x
  -- We need to show this equals x ᵥ* D ⬝ᵥ y
  show (MRP.D *ᵥ y) ⬝ᵥ x = x ᵥ* MRP.D ⬝ᵥ y
  rw [dotProduct_comm, dotProduct_mulVec]

lemma FiniteMRP.inner_eq_sum (x) :
  ⟪x, x⟫ = ∑ s, MRP.μ s * x s ^ 2 := by
  rw [MRP.innder_def]
  simp only [FiniteMRP.D, vecMul_diagonal, dotProduct]
  apply sum_congr rfl
  intro s _
  ring

lemma FiniteMRP.nonexpansive_P :
  ∀ v, ‖MRP.P *ᵥ v‖ ≤ ‖v‖ := by
  letI instSemi : SeminormedAddCommGroup (S → ℝ) := MRP.seminormedAddCommGroup
  letI instIPS : InnerProductSpace ℝ (S → ℝ) := MRP.innerProductSpace
  have hP := (inferInstance : RowStochastic MRP.P)
  intro v
  apply le_of_sq_le_sq
  rw [@norm_sq_eq_re_inner ℝ (S → ℝ) _ instSemi instIPS,
      @norm_sq_eq_re_inner ℝ (S → ℝ) _ instSemi instIPS]
  rw [inner_eq_sum, inner_eq_sum]
  simp only [RCLike.re_to_real]
  have hstat := fun s => congrFun
    (inferInstance : Stationary MRP.μ MRP.P).stationary s
  conv_rhs =>
    arg 2; ext s'
    rw [←hstat s', vecMul, dotProduct, sum_mul]
  rw [sum_comm]
  apply sum_le_sum
  intro s hs
  simp_rw [mul_assoc]
  rw [←mul_sum]
  apply mul_le_mul_of_nonneg_left
  simp [mulVec, dotProduct]
  have := real_inner_mul_inner_self_le (F := WithLp 2 (S → ℝ))
    (x := WithLp.toLp 2 (fun i => √(MRP.P s i)))
    (y := WithLp.toLp 2 (fun i => √(MRP.P s i) * v i))
  simp only [EuclideanSpace.inner_toLp_toLp, star_trivial, ←pow_two] at this
  apply (LE.le.trans ?_ this).trans ?_
  apply le_of_eq
  apply congr
  apply congr rfl
  apply sum_congr rfl
  intro s' hs'
  ring_nf
  rw [sq_sqrt]
  ring
  apply (hP.stochastic s).nonneg
  · rfl
  apply le_of_eq
  simp only [dotProduct]
  have hsqrt : ∀ s', √(MRP.P s s') * √(MRP.P s s') = MRP.P s s' :=
    fun s' => Real.mul_self_sqrt ((hP.stochastic s).nonneg s')
  simp only [hsqrt, (hP.stochastic s).rowsum, one_mul]
  apply sum_congr rfl
  intro s' _
  have h : √(MRP.P s s') * v s' * (√(MRP.P s s') * v s') =
           √(MRP.P s s') * √(MRP.P s s') * (v s' * v s') := by ring
  rw [h, hsqrt s', sq]
  ring_nf
  apply (inferInstance : StochasticVec MRP.μ).nonneg
  apply @norm_nonneg _ instSemi.toSeminormedAddGroup v

lemma FiniteMRP.vecMul_DP_dotProduct_le_norm (v : S → ℝ) :
  v ᵥ* (MRP.D * MRP.P) ⬝ᵥ v ≤ v ᵥ* MRP.D ⬝ᵥ v := by
  letI instSemi : SeminormedAddCommGroup (S → ℝ) := MRP.seminormedAddCommGroup
  letI : InnerProductSpace ℝ (S → ℝ) := MRP.innerProductSpace
  rw [←MRP.innder_def, real_inner_self_eq_norm_sq]
  rw [←vecMul_vecMul, ←dotProduct_mulVec, ←MRP.innder_def]
  grw [real_inner_le_norm]
  grw [MRP.nonexpansive_P]
  rw [pow_two]
  apply @norm_nonneg _ instSemi.toSeminormedAddGroup v

instance : NegDefAsymm MRP.K := by
  have hμpos := pos_of_stationary MRP.μ MRP.P
  constructor
  constructor
  intro z hz
  rw [neg_mulVec, dotProduct_neg, FiniteMRP.K, Matrix.mul_sub,]
  simp
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]
  simp
  simp_rw [dotProduct_mulVec]
  grw [MRP.vecMul_DP_dotProduct_le_norm]
  apply mul_lt_of_lt_one_left
  rw [FiniteMRP.D]
  -- z ᵥ* diagonal μ ⬝ᵥ z = ∑ s, z s * μ s * z s > 0 since μ > 0 and z ≠ 0
  simp only [vecMul_diagonal, dotProduct]
  -- Use sum_pos' which requires all terms nonneg and at least one positive
  have hrewrite : ∀ s, z s * MRP.μ s * z s = MRP.μ s * z s ^ 2 := fun s => by ring
  simp only [hrewrite]
  -- z ≠ 0 means ∃ s, z s ≠ 0
  have ⟨s₀, hs₀⟩ : ∃ s, z s ≠ 0 := by
    by_contra! hall
    apply hz
    funext s
    exact hall s
  apply Finset.sum_pos'
  · intro s _
    apply mul_nonneg (le_of_lt (hμpos s))
    apply sq_nonneg
  · exact ⟨s₀, Finset.mem_univ s₀, mul_pos (hμpos s₀) (sq_pos_of_ne_zero hs₀)⟩
  exact MRP.hγ.2
  exact MRP.hγ.1

noncomputable def FiniteMRP.aug_chain_iid :
  MarkovChain.HomMarkovChainSpec (S × S) := by
  have hP : RowStochastic MRP.P := by infer_instance
  have hμ : StochasticVec MRP.μ := by infer_instance
  have μ : PMF (S × S) := by
    unfold PMF
    let f : S × S → ℝ≥0∞ := fun y => ENNReal.ofReal (MRP.μ y.1 * MRP.P y.1 y.2)
    use f
    have : ∑ y, f y = 1 := by
      simp [f]
      rw [←ENNReal.ofReal_sum_of_nonneg]
      simp
      rw [Fintype.sum_prod_type]
      simp
      apply sum_svec_mul_smat_eq_one
      intro y hy
      apply mul_nonneg
      apply hμ.nonneg
      apply (hP.stochastic y.1).nonneg
    rw [←this]
    apply hasSum_fintype
  let κ := Kernel.const (S × S) μ.toMeasure
  have M : MarkovChain.HomMarkovChainSpec (S × S) := by
    constructor
    case kernel => exact κ
    case init => exact ⟨μ.toMeasure, by infer_instance⟩
    case markov_kernel =>
      constructor
      intro s
      simp [κ]
      infer_instance
  exact M

noncomputable def FiniteMRP.iid_samples :=
  (MarkovChain.traj_prob MRP.aug_chain_iid).1

noncomputable def FiniteMRP.aug_chain_markov :
  MarkovChain.HomMarkovChainSpec (S × S) := by
  have hP : RowStochastic MRP.P := by infer_instance
  have hp₀ : StochasticVec MRP.p₀ := by infer_instance
  let init : PMF (S × S) := by
    unfold PMF
    let f : S × S → ℝ≥0∞ := fun y => ENNReal.ofReal (MRP.p₀ y.1 * MRP.P y.1 y.2)
    use f
    have : ∑ y, f y = 1 := by
      simp [f]
      rw [←ENNReal.ofReal_sum_of_nonneg]
      simp
      rw [Fintype.sum_prod_type]
      simp
      apply sum_svec_mul_smat_eq_one
      intro y hy
      apply mul_nonneg
      apply hp₀.nonneg
      apply (hP.stochastic y.1).nonneg
    rw [←this]
    apply hasSum_fintype
  let κ : Kernel (S × S) (S × S) := by
    let f : S × S → PMF (S × S) := fun y => by
        unfold PMF
        let f' : S × S → ℝ≥0∞ := fun z =>
          ENNReal.ofReal (if y.2 = z.1 then MRP.P z.1 z.2 else 0)
        use f'
        have : ∑ y, f' y = 1 := by
          simp [f']
          rw [←ENNReal.ofReal_sum_of_nonneg]
          simp
          simp [Fintype.sum_prod_type]
          apply (hP.stochastic y.2).rowsum
          intro z hz
          by_cases h : y.2 = z.1
          simp [h]
          apply (hP.stochastic z.1).nonneg
          simp [h]
        rw [←this]
        apply hasSum_fintype
    constructor
    case toFun => exact PMF.toMeasure ∘ f
    case measurable' =>
      apply measurable_of_countable
  constructor
  case init => exact ⟨init.toMeasure, by infer_instance⟩
  case kernel => exact κ
  case markov_kernel =>
    constructor
    intro y
    simp [κ]
    infer_instance

noncomputable def FiniteMRP.markov_samples :=
  (MarkovChain.traj_prob MRP.aug_chain_markov).1

open MarkovChain.Finite in
omit [Nonempty S] in
lemma FiniteMRP.aug_chain_markov_kmat_pow {n : ℕ} (hn : 1 ≤ n) :
  ∀ y z, (kernel_mat MRP.aug_chain_markov ^ n) y z
    = (MRP.P ^ (n - 1)) y.2 z.1 * MRP.P z.1 z.2 := by
  have hP : RowStochastic MRP.P := by infer_instance
  have hbase : ∀ y z, (kernel_mat MRP.aug_chain_markov ^ 1) y z
    = (MRP.P ^ (1 - 1)) y.2 z.1 * MRP.P z.1 z.2 := by
    intro y z
    simp [-PMF.toMeasure_apply_fintype, kernel_mat, aug_chain_markov]
    apply Eq.trans
    apply congrArg
    apply PMF.toMeasure_apply_singleton
    simp
    conv_lhs =>
      congr;
      change (fun z => ENNReal.ofReal _) z
    rw [ENNReal.toReal_ofReal]
    simp [Matrix.one_apply]
    by_cases h : y.2 = z.1
    simp [h]
    apply (hP.stochastic z.1).nonneg
    simp [h]
  refine Nat.le_induction hbase ?succ n hn
  case succ =>
    intro n hn ih y z
    rw [pow_add, Matrix.mul_apply]
    simp_rw [ih, hbase]
    simp [Matrix.one_apply, Fintype.sum_prod_type, ←sum_mul]
    apply Or.inl
    have : n = n - 1 + 1 := by omega
    conv_rhs =>
      rw [this, pow_add, Matrix.mul_apply]
    simp

end ReinforcementLearning
