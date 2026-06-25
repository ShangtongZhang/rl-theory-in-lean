/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Real.StarOrdered

import RLTheory.Data.Matrix.Mul

open Real Finset Filter TopologicalSpace Preorder Matrix EuclideanSpace
open scoped InnerProductSpace RealInnerProductSpace

namespace Matrix

variable {α : Type*} [Fintype α] (A : Matrix α α ℝ)

class PosDefAsymm  : Prop where
  pd : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)

lemma posDefAsymm_iff : PosDefAsymm A ↔ Matrix.PosDef (A + Aᵀ) := by
  constructor
  case mp =>
    intro h
    constructor
    apply isHermitian_add_transpose_self
    intro x hx
    rw [star_trivial, add_mulVec, dotProduct_add,]
    rw [dotProduct_transpose_mulVec]
    have := h.pd x hx
    linarith
  case mpr =>
    intro h
    constructor
    intro x hx
    simp [PosDef] at h
    have := h.2 x hx
    rw [add_mulVec, dotProduct_add] at this
    rw [dotProduct_transpose_mulVec] at this
    linarith

theorem posDefAsymm_iff'
  {α : Type*} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) :
  PosDefAsymm A ↔ ∃ η, 0 < η ∧ ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  by_cases hα : Nonempty α
  case neg =>
    simp at hα
    constructor
    case mp =>
      intro h
      use 1
      simp
      intro x
      simp [dotProduct]
    case mpr =>
      intro h
      constructor
      intro x hx
      apply False.elim
      simp at hx
      have : x = 0 := by
        ext i
        exact (IsEmpty.false i).elim
      contradiction
  case pos =>
    rw [posDefAsymm_iff]
    constructor
    case mp =>
      intro h
      let η := (Finset.univ : Finset α).inf' (by simp) h.1.eigenvalues
      have hηmin : ∀ i, η ≤ h.1.eigenvalues i := by
        intro i
        apply Finset.inf'_le
        simp
      have hηpos : 0 < η := by
        obtain ⟨i, _, hi⟩ :=
          exists_mem_eq_inf' (s := Finset.univ) (by simp) h.1.eigenvalues
        have := h.eigenvalues_pos i
        unfold η
        rw [hi]
        exact this
      refine ⟨?η, ?hηpos, ?hη⟩
      case η => exact (2⁻¹ : ℝ) * η
      case hηpos => positivity
      case hη =>
        intro x
        apply (mul_le_mul_iff_of_pos_left (a := 2) (by simp)).mp
        conv_rhs => rw [two_mul]
        nth_rw 2 [←dotProduct_transpose_mulVec]
        rw [←dotProduct_add, ←add_mulVec, h.1.spectral_theorem]
        simp
        rw [←mulVec_mulVec, dotProduct_mulVec, ←vecMul_vecMul, ]
        rw [vecMul_diagonal_dotProduct]
        simp_rw [mul_assoc]
        rw [←mul_assoc, mul_inv_cancel₀]

        set U : Matrix α α ℝ := ↑h.1.eigenvectorUnitary with hUdef
        simp
        have := UnitaryGroup.star_mul_self h.1.eigenvectorUnitary
        rw [←hUdef] at this
        have := mem_unitaryGroup_iff.mp (mem_unitaryGroup_iff'.mpr this)
        have : x ⬝ᵥ x = x ᵥ* (U * star U) ⬝ᵥ x := by
          simp [this]
        rw [this]
        have : star U = Uᵀ := by simp [star, hUdef]
        rw [this]
        rw [←vecMul_vecMul, ←dotProduct_mulVec, dotProduct]
        rw [mul_sum]
        apply sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg
        apply hηmin
        rfl
        positivity
        nth_rw 1 [←transpose_transpose U]
        rw [vecMul_transpose, ←pow_two]
        apply sq_nonneg
        simp
    case mpr =>
      intro h
      obtain ⟨η, hηpos, hη⟩ := h
      constructor
      apply isHermitian_add_transpose_self
      intro x hx
      rw [star_trivial, add_mulVec, dotProduct_add]
      rw [dotProduct_transpose_mulVec]
      simp
      apply LT.lt.trans_le (?_) (hη x)
      apply mul_pos hηpos
      nth_rw 1 [←star_trivial x]
      apply dotProduct_star_self_pos_iff.mpr hx

class NegDefAsymm : Prop where
  nd : PosDefAsymm (-A)

section invertible

variable [DecidableEq α]

noncomputable instance [PosDefAsymm A] : Invertible A.det := by
  apply invertibleOfNonzero
  apply IsUnit.ne_zero
  apply A.isUnit_iff_isUnit_det.mp
  apply isUnit_toLin'_iff.mp
  apply A.toLin'.isUnit_iff_ker_eq_bot.mpr
  apply ker_toLin'_eq_bot_iff.mpr
  intro x hx
  by_contra h
  have hA : PosDefAsymm A := by infer_instance
  have hA := hA.pd x h
  have : x ⬝ᵥ A *ᵥ x = 0 := by
    rw [hx]
    simp
  linarith

noncomputable instance [PosDefAsymm A] : Invertible A := by
  apply Matrix.invertibleOfDetInvertible

noncomputable instance [NegDefAsymm A] : Invertible A.det := by
  apply invertibleOfNonzero
  have hdet := det_neg A
  by_contra h
  rw [h] at hdet
  simp at hdet
  have := (inferInstance : NegDefAsymm A).nd
  have : Invertible (-A).det := by infer_instance
  have := this.ne_zero
  rw [hdet] at this
  simp at this

noncomputable instance [NegDefAsymm A] : Invertible A := by
  apply Matrix.invertibleOfDetInvertible

end invertible

end Matrix
