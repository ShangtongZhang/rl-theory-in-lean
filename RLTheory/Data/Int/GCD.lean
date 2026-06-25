/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic.Linarith.Frontend

open Finset

lemma cons_eq_union
  (s : Finset ℕ) (e : ℕ) (h : e ∉ s) :
  (cons e s h) = s ∪ {e} := by
    simp; ext i; simp;
    refine Iff.intro ?mp ?mpr
    · intro h; exact Or.symm h
    · intro h; exact Or.symm h

namespace Nat

theorem xgcd_finset {s : Finset ℕ} (hs : s.Nonempty) :
  ∃ c : ℕ → ℤ, s.gcd id = s.sum fun i => i * c i := by
  refine Nonempty.cons_induction
    (singleton := ?singleton)
    (cons := ?cons)
    hs
  case singleton =>
    intro a
    refine ⟨?c, ?hc⟩
    let c : ℕ → ℤ := fun i => if i = a then 1 else 0
    case c => exact c
    case hc => simp
  case cons =>
    intro e s he hs hbase
    obtain ⟨c, hc⟩ := hbase
    let g := s.gcd id
    let g' := gcd g e
    let a := gcdA g e
    let b := gcdB g e
    let g' := gcd g e
    have hxgcd: g' = g * a + e * b := by
      unfold g'; unfold a; unfold b;
      simp [gcd_eq_gcd_ab]
    let c' : ℕ → ℤ := fun i => if i = e then b else a * c i
    let s' := s ∪ {e}
    have hg' : g' = s'.sum fun i => i * c' i := by
      rw [hxgcd]
      unfold s'
      rw [sum_union (h := by simp [he])]
      simp
      unfold c'
      simp
      have : (∑ x ∈ s, if x = e then x * b else x * (a * c x)) =
        ∑ x ∈ s, x * (a * c x) := by
        refine sum_congr rfl ?_
        · intro x hx
          have : ¬ x = e := by
            intro h'
            have : e ∈ s := by simp [h'] at hx; exact hx
            exact he this
          simp [this]
      rw [this]
      unfold g
      simp [hc, Finset.sum_mul]
      refine sum_congr rfl ?_
      · intro x hx; ring
    have hc' : (cons e s he).gcd id = ∑ i ∈ cons e s he, i * c' i := by
      have : s' = cons e s he := by
        unfold s'
        simp [←cons_eq_union s e he]
      conv_rhs =>
        rw [←this, ←hg']; unfold g'
        unfold g
      simp
      apply gcd_comm
    exact ⟨c', hc'⟩

class ClosedUnderAdd (A : Set ℕ) : Prop where
  closed_under_add : ∀ ⦃a b⦄, a ∈ A → b ∈ A → a + b ∈ A

namespace ClosedUnderAdd

variable {A : Set ℕ}

lemma mul_mem [ClosedUnderAdd A] {x : ℕ} (hx : x ∈ A) :
    ∀ n : ℕ, 0 < n → n * x ∈ A := by
  have hA := (inferInstance : ClosedUnderAdd A).closed_under_add
  intro n hn
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero =>
      cases hn
  | succ n =>
      have : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
      have hstep : (n + 1) * x = n * x + x := by ring
      cases this with
      | inl h0 => rw [h0]; simp [hx]
      | inr hnpos =>
          have hx' : n * x ∈ A := ih n (Nat.lt_succ_self n) hnpos
          simp [hstep, hA hx' hx]

lemma lincomb_mem
  [ClosedUnderAdd A] (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℕ):
  (∀ i ∈ s, i ∈ A ∧ 0 < f i) → (s.sum fun i => i * f i) ∈ A := by
  have hA := (inferInstance : ClosedUnderAdd A).closed_under_add
  refine Nonempty.cons_induction ?singleton ?cons hs
  case singleton =>
    intro a ha
    have : @Membership.mem ℕ (Finset ℕ) instMembership {a} a := by simp
    obtain ⟨ha, hfa⟩ := ha a this
    simp
    rw [mul_comm]
    exact mul_mem ha (f a) hfa
  case cons =>
    intro a s ha hs hbase hnew
    have := cons_eq_union s a ha
    rw [this]
    rw [this] at hnew
    rw [sum_union (h := by simp [ha])]
    simp
    apply hA
    · have : ∀ i ∈ s, i ∈ A ∧ 0 < f i := by
        intro i hi
        have : i ∈ s ∪ {a} := by simp [hi]
        exact hnew i this
      exact hbase this
    · have : @Membership.mem ℕ (Finset ℕ) instMembership {a} a := by simp
      have : a ∈ s ∪ {a} := by simp [this]
      obtain ⟨ha, hf⟩ := hnew a this
      rw [mul_comm]
      exact mul_mem ha (f a) hf

end ClosedUnderAdd

lemma Int.toNat_sum (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℤ) :
  (∀ i ∈ s, 0 ≤ f i) → (s.sum f).toNat = s.sum fun i => (f i).toNat := by
  refine Nonempty.cons_induction ?singleton ?cons hs
  case singleton => intro a ha; simp
  case cons =>
    intro a s has hs hbase hnew
    rw [cons_eq_union]
    rw [cons_eq_union] at hnew
    have hsa' : Disjoint s {a} := by simp [has]
    have hfi : ∀ i ∈ s, 0 ≤ f i := by
      intro i hi
      have : i ∈ s ∪ {a} := by simp [hi]
      exact hnew i this
    have h₁ : ∑ x ∈ s, 0 ≤ ∑ x ∈ s, f x := by
      apply sum_le_sum hfi
    simp at h₁
    have h₂ : 0 ≤ f a := by
      have : a ∈ s ∪ {a} := by simp
      exact hnew a this
    conv_lhs =>
      rw [sum_union hsa']
      simp
      apply Int.toNat_add h₁ h₂
    simp [hbase hfi]
    conv_rhs =>
      rw [sum_union hsa']
    rfl

class FiniteGCDOne (A : Set ℕ) : Prop where
  finite_gcd_one : ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ A ∧ s.gcd id = 1 ∧ 0 ∉ s ∧ s.Nonempty

theorem all_but_finite_of_closed_under_add_and_gcd_one
    {A : Set ℕ} [ClosedUnderAdd A] [FiniteGCDOne A] :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → n ∈ A := by
    obtain ⟨s, hsa, hgcd1, h0, hs⟩ := (inferInstance : FiniteGCDOne A)
    obtain ⟨c, hgcd⟩ := xgcd_finset hs
    rw [hgcd1] at hgcd
    let m : ℤ := (s.sum id : ℕ)
    have hmpos : 0 < m := by
      unfold m
      simp
      obtain ⟨i, hi⟩ := hs
      have : i ≠ 0 := by
        intro h
        exact h0 (by simpa [h] using hi)
      have : 0 < (i : ℤ) := by
        exact_mod_cast (Nat.pos_of_ne_zero this)
      apply sum_pos'
      · intro x hx; simp
      · exact ⟨i, hi, this⟩
    let c_bound := s.sum fun i => |c i|
    have hcmax : ∀ i ∈ s, |c i| ≤ c_bound := by
      intro i hi; unfold c_bound;
      rw [←sum_erase_add _ _ hi]
      simp
      apply sum_nonneg
      intro j hj; simp [abs_nonneg]
    have hcnonneg : 0 ≤ c_bound := by
      unfold c_bound
      have : (0 : ℤ) = ∑ i ∈ s, 0 := by simp
      conv_lhs => rw [this]
      apply sum_le_sum
      · simp
    let B := m * m * c_bound + m
    have hBnonneg : 0 ≤ B := by
      apply add_nonneg
      · simp [hcnonneg, hmpos]
      · exact hmpos.le
    have h : ∀ n, B ≤ n → n.toNat ∈ A := by
      intro n hn
      have : n = n / m * m + n % m * (1 : ℕ) := by
        simp
        linarith [Int.emod_add_ediv n m]
      set k := n / m
      set r := n % m
      conv_rhs at this =>
        rw [hgcd]
        unfold m
        simp [mul_comm, sum_mul]
        pattern r * ∑ x ∈ s, c x * x
        simp [mul_comm r _, sum_mul]
      conv_rhs at this =>
        rw [←sum_add_distrib]
      let c' : ℕ → ℤ := fun i => k + r * c i
      have hnrep : n = ∑ i ∈ s, i * c' i := by
        rw [this]
        apply sum_congr rfl _
        intro x hx; ring
      have hcpos : ∀ i ∈ s, 0 < c' i := by
        intro i hi
        unfold c'
        have : -r * c i ≤ m * c_bound := by calc
            -r * c i
          _ ≤ |r * c i| := by simp [neg_le_abs]
          _ = |r| * |c i| := by simp [abs_mul]
          _ ≤ |r| * c_bound := by
            have := hcmax i hi
            gcongr
          _ ≤ r * c_bound := by
            have : 0 ≤ r := by
              have := Int.emod_nonneg n hmpos.ne'
              exact this
            simp [abs_of_nonneg this]
          _ ≤ m * c_bound := by
            have := Int.emod_lt n hmpos.ne'
            rw [Int.natAbs_of_nonneg hmpos.le] at this
            gcongr
        have : m * c_bound < k := by
          unfold k
          unfold B at hn
          have := Int.ediv_le_ediv hmpos hn
          have hcancel : (m * m * c_bound + m * 1) / m
            = m * c_bound + 1 := by
            simp only [mul_assoc, ←mul_add]
            simp [mul_comm _ (m * c_bound + 1)]
            apply Int.mul_ediv_cancel
            · exact hmpos.ne'
          simp at hcancel
          rw [hcancel] at this
          linarith
        linarith
      simp [hnrep]
      have : ∀ i ∈ s, 0 ≤ i * c' i := by
        intro i hi
        apply mul_nonneg
        · simp
        · exact le_of_lt (hcpos i hi)
      rw [Int.toNat_sum (hs := hs)]
      case a => exact this
      have : ∑ i ∈ s, (↑i * c' i).toNat = ∑ i ∈ s, i * (c' i).toNat := by
        apply sum_congr rfl _
        intro i hi;
        have ha : 0 ≤ (i : ℤ) := by simp
        have hb : 0 ≤ c' i := le_of_lt (hcpos i hi)
        simp [Int.toNat_mul ha hb]
      rw [this]
      apply ClosedUnderAdd.lincomb_mem (hs := hs)
      · intro i hi; simp; exact ⟨hsa hi, hcpos i hi⟩
    refine ⟨?n₀, ?hn₀⟩
    case n₀ => exact B.toNat
    case hn₀ =>
      intro n hn
      have := h n (Int.toNat_le.mp hn)
      simp at this
      exact this

end Nat
