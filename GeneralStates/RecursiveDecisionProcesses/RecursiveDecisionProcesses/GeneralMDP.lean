/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.LDPOptimality

/-!
# Markov decision processes on general state spaces

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.1.5 (pp. 197–199).

An MDP `(Γ, r, β, P)` is an LDP whose kernel is `K = βP` (6.12) with `β ∈ [0, 1)` and `P`
stochastic (`ofMDP`); `T_σ = r_σ + βP_σ` (6.13). This also covers **Example 6.1.3** (a finite
MDP is the LDP with `K = βP`, and `‖K_σ‖ ≤ β`).

* **Proposition 6.1.7** (Feller MDPs): under Assumption 6.1.1 with `P` weak Feller, the fundamental
  optimality properties hold, `v* ∈ bcX` and VFI converges geometrically on `bcX`; if `P` is strong
  Feller, OPI and HPI converge. The discount operator is `Dh = β (sup h) 𝟙` in place of the book's
  `(Dh)(x) = β max_{a ∈ Γ(x)} ∫ h dP(x, a)`, which need not be measurable for merely measurable `h`;
  both dominate `K_σ` on `bX₊` and contract with modulus `β`.
* §6.1.5.2: under strong Feller, greedy policies are the pointwise maximizers (6.14) and the
  Bellman operator is (6.15) (from §6.1.3.2).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- The MDP `(Γ, r, β, P)` (§6.1.5.1) as an LDP with `K = βP` (6.12). -/
noncomputable def ofMDP (Γ : X → Set A) (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hσ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) :
    LDP X A where
  Γ := Γ
  r := r
  β := BM.const β
  β_nonneg _ := hβ0
  P := P
  exists_policy := hσ

/-- (6.13): `(T_σ v)(x) = r(x, σ(x)) + β ∫ v(x')P(x, σ(x), dx')`. -/
theorem ofMDP_T_apply (Γ : X → Set A) (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hσ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x)
    (σ : (ofMDP Γ r hβ0 P hσ).Policy) (v : BM X) (x : X) :
    ((ofMDP Γ r hβ0 P hσ).adp.T σ v).toFun x =
      r.toFun (x, σ.1 x) + β * ∫ x', v.toFun x' ∂(P (x, σ.1 x)) := rfl

/-- **Example 6.1.3** (p. 190): for an MDP, `|∫ v dK(x, a)| ≤ β‖v‖`, so `Kv ∈ bG` and
`‖K_σ‖ ≤ β`. -/
theorem example_6_1_3 (Γ : X → Set A) (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hσ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x)
    (σ : (ofMDP Γ r hβ0 P hσ).Policy) : ‖(ofMDP Γ r hβ0 P hσ).K σ‖ ≤ β := by
  refine ((ofMDP Γ r hβ0 P hσ).norm_K_le σ).trans ?_
  exact BM.norm_le hβ0 fun _ => by simp [ofMDP, abs_of_nonneg hβ0]

/-- `Dh = β (sup h) 𝟙`. -/
noncomputable def Dsup (β : ℝ) (h : BM X) : BM X := BM.const (β * ⨆ x, h.toFun x)

theorem abs_iSup_sub_le (u v : BM X) : |(⨆ x, u.toFun x) - ⨆ x, v.toFun x| ≤ ‖u - v‖ := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp
  · have hbu : BddAbove (range u.toFun) :=
      ⟨‖u‖, by rintro _ ⟨x, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm u x)⟩
    have hbv : BddAbove (range v.toFun) :=
      ⟨‖v‖, by rintro _ ⟨x, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm v x)⟩
    exact abs_ciSup_sub_ciSup_le hbu hbv fun x =>
      (BM.abs_sub_le_dist u v x).trans (dist_eq_norm u v).le

/-- `Dh = β (sup h) 𝟙` is a discount operator for `0 ≤ β < 1`. -/
theorem Dsup_isDiscountOperator {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    BanachLattice.IsDiscountOperator (Dsup (X := X) β) := by
  refine ⟨BM.ext fun x => ?_, fun h hh x => ?_, fun u _ v _ huv x => ?_, 1, one_pos, β, hβ0, hβ1,
    fun u _ v _ => ?_⟩
  · change β * (⨆ x, (0 : ℝ)) = 0
    rcases isEmpty_or_nonempty X with hX | hX
    · simp
    · simp
  · exact mul_nonneg hβ0 (Real.iSup_nonneg fun x => hh x)
  · change β * (⨆ x, u.toFun x) ≤ β * ⨆ x, v.toFun x
    refine mul_le_mul_of_nonneg_left ?_ hβ0
    rcases isEmpty_or_nonempty X with hX | hX
    · simp
    · exact ciSup_le fun x => (huv x).trans (le_ciSup ⟨‖v‖, by
        rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm v y)⟩ x)
  · refine BM.norm_le (mul_nonneg hβ0 (norm_nonneg _)) fun x => ?_
    change |β * (⨆ x, u.toFun x) - β * ⨆ x, v.toFun x| ≤ β * ‖u - v‖
    rw [← mul_sub, abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (abs_iSup_sub_le u v) hβ0

theorem K_le_Dsup (Γ : X → Set A) (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hσ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x)
    (σ : (ofMDP Γ r hβ0 P hσ).Policy) (h : BM X) : (ofMDP Γ r hβ0 P hσ).K σ h ≤ Dsup β h :=
  fun x => by
    rw [LDP.K_apply]
    change β * _ ≤ β * ⨆ x, h.toFun x
    refine mul_le_mul_of_nonneg_left ?_ hβ0
    have hb : BddAbove (range h.toFun) :=
      ⟨‖h‖, by rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm h y)⟩
    calc ∫ x', h.toFun x' ∂(P (x, σ.1 x)) ≤ ∫ _, (⨆ y, h.toFun y) ∂(P (x, σ.1 x)) :=
          integral_mono (Integrable.of_bound h.measurable'.aestronglyMeasurable ‖h‖
            (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm h y))
            (integrable_const _)
            fun y => le_ciSup hb y
      _ = ⨆ y, h.toFun y := by simp

variable [TopologicalSpace X] [TopologicalSpace A]

/-- **Proposition 6.1.7** (p. 198): under Assumption 6.1.1 (`Γ` with the maximum theorem, `r`
continuous on `G`), if `P` is weak Feller then (i) the fundamental optimality properties hold, (ii)
`v* ∈ bcX` and (iii) VFI converges geometrically on `bcX`; if `P` is strong Feller, OPI and HPI
converge. -/
theorem proposition_6_1_7 (Γ : X → Set A) (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hσ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x)
    (hB : HasMaxSelections Γ) (hr : ContinuousOn r.toFun {p | p.2 ∈ Γ p.1})
    (hP : ∀ h : BM X, Continuous h.toFun →
      ContinuousOn (fun p => ∫ x', h.toFun x' ∂(P p)) {p | p.2 ∈ Γ p.1}) :
    ∃ hw : (ofMDP Γ r hβ0 P hσ).adp.WellPosed, (ofMDP Γ r hβ0 P hσ).adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc X, (ofMDP Γ r hβ0 P hσ).adp.VFIGeometric (LDP.bc X) vstar ∧
        ((∀ h : BM X, ContinuousOn (fun p => ∫ x', h.toFun x' ∂(P p)) {p | p.2 ∈ Γ p.1}) →
          ∀ g, (ofMDP Γ r hβ0 P hσ).adp.IsSelector g →
            (ofMDP Γ r hβ0 P hσ).adp.OPIConverges g vstar ∧
              (ofMDP Γ r hβ0 P hσ).adp.HPIConverges hw g vstar) := by
  obtain ⟨hw, hFO, vstar, hv, hgeo, hconv⟩ := (ofMDP Γ r hβ0 P hσ).proposition_6_1_3 hB hr
    (fun h hc => continuousOn_const.mul (hP h hc)) (Dsup_isDiscountOperator hβ0 hβ1)
    fun σ h _ => K_le_Dsup Γ r hβ0 P hσ σ h
  exact ⟨hw, hFO, vstar, hv, hgeo, fun hS => hconv fun h => continuousOn_const.mul (hS h)⟩

end SargentStachurski.RecursiveDecisionProcesses
