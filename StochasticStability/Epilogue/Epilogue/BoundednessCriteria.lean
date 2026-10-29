/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.BoundedInProbability
import Epilogue.LinearTChains
import Epilogue.MaximalIrreducibility
import Epilogue.FellerModels
import Epilogue.ModelNonlinearModels
import Epilogue.NonEvanescence

/-!
# Establishing boundedness in probability (MT §12.5)

Meyn and Tweedie, §12.5, pp. 305–307, with Lemma D.5.3 (p. 559), on which the section rests.

**Moment criteria.**
* **Lemma D.5.3 (ii)** (`lemma_D_5_3_ii`): coercive `Vₓ` with `limsup_k E_x[Vₓ(Φₖ)] < ∞` for every
  `x` make the chain bounded in probability; `isBoundedInProbability_of_lintegral_le` is the case
  of one `V`.
* **Lemma D.5.3 (i)**, sufficiency (`isTightMeasureSet_range_of_lintegral_le`): a coercive `V` with
  `sup_n ∫ V dνₙ < ∞` makes `{νₙ}` tight.
* `lintegral_pow_le_of_drift` iterates `PV ≤ αV + β` to `PᵏV ≤ αᵏV + β Σ_{j<k} αʲ`;
  `isBoundedInProbability_of_drift`: with `α < 1` and a coercive `V`, the chain is bounded in
  probability (the argument after (12.34) and (12.36)).
* `isCoercive_nnnorm`: the norm of a proper space is coercive.

**§12.5.1, the linear state space model** (p. 305).
* `lintegral_enorm_lssMatrix_pow_le`: `E_x‖Φₖ‖ ≤ ‖Fᵏx‖ + Σ_{j<k} C rʲ E‖GW‖` when
  `‖Fᵏx‖ ≤ C rᵏ‖x‖`; `lintegral_enorm_mulVec_ne_top`: `E‖W‖ < ∞ ⇒ E‖GW‖ < ∞`.
* **Proposition 12.5.1**: under (LSS5) the model is bounded in probability
  (`proposition_12_5_1_i`); with (LSS4) and (LCM3) as well it is positive Harris
  (`proposition_12_5_1_ii`).

**§12.5.2, the bilinear model** (p. 306).
* `bilinear_isBoundedInProbability`: (12.36)–(12.37), `E|θ + bW| < 1` and `E|W| < ∞` make the
  simple bilinear model bounded in probability.

**§12.5.3, the adaptive control model** (p. 307).
* (12.40) `sac_identity_12_40`; `lintegral_sacKernel_sigma_mul_sq`: one step,
  `E[Σ₁Y₁² | Φ₀] = Σ'(θ̃²Y² + σ_w²)`; `sacKernel_pow_comp_compl`: every `μPᵏ` lives on
  `[σ_z², σ_z²/(1 − α²)] × ℝ²`; `sac_moment_step_12_40`: the moment step from (12.40).
* (12.41) `sac_moment_bound_12_41`.
* **Proposition 12.5.2**: `proposition_12_5_2` gives `sup_k E|Φₖ|² < ∞`, and
  `proposition_12_5_2_tight` gives tightness of the laws of `Φₖ`.

**Hypotheses and method.**
* Proposition 12.5.1 uses only a finite mean `E‖W‖ < ∞`; (LSS2) also asks for a finite
  variance. The proof uses `V(x) = ‖x‖` and the closed form of `Φₖ`, not the quadratic form
  `|x − m|²_M` of (12.32). For the positive Harris part, Theorem 11.3.11 is replaced by Chapter 6,
  9 and 12 results: Proposition 6.3.5 (a `ψ`-irreducible T-chain), Theorem 9.2.2 (a non-evanescent
  T-chain is Harris), Proposition 12.1.1 and Theorem 12.1.2 (an invariant probability for a weak
  Feller chain that is bounded in probability).
* Proposition 12.5.2. (12.38) is a statement about the conditional law of `θ̃ₖ` given the
  observations, and it is not a property of the Markov kernel. It enters as the hypothesis
  `hcond`: `E[g(Σₖ, Yₖ) θ̃ₖ²] = E[g(Σₖ, Yₖ) Σₖ]` for every measurable `g ≥ 0`. This follows from
  (12.38) because `Σₖ` and `Yₖ` are `Yᵏ`-measurable, and it is all that (12.39)–(12.41) use.
  We also assume `E W = 0`, `E W² = σ_w²`, `σ_z ≠ 0`, `σ_w ≠ 0`, an initial law on the
  invariant `Σ`-interval, and `E Y₀² < ∞`. The Gaussian form of (SAC2) is not needed.
* `AdaptiveControlStability` completes the proposition. It derives `hcond` from the Kalman
  filter for the Gaussian model (SAC1)–(SAC2) (`proposition_12_5_2_kalman`), and proves the final
  step "hence `Φ` is positive recurrent" on the restricted state space
  (`proposition_12_5_2_positive`). On all of `ℝ³` the step map is not continuous where
  `ΣY² + σ_w² = 0`.
* `TightnessCriteria` proves the necessity half of Lemma D.5.3 (i).
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set Topology
open Metric
open scoped ENNReal NNReal Matrix

variable {X : Type*} [MeasurableSpace X]

/-! ### Moment bounds and boundedness in probability -/

variable [TopologicalSpace X] in
/-- **Lemma D.5.3 (ii)** (MT p. 559, used on pp. 306–307): if for each `x` there is a coercive
`Vₓ` with `E_x[Vₓ(Φₖ)] ≤ Mₓ` for all large `k` (that is, `limsup_k E_x[Vₓ(Φₖ)] < ∞`), the chain
is bounded in probability (Markov's inequality on the precompact sublevel sets of `Vₓ`). -/
theorem lemma_D_5_3_ii {P : Kernel X X} [IsMarkovKernel P]
    (h : ∀ x, ∃ V : X → ℝ≥0, Measurable V ∧ IsCoercive V ∧
      ∃ M : ℝ≥0, ∀ᶠ k in atTop, ∫⁻ y, (V y : ℝ≥0∞) ∂(P ^ k) x ≤ M) :
    IsBoundedInProbability P := by
  have := isMarkovKernel_pow P
  intro x ε hε
  obtain ⟨V, hVm, hV, M, hM⟩ := h x
  rcases le_or_gt 1 ε with hε1 | hε1
  · exact ⟨∅, isCompact_empty, by rw [tsub_eq_zero_of_le hε1]; exact zero_le⟩
  set e : ℝ≥0 := ε.toNNReal
  have he : (e : ℝ≥0∞) = ε := ENNReal.coe_toNNReal (ne_top_of_lt hε1)
  have he0 : 0 < e := by rw [← ENNReal.coe_pos, he]; exact hε
  set r : ℝ≥0 := M / e + 1
  have hr : (0 : ℝ≥0∞) < r := by positivity
  have hMr : (M : ℝ≥0∞) / r ≤ ε := by
    rw [ENNReal.div_le_iff hr.ne' ENNReal.coe_ne_top, ← he, ← ENNReal.coe_mul,
      ENNReal.coe_le_coe]
    calc M = e * (M / e) := by field_simp
      _ ≤ e * r := by gcongr; exact le_self_add
  refine ⟨closure {y | V y ≤ r}, hV r, le_liminf_of_le (by isBoundedDefault) ?_⟩
  filter_upwards [hM] with k hk
  have hmk : (P ^ k) x {y | (r : ℝ≥0∞) ≤ V y} ≤ (M : ℝ≥0∞) / r :=
    (meas_ge_le_lintegral_div hVm.coe_nnreal_ennreal.aemeasurable hr.ne'
      ENNReal.coe_ne_top).trans (by gcongr)
  have hm : MeasurableSet {y | (r : ℝ≥0∞) ≤ V y} :=
    measurableSet_le measurable_const hVm.coe_nnreal_ennreal
  have hsub : {y | (r : ℝ≥0∞) ≤ V y}ᶜ ⊆ closure {y | V y ≤ r} := fun y hy => by
    simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hy
    exact subset_closure (show V y ≤ r from by exact_mod_cast hy.le)
  calc 1 - ε ≤ 1 - (P ^ k) x {y | (r : ℝ≥0∞) ≤ V y} := tsub_le_tsub_left (hmk.trans hMr) 1
    _ = (P ^ k) x {y | (r : ℝ≥0∞) ≤ V y}ᶜ := (prob_compl_eq_one_sub hm).symm
    _ ≤ (P ^ k) x (closure {y | V y ≤ r}) := measure_mono hsub

variable [TopologicalSpace X] in
/-- Lemma D.5.3 (ii) with one coercive `V` for all initial states. -/
theorem isBoundedInProbability_of_lintegral_le {P : Kernel X X} [IsMarkovKernel P]
    {V : X → ℝ≥0} (hVm : Measurable V) (hV : IsCoercive V)
    (h : ∀ x, ∃ M : ℝ≥0, ∀ᶠ k in atTop, ∫⁻ y, (V y : ℝ≥0∞) ∂(P ^ k) x ≤ M) :
    IsBoundedInProbability P :=
  lemma_D_5_3_ii fun x => ⟨V, hVm, hV, h x⟩

/-- **Iterating a geometric drift**: if `∫ V dP(x) ≤ αV(x) + β`, then
`E_x[V(Φₖ)] ≤ αᵏV(x) + β Σ_{j<k} αʲ`. -/
theorem lintegral_pow_le_of_drift {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0∞}
    (hVm : Measurable V) {α β : ℝ≥0∞} (hdrift : ∀ x, ∫⁻ y, V y ∂P x ≤ α * V x + β) (k : ℕ)
    (x : X) : ∫⁻ y, V y ∂(P ^ k) x ≤ α ^ k * V x + β * ∑ j ∈ Finset.range k, α ^ j := by
  induction k generalizing x with
  | zero => rw [pow_zero_apply, lintegral_dirac' _ hVm]; simp
  | succ k ih =>
    have := isMarkovKernel_pow P k
    rw [Kernel.pow_add, pow_one, Kernel.lintegral_comp _ _ _ hVm]
    calc ∫⁻ y, ∫⁻ z, V z ∂(P ^ k) y ∂P x
        ≤ ∫⁻ y, (α ^ k * V y + β * ∑ j ∈ Finset.range k, α ^ j) ∂P x := lintegral_mono ih
      _ = α ^ k * ∫⁻ y, V y ∂P x + β * ∑ j ∈ Finset.range k, α ^ j := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hVm]; simp
      _ ≤ α ^ k * (α * V x + β) + β * ∑ j ∈ Finset.range k, α ^ j := by gcongr; exact hdrift x
      _ = α ^ (k + 1) * V x + β * ∑ j ∈ Finset.range (k + 1), α ^ j := by
          rw [Finset.sum_range_succ, pow_succ]; ring

/-- **A geometric drift makes the chain bounded in probability** (the remark after (12.34) and
(12.36)): if `V` is coercive and `∫ V dP(x) ≤ αV(x) + β` with `α < 1` and `β < ∞`, then
`sup_k E_x[V(Φₖ)] ≤ V(x) + β/(1 − α)`, so the chain is bounded in probability. -/
theorem isBoundedInProbability_of_drift [TopologicalSpace X]
    {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0} (hVm : Measurable V) (hV : IsCoercive V)
    {α β : ℝ≥0∞} (hα : α < 1) (hβ : β ≠ ∞)
    (hdrift : ∀ x, ∫⁻ y, (V y : ℝ≥0∞) ∂P x ≤ α * V x + β) : IsBoundedInProbability P := by
  refine isBoundedInProbability_of_lintegral_le hVm hV fun x => ?_
  have hgeo : ∑' j, α ^ j = (1 - α)⁻¹ := ENNReal.tsum_geometric α
  have hfin : (V x : ℝ≥0∞) + β * (1 - α)⁻¹ ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.mul_ne_top hβ
      (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hα).ne')⟩
  refine ⟨((V x : ℝ≥0∞) + β * (1 - α)⁻¹).toNNReal, Eventually.of_forall fun k => ?_⟩
  rw [ENNReal.coe_toNNReal hfin]
  calc ∫⁻ y, (V y : ℝ≥0∞) ∂(P ^ k) x ≤ α ^ k * V x + β * ∑ j ∈ Finset.range k, α ^ j :=
        lintegral_pow_le_of_drift hVm.coe_nnreal_ennreal hdrift k x
    _ ≤ V x + β * (1 - α)⁻¹ := by
        gcongr
        · exact mul_le_of_le_one_left' (pow_le_one₀ zero_le hα.le)
        · rw [← hgeo]; exact ENNReal.sum_le_tsum _

/-- The norm is coercive on a proper space: its sublevel sets are closed balls. -/
theorem isCoercive_nnnorm {E : Type*} [NormedAddCommGroup E] [ProperSpace E] :
    IsCoercive fun x : E => ‖x‖₊ := fun r =>
  (isCompact_closedBall (0 : E) r).of_isClosed_subset isClosed_closure
    (closure_minimal (fun x hx => by
      rw [mem_closedBall_zero_iff]
      exact NNReal.coe_le_coe.2 hx) isClosed_closedBall)

/-! ### The linear state space model -/

/-- **The first moment of the LSS(F, G) model** (the proof of Proposition 12.5.1, MT p. 305, with
the closed form of p. 9): if `‖Fᵏx‖ ≤ C rᵏ ‖x‖`, then
`E_x‖Φₖ‖ ≤ ‖Fᵏx‖ + C E‖GW‖ Σ_{j<k} rʲ`. -/
theorem lintegral_enorm_lssMatrix_pow_le {n p : ℕ} (Γ : Measure (Fin p → ℝ))
    [IsProbabilityMeasure Γ] (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    {C r : ℝ} (hr : 0 ≤ r) (hgeo : ∀ (k : ℕ) (x : Fin n → ℝ), ‖(F ^ k) *ᵥ x‖ ≤ C * r ^ k * ‖x‖)
    (k : ℕ) (x : Fin n → ℝ) :
    ∫⁻ y, ‖y‖ₑ ∂(lssMatrixKernel Γ F G ^ k) x ≤ ‖(F ^ k) *ᵥ x‖ₑ +
      ∑ j ∈ Finset.range k, ENNReal.ofReal (C * r ^ j) * ∫⁻ w, ‖G *ᵥ w‖ₑ ∂Γ := by
  have hmv : ∀ (M : Matrix (Fin n) (Fin p) ℝ), Measurable fun w : Fin p → ℝ => ‖M *ᵥ w‖ₑ :=
    fun M => measurable_enorm.comp (measurable_mulVec M)
  have hmeas : Measurable fun u : Fin k → Fin p → ℝ =>
      (F ^ k) *ᵥ x + ∑ i : Fin k, (F ^ (k - 1 - i) * G) *ᵥ u i :=
    (continuous_const.add (continuous_finsetSum _ fun i _ =>
      continuous_const.matrix_mulVec (continuous_apply i))).measurable
  have hj : ∀ j : ℕ, ∫⁻ w, ‖(F ^ j * G) *ᵥ w‖ₑ ∂Γ ≤
      ENNReal.ofReal (C * r ^ j) * ∫⁻ w, ‖G *ᵥ w‖ₑ ∂Γ := fun j => by
    rw [← lintegral_const_mul _ (hmv G)]
    refine lintegral_mono fun w => ?_
    rw [← Matrix.mulVec_mulVec, ← ofReal_norm, ← ofReal_norm]
    by_cases hC : 0 ≤ C
    · rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hgeo j _)
    · have h0 : ‖(F ^ j) *ᵥ (G *ᵥ w)‖ ≤ 0 :=
        (hgeo j _).trans (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (not_le.1 hC).le (by positivity)) (norm_nonneg _))
      rw [ENNReal.ofReal_of_nonpos h0]
      exact zero_le
  rw [lssMatrixKernel_pow_apply, lintegral_map measurable_enorm hmeas]
  calc ∫⁻ u, ‖(F ^ k) *ᵥ x + ∑ i : Fin k, (F ^ (k - 1 - i) * G) *ᵥ u i‖ₑ
          ∂(Measure.pi fun _ : Fin k => Γ)
      ≤ ∫⁻ u, (‖(F ^ k) *ᵥ x‖ₑ + ∑ i : Fin k, ‖(F ^ (k - 1 - i) * G) *ᵥ u i‖ₑ)
          ∂(Measure.pi fun _ : Fin k => Γ) := by
        refine lintegral_mono fun u => (enorm_add_le _ _).trans ?_
        gcongr
        exact enorm_sum_le _ _
    _ = ‖(F ^ k) *ᵥ x‖ₑ + ∑ i : Fin k, ∫⁻ w, ‖(F ^ (k - 1 - i) * G) *ᵥ w‖ₑ ∂Γ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_finsetSum (f := fun (i : Fin k) (u : Fin k → Fin p → ℝ) =>
            ‖(F ^ (k - 1 - (i : ℕ)) * G) *ᵥ u i‖ₑ) _ fun i _ =>
            (hmv (F ^ (k - 1 - (i : ℕ)) * G)).comp (measurable_pi_apply i)]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (measurePreserving_eval (fun _ : Fin k => Γ) i).lintegral_comp (hmv _)
    _ ≤ ‖(F ^ k) *ᵥ x‖ₑ + ∑ i : Fin k,
          ENNReal.ofReal (C * r ^ (k - 1 - (i : ℕ))) * ∫⁻ w, ‖G *ᵥ w‖ₑ ∂Γ := by
        gcongr with i
        exact hj _
    _ = _ := by
        rw [Fin.sum_univ_eq_sum_range
          (fun i => ENNReal.ofReal (C * r ^ (k - 1 - i)) * ∫⁻ w, ‖G *ᵥ w‖ₑ ∂Γ) k,
          Finset.sum_range_reflect (fun j => ENNReal.ofReal (C * r ^ j) * ∫⁻ w, ‖G *ᵥ w‖ₑ ∂Γ) k]

/-- A finite mean of `W` gives a finite mean of `GW`. -/
theorem lintegral_enorm_mulVec_ne_top {n p : ℕ} {Γ : Measure (Fin p → ℝ)}
    (G : Matrix (Fin n) (Fin p) ℝ) (hΓ : ∫⁻ w, ‖w‖ₑ ∂Γ ≠ ∞) : ∫⁻ w, ‖G *ᵥ w‖ₑ ∂Γ ≠ ∞ := by
  let L : (Fin p → ℝ) →L[ℝ] (Fin n → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin G)
  have hL : ∀ w, ‖G *ᵥ w‖ₑ ≤ ‖L‖ₑ * ‖w‖ₑ := fun w => L.le_opENorm w
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hL)
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  exact ENNReal.mul_ne_top enorm_ne_top hΓ

/-- **Proposition 12.5.1, first part** (MT p. 305): under the eigenvalue condition (LSS5), the
linear state space model is bounded in probability. Only a finite mean of `W` is used (the book's
(LSS2) also asks for a finite variance); the proof uses `V(x) = ‖x‖` and the closed form, in place
of the book's quadratic Lyapunov function. -/
theorem proposition_12_5_1_i {n p : ℕ} (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} (G : Matrix (Fin n) (Fin p) ℝ) (hF : IsStableMatrix F)
    (hΓ : ∫⁻ w, ‖w‖ₑ ∂Γ ≠ ∞) : IsBoundedInProbability (lssMatrixKernel Γ F G) := by
  have := isMarkovKernel_lssMatrixKernel Γ F G
  obtain ⟨C, r, hC, hr0, hr1, hgeo⟩ := isStableMatrix_geometric hF
  have hm := lintegral_enorm_mulVec_ne_top G hΓ
  refine isBoundedInProbability_of_lintegral_le (V := fun x => ‖x‖₊) measurable_nnnorm
    isCoercive_nnnorm fun x => ?_
  set m := ∫⁻ w, ‖G *ᵥ w‖ₑ ∂Γ
  set B : ℝ≥0∞ := ENNReal.ofReal (C * ‖x‖) + ENNReal.ofReal C * ENNReal.ofReal (1 - r)⁻¹ * m
  have hB : B ≠ ∞ := by finiteness
  refine ⟨B.toNNReal, Eventually.of_forall fun k => ?_⟩
  rw [ENNReal.coe_toNNReal hB]
  have hsum : ∑ j ∈ Finset.range k, ENNReal.ofReal (C * r ^ j) ≤
      ENNReal.ofReal C * ENNReal.ofReal (1 - r)⁻¹ := by
    rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.mul_sum]
    gcongr
    exact (sum_le_hasSum _ (fun j _ => by positivity)
      (hasSum_geometric_of_lt_one hr0.le hr1))
  calc ∫⁻ y, ((fun x : Fin n → ℝ => ‖x‖₊) y : ℝ≥0∞) ∂(lssMatrixKernel Γ F G ^ k) x
      = ∫⁻ y, ‖y‖ₑ ∂(lssMatrixKernel Γ F G ^ k) x := rfl
    _ ≤ ‖(F ^ k) *ᵥ x‖ₑ + ∑ j ∈ Finset.range k, ENNReal.ofReal (C * r ^ j) * m :=
        lintegral_enorm_lssMatrix_pow_le Γ F G hr0.le hgeo k x
    _ ≤ ENNReal.ofReal (C * ‖x‖) + ENNReal.ofReal C * ENNReal.ofReal (1 - r)⁻¹ * m := by
        rw [← Finset.sum_mul]
        gcongr
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ((hgeo k x).trans ?_)
        have h1 : r ^ k ≤ 1 := pow_le_one₀ hr0.le hr1.le
        nlinarith [mul_nonneg (mul_nonneg hC (norm_nonneg x)) (sub_nonneg.2 h1)]

/-- **Proposition 12.5.1, second part** (MT p. 305): under (LSS4), (LSS5) and the
controllability condition (LCM3), the linear state space model is positive Harris. Instead of
the book's appeal to Theorem 11.3.11, the proof combines Proposition 6.3.5 (a `ψ`-irreducible
T-chain), Theorem 9.2.2 (non-evanescent T-chains are Harris) and Theorem 12.1.2 (the weak Feller
chain, bounded in probability, has an invariant probability). -/
theorem proposition_12_5_1_ii {n p : ℕ} (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G)
    (hns : ¬ Γ ⟂ₘ volume) (hF : IsStableMatrix F) (hΓ : ∫⁻ w, ‖w‖ₑ ∂Γ ≠ ∞) :
    ∃ _ : IsMarkovKernel (lssMatrixKernel Γ F G), ∃ ψ : Measure (Fin n → ℝ),
      IsPositiveHarris (lssMatrixKernel Γ F G) ψ := by
  obtain ⟨hM, ⟨φ, hφ0, hφ⟩, hT, -⟩ := proposition_6_3_5 Γ hc hns hF
  refine ⟨hM, ?_⟩
  obtain ⟨φ₀, -, -, -, hmax⟩ := proposition_4_2_2_maximal _ hφ hφ0
  have hb := (proposition_12_5_1_i Γ G hF hΓ).onAverage
  have hWF : IsWeakFeller (lssMatrixKernel Γ F G) :=
    isWeakFeller_recursionKernel Γ (measurable_lssMatrixStep F G) fun w =>
      show Continuous fun x => F *ᵥ x + G *ᵥ w from
        (continuous_const.matrix_mulVec continuous_id).add continuous_const
  refine ⟨_, (theorem_9_2_2_ii hmax hT).2 (proposition_12_1_1 hb), hmax,
    theorem_12_1_2_ii hWF hb⟩

/-- **Lemma D.5.3 (i)**, the sufficiency half (MT p. 559, used on p. 307), with a uniform bound:
if `V` is coercive and `sup_n ∫ V dνₙ < ∞`, the sequence `νₙ` is tight. -/
theorem isTightMeasureSet_range_of_lintegral_le [TopologicalSpace X] (ν : ℕ → Measure X)
    {V : X → ℝ≥0} (hVm : Measurable V) (hV : IsCoercive V) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (h : ∀ n, ∫⁻ y, (V y : ℝ≥0∞) ∂ν n ≤ M) : IsTightMeasureSet (range ν) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεt
  · exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
  set e : ℝ≥0 := ε.toNNReal
  have he : (e : ℝ≥0∞) = ε := ENNReal.coe_toNNReal hεt
  have he0 : 0 < e := by rw [← ENNReal.coe_pos, he]; exact hε
  set r : ℝ≥0 := M.toNNReal / e + 1
  have hr : (0 : ℝ≥0∞) < r := by positivity
  have hMr : M / r ≤ ε := by
    rw [ENNReal.div_le_iff hr.ne' ENNReal.coe_ne_top, ← ENNReal.coe_toNNReal hM, ← he,
      ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    calc M.toNNReal = e * (M.toNNReal / e) := by field_simp
      _ ≤ e * r := by gcongr; exact le_self_add
  refine ⟨closure {y | V y ≤ r}, hV r, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hsub : (closure {y | V y ≤ r})ᶜ ⊆ {y | (r : ℝ≥0∞) ≤ V y} := fun y hy => by
    have : ¬ V y ≤ r := fun h' => hy (subset_closure h')
    simp only [mem_ofPred_eq]
    exact_mod_cast (not_le.1 this).le
  calc ν n (closure {y | V y ≤ r})ᶜ ≤ ν n {y | (r : ℝ≥0∞) ≤ V y} := measure_mono hsub
    _ ≤ (∫⁻ y, (V y : ℝ≥0∞) ∂ν n) / r :=
        meas_ge_le_lintegral_div hVm.coe_nnreal_ennreal.aemeasurable hr.ne' ENNReal.coe_ne_top
    _ ≤ M / r := by gcongr; exact h n
    _ ≤ ε := hMr

/-! ### The bilinear model -/

/-- **The bilinear model is bounded in probability** (MT §12.5.2, (12.36)–(12.37), p. 306): if
`E|θ + bW| < 1` and `E|W| < ∞`, then `E[|Φₖ₊₁| | Φₖ = x] ≤ E|θ + bW| |x| + E|W|`, and the
simple bilinear model is bounded in probability. -/
theorem bilinear_isBoundedInProbability (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (θ b : ℝ)
    (h37 : ∫⁻ w, ‖θ + b * w‖ₑ ∂Γ < 1) (hW : ∫⁻ w, ‖w‖ₑ ∂Γ ≠ ∞) :
    IsBoundedInProbability (bilinearKernel Γ θ b) := by
  have := isMarkovKernel_bilinearKernel Γ θ b
  refine isBoundedInProbability_of_drift (V := fun x => ‖x‖₊) measurable_nnnorm
    isCoercive_nnnorm h37 hW fun x => ?_
  have hm := (contDiff_bilinearStep θ b).continuous.measurable
  calc ∫⁻ y, ((fun x : ℝ => ‖x‖₊) y : ℝ≥0∞) ∂bilinearKernel Γ θ b x
      = ∫⁻ w, ‖bilinearStep θ b (x, w)‖ₑ ∂Γ := by
        rw [bilinearKernel, recursionKernel_apply Γ hm]
        exact lintegral_map measurable_nnnorm.coe_nnreal_ennreal
          (show Measurable fun w => bilinearStep θ b (x, w) from hm.comp measurable_prodMk_left)
    _ ≤ ∫⁻ w, (‖θ + b * w‖ₑ * ‖x‖ₑ + ‖w‖ₑ) ∂Γ := lintegral_mono fun w => by
        rw [bilinearStep_eq, ← enorm_mul]
        exact enorm_add_le _ _
    _ = (∫⁻ w, ‖θ + b * w‖ₑ ∂Γ) * ‖x‖₊ + ∫⁻ w, ‖w‖ₑ ∂Γ := by
        rw [lintegral_add_right _ measurable_enorm, lintegral_mul_const _ (by fun_prop)]
        rfl

/-! ### The adaptive control model -/

/-- **The identity (12.40)** (MT p. 307): with `Σ' = σ_z² + α²σ_w²Σ(ΣY² + σ_w²)⁻¹` (2.24),
`Σ'(ΣY² + σ_w²) = σ_z²ΣY² + σ_w²σ_z² + α²σ_w²Σ`. -/
theorem sac_identity_12_40 {α σz σw S Y : ℝ} (hD : S * Y ^ 2 + σw ^ 2 ≠ 0) :
    (σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * Y ^ 2 + σw ^ 2)) * (S * Y ^ 2 + σw ^ 2) =
      σz ^ 2 * (S * Y ^ 2) + σw ^ 2 * σz ^ 2 + α ^ 2 * σw ^ 2 * S := by
  field_simp

/-- One step of the adaptive control model: if `E W = 0` and `E W² = σ_w²`, then from
`(Σ, θ̃, Y)`, `E[Σ₁Y₁²] = Σ'(θ̃²Y² + σ_w²)` (the conditional form of (12.39) before the
estimation error is averaged out). -/
theorem lintegral_sacKernel_sigma_mul_sq (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ]
    {α σz σw : ℝ} (hW1 : Integrable (fun z : ℝ × ℝ => z.2) Γ)
    (hW2 : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) Γ) (hm : ∫ z, z.2 ∂Γ = 0)
    (hv : ∫ z, z.2 ^ 2 ∂Γ = σw ^ 2) {S t y : ℝ}
    (hS : 0 ≤ σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * y ^ 2 + σw ^ 2)) :
    ∫⁻ ψ, ENNReal.ofReal (ψ.1 * ψ.2.2 ^ 2) ∂sacKernel Γ α σz σw (S, t, y) =
      ENNReal.ofReal (σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * y ^ 2 + σw ^ 2)) *
        ENNReal.ofReal (t ^ 2 * y ^ 2 + σw ^ 2) := by
  have hmf : Measurable fun ψ : ℝ × ℝ × ℝ => ENNReal.ofReal (ψ.1 * ψ.2.2 ^ 2) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [sacKernel, recursionKernel_apply Γ (measurable_sacStep α σz σw),
    lintegral_map hmf (show Measurable fun w => sacStep α σz σw ((S, t, y), w) from
      (measurable_sacStep α σz σw).comp measurable_prodMk_left)]
  have hexp : (fun z : ℝ × ℝ => (t * y + z.2) ^ 2) =
      fun z => (t * y) ^ 2 + 2 * (t * y) * z.2 + z.2 ^ 2 := by
    funext z
    ring
  have hint1 : Integrable (fun z : ℝ × ℝ => (t * y) ^ 2 + 2 * (t * y) * z.2) Γ :=
    (integrable_const _).add (hW1.const_mul _)
  have hint : Integrable (fun z : ℝ × ℝ => (t * y + z.2) ^ 2) Γ := by
    rw [hexp]
    exact hint1.add hW2
  have hI : ∫ z, (t * y + z.2) ^ 2 ∂Γ = t ^ 2 * y ^ 2 + σw ^ 2 := by
    rw [hexp, integral_add hint1 hW2, integral_add (integrable_const _) (hW1.const_mul _),
      integral_const, integral_const_mul, hm, hv]
    simp only [smul_eq_mul, probReal_univ, mul_zero, add_zero]
    ring
  calc ∫⁻ z, ENNReal.ofReal ((sacStep α σz σw ((S, t, y), z)).1 *
          (sacStep α σz σw ((S, t, y), z)).2.2 ^ 2) ∂Γ
      = ∫⁻ z, ENNReal.ofReal (σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * y ^ 2 + σw ^ 2)) *
          ENNReal.ofReal ((t * y + z.2) ^ 2) ∂Γ := by
        refine lintegral_congr fun z => ?_
        simp only [sacStep]
        rw [ENNReal.ofReal_mul hS]
    _ = _ := by
        rw [lintegral_const_mul _ (f := fun z : ℝ × ℝ => ENNReal.ofReal ((t * y + z.2) ^ 2))
          (by fun_prop),
          ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => sq_nonneg _), hI]

/-- MT p. 36: from initial laws on `X = [σ_z², σ_z²/(1 − α²)] × ℝ²`, every law `μPᵏ` of the
adaptive control chain lives on `X`. -/
theorem sacKernel_pow_comp_compl (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {α σz σw : ℝ}
    (hα : |α| < 1) (hσw : σw ≠ 0) (μ : Measure (ℝ × ℝ × ℝ))
    (hμ : μ (Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ)ᶜ = 0) (k : ℕ) :
    ((sacKernel Γ α σz σw ^ k) ∘ₘ μ) (Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ)ᶜ = 0 := by
  set A : Set (ℝ × ℝ × ℝ) := Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ
  set P := sacKernel Γ α σz σw
  have hA : MeasurableSet A := measurableSet_Icc.prod MeasurableSet.univ
  have := isMarkovKernel_sacKernel Γ α σz σw
  have hstep : ∀ x ∈ A, P x Aᶜ = 0 := by
    rintro ⟨S, t, y⟩ ⟨hS, -⟩
    rw [prob_compl_eq_zero_iff hA]
    exact sacKernel_apply_Icc Γ hα hσw hS
  have hpow : ∀ j : ℕ, ∀ x ∈ A, (P ^ j) x Aᶜ = 0 := by
    intro j
    induction j with
    | zero =>
      intro x hx
      rw [pow_zero_apply, Measure.dirac_apply' _ hA.compl,
        indicator_of_notMem (not_not.2 hx)]
    | succ j ih =>
      intro x hx
      rw [Kernel.pow_add, pow_one, Kernel.comp_apply' _ _ _ hA.compl]
      refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ hA.compl)).2 ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hstep x hx)] with y hy
      exact ih y (not_not.1 hy)
  rw [Measure.bind_apply hA.compl (Kernel.measurable _).aemeasurable]
  refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ hA.compl)).2 ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with x hx
  exact hpow k x (not_not.1 hx)

/-- **The moment step (12.40)** (MT p. 307). Suppose `E W = 0`, `E W² = σ_w²`, the initial law
lives on `[σ_z², σ_z²/(1 − α²)] × ℝ²`, and the estimation error satisfies the averaged form of
(12.38): `E[g(Σₖ, Yₖ) θ̃ₖ²] = E[g(Σₖ, Yₖ) Σₖ]` for every `g ≥ 0`. Then
`E[Σₖ₊₁Y²ₖ₊₁] ≤ σ_z² E[ΣₖYₖ²] + σ_w²σ_z² + α²σ_w² Σ̄`, with `Σ̄ = σ_z²/(1 − α²)`. -/
theorem sac_moment_step_12_40 (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {α σz σw : ℝ}
    (hα : |α| < 1) (hσw : σw ≠ 0) (hW1 : Integrable (fun z : ℝ × ℝ => z.2) Γ)
    (hW2 : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) Γ) (hm : ∫ z, z.2 ∂Γ = 0)
    (hv : ∫ z, z.2 ^ 2 ∂Γ = σw ^ 2) (μ : Measure (ℝ × ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ)ᶜ = 0) (k : ℕ)
    (hcond : ∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ φ, g (φ.1, φ.2.2) * ENNReal.ofReal (φ.2.1 ^ 2) ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ) =
        ∫⁻ φ, g (φ.1, φ.2.2) * ENNReal.ofReal φ.1 ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ)) :
    ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂((sacKernel Γ α σz σw ^ (k + 1)) ∘ₘ μ) ≤
      ENNReal.ofReal (σz ^ 2) *
          ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ) +
        ENNReal.ofReal (σw ^ 2 * σz ^ 2 + α ^ 2 * σw ^ 2 * (σz ^ 2 / (1 - α ^ 2))) := by
  set P := sacKernel Γ α σz σw
  set ν := (P ^ k) ∘ₘ μ
  set b := σz ^ 2 / (1 - α ^ 2)
  set c := σw ^ 2 * σz ^ 2 + α ^ 2 * σw ^ 2 * b
  have := isMarkovKernel_sacKernel Γ α σz σw
  have := isMarkovKernel_pow P k
  have hα2 : α ^ 2 < 1 := by
    have := sq_abs α
    nlinarith [abs_nonneg α]
  have hb0 : 0 ≤ b := div_nonneg (sq_nonneg _) (by linarith)
  have hc0 : 0 ≤ c := by positivity
  have hw2 : 0 < σw ^ 2 := by positivity
  have hsupp : ∀ᵐ φ ∂ν, φ ∈ Icc (σz ^ 2) b ×ˢ (univ : Set (ℝ × ℝ)) :=
    measure_eq_zero_iff_ae_notMem.1 (sacKernel_pow_comp_compl Γ hα hσw μ hμ k) |>.mono
      fun _ h => not_not.1 h
  set Sn : ℝ × ℝ → ℝ := fun q => σz ^ 2 + α ^ 2 * σw ^ 2 * q.1 / (q.1 * q.2 ^ 2 + σw ^ 2)
  have hSnm : Measurable Sn := by fun_prop
  set g : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (Sn q) * ENNReal.ofReal (q.2 ^ 2)
  set h : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (Sn q) * ENNReal.ofReal (σw ^ 2)
  have hg : Measurable g := by fun_prop
  have hh : Measurable h := by fun_prop
  have hpr : Measurable fun φ : ℝ × ℝ × ℝ => (φ.1, φ.2.2) := by fun_prop
  have hSn0 : ∀ φ ∈ Icc (σz ^ 2) b ×ˢ (univ : Set (ℝ × ℝ)), 0 ≤ Sn (φ.1, φ.2.2) := by
    rintro φ ⟨hS, -⟩
    have : 0 ≤ φ.1 := (sq_nonneg _).trans hS.1
    simp only [Sn]
    positivity
  have hν : (P ^ (k + 1)) ∘ₘ μ = P ∘ₘ ν := by
    rw [pow_succ']
    exact Measure.comp_assoc.symm
  have hfm : Measurable fun ψ : ℝ × ℝ × ℝ => ENNReal.ofReal (ψ.1 * ψ.2.2 ^ 2) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [hν, Measure.lintegral_bind (Kernel.measurable _).aemeasurable hfm.aemeasurable]
  calc ∫⁻ φ, ∫⁻ ψ, ENNReal.ofReal (ψ.1 * ψ.2.2 ^ 2) ∂P φ ∂ν
      = ∫⁻ φ, (g (φ.1, φ.2.2) * ENNReal.ofReal (φ.2.1 ^ 2) + h (φ.1, φ.2.2)) ∂ν := by
        refine lintegral_congr_ae ?_
        filter_upwards [hsupp] with φ hφ
        obtain ⟨S, t, y⟩ := φ
        rw [lintegral_sacKernel_sigma_mul_sq Γ hW1 hW2 hm hv (hSn0 _ hφ)]
        simp only [g, h]
        rw [show t ^ 2 * y ^ 2 + σw ^ 2 = y ^ 2 * t ^ 2 + σw ^ 2 by ring,
          ENNReal.ofReal_add (by positivity) hw2.le, ENNReal.ofReal_mul (sq_nonneg _)]
        ring
    _ = ∫⁻ φ, (g (φ.1, φ.2.2) * ENNReal.ofReal φ.1 + h (φ.1, φ.2.2)) ∂ν := by
        have hhm : Measurable fun φ : ℝ × ℝ × ℝ => h (φ.1, φ.2.2) := hh.comp hpr
        rw [lintegral_add_right _ hhm, lintegral_add_right _ hhm, hcond g hg]
    _ ≤ ∫⁻ φ, (ENNReal.ofReal (σz ^ 2) * ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) +
          ENNReal.ofReal c) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hsupp] with φ hφ
        obtain ⟨S, t, y⟩ := φ
        obtain ⟨hS, -⟩ := hφ
        have hS0 : 0 ≤ S := (sq_nonneg _).trans hS.1
        have hD : S * y ^ 2 + σw ^ 2 ≠ 0 := by positivity
        have hSn := hSn0 (S, t, y) ⟨hS, mem_univ _⟩
        simp only [g, h] at hSn ⊢
        rw [← ENNReal.ofReal_mul hSn, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hSn, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_add (by positivity) hc0]
        refine ENNReal.ofReal_le_ofReal ?_
        have h40 := sac_identity_12_40 (α := α) (σz := σz) hD
        have hb : α ^ 2 * σw ^ 2 * S ≤ α ^ 2 * σw ^ 2 * b :=
          mul_le_mul_of_nonneg_left hS.2 (by positivity)
        simp only [Sn]
        nlinarith
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hfm, lintegral_const,
          measure_univ, mul_one]

/-- `μP⁰ = μ`. -/
theorem pow_zero_comp {Y : Type*} [MeasurableSpace Y] (P : Kernel Y Y) (μ : Measure Y) :
    (P ^ (0 : ℕ)) ∘ₘ μ = μ := by
  rw [pow_zero]
  exact Measure.id_comp

/-- **The bound (12.41)** (MT p. 307): under the hypotheses of `sac_moment_step_12_40` at every
time, `E[ΣₖYₖ²] ≤ σ_z^{2k} E[Σ₀Y₀²] + (σ_w²σ_z² + α²σ_w² Σ̄) Σ_{j<k} σ_z^{2j}`, and the sum is at
most `(1 − σ_z²)⁻¹`. (The book bounds `E[Σₖ₊₁Y²ₖ₊₁]` with the factor `σ_z^{2k}`; the induction
gives `σ_z^{2(k+1)}`, which is smaller since `σ_z² < 1`.) -/
theorem sac_moment_bound_12_41 (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {α σz σw : ℝ}
    (hα : |α| < 1) (hσw : σw ≠ 0) (hW1 : Integrable (fun z : ℝ × ℝ => z.2) Γ)
    (hW2 : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) Γ) (hm : ∫ z, z.2 ∂Γ = 0)
    (hv : ∫ z, z.2 ^ 2 ∂Γ = σw ^ 2) (μ : Measure (ℝ × ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ)ᶜ = 0)
    (hcond : ∀ (k : ℕ) (g : ℝ × ℝ → ℝ≥0∞), Measurable g →
      ∫⁻ φ, g (φ.1, φ.2.2) * ENNReal.ofReal (φ.2.1 ^ 2) ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ) =
        ∫⁻ φ, g (φ.1, φ.2.2) * ENNReal.ofReal φ.1 ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ)) (k : ℕ) :
    ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ) ≤
      ENNReal.ofReal (σz ^ 2) ^ k * ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂μ +
        ENNReal.ofReal (σw ^ 2 * σz ^ 2 + α ^ 2 * σw ^ 2 * (σz ^ 2 / (1 - α ^ 2))) *
          ∑ j ∈ Finset.range k, ENNReal.ofReal (σz ^ 2) ^ j := by
  induction k with
  | zero => rw [pow_zero_comp]; simp
  | succ k ih =>
    refine (sac_moment_step_12_40 Γ hα hσw hW1 hW2 hm hv μ hμ k (hcond k)).trans ?_
    calc ENNReal.ofReal (σz ^ 2) *
          ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ) +
        ENNReal.ofReal (σw ^ 2 * σz ^ 2 + α ^ 2 * σw ^ 2 * (σz ^ 2 / (1 - α ^ 2)))
        ≤ ENNReal.ofReal (σz ^ 2) * (ENNReal.ofReal (σz ^ 2) ^ k *
            ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂μ +
            ENNReal.ofReal (σw ^ 2 * σz ^ 2 + α ^ 2 * σw ^ 2 * (σz ^ 2 / (1 - α ^ 2))) *
              ∑ j ∈ Finset.range k, ENNReal.ofReal (σz ^ 2) ^ j) +
          ENNReal.ofReal (σw ^ 2 * σz ^ 2 + α ^ 2 * σw ^ 2 * (σz ^ 2 / (1 - α ^ 2))) := by
          gcongr
      _ = _ := by
          rw [Finset.sum_range_succ', pow_zero, pow_succ']
          simp_rw [pow_succ']
          rw [← Finset.mul_sum]
          ring

/-- **Proposition 12.5.2** (MT p. 307), the moment bound. For the adaptive control model with
`|α| < 1`, `σ_z² < 1`, `σ_z, σ_w ≠ 0`, `E W = 0`, `E W² = σ_w²`, an initial law on
`[σ_z², σ_z²/(1 − α²)] × ℝ²` with `E Y₀² < ∞`, and the averaged form of (12.38) at every time
(`E[g(Σₖ, Yₖ) θ̃ₖ²] = E[g(Σₖ, Yₖ) Σₖ]` for every `g ≥ 0`, which (12.38) implies because `Σₖ` and
`Yₖ` are `Yᵏ`-measurable), `sup_k E|Φₖ|² < ∞`. -/
theorem proposition_12_5_2 (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {α σz σw : ℝ}
    (hα : |α| < 1) (hσw : σw ≠ 0) (hσz : σz ≠ 0) (hσz1 : σz ^ 2 < 1)
    (hW1 : Integrable (fun z : ℝ × ℝ => z.2) Γ)
    (hW2 : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) Γ) (hm : ∫ z, z.2 ∂Γ = 0)
    (hv : ∫ z, z.2 ^ 2 ∂Γ = σw ^ 2) (μ : Measure (ℝ × ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ)ᶜ = 0)
    (hY : ∫⁻ φ, ENNReal.ofReal (φ.2.2 ^ 2) ∂μ ≠ ∞)
    (hcond : ∀ (k : ℕ) (g : ℝ × ℝ → ℝ≥0∞), Measurable g →
      ∫⁻ φ, g (φ.1, φ.2.2) * ENNReal.ofReal (φ.2.1 ^ 2) ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ) =
        ∫⁻ φ, g (φ.1, φ.2.2) * ENNReal.ofReal φ.1 ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ)) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ k : ℕ, ∫⁻ φ, ENNReal.ofReal (φ.1 ^ 2 + φ.2.1 ^ 2 + φ.2.2 ^ 2)
      ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ) ≤ M := by
  set P := sacKernel Γ α σz σw
  set b := σz ^ 2 / (1 - α ^ 2)
  set c := σw ^ 2 * σz ^ 2 + α ^ 2 * σw ^ 2 * b
  set ρ := ENNReal.ofReal (σz ^ 2)
  have := isMarkovKernel_sacKernel Γ α σz σw
  have hα2 : α ^ 2 < 1 := by
    have := sq_abs α
    nlinarith [abs_nonneg α]
  have hb0 : 0 ≤ b := div_nonneg (sq_nonneg _) (by linarith)
  have hz2 : 0 < σz ^ 2 := by positivity
  have hρ : ρ < 1 := ENNReal.ofReal_lt_one.2 hσz1
  have hsupp : ∀ k : ℕ, ∀ᵐ φ ∂((P ^ k) ∘ₘ μ), φ ∈ Icc (σz ^ 2) b ×ˢ (univ : Set (ℝ × ℝ)) :=
    fun k => (measure_eq_zero_iff_ae_notMem.1 (sacKernel_pow_comp_compl Γ hα hσw μ hμ k)).mono
      fun _ h => not_not.1 h
  have hμsupp : ∀ᵐ φ ∂μ, φ ∈ Icc (σz ^ 2) b ×ˢ (univ : Set (ℝ × ℝ)) :=
    measure_eq_zero_iff_ae_notMem.1 hμ |>.mono fun _ h => not_not.1 h
  have hm3 : Measurable fun φ : ℝ × ℝ × ℝ => ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  set a0 := ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂μ
  have ha0 : a0 ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := b)) hY) ?_
    have hm4 : Measurable fun φ : ℝ × ℝ × ℝ => ENNReal.ofReal (φ.2.2 ^ 2) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    rw [← lintegral_const_mul _ hm4]
    refine lintegral_mono_ae ?_
    filter_upwards [hμsupp] with φ hφ
    rw [← ENNReal.ofReal_mul hb0]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hφ.1.2 (sq_nonneg _))
  set A := a0 + ENNReal.ofReal c * (1 - ρ)⁻¹
  have hA : A ≠ ∞ := by
    have : (1 - ρ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hρ).ne'
    finiteness
  have hak : ∀ k : ℕ, ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂((P ^ k) ∘ₘ μ) ≤ A := fun k => by
    refine (sac_moment_bound_12_41 Γ hα hσw hW1 hW2 hm hv μ hμ hcond k).trans ?_
    change ρ ^ k * a0 + ENNReal.ofReal c * ∑ j ∈ Finset.range k, ρ ^ j ≤
      a0 + ENNReal.ofReal c * (1 - ρ)⁻¹
    gcongr
    · exact mul_le_of_le_one_left' (pow_le_one₀ zero_le hρ.le)
    · rw [← ENNReal.tsum_geometric ρ]
      exact ENNReal.sum_le_tsum _
  refine ⟨ENNReal.ofReal (b ^ 2) + ENNReal.ofReal b + ENNReal.ofReal (σz ^ 2)⁻¹ * A,
    by finiteness, fun k => ?_⟩
  have := isMarkovKernel_pow P k
  set ν := (P ^ k) ∘ₘ μ
  have ht : ∫⁻ φ, ENNReal.ofReal (φ.2.1 ^ 2) ∂ν ≤ ENNReal.ofReal b := by
    have h1 := hcond k (fun _ => 1) measurable_const
    simp only [one_mul] at h1
    rw [h1]
    calc ∫⁻ φ, ENNReal.ofReal φ.1 ∂ν ≤ ∫⁻ _, ENNReal.ofReal b ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hsupp k] with φ hφ
          exact ENNReal.ofReal_le_ofReal hφ.1.2
      _ = ENNReal.ofReal b := by rw [lintegral_const, measure_univ, mul_one]
  have hm1 : Measurable fun φ : ℝ × ℝ × ℝ => ENNReal.ofReal (φ.2.1 ^ 2) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hm2 : Measurable fun φ : ℝ × ℝ × ℝ => ENNReal.ofReal (σz ^ 2)⁻¹ *
      ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  calc ∫⁻ φ, ENNReal.ofReal (φ.1 ^ 2 + φ.2.1 ^ 2 + φ.2.2 ^ 2) ∂ν
      ≤ ∫⁻ φ, (ENNReal.ofReal (b ^ 2) + ENNReal.ofReal (φ.2.1 ^ 2) +
          ENNReal.ofReal (σz ^ 2)⁻¹ * ENNReal.ofReal (φ.1 * φ.2.2 ^ 2)) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hsupp k] with φ hφ
        obtain ⟨S, t, y⟩ := φ
        obtain ⟨hS, -⟩ := hφ
        have hS0 : 0 ≤ S := hz2.le.trans hS.1
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hz2.le),
          ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hS2 : S ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hS0 hS.2 2
        have hy : y ^ 2 ≤ (σz ^ 2)⁻¹ * (S * y ^ 2) := by
          rw [le_inv_mul_iff₀ hz2]
          exact mul_le_mul_of_nonneg_right hS.1 (sq_nonneg _)
        simp only
        linarith
    _ = ENNReal.ofReal (b ^ 2) + ∫⁻ φ, ENNReal.ofReal (φ.2.1 ^ 2) ∂ν +
          ENNReal.ofReal (σz ^ 2)⁻¹ * ∫⁻ φ, ENNReal.ofReal (φ.1 * φ.2.2 ^ 2) ∂ν := by
        rw [lintegral_add_right _ hm2, lintegral_add_left measurable_const, lintegral_const,
          measure_univ, mul_one, lintegral_const_mul _ hm3]
    _ ≤ _ := by
        gcongr
        exact hak k

/-- **Proposition 12.5.2, tightness** (MT p. 307): under the hypotheses of `proposition_12_5_2`,
the laws `μPᵏ` of the adaptive control chain are tight. -/
theorem proposition_12_5_2_tight (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {α σz σw : ℝ}
    (hα : |α| < 1) (hσw : σw ≠ 0) (hσz : σz ≠ 0) (hσz1 : σz ^ 2 < 1)
    (hW1 : Integrable (fun z : ℝ × ℝ => z.2) Γ)
    (hW2 : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) Γ) (hm : ∫ z, z.2 ∂Γ = 0)
    (hv : ∫ z, z.2 ^ 2 ∂Γ = σw ^ 2) (μ : Measure (ℝ × ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ)ᶜ = 0)
    (hY : ∫⁻ φ, ENNReal.ofReal (φ.2.2 ^ 2) ∂μ ≠ ∞)
    (hcond : ∀ (k : ℕ) (g : ℝ × ℝ → ℝ≥0∞), Measurable g →
      ∫⁻ φ, g (φ.1, φ.2.2) * ENNReal.ofReal (φ.2.1 ^ 2) ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ) =
        ∫⁻ φ, g (φ.1, φ.2.2) * ENNReal.ofReal φ.1 ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ)) :
    IsTightMeasureSet (range fun k : ℕ => (sacKernel Γ α σz σw ^ k) ∘ₘ μ) := by
  obtain ⟨M, hM, hbd⟩ :=
    proposition_12_5_2 Γ hα hσw hσz hσz1 hW1 hW2 hm hv μ hμ hY hcond
  have := isMarkovKernel_sacKernel Γ α σz σw
  have habs : ∀ a : ℝ, |a| ≤ 1 + a ^ 2 := fun a => by nlinarith [sq_nonneg (|a| - 1), sq_abs a]
  refine isTightMeasureSet_range_of_lintegral_le _ (V := fun x => ‖x‖₊) measurable_nnnorm
    isCoercive_nnnorm (M := 1 + M) (by finiteness) fun k => ?_
  have := isMarkovKernel_pow (sacKernel Γ α σz σw) k
  calc ∫⁻ φ, ((fun x : ℝ × ℝ × ℝ => ‖x‖₊) φ : ℝ≥0∞) ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ)
      ≤ ∫⁻ φ, (1 + ENNReal.ofReal (φ.1 ^ 2 + φ.2.1 ^ 2 + φ.2.2 ^ 2))
          ∂((sacKernel Γ α σz σw ^ k) ∘ₘ μ) := by
        refine lintegral_mono fun φ => ?_
        obtain ⟨S, t, y⟩ := φ
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
        change ‖(S, t, y)‖ₑ ≤ _
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [Prod.norm_def, Real.norm_eq_abs]
        refine max_le ?_ (max_le ?_ ?_) <;>
          nlinarith [habs S, habs t, habs y, sq_nonneg S, sq_nonneg t, sq_nonneg y]
    _ ≤ 1 + M := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        gcongr
        exact hbd k

end MeynTweedie.Epilogue
