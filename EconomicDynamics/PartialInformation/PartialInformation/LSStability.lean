/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.LinearSystems
import PartialInformation.SSLQControl
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Stable matrices and asymptotic tools for Chapter 9

Copied from `EconomicDynamics/LinearQuadratic` (module `LSStability`), namespace renamed.

Miao, Chapter 9 (pp. 291–304) uses "stable matrix" in the sense of Definition 1.4.5 (p. 18):
every eigenvalue has modulus less than one. This module fixes that notion for real matrices
(`ls_Stable`) and collects the analytic facts the chapter's proofs use:

* `ls_stable_iff_tendsto`: `M` is stable iff `Mᵗv → 0` for every `v` (Chapter 1).
* `ls_stable_iff_specRad`: `M` is stable iff the Sargent–Stachurski spectral radius
  `ρ(M) < 1`, so the `SS` LQ results (stated with `ρ`) apply.
* `ls_tendsto_zero_of_le_rec`: `0 ≤ e_{t+1} ≤ re_t + δ_t`, `r < 1`, `δ_t → 0` give `e_t → 0`.
* `ls_tendsto_zero_of_stable_input`: `x_{t+1} = Mx_t + w_t` with `M` stable and `w_t → 0`
  gives `x_t → 0`.
* `ls_tendsto_of_quad`, `ls_exists_tendsto_of_quad`: convergence of symmetric matrices from
  convergence of their quadratic forms (polarization).
* `ls_posDef_coercive`, `ls_tendsto_zero_of_quad_posDef`: a positive definite form dominates
  `c‖x‖²`, so `x_t'Qx_t → 0` forces `x_t → 0`.
-/

open Filter Topology

namespace Miao.PartialInformation

open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Miao's stable matrix (Definition 1.4.5, p. 18), for a real matrix: every (complex)
eigenvalue has modulus less than one. -/
def ls_Stable (M : Matrix X X ℝ) : Prop := IsStableMatrix (M.map Complex.ofRealHom)

/-- A real matrix is stable iff all its orbits `Mᵗv` converge to zero (Chapter 1). -/
theorem ls_stable_iff_tendsto (M : Matrix X X ℝ) :
    ls_Stable M ↔ ∀ v : X → ℝ, Tendsto (fun t => (M ^ t) *ᵥ v) atTop (𝓝 0) :=
  isStableMatrix_iff_tendsto M

/-- `ρ(M) < 1` makes `M` stable. -/
theorem ls_stable_of_specRad [Nonempty X] {M : Matrix X X ℝ} (h : SS.specRad M < 1) :
    ls_Stable M := by
  rw [ls_stable_iff_tendsto]
  intro v
  obtain ⟨r, hr1, hr2⟩ := exists_between h
  have hr0 : 0 ≤ r := (SS.specRad_nonneg M).trans hr1.le
  have hent : ∀ i j, Tendsto (fun t => (M ^ t) i j) atTop (𝓝 0) := fun i j => by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      (SS.eventually_abs_entry_pow_le M hr1 i j) (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr2)
  rw [tendsto_pi_nhds]
  intro i
  simp only [mulVec, dotProduct, Pi.zero_apply]
  rw [show (0 : ℝ) = ∑ j, 0 * v j by simp]
  exact tendsto_finsetSum _ fun j _ => (hent i j).mul_const _

/-- A stable matrix has `ρ(M) < 1`: the spectral radius is attained by an eigenvalue. -/
theorem ls_specRad_lt_of_stable [Nonempty X] {M : Matrix X X ℝ} (h : ls_Stable M) :
    SS.specRad M < 1 := by
  let _ : NormedRing (Matrix X X ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix X X ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  obtain ⟨z, hz, hnorm⟩ := spectrum.exists_nnnorm_eq_spectralRadius (SS.complexify M)
  obtain ⟨e, he, hev⟩ := (SS.mem_spectrum_iff_eigenpair M z).1 hz
  have hz1 : ‖z‖ < 1 := by
    refine h z ?_
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := e) ⟨?_, he⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hev
  have : SS.specRad M = ‖z‖ := by
    unfold SS.specRad
    rw [← hnorm, ENNReal.coe_toReal, coe_nnnorm]
  rw [this]
  exact hz1

/-- `M` is stable iff its spectral radius is below one. -/
theorem ls_stable_iff_specRad [Nonempty X] (M : Matrix X X ℝ) :
    ls_Stable M ↔ SS.specRad M < 1 :=
  ⟨ls_specRad_lt_of_stable, ls_stable_of_specRad⟩

/-- Stability is invariant under transposition. -/
theorem ls_stable_transpose [Nonempty X] (M : Matrix X X ℝ) : ls_Stable Mᵀ ↔ ls_Stable M := by
  rw [ls_stable_iff_specRad, ls_stable_iff_specRad, SS.specRad_transpose]

/-- A scalar recursion `0 ≤ e_{t+1} ≤ re_t + δ_t` with `0 ≤ r < 1` and `δ_t → 0` tends to zero. -/
theorem ls_tendsto_zero_of_le_rec {e δ : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (he : ∀ t, 0 ≤ e t) (hrec : ∀ t, e (t + 1) ≤ r * e t + δ t)
    (hδ : Tendsto δ atTop (𝓝 0)) : Tendsto e atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1r : 0 < 1 - r := by linarith
  set η := ε * (1 - r) / 2 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.1 hδ η hη0
  have hbound : ∀ m, e (T + m) ≤ r ^ m * e T + η / (1 - r) := by
    intro m
    induction m with
    | zero => simp only [add_zero, pow_zero, one_mul]; linarith [div_pos hη0 h1r]
    | succ m ih =>
      have hd : δ (T + m) < η := by
        have := hT (T + m) (Nat.le_add_right T m)
        rw [Real.dist_eq, sub_zero] at this
        exact (le_abs_self _).trans_lt this
      have e1 := hrec (T + m)
      rw [show T + (m + 1) = T + m + 1 by ring]
      have : r * e (T + m) ≤ r * (r ^ m * e T + η / (1 - r)) :=
        mul_le_mul_of_nonneg_left ih hr0
      have hid : r * (r ^ m * e T + η / (1 - r)) + η = r ^ (m + 1) * e T + η / (1 - r) := by
        field_simp
        ring
      linarith
  have hpow : Tendsto (fun m => r ^ m * e T) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const (e T)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hpow (ε / 2) (by positivity)
  refine ⟨T + M, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = T + m := ⟨n - T, by omega⟩
  have hm := hM m (by omega)
  rw [Real.dist_eq, sub_zero] at hm ⊢
  have hb := hbound m
  have hηr : η / (1 - r) = ε / 2 := by rw [hη]; field_simp
  rw [abs_of_nonneg (he _)]
  have := le_abs_self (r ^ m * e T)
  linarith

/-- With `M` stable, `x_{t+1} = Mx_t + w_t` and `w_t → 0` give `x_t → 0`. -/
theorem ls_tendsto_zero_of_stable_input {M : Matrix X X ℝ} (hM : ls_Stable M)
    {x w : ℕ → X → ℝ} (hx : ∀ t, x (t + 1) = M *ᵥ x t + w t)
    (hw : Tendsto w atTop (𝓝 0)) : Tendsto x atTop (𝓝 0) := by
  obtain ⟨K, a, ha0, ha1, hK0, hK⟩ := hasGeomDecay_of_isStableMatrix M hM
  set s : ℕ → ℝ := fun t => ∑ j ∈ Finset.range t, a ^ j * ‖w (t - 1 - j)‖ with hs
  have hs0 : ∀ t, 0 ≤ s t := fun t =>
    Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg ha0 j) (norm_nonneg _)
  have hsrec : ∀ t, s (t + 1) ≤ a * s t + ‖w t‖ := by
    intro t
    apply le_of_eq
    simp only [hs]
    rw [Finset.sum_range_succ', Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show t + 1 - 1 - (j + 1) = t - 1 - j by omega, pow_succ]
      ring
    · simp
  have hδ : Tendsto (fun t => ‖w t‖) atTop (𝓝 0) := by
    simpa using hw.norm
  have hslim := ls_tendsto_zero_of_le_rec ha0 ha1 hs0 hsrec hδ
  have hbd : ∀ t, ‖x t‖ ≤ K * a ^ t * ‖x 0‖ + K * s t := by
    intro t
    rw [backward_sol_eq M hx t]
    refine (norm_add_le _ _).trans (add_le_add (hK t _) ?_)
    simp only [hs, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    calc ‖(M ^ j) *ᵥ w (t - 1 - j)‖ ≤ K * a ^ j * ‖w (t - 1 - j)‖ := hK j _
      _ = K * (a ^ j * ‖w (t - 1 - j)‖) := by ring
  have hlim : Tendsto (fun t => K * a ^ t * ‖x 0‖ + K * s t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => K * a ^ t * ‖x 0‖) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul K).mul_const ‖x 0‖
    simpa using h1.add (hslim.const_mul K)
  exact squeeze_zero_norm hbd hlim

/-- `Pᵢⱼ` from quadratic forms, for symmetric `P` (polarization). -/
theorem ls_entry_eq_polar {P : Matrix X X ℝ} (hP : Pᵀ = P) (i j : X) :
    P i j = ((Pi.single i 1 + Pi.single j 1) ⬝ᵥ (P *ᵥ (Pi.single i 1 + Pi.single j 1)) -
      Pi.single i (1 : ℝ) ⬝ᵥ (P *ᵥ Pi.single i 1) -
      Pi.single j (1 : ℝ) ⬝ᵥ (P *ᵥ Pi.single j 1)) / 2 := by
  rw [SS.LQProblem.quad_add hP]
  have hji : Pi.single j (1 : ℝ) ⬝ᵥ (P *ᵥ Pi.single i 1) = P i j := by
    rw [single_one_dotProduct, mulVec_single_one]
    exact congrFun (congrFun hP i) j
  rw [hji]
  ring

omit [DecidableEq X] in
/-- Symmetric matrices converge when their quadratic forms converge to those of a symmetric
limit. -/
theorem ls_tendsto_of_quad {P : ℕ → Matrix X X ℝ} {P₀ : Matrix X X ℝ}
    (hs : ∀ n, (P n)ᵀ = P n) (hP₀ : P₀ᵀ = P₀)
    (h : ∀ v : X → ℝ, Tendsto (fun n => v ⬝ᵥ (P n *ᵥ v)) atTop (𝓝 (v ⬝ᵥ (P₀ *ᵥ v)))) :
    Tendsto P atTop (𝓝 P₀) := by
  classical
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  simp only [ls_entry_eq_polar (hs _) i j, ls_entry_eq_polar hP₀ i j]
  exact (((h _).sub (h _)).sub (h _)).div_const 2

omit [DecidableEq X] in
/-- If every quadratic form of a sequence of symmetric matrices converges, the matrices converge
(entrywise) to a symmetric limit. -/
theorem ls_exists_tendsto_of_quad {P : ℕ → Matrix X X ℝ} (hs : ∀ n, (P n)ᵀ = P n)
    (h : ∀ v : X → ℝ, ∃ c, Tendsto (fun n => v ⬝ᵥ (P n *ᵥ v)) atTop (𝓝 c)) :
    ∃ P₀ : Matrix X X ℝ, P₀ᵀ = P₀ ∧ Tendsto P atTop (𝓝 P₀) := by
  classical
  choose c hc using h
  set e : X → X → ℝ := fun i => Pi.single i 1
  refine ⟨Matrix.of fun i j => (c (e i + e j) - c (e i) - c (e j)) / 2, ?_, ?_⟩
  · ext i j
    simp only [transpose_apply, of_apply]
    rw [add_comm (e j) (e i)]
    ring
  · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [ls_entry_eq_polar (hs _) i j, of_apply]
    exact (((hc _).sub (hc _)).sub (hc _)).div_const 2

omit [DecidableEq X] in
/-- A positive definite form dominates a multiple of `‖x‖²` (sup norm). -/
theorem ls_posDef_coercive {Q : Matrix X X ℝ} (hQ : Q.PosDef) :
    ∃ c > 0, ∀ x : X → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Q *ᵥ x) := by
  have hQ' := SS.LQProblem.posDef_iff_real.1 hQ
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨1, one_pos, fun x => ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    subst this
    simp
  · have hcpt := isCompact_sphere (0 : X → ℝ) 1
    have hne : (Metric.sphere (0 : X → ℝ) 1).Nonempty :=
      NormedSpace.sphere_nonempty.2 zero_le_one
    have hcont : Continuous fun v : X → ℝ => v ⬝ᵥ (Q *ᵥ v) :=
      Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id)
    obtain ⟨v₀, hv₀, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
    have hv₀ne : v₀ ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hv₀
      exact zero_ne_one hv₀
    refine ⟨v₀ ⬝ᵥ (Q *ᵥ v₀), hQ'.2 hv₀ne, fun x => ?_⟩
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      simp
    · have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
      set v := ‖x‖⁻¹ • x with hv
      have hvS : v ∈ Metric.sphere (0 : X → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, hv, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hnx.ne']
      have h1 := hmin hvS
      have hxv : x = ‖x‖ • v := by rw [hv, smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
      have hq : x ⬝ᵥ (Q *ᵥ x) = ‖x‖ ^ 2 * (v ⬝ᵥ (Q *ᵥ v)) := by
        conv_lhs => rw [hxv]
        rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
        ring
      rw [hq, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)

omit [DecidableEq X] in
/-- For positive definite `Q`, `x_t'Qx_t → 0` forces `x_t → 0`. -/
theorem ls_tendsto_zero_of_quad_posDef {Q : Matrix X X ℝ} (hQ : Q.PosDef) {x : ℕ → X → ℝ}
    (h : Tendsto (fun t => x t ⬝ᵥ (Q *ᵥ x t)) atTop (𝓝 0)) : Tendsto x atTop (𝓝 0) := by
  obtain ⟨c, hc, hcx⟩ := ls_posDef_coercive hQ
  have h2 : Tendsto (fun t => ‖x t‖ ^ 2) atTop (𝓝 0) := by
    have hl : Tendsto (fun t => x t ⬝ᵥ (Q *ᵥ x t) / c) atTop (𝓝 0) := by
      simpa using h.div_const c
    exact squeeze_zero (fun t => by positivity) (fun t => (le_div_iff₀' hc).2 (hcx (x t))) hl
  have h3 : Tendsto (fun t => Real.sqrt (‖x t‖ ^ 2)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    rwa [Real.sqrt_zero] at this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h3.congr fun t => ?_
  exact Real.sqrt_sq (norm_nonneg _)

end Miao.PartialInformation
