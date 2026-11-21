/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.GMBasic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Instances.Matrix

/-!
# Probability tools for the asymptotics of GMM (Miao, §12.1, pp. 390–392)

Tools used for Lemma 12.1.1 and Theorem 12.1.2 (Miao, pp. 390–392), on top of Mathlib's
convergence in probability (`TendstoInMeasure`), convergence in distribution
(`TendstoInDistribution`, with Slutsky's theorem and the continuous mapping theorem) and the
multivariate normal law `multivariateGaussian μ S` on `EuclideanSpace ℝ (Fin q)`.

* `gm_toE`, `gm_matE`: vectors of `ℝ^q` as points of the Euclidean space, and the linear map
  `z ↦ Mz` of a `k × q` matrix.
* `gm_map_multivariateGaussian`: if `Z ~ N(0, S)` then `MZ ~ N(0, MSM')` (characteristic
  functions).
* `gm_tendstoInMeasure_comp`: the continuous mapping theorem for convergence in probability to a
  constant; `gm_tendstoInMeasure_pi`, `gm_tendstoInMeasure_apply`, `gm_tendstoInMeasure_prod`:
  convergence in probability of vectors, matrices and pairs, coordinatewise.
* `gm_tendstoInMeasure_mul`, `gm_tendstoInMeasure_matE`: if `Z_T → Z` in distribution and
  `D_T → 0` in probability then `D_T Z_T → 0` in probability (tightness via the portmanteau
  theorem); no measurability of `D_T` is required.
* `gm_continuousAt_inv`: matrix inversion is continuous at an invertible matrix.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- A vector of `ℝ^q` as a point of the Euclidean space `EuclideanSpace ℝ (Fin q)`. -/
def gm_toE {q : ℕ} (v : Fin q → ℝ) : EuclideanSpace ℝ (Fin q) := WithLp.toLp 2 v

/-- The linear map `z ↦ Mz` of a `k × q` matrix between Euclidean spaces. -/
def gm_matE {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) (z : EuclideanSpace ℝ (Fin q)) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (M.mulVec z.ofLp)

theorem gm_continuous_toE (q : ℕ) : Continuous (gm_toE (q := q)) :=
  PiLp.continuous_toLp 2 _

theorem gm_continuous_matE {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) :
    Continuous (gm_matE M) :=
  (PiLp.continuous_toLp 2 _).comp
    (Continuous.matrix_mulVec continuous_const (PiLp.continuous_ofLp 2 _))

theorem gm_matE_toE {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) (v : Fin q → ℝ) :
    gm_matE M (gm_toE v) = gm_toE (M.mulVec v) := rfl

/-- `⟪Mz, t⟫ = ⟪z, M't⟫`. -/
theorem gm_inner_matE {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) (z : EuclideanSpace ℝ (Fin q))
    (t : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (gm_matE M z) t = inner ℝ z (gm_matE M.transpose t) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, gm_matE, star_trivial]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- **Linear images of normal vectors** (used in Theorem 12.1.2, Miao, p. 391): if `Z ~ N(0, S)`
with `S` positive semidefinite, then `MZ ~ N(0, MSM')`. -/
theorem gm_map_multivariateGaussian {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ)
    {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosSemidef) :
    (multivariateGaussian 0 S).map (gm_matE M) =
      multivariateGaussian 0 (M * S * M.transpose) := by
  have hS' : (M * S * M.transpose).PosSemidef := by
    have := hS.mul_mul_conjTranspose_same M
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hm : Measurable (gm_matE M) := (gm_continuous_matE M).measurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [gm_inner_matE]
  rw [← charFun_apply, charFun_multivariateGaussian hS, charFun_multivariateGaussian hS']
  have key : (M.transpose.mulVec t.ofLp) ⬝ᵥ S.mulVec (M.transpose.mulVec t.ofLp) =
      t.ofLp ⬝ᵥ (M * S * M.transpose).mulVec t.ofLp := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec t.ofLp M,
      ← Matrix.mulVec_transpose]
  simp only [gm_matE, WithLp.ofLp_toLp, key, inner_zero_right]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The continuous mapping theorem for convergence in probability to a constant. -/
theorem gm_tendstoInMeasure_comp {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {P : Measure Ω} {Y : ℕ → Ω → α} {c : α} (hY : TendstoInMeasure P Y atTop (fun _ => c))
    {f : α → β} (hf : ContinuousAt f c) :
    TendstoInMeasure P (fun T ω => f (Y T ω)) atTop (fun _ => f c) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.1 hf ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hY δ hδ)
    (fun _ => zero_le) fun T => measure_mono fun ω hω => ?_
  by_contra hn
  exact absurd hω (not_le.2 (hfδ (not_le.1 hn)))

/-- Coordinatewise convergence in probability gives convergence in probability of the vector. -/
theorem gm_tendstoInMeasure_pi {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, PseudoMetricSpace (β i)] {P : Measure Ω} {Y : ℕ → Ω → ∀ i, β i} {c : ∀ i, β i}
    (h : ∀ i, TendstoInMeasure P (fun T ω => Y T ω i) atTop (fun _ => c i)) :
    TendstoInMeasure P Y atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hi := fun i => tendstoInMeasure_iff_dist.1 (h i) ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun T => ∑ i, P {ω | ε ≤ dist (Y T ω i) (c i)}) ?_ (fun _ => zero_le) fun T => ?_
  · simpa using tendsto_finsetSum Finset.univ fun i _ => hi i
  · refine (measure_mono fun ω hω => ?_).trans (measure_iUnion_fintype_le P _)
    simp only [Set.mem_iUnion]
    by_contra hn
    push Not at hn
    exact absurd hω (not_le.2 ((dist_pi_lt_iff hε).2 fun i => not_le.1 (hn i)))

/-- A coordinate of a vector converging in probability converges in probability. -/
theorem gm_tendstoInMeasure_apply {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, PseudoMetricSpace (β i)] {P : Measure Ω} {Y : ℕ → Ω → ∀ i, β i} {c : ∀ i, β i}
    (h : TendstoInMeasure P Y atTop (fun _ => c)) (i : ι) :
    TendstoInMeasure P (fun T ω => Y T ω i) atTop (fun _ => c i) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ => zero_le) fun T => measure_mono fun ω hω => le_trans hω (dist_le_pi_dist _ _ i)

/-- Convergence in probability of a pair from its components. -/
theorem gm_tendstoInMeasure_prod {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {P : Measure Ω} {Y : ℕ → Ω → α} {Y' : ℕ → Ω → β} {c : α} {c' : β}
    (h : TendstoInMeasure P Y atTop (fun _ => c)) (h' : TendstoInMeasure P Y' atTop (fun _ => c')) :
    TendstoInMeasure P (fun T ω => (Y T ω, Y' T ω)) atTop (fun _ => (c, c')) := by
  rw [tendstoInMeasure_iff_dist] at h h' ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun T => P {ω | ε ≤ dist (Y T ω) c} + P {ω | ε ≤ dist (Y' T ω) c'}) ?_
    (fun _ => zero_le) fun T => ?_
  · simpa using (h ε hε).add (h' ε hε)
  · refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    simp only [Set.mem_ofPred_eq, Prod.dist_eq, le_max_iff] at hω
    exact hω

/-- Probability of a large value of a variable converging in distribution is eventually small
(tightness, from the portmanteau theorem). -/
theorem gm_tight_of_tendstoInDistribution {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℝ} {Z' : Ω' → ℝ} (hZ : TendstoInDistribution Z atTop Z' (fun _ => P) P')
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ T in atTop, P {ω | R ≤ |Z T ω|} < η := by
  set ν : Measure ℝ := P'.map Z'
  have : IsProbabilityMeasure ν := inferInstance
  set A : ℕ → Set ℝ := fun n => {x | (n : ℝ) ≤ |x|}
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_le measurable_const continuous_abs.measurable
  have hanti : Antitone A := fun n m hnm x hx =>
    show (n : ℝ) ≤ |x| from le_trans (by exact_mod_cast hnm) hx
  have hempty : (⋂ n, A n) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall, not_le, A,
      Set.mem_ofPred_eq]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨n, hn⟩
  have hlim := tendsto_measure_iInter_atTop (μ := ν) (fun n => (hAm n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at hlim
  obtain ⟨n, hn, hn1⟩ := ((hlim.eventually (gt_mem_nhds hη)).and (eventually_ge_atTop 1)).exists
  refine ⟨n, by exact_mod_cast hn1, ?_⟩
  have hcl : IsClosed (A n) := isClosed_le continuous_const continuous_abs
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hZ.tendsto hcl
  simp only [ProbabilityMeasure.coe_mk] at hport
  filter_upwards [eventually_lt_of_limsup_lt (hport.trans_lt hn)] with T hT
  rwa [Measure.map_apply_of_aemeasurable (hZ.forall_aemeasurable T) (hAm n)] at hT

/-- If `Z_T → Z` in distribution and `D_T → 0` in probability then `D_T Z_T → 0` in
probability (no measurability of `D_T` needed). -/
theorem gm_tendstoInMeasure_mul {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℝ} {Z' : Ω' → ℝ} (hZ : TendstoInDistribution Z atTop Z' (fun _ => P) P')
    {D : ℕ → Ω → ℝ} (hD : TendstoInMeasure P D atTop (fun _ => 0)) :
    TendstoInMeasure P (fun T ω => D T ω * Z T ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hD ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨R, hR, hev⟩ := gm_tight_of_tendstoInDistribution hZ hη2
  have hD' := (ENNReal.tendsto_nhds_zero.1 (hD (ε / R) (by positivity))) (η / 2) hη2
  filter_upwards [hev, hD'] with T h1 h2
  calc P {ω | ε ≤ dist (D T ω * Z T ω) 0}
      ≤ P ({ω | R ≤ |Z T ω|} ∪ {ω | ε / R ≤ dist (D T ω) 0}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
        by_contra hn
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hn
        have hlt : |D T ω| * |Z T ω| < ε / R * R :=
          mul_lt_mul'' hn.2 hn.1 (abs_nonneg _) (abs_nonneg _)
        rw [div_mul_cancel₀ _ hR.ne', ← abs_mul] at hlt
        exact absurd hω (not_le.2 hlt)
    _ ≤ P {ω | R ≤ |Z T ω|} + P {ω | ε / R ≤ dist (D T ω) 0} := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add h1.le h2
    _ = η := ENNReal.add_halves η

/-- A finite sum of terms converging to `0` in probability converges to `0` in probability. -/
theorem gm_tendstoInMeasure_sum {ι : Type*} [Fintype ι] {P : Measure Ω} {Y : ι → ℕ → Ω → ℝ}
    (h : ∀ i, TendstoInMeasure P (Y i) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun T ω => ∑ i, Y i T ω) atTop (fun _ => 0) := by
  have hpi := gm_tendstoInMeasure_pi (β := fun _ : ι => ℝ) (Y := fun T ω i => Y i T ω)
    (c := fun _ => 0) h
  have := gm_tendstoInMeasure_comp hpi (f := fun v : ι → ℝ => ∑ i, v i)
    (continuous_finsetSum _ fun i _ => continuous_apply i).continuousAt
  simpa using this

/-- If `Z_T → Z` in distribution (in `ℝ^q`) and the matrices `D_T → 0` in probability
(entrywise), then `D_T Z_T → 0` in probability. -/
theorem gm_tendstoInMeasure_matE {k q : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : ℕ → Ω → EuclideanSpace ℝ (Fin q)} {Z' : Ω' → EuclideanSpace ℝ (Fin q)}
    (hZ : TendstoInDistribution Z atTop Z' (fun _ => P) P')
    {D : ℕ → Ω → Matrix (Fin k) (Fin q) ℝ}
    (hD : ∀ i j, TendstoInMeasure P (fun T ω => D T ω i j) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun T ω => gm_matE (D T ω) (Z T ω)) atTop (fun _ => 0) := by
  have hZj : ∀ j, TendstoInDistribution (fun T ω => (Z T ω).ofLp j) atTop
      (fun ω' => (Z' ω').ofLp j) (fun _ => P) P' := fun j =>
    hZ.continuous_comp (g := fun z : EuclideanSpace ℝ (Fin q) => z.ofLp j)
      ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _))
  have hcoord : ∀ i, TendstoInMeasure P
      (fun T ω => (D T ω).mulVec (Z T ω).ofLp i) atTop (fun _ => 0) := fun i =>
    gm_tendstoInMeasure_sum (Y := fun j T ω => D T ω i j * (Z T ω).ofLp j)
      fun j => gm_tendstoInMeasure_mul (hZj j) (hD i j)
  have hpi := gm_tendstoInMeasure_pi (β := fun _ : Fin k => ℝ) (c := fun _ => 0) hcoord
  have := gm_tendstoInMeasure_comp hpi (f := gm_toE) (gm_continuous_toE k).continuousAt
  have h0 : gm_toE (fun _ : Fin k => (0 : ℝ)) = 0 := rfl
  rw [h0] at this
  exact this

/-- Matrix inversion is continuous at an invertible matrix. -/
theorem gm_continuousAt_inv {k : ℕ} {N : Matrix (Fin k) (Fin k) ℝ} (hN : N.det ≠ 0) :
    ContinuousAt (fun A : Matrix (Fin k) (Fin k) ℝ => A⁻¹) N := by
  have h : (fun A : Matrix (Fin k) (Fin k) ℝ => A⁻¹) =
      fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact ((continuousAt_inv₀ hN).comp (continuous_id.matrix_det).continuousAt).smul
    (continuous_id.matrix_adjugate).continuousAt

end Miao.StructuralEstimation
