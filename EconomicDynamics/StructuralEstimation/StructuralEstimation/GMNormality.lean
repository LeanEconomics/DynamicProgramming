/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.GMConsistency
import StructuralEstimation.GMAlgebra
import StructuralEstimation.GMProbability

/-!
# Asymptotic normality of GMM: Theorem 12.1.2 (Miao, §12.1, pp. 390–392)

Miao, pp. 390–392. With `θ̂_T` consistent (Theorem 12.1.1), interior, the first-order
condition (12.2), the (row-wise) mean value expansion (12.3), `M_T → M` in probability and the
central limit theorem `√T g_T(θ₀) →d N(0, S)` (Lemma 12.1.1), Slutsky's theorem gives

`√T(θ̂_T − θ₀) →d N(0, MSM')`, `M = (G₀'WG₀)⁻¹G₀'W`, `G₀ = E ∂h(x_t, θ₀)/∂θ`

(`theorem_12_1_2`). The CLT of Lemma 12.1.1 is a cited result that does not follow from the
assumptions listed for it (see `docs/GM-corrections.md`); `theorem_12_1_2` takes its conclusion as
the explicit hypothesis `hclt`, and `lemma_12_1_1_iid` (module `GMLemma1211`) proves it in the
i.i.d. case from Mathlib's central limit theorem, so the hypothesis is satisfiable.

Departures: (i) the mean value expansion uses a separate `θ̄_{T,i}` for each moment (the single
`θ̄_T` of (12.3) does not exist in general, `eq_12_3_counterexample`); (ii) the rank condition
`G₀x = 0 ⇒ x = 0` (so that `G₀'WG₀` is invertible) is added; (iii) of Assumption 12.1.8(i)
only differentiability of `h(x, ·)` on a ball around `θ₀` is used, and of Assumption 12.1.10(i)
only continuity of `E ∂h/∂θ` at `θ₀`; (iv) the estimator is assumed measurable (a random
variable), which the book takes for granted.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The sample derivative `∂g_T(θ)/∂θ = (1/T) Σ_{t<T} ∂h(x_t, θ)/∂θ`, row by row. -/
noncomputable def gm_sampleDeriv {k q : ℕ} (X : ℕ → Ω → E)
    (Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ) (T : ℕ) (ω : Ω) (θ : Fin k → ℝ) :
    Fin q → (Fin k → ℝ) →L[ℝ] ℝ :=
  fun i => (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, Dh (X t ω) θ i

/-- The sample Jacobian `∂g_T(θ)/∂θ` as a `q × k` matrix. -/
noncomputable def gm_sampleJac {k q : ℕ} (X : ℕ → Ω → E)
    (Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ) (T : ℕ) (ω : Ω) (θ : Fin k → ℝ) :
    Matrix (Fin q) (Fin k) ℝ :=
  gm_jacobian (gm_sampleDeriv X Dh T ω θ)

/-- The population Jacobian `E[∂h(x_t, θ)/∂θ]` (Assumption 12.1.8(iii)). -/
noncomputable def gm_popJac {k q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E)
    (Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ) (θ : Fin k → ℝ) :
    Matrix (Fin q) (Fin k) ℝ :=
  Matrix.of fun i j => ∫ ω, gm_jacobian (Dh (X 0 ω) θ) i j ∂P

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- `g_T` is differentiable with derivative `gm_sampleDeriv` where every `h(x_t, ·)` is. -/
theorem gm_hasFDerivAt_sampleMoment {k q : ℕ} {X : ℕ → Ω → E} {h : E → (Fin k → ℝ) → Fin q → ℝ}
    {Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ} {θ : Fin k → ℝ}
    (hD : ∀ x i, HasFDerivAt (fun θ' => h x θ' i) (Dh x θ i) θ) (T : ℕ) (ω : Ω) (i : Fin q) :
    HasFDerivAt (fun θ' => gm_sampleMoment X h T ω θ' i) (gm_sampleDeriv X Dh T ω θ i) θ :=
  (HasFDerivAt.fun_sum fun t _ => hD (X t ω) i).const_mul ((T : ℝ)⁻¹)

/-- Points of the segment `[θ₀, θ]` are no farther from `θ₀` than `θ`. -/
theorem gm_dist_segment_le {k : ℕ} {θ₀ θ : Fin k → ℝ} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    dist (θ₀ + s • (θ - θ₀)) θ₀ ≤ dist θ θ₀ := by
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hs.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hs.2

omit [MeasurableSpace E] in
/-- Miao, p. 391 (`M_T → M` needs `∂g_T(θ̃_T)/∂θ → G₀`): under Assumption 12.1.10 and
consistency, the sample Jacobian at any point `θ̃_T` no farther from `θ₀` than `θ̂_T` converges in
probability to `G₀ = E ∂h(x_t, θ₀)/∂θ`. -/
theorem gm_sampleJac_tendstoInMeasure {k q : ℕ} {P : Measure Ω} {X : ℕ → Ω → E}
    {Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ} {θ₀ : Fin k → ℝ} {r : ℝ}
    {θh θt : ℕ → Ω → Fin k → ℝ} (hcons : TendstoInMeasure P θh atTop (fun _ => θ₀))
    (hle : ∀ T ω, dist (θt T ω) θ₀ ≤ dist (θh T ω) θ₀) (hr : 0 < r) {i : Fin q} {j : Fin k}
    (hGc : ContinuousAt (fun θ => gm_popJac P X Dh θ i j) θ₀)
    (hGu : ∀ ε > 0, Tendsto (fun T => P {ω | ∃ θ ∈ Metric.ball θ₀ r,
        ε ≤ |gm_sampleJac X Dh T ω θ i j - gm_popJac P X Dh θ i j|}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun T ω => gm_sampleJac X Dh T ω (θt T ω) i j) atTop
      (fun _ => gm_popJac P X Dh θ₀ i j) := by
  rw [tendstoInMeasure_iff_dist] at hcons ⊢
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 hGc (ε / 2) (by linarith)
  have hδ' : 0 < min δ r := lt_min hδ hr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun T => P {ω | min δ r ≤ dist (θh T ω) θ₀} + P {ω | ∃ θ ∈ Metric.ball θ₀ r,
      ε / 2 ≤ |gm_sampleJac X Dh T ω θ i j - gm_popJac P X Dh θ i j|}) ?_
    (fun _ => zero_le) fun T => ?_
  · simpa using (hcons _ hδ').add (hGu (ε / 2) (by linarith))
  · refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_exists, not_and] at hn
    obtain ⟨h1, h2⟩ := hn
    have hd := (hle T ω).trans_lt h1
    have hb : θt T ω ∈ Metric.ball θ₀ r := Metric.mem_ball.2 (hd.trans_le (min_le_right _ _))
    have e1 := h2 _ hb
    have e2 := hcont (hd.trans_le (min_le_left _ _))
    simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω e2
    have := abs_sub_le (gm_sampleJac X Dh T ω (θt T ω) i j) (gm_popJac P X Dh (θt T ω) i j)
      (gm_popJac P X Dh θ₀ i j)
    linarith

/-- **Theorem 12.1.2** (asymptotic normality of GMM, Miao, p. 391). Under Assumptions
12.1.1–12.1.10 — stationarity and ergodicity, continuity, identification, compactness and
dominance (for consistency, Theorem 12.1.1), `W_T` positive semidefinite with `W_T → W > 0`
(12.1.4), `h(x, ·)` differentiable on a ball `B(θ₀, r) ⊆ Θ` with derivative `Dh` (12.1.8),
`E ∂h/∂θ` continuous at `θ₀` and `sup_{B(θ₀,r)} |∂g_T/∂θ − E ∂h/∂θ| → 0` in probability
(12.1.10) — together with the rank condition on `G₀ = E ∂h(x_t, θ₀)/∂θ`, a measurable GMM
estimator, and the central limit theorem `√T g_T(θ₀) →d Z ~ N(0, S)` of Lemma 12.1.1 (the
explicit hypothesis `hclt`; it holds e.g. for i.i.d. data, `lemma_12_1_1_iid`),

`√T(θ̂_T − θ₀) →d −MZ ~ N(0, MSM')`, `M = (G₀'WG₀)⁻¹G₀'W`. -/
theorem theorem_12_1_2 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ)
    {h : E → (Fin k → ℝ) → Fin q → ℝ} (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ)
    (hc : ∀ x, ContinuousOn (h x) Θ) (hid : Assumption_12_1_3 P X h Θ θ₀)
    (hdom : Assumption_12_1_7 P X h Θ)
    {WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hA4 : Assumption_12_1_4 P WT W)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball θ₀ r ⊆ Θ)
    {Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ}
    (hDh : ∀ x, ∀ θ ∈ Metric.ball θ₀ r, ∀ i, HasFDerivAt (fun θ' => h x θ' i) (Dh x θ i) θ)
    (hGc : ∀ i j, ContinuousAt (fun θ => gm_popJac P X Dh θ i j) θ₀)
    (hGu : ∀ i j, ∀ ε > 0, Tendsto (fun T => P {ω | ∃ θ ∈ Metric.ball θ₀ r,
        ε ≤ |gm_sampleJac X Dh T ω θ i j - gm_popJac P X Dh θ i j|}) atTop (𝓝 0))
    (hrank : Function.Injective (gm_popJac P X Dh θ₀).mulVec)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosSemidef) {Z : Ω' → EuclideanSpace ℝ (Fin q)}
    (hZ : HasLaw Z (multivariateGaussian 0 S) P')
    (hclt : TendstoInDistribution
      (fun (T : ℕ) ω => gm_toE (Real.sqrt (T : ℝ) • gm_sampleMoment X h T ω θ₀)) atTop Z
      (fun _ => P) P')
    {θh : ℕ → Ω → Fin k → ℝ} (hθm : ∀ T, Measurable (θh T)) (hθh : ∀ T ω, θh T ω ∈ Θ)
    (hmin : ∀ T ω, ∀ θ ∈ Θ, gm_objective X h WT T ω (θh T ω) ≤ gm_objective X h WT T ω θ) :
    TendstoInDistribution (fun (T : ℕ) ω => gm_toE (Real.sqrt (T : ℝ) • (θh T ω - θ₀))) atTop
      (fun ω' => gm_matE (-gm_M (gm_popJac P X Dh θ₀) W) (Z ω')) (fun _ => P) P' ∧
    HasLaw (fun ω' => gm_matE (-gm_M (gm_popJac P X Dh θ₀) W) (Z ω'))
      (multivariateGaussian 0 (gm_M (gm_popJac P X Dh θ₀) W * S *
        (gm_M (gm_popJac P X Dh θ₀) W).transpose)) P' := by
  classical
  obtain ⟨hWpsd, hW, hWT⟩ := hA4
  set G₀ := gm_popJac P X Dh θ₀ with hG₀
  set Mm := gm_M G₀ W with hMm
  have hWTs : ∀ T ω, (WT T ω).IsSymm := fun T ω => (hWpsd T ω).isHermitian.isSymm
  have hA0 : IsUnit (G₀.transpose * W * G₀).det := gm_isUnit_det_GWG hW hrank
  have hcons := theorem_12_1_1 hX hst herg hΘ hθ₀ hm hc hid hdom ⟨hWpsd, hW, hWT⟩ hθh hmin
  -- the mean value points (row-wise (12.3))
  have hsx : ∀ T ω i, ∃ s ∈ Set.Icc (0 : ℝ) 1, θh T ω ∈ Metric.ball θ₀ r →
      gm_sampleMoment X h T ω (θh T ω) i = gm_sampleMoment X h T ω θ₀ i +
        ∑ j, gm_sampleJac X Dh T ω (θ₀ + s • (θh T ω - θ₀)) i j * (θh T ω - θ₀) j := by
    intro T ω i
    by_cases hb : θh T ω ∈ Metric.ball θ₀ r
    · obtain ⟨s, hs, heq⟩ := eq_12_3 (g := gm_sampleMoment X h T ω)
        (Dg := gm_sampleDeriv X Dh T ω) (θ₀ := θ₀) (θh := θh T ω) (fun i' s hs =>
          gm_hasFDerivAt_sampleMoment (fun x i'' => hDh x _
            (Metric.mem_ball.2 ((gm_dist_segment_le hs).trans_lt (Metric.mem_ball.1 hb))) i'')
            T ω i') i
      exact ⟨s, Set.Ioo_subset_Icc_self hs, fun _ => heq⟩
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun h' => absurd h' hb⟩
  choose s hs01 hsexp using hsx
  set θb : ℕ → Ω → Fin q → Fin k → ℝ := fun T ω i => θ₀ + s T ω i • (θh T ω - θ₀) with hθbdef
  have hθb : ∀ T ω i, dist (θb T ω i) θ₀ ≤ dist (θh T ω) θ₀ := fun T ω i =>
    gm_dist_segment_le (hs01 T ω i)
  set Gh : ℕ → Ω → Matrix (Fin q) (Fin k) ℝ := fun T ω => gm_sampleJac X Dh T ω (θh T ω)
    with hGhdef
  set Gb : ℕ → Ω → Matrix (Fin q) (Fin k) ℝ := fun T ω =>
    Matrix.of fun i j => gm_sampleJac X Dh T ω (θb T ω i) i j with hGbdef
  set MT : ℕ → Ω → Matrix (Fin k) (Fin q) ℝ := fun T ω =>
    ((Gh T ω).transpose * WT T ω * Gb T ω)⁻¹ * (Gh T ω).transpose * WT T ω with hMTdef
  -- convergence of the Jacobians
  have hGh : ∀ i j, TendstoInMeasure P (fun T ω => Gh T ω i j) atTop (fun _ => G₀ i j) :=
    fun i j => gm_sampleJac_tendstoInMeasure hcons (fun _ _ => le_rfl) hr (hGc i j) (hGu i j)
  have hGb : ∀ i j, TendstoInMeasure P (fun T ω => Gb T ω i j) atTop (fun _ => G₀ i j) :=
    fun i j => gm_sampleJac_tendstoInMeasure (θt := fun T ω => θb T ω i) hcons
      (fun T ω => hθb T ω i) hr (hGc i j) (hGu i j)
  -- the triple (Ĝ, Ḡ, W_T) as a function-valued random variable
  set U : ℕ → Ω → (Fin q → Fin k → ℝ) × (Fin q → Fin k → ℝ) × (Fin q → Fin q → ℝ) :=
    fun T ω => (fun i j => Gh T ω i j, fun i j => Gb T ω i j, fun i j => WT T ω i j) with hUdef
  have hU : TendstoInMeasure P U atTop
      (fun _ => ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j))) := by
    refine gm_tendstoInMeasure_prod ?_ (gm_tendstoInMeasure_prod ?_ ?_)
    · exact gm_tendstoInMeasure_pi fun i => gm_tendstoInMeasure_pi fun j => hGh i j
    · exact gm_tendstoInMeasure_pi fun i => gm_tendstoInMeasure_pi fun j => hGb i j
    · exact gm_tendstoInMeasure_pi fun i => gm_tendstoInMeasure_pi fun j => hWT i j
  set Nf : (Fin q → Fin k → ℝ) × (Fin q → Fin k → ℝ) × (Fin q → Fin q → ℝ) →
      Matrix (Fin k) (Fin k) ℝ := fun p =>
    (Matrix.of p.1).transpose * Matrix.of p.2.2 * Matrix.of p.2.1 with hNfdef
  have hNc : Continuous Nf :=
    ((continuous_id.comp continuous_fst).matrix_transpose.matrix_mul
      (continuous_id.comp (continuous_snd.comp continuous_snd))).matrix_mul
      (continuous_id.comp (continuous_fst.comp continuous_snd))
  set Φ : (Fin q → Fin k → ℝ) × (Fin q → Fin k → ℝ) × (Fin q → Fin q → ℝ) →
      Fin k → Fin q → ℝ := fun p =>
    (Nf p)⁻¹ * (Matrix.of p.1).transpose * Matrix.of p.2.2 with hΦdef
  have hN0 : Nf ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j)) =
      G₀.transpose * W * G₀ := rfl
  have hΦc : ContinuousAt Φ ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j)) := by
    have hinv : ContinuousAt (fun p => (Nf p)⁻¹)
        ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j)) := by
      refine ContinuousAt.comp (g := fun A : Matrix (Fin k) (Fin k) ℝ => A⁻¹) ?_ hNc.continuousAt
      rw [hN0]
      exact gm_continuousAt_inv hA0.ne_zero
    have hT : ContinuousAt (fun p : (Fin q → Fin k → ℝ) × (Fin q → Fin k → ℝ) ×
        (Fin q → Fin q → ℝ) => (Matrix.of p.1).transpose)
        ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j)) :=
      (continuous_id.comp continuous_fst).matrix_transpose.continuousAt
    have hV' : ContinuousAt (fun p : (Fin q → Fin k → ℝ) × (Fin q → Fin k → ℝ) ×
        (Fin q → Fin q → ℝ) => Matrix.of p.2.2)
        ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j)) :=
      (continuous_id.comp (continuous_snd.comp continuous_snd)).continuousAt
    have hmul1 : Continuous fun x : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin q) ℝ =>
        x.1 * x.2 := continuous_fst.matrix_mul continuous_snd
    have hmul2 : Continuous fun x : Matrix (Fin k) (Fin q) ℝ × Matrix (Fin q) (Fin q) ℝ =>
        x.1 * x.2 := continuous_fst.matrix_mul continuous_snd
    have hm1 := hmul1.continuousAt.comp (hinv.prodMk hT)
    exact hmul2.continuousAt.comp (hm1.prodMk hV')
  have hMT : ∀ i j, TendstoInMeasure P (fun T ω => MT T ω i j) atTop (fun _ => Mm i j) := by
    intro i j
    have h1 := gm_tendstoInMeasure_comp hU hΦc
    exact gm_tendstoInMeasure_apply (gm_tendstoInMeasure_apply h1 i) j
  have hD : ∀ i j, TendstoInMeasure P (fun T ω => (Mm - MT T ω) i j) atTop (fun _ => 0) := by
    intro i j
    have := gm_tendstoInMeasure_comp (hMT i j) (f := fun x => Mm i j - x)
      (continuous_const.sub continuous_id).continuousAt
    simpa using this
  have hdet : TendstoInMeasure P (fun T ω => (Nf (U T ω)).det) atTop
      (fun _ => (G₀.transpose * W * G₀).det) := by
    have := gm_tendstoInMeasure_comp hU (f := fun p => (Nf p).det)
      (hNc.matrix_det).continuousAt
    rwa [hN0] at this
  -- the linear approximation
  set Y : ℕ → Ω → EuclideanSpace ℝ (Fin k) :=
    fun T ω => gm_toE (Real.sqrt (T : ℝ) • (θh T ω - θ₀)) with hYdef
  set Zs : ℕ → Ω → EuclideanSpace ℝ (Fin q) :=
    fun T ω => gm_toE (Real.sqrt (T : ℝ) • gm_sampleMoment X h T ω θ₀) with hZsdef
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin k) := fun T ω => gm_matE (-Mm) (Zs T ω) with hVdef
  have hgood : ∀ T ω, θh T ω ∈ Metric.ball θ₀ r → (Nf (U T ω)).det ≠ 0 →
      Y T ω - V T ω = gm_matE (Mm - MT T ω) (Zs T ω) := by
    intro T ω hb hdet0
    have hNU : Nf (U T ω) = (Gh T ω).transpose * WT T ω * Gb T ω := rfl
    rw [hNU] at hdet0
    have hinv : IsUnit ((Gh T ω).transpose * WT T ω * Gb T ω).det := isUnit_iff_ne_zero.2 hdet0
    have hloc : IsLocalMin (fun θ => gm_quadForm (WT T ω) (gm_sampleMoment X h T ω θ))
        (θh T ω) := by
      have hmo : IsMinOn (gm_objective X h WT T ω) Θ (θh T ω) := fun θ hθ => hmin T ω θ hθ
      exact hmo.isLocalMin (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hb) hball)
    have hfoc := eq_12_2 (hWTs T ω)
      (fun i => gm_hasFDerivAt_sampleMoment (fun x i' => hDh x _ hb i') T ω i) hloc
    have hexp : gm_sampleMoment X h T ω (θh T ω) =
        gm_sampleMoment X h T ω θ₀ + (Gb T ω).mulVec (θh T ω - θ₀) := by
      funext i
      rw [hsexp T ω i hb]
      rfl
    have hlin := gm_linearization_sqrt (A := Gh T ω) (B := Gb T ω) (V := WT T ω) hfoc hexp hinv
      (Real.sqrt T)
    simp only [hYdef, hVdef, hZsdef, gm_matE_toE]
    rw [hlin, gm_toE, gm_toE, gm_toE, ← WithLp.toLp_sub, Matrix.neg_mulVec, Matrix.sub_mulVec]
    congr 1
    change -(MT T ω).mulVec _ - -Mm.mulVec _ = Mm.mulVec _ - (MT T ω).mulVec _
    abel
  have hprod := gm_tendstoInMeasure_matE hclt hD
  have hYV : TendstoInMeasure P (Y - V) atTop 0 := by
    rw [tendstoInMeasure_iff_dist] at hprod ⊢
    have hc1 := tendstoInMeasure_iff_dist.1 hcons r hr
    have hc2 := tendstoInMeasure_iff_dist.1 hdet |(G₀.transpose * W * G₀).det|
      (abs_pos.2 hA0.ne_zero)
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun T => P {ω | r ≤ dist (θh T ω) θ₀} +
        P {ω | |(G₀.transpose * W * G₀).det| ≤ dist (Nf (U T ω)).det (G₀.transpose * W * G₀).det}
        + P {ω | ε ≤ dist (gm_matE (Mm - MT T ω) (Zs T ω)) 0}) ?_ (fun _ => zero_le) fun T => ?_
    · simpa using (hc1.add hc2).add (hprod ε hε)
    · refine (measure_mono fun ω hω => ?_).trans
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
      by_contra hn
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hn
      obtain ⟨⟨h1, h2⟩, h3⟩ := hn
      have hdet0 : (Nf (U T ω)).det ≠ 0 := by
        intro h0
        rw [h0, Real.dist_eq, zero_sub, abs_neg] at h2
        exact lt_irrefl _ h2
      have := hgood T ω (Metric.mem_ball.2 h1) hdet0
      simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply] at hω
      rw [this] at hω
      exact absurd hω (not_le.2 h3)
  have hV : TendstoInDistribution V atTop (fun ω' => gm_matE (-Mm) (Z ω')) (fun _ => P) P' :=
    by
    have := hclt.continuous_comp (g := gm_matE (-Mm)) (gm_continuous_matE (-Mm))
    exact this
  have hYm : ∀ T, AEMeasurable (Y T) P := fun T =>
    ((gm_continuous_toE k).measurable.comp
      (((hθm T).sub measurable_const).const_smul (Real.sqrt (T : ℝ)))).aemeasurable
  refine ⟨tendstoInDistribution_of_tendstoInMeasure_sub Y _ hV hYV hYm, ?_⟩
  refine ⟨(gm_continuous_matE _).measurable.comp_aemeasurable hZ.aemeasurable, ?_⟩
  have hcomp : (fun ω' => gm_matE (-Mm) (Z ω')) = gm_matE (-Mm) ∘ Z := rfl
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable
    (gm_continuous_matE _).measurable.aemeasurable hZ.aemeasurable, hZ.map_eq,
    gm_map_multivariateGaussian _ hS]
  simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-- Miao, p. 392: with the optimal weighting matrix `W = S⁻¹` (`S` positive definite) the limit
law of Theorem 12.1.2 is `N(0, (G₀'S⁻¹G₀)⁻¹)`. -/
theorem theorem_12_1_2_efficient {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {k q : ℕ}
    {G₀ : Matrix (Fin q) (Fin k) ℝ} (hrank : Function.Injective G₀.mulVec)
    {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosDef) {L : Ω' → EuclideanSpace ℝ (Fin k)}
    (hL : HasLaw L (multivariateGaussian 0 (gm_M G₀ S⁻¹ * S * (gm_M G₀ S⁻¹).transpose)) P') :
    HasLaw L (multivariateGaussian 0 (G₀.transpose * S⁻¹ * G₀)⁻¹) P' := by
  rwa [gm_efficient_var G₀ hS (gm_isUnit_det_GWG hS.inv hrank)] at hL

end Miao.StructuralEstimation
