/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.GMULLN

/-!
# Consistency of GMM: Theorem 12.1.1 (Miao, §12.1, pp. 388–390)

Miao, pp. 388–390. The GMM estimator `θ̂_T` minimises `Q_T(θ) = g_T(θ)' W_T g_T(θ)` over `Θ`.

* `gm_exists_estimator`: for compact nonempty `Θ` and `h(x, ·)` continuous a minimiser exists
  for every `T` and every sample.
* `gm_popObjective_unique_min` (p. 389): by global identification and `W > 0`, `Q₀` has the
  unique minimiser `θ₀` on `Θ`, with `Q₀(θ₀) = 0`.
* `gm_argmin_stable`: the deterministic heart of the proof ("if `θ̂_T` minimises `Q_T` and `Q_T`
  converges to `Q₀` whose unique minimum is at `θ₀`, then `θ̂_T` must converge to `θ₀`"), in a
  quantitative form: for every `ε > 0` there is `ρ > 0` such that any minimiser of `G'VG` over
  `Θ` with `sup_Θ |G − g| ≤ ρ` and `|V − W| ≤ ρ` (entrywise) lies within `ε` of `θ₀`.
* `theorem_12_1_1` (**Theorem 12.1.1**): under Assumptions 12.1.1–12.1.7, `θ̂_T → θ₀` in
  probability. The proof combines the uniform law of large numbers `gm_ulln` (from Birkhoff's
  theorem) with `gm_argmin_stable`; it needs no measurability of `θ̂_T` (Mathlib's
  `TendstoInMeasure` uses the outer measure). `theorem_12_1_1_ae` is the strong-consistency
  variant when `W_T → W` almost surely.

Departures: of Assumption 12.1.4 only `W > 0` and `W_T → W` are used (positive semidefiniteness
of `W_T` is not needed); Assumption 12.1.2's continuity of `E h` is derived
(`gm_continuousOn_popMoment`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

omit [MeasurableSpace E] in
/-- If a.s. eventually `ω ∉ C_T`, for measurable `C_T`, then `P(C_T) → 0`. -/
theorem gm_tendsto_measure_of_ae_eventually {P : Measure Ω} [IsFiniteMeasure P]
    {C : ℕ → Set Ω} (hC : ∀ T, MeasurableSet (C T)) (h : ∀ᵐ ω ∂P, ∀ᶠ T in atTop, ω ∉ C T) :
    Tendsto (fun T => P (C T)) atTop (𝓝 0) := by
  set A : ℕ → Set Ω := fun N => ⋃ T, ⋃ (_ : N ≤ T), C T with hA
  have hAm : ∀ N, MeasurableSet (A N) := fun N =>
    MeasurableSet.iUnion fun T => MeasurableSet.iUnion fun _ => hC T
  have hanti : Antitone A := by
    intro N M hNM ω hω
    obtain ⟨T, hT, hTC⟩ := Set.mem_iUnion₂.1 hω
    exact Set.mem_iUnion₂.2 ⟨T, le_trans hNM hT, hTC⟩
  have h0 : P (⋂ N, A N) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 h)
    intro ω hω hev
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    obtain ⟨T, hT, hTC⟩ := Set.mem_iUnion₂.1 (Set.mem_iInter.1 hω N)
    exact hN T hT hTC
  have hlim := tendsto_measure_iInter_atTop (fun N => (hAm N).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  rw [h0] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun N => measure_mono fun ω hω => Set.mem_iUnion₂.2 ⟨N, le_rfl, hω⟩

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- `θ ↦ g_T(θ)` is continuous on `Θ` when every `h(x, ·)` is. -/
theorem gm_continuousOn_sampleMoment {k q : ℕ} {X : ℕ → Ω → E} {Θ : Set (Fin k → ℝ)}
    {h : E → (Fin k → ℝ) → Fin q → ℝ} (hc : ∀ x, ContinuousOn (h x) Θ) (T : ℕ) (ω : Ω) :
    ContinuousOn (gm_sampleMoment X h T ω) Θ :=
  continuousOn_pi.2 fun i => continuousOn_const.mul
    (continuousOn_finsetSum _ fun _ _ => continuousOn_pi.1 (hc _) i)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- Miao, p. 388: for compact nonempty `Θ` and continuous `h(x, ·)`, the GMM problem
`min_{θ∈Θ} Q_T(θ)` has a solution for every `T` and every sample. -/
theorem gm_exists_estimator {k q : ℕ} {X : ℕ → Ω → E} {Θ : Set (Fin k → ℝ)}
    (hΘ : IsCompact Θ) (hΘne : Θ.Nonempty) {h : E → (Fin k → ℝ) → Fin q → ℝ}
    (hc : ∀ x, ContinuousOn (h x) Θ) (WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ) :
    ∃ θh : ℕ → Ω → Fin k → ℝ, ∀ T ω, θh T ω ∈ Θ ∧
      ∀ θ ∈ Θ, gm_objective X h WT T ω (θh T ω) ≤ gm_objective X h WT T ω θ := by
  have : ∀ T ω, ∃ θ' ∈ Θ, IsMinOn (gm_objective X h WT T ω) Θ θ' := fun T ω =>
    hΘ.exists_isMinOn hΘne
      ((gm_continuous_quadForm _).comp_continuousOn (gm_continuousOn_sampleMoment hc T ω))
  choose θh hθh hmin using this
  exact ⟨θh, fun T ω => ⟨hθh T ω, fun θ hθ => hmin T ω hθ⟩⟩

omit [MeasurableSpace E] in
/-- Miao, p. 389: by global identification (Assumption 12.1.3) and `W > 0`, the population
objective `Q₀(θ) = E h' W E h` vanishes at `θ₀` and is positive elsewhere on `Θ`; so `θ₀` is its
unique minimiser. -/
theorem gm_popObjective_unique_min {k q : ℕ} {P : Measure Ω} {X : ℕ → Ω → E}
    {h : E → (Fin k → ℝ) → Fin q → ℝ} {Θ : Set (Fin k → ℝ)} {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ)
    (hid : Assumption_12_1_3 P X h Θ θ₀) {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.PosDef) :
    gm_popObjective P X h W θ₀ = 0 ∧ ∀ θ ∈ Θ, θ ≠ θ₀ → 0 < gm_popObjective P X h W θ := by
  refine ⟨by rw [gm_popObjective, (hid θ₀ hθ₀).2 rfl, gm_quadForm_zero], fun θ hθ hne => ?_⟩
  exact gm_quadForm_pos hW fun h0 => hne ((hid θ hθ).1 h0)

/-- Identification gap: away from `θ₀`, `Q₀` is bounded below by a positive constant. -/
theorem gm_identification_gap {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ)
    {g : (Fin k → ℝ) → Fin q → ℝ} (hg : ContinuousOn g Θ) {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.PosDef) {θ₀ : Fin k → ℝ} (hid : ∀ θ ∈ Θ, g θ = 0 ↔ θ = θ₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ θ ∈ Θ, ε ≤ dist θ θ₀ → η ≤ gm_quadForm W (g θ) := by
  set K := Θ ∩ {θ | ε ≤ dist θ θ₀} with hKdef
  have hK : IsCompact K :=
    hΘ.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun θ hθ hd => ?_⟩
    have hmem : θ ∈ K := ⟨hθ, hd⟩
    rw [hKe] at hmem
    exact absurd hmem (Set.notMem_empty θ)
  · obtain ⟨θm, hθm, hmin⟩ := hK.exists_isMinOn hKne
      ((gm_continuous_quadForm W).comp_continuousOn (hg.mono Set.inter_subset_left))
    refine ⟨gm_quadForm W (g θm), gm_quadForm_pos hW ?_, fun θ hθ hd => hmin ⟨hθ, hd⟩⟩
    intro h0
    have he := (hid θm hθm.1).1 h0
    have hd : ε ≤ dist θm θ₀ := hθm.2
    rw [he, dist_self] at hd
    linarith

/-- Perturbation of a trilinear term: `|a'v'b' − awb| ≤ 3ρ(|w| + 1)(B + 1)²`. -/
theorem gm_abs_trilinear_sub {a b w a' b' v' ρ B : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hB : 0 ≤ B)
    (ha : |a| ≤ B) (ha' : |a' - a| ≤ ρ) (hb' : |b' - b| ≤ ρ) (hb : |b| ≤ B)
    (hv : |v' - w| ≤ ρ) : |a' * v' * b' - a * w * b| ≤ ρ * (3 * (|w| + 1) * (B + 1) ^ 2) := by
  have e : a' * v' * b' - a * w * b =
      (a' - a) * v' * b' + a * (v' - w) * b' + a * w * (b' - b) := by ring
  have hv1 : |v'| ≤ |w| + 1 := by
    have := abs_sub_abs_le_abs_sub v' w
    linarith
  have hb1 : |b'| ≤ B + 1 := by
    have := abs_sub_abs_le_abs_sub b' b
    linarith
  have hw := abs_nonneg w
  have t1 : |(a' - a) * v' * b'| ≤ ρ * ((|w| + 1) * (B + 1)) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul ha' (mul_le_mul hv1 hb1 (abs_nonneg _) (by positivity)) (by positivity) hρ0
  have t2 : |a * (v' - w) * b'| ≤ B * (ρ * (B + 1)) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul ha (mul_le_mul hv hb1 (abs_nonneg _) hρ0) (by positivity) hB
  have t3 : |a * w * (b' - b)| ≤ B * (|w| * ρ) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul ha (mul_le_mul le_rfl hb' (abs_nonneg _) hw) (by positivity) hB
  have hbr : (|w| + 1) * (B + 1) + B * (B + 1) + B * |w| ≤ 3 * (|w| + 1) * (B + 1) ^ 2 := by
    nlinarith [mul_nonneg hw hB, mul_nonneg hB hB, mul_nonneg (mul_nonneg hw hB) hB]
  have h3 := abs_add_three ((a' - a) * v' * b') (a * (v' - w) * b') (a * w * (b' - b))
  rw [e]
  have hfin : ρ * ((|w| + 1) * (B + 1)) + B * (ρ * (B + 1)) + B * (|w| * ρ) ≤
      ρ * (3 * (|w| + 1) * (B + 1) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hbr hρ0
    linarith
  linarith

/-- Perturbation of the quadratic form: `|G'VG − g'Wg| ≤ ρ K` with
`K = Σ_{ij} 3(|W_ij| + 1)(B + 1)²` when `|g_i| ≤ B`, `|G_i − g_i| ≤ ρ`, `|V_ij − W_ij| ≤ ρ`,
`ρ ≤ 1`. -/
theorem gm_quadForm_perturb {q : ℕ} {W V : Matrix (Fin q) (Fin q) ℝ} {g G : Fin q → ℝ}
    {ρ B : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hB : 0 ≤ B) (hg : ∀ i, |g i| ≤ B)
    (hG : ∀ i, |G i - g i| ≤ ρ) (hV : ∀ i j, |V i j - W i j| ≤ ρ) :
    |gm_quadForm V G - gm_quadForm W g| ≤
      ρ * ∑ i, ∑ j, 3 * (|W i j| + 1) * (B + 1) ^ 2 := by
  unfold gm_quadForm
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact gm_abs_trilinear_sub hρ0 hρ1 hB (hg i) (hG i) (hG j) (hg j) (hV i j)

/-- Miao, p. 389–390 (the argmin argument behind Theorem 12.1.1, quantitative form): if `θ₀`
uniquely solves `g = 0` on compact `Θ` and `W > 0`, then for every `ε > 0` there is `ρ > 0`
such that every minimiser over `Θ` of `G'VG`, with `G` uniformly `ρ`-close to `g` on `Θ` and `V`
entrywise `ρ`-close to `W`, lies within `ε` of `θ₀`. -/
theorem gm_argmin_stable {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ)
    {g : (Fin k → ℝ) → Fin q → ℝ} (hg : ContinuousOn g Θ) {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.PosDef) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ) (hid : ∀ θ ∈ Θ, g θ = 0 ↔ θ = θ₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ (G : (Fin k → ℝ) → Fin q → ℝ) (V : Matrix (Fin q) (Fin q) ℝ)
      (θh : Fin k → ℝ), (∀ θ ∈ Θ, ∀ i, |G θ i - g θ i| ≤ ρ) → (∀ i j, |V i j - W i j| ≤ ρ) →
      θh ∈ Θ → (∀ θ ∈ Θ, gm_quadForm V (G θh) ≤ gm_quadForm V (G θ)) → dist θh θ₀ < ε := by
  obtain ⟨η, hη, hgap⟩ := gm_identification_gap hΘ hg hW hid hε
  obtain ⟨C, hC⟩ := hΘ.exists_bound_of_continuousOn hg
  set B := max C 0 with hBdef
  have hB : 0 ≤ B := le_max_right _ _
  have hgB : ∀ θ ∈ Θ, ∀ i, |g θ i| ≤ B := fun θ hθ i =>
    ((norm_le_pi_norm (g θ) i).trans (hC θ hθ)).trans (le_max_left _ _)
  set K := ∑ i, ∑ j, 3 * (|W i j| + 1) * (B + 1) ^ 2 with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  set ρ := min 1 (η / (2 * (K + 1))) with hρdef
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρK : ρ * K < η / 2 := by
    have h1 : ρ ≤ η / (2 * (K + 1)) := min_le_right _ _
    have h2 : ρ * K ≤ η / (2 * (K + 1)) * K := mul_le_mul_of_nonneg_right h1 hK
    have h3 : η / (2 * (K + 1)) * K < η / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  refine ⟨ρ, hρ0, fun G V θh hG hV hθh hmin => ?_⟩
  by_contra hcon
  have hd : ε ≤ dist θh θ₀ := not_lt.1 hcon
  have e1 := abs_le.1 (gm_quadForm_perturb hρ0.le hρ1 hB (hgB θh hθh) (hG θh hθh) hV)
  have e0 := abs_le.1 (gm_quadForm_perturb hρ0.le hρ1 hB (hgB θ₀ hθ₀) (hG θ₀ hθ₀) hV)
  have hg0 : g θ₀ = 0 := (hid θ₀ hθ₀).2 rfl
  rw [hg0, gm_quadForm_zero] at e0
  have hgp := hgap θh hθh hd
  have hm := hmin θ₀ hθ₀
  linarith [e1.1, e0.2]

/-- The event "the sample moment is uniformly within `ρ` of the population moment on `Θ`" is
measurable (it is an intersection over a countable dense subset of `Θ`). -/
theorem gm_measurableSet_unif {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} {h : E → (Fin k → ℝ) → Fin q → ℝ}
    (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ) (hc : ∀ x, ContinuousOn (h x) Θ)
    (hgc : ContinuousOn (gm_popMoment P X h) Θ) (ρ : ℝ) (T : ℕ) :
    MeasurableSet {ω | ∀ θ ∈ Θ, ∀ i,
      |gm_sampleMoment X h T ω θ i - gm_popMoment P X h θ i| ≤ ρ} := by
  obtain ⟨C, hCΘ, hCc, hΘC⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace Θ).exists_countable_dense_subset
  have heq : {ω | ∀ θ ∈ Θ, ∀ i,
      |gm_sampleMoment X h T ω θ i - gm_popMoment P X h θ i| ≤ ρ} =
      ⋂ c ∈ C, ⋂ i, {ω | |gm_sampleMoment X h T ω c i - gm_popMoment P X h c i| ≤ ρ} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun H c hc i => H c (hCΘ hc) i, fun H θ hθ i => ?_⟩
    have hφ : ContinuousOn (fun θ => |gm_sampleMoment X h T ω θ i - gm_popMoment P X h θ i|) Θ :=
      ((continuousOn_pi.1 (gm_continuousOn_sampleMoment hc T ω) i).sub
        (continuousOn_pi.1 hgc i)).abs
    exact gm_le_of_mem_closure hCΘ hφ hθ (hΘC hθ) fun c hc => H c hc i
  rw [heq]
  refine MeasurableSet.biInter hCc fun c hc => MeasurableSet.iInter fun i => ?_
  refine measurableSet_le (continuous_abs.measurable.comp (Measurable.sub ?_ measurable_const))
    measurable_const
  exact measurable_const.mul (Finset.measurable_fun_sum _ fun t _ =>
    (measurable_pi_iff.1 (hm c (hCΘ hc)) i).comp (hX t))

/-- **Theorem 12.1.1** (consistency of GMM, Miao, p. 389). Under Assumptions 12.1.1 (strict
stationarity), 12.1.2 (`h(x, ·)` continuous on `Θ`, `h(·, θ)` measurable), 12.1.3 (global
identification), 12.1.4 (`W_T → W > 0` in probability), 12.1.5 (ergodicity), 12.1.6 (`Θ`
compact) and 12.1.7 (dominance), every GMM estimator `θ̂_T ∈ argmin_Θ Q_T` satisfies
`θ̂_T → θ₀` in probability. Proved from Birkhoff's theorem via the uniform law of large numbers
`gm_ulln` and the argmin argument `gm_argmin_stable`. -/
theorem theorem_12_1_1 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ)
    {h : E → (Fin k → ℝ) → Fin q → ℝ} (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ)
    (hc : ∀ x, ContinuousOn (h x) Θ) (hid : Assumption_12_1_3 P X h Θ θ₀)
    (hdom : Assumption_12_1_7 P X h Θ)
    {WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hA4 : Assumption_12_1_4 P WT W)
    {θh : ℕ → Ω → Fin k → ℝ} (hθh : ∀ T ω, θh T ω ∈ Θ)
    (hmin : ∀ T ω, ∀ θ ∈ Θ, gm_objective X h WT T ω (θh T ω) ≤ gm_objective X h WT T ω θ) :
    TendstoInMeasure P θh atTop (fun _ => θ₀) := by
  obtain ⟨-, hW, hWT⟩ := hA4
  have hgc := gm_continuousOn_popMoment hX hm hc hdom
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨ρ, hρ, hstab⟩ := gm_argmin_stable hΘ hgc hW hθ₀ hid hε
  set U : ℕ → Set Ω := fun T => {ω | ∀ θ ∈ Θ, ∀ i,
    |gm_sampleMoment X h T ω θ i - gm_popMoment P X h θ i| ≤ ρ} with hUdef
  set V : ℕ → Fin q → Fin q → Set Ω := fun T i j => {ω | ρ ≤ dist (WT T ω i j) (W i j)}
    with hVdef
  have hsub : ∀ T, {ω | ε ≤ dist (θh T ω) θ₀} ⊆ (U T)ᶜ ∪ ⋃ i, ⋃ j, V T i j := by
    intro T ω hω
    by_contra hn
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_iUnion,
      not_exists] at hn
    obtain ⟨hU, hV⟩ := hn
    have hlt := hstab (gm_sampleMoment X h T ω) (WT T ω) (θh T ω) hU (fun i j => ?_)
      (hθh T ω) (hmin T ω)
    · exact absurd hω (not_le.2 hlt)
    · have hVij : ¬ (ρ ≤ dist (WT T ω i j) (W i j)) := hV i j
      rw [Real.dist_eq, not_le] at hVij
      exact hVij.le
  have hUlim : Tendsto (fun T => P (U T)ᶜ) atTop (𝓝 0) := by
    refine gm_tendsto_measure_of_ae_eventually
      (fun T => (gm_measurableSet_unif hX hm hc hgc ρ T).compl) ?_
    filter_upwards [gm_ulln hX hst herg hΘ hm hc hdom] with ω hω
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hω ρ hρ] with T hT
    simp only [hUdef, Set.mem_compl_iff, not_not]
    intro θ hθ i
    have hle := (dist_le_pi_dist _ _ i).trans (hT θ hθ).le
    rw [Real.dist_eq, abs_sub_comm] at hle
    exact hle
  have hVlim : ∀ i j, Tendsto (fun T => P (V T i j)) atTop (𝓝 0) := fun i j =>
    tendstoInMeasure_iff_dist.1 (hWT i j) ρ hρ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun T => P (U T)ᶜ + ∑ i, ∑ j, P (V T i j)) ?_ (fun _ => zero_le) (fun T => ?_)
  · have := hUlim.add (tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ => hVlim i j)
    simpa using this
  · calc P {ω | ε ≤ dist (θh T ω) θ₀} ≤ P ((U T)ᶜ ∪ ⋃ i, ⋃ j, V T i j) := measure_mono (hsub T)
      _ ≤ P (U T)ᶜ + P (⋃ i, ⋃ j, V T i j) := measure_union_le _ _
      _ ≤ P (U T)ᶜ + ∑ i, ∑ j, P (V T i j) := add_le_add le_rfl
          ((measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun i _ => measure_iUnion_fintype_le _ _))

/-- **Theorem 12.1.1** (strong consistency, Miao, p. 389): if moreover `W_T → W` almost surely,
then `θ̂_T → θ₀` almost surely. -/
theorem theorem_12_1_1_ae {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ)
    {h : E → (Fin k → ℝ) → Fin q → ℝ} (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ)
    (hc : ∀ x, ContinuousOn (h x) Θ) (hid : Assumption_12_1_3 P X h Θ θ₀)
    (hdom : Assumption_12_1_7 P X h Θ)
    {WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ} {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.PosDef)
    (hWT : ∀ᵐ ω ∂P, ∀ i j, Tendsto (fun T => WT T ω i j) atTop (𝓝 (W i j)))
    {θh : ℕ → Ω → Fin k → ℝ} (hθh : ∀ T ω, θh T ω ∈ Θ)
    (hmin : ∀ T ω, ∀ θ ∈ Θ, gm_objective X h WT T ω (θh T ω) ≤ gm_objective X h WT T ω θ) :
    ∀ᵐ ω ∂P, Tendsto (fun T => θh T ω) atTop (𝓝 θ₀) := by
  have hgc := gm_continuousOn_popMoment hX hm hc hdom
  filter_upwards [gm_ulln hX hst herg hΘ hm hc hdom, hWT] with ω hω hWω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ρ, hρ, hstab⟩ := gm_argmin_stable hΘ hgc hW hθ₀ hid hε
  have hev1 := Metric.tendstoUniformlyOn_iff.1 hω ρ hρ
  have hev2 : ∀ᶠ T in atTop, ∀ i j, dist (WT T ω i j) (W i j) < ρ :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Metric.tendsto_nhds.1 (hWω i j) ρ hρ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev1.and hev2)
  refine ⟨N, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hN T hT
  refine hstab (gm_sampleMoment X h T ω) (WT T ω) (θh T ω) (fun θ hθ i => ?_)
    (fun i j => ?_) (hθh T ω) (hmin T ω)
  · have hle := (dist_le_pi_dist _ _ i).trans (h1 θ hθ).le
    rw [Real.dist_eq, abs_sub_comm] at hle
    exact hle
  · have := h2 i j
    rw [Real.dist_eq] at this
    exact this.le

end Miao.StructuralEstimation
