/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RBModel
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The stochastic planner's problem of the basic RBC model

Miao, §14.2, p. 472: the planner's problem (14.22)–(14.25), its Euler equation (14.26), the
intratemporal condition (14.27) and "the usual transversality condition", on a probability
space `(Ω, μ)` with a filtration `ℱ`; `E_t` is Mathlib's conditional expectation `μ[·|ℱ t]`.

* `rb_IsFeasible`: positive consumption, `N_t ∈ [0, 1)`, `K_t ≥ 0`, and the resource constraint
  (14.23) with (14.24), `C_t + K_{t+1} = z_tK_t^αN_t^{1−α} + (1 − δ)K_t`.
* `eq_14_26`: `1/C_t = E_t[β(αz_{t+1}K_{t+1}^{α−1}N_{t+1}^{1−α} + 1 − δ)/C_{t+1}]` a.e.;
  `rb_TVC`: `βᵀE[K_{T+1}/C_T] → 0`.
* **Sufficiency** (`rb_planner_suff`, `rb_planner_optimal`): an interior feasible plan
  satisfying (14.26), (14.27) and transversality is optimal: for every feasible adapted
  alternative with the same `K_0`, `∑_{t≤T} βᵗE[u'_t] ≤ ∑_{t≤T} βᵗE[u_t] + βᵀE[K_{T+1}/C_T]`, so
  the expected discounted utility of the alternative is at most that of the plan. The proof
  is the concavity argument (`rb_cd_tangent`, `rb_u_tangent`) with the Euler equation used
  through the pull-out property of `E_t` and a telescoping sum (`rb_suff_core`), which
  `RBEquilibrium` reuses for the household.
* **Non-vacuity** (`rb_bm_solution`): with full depreciation `δ = 1` and a deterministic TFP
  path, `K_{t+1} = αβY_t`, `C_t = (1 − αβ)Y_t`, `N_t = (1 − α)/(1 − α + χ(1 − αβ))` is feasible
  and satisfies (14.26), (14.27), transversality and the integrability hypotheses of
  `rb_planner_suff`, on every probability space.

**Departures.** The book asserts the first-order conditions are satisfied by the optimum; here
the converse (sufficiency, with transversality) is proved in the stochastic setting, and the
necessity of (14.26)–(14.27) is proved for the one-step variations in `RBModel`
(`rb_labour_nec`, `rb_euler_node_nec`). Integrability of the terms involved is assumed
explicitly. The expected discounted utility is the limit of the expected partial sums.
-/

open MeasureTheory Filter Topology

namespace Miao.NeoclassicalGrowth

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The telescoping identity: if `a₀ = 0` and `βa_{t+1} = b_t`, then
`∑_{t≤T} βᵗ(a_t − b_t) = −βᵀb_T`. -/
theorem rb_telescope (β : ℝ) (a b : ℕ → ℝ) (h0 : a 0 = 0) (h : ∀ t, β * a (t + 1) = b t)
    (T : ℕ) : ∑ t ∈ Finset.range (T + 1), β ^ t * (a t - b t) = -β ^ T * b T := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, ← h T]
    ring

/-- The Euler equation through the pull-out property: if `B = E_m[βA]` a.e. and `X` is
`m`-measurable, then `βE[XA] = E[XB]`. -/
theorem rb_integral_euler (μ : Measure Ω) [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {A B X : Ω → ℝ} (β : ℝ) (hX : StronglyMeasurable[m] X)
    (hXA : Integrable (fun ω => X ω * A ω) μ) (hA : Integrable A μ)
    (heul : B =ᵐ[μ] μ[fun ω => β * A ω | m]) :
    β * ∫ ω, X ω * A ω ∂μ = ∫ ω, X ω * B ω ∂μ := by
  have hg : Integrable (fun ω => β * A ω) μ := hA.const_mul β
  have hfg : Integrable (X * fun ω => β * A ω) μ := by
    have := hXA.const_mul β
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]
    ring
  have hpull := condExp_mul_of_stronglyMeasurable_left hX hfg hg
  have h1 : ∫ ω, X ω * B ω ∂μ = ∫ ω, (X * μ[fun ω => β * A ω | m]) ω ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [heul] with ω hω
    simp only [Pi.mul_apply, hω]
  rw [h1, ← integral_congr_ae hpull, integral_condExp hm, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [Pi.mul_apply]
  ring

/-- The core of the sufficiency argument (Miao, p. 472, "the usual transversality condition";
cf. Theorem 7.5.2). If the one-period gains satisfy `d_t ≤ A_tΔ_t − B_tΔ_{t+1}`, `Δ₀ = 0`,
`Δ_{t+1}` is `ℱ_t`-measurable and `B_t = E_t[βA_{t+1}]` (the Euler equation), then
`∑_{t≤T} βᵗE[d_t] ≤ −βᵀE[B_TΔ_{T+1}]`. -/
theorem rb_suff_core (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {β : ℝ}
    (hβ : 0 ≤ β) (d A B Δ : ℕ → Ω → ℝ)
    (hd : ∀ t ω, d t ω ≤ A t ω * Δ t ω - B t ω * Δ (t + 1) ω) (hΔ0 : ∀ ω, Δ 0 ω = 0)
    (hΔm : ∀ t, StronglyMeasurable[ℱ t] (Δ (t + 1)))
    (heul : ∀ t, B t =ᵐ[μ] μ[fun ω => β * A (t + 1) ω | ℱ t])
    (hdi : ∀ t, Integrable (d t) μ) (hAΔ : ∀ t, Integrable (fun ω => A t ω * Δ t ω) μ)
    (hBΔ : ∀ t, Integrable (fun ω => B t ω * Δ (t + 1) ω) μ) (hAi : ∀ t, Integrable (A t) μ)
    (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, d t ω ∂μ ≤
      -β ^ T * ∫ ω, B T ω * Δ (T + 1) ω ∂μ := by
  set a : ℕ → ℝ := fun t => ∫ ω, A t ω * Δ t ω ∂μ
  set b : ℕ → ℝ := fun t => ∫ ω, B t ω * Δ (t + 1) ω ∂μ
  have ha0 : a 0 = 0 := by simp [a, hΔ0]
  have hab : ∀ t, β * a (t + 1) = b t := fun t => by
    have h := rb_integral_euler μ (ℱ.le t) β (hΔm t)
      ((hAΔ (t + 1)).congr (Eventually.of_forall fun ω => mul_comm _ _)) (hAi (t + 1)) (heul t)
    simp only [a, b]
    rw [integral_congr_ae (Eventually.of_forall fun ω => mul_comm (A (t + 1) ω) _), h]
    exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  have hle : ∀ t, ∫ ω, d t ω ∂μ ≤ a t - b t := fun t => by
    simp only [a, b]
    rw [← integral_sub (hAΔ t) (hBΔ t)]
    exact integral_mono (hdi t) ((hAΔ t).sub (hBΔ t)) fun ω => hd t ω
  calc ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, d t ω ∂μ
      ≤ ∑ t ∈ Finset.range (T + 1), β ^ t * (a t - b t) :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hle t) (pow_nonneg hβ t)
    _ = -β ^ T * b T := rb_telescope β a b ha0 hab T

/-! ### The planner's problem -/

/-- A feasible allocation of the planner (Miao, (14.23)–(14.24), p. 472), with investment
eliminated: `C_t > 0`, `0 ≤ N_t < 1`, `K_t ≥ 0` and
`C_t + K_{t+1} = z_tK_t^αN_t^{1−α} + (1 − δ)K_t`. -/
def rb_IsFeasible (α δ : ℝ) (z C N K : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, 0 < C t ω ∧ 0 ≤ N t ω ∧ N t ω < 1 ∧ 0 ≤ K t ω ∧
    C t ω + K (t + 1) ω = rb_Y α (z t ω) (K t ω) (N t ω) + (1 - δ) * K t ω

/-- The gross return on capital `R_{t} = αz_tK_t^{α−1}N_t^{1−α} + 1 − δ` divided by `C_t`. -/
noncomputable def rb_A (α δ : ℝ) (z C N K : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (rb_MPK α (z t ω) (K t ω) (N t ω) + 1 - δ) / C t ω

/-- Miao, (14.26), p. 472: the Euler equation
`1/C_t = E_t[β(αz_{t+1}K_{t+1}^{α−1}N_{t+1}^{1−α} + 1 − δ)/C_{t+1}]` (a.e.). -/
def eq_14_26 (μ : Measure Ω) (ℱ : Filtration ℕ m0) (α β δ : ℝ) (z C N K : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, (fun ω => 1 / C t ω) =ᵐ[μ] μ[fun ω => β * rb_A α δ z C N K (t + 1) ω | ℱ t]

/-- The transversality condition `lim βᵀE[K_{T+1}/C_T] = 0` (Miao, p. 472). -/
def rb_TVC (μ : Measure Ω) (β : ℝ) (C K : ℕ → Ω → ℝ) : Prop :=
  Tendsto (fun T : ℕ => β ^ T * ∫ ω, K (T + 1) ω / C T ω ∂μ) atTop (𝓝 0)

/-- Expected discounted utility up to date `T` (Miao, (14.22)). -/
noncomputable def rb_value (μ : Measure Ω) (β χ : ℝ) (C N : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, rb_u χ (C t ω) (N t ω) ∂μ

/-- The pointwise one-period inequality of the planner: if (14.27) holds for the plan,
`u(C'_t, N'_t) − u(C_t, N_t) ≤ A_t(K'_t − K_t) − (K'_{t+1} − K_{t+1})/C_t`. -/
theorem rb_planner_pointwise {α δ χ z C N K C' N' K' K₁ K₁' : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hχ : 0 ≤ χ) (hz : 0 ≤ z) (hC : 0 < C) (hN0 : 0 < N) (hN1 : N < 1) (hK : 0 < K)
    (hC' : 0 < C') (hN0' : 0 ≤ N') (hN1' : N' < 1) (hK' : 0 ≤ K')
    (hres : C + K₁ = rb_Y α z K N + (1 - δ) * K)
    (hres' : C' + K₁' = rb_Y α z K' N' + (1 - δ) * K') (hfoc : eq_14_27 α χ z K C N) :
    rb_u χ C' N' - rb_u χ C N ≤
      (rb_MPK α z K N + 1 - δ) / C * (K' - K) - 1 / C * (K₁' - K₁) := by
  have ht := rb_u_tangent hχ hC hN1 hC' hN1'
  have hY := rb_cd_tangent' hα0 hα1 hz hK hN0 hK' hN0'
  have h1N : 0 < 1 - N := by linarith
  have hw : χ * ((N' - N) / (1 - N)) = rb_MPL α z K N * (N' - N) / C := by
    rw [eq_14_27] at hfoc
    rw [← hfoc]
    field_simp
  have hq : (C' - C) / C ≤ ((rb_MPK α z K N + 1 - δ) * (K' - K) +
      rb_MPL α z K N * (N' - N) - (K₁' - K₁)) / C := by
    apply div_le_div_of_nonneg_right _ hC.le
    linarith
  have : ((rb_MPK α z K N + 1 - δ) * (K' - K) + rb_MPL α z K N * (N' - N) - (K₁' - K₁)) / C =
      (rb_MPK α z K N + 1 - δ) / C * (K' - K) + rb_MPL α z K N * (N' - N) / C -
        1 / C * (K₁' - K₁) := by
    field_simp
  linarith

/-- **Sufficiency of (14.26), (14.27)** (Miao, §14.2, p. 472). Let `(C, N, K)` be feasible with
`K_t > 0`, `N_t ∈ (0, 1)`, adapted (`K_{t+1}` is `ℱ_t`-measurable), satisfying (14.27) at every
date and state and the Euler equation (14.26). Then for every feasible alternative
`(C', N', K')` with `K'_0 = K_0` and `K'_{t+1}` `ℱ_t`-measurable, and every `T`,
`∑_{t≤T} βᵗE[u(C'_t, N'_t)] ≤ ∑_{t≤T} βᵗE[u(C_t, N_t)] + βᵀE[K_{T+1}/C_T]`
(integrability of the terms involved is assumed). -/
theorem rb_planner_suff (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    {α β δ χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β) (hχ : 0 ≤ χ)
    {z C N K C' N' K' : ℕ → Ω → ℝ} (hz : ∀ t ω, 0 ≤ z t ω) (hF : rb_IsFeasible α δ z C N K)
    (hK : ∀ t ω, 0 < K t ω) (hN : ∀ t ω, 0 < N t ω)
    (hfoc : ∀ t ω, eq_14_27 α χ (z t ω) (K t ω) (C t ω) (N t ω))
    (heul : eq_14_26 μ ℱ α β δ z C N K)
    (hKm : ∀ t, StronglyMeasurable[ℱ t] (K (t + 1)))
    (hui : ∀ t, Integrable (fun ω => rb_u χ (C t ω) (N t ω)) μ)
    (hAi : ∀ t, Integrable (rb_A α δ z C N K t) μ)
    (hAK : ∀ t, Integrable (fun ω => rb_A α δ z C N K t ω * K t ω) μ)
    (hBK : ∀ t, Integrable (fun ω => K (t + 1) ω / C t ω) μ)
    (hF' : rb_IsFeasible α δ z C' N' K') (h0 : ∀ ω, K' 0 ω = K 0 ω)
    (hKm' : ∀ t, StronglyMeasurable[ℱ t] (K' (t + 1)))
    (hui' : ∀ t, Integrable (fun ω => rb_u χ (C' t ω) (N' t ω)) μ)
    (hAK' : ∀ t, Integrable (fun ω => rb_A α δ z C N K t ω * K' t ω) μ)
    (hBK' : ∀ t, Integrable (fun ω => K' (t + 1) ω / C t ω) μ) (T : ℕ) :
    rb_value μ β χ C' N' T ≤
      rb_value μ β χ C N T + β ^ T * ∫ ω, K (T + 1) ω / C T ω ∂μ := by
  set d : ℕ → Ω → ℝ := fun t ω => rb_u χ (C' t ω) (N' t ω) - rb_u χ (C t ω) (N t ω)
  set Δ : ℕ → Ω → ℝ := fun t ω => K' t ω - K t ω
  set B : ℕ → Ω → ℝ := fun t ω => 1 / C t ω
  have hBΔ : ∀ t, Integrable (fun ω => B t ω * Δ (t + 1) ω) μ := fun t =>
    ((hBK' t).sub (hBK t)).congr (Eventually.of_forall fun ω => by
      simp only [B, Δ, Pi.sub_apply]; ring)
  have hcore := rb_suff_core μ ℱ hβ d (rb_A α δ z C N K) B Δ
    (fun t ω => by
      obtain ⟨hC, hN0, hN1, -, hres⟩ := hF t ω
      obtain ⟨hC', hN0', hN1', hK', hres'⟩ := hF' t ω
      exact rb_planner_pointwise hα0 hα1 hχ (hz t ω) hC (hN t ω) hN1 (hK t ω) hC' hN0'
        hN1' hK' hres hres' (hfoc t ω))
    (fun ω => by simp [Δ, h0]) (fun t => (hKm' t).sub (hKm t))
    (fun t => heul t) (fun t => (hui' t).sub (hui t))
    (fun t => ((hAK' t).sub (hAK t)).congr (Eventually.of_forall fun ω => by
      simp only [Δ, Pi.sub_apply]; ring)) hBΔ hAi T
  have hsplit : ∀ t, ∫ ω, d t ω ∂μ =
      ∫ ω, rb_u χ (C' t ω) (N' t ω) ∂μ - ∫ ω, rb_u χ (C t ω) (N t ω) ∂μ :=
    fun t => integral_sub (hui' t) (hui t)
  have hlast : -β ^ T * ∫ ω, B T ω * Δ (T + 1) ω ∂μ ≤
      β ^ T * ∫ ω, K (T + 1) ω / C T ω ∂μ := by
    have hint : ∫ ω, B T ω * Δ (T + 1) ω ∂μ =
        ∫ ω, K' (T + 1) ω / C T ω ∂μ - ∫ ω, K (T + 1) ω / C T ω ∂μ := by
      rw [← integral_sub (hBK' T) (hBK T)]
      exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [B, Δ]; ring)
    have hpos : 0 ≤ ∫ ω, K' (T + 1) ω / C T ω ∂μ :=
      integral_nonneg fun ω => div_nonneg (hF' (T + 1) ω).2.2.2.1 (hF T ω).1.le
    rw [hint]
    have := pow_nonneg hβ T
    nlinarith
  simp only [hsplit] at hcore
  unfold rb_value
  have hs : ∑ t ∈ Finset.range (T + 1), β ^ t * (∫ ω, rb_u χ (C' t ω) (N' t ω) ∂μ -
      ∫ ω, rb_u χ (C t ω) (N t ω) ∂μ) =
      ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, rb_u χ (C' t ω) (N' t ω) ∂μ -
        ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, rb_u χ (C t ω) (N t ω) ∂μ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hs] at hcore
  linarith

/-- **Optimality** (Miao, §14.2, p. 472): under the hypotheses of `rb_planner_suff` and the
transversality condition, if the expected discounted utilities of the plan and of the
alternative converge (to `V` and `V'`), then `V' ≤ V`. -/
theorem rb_planner_optimal (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    {α β δ χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β) (hχ : 0 ≤ χ)
    {z C N K C' N' K' : ℕ → Ω → ℝ} (hz : ∀ t ω, 0 ≤ z t ω) (hF : rb_IsFeasible α δ z C N K)
    (hK : ∀ t ω, 0 < K t ω) (hN : ∀ t ω, 0 < N t ω)
    (hfoc : ∀ t ω, eq_14_27 α χ (z t ω) (K t ω) (C t ω) (N t ω))
    (heul : eq_14_26 μ ℱ α β δ z C N K) (htvc : rb_TVC μ β C K)
    (hKm : ∀ t, StronglyMeasurable[ℱ t] (K (t + 1)))
    (hui : ∀ t, Integrable (fun ω => rb_u χ (C t ω) (N t ω)) μ)
    (hAi : ∀ t, Integrable (rb_A α δ z C N K t) μ)
    (hAK : ∀ t, Integrable (fun ω => rb_A α δ z C N K t ω * K t ω) μ)
    (hBK : ∀ t, Integrable (fun ω => K (t + 1) ω / C t ω) μ)
    (hF' : rb_IsFeasible α δ z C' N' K') (h0 : ∀ ω, K' 0 ω = K 0 ω)
    (hKm' : ∀ t, StronglyMeasurable[ℱ t] (K' (t + 1)))
    (hui' : ∀ t, Integrable (fun ω => rb_u χ (C' t ω) (N' t ω)) μ)
    (hAK' : ∀ t, Integrable (fun ω => rb_A α δ z C N K t ω * K' t ω) μ)
    (hBK' : ∀ t, Integrable (fun ω => K' (t + 1) ω / C t ω) μ) {V V' : ℝ}
    (hV : Tendsto (rb_value μ β χ C N) atTop (𝓝 V))
    (hV' : Tendsto (rb_value μ β χ C' N') atTop (𝓝 V')) : V' ≤ V := by
  have hlim : Tendsto (fun T => rb_value μ β χ C N T + β ^ T * ∫ ω, K (T + 1) ω / C T ω ∂μ)
      atTop (𝓝 (V + 0)) := hV.add htvc
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto' hV' hlim fun T =>
    rb_planner_suff μ ℱ hα0 hα1 hβ hχ hz hF hK hN hfoc heul hKm hui hAi hAK hBK hF' h0 hKm'
      hui' hAK' hBK' T

/-! ### A concrete solution: full depreciation -/

/-- Hours in the full-depreciation solution, `N = (1 − α)/(1 − α + χ(1 − αβ))`. -/
noncomputable def rb_bmN (α β χ : ℝ) : ℝ := (1 - α) / (1 - α + χ * (1 - α * β))

/-- Capital in the full-depreciation solution: `K_{t+1} = αβz_tK_t^αN^{1−α}`. -/
noncomputable def rb_bmK (α β χ : ℝ) (zs : ℕ → ℝ) (k0 : ℝ) : ℕ → ℝ
  | 0 => k0
  | t + 1 => α * β * rb_Y α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ)

/-- Consumption in the full-depreciation solution: `C_t = (1 − αβ)z_tK_t^αN^{1−α}`. -/
noncomputable def rb_bmC (α β χ : ℝ) (zs : ℕ → ℝ) (k0 : ℝ) (t : ℕ) : ℝ :=
  (1 - α * β) * rb_Y α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ)

theorem rb_bmN_mem {α β χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hχ : 0 < χ) : 0 < rb_bmN α β χ ∧ rb_bmN α β χ < 1 := by
  have h1 : 0 < 1 - α * β := by nlinarith
  have h2 : 0 < χ * (1 - α * β) := mul_pos hχ h1
  unfold rb_bmN
  constructor
  · exact div_pos (by linarith) (by linarith)
  · rw [div_lt_one (by linarith)]
    linarith

theorem rb_bmK_pos {α β χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hχ : 0 < χ) {zs : ℕ → ℝ} (hzs : ∀ t, 0 < zs t) {k0 : ℝ} (hk0 : 0 < k0) (t : ℕ) :
    0 < rb_bmK α β χ zs k0 t := by
  induction t with
  | zero => exact hk0
  | succ t ih =>
    have := rb_Y_pos (α := α) (hzs t) ih (rb_bmN_mem hα0 hα1 hβ1 hχ).1
    simp only [rb_bmK]
    positivity

/-- **The full-depreciation solution** (Miao, §14.2 with `δ = 1`; Long and Plosser (1983)).
With `δ = 1` and a deterministic TFP path `z_t > 0`, the allocation `K_{t+1} = αβY_t`,
`C_t = (1 − αβ)Y_t`, `N_t = (1 − α)/(1 − α + χ(1 − αβ))` (constant random variables on any
probability space) is feasible, interior, adapted, satisfies (14.27) and (14.26), the
transversality condition, and all the integrability hypotheses of `rb_planner_suff`. In
particular those hypotheses are satisfiable, and by `rb_planner_optimal` this allocation is
optimal. -/
theorem rb_bm_solution (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {α β χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hχ : 0 < χ)
    {zs : ℕ → ℝ} (hzs : ∀ t, 0 < zs t) {k0 : ℝ} (hk0 : 0 < k0) :
    let z : ℕ → Ω → ℝ := fun t _ => zs t
    let C : ℕ → Ω → ℝ := fun t _ => rb_bmC α β χ zs k0 t
    let N : ℕ → Ω → ℝ := fun _ _ => rb_bmN α β χ
    let K : ℕ → Ω → ℝ := fun t _ => rb_bmK α β χ zs k0 t
    rb_IsFeasible α 1 z C N K ∧ (∀ t ω, 0 < K t ω) ∧ (∀ t ω, 0 < N t ω) ∧
      (∀ t ω, eq_14_27 α χ (z t ω) (K t ω) (C t ω) (N t ω)) ∧ eq_14_26 μ ℱ α β 1 z C N K ∧
      rb_TVC μ β C K ∧ (∀ t, StronglyMeasurable[ℱ t] (K (t + 1))) ∧
      (∀ t, Integrable (fun ω => rb_u χ (C t ω) (N t ω)) μ) ∧
      (∀ t, Integrable (rb_A α 1 z C N K t) μ) ∧
      (∀ t, Integrable (fun ω => rb_A α 1 z C N K t ω * K t ω) μ) ∧
      (∀ t, Integrable (fun ω => K (t + 1) ω / C t ω) μ) := by
  intro z C N K
  obtain ⟨hn0, hn1⟩ := rb_bmN_mem hα0 hα1 hβ1 hχ
  have hab : 0 < 1 - α * β := by nlinarith
  have hKp := rb_bmK_pos hα0 hα1 hβ0 hβ1 hχ hzs hk0
  have hY : ∀ t, 0 < rb_Y α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ) := fun t =>
    rb_Y_pos (hzs t) (hKp t) hn0
  have hCp : ∀ t, 0 < rb_bmC α β χ zs k0 t := fun t => mul_pos hab (hY t)
  refine ⟨fun t ω => ⟨hCp t, hn0.le, hn1, (hKp t).le, ?_⟩, fun t ω => hKp t, fun t ω => hn0,
    fun t ω => ?_, fun t => ?_, ?_, fun t => stronglyMeasurable_const,
    fun t => by simp only [C, N]; exact integrable_const _,
    fun t => by simp only [C, N, K, z]; exact integrable_const _,
    fun t => by simp only [rb_A, C, N, K, z]; exact integrable_const _,
    fun t => by simp only [C, K]; exact integrable_const _⟩
  · simp only [C, K, z, N, rb_bmC, rb_bmK]
    ring
  · simp only [eq_14_27, C, K, z, N]
    rw [rb_MPL_eq _ _ _ hn0, rb_bmC]
    have h1n : 0 < 1 - rb_bmN α β χ := by linarith
    rw [div_eq_div_iff h1n.ne' hn0.ne']
    have hden : 0 < 1 - α + χ * (1 - α * β) := by nlinarith
    simp only [rb_bmN]
    field_simp
    ring
  · have hc : (fun ω : Ω => β * rb_A α 1 z C N K (t + 1) ω) =
        fun _ => 1 / rb_bmC α β χ zs k0 t := by
      funext ω
      simp only [rb_A, C, K, z, N]
      rw [rb_MPK_eq _ _ (hKp (t + 1)), rb_bmC, rb_bmC]
      have hY1 := hY (t + 1)
      have := hY t
      set Y1 := rb_Y α (zs (t + 1)) (rb_bmK α β χ zs k0 (t + 1)) (rb_bmN α β χ)
      set Y0 := rb_Y α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ)
      have hK1 : rb_bmK α β χ zs k0 (t + 1) = α * β * Y0 := rfl
      rw [hK1]
      field_simp
      ring
    rw [hc, condExp_const (ℱ.le t)]
  · simp only [rb_TVC, K, C, integral_const, smul_eq_mul, probReal_univ, one_mul]
    have hr : ∀ T : ℕ, β ^ T * (rb_bmK α β χ zs k0 (T + 1) / rb_bmC α β χ zs k0 T) =
        β ^ T * (α * β / (1 - α * β)) := fun T => by
      congr 1
      rw [rb_bmC]
      simp only [rb_bmK]
      have := hY T
      field_simp
    simp only [hr]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (α * β / (1 - α * β))
    simpa using this

end Miao.NeoclassicalGrowth
