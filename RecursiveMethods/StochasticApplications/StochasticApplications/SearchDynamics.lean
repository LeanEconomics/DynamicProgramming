/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.SearchReservation

/-!
# The dynamics of the search model

SLP §10.8, pp. 308–310. Under the reservation-wage policy, wage offers follow the transition
function `P` on `W = [0, w̄]` (1a)–(1b): from an unacceptable offer `w < w*` the next offer is
drawn from `μ`; from an acceptable one `w ≥ w*` the wage is kept with probability `1 − θ` and
drops to `0` with probability `θ` (`searchP`). Let `λₜ = T*ᵗλ₀` (`searchLaw`) and
`Aᶜ = [0, w*)`, with `0 < w*` and `0 < θ < 1`.

* `searchP_adjoint`: `λₜ₊₁(B) = μ(B) λₜ(Aᶜ) + θ 1_B(0) λₜ(A) + (1 − θ) λₜ(A ∩ B)`.
* `tendsto_affine_rec`: if `|a| < 1` and `bₜ → b`, solutions of `xₜ₊₁ = a xₜ + bₜ` converge to
  `b/(1 − a)`; in particular the difference equation (2) is stable.
* **Exercise 10.8a** (`ex_10_8a`): `λₜ₊₁(Aᶜ) = θ + λₜ(Aᶜ)[μ(Aᶜ) − θ]` (2), and
  `λₜ(Aᶜ) → θ/(θ + μ(A))` (3).
* **Exercise 10.8b** (`ex_10_8b_zero`, `ex_10_8b`): for `C ⊆ Aᶜ`, the recursion and limit (4)
  if `0 ∈ C`, and (5) if `0 ∉ C`.
* **Exercise 10.8c** (`ex_10_8c`): for `C ⊆ A`, `λₜ(C) → [θ/(θ + μ(A))] μ(C)/θ` (6).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- **Stability.** If `|a| < 1` and `bₜ → b`, every solution of `xₜ₊₁ = a xₜ + bₜ` converges to
`b/(1 − a)`. -/
theorem tendsto_affine_rec {a : ℝ} (ha : |a| < 1) {b : ℕ → ℝ} {L : ℝ}
    (hb : Tendsto b atTop (𝓝 L)) {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = a * x t + b t) :
    Tendsto x atTop (𝓝 (L / (1 - a))) := by
  have ha1 : 0 < 1 - a := by linarith [le_abs_self a]
  set c := L / (1 - a)
  have hc : c = a * c + L := by
    simp only [c]; field_simp; ring
  set r := |a|
  have hr0 : 0 ≤ r := abs_nonneg a
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hr1 : 0 < 1 - r := by linarith
  have hε' : 0 < ε * (1 - r) / 2 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hb _ hε'
  have hstep : ∀ k, |x (N + k) - c| ≤ r ^ k * |x N - c| + ε / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have hb' := hN (N + k) (by omega)
      rw [Real.dist_eq] at hb'
      have e : x (N + (k + 1)) - c = a * (x (N + k) - c) + (b (N + k) - L) := by
        rw [show N + (k + 1) = N + k + 1 by ring, hx]
        linear_combination (-1 : ℝ) * hc
      rw [e]
      calc |a * (x (N + k) - c) + (b (N + k) - L)|
          ≤ r * |x (N + k) - c| + |b (N + k) - L| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ r * (r ^ k * |x N - c| + ε / 2) + ε * (1 - r) / 2 :=
            add_le_add (mul_le_mul_of_nonneg_left ih hr0) hb'.le
        _ = r ^ (k + 1) * |x N - c| + ε / 2 := by ring
  obtain ⟨K, hK⟩ := (tendsto_order.1 ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 ha).mul_const
    |x N - c|)).2 (ε / 2) (by rw [zero_mul]; linarith)
  |>.exists_forall_of_atTop
  refine ⟨N + K, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = N + k := ⟨t - N, by omega⟩
  rw [Real.dist_eq]
  have := hK k (by omega)
  linarith [hstep k]

variable {wbar θ : ℝ} (hw : 0 ≤ wbar)

/-- The wage after a job-loss shock: `0` if `d = 0`, the current wage if `d = 1`. -/
def stayMap (p : Icc (0 : ℝ) wbar × Two) : Icc (0 : ℝ) wbar :=
  if p.2 = two0 then w0 hw else p.1

theorem measurable_stayMap : Measurable (stayMap hw) := by
  classical
  exact Measurable.ite (measurable_snd (measurableSet_singleton two0)) measurable_const
    measurable_fst

/-- The transition function (1a)–(1b) of wage offers under the reservation-wage policy. -/
noncomputable def searchP (θ : ℝ) (μ : Measure (Icc (0 : ℝ) wbar)) (ws : Icc (0 : ℝ) wbar) :
    Kernel (Icc (0 : ℝ) wbar) (Icc (0 : ℝ) wbar) :=
  Kernel.piecewise (measurableSet_Iio (a := ws)) (Kernel.const _ μ)
    ((Kernel.deterministic id measurable_id ×ₖ Kernel.const _ (lossMeasure θ)).map (stayMap hw))

variable (μ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure μ] (ws : Icc (0 : ℝ) wbar)

omit [IsProbabilityMeasure μ] in
/-- (1b): from an acceptable offer, `P(w, B) = θ 1_B(0) + (1 − θ) 1_B(w)`. -/
theorem searchP_apply_ge (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {w : Icc (0 : ℝ) wbar} (hw' : ws ≤ w)
    {B : Set (Icc (0 : ℝ) wbar)} (hB : MeasurableSet B) :
    searchP hw θ μ ws w B = ENNReal.ofReal θ * B.indicator 1 (w0 hw) +
      ENNReal.ofReal (1 - θ) * B.indicator 1 w := by
  have : IsProbabilityMeasure (lossMeasure θ) := isProbabilityMeasure_lossMeasure hθ0 hθ1
  have hnot : w ∉ Iio ws := not_lt.2 hw'
  simp only [searchP, Kernel.piecewise_apply, hnot, ↓reduceIte]
  rw [Kernel.map_apply' _ (measurable_stayMap hw) _ hB, Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left ((measurable_stayMap hw) hB)]
  simp only [lossMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply, Measure.dirac_apply]
  by_cases h1 : w0 hw ∈ B <;> by_cases h2 : w ∈ B <;>
    simp [stayMap, h1, h2, Set.indicator, two0_ne_two1.symm]

omit [IsProbabilityMeasure μ] in
/-- `λₜ₊₁(B) = μ(B) λₜ(Aᶜ) + θ 1_B(0) λₜ(A) + (1 − θ) λₜ(A ∩ B)`. -/
theorem searchP_adjoint (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (lam : Measure (Icc (0 : ℝ) wbar))
    {B : Set (Icc (0 : ℝ) wbar)} (hB : MeasurableSet B) :
    adjointOp (searchP hw θ μ ws) lam B = μ B * lam (Iio ws) +
      ENNReal.ofReal θ * B.indicator 1 (w0 hw) * lam (Ici ws) +
        ENNReal.ofReal (1 - θ) * lam (B ∩ Ici ws) := by
  rw [adjointOp_apply _ _ hB, ← lintegral_add_compl _ (measurableSet_Iio (a := ws)), compl_Iio]
  rw [setLIntegral_congr_fun (g := fun _ => μ B) measurableSet_Iio fun w hw' => by
      simp only [searchP, Kernel.piecewise_apply, hw', ↓reduceIte, Kernel.const_apply],
    setLIntegral_congr_fun measurableSet_Ici fun w hw' => searchP_apply_ge hw μ ws hθ0 hθ1 hw' hB,
    setLIntegral_const, lintegral_add_left measurable_const, setLIntegral_const,
    lintegral_const_mul _ (measurable_one.indicator hB), lintegral_indicator_one hB,
    Measure.restrict_apply hB]
  ring

/-- The marginal laws `λₜ = T*ᵗλ₀` of the wage offer. -/
noncomputable def searchLaw (θ : ℝ) (lam₀ : Measure (Icc (0 : ℝ) wbar)) (t : ℕ) :
    Measure (Icc (0 : ℝ) wbar) :=
  (adjointOp (searchP hw θ μ ws))^[t] lam₀

omit [IsProbabilityMeasure μ] in
theorem searchLaw_succ (θ : ℝ) (lam₀ : Measure (Icc (0 : ℝ) wbar)) (t : ℕ) :
    searchLaw hw μ ws θ lam₀ (t + 1) = adjointOp (searchP hw θ μ ws) (searchLaw hw μ ws θ lam₀ t) :=
  Function.iterate_succ_apply' _ _ _

/-- Each `λₜ` is a probability measure. -/
theorem searchLaw_prob (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (lam₀ : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure lam₀] (t : ℕ) : IsProbabilityMeasure (searchLaw hw μ ws θ lam₀ t) := by
  induction t with
  | zero => exact ‹_›
  | succ t ih =>
    refine ⟨?_⟩
    rw [searchLaw_succ, searchP_adjoint hw μ ws hθ0 hθ1 _ MeasurableSet.univ]
    simp only [measure_univ, one_mul, Set.indicator_univ, Pi.one_apply, mul_one, univ_inter]
    have h1 : ENNReal.ofReal θ + ENNReal.ofReal (1 - θ) = 1 := by
      rw [← ENNReal.ofReal_add hθ0 (by linarith)]; simp
    have hd : Disjoint (Iio ws) (Ici ws) := Set.disjoint_left.2 fun x hx hx' =>
      not_le.2 (show x < ws from hx) (show ws ≤ x from hx')
    calc searchLaw hw μ ws θ lam₀ t (Iio ws) + ENNReal.ofReal θ *
          searchLaw hw μ ws θ lam₀ t (Ici ws) +
          ENNReal.ofReal (1 - θ) * searchLaw hw μ ws θ lam₀ t (Ici ws)
        = searchLaw hw μ ws θ lam₀ t (Iio ws) + (ENNReal.ofReal θ + ENNReal.ofReal (1 - θ)) *
          searchLaw hw μ ws θ lam₀ t (Ici ws) := by ring
      _ = 1 := by rw [h1, one_mul, ← measure_union hd measurableSet_Ici, Iio_union_Ici,
          measure_univ]

/-- In real numbers: with `x = λ(Aᶜ)`,
`λ′(B) = μ(B) x + θ 1_B(0) (1 − x) + (1 − θ) λ(B ∩ A)`. -/
theorem searchP_adjoint_real (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (lam : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure lam] {B : Set (Icc (0 : ℝ) wbar)} (hB : MeasurableSet B) :
    (adjointOp (searchP hw θ μ ws) lam B).toReal = (μ B).toReal * (lam (Iio ws)).toReal +
      θ * (B.indicator 1 (w0 hw) : ℝ) * (1 - (lam (Iio ws)).toReal) +
        (1 - θ) * (lam (B ∩ Ici ws)).toReal := by
  have hIci : (lam (Ici ws)).toReal = 1 - (lam (Iio ws)).toReal := by
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, ENNReal.toReal_sub_of_le
      prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have hind : ((B.indicator 1 (w0 hw) : ℝ≥0∞)).toReal = (B.indicator 1 (w0 hw) : ℝ) := by
    by_cases h : w0 hw ∈ B <;> simp [h]
  have hi : B.indicator 1 (w0 hw) ≠ ∞ := by by_cases h : w0 hw ∈ B <;> simp [h]
  have h1 : μ B * lam (Iio ws) ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have h2 : ENNReal.ofReal θ * B.indicator 1 (w0 hw) * lam (Ici ws) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hi) (measure_ne_top _ _)
  have h3 : ENNReal.ofReal (1 - θ) * lam (B ∩ Ici ws) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [searchP_adjoint hw μ ws hθ0 hθ1 lam hB, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨h1, h2⟩)
    h3, ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ0,
    ENNReal.toReal_ofReal (by linarith), hind, hIci]

/-- **Exercise 10.8a.** `λₜ₊₁(Aᶜ) = θ + λₜ(Aᶜ)[μ(Aᶜ) − θ]` (2); since `|μ(Aᶜ) − θ| < 1` the
equation is stable, and `λₜ(Aᶜ) → θ/(θ + μ(A))` (3). -/
theorem ex_10_8a (hθ0 : 0 < θ) (hθ1 : θ < 1) (hws : 0 < ws.1) (lam₀ : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure lam₀] :
    (∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) (Iio ws)).toReal =
      θ + (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * ((μ (Iio ws)).toReal - θ)) ∧
    |(μ (Iio ws)).toReal - θ| < 1 ∧
    Tendsto (fun t => (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal) atTop
      (𝓝 (θ / (θ + (μ (Ici ws)).toReal))) := by
  have h0 : w0 hw ∈ Iio ws := show w0 hw < ws from hws
  have hrec : ∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) (Iio ws)).toReal =
      θ + (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * ((μ (Iio ws)).toReal - θ) := fun t => by
    have := searchLaw_prob hw μ ws hθ0.le hθ1.le lam₀ t
    rw [searchLaw_succ, searchP_adjoint_real hw μ ws hθ0.le hθ1.le _ measurableSet_Iio,
      Set.indicator_of_mem h0, Iio_inter_Ici, Ico_self, measure_empty]
    simp only [Pi.one_apply, ENNReal.toReal_zero]
    ring
  have hμc : (μ (Ici ws)).toReal = 1 - (μ (Iio ws)).toReal := by
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, ENNReal.toReal_sub_of_le
      prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have hμ0 : 0 ≤ (μ (Iio ws)).toReal := ENNReal.toReal_nonneg
  have hμ1 : (μ (Iio ws)).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have ha : |(μ (Iio ws)).toReal - θ| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
  refine ⟨hrec, ha, ?_⟩
  have := tendsto_affine_rec ha (tendsto_const_nhds (x := θ))
    (x := fun t => (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal) fun t => by
      rw [hrec]; ring
  convert this using 2
  rw [hμc]; ring

/-- The limit `L = θ/(θ + μ(A))` of `λₜ(Aᶜ)`, and its recursion. -/
theorem searchLaw_Iio_tendsto (hθ0 : 0 < θ) (hθ1 : θ < 1) (hws : 0 < ws.1)
    (lam₀ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure lam₀] :
    Tendsto (fun t => (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal) atTop
      (𝓝 (θ / (θ + (μ (Ici ws)).toReal))) :=
  (ex_10_8a hw μ ws hθ0 hθ1 hws lam₀).2.2

/-- **Exercise 10.8b** (`0 ∈ C`). For measurable `C ⊆ Aᶜ` with `0 ∈ C`,
`λₜ₊₁(C) = θ + λₜ(Aᶜ)[μ(C) − θ]`, and
`λₜ(C) → [θ/(θ + μ(A))] μ(C) + [μ(A)/(θ + μ(A))] θ` (4). -/
theorem ex_10_8b_zero (hθ0 : 0 < θ) (hθ1 : θ < 1) (hws : 0 < ws.1)
    (lam₀ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure lam₀] {C : Set (Icc (0 : ℝ) wbar)}
    (hC : MeasurableSet C) (hCA : C ⊆ Iio ws) (h0 : w0 hw ∈ C) :
    (∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      θ + (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * ((μ C).toReal - θ)) ∧
    Tendsto (fun t => (searchLaw hw μ ws θ lam₀ t C).toReal) atTop
      (𝓝 (θ / (θ + (μ (Ici ws)).toReal) * (μ C).toReal +
        (μ (Ici ws)).toReal / (θ + (μ (Ici ws)).toReal) * θ)) := by
  have hdisj : C ∩ Ici ws = ∅ := Set.eq_empty_of_forall_notMem fun w hw' =>
    not_le.2 (show w < ws from hCA hw'.1) (show ws ≤ w from hw'.2)
  have hrec : ∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      θ + (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * ((μ C).toReal - θ) := fun t => by
    have := searchLaw_prob hw μ ws hθ0.le hθ1.le lam₀ t
    rw [searchLaw_succ, searchP_adjoint_real hw μ ws hθ0.le hθ1.le _ hC, Set.indicator_of_mem h0,
      hdisj, measure_empty]
    simp only [Pi.one_apply, ENNReal.toReal_zero]
    ring
  refine ⟨hrec, ?_⟩
  have hL := searchLaw_Iio_tendsto hw μ ws hθ0 hθ1 hws lam₀
  have hpos : 0 < θ + (μ (Ici ws)).toReal := by
    have := ENNReal.toReal_nonneg (a := μ (Ici ws)); linarith
  have := (tendsto_const_nhds (x := θ)).add (hL.mul_const ((μ C).toReal - θ))
  rw [← tendsto_add_atTop_iff_nat 1]
  convert this using 1
  · funext t; exact hrec t
  · congr 1; field_simp; ring

/-- **Exercise 10.8b** (`0 ∉ C`). For measurable `C ⊆ Aᶜ` with `0 ∉ C`,
`λₜ₊₁(C) = λₜ(Aᶜ) μ(C)`, and `λₜ(C) → [θ/(θ + μ(A))] μ(C)` (5). -/
theorem ex_10_8b (hθ0 : 0 < θ) (hθ1 : θ < 1) (hws : 0 < ws.1)
    (lam₀ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure lam₀] {C : Set (Icc (0 : ℝ) wbar)}
    (hC : MeasurableSet C) (hCA : C ⊆ Iio ws) (h0 : w0 hw ∉ C) :
    (∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * (μ C).toReal) ∧
    Tendsto (fun t => (searchLaw hw μ ws θ lam₀ t C).toReal) atTop
      (𝓝 (θ / (θ + (μ (Ici ws)).toReal) * (μ C).toReal)) := by
  have hdisj : C ∩ Ici ws = ∅ := Set.eq_empty_of_forall_notMem fun w hw' =>
    not_le.2 (show w < ws from hCA hw'.1) (show ws ≤ w from hw'.2)
  have hrec : ∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * (μ C).toReal := fun t => by
    have := searchLaw_prob hw μ ws hθ0.le hθ1.le lam₀ t
    rw [searchLaw_succ, searchP_adjoint_real hw μ ws hθ0.le hθ1.le _ hC, Set.indicator_of_notMem h0,
      hdisj, measure_empty]
    simp only [ENNReal.toReal_zero]
    ring
  refine ⟨hrec, ?_⟩
  have hL := searchLaw_Iio_tendsto hw μ ws hθ0 hθ1 hws lam₀
  rw [← tendsto_add_atTop_iff_nat 1]
  convert hL.mul_const (μ C).toReal using 1
  funext t; exact hrec t

/-- **Exercise 10.8c.** For measurable `C ⊆ A`, `λₜ₊₁(C) = λₜ(Aᶜ) μ(C) + λₜ(C)(1 − θ)`, and
`λₜ(C) → [θ/(θ + μ(A))] μ(C)/θ` (6). -/
theorem ex_10_8c (hθ0 : 0 < θ) (hθ1 : θ < 1) (hws : 0 < ws.1)
    (lam₀ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure lam₀] {C : Set (Icc (0 : ℝ) wbar)}
    (hC : MeasurableSet C) (hCA : C ⊆ Ici ws) :
    (∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * (μ C).toReal +
        (searchLaw hw μ ws θ lam₀ t C).toReal * (1 - θ)) ∧
    Tendsto (fun t => (searchLaw hw μ ws θ lam₀ t C).toReal) atTop
      (𝓝 (θ / (θ + (μ (Ici ws)).toReal) * ((μ C).toReal / θ))) := by
  have h0 : w0 hw ∉ C := fun h => not_le.2 (show w0 hw < ws from hws) (hCA h)
  have hrec : ∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * (μ C).toReal +
        (searchLaw hw μ ws θ lam₀ t C).toReal * (1 - θ) := fun t => by
    have := searchLaw_prob hw μ ws hθ0.le hθ1.le lam₀ t
    rw [searchLaw_succ, searchP_adjoint_real hw μ ws hθ0.le hθ1.le _ hC, Set.indicator_of_notMem h0,
      inter_eq_left.2 hCA]
    ring
  refine ⟨hrec, ?_⟩
  have hL := (searchLaw_Iio_tendsto hw μ ws hθ0 hθ1 hws lam₀).mul_const (μ C).toReal
  have ha : |1 - θ| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
  have := tendsto_affine_rec ha hL (x := fun t => (searchLaw hw μ ws θ lam₀ t C).toReal)
    fun t => by rw [hrec]; ring
  convert this using 2
  rw [show (1 : ℝ) - (1 - θ) = θ by ring]
  field_simp

end StokeyLucasPrescott.StochasticApplications
