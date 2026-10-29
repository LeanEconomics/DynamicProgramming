/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.RenewalTheorem
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Kendall's renewal theorem (MT §15.1)

Meyn and Tweedie, §15.1.1–15.1.2, pp. 364–368: the renewal sequence of an aperiodic increment law
converges geometrically fast exactly when the increment law has a geometric moment. The proof is
the book's generating-function argument, done with Mathlib's power series and the Cauchy integral
formula on `ℂ`.

**Analytic tools.**
* `genSeries b`: the power series `∑ b(n) zⁿ` as a `FormalMultilinearSeries ℂ ℂ ℂ`
  (`FormalMultilinearSeries.ofScalars`); `genSeries_sum`, `norm_genSeries`,
  `le_radius_genSeries`, `one_le_radius_genSeries`, `summable_of_lt_radius_genSeries`,
  `hasFPowerSeriesOnBall_genFunC`, `differentiableOn_genFunC`.
* `exists_summable_of_differentiableOn`: if the generating function of a bounded `b` extends
  analytically to a disc of radius `> 1`, then `∑ |b(n)| tⁿ < ∞` for some `t > 1` (uniqueness of
  Taylor coefficients plus Cauchy's estimate, as on p. 367).
* `geometric_inverse`: if `a ∗ b = δ₀`, `∑ |a(n)| sⁿ < ∞` for some `s > 1`, `b` is bounded and
  `A(z) ≠ 0` on the closed unit disc, then `b` is geometrically summable (`1/A` is analytic on a
  larger disc, by compactness of the closed disc).

**Renewal identities.**
* `seqDiff v` (`Δv(n) = v(n) − v(n − 1)`, with `v(−1) = 0`), `sum_range_seqDiff`,
  `genFunC_seqDiff` (`ΔV(z) = (1 − z) V(z)`, i.e. (15.15)), `oneSubXSeq`, `genFunC_sub`.
* `realConv_renewalTail_seqDiff`: `tail ∗ Δu = δ₀`, i.e. `R(z) (1 − z) U(z) = 1` with
  `R(z) = (1 − P(z))/(1 − z)` (`one_sub_mul_genFunC_renewalTail`), which is (15.16).
* `genFunC_incr_ne_one`: for aperiodic `p`, `P(z) ≠ 1` on `|z| ≤ 1`, `z ≠ 1` (p. 367);
  `genFunC_renewalTail_ne_zero`: `R(z) ≠ 0` on the closed unit disc when `m_p < ∞` (the root
  `z = 1` of `1 − P(z)` is simple, `R(1) = m_p`).
* `summable_abs_sub_of_seqDiff` and `summable_seqDiff_of_abs_sub`: `∑ |Δv(n)| rⁿ < ∞` and
  `∑ |v(n) − v(∞)| rⁿ < ∞` are equivalent (p. 367, via Lemma D.7.2).
* `summable_mean_of_geometric`: geometric convergence forces `m_p < ∞`.

**Kendall's Theorem.**
* `kendall_geometric_of_moment` ((iii) ⇒ (i)), `kendall_moment_of_geometric` ((i) ⇒ (iii)),
  `kendall_extension_of_geometric` ((i) ⇒ (ii)), `kendall_geometric_of_extension` ((ii) ⇒ (i)).
* **Theorem 15.1.1** (`theorem_15_1_1`, p. 366): the three conditions are equivalent (`TFAE`).
* `kendall_geometric_bound`: the renewal content of Proposition 15.1.2 (p. 369):
  `|u(n) − m_p⁻¹| ≤ R ρⁿ` with `ρ < 1`.
* `kendall_genFunC_sub_pole`: `U(z) − m_p⁻¹/(1 − z) = ∑ (u(n) − m_p⁻¹) zⁿ` is analytic on a disc of
  radius `> 1`.
* `geometric_delayed_bound`: the bound of p. 365,
  `∑ |a ∗ v (n) − c| rⁿ ≤ (∑ a(n) rⁿ)(∑ |v(n) − c| rⁿ) + c r/(r − 1) ∑ a(n) rⁿ`.

**Statement of (ii).** The book says `U` has an analytic extension to `|z| < r₀` "except for a
simple pole at `z = 1`". This is stated as `U(z) = F(z)/(1 − z)` on the unit disc with `F`
analytic on `|z| < r₀` and `F(1) ≠ 0`.

**Hypotheses.** The book's "ergodic renewal sequence" is taken to mean an aperiodic increment law
(`IsAperiodicLaw`); finiteness of the mean is not assumed, as each of (i)–(iii) implies it. The
direction (i) ⇒ (iii) does not use aperiodicity.

**Not formalised.** Propositions 15.1.3 and Theorems 15.1.4–15.1.5, and the examples of §15.1.4:
they concern Markov chains with atoms (Kendall atoms, `f`-Kendall atoms, the regenerative
decomposition (15.8)–(15.11)) and belong to the Chapter 15 Markov chain development, which can use
the results here.

**Corrections.** None.
-/

namespace MeynTweedie.GeneralizedDrift

open Finset Filter Topology
open scoped NNReal ENNReal

/-! ### Power series with real coefficients -/

/-- The formal power series `∑ b(n) zⁿ` over `ℂ` with real coefficients `b`. -/
noncomputable def genSeries (b : ℕ → ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (b n : ℂ))

/-- The sum of `genSeries b` is the generating function `genFunC b`. -/
theorem genSeries_sum (b : ℕ → ℝ) : (genSeries b).sum = genFunC b := by
  funext z
  simp only [FormalMultilinearSeries.sum, genSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    genFunC, smul_eq_mul]

/-- The `n`-th term of `genSeries b` has norm `|b(n)|`. -/
theorem norm_genSeries (b : ℕ → ℝ) (n : ℕ) : ‖genSeries b n‖ = |b n| := by
  rw [genSeries, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs]

/-- If `∑ |b(n)| tⁿ < ∞` then the radius of convergence of `genSeries b` is at least `t`. -/
theorem le_radius_genSeries {b : ℕ → ℝ} {t : ℝ≥0} (h : Summable fun n => |b n| * (t : ℝ) ^ n) :
    (t : ℝ≥0∞) ≤ (genSeries b).radius :=
  (genSeries b).le_radius_of_summable_norm (by simp_rw [norm_genSeries]; exact h)

/-- A bounded coefficient sequence gives radius of convergence at least `1`. -/
theorem one_le_radius_genSeries {b : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |b n| ≤ C) :
    1 ≤ (genSeries b).radius := by
  have h := (genSeries b).le_radius_of_bound (r := 1) C (fun n => by
    rw [norm_genSeries, NNReal.coe_one, one_pow, mul_one]; exact hC n)
  simpa using h

/-- Inside the radius of convergence the coefficients are geometrically summable. -/
theorem summable_of_lt_radius_genSeries {b : ℕ → ℝ} {t : ℝ≥0}
    (h : (t : ℝ≥0∞) < (genSeries b).radius) : Summable fun n => |b n| * (t : ℝ) ^ n := by
  have h' := (genSeries b).summable_norm_mul_pow h
  simp_rw [norm_genSeries] at h'
  exact h'

/-- `genFunC b` is the sum of its power series on the disc of convergence. -/
theorem hasFPowerSeriesOnBall_genFunC {b : ℕ → ℝ} (h : 0 < (genSeries b).radius) :
    HasFPowerSeriesOnBall (genFunC b) (genSeries b) 0 (genSeries b).radius := by
  rw [← genSeries_sum]
  exact (genSeries b).hasFPowerSeriesOnBall h

/-- If `∑ |a(n)| sⁿ < ∞` with `s > 0`, the generating function is complex differentiable on the
disc `|z| < s`. -/
theorem differentiableOn_genFunC {a : ℕ → ℝ} {s : ℝ} (hs : 0 < s)
    (h : Summable fun n => |a n| * s ^ n) : DifferentiableOn ℂ (genFunC a) (Metric.ball 0 s) := by
  set s' : ℝ≥0 := ⟨s, hs.le⟩
  have hrad : (s' : ℝ≥0∞) ≤ (genSeries a).radius := le_radius_genSeries h
  have hpos : 0 < (genSeries a).radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.2 (NNReal.coe_pos.1 hs : 0 < s')) hrad
  refine (hasFPowerSeriesOnBall_genFunC hpos).differentiableOn.mono fun z hz => ?_
  have hz' : z ∈ Metric.eball (0 : ℂ) s' := by rw [Metric.eball_coe]; exact hz
  exact Metric.eball_subset_eball hrad hz'

/-- **Coefficient decay from an analytic extension.** Let `b` be bounded, so that `genFunC b` is
analytic on the unit disc. If it agrees there with a function `G` that is complex differentiable
on a larger disc `|z| < R₀`, then `∑ |b(n)| tⁿ < ∞` for some `t > 1` (Cauchy's inequality and
uniqueness of Taylor coefficients, MT p. 367). -/
theorem exists_summable_of_differentiableOn {b : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |b n| ≤ C)
    {R₀ : ℝ} (hR₀ : 1 < R₀) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (Metric.ball 0 R₀))
    (hGb : ∀ z ∈ Metric.ball (0 : ℂ) 1, G z = genFunC b z) :
    ∃ t > 1, Summable fun n => |b n| * t ^ n := by
  set R : ℝ≥0 := ⟨(1 + R₀) / 2, by linarith⟩ with hRdef
  have hRval : (R : ℝ) = (1 + R₀) / 2 := rfl
  have hRpos : 0 < R := by rw [← NNReal.coe_pos, hRval]; linarith
  have hGc : DifferentiableOn ℂ G (Metric.closedBall 0 R) :=
    hG.mono (Metric.closedBall_subset_ball (by rw [hRval]; linarith))
  have hball := hGc.hasFPowerSeriesOnBall hRpos
  have hrad1 := one_le_radius_genSeries hC
  have h2 := (hasFPowerSeriesOnBall_genFunC (lt_of_lt_of_le zero_lt_one hrad1)).hasFPowerSeriesAt
  have heq : ∀ᶠ z in 𝓝 (0 : ℂ), G z = genFunC b z :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds 0 one_pos) hGb
  have hser := hball.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually h2 heq
  have hRle : (R : ℝ≥0∞) ≤ (genSeries b).radius := hser ▸ hball.r_le
  set t : ℝ≥0 := ⟨(1 + R) / 2, by positivity⟩ with htdef
  have htval : (t : ℝ) = (1 + R) / 2 := rfl
  have htR : t < R := by rw [← NNReal.coe_lt_coe, htval]; rw [hRval]; linarith
  have ht : (t : ℝ≥0∞) < (genSeries b).radius := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 htR) hRle
  refine ⟨t, ?_, summable_of_lt_radius_genSeries ht⟩
  rw [htval, hRval]
  linarith

/-- **Inverting a geometrically summable sequence** (the analytic heart of Kendall's theorem). Let
`a ∗ b = δ₀` with `∑ |a(n)| sⁿ < ∞` for some `s > 1` and `b` bounded. If the generating function
`A(z) = ∑ a(n) zⁿ` has no zero on the closed unit disc, then `∑ |b(n)| tⁿ < ∞` for some `t > 1`:
`1/A` is analytic on a disc of radius `> 1` and its Taylor coefficients are `b`. -/
theorem geometric_inverse {a b : ℕ → ℝ} (hab : realConv a b = deltaSeq) {s : ℝ} (hs : 1 < s)
    (ha : Summable fun n => |a n| * s ^ n) {C : ℝ} (hC : ∀ n, |b n| ≤ C)
    (hA : ∀ z : ℂ, ‖z‖ ≤ 1 → genFunC a z ≠ 0) :
    ∃ t > 1, Summable fun n => |b n| * t ^ n := by
  have hAd := differentiableOn_genFunC (by linarith) ha
  set U : Set ℂ := Metric.ball (0 : ℂ) s ∩ genFunC a ⁻¹' {w | w ≠ 0} with hU
  have hUo : IsOpen U := hAd.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_ne
  have hsub : Metric.closedBall (0 : ℂ) 1 ⊆ U := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    exact ⟨by simpa using hz1.trans_lt hs, hA z hz1⟩
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hUo hsub
  rw [cthickening_closedBall hδ.le zero_le_one] at hδU
  have hball : Metric.ball (0 : ℂ) (δ + 1) ⊆ U :=
    Metric.ball_subset_closedBall.trans hδU
  have hG : DifferentiableOn ℂ (fun z => (genFunC a z)⁻¹) (Metric.ball 0 (δ + 1)) :=
    (hAd.mono fun z hz => (hball hz).1).inv fun z hz => (hball hz).2
  refine exists_summable_of_differentiableOn hC (by linarith) hG fun z hz => ?_
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have ha' : Summable fun n => |a n| * ‖z‖ ^ n :=
    ha.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) n))
      fun n => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (by linarith) n) (abs_nonneg _)
  have hprod : genFunC a z * genFunC b z = 1 := by
    rw [← genFunC_realConv ha' (summable_abs_mul_pow_of_bounded hC hz1), hab, genFunC_deltaSeq]
  exact (eq_inv_of_mul_eq_one_right hprod).symm

/-! ### First differences and generating-function identities -/

/-- The first difference `v(n) − v(n − 1)` of a sequence, with `v(−1) = 0` (MT p. 366). -/
def seqDiff (v : ℕ → ℝ) (n : ℕ) : ℝ := v n - if n = 0 then 0 else v (n - 1)

/-- `Δv(0) = v(0)`. -/
theorem seqDiff_zero (v : ℕ → ℝ) : seqDiff v 0 = v 0 := by simp [seqDiff]

/-- `Δv(n + 1) = v(n + 1) − v(n)`. -/
theorem seqDiff_succ (v : ℕ → ℝ) (n : ℕ) : seqDiff v (n + 1) = v (n + 1) - v n := by
  simp [seqDiff]

/-- Telescoping: `∑_{k ≤ N} Δv(k) = v(N)`. -/
theorem sum_range_seqDiff (v : ℕ → ℝ) (N : ℕ) : ∑ k ∈ range (N + 1), seqDiff v k = v N := by
  induction N with
  | zero => simp [seqDiff_zero]
  | succ N ih => rw [sum_range_succ, ih, seqDiff_succ]; ring

/-- The coefficients of `1 − X`. -/
def oneSubXSeq (n : ℕ) : ℝ := if n = 0 then 1 else if n = 1 then -1 else 0

/-- Differencing is convolution with the coefficients of `1 − X`. -/
theorem realConv_oneSubXSeq (v : ℕ → ℝ) : realConv oneSubXSeq v = seqDiff v := by
  funext n
  rw [realConv_eq_sum_range]
  rcases n with _ | n
  · simp [oneSubXSeq, seqDiff]
  · rw [sum_range_succ', sum_range_succ']
    simp [oneSubXSeq, seqDiff]
    ring

/-- The coefficients of `1 − X` are geometrically summable at every `z`. -/
theorem summable_oneSubXSeq (z : ℂ) : Summable fun n => |oneSubXSeq n| * ‖z‖ ^ n :=
  summable_of_ne_finset_zero (s := range 2) fun n hn => by
    simp only [mem_range, not_lt] at hn
    simp [oneSubXSeq, show n ≠ 0 by omega, show n ≠ 1 by omega]

/-- The generating function of `1 − X` is `1 − z`. -/
theorem genFunC_oneSubXSeq (z : ℂ) : genFunC oneSubXSeq z = 1 - z := by
  rw [genFunC, tsum_eq_sum (s := range 2) fun n hn => by
    simp only [mem_range, not_lt] at hn
    simp [oneSubXSeq, show n ≠ 0 by omega, show n ≠ 1 by omega]]
  simp [oneSubXSeq, sum_range_succ]
  ring

/-- `ΔV(z) = (1 − z) V(z)` wherever `∑ |v(n)| |z|ⁿ < ∞`. -/
theorem genFunC_seqDiff {v : ℕ → ℝ} {z : ℂ} (hv : Summable fun n => |v n| * ‖z‖ ^ n) :
    genFunC (seqDiff v) z = (1 - z) * genFunC v z := by
  rw [← realConv_oneSubXSeq, genFunC_realConv (summable_oneSubXSeq z) hv, genFunC_oneSubXSeq]

/-- The generating function is subtractive. -/
theorem genFunC_sub {a b : ℕ → ℝ} {z : ℂ} (ha : Summable fun n => |a n| * ‖z‖ ^ n)
    (hb : Summable fun n => |b n| * ‖z‖ ^ n) :
    genFunC (a - b) z = genFunC a z - genFunC b z := by
  have hna : Summable fun n => ‖(a n : ℂ) * z ^ n‖ := by simpa [norm_genFunC_term] using ha
  have hnb : Summable fun n => ‖(b n : ℂ) * z ^ n‖ := by simpa [norm_genFunC_term] using hb
  simp only [genFunC]
  rw [← hna.of_norm.tsum_sub hnb.of_norm]
  refine tsum_congr fun n => ?_
  rw [Pi.sub_apply]
  push_cast
  ring

/-- `δ₀` has a finitely supported, hence summable, generating series. -/
theorem summable_deltaSeq (z : ℂ) : Summable fun n => |deltaSeq n| * ‖z‖ ^ n :=
  summable_of_ne_finset_zero (s := {0}) fun n hn => by
    simp [deltaSeq, Finset.mem_singleton.not.1 hn]

/-- The differenced tails are `δ₀ − p`. -/
theorem seqDiff_renewalTail {p : ℕ → ℝ} (hp0 : p 0 = 0) :
    seqDiff (renewalTail p) = deltaSeq - p := by
  funext n
  rcases n with _ | n
  · simp [seqDiff_zero, renewalTail_zero hp0, deltaSeq, hp0]
  · rw [seqDiff_succ, renewalTail_succ]
    simp [deltaSeq]

/-- **`tail ∗ Δu = δ₀`**: in generating functions, `R(z) · (1 − z) U(z) = 1`. -/
theorem realConv_renewalTail_seqDiff {p : ℕ → ℝ} (hp0 : p 0 = 0) :
    realConv (renewalTail p) (seqDiff (realRenewalSeq p)) = deltaSeq := by
  rw [← realConv_oneSubXSeq, ← realConv_assoc, realConv_comm (renewalTail p), realConv_oneSubXSeq,
    seqDiff_renewalTail hp0, realConv_sub_left, realConv_deltaSeq_left]
  funext n
  rw [Pi.sub_apply, realRenewalSeq_eq hp0 n]
  ring

/-- `(1 − z) R(z) = 1 − P(z)` wherever the tail series converges absolutely. -/
theorem one_sub_mul_genFunC_renewalTail {p : ℕ → ℝ} (hp : IsIncrementLaw p) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hr : Summable fun n => |renewalTail p n| * ‖z‖ ^ n) :
    (1 - z) * genFunC (renewalTail p) z = 1 - genFunC p z := by
  rw [← genFunC_seqDiff hr, seqDiff_renewalTail hp.zero,
    genFunC_sub (summable_deltaSeq z) (summable_incr_genFunC hp hz), genFunC_deltaSeq]

/-- **No other root of `P(z) = 1` on the closed unit disc** (MT p. 367). For an aperiodic increment
law and `|z| ≤ 1`, `z ≠ 1`, `P(z) ≠ 1`: equality would force `zⁿ = 1` whenever `p(n) > 0`, so the
order of `z` would divide every such `n`. -/
theorem genFunC_incr_ne_one {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) : genFunC p z ≠ 1 := by
  intro h
  have hns : Summable fun n => ‖(p n : ℂ) * z ^ n‖ := by
    simpa [norm_genFunC_term] using summable_incr_genFunC hp hz
  have hpow1 : ∀ n, ‖z ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  have hre : ∑' n, p n * (z ^ n).re = 1 := by
    have h1 := congrArg Complex.re h
    rw [genFunC, Complex.re_tsum hns.of_norm] at h1
    simpa [Complex.re_ofReal_mul] using h1
  have hs2 : Summable fun n => p n * (z ^ n).re := by
    refine Summable.of_norm_bounded hp.hasSum.summable fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp.nonneg n)]
    exact mul_le_of_le_one_right (hp.nonneg n) ((Complex.abs_re_le_norm _).trans (hpow1 n))
  have hzero : HasSum (fun n => p n * (1 - (z ^ n).re)) 0 := by
    have h2 := hp.hasSum.sub hs2.hasSum
    rw [hre, sub_self] at h2
    convert h2 using 1
    funext n
    ring
  have hnn : ∀ n, 0 ≤ p n * (1 - (z ^ n).re) := fun n =>
    mul_nonneg (hp.nonneg n) (sub_nonneg.2 ((Complex.re_le_norm _).trans (hpow1 n)))
  have hall := (hasSum_zero_iff_of_nonneg hnn).1 hzero
  have hpow : ∀ n, 0 < p n → z ^ n = 1 := by
    intro n hn
    have h1 : (z ^ n).re = 1 := by
      rcases mul_eq_zero.1 (congrFun hall n) with h0 | h0
      · linarith
      · linarith
    have hsq := Complex.normSq_eq_norm_sq (z ^ n)
    rw [Complex.normSq_apply, h1] at hsq
    have hn1 := hpow1 n
    have hn0 := norm_nonneg (z ^ n)
    have him2 : (z ^ n).im * (z ^ n).im ≤ 0 := by nlinarith
    have him : (z ^ n).im = 0 := mul_self_eq_zero.1 (le_antisymm him2 (mul_self_nonneg _))
    exact Complex.ext (by rw [h1, Complex.one_re]) (by rw [him, Complex.one_im])
  have hord := hap (orderOf z) fun n hn => orderOf_dvd_of_pow_eq_one (hpow n hn)
  exact hz1 (orderOf_eq_one_iff.1 hord)

/-- **The tail generating function has no zero on the closed unit disc** (aperiodic, finite mean):
`R(1) = m_p > 0` and `(1 − z) R(z) = 1 − P(z) ≠ 0` for `z ≠ 1`. -/
theorem genFunC_renewalTail_ne_zero {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (hm : Summable fun n : ℕ => (n : ℝ) * p n) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hr : Summable fun n => |renewalTail p n| * ‖z‖ ^ n) : genFunC (renewalTail p) z ≠ 0 := by
  by_cases hz1 : z = 1
  · subst hz1
    have h1 : genFunC (renewalTail p) 1 = ((incrMean p : ℝ) : ℂ) := by
      rw [genFunC, ← (hasSum_renewalTail hp hm).tsum_eq, Complex.ofReal_tsum]
      simp
    rw [h1]
    exact_mod_cast (show incrMean p ≠ 0 by linarith [one_le_incrMean hp hm])
  · intro h0
    have h := one_sub_mul_genFunC_renewalTail hp hz hr
    rw [h0, mul_zero] at h
    exact genFunC_incr_ne_one hp hap hz hz1 (by linear_combination h)

/-! ### From differences to deviations -/

/-- The bound `|Δu(n)| ≤ 1` for a renewal sequence. -/
theorem abs_seqDiff_realRenewalSeq_le {p : ℕ → ℝ} (hp : IsIncrementLaw p) (n : ℕ) :
    |seqDiff (realRenewalSeq p) n| ≤ 1 := by
  rcases n with _ | n
  · rw [seqDiff_zero, realRenewalSeq_zero hp.zero, abs_one]
  · rw [seqDiff_succ, abs_le]
    have := realRenewalSeq_nonneg hp n
    have := realRenewalSeq_nonneg hp (n + 1)
    have := realRenewalSeq_le_one hp n
    have := realRenewalSeq_le_one hp (n + 1)
    constructor <;> linarith

/-- If `v(n) → c` and `Δv` is summable, then `∑ Δv = c`. -/
theorem hasSum_seqDiff {v : ℕ → ℝ} {c : ℝ} (hv : Tendsto v atTop (𝓝 c))
    (hds : Summable (seqDiff v)) : HasSum (seqDiff v) c := by
  rw [hds.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
  simpa [sum_range_seqDiff] using hv

/-- **Geometric decay of differences gives geometric convergence** (MT p. 367, via Lemma D.7.2):
if `v(n) → c` and `∑ |Δv(n)| tⁿ < ∞` with `t > 1`, then `∑ |v(n) − c| tⁿ < ∞`. -/
theorem summable_abs_sub_of_seqDiff {v : ℕ → ℝ} {c : ℝ} (hv : Tendsto v atTop (𝓝 c)) {t : ℝ}
    (ht : 1 < t) (hd : Summable fun n => |seqDiff v n| * t ^ n) :
    Summable fun n => |v n - c| * t ^ n := by
  have ht0 : 0 ≤ t := by linarith
  have hd1 : Summable fun n => |seqDiff v n| :=
    hd.of_nonneg_of_le (fun n => abs_nonneg _)
      (fun n => le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ ht.le))
  have hsum := hasSum_seqDiff hv hd1.of_abs
  have hT := (lemma_D_7_2_i (c := fun n => |seqDiff v n|) (fun n => abs_nonneg _) ht hd).1
  refine hT.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ht0 n))
    fun n => mul_le_mul_of_nonneg_right ?_ (pow_nonneg ht0 n)
  have hsplit := hd1.of_abs.sum_add_tsum_nat_add (n + 1)
  rw [hsum.tsum_eq, sum_range_seqDiff] at hsplit
  have hshift : Summable fun m => |seqDiff v (m + (n + 1))| :=
    (summable_nat_add_iff (f := fun m => |seqDiff v m|) (n + 1)).2 hd1
  have h1 : v n - c = -∑' m, seqDiff v (m + (n + 1)) := by
    rw [← hsplit]; ring
  have h2 : |∑' m, seqDiff v (m + (n + 1))| ≤ ∑' m, |seqDiff v (m + (n + 1))| := by
    have := norm_tsum_le_tsum_norm (f := fun m => seqDiff v (m + (n + 1)))
      (by simpa [Real.norm_eq_abs] using hshift)
    simpa [Real.norm_eq_abs] using this
  rw [h1, abs_neg]
  calc |∑' m, seqDiff v (m + (n + 1))| ≤ ∑' m, |seqDiff v (m + (n + 1))| := h2
    _ ≤ |seqDiff v n| + ∑' m, |seqDiff v (m + (n + 1))| := le_add_of_nonneg_left (abs_nonneg _)
    _ = ∑' m, |seqDiff v (m + n)| := (tailSum_succ hd1 n).symm

/-- Conversely, `∑ |v(n) − c| tⁿ < ∞` with `t ≥ 0` gives `∑ |Δv(n)| tⁿ < ∞`. -/
theorem summable_seqDiff_of_abs_sub {v : ℕ → ℝ} {c t : ℝ} (ht : 0 ≤ t)
    (h : Summable fun n => |v n - c| * t ^ n) : Summable fun n => |seqDiff v n| * t ^ n := by
  rw [← summable_nat_add_iff 1]
  refine (((summable_nat_add_iff 1).2 h).add (h.mul_left t)).of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ht _)) fun n => ?_
  rw [seqDiff_succ, pow_succ]
  have h1 : |v (n + 1) - v n| ≤ |v (n + 1) - c| + |v n - c| := abs_sub_le _ _ _ |>.trans
    (by rw [abs_sub_comm c]) 
  have h2 : 0 ≤ t ^ n * t := mul_nonneg (pow_nonneg ht n) ht
  calc |v (n + 1) - v n| * (t ^ n * t) ≤ (|v (n + 1) - c| + |v n - c|) * (t ^ n * t) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = |v (n + 1) - c| * (t ^ n * t) + t * (|v n - c| * t ^ n) := by ring

/-- Geometric convergence `∑ |u(n) − m_p⁻¹| rⁿ < ∞` with `r > 1` forces `m_p < ∞`: otherwise
`∑ u < ∞`, and Lemma D.7.1 would give `(tail ∗ u)(n) → 0`, contradicting `tail ∗ u ≡ 1`. -/
theorem summable_mean_of_geometric {p : ℕ → ℝ} (hp : IsIncrementLaw p) {r : ℝ} (hr : 1 < r)
    (h : Summable fun n => |realRenewalSeq p n - (incrMean p)⁻¹| * r ^ n) :
    Summable fun n : ℕ => (n : ℝ) * p n := by
  by_contra hm
  have h0 : incrMean p = 0 := tsum_eq_zero_of_not_summable hm
  rw [h0, inv_zero] at h
  have hu : Summable (realRenewalSeq p) := by
    refine h.of_nonneg_of_le (realRenewalSeq_nonneg hp) fun n => ?_
    rw [sub_zero, abs_of_nonneg (realRenewalSeq_nonneg hp n)]
    exact le_mul_of_one_le_right (realRenewalSeq_nonneg hp n) (one_le_pow₀ hr.le)
  have hlim := lemma_D_7_1 (realRenewalSeq_nonneg hp) hu (tendsto_renewalTail hp)
  rw [zero_mul, realConv_comm] at hlim
  have hone : realConv (renewalTail p) (realRenewalSeq p) = fun _ => 1 :=
    funext (realConv_renewalTail_renewal hp.zero)
  rw [hone] at hlim
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

/-! ### Kendall's theorem -/

/-- **(iii) ⇒ (i) of Kendall's theorem.** A geometric moment `∑ p(n) κⁿ < ∞`, `κ > 1`, of an
aperiodic increment law gives geometric convergence `∑ |u(n) − m_p⁻¹| rⁿ < ∞` for some `r > 1`. -/
theorem kendall_geometric_of_moment {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    {κ : ℝ} (hκ : 1 < κ) (hsum : Summable fun n => p n * κ ^ n) :
    ∃ r > 1, Summable fun n => |realRenewalSeq p n - (incrMean p)⁻¹| * r ^ n := by
  have hκ1 : 0 < κ - 1 := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  -- the mean is finite: `n ≤ κⁿ/(κ − 1)` (Bernoulli)
  have hm : Summable fun n : ℕ => (n : ℝ) * p n := by
    refine (hsum.mul_left (1 / (κ - 1))).of_nonneg_of_le
      (fun n => mul_nonneg (Nat.cast_nonneg n) (hp.nonneg n)) fun n => ?_
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ κ - 1 by linarith) n
    rw [add_sub_cancel] at hb
    have hn : (n : ℝ) ≤ κ ^ n / (κ - 1) := by
      rw [le_div_iff₀ hκ1]; linarith
    calc (n : ℝ) * p n ≤ κ ^ n / (κ - 1) * p n := mul_le_mul_of_nonneg_right hn (hp.nonneg n)
      _ = 1 / (κ - 1) * (p n * κ ^ n) := by ring
  -- the tails have the same geometric moment (Lemma D.7.2 (i))
  have hc : Summable fun m => p (m + 1) * κ ^ m := by
    refine (((summable_nat_add_iff (f := fun n => p n * κ ^ n) 1).2 hsum).mul_left κ⁻¹).congr
      fun m => ?_
    rw [pow_succ]
    field_simp
  have htail : Summable fun n => |renewalTail p n| * κ ^ n := by
    have h := (lemma_D_7_2_i (c := fun m => p (m + 1)) (fun m => hp.nonneg _) hκ hc).1
    refine h.congr fun n => ?_
    rw [abs_of_nonneg (renewalTail_nonneg hp n), renewalTail_eq_tsum hp n]
    congr 1
  have hA : ∀ z : ℂ, ‖z‖ ≤ 1 → genFunC (renewalTail p) z ≠ 0 := by
    intro z hz
    refine genFunC_renewalTail_ne_zero hp hap hm hz (htail.of_nonneg_of_le
      (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) n)) fun n => ?_)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (by linarith) n)
      (abs_nonneg _)
  obtain ⟨t, ht, hts⟩ := geometric_inverse (realConv_renewalTail_seqDiff hp.zero) hκ htail
    (abs_seqDiff_realRenewalSeq_le hp) hA
  exact ⟨t, ht, summable_abs_sub_of_seqDiff (renewal_theorem hp hap) ht hts⟩

/-- **(i) ⇒ (iii) of Kendall's theorem.** Geometric convergence of the renewal sequence forces a
geometric moment of the increments (aperiodicity is not needed for this direction). -/
theorem kendall_moment_of_geometric {p : ℕ → ℝ} (hp : IsIncrementLaw p) {r : ℝ} (hr : 1 < r)
    (h : Summable fun n => |realRenewalSeq p n - (incrMean p)⁻¹| * r ^ n) :
    ∃ κ > 1, Summable fun n => p n * κ ^ n := by
  have hm := summable_mean_of_geometric hp hr h
  have hd := summable_seqDiff_of_abs_sub (by linarith) h
  have hab : realConv (seqDiff (realRenewalSeq p)) (renewalTail p) = deltaSeq := by
    rw [realConv_comm, realConv_renewalTail_seqDiff hp.zero]
  have htail1 : Summable (renewalTail p) := (hasSum_renewalTail hp hm).summable
  have hC : ∀ n, |renewalTail p n| ≤ 1 := fun n => by
    rw [abs_of_nonneg (renewalTail_nonneg hp n)]; exact renewalTail_le_one hp n
  have hA : ∀ z : ℂ, ‖z‖ ≤ 1 → genFunC (seqDiff (realRenewalSeq p)) z ≠ 0 := by
    intro z hz
    have hd' : Summable fun n => |seqDiff (realRenewalSeq p) n| * ‖z‖ ^ n :=
      hd.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) n))
        fun n => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (by linarith) n) (abs_nonneg _)
    have hr' : Summable fun n => |renewalTail p n| * ‖z‖ ^ n :=
      htail1.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) n))
        fun n => by
          rw [abs_of_nonneg (renewalTail_nonneg hp n)]
          exact mul_le_of_le_one_right (renewalTail_nonneg hp n)
            (pow_le_one₀ (norm_nonneg _) hz)
    have hprod : genFunC (seqDiff (realRenewalSeq p)) z * genFunC (renewalTail p) z = 1 := by
      rw [← genFunC_realConv hd' hr', hab, genFunC_deltaSeq]
    exact left_ne_zero_of_mul_eq_one hprod
  obtain ⟨t, ht, hts⟩ := geometric_inverse hab hr hd hC hA
  have ht0 : 0 ≤ t := by linarith
  refine ⟨t, ht, ?_⟩
  rw [← summable_nat_add_iff 1]
  refine (hts.mul_left t).of_nonneg_of_le
    (fun n => mul_nonneg (hp.nonneg _) (pow_nonneg ht0 _)) fun n => ?_
  have hle : p (n + 1) ≤ renewalTail p n := by
    have := renewalTail_nonneg hp (n + 1)
    rw [renewalTail_succ] at this
    linarith
  rw [abs_of_nonneg (renewalTail_nonneg hp n), pow_succ]
  calc p (n + 1) * (t ^ n * t) ≤ renewalTail p n * (t ^ n * t) :=
        mul_le_mul_of_nonneg_right hle (mul_nonneg (pow_nonneg ht0 n) ht0)
    _ = t * (renewalTail p n * t ^ n) := by ring

/-- **(i) ⇒ (ii) of Kendall's theorem.** Geometric convergence gives a meromorphic extension of
`U(z)` to a disc of radius `> 1` with a simple pole at `z = 1`: `U(z) = F(z)/(1 − z)` with `F`
analytic on the larger disc and `F(1) = m_p⁻¹ ≠ 0`. -/
theorem kendall_extension_of_geometric {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p) {r : ℝ} (hr : 1 < r)
    (h : Summable fun n => |realRenewalSeq p n - (incrMean p)⁻¹| * r ^ n) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 r) ∧ F 1 ≠ 0 ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, genFunC (realRenewalSeq p) z = F z / (1 - z) := by
  have hm := summable_mean_of_geometric hp hr h
  have hd := summable_seqDiff_of_abs_sub (by linarith) h
  refine ⟨genFunC (seqDiff (realRenewalSeq p)), differentiableOn_genFunC (by linarith) hd, ?_,
    fun z hz => ?_⟩
  · have hd1 : Summable (seqDiff (realRenewalSeq p)) :=
      (hd.of_nonneg_of_le (fun n => abs_nonneg _)
        fun n => le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ hr.le)).of_abs
    have hs := hasSum_seqDiff (renewal_theorem hp hap) hd1
    have h1 : genFunC (seqDiff (realRenewalSeq p)) 1 = (((incrMean p)⁻¹ : ℝ) : ℂ) := by
      rw [genFunC, ← hs.tsum_eq, Complex.ofReal_tsum]
      simp
    rw [h1]
    have := one_le_incrMean hp hm
    exact_mod_cast (inv_pos.2 (by linarith : (0 : ℝ) < incrMean p)).ne'
  · have hz1 : ‖z‖ < 1 := by simpa using hz
    have hne : (1 : ℂ) - z ≠ 0 := by
      intro h0
      have : z = 1 := by linear_combination -h0
      rw [this, norm_one] at hz1
      exact lt_irrefl _ hz1
    rw [genFunC_seqDiff (summable_renewal_genFunC hp hz1), eq_div_iff hne]
    ring

/-- **(ii) ⇒ (i) of Kendall's theorem.** If `(1 − z) U(z)` extends analytically to a disc of
radius `> 1`, then the renewal sequence converges geometrically fast. -/
theorem kendall_geometric_of_extension {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p) {r₀ : ℝ} (hr₀ : 1 < r₀) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 r₀))
    (hU : ∀ z ∈ Metric.ball (0 : ℂ) 1, genFunC (realRenewalSeq p) z = F z / (1 - z)) :
    ∃ r > 1, Summable fun n => |realRenewalSeq p n - (incrMean p)⁻¹| * r ^ n := by
  have hFb : ∀ z ∈ Metric.ball (0 : ℂ) 1, F z = genFunC (seqDiff (realRenewalSeq p)) z := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa using hz
    have hne : (1 : ℂ) - z ≠ 0 := by
      intro h0
      have : z = 1 := by linear_combination -h0
      rw [this, norm_one] at hz1
      exact lt_irrefl _ hz1
    rw [genFunC_seqDiff (summable_renewal_genFunC hp hz1), hU z hz, mul_div_cancel₀ _ hne]
  obtain ⟨t, ht, hts⟩ := exists_summable_of_differentiableOn (abs_seqDiff_realRenewalSeq_le hp) hr₀
    hF hFb
  exact ⟨t, ht, summable_abs_sub_of_seqDiff (renewal_theorem hp hap) ht hts⟩

/-- **Theorem 15.1.1 (Kendall's Theorem)** (MT p. 366). For an aperiodic increment law `p` with
renewal sequence `u` and `u(∞) = lim u(n) = m_p⁻¹` (`renewal_theorem`), the following are
equivalent:
1. (i) `∑ |u(n) − u(∞)| rⁿ < ∞` for some `r > 1` (the series `U₀(z)` of (15.13) converges on a
   disc of radius `> 1`);
2. (ii) `U(z) = ∑ u(n) zⁿ` extends from the unit disc to a disc of radius `r₀ > 1` except for a
   simple pole at `z = 1`: `U(z) = F(z)/(1 − z)` with `F` analytic on `|z| < r₀`, `F(1) ≠ 0`;
3. (iii) `∑ p(n) κⁿ < ∞` for some `κ > 1` (`P(z)` of (15.14) converges on a disc of radius
   `> 1`). -/
theorem theorem_15_1_1 {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p) :
    List.TFAE
      [∃ r > 1, Summable fun n => |realRenewalSeq p n - (incrMean p)⁻¹| * r ^ n,
       ∃ r₀ > 1, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 r₀) ∧ F 1 ≠ 0 ∧
         ∀ z ∈ Metric.ball (0 : ℂ) 1, genFunC (realRenewalSeq p) z = F z / (1 - z),
       ∃ κ > 1, Summable fun n => p n * κ ^ n] := by
  tfae_have 1 → 2 := fun ⟨r, hr, h⟩ => ⟨r, hr, kendall_extension_of_geometric hp hap hr h⟩
  tfae_have 2 → 1 := fun ⟨r₀, hr₀, F, hF, _, hU⟩ =>
    kendall_geometric_of_extension hp hap hr₀ hF hU
  tfae_have 1 → 3 := fun ⟨r, hr, h⟩ => kendall_moment_of_geometric hp hr h
  tfae_have 3 → 1 := fun ⟨κ, hκ, h⟩ => kendall_geometric_of_moment hp hap hκ h
  tfae_finish

/-- **Geometric rate for a Kendall renewal sequence** (the renewal content of Proposition 15.1.2,
MT p. 369). If `∑ p(n) κⁿ < ∞` for some `κ > 1`, there are `ρ ∈ (0, 1)` and `R < ∞` with
`|u(n) − m_p⁻¹| ≤ R ρⁿ` for all `n`. -/
theorem kendall_geometric_bound {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    {κ : ℝ} (hκ : 1 < κ) (hsum : Summable fun n => p n * κ ^ n) :
    ∃ ρ, 0 < ρ ∧ ρ < 1 ∧ ∃ R, ∀ n, |realRenewalSeq p n - (incrMean p)⁻¹| ≤ R * ρ ^ n := by
  obtain ⟨r, hr, h⟩ := kendall_geometric_of_moment hp hap hκ hsum
  have hr0 : 0 < r := by linarith
  refine ⟨r⁻¹, inv_pos.2 hr0, inv_lt_one_of_one_lt₀ hr, ∑' n, |realRenewalSeq p n -
    (incrMean p)⁻¹| * r ^ n, fun n => ?_⟩
  have hle := h.le_tsum n fun m _ => mul_nonneg (abs_nonneg _) (pow_nonneg hr0.le m)
  have hpos : 0 < (r⁻¹) ^ n := pow_pos (inv_pos.2 hr0) n
  calc |realRenewalSeq p n - (incrMean p)⁻¹|
      = |realRenewalSeq p n - (incrMean p)⁻¹| * r ^ n * r⁻¹ ^ n := by
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hr0.ne', one_pow, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hle hpos.le

/-- **The pole is removed by `m_p⁻¹/(1 − z)`** (MT p. 366, (15.13)). Under geometric convergence,
`U(z) − m_p⁻¹/(1 − z) = ∑ (u(n) − m_p⁻¹) zⁿ` on the unit disc, and the right side is analytic on a
disc of radius `> 1`. -/
theorem kendall_genFunC_sub_pole {p : ℕ → ℝ} (hp : IsIncrementLaw p) {r : ℝ} (hr : 1 < r)
    (h : Summable fun n => |realRenewalSeq p n - (incrMean p)⁻¹| * r ^ n) :
    DifferentiableOn ℂ (genFunC fun n => realRenewalSeq p n - (incrMean p)⁻¹) (Metric.ball 0 r) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, genFunC (fun n => realRenewalSeq p n - (incrMean p)⁻¹) z =
        genFunC (realRenewalSeq p) z - ((incrMean p)⁻¹ : ℝ) / (1 - z) := by
  refine ⟨differentiableOn_genFunC (by linarith) h, fun z hz => ?_⟩
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have hc : Summable fun n => |(fun _ : ℕ => (incrMean p)⁻¹) n| * ‖z‖ ^ n :=
    summable_abs_mul_pow_of_bounded (C := |(incrMean p)⁻¹|) (fun _ => le_rfl) hz1
  have hsub := genFunC_sub (summable_renewal_genFunC hp hz1) hc
  have hgeom : genFunC (fun _ : ℕ => (incrMean p)⁻¹) z = ((incrMean p)⁻¹ : ℝ) / (1 - z) := by
    rw [genFunC, tsum_mul_left, tsum_geometric_of_norm_lt_one hz1, div_eq_mul_inv]
  rw [← hgeom, ← hsub]
  rfl

/-- **The geometric bound for a delayed renewal sequence** (MT p. 365, via Lemma D.7.2). For a delay
law `a`, any sequence `v`, `c ≥ 0` and `r > 1`,
`∑ |a ∗ v (n) − c| rⁿ ≤ (∑ a(n) rⁿ)(∑ |v(n) − c| rⁿ) + c · r/(r − 1) · ∑ a(n) rⁿ`, all series
converging when the two on the right do. -/
theorem geometric_delayed_bound {a v : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1) {c : ℝ}
    (hc : 0 ≤ c) {r : ℝ} (hr : 1 < r) (har : Summable fun n => a n * r ^ n)
    (hvr : Summable fun n => |v n - c| * r ^ n) :
    Summable (fun n => |realConv a v n - c| * r ^ n) ∧
      ∑' n, |realConv a v n - c| * r ^ n ≤
        (∑' n, a n * r ^ n) * (∑' n, |v n - c| * r ^ n) +
          c * (r / (r - 1) * ∑' n, a n * r ^ n) := by
  have hr0 : 0 ≤ r := by linarith
  set w : ℕ → ℝ := fun n => |v n - c|
  have hw : ∀ n, 0 ≤ w n := fun n => abs_nonneg _
  have h1 := lemma_D_7_2_ii ha hw hr0 har hvr
  obtain ⟨h2s, h2le⟩ := lemma_D_7_2_i ha hr har
  have hpt : ∀ n, |realConv a v n - c| * r ^ n ≤
      realConv a w n * r ^ n + c * ((∑' m, a (m + n)) * r ^ n) := by
    intro n
    have hsplit := ha1.summable.sum_add_tsum_nat_add (n + 1)
    rw [ha1.tsum_eq] at hsplit
    have heq : realConv a v n - c =
        ∑ j ∈ range (n + 1), a j * (v (n - j) - c) - c * ∑' m, a (m + (n + 1)) := by
      rw [realConv_eq_sum_range]
      have : c = c * (∑ j ∈ range (n + 1), a j + ∑' m, a (m + (n + 1))) := by rw [hsplit, mul_one]
      conv_lhs => rw [this]
      simp only [mul_sub, sum_sub_distrib, mul_add, mul_sum]
      ring_nf
    have htail : ∑' m, a (m + (n + 1)) ≤ ∑' m, a (m + n) := by
      have := tailSum_succ ha1.summable n
      linarith [ha n]
    have hT0 : 0 ≤ ∑' m, a (m + (n + 1)) := tsum_nonneg fun m => ha _
    have hbound : |realConv a v n - c| ≤ realConv a w n + c * ∑' m, a (m + n) := by
      rw [heq]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [realConv_eq_sum_range]
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun j _ => ?_))
        rw [abs_mul, abs_of_nonneg (ha j)]
      · rw [abs_mul, abs_of_nonneg hc, abs_of_nonneg hT0]
        exact mul_le_mul_of_nonneg_left htail hc
    calc |realConv a v n - c| * r ^ n ≤ (realConv a w n + c * ∑' m, a (m + n)) * r ^ n :=
          mul_le_mul_of_nonneg_right hbound (pow_nonneg hr0 n)
      _ = _ := by ring
  have hsum : Summable fun n => realConv a w n * r ^ n + c * ((∑' m, a (m + n)) * r ^ n) :=
    h1.summable.add (h2s.mul_left c)
  have hs : Summable fun n => |realConv a v n - c| * r ^ n :=
    hsum.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg hr0 n)) hpt
  refine ⟨hs, ?_⟩
  calc ∑' n, |realConv a v n - c| * r ^ n
      ≤ ∑' n, (realConv a w n * r ^ n + c * ((∑' m, a (m + n)) * r ^ n)) :=
        Summable.tsum_le_tsum hpt hs hsum
    _ = (∑' n, a n * r ^ n) * (∑' n, w n * r ^ n) +
          c * ∑' n, (∑' m, a (m + n)) * r ^ n := by
        rw [h1.summable.tsum_add (h2s.mul_left c), h1.tsum_eq, tsum_mul_left]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left h2le hc
        linarith

end MeynTweedie.GeneralizedDrift
