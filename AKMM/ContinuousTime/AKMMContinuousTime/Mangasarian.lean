/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.ContinuousHamiltonian
import RamseyCassKoopmans.Concavity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Mangasarian–Arrow sufficiency in the book's setting

AKMM, §9.2 (pp. 246–249) and §9.3.2 (pp. 253–255). The book uses the first-order conditions
of the maximum principle as if they characterized the optimum. Mathlib has no Pontryagin
maximum principle, so their necessity is not formalised. Their sufficiency (Mangasarian 1966,
Arrow) is proved here, for the class of problems of Chapter 9:
`max ∫_0^∞ e^{−ρt}u(c(t))dt` subject to `ẋ = G(t, x) − c`, with `u` concave and `G(t, ·)`
concave.

* `mangasarian`: if a path satisfies the state equation, the costate equation
  `μ̇ = −μ ∂G/∂x` ((9.21)/(9.25)/(9.A.2)), the first-order condition `μ = e^{−ρt}u'(c)`
  ((9.20)/(9.24)/(9.A.1)) with `μ ≥ 0`, then for every competitor from the same initial state,
  `∫_0^T e^{−ρt}u(c') ≤ ∫_0^T e^{−ρt}u(c) + μ(T)(x(T) − x'(T))`. The proof differentiates
  `∫_0^t e^{−ρs}(u(c') − u(c)) + μ(t)(x'(t) − x(t))` and shows it is nonincreasing.
* `mangasarian_catching_up`: if the terminal term is eventually at most any `δ > 0`, the path
  is catching-up optimal, and its welfare is the largest whenever welfare limits exist.
* `mangasarian_consumption_saving`: the household problem (9.16)–(9.17): (9.24), (9.25) and the
  TVC `lim e^{−ρT}u'(c(T))a(T) = 0` imply catching-up optimality against every path satisfying
  the nPg (9.17); instance `mangasarian_consumption_saving_constant` (`r = ρ`).
* `mangasarian_planner`: the planner's problem (9.33): the conditions of p. 254 and the TVC
  (9.34) imply catching-up optimality against every path with `k ≥ 0`; instance
  `mangasarian_planner_steady_state` (the modified-golden-rule steady state is optimal).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- `e^{−ρT} → 0` as `T → ∞` for `ρ > 0`. -/
theorem mangasarian_exp_neg_tendsto {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun T : ℝ => Real.exp (-ρ * T)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hρ)
  refine h.congr fun T => ?_
  simp [neg_mul]

/-- **Mangasarian–Arrow sufficiency, finite horizon** (AKMM, §9.2, pp. 248–249, for the
problems of Chapter 9). Let `u` be concave on `(0, ∞)` with derivative `u'`, and let the
candidate `(x, c)` and costate `μ ≥ 0` satisfy, for `t ≥ 0`, `ẋ = G(t, x) − c`,
`μ̇ = −μ G_x(t, x)` and `μ = e^{−ρt}u'(c)`. If the competitor `(x', c')` has the same initial
state, positive continuous consumption, `ẋ' = G(t, x') − c'`, and
`G(t, x') ≤ G(t, x) + G_x(t, x)(x' − x)` (concavity of `G(t, ·)`), then for every `T ≥ 0`
`∫_0^T e^{−ρt}u(c') ≤ ∫_0^T e^{−ρt}u(c) + μ(T)(x(T) − x'(T))`. -/
theorem mangasarian {ρ : ℝ} {u u' : ℝ → ℝ} {G Gx : ℝ → ℝ → ℝ} {x c μ x' c' : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (G t (x t) - c t) t)
    (hμ : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * Gx t (x t))) t)
    (hfoc : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t)) (hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t)
    (hc' : ∀ t, 0 ≤ t → 0 < c' t) (hcc' : ContinuousOn c' (Set.Ici 0))
    (hx' : ∀ t, 0 ≤ t → HasDerivAt x' (G t (x' t) - c' t) t) (h0 : x' 0 = x 0)
    (hG : ∀ t, 0 ≤ t → G t (x' t) ≤ G t (x t) + Gx t (x t) * (x' t - x t))
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + μ T * (x T - x' T) := by
  have hucont : ContinuousOn u (Set.Ioi 0) := fun y hy =>
    (hu y hy).continuousAt.continuousWithinAt
  have hE : Continuous fun t : ℝ => Real.exp (-ρ * t) := by fun_prop
  have huc : ContinuousOn (fun t => Real.exp (-ρ * t) * u (c t)) (Set.Ici 0) :=
    hE.continuousOn.mul (hucont.comp hcc fun t ht => hc t ht)
  have huc' : ContinuousOn (fun t => Real.exp (-ρ * t) * u (c' t)) (Set.Ici 0) :=
    hE.continuousOn.mul (hucont.comp hcc' fun t ht => hc' t ht)
  set f : ℝ → ℝ := fun t => Real.exp (-ρ * t) * u (c' t) - Real.exp (-ρ * t) * u (c t)
  have hf : ContinuousOn f (Set.Ici 0) := huc'.sub huc
  have hsub : ∀ s : ℝ, 0 ≤ s → Set.uIcc 0 s ⊆ Set.Ici 0 := fun s hs => by
    rw [Set.uIcc_of_le hs]
    exact Set.Icc_subset_Ici_self
  have hint : ∀ s : ℝ, 0 ≤ s → IntervalIntegrable f MeasureTheory.volume 0 s := fun s hs =>
    (hf.mono (hsub s hs)).intervalIntegrable
  set Φ : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, f s) + μ t * (x' t - x t)
  have hD : ∀ t, 0 < t → HasDerivAt Φ (f t + (-(μ t * Gx t (x t)) * (x' t - x t) +
      μ t * ((G t (x' t) - c' t) - (G t (x t) - c t)))) t := by
    intro t ht
    have hfo : ContinuousOn f (Set.Ioi 0) := hf.mono Set.Ioi_subset_Ici_self
    have h1 := intervalIntegral.integral_hasDerivAt_right (hint t ht.le)
      (hfo.stronglyMeasurableAtFilter isOpen_Ioi t ht)
      (hfo.continuousAt (Ioi_mem_nhds ht))
    exact h1.add ((hμ t ht.le).mul ((hx' t ht.le).sub (hx t ht.le)))
  have hneg : ∀ t, 0 < t → f t + (-(μ t * Gx t (x t)) * (x' t - x t) +
      μ t * ((G t (x' t) - c' t) - (G t (x t) - c t))) ≤ 0 := by
    intro t ht
    have hs := RamseyCassKoopmans.concave_support hconc (Set.mem_Ioi.mpr (hc t ht.le))
      (Set.mem_Ioi.mpr (hc' t ht.le)) (hu (c t) (hc t ht.le))
    have hE0 := (Real.exp_pos (-ρ * t)).le
    have hfle : f t ≤ μ t * (c' t - c t) := by
      simp only [f]
      rw [hfoc t ht.le, ← mul_sub, mul_assoc]
      exact mul_le_mul_of_nonneg_left hs hE0
    have hGt := mul_le_mul_of_nonneg_left (hG t ht.le) (hμ0 t ht.le)
    nlinarith
  have hanti : AntitoneOn Φ (Set.Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · have hprim := intervalIntegral.continuousOn_primitive_interval' (hint T hT)
        (Set.left_mem_uIcc (a := (0 : ℝ)) (b := T))
      rw [Set.uIcc_of_le hT] at hprim
      refine hprim.add fun t ht => ?_
      exact (((hμ t ht.1).mul ((hx' t ht.1).sub (hx t ht.1))).continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hD t ht.1).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hD t ht.1).deriv]
      exact hneg t ht.1
  have hle := hanti (Set.left_mem_Icc.mpr hT) (Set.right_mem_Icc.mpr hT) hT
  simp only [Φ, intervalIntegral.integral_same, zero_add, h0, sub_self, mul_zero] at hle
  have hsplit : ∫ s in (0 : ℝ)..T, f s = (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t)) -
      ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t) :=
    intervalIntegral.integral_sub ((huc'.mono (hsub T hT)).intervalIntegrable)
      ((huc.mono (hsub T hT)).intervalIntegrable)
  rw [hsplit] at hle
  linarith

/-- **Mangasarian–Arrow sufficiency, infinite horizon**: under the hypotheses of `mangasarian`,
if the terminal term `μ(T)(x(T) − x'(T))` is eventually at most any `δ > 0`, the candidate is
catching-up optimal against the competitor, and if both welfare integrals converge, the
competitor's welfare is at most the candidate's. -/
theorem mangasarian_catching_up {ρ : ℝ} {u u' : ℝ → ℝ} {G Gx : ℝ → ℝ → ℝ}
    {x c μ x' c' : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (G t (x t) - c t) t)
    (hμ : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * Gx t (x t))) t)
    (hfoc : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t)) (hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t)
    (hc' : ∀ t, 0 ≤ t → 0 < c' t) (hcc' : ContinuousOn c' (Set.Ici 0))
    (hx' : ∀ t, 0 ≤ t → HasDerivAt x' (G t (x' t) - c' t) t) (h0 : x' 0 = x 0)
    (hG : ∀ t, 0 ≤ t → G t (x' t) ≤ G t (x t) + Gx t (x t) * (x' t - x t))
    (hterm : ∀ δ > 0, ∀ᶠ T in atTop, μ T * (x T - x' T) ≤ δ) :
    (∀ δ > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + δ) ∧
    ∀ J J' : ℝ, Tendsto (fun T => ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) atTop (𝓝 J) →
      Tendsto (fun T => ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t)) atTop (𝓝 J') →
      J' ≤ J := by
  have hcu : ∀ δ > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + δ := by
    intro δ hδ
    filter_upwards [hterm δ hδ, eventually_ge_atTop (0 : ℝ)] with T h1 h2
    linarith [mangasarian hconc hu hc hcc hx hμ hfoc hμ0 hc' hcc' hx' h0 hG h2]
  refine ⟨hcu, fun J J' hJ hJ' => ?_⟩
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  exact le_of_tendsto_of_tendsto hJ' (hJ.add_const δ) (hcu δ hδ)

/-- **Sufficiency for the consumption–saving problem** (AKMM, (9.16)–(9.17), (9.24)–(9.25),
pp. 246–249). If `u` is concave with `u' ≥ 0`, and the candidate satisfies `ȧ = w + ra − c`,
(9.24) `μ = e^{−ρt}u'(c)`, (9.25) `rμ + μ̇ = 0`, and the TVC `lim e^{−ρT}u'(c(T))a(T) = 0`,
then it is catching-up optimal against every path from `a(0)` with positive continuous
consumption that satisfies the nPg (9.17), stated as `liminf e^{−rT}a'(T) ≥ 0`. -/
theorem mangasarian_consumption_saving {ρ r w : ℝ} {u u' : ℝ → ℝ} {a c μ a' c' : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hu'0 : ∀ y, 0 < y → 0 ≤ u' y)
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (ha : ∀ t, 0 ≤ t → HasDerivAt a (w + r * a t - c t) t)
    (h924 : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (h925 : ∀ t, 0 ≤ t → HasDerivAt μ (-r * μ t) t)
    (htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * a T) atTop (𝓝 0))
    (hc' : ∀ t, 0 ≤ t → 0 < c' t) (hcc' : ContinuousOn c' (Set.Ici 0))
    (ha' : ∀ t, 0 ≤ t → HasDerivAt a' (w + r * a' t - c' t) t) (h0 : a' 0 = a 0)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ Real.exp (-r * T) * a' T) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + δ := by
  have hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t := fun t ht => by
    rw [h924 t ht]; exact mul_nonneg (Real.exp_pos _).le (hu'0 _ (hc t ht))
  have hμexp : ∀ T, 0 ≤ T → μ T = Real.exp (-r * T) * μ 0 := fun T hT =>
    SargentStachurski.ContinuousTime.eq_exp_of_hasDerivAt rfl h925 hT
  refine (mangasarian_catching_up (G := fun _ y => r * y + w) (Gx := fun _ _ => r) hconc hu hc
    hcc (fun t ht => by convert ha t ht using 1; ring) (fun t ht => by
      convert h925 t ht using 1; ring) h924 hμ0 hc' hcc'
    (fun t ht => by convert ha' t ht using 1; ring) h0 (fun t _ => by ring_nf; rfl) ?_).1
  intro δ hδ
  set K := μ 0
  have hK : 0 ≤ K := hμ0 0 le_rfl
  set η := δ / (2 * (K + 1))
  have hη : 0 < η := div_pos hδ (by positivity)
  have htvc' : Tendsto (fun T => μ T * a T) atTop (𝓝 0) := by
    refine htvc.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [h924 T hT]
  filter_upwards [hnpg η hη, htvc'.eventually (gt_mem_nhds (half_pos hδ)),
    eventually_ge_atTop (0 : ℝ)] with T h1 h2 hT
  have e : μ T * a' T = K * (Real.exp (-r * T) * a' T) := by rw [hμexp T hT]; ring
  have h3 : -(K * η) ≤ μ T * a' T := by
    rw [e]; nlinarith
  have hKη : K * η ≤ δ / 2 := by
    have e2 : K * η = δ / 2 * (K / (K + 1)) := by
      simp only [η]; field_simp
    rw [e2]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by linarith)).mpr (by linarith))
  nlinarith

/-- AKMM, §9.2, an instance of `mangasarian_consumption_saving`: with `r = ρ > 0`, keeping the
asset constant, `a(t) = a_0`, `c(t) = w + ra_0 > 0`, satisfies (9.24), (9.25) and the TVC, so it
is catching-up optimal against every path from `a_0` satisfying the nPg. -/
theorem mangasarian_consumption_saving_constant {ρ w a₀ : ℝ} {u u' : ℝ → ℝ} (hρ : 0 < ρ)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hu'0 : ∀ y, 0 < y → 0 ≤ u' y) (hc0 : 0 < w + ρ * a₀) {a' c' : ℝ → ℝ}
    (hc' : ∀ t, 0 ≤ t → 0 < c' t) (hcc' : ContinuousOn c' (Set.Ici 0))
    (ha' : ∀ t, 0 ≤ t → HasDerivAt a' (w + ρ * a' t - c' t) t) (h0 : a' 0 = a₀)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ Real.exp (-ρ * T) * a' T) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (w + ρ * a₀)) + δ := by
  have hd : ∀ t, HasDerivAt (fun s => Real.exp (-ρ * s) * u' (w + ρ * a₀))
      (-ρ * (Real.exp (-ρ * t) * u' (w + ρ * a₀))) t := fun t =>
    SargentStachurski.ContinuousTime.hasDerivAt_exp_mul (-ρ) _ t
  have htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' (w + ρ * a₀) * a₀) atTop (𝓝 0) := by
    have := ((mangasarian_exp_neg_tendsto hρ).mul_const (u' (w + ρ * a₀))).mul_const a₀
    simpa using this
  exact mangasarian_consumption_saving (a := fun _ => a₀) (c := fun _ => w + ρ * a₀)
    (μ := fun s => Real.exp (-ρ * s) * u' (w + ρ * a₀)) hconc hu hu'0 (fun _ _ => hc0)
    continuousOn_const (fun t _ => by simpa using hasDerivAt_const t a₀)
    (fun _ _ => rfl) (fun t _ => hd t) htvc hc' hcc' ha' h0 hnpg

/-- **Sufficiency for the planner's problem** (AKMM, (9.33)–(9.34), pp. 253–254, and (9.A.1)–
(9.A.2), p. 846). Let `f` be concave on `[0, ∞)` with derivative `f'` along the candidate, `u`
concave with `u' ≥ 0`. If the candidate has positive capital and consumption,
`k̇ = f(k) − δk − c`, `μ = e^{−ρt}u'(c)` (9.A.1), `μ̇ = −μ(f'(k) − δ)` (9.A.2), and the TVC
(9.34) `lim e^{−ρT}u'(c(T))k(T) = 0`, then it is catching-up optimal against every path from
`k(0)` with `k' ≥ 0` and positive continuous consumption; disinvestment is allowed. -/
theorem mangasarian_planner {ρ δ : ℝ} {f f' u u' : ℝ → ℝ} {k c μ k' c' : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y) (hu'0 : ∀ y, 0 < y → 0 ≤ u' y)
    (hk : ∀ t, 0 ≤ t → 0 < k t) (hfd : ∀ t, 0 ≤ t → HasDerivAt f (f' (k t)) (k t))
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hkd : ∀ t, 0 ≤ t → HasDerivAt k (f (k t) - δ * k t - c t) t)
    (h9A1 : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (h9A2 : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * (f' (k t) - δ))) t)
    (htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * k T) atTop (𝓝 0))
    (hk' : ∀ t, 0 ≤ t → 0 ≤ k' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hkd' : ∀ t, 0 ≤ t → HasDerivAt k' (f (k' t) - δ * k' t - c' t) t) (h0 : k' 0 = k 0) :
    (∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + ε) ∧
    ∀ J J' : ℝ, Tendsto (fun T => ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) atTop (𝓝 J) →
      Tendsto (fun T => ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t)) atTop (𝓝 J') →
      J' ≤ J := by
  have hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t := fun t ht => by
    rw [h9A1 t ht]; exact mul_nonneg (Real.exp_pos _).le (hu'0 _ (hc t ht))
  have hG : ∀ t, 0 ≤ t → f (k' t) - δ * k' t ≤
      f (k t) - δ * k t + (f' (k t) - δ) * (k' t - k t) := fun t ht => by
    have hs := RamseyCassKoopmans.concave_support hf (Set.mem_Ici.mpr (hk t ht).le)
      (Set.mem_Ici.mpr (hk' t ht)) (hfd t ht)
    nlinarith
  refine mangasarian_catching_up (G := fun _ y => f y - δ * y) (Gx := fun t _ => f' (k t) - δ)
    hconc hu hc hcc hkd h9A2 h9A1 hμ0 hc' hcc' hkd' h0 hG ?_
  intro ε hε
  have htvc' : Tendsto (fun T => μ T * k T) atTop (𝓝 0) := by
    refine htvc.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [h9A1 T hT]
  filter_upwards [htvc'.eventually (gt_mem_nhds hε), eventually_ge_atTop (0 : ℝ)] with T h1 hT
  nlinarith [mul_nonneg (hμ0 T hT) (hk' T hT)]

/-- AKMM, §9.3.2, p. 255 and fn. 3, an instance of `mangasarian_planner`: at the modified golden
rule `f'(k**) = δ + ρ` with `ρ > 0` and `c** = f(k**) − δk** > 0`, the steady state satisfies
(9.33), (9.A.1), (9.A.2) and the TVC (9.34), so it is optimal from `k(0) = k**` against every
path with `k ≥ 0`. -/
theorem mangasarian_planner_steady_state {ρ δ kss : ℝ} {f u u' : ℝ → ℝ} (hρ : 0 < ρ)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y) (hu'0 : ∀ y, 0 < y → 0 ≤ u' y)
    (hkss : 0 < kss) (hfd : HasDerivAt f (δ + ρ) kss) (hcss : 0 < f kss - δ * kss)
    {k' c' : ℝ → ℝ} (hk' : ∀ t, 0 ≤ t → 0 ≤ k' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hkd' : ∀ t, 0 ≤ t → HasDerivAt k' (f (k' t) - δ * k' t - c' t) t) (h0 : k' 0 = kss) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (f kss - δ * kss)) + ε := by
  set css := f kss - δ * kss
  have hd : ∀ t, HasDerivAt (fun s => Real.exp (-ρ * s) * u' css)
      (-(Real.exp (-ρ * t) * u' css * (δ + ρ - δ))) t := fun t => by
    convert SargentStachurski.ContinuousTime.hasDerivAt_exp_mul (-ρ) (u' css) t using 1
    ring
  have htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' css * kss) atTop (𝓝 0) := by
    have := ((mangasarian_exp_neg_tendsto hρ).mul_const (u' css)).mul_const kss
    simpa using this
  exact (mangasarian_planner (f' := fun _ => δ + ρ) (k := fun _ => kss) (c := fun _ => css)
    (μ := fun s => Real.exp (-ρ * s) * u' css) hf hconc hu hu'0 (fun _ _ => hkss)
    (fun _ _ => hfd) (fun _ _ => hcss) continuousOn_const
    (fun t _ => by simpa [css] using hasDerivAt_const t kss) (fun _ _ => rfl)
    (fun t _ => hd t) htvc hk' hc' hcc' hkd' h0).1

end AKMM.ContinuousTime
