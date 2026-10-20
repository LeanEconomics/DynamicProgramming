/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.WeakConcavity
import DeterministicDynamics.Envelope
import DeterministicDynamics.EulerEquations

/-!
# Differentiability and interior policies in the growth model

SLP Exercise 5.1d, pp. 104–105. In the setting of Exercise 5.1c (`U` and `f` strictly concave):

* `liftR`, `concaveOn_liftR`: `v` extended by zero to `ℝ` is concave on `[0, x̄]`.
* `ex_5_1d`: if `g(x) < f(x)` at an interior `x`, with `U` differentiable at `f(x) − g(x)` and `f`
  differentiable at `x`, then `v′(x) = U′(f(x) − g(x)) f′(x)` (Theorem 4.10). Only `g(x) < f(x)`
  is used, not `g(x) > 0`.
* `ex_5_1d_interior`: if `U′(c) → ∞` as `c ↓ 0`, then `0 < g(x) < f(x)` for every `x > 0`.
  Zero consumption is not optimal, because the first unit of consumption has unbounded marginal
  utility while `v` has bounded slopes. Zero saving is not optimal for the same reason applied to
  `v(ε) − v(0) ≥ U(f(ε)) − U(0)`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {U f : ℝ → ℝ} {β xbar : ℝ}

/-- `v` on `[0, x̄]` extended by zero to `ℝ`. -/
noncomputable def liftR (xbar : ℝ) (v : Icc (0 : ℝ) xbar → ℝ) (x : ℝ) : ℝ := by
  classical exact if hx : x ∈ Icc 0 xbar then v ⟨x, hx⟩ else 0

theorem liftR_of_mem (v : Icc (0 : ℝ) xbar → ℝ) {x : ℝ} (hx : x ∈ Icc 0 xbar) :
    liftR xbar v x = v ⟨x, hx⟩ := by
  simp only [liftR, hx, ↓reduceDIte]

theorem concaveOn_liftR {v : Icc (0 : ℝ) xbar → ℝ} (hv : IsStrictConcaveS (convex_Icc 0 xbar) v) :
    ConcaveOn ℝ (Icc 0 xbar) (liftR xbar v) := by
  refine ⟨convex_Icc 0 xbar, fun x hx y hy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  have hmem : a • x + b • y ∈ Icc (0 : ℝ) xbar := convex_Icc 0 xbar hx hy ha hb hab
  rw [liftR_of_mem v hx, liftR_of_mem v hy, liftR_of_mem v hmem, smul_eq_mul, smul_eq_mul]
  subst hb'
  rcases eq_or_ne x y with rfl | hne
  · have : a • x + (1 - a) • x = x := by rw [← add_smul]; simp
    simp only [this]; ring_nf; rfl
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  rcases (show a ≤ 1 by linarith).eq_or_lt with rfl | ha1
  · simp
  exact (hv ⟨x, hx⟩ ⟨y, hy⟩ (fun he => hne (congrArg Subtype.val he)) a ha' ha1).le

/-- **Exercise 5.1d (differentiability).** If `g(x₀) < f(x₀)` at `x₀ ∈ (0, x̄)`, `U` has derivative
`U′` at `f(x₀) − g(x₀)` and `f` has derivative `f′` at `x₀`, then `v′(x₀) = U′ f′`. -/
theorem ex_5_1d [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) {x₀ : Icc (0 : ℝ) xbar}
    (hx₀ : x₀.1 ∈ Ioo 0 xbar)
    (hgf : (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x₀).1 < f x₀.1)
    {U' f' : ℝ}
    (hU' : HasDerivAt U U' (f x₀.1 - (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x₀).1))
    (hf' : HasDerivAt f f' x₀.1) : HasDerivAt (liftR xbar v) (U' * f') x₀.1 := by
  obtain ⟨hvc, hUA, -⟩ := ex_5_1c_weak h hU hf hv
  set g₀ := argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x₀
  have hX : Icc (0 : ℝ) xbar ∈ 𝓝 x₀.1 := Icc_mem_nhds hx₀.1 hx₀.2
  set W : ℝ → ℝ := fun x => U (f x - g₀.1) + β * v g₀
  have hW : HasDerivAt W (U' * f') x₀.1 := (hU'.comp x₀.1 (hf'.sub_const g₀.1)).add_const _
  have hvx : ∀ x, v x = maxValue (obj (growthF U f xbar) β v) (growthΓ f xbar) x := fun x => by
    rw [← bellman_apply (growth_assumption43 h) (growth_assumption44 h), hv]
  have heq : W x₀.1 = liftR xbar v x₀.1 := by
    rw [liftR_of_mem v x₀.2, Subtype.coe_eta, hvx x₀]
    exact (hUA.argmaxFn_mem x₀).2
  -- for `x` near `x₀`, `g₀ ≤ f(x)`, so `W(x) ≤ v(x)`
  have hfc : ContinuousAt f x₀.1 := hf'.continuousAt
  have hle : ∀ᶠ x in 𝓝 x₀.1, W x ≤ liftR xbar v x := by
    filter_upwards [hX, hfc.eventually (lt_mem_nhds hgf)] with x hx hfx
    rw [liftR_of_mem v hx, hvx]
    exact le_maxValue (z := g₀) (continuousOn_obj (growth_assumption44 h) v.continuous)
      ((growth_assumption43 h).compact _) (show g₀ ∈ growthΓ f xbar ⟨x, hx⟩ from hfx.le)
  have := (theorem_4_10 (concaveOn_liftR hvc) hX hW.hasFDerivAt heq hle).hasDerivAt
  simpa using this

/-- Marginal utility tends to infinity at zero: for every `M`, `U(c) − U(0) ≥ Mc` for small
`c > 0` (the tangent line at `c` lies above `U(0)`). -/
theorem eventually_slope_ge (hU : ConcaveOn ℝ (Ici 0) U)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hinada : Tendsto (deriv U) (𝓝[>] 0) atTop)
    (M : ℝ) : ∀ᶠ c in 𝓝[>] (0 : ℝ), M * c ≤ U c - U 0 := by
  filter_upwards [hinada.eventually (eventually_ge_atTop M), self_mem_nhdsWithin] with c hc hc0
  have htan := concave_le_fderiv hU (z₀ := c) (z := 0) (mem_Ici.2 (le_of_lt hc0))
    (mem_Ici.2 le_rfl) ((hUd c hc0).hasDerivAt.hasFDerivAt)
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, zero_sub] at htan
  have hc0' : (0 : ℝ) < c := hc0
  nlinarith

/-- A concave function on `[0, x̄]` has its left difference quotients at `a` bounded by its chord
slope over `[0, a/2]`, for steps `ε < a/2`. -/
theorem slope_le_chord {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConcaveOn ℝ s φ) {a ε : ℝ}
    (h0 : (0 : ℝ) ∈ s) (ha : a ∈ s) (hε0 : 0 < ε) (hε : ε < a / 2) :
    φ a - φ (a - ε) ≤ ε * ((φ (a / 2) - φ 0) / (a / 2)) := by
  have hs : Icc 0 a ⊆ s := hφ.1.ordConnected.out h0 ha
  have h1 := hφ.slope_anti_adjacent (x := a / 2) (y := a - ε) (z := a)
    (hs ⟨by linarith, by linarith⟩) ha (by linarith) (by linarith)
  have h2 := hφ.slope_anti_adjacent (x := 0) (y := a / 2) (z := a - ε) h0
    (hs ⟨by linarith, by linarith⟩) (by linarith) (by linarith)
  rw [sub_zero] at h2
  have e : a - (a - ε) = ε := by ring
  have h1' : (φ a - φ (a - ε)) / ε ≤ (φ (a - ε) - φ (a / 2)) / (a - ε - a / 2) := by
    simpa only [e] using h1
  rw [div_le_iff₀ hε0] at h1'
  calc φ a - φ (a - ε) ≤ (φ (a - ε) - φ (a / 2)) / (a - ε - a / 2) * ε := h1'
    _ ≤ (φ (a / 2) - φ 0) / (a / 2) * ε := mul_le_mul_of_nonneg_right h2 hε0.le
    _ = ε * ((φ (a / 2) - φ 0) / (a / 2)) := mul_comm _ _

/-- **Exercise 5.1d (interior policies).** If `U` is differentiable on `(0, ∞)` with
`U′(c) → ∞` as `c ↓ 0`, then `0 < g(x) < f(x)` for every `x ∈ (0, x̄]`. -/
theorem ex_5_1d_interior [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hinada : Tendsto (deriv U) (𝓝[>] 0) atTop)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) {x : Icc (0 : ℝ) xbar}
    (hx : 0 < x.1) :
    0 < (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x).1 ∧
      (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x).1 < f x.1 := by
  obtain ⟨hvc, hUA, -⟩ := ex_5_1c_weak h hU hf hv
  set g := argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x
  have hg := hUA.argmaxFn_mem x
  have hgΓ : g.1 ≤ f x.1 := hg.1
  have hvx : ∀ z, v z = maxValue (obj (growthF U f xbar) β v) (growthΓ f xbar) z := fun z => by
    rw [← bellman_apply (growth_assumption43 h) (growth_assumption44 h), hv]
  have hcont := continuousOn_obj (growth_assumption44 h) v.continuous
  -- any `y ≤ f(x)` gives `F(x, y) + βv(y) ≤ F(x, g) + βv(g)`
  have hopt : ∀ y : Icc (0 : ℝ) xbar, y.1 ≤ f x.1 →
      U (f x.1 - y.1) + β * v y ≤ U (f x.1 - g.1) + β * v g := fun y hy => by
    have h1 := le_maxValue hcont ((growth_assumption43 h).compact x) (show y ∈ growthΓ f xbar x
      from hy)
    rw [← hg.2] at h1
    exact h1
  have hfx : x.1 ≤ f x.1 := (h.f_maintain x.1 x.2).1
  have hfxb : f x.1 ≤ xbar := (h.f_maintain x.1 x.2).2
  have hfpos : 0 < f x.1 := hx.trans_le hfx
  have hβ := h.β_pos
  have hconcV := concaveOn_liftR hvc
  have hU0 : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.2 le_rfl
  constructor
  · -- `g(x) > 0`
    by_contra hg0
    have hg0' : g.1 = 0 := le_antisymm (not_lt.1 hg0) g.2.1
    -- `v(0) = U(0) + βv(0)`
    set z₀ : Icc (0 : ℝ) xbar := ⟨0, le_rfl, h.xbar_pos.le⟩
    have hv0 : v z₀ = U 0 + β * v z₀ := by
      obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax (growth_assumption43 h)
        (growth_assumption44 h) v z₀
      have hy0 : y = z₀ := Subtype.ext (le_antisymm (by
        have : y.1 ≤ f 0 := hy; rwa [h.f_zero] at this) y.2.1)
      rw [hv] at hval
      have hF0 : growthF U f xbar (z₀, z₀) = U 0 := by simp [growthF, z₀, h.f_zero]
      rw [hy0, hF0] at hval
      exact hval
    -- the chord bound for `U` near `f(x)`
    set K := (U (f x.1 / 2) - U 0) / (f x.1 / 2)
    have hfc0 : ContinuousWithinAt f (Ici 0) 0 := h.f_cont 0 (mem_Ici.2 le_rfl)
    -- choose `ε` with `U(f(ε)) − U(0) ≥ ((K + 1)/β) f(ε)` and `f(ε)` small
    have hslope := eventually_slope_ge hU.concaveOn hUd hinada ((K + 1) / β)
    obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hslope)
    obtain ⟨η, hη, hηf⟩ := Metric.continuousWithinAt_iff.1 hfc0 δ hδ
    set ε := min (min (η / 2) (f x.1 / 4)) (x.1 / 2)
    have hε0 : 0 < ε := by positivity
    have hεη : ε < η := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hη))
    have hεf : ε < f x.1 / 2 := (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt
      (by linarith))
    have hεx : ε ≤ x.1 := (min_le_right _ _).trans (by linarith)
    set e : Icc (0 : ℝ) xbar := ⟨ε, hε0.le, hεx.trans x.2.2⟩
    -- `f(ε)` is small and at least `ε`
    have hfe : ε ≤ f ε := (h.f_maintain ε e.2).1
    have hfeδ : f ε < δ := by
      have := hηf (mem_Ici.2 hε0.le) (by rw [Real.dist_eq, sub_zero, abs_of_pos hε0]; exact hεη)
      rw [h.f_zero, Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans_lt this
    have hsl := hδs (by rw [Real.dist_eq, sub_zero, abs_of_pos (hε0.trans_le hfe)]; exact hfeδ)
      (show (0 : ℝ) < f ε from hε0.trans_le hfe)
    -- `v(ε) ≥ U(f(ε)) + βv(0)`
    have hve : U (f ε) + β * v z₀ ≤ v e := by
      rw [hvx e]
      have := le_maxValue hcont ((growth_assumption43 h).compact e)
        (show z₀ ∈ growthΓ f xbar e from (show (0 : ℝ) ≤ f ε by linarith))
      simpa [obj, growthF, z₀] using this
    -- optimality of `g = 0` against `ε`
    have hopt' := hopt e (by linarith)
    rw [hg0', sub_zero] at hopt'
    have hgz : g = z₀ := Subtype.ext hg0'
    rw [hgz] at hopt'
    have hUc := slope_le_chord hU.concaveOn hU0 (mem_Ici.2 hfpos.le) hε0 hεf
    have hK0 : 0 ≤ K := by
      have hm : U 0 ≤ U (f x.1 / 2) :=
        h.U_mono.monotoneOn hU0 (mem_Ici.2 (half_pos hfpos).le) (half_pos hfpos).le
      exact div_nonneg (by linarith) (half_pos hfpos).le
    have hKb : 0 ≤ (K + 1) / β := div_nonneg (by linarith) hβ.le
    have h1 : (K + 1) / β * ε ≤ U (f ε) - U 0 :=
      (mul_le_mul_of_nonneg_left hfe hKb).trans hsl
    have he : (e : ℝ) = ε := rfl
    rw [he] at hopt'
    have hdiff : U (f ε) - U 0 ≤ v e - v z₀ := by linarith
    have h2' := mul_le_mul_of_nonneg_left hdiff hβ.le
    have h2 : β * (U (f ε) - U 0) ≤ ε * K := by
      have : β * (v e - v z₀) ≤ U (f x.1) - U (f x.1 - ε) := by linarith
      have hUc' : U (f x.1) - U (f x.1 - ε) ≤ ε * K := hUc
      linarith
    have h3 : β * ((K + 1) / β * ε) = (K + 1) * ε := by field_simp
    nlinarith
  · -- `g(x) < f(x)`
    by_contra hgf
    have hga : g.1 = f x.1 := le_antisymm hgΓ (not_lt.1 hgf)
    set a := f x.1
    set Kv := (liftR xbar v (a / 2) - liftR xbar v 0) / (a / 2)
    have hslope := eventually_slope_ge hU.concaveOn hUd hinada (β * Kv + 1)
    obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hslope)
    set ε := min (δ / 2) (a / 4)
    have hε0 : 0 < ε := by positivity
    have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hεa : ε < a / 2 := (min_le_right _ _).trans_lt (by linarith)
    have hsl := hδs (by rw [Real.dist_eq, sub_zero, abs_of_pos hε0]; exact hεδ) hε0
    set y : Icc (0 : ℝ) xbar := ⟨a - ε, by linarith, by linarith⟩
    have hopt' := hopt y (by change a - ε ≤ a; linarith)
    rw [hga, show a - (a - ε) = ε by ring, sub_self] at hopt'
    have hvc' := slope_le_chord hconcV (show (0 : ℝ) ∈ Icc 0 xbar from ⟨le_rfl,
      h.xbar_pos.le⟩) (show a ∈ Icc 0 xbar from ⟨hfpos.le, hfxb⟩) hε0 hεa
    rw [liftR_of_mem v (show a ∈ Icc 0 xbar from ⟨hfpos.le, hfxb⟩),
      liftR_of_mem v (show a - ε ∈ Icc 0 xbar from ⟨by linarith, by linarith⟩)] at hvc'
    have hgeq : g = ⟨a, hfpos.le, hfxb⟩ := Subtype.ext hga
    rw [hgeq] at hopt'
    have h1 : β * (v ⟨a, hfpos.le, hfxb⟩ - v ⟨a - ε, by linarith, by linarith⟩) ≤
        β * (ε * Kv) := mul_le_mul_of_nonneg_left hvc' hβ.le
    nlinarith

end StokeyLucasPrescott.DeterministicDynamics
