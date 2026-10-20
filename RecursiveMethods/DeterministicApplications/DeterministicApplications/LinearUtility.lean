/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.WeakConcavity

/-!
# Optimal growth with linear utility

SLP §5.3, p. 105: the model of Section 5.1 with `U(c) = c` and `f` satisfying (T1)–(T5). Let
`k*` maximize `βf(k) − k` and `A = βf(k*) − k*`.

* `ex_5_3a`: (U1)–(U3) hold, so Exercise 5.1a–b applies: `v` is the unique bounded continuous
  solution, equals `v*` and is strictly increasing, and `G` is nonempty and u.h.c.; `v` is
  concave. (U4) fails, but when `f` is strictly concave Assumption 4.7 still holds, so `v` is
  strictly concave and the policy is a continuous function (`ex_5_3a_strict`). The interior
  result of Exercise 5.1d fails: below `k*` nothing is consumed (`ex_5_3a_corner`).
* `kstar_le_xbar`: by (T2), `k*` lies in `X`.
* `linear_value_le`, `linear_value_eq`: `v(k) ≤ f(k) + A/(1 − β)` everywhere, with equality
  when `k* ≤ f(k)`.
* `ex_5_3b`: for some `ε > 0`, `|k − k*| < ε` implies `v(k) = f(k) − k* + β[f(k*) − k*]/(1 − β)`.
* `ex_5_3c`: the policy `g(k) = min{f(k), k*}` is optimal: jump to `k*` when it is feasible,
  otherwise invest everything.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {f : ℝ → ℝ} {β xbar : ℝ}

/-- **Exercise 5.3a.** With `U(c) = c` the conclusions of Exercise 5.1a–b hold, and `v` is
concave. -/
theorem ex_5_3a (h : GrowthHyp id f β xbar) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    (fun x => (v x : EReal)) = vstar (growthΓ f xbar) (curryF (growthF id f xbar)) β ∧
      StrictMono v ∧ IsConcaveS (convex_Icc 0 xbar) v ∧
      ∀ x, (argmax (obj (growthF id f xbar) β v) (growthΓ f xbar) x).Nonempty ∧
        IsUHC (argmax (obj (growthF id f xbar) β v) (growthΓ f xbar)) x := by
  obtain ⟨u, -, huniq, hvs, hmono, hG⟩ := ex_5_1ab h
  have hvu := huniq v hv
  subst hvu
  exact ⟨hvs, hmono, growth_concave h (concaveOn_id (convex_Ici 0)) hf hv, hG⟩

/-- **Exercise 5.3a.** Although (U4) fails, a strictly concave `f` gives Assumption 4.7, so `v`
is strictly concave and the policy is a continuous function. -/
theorem ex_5_3a_strict [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp id f β xbar)
    (hf : StrictConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    IsStrictConcaveS (convex_Icc 0 xbar) v ∧
      UniqueArgmax (growthΓ f xbar) (obj (growthF id f xbar) β v) ∧
      Continuous (argmaxFn (growthΓ f xbar) (obj (growthF id f xbar) β v)) := by
  obtain ⟨h1, h2, -, h4⟩ := theorem_4_8 (growth_assumption43 h) (growth_assumption44 h)
    (growth_a47 h (concaveOn_id (convex_Ici 0)) hf) (growth_a48 hf.concaveOn) hv
  exact ⟨h1, h2, h4⟩

/-- By (T2), a maximizer of `βf(k) − k` over `k ≥ 0` lies in `[0, x̄]`. -/
theorem kstar_le_xbar (hβ : 0 < β) (hβ1 : β < 1) (hf0 : f 0 = 0) (hbelow : ∀ x, xbar < x → f x < x)
    {kstar : ℝ} (hk0 : 0 ≤ kstar) (hk : ∀ k, 0 ≤ k → β * f k - k ≤ β * f kstar - kstar) :
    kstar ≤ xbar := by
  by_contra hlt
  push Not at hlt
  have h1 := hbelow kstar hlt
  have h2 := hk 0 le_rfl
  rw [hf0] at h2
  nlinarith [mul_lt_mul_of_pos_left h1 hβ]

variable {kstar : Icc (0 : ℝ) xbar}

/-- `f(k*) ≥ k*`, since `βf(k*) − k* ≥ βf(0) − 0 = 0`. -/
theorem kstar_le_f (h : GrowthHyp id f β xbar)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1) :
    0 ≤ β * f kstar.1 - kstar.1 ∧ kstar.1 ≤ f kstar.1 := by
  have h0 := hk ⟨0, le_rfl, h.xbar_pos.le⟩
  simp only [h.f_zero, mul_zero, sub_zero] at h0
  have hf := growth_f_nonneg h kstar
  refine ⟨h0, ?_⟩
  nlinarith [h.β_lt]

/-- `v(k) ≤ f(k) + A/(1 − β)`, `A = βf(k*) − k*`, for every `k`. -/
theorem linear_value_le (h : GrowthHyp id f β xbar)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) (x : Icc (0 : ℝ) xbar) :
    v x ≤ f x.1 + (β * f kstar.1 - kstar.1) / (1 - β) := by
  have : CompactSpace (Icc (0 : ℝ) xbar) := isCompact_iff_compactSpace.1 isCompact_Icc
  have : Nonempty (Icc (0 : ℝ) xbar) := ⟨⟨0, le_rfl, h.xbar_pos.le⟩⟩
  set A := β * f kstar.1 - kstar.1
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  -- the largest excess `m = max (v − f − A/(1 − β))` satisfies `m ≤ βm`
  set D : Icc (0 : ℝ) xbar → ℝ := fun z => v z - f z.1 - A / (1 - β)
  have hD : Continuous D := (v.continuous.sub (continuous_growth_f h)).sub continuous_const
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hD.continuousOn
  have hmax : ∀ z, D z ≤ D x₀ := fun z => hx₀ (mem_univ z)
  obtain ⟨y, hy, hyv, -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) v x₀
  rw [hv] at hyv
  have e1 := hmax y
  have e2 := hk y
  have hA : A / (1 - β) * (1 - β) = A := div_mul_cancel₀ A h1β.ne'
  have hm : D x₀ ≤ β * D x₀ := by
    simp only [D, growthF, id] at e1 hyv ⊢
    nlinarith [h.β_pos]
  have hm0 : D x₀ ≤ 0 := by nlinarith [h.β_lt]
  have := (hmax x).trans hm0
  simp only [D] at this
  linarith

/-- `v(k) = f(k) + A/(1 − β)` whenever `k* ≤ f(k)`: jumping to `k*` and staying there is
optimal. -/
theorem linear_value_eq (h : GrowthHyp id f β xbar)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) {x : Icc (0 : ℝ) xbar}
    (hx : kstar.1 ≤ f x.1) : v x = f x.1 + (β * f kstar.1 - kstar.1) / (1 - β) := by
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  refine le_antisymm (linear_value_le h hk hv x) ?_
  have hjump : ∀ z : Icc (0 : ℝ) xbar, kstar.1 ≤ f z.1 → f z.1 - kstar.1 + β * v kstar ≤ v z :=
    fun z hz => by
      obtain ⟨-, -, -, hmax⟩ :=
        exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) v z
      rw [hv] at hmax
      simpa [growthF] using hmax kstar hz
  have hks := hjump kstar (kstar_le_f h hk).2
  have hvk : (f kstar.1 - kstar.1) / (1 - β) ≤ v kstar := by
    rw [div_le_iff₀ h1β]; linarith
  have := hjump x hx
  have e : f x.1 + (β * f kstar.1 - kstar.1) / (1 - β) =
      f x.1 - kstar.1 + β * ((f kstar.1 - kstar.1) / (1 - β)) := by
    field_simp; ring
  rw [e]
  nlinarith [h.β_pos]

/-- **Exercise 5.3b.** For some `ε > 0`, `|k − k*| < ε` implies
`v(k) = f(k) − k* + β[f(k*) − k*]/(1 − β)`. -/
theorem ex_5_3b (h : GrowthHyp id f β xbar)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    ∃ ε > 0, ∀ k : Icc (0 : ℝ) xbar, |k.1 - kstar.1| < ε →
      v k = f k.1 - kstar.1 + β * (f kstar.1 - kstar.1) / (1 - β) := by
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  have hform : ∀ k : Icc (0 : ℝ) xbar, kstar.1 ≤ f k.1 →
      v k = f k.1 - kstar.1 + β * (f kstar.1 - kstar.1) / (1 - β) := fun k hk' => by
    rw [linear_value_eq h hk hv hk']
    field_simp; ring
  obtain ⟨hA, -⟩ := kstar_le_f h hk
  rcases eq_or_lt_of_le kstar.2.1 with h0 | hpos
  · -- `k* = 0`: every `k` can jump to `k*`
    exact ⟨1, one_pos, fun k _ => hform k (h0 ▸ growth_f_nonneg h k)⟩
  · -- `k* > 0`: `f(k*) > k*`, and `f` stays above `k*` near `k*`
    have hfk : kstar.1 < f kstar.1 := by nlinarith [h.β_lt, h.β_pos]
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1
      (h.f_cont kstar.1 (mem_Ici.2 kstar.2.1)) (f kstar.1 - kstar.1) (by linarith)
    refine ⟨δ, hδ, fun k hkd => hform k ?_⟩
    have := hball (mem_Ici.2 k.2.1) (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    linarith [neg_abs_le (f k.1 - f kstar.1)]

/-- The policy `g(k) = min{f(k), k*}`. -/
noncomputable def linearPolicy (h : GrowthHyp id f β xbar) (kstar x : Icc (0 : ℝ) xbar) :
    Icc (0 : ℝ) xbar :=
  ⟨min (f x.1) kstar.1, le_min (growth_f_nonneg h x) kstar.2.1, (min_le_right _ _).trans kstar.2.2⟩

/-- **Exercise 5.3c.** The policy `g(k) = min{f(k), k*}` is optimal: jump to `k*` when that is
feasible, and otherwise consume nothing and invest all output. -/
theorem ex_5_3c (h : GrowthHyp id f β xbar) (hf : ConcaveOn ℝ (Ici 0) f)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) (x : Icc (0 : ℝ) xbar) :
    linearPolicy h kstar x ∈ argmax (obj (growthF id f xbar) β v) (growthΓ f xbar) x := by
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  have hvc := growth_concave h (concaveOn_id (convex_Ici 0)) hf hv
  set A := β * f kstar.1 - kstar.1
  -- `ψ(y) = βv(y) − y` is maximized at `k*`
  have hψ : ∀ z : Icc (0 : ℝ) xbar, β * v z - z.1 ≤ β * v kstar - kstar.1 := fun z => by
    have e1 := linear_value_le h hk hv z
    have e2 := linear_value_eq h hk hv (kstar_le_f h hk).2
    have e3 := hk z
    have e : A / (1 - β) * (1 - β) = A := div_mul_cancel₀ A h1β.ne'
    rw [e2]
    nlinarith [h.β_pos]
  -- `ψ` is nondecreasing below `k*`
  have hmono : ∀ z w : Icc (0 : ℝ) xbar, z ≤ w → w ≤ kstar →
      β * v z - z.1 ≤ β * v w - w.1 := fun z w hzw hwk => by
    have hzw' : z.1 ≤ w.1 := hzw
    have hwk' : w.1 ≤ kstar.1 := hwk
    rcases eq_or_lt_of_le (hzw'.trans hwk') with he | hlt
    · have hz : z = w := Subtype.ext (le_antisymm hzw' (he ▸ hwk'))
      rw [hz]
    set θ := (kstar.1 - w.1) / (kstar.1 - z.1)
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
    have hθ1 : θ ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have hne : kstar.1 - z.1 ≠ 0 := by linarith
    have hcmb : cmb (convex_Icc 0 xbar) hθ0 hθ1 z kstar = w := by
      ext1
      simp only [cmb, smul_eq_mul, θ]
      field_simp
      ring
    have hc := hvc z kstar θ hθ0 hθ1
    rw [hcmb] at hc
    have hw : w.1 = θ * z.1 + (1 - θ) * kstar.1 := by
      have := congrArg Subtype.val hcmb
      simp only [cmb, smul_eq_mul] at this
      linarith
    have := hψ z
    have hθ1' : 0 ≤ 1 - θ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hθ1', h.β_pos]
  -- the policy maximizes `F(x, y) + βv(y) = f(x) + ψ(y)`
  have hge : ∀ z ∈ growthΓ f xbar x, obj (growthF id f xbar) β v (x, z) ≤
      obj (growthF id f xbar) β v (x, linearPolicy h kstar x) := fun z hz => by
    have hz' : z.1 ≤ f x.1 := hz
    simp only [obj, growthF, id, linearPolicy]
    rcases le_total (f x.1) kstar.1 with hfk | hfk
    · have hmin : min (f x.1) kstar.1 = f x.1 := min_eq_left hfk
      have := hmono z ⟨f x.1, growth_f_nonneg h x, hfk.trans kstar.2.2⟩ hz' hfk
      simp only [hmin]
      simp only at this
      linarith
    · have hmin : min (f x.1) kstar.1 = kstar.1 := min_eq_right hfk
      have hks : (⟨min (f x.1) kstar.1, le_min (growth_f_nonneg h x) kstar.2.1,
          (min_le_right _ _).trans kstar.2.2⟩ : Icc (0 : ℝ) xbar) = kstar :=
        Subtype.ext hmin
      rw [hks]
      have := hψ z
      linarith
  have hmem : linearPolicy h kstar x ∈ growthΓ f xbar x :=
    show min (f x.1) kstar.1 ≤ f x.1 from min_le_left _ _
  refine ⟨hmem, le_antisymm ?_ ?_⟩
  · exact le_maxValue (continuousOn_obj (growth_assumption44 h) v.continuous)
      ((growth_assumption43 h).compact x) hmem
  · obtain ⟨y, hy, hyv, -⟩ := exists_argmax (continuousOn_obj (growth_assumption44 h)
      v.continuous) ((growth_assumption43 h).compact x) ((growth_assumption43 h).nonempty x)
    rw [← hyv]
    exact hge y hy

/-- **Exercise 5.3a, what fails.** With `f` strictly concave the policy is unique, and wherever
`f(k) < k*` it is `g(k) = f(k)`: nothing is consumed, so the conclusion `0 < g(k) < f(k)` of
Exercise 5.1d fails (there is no Inada condition). If `k* > 0` such `k > 0` exist. -/
theorem ex_5_3a_corner [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp id f β xbar)
    (hf : StrictConcaveOn ℝ (Ici 0) f)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    (∀ x : Icc (0 : ℝ) xbar, f x.1 < kstar.1 →
      (argmaxFn (growthΓ f xbar) (obj (growthF id f xbar) β v) x).1 = f x.1) ∧
    (0 < kstar.1 → ∃ x : Icc (0 : ℝ) xbar, 0 < x.1 ∧ f x.1 < kstar.1) := by
  obtain ⟨-, hUA, -⟩ := ex_5_3a_strict h hf hv
  refine ⟨fun x hx => ?_, fun hpos => ?_⟩
  · have hg := hUA.argmax_eq x
    have hmem := ex_5_3c h hf.concaveOn hk hv x
    rw [hg] at hmem
    rw [← hmem]
    exact min_eq_left hx.le
  · obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1
      (h.f_cont 0 (mem_Ici.2 le_rfl)) kstar.1 hpos
    set x := min (δ / 2) xbar
    have hx0 : 0 < x := lt_min (by linarith) h.xbar_pos
    refine ⟨⟨x, hx0.le, min_le_right _ _⟩, hx0, ?_⟩
    have := hball (mem_Ici.2 hx0.le) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx0]
      exact (min_le_left _ _).trans_lt (by linarith))
    rw [Real.dist_eq, h.f_zero, sub_zero] at this
    exact (le_abs_self _).trans_lt this

end StokeyLucasPrescott.DeterministicApplications
