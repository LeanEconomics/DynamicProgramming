/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.GrowthCertaintyDDGrowthDifferentiability

/-!
# Global stability in the one-sector growth model

Copied unchanged (apart from imports and the namespace `GrowthCertaintyDD`) from the Chapter 6
project `DeterministicDynamics` (module `DeterministicDynamics.GrowthStability`),
for Exercise 16.1(e)–(g).

SLP §6.1, pp. 133–136: `v(k) = max_{0 ≤ y ≤ f(k)} {U[f(k) − y] + βv(y)}` with `f`, `U` strictly
increasing, strictly concave and continuously differentiable, `f(0) = 0`, `f'(0+) = ∞`,
`f'(∞) = 0` and `U'(0+) = ∞` (`GrowthDyn`).

* `exists_kbar`: there is a unique `k̄ > 0` with `f(k̄) = k̄`, with `k < f(k)` on `(0, k̄)` and
  `f(k) < k` beyond; Section 5.1 applies on `[0, k̄]` (`growthHyp_kbar`).
* **Exercise 6.1a** (`ex_6_1a`): for `k ∈ (0, k̄]` the maximum is interior,
  `0 < g(k) < f(k)`; `v` is continuously differentiable on `(0, k̄)` with (3)
  `v'(k) = U'[f(k) − g(k)]f'(k)`; and (2) `U'[f(k) − g(k)] = βv'[g(k)]` holds on `(0, k̄]`.
* **Exercise 6.1b** (`ex_6_1b`): `g` is strictly increasing.
* `exists_setting61`: `k̄` and the solution `v` of (1) on `[0, k̄]` exist (Exercise 5.1).
* **Proposition** (p. 136, `prop_6_1`): the stationary points of `g` are `0` and
  `k* = f'⁻¹(1/β)`, and from every `k₀ ∈ (0, k̄]` the path `k_{t+1} = g(k_t)` converges
  monotonically to `k*`.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

namespace GrowthCertaintyDD

open Set Filter Topology BoundedContinuousFunction

/-! ### Derivatives of concave functions -/

/-- A concave function lies below its tangent line. -/
theorem tangent_le {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConcaveOn ℝ s φ) {a b d : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) (hd : HasDerivAt φ d a) : φ b ≤ φ a + d * (b - a) := by
  have := concave_le_fderiv hφ ha hb hd.hasFDerivAt
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at this
  linarith

/-- A strictly concave function lies strictly below its tangent line off the point of tangency. -/
theorem tangent_lt {φ : ℝ → ℝ} {s : Set ℝ} (hφ : StrictConcaveOn ℝ s φ) {a b d : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) (hab : a ≠ b) (hd : HasDerivAt φ d a) : φ b < φ a + d * (b - a) := by
  have hm : (a + b) / 2 ∈ s := by
    have := hφ.1 ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1; simp only [smul_eq_mul]; ring
  have h1 := tangent_le hφ.concaveOn ha hm hd
  have h2 := hφ.2 ha hb hab (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at h2
  rw [show (1 / 2 : ℝ) * a + 1 / 2 * b = (a + b) / 2 by ring] at h2
  linarith

/-- The derivative of a concave function falls. -/
theorem deriv_le_of_concave {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConcaveOn ℝ s φ) {a b da db : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≤ b) (hda : HasDerivAt φ da a) (hdb : HasDerivAt φ db b) :
    db ≤ da := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_of_eq (hdb.unique hda)
  have h1 := tangent_le hφ ha hb hda
  have h2 := tangent_le hφ hb ha hdb
  nlinarith

/-- The derivative of a strictly concave function falls strictly. -/
theorem deriv_lt_of_strictConcave {φ : ℝ → ℝ} {s : Set ℝ} (hφ : StrictConcaveOn ℝ s φ)
    {a b da db : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) (hda : HasDerivAt φ da a)
    (hdb : HasDerivAt φ db b) : db < da := by
  have h1 := tangent_lt hφ ha hb hab.ne hda
  have h2 := tangent_lt hφ hb ha hab.ne' hdb
  nlinarith

/-! ### The model -/

/-- The assumptions of §6.1 (p. 134). -/
structure GrowthDyn (U f U' f' : ℝ → ℝ) (β : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  f_zero : f 0 = 0
  f_cont : ContinuousOn f (Ici 0)
  f_deriv : ∀ k, 0 < k → HasDerivAt f (f' k) k
  f'_cont : ContinuousOn f' (Ioi 0)
  f_mono : StrictMonoOn f (Ici 0)
  f_conc : StrictConcaveOn ℝ (Ici 0) f
  f'_zero : Tendsto f' (𝓝[>] 0) atTop
  f'_top : Tendsto f' atTop (𝓝 0)
  U_cont : ContinuousOn U (Ici 0)
  U_deriv : ∀ c, 0 < c → HasDerivAt U (U' c) c
  U'_cont : ContinuousOn U' (Ioi 0)
  U_mono : StrictMonoOn U (Ici 0)
  U_conc : StrictConcaveOn ℝ (Ici 0) U
  U'_zero : Tendsto U' (𝓝[>] 0) atTop

variable {U f U' f' : ℝ → ℝ} {β : ℝ}

/-- Auxiliary result `GrowthDyn.f'_lt` of the copied Chapter 4–6 development. -/
theorem GrowthDyn.f'_lt (h : GrowthDyn U f U' f' β) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    f' b < f' a :=
  deriv_lt_of_strictConcave h.f_conc (mem_Ici.2 ha.le) (mem_Ici.2 (ha.trans hab).le) hab
    (h.f_deriv a ha) (h.f_deriv b (ha.trans hab))

/-- Auxiliary result `GrowthDyn.U'_lt` of the copied Chapter 4–6 development. -/
theorem GrowthDyn.U'_lt (h : GrowthDyn U f U' f' β) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    U' b < U' a :=
  deriv_lt_of_strictConcave h.U_conc (mem_Ici.2 ha.le) (mem_Ici.2 (ha.trans hab).le) hab
    (h.U_deriv a ha) (h.U_deriv b (ha.trans hab))

/-- Auxiliary result `GrowthDyn.U'_pos` of the copied Chapter 4–6 development. -/
theorem GrowthDyn.U'_pos (h : GrowthDyn U f U' f' β) {c : ℝ} (hc : 0 < c) : 0 < U' c := by
  have h1 := tangent_lt h.U_conc (mem_Ici.2 hc.le) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c + 1))
    (by linarith : c ≠ c + 1) (h.U_deriv c hc)
  have h2 := h.U_mono (mem_Ici.2 hc.le) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c + 1))
    (by linarith : c < c + 1)
  nlinarith

/-- `f(k) ≥ k f'(k)` (the tangent at `k` passes above `f(0) = 0`). -/
theorem GrowthDyn.f_ge_tangent (h : GrowthDyn U f U' f' β) {k : ℝ} (hk : 0 < k) :
    k * f' k ≤ f k := by
  have := tangent_le h.f_conc.concaveOn (mem_Ici.2 hk.le) (mem_Ici.2 le_rfl) (h.f_deriv k hk)
  rw [h.f_zero] at this
  linarith

/-- The average product `f(k)/k` falls strictly: `x f(y) < y f(x)` for `0 < x < y`. -/
theorem GrowthDyn.mul_lt (h : GrowthDyn U f U' f' β) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    x * f y < y * f x := by
  have hy := hx.trans hxy
  have h1 : 0 < 1 - x / y := sub_pos.2 ((div_lt_one hy).2 hxy)
  have := h.f_conc.2 (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le) hy.ne h1 (div_pos hx hy)
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, h.f_zero] at this
  rw [div_mul_cancel₀ x hy.ne', div_mul_eq_mul_div, div_lt_iff₀ hy] at this
  linarith

/-- The maximum maintainable capital stock: a unique `k̄ > 0` with `f(k̄) = k̄`; `k < f(k)` below
it and `f(k) < k` above it. -/
theorem exists_kbar (h : GrowthDyn U f U' f' β) :
    ∃ kbar, 0 < kbar ∧ f kbar = kbar ∧ (∀ k, 0 < k → k < kbar → k < f k) ∧
      ∀ k, kbar < k → f k < k := by
  -- `f(a) > a` for small `a`
  obtain ⟨a, ha0, ha⟩ : ∃ a, 0 < a ∧ a < f a := by
    obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1
      (eventually_nhdsWithin_iff.1 (h.f'_zero.eventually (eventually_gt_atTop 2)))
    refine ⟨δ / 2, half_pos hδ, ?_⟩
    have hd : dist (δ / 2) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
      linarith
    have h2 : 2 < f' (δ / 2) := hδs hd (half_pos hδ)
    have := h.f_ge_tangent (half_pos hδ)
    nlinarith
  -- `f(b) < b` for large `b`
  obtain ⟨b, hab, hb⟩ : ∃ b, a < b ∧ f b < b := by
    obtain ⟨K, hK⟩ := eventually_atTop.1 (h.f'_top.eventually (gt_mem_nhds (by norm_num :
      (0 : ℝ) < 1 / 2)))
    set K' := max K a + 1
    have hK'0 : 0 < K' := by have := le_max_right K a; linarith
    refine ⟨max K' (2 * f K') + 1, ?_, ?_⟩
    · have := le_max_left K' (2 * f K')
      have := le_max_right K a
      linarith
    have hb0 : K' ≤ max K' (2 * f K') + 1 := by have := le_max_left K' (2 * f K'); linarith
    have ht := tangent_le h.f_conc.concaveOn (mem_Ici.2 hK'0.le)
      (mem_Ici.2 (hK'0.le.trans hb0)) (h.f_deriv K' hK'0)
    have hKK : K ≤ K' := by have := le_max_left K a; linarith
    have hfK := hK K' hKK
    have := le_max_right K' (2 * f K')
    nlinarith
  -- the intermediate value theorem for `f(k) − k`
  have hcont : ContinuousOn (fun k => f k - k) (Icc a b) :=
    (h.f_cont.mono fun k hk => mem_Ici.2 (ha0.le.trans hk.1)).sub continuousOn_id
  obtain ⟨kb, hkb, hkb0⟩ := intermediate_value_Icc' hab.le hcont
    (show (0 : ℝ) ∈ Icc (f b - b) (f a - a) from ⟨by linarith, by linarith⟩)
  have hkb0' : f kb = kb := by simp only at hkb0; linarith
  have hkpos : 0 < kb := ha0.trans_le hkb.1
  refine ⟨kb, hkpos, hkb0', fun k hk hkk => ?_, fun k hk => ?_⟩
  · have := h.mul_lt hk hkk
    rw [hkb0'] at this
    nlinarith
  · have := h.mul_lt hkpos hk
    rw [hkb0'] at this
    nlinarith

/-! ### The policy function on `[0, k̄]` -/

/-- On `[0, k̄]`, Section 5.1 applies. -/
theorem growthHyp_kbar (h : GrowthDyn U f U' f' β) {kbar : ℝ} (hk0 : 0 < kbar)
    (hkf : f kbar = kbar) (hbelow : ∀ k, 0 < k → k < kbar → k < f k) :
    GrowthHyp U f β kbar where
  β_pos := h.β_pos
  β_lt := h.β_lt
  U_cont := h.U_cont
  U_mono := h.U_mono
  f_cont := h.f_cont
  f_zero := h.f_zero
  xbar_pos := hk0
  f_maintain := fun x hx => by
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hx.1 with h0 | hpos
      · rw [← h0, h.f_zero]
      rcases eq_or_lt_of_le hx.2 with he | hlt
      · rw [he, hkf]
      · exact (hbelow x hpos hlt).le
    · rw [← hkf]
      exact h.f_mono.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hk0.le) hx.2
  f_mono := h.f_mono

/-- The policy `g`, extended by zero off `[0, k̄]`. -/
noncomputable def gpol (U f : ℝ → ℝ) (β kbar : ℝ) [Nonempty (Icc (0 : ℝ) kbar)]
    (v : Icc (0 : ℝ) kbar →ᵇ ℝ) (k : ℝ) : ℝ := by
  classical exact if hk : k ∈ Icc 0 kbar then
    (argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v) ⟨k, hk⟩).1 else 0

/-- Auxiliary result `gpol_of_mem` of the copied Chapter 4–6 development. -/
theorem gpol_of_mem {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)] (v : Icc (0 : ℝ) kbar →ᵇ ℝ) {k : ℝ}
    (hk : k ∈ Icc 0 kbar) :
    gpol U f β kbar v k = (argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v) ⟨k, hk⟩).1 := by
  simp only [gpol, hk, ↓reduceDIte]

/-- `v` is strictly concave on `[0, k̄]`. -/
theorem strictConcaveOn_liftR {kbar : ℝ} {v : Icc (0 : ℝ) kbar → ℝ}
    (hv : IsStrictConcaveS (convex_Icc 0 kbar) v) :
    StrictConcaveOn ℝ (Icc 0 kbar) (liftR kbar v) := by
  refine ⟨convex_Icc 0 kbar, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  have hmem : a • x + b • y ∈ Icc (0 : ℝ) kbar := convex_Icc 0 kbar hx hy ha.le hb.le hab
  rw [liftR_of_mem v hx, liftR_of_mem v hy, liftR_of_mem v hmem, smul_eq_mul, smul_eq_mul]
  subst hb'
  exact hv ⟨x, hx⟩ ⟨y, hy⟩ (fun he => hxy (congrArg Subtype.val he)) a ha (by linarith)

/-- The setting of Exercise 6.1: `k̄`, the fixed point `v` of Section 5.1 on `[0, k̄]`, and its
policy. -/
structure Setting61 (U f U' f' : ℝ → ℝ) (β kbar : ℝ) (v : Icc (0 : ℝ) kbar →ᵇ ℝ) : Prop where
  dyn : GrowthDyn U f U' f' β
  kbar_pos : 0 < kbar
  kbar_fix : f kbar = kbar
  below : ∀ k, 0 < k → k < kbar → k < f k
  fixed : bellman (growth_assumption43 (growthHyp_kbar dyn kbar_pos kbar_fix below))
    (growth_assumption44 (growthHyp_kbar dyn kbar_pos kbar_fix below)) v = v

namespace Setting61

variable {kbar : ℝ} {v : Icc (0 : ℝ) kbar →ᵇ ℝ} (S : Setting61 U f U' f' β kbar v)
  [Nonempty (Icc (0 : ℝ) kbar)]
include S

omit [Nonempty (Icc (0 : ℝ) kbar)] in
/-- Auxiliary result `hyp` of the copied Chapter 4–6 development. -/
theorem hyp : GrowthHyp U f β kbar := growthHyp_kbar S.dyn S.kbar_pos S.kbar_fix S.below

omit [Nonempty (Icc (0 : ℝ) kbar)] in
/-- Auxiliary result `inada` of the copied Chapter 4–6 development. -/
theorem inada : Tendsto (deriv U) (𝓝[>] 0) atTop := by
  refine S.dyn.U'_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact ((S.dyn.U_deriv c hc).deriv).symm

/-- Auxiliary result `weak` of the copied Chapter 4–6 development. -/
theorem weak :
    IsStrictConcaveS (convex_Icc 0 kbar) v ∧
      UniqueArgmax (growthΓ f kbar) (obj (growthF U f kbar) β v) ∧
      Continuous (argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v)) := by
  exact ex_5_1c_weak S.hyp S.dyn.U_conc S.dyn.f_conc.concaveOn S.fixed

/-- Auxiliary result `gpol_mem` of the copied Chapter 4–6 development. -/
theorem gpol_mem {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    gpol U f β kbar v k ∈ Icc 0 kbar ∧ gpol U f β kbar v k ≤ f k := by
  rw [gpol_of_mem v hk]
  exact ⟨Subtype.mem _, (S.weak.2.1.argmaxFn_mem ⟨k, hk⟩).1⟩

/-- Auxiliary result `gpol_zero` of the copied Chapter 4–6 development. -/
theorem gpol_zero : gpol U f β kbar v 0 = 0 := by
  have hk : (0 : ℝ) ∈ Icc 0 kbar := ⟨le_rfl, S.kbar_pos.le⟩
  have := S.gpol_mem hk
  rw [S.dyn.f_zero] at this
  exact le_antisymm this.2 this.1.1

/-- The maximum is interior: `0 < g(k) < f(k)` for `k ∈ (0, k̄]`. -/
theorem gpol_interior {k : ℝ} (hk : 0 < k) (hkb : k ≤ kbar) :
    0 < gpol U f β kbar v k ∧ gpol U f β kbar v k < f k := by
  rw [gpol_of_mem v ⟨hk.le, hkb⟩]
  exact ex_5_1d_interior S.hyp S.dyn.U_conc S.dyn.f_conc.concaveOn
    (fun c hc => (S.dyn.U_deriv c hc).differentiableAt) S.inada S.fixed (x := ⟨k, hk.le, hkb⟩) hk

/-- Auxiliary result `gpol_lt_kbar` of the copied Chapter 4–6 development. -/
theorem gpol_lt_kbar {k : ℝ} (hk : 0 < k) (hkb : k ≤ kbar) : gpol U f β kbar v k < kbar := by
  have h1 := (S.gpol_interior hk hkb).2
  have h2 := (S.hyp.f_maintain k ⟨hk.le, hkb⟩).2
  linarith

/-- Auxiliary result `continuousOn_gpol` of the copied Chapter 4–6 development. -/
theorem continuousOn_gpol : ContinuousOn (gpol U f β kbar v) (Icc 0 kbar) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (Icc (0 : ℝ) kbar).domRestrict (gpol U f β kbar v) =
      fun k => (argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v) k).1 := by
    funext k
    simp only [Set.domRestrict_apply]
    rw [gpol_of_mem v k.2]
  rw [e]
  exact continuous_subtype_val.comp S.weak.2.2

/-- (3): `v'(k) = U'[f(k) − g(k)]f'(k)` on `(0, k̄)`. -/
theorem hasDerivAt_v {k : ℝ} (hk : 0 < k) (hkb : k < kbar) :
    HasDerivAt (liftR kbar v) (U' (f k - gpol U f β kbar v k) * f' k) k := by
  have hint := S.gpol_interior hk hkb.le
  rw [gpol_of_mem v ⟨hk.le, hkb.le⟩] at hint ⊢
  exact ex_5_1d S.hyp S.dyn.U_conc S.dyn.f_conc.concaveOn S.fixed (x₀ := ⟨k, hk.le, hkb.le⟩)
    ⟨hk, hkb⟩ hint.2 (S.dyn.U_deriv _ (by linarith [hint.2])) (S.dyn.f_deriv k hk)

/-- (2): `U'[f(k) − g(k)] = βv'[g(k)]` on `(0, k̄]`. -/
theorem foc {k : ℝ} (hk : 0 < k) (hkb : k ≤ kbar) :
    U' (f k - gpol U f β kbar v k) =
      β * (U' (f (gpol U f β kbar v k) - gpol U f β kbar v (gpol U f β kbar v k)) *
        f' (gpol U f β kbar v k)) := by
  set y := gpol U f β kbar v k
  have hint := S.gpol_interior hk hkb
  have hyk : y < kbar := S.gpol_lt_kbar hk hkb
  have hc : 0 < f k - y := by linarith [hint.2]
  have hdv := S.hasDerivAt_v hint.1 hyk
  set φ : ℝ → ℝ := fun z => U (f k - z) + β * liftR kbar v z
  have hφ : HasDerivAt φ (U' (f k - y) * (0 - 1) +
      β * (U' (f y - gpol U f β kbar v y) * f' y)) y :=
    ((S.dyn.U_deriv _ hc).comp y ((hasDerivAt_const y (f k)).sub (hasDerivAt_id y))).add
      (hdv.const_mul β)
  -- `y` maximizes `φ` over `(0, f(k))`
  have hUA := S.weak.2.1
  have hmax : IsLocalMax φ y := by
    filter_upwards [Ioo_mem_nhds hint.1 hint.2] with z hz
    have hzI : z ∈ Icc (0 : ℝ) kbar :=
      ⟨hz.1.le, hz.2.le.trans (S.hyp.f_maintain k ⟨hk.le, hkb⟩).2⟩
    have hyI : y ∈ Icc (0 : ℝ) kbar := (S.gpol_mem ⟨hk.le, hkb⟩).1
    have hmem := hUA.argmaxFn_mem ⟨k, hk.le, hkb⟩
    have hle := le_maxValue hUA.cont (hUA.compact ⟨k, hk.le, hkb⟩)
      (z := ⟨z, hzI⟩) (show (⟨z, hzI⟩ : Icc (0 : ℝ) kbar) ∈ growthΓ f kbar ⟨k, hk.le, hkb⟩ from
        hz.2.le)
    rw [← hmem.2] at hle
    simp only [φ, liftR_of_mem v hzI, liftR_of_mem v hyI]
    have hy : y = (argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v) ⟨k, hk.le, hkb⟩).1 :=
      gpol_of_mem v ⟨hk.le, hkb⟩
    have hyv : (⟨y, hyI⟩ : Icc (0 : ℝ) kbar) =
        argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v) ⟨k, hk.le, hkb⟩ := Subtype.ext hy
    rw [hyv, hy]
    simpa [obj, growthF] using hle
  have := hmax.hasDerivAt_eq_zero hφ
  linarith

/-- `v` is strictly concave on `[0, k̄]`. -/
theorem strictConcave_v : StrictConcaveOn ℝ (Icc 0 kbar) (liftR kbar v) :=
  strictConcaveOn_liftR S.weak.1

end Setting61

/-- **Exercise 6.1a.** For `k ∈ (0, k̄]` the maximum in (1) is interior; `v` is continuously
differentiable on `(0, k̄)`, with (3) `v'(k) = U'[f(k) − g(k)]f'(k)`; and (2)
`U'[f(k) − g(k)] = βv'[g(k)]` holds on `(0, k̄]`. -/
theorem ex_6_1a {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)] {v : Icc (0 : ℝ) kbar →ᵇ ℝ}
    (S : Setting61 U f U' f' β kbar v) :
    (∀ k, 0 < k → k ≤ kbar → 0 < gpol U f β kbar v k ∧ gpol U f β kbar v k < f k) ∧
      (∀ k, 0 < k → k < kbar →
        HasDerivAt (liftR kbar v) (U' (f k - gpol U f β kbar v k) * f' k) k) ∧
      ContinuousOn (fun k => U' (f k - gpol U f β kbar v k) * f' k) (Ioo 0 kbar) ∧
      ∀ k, 0 < k → k ≤ kbar → HasDerivAt (liftR kbar v)
        (U' (f (gpol U f β kbar v k) - gpol U f β kbar v (gpol U f β kbar v k)) *
          f' (gpol U f β kbar v k)) (gpol U f β kbar v k) ∧
        U' (f k - gpol U f β kbar v k) =
          β * (U' (f (gpol U f β kbar v k) - gpol U f β kbar v (gpol U f β kbar v k)) *
            f' (gpol U f β kbar v k)) := by
  refine ⟨fun k hk hkb => S.gpol_interior hk hkb, fun k hk hkb => S.hasDerivAt_v hk hkb, ?_,
    fun k hk hkb => ⟨S.hasDerivAt_v (S.gpol_interior hk hkb).1 (S.gpol_lt_kbar hk hkb),
      S.foc hk hkb⟩⟩
  intro k hk
  have hc : 0 < f k - gpol U f β kbar v k := by linarith [(S.gpol_interior hk.1 hk.2.le).2]
  have hfc : ContinuousAt f k := (S.dyn.f_deriv k hk.1).continuousAt
  have hgc : ContinuousAt (gpol U f β kbar v) k :=
    (S.continuousOn_gpol k (Ioo_subset_Icc_self hk)).continuousAt (Icc_mem_nhds hk.1 hk.2)
  have hU'c : ContinuousAt U' (f k - gpol U f β kbar v k) :=
    S.dyn.U'_cont.continuousAt (Ioi_mem_nhds hc)
  have hf'c : ContinuousAt f' k := S.dyn.f'_cont.continuousAt (Ioi_mem_nhds hk.1)
  have hsub : ContinuousAt (fun x => f x - gpol U f β kbar v x) k := hfc.sub hgc
  exact ((ContinuousAt.comp (f := fun x => f x - gpol U f β kbar v x) hU'c hsub).mul
    hf'c).continuousWithinAt

/-- **Exercise 6.1b.** The policy `g` is strictly increasing on `[0, k̄]`. -/
theorem ex_6_1b {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)] {v : Icc (0 : ℝ) kbar →ᵇ ℝ}
    (S : Setting61 U f U' f' β kbar v) :
    StrictMonoOn (gpol U f β kbar v) (Icc 0 kbar) := by
  intro k hk k' hk' hkk'
  rcases eq_or_lt_of_le hk.1 with h0 | hpos
  · rw [← h0, S.gpol_zero]
    exact (S.gpol_interior (h0 ▸ hkk' : 0 < k') hk'.2).1
  have hpos' : 0 < k' := hpos.trans hkk'
  by_contra hcon
  push Not at hcon
  set y := gpol U f β kbar v k
  set y' := gpol U f β kbar v k'
  have hi := S.gpol_interior hpos hk.2
  have hi' := S.gpol_interior hpos' hk'.2
  -- consumption rises with `k`
  have hfk : f k < f k' := S.dyn.f_mono (mem_Ici.2 hpos.le) (mem_Ici.2 hpos'.le) hkk'
  have hU : U' (f k' - y') < U' (f k - y) := S.dyn.U'_lt (by linarith) (by linarith)
  rw [S.foc hpos hk.2, S.foc hpos' hk'.2] at hU
  -- but `v'` falls, and `y' ≤ y`
  have hd := deriv_le_of_concave S.strictConcave_v.concaveOn
    (⟨hi'.1.le, (S.gpol_lt_kbar hpos' hk'.2).le⟩ : y' ∈ Icc 0 kbar)
    (⟨hi.1.le, (S.gpol_lt_kbar hpos hk.2).le⟩ : y ∈ Icc 0 kbar) hcon
    (S.hasDerivAt_v hi'.1 (S.gpol_lt_kbar hpos' hk'.2))
    (S.hasDerivAt_v hi.1 (S.gpol_lt_kbar hpos hk.2))
  have := mul_le_mul_of_nonneg_left hd S.dyn.β_pos.le
  linarith

/-! ### Stationary points and global stability -/

/-- `k* = f'⁻¹(1/β)`: there is a unique `k* > 0` with `f'(k*) = 1/β`. -/
theorem exists_kstar (h : GrowthDyn U f U' f' β) :
    ∃ kstar, 0 < kstar ∧ f' kstar = 1 / β ∧ ∀ k, 0 < k → f' k = 1 / β → k = kstar := by
  have hβ := h.β_pos
  obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (h.f'_zero.eventually (eventually_gt_atTop (1 / β))))
  set a := δ / 2
  have ha : 0 < a := half_pos hδ
  have hda : dist a 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ha]
    exact half_lt_self hδ
  have hfa : 1 / β < f' a := hδs hda ha
  obtain ⟨K, hK⟩ := eventually_atTop.1 (h.f'_top.eventually (gt_mem_nhds (one_div_pos.2 hβ)))
  set b := max K a + 1
  have hab : a < b := by have := le_max_right K a; linarith
  have hfb : f' b < 1 / β := hK b (by have := le_max_left K a; linarith)
  have hcont : ContinuousOn f' (Icc a b) := h.f'_cont.mono fun k hk => ha.trans_le hk.1
  obtain ⟨ks, hks, hks1⟩ := intermediate_value_Icc' hab.le hcont ⟨hfb.le, hfa.le⟩
  refine ⟨ks, ha.trans_le hks.1, hks1, fun k hk hk1 => ?_⟩
  rcases lt_trichotomy k ks with hlt | heq | hgt
  · have := h.f'_lt hk hlt; linarith
  · exact heq
  · have := h.f'_lt (ha.trans_le hks.1) hgt; linarith

namespace Setting61

variable {kbar : ℝ} {v : Icc (0 : ℝ) kbar →ᵇ ℝ} (S : Setting61 U f U' f' β kbar v)
  [Nonempty (Icc (0 : ℝ) kbar)]
include S

/-- (5) with strict inequality: off the stationary points, `[f'(k) − 1/β][k − g(k)] < 0`. -/
theorem five {k : ℝ} (hk : 0 < k) (hkb : k < kbar) (hne : gpol U f β kbar v k ≠ k) :
    (f' k - 1 / β) * (k - gpol U f β kbar v k) < 0 := by
  set y := gpol U f β kbar v k
  have hi := S.gpol_interior hk hkb.le
  have hyk := S.gpol_lt_kbar hk hkb.le
  have hc : 0 < f k - y := by linarith [hi.2]
  have hU := S.dyn.U'_pos hc
  have hfoc := S.foc hk hkb.le
  have hβ := S.dyn.β_pos
  have hdk := S.hasDerivAt_v hk hkb
  have hdy := S.hasDerivAt_v hi.1 hyk
  set dk := U' (f k - y) * f' k
  set dy := U' (f y - gpol U f β kbar v y) * f' y
  have hkI : k ∈ Icc (0 : ℝ) kbar := ⟨hk.le, hkb.le⟩
  have hyI : y ∈ Icc (0 : ℝ) kbar := ⟨hi.1.le, hyk.le⟩
  -- strict concavity of `v`: `(v'(k) − v'(g(k)))(k − g(k)) < 0`
  have hmono : (dk - dy) * (k - y) < 0 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := deriv_lt_of_strictConcave S.strictConcave_v hyI hkI hlt hdy hdk
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    · have := deriv_lt_of_strictConcave S.strictConcave_v hkI hyI hgt hdk hdy
      exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  -- `v'(g(k)) = U'(c)/β`
  have hdy' : dy = U' (f k - y) / β := by
    rw [eq_div_iff hβ.ne']
    linarith
  have e : (dk - dy) * (k - y) = U' (f k - y) * ((f' k - 1 / β) * (k - y)) := by
    rw [hdy']
    simp only [dk]
    ring
  rw [e] at hmono
  exact neg_of_mul_neg_right hmono hU.le

/-- The positive stationary points of `g` solve `f'(k) = 1/β`. -/
theorem fixed_iff {k : ℝ} (hk : 0 < k) (hkb' : k < kbar) :
    gpol U f β kbar v k = k ↔ f' k = 1 / β := by
  have hβ := S.dyn.β_pos
  have hkb := hkb'.le
  constructor
  · intro hfix
    have hfoc := S.foc hk hkb
    rw [hfix, hfix] at hfoc
    have hc : 0 < f k - k := by
      have := (S.gpol_interior hk hkb).2
      rw [hfix] at this
      linarith
    have hU := S.dyn.U'_pos hc
    field_simp
    nlinarith
  · intro hf1
    by_contra hne
    have := S.five hk hkb' hne
    rw [hf1, sub_self, zero_mul] at this
    exact lt_irrefl 0 this

end Setting61

/-- **Proposition** (p. 136). The stationary points of `g` on `[0, k̄]` are `0` and `k*`, where
`f'(k*) = 1/β`, and from every `k₀ ∈ (0, k̄]` the path `k_{t+1} = g(k_t)` converges monotonically
to `k*`. -/
theorem prop_6_1 {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)] {v : Icc (0 : ℝ) kbar →ᵇ ℝ}
    (S : Setting61 U f U' f' β kbar v) {kstar : ℝ} (hks0 : 0 < kstar) (hks : f' kstar = 1 / β) :
    kstar < kbar ∧
      (∀ k ∈ Icc 0 kbar, gpol U f β kbar v k = k ↔ k = 0 ∨ k = kstar) ∧
      ∀ k₀, 0 < k₀ → k₀ ≤ kbar →
        (Monotone (fun t => (gpol U f β kbar v)^[t] k₀) ∨
          Antitone (fun t => (gpol U f β kbar v)^[t] k₀)) ∧
        Tendsto (fun t => (gpol U f β kbar v)^[t] k₀) atTop (𝓝 kstar) := by
  have hβ := S.dyn.β_pos
  have hβ1 := S.dyn.β_lt
  set g := gpol U f β kbar v
  -- `k* < k̄`, since `f'(k̄) ≤ 1 < 1/β`
  have hlt : kstar < kbar := by
    by_contra hge
    push Not at hge
    have h1 := S.dyn.f_ge_tangent S.kbar_pos
    rw [S.kbar_fix] at h1
    have h2 : f' kbar ≤ 1 := by nlinarith [S.kbar_pos]
    have h3 : 1 < 1 / β := by rw [lt_div_iff₀ hβ]; linarith
    rcases eq_or_lt_of_le hge with he | hgt
    · rw [← he] at hks; linarith
    · have := S.dyn.f'_lt S.kbar_pos hgt; linarith
  have hkI : kstar ∈ Icc (0 : ℝ) kbar := ⟨hks0.le, hlt.le⟩
  have hgks : g kstar = kstar := (S.fixed_iff hks0 hlt).2 hks
  have hmono := ex_6_1b S
  -- the sign of `g(k) − k`
  have below : ∀ k, 0 < k → k < kstar → k < g k := fun k hk hkk => by
    have hne : g k ≠ k := fun he => by
      have := (S.fixed_iff hk (hkk.trans hlt)).1 he
      have := S.dyn.f'_lt hk hkk
      linarith
    have h5 := S.five hk (hkk.trans hlt) hne
    have hf : 1 / β < f' k := by rw [← hks]; exact S.dyn.f'_lt hk hkk
    nlinarith
  have above : ∀ k, kstar < k → k ≤ kbar → g k < k := fun k hkk hkb => by
    have hk : 0 < k := hks0.trans hkk
    rcases eq_or_lt_of_le hkb with he | hkb'
    · have := (S.gpol_interior hk hkb).2
      rw [he, S.kbar_fix] at this
      rw [he]; exact this
    have hne : g k ≠ k := fun he => by
      have := (S.fixed_iff hk hkb').1 he
      have := S.dyn.f'_lt hks0 hkk
      linarith
    have h5 := S.five hk hkb' hne
    have hf : f' k < 1 / β := by rw [← hks]; exact S.dyn.f'_lt hks0 hkk
    nlinarith
  refine ⟨hlt, fun k hk => ⟨fun hfix => ?_, ?_⟩, fun k₀ hk₀ hk₀b => ?_⟩
  · rcases eq_or_lt_of_le hk.1 with h0 | hpos
    · exact Or.inl h0.symm
    · exact Or.inr (by
        rcases lt_trichotomy k kstar with h1 | h1 | h1
        · exact absurd hfix (ne_of_gt (below k hpos h1))
        · exact h1
        · exact absurd hfix (ne_of_lt (above k h1 hk.2)))
  · rintro (rfl | rfl)
    · exact S.gpol_zero
    · exact hgks
  -- the path stays in `(0, k̄]` and is monotone
  set x : ℕ → ℝ := fun t => g^[t] k₀
  have hstep : ∀ t, x (t + 1) = g (x t) := fun t => by
    simp only [x, Function.iterate_succ_apply']
  have hpos : ∀ t, 0 < x t ∧ x t ≤ kbar := by
    intro t
    induction t with
    | zero => exact ⟨hk₀, hk₀b⟩
    | succ t ih =>
      rw [hstep]
      exact ⟨(S.gpol_interior ih.1 ih.2).1, (S.gpol_lt_kbar ih.1 ih.2).le⟩
  have hcont : ∀ L, 0 < L → L ≤ kbar → Tendsto x atTop (𝓝 L) → L = kstar := by
    intro L hL hLb hx
    have hgL : ContinuousWithinAt g (Icc 0 kbar) L := S.continuousOn_gpol L ⟨hL.le, hLb⟩
    have h1 : Tendsto (fun t => g (x t)) atTop (𝓝 (g L)) :=
      hgL.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall fun t =>
        ⟨(hpos t).1.le, (hpos t).2⟩⟩)
    have h2 : Tendsto (fun t => g (x t)) atTop (𝓝 L) := by
      simp only [← hstep]
      exact hx.comp (tendsto_add_atTop_nat 1)
    have hfix : g L = L := tendsto_nhds_unique h1 h2
    have hLlt : L < kbar := by
      have : g L < kbar := S.gpol_lt_kbar hL hLb
      rwa [hfix] at this
    exact ((S.fixed_iff hL hLlt).1 hfix) |> fun h1 => (by
      obtain ⟨k', -, -, huniq⟩ := exists_kstar S.dyn
      exact (huniq L hL h1).trans (huniq kstar hks0 hks).symm)
  rcases le_total k₀ kstar with hle | hge
  · -- from below: the path rises to `k*`
    have hbd : ∀ t, x t ≤ kstar := by
      intro t
      induction t with
      | zero => exact hle
      | succ t ih =>
        rw [hstep, ← hgks]
        exact hmono.monotoneOn ⟨(hpos t).1.le, (hpos t).2⟩ hkI ih
    have hm : Monotone x := monotone_nat_of_le_succ fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hbd t) with he | hlt'
      · rw [he, hgks]
      · exact (below (x t) (hpos t).1 hlt').le
    have hx := tendsto_atTop_ciSup hm ⟨kstar, by rintro _ ⟨t, rfl⟩; exact hbd t⟩
    have hL0 : 0 < ⨆ t, x t := (hpos 0).1.trans_le (le_ciSup ⟨kstar, by
      rintro _ ⟨t, rfl⟩; exact hbd t⟩ 0)
    have hLb : (⨆ t, x t) ≤ kbar := ciSup_le fun t => (hpos t).2
    exact ⟨Or.inl hm, hcont _ hL0 hLb hx ▸ hx⟩
  · -- from above: the path falls to `k*`
    have hbd : ∀ t, kstar ≤ x t := by
      intro t
      induction t with
      | zero => exact hge
      | succ t ih =>
        rw [hstep, ← hgks]
        exact hmono.monotoneOn hkI ⟨(hpos t).1.le, (hpos t).2⟩ ih
    have ha : Antitone x := antitone_nat_of_succ_le fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hbd t) with he | hlt'
      · rw [← he, hgks]
      · exact (above (x t) hlt' (hpos t).2).le
    have hx := tendsto_atTop_ciInf ha ⟨kstar, by rintro _ ⟨t, rfl⟩; exact hbd t⟩
    have hL0 : kstar ≤ ⨅ t, x t := le_ciInf hbd
    have hLb : (⨅ t, x t) ≤ kbar := (ciInf_le ⟨kstar, by
      rintro _ ⟨t, rfl⟩; exact hbd t⟩ 0).trans (hpos 0).2
    exact ⟨Or.inr ha, hcont _ (hks0.trans_le hL0) hLb hx ▸ hx⟩

/-- The setting of §6.1 exists: `k̄`, and the unique bounded continuous solution `v` of (1) on
`[0, k̄]` (Exercise 5.1). -/
theorem exists_setting61 (h : GrowthDyn U f U' f' β) :
    ∃ kbar v, Setting61 U f U' f' β kbar v := by
  obtain ⟨kbar, hk0, hkf, hbelow, -⟩ := exists_kbar h
  obtain ⟨v, hv, -⟩ := ex_5_1ab (growthHyp_kbar h hk0 hkf hbelow)
  exact ⟨kbar, v, ⟨h, hk0, hkf, hbelow, hv⟩⟩

end GrowthCertaintyDD

end StokeyLucasPrescott.EquilibriumApplications
