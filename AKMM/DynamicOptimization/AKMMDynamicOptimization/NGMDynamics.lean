/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.InfiniteNGM
import AKMMDynamicOptimization.TwoPeriod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Dynamics in the optimizing neoclassical growth model

AKMM, §4.4.6, pp. 123–127. `h(k) = f(k) + (1 − δ)k` are total resources, `c = h(k) − g(k)`.

* The maximum sustainable capital `k^u`: the only positive solution of `h(k) = k`, and
  `k ≤ k^u ⇒ h(k) ≤ k^u` (`ngm_max_capital`).
* (4.26)–(4.27): the functional Euler equation of the NGM (`eq_4_26`) and its steady state
  `1 = β(f'(k̄) + 1 − δ)` (`eq_4_27`).
* (4.28): concavity of `V` with the envelope and first-order conditions gives
  `u'(c)[f'(k) + 1 − δ − 1/β][k − g(k)] ≤ 0` (`eq_4_28`); with `c = f(k) + (1 − δ)k − g(k)`, not
  `f(k) − g(k)` as printed. With `V` strictly concave, `g(k) < k` above `k̄` and `g(k) > k` below
  (`ngm_policy_direction`), and then every path converges monotonically to `k̄`
  (`ngm_global_convergence`). For `δ = 1` this is unconditional (`ngm_global_convergence_full`,
  SLP Proposition 6.1).
* (4.29): differentiating (4.26) at `k̄` gives `u''[1 − βa₁] = u''[a₁ − βa₁²] + β²u'f''a₁` for
  `a₁ = g'(k̄)` (`eq_4_29`), i.e. `βa₁² − (1 + β + Θ)a₁ + 1 = 0`, `Θ = β²u'f''/u''`
  (`eq_4_29_quadratic`).
* (4.30): the root `a₁ = (1 + β + Θ − √((1 + β + Θ)² − 4β))/(2β)` (`slopeRoot`): it solves the
  quadratic (`slopeRoot_isRoot`), lies in `(0, 1)` with the other root above `1` for `Θ > 0`
  (`slopeRoot_mem`), equals `1` at `Θ = 0` (`slopeRoot_zero`), is decreasing in `Θ`
  (`slopeRoot_strictAnti`), tends to `0` as `Θ → ∞` (`slopeRoot_tendsto_zero`) and to `1` as
  `Θ → 0` (`slopeRoot_tendsto_one`).
* Calibration: with CRRA utility `Θ = −β²f''(k̄)(f(k̄) − δk̄)/σ` (`theta_crra`), positive and
  decreasing in `σ` (`theta_crra_strictAnti`); with `f(k) = k^α` the book's closed form
  (`theta_cobbDouglas`), decreasing in `α` (`theta_cobbDouglas_strictAnti_alpha`) and increasing
  in `δ` (`theta_cobbDouglas_strictMono_delta`).
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real BoundedContinuousFunction

/-- **AKMM, pp. 123–124: the maximum sustainable capital stock.** Let `f(0) = 0`, `f` strictly
concave on `[0, ∞)`, continuous on `(0, ∞)`, with `f(k)/k → ∞` as `k → 0⁺` and `f(k)/k → 0` as
`k → ∞`, and `0 < δ`. There is a unique `k^u > 0` with `f(k^u) + (1 − δ)k^u = k^u`; the solutions of
`h(k) = k` on `[0, ∞)` are `0` and `k^u`; and if `h` is nondecreasing, `0 ≤ k ≤ k^u` implies
`h(k) ≤ k^u`. -/
theorem ngm_max_capital {f : ℝ → ℝ} (hf0 : f 0 = 0) (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hcont : ContinuousOn f (Set.Ioi 0)) (h0 : Tendsto (fun k => f k / k) (𝓝[>] 0) atTop)
    (htop : Tendsto (fun k => f k / k) atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ku, 0 < ku ∧ f ku + (1 - δ) * ku = ku ∧
      (∀ k, 0 ≤ k → (f k + (1 - δ) * k = k ↔ k = 0 ∨ k = ku)) ∧
      (MonotoneOn (fun k => f k + (1 - δ) * k) (Set.Ici 0) →
        ∀ k, 0 ≤ k → k ≤ ku → f k + (1 - δ) * k ≤ ku) := by
  -- the average product `f(k)/k` is strictly decreasing
  have hanti : StrictAntiOn (fun k => f k / k) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := hx
    have hy0 : 0 < y := hy
    have ht : 0 < x / y := div_pos hx0 hy0
    have ht1 : x / y < 1 := (div_lt_one hy0).2 hxy
    have := hconc.2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy0.le) hy0.ne
      (by linarith : 0 < 1 - x / y)
      ht (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, hf0] at this
    rw [div_mul_cancel₀ x hy0.ne'] at this
    simp only
    rw [div_lt_div_iff₀ hy0 hx0]
    have := mul_lt_mul_of_pos_right this hy0
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hy0.ne'] at this
    linarith
  have hfix : ∀ k, 0 < k → (f k + (1 - δ) * k = k ↔ f k / k = δ) := fun k hk => by
    rw [div_eq_iff hk.ne']; constructor <;> intro h <;> linarith
  obtain ⟨a, ha, ha0⟩ := ((h0.eventually (eventually_gt_atTop δ)).and
    self_mem_nhdsWithin).exists
  obtain ⟨b, hb, hab⟩ := ((htop.eventually (gt_mem_nhds hδ)).and
    (eventually_ge_atTop a)).exists
  have ha0' : 0 < a := ha0
  have hcont' : ContinuousOn (fun k => f k / k) (Set.Icc a b) :=
    ((hcont.mono fun x hx => lt_of_lt_of_le ha0' hx.1).div continuousOn_id fun x hx =>
      (lt_of_lt_of_le ha0' hx.1).ne')
  obtain ⟨ku, hku, hfku⟩ := intermediate_value_Icc' hab hcont' ⟨hb.le, ha.le⟩
  have hku0 : 0 < ku := lt_of_lt_of_le ha0' hku.1
  have hfix_ku : f ku + (1 - δ) * ku = ku := (hfix ku hku0).2 hfku
  refine ⟨ku, hku0, hfix_ku, fun k hk => ⟨fun h => ?_, ?_⟩, fun hmono k hk hkk => ?_⟩
  · rcases eq_or_lt_of_le hk with rfl | hpos
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h1 := (hfix k hpos).1 h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := hanti hpos hku0 hlt; simp only at this; linarith
      · have := hanti hku0 hpos hlt; simp only at this; linarith
  · rintro (rfl | rfl)
    · simp [hf0]
    · exact hfix_ku
  · have := hmono (Set.mem_Ici.2 hk) (Set.mem_Ici.2 hku0.le) hkk
    simp only at this
    linarith

/-- **AKMM, (4.26), p. 124: the functional Euler equation of the NGM.** If the policy satisfies
the first-order condition `u'(h(k) − g(k)) = βV'(g(k))` and the envelope condition
`V'(k) = u'(h(k) − g(k))h'(k)` for all `k`, then
`u'(h(k) − g(k)) = βu'(h(g(k)) − g(g(k)))h'(g(k))`. -/
theorem eq_4_26 {u' h h' g V' : ℝ → ℝ} {β : ℝ}
    (hfoc : ∀ k, u' (h k - g k) = β * V' (g k))
    (henv : ∀ k, V' k = u' (h k - g k) * h' k) (k : ℝ) :
    u' (h k - g k) = β * u' (h (g k) - g (g k)) * h' (g k) := by
  rw [hfoc, henv]; ring

/-- **AKMM, (4.27), p. 124.** At a steady state `g(k̄) = k̄` with `u'(c̄) ≠ 0`, (4.26) gives
`1 = β(f'(k̄) + 1 − δ)`. -/
theorem eq_4_27 {u' h h' g : ℝ → ℝ} {β kbar : ℝ} (hss : g kbar = kbar)
    (h426 : u' (h kbar - g kbar) = β * u' (h (g kbar) - g (g kbar)) * h' (g kbar))
    (hu : u' (h kbar - kbar) ≠ 0) : 1 = β * h' kbar := by
  rw [hss, hss] at h426
  exact eq_4_16_of_euler hu h426

/-- **AKMM, (4.28), p. 124, corrected.** If `V` is concave on a convex set `S` containing `k` and
`g(k)`, differentiable there, and the envelope condition `V'(k) = u'(c)h'(k)` and the first-order
condition `V'(g(k)) = u'(c)/β` hold with `c = h(k) − g(k)` (the book writes `f(k) − g(k)`,
dropping the undepreciated capital), then `u'(c)[h'(k) − 1/β][k − g(k)] ≤ 0`. -/
theorem eq_4_28 {V : ℝ → ℝ} {S : Set ℝ} (hV : ConcaveOn ℝ S V) {k gk Vk Vgk du dh β : ℝ}
    (hk : k ∈ S) (hgk : gk ∈ S) (hdk : HasDerivAt V Vk k) (hdgk : HasDerivAt V Vgk gk)
    (henv : Vk = du * dh) (hfoc : Vgk = du / β) :
    du * (dh - 1 / β) * (k - gk) ≤ 0 := by
  have hmono : (Vk - Vgk) * (k - gk) ≤ 0 := by
    rcases le_total k gk with h | h
    · have := StokeyLucasPrescott.DeterministicDynamics.deriv_le_of_concave hV hk hgk h hdk hdgk
      nlinarith
    · have := StokeyLucasPrescott.DeterministicDynamics.deriv_le_of_concave hV hgk hk h hdgk hdk
      nlinarith
  rw [henv, hfoc] at hmono
  have : du * (dh - 1 / β) = du * dh - du / β := by ring
  rw [this]
  exact hmono

/-- **AKMM, p. 124: the direction of motion.** With `V` strictly concave (differentiable, with
the envelope and first-order conditions), `u'(c) > 0` and `h'` strictly decreasing with
`βh'(k̄) = 1`: if `k > k̄` then `g(k) < k`, and if `0 < k < k̄` then `g(k) > k`. -/
theorem ngm_policy_direction {V : ℝ → ℝ} {S : Set ℝ} (hV : StrictConcaveOn ℝ S V)
    {k gk Vk Vgk du dh dhbar β kbar : ℝ} (hβ : 0 < β) (hk : k ∈ S) (hgk : gk ∈ S)
    (hdk : HasDerivAt V Vk k) (hdgk : HasDerivAt V Vgk gk) (henv : Vk = du * dh)
    (hfoc : Vgk = du / β) (hdu : 0 < du) (hbar : β * dhbar = 1)
    (hanti : k < kbar → dhbar < dh) (hanti' : kbar < k → dh < dhbar) :
    (kbar < k → gk < k) ∧ (k < kbar → k < gk) := by
  have hstrict : gk ≠ k → (Vk - Vgk) * (k - gk) < 0 := by
    intro hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := StokeyLucasPrescott.DeterministicDynamics.deriv_lt_of_strictConcave hV hgk hk h
        hdgk hdk
      nlinarith
    · have := StokeyLucasPrescott.DeterministicDynamics.deriv_lt_of_strictConcave hV hk hgk h
        hdk hdgk
      nlinarith
  have hdb : dhbar = 1 / β := by field_simp; linarith
  have hfix : gk = k → dh = dhbar := by
    intro he
    have : Vk = Vgk := by rw [hdk.unique (he ▸ hdgk)]
    rw [henv, hfoc] at this
    rw [hdb]
    field_simp at this ⊢
    nlinarith
  constructor
  · intro hlt
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with he | hgt
    · exact absurd (hfix he.symm) (hanti' hlt).ne
    · have := hstrict hgt.ne'
      rw [henv, hfoc] at this
      have hd : dh < 1 / β := hdb ▸ hanti' hlt
      have : du * dh - du / β < 0 := by
        rw [show du / β = du * (1 / β) by ring]; nlinarith
      nlinarith
  · intro hlt
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hle with he | hlt'
    · exact absurd (hfix he) (hanti hlt).ne'
    · have := hstrict hlt'.ne
      rw [henv, hfoc] at this
      have hd : 1 / β < dh := hdb ▸ hanti hlt
      have : 0 < du * dh - du / β := by
        rw [show du / β = du * (1 / β) by ring]; nlinarith
      nlinarith

/-- **AKMM, p. 124: global monotone convergence.** If `g` maps `(0, ∞)` into itself, is
nondecreasing and continuous there, `g(k̄) = k̄`, `g(k) > k` on `(0, k̄)` and `g(k) < k` on
`(k̄, ∞)`, then from every `k₀ > 0` the path `k_{t+1} = g(k_t)` is monotone and converges to
`k̄`. -/
theorem ngm_global_convergence {g : ℝ → ℝ} {kbar : ℝ} (hkbar : 0 < kbar)
    (hpos : ∀ k, 0 < k → 0 < g k) (hmono : MonotoneOn g (Set.Ioi 0))
    (hcont : ContinuousOn g (Set.Ioi 0)) (hfix : g kbar = kbar)
    (hbelow : ∀ k, 0 < k → k < kbar → k < g k) (habove : ∀ k, kbar < k → g k < k)
    {k0 : ℝ} (hk0 : 0 < k0) :
    (Monotone (fun t => g^[t] k0) ∨ Antitone (fun t => g^[t] k0)) ∧
      Tendsto (fun t => g^[t] k0) atTop (𝓝 kbar) := by
  set x : ℕ → ℝ := fun t => g^[t] k0
  have hstep : ∀ t, x (t + 1) = g (x t) := fun t => Function.iterate_succ_apply' _ _ _
  have hxpos : ∀ t, 0 < x t := by
    intro t; induction t with
    | zero => exact hk0
    | succ t ih => rw [hstep]; exact hpos _ ih
  -- a fixed point in `(0, ∞)` is `k̄`
  have huniq : ∀ L, 0 < L → g L = L → L = kbar := by
    intro L hL hgL
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hbelow L hL h; linarith
    · have := habove L h; linarith
  have hlim : ∀ L, 0 < L → Tendsto x atTop (𝓝 L) → L = kbar := by
    intro L hL hx
    refine huniq L hL (tendsto_nhds_unique ?_ ((tendsto_add_atTop_iff_nat 1).2 hx))
    have := (hcont L hL).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall hxpos⟩)
    refine (this.congr fun t => ?_)
    simp [Function.comp_apply, hstep]
  rcases le_total k0 kbar with hle | hge
  · -- below: nondecreasing and bounded by `k̄`
    have hbd : ∀ t, x t ≤ kbar := by
      intro t; induction t with
      | zero => exact hle
      | succ t ih => rw [hstep, ← hfix]; exact hmono (hxpos t) hkbar ih
    have hm : Monotone x := monotone_nat_of_le_succ fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hbd t) with he | hlt
      · rw [he, hfix]
      · exact (hbelow _ (hxpos t) hlt).le
    have hx := tendsto_atTop_ciSup hm ⟨kbar, by rintro _ ⟨t, rfl⟩; exact hbd t⟩
    have hL : 0 < ⨆ t, x t := lt_of_lt_of_le hk0 (le_ciSup ⟨kbar, by
      rintro _ ⟨t, rfl⟩; exact hbd t⟩ 0)
    exact ⟨Or.inl hm, hlim _ hL hx ▸ hx⟩
  · -- above: nonincreasing and bounded below by `k̄`
    have hbd : ∀ t, kbar ≤ x t := by
      intro t; induction t with
      | zero => exact hge
      | succ t ih => rw [hstep, ← hfix]; exact hmono hkbar (hxpos t) ih
    have ha : Antitone x := antitone_nat_of_succ_le fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hbd t) with he | hlt
      · rw [← he, hfix]
      · exact (habove _ hlt).le
    have hx := tendsto_atTop_ciInf ha ⟨kbar, by rintro _ ⟨t, rfl⟩; exact hbd t⟩
    have hL : 0 < ⨅ t, x t := lt_of_lt_of_le hkbar (le_ciInf hbd)
    exact ⟨Or.inr ha, hlim _ hL hx ▸ hx⟩

/-- **AKMM, p. 124, for `δ = 1`: global convergence, unconditionally.** In SLP's §6.1 setting
(`f` total resources, strictly concave and increasing, Inada conditions, `f'(∞) = 0`), the
stationary points of the optimal policy on `[0, k̄]` are `0` and `k*`, where `βf'(k*) = 1`, and
from every `k₀ ∈ (0, k̄]` the path converges monotonically to `k*` (SLP Proposition 6.1). -/
theorem ngm_global_convergence_full {U f U' f' : ℝ → ℝ} {β kbar : ℝ}
    [Nonempty (Set.Icc (0 : ℝ) kbar)] {v : Set.Icc (0 : ℝ) kbar →ᵇ ℝ}
    (S : StokeyLucasPrescott.DeterministicDynamics.Setting61 U f U' f' β kbar v) {kstar : ℝ}
    (hks0 : 0 < kstar) (hks : f' kstar = 1 / β) :
    kstar < kbar ∧
      (∀ k ∈ Set.Icc 0 kbar,
        StokeyLucasPrescott.DeterministicDynamics.gpol U f β kbar v k = k ↔ k = 0 ∨ k = kstar) ∧
      ∀ k₀, 0 < k₀ → k₀ ≤ kbar →
        (Monotone (fun t => (StokeyLucasPrescott.DeterministicDynamics.gpol U f β kbar v)^[t] k₀) ∨
          Antitone (fun t => (StokeyLucasPrescott.DeterministicDynamics.gpol U f β kbar v)^[t]
            k₀)) ∧
        Tendsto (fun t => (StokeyLucasPrescott.DeterministicDynamics.gpol U f β kbar v)^[t] k₀)
          atTop (𝓝 kstar) :=
  StokeyLucasPrescott.DeterministicDynamics.prop_6_1 S hks0 hks

end AKMM.DynamicOptimization
