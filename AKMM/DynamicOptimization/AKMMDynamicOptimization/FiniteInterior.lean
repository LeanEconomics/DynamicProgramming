/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.FiniteHorizon
import AKMMDynamicOptimization.TwoPeriod

/-!
# Interior capital in the finite-horizon NGM

AKMM, §4.2.3, p. 102: "Given the Inada conditions, in particular `lim_{k→0} f'(k) = ∞` and
`lim_{c→0} u'(c) = ∞`, it is optimal to set `k_{t+1} > 0` for all `t < T`."

* `ngm_objective_update`: changing `k_{t+1}` alone changes the objective of (P3) only through the
  periods `t` and `t + 1`.
* `ngm_finite_interior`: under the Inada conditions every maximizer of (P3) from `k₀ > 0` has
  `k_{t+1} > 0` for `t < T`. If `k_{t+1} = 0` at the first such date, then `c_{t+1} = 0`, and
  saving a little, `ε`, more at `t` gains `β^{t+1}[u(h(ε)) − u(0)] ≥ β^{t+1}εu'(h(ε))` while losing
  at most `βᵗεu'(c_t/2)`; for small `ε` the gain wins since `u'(h(ε)) → ∞`.
-/

namespace AKMM.DynamicOptimization

open Filter Topology StokeyLucasPrescott.DeterministicDynamics

/-- Changing `k_{t+1}` to `y` changes the (P3) objective by
`βᵗ[u(h(k_t) − y) − u(h(k_t) − k_{t+1})] + β^{t+1}[u(h(y) − k_{t+2}) − u(h(k_{t+1}) − k_{t+2})]`. -/
theorem ngm_objective_update {u h : ℝ → ℝ} {β : ℝ} {T t : ℕ} (ht : t < T) (ks : ℕ → ℝ) (y : ℝ) :
    ngmObjective u h β (Function.update ks (t + 1) y) T = ngmObjective u h β ks T +
      (β ^ t * u (h (ks t) - y) + β ^ (t + 1) * u (h y - ks (t + 2)) -
        (β ^ t * u (h (ks t) - ks (t + 1)) + β ^ (t + 1) * u (h (ks (t + 1)) - ks (t + 2)))) := by
  simp only [ngmObjective, objective]
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_add_of_mem t (t + 1) (Finset.mem_range.2 (by omega))
    (Finset.mem_range.2 (by omega)) (by omega)]
  · rw [Function.update_of_ne (show t ≠ t + 1 by omega), Function.update_self,
      Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega)]
    ring
  · intro c _ hc
    rw [Function.update_of_ne (show c ≠ t + 1 from hc.2),
      Function.update_of_ne (show c + 1 ≠ t + 1 by omega), sub_self]

/-- **AKMM, p. 102: under the Inada conditions capital is positive before `T`.** Let
`h(k) = f(k) + (1 − δ)k` with `δ ≤ 1`; `f(0) = 0`, `f` concave and strictly increasing on
`[0, ∞)`, continuous at `0` from the right, with derivative `f'` on `(0, ∞)` and
`f'(k) → ∞` as `k → 0⁺`; `u` concave on `[0, ∞)` with derivative `u' > 0` on `(0, ∞)` and
`u'(c) → ∞` as `c → 0⁺`; `β > 0`. Then every maximizer of (P3) from `k₀ > 0` has
`k_{t+1} > 0` for all `t < T`. -/
theorem ngm_finite_interior {u u' f f' : ℝ → ℝ} {β δ : ℝ} (hβ : 0 < β) (hδ1 : δ ≤ 1)
    (hu : ConcaveOn ℝ (Set.Ici 0) u) (hdu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu'pos : ∀ c, 0 < c → 0 < u' c) (hinada : Tendsto u' (𝓝[>] 0) atTop) (hf0 : f 0 = 0)
    (hfc : ConcaveOn ℝ (Set.Ici 0) f) (hfmono : StrictMonoOn f (Set.Ici 0))
    (hfcont : ContinuousWithinAt f (Set.Ioi 0) 0) (hdf : ∀ k, 0 < k → HasDerivAt f (f' k) k)
    (hf'0 : Tendsto f' (𝓝[>] 0) atTop) {k0 : ℝ} (hk0 : 0 < k0) {T : ℕ} {ks : ℕ → ℝ}
    (hks : NGMFeasible (fun k => f k + (1 - δ) * k) k0 T ks)
    (hmax : ∀ k, NGMFeasible (fun k => f k + (1 - δ) * k) k0 T k →
      ngmObjective u (fun k => f k + (1 - δ) * k) β k T ≤
        ngmObjective u (fun k => f k + (1 - δ) * k) β ks T) :
    ∀ t < T, 0 < ks (t + 1) := by
  set h : ℝ → ℝ := fun k => f k + (1 - δ) * k
  have hh0 : h 0 = 0 := by simp [h, hf0]
  have hhpos : ∀ k, 0 < k → 0 < h k := fun k hk => by
    have := hfmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hk.le) hk
    simp only [h]; rw [hf0] at this; nlinarith
  by_contra hcon
  push Not at hcon
  -- the first date with `k_{t+1} = 0`
  have hex : ∃ t, t < T ∧ ks (t + 1) = 0 := by
    obtain ⟨t, ht, hle⟩ := hcon
    exact ⟨t, ht, le_antisymm hle (hks.2 t ht.le).1⟩
  classical
  let t := Nat.find hex
  have ht : t < T := (Nat.find_spec hex).1
  have hkt1 : ks (t + 1) = 0 := (Nat.find_spec hex).2
  have hkt : 0 < ks t := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · rw [h0, hks.1]; exact hk0
    · obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have hmin := Nat.find_min hex (show s < t by omega)
      have hnn := (hks.2 s (by omega)).1
      rw [hs]
      by_contra hle
      push Not at hle
      exact hmin ⟨by omega, le_antisymm hle hnn⟩
  have hkt2 : ks (t + 2) = 0 := by
    have := hks.2 (t + 1) (by omega)
    simp only [Set.mem_Icc] at this
    rw [hkt1, hh0] at this
    exact le_antisymm this.2 this.1
  set ct := h (ks t)
  have hct : 0 < ct := hhpos _ hkt
  -- `h(ε) ≥ ε` for small `ε`, since `f(ε) ≥ εf'(ε)` and `f'(ε) → ∞`
  have hhge : ∀ᶠ ε in 𝓝[>] 0, ε ≤ h ε := by
    filter_upwards [hf'0.eventually (eventually_ge_atTop δ), self_mem_nhdsWithin] with ε hε hε0
    have htan := tangent_le hfc (Set.mem_Ici.2 (le_of_lt hε0)) (Set.mem_Ici.2 le_rfl)
      (hdf ε hε0)
    rw [hf0] at htan
    have hε0' : 0 < ε := hε0
    have := mul_le_mul_of_nonneg_left hε hε0'.le
    simp only [h]
    nlinarith
  -- `h(ε) → 0⁺`, so `u'(h(ε)) → ∞`
  have hhlim : Tendsto h (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun k => f k + (1 - δ) * k) (𝓝[>] 0) (𝓝 (f 0 + (1 - δ) * 0)) :=
        hfcont.tendsto.add ((continuous_const.mul continuous_id).continuousWithinAt.tendsto)
      simpa [hf0] using this
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hhpos ε hε
  have hbig := (hinada.comp hhlim).eventually (eventually_gt_atTop (u' (ct / 2) / β))
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ct / 2 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by linarith))
  obtain ⟨ε, ⟨⟨h1, h2⟩, h3⟩, hε0⟩ :=
    (((hhge.and hbig).and hsmall).and self_mem_nhdsWithin).exists
  have hε : 0 < ε := hε0
  simp only [Function.comp_apply] at h2
  -- the perturbed plan is feasible
  have hz : NGMFeasible h k0 T (Function.update ks (t + 1) ε) := by
    refine ⟨by rw [Function.update_of_ne (by omega)]; exact hks.1, fun s hs => ?_⟩
    by_cases hst : s = t
    · rw [hst, Function.update_self, Function.update_of_ne (show t ≠ t + 1 by omega)]
      exact ⟨hε.le, by linarith⟩
    by_cases hst' : s = t + 1
    · rw [hst', Function.update_self, Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega)]
      have : ks (t + 1 + 1) = 0 := hkt2
      rw [this]
      exact ⟨le_rfl, (hhpos ε hε).le⟩
    rw [Function.update_of_ne (show s + 1 ≠ t + 1 by omega), Function.update_of_ne hst']
    exact hks.2 s hs
  have hcmp := hmax _ hz
  rw [ngm_objective_update ht, hkt1, hkt2, hh0, sub_zero, sub_zero, sub_zero] at hcmp
  -- the two tangent bounds
  have hcte : 0 < ct - ε := by linarith
  have ta := tangent_le hu (Set.mem_Ici.2 hcte.le) (Set.mem_Ici.2 hct.le) (hdu _ hcte)
  have tb := tangent_le hu (Set.mem_Ici.2 (hhpos ε hε).le) (Set.mem_Ici.2 le_rfl)
    (hdu _ (hhpos ε hε))
  have hdec : u' (ct - ε) ≤ u' (ct / 2) :=
    deriv_le_of_concave hu (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 hcte.le)
      (by linarith) (hdu _ (by linarith)) (hdu _ hcte)
  have hpos2 := hu'pos (h ε) (hhpos ε hε)
  have hbt : 0 < β ^ t := pow_pos hβ t
  -- gain `≥ βᵗε[βu'(h(ε)) − u'(c_t/2)] > 0`
  have hgain : 0 < β * (h ε * u' (h ε)) - ε * u' (ct / 2) := by
    have : u' (ct / 2) < β * u' (h ε) := by
      have := (div_lt_iff₀ hβ).1 h2; linarith
    have a := mul_lt_mul_of_pos_left this hε
    have b := mul_le_mul_of_nonneg_right h1 (mul_pos hβ hpos2).le
    nlinarith
  have hloss : u ct - u (ct - ε) ≤ ε * u' (ct / 2) := by
    have : u ct ≤ u (ct - ε) + u' (ct - ε) * ε := by
      have := ta; rw [show ct - (ct - ε) = ε by ring] at this; exact this
    nlinarith
  have hwin : β * (h ε * u' (h ε)) ≤ β * (u (h ε) - u 0) := by
    have : h ε * u' (h ε) ≤ u (h ε) - u 0 := by linarith
    exact mul_le_mul_of_nonneg_left this hβ.le
  rw [pow_succ] at hcmp
  nlinarith [mul_pos hbt hgain]

end AKMM.DynamicOptimization
