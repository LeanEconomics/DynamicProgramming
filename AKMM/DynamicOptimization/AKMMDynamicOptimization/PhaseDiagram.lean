/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.TwoPeriod
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The NGM in the phase diagram

AKMM, App. 4.A.4, pp. 831–835: the resource constraint (4.A.8)
`k_{t+1} − k_t = f(k_t) − δk_t − c_t` and the Euler equation (4.A.9)
`u'(c_t) = βu'(c_{t+1})(f'(k_{t+1}) + 1 − δ)`.

* (4.A.10)–(4.A.12): `k` rises, stays or falls as `c_t` is below, on or above
  `f(k_t) − δk_t` (`eq_4A_12`).
* (4.A.13): `c` rises iff `k_{t+1} < k̄` iff `c_t > f(k_t) − δk_t + (k_t − k̄)` (`eq_4A_13`).
* The golden rule `f'(k^G) = δ` maximizes `f(k) − δk` (`golden_rule`), and `k̄ < k^G`
  (`steady_below_golden`).
* The TVC along an Euler path:
  `βᵗu'(c_t)(f'(k_t) + 1 − δ)k_t = u'(c₀)k_t/∏_{s=1}^{t−1}(f'(k_s) + 1 − δ)`
  (`phase_tvc_identity`); the book's product starts at `s = 0`, which is off by the factor
  `f'(k₀) + 1 − δ` (`phase_tvc_printed_differs`).
* Paths below the saddle path, which eventually stay above `k̂ > k^G`, violate the TVC: the
  expression tends to `+∞` (`phase_below_saddle_violates_tvc`, with `phase_return_below_one`).
* A convergent path (the saddle path) satisfies the TVC (`phase_saddle_tvc`).
* A path whose capital tends to `0` while consumption stays above `c̲ > 0` eventually violates
  `k ≥ 0` (`phase_above_saddle_infeasible`).

The facts read off Figures .1–.3 (the shape of the loci, the saddle path, and the paths above
and below it) are proved in `SaddlePath` and `SaddlePathExistence`.
-/

namespace AKMM.DynamicOptimization

open Filter Topology StokeyLucasPrescott.DeterministicDynamics

/-- **AKMM, (4.A.10)–(4.A.12), p. 832.** Under (4.A.8), `k_{t+1} > k_t ⇔ c_t < f(k_t) − δk_t`,
`k_{t+1} < k_t ⇔ c_t > f(k_t) − δk_t`, and `k_{t+1} = k_t ⇔ c_t = f(k_t) − δk_t`. -/
theorem eq_4A_12 {f : ℝ → ℝ} {δ k k' c : ℝ} (h48 : k' - k = f k - δ * k - c) :
    (k < k' ↔ c < f k - δ * k) ∧ (k' < k ↔ f k - δ * k < c) ∧ (k' = k ↔ c = f k - δ * k) := by
  refine ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun h => by linarith,
    fun h => by linarith⟩, ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- **AKMM, (4.A.13), pp. 832–833.** Let `u' > 0` be strictly decreasing and `f'` strictly
decreasing on `(0, ∞)`, `1 = β(f'(k̄) + 1 − δ)` (4.A.11), `β > 0`, and let `(k, c) → (k', c')`
satisfy (4.A.8)–(4.A.9) with positive values. Then `c' > c ⇔ k' < k̄ ⇔
c > f(k) − δk + (k − k̄)`. -/
theorem eq_4A_13 {f f' u' : ℝ → ℝ} {β δ kbar k k' c c' : ℝ} (hβ : 0 < β)
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0))
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hkbar : 0 < kbar) (h411 : 1 = β * (f' kbar + 1 - δ))
    (hk' : 0 < k') (hc : 0 < c) (hc' : 0 < c') (h48 : k' - k = f k - δ * k - c)
    (h49 : u' c = β * u' c' * (f' k' + 1 - δ)) :
    (c < c' ↔ k' < kbar) ∧ (k' < kbar ↔ f k - δ * k + (k - kbar) < c) := by
  have hpos := hu'pos c' hc'
  refine ⟨?_, ⟨fun h => by linarith, fun h => by linarith⟩⟩
  have step : c < c' ↔ 1 < β * (f' k' + 1 - δ) := by
    constructor
    · intro h
      have := hu' (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hc') h
      rw [h49] at this
      nlinarith
    · intro h
      by_contra hle
      push Not at hle
      have : u' c ≤ u' c' := hu'.antitoneOn (Set.mem_Ioi.2 hc') (Set.mem_Ioi.2 hc) hle
      rw [h49] at this
      nlinarith
  rw [step]
  constructor
  · intro h
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with he | hlt
    · rw [← he] at h; linarith
    · have := hf' (Set.mem_Ioi.2 hkbar) (Set.mem_Ioi.2 hk') hlt
      nlinarith
  · intro h
    have := hf' (Set.mem_Ioi.2 hk') (Set.mem_Ioi.2 hkbar) h
    nlinarith

/-- **AKMM, p. 832: the golden rule.** If `f` is concave on `[0, ∞)` and `f'(k^G) = δ`, then
`k^G` maximizes steady-state consumption `f(k) − δk` over `k ≥ 0`. -/
theorem golden_rule {f : ℝ → ℝ} {δ kG : ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) (hkG : 0 ≤ kG)
    (hd : HasDerivAt f δ kG) {k : ℝ} (hk : 0 ≤ k) : f k - δ * k ≤ f kG - δ * kG := by
  have := tangent_le hf (Set.mem_Ici.2 hkG) (Set.mem_Ici.2 hk) hd
  linarith

/-- **AKMM, p. 834: `k̄ < k^G`.** With `f'` strictly decreasing, `f'(k^G) = δ` and
`f'(k̄) = δ + 1/β − 1 > δ` (`0 < β < 1`), the modified golden rule lies below the golden rule. -/
theorem steady_below_golden {f' : ℝ → ℝ} {β δ kbar kG : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hkbar : 0 < kbar) (hkG : 0 < kG)
    (hbar : f' kbar = δ + 1 / β - 1) (hG : f' kG = δ) : kbar < kG := by
  by_contra hle
  push Not at hle
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  rcases eq_or_lt_of_le hle with he | hlt
  · rw [← he] at hbar; linarith
  · have := hf' (Set.mem_Ioi.2 hkG) (Set.mem_Ioi.2 hkbar) hlt
    linarith

/-- **AKMM, p. 834: the TVC along an Euler path**, with `R_s = f'(k_s) + 1 − δ`: if
`u'(c_s) = βu'(c_{s+1})R_{s+1}` for all `s`, then
`β^{t+1}u'(c_{t+1})R_{t+1}k_{t+1} = u'(c₀)k_{t+1}/∏_{s=1}^{t} R_s`, for `R_s ≠ 0`. -/
theorem phase_tvc_identity {β : ℝ} {mu R k : ℕ → ℝ}
    (heuler : ∀ s, mu s = β * mu (s + 1) * R (s + 1)) (hR : ∀ s, R s ≠ 0) (t : ℕ) :
    β ^ (t + 1) * mu (t + 1) * R (t + 1) * k (t + 1) =
      mu 0 * k (t + 1) / ∏ s ∈ Finset.range t, R (s + 1) := by
  have hprod : ∀ t, β ^ t * mu t * ∏ s ∈ Finset.range t, R (s + 1) = mu 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.prod_range_succ, ← ih, heuler t, pow_succ]
      ring
  have hP : ∏ s ∈ Finset.range t, R (s + 1) ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => hR _
  rw [eq_div_iff hP, ← hprod (t + 1), Finset.prod_range_succ]
  ring

/-- **AKMM, p. 834, corrected.** The printed `u'(c₀)k_t/∏_{s=0}^{t−1}R_s` differs from the true
value by the factor `R₀`: at `t = 1` the true value is `u'(c₀)k₁` and the printed one
`u'(c₀)k₁/R₀`, which differ whenever `R₀ ≠ 1`, `u'(c₀) ≠ 0` and `k₁ ≠ 0`. -/
theorem phase_tvc_printed_differs {β : ℝ} {mu R k : ℕ → ℝ}
    (heuler : ∀ s, mu s = β * mu (s + 1) * R (s + 1)) (hR0 : R 0 ≠ 1) (hR0' : R 0 ≠ 0)
    (hmu : mu 0 ≠ 0) (hk : k 1 ≠ 0) :
    β ^ 1 * mu 1 * R 1 * k 1 = mu 0 * k 1 ∧
      β ^ 1 * mu 1 * R 1 * k 1 ≠ mu 0 * k 1 / ∏ s ∈ Finset.range 1, R s := by
  have h1 : β ^ 1 * mu 1 * R 1 * k 1 = mu 0 * k 1 := by rw [heuler 0]; ring
  refine ⟨h1, ?_⟩
  rw [h1, Finset.prod_range_one]
  intro h
  rw [eq_div_iff hR0'] at h
  have : mu 0 * k 1 * (R 0 - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h2 | h2
  · rcases mul_eq_zero.1 h2 with h3 | h3
    · exact hmu h3
    · exact hk h3
  · exact hR0 (by linarith)

/-- AKMM, p. 834: if `k_s ≥ k̂ > k^G` with `f'` strictly decreasing and `f'(k^G) = δ`, then
`R_s = f'(k_s) + 1 − δ ≤ f'(k̂) + 1 − δ < 1`. -/
theorem phase_return_below_one {f' : ℝ → ℝ} {δ kG khat k : ℝ}
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hkG : 0 < kG) (hG : f' kG = δ) (hlt : kG < khat)
    (hk : khat ≤ k) : f' k + 1 - δ ≤ f' khat + 1 - δ ∧ f' khat + 1 - δ < 1 := by
  have hk0 : 0 < khat := hkG.trans hlt
  refine ⟨?_, ?_⟩
  · have := hf'.antitoneOn (Set.mem_Ioi.2 hk0) (Set.mem_Ioi.2 (hk0.trans_le hk)) hk
    linarith
  · have := hf' (Set.mem_Ioi.2 hkG) (Set.mem_Ioi.2 hk0) hlt
    linarith

/-- **AKMM, p. 834: paths below the saddle path violate the TVC.** Along an Euler path with
`u'(c₀) > 0` and returns `R_s > 0`, if from some date `T` on `R_s ≤ ρ < 1` (`k_s` above some
`k̂ > k^G`, `phase_return_below_one`) and `k_s ≥ κ > 0`, then
`βᵗu'(c_t)(f'(k_t) + 1 − δ)k_t → +∞`. -/
theorem phase_below_saddle_violates_tvc {β ρ κ : ℝ} {mu R k : ℕ → ℝ} {T : ℕ}
    (heuler : ∀ s, mu s = β * mu (s + 1) * R (s + 1)) (hR : ∀ s, 0 < R s) (hmu : 0 < mu 0)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hRρ : ∀ s, T ≤ s → R s ≤ ρ) (hκ : 0 < κ)
    (hkκ : ∀ s, T ≤ s → κ ≤ k s) :
    Tendsto (fun t => β ^ (t + 1) * mu (t + 1) * R (t + 1) * k (t + 1)) atTop atTop := by
  set P : ℕ → ℝ := fun t => ∏ s ∈ Finset.range t, R (s + 1)
  have hP : ∀ t, 0 < P t := fun t => Finset.prod_pos fun s _ => hR _
  have hPbound : ∀ n, P (T + n) ≤ P T * ρ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : P (T + (n + 1)) = P (T + n) * R (T + n + 1) := Finset.prod_range_succ _ _
      rw [e, pow_succ, ← mul_assoc]
      exact mul_le_mul ih (hRρ _ (by omega)) (hR _).le (mul_pos (hP T) (pow_pos hρ0 n)).le
  have hgrow : Tendsto (fun n : ℕ => mu 0 * κ / (P T * ρ ^ n)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (ρ⁻¹) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv_iff₀.2 ⟨hρ0, hρ1⟩)
    have h2 := h1.const_mul_atTop (div_pos (mul_pos hmu hκ) (hP T))
    refine h2.congr fun n => ?_
    rw [inv_pow]
    field_simp
  have hshift : Tendsto (fun t => mu 0 * κ / (P T * ρ ^ (t - T))) atTop atTop :=
    hgrow.comp (tendsto_sub_atTop_nat T)
  refine tendsto_atTop_mono' _ ?_ hshift
  filter_upwards [eventually_ge_atTop T] with t ht
  rw [phase_tvc_identity heuler (fun s => (hR s).ne') t]
  obtain ⟨n, rfl⟩ : ∃ n, t = T + n := ⟨t - T, by omega⟩
  rw [show T + n - T = n by omega]
  have hb := hPbound n
  have hPpos := hP (T + n)
  have hk := hkκ (T + n + 1) (by omega)
  have hden : 0 < P T * ρ ^ n := mul_pos (hP T) (pow_pos hρ0 n)
  calc mu 0 * κ / (P T * ρ ^ n) ≤ mu 0 * κ / P (T + n) :=
        div_le_div_of_nonneg_left (mul_pos hmu hκ).le hPpos hb
    _ ≤ mu 0 * k (T + n + 1) / P (T + n) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk hmu.le) hPpos.le

/-- **AKMM, p. 834: the saddle path satisfies the TVC.** If `0 ≤ β < 1` and `k_t → k̄`,
`c_t → c̄`, with `u'` continuous at `c̄` and `f'` continuous at `k̄`, then
`βᵗu'(c_t)(f'(k_t) + 1 − δ)k_t → 0`. -/
theorem phase_saddle_tvc {u' f' : ℝ → ℝ} {β δ kbar cbar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {k c : ℕ → ℝ} (hk : Tendsto k atTop (𝓝 kbar)) (hc : Tendsto c atTop (𝓝 cbar))
    (hu' : ContinuousAt u' cbar) (hf' : ContinuousAt f' kbar) :
    Tendsto (fun t => β ^ t * (u' (c t) * (f' (k t) + 1 - δ) * k t)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t => u' (c t) * (f' (k t) + 1 - δ) * k t) atTop
      (𝓝 (u' cbar * (f' kbar + 1 - δ) * kbar)) :=
    (((hu'.tendsto.comp hc).mul (((hf'.tendsto.comp hk).add_const 1).sub_const δ)).mul hk)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul h1

/-- **AKMM, p. 834: paths above the saddle path become infeasible.** If `f(0) = 0` with `f`
continuous at `0`, `k_t → 0` and `c_t ≥ c̲ > 0`, then (4.A.8) eventually forces `k_{t+1} < 0`. -/
theorem phase_above_saddle_infeasible {f : ℝ → ℝ} {δ clow : ℝ} {k c : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : ContinuousAt f 0) (hclow : 0 < clow) (hc : ∀ t, clow ≤ c t)
    (hk : Tendsto k atTop (𝓝 0)) (h48 : ∀ t, k (t + 1) = f (k t) + (1 - δ) * k t - c t) :
    ∃ t, k (t + 1) < 0 := by
  have h1 : Tendsto (fun t => f (k t) + (1 - δ) * k t) atTop (𝓝 (f 0 + (1 - δ) * 0)) :=
    (hf.tendsto.comp hk).add (hk.const_mul _)
  rw [hf0, mul_zero, add_zero] at h1
  obtain ⟨t, ht⟩ := (h1.eventually (gt_mem_nhds hclow)).exists
  exact ⟨t, by rw [h48]; linarith [hc t]⟩

end AKMM.DynamicOptimization
