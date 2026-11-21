/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.GrowthRates
import Solow1956.Growth.GeneralSolowApplications

/-!
# The Solow model in continuous time

AKMM, §9.3.1 (pp. 251–253): (9.27)–(9.32), Figure 9.1 and the balanced growth path.

* (9.31): the growth rate of `k̃ = K/(AL)` is `K̇/K − Ȧ/A − L̇/L` (`eq_9_31`).
* With constant returns, (9.27)–(9.30) give `k̃̇/k̃ = (sF − δK)/K − γ − n`, `F(K, AL)/(AL) = f(k̃)`
  and (9.32) `k̃̇ = sf(k̃) − (δ + γ + n)k̃` (`solowContinuous_intensive`, `eq_9_32`), the latter
  by EconomicGrowth's `hasDerivAt_capitalPerEffectiveWorker`.
* Figure 9.1: a unique positive steady state `k̃̄`, `k̃̇ > 0` below it and `k̃̇ < 0` above it, and
  global monotone convergence from every `k̃(0) > 0`, for the economy's actual `k̃(t)`
  (`solowContinuous_phase_line`, `solowContinuous_convergence`), from EconomicGrowth's
  `general_solow` and `effective_labour_convergence` with `m = δ + γ + n`.
* The balanced growth path: `Y/L = f(k̃)A`; on the steady state `Y/L` grows at exactly `γ`, and
  along every path its growth rate tends to `γ` (`solowContinuous_income_per_capita_growth`).
-/

namespace AKMM.ContinuousTime

open Filter Topology Solow1956.Neoclassical

/-- AKMM, (9.31), p. 251: for positive differentiable `K, A, L`, the growth rate of
`k̃ = K/(AL)` is `K̇/K − Ȧ/A − L̇/L`. -/
theorem eq_9_31 {K A L : ℝ → ℝ} {K' A' L' t : ℝ} (hK : HasDerivAt K K' t)
    (hA : HasDerivAt A A' t) (hL : HasDerivAt L L' t) (hK0 : 0 < K t) (hA0 : 0 < A t)
    (hL0 : 0 < L t) :
    HasDerivAt (fun s => K s / (A s * L s))
      (K t / (A t * L t) * (K' / K t - A' / A t - L' / L t)) t := by
  have hAL : A t * L t ≠ 0 := (mul_pos hA0 hL0).ne'
  convert hK.div (hA.mul hL) hAL using 1
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- AKMM, p. 252: with constant returns `F(λK, λN) = λF(K, N)` and `f(k) = F(k, 1)`,
`F(K, AL)/(AL) = f(K/(AL))`; and from (9.27)–(9.30), (9.31) reads
`k̃̇/k̃ = (sF(K, AL) − δK)/K − γ − n = sf(k̃)/k̃ − (δ + γ + n)`. -/
theorem solowContinuous_intensive {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N) {K E s δ γ n : ℝ}
    (hK : 0 < K) (hE : 0 < E) :
    F K E / E = F (K / E) 1 ∧
      (s * F K E - δ * K) / K - γ - n = s * F (K / E) 1 / (K / E) - (δ + γ + n) := by
  have h1 : F K E = E * F (K / E) 1 := by
    have := hcrs E hE (K / E) 1
    rw [mul_div_cancel₀ _ hE.ne', mul_one] at this
    exact this
  refine ⟨by rw [h1]; field_simp, ?_⟩
  rw [h1]
  field_simp
  ring

/-- AKMM, (9.27)–(9.32), pp. 251–252: if `L̇ = nL`, `Ȧ = γA`, `K̇ = sF(K, AL) − δK` with
constant returns, then `k̃ = K/(AL)` satisfies (9.32): `k̃̇ = sf(k̃) − (δ + γ + n)k̃`. -/
theorem eq_9_32 {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N) {K A L : ℝ → ℝ}
    {s δ γ n t : ℝ} (hA0 : 0 < A t) (hL0 : 0 < L t)
    (h927 : HasDerivAt L (n * L t) t) (h928 : HasDerivAt A (γ * A t) t)
    (h929 : HasDerivAt K (s * F (K t) (A t * L t) - δ * K t) t) :
    HasDerivAt (fun u => K u / (A u * L u))
      (s * F (K t / (A t * L t)) 1 - (δ + γ + n) * (K t / (A t * L t))) t := by
  have hE : 0 < A t * L t := mul_pos hA0 hL0
  have hEd : HasDerivAt (fun u => A u * L u) ((n + γ) * (A t * L t)) t := by
    convert h928.mul h927 using 1
    ring
  have hY : F (K t) (A t * L t) = A t * L t * F (K t / (A t * L t)) 1 := by
    have := hcrs (A t * L t) hE (K t / (A t * L t)) 1
    rw [mul_div_cancel₀ _ hE.ne', mul_one] at this
    exact this
  have h := Solow1956.SolowSwan.hasDerivAt_capitalPerEffectiveWorker (f := fun k => F k 1)
    (E := fun u => A u * L u) hE h929 hEd hY
  convert h using 1
  ring

/-- AKMM, Figure 9.1, pp. 252–253: for a neoclassical intensive technology, `s > 0` and
`δ + γ + n > 0`, (9.32) has a unique positive steady state `k̃̄`; the right side of (9.32) is
positive below it and negative above it; and from every `k̃(0) > 0` the solution exists, is
unique, stays positive and converges monotonically to `k̃̄`. -/
theorem solowContinuous_phase_line {f : ℝ → ℝ} (h : Technology f) {s δ γ n k₀ : ℝ}
    (hs : 0 < s) (hm : 0 < δ + γ + n) (hk₀ : 0 < k₀) :
    ∃ kbar : ℝ, 0 < kbar ∧ s * f kbar - (δ + γ + n) * kbar = 0 ∧
      (∀ k, 0 < k → s * f k - (δ + γ + n) * k = 0 → k = kbar) ∧
      (∀ k, 0 < k → k < kbar → 0 < s * f k - (δ + γ + n) * k) ∧
      (∀ k, kbar < k → s * f k - (δ + γ + n) * k < 0) ∧
      ∃ k : ℝ → ℝ, k 0 = k₀ ∧
        (∀ t, 0 ≤ t → 0 < k t ∧ HasDerivAt k (s * f (k t) - (δ + γ + n) * k t) t) ∧
        (k₀ < kbar → StrictMonoOn k (Set.Ici 0)) ∧ (kbar < k₀ → StrictAntiOn k (Set.Ici 0)) ∧
        Tendsto k atTop (𝓝 kbar) ∧
        (∀ l : ℝ → ℝ, l 0 = k₀ → (∀ t, 0 ≤ t → 0 ≤ l t) →
          (∀ t, 0 ≤ t → HasDerivAt l (s * f (l t) - (δ + γ + n) * l t) t) →
            Set.EqOn l k (Set.Ici 0)) := by
  obtain ⟨ks, hks, he, hu, k, h0, hk, hlow, hhigh, _, _, hlim, huniq⟩ :=
    general_solow h hs hm hk₀
  refine ⟨ks, hks, he, hu, fun x hx hlt => rate_pos_below h hs hx hlt he,
    fun x hlt => rate_neg_above h hs hks hlt he, k, h0, hk, fun hlt => (hlow hlt).1,
    fun hlt => (hhigh hlt).1, hlim, huniq⟩

/-- AKMM, pp. 252–253: convergence of the economy itself. If the aggregates satisfy
(9.27)–(9.30) with constant returns, `K(0) > 0`, `K ≥ 0`, and the intensive form `f(k) = F(k, 1)`
is neoclassical, then capital per effective worker `K/(AL)` converges to the steady state of
(9.32), whatever its initial value. -/
theorem solowContinuous_convergence {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N)
    (h : Technology fun k => F k 1) {K A L : ℝ → ℝ} {s δ γ n : ℝ} (hs : 0 < s)
    (hm : 0 < n + γ + δ) (hK0 : 0 < K 0) (hK : ∀ t, 0 ≤ t → 0 ≤ K t)
    (hA0 : ∀ t, 0 ≤ t → 0 < A t) (hL0 : ∀ t, 0 ≤ t → 0 < L t)
    (h927 : ∀ t, 0 ≤ t → HasDerivAt L (n * L t) t) (h928 : ∀ t, 0 ≤ t → HasDerivAt A (γ * A t) t)
    (h929 : ∀ t, 0 ≤ t → HasDerivAt K (s * F (K t) (A t * L t) - δ * K t) t) :
    Tendsto (fun t => K t / (A t * L t)) atTop (𝓝 (steadyCapital h s (n + γ + δ))) := by
  refine effective_labour_convergence h (E := fun t => A t * L t)
    (Y := fun t => F (K t) (A t * L t)) hs hm hK0 hK (fun t ht => mul_pos (hA0 t ht) (hL0 t ht))
    h929 (fun t ht => by convert (h928 t ht).mul (h927 t ht) using 1; ring) (fun t ht => ?_)
  have hE := mul_pos (hA0 t ht) (hL0 t ht)
  have := hcrs (A t * L t) hE (K t / (A t * L t)) 1
  rw [mul_div_cancel₀ _ hE.ne', mul_one] at this
  exact this

/-- AKMM, p. 253: income per capita is `Y/L = F(K, AL)/L = f(k̃)A`. On the steady state
(`k̃` constant) it grows at exactly the rate `γ` of technology; along every path converging to
the steady state `k̃̄ > 0` with `k̃̇ = sf(k̃) − (δ + γ + n)k̃`, its growth rate
`γ + f'(k̃)k̃̇/f(k̃)` tends to `γ`. -/
theorem solowContinuous_income_per_capita_growth {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N)
    (h : Technology fun k => F k 1) {K A L k : ℝ → ℝ} {s δ γ n kbar : ℝ}
    (hA0 : ∀ t, 0 < A t) (hL0 : ∀ t, 0 < L t) (hk : ∀ t, 0 < k t) (hkbar : 0 < kbar)
    (hss : s * F kbar 1 - (δ + γ + n) * kbar = 0)
    (hA : ∀ t, HasDerivAt A (γ * A t) t)
    (hkd : ∀ t, HasDerivAt k (s * F (k t) 1 - (δ + γ + n) * k t) t)
    (hlim : Tendsto k atTop (𝓝 kbar)) :
    (∀ t, 0 < K t → K t / (A t * L t) = k t → F (K t) (A t * L t) / L t = F (k t) 1 * A t) ∧
      (∀ t, HasDerivAt (fun u => Real.log (F (k u) 1 * A u))
        (deriv (fun x => F x 1) (k t) * (s * F (k t) 1 - (δ + γ + n) * k t) / F (k t) 1 + γ) t) ∧
      (∀ t, HasDerivAt (fun u => Real.log (F kbar 1 * A u)) γ t) ∧
      Tendsto (fun t => deriv (fun x => F x 1) (k t) * (s * F (k t) 1 - (δ + γ + n) * k t) /
        F (k t) 1 + γ) atTop (𝓝 γ) := by
  refine ⟨fun t hK hkt => ?_, fun t => ?_, fun t => ?_, ?_⟩
  · have hE := mul_pos (hA0 t) (hL0 t)
    have h1 := hcrs (A t * L t) hE (K t / (A t * L t)) 1
    rw [mul_div_cancel₀ _ hE.ne', mul_one] at h1
    rw [h1, ← hkt]
    field_simp [(hL0 t).ne']
  · have hfk := ((h.differentiable (k t) (hk t)).hasDerivAt).comp t (hkd t)
    have hy := (hfk.mul (hA t)).log (mul_pos (h.output_pos (hk t)) (hA0 t)).ne'
    convert hy using 1
    · rfl
    · have := (h.output_pos (hk t)).ne'
      have := (hA0 t).ne'
      simp only [Function.comp, Pi.mul_apply]
      field_simp
  · have hy := ((hA t).const_mul (F kbar 1)).log (mul_pos (h.output_pos hkbar) (hA0 t)).ne'
    convert hy using 1
    have := (h.output_pos hkbar).ne'
    have := (hA0 t).ne'
    field_simp
  · have hev : ∀ᶠ t in atTop, k t ∈ Set.Ioi 0 := Eventually.of_forall fun t => hk t
    have hk' : Tendsto k atTop (𝓝[Set.Ioi 0] kbar) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, hev⟩
    have hd := ((h.derivative_continuous kbar hkbar).tendsto).comp hk'
    have hf := ((h.differentiable kbar hkbar).continuousAt.tendsto).comp hlim
    have hr : Tendsto (fun t => s * F (k t) 1 - (δ + γ + n) * k t) atTop
        (𝓝 (s * F kbar 1 - (δ + γ + n) * kbar)) :=
      (hf.const_mul s).sub (hlim.const_mul _)
    rw [hss] at hr
    have := ((hd.mul hr).div hf (h.output_pos hkbar).ne').add_const γ
    simpa using this

end AKMM.ContinuousTime
