/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.GrowthStability
import DeterministicDynamics.EulerScalar

/-!
# The slope of the optimal policy at the steady state

SLP §6.4, pp. 154–155. In the one-sector growth model of §6.1 (`Setting61`), let `U′` and `f′` be
differentiable at the steady state, `U″(c*) = U₂ < 0` at `c* = f(k*) − k*` and `f″(k*) = f₂ < 0`,
and put `c = βf₂U′(c*)/U₂ > 0` (`growthC`). The book linearizes the Euler equation
`U′[f(k) − g(k)] = βU′[f(g(k)) − g²(k)]f′(g(k))` at `k*` and states that the optimal policy `g`
has slope `λ₁` at `k*`, the root in `(0, 1)` of `λ² − (1 + β⁻¹ + c)λ + β⁻¹` (`growth_roots`).

* `euler_linearization`: the Euler equation, as a function of `(k_t, k_{t+1}, k_{t+2})`, is
  differentiable at `(k*, k*, k*)`; near the steady state
  `k_{t+2} − k* = (1 + β⁻¹ + c)(k_{t+1} − k*) − (k_t − k*)/β + o(|k_t − k*|)` along any triple
  with `|k_{t+1} − k*|, |k_{t+2} − k*| ≤ |k_t − k*|`.
* `hasDerivAt_of_slope_contraction`: if `g` does not move points away from `k*`, and the slope
  `s(k) = (g(k) − g(k*))/(k − k*)` satisfies
  `|s(k) − l| ≤ q|s(g(k)) − l| + τ` near `k*` for every `τ > 0`, with `q < 1`, then `g′(k*) = l`.
* `Setting61.gpol_between`: `g(k)` lies between `k` and `k*` on `(0, k̄]` (from `prop_6_1`).
* `Setting61.hasDerivAt_gpol_of_root`: if `l ≥ 0` is a root of `λ² − (1 + β⁻¹ + c)λ + β⁻¹`
  with `l < β⁻¹ + c`, then `g′(k*) = l`.
* **The growth example** (`growth_policy_deriv`): the optimal policy is differentiable at `k*`
  with `g′(k*) = λ₁`, the root of `λ² − (1 + β⁻¹ + c)λ + β⁻¹` in `(0, 1)`; the other root
  exceeds `1/β`.

Differentiability of `g` is not assumed, and neither the stable manifold theorem nor the
implicit function theorem is used. Since `g(k)` lies between `k` and `k*`, the slope `s(k)` lies
in `[0, 1]`. Writing `s′ = s(g(k))`, the linearized Euler equation reads
`(1 + β⁻¹ + c − s′)s = β⁻¹ + o(1)`, and `λ₁` solves the same equation exactly. Subtracting,
`(1 + β⁻¹ + c − s′)(s − λ₁) = λ₁(s′ − λ₁) + o(1)`, and since `1 + β⁻¹ + c − s′ ≥ β⁻¹ + c > λ₁`
this is a contraction from `s(g(k))` back to `s(k)`. Iterating along the orbit, which converges to
`k*`, squeezes `s(k)` to `λ₁`. `U` and `f` need second derivatives only at the steady state.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Set Filter Topology BoundedContinuousFunction

/-- The book's `c = βf″(k*)U′(c*)/U″(c*)` (p. 155), as a function of `β`, `U′(c*)`, `U″(c*)` and
`f″(k*)`. -/
noncomputable def growthC (β U1 U2 f2 : ℝ) : ℝ := β * f2 * U1 / U2

/-- **The linearized Euler equation** (p. 155). Let `U′` have derivative `U₂` at `c* = f(k*) − k*`
and `f′` derivative `f₂` at `k*`, with `f′(k*) = β⁻¹` and `U₂ ≠ 0`. For every `τ > 0` there is
`δ > 0` such that whenever `|x − k*| < δ`, `|y − k*|, |z − k*| ≤ |x − k*|` and the Euler equation
`U′(f(x) − y) = βU′(f(y) − z)f′(y)` holds,
`|(z − k*) − (1 + β⁻¹ + c)(y − k*) + (x − k*)/β| ≤ τ|x − k*|`, with `c = βf₂U′(c*)/U₂`. -/
theorem euler_linearization {U' f f' : ℝ → ℝ} {β ks U2 f2 : ℝ} (hβ : 0 < β)
    (hU2 : HasDerivAt U' U2 (f ks - ks)) (hU2ne : U2 ≠ 0) (hf : HasDerivAt f β⁻¹ ks)
    (hf' : HasDerivAt f' f2 ks) (hks : f' ks = β⁻¹) :
    ∀ τ > 0, ∃ δ > 0, ∀ x y z : ℝ, |x - ks| < δ → |y - ks| ≤ |x - ks| → |z - ks| ≤ |x - ks| →
      U' (f x - y) = β * (U' (f y - z) * f' y) →
      |(z - ks) - (1 + β⁻¹ + growthC β (U' (f ks - ks)) U2 f2) * (y - ks) + (x - ks) / β| ≤
        τ * |x - ks| := by
  intro τ hτ
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := ((ks, ks, ks) : ℝ × ℝ × ℝ)))
  have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (p := ((ks, ks, ks) : ℝ × ℝ × ℝ))).fst
  have h3 := (hasFDerivAt_snd (𝕜 := ℝ) (p := ((ks, ks, ks) : ℝ × ℝ × ℝ))).snd
  have hA := hU2.comp_hasFDerivAt ((ks, ks, ks) : ℝ × ℝ × ℝ) ((hf.comp_hasFDerivAt _ h1).sub h2)
  have hB := hU2.comp_hasFDerivAt ((ks, ks, ks) : ℝ × ℝ × ℝ) ((hf.comp_hasFDerivAt _ h2).sub h3)
  have hC := hf'.comp_hasFDerivAt ((ks, ks, ks) : ℝ × ℝ × ℝ) h2
  have hG := hA.sub ((hB.mul hC).const_mul β)
  have hU2p : 0 < |U2| := abs_pos.2 hU2ne
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (hG.isLittleO.def (mul_pos hτ hU2p))
  refine ⟨δ, hδ, fun x y z hx hy hz heul => ?_⟩
  have hd : dist ((x, y, z) : ℝ × ℝ × ℝ) (ks, ks, ks) < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt hx (max_lt (hy.trans_lt hx) (hz.trans_lt hx))
  have hn : ‖((x, y, z) : ℝ × ℝ × ℝ) - (ks, ks, ks)‖ ≤ |x - ks| := by
    rw [Prod.norm_def, Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    exact max_le le_rfl (max_le hy hz)
  have hb := (hball hd).trans (mul_le_mul_of_nonneg_left hn (mul_pos hτ hU2p).le)
  simp only [Function.comp_def, Pi.sub_apply, Pi.mul_apply, _root_.sub_apply,
    _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul, Real.norm_eq_abs, heul, hks] at hb
  have e : β * (U' (f y - z) * f' y) - β * (U' (f y - z) * f' y) -
      (U' (f ks - ks) - β * (U' (f ks - ks) * β⁻¹)) -
      (U2 * (β⁻¹ * (x - ks) - (y - ks)) -
        β * (U' (f ks - ks) * (f2 * (y - ks)) + β⁻¹ * (U2 * (β⁻¹ * (y - ks) - (z - ks))))) =
      -(U2 * ((z - ks) - (1 + β⁻¹ + growthC β (U' (f ks - ks)) U2 f2) * (y - ks) +
        (x - ks) / β)) := by
    simp only [growthC]
    field_simp
    ring
  rw [e, abs_neg, abs_mul] at hb
  exact le_of_mul_le_mul_left (by linarith) hU2p

/-- **Slopes squeezed by a contraction.** On `|k − k*| < r` let `g` not move points away from
`k*`, nor onto `k*` from elsewhere, with the slope `s(k) = (g(k) − g(k*))/(k − k*)` within `B`
of `l`. If for every `τ > 0`, near `k*`, `|s(k) − l| ≤ q|s(g(k)) − l| + τ` with
`0 ≤ q < 1`, then `g′(k*) = l`. -/
theorem hasDerivAt_of_slope_contraction {g : ℝ → ℝ} {ks r l q B : ℝ} (hr : 0 < r)
    (hlip : ∀ k, |k - ks| < r → |g k - ks| ≤ |k - ks|)
    (hne : ∀ k, |k - ks| < r → k ≠ ks → g k ≠ ks)
    (hB : ∀ k, |k - ks| < r → k ≠ ks → |slope g ks k - l| ≤ B) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (key : ∀ τ > 0, ∃ δ > 0, ∀ k, |k - ks| < δ → k ≠ ks →
      |slope g ks k - l| ≤ q * |slope g ks (g k) - l| + τ) :
    HasDerivAt g l ks := by
  have hsmall : ∀ η > 0, ∃ δ > 0, ∀ k, |k - ks| < δ → k ≠ ks → |slope g ks k - l| ≤ η := by
    intro η hη
    have hq' : 0 < 1 - q := by linarith
    obtain ⟨δ, hδ, hkey⟩ := key (η * (1 - q)) (mul_pos hη hq')
    refine ⟨min δ r, lt_min hδ hr, fun k hkd hk => ?_⟩
    have hbound : ∀ n : ℕ, ∀ k, |k - ks| < min δ r → k ≠ ks →
        |slope g ks k - l| ≤ q ^ n * B + η := by
      intro n
      induction n with
      | zero =>
        intro k hk hk'
        have := hB k (lt_of_lt_of_le hk (min_le_right _ _)) hk'
        rw [pow_zero, one_mul]
        linarith
      | succ n ih =>
        intro k hk hk'
        have hkr := lt_of_lt_of_le hk (min_le_right _ _)
        have h1 := hkey k (lt_of_lt_of_le hk (min_le_left _ _)) hk'
        have h2 := ih (g k) (lt_of_le_of_lt (hlip k hkr) hk) (hne k hkr hk')
        have h3 := mul_le_mul_of_nonneg_left h2 hq0
        rw [pow_succ]
        nlinarith
    have hlim : Tendsto (fun n : ℕ => q ^ n * B + η) atTop (𝓝 η) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const B).add_const η
    exact ge_of_tendsto' hlim fun n => hbound n k hkd hk
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  obtain ⟨δ, hδ, hs⟩ := hsmall (η / 2) (half_pos hη)
  refine ⟨δ, hδ, fun {k} hk hkd => ?_⟩
  rw [Real.dist_eq] at hkd ⊢
  have := hs k hkd hk
  linarith

variable {U f U' f' : ℝ → ℝ} {β : ℝ}

namespace Setting61

variable {kbar : ℝ} {v : Icc (0 : ℝ) kbar →ᵇ ℝ} (S : Setting61 U f U' f' β kbar v)
  [Nonempty (Icc (0 : ℝ) kbar)]
include S

/-- On `(0, k̄]`, `g(k)` lies between `k` and `k*` (from the monotone convergence of
`prop_6_1`). -/
theorem gpol_between {kstar : ℝ} (hks0 : 0 < kstar) (hks : f' kstar = 1 / β) {k : ℝ}
    (hk : 0 < k) (hkb : k ≤ kbar) :
    (k ≤ kstar → k ≤ gpol U f β kbar v k ∧ gpol U f β kbar v k ≤ kstar) ∧
      (kstar ≤ k → kstar ≤ gpol U f β kbar v k ∧ gpol U f β kbar v k ≤ k) := by
  obtain ⟨-, -, hconv⟩ := prop_6_1 S hks0 hks
  obtain ⟨hmon, hlim⟩ := hconv k hk hkb
  have e0 : (gpol U f β kbar v)^[0] k = k := rfl
  have e1 : (gpol U f β kbar v)^[1] k = gpol U f β kbar v k := rfl
  rcases hmon with hm | ha
  · have h1 : k ≤ gpol U f β kbar v k := by
      have := hm (Nat.zero_le 1)
      simpa only [e0, e1] using this
    have h2 : gpol U f β kbar v k ≤ kstar := by
      have := hm.ge_of_tendsto hlim 1
      simpa only [e1] using this
    exact ⟨fun _ => ⟨h1, h2⟩, fun h => ⟨by linarith, by linarith⟩⟩
  · have h1 : gpol U f β kbar v k ≤ k := by
      have := ha (Nat.zero_le 1)
      simpa only [e0, e1] using this
    have h2 : kstar ≤ gpol U f β kbar v k := by
      have := ha.le_of_tendsto hlim 1
      simpa only [e1] using this
    exact ⟨fun h => ⟨by linarith, by linarith⟩, fun _ => ⟨h2, h1⟩⟩

/-- **The slope of the policy at `k*` is any admissible root.** Let `U′` have derivative
`U₂ ≠ 0` at `c* = f(k*) − k*` and `f′` derivative `f₂` at `k*`. If `l ≥ 0` solves
`l² − (1 + β⁻¹ + c)l + β⁻¹ = 0` and `l < β⁻¹ + c`, with `c = βf₂U′(c*)/U₂`, then the optimal
policy `g` is differentiable at `k*` with `g′(k*) = l`. -/
theorem hasDerivAt_gpol_of_root {kstar : ℝ} (hks0 : 0 < kstar) (hks : f' kstar = 1 / β)
    {U2 f2 : ℝ} (hU2 : HasDerivAt U' U2 (f kstar - kstar)) (hU2ne : U2 ≠ 0)
    (hf2 : HasDerivAt f' f2 kstar) {l : ℝ}
    (hl : l ^ 2 - (1 + β⁻¹ + growthC β (U' (f kstar - kstar)) U2 f2) * l + β⁻¹ = 0)
    (hl0 : 0 ≤ l) (hlm : l < β⁻¹ + growthC β (U' (f kstar - kstar)) U2 f2) :
    HasDerivAt (gpol U f β kbar v) l kstar := by
  set g := gpol U f β kbar v with hg
  set c := growthC β (U' (f kstar - kstar)) U2 f2 with hc
  set m := β⁻¹ + c with hm
  have hβ := S.dyn.β_pos
  have hm0 : 0 < m := lt_of_le_of_lt hl0 hlm
  obtain ⟨hlt, hfixiff, -⟩ := prop_6_1 S hks0 hks
  have hgks : g kstar = kstar := (hfixiff kstar ⟨hks0.le, hlt.le⟩).2 (Or.inr rfl)
  have hks' : f' kstar = β⁻¹ := by rw [hks, one_div]
  have hf1 : HasDerivAt f β⁻¹ kstar := by
    have := S.dyn.f_deriv kstar hks0
    rwa [hks'] at this
  set r := min kstar (kbar - kstar) with hr
  have hr0 : 0 < r := lt_min hks0 (by linarith)
  have hin : ∀ k, |k - kstar| < r → 0 < k ∧ k < kbar := fun k hk => by
    have h1 := lt_of_lt_of_le hk (min_le_left _ _)
    have h2 := lt_of_lt_of_le hk (min_le_right _ _)
    rw [abs_lt] at h1 h2
    constructor <;> linarith
  have hbet : ∀ k, |k - kstar| < r →
      (k ≤ kstar → k ≤ g k ∧ g k ≤ kstar) ∧ (kstar ≤ k → kstar ≤ g k ∧ g k ≤ k) := fun k hk =>
    S.gpol_between hks0 hks (hin k hk).1 (hin k hk).2.le
  have hlip : ∀ k, |k - kstar| < r → |g k - kstar| ≤ |k - kstar| := fun k hk => by
    rcases le_total k kstar with h | h
    · obtain ⟨h1, h2⟩ := (hbet k hk).1 h
      rw [abs_of_nonpos (by linarith : k - kstar ≤ 0), abs_of_nonpos (by linarith)]
      linarith
    · obtain ⟨h1, h2⟩ := (hbet k hk).2 h
      rw [abs_of_nonneg (by linarith : 0 ≤ k - kstar), abs_of_nonneg (by linarith)]
      linarith
  have hne : ∀ k, |k - kstar| < r → k ≠ kstar → g k ≠ kstar := fun k hk hne h => by
    have hkI : k ∈ Icc (0 : ℝ) kbar := ⟨(hin k hk).1.le, (hin k hk).2.le⟩
    exact hne ((ex_6_1b S).injOn hkI ⟨hks0.le, hlt.le⟩ (h.trans hgks.symm))
  have hrel : ∀ k, (k - kstar) * slope g kstar k = g k - kstar := fun k => by
    have := sub_smul_slope g kstar k
    rwa [smul_eq_mul, vsub_eq_sub, hgks] at this
  have hsl : ∀ k, |k - kstar| < r → 0 ≤ slope g kstar k ∧ slope g kstar k ≤ 1 := by
    intro k hk
    have e := hrel k
    rcases lt_trichotomy k kstar with h | h | h
    · obtain ⟨h1, h2⟩ := (hbet k hk).1 h.le
      constructor <;> nlinarith
    · rw [h, slope_same]
      exact ⟨le_rfl, zero_le_one⟩
    · obtain ⟨h1, h2⟩ := (hbet k hk).2 h.le
      constructor <;> nlinarith
  refine hasDerivAt_of_slope_contraction (B := 1 + l) hr0 hlip hne
    (fun k hk _ => abs_le.2 ⟨by linarith [(hsl k hk).1], by linarith [(hsl k hk).2]⟩)
    (div_nonneg hl0 hm0.le) ((div_lt_one hm0).2 hlm) ?_
  intro τ hτ
  obtain ⟨δ, hδ, hlin⟩ := euler_linearization hβ hU2 hU2ne hf1 hf2 hks' (τ * m)
    (mul_pos hτ hm0)
  refine ⟨min δ r, lt_min hδ hr0, fun k hk hk' => ?_⟩
  have hkr := lt_of_lt_of_le hk (min_le_right _ _)
  have hkδ := lt_of_lt_of_le hk (min_le_left _ _)
  have hgr : |g k - kstar| < r := (hlip k hkr).trans_lt hkr
  have hfoc := S.foc (hin k hkr).1 (hin k hkr).2.le
  have hL := hlin k (g k) (g (g k)) hkδ (hlip k hkr) ((hlip (g k) hgr).trans (hlip k hkr)) hfoc
  set s := slope g kstar k with hs
  set s' := slope g kstar (g k) with hs'
  rw [← hrel (g k), ← hrel k] at hL
  have hx : 0 < |k - kstar| := abs_pos.2 (sub_ne_zero.2 hk')
  have hE : |(1 + m - s') * s - β⁻¹| ≤ τ * m := by
    have e : (k - kstar) * s * s' - (1 + β⁻¹ + c) * ((k - kstar) * s) + (k - kstar) / β =
        -(((1 + m - s') * s - β⁻¹) * (k - kstar)) := by
      rw [hm, div_eq_mul_inv]
      ring
    rw [e, abs_neg, abs_mul] at hL
    exact le_of_mul_le_mul_right hL hx
  have h01 := hsl (g k) hgr
  have iden : (1 + m - s') * (s - l) = ((1 + m - s') * s - β⁻¹) + l * (s' - l) := by
    rw [hm]
    linear_combination hl
  have hmain : m * |s - l| ≤ τ * m + l * |s' - l| := by
    calc m * |s - l| ≤ (1 + m - s') * |s - l| :=
          mul_le_mul_of_nonneg_right (by linarith [h01.2]) (abs_nonneg _)
      _ = |(1 + m - s') * (s - l)| := by
        rw [abs_mul, abs_of_pos (show 0 < 1 + m - s' by linarith [h01.2])]
      _ ≤ |(1 + m - s') * s - β⁻¹| + |l * (s' - l)| := by rw [iden]; exact abs_add_le _ _
      _ ≤ τ * m + l * |s' - l| := by rw [abs_mul, abs_of_nonneg hl0]; linarith
  rw [show l / m * |s' - l| + τ = (τ * m + l * |s' - l|) / m by field_simp; ring,
    le_div_iff₀ hm0]
  linarith

end Setting61

/-- **The growth example** (pp. 154–155). In the setting of §6.1, let `k* > 0` with
`f′(k*) = 1/β`, let `U′` have derivative `U″(c*) < 0` at `c* = f(k*) − k*` and `f′` derivative
`f″(k*) < 0` at `k*`, and `c = βf″(k*)U′(c*)/U″(c*)`. Then `c > 0`, the polynomial
`λ² − (1 + β⁻¹ + c)λ + β⁻¹` has exactly the roots `λ₁ ∈ (0, 1)` and `λ₂ > 1/β`, and the optimal
policy `g` is differentiable at `k*` with `g′(k*) = λ₁`. -/
theorem growth_policy_deriv {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)]
    {v : Icc (0 : ℝ) kbar →ᵇ ℝ} (S : Setting61 U f U' f' β kbar v) {kstar : ℝ}
    (hks0 : 0 < kstar) (hks : f' kstar = 1 / β) {U2 f2 : ℝ}
    (hU2 : HasDerivAt U' U2 (f kstar - kstar)) (hU2neg : U2 < 0)
    (hf2 : HasDerivAt f' f2 kstar) (hf2neg : f2 < 0) :
    0 < growthC β (U' (f kstar - kstar)) U2 f2 ∧
      ∃ l₁ l₂ : ℝ, 0 < l₁ ∧ l₁ < 1 ∧ 1 / β < l₂ ∧
        quadRoot (1 + β⁻¹ + growthC β (U' (f kstar - kstar)) U2 f2) β⁻¹ l₁ ∧
        quadRoot (1 + β⁻¹ + growthC β (U' (f kstar - kstar)) U2 f2) β⁻¹ l₂ ∧
        (∀ μ, quadRoot (1 + β⁻¹ + growthC β (U' (f kstar - kstar)) U2 f2) β⁻¹ μ →
          μ = l₁ ∨ μ = l₂) ∧
        HasDerivAt (gpol U f β kbar v) l₁ kstar := by
  have hβ := S.dyn.β_pos
  obtain ⟨hlt, hfixiff, -⟩ := prop_6_1 S hks0 hks
  have hgks : gpol U f β kbar v kstar = kstar := (hfixiff kstar ⟨hks0.le, hlt.le⟩).2 (Or.inr rfl)
  have hcs : 0 < f kstar - kstar := by
    have := (S.gpol_interior hks0 hlt.le).2
    rw [hgks] at this
    linarith
  have hU1 := S.dyn.U'_pos hcs
  have hc : 0 < growthC β (U' (f kstar - kstar)) U2 f2 := by
    simp only [growthC]
    exact div_pos_of_neg_of_neg (by nlinarith [mul_pos hβ hU1]) hU2neg
  obtain ⟨l₁, l₂, h0, h1, h2, hr1, hr2, hall⟩ := growth_roots hβ S.dyn.β_lt hc
  have hreal : l₁ ^ 2 - (1 + β⁻¹ + growthC β (U' (f kstar - kstar)) U2 f2) * l₁ + β⁻¹ = 0 := by
    have := hr1
    simp only [quadRoot] at this
    exact_mod_cast this
  have hbi : 1 < β⁻¹ := (one_lt_inv₀ hβ).2 S.dyn.β_lt
  exact ⟨hc, l₁, l₂, h0, h1, h2, hr1, hr2, hall,
    S.hasDerivAt_gpol_of_root hks0 hks hU2 hU2neg.ne hf2 hreal h0.le (by linarith)⟩

end StokeyLucasPrescott.DeterministicDynamics
