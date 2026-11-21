/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.MIUNonseparable

/-!
# Money in the utility function

AKMM, §17.3.2, "Money in the utility function", p. 511. Preferences
`∑ βᵗ[u(c_t, m_{t+1}p_{m,t}/p_{m,t+1}) + v(l_t)]` (17.30), budget (17.19), first-order conditions
(17.31)–(17.34).

* `eq_17_35`: (17.31), (17.33), (17.34) and the Fisher equation give `u₂/u₁ = i/(1 + i)`.
* `miu_homothetic_partials`, `miu_homothetic_mrs`: for a constant-returns index
  `h(c, m) = cφ(m/c)` (every constant-returns function on `c > 0` has this form) and
  `u = F ∘ h`, `u₂/u₁ = φ′(x)/(φ(x) − xφ′(x))` depends only on `x = m/c`.
* `miu_homothetic_demand`: if this ratio is injective in `x`, the money demand `m/c` is a
  function of `i/(1 + i)` alone.
* `miu_ces_crs`: the CES composite of Galí (2015, p. 35), imported from the
  `ClassicalMonetaryModel` dependency, is of this form (it is AKMM's `h` of p. 518).
-/

namespace AKMM.Money

/-- **AKMM, (17.35)**, p. 511: from `u₁ = λ_t` (17.31), `λ_tq_t = βλ_{t+1}` (17.33),
`λ_tR = u₂R + βλ_{t+1}` (17.34), `R = p_{m,t}/p_{m,t+1}`, and the Fisher equation
`q_t(1 + i_t) = R`: `1 = u₂/u₁ + 1/(1 + i)`, i.e. `u₂/u₁ = i/(1 + i)`. -/
theorem eq_17_35 {U1 U2 lam lam' q R i β : ℝ} (hlam : 0 < lam) (hR : R ≠ 0) (hi : 1 + i ≠ 0)
    (h31 : U1 = lam) (h33 : lam * q = β * lam') (h34 : lam * R = U2 * R + β * lam')
    (hF : q * (1 + i) = R) : 1 = U2 / U1 + 1 / (1 + i) ∧ U2 / U1 = i / (1 + i) := by
  have hq : q = R / (1 + i) := by rw [← hF]; field_simp
  have h : lam = U2 + lam / (1 + i) := by
    have : lam * R = U2 * R + lam * q := by rw [h34, h33]
    rw [hq] at this
    apply mul_right_cancel₀ hR
    rw [this]; field_simp
  have h1 : 1 = U2 / U1 + 1 / (1 + i) := by
    have hU2 : U2 = lam - lam / (1 + i) := by linarith
    rw [h31, hU2]; field_simp; ring
  refine ⟨h1, ?_⟩
  have : U2 / U1 = 1 - 1 / (1 + i) := by linarith
  rw [this]; field_simp; ring

/-- AKMM, p. 511: partial derivatives of a constant-returns index `h(c, m) = cφ(m/c)`:
`h_c = φ(x) − xφ′(x)` and `h_m = φ′(x)`, `x = m/c`. -/
theorem miu_homothetic_partials {φ : ℝ → ℝ} {φ' c m : ℝ} (hc : c ≠ 0)
    (hφ : HasDerivAt φ φ' (m / c)) :
    HasDerivAt (fun c' => c' * φ (m / c')) (φ (m / c) - m / c * φ') c ∧
      HasDerivAt (fun m' => c * φ (m' / c)) φ' m := by
  constructor
  · have hd : HasDerivAt (fun c' => m / c') (-(m / c ^ 2)) c := by
      have := (hasDerivAt_inv hc).const_mul m
      refine (this.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun x => by simp [div_eq_mul_inv]
    have := (hasDerivAt_id' c).mul (hφ.comp c hd)
    refine this.congr_deriv ?_
    have e : c * (φ' * -(m / c ^ 2)) = -(m / c * φ') := by field_simp
    rw [Function.comp_apply, e]
    ring
  · have hd : HasDerivAt (fun m' => m' / c) (1 / c) m := by
      simpa using (hasDerivAt_id' m).div_const c
    have := (hφ.comp m hd).const_mul c
    refine this.congr_deriv ?_
    field_simp

/-- AKMM, p. 511: with `u = F ∘ h`, `F′(h) ≠ 0`, `h(c, m) = cφ(m/c)`, the marginal rate of
substitution `u₂/u₁ = F′h_m/(F′h_c) = φ′(x)/(φ(x) − xφ′(x))` depends only on `x = m/c`. -/
theorem miu_homothetic_mrs {F φ : ℝ → ℝ} {F' φ' c m : ℝ} (hc : c ≠ 0)
    (hF : HasDerivAt F F' (c * φ (m / c))) (hφ : HasDerivAt φ φ' (m / c)) (hF0 : F' ≠ 0) :
    ∃ U1 U2, HasDerivAt (fun c' => F (c' * φ (m / c'))) U1 c ∧
      HasDerivAt (fun m' => F (c * φ (m' / c))) U2 m ∧
      U2 / U1 = φ' / (φ (m / c) - m / c * φ') := by
  obtain ⟨h1, h2⟩ := miu_homothetic_partials hc hφ
  refine ⟨F' * (φ (m / c) - m / c * φ'), F' * φ', hF.comp c h1, hF.comp m h2, ?_⟩
  rw [mul_div_mul_left _ _ hF0]

/-- AKMM, p. 511: if the marginal rate of substitution `g(x) = φ′(x)/(φ(x) − xφ′(x))` is
injective on the positive ratios, then any two consumers facing the same opportunity cost
`i/(1 + i)` (so `g(m/c) = g(m′/c′) = i/(1 + i)` by (17.35)) hold the same ratio of real
balances to consumption: money demand is `m/c = g⁻¹(i/(1 + i))`. -/
theorem miu_homothetic_demand {g : ℝ → ℝ} (hg : Set.InjOn g (Set.Ioi 0)) {c m c' m' i : ℝ}
    (hx : 0 < m / c) (hx' : 0 < m' / c') (h : g (m / c) = i / (1 + i))
    (h' : g (m' / c') = i / (1 + i)) : m / c = m' / c' :=
  hg hx hx' (h.trans h'.symm)

/-- AKMM, p. 518 (with Galí 2015, p. 35): the CES index
`h(c, m) = ((1 − ω)c^ρ + ωm^ρ)^{1/ρ}` (Galí's `composite ω (1 − ρ)`) has constant returns,
`h(c, m) = c h(1, m/c)`, so it is homothetic in the sense above. -/
theorem miu_ces_crs {ω ρ c m : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c) (hm : 0 < m) :
    Gali.ClassicalMonetaryModel.MIUNonseparable.composite ω (1 - ρ) c m =
      c * Gali.ClassicalMonetaryModel.MIUNonseparable.composite ω (1 - ρ) 1 (m / c) := by
  have := Gali.ClassicalMonetaryModel.MIUNonseparable.composite_homogeneous (ν := 1 - ρ)
    hω0 hω1 one_pos (div_pos hm hc) hc
  rw [mul_one, mul_div_cancel₀ _ hc.ne'] at this
  exact this

end AKMM.Money
