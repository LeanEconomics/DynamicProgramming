/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.JobMatching

/-!
# Job matching: the beta posterior

SLP §10.10, Exercise 10.10a–e, pp. 311–313. After `k` successes in `n` trials the density of
the success probability `θ` is `f(θ, n, k) ∝ C(n, k) θᵏ(1 − θ)ⁿ⁻ᵏ μ(θ)` (`postDensity`), and
`π(n, k) = ∫ θ f(θ, n, k) dθ` (`postMean`).

* `integral_beta_kernel`: `∫₀¹ x^{a−1}(1 − x)^{b−1} dx = Γ(a)Γ(b)/Γ(a + b)`.
* **Exercise 10.10a–b** (`ex_10_10a`, `ex_10_10b`): with the uniform prior the posterior is
  beta `(k + 1, n + 1 − k)`; with a beta `(α, β)` prior it is beta `(α + k, β + n − k)`.
* **Exercise 10.10c** (`ex_10_10c`): `π(n, k) = (α + k)/(α + β + n)` (`betaπ`).
* **Exercise 10.10d** (`ex_10_10d`): the four inequalities, as `PiProps`.
* **Exercise 10.10e** (`ex_10_10e`): `kₙ/n → p` implies `π(n, kₙ) → p`; uniformly on the
  windows `{(n + j, kₙ + i) : i ≤ j ≤ J}` (`betaπ_window`), so the limit of Exercise 10.10g holds
  for the beta prior (`ex_10_10g_beta`). Whether (d)–(e) hold for an arbitrary prior density
  positive on `(0, 1)` is not addressed.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

/-- The beta integral: `∫₀¹ x^{a−1}(1 − x)^{b−1} dx = Γ(a)Γ(b)/Γ(a + b)`. -/
theorem integral_beta_kernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Ioo (0 : ℝ) 1, x ^ (a - 1) * (1 - x) ^ (b - 1) = beta a b := by
  rw [beta_eq_betaIntegralReal a b ha hb, Complex.betaIntegral,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Ioc_eq_integral_Ioo,
    ← RCLike.re_to_complex, ← integral_re]
  · refine setIntegral_congr_fun measurableSet_Ioc fun x ⟨hx1, hx2⟩ => ?_
    norm_cast
    rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
      Complex.re_mul_ofReal, Complex.ofReal_re]
    all_goals linarith
  · convert! Complex.betaIntegral_convergent (u := a) (v := b) (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]

/-- The posterior density of `θ` after `k` successes in `n` trials, for a prior density `μ` on
`(0, 1)` (Bayes's rule, p. 312). -/
noncomputable def postDensity (μ : ℝ → ℝ) (n k : ℕ) (θ : ℝ) : ℝ :=
  (n.choose k : ℝ) * θ ^ k * (1 - θ) ^ (n - k) * μ θ /
    ∫ u in Ioo (0 : ℝ) 1, (n.choose k : ℝ) * u ^ k * (1 - u) ^ (n - k) * μ u

/-- The expected return `π(n, k) = ∫ θ f(θ, n, k) dθ` on the next trial. -/
noncomputable def postMean (μ : ℝ → ℝ) (n k : ℕ) : ℝ :=
  ∫ θ in Ioo (0 : ℝ) 1, θ * postDensity μ n k θ

/-- With a beta prior, the likelihood times the prior is a beta kernel. -/
theorem lik_mul_betaPDF {α β : ℝ} {n k : ℕ} (hkn : k ≤ n) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (n.choose k : ℝ) * u ^ k * (1 - u) ^ (n - k) * betaPDFReal α β u =
      (n.choose k : ℝ) / beta α β * (u ^ (α + k - 1) * (1 - u) ^ (β + n - k - 1)) := by
  have h0 : 0 < u := hu.1
  have h1 : 0 < 1 - u := by linarith [hu.2]
  rw [betaPDFReal, ite_eq_left_of_eq_true _ _ (eq_true (show 0 < u ∧ u < 1 from hu))]
  have e1 : u ^ (α + k - 1) = u ^ (k : ℝ) * u ^ (α - 1) := by
    rw [← Real.rpow_add h0]; ring_nf
  have e2 : (1 - u) ^ (β + n - k - 1) = (1 - u) ^ ((n - k : ℕ) : ℝ) * (1 - u) ^ (β - 1) := by
    rw [← Real.rpow_add h1, Nat.cast_sub hkn]; ring_nf
  rw [e1, e2, Real.rpow_natCast, Real.rpow_natCast]
  ring

/-- The normalizing constant of the posterior under a beta prior. -/
theorem integral_lik_mul_betaPDF {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n k : ℕ} (hkn : k ≤ n) :
    ∫ u in Ioo (0 : ℝ) 1, (n.choose k : ℝ) * u ^ k * (1 - u) ^ (n - k) * betaPDFReal α β u =
      (n.choose k : ℝ) / beta α β * beta (α + k) (β + n - k) := by
  rw [setIntegral_congr_fun measurableSet_Ioo fun u hu => lik_mul_betaPDF hkn hu,
    integral_const_mul, integral_beta_kernel (by positivity)]
  have : (k : ℝ) ≤ n := by exact_mod_cast hkn
  linarith

/-- `B(a, b) = Γ(a)Γ(b)/Γ(a + b)`, positive. -/
theorem beta_pos' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < beta a b := beta_pos ha hb

/-- **Exercise 10.10b.** With the beta prior `μ(θ) = Γ(α + β)/[Γ(α)Γ(β)] θ^{α−1}(1 − θ)^{β−1}`,
the posterior after `k` successes in `n` trials is the beta density with parameters
`(α + k, β + n − k)`. -/
theorem ex_10_10b {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n k : ℕ} (hkn : k ≤ n) {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    postDensity (betaPDFReal α β) n k θ = Real.Gamma (α + β + n) /
      (Real.Gamma (α + k) * Real.Gamma (β + n - k)) * θ ^ (α + k - 1) *
        (1 - θ) ^ (β + n - k - 1) := by
  have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hb1 : 0 < β + n - k := by linarith
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hB := beta_pos hα hβ
  have hB' := beta_pos (show 0 < α + k by positivity) hb1
  rw [postDensity, lik_mul_betaPDF hkn hθ, integral_lik_mul_betaPDF hα hβ hkn]
  have e : α + k + (β + n - k) = α + β + n := by ring
  rw [show beta (α + k) (β + n - k) = Real.Gamma (α + k) * Real.Gamma (β + n - k) /
    Real.Gamma (α + β + n) by rw [beta, e]]
  have hG1 := Real.Gamma_pos_of_pos (show 0 < α + k by positivity)
  have hG2 := Real.Gamma_pos_of_pos hb1
  have hG3 := Real.Gamma_pos_of_pos (show 0 < α + β + n by positivity)
  field_simp

/-- **Exercise 10.10a.** With the uniform prior `μ = 1` on `(0, 1)`, the posterior is the beta
density with parameters `(k + 1, n + 1 − k)`. -/
theorem ex_10_10a {n k : ℕ} (hkn : k ≤ n) {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    postDensity (fun _ => 1) n k θ = Real.Gamma (n + 2) /
      (Real.Gamma (k + 1) * Real.Gamma (n + 1 - k)) * θ ^ k * (1 - θ) ^ (n - k) := by
  -- the uniform density is the beta(1, 1) density on `(0, 1)`
  have hB : beta 1 1 = 1 := by norm_num [beta, Real.Gamma_two]
  have hU : ∀ u ∈ Ioo (0 : ℝ) 1, betaPDFReal 1 1 u = 1 := fun u hu => by
    rw [betaPDFReal, ite_eq_left_of_eq_true _ _ (eq_true (show 0 < u ∧ u < 1 from hu)), hB]; simp
  have hpost : postDensity (fun _ => 1) n k θ = postDensity (betaPDFReal 1 1) n k θ := by
    unfold postDensity
    rw [hU θ hθ, setIntegral_congr_fun (g := fun u => (n.choose k : ℝ) * u ^ k * (1 - u) ^ (n - k) *
      betaPDFReal 1 1 u) measurableSet_Ioo fun u hu => by simp only [hU u hu]]
  rw [hpost, ex_10_10b one_pos one_pos hkn hθ]
  have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have e1 : (1 : ℝ) + 1 + n = n + 2 := by ring
  have e2 : (1 : ℝ) + k = k + 1 := by ring
  have e3 : (1 : ℝ) + n - k = n + 1 - k := by ring
  have e4 : θ ^ ((1 : ℝ) + k - 1) = θ ^ k := by
    rw [show (1 : ℝ) + k - 1 = (k : ℝ) by ring, Real.rpow_natCast]
  have e5 : (1 - θ) ^ ((1 : ℝ) + n - k - 1) = (1 - θ) ^ (n - k) := by
    rw [show (1 : ℝ) + n - k - 1 = ((n - k : ℕ) : ℝ) by rw [Nat.cast_sub hkn]; ring,
      Real.rpow_natCast]
  rw [e4, e5, e1, e2, e3]

/-- **Exercise 10.10c.** With the beta prior, `π(n, k) = (α + k)/(α + β + n)`. -/
theorem ex_10_10c {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n k : ℕ} (hkn : k ≤ n) :
    postMean (betaPDFReal α β) n k = (α + k) / (α + β + n) := by
  have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hb1 : 0 < β + n - k := by linarith
  have hak : 0 < α + k := by positivity
  rw [postMean, setIntegral_congr_fun measurableSet_Ioo fun θ hθ => by
      rw [ex_10_10b hα hβ hkn hθ]]
  have hint : ∀ θ ∈ Ioo (0 : ℝ) 1, θ * (Real.Gamma (α + β + n) /
      (Real.Gamma (α + k) * Real.Gamma (β + n - k)) * θ ^ (α + k - 1) *
        (1 - θ) ^ (β + n - k - 1)) = Real.Gamma (α + β + n) /
      (Real.Gamma (α + k) * Real.Gamma (β + n - k)) *
        (θ ^ (α + k + 1 - 1) * (1 - θ) ^ (β + n - k - 1)) := fun θ hθ => by
    have : θ ^ (α + k + 1 - 1) = θ * θ ^ (α + k - 1) := by
      rw [show α + k + 1 - 1 = 1 + (α + k - 1) by ring, Real.rpow_add hθ.1, Real.rpow_one]
    rw [this]; ring
  rw [setIntegral_congr_fun measurableSet_Ioo hint, integral_const_mul,
    integral_beta_kernel (by positivity) hb1, beta]
  have e : α + k + 1 + (β + n - k) = α + β + n + 1 := by ring
  rw [e, Real.Gamma_add_one hak.ne', Real.Gamma_add_one (by positivity : α + β + n ≠ 0)]
  have hG1 := Real.Gamma_pos_of_pos hak
  have hG2 := Real.Gamma_pos_of_pos hb1
  have hG3 := Real.Gamma_pos_of_pos (show 0 < α + β + n by positivity)
  field_simp

/-- The success probability `π(n, k) = (α + k)/(α + β + n)` of Exercise 10.10c. -/
noncomputable def betaπ (α β : ℝ) (n k : ℕ) : ℝ := (α + k) / (α + β + n)

/-- **Exercise 10.10d.** `0 < π(n, k) < 1`, `π(n, k + 1) > π(n, k)`, `π(n + 1, k) < π(n, k)` and
`π(n + 1, k + 1) > π(n, k)`. -/
theorem ex_10_10d {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : PiProps (betaπ α β) := by
  refine ⟨fun n k hkn => ?_, fun n k hkn => ?_, fun n k hkn => ?_, fun n k hkn => ?_⟩ <;>
    unfold betaπ <;> push_cast
  · have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
    exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩
  · have hk : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    exact div_lt_div_of_pos_right (by linarith) (by positivity)
  · have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
    exact div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  · have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem betaπ_mem {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∀ n k, k ≤ n → 0 ≤ betaπ α β n k ∧ betaπ α β n k ≤ 1 := fun n k hkn =>
  ⟨((ex_10_10d hα hβ).bounds n k hkn).1.le, ((ex_10_10d hα hβ).bounds n k hkn).2.le⟩

/-- `π(n + j, kₙ + i) → p` when `kₙ/n → p`. -/
theorem betaπ_tendsto {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {k : ℕ → ℕ} {p : ℝ}
    (hp : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 p)) (j i : ℕ) :
    Tendsto (fun n => betaπ α β (n + j) (k n + i)) atTop (𝓝 p) := by
  have hnum := (tendsto_const_div_atTop_nhds_zero_nat (α + i)).add hp
  have hden := (tendsto_const_div_atTop_nhds_zero_nat (α + β + j)).add_const (1 : ℝ)
  rw [zero_add] at hnum hden
  have := hnum.div hden one_ne_zero
  rw [div_one] at this
  refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change ((α + i) / n + k n / n) / ((α + β + j) / n + 1) = betaπ α β (n + j) (k n + i)
  unfold betaπ
  push_cast
  field_simp
  ring

/-- **Exercise 10.10e.** If `kₙ ≤ n` and `kₙ/n → p`, then `π(n, kₙ) → p`. -/
theorem ex_10_10e {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {k : ℕ → ℕ} {p : ℝ}
    (hp : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 p)) :
    Tendsto (fun n => betaπ α β n (k n)) atTop (𝓝 p) := by
  simpa using betaπ_tendsto hα hβ hp 0 0

/-- The beta `π` is uniformly near `p` on the windows `{(n + j, kₙ + i) : i ≤ j ≤ J}`. -/
theorem betaπ_window {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {k : ℕ → ℕ} {p : ℝ}
    (hp : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 p)) (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ j i, i ≤ j → j ≤ J → |betaπ α β (n + j) (k n + i) - p| ≤ ε := by
  have h : ∀ j ∈ Finset.range (J + 1), ∀ i ∈ Finset.range (J + 1),
      ∀ᶠ n in atTop, |betaπ α β (n + j) (k n + i) - p| ≤ ε := fun j _ i _ =>
    (Metric.tendsto_nhds.1 (betaπ_tendsto hα hβ hp j i) ε hε).mono fun n hn =>
      (Real.dist_eq _ _ ▸ hn).le
  have h' : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (J + 1), ∀ i ∈ Finset.range (J + 1),
      |betaπ α β (n + j) (k n + i) - p| ≤ ε :=
    (eventually_all_finset _).2 fun j hj => (eventually_all_finset _).2 (h j hj)
  filter_upwards [h'] with n hn j i hij hjJ
  exact hn j (Finset.mem_range.2 (by omega)) i (Finset.mem_range.2 (by omega))

/-- **Exercise 10.10g** (limit) for the beta prior: if `kₙ ≤ n` and `kₙ/n → p`, then
`v(n, kₙ) → max{p/(1 − β), v(0, 0)}`. -/
theorem ex_10_10g_beta {α β₀ β : ℝ} (hα : 0 < α) (hβ₀ : 0 < β₀) (hβ0 : 0 < β) (hβ1 : β < 1)
    {v : triD →ᵇ ℝ} (hv : jobT (betaπ_mem hα hβ₀) hβ0.le v = v) {k : ℕ → ℕ}
    (hk : ∀ n, k n ≤ n) {p : ℝ} (hp : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 p)) :
    Tendsto (fun n => v (triMk n (k n) (hk n))) atTop (𝓝 (max (p / (1 - β)) (v tri00))) := by
  have hb : ∀ n, 0 ≤ (k n : ℝ) / n ∧ (k n : ℝ) / n ≤ 1 := fun n => by
    refine ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast hk n) (by positivity)⟩
  exact ex_10_10g_limit (betaπ_mem hα hβ₀) hβ0 hβ1 hv hk
    ⟨ge_of_tendsto' hp fun n => (hb n).1, le_of_tendsto' hp fun n => (hb n).2⟩
    (betaπ_window hα hβ₀ hp)

end StokeyLucasPrescott.StochasticApplications
