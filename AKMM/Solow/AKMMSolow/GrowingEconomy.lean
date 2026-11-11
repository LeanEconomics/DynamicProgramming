/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSolow.BasicModel
import DiscreteTime.GeneralSolowApplications

/-!
# The growing economy, balanced growth, and factor prices

AKMM, §3.2–3.3, pp. 78–81. Labour-augmenting technology `A_{t+1} = (1 + γ)A_t` and labour
`L_{t+1} = (1 + n)L_t`; capital per efficiency unit `k̃_t = K_t/(A_t L_t)` follows (3.7),
`(1 + γ)(1 + n) k̃_{t+1} = (1 − δ)k̃_t + s f(k̃_t)`, which is EconomicGrowth's map
`Solow1956.DiscreteTime.next f s δ ((1 + γ)(1 + n))`.

* (3.7) from the aggregate equations (`eq_3_7`, via EconomicGrowth's
  `capitalPerEffectiveWorker_succ`); the balanced-growth `k̃̄` exists uniquely
  (`solow_bgp_existsUnique`); Cobb–Douglas closed form (3.8) (`eq_3_8`); every path of (3.7)
  converges monotonically (`solow_detrended_convergence`); `γ` and `n` act like depreciation
  (`solow_bgp_strictAnti_growth`).
* Untransforming: `Y/(AL) = f(k̃)`, `y = Y/L = A f(k̃)`, `K/Y = k̃/f(k̃)`
  (`solow_untransform`); from
  the aggregate equations `k̃_t`, `Y_t/(A_tL_t)` and `K_t/Y_t` converge
  (`solow_aggregate_convergence`).
* Growth rates (p. 80): on the balanced path income per capita grows at `γ`
  (`solow_bgp_income_growth`); in general its growth rate is `(1 + γ) f(k̃_{t+1})/f(k̃_t) − 1`
  (`solow_income_growth_identity`), above `γ` below the balanced path and below `γ` above it
  (`solow_transition_growth`), and it converges to `γ` (`solow_income_growth_tendsto`); `y_t/A_t`
  converges to `f(k̃̄)` (`solow_income_long_run`).
* Factor prices (§3.3, p. 81): `r = F₁(K, AL) = f'(k̃)` (`solow_rental_rate`),
  `w = F₂(K, AL) = f(k̃) − k̃ f'(k̃)` (`solow_wage_rate`; EconomicGrowth's `wage`), Euler's theorem
  `Y = K F₁ + AL F₂` (`solow_euler`), the shares (`solow_factor_shares`), their constancy on the
  balanced path and their convergence along any path (`solow_factor_prices_bgp`,
  `solow_factor_prices_tendsto`), and Cobb–Douglas shares `α`, `1 − α` everywhere
  (`solow_cobbDouglas_shares`).
-/

namespace AKMM.Solow

open Filter Topology Solow1956.Neoclassical Solow1956.DiscreteTime

variable {F : ℝ → ℝ → ℝ}

/-- AKMM, §3.2, p. 78: with `0 < s`, `0 < δ < 1` and nonnegative growth rates `γ, n` of
technology and labour, the detrended model has EconomicGrowth's parameter conditions with gross
effective-labour growth `(1 + γ)(1 + n)`. -/
theorem solow_params_growth {s δ γ n : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ)
    (hn : 0 ≤ n) : Params s δ ((1 + γ) * (1 + n)) :=
  ⟨hs, hδ1.le, by positivity, by nlinarith [mul_nonneg hγ hn]⟩

/-- AKMM, (3.7), p. 79: aggregate accumulation `K_{t+1} = (1 − δ)K_t + s F(K_t, A_t L_t)` with
`A_{t+1} = (1 + γ)A_t`, `L_{t+1} = (1 + n)L_t` and constant returns gives
`(1 + γ)(1 + n) k̃_{t+1} = (1 − δ)k̃_t + s f(k̃_t)` for `k̃_t = K_t/(A_t L_t)`; this is
EconomicGrowth's map (`capitalPerEffectiveWorker_succ`). -/
theorem eq_3_7 (hF : SolowAssumptions F) {s δ γ n : ℝ} {K A L : ℕ → ℝ} {t : ℕ}
    (hG : 0 < (1 + γ) * (1 + n)) (hA : A (t + 1) = (1 + γ) * A t)
    (hL : L (t + 1) = (1 + n) * L t) (hApos : 0 < A t) (hLpos : 0 < L t) (hK0 : 0 ≤ K t)
    (hK : K (t + 1) = (1 - δ) * K t + s * F (K t) (A t * L t)) :
    K (t + 1) / (A (t + 1) * L (t + 1)) =
        next (intensive F) s δ ((1 + γ) * (1 + n)) (K t / (A t * L t)) ∧
      (1 + γ) * (1 + n) * (K (t + 1) / (A (t + 1) * L (t + 1))) =
        (1 - δ) * (K t / (A t * L t)) + s * intensive F (K t / (A t * L t)) := by
  have hE : 0 < A t * L t := mul_pos hApos hLpos
  have h1 : K (t + 1) / (A (t + 1) * L (t + 1)) =
      next (intensive F) s δ ((1 + γ) * (1 + n)) (K t / (A t * L t)) :=
    capitalPerEffectiveWorker_succ (E := fun u => A u * L u)
      (Y := fun u => F (K u) (A u * L u)) hG hE (by rw [hK]; ring)
      (by rw [hA, hL]; ring) (solow_intensive_form hF hK0 hE)
  refine ⟨h1, ?_⟩
  rw [h1]
  unfold next
  set G := (1 + γ) * (1 + n)
  field_simp
  ring

/-- AKMM, p. 79: a constant path `k̃_t = k̃̄` solves (3.7) exactly when
`(1 + γ)(1 + n) k̃̄ = (1 − δ)k̃̄ + s f(k̃̄)`. -/
theorem solow_fixed_iff_growth {f : ℝ → ℝ} {s δ G k : ℝ} (hG : 0 < G) :
    next f s δ G k = k ↔ G * k = (1 - δ) * k + s * f k := by
  unfold next
  rw [div_eq_iff (ne_of_gt hG)]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 79: the balanced-growth value `k̃̄ > 0` with
`(1 + γ)(1 + n) k̃̄ = (1 − δ)k̃̄ + s f(k̃̄)` exists and is unique (EconomicGrowth's
`existsUnique_steadyState`). -/
theorem solow_bgp_existsUnique (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    ∃! k : ℝ, 0 < k ∧ (1 + γ) * (1 + n) * k = (1 - δ) * k + s * intensive F k := by
  have P := solow_params_growth hs hδ hδ1 hγ hn
  simpa only [solow_fixed_iff_growth P.growth_pos] using
    existsUnique_steadyState (solow_technology hF) P

/-- AKMM, (3.8), p. 79: with `f(k) = k^α`, `k̃̄ = (s/((1 + γ)(1 + n) + δ − 1))^{1/(1−α)}`
(EconomicGrowth's `CobbDouglas.steady_eq`). -/
theorem eq_3_8 {α s δ γ n : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    steady (technology_rpow hα hα1) s δ ((1 + γ) * (1 + n)) =
      (s / ((1 + γ) * (1 + n) + δ - 1)) ^ (1 / (1 - α)) := by
  rw [CobbDouglas.steady_eq hα hα1 (solow_params_growth hs hδ hδ1 hγ hn),
    Solow1956.SolowSwan.CobbDouglas.steadyState, one_div]
  congr 2
  ring

/-- AKMM, p. 79: starting from any `k̃₀ > 0`, the path of (3.7) converges monotonically to `k̃̄`
(EconomicGrowth's `IsPath.orbit`). -/
theorem solow_detrended_convergence (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {k : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, (1 + γ) * (1 + n) * k (t + 1) = (1 - δ) * k t + s * intensive F (k t)) :
    (∀ t, 0 < k t) ∧
      (k 0 < steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) → StrictMono k ∧
        ∀ t, k t < steady (solow_technology hF) s δ ((1 + γ) * (1 + n))) ∧
      (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) < k 0 → StrictAnti k ∧
        ∀ t, steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) < k t) ∧
      Tendsto k atTop (𝓝 (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)))) := by
  have P := solow_params_growth hs hδ hδ1 hγ hn
  have hp : IsPath (intensive F) s δ ((1 + γ) * (1 + n)) k := ⟨h0, fun t => by
    unfold next
    rw [eq_div_iff (ne_of_gt P.growth_pos), mul_comm, hk]
    ring⟩
  obtain ⟨h1, h2, h3, _, _, h6⟩ := hp.orbit (solow_technology hF) P
  exact ⟨h1, h2, h3, h6⟩

/-- AKMM, p. 79: "the rate of technological progress `γ` and the population growth rate `n`
work similarly to depreciation": faster growth of `A` or `L` lowers `k̃̄`
(EconomicGrowth's `steady_strictAnti_growth`). -/
theorem solow_bgp_strictAnti_growth (hF : SolowAssumptions F) {s δ G₁ G₂ : ℝ} (hs : 0 < s)
    (hm : 0 < G₁ - 1 + δ) (hG : G₁ < G₂) :
    steady (solow_technology hF) s δ G₂ < steady (solow_technology hF) s δ G₁ :=
  steady_strictAnti_growth (solow_technology hF) hs hm hG

/-- AKMM, pp. 79–80: untransforming, `Y_t/(A_t L_t) = f(k̃_t)`, income per capita
`y_t = Y_t/L_t = A_t f(k̃_t)` and `K_t/Y_t = k̃_t/f(k̃_t)`, where `Y_t = F(K_t, A_t L_t)`. -/
theorem solow_untransform (hF : SolowAssumptions F) {K A L : ℝ} (hK : 0 < K) (hA : 0 < A)
    (hL : 0 < L) :
    F K (A * L) / (A * L) = intensive F (K / (A * L)) ∧
      F K (A * L) / L = A * intensive F (K / (A * L)) ∧
      K / F K (A * L) = K / (A * L) / intensive F (K / (A * L)) := by
  have hE : 0 < A * L := mul_pos hA hL
  have hf := solow_intensive_pos hF (div_pos hK hE)
  rw [solow_intensive_form hF hK.le hE]
  refine ⟨by field_simp, by field_simp, by field_simp⟩

/-- AKMM, pp. 79–80: from the aggregate equations and `K₀ > 0`, capital per efficiency unit,
output per efficiency unit and the capital–output ratio converge to their balanced-growth values
`k̃̄`, `f(k̃̄)` and `k̃̄/f(k̃̄)` ("the ratio `k_t/y_t` eventually stabilizes", p. 75). -/
theorem solow_aggregate_convergence (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {K A L : ℕ → ℝ}
    (hA : ∀ t, A (t + 1) = (1 + γ) * A t) (hL : ∀ t, L (t + 1) = (1 + n) * L t)
    (hApos : ∀ t, 0 < A t) (hLpos : ∀ t, 0 < L t) (hK0 : 0 < K 0)
    (hK : ∀ t, K (t + 1) = (1 - δ) * K t + s * F (K t) (A t * L t)) :
    Tendsto (fun t => K t / (A t * L t)) atTop
        (𝓝 (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)))) ∧
      Tendsto (fun t => F (K t) (A t * L t) / (A t * L t)) atTop
        (𝓝 (intensive F (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) ∧
      Tendsto (fun t => K t / F (K t) (A t * L t)) atTop
        (𝓝 (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) /
          intensive F (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) := by
  have P := solow_params_growth hs hδ hδ1 hγ hn
  have h := solow_technology hF
  have hpath : IsPath (intensive F) s δ ((1 + γ) * (1 + n)) (fun t => K t / (A t * L t)) := by
    refine ⟨div_pos hK0 (mul_pos (hApos 0) (hLpos 0)), fun t => ?_⟩
    have hpos : 0 < K t := by
      induction t with
      | zero => exact hK0
      | succ u ih =>
        rw [hK u]
        have := mul_pos hs (solow_intensive_form hF ih.le (mul_pos (hApos u) (hLpos u)) ▸
          mul_pos (mul_pos (hApos u) (hLpos u))
            (solow_intensive_pos hF (div_pos ih (mul_pos (hApos u) (hLpos u)))))
        have := mul_nonneg (sub_nonneg.mpr hδ1.le) ih.le
        linarith
    exact (eq_3_7 hF P.growth_pos (hA t) (hL t) (hApos t) (hLpos t) hpos.le (hK t)).1
  have hlim := hpath.tendsto h P
  have hks := (steady_spec h P).1
  have hpos : ∀ t, 0 < K t := fun t => by
    have := hpath.pos h P t
    exact (div_pos_iff_of_pos_right (mul_pos (hApos t) (hLpos t))).mp this
  have hy : Tendsto (fun t => intensive F (K t / (A t * L t))) atTop
      (𝓝 (intensive F (steady h s δ ((1 + γ) * (1 + n))))) :=
    (h.differentiable _ hks).continuousAt.tendsto.comp hlim
  have e1 : ∀ t, F (K t) (A t * L t) / (A t * L t) = intensive F (K t / (A t * L t)) :=
    fun t => (solow_untransform hF (hpos t) (hApos t) (hLpos t)).1
  have e2 : ∀ t, K t / F (K t) (A t * L t) =
      K t / (A t * L t) / intensive F (K t / (A t * L t)) :=
    fun t => (solow_untransform hF (hpos t) (hApos t) (hLpos t)).2.2
  refine ⟨hlim, ?_, ?_⟩
  · simp only [e1]
    exact hy
  · simp only [e2]
    exact hlim.div hy (ne_of_gt (h.output_pos hks))

/-- AKMM, p. 80: in the long run `y_t/A_t = f(k̃_t)` converges to `f(k̃̄)`, i.e. income per
capita approaches `f(k̃̄) A_t`. -/
theorem solow_income_long_run (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {k y A : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, (1 + γ) * (1 + n) * k (t + 1) = (1 - δ) * k t + s * intensive F (k t))
    (hApos : ∀ t, 0 < A t) (hy : ∀ t, y t = A t * intensive F (k t)) :
    Tendsto (fun t => y t / A t) atTop
      (𝓝 (intensive F (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) := by
  have hlim := (solow_detrended_convergence hF hs hδ hδ1 hγ hn h0 hk).2.2.2
  have hks := (steady_spec (solow_technology hF) (solow_params_growth hs hδ hδ1 hγ hn)).1
  have e : ∀ t, y t / A t = intensive F (k t) := fun t => by
    rw [hy]; field_simp [ne_of_gt (hApos t)]
  simp only [e]
  exact ((solow_technology hF).differentiable _ hks).continuousAt.tendsto.comp hlim

/-- AKMM, p. 80: on the balanced growth path (`k̃_t = k̃̄` for all `t`) income per capita
`y_t = A_t f(k̃̄)` grows at the rate `γ` of technology, whatever `s`. -/
theorem solow_bgp_income_growth {f : ℝ → ℝ} {γ kbar : ℝ} {k y A : ℕ → ℝ} (hf : 0 < f kbar)
    (hApos : ∀ t, 0 < A t) (hA : ∀ t, A (t + 1) = (1 + γ) * A t) (hbgp : ∀ t, k t = kbar)
    (hy : ∀ t, y t = A t * f (k t)) (t : ℕ) :
    (y (t + 1) - y t) / y t = γ := by
  rw [hy, hy, hbgp, hbgp, hA]
  have := hApos t
  field_simp
  ring

/-- AKMM, p. 80: in general the growth rate of income per capita is
`(y_{t+1} − y_t)/y_t = (1 + γ) f(k̃_{t+1})/f(k̃_t) − 1`. -/
theorem solow_income_growth_identity {f : ℝ → ℝ} {γ : ℝ} {k y A : ℕ → ℝ} {t : ℕ}
    (hf : 0 < f (k t)) (hApos : 0 < A t) (hA : A (t + 1) = (1 + γ) * A t)
    (hy : ∀ t, y t = A t * f (k t)) :
    (y (t + 1) - y t) / y t = f (k (t + 1)) / f (k t) * (1 + γ) - 1 := by
  rw [hy, hy, hA]
  field_simp

/-- AKMM, p. 80: if `k̃₀ < k̃̄` income per capita grows faster than `γ` in every period ("a poor
country grows faster than at rate `γ`"); if `k̃₀ > k̃̄` it grows slower. -/
theorem solow_transition_growth (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {k y A : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, (1 + γ) * (1 + n) * k (t + 1) = (1 - δ) * k t + s * intensive F (k t))
    (hApos : ∀ t, 0 < A t) (hA : ∀ t, A (t + 1) = (1 + γ) * A t)
    (hy : ∀ t, y t = A t * intensive F (k t)) :
    (k 0 < steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) →
        ∀ t, γ < (y (t + 1) - y t) / y t) ∧
      (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) < k 0 →
        ∀ t, (y (t + 1) - y t) / y t < γ) := by
  obtain ⟨hpos, hlow, hhigh, _⟩ := solow_detrended_convergence hF hs hδ hδ1 hγ hn h0 hk
  have hmono := solow_intensive_strictMono hF
  have hfpos : ∀ t, 0 < intensive F (k t) := fun t => solow_intensive_pos hF (hpos t)
  have hg : 0 < 1 + γ := by linarith
  refine ⟨fun hlt t => ?_, fun hgt t => ?_⟩
  · rw [solow_income_growth_identity (hfpos t) (hApos t) (hA t) hy]
    have h1 := hmono (Set.mem_Ici.mpr (hpos t).le) (Set.mem_Ici.mpr (hpos (t + 1)).le)
      ((hlow hlt).1 (Nat.lt_succ_self t))
    have h2 : 1 < intensive F (k (t + 1)) / intensive F (k t) := (one_lt_div (hfpos t)).mpr h1
    nlinarith
  · rw [solow_income_growth_identity (hfpos t) (hApos t) (hA t) hy]
    have h1 := hmono (Set.mem_Ici.mpr (hpos (t + 1)).le) (Set.mem_Ici.mpr (hpos t).le)
      ((hhigh hgt).1 (Nat.lt_succ_self t))
    have h2 : intensive F (k (t + 1)) / intensive F (k t) < 1 := (div_lt_one (hfpos t)).mpr h1
    nlinarith

/-- AKMM, p. 80: the growth rate of income per capita converges to `γ`; saving affects the
level, not the long-run growth rate. -/
theorem solow_income_growth_tendsto (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {k y A : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, (1 + γ) * (1 + n) * k (t + 1) = (1 - δ) * k t + s * intensive F (k t))
    (hApos : ∀ t, 0 < A t) (hA : ∀ t, A (t + 1) = (1 + γ) * A t)
    (hy : ∀ t, y t = A t * intensive F (k t)) :
    Tendsto (fun t => (y (t + 1) - y t) / y t) atTop (𝓝 γ) := by
  obtain ⟨hpos, _, _, hlim⟩ := solow_detrended_convergence hF hs hδ hδ1 hγ hn h0 hk
  have hks := (steady_spec (solow_technology hF) (solow_params_growth hs hδ hδ1 hγ hn)).1
  have hc := ((solow_technology hF).differentiable _ hks).continuousAt.tendsto.comp hlim
  have hc1 := hc.comp (tendsto_add_atTop_nat 1)
  have hne := ne_of_gt ((solow_technology hF).output_pos hks)
  have e : ∀ t, (y (t + 1) - y t) / y t =
      intensive F (k (t + 1)) / intensive F (k t) * (1 + γ) - 1 := fun t =>
    solow_income_growth_identity (solow_intensive_pos hF (hpos t)) (hApos t) (hA t) hy
  simp only [e]
  have := ((hc1.div hc hne).mul_const (1 + γ)).sub_const 1
  rw [div_self hne, one_mul, add_sub_cancel_left] at this
  exact this

/-- AKMM, §3.3, p. 81: the competitive rental rate, the marginal product of capital
`r = F₁(K, AL)`, equals `f'(k̃)` with `k̃ = K/(AL)` (differentiate `F(K, E) = E f(K/E)` in `K`). -/
theorem solow_rental_rate (hF : SolowAssumptions F) {K E : ℝ} (hK : 0 < K) (hE : 0 < E) :
    HasDerivAt (fun K' => F K' E) (deriv (intensive F) (K / E)) K := by
  have hf := (hF.differentiable 1 (K / E) one_pos (div_pos hK hE)).hasDerivAt
  have h2 := (hf.comp K ((hasDerivAt_id K).div_const E)).const_mul E
  have h3 : HasDerivAt (fun K' => E * intensive F (K' / E)) (deriv (intensive F) (K / E)) K := by
    convert h2 using 1
    · rfl
    change deriv (fun K => F K 1) (K / E) = _
    field_simp
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hK] with K' hK'
  exact solow_intensive_form hF (le_of_lt hK') hE

/-- AKMM, §3.3, p. 81: the wage per efficiency unit, the marginal product of effective labour
`w = F₂(K, AL)`, equals `f(k̃) − k̃ f'(k̃)` (EconomicGrowth's `wage`); differentiate
`F(K, E) = E f(K/E)` in `E`. -/
theorem solow_wage_rate (hF : SolowAssumptions F) {K E : ℝ} (hK : 0 < K) (hE : 0 < E) :
    HasDerivAt (fun E' => F K E') (wage (intensive F) (K / E)) E := by
  have hf := (hF.differentiable 1 (K / E) one_pos (div_pos hK hE)).hasDerivAt
  have hq : HasDerivAt (fun y => K / y) (-(K / E ^ 2)) E := by
    have := (hasDerivAt_inv (ne_of_gt hE)).const_mul K
    convert this using 1
    · funext y; ring
    · ring
  have h2 := (hasDerivAt_id E).mul (hf.comp E hq)
  have h3 : HasDerivAt (fun E' => E' * intensive F (K / E')) (wage (intensive F) (K / E)) E := by
    convert h2 using 1
    · rfl
    unfold wage intensive
    simp only [id, Function.comp_apply]
    field_simp
    ring
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hE] with E' hE'
  exact solow_intensive_form hF hK.le hE'

/-- AKMM, §3.3 and footnote 5, p. 81: Euler's theorem for the degree-one homogeneous `F`,
`Y = K F₁(K, AL) + AL F₂(K, AL)`; output is exhausted by factor payments. -/
theorem solow_euler (hF : SolowAssumptions F) {K E : ℝ} (hK : 0 < K) (hE : 0 < E) :
    F K E = K * deriv (fun K' => F K' E) K + E * deriv (fun E' => F K E') E := by
  rw [(solow_rental_rate hF hK hE).deriv, (solow_wage_rate hF hK hE).deriv,
    solow_intensive_form hF hK.le hE]
  unfold wage
  field_simp
  ring

/-- AKMM, §3.3, p. 81: the capital share is `rK/Y = k̃ f'(k̃)/f(k̃)`, the labour share is
`wAL/Y = 1 − rK/Y`, and `AL/Y = 1/f(k̃)`. -/
theorem solow_factor_shares (hF : SolowAssumptions F) {K E : ℝ} (hK : 0 < K) (hE : 0 < E) :
    deriv (fun K' => F K' E) K * K / F K E =
        K / E * deriv (intensive F) (K / E) / intensive F (K / E) ∧
      deriv (fun E' => F K E') E * E / F K E =
        1 - deriv (fun K' => F K' E) K * K / F K E ∧
      E / F K E = 1 / intensive F (K / E) := by
  have hf := solow_intensive_pos hF (div_pos hK hE)
  have hY : 0 < F K E := by rw [solow_intensive_form hF hK.le hE]; positivity
  have heu := solow_euler hF hK hE
  rw [(solow_rental_rate hF hK hE).deriv] at heu ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [solow_intensive_form hF hK.le hE]; field_simp
  · rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq (ne_of_gt hY)]
    linarith
  · rw [solow_intensive_form hF hK.le hE]; field_simp

/-- AKMM, §3.3, pp. 80–81: on the balanced growth path (`k̃_t = k̃̄`), the rental rate
`r_t = f'(k̃̄)`, the wage per efficiency unit `w_t`, the capital–output ratio and the capital share
are the same in every period. -/
theorem solow_factor_prices_bgp {f : ℝ → ℝ} {kbar : ℝ} {k : ℕ → ℝ} (hbgp : ∀ t, k t = kbar)
    (t : ℕ) :
    deriv f (k t) = deriv f kbar ∧ wage f (k t) = wage f kbar ∧ k t / f (k t) = kbar / f kbar ∧
      k t * deriv f (k t) / f (k t) = kbar * deriv f kbar / f kbar := by
  rw [hbgp t]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- AKMM, §3.3, p. 81: along every path of (3.7) the rental rate `f'(k̃_t)`, the wage
`f(k̃_t) − k̃_t f'(k̃_t)` and the capital share converge to their balanced-growth values. -/
theorem solow_factor_prices_tendsto (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) {k : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, (1 + γ) * (1 + n) * k (t + 1) = (1 - δ) * k t + s * intensive F (k t)) :
    Tendsto (fun t => deriv (intensive F) (k t)) atTop
        (𝓝 (deriv (intensive F) (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) ∧
      Tendsto (fun t => wage (intensive F) (k t)) atTop
        (𝓝 (wage (intensive F) (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) ∧
      Tendsto (fun t => k t * deriv (intensive F) (k t) / intensive F (k t)) atTop
        (𝓝 (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)) *
          deriv (intensive F) (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))) /
            intensive F (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))) := by
  have h := solow_technology hF
  obtain ⟨hpos, _, _, hlim⟩ := solow_detrended_convergence hF hs hδ hδ1 hγ hn h0 hk
  have hks := (steady_spec h (solow_params_growth hs hδ hδ1 hγ hn)).1
  have hev : ∀ᶠ t in atTop, k t ∈ Set.Ioi (0 : ℝ) := Eventually.of_forall hpos
  have hr : Tendsto (fun t => deriv (intensive F) (k t)) atTop
      (𝓝 (deriv (intensive F) (steady h s δ ((1 + γ) * (1 + n))))) :=
    ((h.derivative_continuous _ hks).tendsto).comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, hev⟩)
  have hy := (h.differentiable _ hks).continuousAt.tendsto.comp hlim
  refine ⟨hr, ?_, ?_⟩
  · unfold wage
    exact hy.sub (hlim.mul hr)
  · exact (hlim.mul hr).div hy (ne_of_gt (h.output_pos hks))

/-- AKMM, §3.3, p. 81: for `F(K, AL) = K^α (AL)^{1−α}` the capital share is `α` and the labour
share is `1 − α` at every `(K, AL)`, on or off the balanced growth path. -/
theorem solow_cobbDouglas_shares {α K E : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hE : 0 < E) :
    deriv (fun K' => K' ^ α * E ^ (1 - α)) K * K / (K ^ α * E ^ (1 - α)) = α ∧
      deriv (fun E' => K ^ α * E' ^ (1 - α)) E * E / (K ^ α * E ^ (1 - α)) = 1 - α := by
  have hF := solow_cobbDouglas_assumptions hα hα1
  obtain ⟨h1, h2, _⟩ := solow_factor_shares hF hK hE
  have hk : 0 < K / E := div_pos hK hE
  have hd : deriv (intensive (fun K L => K ^ α * L ^ (1 - α))) (K / E) =
      α * (K / E) ^ (α - 1) := by
    rw [solow_intensive_cobbDouglas]
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hk))).deriv
  have hcap : deriv (fun K' => K' ^ α * E ^ (1 - α)) K * K / (K ^ α * E ^ (1 - α)) = α := by
    have := h1
    beta_reduce at this
    rw [this, hd, solow_intensive_cobbDouglas, Real.rpow_sub_one (ne_of_gt hk)]
    have : 0 < (K / E) ^ α := Real.rpow_pos_of_pos hk α
    field_simp
  refine ⟨hcap, ?_⟩
  have := h2
  beta_reduce at this
  rw [this, hcap]

end AKMM.Solow
