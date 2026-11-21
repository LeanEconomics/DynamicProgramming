/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCompetitiveEquilibrium.LabourAD
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Arrow–Debreu equilibrium of the neoclassical growth economy

AKMM, §5.2.3, pp. 139–142. Output `Yₜ = AₜKₜ^αLₜ^{1−α}` (5.11); households own capital,
`k_{i,t+1} = (1 − δ)k_{i,t} + ι_{i,t}` (5.13), and face the date-0 budget (5.14); the firm rents
capital and labour (5.12).

* The firm: the marginal-product conditions `rₜ = αAₜKₜ^{α−1}Lₜ^{1−α}`,
  `wₜ = (1 − α)AₜKₜ^αLₜ^{−α}` are necessary for an interior optimum (`growth_firm_foc`), and
  sufficient, with zero profit (`growth_firm_optimal`, by the weighted AM–GM inequality); the
  capital–labour ratio is pinned down (`growth_firm_ratio`).
* The household (Definition 4, `GrowthOptimal`): (5.15), (5.16) and the no-arbitrage condition
  (5.17) are necessary (`eq_5_15`, `eq_5_16`, `eq_5_17`).
* The consolidated budget `Σ pₜc_{i,t} = Σ pₜwₜeᵢℓ_{i,t} + (1 − δ + r₀)k_{i,0}` holds iff
  `p_Tk_{T+1} → 0` (`growth_consolidated_budget`); the book uses it without this condition. When
  the rental share of the gross return is bounded below, every budget-feasible plan has
  `p_Tk_{T+1} → 0` (`growth_capital_value_tendsto_zero`), and then (5.15)–(5.17) are sufficient
  (`growth_foc_sufficient`); a concrete optimal plan (`growth_optimal_instance`).
* Log utility with `k_{i,0} = eᵢK₀` and common hours: `c_{i,t} = eᵢβᵗ(1 − β)W/pₜ`
  (`growth_log_consumption`), so `θᵢ = eᵢ` (fn. 6, `growth_fn6`) and the hours condition does
  not depend on `i` (`growth_log_hours_common`).
* The aggregate system: the aggregate Euler equation (`growth_log_aggregate_euler`), (5.18),
  (5.19), (5.20) (`eq_5_18`, `eq_5_19`, `eq_5_20`); fn. 7, `δ = 1`: saving rate `αβ` and
  `v′(L)L = (1 − α)/(1 − αβ)` (`growth_fn7`).
* The planner (p. 142): the first-order conditions of `Σ βᵗ[log Cₜ − v(Lₜ)]` with respect to
  `K_{t+1}` and `Lₜ` are exactly (5.18) and (5.19) (`growth_planner_foc_K`,
  `growth_planner_foc_L`).

Departures: the household chooses the capital path `k` (with `k₀` given) rather than investment
`ι`, which (5.13) determines one-to-one; consumption positive, hours nonnegative; the values of
consumption, investment, capital income and labour income converge separately, and the utility
series converge.
-/

namespace AKMM.CompetitiveEquilibrium

open MeasureTheory Filter Topology

variable {I : Type*} [MeasurableSpace I]

/-! ### The firm -/

/-- The Cobb–Douglas firm's profit `AK^αL^{1−α} − rK − wL` (AKMM, (5.12), p. 139). -/
noncomputable def cdProfit (A α r w K L : ℝ) : ℝ := A * K ^ α * L ^ (1 - α) - r * K - w * L

/-- **AKMM, p. 141: the firm's first-order conditions are necessary.** If `(K, L)` with
`K, L > 0` maximizes the profit over positive inputs, then `r = αAK^{α−1}L^{1−α}` and
`w = (1 − α)AK^αL^{−α}`. -/
theorem growth_firm_foc {A α r w K L : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hmax : ∀ K' L', 0 < K' → 0 < L' → cdProfit A α r w K' L' ≤ cdProfit A α r w K L) :
    r = α * A * K ^ (α - 1) * L ^ (1 - α) ∧ w = (1 - α) * A * K ^ α * L ^ (-α) := by
  constructor
  · have hloc : IsLocalMax (fun K' => cdProfit A α r w K' L) K := by
      filter_upwards [lt_mem_nhds hK] with K' hK' using hmax K' L hK' hL
    have hd : HasDerivAt (fun K' => cdProfit A α r w K' L)
        (A * (α * K ^ (α - 1)) * L ^ (1 - α) - r * 1) K := by
      have h := ((((Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul A).mul_const
        (L ^ (1 - α))).sub ((hasDerivAt_id K).const_mul r)).sub_const (w * L)
      unfold cdProfit
      convert h using 1
      funext x; simp
    have := hloc.hasDerivAt_eq_zero hd
    linarith
  · have hloc : IsLocalMax (fun L' => cdProfit A α r w K L') L := by
      filter_upwards [lt_mem_nhds hL] with L' hL' using hmax K L' hK hL'
    have hd : HasDerivAt (fun L' => cdProfit A α r w K L')
        (A * K ^ α * ((1 - α) * L ^ (1 - α - 1)) - w * 1) L := by
      have h := (((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hL.ne')).const_mul
        (A * K ^ α)).sub_const (r * K)).sub ((hasDerivAt_id L).const_mul w)
      unfold cdProfit
      convert h using 1
      funext x; simp
    have := hloc.hasDerivAt_eq_zero hd
    have e : (1 : ℝ) - α - 1 = -α := by ring
    rw [e] at this
    linarith

/-- **AKMM, p. 141: the marginal-product prices make `(K, L)` optimal with zero profit.** For
`0 ≤ α ≤ 1`, `A ≥ 0` and `K, L > 0`, at `r = αAK^{α−1}L^{1−α}`, `w = (1 − α)AK^αL^{−α}` every
`(K', L') ≥ 0` earns at most the profit `0` earned at `(K, L)`: the firm is indifferent to its
scale. -/
theorem growth_firm_optimal {A α K L : ℝ} (hA : 0 ≤ A) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hK : 0 < K)
    (hL : 0 < L) :
    cdProfit A α (α * A * K ^ (α - 1) * L ^ (1 - α)) ((1 - α) * A * K ^ α * L ^ (-α)) K L = 0 ∧
      ∀ K' L', 0 ≤ K' → 0 ≤ L' →
        cdProfit A α (α * A * K ^ (α - 1) * L ^ (1 - α)) ((1 - α) * A * K ^ α * L ^ (-α)) K' L'
          ≤ 0 := by
  have hKa : K ^ (α - 1) = K ^ α / K := Real.rpow_sub_one hK.ne' α
  have hLa : L ^ (-α) = L ^ (1 - α) / L := by
    rw [show -α = (1 - α) - 1 by ring, Real.rpow_sub_one hL.ne']
  have hKpos := Real.rpow_pos_of_pos hK α
  have hLpos := Real.rpow_pos_of_pos hL (1 - α)
  constructor
  · unfold cdProfit; rw [hKa, hLa]; field_simp; ring
  intro K' L' hK' hL'
  have amgm := Real.geom_mean_le_arith_mean2_weighted hα0 (by linarith : 0 ≤ 1 - α)
    (div_nonneg hK' hK.le) (div_nonneg hL' hL.le) (by ring)
  rw [Real.div_rpow hK' hK.le, Real.div_rpow hL' hL.le] at amgm
  have key : K' ^ α * L' ^ (1 - α) ≤ K ^ α * L ^ (1 - α) * (α * (K' / K) + (1 - α) * (L' / L)) := by
    have h := mul_le_mul_of_nonneg_left amgm (mul_pos hKpos hLpos).le
    have e : K ^ α * L ^ (1 - α) * (K' ^ α / K ^ α * (L' ^ (1 - α) / L ^ (1 - α))) =
        K' ^ α * L' ^ (1 - α) := by field_simp
    linarith
  unfold cdProfit
  rw [hKa, hLa]
  have h2 := mul_le_mul_of_nonneg_left key hA
  have e : A * (K ^ α * L ^ (1 - α) * (α * (K' / K) + (1 - α) * (L' / L))) =
      α * A * (K ^ α / K) * L ^ (1 - α) * K' + (1 - α) * A * K ^ α * (L ^ (1 - α) / L) * L' := by
    field_simp
  nlinarith

/-- **AKMM, p. 141: the capital–labour ratio is pinned down.** For `0 < α < 1` and `A > 0`, any
two interior optima at the same rental rate have the same capital–labour ratio. -/
theorem growth_firm_ratio {A α r K₁ L₁ K₂ L₂ : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hK₁ : 0 < K₁) (hL₁ : 0 < L₁) (hK₂ : 0 < K₂) (hL₂ : 0 < L₂)
    (h₁ : r = α * A * K₁ ^ (α - 1) * L₁ ^ (1 - α)) (h₂ : r = α * A * K₂ ^ (α - 1) * L₂ ^ (1 - α)) :
    K₁ / L₁ = K₂ / L₂ := by
  have hr : ∀ K L : ℝ, 0 < K → 0 < L → K ^ (α - 1) * L ^ (1 - α) = (K / L) ^ (α - 1) := by
    intro K L hK hL
    rw [Real.div_rpow hK.le hL.le, show 1 - α = -(α - 1) by ring, Real.rpow_neg hL.le]
    field_simp
  have e : (K₁ / L₁) ^ (α - 1) = (K₂ / L₂) ^ (α - 1) := by
    rw [← hr K₁ L₁ hK₁ hL₁, ← hr K₂ L₂ hK₂ hL₂]
    have : α * A ≠ 0 := (mul_pos hα0 hA).ne'
    apply mul_left_cancel₀ this
    linarith
  have hne : α - 1 ≠ 0 := by linarith
  have := congrArg (fun x => x ^ (α - 1)⁻¹) e
  rwa [Real.rpow_rpow_inv (div_pos hK₁ hL₁).le hne,
    Real.rpow_rpow_inv (div_pos hK₂ hL₂).le hne] at this

/-! ### The household -/

/-- AKMM, (5.13)–(5.14), p. 139: the household budget set. The plan is consumption `c > 0`,
hours `ℓ ≥ 0` and capital `k` with `k₀` given; investment is `ιₜ = k_{t+1} − (1 − δ)kₜ`; the
values of consumption, investment, capital income and labour income converge, and
`Σ pₜ(cₜ + ιₜ) = Σ pₜ(rₜkₜ + wₜeℓₜ)`. -/
def GrowthBudget (p r w : ℕ → ℝ) (δ e k0 : ℝ) (c k l : ℕ → ℝ) : Prop :=
  (∀ t, 0 < c t) ∧ (∀ t, 0 ≤ l t) ∧ k 0 = k0 ∧ Summable (fun t => p t * c t) ∧
    Summable (fun t => p t * (k (t + 1) - (1 - δ) * k t)) ∧
    Summable (fun t => p t * (r t * k t)) ∧ Summable (fun t => p t * w t * e * l t) ∧
    ∑' t, p t * (c t + (k (t + 1) - (1 - δ) * k t)) = ∑' t, p t * (r t * k t + w t * e * l t)

/-- **AKMM, Definition 4, part 1, p. 140.** The household's plan maximizes
`Σ βᵗ[u(cₜ) − v(ℓₜ)]` over the budget set, among plans with a convergent utility series. -/
def GrowthOptimal (u v : ℝ → ℝ) (β : ℝ) (p r w : ℕ → ℝ) (δ e k0 : ℝ) (c k l : ℕ → ℝ) : Prop :=
  GrowthBudget p r w δ e k0 c k l ∧ Summable (fun t => β ^ t * (u (c t) - v (l t))) ∧
    ∀ x kk m, GrowthBudget p r w δ e k0 x kk m →
      Summable (fun t => β ^ t * (u (x t) - v (m t))) →
        ∑' t, β ^ t * (u (x t) - v (m t)) ≤ ∑' t, β ^ t * (u (c t) - v (l t))

/-- **AKMM, (5.15), p. 140.** At an optimum with positive prices,
`βˢu′(c_s)pₜ = βᵗu′(cₜ)p_s`: one multiplier `λᵢ` with `βᵗu′(c_{i,t}) = λᵢpₜ`. -/
theorem eq_5_15 {u v : ℝ → ℝ} {β δ e k0 : ℝ} {p r w c k l du : ℕ → ℝ}
    (hopt : GrowthOptimal u v β p r w δ e k0 c k l) (hp : ∀ t, 0 < p t)
    (hd : ∀ t, HasDerivAt u (du t) (c t)) (s t : ℕ) :
    β ^ s * du s * p t = β ^ t * du t * p s := by
  rcases eq_or_ne s t with rfl | hst
  · ring
  obtain ⟨⟨hpos, hl, hk0, hc, hι, hrk, hwl, hW⟩, husum, hmax⟩ := hopt
  have hsum : Summable (fun t => p t * (c t + (k (t + 1) - (1 - δ) * k t))) :=
    (hc.add hι).congr fun t => by ring
  set q := p s / p t with hq
  let x : ℝ → ℕ → ℝ := fun ε n =>
    if n = s then c s + ε else if n = t then c t - q * ε else c n
  have hxs : ∀ ε, x ε s = c s + ε := fun ε => by simp [x]
  have hxt : ∀ ε, x ε t = c t - q * ε := fun ε => by simp [x, hst.symm]
  have hxo : ∀ ε, ∀ n ∉ ({s, t} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [x, hn.1, hn.2]
  have hpt := hp t
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c s + ε ∧ 0 < c t - q * ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c s + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hpos s)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - q * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos t)
    exact h1.and h2
  have hd' : HasDerivAt (fun ε => ∑ n ∈ ({s, t} : Finset ℕ), β ^ n * (u (x ε n) - v (l n)))
      (β ^ s * du s + β ^ t * (du t * (-q))) 0 := by
    have e : (fun ε => ∑ n ∈ ({s, t} : Finset ℕ), β ^ n * (u (x ε n) - v (l n))) =
        fun ε => β ^ s * u (c s + ε) + β ^ t * u (c t - q * ε) -
          (β ^ s * v (l s) + β ^ t * v (l t)) := by
      funext ε; rw [Finset.sum_pair hst, hxs, hxt]; ring
    rw [e]
    have h1 : HasDerivAt (fun ε => u (c s + ε)) (du s) 0 := by
      have hu : HasDerivAt u (du s) (c s + 0) := by simpa using hd s
      simpa using hu.comp_const_add (c s) 0
    have h2 : HasDerivAt (fun ε => u (c t - q * ε)) (du t * (-q)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t - q * ε) (-q) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_sub (c t)
      have hu : HasDerivAt u (du t) (c t - q * 0) := by simpa using hd t
      exact hu.comp 0 hin
    exact ((h1.const_mul _).add (h2.const_mul _)).sub_const _
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * (u (c n) - v (l n)))
    (g := fun ε n => β ^ n * (u (x ε n) - v (l n))) {s, t} husum
    (fun ε n hn => by simp only [hxo ε n hn]) (fun n => by simp [x]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      have hP := ce_tsum_perturb (f := fun n => p n * (c n + (k (n + 1) - (1 - δ) * k n)))
        (g := fun n => p n * (x ε n + (k (n + 1) - (1 - δ) * k n))) {s, t}
        (fun n hn => by simp only [hxo ε n hn]) hsum
      have hPc := ce_tsum_perturb (f := fun n => p n * c n) (g := fun n => p n * x ε n) {s, t}
        (fun n hn => by simp only [hxo ε n hn]) hc
      refine hmax (x ε) k l ⟨fun n => ?_, hl, hk0, hPc.1, hι, hrk, hwl, ?_⟩ hU
      · by_cases h1 : n = s
        · subst h1; rw [hxs]; exact hε.1
        by_cases h2 : n = t
        · subst h2; rw [hxt]; exact hε.2
        simp only [x, h1, h2, ite_false]; exact hpos n
      · have hz : p s * (x ε s + (k (s + 1) - (1 - δ) * k s)) -
            p s * (c s + (k (s + 1) - (1 - δ) * k s)) +
            (p t * (x ε t + (k (t + 1) - (1 - δ) * k t)) -
              p t * (c t + (k (t + 1) - (1 - δ) * k t))) = 0 := by
          rw [hxs, hxt, hq]; field_simp; ring
        rw [hP.2, Finset.sum_pair hst, hz, add_zero, hW]) hd'
  rw [hq] at hzero
  field_simp at hzero
  linarith

/-- **AKMM, (5.16), p. 140.** At an optimum with `β > 0` and positive hours,
`v′(ℓₜ) = ewₜu′(cₜ)`. -/
theorem eq_5_16 {u v : ℝ → ℝ} {β δ e k0 : ℝ} {p r w c k l : ℕ → ℝ} {du dv : ℝ} {t : ℕ}
    (hopt : GrowthOptimal u v β p r w δ e k0 c k l) (hβ : 0 < β) (hlt : 0 < l t)
    (hdu : HasDerivAt u du (c t)) (hdv : HasDerivAt v dv (l t)) : dv = e * w t * du := by
  obtain ⟨⟨hpos, hl, hk0, hc, hι, hrk, hwl, hW⟩, husum, hmax⟩ := hopt
  have hsum : Summable (fun t => p t * (c t + (k (t + 1) - (1 - δ) * k t))) :=
    (hc.add hι).congr fun t => by ring
  have hsumR : Summable (fun t => p t * (r t * k t + w t * e * l t)) :=
    (hrk.add hwl).congr fun t => by ring
  set q := e * w t with hq
  let x : ℝ → ℕ → ℝ := fun ε n => if n = t then c t + q * ε else c n
  let m : ℝ → ℕ → ℝ := fun ε n => if n = t then l t + ε else l n
  have hxo : ∀ ε, ∀ n ∉ ({t} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_singleton] at hn; simp [x, hn]
  have hmo : ∀ ε, ∀ n ∉ ({t} : Finset ℕ), m ε n = l n := fun ε n hn => by
    simp only [Finset.mem_singleton] at hn; simp [m, hn]
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t + q * ε ∧ 0 < l t + ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t + q * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos t)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < l t + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hlt)
    exact h1.and h2
  have hd' : HasDerivAt (fun ε => ∑ n ∈ ({t} : Finset ℕ), β ^ n * (u (x ε n) - v (m ε n)))
      (β ^ t * (du * q - dv)) 0 := by
    have e1 : (fun ε => ∑ n ∈ ({t} : Finset ℕ), β ^ n * (u (x ε n) - v (m ε n))) =
        fun ε => β ^ t * (u (c t + q * ε) - v (l t + ε)) := by
      funext ε; simp [x, m]
    rw [e1]
    have h1 : HasDerivAt (fun ε => u (c t + q * ε)) (du * q) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t + q * ε) q 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_add (c t)
      have hu : HasDerivAt u du (c t + q * 0) := by simpa using hdu
      exact hu.comp 0 hin
    have h2 : HasDerivAt (fun ε => v (l t + ε)) dv 0 := by
      have hv : HasDerivAt v dv (l t + 0) := by simpa using hdv
      simpa using hv.comp_const_add (l t) 0
    exact (h1.sub h2).const_mul _
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * (u (c n) - v (l n)))
    (g := fun ε n => β ^ n * (u (x ε n) - v (m ε n))) {t} husum
    (fun ε n hn => by simp only [hxo ε n hn, hmo ε n hn])
    (fun n => by simp only [x, m]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      have hS1 := ce_tsum_perturb (f := fun n => p n * (c n + (k (n + 1) - (1 - δ) * k n)))
        (g := fun n => p n * (x ε n + (k (n + 1) - (1 - δ) * k n))) {t}
        (fun n hn => by simp only [hxo ε n hn]) hsum
      have hS2 := ce_tsum_perturb (f := fun n => p n * (r n * k n + w n * e * l n))
        (g := fun n => p n * (r n * k n + w n * e * m ε n)) {t}
        (fun n hn => by simp only [hmo ε n hn]) hsumR
      have hPc := ce_tsum_perturb (f := fun n => p n * c n) (g := fun n => p n * x ε n) {t}
        (fun n hn => by simp only [hxo ε n hn]) hc
      have hPw := ce_tsum_perturb (f := fun n => p n * w n * e * l n)
        (g := fun n => p n * w n * e * m ε n) {t} (fun n hn => by simp only [hmo ε n hn]) hwl
      refine hmax (x ε) k (m ε)
        ⟨fun n => ?_, fun n => ?_, hk0, hPc.1, hι, hrk, hPw.1, ?_⟩ hU
      · by_cases h1 : n = t
        · subst h1; simp only [x, ite_true]; exact hε.1
        simp only [x, h1, ite_false]; exact hpos n
      · by_cases h1 : n = t
        · subst h1; simp only [m, ite_true]; exact hε.2.le
        simp only [m, h1, ite_false]; exact hl n
      · rw [hS1.2, hS2.2, hW, Finset.sum_singleton, Finset.sum_singleton]
        simp only [x, m, ite_true, hq]
        ring) hd'
  have := (pow_pos hβ t).ne'
  have h2 : du * q - dv = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd h this
    · exact h
  rw [hq] at h2
  linarith

/-- **AKMM, (5.17), p. 140: no arbitrage.** At an optimum with `β > 0`, positive prices and
`u′(cₜ) ≠ 0`, `pₜ = p_{t+1}r_{t+1} + (1 − δ)p_{t+1}`. Proved by investing `ε` more at `t` and
consuming its gross return `1 − δ + r_{t+1}` at `t + 1`. -/
theorem eq_5_17 {u v : ℝ → ℝ} {β δ e k0 : ℝ} {p r w c k l du : ℕ → ℝ}
    (hopt : GrowthOptimal u v β p r w δ e k0 c k l) (hβ : 0 < β) (hp : ∀ t, 0 < p t)
    (hd : ∀ t, HasDerivAt u (du t) (c t)) (t : ℕ) (hdt : du t ≠ 0) :
    p t = p (t + 1) * r (t + 1) + (1 - δ) * p (t + 1) := by
  have h515 := eq_5_15 hopt hp hd t (t + 1)
  obtain ⟨⟨hpos, hl, hk0, hc, hι, hrk, hwl, hW⟩, husum, hmax⟩ := hopt
  have hsum : Summable (fun t => p t * (c t + (k (t + 1) - (1 - δ) * k t))) :=
    (hc.add hι).congr fun t => by ring
  have hsumR : Summable (fun t => p t * (r t * k t + w t * e * l t)) :=
    (hrk.add hwl).congr fun t => by ring
  set R := 1 - δ + r (t + 1) with hR
  have htt : t + 1 ≠ t := by omega
  let x : ℝ → ℕ → ℝ := fun ε n =>
    if n = t then c t - ε else if n = t + 1 then c (t + 1) + R * ε else c n
  let kk : ℝ → ℕ → ℝ := fun ε n => if n = t + 1 then k (t + 1) + ε else k n
  have hxt : ∀ ε, x ε t = c t - ε := fun ε => by simp [x]
  have hxt1 : ∀ ε, x ε (t + 1) = c (t + 1) + R * ε := fun ε => by simp [x]
  have hxo : ∀ ε, ∀ n ∉ ({t, t + 1} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [x, hn.1, hn.2]
  have hkt1 : ∀ ε, kk ε (t + 1) = k (t + 1) + ε := fun ε => by simp [kk]
  have hko : ∀ ε n, n ≠ t + 1 → kk ε n = k n := fun ε n hn => by simp [kk, hn]
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - ε ∧ 0 < c (t + 1) + R * ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - ε :=
      continuousAt_const.eventually_lt (continuous_const.sub continuous_id).continuousAt
        (by simpa using hpos t)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c (t + 1) + R * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos (t + 1))
    exact h1.and h2
  have hd' : HasDerivAt
      (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), β ^ n * (u (x ε n) - v (l n)))
      (β ^ t * (du t * (-1)) + β ^ (t + 1) * (du (t + 1) * R)) 0 := by
    have e : (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), β ^ n * (u (x ε n) - v (l n))) =
        fun ε => β ^ t * u (c t - ε) + β ^ (t + 1) * u (c (t + 1) + R * ε) -
          (β ^ t * v (l t) + β ^ (t + 1) * v (l (t + 1))) := by
      funext ε; rw [Finset.sum_pair htt.symm, hxt, hxt1]; ring
    rw [e]
    have h1 : HasDerivAt (fun ε => u (c t - ε)) (du t * (-1)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t - ε) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_sub (c t)
      have hu : HasDerivAt u (du t) (c t - 0) := by simpa using hd t
      exact hu.comp 0 hin
    have h2 : HasDerivAt (fun ε => u (c (t + 1) + R * ε)) (du (t + 1) * R) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c (t + 1) + R * ε) R 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul R).const_add (c (t + 1))
      have hu : HasDerivAt u (du (t + 1)) (c (t + 1) + R * 0) := by simpa using hd (t + 1)
      exact hu.comp 0 hin
    exact ((h1.const_mul _).add (h2.const_mul _)).sub_const _
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * (u (c n) - v (l n)))
    (g := fun ε n => β ^ n * (u (x ε n) - v (l n))) {t, t + 1} husum
    (fun ε n hn => by simp only [hxo ε n hn]) (fun n => by simp [x]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      -- the budget series change only at `t + 1`, by `p_{t+1}r_{t+1}ε` on each side
      have hLo : ∀ n ∉ ({t + 1} : Finset ℕ),
          p n * (x ε n + (kk ε (n + 1) - (1 - δ) * kk ε n)) =
            p n * (c n + (k (n + 1) - (1 - δ) * k n)) := by
        intro n hn
        simp only [Finset.mem_singleton] at hn
        by_cases hnt : n = t
        · subst hnt
          rw [hxt, hkt1, hko ε n hn]; ring
        · rw [hxo ε n (by simp [hnt, hn]), hko ε n hn, hko ε (n + 1) (by omega)]
      have hRo : ∀ n ∉ ({t + 1} : Finset ℕ),
          p n * (r n * kk ε n + w n * e * l n) = p n * (r n * k n + w n * e * l n) := by
        intro n hn
        simp only [Finset.mem_singleton] at hn
        rw [hko ε n hn]
      have hS1 := ce_tsum_perturb (f := fun n => p n * (c n + (k (n + 1) - (1 - δ) * k n)))
        (g := fun n => p n * (x ε n + (kk ε (n + 1) - (1 - δ) * kk ε n))) {t + 1} hLo hsum
      have hS2 := ce_tsum_perturb (f := fun n => p n * (r n * k n + w n * e * l n))
        (g := fun n => p n * (r n * kk ε n + w n * e * l n)) {t + 1} hRo hsumR
      have hPc := ce_tsum_perturb (f := fun n => p n * c n) (g := fun n => p n * x ε n)
        {t, t + 1} (fun n hn => by simp only [hxo ε n hn]) hc
      have hPι := ce_tsum_perturb (f := fun n => p n * (k (n + 1) - (1 - δ) * k n))
        (g := fun n => p n * (kk ε (n + 1) - (1 - δ) * kk ε n)) {t, t + 1}
        (fun n hn => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
          rw [hko ε n hn.2, hko ε (n + 1) (by omega)]) hι
      have hPr := ce_tsum_perturb (f := fun n => p n * (r n * k n))
        (g := fun n => p n * (r n * kk ε n)) {t + 1}
        (fun n hn => by
          simp only [Finset.mem_singleton] at hn
          rw [hko ε n hn]) hrk
      refine hmax (x ε) (kk ε) l
        ⟨fun n => ?_, hl, by rw [hko ε 0 (by omega), hk0], hPc.1, hPι.1, hPr.1, hwl, ?_⟩ hU
      · by_cases h1 : n = t
        · subst h1; rw [hxt]; exact hε.1
        by_cases h2 : n = t + 1
        · subst h2; rw [hxt1]; exact hε.2
        rw [hxo ε n (by simp [h1, h2])]; exact hpos n
      · rw [hS1.2, hS2.2, hW, Finset.sum_singleton, Finset.sum_singleton, hxt1, hkt1,
          hko ε (t + 1 + 1) (by omega), hR]
        ring) hd'
  -- combine with (5.15)
  have hb := (pow_pos hβ t).ne'
  have hpt := (hp t).ne'
  have hpt1 := (hp (t + 1)).ne'
  rw [pow_succ] at hzero h515
  have h1 : β * du (t + 1) * R = du t := by
    apply mul_left_cancel₀ hb; linarith
  have h2 : β * du (t + 1) * p t = du t * p (t + 1) := by
    apply mul_left_cancel₀ hb; linarith
  have h3 : du t * p (t + 1) * R = du t * p t := by
    rw [← h2, ← h1]; ring
  have h4 : p (t + 1) * R = p t := by
    apply mul_left_cancel₀ hdt; linarith
  rw [hR] at h4
  linarith

/-- **AKMM, p. 141: the consolidated budget.** If the household's budget (5.14) holds and
(5.17) holds at every date, then `Σ pₜcₜ = Σ pₜwₜeℓₜ + (1 − δ + r₀)p₀k₀` iff `p_Tk_{T+1} → 0`.
The book substitutes (5.17) without stating this limit condition. -/
theorem growth_consolidated_budget {δ e k0 : ℝ} {p r w c k l : ℕ → ℝ}
    (hb : GrowthBudget p r w δ e k0 c k l)
    (h517 : ∀ t, p t = p (t + 1) * r (t + 1) + (1 - δ) * p (t + 1)) :
    ∑' t, p t * c t = ∑' t, p t * w t * e * l t + (1 - δ + r 0) * p 0 * k0 ↔
      Tendsto (fun T => p T * k (T + 1)) atTop (𝓝 0) := by
  obtain ⟨_, _, hk0, hc, hι, hrk, hwl, hW⟩ := hb
  set D : ℕ → ℝ := fun t => p t * (k (t + 1) - (1 - δ) * k t) - p t * (r t * k t) with hD
  have hDs : Summable D := hι.sub hrk
  have hW' : ∑' t, p t * c t + ∑' t, p t * (k (t + 1) - (1 - δ) * k t) =
      ∑' t, p t * (r t * k t) + ∑' t, p t * w t * e * l t := by
    rw [← hc.tsum_add hι, ← hrk.tsum_add hwl]
    convert hW using 2 <;> funext t <;> ring
  have hDv : ∑' t, D t = ∑' t, p t * w t * e * l t - ∑' t, p t * c t := by
    rw [hD, hι.tsum_sub hrk]
    linarith
  have hpart : ∀ T, ∑ t ∈ Finset.range (T + 1), D t =
      p T * k (T + 1) - (1 - δ + r 0) * p 0 * k 0 := by
    intro T
    induction T with
    | zero => simp [hD]; ring
    | succ T ih =>
      rw [Finset.sum_range_succ, ih, hD]
      simp only
      rw [h517 T]
      ring
  have hlim : Tendsto (fun T => p T * k (T + 1)) atTop
      (𝓝 (∑' t, D t + (1 - δ + r 0) * p 0 * k 0)) := by
    have h := (hDs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have e : (fun T => p T * k (T + 1)) =
        fun T => (∑ t ∈ Finset.range (T + 1), D t) + (1 - δ + r 0) * p 0 * k 0 := by
      funext T; rw [hpart T]; ring
    rw [e]
    exact h.add_const _
  rw [hk0] at hlim
  constructor
  · intro h
    have : ∑' t, D t + (1 - δ + r 0) * p 0 * k0 = 0 := by rw [hDv, h]; ring
    rwa [this] at hlim
  · intro h
    have := tendsto_nhds_unique hlim h
    rw [hDv] at this
    linarith

/-- **AKMM, fn. 5, p. 140: no Ponzi scheme in the date-0 budget.** If (5.17) holds at every
date, prices are positive, gross returns `1 − δ + rₜ` are positive and the rental share of the
gross return is bounded below, `ε(1 − δ + rₜ) ≤ rₜ` with `ε > 0`, then every plan in the budget
set has `p_Tk_{T+1} → 0`: convergence of the value of capital income rules out Ponzi
schemes. -/
theorem growth_capital_value_tendsto_zero {δ e k0 ε : ℝ} {p r w c k l : ℕ → ℝ}
    (hb : GrowthBudget p r w δ e k0 c k l)
    (h517 : ∀ t, p t = p (t + 1) * r (t + 1) + (1 - δ) * p (t + 1))
    (hR : ∀ t, 0 < 1 - δ + r t) (hε : 0 < ε) (hrate : ∀ t, ε * (1 - δ + r t) ≤ r t) :
    Tendsto (fun T => p T * k (T + 1)) atTop (𝓝 0) := by
  obtain ⟨_, _, _, _, _, hrk, _, _⟩ := hb
  have hz : Tendsto (fun T => p (T + 1) * (r (T + 1) * k (T + 1))) atTop (𝓝 0) :=
    (hrk.tendsto_atTop_zero).comp (tendsto_add_atTop_nat 1)
  have hrpos : ∀ t, 0 < r t := fun t => lt_of_lt_of_le (mul_pos hε (hR t)) (hrate t)
  have hbound : ∀ T, ‖p T * k (T + 1)‖ ≤ ε⁻¹ * ‖p (T + 1) * (r (T + 1) * k (T + 1))‖ := by
    intro T
    have e : p T * k (T + 1) =
        p (T + 1) * (r (T + 1) * k (T + 1)) * ((1 - δ + r (T + 1)) / r (T + 1)) := by
      rw [h517 T]; have := (hrpos (T + 1)).ne'; field_simp; ring
    rw [e, norm_mul]
    have h1 : ‖(1 - δ + r (T + 1)) / r (T + 1)‖ ≤ ε⁻¹ := by
      rw [Real.norm_of_nonneg (div_pos (hR _) (hrpos _)).le, div_le_iff₀ (hrpos _)]
      have := hrate (T + 1)
      rw [inv_mul_eq_div, le_div_iff₀ hε]
      linarith
    calc ‖p (T + 1) * (r (T + 1) * k (T + 1))‖ * ‖(1 - δ + r (T + 1)) / r (T + 1)‖
        ≤ ‖p (T + 1) * (r (T + 1) * k (T + 1))‖ * ε⁻¹ :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := by ring
  refine squeeze_zero_norm hbound ?_
  have := (hz.norm).const_mul ε⁻¹
  simpa using this

/-- **AKMM, p. 140: the first-order conditions are sufficient.** Let `u` lie below and `v` above
their tangents, `β ≥ 0`, `βᵗu′(cₜ) = λpₜ` (5.15), `v′(ℓₜ) = ewₜu′(cₜ)` (5.16), (5.17)
at every date, positive prices and gross returns with `ε(1 − δ + rₜ) ≤ rₜ`, `ε > 0`. Then a
budget-feasible plan with a convergent utility series solves the household's problem. -/
theorem growth_foc_sufficient {u v : ℝ → ℝ} {β δ e k0 lam ε : ℝ} {p r w c k l du dv : ℕ → ℝ}
    (hβ : 0 ≤ β) (hut : ∀ t x, 0 < x → u x ≤ u (c t) + du t * (x - c t))
    (hvt : ∀ t m, 0 ≤ m → v (l t) + dv t * (m - l t) ≤ v m)
    (h515 : ∀ t, β ^ t * du t = lam * p t) (h516 : ∀ t, dv t = e * w t * du t)
    (h517 : ∀ t, p t = p (t + 1) * r (t + 1) + (1 - δ) * p (t + 1))
    (hR : ∀ t, 0 < 1 - δ + r t) (hε : 0 < ε) (hrate : ∀ t, ε * (1 - δ + r t) ≤ r t)
    (hb : GrowthBudget p r w δ e k0 c k l) (hU : Summable (fun t => β ^ t * (u (c t) - v (l t)))) :
    GrowthOptimal u v β p r w δ e k0 c k l := by
  refine ⟨hb, hU, fun x kk m hx hUx => ?_⟩
  have hcb := (growth_consolidated_budget hb h517).2
    (growth_capital_value_tendsto_zero hb h517 hR hε hrate)
  have hxb := (growth_consolidated_budget hx h517).2
    (growth_capital_value_tendsto_zero hx h517 hR hε hrate)
  obtain ⟨_, _, _, hcs, _, _, hcw, _⟩ := hb
  obtain ⟨hxp, hmp, _, hxs, _, _, hxw, _⟩ := hx
  have key : ∀ t, β ^ t * (u (x t) - v (m t)) ≤ β ^ t * (u (c t) - v (l t)) +
      lam * ((p t * x t - p t * c t) - (p t * w t * e * m t - p t * w t * e * l t)) := by
    intro t
    have h1 := hut t (x t) (hxp t)
    have h2 := hvt t (m t) (hmp t)
    have h3 : β ^ t * (u (x t) - v (m t)) ≤
        β ^ t * ((u (c t) + du t * (x t - c t)) - (v (l t) + dv t * (m t - l t))) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hβ t)
    have h4 : β ^ t * ((u (c t) + du t * (x t - c t)) - (v (l t) + dv t * (m t - l t))) =
        β ^ t * (u (c t) - v (l t)) +
          lam * ((p t * x t - p t * c t) - (p t * w t * e * m t - p t * w t * e * l t)) := by
      rw [h516 t]
      have : β ^ t * (du t * (x t - c t) - e * w t * du t * (m t - l t)) =
          (β ^ t * du t) * ((x t - c t) - e * w t * (m t - l t)) := by ring
      linear_combination this + (x t - c t - e * w t * (m t - l t)) * h515 t
    linarith
  have hS2 : Summable (fun t => lam * ((p t * x t - p t * c t) -
      (p t * w t * e * m t - p t * w t * e * l t))) :=
    ((hxs.sub hcs).sub (hxw.sub hcw)).mul_left lam
  have := hUx.tsum_le_tsum key (hU.add hS2)
  rw [hU.tsum_add hS2, tsum_mul_left, ((hxs.sub hcs)).tsum_sub (hxw.sub hcw),
    hxs.tsum_sub hcs, hxw.tsum_sub hcw, hxb, hcb] at this
  linarith

/-- **AKMM, Definition 4: an instance.** With `u = log`, `v(ℓ) = ℓ²/4`, `β = 1/2`, `δ = 1`,
`pₜ = (1/2)ᵗ`, `r = 2`, `w = e = 1` and `k₀ = 1`, the plan `cₜ = 2`, `kₜ = 1`, `ℓₜ = 1` solves
the household's problem. -/
theorem growth_optimal_instance :
    GrowthOptimal Real.log (fun l => l ^ 2 / 4) (1 / 2) (fun t => (1 / 2 : ℝ) ^ t) (fun _ => 2)
      (fun _ => 1) 1 1 1 (fun _ => 2) (fun _ => 1) (fun _ => 1) := by
  have hgeo := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  refine growth_foc_sufficient (du := fun _ => 1 / 2) (dv := fun _ => 1 / 2) (lam := 1 / 2)
    (ε := 1) (by norm_num) (fun t x hx => ?_) (fun t m _ => ?_)
    (fun t => by ring) (fun t => by ring) (fun t => by rw [pow_succ]; ring) (fun t => by norm_num)
    one_pos (fun t => by norm_num) ⟨fun _ => by norm_num, fun _ => by norm_num, rfl, ?_, ?_, ?_,
      ?_, ?_⟩ ?_
  · have := ce_log_tangent (show (0 : ℝ) < 2 by norm_num) hx
    norm_num at this ⊢
    linarith
  · nlinarith [sq_nonneg (m - 1)]
  · exact (hgeo.mul_right 2).congr fun t => by ring
  · exact (hgeo.mul_right 1).congr fun t => by ring
  · exact (hgeo.mul_right 2).congr fun t => by ring
  · exact (hgeo.mul_right 1).congr fun t => by ring
  · congr 1; funext t; ring
  · exact (hgeo.mul_right (Real.log 2 - 1 / 4)).congr fun t => by norm_num

/-- **AKMM, pp. 141–142: log consumption under `k_{i,0} = eᵢK₀` and common hours.** If
`pₜcₜ = βᵗc₀` (the log form of (5.15) with `p₀ = 1`), `0 ≤ β < 1` and the consolidated budget
`Σ pₜcₜ = Σ pₜwₜeℓₜ + (1 − δ + r₀)eK₀` holds with common hours `ℓ`, then
`cₜ = eβᵗ(1 − β)(Σ pₛwₛℓₛ + (1 − δ + r₀)K₀)/pₜ`. -/
theorem growth_log_consumption {β δ e K0 : ℝ} {p r w c l : ℕ → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hp : ∀ t, 0 < p t) (hfoc : ∀ t, p t * c t = β ^ t * c 0)
    (hbud : ∑' t, p t * c t = ∑' t, p t * w t * e * l t + (1 - δ + r 0) * (e * K0)) (t : ℕ) :
    c t = e * (β ^ t * (1 - β) / p t * (∑' s, p s * w s * l s + (1 - δ + r 0) * K0)) := by
  have hL : ∑' t, p t * c t = c 0 * (1 - β)⁻¹ := by
    simp only [hfoc]; rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1, mul_comm]
  have hR : ∑' t, p t * w t * e * l t = e * ∑' t, p t * w t * l t := by
    rw [← tsum_mul_left]; congr 1; funext s; ring
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hc0 : c 0 = e * ((1 - β) * (∑' s, p s * w s * l s + (1 - δ + r 0) * K0)) := by
    rw [hL, hR] at hbud
    field_simp at hbud
    linarith
  have hct : c t = β ^ t * c 0 / p t := by
    have := hfoc t; have := (hp t).ne'; field_simp; linarith
  rw [hct, hc0]
  have := (hp t).ne'
  field_simp

/-- **AKMM, fn. 6, p. 142.** If `c_{i,t} = eᵢXₜ` with `Xₜ` independent of `i` and
`∫ eᵢ di = 1`, then `Cₜ = ∫ c_{i,t} di = Xₜ`: the consumption share is `θᵢ = eᵢ`. -/
theorem growth_fn6 {μ : Measure I} {e : I → ℝ} {c : I → ℕ → ℝ} {X : ℕ → ℝ}
    (he1 : ∫ i, e i ∂μ = 1) (hc : ∀ i t, c i t = e i * X t) (t : ℕ) :
    ∫ i, c i t ∂μ = X t := by
  simp only [hc, integral_mul_const, he1, one_mul]

/-- **AKMM, p. 142: the hours condition does not depend on `i`.** With log utility, (5.16) reads
`v′(ℓ_{i,t}) = eᵢwₜ/c_{i,t}`; under `c_{i,t} = eᵢβᵗ(1 − β)W/pₜ` with `eᵢ, W > 0` the right
side is `wₜpₜ/(βᵗ(1 − β)W)`, the same for every household. -/
theorem growth_log_hours_common {β e W pt wt : ℝ} {t : ℕ} (he : 0 < e) (hβ : 0 < β)
    (hβ1 : β < 1) (hW : 0 < W) (hpt : 0 < pt) :
    e * wt / (e * (β ^ t * (1 - β) / pt * W)) = wt * pt / (β ^ t * (1 - β) * W) := by
  have : (1 : ℝ) - β ≠ 0 := by linarith
  have := (pow_pos hβ t).ne'
  field_simp

/-- **AKMM, p. 141: the aggregate Euler equation.** If every household satisfies the log
first-order condition `pₜc_{i,t} = βᵗc_{i,0}`, then `pₜCₜ = βᵗC₀` for `Cₜ = ∫ c_{i,t} di`, so
`C_{t+1} = βpₜ/p_{t+1}·Cₜ` when `β > 0`. -/
theorem growth_log_aggregate_euler {μ : Measure I} {β : ℝ} {p : ℕ → ℝ} {c : I → ℕ → ℝ}
    (hβ : 0 < β) (hp : ∀ t, 0 < p t) (hfoc : ∀ i t, p t * c i t = β ^ t * c i 0) (t : ℕ) :
    ∫ i, c i (t + 1) ∂μ = β * p t / p (t + 1) * ∫ i, c i t ∂μ := by
  have hagg : ∀ t, p t * ∫ i, c i t ∂μ = β ^ t * ∫ i, c i 0 ∂μ := by
    intro t
    rw [← integral_const_mul, ← integral_const_mul]
    exact congrArg (fun f => ∫ i, f i ∂μ) (funext fun i => hfoc i t)
  have h1 := hagg t
  have h2 := hagg (t + 1)
  have := (hp t).ne'
  have := (hp (t + 1)).ne'
  have := (pow_pos hβ t).ne'
  rw [pow_succ] at h2
  field_simp
  have e : p (t + 1) * ∫ i, c i (t + 1) ∂μ = β * (p t * ∫ i, c i t ∂μ) := by rw [h2, h1]; ring
  linarith

/-- **AKMM, (5.18), p. 142.** The aggregate Euler equation `C_{t+1} = βpₜ/p_{t+1}·Cₜ`, the
no-arbitrage condition (5.17) and the firm's condition
`r_{t+1} = αA_{t+1}K_{t+1}^{α−1}L_{t+1}^{1−α}` give
`C_{t+1}/Cₜ = β(1 − δ + αA_{t+1}K_{t+1}^{α−1}L_{t+1}^{1−α})`. -/
theorem eq_5_18 {β δ α Ct Ct1 pt pt1 rt1 At1 Kt1 Lt1 : ℝ} (hCt : Ct ≠ 0) (hpt1 : pt1 ≠ 0)
    (heul : Ct1 = β * pt / pt1 * Ct) (h517 : pt = pt1 * rt1 + (1 - δ) * pt1)
    (hr : rt1 = α * At1 * Kt1 ^ (α - 1) * Lt1 ^ (1 - α)) :
    Ct1 / Ct = β * (1 - δ + α * At1 * Kt1 ^ (α - 1) * Lt1 ^ (1 - α)) := by
  rw [heul, h517, ← hr]
  field_simp
  ring

/-- **AKMM, (5.19), p. 142.** If (5.16) holds with `c_{i,t} = eᵢCₜ` and `eᵢ > 0`,
`v′(Lₜ) = eᵢwₜ/c_{i,t}`, and `wₜ = (1 − α)AₜKₜ^αLₜ^{−α}`, then
`v′(Lₜ) = (1 − α)AₜKₜ^αLₜ^{−α}/Cₜ`. -/
theorem eq_5_19 {α e dv wt Ct At Kt Lt : ℝ} (he : 0 < e) (hC : Ct ≠ 0)
    (h516 : dv = e * wt * (e * Ct)⁻¹) (hw : wt = (1 - α) * At * Kt ^ α * Lt ^ (-α)) :
    dv = (1 - α) * At * Kt ^ α * Lt ^ (-α) / Ct := by
  rw [h516, hw]
  have := he.ne'
  field_simp

/-- **AKMM, (5.20), p. 142.** If goods clear, `∫ (c_{i,t} + ι_{i,t}) di = Yₜ`, with
`ι_{i,t} = k_{i,t+1} − (1 − δ)k_{i,t}` and capital clearing `∫ k_{i,s} di = Kₛ` (integrable
consumption and capital), then `Cₜ = Yₜ + (1 − δ)Kₜ − K_{t+1}`. -/
theorem eq_5_20 {μ : Measure I} {δ Yt : ℝ} {c k : I → ℕ → ℝ} {K : ℕ → ℝ} {t : ℕ}
    (hcint : Integrable (c · t) μ) (hkint : ∀ s, Integrable (k · s) μ)
    (hK : ∀ s, ∫ i, k i s ∂μ = K s)
    (hgoods : ∫ i, (c i t + (k i (t + 1) - (1 - δ) * k i t)) ∂μ = Yt) :
    ∫ i, c i t ∂μ = Yt + (1 - δ) * K t - K (t + 1) := by
  have h1 : Integrable (fun i => k i (t + 1) - (1 - δ) * k i t) μ :=
    (hkint (t + 1)).sub ((hkint t).const_mul _)
  have h2 : Integrable (fun i => (1 - δ) * k i t) μ := (hkint t).const_mul _
  rw [integral_add hcint h1, integral_sub (hkint (t + 1)) h2, integral_const_mul, hK, hK]
    at hgoods
  linarith

/-- **AKMM, fn. 7, p. 142.** With `δ = 1`, constant hours `L` with `v′(L)L = (1 − α)/(1 − αβ)`,
saving `K_{t+1} = αβYₜ` and consumption `Cₜ = (1 − αβ)Yₜ`, where
`Yₜ = AₜKₜ^αL^{1−α}`, the path satisfies (5.18), (5.19) and (5.20): the saving rate is `αβ`
and hours do not depend on time. -/
theorem growth_fn7 {α β Lbar dvL : ℝ} {A K C : ℕ → ℝ} (hα0 : 0 < α) (hβ0 : 0 < β)
    (hαβ : α * β < 1) (hA : ∀ t, 0 < A t) (hK0 : 0 < K 0) (hL : 0 < Lbar)
    (hv : dvL * Lbar = (1 - α) / (1 - α * β))
    (hsave : ∀ t, K (t + 1) = α * β * (A t * K t ^ α * Lbar ^ (1 - α)))
    (hcons : ∀ t, C t = (1 - α * β) * (A t * K t ^ α * Lbar ^ (1 - α))) :
    (∀ t, C (t + 1) / C t =
        β * (1 - 1 + α * A (t + 1) * K (t + 1) ^ (α - 1) * Lbar ^ (1 - α))) ∧
      (∀ t, dvL = (1 - α) * A t * K t ^ α * Lbar ^ (-α) / C t) ∧
      ∀ t, C t = A t * K t ^ α * Lbar ^ (1 - α) + (1 - 1) * K t - K (t + 1) := by
  have hKpos : ∀ t, 0 < K t := by
    intro t
    induction t with
    | zero => exact hK0
    | succ t ih =>
      rw [hsave]
      exact mul_pos (mul_pos hα0 hβ0) (mul_pos (mul_pos (hA t) (Real.rpow_pos_of_pos ih _))
        (Real.rpow_pos_of_pos hL _))
  have h1 : 0 < 1 - α * β := by linarith
  have hY : ∀ t, 0 < A t * K t ^ α * Lbar ^ (1 - α) := fun t =>
    mul_pos (mul_pos (hA t) (Real.rpow_pos_of_pos (hKpos t) _)) (Real.rpow_pos_of_pos hL _)
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · have hKa : K (t + 1) ^ (α - 1) = K (t + 1) ^ α / K (t + 1) :=
      Real.rpow_sub_one (hKpos (t + 1)).ne' α
    have hZ : C (t + 1) / C t =
        A (t + 1) * K (t + 1) ^ α * Lbar ^ (1 - α) / (A t * K t ^ α * Lbar ^ (1 - α)) := by
      rw [hcons, hcons]; have := h1.ne'; field_simp
    have e : β * (1 - 1 + α * A (t + 1) * K (t + 1) ^ (α - 1) * Lbar ^ (1 - α)) =
        A (t + 1) * K (t + 1) ^ α * Lbar ^ (1 - α) * (α * β / K (t + 1)) := by
      rw [hKa]; ring
    have hq : α * β / K (t + 1) = 1 / (A t * K t ^ α * Lbar ^ (1 - α)) := by
      rw [hsave t]; have := (hY t).ne'; have := hα0.ne'; have := hβ0.ne'; field_simp
    rw [e, hZ, hq]
    ring
  · rw [hcons]
    have hLa : Lbar ^ (-α) = Lbar ^ (1 - α) / Lbar := by
      rw [show -α = (1 - α) - 1 by ring, Real.rpow_sub_one hL.ne']
    rw [hLa]
    have hd : dvL = (1 - α) / (1 - α * β) / Lbar := by
      field_simp; field_simp at hv; linarith
    rw [hd]
    have := (Real.rpow_pos_of_pos (hKpos t) α).ne'
    have := (Real.rpow_pos_of_pos hL (1 - α)).ne'
    have := (hA t).ne'
    have := h1.ne'
    field_simp
  · rw [hcons, hsave]; ring

/-- The algebra of the planner's condition: for `a, b ≠ 0`,
`−1/a + β(x/b) = 0 ↔ b/a = βx`. -/
theorem ce_planner_iff {a b β x : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    -1 / a + β * (x / b) = 0 ↔ b / a = β * x := by
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [div_eq_iff ha] at h
    field_simp
    linarith

/-- **AKMM, p. 142: the planner's first-order condition in `K_{t+1}`.** The terms of
`Σ βᵗ[log Cₜ − v(Lₜ)]` that depend on `K_{t+1} = k`, after substituting (5.20), are
`log(AₜKₜ^αLₜ^{1−α} + (1 − δ)Kₜ − k) + β log(A_{t+1}k^αL_{t+1}^{1−α} + (1 − δ)k − K_{t+2})`;
at `k = K_{t+1} > 0` with positive consumptions `Cₜ, C_{t+1}` their derivative is
`−1/Cₜ + β(αA_{t+1}K_{t+1}^{α−1}L_{t+1}^{1−α} + 1 − δ)/C_{t+1}`, and it vanishes iff (5.18). -/
theorem growth_planner_foc_K {α β δ At Kt Lt At1 Kt1 Lt1 Kt2 Ct Ct1 : ℝ} (hK1 : 0 < Kt1)
    (hCdef : Ct = At * Kt ^ α * Lt ^ (1 - α) + (1 - δ) * Kt - Kt1)
    (hC1def : Ct1 = At1 * Kt1 ^ α * Lt1 ^ (1 - α) + (1 - δ) * Kt1 - Kt2)
    (hCt : 0 < Ct) (hCt1 : 0 < Ct1) :
    HasDerivAt (fun k => Real.log (At * Kt ^ α * Lt ^ (1 - α) + (1 - δ) * Kt - k) +
        β * Real.log (At1 * k ^ α * Lt1 ^ (1 - α) + (1 - δ) * k - Kt2))
      (-1 / Ct + β * ((α * At1 * Kt1 ^ (α - 1) * Lt1 ^ (1 - α) + (1 - δ)) / Ct1)) Kt1 ∧
    (-1 / Ct + β * ((α * At1 * Kt1 ^ (α - 1) * Lt1 ^ (1 - α) + (1 - δ)) / Ct1) = 0 ↔
      Ct1 / Ct = β * (1 - δ + α * At1 * Kt1 ^ (α - 1) * Lt1 ^ (1 - α))) := by
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun k => At * Kt ^ α * Lt ^ (1 - α) + (1 - δ) * Kt - k) (-1) Kt1 := by
      simpa using (hasDerivAt_id Kt1).const_sub (At * Kt ^ α * Lt ^ (1 - α) + (1 - δ) * Kt)
    have h2 : HasDerivAt (fun k => At1 * k ^ α * Lt1 ^ (1 - α) + (1 - δ) * k - Kt2)
        (At1 * (α * Kt1 ^ (α - 1)) * Lt1 ^ (1 - α) + (1 - δ) * 1) Kt1 := by
      exact ((((Real.hasDerivAt_rpow_const (Or.inl hK1.ne')).const_mul At1).mul_const _).add
        ((hasDerivAt_id Kt1).const_mul (1 - δ))).sub_const Kt2
    rw [hCdef] at hCt
    rw [hC1def] at hCt1
    have := ((Real.hasDerivAt_log hCt.ne').comp Kt1 h1).add
      (((Real.hasDerivAt_log hCt1.ne').comp Kt1 h2).const_mul β)
    rw [hCdef, hC1def]
    convert this using 1 <;> first | rfl | ring
  · rw [ce_planner_iff hCt.ne' hCt1.ne']
    constructor <;> intro h <;> linear_combination h

/-- **AKMM, p. 142: the planner's first-order condition in `Lₜ`.** The terms of the planner's
objective that depend on `Lₜ = L` are `log(AₜKₜ^αL^{1−α} + (1 − δ)Kₜ − K_{t+1}) − v(L)`; at
`L = Lₜ > 0` with positive consumption `Cₜ` their derivative is
`(1 − α)AₜKₜ^αLₜ^{−α}/Cₜ − v′(Lₜ)`, and it vanishes iff (5.19). -/
theorem growth_planner_foc_L {v : ℝ → ℝ} {α δ At Kt Lt Kt1 dv Ct : ℝ} (hL : 0 < Lt)
    (hCdef : Ct = At * Kt ^ α * Lt ^ (1 - α) + (1 - δ) * Kt - Kt1) (hC : 0 < Ct)
    (hdv : HasDerivAt v dv Lt) :
    HasDerivAt (fun L => Real.log (At * Kt ^ α * L ^ (1 - α) + (1 - δ) * Kt - Kt1) - v L)
      ((1 - α) * At * Kt ^ α * Lt ^ (-α) / Ct - dv) Lt ∧
    ((1 - α) * At * Kt ^ α * Lt ^ (-α) / Ct - dv = 0 ↔
      dv = (1 - α) * At * Kt ^ α * Lt ^ (-α) / Ct) := by
  refine ⟨?_, sub_eq_zero.trans eq_comm⟩
  have h1 : HasDerivAt (fun L => At * Kt ^ α * L ^ (1 - α) + (1 - δ) * Kt - Kt1)
      (At * Kt ^ α * ((1 - α) * Lt ^ (1 - α - 1))) Lt :=
    (((Real.hasDerivAt_rpow_const (Or.inl hL.ne')).const_mul (At * Kt ^ α)).add_const
      _).sub_const _
  rw [hCdef] at hC
  have := ((Real.hasDerivAt_log hC.ne').comp Lt h1).sub hdv
  rw [show (1 : ℝ) - α - 1 = -α by ring] at this
  rw [hCdef]
  convert this using 1 <;> first | rfl | ring

end AKMM.CompetitiveEquilibrium
