/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSolow.Production
import DiscreteTime.SolowComparative
import DiscreteTime.SolowSwanDynamics

/-!
# The basic Solow model: steady state and dynamics

AKMM, §3.1–3.1.1, pp. 72–75. No technological progress or population growth: `L = 1` and
`k_{t+1} = (1 − δ)k_t + s f(k_t)` (3.5). This is EconomicGrowth's discrete-time Solow map
`Solow1956.DiscreteTime.next f s δ 1`, so the steady state and the global dynamics are imported:

* (3.5) from (3.1)–(3.4) (`eq_3_5`) and its growth-rate form (`solow_growth_rate_form`);
* the steady state `δk̄ = s f(k̄)` exists and is unique (`solow_steady_existsUnique`, from
  `Solow1956.DiscreteTime.existsUnique_steadyState`), also under the book's weaker boundary
  conditions `lim_{k→0} f' > δ/s`, `lim_{k→∞} f' < δ/s` (`solow_steady_existsUnique_weak`,
  new; no Inada and no monotonicity needed), with global monotone convergence under those weak
  conditions when `f` is increasing (`solow_global_convergence_weak`, from
  `Solow1956.DiscreteTime.Map.attracting_orbit`);
* global monotone convergence from every `k₀ > 0` (`solow_global_convergence`) and the two steps
  of the book's proof (`solow_convergence_proof_steps`);
* `f(k)/k` is decreasing (`solow_average_product_strictAnti`);
* Cobb–Douglas: `k̄ = (s/δ)^{1/(1−α)}` (3.6) (`eq_3_6`), `ȳ = (s/δ)^{α/(1−α)}`
  (`solow_cobbDouglas_output`), comparative statics in `s` and `δ`
  (`solow_steady_strictMono_saving`, `solow_steady_strictAnti_depreciation`), and
  `k̄/ȳ = s/δ` (`solow_capital_output_ratio`, `solow_capital_output_ratio_mono`).
-/

namespace AKMM.Solow

open Filter Topology Solow1956.Neoclassical Solow1956.DiscreteTime

variable {F : ℝ → ℝ → ℝ}

/-- AKMM, §3.1, p. 72: with `0 < s`, `0 < δ < 1` the basic model has EconomicGrowth's parameter
conditions with no growth (`γ = 1`). -/
theorem solow_params_basic {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Params s δ 1 :=
  ⟨hs, hδ1.le, one_pos, by linarith⟩

/-- AKMM, (3.5), p. 73: production (3.1), accumulation (3.2), the resource constraint (3.3) and
constant saving (3.4) give the fundamental equation `k_{t+1} = (1 − δ)k_t + s f(k_t)`, which is
EconomicGrowth's map with `γ = 1`; consumption is `c_t = (1 − s) y_t`. -/
theorem eq_3_5 {f : ℝ → ℝ} {s δ : ℝ} {k y c i : ℕ → ℝ} (hy : ∀ t, y t = f (k t))
    (hk : ∀ t, k (t + 1) = i t + (1 - δ) * k t) (hc : ∀ t, y t = c t + i t)
    (hi : ∀ t, i t = s * y t) (t : ℕ) :
    k (t + 1) = (1 - δ) * k t + s * f (k t) ∧ k (t + 1) = next f s δ 1 (k t) ∧
      c t = (1 - s) * y t := by
  have h1 : k (t + 1) = (1 - δ) * k t + s * f (k t) := by rw [hk, hi, hy]; ring
  refine ⟨h1, by rw [next_acemoglu, h1]; ring, ?_⟩
  have := hc t
  rw [hi] at this
  linarith

/-- AKMM, p. 75: the fundamental equation in growth-rate form,
`(k_{t+1} − k_t)/k_t = s f(k_t)/k_t − δ`. -/
theorem solow_growth_rate_form {f : ℝ → ℝ} {s δ : ℝ} {k : ℕ → ℝ} {t : ℕ} (hk : k t ≠ 0)
    (hsucc : k (t + 1) = (1 - δ) * k t + s * f (k t)) :
    (k (t + 1) - k t) / k t = s * f (k t) / k t - δ := by
  rw [hsucc]
  field_simp
  ring

/-- AKMM, p. 73: a constant path `k_t = k̄` solves (3.5) exactly when `δ k̄ = s f(k̄)`. -/
theorem solow_fixed_iff {f : ℝ → ℝ} {s δ k : ℝ} : next f s δ 1 k = k ↔ δ * k = s * f k := by
  rw [next_acemoglu]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 73: under Assumptions 1–6 a strictly positive steady state `δk̄ = s f(k̄)` exists and
is unique (EconomicGrowth's `existsUnique_steadyState`, Acemoglu Proposition 2.2). -/
theorem solow_steady_existsUnique (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) : ∃! k : ℝ, 0 < k ∧ δ * k = s * intensive F k := by
  simpa only [solow_fixed_iff] using
    existsUnique_steadyState (solow_technology hF) (solow_params_basic hs hδ hδ1)

/-- AKMM, p. 73: the steady state `k̄` (EconomicGrowth's `steady` at `γ = 1`) is positive and
solves `δ k̄ = s f(k̄)`. -/
theorem solow_steady_spec (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    0 < steady (solow_technology hF) s δ 1 ∧
      δ * steady (solow_technology hF) s δ 1 =
        s * intensive F (steady (solow_technology hF) s δ 1) := by
  obtain ⟨h1, h2⟩ := steady_spec (solow_technology hF) (solow_params_basic hs hδ hδ1)
  exact ⟨h1, solow_fixed_iff.mp h2⟩

/-- AKMM, p. 74: global and monotone convergence. Every path of (3.5) from `k₀ > 0` stays
positive; it is strictly increasing and below `k̄` if `k₀ < k̄`, strictly decreasing and above
`k̄` if `k₀ > k̄`, constant if `k₀ = k̄`; it stays between `k₀` and `k̄` and converges to `k̄`
(EconomicGrowth's `IsPath.orbit`, Acemoglu Proposition 2.5). -/
theorem solow_global_convergence (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) {k : ℕ → ℝ} (h0 : 0 < k 0)
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * intensive F (k t)) :
    (∀ t, 0 < k t) ∧
      (k 0 < steady (solow_technology hF) s δ 1 →
        StrictMono k ∧ ∀ t, k t < steady (solow_technology hF) s δ 1) ∧
      (steady (solow_technology hF) s δ 1 < k 0 →
        StrictAnti k ∧ ∀ t, steady (solow_technology hF) s δ 1 < k t) ∧
      (k 0 = steady (solow_technology hF) s δ 1 → ∀ t, k t = steady (solow_technology hF) s δ 1) ∧
      (∀ t, min (k 0) (steady (solow_technology hF) s δ 1) ≤ k t ∧
        k t ≤ max (k 0) (steady (solow_technology hF) s δ 1)) ∧
      Tendsto k atTop (𝓝 (steady (solow_technology hF) s δ 1)) :=
  IsPath.orbit (solow_technology hF) (solow_params_basic hs hδ hδ1)
    ⟨h0, fun t => by rw [hk, next_acemoglu]; ring⟩

/-- AKMM, p. 74, the proof of convergence: if `0 < k_t < k̄` then (i) `k_{t+1} > k_t`, because
`s f(k_t) > δ k_t`, and (ii) `k_{t+1} < k̄`, because the right side of (3.5) is increasing. -/
theorem solow_convergence_proof_steps (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) {k : ℝ} (hk : 0 < k) (hlt : k < steady (solow_technology hF) s δ 1) :
    δ * k < s * intensive F k ∧ k < (1 - δ) * k + s * intensive F k ∧
      (1 - δ) * k + s * intensive F k < steady (solow_technology hF) s δ 1 := by
  have P := solow_params_basic hs hδ hδ1
  have h := solow_technology hF
  have h1 := next_gt_self h P hk hlt
  have hfix := (steady_spec h P).2
  have h2 := next_strictMono h P (Set.mem_Ici.mpr hk.le)
    (Set.mem_Ici.mpr (steady_spec h P).1.le) hlt
  rw [hfix] at h2
  rw [next_acemoglu] at h1 h2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- AKMM, p. 75: `f(0) = 0` and diminishing returns make the average product `f(k)/k` strictly
decreasing (EconomicGrowth's `Technology.average_strictAnti`). -/
theorem solow_average_product_strictAnti (hF : SolowAssumptions F) :
    StrictAntiOn (fun k => intensive F k / k) (Set.Ioi 0) :=
  (solow_technology hF).average_strictAnti

/-- AKMM, (3.6), p. 73: with `f(k) = k^α`, `k̄ = (s/δ)^{1/(1−α)}`; it is the steady state of
EconomicGrowth's map (`Solow1956.DiscreteTime.CobbDouglas.steady_eq`) and the unique positive
solution of `δ k = s k^α`. -/
theorem eq_3_6 {α s δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1) :
    steady (technology_rpow hα hα1) s δ 1 = (s / δ) ^ (1 / (1 - α)) ∧
      δ * (s / δ) ^ (1 / (1 - α)) = s * ((s / δ) ^ (1 / (1 - α))) ^ α := by
  have h := CobbDouglas.steady_eq hα hα1 (solow_params_basic hs hδ hδ1)
  rw [show (1 : ℝ) - 1 + δ = δ by ring] at h
  have heq : steady (technology_rpow hα hα1) s δ 1 = (s / δ) ^ (1 / (1 - α)) := by
    rw [h, Solow1956.SolowSwan.CobbDouglas.steadyState, one_div]
  refine ⟨heq, ?_⟩
  have := solow_fixed_iff.mp (steady_spec (technology_rpow hα hα1) (solow_params_basic hs hδ hδ1)).2
  rw [heq] at this
  exact this

/-- AKMM, p. 74: with Cobb–Douglas production, steady-state output is
`ȳ = k̄^α = (s/δ)^{α/(1−α)}`. -/
theorem solow_cobbDouglas_output {α s δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    steady (technology_rpow hα hα1) s δ 1 ^ α = (s / δ) ^ (α / (1 - α)) := by
  rw [(eq_3_6 hα hα1 hs hδ hδ1).1, ← Real.rpow_mul (div_pos hs hδ).le]
  congr 1
  ring

/-- AKMM, p. 74: the steady state capital stock and output are strictly increasing in the saving
rate (EconomicGrowth's `steady_strictMono_saving`); stated for every `f` satisfying Assumptions
1–6, which includes the book's Cobb–Douglas case. -/
theorem solow_steady_strictMono_saving (hF : SolowAssumptions F) {s₁ s₂ δ : ℝ} (hs₁ : 0 < s₁)
    (hs : s₁ < s₂) (hδ : 0 < δ) :
    steady (solow_technology hF) s₁ δ 1 < steady (solow_technology hF) s₂ δ 1 ∧
      intensive F (steady (solow_technology hF) s₁ δ 1) <
        intensive F (steady (solow_technology hF) s₂ δ 1) := by
  have hm : (0 : ℝ) < 1 - 1 + δ := by linarith
  have h := steady_strictMono_saving (solow_technology hF) hm (Set.mem_Ioi.mpr hs₁)
    (Set.mem_Ioi.mpr (hs₁.trans hs)) hs
  refine ⟨h, solow_intensive_strictMono hF ?_ ?_ h⟩
  · exact Set.mem_Ici.mpr (steadyCapital_spec (solow_technology hF) hs₁ hm).1.le
  · exact Set.mem_Ici.mpr (steadyCapital_spec (solow_technology hF) (hs₁.trans hs) hm).1.le

/-- AKMM, p. 74: the steady state capital stock and output are strictly decreasing in the
depreciation rate (EconomicGrowth's `steady_strictAnti_depreciation`). -/
theorem solow_steady_strictAnti_depreciation (hF : SolowAssumptions F) {s δ₁ δ₂ : ℝ}
    (hs : 0 < s) (hδ₁ : 0 < δ₁) (hδ : δ₁ < δ₂) :
    steady (solow_technology hF) s δ₂ 1 < steady (solow_technology hF) s δ₁ 1 ∧
      intensive F (steady (solow_technology hF) s δ₂ 1) <
        intensive F (steady (solow_technology hF) s δ₁ 1) := by
  have hm : (0 : ℝ) < 1 - 1 + δ₁ := by linarith
  have h := steady_strictAnti_depreciation (solow_technology hF) hs hm hδ
  refine ⟨h, solow_intensive_strictMono hF ?_ ?_ h⟩
  · exact Set.mem_Ici.mpr
      (steadyCapital_spec (solow_technology hF) hs (by linarith : (0 : ℝ) < 1 - 1 + δ₂)).1.le
  · exact Set.mem_Ici.mpr (steadyCapital_spec (solow_technology hF) hs hm).1.le

/-- AKMM, p. 75: the steady-state capital–output ratio is `k̄/ȳ = s/δ` (stated in the book for
Cobb–Douglas; it holds for every technology since `δ k̄ = s f(k̄)`). -/
theorem solow_capital_output_ratio (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    steady (solow_technology hF) s δ 1 / intensive F (steady (solow_technology hF) s δ 1) =
      s / δ := by
  obtain ⟨hk, he⟩ := solow_steady_spec hF hs hδ hδ1
  have hy := solow_intensive_pos hF hk
  rw [div_eq_div_iff (ne_of_gt hy) (ne_of_gt hδ)]
  linarith

/-- AKMM, p. 75: "in the long run `k_t/y_t` is larger when `s` is larger and when `δ` is
smaller". -/
theorem solow_capital_output_ratio_mono (hF : SolowAssumptions F) {s₁ s₂ δ₁ δ₂ : ℝ}
    (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂) (hδ₂ : 0 < δ₂) (hδ : δ₂ ≤ δ₁) (hδ1 : δ₁ < 1) :
    steady (solow_technology hF) s₁ δ₁ 1 / intensive F (steady (solow_technology hF) s₁ δ₁ 1) ≤
      steady (solow_technology hF) s₂ δ₂ 1 /
        intensive F (steady (solow_technology hF) s₂ δ₂ 1) := by
  rw [solow_capital_output_ratio hF hs₁ (hδ₂.trans_le hδ) hδ1,
    solow_capital_output_ratio hF (hs₁.trans_le hs) hδ₂ (hδ.trans_lt hδ1)]
  exact div_le_div₀ (hs₁.trans_le hs).le hs hδ₂ hδ

/-- The average product of a strictly concave `f` with `f(0) = 0` is strictly decreasing. -/
theorem solow_average_strictAnti_of_concave {f : ℝ → ℝ} (h0 : f 0 = 0)
    (hcc : StrictConcaveOn ℝ (Set.Ici 0) f) : StrictAntiOn (fun k => f k / k) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have h := hcc.2 (Set.mem_Ici.mpr hb'.le) (Set.mem_Ici.mpr (le_refl 0)) (ne_of_gt hb')
    (div_pos ha' hb') (sub_pos.mpr ((div_lt_one hb').mpr hab)) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, h0] at h
  rw [div_mul_cancel₀ a (ne_of_gt hb')] at h
  simp only
  rw [div_lt_div_iff₀ hb' ha']
  have h2 : a * f b < f a * b := by
    have := mul_lt_mul_of_pos_right h hb'
    rwa [show a / b * f b * b = a * f b by field_simp] at this
  linarith

/-- AKMM, p. 73: "the Inada conditions are stronger than necessary: they can be replaced by
weaker versions `lim_{k→0} F₁(k, 1) > δ/s` and `lim_{k→∞} F₁(k, 1) < δ/s`". For a continuous,
strictly concave `f` with `f(0) = 0`, differentiable on `(0, ∞)`, with `f' > δ/s` near zero and
`f' < δ/s` for large `k` (implied by the two limit conditions), the steady state `δk = s f(k)`,
`k > 0`, exists and is unique. -/
theorem solow_steady_existsUnique_weak {f : ℝ → ℝ} {s δ : ℝ} (hs : 0 < s)
    (hc : ContinuousOn f (Set.Ici 0)) (h0 : f 0 = 0) (hd : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hcc : StrictConcaveOn ℝ (Set.Ici 0) f) (hlow : ∀ᶠ k in 𝓝[>] 0, δ / s < deriv f k)
    (hhigh : ∀ᶠ k in atTop, deriv f k < δ / s) :
    ∃! k : ℝ, 0 < k ∧ δ * k = s * f k := by
  -- a point near zero where investment exceeds depreciation
  have hz : ∀ᶠ k in 𝓝[>] (0 : ℝ), 0 < k := self_mem_nhdsWithin
  obtain ⟨a, ha, hfa⟩ := (hz.and hlow).exists
  have hga : δ * a < s * f a := by
    have hsl := hcc.concaveOn.deriv_le_slope (Set.mem_Ici.mpr (le_refl 0))
      (Set.mem_Ici.mpr ha.le) ha (hd a ha)
    rw [slope_def_field, h0, sub_zero, sub_zero, le_div_iff₀ ha] at hsl
    have := (div_lt_iff₀ hs).mp hfa
    nlinarith
  -- a large point where depreciation exceeds investment
  obtain ⟨b, hfb, hab⟩ := (hhigh.and (eventually_ge_atTop (a + 1))).exists
  have hb : 0 < b := by linarith
  set c := δ - s * deriv f b with hcdef
  have hcpos : 0 < c := by have := (lt_div_iff₀ hs).mp hfb; linarith
  set K := max (b + 1) ((s * f b - s * deriv f b * b) / c + 1) with hK
  have hbK : b < K := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hgK : s * f K - δ * K ≤ 0 := by
    have hsl := hcc.concaveOn.slope_le_deriv (Set.mem_Ici.mpr hb.le)
      (Set.mem_Ici.mpr (hb.trans hbK).le) hbK (hd b hb)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hbK)] at hsl
    have h2 : (s * f b - s * deriv f b * b) / c + 1 ≤ K := le_max_right _ _
    have h3 : s * f b - s * deriv f b * b ≤ c * K := by
      have := (div_le_iff₀ hcpos).mp (by linarith : (s * f b - s * deriv f b * b) / c ≤ K)
      linarith
    have h4 := mul_le_mul_of_nonneg_left hsl hs.le
    nlinarith
  have haK : a ≤ K := by linarith
  have hcont : ContinuousOn (fun k => s * f k - δ * k) (Set.Icc a K) :=
    ((hc.mono (fun x hx => Set.mem_Ici.mpr (ha.le.trans hx.1))).const_mul s).sub
      (continuousOn_id.const_mul δ)
  obtain ⟨k, hk, hk0⟩ := intermediate_value_Icc' haK hcont
    ⟨hgK, by change 0 ≤ s * f a - δ * a; linarith⟩
  have hk0' : s * f k - δ * k = 0 := hk0
  have hkpos : 0 < k := ha.trans_le hk.1
  refine ⟨k, ⟨hkpos, by linarith⟩, ?_⟩
  rintro y ⟨hy, hye⟩
  have hanti := solow_average_strictAnti_of_concave h0 hcc
  apply hanti.injOn (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hkpos)
  change f y / y = f k / k
  rw [div_eq_div_iff (ne_of_gt hy) (ne_of_gt hkpos)]
  have e1 : s * (f y * k) = δ * y * k := by rw [← mul_assoc, ← hye]
  have e2 : s * (f k * y) = δ * k * y := by
    rw [← mul_assoc, show s * f k = δ * k by linarith]
  have : s * (f y * k) = s * (f k * y) := by rw [e1, e2]; ring
  exact mul_left_cancel₀ (ne_of_gt hs) this

/-- AKMM, p. 74, under the weak boundary conditions of p. 73: if moreover `f` is strictly
increasing and `0 < δ ≤ 1`, every path of (3.5) from `k₀ > 0` converges monotonically to the
unique steady state (EconomicGrowth's `Map.attracting_orbit`, which needs no derivative). -/
theorem solow_global_convergence_weak {f : ℝ → ℝ} {s δ ks : ℝ} (hs : 0 < s) (hδ1 : δ ≤ 1)
    (hc : ContinuousOn f (Set.Ici 0)) (h0 : f 0 = 0) (hmono : StrictMonoOn f (Set.Ici 0))
    (hcc : StrictConcaveOn ℝ (Set.Ici 0) f) (hks : 0 < ks) (hfix : δ * ks = s * f ks)
    {k : ℕ → ℝ} (hk0 : 0 < k 0) (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * f (k t)) :
    (∀ t, 0 < k t) ∧ (k 0 < ks → StrictMono k ∧ ∀ t, k t < ks) ∧
      (ks < k 0 → StrictAnti k ∧ ∀ t, ks < k t) ∧ Tendsto k atTop (𝓝 ks) := by
  have hanti := solow_average_strictAnti_of_concave h0 hcc
  have hav : f ks / ks = δ / s := by
    rw [div_eq_div_iff (ne_of_gt hks) (ne_of_gt hs)]; linarith
  have hgm : StrictMonoOn (fun x => (1 - δ) * x + s * f x) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have h1 := mul_lt_mul_of_pos_left (hmono (Set.mem_Ici.mpr (le_of_lt hx))
      (Set.mem_Ici.mpr (le_of_lt hy)) hxy) hs
    have h2 := mul_le_mul_of_nonneg_left hxy.le (sub_nonneg.mpr hδ1)
    simp only
    linarith
  have hgc : ContinuousOn (fun x => (1 - δ) * x + s * f x) (Set.Ioi 0) :=
    (continuousOn_id.const_mul (1 - δ)).add
      ((hc.mono (fun x hx => Set.mem_Ici.mpr (le_of_lt hx))).const_mul s)
  have hbelow : ∀ y, 0 < y → y < ks → y < (1 - δ) * y + s * f y := by
    intro y hy hlt
    have h := hanti (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hks) hlt
    simp only at h
    rw [hav, div_lt_div_iff₀ hs hy] at h
    linarith
  have habove : ∀ y, ks < y → (1 - δ) * y + s * f y < y := by
    intro y hlt
    have h := hanti (Set.mem_Ioi.mpr hks) (Set.mem_Ioi.mpr (hks.trans hlt)) hlt
    simp only at h
    rw [hav, div_lt_div_iff₀ (hks.trans hlt) hs] at h
    linarith
  obtain ⟨hpos, hlow, hhigh, _, _, hlim⟩ := Map.attracting_orbit hgm hgc hks
    (by linarith) hbelow habove hk0 hk
  exact ⟨hpos, hlow, hhigh, hlim⟩

end AKMM.Solow
