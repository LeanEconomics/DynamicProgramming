/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.MIUNonseparable

/-!
# The cashless limit

AKMM, §17.3.3, "The cashless limit", pp. 517–519, with footnotes 17–18. Utility is
`u(c, m₁) = f(h(c, m₁))` with `f` increasing and strictly concave and the CES index
`h(c, m₁) = ((1 − ω)c^ρ + ωm₁^ρ)^{1/ρ}`, `ρ < 1`, `ρ ≠ 0` (Galí's `composite ω (1 − ρ)`).

* `clH`, `clh`, `clh1`, `clh2`, `clTheta`: the index, its partial derivatives and the money
  share `θ = ωm₁^ρ/H`; `cl_h_eq_composite` identifies `h` with Galí's composite;
  `cl_h_hasDerivAt_c`, `cl_h_hasDerivAt_m`: `h_c = h₁`, `h_m = h₂`.
* `eq_17_41`: `h₂/h₁ = i/(1 + i)` iff `M_{t+1}/P_t = c((1 − ω)/ω · i/(1 + i))^{1/(ρ−1)}`;
  `cl_demand_homogeneous`, `cl_demand_elasticity`, `cl_demand_strictAnti`: unit consumption
  elasticity, constant elasticity `1/(ρ − 1)` in `i/(1 + i)`, decreasing in the opportunity cost;
  `cl_demand_tendsto_zero`: real balances vanish as `ω → 0`.
* `cl_footnote_17`: `(i/(1 + i))m₁/c = (u₁₂m₁/u₁)/(u₂₁c/u₂)`.
* `cl_h1_hasDerivAt_c`, `cl_h1_hasDerivAt_m`: `h₁₁c/h₁ = (ρ − 1)θ`, `h₁₂m₁/h₁ = (1 − ρ)θ`;
  `cl_footnote_18_identities`: `u₁₁c/u₁ = (f″/f′)h₁c + h₁₁c/h₁` and
  `u₁₂m₁/u₁ = (f″/f′)h₂m₁ + h₁₂m₁/h₁` (the latter corrected: printed with `h_{2,2}` for `h₂m₁`).
* `cl_footnote_18_limits`: along the money-demand curve, as `ω → 0`, `θ → 0`, `h → c`, `h₁ → 1`,
  `h₂m₁ → 0`, hence `η_{u₁,c} → −f″(c)c/f′(c) > 0` and `η_{u₁,m₁} → 0`.
-/

open Filter Topology

namespace AKMM.Money

/-- AKMM, p. 518: the CES aggregator inside the index, `H = (1 − ω)c^ρ + ωm^ρ`. -/
noncomputable def clH (ω ρ c m : ℝ) : ℝ := (1 - ω) * c ^ ρ + ω * m ^ ρ

/-- AKMM, p. 518: the CES index `h = H^{1/ρ}`. -/
noncomputable def clh (ω ρ c m : ℝ) : ℝ := clH ω ρ c m ^ (1 / ρ)

/-- AKMM, p. 518: `h₁ = ∂h/∂c = (1 − ω)c^{ρ−1}H^{1/ρ−1}`. -/
noncomputable def clh1 (ω ρ c m : ℝ) : ℝ := (1 - ω) * c ^ (ρ - 1) * clH ω ρ c m ^ (1 / ρ - 1)

/-- AKMM, p. 518: `h₂ = ∂h/∂m₁ = ωm₁^{ρ−1}H^{1/ρ−1}`. -/
noncomputable def clh2 (ω ρ c m : ℝ) : ℝ := ω * m ^ (ρ - 1) * clH ω ρ c m ^ (1 / ρ - 1)

/-- The money share `θ = ωm₁^ρ/H`. -/
noncomputable def clTheta (ω ρ c m : ℝ) : ℝ := ω * m ^ ρ / clH ω ρ c m

/-- The aggregator is positive. -/
theorem clH_pos {ω ρ c m : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c) (hm : 0 < m) :
    0 < clH ω ρ c m := by
  unfold clH
  have := Real.rpow_pos_of_pos hc ρ
  have := Real.rpow_pos_of_pos hm ρ
  have : 0 < 1 - ω := by linarith
  positivity

/-- The book's index is Galí's composite `composite ω (1 − ρ)` (Galí 2015, p. 35). -/
theorem cl_h_eq_composite {ω ρ c m : ℝ} (hρ : ρ ≠ 0) :
    clh ω ρ c m = Gali.ClassicalMonetaryModel.MIUNonseparable.composite ω (1 - ρ) c m := by
  unfold clh clH Gali.ClassicalMonetaryModel.MIUNonseparable.composite
  have h1 : (1 - ρ) ≠ 1 := by intro h; exact hρ (by linarith)
  simp only [h1, ↓reduceIte, show (1 : ℝ) - (1 - ρ) = ρ by ring]

/-- AKMM, p. 518: `∂h/∂c = h₁`. -/
theorem cl_h_hasDerivAt_c {ω ρ c m : ℝ} (hρ : ρ ≠ 0) (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c)
    (hm : 0 < m) : HasDerivAt (fun c' => clh ω ρ c' m) (clh1 ω ρ c m) c := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have hd : HasDerivAt (fun c' => clH ω ρ c' m) ((1 - ω) * (ρ * c ^ (ρ - 1))) c := by
    unfold clH
    exact ((Real.hasDerivAt_rpow_const (Or.inl hc.ne')).const_mul (1 - ω)).add_const _
  have := hd.rpow_const (p := 1 / ρ) (Or.inl hH.ne')
  unfold clh clh1
  refine this.congr_deriv ?_
  field_simp

/-- AKMM, p. 518: `∂h/∂m₁ = h₂`. -/
theorem cl_h_hasDerivAt_m {ω ρ c m : ℝ} (hρ : ρ ≠ 0) (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c)
    (hm : 0 < m) : HasDerivAt (fun m' => clh ω ρ c m') (clh2 ω ρ c m) m := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have hd : HasDerivAt (fun m' => clH ω ρ c m') (ω * (ρ * m ^ (ρ - 1))) m := by
    unfold clH
    exact ((Real.hasDerivAt_rpow_const (Or.inl hm.ne')).const_mul ω).const_add _
  have := hd.rpow_const (p := 1 / ρ) (Or.inl hH.ne')
  unfold clh clh2
  refine this.congr_deriv ?_
  field_simp

/-- AKMM, (17.41), p. 518: money demand `m₁ = c((1 − ω)/ω · s)^{1/(ρ−1)}`, `s = i/(1 + i)`. -/
noncomputable def clDemand (ω ρ c s : ℝ) : ℝ := c * ((1 - ω) / ω * s) ^ (1 / (ρ - 1))

/-- **AKMM, (17.41)**, p. 518: `h_{m₁}/h_c = s` iff `m₁ = c((1 − ω)/ω · s)^{1/(ρ−1)}`. -/
theorem eq_17_41 {ω ρ c m s : ℝ} (hρ1 : ρ < 1) (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c)
    (hm : 0 < m) (hs : 0 < s) : clh2 ω ρ c m / clh1 ω ρ c m = s ↔ m = clDemand ω ρ c s := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have h1ω : 0 < 1 - ω := by linarith
  have hρ' : ρ - 1 ≠ 0 := by linarith
  have hratio : clh2 ω ρ c m / clh1 ω ρ c m = ω / (1 - ω) * (m / c) ^ (ρ - 1) := by
    unfold clh1 clh2
    rw [Real.div_rpow hm.le hc.le]
    have := (Real.rpow_pos_of_pos hH (1 / ρ - 1)).ne'
    have := (Real.rpow_pos_of_pos hc (ρ - 1)).ne'
    field_simp
  rw [hratio]
  have hB : 0 < (1 - ω) / ω * s := by positivity
  have hx : 0 < m / c := div_pos hm hc
  unfold clDemand
  constructor
  · intro h
    have h' : (m / c) ^ (ρ - 1) = (1 - ω) / ω * s := by
      field_simp at h ⊢; linarith
    have : m / c = ((1 - ω) / ω * s) ^ (1 / (ρ - 1)) := by
      rw [← h', one_div, Real.rpow_rpow_inv hx.le hρ']
    rw [← this]; field_simp
  · intro h
    have : m / c = ((1 - ω) / ω * s) ^ (1 / (ρ - 1)) := by rw [h]; field_simp
    rw [this, ← Real.rpow_mul hB.le, one_div, inv_mul_cancel₀ hρ', Real.rpow_one]
    field_simp

/-- AKMM, p. 518: money demand has unitary elasticity with respect to consumption. -/
theorem cl_demand_homogeneous (ω ρ c s k : ℝ) : clDemand ω ρ (k * c) s = k * clDemand ω ρ c s := by
  unfold clDemand; ring

/-- AKMM, p. 518: constant elasticity `1/(ρ − 1)` with respect to `i/(1 + i)`. -/
theorem cl_demand_elasticity {ω ρ c s k : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (hs : 0 < s)
    (hk : 0 < k) : clDemand ω ρ c (k * s) = k ^ (1 / (ρ - 1)) * clDemand ω ρ c s := by
  unfold clDemand
  have h1ω : 0 < 1 - ω := by linarith
  have : 0 < (1 - ω) / ω * s := by positivity
  rw [show (1 - ω) / ω * (k * s) = k * ((1 - ω) / ω * s) by ring,
    Real.mul_rpow hk.le this.le]
  ring

/-- AKMM, p. 518: since `ρ < 1`, real balances are strictly decreasing in the opportunity cost. -/
theorem cl_demand_strictAnti {ω ρ c : ℝ} (hρ1 : ρ < 1) (hω0 : 0 < ω) (hω1 : ω < 1)
    (hc : 0 < c) : StrictAntiOn (clDemand ω ρ c) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  unfold clDemand
  apply mul_lt_mul_of_pos_left _ hc
  have h1ω : 0 < (1 - ω) / ω := div_pos (by linarith) hω0
  exact Real.rpow_lt_rpow_of_neg (by positivity) (mul_lt_mul_of_pos_left hab h1ω)
    (by rw [one_div_neg]; linarith)

/-- AKMM, p. 519: as `ω → 0` real balances vanish, `M_{t+1}/P_t → 0`, for fixed `c` and `i`. -/
theorem cl_demand_tendsto_zero {ρ c s : ℝ} (hρ1 : ρ < 1) (hs : 0 < s) :
    Tendsto (fun ω => clDemand ω ρ c s) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun ω : ℝ => (1 - ω) / ω * s) (𝓝[>] 0) atTop := by
    have : Tendsto (fun ω : ℝ => (ω⁻¹ - 1) * s) (𝓝[>] 0) atTop :=
      (tendsto_atTop_add_const_right _ (-1) tendsto_inv_nhdsGT_zero).atTop_mul_const hs
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ω hω
    have : (0 : ℝ) < ω := hω
    field_simp
  have h2 : Tendsto (fun x : ℝ => x ^ (1 / (ρ - 1))) atTop (𝓝 0) := by
    have hρ' : 0 < 1 - ρ := by linarith
    have := tendsto_rpow_neg_atTop (y := 1 / (1 - ρ)) (by positivity)
    refine this.congr fun x => ?_
    congr 1
    have : (1 : ℝ) - ρ ≠ 0 := by linarith
    have : ρ - 1 ≠ 0 := by linarith
    field_simp
    ring
  have h3 := (h2.comp h1).const_mul c
  rw [mul_zero] at h3
  exact h3

/-- AKMM, footnote 17, p. 519: with `u₂/u₁ = i/(1 + i)` and symmetric cross partials,
`(i/(1 + i))m₁/c = (u₁₂m₁/u₁)/(u₂₁c/u₂)`. -/
theorem cl_footnote_17 {u1 u2 u12 c m s : ℝ} (hu1 : u1 ≠ 0) (hu2 : u2 ≠ 0) (hu12 : u12 ≠ 0)
    (hc : c ≠ 0) (hs : u2 / u1 = s) : s * m / c = (u12 * m / u1) / (u12 * c / u2) := by
  rw [← hs]; field_simp

/-- AKMM, footnote 18, p. 519: `h₁₁c/h₁ = (ρ − 1)θ`: the derivative of `h₁` in `c` is
`h₁(ρ − 1)θ/c`. -/
theorem cl_h1_hasDerivAt_c {ω ρ c m : ℝ} (hρ : ρ ≠ 0) (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c)
    (hm : 0 < m) : HasDerivAt (fun c' => clh1 ω ρ c' m)
      (clh1 ω ρ c m * ((ρ - 1) * clTheta ω ρ c m / c)) c := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have hd : HasDerivAt (fun c' => clH ω ρ c' m) ((1 - ω) * (ρ * c ^ (ρ - 1))) c := by
    unfold clH
    exact ((Real.hasDerivAt_rpow_const (Or.inl hc.ne')).const_mul (1 - ω)).add_const _
  have h1 := (Real.hasDerivAt_rpow_const (p := ρ - 1) (Or.inl hc.ne')).const_mul (1 - ω)
  have h2 := hd.rpow_const (p := 1 / ρ - 1) (Or.inl hH.ne')
  have := h1.mul h2
  unfold clh1 clTheta
  refine this.congr_deriv ?_
  unfold clH at hH ⊢
  have hcρ := Real.rpow_pos_of_pos hc ρ
  simp only [Real.rpow_sub_one hc.ne', Real.rpow_sub_one hH.ne']
  field_simp
  ring

/-- AKMM, footnote 18, p. 519: `h₁₂m₁/h₁ = (1 − ρ)θ`: the derivative of `h₁` in `m₁` is
`h₁(1 − ρ)θ/m₁`. -/
theorem cl_h1_hasDerivAt_m {ω ρ c m : ℝ} (hρ : ρ ≠ 0) (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c)
    (hm : 0 < m) : HasDerivAt (fun m' => clh1 ω ρ c m')
      (clh1 ω ρ c m * ((1 - ρ) * clTheta ω ρ c m / m)) m := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have hd : HasDerivAt (fun m' => clH ω ρ c m') (ω * (ρ * m ^ (ρ - 1))) m := by
    unfold clH
    exact ((Real.hasDerivAt_rpow_const (Or.inl hm.ne')).const_mul ω).const_add _
  have := (hd.rpow_const (p := 1 / ρ - 1) (Or.inl hH.ne')).const_mul ((1 - ω) * c ^ (ρ - 1))
  unfold clh1 clTheta
  refine this.congr_deriv ?_
  unfold clH at hH ⊢
  have hmρ := Real.rpow_pos_of_pos hm ρ
  simp only [Real.rpow_sub_one hm.ne', Real.rpow_sub_one hH.ne']
  field_simp

/-- AKMM, footnote 18, p. 519: with `u₁ = f′(h)h₁` and `f″` the derivative of `f′`,
`u₁₁c/u₁ = (f″/f′)h₁c + h₁₁c/h₁` and `u₁₂m₁/u₁ = (f″/f′)h₂m₁ + h₁₂m₁/h₁`. (The book prints
the second as `(f″/f′)h_{2,2} + h_{1,2}m₁/h₁`; the first term is `(f″/f′)h₂m₁`.) -/
theorem cl_footnote_18_identities {ω ρ c m : ℝ} {df d2f : ℝ → ℝ} (hρ : ρ ≠ 0) (hω0 : 0 < ω)
    (hω1 : ω < 1) (hc : 0 < c) (hm : 0 < m)
    (hdf : HasDerivAt df (d2f (clh ω ρ c m)) (clh ω ρ c m)) (hdf0 : df (clh ω ρ c m) ≠ 0) :
    (∃ u11, HasDerivAt (fun c' => df (clh ω ρ c' m) * clh1 ω ρ c' m) u11 c ∧
      u11 * c / (df (clh ω ρ c m) * clh1 ω ρ c m) =
        d2f (clh ω ρ c m) / df (clh ω ρ c m) * clh1 ω ρ c m * c + (ρ - 1) * clTheta ω ρ c m) ∧
    (∃ u12, HasDerivAt (fun m' => df (clh ω ρ c m') * clh1 ω ρ c m') u12 m ∧
      u12 * m / (df (clh ω ρ c m) * clh1 ω ρ c m) =
        d2f (clh ω ρ c m) / df (clh ω ρ c m) * (clh2 ω ρ c m * m) +
          (1 - ρ) * clTheta ω ρ c m) := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have hh1 : 0 < clh1 ω ρ c m := by
    unfold clh1
    have := Real.rpow_pos_of_pos hc (ρ - 1)
    have := Real.rpow_pos_of_pos hH (1 / ρ - 1)
    have : 0 < 1 - ω := by linarith
    positivity
  constructor
  · refine ⟨_, (hdf.comp c (cl_h_hasDerivAt_c hρ hω0 hω1 hc hm)).mul
      (cl_h1_hasDerivAt_c hρ hω0 hω1 hc hm), ?_⟩
    simp only [Function.comp_apply]
    field_simp
  · refine ⟨_, (hdf.comp m (cl_h_hasDerivAt_m hρ hω0 hω1 hc hm)).mul
      (cl_h1_hasDerivAt_m hρ hω0 hω1 hc hm), ?_⟩
    simp only [Function.comp_apply]
    field_simp

/-- The identity `h₂m₁ = θh`. -/
theorem cl_h2_mul {ω ρ c m : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c) (hm : 0 < m) :
    clh2 ω ρ c m * m = clTheta ω ρ c m * clh ω ρ c m := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  unfold clh2 clTheta clh
  rw [Real.rpow_sub_one hm.ne', Real.rpow_sub_one hH.ne']
  field_simp

/-- Along the money-demand curve the scaled money weight `W(ω) = ω(m₁/c)^ρ` tends to zero as
`ω → 0`: `W = ω^{1/(1−ρ)}((1 − ω)s)^{ρ/(ρ−1)}`. -/
theorem cl_weight_tendsto {ρ c s : ℝ} (hρ1 : ρ < 1) (hc : 0 < c) (hs : 0 < s) :
    Tendsto (fun ω => ω * (clDemand ω ρ c s / c) ^ ρ) (𝓝[>] 0) (𝓝 0) := by
  have hρ' : ρ - 1 ≠ 0 := by linarith
  have hρ'' : (1 : ℝ) - ρ ≠ 0 := by linarith
  have h1ρ : 0 < 1 / (1 - ρ) := by have : 0 < 1 - ρ := by linarith
                                   positivity
  set k := ρ / (ρ - 1) with hk
  have hform : ∀ ω, 0 < ω → ω < 1 →
      ω * (clDemand ω ρ c s / c) ^ ρ = ω ^ (1 / (1 - ρ)) * ((1 - ω) * s) ^ k := by
    intro ω hω0 hω1
    have hB : 0 < (1 - ω) * s := mul_pos (by linarith) hs
    unfold clDemand
    rw [mul_div_cancel_left₀ _ hc.ne', ← Real.rpow_mul (by positivity),
      show (1 - ω) / ω * s = (1 - ω) * s * ω⁻¹ by ring, Real.mul_rpow hB.le (by positivity),
      Real.inv_rpow hω0.le, show 1 / (ρ - 1) * ρ = k by rw [hk]; ring]
    have : ω ^ (1 / (1 - ρ)) = ω * (ω ^ k)⁻¹ := by
      rw [← Real.rpow_neg hω0.le, ← Real.rpow_one_add' hω0.le]
      · congr 1; rw [hk]; field_simp; ring
      · rw [hk]; have : 1 + -(ρ / (ρ - 1)) = 1 / (1 - ρ) := by field_simp; ring
        rw [this]; exact h1ρ.ne'
    rw [this]; ring
  have hlim : Tendsto (fun ω : ℝ => ω ^ (1 / (1 - ρ)) * ((1 - ω) * s) ^ k) (𝓝[>] 0)
      (𝓝 (0 ^ (1 / (1 - ρ)) * ((1 - 0) * s) ^ k)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    apply ContinuousAt.mul (Real.continuousAt_rpow_const 0 _ (Or.inr h1ρ.le))
    apply ContinuousAt.rpow_const _ (Or.inl (by simp only [sub_zero, one_mul, ne_eq]; exact hs.ne'))
    exact ((continuousAt_const.sub continuousAt_id).mul continuousAt_const)
  rw [Real.zero_rpow h1ρ.ne', zero_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ω hω
  exact (hform ω hω.1 hω.2).symm

/-- **AKMM, footnote 18, p. 519: the cashless limit.** Fix `c > 0` and the opportunity cost
`s = i/(1 + i) > 0`, and let real balances follow the money demand (17.41). As `ω → 0`:
the money share `θ → 0`, `h → c`, `h₁ → 1`, `h₂m₁ → 0`. If `f′`, `f″` are continuous at `c` and
`f′(c) ≠ 0`, then `η_{u₁,c} = −((f″/f′)h₁c + (ρ − 1)θ) → −f″(c)c/f′(c)` and
`η_{u₁,m₁} = −((f″/f′)h₂m₁ + (1 − ρ)θ) → 0`. -/
theorem cl_footnote_18_limits {ρ c s : ℝ} {df d2f : ℝ → ℝ} (hρ : ρ ≠ 0) (hρ1 : ρ < 1)
    (hc : 0 < c) (hs : 0 < s) (hdfc : ContinuousAt df c) (hd2fc : ContinuousAt d2f c)
    (hdf0 : df c ≠ 0) :
    let m := fun ω => clDemand ω ρ c s
    Tendsto (fun ω => clTheta ω ρ c (m ω)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ω => clh ω ρ c (m ω)) (𝓝[>] 0) (𝓝 c) ∧
      Tendsto (fun ω => clh1 ω ρ c (m ω)) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun ω => clh2 ω ρ c (m ω) * m ω) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ω => -(d2f (clh ω ρ c (m ω)) / df (clh ω ρ c (m ω)) * clh1 ω ρ c (m ω) * c +
        (ρ - 1) * clTheta ω ρ c (m ω))) (𝓝[>] 0) (𝓝 (-(d2f c * c / df c))) ∧
      Tendsto (fun ω => -(d2f (clh ω ρ c (m ω)) / df (clh ω ρ c (m ω)) *
        (clh2 ω ρ c (m ω) * m ω) + (1 - ρ) * clTheta ω ρ c (m ω))) (𝓝[>] 0) (𝓝 0) := by
  intro m
  have hW := cl_weight_tendsto hρ1 hc hs
  set W := fun ω => ω * (clDemand ω ρ c s / c) ^ ρ with hWdef
  have hmpos : ∀ ω, 0 < ω → ω < 1 → 0 < m ω := fun ω h0 h1 => by
    simp only [m, clDemand]
    have : 0 < (1 - ω) / ω * s := by have : 0 < 1 - ω := by linarith
                                     positivity
    positivity
  have hmρ : ∀ ω, 0 < ω → ω < 1 → m ω ^ ρ = c ^ ρ * (m ω / c) ^ ρ := fun ω h0 h1 => by
    rw [← Real.mul_rpow hc.le (div_pos (hmpos ω h0 h1) hc).le, mul_div_cancel₀ _ hc.ne']
  have ev : ∀ᶠ ω in 𝓝[>] (0 : ℝ), 0 < ω ∧ ω < 1 := Ioo_mem_nhdsGT one_pos
  have hcρ := Real.rpow_pos_of_pos hc ρ
  -- H = c^ρ((1 − ω) + W)
  have hHform : ∀ᶠ ω in 𝓝[>] (0 : ℝ), clH ω ρ c (m ω) = c ^ ρ * ((1 - ω) + W ω) := by
    filter_upwards [ev] with ω hω
    simp only [clH, hWdef]
    rw [hmρ ω hω.1 hω.2]; ring
  have hden : Tendsto (fun ω : ℝ => (1 - ω) + W ω) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun ω : ℝ => 1 - ω) (𝓝[>] 0) (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    simpa using this.add hW
  have hH : Tendsto (fun ω => clH ω ρ c (m ω)) (𝓝[>] 0) (𝓝 (c ^ ρ)) := by
    have := hden.const_mul (c ^ ρ)
    rw [mul_one] at this
    exact this.congr' (hHform.mono fun ω h => h.symm)
  have hθ : Tendsto (fun ω => clTheta ω ρ c (m ω)) (𝓝[>] 0) (𝓝 0) := by
    have hq := hW.div hden one_ne_zero
    rw [zero_div] at hq
    refine hq.congr' ?_
    filter_upwards [ev, hHform] with ω hω hHω
    simp only [clTheta, hHω, hWdef]
    rw [hmρ ω hω.1 hω.2]
    field_simp
    rfl
  have hh : Tendsto (fun ω => clh ω ρ c (m ω)) (𝓝[>] 0) (𝓝 c) := by
    have := ((Real.continuousAt_rpow_const (c ^ ρ) (1 / ρ) (Or.inl hcρ.ne')).tendsto).comp hH
    rwa [← Real.rpow_mul hc.le, mul_one_div_cancel hρ, Real.rpow_one] at this
  have hh1 : Tendsto (fun ω => clh1 ω ρ c (m ω)) (𝓝[>] 0) (𝓝 1) := by
    have h1 : Tendsto (fun ω : ℝ => (1 - ω) * c ^ (ρ - 1)) (𝓝[>] 0) (𝓝 (c ^ (ρ - 1))) := by
      have := (((tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_id (x := 𝓝 (0 : ℝ)))).mul (tendsto_const_nhds (x := c ^ (ρ - 1)))).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have h2 := ((Real.continuousAt_rpow_const (c ^ ρ) (1 / ρ - 1)
      (Or.inl hcρ.ne')).tendsto).comp hH
    have := h1.mul h2
    rw [← Real.rpow_mul hc.le, ← Real.rpow_add hc,
      show ρ - 1 + ρ * (1 / ρ - 1) = 0 by field_simp; ring, Real.rpow_zero] at this
    exact this
  have hh2 : Tendsto (fun ω => clh2 ω ρ c (m ω) * m ω) (𝓝[>] 0) (𝓝 0) := by
    have := hθ.mul hh
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [ev] with ω hω
    exact (cl_h2_mul hω.1 hω.2 hc (hmpos ω hω.1 hω.2)).symm
  have hdf : Tendsto (fun ω => df (clh ω ρ c (m ω))) (𝓝[>] 0) (𝓝 (df c)) := hdfc.tendsto.comp hh
  have hd2f : Tendsto (fun ω => d2f (clh ω ρ c (m ω))) (𝓝[>] 0) (𝓝 (d2f c)) :=
    hd2fc.tendsto.comp hh
  have hratio := hd2f.div hdf hdf0
  refine ⟨hθ, hh, hh1, hh2, ?_, ?_⟩
  · have := ((hratio.mul hh1).mul_const c).add (hθ.const_mul (ρ - 1))
    have := this.neg
    convert this using 2
    ring
  · have := (hratio.mul hh2).add (hθ.const_mul (1 - ρ))
    have := this.neg
    convert this using 2
    ring

end AKMM.Money
