/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.SearchModel

/-!
# Search unemployment: the reservation wage

SLP §10.7, Exercise 10.7d–h, pp. 306–307. Let `v` be a continuous nondecreasing solution of (1)
(`SearchSol`; the fixed point of Exercise 10.7c is one: `searchSol_of_fixed`), and
`A = β ∫ v dμ`. Suppose `μ` puts positive mass on positive wages (with a density this always
holds). Write `F(w) = μ([0, w))`; with a density this is the book's `F(w) = ∫₀ʷ f`.

* `SearchSol.nonneg`, `SearchSol.v_zero`, `SearchSol.A_pos`: `v ≥ 0`, `v(0) = A` and `A > 0`.
* **Exercise 10.7d** (`ex_10_7d`): there is a unique `w*` with
  `v(w*) = U(w*) + β[(1 − θ)v(w*) + θA] = A`, and then `U(w*) = (1 − β)A` (3).
* **Exercise 10.7e** (`ex_10_7e`): `v(w) = A` for `w < w*` and
  `v(w) = [U(w) + βθA]/[1 − β(1 − θ)]` for `w ≥ w*` (4).
* **Exercise 10.7f** (`ex_10_7f`): `(1 − β)A = β/[1 + βθ − βF(w*)] ∫_{w ≥ w*} U dμ` (5).
* **Exercise 10.7g** (`ex_10_7g`): `[1 + βθ − βF(w*)]U(w*) = β ∫_{w ≥ w*} U dμ` (6), and `w*` is the
  only solution of (6): its left side minus its right side, `resΨ`, is strictly increasing in
  `w` (`resΨ_strictMono`).
* **Exercise 10.7h** (`ex_10_7h_θ`, `ex_10_7h_β`): the reservation wage is strictly decreasing in
  the job-loss probability `θ` and, for `θ < 1`, strictly increasing in the discount factor `β`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {U : ℝ → ℝ} {θ β wbar : ℝ} (h : SearchHyp U θ β wbar) (μ : Measure (Icc (0 : ℝ) wbar))

/-- `v` is a continuous nondecreasing solution of the functional equation (1). -/
structure SearchSol (v : Icc (0 : ℝ) wbar → ℝ) : Prop where
  cont : Continuous v
  mono : Monotone v
  fe : ∀ w, v w = max (U w.1 + β * ((1 - θ) * v w + θ * v (w0 h.wbar_pos.le)))
    (β * ∫ z, v z ∂μ)

variable {h} {μ}

/-- The fixed point of Exercise 10.7c gives a solution. -/
theorem searchSol_of_fixed (h : SearchHyp U θ β wbar) (μ : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure (lossMeasure θ)]
    {v : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ}
    (hv : bellman (searchModel h.wbar_pos.le U θ β μ) (search_boundedDP h μ) v = v)
    (s₀ : Two × Icc (0 : ℝ) wbar) : SearchSol h μ fun w => v (w, s₀) := by
  obtain ⟨-, hfe, -, hmono, -⟩ := ex_10_7c h μ hv s₀
  exact ⟨v.continuous.comp (continuous_id.prodMk continuous_const), hmono, hfe⟩

theorem SearchHyp.U_nonneg (h : SearchHyp U θ β wbar) (w : Icc (0 : ℝ) wbar) : 0 ≤ U w.1 := by
  have := h.U_mono.monotoneOn (left_mem_Icc.2 h.wbar_pos.le) w.2 w.2.1
  rwa [h.U_zero] at this

theorem SearchHyp.integrable_U (h : SearchHyp U θ β wbar) (μ : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure μ] : Integrable (fun w : Icc (0 : ℝ) wbar => U w.1) μ :=
  (h.U_cont.comp_continuous continuous_subtype_val fun w => w.2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

namespace SearchSol

variable {h : SearchHyp U θ β wbar} {v : Icc (0 : ℝ) wbar → ℝ} (hs : SearchSol h μ v)
include hs

theorem integrable [IsProbabilityMeasure μ] : Integrable v μ :=
  hs.cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace v)

/-- `v ≥ 0`: at the bottom, `v(0) ≥ β ∫ v dμ ≥ β v(0)`. -/
theorem nonneg [IsProbabilityMeasure μ] (w : Icc (0 : ℝ) wbar) : 0 ≤ v w := by
  have hmin : ∀ z, v (w0 h.wbar_pos.le) ≤ v z := fun z => hs.mono z.2.1
  have hA : v (w0 h.wbar_pos.le) ≤ ∫ z, v z ∂μ := by
    have := integral_mono (integrable_const (v (w0 h.wbar_pos.le))) hs.integrable hmin
    simpa using this
  have h0 : β * ∫ z, v z ∂μ ≤ v (w0 h.wbar_pos.le) := by
    rw [hs.fe (w0 h.wbar_pos.le)]; exact le_max_right _ _
  have : 0 ≤ v (w0 h.wbar_pos.le) := by
    nlinarith [h.β_pos, h.β_lt, mul_le_mul_of_nonneg_left hA h.β_pos.le]
  exact this.trans (hmin w)

/-- `v(0) = A`. -/
theorem v_zero [IsProbabilityMeasure μ] : v (w0 h.wbar_pos.le) = β * ∫ z, v z ∂μ := by
  have hA : 0 ≤ β * ∫ z, v z ∂μ :=
    mul_nonneg h.β_pos.le (integral_nonneg fun z => hs.nonneg z)
  have he := hs.fe (w0 h.wbar_pos.le)
  have hU0 : U (w0 h.wbar_pos.le).1 = 0 := h.U_zero
  rw [hU0] at he
  rcases le_total (β * ((1 - θ) * v (w0 h.wbar_pos.le) + θ * v (w0 h.wbar_pos.le)))
    (β * ∫ z, v z ∂μ) with hle | hle
  · rw [he, zero_add, max_eq_right hle]
  · rw [zero_add, max_eq_left hle] at he
    have : v (w0 h.wbar_pos.le) = 0 := by nlinarith [h.β_lt]
    linarith

/-- The value of working at `w`: `U(w) + β[(1 − θ)v(w) + θA]`. -/
theorem fe' [IsProbabilityMeasure μ] (w : Icc (0 : ℝ) wbar) :
    v w = max (U w.1 + β * ((1 - θ) * v w + θ * (β * ∫ z, v z ∂μ))) (β * ∫ z, v z ∂μ) := by
  have := hs.fe w
  rw [hs.v_zero] at this
  exact this

/-- `A > 0` when `μ` puts mass on positive wages. -/
theorem A_pos [IsProbabilityMeasure μ] (hμ : 0 < μ {w | 0 < w.1}) : 0 < β * ∫ z, v z ∂μ := by
  refine mul_pos h.β_pos ?_
  have hpos : ∀ w : Icc (0 : ℝ) wbar, 0 < w.1 → 0 < v w := fun w hw => by
    have hUw : 0 < U w.1 := by
      have := h.U_mono (left_mem_Icc.2 h.wbar_pos.le) w.2 hw
      rwa [h.U_zero] at this
    have := le_max_left _ _ |>.trans_eq (hs.fe w).symm
    have h1 := hs.nonneg w
    have h2 := hs.nonneg (w0 h.wbar_pos.le)
    have : 0 ≤ β * ((1 - θ) * v w + θ * v (w0 h.wbar_pos.le)) :=
      mul_nonneg h.β_pos.le (add_nonneg (mul_nonneg (by linarith [h.θ_le]) h1)
        (mul_nonneg h.θ_nonneg h2))
    linarith
  rw [integral_pos_iff_support_of_nonneg (fun z => hs.nonneg z) hs.integrable]
  refine hμ.trans_le (measure_mono fun w hw => ?_)
  exact (hpos w hw).ne'

/-- The value of working is strictly increasing in `w`. -/
theorem work_strictMono [IsProbabilityMeasure μ] :
    StrictMono fun w : Icc (0 : ℝ) wbar =>
      U w.1 + β * ((1 - θ) * v w + θ * (β * ∫ z, v z ∂μ)) := by
  intro w w' hww'
  have hU := h.U_mono w.2 w'.2 hww'
  have hv := hs.mono hww'.le
  have : 0 ≤ β * (1 - θ) := mul_nonneg h.β_pos.le (by linarith [h.θ_le])
  nlinarith

end SearchSol

/-- **Exercise 10.7d.** There is a unique `w*` with `v(w*) = U(w*) + β[(1 − θ)v(w*) + θA] = A`;
it satisfies `U(w*) = (1 − β)A` (3), and `w* > 0`. -/
theorem ex_10_7d [IsProbabilityMeasure μ] {h : SearchHyp U θ β wbar} {v : Icc (0 : ℝ) wbar → ℝ}
    (hs : SearchSol h μ v) (hμ : 0 < μ {w | 0 < w.1}) :
    (∃! ws : Icc (0 : ℝ) wbar, v ws = U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) ∧
      v ws = β * ∫ z, v z ∂μ) ∧
    ∀ ws : Icc (0 : ℝ) wbar, U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) =
        β * ∫ z, v z ∂μ →
      U ws.1 = (1 - β) * (β * ∫ z, v z ∂μ) ∧ 0 < ws.1 := by
  set A := β * ∫ z, v z ∂μ
  set Vw : Icc (0 : ℝ) wbar → ℝ := fun w => U w.1 + β * ((1 - θ) * v w + θ * A)
  have hA := hs.A_pos hμ
  have hmono : StrictMono Vw := hs.work_strictMono
  have hfe : ∀ w, v w = max (Vw w) A := hs.fe'
  -- `Vw(0) < A ≤ Vw(w̄)`
  have hlow : Vw (w0 h.wbar_pos.le) < A := by
    have hv0 := hs.v_zero
    have hU0 : U (w0 h.wbar_pos.le).1 = 0 := h.U_zero
    change U (w0 h.wbar_pos.le).1 + β * ((1 - θ) * v (w0 h.wbar_pos.le) + θ * A) < A
    rw [hU0, hv0]
    nlinarith [h.β_lt]
  set wt : Icc (0 : ℝ) wbar := ⟨wbar, h.wbar_pos.le, le_rfl⟩
  have hhigh : A ≤ Vw wt := by
    by_contra hlt
    have hconst : ∀ w, v w = A := fun w => by
      rw [hfe w, max_eq_right ((hmono.monotone (show w ≤ wt from w.2.2)).trans (not_le.1 hlt).le)]
    have hint : ∫ z, v z ∂μ = A := by
      simp_rw [hconst]
      simp
    have : A = β * A := by
      change β * ∫ z, v z ∂μ = β * A
      rw [hint]
    nlinarith [h.β_lt]
  -- the intermediate value theorem along `[0, w̄]`
  have hcont : Continuous Vw :=
    (h.U_cont.comp_continuous continuous_subtype_val fun w => w.2).add
      (continuous_const.mul ((continuous_const.mul hs.cont).add continuous_const))
  have hivt := intermediate_value_Icc h.wbar_pos.le
    (hcont.comp (continuous_projIcc (h := h.wbar_pos.le))).continuousOn
  simp only [Function.comp_apply, projIcc_left, projIcc_right] at hivt
  obtain ⟨x, -, hx⟩ := hivt ⟨(hlow.trans_eq (by rfl)).le, hhigh⟩
  set ws := projIcc 0 wbar h.wbar_pos.le x
  have hx' : Vw ws = A := hx
  have hvws : v ws = A := by rw [hfe, hx', max_self]
  have hprop : ∀ w : Icc (0 : ℝ) wbar, Vw w = A →
      U w.1 = (1 - β) * A ∧ 0 < w.1 := fun w hw => by
    have hvw : v w = A := by rw [hfe, hw, max_self]
    have hU : U w.1 = (1 - β) * A := by
      change U w.1 + β * ((1 - θ) * v w + θ * A) = A at hw
      rw [hvw] at hw
      linarith
    refine ⟨hU, lt_of_le_of_ne w.2.1 fun h0 => ?_⟩
    have : U w.1 = 0 := by rw [← h0]; exact h.U_zero
    nlinarith [h.β_lt]
  refine ⟨⟨ws, ⟨hvws.trans hx'.symm, hvws⟩, fun w hw => ?_⟩, hprop⟩
  have hVw : Vw w = A := hw.1.symm.trans hw.2
  exact hmono.injective (hVw.trans hx'.symm)

/-- **Exercise 10.7e.** With `Vw(w*) = A`, `v(w) = A` below `w*` and
`v(w) = [U(w) + βθA]/[1 − β(1 − θ)]` from `w*` on (4). -/
theorem ex_10_7e [IsProbabilityMeasure μ] {h : SearchHyp U θ β wbar} {v : Icc (0 : ℝ) wbar → ℝ}
    (hs : SearchSol h μ v) {ws : Icc (0 : ℝ) wbar}
    (hws : U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) = β * ∫ z, v z ∂μ)
    (w : Icc (0 : ℝ) wbar) :
    (w < ws → v w = β * ∫ z, v z ∂μ) ∧
      (ws ≤ w → v w = (U w.1 + β * θ * (β * ∫ z, v z ∂μ)) / (1 - β * (1 - θ))) := by
  set A := β * ∫ z, v z ∂μ
  have hmono := hs.work_strictMono
  have hfe := hs.fe' w
  refine ⟨fun hlt => ?_, fun hle => ?_⟩
  · rw [hfe, max_eq_right ((hmono hlt).le.trans_eq hws)]
  · have hge := (hmono.monotone hle)
    rw [hws] at hge
    rw [max_eq_left hge] at hfe
    have hD : 0 < 1 - β * (1 - θ) := by nlinarith [h.β_lt, h.θ_nonneg, h.β_pos]
    rw [eq_div_iff hD.ne']
    linarith

/-- `F(w) = μ([0, w))`. -/
noncomputable def cdfF (μ : Measure (Icc (0 : ℝ) wbar)) (w : Icc (0 : ℝ) wbar) : ℝ :=
  (μ (Iio w)).toReal

theorem cdfF_nonneg (w : Icc (0 : ℝ) wbar) : 0 ≤ cdfF μ w := ENNReal.toReal_nonneg

theorem cdfF_le_one [IsProbabilityMeasure μ] (w : Icc (0 : ℝ) wbar) : cdfF μ w ≤ 1 := by
  unfold cdfF
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

/-- **Exercise 10.7f** (5): `(1 − β)A = β/[1 + βθ − βF(w*)] ∫_{w ≥ w*} U dμ`. -/
theorem ex_10_7f [IsProbabilityMeasure μ] {h : SearchHyp U θ β wbar} {v : Icc (0 : ℝ) wbar → ℝ}
    (hs : SearchSol h μ v) {ws : Icc (0 : ℝ) wbar}
    (hws : U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) = β * ∫ z, v z ∂μ) :
    (1 - β) * (β * ∫ z, v z ∂μ) =
      β / (1 + β * θ - β * cdfF μ ws) * ∫ w in Ici ws, U w.1 ∂μ := by
  set A := β * ∫ z, v z ∂μ
  set Fs := cdfF μ ws
  have hD : 0 < 1 - β * (1 - θ) := by nlinarith [h.β_lt, h.θ_nonneg, h.β_pos]
  have hF1 := cdfF_le_one (μ := μ) ws
  have hF0 := cdfF_nonneg (μ := μ) ws
  have hE : 0 < 1 + β * θ - β * Fs := by nlinarith [h.β_lt, h.θ_nonneg, h.β_pos]
  -- split `∫ v` at `w*`
  have hsplit : ∫ z, v z ∂μ = ∫ z in Iio ws, v z ∂μ + ∫ z in Ici ws, v z ∂μ := by
    rw [← integral_add_compl (measurableSet_Iio (a := ws)) hs.integrable, compl_Iio]
  have hlow : ∫ z in Iio ws, v z ∂μ = Fs * A := by
    rw [setIntegral_congr_fun measurableSet_Iio fun w hw => (ex_10_7e hs hws w).1 hw,
      setIntegral_const, smul_eq_mul]
    rfl
  have hμc : (μ (Ici ws)).toReal = 1 - Fs := by
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, ENNReal.toReal_sub_of_le
      prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
    rfl
  have hhigh : ∫ z in Ici ws, v z ∂μ =
      (∫ z in Ici ws, U z.1 ∂μ + β * θ * A * (1 - Fs)) / (1 - β * (1 - θ)) := by
    rw [setIntegral_congr_fun measurableSet_Ici fun w hw => (ex_10_7e hs hws w).2 hw,
      integral_div, integral_add (h.integrable_U μ).integrableOn (integrable_const _),
      setIntegral_const, smul_eq_mul, measureReal_def, hμc]
    ring
  have hAeq : A = β * (Fs * A + (∫ z in Ici ws, U z.1 ∂μ + β * θ * A * (1 - Fs)) /
      (1 - β * (1 - θ))) := by
    change β * ∫ z, v z ∂μ = _
    rw [hsplit, hlow, hhigh]
  rw [div_mul_eq_mul_div, eq_div_iff hE.ne']
  field_simp at hAeq
  linear_combination hAeq

/-- `Ψ(w) = [1 + βθ − βF(w)]U(w) − β ∫_{w′ ≥ w} U dμ`: equation (6) says `Ψ(w*) = 0`. -/
noncomputable def resΨ (μ : Measure (Icc (0 : ℝ) wbar)) (U : ℝ → ℝ) (β θ : ℝ)
    (w : Icc (0 : ℝ) wbar) : ℝ :=
  (1 + β * θ - β * cdfF μ w) * U w.1 - β * ∫ w' in Ici w, U w'.1 ∂μ

/-- **Exercise 10.7g** (existence): `w*` satisfies (6). -/
theorem ex_10_7g [IsProbabilityMeasure μ] {h : SearchHyp U θ β wbar} {v : Icc (0 : ℝ) wbar → ℝ}
    (hs : SearchSol h μ v) {ws : Icc (0 : ℝ) wbar}
    (hws : U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) = β * ∫ z, v z ∂μ) :
    resΨ μ U β θ ws = 0 := by
  have h5 := ex_10_7f hs hws
  have hvws : v ws = β * ∫ z, v z ∂μ := by rw [hs.fe', hws, max_self]
  have h3 : U ws.1 = (1 - β) * (β * ∫ z, v z ∂μ) := by
    rw [hvws] at hws; linarith
  have hF1 := cdfF_le_one (μ := μ) ws
  have hE : 0 < 1 + β * θ - β * cdfF μ ws := by nlinarith [h.β_lt, h.θ_nonneg, h.β_pos]
  unfold resΨ
  rw [h3, h5, div_mul_eq_mul_div, mul_div_cancel₀ _ hE.ne']
  ring

/-- **Exercise 10.7g** (uniqueness): `Ψ` is strictly increasing, so (6) has at most one root. -/
theorem resΨ_strictMono [IsProbabilityMeasure μ] (h : SearchHyp U θ β wbar) :
    StrictMono (resΨ μ U β θ) := by
  have hUi : Integrable (fun w : Icc (0 : ℝ) wbar => U w.1) μ :=
    (h.U_cont.comp_continuous continuous_subtype_val fun w => w.2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  intro w₁ w₂ h12
  set m := (μ (Ico w₁ w₂)).toReal
  have hF : cdfF μ w₂ = cdfF μ w₁ + m := by
    unfold cdfF
    have hd : Disjoint (Iio w₁) (Ico w₁ w₂) := Set.disjoint_left.2 fun x hx hx' =>
      not_le.2 (show x < w₁ from hx) hx'.1
    rw [← Iio_union_Ico_eq_Iio h12.le, measure_union hd measurableSet_Ico,
      ENNReal.toReal_add (measure_ne_top _ _)
      (measure_ne_top _ _)]
  have hI : ∫ w in Ici w₁, U w.1 ∂μ = ∫ w in Ico w₁ w₂, U w.1 ∂μ + ∫ w in Ici w₂, U w.1 ∂μ := by
    have hd : Disjoint (Ico w₁ w₂) (Ici w₂) := Set.disjoint_left.2 fun x hx hx' =>
      not_le.2 hx.2 (show w₂ ≤ x from hx')
    rw [← Ico_union_Ici_eq_Ici h12.le, setIntegral_union hd measurableSet_Ici
      hUi.integrableOn hUi.integrableOn]
  have hIco : U w₁.1 * m ≤ ∫ w in Ico w₁ w₂, U w.1 ∂μ := by
    have := setIntegral_mono_on (s := Ico w₁ w₂) (integrableOn_const (measure_ne_top _ _))
      hUi.integrableOn measurableSet_Ico (fun w hw => h.U_mono.monotoneOn w₁.2 w.2 hw.1)
      (μ := μ) (f := fun _ => U w₁.1)
    rw [setIntegral_const, smul_eq_mul, measureReal_def] at this
    linarith
  have hU12 : U w₁.1 < U w₂.1 := h.U_mono w₁.2 w₂.2 h12
  have hF1 := cdfF_le_one (μ := μ) w₂
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hE : 0 < 1 + β * θ - β * cdfF μ w₂ := by nlinarith [h.β_lt, h.θ_nonneg, h.β_pos]
  unfold resΨ
  rw [hI, hF]
  rw [hF] at hE
  nlinarith [mul_le_mul_of_nonneg_left hIco h.β_pos.le, mul_pos hE (sub_pos.2 hU12)]

/-- **Exercise 10.7g.** `w*` is the unique solution of (6). -/
theorem ex_10_7g_unique [IsProbabilityMeasure μ] {h : SearchHyp U θ β wbar}
    {v : Icc (0 : ℝ) wbar → ℝ} (hs : SearchSol h μ v) {ws : Icc (0 : ℝ) wbar}
    (hws : U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) = β * ∫ z, v z ∂μ)
    (w : Icc (0 : ℝ) wbar) (hw : resΨ μ U β θ w = 0) : w = ws :=
  (resΨ_strictMono h).injective (hw.trans (ex_10_7g hs hws).symm)

/-- **Exercise 10.7h** (`θ`). The reservation wage falls when the job-loss probability rises: if
`w₁ > 0` solves (6) at `θ₁` and `w₂` solves it at `θ₂ > θ₁`, then `w₂ < w₁`. -/
theorem ex_10_7h_θ [IsProbabilityMeasure μ] {θ₁ θ₂ : ℝ} (h₂ : SearchHyp U θ₂ β wbar)
    {w₁ w₂ : Icc (0 : ℝ) wbar} (hw₁ : resΨ μ U β θ₁ w₁ = 0) (hw₂ : resΨ μ U β θ₂ w₂ = 0)
    (hθ : θ₁ < θ₂) (hpos : 0 < w₁.1) : w₂ < w₁ := by
  have hU : 0 < U w₁.1 := by
    have := h₂.U_mono (left_mem_Icc.2 h₂.wbar_pos.le) w₁.2 hpos
    rwa [h₂.U_zero] at this
  have hgt : resΨ μ U β θ₂ w₂ < resΨ μ U β θ₂ w₁ := by
    have : resΨ μ U β θ₂ w₁ = resΨ μ U β θ₁ w₁ + β * (θ₂ - θ₁) * U w₁.1 := by
      unfold resΨ; ring
    rw [this, hw₁, hw₂]
    have := mul_pos (mul_pos h₂.β_pos (sub_pos.2 hθ)) hU
    linarith
  exact (resΨ_strictMono h₂).lt_iff_lt.1 hgt

/-- **Exercise 10.7h** (`β`). For `θ < 1` the reservation wage rises with patience: if `w₁ > 0`
solves (6) at `β₁` and `w₂` solves it at `β₂ > β₁`, then `w₁ < w₂`. -/
theorem ex_10_7h_β [IsProbabilityMeasure μ] {β₁ β₂ : ℝ} (h₂ : SearchHyp U θ β₂ wbar)
    (hθ1 : θ < 1) {w₁ w₂ : Icc (0 : ℝ) wbar} (hw₁ : resΨ μ U β₁ θ w₁ = 0)
    (hw₂ : resΨ μ U β₂ θ w₂ = 0) (hβ : β₁ < β₂) (hpos : 0 < w₁.1) : w₁ < w₂ := by
  have hUi : Integrable (fun w : Icc (0 : ℝ) wbar => U w.1) μ :=
    (h₂.U_cont.comp_continuous continuous_subtype_val fun w => w.2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hU : 0 < U w₁.1 := by
    have := h₂.U_mono (left_mem_Icc.2 h₂.wbar_pos.le) w₁.2 hpos
    rwa [h₂.U_zero] at this
  -- `∫_{w ≥ w₁} U ≥ U(w₁)(1 − F(w₁))`
  have hμc : (μ (Ici w₁)).toReal = 1 - cdfF μ w₁ := by
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, ENNReal.toReal_sub_of_le
      prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
    rfl
  have hI : U w₁.1 * (1 - cdfF μ w₁) ≤ ∫ w in Ici w₁, U w.1 ∂μ := by
    have := setIntegral_mono_on (integrableOn_const (measure_ne_top _ _))
      hUi.integrableOn measurableSet_Ici (fun w hw => h₂.U_mono.monotoneOn w₁.2 w.2 hw)
      (μ := μ) (f := fun _ => U w₁.1)
    rw [setIntegral_const, smul_eq_mul, measureReal_def, hμc] at this
    linarith
  have hlt : resΨ μ U β₂ θ w₁ < resΨ μ U β₁ θ w₁ := by
    have e : resΨ μ U β₂ θ w₁ - resΨ μ U β₁ θ w₁ = (β₂ - β₁) *
        ((θ - cdfF μ w₁) * U w₁.1 - ∫ w in Ici w₁, U w.1 ∂μ) := by
      unfold resΨ; ring
    have : (θ - cdfF μ w₁) * U w₁.1 - ∫ w in Ici w₁, U w.1 ∂μ < 0 := by
      nlinarith
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 hβ) this]
  rw [hw₁, ← hw₂] at hlt
  exact (resΨ_strictMono h₂).lt_iff_lt.1 hlt

end StokeyLucasPrescott.StochasticApplications
