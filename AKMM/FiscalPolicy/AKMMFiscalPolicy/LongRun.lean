/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFiscalPolicy.DistortionaryTaxes
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Long-run distortions and GHH labour supply

AKMM, §15.3.1, (15.8)–(15.12), pp. 447–448.

* (15.8): in a steady state with constant taxes the Euler equation (15.6) becomes
  `1 = β[1 + (1 − τ_k)(r − δ)]` (`eq_15_8`), and the labour condition (15.9) holds
  (`eq_15_9`). Equivalently `r = δ + ρ/(1 − τ_k)`, `ρ = (1 − β)/β` (`lr_rent_iff`), so "a higher
  capital income tax `τ_k` must increase the steady-state equilibrium rental rate"
  (`lr_rent_strictMonoOn`).
* Cobb–Douglas `f = k^αℓ^{1−α}`: partial derivatives `f₁ = α(k/ℓ)^{α−1}`, `f₂ = (1 − α)(k/ℓ)^α`
  (`lr_cd_hasDerivAt_k`, `lr_cd_hasDerivAt_l`), and (15.11)
  `k/ℓ = (α(1 − τ_k)/(ρ + δ(1 − τ_k)))^{1/(1−α)}` (`eq_15_11`). The ratio is strictly decreasing
  in `τ_k` (`lr_ratio_strictAntiOn`), and so is the wage (15.10) (`lr_wage_strictAntiOn`);
  `r` and `w` depend on `τ_k` only (`lrRent`, `lrWage` take no `τ_ℓ`, `τ_c`).
* GHH utility `log(c − ℓ^{1+1/φ}/(1 + 1/φ))` (`ghhU`) has partials `u₁ = 1/(c − v)`,
  `u₂ = −ℓ^{1/φ}/(c − v)` (`ghh_partials`), so (15.9) gives (15.12)
  `ℓ = ((1 − τ_ℓ)/(1 + τ_c))^φw^φ` (`eq_15_12`): consumption drops out. Hours fall with `τ_ℓ`,
  with `τ_c` and, through `w`, with `τ_k` (`lr_hours_strictAntiOn_labour`,
  `lr_hours_strictAntiOn_cons`, `lr_hours_strictAntiOn_capital`).

Departures: none.
-/

namespace AKMM.FiscalPolicy

open Real

/-- **(15.8)** (AKMM, p. 447): at a household optimum that is a steady state (constant
`c, ℓ, k > 0` and constant `τ_c > −1`, `τ_k`, `r` at dates `0, 1`) with `u` differentiable and
`u₁ ≠ 0`, `1 = β[1 + (1 − τ_k)(r − δ)]`. -/
theorem eq_15_8 {β : ℝ} {u : ℝ → ℝ → ℝ} {δ K0 : ℝ} {p : DTPolicy} {w r : ℕ → ℝ} {x : DTPlan}
    (hx : dtHHOptimal β u δ K0 p w r x) (hβ : 0 < β) {c l k τc τk r0 a b : ℝ}
    (hc : x.c 0 = c ∧ x.c 1 = c) (hl : x.l 0 = l ∧ x.l 1 = l) (hk : x.k 1 = k) (hk0 : 0 < k)
    (hτc : p.τc 0 = τc ∧ p.τc 1 = τc) (hτk : p.τk 1 = τk) (hr : r 1 = r0) (hτ : 0 < 1 + τc)
    (hu : DTPartials u c l a b) (ha : a ≠ 0) :
    1 = β * (1 + (1 - τk) * (r0 - δ)) := by
  have h := eq_15_6 hx 0 (by rw [zero_add, hk]; exact hk0) hβ
    (by rw [hτc.1]; exact hτ) (by rw [zero_add, hτc.2]; exact hτ)
    (by rw [hc.1, hl.1]; exact hu) (by rw [zero_add, hc.2, hl.2]; exact hu) ha
  rw [zero_add, hτc.1, hτc.2, hτk, hr, div_self hτ.ne', div_self ha, one_mul] at h
  exact h

/-- **(15.9)** (AKMM, p. 448): in a steady state, `−u₂(c, ℓ) = ((1 − τ_ℓ)/(1 + τ_c))wu₁(c, ℓ)`. -/
theorem eq_15_9 {β : ℝ} {u : ℝ → ℝ → ℝ} {δ K0 : ℝ} {p : DTPolicy} {w r : ℕ → ℝ} {x : DTPlan}
    (hx : dtHHOptimal β u δ K0 p w r x) (hβ : 0 < β) {c l τc τl w0 a b : ℝ}
    (hc : x.c 0 = c) (hl : x.l 0 = l) (hτc : p.τc 0 = τc) (hτl : p.τl 0 = τl) (hw : w 0 = w0)
    (hτ : 1 + τc ≠ 0) (hu : DTPartials u c l a b) :
    -b = (1 - τl) / (1 + τc) * w0 * a := by
  have h := dt_labour_foc hx 0 hβ (by rw [hτc]; exact hτ) (by rw [hc, hl]; exact hu)
  rwa [hτc, hτl, hw] at h

/-- The household's rate of time preference `ρ = (1 − β)/β` (AKMM, p. 448). -/
noncomputable def lrRho (β : ℝ) : ℝ := (1 - β) / β

/-- The steady-state rental rate `r = δ + ρ/(1 − τ_k)` implied by (15.8). -/
noncomputable def lrRent (β δ τk : ℝ) : ℝ := δ + lrRho β / (1 - τk)

/-- AKMM, p. 448: for `β > 0` and `τ_k < 1`, (15.8) holds iff `r = δ + ρ/(1 − τ_k)`. -/
theorem lr_rent_iff {β δ τk r : ℝ} (hβ : 0 < β) (hτ : τk < 1) :
    1 = β * (1 + (1 - τk) * (r - δ)) ↔ r = lrRent β δ τk := by
  have h1 : (1 - τk) ≠ 0 := by linarith
  unfold lrRent lrRho
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- AKMM, p. 448: "a higher capital income tax `τ_k` must increase the steady-state equilibrium
rental rate for capital `r`" (for `0 < β < 1`). -/
theorem lr_rent_strictMonoOn {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    StrictMonoOn (lrRent β δ) (Set.Iio 1) := by
  intro a ha b hb hab
  have ha' : 0 < 1 - a := by have := Set.mem_Iio.mp ha; linarith
  have hb' : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  unfold lrRent
  have : lrRho β / (1 - a) < lrRho β / (1 - b) :=
    div_lt_div_of_pos_left hρ hb' (by linarith)
  linarith

/-- AKMM, p. 448: Cobb–Douglas `f(k, ℓ) = k^αℓ^{1−α}` has `f₁ = α(k/ℓ)^{α−1}` at `k, ℓ > 0`. -/
theorem lr_cd_hasDerivAt_k {α k l : ℝ} (hk : 0 < k) (hl : 0 < l) :
    HasDerivAt (fun k => k ^ α * l ^ (1 - α)) (α * (k / l) ^ (α - 1)) k := by
  have h := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hk.ne')).mul_const (l ^ (1 - α))
  convert h using 1
  rw [Real.div_rpow hk.le hl.le, div_eq_mul_inv, ← Real.rpow_neg hl.le, neg_sub]
  ring

/-- AKMM, (15.10), p. 448: Cobb–Douglas has `f₂ = (1 − α)(k/ℓ)^α` at `k, ℓ > 0`. -/
theorem lr_cd_hasDerivAt_l {α k l : ℝ} (hk : 0 < k) (hl : 0 < l) :
    HasDerivAt (fun l => k ^ α * l ^ (1 - α)) ((1 - α) * (k / l) ^ α) l := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hl.ne')).const_mul (k ^ α)
  convert h using 1
  rw [Real.div_rpow hk.le hl.le, div_eq_mul_inv, ← Real.rpow_neg hl.le,
    show (1 - α - 1) = -α by ring]
  ring

/-- `s(τ_k) = α(1 − τ_k)/(ρ + δ(1 − τ_k))`, the base of (15.11), equal to `(k/ℓ)^{1−α}`. -/
noncomputable def lrS (α β δ τk : ℝ) : ℝ := α * (1 - τk) / (lrRho β + δ * (1 - τk))

/-- The steady-state capital–labour ratio (15.11). -/
noncomputable def lrRatio (α β δ τk : ℝ) : ℝ := lrS α β δ τk ^ (1 / (1 - α))

/-- The steady-state wage `w = (1 − α)(k/ℓ)^α` (15.10). -/
noncomputable def lrWage (α β δ τk : ℝ) : ℝ := (1 - α) * lrRatio α β δ τk ^ α

/-- AKMM, p. 448: `s(τ_k) = α/r` with `r = δ + ρ/(1 − τ_k)` from (15.8). -/
theorem lr_s_eq {α β δ τk : ℝ} (hτ : τk < 1) (hr : 0 < lrRent β δ τk) :
    lrS α β δ τk = α / lrRent β δ τk := by
  have h1 : (1 - τk) ≠ 0 := by linarith
  have h2 : lrRho β + δ * (1 - τk) ≠ 0 := by
    have : lrRent β δ τk = (lrRho β + δ * (1 - τk)) / (1 - τk) := by
      unfold lrRent
      field_simp
      ring
    intro h
    rw [this, h, zero_div] at hr
    exact lt_irrefl 0 hr
  unfold lrS lrRent
  field_simp
  ring

/-- **(15.11)** (AKMM, p. 448): with Cobb–Douglas `r = α(k/ℓ)^{α−1}` and (15.8), the
steady-state capital–labour ratio is `k/ℓ = (α(1 − τ_k)/(ρ + δ(1 − τ_k)))^{1/(1−α)}`
(for `0 < α < 1`, `0 < β`, `τ_k < 1`, `k/ℓ > 0`). -/
theorem eq_15_11 {α β δ τk x : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hτ : τk < 1)
    (hx : 0 < x) (h158 : 1 = β * (1 + (1 - τk) * (α * x ^ (α - 1) - δ))) :
    x = lrRatio α β δ τk := by
  have hr := (lr_rent_iff hβ hτ).mp h158
  have hrpos : 0 < lrRent β δ τk := by rw [← hr]; positivity
  unfold lrRatio
  rw [lr_s_eq hτ hrpos, ← hr]
  have : α / (α * x ^ (α - 1)) = x ^ (1 - α) := by
    rw [div_mul_eq_div_div, div_self hα0.ne', one_div, ← Real.rpow_neg hx.le, neg_sub]
  rw [this, ← Real.rpow_mul hx.le, mul_one_div_cancel (by linarith), Real.rpow_one]

/-- AKMM, p. 448: `s(τ_k)` is strictly decreasing in `τ_k < 1` (for `ρ > 0`, `δ ≥ 0`, `α > 0`). -/
theorem lr_s_strictAntiOn {α β δ : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) :
    StrictAntiOn (lrS α β δ) (Set.Iio 1) := by
  intro a ha b hb hab
  have ha' : 0 < 1 - a := by have := Set.mem_Iio.mp ha; linarith
  have hb' : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  unfold lrS
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hα hρ]

/-- AKMM, p. 448: "a higher `τ_k` depresses the steady-state capital-labor ratio". -/
theorem lr_ratio_strictAntiOn {α β δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) : StrictAntiOn (lrRatio α β δ) (Set.Iio 1) := by
  intro a ha b hb hab
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hsb : 0 < lrS α β δ b := by
    have : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
    unfold lrS
    positivity
  unfold lrRatio
  exact Real.rpow_lt_rpow hsb.le (lr_s_strictAntiOn hα0 hβ0 hβ1 hδ ha hb hab)
    (by have : 0 < 1 - α := by linarith
        positivity)

/-- AKMM, p. 448: a higher `τ_k` "will depress the steady-state wage `w`". -/
theorem lr_wage_strictAntiOn {α β δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) : StrictAntiOn (lrWage α β δ) (Set.Iio 1) := by
  intro a ha b hb hab
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hxb : 0 < lrRatio α β δ b := by
    have : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
    unfold lrRatio lrS
    positivity
  unfold lrWage
  exact mul_lt_mul_of_pos_left
    (Real.rpow_lt_rpow hxb.le (lr_ratio_strictAntiOn hα0 hα1 hβ0 hβ1 hδ ha hb hab) hα0)
    (by linarith)

/-- GHH utility `u(c, ℓ) = log(c − ℓ^{1+1/φ}/(1 + 1/φ))` (AKMM, p. 448). -/
noncomputable def ghhU (φ c l : ℝ) : ℝ := Real.log (c - l ^ (1 + 1 / φ) / (1 + 1 / φ))

/-- The GHH disutility of hours `v(ℓ) = ℓ^{1+1/φ}/(1 + 1/φ)`. -/
noncomputable def ghhV (φ l : ℝ) : ℝ := l ^ (1 + 1 / φ) / (1 + 1 / φ)

/-- AKMM, p. 448: for `φ > 0`, `ℓ > 0` and `c > v(ℓ)`, GHH utility is differentiable with
`u₁ = 1/(c − v(ℓ))` and `u₂ = −ℓ^{1/φ}/(c − v(ℓ))`. -/
theorem ghh_partials {φ c l : ℝ} (hφ : 0 < φ) (hl : 0 < l) (hc : ghhV φ l < c) :
    DTPartials (ghhU φ) c l (1 / (c - ghhV φ l)) (-(l ^ (1 / φ)) / (c - ghhV φ l)) := by
  have hpos : 0 < c - ghhV φ l := by linarith
  have ha : 0 < 1 + 1 / φ := by positivity
  have hψ : HasDerivAt (fun l => l ^ (1 + 1 / φ) / (1 + 1 / φ))
      ((1 + 1 / φ) * l ^ (1 + 1 / φ - 1) / (1 + 1 / φ)) l :=
    (Real.hasDerivAt_rpow_const (p := 1 + 1 / φ) (Or.inl hl.ne')).div_const _
  have h2 := hψ.comp_hasFDerivAt (c, l) (hasFDerivAt_snd (𝕜 := ℝ) (p := (c, l)))
  have h3 := (hasFDerivAt_fst (𝕜 := ℝ) (p := (c, l))).sub h2
  have hlog : HasDerivAt Real.log (c - ghhV φ l)⁻¹ (c - ghhV φ l) :=
    Real.hasDerivAt_log hpos.ne'
  have h4 := hlog.comp_hasFDerivAt (c, l) h3
  unfold DTPartials
  refine (h4.congr_fderiv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun q => rfl)
  ext
  · simp [ghhV]
  · simp
    field_simp

/-- **(15.12)** (AKMM, p. 448): with GHH utility, the labour condition (15.9) at `ℓ > 0`,
`c > v(ℓ)`, `(1 − τ_ℓ)/(1 + τ_c) > 0`, `w > 0` gives `ℓ = ((1 − τ_ℓ)/(1 + τ_c))^φw^φ`; consumption
does not enter. -/
theorem eq_15_12 {φ c l τl τc w : ℝ} (hφ : 0 < φ) (hl : 0 < l) (hc : ghhV φ l < c)
    (hθ : 0 < (1 - τl) / (1 + τc)) (hw : 0 < w)
    (h159 : -(-(l ^ (1 / φ)) / (c - ghhV φ l)) = (1 - τl) / (1 + τc) * w * (1 / (c - ghhV φ l))) :
    l = ((1 - τl) / (1 + τc)) ^ φ * w ^ φ := by
  have hpos : 0 < c - ghhV φ l := by linarith
  have h1 : l ^ (1 / φ) = (1 - τl) / (1 + τc) * w := by
    field_simp at h159
    rw [h159]
    ring
  rw [← Real.mul_rpow hθ.le hw.le, ← h1, ← Real.rpow_mul hl.le, one_div_mul_cancel hφ.ne',
    Real.rpow_one]

/-- GHH steady-state hours (15.12) as a function of the taxes and the wage. -/
noncomputable def ghhHours (φ τl τc w : ℝ) : ℝ := ((1 - τl) / (1 + τc)) ^ φ * w ^ φ

/-- AKMM, p. 448: "Higher labor income … taxes depress hours worked" (for `τ_c > −1`, `w > 0`,
`φ > 0`, on `τ_ℓ < 1`). -/
theorem lr_hours_strictAntiOn_labour {φ τc w : ℝ} (hφ : 0 < φ) (hτc : 0 < 1 + τc) (hw : 0 < w) :
    StrictAntiOn (fun τl => ghhHours φ τl τc w) (Set.Iio 1) := by
  intro a _ b hb hab
  have hb' : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
  simp only [ghhHours]
  refine mul_lt_mul_of_pos_right ?_ (Real.rpow_pos_of_pos hw φ)
  exact Real.rpow_lt_rpow (by positivity) (div_lt_div_of_pos_right (by linarith) hτc) hφ

/-- AKMM, p. 448: "Higher … consumption taxes depress hours worked" (for `τ_ℓ < 1`, `w > 0`,
on `τ_c > −1`). -/
theorem lr_hours_strictAntiOn_cons {φ τl w : ℝ} (hφ : 0 < φ) (hτl : τl < 1) (hw : 0 < w) :
    StrictAntiOn (fun τc => ghhHours φ τl τc w) (Set.Ioi (-1)) := by
  intro a ha b hb hab
  have ha' : 0 < 1 + a := by have := Set.mem_Ioi.mp ha; linarith
  have hb' : 0 < 1 + b := by have := Set.mem_Ioi.mp hb; linarith
  simp only [ghhHours]
  refine mul_lt_mul_of_pos_right ?_ (Real.rpow_pos_of_pos hw φ)
  have hl : 0 < 1 - τl := by linarith
  exact Real.rpow_lt_rpow (by positivity) (div_lt_div_of_pos_left hl ha' (by linarith)) hφ

/-- AKMM, p. 448: "Higher capital income taxes also depress hours, via their negative impact on
`w`": steady-state GHH hours at the wage (15.10) are strictly decreasing in `τ_k < 1`. -/
theorem lr_hours_strictAntiOn_capital {α β δ φ τl τc : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hθ : 0 < (1 - τl) / (1 + τc)) :
    StrictAntiOn (fun τk => ghhHours φ τl τc (lrWage α β δ τk)) (Set.Iio 1) := by
  intro a ha b hb hab
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hwb : 0 < lrWage α β δ b := by
    have : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
    have : 0 < 1 - α := by linarith
    unfold lrWage lrRatio lrS
    positivity
  simp only [ghhHours]
  refine mul_lt_mul_of_pos_left ?_ (Real.rpow_pos_of_pos hθ φ)
  exact Real.rpow_lt_rpow hwb.le (lr_wage_strictAntiOn hα0 hα1 hβ0 hβ1 hδ ha hb hab) hφ

end AKMM.FiscalPolicy
