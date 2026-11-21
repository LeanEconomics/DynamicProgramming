/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.Romer

/-!
# Expanding varieties: no transitional dynamics, and the corner

AKMM, §13.5.1, footnotes 33–34 (p. 391). The single ODE (13.43) is
`L̇_y = L_y(aL_y − b)` with `a = η(1−φ+σ)/σ` and `b = ρ/σ + ηL`, and `L_y* = b/a`.

* `romer_footnote_33_solution`: `1/L_y` solves a linear ODE, so every positive solution on
  `[0, ∞)` is `1/L_y(t) = 1/L_y* + (1/L_y(0) − 1/L_y*)e^{bt}`.
* `romer_footnote_33_above`: if `L_y(0) > L_y*` there is no positive solution on `[0, ∞)`
  (it explodes in finite time, and so certainly exceeds `L`).
* `romer_footnote_33_below`, `romer_footnote_33_tvc_fails`: if `L_y(0) < L_y*` then
  `L_y → 0`, so `r → 0`, and the TVC `e^{−∫r}a(T) → 0` fails.
* `romer_footnote_33`: hence every equilibrium path has `L_y ≡ L_y*` from date 0.
* `romer_footnote_34`: at the corner `L_r = 0`, `r* = ρ` and `V = π/ρ`, which exceeds the entry
  cost `w/(ηN)` iff (13.32). The printed `V = π/r* = φAX^{1/φ−1}L` omits the `/ρ`
  (`romer_footnote_34_printed_false`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, footnote 33 and (13.43), p. 391: **the explicit solution**. If `L_y > 0` satisfies
`L̇_y = L_y((η(1−φ+σ)L_y − ρ)/σ − ηL)` on `[0, ∞)`, then with `b = ρ/σ + ηL`,
`1/L_y(t) = 1/L_y* + (1/L_y(0) − 1/L_y*)e^{bt}`. -/
theorem romer_footnote_33_solution {φ η σ ρ L : ℝ} {Ly : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hσ : 0 < σ) (hLs : 0 < romerLyStar φ η σ ρ L) (hpos : ∀ t, 0 ≤ t → 0 < Ly t)
    (hode : ∀ t, 0 ≤ t → HasDerivAt Ly (Ly t * ((η * (1 - φ + σ) * Ly t - ρ) / σ - η * L)) t) :
    ∀ t, 0 ≤ t → (Ly t)⁻¹ = (romerLyStar φ η σ ρ L)⁻¹ +
      ((Ly 0)⁻¹ - (romerLyStar φ η σ ρ L)⁻¹) * Real.exp ((ρ / σ + η * L) * t) := by
  set b := ρ / σ + η * L
  set Ls := romerLyStar φ η σ ρ L
  have hden : 0 < 1 - φ + σ := by linarith
  have hrel : η * (1 - φ + σ) * Ls = σ * η * L + ρ := by
    simp only [Ls, romerLyStar]; field_simp
  have hrel0 : σ * η * L + ρ ≠ 0 := by rw [← hrel]; positivity
  have hLsinv : Ls⁻¹ = η * (1 - φ + σ) / (σ * η * L + ρ) := by
    rw [← hrel]; field_simp
  set f := fun s => ((Ly s)⁻¹ - Ls⁻¹) * Real.exp (-b * s)
  have hf : ∀ s, 0 ≤ s → HasDerivAt f 0 s := fun s hs => by
    have hw := (hode s hs).fun_inv (hpos s hs).ne'
    have h1 := (hw.sub_const Ls⁻¹).fun_mul ((hasDerivAt_id' s).const_mul (-b)).exp
    convert h1 using 1
    have hL := (hpos s hs).ne'
    set E := Real.exp (-b * s)
    have hb : b = (σ * η * L + ρ) / σ := by simp only [b]; field_simp; ring
    have key : -(Ly s * ((η * (1 - φ + σ) * Ly s - ρ) / σ - η * L)) / Ly s ^ 2 +
        ((Ly s)⁻¹ - Ls⁻¹) * (-b) = 0 := by
      rw [hb]
      have hLs0 := hLs.ne'
      field_simp
      linear_combination (-(Ly s)) * hrel
    linear_combination (-E) * key
  intro t ht
  have hconst := constant_of_has_deriv_right_zero (f := f) (a := 0) (b := t)
    (fun s hs => (hf s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hf s hs.1).hasDerivWithinAt) t (Set.right_mem_Icc.mpr ht)
  simp only [f, mul_zero, Real.exp_zero, mul_one] at hconst
  have hE : Real.exp (-b * t) * Real.exp (b * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have := congrArg (· * Real.exp (b * t)) hconst
  rw [mul_assoc, hE, mul_one] at this
  linarith

/-- AKMM, footnote 33, p. 391: **starting above `L_y*` is impossible**. If `ρ > 0`, `L > 0`
and `L_y(0) > L_y*`, no positive solution of (13.43) exists on `[0, ∞)`: `1/L_y` would become
negative. -/
theorem romer_footnote_33_above {φ η σ ρ L : ℝ} {Ly : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hσ : 0 < σ) (hρ : 0 < ρ) (hL : 0 < L) (hpos : ∀ t, 0 ≤ t → 0 < Ly t)
    (hode : ∀ t, 0 ≤ t → HasDerivAt Ly (Ly t * ((η * (1 - φ + σ) * Ly t - ρ) / σ - η * L)) t)
    (habove : romerLyStar φ η σ ρ L < Ly 0) : False := by
  have hden : 0 < 1 - φ + σ := by linarith
  have hLs : 0 < romerLyStar φ η σ ρ L := by unfold romerLyStar; positivity
  have hsol := romer_footnote_33_solution hφ1 hη hσ hLs hpos hode
  set b := ρ / σ + η * L
  have hb : 0 < b := by positivity
  set ws := (romerLyStar φ η σ ρ L)⁻¹
  set w0 := (Ly 0)⁻¹
  have hw0 : 0 < w0 := by have := hpos 0 le_rfl; positivity
  have hlt : w0 < ws := inv_strictAnti₀ hLs habove
  set T := (w0 / (ws - w0) + 1) / b
  have hT : 0 ≤ T := by
    have : 0 < ws - w0 := sub_pos.mpr hlt
    positivity
  have hexp : 1 + b * T ≤ Real.exp (b * T) := by
    have := Real.add_one_le_exp (b * T); linarith
  have hbT : b * T = w0 / (ws - w0) + 1 := by simp only [T]; field_simp
  have hneg : ws + (w0 - ws) * Real.exp (b * T) < 0 := by
    have h1 : (w0 - ws) * Real.exp (b * T) ≤ (w0 - ws) * (1 + b * T) :=
      mul_le_mul_of_nonpos_left hexp (by linarith)
    have h2 : ws + (w0 - ws) * (1 + b * T) = w0 - ws := by
      rw [hbT]
      have : ws - w0 ≠ 0 := (sub_pos.mpr hlt).ne'
      field_simp
      ring
    linarith
  have hTpos := hpos T hT
  have := hsol T hT
  have : 0 < (Ly T)⁻¹ := by positivity
  linarith

/-- AKMM, footnote 33, p. 391: **starting below `L_y*`, `L_y → 0`** (for `ρ > 0`, `L > 0`). -/
theorem romer_footnote_33_below {φ η σ ρ L : ℝ} {Ly : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hσ : 0 < σ) (hρ : 0 < ρ) (hL : 0 < L) (hpos : ∀ t, 0 ≤ t → 0 < Ly t)
    (hode : ∀ t, 0 ≤ t → HasDerivAt Ly (Ly t * ((η * (1 - φ + σ) * Ly t - ρ) / σ - η * L)) t)
    (hbelow : Ly 0 < romerLyStar φ η σ ρ L) : Tendsto Ly atTop (𝓝 0) := by
  have hden : 0 < 1 - φ + σ := by linarith
  have hLs : 0 < romerLyStar φ η σ ρ L := by unfold romerLyStar; positivity
  have hsol := romer_footnote_33_solution hφ1 hη hσ hLs hpos hode
  have hb : 0 < ρ / σ + η * L := by positivity
  have hgap : 0 < (Ly 0)⁻¹ - (romerLyStar φ η σ ρ L)⁻¹ :=
    sub_pos.mpr (inv_strictAnti₀ (hpos 0 le_rfl) hbelow)
  have hw : Tendsto (fun t => (romerLyStar φ η σ ρ L)⁻¹ +
      ((Ly 0)⁻¹ - (romerLyStar φ η σ ρ L)⁻¹) * Real.exp ((ρ / σ + η * L) * t)) atTop atTop := by
    apply tendsto_atTop_add_const_left
    apply Tendsto.const_mul_atTop hgap
    exact Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb)
  have hinv := tendsto_inv_atTop_zero.comp hw
  refine hinv.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [Function.comp]
  rw [← hsol t ht, inv_inv]

/-- AKMM, footnote 33, p. 391: **below `L_y*` the TVC fails**. Let `M` be the discount factor,
`Ṁ = −rM` with `r = η(1−φ)L_y` (13.41), `N` the varieties, `Ṅ = η(L − L_y)N` (13.42), both
positive, and `V > 0` the constant firm value, so that wealth is `a = VN`. If `L_y → 0`, then
`M(T)VN(T)` does not tend to `0`. -/
theorem romer_footnote_33_tvc_fails {φ η L V : ℝ} {Ly M N : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hL : 0 < L) (hV : 0 < V) (hM : ∀ t, 0 ≤ t → 0 < M t) (hN : ∀ t, 0 ≤ t → 0 < N t)
    (hMd : ∀ t, 0 ≤ t → HasDerivAt M (-(η * (1 - φ) * Ly t) * M t) t)
    (hNd : ∀ t, 0 ≤ t → HasDerivAt N (η * (L - Ly t) * N t) t)
    (hLy : Tendsto Ly atTop (𝓝 0)) :
    ¬ Tendsto (fun T => M T * V * N T) atTop (𝓝 0) := by
  intro htvc
  have h2φ : 0 < 2 - φ := by linarith
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp
    ((hLy.eventually (gt_mem_nhds (div_pos hL h2φ))).and (eventually_ge_atTop (0 : ℝ)))
  set T1 := max T0 0
  have hP : ∀ t, 0 ≤ t → HasDerivAt (fun s => M s * N s)
      (η * (L - (2 - φ) * Ly t) * (M t * N t)) t := fun t ht => by
    convert (hMd t ht).fun_mul (hNd t ht) using 1
    ring
  have hmono : MonotoneOn (fun s => M s * N s) (Set.Ici T1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici T1)
      (f' := fun t => η * (L - (2 - φ) * Ly t) * (M t * N t))
    · exact fun t ht => (hP t (le_trans (le_max_right _ _) ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hP t (le_trans (le_max_right _ _) ht.le)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht.le
      have hlt := (hT0 t (le_trans (le_max_left _ _) ht.le)).1
      have : (2 - φ) * Ly t < L := by rw [lt_div_iff₀ h2φ] at hlt; linarith
      have := hM t ht0; have := hN t ht0
      have : 0 ≤ L - (2 - φ) * Ly t := by linarith
      positivity
  have hP1 : 0 < M T1 * N T1 := mul_pos (hM T1 (le_max_right _ _)) (hN T1 (le_max_right _ _))
  have hlower : ∀ T, T1 ≤ T → V * (M T1 * N T1) ≤ M T * V * N T := fun T hT => by
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT) hT
    simp only at this
    nlinarith
  have hlim : V * (M T1 * N T1) ≤ 0 := ge_of_tendsto htvc (by
    filter_upwards [eventually_ge_atTop T1] with T hT using hlower T hT)
  have : 0 < V * (M T1 * N T1) := mul_pos hV hP1
  linarith

/-- AKMM, footnote 33 and p. 391: **the balanced growth path is the only equilibrium**. If
`L_y > 0` solves (13.43) on `[0, ∞)` and the TVC `M(T)VN(T) → 0` holds (with `M`, `N`, `V` as in
`romer_footnote_33_tvc_fails`), then `L_y(t) = L_y*` for all `t ≥ 0`: there are no
transitional dynamics. -/
theorem romer_footnote_33 {φ η σ ρ L V : ℝ} {Ly M N : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hσ : 0 < σ) (hρ : 0 < ρ) (hL : 0 < L) (hV : 0 < V) (hpos : ∀ t, 0 ≤ t → 0 < Ly t)
    (hode : ∀ t, 0 ≤ t → HasDerivAt Ly (Ly t * ((η * (1 - φ + σ) * Ly t - ρ) / σ - η * L)) t)
    (hM : ∀ t, 0 ≤ t → 0 < M t) (hN : ∀ t, 0 ≤ t → 0 < N t)
    (hMd : ∀ t, 0 ≤ t → HasDerivAt M (-(η * (1 - φ) * Ly t) * M t) t)
    (hNd : ∀ t, 0 ≤ t → HasDerivAt N (η * (L - Ly t) * N t) t)
    (htvc : Tendsto (fun T => M T * V * N T) atTop (𝓝 0)) :
    ∀ t, 0 ≤ t → Ly t = romerLyStar φ η σ ρ L := by
  have hden : 0 < 1 - φ + σ := by linarith
  have hLs : 0 < romerLyStar φ η σ ρ L := by unfold romerLyStar; positivity
  rcases lt_trichotomy (Ly 0) (romerLyStar φ η σ ρ L) with hlt | heq | hgt
  · exact absurd htvc (romer_footnote_33_tvc_fails hφ1 hη hL hV hM hN hMd hNd
      (romer_footnote_33_below hφ1 hη hσ hρ hL hpos hode hlt))
  · intro t ht
    have := romer_footnote_33_solution hφ1 hη hσ hLs hpos hode t ht
    rw [heq, sub_self, zero_mul, add_zero] at this
    have h1 := hpos t ht
    field_simp at this
    linarith
  · exact absurd hgt (fun h => romer_footnote_33_above hφ1 hη hσ hρ hL hpos hode h)

/-- AKMM, footnote 34, p. 391: **the corner is not an equilibrium**. At `L_r = 0` (`L_y = L`)
there is no growth, so the Euler equation gives `r* = ρ`, and with `V̇ = 0` the HJB equation
gives `V = π/ρ`, `π = φAX^{1/φ−1}L`. Then `V > w/(ηN) = (φA/(η(1−φ)))X^{(1−φ)/φ}` iff (13.32)
`ρ < (1−φ)ηL`, so (13.32) rules the corner out. -/
theorem romer_footnote_34 {A φ ψ η ρ L : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hη : 0 < η) (hρ : 0 < ρ) :
    φ * A / (η * (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) <
        φ * A * romerX A φ ψ ^ (1 / φ - 1) * L / ρ ↔ ρ < (1 - φ) * η * L := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  rw [show 1 / φ - 1 = (1 - φ) / φ by field_simp]
  set P := φ * A * romerX A φ ψ ^ ((1 - φ) / φ)
  have hP : 0 < P := by positivity
  rw [show φ * A / (η * (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) = P / (η * (1 - φ)) by
    simp only [P]; ring, div_lt_div_iff₀ (by positivity) hρ]
  constructor <;> intro h <;> nlinarith

/-- AKMM, footnote 34, p. 391: the printed `V = π/r* = φAX^{1/φ−1}L` is false: with `r* = ρ`,
`π/r* = π` only if `ρ = 1`. -/
theorem romer_footnote_34_printed_false {A φ ψ ρ L : ℝ} (hA : 0 < A) (hφ0 : 0 < φ)
    (hφ1 : φ < 1) (hψ : 0 < ψ) (hL : 0 < L) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) :
    φ * A * romerX A φ ψ ^ (1 / φ - 1) * L / ρ ≠ φ * A * romerX A φ ψ ^ (1 / φ - 1) * L := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  have hP : 0 < φ * A * romerX A φ ψ ^ (1 / φ - 1) * L := by positivity
  intro h
  rw [div_eq_iff hρ.ne'] at h
  apply hρ1
  have h2 : φ * A * romerX A φ ψ ^ (1 / φ - 1) * L * (ρ - 1) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hP.ne'
  · linarith

end AKMM.Growth
