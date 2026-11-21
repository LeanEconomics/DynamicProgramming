/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.ISTCOptimality

/-!
# Expanding varieties: the decentralised equilibrium

AKMM, §13.5.1 (pp. 386–392) and Appendix 13.A.5 (p. 853): Romer (1990) without physical capital.
The allocation is symmetric across the `N` varieties (as in the text after (13.34)), so
`∫_0^N x(ν)^{1−φ}dν = Nx^{1−φ}`; the per-variety problems are solved pointwise. Write
`X = A(1−φ)/ψ`.

* Final-goods first-order conditions (13.23)–(13.24) (`eq_13_23`, `eq_13_24`).
* The monopolist's problem (13.25): `x = X^{1/φ}L_y` (13.33) is the global maximum, the price is
  `ψ/(1−φ)`, profits are (13.34) (`eq_13_33`, `eq_13_34`); footnote 32, the Lerner markup
  (`romer_footnote_32`).
* Output, wage and consumption (13.35)–(13.37) (`eq_13_35`, `eq_13_36`, `eq_13_37`); love of
  variety, footnote 29 (`romer_footnote_29`).
* Free entry (13.39)–(13.40), the HJB equation (13.41), the law of motion (13.42), and the
  single ODE (13.43) (`eq_13_40`, `eq_13_41`, `eq_13_42`, `eq_13_43`).
* The balanced growth path (13.44)–(13.46), `L_r* > 0` iff (13.32), the TVC iff (13.31), and
  (13.52) (`eq_13_44`, `romer_Lr_star`, `eq_13_45`, `eq_13_46`, `romer_tvc_iff`, `eq_13_52`).
* Comparative statics: growth falls with `ρ` and `σ` and rises with `L`, and so does the
  research share (`romer_comparative_statics`, `romer_research_share_mono`).
* p. 392: a profit tax or a lower markup lowers growth (`romer_markup_interest`,
  `romer_theta_growth_mono`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- The constant `X = A(1−φ)/ψ` of the Romer model. -/
noncomputable def romerX (A φ ψ : ℝ) : ℝ := A * (1 - φ) / ψ

/-- `A X^{(1−φ)/φ} = (ψ/(1−φ)) X^{1/φ}`. -/
theorem romer_X_identity {A φ ψ : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ) :
    A * romerX A φ ψ ^ ((1 - φ) / φ) = ψ / (1 - φ) * romerX A φ ψ ^ (1 / φ) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  rw [show 1 / φ = (1 - φ) / φ + 1 by field_simp; ring, Real.rpow_add hX, Real.rpow_one]
  unfold romerX
  field_simp

/-- AKMM, (13.23), p. 387: the marginal product of production labour is `φY/L_y`. -/
theorem eq_13_23 {A φ S Ly : ℝ} (hLy : 0 < Ly) :
    HasDerivAt (fun l => A / (1 - φ) * l ^ φ * S) (φ * (A / (1 - φ) * Ly ^ φ * S) / Ly) Ly := by
  have h := ((Real.hasDerivAt_rpow_const (p := φ) (Or.inl hLy.ne')).const_mul
    (A / (1 - φ))).mul_const S
  convert h using 1
  rw [Real.rpow_sub_one hLy.ne']
  ring

/-- AKMM, (13.24), p. 387: the marginal product of machine `ν` is `AL_y^φx(ν)^{−φ}`. -/
theorem eq_13_24 {A φ Ly x : ℝ} (hφ1 : φ < 1) (hx : 0 < x) :
    HasDerivAt (fun y => A / (1 - φ) * Ly ^ φ * y ^ (1 - φ)) (A * Ly ^ φ * x ^ (-φ)) x := by
  have h1φ : (1 - φ) ≠ 0 := by linarith
  have h := (Real.hasDerivAt_rpow_const (p := 1 - φ) (Or.inl hx.ne')).const_mul
    (A / (1 - φ) * Ly ^ φ)
  convert h using 1
  rw [show 1 - φ - 1 = -φ by ring]
  field_simp

/-- AKMM, (13.33), p. 389: the monopoly quantity `x = X^{1/φ}L_y`. -/
noncomputable def romerXMon (A φ ψ Ly : ℝ) : ℝ := romerX A φ ψ ^ (1 / φ) * Ly

/-- AKMM, (13.25) and (13.33)–(13.34), p. 389: **the monopolist's problem**. Facing the inverse
demand (13.24) `p(x) = AL_y^φx^{−φ}`, profit `AL_y^φx^{1−φ} − ψx` is maximised over `x ≥ 0` at
`x = X^{1/φ}L_y`, where the price is `ψ/(1−φ)`. -/
theorem eq_13_33 {A φ ψ Ly x : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hLy : 0 < Ly) (hx : 0 ≤ x) :
    A * Ly ^ φ * x ^ (1 - φ) - ψ * x ≤
        A * Ly ^ φ * romerXMon A φ ψ Ly ^ (1 - φ) - ψ * romerXMon A φ ψ Ly ∧
      A * Ly ^ φ * romerXMon A φ ψ Ly ^ (-φ) = ψ / (1 - φ) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  set xs := romerXMon A φ ψ Ly
  have hxs : 0 < xs := by simp only [xs, romerXMon]; positivity
  have hprice : A * Ly ^ φ * xs ^ (-φ) = ψ / (1 - φ) := by
    simp only [xs, romerXMon]
    rw [Real.mul_rpow (by positivity) hLy.le, ← Real.rpow_mul hX.le,
      show 1 / φ * -φ = -1 by field_simp, Real.rpow_neg_one, Real.rpow_neg hLy.le]
    unfold romerX
    field_simp
  refine ⟨?_, hprice⟩
  have htan := istc_rpow_tangent (α := 1 - φ) (by linarith) (by linarith) hxs hx
  have hc : 0 ≤ A * Ly ^ φ := by positivity
  have := mul_le_mul_of_nonneg_left htan hc
  have hslope : A * Ly ^ φ * ((1 - φ) * xs ^ (1 - φ - 1)) = ψ := by
    rw [show 1 - φ - 1 = -φ by ring, show A * Ly ^ φ * ((1 - φ) * xs ^ (-φ)) =
      (1 - φ) * (A * Ly ^ φ * xs ^ (-φ)) by ring, hprice]
    field_simp
  nlinarith

/-- AKMM, (13.34), p. 389: monopoly profit `ψx/(1−φ) − ψx = φAX^{1/φ−1}L_y`. -/
theorem eq_13_34 {A φ ψ Ly : ℝ} (hA : 0 < A) (hφ1 : φ < 1) (hψ : 0 < ψ) :
    ψ / (1 - φ) * romerXMon A φ ψ Ly - ψ * romerXMon A φ ψ Ly =
      φ * A * romerX A φ ψ ^ (1 / φ - 1) * Ly := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  unfold romerXMon
  rw [Real.rpow_sub_one hX.ne']
  unfold romerX
  field_simp
  ring

/-- AKMM, footnote 32, p. 389: the Lerner rule. With demand elasticity `−1/φ`, the markup
`(1/φ)/(1/φ − 1)` is `1/(1−φ)`, i.e. the price `ψ/(1−φ)`. -/
theorem romer_footnote_32 {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    (1 / φ) / (1 / φ - 1) = 1 / (1 - φ) := by
  have h1φ : (1 - φ) ≠ 0 := by linarith
  have : (1 / φ - 1) = (1 - φ) / φ := by field_simp
  rw [this]
  field_simp

/-- AKMM, (13.35), p. 389: with every machine at (13.33), output is
`Y = (A/(1−φ))X^{(1−φ)/φ}L_yN`. -/
theorem eq_13_35 {A φ ψ Ly N : ℝ} (hLy : 0 < Ly) (hX : 0 < romerX A φ ψ) :
    A / (1 - φ) * Ly ^ φ * (N * romerXMon A φ ψ Ly ^ (1 - φ)) =
      A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * Ly * N := by
  unfold romerXMon
  rw [Real.mul_rpow (by positivity) hLy.le, ← Real.rpow_mul hX.le,
    show 1 / φ * (1 - φ) = (1 - φ) / φ by ring]
  have : Ly ^ φ * Ly ^ (1 - φ) = Ly := by
    rw [← Real.rpow_add hLy, show φ + (1 - φ) = 1 by ring, Real.rpow_one]
  linear_combination (A / (1 - φ) * N * romerX A φ ψ ^ ((1 - φ) / φ)) * this

/-- AKMM, (13.36), p. 389: the wage `w = φY/L_y = φ(A/(1−φ))X^{(1−φ)/φ}N`. -/
theorem eq_13_36 {A φ ψ Ly N : ℝ} (hLy : 0 < Ly) :
    φ * (A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * Ly * N) / Ly =
      φ * (A / (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) * N := by
  field_simp

/-- AKMM, (13.37), p. 390: goods-market clearing `c = Y − ψNx` gives
`c = (1/(1−φ)² − 1)ψX^{1/φ}L_yN`. -/
theorem eq_13_37 {A φ ψ Ly N : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ) :
    A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * Ly * N - ψ * N * romerXMon A φ ψ Ly =
      (1 / (1 - φ) ^ 2 - 1) * ψ * romerX A φ ψ ^ (1 / φ) * Ly * N := by
  have h1φ : 0 < 1 - φ := by linarith
  have hid := romer_X_identity hA hφ0 hφ1 hψ
  unfold romerXMon
  have e : A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) =
      ψ / (1 - φ) ^ 2 * romerX A φ ψ ^ (1 / φ) := by
    rw [div_mul_eq_mul_div, hid]
    field_simp
  rw [e]
  ring

/-- AKMM, footnote 29, p. 387: **love of variety**. With a budget `E` split equally over `N`
machines at price `p_x`, output is `(A/(1−φ))L_y^φN^φ(E/p_x)^{1−φ}`, increasing in `N`. -/
theorem romer_footnote_29 {A φ Ly E px : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hLy : 0 < Ly) (hE : 0 < E) (hpx : 0 < px) :
    (∀ N : ℝ, 0 < N → A / (1 - φ) * Ly ^ φ * (N * (E / (px * N)) ^ (1 - φ)) =
      A / (1 - φ) * Ly ^ φ * N ^ φ * (E / px) ^ (1 - φ)) ∧
    StrictMonoOn (fun N : ℝ => A / (1 - φ) * Ly ^ φ * N ^ φ * (E / px) ^ (1 - φ))
      (Set.Ioi 0) := by
  have h1φ : 0 < 1 - φ := by linarith
  refine ⟨fun N hN => ?_, fun N₁ h₁ N₂ h₂ h => ?_⟩
  · rw [show E / (px * N) = E / px * N⁻¹ by field_simp, Real.mul_rpow (by positivity)
      (by positivity), Real.inv_rpow hN.le]
    have : N * (N ^ (1 - φ))⁻¹ = N ^ φ := by
      rw [← Real.rpow_neg hN.le]
      nth_rewrite 1 [← Real.rpow_one N]
      rw [← Real.rpow_add hN]; congr 1; ring
    linear_combination (A / (1 - φ) * Ly ^ φ * (E / px) ^ (1 - φ)) * this
  · simp only
    have := Real.rpow_lt_rpow (le_of_lt h₁) h hφ0
    have hc : 0 < A / (1 - φ) * Ly ^ φ := by positivity
    have hd : 0 < (E / px) ^ (1 - φ) := by positivity
    nlinarith [mul_lt_mul_of_pos_left this hc]

/-- AKMM, (13.39)–(13.40), p. 390: free entry `V = w/(ηN)` with the wage (13.36) gives the
constant firm value `V = (φA/(η(1−φ)))X^{(1−φ)/φ}`. -/
theorem eq_13_40 {A φ ψ η N : ℝ} (hη : 0 < η) (hN : 0 < N) :
    φ * (A / (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) * N / (η * N) =
      φ * A / (η * (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) := by
  field_simp

/-- AKMM, (13.41), p. 390: with `V` constant, the HJB equation `Vr = π + V̇` gives
`r = π/V = η(1−φ)L_y`. -/
theorem eq_13_41 {A φ ψ η Ly r : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hη : 0 < η)
    (hjb : φ * A / (η * (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) * r =
      φ * A * romerX A φ ψ ^ (1 / φ - 1) * Ly + 0) :
    r = η * (1 - φ) * Ly := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  rw [show 1 / φ - 1 = (1 - φ) / φ by field_simp, add_zero] at hjb
  have hp : 0 < romerX A φ ψ ^ ((1 - φ) / φ) := by positivity
  field_simp at hjb
  nlinarith [hjb, mul_pos (mul_pos hφ0 hA) hp]

/-- AKMM, (13.42), p. 390: with labour-market clearing `L_r = L − L_y`, (13.26) gives
`Ṅ/N = η(L − L_y)`. -/
theorem eq_13_42 {η L Ly N Ndot : ℝ} (hN : 0 < N) (h1326 : Ndot = η * N * (L - Ly)) :
    Ndot / N = η * (L - Ly) := by
  rw [h1326]; field_simp

/-- AKMM, (13.43), p. 390: **the single ODE**. If `c = κL_yN` (13.37) with `κ ≠ 0`, the Euler
equation `ċ/c = (r − ρ)/σ` (13.38) holds with `r = η(1−φ)L_y` (13.41), and `Ṅ = η(L − L_y)N`
(13.42), then `L̇_y/L_y = (η(1−φ+σ)L_y − ρ)/σ − ηL`. -/
theorem eq_13_43 {κ φ η σ ρ L t Lydot : ℝ} {Ly N c : ℝ → ℝ} (hκ : κ ≠ 0) (hσ : 0 < σ)
    (hLy : 0 < Ly t) (hN : 0 < N t) (hc : c = fun s => κ * Ly s * N s)
    (hLyd : HasDerivAt Ly Lydot t) (hNd : HasDerivAt N (η * (L - Ly t) * N t) t)
    (heuler : HasDerivAt c (c t * (η * (1 - φ) * Ly t - ρ) / σ) t) :
    Lydot / Ly t = (η * (1 - φ + σ) * Ly t - ρ) / σ - η * L := by
  have hd : HasDerivAt c (κ * Lydot * N t + κ * Ly t * (η * (L - Ly t) * N t)) t := by
    rw [hc]; exact (hLyd.const_mul κ).fun_mul hNd
  have hu := heuler.unique hd
  rw [hc] at hu
  simp only at hu
  have hκN : κ * N t ≠ 0 := mul_ne_zero hκ hN.ne'
  have hL : Lydot = Ly t * (η * (1 - φ) * Ly t - ρ) / σ - Ly t * η * (L - Ly t) := by
    apply mul_left_cancel₀ hκN
    linear_combination -hu
  rw [hL]
  field_simp
  ring

/-- AKMM, (13.44), p. 390: the balanced-growth production labour
`L_y* = (σL + ρ/η)/(1 − φ + σ)`. -/
noncomputable def romerLyStar (φ η σ ρ L : ℝ) : ℝ := (σ * L + ρ / η) / (1 - φ + σ)

/-- AKMM, (13.44), p. 390: `L_y*` is the unique zero of the right side of (13.43). -/
theorem eq_13_44 {φ η σ ρ L Ly : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ) :
    (η * (1 - φ + σ) * Ly - ρ) / σ - η * L = 0 ↔ Ly = romerLyStar φ η σ ρ L := by
  have h : 0 < 1 - φ + σ := by linarith
  unfold romerLyStar
  rw [div_sub' hσ.ne', div_eq_zero_iff, or_iff_left hσ.ne', eq_div_iff h.ne']
  constructor <;> intro h0
  · field_simp; linarith
  · field_simp at h0; linarith

/-- AKMM, p. 391: research labour on the balanced growth path
`L_r* = L − L_y* = ((1−φ)L − ρ/η)/(1 − φ + σ)`, positive iff (13.32) `ρ < (1−φ)ηL`. -/
theorem romer_Lr_star {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ) :
    L - romerLyStar φ η σ ρ L = ((1 - φ) * L - ρ / η) / (1 - φ + σ) ∧
      (0 < L - romerLyStar φ η σ ρ L ↔ ρ < (1 - φ) * η * L) := by
  have h : 0 < 1 - φ + σ := by linarith
  have e : L - romerLyStar φ η σ ρ L = ((1 - φ) * L - ρ / η) / (1 - φ + σ) := by
    unfold romerLyStar; field_simp; ring
  refine ⟨e, ?_⟩
  rw [e, div_pos_iff_of_pos_right h, sub_pos, div_lt_iff₀ hη]
  constructor <;> intro h0 <;> linarith

/-- AKMM, (13.45), p. 391: the interest rate on the balanced growth path,
`r* = η(1−φ)L_y* = (1−φ)(ησL + ρ)/(1 − φ + σ)`. -/
theorem eq_13_45 {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ) :
    η * (1 - φ) * romerLyStar φ η σ ρ L = (1 - φ) * (η * σ * L + ρ) / (1 - φ + σ) := by
  have h : 0 < 1 - φ + σ := by linarith
  unfold romerLyStar; field_simp

/-- AKMM, (13.46), p. 391: the growth rate of varieties `ηL_r* = ((1−φ)ηL − ρ)/(1 − φ + σ)`;
it also satisfies the Euler equation `g = (r* − ρ)/σ`. -/
theorem eq_13_46 {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ) :
    η * (L - romerLyStar φ η σ ρ L) = ((1 - φ) * η * L - ρ) / (1 - φ + σ) ∧
      (η * (1 - φ) * romerLyStar φ η σ ρ L - ρ) / σ =
        ((1 - φ) * η * L - ρ) / (1 - φ + σ) := by
  have h : 0 < 1 - φ + σ := by linarith
  refine ⟨?_, ?_⟩ <;> unfold romerLyStar <;> field_simp <;> ring

/-- AKMM, (13.31) and p. 391: with `g` the balanced growth rate and `r* = σg + ρ`, the TVC
`e^{−r*T}a(T) → 0` for `a = a_0e^{gT}`, `a_0 > 0`, holds iff (13.31) `ρ > (1−σ)g`. -/
theorem romer_tvc_iff {σ ρ g a0 : ℝ} (ha0 : 0 < a0) :
    Tendsto (fun T => Real.exp (-(σ * g + ρ) * T) * (a0 * Real.exp (g * T))) atTop (𝓝 0) ↔
      (1 - σ) * g < ρ := by
  have e : ∀ T, Real.exp (-(σ * g + ρ) * T) * (a0 * Real.exp (g * T)) =
      a0 * Real.exp (((1 - σ) * g - ρ) * T) := fun T => by
    rw [mul_left_comm, ← Real.exp_add]; ring_nf
  simp only [e]
  rw [istc_exp_tendsto_zero_iff ha0, sub_neg]

/-- AKMM, (13.52), p. 392: on the balanced growth path `π*/r* = V`, the constant
`(φ/η)(A/(1−φ))X^{(1−φ)/φ}`. -/
theorem eq_13_52 {A φ ψ η Ly : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hη : 0 < η) (hLy : 0 < Ly) :
    φ * A * romerX A φ ψ ^ (1 / φ - 1) * Ly / (η * (1 - φ) * Ly) =
      φ / η * (A / (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) := by
  have h1φ : 0 < 1 - φ := by linarith
  rw [show 1 / φ - 1 = (1 - φ) / φ by field_simp]
  field_simp

/-- AKMM, (13.46), p. 391: **comparative statics**. Under (13.32) the balanced growth rate
`((1−φ)ηL − ρ)/(1 − φ + σ)` is strictly decreasing in `ρ` and in `σ > 0`, and strictly
increasing in `L` (the strong scale effect). -/
theorem romer_comparative_statics {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ)
    (h1332 : ρ < (1 - φ) * η * L) :
    StrictAnti (fun ρ' => ((1 - φ) * η * L - ρ') / (1 - φ + σ)) ∧
      StrictAntiOn (fun σ' => ((1 - φ) * η * L - ρ) / (1 - φ + σ')) (Set.Ioi 0) ∧
      StrictMono (fun L' => ((1 - φ) * η * L' - ρ) / (1 - φ + σ)) := by
  have h : 0 < 1 - φ + σ := by linarith
  have h1φ : 0 < 1 - φ := by linarith
  refine ⟨fun a b hab => ?_, fun a ha b hb hab => ?_, fun a b hab => ?_⟩
  · exact div_lt_div_of_pos_right (by linarith) h
  · simp only
    apply div_lt_div_of_pos_left (by linarith) (by simp at ha; linarith) (by linarith)
  · simp only
    apply div_lt_div_of_pos_right _ h
    have := mul_lt_mul_of_pos_left hab (mul_pos h1φ hη)
    linarith

/-- AKMM, p. 391: **the research share `L_r*/L` rises with `L`**:
`L_r*/L = ((1−φ) − ρ/(ηL))/(1 − φ + σ)` is strictly increasing in `L > 0` when `ρ > 0`. -/
theorem romer_research_share_mono {φ η σ ρ : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ)
    (hρ : 0 < ρ) :
    StrictMonoOn (fun L => (L - romerLyStar φ η σ ρ L) / L) (Set.Ioi 0) := by
  have h : 0 < 1 - φ + σ := by linarith
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  simp only
  rw [(romer_Lr_star hφ1 hη hσ).1, (romer_Lr_star hφ1 hη hσ).1, div_div, div_div,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have hρη : 0 < ρ / η := div_pos hρ hη
  have key : ρ / η * a < ρ / η * b := mul_lt_mul_of_pos_left hab hρη
  nlinarith [mul_lt_mul_of_pos_left key h]

/-- AKMM, p. 392: **profit taxes and markups**. If a fraction `θ > 0` of the monopoly profit
`(μ−1)ψx` is kept (a profit tax `1 − θ`), with markup `μ`, then with `V` from free entry
the HJB equation gives `r = η(1−φ)θ(μ−1)/(φμ)·L_y`; at the Romer markup `μ = 1/(1−φ)` and
`θ = 1` this is (13.41). -/
theorem romer_markup_interest {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    (1 / (1 - φ) - 1) / (φ * (1 / (1 - φ))) = 1 := by
  have h1φ : (1 - φ) ≠ 0 := by linarith
  field_simp
  ring

/-- AKMM, p. 392: with `r = η(1−φ)θL_y` (θ the profit share kept, e.g. after a profit tax or
with a lower markup, `θ = (μ−1)/(φμ)`), the balanced growth rate solving `g = ηL_r`,
`r = ρ + σg`, `L = L_y + L_r` is `g(θ) = ((1−φ)θηL − ρ)/((1−φ)θ + σ)`; it is strictly
increasing in `θ > 0` whenever `ρ > 0`. So taxing profits, or lowering the markup below
`1/(1−φ)` (which lowers `θ`), lowers growth. -/
theorem romer_theta_growth_mono {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ)
    (hρ : 0 < ρ) (hL : 0 < L) :
    (∀ θ, 0 < θ → ∀ Ly, η * (1 - φ) * θ * Ly = ρ + σ * (η * (L - Ly)) →
      η * (L - Ly) = ((1 - φ) * θ * η * L - ρ) / ((1 - φ) * θ + σ)) ∧
    StrictMonoOn (fun θ => ((1 - φ) * θ * η * L - ρ) / ((1 - φ) * θ + σ)) (Set.Ioi 0) := by
  have h1φ : 0 < 1 - φ := by linarith
  refine ⟨fun θ hθ Ly h => ?_, fun a ha b hb hab => ?_⟩
  · have hden : 0 < (1 - φ) * θ + σ := by positivity
    rw [eq_div_iff hden.ne']
    nlinarith [h]
  · simp only [Set.mem_Ioi] at ha hb
    simp only
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : 0 < (b - a) * ((1 - φ) * (σ * η * L + ρ)) := by positivity
    nlinarith

end AKMM.Growth
