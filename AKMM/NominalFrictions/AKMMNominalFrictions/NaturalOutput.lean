/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMNominalFrictions.ResetPrice
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The flexible-price equilibrium, the output gap and the interest-rate rule

AKMM, §18.3, pp. 542–543. With flexible prices (`θ = 0`) a firm maximises
`(p − w/A) p^{−ε} Y`, which gives the markup `µ = ε/(ε − 1)` over marginal cost
(`nat_markup_foc`, `nat_markup_max`, footnote 7), so `w^n/A = 1/µ`. The flexible-price
system then gives natural output (18.13), `Y^n = µ^{−1/(σ+ψ)} A^{(1+ψ)/(σ+ψ)}`
(`nat_output_general`, `eq_18_13`, `eq_18_13_solves`). The output gap is (18.14)
(`nfGap`, `nat_gap_loglinear`, footnote 9). The steady-state intercept of the rule is
`ī = (1 + π*)/β − 1` (`nat_rule_intercept`), and footnote 8's quarterly rescaling of the
output-gap coefficient is `0.5/4 = 0.125` (`nat_quarterly_rule`).
-/

namespace AKMM.NominalFrictions

/-- AKMM, p. 542 and footnote 7: the static first-order condition. For `m = w/A > 0` and
`p > 0`, the derivative of `(p − m) p^{−ε}` vanishes iff `p = µ m`, `µ = ε/(ε − 1)`. -/
theorem nat_markup_foc {ε m p : ℝ} (hε : 1 < ε) (hp : 0 < p) :
    rpBracket ε m p = 0 ↔ p = ε / (ε - 1) * m := by
  have hε1 : ε - 1 ≠ 0 := by linarith
  have e : rpBracket ε m p = p ^ (-ε - 1) * ((1 - ε) * p + ε * m) := by
    unfold rpBracket
    have a1 : p ^ (-ε) = p ^ (-ε - 1) * p := by
      rw [← Real.rpow_add_one hp.ne']; ring_nf
    rw [a1]; ring
  rw [e, mul_eq_zero, or_iff_right (Real.rpow_pos_of_pos hp _).ne']
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp; ring

/-- **AKMM, p. 542 and footnote 7**: the markup price `µ m` maximises the static profit
`(p − m) p^{−ε}` over `p > 0` (Bernoulli's inequality). -/
theorem nat_markup_max {ε m p : ℝ} (hε : 1 < ε) (hm : 0 < m) (hp : 0 < p) :
    (p - m) * p ^ (-ε) ≤ (ε / (ε - 1) * m - m) * (ε / (ε - 1) * m) ^ (-ε) := by
  set q := ε / (ε - 1) * m with hq
  have hε1 : 0 < ε - 1 := by linarith
  have hq0 : 0 < q := by positivity
  set x := p / q with hx
  have hx0 : 0 < x := div_pos hp hq0
  have hB := one_add_mul_self_le_rpow_one_add (s := x - 1) (by linarith) hε.le
  rw [show 1 + (x - 1) = x by ring] at hB
  have hpx : p = x * q := by rw [hx]; field_simp
  have hmq : m = (ε - 1) / ε * q := by rw [hq]; field_simp
  have hxe : (x * q) ^ (-ε) = x ^ (-ε) * q ^ (-ε) := Real.mul_rpow hx0.le hq0.le
  have hxx : x ^ ε * x ^ (-ε) = 1 := by rw [← Real.rpow_add hx0]; simp
  have hxpos : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hx0 _
  have hqpos : 0 < q ^ (-ε) := Real.rpow_pos_of_pos hq0 _
  rw [hpx, hxe, hmq]
  have hε0 : 0 < ε := by linarith
  have key : (x - (ε - 1) / ε) * x ^ (-ε) ≤ 1 - (ε - 1) / ε := by
    have h1 : x - (ε - 1) / ε ≤ x ^ ε / ε := by
      have e : (x - (ε - 1) / ε) * ε = ε * x - (ε - 1) := by field_simp
      rw [le_div_iff₀ hε0, e]; linarith
    calc (x - (ε - 1) / ε) * x ^ (-ε) ≤ x ^ ε / ε * x ^ (-ε) :=
          mul_le_mul_of_nonneg_right h1 hxpos.le
      _ = 1 - (ε - 1) / ε := by field_simp; linear_combination hxx
  have := mul_le_mul_of_nonneg_right key (mul_pos hq0 hqpos).le
  calc (x * q - (ε - 1) / ε * q) * (x ^ (-ε) * q ^ (-ε))
      = (x - (ε - 1) / ε) * x ^ (-ε) * (q * q ^ (-ε)) := by ring
    _ ≤ (1 - (ε - 1) / ε) * (q * q ^ (-ε)) := this
    _ = (q - (ε - 1) / ε * q) * q ^ (-ε) := by ring

/-- AKMM, p. 542: the markup `µ = ε/(ε − 1)` exceeds one when `ε > 1`. -/
theorem nat_markup_gt_one {ε : ℝ} (hε : 1 < ε) : 1 < ε / (ε - 1) := by
  rw [lt_div_iff₀ (by linarith)]; linarith

/-- AKMM, p. 542: with the flexible-price reset price `p^R = µ w/A` and `p^R = 1` (all firms
choose the same price), `w^n/A = 1/µ`. -/
theorem nat_wage {ε w A : ℝ} (h : 1 = ε / (ε - 1) * (w / A)) :
    w / A = 1 / (ε / (ε - 1)) := by
  exact eq_one_div_of_mul_eq_one_right h.symm

/-- AKMM, pp. 542 and 545–546: equilibrium output given the wage. From `C = Y`, `Y = A L/D`
and `C^{−σ} w = L^ψ`, `Y = D^{−ψ/(σ+ψ)} (w/A)^{1/(σ+ψ)} A^{(1+ψ)/(σ+ψ)}`. -/
theorem nat_output_general {σ ψ w A D Y L : ℝ} (hs : 0 < σ + ψ) (hw : 0 < w) (hA : 0 < A)
    (hD : 0 < D) (hY : 0 < Y) (hL : 0 < L) (hprod : Y = A * L / D)
    (hlab : Y ^ (-σ) * w = L ^ ψ) :
    Y = D ^ (-ψ / (σ + ψ)) * (w / A) ^ (1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) := by
  have hLe : L = D * Y / A := by rw [hprod]; field_simp
  have hlog := congrArg Real.log hlab
  rw [Real.log_mul (Real.rpow_pos_of_pos hY _).ne' hw.ne', Real.log_rpow hY,
    Real.log_rpow hL, hLe, Real.log_div (by positivity) hA.ne',
    Real.log_mul hD.ne' hY.ne'] at hlog
  have hlY : Real.log Y = (-ψ * Real.log D + (Real.log w - Real.log A) +
      (1 + ψ) * Real.log A) / (σ + ψ) := by
    rw [eq_div_iff hs.ne']; linarith
  have hR : 0 < D ^ (-ψ / (σ + ψ)) * (w / A) ^ (1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) := by
    positivity
  refine Real.log_injOn_pos hY hR ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hD, Real.log_rpow (div_pos hw hA), Real.log_rpow hA,
    Real.log_div hw.ne' hA.ne', hlY]
  field_simp

/-- **AKMM, (18.13), p. 542**: the flexible-price equilibrium. If `w^n = A/µ`, `Y^n = C^n`,
`Y^n = A L^n` and `(C^n)^{−σ} w^n = (L^n)^ψ`, then `Y^n = µ^{−1/(σ+ψ)} A^{(1+ψ)/(σ+ψ)}`. -/
theorem eq_18_13 {σ ψ mu A Y C L w : ℝ} (hs : 0 < σ + ψ) (hmu : 0 < mu) (hA : 0 < A)
    (hY : 0 < Y) (hL : 0 < L) (hw : w = A / mu) (hC : Y = C) (hprod : Y = A * L)
    (hlab : C ^ (-σ) * w = L ^ ψ) :
    Y = mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) := by
  have h := nat_output_general (D := 1) (w := w) (Y := Y) (L := L) hs
    (by rw [hw]; positivity) hA one_pos hY hL (by rw [hprod, div_one]) (by rw [hC]; exact hlab)
  rw [Real.one_rpow, one_mul, hw, show A / mu / A = mu⁻¹ by field_simp,
    Real.inv_rpow hmu.le, ← Real.rpow_neg hmu.le] at h
  rw [neg_div]; exact h

/-- AKMM, (18.13), p. 542: conversely, the natural allocation solves the flexible-price
system: with `Y = µ^{−1/(σ+ψ)} A^{(1+ψ)/(σ+ψ)}`, `L = Y/A`, `w = A/µ`, `Y^{−σ} w = L^ψ`. -/
theorem eq_18_13_solves {σ ψ mu A : ℝ} (hs : 0 < σ + ψ) (hmu : 0 < mu) (hA : 0 < A) :
    (mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ))) ^ (-σ) * (A / mu) =
      (mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) / A) ^ ψ := by
  have hY : 0 < mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) := by positivity
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hY, Real.log_rpow
    (div_pos hY hA), Real.log_div hY.ne' hA.ne', Real.log_div hA.ne' hmu.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hmu, Real.log_rpow hA]
  field_simp
  ring

/-- AKMM, (18.14), p. 542: the output gap `x = log Y − log Y^n`. -/
noncomputable def nfGap (Y Yn : ℝ) : ℝ := Real.log Y - Real.log Yn

/-- AKMM, (18.13) and (18.14), footnote 9, p. 543: with `Y^n` from (18.13), hats the log
deviations from the steady state `A = 1` (`Ȳ = µ^{−1/(σ+ψ)}`), the output gap is exactly
`x = Ŷ − (1+ψ)/(σ+ψ) Â`. -/
theorem nat_gap_loglinear {σ ψ mu A Y : ℝ} (hmu : 0 < mu) (hA : 0 < A) :
    nfGap Y (mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ))) =
      (Real.log Y - Real.log (mu ^ (-1 / (σ + ψ)))) - (1 + ψ) / (σ + ψ) * Real.log A := by
  unfold nfGap
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hA]
  ring

/-- AKMM, p. 543: in a steady state with constant consumption and inflation `π*`, the Euler
equation (18.5) holds iff `i = ī ≡ (1 + π*)/β − 1`. -/
theorem nat_rule_intercept {β σ C π i : ℝ} (hβ : 0 < β) (hC : 0 < C) (hπ : 0 < 1 + π) :
    C ^ (-σ) = β * ((1 + i) / (1 + π) * C ^ (-σ)) ↔ i = (1 + π) / β - 1 := by
  have hc : 0 < C ^ (-σ) := Real.rpow_pos_of_pos hC _
  constructor
  · intro h
    have h1 : β * ((1 + i) / (1 + π)) = 1 := by
      have := mul_right_cancel₀ hc.ne' (by linarith [h] : 1 * C ^ (-σ) =
        β * ((1 + i) / (1 + π)) * C ^ (-σ))
      linarith
    field_simp at h1 ⊢
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- AKMM, footnote 8, p. 543: with annualised rates `i^a = 4 i^q` and `π^a = 4 π^q` and the
output gap in percent, the rule `i^a = φ_π π^a + φ_x x` reads `i^q = φ_π π^q + (φ_x/4) x`;
Taylor's `φ_x = 0.5` becomes `0.125`. -/
theorem nat_quarterly_rule {φπ φx iq πq x : ℝ} :
    (4 * iq = φπ * (4 * πq) + φx * x ↔ iq = φπ * πq + φx / 4 * x) ∧ (0.5 : ℝ) / 4 = 0.125 := by
  refine ⟨⟨fun h => by linarith, fun h => by rw [h]; ring⟩, by norm_num⟩

end AKMM.NominalFrictions
