/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.MPDispersion

/-!
# Monetary policy design: the quadratic approximation to utility (Miao §19.2.2)

Miao, §19.2.2, pp. 631–635. Hats are log deviations from the zero-inflation steady state
`(C̄, N̄)`: `C = C̄e^ĉ`, `N = N̄e^n̂`.

* `mp_taylor_exp` (p. 632): `(C − C̄)/C̄ = e^ĉ − 1 = ĉ + ĉ²/2 + R`, `|R| ≤ |ĉ|³` for
  `|ĉ| ≤ 1`.
* `mp_uCC`, `mp_uNN`: for (19.1), `u_CC C/u_C = −γ` and `u_NN N/u_N = ν`;
  `mp_eq_19_30_truncation`: the book's second display (the Taylor expansion of `u` in levels,
  with `(C − C̄)/C̄` replaced by `ĉ + ĉ²/2`) equals the right side of (19.30) times `u_C C` plus
  the explicit third- and fourth-order terms the book drops.
* `mp_util_exact`: the exact identity
  `(u_t − u)/(u_C C) = (e^{(1−γ)ĉ} − 1)/(1 − γ) + (u_N N/(u_C C))(e^{(1+ν)n̂} − 1)/(1 + ν)`.
* `eq_19_30`: **(19.30) as a precise Taylor statement**: the remainder
  `(u_t − u)/(u_C C) − [ĉ + (1 − γ)ĉ²/2 + (u_N N/(u_C C))(n̂ + (1 + ν)n̂²/2)]` is bounded by
  `(1 − γ)²|ĉ|³ + |u_N N/(u_C C)|(1 + ν)²|n̂|³` when `|(1 − γ)ĉ|, |(1 + ν)n̂| ≤ 1`, and it is
  `o(ĉ² + n̂²)` (`eq_19_30_littleO`).
* Step 2 (pp. 633–634): `mp_step2_subst` (substituting `ĉ = ŷ`, Step 1's `n̂`),
  `mp_step2_phi` (`u_N N/(u_C C) = −(1 − α)(1 − Φ)` from `−u_N/u_C = MPN(1 − Φ)`,
  `MPN = (1 − α)Y/N`, `Y = C`), `mp_step2_small` (the small-distortion step: the expression
  equals the book's next line plus `Φ × [second-order terms]`, the term the book neglects) and
  `mp_step2_square` (completing the square with `ŷ^f = (1 + ν)a/D`, `x* = Φ(1 − α)/D`:
  `−½Λ(x − x*)² − (1 − α)Δ̂ + t.i.p.`, `Λ = γ + (ν + α)/(1 − α)`, the t.i.p. `mpTip` depending
  only on `a` and `Φ`).
* Step 3 (p. 635): `mp_step3`: for bounded paths and the second-order dispersion law,
  `∑βᵗ[−½Λ(x_t − x*)² − (1 − α)Δ̂_t] = −(Ω/2)∑βᵗ[λ(x_t − x*)² + π_t²]`,
  `Ω = εθ/(Θ(1 − θ)(1 − θβ))`, `λ = Λ/Ω`; `mp_omega_pos`, `mp_lam_pos`: `Ω, λ > 0`;
  `mp_xstar_zero_iff`: `x* = 0` iff `Φ = 0` (distortions move `x*` only, `λ` does not involve
  `Φ`).

Expectations are taken path by path: the identities of Step 3 hold for every realisation, so
they hold under `E` whenever the sums may be interchanged with it.
-/

namespace Miao.NewKeynesian

/-! ### The Taylor expansion of `u` -/

/-- Miao, p. 632: `(e^{c} − e^{c̄})/e^{c̄} = ĉ + ĉ²/2 + R` with `ĉ = c − c̄` and `|R| ≤ |ĉ|³` for
`|ĉ| ≤ 1`. -/
theorem mp_taylor_exp {c cbar : ℝ} (h : |c - cbar| ≤ 1) :
    |(Real.exp c - Real.exp cbar) / Real.exp cbar - ((c - cbar) + (c - cbar) ^ 2 / 2)| ≤
      |c - cbar| ^ 3 := by
  have e : (Real.exp c - Real.exp cbar) / Real.exp cbar = Real.exp (c - cbar) - 1 := by
    rw [Real.exp_sub]
    field_simp
  have hb := Real.exp_bound h (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    Nat.succ_eq_add_one] at hb
  norm_num at hb
  rw [e]
  have e2 : Real.exp (c - cbar) - 1 - ((c - cbar) + (c - cbar) ^ 2 / 2) =
      Real.exp (c - cbar) - (1 + (c - cbar) + (c - cbar) ^ 2 / 2) := by ring
  rw [e2]
  refine hb.trans ?_
  have := pow_nonneg (abs_nonneg (c - cbar)) 3
  nlinarith

/-- For (19.1), `u_CC = −γC^{−γ−1}`, so `u_CC C/u_C = −γ` (`C > 0`). -/
theorem mp_uCC {γ C : ℝ} (hC : 0 < C) :
    HasDerivAt (fun c => c ^ (-γ)) (-γ * C ^ (-γ - 1)) C ∧
      -γ * C ^ (-γ - 1) * C / C ^ (-γ) = -γ := by
  refine ⟨Real.hasDerivAt_rpow_const (Or.inl hC.ne'), ?_⟩
  rw [Real.rpow_sub hC, Real.rpow_one]
  field_simp

/-- For (19.1), `u_N = −χN^ν` has derivative `u_NN = −χνN^{ν−1}`, so `u_NN N/u_N = ν`
(`N, χ > 0`). -/
theorem mp_uNN {χ ν N : ℝ} (hχ : 0 < χ) (hN : 0 < N) :
    HasDerivAt (fun n => -(χ * n ^ ν)) (-(χ * (ν * N ^ (ν - 1)))) N ∧
      -(χ * (ν * N ^ (ν - 1))) * N / (-(χ * N ^ ν)) = ν := by
  refine ⟨((Real.hasDerivAt_rpow_const (Or.inl hN.ne')).const_mul χ).neg, ?_⟩
  rw [Real.rpow_sub hN, Real.rpow_one]
  have : 0 < N ^ ν := Real.rpow_pos_of_pos hN _
  field_simp

/-- **The truncation step** (Miao, p. 632, "keeping terms up to second order"). With
`u_CC C² = −γu_C C` and `u_NN N² = νu_N N`, the second display on p. 632,
`u_C C(ĉ + ĉ²/2) + u_N N(n̂ + n̂²/2) + ½u_CC C²(ĉ + ĉ²/2)² + ½u_NN N²(n̂ + n̂²/2)²`, equals
`u_C C[ĉ + (1 − γ)ĉ²/2] + u_N N[n̂ + (1 + ν)n̂²/2]` plus the third- and fourth-order terms
`−γu_C C(ĉ³ + ĉ⁴/4)/2 + νu_N N(n̂³ + n̂⁴/4)/2`. -/
theorem mp_eq_19_30_truncation {γ ν uCC uC uNN uN c n : ℝ} (hc : uCC = -γ * uC)
    (hn : uNN = ν * uN) :
    uC * (c + c ^ 2 / 2) + uN * (n + n ^ 2 / 2) + 1 / 2 * uCC * (c + c ^ 2 / 2) ^ 2 +
        1 / 2 * uNN * (n + n ^ 2 / 2) ^ 2 =
      uC * (c + (1 - γ) / 2 * c ^ 2) + uN * (n + (1 + ν) / 2 * n ^ 2) +
        (-γ * uC * (c ^ 3 + c ^ 4 / 4) / 2 + ν * uN * (n ^ 3 + n ^ 4 / 4) / 2) := by
  rw [hc, hn]
  ring

/-- **The exact form of `(u_t − u)/(u_C C)`** (Miao, p. 632). For (19.1) with `γ ≠ 1`,
`ν ≠ −1`, `C̄, N̄ > 0`, `C = C̄e^ĉ`, `N = N̄e^n̂`, `u_C C = C̄^{−γ}C̄` and
`u_N N = −χN̄^νN̄`: `(u_t − u)/(u_C C) = (e^{(1−γ)ĉ} − 1)/(1 − γ) +
(u_N N/(u_C C))(e^{(1+ν)n̂} − 1)/(1 + ν)`. -/
theorem mp_util_exact {γ χ ν C N c n : ℝ} (hγ : γ ≠ 1) (hν : ν ≠ -1) (hC : 0 < C)
    (hN : 0 < N) :
    (mpU γ χ ν (C * Real.exp c) (N * Real.exp n) - mpU γ χ ν C N) / (C ^ (-γ) * C) =
      (Real.exp ((1 - γ) * c) - 1) / (1 - γ) +
        (-(χ * N ^ ν) * N) / (C ^ (-γ) * C) * ((Real.exp ((1 + ν) * n) - 1) / (1 + ν)) := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h2 : (1 + ν) ≠ 0 := fun h => hν (by linarith)
  have hCg : C ^ (-γ) * C = C ^ (1 - γ) := by
    rw [sub_eq_neg_add, Real.rpow_add hC, Real.rpow_one]
  have hNn : N ^ ν * N = N ^ (1 + ν) := by
    rw [add_comm, Real.rpow_add hN, Real.rpow_one]
  have hCp : 0 < C ^ (1 - γ) := Real.rpow_pos_of_pos hC _
  simp only [mpU]
  rw [Real.mul_rpow hC.le (Real.exp_pos c).le, Real.mul_rpow hN.le (Real.exp_pos n).le,
    ← Real.exp_mul, ← Real.exp_mul, hCg,
    show -(χ * N ^ ν) * N = -(χ * N ^ (1 + ν)) by rw [← hNn]; ring, mul_comm c, mul_comm n]
  field_simp
  ring

/-- `|(e^{kx} − 1)/k − x − kx²/2| ≤ k²|x|³` for `k ≠ 0`, `|kx| ≤ 1`. -/
theorem mp_exp_quad_bound {k x : ℝ} (hk : k ≠ 0) (h : |k * x| ≤ 1) :
    |(Real.exp (k * x) - 1) / k - (x + k / 2 * x ^ 2)| ≤ k ^ 2 * |x| ^ 3 := by
  have hb := mp_taylor_exp (c := k * x) (cbar := 0) (by simpa using h)
  simp only [sub_zero, Real.exp_zero, div_one] at hb
  have e : (Real.exp (k * x) - 1) / k - (x + k / 2 * x ^ 2) =
      (Real.exp (k * x) - 1 - (k * x + (k * x) ^ 2 / 2)) / k := by
    field_simp
  rw [e, abs_div, div_le_iff₀ (abs_pos.2 hk)]
  calc |Real.exp (k * x) - 1 - (k * x + (k * x) ^ 2 / 2)| ≤ |k * x| ^ 3 := hb
    _ = k ^ 2 * |x| ^ 3 * |k| := by
        rw [abs_mul, mul_pow, ← sq_abs k]
        ring

/-- **(19.30)** (Miao, p. 632), as a precise Taylor statement. For (19.1) with `γ ≠ 1`,
`ν ≠ −1`, `C̄, N̄ > 0`, write `s = u_N N/(u_C C)`. Then
`(u_t − u)/(u_C C) = ĉ + (1 − γ)ĉ²/2 + s(n̂ + (1 + ν)n̂²/2) + R` with
`|R| ≤ (1 − γ)²|ĉ|³ + |s|(1 + ν)²|n̂|³` whenever `|(1 − γ)ĉ| ≤ 1` and `|(1 + ν)n̂| ≤ 1`. -/
theorem eq_19_30 {γ χ ν C N c n : ℝ} (hγ : γ ≠ 1) (hν : ν ≠ -1) (hC : 0 < C) (hN : 0 < N)
    (hc : |(1 - γ) * c| ≤ 1) (hn : |(1 + ν) * n| ≤ 1) :
    |(mpU γ χ ν (C * Real.exp c) (N * Real.exp n) - mpU γ χ ν C N) / (C ^ (-γ) * C) -
        (c + (1 - γ) / 2 * c ^ 2 +
          (-(χ * N ^ ν) * N) / (C ^ (-γ) * C) * (n + (1 + ν) / 2 * n ^ 2))| ≤
      (1 - γ) ^ 2 * |c| ^ 3 + |(-(χ * N ^ ν) * N) / (C ^ (-γ) * C)| * ((1 + ν) ^ 2 * |n| ^ 3) := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h2 : (1 + ν) ≠ 0 := fun h => hν (by linarith)
  rw [mp_util_exact hγ hν hC hN]
  set s := (-(χ * N ^ ν) * N) / (C ^ (-γ) * C)
  have e : (Real.exp ((1 - γ) * c) - 1) / (1 - γ) + s * ((Real.exp ((1 + ν) * n) - 1) / (1 + ν)) -
      (c + (1 - γ) / 2 * c ^ 2 + s * (n + (1 + ν) / 2 * n ^ 2)) =
      ((Real.exp ((1 - γ) * c) - 1) / (1 - γ) - (c + (1 - γ) / 2 * c ^ 2)) +
        s * ((Real.exp ((1 + ν) * n) - 1) / (1 + ν) - (n + (1 + ν) / 2 * n ^ 2)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add (mp_exp_quad_bound h1 hc) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (mp_exp_quad_bound h2 hn) (abs_nonneg s)

/-- **(19.30), little-o form** (Miao, p. 632): the remainder of (19.30) is `o(ĉ² + n̂²)`: for
every `ε > 0` there is `δ > 0` with `|R| ≤ ε(ĉ² + n̂²)` whenever `|ĉ|, |n̂| < δ`. -/
theorem eq_19_30_littleO {γ χ ν C N : ℝ} (hγ : γ ≠ 1) (hν : ν ≠ -1) (hC : 0 < C) (hN : 0 < N) :
    ∀ ε > 0, ∃ δ > 0, ∀ c n, |c| < δ → |n| < δ →
      |(mpU γ χ ν (C * Real.exp c) (N * Real.exp n) - mpU γ χ ν C N) / (C ^ (-γ) * C) -
        (c + (1 - γ) / 2 * c ^ 2 +
          (-(χ * N ^ ν) * N) / (C ^ (-γ) * C) * (n + (1 + ν) / 2 * n ^ 2))| ≤
      ε * (c ^ 2 + n ^ 2) := by
  intro ε hε
  set s := (-(χ * N ^ ν) * N) / (C ^ (-γ) * C)
  set B := (1 - γ) ^ 2 + |s| * (1 + ν) ^ 2 + |1 - γ| + |1 + ν| + 1
  have hB : 0 < B := by positivity
  refine ⟨min (1 / B) (ε / B), lt_min (div_pos one_pos hB) (div_pos hε hB),
    fun c n hc hn => ?_⟩
  have hc1 := (lt_min_iff.1 hc).1
  have hn1 := (lt_min_iff.1 hn).1
  have hc2 := (lt_min_iff.1 hc).2
  have hn2 := (lt_min_iff.1 hn).2
  have hc1' : |c| * B < 1 := by rwa [lt_div_iff₀ hB] at hc1
  have hn1' : |n| * B < 1 := by rwa [lt_div_iff₀ hB] at hn1
  have hcB : |c| * B < ε := by rwa [lt_div_iff₀ hB] at hc2
  have hnB : |n| * B < ε := by rwa [lt_div_iff₀ hB] at hn2
  have hkc : |(1 - γ) * c| ≤ 1 := by
    rw [abs_mul]
    have : |1 - γ| * |c| ≤ B * |c| := mul_le_mul_of_nonneg_right (by
      simp only [B]; nlinarith [sq_nonneg (1 - γ), abs_nonneg s, sq_nonneg (1 + ν),
        abs_nonneg (1 + ν)]) (abs_nonneg c)
    linarith [mul_comm B |c|]
  have hkn : |(1 + ν) * n| ≤ 1 := by
    rw [abs_mul]
    have : |1 + ν| * |n| ≤ B * |n| := mul_le_mul_of_nonneg_right (by
      simp only [B]; nlinarith [sq_nonneg (1 - γ), mul_nonneg (abs_nonneg s) (sq_nonneg (1 + ν)),
        abs_nonneg (1 - γ)]) (abs_nonneg n)
    linarith [mul_comm B |n|]
  refine (eq_19_30 hγ hν hC hN hkc hkn).trans ?_
  have hc3 : |c| ^ 3 = |c| * c ^ 2 := by rw [pow_succ, sq_abs]; ring
  have hn3 : |n| ^ 3 = |n| * n ^ 2 := by rw [pow_succ, sq_abs]; ring
  rw [hc3, hn3]
  have hA1 : (1 - γ) ^ 2 ≤ B := by
    simp only [B]; nlinarith [mul_nonneg (abs_nonneg s) (sq_nonneg (1 + ν)), abs_nonneg (1 - γ),
      abs_nonneg (1 + ν)]
  have hA2 : |s| * (1 + ν) ^ 2 ≤ B := by
    simp only [B]; nlinarith [sq_nonneg (1 - γ), abs_nonneg (1 - γ), abs_nonneg (1 + ν)]
  have hc0 := abs_nonneg c
  have hn0 := abs_nonneg n
  have e1 : (1 - γ) ^ 2 * (|c| * c ^ 2) ≤ ε * c ^ 2 := by
    have : (1 - γ) ^ 2 * |c| ≤ ε := by nlinarith
    nlinarith [sq_nonneg c]
  have e2 : |s| * ((1 + ν) ^ 2 * (|n| * n ^ 2)) ≤ ε * n ^ 2 := by
    have : |s| * (1 + ν) ^ 2 * |n| ≤ ε := by nlinarith
    nlinarith [sq_nonneg n]
  linarith

/-! ### Step 2 -/

/-- **Step 2, substitution** (Miao, p. 633). With `ĉ = ŷ` and Step 1's
`n̂ = (ŷ − a)/(1 − α) + Δ̂` (`α ≠ 1`), the right side of (19.30) equals
`ŷ + (1 − γ)ŷ²/2 + (s/(1 − α))[ŷ + (1 − α)Δ̂ + (1 + ν)(ŷ − a)²/(2(1 − α))]` plus the t.i.p.
`−sa/(1 − α)` plus the terms `s(1 + ν)((ŷ − a)Δ̂/(1 − α) + Δ̂²/2)` of order three and four
(`Δ̂` is of second order, Step 1). -/
theorem mp_step2_subst {α γ ν s y a d : ℝ} (hα : α ≠ 1) :
    y + (1 - γ) / 2 * y ^ 2 + s * (((y - a) / (1 - α) + d) +
        (1 + ν) / 2 * ((y - a) / (1 - α) + d) ^ 2) =
      y + (1 - γ) / 2 * y ^ 2 +
        s / (1 - α) * (y + (1 - α) * d + (1 + ν) / (2 * (1 - α)) * (y - a) ^ 2) +
        (-(s * a / (1 - α))) + s * (1 + ν) * ((y - a) * d / (1 - α) + d ^ 2 / 2) := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  field_simp
  ring

/-- **Step 2, the distortion `Φ`** (Miao, p. 634). If `−u_N/u_C = MPN(1 − Φ)`,
`MPN = (1 − α)Y/N` and `Y = C` (`u_C, C, N ≠ 0`), then `u_N N/(u_C C) = −(1 − α)(1 − Φ)`, so
`s/(1 − α) = −(1 − Φ)`. -/
theorem mp_step2_phi {α Φ uC uN C N Y : ℝ} (huC : uC ≠ 0) (hC : C ≠ 0) (hN : N ≠ 0)
    (hΦ : -uN / uC = (1 - α) * Y / N * (1 - Φ)) (hY : Y = C) :
    uN * N / (uC * C) = -((1 - α) * (1 - Φ)) := by
  rw [hY, div_eq_iff huC] at hΦ
  rw [div_eq_iff (mul_ne_zero huC hC)]
  have h' : uN * N = -((1 - α) * C / N * (1 - Φ) * uC) * N := by rw [← hΦ]; ring
  rw [h']
  field_simp

/-- **Step 2, small distortions** (Miao, p. 634). With `s/(1 − α) = −(1 − Φ)`, the expression
`ŷ + (1 − γ)ŷ²/2 − (1 − Φ)[ŷ + (1 − α)Δ̂ + (1 + ν)(ŷ − a)²/(2(1 − α))]` equals
`Φŷ − (1 − α)Δ̂ − ½[(1 + ν)(ŷ − a)²/(1 − α) − (1 − γ)ŷ²]` plus
`Φ[(1 − α)Δ̂ + (1 + ν)(ŷ − a)²/(2(1 − α))]`, the product of `Φ` with second-order terms that the
book neglects under the small-distortion assumption. -/
theorem mp_step2_small {α γ ν Φ y a d : ℝ} (hα : α ≠ 1) :
    y + (1 - γ) / 2 * y ^ 2 - (1 - Φ) * (y + (1 - α) * d + (1 + ν) / (2 * (1 - α)) * (y - a) ^ 2) =
      Φ * y - (1 - α) * d - 1 / 2 * ((1 + ν) / (1 - α) * (y - a) ^ 2 - (1 - γ) * y ^ 2) +
        Φ * ((1 - α) * d + (1 + ν) / (2 * (1 - α)) * (y - a) ^ 2) := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  field_simp
  ring

/-- `Λ = γ + (ν + α)/(1 − α)`, the weight on `(x_t − x*)²` before normalisation. -/
noncomputable def mpLambdaBar (α γ ν : ℝ) : ℝ := γ + (ν + α) / (1 - α)

/-- The terms independent of policy in Step 2: `½Λ(ŷ^f + x*)² − (1 + ν)a²/(2(1 − α))`. -/
noncomputable def mpTip (α γ ν Φ a : ℝ) : ℝ :=
  1 / 2 * mpLambdaBar α γ ν * ((1 + ν) / (γ * (1 - α) + ν + α) * a + mpXstar α γ ν Φ) ^ 2 -
    (1 + ν) / (2 * (1 - α)) * a ^ 2

/-- **Step 2, completing the square** (Miao, p. 634). With `ŷ^f = (1 + ν)a/D`,
`x* = Φ(1 − α)/D`, `D = γ(1 − α) + ν + α ≠ 0`, `α ≠ 1`, and the output gap `x = ŷ − ŷ^f`:
`Φŷ − (1 − α)Δ̂ − ½[(1 + ν)(ŷ − a)²/(1 − α) − (1 − γ)ŷ²] =
−½Λ(x − x*)² − (1 − α)Δ̂ + t.i.p.`, with t.i.p. `mpTip` independent of `ŷ` and `Δ̂`. The
intermediate line `−½Λ[ŷ² − 2(x* + ŷ^f)ŷ] − (1 − α)Δ̂ + t.i.p.` is the second conjunct. -/
theorem mp_step2_square {α γ ν Φ y a d : ℝ} (hα : α ≠ 1) (hD : γ * (1 - α) + ν + α ≠ 0) :
    (Φ * y - (1 - α) * d - 1 / 2 * ((1 + ν) / (1 - α) * (y - a) ^ 2 - (1 - γ) * y ^ 2) =
      -(1 / 2) * mpLambdaBar α γ ν *
          (y - (1 + ν) / (γ * (1 - α) + ν + α) * a - mpXstar α γ ν Φ) ^ 2 -
        (1 - α) * d + mpTip α γ ν Φ a) ∧
    (Φ * y - (1 - α) * d - 1 / 2 * ((1 + ν) / (1 - α) * (y - a) ^ 2 - (1 - γ) * y ^ 2) =
      -(1 / 2) * mpLambdaBar α γ ν * (y ^ 2 - 2 * (mpXstar α γ ν Φ +
          (1 + ν) / (γ * (1 - α) + ν + α) * a) * y) - (1 - α) * d +
        (-(1 + ν) / (2 * (1 - α)) * a ^ 2)) := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  simp only [mpTip, mpLambdaBar, mpXstar]
  set D := γ * (1 - α) + ν + α with hDdef
  constructor
  · field_simp
    rw [hDdef]
    ring
  · field_simp
    rw [hDdef]
    ring

/-! ### Step 3 -/

/-- `Ω = εθ/(Θ(1 − θ)(1 − θβ))` (Miao, p. 635). -/
noncomputable def mpOmega (α ε θ β : ℝ) : ℝ := ε * θ / (mpTheta α ε * (1 - θ) * (1 - θ * β))

/-- `λ = (γ + (ν + α)/(1 − α))/Ω` (Miao, p. 635). -/
noncomputable def mpLam (α γ ν ε θ β : ℝ) : ℝ := mpLambdaBar α γ ν / mpOmega α ε θ β

/-- `Ω > 0` for `0 ≤ α < 1`, `ε > 0`, `0 < θ < 1`, `β < 1`. -/
theorem mp_omega_pos {α ε θ β : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hβ1 : β < 1) : 0 < mpOmega α ε θ β := by
  have h1 : 0 < 1 - α := by linarith
  have hT : 0 < mpTheta α ε := div_pos h1 (by nlinarith)
  have hθβ : 0 < 1 - θ * β := by nlinarith
  exact div_pos (mul_pos hε hθ0) (mul_pos (mul_pos hT (by linarith)) hθβ)

/-- `λ > 0` for `γ > 0`, `ν ≥ 0` (with the conditions of `mp_omega_pos`). -/
theorem mp_lam_pos {α γ ν ε θ β : ℝ} (hγ : 0 < γ) (hν : 0 ≤ ν) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hε : 0 < ε) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1) :
    0 < mpLam α γ ν ε θ β := by
  have h1 : 0 < 1 - α := by linarith
  exact div_pos (add_pos_of_pos_of_nonneg hγ (div_nonneg (by linarith) h1.le))
    (mp_omega_pos hα0 hα1 hε hθ0 hθ1 hβ1)

/-- **Step 3** (Miao, p. 635). Let `0 ≤ α < 1`, `ε > 0`, `0 < θ < 1`, `0 ≤ β < 1`, `π` and `x`
bounded, and `Δ̂` follow the second-order law of Step 1 (`Δ̂_0 = Kπ_0²`,
`Δ̂_{t+1} = θΔ̂_t + Kπ_{t+1}²`). Then the discounted sum of the Step 2 approximation is
`∑βᵗ[−½Λ(x_t − x*)² − (1 − α)Δ̂_t] = −(Ω/2)∑βᵗ[λ(x_t − x*)² + π_t²]`. -/
theorem mp_step3 {α γ ν ε θ β xs M : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (pin x d : ℕ → ℝ)
    (hM : ∀ t, |pin t| ≤ M) (hMx : ∀ t, |x t - xs| ≤ M) (h0 : d 0 = mpK α ε θ * pin 0 ^ 2)
    (hs : ∀ t, d (t + 1) = θ * d t + mpK α ε θ * pin (t + 1) ^ 2) :
    ∑' t, β ^ t * (-(1 / 2) * mpLambdaBar α γ ν * (x t - xs) ^ 2 - (1 - α) * d t) =
      -(mpOmega α ε θ β / 2) *
        ∑' t, β ^ t * (mpLam α γ ν ε θ β * (x t - xs) ^ 2 + pin t ^ 2) := by
  have hg := summable_geometric_of_lt_one hβ0 hβ1
  have hO := mp_omega_pos hα0 hα1 hε hθ0 hθ1 hβ1
  have hsq : ∀ f : ℕ → ℝ, (∀ t, |f t| ≤ M) → Summable fun t => β ^ t * f t ^ 2 := by
    intro f hf
    refine Summable.of_norm_bounded (g := fun t => M ^ 2 * β ^ t) (hg.mul_left _) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm, abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hf t) 2)
      (pow_nonneg hβ0 t)
  have hsx := hsq (fun t => x t - xs) hMx
  have hsp := hsq pin hM
  have hdb := mp_disp_bounded hθ0.le hθ1 pin d hM h0 hs
  have hsd : Summable fun t => β ^ t * d t := by
    refine Summable.of_norm_bounded (g := fun t => |mpK α ε θ| * M ^ 2 / (1 - θ) * β ^ t)
      (hg.mul_left _) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
    exact mul_le_mul_of_nonneg_right (hdb t) (pow_nonneg hβ0 t)
  have hD := mp_dispersion_sum hθ0.le hθ1 hβ0 hβ1 pin d hM h0 hs
  have hθβ : 1 - θ * β ≠ 0 := by nlinarith
  have hα : α ≠ 1 := hα1.ne
  have ha : (1 - α) ≠ 0 := by linarith
  have hd : 1 - α + α * ε ≠ 0 := by nlinarith
  have hK := mp_K_Theta (β := β) hα hd hθ1.ne hθβ
  have hKO : (1 - α) * (mpK α ε θ / (1 - θ * β)) = mpOmega α ε θ β / 2 := by
    rw [hK, mpOmega]
    have hT : mpTheta α ε ≠ 0 := div_ne_zero ha hd
    have h1 : (1 - θ) ≠ 0 := by linarith
    field_simp
  have e1 : ∀ t, β ^ t * (-(1 / 2) * mpLambdaBar α γ ν * (x t - xs) ^ 2 - (1 - α) * d t) =
      (-(1 / 2) * mpLambdaBar α γ ν) * (β ^ t * (x t - xs) ^ 2) + (-(1 - α)) * (β ^ t * d t) :=
    fun t => by ring
  have e2 : ∀ t, β ^ t * (mpLam α γ ν ε θ β * (x t - xs) ^ 2 + pin t ^ 2) =
      mpLam α γ ν ε θ β * (β ^ t * (x t - xs) ^ 2) + β ^ t * pin t ^ 2 := fun t => by ring
  rw [tsum_congr e1, tsum_congr e2, (hsx.mul_left _).tsum_add (hsd.mul_left _),
    (hsx.mul_left _).tsum_add hsp, tsum_mul_left, tsum_mul_left, tsum_mul_left, hD]
  have hL : mpLam α γ ν ε θ β * mpOmega α ε θ β = mpLambdaBar α γ ν := by
    rw [mpLam, div_mul_cancel₀ _ hO.ne']
  linear_combination ((1 / 2) * ∑' t, β ^ t * (x t - xs) ^ 2) * hL -
    (∑' t, β ^ t * pin t ^ 2) * hKO

/-- Miao, p. 635: "when there is no economic distortion, `Φ = 0` so that `x* = 0`"; and
`x* = 0` only if `Φ = 0` (for `α < 1`, `D ≠ 0`). The weight `λ = mpLam` does not involve `Φ`. -/
theorem mp_xstar_zero_iff {α γ ν Φ : ℝ} (hα : α < 1) (hD : γ * (1 - α) + ν + α ≠ 0) :
    mpXstar α γ ν Φ = 0 ↔ Φ = 0 := by
  have ha : (1 - α) ≠ 0 := by linarith
  simp only [mpXstar, div_eq_zero_iff, mul_eq_zero, hD, ha, or_false]

end Miao.NewKeynesian
