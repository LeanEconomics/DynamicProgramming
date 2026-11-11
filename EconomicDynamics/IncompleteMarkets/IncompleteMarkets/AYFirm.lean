/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# §17.1.2: production, the firm's first-order conditions and capital demand

Miao, §17.1.2, p. 562, with the capital demand curve `K^d(r)` of §17.1.3 (p. 564) and Steps 1,
2 and 5 of the algorithm of §17.1.4 (pp. 564–566). A representative firm with constant returns
to scale technology `Y = F(K, L)` maximises `F(K, L) − (r + δ)K − wL`.

* `ay_CRS`, `ay_profit`: constant returns to scale (on the nonnegative orthant), profits.
* `ay_isLocalMax_of_max`, `eq_17_5_17_6`: at an interior profit maximum, `F_K = r + δ` (17.5) and
  `F_L = w` (17.6).
* `ay_euler_crs`, `ay_zero_profit`: Euler's theorem `F = F_K K + F_L L` for CRS technologies,
  hence zero profits at the optimum.
* Cobb–Douglas `F(K, L) = AK^αL^{1−α}` (`ay_cdF`, used in Example 17.1.1 and footnote 2):
  `ay_cd_crs`, the partial derivatives `ay_cd_hasDerivAt_K`, `ay_cd_hasDerivAt_L`; the capital
  demand `K^d(r) = F_K^{-1}(r + δ)` (Step 5) `ay_Kd`, with `ay_Kd_foc` (it solves (17.5)),
  `ay_Kd_unique`, `ay_Kd_strictAnti` (the demand curve slopes down), `ay_Kd_continuousOn`,
  `ay_Kd_tendsto` (`K^d → ∞` as `r ↓ −δ`, the lower bound of Step 1), `ay_FK_pos_rate`
  (`r = F_K − δ > −δ`); the wage `w(r) = F_L(K^d(r), L)` of Step 2 with `ay_wage_continuousOn`
  ("`w` is a continuous function of `r`", p. 564).
* `ay_saving_rate`, `ay_saving_rate_misprint`: footnote 2, p. 568: the saving rate is
  `δK/F(K, L) = δα/(r + δ)`; the printed `δK/(AF(K, L))` with `F = AK^αL^{1−α}` equals
  `δα/((r + δ)A)`, which differs unless `A = 1`.
-/

namespace Miao.IncompleteMarkets

open Filter Topology

/-- Miao, p. 562: `F` has **constant returns to scale** on the nonnegative orthant:
`F(tK, tL) = tF(K, L)` for `t > 0`, `K, L ≥ 0`. -/
def ay_CRS (F : ℝ × ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ p : ℝ × ℝ, 0 ≤ p.1 → 0 ≤ p.2 → F (t • p) = t * F p

/-- Miao, p. 562: the firm's profit `F(K, L) − (r + δ)K − wL` (the rental rate of capital is
`r + δ`). -/
def ay_profit (F : ℝ × ℝ → ℝ) (r δ w : ℝ) (p : ℝ × ℝ) : ℝ := F p - (r + δ) * p.1 - w * p.2

/-- Miao, p. 562: a profit maximum over `K, L ≥ 0` at an interior point `K, L > 0` is a local
maximum. -/
theorem ay_isLocalMax_of_max {F : ℝ × ℝ → ℝ} {r δ w : ℝ} {p : ℝ × ℝ} (hK : 0 < p.1)
    (hL : 0 < p.2)
    (hmax : ∀ q : ℝ × ℝ, 0 ≤ q.1 → 0 ≤ q.2 → ay_profit F r δ w q ≤ ay_profit F r δ w p) :
    IsLocalMax (ay_profit F r δ w) p := by
  have hn : Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) ∈ 𝓝 p :=
    prod_mem_nhds (Ioi_mem_nhds hK) (Ioi_mem_nhds hL)
  filter_upwards [hn] with q hq
  exact hmax q (Set.mem_Ioi.1 hq.1).le (Set.mem_Ioi.1 hq.2).le

/-- Miao, (17.5)–(17.6), p. 562: static profit maximisation implies `F_K(K, L) = r + δ` and
`F_L(K, L) = w` (with `F_K = F′(1, 0)`, `F_L = F′(0, 1)` for the derivative `F′` at `(K, L)`). -/
theorem eq_17_5_17_6 {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {r δ w : ℝ} {p : ℝ × ℝ}
    (hF : HasFDerivAt F F' p) (hmax : IsLocalMax (ay_profit F r δ w) p) :
    F' (1, 0) = r + δ ∧ F' (0, 1) = w := by
  have hd : HasFDerivAt (ay_profit F r δ w)
      (F' - (r + δ) • ContinuousLinearMap.fst ℝ ℝ ℝ - w • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (hF.sub ((hasFDerivAt_fst).const_mul (r + δ))).sub ((hasFDerivAt_snd).const_mul w)
  have h0 := hmax.hasFDerivAt_eq_zero hd
  have h1 := congrArg (fun f : ℝ × ℝ →L[ℝ] ℝ => f (1, 0)) h0
  have h2 := congrArg (fun f : ℝ × ℝ →L[ℝ] ℝ => f (0, 1)) h0
  simp at h1 h2
  constructor <;> linarith

/-- Miao, p. 562 (Euler's theorem): for a CRS technology differentiable at `(K, L)`, `K, L > 0`,
`F(K, L) = F_K K + F_L L`. -/
theorem ay_euler_crs {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ} (hcrs : ay_CRS F)
    (hK : 0 < p.1) (hL : 0 < p.2) (hF : HasFDerivAt F F' p) :
    F p = F' (1, 0) * p.1 + F' (0, 1) * p.2 := by
  have hs : HasDerivAt (fun t : ℝ => t • p) p 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const p
  have hF1 : HasFDerivAt F F' ((fun t : ℝ => t • p) 1) := by simpa using hF
  have h1 := hF1.comp_hasDerivAt (1 : ℝ) hs
  have hmul : HasDerivAt (fun t : ℝ => t * F p) (F p) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (F p)
  have hev : (fun t : ℝ => t * F p) =ᶠ[𝓝 1] F ∘ fun t : ℝ => t • p := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht
    exact (hcrs t ht p hK.le hL.le).symm
  have h2 := hmul.congr_of_eventuallyEq hev.symm
  have hu := h1.unique h2
  have hp : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [← hu, hp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add]
  ring

/-- Miao, p. 562: with constant returns to scale, the first-order conditions (17.5)–(17.6)
imply zero profits, `F(K, L) = (r + δ)K + wL`. -/
theorem ay_zero_profit {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {r δ w : ℝ} {p : ℝ × ℝ}
    (hcrs : ay_CRS F) (hK : 0 < p.1) (hL : 0 < p.2) (hF : HasFDerivAt F F' p)
    (h5 : F' (1, 0) = r + δ) (h6 : F' (0, 1) = w) :
    ay_profit F r δ w p = 0 := by
  rw [ay_profit, ay_euler_crs hcrs hK hL hF, h5, h6]
  ring

/-- Miao, p. 568: the **Cobb–Douglas** technology `F(K, L) = AK^αL^{1−α}`. -/
noncomputable def ay_cdF (A α : ℝ) (p : ℝ × ℝ) : ℝ := A * p.1 ^ α * p.2 ^ (1 - α)

/-- The Cobb–Douglas marginal product of capital `F_K = αA(K/L)^{α−1}`. -/
noncomputable def ay_cdFK (A α K L : ℝ) : ℝ := α * A * (K / L) ^ (α - 1)

/-- The Cobb–Douglas marginal product of labour `F_L = (1 − α)A(K/L)^α`. -/
noncomputable def ay_cdFL (A α K L : ℝ) : ℝ := (1 - α) * A * (K / L) ^ α

/-- Miao, p. 568: the Cobb–Douglas technology has constant returns to scale. -/
theorem ay_cd_crs (A α : ℝ) : ay_CRS (ay_cdF A α) := by
  intro t ht p hK hL
  simp only [ay_cdF, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [Real.mul_rpow ht.le hK, Real.mul_rpow ht.le hL]
  have : t ^ α * t ^ (1 - α) = t := by
    rw [← Real.rpow_add ht, add_sub_cancel, Real.rpow_one]
  calc A * (t ^ α * p.1 ^ α) * (t ^ (1 - α) * p.2 ^ (1 - α))
      = (t ^ α * t ^ (1 - α)) * (A * p.1 ^ α * p.2 ^ (1 - α)) := by ring
    _ = t * (A * p.1 ^ α * p.2 ^ (1 - α)) := by rw [this]

/-- `K^{α−1}L^{1−α} = (K/L)^{α−1}` for `K, L > 0`. -/
theorem ay_rpow_ratio {K L : ℝ} (hK : 0 < K) (hL : 0 < L) (α : ℝ) :
    K ^ (α - 1) * L ^ (1 - α) = (K / L) ^ (α - 1) := by
  rw [Real.div_rpow hK.le hL.le, show 1 - α = -(α - 1) by ring, Real.rpow_neg hL.le, div_eq_mul_inv]

/-- Miao, (17.5): the Cobb–Douglas partial derivative in `K` is `F_K = αA(K/L)^{α−1}`. -/
theorem ay_cd_hasDerivAt_K (A α : ℝ) {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    HasDerivAt (fun k => ay_cdF A α (k, L)) (ay_cdFK A α K L) K := by
  have h := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul A).mul_const
    (L ^ (1 - α))
  simp only [ay_cdF]
  convert h using 1
  rw [ay_cdFK, ← ay_rpow_ratio hK hL]
  ring

/-- Miao, (17.6): the Cobb–Douglas partial derivative in `L` is `F_L = (1 − α)A(K/L)^α`. -/
theorem ay_cd_hasDerivAt_L (A α : ℝ) {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    HasDerivAt (fun l => ay_cdF A α (K, l)) (ay_cdFL A α K L) L := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hL.ne')).const_mul (A * K ^ α)
  simp only [ay_cdF]
  convert h using 1
  rw [ay_cdFL, Real.div_rpow hK.le hL.le, show 1 - α - 1 = -α by ring, Real.rpow_neg hL.le,
    div_eq_mul_inv]
  ring

/-- Miao, p. 564 and Step 5, p. 566: the **capital demand** `K^d(r) = F_K^{-1}(r + δ)`, for the
Cobb–Douglas technology `K^d(r) = L(αA/(r + δ))^{1/(1−α)}`. -/
noncomputable def ay_Kd (A α δ L r : ℝ) : ℝ := L * (α * A / (r + δ)) ^ (1 / (1 - α))

/-- Miao, (17.5), Step 5: `K^d(r)` solves `F_K(K, L) = r + δ` (`r > −δ`). -/
theorem ay_Kd_foc {A α δ L r : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L)
    (hr : -δ < r) : ay_cdFK A α (ay_Kd A α δ L r) L = r + δ := by
  have hrd : 0 < r + δ := by linarith
  have hx : 0 < α * A / (r + δ) := div_pos (mul_pos hα0 hA) hrd
  rw [ay_cdFK, ay_Kd, mul_div_cancel_left₀ _ hL.ne', ← Real.rpow_mul hx.le,
    show 1 / (1 - α) * (α - 1) = -1 by field_simp [(sub_pos.2 hα1).ne']; ring,
    Real.rpow_neg_one, inv_div]
  field_simp

/-- Miao, (17.5): `F_K(·, L)` is strictly decreasing in `K` (`0 < α < 1`). -/
theorem ay_cdFK_strictAnti {A α L : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L) :
    StrictAntiOn (fun K => ay_cdFK A α K L) (Set.Ioi 0) := by
  intro K hK K' _ hKK
  simp only [ay_cdFK]
  have := Real.rpow_lt_rpow_of_neg (div_pos (Set.mem_Ioi.1 hK) hL)
    (div_lt_div_of_pos_right hKK hL) (by linarith : α - 1 < 0)
  exact mul_lt_mul_of_pos_left this (mul_pos hα0 hA)

/-- Miao, Step 5, p. 566: `K^d(r)` is the unique `K > 0` with `F_K(K, L) = r + δ`. -/
theorem ay_Kd_unique {A α δ L r K : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L)
    (hr : -δ < r) (hK : 0 < K) (hfoc : ay_cdFK A α K L = r + δ) : K = ay_Kd A α δ L r := by
  have hx : 0 < α * A / (r + δ) := div_pos (mul_pos hα0 hA) (by linarith)
  have hKd : 0 < ay_Kd A α δ L r := mul_pos hL (Real.rpow_pos_of_pos hx _)
  refine (ay_cdFK_strictAnti hA hα0 hα1 hL).injOn hK hKd ?_
  rw [hfoc, ay_Kd_foc hA hα0 hα1 hL hr]

/-- Miao, p. 564: the capital demand curve `K^d(r)` is downward sloping on `(−δ, ∞)`. -/
theorem ay_Kd_strictAnti {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L) :
    StrictAntiOn (ay_Kd A α δ L) (Set.Ioi (-δ)) := by
  intro r hr r' hr' hrr
  have h1 : 0 < r + δ := by linarith [Set.mem_Ioi.1 hr]
  have hxy : α * A / (r' + δ) < α * A / (r + δ) :=
    div_lt_div_of_pos_left (mul_pos hα0 hA) h1 (by linarith)
  have := Real.rpow_lt_rpow (div_pos (mul_pos hα0 hA) (by linarith)).le hxy
    (one_div_pos.2 (sub_pos.2 hα1))
  exact mul_lt_mul_of_pos_left this hL

/-- Miao, p. 564: `K^d` is continuous on `(−δ, ∞)`. -/
theorem ay_Kd_continuousOn {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α) :
    ContinuousOn (ay_Kd A α δ L) (Set.Ioi (-δ)) := by
  have hpos : ∀ r ∈ Set.Ioi (-δ), 0 < α * A / (r + δ) := fun r hr =>
    div_pos (mul_pos hα0 hA) (by linarith [Set.mem_Ioi.1 hr])
  have hc : ContinuousOn (fun r => α * A / (r + δ)) (Set.Ioi (-δ)) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const)
      fun r hr => by linarith [Set.mem_Ioi.1 hr]
  exact continuousOn_const.mul (hc.rpow_const fun r hr => Or.inl (hpos r hr).ne')

/-- Miao, Step 1, p. 564: `K^d(r) → ∞` as `r ↓ −δ`. -/
theorem ay_Kd_tendsto {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L) :
    Tendsto (ay_Kd A α δ L) (𝓝[>] (-δ)) atTop := by
  have h1 : Tendsto (fun r : ℝ => r + δ) (𝓝[>] (-δ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun r : ℝ => r + δ) (𝓝 (-δ)) (𝓝 (-δ + δ)) :=
        (continuous_id.add continuous_const).tendsto _
      rw [neg_add_cancel] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact Set.mem_Ioi.2 (by linarith [Set.mem_Ioi.1 hr])
  have h2 : Tendsto (fun r : ℝ => α * A / (r + δ)) (𝓝[>] (-δ)) atTop := by
    have := (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop (mul_pos hα0 hA)
    simpa [div_eq_mul_inv] using this
  have h3 := (tendsto_rpow_atTop (one_div_pos.2 (sub_pos.2 hα1))).comp h2
  exact h3.const_mul_atTop hL

/-- Miao, Step 1, p. 564: since `F_K > 0`, (17.5) forces `r = F_K − δ > −δ`. -/
theorem ay_FK_pos_rate {A α K L r δ : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hK : 0 < K) (hL : 0 < L)
    (h5 : ay_cdFK A α K L = r + δ) : -δ < r := by
  have : 0 < ay_cdFK A α K L := mul_pos (mul_pos hα0 hA) (Real.rpow_pos_of_pos (div_pos hK hL) _)
  linarith

/-- Miao, Step 2, p. 566: the wage implied by (17.5)–(17.6), `w(r) = F_L(K^d(r), L)`. -/
noncomputable def ay_wage (A α δ L r : ℝ) : ℝ := ay_cdFL A α (ay_Kd A α δ L r) L

/-- Miao, p. 564: "given (17.5) and (17.6), `w` is a continuous function of `r`". -/
theorem ay_wage_continuousOn {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α) :
    ContinuousOn (ay_wage A α δ L) (Set.Ioi (-δ)) := by
  have hc : ContinuousOn (fun r => ay_Kd A α δ L r / L) (Set.Ioi (-δ)) :=
    (ay_Kd_continuousOn hA hα0).div_const L
  exact continuousOn_const.mul (hc.rpow_const fun _ _ => Or.inr hα0.le)

/-- Miao, footnote 2, p. 568, corrected: at the capital demand `K = K^d(r)` the aggregate
saving rate is `δK/F(K, L) = δα/(r + δ)`. -/
theorem ay_saving_rate {A α δ L r : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L)
    (hr : -δ < r) :
    δ * ay_Kd A α δ L r / ay_cdF A α (ay_Kd A α δ L r, L) = δ * α / (r + δ) := by
  set K := ay_Kd A α δ L r
  have hrd : 0 < r + δ := by linarith
  have hK : 0 < K := mul_pos hL (Real.rpow_pos_of_pos (div_pos (mul_pos hα0 hA) hrd) _)
  have hfoc := ay_Kd_foc hA hα0 hα1 hL hr
  have hF : ay_cdF A α (K, L) * α = (r + δ) * K := by
    rw [← hfoc, ay_cdFK, ← ay_rpow_ratio hK hL, ay_cdF]
    simp only
    rw [Real.rpow_sub_one hK.ne']
    field_simp
  have hFpos : 0 < ay_cdF A α (K, L) := by
    simp only [ay_cdF]
    exact mul_pos (mul_pos hA (Real.rpow_pos_of_pos hK _)) (Real.rpow_pos_of_pos hL _)
  rw [div_eq_div_iff hFpos.ne' hrd.ne']
  linear_combination -δ * hF

/-- Miao, footnote 2, p. 568: the printed `δK/(AF(K, L))` with `F = AK^αL^{1−α}` equals
`δα/((r + δ)A)`, which is not `δα/(r + δ)` unless `A = 1` (for `δ > 0`). -/
theorem ay_saving_rate_misprint {A α δ L r : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hL : 0 < L) (hr : -δ < r) (hδ : 0 < δ) (hA1 : A ≠ 1) :
    δ * ay_Kd A α δ L r / (A * ay_cdF A α (ay_Kd A α δ L r, L)) ≠ δ * α / (r + δ) := by
  have h := ay_saving_rate hA hα0 hα1 hL hr
  rw [mul_comm A, ← div_div, h]
  intro heq
  have hpos : 0 < δ * α / (r + δ) := div_pos (mul_pos hδ hα0) (by linarith)
  rw [div_eq_iff hA.ne'] at heq
  exact hA1 (mul_left_cancel₀ hpos.ne' (heq.symm.trans (mul_one _).symm))

end Miao.IncompleteMarkets
