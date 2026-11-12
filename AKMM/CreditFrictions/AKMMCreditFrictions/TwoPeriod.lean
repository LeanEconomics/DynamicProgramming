/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The two-period model: closed forms

AKMM, §19.5, pp. 576–578, and the working-capital labour demand of §19.5.5, pp. 584–585.

Utility `u(c, ℓ) = ln(c − ℓ^ν)` and technology `F(z, k, ℓ) = zk^αℓ^{1−α}`. Write
`e = α + ν − 1`.

* Marginal utilities `u₁ = 1/(c − ℓ^ν)`, `u₂ = −νℓ^{ν−1}/(c − ℓ^ν)`, so `−u₂/u₁ = νℓ^{ν−1}`
  (`tp_hasDerivAt_u1`, `tp_hasDerivAt_u2`, `tp_mrs`); marginal products
  `F_k = αF/k` and `F_ℓ = (1 − α)zk^αℓ^{−α} = (1 − α)z(k/ℓ)^α = (1 − α)F/ℓ` (`tp_mpk`,
  `tp_mpl`, `tp_mpl_eq`, `tp_wage_bill`).
* **Labour** (p. 577): for `L > 0`, the condition `(1 − α)z(K/L)^α = ωνL^{ν−1}` holds iff
  `L = ((1 − α)/(ων))^{1/e} z^{1/e} K^{α/e}` (`tpL`, `tp_foc_iff`); `ω = 1` is the period-1
  condition from (19.4) and (19.8) (`tp_labour`), `ω = 1 + µ` the working-capital condition of
  p. 584. With `e > 0`, labour increases in `z` and `K` (`tp_L_strictMono_z`,
  `tp_L_strictMono_K`); with `e < 0` it decreases in `z` (`tp_L_strictAnti_z_of_neg`).
* **Output** (p. 577): `Y = zK^αL^{1−α} = ((1 − α)/ν)^{(1−α)/e} z^{ν/e} K^{να/e}` (`tpY`,
  `tp_Y_eq`), increasing in `z` and `K` (`tp_Y_strictMono_z`, `tp_Y_strictMono_K`).
* **The marginal product of capital** (p. 578): `F_k = α((1 − α)/ν)^{(1−α)/e} z^{ν/e}
  K^{να/e − 1} = αY/K` (`tpFk`, `tp_Fk_eq`), increasing in `z` and, for `ν > 1`, strictly
  decreasing in `K` (`tp_Fk_strictMono_z`, `tp_Fk_strictAnti_K`).
* **`g(z′, K′) = C′ − L′^ν`** (p. 577) with `C′ = (1 − δ)K′ + Y′`: `L^ν = (1 − α)Y/ν`
  (`tp_L_pow_nu`), so `g = (1 − δ)K′ + (e/ν)Y′` (`tp_g_eq`), increasing in `z′` and `K′` on
  the whole positive orthant when `e > 0` and `δ ≤ 1` (`tp_g_strictMono_z`,
  `tp_g_strictMono_K`): the book's "at least in the relevant range" is not needed.
* **Property 19.5.6** (p. 584): with working capital, labour
  `L = ((1 − α)/((1 + µ)ν))^{1/e} z^{1/e} K^{α/e}` (`tp_wc_labour`) is strictly decreasing in
  `µ` (`property_19_5_6`).

Departure: the book does not state a sign for `e = α + ν − 1`; its claims that labour and output
increase in `z` and `K` need `e > 0` (e.g. `ν > 1`), and fail for `e < 0`.
-/

namespace AKMM.CreditFrictions

open Set

/-- AKMM, p. 577 (with `ω = 1`) and p. 585 (with `ω = 1 + µ`): labour
`L = ((1 − α)/(ων))^{1/(α+ν−1)} z^{1/(α+ν−1)} K^{α/(α+ν−1)}`. -/
noncomputable def tpL (α ν ω z K : ℝ) : ℝ :=
  ((1 - α) / (ω * ν)) ^ (1 / (α + ν - 1)) * z ^ (1 / (α + ν - 1)) * K ^ (α / (α + ν - 1))

/-- AKMM, p. 577: output `Y = ((1 − α)/ν)^{(1−α)/(α+ν−1)} z^{ν/(α+ν−1)} K^{να/(α+ν−1)}`. -/
noncomputable def tpY (α ν z K : ℝ) : ℝ :=
  ((1 - α) / ν) ^ ((1 - α) / (α + ν - 1)) * z ^ (ν / (α + ν - 1)) *
    K ^ (ν * α / (α + ν - 1))

/-- AKMM, p. 578: `F_k = α((1 − α)/ν)^{(1−α)/(α+ν−1)} z^{ν/(α+ν−1)} K^{να/(α+ν−1) − 1}`. -/
noncomputable def tpFk (α ν z K : ℝ) : ℝ :=
  α * ((1 - α) / ν) ^ ((1 - α) / (α + ν - 1)) * z ^ (ν / (α + ν - 1)) *
    K ^ (ν * α / (α + ν - 1) - 1)

/-- AKMM, p. 577: `g(z, K) = C − L^ν` with `C = (1 − δ)K + Y`. -/
noncomputable def tpG (δ α ν z K : ℝ) : ℝ :=
  (1 - δ) * K + tpY α ν z K - tpL α ν 1 z K ^ ν

/-! ### Marginal utilities and marginal products -/

/-- AKMM, p. 577: `u₁(c, ℓ) = 1/(c − ℓ^ν)` for `u = ln(c − ℓ^ν)`, `c > ℓ^ν`. -/
theorem tp_hasDerivAt_u1 {c ℓ ν : ℝ} (h : ℓ ^ ν < c) :
    HasDerivAt (fun x => Real.log (x - ℓ ^ ν)) (1 / (c - ℓ ^ ν)) c := by
  have h1 : HasDerivAt (fun x : ℝ => x - ℓ ^ ν) 1 c := (hasDerivAt_id c).sub_const _
  convert h1.log (sub_ne_zero.2 (ne_of_gt h)) using 1

/-- AKMM, p. 577: `u₂(c, ℓ) = −νℓ^{ν−1}/(c − ℓ^ν)`, `ℓ > 0`, `c > ℓ^ν`. -/
theorem tp_hasDerivAt_u2 {c ℓ ν : ℝ} (hℓ : 0 < ℓ) (h : ℓ ^ ν < c) :
    HasDerivAt (fun x => Real.log (c - x ^ ν)) (-(ν * ℓ ^ (ν - 1)) / (c - ℓ ^ ν)) ℓ := by
  have h1 : HasDerivAt (fun x : ℝ => c - x ^ ν) (-(ν * ℓ ^ (ν - 1))) ℓ :=
    (Real.hasDerivAt_rpow_const (Or.inl hℓ.ne')).const_sub c
  exact h1.log (sub_ne_zero.2 (ne_of_gt h))

/-- AKMM, p. 577: the marginal rate of substitution `−u₂/u₁ = νℓ^{ν−1}`. -/
theorem tp_mrs {c ℓ ν : ℝ} (h : ℓ ^ ν < c) :
    -(-(ν * ℓ ^ (ν - 1)) / (c - ℓ ^ ν)) / (1 / (c - ℓ ^ ν)) = ν * ℓ ^ (ν - 1) := by
  have : c - ℓ ^ ν ≠ 0 := by linarith
  field_simp

/-- AKMM, p. 578: `F_k(z, K, L) = αzK^{α−1}L^{1−α} = αF/K`. -/
theorem tp_mpk {α z K L : ℝ} (hK : 0 < K) :
    HasDerivAt (fun k => z * k ^ α * L ^ (1 - α)) (α * (z * K ^ α * L ^ (1 - α)) / K) K := by
  have h := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul z).mul_const
    (L ^ (1 - α))
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one hK.ne']
  field_simp

/-- AKMM, p. 577: `F_ℓ(z, K, L) = (1 − α)zK^αL^{−α}`. -/
theorem tp_mpl {α z K L : ℝ} (hL : 0 < L) :
    HasDerivAt (fun l => z * K ^ α * l ^ (1 - α)) ((1 - α) * z * K ^ α * L ^ (-α)) L := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hL.ne')).const_mul (z * K ^ α)
  refine h.congr_deriv ?_
  rw [show 1 - α - 1 = -α by ring]
  ring

/-- AKMM, p. 577: `(1 − α)zK^αL^{−α} = (1 − α)z(K/L)^α`. -/
theorem tp_mpl_eq {α z K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) :
    (1 - α) * z * K ^ α * L ^ (-α) = (1 - α) * z * (K / L) ^ α := by
  rw [Real.div_rpow hK hL, Real.rpow_neg hL]
  ring

/-- AKMM, p. 578: the wage bill is labour's share, `F_ℓL = (1 − α)F` (used in (19.13)–(19.14)). -/
theorem tp_wage_bill {α z K L : ℝ} (hL : 0 < L) :
    (1 - α) * z * K ^ α * L ^ (-α) * L = (1 - α) * (z * K ^ α * L ^ (1 - α)) := by
  have : L ^ (1 - α) = L ^ (-α) * L := by
    rw [show 1 - α = -α + 1 by ring, Real.rpow_add hL, Real.rpow_one]
  rw [this]
  ring

/-! ### Labour -/

/-- `tpL` is the `1/e`-th power of `((1 − α)/(ων))zK^α`. -/
theorem tp_L_eq {α ν ω z K : ℝ} (hc : 0 ≤ (1 - α) / (ω * ν)) (hz : 0 ≤ z) (hK : 0 ≤ K) :
    tpL α ν ω z K = ((1 - α) / (ω * ν) * z * K ^ α) ^ (1 / (α + ν - 1)) := by
  unfold tpL
  rw [Real.mul_rpow (mul_nonneg hc hz) (Real.rpow_nonneg hK α), Real.mul_rpow hc hz,
    ← Real.rpow_mul hK]
  congr 2
  ring

/-- **Labour** (AKMM, p. 577 for `ω = 1`, p. 585 for `ω = 1 + µ`): for `L > 0`,
`(1 − α)z(K/L)^α = ωνL^{ν−1}` iff `L = ((1 − α)/(ων))^{1/e} z^{1/e} K^{α/e}`,
`e = α + ν − 1 ≠ 0`. -/
theorem tp_foc_iff {α ν ω z K L : ℝ} (hα : α < 1) (hν : 0 < ν) (hω : 0 < ω) (hz : 0 < z)
    (hK : 0 < K) (hL : 0 < L) (he : α + ν - 1 ≠ 0) :
    (1 - α) * z * (K / L) ^ α = ω * ν * L ^ (ν - 1) ↔ L = tpL α ν ω z K := by
  have hc : 0 < (1 - α) / (ω * ν) := div_pos (by linarith) (mul_pos hω hν)
  have hKa : 0 < K ^ α := Real.rpow_pos_of_pos hK α
  have hLa : 0 < L ^ α := Real.rpow_pos_of_pos hL α
  have hA : 0 < (1 - α) / (ω * ν) * z * K ^ α := by positivity
  rw [tp_L_eq hc.le hz.le hK.le, Real.div_rpow hK.le hL.le]
  have hLe : L ^ (α + ν - 1) = L ^ (ν - 1) * L ^ α := by
    rw [← Real.rpow_add hL]
    ring_nf
  have key : (1 - α) * z * (K ^ α / L ^ α) = ω * ν * L ^ (ν - 1) ↔
      L ^ (α + ν - 1) = (1 - α) / (ω * ν) * z * K ^ α := by
    rw [hLe]
    constructor
    · intro h
      field_simp at h ⊢
      linear_combination -h
    · intro h
      field_simp at h ⊢
      linear_combination -h
  rw [key, one_div]
  constructor
  · intro h
    rw [← h, Real.rpow_rpow_inv hL.le he]
  · intro h
    rw [h, Real.rpow_inv_rpow hA.le he]

/-- AKMM, p. 577: in period 1 the household's condition (19.8) with the wage from (19.4),
`u₁w = −u₂` with `w = (1 − α)z(K/L)^α`, `u₁ = 1/(C − L^ν)`, `u₂ = −νL^{ν−1}/(C − L^ν)`, is
`(1 − α)z(K/L)^α = νL^{ν−1}`, and so `L = ((1 − α)/ν)^{1/e} z^{1/e} K^{α/e}`. -/
theorem tp_labour {α ν z K L C : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (hL : 0 < L) (he : α + ν - 1 ≠ 0) (hC : L ^ ν < C)
    (h198 : 1 / (C - L ^ ν) * ((1 - α) * z * (K / L) ^ α) =
      -(-(ν * L ^ (ν - 1)) / (C - L ^ ν))) :
    L = tpL α ν 1 z K := by
  have hCL : C - L ^ ν ≠ 0 := by linarith
  refine (tp_foc_iff hα hν one_pos hz hK hL he).1 ?_
  field_simp at h198
  linear_combination h198

/-- AKMM, p. 577: "labor increases in TFP" (`e = α + ν − 1 > 0`). -/
theorem tp_L_strictMono_z {α ν ω K : ℝ} (hα : α < 1) (hν : 0 < ν) (hω : 0 < ω) (hK : 0 < K)
    (he : 0 < α + ν - 1) : StrictMonoOn (fun z => tpL α ν ω z K) (Ioi 0) := by
  intro z₁ hz₁ z₂ _ h
  have hc : 0 < (1 - α) / (ω * ν) := div_pos (by linarith) (mul_pos hω hν)
  have h1 := Real.rpow_lt_rpow (le_of_lt hz₁) h (one_div_pos.2 he)
  have h2 := Real.rpow_pos_of_pos hc (1 / (α + ν - 1))
  have h3 := Real.rpow_pos_of_pos hK (α / (α + ν - 1))
  simp only [tpL]
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h1 h2) h3

/-- AKMM, p. 577: "labor increases in … capital" (`α > 0`, `e > 0`). -/
theorem tp_L_strictMono_K {α ν ω z : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν) (hω : 0 < ω)
    (hz : 0 < z) (he : 0 < α + ν - 1) : StrictMonoOn (fun K => tpL α ν ω z K) (Ioi 0) := by
  intro K₁ hK₁ K₂ _ h
  have hc : 0 < (1 - α) / (ω * ν) := div_pos (by linarith) (mul_pos hω hν)
  have h1 := Real.rpow_lt_rpow (le_of_lt hK₁) h (div_pos hα0 he)
  have h2 := mul_pos (Real.rpow_pos_of_pos hc (1 / (α + ν - 1)))
    (Real.rpow_pos_of_pos hz (1 / (α + ν - 1)))
  simp only [tpL]
  exact mul_lt_mul_of_pos_left h1 h2

/-- AKMM, p. 577 (the hypothesis `e > 0` is needed): if `α + ν < 1`, labour strictly
decreases in TFP. -/
theorem tp_L_strictAnti_z_of_neg {α ν ω K : ℝ} (hν : 0 < ν) (hω : 0 < ω)
    (hK : 0 < K) (he : α + ν - 1 < 0) : StrictAntiOn (fun z => tpL α ν ω z K) (Ioi 0) := by
  intro z₁ hz₁ z₂ _ h
  have hc : 0 < (1 - α) / (ω * ν) := div_pos (by linarith) (mul_pos hω hν)
  have h1 := Real.rpow_lt_rpow_of_neg hz₁ h (one_div_neg.2 he)
  have h2 := Real.rpow_pos_of_pos hc (1 / (α + ν - 1))
  have h3 := Real.rpow_pos_of_pos hK (α / (α + ν - 1))
  simp only [tpL]
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h1 h2) h3

/-- AKMM, pp. 584–585: in period 0 with working capital, (19.18) `F₃ = (1 + µ)w` with
`F₃ = (1 − α)zK^αL^{−α}` and the household's `w = νL^{ν−1}` give
`(1 − α)zK^αL^{−α} = (1 + µ)νL^{ν−1}`, so `L = ((1 − α)/((1 + µ)ν))^{1/e} z^{1/e} K^{α/e}`
(`µ > −1`). -/
theorem tp_wc_labour {α ν μ z K L w : ℝ} (hα : α < 1) (hν : 0 < ν) (hμ : -1 < μ) (hz : 0 < z)
    (hK : 0 < K) (hL : 0 < L) (he : α + ν - 1 ≠ 0)
    (h1918 : (1 - α) * z * K ^ α * L ^ (-α) = (1 + μ) * w) (h198 : w = ν * L ^ (ν - 1)) :
    L = tpL α ν (1 + μ) z K := by
  refine (tp_foc_iff hα hν (by linarith) hz hK hL he).1 ?_
  rw [← tp_mpl_eq hK.le hL.le, h1918, h198]
  ring

/-- **Property 19.5.6** (AKMM, pp. 584–585): with working capital, period-0 labour
`L = ((1 − α)/((1 + µ)ν))^{1/e} z^{1/e} K^{α/e}` is strictly decreasing in the multiplier `µ`
(`µ > −1`, `e > 0`). -/
theorem property_19_5_6 {α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (he : 0 < α + ν - 1) : StrictAntiOn (fun μ => tpL α ν (1 + μ) z K) (Ioi (-1)) := by
  intro μ₁ hμ₁ μ₂ hμ₂ h
  have h1 : 0 < 1 + μ₁ := by simp only [mem_Ioi] at hμ₁; linarith
  have h2 : 0 < 1 + μ₂ := by simp only [mem_Ioi] at hμ₂; linarith
  have hb : (1 - α) / ((1 + μ₂) * ν) < (1 - α) / ((1 + μ₁) * ν) :=
    div_lt_div_of_pos_left (by linarith) (mul_pos h1 hν) (by nlinarith)
  have hc2 : 0 < (1 - α) / ((1 + μ₂) * ν) := div_pos (by linarith) (mul_pos h2 hν)
  have hr := Real.rpow_lt_rpow hc2.le hb (one_div_pos.2 he)
  have hz' := Real.rpow_pos_of_pos hz (1 / (α + ν - 1))
  have hK' := Real.rpow_pos_of_pos hK (α / (α + ν - 1))
  simp only [tpL]
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hr hz') hK'

/-! ### Output, the marginal product of capital and `g` -/

/-- **Output** (AKMM, p. 577): `zK^αL^{1−α}` at the equilibrium labour is
`((1 − α)/ν)^{(1−α)/e} z^{ν/e} K^{να/e}`. -/
theorem tp_Y_eq {α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (he : α + ν - 1 ≠ 0) : z * K ^ α * tpL α ν 1 z K ^ (1 - α) = tpY α ν z K := by
  have hc : 0 < (1 - α) / ν := div_pos (by linarith) hν
  unfold tpL tpY
  rw [one_mul, Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hz.le _))
    (Real.rpow_nonneg hK.le _), Real.mul_rpow (Real.rpow_nonneg hc.le _)
    (Real.rpow_nonneg hz.le _), ← Real.rpow_mul hc.le, ← Real.rpow_mul hz.le,
    ← Real.rpow_mul hK.le]
  have e1 : ν / (α + ν - 1) = 1 + 1 / (α + ν - 1) * (1 - α) := by field_simp; ring
  have e2 : ν * α / (α + ν - 1) = α + α / (α + ν - 1) * (1 - α) := by field_simp; ring
  have e3 : (1 - α) / (α + ν - 1) = 1 / (α + ν - 1) * (1 - α) := by ring
  rw [e1, e2, e3, Real.rpow_add hz, Real.rpow_add hK, Real.rpow_one]
  ring

/-- AKMM, p. 578: `F_k = αY/K` at the equilibrium labour, the printed closed form. -/
theorem tp_Fk_eq {α ν z K : ℝ} (hK : 0 < K) : α * tpY α ν z K / K = tpFk α ν z K := by
  unfold tpY tpFk
  rw [Real.rpow_sub_one hK.ne']
  ring

/-- AKMM, p. 578: the marginal product of capital at the equilibrium labour,
`∂/∂K [zK^αL^{1−α}]` at `L = L(z, K)`, is `tpFk`. -/
theorem tp_mpk_eq {α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (he : α + ν - 1 ≠ 0) :
    HasDerivAt (fun k => z * k ^ α * tpL α ν 1 z K ^ (1 - α)) (tpFk α ν z K) K := by
  refine (tp_mpk hK).congr_deriv ?_
  rw [tp_Y_eq hα hν hz hK he, tp_Fk_eq hK]

/-- AKMM, p. 577: output increases in `z` (`e > 0`). -/
theorem tp_Y_strictMono_z {α ν K : ℝ} (hα : α < 1) (hν : 0 < ν) (hK : 0 < K)
    (he : 0 < α + ν - 1) : StrictMonoOn (fun z => tpY α ν z K) (Ioi 0) := by
  intro z₁ hz₁ z₂ _ h
  have hc : 0 < (1 - α) / ν := div_pos (by linarith) hν
  have h1 := Real.rpow_lt_rpow (le_of_lt hz₁) h (div_pos hν he)
  have h2 := Real.rpow_pos_of_pos hc ((1 - α) / (α + ν - 1))
  have h3 := Real.rpow_pos_of_pos hK (ν * α / (α + ν - 1))
  simp only [tpY]
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h1 h2) h3

/-- AKMM, p. 577: output increases in `K` (`α > 0`, `e > 0`). -/
theorem tp_Y_strictMono_K {α ν z : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν) (hz : 0 < z)
    (he : 0 < α + ν - 1) : StrictMonoOn (fun K => tpY α ν z K) (Ioi 0) := by
  intro K₁ hK₁ K₂ _ h
  have hc : 0 < (1 - α) / ν := div_pos (by linarith) hν
  have h1 := Real.rpow_lt_rpow (le_of_lt hK₁) h (div_pos (mul_pos hν hα0) he)
  have h2 := mul_pos (Real.rpow_pos_of_pos hc ((1 - α) / (α + ν - 1)))
    (Real.rpow_pos_of_pos hz (ν / (α + ν - 1)))
  simp only [tpY]
  exact mul_lt_mul_of_pos_left h1 h2

/-- Output is positive. -/
theorem tp_Y_pos {α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K) :
    0 < tpY α ν z K := by
  have hc : 0 < (1 - α) / ν := div_pos (by linarith) hν
  unfold tpY
  have := Real.rpow_pos_of_pos hc ((1 - α) / (α + ν - 1))
  have := Real.rpow_pos_of_pos hz (ν / (α + ν - 1))
  have := Real.rpow_pos_of_pos hK (ν * α / (α + ν - 1))
  positivity

/-- AKMM, p. 579: "an increase in `z′` raises the marginal productivity of capital"
(`α > 0`, `e > 0`). -/
theorem tp_Fk_strictMono_z {α ν K : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν) (hK : 0 < K)
    (he : 0 < α + ν - 1) : StrictMonoOn (fun z => tpFk α ν z K) (Ioi 0) := by
  intro z₁ hz₁ z₂ hz₂ h
  simp only
  rw [← tp_Fk_eq hK, ← tp_Fk_eq hK]
  have := tp_Y_strictMono_z hα hν hK he hz₁ hz₂ h
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left this hα0) hK

/-- AKMM, pp. 579, 582: the marginal product of capital is strictly decreasing in `K`
(`0 < α < 1`, `ν > 1`). -/
theorem tp_Fk_strictAnti_K {α ν z : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 1 < ν) (hz : 0 < z) :
    StrictAntiOn (fun K => tpFk α ν z K) (Ioi 0) := by
  intro K₁ hK₁ K₂ _ h
  have he : 0 < α + ν - 1 := by linarith
  have hc : 0 < (1 - α) / ν := div_pos (by linarith) (by linarith)
  have hexp : ν * α / (α + ν - 1) - 1 < 0 := by
    rw [sub_neg, div_lt_one he]
    nlinarith
  have h1 := Real.rpow_lt_rpow_of_neg hK₁ h hexp
  have h2 : 0 < α * ((1 - α) / ν) ^ ((1 - α) / (α + ν - 1)) * z ^ (ν / (α + ν - 1)) :=
    mul_pos (mul_pos hα0 (Real.rpow_pos_of_pos hc _)) (Real.rpow_pos_of_pos hz _)
  simp only [tpFk]
  exact mul_lt_mul_of_pos_left h1 h2

/-- The marginal product of capital is positive. -/
theorem tp_Fk_pos {α ν z K : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν) (hz : 0 < z)
    (hK : 0 < K) : 0 < tpFk α ν z K := by
  rw [← tp_Fk_eq hK]
  have := tp_Y_pos hα hν hz hK
  positivity

/-- AKMM, p. 577: at the equilibrium labour, `L^ν = (1 − α)Y/ν`. -/
theorem tp_L_pow_nu {α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (he : α + ν - 1 ≠ 0) : tpL α ν 1 z K ^ ν = (1 - α) / ν * tpY α ν z K := by
  have hc : 0 < (1 - α) / (1 * ν) := div_pos (by linarith) (by linarith)
  have hKa : 0 < K ^ α := Real.rpow_pos_of_pos hK α
  have hA : 0 < (1 - α) / (1 * ν) * z * K ^ α := by positivity
  have hL : tpL α ν 1 z K = ((1 - α) / (1 * ν) * z * K ^ α) ^ (1 / (α + ν - 1)) :=
    tp_L_eq hc.le hz.le hK.le
  have hLpos : 0 < tpL α ν 1 z K := by rw [hL]; exact Real.rpow_pos_of_pos hA _
  have hLe : tpL α ν 1 z K ^ (α + ν - 1) = (1 - α) / (1 * ν) * z * K ^ α := by
    rw [hL, one_div, Real.rpow_inv_rpow hA.le he]
  have hsplit : tpL α ν 1 z K ^ ν = tpL α ν 1 z K ^ (α + ν - 1) * tpL α ν 1 z K ^ (1 - α) := by
    rw [← Real.rpow_add hLpos]
    ring_nf
  rw [← tp_Y_eq hα hν hz hK he, hsplit, hLe, one_mul]
  ring

/-- AKMM, p. 577: `g(z, K) = C − L^ν = (1 − δ)K + ((α + ν − 1)/ν)Y`. -/
theorem tp_g_eq {δ α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (he : α + ν - 1 ≠ 0) :
    tpG δ α ν z K = (1 - δ) * K + (α + ν - 1) / ν * tpY α ν z K := by
  unfold tpG
  rw [tp_L_pow_nu hα hν hz hK he]
  field_simp
  ring

/-- AKMM, p. 577: "`g(z′, K′)` is increasing in `z′`" (`e > 0`). -/
theorem tp_g_strictMono_z {δ α ν K : ℝ} (hα : α < 1) (hν : 0 < ν) (hK : 0 < K)
    (he : 0 < α + ν - 1) : StrictMonoOn (fun z => tpG δ α ν z K) (Ioi 0) := by
  intro z₁ hz₁ z₂ hz₂ h
  simp only
  rw [tp_g_eq hα hν hz₁ hK he.ne', tp_g_eq hα hν hz₂ hK he.ne']
  have := tp_Y_strictMono_z hα hν hK he hz₁ hz₂ h
  have hcoef : 0 < (α + ν - 1) / ν := div_pos he hν
  nlinarith

/-- AKMM, p. 577: "`g(z′, K′)` is increasing in `K′`" (`α > 0`, `e > 0`, `δ ≤ 1`), on the
whole positive half-line. -/
theorem tp_g_strictMono_K {δ α ν z : ℝ} (hδ : δ ≤ 1) (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν)
    (hz : 0 < z) (he : 0 < α + ν - 1) : StrictMonoOn (fun K => tpG δ α ν z K) (Ioi 0) := by
  intro K₁ hK₁ K₂ hK₂ h
  simp only
  rw [tp_g_eq hα hν hz hK₁ he.ne', tp_g_eq hα hν hz hK₂ he.ne']
  have := tp_Y_strictMono_K hα0 hα hν hz he hK₁ hK₂ h
  have hcoef : 0 < (α + ν - 1) / ν := div_pos he hν
  nlinarith

/-- `g` is positive (`e > 0`, `δ ≤ 1`). -/
theorem tp_g_pos {δ α ν z K : ℝ} (hδ : δ ≤ 1) (hα : α < 1) (hν : 0 < ν) (hz : 0 < z)
    (hK : 0 < K) (he : 0 < α + ν - 1) : 0 < tpG δ α ν z K := by
  rw [tp_g_eq hα hν hz hK he.ne']
  have := tp_Y_pos hα hν hz hK
  have : 0 ≤ (1 - δ) * K := mul_nonneg (by linarith) hK.le
  have : 0 < (α + ν - 1) / ν * tpY α ν z K := by positivity
  linarith

end AKMM.CreditFrictions
