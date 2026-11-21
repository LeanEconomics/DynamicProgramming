/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Primitives of the basic Ramsey model

Miao, §14.1.1, pp. 456–459: the assumptions on the production function `F` and the utility
function `u`, the zero-profit property of a constant-returns firm, and the King–Plosser–Rebelo
(KPR) utility functions (14.5)–(14.6) that are consistent with balanced growth.

* **Zero profits** (p. 459). Euler's theorem for a function homogeneous of degree one and
  Fréchet differentiable at `(K, L)`: `F(K, L) = F_K K + F_L L` (`rm_euler_homogeneous`).
  Hence, with the firm's first-order conditions (14.3), profits `F − R^k K − wN` are zero
  (`rm_zero_profit`). The partial derivatives are homogeneous of degree zero
  (`rm_partial1_homog_zero`, `rm_partial2_homog_zero`), so `F_K(K, AN)` depends only on
  `K/(AN)` (used for detrending).
* **KPR utility** (14.5): `u(c, n) = c^{1−σ}v(n)/(1 − σ)` has `u_c = c^{−σ}v(n)`,
  `u_n = c^{1−σ}v'(n)/(1 − σ)` (`rm_kpr_hasDerivAt_c`, `rm_kpr_hasDerivAt_n`);
  `u_c(λc, n) = λ^{−σ}u_c(c, n)` and `u_n(λc, n) = λ^{1−σ}u_n(c, n)`
  (`rm_kpr_uc_scale`, `rm_kpr_un_scale`), so the marginal rate of substitution `−u_n/u_c` is
  homogeneous of degree one in `c` (`rm_kpr_mrs_scale`). For (14.6), `u = ln c + v(n)`, the same
  holds with `σ = 1` (`rm_log_hasDerivAt_c`, `rm_log_uc_scale`, `rm_log_mrs_scale`).

**Corrections.** The printed limit conditions `lim_{c→0} u(c, ·) = ∞` and
`lim_{K→∞} F(K, 1) = 0` cannot hold: a function increasing in `c` is bounded above near
`c = 0` (`rm_inada_u_misprint`), and `F(·, 1)` strictly increasing with `F(0, 1) = 0` is
bounded below by `F(1, 1) > 0` for `K ≥ 1` (`rm_inada_F_misprint`). The intended conditions are
`lim_{c→0} u_c = ∞` and `lim_{K→∞} F_1(K, 1) = 0`; they hold for log utility
(`rm_log_inada`) and for Cobb–Douglas (`rm_cd_inada_zero`, `rm_cd_inada_top`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-! ### Constant returns to scale -/

/-- Miao, p. 459 (Euler's theorem behind "the firm makes zero profit"): if `F` is homogeneous of
degree one along the ray through `(K, L)` and Fréchet differentiable at `(K, L)` with partial
derivatives `F_K, F_L`, then `F(K, L) = F_K K + F_L L`. -/
theorem rm_euler_homogeneous {F : ℝ → ℝ → ℝ} {FK FL K L : ℝ}
    (hhom : ∀ s, 0 < s → F (s * K) (s * L) = s * F K L)
    (hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (FK • ContinuousLinearMap.fst ℝ ℝ ℝ + FL • ContinuousLinearMap.snd ℝ ℝ ℝ) (K, L)) :
    F K L = FK * K + FL * L := by
  have hγ : HasDerivAt (fun s : ℝ => (s * K, s * L)) (K, L) 1 :=
    (hasDerivAt_mul_const K).prodMk (hasDerivAt_mul_const L)
  have h1 : HasDerivAt (fun s : ℝ => F (s * K) (s * L)) (FK * K + FL * L) 1 := by
    have := hF.comp_hasDerivAt_of_eq (x := (1 : ℝ)) hγ (by simp)
    convert this using 1
    · rfl
    · simp
  have h2 : HasDerivAt (fun s : ℝ => F (s * K) (s * L)) (F K L) 1 := by
    have h3 : HasDerivAt (fun s : ℝ => s * F K L) (F K L) 1 := hasDerivAt_mul_const _
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with s hs
    exact hhom s hs
  exact h2.unique h1

/-- Miao, p. 459: with the first-order conditions (14.3) `R^k = F_K`, `w = F_N` (here `A = 1` is
absorbed into effective labour `L = AN`), a constant-returns firm makes zero profit. -/
theorem rm_zero_profit {F : ℝ → ℝ → ℝ} {FK FL K L Rk w : ℝ}
    (hhom : ∀ s, 0 < s → F (s * K) (s * L) = s * F K L)
    (hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (FK • ContinuousLinearMap.fst ℝ ℝ ℝ + FL • ContinuousLinearMap.snd ℝ ℝ ℝ) (K, L))
    (hR : Rk = FK) (hw : w = FL) : F K L - Rk * K - w * L = 0 := by
  rw [rm_euler_homogeneous hhom hF, hR, hw]; ring

/-- Miao, p. 459 (used for detrending): if `F` is homogeneous of degree one on the positive
quadrant and has partial derivative `F₁` in its first argument there, then `F₁` is homogeneous of
degree zero: `F₁(sK, sL) = F₁(K, L)`. -/
theorem rm_partial1_homog_zero {F F1 : ℝ → ℝ → ℝ}
    (hhom : ∀ s x y, 0 < s → 0 < x → 0 < y → F (s * x) (s * y) = s * F x y)
    (hF1 : ∀ x y, 0 < x → 0 < y → HasDerivAt (fun z => F z y) (F1 x y) x)
    {s K L : ℝ} (hs : 0 < s) (hK : 0 < K) (hL : 0 < L) : F1 (s * K) (s * L) = F1 K L := by
  have hA : HasDerivAt (fun z => F (s * z) (s * L)) (F1 (s * K) (s * L) * s) K := by
    have hl : HasDerivAt (fun z => s * z) s K := by simpa using (hasDerivAt_id K).const_mul s
    exact (hF1 (s * K) (s * L) (mul_pos hs hK) (mul_pos hs hL)).comp K hl
  have hB : HasDerivAt (fun z => F (s * z) (s * L)) (s * F1 K L) K := by
    refine ((hF1 K L hK hL).const_mul s).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hK] with z hz
    exact hhom s z L hs hz hL
  have := hA.unique hB
  have hs' : s ≠ 0 := hs.ne'
  have : (F1 (s * K) (s * L) - F1 K L) * s = 0 := by linarith
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hs')

/-- Miao, p. 459: the partial derivative in the second argument is homogeneous of degree zero
too. -/
theorem rm_partial2_homog_zero {F F2 : ℝ → ℝ → ℝ}
    (hhom : ∀ s x y, 0 < s → 0 < x → 0 < y → F (s * x) (s * y) = s * F x y)
    (hF2 : ∀ x y, 0 < x → 0 < y → HasDerivAt (fun z => F x z) (F2 x y) y)
    {s K L : ℝ} (hs : 0 < s) (hK : 0 < K) (hL : 0 < L) : F2 (s * K) (s * L) = F2 K L := by
  have hA : HasDerivAt (fun z => F (s * K) (s * z)) (F2 (s * K) (s * L) * s) L := by
    have hl : HasDerivAt (fun z => s * z) s L := by simpa using (hasDerivAt_id L).const_mul s
    exact (hF2 (s * K) (s * L) (mul_pos hs hK) (mul_pos hs hL)).comp L hl
  have hB : HasDerivAt (fun z => F (s * K) (s * z)) (s * F2 K L) L := by
    refine ((hF2 K L hK hL).const_mul s).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hL] with z hz
    exact hhom s K z hs hK hz
  have := hA.unique hB
  have : (F2 (s * K) (s * L) - F2 K L) * s = 0 := by linarith
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hs.ne')

/-! ### KPR utility (14.5)–(14.6) -/

/-- The KPR utility (14.5), `u(c, n) = c^{1−σ}v(n)/(1 − σ)`. -/
noncomputable def rmKprU (σ : ℝ) (v : ℝ → ℝ) (c n : ℝ) : ℝ :=
  c ^ (1 - σ) * v n / (1 - σ)

/-- The marginal utility of consumption for (14.5), `u_c = c^{−σ}v(n)`. -/
noncomputable def rmKprUc (σ : ℝ) (v : ℝ → ℝ) (c n : ℝ) : ℝ :=
  c ^ (-σ) * v n

/-- The marginal (dis)utility of labour for (14.5), `u_n = c^{1−σ}v'(n)/(1 − σ)`. -/
noncomputable def rmKprUn (σ : ℝ) (v' : ℝ → ℝ) (c n : ℝ) : ℝ :=
  c ^ (1 - σ) * v' n / (1 - σ)

/-- Miao, (14.5), p. 459: `∂u/∂c = c^{−σ}v(n)` for `c > 0`, `σ ≠ 1`. -/
theorem rm_kpr_hasDerivAt_c {σ : ℝ} (hσ : σ ≠ 1) (v : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (n : ℝ) :
    HasDerivAt (fun x => rmKprU σ v x n) (rmKprUc σ v c n) c := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).mul_const (v n)
    |>.div_const (1 - σ)
  have h1 : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have he : (1 - σ) * c ^ (1 - σ - 1) * v n / (1 - σ) = rmKprUc σ v c n := by
    simp only [rmKprUc, show 1 - σ - 1 = -σ by ring]
    field_simp
  exact he ▸ h

/-- Miao, (14.5), p. 459: `∂u/∂n = c^{1−σ}v'(n)/(1 − σ)` when `v'` is the derivative of `v`. -/
theorem rm_kpr_hasDerivAt_n (σ : ℝ) {v v' : ℝ → ℝ} (c : ℝ) {n : ℝ}
    (hv : HasDerivAt v (v' n) n) :
    HasDerivAt (fun x => rmKprU σ v c x) (rmKprUn σ v' c n) n := by
  have h := (hv.const_mul (c ^ (1 - σ))).div_const (1 - σ)
  exact h

/-- Miao, p. 459: `u_c(λc, n) = λ^{−σ}u_c(c, n)` for (14.5). -/
theorem rm_kpr_uc_scale (σ : ℝ) (v : ℝ → ℝ) {l c : ℝ} (hl : 0 < l) (hc : 0 < c) (n : ℝ) :
    rmKprUc σ v (l * c) n = l ^ (-σ) * rmKprUc σ v c n := by
  simp only [rmKprUc, Real.mul_rpow hl.le hc.le]; ring

/-- Miao, p. 459: `u_n(λc, n) = λ^{1−σ}u_n(c, n)` for (14.5). -/
theorem rm_kpr_un_scale (σ : ℝ) (v' : ℝ → ℝ) {l c : ℝ} (hl : 0 < l) (hc : 0 < c) (n : ℝ) :
    rmKprUn σ v' (l * c) n = l ^ (1 - σ) * rmKprUn σ v' c n := by
  simp only [rmKprUn, Real.mul_rpow hl.le hc.le]; ring

/-- Miao, p. 459: for (14.5) the marginal rate of substitution `−u_n/u_c` is homogeneous of
degree one in consumption, which is why the wage grows at the rate of technology. -/
theorem rm_kpr_mrs_scale (σ : ℝ) {v v' : ℝ → ℝ} {l c : ℝ} (hl : 0 < l) (hc : 0 < c) (n : ℝ)
    (hv : v n ≠ 0) :
    -rmKprUn σ v' (l * c) n / rmKprUc σ v (l * c) n =
      l * (-rmKprUn σ v' c n / rmKprUc σ v c n) := by
  rw [rm_kpr_un_scale σ v' hl hc, rm_kpr_uc_scale σ v hl hc]
  have h1 : l ^ (1 - σ) = l * l ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hl, Real.rpow_one]
  have h2 : 0 < l ^ (-σ) := Real.rpow_pos_of_pos hl _
  have h3 : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  rw [h1]
  simp only [rmKprUc] at *
  field_simp

/-- Miao, (14.6), p. 459: for `u = ln c + v(n)`, `∂u/∂c = 1/c`. -/
theorem rm_log_hasDerivAt_c (v : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (n : ℝ) :
    HasDerivAt (fun x => Real.log x + v n) (1 / c) c := by
  simpa [one_div] using (Real.hasDerivAt_log hc.ne').add_const (v n)

/-- Miao, (14.6), p. 459: `u_c(λc) = λ^{−1}u_c(c)` for log utility. -/
theorem rm_log_uc_scale {l c : ℝ} (hl : 0 < l) (hc : 0 < c) :
    1 / (l * c) = l⁻¹ * (1 / c) := by
  field_simp

/-- Miao, (14.6), p. 459: for log utility `−u_n/u_c = −c v'(n)` is homogeneous of degree one in
`c`. -/
theorem rm_log_mrs_scale (vn l c : ℝ) (hl : 0 < l) (hc : 0 < c) :
    -vn / (1 / (l * c)) = l * (-vn / (1 / c)) := by
  field_simp

/-! ### The limit conditions on p. 456–457 -/

/-- Correction to Miao, p. 456: `lim_{c→0} u(c, n) = ∞` is impossible when `u(·, n)` is
increasing on `(0, ∞)` (as `u_c > 0` requires). -/
theorem rm_inada_u_misprint {u : ℝ → ℝ} (hu : MonotoneOn u (Set.Ioi 0)) :
    ¬ Tendsto u (𝓝[>] 0) atTop := by
  intro h
  have h1 : ∀ᶠ c in 𝓝[>] (0 : ℝ), u 1 + 1 ≤ u c := h.eventually (eventually_ge_atTop _)
  have h2 : ∀ᶠ c in 𝓝[>] (0 : ℝ), c ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  obtain ⟨c, hc1, hc2⟩ := (h1.and h2).exists
  have := hu hc2.1 (Set.mem_Ioi.2 zero_lt_one) hc2.2.le
  linarith

/-- Correction to Miao, p. 457: `lim_{K→∞} F(K, 1) = 0` is impossible when `F(·, 1)` is strictly
increasing on `[0, ∞)` (as `F₁ > 0` requires) and `F(0, 1) = 0`. -/
theorem rm_inada_F_misprint {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.Ici 0)) (h0 : f 0 = 0) :
    ¬ Tendsto f atTop (𝓝 0) := by
  intro h
  have h1 : 0 < f 1 := by
    have := hf (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_lt_one
    linarith
  have h2 : ∀ᶠ K in atTop, f 1 ≤ f K := by
    filter_upwards [eventually_ge_atTop 1] with K hK
    exact hf.monotoneOn (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 (by linarith)) hK
  have := ge_of_tendsto h h2
  linarith

/-- Miao, p. 456 (the intended condition): for log utility `u_c = 1/c → ∞` as `c → 0⁺`. -/
theorem rm_log_inada : Tendsto (fun c : ℝ => 1 / c) (𝓝[>] 0) atTop := by
  simpa [one_div] using tendsto_inv_nhdsGT_zero

/-- Miao, p. 457 (the intended condition): for Cobb–Douglas `F(K, 1) = K^α`, `0 < α < 1`, the
marginal product `F₁(K, 1) = αK^{α−1} → ∞` as `K → 0⁺`. -/
theorem rm_cd_inada_zero {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun K : ℝ => α * K ^ (α - 1)) (𝓝[>] 0) atTop := by
  exact (tendsto_rpow_neg_nhdsGT_zero (show α - 1 < 0 by linarith)).const_mul_atTop hα0

/-- Miao, p. 457 (the intended condition): `F₁(K, 1) = αK^{α−1} → 0` as `K → ∞`. -/
theorem rm_cd_inada_top {α : ℝ} (hα1 : α < 1) :
    Tendsto (fun K : ℝ => α * K ^ (α - 1)) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (show 0 < 1 - α by linarith)
  have h' : Tendsto (fun K : ℝ => K ^ (α - 1)) atTop (𝓝 0) := by
    simpa [show -(1 - α) = α - 1 by ring] using h
  simpa using h'.const_mul α

end Miao.NeoclassicalGrowth
