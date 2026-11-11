/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RMDecentral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# The steady state of the basic Ramsey model

Miao, §14.1.1, pp. 459 and 465: the steady state of the detrended system (balanced growth).

* A constant detrended path solves the detrended planner's system iff
  `F_K(k̃, n) = g_a^σ/β − 1 + δ` (the **modified golden rule**), `−u_n/u_c = F_N(k̃, n)`,
  `ı̃ = (gₙg_a − 1 + δ)k̃` and `c̃ = F(k̃, n) − ı̃` (`rm_steady_state_iff`).
* With `f(x) = F_K(x, 1)` continuous and strictly decreasing on `(0, ∞)`, `f(0⁺) = ∞`,
  `f(∞) = 0`, the capital–labour ratio solving `f(x) = r` exists and is unique for every `r > 0`
  (`rm_steady_ratio_exists_unique`); the target `r = g_a^σ/β − 1 + δ` is positive when
  `g_a ≥ 1` (`rm_mgr_pos`). By homogeneity `F_K(k̃, n) = F_K(k̃/n, 1)` (`rm_FK_ratio`).
* **Comparative statics**: the ratio is decreasing in `r` (`rm_steady_ratio_anti`), so it rises
  with `β` (`rm_cs_beta`) and falls with `δ` (`rm_cs_delta`), with `g_a` when `σ > 0`
  (`rm_cs_ga`), and with `σ` when `g_a > 1` (`rm_cs_sigma`).
* **Balanced growth** (p. 459): at a steady state of the detrended system `C, I, K, Y` grow at
  the gross rate `gₙg_a`, the wage at `g_a`, and the rental rate is constant
  (`rm_balanced_growth`).
* **A worked example**: log utility `ln c + θ ln(1 − n)` and Cobb–Douglas
  `F = k^αn^{1−α}`. The partial derivatives (`rm_cd_FK_hasDerivAt`, `rm_cd_FN_hasDerivAt`),
  homogeneity (`rm_cd_homog`), the hypotheses of the existence theorem (`rm_cd_FK_strictAnti`),
  and the closed-form steady state `x* = (α/r)^{1/(1−α)}`,
  `n* = (1 − α)x*^α/((1 − α)x*^α + θχ)`, `χ = x*^α − (gₙg_a − 1 + δ)x*`, which solves the
  detrended system when `βgₙ < 1` (`rm_cd_log_steady`, `rm_cd_chi_pos`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-- **The steady state** (Miao, pp. 459, 465): a constant path `(c̃, ı̃, n, k̃)` solves the
detrended system iff the modified golden rule `F_K(k̃, n) = g_a^σ/β − 1 + δ`, the labour condition
`−u_n/u_c = F_N(k̃, n)`, `ı̃ = (gₙg_a − 1 + δ)k̃` and `c̃ = F(k̃, n) − ı̃` hold. -/
theorem rm_steady_state_iff {uc un F FK FN : ℝ → ℝ → ℝ} {β ga gn δ σ cs is ns ks : ℝ}
    (hβ : 0 < β) (huc : uc cs ns ≠ 0) :
    RMDetrendedFOC uc un F FK FN β ga gn δ σ (fun _ => cs) (fun _ => is) (fun _ => ns)
        (fun _ => ks) ↔
      FK ks ns = ga ^ σ / β - 1 + δ ∧ -un cs ns / uc cs ns = FN ks ns ∧
        is = (gn * ga - 1 + δ) * ks ∧ cs = F ks ns - is := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h 0
    refine ⟨?_, h2, by linarith, by linarith⟩
    have : β * uc cs ns * (FK ks ns - (ga ^ σ / β - 1 + δ)) = 0 := by
      field_simp
      linear_combination -h1
    have := (mul_eq_zero.1 this).resolve_left (mul_ne_zero hβ.ne' huc)
    linarith
  · rintro ⟨h1, h2, h3, h4⟩ t
    refine ⟨?_, h2, by linarith, by rw [h3]; ring⟩
    rw [h1]
    field_simp
    ring

/-- Miao, p. 465: by homogeneity of degree zero, `F_K(k̃, n) = F_K(k̃/n, 1)`. -/
theorem rm_FK_ratio {FK : ℝ → ℝ → ℝ}
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y) {k n : ℝ}
    (hk : 0 < k) (hn : 0 < n) : FK k n = FK (k / n) 1 := by
  have := hFK n (k / n) 1 hn (div_pos hk hn) one_pos
  rw [mul_div_cancel₀ k hn.ne', mul_one] at this
  exact this

/-- The modified-golden-rule target `g_a^σ/β − 1 + δ` is positive for `g_a ≥ 1`, `σ ≥ 0`,
`0 < β < 1`, `δ ≥ 0`. -/
theorem rm_mgr_pos {β ga δ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hga : 1 ≤ ga) (hσ : 0 ≤ σ)
    (hδ : 0 ≤ δ) : 0 < ga ^ σ / β - 1 + δ := by
  have h1 : 1 ≤ ga ^ σ := Real.one_le_rpow hga hσ
  have h2 : 1 < ga ^ σ / β := by rw [lt_div_iff₀ hβ0]; linarith
  linarith

/-- **Existence and uniqueness of the steady-state capital–labour ratio** (Miao, p. 465, using
the conditions of p. 457): if `f = F_K(·, 1)` is continuous and strictly decreasing on
`(0, ∞)` with `f(0⁺) = ∞` and `f(∞) = 0`, then `f(x) = r` has exactly one solution `x > 0` for
each `r > 0`. -/
theorem rm_steady_ratio_exists_unique {f : ℝ → ℝ} (hc : ContinuousOn f (Set.Ioi 0))
    (hanti : StrictAntiOn f (Set.Ioi 0)) (h0 : Tendsto f (𝓝[>] 0) atTop)
    (htop : Tendsto f atTop (𝓝 0)) {r : ℝ} (hr : 0 < r) : ∃! x, 0 < x ∧ f x = r := by
  obtain ⟨a, ha0, har⟩ : ∃ a, 0 < a ∧ r < f a := by
    have e1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), r + 1 ≤ f x := h0.eventually (eventually_ge_atTop _)
    have e2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
    obtain ⟨a, h1, h2⟩ := (e1.and e2).exists
    exact ⟨a, h2, by linarith⟩
  obtain ⟨b, hab, hbr⟩ : ∃ b, a ≤ b ∧ f b < r := by
    have e1 : ∀ᶠ x in atTop, f x < r := htop.eventually (gt_mem_nhds hr)
    obtain ⟨b, hb⟩ := (e1.and (eventually_ge_atTop a)).exists
    exact ⟨b, hb.2, hb.1⟩
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha0 hx.1
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab (hc.mono hsub) ⟨hbr.le, har.le⟩
  refine ⟨x, ⟨hsub hx, hfx⟩, fun y ⟨hy, hfy⟩ => ?_⟩
  exact hanti.injOn hy (hsub hx) (hfy.trans hfx.symm)

/-- **Comparative statics** (Miao, §14.1.1): the steady-state ratio is decreasing in the target
`r`: if `f(x₁) = r₁ < r₂ = f(x₂)` then `x₂ < x₁`. -/
theorem rm_steady_ratio_anti {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0)) {x1 x2 r1 r2 : ℝ}
    (hx1 : 0 < x1) (hx2 : 0 < x2) (h1 : f x1 = r1) (h2 : f x2 = r2) (hr : r1 < r2) : x2 < x1 := by
  by_contra hc
  rcases (not_lt.1 hc).eq_or_lt with h | h
  · subst h; linarith
  · have := hanti hx1 hx2 h; linarith

/-- Comparative statics: a more patient economy (`β₁ < β₂`) has a higher capital–labour ratio. -/
theorem rm_cs_beta {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0)) {x1 x2 β1 β2 ga δ σ : ℝ}
    (hβ1 : 0 < β1) (hβ : β1 < β2) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (h1 : f x1 = ga ^ σ / β1 - 1 + δ) (h2 : f x2 = ga ^ σ / β2 - 1 + δ) (hga : 0 < ga) :
    x1 < x2 := by
  refine rm_steady_ratio_anti hanti hx2 hx1 h2 h1 ?_
  have : ga ^ σ / β2 < ga ^ σ / β1 :=
    div_lt_div_of_pos_left (Real.rpow_pos_of_pos hga σ) hβ1 hβ
  linarith

/-- Comparative statics: faster depreciation lowers the capital–labour ratio. -/
theorem rm_cs_delta {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0)) {x1 x2 β ga δ1 δ2 σ : ℝ}
    (hδ : δ1 < δ2) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (h1 : f x1 = ga ^ σ / β - 1 + δ1) (h2 : f x2 = ga ^ σ / β - 1 + δ2) : x2 < x1 :=
  rm_steady_ratio_anti hanti hx1 hx2 h1 h2 (by linarith)

/-- Comparative statics: faster technical progress lowers the detrended capital–labour ratio
when `σ > 0`. -/
theorem rm_cs_ga {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0)) {x1 x2 β g1 g2 δ σ : ℝ}
    (hβ : 0 < β) (hσ : 0 < σ) (hg1 : 0 < g1) (hg : g1 < g2) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (h1 : f x1 = g1 ^ σ / β - 1 + δ) (h2 : f x2 = g2 ^ σ / β - 1 + δ) : x2 < x1 := by
  refine rm_steady_ratio_anti hanti hx1 hx2 h1 h2 ?_
  have : g1 ^ σ < g2 ^ σ := Real.rpow_lt_rpow hg1.le hg hσ
  have := div_lt_div_of_pos_right this hβ
  linarith

/-- Comparative statics: with `g_a > 1`, a higher `σ` (lower intertemporal elasticity) lowers the
detrended capital–labour ratio. -/
theorem rm_cs_sigma {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0)) {x1 x2 β ga δ σ1 σ2 : ℝ}
    (hβ : 0 < β) (hga : 1 < ga) (hσ : σ1 < σ2) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (h1 : f x1 = ga ^ σ1 / β - 1 + δ) (h2 : f x2 = ga ^ σ2 / β - 1 + δ) : x2 < x1 := by
  refine rm_steady_ratio_anti hanti hx1 hx2 h1 h2 ?_
  have : ga ^ σ1 < ga ^ σ2 := Real.rpow_lt_rpow_of_exponent_lt hga hσ
  have := div_lt_div_of_pos_right this hβ
  linarith

/-- **Balanced growth** (Miao, p. 459): at a steady state `(c̃, ı̃, k̃, n)` of the detrended
system, the aggregates `X_t = gₙᵗg_aᵗx̃` (`X = C, I, K`) and `Y_t = F(K_t, A_tN_t)` grow at the
gross rate `gₙg_a`, the wage `w_t = A_tF_N(K_t, A_tN_t)` grows at `g_a` and the rental rate
`F_K(K_t, A_tN_t)` is constant. -/
theorem rm_balanced_growth {F FK FN : ℝ → ℝ → ℝ}
    (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    {ga gn x ks ns : ℝ} (hga : 0 < ga) (hgn : 0 < gn) (hk : 0 < ks) (hn : 0 < ns) (t : ℕ) :
    let X := fun s : ℕ => gn ^ s * ga ^ s * x
    let K := fun s : ℕ => gn ^ s * ga ^ s * ks
    let L := fun s : ℕ => ga ^ s * (gn ^ s * ns)
    X (t + 1) = gn * ga * X t ∧ F (K (t + 1)) (L (t + 1)) = gn * ga * F (K t) (L t) ∧
      F (K t) (L t) = gn ^ t * ga ^ t * F ks ns ∧
      ga ^ (t + 1) * FN (K (t + 1)) (L (t + 1)) = ga * (ga ^ t * FN (K t) (L t)) ∧
      FK (K (t + 1)) (L (t + 1)) = FK (K t) (L t) := by
  intro X K L
  have hL : ∀ s, L s = (gn ^ s * ga ^ s) * ns := fun s => by simp only [L]; ring
  have hs : ∀ s : ℕ, (0 : ℝ) < gn ^ s * ga ^ s := fun s => mul_pos (pow_pos hgn s) (pow_pos hga s)
  have hY : ∀ s, F (K s) (L s) = gn ^ s * ga ^ s * F ks ns := fun s => by
    rw [hL]; exact hhom _ _ _ (hs s)
  have hR : ∀ s, FK (K s) (L s) = FK ks ns := fun s => by
    rw [hL]; exact hFK _ _ _ (hs s) hk hn
  have hW : ∀ s, FN (K s) (L s) = FN ks ns := fun s => by
    rw [hL]; exact hFN _ _ _ (hs s) hk hn
  refine ⟨by simp only [X, pow_succ]; ring, by rw [hY, hY, pow_succ, pow_succ]; ring, hY t,
    by rw [hW, hW, pow_succ]; ring, by rw [hR, hR]⟩

/-! ### Worked example: log utility and Cobb–Douglas -/

/-- Cobb–Douglas `F(k, n) = k^αn^{1−α}`. -/
noncomputable def rmCD (α k n : ℝ) : ℝ := k ^ α * n ^ (1 - α)

/-- `F_K = αk^{α−1}n^{1−α}`. -/
noncomputable def rmCDK (α k n : ℝ) : ℝ := α * k ^ (α - 1) * n ^ (1 - α)

/-- `F_N = (1 − α)k^αn^{−α}`. -/
noncomputable def rmCDN (α k n : ℝ) : ℝ := (1 - α) * k ^ α * n ^ (-α)

/-- The Cobb–Douglas partial derivative in capital. -/
theorem rm_cd_FK_hasDerivAt (α : ℝ) {k : ℝ} (hk : 0 < k) (n : ℝ) :
    HasDerivAt (fun z => rmCD α z n) (rmCDK α k n) k := by
  have := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hk.ne')).mul_const (n ^ (1 - α))
  simpa [rmCD, rmCDK] using this

/-- The Cobb–Douglas partial derivative in labour. -/
theorem rm_cd_FN_hasDerivAt (α k : ℝ) {n : ℝ} (hn : 0 < n) :
    HasDerivAt (fun z => rmCD α k z) (rmCDN α k n) n := by
  have := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hn.ne')).const_mul (k ^ α)
  convert this using 1
  · rfl
  · simp only [rmCDN, show 1 - α - 1 = -α by ring]
    ring

/-- Cobb–Douglas is homogeneous of degree one and its partials of degree zero. -/
theorem rm_cd_homog (α : ℝ) {s x y : ℝ} (hs : 0 < s) (hx : 0 < x) (hy : 0 < y) :
    rmCD α (s * x) (s * y) = s * rmCD α x y ∧ rmCDK α (s * x) (s * y) = rmCDK α x y ∧
      rmCDN α (s * x) (s * y) = rmCDN α x y := by
  simp only [rmCD, rmCDK, rmCDN, Real.mul_rpow hs.le hx.le, Real.mul_rpow hs.le hy.le]
  have e1 : s ^ α * s ^ (1 - α) = s := by
    rw [← Real.rpow_add hs]; simp
  have e2 : s ^ (α - 1) * s ^ (1 - α) = 1 := by
    rw [← Real.rpow_add hs]; simp
  have e3 : s ^ α * s ^ (-α) = 1 := by
    rw [← Real.rpow_add hs]; simp
  refine ⟨?_, ?_, ?_⟩
  · linear_combination x ^ α * y ^ (1 - α) * e1
  · linear_combination α * x ^ (α - 1) * y ^ (1 - α) * e2
  · linear_combination (1 - α) * x ^ α * y ^ (-α) * e3

/-- The marginal product `F_K(x, 1) = αx^{α−1}` is continuous and strictly decreasing on
`(0, ∞)`, so (with `rm_cd_inada_zero`, `rm_cd_inada_top`) the existence theorem applies. -/
theorem rm_cd_FK_strictAnti {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    StrictAntiOn (fun x => rmCDK α x 1) (Set.Ioi 0) ∧
      ContinuousOn (fun x => rmCDK α x 1) (Set.Ioi 0) := by
  refine ⟨fun x hx y _ hxy => ?_, ?_⟩
  · simp only [rmCDK, Real.one_rpow, mul_one]
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hx hxy (by linarith)) hα0
  · intro x hx
    simp only [rmCDK, Real.one_rpow, mul_one]
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hx))).const_mul α).continuousWithinAt

/-- In the worked example the steady-state consumption–labour ratio `χ = x^α − (gₙg_a − 1 + δ)x`
at `x = (α/r)^{1/(1−α)}`, `r = g_a/β − 1 + δ`, is positive when `βgₙ < 1`. -/
theorem rm_cd_chi_pos {α β ga gn δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hga : 0 < ga) (hr : 0 < ga / β - 1 + δ) (hβgn : β * gn < 1) :
    let r := ga / β - 1 + δ
    let x := (α / r) ^ (1 / (1 - α))
    0 < x ^ α - (gn * ga - 1 + δ) * x := by
  intro r x
  have hx : 0 < x := Real.rpow_pos_of_pos (div_pos hα0 hr) _
  have hxa : x ^ (α - 1) = r / α := by
    simp only [x]
    rw [← Real.rpow_mul (div_pos hα0 hr).le, show 1 / (1 - α) * (α - 1) = -1 by
      field_simp [show 1 - α ≠ 0 by linarith]; ring, Real.rpow_neg_one, inv_div]
  have hxα : x ^ α = x * (r / α) := by
    rw [← hxa, ← Real.rpow_one_add' hx.le (by linarith)]; ring_nf
  rw [hxα]
  have h1 : r ≤ r / α := by rw [le_div_iff₀ hα0]; nlinarith
  have h2 : gn * ga - 1 + δ < r := by
    have : gn * ga < ga / β := by
      rw [lt_div_iff₀ hβ]; nlinarith
    simp only [r]; linarith
  nlinarith

/-- **Worked steady state** (Miao, §14.1.1, log utility (14.6) with `v(n) = θ ln(1 − n)`,
Cobb–Douglas): with `r = g_a/β − 1 + δ > 0`, `x = (α/r)^{1/(1−α)}`,
`χ = x^α − (gₙg_a − 1 + δ)x > 0`, `n = (1 − α)x^α/((1 − α)x^α + θχ)`, `k̃ = xn`,
`ı̃ = (gₙg_a − 1 + δ)k̃`, `c̃ = χn`, the constant path
solves the detrended system (`σ = 1`, `u_c = 1/c`, `u_n = −θ/(1 − n)`). -/
theorem rm_cd_log_steady {α β ga gn δ θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hθ : 0 < θ) (hr : 0 < ga / β - 1 + δ)
    (hχ : 0 < ((α / (ga / β - 1 + δ)) ^ (1 / (1 - α))) ^ α -
      (gn * ga - 1 + δ) * (α / (ga / β - 1 + δ)) ^ (1 / (1 - α))) :
    let r := ga / β - 1 + δ
    let x := (α / r) ^ (1 / (1 - α))
    let χ := x ^ α - (gn * ga - 1 + δ) * x
    let ns := (1 - α) * x ^ α / ((1 - α) * x ^ α + θ * χ)
    RMDetrendedFOC (fun c _ => 1 / c) (fun _ n => -θ / (1 - n)) (rmCD α) (rmCDK α) (rmCDN α)
      β ga gn δ 1 (fun _ => χ * ns) (fun _ => (gn * ga - 1 + δ) * (x * ns)) (fun _ => ns)
      (fun _ => x * ns) := by
  intro r x χ ns
  have hx : 0 < x := Real.rpow_pos_of_pos (div_pos hα0 hr) _
  have hxa : x ^ (α - 1) = r / α := by
    simp only [x]
    rw [← Real.rpow_mul (div_pos hα0 hr).le, show 1 / (1 - α) * (α - 1) = -1 by
      field_simp [show 1 - α ≠ 0 by linarith]; ring, Real.rpow_neg_one, inv_div]
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hden : 0 < (1 - α) * x ^ α + θ * χ := by
    have : 0 < 1 - α := by linarith
    positivity
  have hns : 0 < ns := div_pos (mul_pos (by linarith) hxα) hden
  have hns1 : ns < 1 := by
    rw [div_lt_one hden]; nlinarith
  have hc : 0 < χ * ns := mul_pos hχ hns
  -- the Cobb–Douglas functions at `(xn, n)`
  have hK : rmCDK α (x * ns) ns = r := by
    have := (rm_cd_homog α hns hx one_pos).2.1
    rw [show ns * x = x * ns by ring, mul_one] at this
    rw [this]; simp only [rmCDK, Real.one_rpow, mul_one, hxa]; field_simp
  have hN : rmCDN α (x * ns) ns = (1 - α) * x ^ α := by
    have := (rm_cd_homog α hns hx one_pos).2.2
    rw [show ns * x = x * ns by ring, mul_one] at this
    rw [this]; simp [rmCDN]
  have hY : rmCD α (x * ns) ns = x ^ α * ns := by
    have := (rm_cd_homog α hns hx one_pos).1
    rw [show ns * x = x * ns by ring, mul_one] at this
    rw [this]; simp [rmCD]; ring
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Real.rpow_one, hK, r]
    field_simp
    ring
  · simp only [hN]
    have h1 : 1 - ns ≠ 0 := by linarith
    have hnum : θ * χ * ns = (1 - α) * x ^ α * (1 - ns) := by
      simp only [ns]; field_simp; ring
    field_simp
    linear_combination hnum
  · simp only [hY, χ]; ring
  · ring

end Miao.NeoclassicalGrowth
