/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.SustainedGrowthWelfare

/-!
# Sustained growth: the direct proof of Exercise 16.3(e)(ii) with inner-product prices

SLP §16.3, p. 487, the [Derived] direct proof of Exercise 16.3(e)(ii). At a Pareto optimum `x`
(a solution of the planning problem) whose lower bound does not bind (`x_t ≥ a′θᵗ`, `a′ > a`),
the price sequence `p_t = βᵗ U′(x_t) = βᵗ x_t^{−σ}` supports `(x, x)` as a competitive
equilibrium.

* `sgCRRA_hasDerivAt`, `sgCRRA_tangent`: `U′(c) = c^{−σ}` and the tangent inequality
  `U(c′) ≤ U(c) + c^{−σ}(c′ − c)`.
* `sgPriceWeight`: in `ℓ_∞` coordinates the price is `π_t = ρᵗ x̃_t^{−σ}` (`ρ = βθ^{1−σ}`,
  `x_t = θᵗ x̃_t`), summable; `sgPriceDual` is the continuous linear functional
  `w ↦ Σ_t π_t w_t` on `S_θ`, and `sgPriceDual_eq_inner`: it is `y ↦ Σ_t p_t y_t` with
  `p_t = βᵗ x_t^{−σ}` and `Σ_t p_t θᵗ < ∞` (the continuity condition of the [Derived] sketch).
* **Exercise 16.3(e)(ii), direct** (`ex_16_3e_ii_direct`): `(x, x, p)` is a competitive
  equilibrium. Utility maximisation is the tangent inequality summed over `t`; profit
  maximisation is the first-order condition along the segment from `x` towards any `y ∈ Y`
  (dominated convergence), as in the hint to Exercise 16.4(c).

**Comments.** This proof works for every `θ > 0` (no interior point of `Y`, hence no
Assumption 15.5, is needed), and it gives the price in inner-product form, which Theorem 15.6
could not (`SustainedGrowthWelfare`). It still needs the non-binding lower bound, both for the
segment from `x` to stay in `X` and for the summability of `p_t θᵗ`. The Euler equation and the
transversality condition of the [Derived] sketch are not needed.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

/-- `U′(c) = c^{−σ}` for `c > 0`. -/
theorem sgCRRA_hasDerivAt {σ c : ℝ} (hc : 0 < c) : HasDerivAt (sgCRRA σ) (c ^ (-σ)) c := by
  by_cases h1 : σ = 1
  · subst h1
    have : sgCRRA 1 = Real.log := funext sgCRRA_one
    rw [this, Real.rpow_neg hc.le, Real.rpow_one]
    exact Real.hasDerivAt_log hc.ne'
  · have : sgCRRA σ = fun c => (c ^ (1 - σ) - 1) / (1 - σ) := funext (sgCRRA_of_ne h1)
    rw [this]
    have hp : (1 - σ) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have h := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).sub_const 1).div_const
      (1 - σ)
    convert h using 1
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp

/-- The **tangent inequality** `U(c′) ≤ U(c) + c^{−σ}(c′ − c)` for `c, c′ > 0`. -/
theorem sgCRRA_tangent {σ c c' : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hc' : 0 < c') :
    sgCRRA σ c' ≤ sgCRRA σ c + c ^ (-σ) * (c' - c) := by
  have hcv := sgCRRA_concaveOn hσ
  rcases lt_trichotomy c c' with h | h | h
  · have := hcv.slope_le_of_hasDerivAt (show c ∈ Ioi 0 from hc) (show c' ∈ Ioi 0 from hc') h
      (sgCRRA_hasDerivAt hc)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · subst h
    simp
  · have := hcv.le_slope_of_hasDerivAt (show c' ∈ Ioi 0 from hc') (show c ∈ Ioi 0 from hc) h
      (sgCRRA_hasDerivAt hc)
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith

/-- The price identity: `βᵗ (θᵗ m)^{−σ} (θᵗ d) = (βθ^{1−σ})ᵗ m^{−σ} d`. -/
theorem sg_price_identity {β θ σ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) (t : ℕ) (d : ℝ) :
    β ^ t * ((θ ^ t * m) ^ (-σ) * (θ ^ t * d)) = (β * θ ^ (1 - σ)) ^ t * (m ^ (-σ) * d) := by
  have hθt : 0 < θ ^ t := pow_pos hθ t
  have h1 : (θ ^ t) ^ (-σ) * θ ^ t = (θ ^ (1 - σ)) ^ t := by
    rw [Real.rpow_pow_comm hθ.le, show (1 : ℝ) - σ = -σ + 1 by ring, Real.rpow_add hθt,
      Real.rpow_one]
  rw [Real.mul_rpow hθt.le hm.le, mul_pow]
  calc β ^ t * ((θ ^ t) ^ (-σ) * m ^ (-σ) * (θ ^ t * d))
      = β ^ t * ((θ ^ t) ^ (-σ) * θ ^ t) * (m ^ (-σ) * d) := by ring
    _ = _ := by rw [h1]

/-- The price weights in `ℓ_∞` coordinates, `π_t = ρᵗ x̃_t^{−σ}`. -/
noncomputable def sgPriceWeight (β θ σ : ℝ) (x : BddSeq ℝ) (t : ℕ) : ℝ :=
  (β * θ ^ (1 - σ)) ^ t * x t ^ (-σ)

/-- `0 ≤ π_t ≤ a′^{−σ} ρᵗ` when `x̃ ≥ a′ > 0`. -/
theorem sgPriceWeight_bound {β θ σ a' : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hθ : 0 < θ)
    (ha' : 0 < a') {x : BddSeq ℝ} (hx : ∀ t, a' ≤ x t) (t : ℕ) :
    0 ≤ sgPriceWeight β θ σ x t ∧
      sgPriceWeight β θ σ x t ≤ a' ^ (-σ) * (β * θ ^ (1 - σ)) ^ t := by
  have hρ0 : 0 ≤ β * θ ^ (1 - σ) := mul_nonneg hβ0 (Real.rpow_nonneg hθ.le _)
  have hxt : 0 < x t := lt_of_lt_of_le ha' (hx t)
  refine ⟨mul_nonneg (pow_nonneg hρ0 t) (Real.rpow_nonneg hxt.le _), ?_⟩
  rw [sgPriceWeight, mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha' (hx t) (by linarith))
    (pow_nonneg hρ0 t)

/-- The weighted series `Σ_t π_t w_t` converges absolutely. -/
theorem sg_price_summable {β θ σ a' : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hθ : 0 < θ)
    (hρ1 : β * θ ^ (1 - σ) < 1) (ha' : 0 < a') {x : BddSeq ℝ} (hx : ∀ t, a' ≤ x t)
    (w : BddSeq ℝ) : Summable fun t => sgPriceWeight β θ σ x t * w t := by
  have hρ0 : 0 ≤ β * θ ^ (1 - σ) := mul_nonneg hβ0 (Real.rpow_nonneg hθ.le _)
  refine Summable.of_norm_bounded
    (((summable_geometric_of_lt_one hρ0 hρ1).mul_left (a' ^ (-σ))).mul_right ‖w‖) fun t => ?_
  obtain ⟨h0, h1⟩ := sgPriceWeight_bound hσ hβ0 hθ ha' hx t
  rw [norm_mul, Real.norm_of_nonneg h0]
  exact mul_le_mul h1 (norm_seq_coord_le w t) (norm_nonneg _) (h0.trans h1)

/-- The **price functional** `w ↦ Σ_t π_t w_t` on `S_θ` (in `ℓ_∞` coordinates). -/
noncomputable def sgPriceDual {β θ σ a' : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hθ : 0 < θ)
    (hρ1 : β * θ ^ (1 - σ) < 1) (ha' : 0 < a') {x : BddSeq ℝ} (hx : ∀ t, a' ≤ x t) :
    StrongDual ℝ (BddSeq ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun w => ∑' t, sgPriceWeight β θ σ x t * w t
      map_add' := fun w w' => by
        rw [← (sg_price_summable hσ hβ0 hθ hρ1 ha' hx w).tsum_add
          (sg_price_summable hσ hβ0 hθ hρ1 ha' hx w')]
        congr 1
        funext t
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun a w => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← tsum_mul_left]
        congr 1
        funext t
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    (a' ^ (-σ) * (1 - β * θ ^ (1 - σ))⁻¹) fun w => by
      have hρ0 : 0 ≤ β * θ ^ (1 - σ) := mul_nonneg hβ0 (Real.rpow_nonneg hθ.le _)
      have hg := ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (a' ^ (-σ))).mul_right ‖w‖
      have hb : ∀ t, ‖sgPriceWeight β θ σ x t * w t‖ ≤ a' ^ (-σ) * (β * θ ^ (1 - σ)) ^ t * ‖w‖ :=
        fun t => by
          obtain ⟨h0, h1⟩ := sgPriceWeight_bound hσ hβ0 hθ ha' hx t
          rw [norm_mul, Real.norm_of_nonneg h0]
          exact mul_le_mul h1 (norm_seq_coord_le w t) (norm_nonneg _) (h0.trans h1)
      refine (norm_tsum_le_tsum_norm (Summable.of_norm_bounded hg hb).norm).trans ?_
      refine ((Summable.of_norm_bounded hg hb).norm.tsum_le_tsum hb hg).trans (le_of_eq ?_)
      rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]

/-- `sgPriceDual` evaluates to `Σ_t π_t w_t`. -/
theorem sgPriceDual_apply {β θ σ a' : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hθ : 0 < θ)
    (hρ1 : β * θ ^ (1 - σ) < 1) (ha' : 0 < a') {x : BddSeq ℝ} (hx : ∀ t, a' ≤ x t)
    (w : BddSeq ℝ) :
    sgPriceDual hσ hβ0 hθ hρ1 ha' hx w = ∑' t, sgPriceWeight β θ σ x t * w t := rfl

/-- **Inner-product form**: the price functional is `y ↦ Σ_t p_t y_t` on `S_θ` with
`p_t = βᵗ U′(x_t) = βᵗ x_t^{−σ}` (original coordinates `y = sgOfBdd θ w`), and
`Σ_t p_t θᵗ < ∞`. -/
theorem sgPriceDual_eq_inner {β θ σ a' : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hθ : 0 < θ)
    (hρ1 : β * θ ^ (1 - σ) < 1) (ha' : 0 < a') {x : BddSeq ℝ} (hx : ∀ t, a' ≤ x t)
    (w : BddSeq ℝ) :
    sgPriceDual hσ hβ0 hθ hρ1 ha' hx w =
      ∑' t, β ^ t * sgOfBdd θ x t ^ (-σ) * sgOfBdd θ w t ∧
      Summable fun t => β ^ t * sgOfBdd θ x t ^ (-σ) * θ ^ t := by
  have hxt : ∀ t, 0 < x t := fun t => lt_of_lt_of_le ha' (hx t)
  have hid : ∀ t (d : ℝ), β ^ t * sgOfBdd θ x t ^ (-σ) * (θ ^ t * d) =
      sgPriceWeight β θ σ x t * d := fun t d => by
    change β ^ t * (θ ^ t * x t) ^ (-σ) * (θ ^ t * d) = _
    rw [sgPriceWeight, mul_assoc, sg_price_identity hθ (hxt t) t d, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [sgPriceDual_apply]
    congr 1
    funext t
    exact (hid t (w t)).symm
  · have := sg_price_summable hσ hβ0 hθ hρ1 ha' hx (sgConst 1)
    refine this.congr fun t => ?_
    have h := hid t 1
    rw [mul_one] at h
    rw [h, sgConst_apply]

/-- **Exercise 16.3(e)(ii), direct proof with inner-product prices**: if `(x, x)` is Pareto
optimal and `x_t ≥ a′θᵗ` with `a′ > a`, then `(x, x, p)` with `p_t = βᵗ x_t^{−σ}`
(`sgPriceDual`, `sgPriceDual_eq_inner`) is a competitive equilibrium. Any `θ > 0`. -/
theorem ex_16_3e_ii_direct {β θ σ a a' γ α k0 : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) (haa' : a < a') (hγ : 0 < γ)
    (hα0 : 0 < α) (hα1 : α < 1) {x : BddSeq ℝ}
    (hPO : ParetoOptimal (sgX θ a) (sgU β σ θ) (sgY θ γ α k0) (fun _ => x) (fun _ => x))
    (hx' : ∀ t, a' ≤ x t) :
    CompetitiveEq (sgX θ a) (sgU β σ θ) (sgY θ γ α k0) (fun _ => x) (fun _ => x)
      (sgPriceDual hσ hβ0 hθ hρ1 (by linarith) hx') := by
  have ha' : 0 < a' := by linarith
  set ρ := β * θ ^ (1 - σ)
  have hρ0 : 0 ≤ ρ := mul_nonneg hβ0 (Real.rpow_nonneg hθ.le _)
  obtain ⟨⟨hxX, hxY⟩, hmax⟩ := sg_paretoOptimal_iff.1 hPO
  set φ := sgPriceDual hσ hβ0 hθ hρ1 ha' hx'
  have hxt : ∀ t, 0 < x t := fun t => lt_of_lt_of_le ha' (hx' t)
  have hux := ex_16_3d_summable hσ hβ0 hβ1 hθ hρ1 ha hxX
  refine ⟨hPO.1, fun _ z hz hφz => ?_, fun _ y hy => ?_⟩
  · -- utility maximisation: the summed tangent inequality
    have huz := ex_16_3d_summable hσ hβ0 hβ1 hθ hρ1 ha hz
    have hsz := sg_price_summable hσ hβ0 hθ hρ1 ha' hx' z
    have hsx := sg_price_summable hσ hβ0 hθ hρ1 ha' hx' x
    have hle : sgUtility β (sgCRRA σ) (sgOfBdd θ z) ≤
        ∑' t, (β ^ t * sgCRRA σ (sgOfBdd θ x t) +
          (sgPriceWeight β θ σ x t * z t - sgPriceWeight β θ σ x t * x t)) := by
      refine huz.tsum_le_tsum (fun t => ?_) (hux.add (hsz.sub hsx))
      have h := sgCRRA_tangent hσ (sgXa_pos hθ ha hxX t) (sgXa_pos hθ ha hz t)
      have hid := sg_price_identity (β := β) (σ := σ) hθ (hxt t) t (z t - x t)
      have e : sgOfBdd θ z t - sgOfBdd θ x t = θ ^ t * (z t - x t) := by
        simp only [sgOfBdd]; ring
      rw [e] at h
      have hb := pow_nonneg hβ0 t
      have := mul_le_mul_of_nonneg_left h hb
      change β ^ t * sgCRRA σ (sgOfBdd θ z t) ≤ _
      rw [sgPriceWeight]
      change β ^ t * sgCRRA σ (sgOfBdd θ z t) ≤ β ^ t * sgCRRA σ (θ ^ t * x t) + _
      have hid' : β ^ t * ((θ ^ t * x t) ^ (-σ) * (θ ^ t * (z t - x t))) =
          (β * θ ^ (1 - σ)) ^ t * x t ^ (-σ) * z t - (β * θ ^ (1 - σ)) ^ t * x t ^ (-σ) * x t := by
        rw [hid]; ring
      change β ^ t * sgCRRA σ (sgOfBdd θ z t) ≤
        β ^ t * (sgCRRA σ (θ ^ t * x t) + (θ ^ t * x t) ^ (-σ) * (θ ^ t * (z t - x t))) at this
      linarith
    rw [hux.tsum_add (hsz.sub hsx), hsz.tsum_sub hsx] at hle
    have hφz' : ∑' t, sgPriceWeight β θ σ x t * z t ≤ ∑' t, sgPriceWeight β θ σ x t * x t := hφz
    change sgUtility β (sgCRRA σ) (sgOfBdd θ z) ≤ sgUtility β (sgCRRA σ) (sgOfBdd θ x)
    unfold sgUtility at hle ⊢
    linarith
  · -- profit maximisation: the first-order condition along the segment towards `y`
    have hy0 : ∀ t, 0 ≤ y t := sgTechθ_nonneg hθ hy
    set l0 := 1 - a / a'
    have hl0 : 0 < l0 := by
      simp only [l0]
      rw [sub_pos, div_lt_one ha']
      exact haa'
    have hl01 : l0 ≤ 1 := by simp only [l0]; linarith [div_pos ha ha']
    set lam : ℕ → ℝ := fun n => l0 / ((n : ℝ) + 1)
    have hlam0 : ∀ n, 0 < lam n := fun n => by positivity
    have hlam1 : ∀ n, lam n ≤ l0 := fun n => by
      simp only [lam]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    set m : ℕ → BddSeq ℝ := fun n => (1 - lam n) • x + lam n • y
    have hmt : ∀ n t, m n t = (1 - lam n) * x t + lam n * y t := fun n t => by
      simp only [m]
      rw [seq_coord_combo, smul_eq_mul, smul_eq_mul]
    have hmX : ∀ n, m n ∈ sgXa θ a := fun n => (mem_sgXa_iff hθ).2 fun t => by
      rw [hmt]
      have h1 : a ≤ (1 - lam n) * a' := by
        have := hlam1 n
        simp only [l0] at this
        have : lam n * a' ≤ a' - a := by
          calc lam n * a' ≤ (1 - a / a') * a' := mul_le_mul_of_nonneg_right this ha'.le
            _ = a' - a := by field_simp
        nlinarith
      have h2 : (1 - lam n) * a' ≤ (1 - lam n) * x t :=
        mul_le_mul_of_nonneg_left (hx' t) (by linarith [hlam1 n])
      nlinarith [mul_nonneg (hlam0 n).le (hy0 t)]
    have hmY : ∀ n, m n ∈ sgTechθ θ γ α k0 := fun n =>
      sg_convex_sgTechθ hγ hα0 hα1 hxY hy (by linarith [hlam1 n]) (hlam0 n).le (by ring)
    have hmpos : ∀ n t, 0 < m n t := fun n t =>
      lt_of_lt_of_le ha ((mem_sgXa_iff hθ).1 (hmX n) t)
    set G : ℕ → ℕ → ℝ := fun n t => ρ ^ t * (m n t ^ (-σ) * (y t - x t))
    -- `G(λ) ≤ 0` for each `λ_n`
    have hGs : ∀ n, Summable (G n) := fun n => by
      refine Summable.of_norm_bounded (((summable_geometric_of_lt_one hρ0 hρ1).mul_left
        (a ^ (-σ))).mul_right (‖y‖ + ‖x‖)) fun t => ?_
      have hm1 : m n t ^ (-σ) ≤ a ^ (-σ) := Real.rpow_le_rpow_of_nonpos ha
        ((mem_sgXa_iff hθ).1 (hmX n) t) (by linarith)
      have hd : |y t - x t| ≤ ‖y‖ + ‖x‖ := by
        have := norm_seq_coord_le y t
        have := norm_seq_coord_le x t
        rw [Real.norm_eq_abs] at *
        exact (abs_sub _ _).trans (by linarith)
      simp only [G]
      rw [norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg hρ0,
        Real.norm_of_nonneg (Real.rpow_nonneg (hmpos n t).le _), Real.norm_eq_abs]
      calc ρ ^ t * (m n t ^ (-σ) * |y t - x t|) ≤ ρ ^ t * (a ^ (-σ) * (‖y‖ + ‖x‖)) := by
            gcongr
        _ = a ^ (-σ) * ρ ^ t * (‖y‖ + ‖x‖) := by ring
    have hGle : ∀ n, ∑' t, G n t ≤ 0 := by
      intro n
      have hum := ex_16_3d_summable hσ hβ0 hβ1 hθ hρ1 ha (hmX n)
      have hu := hmax (m n) ⟨hmX n, hmY n⟩
      change sgUtility β (sgCRRA σ) (sgOfBdd θ (m n)) ≤ sgUtility β (sgCRRA σ) (sgOfBdd θ x)
        at hu
      have hlow : ∑' t, lam n * G n t ≤ ∑' t, (β ^ t * sgCRRA σ (sgOfBdd θ (m n) t) -
          β ^ t * sgCRRA σ (sgOfBdd θ x t)) := by
        refine ((hGs n).mul_left (lam n)).tsum_le_tsum (fun t => ?_) (hum.sub hux)
        have h := sgCRRA_tangent hσ (sgXa_pos hθ ha (hmX n) t) (sgXa_pos hθ ha hxX t)
        have e : sgOfBdd θ x t - sgOfBdd θ (m n) t = θ ^ t * (-(lam n * (y t - x t))) := by
          simp only [sgOfBdd]; rw [hmt]; ring
        rw [e] at h
        have hid := sg_price_identity (β := β) (σ := σ) hθ (hmpos n t) t (-(lam n * (y t - x t)))
        have hb := mul_le_mul_of_nonneg_left h (pow_nonneg hβ0 t)
        have hmo : sgOfBdd θ (m n) t = θ ^ t * m n t := rfl
        rw [hmo] at hb ⊢
        simp only [G]
        nlinarith
      rw [tsum_mul_left, hum.tsum_sub hux] at hlow
      unfold sgUtility at hu
      by_contra hpos
      push Not at hpos
      have := mul_pos (hlam0 n) hpos
      linarith
    -- the limit `λ_n → 0`
    have hlamlim : Tendsto lam atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul l0
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      simp only [lam]
      ring
    have hlim : Tendsto (fun n => ∑' t, G n t) atTop
        (𝓝 (∑' t, ρ ^ t * (x t ^ (-σ) * (y t - x t)))) := by
      refine tendsto_tsum_of_dominated_convergence
        (bound := fun t => a ^ (-σ) * ρ ^ t * (‖y‖ + ‖x‖))
        (((summable_geometric_of_lt_one hρ0 hρ1).mul_left (a ^ (-σ))).mul_right (‖y‖ + ‖x‖))
        (fun t => ?_) (Eventually.of_forall fun n t => ?_)
      · have hmlim : Tendsto (fun n => m n t) atTop (𝓝 (x t)) := by
          have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hlamlim).mul
            (tendsto_const_nhds (x := x t)) |>.add (hlamlim.mul (tendsto_const_nhds (x := y t)))
          simp only [sub_zero, one_mul, zero_mul, add_zero] at this
          exact this.congr fun n => (hmt n t).symm
        have hpow : Tendsto (fun n => m n t ^ (-σ)) atTop (𝓝 (x t ^ (-σ))) :=
          (Real.continuousAt_rpow_const _ _ (Or.inl (hxt t).ne')).tendsto.comp hmlim
        exact tendsto_const_nhds.mul (hpow.mul tendsto_const_nhds)
      · have hm1 : m n t ^ (-σ) ≤ a ^ (-σ) := Real.rpow_le_rpow_of_nonpos ha
          ((mem_sgXa_iff hθ).1 (hmX n) t) (by linarith)
        have hd : |y t - x t| ≤ ‖y‖ + ‖x‖ := by
          have := norm_seq_coord_le y t
          have := norm_seq_coord_le x t
          rw [Real.norm_eq_abs] at *
          exact (abs_sub _ _).trans (by linarith)
        rw [norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg hρ0,
          Real.norm_of_nonneg (Real.rpow_nonneg (hmpos n t).le _), Real.norm_eq_abs]
        calc ρ ^ t * (m n t ^ (-σ) * |y t - x t|) ≤ ρ ^ t * (a ^ (-σ) * (‖y‖ + ‖x‖)) := by
              gcongr
          _ = a ^ (-σ) * ρ ^ t * (‖y‖ + ‖x‖) := by ring
    have hG0 := le_of_tendsto' hlim hGle
    have hsy := sg_price_summable hσ hβ0 hθ hρ1 ha' hx' y
    have hsx := sg_price_summable hσ hβ0 hθ hρ1 ha' hx' x
    have heq : ∑' t, ρ ^ t * (x t ^ (-σ) * (y t - x t)) = φ y - φ x := by
      rw [sgPriceDual_apply, sgPriceDual_apply, ← hsy.tsum_sub hsx]
      congr 1
      funext t
      simp only [sgPriceWeight, ρ]
      ring
    linarith

end StokeyLucasPrescott.EquilibriumApplications
