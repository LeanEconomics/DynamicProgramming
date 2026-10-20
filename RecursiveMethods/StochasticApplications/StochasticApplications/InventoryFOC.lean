/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.InventoryPolicy

/-!
# Production and inventory accumulation: first-order conditions

SLP §10.5, Exercises 10.5c–g, pp. 299–300. Let `v` be the fixed point of the inventory problem
(`InventoryResults`), `Y(x)` and `N(x)` the optimal storage and input at stock `x`, and `v′` the
derivative of `x ↦ v(x, ω)` (which does not depend on `ω`, `inv_indep`).

**Hypotheses.** Besides `InvHyp` (which already has `U` strictly concave and `φ`, `c` strictly
convex), the first-order arguments use, each only where stated:
* `hUd`: `U` is differentiable on `(0, ∞)`;
* `hHd`: `φ` (here `H`) is differentiable on `(0, ∞)`;
* `hcd`: `c` is differentiable on `(0, ∞)`;
* `hc0`: `c′(0) = 0`, as a right derivative (`HasDerivWithinAt c 0 (Ici 0) 0`);
* `hμ`: the harvest has positive mean, `E ω′ > 0`.
The book's continuity of the derivatives and `φ′(0) = 0` are not needed.

**Results.**
* `inv_Y_lt`: `Y(x) < x` for every `x > 0`, with no differentiability. If `Y(x) = x`, the plan
  `(x/2, N(x))` at `x/2` gives `(1 − β)[v(x) − v(x/2)] ≤ −[φ(x) − φ(x/2)] < 0`. So the corner
  where the envelope argument only gives a one-sided bound never occurs for `x > 0`, and
  `inv_hasDerivAt_pos` gives the book's `v′(x) = U′[x − Y(x)]` at every `x > 0` (Exercise 10.5c).
* `inv_N_lt`: `N(x) < N̄`, so `N̄` never binds.
* `inv_differentiableAt`, `inv_deriv_strictAnti`, `inv_deriv_pos`: `v` is differentiable on
  `(0, ∞)`, with `v′ > 0` strictly decreasing.
* `inv_hasDerivAt_Ey`, `inv_hasDerivAt_En`: differentiation of `E v(y + nω′)` under the integral,
  in `y > 0` and in `n > 0`.
* `inv_foc_y`, `inv_foc_n`: the first-order conditions (3) and (4) hold with equality when
  `Y(x) > 0`, resp. `N(x) > 0`.
* **Exercise 10.5d** (`ex_10_5d`): consumption `x − Y(x)` is strictly increasing (needs `hUd`).
* **Exercise 10.5e**, strict form (`ex_10_5e_strict`): for `x₁ < x₂`, `Y(x₁) < Y(x₂)` or
  `Y(x₁) = Y(x₂) = 0` (needs `hUd`, `hHd`). With `ex_10_5e`'s `N(x₂) ≤ N(x₁)`, (3) at both stocks
  gives a contradiction directly; the sign argument of 10.5f (`ex_10_5f`) is not needed.
* **Exercise 10.5g**, corrected (`ex_10_5g`): with `hUd`, `hHd`, `hcd`, `hc0`, `hμ`, for `x₁ < x₂`,
  `N(x₁), N(x₂) > 0` (`inv_N_pos`); `N(x₂) < N(x₁)` if `Y(x₂) > 0` (`inv_N_strict`); and
  `N(x₂) = N(x₁)` if `Y(x₂) = 0` (`inv_N_eq_of_Y_zero`).
* `inv_Y_eq_zero`: if `U′ ≤ L` on `(0, ∞)` and `U′(x) > βL`, then `Y(x) = 0`. Under the book's
  assumptions `U′ = D ≤ D(0) < ∞`, so nothing is stored at small stocks.
* `inv_deriv_le`, `inv_sub_le`: if `U′ ≤ L` then `v′ ≤ L` and `v` is `L`-Lipschitz.
* `inv_N_eq_zero` (the book's question "if `c′(0) > 0`?"): if `U′ ≤ L` and `c(n) ≥ κn` with
  `κ > βLω₂`, then `N ≡ 0`. With `c′(0) > 0`, `N(x) > 0` can fail; `inv_N_strict` still gives
  `N(x₂) < N(x₁)` whenever `Y(x₂) > 0` and `N(x₁) > 0`.

**Correction** (Exercise 10.5g). The claim `x₂ > x₁ ⇒ N(x₂) < N(x₁)` is false: where nothing is
stored, `Y(x₁) = Y(x₂) = 0`, the input solves `max −c(n) + βE v(nω′)`, which does not involve the
stock, so `N(x₁) = N(x₂)`; and by `inv_Y_eq_zero` this happens for all small stocks under the
book's assumptions. A concrete instance satisfying all of them is `ex_10_5g_counterexample` in
`InventoryCounterexample`. The claim `N(x) > 0` also needs `E ω′ > 0`
(`ex_10_5g_mean_zero`).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

variable {U H c : ℝ → ℝ} {β Ubar Nbar ω₁ ω₂ : ℝ} {μ : Measure (Icc ω₁ ω₂)}
  [IsProbabilityMeasure μ]

/-- The continuation integrand in terms of `v(·, ω)`, for any fixed `ω`. -/
theorem inv_cont_eq (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (ω : Icc ω₁ ω₂) (x : Ici (0 : ℝ)) {p : ℝ × ℝ}
    (hy : 0 ≤ p.1) (hn : 0 ≤ p.2) (ω' : Icc ω₁ ω₂) :
    v (invφ (x, p, ω'), ω') = liftS (fun x => v (x, ω)) (p.1 + p.2 * ω'.1) := by
  rw [v_invφ h.ω_nonneg v x hy hn ω']
  congr 1
  funext x'
  exact inv_indep h hv x' ω' ω

/-- The expected continuation value as `E v(y + nω′)`. -/
theorem inv_integral_eq (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v) (ω : Icc ω₁ ω₂)
    (x : Ici (0 : ℝ)) {p : ℝ × ℝ} (hy : 0 ≤ p.1) (hn : 0 ≤ p.2) :
    ∫ ω', v (invφ (x, p, ω'), ω') ∂μ =
      ∫ ω', liftS (fun x => v (x, ω)) (p.1 + p.2 * ω'.1) ∂μ :=
  integral_congr_ae (Eventually.of_forall (inv_cont_eq h hv ω x hy hn))

/-- `ω′ ↦ v(y + nω′)` is integrable. -/
theorem inv_integrable (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v) (ω : Icc ω₁ ω₂)
    {p : ℝ × ℝ} (hy : 0 ≤ p.1) (hn : 0 ≤ p.2) :
    Integrable (fun ω' : Icc ω₁ ω₂ => liftS (fun x => v (x, ω)) (p.1 + p.2 * ω'.1)) μ :=
  (integrable_inv (μ := μ) v ⟨0, mem_Ici.2 le_rfl⟩ p).congr
    (Eventually.of_forall (inv_cont_eq h hv ω _ hy hn))

/-- **No corner in storage.** For `x > 0` it is never optimal to store the whole stock:
`Y(x) < x`. If `Y(x) = x`, the plan `(x/2, N(x))` is feasible at `x/2` and also consumes nothing,
so `v(x) − v(x/2) ≤ −[φ(x) − φ(x/2)] + β[v(x) − v(x/2)]` by concavity of `v`, which is impossible
since `v` is strictly increasing. -/
theorem inv_Y_lt (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) {x : Ici (0 : ℝ)} {ω : Icc ω₁ ω₂} {P : ℝ × ℝ}
    (hP : P ∈ policy (invModel μ U H c β Nbar) v (x, ω)) (hx : 0 < x.1) : P.1 < x.1 := by
  have hy0 : 0 ≤ P.1 := hP.1.1.1
  have hn0 : 0 ≤ P.2 := hP.1.2.1
  rcases lt_or_eq_of_le hP.1.1.2 with hlt | heq
  · exact hlt
  exfalso
  have heq' : P.1 = x.1 := heq
  set g := liftS (fun x => v (x, ω)) with hgdef
  have hx2 : (0 : ℝ) ≤ x.1 / 2 := by positivity
  set x' : Ici (0 : ℝ) := ⟨x.1 / 2, hx2⟩
  have hfeas : ((x.1 / 2, P.2) : ℝ × ℝ) ∈ invΓ Nbar (x', ω) := ⟨⟨hx2, le_rfl⟩, hP.1.2⟩
  have hle := (inv_max h hv (x', ω)).2 _ hfeas
  have e := hP.2
  rw [inv_rhs] at hle e
  rw [inv_integral_eq h hv ω x hy0 hn0] at e
  rw [inv_integral_eq h hv ω x' (p := (x.1 / 2, P.2)) hx2 hn0] at hle
  have i1 := inv_integrable (μ := μ) h hv ω hy0 hn0
  have i2 := inv_integrable (μ := μ) h hv ω (p := (x.1 / 2, P.2)) hx2 hn0
  have hg := concaveOn_liftS (inv_strictConcave h hv ω).isConcaveS
  have hint : ∫ ω', g (P.1 + P.2 * ω'.1) ∂μ - ∫ ω', g (x.1 / 2 + P.2 * ω'.1) ∂μ ≤
      g x.1 - g (x.1 / 2) := by
    rw [← integral_sub i1 i2]
    have := integral_mono (i1.sub i2) (integrable_const (g x.1 - g (x.1 / 2))) fun ω' => by
      have hw : 0 ≤ ω'.1 := h.ω_nonneg.trans ω'.2.1
      have hk : 0 ≤ P.2 * ω'.1 := mul_nonneg hn0 hw
      have := concave_four hg (mem_Ici.2 hx2) (mem_Ici.2 (by linarith : 0 ≤ x.1 + P.2 * ω'.1))
        (by linarith : x.1 / 2 ≤ x.1) (by linarith : x.1 ≤ x.1 + P.2 * ω'.1)
        (by ring : x.1 + (x.1 / 2 + P.2 * ω'.1) = x.1 / 2 + (x.1 + P.2 * ω'.1))
      simp only [Pi.sub_apply, heq']
      linarith
    simpa using this
  have hgx : g x.1 = v (x, ω) := liftS_of_mem _ x.2
  have hgx' : g (x.1 / 2) = v (x', ω) := liftS_of_mem _ (mem_Ici.2 hx2)
  have hlt : v (x', ω) < v (x, ω) :=
    inv_strictMono h hv ω (show x' < x from (by change x.1 / 2 < x.1; linarith))
  have hH := h.H_mono (mem_Ici.2 hx2) x.2 (by linarith : x.1 / 2 < x.1)
  have e0 : x.1 - P.1 = 0 := by rw [heq', sub_self]
  have e0' : (x'.1 : ℝ) - x.1 / 2 = 0 := sub_self _
  have hHP : H P.1 = H x.1 := by rw [heq']
  dsimp only at hle e
  rw [e0] at e
  rw [e0'] at hle
  rw [← hgdef] at e hle
  nlinarith [mul_pos (sub_pos.2 h.β_lt) (sub_pos.2 hlt), h.β_pos]

/-- The input bound never binds: `N(x) < N̄`. At `n = N̄` the return is below `0 ≤ v`. -/
theorem inv_N_lt (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) {x : Ici (0 : ℝ)} {ω : Icc ω₁ ω₂} {P : ℝ × ℝ}
    (hP : P ∈ policy (invModel μ U H c β Nbar) v (x, ω)) : P.2 < Nbar := by
  rcases lt_or_eq_of_le hP.1.2.2 with hlt | heq
  · exact hlt
  exfalso
  have hR := inv_bounds h hv
  have hE : ∫ ω', v (invφ (x, P, ω'), ω') ∂μ ≤ Ubar / (1 - β) := by
    have := integral_mono (integrable_inv (μ := μ) v x P) (integrable_const (Ubar / (1 - β)))
      fun ω' => (hR _).2
    simpa using this
  have hF := h.F_le (p := (x, P, ω)) hP.1.1.2 hP.1.1.1
  have hβ1 : 0 < 1 - β := by linarith [h.β_lt]
  have e : Ubar / (1 - β) = Ubar + β * (Ubar / (1 - β)) := by field_simp; ring
  have h0 := (hR (x, ω)).1
  have e2 := hP.2
  rw [inv_rhs] at e2
  change U (x.1 - P.1) - H P.1 - c P.2 ≤ Ubar - c P.2 at hF
  rw [heq] at hF e2
  nlinarith [mul_le_mul_of_nonneg_left hE h.β_pos.le, h.N_big]

/-- **Exercise 10.5c**, at every `x > 0`: `v′(x) = U′[x − Y(x)]` wherever `U` is differentiable
on `(0, ∞)`. Since `Y(x) < x` (`inv_Y_lt`), the proviso of `inv_hasDerivAt` always holds. -/
theorem inv_hasDerivAt_pos (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v)
    (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q) {x : Ici (0 : ℝ)} {ω : Icc ω₁ ω₂} {P : ℝ × ℝ}
    (hP : P ∈ policy (invModel μ U H c β Nbar) v (x, ω)) (hx : 0 < x.1) :
    HasDerivAt (liftS fun x => v (x, ω)) (deriv U (x.1 - P.1)) x.1 :=
  inv_hasDerivAt h hv hP (inv_Y_lt h hv hP hx)
    (hUd _ (sub_pos.2 (inv_Y_lt h hv hP hx))).hasDerivAt

/-- `v` is differentiable at every `x > 0`. -/
theorem inv_differentiableAt (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v)
    (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q) (ω : Icc ω₁ ω₂) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (liftS fun x => v (x, ω)) z := by
  obtain ⟨p, hp, hval⟩ := (inv_max h hv (⟨z, mem_Ici.2 hz.le⟩, ω)).1
  exact (inv_hasDerivAt_pos h hv hUd (P := p) ⟨hp, hval⟩ hz).differentiableAt

/-- `v′` is strictly decreasing on `(0, ∞)`. -/
theorem inv_deriv_strictAnti (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v)
    (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q) (ω : Icc ω₁ ω₂) :
    StrictAntiOn (deriv (liftS fun x => v (x, ω))) (Ioi 0) :=
  ((strictConcaveOn_liftS (inv_strictConcave h hv ω)).subset Ioi_subset_Ici_self
    (convex_Ioi 0)).strictAntiOn_deriv fun _ hz => inv_differentiableAt h hv hUd ω hz

/-- `v′ > 0` on `(0, ∞)`. -/
theorem inv_deriv_pos (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v)
    (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q) (ω : Icc ω₁ ω₂) {z : ℝ} (hz : 0 < z) :
    0 < deriv (liftS fun x => v (x, ω)) z := by
  have hg := concaveOn_liftS (inv_strictConcave h hv ω).isConcaveS
  have hsl := hg.slope_le_deriv (mem_Ici.2 hz.le) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ z + 1))
    (by linarith : z < z + 1) (inv_differentiableAt h hv hUd ω hz)
  have hlt : v (⟨z, mem_Ici.2 hz.le⟩, ω) < v (⟨z + 1, mem_Ici.2 (by linarith)⟩, ω) :=
    inv_strictMono h hv ω (show (⟨z, _⟩ : Ici (0 : ℝ)) < ⟨z + 1, _⟩ from
      (by change z < z + 1; linarith))
  rw [slope_def_field, liftS_of_mem _ (mem_Ici.2 hz.le),
    liftS_of_mem _ (mem_Ici.2 (by linarith : (0 : ℝ) ≤ z + 1)), add_sub_cancel_left,
    div_one] at hsl
  linarith

/-- The bound `w v′(y + m w) ≤ R/m`, from `v′(m w) ≤ [v(m w) − v(0)]/(m w)`. -/
theorem inv_mul_deriv_le (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v)
    (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q) (ω : Icc ω₁ ω₂) {y m w : ℝ} (hy : 0 ≤ y)
    (hm : 0 < m) (hw : 0 < w) :
    w * deriv (liftS fun x => v (x, ω)) (y + m * w) ≤ Ubar / (1 - β) / m := by
  have hg := concaveOn_liftS (inv_strictConcave h hv ω).isConcaveS
  have hmw : 0 < m * w := mul_pos hm hw
  have h1 : deriv (liftS fun x => v (x, ω)) (y + m * w) ≤
      deriv (liftS fun x => v (x, ω)) (m * w) :=
    (inv_deriv_strictAnti h hv hUd ω).antitoneOn (mem_Ioi.2 hmw) (mem_Ioi.2 (by linarith))
      (by linarith)
  have h2 := hg.deriv_le_slope (mem_Ici.2 le_rfl) (mem_Ici.2 hmw.le) hmw
    (inv_differentiableAt h hv hUd ω hmw)
  rw [slope_def_field, liftS_of_mem _ (mem_Ici.2 hmw.le), liftS_of_mem _ (mem_Ici.2 le_rfl),
    sub_zero, le_div_iff₀ hmw] at h2
  have hR := inv_bounds h hv
  have b1 := (hR (⟨m * w, mem_Ici.2 hmw.le⟩, ω)).2
  have b0 := (hR (⟨0, mem_Ici.2 le_rfl⟩, ω)).1
  rw [le_div_iff₀ hm]
  nlinarith

/-- Differentiation under the integral in `y`: for `y > 0`,
`d/dy E v(y + nω′) = E v′(y + nω′)`. -/
theorem inv_hasDerivAt_Ey (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v)
    (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q) (ω : Icc ω₁ ω₂) {y n : ℝ} (hy : 0 < y)
    (hn : 0 ≤ n) :
    Integrable (fun ω' : Icc ω₁ ω₂ => deriv (liftS fun x => v (x, ω)) (y + n * ω'.1)) μ ∧
      HasDerivAt (fun y => ∫ ω', liftS (fun x => v (x, ω)) (y + n * ω'.1) ∂μ)
        (∫ ω', deriv (liftS fun x => v (x, ω)) (y + n * ω'.1) ∂μ) y := by
  have hpos : ∀ z ∈ Ioi (y / 2), ∀ ω' : Icc ω₁ ω₂, y / 2 < z + n * ω'.1 := fun z hz ω' => by
    have := mul_nonneg hn (h.ω_nonneg.trans ω'.2.1)
    have := mem_Ioi.1 hz
    linarith
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z (ω' : Icc ω₁ ω₂) => liftS (fun x => v (x, ω)) (z + n * ω'.1))
    (F' := fun z (ω' : Icc ω₁ ω₂) => deriv (liftS fun x => v (x, ω)) (z + n * ω'.1))
    (bound := fun _ => deriv (liftS fun x => v (x, ω)) (y / 2))
    (Ioi_mem_nhds (by linarith : y / 2 < y)) ?_ ?_ ?_ ?_ (integrable_const (μ := μ) _) ?_
  · filter_upwards [Ioi_mem_nhds (by linarith : y / 2 < y)] with z hz
    exact (inv_integrable h hv ω (p := (z, n))
      (by have := mem_Ioi.1 hz; dsimp only; linarith) hn).aestronglyMeasurable
  · exact inv_integrable h hv ω (p := (y, n)) hy.le hn
  · exact ((measurable_deriv _).comp (measurable_const.add
      (measurable_const.mul measurable_subtype_coe))).aestronglyMeasurable
  · refine Eventually.of_forall fun ω' z hz => ?_
    have hz' := hpos z hz ω'
    have hp := inv_deriv_pos h hv hUd ω (by linarith : 0 < z + n * ω'.1)
    rw [Real.norm_eq_abs, abs_of_pos hp]
    exact ((inv_deriv_strictAnti h hv hUd ω) (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith))
      hz').le
  · refine Eventually.of_forall fun ω' z hz => ?_
    have hz' := hpos z hz ω'
    exact (inv_differentiableAt h hv hUd ω (by linarith : 0 < z + n * ω'.1)).hasDerivAt
      |>.comp_add_const z (n * ω'.1)

/-- Differentiation under the integral in `n`: for `n > 0`,
`d/dn E v(y + nω′) = E ω′ v′(y + nω′)`. -/
theorem inv_hasDerivAt_En (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v)
    (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q) (ω : Icc ω₁ ω₂) {y n : ℝ} (hy : 0 ≤ y)
    (hn : 0 < n) :
    Integrable (fun ω' : Icc ω₁ ω₂ => ω'.1 * deriv (liftS fun x => v (x, ω)) (y + n * ω'.1)) μ ∧
      HasDerivAt (fun n => ∫ ω', liftS (fun x => v (x, ω)) (y + n * ω'.1) ∂μ)
        (∫ ω', ω'.1 * deriv (liftS fun x => v (x, ω)) (y + n * ω'.1) ∂μ) n := by
  have hR0 : 0 ≤ Ubar / (1 - β) := div_nonneg h.Ubar_nonneg (by linarith [h.β_lt])
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun m (ω' : Icc ω₁ ω₂) => liftS (fun x => v (x, ω)) (y + m * ω'.1))
    (F' := fun m (ω' : Icc ω₁ ω₂) => ω'.1 * deriv (liftS fun x => v (x, ω)) (y + m * ω'.1))
    (bound := fun _ => Ubar / (1 - β) / (n / 2))
    (Ioi_mem_nhds (by linarith : n / 2 < n)) ?_ ?_ ?_ ?_ (integrable_const (μ := μ) _) ?_
  · filter_upwards [Ioi_mem_nhds (by linarith : n / 2 < n)] with m hm
    exact (inv_integrable h hv ω (p := (y, m)) hy
      (by have := mem_Ioi.1 hm; dsimp only; linarith)).aestronglyMeasurable
  · exact inv_integrable h hv ω (p := (y, n)) hy hn.le
  · exact (measurable_subtype_coe.mul ((measurable_deriv _).comp (measurable_const.add
      (measurable_const.mul measurable_subtype_coe)))).aestronglyMeasurable
  · refine Eventually.of_forall fun ω' m hm => ?_
    have hm' : n / 2 < m := hm
    have hw : 0 ≤ ω'.1 := h.ω_nonneg.trans ω'.2.1
    rcases hw.eq_or_lt with hw0 | hw0
    · rw [← hw0, zero_mul, norm_zero]; positivity
    · have hz : 0 < y + m * ω'.1 := by have := mul_pos (by linarith : 0 < m) hw0; linarith
      have hp := inv_deriv_pos h hv hUd ω hz
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos hw0 hp)]
      refine (inv_mul_deriv_le h hv hUd ω hy (by linarith) hw0).trans ?_
      exact div_le_div_of_nonneg_left hR0 (by linarith) hm'.le
  · refine Eventually.of_forall fun ω' m hm => ?_
    have hm' : n / 2 < m := hm
    have hw : 0 ≤ ω'.1 := h.ω_nonneg.trans ω'.2.1
    rcases hw.eq_or_lt with hw0 | hw0
    · simp only [← hw0, mul_zero, add_zero, zero_mul]
      exact hasDerivAt_const _ _
    · have hd : HasDerivAt (fun m => y + m * ω'.1) ω'.1 m := by
        simpa using ((hasDerivAt_id m).mul_const ω'.1).const_add y
      have hz : 0 < y + m * ω'.1 := by have := mul_pos (by linarith : 0 < m) hw0; linarith
      have := (inv_differentiableAt h hv hUd ω hz).hasDerivAt.comp m hd
      rw [mul_comm] at this
      exact this

/-- **First-order condition (3)**, interior case. If `Y(x) > 0`, and `φ` is differentiable at
`Y(x)`, then `U′[x − Y(x)] + φ′[Y(x)] = β E v′[Y(x) + N(x)ω′]`. (`Y(x) < x` by `inv_Y_lt`.) -/
theorem inv_foc_y (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q)
    {x : Ici (0 : ℝ)} {ω : Icc ω₁ ω₂} {P : ℝ × ℝ}
    (hP : P ∈ policy (invModel μ U H c β Nbar) v (x, ω)) (hY : 0 < P.1)
    (hHd : DifferentiableAt ℝ H P.1) :
    deriv U (x.1 - P.1) + deriv H P.1 =
      β * ∫ ω', deriv (liftS fun x => v (x, ω)) (P.1 + P.2 * ω'.1) ∂μ := by
  have hn0 : 0 ≤ P.2 := hP.1.2.1
  have hx : 0 < x.1 := hY.trans_le hP.1.1.2
  have hYx := inv_Y_lt h hv hP hx
  set f : ℝ → ℝ := fun y => U (x.1 - y) - H y - c P.2 +
    β * ∫ ω', liftS (fun x => v (x, ω)) (y + P.2 * ω'.1) ∂μ with hf
  have hmax : IsLocalMax f P.1 := by
    filter_upwards [Ioo_mem_nhds hY hYx] with y hy
    have hfeas : ((y, P.2) : ℝ × ℝ) ∈ invΓ Nbar (x, ω) := ⟨⟨hy.1.le, hy.2.le⟩, hP.1.2⟩
    have hle := (inv_max h hv (x, ω)).2 _ hfeas
    have e := hP.2
    rw [inv_rhs, inv_integral_eq h hv ω x (p := (y, P.2)) hy.1.le hn0] at hle
    rw [inv_rhs, inv_integral_eq h hv ω x hP.1.1.1 hn0] at e
    dsimp only at hle e
    simp only [hf]
    linarith
  have hd : HasDerivAt f (-deriv U (x.1 - P.1) - deriv H P.1 +
      β * ∫ ω', deriv (liftS fun x => v (x, ω)) (P.1 + P.2 * ω'.1) ∂μ) P.1 :=
    ((((hUd _ (sub_pos.2 hYx)).hasDerivAt.comp_const_sub x.1 P.1).sub hHd.hasDerivAt).sub_const
      (c P.2)).add ((inv_hasDerivAt_Ey h hv hUd ω hY hn0).2.const_mul β)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- **First-order condition (4)**, interior case. If `N(x) > 0` and `c` is differentiable at
`N(x)`, then `c′[N(x)] = β E ω′ v′[Y(x) + N(x)ω′]`. (`N(x) < N̄` by `inv_N_lt`.) -/
theorem inv_foc_n (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q)
    {x : Ici (0 : ℝ)} {ω : Icc ω₁ ω₂} {P : ℝ × ℝ}
    (hP : P ∈ policy (invModel μ U H c β Nbar) v (x, ω)) (hN : 0 < P.2)
    (hcd : DifferentiableAt ℝ c P.2) :
    deriv c P.2 = β * ∫ ω', ω'.1 * deriv (liftS fun x => v (x, ω)) (P.1 + P.2 * ω'.1) ∂μ := by
  have hy0 : 0 ≤ P.1 := hP.1.1.1
  have hNN := inv_N_lt h hv hP
  set f : ℝ → ℝ := fun n => U (x.1 - P.1) - H P.1 - c n +
    β * ∫ ω', liftS (fun x => v (x, ω)) (P.1 + n * ω'.1) ∂μ with hf
  have hmax : IsLocalMax f P.2 := by
    filter_upwards [Ioo_mem_nhds hN hNN] with n hn
    have hfeas : ((P.1, n) : ℝ × ℝ) ∈ invΓ Nbar (x, ω) := ⟨hP.1.1, hn.1.le, hn.2.le⟩
    have hle := (inv_max h hv (x, ω)).2 _ hfeas
    have e := hP.2
    rw [inv_rhs, inv_integral_eq h hv ω x (p := (P.1, n)) hy0 hn.1.le] at hle
    rw [inv_rhs, inv_integral_eq h hv ω x hy0 hP.1.2.1] at e
    dsimp only at hle e
    simp only [hf]
    linarith
  have hd : HasDerivAt f (0 - deriv c P.2 +
      β * ∫ ω', ω'.1 * deriv (liftS fun x => v (x, ω)) (P.1 + P.2 * ω'.1) ∂μ) P.2 :=
    ((hasDerivAt_const P.2 (U (x.1 - P.1) - H P.1)).sub hcd.hasDerivAt).add
      ((inv_hasDerivAt_En h hv hUd ω hy0 hN).2.const_mul β)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- **Exercise 10.5d.** Consumption `x − Y(x)` is strictly increasing in the stock `x`, when `U`
is differentiable on `(0, ∞)`. By the envelope condition `v′(x) = U′[x − Y(x)]` at every `x > 0`;
`v′` is strictly decreasing since `v` is strictly concave, and `U′` is nonincreasing. -/
theorem ex_10_5d (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q)
    {x₁ x₂ : Ici (0 : ℝ)} (hx : x₁.1 < x₂.1) (ω : Icc ω₁ ω₂) {P₁ P₂ : ℝ × ℝ}
    (hP₁ : P₁ ∈ policy (invModel μ U H c β Nbar) v (x₁, ω))
    (hP₂ : P₂ ∈ policy (invModel μ U H c β Nbar) v (x₂, ω)) :
    x₁.1 - P₁.1 < x₂.1 - P₂.1 := by
  have hx₂ : 0 < x₂.1 := lt_of_le_of_lt x₁.2 hx
  have hC₂ : 0 < x₂.1 - P₂.1 := sub_pos.2 (inv_Y_lt h hv hP₂ hx₂)
  rcases (mem_Ici.1 x₁.2).eq_or_lt with h0 | hx₁
  · have hY : P₁.1 = 0 := le_antisymm (h0 ▸ hP₁.1.1.2) hP₁.1.1.1
    rw [hY, ← h0, sub_zero]
    exact hC₂
  · have hC₁ : 0 < x₁.1 - P₁.1 := sub_pos.2 (inv_Y_lt h hv hP₁ hx₁)
    have hlt := inv_deriv_strictAnti h hv hUd ω (mem_Ioi.2 hx₁) (mem_Ioi.2 hx₂) hx
    rw [(inv_hasDerivAt_pos h hv hUd hP₁ hx₁).deriv,
      (inv_hasDerivAt_pos h hv hUd hP₂ hx₂).deriv] at hlt
    by_contra hge
    have := (h.U_conc.concaveOn.subset Ioi_subset_Ici_self (convex_Ioi 0)).antitoneOn_deriv
      (fun q hq => hUd q hq) (mem_Ioi.2 hC₂) (mem_Ioi.2 hC₁) (not_lt.1 hge)
    linarith

/-- **Exercise 10.5e** (strict form). If `x₁ < x₂` then `Y(x₁) < Y(x₂)`, or `Y(x₁) = Y(x₂) = 0`,
when `U` and `φ` are differentiable on `(0, ∞)`. If `Y(x₁) = Y(x₂) = Y > 0`, then (3) holds with
equality at both stocks; consumption is larger at `x₂`, so `U′` is strictly smaller there, while
`N(x₂) ≤ N(x₁)` (`ex_10_5e`) makes `E v′(Y + Nω′)` weakly larger. -/
theorem ex_10_5e_strict (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v)
    (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q) (hHd : ∀ y, 0 < y → DifferentiableAt ℝ H y)
    {x₁ x₂ : Ici (0 : ℝ)} (hx : x₁.1 < x₂.1) (ω : Icc ω₁ ω₂) {P₁ P₂ : ℝ × ℝ}
    (hP₁ : P₁ ∈ policy (invModel μ U H c β Nbar) v (x₁, ω))
    (hP₂ : P₂ ∈ policy (invModel μ U H c β Nbar) v (x₂, ω)) :
    P₁.1 < P₂.1 ∨ (P₁.1 = 0 ∧ P₂.1 = 0) := by
  obtain ⟨hY, hN⟩ := ex_10_5e h hv hx.le ω hP₁ hP₂
  rcases hY.lt_or_eq with hlt | heq
  · exact Or.inl hlt
  rcases (hP₁.1.1.1 : 0 ≤ P₁.1).eq_or_lt with h0 | hpos
  · exact Or.inr ⟨h0.symm, heq ▸ h0.symm⟩
  exfalso
  have hpos₂ : 0 < P₂.1 := heq ▸ hpos
  have f₁ := inv_foc_y h hv hUd hP₁ hpos (hHd _ hpos)
  have f₂ := inv_foc_y h hv hUd hP₂ hpos₂ (hHd _ hpos₂)
  rw [← heq] at f₂
  have hx₁ : 0 < x₁.1 := hpos.trans_le hP₁.1.1.2
  have hC₁ : 0 < x₁.1 - P₁.1 := sub_pos.2 (inv_Y_lt h hv hP₁ hx₁)
  have hUlt := (h.U_conc.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    (fun q hq => hUd q hq) (mem_Ioi.2 hC₁) (mem_Ioi.2 (by linarith : 0 < x₂.1 - P₁.1))
    (by linarith : x₁.1 - P₁.1 < x₂.1 - P₁.1)
  have i₁ := (inv_hasDerivAt_Ey h hv hUd ω hpos hP₁.1.2.1).1
  have i₂ := (inv_hasDerivAt_Ey h hv hUd ω hpos hP₂.1.2.1).1
  have hint : ∫ ω', deriv (liftS fun x => v (x, ω)) (P₁.1 + P₁.2 * ω'.1) ∂μ ≤
      ∫ ω', deriv (liftS fun x => v (x, ω)) (P₁.1 + P₂.2 * ω'.1) ∂μ := by
    refine integral_mono i₁ i₂ fun ω' => ?_
    have hw : 0 ≤ ω'.1 := h.ω_nonneg.trans ω'.2.1
    have a1 := mul_nonneg hP₂.1.2.1 hw
    have a2 := mul_le_mul_of_nonneg_right hN hw
    exact (inv_deriv_strictAnti h hv hUd ω).antitoneOn (mem_Ioi.2 (by linarith))
      (mem_Ioi.2 (by linarith)) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hint h.β_pos.le]

/-- **Exercise 10.5g** (first part). If `c′(0) = 0` (from the right) and the harvest has positive
mean, `E ω′ > 0`, then `N(x) > 0`. At `n = 0` a small input `n` costs `c(n) = o(n)` but raises
`E v(Y + nω′)` by at least `n κ E ω′`, where `κ > 0` is a chord slope of `v`. -/
theorem inv_N_pos (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (hc0 : HasDerivWithinAt c 0 (Ici 0) 0)
    (hμ : 0 < ∫ ω', ω'.1 ∂μ) {x : Ici (0 : ℝ)} {ω : Icc ω₁ ω₂} {P : ℝ × ℝ}
    (hP : P ∈ policy (invModel μ U H c β Nbar) v (x, ω)) : 0 < P.2 := by
  rcases (hP.1.2.1 : 0 ≤ P.2).eq_or_lt with h0 | hpos
  swap
  · exact hpos
  exfalso
  set g := liftS (fun x => v (x, ω)) with hgdef
  have hY0 : 0 ≤ P.1 := hP.1.1.1
  have hg := concaveOn_liftS (inv_strictConcave h hv ω).isConcaveS
  have hiw : Integrable (fun ω' : Icc ω₁ ω₂ => ω'.1) μ := Integrable.of_integral_ne_zero hμ.ne'
  have hω₂ : 0 < ω₂ := by
    by_contra hle
    have : ∫ ω', ω'.1 ∂μ ≤ 0 := integral_nonpos fun ω' => ω'.2.2.trans (not_lt.1 hle)
    linarith
  have hgY : g P.1 < g (P.1 + ω₂) := by
    rw [hgdef, liftS_of_mem _ (mem_Ici.2 hY0), liftS_of_mem _ (mem_Ici.2 (by linarith))]
    exact inv_strictMono h hv ω (show (⟨P.1, _⟩ : Ici (0 : ℝ)) < ⟨P.1 + ω₂, _⟩ from
      (by change P.1 < P.1 + ω₂; linarith))
  set κ := (g (P.1 + ω₂) - g P.1) / ω₂ with hκdef
  have hκ : 0 < κ := div_pos (sub_pos.2 hgY) hω₂
  have hchord : ∀ t, 0 ≤ t → t ≤ ω₂ → t * κ ≤ g (P.1 + t) - g P.1 := by
    intro t ht0 ht1
    have hb0 : 0 ≤ t / ω₂ := div_nonneg ht0 hω₂.le
    have hb1 : t / ω₂ ≤ 1 := (div_le_one hω₂).2 ht1
    have hc := hg.2 (mem_Ici.2 hY0) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ P.1 + ω₂))
      (sub_nonneg.2 hb1) hb0 (by ring)
    have harg : (1 - t / ω₂) • P.1 + (t / ω₂) • (P.1 + ω₂) = P.1 + t := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [harg, smul_eq_mul, smul_eq_mul] at hc
    have e : t * κ = t / ω₂ * (g (P.1 + ω₂) - g P.1) := by rw [hκdef]; ring
    nlinarith
  have hslope : Tendsto (fun n => c n / n) (𝓝[>] 0) (𝓝 0) := by
    have := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).1 hc0.Ioi_of_Ici
    refine this.congr' (eventually_nhdsWithin_of_forall fun n _ => ?_)
    rw [slope_def_field, h.c_zero, sub_zero, sub_zero]
  have hδ : 0 < β * κ * ∫ ω', ω'.1 ∂μ := mul_pos (mul_pos h.β_pos hκ) hμ
  have hNb : 0 < Nbar := by
    rcases h.N_nonneg.eq_or_lt with hN0 | hN0
    · have := h.N_big
      rw [← hN0, h.c_zero] at this
      have : 0 ≤ Ubar / (1 - β) := div_nonneg h.Ubar_nonneg (by linarith [h.β_lt])
      linarith
    · exact hN0
  obtain ⟨n, hn1, hn2⟩ := ((hslope.eventually (gt_mem_nhds hδ)).and
    (Ioo_mem_nhdsGT (lt_min one_pos hNb))).exists
  have hn0 : 0 < n := hn2.1
  have hn1' : c n < β * κ * (∫ ω', ω'.1 ∂μ) * n := (div_lt_iff₀ hn0).1 hn1
  have hfeas : ((P.1, n) : ℝ × ℝ) ∈ invΓ Nbar (x, ω) :=
    ⟨hP.1.1, hn0.le, hn2.2.le.trans (min_le_right _ _)⟩
  have hle := (inv_max h hv (x, ω)).2 _ hfeas
  have e := hP.2
  rw [inv_rhs, inv_integral_eq h hv ω x (p := (P.1, n)) hY0 hn0.le] at hle
  rw [inv_rhs, inv_integral_eq h hv ω x hY0 hP.1.2.1] at e
  rw [← h0] at e
  simp only [zero_mul, add_zero, integral_const, probReal_univ, one_smul, h.c_zero] at e
  have hI : ∫ ω', (g P.1 + n * κ * ω'.1) ∂μ = g P.1 + n * κ * ∫ ω', ω'.1 ∂μ := by
    rw [integral_add (integrable_const _) (hiw.const_mul _), integral_const, integral_const_mul,
      probReal_univ, one_smul]
  have hlow : g P.1 + n * κ * ∫ ω', ω'.1 ∂μ ≤ ∫ ω', g (P.1 + n * ω'.1) ∂μ := by
    rw [← hI]
    refine integral_mono (f := fun ω' : Icc ω₁ ω₂ => g P.1 + n * κ * ω'.1)
      ((integrable_const (g P.1)).add (hiw.const_mul (n * κ)))
      (inv_integrable h hv ω (p := (P.1, n)) hY0 hn0.le) fun ω' => ?_
    have hw : 0 ≤ ω'.1 := h.ω_nonneg.trans ω'.2.1
    have hnw : n * ω'.1 ≤ ω₂ := by
      have := mul_le_mul_of_nonneg_right (hn2.2.le.trans (min_le_left _ _)) hw
      linarith [ω'.2.2]
    have := hchord (n * ω'.1) (mul_nonneg hn0.le hw) hnw
    change g P.1 + n * κ * ω'.1 ≤ g (P.1 + n * ω'.1)
    nlinarith
  dsimp only at hle e
  rw [← hgdef] at hle e
  nlinarith [mul_le_mul_of_nonneg_left hlow h.β_pos.le]

/-- If `Y(x₁) = Y(x₂) = 0`, then `N(x₁) = N(x₂)`: with nothing stored, `n` maximizes
`−c(n) + β E v(nω′)`, which does not involve the stock. -/
theorem inv_N_eq_of_Y_zero (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v) {x₁ x₂ : Ici (0 : ℝ)}
    (ω : Icc ω₁ ω₂) {P₁ P₂ : ℝ × ℝ} (hP₁ : P₁ ∈ policy (invModel μ U H c β Nbar) v (x₁, ω))
    (hP₂ : P₂ ∈ policy (invModel μ U H c β Nbar) v (x₂, ω)) (hY₁ : P₁.1 = 0) (hY₂ : P₂.1 = 0) :
    P₁.2 = P₂.2 := by
  obtain ⟨Y₁, N₁⟩ := P₁
  obtain ⟨Y₂, N₂⟩ := P₂
  dsimp only at hY₁ hY₂ ⊢
  subst hY₁ hY₂
  have hfeas₁ : ((0 : ℝ), N₂) ∈ invΓ Nbar (x₁, ω) := ⟨⟨le_rfl, x₁.2⟩, hP₂.1.2⟩
  have hfeas₂ : ((0 : ℝ), N₁) ∈ invΓ Nbar (x₂, ω) := ⟨⟨le_rfl, x₂.2⟩, hP₁.1.2⟩
  have E : ∀ p : ℝ × ℝ, ∫ ω', v (invφ (x₂, p, ω'), ω') ∂μ = ∫ ω', v (invφ (x₁, p, ω'), ω') ∂μ :=
    fun _ => rfl
  have hopt : ((0 : ℝ), N₁) ∈ policy (invModel μ U H c β Nbar) v (x₂, ω) := by
    refine ⟨hfeas₂, le_antisymm ?_ ((inv_max h hv (x₂, ω)).2 _ hfeas₂)⟩
    have l₁ := (inv_max h hv (x₁, ω)).2 _ hfeas₁
    have e₁ := hP₁.2
    have e₂ := hP₂.2
    rw [inv_rhs] at l₁ e₁ e₂ ⊢
    rw [E] at e₂ ⊢
    dsimp only at l₁ e₁ e₂ ⊢
    linarith
  have hpol := (inv_policy h hv).2
  have heq := (inv_policy h hv).1.unique (x₂, ω) _ (hpol (x₂, ω) ▸ hopt) _ (hpol (x₂, ω) ▸ hP₂)
  exact congrArg Prod.snd heq

/-- If `x₁ < x₂`, `Y(x₁) < Y(x₂)` and `N(x₁) > 0`, then `N(x₂) < N(x₁)` (when `U` and `c` are
differentiable on `(0, ∞)` and `E ω′ > 0`). If `N(x₁) = N(x₂) = N > 0`, (4) holds with equality at
both stocks, but `ω′ v′(Y + Nω′)` is strictly smaller at `Y(x₂)` wherever `ω′ > 0`. -/
theorem inv_N_strict (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q)
    (hcd : ∀ n, 0 < n → DifferentiableAt ℝ c n) (hμ : 0 < ∫ ω', ω'.1 ∂μ)
    {x₁ x₂ : Ici (0 : ℝ)} (hx : x₁.1 < x₂.1) (ω : Icc ω₁ ω₂) {P₁ P₂ : ℝ × ℝ}
    (hP₁ : P₁ ∈ policy (invModel μ U H c β Nbar) v (x₁, ω))
    (hP₂ : P₂ ∈ policy (invModel μ U H c β Nbar) v (x₂, ω)) (hY : P₁.1 < P₂.1)
    (hN : 0 < P₁.2) : P₂.2 < P₁.2 := by
  obtain ⟨-, hN'⟩ := ex_10_5e h hv hx.le ω hP₁ hP₂
  rcases hN'.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hN₂ : 0 < P₂.2 := heq ▸ hN
  have f₁ := inv_foc_n h hv hUd hP₁ hN (hcd _ hN)
  have f₂ := inv_foc_n h hv hUd hP₂ hN₂ (hcd _ hN₂)
  rw [heq] at f₂
  have i₁ := (inv_hasDerivAt_En h hv hUd ω hP₁.1.1.1 hN).1
  have i₂ := (inv_hasDerivAt_En h hv hUd ω hP₂.1.1.1 hN).1
  have hiw : Integrable (fun ω' : Icc ω₁ ω₂ => ω'.1) μ := Integrable.of_integral_ne_zero hμ.ne'
  have hpt : ∀ ω' : Icc ω₁ ω₂, 0 < ω'.1 →
      ω'.1 * deriv (liftS fun x => v (x, ω)) (P₂.1 + P₁.2 * ω'.1) <
        ω'.1 * deriv (liftS fun x => v (x, ω)) (P₁.1 + P₁.2 * ω'.1) := fun ω' hw => by
    have a := mul_pos hN hw
    have b : (0 : ℝ) ≤ P₁.1 := hP₁.1.1.1
    exact mul_lt_mul_of_pos_left ((inv_deriv_strictAnti h hv hUd ω) (mem_Ioi.2 (by linarith))
      (mem_Ioi.2 (by linarith)) (by linarith)) hw
  have hnn : (0 : Icc ω₁ ω₂ → ℝ) ≤ fun ω' =>
      ω'.1 * deriv (liftS fun x => v (x, ω)) (P₁.1 + P₁.2 * ω'.1) -
        ω'.1 * deriv (liftS fun x => v (x, ω)) (P₂.1 + P₁.2 * ω'.1) := fun ω' => by
    rcases (h.ω_nonneg.trans ω'.2.1 : 0 ≤ ω'.1).eq_or_lt with hw | hw
    · simp [← hw]
    · have := hpt ω' hw
      simp only [Pi.zero_apply]
      linarith
  have hpos : 0 < ∫ ω', (ω'.1 * deriv (liftS fun x => v (x, ω)) (P₁.1 + P₁.2 * ω'.1) -
      ω'.1 * deriv (liftS fun x => v (x, ω)) (P₂.1 + P₁.2 * ω'.1)) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hnn (i₁.sub i₂)]
    have hsupp := (integral_pos_iff_support_of_nonneg
      (fun ω' => h.ω_nonneg.trans ω'.2.1) hiw).1 hμ
    refine hsupp.trans_le (measure_mono fun ω' hω' => ?_)
    rw [Function.mem_support] at hω' ⊢
    have hw : 0 < ω'.1 := lt_of_le_of_ne (h.ω_nonneg.trans ω'.2.1) (Ne.symm hω')
    have := hpt ω' hw
    exact (sub_pos.2 this).ne'
  rw [integral_sub i₁ i₂] at hpos
  nlinarith [mul_pos h.β_pos hpos]

/-- **Exercise 10.5g**, corrected. Let `U`, `φ` and `c` be differentiable on `(0, ∞)`, with
`c′(0) = 0` from the right, and let `E ω′ > 0`. For `x₁ < x₂`: `N(x₁), N(x₂) > 0`; if
`Y(x₂) > 0` then `N(x₂) < N(x₁)`; and if `Y(x₂) = 0` then `N(x₂) = N(x₁)`. The book's
unconditional `N(x₂) < N(x₁)` fails on the range where nothing is stored
(`ex_10_5g_counterexample`). -/
theorem ex_10_5g (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q)
    (hHd : ∀ y, 0 < y → DifferentiableAt ℝ H y) (hcd : ∀ n, 0 < n → DifferentiableAt ℝ c n)
    (hc0 : HasDerivWithinAt c 0 (Ici 0) 0) (hμ : 0 < ∫ ω', ω'.1 ∂μ) {x₁ x₂ : Ici (0 : ℝ)}
    (hx : x₁.1 < x₂.1) (ω : Icc ω₁ ω₂) {P₁ P₂ : ℝ × ℝ}
    (hP₁ : P₁ ∈ policy (invModel μ U H c β Nbar) v (x₁, ω))
    (hP₂ : P₂ ∈ policy (invModel μ U H c β Nbar) v (x₂, ω)) :
    0 < P₁.2 ∧ 0 < P₂.2 ∧ (0 < P₂.1 → P₂.2 < P₁.2) ∧ (P₂.1 = 0 → P₂.2 = P₁.2) := by
  have hN₁ := inv_N_pos h hv hc0 hμ hP₁
  refine ⟨hN₁, inv_N_pos h hv hc0 hμ hP₂, fun hY₂ => ?_, fun hY₂ => ?_⟩
  · rcases ex_10_5e_strict h hv hUd hHd hx ω hP₁ hP₂ with hY | hY
    · exact inv_N_strict h hv hUd hcd hμ hx ω hP₁ hP₂ hY hN₁
    · linarith [hY.2]
  · have hY₁ : P₁.1 = 0 :=
      le_antisymm ((ex_10_5e h hv hx.le ω hP₁ hP₂).1.trans hY₂.le) hP₁.1.1.1
    exact (inv_N_eq_of_Y_zero h hv ω hP₁ hP₂ hY₁ hY₂).symm

/-- If `U′ ≤ L` on `(0, ∞)`, then `v′ ≤ L` on `(0, ∞)`, by the envelope condition. -/
theorem inv_deriv_le (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q) {L : ℝ}
    (hL : ∀ q, 0 < q → deriv U q ≤ L) (ω : Icc ω₁ ω₂) {z : ℝ} (hz : 0 < z) :
    deriv (liftS fun x => v (x, ω)) z ≤ L := by
  obtain ⟨p, hp, hval⟩ := (inv_max h hv (⟨z, mem_Ici.2 hz.le⟩, ω)).1
  have hP : p ∈ policy (invModel μ U H c β Nbar) v (⟨z, mem_Ici.2 hz.le⟩, ω) := ⟨hp, hval⟩
  rw [(inv_hasDerivAt_pos h hv hUd hP hz).deriv]
  exact hL _ (sub_pos.2 (inv_Y_lt h hv hP hz))

/-- If `U′ ≤ L` on `(0, ∞)`, then `v(y + t) − v(y) ≤ L t` for `y, t ≥ 0`. -/
theorem inv_sub_le (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q) {L : ℝ}
    (hL : ∀ q, 0 < q → deriv U q ≤ L) (ω : Icc ω₁ ω₂) {y t : ℝ} (hy : 0 ≤ y) (ht : 0 ≤ t) :
    liftS (fun x => v (x, ω)) (y + t) - liftS (fun x => v (x, ω)) y ≤ L * t := by
  set g := liftS (fun x => v (x, ω)) with hgdef
  have hg := concaveOn_liftS (inv_strictConcave h hv ω).isConcaveS
  have hslope : ∀ s u, 0 < s → s < u → g u - g s ≤ L * (u - s) := fun s u hs hsu => by
    have := hg.slope_le_deriv (mem_Ici.2 hs.le) (mem_Ici.2 (by linarith)) hsu
      (inv_differentiableAt h hv hUd ω hs)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hsu)] at this
    nlinarith [inv_deriv_le (μ := μ) h hv hUd hL ω hs]
  rcases ht.eq_or_lt with ht0 | ht0
  · rw [← ht0]; simp
  rcases hy.eq_or_lt with hy0 | hy0
  · rw [← hy0, zero_add]
    have hcon : ContinuousOn g (Ici 0) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (Ici (0 : ℝ)).domRestrict g = fun x => v (x, ω) := funext fun x => by
        change g x.1 = v (x, ω)
        rw [hgdef, liftS_of_mem _ x.2]
      rw [this]
      exact v.continuous.comp (continuous_id.prodMk continuous_const)
    have hlim : Tendsto (fun s => g t - g s - L * (t - s)) (𝓝[>] 0)
        (𝓝 (g t - g 0 - L * (t - 0))) :=
      ((tendsto_const_nhds.sub ((hcon 0 (mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self).tendsto).sub
        (tendsto_const_nhds.mul (tendsto_const_nhds.sub
          (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id))))
    have := le_of_tendsto (b := 0) hlim (by
      filter_upwards [Ioo_mem_nhdsGT ht0] with s hs
      have := hslope s t hs.1 hs.2
      linarith)
    linarith
  · have := hslope y (y + t) hy0 (by linarith)
    rw [add_sub_cancel_left] at this
    exact this

/-- **Nothing is stored at small stocks.** Let `U′ ≤ L` on `(0, ∞)` and `φ` be differentiable on
`(0, ∞)`. If `U′(x) > βL`, then `Y(x) = 0`: were `Y(x) > 0`, (3) would give
`U′(x) ≤ U′[x − Y(x)] + φ′[Y(x)] = βE v′ ≤ βL`. Under the book's assumptions `U′ = D` is
bounded by `D(0)` and `D(x) → D(0) > βD(0)` as `x → 0`, so `Y = 0` near `0`. -/
theorem inv_Y_eq_zero (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q)
    (hHd : ∀ y, 0 < y → DifferentiableAt ℝ H y) {L : ℝ} (hL : ∀ q, 0 < q → deriv U q ≤ L)
    {x : Ici (0 : ℝ)} {ω : Icc ω₁ ω₂} {P : ℝ × ℝ}
    (hP : P ∈ policy (invModel μ U H c β Nbar) v (x, ω)) (hx : 0 < x.1)
    (hxL : β * L < deriv U x.1) : P.1 = 0 := by
  rcases (hP.1.1.1 : 0 ≤ P.1).eq_or_lt with h0 | hpos
  · exact h0.symm
  exfalso
  have foc := inv_foc_y h hv hUd hP hpos (hHd _ hpos)
  have hYx := inv_Y_lt h hv hP hx
  have hU := (h.U_conc.concaveOn.subset Ioi_subset_Ici_self (convex_Ioi 0)).antitoneOn_deriv
    (fun q hq => hUd q hq) (mem_Ioi.2 (sub_pos.2 hYx)) (mem_Ioi.2 hx) (by linarith)
  have hH : 0 ≤ deriv H P.1 := by
    have hs := h.H_conv.convexOn.slope_le_deriv (mem_Ici.2 le_rfl) (mem_Ici.2 hpos.le) hpos
      (hHd _ hpos)
    have hHp := h.H_mono (mem_Ici.2 le_rfl) (mem_Ici.2 hpos.le) hpos
    rw [slope_def_field, h.H_zero, sub_zero, sub_zero] at hs
    rw [h.H_zero] at hHp
    linarith [div_pos hHp hpos]
  have hi := (inv_hasDerivAt_Ey h hv hUd ω hpos hP.1.2.1).1
  have hint : ∫ ω', deriv (liftS fun x => v (x, ω)) (P.1 + P.2 * ω'.1) ∂μ ≤ L := by
    have := integral_mono hi (integrable_const L) fun ω' => inv_deriv_le h hv hUd hL ω
      (by have := mul_nonneg hP.1.2.1 (h.ω_nonneg.trans ω'.2.1); linarith)
    simpa using this
  nlinarith [mul_le_mul_of_nonneg_left hint h.β_pos.le]

/-- **Exercise 10.5g with `c′(0) > 0`.** If `U′ ≤ L` on `(0, ∞)` and the input cost is steep at
`0`, `c(n) ≥ κ n` with `κ > βLω₂`, then `N(x) = 0` for every `x`: the marginal product of the
input, at most `βLω₂`, never covers its marginal cost. So `N(x) > 0` fails, and with it the strict
decrease of `N`. -/
theorem inv_N_eq_zero (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (hUd : ∀ q, 0 < q → DifferentiableAt ℝ U q) {L κ : ℝ}
    (hL : ∀ q, 0 < q → deriv U q ≤ L) (hκ : β * L * ω₂ < κ) (hc : ∀ n, 0 ≤ n → κ * n ≤ c n)
    {x : Ici (0 : ℝ)} {ω : Icc ω₁ ω₂} {P : ℝ × ℝ}
    (hP : P ∈ policy (invModel μ U H c β Nbar) v (x, ω)) : P.2 = 0 := by
  rcases (hP.1.2.1 : 0 ≤ P.2).eq_or_lt with h0 | hpos
  · exact h0.symm
  exfalso
  set g := liftS (fun x => v (x, ω)) with hgdef
  have hY0 : 0 ≤ P.1 := hP.1.1.1
  have hL0 : 0 ≤ L := (inv_deriv_pos h hv hUd ω one_pos).le.trans
    (inv_deriv_le (μ := μ) h hv hUd hL ω one_pos)
  have hfeas : ((P.1, 0) : ℝ × ℝ) ∈ invΓ Nbar (x, ω) := ⟨hP.1.1, le_rfl, h.N_nonneg⟩
  have hle := (inv_max h hv (x, ω)).2 _ hfeas
  have e := hP.2
  rw [inv_rhs, inv_integral_eq h hv ω x (p := (P.1, 0)) hY0 le_rfl] at hle
  rw [inv_rhs, inv_integral_eq h hv ω x hY0 hP.1.2.1] at e
  dsimp only at hle e
  simp only [zero_mul, add_zero, integral_const, probReal_univ, one_smul, h.c_zero] at hle
  rw [← hgdef] at hle e
  have hup : ∫ ω', g (P.1 + P.2 * ω'.1) ∂μ ≤ g P.1 + L * P.2 * ω₂ := by
    have := integral_mono (inv_integrable h hv ω (p := P) hY0 hP.1.2.1)
      (integrable_const (g P.1 + L * P.2 * ω₂)) fun ω' => by
        have hw : 0 ≤ ω'.1 := h.ω_nonneg.trans ω'.2.1
        have h1 := inv_sub_le h hv hUd hL ω hY0 (mul_nonneg hP.1.2.1 hw)
        have h2 := mul_le_mul_of_nonneg_left ω'.2.2 (mul_nonneg hL0 hP.1.2.1)
        change g (P.1 + P.2 * ω'.1) ≤ g P.1 + L * P.2 * ω₂
        nlinarith
    simpa using this
  have hcn := hc P.2 hP.1.2.1
  nlinarith [mul_le_mul_of_nonneg_left hup h.β_pos.le, mul_lt_mul_of_pos_right hκ hpos]

end StokeyLucasPrescott.StochasticApplications
