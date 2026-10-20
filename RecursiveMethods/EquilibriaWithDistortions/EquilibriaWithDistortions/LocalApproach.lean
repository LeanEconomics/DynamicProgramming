/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.Brouwer
import EquilibriaWithDistortions.IndirectApproach

/-!
# A local approach based on first-order conditions: the setting

SLP §18.2, pp. 547–549. One-sector growth with a flat tax `θ` on capital income whose proceeds
are thrown away. After-tax income is `ψ(k) = f(k) − θ k f′(k)` (`psi`), and an equilibrium is a
savings function `g` with `F[k, g(k), g²(k)] = 0` (§18.2 (4)), where (§18.2 (3), `Feq`)
`F(x, y, z) = U′[ψ(x) − y] − β(1 − θ) f′(y) U′[ψ(y) − z]`.

* `Assumption18_1` (**Assumption 18.1**, pp. 547–548). `U` and `f` are functions `ℝ → ℝ` that
  are `C²` on all of `ℝ`; the book's properties on `[0, ∞)` are imposed on `Ici 0`. (A `C²`
  function on `[0, ∞)` extends to a `C²` function on `ℝ`, so nothing is lost.) Part (d)'s
  `lim_{k→0} f′(k)` equals `f′(0)` by continuity (`tendsto_deriv_f_zero`).
* Derived facts (F1)–(F4): `U′ > 0` and `f′ > 0` on `[0, ∞)` (`deriv_U_pos`, `deriv_f_pos`),
  `f′` strictly decreasing (`deriv_f_strictAnti`), `ψ(k̄) = k̄` (`psi_kbar`),
  `ψ(k) ≥ k` on `K = [0, k̄]` (`le_psi`), `β(1 − θ) f′(k̄) < 1` (`euler_kbar_lt`), and a unique
  `k* ∈ (0, k̄)` with `β(1 − θ) f′(k*) = 1` (`exists_unique_kstar`).
* **Proposition 18.1** (`prop_18_1`, p. 548): a continuous `g : K → K` solving (4) has exactly
  one fixed point, namely `k*`. Existence of a fixed point is Brouwer's theorem
  (`brouwer`, Theorem 17.3).
* The partial derivatives `F₁, F₂, F₃` (`F1f`, `F2f`, `F3f`, with `hasDerivAt_Feq_x`, `_y`, `_z`)
  and their values `F₁*, F₂*, F₃*` at `(k*, k*, k*)` (§18.2 (6a)–(6c), `F1s`, `F2s`, `F3s`,
  `F1f_star`, `F2f_star`, `F3f_star`).
* `LocalHyp`: the hypotheses used by the local analysis, including the added `U″(c*) < 0`,
  `f″(k*) < 0`; `Assumption18_1.localHyp`.
* The characteristic polynomial `P(λ) = F₁* + F₂* λ + F₃* λ²` (`charPoly`), its roots
  `λ* ∈ (0, 1)` (`lamStar`) and `λ₂ > 1` (`lamTwo`), with `P > 0` on `(λ*, λ₂)` (`charPoly_roots`,
  p. 549), `F₂* > 0`, `H₁* = −F₁*/F₂* > 0`, `H₂* = −F₃*/F₂* > 0`, `H₁* + H₂* < 1`, and
  `H₁* + H₂* λ² < λ` for `λ ∈ (λ*, 1)`.

**Corrections.**
* (Assumption 18.1 vs. Assumption 18.2, NOTE 18.3-A.) Assumption 18.1(b) makes `U` `C²` on
  `[0, ∞)`, so `U′(0)` is finite and the Inada condition `U′(0⁺) = ∞` of Assumption 18.2 fails
  (`Assumption18_1.not_inada`); §18.3 must read `U` as `C²` on `(0, ∞)` only.
* (NOTE 18.2-A, p. 549.) Existence of `k*` uses Assumption 18.1(e) as well as (d)
  (`euler_kbar_lt`); and dividing by `U′` uses `U′ > 0` (`deriv_U_pos`). Verified;
  `exists_unique_kstar` and `prop_18_1` use both.
* (NOTE 18.2-B, p. 549.) The sign claims `P(0) < 0`, `P(1) > 0`, `lim P = −∞` need
  `U″(c*) < 0` and `f″(k*) < 0`, which strict concavity does not give:
  `strictConcave_deriv2_zero_counterexample` is a `C²`, strictly increasing, strictly concave
  `U` with `U″(c₀) = 0` at any prescribed `c₀`. If `U″(c*) = 0` then `F₁* = F₃* = 0` and
  `P(0) = 0` (`charPoly_degenerate_U`); if `f″(k*) = 0` then `P(1) = 0`
  (`charPoly_degenerate_f`). The hypotheses `U″(c*) < 0` and `f″(k*) < 0` are added
  (`LocalHyp`).
* (NOTE 18.2-C, p. 549.) `P(F₁*/F₃*) = (F₁*/F₃*) P(1) > 0` (`charPoly_F1_div_F3`), so
  `F₁*/F₃*` lies strictly between the roots: `λ* < F₁*/F₃* < λ₂`; since `F₁*/F₃* > 1`, the
  inequality `λ* < F₁*/F₃*` is the trivial part. Verified (`charPoly_roots`).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- After-tax income `ψ(k) = f(k) − θ k f′(k)`. -/
noncomputable def psi (θ : ℝ) (f : ℝ → ℝ) (k : ℝ) : ℝ := f k - θ * k * deriv f k

/-- The function `F(x, y, z) = U′[ψ(x) − y] − β(1 − θ) f′(y) U′[ψ(y) − z]` of §18.2 (3). -/
noncomputable def Feq (β θ : ℝ) (U f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv U (psi θ f x - y) - β * (1 - θ) * deriv f y * deriv U (psi θ f y - z)

/-- **Assumption 18.1** (pp. 547–548), with `K = [0, k̄]`.
a. `0 < β < 1`; b. `U` is `C²`, strictly increasing and strictly concave on `[0, ∞)`;
c. `0 < θ < 1`; d. `f` is `C²`, nonnegative, strictly increasing and strictly concave on
`[0, ∞)`, `f(0) > 0` and `f′(0) > 1/[β(1 − θ)]`; e. `ψ(k) − k > 0` on `(0, k̄)` and `< 0` on
`(k̄, ∞)`. -/
structure Assumption18_1 (β θ : ℝ) (U f : ℝ → ℝ) (kbar : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  U_contDiff : ContDiff ℝ 2 U
  U_strictMono : StrictMonoOn U (Ici 0)
  U_strictConcave : StrictConcaveOn ℝ (Ici 0) U
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  f_contDiff : ContDiff ℝ 2 f
  f_nonneg : ∀ k, 0 ≤ k → 0 ≤ f k
  f_strictMono : StrictMonoOn f (Ici 0)
  f_strictConcave : StrictConcaveOn ℝ (Ici 0) f
  f_zero_pos : 0 < f 0
  deriv_f_zero : 1 / (β * (1 - θ)) < deriv f 0
  kbar_pos : 0 < kbar
  psi_gt : ∀ k ∈ Ioo 0 kbar, k < psi θ f k
  psi_lt : ∀ k, kbar < k → psi θ f k < k

/-! ### Smoothness consequences of `C²` -/

/-- A `C²` function is differentiable. -/
theorem differentiable_of_C2 {u : ℝ → ℝ} (h : ContDiff ℝ 2 u) : Differentiable ℝ u :=
  h.differentiable (by norm_num)

/-- The derivative of a `C²` function is differentiable. -/
theorem differentiable_deriv_of_C2 {u : ℝ → ℝ} (h : ContDiff ℝ 2 u) :
    Differentiable ℝ (deriv u) :=
  h.differentiable_deriv_two

/-- The derivative of a `C²` function is continuous. -/
theorem continuous_deriv_of_C2 {u : ℝ → ℝ} (h : ContDiff ℝ 2 u) : Continuous (deriv u) :=
  (differentiable_deriv_of_C2 h).continuous

/-- The second derivative of a `C²` function is continuous. -/
theorem continuous_deriv2_of_C2 {u : ℝ → ℝ} (h : ContDiff ℝ 2 u) :
    Continuous (deriv (deriv u)) :=
  ((contDiff_succ_iff_deriv (n := 1)).1 h).2.2.continuous_deriv_one

/-- `ψ′(x) = (1 − θ) f′(x) − θ x f″(x)`. -/
noncomputable def dpsi (θ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - θ) * deriv f x - θ * x * deriv (deriv f) x

/-- `ψ` has derivative `ψ′ = dpsi`. -/
theorem hasDerivAt_psi {θ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (psi θ f) (dpsi θ f x) x := by
  have h1 := (differentiable_of_C2 hf x).hasDerivAt
  have h2 := (differentiable_deriv_of_C2 hf x).hasDerivAt
  have h3 := ((hasDerivAt_id' x).const_mul θ).mul h2
  exact (h1.sub h3).congr_deriv (by simp only [dpsi]; ring)

/-- `ψ` is continuous. -/
theorem continuous_psi {θ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (psi θ f) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_psi hf x).continuousAt

/-! ### Derived facts (F1)–(F4) -/

/-- A strictly increasing function, concave and differentiable on `[0, ∞)`, has a positive
derivative on `[0, ∞)` (fact (F1)). -/
theorem deriv_pos_of_strictMono_concave {u : ℝ → ℝ} (hm : StrictMonoOn u (Ici 0))
    (hc : ConcaveOn ℝ (Ici 0) u) (hd : Differentiable ℝ u) {c : ℝ} (h0 : 0 ≤ c) :
    0 < deriv u c := by
  by_contra hneg
  push Not at hneg
  have h1 := concave_le_tangent hc (by linarith : (0 : ℝ) ≤ c + 1) h0 (hd c)
  have h2 := hm (mem_Ici.2 h0) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c + 1))
    (by linarith : c < c + 1)
  have e : c + 1 - c = 1 := by ring
  rw [e, mul_one] at h1
  linarith

/-- (F1) `U′ > 0` on `[0, ∞)`. -/
theorem Assumption18_1.deriv_U_pos {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) {c : ℝ} (hc : 0 ≤ c) : 0 < deriv U c :=
  deriv_pos_of_strictMono_concave A.U_strictMono A.U_strictConcave.concaveOn
    (differentiable_of_C2 A.U_contDiff) hc

/-- (F1) `f′ > 0` on `[0, ∞)`. -/
theorem Assumption18_1.deriv_f_pos {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) {k : ℝ} (hk : 0 ≤ k) : 0 < deriv f k :=
  deriv_pos_of_strictMono_concave A.f_strictMono A.f_strictConcave.concaveOn
    (differentiable_of_C2 A.f_contDiff) hk

/-- (F1) `f′` is strictly decreasing on `[0, ∞)`. -/
theorem Assumption18_1.deriv_f_strictAnti {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) : StrictAntiOn (deriv f) (Ici 0) :=
  A.f_strictConcave.strictAntiOn_deriv fun x _ => differentiable_of_C2 A.f_contDiff x

/-- (F1) `U′` is strictly decreasing on `[0, ∞)`. -/
theorem Assumption18_1.deriv_U_strictAnti {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) : StrictAntiOn (deriv U) (Ici 0) :=
  A.U_strictConcave.strictAntiOn_deriv fun x _ => differentiable_of_C2 A.U_contDiff x

/-- Part (d)'s `lim_{k→0} f′(k)` is `f′(0)`: `f′` is continuous. -/
theorem Assumption18_1.tendsto_deriv_f_zero {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) :
    Tendsto (deriv f) (𝓝[>] 0) (𝓝 (deriv f 0)) :=
  ((continuous_deriv_of_C2 A.f_contDiff).tendsto 0).mono_left nhdsWithin_le_nhds

/-- **Assumption 18.1 excludes the Inada condition of Assumption 18.2** (NOTE 18.3-A): since `U`
is `C²` up to `0`, `U′(c) → U′(0) < ∞` as `c → 0⁺`, so `U′(0⁺) = ∞` fails. (Relevant for §18.3,
which assumes both.) -/
theorem Assumption18_1.not_inada {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) : ¬ Tendsto (deriv U) (𝓝[>] 0) atTop := by
  have hlim : Tendsto (deriv U) (𝓝[>] 0) (𝓝 (deriv U 0)) :=
    ((continuous_deriv_of_C2 A.U_contDiff).tendsto 0).mono_left nhdsWithin_le_nhds
  exact hlim.not_tendsto (disjoint_nhds_atTop _)

/-- (F2) `ψ(k̄) = k̄`. -/
theorem Assumption18_1.psi_kbar {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) : psi θ f kbar = kbar := by
  have hc : Continuous fun k => psi θ f k - k := (continuous_psi A.f_contDiff).sub continuous_id
  have hle : psi θ f kbar - kbar ≤ 0 := by
    have hlim : Tendsto (fun k => psi θ f k - k) (𝓝[>] kbar) (𝓝 (psi θ f kbar - kbar)) :=
      (hc.tendsto kbar).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with k hk
    linarith [A.psi_lt k hk]
  have hge : 0 ≤ psi θ f kbar - kbar := by
    have hlim : Tendsto (fun k => psi θ f k - k) (𝓝[<] kbar) (𝓝 (psi θ f kbar - kbar)) :=
      (hc.tendsto kbar).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT A.kbar_pos] with k hk
    linarith [A.psi_gt k hk]
  linarith

/-- (F2) `k ≤ ψ(k)` on `K = [0, k̄]`: stationary consumption is nonnegative on `K`. -/
theorem Assumption18_1.le_psi {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) {k : ℝ} (hk : k ∈ Icc 0 kbar) : k ≤ psi θ f k := by
  rcases eq_or_lt_of_le hk.1 with h | h
  · subst h
    simp only [psi, mul_zero, zero_mul, sub_zero]
    exact A.f_zero_pos.le
  rcases eq_or_lt_of_le hk.2 with h' | h'
  · rw [h', A.psi_kbar]
  · exact (A.psi_gt k ⟨h, h'⟩).le

/-- (F3) `f(k) ≥ f(0) + k f′(k)` on `[0, ∞)`, hence `ψ(k) > (1 − θ) k f′(k)`. -/
theorem Assumption18_1.psi_gt_mul {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) {k : ℝ} (hk : 0 ≤ k) :
    (1 - θ) * k * deriv f k < psi θ f k := by
  have h := concave_le_tangent A.f_strictConcave.concaveOn le_rfl hk
    (differentiable_of_C2 A.f_contDiff k)
  have := A.f_zero_pos
  simp only [psi]
  nlinarith

/-- (F3) `β(1 − θ) f′(k̄) < 1`. -/
theorem Assumption18_1.euler_kbar_lt {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) : β * (1 - θ) * deriv f kbar < 1 := by
  have h := A.psi_gt_mul A.kbar_pos.le
  rw [A.psi_kbar] at h
  have h1 : (1 - θ) * deriv f kbar < 1 := by
    by_contra hc
    push Not at hc
    nlinarith [A.kbar_pos]
  have := A.beta_pos
  have := A.beta_lt_one
  have h2 : 0 < (1 - θ) * deriv f kbar :=
    mul_pos (by linarith [A.theta_lt_one]) (A.deriv_f_pos A.kbar_pos.le)
  nlinarith

/-- (F4) There is a unique `k* ∈ (0, k̄)` with `β(1 − θ) f′(k*) = 1` (§18.2 (5)); it is also the
unique solution in `[0, ∞)`. -/
theorem Assumption18_1.exists_unique_kstar {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) :
    ∃ ks ∈ Ioo 0 kbar, β * (1 - θ) * deriv f ks = 1 ∧
      ∀ k, 0 ≤ k → β * (1 - θ) * deriv f k = 1 → k = ks := by
  have hb : 0 < β * (1 - θ) := mul_pos A.beta_pos (by linarith [A.theta_lt_one])
  have h0 : 1 < β * (1 - θ) * deriv f 0 := by
    have := A.deriv_f_zero
    rw [div_lt_iff₀ hb] at this
    linarith
  have hcont : ContinuousOn (fun k => β * (1 - θ) * deriv f k) (Icc 0 kbar) :=
    (continuous_const.mul (continuous_deriv_of_C2 A.f_contDiff)).continuousOn
  obtain ⟨ks, hks, hval⟩ := intermediate_value_Icc' A.kbar_pos.le hcont
    ⟨A.euler_kbar_lt.le, h0.le⟩
  have hmono : StrictAntiOn (fun k => β * (1 - θ) * deriv f k) (Ici 0) :=
    fun x hx y hy hxy => mul_lt_mul_of_pos_left (A.deriv_f_strictAnti hx hy hxy) hb
  have hne0 : ks ≠ 0 := by
    rintro rfl
    simp only at hval
    linarith
  have hnek : ks ≠ kbar := by
    rintro rfl
    simp only at hval
    linarith [A.euler_kbar_lt]
  refine ⟨ks, ⟨lt_of_le_of_ne hks.1 (Ne.symm hne0), lt_of_le_of_ne hks.2 hnek⟩, hval,
    fun k hk hk1 => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hmono (mem_Ici.2 hk) (mem_Ici.2 hks.1) h
    simp only at this
    linarith
  · have := hmono (mem_Ici.2 hks.1) (mem_Ici.2 hk) h
    simp only at this
    linarith

/-- On the diagonal, `F(k, k, k) = U′[ψ(k) − k] (1 − β(1 − θ) f′(k))`. -/
theorem Feq_diag (β θ : ℝ) (U f : ℝ → ℝ) (k : ℝ) :
    Feq β θ U f k k k = deriv U (psi θ f k - k) * (1 - β * (1 - θ) * deriv f k) := by
  simp only [Feq]
  ring

/-! ### Proposition 18.1 -/

/-- **Proposition 18.1** (p. 548). Under Assumption 18.1, if `g` is continuous on
`K = [0, k̄]`, maps `K` into itself, and satisfies (4), `F[k, g(k), g²(k)] = 0` on `K`, then `g`
has exactly one fixed point in `K`, and it is the `k*` of (5): `β(1 − θ) f′(k*) = 1`.
The existence of a fixed point is Brouwer's theorem (Theorem 17.3). -/
theorem prop_18_1 {β θ kbar : ℝ} {U f g : ℝ → ℝ} (A : Assumption18_1 β θ U f kbar)
    (hgc : ContinuousOn g (Icc 0 kbar)) (hgm : MapsTo g (Icc 0 kbar) (Icc 0 kbar))
    (h4 : ∀ k ∈ Icc 0 kbar, Feq β θ U f k (g k) (g (g k)) = 0) :
    ∃ ks ∈ Ioo 0 kbar, β * (1 - θ) * deriv f ks = 1 ∧ g ks = ks ∧
      ∀ k ∈ Icc 0 kbar, g k = k → k = ks := by
  obtain ⟨ks, hks, hks1, hu⟩ := A.exists_unique_kstar
  have hfix : ∀ k ∈ Icc 0 kbar, g k = k → k = ks := by
    intro k hk hgk
    have h := h4 k hk
    rw [hgk, hgk, Feq_diag] at h
    have hpos : 0 < deriv U (psi θ f k - k) := A.deriv_U_pos (by linarith [A.le_psi hk])
    have h1 : 1 - β * (1 - θ) * deriv f k = 0 := by
      rcases mul_eq_zero.1 h with h2 | h2
      · exact absurd h2 hpos.ne'
      · exact h2
    exact hu k hk.1 (by linarith)
  obtain ⟨k, hk, hgk⟩ := brouwer isCompact_Icc (convex_Icc 0 kbar)
    ⟨0, ⟨le_rfl, A.kbar_pos.le⟩⟩ hgc hgm
  have hkks := hfix k hk hgk
  subst hkks
  exact ⟨k, hks, hks1, hgk, hfix⟩

/-! ### Partial derivatives of `F` and §18.2 (6a)–(6c) -/

/-- `F₁(x, y, z) = U″[ψ(x) − y] ψ′(x)`. -/
noncomputable def F1f (θ : ℝ) (U f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (deriv U) (psi θ f x - y) * dpsi θ f x

/-- `F₂(x, y, z) = −U″[ψ(x) − y] − β(1 − θ)(f″(y) U′[ψ(y) − z] + f′(y) U″[ψ(y) − z] ψ′(y))`. -/
noncomputable def F2f (β θ : ℝ) (U f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  -deriv (deriv U) (psi θ f x - y) - β * (1 - θ) * (deriv (deriv f) y * deriv U (psi θ f y - z) +
    deriv f y * (deriv (deriv U) (psi θ f y - z) * dpsi θ f y))

/-- `F₃(x, y, z) = β(1 − θ) f′(y) U″[ψ(y) − z]`. -/
noncomputable def F3f (β θ : ℝ) (U f : ℝ → ℝ) (y z : ℝ) : ℝ :=
  β * (1 - θ) * deriv f y * deriv (deriv U) (psi θ f y - z)

/-- `∂F/∂x = F₁`. -/
theorem hasDerivAt_Feq_x {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (x y z : ℝ) : HasDerivAt (fun x => Feq β θ U f x y z) (F1f θ U f x y) x := by
  have h1 := (differentiable_deriv_of_C2 hU (psi θ f x - y)).hasDerivAt
  have h2 := (hasDerivAt_psi (θ := θ) hf x).sub_const y
  exact (h1.comp x h2).sub_const (β * (1 - θ) * deriv f y * deriv U (psi θ f y - z))

/-- `∂F/∂y = F₂`. -/
theorem hasDerivAt_Feq_y {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (x y z : ℝ) : HasDerivAt (fun y => Feq β θ U f x y z) (F2f β θ U f x y z) y := by
  have h1 := (differentiable_deriv_of_C2 hU (psi θ f x - y)).hasDerivAt
  have h2 : HasDerivAt (fun y => psi θ f x - y) (-1) y := by
    simpa using (hasDerivAt_id' y).const_sub (psi θ f x)
  have h3 := h1.comp y h2
  have h4 := ((differentiable_deriv_of_C2 hf y).hasDerivAt).const_mul (β * (1 - θ))
  have h5 := (differentiable_deriv_of_C2 hU (psi θ f y - z)).hasDerivAt
  have h6 := h5.comp y ((hasDerivAt_psi (θ := θ) hf y).sub_const z)
  exact (h3.sub (h4.mul h6)).congr_deriv (by simp only [F2f, Function.comp_apply]; ring)

/-- `∂F/∂z = F₃`. -/
theorem hasDerivAt_Feq_z {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (x y z : ℝ) :
    HasDerivAt (fun z => Feq β θ U f x y z) (F3f β θ U f y z) z := by
  have h5 := (differentiable_deriv_of_C2 hU (psi θ f y - z)).hasDerivAt
  have h2 : HasDerivAt (fun z => psi θ f y - z) (-1) z := by
    simpa using (hasDerivAt_id' z).const_sub (psi θ f y)
  have h6 := h5.comp z h2
  have h7 := (h6.const_mul (β * (1 - θ) * deriv f y)).const_sub (deriv U (psi θ f x - y))
  exact h7.congr_deriv (by simp only [F3f]; ring)

/-- Stationary consumption `c* = ψ(k*) − k*`. -/
noncomputable def cstar (θ : ℝ) (f : ℝ → ℝ) (ks : ℝ) : ℝ := psi θ f ks - ks

/-- §18.2 (6a): `F₁* = U″(c*)[β⁻¹ − θ k* f″(k*)]`. -/
noncomputable def F1s (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  deriv (deriv U) (cstar θ f ks) * (β⁻¹ - θ * ks * deriv (deriv f) ks)

/-- §18.2 (6b): `F₂* = −U″(c*)[1 + β⁻¹ − θ k* f″(k*)] − β(1 − θ) f″(k*) U′(c*)`. -/
noncomputable def F2s (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  -deriv (deriv U) (cstar θ f ks) * (1 + β⁻¹ - θ * ks * deriv (deriv f) ks) -
    β * (1 - θ) * deriv (deriv f) ks * deriv U (cstar θ f ks)

/-- §18.2 (6c): `F₃* = U″(c*)`. -/
noncomputable def F3s (U : ℝ → ℝ) (θ : ℝ) (f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  deriv (deriv U) (cstar θ f ks)

/-- `ψ′(k*) = β⁻¹ − θ k* f″(k*)` when `β(1 − θ) f′(k*) = 1`. -/
theorem dpsi_star {β θ ks : ℝ} {f : ℝ → ℝ} (hβ : 0 < β) (heul : β * (1 - θ) * deriv f ks = 1) :
    dpsi θ f ks = β⁻¹ - θ * ks * deriv (deriv f) ks := by
  have h : (1 - θ) * deriv f ks = β⁻¹ := by
    field_simp
    linarith
  simp only [dpsi, h]

/-- (6a) verified: `F₁(k*, k*, k*) = F₁*`. -/
theorem F1f_star {β θ ks : ℝ} {U f : ℝ → ℝ} (hβ : 0 < β)
    (heul : β * (1 - θ) * deriv f ks = 1) : F1f θ U f ks ks = F1s β θ U f ks := by
  simp only [F1f, F1s, cstar, dpsi_star hβ heul]

/-- (6b) verified: `F₂(k*, k*, k*) = F₂*`. -/
theorem F2f_star {β θ ks : ℝ} {U f : ℝ → ℝ} (hβ : 0 < β)
    (heul : β * (1 - θ) * deriv f ks = 1) : F2f β θ U f ks ks ks = F2s β θ U f ks := by
  simp only [F2f, F2s, cstar, dpsi_star hβ heul]
  linear_combination (-(deriv (deriv U) (psi θ f ks - ks) *
    (β⁻¹ - θ * ks * deriv (deriv f) ks))) * heul

/-- (6c) verified: `F₃(k*, k*, k*) = F₃*`. -/
theorem F3f_star {β θ ks : ℝ} {U f : ℝ → ℝ} (heul : β * (1 - θ) * deriv f ks = 1) :
    F3f β θ U f ks ks = F3s U θ f ks := by
  simp only [F3f, F3s, cstar, heul, one_mul]

/-! ### The hypotheses of the local analysis -/

/-- **Hypotheses of the local analysis.** Assumption 18.1 as used near the steady state, with
`k* > 0` solving (5), `U′(c*) > 0`, and the added hypotheses (NOTE 18.2-B) `U″(c*) < 0`,
`f″(k*) < 0`. -/
structure LocalHyp (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  U_contDiff : ContDiff ℝ 2 U
  f_contDiff : ContDiff ℝ 2 f
  ks_pos : 0 < ks
  euler : β * (1 - θ) * deriv f ks = 1
  deriv_U_pos : 0 < deriv U (cstar θ f ks)
  deriv2_U_neg : deriv (deriv U) (cstar θ f ks) < 0
  deriv2_f_neg : deriv (deriv f) ks < 0

/-- Assumption 18.1, the steady state `k* ∈ (0, k̄)` of (5) and the added hypotheses
`U″(c*) < 0`, `f″(k*) < 0` give `LocalHyp`. -/
theorem Assumption18_1.localHyp {β θ kbar ks : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) (hks : ks ∈ Ioo 0 kbar)
    (heul : β * (1 - θ) * deriv f ks = 1) (hU2 : deriv (deriv U) (cstar θ f ks) < 0)
    (hf2 : deriv (deriv f) ks < 0) : LocalHyp β θ U f ks where
  beta_pos := A.beta_pos
  beta_lt_one := A.beta_lt_one
  theta_pos := A.theta_pos
  theta_lt_one := A.theta_lt_one
  U_contDiff := A.U_contDiff
  f_contDiff := A.f_contDiff
  ks_pos := hks.1
  euler := heul
  deriv_U_pos := A.deriv_U_pos (by
    have := A.le_psi ⟨hks.1.le, hks.2.le⟩
    simp only [cstar]
    linarith)
  deriv2_U_neg := hU2
  deriv2_f_neg := hf2

/-- `F₁* < 0`. -/
theorem LocalHyp.F1s_neg {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    F1s β θ U f ks < 0 := by
  have h1 : 0 < β⁻¹ - θ * ks * deriv (deriv f) ks := by
    have := inv_pos.2 L.beta_pos
    have := mul_pos L.theta_pos L.ks_pos
    nlinarith [L.deriv2_f_neg]
  exact mul_neg_of_neg_of_pos L.deriv2_U_neg h1

/-- `F₃* < 0`. -/
theorem LocalHyp.F3s_neg {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    F3s U θ f ks < 0 :=
  L.deriv2_U_neg

/-- `F₂* > 0`. -/
theorem LocalHyp.F2s_pos {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    0 < F2s β θ U f ks := by
  have h1 : 0 < 1 + β⁻¹ - θ * ks * deriv (deriv f) ks := by
    have := inv_pos.2 L.beta_pos
    have := mul_pos L.theta_pos L.ks_pos
    nlinarith [L.deriv2_f_neg]
  have h2 : 0 < -deriv (deriv U) (cstar θ f ks) * (1 + β⁻¹ - θ * ks * deriv (deriv f) ks) :=
    mul_pos (by linarith [L.deriv2_U_neg]) h1
  have h3 : 0 < β * (1 - θ) := mul_pos L.beta_pos (by linarith [L.theta_lt_one])
  have h4 : β * (1 - θ) * deriv (deriv f) ks * deriv U (cstar θ f ks) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h3 L.deriv2_f_neg) L.deriv_U_pos
  simp only [F2s]
  linarith

/-! ### The characteristic polynomial -/

/-- The characteristic polynomial `P(λ) = F₁* + F₂* λ + F₃* λ²` (p. 549). -/
noncomputable def charPoly (β θ : ℝ) (U f : ℝ → ℝ) (ks l : ℝ) : ℝ :=
  F1s β θ U f ks + F2s β θ U f ks * l + F3s U θ f ks * l ^ 2

/-- The discriminant `F₂*² − 4 F₁* F₃*`. -/
noncomputable def charDisc (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  F2s β θ U f ks ^ 2 - 4 * F1s β θ U f ks * F3s U θ f ks

/-- The smaller root `λ* = (−F₂* + √D)/(2F₃*)` (`F₃* < 0`). -/
noncomputable def lamStar (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  (-F2s β θ U f ks + Real.sqrt (charDisc β θ U f ks)) / (2 * F3s U θ f ks)

/-- The larger root `λ₂ = (−F₂* − √D)/(2F₃*)`. -/
noncomputable def lamTwo (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  (-F2s β θ U f ks - Real.sqrt (charDisc β θ U f ks)) / (2 * F3s U θ f ks)

/-- `P(1) = −β(1 − θ) f″(k*) U′(c*)` (p. 549). -/
theorem charPoly_one (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) :
    charPoly β θ U f ks 1 = -(β * (1 - θ) * deriv (deriv f) ks * deriv U (cstar θ f ks)) := by
  simp only [charPoly, F1s, F2s, F3s]
  ring

/-- `P(1) > 0`. -/
theorem LocalHyp.charPoly_one_pos {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    0 < charPoly β θ U f ks 1 := by
  rw [charPoly_one]
  have h3 : 0 < β * (1 - θ) := mul_pos L.beta_pos (by linarith [L.theta_lt_one])
  have := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h3 L.deriv2_f_neg) L.deriv_U_pos
  linarith

/-- `P(0) = F₁* < 0`. -/
theorem LocalHyp.charPoly_zero_neg {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    charPoly β θ U f ks 0 < 0 := by
  simpa [charPoly] using L.F1s_neg

/-- `F₁*/F₃* = β⁻¹ − θ k* f″(k*) > 1`. -/
theorem LocalHyp.one_lt_F1s_div_F3s {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    1 < F1s β θ U f ks / F3s U θ f ks := by
  have hne : F3s U θ f ks ≠ 0 := L.F3s_neg.ne
  have e : F1s β θ U f ks / F3s U θ f ks = β⁻¹ - θ * ks * deriv (deriv f) ks := by
    simp only [F1s, F3s]
    exact mul_div_cancel_left₀ _ hne
  rw [e]
  have h1 : 1 < β⁻¹ := one_lt_inv₀ L.beta_pos |>.2 L.beta_lt_one
  have := mul_pos L.theta_pos L.ks_pos
  nlinarith [L.deriv2_f_neg]

/-- `P(F₁*/F₃*) = (F₁*/F₃*) P(1)` (NOTE 18.2-C). -/
theorem charPoly_F1_div_F3 {β θ ks : ℝ} {U f : ℝ → ℝ} (hne : F3s U θ f ks ≠ 0) :
    charPoly β θ U f ks (F1s β θ U f ks / F3s U θ f ks) =
      F1s β θ U f ks / F3s U θ f ks * charPoly β θ U f ks 1 := by
  simp only [charPoly]
  field_simp
  ring

/-- **Roots of the characteristic polynomial** (p. 549). Under `LocalHyp`: `D > 0`,
`P(λ) = F₃*(λ − λ*)(λ − λ₂)`, `0 < λ* < 1 < λ₂`, `P(λ*) = P(λ₂) = 0`, `P > 0` on `(λ*, λ₂)`,
and `λ* < F₁*/F₃* < λ₂`. -/
theorem LocalHyp.charPoly_roots {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    0 < charDisc β θ U f ks ∧
      (∀ l, charPoly β θ U f ks l =
        F3s U θ f ks * (l - lamStar β θ U f ks) * (l - lamTwo β θ U f ks)) ∧
      0 < lamStar β θ U f ks ∧ lamStar β θ U f ks < 1 ∧ 1 < lamTwo β θ U f ks ∧
      (∀ l, lamStar β θ U f ks < l → l < lamTwo β θ U f ks → 0 < charPoly β θ U f ks l) ∧
      lamStar β θ U f ks < F1s β θ U f ks / F3s U θ f ks ∧
      F1s β θ U f ks / F3s U θ f ks < lamTwo β θ U f ks := by
  set F1 := F1s β θ U f ks with hF1
  set F2 := F2s β θ U f ks with hF2
  set F3 := F3s U θ f ks with hF3
  set D := charDisc β θ U f ks with hD
  have hF3n : F3 < 0 := L.F3s_neg
  have hF3ne : F3 ≠ 0 := hF3n.ne
  have hP1 := L.charPoly_one_pos
  have hP0 := L.charPoly_zero_neg
  simp only [charPoly] at hP1 hP0
  rw [← hF1, ← hF2, ← hF3] at hP1 hP0
  have hDpos : 0 < D := by
    have e : D = (2 * F3 + F2) ^ 2 - 4 * F3 * (F1 + F2 * 1 + F3 * 1 ^ 2) := by
      simp only [hD, charDisc, ← hF1, ← hF2, ← hF3]
      ring
    rw [e]
    nlinarith [sq_nonneg (2 * F3 + F2)]
  have hs : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hDpos.le
  have hsq : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
  set r1 := lamStar β θ U f ks with hr1
  set r2 := lamTwo β θ U f ks with hr2
  have hr1e : r1 = (-F2 + Real.sqrt D) / (2 * F3) := rfl
  have hr2e : r2 = (-F2 - Real.sqrt D) / (2 * F3) := rfl
  have hD' : D = F2 ^ 2 - 4 * F1 * F3 := rfl
  have hnum : (-F2 + Real.sqrt D) * (-F2 - Real.sqrt D) = 4 * F1 * F3 := by
    linear_combination (-1) * hs - hD'
  have hsum : F3 * (r1 + r2) = -F2 := by
    rw [hr1e, hr2e]
    field_simp
    ring
  have hprod : F3 * (r1 * r2) = F1 := by
    rw [hr1e, hr2e, div_mul_div_comm, hnum]
    field_simp
    ring
  have hfac : ∀ l, F1 + F2 * l + F3 * l ^ 2 = F3 * (l - r1) * (l - r2) := by
    intro l
    calc F1 + F2 * l + F3 * l ^ 2 = F3 * l ^ 2 - (-F2) * l + F1 := by ring
      _ = F3 * l ^ 2 - F3 * (r1 + r2) * l + F3 * (r1 * r2) := by rw [hsum, hprod]
      _ = F3 * (l - r1) * (l - r2) := by ring
  have hr12 : r1 < r2 := by
    have e : r2 - r1 = -Real.sqrt D / F3 := by
      rw [hr1e, hr2e]
      field_simp
      ring
    have : 0 < -Real.sqrt D / F3 := div_pos_iff.2 (Or.inr ⟨by linarith, hF3n⟩)
    linarith
  have h1 := hfac 1
  have h0 := hfac 0
  have hprod1 : (1 - r1) * (1 - r2) < 0 := by
    have e : F3 * (1 - r1) * (1 - r2) = F3 * ((1 - r1) * (1 - r2)) := by ring
    rw [e] at h1
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (neg_nonneg.2 hF3n.le) hc]
  have hr1lt : r1 < 1 := by
    by_contra hc
    push Not at hc
    have : 0 ≤ (1 - r1) * (1 - r2) := mul_nonneg_of_nonpos_of_nonpos (by linarith)
      (by linarith)
    linarith
  have hr2gt : 1 < r2 := by
    by_contra hc
    push Not at hc
    have : 0 ≤ (1 - r1) * (1 - r2) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hprod0 : 0 < r1 * r2 := by
    have e : F3 * (0 - r1) * (0 - r2) = F3 * (r1 * r2) := by ring
    rw [e] at h0
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (neg_nonneg.2 hF3n.le) (neg_nonneg.2 hc)]
  have hr1pos : 0 < r1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hpos : ∀ l, r1 < l → l < r2 → 0 < F1 + F2 * l + F3 * l ^ 2 := by
    intro l hl1 hl2
    rw [hfac l]
    have : (l - r1) * (l - r2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have e : F3 * (l - r1) * (l - r2) = F3 * ((l - r1) * (l - r2)) := by ring
    rw [e]
    exact mul_pos_of_neg_of_neg hF3n this
  have hq1 : 1 < F1 / F3 := L.one_lt_F1s_div_F3s
  have hq : 0 < F1 / F3 * (F1 + F2 * 1 + F3 * 1 ^ 2) := mul_pos (by linarith) hP1
  have hPq := charPoly_F1_div_F3 (β := β) (U := U) hF3ne
  simp only [charPoly] at hPq
  rw [← hF1, ← hF2, ← hF3] at hPq
  have hqlt : F1 / F3 < r2 := by
    by_contra hc
    push Not at hc
    have hX : 0 ≤ (F1 / F3 - r1) * (F1 / F3 - r2) := mul_nonneg (by linarith) (by linarith)
    have e := hfac (F1 / F3)
    have e2 : F3 * (F1 / F3 - r1) * (F1 / F3 - r2) =
        F3 * ((F1 / F3 - r1) * (F1 / F3 - r2)) := by ring
    rw [e2] at e
    nlinarith [mul_nonneg (neg_nonneg.2 hF3n.le) hX]
  refine ⟨hDpos, fun l => hfac l, hr1pos, hr1lt, hr2gt, hpos, by linarith, hqlt⟩

/-- For `λ ∈ (λ*, 1]`, `P(λ) > 0`. -/
theorem LocalHyp.charPoly_pos {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) {l : ℝ}
    (hl : lamStar β θ U f ks < l) (hl1 : l ≤ 1) : 0 < charPoly β θ U f ks l := by
  obtain ⟨-, -, -, -, h2, hpos, -⟩ := L.charPoly_roots
  exact hpos l hl (by linarith)

/-- `H₁* = −F₁*/F₂* > 0` (p. 549). -/
theorem LocalHyp.H1s_pos {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    0 < -F1s β θ U f ks / F2s β θ U f ks :=
  div_pos (by linarith [L.F1s_neg]) L.F2s_pos

/-- `H₂* = −F₃*/F₂* > 0` (p. 549). -/
theorem LocalHyp.H2s_pos {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    0 < -F3s U θ f ks / F2s β θ U f ks :=
  div_pos (by linarith [L.F3s_neg]) L.F2s_pos

/-- `H₁* + H₂* λ² < λ ⇔ P(λ) > 0` (proof of Proposition 18.2); in particular for
`λ ∈ (λ*, 1]`. -/
theorem LocalHyp.H_lt_lam {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) {l : ℝ}
    (hl : lamStar β θ U f ks < l) (hl1 : l ≤ 1) :
    -F1s β θ U f ks / F2s β θ U f ks + -F3s U θ f ks / F2s β θ U f ks * l ^ 2 < l := by
  have hP := L.charPoly_pos hl hl1
  have hF2 := L.F2s_pos
  simp only [charPoly] at hP
  have e : -F1s β θ U f ks / F2s β θ U f ks + -F3s U θ f ks / F2s β θ U f ks * l ^ 2 =
      (-F1s β θ U f ks - F3s U θ f ks * l ^ 2) / F2s β θ U f ks := by ring
  rw [e, div_lt_iff₀ hF2]
  linarith

/-- `H₁* + H₂* < 1 ⇔ P(1) > 0` (NOTE 18.2-H). -/
theorem LocalHyp.H_sum_lt_one {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    -F1s β θ U f ks / F2s β θ U f ks + -F3s U θ f ks / F2s β θ U f ks < 1 := by
  have h := L.H_lt_lam (l := 1) (L.charPoly_roots.2.2.2.1) le_rfl
  rwa [one_pow, mul_one] at h

/-- **The corrected step of Proposition 18.3** (NOTE 18.2-E): `H₂*(1 + λ) < 1` for every
`λ ≤ 1`; indeed `H₂*(1 + λ) < H₁* + H₂* < 1` for `λ < 1 < F₁*/F₃*`. -/
theorem LocalHyp.H2s_mul_lt_one {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) {l : ℝ}
    (hl1 : l ≤ 1) : -F3s U θ f ks / F2s β θ U f ks * (1 + l) < 1 := by
  have hF2 := L.F2s_pos
  have hq := L.one_lt_F1s_div_F3s
  have hF3 := L.F3s_neg
  have hP1 := L.charPoly_one_pos
  simp only [charPoly] at hP1
  have hF1F3 : F1s β θ U f ks < F3s U θ f ks * l := by
    rw [lt_div_iff_of_neg hF3] at hq
    nlinarith
  have e : -F3s U θ f ks / F2s β θ U f ks * (1 + l) =
      (-F3s U θ f ks * (1 + l)) / F2s β θ U f ks := by ring
  rw [e, div_lt_iff₀ hF2]
  linarith

/-! ### NOTE 18.2-B: strict concavity does not give a negative second derivative -/

/-- The function `U_{c₀}(c) = −e^{−c}((c − c₀)² + 4(c − c₀) + 6)`. -/
noncomputable def flatU (c₀ c : ℝ) : ℝ := -Real.exp (-c) * ((c - c₀) ^ 2 + 4 * (c - c₀) + 6)

/-- `U_{c₀}′(c) = e^{−c}((c − c₀)² + 2(c − c₀) + 2)`. -/
theorem hasDerivAt_flatU (c₀ c : ℝ) :
    HasDerivAt (flatU c₀) (Real.exp (-c) * ((c - c₀) ^ 2 + 2 * (c - c₀) + 2)) c := by
  have h1 : HasDerivAt (fun c => -Real.exp (-c)) (Real.exp (-c)) c := by
    simpa using ((hasDerivAt_neg c).exp).fun_neg
  have h2 : HasDerivAt (fun c => (c - c₀) ^ 2 + 4 * (c - c₀) + 6) (2 * (c - c₀) + 4) c := by
    have := ((((hasDerivAt_id' c).sub_const c₀).pow 2).add
      (((hasDerivAt_id' c).sub_const c₀).const_mul 4)).add_const 6
    exact this.congr_deriv (by simp)
  exact (h1.mul h2).congr_deriv (by ring)

/-- `U_{c₀}″(c) = −(c − c₀)² e^{−c}`. -/
theorem hasDerivAt_deriv_flatU (c₀ c : ℝ) :
    HasDerivAt (deriv (flatU c₀)) (-(c - c₀) ^ 2 * Real.exp (-c)) c := by
  have e : deriv (flatU c₀) = fun c => Real.exp (-c) * ((c - c₀) ^ 2 + 2 * (c - c₀) + 2) :=
    funext fun c => (hasDerivAt_flatU c₀ c).deriv
  rw [e]
  have h1 : HasDerivAt (fun c => Real.exp (-c)) (Real.exp (-c) * (-1)) c :=
    (hasDerivAt_neg c).exp
  have h2 : HasDerivAt (fun c => (c - c₀) ^ 2 + 2 * (c - c₀) + 2) (2 * (c - c₀) + 2) c := by
    have := ((((hasDerivAt_id' c).sub_const c₀).pow 2).add
      (((hasDerivAt_id' c).sub_const c₀).const_mul 2)).add_const 2
    exact this.congr_deriv (by simp)
  exact (h1.mul h2).congr_deriv (by ring)

/-- **Strict concavity does not give `U″ < 0`** (NOTE 18.2-B). For every `c₀`, the function
`U_{c₀}` is `C²` (indeed `C^∞`), strictly increasing and strictly concave on `ℝ` (so it
satisfies Assumption 18.1(b)), and `U_{c₀}″(c₀) = 0`. -/
theorem strictConcave_deriv2_zero_counterexample (c₀ : ℝ) :
    ContDiff ℝ 2 (flatU c₀) ∧ StrictMono (flatU c₀) ∧ StrictConcaveOn ℝ univ (flatU c₀) ∧
      deriv (deriv (flatU c₀)) c₀ = 0 := by
  have hd : ∀ c, deriv (flatU c₀) c = Real.exp (-c) * ((c - c₀) ^ 2 + 2 * (c - c₀) + 2) :=
    fun c => (hasDerivAt_flatU c₀ c).deriv
  have hpos : ∀ c, 0 < deriv (flatU c₀) c := fun c => by
    rw [hd]
    exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg (c - c₀ + 1)])
  have hcont : Continuous (flatU c₀) := by
    unfold flatU
    fun_prop
  have hd2 : ∀ c, deriv (deriv (flatU c₀)) c = -(c - c₀) ^ 2 * Real.exp (-c) :=
    fun c => (hasDerivAt_deriv_flatU c₀ c).deriv
  have hdc : Continuous (deriv (flatU c₀)) := by
    rw [show deriv (flatU c₀) = fun c => Real.exp (-c) * ((c - c₀) ^ 2 + 2 * (c - c₀) + 2)
      from funext hd]
    fun_prop
  -- `U′` is strictly decreasing: on `(-∞, c₀]` and on `[c₀, ∞)` separately.
  have hanti1 : StrictAntiOn (deriv (flatU c₀)) (Iic c₀) := by
    refine strictAntiOn_of_deriv_neg (convex_Iic c₀) hdc.continuousOn fun c hc => ?_
    rw [interior_Iic] at hc
    rw [hd2]
    have : 0 < (c - c₀) ^ 2 := by nlinarith [mem_Iio.1 hc]
    nlinarith [Real.exp_pos (-c)]
  have hanti2 : StrictAntiOn (deriv (flatU c₀)) (Ici c₀) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici c₀) hdc.continuousOn fun c hc => ?_
    rw [interior_Ici] at hc
    rw [hd2]
    have : 0 < (c - c₀) ^ 2 := by nlinarith [mem_Ioi.1 hc]
    nlinarith [Real.exp_pos (-c)]
  have hanti : StrictAnti (deriv (flatU c₀)) := by
    intro x y hxy
    rcases le_or_gt y c₀ with hy | hy
    · exact hanti1 (mem_Iic.2 (by linarith)) (mem_Iic.2 hy) hxy
    rcases le_or_gt c₀ x with hx | hx
    · exact hanti2 (mem_Ici.2 hx) (mem_Ici.2 (by linarith)) hxy
    exact (hanti2 (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le) hy).trans
      (hanti1 (mem_Iic.2 hx.le) (mem_Iic.2 le_rfl) hx)
  refine ⟨?_, strictMono_of_deriv_pos hpos, hanti.strictConcaveOn_univ_of_deriv hcont,
    by rw [hd2]; ring⟩
  unfold flatU
  fun_prop

/-- **Degenerate case `U″(c*) = 0`** (NOTE 18.2-B): then `F₁* = F₃* = 0`, `P(0) = 0` (so the
book's `P(0) < 0` fails) and `P(λ) = F₂* λ` is linear with root `0`. -/
theorem charPoly_degenerate_U {β θ ks : ℝ} {U f : ℝ → ℝ}
    (h : deriv (deriv U) (cstar θ f ks) = 0) :
    F1s β θ U f ks = 0 ∧ F3s U θ f ks = 0 ∧ charPoly β θ U f ks 0 = 0 ∧
      ∀ l, charPoly β θ U f ks l = F2s β θ U f ks * l := by
  have h1 : F1s β θ U f ks = 0 := by simp [F1s, h]
  have h3 : F3s U θ f ks = 0 := h
  exact ⟨h1, h3, by simp [charPoly, h1, h3], fun l => by simp [charPoly, h1, h3]⟩

/-- **Degenerate case `f″(k*) = 0`** (NOTE 18.2-B): then `P(1) = 0`, so the book's `P(1) > 0`
fails and `λ = 1` is a root. -/
theorem charPoly_degenerate_f {β θ ks : ℝ} {U f : ℝ → ℝ} (h : deriv (deriv f) ks = 0) :
    charPoly β θ U f ks 1 = 0 := by
  rw [charPoly_one, h]
  ring

end StokeyLucasPrescott.EquilibriaWithDistortions
