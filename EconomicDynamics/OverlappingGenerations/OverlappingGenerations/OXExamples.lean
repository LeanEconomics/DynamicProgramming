/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.OXOptimality
import OverlappingGenerations.Scalar

/-!
# Examples 16.1.1 and 16.1.2

Miao, §16.1, pp. 536–537.

* The logarithmic economy (`u = ln`, `β = 1`, `g_m = 1`, any `g_n`): the saving difference
  equation is linear in `x_t = 1/m̂_t`, `x_{t+1} = (g_ne₁/e₂)x_t − 2g_n/e₂` (`ox_log_eulerRel`);
  every monetary equilibrium is `x_t = x* + cλ^{t−1}` with `c ≥ 0` (`ox_log_paths`), every such
  path is one (`ox_log_construct`), and paths with `c > 0` have `m̂_t → 0` (`ox_log_tendsto`).
  This is used again in Exercise 16.1.
* **Example 16.1.1** (`g_n = 1`, `N₀ = 1`): the price difference equation
  `p_te₁ − M = p_{t+1}e₂ + M` (`example_16_1_1_diffeq`), its general solution
  `p_t = 2M/(e₁ − e₂) + c(e₁/e₂)ᵗ` with `c ≥ 0` (`example_16_1_1_general`), every `c ≥ 0` gives a
  monetary equilibrium (`example_16_1_1_construct`); `c = 0` is the stationary monetary
  equilibrium; for `c > 0` the price level explodes, the allocation tends to autarky and gross
  inflation tends to `e₁/e₂ = 1/R_aut` (`example_16_1_1_explosive`). Figure 16.2 in this
  economy: no equilibrium starts to the right of `m* = (e₁ − e₂)/2`, a path of the difference
  equation that does leaves `(0, e₁)` (`example_16_1_1_right`), and equilibria starting to the
  left decrease to the nonmonetary steady state (`example_16_1_1_left`).
* **Example 16.1.2**: the high-interest-rate equilibrium `p_t = 1`, `c = 1/2`, `R = 1`
  (`example_16_1_2_high`); the low-interest-rate (autarky) equilibrium: `R_aut < 1`, the price
  system `p_t/p_{t+1} = R_aut` makes autarky optimal for every generation, prices explode, the
  present value of the aggregate endowment is infinite and autarky is not Pareto optimal
  (`example_16_1_2_low`).

**Corrections.** (i) Example 16.1.2 says the initial old have no money but money `M = 0.5 − ε`
is supplied for `t ≥ 1`; in the model of §16.1 (`M_t = g_mM_{t−1}`) this is the economy with
`M₀ = 0.5 − ε` held by the initial old and `g_m = 1`, which is what is formalised. (ii) In the
low-interest-rate equilibrium the price sequence `p₁ = 1`, `p_t/p_{t+1} = R_aut` with valued money
is not an equilibrium: the initial old would consume `ε + (0.5 − ε) = 0.5`, and (16.6) forces
`R_{t+1} > R_aut` in every monetary equilibrium (`example_16_1_2_not_monetary`). The
low-interest-rate equilibrium is the nonmonetary one (`p_t = ∞`); at the prices `p_t/p_{t+1} =
R_aut` every generation's optimal choice is autarky with zero money demand.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

namespace OXEconomy

variable (E : OXEconomy)

/-- The example economy is logarithmic with `β = 1` and `g_n = g_m = N₀ = 1`, `e₁ > e₂`: it
satisfies the hypotheses of Example 16.1.1. -/
theorem ox_exampleEconomy_log :
    ox_exampleEconomy.ox_P.ox_du = (fun c => c⁻¹) ∧ ox_exampleEconomy.ox_P.ox_β = 1 ∧
      ox_exampleEconomy.ox_gn = 1 ∧ ox_exampleEconomy.ox_gm = 1 ∧ ox_exampleEconomy.ox_N0 = 1 ∧
      ox_exampleEconomy.ox_e2 < ox_exampleEconomy.ox_e1 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [ox_exampleEconomy]; norm_num

/-- With `u = ln`, `β = 1`: `R_aut = e₂/e₁`. -/
theorem ox_log_Raut (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1) :
    E.ox_Raut = E.ox_e2 / E.ox_e1 := by
  unfold ox_Raut; simp only [hdu, hβ, one_mul]
  have := E.ox_e1_pos.ne'; have := E.ox_e2_pos.ne'
  field_simp

/-- The logarithmic saving difference equation (Miao, p. 536): with `u = ln`, `β = 1`, `g_m = 1`
and `a, b ∈ (0, e₁)`, `(a, b)` solves the Euler relation iff
`1/b = (g_ne₁/e₂)(1/a) − 2g_n/e₂`. -/
theorem ox_log_eulerRel (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) {a b : ℝ} (ha : 0 < a) (hae : a < E.ox_e1) (hb : 0 < b)
    (hbe : b < E.ox_e1) :
    E.ox_EulerRel a b ↔ b⁻¹ = E.ox_gn * E.ox_e1 / E.ox_e2 * a⁻¹ - 2 * E.ox_gn / E.ox_e2 := by
  have he2 := E.ox_e2_pos
  have hgn := E.ox_gn_pos
  have h1 : E.ox_e1 - a ≠ 0 := by linarith
  have h2 : E.ox_e2 + E.ox_gn * b ≠ 0 := by nlinarith
  unfold ox_EulerRel
  simp only [hdu, hβ, hgm, one_mul]
  constructor
  · rintro ⟨-, -, -, -, h⟩
    field_simp at h ⊢
    linear_combination h
  · intro h
    refine ⟨ha, hae, hb, hbe, ?_⟩
    field_simp at h ⊢
    linear_combination h

/-- The fixed point `x* = 2g_n/(g_ne₁ − e₂)` and the root `λ = g_ne₁/e₂` of the logarithmic
difference equation satisfy `λx* − 2g_n/e₂ = x*`. -/
theorem ox_log_fixed (hgap : E.ox_e2 < E.ox_gn * E.ox_e1) :
    E.ox_gn * E.ox_e1 / E.ox_e2 * (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2)) -
      2 * E.ox_gn / E.ox_e2 = 2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) := by
  have := E.ox_e2_pos.ne'
  have : E.ox_gn * E.ox_e1 - E.ox_e2 ≠ 0 := by linarith
  field_simp
  ring

/-- Miao, pp. 536–537 and Exercise 16.1(c): in the logarithmic economy every monetary equilibrium
has `1/m̂_{n+1} = x* + cλⁿ` with `c ≥ 0`, `x* = 2g_n/(g_ne₁ − e₂)`, `λ = g_ne₁/e₂ > 1`. -/
theorem ox_log_paths (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) :
    E.ox_e2 < E.ox_gn * E.ox_e1 ∧ ∃ c, 0 ≤ c ∧ ∀ n : ℕ, (E.ox_mhat q (n + 1))⁻¹ =
      2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) + c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ n := by
  have he1 := E.ox_e1_pos
  have he2 := E.ox_e2_pos
  have hgap : E.ox_e2 < E.ox_gn * E.ox_e1 := by
    have := E.proposition_16_1_1_necessity h
    rw [E.ox_log_Raut hdu hβ, hgm, mul_one, div_lt_iff₀ he1] at this
    linarith
  refine ⟨hgap, ?_⟩
  set lam := E.ox_gn * E.ox_e1 / E.ox_e2
  set xs := 2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2)
  have hlam : 1 < lam := (one_lt_div he2).2 hgap
  set y := fun n : ℕ => (E.ox_mhat q (n + 1))⁻¹
  have hsol : IsScalarSol lam (-(2 * E.ox_gn / E.ox_e2)) (fun _ => 1) y := fun n => by
    have hr := E.ox_monetary_eulerRel h (t := n + 1) (by omega)
    have := (E.ox_log_eulerRel hdu hβ hgm hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1).1 hr
    simp only [y, mul_one]; rw [this]; ring
  have hgen := (eq_1_3 hlam.ne' y).1 hsol
  have hxs : -(2 * E.ox_gn / E.ox_e2) / (1 - lam) = xs := by
    simp only [lam, xs]
    have : E.ox_gn * E.ox_e1 - E.ox_e2 ≠ 0 := by linarith
    have : E.ox_e2 - E.ox_gn * E.ox_e1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hxs] at hgen
  refine ⟨y 0 - xs, ?_, fun n => (hgen n).trans (by ring)⟩
  by_contra hneg
  have hc : y 0 - xs < 0 := not_le.1 hneg
  have hpos : ∀ n, 0 < y n := fun n => by
    have := ((E.ox_monetary_alloc h).1 (n + 1) (by omega)).2.1
    exact inv_pos.2 this
  have ht : Tendsto (fun n : ℕ => (y 0 - xs) * lam ^ n) atTop atBot :=
    (tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop_of_neg hc
  obtain ⟨n, hn⟩ := (ht.eventually_lt_atBot (-xs)).exists
  have := hpos n
  rw [hgen n] at this
  linarith

/-- Miao, p. 536 and Exercise 16.1(c): in the logarithmic economy with `e₂ < g_ne₁`, for every
`c ≥ 0` the path `m̂_t = 1/(x* + cλ^{t−1})` is a monetary equilibrium. -/
theorem ox_log_construct (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) (hgap : E.ox_e2 < E.ox_gn * E.ox_e1) {c : ℝ} (hc : 0 ≤ c) :
    E.ox_IsMonetary (E.ox_qOf fun t => (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
        c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t - 1))⁻¹)
      (fun t => E.ox_e1 - (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
        c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t - 1))⁻¹)
      (fun t => E.ox_e2 + E.ox_gn * (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
        c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t + 1 - 1))⁻¹)
      (fun t => E.ox_M t / E.ox_N t) := by
  have he1 := E.ox_e1_pos
  have he2 := E.ox_e2_pos
  have hgn := E.ox_gn_pos
  have hfix := E.ox_log_fixed hgap
  set lam := E.ox_gn * E.ox_e1 / E.ox_e2
  set xs := 2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2)
  have hlam : 1 < lam := (one_lt_div he2).2 hgap
  have hxs : E.ox_e1⁻¹ < xs := by
    simp only [xs]
    rw [inv_lt_iff_one_lt_mul₀ he1, div_mul_eq_mul_div, one_lt_div (by linarith)]
    nlinarith
  have hbig : ∀ k : ℕ, E.ox_e1⁻¹ < xs + c * lam ^ k := fun k => by
    have : 0 ≤ c * lam ^ k := mul_nonneg hc (pow_nonneg (by linarith) k)
    linarith
  have hpos : ∀ k : ℕ, 0 < xs + c * lam ^ k := fun k =>
    lt_trans (inv_pos.2 he1) (hbig k)
  have hlt : ∀ k : ℕ, (xs + c * lam ^ k)⁻¹ < E.ox_e1 := fun k => by
    rw [inv_lt_comm₀ (hpos k) he1]; exact hbig k
  refine E.ox_ofSaving_isMonetary fun t ht => ?_
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine (E.ox_log_eulerRel hdu hβ hgm (inv_pos.2 (hpos s)) (hlt s) (inv_pos.2 (hpos (s + 1)))
    (hlt (s + 1))).2 ?_
  rw [inv_inv, inv_inv, pow_succ]
  linear_combination -hfix

/-- Paths with `c > 0` have real balances `m̂_t → 0`. -/
theorem ox_log_tendsto (hgap : E.ox_e2 < E.ox_gn * E.ox_e1) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℕ => (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
      c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t - 1))⁻¹) atTop (𝓝 0) := by
  have hlam : 1 < E.ox_gn * E.ox_e1 / E.ox_e2 := (one_lt_div E.ox_e2_pos).2 hgap
  refine tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ ?_)
  exact ((tendsto_pow_atTop_atTop_of_one_lt hlam).comp (tendsto_sub_atTop_nat 1)).const_mul_atTop hc

/-- **Example 16.1.1** (Miao, p. 536): with `u = ln`, `β = 1`, `g_n = g_m = 1`, `N₀ = 1`,
`M = M₀`, every monetary equilibrium satisfies `p_te₁ − M = p_{t+1}e₂ + M` (`p_t = 1/q_t`). -/
theorem example_16_1_1_diffeq (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) (hN : E.ox_N0 = 1) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) {t : ℕ} (ht : 1 ≤ t) :
    1 / q t * E.ox_e1 - E.ox_M0 = 1 / q (t + 1) * E.ox_e2 + E.ox_M0 := by
  have hr := E.ox_monetary_eulerRel h ht
  have hrel := (E.ox_log_eulerRel hdu hβ hgm hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1).1 hr
  have hmh : ∀ s, E.ox_mhat q s = q s * E.ox_M0 := fun s => by
    unfold ox_mhat ox_M ox_N; rw [hgm, hgn, hN]; simp
  rw [hmh, hmh, hgn, one_mul] at hrel
  have hq := h.2 t ht
  have hq1 := h.2 (t + 1) (by omega)
  have hM := E.ox_M0_pos
  have he2 := E.ox_e2_pos
  rw [mul_inv, mul_inv] at hrel
  have : 1 / q (t + 1) =
      E.ox_M0 * (E.ox_e1 / E.ox_e2 * ((q t)⁻¹ * E.ox_M0⁻¹) - 2 * 1 / E.ox_e2) := by
    rw [← hrel]; field_simp
  rw [this]
  field_simp
  ring

/-- **Example 16.1.1** (Miao, p. 536): the general solution. Every monetary equilibrium has
`p_t = 2M/(e₁ − e₂) + c(e₁/e₂)ᵗ` for `t ≥ 1`, with `c ≥ 0`. -/
theorem example_16_1_1_general (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) (hN : E.ox_N0 = 1) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) :
    E.ox_e2 < E.ox_e1 ∧ ∃ c, 0 ≤ c ∧ ∀ t, 1 ≤ t →
      1 / q t = 2 * E.ox_M0 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ t := by
  obtain ⟨hgap, c, hc, hx⟩ := E.ox_log_paths hdu hβ hgm h
  rw [hgn, one_mul] at hgap hx
  have he1 := E.ox_e1_pos
  have he2 := E.ox_e2_pos
  have hM := E.ox_M0_pos
  refine ⟨hgap, E.ox_M0 * c * (E.ox_e2 / E.ox_e1), by positivity, fun t ht => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hmh : E.ox_mhat q (n + 1) = q (n + 1) * E.ox_M0 := by
    unfold ox_mhat ox_M ox_N; rw [hgm, hgn, hN]; simp
  have hxn := hx n
  rw [hmh, mul_inv] at hxn
  have hq := (h.2 (n + 1) (by omega)).ne'
  have : 1 / q (n + 1) = E.ox_M0 * ((q (n + 1))⁻¹ * E.ox_M0⁻¹) := by field_simp
  rw [this, hxn, pow_succ]
  have : E.ox_e1 - E.ox_e2 ≠ 0 := by linarith
  field_simp

/-- **Example 16.1.1** (Miao, p. 536): conversely every `c ≥ 0` gives a monetary equilibrium with
`p_t = 2M/(e₁ − e₂) + c(e₁/e₂)ᵗ` for `t ≥ 1`; `c = 0` is the stationary monetary equilibrium with
constant prices. -/
theorem example_16_1_1_construct (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) (hN : E.ox_N0 = 1) (he : E.ox_e2 < E.ox_e1)
    {c : ℝ} (hc : 0 ≤ c) : ∃ q cy co m : ℕ → ℝ, E.ox_IsMonetary q cy co m ∧ ∀ t, 1 ≤ t →
      1 / q t = 2 * E.ox_M0 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ t := by
  have he1 := E.ox_e1_pos
  have he2 := E.ox_e2_pos
  have hM := E.ox_M0_pos
  have hgap : E.ox_e2 < E.ox_gn * E.ox_e1 := by rw [hgn, one_mul]; exact he
  set c' := c * (E.ox_e1 / E.ox_e2) / E.ox_M0
  have hc' : 0 ≤ c' := by positivity
  refine ⟨_, _, _, _, E.ox_log_construct hdu hβ hgm hgap hc', fun t ht => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  unfold ox_qOf ox_M ox_N
  simp only [hgn, hgm, hN, one_pow, mul_one, one_mul, Nat.add_sub_cancel, c']
  have : E.ox_e1 - E.ox_e2 ≠ 0 := by linarith
  rw [pow_succ]
  field_simp

/-- **Example 16.1.1** (Miao, pp. 536–537; Figure 16.2): along a monetary equilibrium with
`c > 0` the price level explodes, `p_t → ∞`, money becomes worthless (`m̂_t → 0`), the allocation
tends to autarky, and gross inflation `p_{t+1}/p_t` tends to `e₁/e₂ = 1/R_aut`, the inverse of the
slope of the offer curve at the origin. -/
theorem example_16_1_1_explosive (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) (hN : E.ox_N0 = 1) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) {c : ℝ} (hc : 0 < c)
    (hp : ∀ t, 1 ≤ t → 1 / q t = 2 * E.ox_M0 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ t) :
    Tendsto (fun t => 1 / q t) atTop atTop ∧ Tendsto (E.ox_mhat q) atTop (𝓝 0) ∧
      Tendsto cy atTop (𝓝 E.ox_e1) ∧ Tendsto co atTop (𝓝 E.ox_e2) ∧
      Tendsto (fun t => q t / q (t + 1)) atTop (𝓝 (E.ox_e1 / E.ox_e2)) := by
  have he := (E.example_16_1_1_general hdu hβ hgn hgm hN h).1
  have he2 := E.ox_e2_pos
  have hlam : 1 < E.ox_e1 / E.ox_e2 := (one_lt_div he2).2 he
  have hev : (fun t => 2 * E.ox_M0 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ t) =ᶠ[atTop]
      fun t => 1 / q t := by
    filter_upwards [eventually_ge_atTop 1] with t ht using (hp t ht).symm
  have hP : Tendsto (fun t => 1 / q t) atTop atTop :=
    (tendsto_atTop_add_const_left _ _
      ((tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop hc)).congr' hev
  have hmh : ∀ t, E.ox_mhat q t = E.ox_M0 * (1 / q t)⁻¹ := fun t => by
    unfold ox_mhat ox_M ox_N; rw [hgm, hgn, hN]; simp; ring
  have h0 : Tendsto (E.ox_mhat q) atTop (𝓝 0) := by
    rw [show E.ox_mhat q = fun t => E.ox_M0 * (1 / q t)⁻¹ from funext hmh]
    simpa using (tendsto_inv_atTop_zero.comp hP).const_mul E.ox_M0
  have halloc := (E.ox_monetary_alloc h).1
  have h01 : Tendsto (fun t => E.ox_mhat q (t + 1)) atTop (𝓝 0) :=
    h0.comp (tendsto_add_atTop_nat 1)
  refine ⟨hP, h0, ?_, ?_, ?_⟩
  · have : Tendsto (fun t => E.ox_e1 - E.ox_mhat q t) atTop (𝓝 (E.ox_e1 - 0)) :=
      h0.const_sub _
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht using (halloc t ht).2.2.2.1.symm
  · have : Tendsto (fun t => E.ox_e2 + E.ox_gn * E.ox_mhat q (t + 1)) atTop
        (𝓝 (E.ox_e2 + E.ox_gn * 0)) := (h01.const_mul _).const_add _
    rw [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht using (halloc t ht).2.2.2.2.symm
  · have := (E.ox_R_tendsto_Raut h h0).2
    rwa [E.ox_log_Raut hdu hβ, inv_div] at this

/-- Example 16.1.1, Figure 16.2 (Miao, pp. 534–535): no monetary equilibrium starts to the right
of the monetary steady state `m* = (e₁ − e₂)/2`, and every one starting to its left has real
balances strictly decreasing to the nonmonetary steady state `0`. -/
theorem example_16_1_1_left (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) :
    E.ox_mhat q 1 ≤ (E.ox_e1 - E.ox_e2) / 2 ∧ (E.ox_mhat q 1 < (E.ox_e1 - E.ox_e2) / 2 →
      StrictAnti (fun n => E.ox_mhat q (n + 1)) ∧ Tendsto (E.ox_mhat q) atTop (𝓝 0)) := by
  obtain ⟨hgap, c, hc, hx⟩ := E.ox_log_paths hdu hβ hgm h
  rw [hgn, one_mul] at hgap hx
  simp only [mul_one] at hx
  have he2 := E.ox_e2_pos
  have hd : 0 < E.ox_e1 - E.ox_e2 := by linarith
  have hlam : 1 < E.ox_e1 / E.ox_e2 := (one_lt_div he2).2 hgap
  have hpos : ∀ n : ℕ, 0 < 2 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ n := fun n => by
    have : 0 ≤ c * (E.ox_e1 / E.ox_e2) ^ n := mul_nonneg hc (pow_nonneg (by linarith) n)
    have : 0 < 2 / (E.ox_e1 - E.ox_e2) := by positivity
    linarith
  have hmh : ∀ n : ℕ, E.ox_mhat q (n + 1) =
      (2 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ n)⁻¹ := fun n => by
    rw [← hx n, inv_inv]
  have hstar : (2 / (E.ox_e1 - E.ox_e2))⁻¹ = (E.ox_e1 - E.ox_e2) / 2 := by rw [inv_div]
  refine ⟨?_, fun hlt => ?_⟩
  · rw [hmh 0, ← hstar, pow_zero, mul_one]
    exact inv_anti₀ (by positivity) (by linarith)
  · have hc0 : 0 < c := by
      rcases eq_or_lt_of_le hc with h0 | h0
      · rw [hmh 0, ← h0, zero_mul, add_zero, hstar] at hlt; exact absurd hlt (lt_irrefl _)
      · exact h0
    refine ⟨fun a b hab => ?_, ?_⟩
    · simp only [hmh]
      refine inv_strictAnti₀ (hpos a) ?_
      have := pow_lt_pow_right₀ hlam hab
      nlinarith
    · have ht : Tendsto (fun n => E.ox_mhat q (n + 1)) atTop (𝓝 0) := by
        simp only [hmh]
        exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _
          ((tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop hc0))
      exact (tendsto_add_atTop_iff_nat 1).1 ht

/-- Example 16.1.1, Figure 16.2 (Miao, p. 535): a solution of the difference equation
`x_{t+1} = (e₁/e₂)x_t − 2/e₂` in `x_t = 1/m_t` that starts to the right of `m*` (`x₀ < x*`)
eventually has `x_t < 1/e₁`, i.e. real balances leave `(0, e₁)`: it is not an equilibrium. -/
theorem example_16_1_1_right {e1 e2 : ℝ} (he2 : 0 < e2) (he : e2 < e1) {x : ℕ → ℝ}
    (hx : ∀ n, x (n + 1) = e1 / e2 * x n - 2 / e2) (h0 : x 0 < 2 / (e1 - e2)) :
    ∃ n, x n < e1⁻¹ := by
  have hlam : 1 < e1 / e2 := (one_lt_div he2).2 he
  have hsol : IsScalarSol (e1 / e2) (-(2 / e2)) (fun _ => 1) x := fun n => by
    rw [hx n]; ring
  have hgen := (eq_1_3 hlam.ne' x).1 hsol
  have hxs : -(2 / e2) / (1 - e1 / e2) = 2 / (e1 - e2) := by
    have : e1 - e2 ≠ 0 := by linarith
    have : e2 - e1 ≠ 0 := by linarith
    field_simp; ring
  rw [hxs] at hgen
  have hc : x 0 - 2 / (e1 - e2) < 0 := by linarith
  have ht : Tendsto (fun n : ℕ => (x 0 - 2 / (e1 - e2)) * (e1 / e2) ^ n) atTop atBot :=
    (tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop_of_neg hc
  obtain ⟨n, hn⟩ := (ht.eventually_lt_atBot (e1⁻¹ - 2 / (e1 - e2))).exists
  exact ⟨n, by rw [hgen n]; linarith⟩

/-- **Example 16.1.2** (Miao, p. 537), the high-interest-rate equilibrium: with `β = 1`,
`e₁ = 1 − ε`, `e₂ = ε`, `ε ∈ (0, 1/2)`, `g_n = g_m = N₀ = 1`, `M = 1/2 − ε`, the prices `p_t = 1`
with `c_t^t = c_{t+1}^t = c₁⁰ = 1/2` and `m_t^t = 1/2 − ε` form a monetary equilibrium with
`R_{t+1} = 1`. -/
theorem example_16_1_2_high {ε : ℝ} (hβ : E.ox_P.ox_β = 1) (he1 : E.ox_e1 = 1 - ε)
    (he2 : E.ox_e2 = ε) (hε : ε < 1 / 2) (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1)
    (hN : E.ox_N0 = 1) (hM : E.ox_M0 = 1 / 2 - ε) :
    E.ox_IsMonetary (fun _ => 1) (fun _ => 1 / 2) (fun _ => 1 / 2) (fun _ => 1 / 2 - ε) ∧
      ∀ t : ℕ, (fun _ : ℕ => (1 : ℝ)) (t + 1) / (fun _ : ℕ => (1 : ℝ)) t = 1 := by
  have hε0 : 0 < 1 / 2 - ε := by linarith
  have hNt : ∀ t, E.ox_N t = 1 := fun t => by unfold ox_N; rw [hN, hgn, one_pow, one_mul]
  have hMt : ∀ t, E.ox_M t = 1 / 2 - ε := fun t => by unfold ox_M; rw [hM, hgm, one_pow, mul_one]
  have hrel : ∀ t, 1 ≤ t → E.ox_EulerRel ((fun _ => 1 / 2 - ε) t) ((fun _ => 1 / 2 - ε) (t + 1)) :=
    fun _ _ => by
      refine ⟨hε0, by rw [he1]; linarith, hε0, by rw [he1]; linarith, ?_⟩
      dsimp only
      rw [hβ, hgn, hgm, he1, he2]
      have a1 : 1 - ε - (1 / 2 - ε) = (1 : ℝ) / 2 := by ring
      have a2 : ε + 1 * (1 / 2 - ε) = (1 : ℝ) / 2 := by ring
      have a3 : 1 * (1 / 2 - ε) / (1 * (1 / 2 - ε)) = (1 : ℝ) := div_self (by linarith)
      rw [a1, a2, a3]; ring
  have h := E.ox_ofSaving_isMonetary hrel
  have hq : E.ox_qOf (fun _ => 1 / 2 - ε) = fun _ => 1 := funext fun t => by
    unfold ox_qOf; rw [hNt, hMt, mul_one]; exact div_self hε0.ne'
  have hcy : (fun _ : ℕ => E.ox_e1 - (1 / 2 - ε)) = fun _ => 1 / 2 := funext fun _ => by
    rw [he1]; ring
  have hco : (fun _ : ℕ => E.ox_e2 + E.ox_gn * (1 / 2 - ε)) = fun _ => 1 / 2 := funext fun _ => by
    rw [he2, hgn]; ring
  have hm : (fun t => E.ox_M t / E.ox_N t) = fun _ => 1 / 2 - ε := funext fun t => by
    rw [hNt, hMt, div_one]
  rw [hq, hcy, hco, hm] at h
  exact ⟨h, fun _ => div_one 1⟩

/-- **Example 16.1.2** (Miao, p. 537), the low-interest-rate equilibrium: `R_aut < 1`; at the prices
`p₁ = 1`, `p_t/p_{t+1} = R_aut` (so `p_t = R_aut^{−(t−1)} → ∞`) every generation's optimal choice is
autarky with zero money demand; autarky with valueless money is an equilibrium, the present value
`∑ p_t(e₁ + e₂)` of the aggregate endowment is infinite, and autarky is not Pareto optimal. -/
theorem example_16_1_2_low {ε : ℝ} (hβ : E.ox_P.ox_β = 1) (he1 : E.ox_e1 = 1 - ε)
    (he2 : E.ox_e2 = ε) (hε : ε < 1 / 2) (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) :
    E.ox_Raut < 1 ∧
      (∀ t, 1 ≤ t → E.ox_Optimal (fun s => E.ox_Raut ^ (s - 1)) t E.ox_e1 E.ox_e2 0) ∧
      Tendsto (fun t : ℕ => 1 / E.ox_Raut ^ (t - 1)) atTop atTop ∧
      (¬ Summable fun t : ℕ => 1 / E.ox_Raut ^ t * (E.ox_e1 + E.ox_e2)) ∧
      E.ox_IsNonmonetary (fun _ => 0) (fun _ => E.ox_e1) (fun _ => E.ox_e2)
        (fun t => E.ox_M t / E.ox_N t) ∧
      ¬ E.ox_ParetoOptimal (fun _ => E.ox_e1) (fun _ => E.ox_e2) := by
  have hε0 : 0 < ε := he2 ▸ E.ox_e2_pos
  have hR0 : 0 < E.ox_Raut := by
    unfold ox_Raut
    have := E.ox_P.ox_du_pos _ E.ox_e1_pos
    have := E.ox_P.ox_du_pos _ E.ox_e2_pos
    have := E.ox_P.ox_β_pos
    positivity
  have hR1 : E.ox_Raut < 1 := by
    unfold ox_Raut
    rw [hβ, one_mul, div_lt_one (E.ox_P.ox_du_pos _ E.ox_e2_pos)]
    exact E.ox_P.ox_du_lt E.ox_e2_pos (by rw [he1, he2]; linarith)
  have hauto := E.ox_autarky_isEquilibrium
  refine ⟨hR1, fun t ht => ?_, ?_, ?_, hauto, ?_⟩
  · have hq : 0 < E.ox_Raut ^ (t - 1) := pow_pos hR0 _
    have hq1 : 0 < E.ox_Raut ^ (t + 1 - 1) := pow_pos hR0 _
    have hτ : E.ox_τ t = 0 := by unfold ox_τ; rw [hgm]; ring
    have hratio : E.ox_Raut ^ (t + 1 - 1) / E.ox_Raut ^ (t - 1) = E.ox_Raut := by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp
    refine ⟨⟨le_rfl, E.ox_e1_pos, E.ox_e2_pos, by simp, by simp [hτ]⟩,
      fun c1' c2' m' hb => ?_⟩
    have hl := E.ox_budget_line (q := fun s => E.ox_Raut ^ (s - 1)) hq hq1 hb
    simp only [hτ, mul_zero, add_zero, hratio] at hl
    exact (E.eq_16_5 hR0).2 rfl c1' c2' hb.2.1 hb.2.2.1 hl
  · have : Tendsto (fun t : ℕ => (1 / E.ox_Raut) ^ (t - 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hR0).2 hR1)).comp (tendsto_sub_atTop_nat 1)
    refine this.congr fun t => ?_
    rw [div_pow, one_pow]
  · intro hs
    have h0 := hs.tendsto_atTop_zero
    have hge : ∀ t : ℕ, E.ox_e1 + E.ox_e2 ≤ 1 / E.ox_Raut ^ t * (E.ox_e1 + E.ox_e2) := fun t => by
      have : 1 ≤ 1 / E.ox_Raut ^ t := by
        rw [le_div_iff₀ (pow_pos hR0 t), one_mul]; exact pow_le_one₀ hR0.le hR1.le
      nlinarith [E.ox_e1_pos, E.ox_e2_pos]
    have hpos : 0 < E.ox_e1 + E.ox_e2 := by linarith [E.ox_e1_pos, E.ox_e2_pos]
    obtain ⟨t, ht⟩ := (h0.eventually (gt_mem_nhds hpos)).exists
    linarith [hge t]
  · rw [E.proposition_16_1_2 hauto, hgn, not_le]; exact hR1

/-- **Correction to Example 16.1.2** (Miao, p. 537): no monetary equilibrium has
`p_t/p_{t+1} = R_aut`; by (16.6), `R_{t+1} > R_aut` in every monetary equilibrium. -/
theorem example_16_1_2_not_monetary {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) :
    ¬ ∀ t, 1 ≤ t → q (t + 1) / q t = E.ox_Raut := fun hR =>
  absurd (hR 1 le_rfl) (E.eq_16_6 h le_rfl).2.ne'

end OXEconomy

end Miao.OverlappingGenerations
