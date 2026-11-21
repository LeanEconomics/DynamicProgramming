/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.OXExamples
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exercises 16.1 and 16.2

Miao, §16.4, p. 556.

* **Exercise 16.1** (`u = ln`, `β = 1`, `N_t = g_nN_{t−1}`, `e₁ > e₂`, one unit of money per
  initial old, constant money stock). (a) The nonmonetary equilibrium is autarky, with
  `R_aut = e₂/e₁` (`ex_16_1_a`). (b) A stationary monetary equilibrium exists iff `e₂ < g_ne₁`
  (`ex_16_1_b_exists`); it is unique, with `m̂ = (g_ne₁ − e₂)/(2g_n)`,
  `c₁ = (g_ne₁ + e₂)/(2g_n)`, `c₂ = (g_ne₁ + e₂)/2`, `R = g_n`, `p_t = 1/(g_nᵗm̂)`
  (`ex_16_1_b_values`); it is Pareto optimal, autarky is not, and it Pareto dominates autarky
  (`ex_16_1_b_rank`); when `e₂ ≥ g_ne₁` autarky is the only equilibrium and it is Pareto
  optimal (`ex_16_1_b_autarky`). (c) Every monetary equilibrium is `1/m̂_{n+1} = x* + cλⁿ`,
  `c ≥ 0`; the rate of return on money is `g_n` for `c = 0` and tends to `R_aut = e₂/e₁` for
  `c > 0` (`ex_16_1_c`); both kinds exist (`ex_16_1_c_exist`).
* **Exercise 16.2** (the initial old also own a tree paying `d > 0` each period; constant
  population). The two-asset budget sets and equilibrium (`ox_TreeBudget`, `ox_TreeOptimal`,
  `ox_TreeEquilibrium`). (a) There is no equilibrium with valued fiat money, for any preferences
  (`ex_16_2_a`). (b) With the preferences of Exercise 16.1 the nonmonetary equilibrium is unique:
  the tree price is constant at `a* = (e₁ − e₂ − 2d + √((e₁ − e₂ − 2d)² + 8de₁))/4`
  (`ex_16_2_b_exists`, `ex_16_2_b_unique`).

**Departures (Exercise 16.2).** The exercise keeps the population growth of Exercise 16.1; with
`g_n ≠ 1` the dividend per young `dN₀/N_t` varies with `t` and the equilibria have no closed
form. We formalise constant population (`g_n = 1`), per capita: each initial old owns one tree
and one unit of money, the young hold one of each in equilibrium. The initial old consume their
resources `e₂ + q₁ + a₁ + d` (their utility maximisation, as in `OXEconomy.ox_oldOptimal_iff`).
-/

open Filter Topology

namespace Miao.OverlappingGenerations

namespace OXEconomy

variable (E : OXEconomy)

/-- **Exercise 16.1(a)** (Miao, p. 556): autarky with valueless money is the nonmonetary
equilibrium, every nonmonetary equilibrium is autarky, and the implicit interest rate is
`R_aut = e₂/e₁`. -/
theorem ex_16_1_a (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1) :
    E.ox_IsNonmonetary (fun _ => 0) (fun _ => E.ox_e1) (fun _ => E.ox_e2)
      (fun t => E.ox_M t / E.ox_N t) ∧
    (∀ q cy co m : ℕ → ℝ, E.ox_IsNonmonetary q cy co m →
      (∀ t, 1 ≤ t → cy t = E.ox_e1 ∧ co t = E.ox_e2) ∧ co 0 = E.ox_e2) ∧
    E.ox_Raut = E.ox_e2 / E.ox_e1 :=
  ⟨E.ox_autarky_isEquilibrium, fun _ _ _ _ h => E.ox_nonmonetary_autarky h, E.ox_log_Raut hdu hβ⟩

/-- **Exercise 16.1(b)** (Miao, p. 556): with `g_m = 1`, a stationary monetary equilibrium exists
iff `e₂ < g_ne₁`. -/
theorem ex_16_1_b_exists (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) :
    (∃ q cy co m : ℕ → ℝ, E.ox_IsMonetary q cy co m ∧ ∃ mh, ∀ t, 1 ≤ t → E.ox_mhat q t = mh) ↔
      E.ox_e2 < E.ox_gn * E.ox_e1 := by
  have he1 := E.ox_e1_pos
  have hiff : E.ox_Raut * E.ox_gm < E.ox_gn ↔ E.ox_e2 < E.ox_gn * E.ox_e1 := by
    rw [E.ox_log_Raut hdu hβ, hgm, mul_one, div_lt_iff₀ he1]
  constructor
  · rintro ⟨q, cy, co, m, h, -⟩
    exact hiff.1 (E.proposition_16_1_1_necessity h)
  · intro hgap
    obtain ⟨mh, -, -, h⟩ := E.proposition_16_1_1_sufficiency (hiff.2 hgap)
    exact ⟨_, _, _, _, h, mh, fun t _ => E.ox_mhat_qOf _ t⟩

/-- **Exercise 16.1(b)** (Miao, p. 556): in every stationary monetary equilibrium (with
`M₀ = N₀`, `g_m = 1`), `m̂ = (g_ne₁ − e₂)/(2g_n)`, `c_t^t = (g_ne₁ + e₂)/(2g_n)`,
`c_{t+1}^t = c₁⁰ = (g_ne₁ + e₂)/2`, `R_{t+1} = g_n` and `p_t = 1/q_t = 1/(g_nᵗm̂)`. -/
theorem ex_16_1_b_values (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) (hM : E.ox_M0 = E.ox_N0) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) {mh : ℝ} (hc : ∀ t, 1 ≤ t → E.ox_mhat q t = mh) :
    mh = (E.ox_gn * E.ox_e1 - E.ox_e2) / (2 * E.ox_gn) ∧
      (∀ t, 1 ≤ t → cy t = (E.ox_gn * E.ox_e1 + E.ox_e2) / (2 * E.ox_gn) ∧
        co t = (E.ox_gn * E.ox_e1 + E.ox_e2) / 2 ∧ q (t + 1) / q t = E.ox_gn ∧
        1 / q t = 1 / (E.ox_gn ^ t * mh)) ∧
      co 0 = (E.ox_gn * E.ox_e1 + E.ox_e2) / 2 := by
  have hgn := E.ox_gn_pos
  obtain ⟨h0, he, hroot⟩ := E.proposition_16_1_1_unique_stationary h hc
  simp only [hdu, hβ, hgm, one_mul, div_one] at hroot
  have h1 : E.ox_e1 - mh ≠ 0 := by linarith
  have h2 : E.ox_e2 + E.ox_gn * mh ≠ 0 := by nlinarith [E.ox_e2_pos]
  have hmh : mh = (E.ox_gn * E.ox_e1 - E.ox_e2) / (2 * E.ox_gn) := by
    field_simp at hroot
    rw [eq_div_iff (by nlinarith [E.ox_e2_pos])] at hroot
    rw [eq_div_iff (by positivity)]
    linarith
  obtain ⟨halloc, hco0⟩ := E.ox_monetary_alloc h
  refine ⟨hmh, fun t ht => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [(halloc t ht).2.2.2.1, hc t ht, hmh]; field_simp; ring
  · rw [(halloc t ht).2.2.2.2, hc (t + 1) (by omega), hmh]; field_simp; ring
  · rw [E.ox_stationary_R h hc ht, hgm, div_one]
  · have := hc t ht
    unfold ox_mhat ox_M ox_N at this
    rw [hM, hgm, one_pow, mul_one] at this
    rw [← this]
    have := E.ox_N0_pos.ne'
    have := (pow_pos hgn t).ne'
    field_simp
  · rw [hco0, hc 1 le_rfl, hmh]; field_simp; ring

/-- **Exercise 16.1(b)** (Miao, p. 556), the Pareto ranking: with `g_m = 1` (for any preferences,
in particular those of the exercise), the stationary monetary equilibrium is Pareto optimal,
autarky is not, and the monetary allocation makes the initial old and every generation strictly
better off than autarky. -/
theorem ex_16_1_b_rank (hgm : E.ox_gm = 1) {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m)
    {mh : ℝ}
    (hc : ∀ t, 1 ≤ t → E.ox_mhat q t = mh) :
    E.ox_ParetoOptimal cy co ∧ ¬ E.ox_ParetoOptimal (fun _ => E.ox_e1) (fun _ => E.ox_e2) ∧
      E.ox_e2 < co 0 ∧ ∀ t, 1 ≤ t → E.ox_EU E.ox_e1 E.ox_e2 < E.ox_EU (cy t) (co t) := by
  have hgn := E.ox_gn_pos
  have hR := E.proposition_16_1_1_necessity h
  obtain ⟨halloc, hco0⟩ := E.ox_monetary_alloc h
  obtain ⟨h0, -, -⟩ := E.proposition_16_1_1_unique_stationary h hc
  have hs : ox_IsStationary cy co (E.ox_e1 - mh) (E.ox_e2 + E.ox_gn * mh) := fun t ht =>
    ⟨by rw [(halloc t ht).2.2.2.1, hc t ht], by rw [(halloc t ht).2.2.2.2, hc (t + 1) (by omega)]⟩
  refine ⟨(E.proposition_16_1_3 hR h hs).2 hgm.le, ?_, ?_, fun t ht => ?_⟩
  · rw [E.proposition_16_1_2 E.ox_autarky_isEquilibrium, not_le]
    rw [hgm, mul_one] at hR; exact hR
  · rw [hco0, hc 1 le_rfl]; nlinarith
  · have hc1 := (h.1.2.1 t ht).1.2.1
    have hc2 := (h.1.2.1 t ht).1.2.2.1
    have heul := E.eq_16_4 h ht
    rw [E.ox_stationary_R h hc ht, hgm, div_one] at heul
    have hd2 := E.ox_P.ox_du_pos _ hc2
    have hβ0 := E.ox_P.ox_β_pos
    rw [div_eq_iff (by positivity)] at heul
    refine E.ox_P.ox_line_optimal_strict hc1 hc2 hgn (by rw [heul]; ring) E.ox_e1_pos
      E.ox_e2_pos ?_ (Or.inl ?_)
    · rw [(hs t ht).1, (hs t ht).2]; field_simp; ring_nf; rfl
    · rw [(hs t ht).1]; linarith

/-- **Exercise 16.1(b)** (Miao, p. 556): when `e₂ ≥ g_ne₁` there is no monetary equilibrium and
autarky, the only equilibrium, is Pareto optimal. -/
theorem ex_16_1_b_autarky (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) (hge : E.ox_gn * E.ox_e1 ≤ E.ox_e2) :
    (¬ ∃ q cy co m : ℕ → ℝ, E.ox_IsMonetary q cy co m) ∧
      E.ox_ParetoOptimal (fun _ => E.ox_e1) (fun _ => E.ox_e2) := by
  have he1 := E.ox_e1_pos
  refine ⟨fun ⟨q, cy, co, m, h⟩ => ?_, ?_⟩
  · have := E.proposition_16_1_1_necessity h
    rw [E.ox_log_Raut hdu hβ, hgm, mul_one, div_lt_iff₀ he1] at this
    linarith
  · rw [E.proposition_16_1_2 E.ox_autarky_isEquilibrium, E.ox_log_Raut hdu hβ, le_div_iff₀ he1]
    exact hge

/-- **Exercise 16.1(c)** (Miao, p. 556): every monetary equilibrium (with `g_m = 1`) has
`1/m̂_{n+1} = x* + cλⁿ` with `c ≥ 0`; if `c = 0` the rate of return on money is `R_{t+1} = g_n`
for all `t`, and if `c > 0` it tends to `R_aut = e₂/e₁`. -/
theorem ex_16_1_c (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) :
    ∃ c, 0 ≤ c ∧ (∀ n : ℕ, (E.ox_mhat q (n + 1))⁻¹ =
      2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) + c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ n) ∧
      (c = 0 → ∀ t, 1 ≤ t → q (t + 1) / q t = E.ox_gn) ∧
      (0 < c → Tendsto (fun t => q (t + 1) / q t) atTop (𝓝 (E.ox_e2 / E.ox_e1))) := by
  obtain ⟨hgap, c, hc, hx⟩ := E.ox_log_paths hdu hβ hgm h
  refine ⟨c, hc, hx, fun h0 t ht => ?_, fun hc0 => ?_⟩
  · have hconst : ∀ t, 1 ≤ t → E.ox_mhat q t = (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2))⁻¹ :=
      fun t ht => by
        obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
        have := hx n
        rw [h0, zero_mul, add_zero] at this
        rw [← this, inv_inv]
    rw [E.ox_stationary_R h hconst ht, hgm, div_one]
  · have hlam : 1 < E.ox_gn * E.ox_e1 / E.ox_e2 := (one_lt_div E.ox_e2_pos).2 hgap
    have ht : Tendsto (fun n => E.ox_mhat q (n + 1)) atTop (𝓝 0) := by
      have : (fun n => E.ox_mhat q (n + 1)) = fun n =>
          (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
            c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ n)⁻¹ := funext fun n => by rw [← hx n, inv_inv]
      rw [this]
      exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _
        ((tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop hc0))
    have := (E.ox_R_tendsto_Raut h ((tendsto_add_atTop_iff_nat 1).1 ht)).1
    rwa [E.ox_log_Raut hdu hβ] at this

/-- **Exercise 16.1(c)** (Miao, p. 556): when `e₂ < g_ne₁` both kinds of monetary equilibrium
exist: the stationary one (`c = 0`) and, for every `c > 0`, one whose real balances vanish. -/
theorem ex_16_1_c_exist (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) (hgap : E.ox_e2 < E.ox_gn * E.ox_e1) {c : ℝ} (hc : 0 ≤ c) :
    ∃ q cy co m : ℕ → ℝ, E.ox_IsMonetary q cy co m ∧ ∀ n : ℕ, (E.ox_mhat q (n + 1))⁻¹ =
      2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) + c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ n :=
  ⟨_, _, _, _, E.ox_log_construct hdu hβ hgm hgap hc, fun n => by
    rw [E.ox_mhat_qOf, inv_inv, Nat.add_sub_cancel]⟩

end OXEconomy

namespace OXPrefs

variable (P : OXPrefs)

/-- Exercise 16.2 (Miao, p. 556): the budget set of a young agent at `t` who can hold money (value
`q_t`) and trees (price `a_t`, dividend `d`), per capita with constant population. -/
def ox_TreeBudget (e1 e2 d : ℝ) (q a : ℕ → ℝ) (t : ℕ) (c1 c2 m x : ℝ) : Prop :=
  0 ≤ m ∧ 0 ≤ x ∧ 0 < c1 ∧ 0 < c2 ∧ c1 + q t * m + a t * x ≤ e1 ∧
    c2 ≤ e2 + q (t + 1) * m + (a (t + 1) + d) * x

/-- Exercise 16.2: an optimal choice of the young at `t`. -/
def ox_TreeOptimal (e1 e2 d : ℝ) (q a : ℕ → ℝ) (t : ℕ) (c1 c2 m x : ℝ) : Prop :=
  ox_TreeBudget e1 e2 d q a t c1 c2 m x ∧
    ∀ c1' c2' m' x', ox_TreeBudget e1 e2 d q a t c1' c2' m' x' → P.ox_U c1' c2' ≤ P.ox_U c1 c2

/-- Exercise 16.2: an equilibrium of the economy with money and trees: nonnegative prices, the
young optimise holding one unit of money and one tree each (market clearing), the initial old
consume their resources, and the goods market clears. -/
def ox_TreeEquilibrium (e1 e2 d : ℝ) (q a cy co : ℕ → ℝ) : Prop :=
  (∀ t, 1 ≤ t → 0 ≤ q t ∧ 0 ≤ a t) ∧
    (∀ t, 1 ≤ t → P.ox_TreeOptimal e1 e2 d q a t (cy t) (co t) 1 1) ∧
    co 0 = e2 + q 1 + a 1 + d ∧ ∀ t, 1 ≤ t → cy t + co (t - 1) = e1 + e2 + d

/-- In the tree economy optimal choices exhaust both budget constraints. -/
theorem ox_tree_binds {e1 e2 d : ℝ} {q a : ℕ → ℝ} {t : ℕ} {c1 c2 m x : ℝ}
    (h : P.ox_TreeOptimal e1 e2 d q a t c1 c2 m x) :
    c1 = e1 - q t * m - a t * x ∧ c2 = e2 + q (t + 1) * m + (a (t + 1) + d) * x := by
  obtain ⟨⟨hm, hx, h1, h2, hb1, hb2⟩, hmax⟩ := h
  constructor
  · by_contra hne
    have hlt : c1 < e1 - q t * m - a t * x := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · linarith
    have := hmax (e1 - q t * m - a t * x) c2 m x ⟨hm, hx, by linarith, h2, by linarith, hb2⟩
    have hu := P.ox_u_lt h1 hlt
    unfold ox_U at this
    linarith
  · by_contra hne
    have hlt : c2 < e2 + q (t + 1) * m + (a (t + 1) + d) * x := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · linarith
    have := hmax c1 _ m x ⟨hm, hx, h1, by linarith, hb1, le_rfl⟩
    have hu := mul_lt_mul_of_pos_left (P.ox_u_lt h2 hlt) P.ox_β_pos
    unfold ox_U at this
    linarith

/-- In the tree economy, with `d > 0` and nonnegative next-period prices, the tree price is
positive (a free tree would be demanded without bound). -/
theorem ox_tree_price_pos {e1 e2 d : ℝ} (hd : 0 < d) {q a : ℕ → ℝ} {t : ℕ} {c1 c2 m x : ℝ}
    (h : P.ox_TreeOptimal e1 e2 d q a t c1 c2 m x) (ha : 0 ≤ a t) (ha1 : 0 ≤ a (t + 1)) :
    0 < a t := by
  rcases eq_or_lt_of_le ha with h0 | h0
  · exfalso
    obtain ⟨⟨hm, hx, h1, h2, hb1, hb2⟩, hmax⟩ := h
    have := hmax c1 (c2 + d) m (x + 1) ⟨hm, by linarith, h1, by linarith,
      by rw [← h0] at hb1 ⊢; linarith, by nlinarith⟩
    have hu := mul_lt_mul_of_pos_left (P.ox_u_lt h2 (show c2 < c2 + d by linarith)) P.ox_β_pos
    unfold ox_U at this
    linarith
  · exact h0

/-- Exercise 16.2: the first-order conditions of the tree economy at a choice with positive
holdings of an asset: for trees `a_tu'(c₁) = β(a_{t+1} + d)u'(c₂)`, for money
`q_tu'(c₁) = βq_{t+1}u'(c₂)`. -/
theorem ox_tree_foc {e1 e2 d : ℝ} {q a : ℕ → ℝ} {t : ℕ} {c1 c2 m x : ℝ}
    (h : P.ox_TreeOptimal e1 e2 d q a t c1 c2 m x) :
    (0 < x → a t * P.ox_du c1 = P.ox_β * (a (t + 1) + d) * P.ox_du c2) ∧
      (0 < m → q t * P.ox_du c1 = P.ox_β * q (t + 1) * P.ox_du c2) := by
  obtain ⟨b1, b2⟩ := P.ox_tree_binds h
  obtain ⟨⟨hm, hx, h1, h2, _, _⟩, hmax⟩ := h
  refine ⟨fun hx0 => P.ox_foc h1 h2 ?_, fun hm0 => P.ox_foc h1 h2 ?_⟩
  · filter_upwards [ox_eventually_pos c1 (-a t) h1, ox_eventually_pos c2 (a (t + 1) + d) h2,
      ox_eventually_pos x 1 hx0] with s hs1 hs2 hs3
    exact hmax _ _ m (x + s) ⟨hm, by linarith, by linarith, hs2, by rw [b1]; linarith,
      by rw [b2]; linarith⟩
  · filter_upwards [ox_eventually_pos c1 (-q t) h1, ox_eventually_pos c2 (q (t + 1)) h2,
      ox_eventually_pos m 1 hm0] with s hs1 hs2 hs3
    exact hmax _ _ (m + s) x ⟨by linarith, hx, by linarith, hs2, by rw [b1]; linarith,
      by rw [b2]; linarith⟩

/-- **Exercise 16.2(a)** (Miao, p. 556): with a tree paying `d > 0`, there is no equilibrium with
valued fiat money (for any preferences). Money and trees must earn the same return,
`q_{t+1}/q_t = (a_{t+1} + d)/a_t`, so `a_t/q_t` falls by `d/q_{t+1} > d/e₁` every period. -/
theorem ex_16_2_a {e1 e2 d : ℝ} (hd : 0 < d) :
    ¬ ∃ q a cy co : ℕ → ℝ, P.ox_TreeEquilibrium e1 e2 d q a cy co ∧ ∀ t, 1 ≤ t → 0 < q t := by
  rintro ⟨q, a, cy, co, ⟨hprice, hopt, -, -⟩, hq⟩
  have hβ := P.ox_β_pos
  have hapos : ∀ t, 1 ≤ t → 0 < a t := fun t ht =>
    P.ox_tree_price_pos hd (hopt t ht) (hprice t ht).2 (hprice (t + 1) (by omega)).2
  have he1 : ∀ t, 1 ≤ t → q t < e1 := fun t ht => by
    obtain ⟨⟨-, -, h1, -, hb1, -⟩, -⟩ := hopt t ht
    have := (hprice t ht).2
    linarith
  set b := fun t => a t / q t
  have hstep : ∀ t, 1 ≤ t → b (t + 1) = b t - d / q (t + 1) := fun t ht => by
    obtain ⟨hx, hm⟩ := P.ox_tree_foc (hopt t ht)
    have hx1 := hx one_pos
    have hm1 := hm one_pos
    obtain ⟨⟨-, -, h1, h2, -, -⟩, -⟩ := hopt t ht
    have hd1 := P.ox_du_pos _ h1
    have hd2 := P.ox_du_pos _ h2
    have hqt := hq t ht
    have hqt1 := hq (t + 1) (by omega)
    have harb : a t * q (t + 1) = q t * (a (t + 1) + d) := by
      have key : (a t * q (t + 1) - q t * (a (t + 1) + d)) * (P.ox_β * P.ox_du (co t)) = 0 := by
        linear_combination q t * hx1 - a t * hm1
      have hne : P.ox_β * P.ox_du (co t) ≠ 0 := by positivity
      have := (mul_eq_zero.1 key).resolve_right hne
      linarith
    simp only [b]
    field_simp
    linear_combination -harb
  have hdec : ∀ n : ℕ, b (n + 1) ≤ b 1 - n * (d / e1) := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hstep (n + 1) (by omega)
      have hqn := hq (n + 2) (by omega)
      have hlt := he1 (n + 2) (by omega)
      have : d / e1 ≤ d / q (n + 1 + 1) := div_le_div_of_nonneg_left hd.le hqn hlt.le
      rw [hs]; push_cast; linarith
  have he1pos : 0 < e1 := lt_trans (hq 1 le_rfl) (he1 1 le_rfl)
  obtain ⟨n, hn⟩ := exists_nat_gt (b 1 / (d / e1))
  have hpos : 0 < b (n + 1) := div_pos (hapos (n + 1) (by omega)) (hq (n + 1) (by omega))
  have := hdec n
  rw [div_lt_iff₀ (by positivity)] at hn
  linarith

/-- The constant tree price of Exercise 16.2(b):
`a* = (e₁ − e₂ − 2d + √((e₁ − e₂ − 2d)² + 8de₁))/4`. -/
noncomputable def ox_astar (e1 e2 d : ℝ) : ℝ :=
  (e1 - e2 - 2 * d + Real.sqrt ((e1 - e2 - 2 * d) ^ 2 + 8 * d * e1)) / 4

/-- Exercise 16.2(b): `a* > 0`, `e₁ − 2a* > 0` and `(a* + d)(e₁ − 2a*) = a*e₂`, the steady state
of the tree-price equation `(a_{t+1} + d)(e₁ − 2a_t) = a_te₂`. -/
theorem ox_astar_spec {e1 e2 d : ℝ} (he1 : 0 < e1) (he2 : 0 < e2) (hd : 0 < d) :
    0 < ox_astar e1 e2 d ∧ 0 < e1 - 2 * ox_astar e1 e2 d ∧
      (ox_astar e1 e2 d + d) * (e1 - 2 * ox_astar e1 e2 d) = ox_astar e1 e2 d * e2 := by
  have hD : 0 ≤ (e1 - e2 - 2 * d) ^ 2 + 8 * d * e1 := by positivity
  have hS := Real.sq_sqrt hD
  have hS0 := Real.sqrt_nonneg ((e1 - e2 - 2 * d) ^ 2 + 8 * d * e1)
  have hSB : |e1 - e2 - 2 * d| < Real.sqrt ((e1 - e2 - 2 * d) ^ 2 + 8 * d * e1) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  have hpos : 0 < ox_astar e1 e2 d := by
    unfold ox_astar
    have := neg_abs_le (e1 - e2 - 2 * d)
    exact div_pos (by linarith) (by norm_num)
  have hrel : (ox_astar e1 e2 d + d) * (e1 - 2 * ox_astar e1 e2 d) = ox_astar e1 e2 d * e2 := by
    unfold ox_astar
    linear_combination (-1 / 8 : ℝ) * hS
  refine ⟨hpos, ?_, hrel⟩
  by_contra hle
  have : (ox_astar e1 e2 d + d) * (e1 - 2 * ox_astar e1 e2 d) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 hle)
  nlinarith

/-- **Exercise 16.2(b)** (Miao, p. 556): with the preferences of Exercise 16.1 (`u = ln`, `β = 1`)
the constant tree price `a*` with valueless money is a nonmonetary equilibrium:
`c_t^t = e₁ − a*`, `c_{t+1}^t = e₂ + a* + d`. -/
theorem ex_16_2_b_exists (hdu : P.ox_du = fun c => c⁻¹) (hβ : P.ox_β = 1) {e1 e2 d : ℝ}
    (he1 : 0 < e1) (he2 : 0 < e2) (hd : 0 < d) :
    P.ox_TreeEquilibrium e1 e2 d (fun _ => 0) (fun _ => ox_astar e1 e2 d)
      (fun _ => e1 - ox_astar e1 e2 d) (fun _ => e2 + ox_astar e1 e2 d + d) := by
  obtain ⟨ha, hea, hrel⟩ := ox_astar_spec he1 he2 hd
  set A := ox_astar e1 e2 d
  have hc1 : 0 < e1 - A := by linarith
  have hc2 : 0 < e2 + A + d := by linarith
  refine ⟨fun _ _ => ⟨le_rfl, ha.le⟩, fun t _ => ⟨⟨zero_le_one, zero_le_one, hc1, hc2,
    by linarith, by linarith⟩, fun c1' c2' m' x' hb => ?_⟩, by ring, fun _ _ => by ring⟩
  obtain ⟨-, hx', h1', h2', hb1, hb2⟩ := hb
  have hR : 0 < (A + d) / A := by positivity
  refine P.ox_line_optimal hc1 hc2 hR ?_ h1' h2' ?_
  · simp only [hdu, hβ, one_mul]
    field_simp
    linear_combination (-1 : ℝ) * hrel
  · simp only [zero_mul, add_zero] at hb1 hb2
    have : c2' / ((A + d) / A) ≤ (e2 + (A + d) * x') / ((A + d) / A) :=
      div_le_div_of_nonneg_right hb2 hR.le
    have e1' : (e2 + (A + d) * x') / ((A + d) / A) = e2 / ((A + d) / A) + A * x' := by
      field_simp
    have e2' : (e2 + A + d) / ((A + d) / A) = e2 / ((A + d) / A) + A := by
      field_simp; ring
    rw [e2']; linarith

/-- **Exercise 16.2(b)** (Miao, p. 556): with the preferences of Exercise 16.1 every nonmonetary
equilibrium has the constant tree price `a_t = a*`: deviations from `a*` grow by at least
`e₂/(e₁ − 2a*) > 1` per period and would leave `(0, e₁)`. -/
theorem ex_16_2_b_unique (hdu : P.ox_du = fun c => c⁻¹) (hβ : P.ox_β = 1) {e1 e2 d : ℝ}
    (he1 : 0 < e1) (he2 : 0 < e2) (hd : 0 < d) {q a cy co : ℕ → ℝ}
    (h : P.ox_TreeEquilibrium e1 e2 d q a cy co) (hq : ∀ t, 1 ≤ t → q t = 0) :
    ∀ t, 1 ≤ t → a t = ox_astar e1 e2 d := by
  obtain ⟨hA, hea, hrelA⟩ := ox_astar_spec he1 he2 hd
  set A := ox_astar e1 e2 d
  obtain ⟨hprice, hopt, -, -⟩ := h
  have hapos : ∀ t, 1 ≤ t → 0 < a t := fun t ht =>
    P.ox_tree_price_pos hd (hopt t ht) (hprice t ht).2 (hprice (t + 1) (by omega)).2
  -- the tree-price difference equation
  have hrel : ∀ t, 1 ≤ t → (a (t + 1) + d) * (e1 - 2 * a t) = a t * e2 := fun t ht => by
    have hfoc := (P.ox_tree_foc (hopt t ht)).1 one_pos
    obtain ⟨b1, b2⟩ := P.ox_tree_binds (hopt t ht)
    obtain ⟨⟨-, -, h1, h2, -, -⟩, -⟩ := hopt t ht
    rw [b1, hq t ht] at h1 hfoc
    rw [b2, hq (t + 1) (by omega)] at h2 hfoc
    simp only [hdu, hβ, one_mul, sub_zero, add_zero, mul_one] at hfoc h1 h2
    field_simp at hfoc
    linear_combination (-1 : ℝ) * hfoc
  have hlt : ∀ t, 1 ≤ t → a t < e1 := fun t ht => by
    obtain ⟨⟨-, -, h1, -, hb1, -⟩, -⟩ := hopt t ht
    have := (hprice t ht).1
    nlinarith [hq t ht]
  have hgap : ∀ t, 1 ≤ t → 0 < e1 - 2 * a t := fun t ht => by
    have h1 := hrel t ht
    have := hapos (t + 1) (by omega)
    by_contra hle
    have : (a (t + 1) + d) * (e1 - 2 * a t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 hle)
    nlinarith [hapos t ht]
  set k := e2 / (e1 - 2 * A)
  have hk : 1 < k := by
    rw [one_lt_div hea]
    nlinarith
  -- deviations grow geometrically
  have hdev : ∀ t, 1 ≤ t → k * |a t - A| ≤ |a (t + 1) - A| := fun t ht => by
    have hid : (a (t + 1) - A) * (e1 - 2 * a t) * (e1 - 2 * A) = e1 * e2 * (a t - A) := by
      linear_combination (e1 - 2 * A) * hrel t ht - (e1 - 2 * a t) * hrelA
    have hg := hgap t ht
    have hle : e1 - 2 * a t ≤ e1 := by linarith [hapos t ht]
    have habs := congrArg abs hid
    simp only [abs_mul, abs_of_pos hg, abs_of_pos hea, abs_of_pos he1, abs_of_pos he2] at habs
    simp only [k]
    rw [div_mul_eq_mul_div, div_le_iff₀ hea]
    have h0 := abs_nonneg (a (t + 1) - A)
    have h1 : e1 * (e2 * |a t - A|) ≤ e1 * (|a (t + 1) - A| * (e1 - 2 * A)) := by
      calc e1 * (e2 * |a t - A|) = |a (t + 1) - A| * (e1 - 2 * a t) * (e1 - 2 * A) := by
            linarith
        _ ≤ |a (t + 1) - A| * e1 * (e1 - 2 * A) := by
            apply mul_le_mul_of_nonneg_right _ hea.le
            exact mul_le_mul_of_nonneg_left hle h0
        _ = e1 * (|a (t + 1) - A| * (e1 - 2 * A)) := by ring
    exact le_of_mul_le_mul_left h1 he1
  intro t ht
  by_contra hne
  have hpos : 0 < |a t - A| := abs_pos.2 (sub_ne_zero.2 hne)
  have hgrow : ∀ j, k ^ j * |a t - A| ≤ |a (t + j) - A| := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      calc k ^ (j + 1) * |a t - A| = k * (k ^ j * |a t - A|) := by ring
        _ ≤ k * |a (t + j) - A| := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ |a (t + j + 1) - A| := hdev (t + j) (by omega)
  have hbdd : ∀ j, |a (t + j) - A| ≤ e1 + A := fun j => by
    have h1 := hapos (t + j) (by omega)
    have h2 := hlt (t + j) (by omega)
    rw [abs_le]; constructor <;> linarith
  have htend : Tendsto (fun j => k ^ j * |a t - A|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hk).atTop_mul_const hpos
  obtain ⟨j, hj⟩ := (htend.eventually_gt_atTop (e1 + A)).exists
  linarith [hgrow j, hbdd j]

end OXPrefs

end Miao.OverlappingGenerations
