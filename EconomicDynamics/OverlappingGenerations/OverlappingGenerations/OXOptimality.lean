/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.OXOfferCurve
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Pareto optimality in the exchange economy

Miao, §16.1, pp. 538–544.

* **Definition 16.1.1** (feasibility (16.9), equivalent to (16.3): `definition_16_1_1`),
  **Definition 16.1.2** (`ox_ParetoOptimal`), **Definition 16.1.3** (`ox_IsStationary`).
* The general stationary criterion behind Propositions 16.1.2–16.1.3: a feasible stationary
  allocation `(c₁, c₂)` with `R = u'(c₁)/(βu'(c₂))` is Pareto optimal iff `R ≥ g_n`
  (`ox_stationary_optimal`, `ox_stationary_not_optimal`, `ox_stationary_optimal_iff`). The
  steps of the book's proof: the perturbations `ε_t = c₁ − c̃_t^t` satisfy `ε_t ≥ 0` (16.10)
  (`eq_16_10`), `g_nε_{t+1} ≥ Rε_t` with strict inequality when `ε_t ≠ 0` (the content of
  `c̄ − e₂ = ε(R_aut + f(ε))`, `f(ε) > 0`: `eq_16_11`), and grow geometrically
  (`ox_eps_geometric`); the transfer scheme `f(ε) = u(e₁ − ε) + βu(e₂ + g_nε)` with
  `f'(0) = −u'(e₁) + βg_nu'(e₂)` (`proposition_16_1_2_transfer`).
* **Proposition 16.1.2**: autarky is optimal iff `R_aut ≥ g_n` (`proposition_16_1_2`).
* (16.12) (`eq_16_12`), (16.13) (`eq_16_13`), **Proposition 16.1.3** (`proposition_16_1_3`),
  and the steps of the book's necessity proof (`proposition_16_1_3_steps`).
* Balasko–Shell (Miao, pp. 542–544): `∏_{s=1}^t R_{s+1} = 1/p_{t+1}` when `p₁ = 1`, so the two
  forms of the criterion agree (`ox_balasko_shell_prod`, `ox_balasko_shell_equiv`); the
  compensating transfers `δ_t = δ₀∏R_{s+1}` (`ox_balasko_shell_transfers`); and the criterion
  for stationary allocations with constant population (`ox_balasko_shell_stationary`). The
  general Balasko–Shell theorem is cited, not proved, by the book; it is not formalised.

**Departures.** (i) Feasible allocations have positive consumption. (ii) The book's
sufficiency proof for Proposition 16.1.2 starts from the first date at which the alternative
allocation differs and represents the indifference curve as `h(c₁) = h(e₁) + (e₁ − c₁)(−h'(e₁) +
f(e₁ − c₁))` (16.11). Here the same estimate is obtained from strict concavity directly: the
tangent-line inequality gives `g_nε_{t+1} ≥ R_autε_t` (strict for `ε_t ≠ 0`) and a uniform chord
bound (`OXPrefs.ox_chord`) replaces `f(ε_{t+j}) ≥ f(ε_{t+1})`. (iii) The necessity half of
Proposition 16.1.3 is proved by the `ε`-transfer of Proposition 16.1.2 rather than by revealed
preference (Figure 16.5); the book's steps (the budget line is flatter, the initial old gain)
are recorded in `proposition_16_1_3_steps`.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

namespace OXEconomy

variable (E : OXEconomy)

/-- **Definition 16.1.1** (Miao, p. 538): an allocation (`cy t = c_t^t`, `co t = c_{t+1}^t`,
`co 0 = c₁⁰`) is feasible if consumption is positive and (16.9) holds:
`g_n c_t^t + c_t^{t−1} = g_n e₁ + e₂`, `t ≥ 1`. -/
def ox_Feasible (cy co : ℕ → ℝ) : Prop :=
  (∀ t, 1 ≤ t → 0 < cy t) ∧ (∀ t, 0 < co t) ∧
    ∀ t, 1 ≤ t → E.ox_gn * cy t + co (t - 1) = E.ox_gn * E.ox_e1 + E.ox_e2

/-- **Definition 16.1.1** (Miao, p. 538): (16.3) is equivalent to (16.9). -/
theorem definition_16_1_1 (cy co : ℕ → ℝ) :
    (∀ t, 1 ≤ t → E.ox_N t * cy t + E.ox_N (t - 1) * co (t - 1) =
      E.ox_N t * E.ox_e1 + E.ox_N (t - 1) * E.ox_e2) ↔
    ∀ t, 1 ≤ t → E.ox_gn * cy t + co (t - 1) = E.ox_gn * E.ox_e1 + E.ox_e2 := by
  refine forall_congr' fun t => imp_congr_right fun ht => ?_
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel, E.ox_N_succ]
  have hN := E.ox_N_pos s
  constructor
  · intro h
    have : E.ox_N s * (E.ox_gn * cy (s + 1) + co s) =
        E.ox_N s * (E.ox_gn * E.ox_e1 + E.ox_e2) := by linarith
    exact mul_left_cancel₀ hN.ne' this
  · intro h
    linear_combination E.ox_N s * h

/-- **Definition 16.1.2** (Miao, p. 539): a feasible allocation is Pareto optimal if no feasible
allocation gives the initial old at least as much consumption and every generation `t ≥ 1` at
least as much utility, with one strict inequality. -/
def ox_ParetoOptimal (cy co : ℕ → ℝ) : Prop :=
  E.ox_Feasible cy co ∧ ¬ ∃ cy' co' : ℕ → ℝ, E.ox_Feasible cy' co' ∧ co 0 ≤ co' 0 ∧
    (∀ t, 1 ≤ t → E.ox_EU (cy t) (co t) ≤ E.ox_EU (cy' t) (co' t)) ∧
    (co 0 < co' 0 ∨ ∃ t, 1 ≤ t ∧ E.ox_EU (cy t) (co t) < E.ox_EU (cy' t) (co' t))

/-- **Definition 16.1.3** (Miao, p. 539): an allocation is stationary, `c_t^t = c_y` and
`c_{t+1}^t = c_o` for all `t ≥ 1` (`c₁⁰` unrestricted). -/
def ox_IsStationary (cy co : ℕ → ℝ) (c1 c2 : ℝ) : Prop :=
  ∀ t, 1 ≤ t → cy t = c1 ∧ co t = c2

/-- Miao, (16.12), p. 541: a stationary allocation with positive consumption is feasible iff
`c₁ + c₂/g_n = e₁ + e₂/g_n` and `c₁⁰ = c₂`. -/
theorem eq_16_12 {cy co : ℕ → ℝ} {c1 c2 : ℝ} (hs : ox_IsStationary cy co c1 c2)
    (h1 : 0 < c1) (h2 : 0 < c2) :
    E.ox_Feasible cy co ↔ c1 + c2 / E.ox_gn = E.ox_e1 + E.ox_e2 / E.ox_gn ∧ co 0 = c2 := by
  have hgn := E.ox_gn_pos
  constructor
  · rintro ⟨-, -, hf⟩
    have hf1 := hf 1 le_rfl
    have hf2 := hf 2 (by omega)
    simp only [Nat.sub_self, Nat.add_one_sub_one] at hf1 hf2
    rw [(hs 1 le_rfl).1] at hf1
    rw [(hs 2 (by omega)).1, (hs 1 le_rfl).2] at hf2
    refine ⟨?_, by linarith⟩
    field_simp
    linarith
  · rintro ⟨hl, h0⟩
    have hl' : E.ox_gn * c1 + c2 = E.ox_gn * E.ox_e1 + E.ox_e2 := by
      field_simp at hl; linarith
    refine ⟨fun t ht => (hs t ht).1 ▸ h1, fun t => ?_, fun t ht => ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · rw [h, h0]; exact h2
      · rw [(hs t h).2]; exact h2
    · rw [(hs t ht).1]
      rcases Nat.eq_zero_or_pos (t - 1) with h | h
      · rw [h, h0]; exact hl'
      · rw [(hs (t - 1) h).2]; exact hl'

/-- Feasibility relative to a feasible stationary `(c₁, c₂)`: the old's consumption is
`c̃_{t+1}^t = c₂ + g_n(c₁ − c̃_{t+1}^{t+1})` (Miao, p. 540, "since `C̃` is feasible"). -/
theorem ox_feasible_old {c1 c2 : ℝ}
    (hl : E.ox_gn * c1 + c2 = E.ox_gn * E.ox_e1 + E.ox_e2)
    {cy' co' : ℕ → ℝ} (hF : E.ox_Feasible cy' co') (t : ℕ) :
    co' t = c2 + E.ox_gn * (c1 - cy' (t + 1)) := by
  have := hF.2.2 (t + 1) (by omega)
  simp only [Nat.add_sub_cancel] at this
  linarith

/-- Miao, (16.11), p. 540 (the content of (16.11) and of
`c̃_{t+2}^{t+1} − e₂ ≥ ε_{t+1}[R_aut + f(ε_{t+1})]`): if a generation is not worse off than at the
stationary `(c₁, c₂)`, then with `R = u'(c₁)/(βu'(c₂))`, `ε = c₁ − c̃₁`:
`c̃₂ − c₂ ≥ Rε`, strictly if `ε ≠ 0`. -/
theorem eq_16_11 {c1 c2 x y : ℝ} (h1 : 0 < c1) (h2 : 0 < c2) (hx : 0 < x) (hy : 0 < y)
    (hU : E.ox_EU c1 c2 ≤ E.ox_EU x y) :
    E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) * (c1 - x) ≤ y - c2 ∧
      (x ≠ c1 → E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) * (c1 - x) < y - c2) := by
  have hβ := E.ox_P.ox_β_pos
  have hd2 := E.ox_P.ox_du_pos _ h2
  have hk : 0 < E.ox_P.ox_β * E.ox_P.ox_du c2 := mul_pos hβ hd2
  have t2 := mul_le_mul_of_nonneg_left (E.ox_P.ox_tangent h2 hy) hβ.le
  unfold ox_EU OXPrefs.ox_U at hU
  have key : E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) * (c1 - x) =
      E.ox_P.ox_du c1 * (c1 - x) / (E.ox_P.ox_β * E.ox_P.ox_du c2) := by ring
  rw [key]
  constructor
  · rw [div_le_iff₀ hk]
    have t1 := E.ox_P.ox_tangent h1 hx
    nlinarith
  · intro hne
    rw [div_lt_iff₀ hk]
    have t1 := E.ox_P.ox_tangent_strict h1 hx hne
    nlinarith

/-- Miao, p. 540 (geometric growth of the perturbations): given `0 < ε₀ < c₁`, there is
`ρ > u'(c₁)/(βu'(c₂))` such that whenever a generation is not worse off than at `(c₁, c₂)` with
`ε = c₁ − c̃₁ ≥ ε₀`, `c̃₂ − c₂ ≥ ρε`. -/
theorem ox_eps_geometric {c1 c2 ε₀ : ℝ} (h2 : 0 < c2) (hε₀ : 0 < ε₀) (hε₀c : ε₀ < c1) :
    ∃ ρ, E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) < ρ ∧ ∀ x y, 0 < x → 0 < y →
      ε₀ ≤ c1 - x → E.ox_EU c1 c2 ≤ E.ox_EU x y → ρ * (c1 - x) ≤ y - c2 := by
  obtain ⟨κ, hκ, hch⟩ := E.ox_P.ox_chord hε₀ hε₀c
  have hβ := E.ox_P.ox_β_pos
  have hd2 := E.ox_P.ox_du_pos _ h2
  have hk : 0 < E.ox_P.ox_β * E.ox_P.ox_du c2 := mul_pos hβ hd2
  refine ⟨κ / (E.ox_P.ox_β * E.ox_P.ox_du c2), div_lt_div_of_pos_right hκ hk,
    fun x y hx hy hε hU => ?_⟩
  have hc := hch (c1 - x) hε (by linarith)
  rw [sub_sub_cancel] at hc
  have t2 := mul_le_mul_of_nonneg_left (E.ox_P.ox_tangent h2 hy) hβ.le
  unfold ox_EU OXPrefs.ox_U at hU
  rw [div_mul_eq_mul_div, div_le_iff₀ hk]
  nlinarith

/-- The perturbations in the sufficiency proof of Proposition 16.1.2: with `R ≥ g_n`, the
sequence `ε_t = c₁ − c̃_t^t` is nonnegative and nondecreasing (Miao, (16.10), p. 539). -/
theorem eq_16_10 {cy co : ℕ → ℝ} {c1 c2 : ℝ} (hs : ox_IsStationary cy co c1 c2)
    (h1 : 0 < c1) (h2 : 0 < c2) (h0 : co 0 = c2)
    (hl : E.ox_gn * c1 + c2 = E.ox_gn * E.ox_e1 + E.ox_e2)
    (hR : E.ox_gn ≤ E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2))
    {cy' co' : ℕ → ℝ} (hF : E.ox_Feasible cy' co') (h0' : co 0 ≤ co' 0)
    (hU : ∀ t, 1 ≤ t → E.ox_EU (cy t) (co t) ≤ E.ox_EU (cy' t) (co' t)) (n : ℕ) :
    0 ≤ c1 - cy' (n + 1) ∧ c1 - cy' (n + 1) ≤ c1 - cy' (n + 2) := by
  have hgn := E.ox_gn_pos
  have hco := E.ox_feasible_old hl hF
  have hstep : ∀ n, 0 ≤ c1 - cy' (n + 1) → c1 - cy' (n + 1) ≤ c1 - cy' (n + 2) := fun n hn => by
    have hUn := hU (n + 1) (by omega)
    rw [(hs (n + 1) (by omega)).1, (hs (n + 1) (by omega)).2] at hUn
    have := (E.eq_16_11 h1 h2 (hF.1 (n + 1) (by omega)) (hF.2.1 (n + 1)) hUn).1
    rw [hco (n + 1)] at this
    have : E.ox_gn * (c1 - cy' (n + 1)) ≤ E.ox_gn * (c1 - cy' (n + 2)) := by
      nlinarith [mul_le_mul_of_nonneg_right hR hn]
    exact le_of_mul_le_mul_left this hgn
  have hnn : ∀ n, 0 ≤ c1 - cy' (n + 1) := fun n => by
    induction n with
    | zero =>
      have := hco 0
      rw [h0] at h0'
      nlinarith
    | succ n ih => exact ih.trans (hstep n ih)
  exact ⟨hnn n, hstep n (hnn n)⟩

/-- Miao, pp. 539–540 (the sufficiency argument of Proposition 16.1.2, for any feasible stationary
allocation): if `(c₁, c₂)` is feasible and `R = u'(c₁)/(βu'(c₂)) ≥ g_n`, it is Pareto optimal. -/
theorem ox_stationary_optimal {cy co : ℕ → ℝ} {c1 c2 : ℝ} (hs : ox_IsStationary cy co c1 c2)
    (h1 : 0 < c1) (h2 : 0 < c2) (hF : E.ox_Feasible cy co)
    (hR : E.ox_gn ≤ E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2)) :
    E.ox_ParetoOptimal cy co := by
  obtain ⟨hl0, h0⟩ := (E.eq_16_12 hs h1 h2).1 hF
  have hgn := E.ox_gn_pos
  have hl : E.ox_gn * c1 + c2 = E.ox_gn * E.ox_e1 + E.ox_e2 := by
    field_simp at hl0; linarith
  refine ⟨hF, ?_⟩
  rintro ⟨cy', co', hF', h0', hU, hstrict⟩
  have hco := E.ox_feasible_old hl hF'
  set ε := fun n : ℕ => c1 - cy' (n + 1)
  have hε := E.eq_16_10 hs h1 h2 h0 hl hR hF' h0' hU
  have hεlt : ∀ n, ε n < c1 := fun n => by
    simp only [ε]; linarith [hF'.1 (n + 1) (by omega)]
  -- all perturbations vanish
  have hzero : ∀ n, ε n = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs0⟩ := hcon
    have hpos : 0 < ε s := lt_of_le_of_ne (hε s).1 (Ne.symm hs0)
    have hmono : ∀ j, ε s ≤ ε (s + j) := fun j => by
      induction j with
      | zero => exact le_rfl
      | succ j ih => exact ih.trans (by simpa [ε, add_assoc] using (hε (s + j)).2)
    obtain ⟨ρ, hρ, hgeo⟩ := E.ox_eps_geometric h2 hpos (hεlt s)
    set k := ρ / E.ox_gn
    have hk : 1 < k := (lt_div_iff₀ hgn).2 (by linarith)
    have hgrow : ∀ j, k ^ j * ε s ≤ ε (s + j) := fun j => by
      induction j with
      | zero => simp
      | succ j ih =>
        have hUj := hU (s + j + 1) (by omega)
        rw [(hs (s + j + 1) (by omega)).1, (hs (s + j + 1) (by omega)).2] at hUj
        have := hgeo _ _ (hF'.1 (s + j + 1) (by omega)) (hF'.2.1 (s + j + 1)) (hmono j) hUj
        rw [hco (s + j + 1)] at this
        have h3 : k * ε (s + j) ≤ ε (s + (j + 1)) := by
          simp only [k, ε, ← add_assoc]
          rw [div_mul_eq_mul_div, div_le_iff₀ hgn]
          linarith
        calc k ^ (j + 1) * ε s = k * (k ^ j * ε s) := by ring
          _ ≤ k * ε (s + j) := mul_le_mul_of_nonneg_left ih (by linarith)
          _ ≤ ε (s + (j + 1)) := h3
    have htend : Tendsto (fun j => k ^ j * ε s) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hk).atTop_mul_const hpos
    obtain ⟨j, hj⟩ := (htend.eventually_gt_atTop c1).exists
    linarith [hgrow j, hεlt (s + j)]
  have hcy : ∀ t, 1 ≤ t → cy' t = c1 := fun t ht => by
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    have := hzero n; simp only [ε] at this; linarith
  have hco' : ∀ t, co' t = c2 := fun t => by
    rw [hco t, hcy (t + 1) (by omega), sub_self, mul_zero, add_zero]
  rcases hstrict with h | ⟨t, ht, h⟩
  · rw [hco' 0, h0] at h; exact lt_irrefl _ h
  · rw [hcy t ht, hco' t, (hs t ht).1, (hs t ht).2] at h; exact lt_irrefl _ h

/-- Miao, p. 541 (the transfer scheme): `f(ε) = u(c₁ − ε) + βu(c₂ + g_nε)` has
`f'(0) = −u'(c₁) + βg_nu'(c₂)`, positive when `g_n > u'(c₁)/(βu'(c₂))`; hence some small `ε > 0`
makes every generation better off. -/
theorem proposition_16_1_2_transfer {c1 c2 : ℝ} (h1 : 0 < c1) (h2 : 0 < c2)
    (hR : E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) < E.ox_gn) :
    HasDerivAt (fun ε => E.ox_EU (c1 - ε) (c2 + E.ox_gn * ε))
        (-E.ox_P.ox_du c1 + E.ox_P.ox_β * E.ox_gn * E.ox_P.ox_du c2) 0 ∧
      0 < -E.ox_P.ox_du c1 + E.ox_P.ox_β * E.ox_gn * E.ox_P.ox_du c2 ∧
      ∃ ε, 0 < ε ∧ ε < c1 ∧ E.ox_EU c1 c2 < E.ox_EU (c1 - ε) (c2 + E.ox_gn * ε) := by
  have hβ := E.ox_P.ox_β_pos
  have hd2 := E.ox_P.ox_du_pos _ h2
  have hl1 : HasDerivAt (fun s : ℝ => c1 - s) (-1) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_sub c1
  have hl2 : HasDerivAt (fun s : ℝ => c2 + E.ox_gn * s) E.ox_gn 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul E.ox_gn).const_add c2
  have hu1 : HasDerivAt E.ox_P.ox_u (E.ox_P.ox_du c1) ((fun s : ℝ => c1 - s) 0) := by
    simpa using E.ox_P.ox_hasDeriv c1 h1
  have hu2 : HasDerivAt E.ox_P.ox_u (E.ox_P.ox_du c2) ((fun s : ℝ => c2 + E.ox_gn * s) 0) := by
    simpa using E.ox_P.ox_hasDeriv c2 h2
  have hd : HasDerivAt (fun ε => E.ox_EU (c1 - ε) (c2 + E.ox_gn * ε))
      (-E.ox_P.ox_du c1 + E.ox_P.ox_β * E.ox_gn * E.ox_P.ox_du c2) 0 := by
    have h0 : HasDerivAt (fun ε => E.ox_EU (c1 - ε) (c2 + E.ox_gn * ε))
        (E.ox_P.ox_du c1 * -1 + E.ox_P.ox_β * (E.ox_P.ox_du c2 * E.ox_gn)) 0 :=
      (hu1.comp 0 hl1).add ((hu2.comp 0 hl2).const_mul E.ox_P.ox_β)
    exact h0.congr_deriv (by ring)
  have hpos : 0 < -E.ox_P.ox_du c1 + E.ox_P.ox_β * E.ox_gn * E.ox_P.ox_du c2 := by
    rw [div_lt_iff₀ (mul_pos hβ hd2)] at hR; linarith
  refine ⟨hd, hpos, ?_⟩
  have hev := (hd.tendsto_slope_zero_right.eventually (lt_mem_nhds hpos)).and
    ((show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < c1 from mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h1)).and
      self_mem_nhdsWithin)
  obtain ⟨ε, hsl, hεc, hε0⟩ := hev.exists
  refine ⟨ε, hε0, hεc, ?_⟩
  simp only [zero_add, smul_eq_mul, sub_zero, mul_zero, add_zero] at hsl
  have := (mul_pos_iff_of_pos_left (inv_pos.2 (Set.mem_Ioi.1 hε0))).1 hsl
  linarith

/-- Miao, pp. 540–541 (necessity in Proposition 16.1.2, for any feasible stationary allocation):
if `R = u'(c₁)/(βu'(c₂)) < g_n` the transfer of `ε` from each young to the old is a Pareto
improvement. -/
theorem ox_stationary_not_optimal {cy co : ℕ → ℝ} {c1 c2 : ℝ}
    (hs : ox_IsStationary cy co c1 c2) (h1 : 0 < c1) (h2 : 0 < c2) (hF : E.ox_Feasible cy co)
    (hR : E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) < E.ox_gn) :
    ¬ E.ox_ParetoOptimal cy co := by
  obtain ⟨-, h0⟩ := (E.eq_16_12 hs h1 h2).1 hF
  obtain ⟨-, -, ε, hε0, hεc, hU⟩ := E.proposition_16_1_2_transfer h1 h2 hR
  have hgn := E.ox_gn_pos
  rintro ⟨-, hno⟩
  refine hno ⟨fun _ => c1 - ε, fun _ => c2 + E.ox_gn * ε, ⟨fun _ _ => by linarith,
    fun _ => by nlinarith, fun t _ => ?_⟩, ?_, fun t ht => ?_, Or.inl ?_⟩
  · have := (E.eq_16_12 hs h1 h2).1 hF
    field_simp at this; linarith [this.1]
  · rw [h0]; nlinarith
  · rw [(hs t ht).1, (hs t ht).2]; exact hU.le
  · rw [h0]; nlinarith

/-- Miao, pp. 539–541: a feasible stationary allocation is Pareto optimal iff
`u'(c₁)/(βu'(c₂)) ≥ g_n`. -/
theorem ox_stationary_optimal_iff {cy co : ℕ → ℝ} {c1 c2 : ℝ}
    (hs : ox_IsStationary cy co c1 c2) (h1 : 0 < c1) (h2 : 0 < c2) (hF : E.ox_Feasible cy co) :
    E.ox_ParetoOptimal cy co ↔ E.ox_gn ≤ E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) :=
  ⟨fun h => not_lt.1 fun hlt => E.ox_stationary_not_optimal hs h1 h2 hF hlt h,
    E.ox_stationary_optimal hs h1 h2 hF⟩

/-- **Proposition 16.1.2** (Miao, p. 539): the nonmonetary equilibrium (autarky) is Pareto optimal
iff `R_aut ≥ g_n`. -/
theorem proposition_16_1_2 {q cy co m : ℕ → ℝ} (h : E.ox_IsNonmonetary q cy co m) :
    E.ox_ParetoOptimal cy co ↔ E.ox_gn ≤ E.ox_Raut := by
  obtain ⟨hy, h0⟩ := E.ox_nonmonetary_autarky h
  have hs : ox_IsStationary cy co E.ox_e1 E.ox_e2 := hy
  have hF : E.ox_Feasible cy co := by
    refine (E.eq_16_12 hs E.ox_e1_pos E.ox_e2_pos).2 ⟨rfl, h0⟩
  exact E.ox_stationary_optimal_iff hs E.ox_e1_pos E.ox_e2_pos hF

/-- Miao, (16.13), p. 542: in a stationary monetary equilibrium with real balances `m̂`
(`R = g_n/g_m`), every choice in a young agent's budget set satisfies
`c₁ + (g_m/g_n)c₂ ≤ e₁ + (g_m/g_n)e₂ + (g_m − 1)m̂`, with equality at the equilibrium allocation. -/
theorem eq_16_13 {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {mh : ℝ}
    (hc : ∀ t, 1 ≤ t → E.ox_mhat q t = mh) {t : ℕ} (ht : 1 ≤ t) :
    (∀ c1 c2 m', E.ox_Budget q t c1 c2 m' → c1 + E.ox_gm / E.ox_gn * c2 ≤
      E.ox_e1 + E.ox_gm / E.ox_gn * E.ox_e2 + (E.ox_gm - 1) * mh) ∧
      cy t + E.ox_gm / E.ox_gn * co t =
        E.ox_e1 + E.ox_gm / E.ox_gn * E.ox_e2 + (E.ox_gm - 1) * mh := by
  have hR := E.ox_stationary_R h hc ht
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  have hqt := h.2 t ht
  have hqt1 := h.2 (t + 1) (by omega)
  have hinv : 1 / (q (t + 1) / q t) = E.ox_gm / E.ox_gn := by rw [hR]; field_simp
  have hτ : q (t + 1) * E.ox_τ t / (q (t + 1) / q t) = (E.ox_gm - 1) * mh := by
    have hm1 := hc (t + 1) (by omega)
    unfold ox_mhat at hm1
    rw [E.ox_M_succ, E.ox_N_succ] at hm1
    rw [div_eq_mul_one_div, hinv]
    unfold ox_τ
    rw [← hm1]
    have := (E.ox_N_pos t).ne'
    field_simp
  obtain ⟨-, -, -, hcy, hco⟩ := (E.ox_monetary_alloc h).1 t ht
  refine ⟨fun c1 c2 m' hb => ?_, ?_⟩
  · have hl := E.ox_budget_line hqt hqt1 hb
    rw [div_eq_mul_one_div c2, hinv, add_div, hτ, div_eq_mul_one_div E.ox_e2, hinv] at hl
    linarith
  · rw [hcy, hco, hc t ht, hc (t + 1) (by omega)]
    field_simp
    ring

/-- Miao, p. 542 (the steps of the necessity proof of Proposition 16.1.3): with `g_m > 1` the
budget line (16.13), slope `−g_n/g_m`, is flatter than the feasibility line (16.12), slope `−g_n`;
and if `c̄₁ < ĉ₁` the initial old can be given strictly more, `e₂ + g_n(e₁ − c̄₁) > e₂ +
g_n(e₁ − ĉ₁)`. -/
theorem proposition_16_1_3_steps (hgm : 1 < E.ox_gm) {cb ch : ℝ} (hlt : cb < ch) :
    E.ox_gn / E.ox_gm < E.ox_gn ∧
      E.ox_e2 + E.ox_gn * (E.ox_e1 - ch) < E.ox_e2 + E.ox_gn * (E.ox_e1 - cb) := by
  have hgn := E.ox_gn_pos
  exact ⟨(div_lt_iff₀ (by linarith)).2 (by nlinarith), by nlinarith⟩

/-- **Proposition 16.1.3** (Miao, p. 541): given `R_aut g_m < g_n`, the stationary monetary
equilibrium is Pareto optimal iff `g_m ≤ 1`. Stated for every monetary equilibrium with a
stationary allocation (by `proposition_16_1_1` one exists exactly when `R_aut g_m < g_n`). -/
theorem proposition_16_1_3 (_hR : E.ox_Raut * E.ox_gm < E.ox_gn) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) {c1 c2 : ℝ} (hs : ox_IsStationary cy co c1 c2) :
    E.ox_ParetoOptimal cy co ↔ E.ox_gm ≤ 1 := by
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  obtain ⟨halloc, h0⟩ := E.ox_monetary_alloc h
  have hc : ∀ t, 1 ≤ t → E.ox_mhat q t = E.ox_e1 - c1 := fun t ht => by
    have := (halloc t ht).2.2.2.1; rw [(hs t ht).1] at this; linarith
  have h1 : 0 < c1 := (hs 1 le_rfl).1 ▸ h.1.2.1 1 le_rfl |>.1.2.1
  have h2 : 0 < c2 := (hs 1 le_rfl).2 ▸ h.1.2.1 1 le_rfl |>.1.2.2.1
  have hF : E.ox_Feasible cy co := by
    refine ⟨fun t ht => (h.1.2.1 t ht).1.2.1, fun t => ?_,
      (E.definition_16_1_1 cy co).1 h.1.2.2.2.2⟩
    rcases Nat.eq_zero_or_pos t with ht | ht
    · rw [ht, h0]
      have := (halloc 1 le_rfl).2.1
      nlinarith [E.ox_e2_pos]
    · exact (h.1.2.1 t ht).1.2.2.1
  have hRe : E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) = E.ox_gn / E.ox_gm := by
    have := E.eq_16_4 h (t := 1) le_rfl
    rw [(hs 1 le_rfl).1, (hs 1 le_rfl).2] at this
    rw [this, E.ox_stationary_R h hc le_rfl]
  rw [E.ox_stationary_optimal_iff hs h1 h2 hF, hRe, le_div_iff₀ hgm]
  constructor
  · intro hle; nlinarith
  · intro hle; nlinarith

/-- Miao, p. 543 (Balasko–Shell): with `p₁ = 1` and `R_{s+1} = p_s/p_{s+1}`,
`∏_{s=1}^t R_{s+1} = 1/p_{t+1}`. -/
theorem ox_balasko_shell_prod {p : ℕ → ℝ} (hp : ∀ t, 0 < p t) (h1 : p 1 = 1) (t : ℕ) :
    ∏ s ∈ Finset.Icc 1 t, p s / p (s + 1) = 1 / p (t + 1) := by
  induction t with
  | zero => simp [h1]
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    have := (hp (n + 1)).ne'
    have := (hp (n + 1 + 1)).ne'
    field_simp

/-- Miao, p. 543 (Balasko–Shell): with `p₁ = 1`, `∑_t ∏_{s=1}^t R_{s+1} = ∞` iff
`∑_t 1/p_t = ∞` (for positive terms, divergence is failure of summability). -/
theorem ox_balasko_shell_equiv {p : ℕ → ℝ} (hp : ∀ t, 0 < p t) (h1 : p 1 = 1) :
    (¬ Summable fun t : ℕ => ∏ s ∈ Finset.Icc 1 (t + 1), p s / p (s + 1)) ↔
      ¬ Summable fun t : ℕ => 1 / p (t + 1) := by
  simp only [ox_balasko_shell_prod hp h1]
  rw [summable_nat_add_iff (f := fun t : ℕ => 1 / p (t + 1)) 1]

/-- Miao, pp. 543–544 (Balasko–Shell intuition): the transfer `δ_t` to generation `t` when old that
compensates for giving up `δ_{t−1}` when young, `δ_{t−1}u'(c_t^t) = δ_tβu'(c_{t+1}^t)`, is
`δ_t = δ₀∏_{s=1}^t R_{s+1}` with `R_{s+1} = u'(c_s^s)/(βu'(c_{s+1}^s))`. -/
theorem ox_balasko_shell_transfers {cy co δ : ℕ → ℝ} (hco : ∀ t, 0 < co t)
    (hδ : ∀ t, 1 ≤ t → δ (t - 1) * E.ox_P.ox_du (cy t) = δ t * E.ox_P.ox_β * E.ox_P.ox_du (co t))
    (t : ℕ) : δ t = δ 0 * ∏ s ∈ Finset.Icc 1 t,
      E.ox_P.ox_du (cy s) / (E.ox_P.ox_β * E.ox_P.ox_du (co s)) := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ← mul_assoc, ← ih]
    have h := hδ (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    have := (mul_pos E.ox_P.ox_β_pos (E.ox_P.ox_du_pos _ (hco (n + 1)))).ne'
    rw [mul_div_assoc', eq_div_iff this, h]
    ring

/-- Miao, p. 543 (Balasko–Shell for stationary allocations, `g_n = 1`): a feasible stationary
allocation is Pareto optimal iff `∑_t ∏_{s=1}^t R_{s+1} = ∑_t Rᵗ = ∞`. -/
theorem ox_balasko_shell_stationary (hgn : E.ox_gn = 1) {cy co : ℕ → ℝ} {c1 c2 : ℝ}
    (hs : ox_IsStationary cy co c1 c2) (h1 : 0 < c1) (h2 : 0 < c2) (hF : E.ox_Feasible cy co) :
    E.ox_ParetoOptimal cy co ↔
      ¬ Summable fun t : ℕ => (E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2)) ^ (t + 1) := by
  rw [E.ox_stationary_optimal_iff hs h1 h2 hF, hgn]
  have hR : 0 < E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) :=
    div_pos (E.ox_P.ox_du_pos _ h1) (mul_pos E.ox_P.ox_β_pos (E.ox_P.ox_du_pos _ h2))
  rw [summable_nat_add_iff (f := fun t : ℕ =>
    (E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2)) ^ t) 1, summable_geometric_iff_norm_lt_one,
    Real.norm_eq_abs, abs_of_pos hR, not_lt]

end OXEconomy

end Miao.OverlappingGenerations
