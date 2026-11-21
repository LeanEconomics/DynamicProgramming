/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.PlannerTree
import InternationalFinancialMarkets.Spanning

/-!
# Competitive market trade under uncertainty

AKMM, §7.4, Definitions 13–14, (7.20)–(7.25), pp. 204–210 (with fn. 14). The event tree is
Miao's `BPTree`; a finite set `ι` of households with consumption `c i h` and endowment `y i h`
at the history `h = ωᵗ`; Arrow–Debreu prices `p h = pₜ(ωᵗ)` (in date-0 goods).

* The date-0 budget `Σₜ Σ_{ωᵗ} pₜcᵢ,ₜ = Σₜ Σ_{ωᵗ} pₜyᵢ,ₜ` (`cm_Budget`), the household's problem
  (`cm_Optimal`) and **Definition 13** (`definition_13`).
* **(7.20)** `βᵗπₜ(ωᵗ)u′(cᵢ,ₜ(ωᵗ)) = λᵢpₜ(ωᵗ)` at every optimum, proved from optimality by moving
  value between two histories (`eq_7_20_pair`, `eq_7_20`).
* Insurance: with actuarially fair prices `pₜ = p̄ₜπₜ` consumption does not depend on `ωᵗ`
  (`cm_insurance`), which in equilibrium forces the aggregate endowment to be constant across the
  date-`t` histories (`cm_insurance_no_aggregate_risk`); fn. 14, fair prices value a payoff by its
  expectation (`cm_fair_value`).
* Risk sharing: `u′(cᵢ)/u′(cⱼ) = λᵢ/λⱼ` (`cm_risk_sharing`), **(7.21)** (`eq_7_21`), and
  consumption depends only on the aggregate endowment (`cm_aggregate_risk_only`).
* Sequential trading: the recursive discounts `q̃` (`seq_disc`), the budget (7.22)/(7.24)
  (`seq_Budget`), the consolidated budget (`seq_consolidated`), and with the no-Ponzi condition the
  date-0 budget at the prices `p = q̃` (`seq_ad_budget_le`, `seq_ad_budget_eq`); the price maps
  between the two arrangements (`seq_price_map`, `seq_price_of_ad`); **Definition 14**
  (`definition_14`), in which asset-market clearing implies goods-market clearing
  (`definition_14_goods_of_assets`).
* Spanning (p. 210): markets are complete iff `rank D = S` (`spanning_iff_rank`, from Obstfeld and
  Rogoff's `spans_iff_rank`), and then the Arrow securities are portfolios (`spanning_arrow`).

Departures: consumption is positive and the series converge; the no-Ponzi condition (7.25) is used
in its date-0 aggregated form (`nodeSum_T(q̃a) ≥ −Σ_{τ≥T} nodeSum_τ(q̃y)`); the book's "one of
these implies the other" in Definition 14 is proved in the direction asset clearing ⇒ goods
clearing; the full equivalence of the sequential and Arrow–Debreu equilibria (asserted, with the
proof sketched) is formalised through its key step, the consolidated budget.
-/

namespace AKMM.Uncertainty

open Miao.CompleteMarkets Filter Topology AKMM.CompetitiveEquilibrium

variable {S : Type*} [Fintype S]

/-! ### The date-0 problem and Definition 13 -/

/-- The date-`t` value `Σ_{ωᵗ} pₜ(ωᵗ)xₜ(ωᵗ)` of a payoff. -/
def cm_value (p x : List S → ℝ) (t : ℕ) : ℝ := bp_nodeSum t (fun h => p h * x h)

/-- AKMM, p. 206: the date-0 budget `Σₜ Σ_{ωᵗ} pₜcₜ = Σₜ Σ_{ωᵗ} pₜyₜ` (both series converge). -/
def cm_Budget (p y c : List S → ℝ) : Prop :=
  Summable (cm_value p c) ∧ Summable (cm_value p y) ∧ ∑' t, cm_value p c t = ∑' t, cm_value p y t

/-- AKMM, p. 206: `c` solves the household's problem at the prices `p` (among positive plans with
convergent utility). -/
def cm_Optimal (T : BPTree S) (β : ℝ) (u : ℝ → ℝ) (p y c : List S → ℝ) : Prop :=
  (∀ h, 0 < c h) ∧ cm_Budget p y c ∧ Summable (pt_util T β u c) ∧
    ∀ c', (∀ h, 0 < c' h) → cm_Budget p y c' → Summable (pt_util T β u c') →
      ∑' t, pt_util T β u c' t ≤ ∑' t, pt_util T β u c t

/-- **AKMM, Definition 13, p. 206: an Arrow–Debreu competitive equilibrium.** Each household's
plan solves its problem, and goods markets clear at every `(t, ωᵗ)`. -/
def definition_13 {ι : Type*} [Fintype ι] (T : BPTree S) (β : ℝ) (u : ℝ → ℝ)
    (p : List S → ℝ) (y c : ι → List S → ℝ) : Prop :=
  (∀ i, cm_Optimal T β u p (y i) (c i)) ∧ ∀ h, ∑ i, c i h = ∑ i, y i h

theorem cm_nodeSum_update [DecidableEq S] (t : ℕ) (g : List S → ℝ) (h₀ : List S) (v : ℝ) :
    bp_nodeSum t (fun h => g h + if h = h₀ then v else 0) =
      bp_nodeSum t g + if h₀.length = t then v else 0 := by
  rw [bp_nodeSum_add]
  congr 1
  split_ifs with hl
  · exact bp_nodeSum_single t h₀ hl v
  · have h0 : bp_nodeSum t (fun h => if h = h₀ then v else 0) =
        bp_nodeSum t (fun h => 0 * h.length) := bp_nodeSum_congr t _ _ fun h hh => by
      have : h ≠ h₀ := fun e => hl (by rw [← e, hh])
      simp [this]
    rw [h0, bp_nodeSum_smul]
    ring

/-- **AKMM, (7.20), p. 206, between two histories.** At an optimum with positive prices, if `u`
has derivative `u′(c)` at each `c > 0`, then for any histories `h₁ = ωᵗ`, `h₂ = (ω^s)′`:
`βᵗπ(h₁)u′(c(h₁))p(h₂) = βˢπ(h₂)u′(c(h₂))p(h₁)`. Proved by buying `ε` more at `h₁` and selling
`ε p(h₁)/p(h₂)` at `h₂`. -/
theorem eq_7_20_pair (T : BPTree S) {β : ℝ} {u du : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt u (du c) c) {p y c : List S → ℝ}
    (hopt : cm_Optimal T β u p y c) (hp : ∀ h, 0 < p h) (h₁ h₂ : List S) :
    β ^ h₁.length * T.pr h₁ * du (c h₁) * p h₂ = β ^ h₂.length * T.pr h₂ * du (c h₂) * p h₁ := by
  classical
  rcases eq_or_ne h₁ h₂ with rfl | hne
  · ring
  obtain ⟨hcpos, ⟨hsc, hsy, hbud⟩, husum, hmax⟩ := hopt
  set r := p h₁ / p h₂ with hr
  set t₁ := h₁.length
  set t₂ := h₂.length
  set cε : ℝ → List S → ℝ := fun ε h =>
    c h + (if h = h₁ then ε else 0) + (if h = h₂ then -(r * ε) else 0) with hcε
  have hne' : h₂ ≠ h₁ := hne.symm
  -- pointwise forms
  have hpc : ∀ ε h, p h * cε ε h = (p h * c h + if h = h₁ then p h₁ * ε else 0) +
      if h = h₂ then -(p h₂ * (r * ε)) else 0 := fun ε h => by
    simp only [hcε]
    by_cases e1 : h = h₁
    · subst e1; simp [hne]; ring
    · by_cases e2 : h = h₂
      · subst e2; simp [hne']; ring
      · simp [e1, e2]
  have huc : ∀ ε h, T.pr h * u (cε ε h) = (T.pr h * u (c h) +
      if h = h₁ then T.pr h₁ * (u (c h₁ + ε) - u (c h₁)) else 0) +
      if h = h₂ then T.pr h₂ * (u (c h₂ - r * ε) - u (c h₂)) else 0 := fun ε h => by
    simp only [hcε]
    by_cases e1 : h = h₁
    · subst e1; simp [hne]; ring
    · by_cases e2 : h = h₂
      · subst e2; simp [hne', sub_eq_add_neg]; ring
      · simp [e1, e2]
  have hval : ∀ ε t, cm_value p (cε ε) t = (cm_value p c t +
      if t₁ = t then p h₁ * ε else 0) + if t₂ = t then -(p h₂ * (r * ε)) else 0 := fun ε t => by
    simp only [cm_value, hpc, cm_nodeSum_update]
    rfl
  have hutil : ∀ ε t, pt_util T β u (cε ε) t = pt_util T β u c t +
      β ^ t * ((if t₁ = t then T.pr h₁ * (u (c h₁ + ε) - u (c h₁)) else 0) +
        if t₂ = t then T.pr h₂ * (u (c h₂ - r * ε) - u (c h₂)) else 0) := fun ε t => by
    simp only [pt_util, huc, cm_nodeSum_update]
    ring
  set s : Finset ℕ := {t₁, t₂}
  have hs1 : t₁ ∈ s := by simp [s]
  have hs2 : t₂ ∈ s := by simp [s]
  have hsum_ite : ∀ (A : ℕ → ℝ) (a b : ℝ), ∑ t ∈ s, A t * ((if t₁ = t then a else 0) +
      if t₂ = t then b else 0) = A t₁ * a + A t₂ * b := fun A a b => by
    simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, hs1, hs2,
      ↓reduceIte]
  -- the budget is unchanged
  have hbudε : ∀ ε, cm_Budget p y (cε ε) := fun ε => by
    obtain ⟨hS, hE⟩ := ce_tsum_perturb s (f := cm_value p c) (g := cm_value p (cε ε))
      (fun t ht => by
        have h1 : t₁ ≠ t := fun e => ht (e ▸ hs1)
        have h2 : t₂ ≠ t := fun e => ht (e ▸ hs2)
        simp [hval, h1, h2]) hsc
    refine ⟨hS, hsy, ?_⟩
    rw [hE, ← hbud]
    have : ∑ t ∈ s, (cm_value p (cε ε) t - cm_value p c t) = 0 := by
      have e : ∀ t, cm_value p (cε ε) t - cm_value p c t =
          1 * ((if t₁ = t then p h₁ * ε else 0) + if t₂ = t then -(p h₂ * (r * ε)) else 0) :=
        fun t => by rw [hval]; ring
      simp only [e]
      rw [hsum_ite (fun _ => 1)]
      simp only [hr]
      field_simp [(hp h₂).ne']
      ring
    rw [this, add_zero]
  -- positivity for small `ε`
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ h, 0 < cε ε h := by
    have c1 : ContinuousAt (fun ε : ℝ => c h₁ + ε) 0 := by fun_prop
    have c2 : ContinuousAt (fun ε : ℝ => c h₂ - r * ε) 0 := by fun_prop
    have e1 := continuousAt_const.eventually_lt c1 (show (0 : ℝ) < c h₁ + 0 by simpa using hcpos h₁)
    have e2 := continuousAt_const.eventually_lt c2
      (show (0 : ℝ) < c h₂ - r * 0 by simpa using hcpos h₂)
    filter_upwards [e1, e2] with ε hε1 hε2 h
    simp only [hcε]
    by_cases f1 : h = h₁
    · subst f1; simpa [hne] using hε1
    · by_cases f2 : h = h₂
      · subst f2; simpa [hne', sub_eq_add_neg] using hε2
      · simpa [f1, f2] using hcpos h
  have hle : ∀ᶠ ε in 𝓝 (0 : ℝ), Summable (pt_util T β u (cε ε)) →
      ∑' t, pt_util T β u (cε ε) t ≤ ∑' t, pt_util T β u c t := by
    filter_upwards [hev] with ε hε hS
    exact hmax _ hε (hbudε ε) hS
  have hder : HasDerivAt (fun ε => ∑ t ∈ s, pt_util T β u (cε ε) t)
      (β ^ t₁ * (T.pr h₁ * du (c h₁)) + β ^ t₂ * (T.pr h₂ * (du (c h₂) * (-r)))) 0 := by
    have e : (fun ε => ∑ t ∈ s, pt_util T β u (cε ε) t) = fun ε =>
        ∑ t ∈ s, pt_util T β u c t + (β ^ t₁ * (T.pr h₁ * (u (c h₁ + ε) - u (c h₁))) +
          β ^ t₂ * (T.pr h₂ * (u (c h₂ - r * ε) - u (c h₂)))) := by
      funext ε
      simp only [hutil, Finset.sum_add_distrib]
      rw [hsum_ite]
    rw [e]
    have d1 : HasDerivAt (fun ε => u (c h₁ + ε)) (du (c h₁)) 0 := by
      have := hu _ (hcpos h₁)
      simpa using (show HasDerivAt u (du (c h₁)) (c h₁ + 0) by simpa using this).comp_const_add
        (c h₁) 0
    have d2 : HasDerivAt (fun ε => u (c h₂ - r * ε)) (du (c h₂) * (-r)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c h₂ - r * ε) (-r) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul r).const_sub (c h₂)
      have hu2 : HasDerivAt u (du (c h₂)) (c h₂ - r * 0) := by simpa using hu _ (hcpos h₂)
      exact hu2.comp 0 hin
    refine HasDerivAt.const_add _ (HasDerivAt.add ?_ ?_)
    · simpa using ((d1.sub_const (u (c h₁))).const_mul (T.pr h₁)).const_mul (β ^ t₁)
    · simpa using ((d2.sub_const (u (c h₂))).const_mul (T.pr h₂)).const_mul (β ^ t₂)
  have hz := ce_foc_of_perturb s husum (fun ε t ht => by
      have h1 : t₁ ≠ t := fun e => ht (e ▸ hs1)
      have h2 : t₂ ≠ t := fun e => ht (e ▸ hs2)
      rw [hutil]; simp [h1, h2])
    (fun t => by simp [hcε]) hle hder
  rw [hr] at hz
  field_simp [(hp h₂).ne'] at hz
  linarith

/-- **AKMM, (7.20), p. 206.** At an optimum with positive prices there is a multiplier `λ` with
`βᵗπₜ(ωᵗ)u′(cₜ(ωᵗ)) = λpₜ(ωᵗ)` at every history (`λ = u′(c₀)/p₀`). -/
theorem eq_7_20 (T : BPTree S) {β : ℝ} {u du : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt u (du c) c) {p y c : List S → ℝ}
    (hopt : cm_Optimal T β u p y c) (hp : ∀ h, 0 < p h) :
    ∃ lam, ∀ h, β ^ h.length * T.pr h * du (c h) = lam * p h := by
  refine ⟨du (c []) / p [], fun h => ?_⟩
  have e := eq_7_20_pair T hu hopt hp h []
  simp only [List.length_nil, pow_zero, T.pr_nil, one_mul] at e
  field_simp [(hp []).ne']
  linarith

/-- **AKMM, p. 207: insurance.** If (7.20) holds and prices are actuarially fair,
`pₜ(ωᵗ) = p̄ₜπₜ(ωᵗ)`, then at histories of the same date marginal utilities and, with `u′`
strictly decreasing, consumption coincide: full insurance. -/
theorem cm_insurance (T : BPTree S) {β lam : ℝ} (hβ : 0 < β) {du : ℝ → ℝ}
    (hdu : StrictAntiOn du (Set.Ioi 0)) {c p : List S → ℝ} {pbar : ℕ → ℝ}
    (hfoc : ∀ h, β ^ h.length * T.pr h * du (c h) = lam * p h)
    (hfair : ∀ h, p h = pbar h.length * T.pr h) (hc : ∀ h, 0 < c h) {h h' : List S}
    (hl : h.length = h'.length) : du (c h) = du (c h') ∧ c h = c h' := by
  have key : ∀ g, du (c g) = lam * pbar g.length / β ^ g.length := fun g => by
    have := hfoc g
    rw [hfair] at this
    have hb := pow_pos hβ g.length
    have hp := T.pr_pos g
    field_simp
    nlinarith
  have hdu' : du (c h) = du (c h') := by rw [key, key, hl]
  exact ⟨hdu', hdu.injOn (hc h) (hc h') hdu'⟩

omit [Fintype S] in
/-- AKMM, p. 207: "full insurance is only feasible in equilibrium if total resources do not
vary": if every household is fully insured and goods markets clear, the aggregate endowment is
the same at all histories of a date. -/
theorem cm_insurance_no_aggregate_risk {ι : Type*} [Fintype ι] {c y : ι → List S → ℝ}
    (hclear : ∀ h, ∑ i, c i h = ∑ i, y i h) {h h' : List S} (hins : ∀ i, c i h = c i h') :
    ∑ i, y i h = ∑ i, y i h' := by
  rw [← hclear, ← hclear]
  exact Finset.sum_congr rfl fun i _ => hins i

/-- AKMM, fn. 14, p. 207: with fair prices `pₜ = p̄ₜπₜ` the date-0 value of a date-`t` payoff is
`p̄ₜE[xₜ]`, which depends only on the date and the expected payoff. -/
theorem cm_fair_value (T : BPTree S) {p x : List S → ℝ} {pbar : ℕ → ℝ}
    (hfair : ∀ h, p h = pbar h.length * T.pr h) (t : ℕ) :
    cm_value p x t = pbar t * bp_condExp T t x [] := by
  rw [bp_condExp_root, cm_value, ← bp_nodeSum_smul]
  refine bp_nodeSum_congr t _ _ fun h hh => ?_
  rw [hfair, hh]; ring

/-- **AKMM, p. 207: risk sharing.** If (7.20) holds for households `i` and `j` with multipliers
`λᵢ, λⱼ`, then `u′(cᵢ,ₜ(ωᵗ))/u′(cⱼ,ₜ(ωᵗ)) = λᵢ/λⱼ` at every history. -/
theorem cm_risk_sharing (T : BPTree S) {β : ℝ} (hβ : 0 < β) {du : ℝ → ℝ} {ci cj p : List S → ℝ}
    {li lj : ℝ} (hi : ∀ h, β ^ h.length * T.pr h * du (ci h) = li * p h)
    (hj : ∀ h, β ^ h.length * T.pr h * du (cj h) = lj * p h)
    (hduj : ∀ h, du (cj h) ≠ 0) (h : List S) : du (ci h) / du (cj h) = li / lj := by
  have hb := (mul_pos (pow_pos hβ h.length) (T.pr_pos h)).ne'
  have hlj : lj ≠ 0 := by
    intro e; have := hj h; rw [e, zero_mul] at this
    exact hduj h (by simpa [hb] using this)
  rw [div_eq_div_iff (hduj h) hlj]
  have e1 := hi h
  have e2 := hj h
  apply mul_left_cancel₀ hb
  calc β ^ h.length * T.pr h * (du (ci h) * lj) = (β ^ h.length * T.pr h * du (ci h)) * lj := by
        ring
    _ = li * (β ^ h.length * T.pr h * du (cj h)) := by rw [e1, e2]; ring
    _ = _ := by ring

/-- **AKMM, (7.21), p. 207.** With `uinv` a left inverse of `u′` on `(0, ∞)`, risk sharing gives
`cᵢ,ₜ(ωᵗ) = u′⁻¹((λᵢ/λⱼ)u′(cⱼ,ₜ(ωᵗ)))`, and goods-market clearing
`Σᵢ u′⁻¹((λᵢ/λⱼ)u′(cⱼ,ₜ(ωᵗ))) = Σᵢ yᵢ,ₜ(ωᵗ)`. -/
theorem eq_7_21 {ι : Type*} [Fintype ι] (T : BPTree S) {β : ℝ} (hβ : 0 < β) {du uinv : ℝ → ℝ}
    (hinv : ∀ c, 0 < c → uinv (du c) = c) {c y : ι → List S → ℝ} {p : List S → ℝ}
    {lam : ι → ℝ} (hfoc : ∀ i h, β ^ h.length * T.pr h * du (c i h) = lam i * p h)
    (hc : ∀ i h, 0 < c i h) (hdu : ∀ i h, du (c i h) ≠ 0)
    (hclear : ∀ h, ∑ i, c i h = ∑ i, y i h) (j : ι) (h : List S) :
    (∀ i, c i h = uinv (lam i / lam j * du (c j h))) ∧
      ∑ i, uinv (lam i / lam j * du (c j h)) = ∑ i, y i h := by
  have hci : ∀ i, c i h = uinv (lam i / lam j * du (c j h)) := fun i => by
    have := cm_risk_sharing T hβ (hfoc i) (hfoc j) (fun h => hdu j h) h
    rw [← this, div_mul_cancel₀ _ (hdu j h), hinv _ (hc i h)]
  exact ⟨hci, by rw [← hclear]; exact Finset.sum_congr rfl fun i _ => (hci i).symm⟩

/-- **AKMM, p. 207: "consumption fluctuations only reflect aggregate risks".** With positive
multipliers, `u′` strictly decreasing on `(0, ∞)`, (7.20) for every household and goods-market
clearing, two histories (of any dates) with the same aggregate endowment give every household the
same consumption. -/
theorem cm_aggregate_risk_only {ι : Type*} [Fintype ι] (T : BPTree S) {β : ℝ} (hβ : 0 < β)
    {du : ℝ → ℝ} (hdu : StrictAntiOn du (Set.Ioi 0)) {c y : ι → List S → ℝ}
    {p : List S → ℝ} {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i)
    (hfoc : ∀ i h, β ^ h.length * T.pr h * du (c i h) = lam i * p h)
    (hc : ∀ i h, 0 < c i h) (hclear : ∀ h, ∑ i, c i h = ∑ i, y i h) {h h' : List S}
    (hY : ∑ i, y i h = ∑ i, y i h') (j : ι) : c j h = c j h' := by
  -- `u′(cᵢ(h)) = (λᵢ/λⱼ)u′(cⱼ(h))`
  have hratio : ∀ i g, du (c i g) = lam i / lam j * du (c j g) := fun i g => by
    have e1 := hfoc i g
    have e2 := hfoc j g
    have hb := (mul_pos (pow_pos hβ g.length) (T.pr_pos g)).ne'
    have hl := (hlam j).ne'
    field_simp
    have : β ^ g.length * T.pr g * (du (c i g) * lam j) =
        β ^ g.length * T.pr g * (lam i * du (c j g)) := by
      calc β ^ g.length * T.pr g * (du (c i g) * lam j) =
          (β ^ g.length * T.pr g * du (c i g)) * lam j := by ring
        _ = lam i * (β ^ g.length * T.pr g * du (c j g)) := by rw [e1, e2]; ring
        _ = _ := by ring
    exact mul_left_cancel₀ hb this
  -- if `cⱼ(h) < cⱼ(h′)` then every `cᵢ(h) < cᵢ(h′)`, contradicting equal totals
  have hmono : ∀ g g', c j g < c j g' → ∀ i, c i g < c i g' := fun g g' hlt i => by
    have h1 := hdu (hc j g) (hc j g') hlt
    have h2 : du (c i g') < du (c i g) := by
      rw [hratio i g, hratio i g']
      exact mul_lt_mul_of_pos_left h1 (div_pos (hlam i) (hlam j))
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt' | heq
    · exact absurd (hdu (hc i g') (hc i g) hlt') (not_lt.2 h2.le)
    · rw [heq] at h2; exact lt_irrefl _ h2
  rcases lt_trichotomy (c j h) (c j h') with hlt | heq | hgt
  · have := Finset.sum_lt_sum_of_nonempty ⟨j, Finset.mem_univ j⟩
      fun i _ => hmono h h' hlt i
    rw [hclear, hclear, hY] at this
    exact absurd this (lt_irrefl _)
  · exact heq
  · have := Finset.sum_lt_sum_of_nonempty ⟨j, Finset.mem_univ j⟩
      fun i _ => hmono h' h hgt i
    rw [hclear, hclear, hY] at this
    exact absurd this (lt_irrefl _)

/-! ### Sequential trading -/

/-- AKMM, p. 209: the discounts `q̃₀^{τ+1}(ω^{τ+1}) = q_τ(ω_{τ+1}|ω^τ)q̃₀^τ(ω^τ)`, `q̃₀⁰ = 1`;
`q h s` is the price at `h` of one unit at `s :: h`. -/
def seq_disc (q : List S → S → ℝ) : List S → ℝ
  | [] => 1
  | s :: h => q h s * seq_disc q h

/-- AKMM, (7.22)/(7.24), pp. 208–209: `cₜ(ωᵗ) + Σ_{ωₜ₊₁} qₜ(ωₜ₊₁|ωᵗ)aₜ₊₁(ωᵗ⁺¹) = yₜ(ωᵗ) + aₜ(ωᵗ)`
at every history. -/
def seq_Budget (q : List S → S → ℝ) (y c a : List S → ℝ) : Prop :=
  ∀ h, c h + ∑ s, q h s * a (s :: h) = y h + a h

/-- **AKMM, p. 210: the consolidated budget.** Multiplying the budgets by `q̃` and summing over
histories, with `a₀ = 0`:
`Σ_{t ≤ T} Σ_{ωᵗ} q̃(ωᵗ)(cₜ − yₜ) = −Σ_{ω^{T+1}} q̃(ω^{T+1})a_{T+1}(ω^{T+1})`. -/
theorem seq_consolidated {q : List S → S → ℝ} {y c a : List S → ℝ}
    (hb : seq_Budget q y c a) (ha0 : a [] = 0) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), (cm_value (seq_disc q) c t - cm_value (seq_disc q) y t) =
      -cm_value (seq_disc q) a (T + 1) := by
  -- one date: `value(c − y)_t = value(a)_t − value(a)_{t+1}`
  have hstep : ∀ t, cm_value (seq_disc q) c t - cm_value (seq_disc q) y t =
      cm_value (seq_disc q) a t - cm_value (seq_disc q) a (t + 1) := fun t => by
    simp only [cm_value, bp_nodeSum_succ, ← bp_nodeSum_sub]
    refine bp_nodeSum_congr t _ _ fun h _ => ?_
    have := hb h
    have e : ∑ s, seq_disc q (s :: h) * a (s :: h) = seq_disc q h * ∑ s, q h s * a (s :: h) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by simp only [seq_disc]; ring
    rw [e]
    have : ∑ s, q h s * a (s :: h) = y h + a h - c h := by linarith
    rw [this]; ring
  induction T with
  | zero =>
    rw [Finset.sum_range_one, hstep]
    simp [cm_value, bp_nodeSum_zero, ha0]
  | succ T ih => rw [Finset.sum_range_succ, ih, hstep]; ring

/-- AKMM, p. 210: with the no-Ponzi condition in its date-0 form,
`Σ_{ωᵀ} q̃aₜ ≥ −Σ_{τ ≥ T} Σ_{ω^τ} q̃yτ`, the sequential budgets imply the date-0 budget
inequality at the prices `p = q̃`: `Σₜ Σ q̃cₜ ≤ Σₜ Σ q̃yₜ`. -/
theorem seq_ad_budget_le {q : List S → S → ℝ} {y c a : List S → ℝ}
    (hb : seq_Budget q y c a) (ha0 : a [] = 0) (hsc : Summable (cm_value (seq_disc q) c))
    (hsy : Summable (cm_value (seq_disc q) y))
    (hnpg : ∀ T, -∑' τ, cm_value (seq_disc q) y (τ + T) ≤ cm_value (seq_disc q) a T) :
    ∑' t, cm_value (seq_disc q) c t ≤ ∑' t, cm_value (seq_disc q) y t := by
  have hs := ((hsc.sub hsy).hasSum.tendsto_sum_nat)
  have hs1 := (tendsto_add_atTop_iff_nat 1).2 hs
  have htail : Tendsto (fun T => ∑' τ, cm_value (seq_disc q) y (τ + (T + 1))) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_sum_nat_add (cm_value (seq_disc q) y))
  have hle := le_of_tendsto_of_tendsto' hs1 htail fun T => by
    rw [seq_consolidated hb ha0 T]
    linarith [hnpg (T + 1)]
  rw [hsc.tsum_sub hsy] at hle
  linarith

/-- AKMM, p. 210: if moreover the value of asset holdings vanishes in the limit, the sequential
budgets give the date-0 budget `Σₜ Σ q̃cₜ = Σₜ Σ q̃yₜ`. -/
theorem seq_ad_budget_eq {q : List S → S → ℝ} {y c a : List S → ℝ}
    (hb : seq_Budget q y c a) (ha0 : a [] = 0) (hsc : Summable (cm_value (seq_disc q) c))
    (hsy : Summable (cm_value (seq_disc q) y))
    (hlim : Tendsto (fun T => cm_value (seq_disc q) a T) atTop (𝓝 0)) :
    cm_Budget (seq_disc q) y c := by
  refine ⟨hsc, hsy, ?_⟩
  have hs := ((hsc.sub hsy).hasSum.tendsto_sum_nat)
  have hs1 := (tendsto_add_atTop_iff_nat 1).2 hs
  have hlim1 : Tendsto (fun T => -cm_value (seq_disc q) a (T + 1)) atTop (𝓝 0) := by
    simpa using ((tendsto_add_atTop_iff_nat 1).2 hlim).neg
  have heq : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1),
      (cm_value (seq_disc q) c t - cm_value (seq_disc q) y t)) atTop (𝓝 0) :=
    hlim1.congr fun T => (seq_consolidated hb ha0 T).symm
  have := tendsto_nhds_unique hs1 heq
  rw [hsc.tsum_sub hsy] at this
  linarith

omit [Fintype S] in
/-- AKMM, p. 209: positive one-period prices give positive discounts, and
`qₜ(ωₜ₊₁|ωᵗ) = q̃(ωᵗ⁺¹)/q̃(ωᵗ)`. -/
theorem seq_price_map {q : List S → S → ℝ} (hq : ∀ h s, 0 < q h s) :
    (∀ h, 0 < seq_disc q h) ∧ ∀ h s, q h s = seq_disc q (s :: h) / seq_disc q h := by
  have hpos : ∀ h, 0 < seq_disc q h := fun h => by
    induction h with
    | nil => simp [seq_disc]
    | cons s h ih => simp only [seq_disc]; exact mul_pos (hq h s) ih
  refine ⟨hpos, fun h s => ?_⟩
  simp only [seq_disc]
  field_simp [(hpos h).ne']

omit [Fintype S] in
/-- AKMM, p. 210: conversely, Arrow–Debreu prices `p > 0` with `p₀ = 1` are the discounts of the
one-period prices `qₜ(ωₜ₊₁|ωᵗ) = pₜ₊₁(ωᵗ⁺¹)/pₜ(ωᵗ)`. -/
theorem seq_price_of_ad {p : List S → ℝ} (hp : ∀ h, 0 < p h) (hp0 : p [] = 1) :
    seq_disc (fun h s => p (s :: h) / p h) = p := by
  funext h
  induction h with
  | nil => simp [seq_disc, hp0]
  | cons s h ih => simp only [seq_disc, ih]; field_simp [(hp h).ne']

/-- **AKMM, Definition 14, p. 209: a sequential competitive equilibrium.** Each household's
consumption and asset plan satisfies (7.24) with `a₀ = 0` and maximises utility among plans
satisfying (7.24) and the no-Ponzi condition (7.25) (here: `nPg`, a given condition on asset
plans), and goods and asset markets clear at every history. -/
def definition_14 {ι : Type*} [Fintype ι] (T : BPTree S) (β : ℝ) (u : ℝ → ℝ)
    (q : List S → S → ℝ) (nPg : (List S → ℝ) → (List S → ℝ) → Prop) (y c a : ι → List S → ℝ) :
    Prop :=
  (∀ i, (∀ h, 0 < c i h) ∧ a i [] = 0 ∧ seq_Budget q (y i) (c i) (a i) ∧ nPg (y i) (a i) ∧
    Summable (pt_util T β u (c i)) ∧
    ∀ c' a', (∀ h, 0 < c' h) → a' [] = 0 → seq_Budget q (y i) c' a' → nPg (y i) a' →
      Summable (pt_util T β u c') → ∑' t, pt_util T β u c' t ≤ ∑' t, pt_util T β u (c i) t) ∧
  (∀ h, ∑ i, c i h = ∑ i, y i h) ∧ ∀ h, ∑ i, a i h = 0

/-- AKMM, p. 210: "requirement 2 has two conditions; one of these implies the other": summing
the budgets (7.24) over households, asset-market clearing at every history implies
goods-market clearing. -/
theorem definition_14_goods_of_assets {ι : Type*} [Fintype ι] {q : List S → S → ℝ}
    {y c a : ι → List S → ℝ} (hb : ∀ i, seq_Budget q (y i) (c i) (a i))
    (hassets : ∀ h, ∑ i, a i h = 0) (h : List S) : ∑ i, c i h = ∑ i, y i h := by
  have hsum := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hb i h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm, hassets h] at hsum
  simp only [← Finset.mul_sum, hassets, mul_zero, Finset.sum_const_zero, add_zero] at hsum
  exact hsum

/-! ### Spanning -/

/-- **AKMM, p. 210: spanning.** For the `S × N` payoff matrix `D`, every payoff `z ∈ ℝˢ` is the
payoff `Dθ` of some portfolio (markets are complete, `M = ℝˢ`) iff `rank D = S`. -/
theorem spanning_iff_rank {St A : Type} [Fintype St] [Fintype A] (D : Matrix St A ℝ) :
    Function.Surjective D.mulVec ↔ D.rank = Fintype.card St :=
  ObstfeldRogoff.InternationalFinancialMarkets.Spanning.spans_iff_rank D

/-- AKMM, p. 210: if markets are complete there are portfolios `θⱼ` with `Dθⱼ` paying one unit
in state `j` and nothing otherwise: the Arrow securities. -/
theorem spanning_arrow {St A : Type} [Fintype St] [Fintype A] [DecidableEq St]
    {D : Matrix St A ℝ} (hD : D.rank = Fintype.card St) (j : St) :
    ∃ θ : A → ℝ, D.mulVec θ = Pi.single j 1 :=
  (spanning_iff_rank D).2 hD (Pi.single j 1)

end AKMM.Uncertainty
