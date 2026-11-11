/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCompetitiveEquilibrium.EndowmentAD
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Arrow–Debreu equilibrium of the production economy with labour

AKMM, §5.2.2, pp. 135–138. Households `i` with skills `eᵢ` choose consumption and hours to
maximize `Σ βᵗ[u(c_{i,t}) − v(ℓ_{i,t})]` (5.4) subject to `Σ pₜc_{i,t} = Σ pₜwₜeᵢℓ_{i,t}` (5.7);
a representative firm with `Yₜ = AₜLₜ` (5.5) maximizes `Σ pₜ(AₜLₜ − wₜLₜ)` (5.6).

* The firm (fn. 3 and p. 137): the problem (5.6) is a sequence of static problems
  (`eq_5_6_static`); `w = A` makes every scale optimal, `A > w` leaves no optimum, `A < w` makes
  `L = 0` the unique optimum (`labour_firm_fn3`); so positive employment forces `wₜ = Aₜ`
  (`labour_wage_eq_productivity`).
* The household: the first-order conditions (5.8)–(5.10) are necessary (`eq_5_8`, `eq_5_9`,
  `eq_5_10`) and, with `u` concave and `v` convex, sufficient (`labour_foc_sufficient`).
* Definition 3 (`IsADEquilibriumLabour`). Log utility: consumption is a constant share of
  output (`labour_log_shares`), the hours condition `v′(ℓ_{i,t})θᵢYₜ = eᵢAₜ`
  (`labour_log_hours`), and with `θᵢ = eᵢ` all households work the same hours
  (`labour_log_equal_hours`). The guess `θᵢ = eᵢ`, `ℓ_{i,t} = L` with `v′(L)L = 1` is an
  equilibrium (`labour_log_equilibrium`, instance `labour_log_equilibrium_instance`).
* The static examples: with `c = wℓ` and utility `log c − v(ℓ)` the chosen hours do not depend
  on `w` (`labour_static_wage_independent`); with asset income `c = eAℓ + a` the first-order
  condition is `v′(ℓ) = eA/(eAℓ + a)` (`labour_static_asset_foc`), not `aA/(eAℓ + a)` as printed
  (`labour_static_asset_printed_counterexample`), and more assets mean fewer hours
  (`labour_assets_lower_hours`).

Departures: consumption positive, hours nonnegative, convergent budget and utility series; the
book's printed numerator `aᵢA` on p. 138 is corrected to `eᵢA`.
-/

namespace AKMM.CompetitiveEquilibrium

open MeasureTheory Filter Topology

variable {I : Type*} [MeasurableSpace I]

/-! ### The firm -/

/-- The firm's time-`t` profit `AL − wL`. -/
def labourProfit (A w L : ℝ) : ℝ := A * L - w * L

/-- `L` maximizes the static profit `AL − wL` over `L ≥ 0`. -/
def LabourStaticOpt (A w L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ L', 0 ≤ L' → labourProfit A w L' ≤ labourProfit A w L

/-- AKMM, (5.6), p. 136: `L` solves the firm's date-0 problem: nonnegative labour with a
convergent profit series that no other such plan beats. -/
def LabourFirmOpt (p A w L : ℕ → ℝ) : Prop :=
  (∀ t, 0 ≤ L t) ∧ Summable (fun t => p t * labourProfit (A t) (w t) (L t)) ∧
    ∀ L' : ℕ → ℝ, (∀ t, 0 ≤ L' t) → Summable (fun t => p t * labourProfit (A t) (w t) (L' t)) →
      ∑' t, p t * labourProfit (A t) (w t) (L' t) ≤ ∑' t, p t * labourProfit (A t) (w t) (L t)

/-- **AKMM, p. 136: the firm's problem is a sequence of static problems.** With positive prices
and a convergent profit series, `L` solves (5.6) iff each `Lₜ` maximizes `AₜLₜ − wₜLₜ`. -/
theorem eq_5_6_static {p A w L : ℕ → ℝ} (hp : ∀ t, 0 < p t)
    (hs : Summable (fun t => p t * labourProfit (A t) (w t) (L t))) :
    LabourFirmOpt p A w L ↔ ∀ t, LabourStaticOpt (A t) (w t) (L t) := by
  constructor
  · rintro ⟨hL, -, hmax⟩ t
    refine ⟨hL t, fun L' hL' => ?_⟩
    let M : ℕ → ℝ := fun n => if n = t then L' else L n
    have hMo : ∀ n ∉ ({t} : Finset ℕ), M n = L n := fun n hn => by
      simp only [Finset.mem_singleton] at hn; simp [M, hn]
    obtain ⟨hS, hE⟩ := ce_tsum_perturb (f := fun n => p n * labourProfit (A n) (w n) (L n))
      (g := fun n => p n * labourProfit (A n) (w n) (M n)) {t}
      (fun n hn => by simp only [hMo n hn]) hs
    have h := hmax M (fun n => by by_cases h : n = t <;> simp [M, h, hL', hL n]) hS
    rw [hE, Finset.sum_singleton] at h
    simp only [M, ite_true] at h
    have : p t * (labourProfit (A t) (w t) L' - labourProfit (A t) (w t) (L t)) ≤ 0 := by
      rw [mul_sub]; linarith
    have := nonpos_of_mul_nonpos_right this (hp t)
    linarith
  · intro h
    refine ⟨fun t => (h t).1, hs, fun L' hL' hs' => hs'.tsum_le_tsum (fun t => ?_) hs⟩
    exact mul_le_mul_of_nonneg_left ((h t).2 (L' t) (hL' t)) (hp t).le

/-- **AKMM, fn. 3, p. 136.** (i) If `w = A`, every `L ≥ 0` maximizes `AL − wL`; (ii) if
`A > w`, nothing does (profits rise without bound with scale); (iii) if `A < w`, `L = 0` is the
unique maximizer. -/
theorem labour_firm_fn3 {A w : ℝ} :
    (w = A → ∀ L, 0 ≤ L → LabourStaticOpt A w L) ∧ (w < A → ∀ L, ¬ LabourStaticOpt A w L) ∧
      (A < w → ∀ L, LabourStaticOpt A w L ↔ L = 0) := by
  refine ⟨fun h L hL => ⟨hL, fun L' _ => by simp [labourProfit, h]⟩, fun h L hopt => ?_,
    fun h L => ⟨fun hopt => ?_, fun hL => ?_⟩⟩
  · obtain ⟨hL, hmax⟩ := hopt
    have := hmax (L + 1) (by linarith)
    simp only [labourProfit] at this
    nlinarith
  · obtain ⟨hL, hmax⟩ := hopt
    have := hmax 0 le_rfl
    simp only [labourProfit, mul_zero, sub_zero] at this
    nlinarith
  · subst hL
    refine ⟨le_rfl, fun L' hL' => ?_⟩
    simp only [labourProfit, mul_zero, sub_zero]
    nlinarith

/-- **AKMM, p. 137: in equilibrium `wₜ = Aₜ`.** If the firm's plan solves (5.6) at positive
prices with positive employment `Lₜ > 0`, then `wₜ = Aₜ`. -/
theorem labour_wage_eq_productivity {p A w L : ℕ → ℝ} (hp : ∀ t, 0 < p t)
    (hopt : LabourFirmOpt p A w L) {t : ℕ} (hLt : 0 < L t) : w t = A t := by
  have hs := (eq_5_6_static hp hopt.2.1).1 hopt t
  rcases lt_trichotomy (w t) (A t) with h | h | h
  · exact absurd hs ((labour_firm_fn3.2.1 h) _)
  · exact h
  · exact absurd (((labour_firm_fn3.2.2 h) _).1 hs) hLt.ne'

/-! ### The household -/

/-- AKMM, (5.7), p. 136: the household budget set: positive consumption, nonnegative hours and
`Σ pₜcₜ = Σ pₜwₜeℓₜ`, both series convergent. -/
def LabourBudget (p w : ℕ → ℝ) (e : ℝ) (c l : ℕ → ℝ) : Prop :=
  (∀ t, 0 < c t) ∧ (∀ t, 0 ≤ l t) ∧ Summable (fun t => p t * c t) ∧
    Summable (fun t => p t * w t * e * l t) ∧ ∑' t, p t * c t = ∑' t, p t * w t * e * l t

/-- AKMM, Definition 3, part 1, p. 136: `(c, ℓ)` maximizes `Σ βᵗ[u(cₜ) − v(ℓₜ)]` (5.4) over the
budget set, among plans with a convergent utility series. -/
def LabourOptimal (u v : ℝ → ℝ) (β : ℝ) (p w : ℕ → ℝ) (e : ℝ) (c l : ℕ → ℝ) : Prop :=
  LabourBudget p w e c l ∧ Summable (fun t => β ^ t * (u (c t) - v (l t))) ∧
    ∀ x m, LabourBudget p w e x m → Summable (fun t => β ^ t * (u (x t) - v (m t))) →
      ∑' t, β ^ t * (u (x t) - v (m t)) ≤ ∑' t, β ^ t * (u (c t) - v (l t))

/-- **AKMM, (5.8), p. 137.** At an optimum with positive prices, `βˢu′(c_s)pₜ = βᵗu′(cₜ)p_s`,
i.e. `βᵗu′(cₜ) = λpₜ` with one multiplier. -/
theorem eq_5_8 {u v : ℝ → ℝ} {β e : ℝ} {p w c l du : ℕ → ℝ}
    (hopt : LabourOptimal u v β p w e c l) (hp : ∀ t, 0 < p t)
    (hd : ∀ t, HasDerivAt u (du t) (c t)) (s t : ℕ) :
    β ^ s * du s * p t = β ^ t * du t * p s := by
  rcases eq_or_ne s t with rfl | hst
  · ring
  obtain ⟨⟨hpos, hl, hsum, hsumw, hW⟩, husum, hmax⟩ := hopt
  set r := p s / p t with hr
  let x : ℝ → ℕ → ℝ := fun ε n =>
    if n = s then c s + ε else if n = t then c t - r * ε else c n
  have hxs : ∀ ε, x ε s = c s + ε := fun ε => by simp [x]
  have hxt : ∀ ε, x ε t = c t - r * ε := fun ε => by simp [x, hst.symm]
  have hxo : ∀ ε, ∀ n ∉ ({s, t} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [x, hn.1, hn.2]
  have hpt := hp t
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c s + ε ∧ 0 < c t - r * ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c s + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hpos s)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - r * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos t)
    exact h1.and h2
  have hd' : HasDerivAt (fun ε => ∑ n ∈ ({s, t} : Finset ℕ), β ^ n * (u (x ε n) - v (l n)))
      (β ^ s * du s + β ^ t * (du t * (-r))) 0 := by
    have e : (fun ε => ∑ n ∈ ({s, t} : Finset ℕ), β ^ n * (u (x ε n) - v (l n))) =
        fun ε => β ^ s * u (c s + ε) + β ^ t * u (c t - r * ε) -
          (β ^ s * v (l s) + β ^ t * v (l t)) := by
      funext ε; rw [Finset.sum_pair hst, hxs, hxt]; ring
    rw [e]
    have h1 : HasDerivAt (fun ε => u (c s + ε)) (du s) 0 := by
      have hu : HasDerivAt u (du s) (c s + 0) := by simpa using hd s
      simpa using hu.comp_const_add (c s) 0
    have h2 : HasDerivAt (fun ε => u (c t - r * ε)) (du t * (-r)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t - r * ε) (-r) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul r).const_sub (c t)
      have hu : HasDerivAt u (du t) (c t - r * 0) := by simpa using hd t
      exact hu.comp 0 hin
    exact ((h1.const_mul _).add (h2.const_mul _)).sub_const _
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * (u (c n) - v (l n)))
    (g := fun ε n => β ^ n * (u (x ε n) - v (l n))) {s, t} husum
    (fun ε n hn => by simp only [hxo ε n hn]) (fun n => by simp [x]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      refine hmax (x ε) l ⟨fun n => ?_, hl, ?_, hsumw, ?_⟩ hU
      · by_cases h1 : n = s
        · subst h1; rw [hxs]; exact hε.1
        by_cases h2 : n = t
        · subst h2; rw [hxt]; exact hε.2
        simp only [x, h1, h2, ite_false]; exact hpos n
      · exact (ce_tsum_perturb (f := fun n => p n * c n) (g := fun n => p n * x ε n) {s, t}
          (fun n hn => by simp only [hxo ε n hn]) hsum).1
      · obtain ⟨_, hE⟩ := ce_tsum_perturb (f := fun n => p n * c n)
          (g := fun n => p n * x ε n) {s, t} (fun n hn => by simp only [hxo ε n hn]) hsum
        have hz : p s * (c s + ε) - p s * c s + (p t * (c t - r * ε) - p t * c t) = 0 := by
          rw [hr]; field_simp; ring
        rw [hE, Finset.sum_pair hst, hxs, hxt, hz, add_zero, hW]) hd'
  rw [hr] at hzero
  field_simp at hzero
  linarith

/-- **AKMM, (5.9), p. 137.** At an optimum with `β > 0` and positive hours `ℓₜ > 0`,
`v′(ℓₜ) = ewₜu′(cₜ)`. Proved by working `ε` more hours at `t` and consuming the wage. -/
theorem eq_5_9 {u v : ℝ → ℝ} {β e : ℝ} {p w c l : ℕ → ℝ} {du dv : ℝ} {t : ℕ}
    (hopt : LabourOptimal u v β p w e c l) (hβ : 0 < β) (hlt : 0 < l t)
    (hdu : HasDerivAt u du (c t)) (hdv : HasDerivAt v dv (l t)) : dv = e * w t * du := by
  obtain ⟨⟨hpos, hl, hsum, hsumw, hW⟩, husum, hmax⟩ := hopt
  set k := e * w t with hk
  let x : ℝ → ℕ → ℝ := fun ε n => if n = t then c t + k * ε else c n
  let m : ℝ → ℕ → ℝ := fun ε n => if n = t then l t + ε else l n
  have hxo : ∀ ε, ∀ n ∉ ({t} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_singleton] at hn; simp [x, hn]
  have hmo : ∀ ε, ∀ n ∉ ({t} : Finset ℕ), m ε n = l n := fun ε n hn => by
    simp only [Finset.mem_singleton] at hn; simp [m, hn]
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t + k * ε ∧ 0 < l t + ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t + k * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos t)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < l t + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hlt)
    exact h1.and h2
  have hd' : HasDerivAt (fun ε => ∑ n ∈ ({t} : Finset ℕ), β ^ n * (u (x ε n) - v (m ε n)))
      (β ^ t * (du * k - dv)) 0 := by
    have e1 : (fun ε => ∑ n ∈ ({t} : Finset ℕ), β ^ n * (u (x ε n) - v (m ε n))) =
        fun ε => β ^ t * (u (c t + k * ε) - v (l t + ε)) := by
      funext ε; simp [x, m]
    rw [e1]
    have h1 : HasDerivAt (fun ε => u (c t + k * ε)) (du * k) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t + k * ε) k 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul k).const_add (c t)
      have hu : HasDerivAt u du (c t + k * 0) := by simpa using hdu
      exact hu.comp 0 hin
    have h2 : HasDerivAt (fun ε => v (l t + ε)) dv 0 := by
      have hv : HasDerivAt v dv (l t + 0) := by simpa using hdv
      simpa using hv.comp_const_add (l t) 0
    exact (h1.sub h2).const_mul _
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * (u (c n) - v (l n)))
    (g := fun ε n => β ^ n * (u (x ε n) - v (m ε n))) {t} husum
    (fun ε n hn => by simp only [hxo ε n hn, hmo ε n hn])
    (fun n => by simp only [x, m]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      have hS1 := ce_tsum_perturb (f := fun n => p n * c n) (g := fun n => p n * x ε n) {t}
        (fun n hn => by simp only [hxo ε n hn]) hsum
      have hS2 := ce_tsum_perturb (f := fun n => p n * w n * e * l n)
        (g := fun n => p n * w n * e * m ε n) {t} (fun n hn => by simp only [hmo ε n hn]) hsumw
      refine hmax (x ε) (m ε) ⟨fun n => ?_, fun n => ?_, hS1.1, hS2.1, ?_⟩ hU
      · by_cases h1 : n = t
        · subst h1; simp only [x, ite_true]; exact hε.1
        simp only [x, h1, ite_false]; exact hpos n
      · by_cases h1 : n = t
        · subst h1; simp only [m, ite_true]; exact hε.2.le
        simp only [m, h1, ite_false]; exact hl n
      · rw [hS1.2, hS2.2, hW, Finset.sum_singleton, Finset.sum_singleton]
        simp only [x, m, ite_true, hk]
        ring) hd'
  have := (pow_pos hβ t).ne'
  have h2 : du * k - dv = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd h this
    · exact h
  rw [hk] at h2
  linarith

/-- **AKMM, (5.10), p. 137.** At an optimum with `β > 0`, positive prices and `u′(cₜ) ≠ 0`,
`p_{t+1}/pₜ = βu′(c_{t+1})/u′(cₜ)`. -/
theorem eq_5_10 {u v : ℝ → ℝ} {β e : ℝ} {p w c l du : ℕ → ℝ}
    (hopt : LabourOptimal u v β p w e c l) (hβ : 0 < β) (hp : ∀ t, 0 < p t)
    (hd : ∀ t, HasDerivAt u (du t) (c t)) (t : ℕ) (hdt : du t ≠ 0) :
    p (t + 1) / p t = β * du (t + 1) / du t := by
  have h := eq_5_8 hopt hp hd t (t + 1)
  have := (hp t).ne'
  have hb := (pow_pos hβ t).ne'
  rw [div_eq_div_iff this hdt]
  rw [pow_succ] at h
  apply mul_left_cancel₀ hb
  linarith

/-- **AKMM, p. 137: the first-order conditions are sufficient.** If `u` lies below and `v` above
their tangents, `(c, ℓ)` is budget-feasible with a convergent utility series,
`βᵗu′(cₜ) = λpₜ` and `v′(ℓₜ) = ewₜu′(cₜ)`, and `β ≥ 0`, then `(c, ℓ)` is optimal. -/
theorem labour_foc_sufficient {u v : ℝ → ℝ} {β e lam : ℝ} {p w c l du dv : ℕ → ℝ}
    (hβ : 0 ≤ β) (hut : ∀ t x, 0 < x → u x ≤ u (c t) + du t * (x - c t))
    (hvt : ∀ t m, 0 ≤ m → v (l t) + dv t * (m - l t) ≤ v m)
    (h58 : ∀ t, β ^ t * du t = lam * p t) (h59 : ∀ t, dv t = e * w t * du t)
    (hb : LabourBudget p w e c l) (hU : Summable (fun t => β ^ t * (u (c t) - v (l t)))) :
    LabourOptimal u v β p w e c l := by
  refine ⟨hb, hU, fun x m hx hUx => ?_⟩
  obtain ⟨_, _, hcs, hcw, hcW⟩ := hb
  obtain ⟨hxp, hmp, hxs, hxw, hxW⟩ := hx
  have key : ∀ t, β ^ t * (u (x t) - v (m t)) ≤ β ^ t * (u (c t) - v (l t)) +
      lam * ((p t * x t - p t * c t) - (p t * w t * e * m t - p t * w t * e * l t)) := by
    intro t
    have h1 := hut t (x t) (hxp t)
    have h2 := hvt t (m t) (hmp t)
    have h3 : β ^ t * (u (x t) - v (m t)) ≤
        β ^ t * ((u (c t) + du t * (x t - c t)) - (v (l t) + dv t * (m t - l t))) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hβ t)
    have h4 : β ^ t * ((u (c t) + du t * (x t - c t)) - (v (l t) + dv t * (m t - l t))) =
        β ^ t * (u (c t) - v (l t)) +
          lam * ((p t * x t - p t * c t) - (p t * w t * e * m t - p t * w t * e * l t)) := by
      rw [h59 t]
      have : β ^ t * (du t * (x t - c t) - e * w t * du t * (m t - l t)) =
          (β ^ t * du t) * ((x t - c t) - e * w t * (m t - l t)) := by ring
      linear_combination this + (x t - c t - e * w t * (m t - l t)) * h58 t
    linarith
  have hS2 : Summable (fun t => lam * ((p t * x t - p t * c t) -
      (p t * w t * e * m t - p t * w t * e * l t))) :=
    ((hxs.sub hcs).sub (hxw.sub hcw)).mul_left lam
  have := hUx.tsum_le_tsum key (hU.add hS2)
  rw [hU.tsum_add hS2, tsum_mul_left, ((hxs.sub hcs)).tsum_sub (hxw.sub hcw),
    hxs.tsum_sub hcs, hxw.tsum_sub hcw, hxW, hcW] at this
  linarith

/-- **AKMM, Definition 3, p. 136.** An Arrow–Debreu equilibrium of the labour economy:
households optimize, the firm solves (5.6), and labour and goods markets clear,
`∫ eᵢℓ_{i,t} di = Lₜ` and `∫ c_{i,t} di = AₜLₜ`. -/
def IsADEquilibriumLabour (μ : Measure I) (u v : ℝ → ℝ) (β : ℝ) (e : I → ℝ)
    (A : ℕ → ℝ) (c l : I → ℕ → ℝ) (L p w : ℕ → ℝ) : Prop :=
  (∀ i, LabourOptimal u v β p w (e i) (c i) (l i)) ∧ LabourFirmOpt p A w L ∧
    ∀ t, ∫ i, e i * l i t ∂μ = L t ∧ ∫ i, c i t ∂μ = A t * L t

/-- **AKMM, p. 137: log consumption shares.** In an equilibrium with log utility, positive
prices, `p₀ = 1` and positive output `AₜLₜ`, `c_{i,t} = θᵢYₜ` with `Yₜ = AₜLₜ` and
`θᵢ = c_{i,0}/Y₀`. -/
theorem labour_log_shares {μ : Measure I} {v : ℝ → ℝ} {β : ℝ} {e : I → ℝ} {A : ℕ → ℝ}
    {c l : I → ℕ → ℝ} {L p w : ℕ → ℝ}
    (he : IsADEquilibriumLabour μ Real.log v β e A c l L p w) (hp : ∀ t, 0 < p t)
    (hp0 : p 0 = 1) (hY : ∀ t, 0 < A t * L t) (i : I) (t : ℕ) :
    c i t = c i 0 / (A 0 * L 0) * (A t * L t) := by
  obtain ⟨hopt, _, hclear⟩ := he
  have hfoc : ∀ i t, p t * c i t = β ^ t * c i 0 := by
    intro i t
    have hc := (hopt i).1.1
    have h := eq_5_8 (hopt i) hp (du := fun t => (c i t)⁻¹)
      (fun t => Real.hasDerivAt_log (hc t).ne') 0 t
    rw [hp0] at h
    have := (hc t).ne'
    have := (hc 0).ne'
    field_simp at h
    linarith
  have h : (fun i => p t * c i t) = fun i => β ^ t * c i 0 := funext fun i => hfoc i t
  have hi := congrArg (fun f => ∫ i, f i ∂μ) h
  simp only [integral_const_mul, (hclear _).2] at hi
  have hX := (hY 0).ne'
  have := (hp t).ne'
  have h1 := hfoc i t
  have e1 : c i t = β ^ t * c i 0 / p t := by field_simp; linarith
  have e2 : A t * L t = β ^ t * (A 0 * L 0) / p t := by field_simp; linarith
  rw [e1, e2, div_mul_div_comm,
    show c i 0 * (β ^ t * (A 0 * L 0)) = β ^ t * c i 0 * (A 0 * L 0) by ring,
    mul_comm (A 0 * L 0) (p t), mul_div_mul_right _ _ hX]

/-- **AKMM, p. 138: the log hours condition.** With log utility, `wₜ = Aₜ` and
`c_{i,t} = θᵢYₜ`, (5.9) reads `v′(ℓ_{i,t})θᵢYₜ = eᵢAₜ` at positive hours. -/
theorem labour_log_hours {v : ℝ → ℝ} {β e θ : ℝ} {p A c l : ℕ → ℝ} {Y : ℕ → ℝ} {dv : ℝ}
    {t : ℕ} (hopt : LabourOptimal Real.log v β p A e c l) (hβ : 0 < β) (hlt : 0 < l t)
    (hdv : HasDerivAt v dv (l t)) (hc : c t = θ * Y t) : dv * (θ * Y t) = e * A t := by
  have hct := hopt.1.1 t
  have h := eq_5_9 hopt hβ hlt (Real.hasDerivAt_log hct.ne') hdv
  rw [h, ← hc]
  field_simp

/-- **AKMM, p. 138: equal hours under `θᵢ = eᵢ`.** If `v′` is injective on the positive reals and
households `i, j` with `eᵢ, eⱼ > 0` have `v′(ℓ_{k,t})eₖYₜ = eₖAₜ`, they work the same hours. -/
theorem labour_log_equal_hours {dv : ℝ → ℝ} (hinj : Set.InjOn dv (Set.Ioi 0))
    {ei ej Yt At li lj : ℝ}
    (hei : 0 < ei) (hej : 0 < ej) (hY : 0 < Yt) (hli : 0 < li) (hlj : 0 < lj)
    (hi : dv li * (ei * Yt) = ei * At) (hj : dv lj * (ej * Yt) = ej * At) : li = lj := by
  apply hinj hli hlj
  have h1 : dv li = At / Yt := by field_simp; nlinarith
  have h2 : dv lj = At / Yt := by field_simp; nlinarith
  rw [h1, h2]

/-- **AKMM, pp. 137–138: the log equilibrium.** Let `0 < β < 1`, skills `eᵢ > 0` with
`∫ eᵢ di = 1`, productivity `Aₜ > 0` with `Σ βᵗ log Aₜ` convergent, and `v` convex with
`v′(L)L = 1` at some `L > 0`. Then `pₜ = βᵗA₀/Aₜ`, `wₜ = Aₜ`, `c_{i,t} = eᵢAₜL`,
`ℓ_{i,t} = L` and `Lₜ = L` form an equilibrium (Definition 3): `θᵢ = eᵢ` and equal hours. -/
theorem labour_log_equilibrium {μ : Measure I} [IsProbabilityMeasure μ] {v : ℝ → ℝ}
    {β Lbar dvL : ℝ} {e : I → ℝ} {A : ℕ → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (he : ∀ i, 0 < e i) (he1 : ∫ i, e i ∂μ = 1)
    (hA : ∀ t, 0 < A t) (hlogA : Summable (fun t => β ^ t * Real.log (A t)))
    (hL : 0 < Lbar) (hvt : ∀ m, 0 ≤ m → v Lbar + dvL * (m - Lbar) ≤ v m)
    (hfoc : dvL * Lbar = 1) :
    IsADEquilibriumLabour μ Real.log v β e A (fun i t => e i * A t * Lbar) (fun _ _ => Lbar)
      (fun _ => Lbar) (fun t => β ^ t * A 0 / A t) A := by
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  refine ⟨fun i => ?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · have hc : ∀ t, 0 < e i * A t * Lbar := fun t => mul_pos (mul_pos (he i) (hA t)) hL
    have hpc : (fun t => β ^ t * A 0 / A t * (e i * A t * Lbar)) =
        fun t => e i * A 0 * Lbar * β ^ t := by
      funext t; have := (hA t).ne'; field_simp
    have hpw : (fun t => β ^ t * A 0 / A t * A t * e i * Lbar) =
        fun t => e i * A 0 * Lbar * β ^ t := by
      funext t; have := (hA t).ne'; field_simp
    refine labour_foc_sufficient (du := fun t => (e i * A t * Lbar)⁻¹) (dv := fun _ => dvL)
      (lam := (e i * A 0 * Lbar)⁻¹) hβ0.le (fun t x hx => ce_log_tangent (hc t) hx)
      (fun t m hm => hvt m hm) (fun t => ?_) (fun t => ?_) ⟨hc, fun _ => hL.le, ?_, ?_, ?_⟩ ?_
    · have := (hA t).ne'; have := (hA 0).ne'; have := (he i).ne'; have := hL.ne'
      field_simp
    · have := (hA t).ne'; have := (he i).ne'; have := hL.ne'
      field_simp
      linarith
    · rw [hpc]; exact hgeo.mul_left _
    · rw [hpw]; exact hgeo.mul_left _
    · rw [hpc, hpw]
    · have e1 : (fun t => β ^ t * (Real.log (e i * A t * Lbar) - v Lbar)) =
          fun t => (Real.log (e i) + Real.log Lbar - v Lbar) * β ^ t + β ^ t * Real.log (A t) := by
        funext t
        rw [Real.log_mul (mul_pos (he i) (hA t)).ne' hL.ne', Real.log_mul (he i).ne' (hA t).ne']
        ring
      rw [e1]; exact (hgeo.mul_left _).add hlogA
  · have hpos : ∀ t, 0 < β ^ t * A 0 / A t := fun t =>
      div_pos (mul_pos (pow_pos hβ0 t) (hA 0)) (hA t)
    have hz : Summable (fun t => β ^ t * A 0 / A t * labourProfit (A t) (A t) Lbar) := by
      simp [labourProfit]
    exact (eq_5_6_static hpos hz).2 fun t => (labour_firm_fn3.1 rfl) Lbar hL.le
  · simp only
    rw [integral_mul_const, he1, one_mul]
  · simp only
    rw [integral_mul_const, integral_mul_const, he1, one_mul]

/-- **AKMM, pp. 137–138: an instance.** On `[0, 1]` with Lebesgue measure, unit skills,
`Aₜ = 1`, `v(ℓ) = ℓ²/2` (so `v′(1)·1 = 1`) and `β = 1/2`, the log equilibrium has `L = 1`. -/
theorem labour_log_equilibrium_instance :
    IsADEquilibriumLabour (volume : Measure unitInterval) Real.log (fun l => l ^ 2 / 2) (1 / 2)
      (fun _ => 1) (fun _ => 1) (fun i t => (fun _ => (1 : ℝ)) i * (fun _ => (1 : ℝ)) t * 1)
      (fun _ _ => 1) (fun _ => 1) (fun t => (1 / 2 : ℝ) ^ t * 1 / 1) (fun _ => 1) :=
  labour_log_equilibrium (dvL := 1) (by norm_num) (by norm_num) (fun _ => one_pos) (by simp)
    (fun _ => one_pos) (by simp) one_pos (fun m _ => by nlinarith [sq_nonneg (m - 1)])
    (by norm_num)

/-! ### The static examples -/

/-- **AKMM, p. 138: with labour income only, hours do not depend on the wage.** For `w, w' > 0`,
`ℓ > 0` maximizes `log(wℓ) − v(ℓ)` over `ℓ > 0` iff it maximizes `log(w'ℓ) − v(ℓ)`. -/
theorem labour_static_wage_independent {v : ℝ → ℝ} {w w' l : ℝ} (hw : 0 < w) (hw' : 0 < w') :
    (∀ m, 0 < m → Real.log (w * m) - v m ≤ Real.log (w * l) - v l) → 0 < l →
      ∀ m, 0 < m → Real.log (w' * m) - v m ≤ Real.log (w' * l) - v l := by
  intro h hl m hm
  have := h m hm
  rw [Real.log_mul hw.ne' hm.ne', Real.log_mul hw.ne' hl.ne'] at this
  rw [Real.log_mul hw'.ne' hm.ne', Real.log_mul hw'.ne' hl.ne']
  linarith

/-- **AKMM, p. 138, corrected: the first-order condition with asset income.** If `ℓ > 0`
maximizes `log(eAℓ + a) − v(ℓ)` over `ℓ ≥ 0` with `eAℓ + a > 0`, then
`v′(ℓ) = eA/(eAℓ + a)`. The book prints the numerator as `aᵢA`. -/
theorem labour_static_asset_foc {v : ℝ → ℝ} {e A a l dv : ℝ} (hl : 0 < l) (hc : 0 < e * A * l + a)
    (hmax : ∀ m, 0 ≤ m → 0 < e * A * m + a →
      Real.log (e * A * m + a) - v m ≤ Real.log (e * A * l + a) - v l)
    (hdv : HasDerivAt v dv l) : dv = e * A / (e * A * l + a) := by
  have hloc : IsLocalMax (fun m => Real.log (e * A * m + a) - v m) l := by
    have h1 : ∀ᶠ m in 𝓝 l, 0 < m := lt_mem_nhds hl
    have h2 : ∀ᶠ m in 𝓝 l, 0 < e * A * m + a :=
      continuousAt_const.eventually_lt
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt (by simpa using hc)
    filter_upwards [h1, h2] with m hm1 hm2
    exact hmax m hm1.le hm2
  have hd : HasDerivAt (fun m => Real.log (e * A * m + a) - v m)
      ((e * A) / (e * A * l + a) - dv) l := by
    have hin : HasDerivAt (fun m => e * A * m + a) (e * A) l := by
      simpa using ((hasDerivAt_id l).const_mul (e * A)).add_const a
    have := ((Real.hasDerivAt_log hc.ne').comp l hin).sub hdv
    rw [← div_eq_inv_mul] at this
    exact this
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- **AKMM, p. 138: the printed condition `v′(ℓ) = aA/(eAℓ + a)` is false.** With `e = A = 1`,
`a = 2` and `v(ℓ) = ℓ²/2`, hours `ℓ* = √2 − 1` maximize `log(ℓ + 2) − ℓ²/2` over `ℓ ≥ 0`, but
`v′(ℓ*) = ℓ*` while `aA/(eAℓ* + a) = 2ℓ*`. -/
theorem labour_static_asset_printed_counterexample :
    let l := Real.sqrt 2 - 1
    0 < l ∧ (∀ m, 0 ≤ m → Real.log (m + 2) - m ^ 2 / 2 ≤ Real.log (l + 2) - l ^ 2 / 2) ∧
      l ≠ 2 * 1 / (1 * 1 * l + 2) := by
  intro l
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hl : 0 < l := by simp only [l]; linarith
  have hfoc : l * (l + 2) = 1 := by simp only [l]; nlinarith
  refine ⟨hl, fun m hm => ?_, ?_⟩
  · have h1 := ce_log_tangent (show 0 < l + 2 by linarith) (show 0 < m + 2 by linarith)
    have h2 : (l + 2)⁻¹ = l := by
      have : l + 2 ≠ 0 := by linarith
      field_simp; linarith
    rw [h2] at h1
    nlinarith [sq_nonneg (m - l)]
  · intro h
    have h3 : l * (l + 2) = 2 := by
      field_simp at h
      nlinarith
    linarith

/-- **AKMM, p. 138: more assets, fewer hours.** If `v′` is increasing and hours `ℓ₁, ℓ₂ > 0`
satisfy the first-order condition `v′(ℓ)(eAℓ + a) = eA` at asset levels `a₁ < a₂` (with
`eA > 0`), then `ℓ₂ < ℓ₁`. -/
theorem labour_assets_lower_hours {dv : ℝ → ℝ} (hmono : Monotone dv) {e A a1 a2 l1 l2 : ℝ}
    (heA : 0 < e * A) (ha : a1 < a2) (hc1 : 0 < e * A * l1 + a1)
    (h1 : dv l1 * (e * A * l1 + a1) = e * A) (h2 : dv l2 * (e * A * l2 + a2) = e * A) :
    l2 < l1 := by
  by_contra hle'
  have hle := not_lt.1 hle'
  have hv1 : 0 < dv l1 := by
    by_contra h; have h' := not_lt.1 h; nlinarith
  have hv := hmono hle
  have : dv l1 * (e * A * l1 + a1) < dv l2 * (e * A * l2 + a2) := by
    have : e * A * l1 + a1 < e * A * l2 + a2 := by nlinarith
    calc dv l1 * (e * A * l1 + a1) < dv l1 * (e * A * l2 + a2) := by
          exact mul_lt_mul_of_pos_left this hv1
      _ ≤ dv l2 * (e * A * l2 + a2) := by
          exact mul_le_mul_of_nonneg_right hv (by linarith)
  linarith

end AKMM.CompetitiveEquilibrium
