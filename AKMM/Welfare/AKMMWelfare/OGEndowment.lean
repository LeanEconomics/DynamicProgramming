/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCompetitiveEquilibrium.OGEconomies
import AKMMCompetitiveEquilibrium.Sequential
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Overlapping generations: the endowment economy

AKMM, §6.4.1, pp. 176–180. Two-period lives, generation `t ≥ 0` with utility
`log c_y + log c_o`, the initial old with `log c`; endowments `ω_{y,t}`, `ω_{o,t}`. The sequential
equilibrium is Chapter 5's Definition 11 (`IsOGEndowEquilibrium 0 Real.log 1`).

* (6.5)–(6.6): the young's optimum (`eq_6_5_6_6`, `og_log_consumption`); the equilibrium is
  unique: autarky with `qₜ = ω_{y,t}/ω_{o,t+1}` (`og_log_equilibrium_iff`).
* Pareto optimality (`ogFeasible`, `ogDominates`, `ogParetoOptimal`); the equilibrium in
  Arrow–Debreu form (`ogADEquilibrium`, from the sequential one: `og_ad_of_seq`).
* **The First Welfare Theorem when the proof goes through** (p. 178): for any utilities strictly
  increasing in `c_y`, an equilibrium is Pareto optimal as soon as `pₜω_{y,t} → 0`, with
  `pₜ = q₀⋯q_{t−1}` (`og_fwt_value`); in particular when the present value `Σ pₜωₜ` is finite
  (`og_fwt_finite_value`). The proof sums the budgets over finitely many generations.
* The examples: `(3, 1)` (`q = 3`, net rate `−2/3`; `(2, 2)` Pareto dominates:
  `og_example_3_1`), `(1, 3)` (`q = 1/3`; Pareto optimal, and `(2, 2)` hurts the initial old:
  `og_example_1_3`), `(2, 2)` (Pareto optimal though `Σ pₜωₜ = ∞`: `og_example_2_2`, via the
  growing-transfer argument of Figure 6.3, `og_equal_endowments_optimal`).
* **Balasko–Shell for the stationary log economy**: the equilibrium is Pareto optimal iff
  `Σ 1/pₜ = ∞` iff `ω_y ≤ ω_o` (`og_balasko_shell_stationary_log`), with the book's sums
  (`og_balasko_shell_sums`).
* Transfers that stop hurt the last giver (`og_finite_transfers_hurt`).

**Correction (p. 179).** "Whenever the gross real interest rate `pₜ/p_{t+1}` converges … the
equilibrium is optimal if and only if the limit net real interest rate is equal to or above 0"
is false at 0. In the log economy with `ω_{y,t} = 1`, `ω_{o,t} = ((t+1)/(t+2))²`, the unique
equilibrium has gross rate `((t+2)/(t+3))² → 1` and is Pareto dominated
(`og_limit_rate_one_counterexample`), while the `(2, 2)` economy has gross rate `1` and is
optimal. What holds: a limit gross rate above one gives optimality (any monotone utilities,
bounded endowments: `og_limit_rate_gt_one`), and below one gives inefficiency (log utility,
young endowments bounded below: `og_limit_rate_lt_one_log`).

The general Balasko–Shell theorem (curvature and boundedness conditions the book does not
state) is not formalised.
-/

namespace AKMM.Welfare

open Filter Topology AKMM.CompetitiveEquilibrium

/-- **AKMM, (6.5)–(6.6), p. 177.** With `q, ω_y, ω_o′ > 0`, saving `a` (in bonds paying one unit
next period) solves `max log(ω_y − qa) + log(ω_o′ + a)` iff `a = (ω_y − qω_o′)/(2q)`. -/
theorem eq_6_5_6_6 {q ωy ωo' a : ℝ} (hq : 0 < q) (hy : 0 < ωy) (ho : 0 < ωo') :
    OGSavingOpt Real.log 1 q ωy ωo' a ↔ a = (ωy - q * ωo') / (2 * q) := by
  set as := (ωy - q * ωo') / (2 * q) with has
  have h1 : ωy - q * as = (ωy + q * ωo') / 2 := by rw [has]; field_simp; ring
  have h2 : ωo' + as = (ωy / q + ωo') / 2 := by rw [has]; field_simp; ring
  have hp1 : 0 < ωy - q * as := by rw [h1]; positivity
  have hp2 : 0 < ωo' + as := by rw [h2]; positivity
  have hprod : ∀ x, (ωy - q * as) * (ωo' + as) - (ωy - q * x) * (ωo' + x) = q * (x - as) ^ 2 := by
    intro x; rw [has]; field_simp; ring
  have hval : ∀ x, 0 < ωy - q * x → 0 < ωo' + x →
      Real.log (ωy - q * x) + 1 * Real.log (ωo' + x) ≤
        Real.log (ωy - q * as) + 1 * Real.log (ωo' + as) := by
    intro x hx1 hx2
    rw [one_mul, one_mul, ← Real.log_mul hx1.ne' hx2.ne', ← Real.log_mul hp1.ne' hp2.ne']
    exact Real.log_le_log (mul_pos hx1 hx2) (by nlinarith [hprod x, sq_nonneg (x - as)])
  constructor
  · rintro ⟨ha1, ha2, hmax⟩
    have h3 := hmax as hp1 hp2
    have h4 := hval a ha1 ha2
    rw [one_mul, one_mul, ← Real.log_mul hp1.ne' hp2.ne', ← Real.log_mul ha1.ne' ha2.ne'] at h3 h4
    have heq := Real.log_injOn_pos (Set.mem_Ioi.2 (mul_pos hp1 hp2))
      (Set.mem_Ioi.2 (mul_pos ha1 ha2)) (le_antisymm h3 h4)
    have hz : q * (a - as) ^ 2 = 0 := by rw [← hprod a, heq, sub_self]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 hz).resolve_left hq.ne')
    linarith
  · rintro rfl
    exact ⟨hp1, hp2, hval⟩

/-- **AKMM, (6.5)–(6.6), p. 177: consumption and saving.** At the optimum
`c_{y,t} = (ω_y + qₜω_o)/2`, `c_{o,t+1} = (ω_y/qₜ + ω_o)/2`, and saving when young is
`ω_y − c_{y,t} = (ω_y − qₜω_o)/2`. -/
theorem og_log_consumption {q ωy ωo' : ℝ} (hq : 0 < q) :
    ωy - q * ((ωy - q * ωo') / (2 * q)) = (ωy + q * ωo') / 2 ∧
      ωo' + (ωy - q * ωo') / (2 * q) = (ωy / q + ωo') / 2 ∧
      ωy - (ωy + q * ωo') / 2 = (ωy - q * ωo') / 2 := by
  refine ⟨by field_simp; ring, by field_simp; ring, by ring⟩

/-- **AKMM, p. 177: the equilibrium is unique.** With positive endowments and bond prices, the
log economy is in equilibrium (Chapter 5's Definition 11, `t₀ = 0`) iff `a_{t+1} = 0`,
consumption is autarkic and `qₜ = ω_{y,t}/ω_{o,t+1}` at every date. -/
theorem og_log_equilibrium_iff {ωy ωo cy co a q : ℕ → ℝ} (hωy : ∀ t, 0 < ωy t)
    (hωo : ∀ t, 0 < ωo t) (hq : ∀ t, 0 < q t) :
    IsOGEndowEquilibrium 0 Real.log 1 ωy ωo cy co a q ↔
      (∀ t, q t = ωy t / ωo (t + 1)) ∧ ∀ t, a (t + 1) = 0 ∧ cy t = ωy t ∧ co t = ωo t := by
  constructor
  · intro he
    have hz := og_autarky he fun t => (hq t).ne'
    refine ⟨fun t => ?_, hz⟩
    have hopt := (he.1 t (Nat.zero_le _)).2.2
    rw [(hz t).1, eq_6_5_6_6 (hq t) (hωy t) (hωo (t + 1))] at hopt
    have := hωo (t + 1)
    have := hq t
    field_simp at hopt ⊢
    linarith
  · rintro ⟨hqt, hz⟩
    refine ⟨fun t _ => ⟨?_, ?_, ?_⟩, (hz 0).2.2, fun t => by rw [(hz t).2.1, (hz t).2.2]⟩
    · rw [(hz t).2.1, (hz t).1, mul_zero, sub_zero]
    · rw [(hz (t + 1)).2.2, (hz t).1, add_zero]
    · rw [(hz t).1, eq_6_5_6_6 (hq t) (hωy t) (hωo (t + 1)), hqt t]
      have := hωo (t + 1)
      field_simp
      ring

/-- A feasible allocation of the OG endowment economy (AKMM, p. 177): positive consumption and
`c_{y,t} + c_{o,t} ≤ ω_{y,t} + ω_{o,t}`; `co 0` is the initial old's consumption. -/
def ogFeasible (ωy ωo cy co : ℕ → ℝ) : Prop :=
  (∀ t, 0 < cy t ∧ 0 < co t) ∧ ∀ t, cy t + co t ≤ ωy t + ωo t

/-- `(cy', co')` Pareto dominates `(cy, co)`: the initial old (utility increasing in `c_{o,0}`)
and every generation `t` (utility `Uₜ(c_{y,t}, c_{o,t+1})`) are at least as well off, one
strictly. -/
def ogDominates (U : ℕ → ℝ → ℝ → ℝ) (cy co cy' co' : ℕ → ℝ) : Prop :=
  co 0 ≤ co' 0 ∧ (∀ t, U t (cy t) (co (t + 1)) ≤ U t (cy' t) (co' (t + 1))) ∧
    (co 0 < co' 0 ∨ ∃ t, U t (cy t) (co (t + 1)) < U t (cy' t) (co' (t + 1)))

/-- AKMM, p. 178: Pareto optimality in the OG endowment economy. -/
def ogParetoOptimal (U : ℕ → ℝ → ℝ → ℝ) (ωy ωo cy co : ℕ → ℝ) : Prop :=
  ogFeasible ωy ωo cy co ∧ ¬ ∃ cy' co', ogFeasible ωy ωo cy' co' ∧ ogDominates U cy co cy' co'

/-- The utility of every generation in §6.4.1: `log c_y + log c_o`. -/
noncomputable def ogLogU : ℕ → ℝ → ℝ → ℝ := fun _ x y => Real.log x + Real.log y

/-- AKMM, p. 178: the equilibrium in Arrow–Debreu form, budgets in date-`t` goods: positive
consumption, the initial old consume `ω_{o,0}`, markets clear, and each generation's bundle
satisfies `c_y + qₜc_o′ = ω_y + qₜω_o′` and maximises `Uₜ` on that budget. -/
def ogADEquilibrium (U : ℕ → ℝ → ℝ → ℝ) (ωy ωo q cy co : ℕ → ℝ) : Prop :=
  (∀ t, 0 < cy t ∧ 0 < co t) ∧ co 0 = ωo 0 ∧ (∀ t, cy t + co t = ωy t + ωo t) ∧
    ∀ t, cy t + q t * co (t + 1) = ωy t + q t * ωo (t + 1) ∧
      ∀ x y, 0 < x → 0 < y → x + q t * y ≤ ωy t + q t * ωo (t + 1) →
        U t x y ≤ U t (cy t) (co (t + 1))

/-- AKMM, p. 178: a sequential equilibrium of the log economy (Chapter 5's Definition 11) is an
equilibrium in Arrow–Debreu form. -/
theorem og_ad_of_seq {ωy ωo cy co a q : ℕ → ℝ} (hωo : ∀ t, 0 < ωo t)
    (he : IsOGEndowEquilibrium 0 Real.log 1 ωy ωo cy co a q) :
    ogADEquilibrium ogLogU ωy ωo q cy co := by
  obtain ⟨hopt, hco0, hclear⟩ := he
  have hco : ∀ t, 0 < co t := by
    intro t
    rcases t with _ | t
    · rw [hco0]; exact hωo 0
    · obtain ⟨_, h2, h3⟩ := hopt t (Nat.zero_le _)
      rw [h2]; exact h3.2.1
  refine ⟨fun t => ⟨?_, hco t⟩, hco0, hclear, fun t => ⟨?_, fun x y hx hy hb => ?_⟩⟩
  · obtain ⟨h1, _, h3⟩ := hopt t (Nat.zero_le _)
    rw [h1]; exact h3.1
  · obtain ⟨h1, h2, _⟩ := hopt t (Nat.zero_le _)
    rw [h1, h2]; ring
  · obtain ⟨h1, h2, ⟨_, _, hmax⟩⟩ := hopt t (Nat.zero_le _)
    have hs1 : x ≤ ωy t - q t * (y - ωo (t + 1)) := by linarith
    have := hmax (y - ωo (t + 1)) (by linarith) (by linarith)
    simp only [one_mul, add_sub_cancel] at this
    simp only [ogLogU, h1, h2]
    linarith [Real.log_le_log hx hs1]

/-- **AKMM, p. 178: the First Welfare Theorem in the OG economy when the proof goes through.**
If every `Uₜ` is strictly increasing in `c_y`, bond prices are positive, `(cy, co)` is an
equilibrium in Arrow–Debreu form and `pₜω_{y,t} → 0` with `pₜ = q₀⋯q_{t−1}`, the equilibrium is
Pareto optimal. -/
theorem og_fwt_value {U : ℕ → ℝ → ℝ → ℝ}
    (hU : ∀ t x x' y, 0 < x → x < x' → 0 < y → U t x y < U t x' y) {ωy ωo q cy co : ℕ → ℝ}
    (hq : ∀ t, 0 < q t) (he : ogADEquilibrium U ωy ωo q cy co)
    (hlim : Tendsto (fun t => seqPrice q t * ωy t) atTop (𝓝 0)) :
    ogParetoOptimal U ωy ωo cy co := by
  obtain ⟨hpos, hco0, hclear, hgen⟩ := he
  refine ⟨⟨hpos, fun t => (hclear t).le⟩, ?_⟩
  rintro ⟨cy', co', ⟨hpos', hfeas'⟩, hold, hle, hstrict⟩
  set P := seqPrice q with hP
  have hPpos : ∀ t, 0 < P t := seqPrice_pos hq
  have hP0 : P 0 = 1 := by simp [hP, seqPrice]
  -- each generation's alternative costs at least its wealth, strictly for a strict gain
  have hcost : ∀ t, ωy t + q t * ωo (t + 1) ≤ cy' t + q t * co' (t + 1) := by
    intro t
    by_contra hcon
    push Not at hcon
    set x' := ωy t + q t * ωo (t + 1) - q t * co' (t + 1)
    have hx' : cy' t < x' := by simp only [x']; linarith
    have := (hgen t).2 x' (co' (t + 1)) (by linarith [(hpos' t).1]) (hpos' (t + 1)).2
      (by simp only [x']; linarith)
    have := hU t _ _ _ (hpos' t).1 hx' (hpos' (t + 1)).2
    linarith [hle t]
  have hcost_strict : ∀ t, U t (cy t) (co (t + 1)) < U t (cy' t) (co' (t + 1)) →
      ωy t + q t * ωo (t + 1) < cy' t + q t * co' (t + 1) := by
    intro t ht
    by_contra hcon
    push Not at hcon
    have := (hgen t).2 _ _ (hpos' t).1 (hpos' (t + 1)).2 hcon
    linarith
  set g : ℕ → ℝ := fun t => P t * (cy' t + q t * co' (t + 1) - (ωy t + q t * ωo (t + 1)))
  have hg0 : ∀ t, 0 ≤ g t := fun t => mul_nonneg (hPpos t).le (by linarith [hcost t])
  set gold := co' 0 - ωo 0
  have hgold : 0 ≤ gold := by simp only [gold]; linarith
  -- the summed budgets
  have hsum : ∀ N, ∑ t ∈ Finset.range N, g t + gold ≤ P N * (ωy N - cy' N) := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add, hP0, one_mul, gold]
              linarith [hfeas' 0]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hstep : P N * (ωy N - cy' N) + g N ≤ P (N + 1) * (ωy (N + 1) - cy' (N + 1)) := by
        have e : P N * (ωy N - cy' N) + g N = P (N + 1) * (co' (N + 1) - ωo (N + 1)) := by
          simp only [g, hP, seqPrice_succ]; ring
        rw [e]
        exact mul_le_mul_of_nonneg_left (by linarith [hfeas' (N + 1)]) (hPpos _).le
      linarith
  -- a strictly positive gap
  obtain ⟨G, T, hG, hGT⟩ : ∃ G T, 0 < G ∧ ∀ N, T < N → G ≤ ∑ t ∈ Finset.range N, g t + gold := by
    rcases hstrict with h | ⟨T, hT⟩
    · refine ⟨gold, 0, by simp only [gold]; linarith, fun N _ => ?_⟩
      linarith [Finset.sum_nonneg fun t (_ : t ∈ Finset.range N) => hg0 t]
    · refine ⟨g T, T, mul_pos (hPpos T) (by linarith [hcost_strict T hT]), fun N hN => ?_⟩
      have := Finset.single_le_sum (fun t _ => hg0 t) (Finset.mem_range.2 hN)
      linarith
  have hev : ∀ᶠ N in atTop, P N * ωy N < G := hlim.eventually (gt_mem_nhds hG)
  obtain ⟨N, hN⟩ := (hev.and (eventually_gt_atTop T)).exists
  have h1 := hGT N hN.2
  have h2 := hsum N
  have h3 : 0 < P N * cy' N := mul_pos (hPpos N) (hpos' N).1
  linarith [hN.1]

/-- **AKMM, p. 178: finite present value.** If `Σ pₜ(ω_{y,t} + ω_{o,t})` converges (positive
endowments), `pₜω_{y,t} → 0`, so `og_fwt_value` applies: the equilibrium is Pareto optimal. -/
theorem og_fwt_finite_value {U : ℕ → ℝ → ℝ → ℝ}
    (hU : ∀ t x x' y, 0 < x → x < x' → 0 < y → U t x y < U t x' y) {ωy ωo q cy co : ℕ → ℝ}
    (hq : ∀ t, 0 < q t) (hωy : ∀ t, 0 < ωy t) (hωo : ∀ t, 0 < ωo t)
    (he : ogADEquilibrium U ωy ωo q cy co)
    (hsum : Summable fun t => seqPrice q t * (ωy t + ωo t)) : ogParetoOptimal U ωy ωo cy co := by
  refine og_fwt_value hU hq he ?_
  have h0 := hsum.tendsto_atTop_zero
  refine squeeze_zero (fun t => (mul_pos (seqPrice_pos hq t) (hωy t)).le) (fun t => ?_) h0
  exact mul_le_mul_of_nonneg_left (by linarith [hωo t]) (seqPrice_pos hq t).le

/-- `log` is strictly increasing in `c_y`. -/
theorem og_logU_mono : ∀ t x x' y, 0 < x → x < x' → 0 < y → ogLogU t x y < ogLogU t x' y := by
  intro _ x x' y hx hxx' _
  simp only [ogLogU]
  linarith [Real.log_lt_log hx hxx']

/-- The stationary autarky equilibrium in Arrow–Debreu form at `q = ω_y/ω_o`. -/
theorem og_stationary_ad {ωy ωo : ℝ} (hy : 0 < ωy) (ho : 0 < ωo) :
    ogADEquilibrium ogLogU (fun _ => ωy) (fun _ => ωo) (fun _ => ωy / ωo) (fun _ => ωy)
      (fun _ => ωo) := by
  refine og_ad_of_seq (a := fun _ => 0) (fun _ => ho) ?_
  exact (og_log_equilibrium_iff (fun _ => hy) (fun _ => ho) (fun _ => div_pos hy ho)).2
    ⟨fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- **AKMM, pp. 179–180 and Figure 6.3: the `(ω, ω)` economy.** With `ω_y = ω_o = ω > 0` and log
utility, autarky is Pareto optimal. A dominating allocation would need transfers to the old
`εₜ = c_{o,t} − ω ≥ 0`, positive at some date, with `ε_{t+1} − εₜ ≥ εₜ²/ω`; they would grow
without bound, but `εₜ < ω`. -/
theorem og_equal_endowments_optimal {ω : ℝ} (hω : 0 < ω) :
    ogParetoOptimal ogLogU (fun _ => ω) (fun _ => ω) (fun _ => ω) (fun _ => ω) := by
  refine ⟨⟨fun _ => ⟨hω, hω⟩, fun _ => le_rfl⟩, ?_⟩
  rintro ⟨cy', co', ⟨hpos, hfeas⟩, hold, hle, hstrict⟩
  set ε : ℕ → ℝ := fun t => co' t - ω with hε
  have hlt : ∀ t, ε t < ω := fun t => by
    simp only [hε]; linarith [hfeas t, (hpos t).1]
  have hy : ∀ t, cy' t ≤ ω - ε t := fun t => by simp only [hε]; linarith [hfeas t]
  -- each generation: `(ω − εₜ)(ω + ε_{t+1}) ≥ c_{y,t}c_{o,t+1} ≥ ω²`
  have hprod : ∀ t, ω * ω ≤ cy' t * co' (t + 1) := by
    intro t
    have := hle t
    simp only [ogLogU] at this
    rw [← Real.log_mul hω.ne' hω.ne', ← Real.log_mul (hpos t).1.ne' (hpos (t + 1)).2.ne'] at this
    exact (Real.log_le_log_iff (mul_pos hω hω) (mul_pos (hpos t).1 (hpos (t + 1)).2)).1 this
  have hkey : ∀ t, ω * ω ≤ (ω - ε t) * (ω + ε (t + 1)) := by
    intro t
    have h1 : cy' t * co' (t + 1) ≤ (ω - ε t) * co' (t + 1) :=
      mul_le_mul_of_nonneg_right (hy t) (hpos (t + 1)).2.le
    have h2 : co' (t + 1) = ω + ε (t + 1) := by simp only [hε]; ring
    rw [h2] at h1
    linarith [hprod t]
  have hnn : ∀ t, 0 ≤ ε t := by
    intro t
    induction t with
    | zero => simp only [hε]; linarith
    | succ t ih =>
      have := hkey t
      have := hlt t
      by_contra hneg
      push Not at hneg
      nlinarith
  have hgrow : ∀ t, ε t * ε t ≤ ω * (ε (t + 1) - ε t) := by
    intro t
    have h1 := hkey t
    have h2 := hnn t
    have h3 := hlt t
    have h4 : ε t * ε t ≤ (ε (t + 1) - ε t) * (ω - ε t) := by nlinarith
    have h5 : 0 ≤ ε (t + 1) - ε t := by
      by_contra hneg
      push Not at hneg
      nlinarith
    nlinarith
  -- a strictly positive transfer
  obtain ⟨s, hs⟩ : ∃ s, 0 < ε s := by
    rcases hstrict with h | ⟨T, hT⟩
    · exact ⟨0, by simp only [hε]; linarith⟩
    · refine ⟨T + 1, ?_⟩
      have hT' : ω * ω < cy' T * co' (T + 1) := by
        simp only [ogLogU] at hT
        rw [← Real.log_mul hω.ne' hω.ne', ← Real.log_mul (hpos T).1.ne'
          (hpos (T + 1)).2.ne'] at hT
        exact (Real.log_lt_log_iff (mul_pos hω hω) (mul_pos (hpos T).1 (hpos (T + 1)).2)).1 hT
      have h1 : cy' T * co' (T + 1) ≤ (ω - ε T) * co' (T + 1) :=
        mul_le_mul_of_nonneg_right (hy T) (hpos (T + 1)).2.le
      have h2 : co' (T + 1) = ω + ε (T + 1) := by simp only [hε]; ring
      rw [h2] at h1
      have := hnn T
      have := hlt T
      by_contra hneg
      push Not at hneg
      nlinarith
  -- linear growth from date `s`
  have hlin : ∀ n : ℕ, ε s ≤ ε (s + n) ∧ ε s + n * (ε s * ε s / ω) ≤ ε (s + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hg := hgrow (s + n)
      have hsq : ε s * ε s ≤ ε (s + n) * ε (s + n) :=
        mul_le_mul ih.1 ih.1 hs.le (hs.le.trans ih.1)
      have : ε s * ε s / ω ≤ ε (s + n + 1) - ε (s + n) := by
        rw [div_le_iff₀ hω]; nlinarith
      push_cast
      rw [← add_assoc]
      constructor <;> nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (ω / (ε s * ε s / ω))
  have hq : 0 < ε s * ε s / ω := by positivity
  have h1 := (hlin n).2
  have h2 := hlt (s + n)
  have : ω < n * (ε s * ε s / ω) := by rwa [div_lt_iff₀ hq] at hn
  linarith

/-- **AKMM, p. 178: `ω_y > ω_o`.** The constant allocation `m = (ω_y + ω_o)/2` is feasible and
Pareto dominates autarky: the initial old gain, and every generation gains since
`2 log m > log ω_y + log ω_o`. -/
theorem og_stationary_improvement {ωy ωo : ℝ} (ho : 0 < ωo) (hlt : ωo < ωy) :
    ogFeasible (fun _ => ωy) (fun _ => ωo) (fun _ => (ωy + ωo) / 2) (fun _ => (ωy + ωo) / 2) ∧
      ogDominates ogLogU (fun _ => ωy) (fun _ => ωo) (fun _ => (ωy + ωo) / 2)
        (fun _ => (ωy + ωo) / 2) ∧
      ¬ ogParetoOptimal ogLogU (fun _ => ωy) (fun _ => ωo) (fun _ => ωy) (fun _ => ωo) := by
  have hm : 0 < (ωy + ωo) / 2 := by linarith
  have hgain : Real.log ωy + Real.log ωo < Real.log ((ωy + ωo) / 2) + Real.log ((ωy + ωo) / 2) := by
    rw [← Real.log_mul (by linarith) ho.ne', ← Real.log_mul hm.ne' hm.ne']
    exact Real.log_lt_log (by nlinarith) (by nlinarith [sq_pos_of_pos (sub_pos.2 hlt)])
  have hF : ogFeasible (fun _ => ωy) (fun _ => ωo) (fun _ => (ωy + ωo) / 2)
      (fun _ => (ωy + ωo) / 2) := ⟨fun _ => ⟨hm, hm⟩, fun _ => by linarith⟩
  have hD : ogDominates ogLogU (fun _ => ωy) (fun _ => ωo) (fun _ => (ωy + ωo) / 2)
      (fun _ => (ωy + ωo) / 2) :=
    ⟨by linarith, fun _ => hgain.le, Or.inl (by linarith)⟩
  exact ⟨hF, hD, fun h => h.2 ⟨_, _, hF, hD⟩⟩

/-- The Arrow–Debreu prices of the stationary economy: `pₜ = qᵗ`. -/
theorem og_seqPrice_const (q : ℝ) (t : ℕ) : seqPrice (fun _ => q) t = q ^ t := by
  simp [seqPrice]

/-- **AKMM, pp. 178–179: Balasko–Shell in the stationary log economy.** With constant positive
endowments, the unique equilibrium (autarky at `q = ω_y/ω_o`, `pₜ = qᵗ`) is Pareto optimal iff
`Σ 1/pₜ = ∞` (the series does not converge), iff `ω_y ≤ ω_o`. -/
theorem og_balasko_shell_stationary_log {ωy ωo : ℝ} (hy : 0 < ωy) (ho : 0 < ωo) :
    (ogParetoOptimal ogLogU (fun _ => ωy) (fun _ => ωo) (fun _ => ωy) (fun _ => ωo) ↔
      ¬ Summable fun t => 1 / seqPrice (fun _ => ωy / ωo) t) ∧
    (¬ Summable (fun t => 1 / seqPrice (fun _ => ωy / ωo) t) ↔ ωy ≤ ωo) := by
  have hsum : (¬ Summable fun t => 1 / seqPrice (fun _ => ωy / ωo) t) ↔ ωy ≤ ωo := by
    have e : (fun t => 1 / seqPrice (fun _ => ωy / ωo) t) = fun t => (ωo / ωy) ^ t := by
      funext t; rw [og_seqPrice_const, one_div, ← inv_pow, inv_div]
    rw [e, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
      abs_of_pos (div_pos ho hy), div_lt_one hy, not_lt]
  refine ⟨?_, hsum⟩
  rw [hsum]
  constructor
  · intro hPO
    by_contra hlt
    push Not at hlt
    exact (og_stationary_improvement ho hlt).2.2 hPO
  · intro hle
    rcases hle.lt_or_eq with hlt | heq
    · refine og_fwt_value og_logU_mono (fun _ => div_pos hy ho) (og_stationary_ad hy ho) ?_
      simp only [og_seqPrice_const]
      have hr : ωy / ωo < 1 := (div_lt_one ho).2 hlt
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hy ho).le hr).mul_const ωy
      simpa using this
    · subst heq
      exact og_equal_endowments_optimal hy

/-- **AKMM, p. 179: the book's sums.** For `qₜ = 3`, `Σ 1/pₜ = Σ 3^{−t} = 3/2`; for `qₜ = 1/3`
and for `qₜ = 1` the series `Σ 1/pₜ` diverges. -/
theorem og_balasko_shell_sums :
    ∑' t, 1 / seqPrice (fun _ => (3 : ℝ)) t = 3 / 2 ∧
      ¬ Summable (fun t => 1 / seqPrice (fun _ => (1 / 3 : ℝ)) t) ∧
      ¬ Summable (fun t => 1 / seqPrice (fun _ => (1 : ℝ)) t) := by
  simp only [og_seqPrice_const]
  refine ⟨?_, ?_, ?_⟩
  · have e : (fun t : ℕ => 1 / (3 : ℝ) ^ t) = fun t => (1 / 3 : ℝ) ^ t := by
      funext t; rw [one_div_pow]
    rw [e, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  · have e : (fun t : ℕ => 1 / (1 / 3 : ℝ) ^ t) = fun t => (3 : ℝ) ^ t := by
      funext t; rw [one_div_pow, one_div_one_div]
    rw [e, summable_geometric_iff_norm_lt_one]
    norm_num
  · simp only [one_pow, div_one]
    exact fun h => by simpa using h.tendsto_atTop_zero

/-- **AKMM, p. 178: the `(3, 1)` economy.** The unique equilibrium price is `q = 3`, the gross
real rate is `1/3` (net `−2/3`, "−67%"), and the allocation `(2, 2)` Pareto dominates autarky
`(3, 1)`: the initial old gain (`2 > 1`), every generation gains
(`log 2 + log 2 > log 3 + log 1`). -/
theorem og_example_3_1 :
    (3 : ℝ) / 1 = 3 ∧ 1 / (3 : ℝ) - 1 = -2 / 3 ∧
      ogDominates ogLogU (fun _ => 3) (fun _ => 1) (fun _ => 2) (fun _ => 2) ∧
      ¬ ogParetoOptimal ogLogU (fun _ => 3) (fun _ => 1) (fun _ => 3) (fun _ => 1) := by
  have h := og_stationary_improvement (ωy := 3) (ωo := 1) one_pos (by norm_num)
  norm_num at h ⊢
  exact h.2

/-- **AKMM, p. 178: the `(1, 3)` economy.** The price is `q = 1/3` (net rate `+2`); the
allocation `(2, 2)` hurts the initial old (`2 < 3`), and autarky is Pareto optimal: the present
value of the endowments is finite and the proof of the First Welfare Theorem goes through. -/
theorem og_example_1_3 :
    (2 : ℝ) < 3 ∧ 1 / (1 / 3 : ℝ) - 1 = 2 ∧
      ogParetoOptimal ogLogU (fun _ => 1) (fun _ => 3) (fun _ => 1) (fun _ => 3) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  refine og_fwt_finite_value og_logU_mono (fun _ => by norm_num) (fun _ => one_pos)
    (fun _ => by norm_num) (og_stationary_ad one_pos (by norm_num)) ?_
  simp only [og_seqPrice_const]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _

/-- **AKMM, p. 179: the `(2, 2)` economy.** The price is `q = 1`, the present value of the
endowments diverges (so the standard proof fails), yet autarky is Pareto optimal. -/
theorem og_example_2_2 :
    ¬ Summable (fun t => seqPrice (fun _ => (2 : ℝ) / 2) t * (2 + 2)) ∧
      ogParetoOptimal ogLogU (fun _ => 2) (fun _ => 2) (fun _ => 2) (fun _ => 2) := by
  refine ⟨?_, og_equal_endowments_optimal two_pos⟩
  simp only [og_seqPrice_const]
  rw [show (2 : ℝ) / 2 = 1 by norm_num]
  simp only [one_pow, one_mul]
  intro h
  have := h.tendsto_atTop_zero
  norm_num at this

/-- **AKMM, p. 179: transfers that stop.** In the `(3, 1)` economy, if the young give one unit
to the old until some date and the transfers then stop, the last generation that gave gets
`(2, 1)`, which is worse than autarky `(3, 1)`. -/
theorem og_finite_transfers_hurt : Real.log 2 + Real.log 1 < Real.log 3 + Real.log 1 := by
  have := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
  linarith

/-- **AKMM, p. 179 (correction): a limit gross rate above one gives optimality.** If every `Uₜ`
is strictly increasing in `c_y`, `qₜ > 0` converges to `q∞ < 1` (gross rate `1/q∞ > 1`), the
young's endowments are bounded and `(cy, co)` is an equilibrium, it is Pareto optimal. -/
theorem og_limit_rate_gt_one {U : ℕ → ℝ → ℝ → ℝ}
    (hU : ∀ t x x' y, 0 < x → x < x' → 0 < y → U t x y < U t x' y) {ωy ωo q cy co : ℕ → ℝ}
    (hq : ∀ t, 0 < q t) {qinf B : ℝ} (hlim : Tendsto q atTop (𝓝 qinf)) (hqinf : qinf < 1)
    (hωy : ∀ t, 0 < ωy t) (hB : ∀ t, ωy t ≤ B) (he : ogADEquilibrium U ωy ωo q cy co) :
    ogParetoOptimal U ωy ωo cy co := by
  refine og_fwt_value hU hq he ?_
  set ρ := (qinf + 1) / 2 with hρ
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (by linarith : qinf < ρ)))
  have hρ0 : 0 < ρ := lt_of_lt_of_le (hq T) (hT T le_rfl).le
  have hbound : ∀ n, seqPrice q (T + n) ≤ seqPrice q T * ρ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, seqPrice_succ, pow_succ, ← mul_assoc]
      exact mul_le_mul ih (hT _ (by omega)).le (hq _).le
        (mul_nonneg (seqPrice_pos hq T).le (pow_nonneg hρ0.le n))
  have hgeo : Tendsto (fun n => seqPrice q T * ρ ^ n * B) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul
      (seqPrice q T)).mul_const B
  have hshift : Tendsto (fun n => seqPrice q (T + n) * ωy (T + n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (mul_pos (seqPrice_pos hq _) (hωy _)).le) (fun n => ?_) hgeo
    exact mul_le_mul (hbound n) (hB _) (hωy _).le
      (mul_nonneg (seqPrice_pos hq T).le (pow_nonneg hρ0.le n))
  rw [← tendsto_add_atTop_iff_nat T]
  simpa [add_comm] using hshift

/-- **AKMM, p. 179 (correction): a limit gross rate below one gives inefficiency** (log
utility). In the log economy with `ω_{y,t} ≥ ω_min > 0`, `ω_{o,t} > 0` and gross rate at autarky
`ω_{o,t+1}/ω_{y,t} → R < 1`, the (unique) autarkic equilibrium is not Pareto optimal: constant
transfers `δ` from the young to the old from some date on improve everyone weakly and one
generation strictly. -/
theorem og_limit_rate_lt_one_log {ωy ωo : ℕ → ℝ} {R ωmin : ℝ} (hmin : 0 < ωmin)
    (hωy : ∀ t, ωmin ≤ ωy t) (hωo : ∀ t, 0 < ωo t)
    (hlim : Tendsto (fun t => ωo (t + 1) / ωy t) atTop (𝓝 R)) (hR : R < 1) :
    ¬ ogParetoOptimal ogLogU ωy ωo ωy ωo := by
  rintro ⟨-, hno⟩
  set R' := (R + 1) / 2 with hR'
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (by linarith : R < R')))
  set δ := (1 - R') * ωmin with hδ
  have hδ0 : 0 < δ := mul_pos (by linarith) hmin
  have hωy0 : ∀ t, 0 < ωy t := fun t => hmin.trans_le (hωy t)
  have hgap : ∀ t, T ≤ t → δ ≤ ωy t - ωo (t + 1) := by
    intro t ht
    have h1 := hT t ht
    rw [div_lt_iff₀ (hωy0 t)] at h1
    have : δ ≤ (1 - R') * ωy t := mul_le_mul_of_nonneg_left (hωy t) (by linarith)
    linarith
  set d : ℕ → ℝ := fun t => if T + 1 ≤ t then δ else 0 with hd
  have hdle : ∀ t, d t ≤ δ := fun t => by simp only [hd]; split_ifs <;> linarith
  have hd0 : ∀ t, 0 ≤ d t := fun t => by simp only [hd]; split_ifs <;> linarith
  have hδy : ∀ t, T + 1 ≤ t → δ < ωy t := by
    intro t ht
    have := hgap t (by omega)
    linarith [hωo (t + 1)]
  refine hno ⟨fun t => ωy t - d t, fun t => ωo t + d t, ⟨fun t => ⟨?_, ?_⟩, fun t => by linarith⟩,
    ?_, fun t => ?_, Or.inr ⟨T, ?_⟩⟩
  · by_cases ht : T + 1 ≤ t
    · simp only [hd, ht, ↓reduceIte]; linarith [hδy t ht]
    · simp only [hd, ht, ↓reduceIte]; linarith [hωy0 t]
  · linarith [hωo t, hd0 t]
  · simp only [hd, show ¬ T + 1 ≤ 0 by omega, ↓reduceIte, add_zero, le_refl]
  · -- generation `t`
    simp only [ogLogU]
    have hy := hωy0 t
    have ho := hωo (t + 1)
    by_cases ht : T + 1 ≤ t
    · have ht1 : T + 1 ≤ t + 1 := by omega
      simp only [hd, ht, ht1, ↓reduceIte]
      have hpos : 0 < ωy t - δ := by linarith [hδy t ht]
      rw [← Real.log_mul hy.ne' ho.ne', ← Real.log_mul hpos.ne' (by linarith : ωo (t + 1) + δ ≠ 0)]
      refine Real.log_le_log (mul_pos hy ho) ?_
      have := hgap t (by omega)
      nlinarith
    · simp only [hd, ht, ↓reduceIte, sub_zero]
      by_cases ht1 : T + 1 ≤ t + 1
      · simp only [ht1, ↓reduceIte]
        linarith [Real.log_le_log ho (by linarith : ωo (t + 1) ≤ ωo (t + 1) + δ)]
      · simp only [ht1, ↓reduceIte, add_zero, le_refl]
  · -- generation `T` receives `δ` when old and gives nothing
    simp only [ogLogU, hd, show ¬ T + 1 ≤ T by omega, show T + 1 ≤ T + 1 from le_rfl,
      ↓reduceIte, sub_zero]
    linarith [Real.log_lt_log (hωo (T + 1)) (by linarith : ωo (T + 1) < ωo (T + 1) + δ)]

/-- The counterexample economy of the correction: `ω_{y,t} = 1`,
`ω_{o,t} = ((t + 1)/(t + 2))²`. -/
noncomputable def ogCexOld (t : ℕ) : ℝ := (((t : ℝ) + 1) / ((t : ℝ) + 2)) ^ 2

/-- **AKMM, p. 179: the printed criterion fails at a zero limit net rate.** In the log economy
with `ω_{y,t} = 1` and `ω_{o,t} = ((t + 1)/(t + 2))²`, autarky with
`qₜ = ω_{y,t}/ω_{o,t+1}` is the equilibrium; the gross real rate
`1/qₜ = ((t + 2)/(t + 3))²` converges to `1` (limit net rate `0`, "equal to or above 0"), yet the
equilibrium is Pareto dominated: transfers `δₜ = 1/(2(t + 2))` from the young to the old make the
initial old strictly and every generation weakly better off. -/
theorem og_limit_rate_one_counterexample :
    IsOGEndowEquilibrium 0 Real.log 1 (fun _ => 1) ogCexOld (fun _ => 1) ogCexOld (fun _ => 0)
        (fun t => 1 / ogCexOld (t + 1)) ∧
      Tendsto (fun t => 1 / (1 / ogCexOld (t + 1))) atTop (𝓝 1) ∧
      ¬ ogParetoOptimal ogLogU (fun _ => 1) ogCexOld (fun _ => 1) ogCexOld := by
  have hpos : ∀ t, 0 < ogCexOld t := fun t => by unfold ogCexOld; positivity
  refine ⟨(og_log_equilibrium_iff (fun _ => one_pos) hpos
      (fun t => one_div_pos.2 (hpos (t + 1)))).2 ⟨fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩,
    ?_, ?_⟩
  · simp only [one_div_one_div, ogCexOld]
    have h : Tendsto (fun t : ℕ => ((t : ℝ) + 1 + 1) / ((t : ℝ) + 1 + 2)) atTop (𝓝 1) := by
      have e : (fun t : ℕ => ((t : ℝ) + 1 + 1) / ((t : ℝ) + 1 + 2)) =
          fun t : ℕ => 1 - 1 / ((t : ℝ) + 3) := by
        funext t
        have : (t : ℝ) + 3 ≠ 0 := by positivity
        field_simp
        ring
      rw [e]
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2)
      have h3 : Tendsto (fun t : ℕ => 1 / ((t : ℝ) + 3)) atTop (𝓝 0) := by
        refine this.congr fun t => ?_
        simp only [Function.comp_apply]
        push_cast
        ring_nf
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h3
    simpa using h.pow 2
  · rintro ⟨-, hno⟩
    set d : ℕ → ℝ := fun t => 1 / (2 * ((t : ℝ) + 2)) with hd
    have hd0 : ∀ t, 0 < d t := fun t => by simp only [hd]; positivity
    have hd1 : ∀ t, d t < 1 := fun t => by
      simp only [hd]; rw [div_lt_one (by positivity)]; linarith [(t.cast_nonneg : (0 : ℝ) ≤ t)]
    refine hno ⟨fun t => 1 - d t, fun t => ogCexOld t + d t,
      ⟨fun t => ⟨by linarith [hd1 t], by linarith [hpos t, hd0 t]⟩, fun t => by linarith⟩,
      by linarith [hd0 0], fun t => ?_, Or.inl (by linarith [hd0 0])⟩
    simp only [ogLogU, Real.log_one, zero_add]
    have h1 : 0 < 1 - d t := by linarith [hd1 t]
    rw [← Real.log_mul h1.ne' (by linarith [hpos (t + 1), hd0 (t + 1)])]
    refine Real.log_le_log (hpos (t + 1)) ?_
    simp only [hd, ogCexOld]
    have ht : (0 : ℝ) ≤ t := t.cast_nonneg
    push_cast
    have key : (1 - 1 / (2 * ((t : ℝ) + 2))) * ((((t : ℝ) + 1 + 1) / ((t : ℝ) + 1 + 2)) ^ 2 +
        1 / (2 * ((t : ℝ) + 1 + 2))) - (((t : ℝ) + 1 + 1) / ((t : ℝ) + 1 + 2)) ^ 2 =
        ((t : ℝ) + 1) / (4 * ((t : ℝ) + 2) * ((t : ℝ) + 3) ^ 2) := by
      field_simp; ring
    have : 0 ≤ ((t : ℝ) + 1) / (4 * ((t : ℝ) + 2) * ((t : ℝ) + 3) ^ 2) := by positivity
    linarith

end AKMM.Welfare
