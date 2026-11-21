/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCompetitiveEquilibrium.GrowthAD
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Sequential equilibrium

AKMM, §5.3, pp. 143–146. Consumers trade one asset period by period: `c_{i,t} + qₜa_{i,t+1} =
a_{i,t} + y_{i,t}`, subject to the no-Ponzi-game condition
`lim (∏_{s ≤ t} q_s) a_{i,t+1} ≥ 0`.

* Definition 5 (`SeqBudget`, `SeqOptimal`, `IsSeqEquilibrium`). The nPg condition is stated as
  `liminf ≥ 0` (for every `ε > 0`, eventually `≥ −ε`), since the book's limit need not exist.
* Walras's law (p. 144 and fn. 10): with `∫ a_{i,0} di = 0`, goods clearing at every date is
  equivalent to asset clearing at every date (`seq_walras`).
* (5.21)–(5.22): `qₜu′(cₜ) = βu′(c_{t+1})` is necessary (`eq_5_21_5_22`), so
  `∏_{s<t} q_s = βᵗu′(cₜ)/u′(c₀)`, the Arrow–Debreu price (5.3) (`seq_price_product`), and
  `p_{t−1}/pₜ = 1/q_{t−1}` (`seq_gross_rate`).
* The budgets (p. 145): after `T` substitutions
  `Σ_{t≤T} pₜcₜ + p_{T+1}a_{T+1} = a₀ + Σ_{t≤T} pₜyₜ` (`seq_budget_iterate`); the book prints the
  factor of `a_{T+1}` as `∏_{s=0}^{T−1} q_s`, which is wrong
  (`seq_budget_iterate_printed_counterexample`). With nPg the lifetime budget
  `Σ pₜcₜ ≤ a₀ + Σ pₜyₜ` follows (`seq_lifetime_budget`), with equality iff
  `p_{T+1}a_{T+1} → 0` (`seq_lifetime_budget_eq_iff`); conversely every plan meeting the
  lifetime budget with equality is financed by a sequence of asset holdings satisfying nPg
  (`seq_of_lifetime_budget`).
* Equivalence (p. 145): with strictly increasing `u`, a plan solves the sequential problem iff it
  solves the date-0 problem at `pₜ = ∏_{s<t} q_s` with wealth `a₀ + Σ pₜyₜ`
  (`seq_optimal_iff_ad`); hence a sequential equilibrium with `a_{i,0} = 0` is an Arrow–Debreu
  equilibrium (`seq_equilibrium_is_ad`). An instance of Definition 5
  (`seq_equilibrium_instance`).
* Definition 6 and Walras's law in the growth economy (p. 146): for a constant-returns
  technology Euler's theorem `F(K, L) = F_K K + F_L L` holds (`euler_crs`), so the consumers'
  budgets and the firm's conditions imply the resource constraint (`seq_growth_walras`).

Departures: consumption positive; the utility series of the plans compared converge.
-/

namespace AKMM.CompetitiveEquilibrium

open MeasureTheory Filter Topology

variable {I : Type*} [MeasurableSpace I]

/-- The Arrow–Debreu price implied by sequential prices: `pₜ = ∏_{s<t} q_s`. -/
noncomputable def seqPrice (q : ℕ → ℝ) (t : ℕ) : ℝ := ∏ s ∈ Finset.range t, q s

/-- `p_{t+1} = pₜqₜ`. -/
theorem seqPrice_succ (q : ℕ → ℝ) (t : ℕ) : seqPrice q (t + 1) = seqPrice q t * q t := by
  simp [seqPrice, Finset.prod_range_succ]

/-- Positive one-period prices give positive Arrow–Debreu prices. -/
theorem seqPrice_pos {q : ℕ → ℝ} (hq : ∀ t, 0 < q t) (t : ℕ) : 0 < seqPrice q t :=
  Finset.prod_pos fun s _ => hq s

/-- The no-Ponzi-game condition of Definition 5 (AKMM, p. 144), as `liminf ≥ 0`:
for every `ε > 0`, eventually `(∏_{s≤t} q_s)a_{t+1} ≥ −ε`. -/
def NoPonzi (q a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ t in atTop, -ε ≤ seqPrice q (t + 1) * a (t + 1)

/-- AKMM, Definition 5, p. 144: the sequential budget set: positive consumption, `a₀` given,
`cₜ + qₜa_{t+1} = aₜ + yₜ` for all `t`, and nPg. -/
def SeqBudget (q y : ℕ → ℝ) (a0 : ℝ) (c a : ℕ → ℝ) : Prop :=
  (∀ t, 0 < c t) ∧ a 0 = a0 ∧ (∀ t, c t + q t * a (t + 1) = a t + y t) ∧ NoPonzi q a

/-- AKMM, Definition 5, part 1, p. 144: `(c, a)` solves the sequential problem, among plans
with a convergent utility series. -/
def SeqOptimal (u : ℝ → ℝ) (β : ℝ) (q y : ℕ → ℝ) (a0 : ℝ) (c a : ℕ → ℝ) : Prop :=
  SeqBudget q y a0 c a ∧ Summable (fun t => β ^ t * u (c t)) ∧
    ∀ x b, SeqBudget q y a0 x b → Summable (fun t => β ^ t * u (x t)) →
      ∑' t, β ^ t * u (x t) ≤ ∑' t, β ^ t * u (c t)

/-- **AKMM, Definition 5, p. 143.** A sequential competitive equilibrium: each consumer solves
the sequential problem from `a_{i,0}`, and goods and assets clear at every date. -/
def IsSeqEquilibrium (μ : Measure I) (u : ℝ → ℝ) (β : ℝ) (y : I → ℕ → ℝ) (a0 : I → ℝ)
    (c a : I → ℕ → ℝ) (q : ℕ → ℝ) : Prop :=
  (∀ i, SeqOptimal u β q (y i) (a0 i) (c i) (a i)) ∧ (∀ t, ∫ i, c i t ∂μ = ∫ i, y i t ∂μ) ∧
    ∀ t, ∫ i, a i (t + 1) ∂μ = 0

/-- **AKMM, p. 144 and fn. 10: Walras's law.** Suppose every consumer's period budgets hold,
consumption, endowments and assets are integrable at every date, `∫ a_{i,0} di = 0` and
`qₜ ≠ 0`. Then goods clear at every date iff assets clear at every date. -/
theorem seq_walras {μ : Measure I} {q : ℕ → ℝ} {y c a : I → ℕ → ℝ}
    (hb : ∀ i t, c i t + q t * a i (t + 1) = a i t + y i t)
    (hc : ∀ t, Integrable (c · t) μ) (hy : ∀ t, Integrable (y · t) μ)
    (ha : ∀ t, Integrable (a · t) μ) (ha0 : ∫ i, a i 0 ∂μ = 0) (hq : ∀ t, q t ≠ 0) :
    (∀ t, ∫ i, c i t ∂μ = ∫ i, y i t ∂μ) ↔ ∀ t, ∫ i, a i (t + 1) ∂μ = 0 := by
  have hagg : ∀ t, ∫ i, c i t ∂μ + q t * ∫ i, a i (t + 1) ∂μ =
      ∫ i, a i t ∂μ + ∫ i, y i t ∂μ := by
    intro t
    rw [← integral_const_mul, ← integral_add (hc t) ((ha (t + 1)).const_mul _),
      ← integral_add (ha t) (hy t)]
    exact congrArg (fun f => ∫ i, f i ∂μ) (funext fun i => hb i t)
  constructor
  · intro hg t
    induction t with
    | zero =>
      have h := hagg 0
      rw [ha0, hg 0] at h
      have : q 0 * ∫ i, a i (0 + 1) ∂μ = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (hq 0)
    | succ t ih =>
      have h := hagg (t + 1)
      rw [ih, hg (t + 1)] at h
      have : q (t + 1) * ∫ i, a i (t + 1 + 1) ∂μ = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (hq (t + 1))
  · intro hA t
    have h := hagg t
    rw [hA t] at h
    rcases t with _ | t
    · rw [ha0] at h; linarith
    · rw [hA t] at h; linarith

/-- **AKMM, (5.21)–(5.22), p. 144.** At a sequential optimum with `β > 0`, positive prices and
derivatives `u′(cₜ)`, `qₜu′(cₜ) = βu′(c_{t+1})`. Proved by saving `ε` more at `t` and consuming
it at `t + 1`. -/
theorem eq_5_21_5_22 {u : ℝ → ℝ} {β a0 : ℝ} {q y c a du : ℕ → ℝ}
    (hopt : SeqOptimal u β q y a0 c a) (hβ : 0 < β) (hd : ∀ t, HasDerivAt u (du t) (c t))
    (t : ℕ) : q t * du t = β * du (t + 1) := by
  obtain ⟨⟨hpos, ha0, hb, hnpg⟩, husum, hmax⟩ := hopt
  have htt : t + 1 ≠ t := by omega
  let x : ℝ → ℕ → ℝ := fun ε n =>
    if n = t then c t - q t * ε else if n = t + 1 then c (t + 1) + ε else c n
  let b : ℝ → ℕ → ℝ := fun ε n => if n = t + 1 then a (t + 1) + ε else a n
  have hxt : ∀ ε, x ε t = c t - q t * ε := fun ε => by simp [x]
  have hxt1 : ∀ ε, x ε (t + 1) = c (t + 1) + ε := fun ε => by simp [x]
  have hxo : ∀ ε, ∀ n ∉ ({t, t + 1} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [x, hn.1, hn.2]
  have hbo : ∀ ε n, n ≠ t + 1 → b ε n = a n := fun ε n hn => by simp [b, hn]
  have hbt1 : ∀ ε, b ε (t + 1) = a (t + 1) + ε := fun ε => by simp [b]
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - q t * ε ∧ 0 < c (t + 1) + ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - q t * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos t)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c (t + 1) + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hpos (t + 1))
    exact h1.and h2
  have hd' : HasDerivAt (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), β ^ n * u (x ε n))
      (β ^ t * (du t * (-q t)) + β ^ (t + 1) * du (t + 1)) 0 := by
    have e : (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), β ^ n * u (x ε n)) =
        fun ε => β ^ t * u (c t - q t * ε) + β ^ (t + 1) * u (c (t + 1) + ε) := by
      funext ε; rw [Finset.sum_pair htt.symm, hxt, hxt1]
    rw [e]
    have h1 : HasDerivAt (fun ε => u (c t - q t * ε)) (du t * (-q t)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t - q t * ε) (-q t) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (q t)).const_sub (c t)
      have hu : HasDerivAt u (du t) (c t - q t * 0) := by simpa using hd t
      exact hu.comp 0 hin
    have h2 : HasDerivAt (fun ε => u (c (t + 1) + ε)) (du (t + 1)) 0 := by
      have hu : HasDerivAt u (du (t + 1)) (c (t + 1) + 0) := by simpa using hd (t + 1)
      simpa using hu.comp_const_add (c (t + 1)) 0
    exact (h1.const_mul _).add (h2.const_mul _)
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * u (c n))
    (g := fun ε n => β ^ n * u (x ε n)) {t, t + 1} husum
    (fun ε n hn => by simp only [hxo ε n hn]) (fun n => by simp [x]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      refine hmax (x ε) (b ε) ⟨fun n => ?_, by rw [hbo ε 0 (by omega), ha0], fun n => ?_,
        fun η hη => ?_⟩ hU
      · by_cases h1 : n = t
        · subst h1; rw [hxt]; exact hε.1
        by_cases h2 : n = t + 1
        · subst h2; rw [hxt1]; exact hε.2
        rw [hxo ε n (by simp [h1, h2])]; exact hpos n
      · by_cases h1 : n = t
        · rw [h1, hxt, hbt1, hbo ε t (by omega)]
          have := hb t; linarith
        by_cases h2 : n = t + 1
        · rw [h2, hxt1, hbt1, hbo ε (t + 1 + 1) (by omega)]
          have := hb (t + 1); linarith
        rw [hxo ε n (by simp [h1, h2]), hbo ε (n + 1) (by omega), hbo ε n h2]
        exact hb n
      · filter_upwards [hnpg η hη, eventually_gt_atTop t] with s hs hst
        rw [hbo ε (s + 1) (by omega)]
        exact hs) hd'
  have hb' := (pow_pos hβ t).ne'
  rw [pow_succ] at hzero
  have : β ^ t * (β * du (t + 1) - q t * du t) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hb'
  · linarith

/-- **AKMM, p. 145: sequential prices compound to Arrow–Debreu prices.** If
`qₜu′(cₜ) = βu′(c_{t+1})` at every date and `u′(cₜ) ≠ 0`, then
`∏_{s<t} q_s = βᵗu′(cₜ)/u′(c₀)`, the price (5.3). -/
theorem seq_price_product {β : ℝ} {q du : ℕ → ℝ} (heul : ∀ t, q t * du t = β * du (t + 1))
    (hdu : ∀ t, du t ≠ 0) (t : ℕ) : seqPrice q t = β ^ t * du t / du 0 := by
  induction t with
  | zero => simp [seqPrice, hdu 0]
  | succ t ih =>
    rw [seqPrice_succ, ih]
    have h := heul t
    have := hdu t
    have := hdu 0
    field_simp
    rw [pow_succ]
    linear_combination β ^ t * h

/-- **AKMM, p. 145: the gross interest rate.** `pₜ/p_{t+1} = 1/qₜ`. -/
theorem seq_gross_rate {q : ℕ → ℝ} (hq : ∀ t, 0 < q t) (t : ℕ) :
    seqPrice q t / seqPrice q (t + 1) = 1 / q t := by
  rw [seqPrice_succ]
  have := (seqPrice_pos hq t).ne'
  have := (hq t).ne'
  field_simp

/-- **AKMM, p. 145: the iterated budget.** If `cₜ + qₜa_{t+1} = aₜ + yₜ` at every date then for
every `T`, `Σ_{t≤T} pₜcₜ + p_{T+1}a_{T+1} = a₀ + Σ_{t≤T} pₜyₜ`, with `pₜ = ∏_{s<t} q_s`; the
factor of `a_{T+1}` is `∏_{s≤T} q_s`. -/
theorem seq_budget_iterate {q y c a : ℕ → ℝ} (hb : ∀ t, c t + q t * a (t + 1) = a t + y t)
    (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), seqPrice q t * c t + seqPrice q (T + 1) * a (T + 1) =
      a 0 + ∑ t ∈ Finset.range (T + 1), seqPrice q t * y t := by
  induction T with
  | zero => simp [seqPrice, hb 0]
  | succ T ih =>
    rw [Finset.sum_range_succ (fun t => seqPrice q t * c t) (T + 1),
      Finset.sum_range_succ (fun t => seqPrice q t * y t) (T + 1), seqPrice_succ q (T + 1)]
    have h := hb (T + 1)
    linear_combination ih + seqPrice q (T + 1) * h

/-- **AKMM, p. 145: the printed iterated budget is wrong.** The book's display multiplies
`a_{T+1}` by `∏_{s=0}^{T−1} q_s`. At `T = 0` it reads `c₀ + a₁ = a₀ + y₀`, which fails for the
budget-feasible `q₀ = 1/2`, `a₀ = 0`, `y₀ = 2`, `c₀ = 1`, `a₁ = 2`. -/
theorem seq_budget_iterate_printed_counterexample :
    let q : ℕ → ℝ := fun _ => 1 / 2
    let y : ℕ → ℝ := fun _ => 2
    let c : ℕ → ℝ := fun _ => 1
    let a : ℕ → ℝ := fun t => if t = 0 then 0 else 2
    c 0 + q 0 * a 1 = a 0 + y 0 ∧
      ∑ t ∈ Finset.range (0 + 1), seqPrice q t * c t + seqPrice q 0 * a (0 + 1) ≠
        a 0 + ∑ t ∈ Finset.range (0 + 1), seqPrice q t * y t := by
  intro q y c a
  refine ⟨by norm_num [q, y, c, a], ?_⟩
  norm_num [q, y, c, a, seqPrice]

/-- **AKMM, p. 145: the lifetime budget.** If the sequential budget (with nPg) holds, prices
`qₜ` are positive and `Σ pₜyₜ` converges, then `Σ pₜcₜ` converges and
`Σ pₜcₜ ≤ a₀ + Σ pₜyₜ`. -/
theorem seq_lifetime_budget {q y c a : ℕ → ℝ} {a0 : ℝ} (hb : SeqBudget q y a0 c a)
    (hq : ∀ t, 0 < q t) (hy : Summable (fun t => seqPrice q t * y t)) :
    Summable (fun t => seqPrice q t * c t) ∧
      ∑' t, seqPrice q t * c t ≤ a0 + ∑' t, seqPrice q t * y t := by
  obtain ⟨hpos, ha0, hbud, hnpg⟩ := hb
  have hit := seq_budget_iterate hbud
  have hnn : ∀ t, 0 ≤ seqPrice q t * c t := fun t =>
    (mul_pos (seqPrice_pos hq t) (hpos t)).le
  -- the partial sums of `pₜyₜ` converge, so the partial sums of `pₜcₜ` are bounded
  have hyT := (hy.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hbound : ∀ ε > 0, ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1), seqPrice q t * c t ≤
      a0 + ∑' t, seqPrice q t * y t + 2 * ε := by
    intro ε hε
    have h1 := hyT.eventually (Metric.ball_mem_nhds _ hε)
    filter_upwards [h1, hnpg ε hε] with T hT hP
    have h2 := hit T
    rw [ha0] at h2
    simp only [Function.comp_apply, Real.dist_eq] at hT
    have := (abs_lt.1 hT).2
    linarith
  -- a uniform bound on all partial sums
  obtain ⟨T0, hT0⟩ := (hbound 1 one_pos).exists_forall_of_atTop
  have hsum : Summable (fun t => seqPrice q t * c t) := by
    refine summable_of_sum_range_le hnn (c := a0 + ∑' t, seqPrice q t * y t + 2 * 1) ?_
    intro n
    calc ∑ t ∈ Finset.range n, seqPrice q t * c t
        ≤ ∑ t ∈ Finset.range (max n T0 + 1), seqPrice q t * c t :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (by omega)) (fun t _ _ => hnn t)
      _ ≤ _ := hT0 _ (le_max_right _ _)
  refine ⟨hsum, ?_⟩
  have hcT := (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hle : ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1), seqPrice q t * c t ≤
      a0 + ∑' t, seqPrice q t * y t + 2 * (ε / 2) := hbound (ε / 2) (by linarith)
  have := le_of_tendsto hcT hle
  linarith

/-- **AKMM, p. 145: equality in the lifetime budget.** Under the hypotheses of
`seq_lifetime_budget`, `Σ pₜcₜ = a₀ + Σ pₜyₜ` iff `p_{T+1}a_{T+1} → 0`. -/
theorem seq_lifetime_budget_eq_iff {q y c a : ℕ → ℝ} {a0 : ℝ} (hb : SeqBudget q y a0 c a)
    (hq : ∀ t, 0 < q t) (hy : Summable (fun t => seqPrice q t * y t)) :
    ∑' t, seqPrice q t * c t = a0 + ∑' t, seqPrice q t * y t ↔
      Tendsto (fun T => seqPrice q (T + 1) * a (T + 1)) atTop (𝓝 0) := by
  have hc := (seq_lifetime_budget hb hq hy).1
  obtain ⟨_, ha0, hbud, _⟩ := hb
  have hlim : Tendsto (fun T => seqPrice q (T + 1) * a (T + 1)) atTop
      (𝓝 (a0 + ∑' t, seqPrice q t * y t - ∑' t, seqPrice q t * c t)) := by
    have hyT := (hy.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have hcT := (hc.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have e : (fun T => seqPrice q (T + 1) * a (T + 1)) = fun T =>
        a0 + (∑ t ∈ Finset.range (T + 1), seqPrice q t * y t) -
          ∑ t ∈ Finset.range (T + 1), seqPrice q t * c t := by
      funext T; have := seq_budget_iterate hbud T; rw [ha0] at this; linarith
    rw [e]
    exact (hyT.const_add a0).sub hcT
  constructor
  · intro h; rw [h, sub_self] at hlim; exact hlim
  · intro h
    have := tendsto_nhds_unique hlim h
    linarith

/-- The asset holdings that finance a consumption plan: `a₀` given and
`a_{t+1} = (aₜ + yₜ − cₜ)/qₜ`. -/
noncomputable def seqAssets (q y c : ℕ → ℝ) (a0 : ℝ) : ℕ → ℝ
  | 0 => a0
  | t + 1 => (seqAssets q y c a0 t + y t - c t) / q t

/-- **AKMM, p. 145: the converse.** If prices are positive, `Σ pₜyₜ` and `Σ pₜcₜ` converge,
`c > 0` and `Σ pₜcₜ = a₀ + Σ pₜyₜ`, then the assets `seqAssets` satisfy the period budgets and
`p_{T+1}a_{T+1} → 0`, so nPg: `c` is sequentially feasible. -/
theorem seq_of_lifetime_budget {q y c : ℕ → ℝ} {a0 : ℝ} (hq : ∀ t, 0 < q t) (hc0 : ∀ t, 0 < c t)
    (hy : Summable (fun t => seqPrice q t * y t)) (hc : Summable (fun t => seqPrice q t * c t))
    (hbud : ∑' t, seqPrice q t * c t = a0 + ∑' t, seqPrice q t * y t) :
    SeqBudget q y a0 c (seqAssets q y c a0) ∧
      Tendsto (fun T => seqPrice q (T + 1) * seqAssets q y c a0 (T + 1)) atTop (𝓝 0) := by
  have hb : ∀ t, c t + q t * seqAssets q y c a0 (t + 1) = seqAssets q y c a0 t + y t := by
    intro t
    simp only [seqAssets]
    have := (hq t).ne'
    field_simp
    ring
  have hlim : Tendsto (fun T => seqPrice q (T + 1) * seqAssets q y c a0 (T + 1)) atTop (𝓝 0) := by
    have hyT := (hy.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have hcT := (hc.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have e : (fun T => seqPrice q (T + 1) * seqAssets q y c a0 (T + 1)) = fun T =>
        a0 + (∑ t ∈ Finset.range (T + 1), seqPrice q t * y t) -
          ∑ t ∈ Finset.range (T + 1), seqPrice q t * c t := by
      funext T
      have := seq_budget_iterate hb T
      simp only [seqAssets] at this ⊢
      linarith
    rw [e]
    have := (hyT.const_add a0).sub hcT
    rwa [← hbud, sub_self] at this
  refine ⟨⟨hc0, rfl, hb, fun ε hε => ?_⟩, hlim⟩
  filter_upwards [hlim.eventually (lt_mem_nhds (by linarith : -ε < 0))] with T hT
  exact hT.le

/-- **AKMM, p. 145: the sequential and date-0 problems are equivalent.** Let `u` be strictly
increasing on `(0, ∞)`, prices `qₜ > 0`, `Σ pₜyₜ` convergent with `pₜ = ∏_{s<t} q_s`. Then a
consumption plan `c` solves the sequential problem (with some asset holdings) iff it solves the
date-0 problem with wealth `a₀ + Σ pₜyₜ`. -/
theorem seq_optimal_iff_ad {u : ℝ → ℝ} {β a0 : ℝ} {q y c : ℕ → ℝ}
    (hu : StrictMonoOn u (Set.Ioi 0)) (hq : ∀ t, 0 < q t)
    (hy : Summable (fun t => seqPrice q t * y t)) :
    (∃ a, SeqOptimal u β q y a0 c a) ↔
      ADOptimal u β (seqPrice q) (a0 + ∑' t, seqPrice q t * y t) c := by
  set W := a0 + ∑' t, seqPrice q t * y t with hW
  have hp := seqPrice_pos hq
  -- raising consumption at date 0 to exhaust a budget slack raises utility
  have hraise : ∀ x : ℕ → ℝ, (∀ t, 0 < x t) → Summable (fun t => seqPrice q t * x t) →
      Summable (fun t => β ^ t * u (x t)) → ∑' t, seqPrice q t * x t ≤ W →
      ∃ x' : ℕ → ℝ, ADBudget (seqPrice q) W x' ∧ Summable (fun t => β ^ t * u (x' t)) ∧
        ∑' t, β ^ t * u (x t) ≤ ∑' t, β ^ t * u (x' t) ∧
        (∑' t, seqPrice q t * x t < W → ∑' t, β ^ t * u (x t) < ∑' t, β ^ t * u (x' t)) := by
    intro x hx hxs hxu hle
    set sl := W - ∑' t, seqPrice q t * x t with hsl
    have hsl0 : 0 ≤ sl := by linarith
    let x' : ℕ → ℝ := fun n => if n = 0 then x 0 + sl else x n
    have hxo : ∀ n ∉ ({0} : Finset ℕ), x' n = x n := fun n hn => by
      simp only [Finset.mem_singleton] at hn; simp [x', hn]
    have hB := ce_tsum_perturb (f := fun n => seqPrice q n * x n)
      (g := fun n => seqPrice q n * x' n) {0} (fun n hn => by simp only [hxo n hn]) hxs
    have hU := ce_tsum_perturb (f := fun n => β ^ n * u (x n))
      (g := fun n => β ^ n * u (x' n)) {0} (fun n hn => by simp only [hxo n hn]) hxu
    have hx'0 : x' 0 = x 0 + sl := by simp [x']
    refine ⟨x', ⟨fun n => ?_, hB.1, ?_⟩, hU.1, ?_, fun hlt => ?_⟩
    · by_cases h : n = 0
      · subst h; rw [hx'0]; linarith [hx 0]
      · rw [hxo n (by simp [h])]; exact hx n
    · rw [hB.2, Finset.sum_singleton, hx'0]; simp [seqPrice, hsl]
    · rw [hU.2, Finset.sum_singleton, hx'0]
      have := hu.monotoneOn (hx 0) (show (0 : ℝ) < x 0 + sl by linarith [hx 0])
        (by linarith : x 0 ≤ x 0 + sl)
      simp only [pow_zero, one_mul]
      linarith
    · rw [hU.2, Finset.sum_singleton, hx'0]
      have hpos : 0 < sl := by linarith
      have := hu (hx 0) (show (0 : ℝ) < x 0 + sl by linarith [hx 0])
        (by linarith : x 0 < x 0 + sl)
      simp only [pow_zero, one_mul]
      linarith
  constructor
  · rintro ⟨a, hb, hU, hmax⟩
    obtain ⟨hcs, hcle⟩ := seq_lifetime_budget hb hq hy
    -- the budget binds
    have hbind : ∑' t, seqPrice q t * c t = W := by
      by_contra hne
      have hlt : ∑' t, seqPrice q t * c t < W := lt_of_le_of_ne hcle hne
      obtain ⟨x', hx'b, hx'u, -, hstrict⟩ := hraise c hb.1 hcs hU hcle
      obtain ⟨hsb, -⟩ := seq_of_lifetime_budget hq hx'b.1 hy hx'b.2.1 hx'b.2.2
      have := hmax x' _ hsb hx'u
      linarith [hstrict hlt]
    refine ⟨⟨hb.1, hcs, hbind⟩, hU, fun x hx hxu => ?_⟩
    exact hmax x _ (seq_of_lifetime_budget hq hx.1 hy hx.2.1 hx.2.2).1 hxu
  · rintro ⟨hb, hU, hmax⟩
    refine ⟨seqAssets q y c a0, (seq_of_lifetime_budget hq hb.1 hy hb.2.1 hb.2.2).1, hU,
      fun x b hxb hxu => ?_⟩
    obtain ⟨hxs, hxle⟩ := seq_lifetime_budget hxb hq hy
    obtain ⟨x', hx'b, hx'u, hle, -⟩ := hraise x hxb.1 hxs hxu hxle
    exact hle.trans (hmax x' hx'b hx'u)

/-- **AKMM, p. 145: a sequential equilibrium is an Arrow–Debreu equilibrium.** With `u`
strictly increasing on `(0, ∞)`, positive `qₜ`, no initial assets (`a_{i,0} = 0`) and
convergent `Σ pₜy_{i,t}`, the consumption of a sequential equilibrium is an Arrow–Debreu
equilibrium (Definition 1) at `pₜ = ∏_{s<t} q_s`. -/
theorem seq_equilibrium_is_ad {μ : Measure I} {u : ℝ → ℝ} {β : ℝ} {y c a : I → ℕ → ℝ}
    {q : ℕ → ℝ} (hu : StrictMonoOn u (Set.Ioi 0)) (hq : ∀ t, 0 < q t)
    (hy : ∀ i, Summable (fun t => seqPrice q t * y i t))
    (he : IsSeqEquilibrium μ u β y (fun _ => 0) c a q) :
    IsADEquilibrium μ u β y c (seqPrice q) := by
  refine ⟨hy, fun i => ?_, he.2.1⟩
  have := (seq_optimal_iff_ad (c := c i) (a0 := 0) hu hq (hy i)).1 ⟨a i, he.1 i⟩
  rwa [zero_add] at this

/-- **AKMM, Definition 5: an instance.** With log utility, `0 < β < 1`, unit endowments and no
initial assets, `qₜ = β`, `c_{i,t} = 1` and `a_{i,t} = 0` form a sequential equilibrium. -/
theorem seq_equilibrium_instance {μ : Measure I} [IsProbabilityMeasure μ] {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    IsSeqEquilibrium μ Real.log β (fun _ _ => 1) (fun _ => 0) (fun _ _ => 1) (fun _ _ => 0)
      (fun _ => β) := by
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  have hp : ∀ t, seqPrice (fun _ => β) t = β ^ t := fun t => by simp [seqPrice]
  have hy : Summable (fun t => seqPrice (fun _ => β) t * 1) := by simpa [hp] using hgeo
  have had : ADOptimal Real.log β (seqPrice fun _ => β)
      (0 + ∑' t, seqPrice (fun _ => β) t * 1) (fun _ => 1) := by
    refine ad_foc_sufficient (du := fun _ => 1) (lam := 1) hβ0.le
      (fun t x hx => by simpa using ce_log_tangent one_pos hx) (fun t => by simp [hp])
      ⟨fun _ => one_pos, hy, by simp⟩ (by simp)
  obtain ⟨a, _, hU, hmax⟩ := (seq_optimal_iff_ad (c := fun _ => 1)
    Real.strictMonoOn_log (fun _ => hβ0) hy).2 had
  refine ⟨fun _ => ⟨⟨fun _ => one_pos, rfl, fun t => by simp, fun ε hε => ?_⟩, hU, hmax⟩,
    fun _ => rfl, fun _ => by simp⟩
  exact Filter.Eventually.of_forall fun _ => by simp; linarith

/-- **AKMM, p. 146: Euler's theorem for constant returns.** If `F : ℝ × ℝ → ℝ` is homogeneous of
degree one, `F(λx) = λF(x)` for `λ > 0`, and differentiable at `x`, then `F′(x)x = F(x)`; with
`F_K = F′(1, 0)`, `F_L = F′(0, 1)`, `F(K, L) = F_K K + F_L L`. -/
theorem euler_crs {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {x : ℝ × ℝ}
    (hhom : ∀ l : ℝ, 0 < l → F (l • x) = l * F x) (hd : HasFDerivAt F F' x) :
    F x = F' (1, 0) * x.1 + F' (0, 1) * x.2 := by
  have hpath : HasDerivAt (fun l : ℝ => l • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hd1 : HasDerivAt (fun l : ℝ => F (l • x)) (F' x) 1 := by
    have hd' : HasFDerivAt F F' ((1 : ℝ) • x) := by simpa using hd
    exact hd'.comp_hasDerivAt 1 hpath
  have hd2 : HasDerivAt (fun l : ℝ => F (l • x)) (F x) 1 := by
    have h : HasDerivAt (fun l : ℝ => l * F x) (F x) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const (F x)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds one_pos] with l hl using hhom l hl
  have heq := hd1.unique hd2
  have hlin : F' x = F' (1, 0) * x.1 + F' (0, 1) * x.2 := by
    have : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [← heq, hlin]

/-- **AKMM, Definition 6 and p. 146: Walras's law in the growth economy.** If every consumer's
budget `c_{i,t} + k_{i,t+1} = (1 − δ + rₜ)k_{i,t} + wₜeᵢ` holds, consumption and capital are
integrable, `∫ eᵢ di = 1`, `∫ k_{i,s} di = K_s` and the firm's prices satisfy Euler's identity
`F(Kₜ, 1) = rₜKₜ + wₜ`, then `Cₜ + K_{t+1} = F(Kₜ, 1) + (1 − δ)Kₜ`: the resource constraint is
redundant. -/
theorem seq_growth_walras {μ : Measure I} {δ Ft : ℝ} {e : I → ℝ} {c k : I → ℕ → ℝ}
    {r w K : ℕ → ℝ} {t : ℕ} (hb : ∀ i, c i t + k i (t + 1) = (1 - δ + r t) * k i t + w t * e i)
    (hc : Integrable (c · t) μ) (hk : ∀ s, Integrable (k · s) μ) (he : Integrable e μ)
    (he1 : ∫ i, e i ∂μ = 1) (hK : ∀ s, ∫ i, k i s ∂μ = K s) (heuler : Ft = r t * K t + w t) :
    ∫ i, c i t ∂μ + K (t + 1) = Ft + (1 - δ) * K t := by
  have h := congrArg (fun f => ∫ i, f i ∂μ) (funext hb)
  simp only at h
  rw [integral_add hc (hk (t + 1)), integral_add ((hk t).const_mul _) (he.const_mul _),
    integral_const_mul, integral_const_mul, he1, hK, hK] at h
  rw [heuler]
  linarith

end AKMM.CompetitiveEquilibrium
