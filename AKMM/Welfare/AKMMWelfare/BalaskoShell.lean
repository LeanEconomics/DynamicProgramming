/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMWelfare.OGEndowment
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Balasko–Shell theorem

AKMM, §6.4.1, pp. 178–179. The book cites Balasko and Shell (1980): in the overlapping-generations
endowment economy "a competitive equilibrium … is Pareto optimal if and only if `Σ 1/pₜ = ∞`",
under "regularity conditions and a bounded sequence for total endowments", which "mainly restrict
the curvature of consumers' indifference curves away from the two extreme cases (linear and
kinked)". The book gives no proof. This module proves the theorem for the book's economy (one good
per date, generation `t` living at `t` and `t + 1` with utility `Uₜ(c_y, c_o)`, the initial old
consuming `c_{o,0}`), with `pₜ = q₀⋯q_{t−1}`, in both directions.

The curvature conditions are stated along the equilibrium allocation `c_t = (c_{y,t}, c_{o,t+1})`,
in date-`t` goods, with `v = qₜ(y − c_{o,t+1})` the date-`t` value of extra old-age consumption:

* **not linear** (`bsCurvBelow`, constant `a > 0`): every bundle `(x, y)` with
  `c_{o,t+1} ≤ y ≤ ω_{y,t+1} + ω_{o,t+1}` that generation `t` weakly prefers to `c_t` costs at least
  `a v²` more than `c_t`: the indifference curve lies above the budget line by a quadratic;
* **not kinked** (`bsCurvAbove`, constant `A ≥ 0`, window `δ > 0`): every bundle with
  `c_{y,t} − δ ≤ x ≤ c_{y,t}`, `c_{o,t+1} ≤ y ≤ c_{o,t+1} + δ` that costs at least `A v²` more than
  `c_t` is weakly preferred: the indifference curve lies below a quadratic above the budget line
  (so `qₜ` is the marginal rate of substitution); plus `c_{y,t} > δ`.

Results.

* **Sufficiency** (`bs_sufficiency`): if every `Uₜ` is strictly increasing in `c_y`, `(cy, co)` is
  an equilibrium (Arrow–Debreu form) satisfying `bsCurvBelow` and `Σ 1/pₜ = ∞`, it is Pareto
  optimal. No bound on endowments is needed. Proof: the extra old-age consumption `εₜ` of a
  dominating allocation has values `zₜ = pₜεₜ` with `a z²_{t+1} ≤ pₜ(z_{t+1} − zₜ)`, so
  `1/zₜ − 1/z_{t+1} ≥ a/pₜ` once some `z_s > 0`, which bounds `Σ 1/pₜ`.
* **Necessity** (`bs_necessity`, with the explicit improvement `bsTransfer`,
  `bs_necessity_transfers`): if `Σ 1/pₜ = T < ∞`, the pay-as-you-go transfers
  `εₜ = 1/(pₜ B Dₜ)`, `B = 2A + 1/δ`, `Dₜ = 2T − Σ_{s<t} 1/p_s`, from the young to the old at every
  date, make the initial old strictly and every generation weakly better off.
* **The theorem** (`bs_balasko_shell`): under both conditions, Pareto optimal iff `Σ 1/pₜ = ∞`.
* **Instances.** Log utility with endowments in `[m, M]`, `0 < m`: the conditions hold at the
  (unique, autarkic) equilibrium with `a = m/(2M²)`, `A = 1/m`, `δ = m/2` (`bs_log_curv_below`,
  `bs_log_curv_above`), so the log equilibrium is optimal iff `Σ 1/pₜ = ∞` (`bs_log`,
  `bs_log_equilibrium`); the stationary result `og_balasko_shell_stationary_log` is recovered
  (`bs_stationary_log`). CRRA utility `u(x) + βu(y)`, `u(c) = c^{1−σ}/(1 − σ)`, with endowments in
  `[m, M]`: autarky at `qₜ = β(ω_{o,t+1}/ω_{y,t})^{−σ}` is an equilibrium and both conditions hold
  (`bs_crra_equilibrium`, `bs_crra_curv_below`, `bs_crra_curv_above`), so
  Balasko–Shell holds there (`bs_crra`).

The book's Cass (1972) criterion for capital accumulation is Theorem 6.2 (p. 182), formalised in
`OGProduction` (`theorem_6_2`).
-/

namespace AKMM.Welfare

open Filter Topology AKMM.CompetitiveEquilibrium

/-- **Balasko–Shell: indifference curves are not linear** (AKMM, p. 178). Along the allocation,
any bundle with `c_{o,t+1} ≤ y ≤ ω_{y,t+1} + ω_{o,t+1}` that generation `t` weakly prefers to
`(c_{y,t}, c_{o,t+1})` costs, at the prices `(1, qₜ)`, at least `a(qₜ(y − c_{o,t+1}))²` more. -/
def bsCurvBelow (U : ℕ → ℝ → ℝ → ℝ) (ωy ωo q cy co : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ t x y, 0 < x → co (t + 1) ≤ y → y ≤ ωy (t + 1) + ωo (t + 1) →
    U t (cy t) (co (t + 1)) ≤ U t x y →
      a * (q t * (y - co (t + 1))) ^ 2 ≤ x - cy t + q t * (y - co (t + 1))

/-- **Balasko–Shell: indifference curves are not kinked** (AKMM, p. 178). Along the allocation,
any bundle within `δ` of `(c_{y,t}, c_{o,t+1})`, with less young and more old consumption, that
costs at least `A(qₜ(y − c_{o,t+1}))²` more is weakly preferred. -/
def bsCurvAbove (U : ℕ → ℝ → ℝ → ℝ) (q cy co : ℕ → ℝ) (A δ : ℝ) : Prop :=
  ∀ t x y, cy t - δ ≤ x → x ≤ cy t → co (t + 1) ≤ y → y ≤ co (t + 1) + δ →
    A * (q t * (y - co (t + 1))) ^ 2 ≤ x - cy t + q t * (y - co (t + 1)) →
      U t (cy t) (co (t + 1)) ≤ U t x y

/-- **Balasko–Shell, sufficiency** (AKMM, pp. 178–179). If every `Uₜ` is strictly increasing in
`c_y`, `qₜ > 0`, `(cy, co)` is an equilibrium in Arrow–Debreu form whose indifference curves are
not linear (`bsCurvBelow` with `a > 0`) and `Σ 1/pₜ = ∞`, the equilibrium is Pareto optimal. -/
theorem bs_sufficiency {U : ℕ → ℝ → ℝ → ℝ}
    (hU : ∀ t x x' y, 0 < x → x < x' → 0 < y → U t x y < U t x' y) {ωy ωo q cy co : ℕ → ℝ}
    {a : ℝ} (ha : 0 < a) (hq : ∀ t, 0 < q t) (he : ogADEquilibrium U ωy ωo q cy co)
    (hcurv : bsCurvBelow U ωy ωo q cy co a) (hdiv : ¬ Summable fun t => 1 / seqPrice q t) :
    ogParetoOptimal U ωy ωo cy co := by
  obtain ⟨hpos, -, hclear, hgen⟩ := he
  refine ⟨⟨hpos, fun t => (hclear t).le⟩, ?_⟩
  rintro ⟨cy', co', ⟨hpos', hfeas'⟩, hold, hle, hstrict⟩
  set P := seqPrice q with hP
  have hPpos : ∀ t, 0 < P t := seqPrice_pos hq
  -- a weakly preferred bundle costs at least as much, a strictly preferred one more
  have hcost : ∀ t, cy t + q t * co (t + 1) ≤ cy' t + q t * co' (t + 1) := by
    intro t
    rw [(hgen t).1]
    by_contra hcon
    push Not at hcon
    set x' := ωy t + q t * ωo (t + 1) - q t * co' (t + 1)
    have hx' : cy' t < x' := by simp only [x']; linarith
    have := (hgen t).2 x' (co' (t + 1)) (by linarith [(hpos' t).1]) (hpos' (t + 1)).2
      (by simp only [x']; linarith)
    have := hU t _ _ _ (hpos' t).1 hx' (hpos' (t + 1)).2
    linarith [hle t]
  have hcost_strict : ∀ t, U t (cy t) (co (t + 1)) < U t (cy' t) (co' (t + 1)) →
      cy t + q t * co (t + 1) < cy' t + q t * co' (t + 1) := by
    intro t ht
    rw [(hgen t).1]
    by_contra hcon
    push Not at hcon
    have := (hgen t).2 _ _ (hpos' t).1 (hpos' (t + 1)).2 hcon
    linarith
  -- the extra old-age consumption
  set ε : ℕ → ℝ := fun t => co' t - co t with hε
  have hy' : ∀ t, cy' t ≤ cy t - ε t := fun t => by
    simp only [hε]; linarith [hfeas' t, hclear t]
  have hstep : ∀ t, ε t ≤ q t * ε (t + 1) := fun t => by
    have h1 := hcost t
    have h2 := hy' t
    simp only [hε] at h2 ⊢
    rw [mul_sub]
    linarith
  have hnn : ∀ t, 0 ≤ ε t := by
    intro t
    induction t with
    | zero => simp only [hε]; linarith
    | succ t ih =>
      have := hstep t
      have := hq t
      by_contra hneg
      push Not at hneg
      nlinarith
  -- the curvature step in values `zₜ = pₜεₜ`
  set z : ℕ → ℝ := fun t => P t * ε t with hz
  have hzs : ∀ t, z (t + 1) = P t * (q t * ε (t + 1)) := fun t => by
    simp only [hz, hP, seqPrice_succ]; ring
  have hcurvz : ∀ t, a * z (t + 1) ^ 2 ≤ P t * (z (t + 1) - z t) := by
    intro t
    have hc := hcurv t (cy' t) (co' (t + 1)) (hpos' t).1
      (by linarith [hnn (t + 1)]) (by linarith [hfeas' (t + 1), (hpos' (t + 1)).1]) (hle t)
    have hc' : a * (q t * ε (t + 1)) ^ 2 ≤ -ε t + q t * ε (t + 1) := by
      have := hy' t
      simp only [hε] at this ⊢
      linarith
    have := mul_le_mul_of_nonneg_left hc' (sq_nonneg (P t))
    rw [hzs t]
    simp only [hz]
    linear_combination this
  have hzmono : ∀ t, z t ≤ z (t + 1) := by
    intro t
    have h1 := hcurvz t
    have h2 : 0 ≤ a * z (t + 1) ^ 2 := by positivity
    have h3 := hPpos t
    by_contra hneg
    push Not at hneg
    nlinarith
  -- a strictly positive value
  obtain ⟨s, hs⟩ : ∃ s, 0 < z s := by
    rcases hstrict with h | ⟨T, hT⟩
    · exact ⟨0, mul_pos (hPpos 0) (by simp only [hε]; linarith)⟩
    · refine ⟨T + 1, mul_pos (hPpos _) ?_⟩
      have h1 := hcost_strict T hT
      have h2 := hy' T
      have h3 := hnn T
      have h4 := hq T
      have h5 : ε T < q T * ε (T + 1) := by
        simp only [hε] at h2 ⊢
        rw [mul_sub]
        linarith
      by_contra hneg
      push Not at hneg
      nlinarith
  have hzge : ∀ n, z s ≤ z (s + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => exact ih.trans (hzmono (s + n))
  -- `1/zₜ − 1/z_{t+1} ≥ a/pₜ` from `s` on, and the telescoped bound
  have hrec : ∀ n, a / P (s + n) ≤ 1 / z (s + n) - 1 / z (s + n + 1) := by
    intro n
    have h0 : 0 < z (s + n) := hs.trans_le (hzge n)
    have h1 : z (s + n) ≤ z (s + n + 1) := hzmono _
    have h1' : 0 < z (s + n + 1) := h0.trans_le h1
    have h2 := hcurvz (s + n)
    have h3 := hPpos (s + n)
    rw [div_sub_div _ _ h0.ne' h1'.ne', le_div_iff₀ (mul_pos h0 h1'), div_mul_eq_mul_div,
      div_le_iff₀ h3]
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg ha.le h1'.le)]
  have htel : ∀ n, ∑ k ∈ Finset.range n, a / P (k + s) ≤ 1 / z s - 1 / z (s + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, add_comm n s, ← add_assoc]
      have := hrec n
      linarith
  refine hdiv ((summable_nat_add_iff s).1 ?_)
  refine summable_of_sum_range_le (c := 1 / (a * z s)) (fun k => (one_div_pos.2 (hPpos _)).le)
    fun n => ?_
  have h1 := htel n
  have h2 : 0 < 1 / z (s + n) := one_div_pos.2 (hs.trans_le (hzge n))
  have e : ∑ k ∈ Finset.range n, a / P (k + s) = a * ∑ k ∈ Finset.range n, 1 / P (k + s) := by
    rw [Finset.mul_sum]; congr 1; funext k; ring
  rw [e] at h1
  rw [le_div_iff₀ (mul_pos ha hs)]
  have h3 : a * ∑ k ∈ Finset.range n, 1 / P (k + s) ≤ 1 / z s := by linarith
  rw [le_div_iff₀ hs] at h3
  linarith

/-- **The Balasko–Shell improvement** (AKMM, p. 179): the transfer from the young to the old at
date `t`, `εₜ = 1/(pₜ B Dₜ)` with `B = 2A + 1/δ` and `Dₜ = 2Σ_s 1/p_s − Σ_{s<t} 1/p_s`. -/
noncomputable def bsTransfer (q : ℕ → ℝ) (A δ : ℝ) (t : ℕ) : ℝ :=
  1 / (seqPrice q t * ((2 * A + 1 / δ) *
    (2 * ∑' s, 1 / seqPrice q s - ∑ s ∈ Finset.range t, 1 / seqPrice q s)))

/-- **Balasko–Shell, necessity: the explicit improvement** (AKMM, p. 179). If `qₜ > 0`, the
allocation `(cy, co)` clears markets, its indifference curves are not kinked (`bsCurvAbove` with
`A ≥ 0`, `δ > 0`, `c_{y,t} > δ`) and `Σ 1/pₜ < ∞`, then the pay-as-you-go transfers
`εₜ = bsTransfer q A δ t` (young to old at every date) give a feasible allocation that the initial
old strictly prefer and no generation finds worse. -/
theorem bs_necessity_transfers {U : ℕ → ℝ → ℝ → ℝ} {ωy ωo q cy co : ℕ → ℝ} {A δ : ℝ}
    (hq : ∀ t, 0 < q t) (hpos : ∀ t, 0 < cy t ∧ 0 < co t)
    (hclear : ∀ t, cy t + co t = ωy t + ωo t) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hδc : ∀ t, δ < cy t) (hflat : bsCurvAbove U q cy co A δ)
    (hsum : Summable fun t => 1 / seqPrice q t) :
    ogFeasible ωy ωo (fun t => cy t - bsTransfer q A δ t) (fun t => co t + bsTransfer q A δ t) ∧
      ogDominates U cy co (fun t => cy t - bsTransfer q A δ t)
        (fun t => co t + bsTransfer q A δ t) := by
  set P := seqPrice q with hP
  have hPpos : ∀ t, 0 < P t := seqPrice_pos hq
  have hterm : ∀ t, 0 < 1 / P t := fun t => one_div_pos.2 (hPpos t)
  set T := ∑' s, 1 / P s with hT
  have hle_T : ∀ t, 1 / P t ≤ T := fun t =>
    hsum.le_tsum t fun j _ => (hterm j).le
  have hS : ∀ t, ∑ s ∈ Finset.range t, 1 / P s ≤ T := fun t =>
    hsum.sum_le_tsum _ fun j _ => (hterm j).le
  have hS0 : ∀ t, 0 ≤ ∑ s ∈ Finset.range t, 1 / P s := fun t =>
    Finset.sum_nonneg fun j _ => (hterm j).le
  have hT0 : 0 < T := (hterm 0).trans_le (hle_T 0)
  set B := 2 * A + 1 / δ with hB
  have hB0 : 0 < B := by rw [hB]; have := one_div_pos.2 hδ; linarith
  set D : ℕ → ℝ := fun t => 2 * T - ∑ s ∈ Finset.range t, 1 / P s with hD
  have hDge : ∀ t, T ≤ D t := fun t => by simp only [hD]; linarith [hS t]
  have hDle : ∀ t, D t ≤ 2 * T := fun t => by simp only [hD]; linarith [hS0 t]
  have hDstep : ∀ t, D t = D (t + 1) + 1 / P t := fun t => by
    simp only [hD, Finset.sum_range_succ]; ring
  set ε := bsTransfer q A δ with hε
  have hεD : ∀ t, ε t = 1 / (P t * (B * D t)) := fun t => rfl
  have hDpos : ∀ t, 0 < D t := fun t => hT0.trans_le (hDge t)
  have hε0 : ∀ t, 0 < ε t := fun t => by
    rw [hεD]; exact one_div_pos.2 (mul_pos (hPpos t) (mul_pos hB0 (hDpos t)))
  have hεδ : ∀ t, ε t ≤ δ := by
    intro t
    have h1 : 1 ≤ P t * T := by
      have := hle_T t
      rw [div_le_iff₀ (hPpos t)] at this
      linarith
    have h2 : 1 / δ ≤ B := by rw [hB]; linarith
    have h3 : 1 ≤ δ * B := by rw [div_le_iff₀ hδ] at h2; linarith
    rw [hεD, div_le_iff₀ (mul_pos (hPpos t) (mul_pos hB0 (hDpos t)))]
    have h4 : P t * T ≤ P t * D t := mul_le_mul_of_nonneg_left (hDge t) (hPpos t).le
    have h5 : 0 ≤ δ * B := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  -- each generation's net gain in value is at least `A` times the squared transfer value
  have hgain : ∀ t, A * (q t * ε (t + 1)) ^ 2 ≤ -ε t + q t * ε (t + 1) := by
    intro t
    have hqε : q t * ε (t + 1) = 1 / (P t * (B * D (t + 1))) := by
      rw [hεD, hP, seqPrice_succ]
      have := hq t
      have := hPpos t
      field_simp
    have hP0 := hPpos t
    have hD1 := hDpos (t + 1)
    have key : A * D t ≤ B * D (t + 1) := by
      have h1 : A * D t ≤ A * (2 * T) := mul_le_mul_of_nonneg_left (hDle t) hA
      have h2 : B * T ≤ B * D (t + 1) := mul_le_mul_of_nonneg_left (hDge (t + 1)) hB0.le
      have h3 : 2 * A ≤ B := by rw [hB]; have := one_div_pos.2 hδ; linarith
      nlinarith
    have e : -ε t + q t * ε (t + 1) - A * (q t * ε (t + 1)) ^ 2 =
        (B * D (t + 1) - A * D t) / (P t ^ 2 * B ^ 2 * D t * D (t + 1) ^ 2) := by
      rw [hqε, hεD, hDstep t]
      have : 0 < D (t + 1) + 1 / P t := by linarith [hterm t]
      field_simp
      ring
    have : 0 ≤ (B * D (t + 1) - A * D t) / (P t ^ 2 * B ^ 2 * D t * D (t + 1) ^ 2) := by
      have := hDpos t
      apply div_nonneg (by linarith)
      positivity
    linarith
  refine ⟨⟨fun t => ⟨by linarith [hεδ t, hδc t], by linarith [(hpos t).2, hε0 t]⟩,
    fun t => by linarith [hclear t]⟩, by linarith [hε0 0], fun t => ?_,
    Or.inl (by linarith [hε0 0])⟩
  refine hflat t _ _ (by linarith [hεδ t]) (by linarith [hε0 t]) (by linarith [hε0 (t + 1)])
    (by linarith [hεδ (t + 1)]) ?_
  have := hgain t
  rw [show co (t + 1) + ε (t + 1) - co (t + 1) = ε (t + 1) by ring]
  linarith

/-- **Balasko–Shell, necessity** (AKMM, pp. 178–179). An equilibrium whose indifference curves
are not kinked (`bsCurvAbove`, `A ≥ 0`, `δ > 0`, `c_{y,t} > δ`) and with `Σ 1/pₜ < ∞` is not
Pareto optimal: `bsTransfer` gives the improvement. -/
theorem bs_necessity {U : ℕ → ℝ → ℝ → ℝ} {ωy ωo q cy co : ℕ → ℝ} {A δ : ℝ}
    (hq : ∀ t, 0 < q t) (he : ogADEquilibrium U ωy ωo q cy co) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hδc : ∀ t, δ < cy t) (hflat : bsCurvAbove U q cy co A δ)
    (hsum : Summable fun t => 1 / seqPrice q t) : ¬ ogParetoOptimal U ωy ωo cy co := by
  rintro ⟨-, hno⟩
  exact hno ⟨_, _, bs_necessity_transfers hq he.1 he.2.2.1 hA hδ hδc hflat hsum⟩

/-- **The Balasko–Shell theorem** (AKMM, pp. 178–179). In the OG endowment economy, let every
`Uₜ` be strictly increasing in `c_y`, `qₜ > 0`, and `(cy, co)` an equilibrium whose indifference
curves are neither linear (`bsCurvBelow`, `a > 0`) nor kinked (`bsCurvAbove`, `A ≥ 0`, `δ > 0`,
`c_{y,t} > δ`). Then the equilibrium is Pareto optimal iff `Σ 1/pₜ = ∞`. -/
theorem bs_balasko_shell {U : ℕ → ℝ → ℝ → ℝ}
    (hU : ∀ t x x' y, 0 < x → x < x' → 0 < y → U t x y < U t x' y) {ωy ωo q cy co : ℕ → ℝ}
    {a A δ : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hδ : 0 < δ) (hq : ∀ t, 0 < q t)
    (he : ogADEquilibrium U ωy ωo q cy co) (hcurv : bsCurvBelow U ωy ωo q cy co a)
    (hδc : ∀ t, δ < cy t) (hflat : bsCurvAbove U q cy co A δ) :
    ogParetoOptimal U ωy ωo cy co ↔ ¬ Summable fun t => 1 / seqPrice q t :=
  ⟨fun hPO hsum => bs_necessity hq he hA hδ hδc hflat hsum hPO,
    bs_sufficiency hU ha hq he hcurv⟩

/-! ### Log utility -/

/-- **Log utility: indifference curves are not linear.** With endowments in `[m, M]`, `0 < m`,
autarky at `qₜ = ω_{y,t}/ω_{o,t+1}` satisfies `bsCurvBelow` with `a = m/(2M²)`: a weakly
preferred bundle has `xy ≥ ω_{y,t}ω_{o,t+1}`, so its extra cost is at least
`ω_{y,t}(y − ω_{o,t+1})²/(yω_{o,t+1})`. -/
theorem bs_log_curv_below {ωy ωo : ℕ → ℝ} {m M : ℝ} (hm : 0 < m)
    (hωy : ∀ t, m ≤ ωy t ∧ ωy t ≤ M) (hωo : ∀ t, m ≤ ωo t ∧ ωo t ≤ M) :
    bsCurvBelow ogLogU ωy ωo (fun t => ωy t / ωo (t + 1)) ωy ωo (m / (2 * M ^ 2)) := by
  intro t x y hx hy1 hy2 hU
  set c := ωy t with hc
  set d := ωo (t + 1) with hd
  have hc0 : 0 < c := hm.trans_le (hωy t).1
  have hd0 : 0 < d := hm.trans_le (hωo (t + 1)).1
  have hy0 : 0 < y := hd0.trans_le hy1
  have hM : 0 < M := hc0.trans_le (hωy t).2
  have hxy : c * d ≤ x * y := by
    simp only [ogLogU] at hU
    rw [← Real.log_mul hc0.ne' hd0.ne', ← Real.log_mul hx.ne' hy0.ne'] at hU
    exact (Real.log_le_log_iff (mul_pos hc0 hd0) (mul_pos hx hy0)).1 hU
  have hyM : y ≤ 2 * M := by linarith [(hωy (t + 1)).2, (hωo (t + 1)).2]
  -- the extra cost times `y d`
  have h1 : c * (y - d) ^ 2 ≤ (x - c + c / d * (y - d)) * (y * d) := by
    have e : (x - c + c / d * (y - d)) * (y * d) = d * (x * y) - 2 * c * y * d + c * y ^ 2 := by
      field_simp; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hxy hd0.le]
  have h2 : m / (2 * M ^ 2) * (c / d * (y - d)) ^ 2 * (y * d) ≤ c * (y - d) ^ 2 := by
    have e : m / (2 * M ^ 2) * (c / d * (y - d)) ^ 2 * (y * d) =
        c * (y - d) ^ 2 * (m * c * y / (2 * M ^ 2 * d)) := by
      field_simp
    rw [e]
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [div_le_one (by positivity)]
    have h3 : m * c ≤ m * M := mul_le_mul_of_nonneg_left (hωy t).2 hm.le
    have h4 : m * c * y ≤ m * M * (2 * M) :=
      mul_le_mul h3 hyM hy0.le (by positivity)
    have h5 : m ≤ d := (hωo (t + 1)).1
    nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * M ^ 2)]
  exact le_of_mul_le_mul_right (h2.trans h1) (mul_pos hy0 hd0)

/-- **Log utility: indifference curves are not kinked.** With endowments in `[m, M]`,
`0 < m`, autarky at `qₜ = ω_{y,t}/ω_{o,t+1}` satisfies `bsCurvAbove` with `A = 1/m`, `δ = m/2`:
giving `e` when young for `f` when old with `g − e ≥ g²/m`, `g = qₜf`, keeps
`xy ≥ ω_{y,t}ω_{o,t+1}`. -/
theorem bs_log_curv_above {ωy ωo : ℕ → ℝ} {m : ℝ} (hm : 0 < m)
    (hωy : ∀ t, m ≤ ωy t) (hωo : ∀ t, 0 < ωo t) :
    bsCurvAbove ogLogU (fun t => ωy t / ωo (t + 1)) ωy ωo (1 / m) (m / 2) := by
  intro t x y hx1 hx2 hy1 _ hineq
  set c := ωy t with hc
  set d := ωo (t + 1) with hd
  have hcm : m ≤ c := hωy t
  have hc0 : 0 < c := hm.trans_le hcm
  have hd0 : 0 < d := hωo (t + 1)
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hd0.trans_le hy1
  set e := c - x with he
  set g := c / d * (y - d) with hg
  have he0 : 0 ≤ e := by rw [he]; linarith
  have hg0 : 0 ≤ g := by rw [hg]; exact mul_nonneg (by positivity) (by linarith)
  have hineq' : g ^ 2 / m ≤ g - e := by
    rw [hg, he]; rw [hg] at hineq; linarith [show 1 / m * (c / d * (y - d)) ^ 2 =
      (c / d * (y - d)) ^ 2 / m by ring]
  have heg : e ≤ g := by have : 0 ≤ g ^ 2 / m := by positivity
                         linarith
  have h1 : g ^ 2 / c ≤ g ^ 2 / m := div_le_div_of_nonneg_left (sq_nonneg g) hm hcm
  have h2 : e * g / c ≤ g ^ 2 / c := by
    rw [sq]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right heg hg0) hc0.le
  have hgap : 0 ≤ g - e - e * g / c := by linarith
  have e1 : x * y - c * d = d * (g - e - e * g / c) := by
    rw [hg, he]; field_simp; ring
  have hxy : c * d ≤ x * y := by nlinarith [mul_nonneg hd0.le hgap]
  simp only [ogLogU]
  rw [← Real.log_mul hc0.ne' hd0.ne', ← Real.log_mul hx0.ne' hy0.ne']
  exact Real.log_le_log (mul_pos hc0 hd0) hxy

/-- The autarkic equilibrium of the log economy in Arrow–Debreu form, at
`qₜ = ω_{y,t}/ω_{o,t+1}`. -/
theorem bs_log_ad {ωy ωo : ℕ → ℝ} (hωy : ∀ t, 0 < ωy t) (hωo : ∀ t, 0 < ωo t) :
    ogADEquilibrium ogLogU ωy ωo (fun t => ωy t / ωo (t + 1)) ωy ωo := by
  refine og_ad_of_seq (a := fun _ => 0) hωo ?_
  exact (og_log_equilibrium_iff hωy hωo (fun t => div_pos (hωy t) (hωo (t + 1)))).2
    ⟨fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- **Balasko–Shell for the log economy** (AKMM, pp. 178–179). With `log c_y + log c_o` and
endowments in `[m, M]`, `0 < m`, the autarkic equilibrium (`qₜ = ω_{y,t}/ω_{o,t+1}`) is Pareto
optimal iff `Σ 1/pₜ = ∞`. -/
theorem bs_log {ωy ωo : ℕ → ℝ} {m M : ℝ} (hm : 0 < m)
    (hωy : ∀ t, m ≤ ωy t ∧ ωy t ≤ M) (hωo : ∀ t, m ≤ ωo t ∧ ωo t ≤ M) :
    ogParetoOptimal ogLogU ωy ωo ωy ωo ↔
      ¬ Summable fun t => 1 / seqPrice (fun t => ωy t / ωo (t + 1)) t := by
  have hy0 : ∀ t, 0 < ωy t := fun t => hm.trans_le (hωy t).1
  have ho0 : ∀ t, 0 < ωo t := fun t => hm.trans_le (hωo t).1
  have hM : 0 < M := (hy0 0).trans_le (hωy 0).2
  exact bs_balasko_shell og_logU_mono (by positivity) (by positivity) (by positivity)
    (fun t => div_pos (hy0 t) (ho0 (t + 1))) (bs_log_ad hy0 ho0) (bs_log_curv_below hm hωy hωo)
    (fun t => by linarith [(hωy t).1]) (bs_log_curv_above hm (fun t => (hωy t).1) ho0)

/-- **Balasko–Shell for the book's log economy, any equilibrium** (AKMM, pp. 177–179). With
endowments in `[m, M]`, `0 < m`, a sequential equilibrium (Chapter 5's Definition 11) is Pareto
optimal iff `Σ 1/pₜ = ∞`, `pₜ = q₀⋯q_{t−1}` its Arrow–Debreu prices. -/
theorem bs_log_equilibrium {ωy ωo cy co a q : ℕ → ℝ} {m M : ℝ} (hm : 0 < m)
    (hωy : ∀ t, m ≤ ωy t ∧ ωy t ≤ M) (hωo : ∀ t, m ≤ ωo t ∧ ωo t ≤ M) (hq : ∀ t, 0 < q t)
    (he : IsOGEndowEquilibrium 0 Real.log 1 ωy ωo cy co a q) :
    ogParetoOptimal ogLogU ωy ωo cy co ↔ ¬ Summable fun t => 1 / seqPrice q t := by
  have hy0 : ∀ t, 0 < ωy t := fun t => hm.trans_le (hωy t).1
  have ho0 : ∀ t, 0 < ωo t := fun t => hm.trans_le (hωo t).1
  obtain ⟨hqt, hz⟩ := (og_log_equilibrium_iff hy0 ho0 hq).1 he
  have ecy : cy = ωy := funext fun t => (hz t).2.1
  have eco : co = ωo := funext fun t => (hz t).2.2
  have eq : q = fun t => ωy t / ωo (t + 1) := funext hqt
  rw [ecy, eco, eq]
  exact bs_log hm hωy hωo

/-- **Corollary: the stationary log economy** (AKMM, pp. 178–179). The first half of
`og_balasko_shell_stationary_log` as a special case of `bs_log`: with constant `ω_y, ω_o > 0`,
autarky is Pareto optimal iff `Σ 1/pₜ = ∞`. -/
theorem bs_stationary_log {ωy ωo : ℝ} (hy : 0 < ωy) (ho : 0 < ωo) :
    ogParetoOptimal ogLogU (fun _ => ωy) (fun _ => ωo) (fun _ => ωy) (fun _ => ωo) ↔
      ¬ Summable fun t => 1 / seqPrice (fun _ => ωy / ωo) t :=
  bs_log (m := min ωy ωo) (M := max ωy ωo) (lt_min hy ho)
    (fun _ => ⟨min_le_left _ _, le_max_left _ _⟩) (fun _ => ⟨min_le_right _ _, le_max_right _ _⟩)

/-! ### CRRA utility -/

/-- A function with nonnegative derivative on `[s, t]` has `φ(s) ≤ φ(t)`. -/
theorem bs_mono_of_deriv {φ φ' : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hd : ∀ r ∈ Set.Icc s t, HasDerivAt φ (φ' r) r) (hnn : ∀ r ∈ Set.Icc s t, 0 ≤ φ' r) :
    φ s ≤ φ t := by
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (f' := φ') (convex_Icc s t)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt)
    (fun r hr => hnn r (interior_subset hr))
  exact hmono ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

/-- **Curvature bounded below gives a quadratic upper bound.** If `f′ = g` on `[L, H]` and
`g(s) − g(t) ≥ κ(t − s)` for `s ≤ t` there (`−f″ ≥ κ`), then
`f(y) ≤ f(c) + g(c)(y − c) − (κ/2)(y − c)²` on `[L, H]`. -/
theorem bs_quad_upper {f g : ℝ → ℝ} {L H κ : ℝ}
    (hd : ∀ r ∈ Set.Icc L H, HasDerivAt f (g r) r)
    (hg : ∀ s ∈ Set.Icc L H, ∀ t ∈ Set.Icc L H, s ≤ t → κ * (t - s) ≤ g s - g t)
    {c y : ℝ} (hc : c ∈ Set.Icc L H) (hy : y ∈ Set.Icc L H) :
    f y ≤ f c + g c * (y - c) - κ / 2 * (y - c) ^ 2 := by
  have hφ : ∀ r ∈ Set.Icc L H, HasDerivAt (fun r => f c + g c * (r - c) - κ / 2 * (r - c) ^ 2 - f r)
      (g c - κ * (r - c) - g r) r := by
    intro r hr
    have := ((((hasDerivAt_id r).sub_const c).const_mul (g c)).const_add (f c)).sub
      ((((hasDerivAt_id r).sub_const c).pow 2).const_mul (κ / 2)) |>.sub (hd r hr)
    refine this.congr_deriv ?_
    simp only [id]
    push_cast
    ring
  rcases le_total c y with hcy | hyc
  · have := bs_mono_of_deriv (φ := fun r => f c + g c * (r - c) - κ / 2 * (r - c) ^ 2 - f r)
      hcy (fun r hr => hφ r ⟨hc.1.trans hr.1, hr.2.trans hy.2⟩) fun r hr => by
        have := hg c hc r ⟨hc.1.trans hr.1, hr.2.trans hy.2⟩ hr.1
        linarith
    simp only [sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero] at this
    linarith
  · have := bs_mono_of_deriv (φ := fun r => -(f c + g c * (r - c) - κ / 2 * (r - c) ^ 2 - f r))
      (φ' := fun r => -(g c - κ * (r - c) - g r))
      hyc (fun r hr => (hφ r ⟨hy.1.trans hr.1, hr.2.trans hc.2⟩).neg) fun r hr => by
        have := hg r ⟨hy.1.trans hr.1, hr.2.trans hc.2⟩ c hc hr.2
        linarith
    simp only [sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero] at this
    linarith

/-- **Curvature bounded above gives a quadratic lower bound.** If `f′ = g` on `[L, H]` and
`g(s) − g(t) ≤ K(t − s)` for `s ≤ t` there (`−f″ ≤ K`), then
`f(y) ≥ f(c) + g(c)(y − c) − (K/2)(y − c)²` on `[L, H]`. -/
theorem bs_quad_lower {f g : ℝ → ℝ} {L H K : ℝ}
    (hd : ∀ r ∈ Set.Icc L H, HasDerivAt f (g r) r)
    (hg : ∀ s ∈ Set.Icc L H, ∀ t ∈ Set.Icc L H, s ≤ t → g s - g t ≤ K * (t - s))
    {c y : ℝ} (hc : c ∈ Set.Icc L H) (hy : y ∈ Set.Icc L H) :
    f c + g c * (y - c) - K / 2 * (y - c) ^ 2 ≤ f y := by
  have hφ : ∀ r ∈ Set.Icc L H, HasDerivAt
      (fun r => f r - (f c + g c * (r - c) - K / 2 * (r - c) ^ 2))
      (g r - (g c - K * (r - c))) r := by
    intro r hr
    have := (hd r hr).sub ((((hasDerivAt_id r).sub_const c).const_mul (g c)).const_add (f c) |>.sub
      ((((hasDerivAt_id r).sub_const c).pow 2).const_mul (K / 2)))
    refine this.congr_deriv ?_
    simp only [id]
    push_cast
    ring
  rcases le_total c y with hcy | hyc
  · have := bs_mono_of_deriv hcy (fun r hr => hφ r ⟨hc.1.trans hr.1, hr.2.trans hy.2⟩)
      fun r hr => by
        have := hg c hc r ⟨hc.1.trans hr.1, hr.2.trans hy.2⟩ hr.1
        linarith
    simp only [sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero] at this
    linarith
  · have := bs_mono_of_deriv (φ := fun r => -(f r - (f c + g c * (r - c) - K / 2 * (r - c) ^ 2)))
      (φ' := fun r => -(g r - (g c - K * (r - c))))
      hyc (fun r hr => (hφ r ⟨hy.1.trans hr.1, hr.2.trans hc.2⟩).neg) fun r hr => by
        have := hg r ⟨hy.1.trans hr.1, hr.2.trans hc.2⟩ c hc hr.2
        linarith
    simp only [sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero] at this
    linarith

/-- For `σ > 0` and `0 < s ≤ t ≤ H`: `s^{−σ} − t^{−σ} ≥ σH^{−σ−1}(t − s)`. -/
theorem bs_rpow_gap_lower {σ s t H : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hst : s ≤ t) (htH : t ≤ H) :
    σ * H ^ (-σ - 1) * (t - s) ≤ s ^ (-σ) - t ^ (-σ) := by
  have := bs_mono_of_deriv (φ := fun r => -r ^ (-σ) - σ * H ^ (-σ - 1) * r)
    (φ' := fun r => -(-σ * r ^ (-σ - 1)) - σ * H ^ (-σ - 1)) hst
    (fun r hr => by
      have hr0 : 0 < r := hs.trans_le hr.1
      have := ((Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hr0.ne')).neg).sub
        ((hasDerivAt_id r).const_mul (σ * H ^ (-σ - 1)))
      refine this.congr_deriv ?_
      ring)
    fun r hr => by
      have hr0 : 0 < r := hs.trans_le hr.1
      have := Real.rpow_le_rpow_of_nonpos hr0 (hr.2.trans htH) (by linarith : -σ - 1 ≤ 0)
      nlinarith
  linarith

/-- For `σ > 0` and `0 < L ≤ s ≤ t`: `s^{−σ} − t^{−σ} ≤ σL^{−σ−1}(t − s)`. -/
theorem bs_rpow_gap_upper {σ s t L : ℝ} (hσ : 0 < σ) (hL : 0 < L) (hLs : L ≤ s) (hst : s ≤ t) :
    s ^ (-σ) - t ^ (-σ) ≤ σ * L ^ (-σ - 1) * (t - s) := by
  have hs : 0 < s := hL.trans_le hLs
  have := bs_mono_of_deriv (φ := fun r => r ^ (-σ) + σ * L ^ (-σ - 1) * r)
    (φ' := fun r => -σ * r ^ (-σ - 1) + σ * L ^ (-σ - 1)) hst
    (fun r hr => by
      have hr0 : 0 < r := hs.trans_le hr.1
      have := (Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hr0.ne')).add
        ((hasDerivAt_id r).const_mul (σ * L ^ (-σ - 1)))
      refine this.congr_deriv ?_
      ring)
    fun r hr => by
      have hr0 : 0 < r := hs.trans_le hr.1
      have := Real.rpow_le_rpow_of_nonpos hL (hLs.trans hr.1) (by linarith : -σ - 1 ≤ 0)
      nlinarith
  linarith

/-- CRRA utility `u(c) = c^{1−σ}/(1 − σ)` (`σ ≠ 1`). -/
noncomputable def bsCRRA (σ c : ℝ) : ℝ := c ^ (1 - σ) / (1 - σ)

/-- `u′(c) = c^{−σ}` for CRRA utility. -/
theorem bs_crra_hasDerivAt {σ c : ℝ} (hσ1 : σ ≠ 1) (hc : 0 < c) :
    HasDerivAt (bsCRRA σ) (c ^ (-σ)) c := by
  have := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).div_const (1 - σ)
  refine this.congr_deriv ?_
  rw [show 1 - σ - 1 = -σ by ring]
  have : (1 - σ) ≠ 0 := sub_ne_zero.2 (Ne.symm hσ1)
  field_simp

/-- CRRA utility is concave: `u(x) ≤ u(c) + c^{−σ}(x − c)` for `x, c > 0`. -/
theorem bs_crra_tangent {σ c x : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hc : 0 < c) (hx : 0 < x) :
    bsCRRA σ x ≤ bsCRRA σ c + c ^ (-σ) * (x - c) := by
  have hL : 0 < min x c := lt_min hx hc
  have := bs_quad_upper (f := bsCRRA σ) (g := fun r => r ^ (-σ)) (L := min x c) (H := max x c)
    (κ := 0) (fun r hr => bs_crra_hasDerivAt hσ1 (hL.trans_le hr.1))
    (fun s hs t _ hst => by
      have := Real.rpow_le_rpow_of_nonpos (hL.trans_le hs.1) hst (by linarith : -σ ≤ 0)
      linarith)
    ⟨min_le_right _ _, le_max_right _ _⟩ ⟨min_le_left _ _, le_max_left _ _⟩
  simpa using this

/-- The CRRA economy: `Uₜ(x, y) = u(x) + βu(y)`. -/
noncomputable def bsCRRAU (σ β : ℝ) : ℕ → ℝ → ℝ → ℝ := fun _ x y => bsCRRA σ x + β * bsCRRA σ y

/-- The autarky price of the CRRA economy, `βω_{o,t+1}^{−σ}/ω_{y,t}^{−σ}`. -/
noncomputable def bsCRRAPrice (σ β : ℝ) (ωy ωo : ℕ → ℝ) (t : ℕ) : ℝ :=
  β * ωo (t + 1) ^ (-σ) / ωy t ^ (-σ)

/-- CRRA utility `u(x) + βu(y)` is strictly increasing in `x`. -/
theorem bs_crra_mono {σ β : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    ∀ t x x' y, 0 < x → x < x' → 0 < y → bsCRRAU σ β t x y < bsCRRAU σ β t x' y := by
  intro _ x x' _ hx hxx' _
  have h1 := bs_crra_tangent hσ hσ1 (hx.trans hxx') hx
  have h2 : 0 < x' ^ (-σ) := Real.rpow_pos_of_pos (hx.trans hxx') _
  have h3 : x' ^ (-σ) * (x - x') < 0 := mul_neg_of_pos_of_neg h2 (by linarith)
  simp only [bsCRRAU]
  linarith

/-- **The CRRA economy's equilibrium.** With `σ > 0`, `σ ≠ 1`, `β > 0` and positive endowments,
autarky at `qₜ = βω_{o,t+1}^{−σ}/ω_{y,t}^{−σ}` (the marginal rate of substitution) is an
equilibrium in Arrow–Debreu form. -/
theorem bs_crra_equilibrium {σ β : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β)
    {ωy ωo : ℕ → ℝ} (hωy : ∀ t, 0 < ωy t) (hωo : ∀ t, 0 < ωo t) :
    ogADEquilibrium (bsCRRAU σ β) ωy ωo (bsCRRAPrice σ β ωy ωo) ωy ωo := by
  refine ⟨fun t => ⟨hωy t, hωo t⟩, rfl, fun t => rfl, fun t => ⟨rfl, fun x y hx hy hb => ?_⟩⟩
  have h1 := bs_crra_tangent hσ hσ1 (hωy t) hx
  have h2 := mul_le_mul_of_nonneg_left (bs_crra_tangent hσ hσ1 (hωo (t + 1)) hy) hβ.le
  have hGc : 0 < ωy t ^ (-σ) := Real.rpow_pos_of_pos (hωy t) _
  have hq : ωy t ^ (-σ) * bsCRRAPrice σ β ωy ωo t = β * ωo (t + 1) ^ (-σ) := by
    simp only [bsCRRAPrice]; field_simp
  have h4 : ωy t ^ (-σ) * (x - ωy t) + β * ωo (t + 1) ^ (-σ) * (y - ωo (t + 1)) =
      ωy t ^ (-σ) * ((x - ωy t) + bsCRRAPrice σ β ωy ωo t * (y - ωo (t + 1))) := by
    rw [mul_add, ← mul_assoc, hq]
  have h5 : ωy t ^ (-σ) * ((x - ωy t) + bsCRRAPrice σ β ωy ωo t * (y - ωo (t + 1))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hGc.le (by linarith)
  simp only [bsCRRAU]
  nlinarith

/-- **CRRA utility: indifference curves are not linear.** With endowments in `[m, M]`, `0 < m`,
autarky satisfies `bsCurvBelow` with `a = σ(2M)^{−σ−1}M^{−σ}/(2βm^{−2σ})`: `−u″ ≥ σ(2M)^{−σ−1}`
on `[m, 2M]`. -/
theorem bs_crra_curv_below {σ β m M : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hm : 0 < m)
    {ωy ωo : ℕ → ℝ} (hωy : ∀ t, m ≤ ωy t ∧ ωy t ≤ M) (hωo : ∀ t, m ≤ ωo t ∧ ωo t ≤ M) :
    bsCurvBelow (bsCRRAU σ β) ωy ωo (bsCRRAPrice σ β ωy ωo) ωy ωo
      (σ * (2 * M) ^ (-σ - 1) * M ^ (-σ) / (2 * β * (m ^ (-σ)) ^ 2)) := by
  intro t x y hx hy1 hy2 hU
  set c := ωy t with hc
  set d := ωo (t + 1) with hd
  have hc0 : 0 < c := hm.trans_le (hωy t).1
  have hd0 : 0 < d := hm.trans_le (hωo (t + 1)).1
  have hM : 0 < M := hc0.trans_le (hωy t).2
  have hyM : y ≤ 2 * M := by linarith [(hωy (t + 1)).2, (hωo (t + 1)).2]
  set κ := σ * (2 * M) ^ (-σ - 1) with hκ
  have hκ0 : 0 < κ := by positivity
  set Gc := c ^ (-σ) with hGc
  set G := d ^ (-σ) with hG
  have hGc0 : 0 < Gc := Real.rpow_pos_of_pos hc0 _
  have hG0 : 0 < G := Real.rpow_pos_of_pos hd0 _
  set q := bsCRRAPrice σ β ωy ωo t with hq
  have hqG : Gc * q = β * G := by
    have hne : ωy t ^ (-σ) ≠ 0 := hGc0.ne'
    simp only [hq, bsCRRAPrice, hGc, hG, hc, hd]; field_simp
  have h1 := bs_crra_tangent hσ hσ1 hc0 hx
  have h2 := bs_quad_upper (f := bsCRRA σ) (g := fun r => r ^ (-σ)) (L := m) (H := 2 * M) (κ := κ)
    (fun r hr => bs_crra_hasDerivAt hσ1 (hm.trans_le hr.1))
    (fun s hs t' ht' hst => bs_rpow_gap_lower hσ (hm.trans_le hs.1) hst ht'.2)
    (c := d) (y := y) ⟨(hωo (t + 1)).1, by linarith [(hωo (t + 1)).2]⟩
    ⟨(hωo (t + 1)).1.trans hy1, hyM⟩
  simp only [bsCRRAU] at hU
  set f := y - d with hf
  set R := x - c + q * f with hR
  have h3 : β * κ / 2 * f ^ 2 ≤ Gc * R := by
    have e : Gc * R = Gc * (x - c) + β * G * f := by rw [hR, mul_add, ← mul_assoc, hqG]
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h2 hβ.le]
  -- `Gc a q² ≤ βκ/2`
  have hMG : M ^ (-σ) ≤ Gc := Real.rpow_le_rpow_of_nonpos hc0 (hωy t).2 (by linarith)
  have hGm : G ≤ m ^ (-σ) := Real.rpow_le_rpow_of_nonpos hm (hωo (t + 1)).1 (by linarith)
  have hmσ : 0 < m ^ (-σ) := Real.rpow_pos_of_pos hm _
  have hMσ : 0 < M ^ (-σ) := Real.rpow_pos_of_pos hM _
  have hkey : Gc * (κ * M ^ (-σ) / (2 * β * (m ^ (-σ)) ^ 2)) * q ^ 2 ≤ β * κ / 2 := by
    have e : Gc * (κ * M ^ (-σ) / (2 * β * (m ^ (-σ)) ^ 2)) * q ^ 2 =
        β * κ / 2 * (M ^ (-σ) / Gc) * (G / m ^ (-σ)) ^ 2 := by
      have hq' : q = β * G / Gc := by rw [← hqG]; field_simp
      rw [hq']
      field_simp
    rw [e]
    have f1 : M ^ (-σ) / Gc ≤ 1 := (div_le_one hGc0).2 hMG
    have f2 : (G / m ^ (-σ)) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hmσ).2 hGm)
    have f3 : 0 ≤ β * κ / 2 := by positivity
    calc β * κ / 2 * (M ^ (-σ) / Gc) * (G / m ^ (-σ)) ^ 2 ≤ β * κ / 2 * 1 * 1 := by
          gcongr
      _ = β * κ / 2 := by ring
  have h4 : Gc * (κ * M ^ (-σ) / (2 * β * (m ^ (-σ)) ^ 2) * (q * f) ^ 2) ≤ Gc * R := by
    have := mul_le_mul_of_nonneg_right hkey (sq_nonneg f)
    nlinarith
  exact le_of_mul_le_mul_left h4 hGc0

/-- **CRRA utility: indifference curves are not kinked.** With endowments in `[m, M]`, `0 < m`,
autarky satisfies `bsCurvAbove` with `δ = m/2` and
`A = σ(m/2)^{−σ−1}(1 + m^{−2σ}/(βM^{−2σ}))/(2M^{−σ})`: `−u″ ≤ σ(m/2)^{−σ−1}` on `[m/2, 2M]`. -/
theorem bs_crra_curv_above {σ β m M : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hm : 0 < m)
    {ωy ωo : ℕ → ℝ} (hωy : ∀ t, m ≤ ωy t ∧ ωy t ≤ M) (hωo : ∀ t, m ≤ ωo t ∧ ωo t ≤ M) :
    bsCurvAbove (bsCRRAU σ β) (bsCRRAPrice σ β ωy ωo) ωy ωo
      (σ * (m / 2) ^ (-σ - 1) * (1 + (m ^ (-σ)) ^ 2 / (β * (M ^ (-σ)) ^ 2)) / (2 * M ^ (-σ)))
      (m / 2) := by
  intro t x y hx1 hx2 hy1 hy2 hineq
  set c := ωy t with hc
  set d := ωo (t + 1) with hd
  have hcm : m ≤ c := (hωy t).1
  have hc0 : 0 < c := hm.trans_le hcm
  have hd0 : 0 < d := hm.trans_le (hωo (t + 1)).1
  have hM : 0 < M := hc0.trans_le (hωy t).2
  have hmM : m ≤ M := hcm.trans (hωy t).2
  set K := σ * (m / 2) ^ (-σ - 1) with hK
  have hK0 : 0 < K := by positivity
  set Gc := c ^ (-σ) with hGc
  set G := d ^ (-σ) with hG
  have hGc0 : 0 < Gc := Real.rpow_pos_of_pos hc0 _
  have hG0 : 0 < G := Real.rpow_pos_of_pos hd0 _
  set gL := M ^ (-σ) with hgL
  set gU := m ^ (-σ) with hgU
  have hgL0 : 0 < gL := Real.rpow_pos_of_pos hM _
  have hgLc : gL ≤ Gc := Real.rpow_le_rpow_of_nonpos hc0 (hωy t).2 (by linarith)
  have hgLd : gL ≤ G := Real.rpow_le_rpow_of_nonpos hd0 (hωo (t + 1)).2 (by linarith)
  have hgUc : Gc ≤ gU := Real.rpow_le_rpow_of_nonpos hm hcm (by linarith)
  set q := bsCRRAPrice σ β ωy ωo t with hq
  have hqG : Gc * q = β * G := by
    have hne : ωy t ^ (-σ) ≠ 0 := hGc0.ne'
    simp only [hq, bsCRRAPrice, hGc, hG, hc, hd]; field_simp
  have hq0 : 0 < q := by
    have : 0 < Gc * q := by rw [hqG]; positivity
    exact pos_of_mul_pos_right this hGc0.le
  have hIx : x ∈ Set.Icc (m / 2) (2 * M) := ⟨by linarith, by linarith [(hωy t).2]⟩
  have hIc : c ∈ Set.Icc (m / 2) (2 * M) := ⟨by linarith, by linarith [(hωy t).2]⟩
  have hId : d ∈ Set.Icc (m / 2) (2 * M) := ⟨by linarith [(hωo (t + 1)).1],
    by linarith [(hωo (t + 1)).2]⟩
  have hIy : y ∈ Set.Icc (m / 2) (2 * M) := ⟨by linarith [(hωo (t + 1)).1],
    by linarith [(hωo (t + 1)).2]⟩
  have hd' : ∀ r ∈ Set.Icc (m / 2) (2 * M), HasDerivAt (bsCRRA σ) (r ^ (-σ)) r :=
    fun r hr => bs_crra_hasDerivAt hσ1 ((half_pos hm).trans_le hr.1)
  have hg' : ∀ s ∈ Set.Icc (m / 2) (2 * M), ∀ t' ∈ Set.Icc (m / 2) (2 * M), s ≤ t' →
      s ^ (-σ) - t' ^ (-σ) ≤ K * (t' - s) :=
    fun s hs t' _ hst => bs_rpow_gap_upper hσ (half_pos hm) hs.1 hst
  have h1 := bs_quad_lower hd' hg' hIc hIx
  have h2 := bs_quad_lower hd' hg' hId hIy
  set f := y - d with hf
  set v := q * f with hv
  set R := x - c + v with hR
  have hf0 : 0 ≤ f := by rw [hf]; linarith
  have hv0 : 0 ≤ v := mul_nonneg hq0.le hf0
  set A := K * (1 + gU ^ 2 / (β * gL ^ 2)) / (2 * gL) with hA
  have hA0 : 0 ≤ A := by positivity
  have hR0 : A * v ^ 2 ≤ R := hineq
  have hxc : (x - c) ^ 2 ≤ v ^ 2 := by
    have : 0 ≤ A * v ^ 2 := by positivity
    have h5 : c - x ≤ v := by linarith
    nlinarith
  have hbf : β * f ^ 2 ≤ gU ^ 2 / (β * gL ^ 2) * v ^ 2 := by
    have e : β * f ^ 2 = Gc ^ 2 / (β * G ^ 2) * v ^ 2 := by
      have hq' : q = β * G / Gc := by rw [← hqG]; field_simp
      rw [hv, hq']
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg v)
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ hGc0.le hgUc 2) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hgL0.le hgLd 2) hβ.le)
  have hgain : K / 2 * ((x - c) ^ 2 + β * f ^ 2) ≤ Gc * R := by
    have e1 : K / 2 * (1 + gU ^ 2 / (β * gL ^ 2)) = gL * A := by
      rw [hA]; field_simp
    have h6 : K / 2 * ((x - c) ^ 2 + β * f ^ 2) ≤ K / 2 * ((1 + gU ^ 2 / (β * gL ^ 2)) * v ^ 2) :=
      mul_le_mul_of_nonneg_left (by rw [add_mul, one_mul]; exact add_le_add hxc hbf)
        (by positivity)
    have h7 : gL * (A * v ^ 2) ≤ Gc * (A * v ^ 2) :=
      mul_le_mul_of_nonneg_right hgLc (by positivity)
    have h8 : Gc * (A * v ^ 2) ≤ Gc * R := mul_le_mul_of_nonneg_left hR0 hGc0.le
    have e2 : K / 2 * ((1 + gU ^ 2 / (β * gL ^ 2)) * v ^ 2) = gL * (A * v ^ 2) := by
      rw [← mul_assoc, ← mul_assoc, e1]
    linarith
  have e3 : Gc * R = Gc * (x - c) + β * G * f := by rw [hR, hv, mul_add, ← mul_assoc, hqG]
  simp only [bsCRRAU]
  linarith [mul_le_mul_of_nonneg_left h2 hβ.le]

/-- **Balasko–Shell for the CRRA economy** (AKMM, pp. 178–179). With
`Uₜ = u(c_y) + βu(c_o)`, `u(c) = c^{1−σ}/(1 − σ)`, `σ > 0`, `σ ≠ 1`, `β > 0`, and endowments in
`[m, M]`, `0 < m`, the autarkic equilibrium is Pareto optimal iff `Σ 1/pₜ = ∞`. -/
theorem bs_crra {σ β m M : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hm : 0 < m)
    {ωy ωo : ℕ → ℝ} (hωy : ∀ t, m ≤ ωy t ∧ ωy t ≤ M) (hωo : ∀ t, m ≤ ωo t ∧ ωo t ≤ M) :
    ogParetoOptimal (bsCRRAU σ β) ωy ωo ωy ωo ↔
      ¬ Summable fun t => 1 / seqPrice (bsCRRAPrice σ β ωy ωo) t := by
  have hy0 : ∀ t, 0 < ωy t := fun t => hm.trans_le (hωy t).1
  have ho0 : ∀ t, 0 < ωo t := fun t => hm.trans_le (hωo t).1
  have hM : 0 < M := (hy0 0).trans_le (hωy 0).2
  have hmσ : 0 < m ^ (-σ) := Real.rpow_pos_of_pos hm _
  have hMσ : 0 < M ^ (-σ) := Real.rpow_pos_of_pos hM _
  have hq : ∀ t, 0 < bsCRRAPrice σ β ωy ωo t := fun t => by
    have := Real.rpow_pos_of_pos (ho0 (t + 1)) (-σ)
    have := Real.rpow_pos_of_pos (hy0 t) (-σ)
    simp only [bsCRRAPrice]; positivity
  exact bs_balasko_shell (bs_crra_mono hσ hσ1) (by positivity) (by positivity) (half_pos hm) hq
    (bs_crra_equilibrium hσ hσ1 hβ hy0 ho0) (bs_crra_curv_below hσ hσ1 hβ hm hωy hωo)
    (fun t => by linarith [(hωy t).1]) (bs_crra_curv_above hσ hσ1 hβ hm hωy hωo)

end AKMM.Welfare
