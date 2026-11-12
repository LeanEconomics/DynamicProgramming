/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMMoney.GovernmentBudget
import AKMMMoney.TransactionCosts
import Monetarism.UnpleasantArithmetic
import TwoPeriodModel.TwoPeriod
import Mathlib.Topology.Order.Compact

/-!
# Seigniorage, unpleasant arithmetic, fiscal backstops and the fiscal theory of the price level

AKMM, §17.3.3, pp. 520–523.

* **The seigniorage Laffer curve** (p. 521). `lf_interior_max`: if the money demand `f` is
  continuous and positive and `f(i)i → 0` as `i → ∞`, arbitrage seigniorage `f(i)i/(1 + i)` has
  a maximum at some `i* > 0`. `lf_counterexample`: "`f` strictly decreasing" alone is not enough
  (`f(i) = 1 + 1/(1 + i)` gives strictly increasing revenue with no maximum);
  `lf_tc_no_max`: neither does the chapter's own transactions-cost demand (17.29).
* **Unpleasant arithmetic** (p. 521). `ua_stationary`: on the benign side of the Laffer curve a
  higher `d̄` requires a higher `ī` and higher inflation. `ua_dynamic`: with fixed surpluses,
  lower seigniorage now means higher seigniorage later (Cochrane's `unpleasant_tradeoff`).
* **A fiscal backstop** (p. 522). `fb_backstop`: every path along which real balances vanish
  eventually breaches the ceiling `P̃₀γᵗ`; `fb_stationary`: the stationary path never does.
* **The fiscal theory** (pp. 523). `eq_17_45`, `eq_17_46`, `ftpl_price_level`: under the tax rule
  (17.45) the present-value budget pins `(1 + i_{−1})B₀/P₀ = (τ̃ − g̃)/(1 − β)`;
  `ftpl_unique` (Cochrane's `lastDay_existsUnique`): with `B₀ > 0` and `τ̃ > g̃`, `P₀` exists and
  is unique; `ftpl_none` (Cochrane's `lastDay_none`): with `τ̃ ≤ g̃` there is no positive `P₀`.

**Departures.** The Laffer maximum needs a hypothesis such as `f(i)i → 0`; the FTPL needs
`τ̃ > g̃` besides `B₀ > 0`.
-/

open Filter Topology

namespace AKMM.Money

/-- AKMM, p. 521: the increasing part `i/(1 + i)` of seigniorage starts at `0`, is strictly
increasing and bounded above by `1`. -/
theorem lf_increasing_part :
    (0 : ℝ) / (1 + 0) = 0 ∧ StrictMonoOn (fun i : ℝ => i / (1 + i)) (Set.Ici 0) ∧
      ∀ i : ℝ, 0 ≤ i → i / (1 + i) < 1 := by
  refine ⟨by norm_num, fun a ha b hb hab => ?_, fun i hi => by
    rw [div_lt_one (by linarith)]; linarith⟩
  have ha' : (0 : ℝ) ≤ a := ha
  simp only
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- **AKMM, p. 521: the seigniorage Laffer curve.** If `f` is continuous on `[0, ∞)`, positive on
`(0, ∞)` and `f(i)i → 0` as `i → ∞`, then seigniorage `f(i)i/(1 + i)` attains its maximum over
`i ≥ 0` at some `i* > 0`. -/
theorem lf_interior_max {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0))
    (hpos : ∀ i, 0 < i → 0 < f i) (hlim : Tendsto (fun i => f i * i) atTop (𝓝 0)) :
    ∃ i0, 0 < i0 ∧ IsMaxOn (fun i => f i * (i / (1 + i))) (Set.Ici 0) i0 := by
  set S := fun i : ℝ => f i * (i / (1 + i)) with hSdef
  have hv : 0 < S 1 := by simp only [hSdef]; have := hpos 1 one_pos; positivity
  have hSle : ∀ i, 0 < i → S i ≤ f i * i := fun i hi => by
    simp only [hSdef]
    apply mul_le_mul_of_nonneg_left _ (hpos i hi).le
    rw [div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨R, hR⟩ := (eventually_atTop.1 (hlim (gt_mem_nhds hv)))
  set R' := max R 1
  have hScont : ContinuousOn S (Set.Icc 0 R') := by
    apply (hcont.mono Set.Icc_subset_Ici_self).mul
    exact (continuousOn_id.div (continuousOn_const.add continuousOn_id) fun x hx => by
      have : (0 : ℝ) ≤ x := hx.1; positivity)
  obtain ⟨i0, hi0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (le_trans zero_le_one (le_max_right R 1))) hScont
  have h1 : S 1 ≤ S i0 := hmax ⟨zero_le_one, le_max_right R 1⟩
  have hi0pos : 0 < i0 := by
    rcases hi0.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at h1; simp [hSdef] at h1; nlinarith [hpos 1 one_pos]
  refine ⟨i0, hi0pos, fun i hi => ?_⟩
  have hi' : (0 : ℝ) ≤ i := hi
  by_cases hiR : i ≤ R'
  · exact hmax ⟨hi', hiR⟩
  · have hiR' : R ≤ i := le_trans (le_max_left R 1) (le_of_not_ge hiR)
    have hipos : 0 < i := lt_of_lt_of_le one_pos (le_trans (le_max_right R 1) (le_of_not_ge hiR))
    have := hR i hiR'
    exact le_trans (hSle i hipos) (le_trans this.le h1)

/-- AKMM, p. 521: "`f` strictly decreasing" is not enough. With `f(i) = 1 + 1/(1 + i)`
(positive, strictly decreasing) seigniorage equals `1 − 1/(1 + i)²`, which is strictly
increasing on `[0, ∞)`: there is no maximum. -/
theorem lf_counterexample :
    StrictAntiOn (fun i : ℝ => 1 + 1 / (1 + i)) (Set.Ici 0) ∧
      (∀ i : ℝ, 0 ≤ i → 0 < 1 + 1 / (1 + i)) ∧
      StrictMonoOn (fun i : ℝ => (1 + 1 / (1 + i)) * (i / (1 + i))) (Set.Ici 0) ∧
      ¬ ∃ i0 : ℝ, 0 ≤ i0 ∧
        IsMaxOn (fun i : ℝ => (1 + 1 / (1 + i)) * (i / (1 + i))) (Set.Ici 0) i0 := by
  have hform : ∀ i : ℝ, 0 ≤ i → (1 + 1 / (1 + i)) * (i / (1 + i)) = 1 - 1 / (1 + i) ^ 2 :=
    fun i hi => by have : (1 + i) ≠ 0 := by linarith
                   field_simp; ring
  have hmono : StrictMonoOn (fun i : ℝ => (1 + 1 / (1 + i)) * (i / (1 + i))) (Set.Ici 0) := by
    intro a ha b hb hab
    have ha' : (0 : ℝ) ≤ a := ha
    have hb' : (0 : ℝ) ≤ b := hb
    simp only
    rw [hform a ha', hform b hb']
    have : 1 / (1 + b) ^ 2 < 1 / (1 + a) ^ 2 := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    linarith
  refine ⟨fun a ha b hb hab => ?_, fun i hi => by positivity, hmono, ?_⟩
  · have ha' : (0 : ℝ) ≤ a := ha
    simp only
    have : 1 / (1 + b) < 1 / (1 + a) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
    linarith
  · rintro ⟨i0, h, hi0⟩
    have hle := isMaxOn_iff.1 hi0
    have h1 := hle (i0 + 1) (show i0 + 1 ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
    have h2 := hmono (show i0 ∈ Set.Ici (0 : ℝ) from h)
      (show i0 + 1 ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) (by linarith)
    linarith

/-- AKMM, p. 521, with (17.29): for the chapter's transactions-cost demand
`m/c = ((1/(κη))s)^{−1/(1+η)}`, `s = i/(1 + i)`, seigniorage per unit of consumption
`(m/c)s` is strictly increasing in `s ∈ (0, 1)`: it has no interior Laffer maximum. -/
theorem lf_tc_no_max {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    StrictMonoOn (fun s => tcDemand κ η 1 s * s) (Set.Ioi 0) := by
  have hform : ∀ s : ℝ, 0 < s →
      tcDemand κ η 1 s * s = (1 / (κ * η)) ^ (-(1 / (1 + η))) * s ^ (η / (1 + η)) := by
    intro s hs
    unfold tcDemand
    rw [one_mul, Real.mul_rpow (by positivity) hs.le, mul_assoc]
    congr 1
    rw [show η / (1 + η) = -(1 / (1 + η)) + 1 by field_simp; ring,
      Real.rpow_add hs, Real.rpow_one]
  intro a ha b hb hab
  dsimp only
  rw [hform a ha, hform b hb]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  exact Real.rpow_lt_rpow (le_of_lt ha) hab (by positivity)

/-- **AKMM, p. 521: unpleasant arithmetic (stationary version).** Fix `ḡ, τ̄, r̄ > 0, c̄ > 0`. If
seigniorage `S` is strictly increasing on a set `I` (the benign side of the Laffer curve) and
`(d̄₁, ī₁)`, `(d̄₂, ī₂)` both satisfy the stationary budget with `ī₁, ī₂ ∈ I`, then `d̄₁ < d̄₂`
forces `ī₁ < ī₂` and, by the Fisher equation, higher inflation. -/
theorem ua_stationary {S : ℝ → ℝ} {I : Set ℝ} (hS : StrictMonoOn S I)
    {gb τb rb cb d1 d2 i1 i2 : ℝ} (hr : 0 < rb) (hc : 0 < cb) (hi1 : i1 ∈ I) (hi2 : i2 ∈ I)
    (h1 : gb + rb / (1 + rb) * d1 = τb + cb * S i1)
    (h2 : gb + rb / (1 + rb) * d2 = τb + cb * S i2) (hd : d1 < d2) :
    i1 < i2 ∧ (1 + i1) / (1 + rb) < (1 + i2) / (1 + rb) := by
  have hk : 0 < rb / (1 + rb) := by positivity
  have : cb * S i1 < cb * S i2 := by nlinarith
  have hS12 : S i1 < S i2 := lt_of_mul_lt_mul_left this hc.le
  have hi : i1 < i2 := (hS.lt_iff_lt hi1 hi2).1 hS12
  exact ⟨hi, div_lt_div_of_pos_right (by linarith) (by linarith)⟩

/-- AKMM, p. 521 (Sargent–Wallace, dynamic version, via Cochrane's `unpleasant_tradeoff`): with
`q ≡ β`, (17.43) reads `∑ βᵗ(s_t + σ_t) = b̂₀` (primary surpluses `s`, seigniorage `σ`). If the
surpluses are fixed with present value `S` and the date-0 seigniorage is cut, `σ′₀ < σ₀`, then
seigniorage must be higher at some later date. -/
theorem ua_dynamic {β b0 S : ℝ} (hβ : 0 < β) {s σ σ' : ℕ → ℝ}
    (hs : HasSum (fun j => β ^ j * s j) S) (hb : HasSum (fun j => β ^ j * (s j + σ j)) b0)
    (hb' : HasSum (fun j => β ^ j * (s j + σ' j)) b0) (h0 : σ' 0 < σ 0) :
    ∃ j, 0 < j ∧ σ j < σ' j :=
  Cochrane.Monetarism.UnpleasantArithmetic.unpleasant_tradeoff hβ hs hb hb' h0

/-- AKMM, p. 522: a fiscal backstop. With money growth `M_t = M₀γᵗ` and real balances `m_t → 0`
(the hyperinflation paths), the price level `P_t = M_t/m_t` eventually exceeds any ceiling
`P̃₀γᵗ`: the promise to buy money at that ceiling rules these paths out. -/
theorem fb_backstop {M0 γ Pt0 : ℝ} {m : ℕ → ℝ} (hM0 : 0 < M0) (hγ : 0 < γ) (hP : 0 < Pt0)
    (hm : ∀ t, 0 < m t) (hlim : Tendsto m atTop (𝓝 0)) :
    ∃ t, Pt0 * γ ^ t < M0 * γ ^ t / m t := by
  obtain ⟨t, ht⟩ := (hlim.eventually (gt_mem_nhds (div_pos hM0 hP))).exists
  refine ⟨t, ?_⟩
  rw [lt_div_iff₀ (hm t)]
  have hg : 0 < γ ^ t := pow_pos hγ t
  rw [lt_div_iff₀ hP] at ht
  nlinarith

/-- AKMM, p. 522: the stationary path `m_t = m̄` respects every ceiling `P̃₀ ≥ M₀/m̄`: the
critical value grows at the money growth rate, as the stationary price level does. -/
theorem fb_stationary {M0 γ Pt0 mb : ℝ} (hγ : 0 < γ) (hP : M0 / mb ≤ Pt0)
    (t : ℕ) : M0 * γ ^ t / mb ≤ Pt0 * γ ^ t := by
  rw [mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right hP (pow_pos hγ t).le

/-- **AKMM, (17.45)**, p. 523: under the tax rule `τ_t − τ̃ = −(M_{t+1} − M_t)/P_t` and
`g_t = g̃` the primary surplus plus seigniorage is constant, `τ̃ − g̃`. -/
theorem eq_17_45 {τt τtil gt gtil st : ℝ} (hrule : τt - τtil = -st) (hg : gt = gtil) :
    τt - gt + st = τtil - gtil := by
  rw [hg]; linarith

/-- **AKMM, (17.46)**, p. 523: with `q_{0,t} = βᵗ`, `0 ≤ β < 1`, the present value of the
constant `τ̃ − g̃` is `(τ̃ − g̃)/(1 − β)`. -/
theorem eq_17_46 {β τtil gtil : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun t : ℕ => β ^ t * (τtil - gtil)) ((τtil - gtil) / (1 - β)) := by
  have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (τtil - gtil)
  simpa [div_eq_inv_mul, mul_comm] using this

/-- AKMM, (17.43) with (17.45)–(17.46), p. 523: if the real flow budget holds at every date with
`q_t = β` (the CIA peg), the discounted terminal liabilities vanish and taxes follow (17.45),
then the initial real liabilities equal the present value of surpluses:
`(1 + i_{−1})B₀/P₀ = (τ̃ − g̃)/(1 − β)`. -/
theorem ftpl_price_level {β τtil gtil : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {g τ s bh : ℕ → ℝ}
    (h : ∀ t, bh t = (τ t - g t + s t) + β * bh (t + 1))
    (htvc : Tendsto (fun T => β ^ T * bh T) atTop (𝓝 0))
    (hrule : ∀ t, τ t - τtil = -s t) (hg : ∀ t, g t = gtil) :
    bh 0 = (τtil - gtil) / (1 - β) := by
  have hcomb : ∀ t, τ t - g t + s t = τtil - gtil := fun t => eq_17_45 (hrule t) (hg t)
  have hx : ∀ t, bh t = (τtil - gtil) + β * bh (t + 1) := fun t => by rw [h t, hcomb t]
  have hit := fun T => gb_iterate (q := fun _ => β) (x := fun _ => τtil - gtil) hx T
  simp only [Finset.prod_const, Finset.card_range] at hit
  have h2 := (eq_17_46 hβ0 hβ1 (τtil := τtil) (gtil := gtil)).tendsto_sum_nat.add htvc
  rw [add_zero] at h2
  have h3 : Tendsto (fun _ : ℕ => bh 0) atTop (𝓝 ((τtil - gtil) / (1 - β))) :=
    h2.congr fun T => (hit T).symm
  exact tendsto_nhds_unique tendsto_const_nhds h3

/-- AKMM, p. 523 (via Cochrane's `lastDay_existsUnique`): with `B₀ > 0`, `1 + i_{−1} > 0`,
`0 < β < 1` and `τ̃ > g̃`, there is exactly one positive `P₀` with
`(1 + i_{−1})B₀/P₀ = (τ̃ − g̃)/(1 − β)`. -/
theorem ftpl_unique {β τtil gtil B0 im1 : ℝ} (hβ1 : β < 1) (hB : 0 < B0) (hi : 0 < 1 + im1)
    (hτ : gtil < τtil) :
    ∃! P0 : ℝ, 0 < P0 ∧ (1 + im1) * B0 / P0 = (τtil - gtil) / (1 - β) :=
  Cochrane.TwoPeriodModel.TwoPeriod.lastDay_existsUnique (mul_pos hi hB)
    (div_pos (by linarith) (by linarith))

/-- AKMM, p. 523 (added hypothesis, via Cochrane's `lastDay_none`): with `B₀ > 0` but
`τ̃ ≤ g̃` no positive price level satisfies (17.46). -/
theorem ftpl_none {β τtil gtil B0 im1 : ℝ} (hβ1 : β < 1) (hB : 0 < B0) (hi : 0 < 1 + im1)
    (hτ : τtil ≤ gtil) :
    ¬ ∃ P0 : ℝ, 0 < P0 ∧ (1 + im1) * B0 / P0 = (τtil - gtil) / (1 - β) :=
  Cochrane.TwoPeriodModel.TwoPeriod.lastDay_none (mul_pos hi hB)
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

end AKMM.Money
