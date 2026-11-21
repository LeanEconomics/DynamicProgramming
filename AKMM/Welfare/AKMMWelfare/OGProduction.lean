/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMWelfare.OGEndowment
import OverlappingGenerations.OPEfficiency

/-!
# Overlapping generations: intertemporal production and dynamic efficiency

AKMM, §6.4.2, pp. 180–183, and Appendix 6.A, pp. 838–839.

* **Storage** (pp. 180–181). With a storage technology of gross return `χ`, the young's problem
  is the bond problem at `q = 1/χ` (`storage_saving`): saving `(ω_y − ω_o/χ)/2`, positive iff
  `χω_y > ω_o` (for `(3, 1)`, `χ > 1/3`). The equilibrium allocation (`stEqAlloc`) is Pareto
  optimal iff `χ > 1`: for `χ ≤ 1` a pay-as-you-go transfer of the stored amount dominates it
  (`storage_not_optimal`, at `χ = 1` the book's social-security argument), and for `χ > 1` the
  summed budgets at `pₜ = χ^{−t}` rule out improvements (`storage_optimal`); together
  `storage_optimal_iff`.
* **The Diamond economy** (pp. 181–182): the law of motion
  `k_{t+1} = h(F₂(kₜ), F₁(k_{t+1}), F₂(k_{t+1}))` (`diamond_law_of_motion`) and
  `∏_{s=1}^t R_s = 1/pₜ` (`theorem_6_2_prices`).
* **Theorem 6.2** (p. 182), dynamic efficiency of a feasible path `k_{t+1} = fₜ(kₜ) − cₜ`
  (`dePath`, `deEfficient`), with the assumptions of fn. 12 (returns `Rₜ` bounded above and away
  from zero, curvature bounded, stated as quadratic bounds on `fₜ` around `kₜ`): if
  `Σₜ ∏_{s=1}^t R_s = ∞` the path is efficient (`theorem_6_2_efficient`); if the sum is finite it
  is inefficient (`theorem_6_2_inefficient`, which also needs `kₜ` bounded away from zero);
  together `theorem_6_2`. Concrete instances satisfy all hypotheses
  (`theorem_6_2_instance_efficient`, `theorem_6_2_instance_inefficient`).
* **Theorem .5** (Appendix 6.A): a steady state `k⋆` is efficient iff `R⋆ = f′(k⋆) ≥ 1`
  (`theorem_A5`, from `theorem_A5_inefficient`, which needs only the derivative, and
  `theorem_A5_efficient`, by the book's growing-deficit argument made rigorous with strict
  concavity); at a steady state the criterion of Theorem 6.2 is `R⋆ ≥ 1` (`theorem_A5_cass`, from
  Miao's `op_cass_steady_state`).

**Corrections.** (i) p. 181: the storage problem is the bond problem at `qₜ = 1/χ`, not `qₜ = χ`
(`storage_printed_counterexample`). (ii) p. 838: `f(k)` must be `F(k, ω_y + ω_o) + (1 − δ)k`,
not `F(k, ω_y + ω_o) + 1 − δ`: with the printed `f` the criterion `f′(k⋆) ≥ 1` misclassifies
(`appendix_6A_printed_f`). (iii) p. 839: the book's limit `c_∞ = f(k⋆ − ε_∞) − (k⋆ − ε_∞)` has
the wrong sign (`ε₂ = k₂ − k⋆ < 0`) and the unbounded growth of the deficits is only sketched;
`theorem_A5_efficient` proves it. (iv) p. 838: part (i) needs no concavity, only `f′(k⋆) < 1`.
-/

namespace AKMM.Welfare

open Filter Topology AKMM.CompetitiveEquilibrium Miao.OverlappingGenerations

/-! ### Storage -/

/-- **AKMM, p. 181 (corrected): the storage problem.** Storing `s` when young gives
`(ω_y − s, ω_o + χs)`, which is the bond plan `a = χs` at the price `q = 1/χ`. With `χ, ω_y,
ω_o > 0`, the optimal plan is `s = (ω_y − ω_o/χ)/2` (equations (6.5)–(6.6) at `q = 1/χ`), with
`c_y = (ω_y + ω_o/χ)/2`, `c_o = (χω_y + ω_o)/2`; storage is positive iff `χω_y > ω_o`. -/
theorem storage_saving {χ ωy ωo s : ℝ} (hχ : 0 < χ) (hy : 0 < ωy) (ho : 0 < ωo) :
    (OGSavingOpt Real.log 1 (1 / χ) ωy ωo (χ * s) ↔ s = (ωy - ωo / χ) / 2) ∧
      ωy - (ωy - ωo / χ) / 2 = (ωy + ωo / χ) / 2 ∧
      ωo + χ * ((ωy - ωo / χ) / 2) = (χ * ωy + ωo) / 2 ∧
      (0 < (ωy - ωo / χ) / 2 ↔ ωo < χ * ωy) := by
  refine ⟨?_, by ring, by field_simp; ring, ?_⟩
  · rw [eq_6_5_6_6 (one_div_pos.2 hχ) hy ho]
    have e : (ωy - 1 / χ * ωo) / (2 * (1 / χ)) = χ * ((ωy - ωo / χ) / 2) := by
      field_simp
    rw [e]
    constructor
    · intro h; exact mul_left_cancel₀ hχ.ne' h
    · intro h; rw [h]
  · rw [div_pos_iff_of_pos_right two_pos, sub_pos, div_lt_iff₀ hχ, mul_comm]

/-- **AKMM, p. 181: the printed price `qₜ = χ` gives the wrong allocation.** In the `(3, 1)`
economy with `χ = 2`, (6.5)–(6.6) at the printed `q = 2` give `(c_y, c_o) = (5/2, 5/4)`, which is
not on the storage budget line (storing `1/2` returns `ω_o + 1 = 2`), while the correct optimum
at `q = 1/χ` is `(7/4, 7/2)`, with strictly higher utility. -/
theorem storage_printed_counterexample :
    (3 + 2 * 1) / 2 = (5 / 2 : ℝ) ∧ (3 / 2 + 1) / 2 = (5 / 4 : ℝ) ∧
      (1 : ℝ) + 2 * (3 - 5 / 2) ≠ 5 / 4 ∧
      OGSavingOpt Real.log 1 (1 / 2) 3 1 (2 * (5 / 4)) ∧
      Real.log (5 / 2) + Real.log (5 / 4) < Real.log (7 / 4) + Real.log (7 / 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [(storage_saving (by norm_num : (0 : ℝ) < 2) (by norm_num) one_pos).1]
    norm_num
  · rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    exact Real.log_lt_log (by norm_num) (by norm_num)

/-- A feasible allocation of the storage economy (AKMM, p. 180): positive consumption,
nonnegative storage `sₜ` by the young at `t` (returning `χsₜ` at `t + 1`), and
`c_{y,t} + c_{o,t} + sₜ ≤ ω_y + ω_o + χs_{t−1}` (`s_{−1} = 0`). -/
def stFeasible (ωy ωo χ : ℝ) (cy co s : ℕ → ℝ) : Prop :=
  (∀ t, 0 < cy t ∧ 0 < co t ∧ 0 ≤ s t) ∧ cy 0 + co 0 + s 0 ≤ ωy + ωo ∧
    ∀ t, cy (t + 1) + co (t + 1) + s (t + 1) ≤ ωy + ωo + χ * s t

/-- Pareto optimality in the storage economy (log utility for every generation). -/
def stParetoOptimal (ωy ωo χ : ℝ) (cy co s : ℕ → ℝ) : Prop :=
  stFeasible ωy ωo χ cy co s ∧
    ¬ ∃ cy' co' s', stFeasible ωy ωo χ cy' co' s' ∧ ogDominates ogLogU cy co cy' co'

/-- The equilibrium allocation of the storage economy: every young stores
`s⋆ = (ω_y − ω_o/χ)/2` and consumes `(ω_y + ω_o/χ)/2`; the old consume `(χω_y + ω_o)/2`, except the
initial old, who consume `ω_o`. -/
noncomputable def stEqAlloc (ωy ωo χ : ℝ) : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) :=
  (fun _ => (ωy + ωo / χ) / 2, fun t => if t = 0 then ωo else (χ * ωy + ωo) / 2,
    fun _ => (ωy - ωo / χ) / 2)

/-- The equilibrium allocation is feasible when storage is positive. -/
theorem stEqAlloc_feasible {ωy ωo χ : ℝ} (hχ : 0 < χ) (hy : 0 < ωy) (ho : 0 < ωo)
    (hs : ωo < χ * ωy) :
    stFeasible ωy ωo χ (stEqAlloc ωy ωo χ).1 (stEqAlloc ωy ωo χ).2.1 (stEqAlloc ωy ωo χ).2.2 := by
  have hs' := ((storage_saving hχ hy ho (s := 0)).2.2.2).2 hs
  refine ⟨fun t => ⟨by simp only [stEqAlloc]; positivity, ?_, hs'.le⟩, ?_, fun t => ?_⟩
  · simp only [stEqAlloc]; split_ifs <;> positivity
  · simp only [stEqAlloc, ↓reduceIte]; linarith
  · simp only [stEqAlloc, Nat.add_one_ne_zero, ↓reduceIte]
    field_simp
    linarith

/-- **AKMM, p. 181: storage with `χ ≤ 1` is inefficient.** When storage is positive and `χ ≤ 1`,
the young can instead give the amount `s⋆` to the current old (a pay-as-you-go scheme, no
storage): every generation's old-age consumption becomes `ω_o + s⋆ ≥ ω_o + χs⋆`, and the initial
old get `ω_o + s⋆ > ω_o`. At `χ = 1` and `(3, 1)` this is the social-security allocation
`(2, 2)` with the initial old at `2` instead of `1`. -/
theorem storage_not_optimal {ωy ωo χ : ℝ} (hχ : 0 < χ) (hy : 0 < ωy) (ho : 0 < ωo)
    (hs : ωo < χ * ωy) (hχ1 : χ ≤ 1) :
    ¬ stParetoOptimal ωy ωo χ (stEqAlloc ωy ωo χ).1 (stEqAlloc ωy ωo χ).2.1
      (stEqAlloc ωy ωo χ).2.2 := by
  rintro ⟨-, hno⟩
  set ss := (ωy - ωo / χ) / 2 with hss
  have hs' : 0 < ss := ((storage_saving hχ hy ho (s := 0)).2.2.2).2 hs
  have hcy : 0 < (ωy + ωo / χ) / 2 := by positivity
  have hco : (χ * ωy + ωo) / 2 ≤ ωo + ss := by
    have e : (χ * ωy + ωo) / 2 = ωo + χ * ss := by rw [hss]; field_simp; ring
    rw [e]; nlinarith
  refine hno ⟨fun _ => (ωy + ωo / χ) / 2, fun _ => ωo + ss, fun _ => 0,
    ⟨fun _ => ⟨hcy, by linarith, le_rfl⟩, ?_, fun _ => ?_⟩, ?_, fun t => ?_, Or.inl ?_⟩
  · rw [hss]; field_simp; linarith
  · rw [hss]; field_simp; linarith
  · simp only [stEqAlloc, ↓reduceIte]; linarith
  · simp only [stEqAlloc, ogLogU, Nat.add_one_ne_zero, ↓reduceIte]
    linarith [Real.log_le_log (by positivity) hco]
  · simp only [stEqAlloc, ↓reduceIte]; linarith

/-- **AKMM, p. 181: storage with `χ > 1` is efficient.** When `χ > 1` and storage is positive,
the equilibrium allocation is Pareto optimal: at the prices `pₜ = χ^{−t}` every generation's
alternative must cost at least its wealth, and the summed budgets leave a surplus of at most
`χ^{−N}ω_y → 0`. -/
theorem storage_optimal {ωy ωo χ : ℝ} (hχ : 1 < χ) (hy : 0 < ωy) (ho : 0 < ωo)
    (hs : ωo < χ * ωy) :
    stParetoOptimal ωy ωo χ (stEqAlloc ωy ωo χ).1 (stEqAlloc ωy ωo χ).2.1
      (stEqAlloc ωy ωo χ).2.2 := by
  have hχ0 : 0 < χ := by linarith
  refine ⟨stEqAlloc_feasible hχ0 hy ho hs, ?_⟩
  rintro ⟨cy', co', s', ⟨hpos, h0, hres⟩, hold, hle, hstrict⟩
  set W := ωy + ωo / χ with hW
  set cs := (ωy + ωo / χ) / 2 with hcs
  set os := (χ * ωy + ωo) / 2 with hos
  have hcs0 : 0 < cs := by positivity
  have hos0 : 0 < os := by positivity
  -- the generation's optimum on the budget `x + y/χ ≤ W`
  have hopt : ∀ x y, 0 < x → 0 < y → x + y / χ ≤ W →
      Real.log x + Real.log y ≤ Real.log cs + Real.log os := by
    intro x y hx hy' hb
    have hsv := ((storage_saving hχ0 hy ho (s := (ωy - ωo / χ) / 2)).1).2 rfl
    obtain ⟨_, _, hmax⟩ := hsv
    have h1 : x ≤ ωy - 1 / χ * (y - ωo) := by
      have : 1 / χ * (y - ωo) = y / χ - ωo / χ := by ring
      rw [hW] at hb; linarith
    have := hmax (y - ωo) (by linarith) (by linarith)
    have e1 : ωy - 1 / χ * (χ * ((ωy - ωo / χ) / 2)) = cs := by rw [hcs]; field_simp; ring
    have e2 : ωo + χ * ((ωy - ωo / χ) / 2) = os := by rw [hos]; field_simp; ring
    rw [e1, e2, one_mul, one_mul, add_sub_cancel] at this
    linarith [Real.log_le_log hx h1]
  have hgenU : ∀ t, ogLogU t ((stEqAlloc ωy ωo χ).1 t) ((stEqAlloc ωy ωo χ).2.1 (t + 1)) =
      Real.log cs + Real.log os := by
    intro t; simp [stEqAlloc, ogLogU, hcs, hos]
  -- costs at the prices `χ^{−t}`
  have hcost : ∀ t, W ≤ cy' t + co' (t + 1) / χ := by
    intro t
    by_contra hcon
    push Not at hcon
    set x' := W - co' (t + 1) / χ
    have hx' : cy' t < x' := by simp only [x']; linarith
    have := hopt x' (co' (t + 1)) (by linarith [(hpos t).1]) (hpos (t + 1)).2.1
      (by simp only [x']; linarith)
    have h2 := hle t
    rw [hgenU] at h2
    simp only [ogLogU] at h2
    linarith [Real.log_lt_log (hpos t).1 hx']
  have hcost_strict : ∀ t, Real.log cs + Real.log os < ogLogU t (cy' t) (co' (t + 1)) →
      W < cy' t + co' (t + 1) / χ := by
    intro t ht
    by_contra hcon
    push Not at hcon
    have := hopt _ _ (hpos t).1 (hpos (t + 1)).2.1 hcon
    simp only [ogLogU] at ht
    linarith
  set ρ := χ⁻¹ with hρ
  have hρ0 : 0 < ρ := inv_pos.2 hχ0
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ hχ
  set g : ℕ → ℝ := fun t => ρ ^ t * (cy' t + co' (t + 1) / χ - W)
  have hg0 : ∀ t, 0 ≤ g t := fun t => mul_nonneg (pow_nonneg hρ0.le t) (by linarith [hcost t])
  set gold := co' 0 - ωo
  have hco0 : (stEqAlloc ωy ωo χ).2.1 0 = ωo := by simp [stEqAlloc]
  have hgold : 0 ≤ gold := by simp only [gold]; rw [hco0] at hold; linarith
  have hsum : ∀ N, ∑ t ∈ Finset.range N, g t + gold ≤ ρ ^ N * (ωy - cy' N - s' N) := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, one_mul, gold]
              linarith
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hstep : ρ ^ N * (ωy - cy' N - s' N) + g N ≤
          ρ ^ (N + 1) * (ωy - cy' (N + 1) - s' (N + 1)) := by
        have e : ρ ^ N * (ωy - cy' N - s' N) + g N =
            ρ ^ (N + 1) * (co' (N + 1) - ωo) - ρ ^ N * s' N := by
          simp only [g, hW, hρ, pow_succ]; field_simp; ring
        have e2 : ρ ^ N * s' N = ρ ^ (N + 1) * (χ * s' N) := by
          rw [pow_succ, hρ]; field_simp
        rw [e, e2, ← mul_sub]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hρ0.le _)
        linarith [hres N]
      linarith
  obtain ⟨G, T, hG, hGT⟩ : ∃ G T, 0 < G ∧ ∀ N, T < N → G ≤ ∑ t ∈ Finset.range N, g t + gold := by
    rcases hstrict with h | ⟨T, hT⟩
    · refine ⟨gold, 0, by simp only [gold]; rw [hco0] at h; linarith, fun N _ => ?_⟩
      linarith [Finset.sum_nonneg fun t (_ : t ∈ Finset.range N) => hg0 t]
    · rw [hgenU] at hT
      refine ⟨g T, T, mul_pos (pow_pos hρ0 T) (by linarith [hcost_strict T hT]), fun N hN => ?_⟩
      have := Finset.single_le_sum (fun t _ => hg0 t) (Finset.mem_range.2 hN)
      linarith
  have hlim : Tendsto (fun N => ρ ^ N * ωy) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const ωy
  obtain ⟨N, hN⟩ := ((hlim.eventually (gt_mem_nhds hG)).and (eventually_gt_atTop T)).exists
  have h1 := hGT N hN.2
  have h2 := hsum N
  have h3 : 0 < ρ ^ N * (cy' N + s' N) :=
    mul_pos (pow_pos hρ0 N) (by linarith [(hpos N).1, (hpos N).2.2])
  nlinarith [hN.1]

/-- **AKMM, p. 181: "the equilibrium is actually optimal when `χ > 1` but not when `χ ≤ 1`".**
For positive storage (`χω_y > ω_o`), the storage equilibrium is Pareto optimal iff `χ > 1`. -/
theorem storage_optimal_iff {ωy ωo χ : ℝ} (hχ : 0 < χ) (hy : 0 < ωy) (ho : 0 < ωo)
    (hs : ωo < χ * ωy) :
    stParetoOptimal ωy ωo χ (stEqAlloc ωy ωo χ).1 (stEqAlloc ωy ωo χ).2.1
      (stEqAlloc ωy ωo χ).2.2 ↔ 1 < χ := by
  constructor
  · intro h
    by_contra hle
    push Not at hle
    exact storage_not_optimal hχ hy ho hs hle h
  · intro h
    exact storage_optimal h hy ho hs

/-! ### The Diamond economy -/

/-- **AKMM, p. 182: the equilibrium law of motion.** If saving is `sₜ = h(wₜ, r_{t+1}, w_{t+1})`,
the asset market clears (`sₜ = k_{t+1}`) and prices are marginal products `rₜ = F₁(kₜ)`,
`wₜ = F₂(kₜ)`, then `k_{t+1} = h(F₂(kₜ), F₁(k_{t+1}), F₂(k_{t+1}))`. -/
theorem diamond_law_of_motion {h : ℝ → ℝ → ℝ → ℝ} {F1 F2 : ℝ → ℝ} {s k r w : ℕ → ℝ}
    (hs : ∀ t, s t = h (w t) (r (t + 1)) (w (t + 1))) (hclear : ∀ t, s t = k (t + 1))
    (hr : ∀ t, r t = F1 (k t)) (hw : ∀ t, w t = F2 (k t)) (t : ℕ) :
    k (t + 1) = h (F2 (k t)) (F1 (k (t + 1))) (F2 (k (t + 1))) := by
  have := hs t
  rw [hclear t, hr, hw, hw] at this
  exact this

/-- **AKMM, p. 182: `∏_{s=1}^t R_s = 1/pₜ`.** With `p₀ = 1` and the no-arbitrage condition
`p_{s+1}R_{s+1} = p_s` (the gross return between `s` and `s + 1` is `p_s/p_{s+1}`), the product
of returns is the reciprocal of the Arrow–Debreu price. -/
theorem theorem_6_2_prices {p R : ℕ → ℝ} (hp : ∀ t, p t ≠ 0) (hp0 : p 0 = 1)
    (hR : ∀ s, p (s + 1) * R (s + 1) = p s) (t : ℕ) :
    ∏ s ∈ Finset.range t, R (s + 1) = 1 / p t := by
  induction t with
  | zero => simp [hp0]
  | succ t ih =>
    rw [Finset.prod_range_succ, ih]
    have := hR t
    have := hp (t + 1)
    have := hp t
    field_simp
    linarith

/-! ### Theorem 6.2: dynamic efficiency -/

/-- A feasible capital path from `k₀` (AKMM, p. 182): `kₜ ≥ 0` and consumption
`cₜ = fₜ(kₜ) − k_{t+1} ≥ 0`, where `fₜ(k) = F(k, ωₜ) + (1 − δ)k` is the gross resource. -/
def dePath (f : ℕ → ℝ → ℝ) (k0 : ℝ) (k : ℕ → ℝ) : Prop :=
  k 0 = k0 ∧ ∀ t, 0 ≤ k t ∧ 0 ≤ f t (k t) - k (t + 1)

/-- Consumption along a path. -/
def deCons (f : ℕ → ℝ → ℝ) (k : ℕ → ℝ) (t : ℕ) : ℝ := f t (k t) - k (t + 1)

/-- AKMM, p. 181: a feasible path is dynamically efficient if no feasible path from the same
`k₀` gives at least as much consumption at every date and more at some date. -/
def deEfficient (f : ℕ → ℝ → ℝ) (k : ℕ → ℝ) : Prop :=
  dePath f (k 0) k ∧ ¬ ∃ k', dePath f (k 0) k' ∧ (∀ t, deCons f k t ≤ deCons f k' t) ∧
    ∃ t, deCons f k t < deCons f k' t

/-- **Theorem 6.2, efficiency half** (AKMM, p. 182, with fn. 12). Let `k` be a feasible path,
bounded by `K̄`, with returns `0 < Rₜ ≤ R̄` that are supergradients of `fₜ` at `kₜ`, and with
curvature bounded below, `fₜ(y) ≤ fₜ(kₜ) + Rₜ(y − kₜ) − (a/2)(y − kₜ)²` for `0 ≤ y ≤ kₜ`
(`a > 0`; this is `−f″ ≥ a`). If `Σₜ ∏_{s=1}^t R_s = ∞`, the path is dynamically efficient. -/
theorem theorem_6_2_efficient {f : ℕ → ℝ → ℝ} {k R : ℕ → ℝ} {a Rbar Kbar : ℝ} (ha : 0 < a)
    (hR : ∀ t, 0 < R t) (hRbar : ∀ t, R t ≤ Rbar) (hK : ∀ t, k t ≤ Kbar)
    (hsup : ∀ t y, 0 ≤ y → f t y ≤ f t (k t) + R t * (y - k t))
    (hstrong : ∀ t y, 0 ≤ y → y ≤ k t →
      f t y ≤ f t (k t) + R t * (y - k t) - a / 2 * (y - k t) ^ 2)
    (hpath : dePath f (k 0) k)
    (hdiv : ¬ Summable fun t => ∏ s ∈ Finset.range t, R (s + 1)) : deEfficient f k := by
  refine ⟨hpath, ?_⟩
  rintro ⟨k', ⟨hk0, hk'⟩, hle, T, hT⟩
  set ε : ℕ → ℝ := fun t => k t - k' t with hε
  have hRbar0 : 0 < Rbar := (hR 0).trans_le (hRbar 0)
  -- `ε_{t+1} ≥ Rₜεₜ + dₜ`
  have hrec : ∀ t, R t * ε t + (deCons f k' t - deCons f k t) ≤ ε (t + 1) := by
    intro t
    have := hsup t (k' t) (hk' t).1
    simp only [deCons, hε]
    linarith
  have hnn : ∀ t, 0 ≤ ε t := by
    intro t
    induction t with
    | zero => simp [hε, hk0]
    | succ t ih => nlinarith [hrec t, hle t, hR t]
  have hεK : ∀ t, ε t ≤ Kbar := fun t => by simp only [hε]; linarith [(hk' t).1, hK t]
  have hT1 : 0 < ε (T + 1) := by nlinarith [hrec T, hR T, hnn T]
  -- the quadratic recursion
  set b := a / (2 * Rbar) with hb
  have hb0 : 0 < b := by positivity
  have hquad : ∀ t, R t * ε t * (1 + b * ε t) ≤ ε (t + 1) := by
    intro t
    have h1 := hstrong t (k' t) (hk' t).1 (by linarith [hnn t])
    have h2 : ε (t + 1) ≥ R t * ε t + a / 2 * ε t ^ 2 := by
      have := hle t
      simp only [deCons, hε] at this ⊢
      nlinarith
    have h3 : R t * ε t * (1 + b * ε t) ≤ R t * ε t + a / 2 * ε t ^ 2 := by
      have hR' : R t * b ≤ a / 2 := by
        rw [hb, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
        nlinarith [hRbar t, hR t]
      nlinarith [sq_nonneg (ε t), hnn t]
    linarith
  have hpos : ∀ n, 0 < ε (T + 1 + n) := by
    intro n
    induction n with
    | zero => simpa using hT1
    | succ n ih =>
      have := hquad (T + 1 + n)
      rw [← add_assoc]
      have hp : 0 < R (T + 1 + n) * ε (T + 1 + n) * (1 + b * ε (T + 1 + n)) :=
        mul_pos (mul_pos (hR _) ih) (by positivity)
      linarith
  -- the weighted reciprocals decrease by at least `c·P_{T+n}`
  set P : ℕ → ℝ := fun t => ∏ s ∈ Finset.range t, R (s + 1) with hP
  have hPpos : ∀ t, 0 < P t := fun t => Finset.prod_pos fun s _ => hR (s + 1)
  set c := b / (1 + b * Kbar) with hc
  have hKbar0 : 0 ≤ Kbar := (hnn 0).trans (hεK 0)
  have hc0 : 0 < c := by positivity
  set v : ℕ → ℝ := fun n => P (T + n) / ε (T + 1 + n) with hv
  have hvstep : ∀ n, v (n + 1) + c * P (T + n) ≤ v n := by
    intro n
    have he := hpos n
    have he1 := hpos (n + 1)
    have hRn := hR (T + n + 1)
    have hq := hquad (T + 1 + n)
    rw [show T + 1 + n + 1 = T + 1 + (n + 1) by ring] at hq
    have hPs : P (T + (n + 1)) = P (T + n) * R (T + n + 1) := by
      simp only [hP, ← add_assoc, Finset.prod_range_succ]
    simp only [hv, hPs]
    have hKe : ε (T + 1 + n) ≤ Kbar := hεK _
    have hPn := hPpos (T + n)
    -- `P R / ε' ≤ P/(ε(1 + bε))`
    have h1 : P (T + n) * R (T + n + 1) / ε (T + 1 + (n + 1)) ≤
        P (T + n) / (ε (T + 1 + n) * (1 + b * ε (T + 1 + n))) := by
      rw [div_le_div_iff₀ he1 (by positivity)]
      have : R (T + n + 1) = R (T + 1 + n) := by ring_nf
      rw [this] at hRn ⊢
      nlinarith [mul_le_mul_of_nonneg_left hq hPn.le]
    -- `1/(ε(1 + bε)) ≤ 1/ε − c`
    have h2 : P (T + n) / (ε (T + 1 + n) * (1 + b * ε (T + 1 + n))) + c * P (T + n) ≤
        P (T + n) / ε (T + 1 + n) := by
      have hden : 0 < 1 + b * Kbar := by positivity
      rw [hc]
      rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) he]
      have : b / (1 + b * Kbar) * (1 + b * ε (T + 1 + n)) ≤ b := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        have := mul_le_mul_of_nonneg_left hKe (mul_pos hb0 hb0).le
        nlinarith
      have e : (P (T + n) + b / (1 + b * Kbar) * P (T + n) *
          (ε (T + 1 + n) * (1 + b * ε (T + 1 + n)))) * ε (T + 1 + n) =
          P (T + n) * ε (T + 1 + n) * (1 + b / (1 + b * Kbar) *
            (1 + b * ε (T + 1 + n)) * ε (T + 1 + n)) := by ring
      rw [e]
      have e2 : P (T + n) * (ε (T + 1 + n) * (1 + b * ε (T + 1 + n))) =
          P (T + n) * ε (T + 1 + n) * (1 + b * ε (T + 1 + n)) := by ring
      rw [e2]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith
    linarith
  have hvsum : ∀ n, v n + c * ∑ j ∈ Finset.range n, P (T + j) ≤ v 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith [hvstep n]
  have hvpos : ∀ n, 0 < v n := fun n => div_pos (hPpos _) (hpos n)
  have hbdd : ∀ n, ∑ j ∈ Finset.range n, P (T + j) ≤ v 0 / c := by
    intro n
    rw [le_div_iff₀ hc0]
    linarith [hvsum n, hvpos n]
  have hsumm : Summable fun j => P (j + T) :=
    summable_of_sum_range_le (fun j => (hPpos _).le) fun n => by
      simpa [add_comm] using hbdd n
  exact hdiv ((summable_nat_add_iff T).1 hsumm)

/-- **Theorem 6.2, inefficiency half** (AKMM, p. 182, with fn. 12). Let `k` be a feasible path
with `kₜ ≥ k_low > 0`, returns `Rₜ ≥ R_low > 0`, and curvature bounded above,
`fₜ(y) ≥ fₜ(kₜ) + Rₜ(y − kₜ) − (M/2)(y − kₜ)²` for `0 ≤ y ≤ kₜ` (`−f″ ≤ M`). If
`Σₜ ∏_{s=1}^t R_s < ∞`, the path is dynamically inefficient: reducing capital by
`εₜ`, with `ε₀ = 0`, `ε₁ = e` small and `ε_{t+1} = Rₜεₜ + (M/2)εₜ²`, raises consumption at date
`0` and lowers it nowhere. -/
theorem theorem_6_2_inefficient {f : ℕ → ℝ → ℝ} {k R : ℕ → ℝ} {M Rlow klow : ℝ} (hM : 0 ≤ M)
    (hRlow : 0 < Rlow) (hR : ∀ t, Rlow ≤ R t) (hklow : 0 < klow) (hk : ∀ t, klow ≤ k t)
    (hlower : ∀ t y, 0 ≤ y → y ≤ k t →
      f t (k t) + R t * (y - k t) - M / 2 * (y - k t) ^ 2 ≤ f t y)
    (hpath : dePath f (k 0) k)
    (hsum : Summable fun t => ∏ s ∈ Finset.range t, R (s + 1)) : ¬ deEfficient f k := by
  rintro ⟨-, hno⟩
  set P : ℕ → ℝ := fun t => ∏ s ∈ Finset.range t, R (s + 1) with hP
  have hR0 : ∀ t, 0 < R t := fun t => hRlow.trans_le (hR t)
  have hPpos : ∀ t, 0 < P t := fun t => Finset.prod_pos fun s _ => hR0 (s + 1)
  set S := ∑' t, P t with hS
  have hPS : ∀ t, P t ≤ S := fun t =>
    hsum.le_tsum t fun j _ => (hPpos j).le
  have hS0 : 0 < S := (hPpos 0).trans_le (hPS 0)
  set c := M / (2 * Rlow) with hc
  have hc0 : 0 ≤ c := by positivity
  set e := 1 / (c * S + S / klow + 1) with he
  have he0 : 0 < e := by positivity
  -- the reductions `e_n = ε_{n+1}`
  let es : ℕ → ℝ := fun n => Nat.rec e (fun m x => R (m + 1) * x + M / 2 * x ^ 2) n
  have hes0 : es 0 = e := rfl
  have hes : ∀ n, es (n + 1) = R (n + 1) * es n + M / 2 * es n ^ 2 := fun n => rfl
  have hespos : ∀ n, 0 < es n := by
    intro n
    induction n with
    | zero => exact he0
    | succ n ih => rw [hes]; have := hR0 (n + 1); positivity
  -- `P_n/e_n ≥ 1/e − cΣ_{j<n} P_j`
  have hvstep : ∀ n, P n / es n - c * P n ≤ P (n + 1) / es (n + 1) := by
    intro n
    have hen := hespos n
    have hRn := hR0 (n + 1)
    have hPs : P (n + 1) = P n * R (n + 1) := by simp only [hP, Finset.prod_range_succ]
    rw [hPs, hes]
    have hcR : M / (2 * R (n + 1)) ≤ c := by
      rw [hc]; exact div_le_div_of_nonneg_left hM (by positivity) (by linarith [hR (n + 1)])
    have hPn := hPpos n
    have h1 : M / 2 ≤ c * R (n + 1) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * R (n + 1))] at hcR
      linarith
    have hD : 0 < R (n + 1) * es n + M / 2 * es n ^ 2 := by positivity
    have key : (P n - c * P n * es n) * (R (n + 1) * es n + M / 2 * es n ^ 2) ≤
        P n * R (n + 1) * es n := by
      have e1 : (P n - c * P n * es n) * (R (n + 1) * es n + M / 2 * es n ^ 2) =
          P n * R (n + 1) * es n + P n * es n ^ 2 * (M / 2 - c * R (n + 1)) -
            c * P n * (M / 2) * es n ^ 3 := by ring
      rw [e1]
      have h2 : P n * es n ^ 2 * (M / 2 - c * R (n + 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      have h3 : 0 ≤ c * P n * (M / 2) * es n ^ 3 := by positivity
      linarith
    calc P n / es n - c * P n = (P n - c * P n * es n) / es n := by field_simp
      _ = (P n - c * P n * es n) * (R (n + 1) * es n + M / 2 * es n ^ 2) /
          (es n * (R (n + 1) * es n + M / 2 * es n ^ 2)) := by field_simp
      _ ≤ P n * R (n + 1) * es n / (es n * (R (n + 1) * es n + M / 2 * es n ^ 2)) :=
          div_le_div_of_nonneg_right key (by positivity)
      _ = P n * R (n + 1) / (R (n + 1) * es n + M / 2 * es n ^ 2) := by field_simp
  have hv : ∀ n, 1 / e - c * ∑ j ∈ Finset.range n, P j ≤ P n / es n := by
    intro n
    induction n with
    | zero => simp [hP, hes0]
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith [hvstep n]
  have hsmall : ∀ n, es n ≤ klow := by
    intro n
    have h1 := hv n
    have h2 : c * ∑ j ∈ Finset.range n, P j ≤ c * S :=
      mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun j _ => (hPpos j).le) hc0
    have h3 : 1 / e = c * S + S / klow + 1 := by rw [he, one_div_one_div]
    have h4 : S / klow < P n / es n := by linarith
    rw [div_lt_div_iff₀ hklow (hespos n)] at h4
    nlinarith [hPS n, hespos n]
  -- the alternative path
  set ε : ℕ → ℝ := fun t => Nat.casesOn t 0 fun n => es n with hεdef
  have hε0 : ε 0 = 0 := rfl
  have hεs : ∀ n, ε (n + 1) = es n := fun n => rfl
  have hεnn : ∀ t, 0 ≤ ε t := fun t => by
    rcases t with _ | n
    · exact le_rfl
    · exact (hespos n).le
  have hεk : ∀ t, ε t ≤ k t := fun t => by
    rcases t with _ | n
    · exact (hpath.2 0).1
    · rw [hεs]; exact (hsmall n).trans (hk _)
  have hrec : ∀ t, R t * ε t + M / 2 * ε t ^ 2 ≤ ε (t + 1) := by
    intro t
    rcases t with _ | n
    · simp only [hε0, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      exact (hespos 0).le
    · exact (hes n).ge
  set k' : ℕ → ℝ := fun t => k t - ε t with hk'
  have hgain : ∀ t, deCons f k t ≤ deCons f k' t := by
    intro t
    have := hlower t (k' t) (by simp only [hk']; linarith [hεk t])
      (by simp only [hk']; linarith [hεnn t])
    simp only [deCons, hk'] at this ⊢
    have hsq : (k t - ε t - k t) ^ 2 = ε t ^ 2 := by ring
    rw [hsq] at this
    nlinarith [hrec t]
  refine hno ⟨k', ⟨by simp [hk', hε0], fun t => ⟨by simp only [hk']; linarith [hεk t],
    by have := hgain t; simp only [deCons] at this; linarith [(hpath.2 t).2]⟩⟩, hgain, 0, ?_⟩
  simp only [deCons, hk', hε0, sub_zero, hεs, hes0]
  linarith

/-- **Theorem 6.2** (AKMM, p. 182). Under the assumptions of fn. 12 (stated as in
`theorem_6_2_efficient` and `theorem_6_2_inefficient`, with the curvature bounds `a ≤ −f″ ≤ M`
as two-sided quadratic bounds), a feasible path is dynamically efficient iff
`Σₜ ∏_{s=1}^t R_s = ∞`. -/
theorem theorem_6_2 {f : ℕ → ℝ → ℝ} {k R : ℕ → ℝ} {a M Rlow Rbar klow Kbar : ℝ} (ha : 0 < a)
    (hM : 0 ≤ M) (hRlow : 0 < Rlow) (hR : ∀ t, Rlow ≤ R t) (hRbar : ∀ t, R t ≤ Rbar)
    (hklow : 0 < klow) (hk : ∀ t, klow ≤ k t) (hK : ∀ t, k t ≤ Kbar)
    (hsup : ∀ t y, 0 ≤ y → f t y ≤ f t (k t) + R t * (y - k t))
    (hstrong : ∀ t y, 0 ≤ y → y ≤ k t →
      f t y ≤ f t (k t) + R t * (y - k t) - a / 2 * (y - k t) ^ 2)
    (hlower : ∀ t y, 0 ≤ y → y ≤ k t →
      f t (k t) + R t * (y - k t) - M / 2 * (y - k t) ^ 2 ≤ f t y)
    (hpath : dePath f (k 0) k) :
    deEfficient f k ↔ ¬ Summable fun t => ∏ s ∈ Finset.range t, R (s + 1) := by
  constructor
  · intro he hs
    exact theorem_6_2_inefficient hM hRlow hR hklow hk hlower hpath hs he
  · intro hdiv
    exact theorem_6_2_efficient ha (fun t => hRlow.trans_le (hR t)) hRbar hK hsup hstrong hpath
      hdiv

/-- The quadratic technology `f(y) = 3y − y²/2` of the instances: around any `k` it equals its
second-order expansion with `f′(k) = 3 − k` and `f″ = −1`. -/
theorem de_quadratic_expansion (k y : ℝ) :
    3 * y - y ^ 2 / 2 = (3 * k - k ^ 2 / 2) + (3 - k) * (y - k) - 1 / 2 * (y - k) ^ 2 := by ring

/-- **Theorem 6.2, a concrete efficient instance.** With `f(y) = 3y − y²/2` and the steady path
`kₜ = 1` (`R = 2`, consumption `3/2`), every hypothesis of `theorem_6_2` holds and the path is
dynamically efficient. -/
theorem theorem_6_2_instance_efficient :
    deEfficient (fun _ y => 3 * y - y ^ 2 / 2) (fun _ => 1) := by
  refine theorem_6_2_efficient (a := 1) (R := fun _ => 2) (Rbar := 2) (Kbar := 1) one_pos
    (fun _ => two_pos) (fun _ => le_rfl) (fun _ => le_rfl) (fun t y _ => ?_)
    (fun t y _ _ => ?_) ⟨rfl, fun _ => ⟨zero_le_one, by norm_num⟩⟩ ?_
  · nlinarith [sq_nonneg (y - 1)]
  · nlinarith [sq_nonneg (y - 1)]
  · simp only [Finset.prod_const, Finset.card_range]
    rw [summable_geometric_iff_norm_lt_one]
    norm_num

/-- **Theorem 6.2, a concrete inefficient instance.** With `f(y) = 3y − y²/2` and the steady path
`kₜ = 5/2` (`R = 1/2`, consumption `15/8`), every hypothesis of `theorem_6_2_inefficient` holds
and the path is dynamically inefficient. -/
theorem theorem_6_2_instance_inefficient :
    ¬ deEfficient (fun _ y => 3 * y - y ^ 2 / 2) (fun _ => 5 / 2) := by
  refine theorem_6_2_inefficient (M := 1) (R := fun _ => 1 / 2) (Rlow := 1 / 2) (klow := 5 / 2)
    zero_le_one (by norm_num) (fun _ => le_rfl) (by norm_num) (fun _ => le_rfl)
    (fun t y _ _ => ?_) ⟨rfl, fun _ => ⟨by norm_num, by norm_num⟩⟩ ?_
  · nlinarith [sq_nonneg (y - 5 / 2)]
  · simp only [Finset.prod_const, Finset.card_range]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-! ### Appendix 6.A: Theorem .5 -/

/-- **Theorem .5 (i)** (AKMM, p. 838): a steady state `k⋆ > 0` with `f′(k⋆) = R⋆ < 1` is
inefficient. A permanent reduction of capital by a small `ε > 0` raises `c₀` by `ε` and every
later `cₜ` by `ε − (f(k⋆) − f(k⋆ − ε)) > 0`. Only the derivative at `k⋆` is used. -/
theorem theorem_A5_inefficient {f : ℝ → ℝ} {kstar Rstar : ℝ} (hk : 0 < kstar)
    (hc : 0 ≤ f kstar - kstar) (hd : HasDerivAt f Rstar kstar) (hR : Rstar < 1) :
    ¬ deEfficient (fun _ => f) (fun _ => kstar) := by
  rintro ⟨-, hno⟩
  have hsl := hd.tendsto_slope_zero_left
  have hev1 : ∀ᶠ t in 𝓝[<] (0 : ℝ), t⁻¹ • (f (kstar + t) - f kstar) < 1 :=
    hsl.eventually (gt_mem_nhds hR)
  have hev2 : ∀ᶠ t in 𝓝[<] (0 : ℝ), -kstar < t :=
    nhdsWithin_le_nhds (lt_mem_nhds (by linarith))
  have hev3 : ∀ᶠ t in 𝓝[<] (0 : ℝ), t < 0 := self_mem_nhdsWithin
  obtain ⟨t, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
  rw [smul_eq_mul] at h1
  set ε := -t with hε
  have hε0 : 0 < ε := by linarith
  have hgain : f kstar - f (kstar - ε) < ε := by
    have : t⁻¹ * (f (kstar + t) - f kstar) = (f kstar - f (kstar - ε)) / ε := by
      rw [hε]; field_simp; ring_nf
    rw [this, div_lt_one hε0] at h1
    exact h1
  set k' : ℕ → ℝ := fun n => if n = 0 then kstar else kstar - ε
  have hcons : ∀ n, deCons (fun _ => f) (fun _ => kstar) n ≤ deCons (fun _ => f) k' n := by
    intro n
    simp only [deCons, k']
    rcases n with _ | n
    · simp only [↓reduceIte, Nat.add_one_ne_zero]; linarith
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]; linarith
  refine hno ⟨k', ⟨rfl, fun n => ⟨?_, ?_⟩⟩, hcons, 0, ?_⟩
  · simp only [k']; split_ifs <;> linarith
  · have := hcons n
    simp only [deCons] at this
    linarith
  · simp only [deCons, k', ↓reduceIte, Nat.add_one_ne_zero]; linarith

/-- **Theorem .5 (ii)** (AKMM, p. 839): a steady state `k⋆ > 0` with `f′(k⋆) = R⋆ ≥ 1` is
efficient, for `f` strictly concave on `[0, ∞)`. With `εₜ = k⋆ − k′ₜ` the deficits of a
dominating path satisfy `εₜ ≥ 0`, become positive, and then grow by at least
`η = h(k⋆) − h(k⋆ − ε_{T+1}) > 0` per period, `h(k) = f(k) − k`; this contradicts `εₜ ≤ k⋆`. -/
theorem theorem_A5_efficient {f : ℝ → ℝ} {kstar Rstar : ℝ} (hk : 0 < kstar)
    (hc : 0 ≤ f kstar - kstar) (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hd : HasDerivAt f Rstar kstar) (hR : 1 ≤ Rstar) :
    deEfficient (fun _ => f) (fun _ => kstar) := by
  have hks : kstar ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 hk.le
  refine ⟨⟨rfl, fun _ => ⟨hk.le, by simpa using hc⟩⟩, ?_⟩
  rintro ⟨k', ⟨hk0, hk'⟩, hle, T, hT⟩
  set ε : ℕ → ℝ := fun t => kstar - k' t with hε
  have hrec : ∀ t, f kstar - f (kstar - ε t) ≤ ε (t + 1) ∧
      (deCons (fun _ => f) (fun _ => kstar) t < deCons (fun _ => f) k' t →
        f kstar - f (kstar - ε t) < ε (t + 1)) := by
    intro t
    have h1 := hle t
    simp only [deCons, hε, sub_sub_cancel] at h1 ⊢
    exact ⟨by linarith, fun h => by linarith⟩
  have hsup : ∀ y, 0 ≤ y → f y ≤ f kstar + Rstar * (y - kstar) := fun y hy =>
    op_concave_tangent hconc.concaveOn hks (Set.mem_Ici.2 hy) hd
  have hεk : ∀ t, ε t ≤ kstar := fun t => by simp only [hε]; linarith [(hk' t).1]
  have hnn : ∀ t, 0 ≤ ε t := by
    intro t
    induction t with
    | zero => simp [hε, hk0]
    | succ t ih =>
      have h1 := (hrec t).1
      have h2 := hsup (kstar - ε t) (by linarith [hεk t])
      nlinarith
  have hT1 : 0 < ε (T + 1) := by
    have h1 := (hrec T).2 hT
    have h2 := hsup (kstar - ε T) (by linarith [hεk T])
    nlinarith [hnn T]
  -- `h(y) = f(y) − y` is nondecreasing on `[0, k⋆]` and strictly below `h(k⋆)` there
  have hlt : ∀ y, 0 ≤ y → y < kstar → f y - y < f kstar - kstar := by
    intro y hy hyk
    have := op_strictConcave_tangent hconc hks (Set.mem_Ici.2 hy) hyk.ne hd
    nlinarith
  have hmono : ∀ y z, 0 ≤ y → y ≤ z → z ≤ kstar → f y - y ≤ f z - z := by
    intro y z hy hyz hzk
    rcases hzk.lt_or_eq with hzk | rfl
    · rcases hyz.lt_or_eq with hyz | rfl
      · -- `z` is a convex combination of `y` and `k⋆`
        set lam := (kstar - z) / (kstar - y) with hlam
        have hl0 : 0 < lam := div_pos (by linarith) (by linarith)
        have hl1 : lam < 1 := by rw [hlam, div_lt_one (by linarith)]; linarith
        have hne : kstar - y ≠ 0 := (sub_pos.2 (by linarith)).ne'
        have hz : lam * y + (1 - lam) * kstar = z := by rw [hlam]; field_simp; ring
        have hcc := hconc.concaveOn.2 (Set.mem_Ici.2 hy) hks hl0.le (by linarith : 0 ≤ 1 - lam)
          (by ring)
        simp only [smul_eq_mul, hz] at hcc
        have := hlt y hy (by linarith)
        nlinarith
      · exact le_rfl
    · rcases hyz.lt_or_eq with hyz | rfl
      · exact (hlt y hy hyz).le
      · exact le_rfl
  set η := (f kstar - kstar) - (f (kstar - ε (T + 1)) - (kstar - ε (T + 1))) with hη
  have hη0 : 0 < η := by
    have := hlt (kstar - ε (T + 1)) (by linarith [hεk (T + 1)]) (by linarith)
    rw [hη]; linarith
  have hgrow : ∀ n : ℕ, ε (T + 1) + n * η ≤ ε (T + 1 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := (hrec (T + 1 + n)).1
      have hge : ε (T + 1) ≤ ε (T + 1 + n) := by
        have : 0 ≤ (n : ℝ) * η := by positivity
        linarith
      have h2 := hmono (kstar - ε (T + 1 + n)) (kstar - ε (T + 1)) (by linarith [hεk (T + 1 + n)])
        (by linarith) (by linarith)
      rw [show T + 1 + (n + 1) = T + 1 + n + 1 by ring]
      push_cast
      rw [hη] at *
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (kstar / η)
  have h1 := hgrow n
  have h2 := hεk (T + 1 + n)
  rw [div_lt_iff₀ hη0] at hn
  linarith

/-- **Theorem .5** (AKMM, Appendix 6.A, p. 838). For `f` strictly concave on `[0, ∞)` with
derivative `R⋆ = f′(k⋆)` at a steady state `k⋆ > 0` with `c⋆ = f(k⋆) − k⋆ ≥ 0`, the steady state
is efficient iff `R⋆ ≥ 1`. -/
theorem theorem_A5 {f : ℝ → ℝ} {kstar Rstar : ℝ} (hk : 0 < kstar) (hc : 0 ≤ f kstar - kstar)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hd : HasDerivAt f Rstar kstar) :
    deEfficient (fun _ => f) (fun _ => kstar) ↔ 1 ≤ Rstar := by
  constructor
  · intro he
    by_contra hlt
    push Not at hlt
    exact theorem_A5_inefficient hk hc hd hlt he
  · exact theorem_A5_efficient hk hc hconc hd

/-- **AKMM, p. 182: the criterion of Theorem 6.2 at a steady state.** With `Rₜ = R⋆ > 0` for all
`t`, `Σₜ ∏_{s=1}^t R_s = ∞` iff `R⋆ ≥ 1` (Miao's `op_cass_steady_state` with `g_n = 1`), the
condition of Theorem .5. -/
theorem theorem_A5_cass {Rstar : ℝ} {R : ℕ → ℝ} (hR : 0 < Rstar) (hRs : ∀ s, R s = Rstar) :
    (¬ Summable fun t => ∏ s ∈ Finset.range t, R (s + 1)) ↔ 1 ≤ Rstar := by
  have := op_cass_steady_state (gn := 1) one_pos hR hRs
  simpa using this

/-- **AKMM, p. 838: the printed `f` misclassifies.** With `F(k) = 2√k` (labour fixed), `δ = 1/2`
and the steady state `k⋆ = 4`, the correct `f(k) = F(k) + (1 − δ)k` has `f′(4) = 1`, so the
steady state is efficient by Theorem .5, but the printed `f(k) = F(k) + 1 − δ` has
`f′(4) = 1/2 < 1`,
which would classify it as inefficient. -/
theorem appendix_6A_printed_f :
    HasDerivAt (fun k => 2 * √k + (1 - 1 / 2) * k) 1 4 ∧
      HasDerivAt (fun k => 2 * √k + (1 - 1 / 2)) (1 / 2) 4 ∧
      deEfficient (fun _ => fun k => 2 * √k + (1 - 1 / 2) * k) (fun _ => 4) := by
  have hs : HasDerivAt (fun k : ℝ => 2 * √k) (1 / 2) 4 := by
    have h := (Real.hasDerivAt_sqrt (by norm_num : (4 : ℝ) ≠ 0)).const_mul 2
    have e : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e] at h
    convert h using 1; norm_num
  have h1 : HasDerivAt (fun k => 2 * √k + (1 - 1 / 2) * k) 1 4 :=
    (hs.add ((hasDerivAt_id (4 : ℝ)).const_mul (1 - 1 / 2))).congr_deriv (by norm_num)
  refine ⟨h1, hs.add_const (1 - 1 / 2), ?_⟩
  have hconc : StrictConcaveOn ℝ (Set.Ici 0) (fun k : ℝ => 2 * √k + (1 - 1 / 2) * k) := by
    have hsq := Real.strictConcaveOn_sqrt
    have h2 : StrictConcaveOn ℝ (Set.Ici 0) (fun k : ℝ => 2 * √k) := by
      refine ⟨hsq.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
      have := hsq.2 hx hy hxy ha hb hab
      simp only [smul_eq_mul] at this ⊢
      linarith
    exact h2.add_concaveOn ((concaveOn_id (convex_Ici 0)).smul (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2))
  have e : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  exact theorem_A5_efficient (by norm_num) (by simp only [e]; norm_num) hconc h1 le_rfl

end AKMM.Welfare
