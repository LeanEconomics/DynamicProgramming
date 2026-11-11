/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMWelfare.Dynastic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Missing markets: a borrowing constraint

AKMM, §6.3.3, pp. 170–171, and §6.5.1, p. 184. Two log-utility consumers share a constant
endowment `ω`; consumer `i ∈ {0, 1}` (the book's agents 1 and 2) receives
`e_{i,t} = ω/2 − (ω/6)(−1)^{i+t}`: agent 1 has `ω/3` in even and `2ω/3` in odd periods, agent 2
the reverse.

* **Unrestricted markets** (p. 170): `pₜ = βᵗ` (gross interest rate `1/β`),
  `c₁ = (1/3 + 2β/3)ω/(1 + β)` and `c₂ = (2/3 + β/3)ω/(1 + β)` form an Arrow–Debreu equilibrium
  (`borrow_unrestricted`, with the endowment values `borrow_endow_value`).
* **The consumption possibility set** (p. 171): `c₀ ≤ a₀ + ω₀` and
  `q₀c₁ ≤ ω₀ + a₀ − c₀ + q₀ω₁` (`borrow_possibility_set`); the book prints `− q₀ω₁`
  (`borrow_possibility_set_printed_counterexample`).
* **No borrowing** (pp. 170–171): the sequential problem with `a_{t+1} ≥ 0` (`nbOptimal`) and its
  equilibrium (`nbEquilibrium`). Bond-market clearing with `a ≥ 0` forces autarky
  (`borrow_autarky`); at an optimum the Euler equation becomes the inequality
  `qₜu′(cₜ) ≥ βu′(c_{t+1})` (`borrow_euler_ineq`, proved by raising `a_{t+1}`); conversely the
  inequality at the endowment makes autarky optimal (`borrow_autarky_optimal`). Hence the
  equilibria are exactly autarky with `qₜ ≥ 2β` for all `t` (`borrow_equilibrium_iff`): `qₜ = 2β`
  is the case in which the lender's constraint does not bind, and fn. 9's `qₜ > 2β` are
  equilibria too. At `qₜ = 2β` the real rate `1/qₜ − 1` is below the unrestricted `1/β − 1`, and
  negative iff `β > 1/2` (`borrow_interest_rate`).
* The autarky allocation is not Pareto optimal: the unrestricted equilibrium allocation is
  feasible and strictly better for both consumers (`borrow_autarky_not_optimal`), so the transfer
  policy of §6.5.1 can make both better off.
-/

namespace AKMM.Welfare

open Filter Topology AKMM.CompetitiveEquilibrium

/-- The endowments of §6.3.3: `e_{i,t} = ω/2 − (ω/6)(−1)^{i+t}`. -/
noncomputable def brEndow (ω : ℝ) (i : Fin 2) (t : ℕ) : ℝ := ω / 2 - ω / 6 * (-1) ^ ((i : ℕ) + t)

/-- The unrestricted equilibrium consumption `cᵢ = ω/2 − (ω/6)(−1)^i(1 − β)/(1 + β)`. -/
noncomputable def brCons (ω β : ℝ) (i : Fin 2) : ℝ :=
  ω / 2 - ω / 6 * (-1) ^ (i : ℕ) * ((1 - β) / (1 + β))

/-- AKMM, p. 170: agent 1 (`i = 0`) has `ω/3` in even and `2ω/3` in odd periods, agent 2 the
reverse, and the total is `ω`. -/
theorem brEndow_spec (ω : ℝ) (t : ℕ) :
    (Even t → brEndow ω 0 t = ω / 3 ∧ brEndow ω 1 t = 2 * ω / 3) ∧
    (Odd t → brEndow ω 0 t = 2 * ω / 3 ∧ brEndow ω 1 t = ω / 3) ∧
    brEndow ω 0 t + brEndow ω 1 t = ω := by
  simp only [brEndow, Fin.val_zero, Fin.val_one, zero_add]
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · rw [h.neg_one_pow, (h.one_add).neg_one_pow]; constructor <;> ring
  · rw [h.neg_one_pow, (h.one_add).neg_one_pow]; constructor <;> ring
  · rw [pow_add]; ring

/-- AKMM, p. 170: the book's formulas `c₁ = (1/3 + 2β/3)ω/(1 + β)`, `c₂ = (2/3 + β/3)ω/(1 + β)`. -/
theorem brCons_spec {ω β : ℝ} (hβ : 0 ≤ β) :
    brCons ω β 0 = (1 / 3 + 2 * β / 3) * ω / (1 + β) ∧
      brCons ω β 1 = (2 / 3 + β / 3) * ω / (1 + β) := by
  have : 1 + β ≠ 0 := by linarith
  simp only [brCons, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  constructor <;> field_simp <;> ring

/-- AKMM, p. 170: the values of the endowments at `pₜ = βᵗ`:
`Σ βᵗe_{i,t} = (ω/2)/(1 − β) − (ω/6)(−1)^i/(1 + β)`. -/
theorem borrow_endow_value {ω β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (i : Fin 2) :
    Summable (fun t => β ^ t * brEndow ω i t) ∧
      ∑' t, β ^ t * brEndow ω i t = ω / 2 / (1 - β) - ω / 6 * (-1) ^ (i : ℕ) / (1 + β) := by
  have hg := summable_geometric_of_lt_one hβ0 hβ1
  have hn : ‖-β‖ < 1 := by rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1
  have hg' := summable_geometric_of_norm_lt_one hn
  have e : (fun t => β ^ t * brEndow ω i t) =
      fun t => ω / 2 * β ^ t - ω / 6 * (-1) ^ (i : ℕ) * (-β) ^ t := by
    funext t; simp only [brEndow, pow_add, neg_pow β]; ring
  rw [e]
  refine ⟨(hg.mul_left _).sub (hg'.mul_left _), ?_⟩
  rw [(hg.mul_left _).tsum_sub (hg'.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one hβ0 hβ1, tsum_geometric_of_norm_lt_one hn]
  have : 1 - β ≠ 0 := by linarith
  have : 1 - -β ≠ 0 := by linarith
  field_simp
  ring

/-- **AKMM, p. 170: the unrestricted equilibrium.** For `ω > 0`, `0 < β < 1`, the prices
`pₜ = βᵗ` and the constant consumptions `brCons` form an Arrow–Debreu equilibrium of the
two-agent log economy; the gross interest rate is `pₜ/p_{t+1} = 1/β`. -/
theorem borrow_unrestricted {ω β : ℝ} (hω : 0 < ω) (hβ0 : 0 < β) (hβ1 : β < 1) :
    dyCompEq Real.log β (brEndow ω) (fun i _ => brCons ω β i) (fun t => β ^ t) ∧
      ∀ t, β ^ t / β ^ (t + 1) = 1 / β := by
  refine ⟨⟨fun i => (borrow_endow_value hβ0.le hβ1 i).1, fun i => ?_, fun t => ?_⟩, fun t => ?_⟩
  · have hr : 0 < (1 - β) / (1 + β) := div_pos (by linarith) (by linarith)
    have hr1 : (1 - β) / (1 + β) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have hc : 0 < brCons ω β i := by
      fin_cases i <;> simp [brCons] <;> nlinarith
    have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
    refine ad_foc_sufficient (du := fun _ => (brCons ω β i)⁻¹) (lam := (brCons ω β i)⁻¹)
      hβ0.le (fun t x hx => ce_log_tangent hc hx) (fun t => by ring)
      ⟨fun _ => hc, hgeo.mul_right _, ?_⟩ (hgeo.mul_right _)
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1, (borrow_endow_value hβ0.le hβ1 i).2]
    simp only [brCons]
    have : 1 - β ≠ 0 := by linarith
    have : 1 + β ≠ 0 := by linarith
    field_simp
  · rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have := (brEndow_spec ω t).2.2
    simp only [brCons, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    linarith
  · rw [pow_succ]; field_simp

/-- **AKMM, p. 171 (corrected).** In the sequential budgets `c₀ + q₀a₁ = ω₀ + a₀`,
`c₁ + q₁a₂ = ω₁ + a₁` with the borrowing constraints `a₁, a₂ ≥ 0` and `q₀ > 0`, `q₁ ≥ 0`:
`c₀ ≤ a₀ + ω₀` and `q₀c₁ ≤ ω₀ + a₀ − c₀ + q₀ω₁`. -/
theorem borrow_possibility_set {c₀ c₁ a₀ a₁ a₂ q₀ q₁ ω₀ ω₁ : ℝ} (hq₀ : 0 < q₀) (hq₁ : 0 ≤ q₁)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₀ : c₀ + q₀ * a₁ = ω₀ + a₀)
    (hb₁ : c₁ + q₁ * a₂ = ω₁ + a₁) :
    c₀ ≤ a₀ + ω₀ ∧ q₀ * c₁ ≤ ω₀ + a₀ - c₀ + q₀ * ω₁ := by
  constructor
  · nlinarith
  · have : c₁ ≤ ω₁ + a₁ := by nlinarith
    nlinarith

/-- **AKMM, p. 171: the printed constraint `q₀c₁ ≤ ω₀ + a₀ − c₀ − q₀ω₁` is wrong.** With
`a₀ = a₁ = a₂ = 0`, `ω₀ = ω₁ = 1`, `q₀ = q₁ = 1`, `c₀ = c₁ = 1` (autarky, which satisfies every
budget and borrowing constraint), the printed inequality reads `1 ≤ −1`. -/
theorem borrow_possibility_set_printed_counterexample :
    let c₀ : ℝ := 1; let c₁ : ℝ := 1; let q₀ : ℝ := 1; let ω₀ : ℝ := 1; let ω₁ : ℝ := 1
    let a₀ : ℝ := 0; let a₁ : ℝ := 0
    c₀ + q₀ * a₁ = ω₀ + a₀ ∧ c₁ + 1 * 0 = ω₁ + a₁ ∧ ¬ (q₀ * c₁ ≤ ω₀ + a₀ - c₀ - q₀ * ω₁) := by
  norm_num

/-- Consumption in the sequential budget `cₜ + qₜa_{t+1} = ωₜ + aₜ`. -/
def nbCons (q ω a : ℕ → ℝ) (t : ℕ) : ℝ := ω t + a t - q t * a (t + 1)

/-- AKMM, p. 170: a plan of bond holdings with `a₀ = 0`, the borrowing constraint
`a_{t+1} ≥ 0` and positive consumption. -/
def nbFeasible (q ω a : ℕ → ℝ) : Prop :=
  a 0 = 0 ∧ (∀ t, 0 ≤ a (t + 1)) ∧ ∀ t, 0 < nbCons q ω a t

/-- AKMM, p. 170: `a` solves `max Σ βᵗ log(ωₜ + aₜ − qₜa_{t+1})` subject to `a_{t+1} ≥ 0`, among
the plans whose utility series converges. -/
def nbOptimal (β : ℝ) (q ω a : ℕ → ℝ) : Prop :=
  nbFeasible q ω a ∧ Summable (fun t => β ^ t * Real.log (nbCons q ω a t)) ∧
    ∀ a', nbFeasible q ω a' → Summable (fun t => β ^ t * Real.log (nbCons q ω a' t)) →
      ∑' t, β ^ t * Real.log (nbCons q ω a' t) ≤ ∑' t, β ^ t * Real.log (nbCons q ω a t)

/-- AKMM, pp. 170–171: an equilibrium with the borrowing constraint: every consumer solves her
problem at the bond prices `q` and the bond market clears. -/
def nbEquilibrium {I : Type*} [Fintype I] (β : ℝ) (q : ℕ → ℝ) (ω a : I → ℕ → ℝ) : Prop :=
  (∀ i, nbOptimal β q (ω i) (a i)) ∧ ∀ t, ∑ i, a i t = 0

/-- **AKMM, p. 171: no borrowing means autarky.** In an equilibrium every `a_{i,t} = 0`, so
`c_{i,t} = ω_{i,t}`. -/
theorem borrow_autarky {I : Type*} [Fintype I] {β : ℝ} {q : ℕ → ℝ} {ω a : I → ℕ → ℝ}
    (he : nbEquilibrium β q ω a) : ∀ i t, a i t = 0 ∧ nbCons q (ω i) (a i) t = ω i t := by
  have ha : ∀ i t, a i t = 0 := by
    intro i t
    rcases t with _ | t
    · exact (he.1 i).1.1
    · exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => (he.1 k).1.2.1 t).1 (he.2 (t + 1)) i
        (Finset.mem_univ _)
  intro i t
  refine ⟨ha i t, ?_⟩
  simp [nbCons, ha i t, ha i (t + 1)]

/-- **AKMM, pp. 170–171: the Euler inequality.** At an optimum of the problem with the
borrowing constraint, with `β, qₜ > 0`, `qₜu′(cₜ) ≥ βu′(c_{t+1})`, i.e.
`β/c_{t+1} ≤ qₜ/cₜ` (the multiplier `µₜ ≥ 0`). Proved by raising `a_{t+1}`. -/
theorem borrow_euler_ineq {β : ℝ} {q ω a : ℕ → ℝ} (hβ : 0 < β) (hopt : nbOptimal β q ω a)
    (t : ℕ) : β / nbCons q ω a (t + 1) ≤ q t / nbCons q ω a t := by
  obtain ⟨⟨ha0, hann, hpos⟩, hU, hmax⟩ := hopt
  set ct := nbCons q ω a t with hct
  set ct1 := nbCons q ω a (t + 1) with hct1
  have hct0 := hpos t
  have hct10 := hpos (t + 1)
  -- the perturbed plans
  let a' : ℝ → ℕ → ℝ := fun ε n => if n = t + 1 then a (t + 1) + ε else a n
  have hc't : ∀ ε, nbCons q ω (a' ε) t = ct - q t * ε := fun ε => by
    simp only [nbCons, a', hct, ↓reduceIte, show t ≠ t + 1 by omega]; ring
  have hc't1 : ∀ ε, nbCons q ω (a' ε) (t + 1) = ct1 + ε := fun ε => by
    simp only [nbCons, a', hct1, ↓reduceIte, show t + 1 + 1 ≠ t + 1 by omega]; ring
  have hc'o : ∀ ε, ∀ n ∉ ({t, t + 1} : Finset ℕ), nbCons q ω (a' ε) n = nbCons q ω a n := by
    intro ε n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp only [nbCons, a', hn.2, show n + 1 ≠ t + 1 by omega, ↓reduceIte]
  set φ : ℝ → ℝ := fun ε => β ^ t * Real.log (ct - q t * ε) + β ^ (t + 1) * Real.log (ct1 + ε)
    with hφ
  -- the optimum is not improved by small `ε > 0`
  have hle : ∀ ε, 0 ≤ ε → 0 < ct - q t * ε → φ ε ≤ φ 0 := by
    intro ε hε hεc
    have hfe : nbFeasible q ω (a' ε) := by
      refine ⟨by simp [a', ha0], fun n => ?_, fun n => ?_⟩
      · by_cases hn : n + 1 = t + 1
        · simp only [a', hn, ↓reduceIte]; linarith [hann t]
        · simp only [a', hn, ↓reduceIte]; exact hann n
      · by_cases hn1 : n = t
        · subst hn1; rw [hc't]; exact hεc
        by_cases hn2 : n = t + 1
        · subst hn2; rw [hc't1]; linarith
        rw [hc'o ε n (by simp [hn1, hn2])]; exact hpos n
    obtain ⟨hS, hE⟩ := ce_tsum_perturb (f := fun n => β ^ n * Real.log (nbCons q ω a n))
      (g := fun n => β ^ n * Real.log (nbCons q ω (a' ε) n)) {t, t + 1}
      (fun n hn => by simp only [hc'o ε n hn]) hU
    have := hmax (a' ε) hfe hS
    rw [hE, Finset.sum_pair (by omega), hc't, hc't1] at this
    simp only [hφ, mul_zero, sub_zero, add_zero]
    linarith
  -- the derivative of `φ` at `0`
  have hd : HasDerivAt φ (β ^ t * (ct⁻¹ * (-q t)) + β ^ (t + 1) * ct1⁻¹) 0 := by
    have h1 : HasDerivAt (fun ε => Real.log (ct - q t * ε)) (ct⁻¹ * (-q t)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => ct - q t * ε) (-q t) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (q t)).const_sub ct
      have hl : HasDerivAt Real.log ct⁻¹ (ct - q t * 0) := by
        simpa using Real.hasDerivAt_log hct0.ne'
      exact hl.comp 0 hin
    have h2 : HasDerivAt (fun ε => Real.log (ct1 + ε)) ct1⁻¹ 0 := by
      have hl : HasDerivAt Real.log ct1⁻¹ (ct1 + 0) := by
        simpa using Real.hasDerivAt_log hct10.ne'
      simpa using hl.comp_const_add ct1 0
    exact (h1.const_mul _).add (h2.const_mul _)
  have hnonpos : β ^ t * (ct⁻¹ * (-q t)) + β ^ (t + 1) * ct1⁻¹ ≤ 0 := by
    by_contra hpos'
    push Not at hpos'
    have hsl := hd.tendsto_slope_zero_right
    have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε⁻¹ • (φ (0 + ε) - φ 0) :=
      hsl.eventually (lt_mem_nhds hpos')
    have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ct - q t * ε := by
      have : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < ct - q t * ε :=
        continuousAt_const.eventually_lt
          (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
          (by simpa using hct0)
      exact nhdsWithin_le_nhds this
    have hev3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    obtain ⟨ε, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
    have := hle ε h3.le h2
    rw [zero_add, smul_eq_mul] at h1
    have : ε⁻¹ * (φ ε - φ 0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 h3.le) (by linarith)
    linarith
  have hbt := pow_pos hβ t
  rw [pow_succ] at hnonpos
  have key : β ^ t * (β * ct - q t * ct1) ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left hnonpos (mul_pos hct0 hct10).le
    have e : ct * ct1 * (β ^ t * (ct⁻¹ * -q t) + β ^ t * β * ct1⁻¹) =
        β ^ t * (β * ct - q t * ct1) := by
      have h1 : ct ≠ 0 := hct0.ne'
      have h2 : ct1 ≠ 0 := hct10.ne'
      field_simp; ring
    rw [e, mul_zero] at h
    exact h
  rw [div_le_div_iff₀ hct10 hct0]
  by_contra hcon
  push Not at hcon
  have := mul_pos hbt (sub_pos.2 hcon)
  linarith

/-- **AKMM, pp. 170–171: autarky is optimal under the Euler inequality.** If `ωₜ > 0`,
`βωₜ ≤ qₜω_{t+1}` (that is, `qₜu′(ωₜ) ≥ βu′(ω_{t+1})`) for all `t`, `β ≥ 0`, and the autarky
utility series converges, then `a = 0` solves the problem with the borrowing constraint.
(No transversality condition is needed: every partial sum is compared.) -/
theorem borrow_autarky_optimal {β : ℝ} {q ω : ℕ → ℝ} (hβ : 0 ≤ β) (hω : ∀ t, 0 < ω t)
    (heul : ∀ t, β * ω t ≤ q t * ω (t + 1))
    (hU : Summable fun t => β ^ t * Real.log (ω t)) : nbOptimal β q ω (fun _ => 0) := by
  have hc0 : ∀ t, nbCons q ω (fun _ => 0) t = ω t := fun t => by simp [nbCons]
  refine ⟨⟨rfl, fun _ => le_rfl, fun t => by rw [hc0]; exact hω t⟩, by simpa [hc0] using hU,
    fun a' ha' hU' => ?_⟩
  simp only [hc0]
  obtain ⟨ha0, hann, hpos⟩ := ha'
  -- the tangent bound at each date
  have htan : ∀ n, β ^ n * Real.log (nbCons q ω a' n) ≤
      β ^ n * Real.log (ω n) + β ^ n * ((a' n - q n * a' (n + 1)) / ω n) := by
    intro n
    have h1 := ce_log_tangent (hω n) (hpos n)
    have h2 : nbCons q ω a' n - ω n = a' n - q n * a' (n + 1) := by simp [nbCons]; ring
    rw [h2] at h1
    have := mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ n)
    calc β ^ n * Real.log (nbCons q ω a' n) ≤ β ^ n * (Real.log (ω n) + (ω n)⁻¹ *
          (a' n - q n * a' (n + 1))) := this
      _ = _ := by ring
  -- the telescoping bound
  have htel : ∀ N, ∑ n ∈ Finset.range N, β ^ n * ((a' n - q n * a' (n + 1)) / ω n) +
      β ^ N * a' N / ω N ≤ 0 := by
    intro N
    induction N with
    | zero => simp [ha0]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hstep : β ^ (N + 1) * a' (N + 1) / ω (N + 1) - β ^ N * q N * a' (N + 1) / ω N ≤ 0 := by
        have hωN := hω N
        have hωN1 := hω (N + 1)
        have e : β ^ (N + 1) * a' (N + 1) / ω (N + 1) - β ^ N * q N * a' (N + 1) / ω N =
            β ^ N * a' (N + 1) * (β * ω N - q N * ω (N + 1)) / (ω N * ω (N + 1)) := by
          field_simp; ring
        rw [e]
        refine div_nonpos_of_nonpos_of_nonneg ?_ (mul_pos hωN hωN1).le
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (pow_nonneg hβ N) (hann N)) (by linarith [heul N])
      have e2 : β ^ N * ((a' N - q N * a' (N + 1)) / ω N) =
          β ^ N * a' N / ω N - β ^ N * q N * a' (N + 1) / ω N := by ring
      linarith
  have hpart : ∀ N, ∑ n ∈ Finset.range N, β ^ n * Real.log (nbCons q ω a' n) ≤
      ∑ n ∈ Finset.range N, β ^ n * Real.log (ω n) := by
    intro N
    have h1 := Finset.sum_le_sum fun n (_ : n ∈ Finset.range N) => htan n
    rw [Finset.sum_add_distrib] at h1
    have h2 : 0 ≤ β ^ N * a' N / ω N := by
      rcases N with _ | N
      · simp [ha0]
      · exact div_nonneg (mul_nonneg (pow_nonneg hβ _) (hann N)) (hω _).le
    linarith [htel N]
  exact le_of_tendsto_of_tendsto' hU'.hasSum.tendsto_sum_nat hU.hasSum.tendsto_sum_nat hpart

/-- The autarky utility series of the alternating economy converges. -/
theorem borrow_endow_log_summable {ω β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (i : Fin 2) :
    Summable fun t => β ^ t * Real.log (brEndow ω i t) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (|Real.log (ω / 3)| +
      |Real.log (2 * ω / 3)|)) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have hv : brEndow ω i t = ω / 3 ∨ brEndow ω i t = 2 * ω / 3 := by
    have := brEndow_spec ω t
    rcases Nat.even_or_odd t with h | h <;> fin_cases i <;> simp_all
  rcases hv with h | h <;> rw [h] <;> linarith [abs_nonneg (Real.log (ω / 3)),
    abs_nonneg (Real.log (2 * ω / 3))]

/-- **AKMM, p. 171 and fn. 9: the equilibria with the borrowing constraint.** In the alternating
economy (`ω > 0`, `0 < β < 1`), `(q, a)` is an equilibrium iff `a = 0` (autarky) and
`qₜ ≥ 2β` for every `t`. -/
theorem borrow_equilibrium_iff {ω β : ℝ} (hω : 0 < ω) (hβ0 : 0 < β) (hβ1 : β < 1)
    {q : ℕ → ℝ} {a : Fin 2 → ℕ → ℝ} :
    nbEquilibrium β q (brEndow ω) a ↔ (∀ i t, a i t = 0) ∧ ∀ t, 2 * β ≤ q t := by
  have hval : ∀ (i : Fin 2) t, (brEndow ω i t = ω / 3 ∧ brEndow ω i (t + 1) = 2 * ω / 3) ∨
      (brEndow ω i t = 2 * ω / 3 ∧ brEndow ω i (t + 1) = ω / 3) := by
    intro i t
    have h0 := brEndow_spec ω t
    have h1 := brEndow_spec ω (t + 1)
    rcases Nat.even_or_odd t with h | h
    · have h' : Odd (t + 1) := h.add_one
      fin_cases i <;> simp_all
    · have h' : Even (t + 1) := h.add_one
      fin_cases i <;> simp_all
  constructor
  · intro he
    have hz := borrow_autarky he
    refine ⟨fun i t => (hz i t).1, fun t => ?_⟩
    -- the consumer who is rich at `t`
    obtain ⟨i, hi⟩ : ∃ i : Fin 2, brEndow ω i t = 2 * ω / 3 ∧ brEndow ω i (t + 1) = ω / 3 := by
      rcases hval 0 t with h | h
      · refine ⟨1, ?_⟩
        have := (brEndow_spec ω t).2.2
        have := (brEndow_spec ω (t + 1)).2.2
        constructor <;> linarith [h.1, h.2]
      · exact ⟨0, h⟩
    have := borrow_euler_ineq hβ0 (he.1 i) t
    rw [(hz i t).2, (hz i (t + 1)).2, hi.1, hi.2] at this
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at this
    nlinarith
  · rintro ⟨hz, hq2⟩
    have ha : a = fun _ _ => 0 := funext fun i => funext fun t => hz i t
    subst ha
    refine ⟨fun i => borrow_autarky_optimal hβ0.le (fun t => ?_) (fun t => ?_)
      (borrow_endow_log_summable hβ0.le hβ1 i), fun t => by simp⟩
    · rcases hval i t with h | h <;> rw [h.1] <;> positivity
    · have := hq2 t
      rcases hval i t with h | h <;> rw [h.1, h.2] <;> nlinarith

/-- **AKMM, p. 171: the interest rate at `qₜ = 2β`.** The real rate `1/(2β) − 1` is below the
unrestricted rate `1/β − 1`, and it is negative iff `β > 1/2`. -/
theorem borrow_interest_rate {β : ℝ} (hβ : 0 < β) :
    1 / (2 * β) - 1 < 1 / β - 1 ∧ (1 / (2 * β) - 1 < 0 ↔ 1 / 2 < β) := by
  constructor
  · have : 1 / (2 * β) < 1 / β := by
      rw [div_lt_div_iff₀ (by positivity) hβ]; linarith
    linarith
  · rw [sub_neg, div_lt_one (by positivity)]
    constructor <;> intro h <;> linarith

/-- **AKMM, p. 171: the no-borrowing allocation is not Pareto optimal** ("consumption is not
smoothed"). The unrestricted equilibrium allocation is feasible and gives both consumers strictly
higher utility than autarky. -/
theorem borrow_autarky_not_optimal {ω β : ℝ} (hω : 0 < ω) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ¬ dyParetoOptimal Real.log β (brEndow ω) (brEndow ω) ∧
      ∀ i, dyU Real.log β (brEndow ω i) < dyU Real.log β (fun _ => brCons ω β i) := by
  obtain ⟨he, -⟩ := borrow_unrestricted hω hβ0 hβ1
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  have hgain : ∀ i, dyU Real.log β (brEndow ω i) < dyU Real.log β (fun _ => brCons ω β i) := by
    intro i
    have hc := (he.2.1 i).1.1 0
    have hepos : ∀ t, 0 < brEndow ω i t := by
      intro t
      rcases (brEndow_spec ω t) with ⟨h1, h2, -⟩
      rcases Nat.even_or_odd t with h | h <;> fin_cases i <;> simp_all
    have hne : brEndow ω i 0 ≠ brCons ω β i := by
      simp only [brEndow, brCons, add_zero]
      intro h
      have h1 : (-1 : ℝ) ^ (i : ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
      have : ω / 6 * (-1) ^ (i : ℕ) * (1 - (1 - β) / (1 + β)) = 0 := by linarith
      have hb : 1 - (1 - β) / (1 + β) = 2 * β / (1 + β) := by field_simp; ring
      rw [hb] at this
      have h2 : 2 * β / (1 + β) ≠ 0 := by positivity
      rcases mul_eq_zero.1 this with h | h
      · rcases mul_eq_zero.1 h with h | h
        · linarith
        · exact h1 h
      · exact h2 h
    -- strict tangent inequality
    have htan : ∀ t, β ^ t * Real.log (brEndow ω i t) ≤ β ^ t * Real.log (brCons ω β i) +
        (brCons ω β i)⁻¹ * (β ^ t * brEndow ω i t - β ^ t * brCons ω β i) := by
      intro t
      have := mul_le_mul_of_nonneg_left (ce_log_tangent hc (hepos t)) (pow_nonneg hβ0.le t)
      linarith [show β ^ t * (Real.log (brCons ω β i) + (brCons ω β i)⁻¹ *
        (brEndow ω i t - brCons ω β i)) = β ^ t * Real.log (brCons ω β i) +
        (brCons ω β i)⁻¹ * (β ^ t * brEndow ω i t - β ^ t * brCons ω β i) by ring]
    have hstrict : Real.log (brEndow ω i 0) < Real.log (brCons ω β i) +
        (brCons ω β i)⁻¹ * (brEndow ω i 0 - brCons ω β i) := by
      have hx := Real.log_lt_sub_one_of_pos (div_pos (hepos 0) hc)
        (by rw [Ne, div_eq_one_iff_eq hc.ne']; exact hne)
      rw [Real.log_div (hepos 0).ne' hc.ne'] at hx
      have : brEndow ω i 0 / brCons ω β i - 1 =
          (brCons ω β i)⁻¹ * (brEndow ω i 0 - brCons ω β i) := by field_simp
      linarith
    have hS : Summable fun t => β ^ t * Real.log (brCons ω β i) +
        (brCons ω β i)⁻¹ * (β ^ t * brEndow ω i t - β ^ t * brCons ω β i) :=
      (hgeo.mul_right _).add (((borrow_endow_value hβ0.le hβ1 i).1.sub
        (hgeo.mul_right _)).mul_left _)
    have hlt := Summable.tsum_lt_tsum (i := 0) htan (by simpa using hstrict)
      (borrow_endow_log_summable hβ0.le hβ1 i) hS
    rw [(hgeo.mul_right _).tsum_add (((borrow_endow_value hβ0.le hβ1 i).1.sub
        (hgeo.mul_right _)).mul_left _), tsum_mul_left,
      (borrow_endow_value hβ0.le hβ1 i).1.tsum_sub (hgeo.mul_right _)] at hlt
    have hW : ∑' t, β ^ t * brCons ω β i = ∑' t, β ^ t * brEndow ω i t := (he.2.1 i).1.2.2
    rw [hW, sub_self, mul_zero, add_zero] at hlt
    exact hlt
  refine ⟨fun ⟨_, _, hno⟩ => hno ⟨fun i _ => brCons ω β i,
    ⟨fun i t => (he.2.1 i).1.1 t, fun t => (he.2.2 t).le⟩, fun i => (he.2.1 i).2.1,
    fun i => (hgain i).le, 0, hgain 0⟩, hgain⟩

end AKMM.Welfare
