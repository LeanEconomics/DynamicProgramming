/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSustainability.Basics
import DeterministicApplications.CakeEating
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Cake eating, Hotelling rents and the oil owner

AKMM, §25.5.2 (pp. 775–778) and the oil producer of §25.4.2 (p. 769). Throughout
`0 < β < 1` and the resource stock is `R₀ > 0`.

* **The planner** (p. 775–776): `c_t = (1 − β)β^t R₀` (`cakePath`) exhausts the cake
  (`cake_hasSum`), follows `c_t = (1 − β)R_t`, `R_{t+1} = R_t − c_t` (`cake_policy`), and has
  finite utility `log((1 − β)R₀)/(1 − β) + β log β/(1 − β)²` (`cake_utility_hasSum`: "utility is
  bounded" in this sense, although `log c_t → −∞`). It is optimal: for every positive plan
  with `Σ_{t<T} c_t ≤ R₀`, `Σ_{t<T} β^t log c_t ≤ Σ_{t<T} β^t log c*_t + β^T/(1 − β)`
  (`cake_overtake`), so its utility is the largest (`cake_optimal`) and it is the unique
  optimum (`cake_unique`). Consumption falls over time (`cake_decreasing`). The same plan is the
  optimal plan of Stokey–Lucas Exercise 5.2b (`cake_slp`, reusing
  `DeterministicApplications`).
* **The market** (pp. 776–777): if the owner's sales maximise income, a date with positive
  sales has the highest Arrow–Debreu price, so with sales at all dates the price is constant
  (`hotelling_price_max`, `hotelling_price_const`). At a constant price `p̂ > 0` selling `c*`
  maximises income and buying `c*` maximises utility within the budget, so the planner's
  allocation is a competitive equilibrium (`cake_market_equilibrium`), with
  `p̂_{t+1}/p̂_t = βc_t/c_{t+1}` (`cake_market_foc`). The **Hotelling rent** is positive: no
  consumer optimum exists if some price is `≤ 0` (`hotelling_rent_pos`). With a second good the
  spot price satisfies `p^o_t = (p_{t+1}/p_t)p^o_{t+1}`, i.e. it grows at the real interest
  rate (`hotelling_rule`).
* **Extraction costs** (p. 778): indifference between extracting at `t` and `t + 1`
  (`hotelling_cost_indifference`) gives
  `p_{t+1}/p_t = 1 + r_t + (mc_{t+1} − (1 + r_t)mc_t)/p_t` (`hotelling_cost_rule`).
* **The oil owner** (p. 769): with log utility and any positive prices, the owner extracts
  `e_t = (1 − β)R_t` with `R_{t+1} = βR_t` (`oil_owner_overtake`, `oil_owner_optimal`).
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

/-- If the partial sums of `f` are eventually below those of `g` up to a vanishing error, the
sums compare. -/
theorem sust_hasSum_le_of_partial {f g : ℕ → ℝ} {a b : ℝ} (hf : HasSum f a) (hg : HasSum g b)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ᶠ T in atTop, ∑ t ∈ range T, f t ≤ ∑ t ∈ range T, g t + ε T) : a ≤ b := by
  have := hg.tendsto_sum_nat.add hε
  rw [add_zero] at this
  exact le_of_tendsto_of_tendsto hf.tendsto_sum_nat this h

/-- AKMM, p. 776: the planner's cake path `c_t = (1 − β)β^t R₀`. -/
noncomputable def cakePath (β R₀ : ℝ) (t : ℕ) : ℝ := (1 - β) * β ^ t * R₀

variable {β R₀ : ℝ}

/-- `Σ_{t<T} (1 − β)β^t R₀ = R₀ − β^T R₀`. -/
theorem cake_partial_sum (β R₀ : ℝ) (T : ℕ) :
    ∑ t ∈ range T, cakePath β R₀ t = R₀ - β ^ T * R₀ := by
  induction T with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, cakePath, pow_succ]; ring

/-- AKMM, p. 776: the planner's path exhausts the cake, `Σ_t c_t = R₀`. -/
theorem cake_hasSum (hβ0 : 0 ≤ β) (hβ1 : β < 1) (R₀ : ℝ) : HasSum (cakePath β R₀) R₀ := by
  have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left ((1 - β) * R₀)
  convert this using 1
  · funext t; simp only [cakePath]; ring
  · field_simp [(by linarith : (0 : ℝ) < 1 - β).ne']

/-- AKMM, p. 776: "the solution to the planning problem is `c_t = (1 − β)R_t`, where
`R_{t+1} = R_t − c_t`, so that `c_t = (1 − β)β^t R₀`": with `R_t = β^t R₀`. -/
theorem cake_policy (β R₀ : ℝ) (t : ℕ) :
    cakePath β R₀ t = (1 - β) * (β ^ t * R₀) ∧
      β ^ (t + 1) * R₀ = β ^ t * R₀ - cakePath β R₀ t := by
  constructor <;> simp only [cakePath, pow_succ] <;> ring

/-- AKMM, p. 776: "consumption is higher in the beginning than later, all because of
discounting". -/
theorem cake_decreasing (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) :
    StrictAnti (cakePath β R₀) := by
  refine strictAnti_nat_of_succ_lt fun t => ?_
  simp only [cakePath, pow_succ]
  have : 0 < (1 - β) * β ^ t * R₀ := by
    have : 0 < 1 - β := by linarith
    positivity
  nlinarith

/-- AKMM, p. 776: the planner's utility is finite: `Σ_t β^t log c_t` converges to
`log((1 − β)R₀)/(1 − β) + β log β/(1 − β)²`. -/
theorem cake_utility_hasSum (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) :
    HasSum (fun t => β ^ t * Real.log (cakePath β R₀ t))
      (Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2) := by
  have h1β : 0 < 1 - β := by linarith
  have hnorm : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
  have h1 := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left (Real.log ((1 - β) * R₀))
  have h2 := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_right (Real.log β)
  convert h1.add h2 using 1
  · funext t
    have : cakePath β R₀ t = ((1 - β) * R₀) * β ^ t := by simp only [cakePath]; ring
    rw [this, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  · field_simp

/-- AKMM, pp. 775–776: the planner's path is optimal. For every plan with `c_t > 0` and
`Σ_{t<T} c_t ≤ R₀` for all `T`,
`Σ_{t<T} β^t log c_t ≤ Σ_{t<T} β^t log c*_t + β^T/(1 − β)`. The bound comes from
`log c ≤ log c* + (c − c*)/c*` and `β^t/c*_t = 1/((1 − β)R₀)`. -/
theorem cake_overtake (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {c : ℕ → ℝ}
    (hc : ∀ t, 0 < c t) (hsum : ∀ T, ∑ t ∈ range T, c t ≤ R₀) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * Real.log (c t) ≤
      ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) + β ^ T / (1 - β) := by
  have h1β : 0 < 1 - β := by linarith
  have hK : 0 < (1 - β) * R₀ := by positivity
  have hstar : ∀ t, 0 < cakePath β R₀ t := fun t => by unfold cakePath; positivity
  have key : ∀ t ∈ range T, β ^ t * Real.log (c t) ≤
      β ^ t * Real.log (cakePath β R₀ t) + (c t - cakePath β R₀ t) / ((1 - β) * R₀) := by
    intro t _
    have h := sust_log_le_tangent (hc t) (hstar t)
    have hb : 0 < β ^ t := by positivity
    have : β ^ t * ((c t - cakePath β R₀ t) / cakePath β R₀ t) =
        (c t - cakePath β R₀ t) / ((1 - β) * R₀) := by
      simp only [cakePath]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left h hb.le]
  calc ∑ t ∈ range T, β ^ t * Real.log (c t)
      ≤ ∑ t ∈ range T, (β ^ t * Real.log (cakePath β R₀ t) +
          (c t - cakePath β R₀ t) / ((1 - β) * R₀)) := sum_le_sum key
    _ = ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) +
          (∑ t ∈ range T, c t - (R₀ - β ^ T * R₀)) / ((1 - β) * R₀) := by
        rw [sum_add_distrib, ← sum_div, sum_sub_distrib, cake_partial_sum]
    _ ≤ ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) +
          (R₀ - (R₀ - β ^ T * R₀)) / ((1 - β) * R₀) := by
        gcongr
        exact hsum T
    _ = _ := by field_simp; ring

/-- AKMM, pp. 775–776: the planner's path maximises lifetime utility among positive plans that
use at most the cake (`Σ_{t<T} c_t ≤ R₀`) and have summable utility. -/
theorem cake_optimal (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {c : ℕ → ℝ} {U : ℝ}
    (hc : ∀ t, 0 < c t) (hsum : ∀ T, ∑ t ∈ range T, c t ≤ R₀)
    (hU : HasSum (fun t => β ^ t * Real.log (c t)) U) :
    U ≤ Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2 := by
  have h1β : 0 < 1 - β := by linarith
  refine sust_hasSum_le_of_partial hU (cake_utility_hasSum hβ0 hβ1 hR)
    (ε := fun T => β ^ T / (1 - β)) ?_
    (Eventually.of_forall fun T => cake_overtake hβ0 hβ1 hR hc hsum T)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).div_const (1 - β)

/-- AKMM, p. 776: the planner's path is the unique optimum: any other positive plan within the
cake has strictly lower utility. -/
theorem cake_unique (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {c : ℕ → ℝ} {U : ℝ}
    (hc : ∀ t, 0 < c t) (hsum : ∀ T, ∑ t ∈ range T, c t ≤ R₀)
    (hU : HasSum (fun t => β ^ t * Real.log (c t)) U) (hne : c ≠ cakePath β R₀) :
    U < Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2 := by
  have h1β : 0 < 1 - β := by linarith
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hne
  have hstar : 0 < cakePath β R₀ s := by unfold cakePath; positivity
  set δ := β ^ s * (Real.log (cakePath β R₀ s) + (c s - cakePath β R₀ s) / cakePath β R₀ s -
    Real.log (c s)) with hδ
  have hδ0 : 0 < δ := by
    have := sust_log_lt_tangent (hc s) hstar hs
    have : 0 < β ^ s := by positivity
    rw [hδ]; nlinarith
  -- the tangent bound loses at least `δ` at date `s`
  have hbound : ∀ T, s < T → ∑ t ∈ range T, β ^ t * Real.log (c t) ≤
      ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) + β ^ T / (1 - β) - δ := by
    intro T hT
    have hK : 0 < (1 - β) * R₀ := by positivity
    set g : ℕ → ℝ := fun t => β ^ t * Real.log (cakePath β R₀ t) +
      (c t - cakePath β R₀ t) / ((1 - β) * R₀) with hg
    have key : ∀ t, β ^ t * Real.log (c t) ≤ g t := by
      intro t
      have hst : 0 < cakePath β R₀ t := by unfold cakePath; positivity
      have h := sust_log_le_tangent (hc t) hst
      have hb : 0 < β ^ t := by positivity
      have : β ^ t * ((c t - cakePath β R₀ t) / cakePath β R₀ t) =
          (c t - cakePath β R₀ t) / ((1 - β) * R₀) := by
        simp only [cakePath]; field_simp
      simp only [hg]
      nlinarith [mul_le_mul_of_nonneg_left h hb.le]
    have keys : β ^ s * Real.log (c s) = g s - δ := by
      have : β ^ s * ((c s - cakePath β R₀ s) / cakePath β R₀ s) =
          (c s - cakePath β R₀ s) / ((1 - β) * R₀) := by
        simp only [cakePath]; field_simp
      simp only [hg, hδ]; linarith
    have hsT : s ∈ range T := mem_range.mpr hT
    calc ∑ t ∈ range T, β ^ t * Real.log (c t)
        = β ^ s * Real.log (c s) + ∑ t ∈ (range T).erase s, β ^ t * Real.log (c t) :=
          (add_sum_erase _ _ hsT).symm
      _ ≤ (g s - δ) + ∑ t ∈ (range T).erase s, g t := by
          rw [keys]; gcongr with t; exact key t
      _ = ∑ t ∈ range T, g t - δ := by rw [← add_sum_erase _ _ hsT]; ring
      _ = ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) +
            (∑ t ∈ range T, c t - (R₀ - β ^ T * R₀)) / ((1 - β) * R₀) - δ := by
          simp only [hg]
          rw [sum_add_distrib, ← sum_div, sum_sub_distrib, cake_partial_sum]
      _ ≤ ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) +
            (R₀ - (R₀ - β ^ T * R₀)) / ((1 - β) * R₀) - δ := by
          gcongr
          exact hsum T
      _ = _ := by field_simp; ring
  have hle : U ≤ Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2 - δ := by
    have hU' : HasSum (fun t => β ^ t * Real.log (cakePath β R₀ t) - δ * (if t = 0 then 1 else 0))
        (Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2 - δ * 1) :=
      (cake_utility_hasSum hβ0 hβ1 hR).sub ((hasSum_ite_eq 0 (1 : ℝ)).mul_left δ)
    rw [mul_one] at hU'
    refine sust_hasSum_le_of_partial hU hU' (ε := fun T => β ^ T / (1 - β)) ?_ ?_
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).div_const (1 - β)
    · filter_upwards [eventually_gt_atTop s] with T hT
      have h0 : 0 ∈ range T := mem_range.mpr (by omega)
      rw [sum_sub_distrib, ← mul_sum, sum_ite_eq' (range T) 0]
      simp only [h0, ↓reduceIte]
      linarith [hbound T hT]
  linarith

/-- AKMM, p. 776, reusing Stokey–Lucas Exercise 5.2b (`DeterministicApplications`): the SLP
cake-eating policy `g(x) = βx` leaves `β^t R₀` after `t` periods, so its consumption is the
book's path, and SLP prove it optimal in their formulation. -/
theorem cake_slp (hβ0 : 0 < β) (hβ1 : β < 1)
    (k₀ : StokeyLucasPrescott.DeterministicApplications.PosR) (t : ℕ) :
    ((StokeyLucasPrescott.DeterministicApplications.logPolicy 1 β one_pos hβ0)^[t] k₀).1 =
        β ^ t * k₀.1 ∧
      ((StokeyLucasPrescott.DeterministicApplications.logPolicy 1 β one_pos hβ0)^[t] k₀).1 -
        ((StokeyLucasPrescott.DeterministicApplications.logPolicy 1 β one_pos hβ0)^[t + 1]
          k₀).1 = cakePath β k₀.1 t ∧
      StokeyLucasPrescott.DeterministicApplications.total
          (StokeyLucasPrescott.DeterministicApplications.logF 1) β
          (fun s => (StokeyLucasPrescott.DeterministicApplications.logPolicy 1 β one_pos hβ0)^[s]
            k₀) =
        StokeyLucasPrescott.DeterministicApplications.vstar
          (StokeyLucasPrescott.DeterministicApplications.logΓ 1)
          (StokeyLucasPrescott.DeterministicApplications.logF 1) β k₀ := by
  have hit : ∀ s, ((StokeyLucasPrescott.DeterministicApplications.logPolicy 1 β one_pos
      hβ0)^[s] k₀).1 = β ^ s * k₀.1 := by
    intro s
    induction s with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', StokeyLucasPrescott.DeterministicApplications.cake_policy
        hβ0, ih, pow_succ]
      ring
  refine ⟨hit t, ?_, StokeyLucasPrescott.DeterministicApplications.ex_5_2b_policy hβ0 hβ1 k₀⟩
  rw [hit, hit, cakePath, pow_succ]
  ring

/-- AKMM, p. 776: if the owner's sales `e ≥ 0` (with `Σ e_t = R`) maximise income
`Σ p̂_t e_t` among such sales plans, then a date with positive sales carries the highest
Arrow–Debreu price. -/
theorem hotelling_price_max {p e : ℕ → ℝ} {R I : ℝ} (he : ∀ t, 0 ≤ e t) (hR : HasSum e R)
    (hI : HasSum (fun t => p t * e t) I)
    (hmax : ∀ e' : ℕ → ℝ, (∀ t, 0 ≤ e' t) → HasSum e' R → ∀ I',
      HasSum (fun t => p t * e' t) I' → I' ≤ I) {t : ℕ} (ht : 0 < e t) (s : ℕ) :
    p s ≤ p t := by
  set e' : ℕ → ℝ := fun u => e u + (if u = s then e t else 0) - (if u = t then e t else 0)
  have he' : ∀ u, 0 ≤ e' u := by
    intro u
    simp only [e']
    by_cases hut : u = t
    · subst hut; split_ifs <;> linarith
    · have := he u
      simp only [hut, ↓reduceIte, sub_zero]
      split_ifs <;> linarith
  have hR' : HasSum e' R := by
    have := (hR.add (hasSum_ite_eq s (e t))).sub (hasSum_ite_eq t (e t))
    simpa using this
  have hI' : HasSum (fun u => p u * e' u) (I + p s * e t - p t * e t) := by
    have h1 := (hasSum_ite_eq s (e t)).mul_left (p s)
    have h2 := (hasSum_ite_eq t (e t)).mul_left (p t)
    convert (hI.add h1).sub h2 using 1
    funext u
    simp only [e']
    split_ifs with h1 h2 <;> (try simp_all)
    ring
  have := hmax e' he' hR' _ hI'
  nlinarith

/-- AKMM, p. 776: "the price has to be the same; otherwise the consumer would sell all of the
resource at the date with the highest price": with positive sales at every date the
Arrow–Debreu price is constant. -/
theorem hotelling_price_const {p e : ℕ → ℝ} {R I : ℝ} (he : ∀ t, 0 < e t) (hR : HasSum e R)
    (hI : HasSum (fun t => p t * e t) I)
    (hmax : ∀ e' : ℕ → ℝ, (∀ t, 0 ≤ e' t) → HasSum e' R → ∀ I',
      HasSum (fun t => p t * e' t) I' → I' ≤ I) (s t : ℕ) : p s = p t :=
  le_antisymm (hotelling_price_max (fun u => (he u).le) hR hI hmax (he t) s)
    (hotelling_price_max (fun u => (he u).le) hR hI hmax (he s) t)

/-- AKMM, p. 776: the consumer's first-order conditions at the planner's path:
`β^t/c*_t = 1/((1 − β)R₀)` at every date, so with a constant price the multiplier is constant
and `p̂_{t+1}/p̂_t = βc_t/c_{t+1}` holds with `p̂_{t+1} = p̂_t`. -/
theorem cake_market_foc (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) (t : ℕ) :
    β ^ t / cakePath β R₀ t = 1 / ((1 - β) * R₀) ∧
      β * cakePath β R₀ t / cakePath β R₀ (t + 1) = 1 := by
  have h1β : 0 < 1 - β := by linarith
  constructor
  · simp only [cakePath]; field_simp
  · simp only [cakePath, pow_succ]; field_simp

/-- AKMM, pp. 776: the competitive equilibrium of the cake economy. At a constant Arrow–Debreu
price `p̂ > 0`: (i) every sales plan exhausting the cake earns the same income `p̂R₀`, so selling
the planner's path maximises income; (ii) a consumer with that income who buys any positive plan
within the budget gets at most the planner's utility; (iii) markets clear with `c = e = c*`. So
markets deliver the planner's allocation. -/
theorem cake_market_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {ph : ℝ}
    (hp : 0 < ph) :
    HasSum (fun t => ph * cakePath β R₀ t) (ph * R₀) ∧
      (∀ e' : ℕ → ℝ, HasSum e' R₀ → HasSum (fun t => ph * e' t) (ph * R₀)) ∧
      ∀ (c : ℕ → ℝ) (U : ℝ), (∀ t, 0 < c t) → (∀ T, ∑ t ∈ range T, ph * c t ≤ ph * R₀) →
        HasSum (fun t => β ^ t * Real.log (c t)) U →
        U ≤ Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2 := by
  refine ⟨(cake_hasSum hβ0.le hβ1 R₀).mul_left ph, fun e' he' => he'.mul_left ph,
    fun c U hc hbud hU => cake_optimal hβ0 hβ1 hR hc (fun T => ?_) hU⟩
  have := hbud T
  rw [← mul_sum] at this
  exact le_of_mul_le_mul_left this hp

/-- AKMM, p. 777: "`p^o_t > 0` for all `t`": the Hotelling rent is positive. If the consumer's
problem — maximise `Σβ^t log c_t` over positive plans with `Σ p̂_t c_t ≤ I` — has a solution
`c`, then every price is positive (otherwise consuming one more unit at a date with
`p̂_t ≤ 0` is affordable and strictly better). -/
theorem hotelling_rent_pos (hβ0 : 0 < β) {p c : ℕ → ℝ} {I B U : ℝ} (hc : ∀ t, 0 < c t)
    (hB : HasSum (fun t => p t * c t) B) (hBI : B ≤ I)
    (hU : HasSum (fun t => β ^ t * Real.log (c t)) U)
    (hopt : ∀ c' : ℕ → ℝ, (∀ t, 0 < c' t) → ∀ B' U', HasSum (fun t => p t * c' t) B' →
      B' ≤ I → HasSum (fun t => β ^ t * Real.log (c' t)) U' → U' ≤ U) (t : ℕ) :
    0 < p t := by
  by_contra hpt
  rw [not_lt] at hpt
  set c' : ℕ → ℝ := fun u => c u + if u = t then 1 else 0
  have hc' : ∀ u, 0 < c' u := fun u => by
    simp only [c']; split_ifs <;> linarith [hc u]
  have hB' : HasSum (fun u => p u * c' u) (B + p t * 1) := by
    convert hB.add ((hasSum_ite_eq t (1 : ℝ)).mul_left (p t)) using 1
    funext u; simp only [c']; split_ifs with h
    · subst h; ring
    · simp
  set gain := β ^ t * (Real.log (c t + 1) - Real.log (c t))
  have hgain : 0 < gain := by
    have : Real.log (c t) < Real.log (c t + 1) :=
      Real.log_lt_log (hc t) (by linarith)
    have : 0 < β ^ t := by positivity
    simp only [gain]; nlinarith
  have hU' : HasSum (fun u => β ^ u * Real.log (c' u)) (U + gain) := by
    convert hU.add ((hasSum_ite_eq t gain)) using 1
    funext u; simp only [c', gain]; split_ifs with h
    · subst h; ring
    · simp
  have := hopt c' hc' _ _ hB' (by linarith) hU'
  linarith

/-- AKMM, p. 776, the Hotelling rule: with Arrow–Debreu prices `p̂_t = p^o_t p_t` constant
(`p_t` the price of a second good), the spot price satisfies `p^o_t = (p_{t+1}/p_t)p^o_{t+1}`,
i.e. `p^o_{t+1} = (1 + r_t)p^o_t` with the gross real rate `1 + r_t = p_t/p_{t+1}`. -/
theorem hotelling_rule {po p : ℕ → ℝ} (hp : ∀ t, 0 < p t)
    (hconst : ∀ t, po t * p t = po (t + 1) * p (t + 1)) (t : ℕ) :
    po t = p (t + 1) / p t * po (t + 1) ∧ po (t + 1) = p t / p (t + 1) * po t := by
  have h0 := (hp t).ne'
  have h1 := (hp (t + 1)).ne'
  constructor
  · field_simp; linarith [hconst t]
  · field_simp; linarith [hconst t]

/-- AKMM, p. 778: with extraction costs, the owner is indifferent between extracting at `t` and
`t + 1` exactly when `p_t − mc_t = (p_{t+1} − mc_{t+1})/(1 + r_t)`: if the split `(x, y)` of a
given total `x + y = Q` between the two dates maximises discounted profit, with both parts
positive, the condition holds. -/
theorem hotelling_cost_indifference {pt mct pt1 mct1 r x y : ℝ} (hr : 0 < 1 + r) (hx : 0 < x)
    (hy : 0 < y)
    (hmax : ∀ x' y', 0 ≤ x' → 0 ≤ y' → x' + y' = x + y →
      (pt - mct) * x' + (pt1 - mct1) * y' / (1 + r) ≤
        (pt - mct) * x + (pt1 - mct1) * y / (1 + r)) :
    pt - mct = (pt1 - mct1) / (1 + r) := by
  have h1 := hmax 0 (x + y) le_rfl (by linarith) (by ring)
  have h2 := hmax (x + y) 0 (by linarith) le_rfl (by ring)
  have e1 : (pt1 - mct1) * (x + y) / (1 + r) = (pt1 - mct1) * y / (1 + r) +
      (pt1 - mct1) / (1 + r) * x := by field_simp; ring
  have e2 : (pt1 - mct1) * y / (1 + r) = (pt1 - mct1) / (1 + r) * y := by ring
  rw [e1] at h1
  rw [e2] at h1 h2
  simp only [zero_add, mul_zero, zero_div, add_zero] at h1 h2
  have k1 : ((pt1 - mct1) / (1 + r) - (pt - mct)) * x ≤ 0 := by nlinarith
  have k2 : ((pt - mct) - (pt1 - mct1) / (1 + r)) * y ≤ 0 := by nlinarith
  have := nonpos_of_mul_nonpos_left k1 hx
  have := nonpos_of_mul_nonpos_left k2 hy
  linarith

/-- AKMM, p. 778: the indifference condition implies
`p_{t+1}/p_t = 1 + r_t + (mc_{t+1} − (1 + r_t)mc_t)/p_t`. -/
theorem hotelling_cost_rule {pt mct pt1 mct1 r : ℝ} (hr : 0 < 1 + r) (hp : pt ≠ 0)
    (h : pt - mct = (pt1 - mct1) / (1 + r)) :
    pt1 / pt = 1 + r + (mct1 - (1 + r) * mct) / pt := by
  have : pt1 = (1 + r) * (pt - mct) + mct1 := by
    rw [h]; field_simp; ring
  rw [this]
  field_simp
  ring

/-- AKMM, p. 769: the oil owner with log utility and income `p_t e_t` from any positive prices:
the extraction path `e_t = (1 − β)β^t R₀`, i.e. `e_t = (1 − β)R_t`, `R_{t+1} = βR_t`, beats every
positive extraction plan within the stock, up to `β^T/(1 − β)` at every horizon (prices cancel
because `log(p_t e_t) = log p_t + log e_t`). -/
theorem oil_owner_overtake (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {p e : ℕ → ℝ}
    (hp : ∀ t, 0 < p t) (he : ∀ t, 0 < e t) (hsum : ∀ T, ∑ t ∈ range T, e t ≤ R₀) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * Real.log (p t * e t) ≤
      ∑ t ∈ range T, β ^ t * Real.log (p t * cakePath β R₀ t) + β ^ T / (1 - β) := by
  have hstar : ∀ t, 0 < cakePath β R₀ t := fun t => by
    have : 0 < 1 - β := by linarith
    unfold cakePath; positivity
  have hsplit : ∀ x : ℕ → ℝ, (∀ t, 0 < x t) → ∑ t ∈ range T, β ^ t * Real.log (p t * x t) =
      ∑ t ∈ range T, β ^ t * Real.log (p t) + ∑ t ∈ range T, β ^ t * Real.log (x t) := by
    intro x hx
    rw [← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [Real.log_mul (hp t).ne' (hx t).ne']
    ring
  rw [hsplit e he, hsplit _ hstar]
  have := cake_overtake hβ0 hβ1 hR he hsum T
  linarith

/-- AKMM, p. 769: "The maximization of `Σβ^t log(C_{o,t})` subject to this constraint and (25.25)
straightforwardly delivers `e_{o,t} = (1 − β)R_t`": among positive plans within the stock whose
utility converges, the path `(1 − β)β^t R₀` is optimal for the oil owner. -/
theorem oil_owner_optimal (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {p e : ℕ → ℝ}
    {U Us : ℝ} (hp : ∀ t, 0 < p t) (he : ∀ t, 0 < e t)
    (hsum : ∀ T, ∑ t ∈ range T, e t ≤ R₀)
    (hU : HasSum (fun t => β ^ t * Real.log (p t * e t)) U)
    (hUs : HasSum (fun t => β ^ t * Real.log (p t * cakePath β R₀ t)) Us) : U ≤ Us := by
  have h1β : 0 < 1 - β := by linarith
  refine sust_hasSum_le_of_partial hU hUs (ε := fun T => β ^ T / (1 - β)) ?_
    (Eventually.of_forall fun T => oil_owner_overtake hβ0 hβ1 hR hp he hsum T)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).div_const (1 - β)

end AKMM.Sustainability
