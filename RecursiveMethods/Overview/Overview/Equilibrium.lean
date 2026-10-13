/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Overview.Technology

/-!
# Competitive equilibrium in the finite-horizon growth economy

SLP §2.3, pp. 22–29, and Exercises 2.8–2.10.

Households own capital and labour, rent them to firms, and trade in one market in period 0 at
prices `p_t` (goods), `r_t` (capital rental) and `w_t` (labour), in units of period-`t` goods.

* `firm_profit_le`: at `r = F_k(k*, 1)` and `w = F(k*, 1) − k* F_k(k*, 1)` every input pair earns at
  most zero profit, which `(k*, 1)` attains: the firm's problem (8) is solved and `π = 0`.
* `first_welfare` (SLP pp. 26–27): a competitive equilibrium allocation solves the planner's
  problem.
* `household_optimal`, `second_welfare` (Ex 2.8): the planner's Euler path with the prices
  (20)–(22) is a competitive equilibrium.
* `firmOwned_firm_optimal`, `firmOwned_household_optimal` (Ex 2.9): the same quantities and prices
  form an equilibrium when firms own the capital and households own shares.
* `sequential_budget`, `sequential_household_optimal` (Ex 2.10): with sequential spot markets,
  one-period bonds at `q_t = 1/f′(k*_{t+1})` and perfect foresight, the same allocation with zero
  bond holdings is optimal for the household.
-/

open Finset Set Filter Topology

namespace StokeyLucasPrescott.Overview

/-! ### The firm -/

/-- **The firm's problem (8).** If `F` is homogeneous of degree one with `k ↦ F(k, 1)` concave, then
at `r = F_k(k*, 1)`, `w = F(k*, 1) − k* F_k(k*, 1)`, every `(k, n) ≥ 0` has
`F(k, n) − rk − wn ≤ 0`. -/
theorem firm_profit_le {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ}
    (hom : ∀ l k n : ℝ, 0 < l → 0 ≤ k → 0 ≤ n → F (l * k) (l * n) = l * F k n)
    (hconc : ConcaveOn ℝ (Ici 0) fun k => F k 1)
    (hcont0 : ∀ k, 0 ≤ k → Tendsto (fun n => F k n) (𝓝[>] 0) (𝓝 (F k 0)))
    {ks : ℝ} (hks : 0 < ks) (hd : HasDerivAt (fun k => F k 1) (Fk ks) ks)
    {k n : ℝ} (hk : 0 ≤ k) (hn : 0 ≤ n) :
    F k n - Fk ks * k - (F ks 1 - ks * Fk ks) * n ≤ 0 := by
  -- for `n > 0`, homogeneity and the tangent line at `k*`
  have hpos : ∀ n, 0 < n → F k n - Fk ks * k - (F ks 1 - ks * Fk ks) * n ≤ 0 := fun n hn => by
    have h1 := hom n (k / n) 1 hn (by positivity) zero_le_one
    rw [show n * (k / n) = k by field_simp, mul_one] at h1
    have h2 := concave_le_tangent hconc (Set.mem_Ici.2 hks.le)
      (Set.mem_Ici.2 (by positivity : 0 ≤ k / n))
      hd
    have h3 := mul_le_mul_of_nonneg_left h2 hn.le
    rw [h1]
    have e : n * (F ks 1 + Fk ks * (k / n - ks)) = Fk ks * k + (F ks 1 - ks * Fk ks) * n := by
      field_simp
      ring
    linarith
  rcases hn.eq_or_lt with rfl | hn
  · -- at `n = 0`, pass to the limit
    have hlim : Tendsto (fun n => F k n - Fk ks * k - (F ks 1 - ks * Fk ks) * n) (𝓝[>] 0)
        (𝓝 (F k 0 - Fk ks * k - (F ks 1 - ks * Fk ks) * 0)) :=
      ((hcont0 k hk).sub tendsto_const_nhds).sub
        (tendsto_const_nhds.mul (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id))
    exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun n hn => hpos n hn)
  · exact hpos n hn

/-- **Zero profit.** `(k*, 1)` earns zero profit at these prices. -/
theorem firm_profit_zero (F : ℝ → ℝ → ℝ) (Fk : ℝ → ℝ) (ks : ℝ) :
    F ks 1 - Fk ks * ks - (F ks 1 - ks * Fk ks) * 1 = 0 := by ring

/-! ### Households and equilibrium -/

/-- Lifetime utility `∑_{t=0}^T βᵗ U(c_t)`. -/
def utility (β : ℝ) (U : ℝ → ℝ) (T : ℕ) (c : ℕ → ℝ) : ℝ := ∑ t ∈ range (T + 1), β ^ t * U (c t)

/-- The household's feasible set (13): consumption in the domain of `U`, `k_{t+1} ≥ 0` and
`k₀ = x₀`. -/
def HHFeasible (D : Set ℝ) (x₀ : ℝ) (T : ℕ) (c k : ℕ → ℝ) : Prop :=
  k 0 = x₀ ∧ ∀ t ≤ T, c t ∈ D ∧ 0 ≤ k (t + 1)

/-- The household's budget constraint (12), with profit income `prof`. -/
def HHBudget (p r w : ℕ → ℝ) (δ prof : ℝ) (T : ℕ) (c k : ℕ → ℝ) : Prop :=
  ∑ t ∈ range (T + 1), p t * (c t + k (t + 1) - (r t + 1 - δ) * k t - w t) ≤ prof

variable (D : Set ℝ) (β : ℝ) (U : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (δ x₀ : ℝ) (T : ℕ)
  (p r w c k : ℕ → ℝ) in
/-- A competitive equilibrium (SLP p. 25): firms maximize profit each period, households maximize
utility over their budget set given equilibrium profits, and goods markets clear. -/
structure IsEquilibrium : Prop where
  firm : ∀ t ≤ T, ∀ k' n', 0 ≤ k' → 0 ≤ n' →
    F k' n' - r t * k' - w t * n' ≤ F (k t) 1 - r t * k t - w t
  feasible : HHFeasible D x₀ T c k
  budget : HHBudget p r w δ (∑ t ∈ range (T + 1), p t * (F (k t) 1 - r t * k t - w t)) T c k
  household : ∀ c' k', HHFeasible D x₀ T c' k' →
    HHBudget p r w δ (∑ t ∈ range (T + 1), p t * (F (k t) 1 - r t * k t - w t)) T c' k' →
    utility β U T c' ≤ utility β U T c
  clear : ∀ t ≤ T, c t + k (t + 1) - (1 - δ) * k t = F (k t) 1

/-- **The first welfare theorem** (SLP pp. 26–27): with nonnegative goods prices, a competitive
equilibrium allocation maximizes the planner's objective over all allocations with
`c_t + k_{t+1} ≤ f(k_t)`. -/
theorem first_welfare {D : Set ℝ} {β : ℝ} {U : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {δ x₀ : ℝ} {T : ℕ}
    {p r w c k : ℕ → ℝ} (he : IsEquilibrium D β U F δ x₀ T p r w c k) (hp : ∀ t, 0 ≤ p t)
    (hx₀ : 0 ≤ x₀) {c' k' : ℕ → ℝ} (hf : HHFeasible D x₀ T c' k')
    (hres : ∀ t ≤ T, c' t + k' (t + 1) ≤ goods F δ (k' t)) :
    utility β U T c' ≤ utility β U T c := by
  refine he.household c' k' hf ?_
  unfold HHBudget
  refine sum_le_sum fun t ht => ?_
  have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
  have hk't : 0 ≤ k' t := by
    rcases t with _ | t
    · rw [hf.1]; exact hx₀
    · exact (hf.2 t (by omega)).2
  have hfirm := he.firm t htT (k' t) 1 hk't zero_le_one
  have hr := hres t htT
  simp only [goods] at hr
  apply mul_le_mul_of_nonneg_left _ (hp t)
  linarith

/-! ### Exercise 2.8: the planner's allocation is an equilibrium -/

/-- The goods prices (20): `p₀` given, `p_t = p_{t−1}/f′(k*_t)`. -/
noncomputable def priceP (p₀ : ℝ) (fd : ℝ → ℝ) (ks : ℕ → ℝ) : ℕ → ℝ
  | 0 => p₀
  | t + 1 => priceP p₀ fd ks t / fd (ks (t + 1))

theorem priceP_pos {p₀ : ℝ} {fd : ℝ → ℝ} {ks : ℕ → ℝ} (hp₀ : 0 < p₀)
    (hfd : ∀ t, 0 < fd (ks t)) (t : ℕ) : 0 < priceP p₀ fd ks t := by
  induction t with
  | zero => exact hp₀
  | succ t ih => exact div_pos ih (hfd (t + 1))

/-- **Ex 2.8 (household).** At the prices (20)–(22), the planner's consumption maximizes the
household's utility over its budget set (11)–(13) (with zero profits). -/
theorem household_optimal {D : Set ℝ} {U U' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ}
    {β δ x₀ p₀ : ℝ} {T : ℕ} {ks : ℕ → ℝ} (hβ : 0 ≤ β) (hp₀ : 0 < p₀) (hU : ConcaveOn ℝ D U)
    (hks0 : ks 0 = x₀)
    (hcs : ∀ t ≤ T, goods F δ (ks t) - ks (t + 1) ∈ D)
    (hUd : ∀ t ≤ T, HasDerivAt U (U' (goods F δ (ks t) - ks (t + 1)))
      (goods F δ (ks t) - ks (t + 1)))
    (hU'0 : 0 ≤ U' (goods F δ (ks 0) - ks 1))
    (hfd : ∀ t, 0 < Fk (ks t) + (1 - δ))
    (heuler : ∀ t, 1 ≤ t → t ≤ T → β * (Fk (ks t) + (1 - δ)) * U' (goods F δ (ks t) - ks (t + 1)) =
      U' (goods F δ (ks (t - 1)) - ks t))
    (hT : ks (T + 1) = 0) {c k : ℕ → ℝ} (hf : HHFeasible D x₀ T c k)
    (hb : HHBudget (priceP p₀ (fun k => Fk k + (1 - δ)) ks) (fun t => Fk (ks t))
      (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ 0 T c k) :
    utility β U T c ≤ utility β U T fun t => goods F δ (ks t) - ks (t + 1) := by
  set p := priceP p₀ (fun k => Fk k + (1 - δ)) ks
  set cs : ℕ → ℝ := fun t => goods F δ (ks t) - ks (t + 1)
  set d : ℕ → ℝ := fun t => k t - ks t
  set lam := U' (cs 0) / p₀
  have hp : ∀ t, 0 < p t := priceP_pos hp₀ hfd
  -- marginal utilities are proportional to prices: `βᵗ U′(c*_t) = λ p_t`
  have hprop : ∀ t ≤ T, β ^ t * U' (cs t) = lam * p t := by
    intro t ht
    induction t with
    | zero => simp [lam, p, priceP, hp₀.ne']
    | succ t ih =>
      have he := heuler (t + 1) (by omega) ht
      simp only [Nat.add_sub_cancel] at he
      have ih' := ih (by omega)
      simp only [p, priceP]
      have hne := (hfd (t + 1)).ne'
      field_simp
      simp only [p] at ih'
      rw [pow_succ]
      calc β ^ t * β * U' (cs (t + 1)) * (Fk (ks (t + 1)) + (1 - δ))
          = β ^ t * (β * (Fk (ks (t + 1)) + (1 - δ)) * U' (cs (t + 1))) := by ring
        _ = β ^ t * U' (cs t) := by rw [he]
        _ = lam * priceP p₀ (fun k => Fk k + (1 - δ)) ks t := ih'
  have hlam : 0 ≤ lam := div_nonneg hU'0 hp₀.le
  -- concavity of `U`
  have hconc : utility β U T c - utility β U T cs ≤
      lam * ∑ t ∈ range (T + 1), p t * (c t - cs t) := by
    unfold utility
    rw [← sum_sub_distrib, mul_sum]
    refine sum_le_sum fun t ht => ?_
    have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have h1 := concave_le_tangent hU (hcs t htT) (hf.2 t htT).1 (hUd t htT)
    have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ t)
    have h3 := hprop t htT
    calc β ^ t * U (c t) - β ^ t * U (cs t) ≤ β ^ t * U' (cs t) * (c t - cs t) := by
          simp only [cs] at h2 ⊢; nlinarith
      _ = lam * (p t * (c t - cs t)) := by rw [h3]; ring
  -- the budget, against the planner's allocation which exhausts it
  have hzero : ∀ t, cs t + ks (t + 1) - (Fk (ks t) + 1 - δ) * ks t -
      (F (ks t) 1 - ks t * Fk (ks t)) = 0 := fun t => by simp only [cs, goods]; ring
  have hbud : ∑ t ∈ range (T + 1), p t * (c t - cs t) ≤
      ∑ t ∈ range (T + 1), p t * ((Fk (ks t) + (1 - δ)) * d t - d (t + 1)) := by
    unfold HHBudget at hb
    have : ∑ t ∈ range (T + 1), p t * (c t - cs t) -
        ∑ t ∈ range (T + 1), p t * ((Fk (ks t) + (1 - δ)) * d t - d (t + 1)) =
        ∑ t ∈ range (T + 1), p t * (c t + k (t + 1) - (Fk (ks t) + 1 - δ) * k t -
          (F (ks t) 1 - ks t * Fk (ks t))) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun t _ => ?_
      have := hzero t
      simp only [d]
      linear_combination (-p t) * this
    beta_reduce at hb
    linarith
  -- telescoping
  have hd0 : d 0 = 0 := by simp only [d, hf.1, hks0, sub_self]
  have htel := sum_telescope (a := p) (g := fun t => Fk (ks t) + (1 - δ)) (d := d) hd0 T
    fun t h1 _ => by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      simp only [p, priceP, Nat.add_sub_cancel]
      field_simp [(hfd (s + 1)).ne']
  have hlast : 0 ≤ p T * d (T + 1) := by
    simp only [d, hT, sub_zero]
    exact mul_nonneg (hp T).le (hf.2 T le_rfl).2
  have := mul_le_mul_of_nonneg_left (hbud.trans (htel.le.trans
    (show -(p T * d (T + 1)) ≤ 0 by linarith))) hlam
  linarith

/-- **Ex 2.8 (second welfare theorem).** The planner's Euler path, with the prices (20)–(22), is a
competitive equilibrium. -/
theorem second_welfare {D : Set ℝ} {U U' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ}
    {β δ x₀ p₀ : ℝ} {T : ℕ} {ks : ℕ → ℝ} (hβ : 0 ≤ β) (hp₀ : 0 < p₀) (hU : ConcaveOn ℝ D U)
    (hom : ∀ l k n : ℝ, 0 < l → 0 ≤ k → 0 ≤ n → F (l * k) (l * n) = l * F k n)
    (hconc : ConcaveOn ℝ (Ici 0) fun k => F k 1)
    (hcont0 : ∀ k, 0 ≤ k → Tendsto (fun n => F k n) (𝓝[>] 0) (𝓝 (F k 0)))
    (hderiv : ∀ t ≤ T, HasDerivAt (fun k => F k 1) (Fk (ks t)) (ks t))
    (hks : ∀ t ≤ T, 0 < ks t) (hks0 : ks 0 = x₀)
    (hcs : ∀ t ≤ T, goods F δ (ks t) - ks (t + 1) ∈ D)
    (hUd : ∀ t ≤ T, HasDerivAt U (U' (goods F δ (ks t) - ks (t + 1)))
      (goods F δ (ks t) - ks (t + 1)))
    (hU'0 : 0 ≤ U' (goods F δ (ks 0) - ks 1))
    (hfd : ∀ t, 0 < Fk (ks t) + (1 - δ))
    (heuler : ∀ t, 1 ≤ t → t ≤ T → β * (Fk (ks t) + (1 - δ)) * U' (goods F δ (ks t) - ks (t + 1)) =
      U' (goods F δ (ks (t - 1)) - ks t))
    (hT : ks (T + 1) = 0) :
    IsEquilibrium D β U F δ x₀ T (priceP p₀ (fun k => Fk k + (1 - δ)) ks) (fun t => Fk (ks t))
      (fun t => F (ks t) 1 - ks t * Fk (ks t)) (fun t => goods F δ (ks t) - ks (t + 1)) ks := by
  have hprofit : ∑ t ∈ range (T + 1), priceP p₀ (fun k => Fk k + (1 - δ)) ks t *
      (F (ks t) 1 - Fk (ks t) * ks t - (F (ks t) 1 - ks t * Fk (ks t))) = 0 :=
    sum_eq_zero fun t _ => by ring
  have hfeas : HHFeasible D x₀ T (fun t => goods F δ (ks t) - ks (t + 1)) ks :=
    ⟨hks0, fun t ht => ⟨hcs t ht, by
      rcases (Nat.lt_or_ge t T) with h | h
      · exact (hks (t + 1) (by omega)).le
      · rw [show t = T by omega, hT]⟩⟩
  refine ⟨fun t ht k' n' hk' hn' => ?_, hfeas, ?_, fun c' k' hf hb => ?_, fun t _ => ?_⟩
  · have := firm_profit_le hom hconc hcont0 (hks t ht) (hderiv t ht) hk' hn'
    linarith
  · rw [hprofit]
    unfold HHBudget
    exact (sum_eq_zero fun t _ => by simp only [goods]; ring).le
  · rw [hprofit] at hb
    exact household_optimal hβ hp₀ hU hks0 hcs hUd hU'0 hfd heuler hT hf hb
  · simp only [goods]; ring

/-! ### Exercise 2.9: firms own the capital -/

/-- The firm's discounted profit when it owns the capital, invests `k_{t+1} − (1 − δ)k_t` and hires
labour `n_t`. -/
def firmValue (F : ℝ → ℝ → ℝ) (p w : ℕ → ℝ) (δ : ℝ) (T : ℕ) (k n : ℕ → ℝ) : ℝ :=
  ∑ t ∈ range (T + 1), p t * (F (k t) (n t) - w t * n t - (k (t + 1) - (1 - δ) * k t))

/-- **Ex 2.9 (firm).** At the prices (20) and (22), the planner's capital path with `n = 1`
maximizes the value of a firm that owns the capital, over all `k ≥ 0`, `n ≥ 0` with `k₀ = x₀`. -/
theorem firmOwned_firm_optimal {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ} {δ x₀ p₀ : ℝ} {T : ℕ}
    {ks : ℕ → ℝ} (hp₀ : 0 < p₀)
    (hom : ∀ l k n : ℝ, 0 < l → 0 ≤ k → 0 ≤ n → F (l * k) (l * n) = l * F k n)
    (hconc : ConcaveOn ℝ (Ici 0) fun k => F k 1)
    (hcont0 : ∀ k, 0 ≤ k → Tendsto (fun n => F k n) (𝓝[>] 0) (𝓝 (F k 0)))
    (hderiv : ∀ t ≤ T, HasDerivAt (fun k => F k 1) (Fk (ks t)) (ks t))
    (hks : ∀ t ≤ T, 0 < ks t) (hks0 : ks 0 = x₀) (hfd : ∀ t, 0 < Fk (ks t) + (1 - δ))
    (hT : ks (T + 1) = 0) {k n : ℕ → ℝ} (hk0 : k 0 = x₀) (hk : ∀ t ≤ T + 1, 0 ≤ k t)
    (hn : ∀ t ≤ T, 0 ≤ n t) :
    firmValue F (priceP p₀ (fun k => Fk k + (1 - δ)) ks)
        (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T k n ≤
      firmValue F (priceP p₀ (fun k => Fk k + (1 - δ)) ks)
        (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T ks fun _ => 1 := by
  set p := priceP p₀ (fun k => Fk k + (1 - δ)) ks
  set d : ℕ → ℝ := fun t => k t - ks t
  have hp : ∀ t, 0 < p t := priceP_pos hp₀ hfd
  -- each period, output is bounded by factor payments at the equilibrium prices
  have hbound : firmValue F p (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T k n -
      firmValue F p (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T ks (fun _ => 1) ≤
      ∑ t ∈ range (T + 1), p t * ((Fk (ks t) + (1 - δ)) * d t - d (t + 1)) := by
    unfold firmValue
    rw [← sum_sub_distrib]
    refine sum_le_sum fun t ht => ?_
    have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have hfirm := firm_profit_le hom hconc hcont0 (hks t htT) (hderiv t htT) (hk t (by omega))
      (hn t htT)
    have := mul_le_mul_of_nonneg_left hfirm (hp t).le
    simp only [d]
    nlinarith
  have hd0 : d 0 = 0 := by simp only [d, hk0, hks0, sub_self]
  have htel := sum_telescope (a := p) (g := fun t => Fk (ks t) + (1 - δ)) (d := d) hd0 T
    fun t h1 _ => by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      simp only [p, priceP, Nat.add_sub_cancel]
      field_simp [(hfd (s + 1)).ne']
  have hlast : 0 ≤ p T * d (T + 1) := by
    simp only [d, hT, sub_zero]
    exact mul_nonneg (hp T).le (hk (T + 1) le_rfl)
  linarith

/-- **Ex 2.9 (household).** With firms owning the capital, the household chooses consumption and
labour `n_t ≤ 1` subject to `∑ p_t (c_t − w_t n_t) ≤ V`, where `V` is the firm's value; the
planner's consumption is optimal. -/
theorem firmOwned_household_optimal {D : Set ℝ} {U U' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ}
    {β δ p₀ : ℝ} {T : ℕ} {ks : ℕ → ℝ} (hβ : 0 ≤ β) (hp₀ : 0 < p₀) (hU : ConcaveOn ℝ D U)
    (hconc : ConcaveOn ℝ (Ici 0) fun k => F k 1) (hF0 : 0 ≤ F 0 1)
    (hderiv : ∀ t ≤ T, HasDerivAt (fun k => F k 1) (Fk (ks t)) (ks t))
    (hks : ∀ t ≤ T, 0 < ks t)
    (hcs : ∀ t ≤ T, goods F δ (ks t) - ks (t + 1) ∈ D)
    (hUd : ∀ t ≤ T, HasDerivAt U (U' (goods F δ (ks t) - ks (t + 1)))
      (goods F δ (ks t) - ks (t + 1)))
    (hU'0 : 0 ≤ U' (goods F δ (ks 0) - ks 1))
    (hfd : ∀ t, 0 < Fk (ks t) + (1 - δ))
    (heuler : ∀ t, 1 ≤ t → t ≤ T → β * (Fk (ks t) + (1 - δ)) * U' (goods F δ (ks t) - ks (t + 1)) =
      U' (goods F δ (ks (t - 1)) - ks t))
    {c n : ℕ → ℝ} (hc : ∀ t ≤ T, c t ∈ D) (hn : ∀ t ≤ T, n t ≤ 1)
    (hb : ∑ t ∈ range (T + 1), priceP p₀ (fun k => Fk k + (1 - δ)) ks t *
      (c t - (F (ks t) 1 - ks t * Fk (ks t)) * n t) ≤
      firmValue F (priceP p₀ (fun k => Fk k + (1 - δ)) ks)
        (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T ks fun _ => 1) :
    utility β U T c ≤ utility β U T fun t => goods F δ (ks t) - ks (t + 1) := by
  set p := priceP p₀ (fun k => Fk k + (1 - δ)) ks
  set cs : ℕ → ℝ := fun t => goods F δ (ks t) - ks (t + 1)
  set lam := U' (cs 0) / p₀
  have hp : ∀ t, 0 < p t := priceP_pos hp₀ hfd
  have hprop : ∀ t ≤ T, β ^ t * U' (cs t) = lam * p t := by
    intro t ht
    induction t with
    | zero => simp [lam, p, priceP, hp₀.ne']
    | succ t ih =>
      have he := heuler (t + 1) (by omega) ht
      simp only [Nat.add_sub_cancel] at he
      have ih' := ih (by omega)
      simp only [p, priceP]
      have hne := (hfd (t + 1)).ne'
      field_simp
      simp only [p] at ih'
      rw [pow_succ]
      calc β ^ t * β * U' (cs (t + 1)) * (Fk (ks (t + 1)) + (1 - δ))
          = β ^ t * (β * (Fk (ks (t + 1)) + (1 - δ)) * U' (cs (t + 1))) := by ring
        _ = β ^ t * U' (cs t) := by rw [he]
        _ = lam * priceP p₀ (fun k => Fk k + (1 - δ)) ks t := ih'
  have hlam : 0 ≤ lam := div_nonneg hU'0 hp₀.le
  -- wages are nonnegative: `F(k*, 1) − k* F_k ≥ F(0, 1) ≥ 0` by concavity
  have hw : ∀ t ≤ T, 0 ≤ F (ks t) 1 - ks t * Fk (ks t) := fun t ht => by
    have := concave_le_tangent hconc (Set.mem_Ici.2 (hks t ht).le) (Set.mem_Ici.2 le_rfl)
      (hderiv t ht)
    linarith
  have hconcU : utility β U T c - utility β U T cs ≤
      lam * ∑ t ∈ range (T + 1), p t * (c t - cs t) := by
    unfold utility
    rw [← sum_sub_distrib, mul_sum]
    refine sum_le_sum fun t ht => ?_
    have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have h1 := concave_le_tangent hU (hcs t htT) (hc t htT) (hUd t htT)
    have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ t)
    have h3 := hprop t htT
    calc β ^ t * U (c t) - β ^ t * U (cs t) ≤ β ^ t * U' (cs t) * (c t - cs t) := by
          simp only [cs] at h2 ⊢; nlinarith
      _ = lam * (p t * (c t - cs t)) := by rw [h3]; ring
  -- the planner's consumption exhausts the budget at `n = 1`
  have hspend : ∑ t ∈ range (T + 1), p t * (c t - cs t) ≤ 0 := by
    have hfv : firmValue F p (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T ks (fun _ => 1) =
        ∑ t ∈ range (T + 1), p t * (cs t - (F (ks t) 1 - ks t * Fk (ks t))) := by
      unfold firmValue
      refine sum_congr rfl fun t _ => ?_
      simp only [cs, goods]
      ring
    have hlab : ∀ t ∈ range (T + 1), p t * (c t - (F (ks t) 1 - ks t * Fk (ks t))) ≤
        p t * (c t - (F (ks t) 1 - ks t * Fk (ks t)) * n t) := fun t ht => by
      have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
      have := mul_le_mul_of_nonneg_left (hn t htT) (hw t htT)
      exact mul_le_mul_of_nonneg_left (by linarith) (hp t).le
    have h1 := (sum_le_sum hlab).trans hb
    rw [hfv] at h1
    rw [← sub_nonpos, ← sum_sub_distrib] at h1
    have : ∑ t ∈ range (T + 1), p t * (c t - cs t) =
        ∑ t ∈ range (T + 1), (p t * (c t - (F (ks t) 1 - ks t * Fk (ks t))) -
          p t * (cs t - (F (ks t) 1 - ks t * Fk (ks t)))) :=
      sum_congr rfl fun t _ => by ring
    linarith
  have := mul_le_mul_of_nonneg_left hspend hlam
  linarith

/-! ### Exercise 2.10: sequential markets -/

/-- The present-value price of period-`t` goods implied by bond prices: `P₀ = 1`,
`P_{t+1} = P_t q_t`. -/
def pvPrice (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => pvPrice q t * q t

/-- The household's period-`t` budget constraint in sequential markets: goods, capital and
one-period bonds `b`, with `b₀ = 0`. -/
def SeqBudget (q r w : ℕ → ℝ) (δ : ℝ) (t : ℕ) (c k b : ℕ → ℝ) : Prop :=
  c t + k (t + 1) - (1 - δ) * k t + q t * b (t + 1) ≤ r t * k t + w t + b t

/-- **Sequential budgets imply the Arrow–Debreu budget.** If each period's budget holds, `b₀ = 0`
and `b_{T+1} = 0`, then `∑ P_t (c_t + k_{t+1} − (r_t + 1 − δ)k_t − w_t) ≤ 0` with
`P_t = ∏_{s<t} q_s`, `q ≥ 0`. -/
theorem sequential_budget {q r w : ℕ → ℝ} {δ : ℝ} {T : ℕ} {c k b : ℕ → ℝ} (hq : ∀ t, 0 ≤ q t)
    (hb : ∀ t ≤ T, SeqBudget q r w δ t c k b) (hb0 : b 0 = 0) (hbT : b (T + 1) = 0) :
    HHBudget (pvPrice q) r w δ 0 T c k := by
  have hP : ∀ t, 0 ≤ pvPrice q t := fun t => by
    induction t with
    | zero => simp [pvPrice]
    | succ t ih => exact mul_nonneg ih (hq t)
  -- weight each period's budget by `P_t`; the bond terms telescope
  have hsum : ∀ n ≤ T, ∑ t ∈ range (n + 1), pvPrice q t *
      (c t + k (t + 1) - (r t + 1 - δ) * k t - w t) ≤ -(pvPrice q (n + 1) * b (n + 1)) := by
    intro n hn
    induction n with
    | zero =>
      have h := mul_le_mul_of_nonneg_left (hb 0 (by omega)) (hP 0)
      simp only [sum_range_one, pvPrice, hb0, zero_add] at h ⊢
      linarith
    | succ n ih =>
      rw [sum_range_succ]
      have h := mul_le_mul_of_nonneg_left (hb (n + 1) hn) (hP (n + 1))
      have ih' := ih (by omega)
      simp only [pvPrice] at h ih' ⊢
      linear_combination ih' + h
  have := hsum T le_rfl
  rw [hbT, mul_zero, neg_zero] at this
  exact this

/-- **Ex 2.10.** In sequential markets with bond prices `q_t = 1/f′(k*_{t+1})` and the factor prices
(21)–(22), the planner's consumption is optimal for the household among all plans satisfying
the period budgets with `b₀ = b_{T+1} = 0`; the planner's allocation with `b ≡ 0` satisfies them,
so bond markets clear. -/
theorem sequential_household_optimal {D : Set ℝ} {U U' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ}
    {β δ x₀ : ℝ} {T : ℕ} {ks : ℕ → ℝ} (hβ : 0 ≤ β) (hU : ConcaveOn ℝ D U) (hks0 : ks 0 = x₀)
    (hcs : ∀ t ≤ T, goods F δ (ks t) - ks (t + 1) ∈ D)
    (hUd : ∀ t ≤ T, HasDerivAt U (U' (goods F δ (ks t) - ks (t + 1)))
      (goods F δ (ks t) - ks (t + 1)))
    (hU'0 : 0 ≤ U' (goods F δ (ks 0) - ks 1))
    (hfd : ∀ t, 0 < Fk (ks t) + (1 - δ))
    (heuler : ∀ t, 1 ≤ t → t ≤ T → β * (Fk (ks t) + (1 - δ)) * U' (goods F δ (ks t) - ks (t + 1)) =
      U' (goods F δ (ks (t - 1)) - ks t))
    (hT : ks (T + 1) = 0) {c k b : ℕ → ℝ} (hf : HHFeasible D x₀ T c k)
    (hb : ∀ t ≤ T, SeqBudget (fun t => 1 / (Fk (ks (t + 1)) + (1 - δ))) (fun t => Fk (ks t))
      (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ t c k b)
    (hb0 : b 0 = 0) (hbT : b (T + 1) = 0) :
    utility β U T c ≤ utility β U T fun t => goods F δ (ks t) - ks (t + 1) := by
  have hq : ∀ t, 0 ≤ 1 / (Fk (ks (t + 1)) + (1 - δ)) := fun t => (one_div_pos.2 (hfd _)).le
  have hAD := sequential_budget hq hb hb0 hbT
  -- the present-value prices are the prices (20) with `p₀ = 1`
  have hPeq : pvPrice (fun t => 1 / (Fk (ks (t + 1)) + (1 - δ))) =
      priceP 1 (fun k => Fk k + (1 - δ)) ks := by
    funext t
    induction t with
    | zero => rfl
    | succ t ih => simp only [pvPrice, priceP, ih]; ring
  rw [hPeq] at hAD
  exact household_optimal hβ one_pos hU hks0 hcs hUd hU'0 hfd heuler hT hf hAD

/-- **Ex 2.10 (bond-market clearing).** The planner's allocation with zero bond holdings satisfies
every period's budget with equality. -/
theorem sequential_planner_feasible {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ} {δ : ℝ} {ks : ℕ → ℝ}
    (q : ℕ → ℝ) (t : ℕ) :
    SeqBudget q (fun t => Fk (ks t)) (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ t
      (fun t => goods F δ (ks t) - ks (t + 1)) ks fun _ => 0 := by
  unfold SeqBudget goods
  ring_nf
  exact le_rfl

end StokeyLucasPrescott.Overview
