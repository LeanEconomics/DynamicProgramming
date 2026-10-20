/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.ConsumerRecursive

/-!
# The principle of optimality with recursive preferences

SLP Exercise 5.12a, p. 117: relate the sequence problem
`max u_W(c)` subject to `Σ Rᵗ(p·c_t) ≤ A` (1) to the functional equation (2), as Theorems
4.2–4.5 do for additive preferences. Here `u_W` is the utility of Exercise 5.11d, plans are
bounded sequences in `ℝˡ₊`, and `R < 1`.

* `planCost_cons`, `feasible_head`, `feasible_shift`: a plan is feasible from `A` iff its first
  choice is in `Γ(A)` and the rest is feasible from `R⁻¹(A − p·c₀)` (the budget recursion).
* `utility_le_value` (Theorems 4.2–4.3, upper half): with `W` nondecreasing in `z` (W4), every
  feasible plan has `u_W(c) ≤ v(A)`.
* `exists_plan_near` (lower half): following the policy for `n + 1` periods and consuming nothing
  afterwards is feasible and comes within `βⁿ⁺¹(‖u_W‖ + ‖v‖)` of `v(A)`.
* `ex_5_12a`: so `v(A) = sup{u_W(c) : c feasible from A}`, the supremum function.
* `ex_5_12a_optimal` (Theorem 4.5): a plan whose wealth path satisfies
  `v(A_t) = W(c_t, v(A_{t+1}))` at every date attains `v(A)`; `ex_5_12a_necessary`
  (Theorem 4.4): with `W` strictly increasing in `z`, an optimal plan satisfies (2) at the first
  date and its continuation is optimal.

Optimal plans need not exist: when the policy's consumption path is unbounded it is not in `L`,
and the supremum is approached by the truncated plans only.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {l : ℕ} {W : (Fin l → ℝ) → ℝ → ℝ} {p : Fin l → ℝ} {R β M : ℝ}

/-- The present value `Σ Rᵗ(p·c_t)` of a plan. -/
noncomputable def planCost (p : Fin l → ℝ) (R : ℝ) (c : Seq l) : ℝ :=
  ∑' t, R ^ t * spend p (c.1 t)

theorem spend_le_bound {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (c : Seq l) (t : ℕ) :
    spend p (c.1 t) ≤ (∑ i, p i) * ‖c.1‖ := by
  simp only [spend, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hp i).le
  calc c.1 t i ≤ ‖c.1 t i‖ := Real.le_norm_self _
    _ ≤ ‖c.1 t‖ := norm_le_pi_norm _ i
    _ ≤ ‖c.1‖ := c.1.norm_coe_le_norm t

theorem summable_planCost {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hR0 : 0 < R) (hR1 : R < 1)
    (c : Seq l) : Summable fun t => R ^ t * spend p (c.1 t) :=
  Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hR0.le t) (spend_nonneg hp (c.2 t)))
    (fun t => mul_le_mul_of_nonneg_left (spend_le_bound hp c t) (pow_nonneg hR0.le t))
    ((summable_geometric_of_lt_one hR0.le hR1).mul_right _)

theorem planCost_nonneg {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hR0 : 0 < R) (c : Seq l) :
    0 ≤ planCost p R c :=
  tsum_nonneg fun t => mul_nonneg (pow_nonneg hR0.le t) (spend_nonneg hp (c.2 t))

/-- The budget recursion: `Σ Rᵗp·c_t = p·c₀ + R Σ Rᵗp·c_{t+1}`. -/
theorem planCost_eq {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hR0 : 0 < R) (hR1 : R < 1)
    (c : Seq l) : planCost p R c = spend p (c.1 0) + R * planCost p R (shiftSeq c) := by
  rw [planCost, (summable_planCost hp hR0 hR1 c).tsum_eq_zero_add, planCost, ← tsum_mul_left]
  simp only [pow_zero, one_mul, shiftSeq_apply, pow_succ]
  congr 1
  exact tsum_congr fun t => by ring

/-- `c` is feasible from `A`. -/
def Feasible5 (p : Fin l → ℝ) (R : ℝ) (A : ℝ) (c : Seq l) : Prop := planCost p R c ≤ A

theorem feasible_head {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hR0 : 0 < R) (hR1 : R < 1)
    {A : Wealth} {c : Seq l} (hc : Feasible5 p R A.1 c) : c.1 0 ∈ budgetΓ p A := by
  refine ⟨c.2 0, ?_⟩
  have := planCost_eq hp hR0 hR1 c
  have := mul_nonneg hR0.le (planCost_nonneg hp hR0 (shiftSeq c))
  unfold Feasible5 at hc
  linarith

theorem feasible_shift {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hR0 : 0 < R) (hR1 : R < 1)
    {A : ℝ} {c : Seq l} (hc : Feasible5 p R A c) :
    Feasible5 p R (nextWealth p R A (c.1 0)) (shiftSeq c) := by
  have := planCost_eq hp hR0 hR1 c
  unfold Feasible5 at hc ⊢
  rw [nextWealth, le_div_iff₀ hR0]
  linarith

/-! ### The value bounds every feasible plan -/

/-- **Exercise 5.12a (Theorems 4.2–4.3, upper half).** With `W` nondecreasing in `z`, every
feasible plan has `u_W(c) ≤ v(A)`. -/
theorem utility_le_value (h : ConsHyp W p R β M) (hA : AggHyp W β M) (hR1 : R < 1)
    (hW4 : ∀ C, 0 ≤ C → Monotone (W C)) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {uW : Seq l →ᵇ ℝ} (hu : opTW hA uW = uW) (A : Wealth) (c : Seq l)
    (hc : Feasible5 p R A.1 c) : uW c ≤ v A := by
  set K := ‖uW‖ + ‖v‖
  have hvx : ∀ A : Wealth, v A = maxValue (consObj W p R v) (budgetΓ p) A := fun A =>
    (DFunLike.congr_fun hv A).symm
  have hfe : ∀ c, uW c = W (c.1 0) (uW (shiftSeq c)) := fun c => (DFunLike.congr_fun hu c).symm
  have hstep : ∀ n : ℕ, ∀ (A : Wealth) (c : Seq l), Feasible5 p R A.1 c →
      uW c - v A ≤ β ^ n * K := by
    intro n
    induction n with
    | zero =>
      intro A c _
      have h1 := abs_apply_le_norm uW c
      have h2 : |v A| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm A
      have h3 := le_abs_self (uW c)
      have h4 := neg_abs_le (v A)
      rw [pow_zero, one_mul]
      simp only [K]
      linarith
    | succ n ih =>
      intro A c hc
      have hc0 := feasible_head h.p_pos h.R_pos hR1 hc
      set A₁ : Wealth := ⟨nextWealth p R A.1 (c.1 0), mem_Ici.2 (div_nonneg
        (by linarith [hc0.2]) h.R_pos.le)⟩
      have hsc := feasible_shift h.p_pos h.R_pos hR1 hc
      have hIH := ih A₁ (shiftSeq c) hsc
      have hvA : W (c.1 0) (v A₁) ≤ v A := by
        rw [hvx A]
        have := le_maxValue (continuous_consObj h v.continuous).continuousOn
          (budget_compact h.p_pos A) hc0
        have e : vext v (nextWealth p R A.1 (c.1 0)) = v A₁ := vext_of_nonneg v A₁.2
        simp only [consObj] at this
        rw [e] at this
        exact this
      rw [hfe c]
      rcases le_total (uW (shiftSeq c)) (v A₁) with hle | hlt
      · have := hW4 _ (c.2 0) hle
        have : 0 ≤ β ^ (n + 1) * K :=
          mul_nonneg (pow_nonneg h.β_pos.le _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
        linarith
      · have hl := h.lip _ (c.2 0) (uW (shiftSeq c)) (v A₁)
        rw [abs_of_nonneg (sub_nonneg.2 hlt)] at hl
        have := le_abs_self (W (c.1 0) (uW (shiftSeq c)) - W (c.1 0) (v A₁))
        have hb := mul_le_mul_of_nonneg_left hIH h.β_pos.le
        rw [pow_succ]
        nlinarith
  have hlim : Tendsto (fun n => β ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.β_pos.le h.β_lt).mul_const K
  have := ge_of_tendsto' hlim fun n => hstep n A c hc
  linarith

/-! ### Plans that follow the policy -/

/-- `(C, c₀, c₁, …)`. -/
noncomputable def consSeq (C : Fin l → ℝ) (hC : 0 ≤ C) (c : Seq l) : Seq l :=
  ⟨BoundedContinuousFunction.mkOfDiscrete (fun t => Nat.casesOn t C fun s => c.1 s)
      (2 * (‖C‖ + ‖c.1‖)) fun s t => by
        have hb : ∀ u : ℕ, ‖(Nat.casesOn u C fun s => c.1 s : Fin l → ℝ)‖ ≤ ‖C‖ + ‖c.1‖ :=
          fun u => by
            cases u with
            | zero =>
              change ‖C‖ ≤ ‖C‖ + ‖c.1‖
              linarith [norm_nonneg c.1]
            | succ s =>
              change ‖c.1 s‖ ≤ ‖C‖ + ‖c.1‖
              linarith [c.1.norm_coe_le_norm s, norm_nonneg C]
        exact (dist_le_norm_add_norm _ _).trans (by linarith [hb s, hb t]),
    fun t => by
      cases t with
      | zero => exact hC
      | succ s => exact c.2 s⟩

theorem consSeq_head (C : Fin l → ℝ) (hC : 0 ≤ C) (c : Seq l) : (consSeq C hC c).1 0 = C := rfl

theorem shiftSeq_consSeq (C : Fin l → ℝ) (hC : 0 ≤ C) (c : Seq l) :
    shiftSeq (consSeq C hC c) = c := Subtype.ext (by ext t i; rfl)

/-- The policy: a maximizer at each wealth level. -/
noncomputable def consPolicy (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) (A : Wealth) :
    Fin l → ℝ :=
  (exists_consT_argmax h v A).choose

theorem consPolicy_spec (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) (A : Wealth) :
    consPolicy h v A ∈ budgetΓ p A ∧
      consT h v A = consObj W p R v (A, consPolicy h v A) :=
  ⟨(exists_consT_argmax h v A).choose_spec.1, (exists_consT_argmax h v A).choose_spec.2.1⟩

/-- Next period's wealth under the policy. -/
noncomputable def policyNext (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) (A : Wealth) : Wealth :=
  ⟨nextWealth p R A.1 (consPolicy h v A), mem_Ici.2 (by
    unfold nextWealth
    exact div_nonneg (by linarith [(consPolicy_spec h v A).1.2]) h.R_pos.le)⟩

/-- Follow the policy for `n + 1` periods, then consume nothing. -/
noncomputable def policyPlan (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) :
    ℕ → Wealth → Seq l
  | 0, A => consSeq (consPolicy h v A) (consPolicy_spec h v A).1.1 zeroSeq
  | n + 1, A => consSeq (consPolicy h v A) (consPolicy_spec h v A).1.1
      (policyPlan h v n (policyNext h v A))

/-- **Exercise 5.12a (lower half).** The truncated policy plans are feasible and come within
`βⁿ⁺¹(‖u_W‖ + ‖v‖)` of `v(A)`. -/
theorem exists_plan_near (h : ConsHyp W p R β M) (hA : AggHyp W β M) (hR1 : R < 1)
    {v : Wealth →ᵇ ℝ} (hv : consT h v = v) {uW : Seq l →ᵇ ℝ} (hu : opTW hA uW = uW)
    (huz : uW zeroSeq = 0) (n : ℕ) (A : Wealth) :
    Feasible5 p R A.1 (policyPlan h v n A) ∧
      |uW (policyPlan h v n A) - v A| ≤ β ^ (n + 1) * (‖uW‖ + ‖v‖) := by
  have hfe : ∀ c, uW c = W (c.1 0) (uW (shiftSeq c)) := fun c => (DFunLike.congr_fun hu c).symm
  have hvA : ∀ A : Wealth, v A = W (consPolicy h v A) (v (policyNext h v A)) := fun A => by
    have := (consPolicy_spec h v A).2
    rw [hv] at this
    rw [this]
    simp only [consObj]
    have e : vext v (nextWealth p R A.1 (consPolicy h v A)) = v (policyNext h v A) :=
      vext_of_nonneg v (policyNext h v A).2
    rw [e]
  have hcost : ∀ (C : Fin l → ℝ) (hC : 0 ≤ C) (c : Seq l),
      planCost p R (consSeq C hC c) = spend p C + R * planCost p R c := fun C hC c => by
    rw [planCost_eq h.p_pos h.R_pos hR1, consSeq_head, shiftSeq_consSeq]
  have hzero : planCost p R (zeroSeq : Seq l) = 0 := by
    simp [planCost, zeroSeq, spend]
  have hKn : 0 ≤ ‖uW‖ + ‖v‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  induction n generalizing A with
  | zero =>
    have hs := (consPolicy_spec h v A).1
    refine ⟨?_, ?_⟩
    · unfold Feasible5
      simp only [policyPlan]
      rw [hcost, hzero, mul_zero, add_zero]
      exact hs.2
    · simp only [policyPlan]
      rw [hfe, consSeq_head, shiftSeq_consSeq, huz, hvA A]
      refine (h.lip _ hs.1 0 _).trans ?_
      rw [zero_sub, abs_neg, zero_add, pow_one]
      have : |v (policyNext h v A)| ≤ ‖v‖ := by
        simpa [Real.norm_eq_abs] using v.norm_coe_le_norm _
      nlinarith [h.β_pos, norm_nonneg uW]
  | succ n ih =>
    have hs := (consPolicy_spec h v A).1
    obtain ⟨hf, hb⟩ := ih (policyNext h v A)
    refine ⟨?_, ?_⟩
    · unfold Feasible5 at hf ⊢
      simp only [policyPlan]
      rw [hcost]
      have hn : (policyNext h v A).1 = nextWealth p R A.1 (consPolicy h v A) := rfl
      rw [hn, nextWealth] at hf
      have := mul_le_mul_of_nonneg_left hf h.R_pos.le
      rw [mul_div_cancel₀ _ h.R_pos.ne'] at this
      linarith
    · simp only [policyPlan]
      rw [hfe, consSeq_head, shiftSeq_consSeq, hvA A]
      refine (h.lip _ hs.1 _ _).trans ?_
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left hb h.β_pos.le

/-- **Exercise 5.12a.** The solution of (2) is the supremum function of (1):
`v(A) = sup{u_W(c) : Σ Rᵗp·c_t ≤ A}`. -/
theorem ex_5_12a (h : ConsHyp W p R β M) (hA : AggHyp W β M) (hR1 : R < 1)
    (hW4 : ∀ C, 0 ≤ C → Monotone (W C)) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {uW : Seq l →ᵇ ℝ} (hu : opTW hA uW = uW) (huz : uW zeroSeq = 0) (A : Wealth) :
    v A = sSup (uW '' {c | Feasible5 p R A.1 c}) := by
  have hne : (uW '' {c | Feasible5 p R A.1 c}).Nonempty :=
    ⟨_, zeroSeq, show planCost p R zeroSeq ≤ A.1 by simp [planCost, zeroSeq, spend, A.2.out], rfl⟩
  have hbdd : BddAbove (uW '' {c | Feasible5 p R A.1 c}) := by
    refine ⟨v A, ?_⟩
    rintro _ ⟨c, hc, rfl⟩
    exact utility_le_value h hA hR1 hW4 hv hu A c hc
  have hub : ∀ y ∈ uW '' {c | Feasible5 p R A.1 c}, y ≤ v A := by
    rintro _ ⟨c, hc, rfl⟩
    exact utility_le_value h hA hR1 hW4 hv hu A c hc
  refine le_antisymm ?_ (csSup_le hne hub)
  have hlim : Tendsto (fun n : ℕ => v A - β ^ (n + 1) * (‖uW‖ + ‖v‖)) atTop (𝓝 (v A)) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h.β_pos.le h.β_lt).comp
      (tendsto_add_atTop_nat 1)).mul_const (‖uW‖ + ‖v‖)
    simpa using (tendsto_const_nhds (x := v A)).sub this
  refine le_of_tendsto' hlim fun n => ?_
  obtain ⟨hf, hb⟩ := exists_plan_near h hA hR1 hv hu huz n A
  have := le_csSup hbdd ⟨_, hf, rfl⟩
  linarith [neg_abs_le (uW (policyPlan h v n A) - v A)]

/-- The wealth path `A₀ = A`, `A_{t+1} = R⁻¹(A_t − p·c_t)`. -/
noncomputable def wealthPath (p : Fin l → ℝ) (R : ℝ) (A : ℝ) (c : Seq l) : ℕ → ℝ
  | 0 => A
  | t + 1 => nextWealth p R (wealthPath p R A c t) (c.1 t)

/-- **Exercise 5.12a (Theorem 4.5).** If `v(A_t) = W(c_t, v(A_{t+1}))` along the wealth path at
every date, then `u_W(c) = v(A)`: the plan is optimal. -/
theorem ex_5_12a_optimal (hA : AggHyp W β M) {v : Wealth →ᵇ ℝ} {uW : Seq l →ᵇ ℝ}
    (hu : opTW hA uW = uW) (A : ℝ) (c : Seq l)
    (hpath : ∀ t, vext v (wealthPath p R A c t) =
      W (c.1 t) (vext v (wealthPath p R A c (t + 1)))) : uW c = vext v A := by
  have hfe : ∀ c, uW c = W (c.1 0) (uW (shiftSeq c)) := fun c => (DFunLike.congr_fun hu c).symm
  set K := ‖uW‖ + ‖v‖
  -- along the shifted plans, `|u_W(ₜc) − v(A_t)| ≤ βⁿK`
  have hpathshift : ∀ (n : ℕ) (A : ℝ) (c : Seq l), (∀ t, vext v (wealthPath p R A c t) =
      W (c.1 t) (vext v (wealthPath p R A c (t + 1)))) →
      |uW c - vext v A| ≤ β ^ n * K := by
    intro n
    induction n with
    | zero =>
      intro A c _
      have h1 := abs_apply_le_norm uW c
      have h2 := abs_vext_le v A
      simp only [pow_zero, one_mul, K]
      exact (abs_sub _ _).trans (add_le_add h1 h2)
    | succ n ih =>
      intro A c hp
      have hp' : ∀ t, vext v (wealthPath p R (nextWealth p R A (c.1 0)) (shiftSeq c) t) =
          W ((shiftSeq c).1 t) (vext v (wealthPath p R (nextWealth p R A (c.1 0))
            (shiftSeq c) (t + 1))) := by
        have hw : ∀ t, wealthPath p R (nextWealth p R A (c.1 0)) (shiftSeq c) t =
            wealthPath p R A c (t + 1) := by
          intro t
          induction t with
          | zero => rfl
          | succ t iht => simp only [wealthPath] at iht ⊢; rw [iht]; rfl
        intro t
        rw [hw, hw]
        exact hp (t + 1)
      have hIH := ih _ _ hp'
      rw [hfe c, show vext v A = W (c.1 0) (vext v (wealthPath p R A c 1)) from hp 0]
      refine (hA.lip _ (c.2 0) _ _).trans ?_
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left hIH hA.β_pos.le
  have hlim : Tendsto (fun n => β ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hA.β_pos.le hA.β_lt).mul_const K
  have := ge_of_tendsto' hlim fun n => hpathshift n A c hpath
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- **Exercise 5.12a (Theorem 4.4).** With `W` strictly increasing in `z`, an optimal feasible plan
satisfies (2) at the first date, and its continuation is optimal from next period's wealth. -/
theorem ex_5_12a_necessary (h : ConsHyp W p R β M) (hA : AggHyp W β M) (hR1 : R < 1)
    (hW4 : ∀ C, 0 ≤ C → StrictMono (W C)) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {uW : Seq l →ᵇ ℝ} (hu : opTW hA uW = uW) {A : Wealth} {c : Seq l}
    (hc : Feasible5 p R A.1 c) (hopt : uW c = v A) :
    v A = W (c.1 0) (vext v (nextWealth p R A.1 (c.1 0))) ∧
      uW (shiftSeq c) = vext v (nextWealth p R A.1 (c.1 0)) := by
  have hc0 := feasible_head h.p_pos h.R_pos hR1 hc
  have hA₁ : 0 ≤ nextWealth p R A.1 (c.1 0) := div_nonneg (by linarith [hc0.2]) h.R_pos.le
  set A₁ : Wealth := ⟨_, hA₁⟩
  have hfe : ∀ c, uW c = W (c.1 0) (uW (shiftSeq c)) := fun c => (DFunLike.congr_fun hu c).symm
  have hle := utility_le_value h hA hR1 (fun C hC => (hW4 C hC).monotone) hv hu A₁ (shiftSeq c)
    (feasible_shift h.p_pos h.R_pos hR1 hc)
  have hvA : W (c.1 0) (v A₁) ≤ v A := by
    rw [← DFunLike.congr_fun hv A]
    have := le_maxValue (continuous_consObj h v.continuous).continuousOn
      (budget_compact h.p_pos A) hc0
    simp only [consObj, vext_of_nonneg v hA₁] at this
    exact this
  have h1 := (hW4 _ (c.2 0)).monotone hle
  rw [← hfe c, hopt] at h1
  have heq : W (c.1 0) (uW (shiftSeq c)) = W (c.1 0) (v A₁) := by
    rw [← hfe c]; linarith
  rw [vext_of_nonneg v hA₁]
  exact ⟨by linarith, (hW4 _ (c.2 0)).injective heq⟩

end StokeyLucasPrescott.DeterministicApplications
