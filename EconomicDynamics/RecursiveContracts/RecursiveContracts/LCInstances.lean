/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.LCBellman
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Solutions of the Bellman equation with log utility, and the Markov counterexample

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1.1, pp. 776–778, with `u = log`
(which satisfies the Inada conditions; its inverse is `exp`).

* `lc_absorbing_bellman`: at an absorbing state with endowment `θⱼ` the Bellman equation of
  §22.1.1 is solved, for every promised value `v ∈ ℝ`, by the explicit function `lc_absorbP`:
  with `B = log θⱼ = (1 − β) U_d(θⱼ)`, `κ = β/(1 − β)` and `b = max{B, (1 − β)v}`,
  `P(v) = θⱼ/(1 − β) − exp(v − κb) − κ exp(b)`; for `v ≥ U_d(θⱼ)` this is
  `(θⱼ − exp((1 − β)v))/(1 − β)`, full insurance at the constant consumption `exp((1 − β)v)`.
* `lc_bellman_one_state`: the one-state economy, where `U_d` is the autarky value; this shows
  that the Bellman equation `lc_Bellman` has solutions.
* `lc_promise_decrease_counterexample`: a three-state Markov chain (state 0 moves to a high or a
  low absorbing state with probability 1/2 each, `β = 1/2`) in which the optimal contract at
  `(θ₀, v = 1)` gives the promised value `w₂ = 0 < v` after the low state, although the
  incentive constraint there is slack (`w₂ > U_d(θ₂) = −4`). This refutes the book's claims
  "`λᵢ = 0` implies `wᵢ = v`", `w = max{U_d(y), v}` and "promised values never decrease" for
  general Markov endowments (p. 777–778); they hold in the i.i.d. case (`lc_iid_promised_value`).
-/

namespace Miao.RecursiveContracts

open Real

/-- The value at an absorbing state with log utility (see the module docstring). -/
noncomputable def lc_absorbP (β θj B v : ℝ) : ℝ :=
  θj / (1 - β) - exp (v - β / (1 - β) * max B ((1 - β) * v)) -
    β / (1 - β) * exp (max B ((1 - β) * v))

/-- For `(1 − β)v ≥ B` the absorbing-state value is `(θⱼ − exp((1 − β)v))/(1 − β)`. -/
theorem lc_absorbP_of_le {β : ℝ} (hβ1 : β < 1) (θj B v : ℝ) (h : B ≤ (1 - β) * v) :
    lc_absorbP β θj B v = θj / (1 - β) - exp ((1 - β) * v) / (1 - β) := by
  have h1 : 0 < 1 - β := by linarith
  unfold lc_absorbP
  rw [max_eq_right h]
  have : v - β / (1 - β) * ((1 - β) * v) = (1 - β) * v := by field_simp
  rw [this]
  field_simp
  ring

/-- The supporting-line inequality `exp b ≥ exp a (1 + b − a)`. -/
theorem lc_exp_ge_tangent (a b : ℝ) : exp a * (1 + (b - a)) ≤ exp b := by
  have h := add_one_le_exp (b - a)
  have : exp b = exp a * exp (b - a) := by rw [← exp_add]; ring_nf
  rw [this]
  nlinarith [exp_pos a]

/-- Miao, p. 776, with `u = log` at an absorbing state: `lc_absorbP` solves the Bellman equation
at `θⱼ` for every promised value `v`. -/
theorem lc_absorbing_bellman {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (pl : ι → ι → ℝ) (θ : ι → ℝ) (Ud : ι → ℝ) (P : ι → ℝ → ℝ) (j : ι)
    (hpl : ∀ k, pl j k = if k = j then 1 else 0) (hUd : Ud j = log (θ j) / (1 - β))
    (hP : P j = lc_absorbP β (θ j) (log (θ j))) (v : ℝ) :
    lc_BellmanAt β pl θ log Ud P j v := by
  have h1 : 0 < 1 - β := by linarith
  have hsum : ∀ X : ι → ℝ, ∑ k, pl j k * X k = X j := by
    intro X
    simp_rw [hpl, ite_mul, one_mul, zero_mul]
    simp
  set B := log (θ j)
  set κ := β / (1 - β) with hκ
  set bs := max B ((1 - β) * v) with hbs
  set as := v - κ * bs with has
  have hκ0 : 0 ≤ κ := div_nonneg hβ0 h1.le
  have hκβ : ∀ x, β * (x / (1 - β)) = κ * x := by intro x; rw [hκ]; ring
  have hPw : ∀ w, Ud j ≤ w → P j w = θ j / (1 - β) - exp ((1 - β) * w) / (1 - β) := by
    intro w hw
    rw [hP]
    apply lc_absorbP_of_le hβ1
    rw [hUd, div_le_iff₀ h1] at hw
    linarith
  -- the key inequality
  have hkey : ∀ a b, B ≤ b → v ≤ a + κ * b → exp as + κ * exp bs ≤ exp a + κ * exp b := by
    intro a b hb hv
    have ha := lc_exp_ge_tangent as a
    have hb' : exp bs + exp as * (b - bs) ≤ exp b := by
      rcases le_total B ((1 - β) * v) with hle | hle
      · have hbs' : bs = (1 - β) * v := max_eq_right hle
        have : as = bs := by rw [has, hbs', hκ]; field_simp
        have := lc_exp_ge_tangent bs b
        rw [‹as = bs›]
        nlinarith
      · have hbs' : bs = B := max_eq_left hle
        have hasB : as ≤ B := by
          rw [has, hbs', hκ]
          have : v * (1 - β) ≤ B := by linarith
          have e : v - β / (1 - β) * B = (v * (1 - β) - β * B) / (1 - β) := by field_simp
          rw [e, div_le_iff₀ h1]
          nlinarith
        have := lc_exp_ge_tangent B b
        have hexp : exp as ≤ exp B := exp_le_exp.mpr hasB
        rw [hbs']
        nlinarith [mul_le_mul_of_nonneg_right hexp (by linarith : (0 : ℝ) ≤ b - B)]
    have hsumv : as + κ * bs = v := by rw [has]; ring
    nlinarith [mul_le_mul_of_nonneg_left hb' hκ0, exp_pos as]
  have hval : lc_absorbP β (θ j) B v = θ j / (1 - β) - exp as - κ * exp bs := rfl
  refine ⟨⟨exp as, fun k => if k = j then bs / (1 - β) else Ud k, ⟨exp_pos _, fun k => ?_, ?_⟩,
    ?_⟩, ?_⟩
  · by_cases hk : k = j
    · subst hk
      simp only [↓reduceIte]
      rw [hUd]
      exact div_le_div_of_nonneg_right (le_max_left _ _) h1.le
    · simp [hk]
  · rw [hsum]
    simp only [↓reduceIte, log_exp]
    rw [hκβ, has]
    linarith
  · simp only [lc_obj]
    rw [hsum]
    simp only [↓reduceIte]
    rw [hPw (bs / (1 - β)) (by rw [hUd]; exact div_le_div_of_nonneg_right (le_max_left _ _) h1.le),
      hP]
    rw [hval]
    have : (1 - β) * (bs / (1 - β)) = bs := by field_simp
    rw [this, hκ]
    field_simp
    ring
  · rintro x ⟨c, w, ⟨hc, hw, hv⟩, rfl⟩
    rw [hP, hval]
    simp only [lc_obj]
    rw [hsum] at hv ⊢
    rw [hPw _ (hw j)]
    have hb : B ≤ (1 - β) * w j := by
      have := hw j
      rw [hUd, div_le_iff₀ h1] at this
      linarith
    have hk := hkey (log c) ((1 - β) * w j) hb (by
      have : κ * ((1 - β) * w j) = β * w j := by rw [hκ]; field_simp
      rw [this]; exact hv)
    rw [exp_log hc] at hk
    have e : β * (θ j / (1 - β) - exp ((1 - β) * w j) / (1 - β)) =
        κ * θ j - κ * exp ((1 - β) * w j) := by rw [hκ]; field_simp
    have e2 : θ j / (1 - β) = θ j + κ * θ j := by rw [hκ]; field_simp; ring
    rw [e, e2]
    linarith

/-- Miao, pp. 775–776, the one-state economy with `u = log`: the autarky value is
`log θ₀/(1 − β)` and `lc_absorbP` solves the Bellman equation at every promised value. So
`lc_Bellman` has solutions (with `U_d` the true autarky value). -/
theorem lc_bellman_one_state {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (θ0 : ℝ) :
    let pl : Unit → Unit → ℝ := fun _ _ => 1
    let Ud : Unit → ℝ := fun _ => log θ0 / (1 - β)
    Ud = lc_autarky β pl (fun _ => log θ0) ∧
      lc_Bellman β pl (fun _ => θ0) log Ud (fun _ => lc_absorbP β θ0 (log θ0)) := by
  intro pl Ud
  have h1 : 0 < 1 - β := by linarith
  refine ⟨?_, fun i v => ?_⟩
  · apply lc_autarky_unique hβ0 hβ1 ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
    intro i
    simp only [Ud, Finset.univ_unique, Finset.sum_singleton, one_mul]
    field_simp
    ring
  · cases i
    exact lc_absorbing_bellman hβ0 hβ1 pl _ Ud _ () (fun k => by cases k; rfl) rfl rfl v

/-- Miao, pp. 777–778, counterexample to "`λᵢ = 0` implies `wᵢ = v`", to `w = max{U_d(y), v}`
and to "promised values never decrease" for Markov endowments. States `0, 1, 2`, `β = 1/2`,
`u = log`, endowments `1, e², e⁻²`; state 0 moves to 1 or 2 with probability 1/2 each and 1, 2 are
absorbing. Then `U_d = (0, 4, −4)` is the autarky value, `lc_absorbP` solves the Bellman equation
at states 1 and 2, and at `(θ₀, v = 1)` the contract `c = 1`, `w = (0, 4, 0)` is optimal: after
state 2 the incentive constraint is slack (`w₂ = 0 > −4`) but the promised value falls to
`w₂ = 0 < v = 1 = max{U_d(θ₂), v}`. -/
theorem lc_promise_decrease_counterexample :
    let β : ℝ := 1 / 2
    let pl : Fin 3 → Fin 3 → ℝ := ![![0, 1 / 2, 1 / 2], ![0, 1, 0], ![0, 0, 1]]
    let θ : Fin 3 → ℝ := ![1, exp 2, exp (-2)]
    let Ud : Fin 3 → ℝ := ![0, 4, -4]
    let P : Fin 3 → ℝ → ℝ :=
      ![fun _ => 0, lc_absorbP β (exp 2) 2, lc_absorbP β (exp (-2)) (-2)]
    let w : Fin 3 → ℝ := ![0, 4, 0]
    Ud = lc_autarky β pl (fun i => log (θ i)) ∧
      (∀ v, lc_BellmanAt β pl θ log Ud P 1 v) ∧ (∀ v, lc_BellmanAt β pl θ log Ud P 2 v) ∧
      lc_feasible β pl log Ud 0 1 1 w ∧
      IsGreatest (lc_valueSet β pl θ log Ud P 0 1) (lc_obj β pl θ P 0 1 w) ∧
      Ud 2 < w 2 ∧ w 2 < 1 ∧ w 2 ≠ max (Ud 2) 1 := by
  intro β pl θ Ud P w
  have hstoch : lc_IsStochastic pl := by
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [pl]
    · fin_cases i <;> simp [pl, Fin.sum_univ_three]
      norm_num
  have hβ0 : (0 : ℝ) ≤ β := by norm_num [β]
  have hβ1 : β < 1 := by norm_num [β]
  refine ⟨?_, fun v => ?_, fun v => ?_, ?_, ?_, ?_⟩
  · apply lc_autarky_unique hβ0 hβ1 hstoch
    intro i
    fin_cases i <;> simp [Ud, pl, θ, β, Fin.sum_univ_three] <;> norm_num
  · refine lc_absorbing_bellman hβ0 hβ1 pl θ Ud P 1 (fun k => ?_) ?_ ?_ v
    · fin_cases k <;> simp [pl]
    · simp [Ud, θ, β]; norm_num
    · simp [P, θ]
  · refine lc_absorbing_bellman hβ0 hβ1 pl θ Ud P 2 (fun k => ?_) ?_ ?_ v
    · fin_cases k <;> simp [pl]
    · simp [Ud, θ, β]; norm_num
    · simp [P, θ]
  · refine ⟨one_pos, fun k => ?_, ?_⟩
    · fin_cases k <;> simp [Ud, w]
    · simp [pl, w, β, Fin.sum_univ_three]; norm_num
  · have hP1 : ∀ x, 4 ≤ x → P 1 x = 2 * exp 2 - 2 * exp (x / 2) := by
      intro x hx
      simp only [P, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [lc_absorbP_of_le hβ1 _ _ _ (by norm_num [β]; linarith)]
      norm_num [β]
      ring_nf
    have hP2 : ∀ x, -4 ≤ x → P 2 x = 2 * exp (-2) - 2 * exp (x / 2) := by
      intro x hx
      simp only [P, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [lc_absorbP_of_le hβ1 _ _ _ (by norm_num [β]; linarith)]
      norm_num [β]
      ring_nf
    have hobj : ∀ c (w' : Fin 3 → ℝ), 4 ≤ w' 1 → -4 ≤ w' 2 →
        lc_obj β pl θ P 0 c w' = 1 - c + (exp 2 + exp (-2)) / 2 -
          (exp (w' 1 / 2) + exp (w' 2 / 2)) / 2 := by
      intro c w' h1 h2
      simp only [lc_obj, Fin.sum_univ_three]
      rw [hP1 _ h1, hP2 _ h2]
      simp [pl, θ, β]
      ring
    refine ⟨⟨1, w, ?_, rfl⟩, ?_⟩
    · refine ⟨one_pos, fun k => ?_, ?_⟩
      · fin_cases k <;> simp [Ud, w]
      · simp [pl, w, β, Fin.sum_univ_three]; norm_num
    · rintro x ⟨c, w', ⟨hc, hw, hv⟩, rfl⟩
      have h1 : 4 ≤ w' 1 := by simpa [Ud] using hw 1
      have h2 : -4 ≤ w' 2 := by simpa [Ud] using hw 2
      rw [hobj c w' h1 h2, hobj 1 w (by simp [w]) (by simp [w])]
      simp only [pl, β, Fin.sum_univ_three] at hv
      norm_num at hv
      have ha := lc_exp_ge_tangent 0 (log c)
      rw [exp_log hc, exp_zero] at ha
      have hb := lc_exp_ge_tangent 0 (w' 2 / 2)
      have hc2 := lc_exp_ge_tangent 2 (w' 1 / 2)
      have he2 : 1 ≤ exp 2 := one_le_exp (by norm_num)
      simp only [w, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      norm_num
      rw [exp_zero] at hb
      nlinarith [mul_le_mul_of_nonneg_right he2 (by linarith : (0 : ℝ) ≤ w' 1 / 2 - 2)]
  · simp [Ud, w]
    norm_num

end Miao.RecursiveContracts
