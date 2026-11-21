/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.RDEquivalence

/-!
# A bubble on one branch, a Ponzi scheme on the other

Counterexamples to (13.23) and to Theorem 13.5.1 ("if") as printed (Miao, pp. 433, 435).

The economy: two equally likely states each period (`rd_uniformTree Bool`), `β = 1/2`, two
agents with linear expected utility `U(c) = ∑ βᵗ E cₜ`, endowments `1`, complete Arrow
securities priced at `1/4` (so `q⁰(sᵗ) = 4⁻ᵗ`, `π(sᵗ) = 2⁻ᵗ`). Both agents consume their
endowment. The martingale `m = q⁰ V` (`rd_mg`) is `+1` along the branch that starts with `true`
and continues with `true`, `−1` along the branch that starts with `false` and continues with
`true`, and `0` elsewhere; the zero-cost strategy `ψ` (`rd_psi`) has value `V(sᵗ) = 4ᵗ m(sᵗ)`.
Agent `true` holds `ψ`, agent `false` holds `−ψ`.

* `theorem_13_5_1_counterexample`: this is a competitive equilibrium with transversality
  condition (the date-0 condition (13.21) holds because `E[π_T p_T · ψ_T] = m(s⁰) = 0`), markets
  are complete, utilities are strictly increasing and satisfy Assumption 13.5.1, but `(c, θ, p)`
  is not a Radner equilibrium with any bounded borrowing limits or bounded debt limits:
  `p · (−ψ)` and `f · (−ψ)` are unbounded below. (Theorem 13.5.1 holds with the replicating
  strategies, here `θ̃ = 0`: `theorem_13_5_1_if`.)
* `eq_13_23_counterexample`: the plan of agent `true` satisfies (13.11) and (13.21), but (13.23)
  fails at the node `(false)`.
-/

namespace Miao.CompleteMarkets

open Filter Topology

/-- The martingale `m`: `m(s⁰) = 0`, `m(s₁) = ±1` by the first shock, and afterwards `m` is
carried along shocks `true` and dropped to `0` at a shock `false`. -/
def rd_mg : List Bool → ℝ
  | [] => 0
  | [s] => if s then 1 else -1
  | s :: t :: h => if s then rd_mg (t :: h) else 0

/-- `m` is a martingale on the tree: `∑ₛ m(sᵗ, s) = m(sᵗ)`. -/
theorem rd_mg_sum (h : List Bool) : ∑ s, rd_mg (s :: h) = rd_mg h := by
  cases h with
  | nil => simp [rd_mg]
  | cons t h => simp [rd_mg]

/-- The martingale property over any number of periods. -/
theorem rd_dsum_mg (h : List Bool) (j : ℕ) : rd_dsum rd_mg h j = rd_mg h := by
  induction j generalizing h with
  | zero => exact rd_dsum_zero _ _
  | succ j ih =>
    rw [rd_dsum_succ]
    simp only [ih, rd_mg_sum]

/-- `m = 1` along the all-`true` branch. -/
theorem rd_mg_true (n : ℕ) : rd_mg (List.replicate (n + 1) true) = 1 := by
  induction n with
  | zero => simp [rd_mg]
  | succ n ih =>
    rw [List.replicate_succ] at ih ⊢
    rw [List.replicate_succ]
    simp only [rd_mg, ↓reduceIte]
    exact ih

/-- The zero-cost strategy: the Arrow holdings paying `V(sᵗ, s) = 4^{t+1} m(sᵗ, s)`. -/
noncomputable def rd_psi (h : List Bool) : Bool → ℝ := fun s => rd_mg (s :: h) * 4 ^ (h.length + 1)

/-- The probabilities of the uniform tree on `Bool`. -/
theorem rd_cx_Pr (h : List Bool) : (rd_uniformTree Bool).Pr h = (1 / 2) ^ h.length := by
  simp [rd_uniformTree]

/-- The deflator `π(sᵗ) = 2⁻ᵗ`. -/
noncomputable def rd_cxpd (h : List Bool) : ℝ := (1 / 2) ^ h.length

/-- The Arrow prices `1/4`. -/
noncomputable def rd_cxp (_h : List Bool) (_s : Bool) : ℝ := 1 / 4

/-- The state prices `q⁰ = π Pr = 4⁻ᵗ`. -/
theorem rd_cx_q (h : List Bool) :
    rd_cxpd h * (rd_uniformTree Bool).Pr h = (1 / 4) ^ h.length := by
  rw [rd_cx_Pr, rd_cxpd, ← mul_pow]
  norm_num

/-- The strategies: agent `true` holds `ψ`, agent `false` holds `−ψ`. -/
noncomputable def rd_cxθ (i : Bool) : List Bool → Bool → ℝ := if i then rd_psi else -rd_psi

/-- The cost of `ψ` at `sᵗ` is its value `4ᵗ m(sᵗ)`. -/
theorem rd_psi_cost (h : List Bool) : rd_cxp h ⬝ᵥ rd_psi h = rd_mg h * 4 ^ h.length := by
  rw [← rd_mg_sum h]
  simp only [rd_cxp, rd_psi, dotProduct, Fintype.sum_bool, pow_succ]
  ring

/-- The payoff of `ψ` bought at `sᵗ` in state `s`. -/
theorem rd_psi_payoff (h : List Bool) (s : Bool) :
    rd_arrowPayoff (s :: h) ⬝ᵥ rd_psi h = rd_mg (s :: h) * 4 ^ (s :: h).length := by
  cases s <;> simp [rd_arrowPayoff, rd_psi, dotProduct]

/-- The state prices of the economy. -/
theorem rd_cx_statePrice :
    rd_StatePrice rd_cxp rd_arrowPayoff fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g := by
  rw [rd_arrow_statePrice _ _ fun h => by rw [rd_cx_q]; positivity]
  intro h s
  simp only [rd_cx_q, List.length_cons, pow_succ, rd_cxp]
  ring

/-- `q⁰ ∈ L¹`. -/
theorem rd_cx_L1 : rd_L1 fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g := by
  have e : ∀ t, rd_dsum (fun g => |rd_cxpd g * (rd_uniformTree Bool).Pr g|) [] t =
      (1 / 2) ^ t := by
    intro t
    have : (fun g => |rd_cxpd g * (rd_uniformTree Bool).Pr g|) =
        fun g => (1 / 2 : ℝ) ^ g.length * (rd_uniformTree Bool).Pr g := by
      funext g
      rw [abs_of_pos (mul_pos (by unfold rd_cxpd; positivity) ((rd_uniformTree Bool).pos g))]
      rfl
    rw [this, rd_dsum_pow, rd_dsum_Pr, (rd_uniformTree Bool).root, mul_one]
  simp only [rd_L1, e]
  exact summable_geometric_two

/-- Linear expected utility is the state-price value of consumption. -/
theorem rd_cx_EU (c : List Bool → ℝ) :
    rd_EU (rd_uniformTree Bool) (1 / 2) id c =
      ∑' t, rd_dsum (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g * c g) [] t := by
  refine tsum_congr fun t => ?_
  rw [← rd_dsum_pow]
  exact rd_dsum_congr (fun g => by simp [rd_cxpd]; ring) _ _

/-- The agents' budgets bind and the date-0 transversality condition holds. -/
theorem rd_cx_budget (i : Bool) :
    rd_BudgetEq rd_cxp rd_arrowPayoff (fun _ => 1) 0 (fun _ => 1) (rd_cxθ i) ∧
      rd_TVC (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g) rd_cxp (rd_cxθ i) := by
  have hθ : ∀ g, rd_cxθ i g = (if i then (1 : ℝ) else -1) • rd_psi g := fun g => by
    cases i <;> simp [rd_cxθ]
  refine ⟨fun h => ?_, ?_⟩
  · cases h with
    | nil =>
      simp only [hθ, dotProduct_smul, rd_psi_cost, rd_fz, rd_prev, dotProduct_zero]
      simp [rd_mg]
    | cons s g =>
      simp only [hθ, dotProduct_smul, rd_psi_cost, rd_fz, rd_prev, rd_psi_payoff]
      ring
  · have e : (fun T => rd_dsum (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g *
        (rd_cxp g ⬝ᵥ rd_cxθ i g)) [] T) = fun _ => 0 := by
      funext T
      have : (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g * (rd_cxp g ⬝ᵥ rd_cxθ i g)) =
          fun g => (if i then (1 : ℝ) else -1) * rd_mg g := by
        funext g
        rw [hθ, dotProduct_smul, rd_psi_cost, rd_cx_q, smul_eq_mul]
        rw [show (1 / 4 : ℝ) ^ g.length * ((if i then 1 else -1) * (rd_mg g * 4 ^ g.length)) =
          (if i then 1 else -1) * rd_mg g * ((1 / 4) ^ g.length * 4 ^ g.length) by ring,
          ← mul_pow]
        norm_num
      rw [this, rd_dsum_const_mul, rd_dsum_mg]
      simp [rd_mg]
    rw [rd_TVC, e]
    exact tendsto_const_nhds

/-- The value of `ψ` is unbounded along the all-`true` branch. -/
theorem rd_psi_unbounded (M : ℝ) : ∃ n, M < rd_cxp (List.replicate (n + 1) true) ⬝ᵥ
    rd_psi (List.replicate (n + 1) true) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 4)
  refine ⟨n, ?_⟩
  rw [rd_psi_cost, rd_mg_true, one_mul, List.length_replicate]
  calc M < 4 ^ n := hn
    _ ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)

/-- **Theorem 13.5.1** (Miao, p. 435), counterexample to the "if" direction as printed. The
economy above is a competitive equilibrium with transversality condition, markets are complete,
utilities are strictly increasing and satisfy Assumption 13.5.1, but with the equilibrium
strategies it is not a Radner equilibrium with any bounded borrowing or debt limits. -/
theorem theorem_13_5_1_counterexample :
    rd_CETVC (rd_uniformTree Bool) (fun _ => rd_EU (rd_uniformTree Bool) (1 / 2) id)
        (fun _ _ => 1) (fun _ => 0) rd_arrowPayoff (fun _ _ => 1) rd_cxθ rd_cxpd rd_cxp ∧
      (∀ h, (rd_payoffMatrix (rd_arrowPayoff (S := Bool)) h).rank = Fintype.card Bool) ∧
      (∀ _i : Bool, rd_StrictIncr (rd_EU (rd_uniformTree Bool) (1 / 2) id)) ∧
      (∀ _i : Bool, rd_Assumption1351 (rd_EU (rd_uniformTree Bool) (1 / 2) id)
        fun _ => ∑ _k : Bool, (1 : ℝ)) ∧
      (¬ ∃ Bbar : Bool → List Bool → ℝ, (∀ i, rd_Bdd (Bbar i)) ∧
        rd_RadnerBC (fun _ => rd_EU (rd_uniformTree Bool) (1 / 2) id) (fun _ _ => 1)
          (fun _ => 0) rd_cxp rd_arrowPayoff Bbar (fun _ _ => 1) rd_cxθ) ∧
      ¬ ∃ Dbar : Bool → List Bool → ℝ, (∀ i, rd_Bdd (Dbar i)) ∧
        rd_RadnerDC (fun _ => rd_EU (rd_uniformTree Bool) (1 / 2) id) (fun _ _ => 1)
          (fun _ => 0) rd_cxp rd_arrowPayoff Dbar (fun _ _ => 1) rd_cxθ := by
  set q : List Bool → ℝ := fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g
  have hone : rd_LinfPos (fun _ : List Bool => (1 : ℝ)) := ⟨rd_bdd_one, fun _ => zero_le_one⟩
  have hU : ∀ c', rd_LinfPos c' → rd_ADBudget q (fun _ => 1) c' →
      rd_EU (rd_uniformTree Bool) (1 / 2) id c' ≤
        rd_EU (rd_uniformTree Bool) (1 / 2) id fun _ => 1 := by
    intro c' _ hb
    rw [rd_cx_EU, rd_cx_EU]
    exact hb
  have hseq : ∀ c' θ', rd_LinfPos c' → rd_Budget rd_cxp rd_arrowPayoff (fun _ => 1) 0 c' θ' →
      rd_TVC q rd_cxp θ' → rd_ADBudget q (fun _ => 1) c' := by
    intro c' θ' hc' hB hT
    have := eq_13_22 rd_cx_statePrice hB hT (rd_L1_mul rd_cx_L1 hc'.1)
      (rd_L1_mul rd_cx_L1 rd_bdd_one)
    simpa [rd_ADBudget] using this
  refine ⟨⟨fun _ => hone, rd_cx_L1, fun h => by unfold rd_cxpd; positivity,
    fun _ _ => by unfold rd_cxp; norm_num, fun _ => ⟨1 / 4, fun _ => by
      unfold rd_cxp; norm_num [abs_of_pos]⟩,
    fun i => ⟨⟨hone, fun h => ((rd_cx_budget i).1 h).le, (rd_cx_budget i).2⟩,
      fun c' θ' ⟨hc', hB, hT⟩ => hU c' hc' (hseq c' θ' hc' hB hT)⟩,
    fun i => ⟨⟨hone, by simp⟩, fun c' ⟨hc', hb⟩ => hU c' hc' (by simpa [rd_ADBudget] using hb)⟩,
    rd_cx_statePrice, fun h => rfl, fun h => ?_⟩,
    fun h => rd_arrow_rank h, fun _ => rd_eq_13_1 _ (by norm_num) (by norm_num) strictMonoOn_id,
    fun _ => assumption_13_5_1 _ (by norm_num) (by norm_num) strictMonoOn_id
      continuous_id.continuousOn (m := 2) (Y := 2) (by norm_num) (fun _ => by simp)
      (fun _ => by simp), ?_, ?_⟩
  · funext s
    simp [rd_cxθ]
  · rintro ⟨Bbar, hBb, hsol, -, -⟩
    obtain ⟨M, hM⟩ := hBb false
    obtain ⟨n, hn⟩ := rd_psi_unbounded M
    have := (hsol false).1.2.2 (List.replicate (n + 1) true)
    simp only [rd_cxθ, Bool.false_eq_true, ↓reduceIte, Pi.neg_apply, dotProduct_neg] at this
    linarith [(le_abs_self _).trans (hM (List.replicate (n + 1) true))]
  · rintro ⟨Dbar, hDb, hsol, -, -⟩
    obtain ⟨M, hM⟩ := hDb false
    obtain ⟨n, hn⟩ := rd_psi_unbounded M
    have := (hsol false).1.2.2 (List.replicate n true) true
    simp only [rd_cxθ, Bool.false_eq_true, ↓reduceIte, Pi.neg_apply, dotProduct_neg,
      rd_psi_payoff] at this
    rw [rd_psi_cost] at hn
    have hM' := (le_abs_self _).trans (hM (List.replicate (n + 1) true))
    rw [← List.replicate_succ] at this
    linarith

/-- (13.23) (Miao, p. 433), counterexample: agent `true`'s plan satisfies the budget (13.11) and
the transversality condition (13.21), but the conditional present-value budget (13.23) fails at
the node `(false)`, where the strategy is worth `−4` (`q⁰ = 1/4`). -/
theorem eq_13_23_counterexample :
    rd_Budget rd_cxp rd_arrowPayoff (fun _ => 1) 0 (fun _ => 1) rd_psi ∧
      rd_TVC (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g) rd_cxp rd_psi ∧
      ¬ (∑' j, rd_dsum (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g * 1) [false] j ≤
        rd_cxpd [false] * (rd_uniformTree Bool).Pr [false] *
          (rd_fz rd_cxp rd_arrowPayoff [false] ⬝ᵥ rd_prev rd_psi 0 [false]) +
        ∑' j, rd_dsum (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g * 1) [false] j) := by
  have hb := rd_cx_budget true
  simp only [rd_cxθ, ↓reduceIte] at hb
  refine ⟨fun h => (hb.1 h).le, hb.2, fun hle => ?_⟩
  have : rd_cxpd [false] * (rd_uniformTree Bool).Pr [false] *
      (rd_fz rd_cxp rd_arrowPayoff [false] ⬝ᵥ rd_prev rd_psi 0 [false]) = -1 := by
    rw [rd_cx_q]
    simp only [rd_fz, rd_prev]
    rw [rd_psi_payoff]
    simp [rd_mg]
  linarith

end Miao.CompleteMarkets
