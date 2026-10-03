/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Examples
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Applications: savings, investment and hiring

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.1.2.3–§5.1.2.4 and
§5.2 (pp. 133–134, 145–161).

Each application chooses next period's endogenous state directly while an
exogenous shock moves by a Markov matrix `Q`, so the kernel is
`P((y, z), q, (y', z')) = 1{y' = q}Q(z, z')`: the choice kernel. Cake eating
(Exercise 5.1.4) is the special case without a shock. The savings model with
labour income (§5.2.2) has `Γ(w, y) = {s : s ≤ R(w + y)}`, reward
`u(w + y − s/R)`, Bellman operator (5.29), policy operator (5.30), and `P_σ`,
`r_σ` as on p. 150. The monopolist's investment problem (§5.2.3) has reward
`(a₀ − a₁y + z − c)y − γ(q − y)²`; Exercise 5.2.2: without adjustment costs the
profit-maximising output is `Ȳ = (a₀ − c + z)/(2a₁)`. The hiring model of
Exercise 5.2.3 has fixed adjustment costs `κ·1{ℓ' ≠ ℓ}`.

Job search with Markov wages as an MDP (Exercise 5.1.5) is also here: on the
state space `{0, 1} × W` with actions reject/accept, the employed value is
`w/(1 − β)` and the unemployed value satisfies the Bellman equation of
Vol. 1 (3.23).
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

variable {Y Z : Type*} [Fintype Y] [Fintype Z] [DecidableEq Y]

/-- The choice kernel `P((y, z), q, (y', z')) = 1{y' = q}Q(z, z')`: the endogenous component is
chosen, the exogenous one moves by `Q` (pp. 149, 157). -/
def choiceKernel (Q : Matrix Z Z ℝ) (x : Y × Z) (q : Y) (x' : Y × Z) : ℝ :=
  (if x'.1 = q then 1 else 0) * Q x.2 x'.2

omit [Fintype Y] in
theorem choiceKernel_nonneg {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (x : Y × Z) (q : Y) (x' : Y × Z) :
    0 ≤ choiceKernel Q x q x' := by
  unfold choiceKernel
  split_ifs <;> simp [hQ.nonneg]

theorem choiceKernel_rowsum {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (x : Y × Z) (q : Y) :
    ∑ x', choiceKernel Q x q x' = 1 := by
  unfold choiceKernel
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq' univ q, mem_univ, ite_true]
  exact hQ.rowsum x.2

/-- `∑_{x'} v(x')P((y, z), q, x') = ∑_{z'} v(q, z')Q(z, z')`. -/
theorem sum_mul_choiceKernel (Q : Matrix Z Z ℝ) (v : Y × Z → ℝ) (x : Y × Z) (q : Y) :
    ∑ x', v x' * choiceKernel Q x q x' = ∑ z', v (q, z') * Q x.2 z' := by
  rw [Fintype.sum_prod_type]
  have h : ∀ (y' : Y) (z' : Z), v (y', z') * choiceKernel Q x q (y', z') =
      if y' = q then v (q, z') * Q x.2 z' else 0 := by
    intro y' z'
    simp only [choiceKernel]
    split_ifs with h
    · rw [h]
      ring
    · ring
  simp only [h]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq' univ q, mem_univ, ite_true]

/-! ### Cake eating (§5.1.2.3, Exercise 5.1.4) -/

/-- Exercise 5.1.4 (p. 133): cake eating as an MDP. Wealth takes values in a finite set with values
`wealth : W → ℝ`; the action is next-period wealth `w'`, feasible iff `w' ≤ Rw` (so that consumption
`w − w'/R` is nonnegative); the reward is `u(w − w'/R)`; the kernel is deterministic. -/
noncomputable def cakeEating {W : Type*} [Fintype W] [DecidableEq W] (wealth : W → ℝ) (R : ℝ)
    (u : ℝ → ℝ) (hΓ : ∀ w, ∃ w', wealth w' ≤ R * wealth w) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    MDP W W where
  Γ := fun w => univ.filter fun w' => wealth w' ≤ R * wealth w
  Γ_nonempty := fun w => by
    obtain ⟨w', hw'⟩ := hΓ w
    exact ⟨w', by simp [hw']⟩
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := fun w w' => u (wealth w - wealth w' / R)
  P := detKernel fun _ w' => w'
  P_nonneg := detKernel_nonneg _
  P_rowsum := detKernel_rowsum _

/-- The cake-eating Bellman equation (5.13): `v*(w) = max_{w' ≤ Rw} {u(w − w'/R) + βv*(w')}`. -/
theorem cakeEating_bellman {W : Type*} [Fintype W] [DecidableEq W] (wealth : W → ℝ) (R : ℝ)
    (u : ℝ → ℝ) (hΓ : ∀ w, ∃ w', wealth w' ≤ R * wealth w) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (w : W) :
    (cakeEating wealth R u hΓ hβ0 hβ1).vstar w =
      (univ.filter fun w' => wealth w' ≤ R * wealth w).sup'
        ((cakeEating wealth R u hΓ hβ0 hβ1).Γ_nonempty w)
        fun w' =>
          u (wealth w - wealth w' / R) + β * (cakeEating wealth R u hΓ hβ0 hβ1).vstar w' := by
  rw [MDP.bellman_equation]
  refine Finset.sup'_congr _ rfl fun w' _ => ?_
  change u (wealth w - wealth w' / R) + β * ∑ x', _ * detKernel (fun _ w' => w') w w' x' = _
  rw [sum_mul_detKernel]

/-! ### Optimal savings with labour income (§5.2.2) -/

/-- The optimal savings model (§5.2.2.1): states `(w, y)` with wealth values `wealth` and income
values `inc`, `Q`-Markov income, actions `s ∈ W` with `Γ(w, y) = {s : s ≤ R(w + y)}`, reward
`u(w + y − s/R)`, choice kernel. -/
noncomputable def savings {W : Type*} [Fintype W] [DecidableEq W] (wealth : W → ℝ) (inc : Y → ℝ)
    {Q : Matrix Y Y ℝ} (hQ : IsMarkov Q) (R : ℝ) (u : ℝ → ℝ)
    (hΓ : ∀ w y, ∃ s, wealth s ≤ R * (wealth w + inc y)) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    MDP (W × Y) W where
  Γ := fun x => univ.filter fun s => wealth s ≤ R * (wealth x.1 + inc x.2)
  Γ_nonempty := fun x => by
    obtain ⟨s, hs⟩ := hΓ x.1 x.2
    exact ⟨s, by simp [hs]⟩
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := fun x s => u (wealth x.1 + inc x.2 - wealth s / R)
  P := choiceKernel Q
  P_nonneg := choiceKernel_nonneg hQ
  P_rowsum := choiceKernel_rowsum hQ

namespace savings

variable {W : Type*} [Fintype W] [DecidableEq W] (wealth : W → ℝ) (inc : Y → ℝ)
  {Q : Matrix Y Y ℝ} (hQ : IsMarkov Q) (R : ℝ) (u : ℝ → ℝ)
  (hΓ : ∀ w y, ∃ s, wealth s ≤ R * (wealth w + inc y)) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)

omit [DecidableEq Y] in
/-- The feasible savings: `s ∈ Γ(w, y) ⟺ s ≤ R(w + y)` (p. 149). -/
theorem mem_Γ (w : W) (y : Y) (s : W) :
    s ∈ (savings wealth inc hQ R u hΓ hβ0 hβ1).Γ (w, y) ↔ wealth s ≤ R * (wealth w + inc y) := by
  simp [savings]

omit [DecidableEq Y] in
/-- The Bellman operator (5.29):
`(Tv)(w, y) = max_{w' ∈ Γ(w, y)} {u(w + y − w'/R) + β ∑ v(w', y')Q(y, y')}`. -/
theorem T_apply (v : W × Y → ℝ) (w : W) (y : Y) :
    (savings wealth inc hQ R u hΓ hβ0 hβ1).T v (w, y) =
      ((savings wealth inc hQ R u hΓ hβ0 hβ1).Γ (w, y)).sup'
        ((savings wealth inc hQ R u hΓ hβ0 hβ1).Γ_nonempty (w, y))
        fun w' => u (wealth w + inc y - wealth w' / R) + β * ∑ y', v (w', y') * Q y y' := by
  rw [MDP.T_apply]
  refine Finset.sup'_congr _ rfl fun w' _ => ?_
  change u (wealth w + inc y - wealth w' / R) + β * ∑ x', v x' * choiceKernel Q (w, y) w' x' = _
  rw [sum_mul_choiceKernel]

omit [DecidableEq Y] in
/-- The policy operator (5.30):
`(T_σ v)(w, y) = u(w + y − σ(w, y)/R) + β ∑ v(σ(w, y), y')Q(y, y')`. -/
theorem Tσ_apply (σ : W × Y → W) (v : W × Y → ℝ) (w : W) (y : Y) :
    (savings wealth inc hQ R u hΓ hβ0 hβ1).Tσ σ v (w, y) =
      u (wealth w + inc y - wealth (σ (w, y)) / R) + β * ∑ y', v (σ (w, y), y') * Q y y' := by
  rw [MDP.Tσ_apply]
  change u (wealth w + inc y - wealth (σ (w, y)) / R) +
    β * ∑ x', v x' * choiceKernel Q (w, y) (σ (w, y)) x' = _
  rw [sum_mul_choiceKernel]

omit [DecidableEq Y] in
/-- `P_σ((w, y), (w', y')) = 1{σ(w, y) = w'}Q(y, y')` (p. 150). -/
theorem Pσ_apply (σ : W × Y → W) (w : W) (y : Y) (w' : W) (y' : Y) :
    (savings wealth inc hQ R u hΓ hβ0 hβ1).Pσ σ (w, y) (w', y') =
      (if w' = σ (w, y) then 1 else 0) * Q y y' := rfl

omit [DecidableEq Y] in
/-- `r_σ(w, y) = u(w + y − σ(w, y)/R)` (p. 150). -/
theorem rσ_apply (σ : W × Y → W) (w : W) (y : Y) :
    (savings wealth inc hQ R u hΓ hβ0 hβ1).rσ σ (w, y) =
      u (wealth w + inc y - wealth (σ (w, y)) / R) := rfl

end savings

/-! ### Optimal investment (§5.2.3) -/

/-- The monopolist's current profit `(a₀ − a₁y + z − c)y − γ(q − y)²` (p. 157). -/
def investmentReward (a₀ a₁ c γ : ℝ) (y z q : ℝ) : ℝ := (a₀ - a₁ * y + z - c) * y - γ * (q - y) ^ 2

/-- Exercise 5.2.2 (p. 156): without adjustment costs (`γ = 0`), `Ȳ = (a₀ − c + z)/(2a₁)` maximises
current profit `(a₀ − a₁y + z − c)y` over all `y ∈ ℝ`, when `a₁ > 0`. -/
theorem investmentReward_le_at_Ybar {a₀ a₁ c z : ℝ} (ha₁ : 0 < a₁) (y q : ℝ) :
    investmentReward a₀ a₁ c 0 y z q ≤
      investmentReward a₀ a₁ c 0 ((a₀ - c + z) / (2 * a₁)) z q := by
  unfold investmentReward
  simp only [zero_mul, sub_zero]
  have h : (a₀ - a₁ * ((a₀ - c + z) / (2 * a₁)) + z - c) * ((a₀ - c + z) / (2 * a₁)) -
      (a₀ - a₁ * y + z - c) * y = a₁ * (y - (a₀ - c + z) / (2 * a₁)) ^ 2 := by
    field_simp
    ring
  nlinarith [mul_nonneg ha₁.le (sq_nonneg (y - (a₀ - c + z) / (2 * a₁)))]

/-- The optimal investment model (§5.2.3.2): states `(y, z)` with output values `out` and shock
values `shock`, actions `q ∈ Y` (next output) unrestricted, reward
`(a₀ − a₁y + z − c)y − γ(q − y)²`, choice kernel, `β = 1/(1 + r)`. -/
noncomputable def investment [Nonempty Y] (out : Y → ℝ) (shock : Z → ℝ) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) (a₀ a₁ c γ : ℝ) {r : ℝ} (hr : 0 < r) : MDP (Y × Z) Y where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  r := fun x q => investmentReward a₀ a₁ c γ (out x.1) (shock x.2) (out q)
  P := choiceKernel Q
  P_nonneg := choiceKernel_nonneg hQ
  P_rowsum := choiceKernel_rowsum hQ

/-- The investment Bellman operator (p. 157):
`(Tv)(y, z) = max_{y' ∈ Y} {r(y, z, y') + β ∑ v(y', z')Q(z, z')}`. -/
theorem investment_T_apply [Nonempty Y] (out : Y → ℝ) (shock : Z → ℝ) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) (a₀ a₁ c γ : ℝ) {r : ℝ} (hr : 0 < r) (v : Y × Z → ℝ) (y : Y) (z : Z) :
    (investment out shock hQ a₀ a₁ c γ hr).T v (y, z) =
      (univ : Finset Y).sup' ((investment out shock hQ a₀ a₁ c γ hr).Γ_nonempty (y, z))
        fun y' => investmentReward a₀ a₁ c γ (out y) (shock z) (out y') +
          1 / (1 + r) * ∑ z', v (y', z') * Q z z' := by
  rw [MDP.T_apply]
  refine Finset.sup'_congr _ rfl fun y' _ => ?_
  change investmentReward a₀ a₁ c γ (out y) (shock z) (out y') +
    1 / (1 + r) * ∑ x', v x' * choiceKernel Q (y, z) y' x' = _
  rw [sum_mul_choiceKernel]

/-! ### Firm hiring with fixed adjustment costs (Exercise 5.2.3) -/

/-- Exercise 5.2.3 (p. 160): current profit `pzℓᵅ − wℓ − κ·1{ℓ' ≠ ℓ}` with fixed hiring and firing
costs. -/
noncomputable def hiringReward (p w α κ : ℝ) (z ℓ ℓ' : ℝ) : ℝ :=
  p * z * ℓ ^ α - w * ℓ - κ * (if ℓ' ≠ ℓ then 1 else 0)

/-- Exercise 5.2.3 (p. 160): the hiring model as an MDP. States `(ℓ, z)` with labour values `lab`
and shock values `shock`, actions `ℓ' ∈ L` (next period's labour), reward `pzℓᵅ − wℓ − κ1{ℓ' ≠ ℓ}`,
choice kernel, `β = 1/(1 + r)`. -/
noncomputable def hiring [Nonempty Y] (lab : Y → ℝ) (shock : Z → ℝ) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) (p w α κ : ℝ) {r : ℝ} (hr : 0 < r) : MDP (Y × Z) Y where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  r := fun x ℓ' => hiringReward p w α κ (shock x.2) (lab x.1) (lab ℓ')
  P := choiceKernel Q
  P_nonneg := choiceKernel_nonneg hQ
  P_rowsum := choiceKernel_rowsum hQ

/-- Exercise 5.2.3 (p. 160), the Bellman equation:
`v*(ℓ, z) = max_{ℓ'} {pzℓᵅ − wℓ − κ1{ℓ' ≠ ℓ} + β ∑ v*(ℓ', z')Q(z, z')}`. -/
theorem hiring_bellman [Nonempty Y] (lab : Y → ℝ) (shock : Z → ℝ) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) (p w α κ : ℝ) {r : ℝ} (hr : 0 < r) [DecidableEq Z] (ℓ : Y) (z : Z) :
    (hiring lab shock hQ p w α κ hr).vstar (ℓ, z) =
      (univ : Finset Y).sup' ((hiring lab shock hQ p w α κ hr).Γ_nonempty (ℓ, z))
        fun ℓ' => hiringReward p w α κ (shock z) (lab ℓ) (lab ℓ') +
          1 / (1 + r) * ∑ z', (hiring lab shock hQ p w α κ hr).vstar (ℓ', z') * Q z z' := by
  rw [MDP.bellman_equation]
  refine Finset.sup'_congr _ rfl fun ℓ' _ => ?_
  change hiringReward p w α κ (shock z) (lab ℓ) (lab ℓ') +
    1 / (1 + r) * ∑ x', _ * choiceKernel Q (ℓ, z) ℓ' x' = _
  rw [sum_mul_choiceKernel]

/-! ### Job search with Markov wages as an MDP (Exercise 5.1.5) -/

/-- The job search kernel on `{0, 1} × W` (p. 134): an employed worker stays employed at the same
wage; an unemployed worker who accepts becomes employed at the current wage; one who rejects draws a
new offer from `Q(w, ·)`. -/
def jobSearchKernel {W : Type*} [DecidableEq W] (Q : Matrix W W ℝ) (x : Bool × W) (a : Bool)
    (x' : Bool × W) : ℝ :=
  if x.1 || a then (if x' = (true, x.2) then 1 else 0)
  else (if x'.1 = false then Q x.2 x'.2 else 0)

theorem jobSearchKernel_nonneg {W : Type*} [Fintype W] [DecidableEq W] {Q : Matrix W W ℝ}
    (hQ : IsMarkov Q)
    (x : Bool × W) (a : Bool) (x' : Bool × W) : 0 ≤ jobSearchKernel Q x a x' := by
  unfold jobSearchKernel
  split_ifs <;> first | exact zero_le_one | exact le_rfl | exact hQ.nonneg _ _

theorem jobSearchKernel_rowsum {W : Type*} [Fintype W] [DecidableEq W] {Q : Matrix W W ℝ}
    (hQ : IsMarkov Q) (x : Bool × W) (a : Bool) : ∑ x', jobSearchKernel Q x a x' = 1 := by
  unfold jobSearchKernel
  split_ifs
  · simp
  · rw [Fintype.sum_prod_type]
    simp [hQ.rowsum]

/-- Exercise 5.1.5 (p. 134): job search with `Q`-Markov wages as an MDP on `{0, 1} × W` with
actions reject (`false`) / accept (`true`): the employed earn their wage, the unemployed earn `c`
if they reject and the wage if they accept. -/
noncomputable def jobSearch {W : Type*} [Fintype W] [DecidableEq W] (wage : W → ℝ)
    {Q : Matrix W W ℝ} (hQ : IsMarkov Q) (c : ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    MDP (Bool × W) Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := fun x a => if x.1 || a then wage x.2 else c
  P := jobSearchKernel Q
  P_nonneg := jobSearchKernel_nonneg hQ
  P_rowsum := jobSearchKernel_rowsum hQ

namespace jobSearch

variable {W : Type*} [Fintype W] [DecidableEq W] (wage : W → ℝ) {Q : Matrix W W ℝ}
  (hQ : IsMarkov Q) (c : ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)

/-- From an employed state, or on acceptance, the next state is `(1, w)` with certainty. -/
theorem sum_mul_kernel_stay (v : Bool × W → ℝ) (e : Bool) (w : W) (a : Bool) (h : (e || a) = true) :
    ∑ x', v x' * jobSearchKernel Q (e, w) a x' = v (true, w) := by
  have hk : ∀ x', jobSearchKernel Q (e, w) a x' = if x' = (true, w) then 1 else 0 := by
    intro x'
    simp [jobSearchKernel, h]
  simp only [hk, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' univ (true, w)]
  simp

/-- On rejection the next state is `(0, w')` with `w' ∼ Q(w, ·)`. -/
theorem sum_mul_kernel_reject (v : Bool × W → ℝ) (w : W) :
    ∑ x', v x' * jobSearchKernel Q (false, w) false x' = ∑ w', v (false, w') * Q w w' := by
  have hk : ∀ x', jobSearchKernel Q (false, w) false x' = if x'.1 = false then Q w x'.2 else 0 := by
    intro x'
    simp [jobSearchKernel]
  simp only [hk]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp

/-- An employed worker is worth `w/(1 − β)`: both actions give `w + βv*(1, w)`. -/
theorem vstar_employed (w : W) :
    (jobSearch wage hQ c hβ0 hβ1).vstar (true, w) = wage w / (1 - β) := by
  have h := (jobSearch wage hQ c hβ0 hβ1).bellman_equation (true, w)
  change _ = (univ : Finset Bool).sup' univ_nonempty (fun a =>
    (if (true || a) = true then wage w else c) +
      β * ∑ x', (jobSearch wage hQ c hβ0 hβ1).vstar x' * jobSearchKernel Q (true, w) a x') at h
  rw [sup'_bool, sum_mul_kernel_stay _ _ _ _ rfl, sum_mul_kernel_stay _ _ _ _ rfl] at h
  simp only [Bool.true_or, ite_true, max_self] at h
  have hβ' : (1 : ℝ) - β ≠ 0 := by linarith
  rw [eq_div_iff hβ']
  linarith

/-- Vol. 1 (3.23) recovered: the unemployed value satisfies
`v*(0, w) = max{w/(1 − β), c + β ∑ v*(0, w')Q(w, w')}`. -/
theorem vstar_unemployed (w : W) :
    (jobSearch wage hQ c hβ0 hβ1).vstar (false, w) =
      max (wage w / (1 - β))
        (c + β * ∑ w', (jobSearch wage hQ c hβ0 hβ1).vstar (false, w') * Q w w') := by
  have h := (jobSearch wage hQ c hβ0 hβ1).bellman_equation (false, w)
  change _ = (univ : Finset Bool).sup' univ_nonempty (fun a =>
    (if (false || a) = true then wage w else c) +
      β * ∑ x', (jobSearch wage hQ c hβ0 hβ1).vstar x' * jobSearchKernel Q (false, w) a x') at h
  rw [sup'_bool, sum_mul_kernel_stay _ _ _ _ rfl, sum_mul_kernel_reject] at h
  simp only [Bool.false_or, ite_true, Bool.false_eq_true, ite_false] at h
  rw [h, vstar_employed]
  congr 1
  have hβ' : (1 : ℝ) - β ≠ 0 := by linarith
  field_simp
  ring

end jobSearch

end SargentStachurski.MarkovDecisionProcesses
