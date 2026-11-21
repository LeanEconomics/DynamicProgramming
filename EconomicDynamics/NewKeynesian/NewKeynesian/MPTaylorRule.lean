/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.NewKeynesian

/-!
# Implementing strict inflation targeting: the Taylor principle (19.31) and Exercise 19.2

Miao, §19.2.3, p. 635 ((19.31)), and Exercise 19.2 of §19.5, p. 669. The setting is the one of
Miao, Exercise 2.2 (module `NewKeynesian`): a `CondExpSystem ℝ V`, the state
`X_t = (x_t, π_t)` (both jump variables), stable (bounded) adapted processes. The model is the
Phillips curve (19.24) `π_t = κx_t + βE_tπ_{t+1}`, the IS curve (19.28)
`x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1} − r^n_t)` and an interest-rate rule
`i_t = ī_t + φ_ππ_t + φ_yx_t` (`mpRuleEqm`; no policy shock).

* `mp_rule_eqm_iff`: with intercept `ī`, the model is Exercise 2.2's Taylor-rule model with the
  shock `ε_t = ī_t − r^n_t` (and no IS shock).
* `mp_zero_eqm_iff`: strict inflation targeting `π = x = 0` is an equilibrium iff `ī_t = r^n_t`
  at every date (`γ ≠ 0`); in that case `i_t = r^n_t` (`mp_strict_targeting_rate`).
* `mpImplements`: the rule implements the optimal policy if `π = x = 0` is an equilibrium and the
  only stable adapted one.
* `eq_19_31`: for `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0`, the rule `i_t = r^n_t + φ_ππ_t + φ_yx_t`
  implements the optimal policy when `κ(φ_π − 1) + (1 − β)φ_y > 0`.
* `ex_19_2`: **Exercise 19.2**, corrected: for `φ_π, φ_y ≥ 0` (and `V` containing a nonzero
  `F_0`-measurable `w`), the rule `i_t = r^n_t + φ_ππ_t + φ_yx_t` implements the optimal policy
  iff (19.31) holds. `mp_ex_19_2_instance`: a concrete instance (deterministic system, `κ = γ = 1`,
  `β = 1/2`, `φ_π = 3/2`, `φ_y = 0`), so the hypotheses are satisfiable.

**Correction.** The text and the exercise use the rule (19.29) `i_t = −ln β + φ_ππ_t + φ_yx_t`
"where the monetary policy shock is removed". Since `π = x = 0` requires `i_t = r^n_t`, that
rule implements strict inflation targeting only if the natural rate is constant at `−ln β`
(`mp_zero_eqm_iff`); `mp_printed_rule_fails` and `mp_printed_rule_counterexample` (deterministic
system, `r^n ≡ 1`, intercept `0`) show the printed statement fails otherwise. With the intercept
`r^n_t` (equivalently, (19.29) with `i_t, r^n_t` measured as deviations, no natural-rate shocks)
the exercise is true. (For `φ_π < 0` the exact determinacy condition has a second branch,
Exercise 2.2(b).)
-/

namespace Miao.NewKeynesian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The model (19.24), (19.28) with the rule `i_t = ī_t + φ_ππ_t + φ_yx_t` (Miao, p. 635);
`X t 0 = x_t`, `X t 1 = π_t`. -/
def mpRuleEqm (E : CondExpSystem ℝ V) (κ β γ φπ φy : ℝ) (rn ibar : ℕ → V)
    (X : ℕ → Fin 2 → V) : Prop :=
  ∀ t, X t 1 = κ • X t 0 + β • E.E t (X (t + 1) 1) ∧
    X t 0 = E.E t (X (t + 1) 0) -
      γ⁻¹ • ((ibar t + φπ • X t 1 + φy • X t 0) - E.E t (X (t + 1) 1) - rn t)

/-- Miao, p. 635: the model with intercept `ī` is Exercise 2.2's Taylor-rule model
`nkTaylorEqm` with monetary shock `ε_t = ī_t − r^n_t` and no IS shock. -/
theorem mp_rule_eqm_iff (E : CondExpSystem ℝ V) (κ β γ φπ φy : ℝ) (rn ibar : ℕ → V)
    (X : ℕ → Fin 2 → V) :
    mpRuleEqm E κ β γ φπ φy rn ibar X ↔
      nkTaylorEqm E κ β γ φπ φy (fun t => ibar t - rn t) (fun _ => 0) X := by
  refine forall_congr' fun t => and_congr Iff.rfl ?_
  have e : E.E t (X (t + 1) 0) -
      γ⁻¹ • ((ibar t + φπ • X t 1 + φy • X t 0) - E.E t (X (t + 1) 1) - rn t) =
      E.E t (X (t + 1) 0) - γ⁻¹ • ((φπ • X t 1 + φy • X t 0 + (ibar t - rn t)) -
        E.E t (X (t + 1) 1)) + 0 := by module
  rw [e]

/-- With intercept `r^n_t`, the model is Exercise 2.2's model with no shocks. -/
theorem mp_rule_eqm_rn_iff (E : CondExpSystem ℝ V) (κ β γ φπ φy : ℝ) (rn : ℕ → V)
    (X : ℕ → Fin 2 → V) :
    mpRuleEqm E κ β γ φπ φy rn rn X ↔ nkTaylorEqm E κ β γ φπ φy (fun _ => 0) (fun _ => 0) X := by
  rw [mp_rule_eqm_iff]
  simp only [sub_self]

/-- **Strict inflation targeting as an equilibrium** (Miao, p. 635). For `γ ≠ 0`, the path
`π = x = 0` solves the model with the rule `i_t = ī_t + φ_ππ_t + φ_yx_t` iff `ī_t = r^n_t` at
every date. -/
theorem mp_zero_eqm_iff (E : CondExpSystem ℝ V) {γ : ℝ} (hγ : γ ≠ 0) (κ β φπ φy : ℝ)
    (rn ibar : ℕ → V) :
    mpRuleEqm E κ β γ φπ φy rn ibar 0 ↔ ∀ t, ibar t = rn t := by
  simp only [mpRuleEqm, Pi.zero_apply, map_zero, smul_zero, add_zero, sub_zero, zero_sub,
    true_and]
  refine forall_congr' fun t => ?_
  rw [eq_comm, neg_eq_zero, smul_eq_zero, sub_eq_zero]
  simp [hγ]

/-- The rule with intercept `ī` **implements the optimal policy** (Miao, p. 635) if strict
inflation targeting `π = x = 0` is an equilibrium and it is the only stable adapted one. -/
def mpImplements (E : CondExpSystem ℝ V) (κ β γ φπ φy : ℝ) (rn ibar : ℕ → V) : Prop :=
  mpRuleEqm E κ β γ φπ φy rn ibar 0 ∧
    ∀ X, mpRuleEqm E κ β γ φπ φy rn ibar X → IsAdaptedV E X → IsStableProc X → X = 0

/-- **The Taylor principle (19.31)** (Miao, p. 635). For `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0`, if
`κ(φ_π − 1) + (1 − β)φ_y > 0`, the rule `i_t = r^n_t + φ_ππ_t + φ_yx_t` implements strict inflation
targeting, for any natural-rate process `r^n`. -/
theorem eq_19_31 [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ φπ φy : ℝ} (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφy : 0 ≤ φy)
    (h31 : 0 < κ * (φπ - 1) + (1 - β) * φy) (rn : ℕ → V) :
    mpImplements E κ β γ φπ φy rn rn := by
  have hz : mpRuleEqm E κ β γ φπ φy rn rn 0 := (mp_zero_eqm_iff E hγ.ne' κ β φπ φy rn rn).2
    fun _ => rfl
  refine ⟨hz, fun X hX hXa hXs => ?_⟩
  have hdet := ex_2_2_suff E hκ hβ0 hβ1 hγ hφy (Or.inl h31)
  obtain ⟨Y, -, hYu⟩ := hdet (fun _ => 0) (fun _ => 0) ⟨0, fun _ => by simp⟩
    ⟨0, fun _ => by simp⟩ (fun _ => map_zero _) (fun _ => map_zero _)
  have h1 := hYu X ⟨(mp_rule_eqm_rn_iff E κ β γ φπ φy rn X).1 hX, hXa, hXs⟩
  have h2 := hYu 0 ⟨(mp_rule_eqm_rn_iff E κ β γ φπ φy rn 0).1 hz, fun _ _ => map_zero _,
    ⟨1, one_pos, fun _ _ => by simp⟩⟩
  exact h1.trans h2.symm

/-- **Exercise 19.2** (Miao, p. 669), corrected. For `κ, γ > 0`, `0 < β < 1`, `φ_π, φ_y ≥ 0`, and
`V` containing a nonzero `F_0`-measurable `w`, the rule `i_t = r^n_t + φ_ππ_t + φ_yx_t` implements
the optimal policy (strict inflation targeting) iff (19.31) `κ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem ex_19_2 [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ φπ φy : ℝ} (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) {w : V}
    (hw : w ≠ 0) (hw0 : E.E 0 w = w) (rn : ℕ → V) :
    mpImplements E κ β γ φπ φy rn rn ↔ 0 < κ * (φπ - 1) + (1 - β) * φy := by
  refine ⟨fun himp => ?_, fun h31 => eq_19_31 E hκ hβ0 hβ1 hγ hφy h31 rn⟩
  by_contra hc
  have hnb : ¬ nkBothOut (nkWT κ β γ φπ φy 0 0 + nkWT κ β γ φπ φy 1 1)
      (nkWT κ β γ φπ φy 0 0 * nkWT κ β γ φπ φy 1 1 -
        nkWT κ β γ φπ φy 0 1 * nkWT κ β γ φπ φy 1 0) := by
    intro hb
    rcases (nk_bothOut_WT hκ hβ0 hβ1 hγ hφy).1 hb with h | h
    · exact hc h
    · nlinarith [mul_nonneg hκ.le hφπ, mul_nonneg hβ0.le hφy]
  have hM10 : nkWT κ β γ φπ φy 1 0 ≠ 0 := by
    have e : nkWT κ β γ φπ φy 1 0 = -κ / β := by simp [nkWT]
    rw [e]
    exact div_ne_zero (neg_ne_zero.2 hκ.ne') hβ0.ne'
  obtain ⟨X, hX0, hXe, hXa, hXs⟩ := nk_jump2_nonunique E (nkWT κ β γ φπ φy) hM10
    (nk_WT_trace hκ hβ0 hβ1 hγ hφy) hnb hw hw0
  have hz : (![γ⁻¹ • (0 : V) - 0, 0] : Fin 2 → V) = 0 := by
    funext i
    fin_cases i <;> simp
  have hXeq : mpRuleEqm E κ β γ φπ φy rn rn X :=
    (mp_rule_eqm_rn_iff E κ β γ φπ φy rn X).2
      ((nk_taylor_iff E φπ φy hβ0.ne' _ _ X).2 fun t => by rw [hXe t, hz, add_zero])
  exact hX0 (himp.2 X hXeq hXa hXs)

/-- **The printed rule (19.29) fails** (Miao, pp. 635 and 669). With a constant intercept `c`
(`c = −ln β` in (19.29)), if the natural rate differs from `c` at some date (`γ ≠ 0`), strict
inflation targeting is not an equilibrium, so the rule does not implement it. -/
theorem mp_printed_rule_fails (E : CondExpSystem ℝ V) {γ : ℝ} (hγ : γ ≠ 0) (κ β φπ φy : ℝ)
    (rn : ℕ → V) (c : V) (hrn : ∃ t, rn t ≠ c) :
    ¬ mpImplements E κ β γ φπ φy rn (fun _ => c) := by
  rintro ⟨h0, -⟩
  obtain ⟨t, ht⟩ := hrn
  exact ht ((mp_zero_eqm_iff E hγ κ β φπ φy rn (fun _ => c)).1 h0 t).symm

/-- The deterministic conditional-expectation system on `ℝ`: `E_t = id`. -/
noncomputable def mpDetSystem : CondExpSystem ℝ ℝ where
  E := fun _ => ContinuousLinearMap.id ℝ ℝ
  norm_le := fun _ => ContinuousLinearMap.norm_id_le
  tower_le := fun _ _ _ => ContinuousLinearMap.id_comp _
  tower_ge := fun _ _ _ => ContinuousLinearMap.id_comp _

/-- **Counterexample to the printed Exercise 19.2** (Miao, p. 669). In the deterministic system
with `κ = γ = 1`, `β = 1/2`, `φ_π = 3/2`, `φ_y = 0` ((19.31) holds), a natural rate `r^n ≡ 1`
and the printed constant intercept `0` (the steady-state rate), the rule does not implement
strict inflation targeting, while the rule with intercept `r^n_t` does. -/
theorem mp_printed_rule_counterexample :
    0 < (1 : ℝ) * (3 / 2 - 1) + (1 - 1 / 2) * 0 ∧
      ¬ mpImplements mpDetSystem 1 (1 / 2) 1 (3 / 2) 0 (fun _ => 1) (fun _ => 0) ∧
      mpImplements mpDetSystem 1 (1 / 2) 1 (3 / 2) 0 (fun _ => 1) (fun _ => 1) := by
  refine ⟨by norm_num, mp_printed_rule_fails mpDetSystem one_ne_zero 1 (1 / 2) (3 / 2) 0 _ 0
    ⟨0, one_ne_zero⟩, eq_19_31 mpDetSystem one_pos (by norm_num) (by norm_num) one_pos le_rfl
    (by norm_num) _⟩

/-- **Exercise 19.2, an instance**: the hypotheses of `ex_19_2` are satisfiable (deterministic
system, `w = 1`), and there the rule with `φ_π = 3/2`, `φ_y = 0` implements the optimal policy
while `φ_π = 1/2` does not. -/
theorem mp_ex_19_2_instance (rn : ℕ → ℝ) :
    mpImplements mpDetSystem 1 (1 / 2) 1 (3 / 2) 0 rn rn ∧
      ¬ mpImplements mpDetSystem 1 (1 / 2) 1 (1 / 2) 0 rn rn := by
  have hw0 : mpDetSystem.E 0 (1 : ℝ) = 1 := rfl
  refine ⟨(ex_19_2 mpDetSystem one_pos (by norm_num) (by norm_num) one_pos (by norm_num) le_rfl
    one_ne_zero hw0 rn).2 (by norm_num), fun h => ?_⟩
  have := (ex_19_2 mpDetSystem one_pos (by norm_num) (by norm_num) one_pos (by norm_num) le_rfl
    one_ne_zero hw0 rn).1 h
  norm_num at this

end Miao.NewKeynesian
