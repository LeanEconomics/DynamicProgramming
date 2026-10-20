/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.GrowthCertaintyHousehold

/-!
# The one-sector model under certainty: the planner's policy and the price `q(k)`

SLP §16.1, p. 480, equations (3)–(4). The planner's problem (3)
`v(k) = max_{0 ≤ k′ ≤ f(k)} {U[f(k) − k′] + β v(k′)}` has a policy `g` with consumption
`c(k) = f(k) − g(k)`. `GrowthCertaintyPlanner` records the properties of `(g, c)` used in
Exercise 16.1(e)–(g) — the properties the solution of (3) has under the interiority conditions of
Exercise 5.1d (Chapters 4–6): `g` maps an interval `K = [a, k_max]`, `a > 0`, continuously into
itself, `c > 0` on `K`, and the Euler equation `U′(c(k)) = β f′(g(k)) U′(c(g(k)))` holds on `K`.
(These are hypotheses here; they are not derived from (3).)

* `gcQ`: the **corrected** price (4), `q(k) = β U′(c[g(k)]) / U′[c(k)]`; `gcQPrinted`: (4) as
  printed, with the spurious factor `f′(k)`.
* `gc_planner_q_mul_df`: `q(k) f′(g(k)) = 1`, i.e. `1 + r = f′(k_{t+1})` as in Ex 16.1d;
  `gc_planner_household_foc`: `q(k) U′(c(k)) = β U′(c(g(k)))`, the household's first-order and
  envelope conditions for (2) at the equilibrium.
* `gc_planner_steady_state`: `g` has a steady state `k* ∈ K` (intermediate value theorem).
* `gc_eq4_typo_counterexample`: at a steady state the printed (4) gives `q = 1`, the corrected
  formula `q = β`, and the printed value violates the household's first-order condition.
* `gc_planner_prod_q`: `Π_{s<n} q(gˢ(k)) = βⁿ U′(c(gⁿ(k)))/U′(c(k))`; `gc_planner_firmData`: the
  **uniform** bound `≤ M βⁿ` with `M = max U′(c)/min U′(c)` on `K`, so (1) is well posed
  (`GcFirmData`); `gc_planner_hhData`: the data of (2) (`GcHouseholdData`).
* `gc_logCD_q_gt_one`: in the log-utility, `f(k) = √k` economy (`g(k) = √k/4`, `β = 1/2`), the
  Euler equation holds and `q(16) = 2 > 1`: (1) is not a contraction (`ex_16_1e_not_contraction`).

**Corrections.**
* (p. 480, eq. (4)) The factor `f′(k)` must not be there; the correct price is
  `q(k) = βU′(c[g(k)])/U′[c(k)] = 1/f′(g(k))` (`gc_eq4_typo_counterexample`).
* (manual, Ex 16.1e) The contraction modulus and `M` must not depend on `k`; the uniform bound is
  `gc_planner_firmData`. `q(k) > 1` does occur (`gc_logCD_q_gt_one`; that economy has unbounded `U`,
  outside §16.1's class, but `q` only involves `U′`).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

/-- The properties of the planner's policy `g` and consumption `c = f − g` used in Ex 16.1(e)–(g):
`U`, `f` as in §16.1 with derivatives `U′ = dU > 0`, `f′ = df`, an invariant interval
`K = [a, k_max]` with `a > 0`, interior consumption, and the Euler equation on `K`. -/
structure GrowthCertaintyPlanner (U f g c dU df : ℝ → ℝ) (β a kmax : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  a_pos : 0 < a
  a_le : a ≤ kmax
  U_bdd : ∃ B, ∀ x, 0 ≤ x → |U x| ≤ B
  U_cont : ContinuousOn U (Ici 0)
  U_strictConcave : StrictConcaveOn ℝ (Ici 0) U
  dU_deriv : ∀ x, 0 < x → HasDerivAt U (dU x) x
  dU_pos : ∀ x, 0 < x → 0 < dU x
  dU_cont : ContinuousOn dU (Ioi 0)
  f_cont : ContinuousOn f (Ici 0)
  f_strictConcave : StrictConcaveOn ℝ (Ici 0) f
  f_nonneg : ∀ z, 0 ≤ z → 0 ≤ f z
  f_le : ∀ z, 0 ≤ z → z ≤ kmax → f z ≤ kmax
  df_deriv : ∀ k, 0 < k → HasDerivAt f (df k) k
  g_cont : ContinuousOn g (Icc a kmax)
  g_mem : ∀ k ∈ Icc a kmax, g k ∈ Icc a kmax
  c_eq : ∀ k ∈ Icc a kmax, c k = f k - g k
  c_pos : ∀ k ∈ Icc a kmax, 0 < c k
  euler : ∀ k ∈ Icc a kmax, dU (c k) = β * df (g k) * dU (c (g k))

/-- The **corrected** equilibrium price (4): `q(k) = β U′(c[g(k)]) / U′[c(k)]`. -/
noncomputable def gcQ (β : ℝ) (dU c g : ℝ → ℝ) (k : ℝ) : ℝ := β * dU (c (g k)) / dU (c k)

/-- Equation (4) **as printed** (p. 480): `q(k) = β f′(k) U′(c[g(k)]) / U′[c(k)]`. -/
noncomputable def gcQPrinted (β : ℝ) (dU c g df : ℝ → ℝ) (k : ℝ) : ℝ :=
  β * df k * dU (c (g k)) / dU (c k)

variable {U f g c dU df : ℝ → ℝ} {β a kmax : ℝ}

/-- `g` as a self-map of `K`. -/
def gcGK (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax) : Icc a kmax :=
  ⟨g k, H.g_mem k k.2⟩

/-- `q` as a function on `K`. -/
noncomputable def gcQK (β : ℝ) (dU c g : ℝ → ℝ) (k : Icc a kmax) : ℝ := gcQ β dU c g k

/-- `U′(c(k)) > 0` on `K`. -/
theorem gc_planner_dUc_pos (H : GrowthCertaintyPlanner U f g c dU df β a kmax) {k : ℝ}
    (hk : k ∈ Icc a kmax) : 0 < dU (c k) := H.dU_pos _ (H.c_pos k hk)

/-- `q(k) > 0` on `K`. -/
theorem gc_planner_q_pos (H : GrowthCertaintyPlanner U f g c dU df β a kmax) {k : ℝ}
    (hk : k ∈ Icc a kmax) : 0 < gcQ β dU c g k :=
  div_pos (mul_pos H.beta_pos (gc_planner_dUc_pos H (H.g_mem k hk))) (gc_planner_dUc_pos H hk)

/-- **The household's first-order and envelope conditions** for (2) at the equilibrium:
`q(k) U′(c(k)) = β U′(c(g(k)))`. -/
theorem gc_planner_household_foc (H : GrowthCertaintyPlanner U f g c dU df β a kmax) {k : ℝ}
    (hk : k ∈ Icc a kmax) : gcQ β dU c g k * dU (c k) = β * dU (c (g k)) := by
  rw [gcQ, div_mul_cancel₀ _ (gc_planner_dUc_pos H hk).ne']

/-- `q(k) f′(g(k)) = 1` (from the planner's Euler equation): the price of next period's good is
`1/f′(k_{t+1})`, so `1 + r_t = f′(k_{t+1})` (Ex 16.1d). -/
theorem gc_planner_q_mul_df (H : GrowthCertaintyPlanner U f g c dU df β a kmax) {k : ℝ}
    (hk : k ∈ Icc a kmax) : gcQ β dU c g k * df (g k) = 1 := by
  have he := H.euler k hk
  have hpos := gc_planner_dUc_pos H hk
  rw [gcQ, div_mul_eq_mul_div, div_eq_one_iff_eq hpos.ne', he]
  ring

/-- `g` has a **steady state** in `K` (intermediate value theorem for `k − g(k)`). -/
theorem gc_planner_steady_state (H : GrowthCertaintyPlanner U f g c dU df β a kmax) :
    ∃ k ∈ Icc a kmax, g k = k := by
  have hc : ContinuousOn (fun k => k - g k) (Icc a kmax) := continuousOn_id.sub H.g_cont
  have ha := H.g_mem a ⟨le_rfl, H.a_le⟩
  have hb := H.g_mem kmax ⟨H.a_le, le_rfl⟩
  obtain ⟨k, hk, hk0⟩ := intermediate_value_Icc H.a_le hc
    (⟨by linarith [ha.1], by linarith [hb.2]⟩ : (0 : ℝ) ∈ Icc (a - g a) (kmax - g kmax))
  exact ⟨k, hk, by linarith [hk0]⟩

/-- **Counterexample to (4) as printed** (p. 480): at a steady state `k* = g(k*)` the printed
formula gives `q(k*) = 1` and the corrected one `q(k*) = β`; the printed value violates the
household's first-order condition `q U′(c) = β U′(c(g(k)))`. Every economy satisfying
`GrowthCertaintyPlanner` has a steady state (`gc_planner_steady_state`). -/
theorem gc_eq4_typo_counterexample (H : GrowthCertaintyPlanner U f g c dU df β a kmax) {k : ℝ}
    (hk : k ∈ Icc a kmax) (hfix : g k = k) :
    gcQPrinted β dU c g df k = 1 ∧ gcQ β dU c g k = β ∧
      gcQPrinted β dU c g df k * dU (c k) ≠ β * dU (c (g k)) := by
  have he := H.euler k hk
  rw [hfix] at he
  have hpos := gc_planner_dUc_pos H hk
  have h1 : β * df k = 1 := by
    have : dU (c k) * (β * df k) = dU (c k) * 1 := by rw [mul_one]; linarith
    exact mul_left_cancel₀ hpos.ne' this
  refine ⟨?_, ?_, ?_⟩
  · rw [gcQPrinted, hfix, h1, one_mul, div_self hpos.ne']
  · rw [gcQ, hfix, mul_div_assoc, div_self hpos.ne', mul_one]
  · rw [gcQPrinted, hfix, h1, one_mul, div_self hpos.ne', one_mul]
    intro h
    have := H.beta_lt_one
    nlinarith

/-! ### The data of (1) and (2) -/

/-- `U′(c(·))` is continuous on `K`. -/
theorem gc_planner_dUc_continuousOn (H : GrowthCertaintyPlanner U f g c dU df β a kmax) :
    ContinuousOn (fun k => dU (c k)) (Icc a kmax) := by
  have hc : ContinuousOn c (Icc a kmax) :=
    ((H.f_cont.mono fun k hk => le_trans H.a_pos.le hk.1).sub H.g_cont).congr
      fun k hk => H.c_eq k hk
  exact H.dU_cont.comp hc fun k hk => H.c_pos k hk

/-- Iterates of `g` on `K` are iterates of `g`. -/
theorem gcGK_iterate (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (n : ℕ)
    (k : Icc a kmax) : (((gcGK H)^[n] k : Icc a kmax) : ℝ) = g^[n] k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

/-- **The discount factors along the equilibrium path**:
`Π_{s<n} q(gˢ(k)) = βⁿ U′(c(gⁿ(k)))/U′(c(k))`. -/
theorem gc_planner_prod_q (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax)
    (n : ℕ) : gcDisc (gcGK H) (gcQK β dU c g) n k =
      β ^ n * dU (c (((gcGK H)^[n] k : Icc a kmax) : ℝ)) / dU (c k) := by
  induction n with
  | zero => simp [gcDisc, div_self (gc_planner_dUc_pos H k.2).ne']
  | succ n ih =>
    rw [gcDisc_succ', ih, gcQK, gcQ, Function.iterate_succ_apply']
    have h1 := (gc_planner_dUc_pos H k.2).ne'
    have h2 := (gc_planner_dUc_pos H ((gcGK H)^[n] k).2).ne'
    change β ^ n * dU (c ((gcGK H)^[n] k)) / dU (c k) *
      (β * dU (c (g ((gcGK H)^[n] k))) / dU (c ((gcGK H)^[n] k))) =
      β ^ (n + 1) * dU (c (g ((gcGK H)^[n] k))) / dU (c k)
    field_simp
    ring

/-- `gcGK` is continuous. -/
theorem gcGK_continuous (H : GrowthCertaintyPlanner U f g c dU df β a kmax) :
    Continuous (gcGK H) :=
  Continuous.subtype_mk (H.g_cont.comp_continuous continuous_subtype_val fun k => k.2) _

/-- `q` is continuous on `K`. -/
theorem gcQK_continuous (H : GrowthCertaintyPlanner U f g c dU df β a kmax) :
    Continuous (gcQK (a := a) (kmax := kmax) β dU c g) := by
  have hd := gc_planner_dUc_continuousOn H
  have hq : ContinuousOn (gcQ β dU c g) (Icc a kmax) :=
    (continuousOn_const.mul (hd.comp H.g_cont fun k hk => H.g_mem k hk)).div hd
      fun k hk => (gc_planner_dUc_pos H hk).ne'
  exact hq.comp_continuous continuous_subtype_val fun k => k.2

/-- **The uniform bound** (NOTE to the manual's Ex 16.1e): with `M = max_K U′(c)/min_K U′(c)`,
`Π_{s<n} q(gˢ(k)) ≤ M βⁿ` for every `k ∈ K` and `n`, so the planner's `(g, q)` are data for (1). -/
theorem gc_planner_firmData (H : GrowthCertaintyPlanner U f g c dU df β a kmax) :
    ∃ M, GcFirmData f (gcGK H) (gcQK β dU c g) β M := by
  have hne : (Icc a kmax).Nonempty := nonempty_Icc.2 H.a_le
  have hd := gc_planner_dUc_continuousOn H
  obtain ⟨k₁, hk₁, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hd
  obtain ⟨k₂, hk₂, hmin⟩ := isCompact_Icc.exists_isMinOn hne hd
  have hmn := gc_planner_dUc_pos H hk₂
  refine ⟨dU (c k₁) / dU (c k₂), ⟨H.beta_pos, H.beta_lt_one, H.a_pos.le.trans H.a_le,
    H.f_cont.mono fun z hz => hz.1, fun z hz => H.f_nonneg z hz.1, fun z hz => H.f_le z hz.1 hz.2,
    gcGK_continuous H, gcQK_continuous H, fun k => gc_planner_q_pos H k.2, fun k n => ?_⟩⟩
  change gcDisc (gcGK H) (gcQK β dU c g) n k ≤ _
  rw [gc_planner_prod_q H k n]
  have h1 : dU (c (((gcGK H)^[n] k : Icc a kmax) : ℝ)) ≤ dU (c k₁) := hmax ((gcGK H)^[n] k).2
  have h2 : dU (c k₂) ≤ dU (c k) := hmin k.2
  have hk := gc_planner_dUc_pos H k.2
  have hβ := pow_pos H.beta_pos n
  rw [div_le_iff₀ hk]
  calc β ^ n * dU (c (((gcGK H)^[n] k : Icc a kmax) : ℝ)) ≤ β ^ n * dU (c k₁) :=
        mul_le_mul_of_nonneg_left h1 hβ.le
    _ = dU (c k₁) / dU (c k₂) * β ^ n * dU (c k₂) := by field_simp
    _ ≤ dU (c k₁) / dU (c k₂) * β ^ n * dU (c k) :=
        mul_le_mul_of_nonneg_left h2
          (mul_nonneg (div_nonneg (gc_planner_dUc_pos H hk₁).le hmn.le) hβ.le)

/-- The planner's `(g, q)` are data for the household's equation (2). -/
theorem gc_planner_hhData (H : GrowthCertaintyPlanner U f g c dU df β a kmax) :
    GcHouseholdData U (gcGK H) (gcQK β dU c g) β :=
  ⟨H.beta_pos, H.beta_lt_one, H.U_bdd, H.U_cont, gcGK_continuous H, gcQK_continuous H,
    fun k => gc_planner_q_pos H k.2⟩

/-! ### `q(k) > 1` happens: a log / square-root example -/

/-- The policy `g(k) = √k/4` of the log-utility economy with `f(k) = √k`, `β = 1/2`. -/
noncomputable def gcLogG (k : ℝ) : ℝ := Real.sqrt k / 4

/-- Consumption `c(k) = 3√k/4 = f(k) − g(k)` in that economy. -/
noncomputable def gcLogC (k : ℝ) : ℝ := 3 * Real.sqrt k / 4

/-- `U′(x) = 1/x` (log utility). -/
noncomputable def gcLogDU (x : ℝ) : ℝ := 1 / x

/-- `f′(k) = 1/(2√k)` for `f(k) = √k`. -/
noncomputable def gcLogDF (k : ℝ) : ℝ := 1 / (2 * Real.sqrt k)

/-- **`q(k) > 1` occurs** (NOTE to Ex 16.1e): in the economy `U = log`, `f(k) = √k`, `β = 1/2`,
the policy `g(k) = √k/4` satisfies `c = f − g` and the Euler equation
`U′(c(k)) = β f′(g(k)) U′(c(g(k)))` for all `k > 0`, and the equilibrium price is
`q(16) = β U′(c(g(16)))/U′(c(16)) = 2 > 1` (also `= 1/f′(g(16))`). So the operator of (1) is not a
contraction there (`ex_16_1e_not_contraction`). -/
theorem gc_logCD_q_gt_one :
    (∀ k, 0 < k → gcLogC k = Real.sqrt k - gcLogG k) ∧
    (∀ k, 0 < k → gcLogDU (gcLogC k) = 1 / 2 * gcLogDF (gcLogG k) * gcLogDU (gcLogC (gcLogG k))) ∧
    gcQ (1 / 2) gcLogDU gcLogC gcLogG 16 = 2 ∧ 1 / gcLogDF (gcLogG 16) = 2 := by
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hg16 : gcLogG 16 = 1 := by rw [gcLogG, h16]; norm_num
  refine ⟨fun k _ => by simp only [gcLogC, gcLogG]; ring, fun k hk => ?_, ?_, ?_⟩
  · have hs : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
    have hs2 : 0 < Real.sqrt (Real.sqrt k / 4) := Real.sqrt_pos.2 (by positivity)
    have hsq : Real.sqrt (Real.sqrt k / 4) * Real.sqrt (Real.sqrt k / 4) = Real.sqrt k / 4 :=
      Real.mul_self_sqrt (by positivity)
    simp only [gcLogDU, gcLogC, gcLogDF, gcLogG]
    field_simp
    nlinarith [hsq]
  · simp only [gcQ, gcLogDU, gcLogC, hg16, Real.sqrt_one, h16]
    norm_num
  · simp only [gcLogDF, hg16, Real.sqrt_one]
    norm_num

end StokeyLucasPrescott.EquilibriumApplications
