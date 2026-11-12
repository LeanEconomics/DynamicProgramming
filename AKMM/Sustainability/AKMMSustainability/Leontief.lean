/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSustainability.CakeEating

/-!
# Strong complementarity: the Leontief resource economy

AKMM, §25.5.3, "Strong complementarity" (p. 779). Output is `y_t = min{Ak_t^α, e_t}`,
`c_t + k_{t+1} = y_t`, `Σ_t e_t ≤ R`, `k₀` given, utility `Σβ^t log c_t`. The book argues,
"without fully solving the model", that `Ak_t^α = e_t` at all dates and that `e` first rises
and then falls.

* **No idle capital** (`leontief_no_idle_capital`): if `Ak_t^α > e_t` at some `t ≥ 1`, lowering
  `k_t` to `(e_t/A)^{1/α}` leaves output unchanged and raises `c_{t−1}`; so an optimal plan has
  `Ak_t^α ≤ e_t` for `t ≥ 1` (`leontief_optimal_no_idle`).
* **No waste** (`leontief_no_waste`): cutting `e_t` to `min{e_t, Ak_t^α}` leaves every `c_t`
  unchanged and uses no more of the resource. So from any optimal plan one obtains an optimal
  plan with `e_t = Ak_t^α` for all `t ≥ 1` (`leontief_optimal_tight`) — the book's claim.
* **At date 0** the claim `e₀ = Ak₀^α` needs `R ≥ Ak₀^α` (the book's "`R₀` was high in
  relation to `Ak₀^α`"); otherwise it is infeasible (`leontief_e0_infeasible`).
* **Eventual decline**: along any feasible plan `e_t → 0`, and every `e_t` is followed by a
  smaller one (`leontief_eventually_declines`).
* **Initial rise, abundant resource**: when the resource constraint does not bind the economy
  is the log/Cobb–Douglas growth model, whose optimal policy is `k_{t+1} = αβk_t^α`
  (Stokey–Lucas, reused from `DeterministicApplications`, with `A = 1`); from `k₀` below the
  steady state, capital and resource use `e_t = k_t^α` rise strictly at every date
  (`leontief_abundant`). The full hump-shaped path for finite `R` is asserted, not derived, in
  the book and is not formalised.
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

/-- AKMM, p. 779: Leontief output `y = min{Ak^α, e}`. -/
noncomputable def leontiefY (A α k e : ℝ) : ℝ := min (A * k ^ α) e

/-- Consumption `c_t = y_t − k_{t+1}`. -/
noncomputable def leontiefC (A α : ℝ) (k e : ℕ → ℝ) (t : ℕ) : ℝ :=
  leontiefY A α (k t) (e t) - k (t + 1)

/-- A feasible plan of the Leontief economy. -/
def LeontiefFeasible (A α R K0 : ℝ) (k e : ℕ → ℝ) : Prop :=
  k 0 = K0 ∧ (∀ t, 0 < k t) ∧ (∀ t, 0 < e t) ∧ (∀ T, ∑ t ∈ range T, e t ≤ R) ∧
    ∀ t, 0 < leontiefC A α k e t

/-- A feasible Leontief plan exists (so `LeontiefFeasible` is not vacuous): extract
`e_t = (1/2)^{t+1}R` and save half of output. -/
theorem leontief_feasible_exists {A α R K0 : ℝ} (hA : 0 < A) (hR : 0 < R) (hK0 : 0 < K0) :
    ∃ k e : ℕ → ℝ, LeontiefFeasible A α R K0 k e := by
  set e : ℕ → ℝ := cakePath (1 / 2) R with he
  have he0 : ∀ t, 0 < e t := fun t => by simp only [he, cakePath]; positivity
  set k : ℕ → ℝ := fun t => Nat.rec (motive := fun _ => ℝ) K0
    (fun n kn => leontiefY A α kn (e n) / 2) t with hk
  have hk1 : ∀ t, k (t + 1) = leontiefY A α (k t) (e t) / 2 := fun t => rfl
  have hkpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hK0
    | succ n ih =>
      rw [hk1]
      have : 0 < leontiefY A α (k n) (e n) :=
        lt_min (by have := Real.rpow_pos_of_pos ih α; positivity) (he0 n)
      positivity
  refine ⟨k, e, rfl, hkpos, he0, fun T => ?_, fun t => ?_⟩
  · rw [he, cake_partial_sum]
    have : 0 ≤ (1 / 2 : ℝ) ^ T * R := by positivity
    linarith
  · unfold leontiefC
    rw [hk1]
    have : 0 < leontiefY A α (k t) (e t) :=
      lt_min (by have := Real.rpow_pos_of_pos (hkpos t) α; positivity) (he0 t)
    linarith

/-- AKMM, p. 779: lowering idle capital. If `Ak_{s+1}^α > e_{s+1}`, replacing `k_{s+1}` by
`(e_{s+1}/A)^{1/α}` gives a feasible plan whose consumption is unchanged except at `s`, where it
is strictly higher. -/
theorem leontief_no_idle_capital {A α R K0 : ℝ} (hA : 0 < A) (hα : 0 < α) {k e : ℕ → ℝ}
    (hF : LeontiefFeasible A α R K0 k e) {s : ℕ} (hidle : e (s + 1) < A * k (s + 1) ^ α) :
    LeontiefFeasible A α R K0 (Function.update k (s + 1) ((e (s + 1) / A) ^ (1 / α))) e ∧
      leontiefC A α k e s <
        leontiefC A α (Function.update k (s + 1) ((e (s + 1) / A) ^ (1 / α))) e s ∧
      ∀ t ≠ s, leontiefC A α (Function.update k (s + 1) ((e (s + 1) / A) ^ (1 / α))) e t =
        leontiefC A α k e t := by
  obtain ⟨hk0, hk, he, hsum, hc⟩ := hF
  set v := (e (s + 1) / A) ^ (1 / α) with hv
  set k' := Function.update k (s + 1) v with hk'
  have hv0 : 0 < v := by have := he (s + 1); positivity
  have hvα : A * v ^ α = e (s + 1) := by
    rw [hv, ← Real.rpow_mul (by have := he (s + 1); positivity), one_div_mul_cancel hα.ne',
      Real.rpow_one]
    field_simp
  have hvk : v < k (s + 1) := by
    by_contra h
    rw [not_lt] at h
    have : A * k (s + 1) ^ α ≤ A * v ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hk _).le h hα.le) hA.le
    linarith
  have hy1 : leontiefY A α v (e (s + 1)) = leontiefY A α (k (s + 1)) (e (s + 1)) := by
    unfold leontiefY
    rw [hvα, min_self, min_eq_right hidle.le]
  have hcs : leontiefC A α k' e s = leontiefC A α k e s + (k (s + 1) - v) := by
    unfold leontiefC
    rw [hk', Function.update_of_ne (by omega), Function.update_self]
    ring
  have hrest : ∀ t ≠ s, leontiefC A α k' e t = leontiefC A α k e t := by
    intro t ht
    unfold leontiefC
    by_cases h1 : t = s + 1
    · subst h1
      rw [hk', Function.update_self, Function.update_of_ne (by omega), hy1]
    · rw [hk', Function.update_of_ne h1, Function.update_of_ne (by omega)]
  refine ⟨⟨by rw [hk', Function.update_of_ne (by omega)]; exact hk0, fun t => ?_, he, hsum,
    fun t => ?_⟩, by rw [hcs]; linarith, hrest⟩
  · by_cases h1 : t = s + 1
    · subst h1; rw [hk', Function.update_self]; exact hv0
    · rw [hk', Function.update_of_ne h1]; exact hk t
  · by_cases h1 : t = s
    · subst h1; rw [hcs]; linarith [hc t]
    · rw [hrest t h1]; exact hc t

/-- AKMM, p. 779: "a Leontief function implies that `Ak_t^α = e_t` must hold": an optimal plan
(maximal utility among feasible plans with convergent utility) has no idle capital at dates
`t ≥ 1`: `Ak_t^α ≤ e_t`. -/
theorem leontief_optimal_no_idle {A α β R K0 U : ℝ} (hA : 0 < A) (hα : 0 < α) (hβ : 0 < β)
    {k e : ℕ → ℝ} (hF : LeontiefFeasible A α R K0 k e)
    (hU : HasSum (fun t => β ^ t * Real.log (leontiefC A α k e t)) U)
    (hopt : ∀ k' e' : ℕ → ℝ, LeontiefFeasible A α R K0 k' e' → ∀ U',
      HasSum (fun t => β ^ t * Real.log (leontiefC A α k' e' t)) U' → U' ≤ U) (s : ℕ) :
    A * k (s + 1) ^ α ≤ e (s + 1) := by
  by_contra h
  rw [not_le] at h
  obtain ⟨hF', hlt, hrest⟩ := leontief_no_idle_capital hA hα hF h
  set k' := Function.update k (s + 1) ((e (s + 1) / A) ^ (1 / α))
  set gain := β ^ s * (Real.log (leontiefC A α k' e s) - Real.log (leontiefC A α k e s))
  have hgain : 0 < gain := by
    have := Real.log_lt_log (hF.2.2.2.2 s) hlt
    have : 0 < β ^ s := by positivity
    simp only [gain]; nlinarith
  have hU' : HasSum (fun t => β ^ t * Real.log (leontiefC A α k' e t)) (U + gain) := by
    convert hU.add (hasSum_ite_eq s gain) using 1
    funext t
    by_cases ht : t = s
    · subst ht; simp only [gain, ↓reduceIte]; ring
    · simp only [ht, ↓reduceIte, add_zero, hrest t ht]
  have := hopt k' e hF' _ hU'
  linarith

/-- AKMM, p. 779: wasting the resource never helps: with `e'_t = min{e_t, Ak_t^α}` the plan is
feasible, every `c_t` is unchanged, and no more of the resource is used. -/
theorem leontief_no_waste {A α R K0 : ℝ} (hA : 0 < A) {k e : ℕ → ℝ}
    (hF : LeontiefFeasible A α R K0 k e) :
    LeontiefFeasible A α R K0 k (fun t => min (e t) (A * k t ^ α)) ∧
      ∀ t, leontiefC A α k (fun t => min (e t) (A * k t ^ α)) t = leontiefC A α k e t := by
  obtain ⟨hk0, hk, he, hsum, hc⟩ := hF
  have hsame : ∀ t, leontiefC A α k (fun t => min (e t) (A * k t ^ α)) t =
      leontiefC A α k e t := by
    intro t
    unfold leontiefC leontiefY
    simp only
    rw [min_comm (e t) (A * k t ^ α), ← min_assoc, min_self]
  refine ⟨⟨hk0, hk, fun t => lt_min (he t) (by have := hk t; positivity), fun T => ?_,
    fun t => by rw [hsame]; exact hc t⟩, hsame⟩
  exact le_trans (sum_le_sum fun t _ => min_le_left _ _) (hsum T)

/-- AKMM, p. 779: an optimal plan can be taken with `Ak_t^α = e_t` at every date `t ≥ 1`: the
waste-free version of an optimal plan is feasible, has the same consumption (hence the same
utility) and uses exactly `e_t = Ak_t^α` for `t ≥ 1`. -/
theorem leontief_optimal_tight {A α β R K0 U : ℝ} (hA : 0 < A) (hα : 0 < α) (hβ : 0 < β)
    {k e : ℕ → ℝ} (hF : LeontiefFeasible A α R K0 k e)
    (hU : HasSum (fun t => β ^ t * Real.log (leontiefC A α k e t)) U)
    (hopt : ∀ k' e' : ℕ → ℝ, LeontiefFeasible A α R K0 k' e' → ∀ U',
      HasSum (fun t => β ^ t * Real.log (leontiefC A α k' e' t)) U' → U' ≤ U) :
    LeontiefFeasible A α R K0 k (fun t => min (e t) (A * k t ^ α)) ∧
      HasSum (fun t => β ^ t * Real.log
        (leontiefC A α k (fun t => min (e t) (A * k t ^ α)) t)) U ∧
      ∀ s, min (e (s + 1)) (A * k (s + 1) ^ α) = A * k (s + 1) ^ α := by
  obtain ⟨hF', hsame⟩ := leontief_no_waste hA hF
  refine ⟨hF', by simpa only [hsame] using hU, fun s => ?_⟩
  exact min_eq_right (leontief_optimal_no_idle hA hα hβ hF hU hopt s)

/-- AKMM, p. 779: "At time 0, this means that `e₀` must be given by `Ak₀^α`" requires
`R ≥ Ak₀^α`: if `R < Ak₀^α`, every feasible plan has `e₀ < Ak₀^α`. -/
theorem leontief_e0_infeasible {A α R K0 : ℝ} {k e : ℕ → ℝ}
    (hF : LeontiefFeasible A α R K0 k e) (hR : R < A * K0 ^ α) : e 0 < A * k 0 ^ α := by
  obtain ⟨hk0, -, -, hsum, -⟩ := hF
  have := hsum 1
  simp only [range_one, sum_singleton] at this
  rw [hk0]
  linarith

/-- AKMM, p. 779: "eventually, `e` will have to decline": along any feasible plan `e_t → 0`, so
after every date there is a later date with strictly smaller resource use. -/
theorem leontief_eventually_declines {A α R K0 : ℝ} {k e : ℕ → ℝ}
    (hF : LeontiefFeasible A α R K0 k e) :
    Tendsto e atTop (𝓝 0) ∧ ∀ t, ∃ s, t < s ∧ e s < e t := by
  obtain ⟨-, -, he, hsum, -⟩ := hF
  have hs : Summable e := summable_of_sum_range_le (fun t => (he t).le) hsum
  have hlim := hs.tendsto_atTop_zero
  refine ⟨hlim, fun t => ?_⟩
  have h1 : ∀ᶠ s in atTop, e s < e t := hlim.eventually (gt_mem_nhds (he t))
  obtain ⟨s, hs1, hs2⟩ := (h1.and (eventually_gt_atTop t)).exists
  exact ⟨s, hs2, hs1⟩

/-- Below the steady state `k̄ = (αβ)^{1/(1−α)}`, the policy `k ↦ αβk^α` raises capital and
stays below `k̄`. -/
theorem leontief_policy_step {α β k : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hab : 0 < α * β)
    (hk : 0 < k) (hkb : k < (α * β) ^ (1 / (1 - α))) :
    k < α * β * k ^ α ∧ α * β * k ^ α < (α * β) ^ (1 / (1 - α)) := by
  have h1α : 0 < 1 - α := by linarith
  set kb := (α * β) ^ (1 / (1 - α)) with hkb'
  have hkb0 : 0 < kb := by positivity
  have hkb1 : kb ^ (1 - α) = α * β := by
    rw [hkb', ← Real.rpow_mul hab.le, one_div_mul_cancel h1α.ne', Real.rpow_one]
  have hka := Real.rpow_pos_of_pos hk α
  constructor
  · have h := Real.rpow_lt_rpow hk.le hkb h1α
    rw [hkb1] at h
    have : k = k ^ (1 - α) * k ^ α := by
      rw [← Real.rpow_add hk]; simp
    calc k = k ^ (1 - α) * k ^ α := this
      _ < α * β * k ^ α := mul_lt_mul_of_pos_right h hka
  · have h := Real.rpow_lt_rpow hk.le hkb hα0
    have : kb = kb ^ (1 - α) * kb ^ α := by
      rw [← Real.rpow_add hkb0]; simp
    calc α * β * k ^ α < α * β * kb ^ α := mul_lt_mul_of_pos_left h hab
      _ = kb := by rw [← hkb1, ← this]

/-- AKMM, p. 779: "the optimal allocation would be to accumulate capital over time, i.e.
`k₀ < k₁ < k₂ …`, so that `e_t = Ak_t^α` is increasing over time" — in the limit of an
abundant resource (`A = 1`), where the economy is the Stokey–Lucas log/Cobb–Douglas model. Its
optimal plan (`DeterministicApplications`: `log_policy_optimal`) is `k_{t+1} = αβk_t^α`, and
from `k₀ < (αβ)^{1/(1−α)}` capital and resource use rise strictly at every date. -/
theorem leontief_abundant {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (k₀ : StokeyLucasPrescott.DeterministicApplications.PosR)
    (hk₀ : k₀.1 < (α * β) ^ (1 / (1 - α))) :
    StokeyLucasPrescott.DeterministicApplications.total
        (StokeyLucasPrescott.DeterministicApplications.logF α) β
        (fun t => (StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0)^[t] k₀) =
      StokeyLucasPrescott.DeterministicApplications.vstar
        (StokeyLucasPrescott.DeterministicApplications.logΓ α)
        (StokeyLucasPrescott.DeterministicApplications.logF α) β k₀ ∧
    ∀ t, ((StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0)^[t] k₀).1 <
        ((StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0)^[t + 1] k₀).1 ∧
      ((StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0)^[t] k₀).1 ^ α <
        ((StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0)^[t + 1] k₀).1 ^
          α := by
  have hab : 0 < α * β := mul_pos hα0 hβ0
  set g := StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0
  have hg : ∀ x, (g x).1 = α * β * x.1 ^ α := fun x => rfl
  have hbelow : ∀ t, (g^[t] k₀).1 < (α * β) ^ (1 / (1 - α)) := by
    intro t
    induction t with
    | zero => exact hk₀
    | succ n ih =>
      rw [Function.iterate_succ_apply', hg]
      exact (leontief_policy_step hα0 hα1 hab (g^[n] k₀).2 ih).2
  refine ⟨StokeyLucasPrescott.DeterministicApplications.log_policy_optimal hα0 hα1.le hβ0 hβ1 k₀,
    fun t => ?_⟩
  have hstep : (g^[t] k₀).1 < (g^[t + 1] k₀).1 := by
    rw [Function.iterate_succ_apply', hg]
    exact (leontief_policy_step hα0 hα1 hab (g^[t] k₀).2 (hbelow t)).1
  exact ⟨hstep, Real.rpow_lt_rpow (g^[t] k₀).2.le hstep hα0⟩

end AKMM.Sustainability
