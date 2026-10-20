/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.GrowthCertaintySequential
import EquilibriumApplications.GrowthCertaintyDDGrowthStability

/-!
# The one-sector model under certainty: Exercise 16.1(e)–(g) from the Bellman equation (3)

SLP §16.1, p. 480. Here the planner's policy `g` is **the** policy of the Bellman equation (3)
`v(k) = max_{0 ≤ k′ ≤ f(k)} {U[f(k) − k′] + βv(k′)}`, not an assumed function. The properties of `g`
used in Exercise 16.1(e)–(g) (`GrowthCertaintyPlanner`) are derived from Chapters 5–6, copied
into this project as the modules `GrowthCertaintyDD*` (from the Chapter 6 project
`DeterministicDynamics`:
`ExtendedReals`, `Principle`, `Assumption42`, `Contraction`, `Correspondences`, `Maximum`,
`BoundedReturns`, `Concavity`, `OneSectorGrowth`, `WeakConcavity`, `Envelope`, `EulerEquations`,
`GrowthDifferentiability`, `GrowthStability`; namespace `GrowthCertaintyDD`).

Setting (§6.1, `GrowthDyn`): `f`, `U` strictly increasing, strictly concave, continuously
differentiable, `f(0) = 0`, the Inada conditions `f′(0+) = ∞`, `f′(∞) = 0`, `U′(0+) = ∞`; in
addition `U` is bounded on `ℝ₊` (the book's §16.1 assumption) and `0 < k̂ ≤ k̄`. `Setting61` records
`k̄` and the solution `v` of (3) on `[0, k̄]` (it exists: `exists_setting61`).

* `gc_policy_ge_of_le_kstar`: `g(a) ≥ a` for `0 < a ≤ k*` (from the monotone convergence of
  Proposition 6.1).
* `gc_planner_of_bellman`: the policy of (3) and `c = f − g` satisfy `GrowthCertaintyPlanner` on
  `K = [a, k̄]` for every `0 < a ≤ k*` (invariance of `K`, interiority, the Euler equation from
  the first-order and envelope conditions of Exercise 6.1a).
* `gc_hyp_of_dyn`: the §6.1 setting gives `GrowthCertaintyHyp` (§16.1's restrictions).
* **Exercise 16.1(e)–(g) from (3)** (`ex_16_1efg`): with `g` the policy of (3), `q` the price (4)
  (corrected), the functional equations (1) and (2) have unique bounded continuous solutions with
  single-valued continuous policies `h`, `ω`, (R3)–(R4) hold, the sequential allocation from
  `k̂` is `c(gᵗ(k̂))`, and this is the unique optimum `x⁰` of Exercise 16.1(a).
* `ex_16_1efg_exists`: the same with `k̄` and `v` produced by Exercise 5.1, for every
  `0 < k̂ ≤ k̄`.

**Correction.** The exercise needs the Inada (interiority) conditions and differentiability of
§6.1 (or Exercise 5.1d), which §16.1 does not state, and `k̂ ≤ k̄` (the Chapter 5 state space
`[0, k̄]` of maintainable stocks; for `k̂ > k̄` the state space `[0, k̂]` would be needed).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set GrowthCertaintyDD
open scoped BoundedContinuousFunction

variable {U f U' f' : ℝ → ℝ} {β : ℝ}

/-- **`g(a) ≥ a` below the steady state**: for `0 < a ≤ k*` the optimal path from `a` rises
(Proposition 6.1), so `g(a) ≥ a`. -/
theorem gc_policy_ge_of_le_kstar {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)]
    {v : Icc (0 : ℝ) kbar →ᵇ ℝ} (S : Setting61 U f U' f' β kbar v) {kstar : ℝ} (hks0 : 0 < kstar)
    (hks : f' kstar = 1 / β) {a : ℝ} (ha : 0 < a) (hak : a ≤ kstar) :
    a ≤ gpol U f β kbar v a := by
  obtain ⟨hlt, hfix, hpath⟩ := prop_6_1 S hks0 hks
  rcases eq_or_lt_of_le hak with heq | hlt'
  · rw [heq, ((hfix kstar ⟨hks0.le, hlt.le⟩).2 (Or.inr rfl))]
  obtain ⟨hmono, hconv⟩ := hpath a ha (hlt'.le.trans hlt.le)
  rcases hmono with hm | ha'
  · have := hm (Nat.zero_le 1)
    simpa using this
  · exfalso
    have : kstar ≤ a := le_of_tendsto' hconv fun t => by
      have := ha' (Nat.zero_le t)
      simpa using this
    linarith

/-- **The policy of (3) has the properties used in Ex 16.1(e)–(g)** on `K = [a, k̄]`,
`0 < a ≤ k*`: `g` is continuous and maps `K` into itself, consumption `c = f − g` is positive, and
the Euler equation `U′(c(k)) = β f′(g(k)) U′(c(g(k)))` holds. -/
theorem gc_planner_of_bellman {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)]
    {v : Icc (0 : ℝ) kbar →ᵇ ℝ} (S : Setting61 U f U' f' β kbar v)
    (hUb : ∃ B, ∀ x, 0 ≤ x → |U x| ≤ B) {kstar : ℝ} (hks0 : 0 < kstar) (hks : f' kstar = 1 / β)
    {a : ℝ} (ha : 0 < a) (hak : a ≤ kstar) :
    GrowthCertaintyPlanner U f (gpol U f β kbar v) (fun k => f k - gpol U f β kbar v k) U' f'
      β a kbar := by
  have hlt := (prop_6_1 S hks0 hks).1
  have hak' : a ≤ kbar := hak.trans hlt.le
  have hfmono := S.dyn.f_mono
  have hga := gc_policy_ge_of_le_kstar S hks0 hks ha hak
  exact {
    beta_pos := S.dyn.β_pos
    beta_lt_one := S.dyn.β_lt
    a_pos := ha
    a_le := hak'
    U_bdd := hUb
    U_cont := S.dyn.U_cont
    U_strictConcave := S.dyn.U_conc
    dU_deriv := S.dyn.U_deriv
    dU_pos := fun x hx => S.dyn.U'_pos hx
    dU_cont := S.dyn.U'_cont
    f_cont := S.dyn.f_cont
    f_strictConcave := S.dyn.f_conc
    f_nonneg := fun z hz => by
      have := hfmono.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hz) hz
      rwa [S.dyn.f_zero] at this
    f_le := fun z hz hzk => by
      have := hfmono.monotoneOn (mem_Ici.2 hz) (mem_Ici.2 S.kbar_pos.le) hzk
      rwa [S.kbar_fix] at this
    df_deriv := S.dyn.f_deriv
    g_cont := S.continuousOn_gpol.mono (Icc_subset_Icc ha.le le_rfl)
    g_mem := fun k hk => ⟨hga.trans ((ex_6_1b S).monotoneOn ⟨ha.le, hak'⟩
      ⟨ha.le.trans hk.1, hk.2⟩ hk.1), (S.gpol_lt_kbar (ha.trans_le hk.1) hk.2).le⟩
    c_eq := fun _ _ => rfl
    c_pos := fun k hk => sub_pos.2 (S.gpol_interior (ha.trans_le hk.1) hk.2).2
    euler := fun k hk => by
      have := S.foc (ha.trans_le hk.1) hk.2
      rw [this]
      ring }

/-- The §6.1 setting with `U` bounded and `0 < k̂ ≤ k̄` gives the restrictions of §16.1
(`GrowthCertaintyHyp`); `f(k) < k` for `k > k̄` follows from strict concavity. -/
theorem gc_hyp_of_dyn {kbar : ℝ} {v : Icc (0 : ℝ) kbar →ᵇ ℝ} (S : Setting61 U f U' f' β kbar v)
    (hUb : ∃ B, ∀ x, 0 ≤ x → |U x| ≤ B) {khat : ℝ} (hk0 : 0 < khat) :
    GrowthCertaintyHyp U f β khat kbar where
  beta_pos := S.dyn.β_pos
  beta_lt_one := S.dyn.β_lt
  U_bdd := hUb
  U_cont := S.dyn.U_cont
  U_strictMono := S.dyn.U_mono
  U_strictConcave := S.dyn.U_conc
  f_cont := S.dyn.f_cont
  f_strictMono := S.dyn.f_mono
  f_strictConcave := S.dyn.f_conc
  f_zero := S.dyn.f_zero
  khat_pos := hk0
  kbar_pos := S.kbar_pos
  f_kbar := S.kbar_fix
  f_lt_self := fun k hk => by
    have hk0' : 0 < k := S.kbar_pos.trans hk
    have hb0 : 0 < kbar / k := div_pos S.kbar_pos hk0'
    have hb1 : kbar / k < 1 := (div_lt_one hk0').2 hk
    have := S.dyn.f_conc.2 (mem_Ici.2 le_rfl) (mem_Ici.2 hk0'.le) hk0'.ne (sub_pos.2 hb1) hb0
      (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hk0'.ne'] at this
    rw [S.dyn.f_zero, mul_zero, zero_add, S.kbar_fix] at this
    by_contra hge
    push Not at hge
    have : kbar / k * k ≤ kbar / k * f k := mul_le_mul_of_nonneg_left hge hb0.le
    rw [div_mul_cancel₀ _ hk0'.ne'] at this
    linarith

/-- **Exercise 16.1(e)–(g), with `g` the policy of the Bellman equation (3)**. In the §6.1 setting
with `U` bounded and `0 < k̂ ≤ k̄`, on `K = [a, k̄]` with `a = min {k̂, k*}`: `g` has the properties
`GrowthCertaintyPlanner`; the firm's and household's equations (1)–(2) (with the corrected price
(4)) have solutions `ψ`, `Ω`, and `(g, q, ψ, h, Ω, ω)` is a recursive competitive equilibrium
((R1)–(R4)); from `z₀ = k̂`, `a₀ = ψ(k̂, k̂)` capital follows `gᵗ(k̂)` and consumption
`c(gᵗ(k̂))`; and that consumption sequence is the unique optimum `x⁰` of Exercise 16.1(a). -/
theorem ex_16_1efg {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)] {v : Icc (0 : ℝ) kbar →ᵇ ℝ}
    (S : Setting61 U f U' f' β kbar v) (hUb : ∃ B, ∀ x, 0 ≤ x → |U x| ≤ B) {khat : ℝ}
    (hk0 : 0 < khat) (hkb : khat ≤ kbar) :
    ∃ a : ℝ, ∃ H : GrowthCertaintyPlanner U f (gpol U f β kbar v)
        (fun k => f k - gpol U f β kbar v k) U' f' β a kbar, ∃ hk : khat ∈ Icc a kbar,
      (∃ (ψ : Icc a kbar × Icc (0 : ℝ) kbar →ᵇ ℝ)
        (hψ : GcFirmBellman f (gcGK H) (gcQK β U' (fun k => f k - gpol U f β kbar v k)
          (gpol U f β kbar v)) ψ) (Ω : Icc a kbar × Ici (0 : ℝ) →ᵇ ℝ)
        (hΩ : GcHouseholdBellman U (gcGK H) (gcQK β U' (fun k => f k - gpol U f β kbar v k)
          (gpol U f β kbar v)) β Ω),
        GcConcaveZ ψ ∧ GcConcaveA Ω ∧ GcRecursiveEq H ψ (gcFirmPolicy hψ) Ω (gcHhPolicy hΩ) ∧
        ∀ t, gcFirmPath H hψ ⟨khat, hk⟩ (gcKtoZ H ⟨khat, hk⟩) t = gcKPath H ⟨khat, hk⟩ t ∧
          gcHhPath H hΩ ⟨khat, hk⟩ (gcHhCand H hψ ⟨khat, hk⟩ 0) t =
            gcHhCand H hψ ⟨khat, hk⟩ t) ∧
      ∃ x₀ : BddSeq ℝ, (∀ t, x₀ t = f ((gpol U f β kbar v)^[t] khat) -
          gpol U f β kbar v ((gpol U f β kbar v)^[t] khat)) ∧ x₀ ∈ gcX ∧ x₀ ∈ gcY f khat ∧
        (∀ z ∈ gcX, z ∈ gcY f khat → gcU β U z ≤ gcU β U x₀) ∧
        ∀ x ∈ gcX, x ∈ gcY f khat →
          (∀ z ∈ gcX, z ∈ gcY f khat → gcU β U z ≤ gcU β U x) → x = x₀ := by
  obtain ⟨kstar, hks0, hks, -⟩ := exists_kstar S.dyn
  set a := min khat kstar
  have ha : 0 < a := lt_min hk0 hks0
  have H := gc_planner_of_bellman S hUb hks0 hks ha (min_le_right _ _)
  have hk : khat ∈ Icc a kbar := ⟨min_le_left _ _, hkb⟩
  refine ⟨a, H, hk, ?_, ex_16_1g_planner H (gc_hyp_of_dyn S hUb hk0) hk⟩
  obtain ⟨ψ, hψ, Ω, hΩ, hcv, hcvΩ, hR⟩ := ex_16_1f H
  exact ⟨ψ, hψ, Ω, hΩ, hcv, hcvΩ, hR, fun t =>
    ⟨(ex_16_1g H hψ hcv hΩ hcvΩ ⟨khat, hk⟩ t).1, (ex_16_1g H hψ hcv hΩ hcvΩ ⟨khat, hk⟩ t).2.1⟩⟩

/-- **Exercise 16.1(e)–(g), existence form**: in the §6.1 setting with `U` bounded there are `k̄`
and the solution `v` of (3) on `[0, k̄]` (Exercise 5.1), and for every `0 < k̂ ≤ k̄` the
conclusions of `ex_16_1efg` hold. -/
theorem ex_16_1efg_exists (h : GrowthDyn U f U' f' β) :
    ∃ kbar, ∃ v : Icc (0 : ℝ) kbar →ᵇ ℝ, Nonempty (Setting61 U f U' f' β kbar v) ∧ 0 < kbar :=
  let ⟨kbar, v, S⟩ := exists_setting61 h
  ⟨kbar, v, ⟨S⟩, S.kbar_pos⟩

end StokeyLucasPrescott.EquilibriumApplications
