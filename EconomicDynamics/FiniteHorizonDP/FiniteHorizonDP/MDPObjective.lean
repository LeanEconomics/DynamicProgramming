/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.MDPHistories
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Total discounted expected rewards and the value function

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `Objective`),
with the namespace renamed.

Miao, §5.1, pp. 139–141: Assumptions 5.1.2–5.1.4, the objectives (5.3)–(5.4), the value
functions (5.5)–(5.6) and their characterisation, and optimal plans.

* `rew M s₀ π t sᵗ = u_t(s_t, π_t(sᵗ))`, the reward process; `measurable_rew` (it is
  measurable on `Sᵗ`, which is what makes the expectations of (5.3)–(5.4) meaningful).
* `J0T M T s₀ π` (5.3) and `J M s₀ π` (5.4), the latter the limit in `[−∞, +∞]` of the partial
  sums `partialSum`; `eq_5_3`, `eq_5_4` show they are the book's expressions.
* `Assumption512`, `Assumption513`, `Assumption514`. Under Assumption 5.1.4 the partial sums
  converge to `J` (`J_spec`), so `J(s, ·)` is well defined on `Π(s)`; with Assumption 5.1.1
  `Π(s)` is nonempty (Lemma 5.1.1), as the text claims on p. 140.
* Sufficient conditions (claims of p. 140, made precise): bounded measurable rewards give
  Assumptions 5.1.3 and 5.1.4 and `|J| ≤ B/(1 − β)` (`assumption_5_1_3_of_bounded`,
  `assumption_5_1_4_of_bounded`, `abs_J_le`); rewards bounded above (below) give the
  existence of the limit in Assumption 5.1.4, with value in `[−∞, ∞)` (`(−∞, ∞]`)
  (`tendsto_partialSum_of_bddAbove`, `tendsto_partialSum_of_bddBelow`).
* `V0` (5.5), `V` (5.6), and the characterisation by the three conditions of p. 141
  (`IsValueOf`, `isValueOf_iff`, `V0_char`, `V_char`): `V₀` is the unique function satisfying
  them. `IsOptimalPlan` is an optimal plan.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The reward at date `t` along the plan: `u_t(s_t, π_t(sᵗ))`. -/
def rew (M : MDP S A) (s₀ : S) (π : Plan S A) (t : ℕ) (h : Fin t → S) : ℝ :=
  M.u t (lastState s₀ h, π t h)

/-- The expected reward at date `t`: `∫ u_t(s_t, π_t(sᵗ)) μᵗ(s₀, dsᵗ; π)`. -/
noncomputable def expRew (M : MDP S A) (s₀ : S) (π : Plan S A) (t : ℕ) : ℝ :=
  ∫ h, rew M s₀ π t h ∂mu M s₀ π t

/-- The total discounted expected rewards over the horizon `T < ∞` (Miao (5.3), p. 140). -/
noncomputable def J0T (M : MDP S A) (T : ℕ) (s₀ : S) (π : Plan S A) : ℝ :=
  ∑ t ∈ Finset.range T, M.β ^ t * expRew M s₀ π t +
    M.β ^ T * ∫ h, M.uT (lastState s₀ h) ∂mu M s₀ π T

/-- The partial sums `u(s₀, π₀) + ∑_{t=1}^{n} βᵗ ∫ u(s_t, π_t(sᵗ)) dμᵗ`. -/
noncomputable def partialSum (M : MDP S A) (s₀ : S) (π : Plan S A) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (n + 1), M.β ^ t * expRew M s₀ π t

/-- The total discounted expected rewards over an infinite horizon (Miao (5.4), p. 140): the
limit of the partial sums in `[−∞, +∞]`. -/
noncomputable def J (M : MDP S A) (s₀ : S) (π : Plan S A) : EReal :=
  limUnder atTop fun n => (partialSum M s₀ π n : EReal)

/-- **Assumption 5.1.2** (Miao, p. 139). `β ∈ (0, 1)`. -/
def Assumption512 (M : MDP S A) : Prop := 0 < M.β ∧ M.β < 1

/-- **Assumption 5.1.3** (Miao, p. 139). `T < ∞`; the rewards `u_t` (`t < T`) and `u_T` are
measurable, and along every feasible plan each reward is integrable. -/
def Assumption513 (M : MDP S A) (T : ℕ) : Prop :=
  (∀ t < T, Measurable (M.u t)) ∧ Measurable M.uT ∧
    ∀ s₀, ∀ π ∈ feasiblePlans M T s₀,
      (∀ t < T, Integrable (rew M s₀ π t) (mu M s₀ π t)) ∧
        Integrable (fun h => M.uT (lastState s₀ h)) (mu M s₀ π T)

/-- **Assumption 5.1.4** (Miao, p. 139). `T = ∞`; the process is stationary, the rewards along
every feasible plan are integrable and the partial sums of (5.4) have a limit in `[−∞, +∞]`. -/
def Assumption514 (M : MDP S A) : Prop :=
  M.IsStationary ∧ ∀ s₀, ∀ π ∈ feasiblePlans M ⊤ s₀,
    (∀ t, Integrable (rew M s₀ π t) (mu M s₀ π t)) ∧
      ∃ L : EReal, Tendsto (fun n => (partialSum M s₀ π n : EReal)) atTop (𝓝 L)

/-- The reward process is measurable on `Sᵗ` when `u_t` and `π_t` are. -/
theorem measurable_rew (M : MDP S A) (s₀ : S) {π : Plan S A} {t : ℕ}
    (hu : Measurable (M.u t)) (hπ : Measurable (π t)) : Measurable (rew M s₀ π t) :=
  hu.comp ((measurable_lastState s₀ t).prodMk hπ)

theorem expRew_zero (M : MDP S A) (s₀ : S) (π : Plan S A) :
    expRew M s₀ π 0 = M.u 0 (s₀, π 0 Fin.elim0) := by
  rw [expRew, integral_mu_zero]
  rfl

/-- **Miao (5.3)**, p. 140. For `T ≥ 1`, `J₀ᵀ(s₀, π) = u₀(s₀, π₀) +
∑_{t=1}^{T−1} βᵗ ∫ u_t(s_t, π_t(sᵗ)) dμᵗ + βᵀ ∫ u_T(s_T) dμᵀ`. -/
theorem eq_5_3 (M : MDP S A) {T : ℕ} (hT : 1 ≤ T) (s₀ : S) (π : Plan S A) :
    J0T M T s₀ π = M.u 0 (s₀, π 0 Fin.elim0) +
      ∑ t ∈ Finset.Ico 1 T, M.β ^ t * ∫ h, M.u t (lastState s₀ h, π t h) ∂mu M s₀ π t +
        M.β ^ T * ∫ h, M.uT (lastState s₀ h) ∂mu M s₀ π T := by
  rw [J0T, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), pow_zero, one_mul,
    expRew_zero]
  rfl

/-- The partial sums of (5.4): `u(s₀, π₀) + ∑_{t=1}^{n} βᵗ ∫ u(s_t, π_t(sᵗ)) dμᵗ`. -/
theorem partialSum_eq (M : MDP S A) (s₀ : S) (π : Plan S A) (n : ℕ) :
    partialSum M s₀ π n = M.u 0 (s₀, π 0 Fin.elim0) +
      ∑ t ∈ Finset.Icc 1 n, M.β ^ t * ∫ h, M.u t (lastState s₀ h, π t h) ∂mu M s₀ π t := by
  rw [partialSum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), pow_zero,
    one_mul, expRew_zero]
  rfl

/-- **Miao (5.4)**, p. 140. If the partial sums `u(s₀, π₀) + ∑_{t=1}^{n} βᵗ ∫ u dμᵗ` tend to
`L ∈ [−∞, +∞]`, then `J(s₀, π) = L`. -/
theorem eq_5_4 (M : MDP S A) (s₀ : S) (π : Plan S A) {L : EReal}
    (h : Tendsto (fun n => ((M.u 0 (s₀, π 0 Fin.elim0) + ∑ t ∈ Finset.Icc 1 n,
      M.β ^ t * ∫ h, M.u t (lastState s₀ h, π t h) ∂mu M s₀ π t : ℝ) : EReal)) atTop (𝓝 L)) :
    J M s₀ π = L := by
  simp only [← partialSum_eq] at h
  exact h.limUnder_eq

/-- Miao, p. 140: under Assumption 5.1.4, `J(s₀, π)` is well defined: the partial sums converge
to it. -/
theorem J_spec {M : MDP S A} (h : Assumption514 M) {s₀ : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ⊤ s₀) :
    Tendsto (fun n => (partialSum M s₀ π n : EReal)) atTop (𝓝 (J M s₀ π)) := by
  obtain ⟨L, hL⟩ := (h.2 s₀ π hπ).2
  rw [J, hL.limUnder_eq]
  exact hL

/-- Miao, p. 140: Assumptions 5.1.1 and 5.1.4 make `J(s, ·)` a well-defined function on a
nonempty set `Π(s)`. -/
theorem J_welldefined {M : MDP S A} (hΓ : HasMeasurableSelection M.Γ) (h : Assumption514 M)
    (s : S) : (feasiblePlans M ⊤ s).Nonempty ∧ ∀ π ∈ feasiblePlans M ⊤ s,
      Tendsto (fun n => (partialSum M s π n : EReal)) atTop (𝓝 (J M s π)) :=
  ⟨lemma_5_1_1 M hΓ ⊤ s, fun _ hπ => J_spec h hπ⟩

/-- Rewards bounded by `B` in absolute value (all dates, and the terminal reward). -/
def BoundedRewards (M : MDP S A) (B : ℝ) : Prop :=
  (∀ t x, |M.u t x| ≤ B) ∧ ∀ s, |M.uT s| ≤ B

theorem integrable_of_bounded {t : ℕ} {μ : Measure (Fin t → S)} [IsFiniteMeasure μ]
    {f : (Fin t → S) → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ h, |f h| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall fun h => by
    simpa [Real.norm_eq_abs] using hB h)

theorem plan_lt {T : ℕ} {s₀ : S} {M : MDP S A} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M T s₀) : ∀ j < T, Measurable (π j) :=
  fun j hj => hπ.1 j (by exact_mod_cast hj)

/-- Miao, p. 140 (made precise): with Markov kernels, measurable rewards bounded by `B`
satisfy Assumption 5.1.3 for every horizon. -/
theorem assumption_5_1_3_of_bounded {M : MDP S A} (hP : M.IsMarkov) {B : ℝ}
    (hB : BoundedRewards M B) (hu : ∀ t, Measurable (M.u t)) (huT : Measurable M.uT)
    (T : ℕ) : Assumption513 M T := by
  refine ⟨fun t _ => hu t, huT, fun s₀ π hπ => ⟨fun t ht => ?_, ?_⟩⟩
  · have := isProbabilityMeasure_mu M hP s₀ (t := t) fun j hj => plan_lt hπ j (by omega)
    exact integrable_of_bounded (measurable_rew M s₀ (hu t) (plan_lt hπ t ht))
      fun h => hB.1 t _
  · have := isProbabilityMeasure_mu M hP s₀ (t := T) (plan_lt hπ)
    exact integrable_of_bounded (huT.comp (measurable_lastState s₀ T)) fun h => hB.2 _

theorem abs_expRew_le {M : MDP S A} (hP : M.IsMarkov) {B : ℝ} (s₀ : S) {π : Plan S A}
    {t : ℕ} (hB : ∀ h, |rew M s₀ π t h| ≤ B) (hπ : ∀ j < t, Measurable (π j)) :
    |expRew M s₀ π t| ≤ B := by
  have := isProbabilityMeasure_mu M hP s₀ hπ
  have h := norm_integral_le_of_norm_le_const (μ := mu M s₀ π t) (f := rew M s₀ π t) (C := B)
    (Eventually.of_forall fun h => by simpa [Real.norm_eq_abs] using hB h)
  simpa [Real.norm_eq_abs, expRew] using h

/-- Bounded rewards and `0 ≤ β < 1`: the partial sums of (5.4) converge in `ℝ` to
`∑ βᵗ ∫ u dμᵗ`. -/
theorem tendsto_partialSum_of_bounded {M : MDP S A} (hP : M.IsMarkov) {B : ℝ}
    (hβ0 : 0 ≤ M.β) (hβ1 : M.β < 1) (s₀ : S) {π : Plan S A}
    (hB : ∀ t h, |rew M s₀ π t h| ≤ B) (hπ : ∀ j, Measurable (π j)) :
    Summable (fun t => M.β ^ t * expRew M s₀ π t) ∧
      Tendsto (partialSum M s₀ π) atTop (𝓝 (∑' t, M.β ^ t * expRew M s₀ π t)) := by
  have hs : Summable (fun t => M.β ^ t * expRew M s₀ π t) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B) ?_
    intro t
    rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (abs_expRew_le hP s₀ (hB t) fun j _ => hπ j)
      (pow_nonneg hβ0 t)
  refine ⟨hs, ?_⟩
  have := hs.hasSum.tendsto_sum_nat
  exact this.comp (tendsto_add_atTop_nat 1)

/-- Miao, p. 140 (made precise): for a stationary process with Markov kernels, measurable
rewards bounded by `B` and `0 ≤ β < 1`, Assumption 5.1.4 holds. -/
theorem assumption_5_1_4_of_bounded {M : MDP S A} (hP : M.IsMarkov) (hst : M.IsStationary)
    {B : ℝ} (hB : ∀ t x, |M.u t x| ≤ B) (hu : ∀ t, Measurable (M.u t)) (hβ0 : 0 ≤ M.β)
    (hβ1 : M.β < 1) : Assumption514 M := by
  refine ⟨hst, fun s₀ π hπ => ⟨fun t => ?_, ?_⟩⟩
  · have := isProbabilityMeasure_mu M hP s₀ (t := t) fun j _ => hπ.1 j (WithTop.coe_lt_top j)
    exact integrable_of_bounded (measurable_rew M s₀ (hu t) (hπ.1 t (WithTop.coe_lt_top t)))
      fun h => by simpa [rew] using hB t _
  · exact ⟨_, (continuous_coe_real_ereal.tendsto _).comp (tendsto_partialSum_of_bounded hP
      hβ0 hβ1 s₀ (fun t h => hB t _) fun j => hπ.1 j (WithTop.coe_lt_top j)).2⟩

/-- The same with rewards bounded only on the graph of `Γ`, `|u_t(s, a)| ≤ B` for `a ∈ Γ(s)`
(the rewards that feasible plans can collect). -/
theorem assumption_5_1_4_of_boundedOn {M : MDP S A} (hP : M.IsMarkov) (hst : M.IsStationary)
    {B : ℝ} (hB : ∀ t s a, a ∈ M.Γ s → |M.u t (s, a)| ≤ B) (hu : ∀ t, Measurable (M.u t))
    (hβ0 : 0 ≤ M.β) (hβ1 : M.β < 1) : Assumption514 M := by
  refine ⟨hst, fun s₀ π hπ => ⟨fun t => ?_, ?_⟩⟩
  · have := isProbabilityMeasure_mu M hP s₀ (t := t) fun j _ => hπ.1 j (WithTop.coe_lt_top j)
    exact integrable_of_bounded (measurable_rew M s₀ (hu t) (hπ.1 t (WithTop.coe_lt_top t)))
      fun h => hB t _ _ (hπ.2 t (WithTop.coe_lt_top t) h)
  · exact ⟨_, (continuous_coe_real_ereal.tendsto _).comp (tendsto_partialSum_of_bounded hP
      hβ0 hβ1 s₀ (fun t h => hB t _ _ (hπ.2 t (WithTop.coe_lt_top t) h))
        fun j => hπ.1 j (WithTop.coe_lt_top j)).2⟩

/-- With bounded rewards, `J(s₀, π)` is finite: `J(s₀, π) = ∑ βᵗ ∫ u dμᵗ` and
`|J(s₀, π)| ≤ B/(1 − β)`. -/
theorem abs_J_le {M : MDP S A} (hP : M.IsMarkov) {B : ℝ} (hB : ∀ t x, |M.u t x| ≤ B)
    (hβ0 : 0 ≤ M.β) (hβ1 : M.β < 1) (s₀ : S) {π : Plan S A} (hπ : ∀ j, Measurable (π j)) :
    J M s₀ π = ((∑' t, M.β ^ t * expRew M s₀ π t : ℝ) : EReal) ∧
      |∑' t, M.β ^ t * expRew M s₀ π t| ≤ B / (1 - M.β) := by
  obtain ⟨hs, ht⟩ := tendsto_partialSum_of_bounded hP hβ0 hβ1 s₀ (fun t h => hB t _) hπ
  refine ⟨((continuous_coe_real_ereal.tendsto _).comp ht).limUnder_eq, ?_⟩
  have hg := hasSum_geometric_of_lt_one hβ0 hβ1
  have hgB : HasSum (fun t => M.β ^ t * B) (B / (1 - M.β)) := by
    convert hg.mul_right B using 1
    rw [div_eq_mul_inv, mul_comm]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  rw [← hgB.tsum_eq]
  refine Summable.tsum_le_tsum (fun t => ?_) hs.norm hgB.summable
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (abs_expRew_le hP s₀ (fun h => hB t _) fun j _ => hπ j)
    (pow_nonneg hβ0 t)

theorem geom_partial_tendsto {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (B : ℝ) :
    Tendsto (fun n => ((B * ∑ t ∈ Finset.range (n + 1), β ^ t : ℝ) : EReal)) atTop
      (𝓝 ((B * (1 - β)⁻¹ : ℝ) : EReal)) := by
  refine (continuous_coe_real_ereal.tendsto _).comp ?_
  refine Tendsto.const_mul B ?_
  exact (hasSum_geometric_of_lt_one hβ0 hβ1).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- Miao, p. 139, the limit in Assumption 5.1.4 exists when the rewards are **bounded above**
(the limit then lies in `[−∞, ∞)`). -/
theorem tendsto_partialSum_of_bddAbove {M : MDP S A} (hP : M.IsMarkov) {B : ℝ}
    (hB : ∀ t x, M.u t x ≤ B) (hβ0 : 0 ≤ M.β) (hβ1 : M.β < 1) (s₀ : S) {π : Plan S A}
    (hπ : ∀ j, Measurable (π j)) (hi : ∀ t, Integrable (rew M s₀ π t) (mu M s₀ π t)) :
    ∃ L : EReal, L ≠ ⊤ ∧ Tendsto (fun n => (partialSum M s₀ π n : EReal)) atTop (𝓝 L) := by
  set b : ℕ → ℝ := fun n => ∑ t ∈ Finset.range (n + 1), M.β ^ t * (expRew M s₀ π t - B)
  have hle : ∀ t, expRew M s₀ π t ≤ B := by
    intro t
    have := isProbabilityMeasure_mu M hP s₀ (t := t) fun j _ => hπ j
    have h := integral_mono (hi t) (integrable_const B) (fun h => hB t _)
    simpa [expRew] using h
  have hanti : Antitone fun n => (b n : EReal) := by
    refine antitone_nat_of_succ_le fun n => ?_
    refine EReal.coe_le_coe_iff.2 ?_
    simp only [b, Finset.sum_range_succ _ (n + 1)]
    have : M.β ^ (n + 1) * (expRew M s₀ π (n + 1) - B) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ0 _) (by linarith [hle (n + 1)])
    linarith
  have hb := tendsto_atTop_iInf hanti
  have hL : (⨅ n, (b n : EReal)) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top (b 0)) (iInf_le _ 0)
  refine ⟨(⨅ n, (b n : EReal)) + ((B * (1 - M.β)⁻¹ : ℝ) : EReal), ?_, ?_⟩
  · exact EReal.add_ne_top hL (EReal.coe_ne_top _)
  · have hc := (EReal.continuousAt_add (p := ((⨅ n, (b n : EReal)), ((B * (1 - M.β)⁻¹ : ℝ) :
      EReal))) (Or.inl hL) (Or.inr (EReal.coe_ne_top _))).tendsto.comp
        (hb.prodMk_nhds (geom_partial_tendsto hβ0 hβ1 B))
    refine hc.congr fun n => ?_
    simp only [Function.comp_apply, ← EReal.coe_add, b, partialSum, Finset.mul_sum, ←
      Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t _ => by ring

/-- Miao, p. 139, the limit in Assumption 5.1.4 exists when the rewards are **bounded below**
(the limit then lies in `(−∞, ∞]`). -/
theorem tendsto_partialSum_of_bddBelow {M : MDP S A} (hP : M.IsMarkov) {B : ℝ}
    (hB : ∀ t x, B ≤ M.u t x) (hβ0 : 0 ≤ M.β) (hβ1 : M.β < 1) (s₀ : S) {π : Plan S A}
    (hπ : ∀ j, Measurable (π j)) (hi : ∀ t, Integrable (rew M s₀ π t) (mu M s₀ π t)) :
    ∃ L : EReal, L ≠ ⊥ ∧ Tendsto (fun n => (partialSum M s₀ π n : EReal)) atTop (𝓝 L) := by
  set b : ℕ → ℝ := fun n => ∑ t ∈ Finset.range (n + 1), M.β ^ t * (expRew M s₀ π t - B)
  have hle : ∀ t, B ≤ expRew M s₀ π t := by
    intro t
    have := isProbabilityMeasure_mu M hP s₀ (t := t) fun j _ => hπ j
    have h := integral_mono (integrable_const B) (hi t) (fun h => hB t _)
    simpa [expRew] using h
  have hmono : Monotone fun n => (b n : EReal) := by
    refine monotone_nat_of_le_succ fun n => ?_
    refine EReal.coe_le_coe_iff.2 ?_
    simp only [b, Finset.sum_range_succ _ (n + 1)]
    have : 0 ≤ M.β ^ (n + 1) * (expRew M s₀ π (n + 1) - B) :=
      mul_nonneg (pow_nonneg hβ0 _) (by linarith [hle (n + 1)])
    linarith
  have hb := tendsto_atTop_iSup hmono
  have hL : (⨆ n, (b n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot (b 0))
    (le_iSup (fun n => (b n : EReal)) 0)
  refine ⟨(⨆ n, (b n : EReal)) + ((B * (1 - M.β)⁻¹ : ℝ) : EReal), ?_, ?_⟩
  · exact EReal.add_ne_bot_iff.2 ⟨hL, EReal.coe_ne_bot _⟩
  · have hc := (EReal.continuousAt_add (p := ((⨆ n, (b n : EReal)), ((B * (1 - M.β)⁻¹ : ℝ) :
      EReal))) (Or.inr (EReal.coe_ne_bot _)) (Or.inl hL)).tendsto.comp
        (hb.prodMk_nhds (geom_partial_tendsto hβ0 hβ1 B))
    refine hc.congr fun n => ?_
    simp only [Function.comp_apply, ← EReal.coe_add, b, partialSum, Finset.mul_sum, ←
      Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t _ => by ring

/-- The value function `V₀` of the `T`-horizon problem (Miao (5.5), p. 140). -/
noncomputable def V0 (M : MDP S A) (T : ℕ) (s : S) : EReal :=
  ⨆ π ∈ feasiblePlans M T s, (J0T M T s π : EReal)

/-- The value function `V` of the infinite-horizon problem (Miao (5.6), p. 140). -/
noncomputable def V (M : MDP S A) (s : S) : EReal := ⨆ π ∈ feasiblePlans M ⊤ s, J M s π

/-- The three conditions of Miao, p. 141, for `w` to be the value of the problem with objective
`j` on the feasible set `F`. -/
def IsValueOf {α : Type*} (F : Set α) (j : α → EReal) (w : EReal) : Prop :=
  ((w ≠ ⊤ ∧ w ≠ ⊥) → (∀ x ∈ F, j x ≤ w) ∧ ∀ ε : ℝ, 0 < ε → ∃ x ∈ F, w ≤ j x + ε) ∧
    (w = ⊤ → ∃ x : ℕ → α, (∀ k, x k ∈ F) ∧ Tendsto (j ∘ x) atTop (𝓝 ⊤)) ∧
      (w = ⊥ → ∀ x ∈ F, j x = ⊥)

/-- Miao, p. 141: a value `w` satisfies the three conditions if and only if it is the supremum
`sup_{x ∈ F} j(x)`. -/
theorem isValueOf_iff {α : Type*} (F : Set α) (j : α → EReal) (w : EReal) :
    IsValueOf F j w ↔ w = ⨆ x ∈ F, j x := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases eq_or_ne w ⊤ with hw | hw
    · obtain ⟨x, hxF, hx⟩ := h2 hw
      rw [hw, eq_comm, eq_top_iff]
      refine le_of_tendsto' hx fun k => ?_
      exact le_iSup₂ (f := fun x (_ : x ∈ F) => j x) (x k) (hxF k)
    rcases eq_or_ne w ⊥ with hb | hb
    · rw [hb, eq_comm, eq_bot_iff]
      exact iSup₂_le fun x hx => (h3 hb x hx).le
    obtain ⟨hle, happrox⟩ := h1 ⟨hw, hb⟩
    refine le_antisymm ?_ (iSup₂_le hle)
    lift w to ℝ using ⟨hw, hb⟩
    refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
    by_contra hzw
    push Not at hzw
    have hε : 0 < w - z := sub_pos.2 (EReal.coe_lt_coe_iff.1 hzw)
    obtain ⟨x, hxF, hx⟩ := happrox (w - z) hε
    have hjz : j x < z := lt_of_le_of_lt (le_iSup₂ (f := fun x (_ : x ∈ F) => j x) x hxF) hz
    have := EReal.add_lt_add_right_coe hjz (w - z)
    rw [← EReal.coe_add, add_sub_cancel] at this
    exact absurd hx (not_le.2 this)
  · intro hw
    refine ⟨fun hfin => ⟨fun x hx => hw ▸ le_iSup₂ (f := fun x (_ : x ∈ F) => j x) x hx,
      fun ε hε => ?_⟩, fun htop => ?_, fun hbot x hx => ?_⟩
    · lift w to ℝ using hfin
      have : ((w - ε : ℝ) : EReal) < ⨆ x ∈ F, j x := by
        rw [← hw]
        exact EReal.coe_lt_coe_iff.2 (by linarith)
      obtain ⟨x, hxF, hx⟩ := lt_biSup_iff.1 this
      refine ⟨x, hxF, ?_⟩
      induction h : j x using EReal.rec with
      | bot => rw [h] at hx; exact absurd hx (not_lt_bot)
      | top => exact le_top
      | coe r =>
        rw [h] at hx
        rw [← EReal.coe_add]
        exact EReal.coe_le_coe_iff.2 (by linarith [EReal.coe_lt_coe_iff.1 hx])
    · have hk : ∀ k : ℕ, ∃ x ∈ F, ((k : ℝ) : EReal) < j x := fun k =>
        lt_biSup_iff.1 (by rw [← hw, htop]; exact EReal.coe_lt_top _)
      choose x hxF hx using hk
      refine ⟨x, hxF, EReal.tendsto_nhds_top_iff_real.2 fun r => ?_⟩
      filter_upwards [eventually_ge_atTop (Nat.ceil r)] with k hk
      refine lt_of_le_of_lt (EReal.coe_le_coe_iff.2 ?_) (hx k)
      exact (Nat.le_ceil r).trans (by exact_mod_cast hk)
    · exact le_bot_iff.1 (hbot ▸ hw ▸ le_iSup₂ (f := fun x (_ : x ∈ F) => j x) x hx)

/-- Miao, p. 141: `V₀` is the unique function satisfying the three conditions (for the
`T`-horizon problem). -/
theorem V0_char (M : MDP S A) (T : ℕ) (W : S → EReal) :
    (∀ s, IsValueOf (feasiblePlans M T s) (fun π => (J0T M T s π : EReal)) (W s)) ↔
      W = V0 M T := by
  simp only [isValueOf_iff, funext_iff, V0]

/-- Miao, p. 141: `V` is the unique function satisfying the three conditions (for the
infinite-horizon problem). -/
theorem V_char (M : MDP S A) (W : S → EReal) :
    (∀ s, IsValueOf (feasiblePlans M ⊤ s) (fun π => J M s π) (W s)) ↔ W = V M := by
  simp only [isValueOf_iff, funext_iff, V]

/-- An **optimal plan** from `s` for the `T`-horizon problem (Miao, p. 141): a feasible plan
attaining the supremum in (5.5). -/
def IsOptimalPlan0 (M : MDP S A) (T : ℕ) (s : S) (π : Plan S A) : Prop :=
  π ∈ feasiblePlans M T s ∧ V0 M T s = J0T M T s π

/-- An **optimal plan** from `s` for the infinite-horizon problem (Miao, p. 141). -/
def IsOptimalPlan (M : MDP S A) (s : S) (π : Plan S A) : Prop :=
  π ∈ feasiblePlans M ⊤ s ∧ V M s = J M s π

/-- Miao, p. 141: if an optimal plan exists, the supremum in (5.5) is a maximum. -/
theorem IsOptimalPlan0.isGreatest {M : MDP S A} {T : ℕ} {s : S} {π : Plan S A}
    (h : IsOptimalPlan0 M T s π) :
    IsGreatest ((fun π => (J0T M T s π : EReal)) '' feasiblePlans M T s) (V0 M T s) :=
  ⟨⟨π, h.1, h.2.symm⟩, by
    rintro _ ⟨π', hπ', rfl⟩
    exact le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans M T s) => (J0T M T s π : EReal)) π' hπ'⟩

end Miao.FiniteHorizonDP
