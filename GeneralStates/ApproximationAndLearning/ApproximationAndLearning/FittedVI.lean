/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ApproximationAndLearning.MetricADP

/-!
# Fitted value iteration and error bounds

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.1.2 (pp. 299–303).

`(V, 𝕋)` is an ADP on a partially ordered metric space. Under Assumption 9.1.1 (regular, each
`T_σ` a contraction of modulus `β`, the metric complete and sup-nonexpansive), the Bellman
operator is a contraction of modulus `β` (Lemma A.5.21) and Theorem 3.1.5 applies with
`V₀ = V`. An approximation operator `L : V → V` gives the approximate Bellman operator
`T̂ = L ∘ T`, and fitted value iteration (Algorithm 9.1) iterates `T̂`.

* `assumption_9_1_1`: the consequences of Assumption 9.1.1 listed on p. 299.
* **Lemma 9.1.2**: `T̂` is a contraction of modulus `β` when `L` is nonexpansive; FVI then
  converges to the fixed point of `T̂` and its stopping rule is eventually met.
* **Theorem 9.1.3** (9.5) and **Theorem 9.1.4** (9.10): bounds on `d(v*, v_σ)` for a policy
  `σ` greedy at the last iterate.
* **Proposition 9.1.5**: with `L` order preserving, `(L(V), 𝕋̂)` is an ADP.
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

namespace ADP

variable {V P : Type*} [PartialOrder V] [MetricSpace V]

/-- **Assumption 9.1.1** (p. 299): `(V, 𝕋)` is regular, each `T_σ` is a contraction of modulus
`β < 1`, and the metric is sup-nonexpansive (completeness is the instance `CompleteSpace V`). -/
structure Assumption911 (A : ADP V P) (β : ℝ) : Prop where
  regular : A.Regular
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  contraction : ∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ β * dist v w
  supNonexpansive : IsSupNonexpansive (dist : V → V → ℝ)

/-- A map is nonexpansive (9.4). -/
def Nonexpansive (L : V → V) : Prop := ∀ v w, dist (L v) (L w) ≤ dist v w

variable {A : ADP V P} {β : ℝ}

namespace Assumption911

variable (h : A.Assumption911 β)
include h

/-- Under Assumption 9.1.1 the Bellman operator is a contraction of modulus `β`. -/
theorem bellman_contraction (v w : V) : dist (A.bellman v) (A.bellman w) ≤ β * dist v w :=
  lemma_A_5_21 h.supNonexpansive h.β_nonneg h.contraction (h.regular v) (h.regular w)

/-- A `v`-greedy policy attains the Bellman operator: `T_σ v = Tv`. -/
theorem T_eq_bellman {v : V} {σ : P} (hσ : A.IsGreedy v σ) : A.T σ v = A.bellman v :=
  (A.isGreedy_iff (h.regular v) σ).1 hσ

/-- `d(v*, v) ≤ d(Tv, v)/(1 − β)` for the fixed point `v*` of `T`, (9.7). -/
theorem one_sub_mul_dist_fixed_le {vstar : V} (hvs : A.bellman vstar = vstar) (v : V) :
    (1 - β) * dist vstar v ≤ dist (A.bellman v) v := by
  have h1 := dist_triangle vstar (A.bellman v) v
  have h2 := h.bellman_contraction vstar v
  rw [hvs] at h2
  linarith

/-- `d(v, v_σ) ≤ d(v, Tv)/(1 − β)` for `σ` greedy at `v` and `v_σ = T_σ v_σ`. -/
theorem one_sub_mul_dist_vσ_le {v vσ : V} {σ : P} (hσ : A.IsGreedy v σ)
    (hvσ : A.T σ vσ = vσ) : (1 - β) * dist v vσ ≤ dist v (A.bellman v) := by
  have h1 := dist_triangle v (A.bellman v) vσ
  have h2 := h.contraction σ v vσ
  rw [h.T_eq_bellman hσ, hvσ] at h2
  linarith

end Assumption911

/-- Consequences of **Assumption 9.1.1** (p. 299), by Theorem 3.1.5 with `V₀ = V`: the
fundamental optimality properties hold, `T` is a contraction of modulus `β`, the value function
`v*` is the unique fixed point of `T`, and VFI, OPI and HPI converge. -/
theorem assumption_9_1_1 [CompleteSpace V] [OrderClosedTopology V] [Nonempty V]
    (h : A.Assumption911 β) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧
      (∀ v w, dist (A.bellman v) (A.bellman w) ≤ β * dist v w) ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.bellman vstar = vstar ∧
        (∀ w, A.bellman w = w → w = vstar) ∧ A.VFIGeometric univ vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar := by
  obtain ⟨hFO, vstar, -, hgeo, hconv⟩ := theorem_3_1_5 h.supNonexpansive h.β_nonneg h.β_lt_one
    h.contraction (V₀ := univ) ⟨isClosed_univ, fun v _ => h.regular v, mapsTo_univ _ _⟩
    univ_nonempty
  obtain ⟨w, hw, -, hws, huniq⟩ := hFO.2.1
  have hfix : A.bellman vstar = vstar := by
    rw [hgeo.1.unique hw]
    exact (A.solvesBellman_iff (h.regular w)).1 hws
  refine ⟨_, hFO, h.bellman_contraction, vstar, hgeo.1, hfix, fun u hu => ?_, hgeo,
    hconv h.regular⟩
  rw [hgeo.1.unique hw]
  exact huniq u (h.regular u) ((A.solvesBellman_iff (h.regular u)).2 hu)

/-- The approximate Bellman operator `T̂ = L ∘ T`. -/
noncomputable def approxBellman (A : ADP V P) (L : V → V) (v : V) : V := L (A.bellman v)

/-- **Lemma 9.1.2** (p. 300): if `L` is nonexpansive, `T̂ = L ∘ T` is a contraction of
modulus `β`. -/
theorem lemma_9_1_2 (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L) (v w : V) :
    dist (A.approxBellman L v) (A.approxBellman L w) ≤ β * dist v w :=
  (hL _ _).trans (h.bellman_contraction v w)

/-- By Lemma 9.1.2 and Banach's theorem, `T̂` has a unique fixed point `v̂` and the FVI iterates
`T̂ⁿv₀` converge to it from every `v₀` (p. 300). -/
theorem approxBellman_globallyStable [CompleteSpace V] [Nonempty V] (h : A.Assumption911 β)
    {L : V → V} (hL : Nonexpansive L) :
    ∃ vhat, A.approxBellman L vhat = vhat ∧ (∀ w, A.approxBellman L w = w → w = vhat) ∧
      ∀ v₀, Tendsto (fun n => (A.approxBellman L)^[n] v₀) atTop (𝓝 vhat) := by
  have hc : ContractingWith ⟨β, h.β_nonneg⟩ (A.approxBellman L) :=
    ⟨h.β_lt_one, LipschitzWith.of_dist_le_mul fun v w => lemma_9_1_2 h hL v w⟩
  exact ⟨hc.fixedPoint _, hc.fixedPoint_isFixedPt, fun w hw => hc.fixedPoint_unique hw,
    hc.tendsto_iterate_fixedPoint⟩

/-- The FVI step size `e_n = d(v_n, v_{n−1})` shrinks geometrically, so the stopping rule
`e_N ≤ τ` of Algorithm 9.1 is met for every tolerance `τ > 0`. -/
theorem fvi_terminates (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L) (v₀ : V)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ N, dist ((A.approxBellman L)^[N + 1] v₀) ((A.approxBellman L)^[N] v₀) ≤ τ := by
  set f := A.approxBellman L
  have hstep : ∀ n, dist (f^[n + 1] v₀) (f^[n] v₀) ≤ β ^ n * dist (f v₀) v₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : f^[n + 1 + 1] v₀ = f (f^[n + 1] v₀) := iterate_succ_apply' f (n + 1) v₀
      have e2 : f^[n + 1] v₀ = f (f^[n] v₀) := iterate_succ_apply' f n v₀
      calc dist (f^[n + 1 + 1] v₀) (f^[n + 1] v₀) = dist (f (f^[n + 1] v₀)) (f (f^[n] v₀)) := by
            rw [← e1, ← e2]
        _ ≤ β * dist (f^[n + 1] v₀) (f^[n] v₀) := lemma_9_1_2 h hL _ _
        _ ≤ β * (β ^ n * dist (f v₀) v₀) := mul_le_mul_of_nonneg_left ih h.β_nonneg
        _ = β ^ (n + 1) * dist (f v₀) v₀ := by ring
  have hlim : Tendsto (fun n => β ^ n * dist (f v₀) v₀) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.β_nonneg h.β_lt_one).mul_const
      (dist (f v₀) v₀)
  obtain ⟨N, hN⟩ := (hlim.eventually (ge_mem_nhds hτ)).exists
  exact ⟨N, (hstep N).trans hN⟩

/-- **Theorem 9.1.3** (p. 301), (9.5): let `v = L(Tu)` be an FVI iterate following `u`, with step
size `e = d(v, u)`, and let `σ` be `v`-greedy. If `L` is nonexpansive, then
`d(v*, v_σ) ≤ 2/(1 − β) · (βe + d(LTv, Tv))`. -/
theorem theorem_9_1_3 (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L)
    {vstar : V} (hvs : A.bellman vstar = vstar) {u v : V} (huv : v = A.approxBellman L u)
    {σ : P} (hσ : A.IsGreedy v σ) {vσ : V} (hvσ : A.T σ vσ = vσ) :
    dist vstar vσ ≤ 2 / (1 - β) * (β * dist v u + dist (L (A.bellman v)) (A.bellman v)) := by
  have hb := sub_pos.2 h.β_lt_one
  -- `d(Tv, v) ≤ d(Tv, LTv) + βe`
  have hTv : dist (A.bellman v) v ≤ dist (L (A.bellman v)) (A.bellman v) + β * dist v u := by
    have h1 := dist_triangle (A.bellman v) (L (A.bellman v)) v
    have h2 : dist (L (A.bellman v)) v ≤ β * dist v u := by
      have := lemma_9_1_2 h hL v u
      rw [← huv] at this
      exact this
    linarith [dist_comm (A.bellman v) (L (A.bellman v))]
  have h98 := h.one_sub_mul_dist_fixed_le hvs v
  have h99 := h.one_sub_mul_dist_vσ_le hσ hvσ
  rw [dist_comm v (A.bellman v)] at h99
  have htri := mul_le_mul_of_nonneg_left (dist_triangle vstar v vσ) hb.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hb]
  linarith

/-- **Theorem 9.1.4** (p. 301), (9.10): with `v = L(Tu)`, `e = d(v, u)` and `σ` `v`-greedy, if `L`
is nonexpansive then `d(v*, v_σ) ≤ 2/(1 − β)² · (βe + d(Lv*, v*))`. -/
theorem theorem_9_1_4 (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L)
    {vstar : V} (hvs : A.bellman vstar = vstar) {u v : V} (huv : v = A.approxBellman L u)
    {σ : P} (hσ : A.IsGreedy v σ) {vσ : V} (hvσ : A.T σ vσ = vσ) :
    dist vstar vσ ≤ 2 / (1 - β) ^ 2 * (β * dist v u + dist (L vstar) vstar) := by
  have hb := sub_pos.2 h.β_lt_one
  -- (9.11): `(1 − β) d(v*, v_σ) ≤ 2 d(v, v*)`
  have hTv : dist v (A.bellman v) ≤ (1 + β) * dist v vstar := by
    have h1 := dist_triangle v vstar (A.bellman v)
    have h2 := h.bellman_contraction vstar v
    rw [hvs, dist_comm vstar v] at h2
    linarith
  have h99 := h.one_sub_mul_dist_vσ_le hσ hvσ
  have h911 : (1 - β) * dist vstar vσ ≤ 2 * dist v vstar := by
    have htri := dist_triangle vstar v vσ
    rw [dist_comm vstar v] at htri
    nlinarith
  -- `(1 − β) d(v*, v) ≤ d(v*, Lv*) + βe`
  have hvsv : (1 - β) * dist vstar v ≤ dist (L vstar) vstar + β * dist v u := by
    have h1 := dist_triangle vstar (L vstar) v
    have h2 : dist (L vstar) v ≤ β * dist vstar u := by
      have := lemma_9_1_2 h hL vstar u
      rw [← huv, show A.approxBellman L vstar = L vstar by rw [approxBellman, hvs]] at this
      exact this
    have h3 := dist_triangle vstar v u
    rw [dist_comm vstar (L vstar)] at h1
    nlinarith [mul_le_mul_of_nonneg_left h3 h.β_nonneg]
  rw [dist_comm v vstar] at h911
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb 2)]
  nlinarith [mul_le_mul_of_nonneg_left hvsv (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Theorem 9.1.3** for the FVI iterates `v_n = T̂ⁿv₀`: if the algorithm stops at `v_{N+1}` with
step size `e = d(v_{N+1}, v_N)` and `σ` is `v_{N+1}`-greedy, (9.5) holds. -/
theorem theorem_9_1_3_fvi (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L)
    {vstar : V} (hvs : A.bellman vstar = vstar) (v₀ : V) (N : ℕ) {σ : P}
    (hσ : A.IsGreedy ((A.approxBellman L)^[N + 1] v₀) σ) {vσ : V} (hvσ : A.T σ vσ = vσ) :
    dist vstar vσ ≤ 2 / (1 - β) * (β * dist ((A.approxBellman L)^[N + 1] v₀)
      ((A.approxBellman L)^[N] v₀) + dist (L (A.bellman ((A.approxBellman L)^[N + 1] v₀)))
        (A.bellman ((A.approxBellman L)^[N + 1] v₀))) :=
  theorem_9_1_3 h hL hvs (iterate_succ_apply' _ N v₀) hσ hvσ

/-- **Theorem 9.1.4** for the FVI iterates: (9.10) at the stopping iterate `v_{N+1}`. -/
theorem theorem_9_1_4_fvi (h : A.Assumption911 β) {L : V → V} (hL : Nonexpansive L)
    {vstar : V} (hvs : A.bellman vstar = vstar) (v₀ : V) (N : ℕ) {σ : P}
    (hσ : A.IsGreedy ((A.approxBellman L)^[N + 1] v₀) σ) {vσ : V} (hvσ : A.T σ vσ = vσ) :
    dist vstar vσ ≤ 2 / (1 - β) ^ 2 * (β * dist ((A.approxBellman L)^[N + 1] v₀)
      ((A.approxBellman L)^[N] v₀) + dist (L vstar) vstar) :=
  theorem_9_1_4 h hL hvs (iterate_succ_apply' _ N v₀) hσ hvσ

/-- **Proposition 9.1.5** (p. 303): if `L` is order preserving, `(L(V), 𝕋̂)` with
`T̂_σ = L ∘ T_σ` is an ADP. (Nonexpansiveness, assumed in the book, is not needed.) -/
def approxADP (A : ADP V P) {L : V → V} (hL : Monotone L) : ADP (range L) P where
  T σ v := ⟨L (A.T σ v), mem_range_self _⟩
  mono σ _ _ hvw := hL (A.mono σ hvw)
  nonempty := A.nonempty

omit [MetricSpace V] in
theorem proposition_9_1_5 (A : ADP V P) {L : V → V} (hL : Monotone L) (σ : P) (v : range L) :
    ((A.approxADP hL).T σ v : V) = L (A.T σ v) := rfl

end ADP

end SargentStachurski.ApproximationAndLearning
