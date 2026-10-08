/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PreludeExamples.ContractingDP
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.LinearCombination

/-!
# Finite Markov decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.2.1 (pp. 19–26).

A finite MDP has a finite state space `X`, a nonempty finite feasible set `Γ(x)` of actions, a
reward `r`, a discount factor `β ∈ [0, 1)` and transition probabilities `P(x, a, ·)` on the
feasible pairs. The action set need not be finite: only the sets `Γ(x)` are.

* **Exercise 1.2.1**: `T_σ v = r_σ + βP_σ v` (1.18) is a `β`-contraction on `ℝ^X` whose fixed
  point is `v_σ = (I − βP_σ)⁻¹r_σ = ∑ₜ (βP_σ)ᵗr_σ` (1.17); `I − βP_σ` is invertible.
* **Exercise 1.2.2**: with `r̄ ≥ |r|` on `G` and `M = r̄/(1 − β)`, each `T_σ` maps `[−M, M]` into
  itself and `|v_σ| ≤ M`, so `v* = sup_σ v_σ` is well defined.
* The Bellman operator (1.20); **Exercise 1.2.3** (it is a `β`-contraction); `v`-greedy policies
  (1.21) and **Exercise 1.2.4**.
* **Theorem 1.2.1**: `v*` is the unique solution of the Bellman equation (1.19), a policy is
  optimal iff it is `v*`-greedy, and an optimal policy exists.
* **Theorem 1.2.2**: VFI and OPI (for every `m ≥ 1`) converge to `v*` from every starting point,
  and HPI reaches an optimal policy in finitely many steps.
* **Lemma 1.2.3** and **Proposition 1.2.4**: `v*` is the unique solution of the linear program
  (1.23) for any everywhere positive weight `c`.
-/

open Filter Topology Set Function Matrix

namespace SargentStachurski.PreludeExamples

/-- A finite MDP `(Γ, r, β, P)` (§1.2.1.1). The kernel is required to be stochastic on the
feasible pairs only. -/
structure FiniteMDP (X A : Type*) [Fintype X] where
  /-- the feasible correspondence -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the reward -/
  r : X → A → ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the transition probabilities -/
  P : X → A → X → ℝ
  P_nonneg : ∀ x, ∀ a ∈ Γ x, ∀ x', 0 ≤ P x a x'
  P_sum : ∀ x, ∀ a ∈ Γ x, ∑ x', P x a x' = 1

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- The feasible policies `Σ = {σ ∈ A^X : σ(x) ∈ Γ(x)}` (1.15). -/
def Policy : Type _ := {σ : X → A // ∀ x, σ x ∈ M.Γ x}

/-- The value of action `a` at `x` given `v`: `r(x, a) + β ∑_{x'} v(x')P(x, a, x')`. -/
def Q (v : X → ℝ) (x : X) (a : A) : ℝ := M.r x a + M.β * ∑ x', v x' * M.P x a x'

/-- The policy operator (1.18): `(T_σ v)(x) = r(x, σ(x)) + β ∑_{x'} v(x')P(x, σ(x), x')`. -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := fun x => M.Q v x (σ x)

omit [Fintype X] in
/-- Every function on a finite set is bounded. -/
theorem isBdd_of_finite [Finite X] (v : X → ℝ) : IsBdd v := by
  have := Fintype.ofFinite X
  exact ⟨∑ x, |v x|, fun x =>
    Finset.single_le_sum (f := fun y => |v y|) (fun y _ => abs_nonneg _) (Finset.mem_univ x)⟩

/-- `|∑ v P − ∑ w P| ≤ c` when `|v − w| ≤ c`, for a feasible pair. -/
theorem abs_sum_sub_le {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} {c : ℝ}
    (h : ∀ y, |v y - w y| ≤ c) :
    |∑ x', v x' * M.P x a x' - ∑ x', w x' * M.P x a x'| ≤ c := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ x', (v x' * M.P x a x' - w x' * M.P x a x')|
      ≤ ∑ x', |v x' * M.P x a x' - w x' * M.P x a x'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x', c * M.P x a x' := Finset.sum_le_sum fun y _ => by
        rw [← sub_mul, abs_mul, abs_of_nonneg (M.P_nonneg x a ha y)]
        exact mul_le_mul_of_nonneg_right (h y) (M.P_nonneg x a ha y)
    _ = c := by rw [← Finset.mul_sum, M.P_sum x a ha, mul_one]

theorem Q_mono {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} (h : v ≤ w) : M.Q v x a ≤ M.Q w x a :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_right (h y) (M.P_nonneg x a ha y)) M.β_nonneg)

theorem abs_Q_sub_le {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} {c : ℝ}
    (h : ∀ y, |v y - w y| ≤ c) : |M.Q v x a - M.Q w x a| ≤ M.β * c := by
  simp only [Q, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_nonneg]
  exact mul_le_mul_of_nonneg_left (M.abs_sum_sub_le ha h) M.β_nonneg

/-- Shifting by a constant: `Q(v − c) = Qv − βc` on feasible pairs. -/
theorem Q_sub_const {x : X} {a : A} (ha : a ∈ M.Γ x) (v : X → ℝ) (c : ℝ) :
    M.Q (fun y => v y - c) x a = M.Q v x a - M.β * c := by
  simp only [Q, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, M.P_sum x a ha]
  ring

/-- A `v`-greedy action exists at every state. -/
theorem exists_greedy (v : X → ℝ) :
    ∃ σ : M.Policy, ∀ x, ∀ a ∈ M.Γ x, M.Q v x a ≤ M.Q v x (σ.1 x) := by
  choose f hf hmax using fun x => Finset.exists_max_image (M.Γ x) (M.Q v x) (M.Γ_nonempty x)
  exact ⟨⟨f, hf⟩, hmax⟩

/-- The finite MDP as a contracting dynamic program on `ℝ^X`. -/
def toDP : ContractingDP X M.Policy where
  V := univ
  T σ := M.Tσ σ.1
  β := M.β
  β_nonneg := M.β_nonneg
  β_lt_one := M.β_lt_one
  nonempty := ⟨0, trivial⟩
  bdd v _ := isBdd_of_finite v
  closed _ _ _ _ := trivial
  mapsTo _ _ _ := trivial
  mono σ _ _ _ _ h x := M.Q_mono (σ.2 x) h
  contraction σ _ _ _ _ _ h x := M.abs_Q_sub_le (σ.2 x) h
  exists_greedy v _ := by
    obtain ⟨σ, hσ⟩ := M.exists_greedy v
    exact ⟨σ, fun τ x => hσ x _ (τ.2 x)⟩

/-- `σ` is `v`-greedy in the sense of (1.21). -/
def IsGreedy (v : X → ℝ) (σ : M.Policy) : Prop := ∀ x, ∀ a ∈ M.Γ x, M.Q v x a ≤ M.Q v x (σ.1 x)

/-- **Exercise 1.2.4** (p. 22): `σ` is `v`-greedy iff `T_σ v ≥ T_τ v` for all `τ ∈ Σ`. -/
theorem isGreedy_iff (v : X → ℝ) (σ : M.Policy) :
    M.IsGreedy v σ ↔ M.toDP.IsGreedy v σ := by
  classical
  constructor
  · exact fun h τ x => h x _ (τ.2 x)
  · intro h x a ha
    let τ : M.Policy := ⟨Function.update σ.1 x a, fun y => by
      rcases eq_or_ne y x with rfl | hy
      · rw [Function.update_self]; exact ha
      · rw [Function.update_of_ne hy]; exact σ.2 y⟩
    have := h τ x
    change M.Q v x (Function.update σ.1 x a x) ≤ M.Q v x (σ.1 x) at this
    rwa [Function.update_self] at this

/-- The Bellman operator (1.20): `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑ v(x')P(x, a, x')}`. -/
theorem bellman_eq (v : X → ℝ) (x : X) :
    M.toDP.bellman v x = (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x) := by
  obtain ⟨σ, hσ⟩ := M.exists_greedy v
  refine le_antisymm (Finset.le_sup' (M.Q v x) ((M.toDP.greedy v).2 x)) ?_
  refine Finset.sup'_le _ _ fun a ha => (hσ x a ha).trans ?_
  exact M.toDP.T_le_bellman σ (mem_univ v) x

/-- **Exercise 1.2.3** (p. 22): the Bellman operator is a `β`-contraction on `(ℝ^X, d_∞)`. -/
theorem bellman_contraction : IsSupContraction univ M.toDP.bellman M.β :=
  M.toDP.bellman_contraction

/-! ### Lifetime values as matrix expressions -/

/-- `P_σ(x, x') = P(x, σ(x), x')` (1.16). -/
def Pσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.P x (σ x) x'

/-- `r_σ(x) = r(x, σ(x))` (1.16). -/
def rσ (σ : X → A) : X → ℝ := fun x => M.r x (σ x)

theorem Tσ_eq_mulVec (σ : X → A) (v : X → ℝ) : M.Tσ σ v = M.rσ σ + (M.β • M.Pσ σ) *ᵥ v := by
  funext x
  simp only [Tσ, Q, rσ, Pσ, Pi.add_apply, smul_mulVec, Pi.smul_apply, smul_eq_mul, mulVec,
    dotProduct, Matrix.of_apply]
  congr 2
  exact Finset.sum_congr rfl fun y _ => mul_comm _ _

/-- `|P_σ w| ≤ c` when `|w| ≤ c`. -/
theorem abs_Pσ_mulVec_le (σ : M.Policy) {w : X → ℝ} {c : ℝ} (h : ∀ y, |w y| ≤ c) (x : X) :
    |(M.Pσ σ.1 *ᵥ w) x| ≤ c := by
  have := M.abs_sum_sub_le (σ.2 x) (v := w) (w := 0) (c := c) (by simpa using h)
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] at this
  simpa [Pσ, mulVec, dotProduct, mul_comm] using this

/-- **Exercise 1.2.1** (p. 21), (1.17): `I − βP_σ` is invertible and `v_σ = (I − βP_σ)⁻¹r_σ`. -/
theorem vσ_eq_inv [DecidableEq X] (σ : M.Policy) :
    IsUnit (1 - M.β • M.Pσ σ.1) ∧ M.toDP.vσ σ = (1 - M.β • M.Pσ σ.1)⁻¹ *ᵥ M.rσ σ.1 := by
  set B := M.β • M.Pσ σ.1
  -- `z = Bz` forces `z = 0`
  have hzero : ∀ z : X → ℝ, z = B *ᵥ z → z = 0 := by
    intro z hz
    have hc : IsSupContraction (univ : Set (X → ℝ)) (fun v => B *ᵥ v) M.β := by
      intro v _ w _ c h x
      have e : (B *ᵥ v) x - (B *ᵥ w) x = M.β * (M.Pσ σ.1 *ᵥ (v - w)) x := by
        simp only [B, smul_mulVec, mulVec_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      change |(B *ᵥ v) x - (B *ᵥ w) x| ≤ M.β * c
      rw [e, abs_mul, abs_of_nonneg M.β_nonneg]
      exact mul_le_mul_of_nonneg_left
        (M.abs_Pσ_mulVec_le σ (fun y => by simpa using h y) x) M.β_nonneg
    exact hc.eq_of_isFixedPt M.β_nonneg M.β_lt_one (mem_univ z) (mem_univ 0)
      (isBdd_of_finite z) (isBdd_of_finite 0) hz.symm (by simp)
  have hunit : IsUnit (1 - B) := by
    rw [← mulVec_injective_iff_isUnit]
    intro u w huw
    have : u - w = B *ᵥ (u - w) := by
      have h2 : (1 - B) *ᵥ (u - w) = 0 := by rw [mulVec_sub, huw, sub_self]
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at h2
      exact h2
    exact sub_eq_zero.1 (hzero _ this)
  refine ⟨hunit, ?_⟩
  have hfix : M.toDP.vσ σ = M.rσ σ.1 + B *ᵥ M.toDP.vσ σ := by
    conv_lhs => rw [← M.toDP.T_vσ σ]
    exact M.Tσ_eq_mulVec σ.1 _
  have h1 : (1 - B) *ᵥ M.toDP.vσ σ = M.rσ σ.1 := by
    rw [sub_mulVec, one_mulVec]
    nth_rewrite 1 [hfix]
    abel
  rw [← h1, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hunit), one_mulVec]

/-- (1.17) (p. 21): `v_σ = ∑ₜ (βP_σ)ᵗr_σ`. -/
theorem vσ_hasSum [DecidableEq X] (σ : M.Policy) (x : X) :
    HasSum (fun t => ((M.β • M.Pσ σ.1) ^ t *ᵥ M.rσ σ.1) x) (M.toDP.vσ σ x) := by
  set B := M.β • M.Pσ σ.1
  obtain ⟨R, hR⟩ := isBdd_of_finite (M.rσ σ.1)
  have hbound : ∀ t y, |(B ^ t *ᵥ M.rσ σ.1) y| ≤ M.β ^ t * R := by
    intro t
    induction t with
    | zero => simpa using hR
    | succ t ih =>
      intro y
      rw [pow_succ', ← mulVec_mulVec, smul_mulVec, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg M.β_nonneg, pow_succ, mul_comm (M.β ^ t) M.β, mul_assoc]
      exact mul_le_mul_of_nonneg_left (M.abs_Pσ_mulVec_le σ ih y) M.β_nonneg
  have hsum : Summable fun t => (B ^ t *ᵥ M.rσ σ.1) x :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one M.β_nonneg M.β_lt_one).mul_right R)
      fun t => by rw [Real.norm_eq_abs]; exact hbound t x
  -- the partial sums are the iterates of `T_σ` from `0`
  have hiter : ∀ n, (M.toDP.T σ)^[n] 0 = ∑ t ∈ Finset.range n, B ^ t *ᵥ M.rσ σ.1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply', ih]
      change M.Tσ σ.1 _ = _
      rw [M.Tσ_eq_mulVec, mulVec_sum, Finset.sum_range_succ', pow_zero, one_mulVec, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun t _ => by rw [mulVec_mulVec, pow_succ']
  have hlim := (M.toDP.tendsto_vσ σ (mem_univ 0)).tendsto_at x
  simp only [hiter, Finset.sum_apply] at hlim
  exact (tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim) ▸ hsum.hasSum

/-- **Exercise 1.2.2** (p. 21): if `|r| ≤ r̄` on `G` and `M = r̄/(1 − β)`, then (i) every `T_σ`
maps `[−M, M]` into itself and (ii) `|v_σ| ≤ M`. -/
theorem abs_vσ_le {rbar : ℝ} (hr : ∀ x, ∀ a ∈ M.Γ x, |M.r x a| ≤ rbar) :
    (∀ σ : M.Policy, ∀ v : X → ℝ, (∀ x, |v x| ≤ rbar / (1 - M.β)) →
      ∀ x, |M.Tσ σ.1 v x| ≤ rbar / (1 - M.β)) ∧
      ∀ σ x, |M.toDP.vσ σ x| ≤ rbar / (1 - M.β) := by
  have h1β : 0 < 1 - M.β := sub_pos.2 M.β_lt_one
  have hK : rbar + M.β * (rbar / (1 - M.β)) = rbar / (1 - M.β) := by
    have : rbar / (1 - M.β) * (1 - M.β) = rbar := div_mul_cancel₀ _ h1β.ne'
    linear_combination -this
  have hself : ∀ σ : M.Policy, ∀ v : X → ℝ, (∀ x, |v x| ≤ rbar / (1 - M.β)) →
      ∀ x, |M.Tσ σ.1 v x| ≤ rbar / (1 - M.β) := by
    intro σ v hv x
    have hP := M.abs_Pσ_mulVec_le σ hv x
    simp only [Pσ, mulVec, dotProduct, Matrix.of_apply] at hP
    simp only [Tσ, Q]
    calc |M.r x (σ.1 x) + M.β * ∑ x', v x' * M.P x (σ.1 x) x'|
        ≤ |M.r x (σ.1 x)| + M.β * |∑ x', v x' * M.P x (σ.1 x) x'| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg M.β_nonneg]
      _ ≤ rbar + M.β * (rbar / (1 - M.β)) := by
          refine add_le_add (hr x _ (σ.2 x)) (mul_le_mul_of_nonneg_left ?_ M.β_nonneg)
          simpa only [mul_comm] using hP
      _ = rbar / (1 - M.β) := hK
  refine ⟨hself, fun σ x => ?_⟩
  -- the iterates from `0` stay in `[−M, M]`, and so does their limit `v_σ`
  have hrbar : 0 ≤ rbar / (1 - M.β) := by
    have hr0 : 0 ≤ rbar := (abs_nonneg _).trans (hr x _ (σ.2 x))
    positivity
  have hit : ∀ n y, |(M.toDP.T σ)^[n] 0 y| ≤ rbar / (1 - M.β) := by
    intro n
    induction n with
    | zero => intro y; simpa using hrbar
    | succ n ih => intro y; rw [iterate_succ_apply']; exact hself σ _ ih y
  exact le_of_tendsto' (((M.toDP.tendsto_vσ σ (mem_univ 0)).tendsto_at x).abs) fun n => hit n x

/-! ### Optimality and algorithms -/

/-- `Σ` is finite: each `Γ(x)` is. -/
theorem finite_policy : Finite M.Policy := by
  classical
  refine Finite.of_injective (fun σ : M.Policy => fun x => (⟨σ.1 x, σ.2 x⟩ : M.Γ x)) ?_
  intro σ τ h
  apply Subtype.ext
  funext x
  have := congrFun h x
  simpa using congrArg Subtype.val this

/-- **Theorem 1.2.1** (p. 22): the value function `v*` is the unique solution in `ℝ^X` of the
Bellman equation (1.19), a policy is optimal iff it is `v*`-greedy (1.21), and an optimal policy
exists. -/
theorem theorem_1_2_1 :
    (∀ x, M.toDP.vstar x = ⨆ σ, M.toDP.vσ σ x) ∧
      (∀ x, M.toDP.vstar x = (M.Γ x).sup' (M.Γ_nonempty x) (M.Q M.toDP.vstar x)) ∧
      (∀ v : X → ℝ, (∀ x, v x = (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x)) → v = M.toDP.vstar) ∧
      (∀ σ, M.toDP.IsOptimal σ ↔ M.IsGreedy M.toDP.vstar σ) ∧ ∃ σ, M.toDP.IsOptimal σ := by
  obtain ⟨-, hsup, hfix, hopt, hex, -⟩ := M.toDP.optimality
  refine ⟨hsup, fun x => ?_, fun v hv => (hfix v (mem_univ v)).1 (funext fun x => ?_),
    fun σ => (hopt σ).trans (M.isGreedy_iff _ σ).symm, hex⟩
  · rw [← M.bellman_eq, M.toDP.bellman_vstar]
  · rw [M.bellman_eq]; exact (hv x).symm

/-- **Theorem 1.2.2** (p. 24): VFI converges, OPI converges for every `m ≥ 1`, from every
starting point, and HPI reaches an optimal policy in finitely many steps. -/
theorem theorem_1_2_2 :
    (∀ v, TendstoUniformly (fun n => M.toDP.bellman^[n] v) M.toDP.vstar atTop) ∧
      (∀ m, 1 ≤ m → ∀ v, TendstoUniformly (M.toDP.opi m v) M.toDP.vstar atTop) ∧
      ∀ σ₀, ∃ k, ∀ j, k ≤ j → M.toDP.vσ (M.toDP.hpiPolicy σ₀ j) = M.toDP.vstar ∧
        M.toDP.IsOptimal (M.toDP.hpiPolicy σ₀ j) := by
  have := M.finite_policy
  refine ⟨fun v => M.toDP.tendsto_bellman_iterate (mem_univ v), fun m hm v => ?_,
    M.toDP.hpi_terminates⟩
  refine M.toDP.tendsto_opi hm (fun σ v _ c => ?_) (fun _ _ _ => trivial) (mem_univ v)
  funext x
  exact M.Q_sub_const (σ.2 x) v c

/-- **Lemma 1.2.3** (p. 25): if `Tv ≤ v` then `v* ≤ v`. -/
theorem vstar_le {v : X → ℝ} (h : ∀ x, (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x) ≤ v x) :
    M.toDP.vstar ≤ v :=
  M.toDP.vstar_le_of_bellman_le (mem_univ v) fun x => (M.bellman_eq v x).trans_le (h x)

/-- The constraint set of the linear program (1.23). -/
def IsLPFeasible (v : X → ℝ) : Prop := ∀ x, ∀ a ∈ M.Γ x, M.Q v x a ≤ v x

/-- **Proposition 1.2.4** (p. 25): for any everywhere positive `c`, the value function `v*` is
the unique solution of the linear program `min ⟨c, v⟩` subject to
`r(x, a) + β ∑ v(x')P(x, a, x') ≤ v(x)` for all `(x, a) ∈ G` (1.23). -/
theorem lp_solution {c : X → ℝ} (hc : ∀ x, 0 < c x) :
    IsLeast {s | ∃ v, M.IsLPFeasible v ∧ s = ∑ x, c x * v x} (∑ x, c x * M.toDP.vstar x) ∧
      ∀ v, M.IsLPFeasible v → ∑ x, c x * v x ≤ ∑ x, c x * M.toDP.vstar x → v = M.toDP.vstar := by
  have hfeas : M.IsLPFeasible M.toDP.vstar := fun x a ha => by
    rw [← congrFun M.toDP.bellman_vstar x, M.bellman_eq]
    exact Finset.le_sup' (M.Q M.toDP.vstar x) ha
  have hge : ∀ v, M.IsLPFeasible v → M.toDP.vstar ≤ v := fun v hv =>
    M.vstar_le fun x => Finset.sup'_le _ _ fun a ha => hv x a ha
  refine ⟨⟨⟨_, hfeas, rfl⟩, ?_⟩, fun v hv hle => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hge v hv x) (hc x).le
  · have hvs := hge v hv
    have hsum : ∑ x, c x * (v x - M.toDP.vstar x) = 0 := by
      have h0 : 0 ≤ ∑ x, c x * (v x - M.toDP.vstar x) :=
        Finset.sum_nonneg fun x _ => mul_nonneg (hc x).le (sub_nonneg.2 (hvs x))
      have : ∑ x, c x * (v x - M.toDP.vstar x) = ∑ x, c x * v x - ∑ x, c x * M.toDP.vstar x := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
      mul_nonneg (hc x).le (sub_nonneg.2 (hvs x))).1 hsum
    funext x
    have := hterm x (Finset.mem_univ x)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hc x).ne'
    · linarith

end FiniteMDP

end SargentStachurski.PreludeExamples
