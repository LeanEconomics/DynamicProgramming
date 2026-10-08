/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPsOnPospaces.MetricADP

/-!
# Nonstationary policies

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.1.4 (pp. 103–105).

A policy plan is a sequence `σ̄ = (σ_t)_{t ≥ 0}` of policies. Its lifetime value is (3.2),
`v_σ̄ = lim_n T_{σ₀} ⋯ T_{σₙ} v`, the policy operators being applied backwards from the terminal
condition `v`.

* **Assumption 3.1.1**: a complete sup-nonexpansive metric, a common contraction modulus
  `λ ∈ (0, 1)` and `sup_σ d(v, T_σ v) < ∞` for every `v`.
* **Lemma 3.1.9**: (i) the limit (3.2) exists and does not depend on `v`; (ii) each `T_σ` is
  continuous and globally stable; (iii) under semi-regularity on a nonempty `V₀`, some `v` solves
  `v = ⋁_σ T_σ v`.
* **Theorem 3.1.10**: for a regular ADP the fundamental optimality properties hold, and every
  policy plan is weakly dominated by a stationary policy.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPsOnPospaces

namespace ADP

variable {V P : Type*} [PartialOrder V] {A : ADP V P}

variable (A) in
/-- `T_{σ₀} ∘ ⋯ ∘ T_{σ_{n-1}}` for a policy plan `σs` (the identity when `n = 0`). -/
def planComp (σs : ℕ → P) : ℕ → V → V
  | 0 => id
  | n + 1 => fun v => planComp σs n (A.T (σs n) v)

theorem planComp_succ (σs : ℕ → P) (n : ℕ) (v : V) :
    A.planComp σs (n + 1) v = A.planComp σs n (A.T (σs n) v) := rfl

/-- Each `planComp σs n` is order preserving. -/
theorem planComp_mono (σs : ℕ → P) (n : ℕ) : Monotone (A.planComp σs n) := by
  induction n with
  | zero => exact monotone_id
  | succ n ih => exact fun v w h => ih (A.mono (σs n) h)

variable [MetricSpace V]

variable (A) in
/-- **Assumption 3.1.1** (p. 103), with completeness of the metric kept as a separate hypothesis:
the metric is sup-nonexpansive, every `T_σ` is a contraction of modulus `λ ∈ (0, 1)`, and
`sup_σ d(v, T_σ v) < ∞` for every `v`. -/
structure Assumption311 (lam : ℝ) : Prop where
  /-- the metric is sup-nonexpansive -/
  supNonexp : IsSupNonexpansive (dist : V → V → ℝ)
  /-- `λ > 0` -/
  pos : 0 < lam
  /-- `λ < 1` -/
  lt_one : lam < 1
  /-- common contraction modulus -/
  contr : ∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ lam * dist v w
  /-- `sup_σ d(v, T_σ v) < ∞` -/
  bdd : ∀ v, BddAbove (range fun σ => dist v (A.T σ v))

/-- `planComp σs n` is Lipschitz with constant `λⁿ`. -/
theorem Assumption311.dist_planComp {lam : ℝ} (h : A.Assumption311 lam) (σs : ℕ → P) (n : ℕ)
    (v w : V) : dist (A.planComp σs n v) (A.planComp σs n w) ≤ lam ^ n * dist v w := by
  induction n generalizing v w with
  | zero => simp [planComp]
  | succ n ih =>
    rw [planComp_succ, planComp_succ, pow_succ, mul_assoc]
    exact (ih _ _).trans (mul_le_mul_of_nonneg_left (h.contr _ v w)
      (pow_nonneg h.pos.le n))

variable [CompleteSpace V]

/-- **Lemma 3.1.9 (i)** (p. 104): for every policy plan `σs` and every `v₀`, the limit
`lim_n T_{σ₀} ⋯ T_{σₙ} v₀` exists, and every other starting point `v` gives the same limit. -/
theorem Assumption311.exists_planValue {lam : ℝ} (h : A.Assumption311 lam) (σs : ℕ → P)
    (v₀ : V) : ∃ vbar, ∀ v, Tendsto (fun n => A.planComp σs n v) atTop (𝓝 vbar) := by
  obtain ⟨b, hb⟩ := h.bdd v₀
  have hcauchy : CauchySeq fun n => A.planComp σs n v₀ := by
    refine cauchySeq_of_le_geometric lam b h.lt_one fun n => ?_
    rw [planComp_succ]
    refine (h.dist_planComp σs n _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hb ⟨σs n, rfl⟩) (pow_nonneg h.pos.le n)
  obtain ⟨vbar, hvbar⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨vbar, fun v => tendsto_iff_dist_tendsto_zero.2 ?_⟩
  have hpow : Tendsto (fun n => lam ^ n * dist v v₀) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.pos.le h.lt_one).mul_const
      (dist v v₀)
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => dist_triangle _
    (A.planComp σs n v₀) _) ?_
  simpa using (squeeze_zero (fun _ => dist_nonneg) (fun n => h.dist_planComp σs n v v₀)
    hpow).add (tendsto_iff_dist_tendsto_zero.1 hvbar)

variable (A) in
/-- The lifetime value (3.2) of a policy plan `σs` from terminal condition `v`. -/
noncomputable def planValue [Nonempty V] (σs : ℕ → P) (v : V) : V :=
  limUnder atTop fun n => A.planComp σs n v

/-- `T_{σ₀} ⋯ T_{σₙ} v → v_σ̄`. -/
theorem Assumption311.tendsto_planValue [Nonempty V] {lam : ℝ} (h : A.Assumption311 lam)
    (σs : ℕ → P) (v : V) : Tendsto (fun n => A.planComp σs n v) atTop (𝓝 (A.planValue σs v)) := by
  obtain ⟨vbar, hvbar⟩ := h.exists_planValue σs v
  exact tendsto_nhds_limUnder ⟨vbar, hvbar v⟩

/-- **Lemma 3.1.9 (i)** (p. 104): `v_σ̄` does not depend on the terminal condition. -/
theorem Assumption311.planValue_eq [Nonempty V] {lam : ℝ} (h : A.Assumption311 lam)
    (σs : ℕ → P) (v w : V) : A.planValue σs v = A.planValue σs w := by
  obtain ⟨vbar, hvbar⟩ := h.exists_planValue σs v
  exact tendsto_nhds_unique (h.tendsto_planValue σs v) (hvbar v) |>.trans
    (tendsto_nhds_unique (h.tendsto_planValue σs w) (hvbar w)).symm

/-- **Lemma 3.1.9 (ii)** (p. 104): every `T_σ` is continuous and globally stable on `V`, with
`v_σ = lim_j T_σʲ v` (3.3). -/
theorem Assumption311.continuous_globallyStable [Nonempty V] {lam : ℝ}
    (h : A.Assumption311 lam) (σ : P) : Continuous (A.T σ) ∧ GloballyStable (A.T σ) :=
  ⟨(LipschitzWith.of_dist_le_mul (K := ⟨lam, h.pos.le⟩) fun v w => h.contr σ v w).continuous,
    isGloballyStable_of_contraction ‹_› h.pos.le h.lt_one h.contr σ⟩

/-- **Lemma 3.1.9 (iii)** (p. 104): if, in addition, `(V, 𝕋)` is semi-regular on a nonempty
`V₀`, some `v` satisfies `v = ⋁_σ T_σ v`. -/
theorem Assumption311.exists_solvesBellman [OrderClosedTopology V] {lam : ℝ}
    (h : A.Assumption311 lam) {V₀ : Set V} (hsr : A.IsSemiRegular V₀) (hne : V₀.Nonempty) :
    ∃ v, A.SolvesBellman v := by
  obtain ⟨⟨-, ⟨v, -, -, hb, -⟩, -⟩, -⟩ :=
    theorem_3_1_5 h.supNonexp h.pos.le h.lt_one h.contr hsr hne
  exact ⟨v, hb⟩

/-- **Theorem 3.1.10** (p. 105): if `(V, 𝕋)` is regular and Assumption 3.1.1 holds, the
fundamental optimality properties hold, and every policy plan `σ̄` is weakly dominated by a
stationary policy: `v_σ̄ ≼ v_σ` for some `σ`. -/
theorem theorem_3_1_10 [OrderClosedTopology V] [Nonempty V] {lam : ℝ} (hr : A.Regular)
    (h : A.Assumption311 lam) :
    A.FundamentalOptimality
        (isGloballyStable_of_contraction ‹_› h.pos.le h.lt_one h.contr).wellPosed ∧
      ∀ σs : ℕ → P, ∃ σ, ∀ v, A.planValue σs v ≤
        A.vσ (isGloballyStable_of_contraction ‹_› h.pos.le h.lt_one h.contr).wellPosed σ := by
  obtain ⟨hFO, -⟩ := theorem_3_1_5 h.supNonexp h.pos.le h.lt_one h.contr
    ⟨isClosed_univ, fun v _ => hr v, mapsTo_univ _ _⟩ univ_nonempty
  refine ⟨hFO, fun σs => ?_⟩
  obtain ⟨vstar, σ, -, hσ, hvG, hb⟩ := hFO.exists_vstar
  have hfix : A.bellman vstar = vstar := (A.solvesBellman_iff hvG).1 hb
  have hle : ∀ n, A.planComp σs n vstar ≤ vstar := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [planComp_succ]
      exact (planComp_mono σs n ((A.T_le_bellman _ (hr vstar)).trans_eq hfix)).trans ih
  refine ⟨σ, fun v => ?_⟩
  rw [hσ, h.planValue_eq σs v vstar]
  exact le_of_tendsto' (h.tendsto_planValue σs vstar) hle

end ADP

end SargentStachurski.ADPsOnPospaces
