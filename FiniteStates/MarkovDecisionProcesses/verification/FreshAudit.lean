import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Chapter 5 builds on
Markov matrices (§2.3.1.3), the contraction machinery of §1.2.2, Blackwell's
condition (Lemma 2.2.4), the comparison of fixed points of ordered operators
(Proposition 2.2.7) and the estimate `|max f − max g| ≤ max |f − g|`
(Lemma 2.2.2). Each chapter project is self-contained, so these are restated
here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

variable {X : Type*} [Fintype X]

/-- A stochastic (Markov) matrix on the finite state space `X` (Vol. 1, p. 71): nonnegative with
unit row sums. -/
structure IsMarkov (P : Matrix X X ℝ) : Prop where
  nonneg : ∀ x x', 0 ≤ P x x'
  rowsum : ∀ x, ∑ x', P x x' = 1

/-- A distribution on `X` (Vol. 1, p. 31): nonnegative and summing to one. -/
structure IsDistribution (ψ : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ψ x
  sum_eq_one : ∑ x, ψ x = 1

/-- `(Ph)(x) = ∑ h(x')P(x, x')`, Vol. 1 (3.12). -/
theorem mulVec_apply_eq (P : Matrix X X ℝ) (h : X → ℝ) (x : X) :
    (P *ᵥ h) x = ∑ x', h x' * P x x' := by
  simp only [mulVec, dotProduct, mul_comm]

theorem IsMarkov.mul {P Q : Matrix X X ℝ} (hP : IsMarkov P) (hQ : IsMarkov Q) :
    IsMarkov (P * Q) where
  nonneg x x' := by
    rw [Matrix.mul_apply]
    exact sum_nonneg fun z _ => mul_nonneg (hP.nonneg x z) (hQ.nonneg z x')
  rowsum x := by
    simp only [Matrix.mul_apply]
    rw [sum_comm]
    simp only [← mul_sum, hQ.rowsum, mul_one, hP.rowsum]

/-- `Pᵏ` is Markov. -/
theorem IsMarkov.pow [DecidableEq X] {P : Matrix X X ℝ} (hP : IsMarkov P) (k : ℕ) :
    IsMarkov (P ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun x x' => ?_, fun x => ?_⟩
    · simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [pow_zero, Matrix.one_apply]
  | succ k ih => rw [pow_succ]; exact ih.mul hP

/-- A Markov matrix preserves `≤` on functions. -/
theorem IsMarkov.mulVec_le_mulVec {P : Matrix X X ℝ} (hP : IsMarkov P) {f g : X → ℝ} (hfg : f ≤ g) :
    P *ᵥ f ≤ P *ᵥ g := fun x =>
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hfg x') (hP.nonneg x x')

/-- `P𝟙 = 𝟙`: constants are fixed by a Markov matrix. -/
theorem IsMarkov.mulVec_const {P : Matrix X X ℝ} (hP : IsMarkov P) (c : ℝ) :
    P *ᵥ (fun _ => c) = fun _ => c := by
  funext x
  simp only [mulVec, dotProduct, ← sum_mul, hP.rowsum, one_mul]

/-- `|Ph(x)| ≤ ‖h‖_∞` (Vol. 1, Ex 3.2.1). -/
theorem IsMarkov.abs_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ) (x : X) :
    |(P *ᵥ h) x| ≤ ‖h‖ := by
  have hb : ∀ x', |h x'| ≤ ‖h‖ := fun x' => by
    have := norm_le_pi_norm h x'
    rwa [Real.norm_eq_abs] at this
  calc |(P *ᵥ h) x| = |∑ x', P x x' * h x'| := rfl
    _ ≤ ∑ x', |P x x' * h x'| := abs_sum_le_sum_abs _ _
    _ = ∑ x', P x x' * |h x'| := sum_congr rfl fun x' _ => by
        rw [abs_mul, abs_of_nonneg (hP.nonneg x x')]
    _ ≤ ∑ x', P x x' * ‖h‖ :=
        sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hb x') (hP.nonneg x x')
    _ = ‖h‖ := by rw [← sum_mul, hP.rowsum, one_mul]

/-- `‖Ph‖_∞ ≤ ‖h‖_∞`. -/
theorem IsMarkov.norm_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ) :
    ‖P *ᵥ h‖ ≤ ‖h‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Real.norm_eq_abs]
  exact hP.abs_mulVec_le h x

/-- `|(Pf)(x) − (Pg)(x)| ≤ ‖f − g‖_∞`. -/
theorem IsMarkov.abs_mulVec_sub_le {P : Matrix X X ℝ} (hP : IsMarkov P) (f g : X → ℝ) (x : X) :
    |(P *ᵥ f) x - (P *ᵥ g) x| ≤ ‖f - g‖ := by
  have := hP.abs_mulVec_le (f - g) x
  rwa [mulVec_sub, Pi.sub_apply] at this

/-- Global stability (Vol. 1, p. 22). -/
def GloballyStable {U : Type*} [TopologicalSpace U] (T : U → U) : Prop :=
  ∃ u' : U, IsFixedPt T u' ∧ (∀ v, IsFixedPt T v → v = u') ∧
    ∀ u, Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')

variable {E : Type*} [NormedAddCommGroup E]

/-- A contraction of modulus `L` on `U` (Vol. 1, (1.17)). -/
structure IsContractionOn (T : E → E) (U : Set E) (L : ℝ) : Prop where
  mapsTo : Set.MapsTo T U U
  nonneg : 0 ≤ L
  lt_one : L < 1
  norm_sub_le : ∀ u ∈ U, ∀ v ∈ U, ‖T u - T v‖ ≤ L * ‖u - v‖

namespace IsContractionOn

variable {T : E → E} {U : Set E} {L : ℝ}

theorem fixedPt_unique (h : IsContractionOn T U L) {u v : E} (hu : u ∈ U) (hv : v ∈ U)
    (hfu : IsFixedPt T u) (hfv : IsFixedPt T v) : u = v := by
  have hb := h.norm_sub_le u hu v hv
  rw [hfu.eq, hfv.eq] at hb
  have hnn : 0 ≤ ‖u - v‖ := norm_nonneg _
  have hpos : 0 < 1 - L := by linarith [h.lt_one]
  have : ‖u - v‖ ≤ 0 := by nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this hnn))

theorem iterate_mem (h : IsContractionOn T U L) {u : E} (hu : u ∈ U) (k : ℕ) : T^[k] u ∈ U := by
  induction k with
  | zero => simpa using hu
  | succ k ih => rw [iterate_succ_apply']; exact h.mapsTo ih

theorem norm_iterate_sub_fixedPt_le (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U)
    (hu' : u' ∈ U) (hfix : IsFixedPt T u') (k : ℕ) :
    ‖T^[k] u - u'‖ ≤ L ^ k * ‖u - u'‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply']
    calc ‖T (T^[k] u) - u'‖ = ‖T (T^[k] u) - T u'‖ := by rw [hfix.eq]
      _ ≤ L * ‖T^[k] u - u'‖ := h.norm_sub_le _ (h.iterate_mem hu k) _ hu'
      _ ≤ L * (L ^ k * ‖u - u'‖) := mul_le_mul_of_nonneg_left ih h.nonneg
      _ = L ^ (k + 1) * ‖u - u'‖ := by ring

theorem tendsto_iterate_fixedPt (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U) (hu' : u' ∈ U)
    (hfix : IsFixedPt T u') : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u') := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  refine squeeze_zero (fun _ => norm_nonneg _) (h.norm_iterate_sub_fixedPt_le hu hu' hfix) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.nonneg h.lt_one).mul_const ‖u - u'‖

/-- Banach's theorem (Vol. 1, Theorem 1.2.3), existence, from Mathlib's `ContractingWith`. -/
theorem exists_fixedPt [CompleteSpace E] (h : IsContractionOn T U L) (hU : IsClosed U)
    (hne : U.Nonempty) : ∃ u' ∈ U, IsFixedPt T u' := by
  have : CompleteSpace U := hU.completeSpace_coe
  have : Nonempty U := hne.to_subtype
  let T' : U → U := h.mapsTo.restrict T U U
  have hT' : ContractingWith ⟨L, h.nonneg⟩ T' := by
    refine ⟨by exact_mod_cast h.lt_one, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [T', Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
    exact h.norm_sub_le x x.2 y y.2
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, IsFixedPt T' u₀ := ⟨_, hT'.fixedPoint_isFixedPt⟩
  exact ⟨u₀.1, u₀.2, congrArg Subtype.val hu₀⟩

/-- A contraction on the whole of a complete space is globally stable (Vol. 1, Theorem 1.2.3). -/
theorem globallyStable_univ [CompleteSpace E] (h : IsContractionOn T Set.univ L) :
    GloballyStable T := by
  obtain ⟨u', -, hu'⟩ := h.exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩
  exact ⟨u', hu', fun v hv => h.fixedPt_unique (Set.mem_univ v) (Set.mem_univ u') hv hu',
    fun u => h.tendsto_iterate_fixedPt (Set.mem_univ u) (Set.mem_univ u') hu'⟩

end IsContractionOn

omit [Fintype X] in
/-- Vol. 1, Proposition 2.2.7, in the form used here: if `S ≤ T` pointwise, `T` is order
preserving and its iterates from any point converge to `u_T`, then every fixed point of `S` lies
below `u_T`. The ambient space is `ℝ^X` with the pointwise order. -/
theorem fixedPt_le_of_le {S T : (X → ℝ) → (X → ℝ)} (hST : ∀ v, S v ≤ T v) (hT : Monotone T)
    {uS uT : X → ℝ} (huS : IsFixedPt S uS) (hlim : Tendsto (fun k : ℕ => T^[k] uS) atTop (𝓝 uT)) :
    uS ≤ uT := by
  have hle : ∀ k : ℕ, uS ≤ T^[k] uS := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      calc uS = S uS := huS.eq.symm
        _ ≤ T uS := hST uS
        _ ≤ T (T^[k] uS) := hT ih
  intro x
  exact ge_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hle k x

omit [Fintype X] in
/-- If `u ≤ Tu`, `T` is order preserving and `Tᵏu → u*`, then `u ≤ u*`: the monotone-improvement
step behind Howard policy iteration. -/
theorem le_fixedPt_of_le_apply {T : (X → ℝ) → (X → ℝ)} (hT : Monotone T) {u u' : X → ℝ}
    (hu : u ≤ T u) (hlim : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')) : u ≤ u' := by
  have hle : ∀ k : ℕ, u ≤ T^[k] u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      exact hu.trans (hT ih)
  intro x
  exact ge_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hle k x

/-- Blackwell's condition (Vol. 1, Lemma 2.2.4) on all of `ℝ^X`: an order-preserving `T` with
`T(u + c) ≤ Tu + βc` for `c ≥ 0` is a contraction of modulus `β` in the supremum norm. -/
theorem isContractionOn_of_blackwell {T : (X → ℝ) → (X → ℝ)} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hmono : Monotone T)
    (hdisc : ∀ u : X → ℝ, ∀ c : ℝ, 0 ≤ c → T (u + fun _ : X => c) ≤ T u + fun _ : X => β * c) :
    IsContractionOn T Set.univ β := by
  refine ⟨Set.mapsTo_univ _ _, hβ0, hβ1, fun u _ v _ => ?_⟩
  have key : ∀ u v : X → ℝ, ∀ x : X, T u x - T v x ≤ β * ‖u - v‖ := by
    intro u v x
    have hle : u ≤ v + fun _ : X => ‖u - v‖ := fun y => by
      have := norm_le_pi_norm (u - v) y
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      simp only [Pi.add_apply]
      linarith [le_abs_self (u y - v y)]
    have h1 := hmono hle x
    have h2 := hdisc v ‖u - v‖ (norm_nonneg _) x
    simp only [Pi.add_apply] at h1 h2
    linarith
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ0 (norm_nonneg _))]
  intro x
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  refine ⟨key u v x, ?_⟩
  have := key v u x
  rwa [norm_sub_rev] at this

omit [Fintype X] in
/-- Vol. 1, Lemma 2.2.2: for a nonempty finite `D`, `|max f − max g| ≤ max |f − g|`. -/
theorem abs_sup'_sub_sup'_le {D : Type*} {s : Finset D} (hs : s.Nonempty) (f g : D → ℝ) :
    |s.sup' hs f - s.sup' hs g| ≤ s.sup' hs fun z => |f z - g z| := by
  have key : ∀ f g : D → ℝ, s.sup' hs f - s.sup' hs g ≤ s.sup' hs fun z => |f z - g z| := by
    intro f g
    rw [sub_le_iff_le_add]
    refine Finset.sup'_le hs f fun z hz => ?_
    calc f z = (f z - g z) + g z := by ring
      _ ≤ |f z - g z| + g z := add_le_add (le_abs_self _) le_rfl
      _ ≤ (s.sup' hs fun z => |f z - g z|) + s.sup' hs g :=
          add_le_add (Finset.le_sup' (fun z => |f z - g z|) hz) (Finset.le_sup' g hz)
  rw [abs_sub_le_iff]
  refine ⟨key f g, ?_⟩
  have := key g f
  simpa [abs_sub_comm] using this

end SargentStachurski.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov decision processes, policies and lifetime values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.1.1 and §5.1.3.1
(pp. 128–136).

An MDP is `M = (Γ, β, r, P)`: a nonempty feasible correspondence `Γ`, a
discount factor `β ∈ (0, 1)`, a reward `r` and a stochastic kernel `P` from the
feasible state–action pairs `G` to `X`. Here `r` and `P` are given on all of
`X × A`, with `P(x, a, ·)` a distribution for every `a`; off `G` their values
never enter, since maximisation is over `Γ(x)` and policies are feasible.

A feasible policy `σ` induces the Markov matrix `P_σ(x, x') = P(x, σ(x), x')`
and reward `r_σ(x) = r(x, σ(x))`; its lifetime value is
`v_σ = ∑ βᵗP_σᵗ r_σ = (I − βP_σ)⁻¹ r_σ`, (5.18), the unique fixed point of the
policy operator `T_σ v = r_σ + βP_σ v`, (5.19)–(5.20), which is an
order-preserving contraction of modulus `β` (Exercise 5.1.7). Exercise 5.1.6
bounds `v_σ`, Exercises 5.1.8–5.1.9 identify the iterates `T_σᵏ v` with
truncated discounted sums.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

/-- A Markov decision process `M = (Γ, β, r, P)` on the finite state space `X` and action space
`A` (p. 129). -/
structure MDP (X A : Type*) [Fintype X] [Fintype A] where
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  r : X → A → ℝ
  P : X → A → X → ℝ
  P_nonneg : ∀ x a x', 0 ≤ P x a x'
  P_rowsum : ∀ x a, ∑ x', P x a x' = 1

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The feasible state–action pairs `G = {(x, a) : a ∈ Γ(x)}` (p. 129). -/
def Feasible (x : X) (a : A) : Prop := a ∈ M.Γ x

/-- A feasible policy (5.16): `σ(x) ∈ Γ(x)` for all `x`. -/
abbrev IsFeasible (σ : X → A) : Prop := ∀ x, σ x ∈ M.Γ x

/-- The set `Σ` of feasible policies (5.16), as a subtype. -/
abbrev Policy := {σ : X → A // M.IsFeasible σ}

/-- A feasible policy exists: choose any feasible action in each state. -/
noncomputable def defaultPolicy : M.Policy :=
  ⟨fun x => (M.Γ_nonempty x).choose, fun x => (M.Γ_nonempty x).choose_spec⟩

theorem policy_nonempty : Nonempty M.Policy := ⟨M.defaultPolicy⟩

/-- The row `P(x, a, ·)` is a distribution. -/
theorem isDistribution_P (x : X) (a : A) : IsDistribution (M.P x a) :=
  ⟨M.P_nonneg x a, M.P_rowsum x a⟩

/-- The closed-loop transition matrix `P_σ(x, x') = P(x, σ(x), x')` (p. 134). -/
def Pσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.P x (σ x) x'

theorem Pσ_apply (σ : X → A) (x x' : X) : M.Pσ σ x x' = M.P x (σ x) x' := rfl

/-- `P_σ ∈ M(ℝ^X)` (p. 134). -/
theorem isMarkov_Pσ (σ : X → A) : IsMarkov (M.Pσ σ) :=
  ⟨fun x x' => M.P_nonneg x (σ x) x', fun x => M.P_rowsum x (σ x)⟩

/-- The reward under `σ`: `r_σ(x) = r(x, σ(x))` (p. 134). -/
def rσ (σ : X → A) : X → ℝ := fun x => M.r x (σ x)

/-- The action value `B(x, a, v) = r(x, a) + β ∑ v(x')P(x, a, x')`, the expression maximised in
the Bellman equation (5.2). -/
def B (v : X → ℝ) (x : X) (a : A) : ℝ := M.r x a + M.β * ∑ x', v x' * M.P x a x'

/-- The policy operator (5.19): `(T_σ v)(x) = r(x, σ(x)) + β ∑ v(x')P(x, σ(x), x')`. -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := fun x => M.B v x (σ x)

theorem Tσ_apply (σ : X → A) (v : X → ℝ) (x : X) :
    M.Tσ σ v x = M.r x (σ x) + M.β * ∑ x', v x' * M.P x (σ x) x' := rfl

/-- (5.20): `T_σ v = r_σ + βP_σ v`. -/
theorem Tσ_eq (σ : X → A) (v : X → ℝ) : M.Tσ σ v = M.rσ σ + M.β • (M.Pσ σ *ᵥ v) := by
  funext x
  simp only [Tσ, B, rσ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_apply_eq, Pσ_apply]

/-- Exercise 5.1.7 (i), p. 135: `T_σ` is an order-preserving self-map on `ℝ^X`. -/
theorem Tσ_monotone (σ : X → A) : Monotone (M.Tσ σ) := by
  intro v v' hvv' x
  simp only [Tσ_apply]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun x' _ => ?_) M.β_pos.le)
  exact mul_le_mul_of_nonneg_right (hvv' x') (M.P_nonneg x (σ x) x')

/-- `|(T_σ v)(x) − (T_σ v')(x)| ≤ β‖v − v'‖`. -/
theorem abs_Tσ_sub_le (σ : X → A) (v v' : X → ℝ) (x : X) :
    |M.Tσ σ v x - M.Tσ σ v' x| ≤ M.β * ‖v - v'‖ := by
  simp only [Tσ_apply]
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_pos.le]
  refine mul_le_mul_of_nonneg_left ?_ M.β_pos.le
  have := (M.isMarkov_Pσ σ).abs_mulVec_sub_le v v' x
  simp only [mulVec_apply_eq, Pσ_apply] at this
  exact this

/-- Exercise 5.1.7 (ii), p. 135: `T_σ` is a contraction of modulus `β` on `ℝ^X` under the supremum
norm. -/
theorem isContractionOn_Tσ (σ : X → A) : IsContractionOn (M.Tσ σ) Set.univ M.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := M.β_pos.le
  lt_one := M.β_lt_one
  norm_sub_le v _ v' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg M.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact M.abs_Tσ_sub_le σ v v' x

/-- The `σ`-value function `v_σ` (5.17)–(5.18), p. 134: the unique fixed point of `T_σ`. -/
noncomputable def vσ (σ : X → A) : X → ℝ :=
  Classical.choose ((M.isContractionOn_Tσ σ).exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩)

/-- Exercise 5.1.7 (iii), p. 135: `v_σ` is a fixed point of `T_σ`. -/
theorem isFixedPt_vσ (σ : X → A) : IsFixedPt (M.Tσ σ) (M.vσ σ) :=
  (Classical.choose_spec
    ((M.isContractionOn_Tσ σ).exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩)).2

/-- Exercise 5.1.7 (iii), p. 135: `v_σ` is the only fixed point of `T_σ` in `ℝ^X`. -/
theorem eq_vσ_of_isFixedPt (σ : X → A) {v : X → ℝ} (hv : IsFixedPt (M.Tσ σ) v) : v = M.vσ σ :=
  (M.isContractionOn_Tσ σ).fixedPt_unique (Set.mem_univ v) (Set.mem_univ _) hv (M.isFixedPt_vσ σ)

/-- Exercise 5.1.7 (iv), p. 135: `T_σᵏ v → v_σ` for every `v ∈ ℝ^X`. -/
theorem tendsto_iterate_Tσ (σ : X → A) (v : X → ℝ) :
    Tendsto (fun k : ℕ => (M.Tσ σ)^[k] v) atTop (𝓝 (M.vσ σ)) :=
  (M.isContractionOn_Tσ σ).tendsto_iterate_fixedPt (Set.mem_univ v) (Set.mem_univ _)
    (M.isFixedPt_vσ σ)

/-- `v_σ = r_σ + βP_σ v_σ`. -/
theorem vσ_eq (σ : X → A) : M.vσ σ = M.rσ σ + M.β • (M.Pσ σ *ᵥ M.vσ σ) := by
  rw [← Tσ_eq]
  exact (M.isFixedPt_vσ σ).eq.symm

/-- `‖βP_σ u‖ ≤ β‖u‖`. -/
theorem norm_smul_Pσ_mulVec_le (σ : X → A) (u : X → ℝ) :
    ‖M.β • (M.Pσ σ *ᵥ u)‖ ≤ M.β * ‖u‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg M.β_pos.le]
  exact mul_le_mul_of_nonneg_left ((M.isMarkov_Pσ σ).norm_mulVec_le u) M.β_pos.le

/-- `I − βP_σ` is invertible: `u = βP_σ u` forces `‖u‖ ≤ β‖u‖`. -/
theorem isUnit_one_sub_smul_Pσ [DecidableEq X] (σ : X → A) : IsUnit (1 - M.β • M.Pσ σ) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  have hd : (1 - M.β • M.Pσ σ) *ᵥ (u - v) = 0 := by
    rw [mulVec_sub]
    exact sub_eq_zero.2 huv
  rw [sub_mulVec, one_mulVec, sub_eq_zero, smul_mulVec] at hd
  have hnorm : ‖u - v‖ ≤ M.β * ‖u - v‖ := by
    calc ‖u - v‖ = ‖M.β • (M.Pσ σ *ᵥ (u - v))‖ := by rw [← hd]
      _ ≤ M.β * ‖u - v‖ := M.norm_smul_Pσ_mulVec_le σ _
  have : ‖u - v‖ ≤ 0 := by nlinarith [norm_nonneg (u - v), M.β_lt_one]
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this (norm_nonneg _)))

/-- (5.18), p. 135: `v_σ = (I − βP_σ)⁻¹ r_σ`, by Lemma 3.2.1. -/
theorem vσ_eq_inv [DecidableEq X] (σ : X → A) : M.vσ σ = (1 - M.β • M.Pσ σ)⁻¹ *ᵥ M.rσ σ := by
  have hunit := M.isUnit_one_sub_smul_Pσ σ
  have h1 : (1 - M.β • M.Pσ σ) *ᵥ M.vσ σ = M.rσ σ := by
    rw [sub_mulVec, one_mulVec, smul_mulVec, sub_eq_iff_eq_add]
    exact M.vσ_eq σ
  calc M.vσ σ = (1 - M.β • M.Pσ σ)⁻¹ *ᵥ ((1 - M.β • M.Pσ σ) *ᵥ M.vσ σ) := by
        rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
          one_mulVec]
    _ = (1 - M.β • M.Pσ σ)⁻¹ *ᵥ M.rσ σ := by rw [h1]

/-- `‖βᵗP_σᵗ u‖ ≤ βᵗ‖u‖`. -/
theorem norm_pow_smul_mulVec_le [DecidableEq X] (σ : X → A) (u : X → ℝ) (t : ℕ) :
    ‖M.β ^ t • (M.Pσ σ ^ t *ᵥ u)‖ ≤ M.β ^ t * ‖u‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg M.β_pos.le t)]
  exact mul_le_mul_of_nonneg_left (((M.isMarkov_Pσ σ).pow t).norm_mulVec_le u)
    (pow_nonneg M.β_pos.le t)

/-- (5.18): the series `∑ₜ βᵗP_σᵗ r_σ` converges. -/
theorem summable_pow_smul_mulVec [DecidableEq X] (σ : X → A) :
    Summable fun t : ℕ => M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one M.β_pos.le M.β_lt_one).mul_right
    ‖M.rσ σ‖) (M.norm_pow_smul_mulVec_le σ _)

/-- Exercise 5.1.9 (p. 136) in matrix form: `T_σᵏ v = ∑_{t<k} βᵗP_σᵗ r_σ + βᵏP_σᵏ v`, the payoff
from following `σ` for `k` periods with terminal payoff `v`, the expectations being the entries
of `P_σᵗ`. -/
theorem iterate_Tσ_eq [DecidableEq X] (σ : X → A) (v : X → ℝ) (k : ℕ) :
    (M.Tσ σ)^[k] v =
      (∑ t ∈ range k, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ)) +
        M.β ^ k • (M.Pσ σ ^ k *ᵥ v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', ih, Tσ_eq, sum_range_succ', pow_zero, one_smul, pow_zero, one_mulVec]
    have h1 : ∀ (w : X → ℝ) (t : ℕ),
        M.β • (M.Pσ σ *ᵥ (M.β ^ t • (M.Pσ σ ^ t *ᵥ w))) =
          M.β ^ (t + 1) • (M.Pσ σ ^ (t + 1) *ᵥ w) := by
      intro w t
      rw [mulVec_smul, mulVec_mulVec, smul_smul, ← pow_succ', ← pow_succ']
    rw [mulVec_add, smul_add, mulVec_sum, smul_sum]
    simp only [h1]
    abel

/-- Exercise 5.1.8 (p. 135): starting from `v ≡ 0`, `T_σᵏ 0 = ∑_{t<k} βᵗP_σᵗ r_σ`. -/
theorem iterate_Tσ_zero [DecidableEq X] (σ : X → A) (k : ℕ) :
    (M.Tσ σ)^[k] 0 = ∑ t ∈ range k, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ) := by
  rw [iterate_Tσ_eq]
  simp

/-- (5.18) as a series: `v_σ = ∑ₜ βᵗP_σᵗ r_σ`. -/
theorem vσ_eq_tsum [DecidableEq X] (σ : X → A) :
    M.vσ σ = ∑' t : ℕ, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ) := by
  have hs := M.summable_pow_smul_mulVec σ
  have hlim := hs.hasSum.tendsto_sum_nat
  have hiter : (fun k : ℕ => ∑ t ∈ range k, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ)) =
      fun k => (M.Tσ σ)^[k] 0 := funext fun k => (M.iterate_Tσ_zero σ k).symm
  rw [hiter] at hlim
  exact tendsto_nhds_unique (M.tendsto_iterate_Tσ σ 0) hlim

/-- Exercise 5.1.6 (p. 135): if `|r| ≤ R` on the feasible pairs used by `σ`, then
`−R/(1 − β) ≤ v_σ ≤ R/(1 − β)`. -/
theorem abs_vσ_le (σ : X → A) {R : ℝ} (hR : ∀ x, |M.r x (σ x)| ≤ R) (x : X) :
    |M.vσ σ x| ≤ R / (1 - M.β) := by
  have hβ : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR x)
  set C : ℝ := R / (1 - M.β) with hC
  have hCeq : R + M.β * C = C := by
    rw [hC]
    field_simp
    ring
  set S : Set (X → ℝ) := {v | ∀ y, |v y| ≤ C} with hS
  have hclosed : IsClosed S := by
    have : S = ⋂ y, {v : X → ℝ | |v y| ≤ C} := by ext; simp [hS]
    rw [this]
    exact isClosed_iInter fun y => isClosed_le (continuous_abs.comp (continuous_apply y))
      continuous_const
  have hmaps : ∀ v ∈ S, M.Tσ σ v ∈ S := by
    intro v hv y
    rw [Tσ_apply]
    calc |M.r y (σ y) + M.β * ∑ x', v x' * M.P y (σ y) x'|
        ≤ |M.r y (σ y)| + M.β * |∑ x', v x' * M.P y (σ y) x'| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg M.β_pos.le]
      _ ≤ R + M.β * C := by
          refine add_le_add (hR y) (mul_le_mul_of_nonneg_left ?_ M.β_pos.le)
          calc |∑ x', v x' * M.P y (σ y) x'| ≤ ∑ x', |v x'| * M.P y (σ y) x' := by
                refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => ?_)
                rw [abs_mul, abs_of_nonneg (M.P_nonneg y (σ y) x')]
            _ ≤ ∑ x', C * M.P y (σ y) x' := sum_le_sum fun x' _ =>
                mul_le_mul_of_nonneg_right (hv x') (M.P_nonneg y (σ y) x')
            _ = C := by rw [← mul_sum, M.P_rowsum, mul_one]
      _ = C := hCeq
  have hiter : ∀ k : ℕ, (M.Tσ σ)^[k] 0 ∈ S := by
    intro k
    induction k with
    | zero => intro y; simp only [iterate_zero, id, Pi.zero_apply, abs_zero]; positivity
    | succ k ih => rw [iterate_succ_apply']; exact hmaps _ ih
  exact hclosed.mem_of_tendsto (M.tendsto_iterate_Tσ σ 0) (Eventually.of_forall hiter) x

end MDP

end SargentStachurski.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimality: the Bellman operator, greedy policies and the algorithms

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.1.3.2–§5.1.4
(pp. 136–145).

The value function is `v* = ⋁_σ v_σ` over the finitely many feasible policies,
(5.21); `σ` is optimal if `v_σ = v*`. The Bellman operator (5.24) maximises the
action value over `Γ(x)`; a `v`-greedy policy attains that maximum, (5.22).
Exercises 5.1.10–5.1.12: the family `{T_σ v}` has least and greatest elements,
greedy policies exist and are exactly those with `T_σ v = Tv`, `T = ⋁_σ T_σ`,
and `T` is a contraction of modulus `β`. Proposition 5.1.1: `v*` is the unique
solution of the Bellman equation, `Tᵏv → v*`, Bellman's principle of
optimality holds, and an optimal policy exists (Exercise 5.1.13).

For the algorithms: Lemma 5.1.2 (`βP_σ` is a subgradient of `T` at `v` for a
`v`-greedy `σ`), the identity that makes Howard policy iteration a Newton step,
the monotone improvement step of HPI with its termination criterion, and the
observations that optimistic policy iteration with `m = 1` is VFI and that its
inner iterates converge to `v_σ` as `m → ∞`.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The Bellman operator (5.24): `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑ v(x')P(x, a, x')}`. -/
noncomputable def T (v : X → ℝ) : X → ℝ := fun x => (M.Γ x).sup' (M.Γ_nonempty x) (M.B v x)

theorem T_apply (v : X → ℝ) (x : X) :
    M.T v x = (M.Γ x).sup' (M.Γ_nonempty x) fun a => M.r x a + M.β * ∑ x', v x' * M.P x a x' := rfl

/-- `B(x, a, v) ≤ (Tv)(x)` for every feasible `a`. -/
theorem B_le_T (v : X → ℝ) {x : X} {a : A} (ha : a ∈ M.Γ x) : M.B v x a ≤ M.T v x :=
  Finset.le_sup' (M.B v x) ha

/-- `T_σ v ≤ Tv` for every feasible policy. -/
theorem Tσ_le_T (σ : M.Policy) (v : X → ℝ) : M.Tσ σ.1 v ≤ M.T v := fun x =>
  M.B_le_T v (σ.2 x)

/-- The action value is order preserving in `v`. -/
theorem B_mono {v v' : X → ℝ} (hvv' : v ≤ v') (x : X) (a : A) : M.B v x a ≤ M.B v' x a := by
  unfold B
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun x' _ => ?_) M.β_pos.le)
  exact mul_le_mul_of_nonneg_right (hvv' x') (M.P_nonneg x a x')

/-- `T` is an order-preserving self-map on `ℝ^X`. -/
theorem T_monotone : Monotone M.T := by
  intro v v' hvv' x
  exact Finset.sup'_mono_fun fun a _ => M.B_mono hvv' x a

/-- `|B(x, a, v) − B(x, a, v')| ≤ β‖v − v'‖`. -/
theorem abs_B_sub_le (v v' : X → ℝ) (x : X) (a : A) : |M.B v x a - M.B v' x a| ≤ M.β * ‖v - v'‖ :=
  M.abs_Tσ_sub_le (fun _ => a) v v' x

/-- Exercise 5.1.12 (p. 137): `T` is a contraction of modulus `β` on `ℝ^X` under the supremum
norm. -/
theorem isContractionOn_T : IsContractionOn M.T Set.univ M.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := M.β_pos.le
  lt_one := M.β_lt_one
  norm_sub_le v _ v' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg M.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs, T_apply, T_apply]
    refine (abs_sup'_sub_sup'_le _ _ _).trans (Finset.sup'_le _ _ fun a _ => ?_)
    exact M.abs_B_sub_le v v' x a

/-! ### Greedy policies (5.22) -/

/-- A `v`-greedy policy (5.22), p. 136: feasible, and `σ(x)` maximises the action value over
`Γ(x)`. -/
def IsGreedy (v : X → ℝ) (σ : X → A) : Prop :=
  M.IsFeasible σ ∧ ∀ x, ∀ a ∈ M.Γ x, M.B v x a ≤ M.B v x (σ x)

/-- A `v`-greedy policy, chosen by maximising the action value in each state. -/
noncomputable def greedy (v : X → ℝ) : X → A := fun x =>
  ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose

theorem greedy_mem (v : X → ℝ) (x : X) : M.greedy v x ∈ M.Γ x :=
  ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose_spec.1

/-- Exercise 5.1.11 (i), p. 137: a `v`-greedy policy exists. -/
theorem isGreedy_greedy (v : X → ℝ) : M.IsGreedy v (M.greedy v) :=
  ⟨M.greedy_mem v, fun x a ha =>
    ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose_spec.2 a ha⟩

/-- The greedy policy as an element of `Σ`. -/
noncomputable def greedyPolicy (v : X → ℝ) : M.Policy := ⟨M.greedy v, M.greedy_mem v⟩

/-- Exercise 5.1.11 (ii), p. 137: a feasible `σ` is `v`-greedy iff `T_σ v = Tv`. -/
theorem isGreedy_iff_Tσ_eq_T (v : X → ℝ) (σ : M.Policy) :
    M.IsGreedy v σ.1 ↔ M.Tσ σ.1 v = M.T v := by
  constructor
  · rintro ⟨-, h⟩
    funext x
    exact le_antisymm (M.B_le_T v (σ.2 x)) (Finset.sup'_le _ _ fun a ha => h x a ha)
  · intro h
    refine ⟨σ.2, fun x a ha => ?_⟩
    have := congrFun h x
    rw [Tσ] at this
    rw [this]
    exact M.B_le_T v ha

/-- For a `v`-greedy `σ`, `T_σ v = Tv`. -/
theorem Tσ_eq_T_of_isGreedy {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) : M.Tσ σ v = M.T v :=
  (M.isGreedy_iff_Tσ_eq_T v ⟨σ, hσ.1⟩).1 hσ

/-- Exercise 5.1.11 (iii), p. 137: `(Tv)(x) = max_σ (T_σ v)(x)`, i.e. `T = ⋁_σ T_σ`. -/
theorem T_apply_eq_sup' [DecidableEq X] [DecidableEq A] (v : X → ℝ) (x : X) :
    M.T v x =
      univ.sup' (univ_nonempty_iff.2 M.policy_nonempty) fun σ : M.Policy => M.Tσ σ.1 v x := by
  apply le_antisymm
  · have h := congrFun (M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy v)) x
    rw [← h]
    exact Finset.le_sup' (fun σ : M.Policy => M.Tσ σ.1 v x) (mem_univ (M.greedyPolicy v))
  · exact Finset.sup'_le _ _ fun σ _ => M.Tσ_le_T σ v x

/-- Exercise 5.1.10 (p. 136), greatest element: `Tv` is the greatest element of `{T_σ v}_σ`. -/
theorem isGreatest_T (v : X → ℝ) : IsGreatest (Set.range fun σ : M.Policy => M.Tσ σ.1 v) (M.T v) :=
  ⟨⟨M.greedyPolicy v, M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy v)⟩, by
    rintro _ ⟨σ, rfl⟩
    exact M.Tσ_le_T σ v⟩

/-- The policy that minimises the action value in each state. -/
noncomputable def antiGreedy (v : X → ℝ) : X → A := fun x =>
  ((M.Γ x).exists_min_image (M.B v x) (M.Γ_nonempty x)).choose

theorem antiGreedy_mem (v : X → ℝ) (x : X) : M.antiGreedy v x ∈ M.Γ x :=
  ((M.Γ x).exists_min_image (M.B v x) (M.Γ_nonempty x)).choose_spec.1

/-- Exercise 5.1.10 (p. 136), least element: `{T_σ v}_σ` has a least element, the value of the
policy that minimises the action value in each state. -/
theorem isLeast_Tσ_antiGreedy (v : X → ℝ) :
    IsLeast (Set.range fun σ : M.Policy => M.Tσ σ.1 v) (M.Tσ (M.antiGreedy v) v) :=
  ⟨⟨⟨M.antiGreedy v, M.antiGreedy_mem v⟩, rfl⟩, by
    rintro _ ⟨σ, rfl⟩ x
    exact ((M.Γ x).exists_min_image (M.B v x) (M.Γ_nonempty x)).choose_spec.2 _ (σ.2 x)⟩

/-! ### The value function and Proposition 5.1.1 -/

variable [DecidableEq X] [DecidableEq A]

/-- The value function (5.21), p. 136: `v*(x) = max_{σ ∈ Σ} v_σ(x)`. -/
noncomputable def vstar : X → ℝ := fun x =>
  univ.sup' (univ_nonempty_iff.2 M.policy_nonempty) fun σ : M.Policy => M.vσ σ.1 x

/-- `v_σ ≤ v*` for every feasible policy. -/
theorem vσ_le_vstar (σ : M.Policy) : M.vσ σ.1 ≤ M.vstar := fun x =>
  Finset.le_sup' (fun σ : M.Policy => M.vσ σ.1 x) (mem_univ σ)

/-- An optimal policy (p. 136): a feasible `σ` with `v_σ = v*`. -/
def IsOptimal (σ : X → A) : Prop := M.IsFeasible σ ∧ M.vσ σ = M.vstar

/-- **Proposition 5.1.1 (i)**, existence half (pp. 137–138): `v*` is a fixed point of `T`. -/
theorem isFixedPt_T_vstar : IsFixedPt M.T M.vstar := by
  obtain ⟨vbar, -, hvbar⟩ := M.isContractionOn_T.exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩
  -- `v̄ ≤ v*`: `v̄` is the value of its own greedy policy
  have h1 : vbar ≤ M.vstar := by
    have hfix : IsFixedPt (M.Tσ (M.greedy vbar)) vbar := by
      rw [IsFixedPt, M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy vbar)]
      exact hvbar
    rw [M.eq_vσ_of_isFixedPt _ hfix]
    exact M.vσ_le_vstar (M.greedyPolicy vbar)
  -- `v* ≤ v̄`: each `v_σ ≤ v̄` by Proposition 2.2.7, since `T_σ ≤ T`
  have h2 : M.vstar ≤ vbar := by
    intro x
    refine Finset.sup'_le _ _ fun σ _ => ?_
    exact fixedPt_le_of_le (M.Tσ_le_T σ) M.T_monotone (M.isFixedPt_vσ σ.1)
      (M.isContractionOn_T.tendsto_iterate_fixedPt (Set.mem_univ _) (Set.mem_univ _) hvbar) x
  have : M.vstar = vbar := le_antisymm h2 h1
  rw [this]
  exact hvbar

/-- Proposition 5.1.1 (i), uniqueness half: `v*` is the only fixed point of `T` in `ℝ^X`. -/
theorem eq_vstar_of_isFixedPt {v : X → ℝ} (hv : IsFixedPt M.T v) : v = M.vstar :=
  M.isContractionOn_T.fixedPt_unique (Set.mem_univ v) (Set.mem_univ _) hv M.isFixedPt_T_vstar

/-- The Bellman equation (5.2): `v*(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑ v*(x')P(x, a, x')}`,
with `v*` its unique solution (Proposition 5.1.1 (i)). -/
theorem bellman_equation (x : X) :
    M.vstar x = (M.Γ x).sup' (M.Γ_nonempty x) fun a =>
      M.r x a + M.β * ∑ x', M.vstar x' * M.P x a x' :=
  (congrFun M.isFixedPt_T_vstar.eq x).symm

/-- Proposition 5.1.1 (ii): `Tᵏv → v*` for all `v ∈ ℝ^X` (value function iteration, §5.1.4.1). -/
theorem tendsto_iterate_T (v : X → ℝ) : Tendsto (fun k : ℕ => M.T^[k] v) atTop (𝓝 M.vstar) :=
  M.isContractionOn_T.tendsto_iterate_fixedPt (Set.mem_univ v) (Set.mem_univ _) M.isFixedPt_T_vstar

theorem norm_iterate_T_sub_vstar_le (v : X → ℝ) (k : ℕ) :
    ‖M.T^[k] v - M.vstar‖ ≤ M.β ^ k * ‖v - M.vstar‖ :=
  M.isContractionOn_T.norm_iterate_sub_fixedPt_le (Set.mem_univ v) (Set.mem_univ _)
    M.isFixedPt_T_vstar k

omit [DecidableEq X] [DecidableEq A] in
/-- `T` is globally stable on `ℝ^X` (p. 137). -/
theorem globallyStable_T : GloballyStable M.T := M.isContractionOn_T.globallyStable_univ

/-- Optimality is `v_σ = v*` pointwise: `σ` is optimal iff it is feasible and `v_σ'(x) ≤ v_σ(x)` for
all feasible `σ'` and all `x`. -/
theorem isOptimal_iff (σ : X → A) :
    M.IsOptimal σ ↔
      M.IsFeasible σ ∧ ∀ (σ' : M.Policy) (x : X), M.vσ σ'.1 x ≤ M.vσ σ x := by
  constructor
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, fun σ' x => ?_⟩
    rw [h]
    exact M.vσ_le_vstar σ' x
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, funext fun x => le_antisymm (M.vσ_le_vstar ⟨σ, hσ⟩ x) ?_⟩
    exact Finset.sup'_le _ _ fun σ' _ => h σ' x

/-- **Proposition 5.1.1 (iii)**, Bellman's principle of optimality (p. 137), via (5.25):
`σ` is optimal iff it is `v*`-greedy. -/
theorem isOptimal_iff_isGreedy (σ : X → A) : M.IsOptimal σ ↔ M.IsGreedy M.vstar σ := by
  constructor
  · rintro ⟨hσ, h⟩
    rw [M.isGreedy_iff_Tσ_eq_T M.vstar ⟨σ, hσ⟩]
    -- `T_σ v* = T_σ v_σ = v_σ = v* = Tv*`
    rw [← h, (M.isFixedPt_vσ σ).eq, h, M.isFixedPt_T_vstar.eq]
  · intro h
    refine ⟨h.1, ?_⟩
    have hfix : IsFixedPt (M.Tσ σ) M.vstar := by
      rw [IsFixedPt, M.Tσ_eq_T_of_isGreedy h]
      exact M.isFixedPt_T_vstar
    exact (M.eq_vσ_of_isFixedPt σ hfix).symm

/-- Proposition 5.1.1 (iv), Exercise 5.1.13 (p. 139): an optimal policy exists, namely any
`v*`-greedy policy. -/
theorem isOptimal_greedy_vstar : M.IsOptimal (M.greedy M.vstar) :=
  (M.isOptimal_iff_isGreedy _).2 (M.isGreedy_greedy _)

theorem exists_isOptimal : ∃ σ : X → A, M.IsOptimal σ := ⟨_, M.isOptimal_greedy_vstar⟩

/-! ### Algorithms (§5.1.4) -/

omit [DecidableEq X] [DecidableEq A] in
/-- **Lemma 5.1.2** (p. 144): if `σ` is `v`-greedy then `βP_σ` is a subgradient of `T` at `v`:
`Tu ≥ Tv + βP_σ(u − v)` for all `u`. -/
theorem subgradient_of_isGreedy {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) (u : X → ℝ) :
    M.T v + M.β • (M.Pσ σ *ᵥ (u - v)) ≤ M.T u := by
  have h1 := M.Tσ_le_T ⟨σ, hσ.1⟩ u
  have h2 := M.Tσ_eq_T_of_isGreedy hσ
  rw [Tσ_eq] at h1 h2
  rw [← h2, mulVec_sub, smul_sub]
  intro x
  have := h1 x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  linarith

omit [DecidableEq A] in
/-- HPI as Newton's method (p. 144): for a `v`-greedy `σ`, the Newton step
`Qv = (I − βP_σ)⁻¹(Tv − βP_σ v)` equals `(I − βP_σ)⁻¹ r_σ = v_σ`, the next value in HPI. -/
theorem newton_step_eq_vσ {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) :
    (1 - M.β • M.Pσ σ)⁻¹ *ᵥ (M.T v - M.β • (M.Pσ σ *ᵥ v)) = M.vσ σ := by
  rw [← M.Tσ_eq_T_of_isGreedy hσ, Tσ_eq, add_sub_cancel_right, M.vσ_eq_inv]

omit [DecidableEq X] [DecidableEq A] in
/-- Howard policy iteration (Algorithm 5.3), the improvement step: if `σ'` is `v_σ`-greedy then
`v_σ ≤ v_σ'`, since `v_σ = T_σ v_σ ≤ Tv_σ = T_σ' v_σ` and `T_σ'ᵏ v_σ → v_σ'`. -/
theorem vσ_le_vσ_of_isGreedy {σ : X → A} (hσ : M.IsFeasible σ) {σ' : X → A}
    (hσ' : M.IsGreedy (M.vσ σ) σ') : M.vσ σ ≤ M.vσ σ' := by
  have h : M.vσ σ ≤ M.Tσ σ' (M.vσ σ) := by
    rw [M.Tσ_eq_T_of_isGreedy hσ']
    calc M.vσ σ = M.Tσ σ (M.vσ σ) := (M.isFixedPt_vσ σ).eq.symm
      _ ≤ M.T (M.vσ σ) := M.Tσ_le_T ⟨σ, hσ⟩ _
  exact le_fixedPt_of_le_apply (M.Tσ_monotone σ') h (M.tendsto_iterate_Tσ σ' _)

/-- HPI, the termination criterion (Algorithm 5.3, line 6): if `σ'` is `v_σ`-greedy and
`v_σ' = v_σ`, then `σ'` is optimal. -/
theorem isOptimal_of_hpi_fixed {σ σ' : X → A} (hσ' : M.IsGreedy (M.vσ σ) σ')
    (heq : M.vσ σ' = M.vσ σ) : M.IsOptimal σ' := by
  have hfix : IsFixedPt M.T (M.vσ σ) := by
    rw [IsFixedPt, ← M.Tσ_eq_T_of_isGreedy hσ', ← heq]
    exact (M.isFixedPt_vσ σ').eq
  refine ⟨hσ'.1, ?_⟩
  rw [heq]
  exact M.eq_vstar_of_isFixedPt hfix

omit [DecidableEq X] [DecidableEq A] in
/-- Optimistic policy iteration (Algorithm 5.4) with `m = 1` is value function iteration: for a
`v`-greedy `σ`, `T_σ v = Tv` (p. 145). -/
theorem opi_one_step_eq_vfi {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) :
    (M.Tσ σ)^[1] v = M.T v := by
  rw [iterate_one]
  exact M.Tσ_eq_T_of_isGreedy hσ

omit [DecidableEq X] [DecidableEq A] in
/-- OPI approximates HPI as `m → ∞`: `T_σᵐ v → v_σ` (p. 145). -/
theorem tendsto_opi_inner (σ : X → A) (v : X → ℝ) :
    Tendsto (fun m : ℕ => (M.Tσ σ)^[m] v) atTop (𝓝 (M.vσ σ)) :=
  M.tendsto_iterate_Tσ σ v

end MDP

end SargentStachurski.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Examples of MDPs

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.1.2 (pp. 130–134).

* The renewal problem (§5.1.2.1): action `1` resets the state to `x̄`, action `0`
  lets it move by `Q`. Exercise 5.1.1: the kernel (5.4) is stochastic; the
  renewal Bellman equation (5.3) is the MDP Bellman equation (5.2).
* Optimal inventory management (§5.1.2.2): state `{0, …, K}`, orders
  `Γ(x) = {0, …, K − x}`, IID geometric demand. The reward (5.8) and kernel
  (5.9) are infinite sums over demand; Exercise 5.1.2 gives the kernel in closed
  form and the Bellman operator takes the form (5.12). Exercise 5.1.3 (`T` is a
  `β`-contraction) is the general Exercise 5.1.12.
* Cake eating (§5.1.2.3): Exercise 5.1.4 frames (5.13) as an MDP with wealth as
  the state and next-period wealth as the action; the kernel is deterministic.
* Optimal stopping (§5.1.2.4): Exercise 5.1.5 frames job search with Markov
  wages as an MDP on `{0, 1} × W` with actions reject/accept. Its value function
  satisfies the job search Bellman equation of Vol. 1 (3.23): employed workers
  are worth `w/(1 − β)`, and `v*(0, w) = max{w/(1 − β), c + β ∑ v*(0, w')Q(w, w')}`.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

/-- The maximum over `Bool`. -/
theorem sup'_bool (f : Bool → ℝ) :
    (univ : Finset Bool).sup' univ_nonempty f = max (f true) (f false) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun a _ => ?_
    cases a
    · exact le_max_right _ _
    · exact le_max_left _ _
  · exact max_le (Finset.le_sup' f (mem_univ true)) (Finset.le_sup' f (mem_univ false))

/-- A deterministic kernel: the next state is `g(x, a)`. -/
def detKernel {X A : Type*} [DecidableEq X] (g : X → A → X) (x : X) (a : A) (x' : X) : ℝ :=
  if x' = g x a then 1 else 0

theorem detKernel_nonneg {X A : Type*} [DecidableEq X] (g : X → A → X) (x : X) (a : A) (x' : X) :
    0 ≤ detKernel g x a x' := by
  unfold detKernel
  split_ifs <;> norm_num

theorem detKernel_rowsum {X A : Type*} [Fintype X] [DecidableEq X] (g : X → A → X) (x : X)
    (a : A) : ∑ x', detKernel g x a x' = 1 := by
  simp [detKernel]

/-- `∑ v(x')·1{x' = g(x, a)} = v(g(x, a))`. -/
theorem sum_mul_detKernel {X A : Type*} [Fintype X] [DecidableEq X] (g : X → A → X) (v : X → ℝ)
    (x : X) (a : A) : ∑ x', v x' * detKernel g x a x' = v (g x a) := by
  simp [detKernel]

/-! ### The renewal problem (§5.1.2.1) -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The renewal kernel (5.4): `P(x, a, x') = a·1{x' = x̄} + (1 − a)Q(x, x')`, with `a : Bool`. -/
def renewalKernel (Q : Matrix X X ℝ) (xbar : X) (x : X) (a : Bool) (x' : X) : ℝ :=
  if a then (if x' = xbar then 1 else 0) else Q x x'

/-- Exercise 5.1.1 (p. 131): the renewal kernel is a stochastic kernel from `G` to `X`. -/
theorem renewalKernel_nonneg {Q : Matrix X X ℝ} (hQ : IsMarkov Q) (xbar x : X) (a : Bool) (x' : X) :
    0 ≤ renewalKernel Q xbar x a x' := by
  unfold renewalKernel
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact hQ.nonneg x x'

theorem renewalKernel_rowsum {Q : Matrix X X ℝ} (hQ : IsMarkov Q) (xbar x : X) (a : Bool) :
    ∑ x', renewalKernel Q xbar x a x' = 1 := by
  unfold renewalKernel
  cases a
  · simp [hQ.rowsum x]
  · simp

/-- The renewal problem as an MDP (p. 131): `A = {0, 1}` with `Γ(x) = A`, rewards `r(x, a)`. -/
noncomputable def renewal {Q : Matrix X X ℝ} (hQ : IsMarkov Q) (xbar : X) (r : X → Bool → ℝ)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : MDP X Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := r
  P := renewalKernel Q xbar
  P_nonneg := fun x a x' => renewalKernel_nonneg hQ xbar x a x'
  P_rowsum := fun x a => renewalKernel_rowsum hQ xbar x a

/-- The renewal Bellman equation (5.3), p. 130, as the MDP Bellman equation (5.2):
`v*(x) = max{r(x, 1) + βv*(x̄), r(x, 0) + β ∑ v*(x')Q(x, x')}`. -/
theorem renewal_bellman {Q : Matrix X X ℝ} (hQ : IsMarkov Q) (xbar : X) (r : X → Bool → ℝ)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (x : X) :
    (renewal hQ xbar r hβ0 hβ1).vstar x =
      max (r x true + β * (renewal hQ xbar r hβ0 hβ1).vstar xbar)
        (r x false + β * ∑ x', (renewal hQ xbar r hβ0 hβ1).vstar x' * Q x x') := by
  rw [MDP.bellman_equation]
  change (univ : Finset Bool).sup' univ_nonempty (fun a => r x a + β *
    ∑ x', (renewal hQ xbar r hβ0 hβ1).vstar x' * renewalKernel Q xbar x a x') = _
  rw [sup'_bool]
  simp [renewalKernel]

/-! ### Optimal inventory management (§5.1.2.2) -/

/-- The inventory update (5.6): `f(x, a, d) = (x − d) ∨ 0 + a`, clamped at the capacity `K` so that
the kernel is a distribution for every pair, feasible or not. -/
def inventoryNext (K x a d : ℕ) : ℕ := min ((x - d) + a) K

theorem inventoryNext_of_feasible {K x a d : ℕ} (h : a ≤ K - x) (hx : x ≤ K) :
    inventoryNext K x a d = (x - d) + a := by
  unfold inventoryNext
  omega

/-- The geometric demand distribution `φ(d) = p(1 − p)ᵈ`. -/
noncomputable def geomPmf (p : ℝ) (d : ℕ) : ℝ := p * (1 - p) ^ d

theorem geomPmf_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (d : ℕ) : 0 < geomPmf p d :=
  mul_pos hp0 (pow_pos (by linarith) d)

theorem summable_geomPmf {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : Summable (geomPmf p) :=
  (summable_geometric_of_lt_one (by linarith) (by linarith)).mul_left p

theorem tsum_geomPmf {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : ∑' d, geomPmf p d = 1 := by
  unfold geomPmf
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by linarith) (by linarith)]
  have h1 : (1 : ℝ) - (1 - p) = p := by ring
  rw [h1, inv_eq_one_div, mul_one_div, div_self hp0.ne']

/-- The tail `∑_{d ≥ x} φ(d) = (1 − p)ˣ`. -/
theorem tsum_geomPmf_tail {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : ℕ) :
    ∑' d, (if x ≤ d then geomPmf p d else 0) = (1 - p) ^ x := by
  have hs : Summable fun d => if x ≤ d then geomPmf p d else 0 :=
    (summable_geomPmf hp0 hp1).of_nonneg_of_le
      (fun d => by split_ifs <;> [exact (geomPmf_pos hp0 hp1 d).le; exact le_rfl])
      (fun d => by split_ifs <;> [exact le_rfl; exact (geomPmf_pos hp0 hp1 d).le])
  rw [← hs.sum_add_tsum_nat_add x]
  have h0 : ∑ d ∈ range x, (if x ≤ d then geomPmf p d else 0) = 0 :=
    sum_eq_zero fun d hd => by rw [mem_range] at hd; simp [not_le.2 hd]
  rw [h0, zero_add]
  have h1 : ∀ d, (if x ≤ d + x then geomPmf p (d + x) else 0) = (1 - p) ^ x * geomPmf p d := by
    intro d
    have hd : x ≤ d + x := by omega
    simp only [hd, ite_true]
    unfold geomPmf
    rw [pow_add]
    ring
  simp only [h1]
  rw [tsum_mul_left, tsum_geomPmf hp0 hp1, mul_one]

/-- The inventory kernel (5.9): `P(x, a, x') = P{f(x, a, D) = x'}` for `D ∼ φ`. -/
noncomputable def inventoryKernel (K : ℕ) (p : ℝ) (x a x' : Fin (K + 1)) : ℝ :=
  ∑' d : ℕ, if inventoryNext K x a d = x' then geomPmf p d else 0

theorem summable_inventoryTerm (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x a x' : Fin (K + 1)) :
    Summable fun d : ℕ => if inventoryNext K x a d = x' then geomPmf p d else 0 :=
  (summable_geomPmf hp0 hp1).of_nonneg_of_le
    (fun d => by split_ifs <;> [exact (geomPmf_pos hp0 hp1 d).le; exact le_rfl])
    (fun d => by split_ifs <;> [exact le_rfl; exact (geomPmf_pos hp0 hp1 d).le])

theorem inventoryKernel_nonneg (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x a x' : Fin (K + 1)) :
    0 ≤ inventoryKernel K p x a x' :=
  tsum_nonneg fun d => by split_ifs <;> [exact (geomPmf_pos hp0 hp1 d).le; exact le_rfl]

theorem inventoryKernel_rowsum (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x a : Fin (K + 1)) :
    ∑ x', inventoryKernel K p x a x' = 1 := by
  unfold inventoryKernel
  rw [← Summable.tsum_finsetSum fun x' _ => summable_inventoryTerm K hp0 hp1 x a x',
    ← tsum_geomPmf hp0 hp1]
  refine tsum_congr fun d => ?_
  have hlt : inventoryNext K x a d < K + 1 := by unfold inventoryNext; omega
  rw [Finset.sum_eq_single (⟨inventoryNext K x a d, hlt⟩ : Fin (K + 1))]
  · simp
  · intro i _ hi
    have : ¬ (inventoryNext K x a d = (i : ℕ)) := fun h => hi (Fin.ext h.symm)
    simp [this]
  · intro h
    exact absurd (mem_univ _) h

/-- The expected revenue `∑_d (x ∧ d)φ(d)` of (5.8). -/
noncomputable def expectedRevenue (p : ℝ) (x : ℕ) : ℝ := ∑' d : ℕ, min (x : ℝ) d * geomPmf p d

theorem summable_revenueTerm {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : ℕ) :
    Summable fun d : ℕ => min (x : ℝ) d * geomPmf p d :=
  ((summable_geomPmf hp0 hp1).mul_left (x : ℝ)).of_nonneg_of_le
    (fun d => mul_nonneg (le_min (Nat.cast_nonneg x) (Nat.cast_nonneg d))
      (geomPmf_pos hp0 hp1 d).le)
    (fun d => mul_le_mul_of_nonneg_right (min_le_left _ _) (geomPmf_pos hp0 hp1 d).le)

/-- The inventory reward (5.8): `r(x, a) = ∑_d (x ∧ d)φ(d) − ca − κ·1{a > 0}`. -/
noncomputable def inventoryReward (p c κ : ℝ) (x a : ℕ) : ℝ :=
  expectedRevenue p x - c * a - κ * (if 0 < a then 1 else 0)

/-- The optimal inventory model as an MDP (pp. 131–132): states and actions `{0, …, K}`,
`Γ(x) = {0, …, K − x}`, `β = 1/(1 + r)`. -/
noncomputable def inventory (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) {r : ℝ}
    (hr : 0 < r) : MDP (Fin (K + 1)) (Fin (K + 1)) where
  Γ := fun x => univ.filter fun a => (a : ℕ) ≤ K - x
  Γ_nonempty := fun x => ⟨⟨0, by omega⟩, by simp⟩
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  r := fun x a => inventoryReward p c κ x a
  P := inventoryKernel K p
  P_nonneg := inventoryKernel_nonneg K hp0 hp1
  P_rowsum := inventoryKernel_rowsum K hp0 hp1

/-- The feasible orders (5.7): `a ∈ Γ(x) ⟺ a ≤ K − x`. -/
theorem inventory_mem_Γ (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) {r : ℝ} (hr : 0 < r)
    (x a : Fin (K + 1)) : a ∈ (inventory K hp0 hp1 c κ hr).Γ x ↔ (a : ℕ) ≤ K - x := by
  simp [inventory]

/-- Exercise 5.1.2 (p. 132): for a feasible order `a ≤ K − x`, the kernel (5.9) is
`P(x, a, x') = (1 − p)ˣ` if `x' = a` (demand at least `x`), `p(1 − p)^{x + a − x'}` if
`a < x' ≤ x + a` (demand exactly `x + a − x'`), and `0` otherwise. -/
theorem inventoryKernel_eq (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {x a x' : Fin (K + 1)}
    (ha : (a : ℕ) ≤ K - x) :
    inventoryKernel K p x a x' =
      if (x' : ℕ) = a then (1 - p) ^ (x : ℕ)
      else if (a : ℕ) < x' ∧ (x' : ℕ) ≤ (x : ℕ) + a then geomPmf p ((x : ℕ) + a - x') else 0 := by
  have hx : (x : ℕ) ≤ K := Nat.le_of_lt_succ x.2
  have hnext : ∀ d, inventoryNext K x a d = (x - d) + a := fun d =>
    inventoryNext_of_feasible ha hx
  unfold inventoryKernel
  simp only [hnext]
  split_ifs with h1 h2
  · -- `x' = a`: exactly the demands `d ≥ x`
    rw [← tsum_geomPmf_tail hp0 hp1 x]
    refine tsum_congr fun d => ?_
    have : (x - d) + a = (x' : ℕ) ↔ x ≤ d := by omega
    simp only [this]
  · -- `a < x' ≤ x + a`: exactly the demand `d = x + a − x'`
    rw [tsum_eq_single ((x : ℕ) + a - x')]
    · have : ((x : ℕ) - ((x : ℕ) + a - x')) + a = (x' : ℕ) := by omega
      simp [this]
    · intro d hd
      have : ¬ (((x : ℕ) - d) + a = (x' : ℕ)) := by omega
      simp [this]
  · -- otherwise no demand leads to `x'`
    refine (tsum_congr fun d => ?_).trans tsum_zero
    have : ¬ ((x - d) + a = (x' : ℕ)) := by omega
    simp [this]

end SargentStachurski.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Operator factorisations: expected value functions and Q-factors

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.3.4–§5.3.5
(pp. 171–178).

The Bellman operator factors as `T = M D E` through three auxiliary operators:
`E` takes conditional expectations, `(Ev)(x, a) = ∑ v(x')P(x, a, x')`; `D`
discounts and adds rewards, `(Dg)(x, a) = r(x, a) + βg(x, a)`; `M` maximises
over feasible actions, `(Mq)(x) = max_{a ∈ Γ(x)} q(x, a)`. The other two
round trips `R = E M D` (expected value functions) and `S = D E M` (Q-factors)
are given explicitly (Exercise 5.3.5), satisfy the iterate relations of
Exercise 5.3.6, and are contractions of modulus `β` because `E` and `M` are
nonexpansive and `D` contracts (Exercise 5.3.7, Lemma 5.3.5). Their fixed
points are `g* = Ev*`, `q* = Dg*`, `v* = Mq*` (Proposition 5.3.6), and a policy
is optimal iff it is `v*`-greedy iff `g*`-greedy iff `q*`-greedy
(Corollary 5.3.7), which contains Proposition 5.3.4 on Q-factors
(Exercise 5.3.4). The policy versions `R_σ = E M_σ D`, `S_σ = D E M_σ`,
`T_σ = M_σ D E` satisfy `R_σᵏ = E T_σᵏ⁻¹ M_σ D` (Exercise 5.3.8), which gives the
equivalence of refactored and regular optimistic policy iteration (p. 178).

Functions on the feasible pairs `G` are represented as functions on `X × A`;
the maximisation `M` only ever looks at feasible actions.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- `E : ℝ^X → ℝ^G`, `(Ev)(x, a) = ∑ v(x')P(x, a, x')` (p. 172). -/
def E (v : X → ℝ) : X × A → ℝ := fun p => ∑ x', v x' * M.P p.1 p.2 x'

/-- `D : ℝ^G → ℝ^G`, `(Dg)(x, a) = r(x, a) + βg(x, a)` (p. 172). -/
def D (g : X × A → ℝ) : X × A → ℝ := fun p => M.r p.1 p.2 + M.β * g p

/-- `Mop : ℝ^G → ℝ^X`, `(Mq)(x) = max_{a ∈ Γ(x)} q(x, a)` (p. 172). -/
noncomputable def Mop (q : X × A → ℝ) : X → ℝ := fun x =>
  (M.Γ x).sup' (M.Γ_nonempty x) fun a => q (x, a)

/-- `D(Ev) = B(·, ·, v)`: discounting the expectation gives the action value. -/
theorem D_E (v : X → ℝ) (p : X × A) : M.D (M.E v) p = M.B v p.1 p.2 := rfl

/-- (5.40): `T = M D E`. -/
theorem T_eq_Mop_D_E (v : X → ℝ) : M.T v = M.Mop (M.D (M.E v)) := rfl

/-- The expected value Bellman operator `R = E M D` (5.40). -/
noncomputable def R (g : X × A → ℝ) : X × A → ℝ := M.E (M.Mop (M.D g))

/-- The Q-factor Bellman operator `S = D E M` (5.40), (5.39). -/
noncomputable def S (q : X × A → ℝ) : X × A → ℝ := M.D (M.E (M.Mop q))

/-- Exercise 5.3.5 (p. 173):
`(Rg)(x, a) = ∑ max_{a' ∈ Γ(x')} {r(x', a') + βg(x', a')} P(x, a, x')`. -/
theorem R_apply (g : X × A → ℝ) (p : X × A) :
    M.R g p = ∑ x', ((M.Γ x').sup' (M.Γ_nonempty x') fun a' => M.r x' a' + M.β * g (x', a')) *
      M.P p.1 p.2 x' := rfl

/-- Exercise 5.3.5 (p. 173), (5.39):
`(Sq)(x, a) = r(x, a) + β ∑ max_{a' ∈ Γ(x')} q(x', a') P(x, a, x')`. -/
theorem S_apply (q : X × A → ℝ) (p : X × A) :
    M.S q p = M.r p.1 p.2 + M.β * ∑ x', ((M.Γ x').sup' (M.Γ_nonempty x') fun a' => q (x', a')) *
      M.P p.1 p.2 x' := rfl

/-! ### Exercise 5.3.6: iterate relations -/

/-- `Rᵏ⁺¹ = E Tᵏ M D`. -/
theorem R_iterate_succ (k : ℕ) (g : X × A → ℝ) : M.R^[k + 1] g = M.E (M.T^[k] (M.Mop (M.D g))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `Rᵏ⁺¹ = E M Sᵏ D`. -/
theorem R_iterate_succ' (k : ℕ) (g : X × A → ℝ) :
    M.R^[k + 1] g = M.E (M.Mop (M.S^[k] (M.D g))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `Sᵏ⁺¹ = D Rᵏ E M`. -/
theorem S_iterate_succ (k : ℕ) (q : X × A → ℝ) : M.S^[k + 1] q = M.D (M.R^[k] (M.E (M.Mop q))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `Sᵏ⁺¹ = D E Tᵏ M`. -/
theorem S_iterate_succ' (k : ℕ) (q : X × A → ℝ) :
    M.S^[k + 1] q = M.D (M.E (M.T^[k] (M.Mop q))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `Tᵏ⁺¹ = M Sᵏ D E`. -/
theorem T_iterate_succ (k : ℕ) (v : X → ℝ) : M.T^[k + 1] v = M.Mop (M.S^[k] (M.D (M.E v))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `Tᵏ⁺¹ = M D Rᵏ E`. -/
theorem T_iterate_succ' (k : ℕ) (v : X → ℝ) : M.T^[k + 1] v = M.Mop (M.D (M.R^[k] (M.E v))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-! ### Exercise 5.3.7: `E` and `M` are nonexpansive, `D` is a contraction -/

/-- Exercise 5.3.7 (i): `‖Ev − Ev'‖ ≤ ‖v − v'‖`. -/
theorem norm_E_sub_le (v v' : X → ℝ) : ‖M.E v - M.E v'‖ ≤ ‖v - v'‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  rintro ⟨x, a⟩
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have := (M.isMarkov_Pσ fun _ => a).abs_mulVec_sub_le v v' x
  simp only [mulVec_apply_eq, Pσ_apply] at this
  exact this

/-- Exercise 5.3.7 (ii): `‖Mg − Mg'‖ ≤ ‖g − g'‖`. -/
theorem norm_Mop_sub_le (g g' : X × A → ℝ) : ‖M.Mop g - M.Mop g'‖ ≤ ‖g - g'‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Pi.sub_apply, Real.norm_eq_abs, Mop, Mop]
  refine (abs_sup'_sub_sup'_le _ _ _).trans (Finset.sup'_le _ _ fun a _ => ?_)
  have := norm_le_pi_norm (g - g') (x, a)
  simpa [Real.norm_eq_abs] using this

/-- Exercise 5.3.7 (iii): `‖Dq − Dq'‖ ≤ β‖q − q'‖`. -/
theorem norm_D_sub_le (q q' : X × A → ℝ) : ‖M.D q - M.D q'‖ ≤ M.β * ‖q - q'‖ := by
  have : M.D q - M.D q' = M.β • (q - q') := by
    funext p
    simp only [D, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg M.β_pos.le]

/-- Lemma 5.3.5 (p. 174): `R` is a contraction of modulus `β`. -/
theorem isContractionOn_R : IsContractionOn M.R Set.univ M.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := M.β_pos.le
  lt_one := M.β_lt_one
  norm_sub_le _ _ _ _ :=
    (M.norm_E_sub_le _ _).trans ((M.norm_Mop_sub_le _ _).trans (M.norm_D_sub_le _ _))

/-- Lemma 5.3.5 (p. 174), Exercise 5.3.4 (p. 171): `S` is a contraction of modulus `β`. -/
theorem isContractionOn_S : IsContractionOn M.S Set.univ M.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := M.β_pos.le
  lt_one := M.β_lt_one
  norm_sub_le _ _ _ _ :=
    (M.norm_D_sub_le _ _).trans (mul_le_mul_of_nonneg_left
      ((M.norm_E_sub_le _ _).trans (M.norm_Mop_sub_le _ _)) M.β_pos.le)

/-- Lemma 5.3.5 (p. 174): the factorisation proof that `T` is a contraction of modulus `β`. -/
theorem norm_T_sub_le (v v' : X → ℝ) : ‖M.T v - M.T v'‖ ≤ M.β * ‖v - v'‖ := by
  rw [T_eq_Mop_D_E, T_eq_Mop_D_E]
  exact (M.norm_Mop_sub_le _ _).trans ((M.norm_D_sub_le _ _).trans
    (mul_le_mul_of_nonneg_left (M.norm_E_sub_le _ _) M.β_pos.le))

/-- `E`, `D` and `M` are order preserving. -/
theorem E_monotone : Monotone M.E := fun _ _ h _ =>
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (h x') (M.P_nonneg _ _ _)

theorem D_monotone : Monotone M.D := fun _ _ h p =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (h p) M.β_pos.le)

theorem Mop_monotone : Monotone M.Mop := fun _ _ h x =>
  Finset.sup'_mono_fun fun a _ => h (x, a)

/-- Exercise 5.3.4 (p. 171): `S` is order preserving. -/
theorem S_monotone : Monotone M.S := fun _ _ h =>
  M.D_monotone (M.E_monotone (M.Mop_monotone h))

theorem R_monotone : Monotone M.R := fun _ _ h =>
  M.E_monotone (M.Mop_monotone (M.D_monotone h))

/-! ### Fixed points (Proposition 5.3.6) and greedy policies (Corollary 5.3.7) -/

/-- `g`-greedy (p. 175): `σ(x)` maximises `r(x, a) + βg(x, a)` over `Γ(x)`. -/
def IsGGreedy (g : X × A → ℝ) (σ : X → A) : Prop :=
  M.IsFeasible σ ∧ ∀ x, ∀ a ∈ M.Γ x, M.D g (x, a) ≤ M.D g (x, σ x)

/-- `q`-greedy (p. 175): `σ(x)` maximises `q(x, a)` over `Γ(x)`. -/
def IsQGreedy (q : X × A → ℝ) (σ : X → A) : Prop :=
  M.IsFeasible σ ∧ ∀ x, ∀ a ∈ M.Γ x, q (x, a) ≤ q (x, σ x)

/-- `v`-greedy is `(Ev)`-greedy, since `D(Ev) = B(·, ·, v)`. -/
theorem isGreedy_iff_isGGreedy_E (v : X → ℝ) (σ : X → A) : M.IsGreedy v σ ↔ M.IsGGreedy (M.E v) σ :=
  Iff.rfl

/-- `g`-greedy is `(Dg)`-greedy. -/
theorem isGGreedy_iff_isQGreedy_D (g : X × A → ℝ) (σ : X → A) :
    M.IsGGreedy g σ ↔ M.IsQGreedy (M.D g) σ :=
  Iff.rfl

/-! ### Policy operators in the three spaces (§5.3.5.3) -/

/-- `(M_σ q)(x) = q(x, σ(x))` (p. 177). -/
def Mσ (σ : X → A) (q : X × A → ℝ) : X → ℝ := fun x => q (x, σ x)

/-- `T_σ = M_σ D E` (p. 177): the policy operator of (5.19). -/
theorem Tσ_eq_Mσ_D_E (σ : X → A) (v : X → ℝ) : M.Tσ σ v = Mσ σ (M.D (M.E v)) := rfl

/-- `R_σ = E M_σ D` (p. 177). -/
def Rσ (σ : X → A) (g : X × A → ℝ) : X × A → ℝ := M.E (Mσ σ (M.D g))

/-- `S_σ = D E M_σ` (p. 177). -/
def Sσ (σ : X → A) (q : X × A → ℝ) : X × A → ℝ := M.D (M.E (Mσ σ q))

/-- Exercise 5.3.8, (5.41): `R_σᵏ⁺¹ = E T_σᵏ M_σ D`. -/
theorem Rσ_iterate_succ (σ : X → A) (k : ℕ) (g : X × A → ℝ) :
    (M.Rσ σ)^[k + 1] g = M.E ((M.Tσ σ)^[k] (Mσ σ (M.D g))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `S_σᵏ⁺¹ = D E T_σᵏ M_σ`. -/
theorem Sσ_iterate_succ (σ : X → A) (k : ℕ) (q : X × A → ℝ) :
    (M.Sσ σ)^[k + 1] q = M.D (M.E ((M.Tσ σ)^[k] (Mσ σ q))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- Refactored OPI (p. 178): `R_σᵐ (Ev) = E (T_σᵐ v)`, so the expected value iterates of
Algorithm 5.5 started at `g₀ = Ev₀` are the images under `E` of the regular OPI iterates. -/
theorem Rσ_iterate_E (σ : X → A) (m : ℕ) (v : X → ℝ) :
    (M.Rσ σ)^[m] (M.E v) = M.E ((M.Tσ σ)^[m] v) := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [Rσ_iterate_succ, iterate_succ_apply]
    rfl

/-- Refactored OPI (p. 178): a policy is `(Ev)`-greedy iff it is `v`-greedy, so both algorithms
select the same policies. -/
theorem isGGreedy_E_iff (v : X → ℝ) (σ : X → A) : M.IsGGreedy (M.E v) σ ↔ M.IsGreedy v σ :=
  Iff.rfl

variable [DecidableEq X] [DecidableEq A]

/-- `g* = Ev*`: the expected value function of the optimal value. -/
noncomputable def gstar : X × A → ℝ := M.E M.vstar

/-- `q* = Dg*`: the optimal Q-factor. -/
noncomputable def qstar : X × A → ℝ := M.D M.gstar

/-- Proposition 5.3.6 (i), p. 175: `g* = Ev*` is a fixed point of `R`, since
`Ev* = ETv* = EMDEv*`. -/
theorem isFixedPt_R_gstar : IsFixedPt M.R M.gstar := by
  change M.E (M.Mop (M.D (M.E M.vstar))) = M.E M.vstar
  rw [← T_eq_Mop_D_E, M.isFixedPt_T_vstar.eq]

/-- Proposition 5.3.6: `g*` is the unique fixed point of `R` in `ℝ^G`. -/
theorem eq_gstar_of_isFixedPt {g : X × A → ℝ} (hg : IsFixedPt M.R g) : g = M.gstar :=
  M.isContractionOn_R.fixedPt_unique (Set.mem_univ g) (Set.mem_univ _) hg M.isFixedPt_R_gstar

/-- Proposition 5.3.6 (ii), p. 175: `q* = Dg*` is a fixed point of `S`. -/
theorem isFixedPt_S_qstar : IsFixedPt M.S M.qstar := by
  change M.D (M.E (M.Mop (M.D (M.E M.vstar)))) = M.D (M.E M.vstar)
  rw [← T_eq_Mop_D_E, M.isFixedPt_T_vstar.eq]

/-- Proposition 5.3.6: `q*` is the unique fixed point of `S` in `ℝ^G`. -/
theorem eq_qstar_of_isFixedPt {q : X × A → ℝ} (hq : IsFixedPt M.S q) : q = M.qstar :=
  M.isContractionOn_S.fixedPt_unique (Set.mem_univ q) (Set.mem_univ _) hq M.isFixedPt_S_qstar

/-- Proposition 5.3.6 (iii), p. 175: `v* = Mq*`. -/
theorem vstar_eq_Mop_qstar : M.vstar = M.Mop M.qstar :=
  M.isFixedPt_T_vstar.eq.symm

/-- The explicit forms (p. 175): `g*(x, a) = ∑ v*(x')P(x, a, x')`, `q*(x, a) = r(x, a) + βg*(x, a)`,
`v*(x) = max_{a ∈ Γ(x)} q*(x, a)`. -/
theorem gstar_apply (x : X) (a : A) : M.gstar (x, a) = ∑ x', M.vstar x' * M.P x a x' := rfl

theorem qstar_apply (x : X) (a : A) : M.qstar (x, a) = M.r x a + M.β * M.gstar (x, a) := rfl

theorem vstar_apply_eq_sup'_qstar (x : X) :
    M.vstar x = (M.Γ x).sup' (M.Γ_nonempty x) fun a => M.qstar (x, a) :=
  congrFun M.vstar_eq_Mop_qstar x

/-- Successive approximation with `R` and `S` converges to `g*` and `q*` (p. 176). -/
theorem tendsto_iterate_R (g : X × A → ℝ) : Tendsto (fun k : ℕ => M.R^[k] g) atTop (𝓝 M.gstar) :=
  M.isContractionOn_R.tendsto_iterate_fixedPt (Set.mem_univ g) (Set.mem_univ _) M.isFixedPt_R_gstar

theorem tendsto_iterate_S (q : X × A → ℝ) : Tendsto (fun k : ℕ => M.S^[k] q) atTop (𝓝 M.qstar) :=
  M.isContractionOn_S.tendsto_iterate_fixedPt (Set.mem_univ q) (Set.mem_univ _) M.isFixedPt_S_qstar

/-- Corollary 5.3.7 (p. 176), (i) ⟺ (ii): `v*`-greedy iff `g*`-greedy. -/
theorem isGreedy_vstar_iff_isGGreedy_gstar (σ : X → A) :
    M.IsGreedy M.vstar σ ↔ M.IsGGreedy M.gstar σ :=
  Iff.rfl

/-- Corollary 5.3.7 (p. 176), (ii) ⟺ (iii): `g*`-greedy iff `q*`-greedy. -/
theorem isGGreedy_gstar_iff_isQGreedy_qstar (σ : X → A) :
    M.IsGGreedy M.gstar σ ↔ M.IsQGreedy M.qstar σ :=
  Iff.rfl

/-- Corollary 5.3.7 (p. 176): `σ` is optimal iff it is `g*`-greedy. -/
theorem isOptimal_iff_isGGreedy (σ : X → A) : M.IsOptimal σ ↔ M.IsGGreedy M.gstar σ :=
  M.isOptimal_iff_isGreedy σ

/-- **Proposition 5.3.4** (p. 172) and Corollary 5.3.7: `σ` is optimal iff it is `q*`-greedy,
`σ(x) ∈ argmax_{a ∈ Γ(x)} q*(x, a)`. -/
theorem isOptimal_iff_isQGreedy (σ : X → A) : M.IsOptimal σ ↔ M.IsQGreedy M.qstar σ :=
  M.isOptimal_iff_isGreedy σ

end MDP

end SargentStachurski.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Expected value functions: structural estimation and stochastic returns

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.3.1 and §5.3.3
(pp. 162–171).

The generic structural model (5.33) has an endogenous state `y`, a preference
shock `ε` drawn IID from `φ`, and a kernel `P₀(y, a, y')` for `y`; the state is
`(y, ε)`. The book allows a continuous shock space; here `E` is finite, the
discretised form in which "all the optimality theory for MDPs applies" (p. 165).
The expected value function (5.34) depends on `(y, a)` only; the expected value
Bellman operator `R` of (5.35) acts on `ℝ^{Y × A}`, is order preserving and a
contraction of modulus `β` (Exercise 5.3.1), and its fixed point `g*`
determines optimality (Proposition 5.3.1): `σ` is optimal iff
`σ(y, ε) ∈ argmax_{a ∈ Γ(y, ε)} {r(y, ε, a) + βg*(y, a)}`. The feasible set may
depend on the shock, as it does in §5.3.3.

Optimal savings with stochastic returns (§5.3.3) and the savings model with
transient and persistent income (Exercise 5.3.3) are instances: their expected
value functions (5.37) depend only on income and next period's wealth, and
their Bellman equations in expected value form are the fixed point equations of
the reduced operator; the modified `σ`-value operator `R_σ` of p. 169 is the
policy operator of §5.3.5.3 in reduced form.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

/-- The generic structural model (5.33): endogenous states `Y`, shocks `E` with distribution `φ`,
actions `A`, feasible sets `Γ(y, ε)`, rewards `r(y, ε, a)`, a stochastic kernel `P₀` for `y`. -/
structure Structural (Y E A : Type*) [Fintype Y] [Fintype E] [Fintype A] where
  Γ : Y → E → Finset A
  Γ_nonempty : ∀ y ε, (Γ y ε).Nonempty
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  r : Y → E → A → ℝ
  P₀ : Y → A → Y → ℝ
  P₀_nonneg : ∀ y a y', 0 ≤ P₀ y a y'
  P₀_rowsum : ∀ y a, ∑ y', P₀ y a y' = 1
  φ : E → ℝ
  φ_dist : IsDistribution φ

/-- The lift of a function on `Y × A` to one on `(Y × E) × A`, constant in the shock. -/
def liftEV {Y A : Type*} (E : Type*) (g : Y × A → ℝ) : (Y × E) × A → ℝ := fun p => g (p.1.1, p.2)

/-- `‖lift g − lift g'‖ ≤ ‖g − g'‖`. -/
theorem norm_liftEV_sub_le {Y A : Type*} [Fintype Y] [Fintype A] (E : Type*) [Fintype E]
    (g g' : Y × A → ℝ) : ‖liftEV E g - liftEV E g'‖ ≤ ‖g - g'‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  rintro ⟨⟨y, ε⟩, a⟩
  have := norm_le_pi_norm (g - g') (y, a)
  simpa [liftEV] using this

/-- `‖g − g'‖ ≤ ‖lift g − lift g'‖` when the shock space is nonempty. -/
theorem norm_le_norm_liftEV {Y A : Type*} [Fintype Y] [Fintype A] (E : Type*) [Fintype E]
    [Nonempty E] (g g' : Y × A → ℝ) : ‖g - g'‖ ≤ ‖liftEV E g - liftEV E g'‖ := by
  obtain ⟨ε⟩ := ‹Nonempty E›
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  rintro ⟨y, a⟩
  have := norm_le_pi_norm (liftEV E g - liftEV E g') ((y, ε), a)
  simpa [liftEV] using this

namespace Structural

variable {Y E A : Type*} [Fintype Y] [Fintype E] [Fintype A] (S : Structural Y E A)

/-- The MDP on the state space `Y × E` (p. 165): `P((y, ε), a, (y', ε')) = P₀(y, a, y')φ(ε')`. -/
noncomputable def toMDP : MDP (Y × E) A where
  Γ := fun x => S.Γ x.1 x.2
  Γ_nonempty := fun x => S.Γ_nonempty x.1 x.2
  β := S.β
  β_pos := S.β_pos
  β_lt_one := S.β_lt_one
  r := fun x a => S.r x.1 x.2 a
  P := fun x a x' => S.P₀ x.1 a x'.1 * S.φ x'.2
  P_nonneg := fun x a x' => mul_nonneg (S.P₀_nonneg _ _ _) (S.φ_dist.nonneg _)
  P_rowsum := fun x a => by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, S.φ_dist.sum_eq_one, mul_one]
    exact S.P₀_rowsum x.1 a

/-- The expectation of `v` under `P((y, ε), a, ·)` is the expected value function (5.34):
`∑_{y', ε'} v(y', ε')P₀(y, a, y')φ(ε')`, independent of `ε`. -/
theorem E_toMDP (v : Y × E → ℝ) (y : Y) (ε : E) (a : A) :
    S.toMDP.E v ((y, ε), a) = ∑ y', (∑ ε', v (y', ε') * S.φ ε') * S.P₀ y a y' := by
  simp only [MDP.E, toMDP]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun y' _ => ?_
  rw [sum_mul]
  exact sum_congr rfl fun ε' _ => by ring

/-- The expected value function on `Y × A`, (5.34):
`g(y, a) = ∑_{y', ε'} v(y', ε')P₀(y, a, y')φ(ε')`. -/
def Ered (v : Y × E → ℝ) : Y × A → ℝ := fun p =>
  ∑ y', (∑ ε', v (y', ε') * S.φ ε') * S.P₀ p.1 p.2 y'

theorem E_toMDP_eq_lift (v : Y × E → ℝ) : S.toMDP.E v = liftEV E (S.Ered v) := by
  funext ⟨⟨y, ε⟩, a⟩
  exact S.E_toMDP v y ε a

/-- The expected value Bellman operator (5.35) on `ℝ^{Y × A}`:
`(Rg)(y, a) = ∑_{y'} ∑_{ε'} max_{a' ∈ Γ(y', ε')} {r(y', ε', a') + βg(y', a')} φ(ε')P₀(y, a, y')`. -/
noncomputable def Rred (g : Y × A → ℝ) : Y × A → ℝ := fun p =>
  ∑ y', (∑ ε', ((S.Γ y' ε').sup' (S.Γ_nonempty y' ε') fun a' => S.r y' ε' a' + S.β * g (y', a')) *
    S.φ ε') * S.P₀ p.1 p.2 y'

/-- The MDP's operator `R = EMD` acts on lifted functions as the reduced operator. -/
theorem R_lift (g : Y × A → ℝ) : S.toMDP.R (liftEV E g) = liftEV E (S.Rred g) := by
  funext ⟨⟨y, ε⟩, a⟩
  simp only [MDP.R]
  rw [S.E_toMDP]
  rfl

/-- Exercise 5.3.1 (p. 166): `R` is order preserving. -/
theorem Rred_monotone : Monotone S.Rred := by
  intro g g' hgg' p
  unfold Rred
  refine sum_le_sum fun y' _ => mul_le_mul_of_nonneg_right (sum_le_sum fun ε' _ =>
    mul_le_mul_of_nonneg_right (Finset.sup'_mono_fun fun a' _ => ?_) (S.φ_dist.nonneg ε'))
    (S.P₀_nonneg _ _ _)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hgg' (y', a')) S.β_pos.le)

/-- Exercise 5.3.1 (p. 166): `R` is a contraction of modulus `β` on `ℝ^{Y × A}` under the supremum
norm, through the lift to the MDP's operator (Lemma 5.3.5). -/
theorem isContractionOn_Rred [Nonempty E] : IsContractionOn S.Rred Set.univ S.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := S.β_pos.le
  lt_one := S.β_lt_one
  norm_sub_le g _ g' _ := by
    calc ‖S.Rred g - S.Rred g'‖ ≤ ‖liftEV E (S.Rred g) - liftEV E (S.Rred g')‖ :=
          norm_le_norm_liftEV E _ _
      _ = ‖S.toMDP.R (liftEV E g) - S.toMDP.R (liftEV E g')‖ := by rw [R_lift, R_lift]
      _ ≤ S.β * ‖liftEV E g - liftEV E g'‖ :=
          S.toMDP.isContractionOn_R.norm_sub_le _ (Set.mem_univ _) _ (Set.mem_univ _)
      _ ≤ S.β * ‖g - g'‖ := mul_le_mul_of_nonneg_left (norm_liftEV_sub_le E g g') S.β_pos.le

variable [DecidableEq Y] [DecidableEq E] [DecidableEq A]

/-- The reduced optimal expected value function `g* = Ered v*`, (5.34) at `v = v*`. -/
noncomputable def gred : Y × A → ℝ := S.Ered S.toMDP.vstar

/-- The MDP's `g*` is the lift of the reduced `g*`. -/
theorem gstar_eq_lift : S.toMDP.gstar = liftEV E S.gred := S.E_toMDP_eq_lift _

/-- `g*` solves the expected value Bellman equation (p. 165): it is a fixed point of `R`. -/
theorem isFixedPt_Rred_gred [Nonempty E] : IsFixedPt S.Rred S.gred := by
  have h := S.toMDP.isFixedPt_R_gstar
  rw [IsFixedPt, gstar_eq_lift, R_lift] at h
  funext p
  obtain ⟨ε⟩ := ‹Nonempty E›
  exact congrFun h ((p.1, ε), p.2)

/-- `g*` is the unique fixed point of `R` in `ℝ^{Y × A}`, computable by successive approximation
(p. 166). -/
theorem eq_gred_of_isFixedPt [Nonempty E] {g : Y × A → ℝ} (hg : IsFixedPt S.Rred g) :
    g = S.gred :=
  S.isContractionOn_Rred.fixedPt_unique (Set.mem_univ g) (Set.mem_univ _) hg S.isFixedPt_Rred_gred

theorem tendsto_iterate_Rred [Nonempty E] (g : Y × A → ℝ) :
    Tendsto (fun k : ℕ => S.Rred^[k] g) atTop (𝓝 S.gred) :=
  S.isContractionOn_Rred.tendsto_iterate_fixedPt (Set.mem_univ g) (Set.mem_univ _)
    S.isFixedPt_Rred_gred

/-- The Bellman equation in expected value form (p. 165):
`v*(y, ε) = max_{a ∈ Γ(y, ε)} {r(y, ε, a) + βg*(y, a)}`. -/
theorem vstar_eq (y : Y) (ε : E) :
    S.toMDP.vstar (y, ε) =
      (S.Γ y ε).sup' (S.Γ_nonempty y ε) fun a => S.r y ε a + S.β * S.gred (y, a) := by
  rw [S.toMDP.vstar_apply_eq_sup'_qstar]
  refine Finset.sup'_congr _ rfl fun a _ => ?_
  rw [MDP.qstar_apply, gstar_eq_lift]
  rfl

/-- **Proposition 5.3.1** (p. 166): a feasible policy is optimal iff
`σ(y, ε) ∈ argmax_{a ∈ Γ(y, ε)} {r(y, ε, a) + βg*(y, a)}` for all `(y, ε)`. -/
theorem isOptimal_iff (σ : Y × E → A) :
    S.toMDP.IsOptimal σ ↔
      S.toMDP.IsFeasible σ ∧ ∀ y ε, ∀ a ∈ S.Γ y ε,
        S.r y ε a + S.β * S.gred (y, a) ≤ S.r y ε (σ (y, ε)) + S.β * S.gred (y, σ (y, ε)) := by
  rw [S.toMDP.isOptimal_iff_isGGreedy, MDP.IsGGreedy, gstar_eq_lift]
  constructor
  · rintro ⟨hσ, h⟩
    exact ⟨hσ, fun y ε a ha => h (y, ε) a ha⟩
  · rintro ⟨hσ, h⟩
    exact ⟨hσ, fun x a ha => h x.1 x.2 a ha⟩

omit [DecidableEq Y] [DecidableEq E] [DecidableEq A] in
/-- The modified `σ`-value operator `R_σ = E M_σ D` of p. 169, in reduced form:
`(R_σ g)(y, a) = ∑_{y', ε'} [r(y', ε', σ(y', ε')) + βg(y', σ(y', ε'))] φ(ε') P₀(y, a, y')`. -/
theorem Rσ_lift (σ : Y × E → A) (g : Y × A → ℝ) (y : Y) (ε : E) (a : A) :
    S.toMDP.Rσ σ (liftEV E g) ((y, ε), a) =
      ∑ y', (∑ ε', (S.r y' ε' (σ (y', ε')) + S.β * g (y', σ (y', ε'))) * S.φ ε') * S.P₀ y a y' := by
  simp only [MDP.Rσ]
  rw [S.E_toMDP]
  rfl

end Structural

/-! ### Optimal savings with stochastic returns (§5.3.3) -/

variable {W Yi Et : Type*} [Fintype W] [Fintype Yi] [Fintype Et] [DecidableEq W]

/-- Optimal savings with IID gross returns `η ∼ φ` (§5.3.3): endogenous state `(w, y)` with wealth
values `wealth` and income values `inc`, shock `η` with return `ret η`, actions `w'` with
`w' ≤ η(w + y)`, reward `u(w + y − w'/η)`, income `Q`-Markov. -/
noncomputable def stochasticReturns (wealth : W → ℝ) (inc : Yi → ℝ) (ret : Et → ℝ)
    {Q : Matrix Yi Yi ℝ} (hQ : IsMarkov Q) {φ : Et → ℝ} (hφ : IsDistribution φ) (u : ℝ → ℝ)
    (hΓ : ∀ w y η, ∃ s, wealth s ≤ ret η * (wealth w + inc y)) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Structural (W × Yi) Et W where
  Γ := fun x η => univ.filter fun s => wealth s ≤ ret η * (wealth x.1 + inc x.2)
  Γ_nonempty := fun x η => by
    obtain ⟨s, hs⟩ := hΓ x.1 x.2 η
    exact ⟨s, by simp [hs]⟩
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := fun x η s => u (wealth x.1 + inc x.2 - wealth s / ret η)
  P₀ := choiceKernel Q
  P₀_nonneg := choiceKernel_nonneg hQ
  P₀_rowsum := choiceKernel_rowsum hQ
  φ := φ
  φ_dist := hφ

namespace stochasticReturns

variable (wealth : W → ℝ) (inc : Yi → ℝ) (ret : Et → ℝ) {Q : Matrix Yi Yi ℝ} (hQ : IsMarkov Q)
  {φ : Et → ℝ} (hφ : IsDistribution φ) (u : ℝ → ℝ)
  (hΓ : ∀ w y η, ∃ s, wealth s ≤ ret η * (wealth w + inc y)) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)

/-- (5.37): the expected value function `g(y, w') = ∑_{y', η'} v(w', y', η')Q(y, y')φ(η')`
depends on the current state only through income `y`, not current wealth `w`. -/
theorem Ered_apply (v : (W × Yi) × Et → ℝ) (w : W) (y : Yi) (w' : W) :
    (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).Ered v ((w, y), w') =
      ∑ y', (∑ η', v ((w', y'), η') * φ η') * Q y y' := by
  exact sum_mul_choiceKernel Q _ (w, y) w'

/-- The Bellman equation with stochastic returns (p. 168):
`v*(w, y, η) = max_{w' ≤ η(w + y)} {u(w + y − w'/η) + βg*(y, w')}`, with `g*` the expected value
function (5.37) of `v*`. -/
theorem bellman_equation [DecidableEq Yi] [DecidableEq Et] (w : W) (y : Yi) (η : Et) :
    (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).toMDP.vstar ((w, y), η) =
      (univ.filter fun s => wealth s ≤ ret η * (wealth w + inc y)).sup'
        ((stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).Γ_nonempty (w, y) η)
        fun w' => u (wealth w + inc y - wealth w' / ret η) +
          β * (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).gred ((w, y), w') :=
  Structural.vstar_eq _ (w, y) η

/-- The Bellman equation in expected value form (p. 169): `g*` satisfies
`g*(y, w') = ∑_{y', η'} max_{w'' ≤ η'(w' + y')} {u(w' + y' − w''/η') + βg*(y', w'')} Q(y, y')φ(η')`.
-/
theorem gred_eq [DecidableEq Yi] [DecidableEq Et] [Nonempty Et] (w : W) (y : Yi) (w' : W) :
    (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).gred ((w, y), w') =
      ∑ y', (∑ η', ((univ.filter fun s => wealth s ≤ ret η' * (wealth w' + inc y')).sup'
        ((stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).Γ_nonempty (w', y') η')
        fun w'' => u (wealth w' + inc y' - wealth w'' / ret η') +
          β * (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).gred ((w', y'), w'')) * φ η') *
        Q y y' := by
  have h := congrFun (Structural.isFixedPt_Rred_gred
    (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1)).eq ((w, y), w')
  rw [← h]
  exact sum_mul_choiceKernel Q _ (w, y) w'

end stochasticReturns

/-! ### Exercise 5.3.3: transient and persistent income -/

variable {Zp : Type*} [Fintype Zp]

/-- Exercise 5.3.3 (p. 169): optimal savings with labour income `Y = Z + ε`, `Z` `Q`-Markov and `ε`
IID with distribution `φ`, constant gross return `R`; endogenous state `(w, z)`, shock `ε`, actions
`w' ≤ R(w + z + ε)`, reward `u(w + z + ε − w'/R)`. -/
noncomputable def transientIncome (wealth : W → ℝ) (zval : Zp → ℝ) (eps : Et → ℝ)
    {Q : Matrix Zp Zp ℝ} (hQ : IsMarkov Q) {φ : Et → ℝ} (hφ : IsDistribution φ) (R : ℝ) (u : ℝ → ℝ)
    (hΓ : ∀ w z ε, ∃ s, wealth s ≤ R * (wealth w + zval z + eps ε)) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) : Structural (W × Zp) Et W where
  Γ := fun x ε => univ.filter fun s => wealth s ≤ R * (wealth x.1 + zval x.2 + eps ε)
  Γ_nonempty := fun x ε => by
    obtain ⟨s, hs⟩ := hΓ x.1 x.2 ε
    exact ⟨s, by simp [hs]⟩
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := fun x ε s => u (wealth x.1 + zval x.2 + eps ε - wealth s / R)
  P₀ := choiceKernel Q
  P₀_nonneg := choiceKernel_nonneg hQ
  P₀_rowsum := choiceKernel_rowsum hQ
  φ := φ
  φ_dist := hφ

namespace transientIncome

variable (wealth : W → ℝ) (zval : Zp → ℝ) (eps : Et → ℝ) {Q : Matrix Zp Zp ℝ} (hQ : IsMarkov Q)
  {φ : Et → ℝ} (hφ : IsDistribution φ) (R : ℝ) (u : ℝ → ℝ)
  (hΓ : ∀ w z ε, ∃ s, wealth s ≤ R * (wealth w + zval z + eps ε)) {β : ℝ} (hβ0 : 0 < β)
  (hβ1 : β < 1)

/-- Exercise 5.3.3, the Bellman equation: `v*(w, z, ε)` equals
`max_{w' ≤ R(w + z + ε)} {u(w + z + ε − w'/R) + β ∑_{z', ε'} v*(w', z', ε')Q(z, z')φ(ε')}`. -/
theorem bellman_equation [DecidableEq Zp] [DecidableEq Et] (w : W) (z : Zp) (ε : Et) :
    (transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).toMDP.vstar ((w, z), ε) =
      (univ.filter fun s => wealth s ≤ R * (wealth w + zval z + eps ε)).sup'
        ((transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).Γ_nonempty (w, z) ε)
        fun w' => u (wealth w + zval z + eps ε - wealth w' / R) +
          β * ∑ z', (∑ ε', (transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).toMDP.vstar
            ((w', z'), ε') * φ ε') * Q z z' := by
  rw [Structural.vstar_eq]
  refine Finset.sup'_congr _ rfl fun w' _ => ?_
  congr 2
  exact sum_mul_choiceKernel Q _ (w, z) w'

/-- Exercise 5.3.3, the Bellman equation in expected value form: with
`g*(z, w') = ∑_{z', ε'} v*(w', z', ε')Q(z, z')φ(ε')`, `g*(z, w')` equals
`∑_{z', ε'} max_{w'' ≤ R(w' + z' + ε')} {u(w' + z' + ε' − w''/R) + βg*(z', w'')} Q(z, z')φ(ε')`. -/
theorem gred_eq [DecidableEq Zp] [DecidableEq Et] [Nonempty Et] (w : W) (z : Zp) (w' : W) :
    (transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).gred ((w, z), w') =
      ∑ z', (∑ ε', ((univ.filter fun s => wealth s ≤ R * (wealth w' + zval z' + eps ε')).sup'
        ((transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).Γ_nonempty (w', z') ε')
        fun w'' => u (wealth w' + zval z' + eps ε' - wealth w'' / R) +
          β * (transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).gred ((w', z'), w'')) * φ ε') *
        Q z z' := by
  have h := congrFun (Structural.isFixedPt_Rred_gred
    (transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1)).eq ((w, z), w')
  rw [← h]
  exact sum_mul_choiceKernel Q _ (w, z) w'

end transientIncome

end SargentStachurski.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Gumbel max trick

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.3.2 (pp. 166–168).

When every feasible action's reward carries an independent standard Gumbel
shock, the expected maximum in the expected value Bellman operator has the
closed form `ln ∑ exp(·)` (Lemma 5.3.2, cited from Huijben et al.), and the
operator becomes (5.36):
`(Rg)(y, a) = ∑_{y'} ln[∑_{a'} exp(r(y', a') + βg(y', a'))] P(y, a, y')`.
Proposition 5.3.3: this `R` is a contraction of modulus `β`, by Blackwell's
condition: it is order preserving and `R(g + c) = Rg + βc`.

Exercise 5.3.2 is formalised at the level of distribution functions: the
Gumbel CDF with mode `μ` is `F_μ(z) = exp(−exp(−(z − μ)))`, and shifting a
random variable by `λ` shifts the mode, `F_μ(z − λ) = F_{μ+λ}(z)`. The book
prints `exp(−exp(z − μ))`, which is decreasing in `z` and so cannot be a
distribution function; the sign inside is corrected here. The mean `μ + γ` and
Lemma 5.3.2 itself are statements about integrals against the Gumbel density
and are not claimed.
-/

open Finset Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

/-- The Gumbel distribution function with mode `μ` (p. 167, with the sign corrected):
`F_μ(z) = exp(−exp(−(z − μ)))`. -/
noncomputable def gumbelCDF (μ z : ℝ) : ℝ := Real.exp (-Real.exp (-(z - μ)))

/-- Exercise 5.3.2 (p. 167), at the level of distribution functions: if `Z ∼ G(μ)` then
`Z + λ ∼ G(μ + λ)`, since `P{Z + λ ≤ z} = F_μ(z − λ) = F_{μ+λ}(z)`. -/
theorem gumbelCDF_shift (μ lam z : ℝ) : gumbelCDF μ (z - lam) = gumbelCDF (μ + lam) z := by
  unfold gumbelCDF
  congr 3
  ring

/-- The corrected CDF is increasing in `z`, as a distribution function must be. -/
theorem gumbelCDF_monotone (μ : ℝ) : Monotone (gumbelCDF μ) := by
  intro z z' hzz'
  unfold gumbelCDF
  exact Real.exp_le_exp.2 (neg_le_neg (Real.exp_le_exp.2 (by linarith)))

variable {Y A : Type*} [Fintype Y] [Fintype A]

/-- The Gumbel expected value Bellman operator (5.36) on `ℝ^{Y × A}`, for unrestricted actions:
`(Rg)(y, a) = ∑_{y'} ln[∑_{a'} exp(r(y', a') + βg(y', a'))] P(y, a, y')`. -/
noncomputable def gumbelR (r : Y → A → ℝ) (P : Y → A → Y → ℝ) (β : ℝ) (g : Y × A → ℝ) :
    Y × A → ℝ := fun p =>
  ∑ y', Real.log (∑ a', Real.exp (r y' a' + β * g (y', a'))) * P p.1 p.2 y'

/-- The log-sum-exp is order preserving. -/
theorem logSumExp_mono [Nonempty A] {f f' : A → ℝ} (h : ∀ a, f a ≤ f' a) :
    Real.log (∑ a, Real.exp (f a)) ≤ Real.log (∑ a, Real.exp (f' a)) := by
  apply Real.log_le_log
  · exact sum_pos (fun a _ => Real.exp_pos _) univ_nonempty
  · exact sum_le_sum fun a _ => Real.exp_le_exp.2 (h a)

/-- Adding a constant inside the log-sum-exp adds it outside. -/
theorem logSumExp_add_const [Nonempty A] (f : A → ℝ) (c : ℝ) :
    Real.log (∑ a, Real.exp (f a + c)) = Real.log (∑ a, Real.exp (f a)) + c := by
  simp only [Real.exp_add, ← sum_mul]
  rw [Real.log_mul (sum_pos (fun a _ => Real.exp_pos _) univ_nonempty).ne' (Real.exp_pos c).ne',
    Real.log_exp]

/-- The Gumbel operator is order preserving (proof of Proposition 5.3.3). -/
theorem gumbelR_monotone [Nonempty A] (r : Y → A → ℝ) {P : Y → A → Y → ℝ}
    (hP : ∀ y a y', 0 ≤ P y a y') {β : ℝ} (hβ : 0 ≤ β) : Monotone (gumbelR r P β) := by
  intro g g' hgg' p
  unfold gumbelR
  refine sum_le_sum fun y' _ => mul_le_mul_of_nonneg_right ?_ (hP _ _ _)
  exact logSumExp_mono fun a' => add_le_add le_rfl (mul_le_mul_of_nonneg_left (hgg' (y', a')) hβ)

/-- `R(g + c) = Rg + βc` (proof of Proposition 5.3.3). -/
theorem gumbelR_add_const [Nonempty A] (r : Y → A → ℝ) {P : Y → A → Y → ℝ}
    (hP : ∀ y a, ∑ y', P y a y' = 1) (β : ℝ) (g : Y × A → ℝ) (c : ℝ) :
    gumbelR r P β (g + fun _ => c) = gumbelR r P β g + fun _ => β * c := by
  funext p
  simp only [gumbelR, Pi.add_apply]
  have h : ∀ y', Real.log (∑ a', Real.exp (r y' a' + β * (g (y', a') + c))) =
      Real.log (∑ a', Real.exp (r y' a' + β * g (y', a'))) + β * c := by
    intro y'
    rw [← logSumExp_add_const (fun a' => r y' a' + β * g (y', a')) (β * c)]
    congr 1
    exact sum_congr rfl fun a' _ => by ring_nf
  simp only [h, add_mul, sum_add_distrib, ← mul_sum, hP p.1 p.2, mul_one]

/-- **Proposition 5.3.3** (p. 167): the Gumbel operator (5.36) is a contraction of modulus `β` on
`ℝ^{Y × A}`, by Blackwell's condition. -/
theorem isContractionOn_gumbelR [Nonempty A] (r : Y → A → ℝ) {P : Y → A → Y → ℝ}
    (hP0 : ∀ y a y', 0 ≤ P y a y') (hP1 : ∀ y a, ∑ y', P y a y' = 1) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : IsContractionOn (gumbelR r P β) Set.univ β :=
  isContractionOn_of_blackwell hβ0 hβ1 (gumbelR_monotone r hP0 hβ0) fun g c _ =>
    (gumbelR_add_const r hP1 β g c).le

end SargentStachurski.MarkovDecisionProcesses

set_option linter.style.longLine false
#print axioms SargentStachurski.MarkovDecisionProcesses.IsMarkov
#print axioms SargentStachurski.MarkovDecisionProcesses.IsMarkov.mk
#print axioms SargentStachurski.MarkovDecisionProcesses.IsMarkov.nonneg
#print axioms SargentStachurski.MarkovDecisionProcesses.IsMarkov.rowsum
#print axioms SargentStachurski.MarkovDecisionProcesses.IsDistribution
#print axioms SargentStachurski.MarkovDecisionProcesses.IsDistribution.mk
#print axioms SargentStachurski.MarkovDecisionProcesses.IsDistribution.nonneg
#print axioms SargentStachurski.MarkovDecisionProcesses.IsDistribution.sum_eq_one
#print axioms SargentStachurski.MarkovDecisionProcesses.mulVec_apply_eq
#print axioms SargentStachurski.MarkovDecisionProcesses.IsMarkov.mul
#print axioms SargentStachurski.MarkovDecisionProcesses.IsMarkov.pow
#print axioms SargentStachurski.MarkovDecisionProcesses.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.MarkovDecisionProcesses.IsMarkov.mulVec_const
#print axioms SargentStachurski.MarkovDecisionProcesses.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.MarkovDecisionProcesses.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.MarkovDecisionProcesses.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.MarkovDecisionProcesses.GloballyStable
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn.mk
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn.mapsTo
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn.nonneg
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn.lt_one
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn.iterate_mem
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.MarkovDecisionProcesses.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.MarkovDecisionProcesses.fixedPt_le_of_le
#print axioms SargentStachurski.MarkovDecisionProcesses.le_fixedPt_of_le_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.isContractionOn_of_blackwell
#print axioms SargentStachurski.MarkovDecisionProcesses.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.mk
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Γ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Γ_nonempty
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.β
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.β_pos
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.β_lt_one
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.r
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.P
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.P_nonneg
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.P_rowsum
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Feasible
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.IsFeasible
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Policy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.defaultPolicy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.policy_nonempty
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isDistribution_P
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Pσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Pσ_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isMarkov_Pσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.rσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.B
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Tσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Tσ_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Tσ_eq
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Tσ_monotone
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.abs_Tσ_sub_le
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isContractionOn_Tσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.vσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isFixedPt_vσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.eq_vσ_of_isFixedPt
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.tendsto_iterate_Tσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.vσ_eq
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.norm_smul_Pσ_mulVec_le
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isUnit_one_sub_smul_Pσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.vσ_eq_inv
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.norm_pow_smul_mulVec_le
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.summable_pow_smul_mulVec
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.iterate_Tσ_eq
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.iterate_Tσ_zero
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.vσ_eq_tsum
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.abs_vσ_le
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.T
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.T_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.B_le_T
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Tσ_le_T
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.B_mono
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.T_monotone
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.abs_B_sub_le
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isContractionOn_T
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.IsGreedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.greedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.greedy_mem
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isGreedy_greedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.greedyPolicy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isGreedy_iff_Tσ_eq_T
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Tσ_eq_T_of_isGreedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.T_apply_eq_sup'
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isGreatest_T
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.antiGreedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.antiGreedy_mem
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isLeast_Tσ_antiGreedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.vstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.vσ_le_vstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.IsOptimal
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isFixedPt_T_vstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.eq_vstar_of_isFixedPt
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.bellman_equation
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.tendsto_iterate_T
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.norm_iterate_T_sub_vstar_le
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.globallyStable_T
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isOptimal_iff
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isOptimal_iff_isGreedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isOptimal_greedy_vstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.exists_isOptimal
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.subgradient_of_isGreedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.newton_step_eq_vσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.vσ_le_vσ_of_isGreedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isOptimal_of_hpi_fixed
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.opi_one_step_eq_vfi
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.tendsto_opi_inner
#print axioms SargentStachurski.MarkovDecisionProcesses.sup'_bool
#print axioms SargentStachurski.MarkovDecisionProcesses.detKernel
#print axioms SargentStachurski.MarkovDecisionProcesses.detKernel_nonneg
#print axioms SargentStachurski.MarkovDecisionProcesses.detKernel_rowsum
#print axioms SargentStachurski.MarkovDecisionProcesses.sum_mul_detKernel
#print axioms SargentStachurski.MarkovDecisionProcesses.renewalKernel
#print axioms SargentStachurski.MarkovDecisionProcesses.renewalKernel_nonneg
#print axioms SargentStachurski.MarkovDecisionProcesses.renewalKernel_rowsum
#print axioms SargentStachurski.MarkovDecisionProcesses.renewal
#print axioms SargentStachurski.MarkovDecisionProcesses.renewal_bellman
#print axioms SargentStachurski.MarkovDecisionProcesses.inventoryNext
#print axioms SargentStachurski.MarkovDecisionProcesses.inventoryNext_of_feasible
#print axioms SargentStachurski.MarkovDecisionProcesses.geomPmf
#print axioms SargentStachurski.MarkovDecisionProcesses.geomPmf_pos
#print axioms SargentStachurski.MarkovDecisionProcesses.summable_geomPmf
#print axioms SargentStachurski.MarkovDecisionProcesses.tsum_geomPmf
#print axioms SargentStachurski.MarkovDecisionProcesses.tsum_geomPmf_tail
#print axioms SargentStachurski.MarkovDecisionProcesses.inventoryKernel
#print axioms SargentStachurski.MarkovDecisionProcesses.summable_inventoryTerm
#print axioms SargentStachurski.MarkovDecisionProcesses.inventoryKernel_nonneg
#print axioms SargentStachurski.MarkovDecisionProcesses.inventoryKernel_rowsum
#print axioms SargentStachurski.MarkovDecisionProcesses.expectedRevenue
#print axioms SargentStachurski.MarkovDecisionProcesses.summable_revenueTerm
#print axioms SargentStachurski.MarkovDecisionProcesses.inventoryReward
#print axioms SargentStachurski.MarkovDecisionProcesses.inventory
#print axioms SargentStachurski.MarkovDecisionProcesses.inventory_mem_Γ
#print axioms SargentStachurski.MarkovDecisionProcesses.inventoryKernel_eq
#print axioms SargentStachurski.MarkovDecisionProcesses.choiceKernel
#print axioms SargentStachurski.MarkovDecisionProcesses.choiceKernel_nonneg
#print axioms SargentStachurski.MarkovDecisionProcesses.choiceKernel_rowsum
#print axioms SargentStachurski.MarkovDecisionProcesses.sum_mul_choiceKernel
#print axioms SargentStachurski.MarkovDecisionProcesses.cakeEating
#print axioms SargentStachurski.MarkovDecisionProcesses.cakeEating_bellman
#print axioms SargentStachurski.MarkovDecisionProcesses.savings
#print axioms SargentStachurski.MarkovDecisionProcesses.savings.mem_Γ
#print axioms SargentStachurski.MarkovDecisionProcesses.savings.T_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.savings.Tσ_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.savings.Pσ_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.savings.rσ_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.investmentReward
#print axioms SargentStachurski.MarkovDecisionProcesses.investmentReward_le_at_Ybar
#print axioms SargentStachurski.MarkovDecisionProcesses.investment
#print axioms SargentStachurski.MarkovDecisionProcesses.investment_T_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.hiringReward
#print axioms SargentStachurski.MarkovDecisionProcesses.hiring
#print axioms SargentStachurski.MarkovDecisionProcesses.hiring_bellman
#print axioms SargentStachurski.MarkovDecisionProcesses.jobSearchKernel
#print axioms SargentStachurski.MarkovDecisionProcesses.jobSearchKernel_nonneg
#print axioms SargentStachurski.MarkovDecisionProcesses.jobSearchKernel_rowsum
#print axioms SargentStachurski.MarkovDecisionProcesses.jobSearch
#print axioms SargentStachurski.MarkovDecisionProcesses.jobSearch.sum_mul_kernel_stay
#print axioms SargentStachurski.MarkovDecisionProcesses.jobSearch.sum_mul_kernel_reject
#print axioms SargentStachurski.MarkovDecisionProcesses.jobSearch.vstar_employed
#print axioms SargentStachurski.MarkovDecisionProcesses.jobSearch.vstar_unemployed
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.E
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.D
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Mop
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.D_E
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.T_eq_Mop_D_E
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.R
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.S
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.R_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.S_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.R_iterate_succ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.R_iterate_succ'
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.S_iterate_succ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.S_iterate_succ'
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.T_iterate_succ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.T_iterate_succ'
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.norm_E_sub_le
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.norm_Mop_sub_le
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.norm_D_sub_le
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isContractionOn_R
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isContractionOn_S
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.norm_T_sub_le
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.E_monotone
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.D_monotone
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Mop_monotone
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.S_monotone
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.R_monotone
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.IsGGreedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.IsQGreedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isGreedy_iff_isGGreedy_E
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isGGreedy_iff_isQGreedy_D
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Mσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Tσ_eq_Mσ_D_E
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Rσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Sσ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Rσ_iterate_succ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Sσ_iterate_succ
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.Rσ_iterate_E
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isGGreedy_E_iff
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.gstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.qstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isFixedPt_R_gstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.eq_gstar_of_isFixedPt
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isFixedPt_S_qstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.eq_qstar_of_isFixedPt
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.vstar_eq_Mop_qstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.gstar_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.qstar_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.vstar_apply_eq_sup'_qstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.tendsto_iterate_R
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.tendsto_iterate_S
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isGreedy_vstar_iff_isGGreedy_gstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isGGreedy_gstar_iff_isQGreedy_qstar
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isOptimal_iff_isGGreedy
#print axioms SargentStachurski.MarkovDecisionProcesses.MDP.isOptimal_iff_isQGreedy
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.mk
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.Γ
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.Γ_nonempty
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.β
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.β_pos
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.β_lt_one
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.r
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.P₀
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.P₀_nonneg
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.P₀_rowsum
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.φ
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.φ_dist
#print axioms SargentStachurski.MarkovDecisionProcesses.liftEV
#print axioms SargentStachurski.MarkovDecisionProcesses.norm_liftEV_sub_le
#print axioms SargentStachurski.MarkovDecisionProcesses.norm_le_norm_liftEV
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.toMDP
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.E_toMDP
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.Ered
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.E_toMDP_eq_lift
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.Rred
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.R_lift
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.Rred_monotone
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.isContractionOn_Rred
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.gred
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.gstar_eq_lift
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.isFixedPt_Rred_gred
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.eq_gred_of_isFixedPt
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.tendsto_iterate_Rred
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.vstar_eq
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.isOptimal_iff
#print axioms SargentStachurski.MarkovDecisionProcesses.Structural.Rσ_lift
#print axioms SargentStachurski.MarkovDecisionProcesses.stochasticReturns
#print axioms SargentStachurski.MarkovDecisionProcesses.stochasticReturns.Ered_apply
#print axioms SargentStachurski.MarkovDecisionProcesses.stochasticReturns.bellman_equation
#print axioms SargentStachurski.MarkovDecisionProcesses.stochasticReturns.gred_eq
#print axioms SargentStachurski.MarkovDecisionProcesses.transientIncome
#print axioms SargentStachurski.MarkovDecisionProcesses.transientIncome.bellman_equation
#print axioms SargentStachurski.MarkovDecisionProcesses.transientIncome.gred_eq
#print axioms SargentStachurski.MarkovDecisionProcesses.gumbelCDF
#print axioms SargentStachurski.MarkovDecisionProcesses.gumbelCDF_shift
#print axioms SargentStachurski.MarkovDecisionProcesses.gumbelCDF_monotone
#print axioms SargentStachurski.MarkovDecisionProcesses.gumbelR
#print axioms SargentStachurski.MarkovDecisionProcesses.logSumExp_mono
#print axioms SargentStachurski.MarkovDecisionProcesses.logSumExp_add_const
#print axioms SargentStachurski.MarkovDecisionProcesses.gumbelR_monotone
#print axioms SargentStachurski.MarkovDecisionProcesses.gumbelR_add_const
#print axioms SargentStachurski.MarkovDecisionProcesses.isContractionOn_gumbelR
