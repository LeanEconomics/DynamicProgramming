import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and monotone operators: the shared vocabulary

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Chapter 4 builds on
Markov matrices (§2.3.1.3), the contraction machinery of §1.2.2, stochastic
dominance and monotone Markov operators (§2.2.4, §3.2.1.3) and the comparison
of fixed points of ordered operators (Proposition 2.2.7). Each chapter project
is self-contained, so these are restated here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

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

/-- The increasing functions on a preordered set form a closed subset of `ℝ^X`
(Vol. 1, Ex 2.2.30). -/
theorem isClosed_monotone (Y : Type*) [Preorder Y] : IsClosed {h : Y → ℝ | Monotone h} := by
  have : {h : Y → ℝ | Monotone h} = ⋂ (p : Y) (q : Y) (_ : p ≤ q), {h : Y → ℝ | h p ≤ h q} := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun hm p q hpq => hm hpq, fun hm p q hpq => hm p q hpq⟩
  rw [this]
  exact isClosed_iInter fun p => isClosed_iInter fun q => isClosed_iInter fun _ =>
    isClosed_le (continuous_apply p) (continuous_apply q)

/-! ### Monotone Markov operators (Vol. 1, §3.2.1.3) -/

variable [PartialOrder X]

/-- First-order stochastic dominance (Vol. 1, (2.9)). -/
def FOSD (φ ψ : X → ℝ) : Prop := ∀ u : X → ℝ, Monotone u → ∑ x, u x * φ x ≤ ∑ x, u x * ψ x

/-- A monotone increasing Markov operator (Vol. 1, p. 93): `x ≤ y ⇒ P(x, ·) ≼_F P(y, ·)`. -/
def MonotoneIncreasing (P : Matrix X X ℝ) : Prop := ∀ x y, x ≤ y → FOSD (P x) (P y)

/-- Vol. 1, Ex 3.2.4: `P` is monotone increasing iff it maps increasing functions to increasing
functions. -/
theorem monotoneIncreasing_iff (P : Matrix X X ℝ) :
    MonotoneIncreasing P ↔ ∀ h : X → ℝ, Monotone h → Monotone (P *ᵥ h) := by
  constructor
  · intro hP h hh x y hxy
    rw [mulVec_apply_eq, mulVec_apply_eq]
    exact hP x y hxy h hh
  · intro hP x y hxy u hu
    have := hP u hu hxy
    rwa [mulVec_apply_eq, mulVec_apply_eq] at this

end SargentStachurski.OptimalStopping

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal stopping problems, policies and lifetime values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.1.1–§4.1.1.3
(pp. 105–108).

An optimal stopping problem is `S = (β, P, c, e)`: a discount factor
`β ∈ (0, 1)`, a Markov matrix `P`, a continuation reward `c` and an exit reward
`e`. A policy `σ : X → {0, 1}` says where to stop. The `σ`-value function `v_σ`
solves `v_σ = r_σ + L_σ v_σ`, (4.2)–(4.3), where `r_σ = σe + (1 − σ)c` and
`L_σ = β(1 − σ)P`; it is the unique fixed point of the policy operator `T_σ`
of (4.5), which is order preserving (Exercise 4.1.2) and a contraction of
modulus `β` in the supremum norm (Proposition 4.1.1, Exercise 4.1.3). Hence
`v_σ = (I − L_σ)⁻¹ r_σ = ∑ₜ L_σᵗ r_σ`, (4.4); Exercise 4.1.1, that
`ρ(L_σ) < 1`, is in `SpectralRadius`.

Examples 4.1.1 (IID job search) and 4.1.2 (a perpetual American call) are
constructed as stopping problems.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

/-- An optimal stopping problem `S = (β, P, c, e)` on the finite state space `X` (p. 106). -/
structure StoppingProblem (X : Type*) [Fintype X] where
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  P : Matrix X X ℝ
  P_markov : IsMarkov P
  c : X → ℝ
  e : X → ℝ

/-- A policy (p. 106): `true` means stop, `false` means continue. -/
abbrev Policy (X : Type*) := X → Bool

namespace StoppingProblem

variable {X : Type*} [Fintype X] (S : StoppingProblem X)

/-- The continuation payoff `c(x) + β ∑ v(x')P(x, x')` given a value function `v`. -/
def cont (v : X → ℝ) : X → ℝ := fun x => S.c x + S.β * (S.P *ᵥ v) x

theorem cont_apply (v : X → ℝ) (x : X) : S.cont v x = S.c x + S.β * ∑ x', v x' * S.P x x' := by
  rw [cont, mulVec_apply_eq]

/-- `r_σ = σe + (1 − σ)c` (p. 107). -/
def r (σ : Policy X) : X → ℝ := fun x => if σ x then S.e x else S.c x

/-- `L_σ(x, x') = β(1 − σ(x))P(x, x')` (p. 107). -/
def L (σ : Policy X) : Matrix X X ℝ := Matrix.of fun x x' => if σ x then 0 else S.β * S.P x x'

theorem L_apply (σ : Policy X) (x x' : X) :
    S.L σ x x' = if σ x then 0 else S.β * S.P x x' := rfl

/-- The policy operator (4.5): `(T_σ v)(x) = σ(x)e(x) + (1 − σ(x))[c(x) + β ∑ v(x')P(x, x')]`. -/
def Tσ (σ : Policy X) (v : X → ℝ) : X → ℝ := fun x => if σ x then S.e x else S.cont v x

/-- `T_σ v = r_σ + L_σ v` (p. 108). -/
theorem Tσ_eq (σ : Policy X) (v : X → ℝ) : S.Tσ σ v = S.r σ + S.L σ *ᵥ v := by
  funext x
  simp only [Tσ, r, L, cont, Pi.add_apply, mulVec, dotProduct, Matrix.of_apply]
  by_cases h : σ x
  · simp [h]
  · simp only [h, Bool.false_eq_true, ite_false, mul_sum]
    congr 1
    exact sum_congr rfl fun x' _ => by ring

/-- Exercise 4.1.2 (p. 108): `T_σ` is order preserving. -/
theorem Tσ_monotone (σ : Policy X) : Monotone (S.Tσ σ) := by
  intro v v' hvv' x
  unfold Tσ cont
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (S.P_markov.mulVec_le_mulVec hvv' x)
      S.β_pos.le)

/-- `|(T_σ v)(x) − (T_σ v')(x)| ≤ β‖v − v'‖`. -/
theorem abs_Tσ_sub_le (σ : Policy X) (v v' : X → ℝ) (x : X) :
    |S.Tσ σ v x - S.Tσ σ v' x| ≤ S.β * ‖v - v'‖ := by
  unfold Tσ cont
  split_ifs
  · simp only [sub_self, abs_zero]
    exact mul_nonneg S.β_pos.le (norm_nonneg _)
  · rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.β_pos.le]
    exact mul_le_mul_of_nonneg_left (S.P_markov.abs_mulVec_sub_le v v' x) S.β_pos.le

/-- **Proposition 4.1.1** (p. 108, Exercise 4.1.3): `T_σ` is a contraction of modulus `β` on `ℝ^X`
under the supremum norm. -/
theorem isContractionOn_Tσ (σ : Policy X) : IsContractionOn (S.Tσ σ) Set.univ S.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := S.β_pos.le
  lt_one := S.β_lt_one
  norm_sub_le v _ v' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg S.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact S.abs_Tσ_sub_le σ v v' x

/-- The `σ`-value function `v_σ` (p. 107): the unique fixed point of `T_σ`. -/
noncomputable def vσ (σ : Policy X) : X → ℝ :=
  Classical.choose ((S.isContractionOn_Tσ σ).exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩)

theorem isFixedPt_vσ (σ : Policy X) : IsFixedPt (S.Tσ σ) (S.vσ σ) :=
  (Classical.choose_spec
    ((S.isContractionOn_Tσ σ).exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩)).2

/-- `v_σ` is the only fixed point of `T_σ` in `ℝ^X` (p. 108). -/
theorem eq_vσ_of_isFixedPt (σ : Policy X) {v : X → ℝ} (hv : IsFixedPt (S.Tσ σ) v) : v = S.vσ σ :=
  (S.isContractionOn_Tσ σ).fixedPt_unique (Set.mem_univ v) (Set.mem_univ _) hv (S.isFixedPt_vσ σ)

/-- Iterates of `T_σ` converge to `v_σ` from any `v` (p. 108). -/
theorem tendsto_iterate_Tσ (σ : Policy X) (v : X → ℝ) :
    Tendsto (fun k : ℕ => (S.Tσ σ)^[k] v) atTop (𝓝 (S.vσ σ)) :=
  (S.isContractionOn_Tσ σ).tendsto_iterate_fixedPt (Set.mem_univ v) (Set.mem_univ _)
    (S.isFixedPt_vσ σ)

/-- (4.2), p. 107: `v_σ(x) = σ(x)e(x) + (1 − σ(x))[c(x) + β ∑ v_σ(x')P(x, x')]`. -/
theorem vσ_eq (σ : Policy X) (x : X) :
    S.vσ σ x = if σ x then S.e x else S.c x + S.β * ∑ x', S.vσ σ x' * S.P x x' := by
  have := congrFun (S.isFixedPt_vσ σ).eq x
  rw [← this, Tσ, cont_apply]

/-- Stopping states: `v_σ(x) = e(x)`. -/
theorem vσ_of_stop (σ : Policy X) {x : X} (hx : σ x = true) : S.vσ σ x = S.e x := by
  rw [vσ_eq, hx]
  simp

/-- (4.3), p. 107: at continuation states, `v_σ(x) = c(x) + β ∑ v_σ(x')P(x, x')`. -/
theorem vσ_of_continue (σ : Policy X) {x : X} (hx : σ x = false) :
    S.vσ σ x = S.c x + S.β * ∑ x', S.vσ σ x' * S.P x x' := by
  rw [vσ_eq, hx]
  simp

/-- `v_σ = r_σ + L_σ v_σ`, the matrix form of (4.2). -/
theorem vσ_eq_r_add (σ : Policy X) : S.vσ σ = S.r σ + S.L σ *ᵥ S.vσ σ := by
  rw [← Tσ_eq]
  exact (S.isFixedPt_vσ σ).eq.symm

/-! ### The matrix `L_σ` and the formula (4.4) -/

theorem L_nonneg (σ : Policy X) (x x' : X) : 0 ≤ S.L σ x x' := by
  rw [L_apply]
  split_ifs
  · exact le_rfl
  · exact mul_nonneg S.β_pos.le (S.P_markov.nonneg x x')

/-- Each row of `L_σ` sums to `β(1 − σ(x)) ≤ β`. -/
theorem L_rowsum_le (σ : Policy X) (x : X) : ∑ x', S.L σ x x' ≤ S.β := by
  simp only [L_apply]
  split_ifs
  · simp only [sum_const_zero]
    exact S.β_pos.le
  · rw [← mul_sum, S.P_markov.rowsum, mul_one]

/-- `|(L_σ u)(x)| ≤ β‖u‖`. -/
theorem abs_L_mulVec_le (σ : Policy X) (u : X → ℝ) (x : X) : |(S.L σ *ᵥ u) x| ≤ S.β * ‖u‖ := by
  have h : (S.L σ *ᵥ u) x = if σ x then 0 else S.β * (S.P *ᵥ u) x := by
    simp only [mulVec, dotProduct, L_apply]
    split_ifs
    · simp
    · rw [mul_sum]
      exact sum_congr rfl fun x' _ => by ring
  rw [h]
  split_ifs
  · simp only [abs_zero]
    exact mul_nonneg S.β_pos.le (norm_nonneg _)
  · rw [abs_mul, abs_of_nonneg S.β_pos.le]
    exact mul_le_mul_of_nonneg_left (S.P_markov.abs_mulVec_le u x) S.β_pos.le

/-- `‖L_σ u‖ ≤ β‖u‖`. -/
theorem norm_L_mulVec_le (σ : Policy X) (u : X → ℝ) : ‖S.L σ *ᵥ u‖ ≤ S.β * ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg S.β_pos.le (norm_nonneg _))]
  intro x
  rw [Real.norm_eq_abs]
  exact S.abs_L_mulVec_le σ u x

/-- `‖L_σᵗ u‖ ≤ βᵗ‖u‖`. -/
theorem norm_L_pow_mulVec_le [DecidableEq X] (σ : Policy X) (u : X → ℝ) (t : ℕ) :
    ‖S.L σ ^ t *ᵥ u‖ ≤ S.β ^ t * ‖u‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec]
    calc ‖S.L σ *ᵥ (S.L σ ^ t *ᵥ u)‖ ≤ S.β * ‖S.L σ ^ t *ᵥ u‖ := S.norm_L_mulVec_le σ _
      _ ≤ S.β * (S.β ^ t * ‖u‖) := mul_le_mul_of_nonneg_left ih S.β_pos.le
      _ = S.β ^ (t + 1) * ‖u‖ := by ring

/-- `I − L_σ` is invertible: `u = L_σ u` forces `‖u‖ ≤ β‖u‖`, so `u = 0`. This is the conclusion
the book draws from Exercise 4.1.1 and the Neumann series lemma (p. 107). -/
theorem isUnit_one_sub_L [DecidableEq X] (σ : Policy X) : IsUnit (1 - S.L σ) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  have hd : (1 - S.L σ) *ᵥ (u - v) = 0 := by
    rw [mulVec_sub]
    exact sub_eq_zero.2 huv
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at hd
  have hnorm : ‖u - v‖ ≤ S.β * ‖u - v‖ := by
    calc ‖u - v‖ = ‖S.L σ *ᵥ (u - v)‖ := by rw [← hd]
      _ ≤ S.β * ‖u - v‖ := S.norm_L_mulVec_le σ _
  have : ‖u - v‖ ≤ 0 := by nlinarith [norm_nonneg (u - v), S.β_lt_one]
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this (norm_nonneg _)))

/-- (4.4), p. 107: `v_σ = (I − L_σ)⁻¹ r_σ`. -/
theorem vσ_eq_inv [DecidableEq X] (σ : Policy X) : S.vσ σ = (1 - S.L σ)⁻¹ *ᵥ S.r σ := by
  have hunit := S.isUnit_one_sub_L σ
  have h1 : (1 - S.L σ) *ᵥ S.vσ σ = S.r σ := by
    rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add]
    exact S.vσ_eq_r_add σ
  calc S.vσ σ = (1 - S.L σ)⁻¹ *ᵥ ((1 - S.L σ) *ᵥ S.vσ σ) := by
        rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
          one_mulVec]
    _ = (1 - S.L σ)⁻¹ *ᵥ S.r σ := by rw [h1]

/-- The Neumann series for `v_σ`: `∑ₜ L_σᵗ r_σ` converges. -/
theorem summable_L_pow_mulVec [DecidableEq X] (σ : Policy X) :
    Summable fun t : ℕ => S.L σ ^ t *ᵥ S.r σ :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one S.β_pos.le S.β_lt_one).mul_right
    ‖S.r σ‖) (S.norm_L_pow_mulVec_le σ _)

/-- (4.4) as a series: `v_σ = ∑ₜ L_σᵗ r_σ`, the Neumann series of the book's argument (p. 107). -/
theorem vσ_eq_tsum [DecidableEq X] (σ : Policy X) : S.vσ σ = ∑' t : ℕ, S.L σ ^ t *ᵥ S.r σ := by
  have hs := S.summable_L_pow_mulVec σ
  have hs' : Summable fun t : ℕ => S.L σ ^ (t + 1) *ᵥ S.r σ := (summable_nat_add_iff 1).2 hs
  -- the series is a fixed point of `T_σ`
  have hfix : IsFixedPt (S.Tσ σ) (∑' t : ℕ, S.L σ ^ t *ᵥ S.r σ) := by
    rw [IsFixedPt, Tσ_eq]
    let M := LinearMap.toContinuousLinearMap (Matrix.mulVecLin (S.L σ))
    have hM : ∀ u, M u = S.L σ *ᵥ u := fun u => rfl
    rw [← hM, M.map_tsum hs]
    simp only [hM, mulVec_mulVec, ← pow_succ']
    rw [hs.tsum_eq_zero_add]
    simp
  exact (S.eq_vσ_of_isFixedPt σ hfix).symm

/-! ### Examples 4.1.1 and 4.1.2 -/

/-- Example 4.1.1 (p. 106): IID job search as a stopping problem. Every row of `P` is the offer
distribution `φ`, the exit reward is `w/(1 − β)` and the continuation reward is unemployment
compensation `c`. -/
noncomputable def iidJobSearch {W : Type*} [Fintype W] (wage : W → ℝ) {φ : W → ℝ}
    (hφ : IsDistribution φ) (c : ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : StoppingProblem W where
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  P := Matrix.of fun _ w' => φ w'
  P_markov := ⟨fun _ w' => hφ.nonneg w', fun _ => hφ.sum_eq_one⟩
  c := fun _ => c
  e := fun w => wage w / (1 - β)

/-- Example 4.1.2 (p. 106): a perpetual American call option on an asset with price `s(Xₜ)`,
strike `K` and interest rate `r > 0`: discount factor `1/(1 + r)`, exit reward `s(x) − K`,
continuation reward zero. -/
noncomputable def perpetualOption {Q : Matrix X X ℝ} (hQ : IsMarkov Q) (s : X → ℝ) (K : ℝ)
    {r : ℝ} (hr : 0 < r) : StoppingProblem X where
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  P := Q
  P_markov := hQ
  c := fun _ => 0
  e := fun x => s x - K

end StoppingProblem

end SargentStachurski.OptimalStopping

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral radius of `L_σ`

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Exercise 4.1.1
(p. 107): `ρ(L_σ) < 1` for every policy `σ` of an optimal stopping problem.

The spectral radius of a real matrix is defined, as in Vol. 1 (1.15), as the
largest modulus of a complex eigenvalue, through Mathlib's `spectralRadius` of
the complexified matrix, and it is bounded by the ℓ∞ operator norm, which is
the largest absolute row sum. Since `L_σ = β(1 − σ)P ≥ 0` has row sums at most
`β`, `ρ(L_σ) ≤ ‖L_σ‖ ≤ β < 1`.
-/

open Finset Matrix

namespace SargentStachurski.OptimalStopping

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The complexification of a real matrix. -/
def complexify (A : Matrix X X ℝ) : Matrix X X ℂ := A.map Complex.ofReal

omit [Fintype X] [DecidableEq X] in
theorem complexify_apply (A : Matrix X X ℝ) (i j : X) : complexify A i j = (A i j : ℂ) := rfl

theorem nnnorm_complexify (A : Matrix X X ℝ) : ‖complexify A‖₊ = ‖A‖₊ := by
  simp only [Matrix.linfty_opNNNorm_def, complexify_apply, Complex.nnnorm_real]

theorem norm_complexify (A : Matrix X X ℝ) : ‖complexify A‖ = ‖A‖ :=
  congrArg NNReal.toReal (nnnorm_complexify A)

/-- The spectral radius (Vol. 1, (1.15)): the largest modulus of a complex eigenvalue. -/
noncomputable def specRad (A : Matrix X X ℝ) : ℝ := (spectralRadius ℂ (complexify A)).toReal

/-- The ℓ∞ operator norm is bounded by a bound on the row sums of absolute values. -/
theorem norm_le_of_rowsum_abs_le (A : Matrix X X ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, |A i j| ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have : (univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ c.toNNReal := by
    refine Finset.sup_le fun i _ => ?_
    have hi := h i
    exact (NNReal.coe_le_coe (r₁ := ∑ j, ‖A i j‖₊) (r₂ := c.toNNReal)).1
      (by simpa [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal c hc] using hi)
  have h2 := NNReal.coe_le_coe.2 this
  rwa [Real.coe_toNNReal c hc] at h2

/-- `ρ(A) ≤ ‖A‖` (Vol. 1, Lemma 1.2.2 for `k = 1`), for a nonempty state space. -/
theorem specRad_le_norm [Nonempty X] (A : Matrix X X ℝ) : specRad A ≤ ‖A‖ := by
  have := ENNReal.toReal_mono ENNReal.coe_ne_top
    (spectralRadius_le_nnnorm (𝕜 := ℂ) (complexify A))
  rwa [ENNReal.coe_toReal, coe_nnnorm, norm_complexify] at this

namespace StoppingProblem

variable (S : StoppingProblem X)

/-- `‖L_σ‖ ≤ β`: the rows of `L_σ ≥ 0` sum to at most `β`. -/
theorem norm_L_le (σ : Policy X) : ‖S.L σ‖ ≤ S.β :=
  norm_le_of_rowsum_abs_le _ S.β_pos.le fun x => by
    have : ∑ x', |S.L σ x x'| = ∑ x', S.L σ x x' :=
      sum_congr rfl fun x' _ => abs_of_nonneg (S.L_nonneg σ x x')
    rw [this]
    exact S.L_rowsum_le σ x

omit [DecidableEq X] in
/-- Exercise 4.1.1 (p. 107): `ρ(L_σ) < 1` for every policy `σ`. -/
theorem specRad_L_lt_one [Nonempty X] (σ : Policy X) : specRad (S.L σ) < 1 := by
  classical
  exact ((specRad_le_norm _).trans (S.norm_L_le σ)).trans_lt S.β_lt_one

end StoppingProblem

end SargentStachurski.OptimalStopping

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The value function, the Bellman operator and optimal policies

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.1.4–§4.1.1.7
(pp. 108–111).

The value function is `v* = ⋁_σ v_σ`, (4.6), the pointwise maximum over the
finitely many policies. The Bellman operator `Tv = e ∨ (c + βPv)`, (4.8), is an
order-preserving self-map (Exercise 4.1.4) and a contraction of modulus `β`
(Proposition 4.1.2 (i), Exercise 4.1.5); its unique fixed point is `v*`
(Proposition 4.1.2 (ii)), so `v*` is the unique solution of the Bellman
equation (4.7) and value function iteration converges to it. A policy is
optimal, (4.1), iff it is `v*`-greedy, (4.9) (Proposition 4.1.3, which the book
proves in Chapter 5 in a general setting; the proof here is direct).
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

namespace StoppingProblem

variable {X : Type*} [Fintype X] (S : StoppingProblem X)

/-- The Bellman operator (4.8): `(Tv)(x) = max{e(x), c(x) + β ∑ v(x')P(x, x')}`. -/
def T (v : X → ℝ) : X → ℝ := fun x => max (S.e x) (S.cont v x)

theorem T_apply (v : X → ℝ) (x : X) :
    S.T v x = max (S.e x) (S.c x + S.β * ∑ x', v x' * S.P x x') := by
  rw [T, cont_apply]

/-- Exercise 4.1.4 (p. 109): `T` is an order-preserving self-map on `ℝ^X`. -/
theorem T_monotone : Monotone S.T := by
  intro v v' hvv' x
  exact max_le_max le_rfl (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (S.P_markov.mulVec_le_mulVec hvv' x) S.β_pos.le))

/-- `|(Tv)(x) − (Tv')(x)| ≤ β‖v − v'‖`, by `|α ∨ x − α ∨ y| ≤ |x − y|`. -/
theorem abs_T_sub_le (v v' : X → ℝ) (x : X) : |S.T v x - S.T v' x| ≤ S.β * ‖v - v'‖ := by
  unfold T cont
  rw [max_comm (S.e x), max_comm (S.e x)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.β_pos.le]
  exact mul_le_mul_of_nonneg_left (S.P_markov.abs_mulVec_sub_le v v' x) S.β_pos.le

/-- **Proposition 4.1.2 (i)** (p. 109, Exercise 4.1.5): `T` is a contraction of modulus `β` on
`ℝ^X` under the supremum norm. -/
theorem isContractionOn_T : IsContractionOn S.T Set.univ S.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := S.β_pos.le
  lt_one := S.β_lt_one
  norm_sub_le v _ v' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg S.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact S.abs_T_sub_le v v' x

/-- `T_σ v ≤ Tv` for every policy `σ` and every `v` (p. 110). -/
theorem Tσ_le_T (σ : Policy X) (v : X → ℝ) : S.Tσ σ v ≤ S.T v := by
  intro x
  unfold Tσ T
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- A `v`-greedy policy (4.9), p. 110: `σ(x)` maximises `a e(x) + (1 − a)[c(x) + β(Pv)(x)]` over
`a ∈ {0, 1}`: stopping is chosen only if `e(x) ≥ c(x) + β(Pv)(x)`, continuing only if `≤`. -/
def IsGreedy (v : X → ℝ) (σ : Policy X) : Prop :=
  ∀ x, (σ x = true → S.cont v x ≤ S.e x) ∧ (σ x = false → S.e x ≤ S.cont v x)

/-- The greedy policy that stops on ties: `σ(x) = 1{e(x) ≥ c(x) + β(Pv)(x)}`. -/
noncomputable def greedy (v : X → ℝ) : Policy X := fun x => decide (S.cont v x ≤ S.e x)

theorem isGreedy_greedy (v : X → ℝ) : S.IsGreedy v (S.greedy v) := fun x => by
  simp only [greedy, decide_eq_true_iff, decide_eq_false_iff_not]
  exact ⟨id, fun h => (not_le.1 h).le⟩

/-- For a `v`-greedy `σ`, `T_σ v = Tv` (p. 110). -/
theorem Tσ_eq_T_of_isGreedy {v : X → ℝ} {σ : Policy X} (hσ : S.IsGreedy v σ) :
    S.Tσ σ v = S.T v := by
  funext x
  unfold Tσ T
  rcases Bool.eq_false_or_eq_true (σ x) with h | h
  · simp only [h, ↓reduceIte]
    exact (max_eq_left ((hσ x).1 h)).symm
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right ((hσ x).2 h)).symm

variable [DecidableEq X]

/-- The value function (4.6), p. 108: `v*(x) = max_σ v_σ(x)`. -/
noncomputable def vstar : X → ℝ := fun x => univ.sup' univ_nonempty fun σ : Policy X => S.vσ σ x

/-- `v_σ ≤ v*` for every policy. -/
theorem vσ_le_vstar (σ : Policy X) : S.vσ σ ≤ S.vstar := fun x =>
  Finset.le_sup' (fun σ : Policy X => S.vσ σ x) (mem_univ σ)

/-- `v*(x)` is attained by some policy. -/
theorem exists_vσ_eq_vstar (x : X) : ∃ σ : Policy X, S.vσ σ x = S.vstar x := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_sup' univ_nonempty fun σ : Policy X => S.vσ σ x
  exact ⟨σ, hσ.symm⟩

/-- **Proposition 4.1.2 (ii)** (p. 109): the value function `v*` is a fixed point of `T`. -/
theorem isFixedPt_T_vstar : IsFixedPt S.T S.vstar := by
  -- the fixed point `v̄` of `T` given by Banach's theorem
  obtain ⟨vbar, -, hvbar⟩ := S.isContractionOn_T.exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩
  -- `v̄ ≤ v*`: `v̄` is the value of its own greedy policy
  have h1 : vbar ≤ S.vstar := by
    have hfix : IsFixedPt (S.Tσ (S.greedy vbar)) vbar := by
      rw [IsFixedPt, S.Tσ_eq_T_of_isGreedy (S.isGreedy_greedy vbar)]
      exact hvbar
    rw [S.eq_vσ_of_isFixedPt _ hfix]
    exact S.vσ_le_vstar _
  -- `v* ≤ v̄`: each `v_σ ≤ v̄` by Proposition 2.2.7, since `T_σ ≤ T`
  have h2 : S.vstar ≤ vbar := by
    intro x
    refine Finset.sup'_le _ _ fun σ _ => ?_
    exact fixedPt_le_of_le (S.Tσ_le_T σ) S.T_monotone (S.isFixedPt_vσ σ)
      (S.isContractionOn_T.tendsto_iterate_fixedPt (Set.mem_univ _) (Set.mem_univ _) hvbar) x
  have : S.vstar = vbar := le_antisymm h2 h1
  rw [this]
  exact hvbar

/-- Proposition 4.1.2 (ii): `v*` is the only fixed point of `T` in `ℝ^X`. -/
theorem eq_vstar_of_isFixedPt {v : X → ℝ} (hv : IsFixedPt S.T v) : v = S.vstar :=
  S.isContractionOn_T.fixedPt_unique (Set.mem_univ v) (Set.mem_univ _) hv S.isFixedPt_T_vstar

/-- The Bellman equation (4.7), p. 109: `v*(x) = max{e(x), c(x) + β ∑ v*(x')P(x, x')}`, with `v*`
its unique solution. -/
theorem bellman_equation (x : X) :
    S.vstar x = max (S.e x) (S.c x + S.β * ∑ x', S.vstar x' * S.P x x') := by
  have := congrFun S.isFixedPt_T_vstar.eq x
  rw [← this, T_apply]

/-- Value function iteration (§4.1.1.7, p. 111): `Tᵏv → v*` from every `v ∈ ℝ^X`, at rate `βᵏ`. -/
theorem tendsto_iterate_T (v : X → ℝ) : Tendsto (fun k : ℕ => S.T^[k] v) atTop (𝓝 S.vstar) :=
  S.isContractionOn_T.tendsto_iterate_fixedPt (Set.mem_univ v) (Set.mem_univ _) S.isFixedPt_T_vstar

theorem norm_iterate_T_sub_vstar_le (v : X → ℝ) (k : ℕ) :
    ‖S.T^[k] v - S.vstar‖ ≤ S.β ^ k * ‖v - S.vstar‖ :=
  S.isContractionOn_T.norm_iterate_sub_fixedPt_le (Set.mem_univ v) (Set.mem_univ _)
    S.isFixedPt_T_vstar k

omit [DecidableEq X] in
/-- `T` is globally stable on `ℝ^X` (p. 110). -/
theorem globallyStable_T : GloballyStable S.T := S.isContractionOn_T.globallyStable_univ

/-! ### Optimal policies (§4.1.1.6) -/

/-- An optimal policy (4.1), p. 107: `v_σ*(x) = max_σ v_σ(x)` for all `x`. -/
def IsOptimal (σ : Policy X) : Prop := ∀ (σ' : Policy X) (x : X), S.vσ σ' x ≤ S.vσ σ x

/-- `σ` is optimal iff `v_σ = v*`. -/
theorem isOptimal_iff_vσ_eq (σ : Policy X) : S.IsOptimal σ ↔ S.vσ σ = S.vstar := by
  constructor
  · intro h
    funext x
    refine le_antisymm (S.vσ_le_vstar σ x) ?_
    exact Finset.sup'_le _ _ fun σ' _ => h σ' x
  · intro h σ' x
    rw [h]
    exact S.vσ_le_vstar σ' x

/-- **Proposition 4.1.3** (Bellman's principle of optimality, p. 110): a policy is optimal iff it is
`v*`-greedy. -/
theorem isOptimal_iff_isGreedy (σ : Policy X) : S.IsOptimal σ ↔ S.IsGreedy S.vstar σ := by
  rw [isOptimal_iff_vσ_eq]
  constructor
  · intro h x
    -- `v* = T_σ v*` pointwise, and `v* = T v*`
    have h1 : S.vstar x = S.Tσ σ S.vstar x := by
      rw [← h]
      exact (congrFun (S.isFixedPt_vσ σ).eq x).symm
    have h2 : S.vstar x = max (S.e x) (S.cont S.vstar x) := (congrFun S.isFixedPt_T_vstar.eq x).symm
    constructor
    · intro hσ
      have h1' : S.vstar x = S.e x := by
        rw [h1, Tσ]
        simp [hσ]
      exact max_eq_left_iff.1 (h1'.symm.trans h2).symm
    · intro hσ
      have h1' : S.vstar x = S.cont S.vstar x := by
        rw [h1, Tσ]
        simp [hσ]
      exact max_eq_right_iff.1 (h1'.symm.trans h2).symm
  · intro h
    have hfix : IsFixedPt (S.Tσ σ) S.vstar := by
      rw [IsFixedPt, S.Tσ_eq_T_of_isGreedy h]
      exact S.isFixedPt_T_vstar
    exact (S.eq_vσ_of_isFixedPt σ hfix).symm

/-- An optimal policy exists: the `v*`-greedy policy that stops on ties. -/
theorem isOptimal_greedy_vstar : S.IsOptimal (S.greedy S.vstar) :=
  (S.isOptimal_iff_isGreedy _).2 (S.isGreedy_greedy _)

end StoppingProblem

end SargentStachurski.OptimalStopping

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Continuation values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.3.1 (the
definition (4.10)) and §4.1.4.1 (pp. 114, 117–118).

The continuation value function is `h* = c + βPv*`, (4.10); the Bellman
equation becomes `v* = e ∨ h*`, (4.11), and taking expectations gives
`h* = c + βP(e ∨ h*)`, (4.12). The continuation value operator
`Ch = c + βP(e ∨ h)`, (4.13), is a contraction of modulus `β` with unique
fixed point `h*` (Proposition 4.1.5), so `h*` can be computed by successive
approximation and the policy `σ*(x) = 1{e(x) ≥ h*(x)}` is `v*`-greedy, hence
optimal.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

namespace StoppingProblem

variable {X : Type*} [Fintype X] [DecidableEq X] (S : StoppingProblem X)

/-- The continuation value function (4.10), p. 114: `h*(x) = c(x) + β ∑ v*(x')P(x, x')`. -/
noncomputable def hstar : X → ℝ := S.cont S.vstar

theorem hstar_apply (x : X) : S.hstar x = S.c x + S.β * ∑ x', S.vstar x' * S.P x x' :=
  S.cont_apply S.vstar x

/-- (4.11), p. 117: `v* = e ∨ h*`. -/
theorem vstar_eq_max_hstar (x : X) : S.vstar x = max (S.e x) (S.hstar x) :=
  (congrFun S.isFixedPt_T_vstar.eq x).symm

/-- The continuation value operator (4.13), p. 117:
`(Ch)(x) = c(x) + β ∑ max{e(x'), h(x')} P(x, x')`. -/
noncomputable def C (h : X → ℝ) : X → ℝ := S.cont fun x' => max (S.e x') (h x')

omit [DecidableEq X] in
theorem C_apply (h : X → ℝ) (x : X) :
    S.C h x = S.c x + S.β * ∑ x', max (S.e x') (h x') * S.P x x' :=
  S.cont_apply _ x

/-- (4.12), p. 117: `h*(x) = c(x) + β ∑ max{e(x'), h*(x')} P(x, x')`, i.e. `h*` is a fixed point
of `C`. -/
theorem isFixedPt_C_hstar : IsFixedPt S.C S.hstar := by
  change S.C S.hstar = S.hstar
  unfold C hstar
  congr 1
  funext x'
  exact (S.vstar_eq_max_hstar x').symm

omit [DecidableEq X] in
/-- `C` is order preserving. -/
theorem C_monotone : Monotone S.C := by
  intro h h' hhh' x
  unfold C cont
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (S.P_markov.mulVec_le_mulVec
    (fun x' => max_le_max le_rfl (hhh' x')) x) S.β_pos.le)

omit [DecidableEq X] in
/-- `|(Cf)(x) − (Cg)(x)| ≤ β‖f − g‖`, the estimate in the proof of Proposition 4.1.5. -/
theorem abs_C_sub_le (f g : X → ℝ) (x : X) : |S.C f x - S.C g x| ≤ S.β * ‖f - g‖ := by
  unfold C cont
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.β_pos.le]
  refine mul_le_mul_of_nonneg_left ((S.P_markov.abs_mulVec_sub_le _ _ x).trans ?_) S.β_pos.le
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x'
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [max_comm (S.e x') (f x'), max_comm (S.e x') (g x')]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have := norm_le_pi_norm (f - g) x'
  simpa [Real.norm_eq_abs] using this

omit [DecidableEq X] in
/-- **Proposition 4.1.5** (p. 117): `C` is a contraction of modulus `β` on `ℝ^X`. -/
theorem isContractionOn_C : IsContractionOn S.C Set.univ S.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := S.β_pos.le
  lt_one := S.β_lt_one
  norm_sub_le f _ g _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg S.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact S.abs_C_sub_le f g x

/-- Proposition 4.1.5: `h*` is the unique fixed point of `C` in `ℝ^X`. -/
theorem eq_hstar_of_isFixedPt {h : X → ℝ} (hh : IsFixedPt S.C h) : h = S.hstar :=
  S.isContractionOn_C.fixedPt_unique (Set.mem_univ h) (Set.mem_univ _) hh S.isFixedPt_C_hstar

/-- Successive approximation with `C` converges to `h*` from any `h` (p. 117, step (i)). -/
theorem tendsto_iterate_C (h : X → ℝ) : Tendsto (fun k : ℕ => S.C^[k] h) atTop (𝓝 S.hstar) :=
  S.isContractionOn_C.tendsto_iterate_fixedPt (Set.mem_univ h) (Set.mem_univ _) S.isFixedPt_C_hstar

/-- The policy `σ*(x) = 1{e(x) ≥ h*(x)}` of p. 117, step (ii). -/
noncomputable def sigmaStar : Policy X := fun x => decide (S.hstar x ≤ S.e x)

theorem sigmaStar_eq_greedy : S.sigmaStar = S.greedy S.vstar := rfl

/-- `σ*` is `v*`-greedy, hence optimal (Proposition 4.1.3). -/
theorem isGreedy_sigmaStar : S.IsGreedy S.vstar S.sigmaStar := S.isGreedy_greedy S.vstar

theorem isOptimal_sigmaStar : S.IsOptimal S.sigmaStar := S.isOptimal_greedy_vstar

/-- `σ*` stops exactly where the exit reward is at least the continuation value. -/
theorem sigmaStar_eq_true_iff (x : X) : S.sigmaStar x = true ↔ S.hstar x ≤ S.e x := by
  simp [sigmaStar]

end StoppingProblem

end SargentStachurski.OptimalStopping

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monotone values and monotone actions

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.3 (pp. 114–116).

Lemma 4.1.4: if `e` and `c` are increasing and `P` is monotone increasing then
`h*` and `v*` are increasing. The proof is the book's: `T` maps the closed set
of increasing functions into itself, so the fixed point lies in it
(Vol. 1, Ex 1.2.18).

Exercises 4.1.9–4.1.11: the optimal policy `σ* = 1{e ≥ h*}` is decreasing when
`e` is decreasing and `h*` increasing, which holds when `e` is constant, `c`
increasing and `P` monotone increasing; and increasing when `e` is increasing
and `h*` decreasing, as in IID job search (Example 4.1.5), where `h*` is
constant. On a totally ordered state space a monotone binary policy is a
threshold policy (p. 116).
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

namespace StoppingProblem

variable {X : Type*} [Fintype X] [DecidableEq X] (S : StoppingProblem X)

/-! ### Monotone values (§4.1.3.1) -/

variable [PartialOrder X]

omit [DecidableEq X] in
/-- `T` maps increasing functions to increasing functions when `e`, `c` are increasing and `P` is
monotone increasing (the step in the proof of Lemma 4.1.4). -/
theorem monotone_T_of_monotone (he : Monotone S.e) (hc : Monotone S.c)
    (hP : MonotoneIncreasing S.P) {v : X → ℝ} (hv : Monotone v) : Monotone (S.T v) := by
  intro x y hxy
  have h := (monotoneIncreasing_iff S.P).1 hP v hv hxy
  exact max_le_max (he hxy) (add_le_add (hc hxy) (mul_le_mul_of_nonneg_left h S.β_pos.le))

/-- **Lemma 4.1.4** (p. 114): if `e, c ∈ iℝ^X` and `P` is monotone increasing, then `v*` is
increasing. -/
theorem monotone_vstar (he : Monotone S.e) (hc : Monotone S.c) (hP : MonotoneIncreasing S.P) :
    Monotone S.vstar := by
  have hiter : ∀ k : ℕ, Monotone (S.T^[k] 0) := by
    intro k
    induction k with
    | zero => exact fun _ _ _ => le_rfl
    | succ k ih => rw [iterate_succ_apply']; exact S.monotone_T_of_monotone he hc hP ih
  exact (isClosed_monotone X).mem_of_tendsto (S.tendsto_iterate_T 0) (Eventually.of_forall hiter)

/-- Lemma 4.1.4 (p. 114): under the same hypotheses `h* = c + βPv*` is increasing. -/
theorem monotone_hstar (he : Monotone S.e) (hc : Monotone S.c) (hP : MonotoneIncreasing S.P) :
    Monotone S.hstar := by
  intro x y hxy
  have h := (monotoneIncreasing_iff S.P).1 hP S.vstar (S.monotone_vstar he hc hP) hxy
  exact add_le_add (hc hxy) (mul_le_mul_of_nonneg_left h S.β_pos.le)

/-! ### Monotone actions (§4.1.3.2) -/

/-- Exercise 4.1.9 (p. 115): `σ*` is decreasing whenever `e` is decreasing and `h*` is
increasing. Policies are ordered pointwise with `false < true`. -/
theorem antitone_sigmaStar (he : Antitone S.e) (hh : Monotone S.hstar) : Antitone S.sigmaStar := by
  intro x y hxy
  simp only [sigmaStar]
  by_cases hy : S.hstar y ≤ S.e y
  · have hx : S.hstar x ≤ S.e x := (hh hxy).trans (hy.trans (he hxy))
    simp [hx, hy]
  · simp [hy]

/-- Exercise 4.1.10 (p. 115): the conditions of Exercise 4.1.9 hold when `e` is constant, `c` is
increasing and `P` is monotone increasing; so `σ*` is decreasing. -/
theorem antitone_sigmaStar_of_const (he : ∀ x y, S.e x = S.e y) (hc : Monotone S.c)
    (hP : MonotoneIncreasing S.P) : Antitone S.sigmaStar :=
  S.antitone_sigmaStar (fun x y _ => (he y x).le)
    (S.monotone_hstar (fun x y _ => (he x y).le) hc hP)

/-- Exercise 4.1.11 (p. 115): `σ*` is increasing whenever `e` is increasing and `h*` is
decreasing. -/
theorem monotone_sigmaStar (he : Monotone S.e) (hh : Antitone S.hstar) : Monotone S.sigmaStar := by
  intro x y hxy
  simp only [sigmaStar]
  by_cases hx : S.hstar x ≤ S.e x
  · have hy : S.hstar y ≤ S.e y := (hh hxy).trans (hx.trans (he hxy))
    simp [hx, hy]
  · simp [hx]

omit [PartialOrder X] in
/-- When every row of `P` is the same distribution (IID transitions) and `c` is constant, the
continuation value `h*` is constant. -/
theorem hstar_const_of_iid (hP : ∀ x y, S.P x = S.P y) (hc : ∀ x y, S.c x = S.c y) (x y : X) :
    S.hstar x = S.hstar y := by
  simp only [hstar_apply]
  rw [hc x y, hP x y]

/-- Example 4.1.5 (p. 116): in IID job search, `e(w) = w/(1 − β)` is increasing and `h*` is
constant, so `σ*` is increasing: the agent accepts all sufficiently large offers. -/
theorem monotone_sigmaStar_of_iid (he : Monotone S.e) (hP : ∀ x y, S.P x = S.P y)
    (hc : ∀ x y, S.c x = S.c y) : Monotone S.sigmaStar :=
  S.monotone_sigmaStar he fun x y _ => (S.hstar_const_of_iid hP hc y x).le

end StoppingProblem

/-! ### Threshold policies (p. 116) -/

variable {Y : Type*} [Finite Y] [LinearOrder Y]

/-- On a totally ordered finite set, an increasing binary policy that stops somewhere is a
threshold policy: there is `x*` with `σ(x) = 1 ⟺ x ≥ x*` (p. 116). -/
theorem exists_threshold_of_monotone {σ : Policy Y} (hσ : Monotone σ) (hne : ∃ x, σ x = true) :
    ∃ xs : Y, ∀ x, σ x = true ↔ xs ≤ x := by
  classical
  cases nonempty_fintype Y
  have hne' : (univ.filter fun x => σ x = true).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simp [hx]⟩
  refine ⟨(univ.filter fun x => σ x = true).min' hne', fun x => ?_⟩
  constructor
  · intro hx
    exact Finset.min'_le _ _ (by simp [hx])
  · intro hx
    have hmin : σ ((univ.filter fun x => σ x = true).min' hne') = true := by
      have := Finset.min'_mem _ hne'
      simpa using this
    have := hσ hx
    rw [hmin] at this
    rcases Bool.eq_false_or_eq_true (σ x) with h | h
    · exact h
    · rw [h] at this
      exact absurd this (by decide)

/-- A decreasing binary policy that stops somewhere is a threshold policy from below:
`σ(x) = 1 ⟺ x ≤ x*`. -/
theorem exists_threshold_of_antitone {σ : Policy Y} (hσ : Antitone σ) (hne : ∃ x, σ x = true) :
    ∃ xs : Y, ∀ x, σ x = true ↔ x ≤ xs := by
  classical
  cases nonempty_fintype Y
  have hne' : (univ.filter fun x => σ x = true).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simp [hx]⟩
  refine ⟨(univ.filter fun x => σ x = true).max' hne', fun x => ?_⟩
  constructor
  · intro hx
    exact Finset.le_max' _ _ (by simp [hx])
  · intro hx
    have hmax : σ ((univ.filter fun x => σ x = true).max' hne') = true := by
      have := Finset.max'_mem _ hne'
      simpa using this
    have := hσ hx
    rw [hmax] at this
    rcases Bool.eq_false_or_eq_true (σ x) with h | h
    · exact h
    · rw [h] at this
      exact absurd this (by decide)

end SargentStachurski.OptimalStopping

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dimensionality reduction through continuation values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.4.2–§4.1.4.3
(pp. 118–119).

When the state is `x = (w, z)` with `w` IID with distribution `φ` and `z`
`Q`-Markov, the transition matrix is `P((w, z), (w', z')) = φ(w')Q(z, z')`. If
the continuation reward depends only on `z`, the continuation value function
`h*(w, z)` does not depend on `w`, and it is the unique fixed point of the
reduced operator (4.15) acting on `ℝ^Z`. Example 4.1.6 embeds IID job search
(`Z` a point), where the reduced operator is the scalar map of Vol. 1 (1.33).

§4.1.4.3 treats a firm whose scrap value is IID. Exercise 4.1.13 is formalised
with scrap values on a finite set `W ⊂ ℝ₊`, the discretised form the section
itself recommends: if `φ_a ≼_F φ_b` then the optimal policies satisfy
`σ*_a ≥ σ*_b` pointwise.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

variable {W Z : Type*} [Fintype W] [Fintype Z]

/-- The product kernel `P((w, z), (w', z')) = φ(w')Q(z, z')` of p. 118. -/
def productKernel (φ : W → ℝ) (Q : Matrix Z Z ℝ) : Matrix (W × Z) (W × Z) ℝ :=
  Matrix.of fun x x' => φ x'.1 * Q x.2 x'.2

omit [Fintype W] [Fintype Z] in
theorem productKernel_apply (φ : W → ℝ) (Q : Matrix Z Z ℝ) (x x' : W × Z) :
    productKernel φ Q x x' = φ x'.1 * Q x.2 x'.2 := rfl

/-- The product kernel is Markov when `φ` is a distribution and `Q` is Markov (p. 118). -/
theorem isMarkov_productKernel {φ : W → ℝ} (hφ : IsDistribution φ) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) : IsMarkov (productKernel φ Q) where
  nonneg x x' := mul_nonneg (hφ.nonneg _) (hQ.nonneg _ _)
  rowsum x := by
    simp only [productKernel_apply]
    rw [Fintype.sum_prod_type, sum_comm]
    simp only [← sum_mul, hφ.sum_eq_one, one_mul]
    exact hQ.rowsum _

/-- `(Pv)(w, z) = ∑_{z'} (∑_{w'} v(w', z')φ(w')) Q(z, z')` does not depend on `w`. -/
theorem productKernel_mulVec (φ : W → ℝ) (Q : Matrix Z Z ℝ) (v : W × Z → ℝ) (w : W) (z : Z) :
    (productKernel φ Q *ᵥ v) (w, z) = ∑ z', (∑ w', v (w', z') * φ w') * Q z z' := by
  rw [mulVec_apply_eq, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun z' _ => ?_
  rw [sum_mul]
  exact sum_congr rfl fun w' _ => by rw [productKernel_apply]; ring

/-- A stopping problem on `W × Z` with product transitions and a continuation reward depending
only on `z` (p. 118). -/
noncomputable def productProblem {φ : W → ℝ} (hφ : IsDistribution φ) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) (c : Z → ℝ) (e : W × Z → ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    StoppingProblem (W × Z) where
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  P := productKernel φ Q
  P_markov := isMarkov_productKernel hφ hQ
  c := fun x => c x.2
  e := e

namespace productProblem

variable {φ : W → ℝ} (hφ : IsDistribution φ) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (c : Z → ℝ)
  (e : W × Z → ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)

/-- The Bellman operator (4.14):
`(Tv)(w, z) = max{e(w, z), c(z) + β ∑_{w'} ∑_{z'} v(w', z')φ(w')Q(z, z')}`. -/
theorem T_apply (v : W × Z → ℝ) (w : W) (z : Z) :
    (productProblem hφ hQ c e hβ0 hβ1).T v (w, z) =
      max (e (w, z)) (c z + β * ∑ z', (∑ w', v (w', z') * φ w') * Q z z') := by
  rw [StoppingProblem.T, StoppingProblem.cont, productProblem, productKernel_mulVec]

/-- The reduced continuation value operator (4.15) on `ℝ^Z`:
`(C̃h)(z) = c(z) + β ∑_{w'} ∑_{z'} max{e(w', z'), h(z')} φ(w')Q(z, z')`. -/
noncomputable def reducedC (h : Z → ℝ) : Z → ℝ := fun z =>
  c z + β * ∑ z', (∑ w', max (e (w', z')) (h z') * φ w') * Q z z'

include hφ hQ hβ0 in
/-- `C̃` is order preserving. -/
theorem reducedC_monotone : Monotone (reducedC (φ := φ) (Q := Q) c e (β := β)) := by
  intro h h' hhh' z
  unfold reducedC
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun z' _ => ?_) hβ0.le)
  refine mul_le_mul_of_nonneg_right (sum_le_sum fun w' _ => ?_) (hQ.nonneg z z')
  exact mul_le_mul_of_nonneg_right (max_le_max le_rfl (hhh' z')) (hφ.nonneg w')

include hφ hQ hβ0 hβ1 in
/-- `C̃` is a contraction of modulus `β` on `ℝ^Z`. -/
theorem isContractionOn_reducedC :
    IsContractionOn (reducedC (φ := φ) (Q := Q) c e (β := β)) Set.univ β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := hβ0.le
  lt_one := hβ1
  norm_sub_le h _ h' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ0.le (norm_nonneg _))]
    intro z
    rw [Pi.sub_apply, Real.norm_eq_abs]
    unfold reducedC
    rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ0.le]
    refine mul_le_mul_of_nonneg_left ?_ hβ0.le
    have hb : ∀ z', |h z' - h' z'| ≤ ‖h - h'‖ := fun z' => by
      have := norm_le_pi_norm (h - h') z'
      simpa [Real.norm_eq_abs] using this
    calc |∑ z', (∑ w', max (e (w', z')) (h z') * φ w') * Q z z' -
          ∑ z', (∑ w', max (e (w', z')) (h' z') * φ w') * Q z z'|
        = |∑ z', (∑ w', (max (e (w', z')) (h z') - max (e (w', z')) (h' z')) * φ w') * Q z z'| := by
          rw [← sum_sub_distrib]
          congr 1
          refine sum_congr rfl fun z' _ => ?_
          rw [← sub_mul, ← sum_sub_distrib]
          congr 1
          exact sum_congr rfl fun w' _ => by ring
      _ ≤ ∑ z', (∑ w', |max (e (w', z')) (h z') - max (e (w', z')) (h' z')| * φ w') * Q z z' := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun z' _ => ?_)
          rw [abs_mul, abs_of_nonneg (hQ.nonneg z z')]
          refine mul_le_mul_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans
            (sum_le_sum fun w' _ => ?_)) (hQ.nonneg z z')
          rw [abs_mul, abs_of_nonneg (hφ.nonneg w')]
      _ ≤ ∑ z', (∑ w', ‖h - h'‖ * φ w') * Q z z' := by
          refine sum_le_sum fun z' _ => mul_le_mul_of_nonneg_right (sum_le_sum fun w' _ =>
            mul_le_mul_of_nonneg_right ?_ (hφ.nonneg w')) (hQ.nonneg z z')
          rw [max_comm (e (w', z')) (h z'), max_comm (e (w', z')) (h' z')]
          exact (abs_max_sub_max_le_abs _ _ _).trans (hb z')
      _ = ‖h - h'‖ := by
          simp only [← mul_sum, hφ.sum_eq_one, mul_one]
          rw [hQ.rowsum, mul_one]

/-- The reduced continuation value: the unique fixed point of `C̃` in `ℝ^Z`. -/
noncomputable def reducedH : Z → ℝ :=
  Classical.choose ((isContractionOn_reducedC hφ hQ c e hβ0 hβ1).exists_fixedPt isClosed_univ
    ⟨0, Set.mem_univ 0⟩)

theorem isFixedPt_reducedH :
    IsFixedPt (reducedC (φ := φ) (Q := Q) c e (β := β)) (reducedH hφ hQ c e hβ0 hβ1) :=
  (Classical.choose_spec ((isContractionOn_reducedC hφ hQ c e hβ0 hβ1).exists_fixedPt isClosed_univ
    ⟨0, Set.mem_univ 0⟩)).2

theorem eq_reducedH_of_isFixedPt {h : Z → ℝ}
    (hh : IsFixedPt (reducedC (φ := φ) (Q := Q) c e (β := β)) h) : h = reducedH hφ hQ c e hβ0 hβ1 :=
  (isContractionOn_reducedC hφ hQ c e hβ0 hβ1).fixedPt_unique (Set.mem_univ h) (Set.mem_univ _) hh
    (isFixedPt_reducedH hφ hQ c e hβ0 hβ1)

theorem tendsto_iterate_reducedC (h : Z → ℝ) :
    Tendsto (fun k : ℕ => (reducedC (φ := φ) (Q := Q) c e (β := β))^[k] h) atTop
      (𝓝 (reducedH hφ hQ c e hβ0 hβ1)) :=
  (isContractionOn_reducedC hφ hQ c e hβ0 hβ1).tendsto_iterate_fixedPt (Set.mem_univ h)
    (Set.mem_univ _) (isFixedPt_reducedH hφ hQ c e hβ0 hβ1)

variable [DecidableEq W] [DecidableEq Z]

/-- The continuation value does not depend on the IID component (p. 118). -/
theorem hstar_indep (w w' : W) (z : Z) :
    (productProblem hφ hQ c e hβ0 hβ1).hstar (w, z) =
      (productProblem hφ hQ c e hβ0 hβ1).hstar (w', z) := by
  simp only [StoppingProblem.hstar, StoppingProblem.cont, productProblem, productKernel_mulVec]

/-- The continuation value function of the full problem is the reduced one (p. 118):
`h*(w, z) = h̃(z)`. -/
theorem hstar_eq_reducedH (w : W) (z : Z) :
    (productProblem hφ hQ c e hβ0 hβ1).hstar (w, z) = reducedH hφ hQ c e hβ0 hβ1 z := by
  set S := productProblem hφ hQ c e hβ0 hβ1 with hS
  -- `z ↦ h*(w, z)` is a fixed point of `C̃`
  have hfix : IsFixedPt (reducedC (φ := φ) (Q := Q) c e (β := β)) fun z => S.hstar (w, z) := by
    funext z
    have h1 := congrFun S.isFixedPt_C_hstar.eq (w, z)
    rw [StoppingProblem.C, StoppingProblem.cont] at h1
    rw [← h1]
    have hind : ∀ w' z', S.hstar (w', z') = S.hstar (w, z') := fun w' z' =>
      hstar_indep hφ hQ c e hβ0 hβ1 w' w z'
    have hP : S.P = productKernel φ Q := rfl
    have hc : ∀ x, S.c x = c x.2 := fun _ => rfl
    have he : ∀ x, S.e x = e x := fun _ => rfl
    have hβ : S.β = β := rfl
    rw [hP, productKernel_mulVec]
    simp only [reducedC, hc, he, hβ, hind]
  have := eq_reducedH_of_isFixedPt hφ hQ c e hβ0 hβ1 hfix
  exact congrFun this z

/-- The optimal policy in reduced form: stop at `(w, z)` iff `e(w, z) ≥ h̃(z)`. -/
theorem sigmaStar_eq_true_iff (w : W) (z : Z) :
    (productProblem hφ hQ c e hβ0 hβ1).sigmaStar (w, z) = true ↔
      reducedH hφ hQ c e hβ0 hβ1 z ≤ e (w, z) := by
  rw [StoppingProblem.sigmaStar_eq_true_iff, hstar_eq_reducedH]
  exact Iff.rfl

end productProblem

/-- Example 4.1.6 (p. 118): with `Z` a single point, the reduced operator on `ℝ^Z ≅ ℝ` is the
scalar map `h ↦ c + β ∑_{w'} max{e(w'), h} φ(w')` of Vol. 1 (1.33), which is why IID job search
reduces to a one-dimensional problem. -/
theorem reducedC_unit {φ : W → ℝ} (c : ℝ) (e : W → ℝ) (β : ℝ) (h : Unit → ℝ) :
    productProblem.reducedC (φ := φ) (Q := (1 : Matrix Unit Unit ℝ)) (fun _ => c)
      (fun x => e x.1) (β := β) h () = c + β * ∑ w', max (e w') (h ()) * φ w' := by
  simp [productProblem.reducedC]

/-! ### Application to firm value with IID scrap values (§4.1.4.3) -/

/-- The firm of §4.1.2 whose scrap value `s(w)` is drawn IID from `φ` each period: exit reward
`s(w)`, continuation reward `π(z)` (p. 119). -/
noncomputable def scrapFirm {φ : W → ℝ} (hφ : IsDistribution φ) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) (π : Z → ℝ) (s : W → ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    StoppingProblem (W × Z) :=
  productProblem hφ hQ π (fun x => s x.1) hβ0 hβ1

/-- Exercise 4.1.12 (p. 119): the continuation value operator of the scrap-value firm, as a
self-map of `ℝ^Z`: `(C̃h)(z) = π(z) + β ∑_{z'} ∑_{w'} max{s(w'), h(z')} φ(w') Q(z, z')`. -/
theorem scrapFirm_reducedC {φ : W → ℝ} {Q : Matrix Z Z ℝ} (π : Z → ℝ) (s : W → ℝ) (β : ℝ)
    (h : Z → ℝ) (z : Z) :
    productProblem.reducedC (φ := φ) (Q := Q) π (fun x : W × Z => s x.1) (β := β) h z =
      π z + β * ∑ z', (∑ w', max (s w') (h z') * φ w') * Q z z' := rfl

variable [DecidableEq W] [DecidableEq Z] [PartialOrder W]

omit [DecidableEq W] [DecidableEq Z] in
/-- A higher scrap distribution raises the reduced operator: if `φ_a ≼_F φ_b` and `s` is
increasing, then `C̃_a h ≤ C̃_b h` for every `h`. -/
theorem scrapFirm_reducedC_le {φa φb : W → ℝ} (hab : FOSD φa φb) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) (π : Z → ℝ) {s : W → ℝ} (hs : Monotone s) {β : ℝ} (hβ0 : 0 < β)
    (h : Z → ℝ) :
    productProblem.reducedC (φ := φa) (Q := Q) π (fun x : W × Z => s x.1) (β := β) h ≤
      productProblem.reducedC (φ := φb) (Q := Q) π (fun x : W × Z => s x.1) (β := β) h := by
  intro z
  simp only [scrapFirm_reducedC]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun z' _ => ?_) hβ0.le)
  refine mul_le_mul_of_nonneg_right ?_ (hQ.nonneg z z')
  exact hab (fun w' => max (s w') (h z')) fun a b hab' => max_le_max (hs hab') le_rfl

/-- Exercise 4.1.13 (p. 119), finite-support version: if `φ_a ≼_F φ_b` then the reduced
continuation values satisfy `h̃_a ≤ h̃_b`, so the optimal policies satisfy `σ*_a ≥ σ*_b` pointwise:
a firm facing stochastically larger scrap values exits in fewer states. -/
theorem scrapFirm_sigmaStar_ge {φa φb : W → ℝ} (hφa : IsDistribution φa) (hφb : IsDistribution φb)
    (hab : FOSD φa φb) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (π : Z → ℝ) {s : W → ℝ}
    (hs : Monotone s) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (w : W) (z : Z) :
    (scrapFirm hφb hQ π s hβ0 hβ1).sigmaStar (w, z) = true →
      (scrapFirm hφa hQ π s hβ0 hβ1).sigmaStar (w, z) = true := by
  simp only [scrapFirm, productProblem.sigmaStar_eq_true_iff]
  intro hb
  refine le_trans ?_ hb
  exact fixedPt_le_of_le (scrapFirm_reducedC_le hab hQ π hs hβ0)
    (productProblem.reducedC_monotone hφb hQ π _ hβ0)
    (productProblem.isFixedPt_reducedH hφa hQ π _ hβ0 hβ1)
    (productProblem.tendsto_iterate_reducedC hφb hQ π _ hβ0 hβ1 _) z

end SargentStachurski.OptimalStopping

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Firm valuation with exit

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.2 (pp. 111–114)
and Examples 4.1.3–4.1.4 (pp. 115).

A firm with `Q`-Markov productivity earns `π(Zₜ)` while operating and may exit
for scrap value `s`, discounting at `β = 1/(1 + r)`. This is a stopping problem
with constant exit reward, so Propositions 4.1.2–4.1.3 apply. The no-exit value
`w = (I − βQ)⁻¹π` is the value of the policy that never exits, hence `w ≤ v*`
(p. 114); Exercise 4.1.7: if `Q ≫ 0` and `s > w(z)` somewhere, then `w ≪ v*`.
Examples 4.1.3–4.1.4: `v*` and `h*` are increasing and the optimal policy is
decreasing when `π` is increasing and `Q` monotone increasing. Exercise 4.1.8:
with stochastic prices and profit `max_ℓ (pℓ^{1/2} − wℓ) = p²/(4w)`, the
Bellman equation takes the stated form.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- The firm with an exit option (p. 111): productivity `Q`-Markov, profit `π`, scrap value `s`,
discount factor `β = 1/(1 + r)`. -/
noncomputable def firmExit {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (π : Z → ℝ) (s : ℝ) {r : ℝ}
    (hr : 0 < r) : StoppingProblem Z where
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  P := Q
  P_markov := hQ
  c := π
  e := fun _ => s

namespace firmExit

variable {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (π : Z → ℝ) (s : ℝ) {r : ℝ} (hr : 0 < r)

omit [DecidableEq Z] in
/-- The policy operator (p. 111): `(T_σ v)(z) = σ(z)s + (1 − σ(z))[π(z) + β ∑ v(z')Q(z, z')]`. -/
theorem Tσ_apply (σ : Policy Z) (v : Z → ℝ) (z : Z) :
    (firmExit hQ π s hr).Tσ σ v z =
      if σ z then s else π z + 1 / (1 + r) * ∑ z', v z' * Q z z' := by
  rw [StoppingProblem.Tσ, StoppingProblem.cont_apply]
  rfl

omit [DecidableEq Z] in
/-- The Bellman operator (p. 111): `(Tv)(z) = max{s, π(z) + β ∑ v(z')Q(z, z')}`. -/
theorem T_apply (v : Z → ℝ) (z : Z) :
    (firmExit hQ π s hr).T v z = max s (π z + 1 / (1 + r) * ∑ z', v z' * Q z z') := by
  rw [StoppingProblem.T_apply]
  rfl

/-- The Bellman equation for the firm (p. 112): `v*(z) = max{s, π(z) + β ∑ v*(z')Q(z, z')}`, with
`v*` its unique solution. -/
theorem bellman_equation (z : Z) :
    (firmExit hQ π s hr).vstar z =
      max s (π z + 1 / (1 + r) * ∑ z', (firmExit hQ π s hr).vstar z' * Q z z') := by
  rw [StoppingProblem.bellman_equation]
  rfl

/-- `v* = s ∨ h*` (p. 112): the value is the larger of the scrap value and the continuation
value `h* = π + βQv*`. -/
theorem vstar_eq_max (z : Z) :
    (firmExit hQ π s hr).vstar z = max s ((firmExit hQ π s hr).hstar z) :=
  StoppingProblem.vstar_eq_max_hstar _ z

/-- The `v*`-greedy policy exits when the continuation value falls below the scrap value
(p. 112): `σ*(z) = 1 ⟺ h*(z) ≤ s`. -/
theorem sigmaStar_eq_true_iff (z : Z) :
    (firmExit hQ π s hr).sigmaStar z = true ↔ (firmExit hQ π s hr).hstar z ≤ s :=
  StoppingProblem.sigmaStar_eq_true_iff _ z

/-! ### Exit versus no-exit (§4.1.2.2) -/

/-- The no-exit value `w` (p. 112): the value of the policy `σ ≡ 0` that never exits. -/
noncomputable def noExitValue : Z → ℝ := (firmExit hQ π s hr).vσ fun _ => false

omit [DecidableEq Z] in
/-- `w = π + βQw` (p. 114). -/
theorem noExitValue_eq (z : Z) :
    noExitValue hQ π s hr z = π z + 1 / (1 + r) * ∑ z', noExitValue hQ π s hr z' * Q z z' := by
  unfold noExitValue
  rw [StoppingProblem.vσ_of_continue _ _ rfl]
  rfl

/-- `w = (I − βQ)⁻¹π` (p. 114, by Lemma 3.2.1): `L_σ = βQ` and `r_σ = π` for `σ ≡ 0`. -/
theorem noExitValue_eq_inv :
    noExitValue hQ π s hr = (1 - (1 / (1 + r)) • Q)⁻¹ *ᵥ π := by
  unfold noExitValue
  rw [StoppingProblem.vσ_eq_inv]
  have hL : (firmExit hQ π s hr).L (fun _ => false) = (1 / (1 + r)) • Q := by
    ext z z'
    simp [StoppingProblem.L_apply, firmExit]
  have hr' : (firmExit hQ π s hr).r (fun _ => false) = π := by
    funext z
    simp [StoppingProblem.r, firmExit]
  rw [hL, hr']

/-- p. 114: `w ≤ v*`, since never exiting is a feasible policy. -/
theorem noExitValue_le_vstar : noExitValue hQ π s hr ≤ (firmExit hQ π s hr).vstar :=
  StoppingProblem.vσ_le_vstar _ _

/-- Exercise 4.1.7 (p. 114): if `Q ≫ 0` and `s > w(z₀)` for some `z₀`, then `w ≪ v*`: the option
to exit is strictly valuable everywhere, because every state reaches `z₀` next period with positive
probability, where exiting beats continuing. -/
theorem noExitValue_lt_vstar (hQpos : ∀ z z', 0 < Q z z') {z₀ : Z}
    (hz₀ : noExitValue hQ π s hr z₀ < s) (z : Z) :
    noExitValue hQ π s hr z < (firmExit hQ π s hr).vstar z := by
  set S := firmExit hQ π s hr with hS
  have hle := noExitValue_le_vstar hQ π s hr
  -- at `z₀` the value function is strictly above `w`
  have h0 : noExitValue hQ π s hr z₀ < S.vstar z₀ := by
    have := S.bellman_equation z₀
    rw [hS] at this
    calc noExitValue hQ π s hr z₀ < s := hz₀
      _ ≤ S.vstar z₀ := by rw [bellman_equation]; exact le_max_left _ _
  -- hence the expectation under any row of `Q ≫ 0` is strictly larger
  have hsum : ∑ z', noExitValue hQ π s hr z' * Q z z' < ∑ z', S.vstar z' * Q z z' := by
    refine sum_lt_sum (fun z' _ => mul_le_mul_of_nonneg_right (hle z') (hQpos z z').le)
      ⟨z₀, mem_univ _, mul_lt_mul_of_pos_right h0 (hQpos z z₀)⟩
  have hβ : (0 : ℝ) < 1 / (1 + r) := by positivity
  calc noExitValue hQ π s hr z = π z + 1 / (1 + r) * ∑ z', noExitValue hQ π s hr z' * Q z z' :=
        noExitValue_eq hQ π s hr z
    _ < π z + 1 / (1 + r) * ∑ z', S.vstar z' * Q z z' := by
        linarith [mul_lt_mul_of_pos_left hsum hβ]
    _ ≤ S.vstar z := by rw [bellman_equation]; exact le_max_right _ _

/-! ### Monotonicity (Examples 4.1.3–4.1.4) -/

variable [PartialOrder Z]

/-- Example 4.1.3 (p. 115): `v*` and `h*` are increasing when `π` is increasing and `Q` is monotone
increasing, since the scrap value is constant. -/
theorem monotone_vstar_hstar (hπ : Monotone π) (hQm : MonotoneIncreasing Q) :
    Monotone (firmExit hQ π s hr).vstar ∧ Monotone (firmExit hQ π s hr).hstar :=
  ⟨StoppingProblem.monotone_vstar _ (fun _ _ _ => le_rfl) hπ hQm,
    StoppingProblem.monotone_hstar _ (fun _ _ _ => le_rfl) hπ hQm⟩

/-- Example 4.1.4 (p. 115): under the same conditions the optimal policy is decreasing: exit is
optimal when the state is small and continuing when it is large. -/
theorem antitone_sigmaStar (hπ : Monotone π) (hQm : MonotoneIncreasing Q) :
    Antitone (firmExit hQ π s hr).sigmaStar :=
  StoppingProblem.antitone_sigmaStar_of_const _ (fun _ _ => rfl) hπ hQm

end firmExit

/-! ### Exercise 4.1.8: stochastic prices -/

/-- Exercise 4.1.8 (p. 114): with price `p ≥ 0` and wage `w > 0`, the one-period profit
`max_{ℓ ≥ 0} (p√ℓ − wℓ)` equals `p²/(4w)`, attained at `ℓ = (p/(2w))²`. -/
theorem isGreatest_profit {p w : ℝ} (hp : 0 ≤ p) (hw : 0 < w) :
    IsGreatest ((fun ℓ => p * Real.sqrt ℓ - w * ℓ) '' Set.Ici 0) (p ^ 2 / (4 * w)) := by
  constructor
  · refine ⟨(p / (2 * w)) ^ 2, Set.mem_Ici.2 (sq_nonneg _), ?_⟩
    have hsq : Real.sqrt ((p / (2 * w)) ^ 2) = p / (2 * w) :=
      Real.sqrt_sq (div_nonneg hp (by positivity))
    simp only [hsq]
    field_simp
    ring
  · rintro y ⟨ℓ, hℓ, rfl⟩
    have hℓ' : 0 ≤ ℓ := hℓ
    have hsq : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ'
    have hs0 : 0 ≤ Real.sqrt ℓ := Real.sqrt_nonneg ℓ
    change p * Real.sqrt ℓ - w * ℓ ≤ p ^ 2 / (4 * w)
    rw [le_div_iff₀ (by positivity)]
    set t := Real.sqrt ℓ with ht
    rw [← hsq]
    nlinarith [sq_nonneg (p - 2 * w * t)]

/-- Exercise 4.1.8 (p. 114): the firm with constant productivity, `Q`-Markov prices, profit
`π(p) = p²/(4w)` from the optimal labour choice, scrap value `s` and interest rate `r`. -/
noncomputable def priceFirm {Pm : Type*} [Fintype Pm] {Q : Matrix Pm Pm ℝ} (hQ : IsMarkov Q)
    (price : Pm → ℝ) (w s : ℝ) {r : ℝ} (hr : 0 < r) : StoppingProblem Pm :=
  firmExit hQ (fun p => price p ^ 2 / (4 * w)) s hr

/-- Exercise 4.1.8 (p. 114), the Bellman equation:
`v*(p) = max{s, p²/(4w) + β ∑ v*(p')Q(p, p')}` with `β = 1/(1 + r)`. -/
theorem priceFirm_bellman {Pm : Type*} [Fintype Pm] [DecidableEq Pm] {Q : Matrix Pm Pm ℝ}
    (hQ : IsMarkov Q) (price : Pm → ℝ) (w s : ℝ) {r : ℝ} (hr : 0 < r) (p : Pm) :
    (priceFirm hQ price w s hr).vstar p =
      max s (price p ^ 2 / (4 * w) +
        1 / (1 + r) * ∑ p', (priceFirm hQ price w s hr).vstar p' * Q p p') :=
  firmExit.bellman_equation hQ _ s hr p

end SargentStachurski.OptimalStopping

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# American options

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.2.1 (pp. 119–122).

A finite-horizon American call with expiry `T` is embedded in infinite-horizon
optimal stopping by putting the date into the state: `t ∈ {1, …, T + 1}`
updates by `m(t) = min{t + 1, T + 1}`, the stock price is `Sₜ = Zₜ + Wₜ` with
`Zₜ` `Q`-Markov and `Wₜ` IID with distribution `φ`, the exit reward is
`1{t ≤ T}(z + w − K)`, the continuation reward is zero and `β = 1/(1 + r)`.
The state is `(w, (t, z))`, the IID component first, so that the product
reduction of §4.1.4.2 applies: the continuation value operator (4.16) acts on
`ℝ^{T × Z}` and `σ*(t, w, z) = 1{e(t, w, z) ≥ h*(t, z)}`.

The claim of p. 122 that the exercise region expands with `t` is proved: `v*`
is nonnegative and nonincreasing in the date, so `h*(t, z)` is nonincreasing
in `t` and exercise at `(t, w, z)` implies exercise at `(m(t), w, z)` while
the option is alive.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

/-- The data of the American option model (p. 120): expiry `T`, the IID component `W` with
distribution `φ` and values `wval`, the Markov component `Z` with matrix `Q` and values `zval`,
strike `K` and interest rate `r > 0`. -/
structure AmericanOption (W Z : Type*) [Fintype W] [Fintype Z] where
  T : ℕ
  φ : W → ℝ
  φ_dist : IsDistribution φ
  wval : W → ℝ
  Q : Matrix Z Z ℝ
  Q_markov : IsMarkov Q
  zval : Z → ℝ
  K : ℝ
  r : ℝ
  r_pos : 0 < r

namespace AmericanOption

variable {W Z : Type*} [Fintype W] [Fintype Z] (m : AmericanOption W Z)

/-- The dates `{1, …, T + 1}`, represented zero-based: `t : Fin (T + 1)` stands for the date
`t + 1`. -/
abbrev Time := Fin (m.T + 1)

/-- The date update `m(t) = min{t + 1, T + 1}` (p. 120), zero-based. -/
def next (t : m.Time) : m.Time := ⟨min (t.val + 1) m.T, by omega⟩

/-- The option is alive at date `t` (book: `t ≤ T`), zero-based `t < T`. -/
abbrev alive (t : m.Time) : Prop := t.val < m.T

theorem next_of_alive {t : m.Time} (h : m.alive t) : (m.next t).val = t.val + 1 := by
  unfold next
  simp only
  unfold alive at h
  omega

theorem next_of_not_alive {t : m.Time} (h : ¬ m.alive t) : m.next t = t := by
  unfold alive at h
  apply Fin.ext
  unfold next
  simp only
  have := t.2
  omega

theorem next_next_of_last {t : m.Time} (h : ¬ m.alive (m.next t)) : m.next (m.next t) = m.next t :=
  m.next_of_not_alive h

/-- The discount factor `β = 1/(1 + r)` lies in `(0, 1)`. -/
theorem β_pos : (0 : ℝ) < 1 / (1 + m.r) := div_pos one_pos (by linarith [m.r_pos])

theorem β_lt_one : (1 : ℝ) / (1 + m.r) < 1 := by
  rw [div_lt_one (by linarith [m.r_pos])]
  linarith [m.r_pos]

/-- The deterministic-time kernel on `T × Z`: `1{t' = m(t)} Q(z, z')`. -/
noncomputable def timeKernel : Matrix (m.Time × Z) (m.Time × Z) ℝ :=
  Matrix.of fun x x' => (if x'.1 = m.next x.1 then 1 else 0) * m.Q x.2 x'.2

theorem isMarkov_timeKernel : IsMarkov m.timeKernel where
  nonneg x x' := by
    simp only [timeKernel, Matrix.of_apply]
    split_ifs <;> simp [m.Q_markov.nonneg]
  rowsum x := by
    rw [Fintype.sum_prod_type]
    have h : ∀ (t' : m.Time) (z' : Z),
        m.timeKernel x (t', z') = if t' = m.next x.1 then m.Q x.2 z' else 0 := by
      intro t' z'
      simp only [timeKernel, Matrix.of_apply]
      split_ifs <;> simp
    simp only [h]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq' univ (m.next x.1), mem_univ, ite_true]
    exact m.Q_markov.rowsum x.2

/-- `(Kv)(t, z) = ∑_{z'} v(m(t), z') Q(z, z')` for the time kernel. -/
theorem timeKernel_mulVec (v : m.Time × Z → ℝ) (t : m.Time) (z : Z) :
    (m.timeKernel *ᵥ v) (t, z) = ∑ z', v (m.next t, z') * m.Q z z' := by
  rw [mulVec_apply_eq, Fintype.sum_prod_type]
  have h : ∀ (t' : m.Time) (z' : Z), v (t', z') * m.timeKernel (t, z) (t', z') =
      if t' = m.next t then v (m.next t, z') * m.Q z z' else 0 := by
    intro t' z'
    simp only [timeKernel, Matrix.of_apply]
    split_ifs with h
    · rw [h]
      ring
    · ring
  simp only [h]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq' univ (m.next t), mem_univ, ite_true]

/-- The exit reward (p. 121): `e(t, w, z) = 1{t ≤ T}(z + w − K)`. -/
noncomputable def e (x : W × (m.Time × Z)) : ℝ :=
  if m.alive x.2.1 then m.zval x.2.2 + m.wval x.1 - m.K else 0

/-- The option as a stopping problem on `W × (T × Z)` (p. 120): transitions
`P((w, t, z), (w', t', z')) = 1{t' = m(t)} φ(w') Q(z, z')`, zero continuation reward,
`β = 1/(1 + r)`. -/
noncomputable def problem : StoppingProblem (W × (m.Time × Z)) :=
  productProblem m.φ_dist m.isMarkov_timeKernel (fun _ => 0) m.e m.β_pos m.β_lt_one

/-- The transition probabilities, as on p. 120. -/
theorem problem_P (w : W) (t : m.Time) (z : Z) (w' : W) (t' : m.Time) (z' : Z) :
    m.problem.P (w, (t, z)) (w', (t', z')) =
      (if t' = m.next t then 1 else 0) * m.φ w' * m.Q z z' := by
  simp only [problem, productProblem, productKernel_apply, timeKernel, Matrix.of_apply]
  ring

/-- `(Pv)(w, t, z) = ∑_{z'} (∑_{w'} v(w', m(t), z') φ(w')) Q(z, z')`: the time component updates
deterministically and `w` does not matter. -/
theorem problem_mulVec (v : W × (m.Time × Z) → ℝ) (w : W) (t : m.Time) (z : Z) :
    (m.problem.P *ᵥ v) (w, (t, z)) =
      ∑ z', (∑ w', v (w', (m.next t, z')) * m.φ w') * m.Q z z' := by
  rw [problem, productProblem, productKernel_mulVec, Fintype.sum_prod_type]
  have h : ∀ (t' : m.Time) (z' : Z),
      (∑ w', v (w', (t', z')) * m.φ w') * m.timeKernel (t, z) (t', z') =
      if t' = m.next t then (∑ w', v (w', (m.next t, z')) * m.φ w') * m.Q z z' else 0 := by
    intro t' z'
    simp only [timeKernel, Matrix.of_apply]
    split_ifs with h
    · rw [h]
      ring
    · ring
  simp only [h]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq' univ (m.next t), mem_univ, ite_true]

/-- The Bellman equation (p. 121):
`v(t, w, z) = max{e(t, w, z), β ∑_{w'} ∑_{z'} v(m(t), w', z') φ(w') Q(z, z')}`. -/
theorem bellman_equation [DecidableEq W] [DecidableEq Z] (w : W) (t : m.Time) (z : Z) :
    m.problem.vstar (w, (t, z)) =
      max (m.e (w, (t, z)))
        (1 / (1 + m.r) *
          ∑ z', (∑ w', m.problem.vstar (w', (m.next t, z')) * m.φ w') * m.Q z z') := by
  have := congrFun m.problem.isFixedPt_T_vstar.eq (w, (t, z))
  rw [← this, StoppingProblem.T, StoppingProblem.cont, problem_mulVec]
  simp [problem, productProblem]

variable [DecidableEq W] [DecidableEq Z]

omit [DecidableEq W] [DecidableEq Z] in
/-- The continuation value operator (4.16) on `ℝ^{T × Z}`:
`(Ch)(t, z) = β ∑_{z'} ∑_{w'} max{e(m(t), w', z'), h(m(t), z')} φ(w') Q(z, z')`. -/
theorem reducedC_apply (h : m.Time × Z → ℝ) (t : m.Time) (z : Z) :
    productProblem.reducedC (φ := m.φ) (Q := m.timeKernel) (fun _ => 0) m.e (β := 1 / (1 + m.r))
      h (t, z) =
      1 / (1 + m.r) * ∑ z', (∑ w', max (m.e (w', (m.next t, z'))) (h (m.next t, z')) * m.φ w') *
        m.Q z z' := by
  simp only [productProblem.reducedC, zero_add]
  rw [Fintype.sum_prod_type]
  have hk : ∀ (t' : m.Time) (z' : Z),
      (∑ w', max (m.e (w', (t', z'))) (h (t', z')) * m.φ w') * m.timeKernel (t, z) (t', z') =
      if t' = m.next t then
        (∑ w', max (m.e (w', (m.next t, z'))) (h (m.next t, z')) * m.φ w') * m.Q z z' else 0 := by
    intro t' z'
    simp only [timeKernel, Matrix.of_apply]
    split_ifs with h
    · rw [h]
      ring
    · ring
  simp only [hk]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq' univ (m.next t), mem_univ, ite_true]

/-- The continuation value function `h*(t, z)` (p. 121): the unique fixed point of (4.16). -/
noncomputable def hstar : m.Time × Z → ℝ :=
  productProblem.reducedH m.φ_dist m.isMarkov_timeKernel (fun _ => 0) m.e m.β_pos m.β_lt_one

/-- The full continuation value depends on `(t, z)` only, through `h*` (p. 121). -/
theorem hstar_eq (w : W) (t : m.Time) (z : Z) :
    m.problem.hstar (w, (t, z)) = m.hstar (t, z) :=
  productProblem.hstar_eq_reducedH _ _ _ _ _ _ w (t, z)

omit [DecidableEq W] [DecidableEq Z] in
/-- `Cᵏh → h*` for every `h ∈ ℝ^{T × Z}` (p. 121). -/
theorem tendsto_iterate_reducedC (h : m.Time × Z → ℝ) :
    Tendsto (fun k : ℕ => (productProblem.reducedC (φ := m.φ) (Q := m.timeKernel) (fun _ => 0) m.e
      (β := 1 / (1 + m.r)))^[k] h) atTop (𝓝 m.hstar) :=
  productProblem.tendsto_iterate_reducedC _ _ _ _ _ _ h

/-- The optimal policy (p. 121): exercise at `(t, w, z)` iff `e(t, w, z) ≥ h*(t, z)`. -/
theorem sigmaStar_eq_true_iff (w : W) (t : m.Time) (z : Z) :
    m.problem.sigmaStar (w, (t, z)) = true ↔ m.hstar (t, z) ≤ m.e (w, (t, z)) := by
  rw [StoppingProblem.sigmaStar_eq_true_iff, hstar_eq]
  exact Iff.rfl

theorem isOptimal_sigmaStar : m.problem.IsOptimal m.problem.sigmaStar :=
  m.problem.isOptimal_sigmaStar

/-! ### The exercise region expands with the date (p. 122) -/

/-- `v* ≥ 0` and `v*` is nonincreasing in the date: `v*(w, m(t), z) ≤ v*(w, t, z)`. The Bellman
operator preserves this closed set of functions. -/
theorem vstar_nonneg_antitone :
    (∀ x, 0 ≤ m.problem.vstar x) ∧
      ∀ w t z, m.problem.vstar (w, (m.next t, z)) ≤ m.problem.vstar (w, (t, z)) := by
  set A : Set (W × (m.Time × Z) → ℝ) :=
    {v | (∀ x, 0 ≤ v x) ∧ ∀ w t z, v (w, (m.next t, z)) ≤ v (w, (t, z))} with hA
  have hclosed : IsClosed A := by
    have h1 : IsClosed {v : W × (m.Time × Z) → ℝ | ∀ x, 0 ≤ v x} := by
      have : {v : W × (m.Time × Z) → ℝ | ∀ x, 0 ≤ v x} = ⋂ x, {v | 0 ≤ v x} := by ext; simp
      rw [this]
      exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)
    have h2 : IsClosed {v : W × (m.Time × Z) → ℝ |
        ∀ w t z, v (w, (m.next t, z)) ≤ v (w, (t, z))} := by
      have : {v : W × (m.Time × Z) → ℝ | ∀ w t z, v (w, (m.next t, z)) ≤ v (w, (t, z))} =
          ⋂ (w) (t) (z), {v | v (w, (m.next t, z)) ≤ v (w, (t, z))} := by ext; simp
      rw [this]
      exact isClosed_iInter fun w => isClosed_iInter fun t => isClosed_iInter fun z =>
        isClosed_le (continuous_apply _) (continuous_apply _)
    exact h1.inter h2
  have hβ : (0 : ℝ) ≤ 1 / (1 + m.r) := m.β_pos.le
  -- the continuation payoff, written through `problem_mulVec`
  have hcont : ∀ v w t z, m.problem.cont v (w, (t, z)) =
      1 / (1 + m.r) * ∑ z', (∑ w', v (w', (m.next t, z')) * m.φ w') * m.Q z z' := by
    intro v w t z
    rw [StoppingProblem.cont, problem_mulVec]
    simp [problem, productProblem]
  have hmaps : ∀ v ∈ A, m.problem.T v ∈ A := by
    rintro v ⟨hv0, hvm⟩
    have hT0 : ∀ x, 0 ≤ m.problem.T v x := by
      rintro ⟨w, t, z⟩
      refine le_max_of_le_right ?_
      rw [hcont]
      refine mul_nonneg hβ (sum_nonneg fun z' _ => mul_nonneg (sum_nonneg fun w' _ =>
        mul_nonneg (hv0 _) (m.φ_dist.nonneg w')) (m.Q_markov.nonneg z z'))
    refine ⟨hT0, fun w t z => ?_⟩
    -- continuation payoffs are ordered because `v` is
    have hc : m.problem.cont v (w, (m.next t, z)) ≤ m.problem.cont v (w, (t, z)) := by
      rw [hcont, hcont]
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun z' _ => mul_le_mul_of_nonneg_right
        (sum_le_sum fun w' _ => mul_le_mul_of_nonneg_right (hvm w' (m.next t) z')
          (m.φ_dist.nonneg w')) (m.Q_markov.nonneg z z')) hβ
    by_cases halive : m.alive (m.next t)
    · -- both dates are alive: equal exit rewards
      have ht : m.alive t := by
        unfold alive at halive ⊢
        unfold next at halive
        simp only at halive
        omega
      have he : m.e (w, (m.next t, z)) = m.e (w, (t, z)) := by
        simp [e, halive, ht]
      change max (m.e (w, (m.next t, z))) (m.problem.cont v (w, (m.next t, z))) ≤
        max (m.e (w, (t, z))) (m.problem.cont v (w, (t, z)))
      rw [he]
      exact max_le_max le_rfl hc
    · -- the option is dead at `m(t)`: exit reward `0 ≤ Tv(w, t, z)`
      have he : m.e (w, (m.next t, z)) = 0 := by simp [e, halive]
      change max (m.e (w, (m.next t, z))) (m.problem.cont v (w, (m.next t, z))) ≤
        max (m.e (w, (t, z))) (m.problem.cont v (w, (t, z)))
      rw [he]
      exact max_le (hT0 (w, (t, z))) (hc.trans (le_max_right _ _))
  have h0 : (0 : W × (m.Time × Z) → ℝ) ∈ A := ⟨fun _ => le_rfl, fun _ _ _ => le_rfl⟩
  have hiter : ∀ k : ℕ, m.problem.T^[k] 0 ∈ A := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih => rw [iterate_succ_apply']; exact hmaps _ ih
  exact hclosed.mem_of_tendsto (m.problem.tendsto_iterate_T 0) (Eventually.of_forall hiter)

omit [DecidableEq W] [DecidableEq Z] in
/-- The continuation value is nonincreasing in the date: `h*(m(t), z) ≤ h*(t, z)` (p. 122). -/
theorem hstar_antitone (t : m.Time) (z : Z) : m.hstar (m.next t, z) ≤ m.hstar (t, z) := by
  classical
  obtain ⟨w⟩ : Nonempty W := by
    by_contra hW
    rw [not_nonempty_iff] at hW
    exact absurd m.φ_dist.sum_eq_one (by simp)
  rw [← hstar_eq m w, ← hstar_eq m w]
  have := (m.vstar_nonneg_antitone).2
  have hc : ∀ x, m.problem.c x = 0 := fun _ => rfl
  have hβ : m.problem.β = 1 / (1 + m.r) := rfl
  simp only [StoppingProblem.hstar, StoppingProblem.cont, problem_mulVec, hc, hβ, zero_add]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun z' _ => mul_le_mul_of_nonneg_right
    (sum_le_sum fun w' _ => mul_le_mul_of_nonneg_right (this w' (m.next t) z')
      (m.φ_dist.nonneg w')) (m.Q_markov.nonneg z z')) m.β_pos.le

/-- The exercise region expands with `t` (p. 122): while the option is alive at `m(t)`, exercising
at `(t, w, z)` is optimal only if exercising at `(m(t), w, z)` is. -/
theorem exercise_region_expands (w : W) (t : m.Time) (z : Z) (halive : m.alive (m.next t)) :
    m.problem.sigmaStar (w, (t, z)) = true → m.problem.sigmaStar (w, (m.next t, z)) = true := by
  rw [sigmaStar_eq_true_iff, sigmaStar_eq_true_iff]
  intro h
  have ht : m.alive t := by
    unfold alive at halive ⊢
    unfold next at halive
    simp only at halive
    omega
  have he : m.e (w, (m.next t, z)) = m.e (w, (t, z)) := by simp [e, halive, ht]
  rw [he]
  exact (m.hstar_antitone t z).trans h

end AmericanOption

end SargentStachurski.OptimalStopping

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Research and development

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.2.2 (pp. 122–126).

A firm develops a product worth `π(Xₜ)` when marketed, paying a flow cost
while it continues. With constant cost `c`, this is a stopping problem with
exit reward `π` and continuation reward `−c`, Bellman equation (4.17);
Exercise 4.2.1 gives the continuation value operator and shows `h*` is
increasing when `π` is and `P` is monotone increasing; Exercise 4.2.2 shows
the optimal policy is increasing when `π` is increasing and `(Xₜ)` is IID.

With IID costs `Cₜ ∼ φ` the state is `(c, x)` and the continuation value still
depends on `c`; the expected value function `g(x) = ∑ v*(c', x')φ(c')P(x, x')`,
(4.19), solves the functional equation (4.20) on `ℝ^X`. Exercise 4.2.3: the
operator `R` of (4.20) is a contraction of modulus `β`, so `g*` is unique and
computable by successive approximation, and
`σ*(c, x) = 1{π(x) ≥ −c + βg*(x)}` is optimal.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Constant R&D costs (§4.2.2.1) -/

/-- R&D with constant cost `c₀` (p. 125): exit reward `π`, continuation reward `−c₀`,
`β = 1/(1 + r)`. -/
noncomputable def rdConstant {P : Matrix X X ℝ} (hP : IsMarkov P) (π : X → ℝ) (c₀ : ℝ) {r : ℝ}
    (hr : 0 < r) : StoppingProblem X where
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  P := P
  P_markov := hP
  c := fun _ => -c₀
  e := π

namespace rdConstant

variable {P : Matrix X X ℝ} (hP : IsMarkov P) (π : X → ℝ) (c₀ : ℝ) {r : ℝ} (hr : 0 < r)

/-- The Bellman equation (4.17): `v*(x) = max{π(x), −c₀ + β ∑ v*(x')P(x, x')}`. -/
theorem bellman_equation (x : X) :
    (rdConstant hP π c₀ hr).vstar x =
      max (π x) (-c₀ + 1 / (1 + r) * ∑ x', (rdConstant hP π c₀ hr).vstar x' * P x x') := by
  rw [StoppingProblem.bellman_equation]
  rfl

omit [DecidableEq X] in
/-- Exercise 4.2.1 (p. 125): the continuation value operator is
`(Ch)(x) = −c₀ + β ∑ max{π(x'), h(x')} P(x, x')`. -/
theorem C_apply (h : X → ℝ) (x : X) :
    (rdConstant hP π c₀ hr).C h x = -c₀ + 1 / (1 + r) * ∑ x', max (π x') (h x') * P x x' := by
  rw [StoppingProblem.C_apply]
  rfl

/-- Exercise 4.2.1 (p. 125): `h*` is increasing whenever `π` is increasing and `P` is monotone
increasing (Lemma 4.1.4 with a constant continuation reward). -/
theorem monotone_hstar [PartialOrder X] (hπ : Monotone π) (hPm : MonotoneIncreasing P) :
    Monotone (rdConstant hP π c₀ hr).hstar :=
  StoppingProblem.monotone_hstar _ hπ (fun _ _ _ => le_rfl) hPm

/-- Exercise 4.2.2 (p. 125): the optimal policy is increasing whenever `π` is increasing and `(Xₜ)`
is IID, i.e. all rows of `P` are identical: then `h*` is constant and Exercise 4.1.11 applies. A
higher state means a more valuable product to market now, while the prospects of waiting do not
depend on the state. -/
theorem monotone_sigmaStar [PartialOrder X] (hπ : Monotone π) (hiid : ∀ x y, P x = P y) :
    Monotone (rdConstant hP π c₀ hr).sigmaStar :=
  StoppingProblem.monotone_sigmaStar_of_iid _ hπ hiid fun _ _ => rfl

end rdConstant

/-! ### IID R&D costs (§4.2.2.2) -/

variable {Wc : Type*} [Fintype Wc] [DecidableEq Wc]

/-- R&D with IID costs (p. 125): the state is `(c, x)` with `c ∼ φ` IID and `x` `P`-Markov, exit
reward `π(x)`, continuation reward `−cost(c)`. -/
noncomputable def rdIID {φ : Wc → ℝ} (hφ : IsDistribution φ) {P : Matrix X X ℝ} (hP : IsMarkov P)
    (cost : Wc → ℝ) (π : X → ℝ) {r : ℝ} (hr : 0 < r) : StoppingProblem (Wc × X) where
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  P := productKernel φ P
  P_markov := isMarkov_productKernel hφ hP
  c := fun x => -cost x.1
  e := fun x => π x.2

namespace rdIID

variable {φ : Wc → ℝ} (hφ : IsDistribution φ) {P : Matrix X X ℝ} (hP : IsMarkov P)
  (cost : Wc → ℝ) (π : X → ℝ) {r : ℝ} (hr : 0 < r)

/-- The Bellman equation (4.18):
`v*(c, x) = max{π(x), −c + β ∑_{x'} ∑_{c'} v*(c', x') φ(c') P(x, x')}`. -/
theorem bellman_equation (c : Wc) (x : X) :
    (rdIID hφ hP cost π hr).vstar (c, x) =
      max (π x) (-cost c + 1 / (1 + r) *
        ∑ x', (∑ c', (rdIID hφ hP cost π hr).vstar (c', x') * φ c') * P x x') := by
  have := congrFun (rdIID hφ hP cost π hr).isFixedPt_T_vstar.eq (c, x)
  rw [← this, StoppingProblem.T, StoppingProblem.cont, rdIID, productKernel_mulVec]

/-- The expected value function (4.19): `g(x) = ∑_{x'} ∑_{c'} v*(c', x') φ(c') P(x, x')`. -/
noncomputable def g : X → ℝ := fun x =>
  ∑ x', (∑ c', (rdIID hφ hP cost π hr).vstar (c', x') * φ c') * P x x'

/-- `v*(c', x') = max{π(x'), −c' + βg(x')}` (p. 126). -/
theorem vstar_eq (c : Wc) (x : X) :
    (rdIID hφ hP cost π hr).vstar (c, x) =
      max (π x) (-cost c + 1 / (1 + r) * g hφ hP cost π hr x) :=
  bellman_equation hφ hP cost π hr c x

/-- The operator `R` of p. 126:
`(Rg)(x) = ∑_{x'} ∑_{c'} max{π(x'), −c' + βg(x')} φ(c') P(x, x')`. -/
noncomputable def R (φ : Wc → ℝ) (P : Matrix X X ℝ) (cost : Wc → ℝ) (π : X → ℝ) (r : ℝ)
    (g : X → ℝ) : X → ℝ := fun x =>
  ∑ x', (∑ c', max (π x') (-cost c' + 1 / (1 + r) * g x') * φ c') * P x x'

/-- (4.20), p. 126: `g` is a fixed point of `R`. -/
theorem isFixedPt_R_g : IsFixedPt (R φ P cost π r) (g hφ hP cost π hr) := by
  funext x
  unfold R
  conv_rhs => rw [g]
  refine sum_congr rfl fun x' _ => ?_
  congr 1
  refine sum_congr rfl fun c' _ => ?_
  rw [vstar_eq]

omit [DecidableEq X] [DecidableEq Wc] in
include hφ hP hr in
/-- Exercise 4.2.3 (p. 126): `R` is a contraction of modulus `β` on `ℝ^X`. -/
theorem isContractionOn_R : IsContractionOn (R φ P cost π r) Set.univ (1 / (1 + r)) where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := by positivity
  lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  norm_sub_le g _ g' _ := by
    have hβ : (0 : ℝ) ≤ 1 / (1 + r) := by positivity
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    have hb : ∀ x', |g x' - g' x'| ≤ ‖g - g'‖ := fun x' => by
      have := norm_le_pi_norm (g - g') x'
      simpa [Real.norm_eq_abs] using this
    unfold R
    calc |∑ x', (∑ c', max (π x') (-cost c' + 1 / (1 + r) * g x') * φ c') * P x x' -
          ∑ x', (∑ c', max (π x') (-cost c' + 1 / (1 + r) * g' x') * φ c') * P x x'|
        = |∑ x', (∑ c', (max (π x') (-cost c' + 1 / (1 + r) * g x') -
            max (π x') (-cost c' + 1 / (1 + r) * g' x')) * φ c') * P x x'| := by
          rw [← sum_sub_distrib]
          congr 1
          refine sum_congr rfl fun x' _ => ?_
          rw [← sub_mul, ← sum_sub_distrib]
          congr 1
          exact sum_congr rfl fun c' _ => by ring
      _ ≤ ∑ x', (∑ c', |max (π x') (-cost c' + 1 / (1 + r) * g x') -
            max (π x') (-cost c' + 1 / (1 + r) * g' x')| * φ c') * P x x' := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => ?_)
          rw [abs_mul, abs_of_nonneg (hP.nonneg x x')]
          refine mul_le_mul_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans
            (sum_le_sum fun c' _ => ?_)) (hP.nonneg x x')
          rw [abs_mul, abs_of_nonneg (hφ.nonneg c')]
      _ ≤ ∑ x', (∑ c', (1 / (1 + r) * ‖g - g'‖) * φ c') * P x x' := by
          refine sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (sum_le_sum fun c' _ =>
            mul_le_mul_of_nonneg_right ?_ (hφ.nonneg c')) (hP.nonneg x x')
          rw [max_comm (π x'), max_comm (π x')]
          refine (abs_max_sub_max_le_abs _ _ _).trans ?_
          rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ]
          exact mul_le_mul_of_nonneg_left (hb x') hβ
      _ = 1 / (1 + r) * ‖g - g'‖ := by
          simp only [← mul_sum, hφ.sum_eq_one, mul_one]
          rw [hP.rowsum, mul_one]

/-- `g` is the unique solution of (4.20) in `ℝ^X`, and successive approximation with `R` converges
to it from any starting point (p. 126). -/
theorem eq_g_of_isFixedPt {g' : X → ℝ} (hg' : IsFixedPt (R φ P cost π r) g') :
    g' = g hφ hP cost π hr :=
  (isContractionOn_R hφ hP cost π hr).fixedPt_unique (Set.mem_univ _) (Set.mem_univ _) hg'
    (isFixedPt_R_g hφ hP cost π hr)

theorem tendsto_iterate_R (g₀ : X → ℝ) :
    Tendsto (fun k : ℕ => (R φ P cost π r)^[k] g₀) atTop (𝓝 (g hφ hP cost π hr)) :=
  (isContractionOn_R hφ hP cost π hr).tendsto_iterate_fixedPt (Set.mem_univ _) (Set.mem_univ _)
    (isFixedPt_R_g hφ hP cost π hr)

/-- The optimal policy (p. 126): `σ*(c, x) = 1{π(x) ≥ −c + βg*(x)}`. -/
theorem sigmaStar_eq_true_iff (c : Wc) (x : X) :
    (rdIID hφ hP cost π hr).sigmaStar (c, x) = true ↔
      -cost c + 1 / (1 + r) * g hφ hP cost π hr x ≤ π x := by
  rw [StoppingProblem.sigmaStar_eq_true_iff]
  have : (rdIID hφ hP cost π hr).hstar (c, x) = -cost c + 1 / (1 + r) * g hφ hP cost π hr x := by
    rw [StoppingProblem.hstar, StoppingProblem.cont, rdIID, productKernel_mulVec]
    rfl
  rw [this]
  rfl

end rdIID

end SargentStachurski.OptimalStopping

set_option linter.style.longLine false
#print axioms SargentStachurski.OptimalStopping.IsMarkov
#print axioms SargentStachurski.OptimalStopping.IsMarkov.mk
#print axioms SargentStachurski.OptimalStopping.IsMarkov.nonneg
#print axioms SargentStachurski.OptimalStopping.IsMarkov.rowsum
#print axioms SargentStachurski.OptimalStopping.IsDistribution
#print axioms SargentStachurski.OptimalStopping.IsDistribution.mk
#print axioms SargentStachurski.OptimalStopping.IsDistribution.nonneg
#print axioms SargentStachurski.OptimalStopping.IsDistribution.sum_eq_one
#print axioms SargentStachurski.OptimalStopping.mulVec_apply_eq
#print axioms SargentStachurski.OptimalStopping.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.OptimalStopping.IsMarkov.mulVec_const
#print axioms SargentStachurski.OptimalStopping.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.OptimalStopping.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.OptimalStopping.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.OptimalStopping.GloballyStable
#print axioms SargentStachurski.OptimalStopping.IsContractionOn
#print axioms SargentStachurski.OptimalStopping.IsContractionOn.mk
#print axioms SargentStachurski.OptimalStopping.IsContractionOn.mapsTo
#print axioms SargentStachurski.OptimalStopping.IsContractionOn.nonneg
#print axioms SargentStachurski.OptimalStopping.IsContractionOn.lt_one
#print axioms SargentStachurski.OptimalStopping.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.OptimalStopping.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.OptimalStopping.IsContractionOn.iterate_mem
#print axioms SargentStachurski.OptimalStopping.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.OptimalStopping.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.OptimalStopping.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.OptimalStopping.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.OptimalStopping.fixedPt_le_of_le
#print axioms SargentStachurski.OptimalStopping.isClosed_monotone
#print axioms SargentStachurski.OptimalStopping.FOSD
#print axioms SargentStachurski.OptimalStopping.MonotoneIncreasing
#print axioms SargentStachurski.OptimalStopping.monotoneIncreasing_iff
#print axioms SargentStachurski.OptimalStopping.StoppingProblem
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.mk
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.β
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.β_pos
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.β_lt_one
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.P
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.P_markov
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.c
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.e
#print axioms SargentStachurski.OptimalStopping.Policy
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.cont
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.cont_apply
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.r
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.L
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.L_apply
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.Tσ
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.Tσ_eq
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.Tσ_monotone
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.abs_Tσ_sub_le
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isContractionOn_Tσ
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.vσ
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isFixedPt_vσ
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.eq_vσ_of_isFixedPt
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.tendsto_iterate_Tσ
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.vσ_eq
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.vσ_of_stop
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.vσ_of_continue
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.vσ_eq_r_add
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.L_nonneg
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.L_rowsum_le
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.abs_L_mulVec_le
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.norm_L_mulVec_le
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.norm_L_pow_mulVec_le
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isUnit_one_sub_L
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.vσ_eq_inv
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.summable_L_pow_mulVec
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.vσ_eq_tsum
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.iidJobSearch
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.perpetualOption
#print axioms SargentStachurski.OptimalStopping.complexify
#print axioms SargentStachurski.OptimalStopping.complexify_apply
#print axioms SargentStachurski.OptimalStopping.nnnorm_complexify
#print axioms SargentStachurski.OptimalStopping.norm_complexify
#print axioms SargentStachurski.OptimalStopping.specRad
#print axioms SargentStachurski.OptimalStopping.norm_le_of_rowsum_abs_le
#print axioms SargentStachurski.OptimalStopping.specRad_le_norm
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.norm_L_le
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.specRad_L_lt_one
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.T
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.T_apply
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.T_monotone
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.abs_T_sub_le
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isContractionOn_T
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.Tσ_le_T
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.IsGreedy
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.greedy
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isGreedy_greedy
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.Tσ_eq_T_of_isGreedy
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.vstar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.vσ_le_vstar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.exists_vσ_eq_vstar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isFixedPt_T_vstar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.eq_vstar_of_isFixedPt
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.bellman_equation
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.tendsto_iterate_T
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.norm_iterate_T_sub_vstar_le
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.globallyStable_T
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.IsOptimal
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isOptimal_iff_vσ_eq
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isOptimal_iff_isGreedy
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isOptimal_greedy_vstar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.hstar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.hstar_apply
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.vstar_eq_max_hstar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.C
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.C_apply
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isFixedPt_C_hstar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.C_monotone
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.abs_C_sub_le
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isContractionOn_C
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.eq_hstar_of_isFixedPt
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.tendsto_iterate_C
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.sigmaStar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.sigmaStar_eq_greedy
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isGreedy_sigmaStar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.isOptimal_sigmaStar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.sigmaStar_eq_true_iff
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.monotone_T_of_monotone
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.monotone_vstar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.monotone_hstar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.antitone_sigmaStar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.antitone_sigmaStar_of_const
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.monotone_sigmaStar
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.hstar_const_of_iid
#print axioms SargentStachurski.OptimalStopping.StoppingProblem.monotone_sigmaStar_of_iid
#print axioms SargentStachurski.OptimalStopping.exists_threshold_of_monotone
#print axioms SargentStachurski.OptimalStopping.exists_threshold_of_antitone
#print axioms SargentStachurski.OptimalStopping.productKernel
#print axioms SargentStachurski.OptimalStopping.productKernel_apply
#print axioms SargentStachurski.OptimalStopping.isMarkov_productKernel
#print axioms SargentStachurski.OptimalStopping.productKernel_mulVec
#print axioms SargentStachurski.OptimalStopping.productProblem
#print axioms SargentStachurski.OptimalStopping.productProblem.T_apply
#print axioms SargentStachurski.OptimalStopping.productProblem.reducedC
#print axioms SargentStachurski.OptimalStopping.productProblem.reducedC_monotone
#print axioms SargentStachurski.OptimalStopping.productProblem.isContractionOn_reducedC
#print axioms SargentStachurski.OptimalStopping.productProblem.reducedH
#print axioms SargentStachurski.OptimalStopping.productProblem.isFixedPt_reducedH
#print axioms SargentStachurski.OptimalStopping.productProblem.eq_reducedH_of_isFixedPt
#print axioms SargentStachurski.OptimalStopping.productProblem.tendsto_iterate_reducedC
#print axioms SargentStachurski.OptimalStopping.productProblem.hstar_indep
#print axioms SargentStachurski.OptimalStopping.productProblem.hstar_eq_reducedH
#print axioms SargentStachurski.OptimalStopping.productProblem.sigmaStar_eq_true_iff
#print axioms SargentStachurski.OptimalStopping.reducedC_unit
#print axioms SargentStachurski.OptimalStopping.scrapFirm
#print axioms SargentStachurski.OptimalStopping.scrapFirm_reducedC
#print axioms SargentStachurski.OptimalStopping.scrapFirm_reducedC_le
#print axioms SargentStachurski.OptimalStopping.scrapFirm_sigmaStar_ge
#print axioms SargentStachurski.OptimalStopping.firmExit
#print axioms SargentStachurski.OptimalStopping.firmExit.Tσ_apply
#print axioms SargentStachurski.OptimalStopping.firmExit.T_apply
#print axioms SargentStachurski.OptimalStopping.firmExit.bellman_equation
#print axioms SargentStachurski.OptimalStopping.firmExit.vstar_eq_max
#print axioms SargentStachurski.OptimalStopping.firmExit.sigmaStar_eq_true_iff
#print axioms SargentStachurski.OptimalStopping.firmExit.noExitValue
#print axioms SargentStachurski.OptimalStopping.firmExit.noExitValue_eq
#print axioms SargentStachurski.OptimalStopping.firmExit.noExitValue_eq_inv
#print axioms SargentStachurski.OptimalStopping.firmExit.noExitValue_le_vstar
#print axioms SargentStachurski.OptimalStopping.firmExit.noExitValue_lt_vstar
#print axioms SargentStachurski.OptimalStopping.firmExit.monotone_vstar_hstar
#print axioms SargentStachurski.OptimalStopping.firmExit.antitone_sigmaStar
#print axioms SargentStachurski.OptimalStopping.isGreatest_profit
#print axioms SargentStachurski.OptimalStopping.priceFirm
#print axioms SargentStachurski.OptimalStopping.priceFirm_bellman
#print axioms SargentStachurski.OptimalStopping.AmericanOption
#print axioms SargentStachurski.OptimalStopping.AmericanOption.mk
#print axioms SargentStachurski.OptimalStopping.AmericanOption.T
#print axioms SargentStachurski.OptimalStopping.AmericanOption.φ
#print axioms SargentStachurski.OptimalStopping.AmericanOption.φ_dist
#print axioms SargentStachurski.OptimalStopping.AmericanOption.wval
#print axioms SargentStachurski.OptimalStopping.AmericanOption.Q
#print axioms SargentStachurski.OptimalStopping.AmericanOption.Q_markov
#print axioms SargentStachurski.OptimalStopping.AmericanOption.zval
#print axioms SargentStachurski.OptimalStopping.AmericanOption.K
#print axioms SargentStachurski.OptimalStopping.AmericanOption.r
#print axioms SargentStachurski.OptimalStopping.AmericanOption.r_pos
#print axioms SargentStachurski.OptimalStopping.AmericanOption.Time
#print axioms SargentStachurski.OptimalStopping.AmericanOption.next
#print axioms SargentStachurski.OptimalStopping.AmericanOption.alive
#print axioms SargentStachurski.OptimalStopping.AmericanOption.next_of_alive
#print axioms SargentStachurski.OptimalStopping.AmericanOption.next_of_not_alive
#print axioms SargentStachurski.OptimalStopping.AmericanOption.next_next_of_last
#print axioms SargentStachurski.OptimalStopping.AmericanOption.β_pos
#print axioms SargentStachurski.OptimalStopping.AmericanOption.β_lt_one
#print axioms SargentStachurski.OptimalStopping.AmericanOption.timeKernel
#print axioms SargentStachurski.OptimalStopping.AmericanOption.isMarkov_timeKernel
#print axioms SargentStachurski.OptimalStopping.AmericanOption.timeKernel_mulVec
#print axioms SargentStachurski.OptimalStopping.AmericanOption.e
#print axioms SargentStachurski.OptimalStopping.AmericanOption.problem
#print axioms SargentStachurski.OptimalStopping.AmericanOption.problem_P
#print axioms SargentStachurski.OptimalStopping.AmericanOption.problem_mulVec
#print axioms SargentStachurski.OptimalStopping.AmericanOption.bellman_equation
#print axioms SargentStachurski.OptimalStopping.AmericanOption.reducedC_apply
#print axioms SargentStachurski.OptimalStopping.AmericanOption.hstar
#print axioms SargentStachurski.OptimalStopping.AmericanOption.hstar_eq
#print axioms SargentStachurski.OptimalStopping.AmericanOption.tendsto_iterate_reducedC
#print axioms SargentStachurski.OptimalStopping.AmericanOption.sigmaStar_eq_true_iff
#print axioms SargentStachurski.OptimalStopping.AmericanOption.isOptimal_sigmaStar
#print axioms SargentStachurski.OptimalStopping.AmericanOption.vstar_nonneg_antitone
#print axioms SargentStachurski.OptimalStopping.AmericanOption.hstar_antitone
#print axioms SargentStachurski.OptimalStopping.AmericanOption.exercise_region_expands
#print axioms SargentStachurski.OptimalStopping.rdConstant
#print axioms SargentStachurski.OptimalStopping.rdConstant.bellman_equation
#print axioms SargentStachurski.OptimalStopping.rdConstant.C_apply
#print axioms SargentStachurski.OptimalStopping.rdConstant.monotone_hstar
#print axioms SargentStachurski.OptimalStopping.rdConstant.monotone_sigmaStar
#print axioms SargentStachurski.OptimalStopping.rdIID
#print axioms SargentStachurski.OptimalStopping.rdIID.bellman_equation
#print axioms SargentStachurski.OptimalStopping.rdIID.g
#print axioms SargentStachurski.OptimalStopping.rdIID.vstar_eq
#print axioms SargentStachurski.OptimalStopping.rdIID.R
#print axioms SargentStachurski.OptimalStopping.rdIID.isFixedPt_R_g
#print axioms SargentStachurski.OptimalStopping.rdIID.isContractionOn_R
#print axioms SargentStachurski.OptimalStopping.rdIID.eq_g_of_isFixedPt
#print axioms SargentStachurski.OptimalStopping.rdIID.tendsto_iterate_R
#print axioms SargentStachurski.OptimalStopping.rdIID.sigmaStar_eq_true_iff
