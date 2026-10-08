/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDynamics.Tauchen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Geometric sums

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.2.2 (pp. 94–97).

The lifetime value `v(x) = E_x ∑ βᵗ h(Xₜ)`, (3.16), is `∑ βᵗ Pᵗ h` by (3.14),
(3.18). Lemma 3.2.1: for `β < 1`, `I − βP` is invertible and
`v = ∑ (βP)ᵗ h = (I − βP)⁻¹ h`, (3.17). The book applies the Neumann series lemma
to `βP` with `ρ(βP) = β`; here the series is summed directly in the
supremum norm, where `‖(βP)ᵗh‖ ≤ βᵗ‖h‖`, and `I − βP` is invertible because
`u = βPu` forces `‖u‖ ≤ β‖u‖`.

Applications: the valuation of a firm (3.19) with `β = 1/(1 + r)`, and the
value of a consumption stream (3.20)–(3.21). Exercise 3.2.6: `v` is increasing
when `π` is increasing and `P` monotone increasing, since each `Pᵗπ` is
increasing and the increasing functions are closed. Exercise 3.2.8: with CRRA
utility `u(c) = c^{1−γ}/(1 − γ)`, `c(x) = eˣ` and a Tauchen chain with
`ρ ≥ 0`, the value is increasing in the state.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDynamics

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `‖(βP)ᵗ h‖ ≤ βᵗ ‖h‖` for a Markov matrix `P` and `β ≥ 0`. -/
theorem IsMarkov.norm_smul_pow_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ : 0 ≤ β)
    (h : X → ℝ) (t : ℕ) : ‖(β • P) ^ t *ᵥ h‖ ≤ β ^ t * ‖h‖ := by
  rw [smul_pow, smul_mulVec, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hβ t)]
  exact mul_le_mul_of_nonneg_left ((hP.pow t).norm_mulVec_le h) (pow_nonneg hβ t)

/-- (3.18): the series `∑ₜ (βP)ᵗ h` converges in `ℝ^X`. -/
theorem IsMarkov.summable_smul_pow_mulVec {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (h : X → ℝ) : Summable fun t : ℕ => (β • P) ^ t *ᵥ h :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right ‖h‖)
    (hP.norm_smul_pow_mulVec_le hβ0 h)

/-- The lifetime value (3.16), computed by (3.18): `v = ∑ₜ βᵗ Pᵗ h`. -/
noncomputable def lifetimeValue (P : Matrix X X ℝ) (β : ℝ) (h : X → ℝ) : X → ℝ :=
  ∑' t : ℕ, (β • P) ^ t *ᵥ h

theorem lifetimeValue_eq_tsum_smul (P : Matrix X X ℝ) (β : ℝ) (h : X → ℝ) :
    lifetimeValue P β h = ∑' t : ℕ, β ^ t • (P ^ t *ᵥ h) := by
  unfold lifetimeValue
  refine tsum_congr fun t => ?_
  rw [smul_pow, smul_mulVec]

/-- `(I − βP) ∑ₜ (βP)ᵗ h = h`: the series telescopes. -/
theorem IsMarkov.one_sub_smul_mulVec_lifetimeValue {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (h : X → ℝ) :
    (1 - β • P) *ᵥ lifetimeValue P β h = h := by
  have hs := hP.summable_smul_pow_mulVec hβ0 hβ1 h
  have hs' : Summable fun t : ℕ => (β • P) ^ (t + 1) *ᵥ h :=
    (summable_nat_add_iff 1).2 hs
  -- the matrix acts continuously and linearly, so it passes through the sum
  let L := LinearMap.toContinuousLinearMap (Matrix.mulVecLin (1 - β • P))
  have hL : ∀ u, L u = (1 - β • P) *ᵥ u := fun u => rfl
  unfold lifetimeValue
  rw [← hL, L.map_tsum hs]
  simp only [hL, sub_mulVec, one_mulVec]
  have hterm : ∀ t : ℕ, (β • P) ^ t *ᵥ h - (β • P) *ᵥ ((β • P) ^ t *ᵥ h) =
      (β • P) ^ t *ᵥ h - (β • P) ^ (t + 1) *ᵥ h := by
    intro t
    rw [mulVec_mulVec, ← pow_succ']
  simp only [hterm]
  rw [hs.tsum_sub hs', hs.tsum_eq_zero_add]
  simp

/-- `I − βP` is invertible for `β ∈ [0, 1)`: `u = βPu` forces `‖u‖ ≤ β‖u‖`, so `u = 0`. -/
theorem IsMarkov.isUnit_one_sub_smul {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : IsUnit (1 - β • P) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  have hd : (1 - β • P) *ᵥ (u - v) = 0 := by
    rw [mulVec_sub]
    exact sub_eq_zero.2 huv
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at hd
  have hnorm : ‖u - v‖ ≤ β * ‖u - v‖ := by
    calc ‖u - v‖ = ‖(β • P) *ᵥ (u - v)‖ := by rw [← hd]
      _ = β * ‖P *ᵥ (u - v)‖ := by
          rw [smul_mulVec, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ0]
      _ ≤ β * ‖u - v‖ := mul_le_mul_of_nonneg_left (hP.norm_mulVec_le _) hβ0
  have : ‖u - v‖ ≤ 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this (norm_nonneg _)))

/-- **Lemma 3.2.1** (p. 94), (3.17): if `β < 1` then `I − βP` is invertible and
`v = ∑ₜ (βP)ᵗ h = (I − βP)⁻¹ h`. -/
theorem IsMarkov.lifetimeValue_eq_inv {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (h : X → ℝ) :
    IsUnit (1 - β • P) ∧ lifetimeValue P β h = (1 - β • P)⁻¹ *ᵥ h := by
  have hunit := hP.isUnit_one_sub_smul hβ0 hβ1
  refine ⟨hunit, ?_⟩
  have hv := hP.one_sub_smul_mulVec_lifetimeValue hβ0 hβ1 h
  calc lifetimeValue P β h = (1 - β • P)⁻¹ *ᵥ ((1 - β • P) *ᵥ lifetimeValue P β h) := by
        rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
          one_mulVec]
    _ = (1 - β • P)⁻¹ *ᵥ h := by rw [hv]

/-- The recursive form `v = h + βPv`, the step behind (3.17). -/
theorem IsMarkov.lifetimeValue_eq_add {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (h : X → ℝ) :
    lifetimeValue P β h = h + β • (P *ᵥ lifetimeValue P β h) := by
  have := hP.one_sub_smul_mulVec_lifetimeValue hβ0 hβ1 h
  rw [sub_mulVec, one_mulVec, smul_mulVec, sub_eq_iff_eq_add] at this
  exact this

/-! ### Valuation of firms (§3.2.2.2) -/

/-- The firm's discount factor `β = 1/(1 + r)` lies in `(0, 1)` for `r > 0` (p. 95). -/
theorem firm_discount_mem {r : ℝ} (hr : 0 < r) : 0 < 1 / (1 + r) ∧ 1 / (1 + r) < 1 := by
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]
    linarith

/-- The value of the firm (3.19), p. 95: `v = ∑ₜ βᵗ Pᵗ π = (I − βP)⁻¹ π` with `β = 1/(1 + r)`. -/
theorem IsMarkov.firm_value {P : Matrix X X ℝ} (hP : IsMarkov P) {r : ℝ} (hr : 0 < r)
    (π : X → ℝ) :
    lifetimeValue P (1 / (1 + r)) π = (1 - (1 / (1 + r)) • P)⁻¹ *ᵥ π :=
  (hP.lifetimeValue_eq_inv (firm_discount_mem hr).1.le (firm_discount_mem hr).2 π).2

/-- The increasing functions `iℝ^X` on a partially ordered set form a closed set
(Vol. 1, Ex 2.2.30). -/
theorem isClosed_monotone (Y : Type*) [Preorder Y] : IsClosed {h : Y → ℝ | Monotone h} := by
  have : {h : Y → ℝ | Monotone h} = ⋂ (p : Y) (q : Y) (_ : p ≤ q), {h : Y → ℝ | h p ≤ h q} := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun hm p q hpq => hm hpq, fun hm p q hpq => hm p q hpq⟩
  rw [this]
  exact isClosed_iInter fun p => isClosed_iInter fun q => isClosed_iInter fun _ =>
    isClosed_le (continuous_apply p) (continuous_apply q)

/-- A finite sum of increasing functions is increasing. -/
theorem monotone_sum {Y : Type*} [Preorder Y] {ι : Type*} (s : Finset ι) {f : ι → Y → ℝ}
    (hf : ∀ i ∈ s, Monotone (f i)) : Monotone fun y => ∑ i ∈ s, f i y :=
  fun _ _ hab => sum_le_sum fun i hi => hf i hi hab

/-- Exercise 3.2.6 (p. 95): if `π` is increasing and `P` is monotone increasing, then the value
`v = ∑ βᵗ Pᵗ π` is increasing on `X`. -/
theorem IsMarkov.monotone_lifetimeValue [PartialOrder X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hmono : MonotoneIncreasing P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {π : X → ℝ}
    (hπ : Monotone π) : Monotone (lifetimeValue P β π) := by
  have hs := hP.summable_smul_pow_mulVec hβ0 hβ1 π
  have hlim := hs.hasSum.tendsto_sum_nat
  have hterm : ∀ t : ℕ, Monotone ((β • P) ^ t *ᵥ π) := by
    intro t
    rw [smul_pow, smul_mulVec]
    have := (monotoneIncreasing_iff (P ^ t)).1 (hmono.pow t) π hπ
    exact fun a b hab => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (this hab) (pow_nonneg hβ0 t)
  have hpartial : ∀ K, Monotone (∑ t ∈ range K, (β • P) ^ t *ᵥ π) := by
    intro K
    have := monotone_sum (range K) (f := fun t => (β • P) ^ t *ᵥ π) fun t _ => hterm t
    convert this using 1
    funext y
    simp [Finset.sum_apply]
  exact (isClosed_monotone X).mem_of_tendsto hlim (Eventually.of_forall hpartial)

/-! ### Valuing consumption streams (§3.2.2.3) -/

/-- The CRRA flow utility (3.22): `u(c) = c^{1−γ}/(1 − γ)`. -/
noncomputable def crra (γ c : ℝ) : ℝ := c ^ (1 - γ) / (1 - γ)

/-- The value of the consumption stream (3.21): `v = (I − βP)⁻¹ r` with `r = u ∘ c`. -/
theorem IsMarkov.consumption_value {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (u : ℝ → ℝ) (c : X → ℝ) :
    lifetimeValue P β (u ∘ c) = (1 - β • P)⁻¹ *ᵥ (u ∘ c) :=
  (hP.lifetimeValue_eq_inv hβ0 hβ1 _).2

/-- `x ↦ u(eˣ)` is increasing for CRRA utility with `γ ≠ 1`: `eˣ^{1−γ}/(1 − γ) = e^{(1−γ)x}/(1 − γ)`
and both the numerator's monotonicity and the sign of `1 − γ` flip together. -/
theorem monotone_crra_exp {γ : ℝ} (hγ : γ ≠ 1) : Monotone fun x : ℝ => crra γ (Real.exp x) := by
  intro a b hab
  change Real.exp a ^ (1 - γ) / (1 - γ) ≤ Real.exp b ^ (1 - γ) / (1 - γ)
  rw [Real.rpow_def_of_pos (Real.exp_pos a), Real.rpow_def_of_pos (Real.exp_pos b),
    Real.log_exp, Real.log_exp]
  rcases lt_or_gt_of_ne hγ with h | h
  · have hpos : 0 < 1 - γ := by linarith
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hpos.le
  · have hneg : 1 - γ < 0 := by linarith
    rw [div_le_div_right_of_neg hneg]
    exact Real.exp_le_exp.2 (by nlinarith)

/-- Exercise 3.2.8 (p. 96): for the CRRA model with `c(x) = eˣ` on a Tauchen chain with `ρ ≥ 0`
and `γ ≠ 1`, the value function is increasing in the state. -/
theorem Tauchen.monotone_crra_value (m : Tauchen) (hρ : 0 ≤ m.ρ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {γ : ℝ} (hγ : γ ≠ 1) :
    Monotone (lifetimeValue m.P β fun i : Fin m.n => crra γ (Real.exp (m.x i))) :=
  m.isMarkov_P.monotone_lifetimeValue (m.monotoneIncreasing_P hρ) hβ0 hβ1
    fun _ _ hij => monotone_crra_exp hγ (m.x_mono (Fin.le_def.1 hij))

end SargentStachurski.MarkovDynamics
