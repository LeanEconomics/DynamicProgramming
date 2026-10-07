/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.SpectralBound
import Mathlib.Topology.Instances.Matrix

/-!
# Strongly continuous semigroups on `ℝ^X`

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.2.5 (pp. 317–318).

A family `(S_t)_{t ≥ 0}` of linear operators on `ℝ^X` is a `C₀`-semigroup if `S₀ = I`,
`S_{t+t'} = S_t S_{t'}` and `t ↦ S_t u` is continuous on `[0, ∞)` for every `u`.

* Example 10.1.3: `S_t = e^{tA}` is a `C₀`-semigroup.
* **Proposition 10.1.6**: every `C₀`-semigroup on `ℝ^X` is exponential, `S_t = e^{tA}`, and `A` is
  its infinitesimal generator (10.19), `A = lim_{t ↓ 0} (S_t − I)/t`. The book cites Engel and Nagel
  (Theorem 2.12). The proof here: `V(h) = ∫₀^h S_τ dτ` has `V(h)/h → I`, so `W = V(h₀)` is
  invertible for some `h₀ > 0`; then `S_h W = V(h + h₀) − V(h)`, so `S` is differentiable with
  `Ṡ_h = S_h A`, `A = (S_{h₀} − I)W⁻¹`; finally `S_h e^{−hA}` has derivative zero.

Matrix-valued derivatives and limits are taken entry by entry, as in the book (p. 312).
-/

open Finset Matrix Filter Topology Function Set MeasureTheory

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A strongly continuous (`C₀`) semigroup on `ℝ^X` (p. 317). -/
structure IsC0Semigroup (S : ℝ → Matrix X X ℝ) : Prop where
  zero : S 0 = 1
  add : ∀ s t, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t
  cont : ∀ u : X → ℝ, ContinuousOn (fun t => S t *ᵥ u) (Ici 0)

/-- **Example 10.1.3** (p. 317): `S_t = e^{tA}` is a `C₀`-semigroup. -/
theorem isC0Semigroup_exp (A : Matrix X X ℝ) :
    IsC0Semigroup fun t : ℝ => NormedSpace.exp (t • A) where
  zero := by rw [zero_smul, NormedSpace.exp_zero]
  add s t _ _ := exp_smul_add A s t
  cont u := fun t _ => (hasDerivAt_exp_smul_mulVec A u t).continuousAt.continuousWithinAt

omit [DecidableEq X] in
/-- Product rule for matrix products, entrywise, at a point. -/
theorem hasDerivAt_mul_entry {M N : ℝ → Matrix X X ℝ} {M' N' : Matrix X X ℝ} {t : ℝ}
    (hM : ∀ x y, HasDerivAt (fun s => M s x y) (M' x y) t)
    (hN : ∀ x y, HasDerivAt (fun s => N s x y) (N' x y) t) (x y : X) :
    HasDerivAt (fun s => (M s * N s) x y) ((M' * N t + M t * N') x y) t := by
  have h := HasDerivAt.fun_sum (u := univ) fun z _ => (hM x z).mul (hN z y)
  simp only [Matrix.mul_apply, Matrix.add_apply]
  convert h using 1
  rw [← Finset.sum_add_distrib]

namespace IsC0Semigroup

variable {S : ℝ → Matrix X X ℝ} (h : IsC0Semigroup S)
include h

/-- The entries of a `C₀`-semigroup are continuous on `[0, ∞)`. -/
theorem continuousOn_entry (x y : X) : ContinuousOn (fun t => S t x y) (Ici 0) := by
  have h1 := (continuous_apply x).comp_continuousOn (h.cont (Pi.single y 1))
  refine h1.congr fun t _ => ?_
  simp [Function.comp, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The entries are interval integrable on `[0, b]` for `b ≥ 0`. -/
theorem intervalIntegrable_entry (x y : X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t => S t x y) volume a b :=
  ((h.continuousOn_entry x y).mono fun _ hs => le_trans (le_min ha hb) hs.1).intervalIntegrable

/-- `V(h) = ∫₀^h S_τ dτ`, entrywise. -/
noncomputable def V (S : ℝ → Matrix X X ℝ) (b : ℝ) : Matrix X X ℝ :=
  fun x y => ∫ τ in (0 : ℝ)..b, S τ x y

/-- `d/dh V(h) = S_h` for `h > 0`. -/
theorem hasDerivAt_V {b : ℝ} (hb : 0 < b) (x y : X) :
    HasDerivAt (fun c => V S c x y) (S b x y) b :=
  intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable_entry x y le_rfl hb.le)
    ((h.continuousOn_entry x y).mono Ioi_subset_Ici_self |>.stronglyMeasurableAtFilter isOpen_Ioi b
      hb)
    ((h.continuousOn_entry x y).continuousAt (Ici_mem_nhds hb))

/-- `V(h)/h → I` as `h ↓ 0`, entrywise. -/
theorem tendsto_V_div (x y : X) :
    Tendsto (fun c => c⁻¹ * V S c x y) (𝓝[>] 0) (𝓝 ((1 : Matrix X X ℝ) x y)) := by
  have hd : HasDerivWithinAt (fun c => V S c x y) (S 0 x y) (Ici 0) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right (h.intervalIntegrable_entry x y le_rfl le_rfl)
      (((h.continuousOn_entry x y).mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin
        measurableSet_Ioi 0)
      (((h.continuousOn_entry x y) 0 (Set.mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self)
  have hs := hasDerivWithinAt_iff_tendsto_slope.1 hd
  rw [show Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 by ext; simp [lt_iff_le_and_ne, eq_comm]] at hs
  rw [h.zero] at hs
  refine hs.congr fun c => ?_
  simp [slope_def_field, V, div_eq_inv_mul]

/-- There is `h₀ > 0` with `V(h₀)` invertible. -/
theorem exists_V_isUnit : ∃ h₀ : ℝ, 0 < h₀ ∧ IsUnit (V S h₀) := by
  have hT : Tendsto (fun c => c⁻¹ • V S c) (𝓝[>] 0) (𝓝 (1 : Matrix X X ℝ)) :=
    tendsto_pi_nhds.2 fun x => tendsto_pi_nhds.2 fun y => by
      simpa [Matrix.smul_apply] using h.tendsto_V_div x y
  have hdet := ((continuous_id.matrix_det).tendsto (1 : Matrix X X ℝ)).comp hT
  simp only [id, Matrix.det_one] at hdet
  obtain ⟨c, hc, hcpos⟩ := ((hdet.eventually (isOpen_ne.mem_nhds one_ne_zero)).and
    self_mem_nhdsWithin).exists
  refine ⟨c, hcpos, (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun h0 => hc ?_)⟩
  change (c⁻¹ • V S c).det = 0
  rw [Matrix.det_smul, h0, mul_zero]

/-- `S_h V(h₀) = V(h + h₀) − V(h)` for `h, h₀ ≥ 0`. -/
theorem mul_V {b h₀ : ℝ} (hb : 0 ≤ b) (hh₀ : 0 ≤ h₀) :
    S b * V S h₀ = V S (b + h₀) - V S b := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.sub_apply, V]
  calc ∑ z, S b x z * ∫ τ in (0 : ℝ)..h₀, S τ z y
      = ∑ z, ∫ τ in (0 : ℝ)..h₀, S b x z * S τ z y := by
        simp only [intervalIntegral.integral_const_mul]
    _ = ∫ τ in (0 : ℝ)..h₀, ∑ z, S b x z * S τ z y := by
        rw [intervalIntegral.integral_finsetSum fun z _ =>
          (h.intervalIntegrable_entry z y le_rfl hh₀).const_mul _]
    _ = ∫ τ in (0 : ℝ)..h₀, S (b + τ) x y := by
        refine intervalIntegral.integral_congr fun τ hτ => ?_
        have hτ0 : 0 ≤ τ := by
          rw [uIcc_of_le hh₀] at hτ
          exact hτ.1
        simp only [h.add b τ hb hτ0, Matrix.mul_apply]
    _ = ∫ σ in b..b + h₀, S σ x y := by
        rw [intervalIntegral.integral_comp_add_left (fun σ => S σ x y), add_zero]
    _ = (∫ τ in (0 : ℝ)..b + h₀, S τ x y) - ∫ τ in (0 : ℝ)..b, S τ x y :=
        (intervalIntegral.integral_interval_sub_left
          (h.intervalIntegrable_entry x y le_rfl (by linarith))
          (h.intervalIntegrable_entry x y le_rfl hb)).symm

/-- `Ṡ_h = S_h A` for `h > 0`, with `A = (S_{h₀} − I)V(h₀)⁻¹`. -/
theorem hasDerivAt_entry {h₀ : ℝ} (hh₀ : 0 < h₀) (hW : IsUnit (V S h₀)) {b : ℝ} (hb : 0 < b)
    (x y : X) :
    HasDerivAt (fun c => S c x y) ((S b * ((S h₀ - 1) * (V S h₀)⁻¹)) x y) b := by
  set W := V S h₀
  have hWdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det _).1 hW
  -- `S_c = (V(c + h₀) − V(c))W⁻¹` near `b`
  have heq : ∀ᶠ c in 𝓝 b, S c x y = ((V S (c + h₀) - V S c) * W⁻¹) x y := by
    filter_upwards [Ioi_mem_nhds hb] with c hc
    rw [← h.mul_V (le_of_lt hc) hh₀.le, Matrix.mul_nonsing_inv_cancel_right _ _ hWdet]
  have hd : HasDerivAt (fun c => ((V S (c + h₀) - V S c) * W⁻¹) x y)
      (((S (b + h₀) - S b) * W⁻¹) x y) b := by
    simp only [Matrix.mul_apply, Matrix.sub_apply]
    refine HasDerivAt.fun_sum fun z _ => HasDerivAt.mul_const ?_ _
    have h1 : HasDerivAt (fun c => V S (c + h₀) x z) (S (b + h₀) x z) b := by
      have := (h.hasDerivAt_V (show (0 : ℝ) < b + h₀ by linarith) x z).comp b
        ((hasDerivAt_id b).add_const h₀)
      simp only [id, mul_one] at this
      exact this
    exact h1.sub (h.hasDerivAt_V hb x z)
  have hval : (S (b + h₀) - S b) * W⁻¹ = S b * ((S h₀ - 1) * W⁻¹) := by
    rw [h.add b h₀ hb.le hh₀.le, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one]
  rw [← hval]
  exact hd.congr_of_eventuallyEq heq

/-- **Proposition 10.1.6** (p. 318): every `C₀`-semigroup on `ℝ^X` is exponential, `S_t = e^{tA}`
for `t ≥ 0`, and `A` is its infinitesimal generator (10.19): `(S_t − I)/t → A` as `t ↓ 0`. -/
theorem exists_eq_exp :
    ∃ A : Matrix X X ℝ, (∀ t, 0 ≤ t → S t = NormedSpace.exp (t • A)) ∧
      ∀ x y, Tendsto (fun t => (S t x y - (1 : Matrix X X ℝ) x y) / t) (𝓝[>] 0) (𝓝 (A x y)) := by
  obtain ⟨h₀, hh₀, hW⟩ := h.exists_V_isUnit
  obtain ⟨A, hA⟩ : ∃ A, A = (S h₀ - 1) * (V S h₀)⁻¹ := ⟨_, rfl⟩
  set g : ℝ → Matrix X X ℝ := fun c => S c * NormedSpace.exp ((-c) • A)
  -- `g` has derivative zero on `(0, ∞)`
  have hg : ∀ c, 0 < c → ∀ x y, HasDerivAt (fun s => g s x y) 0 c := fun c hc x y => by
    have hp := hasDerivAt_mul_entry (M' := S c * A) (N' := -(A * NormedSpace.exp ((-c) • A)))
      (fun x y => by rw [hA]; exact h.hasDerivAt_entry hh₀ hW hc x y)
      (fun x y => hasDerivAt_exp_neg_smul_entry A c x y) x y
    convert hp using 1
    rw [Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel, Matrix.zero_apply]
  have hgcont : ∀ x y, ContinuousOn (fun s => g s x y) (Ici 0) := fun x y => by
    simp only [g, Matrix.mul_apply]
    refine continuousOn_finsetSum _ fun z _ => (h.continuousOn_entry x z).mul ?_
    exact (continuous_apply_apply z y |>.comp (continuous_exp_smul A |>.comp continuous_neg))
      |>.continuousOn
  have hg0 : g 0 = 1 := by simp [g, h.zero]
  have hgt : ∀ t, 0 ≤ t → g t = 1 := by
    intro t ht
    rcases ht.lt_or_eq with htpos | rfl
    · ext x y
      -- `g` is constant on `[ε, t]` for every `ε ∈ (0, t]`
      have hconst : ∀ᶠ ε in 𝓝[>] 0, g t x y = g ε x y := by
        filter_upwards [Ioo_mem_nhdsGT htpos] with ε hε
        have hc := constant_of_has_deriv_right_zero (a := ε) (b := t) ((hgcont x y).mono fun s hs =>
          le_trans hε.1.le hs.1) fun s hs => (hg s (lt_of_lt_of_le hε.1 hs.1) x y).hasDerivWithinAt
        exact hc t ⟨hε.2.le, le_rfl⟩
      have hlim : Tendsto (fun ε => g ε x y) (𝓝[>] 0) (𝓝 (g 0 x y)) :=
        ((hgcont x y) 0 (Set.mem_Ici.2 le_rfl)).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
      have := tendsto_nhds_unique (tendsto_const_nhds.congr' hconst) hlim
      rw [this, hg0]
    · exact hg0
  have hS : ∀ t, 0 ≤ t → S t = NormedSpace.exp (t • A) := fun t ht => by
    have hinv : NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A) = 1 := by
      have := exp_smul_mul_exp_neg_smul A (-t)
      rwa [neg_neg] at this
    calc S t = S t * (NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A)) := by
          rw [hinv, Matrix.mul_one]
      _ = g t * NormedSpace.exp (t • A) := by simp only [g, Matrix.mul_assoc]
      _ = NormedSpace.exp (t • A) := by rw [hgt t ht, Matrix.one_mul]
  refine ⟨A, hS, fun x y => ?_⟩
  have hslope := (hasDerivAt_exp_smul_entry A 0 x y).tendsto_slope_zero_right
  rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at hslope
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [zero_add, smul_eq_mul, hS t (le_of_lt ht), div_eq_inv_mul]

end IsC0Semigroup

end SargentStachurski.ContinuousTime
