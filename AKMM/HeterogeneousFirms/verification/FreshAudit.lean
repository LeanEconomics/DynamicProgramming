import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import NewKeynesian.NKFinalGoods
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Sqrt
import ParetoOptimaEquilibria.Welfare
import AKMMGrowth.QualityLadders
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A simple model of heterogeneous firms (AKMM §22.2)

AKMM, §22.2, pp. 664–665, with footnote 2. Firm `i` produces `yᵢ = aᵢF(xᵢ)^γ` with `F`
homogeneous of degree one and `0 < γ < 1`. The unit mass of firms is a probability space
`(Ω, P)`; the book's `∫ · di` is `∫ · ∂P`.

* **Two-stage cost minimisation**: if `x*` minimises `p·x` on `{F = 1}` with unit cost `c`, then
  `m x*` minimises cost on `{F = m}` at cost `cm` (`twostage_cost`), and the firm's profit is at
  most `amᵞ − cm` with `m = F(x)`, attained by `m x*` (`twostage_profit_le`,
  `twostage_profit_eq`).
* **(22.1)–(22.2)**: the scale problem has the unique maximiser `m* = (γa/c)^{1/(1−γ)}`,
  characterised by the first-order condition (`eq_22_1`, `eq_22_2`), and `y = (c/γ)m`
  (`simple_output_eq`).
* **Aggregation (22.3)–(22.7)**: `Y = (c/γ)M` (`eq_22_3`); with `A` of (22.6),
  `A = (c/γ)M^{1−γ}` (`simple_A_eq`) and `Y = AM^γ` (`eq_22_7_M`); input-market clearing
  `X = ∫ mᵢx* = Mx*` gives `F(X) = M` and `Y = AF(X)^γ` (`eq_22_7`).
* **The planner**: no reallocation of the total `M` raises output (`simple_planner`).
* **Footnote 2** (Cobb–Douglas `F = k^αℓ^{1−α}`): the unit cost `(r/α)^α(w/(1−α))^{1−α}` and the
  cost-minimising unit input (`cobbDouglas_unit_cost`), and the equilibrium factor prices
  (`simple_footnote_2`).
-/

open MeasureTheory

namespace AKMM.HeterogeneousFirms

/-! ### Two-stage cost minimisation -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- AKMM, p. 664: **the first stage scales**. Let `F` be homogeneous of degree one on a cone `D`
and let `x* ∈ D` minimise the cost `p(x)` on `{x ∈ D | F x = 1}` with unit cost `c = p(x*)`.
Then for `m > 0`, `m x*` produces `m`, costs `cm`, and every `x ∈ D` with `F x = m` costs at
least `cm`. -/
theorem twostage_cost {F : E → ℝ} {p : E →ₗ[ℝ] ℝ} {D : Set E}
    (hD : ∀ t : ℝ, 0 < t → ∀ x ∈ D, t • x ∈ D)
    (hF : ∀ t : ℝ, 0 < t → ∀ x ∈ D, F (t • x) = t * F x) {xs : E} (hxs : xs ∈ D)
    (hF1 : F xs = 1) (hmin : ∀ x ∈ D, F x = 1 → p xs ≤ p x) {m : ℝ} (hm : 0 < m) :
    m • xs ∈ D ∧ F (m • xs) = m ∧ p (m • xs) = p xs * m ∧
      ∀ x ∈ D, F x = m → p xs * m ≤ p x := by
  refine ⟨hD m hm xs hxs, by rw [hF m hm xs hxs, hF1, mul_one], by
    rw [map_smul, smul_eq_mul, mul_comm], fun x hx hFx => ?_⟩
  have hm' : 0 < m⁻¹ := inv_pos.mpr hm
  have h1 : F (m⁻¹ • x) = 1 := by rw [hF _ hm' x hx, hFx, inv_mul_cancel₀ hm.ne']
  have h2 := hmin _ (hD _ hm' x hx) h1
  rw [map_smul, smul_eq_mul] at h2
  have h3 := mul_le_mul_of_nonneg_right h2 hm.le
  rwa [mul_comm m⁻¹, mul_assoc, inv_mul_cancel₀ hm.ne', mul_one] at h3

/-- AKMM, p. 664: **the second stage**. With `x*` as in `twostage_cost`, nonnegative costs and
`F ≥ 0` on `D`, every input choice `x ∈ D` earns at most the scale profit `amᵞ − cm` at
`m = F(x)`. -/
theorem twostage_profit_le {F : E → ℝ} {p : E →ₗ[ℝ] ℝ} {D : Set E}
    (hD : ∀ t : ℝ, 0 < t → ∀ x ∈ D, t • x ∈ D)
    (hF : ∀ t : ℝ, 0 < t → ∀ x ∈ D, F (t • x) = t * F x) {xs : E} (hxs : xs ∈ D)
    (hF1 : F xs = 1) (hmin : ∀ x ∈ D, F x = 1 → p xs ≤ p x) (hp0 : ∀ x ∈ D, 0 ≤ p x)
    (hF0 : ∀ x ∈ D, 0 ≤ F x) {a γ : ℝ} {x : E} (hx : x ∈ D) :
    a * F x ^ γ - p x ≤ a * F x ^ γ - p xs * F x := by
  rcases (hF0 x hx).lt_or_eq with h | h
  · linarith [(twostage_cost hD hF hxs hF1 hmin h).2.2.2 x hx rfl]
  · rw [← h, mul_zero]
    linarith [hp0 x hx]

/-- AKMM, p. 664: the scaled unit input `m x*` attains the scale profit `amᵞ − cm`. -/
theorem twostage_profit_eq {F : E → ℝ} {p : E →ₗ[ℝ] ℝ} {D : Set E}
    (hD : ∀ t : ℝ, 0 < t → ∀ x ∈ D, t • x ∈ D)
    (hF : ∀ t : ℝ, 0 < t → ∀ x ∈ D, F (t • x) = t * F x) {xs : E} (hxs : xs ∈ D)
    (hF1 : F xs = 1) (hmin : ∀ x ∈ D, F x = 1 → p xs ≤ p x) {a γ m : ℝ} (hm : 0 < m) :
    a * F (m • xs) ^ γ - p (m • xs) = a * m ^ γ - p xs * m := by
  obtain ⟨-, h1, h2, -⟩ := twostage_cost hD hF hxs hF1 hmin hm
  rw [h1, h2]

/-! ### The scale problem (22.1)–(22.2) -/

/-- The optimal scale `m* = (γa/c)^{1/(1−γ)}` of a firm with productivity `a`. -/
noncomputable def simpleScale (γ c a : ℝ) : ℝ := (γ * a / c) ^ (1 / (1 - γ))

theorem simple_scale_pos {γ c a : ℝ} (hc : 0 < c) (hγ : 0 < γ) (ha : 0 < a) :
    0 < simpleScale γ c a :=
  Real.rpow_pos_of_pos (div_pos (mul_pos hγ ha) hc) _

/-- `m*^{1−γ} = γa/c`. -/
theorem simple_scale_rpow {γ c a : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1) (ha : 0 < a) :
    simpleScale γ c a ^ (1 - γ) = γ * a / c := by
  unfold simpleScale
  rw [← Real.rpow_mul (div_pos (mul_pos hγ ha) hc).le, one_div,
    inv_mul_cancel₀ (by linarith : (1 - γ) ≠ 0), Real.rpow_one]

/-- AKMM, (22.2), p. 664: the first-order condition `a m^{γ−1} = c/γ` holds at `m*`, and it
characterises `m*` among positive scales. -/
theorem eq_22_2 {γ c a m : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1) (ha : 0 < a)
    (hm : 0 < m) : a * m ^ (γ - 1) = c / γ ↔ m = simpleScale γ c a := by
  have h1γ : (1 - γ) ≠ 0 := by linarith
  have hmγ : m ^ (γ - 1) = (m ^ (1 - γ))⁻¹ := by
    rw [← Real.rpow_neg hm.le, neg_sub]
  constructor
  · intro h
    have h' : m ^ (1 - γ) = γ * a / c := by
      rw [hmγ] at h
      have hpos : 0 < m ^ (1 - γ) := Real.rpow_pos_of_pos hm _
      field_simp at h ⊢
      linarith
    unfold simpleScale
    rw [← h', ← Real.rpow_mul hm.le, one_div, mul_inv_cancel₀ h1γ, Real.rpow_one]
  · rintro rfl
    rw [hmγ, simple_scale_rpow hc hγ hγ1 ha]
    field_simp

/-- AKMM, (22.1), p. 664: `m*` maximises the scale profit `amᵞ − cm` over `m ≥ 0`. -/
theorem eq_22_1 {γ c a m : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1) (ha : 0 < a)
    (hm : 0 ≤ m) : a * m ^ γ - c * m ≤
      a * simpleScale γ c a ^ γ - c * simpleScale γ c a := by
  set d := simpleScale γ c a
  have hd : 0 < d := simple_scale_pos hc hγ ha
  have hfoc : a * d ^ (γ - 1) = c / γ := (eq_22_2 hc hγ hγ1 ha hd).2 rfl
  have ht := Miao.NewKeynesian.nk_rpow_tangent hγ hγ1 hm hd
  have hdd : d ^ γ = d * d ^ (γ - 1) := by
    rw [mul_comm, ← Real.rpow_add_one hd.ne']; ring_nf
  have key : a * (γ * m * d ^ (γ - 1) + (1 - γ) * d ^ γ) =
      c * m + (1 - γ) * (a * d ^ γ) := by
    have : a * d ^ (γ - 1) * γ = c := by rw [hfoc]; field_simp
    linear_combination m * this
  have hcd : c * d = γ * (a * d ^ γ) := by
    have : a * d ^ (γ - 1) * γ = c := by rw [hfoc]; field_simp
    rw [hdd, ← this]; ring
  nlinarith [mul_le_mul_of_nonneg_left ht ha.le]

/-- AKMM, p. 664, after (22.2): at the optimum `y = am*^γ = (c/γ)m*`. -/
theorem simple_output_eq {γ c a : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1) (ha : 0 < a) :
    a * simpleScale γ c a ^ γ = c / γ * simpleScale γ c a := by
  set d := simpleScale γ c a
  have hd : 0 < d := simple_scale_pos hc hγ ha
  have hfoc : a * d ^ (γ - 1) = c / γ := (eq_22_2 hc hγ hγ1 ha hd).2 rfl
  have hdd : d ^ γ = d * d ^ (γ - 1) := by
    rw [mul_comm, ← Real.rpow_add_one hd.ne']; ring_nf
  rw [← hfoc, hdd]; ring

/-! ### Aggregation (22.3)–(22.7) -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- AKMM, (22.6), p. 665: aggregate productivity `A = (∫ a^{1/(1−γ)})^{1−γ}`. -/
noncomputable def aggTFP (P : Measure Ω) (γ : ℝ) (a : Ω → ℝ) : ℝ :=
  (∫ ω, a ω ^ (1 / (1 - γ)) ∂P) ^ (1 - γ)

/-- `m*` is `(γ/c)^{1/(1−γ)} a^{1/(1−γ)}`. -/
theorem simple_scale_eq {γ c a : ℝ} (hc : 0 < c) (hγ : 0 < γ) (ha : 0 < a) :
    simpleScale γ c a = (γ / c) ^ (1 / (1 - γ)) * a ^ (1 / (1 - γ)) := by
  unfold simpleScale
  rw [← Real.mul_rpow (div_pos hγ hc).le ha.le]; ring_nf

/-- The aggregate combined input `M = ∫ m*ᵢ = (γ/c)^{1/(1−γ)} ∫ a^{1/(1−γ)}`. -/
theorem simple_M_eq (P : Measure Ω) {γ c : ℝ} (hc : 0 < c) (hγ : 0 < γ) {a : Ω → ℝ}
    (ha : ∀ ω, 0 < a ω) :
    ∫ ω, simpleScale γ c (a ω) ∂P = (γ / c) ^ (1 / (1 - γ)) * ∫ ω, a ω ^ (1 / (1 - γ)) ∂P := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => simple_scale_eq hc hγ (ha ω))

/-- AKMM, (22.3)–(22.5), p. 664: total output `Y = ∫ aᵢm*ᵢ^γ` equals `(c/γ)M`. -/
theorem eq_22_3 (P : Measure Ω) {γ c : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1)
    {a : Ω → ℝ} (ha : ∀ ω, 0 < a ω) :
    ∫ ω, a ω * simpleScale γ c (a ω) ^ γ ∂P = c / γ * ∫ ω, simpleScale γ c (a ω) ∂P := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    simple_output_eq hc hγ hγ1 (ha ω))

/-- AKMM, p. 665, from (22.2) and (22.6): `A = (c/γ)M^{1−γ}`, for `∫ a^{1/(1−γ)} > 0`. -/
theorem simple_A_eq (P : Measure Ω) {γ c : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1)
    {a : Ω → ℝ} (ha : ∀ ω, 0 < a ω) (hI : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) ∂P) :
    aggTFP P γ a = c / γ * (∫ ω, simpleScale γ c (a ω) ∂P) ^ (1 - γ) := by
  rw [simple_M_eq P hc hγ ha, Real.mul_rpow (by positivity) hI.le,
    ← Real.rpow_mul (div_pos hγ hc).le, one_div, inv_mul_cancel₀ (by linarith : (1 - γ) ≠ 0),
    Real.rpow_one, aggTFP, ← mul_assoc, div_mul_div_comm, mul_comm c γ,
    div_self (mul_pos hγ hc).ne', one_mul, one_div]

/-- AKMM, (22.7), p. 665, in terms of `M`: `Y = AM^γ`. -/
theorem eq_22_7_M (P : Measure Ω) {γ c : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1)
    {a : Ω → ℝ} (ha : ∀ ω, 0 < a ω) (hI : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) ∂P) :
    ∫ ω, a ω * simpleScale γ c (a ω) ^ γ ∂P =
      aggTFP P γ a * (∫ ω, simpleScale γ c (a ω) ∂P) ^ γ := by
  have hM : 0 < ∫ ω, simpleScale γ c (a ω) ∂P := by
    rw [simple_M_eq P hc hγ ha]; positivity
  rw [eq_22_3 P hc hγ hγ1 ha, simple_A_eq P hc hγ hγ1 ha hI, mul_assoc,
    ← Real.rpow_add hM]
  ring_nf
  rw [Real.rpow_one]

/-- AKMM, (22.7), p. 665: **the aggregate production function**. Each firm uses
`xᵢ = m*ᵢx*` with `F(x*) = 1`; if the input market clears, `X = ∫ m*ᵢx* = Mx*`, then
`F(X) = M` and `Y = AF(X)^γ`. -/
theorem eq_22_7 {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    (P : Measure Ω) {γ c : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1) {a : Ω → ℝ}
    (ha : ∀ ω, 0 < a ω) (hI : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) ∂P) {F : E' → ℝ} {D : Set E'}
    (hF : ∀ t : ℝ, 0 < t → ∀ x ∈ D, F (t • x) = t * F x) {xs X : E'} (hxs : xs ∈ D)
    (hF1 : F xs = 1) (hX : X = ∫ ω, simpleScale γ c (a ω) • xs ∂P) :
    F X = ∫ ω, simpleScale γ c (a ω) ∂P ∧
      ∫ ω, a ω * simpleScale γ c (a ω) ^ γ ∂P = aggTFP P γ a * F X ^ γ := by
  have hM : 0 < ∫ ω, simpleScale γ c (a ω) ∂P := by
    rw [simple_M_eq P hc hγ ha]; positivity
  have hFX : F X = ∫ ω, simpleScale γ c (a ω) ∂P := by
    rw [hX, integral_smul_const, hF _ hM xs hxs, hF1, mul_one]
  exact ⟨hFX, by rw [hFX]; exact eq_22_7_M P hc hγ hγ1 ha hI⟩

/-- AKMM, p. 665: **the competitive allocation is efficient**. Any other allocation `m ≥ 0` of
the same total `∫ m = M` produces at most `Y = ∫ a m*^γ`: inputs cannot be reallocated to raise
output. -/
theorem simple_planner (P : Measure Ω) {γ c : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1)
    {a m : Ω → ℝ} (ha : ∀ ω, 0 < a ω) (hm : ∀ ω, 0 ≤ m ω)
    (hmI : Integrable m P) (hsI : Integrable (fun ω => simpleScale γ c (a ω)) P)
    (hYI : Integrable (fun ω => a ω * simpleScale γ c (a ω) ^ γ) P)
    (hyI : Integrable (fun ω => a ω * m ω ^ γ) P)
    (hMM : ∫ ω, m ω ∂P = ∫ ω, simpleScale γ c (a ω) ∂P) :
    ∫ ω, a ω * m ω ^ γ ∂P ≤ ∫ ω, a ω * simpleScale γ c (a ω) ^ γ ∂P := by
  have hpt : ∀ ω, a ω * m ω ^ γ ≤
      a ω * simpleScale γ c (a ω) ^ γ + c * (m ω - simpleScale γ c (a ω)) := fun ω => by
    linarith [eq_22_1 hc hγ hγ1 (ha ω) (hm ω)]
  have h2 : Integrable (fun ω => c * (m ω - simpleScale γ c (a ω))) P :=
    (hmI.sub hsI).const_mul c
  have h : ∫ ω, a ω * m ω ^ γ ∂P ≤ ∫ ω, (a ω * simpleScale γ c (a ω) ^ γ +
      c * (m ω - simpleScale γ c (a ω))) ∂P := integral_mono hyI (hYI.add h2) hpt
  rw [integral_add hYI h2, integral_const_mul, integral_sub hmI hsI, hMM, sub_self, mul_zero,
    add_zero] at h
  exact h

/-! ### Footnote 2: Cobb–Douglas -/

/-- AKMM, p. 665, footnote 2: **the Cobb–Douglas unit cost**. With `F(k, ℓ) = k^αℓ^{1−α}` and
factor prices `r, w > 0`, every `(k, ℓ) ≥ 0` costs at least `c F(k, ℓ)`, where
`c = (r/α)^α(w/(1−α))^{1−α}`; the unit input `(αc/r, (1−α)c/w)` produces one unit at cost `c`. -/
theorem cobbDouglas_unit_cost {α r w k l : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r)
    (hw : 0 < w) (hk : 0 ≤ k) (hl : 0 ≤ l) :
    (r / α) ^ α * (w / (1 - α)) ^ (1 - α) * (k ^ α * l ^ (1 - α)) ≤ r * k + w * l ∧
      (α * ((r / α) ^ α * (w / (1 - α)) ^ (1 - α)) / r) ^ α *
        ((1 - α) * ((r / α) ^ α * (w / (1 - α)) ^ (1 - α)) / w) ^ (1 - α) = 1 ∧
      r * (α * ((r / α) ^ α * (w / (1 - α)) ^ (1 - α)) / r) +
        w * ((1 - α) * ((r / α) ^ α * (w / (1 - α)) ^ (1 - α)) / w) =
        (r / α) ^ α * (w / (1 - α)) ^ (1 - α) := by
  have h1α : 0 < 1 - α := by linarith
  set c := (r / α) ^ α * (w / (1 - α)) ^ (1 - α) with hc
  have hra : 0 < r / α := div_pos hr hα
  have hwa : 0 < w / (1 - α) := div_pos hw h1α
  have hc0 : 0 < c := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have h := Real.geom_mean_le_arith_mean2_weighted hα.le h1α.le
      (mul_nonneg hra.le hk) (mul_nonneg hwa.le hl) (by ring)
    rw [Real.mul_rpow hra.le hk, Real.mul_rpow hwa.le hl] at h
    have e : α * (r / α * k) + (1 - α) * (w / (1 - α) * l) = r * k + w * l := by
      field_simp
    calc c * (k ^ α * l ^ (1 - α))
        = (r / α) ^ α * k ^ α * ((w / (1 - α)) ^ (1 - α) * l ^ (1 - α)) := by rw [hc]; ring
      _ ≤ _ := h
      _ = r * k + w * l := e
  · have e1 : α * c / r = c / (r / α) := by field_simp
    have e2 : (1 - α) * c / w = c / (w / (1 - α)) := by field_simp
    rw [e1, e2, Real.div_rpow hc0.le hra.le, Real.div_rpow hc0.le hwa.le, div_mul_div_comm,
      ← Real.rpow_add hc0, add_sub_cancel, Real.rpow_one, hc, div_self]
    positivity
  · field_simp
    ring

/-- AKMM, p. 665, footnote 2: **equilibrium factor prices**. In the Cobb–Douglas case, if each
firm uses the cost-minimising unit input `(k*, ℓ*) = (αc/r, (1−α)c/w)`, the factor markets
clear (`K = Mk*`, `L = Mℓ*`) and `c/γ = AM^{γ−1}` (from `A = (c/γ)M^{1−γ}`), then
`r = γαA(K^αL^{1−α})^{γ−1}K^{α−1}L^{1−α}` and `w = γ(1−α)A(K^αL^{1−α})^{γ−1}K^αL^{−α}`. -/
theorem simple_footnote_2 {α γ A c r w M K L : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r)
    (hw : 0 < w) (hc : 0 < c) (hγ : 0 < γ) (hM : 0 < M)
    (hK : K = M * (α * c / r)) (hL : L = M * ((1 - α) * c / w))
    (hFM : K ^ α * L ^ (1 - α) = M) (hA : c / γ = A * M ^ (γ - 1)) :
    r = γ * α * A * (K ^ α * L ^ (1 - α)) ^ (γ - 1) * K ^ (α - 1) * L ^ (1 - α) ∧
      w = γ * (1 - α) * A * (K ^ α * L ^ (1 - α)) ^ (γ - 1) * K ^ α * L ^ (-α) := by
  have h1α : 0 < 1 - α := by linarith
  have hK0 : 0 < K := by rw [hK]; positivity
  have hL0 : 0 < L := by rw [hL]; positivity
  have hcA : c = γ * (A * M ^ (γ - 1)) := by rw [← hA]; field_simp
  rw [hFM]
  have eK : K ^ (α - 1) = K ^ α / K := by rw [Real.rpow_sub_one hK0.ne']
  have eL : L ^ (-α) = L ^ (1 - α) / L := by
    rw [show (-α) = (1 - α) - 1 by ring, Real.rpow_sub_one hL0.ne']
  constructor
  · rw [eK]
    have : r = α * c * M / K := by rw [hK]; field_simp
    rw [this, hcA]
    have hM' : M = K ^ α * L ^ (1 - α) := hFM.symm
    calc α * (γ * (A * M ^ (γ - 1))) * M / K
        = γ * α * A * M ^ (γ - 1) * (K ^ α * L ^ (1 - α)) / K := by rw [← hM']; ring
      _ = _ := by ring
  · rw [eL]
    have : w = (1 - α) * c * M / L := by rw [hL]; field_simp
    rw [this, hcA]
    have hM' : M = K ^ α * L ^ (1 - α) := hFM.symm
    calc (1 - α) * (γ * (A * M ^ (γ - 1))) * M / L
        = γ * (1 - α) * A * M ^ (γ - 1) * (K ^ α * L ^ (1 - α)) / L := by rw [← hM']; ring
      _ = _ := by ring

end AKMM.HeterogeneousFirms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lognormal productivity and wedges (AKMM (22.8), (22.10)–(22.11), App. 22.A.1, 22.A.3)

AKMM, §22.2, p. 665, §22.4, pp. 672–673, and Appendix 22.A.1 and 22.A.3, pp. 888–892. The unit
mass of firms is a probability space `(Ω, P)`, and the book's appeal to the law of large numbers
(`∫ · di = E[·]`) is the identification of the cross-section integral with `∫ · ∂P`.

* **(22.8)** and App. 22.A.1: if `log a ∼ N(ν − σ²/2, σ²)` then `∫ a = e^ν` and
  `A = exp(ν + γσ²/(2(1−γ)))` (`lognormal_mean`, `eq_22_8`); at fixed mean, `A` is strictly
  increasing in the dispersion `σ²` (`lognormal_A_strictMono`).
* **For any distribution**: `A ≥ ∫ a` (`aggTFP_ge_mean`), the general form of "dispersion raises
  `A`".
* **(22.10)–(22.11)** and App. 22.A.3: the normal fact used (the moment generating function of
  `αX + βY` for a bivariate normal `(X, Y)`, `bivariate_mgf`); with
  `(log a, log(1−τ))` bivariate normal with means `(ν_a − σ_a²/2, ν_τ − σ_τ²/2)`,
  `A = exp(ν_a + γ(σ_a² − σ_τ²)/(2(1−γ)))` (`eq_22_11`); `A` depends neither on `ν_τ` nor on
  the correlation (`wedge_A_indep`) and is strictly decreasing in `σ_τ²` (`wedge_A_strictAnti`).
-/

open MeasureTheory ProbabilityTheory

namespace AKMM.HeterogeneousFirms

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### (22.8) -/

/-- AKMM, p. 665: for `log a ∼ N(ν − σ²/2, σ²)` the mean productivity is `∫ a = e^ν`. -/
theorem lognormal_mean {P : Measure Ω} {Z : Ω → ℝ} {ν : ℝ} {v : NNReal}
    (hZ : HasLaw Z (gaussianReal (ν - v / 2) v) P) :
    ∫ ω, Real.exp (Z ω) ∂P = Real.exp ν := by
  have h := mgf_gaussianReal hZ 1
  simp only [mgf, one_mul, one_pow, mul_one] at h
  rw [h]; congr 1; ring

/-- AKMM, (22.8), p. 665 and App. 22.A.1, p. 888: for `log a ∼ N(ν − σ²/2, σ²)`,
`A = (∫ a^{1/(1−γ)})^{1−γ} = exp(ν + γσ²/(2(1−γ)))`. -/
theorem eq_22_8 {P : Measure Ω} {Z : Ω → ℝ} {ν γ : ℝ} {v : NNReal} (hγ1 : γ < 1)
    (hZ : HasLaw Z (gaussianReal (ν - v / 2) v) P) :
    aggTFP P γ (fun ω => Real.exp (Z ω)) = Real.exp (ν + γ / (1 - γ) * (1 / 2) * v) := by
  have h1γ : (1 - γ) ≠ 0 := by linarith
  have h := mgf_gaussianReal hZ (1 / (1 - γ))
  have e : ∀ ω, Real.exp (Z ω) ^ (1 / (1 - γ)) = Real.exp (1 / (1 - γ) * Z ω) := fun ω => by
    rw [← Real.exp_mul, mul_comm]
  unfold aggTFP
  simp only [e]
  rw [show (∫ ω, Real.exp (1 / (1 - γ) * Z ω) ∂P) = mgf Z P (1 / (1 - γ)) from rfl, h,
    ← Real.exp_mul]
  congr 1
  field_simp
  ring

/-- AKMM, p. 665: **dispersion raises `A` at a fixed mean**. With `log a ∼ N(ν − σ²/2, σ²)`
(mean `e^ν` for every `σ`), the closed form of `A` is strictly increasing in `σ²`. -/
theorem lognormal_A_strictMono {ν γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    StrictMono fun s : ℝ => Real.exp (ν + γ / (1 - γ) * (1 / 2) * s) := by
  have hk : 0 < γ / (1 - γ) * (1 / 2) := by
    have : 0 < 1 - γ := by linarith
    positivity
  intro s t hst
  simp only
  rw [Real.exp_lt_exp]
  nlinarith

/-- AKMM, p. 665: **`A` is at least mean productivity**, for any distribution: with `a > 0`,
`p = 1/(1−γ) > 1`, `∫ a > 0` and `a`, `a^p` integrable, `(∫ a^p)^{1/p} ≥ ∫ a` (Jensen). -/
theorem aggTFP_ge_mean {P : Measure Ω} [IsProbabilityMeasure P] {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ < 1) {a : Ω → ℝ} (ha : ∀ ω, 0 < a ω) (haI : Integrable a P)
    (hpI : Integrable (fun ω => a ω ^ (1 / (1 - γ))) P) :
    ∫ ω, a ω ∂P ≤ aggTFP P γ a := by
  set m := ∫ ω, a ω ∂P with hm
  have hm0 : 0 < m := integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => (ha ω).le) haI |>.mpr (by
      have : Function.support a = Set.univ := Set.eq_univ_of_forall fun ω => (ha ω).ne'
      rw [this]; simp)
  have h1γ : 0 < 1 - γ := by linarith
  set p := 1 / (1 - γ) with hp
  have hp1 : 1 ≤ p := by rw [hp, le_div_iff₀ h1γ]; linarith
  -- Bernoulli: (a/m)^p ≥ 1 + p(a/m − 1)
  have hpt : ∀ ω, m ^ p * (1 + p * (a ω / m - 1)) ≤ a ω ^ p := fun ω => by
    have hb := one_add_mul_self_le_rpow_one_add (by
      have : 0 ≤ a ω / m := (div_pos (ha ω) hm0).le
      linarith : (-1 : ℝ) ≤ a ω / m - 1) hp1
    rw [add_sub_cancel, Real.div_rpow (ha ω).le hm0.le] at hb
    have hmp : 0 < m ^ p := Real.rpow_pos_of_pos hm0 p
    calc m ^ p * (1 + p * (a ω / m - 1)) ≤ m ^ p * (a ω ^ p / m ^ p) :=
          mul_le_mul_of_nonneg_left hb hmp.le
      _ = a ω ^ p := by field_simp
  have hlin : Integrable (fun ω => m ^ p * (1 + p * (a ω / m - 1))) P :=
    ((integrable_const 1).add (((haI.div_const m).sub (integrable_const 1)).const_mul p)).const_mul
      _
  have hI := integral_mono hlin hpI hpt
  have hval : ∫ ω, m ^ p * (1 + p * (a ω / m - 1)) ∂P = m ^ p := by
    have h2 : ∀ ω, m ^ p * (1 + p * (a ω / m - 1)) = m ^ p * (1 - p) + m ^ p * p / m * a ω :=
      fun ω => by field_simp; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall h2),
      integral_add (integrable_const _) (haI.const_mul _), integral_const, integral_const_mul,
      ← hm]
    simp only [probReal_univ, one_smul]
    field_simp
    ring
  rw [hval] at hI
  unfold aggTFP
  have := Real.rpow_le_rpow (Real.rpow_pos_of_pos hm0 p).le hI h1γ.le
  rwa [← Real.rpow_mul hm0.le, hp, one_div, inv_mul_cancel₀ h1γ.ne', Real.rpow_one,
    ← one_div] at this

/-! ### Bivariate normal and (22.11) -/

/-- AKMM, App. 22.A.3, p. 889: **the normal fact used**. If `(X, Y)` is jointly Gaussian then
`E[exp(αX + βY)] = exp(αE X + βE Y + (α² Var X + 2αβ Cov(X, Y) + β² Var Y)/2)`: `αX + βY` is
normal with that mean and variance. -/
theorem bivariate_mgf {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) (α β : ℝ) :
    ∫ ω, Real.exp (α * X ω + β * Y ω) ∂P = Real.exp (α * P[X] + β * P[Y] +
      (α ^ 2 * Var[X; P] + 2 * α * β * cov[X, Y; P] + β ^ 2 * Var[Y; P]) / 2) := by
  have hX := hXY.fst
  have hY := hXY.snd
  set L : ℝ × ℝ →L[ℝ] ℝ := α • ContinuousLinearMap.fst ℝ ℝ ℝ +
    β • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hZ' := hXY.map_fun L
  have eZ : (fun ω => L (X ω, Y ω)) = fun ω => α * X ω + β * Y ω := by
    funext ω; simp [L]
  rw [eZ] at hZ'
  have hαX : MemLp (fun ω => α * X ω) 2 P := hX.memLp_two.const_mul α
  have hβY : MemLp (fun ω => β * Y ω) 2 P := hY.memLp_two.const_mul β
  have hmean : P[fun ω => α * X ω + β * Y ω] = α * P[X] + β * P[Y] := by
    rw [integral_add (hX.integrable.const_mul α) (hY.integrable.const_mul β),
      integral_const_mul, integral_const_mul]
  have hvar : Var[fun ω => α * X ω + β * Y ω; P] =
      α ^ 2 * Var[X; P] + 2 * α * β * cov[X, Y; P] + β ^ 2 * Var[Y; P] := by
    rw [variance_fun_add hαX hβY, variance_const_mul, variance_const_mul,
      covariance_const_mul_left, covariance_const_mul_right]
    ring
  have hlaw := hZ'.map_eq_gaussianReal
  have hmg : mgf (fun ω => α * X ω + β * Y ω) P 1 = ∫ ω, Real.exp (α * X ω + β * Y ω) ∂P := by
    simp [mgf]
  rw [← hmg, ← mgf_id_map hZ'.aemeasurable, hlaw, mgf_id_gaussianReal, hmean, hvar,
    Real.coe_toNNReal _ (by rw [← hvar]; exact variance_nonneg _ _)]
  ring_nf

/-- AKMM, (22.10), p. 672: aggregate productivity with output wedges `τ`,
`A = ∫ a^{1/(1−γ)}(1−τ)^{γ/(1−γ)} / (∫ a^{1/(1−γ)}(1−τ)^{1/(1−γ)})^γ`, written with `b = 1 − τ`. -/
noncomputable def wedgeTFP (P : Measure Ω) (γ : ℝ) (a b : Ω → ℝ) : ℝ :=
  (∫ ω, a ω ^ (1 / (1 - γ)) * b ω ^ (γ / (1 - γ)) ∂P) /
    (∫ ω, a ω ^ (1 / (1 - γ)) * b ω ^ (1 / (1 - γ)) ∂P) ^ γ

/-- AKMM, p. 672: with no wedges (`τ ≡ 0`, `b ≡ 1`), (22.10) reduces to (22.6). -/
theorem wedgeTFP_one (P : Measure Ω) {γ : ℝ} {a : Ω → ℝ}
    (hI : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) ∂P) :
    wedgeTFP P γ a (fun _ => 1) = aggTFP P γ a := by
  unfold wedgeTFP aggTFP
  simp only [Real.one_rpow, mul_one]
  rw [Real.rpow_sub hI, Real.rpow_one]

/-- The exponent algebra behind (22.11). -/
theorem wedge_exponent {γ νa ντ va vτ cv : ℝ} (hγ1 : γ < 1) :
    1 / (1 - γ) * (νa - va / 2) + γ / (1 - γ) * (ντ - vτ / 2) +
        ((1 / (1 - γ)) ^ 2 * va + 2 * (1 / (1 - γ)) * (γ / (1 - γ)) * cv +
          (γ / (1 - γ)) ^ 2 * vτ) / 2 -
      γ * (1 / (1 - γ) * (νa - va / 2) + 1 / (1 - γ) * (ντ - vτ / 2) +
        ((1 / (1 - γ)) ^ 2 * va + 2 * (1 / (1 - γ)) * (1 / (1 - γ)) * cv +
          (1 / (1 - γ)) ^ 2 * vτ) / 2) =
      νa + γ / (1 - γ) * (1 / 2) * (va - vτ) := by
  have h1γ : (1 - γ) ≠ 0 := by linarith
  field_simp
  ring

/-- AKMM, (22.11), p. 672 and App. 22.A.3, pp. 889–892: if `(log a, log(1−τ))` is bivariate
normal with means `(ν_a − σ_a²/2, ν_τ − σ_τ²/2)`, variances `(σ_a², σ_τ²)` and covariance
`ρσ_aσ_τ`, then `A = exp(ν_a + γ(σ_a² − σ_τ²)/(2(1−γ)))`. -/
theorem eq_22_11 {P : Measure Ω} [IsProbabilityMeasure P] {X T : Ω → ℝ}
    (hXT : HasGaussianLaw (fun ω => (X ω, T ω)) P) {γ νa ντ : ℝ} (hγ1 : γ < 1)
    (hmX : P[X] = νa - Var[X; P] / 2) (hmT : P[T] = ντ - Var[T; P] / 2) :
    wedgeTFP P γ (fun ω => Real.exp (X ω)) (fun ω => Real.exp (T ω)) =
      Real.exp (νa + γ / (1 - γ) * (1 / 2) * (Var[X; P] - Var[T; P])) := by
  have e : ∀ (x t p q : ℝ), Real.exp x ^ p * Real.exp t ^ q = Real.exp (p * x + q * t) :=
    fun x t p q => by rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]; ring_nf
  unfold wedgeTFP
  simp only [e]
  rw [bivariate_mgf hXT, bivariate_mgf hXT, ← Real.exp_mul, ← Real.exp_sub, hmX, hmT]
  congr 1
  rw [← wedge_exponent hγ1]
  ring

/-- AKMM, p. 673: in the lognormal case `A` does not depend on `ν_τ` (the level of the wedge does
not distort the allocation) nor on the correlation `ρ` between `a` and `1 − τ`. -/
theorem wedge_A_indep {P : Measure Ω} [IsProbabilityMeasure P] {X T X' T' : Ω → ℝ}
    (hXT : HasGaussianLaw (fun ω => (X ω, T ω)) P)
    (hXT' : HasGaussianLaw (fun ω => (X' ω, T' ω)) P) {γ νa ντ ντ' : ℝ} (hγ1 : γ < 1)
    (hmX : P[X] = νa - Var[X; P] / 2) (hmT : P[T] = ντ - Var[T; P] / 2)
    (hmX' : P[X'] = νa - Var[X'; P] / 2) (hmT' : P[T'] = ντ' - Var[T'; P] / 2)
    (hvX : Var[X'; P] = Var[X; P]) (hvT : Var[T'; P] = Var[T; P]) :
    wedgeTFP P γ (fun ω => Real.exp (X' ω)) (fun ω => Real.exp (T' ω)) =
      wedgeTFP P γ (fun ω => Real.exp (X ω)) (fun ω => Real.exp (T ω)) := by
  rw [eq_22_11 hXT hγ1 hmX hmT, eq_22_11 hXT' hγ1 hmX' hmT', hvX, hvT]

/-- AKMM, p. 673: **wedge dispersion lowers `A`**: the closed form (22.11) is strictly decreasing
in `σ_τ²`, and equals (22.8) at `σ_τ = 0`. -/
theorem wedge_A_strictAnti {νa γ va : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    StrictAnti (fun vτ : ℝ => Real.exp (νa + γ / (1 - γ) * (1 / 2) * (va - vτ))) ∧
      Real.exp (νa + γ / (1 - γ) * (1 / 2) * (va - 0)) =
        Real.exp (νa + γ / (1 - γ) * (1 / 2) * va) := by
  have hk : 0 < γ / (1 - γ) * (1 / 2) := by
    have : 0 < 1 - γ := by linarith
    positivity
  refine ⟨fun s t hst => ?_, by rw [sub_zero]⟩
  simp only
  rw [Real.exp_lt_exp]
  nlinarith

end AKMM.HeterogeneousFirms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Reallocation and misallocation (AKMM §22.3–22.4)

AKMM, §22.3, pp. 668–669 ((22.9)), §22.4, pp. 671–673, and footnote 14, p. 676.

* **Job flows (22.9)**: job creation minus job destruction is the net change in employment,
  `JC − JD = (L_t − L_{t−1})/L̄_t` (`jobflows_net`); in a steady state `JC = JD` (footnote 14,
  `jobflows_steady`).
* **The FHK decomposition** (p. 671): the exact identity for the change in output-weighted
  productivity with continuers, entrants and exiters (`fhk_decomposition`); without share changes,
  entry or exit only within-firm growth remains (`fhk_within_only`).
* **The planner bound**: any allocation of total input `M` produces at most `AM^γ`
  (`simple_planner_A`).
* **Wedges (22.10)**: firms facing output taxes `τ` choose `m = m*(γ, c, (1−τ)a)` and then
  `Y = AM^γ` with `A` of (22.10) (`eq_22_10`); **misallocation lowers TFP**: for every
  distribution of `(a, τ)`, `A` of (22.10) is at most `A` of (22.6) (`wedge_A_le`). The book
  shows this only for the lognormal case (22.11).
-/

open MeasureTheory

namespace AKMM.HeterogeneousFirms

/-! ### Job flows -/

/-- AKMM, (22.9), p. 669: job creation `Σ_{ℓ_t > ℓ_{t−1}} (ℓ_t − ℓ_{t−1}) / L̄`; entrants have
`ℓ_{t−1} = 0`, exiters `ℓ_t = 0`. -/
noncomputable def jobCreation {ι : Type*} (S : Finset ι) (l0 l1 : ι → ℝ) (Lbar : ℝ) : ℝ :=
  (∑ i ∈ S.filter (fun i => l0 i < l1 i), (l1 i - l0 i)) / Lbar

/-- AKMM, p. 669: job destruction `Σ_{ℓ_t < ℓ_{t−1}} (ℓ_{t−1} − ℓ_t) / L̄`. -/
noncomputable def jobDestruction {ι : Type*} (S : Finset ι) (l0 l1 : ι → ℝ) (Lbar : ℝ) : ℝ :=
  (∑ i ∈ S.filter (fun i => l1 i < l0 i), (l0 i - l1 i)) / Lbar

/-- AKMM, p. 669: **gross and net flows**. `JC − JD = (L_t − L_{t−1})/L̄`. -/
theorem jobflows_net {ι : Type*} (S : Finset ι) (l0 l1 : ι → ℝ) (Lbar : ℝ) :
    jobCreation S l0 l1 Lbar - jobDestruction S l0 l1 Lbar =
      (∑ i ∈ S, l1 i - ∑ i ∈ S, l0 i) / Lbar := by
  classical
  unfold jobCreation jobDestruction
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  have h1 : ∑ i ∈ S.filter (fun i => l0 i < l1 i), (l1 i - l0 i) =
      ∑ i ∈ S, if l0 i < l1 i then l1 i - l0 i else 0 := Finset.sum_filter _ _
  have h2 : ∑ i ∈ S.filter (fun i => l1 i < l0 i), (l0 i - l1 i) =
      ∑ i ∈ S, if l1 i < l0 i then l0 i - l1 i else 0 := Finset.sum_filter _ _
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases lt_trichotomy (l0 i) (l1 i) with h | h | h
  · simp [h, h.not_gt]
  · simp [h]
  · simp [h, h.not_gt]

/-- AKMM, p. 676, footnote 14: **in a steady state job creation equals job destruction**. -/
theorem jobflows_steady {ι : Type*} (S : Finset ι) (l0 l1 : ι → ℝ) (Lbar : ℝ)
    (hL : ∑ i ∈ S, l1 i = ∑ i ∈ S, l0 i) :
    jobCreation S l0 l1 Lbar = jobDestruction S l0 l1 Lbar := by
  have h := jobflows_net S l0 l1 Lbar
  rw [hL, sub_self, zero_div] at h
  linarith

/-! ### The Foster–Haltiwanger–Krizan decomposition -/

/-- AKMM, p. 671: **the FHK decomposition**. Let `C`, `N`, `X` be the continuing, entering and
exiting establishments, with output shares `s₀` (at `t−1`, on `C ∪ X`) and `s₁` (at `t`, on
`C ∪ N`) summing to one, and `Ā₀ = Σ_{C∪X} s₀a₀`, `Ā₁ = Σ_{C∪N} s₁a₁`. Then `Ā₁ − Ā₀` is the sum
of the within, between, cross, entry and exit terms. -/
theorem fhk_decomposition {ι : Type*} (C N X : Finset ι) (s0 s1 a0 a1 : ι → ℝ)
    (h0 : ∑ i ∈ C, s0 i + ∑ i ∈ X, s0 i = 1) (h1 : ∑ i ∈ C, s1 i + ∑ i ∈ N, s1 i = 1) :
    (∑ i ∈ C, s1 i * a1 i + ∑ i ∈ N, s1 i * a1 i) -
        (∑ i ∈ C, s0 i * a0 i + ∑ i ∈ X, s0 i * a0 i) =
      ∑ i ∈ C, s0 i * (a1 i - a0 i) +
        ∑ i ∈ C, (a0 i - (∑ j ∈ C, s0 j * a0 j + ∑ j ∈ X, s0 j * a0 j)) * (s1 i - s0 i) +
        ∑ i ∈ C, (a1 i - a0 i) * (s1 i - s0 i) +
        ∑ i ∈ N, s1 i * (a1 i - (∑ j ∈ C, s0 j * a0 j + ∑ j ∈ X, s0 j * a0 j)) -
        ∑ i ∈ X, s0 i * (a0 i - (∑ j ∈ C, s0 j * a0 j + ∑ j ∈ X, s0 j * a0 j)) := by
  set A0 := ∑ j ∈ C, s0 j * a0 j + ∑ j ∈ X, s0 j * a0 j
  have e1 : ∑ i ∈ C, (a0 i - A0) * (s1 i - s0 i) =
      ∑ i ∈ C, a0 i * (s1 i - s0 i) - A0 * (∑ i ∈ C, s1 i - ∑ i ∈ C, s0 i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ N, s1 i * (a1 i - A0) = ∑ i ∈ N, s1 i * a1 i - A0 * ∑ i ∈ N, s1 i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i ∈ X, s0 i * (a0 i - A0) = ∑ i ∈ X, s0 i * a0 i - A0 * ∑ i ∈ X, s0 i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : ∑ i ∈ C, s1 i * a1 i - ∑ i ∈ C, s0 i * a0 i =
      ∑ i ∈ C, s0 i * (a1 i - a0 i) + ∑ i ∈ C, a0 i * (s1 i - s0 i) +
        ∑ i ∈ C, (a1 i - a0 i) * (s1 i - s0 i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3]
  linear_combination e4 - A0 * h0 + A0 * h1

/-- AKMM, p. 672: without share changes and without entry or exit, the only source of growth in
`Ā` is within-establishment productivity growth. -/
theorem fhk_within_only {ι : Type*} (C : Finset ι) (s a0 a1 : ι → ℝ) :
    ∑ i ∈ C, s i * a1 i - ∑ i ∈ C, s i * a0 i = ∑ i ∈ C, s i * (a1 i - a0 i) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The planner bound and wedges -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- AKMM, p. 665: **the aggregate production function is a frontier**. For any allocation
`m ≥ 0` with total `M = ∫ m > 0`, output is at most `AM^γ`, with `A` of (22.6). -/
theorem simple_planner_A {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) {a m : Ω → ℝ}
    (ha : ∀ ω, 0 < a ω) (hm : ∀ ω, 0 ≤ m ω) (hmI : Integrable m P)
    (hpI : Integrable (fun ω => a ω ^ (1 / (1 - γ))) P)
    (hyI : Integrable (fun ω => a ω * m ω ^ γ) P) (hI : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) ∂P)
    (hM : 0 < ∫ ω, m ω ∂P) :
    ∫ ω, a ω * m ω ^ γ ∂P ≤ aggTFP P γ a * (∫ ω, m ω ∂P) ^ γ := by
  set S := ∫ ω, a ω ^ (1 / (1 - γ)) ∂P
  set M := ∫ ω, m ω ∂P
  have h1γ : 0 < 1 - γ := by linarith
  set c := γ * (S / M) ^ (1 - γ) with hcdef
  have hc : 0 < c := by positivity
  have hγc : γ / c = (M / S) ^ (1 - γ) := by
    rw [hcdef, div_mul_eq_div_div, div_self hγ.ne', one_div, ← Real.inv_rpow (by positivity),
      inv_div]
  have hsum : ∫ ω, simpleScale γ c (a ω) ∂P = M := by
    rw [simple_M_eq P hc hγ ha, hγc, ← Real.rpow_mul (by positivity), mul_one_div_cancel
      h1γ.ne', Real.rpow_one, div_mul_cancel₀ _ hI.ne']
  have hsI : Integrable (fun ω => simpleScale γ c (a ω)) P := by
    have : (fun ω => simpleScale γ c (a ω)) =
        fun ω => (γ / c) ^ (1 / (1 - γ)) * a ω ^ (1 / (1 - γ)) :=
      funext fun ω => simple_scale_eq hc hγ (ha ω)
    rw [this]; exact hpI.const_mul _
  have hYI : Integrable (fun ω => a ω * simpleScale γ c (a ω) ^ γ) P := by
    have : (fun ω => a ω * simpleScale γ c (a ω) ^ γ) =
        fun ω => c / γ * simpleScale γ c (a ω) :=
      funext fun ω => simple_output_eq hc hγ hγ1 (ha ω)
    rw [this]; exact hsI.const_mul _
  have h := simple_planner P hc hγ hγ1 ha hm hmI hsI hYI hyI (by rw [hsum])
  rw [eq_22_7_M P hc hγ hγ1 ha hI, hsum] at h
  exact h

/-- `(γb a/c)^{1/(1−γ)}`-scales with wedges: `a·m^γ = a^{1/(1−γ)}b^{γ/(1−γ)}·K^γ` and
`m = a^{1/(1−γ)}b^{1/(1−γ)}·K` where `K = (γ/c)^{1/(1−γ)}`. -/
theorem wedge_scale_eq {γ c a b : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1) (ha : 0 < a)
    (hb : 0 < b) :
    simpleScale γ c (b * a) =
        (γ / c) ^ (1 / (1 - γ)) * (a ^ (1 / (1 - γ)) * b ^ (1 / (1 - γ))) ∧
      a * simpleScale γ c (b * a) ^ γ =
        ((γ / c) ^ (1 / (1 - γ))) ^ γ * (a ^ (1 / (1 - γ)) * b ^ (γ / (1 - γ))) := by
  have h1γ : 0 < 1 - γ := by linarith
  have hK : 0 < (γ / c) ^ (1 / (1 - γ)) := by positivity
  have hs := simple_scale_eq hc hγ (mul_pos hb ha)
  rw [Real.mul_rpow hb.le ha.le] at hs
  refine ⟨by rw [hs]; ring, ?_⟩
  rw [hs, Real.mul_rpow hK.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hb.le, ← Real.rpow_mul ha.le]
  have ea : a * a ^ (1 / (1 - γ) * γ) = a ^ (1 / (1 - γ)) := by
    rw [← Real.rpow_one_add' ha.le (by positivity)]
    congr 1; field_simp; ring
  have eb : 1 / (1 - γ) * γ = γ / (1 - γ) := by ring
  rw [eb] at ea ⊢
  calc a * (((γ / c) ^ (1 / (1 - γ))) ^ γ * (b ^ (γ / (1 - γ)) * a ^ (γ / (1 - γ))))
      = ((γ / c) ^ (1 / (1 - γ))) ^ γ * ((a * a ^ (γ / (1 - γ))) * b ^ (γ / (1 - γ))) := by
        ring
    _ = _ := by rw [ea]

/-- AKMM, (22.10), p. 672: **the aggregate production function with wedges**. Firm `i` solves
`max (1−τᵢ)aᵢmᵞ − cm`, i.e. the scale problem with productivity `bᵢaᵢ`, `bᵢ = 1 − τᵢ`
(`eq_22_1`), so `mᵢ = m*(γ, c, bᵢaᵢ)`; output `Y = ∫ aᵢmᵢ^γ` is `AM^γ` with `A` of (22.10). -/
theorem eq_22_10 {P : Measure Ω} {γ c : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1)
    {a b : Ω → ℝ} (ha : ∀ ω, 0 < a ω) (hb : ∀ ω, 0 < b ω)
    (hI : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) * b ω ^ (1 / (1 - γ)) ∂P) :
    ∫ ω, a ω * simpleScale γ c (b ω * a ω) ^ γ ∂P =
      wedgeTFP P γ a b * (∫ ω, simpleScale γ c (b ω * a ω) ∂P) ^ γ := by
  have hK : 0 < (γ / c) ^ (1 / (1 - γ)) := by positivity
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (wedge_scale_eq hc hγ hγ1 (ha ω) (hb ω)).2),
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (wedge_scale_eq hc hγ hγ1 (ha ω) (hb ω)).1), integral_const_mul, integral_const_mul,
    Real.mul_rpow hK.le hI.le, wedgeTFP]
  field_simp

/-- AKMM, pp. 672–673: **misallocation lowers TFP**, for any joint distribution of
productivity and wedges: `A` of (22.10) is at most `A` of (22.6). The wedge allocation is one
allocation of the same total input, so the planner bound `simple_planner_A` applies. -/
theorem wedge_A_le {P : Measure Ω} {γ c : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1)
    {a b : Ω → ℝ} (ha : ∀ ω, 0 < a ω) (hb : ∀ ω, 0 < b ω)
    (hpI : Integrable (fun ω => a ω ^ (1 / (1 - γ))) P)
    (hmI : Integrable (fun ω => a ω ^ (1 / (1 - γ)) * b ω ^ (1 / (1 - γ))) P)
    (hyI : Integrable (fun ω => a ω ^ (1 / (1 - γ)) * b ω ^ (γ / (1 - γ))) P)
    (hI : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) ∂P)
    (hJ : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) * b ω ^ (1 / (1 - γ)) ∂P) :
    wedgeTFP P γ a b ≤ aggTFP P γ a := by
  set K := (γ / c) ^ (1 / (1 - γ))
  have hK : 0 < K := by positivity
  have hm : ∀ ω, 0 ≤ simpleScale γ c (b ω * a ω) := fun ω =>
    (simple_scale_pos hc hγ (mul_pos (hb ω) (ha ω))).le
  have hmI' : Integrable (fun ω => simpleScale γ c (b ω * a ω)) P := by
    rw [show (fun ω => simpleScale γ c (b ω * a ω)) = fun ω =>
      K * (a ω ^ (1 / (1 - γ)) * b ω ^ (1 / (1 - γ))) from
      funext fun ω => (wedge_scale_eq hc hγ hγ1 (ha ω) (hb ω)).1]
    exact hmI.const_mul _
  have hyI' : Integrable (fun ω => a ω * simpleScale γ c (b ω * a ω) ^ γ) P := by
    rw [show (fun ω => a ω * simpleScale γ c (b ω * a ω) ^ γ) = fun ω =>
      K ^ γ * (a ω ^ (1 / (1 - γ)) * b ω ^ (γ / (1 - γ))) from
      funext fun ω => (wedge_scale_eq hc hγ hγ1 (ha ω) (hb ω)).2]
    exact hyI.const_mul _
  have hM : 0 < ∫ ω, simpleScale γ c (b ω * a ω) ∂P := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (wedge_scale_eq hc hγ hγ1 (ha ω) (hb ω)).1), integral_const_mul]
    positivity
  have h := simple_planner_A hγ hγ1 ha hm hmI' hpI hyI' hI hM
  rw [eq_22_10 hc hγ hγ1 ha hb hJ] at h
  exact le_of_mul_le_mul_right h (by positivity)

end AKMM.HeterogeneousFirms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hopenhayn–Rogerson: block recursivity (AKMM §22.5)

AKMM, §22.5.1, pp. 673–675, with footnote 11. The firm's problem (22.13) is posed on a finite
grid: productivity states `a ∈ A` with values `aᵥ(a) > 0` and a Markov matrix `Q`, employment
choices `ℓ ∈ L` with values `ℓᵥ`, and lagged employment in `Option L` (`none` is the entrant's
`ℓ₋₁ = 0`).

* **The Bellman equation (22.12)–(22.13)** at the wage `w` has a unique solution `W_w`
  (`hr_bellman_existsUnique`); the operator is a `β`-contraction (`hr_T_sub_le`).
* **Monotonicity in the wage**: `W_w` is antitone in `w`, strictly when every employment level
  is positive, with an explicit gap (`hr_value_wage_gap`), and `W_w` is Lipschitz in `w`
  (`hr_value_lipschitz`).
* **Block recursivity and free entry (22.14)**: the entry value `Wᵉ(w)` depends on `w` only; it
  is strictly decreasing and continuous (`hr_entry_strictAnti`, `hr_entry_continuous`), so free
  entry `Wᵉ(w) = c_e + κ` has at most one solution (`hr_free_entry_unique`), one exists when
  `Wᵉ` brackets `c_e + κ` (`hr_free_entry_exists`), and higher entry barriers `κ` lower the
  wage (`hr_entry_barrier_wage`).
* **The stationary distribution for a given entry mass `M`**: with a survivor matrix whose row
  sums are at most `q < 1`, `μ = μQ + Mν` has a unique solution, it is nonnegative, and it is
  `M` times the solution for `M = 1` (`hr_stationary_existsUnique`, `hr_stationary_nonneg`,
  `hr_stationary_linear`); aggregates are linear in `M` (`hr_aggregate_linear`).
* **The labour market (22.15)** with `u = log`: labour supply is `1/χ − (Π + R)/w`
  (`eq_22_15`), and the entry mass clearing the market is unique (`hr_entry_mass`).
* **Footnote 11**: the steady-state Euler equation gives the gross interest rate `1/β`
  (`hr_footnote_11`).
-/

namespace AKMM.HeterogeneousFirms

/-! ### The firm's problem -/

/-- The primitives of the Hopenhayn–Rogerson firm on a grid (AKMM, p. 673): discount factor,
firing tax, fixed cost, returns `γ`, productivity values, employment values, productivity
transition matrix. -/
structure HRFirm (A L : Type*) where
  β : ℝ
  τ : ℝ
  cf : ℝ
  γ : ℝ
  av : A → ℝ
  lv : L → ℝ
  Q : A → A → ℝ

variable {A L : Type*} [Fintype A] [Fintype L] [Nonempty L]

/-- Lagged employment: `none` is `ℓ₋₁ = 0`. -/
def hrLag {L : Type*} (lv : L → ℝ) (o : Option L) : ℝ := o.elim 0 lv

/-- AKMM, (22.12), p. 673: the flow profit `aℓ^γ − wℓ − c_f − τ max(0, ℓ₋₁ − ℓ)`. -/
noncomputable def hrProfit (F : HRFirm A L) (w : ℝ) (l0 : Option L) (l : L) (a : A) : ℝ :=
  F.av a * F.lv l ^ F.γ - w * F.lv l - F.cf - F.τ * max 0 (hrLag F.lv l0 - F.lv l)

/-- AKMM, (22.13), p. 674: the Bellman operator
`(TW)(a, ℓ₋₁) = max_ℓ π(ℓ₋₁, ℓ, a) + β max{E[W(a', ℓ)|a], −τℓ}`. -/
noncomputable def hrT (F : HRFirm A L) (w : ℝ) (W : A → Option L → ℝ) (a : A)
    (l0 : Option L) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun l =>
    hrProfit F w l0 l a + F.β * max (∑ a', F.Q a a' * W a' (some l)) (-(F.τ * F.lv l))

/-- `max x c − max y c ≤ max (x − y) 0`. -/
theorem hr_max_sub_le (x y c : ℝ) : max x c - max y c ≤ max (x - y) 0 := by
  have h1 : max x c ≤ max y c + max (x - y) 0 := max_le (by
    linarith [le_max_left y c, le_max_left (x - y) 0]) (by
    linarith [le_max_right y c, le_max_right (x - y) 0])
  linarith

/-- The key estimate: if `W − W' ≤ D` with `D ≥ 0`, and `(w' − w)k ≤ (w' − w)ℓᵥ` for every
`ℓ`, then `T_{w'}W − T_wW' ≤ βD − (w' − w)k`. -/
theorem hr_T_sub_le (F : HRFirm A L) (hβ : 0 ≤ F.β) (hQ0 : ∀ a a', 0 ≤ F.Q a a')
    (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {W W' : A → Option L → ℝ} {D : ℝ}
    (hD : ∀ a l0, W a l0 - W' a l0 ≤ D) (hD0 : 0 ≤ D) {w w' k : ℝ}
    (hk : ∀ l, (w' - w) * k ≤ (w' - w) * F.lv l) (a : A) (l0 : Option L) :
    hrT F w' W a l0 - hrT F w W' a l0 ≤ F.β * D - (w' - w) * k := by
  unfold hrT
  rw [sub_le_iff_le_add]
  refine Finset.sup'_le _ _ fun l _ => ?_
  refine le_trans ?_ (add_le_add le_rfl (Finset.le_sup' (fun l =>
    hrProfit F w l0 l a + F.β * max (∑ a', F.Q a a' * W' a' (some l)) (-(F.τ * F.lv l)))
    (Finset.mem_univ l)))
  have hE : ∑ a', F.Q a a' * W a' (some l) - ∑ a', F.Q a a' * W' a' (some l) ≤ D := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ a', (F.Q a a' * W a' (some l) - F.Q a a' * W' a' (some l))
        ≤ ∑ a', F.Q a a' * D := Finset.sum_le_sum fun a' _ => by
          rw [← mul_sub]; exact mul_le_mul_of_nonneg_left (hD a' _) (hQ0 a a')
      _ = D := by rw [← Finset.sum_mul, hQ1, one_mul]
  have hM := hr_max_sub_le (∑ a', F.Q a a' * W a' (some l))
    (∑ a', F.Q a a' * W' a' (some l)) (-(F.τ * F.lv l))
  have hM' : max (∑ a', F.Q a a' * W a' (some l) - ∑ a', F.Q a a' * W' a' (some l)) 0 ≤ D :=
    max_le hE hD0
  have hπ : hrProfit F w' l0 l a = hrProfit F w l0 l a - (w' - w) * F.lv l := by
    unfold hrProfit; ring
  rw [hπ]
  nlinarith [mul_le_mul_of_nonneg_left (hM.trans hM') hβ, hk l]

/-- The Bellman operator is a `β`-contraction in the sup metric. -/
theorem hr_T_dist_le (F : HRFirm A L) (hβ : 0 ≤ F.β) (hQ0 : ∀ a a', 0 ≤ F.Q a a')
    (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) (w : ℝ) (W W' : A → Option L → ℝ) :
    dist (hrT F w W) (hrT F w W') ≤ F.β * dist W W' := by
  have hd : ∀ (U V : A → Option L → ℝ) a l0, U a l0 - V a l0 ≤ dist U V := fun U V a l0 =>
    (le_abs_self _).trans (by
      rw [← Real.dist_eq]; exact (dist_le_pi_dist (U a) (V a) l0).trans (dist_le_pi_dist U V a))
  have hk : ∀ l, (w - w) * 0 ≤ (w - w) * F.lv l := fun l => by simp
  rw [dist_pi_le_iff (mul_nonneg hβ dist_nonneg)]
  intro a
  rw [dist_pi_le_iff (mul_nonneg hβ dist_nonneg)]
  intro l0
  rw [Real.dist_eq, abs_le]
  have h1 := hr_T_sub_le F hβ hQ0 hQ1 (hd W W') dist_nonneg hk a l0
  have h2 := hr_T_sub_le F hβ hQ0 hQ1 (hd W' W) dist_nonneg hk a l0
  rw [dist_comm W' W] at h2
  constructor <;> linarith

/-- AKMM, (22.13), p. 674: **the firm's Bellman equation has a unique solution** at every wage,
for `0 ≤ β < 1` and a Markov matrix `Q`. -/
theorem hr_bellman_existsUnique (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) (w : ℝ) :
    ∃! W : A → Option L → ℝ, hrT F w W = W := by
  have hK : ContractingWith (Real.toNNReal F.β) (hrT F w) := by
    refine ⟨by rw [Real.toNNReal_lt_one]; exact hβ1, LipschitzWith.of_dist_le' fun W W' =>
      hr_T_dist_le F hβ hQ0 hQ1 w W W'⟩
  refine ⟨ContractingWith.fixedPoint _ hK, ContractingWith.fixedPoint_isFixedPt hK,
    fun W hW => ContractingWith.fixedPoint_unique hK hW⟩

/-- The value function `W_w` (chosen by `Classical.epsilon`; it solves the Bellman equation
under the hypotheses of `hr_bellman_existsUnique`, see `hr_value_spec`). -/
noncomputable def hrValue (F : HRFirm A L) (w : ℝ) : A → Option L → ℝ :=
  Classical.epsilon fun W => hrT F w W = W

theorem hr_value_spec (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) (w : ℝ) :
    hrT F w (hrValue F w) = hrValue F w :=
  Classical.epsilon_spec (hr_bellman_existsUnique F hβ hβ1 hQ0 hQ1 w).exists

/-- A fixed-point comparison: if `W = T_wW`, `W' = T_{w'}W'` and `(w' − w)k ≤ (w' − w)ℓᵥ` for
all `ℓ`, then `W' − W ≤ max(0, −(w' − w)k)/(1 − β)`; in particular `W' ≤ W − (w' − w)k` when
`(w' − w)k ≥ 0`. -/
theorem hr_fixed_compare [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {w w' k : ℝ}
    {W W' : A → Option L → ℝ} (hW : hrT F w W = W) (hW' : hrT F w' W' = W')
    (hk : ∀ l, (w' - w) * k ≤ (w' - w) * F.lv l) :
    ∀ a l0, W' a l0 - W a l0 ≤ F.β * max (-(w' - w) * k) 0 / (1 - F.β) - (w' - w) * k := by
  obtain ⟨⟨a1, o1⟩, hmax⟩ := Finite.exists_max fun s : A × Option L => W' s.1 s.2 - W s.1 s.2
  set D := max (W' a1 o1 - W a1 o1) 0
  have hD : ∀ a l0, W' a l0 - W a l0 ≤ D := fun a l0 =>
    (hmax (a, l0)).trans (le_max_left _ _)
  have hD0 : 0 ≤ D := le_max_right _ _
  have hstep : ∀ a l0, W' a l0 - W a l0 ≤ F.β * D - (w' - w) * k := fun a l0 => by
    have := hr_T_sub_le F hβ hQ0 hQ1 hD hD0 hk a l0
    rwa [hW, hW'] at this
  have h1β : 0 < 1 - F.β := by linarith
  have hDle : D ≤ F.β * D + max (-(w' - w) * k) 0 := max_le
    (by linarith [hstep a1 o1, le_max_left (-(w' - w) * k) 0])
    (by nlinarith [le_max_right (-(w' - w) * k) 0])
  have hDb : D ≤ max (-(w' - w) * k) 0 / (1 - F.β) := by
    rw [le_div_iff₀ h1β]; linarith
  intro a l0
  have := hstep a l0
  have := mul_le_mul_of_nonneg_left hDb hβ
  rw [mul_div_assoc]
  linarith

/-- AKMM, p. 675: **the value falls with the wage, with a gap**. If every employment level is at
least `m ≥ 0` and `w ≤ w'`, then `W_{w'} ≤ W_w − (w' − w)m`. -/
theorem hr_value_wage_gap [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {m : ℝ} (hm : 0 ≤ m)
    (hlm : ∀ l, m ≤ F.lv l) {w w' : ℝ} (hww : w ≤ w') (a : A) (l0 : Option L) :
    hrValue F w' a l0 ≤ hrValue F w a l0 - (w' - w) * m := by
  have h := hr_fixed_compare F hβ hβ1 hQ0 hQ1 (hr_value_spec F hβ hβ1 hQ0 hQ1 w)
    (hr_value_spec F hβ hβ1 hQ0 hQ1 w') (k := m)
    (fun l => mul_le_mul_of_nonneg_left (hlm l) (by linarith)) a l0
  have : max (-(w' - w) * m) 0 = 0 := max_eq_right (by nlinarith)
  rw [this, mul_zero, zero_div, zero_sub] at h
  linarith

/-- The value is Lipschitz in the wage: with employment levels in `[0, ℓ̄]`,
`|W_w − W_{w'}| ≤ ℓ̄|w − w'|/(1 − β)`. -/
theorem hr_value_lipschitz [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {lbar : ℝ}
    (hl0 : ∀ l, 0 ≤ F.lv l) (hlb : ∀ l, F.lv l ≤ lbar) {w w' : ℝ} (hww : w ≤ w') (a : A)
    (l0 : Option L) :
    |hrValue F w a l0 - hrValue F w' a l0| ≤ lbar * (w' - w) / (1 - F.β) := by
  have h1β : 0 < 1 - F.β := by linarith
  have hlb0 : 0 ≤ lbar := (hl0 (Classical.arbitrary L)).trans (hlb _)
  have hW := hr_value_spec F hβ hβ1 hQ0 hQ1 w
  have hW' := hr_value_spec F hβ hβ1 hQ0 hQ1 w'
  -- `W_w − W_{w'}`: compare with the roles of the wages swapped, `k = ℓ̄`
  have h1 := hr_fixed_compare F hβ hβ1 hQ0 hQ1 hW' hW (k := lbar)
    (fun l => mul_le_mul_of_nonpos_left (hlb l) (by linarith)) a l0
  have hmx : max (-(w - w') * lbar) 0 = lbar * (w' - w) := by
    rw [max_eq_left (by nlinarith [mul_nonneg (sub_nonneg.mpr hww) hlb0])]; ring
  rw [hmx] at h1
  have e : F.β * (lbar * (w' - w)) / (1 - F.β) - (w - w') * lbar = lbar * (w' - w) / (1 - F.β) :=
    by field_simp; ring
  rw [e] at h1
  have h2 := hr_value_wage_gap F hβ hβ1 hQ0 hQ1 le_rfl hl0 hww a l0
  rw [abs_le]
  constructor
  · have : 0 ≤ lbar * (w' - w) / (1 - F.β) := by
      apply div_nonneg _ h1β.le; nlinarith
    linarith
  · linarith

/-! ### Free entry (22.14) -/

/-- AKMM, p. 674: the value of entry `Wᵉ(w) = Σ_a ν(a)(W_w(a, 0) + c_f)`. It depends on the wage
only: **block recursivity**. -/
noncomputable def hrEntry (F : HRFirm A L) (ν : A → ℝ) (w : ℝ) : ℝ :=
  ∑ a, ν a * (hrValue F w a none + F.cf)

/-- AKMM, p. 675: with positive employment levels (`ℓᵥ ≥ m > 0`) and an entrant distribution
`ν`, the entry value is strictly decreasing in the wage. -/
theorem hr_entry_strictAnti [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {m : ℝ} (hm : 0 < m)
    (hlm : ∀ l, m ≤ F.lv l) {ν : A → ℝ} (hν0 : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1) :
    StrictAnti (hrEntry F ν) := by
  intro w w' hww
  unfold hrEntry
  have h : ∑ a, ν a * (hrValue F w' a none + F.cf) ≤
      ∑ a, ν a * (hrValue F w a none + F.cf) - (w' - w) * m := by
    rw [show (w' - w) * m = ∑ a, ν a * ((w' - w) * m) by rw [← Finset.sum_mul, hν1, one_mul],
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (hν0 a)
    linarith [hr_value_wage_gap F hβ hβ1 hQ0 hQ1 hm.le hlm hww.le a none]
  have : 0 < (w' - w) * m := mul_pos (by linarith) hm
  linarith

/-- The entry value is continuous in the wage. -/
theorem hr_entry_continuous [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {lbar : ℝ}
    (hl0 : ∀ l, 0 ≤ F.lv l) (hlb : ∀ l, F.lv l ≤ lbar) (ν : A → ℝ) :
    Continuous (hrEntry F ν) := by
  have h1β : 0 < 1 - F.β := by linarith
  have hlb0 : 0 ≤ lbar := (hl0 (Classical.arbitrary L)).trans (hlb _)
  have hc : ∀ a, Continuous fun w => hrValue F w a none := fun a => by
    refine (LipschitzWith.of_dist_le' (K := lbar / (1 - F.β)) fun w w' => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total w w' with h | h
    · have := hr_value_lipschitz F hβ hβ1 hQ0 hQ1 hl0 hlb h a none
      rw [abs_of_nonpos (by linarith : w - w' ≤ 0)]
      calc _ ≤ lbar * (w' - w) / (1 - F.β) := this
        _ = lbar / (1 - F.β) * -(w - w') := by ring
    · have := hr_value_lipschitz F hβ hβ1 hQ0 hQ1 hl0 hlb h a none
      rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ w - w')]
      calc _ ≤ lbar * (w - w') / (1 - F.β) := this
        _ = lbar / (1 - F.β) * (w - w') := by ring
  unfold hrEntry
  exact continuous_finsetSum _ fun a _ => continuous_const.mul ((hc a).add continuous_const)

/-- AKMM, (22.14), p. 674: **free entry pins down the wage**: at most one `w` satisfies
`Wᵉ(w) = c_e + κ`. -/
theorem hr_free_entry_unique [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {m : ℝ} (hm : 0 < m)
    (hlm : ∀ l, m ≤ F.lv l) {ν : A → ℝ} (hν0 : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1)
    {ce κ w w' : ℝ} (hw : hrEntry F ν w = ce + κ) (hw' : hrEntry F ν w' = ce + κ) :
    w = w' :=
  (hr_entry_strictAnti F hβ hβ1 hQ0 hQ1 hm hlm hν0 hν1).injective (hw.trans hw'.symm)

/-- AKMM, (22.14): a free-entry wage exists when `Wᵉ` brackets `c_e + κ` on `[w₀, w₁]`. -/
theorem hr_free_entry_exists [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {lbar : ℝ}
    (hl0 : ∀ l, 0 ≤ F.lv l) (hlb : ∀ l, F.lv l ≤ lbar) (ν : A → ℝ) {ce κ w0 w1 : ℝ}
    (h01 : w0 ≤ w1) (hlo : ce + κ ≤ hrEntry F ν w0) (hhi : hrEntry F ν w1 ≤ ce + κ) :
    ∃ w ∈ Set.Icc w0 w1, hrEntry F ν w = ce + κ := by
  have hc := (hr_entry_continuous F hβ hβ1 hQ0 hQ1 hl0 hlb ν).continuousOn (s := Set.Icc w0 w1)
  exact intermediate_value_Icc' h01 hc ⟨hhi, hlo⟩

/-- AKMM, p. 677: **entry barriers lower the wage**: if `w` and `w'` clear free entry with
barriers `κ < κ'`, then `w' < w`. -/
theorem hr_entry_barrier_wage [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {m : ℝ} (hm : 0 < m)
    (hlm : ∀ l, m ≤ F.lv l) {ν : A → ℝ} (hν0 : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1)
    {ce κ κ' w w' : ℝ} (hκ : κ < κ') (hw : hrEntry F ν w = ce + κ)
    (hw' : hrEntry F ν w' = ce + κ') : w' < w :=
  (hr_entry_strictAnti F hβ hβ1 hQ0 hQ1 hm hlm hν0 hν1).lt_iff_gt.mp (by linarith)

/-! ### The stationary distribution for a given entry mass -/

variable {S : Type*} [Fintype S]

/-- AKMM, p. 675: the stationary condition with entry mass `M`: `μ(s') = Σ_s μ(s)Q(s,s') + Mν(s')`,
where `Q` is the survivor transition under the decision rule of (22.13) (row sums `< 1` through
exit) and `ν` the entrants' distribution over states. -/
def HRStationary (Q : S → S → ℝ) (ν : S → ℝ) (M : ℝ) (μ : S → ℝ) : Prop :=
  ∀ s', μ s' = ∑ s, μ s * Q s s' + M * ν s'

/-- A solution with no entry and a strictly substochastic `Q` is zero. -/
theorem hr_stationary_zero {Q : S → S → ℝ} (hQ0 : ∀ s s', 0 ≤ Q s s') {q : ℝ} (hq : q < 1)
    (hQq : ∀ s, ∑ s', Q s s' ≤ q) {d : S → ℝ} (hd : ∀ s', d s' = ∑ s, d s * Q s s') :
    d = 0 := by
  have habs : ∀ s', |d s'| ≤ ∑ s, |d s| * Q s s' := fun s' => by
    rw [hd s']
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun s _ => by rw [abs_mul, abs_of_nonneg (hQ0 s s')]
  have hsum : ∑ s', |d s'| ≤ q * ∑ s, |d s| := by
    calc ∑ s', |d s'| ≤ ∑ s', ∑ s, |d s| * Q s s' := Finset.sum_le_sum fun s' _ => habs s'
      _ = ∑ s, |d s| * ∑ s', Q s s' := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
      _ ≤ ∑ s, |d s| * q := Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hQq s) (abs_nonneg _)
      _ = q * ∑ s, |d s| := by rw [← Finset.sum_mul, mul_comm]
  have h0 : ∑ s, |d s| = 0 := by
    have := Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) => abs_nonneg (d s)
    nlinarith
  funext s
  have := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => abs_nonneg (d s)).mp h0 s
    (Finset.mem_univ s)
  simpa using this

/-- AKMM, p. 675: **for a given entry mass the stationary distribution exists and is unique**
(survivor matrix with row sums at most `q < 1`). -/
theorem hr_stationary_existsUnique {Q : S → S → ℝ} (hQ0 : ∀ s s', 0 ≤ Q s s') {q : ℝ}
    (hq : q < 1) (hQq : ∀ s, ∑ s', Q s s' ≤ q) (ν : S → ℝ) (M : ℝ) :
    ∃! μ, HRStationary Q ν M μ := by
  let T : (S → ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun μ s' => μ s' - ∑ s, μ s * Q s s'
      map_add' := fun μ μ' => by
        funext s'; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
      map_smul' := fun c μ => by
        funext s'
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]
        ring }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    refine hr_stationary_zero hQ0 hq hQq fun s' => ?_
    have := congrFun hd s'
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    linarith
  obtain ⟨μ, hμ⟩ := (LinearMap.injective_iff_surjective.mp hinj) (fun s' => M * ν s')
  refine ⟨μ, fun s' => ?_, fun μ' hμ' => ?_⟩
  · have := congrFun hμ s'
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk] at this
    linarith
  · have h := hr_stationary_zero hQ0 hq hQq (d := μ' - μ) fun s' => by
      have h1 := hμ' s'
      have h2 := congrFun hμ s'
      simp only [T, LinearMap.coe_mk, AddHom.coe_mk] at h2
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      linarith
    exact (sub_eq_zero.mp h)

/-- The stationary distribution is nonnegative when `ν ≥ 0` and `M ≥ 0`. -/
theorem hr_stationary_nonneg {Q : S → S → ℝ} (hQ0 : ∀ s s', 0 ≤ Q s s') {q : ℝ}
    (hq : q < 1) (hQq : ∀ s, ∑ s', Q s s' ≤ q) {ν : S → ℝ} (hν : ∀ s, 0 ≤ ν s) {M : ℝ}
    (hM : 0 ≤ M) {μ : S → ℝ} (hμ : HRStationary Q ν M μ) : ∀ s, 0 ≤ μ s := by
  set n : S → ℝ := fun s => max (-μ s) 0
  have hn : ∀ s', n s' ≤ ∑ s, n s * Q s s' := fun s' => by
    refine max_le ?_ (Finset.sum_nonneg fun s _ => mul_nonneg (le_max_right _ _) (hQ0 s s'))
    rw [hμ s', neg_add]
    have h1 : -∑ s, μ s * Q s s' ≤ ∑ s, n s * Q s s' := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun s _ => by
        rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hQ0 s s')
    nlinarith [mul_nonneg hM (hν s')]
  have hsum : ∑ s', n s' ≤ q * ∑ s, n s := by
    calc ∑ s', n s' ≤ ∑ s', ∑ s, n s * Q s s' := Finset.sum_le_sum fun s' _ => hn s'
      _ = ∑ s, n s * ∑ s', Q s s' := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
      _ ≤ ∑ s, n s * q := Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hQq s) (le_max_right _ _)
      _ = q * ∑ s, n s := by rw [← Finset.sum_mul, mul_comm]
  have hn0 : ∀ s, 0 ≤ n s := fun s => le_max_right _ _
  have h0 : ∑ s, n s = 0 := by
    have := Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) => hn0 s
    nlinarith
  intro s
  have := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => hn0 s).mp h0 s (Finset.mem_univ s)
  have hle : -μ s ≤ 0 := by rw [← this]; exact le_max_left _ _
  linarith

/-- AKMM, p. 675: **the stationary distribution is linear in the entry mass**: if `μ₁` is
stationary for `M = 1`, then `Mμ₁` is stationary for `M`, and it is the only one. -/
theorem hr_stationary_linear {Q : S → S → ℝ} (hQ0 : ∀ s s', 0 ≤ Q s s') {q : ℝ}
    (hq : q < 1) (hQq : ∀ s, ∑ s', Q s s' ≤ q) {ν μ1 : S → ℝ} (h1 : HRStationary Q ν 1 μ1)
    (M : ℝ) {μ : S → ℝ} (hμ : HRStationary Q ν M μ) : μ = fun s => M * μ1 s := by
  have hM : HRStationary Q ν M fun s => M * μ1 s := fun s' => by
    change M * μ1 s' = ∑ s, M * μ1 s * Q s s' + M * ν s'
    rw [h1 s']; simp only [Finset.mul_sum, mul_add]
    rw [one_mul]; congr 1; exact Finset.sum_congr rfl fun s _ => by ring
  exact (hr_stationary_existsUnique hQ0 hq hQq ν M).unique hμ hM

/-- AKMM, p. 675: labour demand, profits and firing taxes are aggregates `Σ μ(s)g(s)` of the
stationary distribution, hence `M` times their value at `M = 1`. -/
theorem hr_aggregate_linear {Q : S → S → ℝ} (hQ0 : ∀ s s', 0 ≤ Q s s') {q : ℝ}
    (hq : q < 1) (hQq : ∀ s, ∑ s', Q s s' ≤ q) {ν μ1 : S → ℝ} (h1 : HRStationary Q ν 1 μ1)
    (M : ℝ) {μ : S → ℝ} (hμ : HRStationary Q ν M μ) (g : S → ℝ) :
    ∑ s, μ s * g s = M * ∑ s, μ1 s * g s := by
  rw [hr_stationary_linear hQ0 hq hQq h1 M hμ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-! ### The labour market -/

/-- AKMM, (22.15), p. 675, with `u = log` (the calibration, p. 675): the household's condition
`w u'(wLˢ + Π + R) = χ` holds iff `Lˢ = 1/χ − (Π + R)/w` (with positive consumption). -/
theorem eq_22_15 {w χ Ls PR : ℝ} (hw : 0 < w) (hχ : 0 < χ) (hC : 0 < w * Ls + PR) :
    w * (1 / (w * Ls + PR)) = χ ↔ Ls = 1 / χ - PR / w := by
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    have e : w * Ls + PR = w / χ := by rw [h]; field_simp; ring
    rw [e]; field_simp

/-- AKMM, p. 675: **the entry mass**. With labour demand `M ℓ̂` and profits plus taxes `M ϖ̂`
(linear in `M`, `hr_aggregate_linear`), the market clears, `M ℓ̂ = 1/χ − Mϖ̂/w`, iff
`M = 1/(χ(ℓ̂ + ϖ̂/w))`: the entry mass is unique. -/
theorem hr_entry_mass {w χ lhat phat M : ℝ} (hχ : 0 < χ)
    (hpos : 0 < lhat + phat / w) :
    M * lhat = 1 / χ - M * phat / w ↔ M = 1 / (χ * (lhat + phat / w)) := by
  have e : M * phat / w = M * (phat / w) := mul_div_assoc M phat w
  rw [eq_div_iff (by positivity)]
  constructor
  · intro h
    have h2 : M * (lhat + phat / w) = 1 / χ := by rw [mul_add]; linarith
    rw [show M * (χ * (lhat + phat / w)) = χ * (M * (lhat + phat / w)) by ring, h2]
    field_simp
  · intro h
    have h2 : M * (lhat + phat / w) = 1 / χ := by
      rw [eq_div_iff hχ.ne']; linarith [show M * (χ * (lhat + phat / w)) =
        M * (lhat + phat / w) * χ by ring]
    rw [mul_add] at h2
    linarith

/-- AKMM, p. 674, footnote 11: in a steady state with constant consumption the Euler equation
`u'(C) = β(1 + r)u'(C)` gives the gross interest rate `1 + r = 1/β`. -/
theorem hr_footnote_11 {β r up : ℝ} (hβ : 0 < β) (hup : 0 < up) (h : up = β * (1 + r) * up) :
    1 + r = 1 / β := by
  have : β * (1 + r) = 1 := by
    have := mul_right_cancel₀ hup.ne' (h.symm.trans (one_mul up).symm)
    exact this
  field_simp; linarith

end AKMM.HeterogeneousFirms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monopolistic competition (AKMM §22.6.1)

AKMM, §22.6.1, pp. 677–679. The final good is the Dixit–Stiglitz aggregate (22.16) of a unit
mass of intermediate goods, a probability space `(Ω, P)`; `σ > 1`. The Dixit–Stiglitz aggregate,
the price index and the final producer's cost minimisation are imported from Miao's Chapter 19
(`Miao.NewKeynesian.nk_aggY`, `nk_priceIndex`, `eq_19_6_foc`, `eq_19_6`, `eq_19_7`), which is the
same model with `ε = σ`.

* **(22.17)–(22.18)**: the first-order condition `pᵢ = λyᵢ^{−1/σ}Y^{1/σ}` is the demand curve, the
  multiplier is the price index and `∫pᵢyᵢ = λY` (`eq_22_17`); with `P = 1`, the inverse demand
  (22.18) (`eq_22_18`).
* **(22.19)–(22.20)**: the monopolist's problem is the scale problem of §22.2 with returns
  `γ(σ−1)/σ` and productivity `a^{(σ−1)/σ}Y^{1/σ}` (`eq_22_19`, `eq_22_20`), so it is well posed
  for `γ < σ/(σ−1)`, in particular under constant returns `γ = 1`.
* **(22.21)–(22.22)**: the constant markup `p = σ/(σ−1)·MC` (`eq_22_22`).
* **Aggregation**: `Y = (c/γ)(σ/(σ−1))M` (`mc_output_eq`), and `Y = AM^γ` with
  `A = (∫ a^{1/(σ/(σ−1)−γ)})^{σ/(σ−1)−γ}` (`mc_aggregate`, `mc_aggregate_eq`).
-/

open MeasureTheory

namespace AKMM.HeterogeneousFirms

/-- AKMM, (22.17), p. 678: **the final producer's first-order condition** `pᵢ = λyᵢ^{−1/σ}Y^{1/σ}`
is the demand curve `yᵢ = (pᵢ/λ)^{−σ}Y`; along it, `∫pᵢyᵢ = λY` iff `λ` is the price index
`(∫ p^{1−σ})^{1/(1−σ)}` (so `λ = P`). Imported from Miao (19.6)–(19.7). -/
theorem eq_22_17 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {σ Y lam : ℝ} (hσ : 1 < σ) (hY : 0 < Y) (hlam : 0 < lam) {p y : Ω → ℝ}
    (hp : ∀ i, 0 < p i) (hy : ∀ i, 0 < y i) (hI : Integrable (fun i => p i ^ (1 - σ)) P)
    (hfoc : ∀ i, lam * Y ^ (1 / σ) * y i ^ (-1 / σ) = p i) :
    (∀ i, y i = (p i / lam) ^ (-σ) * Y) ∧
      (∫ i, p i * y i ∂P = lam * Y ↔ lam = Miao.NewKeynesian.nk_priceIndex P σ p) := by
  have hd : ∀ i, y i = (p i / lam) ^ (-σ) * Y := fun i =>
    (Miao.NewKeynesian.eq_19_6_foc (by linarith) hlam hY (hy i) (hp i)).mp (hfoc i)
  refine ⟨hd, ?_⟩
  have e : ∫ i, p i * y i ∂P = ∫ i, p i * ((p i / lam) ^ (-σ) * Y) ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun i => by simp only [hd i])
  rw [e]
  exact Miao.NewKeynesian.eq_19_7 hσ hY hlam hp hI

/-- AKMM, (22.18), p. 678: with the final good as numeraire (`P = λ = 1`) the inverse demand is
`pᵢ = yᵢ^{−1/σ}Y^{1/σ}`. -/
theorem eq_22_18 {σ Y yi : ℝ} :
    1 * Y ^ (1 / σ) * yi ^ (-1 / σ) = yi ^ (-1 / σ) * Y ^ (1 / σ) := by ring

/-- `(a mᵞ)^{1−1/σ}Y^{1/σ} = (a^{(σ−1)/σ}Y^{1/σ}) m^{γ(σ−1)/σ}`. -/
theorem mc_revenue_eq {σ γ a m Y : ℝ} (hσ : 1 < σ) (hγ : 0 < γ) (ha : 0 < a) (hm : 0 ≤ m) :
    (a * m ^ γ) ^ (-1 / σ) * Y ^ (1 / σ) * (a * m ^ γ) =
      a ^ ((σ - 1) / σ) * Y ^ (1 / σ) * m ^ (γ * ((σ - 1) / σ)) := by
  have hσ0 : σ ≠ 0 := by linarith
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  rcases hm.lt_or_eq with hm | rfl
  · have hy : 0 < a * m ^ γ := mul_pos ha (Real.rpow_pos_of_pos hm γ)
    have e : (a * m ^ γ) ^ (-1 / σ) * (a * m ^ γ) = (a * m ^ γ) ^ ((σ - 1) / σ) := by
      rw [← Real.rpow_add_one hy.ne']
      congr 1
      field_simp
      ring
    rw [mul_right_comm, e, Real.mul_rpow ha.le (Real.rpow_nonneg hm.le _), ← Real.rpow_mul hm.le]
    ring
  · rw [Real.zero_rpow hγ.ne', Real.zero_rpow (mul_pos hγ hθ).ne']
    ring

/-- AKMM, (22.19), p. 678: **the monopolist's problem**. Taking `Y` as given, firm `i` maximises
`pᵢyᵢ − cm = (am^γ)^{−1/σ}Y^{1/σ}·am^γ − cm`. This is the scale problem of §22.2 with productivity
`a^{(σ−1)/σ}Y^{1/σ}` and returns `γ(σ−1)/σ`, so for `0 < γ(σ−1)/σ < 1` its maximiser is
`m* = simpleScale (γ(σ−1)/σ) c (a^{(σ−1)/σ}Y^{1/σ})`. -/
theorem eq_22_19 {σ γ c a Y m : ℝ} (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1)
    (hc : 0 < c) (ha : 0 < a) (hY : 0 < Y) (hm : 0 ≤ m) :
    (a * m ^ γ) ^ (-1 / σ) * Y ^ (1 / σ) * (a * m ^ γ) - c * m ≤
      (a * simpleScale (γ * ((σ - 1) / σ)) c (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ^ γ) ^ (-1 / σ) *
          Y ^ (1 / σ) *
          (a * simpleScale (γ * ((σ - 1) / σ)) c (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ^ γ) -
        c * simpleScale (γ * ((σ - 1) / σ)) c (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) := by
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  have hA : 0 < a ^ ((σ - 1) / σ) * Y ^ (1 / σ) := by positivity
  have hs := (simple_scale_pos hc (mul_pos hγ hθ) hA).le
  rw [mc_revenue_eq hσ hγ ha hm, mc_revenue_eq hσ hγ ha hs]
  exact eq_22_1 hc (mul_pos hγ hθ) hg hA hm

/-- AKMM, (22.20), p. 679: **the first-order condition**
`(1 − 1/σ)γa^{1−1/σ}m^{γ−γ/σ−1}Y^{1/σ} = c` characterises the monopolist's optimum. -/
theorem eq_22_20 {σ γ c a Y m : ℝ} (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1)
    (hc : 0 < c) (ha : 0 < a) (hY : 0 < Y) (hm : 0 < m) :
    (1 - 1 / σ) * γ * a ^ (1 - 1 / σ) * m ^ (γ - γ / σ - 1) * Y ^ (1 / σ) = c ↔
      m = simpleScale (γ * ((σ - 1) / σ)) c (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) := by
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  have hA : 0 < a ^ ((σ - 1) / σ) * Y ^ (1 / σ) := by positivity
  rw [← eq_22_2 hc (mul_pos hγ hθ) hg hA hm]
  have hσ0 : σ ≠ 0 := by linarith
  have e1 : (1 - 1 / σ) = (σ - 1) / σ := by field_simp
  have e2 : γ - γ / σ - 1 = γ * ((σ - 1) / σ) - 1 := by field_simp
  rw [e1, e2]
  have hg0 : 0 < γ * ((σ - 1) / σ) := mul_pos hγ hθ
  constructor
  · intro h; rw [eq_div_iff hg0.ne']; rw [← h]; ring
  · intro h; rw [eq_div_iff hg0.ne'] at h; rw [← h]; ring

/-- AKMM, (22.21)–(22.22), p. 679: **the constant markup**. At the optimum (first-order condition
(22.20)), the price `p = (am^γ)^{−1/σ}Y^{1/σ}` is `σ/(σ−1)` times the marginal cost
`MC = cm^{1−γ}/(γa)`. -/
theorem eq_22_22 {σ γ c a Y m : ℝ} (hσ : 1 < σ) (hγ : 0 < γ) (ha : 0 < a) (hY : 0 < Y)
    (hm : 0 < m)
    (hfoc : (1 - 1 / σ) * γ * a ^ (1 - 1 / σ) * m ^ (γ - γ / σ - 1) * Y ^ (1 / σ) = c) :
    (a * m ^ γ) ^ (-1 / σ) * Y ^ (1 / σ) = σ / (σ - 1) * (c * m ^ (1 - γ) / (γ * a)) := by
  have hσ0 : σ ≠ 0 := by linarith
  have hσ1 : σ - 1 ≠ 0 := by linarith
  rw [← hfoc, Real.mul_rpow ha.le (Real.rpow_nonneg hm.le _), ← Real.rpow_mul hm.le]
  have ea : a ^ (1 - 1 / σ) / a = a ^ (-1 / σ) := by
    rw [← Real.rpow_sub_one ha.ne']; congr 1; ring
  have em : m ^ (γ - γ / σ - 1) * m ^ (1 - γ) = m ^ (γ * (-1 / σ)) := by
    rw [← Real.rpow_add hm]; congr 1; ring
  calc a ^ (-1 / σ) * m ^ (γ * (-1 / σ)) * Y ^ (1 / σ)
      = σ / (σ - 1) * ((1 - 1 / σ) * γ * (a ^ (1 - 1 / σ) / a) *
          (m ^ (γ - γ / σ - 1) * m ^ (1 - γ)) * Y ^ (1 / σ) / γ) := by
        rw [ea, em]; field_simp
    _ = _ := by field_simp

/-- AKMM, p. 679: **`Y = (c/γ)(σ/(σ−1))M`**. Revenue `pᵢyᵢ` is `(c/(γ(σ−1)/σ))mᵢ` at each
firm's optimum (§22.2 with returns `γ(σ−1)/σ`); final-good zero profit `∫pᵢyᵢ = Y` gives the
claim. -/
theorem mc_output_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {σ γ c Y : ℝ}
    (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1) (hc : 0 < c) (hY : 0 < Y)
    {a : Ω → ℝ} (ha : ∀ i, 0 < a i)
    (hrev : ∫ i, a i ^ ((σ - 1) / σ) * Y ^ (1 / σ) *
      simpleScale (γ * ((σ - 1) / σ)) c (a i ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ^
        (γ * ((σ - 1) / σ)) ∂P = Y) :
    Y = c / γ * (σ / (σ - 1)) *
      ∫ i, simpleScale (γ * ((σ - 1) / σ)) c (a i ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ∂P := by
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  have hA : ∀ i, 0 < a i ^ ((σ - 1) / σ) * Y ^ (1 / σ) := fun i => by
    have := ha i; positivity
  calc Y = _ := hrev.symm
    _ = _ := eq_22_3 P hc (mul_pos hγ hθ) hg hA
    _ = _ := by
      have hσ0 : σ ≠ 0 := by linarith
      have hσ1 : σ - 1 ≠ 0 := by linarith
      congr 1
      field_simp

/-- AKMM, p. 679: the modified aggregate productivity
`A = (∫ a^{1/(σ/(σ−1)−γ)})^{σ/(σ−1)−γ}`. -/
noncomputable def mcTFP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (σ γ : ℝ)
    (a : Ω → ℝ) : ℝ :=
  (∫ i, a i ^ (1 / (σ / (σ - 1) - γ)) ∂P) ^ (σ / (σ - 1) - γ)

/-- AKMM, p. 679: **the aggregate production function under monopolistic competition**. If the
combined inputs are `mᵢ = K aᵢ^{1/(σ/(σ−1)−γ)}` for some `K > 0` (the optimum, `mc_scale_form`),
then the Dixit–Stiglitz output of `yᵢ = aᵢmᵢ^γ` is `AM^γ`. -/
theorem mc_aggregate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {σ γ K : ℝ}
    (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1) (hK : 0 < K) {a : Ω → ℝ}
    (ha : ∀ i, 0 < a i) (hS : 0 < ∫ i, a i ^ (1 / (σ / (σ - 1) - γ)) ∂P) :
    Miao.NewKeynesian.nk_aggY P σ
        (fun i => a i * (K * a i ^ (1 / (σ / (σ - 1) - γ))) ^ γ) =
      mcTFP P σ γ a * (∫ i, K * a i ^ (1 / (σ / (σ - 1) - γ)) ∂P) ^ γ := by
  have hσ0 : σ ≠ 0 := by linarith
  have hσ1 : 0 < σ - 1 := by linarith
  set θ := (σ - 1) / σ with hθdef
  have hθ : 0 < θ := div_pos hσ1 (by linarith)
  have hinv : σ / (σ - 1) = 1 / θ := by rw [hθdef]; field_simp
  have hD : 0 < 1 / θ - γ := by
    rw [sub_pos, lt_div_iff₀ hθ]; linarith [mul_comm γ θ]
  unfold Miao.NewKeynesian.nk_aggY mcTFP
  rw [hinv] at hS ⊢
  rw [← hθdef]
  set e := 1 / (1 / θ - γ) with he
  have he0 : 0 < e := by positivity
  have hy : ∀ i, (a i * (K * a i ^ e) ^ γ) ^ θ = K ^ (γ * θ) * a i ^ e := fun i => by
    have hai := ha i
    have h1 : (K * a i ^ e) ^ γ = K ^ γ * a i ^ (e * γ) := by
      rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul hai.le]
    rw [h1, show a i * (K ^ γ * a i ^ (e * γ)) = K ^ γ * a i ^ (1 + e * γ) by
        rw [Real.rpow_add hai, Real.rpow_one]; ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hK.le,
      ← Real.rpow_mul hai.le]
    congr 2
    have hne : 1 - θ * γ ≠ 0 := by linarith [mul_comm γ θ]
    rw [he]; field_simp; ring
  set S := ∫ i, a i ^ e ∂P
  rw [integral_congr_ae (Filter.Eventually.of_forall hy), integral_const_mul, integral_const_mul,
    Real.mul_rpow (by positivity) hS.le, Real.mul_rpow hK.le hS.le, ← Real.rpow_mul hK.le]
  rw [show γ * θ * (1 / θ) = γ by field_simp]
  rw [show S ^ (1 / θ) = S ^ (1 / θ - γ) * S ^ γ by rw [← Real.rpow_add hS]; ring_nf]
  ring

/-- The optimal combined input has the form `K a^{1/(σ/(σ−1)−γ)}`, with `K` common to all
firms. -/
theorem mc_scale_form {σ γ c a Y : ℝ} (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1)
    (hc : 0 < c) (ha : 0 < a) (hY : 0 < Y) :
    simpleScale (γ * ((σ - 1) / σ)) c (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) =
      ((γ * ((σ - 1) / σ)) / c * Y ^ (1 / σ)) ^ (1 / (1 - γ * ((σ - 1) / σ))) *
        a ^ (1 / (σ / (σ - 1) - γ)) := by
  have hσ0 : σ ≠ 0 := by linarith
  have hσ1 : σ - 1 ≠ 0 := by linarith
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  have hg1 : 0 < 1 - γ * ((σ - 1) / σ) := by linarith
  unfold simpleScale
  rw [show γ * ((σ - 1) / σ) * (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) / c =
      (γ * ((σ - 1) / σ) / c * Y ^ (1 / σ)) * a ^ ((σ - 1) / σ) by ring,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha.le]
  congr 2
  field_simp

/-- AKMM, p. 679: **`Y = AM^γ` at the monopolistic-competition equilibrium**, combining
`mc_scale_form` and `mc_aggregate`. -/
theorem mc_aggregate_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {σ γ c Y : ℝ}
    (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1) (hc : 0 < c) (hY : 0 < Y)
    {a : Ω → ℝ} (ha : ∀ i, 0 < a i) (hS : 0 < ∫ i, a i ^ (1 / (σ / (σ - 1) - γ)) ∂P) :
    Miao.NewKeynesian.nk_aggY P σ (fun i => a i *
        simpleScale (γ * ((σ - 1) / σ)) c (a i ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ^ γ) =
      mcTFP P σ γ a *
        (∫ i, simpleScale (γ * ((σ - 1) / σ)) c (a i ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ∂P) ^ γ := by
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  have hK : 0 < ((γ * ((σ - 1) / σ)) / c * Y ^ (1 / σ)) ^ (1 / (1 - γ * ((σ - 1) / σ))) := by
    have : 0 < γ * ((σ - 1) / σ) := mul_pos hγ hθ
    positivity
  have h := mc_aggregate P hσ hγ hg hK ha hS
  simp only [← mc_scale_form hσ hγ hg hc (ha _) hY] at h
  exact h

end AKMM.HeterogeneousFirms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Oligopoly and endogenous markups: Atkeson–Burstein (AKMM §22.6.2, App. 22.A.4)

AKMM, §22.6.2, pp. 679–681, and Appendix 22.A.4, pp. 892–893. Sector `i` has `J` brands combined
by the CES aggregator (22.23) with elasticity `η > σ > 1`; the sector good enters (22.16).

* **The nested CES (22.24)–(22.25)**: with brand prices `p̂ⱼ = p qⱼ^{−1/η}y^{1/η}`, the sector
  price is the CES index of the brand prices and `Σ p̂ⱼqⱼ = py` (`eq_22_24`, `eq_22_25`); the sales
  share is `sⱼ = qⱼ^{(η−1)/η}/Σₖ qₖ^{(η−1)/η}` (`eq_22_29`).
* **Cournot (22.27)–(22.28)**: the derivative of the brand's revenue with respect to its own
  quantity, taking `Y` but not the sector output as given, is `p̂(1 − 1/ε(s))` with
  `ε(s) = ((1−s)/η + s/σ)^{−1}` (`eq_22_28`), so marginal revenue equal to marginal cost gives
  the markup `p̂ = ε/(ε−1)·MC` (`eq_22_27`).
* **Properties of `ε`**: `ε(0) = η`, `ε(1) = σ`, `ε` strictly decreasing on `[0, 1]` with values
  in `[σ, η]` (`cournot_endpoints`, `cournot_strictAntiOn`, `cournot_mem_Icc`); with `J` symmetric
  firms `ε = ((J−1)/(ηJ) + 1/(σJ))^{−1}` (`cournot_symmetric`), equal to `σ` for `J = 1`, rising in
  `J` (`cournot_symmetric_mono`) and tending to `η` (`cournot_symmetric_tendsto`); markups fall
  with `ε` (`markup_strictAnti`).
* **Bertrand (App. 22.A.4)**: the brand's demand `q = p̂^{−η}p^{η−σ}Y` has elasticity
  `ε(s) = η(1−s) + σs` (`bertrand_demand_deriv`, `eq_22_A_4`), giving the same pricing rule
  (`bertrand_markup`). Printed signs corrected: `(q/p̂)/(∂q/∂p̂) = −1/ε` and the first-order
  condition is `(1 + (q/p̂)/(∂q/∂p̂))p̂ = MC` (`bertrand_ratio`).
* **Cournot markups exceed Bertrand markups** (`cournot_le_bertrand`, `markup_cournot_ge`).
-/

open Filter Topology

namespace AKMM.HeterogeneousFirms

/-! ### The nested CES -/

/-- AKMM, (22.23), p. 680: sector output `y = (Σⱼ qⱼ^{(η−1)/η})^{η/(η−1)}`. -/
noncomputable def sectorOutput {J : Type*} [Fintype J] (η : ℝ) (q : J → ℝ) : ℝ :=
  (∑ j, q j ^ ((η - 1) / η)) ^ (η / (η - 1))

theorem sectorOutput_rpow {J : Type*} [Fintype J] {η : ℝ} (hη : 1 < η) {q : J → ℝ}
    (hq : ∀ j, 0 < q j) [Nonempty J] :
    sectorOutput η q ^ ((η - 1) / η) = ∑ j, q j ^ ((η - 1) / η) := by
  have hS : 0 < ∑ j, q j ^ ((η - 1) / η) :=
    Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hq j) _) Finset.univ_nonempty
  unfold sectorOutput
  rw [← Real.rpow_mul hS.le, show η / (η - 1) * ((η - 1) / η) = 1 by
    have : η - 1 ≠ 0 := by linarith
    have : η ≠ 0 := by linarith
    field_simp, Real.rpow_one]

/-- AKMM, (22.24)–(22.25), p. 680: with brand prices `p̂ⱼ = p qⱼ^{−1/η}y^{1/η}` (the within-sector
cost-minimisation condition (22.24)), total spending is `Σ p̂ⱼqⱼ = py` (22.25). -/
theorem eq_22_25 {J : Type*} [Fintype J] [Nonempty J] {η p : ℝ} (hη : 1 < η) {q : J → ℝ}
    (hq : ∀ j, 0 < q j) :
    ∑ j, p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η) * q j = p * sectorOutput η q := by
  have hη0 : η ≠ 0 := by linarith
  have hy : 0 < sectorOutput η q := by
    unfold sectorOutput
    exact Real.rpow_pos_of_pos (Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hq j) _)
      Finset.univ_nonempty) _
  have e : ∀ j, p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η) * q j =
      p * sectorOutput η q ^ (1 / η) * q j ^ ((η - 1) / η) := fun j => by
    rw [show q j ^ ((η - 1) / η) = q j ^ (-1 / η) * q j by
      rw [← Real.rpow_add_one (hq j).ne']; congr 1; field_simp; ring]
    ring
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, ← sectorOutput_rpow hη hq,
    mul_assoc, ← Real.rpow_add hy]
  rw [show 1 / η + (η - 1) / η = 1 by field_simp; ring, Real.rpow_one]

/-- AKMM, p. 680, after (22.24): the sector price is the CES index of the brand prices,
`p = (Σ p̂ⱼ^{1−η})^{1/(1−η)}`. -/
theorem eq_22_24 {J : Type*} [Fintype J] [Nonempty J] {η p : ℝ} (hη : 1 < η) (hp : 0 < p)
    {q : J → ℝ} (hq : ∀ j, 0 < q j) :
    (∑ j, (p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η)) ^ (1 - η)) ^ (1 / (1 - η)) = p := by
  have hη0 : η ≠ 0 := by linarith
  have hη1 : 1 - η ≠ 0 := by linarith
  have hy : 0 < sectorOutput η q := by
    unfold sectorOutput
    exact Real.rpow_pos_of_pos (Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hq j) _)
      Finset.univ_nonempty) _
  have e : ∀ j, (p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η)) ^ (1 - η) =
      p ^ (1 - η) * sectorOutput η q ^ ((1 - η) / η) * q j ^ ((η - 1) / η) := fun j => by
    have hqj := hq j
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hp.le (by positivity),
      ← Real.rpow_mul hqj.le, ← Real.rpow_mul hy.le]
    rw [show -1 / η * (1 - η) = (η - 1) / η by field_simp; ring,
      show 1 / η * (1 - η) = (1 - η) / η by ring]
    ring
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, ← sectorOutput_rpow hη hq,
    mul_assoc, ← Real.rpow_add hy, show (1 - η) / η + (η - 1) / η = 0 by ring, Real.rpow_zero,
    mul_one, ← Real.rpow_mul hp.le, mul_one_div_cancel hη1, Real.rpow_one]

/-- AKMM, (22.29), p. 681: the sales share `sⱼ = p̂ⱼqⱼ/(py) = qⱼ^{(η−1)/η}/Σₖ qₖ^{(η−1)/η}`. -/
theorem eq_22_29 {J : Type*} [Fintype J] [Nonempty J] {η p : ℝ} (hη : 1 < η) (hp : 0 < p)
    {q : J → ℝ} (hq : ∀ j, 0 < q j) (j : J) :
    p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η) * q j / (p * sectorOutput η q) =
      q j ^ ((η - 1) / η) / ∑ k, q k ^ ((η - 1) / η) := by
  have hη0 : η ≠ 0 := by linarith
  have hy : 0 < sectorOutput η q := by
    unfold sectorOutput
    exact Real.rpow_pos_of_pos (Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hq j) _)
      Finset.univ_nonempty) _
  have hqρ : q j ^ (-1 / η) * q j = q j ^ ((η - 1) / η) := by
    rw [← Real.rpow_add_one (hq j).ne']; congr 1; field_simp; ring
  have e1 : p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η) * q j =
      (p * sectorOutput η q ^ (1 / η)) * q j ^ ((η - 1) / η) := by rw [← hqρ]; ring
  have e2 : p * sectorOutput η q =
      (p * sectorOutput η q ^ (1 / η)) * sectorOutput η q ^ ((η - 1) / η) := by
    rw [mul_assoc, ← Real.rpow_add hy, show 1 / η + (η - 1) / η = 1 by field_simp; ring,
      Real.rpow_one]
  have hne : p * sectorOutput η q ^ (1 / η) ≠ 0 := by positivity
  rw [e1, e2, mul_div_mul_left _ _ hne, sectorOutput_rpow hη hq]

/-! ### Cournot -/

/-- AKMM, (22.28), p. 681: the Cournot demand elasticity `ε(s) = ((1−s)/η + s/σ)^{−1}`. -/
noncomputable def cournotElas (σ η s : ℝ) : ℝ := ((1 - s) / η + s / σ)⁻¹

/-- AKMM, App. 22.A.4, p. 893: the Bertrand demand elasticity `ε(s) = η(1−s) + σs`. -/
def bertrandElas (σ η s : ℝ) : ℝ := η * (1 - s) + σ * s

/-- AKMM, (22.28), p. 681: **the Cournot marginal revenue**. Let the other brands contribute
`C ≥ 0` to `Σ qₖ^ρ`, `ρ = (η−1)/η`, so `y(q) = (C + q^ρ)^{1/ρ}`; the revenue
`p̂q = q^ρ(C + q^ρ)^{(1/η−1/σ)/ρ}Y^{1/σ}` (from (22.18), (22.24)) has derivative `p̂(1 − 1/ε(s))`
at `q > 0`, with `p̂ = q^{ρ−1}(C + q^ρ)^{(1/η−1/σ)/ρ}Y^{1/σ}` and the sales share
`s = q^ρ/(C + q^ρ)`. -/
theorem eq_22_28 {σ η C Z q : ℝ} (hσ : 1 < σ) (hη : 1 < η) (hC : 0 ≤ C) (hq : 0 < q) :
    HasDerivAt
      (fun x => Z * x ^ ((η - 1) / η) * (C + x ^ ((η - 1) / η)) ^ ((1 / η - 1 / σ) /
        ((η - 1) / η)))
      (Z * q ^ ((η - 1) / η - 1) * (C + q ^ ((η - 1) / η)) ^ ((1 / η - 1 / σ) / ((η - 1) / η)) *
        (1 - 1 / cournotElas σ η (q ^ ((η - 1) / η) / (C + q ^ ((η - 1) / η))))) q := by
  set ρ := (η - 1) / η with hρ
  set κ := (1 / η - 1 / σ) / ρ with hκ
  have hη0 : η ≠ 0 := by linarith
  have hσ0 : σ ≠ 0 := by linarith
  have hρ0 : ρ ≠ 0 := by rw [hρ]; exact div_ne_zero (by linarith) hη0
  have hqρ : 0 < q ^ ρ := Real.rpow_pos_of_pos hq ρ
  have hg : 0 < C + q ^ ρ := by linarith
  have h1 : HasDerivAt (fun x => x ^ ρ) (ρ * q ^ (ρ - 1)) q :=
    Real.hasDerivAt_rpow_const (Or.inl hq.ne')
  have h3 : HasDerivAt (fun x => (C + x ^ ρ) ^ κ)
      (ρ * q ^ (ρ - 1) * κ * (C + q ^ ρ) ^ (κ - 1)) q :=
    (h1.const_add C).rpow_const (Or.inl hg.ne')
  have h := (h1.mul h3).const_mul Z
  convert h using 1
  · funext x; simp only [Pi.mul_apply]; ring
  · rw [cournotElas, one_div, inv_inv, Real.rpow_sub_one hg.ne']
    have hρκ : ρ * κ = 1 / η - 1 / σ := by rw [hκ]; field_simp
    have hρ' : ρ = 1 - 1 / η := by rw [hρ]; field_simp
    linear_combination (-(Z * q ^ (ρ - 1) * (C + q ^ ρ) ^ κ)) * hρ' +
      (-(Z * q ^ (ρ - 1) * (C + q ^ ρ) ^ κ * (q ^ ρ / (C + q ^ ρ)))) * hρκ

/-- AKMM, (22.27), p. 680: **Cournot pricing**. If marginal revenue `p̂(1 − 1/ε)` equals marginal
cost `MC` and `ε > 1`, then `p̂ = ε/(ε−1)·MC`. -/
theorem eq_22_27 {ε ph MC : ℝ} (hε : 1 < ε) (h : ph * (1 - 1 / ε) = MC) :
    ph = ε / (ε - 1) * MC := by
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  rw [← h]; field_simp

/-- AKMM, p. 681: `ε(0) = η` and `ε(1) = σ`. -/
theorem cournot_endpoints (σ η : ℝ) : cournotElas σ η 0 = η ∧ cournotElas σ η 1 = σ := by
  unfold cournotElas; simp

/-- AKMM, p. 681: for `1 < σ < η`, `ε(s)` **decreases strictly** on `[0, 1]`. -/
theorem cournot_strictAntiOn {σ η : ℝ} (hσ : 1 < σ) (hση : σ < η) :
    StrictAntiOn (cournotElas σ η) (Set.Icc 0 1) := by
  intro s hs t ht hst
  unfold cournotElas
  have hη : 0 < η := by linarith
  have hσ0 : 0 < σ := by linarith
  have hd : 1 / η < 1 / σ := one_div_lt_one_div_of_lt hσ0 hση
  have hps : 0 < (1 - s) / η + s / σ := by
    have h1 : 0 ≤ (1 - s) / η := div_nonneg (by linarith [hs.2]) hη.le
    have h2 : 0 ≤ s / σ := div_nonneg hs.1 hσ0.le
    rcases hs.1.lt_or_eq with h | h
    · have : 0 < s / σ := div_pos h hσ0; linarith
    · subst h; simp only [sub_zero, one_div, zero_div, add_zero, inv_pos, gt_iff_lt]; exact hη
  apply inv_strictAnti₀ hps
  have : (1 - s) / η + s / σ = 1 / η + s * (1 / σ - 1 / η) := by ring
  have : (1 - t) / η + t / σ = 1 / η + t * (1 / σ - 1 / η) := by ring
  nlinarith

/-- AKMM, p. 681: for `s ∈ [0, 1]` and `1 < σ < η`, `σ ≤ ε(s) ≤ η`. -/
theorem cournot_mem_Icc {σ η s : ℝ} (hσ : 1 < σ) (hση : σ < η) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    cournotElas σ η s ∈ Set.Icc σ η := by
  have hA := cournot_strictAntiOn hσ hση
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨e0, e1⟩ := cournot_endpoints σ η
  constructor
  · calc σ = cournotElas σ η 1 := e1.symm
      _ ≤ cournotElas σ η s := hA.antitoneOn hs h1 hs.2
  · calc cournotElas σ η s ≤ cournotElas σ η 0 := hA.antitoneOn h0 hs hs.1
      _ = η := e0

/-- AKMM, p. 681: **symmetric firms**: with `s = 1/J`,
`ε = ((1/η)(J−1)/J + 1/(σJ))^{−1}`. -/
theorem cournot_symmetric (σ η : ℝ) {J : ℝ} (hJ : J ≠ 0) :
    cournotElas σ η (1 / J) = (1 / η * ((J - 1) / J) + 1 / (σ * J))⁻¹ := by
  unfold cournotElas
  congr 1
  field_simp

/-- AKMM, p. 681: one firm per sector (`J = 1`) is monopolistic competition, `ε = σ`. -/
theorem cournot_symmetric_one (σ η : ℝ) : cournotElas σ η (1 / 1) = σ := by
  rw [div_one]; exact (cournot_endpoints σ η).2

/-- AKMM, p. 681: **the markup falls as the number of firms rises**: `ε(1/J)` is strictly
increasing in `J ≥ 1`. -/
theorem cournot_symmetric_mono {σ η : ℝ} (hσ : 1 < σ) (hση : σ < η) {J J' : ℕ} (hJ : 1 ≤ J)
    (hJJ : J < J') : cournotElas σ η (1 / (J : ℝ)) < cournotElas σ η (1 / (J' : ℝ)) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJ'0 : (0 : ℝ) < J' := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hJ).trans hJJ
  have hJJ' : (J : ℝ) < J' := by exact_mod_cast hJJ
  apply cournot_strictAntiOn hσ hση
  · have h1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    exact ⟨div_nonneg zero_le_one hJ'0.le, (div_le_one hJ'0).mpr (by linarith)⟩
  · have h1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    exact ⟨div_nonneg zero_le_one hJ0.le, (div_le_one hJ0).mpr h1⟩
  · exact one_div_lt_one_div_of_lt hJ0 hJJ'

/-- AKMM, p. 681: **`ε(1/J) → η` as `J → ∞`**. -/
theorem cournot_symmetric_tendsto {σ η : ℝ} (hη : 0 < η) :
    Tendsto (fun J : ℕ => cournotElas σ η (1 / (J : ℝ))) atTop (𝓝 η) := by
  have h : Tendsto (fun J : ℕ => (1 / (J : ℝ))) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hc : ContinuousAt (cournotElas σ η) 0 := by
    unfold cournotElas
    refine ContinuousAt.inv₀ (by fun_prop) ?_
    simp only [sub_zero, one_div, zero_div, add_zero, ne_eq, inv_eq_zero]; exact hη.ne'
  have := hc.tendsto.comp h
  rwa [(cournot_endpoints σ η).1] at this

/-- AKMM, p. 681: the markup `ε/(ε−1)` is strictly decreasing in `ε > 1`. -/
theorem markup_strictAnti : StrictAntiOn (fun ε : ℝ => ε / (ε - 1)) (Set.Ioi 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < y - 1 := by linarith
  rw [div_lt_div_iff₀ h2 h1]
  nlinarith

/-! ### Bertrand -/

/-- AKMM, App. 22.A.4, pp. 892–893: **the Bertrand demand curve**. With the other brands'
`D = Σ_{k≠j} p̂ₖ^{1−η} ≥ 0`, sector price `p = (D + p̂^{1−η})^{1/(1−η)}` (22.A.4) and sector demand
`y = p^{−σ}Y` (22.A.3), the brand demand `q = (p̂/p)^{−η}y` from (22.A.2) is
`p̂^{−η}(D + p̂^{1−η})^{(η−σ)/(1−η)}Y`. -/
theorem bertrand_demand_form {σ η D Y ph : ℝ} (hη : 1 < η) (hD : 0 ≤ D) (hph : 0 < ph) :
    (ph / (D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-η) *
        (((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-σ) * Y) =
      ph ^ (-η) * (D + ph ^ (1 - η)) ^ ((η - σ) / (1 - η)) * Y := by
  have hG : 0 < D + ph ^ (1 - η) := by have := Real.rpow_pos_of_pos hph (1 - η); linarith
  have hp : 0 < (D + ph ^ (1 - η)) ^ (1 / (1 - η)) := Real.rpow_pos_of_pos hG _
  have h1η : 1 - η ≠ 0 := by linarith
  have e : ((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-σ) /
      ((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-η) = (D + ph ^ (1 - η)) ^ ((η - σ) / (1 - η)) := by
    rw [← Real.rpow_sub hp, ← Real.rpow_mul hG.le]; congr 1; field_simp; ring
  calc (ph / (D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-η) *
        (((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-σ) * Y)
      = ph ^ (-η) * (((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-σ) /
          ((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-η)) * Y := by
        rw [Real.div_rpow hph.le hp.le]; ring
    _ = _ := by rw [e]

/-- AKMM, App. 22.A.4, p. 893: **the Bertrand demand slope**. The derivative of
`q(p̂) = p̂^{−η}(D + p̂^{1−η})^{(η−σ)/(1−η)}Y` is `−ε(s)q/p̂` with `ε(s) = η(1−s) + σs` and
`s = p̂^{1−η}/(D + p̂^{1−η})` the sales share. -/
theorem bertrand_demand_deriv {σ η D Y ph : ℝ} (hη : 1 < η) (hD : 0 ≤ D) (hph : 0 < ph) :
    HasDerivAt (fun x => x ^ (-η) * (D + x ^ (1 - η)) ^ ((η - σ) / (1 - η)) * Y)
      (-bertrandElas σ η (ph ^ (1 - η) / (D + ph ^ (1 - η))) *
        (ph ^ (-η) * (D + ph ^ (1 - η)) ^ ((η - σ) / (1 - η)) * Y) / ph) ph := by
  have h1η : 1 - η ≠ 0 := by linarith
  have hpp : 0 < ph ^ (1 - η) := Real.rpow_pos_of_pos hph _
  have hG : 0 < D + ph ^ (1 - η) := by linarith
  have ha : HasDerivAt (fun x => x ^ (-η)) (-η * ph ^ (-η - 1)) ph :=
    Real.hasDerivAt_rpow_const (Or.inl hph.ne')
  have hb : HasDerivAt (fun x => x ^ (1 - η)) ((1 - η) * ph ^ (1 - η - 1)) ph :=
    Real.hasDerivAt_rpow_const (Or.inl hph.ne')
  have hc : HasDerivAt (fun x => (D + x ^ (1 - η)) ^ ((η - σ) / (1 - η)))
      ((1 - η) * ph ^ (1 - η - 1) * ((η - σ) / (1 - η)) *
        (D + ph ^ (1 - η)) ^ ((η - σ) / (1 - η) - 1)) ph :=
    (hb.const_add D).rpow_const (Or.inl hG.ne')
  have h := (ha.mul hc).mul_const Y
  convert h using 1
  rw [bertrandElas, Real.rpow_sub_one hG.ne', Real.rpow_sub_one hph.ne',
    Real.rpow_sub_one hph.ne']
  have e : ph ^ (1 - η) = ph * ph ^ (-η) := by
    rw [show (1 - η) = -η + 1 by ring, Real.rpow_add_one hph.ne']; ring
  rw [e] at hG ⊢
  have : 0 < ph ^ (-η) := Real.rpow_pos_of_pos hph _
  field_simp
  ring

/-- AKMM, App. 22.A.4, p. 893, corrected: with `q' = −εq/p̂`, `(q/p̂)/q' = −1/ε` (printed `1/ε`). -/
theorem bertrand_ratio {ε q ph : ℝ} (hε : ε ≠ 0) (hq : q ≠ 0) (hph : ph ≠ 0) :
    (q / ph) / (-ε * q / ph) = -(1 / ε) := by
  field_simp

/-- AKMM, App. 22.A.4, p. 893: the printed `(q/p̂)/(∂q/∂p̂) = 1/ε` is false for every `ε ≠ 0`. -/
theorem bertrand_ratio_printed_false {ε q ph : ℝ} (hε : ε ≠ 0) (hq : q ≠ 0) (hph : ph ≠ 0) :
    (q / ph) / (-ε * q / ph) ≠ 1 / ε := by
  rw [bertrand_ratio hε hq hph]
  intro h
  have : 1 / ε = 0 := by linarith
  exact hε (by simpa using this)

/-- AKMM, App. 22.A.4, p. 893: **Bertrand pricing**. The first-order condition
`p̂q' + q = MC·q'` with `q' = −εq/p̂`, `q > 0`, `ε > 1` gives `p̂ = ε/(ε−1)·MC`; equivalently the
corrected `(1 + (q/p̂)/q')p̂ = MC`. -/
theorem bertrand_markup {ε q ph MC : ℝ} (hε : 1 < ε) (hq : 0 < q) (hph : 0 < ph)
    (hfoc : ph * (-ε * q / ph) + q = MC * (-ε * q / ph)) :
    ph = ε / (ε - 1) * MC ∧ (1 + (q / ph) / (-ε * q / ph)) * ph = MC := by
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  have hMC : MC = ph * (1 - 1 / ε) := by
    field_simp at hfoc ⊢
    nlinarith
  refine ⟨by rw [hMC]; field_simp, ?_⟩
  rw [bertrand_ratio hε0 hq.ne' hph.ne', hMC]; ring

/-- AKMM, App. 22.A.4: `ε(0) = η`, `ε(1) = σ` for Bertrand too, and `ε` decreases in `s` when
`σ < η`. -/
theorem eq_22_A_4 {σ η : ℝ} (hση : σ < η) :
    bertrandElas σ η 0 = η ∧ bertrandElas σ η 1 = σ ∧ StrictAnti (bertrandElas σ η) := by
  refine ⟨by simp [bertrandElas], by simp [bertrandElas], fun s t hst => ?_⟩
  unfold bertrandElas; nlinarith

/-- AKMM, p. 681: **the Cournot elasticity is below the Bertrand elasticity** (harmonic versus
arithmetic mean of `η` and `σ`) for `s ∈ [0, 1]`. -/
theorem cournot_le_bertrand {σ η s : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    cournotElas σ η s ≤ bertrandElas σ η s := by
  unfold cournotElas bertrandElas
  obtain ⟨h0, h1⟩ := hs
  have hps : 0 < (1 - s) / η + s / σ := by
    rcases h0.lt_or_eq with h | h
    · have : 0 < s / σ := div_pos h hσ
      have : 0 ≤ (1 - s) / η := div_nonneg (by linarith) hη.le
      linarith
    · subst h; simp only [sub_zero, one_div, zero_div, add_zero, inv_pos]; exact hη
  rw [inv_le_iff_one_le_mul₀' hps]
  have key : (η * (1 - s) + σ * s) * ((1 - s) / η + s / σ) - 1 =
      s * (1 - s) * (η - σ) ^ 2 / (η * σ) := by
    field_simp; ring
  have : 0 ≤ s * (1 - s) * (η - σ) ^ 2 / (η * σ) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg h0 (by linarith)) (sq_nonneg _)
  linarith

/-- AKMM, p. 681: **Cournot markups are at least Bertrand markups**. -/
theorem markup_cournot_ge {σ η s : ℝ} (hσ : 1 < σ) (hση : σ < η) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    bertrandElas σ η s / (bertrandElas σ η s - 1) ≤
      cournotElas σ η s / (cournotElas σ η s - 1) := by
  have hc := cournot_mem_Icc hσ hση hs
  have hle := cournot_le_bertrand (σ := σ) (η := η) (by linarith) (by linarith) hs
  have hc1 : 1 < cournotElas σ η s := by linarith [hc.1]
  rcases hle.lt_or_eq with h | h
  · exact (markup_strictAnti (Set.mem_Ioi.mpr hc1)
      (Set.mem_Ioi.mpr (show 1 < bertrandElas σ η s by linarith)) h).le
  · rw [h]

end AKMM.HeterogeneousFirms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Idiosyncratic shocks and aggregate volatility (AKMM §22.7, (22.30))

AKMM, §22.7, pp. 681–682. GDP is the sum of the outputs of `N` firms, and firm growth rates
`σεᵢ` have `εᵢ` with variance one and no correlation across firms (the book assumes i.i.d.).

* GDP growth is the share-weighted average of firm growth (`granular_growth`).
* **(22.30)**: `σ_Y = σ √(Σ (yᵢ/Y)²)` (`eq_22_30`).
* **Equal sizes**: `σ_Y = σ/√N` (`granular_equal_sizes`), and `√(10⁶) = 1000` (p. 682); equal
  sizes give the smallest volatility for given `N` (`granular_herfindahl_ge`).
* Gabaix's result under Zipf's law (`σ_Y log N` converges in distribution) is not formalised (a
  generalised central limit theorem, beyond the text, decision 5).
-/

open MeasureTheory ProbabilityTheory

namespace AKMM.HeterogeneousFirms

/-- AKMM, p. 682: if `y_{i,t+1} = yᵢ(1 + σεᵢ)`, GDP growth `(Y_{t+1} − Y_t)/Y_t` is
`Σᵢ (yᵢ/Y)σεᵢ`. -/
theorem granular_growth {ι : Type*} [Fintype ι] (y e : ι → ℝ) (σ : ℝ) (hY : ∑ i, y i ≠ 0) :
    (∑ i, y i * (1 + σ * e i) - ∑ i, y i) / ∑ i, y i = ∑ i, y i / (∑ j, y j) * (σ * e i) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by field_simp; ring

/-- AKMM, (22.30), p. 682: **aggregate volatility**. With firm shocks `εᵢ` of unit variance and
uncorrelated across firms, the variance of GDP growth `Σ sᵢσεᵢ` is `σ² Σ sᵢ²`, so its standard
deviation is `σ √(Σ sᵢ²)`, `sᵢ = yᵢ/Y`. -/
theorem eq_22_30 {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    [Fintype ι] [DecidableEq ι] {e : ι → Ω → ℝ} (he : ∀ i, MemLp (e i) 2 P)
    (hcov : ∀ i j, cov[(e i), (e j); P] = if i = j then 1 else 0) (s : ι → ℝ) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    Var[(fun ω => ∑ i, s i * (σ * e i ω)); P] = σ ^ 2 * ∑ i, s i ^ 2 ∧
      Real.sqrt (Var[(fun ω => ∑ i, s i * (σ * e i ω)); P]) = σ * Real.sqrt (∑ i, s i ^ 2) := by
  have hX : ∀ i, MemLp (fun ω => s i * (σ * e i ω)) 2 P := fun i =>
    ((he i).const_mul σ).const_mul (s i)
  have hv : Var[(fun ω => ∑ i, s i * (σ * e i ω)); P] = σ ^ 2 * ∑ i, s i ^ 2 := by
    rw [variance_fun_sum hX]
    have hc : ∀ i j, cov[(fun ω => s i * (σ * e i ω)), (fun ω => s j * (σ * e j ω)); P] =
        if i = j then σ ^ 2 * s i ^ 2 else 0 := fun i j => by
      have e1 : (fun ω => s i * (σ * e i ω)) = fun ω => (s i * σ) * e i ω := by
        funext ω; ring
      have e2 : (fun ω => s j * (σ * e j ω)) = fun ω => (s j * σ) * e j ω := by
        funext ω; ring
      rw [e1, e2, covariance_const_mul_left, covariance_const_mul_right, hcov]
      split_ifs with h
      · subst h; ring
      · ring
    simp only [hc, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]
  refine ⟨hv, ?_⟩
  rw [hv, Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ]

/-- AKMM, p. 682: **equal sizes**: with `sᵢ = 1/N`, `σ √(Σ sᵢ²) = σ/√N`. -/
theorem granular_equal_sizes {N : ℕ} (hN : 0 < N) (σ : ℝ) :
    σ * Real.sqrt (∑ _i : Fin N, (1 / (N : ℝ)) ^ 2) = σ / Real.sqrt N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show (N : ℝ) * (1 / (N : ℝ)) ^ 2 = 1 / N by field_simp, Real.sqrt_div' _ hN'.le,
    Real.sqrt_one]
  ring

/-- AKMM, p. 682: with one million firms, `1/√N = 0.001`. -/
theorem granular_million : 1 / Real.sqrt (1000000 : ℝ) = 0.001 := by
  rw [show (1000000 : ℝ) = 1000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- AKMM, p. 682: **equal sizes minimise aggregate volatility**: shares summing to one have
`Σ sᵢ² ≥ 1/N` (Cauchy–Schwarz), with equality at `sᵢ = 1/N`. -/
theorem granular_herfindahl_ge {N : ℕ} (hN : 0 < N) (s : Fin N → ℝ) (hs : ∑ i, s i = 1) :
    1 / (N : ℝ) ≤ ∑ i, s i ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : 0 ≤ ∑ i, (s i - 1 / N) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have e : ∑ i, (s i - 1 / N) ^ 2 = ∑ i, s i ^ 2 - 2 / N * ∑ i, s i + N * (1 / N) ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    congr 1; congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, hs] at h0
  have : (N : ℝ) * (1 / N) ^ 2 = 1 / N := by field_simp
  rw [this] at h0
  have : 2 / (N : ℝ) * 1 = 2 * (1 / N) := by ring
  linarith

end AKMM.HeterogeneousFirms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hulten's theorem (AKMM §22.7.2, App. 22.A.5)

AKMM, §22.7.2, pp. 683–684, (22.31)–(22.32), and Appendix 22.A.5, pp. 894–896.

The economy has goods `G` and primary factors `V` (the appendix has labour only; the text and the
two-sector example also have capital), both finite; the commodity space is `G ⊕ V → ℝ`. Sector
`j` turns factors `ℓ ≥ 0` and intermediates `x ≥ 0` into `y ≤ aⱼFⱼ(ℓ, x)` of good `j`; the
representative consumer supplies the factor endowment inelastically and has utility `U(c)` over
goods. The competitive equilibrium and Pareto optimality are those of Stokey–Lucas–Prescott
Chapter 15 (`StokeyLucasPrescott.ParetoOptimaEquilibria`), and the **First Welfare Theorem**
(`theorem_15_3`) is imported.

* **Hulten's theorem (22.31), App. 22.A.5**: if the competitive equilibrium is locally nonsatiated,
  `U` is differentiable at `c` with gradient the goods prices (22.A.5, with the book's
  normalisation `λ = 1`) and linearly homogeneous, and the planner's value `V(aᵢ)` is
  differentiable in `aᵢ`, then `dV/daᵢ = pᵢyᵢ/aᵢ` (22.A.8), `V = U(c) = Σ pc` (22.A.6), and the
  elasticity of GDP with respect to `aᵢ` is the Domar weight `pᵢyᵢ/Σ pc` (`hulten`). The
  differentiability of the planner's value is an extra hypothesis (the book's envelope theorem
  presumes it); the proof uses only a lower bound: shifting the extra output of sector `i` to
  consumption is feasible.
* **The two-sector example (22.32)**: `Y = a₁(a₂K)^{1−γ}L^γ`, its elasticities `1` and `1 − γ`,
  the intermediate price and the Domar weights `1` and `1 − γ`, which differ from the value-added
  shares `γ` and `1 − γ` (`eq_22_32`, `hulten_example_prices`).
-/

open Filter Topology StokeyLucasPrescott.ParetoOptimaEquilibria

namespace AKMM.HeterogeneousFirms

variable {G V : Type*} [Fintype G] [Fintype V] [DecidableEq G]

/-- The net output vector of sector `j`: `y` of good `j`, minus intermediates `x` and factors
`ℓ`. -/
def hultenNet (j : G) (y : ℝ) (l : V → ℝ) (x : G → ℝ) : G ⊕ V → ℝ :=
  Sum.elim (fun g => (if g = j then y else 0) - x g) (fun v => -l v)

/-- AKMM, p. 894: the production set of sector `j`, `yⱼ ≤ aⱼFⱼ(ℓⱼ, xⱼ)`. -/
def hultenTech (F : G → (V → ℝ) → (G → ℝ) → ℝ) (a : G → ℝ) (j : G) : Set (G ⊕ V → ℝ) :=
  {z | ∃ y l x, 0 ≤ l ∧ 0 ≤ x ∧ y ≤ a j * F j l x ∧ z = hultenNet j y l x}

/-- AKMM, p. 894: the consumer's set: any goods bundle, with the factor endowment `e` supplied. -/
def hultenCons (e : V → ℝ) : Unit → Set (G ⊕ V → ℝ) :=
  fun _ => {z | ∀ v, z (Sum.inr v) = -e v}

/-- The consumer's utility `U` of the goods part of a bundle. -/
def hultenUtil (U : (G → ℝ) → ℝ) : Unit → (G ⊕ V → ℝ) → ℝ :=
  fun _ z => U fun g => z (Sum.inl g)

/-- The embedding of goods bundles in the commodity space. -/
noncomputable def hultenGoods : (G → ℝ) →L[ℝ] (G ⊕ V → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun d => Sum.elim d 0
      map_add' := fun d d' => by funext s; cases s <;> simp
      map_smul' := fun r d => by funext s; cases s <;> simp }

omit [Fintype V] [DecidableEq G] in
theorem hulten_goods_apply (d : G → ℝ) (s : G ⊕ V) :
    hultenGoods d s = Sum.elim d (0 : V → ℝ) s := rfl

omit [Fintype G] [DecidableEq G] in
/-- AKMM, App. 22.A.5, (22.A.6), p. 895: **GDP equals utility**. If `U` is linearly homogeneous
and differentiable at `c` with gradient the prices (22.A.5, `λ = 1`), then
`Y = Σ pᵢcᵢ = U(c)` (Euler's theorem). -/
theorem eq_22_A_6 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : E → ℝ} {c : E}
    {L : E →L[ℝ] ℝ}
    (hU : HasFDerivAt U L c) (hhom : ∀ s : ℝ, 0 < s → U (s • c) = s * U c) : L c = U c := by
  have h1 : HasDerivAt (fun s : ℝ => U (s • c)) (L c) 1 := by
    have hs : HasDerivAt (fun s : ℝ => s • c) c 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const c
    have hU' : HasFDerivAt U L ((1 : ℝ) • c) := by rwa [one_smul]
    exact hU'.comp_hasDerivAt (1 : ℝ) hs
  have h2 : HasDerivAt (fun s : ℝ => U (s • c)) (U c) 1 := by
    have h : HasDerivAt (fun s : ℝ => s * U c) (U c) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const (U c)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact hhom s hs
  exact h1.unique h2

/-- AKMM, (22.31), p. 683, and App. 22.A.5, pp. 894–896: **Hulten's theorem**. Let `(x, y)` be a
competitive equilibrium at prices `φ` of the economy with productivities `a`, locally
nonsatiated, with consumption `c` and sector `i` on its frontier, `yᵢ = aᵢFᵢ(ℓᵢ, xᵢ)`. Let `U` be
differentiable at `c` with gradient `pc ↦ φ(c)` (22.A.5) and linearly homogeneous, and let
`V(t)` be the planner's value when sector `i`'s productivity is `t` (the least upper bound of
feasible utilities), differentiable at `aᵢ` with derivative `D`. Then `V(aᵢ) = U(c) = Σpc`,
`D = pᵢyᵢ/aᵢ` (22.A.8) and `D·aᵢ/V(aᵢ) = pᵢyᵢ/Σpc`, the Domar weight. -/
theorem hulten {F : G → (V → ℝ) → (G → ℝ) → ℝ} {a : G → ℝ} {e : V → ℝ}
    {U : (G → ℝ) → ℝ} {xc : Unit → (G ⊕ V → ℝ)} {ys : G → (G ⊕ V → ℝ)}
    {φ : StrongDual ℝ (G ⊕ V → ℝ)}
    (hCE : CompetitiveEq (hultenCons e) (hultenUtil U) (hultenTech F a) xc ys φ)
    (hLNS : LocalNonsatiation (hultenCons e) (hultenUtil U))
    {i : G} {li : V → ℝ} {xi : G → ℝ} (hli : 0 ≤ li) (hxi : 0 ≤ xi)
    (hys : ys i = hultenNet i (a i * F i li xi) li xi)
    (hU : HasFDerivAt U (φ.comp hultenGoods) (fun g => xc () (Sum.inl g)))
    (hhom : ∀ s : ℝ, 0 < s → U (s • fun g => xc () (Sum.inl g)) =
      s * U (fun g => xc () (Sum.inl g)))
    {Vf : ℝ → ℝ} (hV : ∀ t, IsLUB {r | ∃ x' y', Feasible (hultenCons e)
      (hultenTech F (Function.update a i t)) x' y' ∧ r = hultenUtil U () (x' ())} (Vf t))
    {D : ℝ} (hVd : HasDerivAt Vf D (a i)) (ha : a i ≠ 0)
    (hY : φ (hultenGoods fun g => xc () (Sum.inl g)) ≠ 0) :
    Vf (a i) = U (fun g => xc () (Sum.inl g)) ∧
      U (fun g => xc () (Sum.inl g)) = φ (hultenGoods fun g => xc () (Sum.inl g)) ∧
      D = φ (hultenGoods (Pi.single i 1)) * (a i * F i li xi) / a i ∧
      D * a i / Vf (a i) = φ (hultenGoods (Pi.single i 1)) * (a i * F i li xi) /
        φ (hultenGoods fun g => xc () (Sum.inl g)) := by
  set c : G → ℝ := fun g => xc () (Sum.inl g) with hc
  set Fi := F i li xi
  set δ : G → ℝ := Pi.single i Fi
  -- the perturbed allocation: extra output of sector `i` goes to consumption
  let x' : ℝ → Unit → (G ⊕ V → ℝ) := fun t _ => xc () + hultenGoods ((t - a i) • δ)
  let y' : ℝ → G → (G ⊕ V → ℝ) := fun t => Function.update ys i (hultenNet i (t * Fi) li xi)
  have hnet : ∀ t, hultenNet i (t * Fi) li xi - hultenNet i (a i * Fi) li xi =
      hultenGoods ((t - a i) • δ) := fun t => by
    funext s
    cases s with
    | inl g =>
      simp only [hultenNet, Pi.sub_apply, Sum.elim_inl, hulten_goods_apply, Pi.smul_apply,
        smul_eq_mul, δ]
      by_cases hg : g = i
      · subst hg; simp; ring
      · simp [hg]
    | inr v => simp [hultenNet, hulten_goods_apply]
  have hfeas : ∀ t, Feasible (hultenCons e) (hultenTech F (Function.update a i t)) (x' t)
      (y' t) := fun t => by
    obtain ⟨⟨hX, hYs, hsum⟩, -, -⟩ := hCE
    refine ⟨fun u => ?_, fun j => ?_, ?_⟩
    · intro v
      have := hX () v
      simp only [x', Pi.add_apply, hulten_goods_apply, Sum.elim_inr, Pi.zero_apply, add_zero]
      exact this
    · by_cases hj : j = i
      · subst hj
        simp only [y', Function.update_self]
        exact ⟨t * Fi, li, xi, hli, hxi, by simp [Fi], rfl⟩
      · simp only [y', Function.update_of_ne hj]
        obtain ⟨y0, l0, x0, hl0, hx0, hy0, hz⟩ := hYs j
        exact ⟨y0, l0, x0, hl0, hx0, by rw [Function.update_of_ne hj]; exact hy0, hz⟩
    · have hsum' : ∑ j, y' t j = ∑ j, ys j + hultenGoods ((t - a i) • δ) := by
        rw [← hnet t, ← hys]
        simp only [y']
        rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _
          (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
        abel
      rw [hsum']
      simp only [x', Finset.univ_unique, Finset.sum_singleton] at hsum ⊢
      rw [show (default : Unit) = () from rfl] at hsum
      rw [← sub_sub, ← hsum]
      abel
  -- the lower bound `W(t)`
  let W : ℝ → ℝ := fun t => U (c + (t - a i) • δ)
  have hWle : ∀ t, W t ≤ Vf t := fun t => by
    refine (hV t).1 ⟨x' t, y' t, hfeas t, ?_⟩
    simp only [W, hultenUtil, x']
    congr 1
  -- the First Welfare Theorem: the equilibrium utility is the planner's value
  have hPO := theorem_15_3 hLNS hCE
  have hVa : Vf (a i) = U c := by
    have hupd : Function.update a i (a i) = a := Function.update_eq_self i a
    have hgreat : IsGreatest {r | ∃ x' y', Feasible (hultenCons e)
        (hultenTech F (Function.update a i (a i))) x' y' ∧ r = hultenUtil U () (x' ())} (U c) := by
      rw [hupd]
      refine ⟨⟨xc, ys, hCE.1, rfl⟩, ?_⟩
      rintro r ⟨x'', y'', hF, rfl⟩
      by_contra hlt0
      have hlt := not_le.mp hlt0
      exact hPO.2 ⟨x'', y'', hF, fun u => by cases u; exact hlt.le, (), hlt⟩
    exact (hV (a i)).unique hgreat.isLUB
  have hWa : W (a i) = U c := by simp [W]
  -- `W` is differentiable with derivative `pᵢFᵢ`
  have hWd : HasDerivAt W (φ (hultenGoods δ)) (a i) := by
    have hl : HasDerivAt (fun t : ℝ => c + (t - a i) • δ) δ (a i) := by
      simpa using ((hasDerivAt_id (a i)).sub_const (a i)).smul_const δ |>.const_add c
    have hU2 : HasFDerivAt U (φ.comp hultenGoods) (c + (a i - a i) • δ) := by
      rw [sub_self, zero_smul, add_zero]; exact hU
    exact hU2.comp_hasDerivAt (a i) hl
  -- Fermat: `V − W` has a minimum at `aᵢ`
  have hmin : IsLocalMin (fun t => Vf t - W t) (a i) :=
    Filter.Eventually.of_forall fun t => by
      simp only
      rw [hVa, hWa, sub_self]; linarith [hWle t]
  have hD : D = φ (hultenGoods δ) := by
    have := hmin.hasDerivAt_eq_zero (hVd.sub hWd)
    linarith
  have hδ : δ = Fi • Pi.single i 1 := by
    funext g; simp [δ, Pi.single_apply]
  have hEuler := eq_22_A_6 hU hhom
  simp only [ContinuousLinearMap.comp_apply] at hEuler
  refine ⟨hVa, hEuler.symm, ?_, ?_⟩
  · rw [hD, hδ, map_smul, map_smul, smul_eq_mul]
    field_simp
  · rw [hD, hVa, ← hEuler, hδ, map_smul, map_smul, smul_eq_mul]
    field_simp

/-! ### The two-sector example -/

/-- AKMM, (22.32), p. 684: **the two-sector example**. With `Y = a₁(a₂K)^{1−γ}L^γ`, the
elasticities of `Y` with respect to `a₁` and `a₂` are `1` and `1 − γ`
(`dY/Y = da₁/a₁ + (1−γ)da₂/a₂`). -/
theorem eq_22_32 {γ K L a1 a2 : ℝ} (hK : 0 < K) (ha2 : 0 < a2) :
    HasDerivAt (fun t => t * (a2 * K) ^ (1 - γ) * L ^ γ) ((a2 * K) ^ (1 - γ) * L ^ γ) a1 ∧
      HasDerivAt (fun t => a1 * (t * K) ^ (1 - γ) * L ^ γ)
        ((1 - γ) * (a1 * (a2 * K) ^ (1 - γ) * L ^ γ) / a2) a2 := by
  constructor
  · simpa using ((hasDerivAt_id a1).mul_const ((a2 * K) ^ (1 - γ))).mul_const (L ^ γ)
  · have h1 : HasDerivAt (fun t => t * K) K a2 := by simpa using (hasDerivAt_id a2).mul_const K
    have h2 := h1.rpow_const (p := 1 - γ) (Or.inl (mul_pos ha2 hK).ne')
    have h3 := (h2.const_mul a1).mul_const (L ^ γ)
    convert h3 using 1
    rw [Real.rpow_sub_one (mul_pos ha2 hK).ne']
    field_simp

/-- AKMM, p. 684: **prices and Domar weights in the example**. With the intermediate price
`p = (1−γ)a₁x^{−γ}L^γ`, `x = a₂K`: sector 2's value added (= its sales) is `pa₂K = (1−γ)Y`,
sector 1's value added is `Y − px = γY`, so the Domar weights are `Y/Y = 1` and `1 − γ`, the
coefficients of (22.32), while the value-added share of sector 1 is `γ`. -/
theorem hulten_example_prices {γ K L a1 a2 : ℝ} (hK : 0 < K) (ha2 : 0 < a2) :
    (1 - γ) * a1 * (a2 * K) ^ (-γ) * L ^ γ * (a2 * K) =
        (1 - γ) * (a1 * (a2 * K) ^ (1 - γ) * L ^ γ) ∧
      a1 * (a2 * K) ^ (1 - γ) * L ^ γ - (1 - γ) * a1 * (a2 * K) ^ (-γ) * L ^ γ * (a2 * K) =
        γ * (a1 * (a2 * K) ^ (1 - γ) * L ^ γ) := by
  have hx : 0 < a2 * K := mul_pos ha2 hK
  have e : (a2 * K) ^ (-γ) * (a2 * K) = (a2 * K) ^ (1 - γ) := by
    rw [← Real.rpow_add_one hx.ne']; ring_nf
  constructor
  · calc (1 - γ) * a1 * (a2 * K) ^ (-γ) * L ^ γ * (a2 * K)
        = (1 - γ) * a1 * ((a2 * K) ^ (-γ) * (a2 * K)) * L ^ γ := by ring
      _ = _ := by rw [e]; ring
  · calc a1 * (a2 * K) ^ (1 - γ) * L ^ γ - (1 - γ) * a1 * (a2 * K) ^ (-γ) * L ^ γ * (a2 * K)
        = a1 * (a2 * K) ^ (1 - γ) * L ^ γ - (1 - γ) * a1 * ((a2 * K) ^ (-γ) * (a2 * K)) *
            L ^ γ := by ring
      _ = _ := by rw [e]; ring

end AKMM.HeterogeneousFirms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hulten's theorem: a concrete economy (AKMM App. 22.A.5)

A one-good, one-factor economy satisfies every hypothesis of `hulten`: technology `y ≤ Aℓ`,
labour endowment `1`, utility `U(c) = c`, price of the good `1` and wage `A`. The planner's value
is `V(t) = t`, and Hulten's theorem gives `dV/dA = 1` and the Domar weight `1`
(`hulten_one_sector`). This shows that the hypotheses of `hulten` are consistent.
-/

open Filter Topology StokeyLucasPrescott.ParetoOptimaEquilibria

namespace AKMM.HeterogeneousFirms

/-- The price functional of the one-sector economy: good at `1`, labour at `A`. -/
noncomputable def hultenOnePrice (A : ℝ) : StrongDual ℝ (Unit ⊕ Unit → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => z (Sum.inl ()) + A * z (Sum.inr ())
      map_add' := fun z z' => by simp only [Pi.add_apply]; ring
      map_smul' := fun r z => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

theorem hulten_one_price_apply (A : ℝ) (z : Unit ⊕ Unit → ℝ) :
    hultenOnePrice A z = z (Sum.inl ()) + A * z (Sum.inr ()) := rfl

/-- AKMM, App. 22.A.5: **a concrete instance of Hulten's theorem**. In the economy with
`y ≤ Aℓ`, `ℓ̄ = 1`, `U(c) = c` and `A > 0`, the competitive equilibrium (`c = A`, `p = 1`,
`w = A`) satisfies all hypotheses of `hulten`, the planner's value is `V(t) = t`, and
Hulten's theorem gives `dV/dA = pY/A = 1` and the Domar weight `pY/Σpc = 1`. -/
theorem hulten_one_sector {A : ℝ} (hA : 0 < A) :
    (fun t : ℝ => t) A = (fun c : Unit → ℝ => c ()) (fun _ => A) ∧
      (1 : ℝ) = hultenOnePrice A (hultenGoods (Pi.single () 1)) * (A * 1) / A ∧
      (1 : ℝ) * A / A = hultenOnePrice A (hultenGoods (Pi.single () 1)) * (A * 1) /
        hultenOnePrice A (hultenGoods fun _ => A) := by
  set F : Unit → (Unit → ℝ) → (Unit → ℝ) → ℝ := fun _ l _ => l ()
  set a : Unit → ℝ := fun _ => A
  set e : Unit → ℝ := fun _ => 1
  set U : (Unit → ℝ) → ℝ := fun c => c ()
  set φ := hultenOnePrice A
  set z0 : Unit ⊕ Unit → ℝ := Sum.elim (fun _ => A) (fun _ => -1)
  set xc : Unit → (Unit ⊕ Unit → ℝ) := fun _ => z0
  set ys : Unit → (Unit ⊕ Unit → ℝ) := fun _ => hultenNet () (a () * F () (fun _ => 1) 0)
    (fun _ => 1) 0
  have hnet : ∀ (y : ℝ) (l x : Unit → ℝ), hultenNet () y l x =
      Sum.elim (fun _ => y - x ()) (fun _ => -l ()) := fun y l x => by
    funext s; cases s <;> simp [hultenNet]
  have hfeas0 : Feasible (hultenCons e) (hultenTech F a) xc ys := by
    refine ⟨fun _ v => by simp [xc, z0, e], fun j => ⟨a () * F () (fun _ => 1) 0, fun _ => 1, 0,
      fun _ => zero_le_one, le_rfl, le_rfl, rfl⟩, ?_⟩
    funext s
    cases s <;> simp [xc, ys, z0, hnet, a, F]
  have hCE : CompetitiveEq (hultenCons e) (hultenUtil U) (hultenTech F a) xc ys φ := by
    refine ⟨hfeas0, fun _ z hz hle => ?_, fun j w hw => ?_⟩
    · have hz' := hz ()
      simp only [φ, hulten_one_price_apply, hz', xc, z0, Sum.elim_inl, Sum.elim_inr, e] at hle
      simp only [hultenUtil, U, xc, z0, Sum.elim_inl]
      linarith
    · obtain ⟨y, l, x, hl, hx, hy, rfl⟩ := hw
      simp only [φ, hulten_one_price_apply, ys, hnet, Sum.elim_inl, Sum.elim_inr, a, F]
      have hx0 : (0 : ℝ) ≤ x () := hx ()
      have : y ≤ A * l () := hy
      simp only [Pi.zero_apply]
      linarith
  have hLNS : LocalNonsatiation (hultenCons e) (hultenUtil U) := by
    intro _ z hz
    refine ⟨fun n => z + (1 / ((n : ℝ) + 1)) • hultenGoods (fun _ => (1 : ℝ)), fun n => ?_,
      ?_, fun n => ?_⟩
    · intro v
      simp only [Pi.add_apply, Pi.smul_apply, hulten_goods_apply, Sum.elim_inr, Pi.zero_apply,
        smul_zero, add_zero]
      exact hz v
    · have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := (h.smul_const (hultenGoods (fun _ => (1 : ℝ)))).const_add z
      simpa using this
    · simp only [hultenUtil, U, Pi.add_apply, Pi.smul_apply, hulten_goods_apply, Sum.elim_inl,
        smul_eq_mul, mul_one]
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hU : HasFDerivAt U (φ.comp hultenGoods) (fun g => xc () (Sum.inl g)) := by
    have : U = ⇑(φ.comp hultenGoods) := by
      funext c
      simp [U, φ, hulten_one_price_apply, hulten_goods_apply]
    rw [this]
    exact (φ.comp hultenGoods).hasFDerivAt
  have hhom : ∀ s : ℝ, 0 < s → U (s • fun g => xc () (Sum.inl g)) =
      s * U (fun g => xc () (Sum.inl g)) := fun s _ => by simp [U]
  have hV : ∀ t, IsLUB {r | ∃ x' y', Feasible (hultenCons e)
      (hultenTech F (Function.update a () t)) x' y' ∧ r = hultenUtil U () (x' ())} t := by
    intro t
    have hupd : Function.update a () t = fun _ => t := by
      funext u; cases u; simp
    rw [hupd]
    refine IsGreatest.isLUB ⟨⟨fun _ => Sum.elim (fun _ => t) (fun _ => -1),
      fun _ => hultenNet () (t * 1) (fun _ => 1) 0, ⟨fun _ v => by simp [e],
        fun j => ⟨t * 1, fun _ => 1, 0, fun _ => zero_le_one, le_rfl, by simp [F], rfl⟩, ?_⟩,
      by simp [hultenUtil, U]⟩, ?_⟩
    · funext s; cases s <;> simp [hnet]
    · rintro r ⟨x', y', ⟨hX, hYs, hsum⟩, rfl⟩
      obtain ⟨y, l, x, hl, hx, hy, hz⟩ := hYs ()
      have hs := congrFun hsum
      simp only [Finset.univ_unique, Finset.sum_singleton, Pi.sub_apply, Pi.zero_apply] at hs
      have h1 := hs (Sum.inr ())
      have h2 := hs (Sum.inl ())
      rw [show (default : Unit) = () from rfl, hz, hnet] at h1 h2
      simp only [Sum.elim_inr, Sum.elim_inl] at h1 h2
      have hxv := hX () ()
      simp only [e] at hxv
      have hl1 : l () = 1 := by linarith
      have hyt : y ≤ t := by
        have h' : y ≤ t * l () := hy
        rwa [hl1, mul_one] at h'
      have := hx ()
      simp only [hultenUtil, U]
      simp only [Pi.zero_apply] at this
      nlinarith
  have hVd : HasDerivAt (fun t : ℝ => t) 1 (a ()) := hasDerivAt_id' _
  have hY : φ (hultenGoods fun g => xc () (Sum.inl g)) ≠ 0 := by
    simp [φ, hulten_one_price_apply, hulten_goods_apply, xc, z0, hA.ne']
  have h := hulten hCE hLNS (i := ()) (li := fun _ => 1) (xi := 0)
    (fun _ => zero_le_one) le_rfl rfl hU hhom hV hVd hA.ne' hY
  simp only [a, F, xc, z0, Sum.elim_inl] at h
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

end AKMM.HeterogeneousFirms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Klette–Kortum in discrete time (AKMM §22.8)

AKMM, §22.8, pp. 686–692. A unit mass of products `j` is a probability space `(Ω, P)`; the book's
law of large numbers is the identification of cross-section averages with `∫ · ∂P`.

* **The intratemporal problem (22.35)–(22.36)**: equal expenditure shares `c = E/p` maximise
  `∫ log(qc)` subject to `∫ pc ≤ E` (`eq_22_36`); `PC = E` and the normalisation (22.37)
  (`kk_price_index`, `eq_22_37`).
* **(22.38)**: the balanced-growth Euler equation `1/(1+r) = β/(1+γ)` (`eq_22_38`).
* **Limit pricing (22.39)–(22.40)**: consumers buy the leader iff `p ≤ λw` (from the
  quality-ladder condition (13.A.26) of AKMM Chapter 13, `AKMM.Growth.eq_13_A_26`, at `φ = 0`)
  (`kk_limit_price_iff`); with unit-elastic demand profit rises with the price, so `p = λw` is
  optimal (`eq_22_39`); profit `(1 − 1/λ)C` (`eq_22_40`); `w₀ = 1` (`kk_wage_normalisation`).
* **The Bellman equation (22.41)–(22.43)**: the four scenarios have probabilities summing to one
  and expected future lines `1 + η − μ` (`eq_22_41`); detrending gives (22.42) (`eq_22_42`); for
  convex `R` the first-order condition `R'(η) = βv` gives the optimum (`eq_22_43`).
* **Equilibrium (22.44)–(22.46)**: with entry using `c_e` units of labour per entrant (corrected
  from the printed `ν`), the equilibrium `(C₀, μ)` given `η` is unique, in closed form
  (`kk_equilibrium`).
* **Growth**: with `J_t = J₀ + Σ_{s<t} Bernoulli(μ)`, the wage grows by `λ^μ`:
  `log w_{t+1} − log w_t = μ log λ` exactly (`kk_growth`).
* **Gibrat's law**: a firm with `n` lines expects `n(1 + η − μ)` lines next period, so all firms
  grow at `η − μ = −ν` (`kk_gibrat`); with new-product creation `ξ`, `ξ − ν` (`kk_gibrat_xi`).
-/

open MeasureTheory

namespace AKMM.HeterogeneousFirms

variable {Ω : Type*} [MeasurableSpace Ω]

/-- AKMM, (22.35)–(22.36), p. 687: **equal expenditure shares**. With log preferences over a unit
mass of goods, prices `p > 0`, qualities `q > 0` and spending `E > 0`, any positive consumption
plan `c` with `∫ pc ≤ E` gives `∫ log(qc) ≤ ∫ log(qE/p)`: the plan `c = E/p` is optimal. -/
theorem eq_22_36 {P : Measure Ω} [IsProbabilityMeasure P] {p q c : Ω → ℝ} {E : ℝ} (hE : 0 < E)
    (hp : ∀ j, 0 < p j) (hq : ∀ j, 0 < q j) (hc : ∀ j, 0 < c j)
    (hpc : Integrable (fun j => p j * c j) P)
    (hlc : Integrable (fun j => Real.log (q j * c j)) P)
    (hlo : Integrable (fun j => Real.log (q j * (E / p j))) P)
    (hbud : ∫ j, p j * c j ∂P ≤ E) :
    ∫ j, Real.log (q j * c j) ∂P ≤ ∫ j, Real.log (q j * (E / p j)) ∂P := by
  have hpt : ∀ j, Real.log (q j * c j) ≤ Real.log (q j * (E / p j)) + (p j * c j / E - 1) :=
    fun j => by
      have hpj := hp j; have hqj := hq j; have hcj := hc j
      have h := Real.log_le_sub_one_of_pos (show 0 < p j * c j / E by positivity)
      have e : Real.log (q j * c j) = Real.log (q j * (E / p j)) + Real.log (p j * c j / E) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1; field_simp
      linarith
  have h2 : Integrable (fun j => p j * c j / E - 1) P :=
    (hpc.div_const E).sub (integrable_const 1)
  have h : ∫ j, Real.log (q j * c j) ∂P ≤
      ∫ j, (Real.log (q j * (E / p j)) + (p j * c j / E - 1)) ∂P :=
    integral_mono hlc (hlo.add h2) hpt
  rw [integral_add hlo h2,
    integral_sub (hpc.div_const E) (integrable_const 1), integral_div] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  have : (∫ j, p j * c j ∂P) / E - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hE]; exact hbud
  linarith

/-- AKMM, p. 687: at `c = E/p`, consumption is `C = E·exp(∫(log q − log p))`, so with the price
index `P = exp(∫(log p − log q))`, `PC = E`. -/
theorem kk_price_index {P : Measure Ω} {p q : Ω → ℝ} {E : ℝ} (hE : 0 < E) (hp : ∀ j, 0 < p j)
    (hq : ∀ j, 0 < q j) (hlq : Integrable (fun j => Real.log (q j)) P)
    (hlp : Integrable (fun j => Real.log (p j)) P) [IsProbabilityMeasure P] :
    Real.exp (∫ j, Real.log (q j * (E / p j)) ∂P) =
        E * Real.exp (∫ j, (Real.log (q j) - Real.log (p j)) ∂P) ∧
      Real.exp (∫ j, (Real.log (p j) - Real.log (q j)) ∂P) *
        (E * Real.exp (∫ j, (Real.log (q j) - Real.log (p j)) ∂P)) = E := by
  have e : ∀ j, Real.log (q j * (E / p j)) = Real.log E + (Real.log (q j) - Real.log (p j)) :=
    fun j => by
      rw [Real.log_mul (hq j).ne' (div_pos hE (hp j)).ne', Real.log_div hE.ne' (hp j).ne']; ring
  have hqp : Integrable (fun j => Real.log (q j) - Real.log (p j)) P := hlq.sub hlp
  have hpq : Integrable (fun j => Real.log (p j) - Real.log (q j)) P := hlp.sub hlq
  constructor
  · rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_add (integrable_const _)
      hqp]
    simp only [integral_const, probReal_univ, one_smul]
    rw [Real.exp_add, Real.exp_log hE]
  · rw [mul_left_comm, ← Real.exp_add, ← integral_add hpq hqp]
    simp

/-- AKMM, (22.37), p. 687: the normalisation `P = 1` holds iff `∫ log p = ∫ log q`. -/
theorem eq_22_37 {P : Measure Ω} {p q : Ω → ℝ} (hlq : Integrable (fun j => Real.log (q j)) P)
    (hlp : Integrable (fun j => Real.log (p j)) P) :
    Real.exp (∫ j, (Real.log (p j) - Real.log (q j)) ∂P) = 1 ↔
      ∫ j, Real.log (p j) ∂P = ∫ j, Real.log (q j) ∂P := by
  rw [Real.exp_eq_one_iff, integral_sub hlp hlq, sub_eq_zero]

/-- AKMM, (22.38), p. 688: **the balanced-growth Euler equation**. If `1/C_t = β(1+r)/C_{t+1}`
and `C_{t+1} = (1+γ)C_t` with `C_t > 0`, then `1/(1+r) = β/(1+γ)`. -/
theorem eq_22_38 {β r γ Ct : ℝ} (hC : 0 < Ct) (hγ : 0 < 1 + γ) (hr : 0 < 1 + r)
    (h : 1 / Ct = β * (1 + r) * (1 / ((1 + γ) * Ct))) : 1 / (1 + r) = β / (1 + γ) := by
  field_simp at h ⊢
  linarith

/-- AKMM, (22.39), p. 688: **limit pricing**. A leader of quality `λq'` priced at `p` beats the
follower of quality `q'` priced at marginal cost `w` (quality-adjusted prices
`p/(λq') ≤ w/q'`) iff `p ≤ λw`. This is the quality-ladder condition (13.A.26) of Chapter 13 at
`φ = 0` (marginal cost `ψq' = w`). -/
theorem kk_limit_price_iff {lam w q' p : ℝ} (hlam : 0 < lam) (hw : 0 < w) (hq' : 0 < q') :
    p / (lam * q') ≤ w / q' ↔ p ≤ lam * w := by
  have h := AKMM.Growth.eq_13_A_26 (φ := 0) (ψ := w / q') (by norm_num) (div_pos hw hq')
    hlam hq' (p := p)
  simp only [sub_zero, div_one, Real.rpow_one, Real.rpow_zero] at h
  rw [show w / q' * q' / q' = w / q' by field_simp] at h
  rw [h, show w / q' * (lam * q') = lam * w by field_simp, div_le_one (by positivity)]

/-- AKMM, (22.39)–(22.40), p. 688: **the optimal price is the limit price**. With unit-elastic
demand `c = C/p`, the leader's profit `(p − w)C/p` is increasing in `p`, so among the prices that
keep the follower out (`p ≤ λw`) it is maximised at `p = λw`, where it equals `(1 − 1/λ)C`. -/
theorem eq_22_39 {lam w C p : ℝ} (hlam : 1 < lam) (hw : 0 < w) (hC : 0 < C) (hp : 0 < p)
    (hpl : p ≤ lam * w) :
    (p - w) * (C / p) ≤ (lam * w - w) * (C / (lam * w)) := by
  have hlw : 0 < lam * w := by nlinarith
  have e1 : (p - w) * (C / p) = C - w * C / p := by field_simp
  have e2 : (lam * w - w) * (C / (lam * w)) = C - w * C / (lam * w) := by field_simp
  rw [e1, e2]
  have : w * C / (lam * w) ≤ w * C / p := div_le_div_of_nonneg_left (by positivity) hp hpl
  linarith

/-- AKMM, (22.40), p. 688: the profit at the limit price is `π = (1 − 1/λ)C`. -/
theorem eq_22_40 {lam w C : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    (lam * w - w) * (C / (lam * w)) = (1 - 1 / lam) * C := by
  field_simp

/-- AKMM, p. 689: from (22.37) and (22.39), `log(λw₀) = ∫ log q₀`; with `q₀ = λ`, `w₀ = 1`. -/
theorem kk_wage_normalisation {lam w0 : ℝ} (hlam : 0 < lam) (hw : 0 < w0)
    (h : Real.log (lam * w0) = Real.log lam) : w0 = 1 := by
  rw [Real.log_mul hlam.ne' hw.ne'] at h
  have : Real.log w0 = 0 := by linarith
  rcases Real.log_eq_zero.mp this with h0 | h1 | hm
  · linarith
  · exact h1
  · linarith

/-- AKMM, (22.41), p. 689: **the four scenarios**. Innovating with probability `η` and losing the
line with probability `μ`, independently: the probabilities sum to one and the expected number
of lines next period is `2η(1−μ) + 0·μ(1−η) + 1·μη + 1·(1−μ)(1−η) = 1 + η − μ`. -/
theorem eq_22_41 (η μ : ℝ) :
    η * (1 - μ) + μ * (1 - η) + μ * η + (1 - μ) * (1 - η) = 1 ∧
      2 * (η * (1 - μ)) + 0 * (μ * (1 - η)) + 1 * (μ * η) + 1 * ((1 - μ) * (1 - η)) =
        1 + η - μ := by
  constructor <;> ring

/-- AKMM, (22.42), p. 689: **detrending**. If `V_t = (1+γ)^t v`, `π_t = (1 − 1/λ)C₀(1+γ)^t`,
`w_t = (1+γ)^t` and `1/(1+r) = β/(1+γ)`, then the Bellman equation (22.41) at a given `η`,
`V_t = π_t − w_tR(η) + (1+η−μ)V_{t+1}/(1+r)`, holds iff
`v = (1 − 1/λ)C₀ − R(η) + β(1+η−μ)v`. -/
theorem eq_22_42 {γ r β lam C0 R η μ v : ℝ} (hγ : 0 < 1 + γ) (hr : 1 / (1 + r) = β / (1 + γ))
    (t : ℕ) :
    (1 + γ) ^ t * v = (1 - 1 / lam) * C0 * (1 + γ) ^ t - (1 + γ) ^ t * R +
        1 / (1 + r) * (1 + η - μ) * ((1 + γ) ^ (t + 1) * v) ↔
      v = (1 - 1 / lam) * C0 - R + β * (1 + η - μ) * v := by
  rw [hr]
  have hg : 0 < (1 + γ) ^ t := pow_pos hγ t
  constructor
  · intro h
    have : (1 + γ) ^ t * v = (1 + γ) ^ t * ((1 - 1 / lam) * C0 - R + β * (1 + η - μ) * v) := by
      rw [h, pow_succ]; field_simp
    exact mul_left_cancel₀ hg.ne' this
  · intro h
    conv_lhs => rw [h]
    rw [pow_succ]; field_simp

/-- AKMM, (22.43), p. 689: **the innovation first-order condition**. If `R` is convex and
`R'(η*) = βv`, then `η*` maximises `−R(η) + βηv`, the part of (22.42) that depends on `η`. -/
theorem eq_22_43 {R : ℝ → ℝ} (hR : ConvexOn ℝ Set.univ R) {β v ηs : ℝ}
    (hd : HasDerivAt R (β * v) ηs) (η : ℝ) : -R η + β * η * v ≤ -R ηs + β * ηs * v := by
  rcases lt_trichotomy η ηs with h | h | h
  · have := hR.slope_le_of_hasDerivAt (Set.mem_univ η) (Set.mem_univ ηs) h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    nlinarith
  · rw [h]
  · have := hR.le_slope_of_hasDerivAt (Set.mem_univ ηs) (Set.mem_univ η) h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith

/-- AKMM, (22.42)–(22.46), pp. 689–690, with the entry labour corrected to `c_eν`: **the
equilibrium given `η`**. With free entry `v = c_e` (22.44), `μ = η + ν` (22.45), the Bellman
equation (22.42) and the labour market `C₀/λ + R(η) + c_e(μ − η) = L`, the pair `(C₀, μ)` is
unique: `μ = ((λ−1)(L − R + c_eη) − R − c_e(1 − β(1+η)))/(c_e(β + λ − 1))` and
`C₀ = λ(L − R − c_e(μ − η))`. -/
theorem kk_equilibrium {lam β ce L R η C0 μ : ℝ} (hlam : 1 < lam) (hβ : 0 < β) (hce : 0 < ce) :
    (ce = (1 - 1 / lam) * C0 - R + β * (1 + η - μ) * ce ∧ C0 / lam + R + ce * (μ - η) = L) ↔
      (μ = ((lam - 1) * (L - R + ce * η) - R - ce * (1 - β * (1 + η))) /
          (ce * (β + lam - 1)) ∧
        C0 = lam * (L - R - ce * (μ - η))) := by
  have hl0 : lam ≠ 0 := by linarith
  have hd : ce * (β + lam - 1) ≠ 0 := by
    have : 0 < β + lam - 1 := by linarith
    positivity
  have key : ∀ X : ℝ, (1 - 1 / lam) * (lam * X) = (lam - 1) * X := fun X => by field_simp
  constructor
  · rintro ⟨h1, h2⟩
    have hC : C0 = lam * (L - R - ce * (μ - η)) := by
      rw [← h2]; field_simp; ring
    refine ⟨?_, hC⟩
    rw [eq_div_iff hd]
    rw [hC, key] at h1
    linear_combination h1
  · rintro ⟨h1, h2⟩
    rw [eq_div_iff hd] at h1
    refine ⟨?_, by rw [h2, mul_div_cancel_left₀ _ hl0]; ring⟩
    rw [h2, key]
    linear_combination h1

/-- AKMM, (22.46), p. 690: the printed entry labour `ν` differs from the `c_eν` units entrants
hire (p. 689) whenever `c_e ≠ 1` and `ν ≠ 0`. -/
theorem kk_labour_printed_false {C0 lam R ν ce : ℝ} (hce : ce ≠ 1) (hν : ν ≠ 0) :
    C0 / lam + R + ν ≠ C0 / lam + R + ce * ν := by
  intro h
  have : (ce - 1) * ν = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hce (by linarith)
  · exact hν h1

/-- AKMM, p. 690: **the growth rate**. Let `log q_t(j) = J_t(j) log λ` with `J_t = J₀ + Σ_{s<t}Xₛ`,
each `Xₛ` a Bernoulli trial with mean `μ` (`∫Xₛ = μ`), and `log w_t = ∫ log q_t − log λ`
(from (22.37) and (22.39)). Then `log w_{t+1} − log w_t = μ log λ`: the gross growth rate is
exactly `λ^μ` (the book's `γ ≈ μ log λ`). -/
theorem kk_growth {P : Measure Ω} [IsProbabilityMeasure P] {lam μ : ℝ} {J0 : Ω → ℝ}
    {X : ℕ → Ω → ℝ} (hJ0 : Integrable J0 P) (hX : ∀ s, Integrable (X s) P)
    (hμ : ∀ s, ∫ j, X s j ∂P = μ) {w : ℕ → ℝ}
    (hw : ∀ t, Real.log (w t) =
      ∫ j, (J0 j + ∑ s ∈ Finset.range t, X s j) * Real.log lam ∂P - Real.log lam) (t : ℕ) :
    Real.log (w (t + 1)) - Real.log (w t) = μ * Real.log lam := by
  have hI : ∀ t, Integrable (fun j => J0 j + ∑ s ∈ Finset.range t, X s j) P := fun t =>
    hJ0.add (integrable_finsetSum _ fun s _ => hX s)
  have hE : ∀ t, ∫ j, (J0 j + ∑ s ∈ Finset.range t, X s j) * Real.log lam ∂P =
      (∫ j, J0 j ∂P + t * μ) * Real.log lam := fun t => by
    rw [integral_mul_const, integral_add hJ0 (integrable_finsetSum _ fun s _ => hX s),
      integral_finsetSum _ fun s _ => hX s]
    simp [hμ]
  rw [hw, hw, hE, hE]
  push_cast
  ring

/-- AKMM, p. 691: **Gibrat's law**. A firm with `n` lines; each line `l` is lost with
probability `μ` (`∫Lₗ = μ`) and generates a new line with probability `η` (`∫Gₗ = η`). The
expected number of lines next period is `n(1 + η − μ)`, and with `μ = η + ν` the expected growth
rate `η − μ = −ν` is the same for all sizes. -/
theorem kk_gibrat {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {η μ ν : ℝ}
    {Lo Ga : ℕ → Ω → ℝ} (hL : ∀ l, Integrable (Lo l) P) (hG : ∀ l, Integrable (Ga l) P)
    (hLμ : ∀ l, ∫ j, Lo l j ∂P = μ) (hGη : ∀ l, ∫ j, Ga l j ∂P = η) (hμ : μ = η + ν) :
    ∫ j, ((n : ℝ) - ∑ l ∈ Finset.range n, Lo l j + ∑ l ∈ Finset.range n, Ga l j) ∂P =
        n * (1 + η - μ) ∧ η - μ = -ν := by
  refine ⟨?_, by rw [hμ]; ring⟩
  have hLs : Integrable (fun j => ∑ l ∈ Finset.range n, Lo l j) P :=
    integrable_finsetSum _ fun l _ => hL l
  have hGs : Integrable (fun j => ∑ l ∈ Finset.range n, Ga l j) P :=
    integrable_finsetSum _ fun l _ => hG l
  have h1 : Integrable (fun j => (n : ℝ) - ∑ l ∈ Finset.range n, Lo l j) P :=
    (integrable_const _).sub hLs
  rw [integral_add h1 hGs, integral_sub (integrable_const _) hLs,
    integral_finsetSum _ fun l _ => hL l, integral_finsetSum _ fun l _ => hG l]
  simp [hLμ, hGη]
  ring

/-- AKMM, p. 692: with new-product creation `ξ` (`μ = η + ν − ξ`), the expected growth rate
`η − μ` is `ξ − ν`, positive when `ξ > ν`. -/
theorem kk_gibrat_xi {η μ ν ξ : ℝ} (hμ : μ = η + ν - ξ) : η - μ = ξ - ν := by
  rw [hμ]; ring

end AKMM.HeterogeneousFirms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The firm-size distribution (AKMM §22.8, p. 692, and App. 22.A.6)

* **A Pareto stationary density** (p. 692): `h(n) = Fn^{−(ζ+1)}` satisfies
  `(1+g)h((1+g)n) = (1−δ)h(n)` for all `n > 0` iff `ζ = −log(1−δ)/log(1+g)` (`pareto_stationary`);
  then `ζ > 0` (`pareto_zeta_pos`), and the tail is thicker when `δ` is smaller or `g` larger
  (`pareto_zeta_mono`).
* **The transition of firm sizes** (App. 22.A.6, p. 896): from `j` lines a firm loses
  `Bin(j, μ)` lines and gains `Bin(j, η)`; `fsdT μ η j k` is the probability of ending with `k`
  lines (`fsd_T_sum` : the probabilities sum to one). The three groups of the book's equation
  for `M_{k,t+1}` are `fsdT (k−h) k`, `fsdT k k` and `fsdT (k+h) k`: we prove the book's sums for
  the second and third (`fsd_stay`, `fsd_from_above`) and the first with the **corrected inner
  bound** `i = 0, …, k − 2h` (`fsd_from_below`), and that sources with `2h > k` cannot reach `k`
  (`fsd_below_zero`), which justifies the outer bound `⌊k/2⌋`. The printed inner bound
  `⌊k/2 − h⌋` omits terms: for `k = 4`, `h = 1` it misses `P_μ(3,2)P_η(3,3) > 0`
  (`fsd_printed_bound_false`).
-/

namespace AKMM.HeterogeneousFirms

/-! ### The Pareto tail -/

/-- AKMM, p. 692: **a Pareto stationary density**. For `F > 0`, `g > 0`, `0 < δ < 1`, the density
`h(n) = Fn^{−(ζ+1)}` satisfies `(1+g)h((1+g)n) = (1−δ)h(n)` for every `n > 0` iff
`ζ = −log(1−δ)/log(1+g)`. -/
theorem pareto_stationary {F g δ ζ : ℝ} (hF : 0 < F) (hg : 0 < g) (hδ1 : δ < 1) :
    (∀ n : ℝ, 0 < n → (1 + g) * (F * ((1 + g) * n) ^ (-(ζ + 1))) =
      (1 - δ) * (F * n ^ (-(ζ + 1)))) ↔ ζ = -Real.log (1 - δ) / Real.log (1 + g) := by
  have h1g : 0 < 1 + g := by linarith
  have hlg : 0 < Real.log (1 + g) := Real.log_pos (by linarith)
  have h1d : 0 < 1 - δ := by linarith
  have key : ∀ n : ℝ, 0 < n → (1 + g) * (F * ((1 + g) * n) ^ (-(ζ + 1))) =
      (1 + g) ^ (-ζ) * (F * n ^ (-(ζ + 1))) := fun n hn => by
    rw [Real.mul_rpow h1g.le hn.le]
    have : (1 + g) * (1 + g) ^ (-(ζ + 1)) = (1 + g) ^ (-ζ) := by
      rw [show (1 + g) * (1 + g) ^ (-(ζ + 1)) = (1 + g) ^ (1 + -(ζ + 1)) by
        rw [Real.rpow_add h1g, Real.rpow_one]]
      ring_nf
    calc (1 + g) * (F * ((1 + g) ^ (-(ζ + 1)) * n ^ (-(ζ + 1))))
        = ((1 + g) * (1 + g) ^ (-(ζ + 1))) * (F * n ^ (-(ζ + 1))) := by ring
      _ = _ := by rw [this]
  have hlog : (1 + g) ^ (-ζ) = 1 - δ ↔ Real.log (1 + g) * (-ζ) = Real.log (1 - δ) := by
    rw [Real.rpow_def_of_pos h1g]
    constructor
    · intro h; rw [← h, Real.log_exp]
    · intro h; rw [h, Real.exp_log h1d]
  have hiff : (1 + g) ^ (-ζ) = 1 - δ ↔ ζ = -Real.log (1 - δ) / Real.log (1 + g) := by
    rw [hlog, eq_div_iff hlg.ne']
    constructor <;> intro h <;> linarith
  rw [← hiff]
  constructor
  · intro h
    have h1 := h 1 one_pos
    rw [key 1 one_pos] at h1
    have hpos : 0 < F * (1 : ℝ) ^ (-(ζ + 1)) := by rw [Real.one_rpow]; linarith
    exact mul_right_cancel₀ hpos.ne' h1
  · intro h n hn
    rw [key n hn, h]

/-- AKMM, p. 692: `ζ = −log(1−δ)/log(1+g) > 0`. -/
theorem pareto_zeta_pos {g δ : ℝ} (hg : 0 < g) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < -Real.log (1 - δ) / Real.log (1 + g) := by
  have hlg : 0 < Real.log (1 + g) := Real.log_pos (by linarith)
  have hld : Real.log (1 - δ) < 0 := Real.log_neg (by linarith) (by linarith)
  exact div_pos (by linarith) hlg

/-- AKMM, p. 692: **the tail is thick when `δ` is small or `g` large**: `ζ` is increasing in `δ`
and decreasing in `g`. -/
theorem pareto_zeta_mono {g g' δ δ' : ℝ} (hg : 0 < g) (hgg : g ≤ g') (hδ : 0 < δ) (hδδ : δ ≤ δ')
    (hδ1 : δ' < 1) :
    -Real.log (1 - δ) / Real.log (1 + g') ≤ -Real.log (1 - δ) / Real.log (1 + g) ∧
      -Real.log (1 - δ) / Real.log (1 + g) ≤ -Real.log (1 - δ') / Real.log (1 + g) := by
  have hlg : 0 < Real.log (1 + g) := Real.log_pos (by linarith)
  have hlg' : Real.log (1 + g) ≤ Real.log (1 + g') := Real.log_le_log (by linarith) (by linarith)
  have hld : 0 ≤ -Real.log (1 - δ) := by
    have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - δ) (by linarith); linarith
  have hld' : -Real.log (1 - δ) ≤ -Real.log (1 - δ') := by
    have := Real.log_le_log (by linarith : (0 : ℝ) < 1 - δ') (by linarith : 1 - δ' ≤ 1 - δ)
    linarith
  exact ⟨div_le_div_of_nonneg_left hld hlg hlg', div_le_div_of_nonneg_right hld' hlg.le⟩

/-! ### Transitions of product lines -/

/-- AKMM, p. 896: the binomial probability `P_p(a, b) = C(a,b)p^b(1−p)^{a−b}`. -/
noncomputable def binomP (p : ℝ) (a b : ℕ) : ℝ := (a.choose b : ℝ) * p ^ b * (1 - p) ^ (a - b)

theorem binomP_eq_zero {p : ℝ} {a b : ℕ} (h : a < b) : binomP p a b = 0 := by
  simp [binomP, Nat.choose_eq_zero_of_lt h]

theorem binomP_sum (p : ℝ) (a : ℕ) : ∑ b ∈ Finset.range (a + 1), binomP p a b = 1 := by
  have h := add_pow p (1 - p) a
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  rw [h]
  exact Finset.sum_congr rfl fun b _ => by unfold binomP; ring

/-- AKMM, App. 22.A.6: the probability that a firm with `j` lines has `k` lines next period: it
loses `ℓ ∼ Bin(j, μ)` and gains `g ∼ Bin(j, η)` lines, independently, and `k = j − ℓ + g`. -/
noncomputable def fsdT (μ η : ℝ) (j k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (j + 1), ∑ g ∈ Finset.range (j + 1),
    if j - l + g = k then binomP μ j l * binomP η j g else 0

/-- The transition probabilities from `j` lines sum to one. -/
theorem fsd_T_sum (μ η : ℝ) (j : ℕ) :
    ∑ k ∈ Finset.range (2 * j + 1), fsdT μ η j k = 1 := by
  unfold fsdT
  rw [Finset.sum_comm]
  have : ∀ l ∈ Finset.range (j + 1), ∑ k ∈ Finset.range (2 * j + 1), ∑ g ∈ Finset.range (j + 1),
      (if j - l + g = k then binomP μ j l * binomP η j g else 0) =
      binomP μ j l * ∑ g ∈ Finset.range (j + 1), binomP η j g := fun l hl => by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range] at hl hg ⊢
    rw [ite_eq_left (by omega)]
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, binomP_sum, binomP_sum, one_mul]

/-- The single-sum form: `fsdT j k = Σ_ℓ [j ≤ k + ℓ] P_μ(j, ℓ)P_η(j, k + ℓ − j)`. -/
theorem fsd_T_eq (μ η : ℝ) (j k : ℕ) :
    fsdT μ η j k = ∑ l ∈ Finset.range (j + 1),
      if j ≤ k + l then binomP μ j l * binomP η j (k + l - j) else 0 := by
  unfold fsdT
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [Finset.mem_range] at hl
  by_cases hjk : j ≤ k + l
  · rw [ite_eq_left hjk]
    by_cases hg : k + l - j < j + 1
    · rw [Finset.sum_eq_single (k + l - j)]
      · rw [ite_eq_left (by omega)]
      · intro g _ hne; rw [ite_eq_right (by omega)]
      · intro h; exact absurd (Finset.mem_range.mpr hg) h
    · rw [binomP_eq_zero (by omega : j < k + l - j), mul_zero]
      exact Finset.sum_eq_zero fun g hg' => by
        simp only [Finset.mem_range] at hg'; rw [ite_eq_right (by omega)]
  · rw [ite_eq_right hjk]
    exact Finset.sum_eq_zero fun g _ => by rw [ite_eq_right (by omega)]

/-- AKMM, App. 22.A.6, p. 896: **firms that keep `k` lines**:
`fsdT k k = Σ_{i=0}^k P_μ(k,i)P_η(k,i)` (the book's middle term). -/
theorem fsd_stay (μ η : ℝ) (k : ℕ) :
    fsdT μ η k k = ∑ i ∈ Finset.range (k + 1), binomP μ k i * binomP η k i := by
  rw [fsd_T_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ite_eq_left (by omega), show k + i - k = i by omega]

/-- AKMM, App. 22.A.6, p. 896: **firms shrinking from `k + h` to `k` lines**:
`fsdT (k+h) k = Σ_{i=h}^{k+h} P_μ(k+h, i)P_η(k+h, i−h)` (the book's last term). -/
theorem fsd_from_above (μ η : ℝ) (k h : ℕ) :
    fsdT μ η (k + h) k = ∑ i ∈ Finset.Ico h (k + h + 1),
      binomP μ (k + h) i * binomP η (k + h) (i - h) := by
  rw [fsd_T_eq, Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le h) (by omega : h ≤ k + h + 1)]
  rw [Finset.sum_eq_zero (fun i hi => by
    simp only [Finset.mem_Ico] at hi; rw [ite_eq_right (by omega)]), zero_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_Ico] at hi
  rw [ite_eq_left (by omega), show k + i - (k + h) = i - h by omega]

/-- AKMM, App. 22.A.6, p. 896, **corrected**: **firms growing from `k − h` to `k` lines**, for
`1 ≤ h` and `2h ≤ k`: `fsdT (k−h) k = Σ_{i=0}^{k−2h} P_μ(k−h, i)P_η(k−h, i+h)` — lose `i`, gain
`i + h ≤ k − h`; the book prints the bound `⌊k/2 − h⌋`. -/
theorem fsd_from_below (μ η : ℝ) {k h : ℕ} (h2 : 2 * h ≤ k) :
    fsdT μ η (k - h) k = ∑ i ∈ Finset.range (k - 2 * h + 1),
      binomP μ (k - h) i * binomP η (k - h) (i + h) := by
  rw [fsd_T_eq]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega :
    k - 2 * h + 1 ≤ k - h + 1))]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [ite_eq_left (by omega), show k + i - (k - h) = i + h by omega]
  · intro i hi hi'
    simp only [Finset.mem_range] at hi hi'
    rw [ite_eq_left (by omega), show k + i - (k - h) = i + h by omega,
      binomP_eq_zero (by omega : k - h < i + h), mul_zero]

/-- AKMM, App. 22.A.6, p. 896: a firm with `k − h` lines cannot reach `k` lines when `2h > k`
(it gains at most `k − h < h` lines), which justifies the outer bound `⌊k/2⌋`. -/
theorem fsd_below_zero (μ η : ℝ) {k h : ℕ} (hk : k < 2 * h) (hhk : h ≤ k) :
    fsdT μ η (k - h) k = 0 := by
  rw [fsd_T_eq]
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [ite_eq_left (by omega), binomP_eq_zero (by omega : k - h < k + i - (k - h)), mul_zero]

/-- AKMM, App. 22.A.6, p. 896: **the printed inner bound is wrong**. For `k = 4`, `h = 1` the
printed sum runs over `i = 0, …, ⌊4/2 − 1⌋ = 1`, but the transition probability from 3 to 4
lines also contains `i = 2` (lose 2, gain 3), `P_μ(3,2)P_η(3,3) = 3μ²(1−μ)η³ > 0`. -/
theorem fsd_printed_bound_false {μ η : ℝ} (hμ : 0 < μ) (hμ1 : μ < 1) (hη : 0 < η) :
    ∑ i ∈ Finset.range (4 / 2 - 1 + 1), binomP μ 3 i * binomP η 3 (i + 1) <
      fsdT μ η (4 - 1) 4 := by
  rw [fsd_from_below μ η (by norm_num : 2 * 1 ≤ 4)]
  norm_num [Finset.sum_range_succ, binomP]
  have : 0 < 1 - μ := by linarith
  positivity

end AKMM.HeterogeneousFirms

set_option linter.style.longLine false
#print axioms AKMM.HeterogeneousFirms.twostage_cost
#print axioms AKMM.HeterogeneousFirms.twostage_profit_le
#print axioms AKMM.HeterogeneousFirms.twostage_profit_eq
#print axioms AKMM.HeterogeneousFirms.simpleScale
#print axioms AKMM.HeterogeneousFirms.simple_scale_pos
#print axioms AKMM.HeterogeneousFirms.simple_scale_rpow
#print axioms AKMM.HeterogeneousFirms.eq_22_2
#print axioms AKMM.HeterogeneousFirms.eq_22_1
#print axioms AKMM.HeterogeneousFirms.simple_output_eq
#print axioms AKMM.HeterogeneousFirms.aggTFP
#print axioms AKMM.HeterogeneousFirms.simple_scale_eq
#print axioms AKMM.HeterogeneousFirms.simple_M_eq
#print axioms AKMM.HeterogeneousFirms.eq_22_3
#print axioms AKMM.HeterogeneousFirms.simple_A_eq
#print axioms AKMM.HeterogeneousFirms.eq_22_7_M
#print axioms AKMM.HeterogeneousFirms.eq_22_7
#print axioms AKMM.HeterogeneousFirms.simple_planner
#print axioms AKMM.HeterogeneousFirms.cobbDouglas_unit_cost
#print axioms AKMM.HeterogeneousFirms.simple_footnote_2
#print axioms AKMM.HeterogeneousFirms.lognormal_mean
#print axioms AKMM.HeterogeneousFirms.eq_22_8
#print axioms AKMM.HeterogeneousFirms.lognormal_A_strictMono
#print axioms AKMM.HeterogeneousFirms.aggTFP_ge_mean
#print axioms AKMM.HeterogeneousFirms.bivariate_mgf
#print axioms AKMM.HeterogeneousFirms.wedgeTFP
#print axioms AKMM.HeterogeneousFirms.wedgeTFP_one
#print axioms AKMM.HeterogeneousFirms.wedge_exponent
#print axioms AKMM.HeterogeneousFirms.eq_22_11
#print axioms AKMM.HeterogeneousFirms.wedge_A_indep
#print axioms AKMM.HeterogeneousFirms.wedge_A_strictAnti
#print axioms AKMM.HeterogeneousFirms.jobCreation
#print axioms AKMM.HeterogeneousFirms.jobDestruction
#print axioms AKMM.HeterogeneousFirms.jobflows_net
#print axioms AKMM.HeterogeneousFirms.jobflows_steady
#print axioms AKMM.HeterogeneousFirms.fhk_decomposition
#print axioms AKMM.HeterogeneousFirms.fhk_within_only
#print axioms AKMM.HeterogeneousFirms.simple_planner_A
#print axioms AKMM.HeterogeneousFirms.wedge_scale_eq
#print axioms AKMM.HeterogeneousFirms.eq_22_10
#print axioms AKMM.HeterogeneousFirms.wedge_A_le
#print axioms AKMM.HeterogeneousFirms.HRFirm
#print axioms AKMM.HeterogeneousFirms.HRFirm.mk
#print axioms AKMM.HeterogeneousFirms.HRFirm.β
#print axioms AKMM.HeterogeneousFirms.HRFirm.τ
#print axioms AKMM.HeterogeneousFirms.HRFirm.cf
#print axioms AKMM.HeterogeneousFirms.HRFirm.γ
#print axioms AKMM.HeterogeneousFirms.HRFirm.av
#print axioms AKMM.HeterogeneousFirms.HRFirm.lv
#print axioms AKMM.HeterogeneousFirms.HRFirm.Q
#print axioms AKMM.HeterogeneousFirms.hrLag
#print axioms AKMM.HeterogeneousFirms.hrProfit
#print axioms AKMM.HeterogeneousFirms.hrT
#print axioms AKMM.HeterogeneousFirms.hr_max_sub_le
#print axioms AKMM.HeterogeneousFirms.hr_T_sub_le
#print axioms AKMM.HeterogeneousFirms.hr_T_dist_le
#print axioms AKMM.HeterogeneousFirms.hr_bellman_existsUnique
#print axioms AKMM.HeterogeneousFirms.hrValue
#print axioms AKMM.HeterogeneousFirms.hr_value_spec
#print axioms AKMM.HeterogeneousFirms.hr_fixed_compare
#print axioms AKMM.HeterogeneousFirms.hr_value_wage_gap
#print axioms AKMM.HeterogeneousFirms.hr_value_lipschitz
#print axioms AKMM.HeterogeneousFirms.hrEntry
#print axioms AKMM.HeterogeneousFirms.hr_entry_strictAnti
#print axioms AKMM.HeterogeneousFirms.hr_entry_continuous
#print axioms AKMM.HeterogeneousFirms.hr_free_entry_unique
#print axioms AKMM.HeterogeneousFirms.hr_free_entry_exists
#print axioms AKMM.HeterogeneousFirms.hr_entry_barrier_wage
#print axioms AKMM.HeterogeneousFirms.HRStationary
#print axioms AKMM.HeterogeneousFirms.hr_stationary_zero
#print axioms AKMM.HeterogeneousFirms.hr_stationary_existsUnique
#print axioms AKMM.HeterogeneousFirms.hr_stationary_nonneg
#print axioms AKMM.HeterogeneousFirms.hr_stationary_linear
#print axioms AKMM.HeterogeneousFirms.hr_aggregate_linear
#print axioms AKMM.HeterogeneousFirms.eq_22_15
#print axioms AKMM.HeterogeneousFirms.hr_entry_mass
#print axioms AKMM.HeterogeneousFirms.hr_footnote_11
#print axioms AKMM.HeterogeneousFirms.eq_22_17
#print axioms AKMM.HeterogeneousFirms.eq_22_18
#print axioms AKMM.HeterogeneousFirms.mc_revenue_eq
#print axioms AKMM.HeterogeneousFirms.eq_22_19
#print axioms AKMM.HeterogeneousFirms.eq_22_20
#print axioms AKMM.HeterogeneousFirms.eq_22_22
#print axioms AKMM.HeterogeneousFirms.mc_output_eq
#print axioms AKMM.HeterogeneousFirms.mcTFP
#print axioms AKMM.HeterogeneousFirms.mc_aggregate
#print axioms AKMM.HeterogeneousFirms.mc_scale_form
#print axioms AKMM.HeterogeneousFirms.mc_aggregate_eq
#print axioms AKMM.HeterogeneousFirms.sectorOutput
#print axioms AKMM.HeterogeneousFirms.sectorOutput_rpow
#print axioms AKMM.HeterogeneousFirms.eq_22_25
#print axioms AKMM.HeterogeneousFirms.eq_22_24
#print axioms AKMM.HeterogeneousFirms.eq_22_29
#print axioms AKMM.HeterogeneousFirms.cournotElas
#print axioms AKMM.HeterogeneousFirms.bertrandElas
#print axioms AKMM.HeterogeneousFirms.eq_22_28
#print axioms AKMM.HeterogeneousFirms.eq_22_27
#print axioms AKMM.HeterogeneousFirms.cournot_endpoints
#print axioms AKMM.HeterogeneousFirms.cournot_strictAntiOn
#print axioms AKMM.HeterogeneousFirms.cournot_mem_Icc
#print axioms AKMM.HeterogeneousFirms.cournot_symmetric
#print axioms AKMM.HeterogeneousFirms.cournot_symmetric_one
#print axioms AKMM.HeterogeneousFirms.cournot_symmetric_mono
#print axioms AKMM.HeterogeneousFirms.cournot_symmetric_tendsto
#print axioms AKMM.HeterogeneousFirms.markup_strictAnti
#print axioms AKMM.HeterogeneousFirms.bertrand_demand_form
#print axioms AKMM.HeterogeneousFirms.bertrand_demand_deriv
#print axioms AKMM.HeterogeneousFirms.bertrand_ratio
#print axioms AKMM.HeterogeneousFirms.bertrand_ratio_printed_false
#print axioms AKMM.HeterogeneousFirms.bertrand_markup
#print axioms AKMM.HeterogeneousFirms.eq_22_A_4
#print axioms AKMM.HeterogeneousFirms.cournot_le_bertrand
#print axioms AKMM.HeterogeneousFirms.markup_cournot_ge
#print axioms AKMM.HeterogeneousFirms.granular_growth
#print axioms AKMM.HeterogeneousFirms.eq_22_30
#print axioms AKMM.HeterogeneousFirms.granular_equal_sizes
#print axioms AKMM.HeterogeneousFirms.granular_million
#print axioms AKMM.HeterogeneousFirms.granular_herfindahl_ge
#print axioms AKMM.HeterogeneousFirms.hultenNet
#print axioms AKMM.HeterogeneousFirms.hultenTech
#print axioms AKMM.HeterogeneousFirms.hultenCons
#print axioms AKMM.HeterogeneousFirms.hultenUtil
#print axioms AKMM.HeterogeneousFirms.hultenGoods
#print axioms AKMM.HeterogeneousFirms.hulten_goods_apply
#print axioms AKMM.HeterogeneousFirms.eq_22_A_6
#print axioms AKMM.HeterogeneousFirms.hulten
#print axioms AKMM.HeterogeneousFirms.eq_22_32
#print axioms AKMM.HeterogeneousFirms.hulten_example_prices
#print axioms AKMM.HeterogeneousFirms.hultenOnePrice
#print axioms AKMM.HeterogeneousFirms.hulten_one_price_apply
#print axioms AKMM.HeterogeneousFirms.hulten_one_sector
#print axioms AKMM.HeterogeneousFirms.eq_22_36
#print axioms AKMM.HeterogeneousFirms.kk_price_index
#print axioms AKMM.HeterogeneousFirms.eq_22_37
#print axioms AKMM.HeterogeneousFirms.eq_22_38
#print axioms AKMM.HeterogeneousFirms.kk_limit_price_iff
#print axioms AKMM.HeterogeneousFirms.eq_22_39
#print axioms AKMM.HeterogeneousFirms.eq_22_40
#print axioms AKMM.HeterogeneousFirms.kk_wage_normalisation
#print axioms AKMM.HeterogeneousFirms.eq_22_41
#print axioms AKMM.HeterogeneousFirms.eq_22_42
#print axioms AKMM.HeterogeneousFirms.eq_22_43
#print axioms AKMM.HeterogeneousFirms.kk_equilibrium
#print axioms AKMM.HeterogeneousFirms.kk_labour_printed_false
#print axioms AKMM.HeterogeneousFirms.kk_growth
#print axioms AKMM.HeterogeneousFirms.kk_gibrat
#print axioms AKMM.HeterogeneousFirms.kk_gibrat_xi
#print axioms AKMM.HeterogeneousFirms.pareto_stationary
#print axioms AKMM.HeterogeneousFirms.pareto_zeta_pos
#print axioms AKMM.HeterogeneousFirms.pareto_zeta_mono
#print axioms AKMM.HeterogeneousFirms.binomP
#print axioms AKMM.HeterogeneousFirms.binomP_eq_zero
#print axioms AKMM.HeterogeneousFirms.binomP_sum
#print axioms AKMM.HeterogeneousFirms.fsdT
#print axioms AKMM.HeterogeneousFirms.fsd_T_sum
#print axioms AKMM.HeterogeneousFirms.fsd_T_eq
#print axioms AKMM.HeterogeneousFirms.fsd_stay
#print axioms AKMM.HeterogeneousFirms.fsd_from_above
#print axioms AKMM.HeterogeneousFirms.fsd_from_below
#print axioms AKMM.HeterogeneousFirms.fsd_below_zero
#print axioms AKMM.HeterogeneousFirms.fsd_printed_bound_false
