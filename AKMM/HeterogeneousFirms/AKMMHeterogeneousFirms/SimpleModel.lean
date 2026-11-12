/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import NewKeynesian.NKFinalGoods

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
