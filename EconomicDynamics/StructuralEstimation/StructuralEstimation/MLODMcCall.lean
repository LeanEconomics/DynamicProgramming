/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.MLODBasic

/-!
# McCall's job search model, with and without job loss

Copied from `EconomicDynamics/Applications` (module `ODMcCall`), with the namespace renamed and
the names prefixed `ml_`; the link to the stopping problem of Exercise 5.1 (which needs the
MDP modules) is omitted. Used for the job search likelihood of Miao Example 12.2.1.

Miao, §8.1, p. 234, and **Exercise 8.2**, p. 288. Wage offers are drawn i.i.d. from `F` on
`[0, B]`; an unemployed worker receives `c` and draws a new offer next period; `β ∈ (0, 1)`.

**Exercise 8.2.** Each period an employed worker is fired with probability `α ∈ [0, 1]`; a fired
worker waits one period (receiving `c`) and searches again the period after. Writing `U` for the
value of a worker who is unemployed this period and searches next period, `E(w)` for the value of
working at `w` and `V(w)` for the value of holding the offer `w`, the Bellman equations are
(`ml_od_FiringBellman`)
`U = c + β ∫ V dF`, `E(w) = w + β[(1 − α)E(w) + αU]`, `V(w) = max(E(w), U)`.
(The fired worker's position is that of a worker who rejects an offer: he receives `c` now and
draws next period, so his value is `U`.)

* `ml_ex_8_2_E`: `E(w) = (w + αβU)/(1 − β + αβ)`.
* `ml_ex_8_2`: the system has exactly one solution; `U` is the unique fixed point of
  `U ↦ c + β ∫ max((w + αβU)/(1 − β + αβ), U) dF(w)`.
* `ml_ex_8_2_reservation`: the worker accepts exactly the offers `w ≥ w̄ = (1 − β)U` (the
  reservation wage); `V = E` above `w̄` and `V = U` below.
* `ml_ex_8_2_reservation_eq`: `w̄ − c = β/(1 − β + αβ) ∫_{w > w̄} (w − w̄) dF(w)`, and this equation
  has `w̄` as its only root (`ml_ex_8_2_root_unique`).
* `ml_ex_8_2_alpha`: the reservation wage decreases with the firing probability `α`.

**McCall (p. 234).** The Bellman equation `V(w) = max(c + β ∫ V dF, w/(1 − β))`
(`ml_od_McCallBellman`) is the case `α = 0` (`ml_od_mccall_iff_firing`).
`ml_od_mccall_exists_unique`: exactly one solution,
`V(w) = max(Q, w/(1 − β))` with `Q = c + β ∫ V dF`; `ml_od_mccall_reservation`: the worker accepts
iff `w ≥ w̄ = (1 − β)Q`, and `w̄ − c = β/(1 − β) ∫_{w > w̄} (w − w̄) dF`.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory

/-- The Bellman equations of **Exercise 8.2** (job search with firing probability `α`). -/
def ml_od_FiringBellman (F : Measure ℝ) (B c α β : ℝ) (V E : ℝ → ℝ) (U : ℝ) : Prop :=
  U = c + β * ∫ w, V w ∂F ∧
    ∀ w ∈ Set.Icc 0 B, E w = w + β * ((1 - α) * E w + α * U) ∧ V w = max (E w) U

/-- The scalar Bellman map for `U` in Exercise 8.2. -/
noncomputable def ml_od_firingΦ (F : Measure ℝ) (c α β U : ℝ) : ℝ :=
  c + β * ∫ w, max ((w + α * β * U) / (1 - β + α * β)) U ∂F

variable {F : Measure ℝ} [IsProbabilityMeasure F] {B c α β : ℝ}

theorem ml_od_firing_D_pos (hβ1 : β < 1) (hα0 : 0 ≤ α) (hβ0 : 0 < β) : 0 < 1 - β + α * β := by
  nlinarith

theorem ml_od_firing_integrable (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (α β U : ℝ) :
    Integrable (fun w => max ((w + α * β * U) / (1 - β + α * β)) U) F :=
  ml_od_integrable_of_continuous hF
    (((continuous_id.add continuous_const).div_const _).max continuous_const)

theorem ml_od_firingΦ_lipschitz (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (x y : ℝ) :
    |ml_od_firingΦ F c α β x - ml_od_firingΦ F c α β y| ≤ β * |x - y| := by
  have hD := ml_od_firing_D_pos hβ1 hα0 hβ0
  have hk0 : 0 ≤ α * β / (1 - β + α * β) := div_nonneg (mul_nonneg hα0 hβ0.le) hD.le
  have hk1 : α * β / (1 - β + α * β) ≤ 1 := by
    rw [div_le_one hD]; linarith
  have hL : ∀ x y w : ℝ, |max ((w + α * β * x) / (1 - β + α * β)) x -
      max ((w + α * β * y) / (1 - β + α * β)) y| ≤ |x - y| := fun x y w => by
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ le_rfl)
    have : (w + α * β * x) / (1 - β + α * β) - (w + α * β * y) / (1 - β + α * β) =
        α * β / (1 - β + α * β) * (x - y) := by field_simp; ring
    rw [this, abs_mul, abs_of_nonneg hk0]
    exact mul_le_of_le_one_left (abs_nonneg _) hk1
  have key := ml_od_abs_integral_sub_le (F := F) (ml_od_firing_integrable hF α β) hL x y
  unfold ml_od_firingΦ
  rw [show (c + β * ∫ w, max ((w + α * β * x) / (1 - β + α * β)) x ∂F) -
      (c + β * ∫ w, max ((w + α * β * y) / (1 - β + α * β)) y ∂F) =
      β * (∫ w, max ((w + α * β * x) / (1 - β + α * β)) x ∂F -
        ∫ w, max ((w + α * β * y) / (1 - β + α * β)) y ∂F) by ring,
    abs_mul, abs_of_pos hβ0]
  exact mul_le_mul_of_nonneg_left key hβ0.le

omit [IsProbabilityMeasure F] in
/-- **Exercise 8.2** (Miao, p. 288): the value of working at `w` is
`E(w) = (w + αβU)/(1 − β + αβ)`. -/
theorem ml_ex_8_2_E (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) {V E : ℝ → ℝ} {U : ℝ}
    (hB : ml_od_FiringBellman F B c α β V E U) :
    ∀ w ∈ Set.Icc 0 B, E w = (w + α * β * U) / (1 - β + α * β) := by
  intro w hw
  have hD := ml_od_firing_D_pos hβ1 hα0 hβ0
  have h := (hB.2 w hw).1
  rw [eq_div_iff hD.ne']
  linarith

omit [IsProbabilityMeasure F] in
/-- In a solution, `U` is a fixed point of the scalar map. -/
theorem ml_od_firing_fixed (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) {V E : ℝ → ℝ} {U : ℝ} (hB : ml_od_FiringBellman F B c α β V E U) :
    ml_od_firingΦ F c α β U = U := by
  have hE := ml_ex_8_2_E hβ0 hβ1 hα0 hB
  unfold ml_od_firingΦ
  conv_rhs => rw [hB.1]
  congr 2
  refine integral_congr_ae (hF.mono fun w hw => ?_)
  simp only
  rw [(hB.2 w hw).2, hE w hw]

/-- **Exercise 8.2** (Miao, p. 288): the Bellman equations have a solution, with `U` the unique
fixed point of `U ↦ c + β ∫ max((w + αβU)/(1 − β + αβ), U) dF`, `E(w) = (w + αβU)/(1 − β + αβ)`
and `V = max(E, U)`; every solution has this `U` and agrees with it on `[0, B]`. -/
theorem ml_ex_8_2 (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) :
    ∃ U, ml_od_firingΦ F c α β U = U ∧
      ml_od_FiringBellman F B c α β (fun w => max ((w + α * β * U) / (1 - β + α * β)) U)
        (fun w => (w + α * β * U) / (1 - β + α * β)) U ∧
      ∀ V' E' U', ml_od_FiringBellman F B c α β V' E' U' → U' = U ∧
        ∀ w ∈ Set.Icc 0 B, E' w = (w + α * β * U) / (1 - β + α * β) ∧
          V' w = max ((w + α * β * U) / (1 - β + α * β)) U := by
  obtain ⟨U, hU, huniq⟩ := ml_od_scalar_fixed hβ0 hβ1
    (ml_od_firingΦ_lipschitz (c := c) hF hβ0 hβ1 hα0)
  have hD := ml_od_firing_D_pos hβ1 hα0 hβ0
  refine ⟨U, hU, ⟨hU.symm, fun w _ => ⟨?_, rfl⟩⟩, fun V' E' U' hB' => ?_⟩
  · field_simp; ring
  have hU' : U' = U := huniq _ (ml_od_firing_fixed hF hβ0 hβ1 hα0 hB')
  subst hU'
  refine ⟨rfl, fun w hw => ⟨ml_ex_8_2_E hβ0 hβ1 hα0 hB' w hw, ?_⟩⟩
  rw [(hB'.2 w hw).2, ml_ex_8_2_E hβ0 hβ1 hα0 hB' w hw]

omit [IsProbabilityMeasure F] in
/-- **Exercise 8.2** (Miao, p. 288): the reservation wage property. With `w̄ = (1 − β)U`, the
worker accepts the offer `w` (`E(w) ≥ U`) iff `w ≥ w̄`; `V = E` for `w ≥ w̄` and `V = U` for
`w ≤ w̄`. -/
theorem ml_ex_8_2_reservation (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) {V E : ℝ → ℝ} {U : ℝ}
    (hB : ml_od_FiringBellman F B c α β V E U) :
    ∀ w ∈ Set.Icc 0 B, (U ≤ E w ↔ (1 - β) * U ≤ w) ∧
      ((1 - β) * U ≤ w → V w = E w) ∧ (w ≤ (1 - β) * U → V w = U) := by
  intro w hw
  have hD := ml_od_firing_D_pos hβ1 hα0 hβ0
  have hE := ml_ex_8_2_E hβ0 hβ1 hα0 hB w hw
  have hiff : ∀ {x y : ℝ}, x ≤ (y + α * β * x) / (1 - β + α * β) ↔ (1 - β) * x ≤ y :=
    fun {x y} => by rw [le_div_iff₀ hD]; constructor <;> intro h <;> nlinarith
  have hiff' : ∀ {x y : ℝ}, (y + α * β * x) / (1 - β + α * β) ≤ x ↔ y ≤ (1 - β) * x :=
    fun {x y} => by rw [div_le_iff₀ hD]; constructor <;> intro h <;> nlinarith
  refine ⟨by rw [hE]; exact hiff, fun h => ?_, fun h => ?_⟩
  · rw [(hB.2 w hw).2, max_eq_left (by rw [hE]; exact hiff.2 h)]
  · rw [(hB.2 w hw).2, max_eq_right (by rw [hE]; exact hiff'.2 h)]

/-- The function whose root is the reservation wage in Exercise 8.2,
`ψ_α(x) = x − c − β/(1 − β + αβ) ∫_{w > x} (w − x) dF`. -/
noncomputable def ml_od_firingψ (F : Measure ℝ) (c α β x : ℝ) : ℝ :=
  x - c - β / (1 - β + α * β) * ∫ w in Set.Ioi x, (w - x) ∂F

/-- **Exercise 8.2** (Miao, p. 288): the reservation wage `w̄ = (1 − β)U` solves
`w̄ − c = β/(1 − β + αβ) ∫_{w > w̄} (w − w̄) dF(w)`. -/
theorem ml_ex_8_2_reservation_eq (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) {V E : ℝ → ℝ} {U : ℝ} (hB : ml_od_FiringBellman F B c α β V E U) :
    (1 - β) * U - c = β / (1 - β + α * β) * ∫ w in Set.Ioi ((1 - β) * U), (w - (1 - β) * U) ∂F := by
  have hfix := ml_od_firing_fixed hF hβ0 hβ1 hα0 hB
  have hD := ml_od_firing_D_pos hβ1 hα0 hβ0
  unfold ml_od_firingΦ at hfix
  have hfun : (fun w => max ((w + α * β * U) / (1 - β + α * β)) U) =
      fun w => U + max (w - (1 - β) * U) 0 / (1 - β + α * β) := by
    funext w
    have : (w + α * β * U) / (1 - β + α * β) = U + (w - (1 - β) * U) / (1 - β + α * β) := by
      field_simp; ring
    rw [this]
    rcases le_total 0 (w - (1 - β) * U) with h | h
    · have : 0 ≤ (w - (1 - β) * U) / (1 - β + α * β) := div_nonneg h hD.le
      rw [max_eq_left (by linarith), max_eq_left h]
    · have : (w - (1 - β) * U) / (1 - β + α * β) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hD.le
      rw [max_eq_right (by linarith), max_eq_right h]; simp
  have hi : Integrable (fun w => max (w - (1 - β) * U) 0 / (1 - β + α * β)) F :=
    ((ml_od_integrable_sub hF _).sup (integrable_const 0)).div_const _
  rw [hfun, integral_add (integrable_const U) hi, integral_div] at hfix
  rw [ml_od_setIntegral_Ioi_eq]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hfix
  linear_combination -hfix

/-- `ψ_α` is strictly increasing. -/
theorem ml_od_firingψ_strictMono (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) : StrictMono (ml_od_firingψ F c α β) := by
  intro x y hxy
  unfold ml_od_firingψ
  rw [ml_od_setIntegral_Ioi_eq, ml_od_setIntegral_Ioi_eq]
  have hmono : ∫ z, max (z - y) 0 ∂F ≤ ∫ z, max (z - x) 0 ∂F :=
    integral_mono ((ml_od_integrable_sub hF y).sup (integrable_const 0))
      ((ml_od_integrable_sub hF x).sup (integrable_const 0))
      fun z => max_le_max (by linarith) le_rfl
  have hc : 0 ≤ β / (1 - β + α * β) := div_nonneg hβ0.le (ml_od_firing_D_pos hβ1 hα0 hβ0).le
  nlinarith [mul_le_mul_of_nonneg_left hmono hc]

/-- **Exercise 8.2** (Miao, p. 288): the reservation wage is the only root of its equation. -/
theorem ml_ex_8_2_root_unique (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) {V E : ℝ → ℝ} {U : ℝ} (hB : ml_od_FiringBellman F B c α β V E U) (x : ℝ) :
    ml_od_firingψ F c α β x = 0 ↔ x = (1 - β) * U := by
  have hroot : ml_od_firingψ F c α β ((1 - β) * U) = 0 := by
    unfold ml_od_firingψ; linarith [ml_ex_8_2_reservation_eq hF hβ0 hβ1 hα0 hB]
  exact ⟨fun hx => (ml_od_firingψ_strictMono hF hβ0 hβ1 hα0).injective (hx.trans hroot.symm),
    fun hx => hx ▸ hroot⟩

/-- **Exercise 8.2** (Miao, p. 288): the reservation wage decreases with the firing
probability: if `α₁ ≤ α₂` then `w̄(α₂) ≤ w̄(α₁)`. -/
theorem ml_ex_8_2_alpha (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) {α₁ α₂ : ℝ}
    (hα₁ : 0 ≤ α₁) (h12 : α₁ ≤ α₂) {V₁ E₁ V₂ E₂ : ℝ → ℝ} {U₁ U₂ : ℝ}
    (hB₁ : ml_od_FiringBellman F B c α₁ β V₁ E₁ U₁)
    (hB₂ : ml_od_FiringBellman F B c α₂ β V₂ E₂ U₂) :
    (1 - β) * U₂ ≤ (1 - β) * U₁ := by
  have hα₂ : 0 ≤ α₂ := hα₁.trans h12
  set x₁ := (1 - β) * U₁
  have h1 : ml_od_firingψ F c α₁ β x₁ = 0 := (ml_ex_8_2_root_unique hF hβ0 hβ1 hα₁ hB₁ x₁).2 rfl
  have hD₁ := ml_od_firing_D_pos hβ1 hα₁ hβ0
  have hcoef : β / (1 - β + α₂ * β) ≤ β / (1 - β + α₁ * β) :=
    div_le_div_of_nonneg_left hβ0.le hD₁ (by nlinarith)
  have hint : 0 ≤ ∫ w in Set.Ioi x₁, (w - x₁) ∂F := by
    rw [ml_od_setIntegral_Ioi_eq]; exact integral_nonneg fun _ => le_max_right _ _
  have h2 : 0 ≤ ml_od_firingψ F c α₂ β x₁ := by
    unfold ml_od_firingψ at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_right hcoef hint]
  have h3 : ml_od_firingψ F c α₂ β ((1 - β) * U₂) = 0 :=
    (ml_ex_8_2_root_unique hF hβ0 hβ1 hα₂ hB₂ _).2 rfl
  exact (ml_od_firingψ_strictMono hF hβ0 hβ1 hα₂).le_iff_le.1 (by rw [h3]; exact h2)

/-- The Bellman equation of McCall's job search model (Miao, p. 234) on `[0, B]`. -/
def ml_od_McCallBellman (F : Measure ℝ) (B c β : ℝ) (V : ℝ → ℝ) : Prop :=
  ∀ w ∈ Set.Icc 0 B, V w = max (c + β * ∫ w', V w' ∂F) (w / (1 - β))

omit [IsProbabilityMeasure F] in
/-- Miao, p. 234: McCall's Bellman equation is the case `α = 0` of Exercise 8.2, with
`E(w) = w/(1 − β)` and `U = c + β ∫ V dF`. -/
theorem ml_od_mccall_iff_firing (hβ1 : β < 1) (V : ℝ → ℝ) :
    ml_od_McCallBellman F B c β V ↔
      ml_od_FiringBellman F B c 0 β V (fun w => w / (1 - β)) (c + β * ∫ w, V w ∂F) := by
  have hne : 1 - β ≠ 0 := by linarith
  have hE : ∀ w : ℝ, w / (1 - β) = w + β * ((1 - 0) * (w / (1 - β)) + 0 * (c +
      β * ∫ w, V w ∂F)) := fun w => by field_simp; ring
  constructor
  · intro h
    exact ⟨rfl, fun w hw => ⟨hE w, by rw [h w hw, max_comm]⟩⟩
  · intro h w hw
    rw [(h.2 w hw).2, max_comm]

/-- Miao, p. 234: McCall's Bellman equation has exactly one solution on `[0, B]`,
`V(w) = max(Q, w/(1 − β))` with `Q` the fixed point of `Q ↦ c + β ∫ max(Q, w/(1 − β)) dF`. -/
theorem ml_od_mccall_exists_unique (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ Q, ml_od_McCallBellman F B c β (fun w => max Q (w / (1 - β))) ∧
      ∀ W, ml_od_McCallBellman F B c β W → ∀ w ∈ Set.Icc 0 B, W w = max Q (w / (1 - β)) := by
  obtain ⟨U, hU, hB, huniq⟩ := ml_ex_8_2 (c := c) hF hβ0 hβ1 le_rfl
  have hne : 1 - β ≠ 0 := by linarith
  have hsimp : ∀ w : ℝ, (w + 0 * β * U) / (1 - β + 0 * β) = w / (1 - β) := fun w => by ring_nf
  refine ⟨U, fun w hw => ?_, fun W hW w hw => ?_⟩
  · simp only [hsimp] at hB
    have hfe : (fun w => max (w / (1 - β)) U) = fun w => max U (w / (1 - β)) :=
      funext fun _ => max_comm _ _
    rw [hfe] at hB
    change max U (w / (1 - β)) = max (c + β * ∫ w', max U (w' / (1 - β)) ∂F) (w / (1 - β))
    rw [← hB.1]
  · obtain ⟨hU', hW'⟩ := huniq W _ _ ((ml_od_mccall_iff_firing hβ1 W).1 hW)
    rw [(hW' w hw).2, hsimp, max_comm]

/-- Miao, p. 234: the reservation wage. With `Q = c + β ∫ V dF` and `w̄ = (1 − β)Q`, the worker
accepts `w` (`w/(1 − β) ≥ Q`) iff `w ≥ w̄`, and `w̄ − c = β/(1 − β) ∫_{w > w̄} (w − w̄) dF`. -/
theorem ml_od_mccall_reservation (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    {V : ℝ → ℝ} (hV : ml_od_McCallBellman F B c β V) :
    let Q := c + β * ∫ w, V w ∂F
    (∀ w ∈ Set.Icc 0 B, (Q ≤ w / (1 - β) ↔ (1 - β) * Q ≤ w) ∧
      ((1 - β) * Q ≤ w → V w = w / (1 - β)) ∧ (w ≤ (1 - β) * Q → V w = Q)) ∧
      (1 - β) * Q - c = β / (1 - β) * ∫ w in Set.Ioi ((1 - β) * Q), (w - (1 - β) * Q) ∂F := by
  intro Q
  have hB := (ml_od_mccall_iff_firing hβ1 V).1 hV
  refine ⟨ml_ex_8_2_reservation hβ0 hβ1 le_rfl hB, ?_⟩
  have := ml_ex_8_2_reservation_eq hF hβ0 hβ1 le_rfl hB
  simpa using this

end Miao.StructuralEstimation
