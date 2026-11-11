/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMQuantitativeMethods.StaticModel
import AKMMQuantitativeMethods.VARLP
import NeoclassicalGrowth.RBUtility
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# The dynamic fiscal model, its steady state and its calibration

AKMM, §8.6, (8.10)–(8.18), pp. 229–231; §8.6.2, p. 231; §8.8, pp. 234–237; Appendix 8.A.1,
p. 842.

* (8.11) from the accumulation equation (`eq_8_11`) and from the budgets with `T = G`
  (`fm_budget_resource`).
* The firm's first-order conditions (8.16)–(8.17) are the marginal products of `Akᵅℓ^{1−α}`
  (`eq_8_16_8_17`), the labour condition (8.15) is the first-order condition of the household's
  labour choice (`eq_8_15`), and (8.18) is the planner's condition for `G`, with the unique
  solution `G = γη/(1+γη)·x` (`eq_8_18`).
* The AR(1) processes (8.12)–(8.13) have unit mean (`eq_8_12_mean`).
* **The equilibrium** (8.10)–(8.18) (`fm_IsEquilibrium`), with the deterministic steady state as
  an equilibrium when the shocks are zero (`fm_steady_isEquilibrium`).
* **Appendix 8.A.1**: the steady state exists and is unique, with `r̄ = 1/β − 1 + δ`,
  `ȳ/k̄ = r̄/α`, `k̄/ℓ̄ = (ȳ/k̄)^{1/(α−1)}`, `ȳ/ℓ̄ = (r̄/α)^{α/(α−1)}`, `w̄ = (1−α)ȳ/ℓ̄`,
  `c̄ = w̄ℓ̄^{−ψ}`, `Ḡ = γc̄` and the scalar equation for `ℓ̄` (`appendix_8A_1`,
  `appendix_8A_1_ratios`, `fm_steady_exists`). The printed rule `Ḡ = (η̄c̄γ)^{−γ₁}` is a misprint
  (`appendix_8A_1_printed_G`).
* **§8.6.2**: with capital and investment fixed, the multiplier is between zero and one
  (`fm_fixed_investment_multiplier`).
* **Calibration** (§8.8): `β = (1 + αȳ/k̄ − δ)⁻¹` (`fm_beta_calibration`), the Frisch elasticity
  `1/ψ` (`fm_frisch`, from Miao's `rb_u39_frisch`), `dℓ/dc = −(1/ψ)ℓ/c` (`fm_dl_dc`), the
  lottery formula and its inversion for `ψ` (`fm_lottery`), `γ = Ḡ/c̄` (`fm_gamma_calibration`),
  and the scale invariance of the multiplier in a linear solution (`fm_multiplier_scale`).

Departure: the household's Euler equation (8.14) is stated by the book from Chapter 7 and enters
the equilibrium definition as stated; it is not re-derived.
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Filter Topology

/-! ### The first-order conditions -/

/-- **(8.16)–(8.17)** (AKMM, p. 230): for `y = Akᵅℓ^{1−α}` with `k, ℓ > 0`, the marginal
products are `∂y/∂k = αy/k` and `∂y/∂ℓ = (1−α)y/ℓ`, and they exhaust output,
`(αy/k)k + ((1−α)y/ℓ)ℓ = y`. -/
theorem eq_8_16_8_17 {A α k ℓ : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) :
    HasDerivAt (fun x => A * x ^ α * ℓ ^ (1 - α)) (α * (A * k ^ α * ℓ ^ (1 - α)) / k) k ∧
      HasDerivAt (fun x => A * k ^ α * x ^ (1 - α))
        ((1 - α) * (A * k ^ α * ℓ ^ (1 - α)) / ℓ) ℓ ∧
      α * (A * k ^ α * ℓ ^ (1 - α)) / k * k +
        (1 - α) * (A * k ^ α * ℓ ^ (1 - α)) / ℓ * ℓ = A * k ^ α * ℓ ^ (1 - α) := by
  refine ⟨?_, ?_, by field_simp; ring⟩
  · have := ((Real.hasDerivAt_rpow_const (Or.inl hk.ne') (p := α)).const_mul A).mul_const
      (ℓ ^ (1 - α))
    convert this using 1
    rw [Real.rpow_sub_one hk.ne']
    field_simp
  · have := (Real.hasDerivAt_rpow_const (Or.inl hℓ.ne') (p := 1 - α)).const_mul (A * k ^ α)
    convert this using 1
    rw [Real.rpow_sub_one hℓ.ne']
    field_simp

/-- **(8.11)** (AKMM, p. 229): `k_{t+1} = (1 − δ)k_t + I_t` and `y_t = c_t + I_t + G_t` give
`y_t = c_t + k_{t+1} − (1 − δ)k_t + G_t`. -/
theorem eq_8_11 {y c I G k k' δ : ℝ} (hk : k' = (1 - δ) * k + I) (hy : y = c + I + G) :
    y = c + k' - (1 - δ) * k + G := by
  rw [hy, hk]; ring

/-- AKMM, pp. 229–230: the household budget `c + k' = (1 + r − δ)k + wℓ − T` (the book prints
`K_t` for `k_t`), the government budget `T = G` and zero profits `y = rk + wℓ` give the resource
constraint (8.11). -/
theorem fm_budget_resource {y c k k' r w ℓ T G δ : ℝ}
    (hb : c + k' = (1 + r - δ) * k + w * ℓ - T) (hT : T = G) (hπ : y = r * k + w * ℓ) :
    y = c + k' - (1 - δ) * k + G := by
  rw [hπ]; rw [hT] at hb; linarith

/-- **(8.15)** (AKMM, p. 230): the household's labour choice. With other income `x` and wage
`w > 0`, `ℓ ↦ log(x + wℓ) − ℓ^{1+ψ}/(1+ψ)` has derivative `w/c − ℓ^ψ` at `ℓ > 0`
(`c = x + wℓ > 0`), which vanishes iff `w/c = ℓ^ψ`. -/
theorem eq_8_15 {ψ x w ℓ : ℝ} (hψ : 0 < ψ) (hℓ : 0 < ℓ) (hc : 0 < x + w * ℓ) :
    HasDerivAt (fun l => Real.log (x + w * l) - l ^ (1 + ψ) / (1 + ψ))
      (w / (x + w * ℓ) - ℓ ^ ψ) ℓ ∧
      (w / (x + w * ℓ) - ℓ ^ ψ = 0 ↔ w / (x + w * ℓ) = ℓ ^ ψ) := by
  refine ⟨?_, sub_eq_zero⟩
  have h1 : HasDerivAt (fun l => x + w * l) w ℓ := by
    simpa using ((hasDerivAt_id ℓ).const_mul w).const_add x
  have h2 := h1.log hc.ne'
  have h3 := (Real.hasDerivAt_rpow_const (Or.inl hℓ.ne') (p := 1 + ψ)).div_const (1 + ψ)
  convert h2.sub h3 using 1
  rw [show 1 + ψ - 1 = ψ by ring]
  field_simp

/-- **(8.18)** (AKMM, p. 230): the planner's choice of `G` given resources `x = c + G`.
`G ↦ log(x − G) + γη log G` has derivative `−1/c + γη/G`, which vanishes iff `γη/G = 1/c`, and
on `0 < G < x` this holds exactly at `G = γη/(1+γη)·x`. -/
theorem eq_8_18 {γ η x G : ℝ} (hγη : 0 < γ * η) (hG : 0 < G) (hGx : G < x) :
    HasDerivAt (fun g => Real.log (x - g) + γ * η * Real.log g)
      (-(1 / (x - G)) + γ * η / G) G ∧
      (γ * η / G = 1 / (x - G) ↔ G = γ * η / (1 + γ * η) * x) := by
  have hc : 0 < x - G := by linarith
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun g => x - g) (-1) G := by
      simpa using (hasDerivAt_id G).const_sub x
    have h2 := (h1.log hc.ne').add ((Real.hasDerivAt_log hG.ne').const_mul (γ * η))
    convert h2 using 1
    field_simp
  · have hX : 0 < 1 + γ * η := by linarith
    constructor
    · intro h
      field_simp at h
      field_simp
      linarith
    · intro h
      have hγ0 : γ ≠ 0 := left_ne_zero_of_mul hγη.ne'
      have hη0 : η ≠ 0 := right_ne_zero_of_mul hγη.ne'
      have hx0 : x ≠ 0 := by linarith
      rw [h]
      field_simp
      ring

/-- **(8.12)–(8.13)** (AKMM, p. 230): the AR(1) `Aₜ₊₁ = (1 − ρ) + ρAₜ + εₜ₊₁` with integrable
`A₀`, `εₜ`, `E A₀ = 1` and `E εₜ = 0` on a probability space has `E Aₜ = 1` for all `t`; and `1`
is its deterministic steady state, the unique one for `ρ ≠ 1`. -/
theorem eq_8_12_mean {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ρ : ℝ} {A ε : ℕ → Ω → ℝ}
    (hrec : ∀ t ω, A (t + 1) ω = (1 - ρ) + ρ * A t ω + ε (t + 1) ω)
    (hA : ∀ t, Integrable (A t) μ) (hε : ∀ t, Integrable (ε t) μ) (h0 : ∫ ω, A 0 ω ∂μ = 1)
    (hε0 : ∀ t, ∫ ω, ε t ω ∂μ = 0) :
    (∀ t, ∫ ω, A t ω ∂μ = 1) ∧ (1 - ρ) + ρ * 1 = (1 : ℝ) ∧
      (ρ ≠ 1 → ∀ a : ℝ, (1 - ρ) + ρ * a = a → a = 1) := by
  refine ⟨fun t => ?_, by ring, fun hρ a ha => ?_⟩
  · induction t with
    | zero => exact h0
    | succ t ih =>
      have e : ∫ ω, A (t + 1) ω ∂μ = ∫ ω, ((1 - ρ) + ρ * A t ω) + ε (t + 1) ω ∂μ := by
        simp only [hrec t]
      have hi1 : Integrable (fun ω => (1 - ρ) + ρ * A t ω) μ :=
        (integrable_const _).add ((hA t).const_mul ρ)
      rw [e, integral_add hi1 (hε _), integral_add (integrable_const (1 - ρ))
        ((hA t).const_mul ρ), integral_const_mul, ih, hε0]
      simp
  · have : (1 - ρ) * (a - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (by linarith) hρ
    · linarith

/-! ### The equilibrium and its steady state -/

/-- **The equilibrium** (AKMM, p. 230): processes `k, c, y, ℓ, G, r, w, A, η` (adapted to `ℱ`)
with the shocks `ε_A, ε_η` satisfying (8.10)–(8.18), with (8.14) as an almost-sure equality of
conditional expectations. -/
def fm_IsEquilibrium {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (α β δ ψ γ ρA ρη : ℝ) (k c y ℓ G r w A η εA εη : ℕ → Ω → ℝ) :
    Prop :=
  (∀ t ω, y t ω = A t ω * k t ω ^ α * ℓ t ω ^ (1 - α)) ∧
    (∀ t ω, y t ω = c t ω + k (t + 1) ω - (1 - δ) * k t ω + G t ω) ∧
    (∀ t ω, A (t + 1) ω = (1 - ρA) + ρA * A t ω + εA (t + 1) ω) ∧
    (∀ t ω, η (t + 1) ω = (1 - ρη) + ρη * η t ω + εη (t + 1) ω) ∧
    (∀ t, (fun ω => 1 / c t ω) =ᵐ[μ]
      μ[fun ω => β * ((1 + r (t + 1) ω - δ) * (1 / c (t + 1) ω)) | ℱ t]) ∧
    (∀ t ω, w t ω / c t ω = ℓ t ω ^ ψ) ∧
    (∀ t ω, r t ω = α * y t ω / k t ω) ∧
    (∀ t ω, w t ω = (1 - α) * y t ω / ℓ t ω) ∧
    (∀ t ω, γ * η t ω / G t ω = 1 / c t ω)

/-- **The steady state** (AKMM, Appendix 8.A.1, p. 842): `Ā = η̄ = 1` and (8.10)–(8.18) with
constant values. -/
def fm_IsSteady (α β δ ψ γ k c y ℓ G r w : ℝ) : Prop :=
  0 < k ∧ 0 < c ∧ 0 < ℓ ∧ 0 < G ∧ y = k ^ α * ℓ ^ (1 - α) ∧ y = c + δ * k + G ∧
    1 = β * (1 + r - δ) ∧ w / c = ℓ ^ ψ ∧ r = α * y / k ∧ w = (1 - α) * y / ℓ ∧
    γ / G = 1 / c

/-- AKMM, p. 842: `r̄ = 1/β − 1 + δ`. -/
noncomputable def fm_r (β δ : ℝ) : ℝ := 1 / β - 1 + δ

/-- AKMM, p. 842: `k̄/ℓ̄ = (r̄/α)^{1/(α−1)}`. -/
noncomputable def fm_kl (α β δ : ℝ) : ℝ := (fm_r β δ / α) ^ (α - 1)⁻¹

/-- AKMM, p. 842: `ℓ̄`, the root of `(ȳ/ℓ̄ − δk̄/ℓ̄)ℓ̄ = (1+γ)w̄ℓ̄^{−ψ}`. -/
noncomputable def fm_l (α β δ ψ γ : ℝ) : ℝ :=
  ((1 + γ) * ((1 - α) * fm_kl α β δ ^ α) / (fm_kl α β δ ^ α - δ * fm_kl α β δ)) ^ (1 + ψ)⁻¹

/-- The hypotheses on the parameters used for the steady state. -/
def fm_Params (α β δ ψ γ : ℝ) : Prop :=
  0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧ 0 ≤ δ ∧ 0 < ψ ∧ 0 < γ

theorem fm_r_pos {α β δ : ℝ} (hp : 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧ 0 ≤ δ) :
    α * δ < fm_r β δ := by
  obtain ⟨ha0, ha1, hb0, hb1, hd⟩ := hp
  have : 1 < 1 / β := by rw [lt_div_iff₀ hb0]; linarith
  unfold fm_r
  nlinarith

/-- `κ = k̄/ℓ̄ > 0`, `κ^{α−1} = r̄/α`, `κᵅ = κ·r̄/α`, and `κᵅ − δκ > 0`. -/
theorem fm_kl_props {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    0 < fm_kl α β δ ∧ fm_kl α β δ ^ (α - 1) = fm_r β δ / α ∧
      fm_kl α β δ ^ α = fm_kl α β δ * (fm_r β δ / α) ∧
      0 < fm_kl α β δ ^ α - δ * fm_kl α β δ := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩ := hp
  have hr := fm_r_pos ⟨ha0, ha1, hb0, hb1, hd⟩
  have hrpos : 0 < fm_r β δ / α := div_pos (by nlinarith) ha0
  have hκ : 0 < fm_kl α β δ := Real.rpow_pos_of_pos hrpos _
  have h1 : fm_kl α β δ ^ (α - 1) = fm_r β δ / α :=
    Real.rpow_inv_rpow hrpos.le (by linarith)
  have h2 : fm_kl α β δ ^ α = fm_kl α β δ * (fm_r β δ / α) := by
    rw [← h1, ← Real.rpow_one_add' hκ.le (by linarith)]
    ring_nf
  refine ⟨hκ, h1, h2, ?_⟩
  rw [h2]
  have : δ < fm_r β δ / α := by rw [lt_div_iff₀ ha0]; linarith
  nlinarith

/-- `kᵅℓ^{1−α} = (k/ℓ)ᵅℓ` for `k, ℓ > 0`. -/
theorem fm_cd_ratio {α k ℓ : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) :
    k ^ α * ℓ ^ (1 - α) = (k / ℓ) ^ α * ℓ := by
  rw [Real.div_rpow hk.le hℓ.le, Real.rpow_sub hℓ, Real.rpow_one]
  have := Real.rpow_pos_of_pos hℓ α
  field_simp

/-- **Appendix 8.A.1** (AKMM, p. 842): every steady state is given by the book's formulas:
`r̄ = 1/β − 1 + δ`, `k̄ = κℓ̄` with `κ = (r̄/α)^{1/(α−1)}`, `ȳ = κᵅℓ̄`, `w̄ = (1−α)κᵅ`,
`c̄ = w̄ℓ̄^{−ψ}`, `Ḡ = γc̄` and `ℓ̄ = ((1+γ)w̄/(κᵅ − δκ))^{1/(1+ψ)}`. -/
theorem appendix_8A_1 {α β δ ψ γ k c y ℓ G r w : ℝ} (hp : fm_Params α β δ ψ γ)
    (hs : fm_IsSteady α β δ ψ γ k c y ℓ G r w) :
    r = fm_r β δ ∧ ℓ = fm_l α β δ ψ γ ∧ k = fm_kl α β δ * ℓ ∧ y = fm_kl α β δ ^ α * ℓ ∧
      w = (1 - α) * fm_kl α β δ ^ α ∧ c = w * ℓ ^ (-ψ) ∧ G = γ * c := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩ := hp
  obtain ⟨hk, hc, hℓ, hG, hY, hR, hE, hL, hr, hw, hGc⟩ := hs
  obtain ⟨hκ, hκ1, -, hden⟩ := fm_kl_props ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩
  have hr' : r = fm_r β δ := by unfold fm_r; field_simp; linarith
  -- the capital–labour ratio
  have hx : 0 < k / ℓ := div_pos hk hℓ
  have hy : y = (k / ℓ) ^ α * ℓ := by rw [hY, fm_cd_ratio hk hℓ]
  have hyk : y / k = (k / ℓ) ^ (α - 1) := by
    rw [hy, Real.rpow_sub_one hx.ne']; field_simp
  have hyk' : y / k = fm_r β δ / α := by
    rw [← hr', hr]; field_simp
  have hkl : k / ℓ = fm_kl α β δ :=
    (sm_eq_rpow_inv_iff hx (div_pos (by nlinarith [fm_r_pos ⟨ha0, ha1, hb0, hb1, hd⟩]) ha0)
      (by linarith)).2 (by rw [← hyk, hyk'])
  have hk' : k = fm_kl α β δ * ℓ := by rw [← hkl]; field_simp
  have hy' : y = fm_kl α β δ ^ α * ℓ := by rw [hy, hkl]
  have hw' : w = (1 - α) * fm_kl α β δ ^ α := by rw [hw, hy']; field_simp
  have hc' : c = w * ℓ ^ (-ψ) := by
    rw [Real.rpow_neg hℓ.le]
    have := Real.rpow_pos_of_pos hℓ ψ
    field_simp at hL ⊢
    linarith
  have hG' : G = γ * c := by field_simp at hGc; linarith
  refine ⟨hr', ?_, hk', hy', hw', hc', hG'⟩
  -- the scalar equation for ℓ
  have hpow : ℓ ^ (1 + ψ) = (1 + γ) * ((1 - α) * fm_kl α β δ ^ α) /
      (fm_kl α β δ ^ α - δ * fm_kl α β δ) := by
    rw [eq_div_iff hden.ne', Real.rpow_add hℓ, Real.rpow_one]
    have hlψ := Real.rpow_pos_of_pos hℓ ψ
    have hR' := hR
    rw [hy', hk', hG', hc', hw', Real.rpow_neg hℓ.le] at hR'
    field_simp at hR'
    nlinarith [hR']
  exact (sm_eq_rpow_inv_iff hℓ (by
    have : 0 < (1 - α) * fm_kl α β δ ^ α := mul_pos (by linarith) (Real.rpow_pos_of_pos hκ α)
    positivity) (by linarith)).2 hpow

/-- **The steady state exists** (AKMM, Appendix 8.A.1, p. 842): the book's formulas satisfy
(8.10)–(8.18) at `Ā = η̄ = 1`. With `appendix_8A_1`, the steady state is unique. -/
theorem fm_steady_exists {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    fm_IsSteady α β δ ψ γ (fm_kl α β δ * fm_l α β δ ψ γ)
      ((1 - α) * fm_kl α β δ ^ α * fm_l α β δ ψ γ ^ (-ψ))
      (fm_kl α β δ ^ α * fm_l α β δ ψ γ) (fm_l α β δ ψ γ)
      (γ * ((1 - α) * fm_kl α β δ ^ α * fm_l α β δ ψ γ ^ (-ψ))) (fm_r β δ)
      ((1 - α) * fm_kl α β δ ^ α) := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩ := hp
  obtain ⟨hκ, -, hκα, hden⟩ := fm_kl_props ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩
  set κ := fm_kl α β δ with hκ_def
  set ℓ := fm_l α β δ ψ γ with hℓ_def
  have hpa : 0 < κ ^ α := Real.rpow_pos_of_pos hκ α
  have hwpos : 0 < (1 - α) * κ ^ α := mul_pos (by linarith) hpa
  have hbase : 0 < (1 + γ) * ((1 - α) * κ ^ α) / (κ ^ α - δ * κ) := by positivity
  have hℓ : 0 < ℓ := Real.rpow_pos_of_pos hbase _
  have hℓp : ℓ ^ (1 + ψ) = (1 + γ) * ((1 - α) * κ ^ α) / (κ ^ α - δ * κ) :=
    Real.rpow_inv_rpow hbase.le (by linarith)
  have hlψ : 0 < ℓ ^ ψ := Real.rpow_pos_of_pos hℓ ψ
  have hneg : ℓ ^ (-ψ) = (ℓ ^ ψ)⁻¹ := Real.rpow_neg hℓ.le ψ
  have hc : 0 < (1 - α) * κ ^ α * ℓ ^ (-ψ) := by rw [hneg]; positivity
  have h1a : (1 - α) ≠ 0 := by linarith
  refine ⟨mul_pos hκ hℓ, hc, hℓ, mul_pos hγ hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fm_cd_ratio (mul_pos hκ hℓ) hℓ]; field_simp
  · rw [hneg]
    rw [Real.rpow_add hℓ, Real.rpow_one] at hℓp
    field_simp
    rw [eq_div_iff hden.ne'] at hℓp
    nlinarith [hℓp]
  · unfold fm_r; field_simp; ring
  · rw [hneg]; field_simp
  · rw [hκα, fm_r]; field_simp
  · field_simp
  · field_simp

/-- **The ratios of Appendix 8.A.1** (AKMM, p. 842): at the steady state, `ȳ/k̄ = r̄/α`,
`k̄/ℓ̄ = (ȳ/k̄)^{1/(α−1)}` and `ȳ/ℓ̄ = (ȳ/k̄)(k̄/ℓ̄) = (r̄/α)^{α/(α−1)}`. -/
theorem appendix_8A_1_ratios {α β δ ψ γ k c y ℓ G r w : ℝ} (hp : fm_Params α β δ ψ γ)
    (hs : fm_IsSteady α β δ ψ γ k c y ℓ G r w) :
    y / k = r / α ∧ k / ℓ = (y / k) ^ (α - 1)⁻¹ ∧ y / ℓ = y / k * (k / ℓ) ∧
      y / ℓ = (r / α) ^ (α / (α - 1)) := by
  obtain ⟨hr, -, hk, hy, -, -, -⟩ := appendix_8A_1 hp hs
  obtain ⟨ha0, ha1, hb0, hb1, hd, -, -⟩ := hp
  obtain ⟨hk0, -, hℓ, -, -, -, -, -, hrr, -, -⟩ := hs
  have hyk : y / k = r / α := by rw [hrr]; field_simp
  refine ⟨hyk, ?_, by field_simp, ?_⟩
  · rw [hyk, hr, hk]; unfold fm_kl; field_simp
  · rw [hy, hr]
    unfold fm_kl
    rw [← Real.rpow_mul (div_pos (by nlinarith [fm_r_pos ⟨ha0, ha1, hb0, hb1, hd⟩]) ha0).le]
    field_simp

/-- **The printed government rule** (AKMM, p. 842): the book prints `Ḡ = (η̄c̄γ)^{−γ₁}`; by
(8.18) at `η̄ = 1` the rule is `Ḡ = γc̄` (as in the main text, `γ = Ḡ/c̄`, p. 236). The printed
rule agrees with it for all `c̄ > 0` only if `γ₁ = −1`. -/
theorem appendix_8A_1_printed_G {γ g1 : ℝ} (hγ : 0 < γ)
    (h : ∀ c : ℝ, 0 < c → (1 * c * γ) ^ (-g1) = γ * c) : g1 = -1 := by
  have h1 := h (Real.exp 1 / γ) (by positivity)
  rw [show 1 * (Real.exp 1 / γ) * γ = Real.exp 1 by field_simp,
    show γ * (Real.exp 1 / γ) = Real.exp 1 by field_simp] at h1
  have h2 := congrArg Real.log h1
  rw [Real.log_rpow (Real.exp_pos 1), Real.log_exp] at h2
  linarith

/-- **The steady state is an equilibrium** (AKMM, pp. 230–231, 842): with zero shocks, the
constant processes at a steady state satisfy (8.10)–(8.18). -/
theorem fm_steady_isEquilibrium {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {α β δ ψ γ ρA ρη k c y ℓ G r w : ℝ}
    (hs : fm_IsSteady α β δ ψ γ k c y ℓ G r w) :
    fm_IsEquilibrium μ ℱ α β δ ψ γ ρA ρη (fun _ _ => k) (fun _ _ => c) (fun _ _ => y)
      (fun _ _ => ℓ) (fun _ _ => G) (fun _ _ => r) (fun _ _ => w) (fun _ _ => 1)
      (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) := by
  obtain ⟨hk, hc, hℓ, hG, hY, hR, hE, hL, hr, hw, hGc⟩ := hs
  refine ⟨fun _ _ => by rw [hY, one_mul], fun _ _ => by rw [hR]; ring,
    fun _ _ => by ring, fun _ _ => by ring, fun t => ?_, fun _ _ => hL, fun _ _ => hr,
    fun _ _ => hw, fun _ _ => by rw [mul_one]; exact hGc⟩
  rw [condExp_const (ℱ.le t)]
  refine Filter.Eventually.of_forall fun _ => ?_
  change 1 / c = β * ((1 + r - δ) * (1 / c))
  rw [← mul_assoc, ← hE, one_mul]

/-! ### The multiplier with investment fixed -/

/-- **§8.6.2** (AKMM, p. 231): with `k` and investment `I` fixed (`Z = Akᵅ > 0`), the period
equilibrium `y = Zℓ^{1−α}`, `c = y − I − G`, `w/c = ℓ^ψ`, `w = (1−α)y/ℓ` is parametrised by
`ℓ`: `y(ℓ) = Zℓ^{1−α}`, `G(ℓ) = Zℓ^{1−α} − I − (1−α)Zℓ^{−α−ψ}`. At `ℓ̄ > 0`, `G` has a positive
strict derivative, so near `Ḡ = G(ℓ̄)` there is a local inverse `φ`, and output as a function of
spending, `y ∘ φ`, has derivative `y′(ℓ̄)/G′(ℓ̄) ∈ (0, 1)`: the multiplier is between zero and
one. -/
theorem fm_fixed_investment_multiplier {α ψ Z I lbar : ℝ} (ha0 : 0 ≤ α) (ha1 : α < 1)
    (hψ : 0 < ψ) (hZ : 0 < Z) (hl : 0 < lbar) :
    let yf : ℝ → ℝ := fun l => Z * l ^ (1 - α)
    let Gf : ℝ → ℝ := fun l => Z * l ^ (1 - α) - I - (1 - α) * Z * l ^ (-α - ψ)
    (∀ l, 0 < l → (1 - α) * yf l / l / (yf l - I - Gf l) = l ^ ψ) ∧
    ∃ φ : ℝ → ℝ, ∃ m : ℝ, φ (Gf lbar) = lbar ∧ (∀ᶠ g in 𝓝 (Gf lbar), Gf (φ g) = g) ∧
      HasStrictDerivAt (yf ∘ φ) m (Gf lbar) ∧ 0 < m ∧ m < 1 := by
  intro yf Gf
  have h1a : 0 < 1 - α := by linarith
  refine ⟨fun l hl0 => ?_, ?_⟩
  · simp only [yf, Gf]
    have e1 : Z * l ^ (1 - α) - I - (Z * l ^ (1 - α) - I - (1 - α) * Z * l ^ (-α - ψ)) =
        (1 - α) * Z * l ^ (-α - ψ) := by ring
    rw [e1, Real.rpow_sub hl0, Real.rpow_one, Real.rpow_sub hl0, Real.rpow_neg hl0.le]
    have := Real.rpow_pos_of_pos hl0 α
    have := Real.rpow_pos_of_pos hl0 ψ
    field_simp
  · set dy := (1 - α) * Z * lbar ^ (1 - α - 1) with hdy
    set dG := (1 - α) * Z * lbar ^ (1 - α - 1) +
      (1 - α) * Z * (α + ψ) * lbar ^ (-α - ψ - 1) with hdG
    have hyd : HasStrictDerivAt yf dy lbar := by
      have := (Real.hasStrictDerivAt_rpow_const_of_ne hl.ne' (1 - α)).const_mul Z
      exact this.congr_deriv (by rw [hdy]; ring)
    have hGd : HasStrictDerivAt Gf dG lbar := by
      have h1 := (Real.hasStrictDerivAt_rpow_const_of_ne hl.ne' (1 - α)).const_mul Z
      have h2 := (Real.hasStrictDerivAt_rpow_const_of_ne hl.ne' (-α - ψ)).const_mul
        ((1 - α) * Z)
      have h3 : HasStrictDerivAt (fun l => Z * l ^ (1 - α) - I - (1 - α) * Z * l ^ (-α - ψ))
          (Z * ((1 - α) * lbar ^ (1 - α - 1)) - (1 - α) * Z * ((-α - ψ) * lbar ^ (-α - ψ - 1)))
          lbar := (h1.sub_const I).sub h2
      exact HasStrictDerivAt.congr_deriv h3 (by rw [hdG]; ring)
    have hdy0 : 0 < dy := by rw [hdy]; have := Real.rpow_pos_of_pos hl (1 - α - 1); positivity
    have hextra : 0 < (1 - α) * Z * (α + ψ) * lbar ^ (-α - ψ - 1) := by
      have := Real.rpow_pos_of_pos hl (-α - ψ - 1)
      have : 0 < α + ψ := by linarith
      positivity
    have hdG0 : dG ≠ 0 := by rw [hdG]; linarith
    set φ := hGd.localInverse Gf dG lbar hdG0
    have hφ := hGd.to_localInverse hdG0
    have hφG : φ (Gf lbar) = lbar := (hGd.eventually_left_inverse hdG0).self_of_nhds
    refine ⟨φ, dy * dG⁻¹, hφG, hGd.eventually_right_inverse hdG0, ?_, ?_, ?_⟩
    · have hyd' : HasStrictDerivAt yf dy (φ (Gf lbar)) := by rw [hφG]; exact hyd
      exact hyd'.comp (Gf lbar) hφ
    · have : 0 < dG := by rw [hdG]; linarith
      positivity
    · have hpos : 0 < dG := by rw [hdG]; linarith
      rw [← div_eq_mul_inv, div_lt_one hpos, hdG]
      linarith

/-! ### Calibration (§8.8) -/

/-- **The discount factor** (AKMM, p. 235): from (8.14) and (8.16) in the steady state,
`1 = β(1 + r̄ − δ)` and `r̄ = αȳ/k̄` give `β = (1 + αȳ/k̄ − δ)⁻¹`. -/
theorem fm_beta_calibration {α β δ r y k : ℝ} (hE : 1 = β * (1 + r - δ))
    (hr : r = α * y / k) : β = (1 + α * y / k - δ)⁻¹ := by
  rw [← hr]
  have : 1 + r - δ ≠ 0 := fun h => by rw [h, mul_zero] at hE; exact one_ne_zero hE
  field_simp
  linarith

/-- **The Frisch elasticity is `1/ψ`** (AKMM, p. 235): holding the marginal utility of
consumption `λ = 1/c` fixed, (8.15) `λw = ℓ^ψ` holds iff `ℓ = (λw)^{1/ψ}`, and along
`w(s) = weˢ`, `log ℓ(s) = log ℓ + s/ψ`. From Miao's `rb_u39_frisch` with `χ = 1`. -/
theorem fm_frisch {ψ lam w ℓ : ℝ} (hψ : 0 < ψ) (hlam : 0 < lam) (hw : 0 < w) (hℓ : 0 < ℓ) :
    (ℓ ^ ψ = lam * w ↔ ℓ = (lam * w) ^ ψ⁻¹) ∧
      ∀ s : ℝ, Real.log ((lam * (w * Real.exp s)) ^ ψ⁻¹) =
        Real.log ((lam * w) ^ ψ⁻¹) + s / ψ := by
  obtain ⟨h1, h2⟩ := Miao.NeoclassicalGrowth.rb_u39_frisch (χ := 1) hψ one_pos hlam hw hℓ
  refine ⟨?_, fun s => ?_⟩
  · simpa using h1
  · simpa using h2 s

/-- **`dℓ/dc = −(1/ψ)ℓ/c`** (AKMM, p. 235): solving (8.15) for `ℓ(c) = (w/c)^{1/ψ}` and
differentiating with respect to `c`. -/
theorem fm_dl_dc {ψ w c : ℝ} (hψ : 0 < ψ) (hw : 0 < w) (hc : 0 < c) :
    HasDerivAt (fun x => (w / x) ^ ψ⁻¹) (-(1 / ψ) * ((w / c) ^ ψ⁻¹ / c)) c := by
  have h1 : HasDerivAt (fun x => w / x) (-(w / c ^ 2)) c := by
    have := (hasDerivAt_inv hc.ne').const_mul w
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp
  have h2 := h1.rpow_const (p := ψ⁻¹) (Or.inl (div_pos hw hc).ne')
  convert h2 using 1
  rw [Real.rpow_sub_one (div_pos hw hc).ne']
  field_simp

/-- **The lottery calibration** (AKMM, p. 235): a windfall `W` raises consumption by the annuity
value `dc = (r/(1+r))W`; with `dℓ = −(1/ψ)(ℓ/c)dc`, annual earnings change by
`Δ = 4w dℓ = −(4/ψ)(wℓ/c)(r/(1+r))W`; for `Δ ≠ 0` this gives
`ψ = −(4/Δ)(wℓ/c)(r/(1+r))W`. -/
theorem fm_lottery {ψ w ℓ c r W Δ : ℝ} (hψ : ψ ≠ 0) (hc : c ≠ 0) (hr : 1 + r ≠ 0)
    (hΔ : Δ = 4 * w * (-(1 / ψ) * (ℓ / c) * (r / (1 + r) * W))) (hΔ0 : Δ ≠ 0) :
    Δ = -(4 / ψ) * (w * ℓ / c) * (r / (1 + r)) * W ∧
      ψ = -(4 / Δ) * (w * ℓ / c) * (r / (1 + r)) * W := by
  refine ⟨by rw [hΔ]; field_simp, ?_⟩
  rw [hΔ]
  rw [hΔ] at hΔ0
  have : w * ℓ * r * W ≠ 0 := by
    intro h
    apply hΔ0
    field_simp
    linear_combination (-4) * h
  have hw0 : w ≠ 0 := by intro h; apply this; simp [h]
  have hl0 : ℓ ≠ 0 := by intro h; apply this; simp [h]
  have hr0 : r ≠ 0 := by intro h; apply this; simp [h]
  have hW0 : W ≠ 0 := by intro h; apply this; simp [h]
  field_simp

/-- **`γ = Ḡ/c̄`** (AKMM, p. 236): in the steady state (8.18) becomes `γ = Ḡ/c̄`. -/
theorem fm_gamma_calibration {γ G c : ℝ} (hG : 0 < G) (hc : 0 < c) (h : γ * 1 / G = 1 / c) :
    γ = G / c := by
  field_simp at h ⊢
  linarith

/-- AKMM, p. 236: "the linear solution scales one-for-one with the size of the shocks so the
magnitude of the fiscal shock will not affect the fiscal multiplier": responses scaled by
`s ≠ 0` have the same cumulative multiplier. -/
theorem fm_multiplier_scale {y G : ℕ → ℝ} (H : ℕ) {s : ℝ} (hs : s ≠ 0) :
    vl_cumMult (fun h => s * y h) (fun h => s * G h) H = vl_cumMult y G H := by
  unfold vl_cumMult
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_mul_left _ _ hs]

end AKMM.QuantitativeMethods
