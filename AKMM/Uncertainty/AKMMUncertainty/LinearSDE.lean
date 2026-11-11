/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.VARMoments

/-!
# Linear stochastic difference equations

AKMM, §7.1.4, (7.2)–(7.6), pp. 191–192.

`x_{t+1} = Ax_t + Bε_{t+1} + C` (7.5) with `Eₜ[ε_{t+1}] = 0` (7.2), `Eₜ[ε_{t+1}ε′_{t+1}] = I`
(7.3) (Miao's `var_ShockMDS`, which also gives (7.4)). The moments come from Miao's
`RationalExpectations` (the system (2.1) without a constant) applied to `x_t − µ`.

* If every eigenvalue of `A` is inside the unit circle, `I − A` is invertible and
  `µ = (I − A)⁻¹C` solves `µ = Aµ + C` (`sde_mean_fixed`); then `x_t − µ = A(x_{t−1} − µ) + Bε_t`
  (`sde_deviation`), and the means satisfy `E[x_{t+1}] = AE[x_t] + C` (`sde_mean_rec`).
* **(7.6)**: a covariance-stationary solution has mean `µ = (I − A)⁻¹C`, `Γ(0) = AΓ(0)A′ + BB′`
  (the Lyapunov equation, whose only solution is `Σⱼ AʲBB′A′ʲ`) and `Γ(j) = AʲΓ(0)`
  (`eq_7_6`).
* Impulse responses: with no shocks after `ε_t`, `x_{t+h} − µ = A^{h+1}(x_{t−1} − µ) + AʰBε_t`
  (`sde_no_further_shocks`), and the effect of `ε_t` on `x_{t+h}` is `F(h) = AʰBε`
  (`sde_impulse_response`).
-/

namespace AKMM.Uncertainty

open MeasureTheory Filter Topology Matrix Miao.RationalExpectations

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- AKMM, p. 192: if `A` is stable, `I − A` is invertible and `µ = (I − A)⁻¹C` solves
`µ = Aµ + C`. -/
theorem sde_mean_fixed {A : Matrix n n ℝ} (hA : IsStableMatrix (A.map Complex.ofRealHom))
    (C : n → ℝ) : IsUnit (1 - A) ∧ (1 - A)⁻¹ *ᵥ C = A *ᵥ ((1 - A)⁻¹ *ᵥ C) + C := by
  have hinj : Function.Injective (1 - A).mulVec := by
    intro v w hvw
    have h0 : (1 - A) *ᵥ (v - w) = 0 := by rw [mulVec_sub, hvw, sub_self]
    have hfix : A *ᵥ (v - w) = v - w := by
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at h0
      exact h0.symm
    have hpow : ∀ t : ℕ, (A ^ t) *ᵥ (v - w) = v - w := fun t => by
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ, ← mulVec_mulVec, hfix, ih]
    have hlim := tendsto_of_isStableMatrix A hA (v - w)
    simp only [hpow] at hlim
    exact sub_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds hlim)
  have hu : IsUnit (1 - A) := mulVec_injective_iff_isUnit.1 hinj
  refine ⟨hu, ?_⟩
  have h1 : (1 - A) *ᵥ ((1 - A)⁻¹ *ᵥ C) = C := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hu), one_mulVec]
  rw [sub_mulVec, one_mulVec] at h1
  exact sub_eq_iff_eq_add'.1 h1

omit [DecidableEq n] [DecidableEq k] in
/-- AKMM, p. 192: with `C = µ − Aµ`, (7.5) becomes `x_{t+1} − µ = A(x_t − µ) + Bε_{t+1}`. -/
theorem sde_deviation {A : Matrix n n ℝ} {B : Matrix n k ℝ} {C mu xt x1 : n → ℝ} {e : k → ℝ}
    (hmu : mu = A *ᵥ mu + C) (h75 : x1 = A *ᵥ xt + B *ᵥ e + C) :
    x1 - mu = A *ᵥ (xt - mu) + B *ᵥ e := by
  have hC : C = mu - A *ᵥ mu := eq_sub_of_add_eq' hmu.symm
  rw [h75, mulVec_sub, hC]
  abel

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

omit [DecidableEq n] in
/-- AKMM, p. 192: taking expectations of (7.5) in deviation form: if `x_t` (here the deviation
`x_t − µ`) solves `x_{t+1} = Ax_t + Bε_{t+1}`, then `E[x_{t+1}] = AE[x_t]`. -/
theorem sde_mean_rec {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {A : Matrix n n ℝ} {B : Matrix n k ℝ} {x : ℕ → Ω → n → ℝ}
    {ε : ℕ → Ω → k → ℝ} (hε : var_ShockMDS μ ℱ ε)
    (h75 : ∀ t ω, x (t + 1) ω = A *ᵥ x t ω + B *ᵥ ε (t + 1) ω)
    (hx0 : ∀ i, MemLp (fun ω => x 0 ω i) 2 μ) (hx0m : ∀ i, Measurable[ℱ 0] fun ω => x 0 ω i)
    (t : ℕ) : var_mean μ (x (t + 1)) = A *ᵥ var_mean μ (x t) :=
  var_mean_rec ⟨h75, hx0, hx0m, hε⟩ t

/-- **AKMM, (7.6), p. 192.** Let `A` be stable, `ε` satisfy (7.2)–(7.3) and `x` solve (7.5)
from a square-integrable `ℱ₀`-measurable `x₀`. If `x` is covariance stationary, then
`E[x_t] = µ = (I − A)⁻¹C`, the autocovariances `Γ(j) = E[(x_{t+j} − µ)(x_t − µ)′]` satisfy the
Lyapunov equation `Γ(0) = AΓ(0)A′ + BB′`, whose only solution is `Σⱼ AʲBB′A′ʲ`, and
`Γ(j) = AʲΓ(0)`. -/
theorem eq_7_6 {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {A : Matrix n n ℝ} {B : Matrix n k ℝ} {C : n → ℝ}
    (hA : IsStableMatrix (A.map Complex.ofRealHom))
    {x : ℕ → Ω → n → ℝ} {ε : ℕ → Ω → k → ℝ} (hε : var_ShockMDS μ ℱ ε)
    (h75 : ∀ t ω, x (t + 1) ω = A *ᵥ x t ω + B *ᵥ ε (t + 1) ω + C)
    (hx0m : ∀ i, Measurable[ℱ 0] fun ω => x 0 ω i) (hs : var_IsCovStationary μ x) :
    ∃ Γ : ℕ → Matrix n n ℝ,
      (∀ t, var_mean μ (x t) = (1 - A)⁻¹ *ᵥ C) ∧
      (∀ t j, var_mom μ (fun ω => x (t + j) ω - (1 - A)⁻¹ *ᵥ C)
        (fun ω => x t ω - (1 - A)⁻¹ *ᵥ C) = Γ j) ∧
      Γ 0 = A * Γ 0 * Aᵀ + B * Bᵀ ∧ Γ 0 = var_lyapSol A (B * Bᵀ) ∧
      ∀ j, Γ j = A ^ j * Γ 0 := by
  obtain ⟨-, hmu⟩ := sde_mean_fixed hA C
  set mu := (1 - A)⁻¹ *ᵥ C with hmu_def
  obtain ⟨hmem, m, Γx, hm, hΓx⟩ := hs
  set z : ℕ → Ω → n → ℝ := fun t ω => x t ω - mu with hz
  have hint : ∀ t i, Integrable (fun ω => x t ω i) μ := fun t i =>
    (hmem t i).integrable one_le_two
  have hmodel : var_Model n μ ℱ A B z ε := by
    refine ⟨fun t ω => ?_, fun i => (hmem 0 i).sub (memLp_const _), fun i => ?_, hε⟩
    · exact sde_deviation hmu (h75 t ω)
    · exact (hx0m i).sub measurable_const
  have hmean_z : ∀ t, var_mean μ (z t) = m - mu := fun t => by
    funext i
    simp only [var_mean, hz, Pi.sub_apply]
    rw [integral_sub (hint t i) (integrable_const _), integral_const]
    have := congrFun (hm t) i
    simp only [var_mean] at this
    simp [this]
  have hcs : var_IsCovStationary μ z := by
    refine ⟨fun t i => (hmem t i).sub (memLp_const _), m - mu, Γx, hmean_z, fun t j => ?_⟩
    rw [← hΓx t j]
    simp only [hz]
    congr 1 <;> funext ω <;> abel
  obtain ⟨Γ, hm0, hΓ, h0, hj⟩ := var_stationary_moments hmodel hA hcs
  refine ⟨Γ, fun t => ?_, hΓ, ?_, h0, fun j => by rw [hj j, h0]⟩
  · have h := hmean_z t
    rw [hm0 t] at h
    funext i
    have hi := congrFun h i
    have hmi := congrFun (hm t) i
    simp only [Pi.zero_apply, Pi.sub_apply] at hi
    rw [hmi]
    linarith
  · have hfix := lyap_fixed A hA (B * Bᵀ)
    rw [h0]
    exact hfix.symm

omit [DecidableEq k] in
/-- AKMM, p. 192: if `ε_t` occurs and no further shocks follow, repeated substitution gives
`x_{t+h} − µ = A^{h+1}(x_{t−1} − µ) + AʰBε_t` (here with `t − 1 = s`). -/
theorem sde_no_further_shocks {A : Matrix n n ℝ} {B : Matrix n k ℝ} {mu : n → ℝ}
    {x : ℕ → n → ℝ} {e : ℕ → k → ℝ}
    (hdev : ∀ t, x (t + 1) - mu = A *ᵥ (x t - mu) + B *ᵥ e (t + 1)) (s : ℕ)
    (hnone : ∀ i, 1 ≤ i → e (s + 1 + i) = 0) (h : ℕ) :
    x (s + 1 + h) - mu = (A ^ (h + 1)) *ᵥ (x s - mu) + (A ^ h * B) *ᵥ e (s + 1) := by
  induction h with
  | zero => simp [hdev s]
  | succ h ih =>
    rw [← Nat.add_assoc, hdev, ih, show s + 1 + h + 1 = s + 1 + (h + 1) by omega,
      hnone (h + 1) (by omega), mulVec_zero, add_zero, mulVec_add,
      mulVec_mulVec, mulVec_mulVec, ← pow_succ', ← Matrix.mul_assoc, ← pow_succ']

omit [DecidableEq k] in
/-- **AKMM, p. 192: the impulse response function `F(h) = AʰBε`.** If two solutions of (7.5)
start from the same `x₀` and their shocks differ only by `ε` at date `s + 1`, then they agree
before `s + 1` and `x′_{s+1+h} − x_{s+1+h} = AʰBε`. -/
theorem sde_impulse_response {A : Matrix n n ℝ} {B : Matrix n k ℝ} {C : n → ℝ}
    {x x' : ℕ → n → ℝ} {e e' : ℕ → k → ℝ}
    (h75 : ∀ t, x (t + 1) = A *ᵥ x t + B *ᵥ e (t + 1) + C)
    (h75' : ∀ t, x' (t + 1) = A *ᵥ x' t + B *ᵥ e' (t + 1) + C) (h0 : x' 0 = x 0) (s : ℕ)
    (v : k → ℝ) (he : ∀ t, e' t = if t = s + 1 then e t + v else e t) :
    (∀ t ≤ s, x' t = x t) ∧ ∀ h, x' (s + 1 + h) - x (s + 1 + h) = (A ^ h * B) *ᵥ v := by
  -- remove the constant by the deviation from the first solution's constant path
  set y : ℕ → n → ℝ := fun t => x t - (∑ i ∈ Finset.range t, (A ^ i) *ᵥ C) with hy
  set y' : ℕ → n → ℝ := fun t => x' t - (∑ i ∈ Finset.range t, (A ^ i) *ᵥ C) with hy'
  have hc : ∀ t, ∑ i ∈ Finset.range (t + 1), (A ^ i) *ᵥ C =
      A *ᵥ (∑ i ∈ Finset.range t, (A ^ i) *ᵥ C) + C := fun t => by
    rw [Finset.sum_range_succ', mulVec_sum]
    simp only [pow_succ', ← mulVec_mulVec, pow_zero, one_mulVec]
  have hrec : ∀ t, y (t + 1) = A *ᵥ y t + B *ᵥ e (t + 1) := fun t => by
    simp only [hy]; rw [h75, hc, mulVec_sub]; abel
  have hrec' : ∀ t, y' (t + 1) = A *ᵥ y' t + B *ᵥ e' (t + 1) := fun t => by
    simp only [hy']; rw [h75', hc, mulVec_sub]; abel
  obtain ⟨hb, hd⟩ := var_impulse_response hrec hrec' (by simp [hy, hy', h0]) s v he
  refine ⟨fun t ht => ?_, fun h => ?_⟩
  · have := hb t ht
    simp only [hy, hy', sub_left_inj] at this
    exact this
  · rw [← hd h]
    simp only [hy, hy']
    abel

end AKMM.Uncertainty
