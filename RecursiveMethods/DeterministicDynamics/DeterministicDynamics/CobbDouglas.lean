/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.EulerScalar

/-!
# The cyclical example: the return function and its steady state

SLP §6.1 (Exercise 6.2) and §6.5 (Exercise 6.7), pp. 138 and 156–158. With `U(c) = c^α` and
`f(z) = z^θ`, the return of (6) is `F(k, y) = [(1 − y)(k/(1 − y))^θ]^α = k^a(1 − y)^b` with
`a = αθ`, `b = α(1 − θ)`, so `a, b > 0` and `a + b = α < 1` (`cdF`). Its partial derivatives are
`F_x = ak^{a−1}(1 − y)^b` and `F_y = −bk^a(1 − y)^{b−1}` (`cdFx`, `cdFy`).

* **Exercise 6.7b** (`ex_6_7b`): the Euler equation
  `F_y(k_t, k_{t+1}) + βF_x(k_{t+1}, k_{t+2}) = 0` has exactly one interior stationary point,
  `k* = βa/(b + βa) = βθ/(1 − θ + βθ)`.
* **Exercise 6.7c**:
  * At `k*`, `(F_yy + βF_xx)/(βF_xy)` equals the book's
    `B = [1 − α(1 − θ)]/[α(1 − θ)] + (1 − αθ)/(αθβ)` (`linearization_B`). So the linear
    approximation is `(k_{t+2} − k*) + B(k_{t+1} − k*) + β⁻¹(k_t − k*) = 0`.
  * The roots of `λ² + Bλ + β⁻¹` are real, with `λ₁λ₂ = β⁻¹` (so `λ₂ = (βλ₁)⁻¹`) and
    `λ₁ + λ₂ = −B`, and both are negative (`ex_6_7c`).
  * `k*` is locally stable, in the sense that one root lies in `(−1, 0)`, iff `B > 1 + β⁻¹`
    (`ex_6_7c_stable_iff`).
* **Exercise 6.7d** (`ex_6_7d`): for `β = 0.1`, `α = 0.8`, `θ = 0.75`, `k* = 3/13 ≈ 0.23` and
  `B = 32/3 < 11 = 1 + β⁻¹`: both roots are below `−1`, so `k*` is unstable.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Real

/-- `F(k, y) = k^a(1 − y)^b`. -/
noncomputable def cdF (a b k y : ℝ) : ℝ := k ^ a * (1 - y) ^ b

/-- `F_x(k, y) = ak^{a−1}(1 − y)^b`. -/
noncomputable def cdFx (a b k y : ℝ) : ℝ := a * k ^ (a - 1) * (1 - y) ^ b

/-- `F_y(k, y) = −bk^a(1 − y)^{b−1}`. -/
noncomputable def cdFy (a b k y : ℝ) : ℝ := -(b * k ^ a * (1 - y) ^ (b - 1))

/-- `F_xx = a(a − 1)k^{a−2}(1 − y)^b`. -/
noncomputable def cdFxx (a b k y : ℝ) : ℝ := a * (a - 1) * k ^ (a - 2) * (1 - y) ^ b

/-- `F_yy = b(b − 1)k^a(1 − y)^{b−2}`. -/
noncomputable def cdFyy (a b k y : ℝ) : ℝ := b * (b - 1) * k ^ a * (1 - y) ^ (b - 2)

/-- `F_xy = −abk^{a−1}(1 − y)^{b−1}`. -/
noncomputable def cdFxy (a b k y : ℝ) : ℝ := -(a * b * k ^ (a - 1) * (1 - y) ^ (b - 1))

variable {a b : ℝ}

/-- `F_x` is the partial derivative in `k` (for `k > 0`). -/
theorem hasDerivAt_cdF_k {k : ℝ} (hk : 0 < k) (y : ℝ) :
    HasDerivAt (fun k => cdF a b k y) (cdFx a b k y) k := by
  have := (hasDerivAt_rpow_const (p := a) (Or.inl hk.ne')).mul_const ((1 - y) ^ b)
  simpa [cdF, cdFx, mul_comm, mul_assoc, mul_left_comm] using this

/-- `F_y` is the partial derivative in `y` (for `y < 1`). -/
theorem hasDerivAt_cdF_y (k : ℝ) {y : ℝ} (hy : y < 1) :
    HasDerivAt (fun y => cdF a b k y) (cdFy a b k y) y := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have := (h1.rpow_const (p := b) (Or.inl (by linarith))).const_mul (k ^ a)
  unfold cdF cdFy
  convert this using 1
  ring

/-- `F_xx` and `F_xy` are the partial derivatives of `F_x`. -/
theorem hasDerivAt_cdFx_k {k : ℝ} (hk : 0 < k) (y : ℝ) :
    HasDerivAt (fun k => cdFx a b k y) (cdFxx a b k y) k := by
  have := ((hasDerivAt_rpow_const (p := a - 1) (Or.inl hk.ne')).const_mul a).mul_const
    ((1 - y) ^ b)
  unfold cdFx cdFxx
  convert this using 1
  rw [show a - 1 - 1 = a - 2 by ring]
  ring

theorem hasDerivAt_cdFx_y (k : ℝ) {y : ℝ} (hy : y < 1) :
    HasDerivAt (fun y => cdFx a b k y) (cdFxy a b k y) y := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have := (h1.rpow_const (p := b) (Or.inl (by linarith))).const_mul (a * k ^ (a - 1))
  unfold cdFx cdFxy
  convert this using 1
  ring

theorem hasDerivAt_cdFy_y (k : ℝ) {y : ℝ} (hy : y < 1) :
    HasDerivAt (fun y => cdFy a b k y) (cdFyy a b k y) y := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have := (h1.rpow_const (p := b - 1) (Or.inl (by linarith))).const_mul (-(b * k ^ a))
  have e : (fun y => cdFy a b k y) = fun y => -(b * k ^ a) * (1 - y) ^ (b - 1) := by
    funext z; simp only [cdFy]; ring
  rw [e]
  convert this using 1
  rw [show b - 1 - 1 = b - 2 by ring]
  simp only [cdFyy]
  ring

/-- The Euler equation at a constant path factors as
`F_y(k, k) + βF_x(k, k) = k^{a−1}(1 − k)^{b−1}[βa(1 − k) − bk]`. -/
theorem euler_steady {β k : ℝ} (hk : 0 < k) (hk1 : k < 1) :
    cdFy a b k k + β * cdFx a b k k =
      k ^ (a - 1) * (1 - k) ^ (b - 1) * (β * a * (1 - k) - b * k) := by
  have h1 : k ^ a = k ^ (a - 1) * k := by
    rw [← rpow_add_one hk.ne', sub_add_cancel]
  have h2 : (1 - k) ^ b = (1 - k) ^ (b - 1) * (1 - k) := by
    rw [← rpow_add_one (by linarith), sub_add_cancel]
  simp only [cdFy, cdFx, h1, h2]
  ring

/-- **Exercise 6.7b.** The unique interior stationary point of the Euler equation is
`k* = βa/(b + βa)`. -/
theorem ex_6_7b {β : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ : 0 < β) :
    let kstar := β * a / (b + β * a)
    0 < kstar ∧ kstar < 1 ∧ cdFy a b kstar kstar + β * cdFx a b kstar kstar = 0 ∧
      ∀ k, 0 < k → k < 1 → cdFy a b k k + β * cdFx a b k k = 0 → k = kstar := by
  intro kstar
  have hpos : 0 < b + β * a := by positivity
  have hk0 : 0 < kstar := by positivity
  have hk1 : kstar < 1 := by
    simp only [kstar]; rw [div_lt_one hpos]; linarith
  have hlin : β * a * (1 - kstar) - b * kstar = 0 := by
    simp only [kstar]; field_simp; ring
  refine ⟨hk0, hk1, by rw [euler_steady hk0 hk1, hlin, mul_zero], fun k hk hk1' h => ?_⟩
  rw [euler_steady hk hk1'] at h
  have hne : k ^ (a - 1) * (1 - k) ^ (b - 1) ≠ 0 :=
    mul_ne_zero (rpow_pos_of_pos hk _).ne' (rpow_pos_of_pos (by linarith) _).ne'
  have := (mul_eq_zero.1 h).resolve_left hne
  simp only [kstar]
  field_simp
  linarith

/-- In the book's parameters, `k* = βθ/(1 − θ + βθ)`. -/
theorem kstar_eq {α θ β : ℝ} (hα : 0 < α) :
    β * (α * θ) / (α * (1 - θ) + β * (α * θ)) = β * θ / (1 - θ + β * θ) := by
  have : α * (1 - θ) + β * (α * θ) = α * (1 - θ + β * θ) := by ring
  rw [this, show β * (α * θ) = α * (β * θ) by ring, mul_div_mul_left _ _ hα.ne']

/-- **Exercise 6.7c (the linearization).** At `k* = βa/(b + βa)`,
`(F_yy + βF_xx)/(βF_xy) = (1 − b)/b + (1 − a)/(βa)`, which is the book's
`B = [1 − α(1 − θ)]/[α(1 − θ)] + (1 − αθ)/(αθβ)`. -/
theorem linearization_B {β : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ : 0 < β) :
    let kstar := β * a / (b + β * a)
    (cdFyy a b kstar kstar + β * cdFxx a b kstar kstar) / (β * cdFxy a b kstar kstar) =
      (1 - b) / b + (1 - a) / (β * a) := by
  intro kstar
  obtain ⟨hk0, hk1, -, -⟩ := ex_6_7b ha hb hβ
  have hk0' : 0 < kstar := hk0
  have hk1' : 0 < 1 - kstar := by have : kstar < 1 := hk1; linarith
  set p := kstar ^ (a - 1) * (1 - kstar) ^ (b - 1)
  have hp : 0 < p := mul_pos (rpow_pos_of_pos hk0' _) (rpow_pos_of_pos hk1' _)
  -- express every second derivative through `p`
  have e1 : kstar ^ a = kstar ^ (a - 1) * kstar := by
    rw [← rpow_add_one hk0'.ne', sub_add_cancel]
  have e2 : (1 - kstar) ^ b = (1 - kstar) ^ (b - 1) * (1 - kstar) := by
    rw [← rpow_add_one hk1'.ne', sub_add_cancel]
  have e3 : kstar ^ (a - 2) * kstar = kstar ^ (a - 1) := by
    rw [← rpow_add_one hk0'.ne']; congr 1; ring
  have e4 : (1 - kstar) ^ (b - 2) * (1 - kstar) = (1 - kstar) ^ (b - 1) := by
    rw [← rpow_add_one hk1'.ne']; congr 1; ring
  have hxx : cdFxx a b kstar kstar * kstar = a * (a - 1) * p * (1 - kstar) := by
    simp only [cdFxx, p, e2]; rw [← e3]; ring
  have hyy : cdFyy a b kstar kstar * (1 - kstar) = b * (b - 1) * p * kstar := by
    simp only [cdFyy, p, e1]; rw [← e4]; ring
  have hxy : cdFxy a b kstar kstar = -(a * b * p) := by simp only [cdFxy, p]; ring
  have hss : b * kstar = β * a * (1 - kstar) := by
    simp only [kstar]; field_simp; ring
  have hxx' : cdFxx a b kstar kstar = a * (a - 1) * p * (1 - kstar) / kstar := by
    rw [← hxx, mul_div_cancel_right₀ _ hk0'.ne']
  have hyy' : cdFyy a b kstar kstar = b * (b - 1) * p * kstar / (1 - kstar) := by
    rw [← hyy, mul_div_cancel_right₀ _ hk1'.ne']
  have r1 : kstar / (1 - kstar) = β * a / b := by
    rw [div_eq_div_iff hk1'.ne' hb.ne']; linarith
  have r2 : (1 - kstar) / kstar = b / (β * a) := by
    rw [div_eq_div_iff hk0'.ne' (by positivity)]; linarith
  rw [hxy, hxx', hyy']
  calc (b * (b - 1) * p * kstar / (1 - kstar) + β * (a * (a - 1) * p * (1 - kstar) / kstar)) /
        (β * -(a * b * p))
      = (b * (b - 1) * p * (kstar / (1 - kstar)) +
          β * (a * (a - 1) * p * ((1 - kstar) / kstar))) / (β * -(a * b * p)) := by ring
    _ = (1 - b) / b + (1 - a) / (β * a) := by
      rw [r1, r2]
      field_simp
      ring

/-- **Exercise 6.7c (the roots).** For `0 < a`, `0 < b`, `a + b < 1` and `β > 0`, with
`B = (1 − b)/b + (1 − a)/(βa)`, the roots of `λ² + Bλ + β⁻¹` are real and negative, with product
`β⁻¹` (so `λ₂ = (βλ₁)⁻¹`) and sum `−B`. -/
theorem ex_6_7c {β : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1) (hβ : 0 < β) :
    let B := (1 - b) / b + (1 - a) / (β * a)
    ∃ l₁ l₂ : ℝ, l₁ < 0 ∧ l₂ < 0 ∧ l₁ * l₂ = β⁻¹ ∧ l₁ + l₂ = -B ∧
      quadRoot (-B) β⁻¹ l₁ ∧ quadRoot (-B) β⁻¹ l₂ ∧
      ∀ μ, quadRoot (-B) β⁻¹ μ → μ = l₁ ∨ μ = l₂ := by
  intro B
  have h1b : 0 < 1 - b := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hBpos : 0 < B := by positivity
  -- `B² ≥ 4/β`: `B ≥ 2√((1 − a)(1 − b)/(abβ))` and `(1 − a)(1 − b) ≥ ab`
  have hd : 4 * β⁻¹ ≤ (-B) ^ 2 := by
    rw [neg_sq]
    have hx : 0 < (1 - b) / b := by positivity
    have hy : 0 < (1 - a) / (β * a) := by positivity
    have hxy : β⁻¹ ≤ (1 - b) / b * ((1 - a) / (β * a)) := by
      rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
      field_simp
      nlinarith
    nlinarith [sq_nonneg ((1 - b) / b - (1 - a) / (β * a))]
  set q := Real.sqrt ((-B) ^ 2 - 4 * β⁻¹)
  have hq : q ^ 2 = (-B) ^ 2 - 4 * β⁻¹ := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqc : (q : ℂ) ^ 2 = ((-B : ℝ) : ℂ) ^ 2 - 4 * (β : ℂ)⁻¹ := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hq
    push_cast at this ⊢
    exact this
  have hroot : ∀ r : ℝ, r = (-B + q) / 2 ∨ r = (-B - q) / 2 → quadRoot (-B) β⁻¹ r := by
    rintro r (rfl | rfl) <;> simp only [quadRoot] <;> push_cast at hqc ⊢ <;>
      linear_combination (1 / 4 : ℂ) * hqc
  have hqB : q < B := by
    have : q ^ 2 < B ^ 2 := by
      rw [hq, neg_sq]; have := inv_pos.2 hβ; linarith
    exact lt_of_pow_lt_pow_left₀ 2 hBpos.le this
  refine ⟨(-B + q) / 2, (-B - q) / 2, by linarith, by linarith, by nlinarith, by ring,
    hroot _ (Or.inl rfl), hroot _ (Or.inr rfl), fun μ hμ => ?_⟩
  obtain ⟨r, rfl, hr⟩ := quadRoot_real hd hμ
  rcases hr with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Exercise 6.7c (stability).** The roots of `λ² + Bλ + β⁻¹` are negative with product
`β⁻¹ > 1`, so at most one lies in `(−1, 0)`; one does iff `B > 1 + β⁻¹`. -/
theorem ex_6_7c_stable_iff {B β l₁ l₂ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (h1 : l₁ < 0)
    (h2 : l₂ < 0) (hprod : l₁ * l₂ = β⁻¹) (hsum : l₁ + l₂ = -B) :
    (-1 < l₁ ∨ -1 < l₂) ↔ 1 + β⁻¹ < B := by
  have hbi : 1 < β⁻¹ := (one_lt_inv₀ hβ).2 hβ1
  -- `p(−1) = 1 − B + β⁻¹ = (−1 − l₁)(−1 − l₂)`
  have hp : 1 - B + β⁻¹ = (-1 - l₁) * (-1 - l₂) := by nlinarith
  constructor
  · rintro (h | h)
    · have : l₂ < -1 := by
        by_contra hc; push Not at hc
        have : l₁ * l₂ ≤ 1 := by nlinarith
        linarith
      nlinarith
    · have : l₁ < -1 := by
        by_contra hc; push Not at hc
        have : l₁ * l₂ ≤ 1 := by nlinarith
        linarith
      nlinarith
  · intro hB
    by_contra hc
    push Not at hc
    nlinarith

/-- **Exercise 6.7d.** For `β = 0.1`, `α = 0.8`, `θ = 0.75` (`a = 0.6`, `b = 0.2`):
`k* = 3/13 ≈ 0.23` and `B = 32/3 < 11 = 1 + β⁻¹`, so `k*` is not locally stable. -/
theorem ex_6_7d :
    (1 / 10 : ℝ) * (4 / 5 * (3 / 4)) / (4 / 5 * (1 - 3 / 4) + 1 / 10 * (4 / 5 * (3 / 4))) =
        3 / 13 ∧
      (1 - 1 / 5 : ℝ) / (1 / 5) + (1 - 3 / 5) / (1 / 10 * (3 / 5)) = 32 / 3 ∧
      ¬ (1 + (1 / 10 : ℝ)⁻¹ < 32 / 3) := by
  norm_num

end StokeyLucasPrescott.DeterministicDynamics
