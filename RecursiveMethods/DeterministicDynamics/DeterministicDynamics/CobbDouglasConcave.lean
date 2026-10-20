/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.CobbDouglas
import DeterministicDynamics.EulerEquations

/-!
# The cyclical example: concavity and differentiability of the return

SLP §6.5, p. 156. `F(k, y) = k^a(1 − y)^b`, `a, b > 0`, `a + b ≤ 1`, on `[0, 1]²`.

* `geomMean_concave`: the weighted geometric mean `u₁^p u₂^q` (`p + q = 1`) is concave on `ℝ²₊`.
  Divide by its value at the convex combination and apply the weighted AM–GM inequality.
* `cd_concave`: `F` is concave on `[0, 1]²`, since `F = (geometric mean)^{a+b}` composed with an
  affine map.
* `cd_not_strict`: `F` is **not** strictly concave in the sense of Assumption 4.7, because
  `F(·, 1) ≡ 0`: `F(1/4, 1) = F(3/4, 1) = F(1/2, 1) = 0`. Exercise 6.7a's claim that
  Assumption 4.7 holds is therefore false as stated.
* `hasFDerivAt_cd`: at interior points, `DF(k, y)(u, w) = F_x u + F_y w`.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Set Real

/-- The weighted geometric mean `u₁^p u₂^q`, `p, q > 0`, `p + q = 1`, is concave on `ℝ²₊`. -/
theorem geomMean_concave {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1)
    {u₁ u₂ v₁ v₂ θ : ℝ} (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * (u₁ ^ p * u₂ ^ q) + (1 - θ) * (v₁ ^ p * v₂ ^ q) ≤
      (θ * u₁ + (1 - θ) * v₁) ^ p * (θ * u₂ + (1 - θ) * v₂) ^ q := by
  set m₁ := θ * u₁ + (1 - θ) * v₁
  set m₂ := θ * u₂ + (1 - θ) * v₂
  have hm₁ : 0 ≤ m₁ := by positivity
  have hm₂ : 0 ≤ m₂ := by positivity
  have hθ1 : 0 ≤ 1 - θ := by linarith
  -- if a coordinate of the combination vanishes, both sides are zero
  have zero_case : ∀ {s₁ s₂ : ℝ} (r : ℝ), 0 < r → 0 ≤ s₁ → 0 ≤ s₂ →
      θ * s₁ + (1 - θ) * s₂ = 0 → θ * s₁ ^ r = 0 ∧ (1 - θ) * s₂ ^ r = 0 :=
    fun {s₁} {s₂} r hr h₁ h₂ h => by
      have e1 : θ * s₁ = 0 := by nlinarith [mul_nonneg h0 h₁, mul_nonneg hθ1 h₂]
      have e2 : (1 - θ) * s₂ = 0 := by nlinarith [mul_nonneg h0 h₁, mul_nonneg hθ1 h₂]
      constructor
      · rcases mul_eq_zero.1 e1 with h | h
        · rw [h, zero_mul]
        · rw [h, zero_rpow hr.ne', mul_zero]
      · rcases mul_eq_zero.1 e2 with h | h
        · rw [h, zero_mul]
        · rw [h, zero_rpow hr.ne', mul_zero]
  rcases eq_or_lt_of_le hm₁ with he₁ | hlt₁
  · obtain ⟨z1, z2⟩ := zero_case p hp hu₁ hv₁ he₁.symm
    rw [← he₁, zero_rpow hp.ne', zero_mul,
      show θ * (u₁ ^ p * u₂ ^ q) = θ * u₁ ^ p * u₂ ^ q by ring,
      show (1 - θ) * (v₁ ^ p * v₂ ^ q) = (1 - θ) * v₁ ^ p * v₂ ^ q by ring, z1, z2]
    simp
  rcases eq_or_lt_of_le hm₂ with he₂ | hlt₂
  · obtain ⟨z1, z2⟩ := zero_case q hq hu₂ hv₂ he₂.symm
    rw [← he₂, zero_rpow hq.ne', mul_zero,
      show θ * (u₁ ^ p * u₂ ^ q) = θ * u₂ ^ q * u₁ ^ p by ring,
      show (1 - θ) * (v₁ ^ p * v₂ ^ q) = (1 - θ) * v₂ ^ q * v₁ ^ p by ring, z1, z2]
    simp
  -- AM–GM for `u/m` and `v/m`
  have hu := geom_mean_le_arith_mean2_weighted hp.le hq.le (div_nonneg hu₁ hlt₁.le)
    (div_nonneg hu₂ hlt₂.le) hpq
  have hv := geom_mean_le_arith_mean2_weighted hp.le hq.le (div_nonneg hv₁ hlt₁.le)
    (div_nonneg hv₂ hlt₂.le) hpq
  rw [div_rpow hu₁ hlt₁.le, div_rpow hu₂ hlt₂.le] at hu
  rw [div_rpow hv₁ hlt₁.le, div_rpow hv₂ hlt₂.le] at hv
  have hG : 0 < m₁ ^ p * m₂ ^ q := mul_pos (rpow_pos_of_pos hlt₁ _) (rpow_pos_of_pos hlt₂ _)
  have e : ∀ s t : ℝ, s ^ p / m₁ ^ p * (t ^ q / m₂ ^ q) = s ^ p * t ^ q / (m₁ ^ p * m₂ ^ q) :=
    fun s t => by rw [div_mul_div_comm]
  rw [e] at hu hv
  rw [div_le_iff₀ hG] at hu hv
  have hsum : θ * (p * (u₁ / m₁) + q * (u₂ / m₂)) + (1 - θ) * (p * (v₁ / m₁) + q * (v₂ / m₂)) =
      1 := by
    field_simp
    simp only [m₁, m₂] at *
    linear_combination (θ * u₁ + (1 - θ) * v₁) * (θ * u₂ + (1 - θ) * v₂) * hpq
  have := add_le_add (mul_le_mul_of_nonneg_left hu h0)
    (mul_le_mul_of_nonneg_left hv (by linarith : (0 : ℝ) ≤ 1 - θ))
  nlinarith

variable {a b : ℝ}

/-- **`F` is concave on `[0, 1]²`.** -/
theorem cd_concave (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) :
    ConcaveOn ℝ (Icc 0 1 ×ˢ Icc 0 1) (fun p : ℝ × ℝ => cdF a b p.1 p.2) := by
  refine ⟨(convex_Icc 0 1).prod (convex_Icc 0 1), ?_⟩
  rintro ⟨k, y⟩ ⟨⟨hk0, hk1⟩, ⟨hy0, hy1⟩⟩ ⟨k', y'⟩ ⟨⟨hk0', hk1'⟩, ⟨hy0', hy1'⟩⟩ θ μ h0 hμ hθμ
  simp only at hk0 hk1 hy0 hy1 hk0' hk1' hy0' hy1'
  obtain rfl : μ = 1 - θ := by linarith
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  set s := a + b
  have hs : 0 < s := by positivity
  set p := a / s
  set q := b / s
  have hp : 0 < p := div_pos ha hs
  have hq : 0 < q := div_pos hb hs
  have hpq : p + q = 1 := by simp only [p, q, s]; field_simp
  -- `F(k, y) = (k^p(1 − y)^q)^s`
  have hF : ∀ k y : ℝ, 0 ≤ k → y ≤ 1 → cdF a b k y = (k ^ p * (1 - y) ^ q) ^ s := by
    intro k y hk hy
    rw [mul_rpow (rpow_nonneg hk _) (rpow_nonneg (by linarith) _), ← rpow_mul hk,
      ← rpow_mul (by linarith : (0 : ℝ) ≤ 1 - y)]
    simp only [cdF, p, q, div_mul_cancel₀ _ hs.ne']
  have hm : θ * y + (1 - θ) * y' ≤ 1 := by nlinarith
  have hmk : 0 ≤ θ * k + (1 - θ) * k' := by nlinarith
  rw [hF k y hk0 hy1, hF k' y' hk0' hy1', hF _ _ hmk hm]
  have e : 1 - (θ * y + (1 - θ) * y') = θ * (1 - y) + (1 - θ) * (1 - y') := by ring
  rw [e]
  have hG := geomMean_concave (u₁ := k) (u₂ := 1 - y) (v₁ := k') (v₂ := 1 - y') hp hq hpq hk0
    (by linarith) hk0' (by linarith) h0 (by linarith)
  have hGu : 0 ≤ k ^ p * (1 - y) ^ q := mul_nonneg (rpow_nonneg hk0 _)
    (rpow_nonneg (by linarith) _)
  have hGv : 0 ≤ k' ^ p * (1 - y') ^ q := mul_nonneg (rpow_nonneg hk0' _)
    (rpow_nonneg (by linarith) _)
  have hconc := (concaveOn_rpow hs.le hab).2 (mem_Ici.2 hGu) (mem_Ici.2 hGv) h0
    (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hconc
  refine hconc.trans (rpow_le_rpow (by positivity) hG hs.le)

/-- **Exercise 6.7a (correction).** `F` is not strictly concave in the sense of Assumption 4.7:
on the edge `y = 1`, `F(1/4, 1) = F(3/4, 1) = F(1/2, 1) = 0`, although `1/4 ≠ 3/4`. -/
theorem cd_not_strict (hb : 0 < b) :
    (1 / 2 : ℝ) * cdF a b (1 / 4) 1 + (1 / 2) * cdF a b (3 / 4) 1 =
      cdF a b (1 / 2 * (1 / 4) + 1 / 2 * (3 / 4)) (1 / 2 * 1 + 1 / 2 * 1) := by
  norm_num [cdF, zero_rpow hb.ne']

/-- At an interior point, `DF(k, y)(u, w) = F_x u + F_y w`. -/
theorem hasFDerivAt_cd {k y : ℝ} (hk : 0 < k) (hy : y < 1) :
    HasFDerivAt (fun p : ℝ × ℝ => cdF a b p.1 p.2)
      (cdFx a b k y • ContinuousLinearMap.fst ℝ ℝ ℝ +
        cdFy a b k y • ContinuousLinearMap.snd ℝ ℝ ℝ) (k, y) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ a)
      ((a * k ^ (a - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ) (k, y) := by
    have := (hasDerivAt_rpow_const (p := a) (Or.inl hk.ne')).comp_hasFDerivAt (k, y)
      (hasFDerivAt_fst (𝕜 := ℝ) (p := (k, y)))
    exact this
  have h2' : HasDerivAt (fun z : ℝ => (1 - z) ^ b) (-(b * (1 - y) ^ (b - 1))) y := by
    have hlin : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    convert hlin.rpow_const (p := b) (Or.inl (by linarith)) using 1
    ring
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => (1 - p.2) ^ b)
      ((-(b * (1 - y) ^ (b - 1))) • ContinuousLinearMap.snd ℝ ℝ ℝ) (k, y) := by
    have := h2'.comp_hasFDerivAt (k, y) (hasFDerivAt_snd (𝕜 := ℝ) (p := (k, y)))
    exact this
  unfold cdF
  convert h1.mul h2 using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [cdFx, cdFy, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

end StokeyLucasPrescott.DeterministicDynamics
