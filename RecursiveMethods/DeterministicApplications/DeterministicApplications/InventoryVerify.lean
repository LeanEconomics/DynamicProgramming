/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.InventorySolution

/-!
# The (s, S) policy: verification

SLP Exercise 5.14d–h, continued. Throughout, `N` maximizes `Y_n`, `Y = Y_N > 0` and
`φ(u) = −c₁u + βw(u)`, so that ordering up to `u` from `z` is worth `−c₀ + c₁z + φ(u)`.

* **Exercise 5.14d (derivatives)**: `w' = p` on `(0, 1)`, `w' = β^{ν−1}c₁` on `(ν, ν + A)` and
  `w' = β^νp` on `(ν + A, ν + 1)` (`wSS_deriv_low`, `wSS_deriv_left`, `wSS_deriv_right`); `w` is not
  differentiable at `1`, at each integer `ν ≥ 2`, or at `ν + A` (`wSS_kink_one`,
  `wSS_kink_int`, `wSS_kink_A`).
* **Exercise 5.14e**: `phi_cell_convex`: `φ` is convex on each cell, so
  (`ex_5_14e`) any order is beaten either by the limit `y ↓ 0` (not attained) or by an order
  that brings the stock to an integer.
* **Exercise 5.14f** (`ex_5_14f`): ordering up to the integer `n` from `z` is worth
  `c₁z + r_n + βⁿY`.
* **Exercise 5.14g** (`ex_5_14g`): `max_{n ≥ 1} (r_n + βⁿY_N) = Y_N`.
* **Exercise 5.14h** (`ex_5_14h`): `w` satisfies (1); so `w = v` (`ex_5_14_value`). The key
  step for `x ≥ 2` is `key_ineq`: `βw(z) > c₁z + r_n + βⁿY` for integers `n > z ≥ 1`.
* `ex_5_14_policy`: the (s, S) policy, `s = 1 + A`, `S = N`: below `1 + A` order up to `N`,
  above it do not order; at `1 + A` both are optimal, so the optimal policy is not unique
  (Exercise 5.14a).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {p c₀ c₁ β : ℝ} {N : ℕ}

/-- The branches differ by `(βp − c₁)(α − A)`. -/
theorem cross_eq (h : SSHyp p c₀ c₁ β N) (a : ℝ) :
    β * (p * a + Yn p c₀ c₁ β N) - (c₁ * a + Yn p c₀ c₁ β N) =
      (β * p - c₁) * (a - Aind p c₀ c₁ β N) := by
  have hm : β * p - c₁ ≠ 0 := by linarith [h.inv.margin]
  unfold Aind
  field_simp
  ring

/-- On `[ν, ν + A]`, `w(u) = p(1 − β^ν)/(1 − β) + β^{ν−1}(c₁(u − ν) + Y)`. -/
theorem wSS_left_piece (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) {u : ℝ}
    (hu : u ∈ Icc (ν : ℝ) (ν + Aind p c₀ c₁ β N)) :
    wSS p c₀ c₁ β N u = p * (1 - β ^ ν) / (1 - β) +
      β ^ (ν - 1) * (c₁ * (u - ν) + Yn p c₀ c₁ β N) := by
  rw [wSS_cell h hν ⟨hu.1, by linarith [hu.2, h.A_lt]⟩, cellW, max_eq_left]
  have := cross_eq h (u - ν)
  nlinarith [h.inv.margin, hu.2]

/-- On `[ν + A, ν + 1]`, `w(u) = p(1 − β^ν)/(1 − β) + β^ν(p(u − ν) + Y)`. -/
theorem wSS_right_piece (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) {u : ℝ}
    (hu : u ∈ Icc ((ν : ℝ) + Aind p c₀ c₁ β N) (ν + 1)) :
    wSS p c₀ c₁ β N u = p * (1 - β ^ ν) / (1 - β) +
      β ^ ν * (p * (u - ν) + Yn p c₀ c₁ β N) := by
  rw [wSS_cell h hν ⟨by linarith [hu.1, h.A_pos], hu.2⟩, cellW,
    max_eq_right ((cross_iff h _).2 (by linarith [hu.1]))]
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

/-! ### Exercise 5.14d: derivatives -/

theorem wSS_deriv_low {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt (wSS p c₀ c₁ β N) p x := by
  have h1 : HasDerivAt (fun u => p * u + Yn p c₀ c₁ β N) p x := by
    simpa using ((hasDerivAt_id' x).const_mul p).add_const (Yn p c₀ c₁ β N)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hx.2] with u hu
  exact wSS_low (le_of_lt hu)

theorem wSS_deriv_left (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) {x : ℝ}
    (hx : x ∈ Ioo (ν : ℝ) (ν + Aind p c₀ c₁ β N)) :
    HasDerivAt (wSS p c₀ c₁ β N) (β ^ (ν - 1) * c₁) x := by
  have h1 : HasDerivAt (fun u => p * (1 - β ^ ν) / (1 - β) +
      β ^ (ν - 1) * (c₁ * (u - ν) + Yn p c₀ c₁ β N)) (β ^ (ν - 1) * c₁) x := by
    have := (((hasDerivAt_id' x).sub_const (ν : ℝ)).const_mul c₁).add_const (Yn p c₀ c₁ β N)
      |>.const_mul (β ^ (ν - 1)) |>.const_add (p * (1 - β ^ ν) / (1 - β))
    simpa using this
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with u hu
  exact wSS_left_piece h hν ⟨hu.1.le, hu.2.le⟩

theorem wSS_deriv_right (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) {x : ℝ}
    (hx : x ∈ Ioo ((ν : ℝ) + Aind p c₀ c₁ β N) (ν + 1)) :
    HasDerivAt (wSS p c₀ c₁ β N) (β ^ ν * p) x := by
  have h1 : HasDerivAt (fun u => p * (1 - β ^ ν) / (1 - β) +
      β ^ ν * (p * (u - ν) + Yn p c₀ c₁ β N)) (β ^ ν * p) x := by
    have := (((hasDerivAt_id' x).sub_const (ν : ℝ)).const_mul p).add_const (Yn p c₀ c₁ β N)
      |>.const_mul (β ^ ν) |>.const_add (p * (1 - β ^ ν) / (1 - β))
    simpa using this
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with u hu
  exact wSS_right_piece h hν ⟨hu.1.le, hu.2.le⟩

/-- A function that is affine with slope `a` just left of `x₀` and slope `b ≠ a` just right of it is
not differentiable at `x₀`. -/
theorem not_differentiableAt_of_kink {f : ℝ → ℝ} {x₀ a b : ℝ}
    (hL : ∀ᶠ u in 𝓝[≤] x₀, f u = f x₀ + a * (u - x₀))
    (hR : ∀ᶠ u in 𝓝[≥] x₀, f u = f x₀ + b * (u - x₀)) (hab : a ≠ b) :
    ¬ DifferentiableAt ℝ f x₀ := by
  intro hd
  have hlin : ∀ c : ℝ, HasDerivAt (fun u => f x₀ + c * (u - x₀)) c x₀ := fun c => by
    simpa using (((hasDerivAt_id' x₀).sub_const x₀).const_mul c).const_add (f x₀)
  have h1 : HasDerivWithinAt f a (Iic x₀) x₀ :=
    (hlin a).hasDerivWithinAt.congr_of_eventuallyEq hL (by simp)
  have h2 : HasDerivWithinAt f b (Ici x₀) x₀ :=
    (hlin b).hasDerivWithinAt.congr_of_eventuallyEq hR (by simp)
  have e1 := (uniqueDiffWithinAt_Iic x₀).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt h1
  have e2 := (uniqueDiffWithinAt_Ici x₀).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt h2
  exact hab (e1.symm.trans e2)

/-- **Exercise 5.14d.** `w` has a kink at `1`: slopes `p` and `c₁`. -/
theorem wSS_kink_one (h : SSHyp p c₀ c₁ β N) : ¬ DifferentiableAt ℝ (wSS p c₀ c₁ β N) 1 := by
  have hw1 : wSS p c₀ c₁ β N 1 = p + Yn p c₀ c₁ β N := by rw [wSS_low le_rfl]; ring
  refine not_differentiableAt_of_kink (a := p) (b := c₁) ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with u (hu : u ≤ 1)
    rw [wSS_low hu, hw1]; ring
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
      (show (1 : ℝ) < 1 + Aind p c₀ c₁ β N by linarith [h.A_pos]))] with u (hu : 1 ≤ u) hu'
    rw [wSS_left_piece h (ν := 1) le_rfl ⟨by simpa using hu, by simpa using hu'.le⟩, hw1]
    simp only [Nat.cast_one, pow_one, Nat.sub_self, pow_zero, one_mul]
    have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
    field_simp
    ring
  · have : c₁ < p := by nlinarith [h.inv.margin, h.inv.β_lt, h.inv.β_pos, h.inv.c₁_pos]
    exact this.ne'

/-- **Exercise 5.14d.** `w` has a kink at each integer `ν ≥ 2`: slopes `β^{ν−1}p` and
`β^{ν−1}c₁`. -/
theorem wSS_kink_int (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 2 ≤ ν) :
    ¬ DifferentiableAt ℝ (wSS p c₀ c₁ β N) ν := by
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 2 := ⟨ν - 2, by omega⟩
  have hb := pow_pos h.inv.β_pos (m + 1)
  have hw : wSS p c₀ c₁ β N ((m + 2 : ℕ) : ℝ) = p * (1 - β ^ (m + 2)) / (1 - β) +
      β ^ (m + 1) * Yn p c₀ c₁ β N := by
    rw [wSS_left_piece h (ν := m + 2) (by omega) ⟨le_rfl, by linarith [h.A_pos]⟩]
    simp
  refine not_differentiableAt_of_kink (a := β ^ (m + 1) * p) (b := β ^ (m + 1) * c₁) ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds
      (show ((m + 1 : ℕ) : ℝ) + Aind p c₀ c₁ β N < ((m + 2 : ℕ) : ℝ) by
        push_cast; linarith [h.A_lt]))] with u (hu : u ≤ _) hu'
    rw [wSS_right_piece h (ν := m + 1) (by omega) ⟨hu'.le, by push_cast at hu ⊢; linarith⟩, hw]
    have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
    push_cast
    field_simp
    ring
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
      (show ((m + 2 : ℕ) : ℝ) < (m + 2 : ℕ) + Aind p c₀ c₁ β N by linarith [h.A_pos]))] with
      u (hu : _ ≤ u) hu'
    rw [wSS_left_piece h (ν := m + 2) (by omega) ⟨hu, hu'.le⟩, hw]
    simp only [show m + 2 - 1 = m + 1 by omega]
    ring
  · intro he
    have : p = c₁ := mul_left_cancel₀ hb.ne' he
    nlinarith [h.inv.margin, h.inv.β_lt, h.inv.β_pos, h.inv.c₁_pos]

/-- **Exercise 5.14d.** `w` has a kink at `ν + A` (`ν ≥ 1`): slopes `β^{ν−1}c₁` and `β^νp`. -/
theorem wSS_kink_A (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) :
    ¬ DifferentiableAt ℝ (wSS p c₀ c₁ β N) (ν + Aind p c₀ c₁ β N) := by
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  have hb := pow_pos h.inv.β_pos m
  set A := Aind p c₀ c₁ β N
  have hw := wSS_left_piece h (ν := m + 1) hν (u := ((m + 1 : ℕ) : ℝ) + A)
    ⟨by linarith [h.A_pos], le_rfl⟩
  refine not_differentiableAt_of_kink (a := β ^ m * c₁) (b := β ^ (m + 1) * p) ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds
      (show ((m + 1 : ℕ) : ℝ) < (m + 1 : ℕ) + A by linarith [h.A_pos]))] with u (hu : u ≤ _) hu'
    rw [wSS_left_piece h hν ⟨hu'.le, hu⟩, hw]
    try simp only [Nat.add_sub_cancel]
    ring
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
      (show ((m + 1 : ℕ) : ℝ) + A < (m + 1 : ℕ) + 1 by linarith [h.A_lt]))] with
      u (hu : _ ≤ u) hu'
    rw [wSS_right_piece h hν ⟨hu, hu'.le⟩, hw]
    try simp only [Nat.add_sub_cancel]
    have hc := cross_eq h (Aind p c₀ c₁ β N)
    rw [sub_self, mul_zero] at hc
    rw [pow_succ]
    nlinarith [hc]
  · intro he
    rw [pow_succ, mul_assoc] at he
    have := mul_left_cancel₀ hb.ne' he
    linarith [h.inv.margin]

/-! ### Exercise 5.14e–g -/

/-- `φ(u) = −c₁u + βw(u)`. -/
noncomputable def phiSS (p c₀ c₁ β : ℝ) (N : ℕ) (u : ℝ) : ℝ := -(c₁ * u) + β * wSS p c₀ c₁ β N u

/-- `φ` is convex on each cell `[ν, ν + 1]`, `ν ≥ 1`: an affine function plus a nonnegative
multiple of the maximum of two affine functions. -/
theorem phi_cell_convex (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) :
    ConvexOn ℝ (Icc (ν : ℝ) (ν + 1)) (phiSS p c₀ c₁ β N) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hmem : a • x + b • y ∈ Icc (ν : ℝ) (ν + 1) := convex_Icc _ _ hx hy ha hb hab
  simp only [phiSS]
  rw [wSS_cell h hν hmem, wSS_cell h hν hx, wSS_cell h hν hy]
  simp only [smul_eq_mul, cellW]
  set Y := Yn p c₀ c₁ β N
  set q := β ^ (ν - 1)
  have hq : 0 ≤ q := pow_nonneg h.inv.β_pos.le _
  have hb' : b = 1 - a := by linarith
  subst hb'
  -- the maximum of affine functions is convex
  have hmax : max (c₁ * (a * x + (1 - a) * y - ν) + Y) (β * (p * (a * x + (1 - a) * y - ν) + Y))
      ≤ a * max (c₁ * (x - ν) + Y) (β * (p * (x - ν) + Y)) +
        (1 - a) * max (c₁ * (y - ν) + Y) (β * (p * (y - ν) + Y)) := by
    refine max_le ?_ ?_
    · have := mul_le_mul_of_nonneg_left (le_max_left (c₁ * (x - ν) + Y)
        (β * (p * (x - ν) + Y))) ha
      have := mul_le_mul_of_nonneg_left (le_max_left (c₁ * (y - ν) + Y)
        (β * (p * (y - ν) + Y))) hb
      nlinarith
    · have := mul_le_mul_of_nonneg_left (le_max_right (c₁ * (x - ν) + Y)
        (β * (p * (x - ν) + Y))) ha
      have := mul_le_mul_of_nonneg_left (le_max_right (c₁ * (y - ν) + Y)
        (β * (p * (y - ν) + Y))) hb
      nlinarith
  have := mul_le_mul_of_nonneg_left hmax (mul_nonneg h.inv.β_pos.le hq)
  nlinarith

/-- **Exercise 5.14e.** For `u > z ≥ 0`, either `φ(u) ≤ φ(z)` or `φ(u) ≤ φ(n)` for an integer
`n > z`: an order is beaten by not ordering (the supremum approached as `y ↓ 0`) or by an order
that brings the stock to an integer. -/
theorem ex_5_14e (h : SSHyp p c₀ c₁ β N) {z u : ℝ} (hz : 0 ≤ z) (hzu : z < u) :
    phiSS p c₀ c₁ β N u ≤ phiSS p c₀ c₁ β N z ∨
      ∃ n : ℕ, z < n ∧ phiSS p c₀ c₁ β N u ≤ phiSS p c₀ c₁ β N n := by
  set m := ⌊u⌋₊
  have hu0 : 0 ≤ u := by linarith
  have hmu : (m : ℝ) ≤ u := Nat.floor_le hu0
  have hum : u < m + 1 := Nat.lt_floor_add_one u
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- on `[0, 1]`, `φ` increases (slope `βp − c₁ > 0`)
    rw [hm0, Nat.cast_zero, zero_add] at hum
    right
    refine ⟨1, by push_cast; linarith, ?_⟩
    simp only [phiSS, Nat.cast_one]
    rw [wSS_low hum.le, wSS_low le_rfl]
    nlinarith [h.inv.margin]
  · have hconv := phi_cell_convex h (ν := m) hmpos
    have hm1 : ((m + 1 : ℕ) : ℝ) = m + 1 := by push_cast; ring
    have hmm : (m : ℝ) ∈ Icc (m : ℝ) (m + 1) := ⟨le_rfl, by linarith⟩
    have hm1m : (m : ℝ) + 1 ∈ Icc (m : ℝ) (m + 1) := ⟨by linarith, le_rfl⟩
    rcases le_total z m with hzm | hmz
    · -- `u ∈ [m, m + 1]`: the larger end value bounds `φ(u)`
      have hle := hconv.le_max_of_mem_Icc (x := (m : ℝ)) (y := (m : ℝ) + 1) (z := u)
        hmm hm1m ⟨hmu, hum.le⟩
      rcases le_total (phiSS p c₀ c₁ β N m) (phiSS p c₀ c₁ β N (m + 1)) with h1 | h1
      · right
        refine ⟨m + 1, by rw [hm1]; linarith, ?_⟩
        rw [hm1]
        exact hle.trans (max_le h1 le_rfl)
      · rcases eq_or_lt_of_le hzm with hzm' | hzm'
        · left
          rw [hzm']
          exact hle.trans (max_le le_rfl h1)
        · right
          exact ⟨m, hzm', hle.trans (max_le le_rfl h1)⟩
    · have hzI : z ∈ Icc (m : ℝ) (m + 1) := ⟨hmz, by linarith⟩
      have hle := hconv.le_max_of_mem_Icc (x := z) (y := (m : ℝ) + 1) (z := u)
        hzI hm1m ⟨hzu.le, hum.le⟩
      rcases le_total (phiSS p c₀ c₁ β N z) (phiSS p c₀ c₁ β N (m + 1)) with h1 | h1
      · right
        refine ⟨m + 1, by rw [hm1]; linarith, ?_⟩
        rw [hm1]
        exact hle.trans (max_le h1 le_rfl)
      · left
        exact hle.trans (max_le le_rfl h1)

/-- `w(n) = p(1 − βⁿ)/(1 − β) + β^{n−1}Y` at integers `n ≥ 1`. -/
theorem wSS_int (h : SSHyp p c₀ c₁ β N) {n : ℕ} (hn : 1 ≤ n) :
    wSS p c₀ c₁ β N n = p * (1 - β ^ n) / (1 - β) + β ^ (n - 1) * Yn p c₀ c₁ β N := by
  rw [wSS_left_piece h hn ⟨le_rfl, by linarith [h.A_pos]⟩]
  simp

/-- **Exercise 5.14f.** Ordering up to the integer `n ≥ 1` from `z` is worth
`−c₀ − c₁(n − z) + βw(n) = c₁z + r_n + βⁿY`. -/
theorem ex_5_14f (h : SSHyp p c₀ c₁ β N) (z : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    -c₀ - c₁ * (n - z) + β * wSS p c₀ c₁ β N n =
      c₁ * z + rn p c₀ c₁ β n + β ^ n * Yn p c₀ c₁ β N := by
  rw [wSS_int h hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [rn, Nat.add_sub_cancel, pow_succ]
  have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
  field_simp
  ring

/-- **Exercise 5.14g.** `r_n + βⁿY_N ≤ Y_N` for every `n ≥ 1`, with equality at `n = N`. -/
theorem ex_5_14g (h : SSHyp p c₀ c₁ β N) :
    (∀ n, 1 ≤ n → rn p c₀ c₁ β n + β ^ n * Yn p c₀ c₁ β N ≤ Yn p c₀ c₁ β N) ∧
      rn p c₀ c₁ β N + β ^ N * Yn p c₀ c₁ β N = Yn p c₀ c₁ β N := by
  have hr : ∀ n, 1 ≤ n → rn p c₀ c₁ β n = (1 - β ^ n) * Yn p c₀ c₁ β n := fun n hn => by
    have := one_sub_pow_pos h.inv hn
    simp only [Yn]; field_simp
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [hr n hn]
    have := mul_le_mul_of_nonneg_left (h.N_max n hn) (one_sub_pow_pos h.inv hn).le
    linarith
  · rw [hr N h.N_pos]; ring

/-- **The key step of Exercise 5.14h.** For `z ≥ 1` and an integer `n > z`,
`βw(z) > c₁z + r_n + βⁿY`: with `z = ν + α` and `n = ν + k` the difference is at least
`β^ν(1 − β^k)(Y_N − Y_k) + (1 − β^ν)(c₀ + c₁(k − α)) > 0`. -/
theorem key_ineq (h : SSHyp p c₀ c₁ β N) {z : ℝ} (hz : 1 ≤ z) {n : ℕ} (hn : z < n) :
    c₁ * z + rn p c₀ c₁ β n + β ^ n * Yn p c₀ c₁ β N < β * wSS p c₀ c₁ β N z := by
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = ⌊z⌋₊ := ⟨_, rfl⟩
  have hν : 1 ≤ ν := hνdef ▸ Nat.le_floor (by exact_mod_cast hz)
  have hνz : (ν : ℝ) ≤ z := hνdef ▸ Nat.floor_le (by linarith)
  have hzν : z < ν + 1 := hνdef ▸ Nat.lt_floor_add_one z
  have hk : ν + 1 ≤ n := by
    have : (ν : ℝ) < n := lt_of_le_of_lt hνz hn
    exact_mod_cast this
  obtain ⟨k, hk', rfl⟩ : ∃ k, 1 ≤ k ∧ n = ν + k := ⟨n - ν, by omega, by omega⟩
  have hcell := wSS_cell h hν ⟨hνz, hzν.le⟩
  clear hνdef
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  set Y := Yn p c₀ c₁ β N
  have hw : p * (1 - β ^ (m + 1)) / (1 - β) + β ^ m * (c₁ * (z - ((m + 1 : ℕ) : ℝ)) + Y) ≤
      wSS p c₀ c₁ β N z := by
    rw [hcell, cellW, Nat.add_sub_cancel]
    have := le_max_left (c₁ * (z - ((m + 1 : ℕ) : ℝ)) + Y) (β * (p * (z - ((m + 1 : ℕ) : ℝ)) + Y))
    nlinarith [pow_nonneg h.inv.β_pos.le m]
  have hYk : rn p c₀ c₁ β k ≤ (1 - β ^ k) * Y := by
    have := mul_le_mul_of_nonneg_left (h.N_max k hk') (one_sub_pow_pos h.inv hk').le
    have e : rn p c₀ c₁ β k = (1 - β ^ k) * Yn p c₀ c₁ β k := by
      have := one_sub_pow_pos h.inv hk'
      simp only [Yn]; field_simp
    rw [e]; exact this
  have hα : z - ((m + 1 : ℕ) : ℝ) < k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk'
    push_cast at hzν ⊢; linarith
  have hbpos := pow_pos h.inv.β_pos (m + 1)
  have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
  have hexp : β * (p * (1 - β ^ (m + 1)) / (1 - β) + β ^ m * (c₁ * (z - ((m + 1 : ℕ) : ℝ)) + Y)) -
      (c₁ * z + rn p c₀ c₁ β (m + 1 + k) + β ^ (m + 1 + k) * Y) =
      β ^ (m + 1) * ((1 - β ^ k) * Y - rn p c₀ c₁ β k) +
        (1 - β ^ (m + 1)) * (c₀ + c₁ * (k - (z - ((m + 1 : ℕ) : ℝ)))) := by
    simp only [rn, pow_add, pow_succ]
    push_cast
    field_simp
    ring
  have hfirst : 0 ≤ β ^ (m + 1) * ((1 - β ^ k) * Y - rn p c₀ c₁ β k) :=
    mul_nonneg hbpos.le (by linarith)
  have hlt1 : β ^ (m + 1) < 1 := pow_lt_one₀ h.inv.β_pos.le h.inv.β_lt (by omega)
  have hsecond : 0 < (1 - β ^ (m + 1)) * (c₀ + c₁ * (k - (z - ((m + 1 : ℕ) : ℝ)))) :=
    mul_pos (by linarith) (by nlinarith [h.inv.c₀_pos, h.inv.c₁_pos])
  have := mul_le_mul_of_nonneg_left hw h.inv.β_pos.le
  linarith

/-! ### Exercise 5.14h: the conjecture solves (1) -/

/-- `w` as a bounded continuous function on `ℝ₊`. -/
noncomputable def wBCF (h : SSHyp p c₀ c₁ β N) : Stock →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => wSS p c₀ c₁ β N x.1)
    ((continuousOn_wSS h).comp_continuous continuous_subtype_val fun x => x.2)
    (p / (1 - β) + p + Yn p c₀ c₁ β N) fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (wSS_bounds h x.2.out).1]
      exact (wSS_bounds h x.2.out).2

theorem sext_wBCF (h : SSHyp p c₀ c₁ β N) {x : ℝ} (hx : 0 ≤ x) :
    sext (wBCF h) x = wSS p c₀ c₁ β N x := by
  rw [sext_of_nonneg _ hx]; rfl

/-- The value of an order `y > 0` from `z`, in terms of `φ`. -/
theorem orderVal_wBCF (h : SSHyp p c₀ c₁ β N) {z y : ℝ} (hz : 0 ≤ z) (hy : 0 < y) :
    orderVal c₀ c₁ β (wBCF h) z y = -c₀ + c₁ * z + phiSS p c₀ c₁ β N (z + y) := by
  simp only [orderVal, phiSS, sext_wBCF h (by linarith : 0 ≤ z + y)]
  ring

/-- Every order from `z ≥ 0` is worth at most not ordering minus `c₀`, or some integer
order. -/
theorem order_le (h : SSHyp p c₀ c₁ β N) {z y : ℝ} (hz : 0 ≤ z) (hy : 0 < y) :
    orderVal c₀ c₁ β (wBCF h) z y ≤ -c₀ + β * wSS p c₀ c₁ β N z ∨
      ∃ n : ℕ, z < n ∧ orderVal c₀ c₁ β (wBCF h) z y ≤
        c₁ * z + rn p c₀ c₁ β n + β ^ n * Yn p c₀ c₁ β N := by
  rw [orderVal_wBCF h hz hy]
  rcases ex_5_14e h hz (by linarith : z < z + y) with h1 | ⟨n, hn, h1⟩
  · left; simp only [phiSS] at h1 ⊢; linarith
  · right
    have hn1 : 1 ≤ n := by
      have : (0 : ℝ) < n := lt_of_le_of_lt hz hn
      exact_mod_cast this
    refine ⟨n, hn, ?_⟩
    rw [← ex_5_14f h z hn1]
    simp only [phiSS] at h1 ⊢
    linarith

/-- An integer order is available whenever `n > z`. -/
theorem order_int (h : SSHyp p c₀ c₁ β N) {z : ℝ} (hz : 0 ≤ z) {n : ℕ} (hn : z < n) :
    c₁ * z + rn p c₀ c₁ β n + β ^ n * Yn p c₀ c₁ β N ≤ ordSup c₀ c₁ β (wBCF h) z := by
  have hn1 : 1 ≤ n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt hz hn
    exact_mod_cast this
  refine le_trans (le_of_eq ?_) (le_csSup (bddAbove_ordSup h.inv (wBCF h) z)
    ⟨n - z, by simp only [Set.mem_Ioi]; linarith, rfl⟩)
  rw [orderVal, sext_wBCF h (by linarith), show z + (n - z) = n by ring, ← ex_5_14f h z hn1]

/-- **Exercise 5.14h.** `w` satisfies the functional equation (1) at every `x ≥ 0`. -/
theorem ex_5_14h (h : SSHyp p c₀ c₁ β N) (x : Stock) :
    invRHS p c₀ c₁ β (wBCF h) x = wBCF h x := by
  have hx := x.2.out
  have hY := h.Y_pos
  obtain ⟨hg, hgN⟩ := ex_5_14g h
  change p * min x.1 1 + max (β * sext (wBCF h) (leftover x.1))
    (ordSup c₀ c₁ β (wBCF h) (leftover x.1)) = wSS p c₀ c₁ β N x.1
  have hz0 : 0 ≤ leftover x.1 := le_max_right _ _
  rw [sext_wBCF h hz0]
  rcases le_or_gt x.1 1 with hx1 | hx1
  · -- `x ≤ 1`: order `N`, worth `Y`
    have hz : leftover x.1 = 0 := max_eq_right (by linarith)
    rw [hz, wSS_low (by norm_num : (0 : ℝ) ≤ 1), wSS_low hx1, min_eq_left hx1]
    have hlow := order_int h (le_refl 0) (n := N) (by exact_mod_cast h.N_pos)
    have hlow' : Yn p c₀ c₁ β N ≤ ordSup c₀ c₁ β (wBCF h) 0 := by linarith [hgN]
    have hup : ordSup c₀ c₁ β (wBCF h) 0 ≤ Yn p c₀ c₁ β N := by
      refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      rcases order_le h (z := 0) le_rfl hy with h1 | ⟨n, hn, h1⟩
      · rw [wSS_low (by norm_num : (0 : ℝ) ≤ 1)] at h1
        nlinarith [h.inv.c₀_pos, h.inv.β_lt]
      · have hn1 : 1 ≤ n := by exact_mod_cast hn
        linarith [hg n hn1]
    rw [le_antisymm hup hlow', max_eq_right]
    nlinarith [h.inv.β_lt]
  rcases lt_or_ge x.1 2 with hx2 | hx2
  · -- `1 < x < 2`: compare not ordering with ordering up to `N`
    have hz : leftover x.1 = x.1 - 1 := max_eq_left (by linarith)
    rw [hz, min_eq_right hx1.le, mul_one, wSS_one_two h ⟨hx1.le, hx2.le⟩]
    have hlow := order_int h (by linarith : (0 : ℝ) ≤ x.1 - 1) (n := N)
      (by have : (1 : ℝ) ≤ N := by exact_mod_cast h.N_pos
          linarith)
    have hlow' : c₁ * (x.1 - 1) + Yn p c₀ c₁ β N ≤ ordSup c₀ c₁ β (wBCF h) (x.1 - 1) := by
      linarith [hgN]
    have hup : ordSup c₀ c₁ β (wBCF h) (x.1 - 1) ≤
        max (β * wSS p c₀ c₁ β N (x.1 - 1)) (c₁ * (x.1 - 1) + Yn p c₀ c₁ β N) := by
      refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      rcases order_le h (z := x.1 - 1) (by linarith) hy with h1 | ⟨n, hn, h1⟩
      · exact (h1.trans (by linarith [h.inv.c₀_pos])).trans (le_max_left _ _)
      · have hn1 : 1 ≤ n := by
          have : (0 : ℝ) < n := lt_of_le_of_lt (by linarith) hn
          exact_mod_cast this
        exact (h1.trans (by linarith [hg n hn1])).trans (le_max_right _ _)
    rw [max_comm (c₁ * (x.1 - 1) + _)]
    congr 1
    refine le_antisymm (max_le (le_max_left _ _) hup) (max_le (le_max_left _ _) ?_)
    exact hlow'.trans (le_max_right _ _)
  · -- `x ≥ 2`: not ordering is optimal (`key_ineq`)
    have hz : leftover x.1 = x.1 - 1 := max_eq_left (by linarith)
    rw [hz, min_eq_right (by linarith), mul_one, wSS_five h hx2]
    have hup : ordSup c₀ c₁ β (wBCF h) (x.1 - 1) ≤ β * wSS p c₀ c₁ β N (x.1 - 1) := by
      refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      rcases order_le h (z := x.1 - 1) (by linarith) hy with h1 | ⟨n, hn, h1⟩
      · linarith [h.inv.c₀_pos]
      · exact h1.trans (key_ineq h (by linarith) hn).le
    rw [max_eq_left hup]

/-- **Exercise 5.14h.** The solution of (1) is `w`: the (s, S) conjecture is correct. -/
theorem ex_5_14_value (h : SSHyp p c₀ c₁ β N) {v : Stock →ᵇ ℝ}
    (hv : ∀ x, v x = invRHS p c₀ c₁ β v x) : v = wBCF h := by
  obtain ⟨v₀, -, huniq, -⟩ := ex_5_14a h.inv
  rw [huniq v hv, huniq (wBCF h) fun x => (ex_5_14h h x).symm]

/-- **The (s, S) policy.** With `s = 1 + A` and `S = N`: below `s` it is strictly optimal to order
up to `N` (from stock `z` left after sales, order `N − z`); above `s` not ordering is optimal;
at `x = s` ordering up to `N` and not ordering are both optimal, so the optimal policy is not
unique. -/
theorem ex_5_14_policy (h : SSHyp p c₀ c₁ β N) :
    (∀ x : Stock, x.1 < 1 + Aind p c₀ c₁ β N →
      β * sext (wBCF h) (leftover x.1) < orderVal c₀ c₁ β (wBCF h) (leftover x.1)
        (N - leftover x.1) ∧
      orderVal c₀ c₁ β (wBCF h) (leftover x.1) (N - leftover x.1) =
        ordSup c₀ c₁ β (wBCF h) (leftover x.1)) ∧
    (∀ x : Stock, 1 + Aind p c₀ c₁ β N ≤ x.1 →
      ordSup c₀ c₁ β (wBCF h) (leftover x.1) ≤ β * sext (wBCF h) (leftover x.1)) ∧
    (∀ x : Stock, x.1 = 1 + Aind p c₀ c₁ β N →
      orderVal c₀ c₁ β (wBCF h) (leftover x.1) (N - leftover x.1) =
        β * sext (wBCF h) (leftover x.1)) := by
  have hA0 := h.A_pos
  have hA1 := h.A_lt
  have hY := h.Y_pos
  obtain ⟨hg, hgN⟩ := ex_5_14g h
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.N_pos
  -- the order up to `N` from `z < 1` is worth `c₁z + Y`
  have hvalN : ∀ z : ℝ, 0 ≤ z → z < 1 →
      orderVal c₀ c₁ β (wBCF h) z (N - z) = c₁ * z + Yn p c₀ c₁ β N := fun z hz hz1 => by
    rw [orderVal, sext_wBCF h (by linarith), show z + (N - z) = (N : ℝ) by ring,
      ex_5_14f h z h.N_pos]
    linarith [hgN]
  -- for `z < 1` the supremum is `max{βw(z) − c₀, c₁z + Y}` at most, and `c₁z + Y` at least
  have hsup : ∀ z : ℝ, 0 ≤ z → z < 1 → ordSup c₀ c₁ β (wBCF h) z ≤
      max (-c₀ + β * wSS p c₀ c₁ β N z) (c₁ * z + Yn p c₀ c₁ β N) := fun z hz hz1 => by
    refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases order_le h hz hy with h1 | ⟨n, hn, h1⟩
    · exact h1.trans (le_max_left _ _)
    · have hn1 : 1 ≤ n := by
        have : (0 : ℝ) < n := lt_of_le_of_lt hz hn
        exact_mod_cast this
      exact (h1.trans (by linarith [hg n hn1])).trans (le_max_right _ _)
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have hz0 : 0 ≤ leftover x.1 := le_max_right _ _
    have hz1 : leftover x.1 < Aind p c₀ c₁ β N := by
      unfold leftover; exact max_lt (by linarith) hA0
    rw [sext_wBCF h hz0, hvalN _ hz0 (by linarith),
      wSS_low (by linarith : leftover x.1 ≤ 1)]
    have hc := cross_eq h (leftover x.1)
    have hlt : β * (p * leftover x.1 + Yn p c₀ c₁ β N) < c₁ * leftover x.1 + Yn p c₀ c₁ β N := by
      nlinarith [h.inv.margin]
    refine ⟨hlt, le_antisymm ?_ ?_⟩
    · have := order_int h hz0 (n := N) (by linarith)
      linarith [hgN]
    · refine (hsup _ hz0 (by linarith)).trans (max_le ?_ le_rfl)
      rw [wSS_low (by linarith : leftover x.1 ≤ 1)]
      linarith [h.inv.c₀_pos]
  · have hz : leftover x.1 = x.1 - 1 := max_eq_left (by linarith)
    rw [hz, sext_wBCF h (by linarith)]
    rcases lt_or_ge x.1 2 with hx2 | hx2
    · refine (hsup _ (by linarith) (by linarith)).trans (max_le (by linarith [h.inv.c₀_pos]) ?_)
      rw [wSS_low (by linarith : x.1 - 1 ≤ 1)]
      exact (cross_iff h _).2 (by linarith)
    · refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      rcases order_le h (z := x.1 - 1) (by linarith) hy with h1 | ⟨n, hn, h1⟩
      · linarith [h.inv.c₀_pos]
      · exact h1.trans (key_ineq h (by linarith) hn).le
  · have hz : leftover x.1 = Aind p c₀ c₁ β N := by
      unfold leftover; rw [hx]; simp [hA0.le]
    rw [hz, hvalN _ hA0.le hA1, sext_wBCF h hA0.le, wSS_low hA1.le]
    have := cross_eq h (Aind p c₀ c₁ β N)
    simp only [sub_self, mul_zero] at this
    linarith

end StokeyLucasPrescott.DeterministicApplications
