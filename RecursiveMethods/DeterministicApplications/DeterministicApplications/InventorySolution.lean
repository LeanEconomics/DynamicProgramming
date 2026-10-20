/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.Inventory

/-!
# The (s, S) policy: the value function

SLP Exercise 5.14d–h, pp. 120–122. Let `N ≥ 1` maximize `Y_n`, with `Y = Y_N > 0`, and
`A = (1 − β)Y/(βp − c₁) ∈ (0, 1)`.

* `cellW`: on the cell `[ν, ν + 1]` (`ν ≥ 1`), with `α = u − ν`,
  `w(u) = p(1 − β^ν)/(1 − β) + β^{ν−1} max{c₁α + Y, β(pα + Y)}` (`wSS_cell`); the maximum picks
  `c₁α + Y` exactly when `α ≤ A` (`cross_iff`). This is the book's (6) (`wSS_six`), and holds on
  the closed cell because `A < 1`.
* **Exercise 5.14d**: `wSS` solves the difference equations (2), (3) and (5)
  (`wSS_two`, `wSS_three_left`, `wSS_three_right`, `wSS_five`); it is continuous on `ℝ₊`
  (`continuousOn_wSS`), bounded (`wSS_bounds`) and piecewise linear.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {p c₀ c₁ β : ℝ} {N : ℕ}

/-- The hypotheses of Exercise 5.14d–h: `N` maximizes `Y_n` and `Y_N > 0`. -/
structure SSHyp (p c₀ c₁ β : ℝ) (N : ℕ) : Prop where
  inv : InvHyp p c₀ c₁ β
  N_pos : 1 ≤ N
  N_max : ∀ n, 1 ≤ n → Yn p c₀ c₁ β n ≤ Yn p c₀ c₁ β N
  Y_pos : 0 < Yn p c₀ c₁ β N

/-- The indifference point `A = (1 − β)Y_N/(βp − c₁)`. -/
noncomputable def Aind (p c₀ c₁ β : ℝ) (N : ℕ) : ℝ := (1 - β) * Yn p c₀ c₁ β N / (β * p - c₁)

/-- `w` on the cell `[ν, ν + 1]`. -/
noncomputable def cellW (p c₀ c₁ β : ℝ) (N ν : ℕ) (u : ℝ) : ℝ :=
  p * (1 - β ^ ν) / (1 - β) +
    β ^ (ν - 1) * max (c₁ * (u - ν) + Yn p c₀ c₁ β N) (β * (p * (u - ν) + Yn p c₀ c₁ β N))

/-- The conjectured value function (2), (3), (5), in the closed form (6). -/
noncomputable def wSS (p c₀ c₁ β : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  if x ≤ 1 then p * x + Yn p c₀ c₁ β N else cellW p c₀ c₁ β N ⌊x⌋₊ x

theorem SSHyp.A_pos (h : SSHyp p c₀ c₁ β N) : 0 < Aind p c₀ c₁ β N :=
  (ex_5_14c h.inv h.N_pos h.Y_pos).1

theorem SSHyp.A_lt (h : SSHyp p c₀ c₁ β N) : Aind p c₀ c₁ β N < 1 :=
  (ex_5_14c h.inv h.N_pos h.Y_pos).2

/-- `c₁a + Y ≤ β(pa + Y)` iff `A ≤ a`: the two branches cross at `A`. -/
theorem cross_iff (h : SSHyp p c₀ c₁ β N) (a : ℝ) :
    c₁ * a + Yn p c₀ c₁ β N ≤ β * (p * a + Yn p c₀ c₁ β N) ↔ Aind p c₀ c₁ β N ≤ a := by
  have hm : 0 < β * p - c₁ := by linarith [h.inv.margin]
  unfold Aind
  rw [div_le_iff₀ hm]
  constructor <;> intro hh <;> nlinarith

theorem cross_one (h : SSHyp p c₀ c₁ β N) :
    max (c₁ * 1 + Yn p c₀ c₁ β N) (β * (p * 1 + Yn p c₀ c₁ β N)) =
      β * (p * 1 + Yn p c₀ c₁ β N) :=
  max_eq_right ((cross_iff h 1).2 h.A_lt.le)

theorem cross_zero (h : SSHyp p c₀ c₁ β N) :
    max (c₁ * 0 + Yn p c₀ c₁ β N) (β * (p * 0 + Yn p c₀ c₁ β N)) = Yn p c₀ c₁ β N := by
  simp only [mul_zero, zero_add]
  exact max_eq_left (mul_le_of_le_one_left h.Y_pos.le h.inv.β_lt.le)

/-- On the closed cell `[ν, ν + 1]`, `ν ≥ 1`, `w = cellW ν`. -/
theorem wSS_cell (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) {u : ℝ}
    (hu : u ∈ Icc (ν : ℝ) (ν + 1)) : wSS p c₀ c₁ β N u = cellW p c₀ c₁ β N ν u := by
  have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  push_cast at hu
  rcases eq_or_lt_of_le hu.2 with htop | hlt
  · -- the right end `u = m + 2`
    have hfl : ⌊u⌋₊ = m + 2 := by
      rw [htop]; exact_mod_cast Nat.floor_natCast (m + 2) |>.trans rfl
    have hu1 : ¬ u ≤ 1 := by rw [htop]; push Not; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    simp only [wSS, hu1, ↓reduceIte, hfl, cellW]
    have e1 : u - ((m + 2 : ℕ) : ℝ) = 0 := by rw [htop]; push_cast; ring
    have e2 : u - ((m + 1 : ℕ) : ℝ) = 1 := by rw [htop]; push_cast; ring
    rw [e1, e2, cross_zero h, cross_one h]
    simp only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega, pow_succ]
    field_simp
    ring
  · rcases eq_or_lt_of_le hu.1 with hbot | hgt
    · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- `u = 1`
        subst hm0
        have hu1 : u = 1 := by rw [← hbot]; norm_num
        subst hu1
        simp only [wSS, le_refl, ↓reduceIte, cellW]
        rw [show (1 : ℝ) - ((0 + 1 : ℕ) : ℝ) = 0 by norm_num, cross_zero h]
        simp only [pow_one, zero_add, Nat.sub_self, pow_zero, one_mul, mul_one]
        field_simp
      · have hu1 : ¬ u ≤ 1 := by
          push Not
          have : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
          linarith
        have hfl : ⌊u⌋₊ = m + 1 := (Nat.floor_eq_iff (by linarith)).2 ⟨by push_cast; linarith,
          by push_cast; linarith⟩
        simp only [wSS, hu1, ↓reduceIte, hfl]
    · have hu1 : ¬ u ≤ 1 := by
        push Not
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      have hfl : ⌊u⌋₊ = m + 1 :=
        (Nat.floor_eq_iff (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])).2
          ⟨by push_cast; linarith, by push_cast; linarith⟩
      simp only [wSS, hu1, ↓reduceIte, hfl]

theorem wSS_low {x : ℝ} (hx : x ≤ 1) : wSS p c₀ c₁ β N x = p * x + Yn p c₀ c₁ β N := by
  simp only [wSS, hx, ↓reduceIte]

/-- **Exercise 5.14d, (2).** `w(x) = px + Y` on `[0, 1]`. -/
theorem wSS_two (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : wSS p c₀ c₁ β N x = p * x + Yn p c₀ c₁ β N :=
  wSS_low hx.2

/-- On `[1, 2]`, `w(x) = p + max{c₁(x − 1) + Y, βw(x − 1)}`. -/
theorem wSS_one_two (h : SSHyp p c₀ c₁ β N) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    wSS p c₀ c₁ β N x = p + max (c₁ * (x - 1) + Yn p c₀ c₁ β N)
      (β * wSS p c₀ c₁ β N (x - 1)) := by
  have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
  rw [wSS_cell h le_rfl (by push_cast; exact ⟨hx.1, by linarith [hx.2]⟩),
    wSS_low (by linarith [hx.2] : x - 1 ≤ 1)]
  simp only [cellW, Nat.cast_one, pow_one, Nat.sub_self, pow_zero, one_mul]
  congr 1
  field_simp

/-- **Exercise 5.14d, (3).** On `(1, 1 + A)`, `w(x) = p + c₁(x − 1) + Y`. -/
theorem wSS_three_left (h : SSHyp p c₀ c₁ β N) {x : ℝ}
    (hx : x ∈ Ioo (1 : ℝ) (1 + Aind p c₀ c₁ β N)) :
    wSS p c₀ c₁ β N x = p + c₁ * (x - 1) + Yn p c₀ c₁ β N := by
  rw [wSS_one_two h ⟨hx.1.le, by linarith [hx.2, h.A_lt]⟩,
    wSS_low (show x - 1 ≤ 1 by linarith [hx.2, h.A_lt])]
  rw [max_eq_left]
  · ring
  · have := (cross_iff h (x - 1)).not.2 (by push Not; linarith [hx.2])
    push Not at this
    exact this.le

/-- **Exercise 5.14d, (3).** On `[1 + A, 2]`, `w(x) = p + βw(x − 1)`. -/
theorem wSS_three_right (h : SSHyp p c₀ c₁ β N) {x : ℝ}
    (hx : x ∈ Icc (1 + Aind p c₀ c₁ β N) 2) :
    wSS p c₀ c₁ β N x = p + β * wSS p c₀ c₁ β N (x - 1) := by
  rw [wSS_one_two h ⟨by linarith [hx.1, h.A_pos], hx.2⟩]
  rw [wSS_low (by linarith [hx.2] : x - 1 ≤ 1)]
  rw [max_eq_right ((cross_iff h (x - 1)).2 (by linarith [hx.1]))]

/-- **Exercise 5.14d, (5).** For `x ≥ 2`, `w(x) = p + βw(x − 1)`. -/
theorem wSS_five (h : SSHyp p c₀ c₁ β N) {x : ℝ} (hx : 2 ≤ x) :
    wSS p c₀ c₁ β N x = p + β * wSS p c₀ c₁ β N (x - 1) := by
  have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
  set ν := ⌊x⌋₊
  have hν2 : 2 ≤ ν := Nat.le_floor (by exact_mod_cast hx)
  have hνx : (ν : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxν : x < ν + 1 := Nat.lt_floor_add_one x
  obtain ⟨m, hm⟩ : ∃ m, ν = m + 2 := ⟨ν - 2, by omega⟩
  rw [wSS_cell h (ν := ν) (by omega) ⟨hνx, hxν.le⟩,
    wSS_cell h (ν := m + 1) (by omega) ⟨by rw [hm] at hνx; push_cast at hνx ⊢; linarith,
      by rw [hm] at hxν; push_cast at hxν ⊢; linarith⟩]
  simp only [cellW, hm]
  push_cast
  have e : x - (↑m + 1) - 1 = x - (↑m + 2) := by ring
  rw [show x - 1 - (↑m + 1) = x - (↑m + 2) by ring]
  simp only [pow_succ]
  field_simp
  ring

/-- **Exercise 5.14d, (6).** For `x > 1` with `ν = ⌊x⌋`, `α = x − ν`: below the indifference
point `w(x) = p(1 − β^ν)/(1 − β) + β^{ν−1}(c₁α + Y)`, above it
`w(x) = p(1 − β^ν)/(1 − β) + β^ν(pα + Y)`. -/
theorem wSS_six (h : SSHyp p c₀ c₁ β N) {x : ℝ} (hx : 1 < x) :
    (x - ⌊x⌋₊ < Aind p c₀ c₁ β N → wSS p c₀ c₁ β N x =
      p * (1 - β ^ ⌊x⌋₊) / (1 - β) + β ^ (⌊x⌋₊ - 1) * (c₁ * (x - ⌊x⌋₊) + Yn p c₀ c₁ β N)) ∧
    (Aind p c₀ c₁ β N ≤ x - ⌊x⌋₊ → wSS p c₀ c₁ β N x =
      p * (1 - β ^ ⌊x⌋₊) / (1 - β) + β ^ ⌊x⌋₊ * (p * (x - ⌊x⌋₊) + Yn p c₀ c₁ β N)) := by
  have hν : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx.le)
  have hcell := wSS_cell h hν ⟨Nat.floor_le (by linarith), (Nat.lt_floor_add_one x).le⟩
  refine ⟨fun hα => ?_, fun hα => ?_⟩
  · rw [hcell, cellW, max_eq_left]
    have := (cross_iff h (x - ⌊x⌋₊)).not.2 (by push Not; exact hα)
    push Not at this
    exact this.le
  · rw [hcell, cellW, max_eq_right ((cross_iff h _).2 hα)]
    obtain ⟨m, hm⟩ : ∃ m, ⌊x⌋₊ = m + 1 := ⟨⌊x⌋₊ - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, pow_succ]
    ring

/-! ### Continuity and bounds -/

theorem continuous_cellW (ν : ℕ) : Continuous (cellW p c₀ c₁ β N ν) := by
  unfold cellW
  fun_prop

/-- `w` is continuous on each cell `[n, n + 1]`. -/
theorem continuousOn_wSS_cell (h : SSHyp p c₀ c₁ β N) (n : ℕ) :
    ContinuousOn (wSS p c₀ c₁ β N) (Icc (n : ℝ) (n + 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (show Continuous (fun x : ℝ => p * x + Yn p c₀ c₁ β N) by
      fun_prop).continuousOn.congr fun x hx => ?_
    simp only [Nat.cast_zero, zero_add] at hx
    exact wSS_low hx.2
  · exact (continuous_cellW n).continuousOn.congr fun x hx => wSS_cell h hn hx

/-- **Exercise 5.14d.** `w` is continuous on `ℝ₊`. -/
theorem continuousOn_wSS (h : SSHyp p c₀ c₁ β N) : ContinuousOn (wSS p c₀ c₁ β N) (Ici 0) := by
  -- two adjacent cells cover a neighbourhood
  have hpair : ∀ n : ℕ, ContinuousOn (wSS p c₀ c₁ β N) (Icc (n : ℝ) (n + 2)) := fun n => by
    have := (continuousOn_wSS_cell h n).union_of_isClosed (continuousOn_wSS_cell h (n + 1))
      isClosed_Icc isClosed_Icc
    rwa [show ((n + 1 : ℕ) : ℝ) = n + 1 by push_cast; ring,
      show (n : ℝ) + 1 + 1 = n + 2 by ring, Icc_union_Icc_eq_Icc (by linarith)
        (by linarith)] at this
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := hx
  set m := ⌊x⌋₊
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hxm : x < m + 1 := Nat.lt_floor_add_one x
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have hc := hpair 0
    simp only [Nat.cast_zero, zero_add] at hc
    refine (hc x ⟨hx0, by rw [hm0] at hxm; push_cast at hxm; linarith⟩).mono_of_mem_nhdsWithin ?_
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by rw [hm0] at hxm; push_cast at hxm; linarith))
  · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hc := hpair k
    have hk' : (m : ℝ) = k + 1 := by rw [hk]; push_cast; ring
    refine (hc x ⟨by linarith, by linarith⟩).mono_of_mem_nhdsWithin
      (nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith)))

/-- **Exercise 5.14d.** `w` is bounded: `0 ≤ w ≤ p/(1 − β) + p + Y` on `ℝ₊`. -/
theorem wSS_bounds (h : SSHyp p c₀ c₁ β N) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ wSS p c₀ c₁ β N x ∧
      wSS p c₀ c₁ β N x ≤ p / (1 - β) + p + Yn p c₀ c₁ β N := by
  have hp := h.inv.p_pos
  have hY := h.Y_pos
  have h1β : 0 < 1 - β := by linarith [h.inv.β_lt]
  rcases le_or_gt x 1 with hx1 | hx1
  · rw [wSS_low hx1]
    have : 0 ≤ p / (1 - β) := div_nonneg hp.le h1β.le
    constructor <;> nlinarith
  · set ν := ⌊x⌋₊
    have hν : 1 ≤ ν := Nat.le_floor (by exact_mod_cast hx1.le)
    have hνx : (ν : ℝ) ≤ x := Nat.floor_le hx
    have hxν : x < ν + 1 := Nat.lt_floor_add_one x
    rw [wSS_cell h hν ⟨hνx, hxν.le⟩, cellW]
    have hpow : 0 ≤ β ^ ν := pow_nonneg h.inv.β_pos.le ν
    have hpow1 : β ^ ν ≤ 1 := pow_le_one₀ h.inv.β_pos.le h.inv.β_lt.le
    have hq0 : 0 ≤ β ^ (ν - 1) := pow_nonneg h.inv.β_pos.le _
    have hq1 : β ^ (ν - 1) ≤ 1 := pow_le_one₀ h.inv.β_pos.le h.inv.β_lt.le
    have hα0 : 0 ≤ x - ν := by linarith
    have hα1 : x - ν ≤ 1 := by linarith
    have hM0 : 0 ≤ max (c₁ * (x - ν) + Yn p c₀ c₁ β N) (β * (p * (x - ν) + Yn p c₀ c₁ β N)) :=
      le_max_of_le_left (by nlinarith [h.inv.c₁_pos])
    have hM1 : max (c₁ * (x - ν) + Yn p c₀ c₁ β N) (β * (p * (x - ν) + Yn p c₀ c₁ β N)) ≤
        p + Yn p c₀ c₁ β N := by
      have hpα : p * (x - ν) ≤ p := mul_le_of_le_one_right hp.le hα1
      have hpα0 : 0 ≤ p * (x - ν) := mul_nonneg hp.le hα0
      have hc₁p : c₁ ≤ p := by nlinarith [h.inv.margin, h.inv.β_lt, h.inv.β_pos]
      refine max_le ?_ ?_
      · nlinarith [h.inv.c₁_pos]
      · have := mul_le_of_le_one_left (by linarith : 0 ≤ p * (x - ν) + Yn p c₀ c₁ β N)
          h.inv.β_lt.le
        linarith
    have hA : 0 ≤ p * (1 - β ^ ν) / (1 - β) := div_nonneg (by nlinarith) h1β.le
    have hB : p * (1 - β ^ ν) / (1 - β) ≤ p / (1 - β) :=
      div_le_div_of_nonneg_right (by nlinarith) h1β.le
    constructor <;> nlinarith

end StokeyLucasPrescott.DeterministicApplications
