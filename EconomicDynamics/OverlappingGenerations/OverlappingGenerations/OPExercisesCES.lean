/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.OPExercises

/-!
# Exercise 16.5: the Diamond model with CES technology

Miao, §16.4, Exercise 16.5, pp. 556–557: `u = ln c` and
`f(k) = A[ak^ρ + 1 − a]^{1/ρ}` with `ρ = (σ − 1)/σ`, `σ` the elasticity of substitution.

* The derivative of `f`, the wage `w(k) = A(1 − a)[ak^ρ + 1 − a]^{1/ρ − 1}` and the law of
  motion `k_{t+1} = βw(k_t)/((1 + β)g_n)` (`opCES`, `ex_16_5_hasDerivAt`, `ex_16_5_wage`,
  `ex_16_5_law`).
* (a) `σ > 1` (`0 < ρ < 1`): a positive steady state exists (`ex_16_5_a`); `σ = 1` is
  Cobb–Douglas `Ak^a`, which has the positive steady state of Exercise 16.4
  (`ex_16_5_a_cobbDouglas`).
* (b) `σ < 1` (`ρ < 0`): `w(k) ≤ AMk` with `M` independent of `A` (`ex_16_5_b_bound`); for `A`
  small (`βAM < (1 + β)g_n`) there is no positive steady state (`ex_16_5_b_none`) and every
  path converges to `0` geometrically (`ex_16_5_b_collapse`); for `A` large
  (`βA(1 − a) > (1 + β)g_n`) there are at least two positive steady states, so uniqueness fails
  (`ex_16_5_b_two`).

Departure: the printed formula is undefined at `σ = 1` (exponent `σ/(σ − 1)`); "`σ = 1`
corresponds to Cobb–Douglas" is the limit `σ → 1`, so `σ = 1` is treated with `f = Ak^a`.
Not formalised: the stability of each steady state for `σ < 1` and an upper bound (two) on
their number.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- The CES aggregate `ak^ρ + 1 − a`. -/
noncomputable def opCESbase (a ρ k : ℝ) : ℝ := a * k ^ ρ + (1 - a)

/-- CES technology `f(k) = A[ak^ρ + 1 − a]^{1/ρ}`. -/
noncomputable def opCES (A a ρ k : ℝ) : ℝ := A * opCESbase a ρ k ^ (1 / ρ)

/-- Its derivative `f′(k) = Aak^{ρ−1}[ak^ρ + 1 − a]^{1/ρ − 1}`. -/
noncomputable def opCESfp (A a ρ k : ℝ) : ℝ :=
  A * a * k ^ (ρ - 1) * opCESbase a ρ k ^ (1 / ρ - 1)

/-- The CES wage `A(1 − a)[ak^ρ + 1 − a]^{1/ρ − 1}`. -/
noncomputable def opCESwage (A a ρ k : ℝ) : ℝ := A * (1 - a) * opCESbase a ρ k ^ (1 / ρ - 1)

theorem op_ces_base_pos {a ρ k : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hk : 0 < k) :
    0 < opCESbase a ρ k ∧ 1 - a ≤ opCESbase a ρ k ∧ a * k ^ ρ ≤ opCESbase a ρ k := by
  have := Real.rpow_pos_of_pos hk ρ
  unfold opCESbase
  refine ⟨by nlinarith, by nlinarith, by linarith⟩

/-- **Exercise 16.5**: `f′(k) = Aak^{ρ−1}[ak^ρ + 1 − a]^{1/ρ − 1}`. -/
theorem ex_16_5_hasDerivAt {A a ρ k : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hρ : ρ ≠ 0)
    (hk : 0 < k) : HasDerivAt (opCES A a ρ) (opCESfp A a ρ k) k := by
  have hb : HasDerivAt (opCESbase a ρ) (a * (ρ * k ^ (ρ - 1))) k := by
    unfold opCESbase
    exact ((Real.hasDerivAt_rpow_const (p := ρ) (Or.inl hk.ne')).const_mul a).add_const _
  have hr := (hb.rpow_const (p := 1 / ρ)
    (Or.inl (op_ces_base_pos ha0 ha1 hk).1.ne')).const_mul A
  unfold opCES opCESfp
  convert hr using 1
  field_simp

/-- **Exercise 16.5**: the CES wage `w(k) = f(k) − kf′(k) = A(1 − a)[ak^ρ + 1 − a]^{1/ρ − 1}`. -/
theorem ex_16_5_wage {A a ρ k : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hk : 0 < k) :
    opWage (opCES A a ρ) (opCESfp A a ρ) k = opCESwage A a ρ k := by
  have hb := (op_ces_base_pos (ρ := ρ) ha0 ha1 hk).1
  have e1 : opCESbase a ρ k ^ (1 / ρ) = opCESbase a ρ k ^ (1 / ρ - 1) * opCESbase a ρ k := by
    rw [Real.rpow_sub_one hb.ne']; field_simp
  unfold opWage opCES opCESfp opCESwage
  rw [e1, show k * (A * a * k ^ (ρ - 1) * opCESbase a ρ k ^ (1 / ρ - 1)) =
    A * a * (k * k ^ (ρ - 1)) * opCESbase a ρ k ^ (1 / ρ - 1) by ring, ← op_rpow_eq_mul hk]
  unfold opCESbase
  ring

/-- **Exercise 16.5**: with log utility the law of motion is `k_{t+1} = βw(k_t)/((1 + β)g_n)`. -/
theorem ex_16_5_law {β A a ρ gn : ℝ} {k : ℕ → ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    OPIsDiamondEqm (fun w R => opLogSaving β w 0 R) (opCES A a ρ) (opCESfp A a ρ) gn k ↔
      ∀ t, 0 < k t ∧ k (t + 1) = β / ((1 + β) * gn) * opCESwage A a ρ (k t) := by
  refine forall_congr' fun t => ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · rw [ex_16_5_wage ha0 ha1 h1] at h2
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)
  · rw [ex_16_5_wage ha0 ha1 h1]
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)

/-- The CES wage is continuous on `(0, ∞)`. -/
theorem op_ces_wage_continuousOn {A a ρ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ContinuousOn (opCESwage A a ρ) (Set.Ioi 0) := by
  have hb : ContinuousOn (opCESbase a ρ) (Set.Ioi 0) := by
    unfold opCESbase
    exact (continuousOn_const.mul (continuousOn_id.rpow_const fun x hx =>
      Or.inl (ne_of_gt hx))).add continuousOn_const
  unfold opCESwage
  exact continuousOn_const.mul (hb.rpow_const fun x hx =>
    Or.inl (op_ces_base_pos ha0 ha1 hx).1.ne')

/-- **Exercise 16.5(a)** (Miao, p. 557): for `σ > 1` (`0 < ρ < 1`) there is a positive steady
state `k = βw(k)/((1 + β)g_n)`. -/
theorem ex_16_5_a {β A a ρ gn : ℝ} (hβ : 0 < β) (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hgn : 0 < gn) :
    ∃ k, 0 < k ∧ k = β / ((1 + β) * gn) * opCESwage A a ρ k := by
  set c := β / ((1 + β) * gn) with hc
  have hc0 : 0 < c := by positivity
  have he : 0 < 1 / ρ - 1 := by
    have : 1 < 1 / ρ := by rw [lt_div_iff₀ hρ0]; linarith
    linarith
  have h1a : 0 < 1 - a := by linarith
  set W0 := A * (1 - a) * (1 - a) ^ (1 / ρ - 1) with hW0
  have hW00 : 0 < W0 := by have := Real.rpow_pos_of_pos h1a (1 / ρ - 1); positivity
  have hlow : ∀ k, 0 < k → W0 ≤ opCESwage A a ρ k := by
    intro k hk
    have hb := op_ces_base_pos (ρ := ρ) ha0 ha1 hk
    have := Real.rpow_le_rpow h1a.le hb.2.1 he.le
    unfold opCESwage
    rw [hW0]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hup : ∀ k, 1 ≤ k → opCESwage A a ρ k ≤ A * (1 - a) * (k / k ^ ρ) := by
    intro k hk
    have hk0 : 0 < k := by linarith
    have hb := op_ces_base_pos (ρ := ρ) ha0 ha1 hk0
    have hkρ : 1 ≤ k ^ ρ := Real.one_le_rpow hk hρ0.le
    have hbase : opCESbase a ρ k ≤ k ^ ρ := by unfold opCESbase; nlinarith
    have h1 := Real.rpow_le_rpow hb.1.le hbase he.le
    rw [← Real.rpow_mul hk0.le, show ρ * (1 / ρ - 1) = 1 - ρ by field_simp,
      Real.rpow_sub hk0, Real.rpow_one] at h1
    unfold opCESwage
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  set C := c * (A * (1 - a)) with hC
  have hC0 : 0 < C := by positivity
  set khi := max 1 ((C + 1) ^ ρ⁻¹) with hkhi
  have hkhi1 : 1 ≤ khi := le_max_left _ _
  have hkhi0 : 0 < khi := by linarith
  have hkhiρ : C + 1 ≤ khi ^ ρ := by
    have := Real.rpow_le_rpow (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < C + 1) _).le
      (le_max_right 1 ((C + 1) ^ ρ⁻¹)) hρ0.le
    rwa [Real.rpow_inv_rpow (by linarith) hρ0.ne'] at this
  have hφhi : c * opCESwage A a ρ khi < khi := by
    have h := mul_le_mul_of_nonneg_left (hup khi hkhi1) hc0.le
    have hkp : 0 < khi ^ ρ := by linarith
    have : C * (khi / khi ^ ρ) < khi := by
      rw [mul_div_assoc', div_lt_iff₀ hkp]; nlinarith
    rw [hC] at this
    linarith
  set klo := c * W0 / 2 with hklo
  have hklo0 : 0 < klo := by positivity
  have hφlo : klo < c * opCESwage A a ρ klo := by
    have := mul_le_mul_of_nonneg_left (hlow klo hklo0) hc0.le
    rw [hklo]; linarith
  set φ : ℝ → ℝ := fun k => c * opCESwage A a ρ k - k with hφ
  have hsub : Set.uIcc klo khi ⊆ Set.Ioi 0 := by
    intro x hx
    rcases Set.mem_uIcc.1 hx with h | h
    · exact lt_of_lt_of_le hklo0 h.1
    · exact lt_of_lt_of_le hkhi0 h.1
  have hcont : ContinuousOn φ (Set.uIcc klo khi) :=
    ((continuousOn_const.mul (op_ces_wage_continuousOn ha0 ha1)).sub continuousOn_id).mono hsub
  have h0 : (0 : ℝ) ∈ Set.uIcc (φ klo) (φ khi) :=
    Set.mem_uIcc.2 (Or.inr ⟨by simp only [hφ]; linarith, by simp only [hφ]; linarith⟩)
  obtain ⟨k, hk, hk0⟩ := intermediate_value_uIcc hcont h0
  refine ⟨k, hsub hk, ?_⟩
  simp only [hφ] at hk0
  linarith

/-- **Exercise 16.5(a)**, `σ = 1`: with Cobb–Douglas `f = Ak^a` the positive steady state is
`k* = [βA(1 − a)/((1 + β)g_n)]^{1/(1−a)}`. -/
theorem ex_16_5_a_cobbDouglas {β A a gn : ℝ} (hβ : 0 < β) (hA : 0 < A) (ha1 : a < 1)
    (hgn : 0 < gn) :
    ∃ k, 0 < k ∧ k = β / ((1 + β) * gn) * opWage (opCD A a) (opCDfp A a) k := by
  have hc : 0 < β / ((1 + β) * gn) * ((1 - a) * A) := by
    have : 0 < 1 - a := by linarith
    positivity
  set k := opKstarCD (β / ((1 + β) * gn) * ((1 - a) * A)) a
  have hk : 0 < k := op_kstarCD_pos hc
  refine ⟨k, hk, ?_⟩
  rw [op_cd_wage hk]
  have := (op_cd_steady_iff hc ha1 hk).2 rfl
  linear_combination this

/-- The constant `M = (1 − a)·max(a^e, (1 − a)^e)`, `e = 1/ρ − 1`, of the bound for `σ < 1`. -/
noncomputable def opCESM (a ρ : ℝ) : ℝ :=
  (1 - a) * max (a ^ (1 / ρ - 1)) ((1 - a) ^ (1 / ρ - 1))

/-- For `ρ < 0`: `w(k) ≤ A(1 − a)a^e k^{1−ρ}` with `e = 1/ρ − 1`. -/
theorem op_ces_wage_le_small {A a ρ k : ℝ} (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ρ < 0) (hk : 0 < k) :
    opCESwage A a ρ k ≤ A * (1 - a) * a ^ (1 / ρ - 1) * (k * k ^ (-ρ)) := by
  have he : 1 / ρ - 1 ≤ 0 := by
    have : 1 / ρ < 0 := by rw [one_div]; exact inv_lt_zero.2 hρ
    linarith
  have hb := op_ces_base_pos (ρ := ρ) ha0 ha1 hk
  have hakp : 0 < a * k ^ ρ := mul_pos ha0 (Real.rpow_pos_of_pos hk ρ)
  have hρne : ρ ≠ 0 := hρ.ne
  have h1 := Real.rpow_le_rpow_of_nonpos hakp hb.2.2 he
  rw [Real.mul_rpow ha0.le (Real.rpow_pos_of_pos hk ρ).le, ← Real.rpow_mul hk.le,
    show ρ * (1 / ρ - 1) = 1 + -ρ by field_simp; ring, Real.rpow_add hk, Real.rpow_one] at h1
  unfold opCESwage
  have h1a : 0 < 1 - a := by linarith
  calc A * (1 - a) * opCESbase a ρ k ^ (1 / ρ - 1)
      ≤ A * (1 - a) * (a ^ (1 / ρ - 1) * (k * k ^ (-ρ))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = A * (1 - a) * a ^ (1 / ρ - 1) * (k * k ^ (-ρ)) := by ring

/-- For `ρ < 0`: `w(k) ≤ A(1 − a)^{1/ρ}`, a bound uniform in `k`. -/
theorem op_ces_wage_le_large {A a ρ k : ℝ} (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ρ < 0) (hk : 0 < k) :
    opCESwage A a ρ k ≤ A * (1 - a) * (1 - a) ^ (1 / ρ - 1) := by
  have he : 1 / ρ - 1 ≤ 0 := by
    have : 1 / ρ < 0 := by rw [one_div]; exact inv_lt_zero.2 hρ
    linarith
  have hb := op_ces_base_pos (ρ := ρ) ha0 ha1 hk
  have h1a : 0 < 1 - a := by linarith
  have h1 := Real.rpow_le_rpow_of_nonpos h1a hb.2.1 he
  unfold opCESwage
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **Exercise 16.5(b)**: for `σ < 1` (`ρ < 0`), `w(k) ≤ AMk` for all `k > 0`, with
`M = opCESM a ρ > 0` independent of `A`. -/
theorem ex_16_5_b_bound {A a ρ : ℝ} (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1) (hρ : ρ < 0) :
    0 < opCESM a ρ ∧ ∀ k, 0 < k → opCESwage A a ρ k ≤ A * opCESM a ρ * k := by
  have h1a : 0 < 1 - a := by linarith
  have hM : 0 < opCESM a ρ := by
    unfold opCESM
    exact mul_pos h1a (lt_of_lt_of_le (Real.rpow_pos_of_pos ha0 _) (le_max_left _ _))
  refine ⟨hM, fun k hk => ?_⟩
  rcases le_total k 1 with hk1 | hk1
  · have h := op_ces_wage_le_small hA ha0 ha1 hρ hk
    have hkr : k ^ (-ρ) ≤ 1 := Real.rpow_le_one hk.le hk1 (by linarith)
    have hae : 0 < a ^ (1 / ρ - 1) := Real.rpow_pos_of_pos ha0 _
    have : A * (1 - a) * a ^ (1 / ρ - 1) * (k * k ^ (-ρ)) ≤
        A * (1 - a) * a ^ (1 / ρ - 1) * k := by
      have : k * k ^ (-ρ) ≤ k := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hmax : A * (1 - a) * a ^ (1 / ρ - 1) * k ≤ A * opCESM a ρ * k := by
      unfold opCESM
      have := le_max_left (a ^ (1 / ρ - 1)) ((1 - a) ^ (1 / ρ - 1))
      have : 0 ≤ A * (1 - a) * k := by positivity
      nlinarith
    linarith
  · have h := op_ces_wage_le_large hA ha0 ha1 hρ hk
    have hae : 0 < (1 - a) ^ (1 / ρ - 1) := Real.rpow_pos_of_pos h1a _
    have : A * (1 - a) * (1 - a) ^ (1 / ρ - 1) ≤ A * (1 - a) * (1 - a) ^ (1 / ρ - 1) * k := by
      have : 0 ≤ A * (1 - a) * (1 - a) ^ (1 / ρ - 1) := by positivity
      nlinarith
    have hmax : A * (1 - a) * (1 - a) ^ (1 / ρ - 1) * k ≤ A * opCESM a ρ * k := by
      unfold opCESM
      have := le_max_right (a ^ (1 / ρ - 1)) ((1 - a) ^ (1 / ρ - 1))
      have : 0 ≤ A * (1 - a) * k := by positivity
      nlinarith
    linarith

/-- **Exercise 16.5(b)** (Miao, p. 557): "for `A` sufficiently small, there is no positive steady
state": if `βAM < (1 + β)g_n` then `βw(k)/((1 + β)g_n) < k` for every `k > 0`. -/
theorem ex_16_5_b_none {β A a ρ gn : ℝ} (hβ : 0 < β) (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ρ < 0) (hgn : 0 < gn) (hsmall : β / ((1 + β) * gn) * A * opCESM a ρ < 1) :
    ∀ k, 0 < k → β / ((1 + β) * gn) * opCESwage A a ρ k < k := by
  intro k hk
  have h := (ex_16_5_b_bound hA ha0 ha1 hρ).2 k hk
  have hc : 0 < β / ((1 + β) * gn) := by positivity
  have := mul_le_mul_of_nonneg_left h hc.le
  nlinarith

/-- **Exercise 16.5(b)**: with `A` small every equilibrium path collapses to `0`:
`k_t ≤ qᵗk₀` with `q = βAM/((1 + β)g_n) < 1`, so the zero steady state is globally stable. -/
theorem ex_16_5_b_collapse {β A a ρ gn : ℝ} {k : ℕ → ℝ} (hβ : 0 < β) (hA : 0 < A)
    (ha0 : 0 < a) (ha1 : a < 1) (hρ : ρ < 0) (hgn : 0 < gn)
    (hsmall : β / ((1 + β) * gn) * A * opCESM a ρ < 1)
    (h : OPIsDiamondEqm (fun w R => opLogSaving β w 0 R) (opCES A a ρ) (opCESfp A a ρ) gn k) :
    (∀ t, k t ≤ (β / ((1 + β) * gn) * A * opCESM a ρ) ^ t * k 0) ∧ Tendsto k atTop (𝓝 0) := by
  have hl := (ex_16_5_law ha0 ha1).1 h
  set q := β / ((1 + β) * gn) * A * opCESM a ρ with hq
  have hc : 0 < β / ((1 + β) * gn) := by positivity
  have hq0 : 0 < q := mul_pos (mul_pos hc hA) (ex_16_5_b_bound hA ha0 ha1 hρ).1
  have hstep : ∀ t, k (t + 1) ≤ q * k t := by
    intro t
    rw [(hl t).2]
    have := mul_le_mul_of_nonneg_left ((ex_16_5_b_bound hA ha0 ha1 hρ).2 _ (hl t).1) hc.le
    rw [hq]; linarith
  have hb : ∀ t, k t ≤ q ^ t * k 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      calc k (t + 1) ≤ q * k t := hstep t
        _ ≤ q * (q ^ t * k 0) := mul_le_mul_of_nonneg_left ih hq0.le
        _ = q ^ (t + 1) * k 0 := by ring
  refine ⟨hb, ?_⟩
  have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hsmall).mul_const (k 0)
  rw [zero_mul] at hz
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun t => (hl t).1.le) hb

/-- **Exercise 16.5(b)**: for `A` large (`βA(1 − a) > (1 + β)g_n`) there are at least two
positive steady states `k₁ < 1 < k₂`, so the steady state is not unique. -/
theorem ex_16_5_b_two {β A a ρ gn : ℝ} (hβ : 0 < β) (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ρ < 0) (hgn : 0 < gn) (hlarge : 1 < β / ((1 + β) * gn) * (A * (1 - a))) :
    ∃ k1 k2, 0 < k1 ∧ k1 < 1 ∧ 1 < k2 ∧
      k1 = β / ((1 + β) * gn) * opCESwage A a ρ k1 ∧
      k2 = β / ((1 + β) * gn) * opCESwage A a ρ k2 := by
  set c := β / ((1 + β) * gn) with hc
  have hc0 : 0 < c := by positivity
  have h1a : 0 < 1 - a := by linarith
  set φ : ℝ → ℝ := fun k => c * opCESwage A a ρ k - k with hφ
  have hcont : ContinuousOn φ (Set.Ioi 0) :=
    (continuousOn_const.mul (op_ces_wage_continuousOn ha0 ha1)).sub continuousOn_id
  -- `φ(1) > 0`
  have hφ1 : 0 < φ 1 := by
    simp only [hφ, opCESwage, opCESbase, Real.one_rpow, mul_one]
    rw [show a + (1 - a) = 1 by ring, Real.one_rpow, mul_one]
    linarith
  -- small `k`
  set B := c * (A * (1 - a) * a ^ (1 / ρ - 1)) with hB
  have hB0 : 0 < B := by have := Real.rpow_pos_of_pos ha0 (1 / ρ - 1); positivity
  have hnρ : 0 < -ρ := by linarith
  set klo := min (1 / 2) ((1 / (2 * B)) ^ (-ρ)⁻¹) with hklo
  have hklo0 : 0 < klo := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hklo1 : klo < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hkr : klo ^ (-ρ) ≤ 1 / (2 * B) := by
    have := Real.rpow_le_rpow hklo0.le (min_le_right (1 / 2) ((1 / (2 * B)) ^ (-ρ)⁻¹))
      hnρ.le
    rwa [Real.rpow_inv_rpow (by positivity) hnρ.ne'] at this
  have hφlo : φ klo < 0 := by
    have h := mul_le_mul_of_nonneg_left (op_ces_wage_le_small hA ha0 ha1 hρ hklo0) hc0.le
    have : c * (A * (1 - a) * a ^ (1 / ρ - 1) * (klo * klo ^ (-ρ))) = B * klo * klo ^ (-ρ) := by
      rw [hB]; ring
    have hk2 : B * klo * klo ^ (-ρ) ≤ klo / 2 := by
      have := mul_le_mul_of_nonneg_left hkr (by positivity : 0 ≤ B * klo)
      have e : B * klo * (1 / (2 * B)) = klo / 2 := by field_simp
      linarith
    simp only [hφ]
    linarith
  -- large `k`
  set W1 := A * (1 - a) * (1 - a) ^ (1 / ρ - 1) with hW1
  set khi := max 2 (c * W1 + 1) with hkhi
  have hkhi1 : 1 < khi := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hφhi : φ khi < 0 := by
    have h := mul_le_mul_of_nonneg_left (op_ces_wage_le_large hA ha0 ha1 hρ
      (by linarith : (0 : ℝ) < khi)) hc0.le
    have : c * W1 + 1 ≤ khi := le_max_right _ _
    simp only [hφ]
    rw [hW1] at this
    linarith
  obtain ⟨k1, hk1, hk1e⟩ := intermediate_value_Ioo hklo1.le
    (hcont.mono fun x hx => lt_of_lt_of_le hklo0 hx.1) ⟨hφlo, hφ1⟩
  obtain ⟨k2, hk2, hk2e⟩ := intermediate_value_Ioo' hkhi1.le
    (hcont.mono fun x hx => lt_of_lt_of_le one_pos hx.1) ⟨hφhi, hφ1⟩
  refine ⟨k1, k2, lt_trans hklo0 hk1.1, hk1.2, hk2.1, ?_, ?_⟩
  · simp only [hφ] at hk1e; linarith
  · simp only [hφ] at hk2e; linarith

end Miao.OverlappingGenerations
