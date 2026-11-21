/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RBLogLinear
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The phase diagram and the saddle path of the log-linearised RBC model

Miao, §14.2, pp. 476–478 (Figure 14.1) and p. 484 (Figure 14.3). Throughout,
`0 < α < 1`, `0 < β < 1`, `ζ > 0`, `Y/K > 0`, `C/K > 0`.

* (14.34): `K̂_{t+1} − K̂_t = (p − 1)K̂_t + gẑ_t − qĈ_t` (`eq_14_34_K`). The second line of
  (14.34) is printed with `+(1 − α)βα(Y/K)/(α + ζ)·Ĉ_{t+1}`; (14.33) gives `−aĈ_{t+1}`
  (`eq_14_34_C`); the printed sign is wrong (`eq_14_34_printed_false`).
* The isocline `ΔĈ = 0` is `Ĉ_{t+1} = (1 + ζ)/(1 − α)·ẑ_{t+1} − ζK̂_{t+1}`, downward sloping
  (`rb_isocline_C`), and `Ĉ` falls exactly to the right of it (`rb_isocline_C_sign`). The
  isocline `ΔK̂ = 0` is (14.35), upward sloping (`eq_14_35`), and `K̂` falls exactly above it
  (`eq_14_35_sign`).
* With `ẑ = 0` the system is `x_{t+1} = Mx_t` (`rb_det_system`) with `det M = p/(1 + a)` and
  characteristic polynomial negative at `1` (`rb_char_one_neg`); hence its eigenvalues are real
  with `0 < λ₁ < 1 < λ₂` (`rb_saddle_roots`, `rb_saddle_eigen`): a saddle.
* The saddle path (`rb_saddle_det`): for every `K̂₀`, `K̂_t = λ₁ᵗK̂₀`, `Ĉ_t = φK̂_t` with
  `φ = (λ₂ − m₂₂)/q > 0` (upward sloping) solves the system and converges monotonically to the
  steady state, and it is the only bounded solution with that `K̂₀`: "given any initial state
  `K̂₀` there is a unique solution `Ĉ₀`, which must lie on the saddle".
* A permanent TFP shock (p. 484): with `ẑ_t = ẑ` for all `t`, the new steady state is
  `K̂* = Ĉ* = ẑ/(1 − α)` (`rb_permanent_ss`; both isoclines shift up, `rb_permanent_shift`);
  from `K̂₀ = 0` the unique bounded path rises monotonically to it, the interest rate
  `r̂^f_{t+1} = Ĉ_{t+1} − Ĉ_t` is positive and investment rises (`rb_permanent_path`). Initial
  consumption `Ĉ₀ = (1 − φ)ẑ/(1 − α)` may be of either sign (as the book says).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-! ### Signs of the coefficients -/

theorem rb_coeff_pos {α β ζ yk ck : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck) :
    1 < rb_p α β ζ yk ∧ 0 < rb_q α ζ yk ck ∧ 0 < rb_a α β ζ yk ∧ 0 < rb_b α β ζ yk ∧
      0 < rb_c α β ζ yk ∧ 0 < rb_g α ζ yk := by
  have h1 : 0 < 1 - α := by linarith
  have h2 : 0 < α + ζ := by linarith
  have hb : 1 < 1 / β := by rw [lt_one_div (by norm_num) hβ0]; simpa using hβ1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rb_p
    have : 0 < (1 - α) / (α + ζ) * α * yk := by positivity
    linarith
  · unfold rb_q; positivity
  · unfold rb_a; positivity
  · unfold rb_b; positivity
  · unfold rb_c; positivity
  · unfold rb_g; positivity

theorem rb_b_eq {α β ζ yk : ℝ} (hα1 : α < 1) :
    rb_b α β ζ yk = rb_a α β ζ yk * ((1 + ζ) / (1 - α)) := by
  have h1 : 1 - α ≠ 0 := by linarith
  unfold rb_a rb_b
  field_simp

theorem rb_c_eq (α β ζ yk : ℝ) : rb_c α β ζ yk = rb_a α β ζ yk * ζ := by
  unfold rb_a rb_c
  ring

/-! ### The phase diagram (14.34)–(14.35) -/

/-- Miao, (14.34), first line, p. 476: `K̂_{t+1} − K̂_t = (1/β − 1 + (1 − α)/(α + ζ)·αY/K)K̂_t
+ (Y/K)(1 + ζ)/(ζ + α)·ẑ_t − (C/K + (1 − α)/(α + ζ)·Y/K)Ĉ_t`. -/
theorem eq_14_34_K {α β ζ yk ck c k k' z : ℝ}
    (h : k' = rb_p α β ζ yk * k + rb_g α ζ yk * z - rb_q α ζ yk ck * c) :
    k' - k = (1 / β - 1 + (1 - α) / (α + ζ) * α * yk) * k + rb_g α ζ yk * z -
      rb_q α ζ yk ck * c := by
  rw [h, rb_p]
  ring

/-- Miao, (14.34), second line, corrected: (14.33) gives
`Ĉ_{t+1} − Ĉ_t = −(1 − α)βα(Y/K)/(α + ζ)·Ĉ_{t+1} + βα(Y/K)(1 + ζ)/(α + ζ)·ẑ_{t+1}
− βα(1 − α)(Y/K)ζ/(α + ζ)·K̂_{t+1}`. -/
theorem eq_14_34_C {α β ζ yk c c' k' z' : ℝ}
    (h : -c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k') :
    c' - c = -rb_a α β ζ yk * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k' := by
  linarith

/-- Correction to Miao, (14.34), p. 476: the printed second line
`Ĉ_{t+1} − Ĉ_t = +aĈ_{t+1} + bẑ_{t+1} − cK̂_{t+1}` is inconsistent with (14.33): whenever `a ≠ 0`,
the point `Ĉ_{t+1} = 1`, `Ĉ_t = 1 + a`, `ẑ_{t+1} = K̂_{t+1} = 0` satisfies (14.33) but not the
printed equation. -/
theorem eq_14_34_printed_false {α β ζ yk : ℝ} (ha : rb_a α β ζ yk ≠ 0) :
    let c' : ℝ := 1
    let c : ℝ := 1 + rb_a α β ζ yk
    (-c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * 0 - rb_c α β ζ yk * 0) ∧
      c' - c ≠ rb_a α β ζ yk * c' + rb_b α β ζ yk * 0 - rb_c α β ζ yk * 0 := by
  intro c' c
  refine ⟨by simp [c, c'], fun h => ha ?_⟩
  simp only [c, c'] at h
  linarith

/-- Miao, p. 477: the isocline `ΔĈ_t = 0`. Along (14.33),
`Ĉ_{t+1} − Ĉ_t = −a(Ĉ_{t+1} − (1 + ζ)/(1 − α)·ẑ_{t+1} + ζK̂_{t+1})`, so `Ĉ_{t+1} = Ĉ_t` iff
`Ĉ_{t+1} = (1 + ζ)/(1 − α)·ẑ_{t+1} − ζK̂_{t+1}`, a downward-sloping line (slope `−ζ < 0`). -/
theorem rb_isocline_C {α β ζ yk c c' k' z' : ℝ} (hα1 : α < 1) (ha : rb_a α β ζ yk ≠ 0)
    (h : -c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k') :
    c' - c = -rb_a α β ζ yk * (c' - (1 + ζ) / (1 - α) * z' + ζ * k') ∧
      (c' = c ↔ c' = (1 + ζ) / (1 - α) * z' - ζ * k') := by
  have hd : c' - c = -rb_a α β ζ yk * (c' - (1 + ζ) / (1 - α) * z' + ζ * k') := by
    rw [eq_14_34_C h, rb_b_eq hα1, rb_c_eq]
    ring
  refine ⟨hd, ⟨fun he => ?_, fun he => ?_⟩⟩
  · have : rb_a α β ζ yk * (c' - (1 + ζ) / (1 - α) * z' + ζ * k') = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 ha
    · linarith
  · have : c' - c = 0 := by rw [hd, he]; ring
    linarith

/-- Miao, p. 477: "when `K̂` is above the isocline `Ĉ_t = Ĉ_{t+1}`, `Ĉ_t` is expected to fall":
with `a > 0`, `Ĉ_{t+1} < Ĉ_t` iff `ζK̂_{t+1} > (1 + ζ)/(1 − α)·ẑ_{t+1} − Ĉ_{t+1}`. -/
theorem rb_isocline_C_sign {α β ζ yk c c' k' z' : ℝ} (hα1 : α < 1) (ha : 0 < rb_a α β ζ yk)
    (h : -c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k') :
    c' < c ↔ (1 + ζ) / (1 - α) * z' - c' < ζ * k' := by
  have hd := (rb_isocline_C hα1 ha.ne' h).1
  constructor
  · intro hlt
    by_contra hge
    push Not at hge
    have : 0 ≤ c' - c := by
      rw [hd]
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    linarith
  · intro hlt
    have : c' - c < 0 := by
      rw [hd]
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith

/-- Miao, (14.35), p. 477: the isocline `ΔK̂_t = 0`: `K̂_{t+1} = K̂_t` iff
`Ĉ_t = (C/K + (1 − α)/(α + ζ)·Y/K)⁻¹[(1/β − 1 + (1 − α)/(α + ζ)·αY/K)K̂_t
+ (Y/K)(1 + ζ)/(ζ + α)·ẑ_t]`, an upward-sloping line. -/
theorem eq_14_35 {α β ζ yk ck c k k' z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck)
    (h : k' = rb_p α β ζ yk * k + rb_g α ζ yk * z - rb_q α ζ yk ck * c) :
    (k' = k ↔ c = (rb_q α ζ yk ck)⁻¹ * ((1 / β - 1 + (1 - α) / (α + ζ) * α * yk) * k +
        rb_g α ζ yk * z)) ∧
      0 < (rb_q α ζ yk ck)⁻¹ * (1 / β - 1 + (1 - α) / (α + ζ) * α * yk) := by
  obtain ⟨hp, hq, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have hd := eq_14_34_K h
  have hp' : 1 / β - 1 + (1 - α) / (α + ζ) * α * yk = rb_p α β ζ yk - 1 := by
    rw [rb_p]; ring
  refine ⟨⟨fun he => ?_, fun he => ?_⟩, ?_⟩
  · rw [he, sub_self, hp'] at hd
    rw [hp', eq_inv_mul_iff_mul_eq₀ hq.ne']
    linarith
  · rw [hp'] at he hd
    rw [he, mul_inv_cancel_left₀ hq.ne'] at hd
    linarith
  · rw [hp']
    have : 0 < rb_p α β ζ yk - 1 := by linarith
    positivity

/-- Miao, pp. 477–478: "when `Ĉ_t` is above the isocline `K̂_{t+1} = K̂_t`, `K̂_t` is expected to
fall because households save less": `K̂_{t+1} < K̂_t` iff `Ĉ_t` exceeds the right side of
(14.35). -/
theorem eq_14_35_sign {α β ζ yk ck c k k' z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck)
    (h : k' = rb_p α β ζ yk * k + rb_g α ζ yk * z - rb_q α ζ yk ck * c) :
    k' < k ↔ (rb_q α ζ yk ck)⁻¹ * ((1 / β - 1 + (1 - α) / (α + ζ) * α * yk) * k +
        rb_g α ζ yk * z) < c := by
  obtain ⟨-, hq, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have hd := eq_14_34_K h
  rw [inv_mul_lt_iff₀ hq]
  constructor <;> intro h' <;> nlinarith

/-! ### The deterministic system as `x_{t+1} = Mx_t` -/

/-- The entries of the matrix `M` of the deterministic log-linearised system in `(K̂, Ĉ)`. -/
noncomputable def rb_m21 (α β ζ yk : ℝ) : ℝ :=
  -(rb_c α β ζ yk * rb_p α β ζ yk) / (1 + rb_a α β ζ yk)

/-- `m₂₂ = (1 + cq)/(1 + a)`. -/
noncomputable def rb_m22 (α β ζ yk ck : ℝ) : ℝ :=
  (1 + rb_c α β ζ yk * rb_q α ζ yk ck) / (1 + rb_a α β ζ yk)

/-- Miao, pp. 476–477: the deterministic system (14.32)–(14.33) is
`K̂_{t+1} = pK̂_t − qĈ_t + gẑ_t`,
`Ĉ_{t+1} = m₂₁K̂_t + m₂₂Ĉ_t + (bẑ_{t+1} − cgẑ_t)/(1 + a)`. -/
theorem rb_det_system {α β ζ yk ck c c' k k' z z' : ℝ} (ha : 1 + rb_a α β ζ yk ≠ 0)
    (h1 : k' = rb_p α β ζ yk * k + rb_g α ζ yk * z - rb_q α ζ yk ck * c)
    (h2 : -c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k') :
    c' = rb_m21 α β ζ yk * k + rb_m22 α β ζ yk ck * c +
      (rb_b α β ζ yk * z' - rb_c α β ζ yk * rb_g α ζ yk * z) / (1 + rb_a α β ζ yk) := by
  rw [rb_m21, rb_m22]
  field_simp
  rw [h1] at h2
  linarith

/-- `det M = m₁₁m₂₂ − m₁₂m₂₁ = p/(1 + a)`. -/
theorem rb_det_M {α β ζ yk ck : ℝ} (ha : 1 + rb_a α β ζ yk ≠ 0) :
    rb_p α β ζ yk * rb_m22 α β ζ yk ck - (-rb_q α ζ yk ck) * rb_m21 α β ζ yk =
      rb_p α β ζ yk / (1 + rb_a α β ζ yk) := by
  rw [rb_m21, rb_m22]
  field_simp
  ring

/-- The characteristic polynomial `λ² − (m₁₁ + m₂₂)λ + det M` is negative at `λ = 1`:
`1 − tr M + det M = (a(1 − p) − cq)/(1 + a) < 0`; also `det M > 0` and `m₁₂m₂₁ > 0`. -/
theorem rb_char_one_neg {α β ζ yk ck : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck) :
    1 - (rb_p α β ζ yk + rb_m22 α β ζ yk ck) +
        (rb_p α β ζ yk * rb_m22 α β ζ yk ck - (-rb_q α ζ yk ck) * rb_m21 α β ζ yk) < 0 ∧
      0 < rb_p α β ζ yk * rb_m22 α β ζ yk ck - (-rb_q α ζ yk ck) * rb_m21 α β ζ yk ∧
      0 < (-rb_q α ζ yk ck) * rb_m21 α β ζ yk := by
  obtain ⟨hp, hq, ha, -, hc, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have ha' : 1 + rb_a α β ζ yk ≠ 0 := by linarith
  rw [rb_det_M ha']
  refine ⟨?_, by positivity, ?_⟩
  · have : 1 - (rb_p α β ζ yk + rb_m22 α β ζ yk ck) + rb_p α β ζ yk / (1 + rb_a α β ζ yk) =
        (rb_a α β ζ yk * (1 - rb_p α β ζ yk) - rb_c α β ζ yk * rb_q α ζ yk ck) /
          (1 + rb_a α β ζ yk) := by
      rw [rb_m22]
      field_simp
      ring
    rw [this]
    apply div_neg_of_neg_of_pos _ (by linarith)
    nlinarith [mul_pos hc hq]
  · rw [rb_m21]
    have : 0 < rb_c α β ζ yk * rb_p α β ζ yk := by nlinarith
    rw [neg_mul, neg_div, mul_neg, neg_neg]
    positivity

/-- The two roots of `λ² − Tλ + D`. -/
noncomputable def rb_lam1 (T D : ℝ) : ℝ := (T - √(T ^ 2 - 4 * D)) / 2

/-- The larger root of `λ² − Tλ + D`. -/
noncomputable def rb_lam2 (T D : ℝ) : ℝ := (T + √(T ^ 2 - 4 * D)) / 2

/-- If `1 − T + D < 0` and `D > 0`, the roots of `λ² − Tλ + D` are real and
`0 < λ₁ < 1 < λ₂`, with `λ₁ + λ₂ = T` and `λ₁λ₂ = D`. -/
theorem rb_saddle_roots {T D : ℝ} (h1 : 1 - T + D < 0) (hD : 0 < D) :
    rb_lam1 T D + rb_lam2 T D = T ∧ rb_lam1 T D * rb_lam2 T D = D ∧
      0 < rb_lam1 T D ∧ rb_lam1 T D < 1 ∧ 1 < rb_lam2 T D ∧
      (∀ x, x ^ 2 - T * x + D = (x - rb_lam1 T D) * (x - rb_lam2 T D)) := by
  have hdisc : (T - 2) ^ 2 < T ^ 2 - 4 * D := by nlinarith
  have hd0 : 0 ≤ T ^ 2 - 4 * D := le_trans (sq_nonneg _) hdisc.le
  set r := √(T ^ 2 - 4 * D)
  have hr2 : r ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt hd0
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have habs : |T - 2| < r := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hdisc
  have hsum : rb_lam1 T D + rb_lam2 T D = T := by unfold rb_lam1 rb_lam2; ring
  have hprod : rb_lam1 T D * rb_lam2 T D = D := by
    unfold rb_lam1 rb_lam2
    nlinarith
  have hl2 : 1 < rb_lam2 T D := by
    unfold rb_lam2
    have := neg_abs_le (T - 2)
    linarith
  have hl1 : rb_lam1 T D < 1 := by
    unfold rb_lam1
    have := le_abs_self (T - 2)
    linarith
  refine ⟨hsum, hprod, ?_, hl1, hl2, fun x => ?_⟩
  · by_contra hn
    push Not at hn
    nlinarith
  · have : (x - rb_lam1 T D) * (x - rb_lam2 T D) =
        x ^ 2 - (rb_lam1 T D + rb_lam2 T D) * x + rb_lam1 T D * rb_lam2 T D := by ring
    rw [this, hsum, hprod]

/-- **The saddle property** (Miao, pp. 477–478): the matrix `M` of the deterministic system has
real eigenvalues `0 < λ₁ < 1 < λ₂` (roots of `λ² − tr M·λ + det M`), and `λ₁ < m₂₂ < λ₂`. -/
theorem rb_saddle_eigen {α β ζ yk ck : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck) :
    let T := rb_p α β ζ yk + rb_m22 α β ζ yk ck
    let D := rb_p α β ζ yk * rb_m22 α β ζ yk ck - (-rb_q α ζ yk ck) * rb_m21 α β ζ yk
    rb_lam1 T D + rb_lam2 T D = T ∧ rb_lam1 T D * rb_lam2 T D = D ∧ 0 < rb_lam1 T D ∧
      rb_lam1 T D < 1 ∧ 1 < rb_lam2 T D ∧ rb_lam1 T D < rb_m22 α β ζ yk ck ∧
      rb_m22 α β ζ yk ck < rb_lam2 T D := by
  intro T D
  obtain ⟨h1, hD, hm⟩ := rb_char_one_neg hα0 hα1 hβ0 hβ1 hζ hyk hck
  obtain ⟨hs, hp, hl0, hl1, hl2, hfac⟩ := rb_saddle_roots h1 hD
  have hneg : (rb_m22 α β ζ yk ck - rb_lam1 T D) * (rb_m22 α β ζ yk ck - rb_lam2 T D) < 0 := by
    rw [← hfac]
    nlinarith
  have hle : rb_lam1 T D ≤ rb_lam2 T D := by linarith
  refine ⟨hs, hp, hl0, hl1, hl2, ?_, ?_⟩
  · by_contra hn
    push Not at hn
    nlinarith
  · by_contra hn
    push Not at hn
    nlinarith

/-! ### The saddle path of a `2 × 2` system -/

/-- The left eigenvector identity: if `l² − (m₁₁ + m₂₂)l + (m₁₁m₂₂ − m₁₂m₂₁) = 0`, then
`w = (l − m₂₂)k + m₁₂c` satisfies `w' = lw` along `x' = Mx`. -/
theorem rb_left_eig {m11 m12 m21 m22 l : ℝ}
    (hl : l ^ 2 - (m11 + m22) * l + (m11 * m22 - m12 * m21) = 0) (k c : ℝ) :
    (l - m22) * (m11 * k + m12 * c) + m12 * (m21 * k + m22 * c) =
      l * ((l - m22) * k + m12 * c) := by
  linear_combination (-k) * hl

/-- **The saddle path** of `x_{t+1} = Mx_t` (Miao, pp. 477–478). Let `λ₁ + λ₂ = m₁₁ + m₂₂`,
`λ₁λ₂ = m₁₁m₂₂ − m₁₂m₂₁`, `m₁₂ ≠ 0`, `|λ₁| < 1 < λ₂`, and `φ = (m₂₂ − λ₂)/m₁₂`. Then for
every `k₀`: (i) `k_t = λ₁ᵗk₀`, `c_t = φk_t` solves the system and tends to `0`; (ii) every
bounded solution with `k_0 = k₀` is this one. -/
theorem rb_saddle_det {m11 m12 m21 m22 l1 l2 : ℝ} (hsum : l1 + l2 = m11 + m22)
    (hprod : l1 * l2 = m11 * m22 - m12 * m21) (hm12 : m12 ≠ 0) (hl1 : |l1| < 1)
    (hl2 : 1 < l2) (k0 : ℝ) :
    let φ := (m22 - l2) / m12
    ((∀ t : ℕ, l1 ^ (t + 1) * k0 = m11 * (l1 ^ t * k0) + m12 * (φ * (l1 ^ t * k0)) ∧
        φ * (l1 ^ (t + 1) * k0) = m21 * (l1 ^ t * k0) + m22 * (φ * (l1 ^ t * k0))) ∧
      Tendsto (fun t : ℕ => l1 ^ t * k0) atTop (𝓝 0)) ∧
      ∀ k c : ℕ → ℝ, k 0 = k0 →
        (∀ t, k (t + 1) = m11 * k t + m12 * c t ∧ c (t + 1) = m21 * k t + m22 * c t) →
        (∃ B, ∀ t, |k t| ≤ B ∧ |c t| ≤ B) → ∀ t, k t = l1 ^ t * k0 ∧ c t = φ * k t := by
  intro φ
  have hl2' : l2 ^ 2 - (m11 + m22) * l2 + (m11 * m22 - m12 * m21) = 0 := by
    rw [← hsum, ← hprod]; ring
  have hφ1 : m11 + m12 * φ = l1 := by
    simp only [φ]
    field_simp
    linarith
  have hφ2 : m21 + m22 * φ = φ * l1 := by
    simp only [φ]
    field_simp
    have : l1 = m11 + m22 - l2 := by linarith
    rw [this]
    linear_combination (-1) * hl2'
  refine ⟨⟨fun t => ⟨?_, ?_⟩, ?_⟩, fun k c hk0 hsys hB => ?_⟩
  · rw [pow_succ]
    linear_combination (-(l1 ^ t * k0)) * hφ1
  · rw [pow_succ]
    linear_combination (-(l1 ^ t * k0)) * hφ2
  · simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hl1).mul_const k0
  · -- the unstable combination `w_t = (λ₂ − m₂₂)k_t + m₁₂c_t` grows like `λ₂ᵗ`
    set w : ℕ → ℝ := fun t => (l2 - m22) * k t + m12 * c t
    have hw : ∀ t, w t = l2 ^ t * w 0 := fun t => by
      induction t with
      | zero => simp
      | succ t ih =>
        have h := rb_left_eig hl2' (k t) (c t)
        simp only [w] at ih ⊢
        rw [(hsys t).1, (hsys t).2, h, ih, pow_succ]
        ring
    obtain ⟨B, hBt⟩ := hB
    have hw0 : w 0 = 0 := by
      by_contra hne
      have hbd : ∀ t, |w t| ≤ (|l2 - m22| + |m12|) * B := fun t => by
        simp only [w]
        calc |(l2 - m22) * k t + m12 * c t| ≤ |l2 - m22| * |k t| + |m12| * |c t| := by
              rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
          _ ≤ |l2 - m22| * B + |m12| * B := by
              gcongr
              · exact (hBt t).1
              · exact (hBt t).2
          _ = _ := by ring
      have htend : Tendsto (fun t : ℕ => l2 ^ t * |w 0|) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt hl2).atTop_mul_const (abs_pos.2 hne)
      obtain ⟨t, ht⟩ := (htend.eventually_gt_atTop ((|l2 - m22| + |m12|) * B)).exists
      have := hbd t
      rw [hw t, abs_mul, abs_of_pos (pow_pos (by linarith) t)] at this
      linarith
    have hc : ∀ t, c t = φ * k t := fun t => by
      have h0 : w t = 0 := by rw [hw t, hw0, mul_zero]
      simp only [w, φ] at h0 ⊢
      field_simp
      linarith
    have hk : ∀ t, k t = l1 ^ t * k0 := fun t => by
      induction t with
      | zero => simp [hk0]
      | succ t ih =>
        rw [(hsys t).1, hc t, ih, pow_succ]
        linear_combination (l1 ^ t * k0) * hφ1
    exact fun t => ⟨hk t, hc t⟩

/-! ### A permanent TFP shock (p. 484) -/

/-- Miao, p. 484: with a permanent shock `ẑ_t = ẑ` and the steady-state relations
`1/β = αY/K + 1 − δ`, `C/K = Y/K − δ`, the point `K̂* = Ĉ* = ẑ/(1 − α)` is a steady state of
(14.32)–(14.33). -/
theorem rb_permanent_ss {α β δ ζ yk ck : ℝ} (hα1 : α < 1) (hαζ : α + ζ ≠ 0)
    (hβ : 1 / β = α * yk + 1 - δ) (hck : ck = yk - δ) (z : ℝ) :
    z / (1 - α) = rb_p α β ζ yk * (z / (1 - α)) + rb_g α ζ yk * z -
        rb_q α ζ yk ck * (z / (1 - α)) ∧
      -(z / (1 - α)) = -(1 + rb_a α β ζ yk) * (z / (1 - α)) + rb_b α β ζ yk * z -
        rb_c α β ζ yk * (z / (1 - α)) := by
  have h1 : 1 - α ≠ 0 := by linarith
  have h2 : ζ + α ≠ 0 := by rwa [add_comm]
  constructor
  · rw [rb_p, hβ, rb_g, rb_q, hck]
    field_simp
    ring
  · rw [rb_a, rb_b, rb_c]
    field_simp
    ring

/-- Miao, p. 484: "both isoclines `ΔĈ_t = 0` and `ΔK̂_t = 0` shift up" with a permanent rise in
`ẑ`: the intercepts `(1 + ζ)/(1 − α)·ẑ` and `q⁻¹gẑ` increase with `ẑ`. -/
theorem rb_permanent_shift {α β ζ yk ck : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck) :
    StrictMono (fun z : ℝ => (1 + ζ) / (1 - α) * z) ∧
      StrictMono (fun z : ℝ => (rb_q α ζ yk ck)⁻¹ * (rb_g α ζ yk * z)) := by
  obtain ⟨-, hq, -, -, -, hg⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have h1 : 0 < (1 + ζ) / (1 - α) := div_pos (by linarith) (by linarith)
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · simp only
    exact mul_lt_mul_of_pos_left hab h1
  · simp only
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hab hg) (inv_pos.2 hq)

/-- **The response to a permanent TFP shock** (Miao, p. 484, Figure 14.3). Let `ẑ_t = ẑ > 0`
for all `t`, `K̂₀ = 0`, with the steady-state relations of `rb_permanent_ss`. Write
`λ₁ < 1 < λ₂` for the eigenvalues of `M` and `φ = (λ₂ − m₂₂)/q > 0` for the slope of the saddle
path. Then `K̂_t = (1 − λ₁ᵗ)ẑ/(1 − α)`, `Ĉ_t = ẑ/(1 − α) − φλ₁ᵗẑ/(1 − α)` solves
(14.32)–(14.33); it is the unique bounded solution with `K̂₀ = 0`; capital and consumption rise
strictly along it (so the interest rate `r̂^f_{t+1} = Ĉ_{t+1} − Ĉ_t > 0`), and investment
`Î_t = (K̂_{t+1} − (1 − δ)K̂_t)/δ` is positive for `0 < δ ≤ 1`. -/
theorem rb_permanent_path {α β δ ζ yk ck : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck)
    (hβ : 1 / β = α * yk + 1 - δ) (hck' : ck = yk - δ) {z : ℝ} (hz : 0 < z) :
    let T := rb_p α β ζ yk + rb_m22 α β ζ yk ck
    let D := rb_p α β ζ yk * rb_m22 α β ζ yk ck - (-rb_q α ζ yk ck) * rb_m21 α β ζ yk
    let l1 := rb_lam1 T D
    let φ := (rb_lam2 T D - rb_m22 α β ζ yk ck) / rb_q α ζ yk ck
    let K : ℕ → ℝ := fun t => (1 - l1 ^ t) * (z / (1 - α))
    let C : ℕ → ℝ := fun t => z / (1 - α) - φ * (l1 ^ t * (z / (1 - α)))
    0 < φ ∧
      (∀ t, K (t + 1) = rb_p α β ζ yk * K t + rb_g α ζ yk * z - rb_q α ζ yk ck * C t ∧
        -C t = -(1 + rb_a α β ζ yk) * C (t + 1) + rb_b α β ζ yk * z -
          rb_c α β ζ yk * K (t + 1)) ∧
      (∀ K' C' : ℕ → ℝ, K' 0 = 0 →
        (∀ t, K' (t + 1) = rb_p α β ζ yk * K' t + rb_g α ζ yk * z - rb_q α ζ yk ck * C' t ∧
          -C' t = -(1 + rb_a α β ζ yk) * C' (t + 1) + rb_b α β ζ yk * z -
            rb_c α β ζ yk * K' (t + 1)) →
        (∃ B, ∀ t, |K' t| ≤ B ∧ |C' t| ≤ B) → K' = K ∧ C' = C) ∧
      StrictMono K ∧ StrictMono C ∧ (∀ t, 0 < C (t + 1) - C t) ∧
      (∀ t, 0 < (K (t + 1) - (1 - δ) * K t) / δ) := by
  intro T D l1 φ K C
  obtain ⟨hp, hq, ha, -, hc, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have ha' : 1 + rb_a α β ζ yk ≠ 0 := by linarith
  obtain ⟨hs, hpr, hl0, hl1, hl2, hlm, hml⟩ := rb_saddle_eigen hα0 hα1 hβ0 hβ1 hζ hyk hck
  have hαζ : α + ζ ≠ 0 := by linarith
  obtain ⟨hss1, hss2⟩ := rb_permanent_ss (z := z) (yk := yk) (ck := ck) hα1 hαζ hβ hck'
  have hz1 : 0 < z / (1 - α) := div_pos hz (by linarith)
  have hφ : 0 < φ := div_pos (by linarith) hq
  -- the deviations from the new steady state solve the homogeneous system
  have hM := rb_saddle_det (m11 := rb_p α β ζ yk) (m12 := -rb_q α ζ yk ck)
    (m21 := rb_m21 α β ζ yk) (m22 := rb_m22 α β ζ yk ck) hs hpr (neg_ne_zero.2 hq.ne')
    (by rw [abs_of_pos hl0]; exact hl1) hl2 (-(z / (1 - α)))
  have hφ' : (rb_m22 α β ζ yk ck - rb_lam2 T D) / -rb_q α ζ yk ck = φ := by
    simp only [φ]
    rw [div_neg, ← neg_div, neg_sub]
  obtain ⟨⟨hsol, -⟩, huniq⟩ := hM
  -- from the matrix form back to (14.32)–(14.33)
  have hback : ∀ k c k' c' : ℝ, k' = rb_p α β ζ yk * k + (-rb_q α ζ yk ck) * c →
      c' = rb_m21 α β ζ yk * k + rb_m22 α β ζ yk ck * c →
      k' = rb_p α β ζ yk * k - rb_q α ζ yk ck * c ∧
        -c = -(1 + rb_a α β ζ yk) * c' - rb_c α β ζ yk * k' := fun k c k' c' h1 h2 => by
    refine ⟨by linarith, ?_⟩
    rw [h2, h1, rb_m21, rb_m22]
    field_simp
    ring
  have hfwd : ∀ k c k' c' : ℝ, k' = rb_p α β ζ yk * k - rb_q α ζ yk ck * c →
      -c = -(1 + rb_a α β ζ yk) * c' - rb_c α β ζ yk * k' →
      k' = rb_p α β ζ yk * k + (-rb_q α ζ yk ck) * c ∧
        c' = rb_m21 α β ζ yk * k + rb_m22 α β ζ yk ck * c := fun k c k' c' h1 h2 => by
    refine ⟨by linarith, ?_⟩
    have := rb_det_system (c := c) (c' := c') (k := k) (k' := k') (z := 0) (z' := 0) ha'
      (by rw [h1]; ring) (by linarith)
    simpa using this
  have hKd : ∀ t, K t = z / (1 - α) + l1 ^ t * (-(z / (1 - α))) := fun t => by
    simp only [K]; ring
  have hCd : ∀ t, C t = z / (1 - α) + φ * (l1 ^ t * (-(z / (1 - α)))) := fun t => by
    simp only [C]; ring
  have hsys : ∀ t, K (t + 1) = rb_p α β ζ yk * K t + rb_g α ζ yk * z -
      rb_q α ζ yk ck * C t ∧ -C t = -(1 + rb_a α β ζ yk) * C (t + 1) + rb_b α β ζ yk * z -
        rb_c α β ζ yk * K (t + 1) := fun t => by
    obtain ⟨e1, e2⟩ := hback _ _ _ _ (hsol t).1 (hsol t).2
    rw [hKd, hKd, hCd, hCd]
    constructor
    · linear_combination e1 + hss1
    · linear_combination e2 + hss2
  refine ⟨hφ, hsys, fun K' C' hK0 hsys' hB => ?_, ?_, ?_, ?_, ?_⟩
  · -- uniqueness: the deviations are a bounded solution of the homogeneous system
    obtain ⟨B, hB⟩ := hB
    have hu := huniq (fun t => K' t - z / (1 - α)) (fun t => C' t - z / (1 - α))
      (by simp [hK0]) (fun t => by
        obtain ⟨e1, e2⟩ := hsys' t
        have e1' : K' (t + 1) - z / (1 - α) = rb_p α β ζ yk * (K' t - z / (1 - α)) -
            rb_q α ζ yk ck * (C' t - z / (1 - α)) := by linear_combination e1 - hss1
        have e2' : -(C' t - z / (1 - α)) = -(1 + rb_a α β ζ yk) * (C' (t + 1) - z / (1 - α)) -
            rb_c α β ζ yk * (K' (t + 1) - z / (1 - α)) := by linear_combination e2 - hss2
        exact hfwd _ _ _ _ e1' e2')
      ⟨B + |z / (1 - α)|, fun t => ⟨(abs_sub _ _).trans (by linarith [(hB t).1]),
        (abs_sub _ _).trans (by linarith [(hB t).2])⟩⟩
    refine ⟨funext fun t => ?_, funext fun t => ?_⟩
    · have := (hu t).1
      rw [hKd]
      linarith
    · have h1 := (hu t).1
      have e : C' t - z / (1 - α) = φ * (K' t - z / (1 - α)) := by rw [(hu t).2, ← hφ']
      rw [hCd, ← h1]
      linarith
  · refine strictMono_nat_of_lt_succ fun t => ?_
    simp only [K]
    have : l1 ^ (t + 1) < l1 ^ t := pow_lt_pow_right_of_lt_one₀ hl0 hl1 (Nat.lt_succ_self t)
    nlinarith
  · refine strictMono_nat_of_lt_succ fun t => ?_
    simp only [C]
    have : l1 ^ (t + 1) < l1 ^ t := pow_lt_pow_right_of_lt_one₀ hl0 hl1 (Nat.lt_succ_self t)
    have : 0 < φ * ((l1 ^ t - l1 ^ (t + 1)) * (z / (1 - α))) := by
      apply mul_pos hφ (mul_pos (by linarith) hz1)
    nlinarith
  · intro t
    simp only [C]
    have : l1 ^ (t + 1) < l1 ^ t := pow_lt_pow_right_of_lt_one₀ hl0 hl1 (Nat.lt_succ_self t)
    have : 0 < φ * ((l1 ^ t - l1 ^ (t + 1)) * (z / (1 - α))) := by
      apply mul_pos hφ (mul_pos (by linarith) hz1)
    nlinarith
  · intro t
    apply div_pos _ hδ0
    simp only [K]
    have h1 : l1 ^ (t + 1) < l1 ^ t := pow_lt_pow_right_of_lt_one₀ hl0 hl1 (Nat.lt_succ_self t)
    have h2 : l1 ^ t ≤ 1 := pow_le_one₀ hl0.le hl1.le
    have h3 : 0 ≤ 1 - δ := by linarith
    have : (1 - δ) * ((1 - l1 ^ t) * (z / (1 - α))) ≤ (1 - l1 ^ t) * (z / (1 - α)) := by
      have : 0 ≤ (1 - l1 ^ t) * (z / (1 - α)) := mul_nonneg (by linarith) hz1.le
      nlinarith
    nlinarith

end Miao.NeoclassicalGrowth
