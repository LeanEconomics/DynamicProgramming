/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSustainability.CakeEating

/-!
# Log utility, Cobb–Douglas output and full depreciation

The common structure of the chapter's dynamic models (AKMM, §25.4.2, pp. 767–771, and §25.5.2,
pp. 777–778): log utility, output `Y_t` with `log Y_t = w_t + α log K_t` for some sequence `w`
(productivity, damages, energy) and the resource constraint `C_t + K_{t+1} = Y_t`.

With the saving rate `s_t = K_{t+1}/Y_t` and `B = 1/(1 − αβ)`, for every horizon `T`
`Σ_{t<T} β^t log C_t = Bα log K₀ + B Σ_{t<T} β^t w_t + Σ_{t<T} β^t φ(s_t) − β^T Bα log K_T`
with `φ(s) = log(1 − s) + αβB log s` (`lg_identity`). `φ` is maximised at `s = αβ`
(`lg_phi_le`). So lifetime utility splits into a saving part, maximised by the constant saving
rate `αβ`, a part linear in the `w_t`, and a terminal term: this is the guess-and-verify
argument behind the closed forms of GHKT and of Dasgupta–Heal, made exact at every finite
horizon (`lg_compare`). The terminal terms vanish under linear growth bounds
(`lg_linear_bound`, `lg_tendsto_linear`, `lg_summable_linear`).
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

/-- The saving part of the period objective, `φ(s) = log(1 − s) + (αβ/(1 − αβ)) log s`. -/
noncomputable def lgPhi (α β s : ℝ) : ℝ :=
  Real.log (1 - s) + α * β / (1 - α * β) * Real.log s

/-- `φ` is maximised at the saving rate `s = αβ`. -/
theorem lg_phi_le {α β s : ℝ} (hab0 : 0 < α * β) (hab1 : α * β < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    lgPhi α β s ≤ lgPhi α β (α * β) := by
  have h1 : 0 < 1 - α * β := by linarith
  have t1 := sust_log_le_tangent (by linarith : 0 < 1 - s) h1
  have t2 := sust_log_le_tangent hs0 hab0
  have hk : 0 ≤ α * β / (1 - α * β) := by positivity
  have ha : α ≠ 0 := left_ne_zero_of_mul hab0.ne'
  have hb : β ≠ 0 := right_ne_zero_of_mul hab0.ne'
  unfold lgPhi
  have e : (1 - s - (1 - α * β)) / (1 - α * β) +
      α * β / (1 - α * β) * ((s - α * β) / (α * β)) = 0 := by
    field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left t2 hk]

/-- The exact finite-horizon decomposition of lifetime utility: with `s_t = K_{t+1}/Y_t`,
`Σ_{t<T} β^t log C_t = (α/(1 − αβ)) log K₀ + (1/(1 − αβ)) Σ_{t<T} β^t w_t
  + Σ_{t<T} β^t φ(s_t) − β^T (α/(1 − αβ)) log K_T`. -/
theorem lg_identity {α β : ℝ} (hab1 : α * β < 1) {K Y C w : ℕ → ℝ} (hK : ∀ t, 0 < K t)
    (hC : ∀ t, 0 < C t) (hres : ∀ t, C t + K (t + 1) = Y t)
    (hY : ∀ t, Real.log (Y t) = w t + α * Real.log (K t)) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * Real.log (C t) =
      α / (1 - α * β) * Real.log (K 0) + 1 / (1 - α * β) * ∑ t ∈ range T, β ^ t * w t +
        ∑ t ∈ range T, β ^ t * lgPhi α β (K (t + 1) / Y t) -
          β ^ T * (α / (1 - α * β)) * Real.log (K T) := by
  have h1 : (1 : ℝ) - α * β ≠ 0 := (by linarith : (0 : ℝ) < 1 - α * β).ne'
  induction T with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ, sum_range_succ]
    have hYp : 0 < Y n := by rw [← hres n]; linarith [hC n, hK (n + 1)]
    have hs1 : Real.log (1 - K (n + 1) / Y n) = Real.log (C n) - Real.log (Y n) := by
      rw [← Real.log_div (hC n).ne' hYp.ne']
      congr 1
      rw [eq_div_iff hYp.ne', sub_mul, one_mul, div_mul_cancel₀ _ hYp.ne']
      linarith [hres n]
    have hs2 : Real.log (K (n + 1) / Y n) = Real.log (K (n + 1)) - Real.log (Y n) :=
      Real.log_div (hK (n + 1)).ne' hYp.ne'
    simp only [lgPhi, hs1, hs2, hY n, pow_succ]
    field_simp
    ring

/-- The comparison of two plans from the same `K₀`, the second with the constant saving rate
`αβ`: at every horizon
`Σ_{t<T} β^t log C_t − Σ_{t<T} β^t log C*_t
  ≤ (1/(1 − αβ)) Σ_{t<T} β^t (w_t − w*_t) − β^T (α/(1 − αβ))(log K_T − log K*_T)`. -/
theorem lg_compare {α β : ℝ} (hab0 : 0 < α * β) (hab1 : α * β < 1) (hβ : 0 < β)
    {K Y C w Ks Ys Cs ws : ℕ → ℝ} (hK : ∀ t, 0 < K t) (hC : ∀ t, 0 < C t)
    (hres : ∀ t, C t + K (t + 1) = Y t) (hY : ∀ t, Real.log (Y t) = w t + α * Real.log (K t))
    (hKs : ∀ t, 0 < Ks t) (hCs : ∀ t, 0 < Cs t) (hress : ∀ t, Cs t + Ks (t + 1) = Ys t)
    (hYs : ∀ t, Real.log (Ys t) = ws t + α * Real.log (Ks t))
    (hsave : ∀ t, Ks (t + 1) = α * β * Ys t) (h0 : K 0 = Ks 0) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * Real.log (C t) - ∑ t ∈ range T, β ^ t * Real.log (Cs t) ≤
      1 / (1 - α * β) * ∑ t ∈ range T, β ^ t * (w t - ws t) -
        β ^ T * (α / (1 - α * β)) * (Real.log (K T) - Real.log (Ks T)) := by
  rw [lg_identity hab1 hK hC hres hY, lg_identity hab1 hKs hCs hress hYs, h0]
  have hphi : ∑ t ∈ range T, β ^ t * lgPhi α β (K (t + 1) / Y t) ≤
      ∑ t ∈ range T, β ^ t * lgPhi α β (Ks (t + 1) / Ys t) := by
    refine sum_le_sum fun t _ => ?_
    have hYp : 0 < Y t := by rw [← hres t]; linarith [hC t, hK (t + 1)]
    have hYsp : 0 < Ys t := by rw [← hress t]; linarith [hCs t, hKs (t + 1)]
    have hs : Ks (t + 1) / Ys t = α * β := by rw [hsave t]; field_simp
    rw [hs]
    refine mul_le_mul_of_nonneg_left (lg_phi_le hab0 hab1 (div_pos (hK (t + 1)) hYp) ?_)
      (by positivity)
    rw [div_lt_one hYp, ← hres t]; linarith [hC t]
  have e : ∑ t ∈ range T, β ^ t * (w t - ws t) =
      ∑ t ∈ range T, β ^ t * w t - ∑ t ∈ range T, β ^ t * ws t := by
    rw [← sum_sub_distrib]; congr 1; ext t; ring
  rw [e, mul_sub]
  linarith

/-- A linear growth bound for `a_{t+1} = c_t + α a_t` with `|c_t| ≤ M(1 + t)` and `0 ≤ α < 1`:
`|a_t| ≤ |a₀| + (M/(1 − α))t`. -/
theorem lg_linear_bound {α M : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M) {a c : ℕ → ℝ}
    (hc : ∀ t, |c t| ≤ M * (1 + t)) (ha : ∀ t, a (t + 1) = c t + α * a t) (t : ℕ) :
    |a t| ≤ |a 0| + M / (1 - α) * t := by
  have h1 : 0 < 1 - α := by linarith
  set Q := M / (1 - α) with hQ
  have hQM : M ≤ Q := by rw [hQ, le_div_iff₀ h1]; nlinarith
  have hQeq : M + α * Q = Q := by rw [hQ]; field_simp; ring
  induction t with
  | zero => simp
  | succ n ih =>
    rw [ha n]
    have hQ0 : 0 ≤ Q := le_trans hM hQM
    calc |c n + α * a n| ≤ |c n| + α * |a n| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hα0]
      _ ≤ M * (1 + n) + α * (|a 0| + Q * n) := by gcongr; exact hc n
      _ ≤ |a 0| + Q * ((n : ℝ) + 1) := by
          have : 0 ≤ |a 0| := abs_nonneg _
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith [mul_le_mul_of_nonneg_right hQM hn]
      _ = |a 0| + Q * ((n + 1 : ℕ) : ℝ) := by push_cast; ring

/-- `β^T(P + QT) → 0` for `0 ≤ β < 1`. -/
theorem lg_tendsto_linear {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P Q : ℝ) :
    Tendsto (fun T : ℕ => β ^ T * (P + Q * T)) atTop (𝓝 0) := by
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const P
  have h2 := (tendsto_self_mul_const_pow_of_lt_one hβ0 hβ1).const_mul Q
  have := h1.add h2
  simp only [zero_mul, mul_zero, add_zero] at this
  refine this.congr fun T => ?_
  ring

/-- `Σ_t β^t(P + Qt)` converges for `0 ≤ β < 1`. -/
theorem lg_summable_linear {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P Q : ℝ) :
    Summable (fun t : ℕ => β ^ t * (P + Q * t)) := by
  have hn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1
  have h1 := (summable_geometric_of_lt_one hβ0 hβ1).mul_left P
  have h2 := (summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_left Q
  refine (h1.add h2).congr fun t => ?_
  simp only [pow_one]
  ring

end AKMM.Sustainability
