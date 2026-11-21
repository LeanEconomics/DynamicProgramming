/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSolow.Production
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Business cycles in the Solow model: variants and impulse responses

AKMM, §3.5, pp. 88–92.

* **Variants** (§3.5.1): the RBC law of motion reduces to (3.5) with constant saving, labour and
  technology (`solow_rbc_reduces`); Harrod- and Hicks-neutral Cobb–Douglas technology coincide
  with `Ã = A^{1−α}` (`solow_harrod_hicks_cobbDouglas`); the investment-specific law
  `k_{t+1} = sν_t F(k_t, ℓ) + (1 − δ)k_t` from `y = c + i/ν` (`solow_investment_specific`); demand
  shocks: `c + i = c/(1 − s)`, the law of motion, and the unemployment rate is determined by
  `(c, k)` (`solow_demand_shock`, `solow_demand_unemployment_unique`).
* **Impulse responses** (§3.5.2): the steady state (3.17) with its Cobb–Douglas closed form
  (`eq_3_17`); the exact log form of (3.14) in deviations `k̂, Â` (`solow_irf_log_form`); the
  log-linear law (3.18) as the exact partial derivatives of that map at the steady state
  (`eq_3_18`); the closed-form solution of the linear recursion, as the book's sum and as a
  geometric expression (`solow_irf_capital_sum`, `solow_irf_capital_closed_form`); the output
  response, corrected (`solow_irf_output`) with a counterexample to the printed formula
  (`solow_irf_output_printed_false`); the level linearisation `g_k = 1 − δ(1 − α)`,
  `g_A = s^{1/(1−α)} δ^{−α/(1−α)} A^{α/(1−α)}` (`solow_level_linearisation`).

Only the linear recursion (3.18) is solved; "the log-linear approximation performs well" and the
figure's numbers are numerical claims and are not formalised.
-/

namespace AKMM.Solow

open Filter Topology

/-- AKMM, §3.5.1, p. 89: the RBC law of motion `k_{t+1} = (1 − δ)k_t + s(k_t, A_t) A_t F(k_t,
ℓ(k_t, A_t))` is the fundamental equation (3.5) when saving and labour are constant (`ℓ = 1`)
and `A_t = 1`. -/
theorem solow_rbc_reduces {F : ℝ → ℝ → ℝ} {δ s : ℝ} (sfun ℓfun : ℝ → ℝ → ℝ)
    (hs : ∀ k A, sfun k A = s) (hℓ : ∀ k A, ℓfun k A = 1) (k : ℝ) :
    (1 - δ) * k + sfun k 1 * 1 * F k (ℓfun k 1) = (1 - δ) * k + s * intensive F k := by
  rw [hs, hℓ, mul_one]
  rfl

/-- AKMM, p. 89: with Cobb–Douglas production the Harrod-neutral form `k^α (Aℓ)^{1−α}` equals the
Hicks-neutral form `Ã k^α ℓ^{1−α}` with `Ã = A^{1−α}`. -/
theorem solow_harrod_hicks_cobbDouglas {α A k ℓ : ℝ} (hA : 0 ≤ A) (hℓ : 0 ≤ ℓ) :
    k ^ α * (A * ℓ) ^ (1 - α) = A ^ (1 - α) * (k ^ α * ℓ ^ (1 - α)) := by
  rw [Real.mul_rpow hA hℓ]
  ring

/-- AKMM, §3.5.1, p. 89 (investment-specific technology): with `y = c + i/ν`, consumption
`c = (1 − s)y` and `k_{t+1} = i_t + (1 − δ)k_t`, the law of motion is
`k_{t+1} = sν_t F(k_t, ℓ) + (1 − δ)k_t`; with `ν = 1` it is (3.5). -/
theorem solow_investment_specific {F : ℝ → ℝ → ℝ} {s δ ℓ : ℝ} {k c i y ν : ℕ → ℝ} {t : ℕ}
    (hν : ν t ≠ 0) (hy : y t = F (k t) ℓ) (hres : y t = c t + i t / ν t)
    (hc : c t = (1 - s) * y t) (hk : k (t + 1) = i t + (1 - δ) * k t) :
    k (t + 1) = s * ν t * F (k t) ℓ + (1 - δ) * k t := by
  have hi : i t = s * ν t * y t := by
    have : i t / ν t = s * y t := by rw [hc] at hres; linarith
    field_simp at this
    linarith
  rw [hk, hi, hy]

/-- AKMM, §3.5.1, pp. 89–90 (demand shocks): if `i_t/c_t = s/(1 − s)` then total demand is
`c_t + i_t = c_t/(1 − s)`; when output is demand-determined, `y_t = c_t/(1 − s) =
F(k_t, ℓ(1 − u_t))`, and `k_{t+1} = i_t + (1 − δ)k_t` gives
`k_{t+1} = s F(k_t, ℓ(1 − u_t)) + (1 − δ)k_t`. -/
theorem solow_demand_shock {F : ℝ → ℝ → ℝ} {s δ ℓ : ℝ} {k c i u : ℕ → ℝ} {t : ℕ} (hs1 : s < 1)
    (hc : c t ≠ 0) (hic : i t / c t = s / (1 - s))
    (hy : c t / (1 - s) = F (k t) (ℓ * (1 - u t))) (hk : k (t + 1) = i t + (1 - δ) * k t) :
    c t + i t = c t / (1 - s) ∧ k (t + 1) = s * F (k t) (ℓ * (1 - u t)) + (1 - δ) * k t := by
  have h1s : (1 - s) ≠ 0 := ne_of_gt (by linarith)
  have hi : i t = s / (1 - s) * c t := by
    rw [div_eq_iff hc] at hic
    exact hic
  refine ⟨by rw [hi]; field_simp; ring, ?_⟩
  rw [hk, ← hy, hi]
  ring

/-- AKMM, p. 90: "`u_t` can be represented as a function of `c_t` and `k_t`": since `F` is
strictly increasing in labour, at most one unemployment rate `u < 1` clears
`c/(1 − s) = F(k, ℓ(1 − u))`. -/
theorem solow_demand_unemployment_unique {F : ℝ → ℝ → ℝ} (hF : SolowAssumptions F)
    {s ℓ c k u₁ u₂ : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) (hu₁ : u₁ < 1) (hu₂ : u₂ < 1)
    (h₁ : c / (1 - s) = F k (ℓ * (1 - u₁))) (h₂ : c / (1 - s) = F k (ℓ * (1 - u₂))) :
    u₁ = u₂ := by
  have hp₁ : ℓ * (1 - u₁) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (mul_pos hℓ (by linarith))
  have hp₂ : ℓ * (1 - u₂) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (mul_pos hℓ (by linarith))
  have := (hF.mono_labour k hk).injOn hp₁ hp₂ (h₁.symm.trans h₂)
  have := mul_left_cancel₀ (ne_of_gt hℓ) this
  linarith

/-- AKMM, (3.17), p. 92: the steady state of (3.14) at `A = Ā`, `k̄ = (sĀℓ^{1−α}/δ)^{1/(1−α)}`,
solves `k̄ = sĀk̄^α ℓ^{1−α} + (1 − δ)k̄`, i.e. `δk̄ = sĀk̄^α ℓ^{1−α}`. -/
theorem eq_3_17 {α s δ A ℓ : ℝ} (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ) (hA : 0 < A)
    (hℓ : 0 < ℓ) :
    δ * (s * A * ℓ ^ (1 - α) / δ) ^ (1 / (1 - α)) =
        s * A * ((s * A * ℓ ^ (1 - α) / δ) ^ (1 / (1 - α))) ^ α * ℓ ^ (1 - α) ∧
      (s * A * ℓ ^ (1 - α) / δ) ^ (1 / (1 - α)) =
        s * A * ((s * A * ℓ ^ (1 - α) / δ) ^ (1 / (1 - α))) ^ α * ℓ ^ (1 - α) +
          (1 - δ) * (s * A * ℓ ^ (1 - α) / δ) ^ (1 / (1 - α)) := by
  set b := s * A * ℓ ^ (1 - α) / δ with hb
  have hbpos : 0 < b := by positivity
  set k := b ^ (1 / (1 - α)) with hk
  have hkpos : 0 < k := Real.rpow_pos_of_pos hbpos _
  have h1α : (1 - α) ≠ 0 := ne_of_gt (by linarith)
  have hpow : k ^ (1 - α) = b := by
    rw [hk, ← Real.rpow_mul hbpos.le, one_div, inv_mul_cancel₀ h1α, Real.rpow_one]
  have hsplit : k = k ^ (1 - α) * k ^ α := by
    rw [← Real.rpow_add hkpos, sub_add_cancel, Real.rpow_one]
  have key : δ * k = s * A * k ^ α * ℓ ^ (1 - α) := by
    conv_lhs => rw [hsplit, hpow, hb]
    field_simp
  exact ⟨key, by linarith⟩

/-- AKMM, p. 92: writing `k_t = k̄ e^{k̂_t}` and `A_t = Ā e^{Â_t}` (3.15) and using
`δk̄ = sĀk̄^α ℓ^{1−α}` (3.17), the right side of (3.14) is exactly
`k̄ (δ e^{Â_t + αk̂_t} + (1 − δ) e^{k̂_t})`; so (3.14) is
`k̂_{t+1} = log(δ e^{Â_t + αk̂_t} + (1 − δ) e^{k̂_t})`. -/
theorem solow_irf_log_form {α s δ A ℓ kbar kh ah : ℝ} (hk : 0 < kbar)
    (hss : δ * kbar = s * A * kbar ^ α * ℓ ^ (1 - α)) :
    s * (A * Real.exp ah) * (kbar * Real.exp kh) ^ α * ℓ ^ (1 - α) +
        (1 - δ) * (kbar * Real.exp kh) =
      kbar * (δ * Real.exp (ah + α * kh) + (1 - δ) * Real.exp kh) := by
  rw [Real.mul_rpow hk.le (Real.exp_pos kh).le, ← Real.exp_mul, Real.exp_add]
  have : s * (A * Real.exp ah) * (kbar ^ α * Real.exp (kh * α)) * ℓ ^ (1 - α) =
      (s * A * kbar ^ α * ℓ ^ (1 - α)) * (Real.exp ah * Real.exp (kh * α)) := by ring
  rw [this, ← hss, mul_comm kh α]
  ring

/-- AKMM, (3.18), p. 92: the map `(k̂, Â) ↦ log(δ e^{Â + αk̂} + (1 − δ) e^{k̂})` of
`solow_irf_log_form` vanishes at the steady state and its partial derivatives there are
`1 − δ(1 − α)` in `k̂` and `δ` in `Â`; the first-order approximation is
`k̂_{t+1} = (1 − δ(1 − α))k̂_t + δÂ_t`. -/
theorem eq_3_18 {α δ : ℝ} :
    Real.log (δ * Real.exp (0 + α * 0) + (1 - δ) * Real.exp 0) = 0 ∧
      HasDerivAt (fun x => Real.log (δ * Real.exp (0 + α * x) + (1 - δ) * Real.exp x))
        (1 - δ * (1 - α)) 0 ∧
      HasDerivAt (fun a => Real.log (δ * Real.exp (a + α * 0) + (1 - δ) * Real.exp 0)) δ 0 := by
  refine ⟨by simp, ?_, ?_⟩
  · have hin : HasDerivAt (fun x => δ * Real.exp (0 + α * x) + (1 - δ) * Real.exp x)
        (δ * (Real.exp (0 + α * 0) * (α * 1)) + (1 - δ) * Real.exp 0) 0 := by
      have h1 : HasDerivAt (fun x : ℝ => 0 + α * x) (α * 1) 0 :=
        ((hasDerivAt_id' 0).const_mul α).const_add 0
      exact (h1.exp.const_mul δ).add ((Real.hasDerivAt_exp 0).const_mul (1 - δ))
    have h := hin.log (by simp)
    convert h using 1
    simp
    ring
  · have hin : HasDerivAt (fun a => δ * Real.exp (a + α * 0) + (1 - δ) * Real.exp 0)
        (δ * (Real.exp (0 + α * 0) * 1)) 0 := by
      have h1 : HasDerivAt (fun a : ℝ => a + α * 0) 1 0 := (hasDerivAt_id' 0).add_const _
      exact (h1.exp.const_mul δ).add_const _
    have h := hin.log (by simp)
    convert h using 1
    simp

/-- AKMM, p. 92: the impulse response of (3.18) with `k̂₀ = 0`, `Â_t = ρ^t ε`:
`k̂_{t+1} = Σ_{τ=0}^{t} ρ^{t−τ}(1 − λ)^τ δε`. -/
theorem solow_irf_capital_sum {lam δ ρ ε : ℝ} {x : ℕ → ℝ} (h0 : x 0 = 0)
    (hx : ∀ t, x (t + 1) = (1 - lam) * x t + δ * (ρ ^ t * ε)) (t : ℕ) :
    x (t + 1) = ∑ τ ∈ Finset.range (t + 1), ρ ^ (t - τ) * (1 - lam) ^ τ * (δ * ε) := by
  induction t with
  | zero => rw [hx, h0]; simp
  | succ u ih =>
    rw [hx, ih, Finset.sum_range_succ' _ (u + 1), Finset.mul_sum]
    simp only [Nat.sub_zero, pow_zero, mul_one, Nat.add_sub_add_right, pow_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro τ _
      ring
    · ring

/-- AKMM, p. 92: the closed form
`k̂_{t+1} = ρ^t (1 − ((1 − λ)/ρ)^{t+1})/(1 − (1 − λ)/ρ) · δε`, for `ρ ≠ 0` and `ρ ≠ 1 − λ`. -/
theorem solow_irf_capital_closed_form {lam δ ρ ε : ℝ} {x : ℕ → ℝ} (hρ : ρ ≠ 0)
    (hq : (1 - lam) / ρ ≠ 1) (h0 : x 0 = 0)
    (hx : ∀ t, x (t + 1) = (1 - lam) * x t + δ * (ρ ^ t * ε)) (t : ℕ) :
    x (t + 1) = ρ ^ t * ((1 - ((1 - lam) / ρ) ^ (t + 1)) / (1 - (1 - lam) / ρ)) * (δ * ε) := by
  have hq' : 1 - (1 - lam) / ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  set q := (1 - lam) / ρ with hqdef
  have hl : 1 - lam = q * ρ := by rw [hqdef]; field_simp
  induction t with
  | zero => rw [hx, h0]; field_simp; ring
  | succ u ih =>
    rw [hx, ih, hl]
    field_simp
    ring

/-- AKMM, p. 92, corrected: the output response `ŷ_t = Â_t + αk̂_t` is `ŷ₀ = ε` and, for
`t ≥ 1`, `ŷ_t = ρ^t ε (1 + (αδ/ρ)(1 − q^t)/(1 − q))` with `q = (1 − λ)/ρ`. The first term is
`ρ^t ε`, since `Â_t = ρ^t ε`. -/
theorem solow_irf_output {α lam δ ρ ε : ℝ} {x : ℕ → ℝ} (hρ : ρ ≠ 0)
    (hq : (1 - lam) / ρ ≠ 1) (h0 : x 0 = 0)
    (hx : ∀ t, x (t + 1) = (1 - lam) * x t + δ * (ρ ^ t * ε)) (t : ℕ) :
    ρ ^ 0 * ε + α * x 0 = ε ∧
      ρ ^ (t + 1) * ε + α * x (t + 1) =
        ρ ^ (t + 1) * ε * (1 + α * δ / ρ * ((1 - ((1 - lam) / ρ) ^ (t + 1)) /
          (1 - (1 - lam) / ρ))) := by
  refine ⟨by rw [h0]; ring, ?_⟩
  rw [solow_irf_capital_closed_form hρ hq h0 hx t, pow_succ]
  field_simp

/-- AKMM, p. 92, the printed formula `ŷ_t = ρ^t (1 + (α/ρ)(1 − q^t)/(1 − q)) δε` is false: at
`t = 1` the true response is `ρε + αδε` and the printed one is `ρδε + αδε`; they differ whenever
`δ ≠ 1`, `ρ ≠ 0`, `ε ≠ 0`. -/
theorem solow_irf_output_printed_false {α lam δ ρ ε : ℝ} {x : ℕ → ℝ} (hρ : ρ ≠ 0) (hε : ε ≠ 0)
    (hδ1 : δ ≠ 1) (hq : (1 - lam) / ρ ≠ 1) (h0 : x 0 = 0)
    (hx : ∀ t, x (t + 1) = (1 - lam) * x t + δ * (ρ ^ t * ε)) :
    ρ ^ 1 * ε + α * x 1 ≠
      ρ ^ 1 * (1 + α / ρ * ((1 - ((1 - lam) / ρ) ^ 1) / (1 - (1 - lam) / ρ))) * (δ * ε) := by
  have hq' : 1 - (1 - lam) / ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hx1 : x 1 = δ * ε := by rw [hx 0, h0]; ring
  rw [hx1, pow_one, pow_one, div_self hq', mul_one]
  intro h
  field_simp at h
  have : ρ * (1 - δ) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hρ h1
  · exact hδ1 (by linarith)

/-- AKMM, p. 92: for `g(k, A) = (1 − δ)k + sA k^α` at the steady state
`k̄ = (sA/δ)^{1/(1−α)}`, the partial derivatives are `g_k = 1 − δ(1 − α)` and
`g_A = s^{1/(1−α)} δ^{−α/(1−α)} A^{α/(1−α)}`, so `Δk_{t+1} = g_k Δk_t + g_A ΔA_t`. -/
theorem solow_level_linearisation {α s δ A : ℝ} (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ)
    (hA : 0 < A) :
    HasDerivAt (fun k => (1 - δ) * k + s * A * k ^ α) (1 - δ * (1 - α))
        ((s * A / δ) ^ (1 / (1 - α))) ∧
      HasDerivAt (fun a => (1 - δ) * (s * A / δ) ^ (1 / (1 - α)) +
          s * a * ((s * A / δ) ^ (1 / (1 - α))) ^ α)
        (s ^ (1 / (1 - α)) * δ ^ (-(α / (1 - α))) * A ^ (α / (1 - α))) A := by
  set k := (s * A / δ) ^ (1 / (1 - α)) with hk
  have hb : 0 < s * A / δ := by positivity
  have hkpos : 0 < k := Real.rpow_pos_of_pos hb _
  have h1α : (1 - α) ≠ 0 := ne_of_gt (by linarith)
  have hpow : k ^ (1 - α) = s * A / δ := by
    rw [hk, ← Real.rpow_mul hb.le, one_div, inv_mul_cancel₀ h1α, Real.rpow_one]
  have hsplit : k = k ^ (1 - α) * k ^ α := by
    rw [← Real.rpow_add hkpos, sub_add_cancel, Real.rpow_one]
  have hss : s * A * k ^ α = δ * k := by
    conv_rhs => rw [hsplit, hpow]
    field_simp
  refine ⟨?_, ?_⟩
  · have hd := ((hasDerivAt_id' k).const_mul (1 - δ)).add
      ((Real.hasDerivAt_rpow_const (p := α) (Or.inl (ne_of_gt hkpos))).const_mul (s * A))
    convert hd using 1
    rw [Real.rpow_sub_one (ne_of_gt hkpos)]
    have : s * A * (α * (k ^ α / k)) = α * (s * A * k ^ α) / k := by ring
    rw [this, hss]
    field_simp
    ring
  · have hd := ((hasDerivAt_id' A).const_mul s).mul_const (k ^ α) |>.const_add ((1 - δ) * k)
    convert hd using 1
    rw [mul_one, hk, ← Real.rpow_mul hb.le, Real.div_rpow (by positivity) hδ.le,
      Real.mul_rpow hs.le hA.le, Real.rpow_neg hδ.le]
    have hs' : s ^ (1 / (1 - α)) = s * s ^ (α / (1 - α)) := by
      rw [show (1 / (1 - α)) = 1 + α / (1 - α) by field_simp; ring, Real.rpow_add hs,
        Real.rpow_one]
    rw [hs', show 1 / (1 - α) * α = α / (1 - α) by ring]
    field_simp

end AKMM.Solow
