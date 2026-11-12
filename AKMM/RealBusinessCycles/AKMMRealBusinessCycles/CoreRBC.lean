/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RXCopied
import NeoclassicalGrowth.RBEquilibrium
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The core RBC model: the planner's Bellman equation

AKMM, §14.4.2, (14.8)–(14.11), pp. 422–424.

TFP takes finitely many values `z s` and moves from `s` to `s′` with probability `P s s′`.
Resources are `zF(k, ℓ) + (1 − δ)k`, consumption `c = zF(k, ℓ) + (1 − δ)k − k′`, and
`V(s, k) = max_{k′, ℓ} U(c, 1 − ℓ) + βΣ_{s′}P(s, s′)V(s′, k′)`, attained at `k′ = g(s, k)`,
`ℓ = h(s, k)` with interior choices (`rbc_Bellman`). Partial derivatives are Miao's
`rx_HasPartials` (imported).

* **(14.8)** `zF₂(k, ℓ)U₁ = U₂`, i.e. `zF₂ = U₂/U₁` (`eq_14_8`), from the labour choice.
* **(14.9)** `U₁ = βΣP V₁(s′, k′)` (`eq_14_9`), from the capital choice.
* **(14.10)** the envelope condition `V₁(s, k) = (zF₁ + 1 − δ)U₁` (`eq_14_10`), by comparing
  with the plan that keeps `(k′, ℓ)`.
* **(14.11)** the stochastic Euler equation (`eq_14_11`).
* The printed Bellman equation omits `β`; with it, (14.9) holds with `β`, and the two first-order
  conditions are compatible only if `β = 1` or `U₁ = 0` (`rbc_printed_bellman_beta`).
* Non-vacuity (`rbc_example_bellman`): `U(c, x) = c + ln x`, `F(k, ℓ) = k + ℓ`, `z = 2`,
  `δ = 1`, `β = 1/2`, with `V(k) = 2k + 2(1 − ln 2)`, `g(k) = k`, `h = 1/2`.
* The welfare theorems (p. 423, asserted): for the calibrated utility `(1 − φ)ln c + φ ln(1 − ℓ)`
  and Cobb–Douglas technology they are Miao's `rb_sce_iff` and `rb_sce_optimal` (imported), whose
  utility `ln c + χ ln(1 − ℓ)` is a positive multiple of the calibrated one with
  `χ = φ/(1 − φ)` (`rbc_calib_utility`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology Miao.NeoclassicalGrowth

variable {S : Type*} [Fintype S]

/-- Resources `zF(k, ℓ) + (1 − δ)k`. -/
def rbcRes (F : ℝ × ℝ → ℝ) (δ z k ℓ : ℝ) : ℝ := z * F (k, ℓ) + (1 - δ) * k

/-- The Bellman equation of the core RBC planner (AKMM, p. 423, with the discount factor `β`):
at every `k > 0` the policy `(g, h)` is interior (`g > 0`, `0 < h < 1`, positive consumption),
attains the maximum, and `V` is the maximum value. -/
def rbc_Bellman (U F : ℝ × ℝ → ℝ) (β δ : ℝ) (z : S → ℝ) (P : S → S → ℝ) (V g h : S → ℝ → ℝ) :
    Prop :=
  ∀ s k, 0 < k → (0 < g s k ∧ 0 < h s k ∧ h s k < 1 ∧ g s k < rbcRes F δ (z s) k (h s k)) ∧
    V s k = U (rbcRes F δ (z s) k (h s k) - g s k, 1 - h s k) +
      β * ∑ s', P s s' * V s' (g s k) ∧
    ∀ k' ℓ', 0 < k' → 0 < ℓ' → ℓ' < 1 → k' < rbcRes F δ (z s) k ℓ' →
      U (rbcRes F δ (z s) k ℓ' - k', 1 - ℓ') + β * ∑ s', P s s' * V s' k' ≤ V s k

/-- **AKMM, (14.8), p. 423: the intratemporal condition.** If `U` has partials `(U₁, U₂)` at
`(c, 1 − ℓ)` and `F` has partials `(F₁, F₂)` at `(k, ℓ)` (the policy at `(s, k)`), then
`zF₂(k, ℓ)U₁ = U₂`; so `zF₂ = U₂/U₁` when `U₁ ≠ 0`. -/
theorem eq_14_8 {U F : ℝ × ℝ → ℝ} {β δ : ℝ} {z : S → ℝ} {P : S → S → ℝ} {V g h : S → ℝ → ℝ}
    (hB : rbc_Bellman U F β δ z P V g h) {s : S} {k : ℝ} (hk : 0 < k) {U1 U2 F1 F2 : ℝ}
    (hU : rx_HasPartials U U1 U2 (rbcRes F δ (z s) k (h s k) - g s k, 1 - h s k))
    (hF : rx_HasPartials F F1 F2 (k, h s k)) :
    z s * F2 * U1 = U2 ∧ (U1 ≠ 0 → z s * F2 = U2 / U1) := by
  obtain ⟨⟨hg0, hh0, hh1, hgc⟩, hval, hle⟩ := hB s k hk
  set ℓ := h s k
  set k' := g s k
  -- the resources along the labour choice
  have hFℓ : HasDerivAt (fun x => F (k, x)) F2 ℓ := by
    have := hF.comp (x := fun _ => k) (y := id) (hasDerivAt_const ℓ k) (hasDerivAt_id ℓ)
    simpa using this
  have hres : HasDerivAt (fun x => rbcRes F δ (z s) k x - k') (z s * F2) ℓ := by
    have := (hFℓ.const_mul (z s)).add_const ((1 - δ) * k) |>.sub_const k'
    simpa [rbcRes] using this
  have hleis : HasDerivAt (fun x : ℝ => 1 - x) (-1) ℓ := by
    simpa using (hasDerivAt_id ℓ).const_sub 1
  have hd : HasDerivAt (fun x => U (rbcRes F δ (z s) k x - k', 1 - x))
      (U1 * (z s * F2) + U2 * (-1)) ℓ := hU.comp hres hleis
  have hpos : (0 : ℝ) < rbcRes F δ (z s) k ℓ - k' := by linarith
  have hmax : IsLocalMax (fun x => U (rbcRes F δ (z s) k x - k', 1 - x)) ℓ := by
    filter_upwards [lt_mem_nhds hh0, gt_mem_nhds hh1,
      continuousAt_const.eventually_lt hres.continuousAt hpos] with x h1 h2 h3
    have := hle k' x hg0 h1 h2 (by linarith)
    rw [hval] at this
    linarith
  have h0 := hmax.hasDerivAt_eq_zero hd
  refine ⟨by linarith, fun hU1 => ?_⟩
  field_simp
  linarith

/-- **AKMM, (14.9), p. 423: the capital choice.** If `U` has partials `(U₁, U₂)` at the optimum
and each `V(s′, ·)` is differentiable at `k′ = g(s, k)` with derivative `V₁(s′)`, then
`U₁ = βΣ_{s′}P(s, s′)V₁(s′)`. -/
theorem eq_14_9 {U F : ℝ × ℝ → ℝ} {β δ : ℝ} {z : S → ℝ} {P : S → S → ℝ} {V g h : S → ℝ → ℝ}
    (hB : rbc_Bellman U F β δ z P V g h) {s : S} {k : ℝ} (hk : 0 < k) {U1 U2 : ℝ}
    (hU : rx_HasPartials U U1 U2 (rbcRes F δ (z s) k (h s k) - g s k, 1 - h s k))
    {V1 : S → ℝ} (hV : ∀ s', HasDerivAt (V s') (V1 s') (g s k)) :
    U1 = β * ∑ s', P s s' * V1 s' := by
  obtain ⟨⟨hg0, hh0, hh1, hgc⟩, hval, hle⟩ := hB s k hk
  set ℓ := h s k
  set k' := g s k
  set R := rbcRes F δ (z s) k ℓ
  have hc : HasDerivAt (fun x => R - x) (-1) k' := by simpa using (hasDerivAt_id k').const_sub R
  have hU' : HasDerivAt (fun x => U (R - x, 1 - ℓ)) (U1 * (-1) + U2 * 0) k' :=
    hU.comp (x := fun x => R - x) (y := fun _ => 1 - ℓ) hc (hasDerivAt_const k' _)
  have hsum : HasDerivAt (fun x => ∑ s', P s s' * V s' x) (∑ s', P s s' * V1 s') k' :=
    HasDerivAt.fun_sum (u := Finset.univ) fun s' _ => (hV s').const_mul (P s s')
  have hd := hU'.add (hsum.const_mul β)
  have hmax : IsLocalMax (fun x => U (R - x, 1 - ℓ) + β * ∑ s', P s s' * V s' x) k' := by
    filter_upwards [lt_mem_nhds hg0, gt_mem_nhds hgc] with x h1 h2
    have := hle x ℓ h1 hh0 hh1 h2
    rw [hval] at this
    exact this
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- **AKMM, (14.10), p. 423: the envelope condition.** If `V(s, ·)` is differentiable at `k`
with derivative `V₁`, `U` has partials `(U₁, U₂)` at the optimum and `F` has partials
`(F₁, F₂)` at `(k, ℓ)`, then `V₁ = (zF₁(k, ℓ) + 1 − δ)U₁`. -/
theorem eq_14_10 {U F : ℝ × ℝ → ℝ} {β δ : ℝ} {z : S → ℝ} {P : S → S → ℝ} {V g h : S → ℝ → ℝ}
    (hB : rbc_Bellman U F β δ z P V g h) {s : S} {k : ℝ} (hk : 0 < k) {U1 U2 F1 F2 V1 : ℝ}
    (hU : rx_HasPartials U U1 U2 (rbcRes F δ (z s) k (h s k) - g s k, 1 - h s k))
    (hF : rx_HasPartials F F1 F2 (k, h s k)) (hV : HasDerivAt (V s) V1 k) :
    V1 = (z s * F1 + 1 - δ) * U1 := by
  obtain ⟨⟨hg0, hh0, hh1, hgc⟩, hval, -⟩ := hB s k hk
  set ℓ := h s k
  set k' := g s k
  set W := β * ∑ s', P s s' * V s' k'
  have hFk : HasDerivAt (fun j => F (j, ℓ)) F1 k := by
    have := hF.comp (x := id) (y := fun _ => ℓ) (hasDerivAt_id k) (hasDerivAt_const k ℓ)
    simpa using this
  have hres : HasDerivAt (fun j => rbcRes F δ (z s) j ℓ - k') (z s * F1 + (1 - δ)) k := by
    have := ((hFk.const_mul (z s)).add ((hasDerivAt_id k).const_mul (1 - δ))).sub_const k'
    simpa [rbcRes] using this
  have hd1 : HasDerivAt (fun j => U (rbcRes F δ (z s) j ℓ - k', 1 - ℓ))
      (U1 * (z s * F1 + (1 - δ)) + U2 * 0) k :=
    hU.comp hres (hasDerivAt_const k _)
  have hd : HasDerivAt (fun j => V s j - (U (rbcRes F δ (z s) j ℓ - k', 1 - ℓ) + W))
      (V1 - (U1 * (z s * F1 + (1 - δ)) + U2 * 0)) k := hV.sub (hd1.add_const W)
  have hpos : (0 : ℝ) < rbcRes F δ (z s) k ℓ - k' := by linarith
  have hmin : IsLocalMin (fun j => V s j - (U (rbcRes F δ (z s) j ℓ - k', 1 - ℓ) + W)) k := by
    filter_upwards [lt_mem_nhds hk, continuousAt_const.eventually_lt hres.continuousAt hpos]
      with j hj hj'
    have := (hB s j hj).2.2 k' ℓ hg0 hh0 hh1 (by linarith)
    have h0 : V s k - (U (rbcRes F δ (z s) k ℓ - k', 1 - ℓ) + W) = 0 := by rw [hval]; ring
    change V s k - _ ≤ V s j - _
    rw [h0]
    linarith
  have := hmin.hasDerivAt_eq_zero hd
  linarith

/-- **AKMM, (14.11), p. 423: the stochastic Euler equation.** With partial derivatives `U₁, U₂`
of `U` at every optimum and `F₁, F₂` of `F` at every `(k, h(s, k))`, and `V(s, ·)`
differentiable with derivative `V₁(s, ·)` on `(0, ∞)`:
`U₁(s, k) = βΣ_{s′}P(s, s′)(z(s′)F₁(s′, k′) + 1 − δ)U₁(s′, k′)`, `k′ = g(s, k)`. -/
theorem eq_14_11 {U F : ℝ × ℝ → ℝ} {β δ : ℝ} {z : S → ℝ} {P : S → S → ℝ} {V g h : S → ℝ → ℝ}
    (hB : rbc_Bellman U F β δ z P V g h) {U1 U2 F1 F2 V1 : S → ℝ → ℝ}
    (hU : ∀ s k, 0 < k →
      rx_HasPartials U (U1 s k) (U2 s k) (rbcRes F δ (z s) k (h s k) - g s k, 1 - h s k))
    (hF : ∀ s k, 0 < k → rx_HasPartials F (F1 s k) (F2 s k) (k, h s k))
    (hV : ∀ s k, 0 < k → HasDerivAt (V s) (V1 s k) k) {s : S} {k : ℝ} (hk : 0 < k) :
    U1 s k = β * ∑ s', P s s' * ((z s' * F1 s' (g s k) + 1 - δ) * U1 s' (g s k)) := by
  have hg := (hB s k hk).1.1
  rw [eq_14_9 hB hk (hU s k hk) (fun s' => hV s' (g s k) hg)]
  congr 1
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [eq_14_10 hB hg (hU s' _ hg) (hF s' _ hg) (hV s' _ hg)]

/-- AKMM, p. 423: the printed Bellman equation has no discount factor; its first-order condition
for capital is `U₁ = ΣP V₁` (`eq_14_9` with `β = 1`), and it is compatible with the printed
(14.9) `U₁ = βΣP V₁` only if `β = 1` or `U₁ = 0`. -/
theorem rbc_printed_bellman_beta {β U1 EV : ℝ} (hprinted : U1 = EV) (h149 : U1 = β * EV) :
    β = 1 ∨ U1 = 0 := by
  rcases eq_or_ne U1 0 with h | h
  · exact Or.inr h
  · left
    have hEV : EV ≠ 0 := hprinted ▸ h
    have : β * EV = 1 * EV := by rw [← h149, one_mul, hprinted]
    exact mul_right_cancel₀ hEV this

/-- Non-vacuity of `rbc_Bellman`: with one TFP state, `U(c, x) = c + ln x`, `F(k, ℓ) = k + ℓ`,
`z = 2`, `δ = 1` and `β = 1/2`, the value `V(k) = 2k + 2(1 − ln 2)` with policies `g(k) = k`,
`h = 1/2` solves the Bellman equation. -/
theorem rbc_example_bellman :
    rbc_Bellman (S := Unit) (fun p => p.1 + Real.log p.2) (fun p => p.1 + p.2) (1 / 2) 1
      (fun _ => 2) (fun _ _ => 1) (fun _ k => 2 * k + 2 * (1 - Real.log 2)) (fun _ k => k)
      (fun _ _ => 1 / 2) := by
  intro s k hk
  simp only [rbcRes, Finset.univ_unique, Finset.sum_singleton, one_mul, sub_self, zero_mul,
    add_zero]
  have hl2 : Real.log (1 - 1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
  refine ⟨⟨hk, by norm_num, by norm_num, by linarith⟩, by rw [hl2]; ring, ?_⟩
  intro k' ℓ' _ _ hℓ1 _
  have ht := rb_log_tangent (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 0 < 1 - ℓ')
  rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]] at ht
  linarith

/-- AKMM, p. 428: the calibrated utility `(1 − φ)ln c + φ ln(1 − ℓ)` is `(1 − φ)` times Miao's
`rb_u χ = ln c + χ ln(1 − ℓ)` with `χ = φ/(1 − φ)`; so it ranks allocations as `rb_u χ` does,
and Miao's welfare theorems `rb_sce_iff`, `rb_sce_optimal` apply to the calibrated model. -/
theorem rbc_calib_utility {φ c ℓ : ℝ} (hφ : φ < 1) :
    (1 - φ) * Real.log c + φ * Real.log (1 - ℓ) = (1 - φ) * rb_u (φ / (1 - φ)) c ℓ ∧
      ∀ c' ℓ', ((1 - φ) * Real.log c' + φ * Real.log (1 - ℓ') ≤
        (1 - φ) * Real.log c + φ * Real.log (1 - ℓ) ↔
        rb_u (φ / (1 - φ)) c' ℓ' ≤ rb_u (φ / (1 - φ)) c ℓ) := by
  have h1 : 0 < 1 - φ := by linarith
  have e : ∀ c ℓ, (1 - φ) * Real.log c + φ * Real.log (1 - ℓ) =
      (1 - φ) * rb_u (φ / (1 - φ)) c ℓ := fun c ℓ => by
    unfold rb_u; field_simp
  refine ⟨e c ℓ, fun c' ℓ' => ?_⟩
  rw [e, e]
  exact mul_le_mul_iff_of_pos_left h1

end AKMM.RealBusinessCycles
