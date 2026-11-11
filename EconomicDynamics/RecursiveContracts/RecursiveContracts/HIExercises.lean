/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.HIOptimal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exercises 22.3 and 22.4

Miao, §22.4, pp. 798–799.

**Exercise 22.4** (CARA utility `u(c) = −exp(−γc)`). Shifting every transfer by `k` multiplies
every utility by `e^{−γk}`, so `(c, w) ↦ (c + k, e^{−γk} w)` maps the contracts feasible at `v`
onto those feasible at `e^{−γk} v` (`hi_cara_scale_feasible`) and the Bellman operator commutes
with `f ↦ f(e^{−γk} ·) + k/(1 − β)` (`hi_T_scaleFn`). By uniqueness of the fixed point
(Proposition 22.3.1) `P(e^{−γk} v) = P(v) − k/(1 − β)` (`hi_cara_P_scale`), hence
`P(v) = [ln(−v) + K]/(γ(1 − β))` (`ex_22_4_value`). Optimal contracts rescale
(`hi_cara_optimal_scale`), so `cᵢ(v) = −(1/γ) ln(−aᵢ v)`, `wᵢ(v) = dᵢ v` with
`0 < aᵢ₋₁ ≤ aᵢ`, `dᵢ₋₁ ≥ dᵢ > 0`, `Σ πᵢ/dᵢ = 1`, `Σ πᵢ (e^{−γθᵢ} aᵢ + β dᵢ) = 1` and
`K = Σ πᵢ ln aᵢ + β/(1 − β) Σ πᵢ ln dᵢ` (`ex_22_4`).

The book prints the form with a constant `A = Σ πᵢ/aᵢ`: `cᵢ = −(1/γ) ln(−aᵢ(v + A))`,
`wᵢ = dᵢ v + (dᵢ − 1)A`, `P(v) = [ln(−v − A) + K]/(γ(1 − β))`. Promise keeping forces `A = 0`
(`hi_ex_22_4_A_eq_zero`), which contradicts `A = Σ πᵢ/aᵢ > 0`
(`ex_22_4_printed_inconsistent`).

**Exercise 22.3** (`β → 1`). Not formalised as a limit; `ex_22_3_upper` proves the half that
follows from (22.26), and `hi_normalized_bounds` shows that in per-period terms both bounds of
(22.26) are independent of `β`, so they cannot settle the limit.
-/

namespace Miao.RecursiveContracts

open Finset Filter Topology

/-- `u(x + k) = e^{−γk} u(x)` for CARA utility. -/
theorem hi_cara_shift (γ x k : ℝ) : hi_cara γ (x + k) = Real.exp (-γ * k) * hi_cara γ x := by
  unfold hi_cara
  rw [show -γ * (x + k) = -γ * k + -γ * x by ring, Real.exp_add]; ring

/-- With CARA utility, `vmax = 0`. -/
theorem hi_cara_vmax (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) :
    hi_vmax M = 0 := by
  unfold hi_vmax hi_ubar; rw [hu, hi_cara_sSup hγ, zero_div]

/-- Exercise 22.4: `(c, w) ↦ (c + k, e^{−γk} w)` maps contracts feasible at `v` to contracts
feasible at `e^{−γk} v`. -/
theorem hi_cara_scale_feasible (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ)
    (k : ℝ) {v : ℝ} {c w : Fin (M.N + 1) → ℝ} (h : hi_Feasible M v c w) :
    hi_Feasible M (Real.exp (-γ * k) * v) (fun i => c i + k)
      (fun i => Real.exp (-γ * k) * w i) := by
  obtain ⟨hic, hpk, hw⟩ := h
  have he := Real.exp_pos (-γ * k)
  have hv := hi_cara_vmax M hγ hu
  refine ⟨fun i j => ?_, ?_, fun i => ?_⟩
  · have hC : hi_C M (fun i => c i + k) (fun i => Real.exp (-γ * k) * w i) i j =
        Real.exp (-γ * k) * hi_C M c w i j := by
      unfold hi_C
      rw [hu, show M.θ i + (c i + k) = M.θ i + c i + k by ring,
        show M.θ i + (c j + k) = M.θ i + c j + k by ring, hi_cara_shift γ (M.θ i + c i) k,
        hi_cara_shift γ (M.θ i + c j) k]
      ring
    rw [hC]; exact mul_nonneg he.le (hic i j)
  · rw [← hpk]; unfold hi_agentValue
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu, show M.θ i + (c i + k) = M.θ i + c i + k by ring,
      hi_cara_shift γ (M.θ i + c i) k]
    ring
  · have := hw i; rw [hv] at this ⊢; nlinarith

/-- Exercise 22.4: `b(e^{−γk} v) = b(v) + k`. -/
theorem hi_cara_b_shift (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {v : ℝ} (hv : v < 0) : hi_b M (Real.exp (-γ * k) * v) = hi_b M v + k := by
  have hV := hi_cara_vmax M hγ hu
  have he := Real.exp_pos (-γ * k)
  have h1 : v < hi_vmax M := by rw [hV]; exact hv
  have h2 : Real.exp (-γ * k) * v < hi_vmax M := by rw [hV]; nlinarith
  apply (hi_Bfun_strictMono M).injective
  rw [hi_b_spec M h2]
  have := hi_b_spec M h1
  unfold hi_Bfun at this ⊢
  have e : ∑ i, M.prob i * M.u (M.θ i + (hi_b M v + k)) =
      Real.exp (-γ * k) * ∑ i, M.prob i * M.u (M.θ i + hi_b M v) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu, show M.θ i + (hi_b M v + k) = M.θ i + hi_b M v + k by ring,
      hi_cara_shift γ (M.θ i + hi_b M v) k]; ring
  rw [e, this]; ring

/-- Exercise 22.4: `c*(e^{−γk} v) = c*(v) + k`. -/
theorem hi_cara_cstar_shift (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {v : ℝ} (hv : v < 0) : hi_cstar M (Real.exp (-γ * k) * v) = hi_cstar M v + k := by
  have hV := hi_cara_vmax M hγ hu
  have he := Real.exp_pos (-γ * k)
  have h1 : v < hi_vmax M := by rw [hV]; exact hv
  have h2 : Real.exp (-γ * k) * v < hi_vmax M := by rw [hV]; nlinarith
  apply M.u_strictMono.injective
  rw [hi_cstar_spec M h2]
  have := hi_cstar_spec M h1
  rw [hu] at this ⊢
  rw [hi_cara_shift γ (hi_cstar M v) k, this]; ring

/-- The rescaled function `f(e^{−γk} v) + k/(1 − β)`. -/
noncomputable def hi_scaleFn (M : HIModel) (γ k : ℝ) (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  f (Real.exp (-γ * k) * v) + k / (1 - M.β)

/-- The bounds (22.26) are invariant under the rescaling. -/
theorem hi_scaleFn_InF (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {f : ℝ → ℝ} (hf : hi_InF M f) : hi_InF M (hi_scaleFn M γ k f) := by
  have hV := hi_cara_vmax M hγ hu
  have he := Real.exp_pos (-γ * k)
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  intro v hv
  rw [hV] at hv
  have h2 : Real.exp (-γ * k) * v < hi_vmax M := by rw [hV]; nlinarith
  obtain ⟨hL, hU⟩ := hf _ h2
  have eL : hi_L M (Real.exp (-γ * k) * v) + k / (1 - M.β) = hi_L M v := by
    unfold hi_L; rw [hi_cara_b_shift M hγ hu k hv]; field_simp; ring
  have eU : hi_U M (Real.exp (-γ * k) * v) + k / (1 - M.β) = hi_U M v := by
    unfold hi_U; rw [hi_cara_cstar_shift M hγ hu k hv]; field_simp; ring
  unfold hi_scaleFn
  constructor <;> linarith

/-- The principal's value of a rescaled contract against a rescaled continuation. -/
theorem hi_pv_scaleFn (M : HIModel) (γ k : ℝ) (f : ℝ → ℝ) (c w : Fin (M.N + 1) → ℝ) :
    hi_principalValue M (hi_scaleFn M γ k f) c w =
      hi_principalValue M f (fun i => c i + k) (fun i => Real.exp (-γ * k) * w i) +
        k / (1 - M.β) := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_principalValue hi_scaleFn
  have : ∀ i, M.prob i * (-c i + M.β * (f (Real.exp (-γ * k) * w i) + k / (1 - M.β))) =
      M.prob i * (-(c i + k) + M.β * f (Real.exp (-γ * k) * w i)) +
        M.prob i * (k / (1 - M.β)) := fun i => by field_simp; ring
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, hi_sum_const]

/-- Exercise 22.4: the Bellman operator commutes with the rescaling,
`T(f(e^{−γk} ·) + k/(1 − β)) = (Tf)(e^{−γk} ·) + k/(1 − β)`. -/
theorem hi_T_scaleFn (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {f : ℝ → ℝ} (hf : hi_InF M f) {v : ℝ} (hv : v < 0) :
    hi_T M (hi_scaleFn M γ k f) v = hi_scaleFn M γ k (hi_T M f) v := by
  have hV := hi_cara_vmax M hγ hu
  have he := Real.exp_pos (-γ * k)
  have hvV : v < hi_vmax M := by rw [hV]; exact hv
  have h2 : Real.exp (-γ * k) * v < hi_vmax M := by rw [hV]; nlinarith
  have hsF := hi_scaleFn_InF M hγ hu k hf
  change hi_T M (hi_scaleFn M γ k f) v = hi_T M f (Real.exp (-γ * k) * v) + k / (1 - M.β)
  apply le_antisymm
  · refine csSup_le (hi_vals_nonempty M _ hvV) ?_
    rintro _ ⟨c, w, h, rfl⟩
    rw [hi_pv_scaleFn]
    have := hi_le_T M (fun w hw => (hf w hw).2) (hi_cara_scale_feasible M hγ hu k h)
    linarith
  · have : hi_T M f (Real.exp (-γ * k) * v) ≤
        hi_T M (hi_scaleFn M γ k f) v - k / (1 - M.β) := by
      refine csSup_le (hi_vals_nonempty M _ h2) ?_
      rintro _ ⟨c, w, h, rfl⟩
      have hb := hi_cara_scale_feasible M hγ hu (-k) h
      have e1 : Real.exp (-γ * -k) * (Real.exp (-γ * k) * v) = v := by
        rw [← mul_assoc, ← Real.exp_add]; simp
      rw [e1] at hb
      have := hi_le_T M (fun w hw => (hsF w hw).2) hb
      rw [hi_pv_scaleFn] at this
      have e2 : (fun i => Real.exp (-γ * k) * (Real.exp (-γ * -k) * w i)) = w := by
        funext i; rw [← mul_assoc, ← Real.exp_add]; simp
      have e3 : (fun i => c i + -k + k) = c := by funext i; ring
      simp only [e2, e3] at this
      linarith
    linarith

/-- Exercise 22.4: `P(e^{−γk} v) + k/(1 − β) = P(v)` for `v < 0`, by uniqueness of the fixed
point (Proposition 22.3.1). -/
theorem hi_cara_P_scale (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {v : ℝ} (hv : v < 0) :
    hi_P M (Real.exp (-γ * k) * v) + k / (1 - M.β) = hi_P M v := by
  have hV := hi_cara_vmax M hγ hu
  have hQ := hi_scaleFn_InF M hγ hu k (hi_P_InF M)
  have hQf : ∀ x < hi_vmax M,
      hi_T M (hi_scaleFn M γ k (hi_P M)) x = hi_scaleFn M γ k (hi_P M) x := by
    intro x hx
    rw [hV] at hx
    rw [hi_T_scaleFn M hγ hu k (hi_P_InF M) hx]
    unfold hi_scaleFn
    rw [hi_P_fixed M (by rw [hV]; nlinarith [Real.exp_pos (-γ * k)])]
  have := hi_fixed_unique M hQ (hi_P_InF M) hQf (fun x hx => hi_P_fixed M hx)
    (show v < hi_vmax M by rw [hV]; exact hv)
  unfold hi_scaleFn at this
  exact this

/-- **Exercise 22.4** (Miao, p. 799), the value function: with CARA utility,
`P(v) = [ln(−v) + K]/(γ(1 − β))` on `(−∞, 0)`, with `K = γ(1 − β)P(−1)`. -/
theorem ex_22_4_value (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) {v : ℝ}
    (hv : v < 0) :
    hi_P M v = (Real.log (-v) + γ * (1 - M.β) * hi_P M (-1)) / (γ * (1 - M.β)) := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have := hi_cara_P_scale M hγ hu (-Real.log (-v) / γ) (show (-1 : ℝ) < 0 by norm_num)
  have e : Real.exp (-γ * (-Real.log (-v) / γ)) * -1 = v := by
    rw [show -γ * (-Real.log (-v) / γ) = Real.log (-v) by field_simp,
      Real.exp_log (by linarith)]; ring
  rw [e] at this
  field_simp
  field_simp at this
  linarith

/-- With CARA utility, `P'(v) = 1/(γ(1 − β)v)` on `(−∞, 0)`. -/
theorem hi_cara_P_hasDerivAt (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) {v : ℝ}
    (hv : v < 0) : HasDerivAt (hi_P M) (1 / (γ * (1 - M.β) * v)) v := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  set K := γ * (1 - M.β) * hi_P M (-1)
  have hd : HasDerivAt (fun x => (Real.log (-x) + K) / (γ * (1 - M.β)))
      (1 / (γ * (1 - M.β) * v)) v := by
    have h1 := ((hasDerivAt_neg v).log (by linarith : -v ≠ 0)).add_const K
    have h2 := h1.div_const (γ * (1 - M.β))
    convert h2 using 1
    field_simp
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hv] with x hx
  exact ex_22_4_value M hγ hu hx

/-- With CARA utility, rescaling a contract lowers the principal's value by `k/(1 − β)`. -/
theorem hi_cara_pv_scale (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {c w : Fin (M.N + 1) → ℝ} (hw : ∀ i, w i < 0) :
    hi_principalValue M (hi_P M) (fun i => c i + k) (fun i => Real.exp (-γ * k) * w i) =
      hi_principalValue M (hi_P M) c w - k / (1 - M.β) := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_principalValue
  have : ∀ i, M.prob i * (-(c i + k) + M.β * hi_P M (Real.exp (-γ * k) * w i)) =
      M.prob i * (-c i + M.β * hi_P M (w i)) - M.prob i * (k / (1 - M.β)) := fun i => by
    have h := hi_cara_P_scale M hγ hu k (hw i)
    rw [show hi_P M (Real.exp (-γ * k) * w i) = hi_P M (w i) - k / (1 - M.β) by linarith]
    field_simp; ring
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, hi_sum_const]

/-- Exercise 22.4: an optimal contract at `v` rescales to an optimal contract at
`e^{−γk} v`. -/
theorem hi_cara_optimal_scale (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ)
    (k : ℝ) {v : ℝ} {c w : Fin (M.N + 1) → ℝ} (h : hi_Optimal M (hi_P M) v c w) :
    hi_Optimal M (hi_P M) (Real.exp (-γ * k) * v) (fun i => c i + k)
      (fun i => Real.exp (-γ * k) * w i) := by
  have hV := hi_cara_vmax M hγ hu
  obtain ⟨hf, hbest⟩ := h
  have hw : ∀ i, w i < 0 := fun i => by have := hf.2.2 i; rwa [hV] at this
  refine ⟨hi_cara_scale_feasible M hγ hu k hf, fun c' w' h' => ?_⟩
  have hw' : ∀ i, w' i < 0 := fun i => by have := h'.2.2 i; rwa [hV] at this
  have hb := hi_cara_scale_feasible M hγ hu (-k) h'
  have e1 : Real.exp (-γ * -k) * (Real.exp (-γ * k) * v) = v := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [e1] at hb
  have h1 := hbest _ _ hb
  have hw'' : ∀ i, Real.exp (-γ * -k) * w' i < 0 := fun i => by
    nlinarith [Real.exp_pos (-γ * -k), hw' i]
  have h2 := hi_cara_pv_scale M hγ hu k (c := fun i => c' i + -k) hw''
  have e2 : (fun i => Real.exp (-γ * k) * (Real.exp (-γ * -k) * w' i)) = w' := by
    funext i; rw [← mul_assoc, ← Real.exp_add]; simp
  have e3 : (fun i => c' i + -k + k) = c' := by funext i; ring
  simp only [e2, e3] at h2
  rw [hi_cara_pv_scale M hγ hu k hw]
  linarith

/-- An optimal contract attains the value function. -/
theorem hi_optimal_value (M : HIModel) {v : ℝ} {c w : Fin (M.N + 1) → ℝ}
    (h : hi_Optimal M (hi_P M) v c w) : hi_principalValue M (hi_P M) c w = hi_P M v := by
  have hv : v < hi_vmax M := h.1.2.1 ▸ hi_agentValue_lt_vmax M h.1.2.2
  rw [← hi_P_fixed M hv]
  apply le_antisymm (hi_le_T M (fun w hw => (hi_P_InF M w hw).2) h.1)
  exact csSup_le (hi_vals_nonempty M _ hv) (by rintro _ ⟨c', w', h', rfl⟩; exact h.2 c' w' h')

/-- **Exercise 22.4** (Miao, p. 799), the optimal contract, corrected (`A = 0`). With CARA
utility, let `(c, w)` be an optimal contract at `v = −1`, and put `aᵢ = e^{−γcᵢ}`,
`dᵢ = −wᵢ`. Then for every `v < 0` the contract `cᵢ(v) = −(1/γ) ln(−aᵢ v)`, `wᵢ(v) = dᵢ v` is
optimal at `v`; `0 < aᵢ₋₁ ≤ aᵢ`, `dᵢ₋₁ ≥ dᵢ > 0`, `Σ πᵢ/dᵢ = 1`,
`Σ πᵢ (e^{−γθᵢ} aᵢ + β dᵢ) = 1`, and `P(v) = [ln(−v) + K]/(γ(1 − β))` with
`K = Σ πᵢ ln aᵢ + β/(1 − β) Σ πᵢ ln dᵢ`. -/
theorem ex_22_4 (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ)
    {c w : Fin (M.N + 1) → ℝ} (h : hi_Optimal M (hi_P M) (-1) c w) :
    let a := fun i => Real.exp (-γ * c i)
    let d := fun i => -w i
    let K := ∑ i, M.prob i * Real.log (a i) + M.β / (1 - M.β) * ∑ i, M.prob i * Real.log (d i)
    (∀ v < 0, hi_Optimal M (hi_P M) v (fun i => -(1 / γ) * Real.log (-(a i * v)))
      (fun i => d i * v)) ∧
    (∀ i, 0 < a i) ∧ Monotone a ∧ (∀ i, 0 < d i) ∧ Antitone d ∧
    ∑ i, M.prob i / d i = 1 ∧
    ∑ i, M.prob i * (Real.exp (-γ * M.θ i) * a i + M.β * d i) = 1 ∧
    ∀ v < 0, hi_P M v = (Real.log (-v) + K) / (γ * (1 - M.β)) := by
  intro a d K
  have hV := hi_cara_vmax M hγ hu
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  obtain ⟨⟨hic, hpk, hwv⟩, hbest⟩ := h
  have hw : ∀ i, w i < 0 := fun i => by have := hwv i; rwa [hV] at this
  obtain ⟨hcm, hwm⟩ := lemma_22_3_1 M c w hic
  have hval := hi_optimal_value M ⟨⟨hic, hpk, hwv⟩, hbest⟩
  -- the value at `−1` and `K`
  have hK : γ * (1 - M.β) * hi_P M (-1) = K := by
    have hPw : ∀ i, hi_P M (w i) =
        (Real.log (d i) + γ * (1 - M.β) * hi_P M (-1)) / (γ * (1 - M.β)) := fun i => by
      rw [ex_22_4_value M hγ hu (hw i)]
    have hc : ∀ i, -c i = Real.log (a i) / γ := fun i => by
      simp only [a, Real.log_exp]; field_simp
    unfold hi_principalValue at hval
    simp only [hc, hPw] at hval
    simp only [K]
    have e : ∑ i, M.prob i * (Real.log (a i) / γ + M.β *
        ((Real.log (d i) + γ * (1 - M.β) * hi_P M (-1)) / (γ * (1 - M.β)))) =
        (∑ i, M.prob i * Real.log (a i)) / γ +
          M.β / (γ * (1 - M.β)) * ∑ i, M.prob i * Real.log (d i) +
          M.β * hi_P M (-1) := by
      have : ∀ i, M.prob i * (Real.log (a i) / γ + M.β *
          ((Real.log (d i) + γ * (1 - M.β) * hi_P M (-1)) / (γ * (1 - M.β)))) =
          M.prob i * Real.log (a i) / γ + M.β / (γ * (1 - M.β)) * (M.prob i * Real.log (d i)) +
            M.prob i * (M.β * hi_P M (-1)) := fun i => by field_simp; ring
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib,
        Finset.sum_add_distrib, hi_sum_const, ← Finset.sum_div, ← Finset.mul_sum]
    rw [e] at hval
    field_simp at hval ⊢
    linarith
  refine ⟨fun v hv => ?_, fun i => Real.exp_pos _, fun i j hij => ?_, fun i => ?_,
    fun i j hij => ?_, ?_, ?_, fun v hv => ?_⟩
  · -- rescale with `k = −ln(−v)/γ`
    have hs := hi_cara_optimal_scale M hγ hu (-Real.log (-v) / γ) ⟨⟨hic, hpk, hwv⟩, hbest⟩
    have ek : Real.exp (-γ * (-Real.log (-v) / γ)) = -v := by
      rw [show -γ * (-Real.log (-v) / γ) = Real.log (-v) by field_simp,
        Real.exp_log (by linarith)]
    rw [ek] at hs
    have e1 : -v * -1 = v := by ring
    have e2 : (fun i => c i + -Real.log (-v) / γ) =
        fun i => -(1 / γ) * Real.log (-(a i * v)) := by
      funext i
      simp only [a]
      rw [show -(Real.exp (-γ * c i) * v) = Real.exp (-γ * c i) * -v by ring,
        Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp]
      field_simp; ring
    have e3 : (fun i => -v * w i) = fun i => d i * v := by funext i; simp only [d]; ring
    rw [e1, e2, e3] at hs
    exact hs
  · simp only [a]
    exact Real.exp_le_exp.2 (by nlinarith [hcm hij])
  · simp only [d]; linarith [hw i]
  · simp only [d]; linarith [hwm hij]
  · -- the martingale property (22.30)
    have hm := hi_martingale_of_shift M (dP := fun x => 1 / (γ * (1 - M.β) * x)) (hi_P_InF M)
      (fun x hx => hi_P_fixed M hx)
      ⟨hic, hpk, hwv⟩ hval (hi_cara_P_hasDerivAt M hγ hu (by norm_num : (-1 : ℝ) < 0))
      fun i => hi_cara_P_hasDerivAt M hγ hu (hw i)
    have hC : 0 < γ * (1 - M.β) := mul_pos hγ h1β
    have e : ∀ i, M.prob i * (1 / (γ * (1 - M.β) * w i)) =
        -(1 / (γ * (1 - M.β))) * (M.prob i / d i) := fun i => by
      simp only [d]; have := (hw i).ne; field_simp
    simp only [e] at hm
    rw [← Finset.mul_sum] at hm
    have : (1 : ℝ) / (γ * (1 - M.β) * -1) = -(1 / (γ * (1 - M.β))) * 1 := by
      rw [mul_neg_one, one_div_neg_eq_neg_one_div, mul_one]
    rw [this] at hm
    exact mul_left_cancel₀ (neg_ne_zero.2 (one_div_ne_zero hC.ne')) hm
  · -- promise keeping at `−1`
    have := hpk
    unfold hi_agentValue at this
    have e : ∀ i, M.prob i * (M.u (M.θ i + c i) + M.β * w i) =
        -(M.prob i * (Real.exp (-γ * M.θ i) * a i + M.β * d i)) := fun i => by
      rw [hu]; simp only [hi_cara, a, d]
      rw [show -γ * (M.θ i + c i) = -γ * M.θ i + -γ * c i by ring, Real.exp_add]; ring
    simp only [e, Finset.sum_neg_distrib] at this
    linarith
  · rw [ex_22_4_value M hγ hu hv, hK]

/-- Exercise 22.4, the printed form: if `cᵢ(v) = −(1/γ) ln(−aᵢ(v + A))` and
`wᵢ(v) = dᵢ v + (dᵢ − 1)A` keep the promise at two distinct values `v₁ ≠ v₂` (with
`vⱼ + A < 0`), then `A = 0`. -/
theorem hi_ex_22_4_A_eq_zero (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ)
    {a d : Fin (M.N + 1) → ℝ} (ha : ∀ i, 0 < a i) {A v1 v2 : ℝ} (h12 : v1 ≠ v2)
    (hv1 : v1 + A < 0) (hv2 : v2 + A < 0)
    (hpk : ∀ v ∈ ({v1, v2} : Set ℝ),
      hi_agentValue M (fun i => -(1 / γ) * Real.log (-(a i * (v + A))))
      (fun i => d i * v + (d i - 1) * A) = v) : A = 0 := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  set S := ∑ i, M.prob i * (Real.exp (-γ * M.θ i) * a i)
  set D := ∑ i, M.prob i * d i
  have hform : ∀ v, v + A < 0 → hi_agentValue M (fun i => -(1 / γ) * Real.log (-(a i * (v + A))))
      (fun i => d i * v + (d i - 1) * A) = (v + A) * S + M.β * (D * v + (D - 1) * A) := by
    intro v hv
    unfold hi_agentValue
    have e : ∀ i, M.prob i * (M.u (M.θ i + -(1 / γ) * Real.log (-(a i * (v + A)))) +
        M.β * (d i * v + (d i - 1) * A)) = (v + A) * (M.prob i * (Real.exp (-γ * M.θ i) * a i)) +
        M.β * (v * (M.prob i * d i) + A * (M.prob i * d i) - A * M.prob i) := fun i => by
      rw [hu]; simp only [hi_cara]
      have hpos : 0 < -(a i * (v + A)) := by nlinarith [ha i]
      rw [show -γ * (M.θ i + -(1 / γ) * Real.log (-(a i * (v + A)))) =
        -γ * M.θ i + Real.log (-(a i * (v + A))) by field_simp; ring, Real.exp_add,
        Real.exp_log hpos]
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, M.prob_sum]
    ring
  have e1 := hpk v1 (by simp)
  have e2 := hpk v2 (by simp)
  rw [hform v1 hv1] at e1
  rw [hform v2 hv2] at e2
  -- subtracting: `(v₁ − v₂)(S + βD − 1) = 0`
  have hS : S + M.β * D = 1 := by
    have : (v1 - v2) * (S + M.β * D - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h12
    · linarith
  have : A * (1 - M.β) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · linarith

/-- **Exercise 22.4** (Miao, p. 799), the printed form is inconsistent: there are no positive
`aᵢ` and constants `dᵢ`, `A = Σ πᵢ/aᵢ` for which the printed contract
`cᵢ = −(1/γ) ln(−aᵢ(v + A))`, `wᵢ = dᵢ v + (dᵢ − 1)A` keeps the promise for all `v < −A`. -/
theorem ex_22_4_printed_inconsistent (M : HIModel) {γ : ℝ} (hγ : 0 < γ)
    (hu : M.u = hi_cara γ) :
    ¬ ∃ (a d : Fin (M.N + 1) → ℝ) (A : ℝ), (∀ i, 0 < a i) ∧ ∑ i, M.prob i / a i = A ∧
      ∀ v, v + A < 0 → hi_agentValue M (fun i => -(1 / γ) * Real.log (-(a i * (v + A))))
        (fun i => d i * v + (d i - 1) * A) = v := by
  rintro ⟨a, d, A, ha, hA, hpk⟩
  have h0 := hi_ex_22_4_A_eq_zero M hγ hu ha (v1 := -A - 1) (v2 := -A - 2) (by norm_num)
    (by linarith) (by linarith) (by
      intro v hv
      rcases hv with rfl | rfl
      · exact hpk _ (by linarith)
      · exact hpk _ (by linarith))
  have hpos : 0 < ∑ i, M.prob i / a i :=
    Finset.sum_pos (fun i _ => div_pos (M.prob_pos i) (ha i)) Finset.univ_nonempty
  linarith

/-- **Exercise 22.3** (Miao, p. 798), the half that holds for every `β`: in per-period terms the
value function never exceeds the first best, `(1 − β) P(ṽ/(1 − β)) ≤ θ̄ − u⁻¹(ṽ)` for
`ṽ < sup u`. -/
theorem ex_22_3_upper (M : HIModel) {vt : ℝ} (hvt : vt < hi_ubar M) :
    (1 - M.β) * hi_P M (vt / (1 - M.β)) ≤ hi_θbar M - hi_uinv M vt := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hv : vt / (1 - M.β) < hi_vmax M := by
    rw [hi_lt_vmax_iff, mul_div_cancel₀ _ h1β.ne']; exact hvt
  have := (hi_P_InF M _ hv).2
  unfold hi_U hi_cstar at this
  rw [mul_div_cancel₀ _ h1β.ne'] at this
  rw [le_div_iff₀ h1β] at this
  linarith

/-- Exercise 22.3: in per-period terms both bounds of (22.26) are independent of `β`:
`(1 − β) U(ṽ/(1 − β)) = θ̄ − u⁻¹(ṽ)` and `(1 − β) L(ṽ/(1 − β)) = −b̃(ṽ)` where
`Σ πᵢ u(θᵢ + b̃) = ṽ`. So the bounds alone cannot give the limit `β → 1`. -/
theorem hi_normalized_bounds (M : HIModel) {vt : ℝ} (hvt : vt < hi_ubar M) :
    (1 - M.β) * hi_U M (vt / (1 - M.β)) = hi_θbar M - hi_uinv M vt ∧
      (1 - M.β) * hi_L M (vt / (1 - M.β)) = -hi_b M (vt / (1 - M.β)) ∧
      hi_Bfun M (hi_b M (vt / (1 - M.β))) = vt := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hv : vt / (1 - M.β) < hi_vmax M := by
    rw [hi_lt_vmax_iff, mul_div_cancel₀ _ h1β.ne']; exact hvt
  refine ⟨?_, ?_, ?_⟩
  · unfold hi_U hi_cstar; rw [mul_div_cancel₀ _ h1β.ne']; field_simp
  · unfold hi_L; field_simp
  · rw [hi_b_spec M hv, mul_div_cancel₀ _ h1β.ne']

end Miao.RecursiveContracts
