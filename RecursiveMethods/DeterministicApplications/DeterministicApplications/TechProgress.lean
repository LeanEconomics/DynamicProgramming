/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.WeakConcavity

/-!
# Growth with technical progress

SLP §5.4, pp. 105–107: effective labour grows by the factor `1 + λ > 1`, `F` has constant returns,
capital depreciates at rate `δ`, and `U(C) = C^γ/γ`. Dividing every variable by `(1 + λ)ᵗ` gives
a problem in `k_t = K_t/(1 + λ)ᵗ`.

* `renorm_budget`, `renorm_capital`: with `F` homogeneous of degree one, the constraints become
  `c_t + i_t ≤ f(k_t)`, `f(k) = F(k, 1)`, and `k_{t+1} = [(1 − δ)k_t + i_t]/(1 + λ)`.
* `renorm_power_utility`: `βᵗ C_t^γ/γ = [β(1 + λ)^γ]ᵗ c_t^γ/γ`; `renorm_log_utility`: for
  `U = ln` the objective changes only by a constant.
* `renorm_consumption`: eliminating `i_t`, consumption is `(1 + λ)[f̃(k_t) − k_{t+1}]` with
  `f̃(k) = [f(k) + (1 − δ)k]/(1 + λ)`. **Exercise 5.4**: the functional equation is
  `v(k) = max_{0 ≤ y ≤ f̃(k)} {Ũ(f̃(k) − y) + β̃v(y)}`, `Ũ(c) = U((1 + λ)c)`, `β̃ = β(1 + λ)^γ`.
* `ex_5_4`: if `β̃ < 1` (and `f̃` satisfies (T2)), then `(Ũ, f̃, β̃)` satisfies the hypotheses of
  Section 5.1, and concavity carries over (`renormU_strictConcave`, `renormF_concave`); so the
  analysis of Section 5.1 goes through (`ex_5_4_analysis`).
* `power_utility`: `c^γ/γ` with `0 < γ < 1` satisfies (U2)–(U4).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {U f : ℝ → ℝ} {β γ δ lam xbar : ℝ}

/-- `Ũ(c) = U((1 + λ)c)`. -/
def renormU (U : ℝ → ℝ) (lam : ℝ) (c : ℝ) : ℝ := U ((1 + lam) * c)

/-- `f̃(k) = [f(k) + (1 − δ)k]/(1 + λ)`. -/
noncomputable def renormF (f : ℝ → ℝ) (δ lam : ℝ) (k : ℝ) : ℝ := (f k + (1 - δ) * k) / (1 + lam)

/-- With `F` homogeneous of degree one and `L_t = (1 + λ)ᵗ`, `C_t + I_t ≤ F(K_t, L_t)` iff
`c_t + i_t ≤ f(k_t)` for the renormalized variables. -/
theorem renorm_budget (F : ℝ → ℝ → ℝ) (hF : ∀ a > 0, ∀ K L, F (a * K) (a * L) = a * F K L)
    (hlam : 0 < 1 + lam) (t : ℕ) (C I K : ℝ) :
    C + I ≤ F K ((1 + lam) ^ t) ↔
      C / (1 + lam) ^ t + I / (1 + lam) ^ t ≤ F (K / (1 + lam) ^ t) 1 := by
  have hp : 0 < (1 + lam) ^ t := pow_pos hlam t
  have e : F K ((1 + lam) ^ t) = (1 + lam) ^ t * F (K / (1 + lam) ^ t) 1 := by
    rw [← hF _ hp]
    congr 1 <;> field_simp
  rw [e, ← add_div, div_le_iff₀ hp, mul_comm]

/-- `K_{t+1} = (1 − δ)K_t + I_t` iff `k_{t+1} = [(1 − δ)k_t + i_t]/(1 + λ)`. -/
theorem renorm_capital (hlam : 0 < 1 + lam) (t : ℕ) (K K' I : ℝ) :
    K' = (1 - δ) * K + I ↔
      K' / (1 + lam) ^ (t + 1) =
        ((1 - δ) * (K / (1 + lam) ^ t) + I / (1 + lam) ^ t) / (1 + lam) := by
  have hp : 0 < (1 + lam) ^ t := pow_pos hlam t
  have hne : (1 + lam) ^ t ≠ 0 := hp.ne'
  have hne' : (1 + lam) ≠ 0 := hlam.ne'
  rw [pow_succ]
  constructor
  · intro h; rw [h]; field_simp
  · intro h
    field_simp at h
    linarith

/-- `βᵗ C^γ/γ = [β(1 + λ)^γ]ᵗ c^γ/γ` for `C = (1 + λ)ᵗc`, `c ≥ 0`. -/
theorem renorm_power_utility (hlam : 0 < 1 + lam) {c : ℝ} (hc : 0 ≤ c) (t : ℕ) :
    β ^ t * (((1 + lam) ^ t * c) ^ γ / γ) = (β * (1 + lam) ^ γ) ^ t * (c ^ γ / γ) := by
  have e : ((1 + lam) ^ t) ^ γ = ((1 + lam) ^ γ) ^ t := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le,
      ← Real.rpow_mul hlam.le]
    congr 1
    ring
  rw [Real.mul_rpow (pow_nonneg hlam.le t) hc, e, mul_pow]
  ring

/-- For `U = ln`, `βᵗ ln C_t = βᵗ t ln(1 + λ) + βᵗ ln c_t`: the objective changes by a constant
and `β̃ = β`. -/
theorem renorm_log_utility (hlam : 0 < 1 + lam) {c : ℝ} (hc : 0 < c) (t : ℕ) :
    β ^ t * Real.log ((1 + lam) ^ t * c) =
      β ^ t * (t * Real.log (1 + lam)) + β ^ t * Real.log c := by
  rw [Real.log_mul (pow_pos hlam t).ne' hc.ne', Real.log_pow]
  ring

/-- Eliminating investment, consumption is `f(k) + (1 − δ)k − (1 + λ)y = (1 + λ)[f̃(k) − y]`,
so the return is `U(c) = Ũ(f̃(k) − y)`. -/
theorem renorm_consumption (hlam : 0 < 1 + lam) (k y : ℝ) :
    U (f k + (1 - δ) * k - (1 + lam) * y) = renormU U lam (renormF f δ lam k - y) := by
  simp only [renormU, renormF]
  congr 1
  field_simp

/-- `Ũ` inherits continuity and strict monotonicity on `[0, ∞)`. -/
theorem renormU_hyp (hlam : 0 < 1 + lam) (hUc : ContinuousOn U (Ici 0))
    (hUm : StrictMonoOn U (Ici 0)) :
    ContinuousOn (renormU U lam) (Ici 0) ∧ StrictMonoOn (renormU U lam) (Ici 0) := by
  have hmaps : MapsTo (fun c => (1 + lam) * c) (Ici 0) (Ici 0) := fun c hc =>
    mem_Ici.2 (mul_nonneg hlam.le hc)
  refine ⟨hUc.comp (continuous_const.mul continuous_id).continuousOn hmaps, ?_⟩
  intro a ha b hb hab
  exact hUm (hmaps ha) (hmaps hb) (mul_lt_mul_of_pos_left hab hlam)

/-- `Ũ` inherits strict concavity. -/
theorem renormU_strictConcave (hlam : 0 < 1 + lam) (hU : StrictConcaveOn ℝ (Ici 0) U) :
    StrictConcaveOn ℝ (Ici 0) (renormU U lam) := by
  refine ⟨convex_Ici 0, fun a ha b hb hab s t hs ht hst => ?_⟩
  have ha' : (1 + lam) * a ∈ Ici (0 : ℝ) := mem_Ici.2 (mul_nonneg hlam.le ha)
  have hb' : (1 + lam) * b ∈ Ici (0 : ℝ) := mem_Ici.2 (mul_nonneg hlam.le hb)
  have hne : (1 + lam) * a ≠ (1 + lam) * b := fun he =>
    hab (mul_left_cancel₀ hlam.ne' he)
  have := hU.2 ha' hb' hne hs ht hst
  simp only [smul_eq_mul, renormU] at this ⊢
  convert this using 2
  ring

/-- `f̃` inherits (T1), `f̃(0) = 0` and (T3) when `0 ≤ δ ≤ 1`. -/
theorem renormF_hyp (hlam : 0 < 1 + lam) (hδ : δ ≤ 1) (hfc : ContinuousOn f (Ici 0))
    (hf0 : f 0 = 0) (hfm : StrictMonoOn f (Ici 0)) :
    ContinuousOn (renormF f δ lam) (Ici 0) ∧ renormF f δ lam 0 = 0 ∧
      StrictMonoOn (renormF f δ lam) (Ici 0) := by
  refine ⟨(hfc.add (continuous_const.mul continuous_id).continuousOn).div_const _,
    by simp [renormF, hf0], fun a ha b hb hab => ?_⟩
  have h1 := hfm ha hb hab
  have h2 : (1 - δ) * a ≤ (1 - δ) * b := mul_le_mul_of_nonneg_left hab.le (by linarith)
  exact div_lt_div_of_pos_right (by linarith) hlam

/-- `f̃` inherits (T4). -/
theorem renormF_concave (hlam : 0 < 1 + lam) (hf : ConcaveOn ℝ (Ici 0) f) :
    ConcaveOn ℝ (Ici 0) (renormF f δ lam) := by
  have hlin : ConcaveOn ℝ (Ici 0) fun k : ℝ => (1 - δ) * k :=
    (LinearMap.mulLeft ℝ (1 - δ)).concaveOn (convex_Ici 0)
  have := (hf.add hlin).smul (inv_nonneg.2 hlam.le)
  refine this.congr fun k _ => ?_
  simp only [renormF, Pi.add_apply, smul_eq_mul]
  ring

/-- **Exercise 5.4.** If `β̃ = β(1 + λ)^γ` lies in `(0, 1)` and `f̃` satisfies (T2) on `[0, x̄]`,
the renormalized problem satisfies the hypotheses of Section 5.1. -/
theorem ex_5_4 (hlam : 0 < lam) (hδ : δ ≤ 1) (hβ0 : 0 < β * (1 + lam) ^ γ)
    (hβ1 : β * (1 + lam) ^ γ < 1) (hUc : ContinuousOn U (Ici 0))
    (hUm : StrictMonoOn U (Ici 0)) (hfc : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0)
    (hfm : StrictMonoOn f (Ici 0)) (hx : 0 < xbar)
    (hT2 : ∀ x ∈ Icc 0 xbar, x ≤ renormF f δ lam x ∧ renormF f δ lam x ≤ xbar) :
    GrowthHyp (renormU U lam) (renormF f δ lam) (β * (1 + lam) ^ γ) xbar := by
  have hl : 0 < 1 + lam := by linarith
  obtain ⟨h1, h2⟩ := renormU_hyp hl hUc hUm
  obtain ⟨h3, h4, h5⟩ := renormF_hyp hl hδ hfc hf0 hfm
  exact ⟨hβ0, hβ1, h1, h2, h3, h4, hx, hT2, h5⟩

/-- **Exercise 5.4.** The analysis of Section 5.1 goes through: under (U1)–(U4) and
(T1)–(T4) for the original model, the renormalized value function is the supremum function, is
strictly increasing and strictly concave, and the policy is a continuous function. -/
theorem ex_5_4_analysis [Nonempty (Icc (0 : ℝ) xbar)] (hlam : 0 < lam) (hδ : δ ≤ 1)
    (hβ0 : 0 < β * (1 + lam) ^ γ) (hβ1 : β * (1 + lam) ^ γ < 1) (hUc : ContinuousOn U (Ici 0))
    (hUm : StrictMonoOn U (Ici 0)) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hfc : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0) (hfm : StrictMonoOn f (Ici 0))
    (hf : ConcaveOn ℝ (Ici 0) f) (hx : 0 < xbar)
    (hT2 : ∀ x ∈ Icc 0 xbar, x ≤ renormF f δ lam x ∧ renormF f δ lam x ≤ xbar)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 (ex_5_4 hlam hδ hβ0 hβ1 hUc hUm hfc hf0 hfm hx hT2))
      (growth_assumption44 (ex_5_4 hlam hδ hβ0 hβ1 hUc hUm hfc hf0 hfm hx hT2)) v = v) :
    (fun x => (v x : EReal)) = vstar (growthΓ (renormF f δ lam) xbar)
      (curryF (growthF (renormU U lam) (renormF f δ lam) xbar)) (β * (1 + lam) ^ γ) ∧
      StrictMono v ∧ IsStrictConcaveS (convex_Icc 0 xbar) v ∧
      Continuous (argmaxFn (growthΓ (renormF f δ lam) xbar)
        (obj (growthF (renormU U lam) (renormF f δ lam) xbar) (β * (1 + lam) ^ γ) v)) := by
  have hl : 0 < 1 + lam := by linarith
  set h := ex_5_4 hlam hδ hβ0 hβ1 hUc hUm hfc hf0 hfm hx hT2
  obtain ⟨u, -, huniq, hvs, hmono, -⟩ := ex_5_1ab h
  have hvu := huniq v hv
  subst hvu
  obtain ⟨c1, -, c3⟩ := ex_5_1c_weak h (renormU_strictConcave hl hU) (renormF_concave hl hf) hv
  exact ⟨hvs, hmono, c1, c3⟩

/-- `c^γ/γ` with `0 < γ < 1` satisfies (U2)–(U4) on `[0, ∞)`. -/
theorem power_utility (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ContinuousOn (fun c : ℝ => c ^ γ / γ) (Ici 0) ∧
      StrictMonoOn (fun c : ℝ => c ^ γ / γ) (Ici 0) ∧
      StrictConcaveOn ℝ (Ici 0) (fun c : ℝ => c ^ γ / γ) := by
  refine ⟨fun c _ =>
    ((Real.continuousAt_rpow_const c γ (Or.inr hγ0.le)).div_const γ).continuousWithinAt,
    fun a ha b hb hab => div_lt_div_of_pos_right (Real.rpow_lt_rpow ha hab hγ0) hγ0, ?_⟩
  refine ⟨convex_Ici 0, fun a ha b hb hab s t hs ht hst => ?_⟩
  have h := (Real.strictConcaveOn_rpow hγ0 hγ1).2 ha hb hab hs ht hst
  simp only [smul_eq_mul] at h ⊢
  calc s * (a ^ γ / γ) + t * (b ^ γ / γ) = (s * a ^ γ + t * b ^ γ) / γ := by ring
    _ < (s * a + t * b) ^ γ / γ := div_lt_div_of_pos_right h hγ0

end StokeyLucasPrescott.DeterministicApplications
