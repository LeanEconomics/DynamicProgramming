/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.PAWeil
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Exercises 20.6 and 20.7: first-order conditions for recursive Pareto problems

Miao, *Economic Dynamics in Discrete Time*, Exercises 20.6–20.7 (pp. 735–736).

**Exercise 20.6** (production). Agents `i` with recursive utility
`Uⁱ = Wⁱ(c₀ⁱ, Rⁱ(s ↦ uⁱ(c₁ⁱ(s))))`, resource constraints `∑ c₀ⁱ + k₁ = z₀F(k₀)` and
`∑ c₁ⁱ(s) = z₁(s)F(k₁)`, Pareto weights `θ`. At an optimum of the planner's problem, with
`Wⁱ`, `Rⁱ`, `uⁱ`, `F` differentiable (`W₁ⁱ, W₂ⁱ` the partials of `Wⁱ`, `Rₛⁱ` the partial of `Rⁱ`
in state `s`):
* date-0 risk sharing `θᵢW₁ⁱ = θⱼW₁ʲ` (`ex_20_6_sharing0`);
* date-1 risk sharing `θᵢW₂ⁱRₛⁱuⁱ'(c₁ⁱ(s)) = θⱼW₂ʲRₛʲuʲ'(c₁ʲ(s))` (`ex_20_6_sharing1`);
* the Euler equation `W₁ⁱ = W₂ⁱ ∑ₛ Rₛⁱ uⁱ'(c₁ⁱ(s)) z₁(s)F'(k₁)` (`ex_20_6_euler`).
The general directional derivative of the planner's objective is `pa_planner_hasDerivAt`.
For Epstein–Zin utility `W₂/W₁` and `Rₛ` are explicit (`pa_W`, `pa_CE`), which this
general statement covers.

**Exercise 20.7** (multiplier preferences). `Uⁱ = uⁱ(c₀ⁱ) − βϑᵢ ln E exp(−U₁ⁱ/ϑᵢ)` with
`U₁ⁱ(s) = uⁱ(c₁ⁱ(s))`, pure exchange. The certainty equivalent has the partial derivative
`p(s) m(s)` with the worst-case distortion `m(s) = e^{−U₁(s)/ϑ}/E e^{−U₁/ϑ}`
(`pa_multiplier_hasDerivAt`), and an optimum satisfies `λᵢ uⁱ'(c₀ⁱ) = λⱼ uʲ'(c₀ʲ)` and
`λᵢ mᵢ(s) uⁱ'(c₁ⁱ(s)) = λⱼ mⱼ(s) uʲ'(c₁ʲ(s))` (`ex_20_7`). Part (b) is computational (Matlab) and
is not formalised.

Exercise 20.4 (Matlab replication of Bansal–Yaron) is computational; its formulas are the
theorems of `PALongRunRisk` and `PALongRunRiskPricing`.

The first-order conditions are necessary conditions at an interior optimum (the
perturbations used are feasible for all `t`).
-/

namespace Miao.RecursiveUtility

open Real Filter Topology

theorem pa_clm_pi_apply {S : Type*} [Fintype S] [DecidableEq S] (L : (S → ℝ) →L[ℝ] ℝ)
    (z : S → ℝ) : L z = ∑ s, L (Pi.single s 1) * z s := by
  have := L.toLinearMap.pi_apply_eq_sum_univ z
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

theorem pa_clm_prod_apply (L : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • (1, 0) + b • (0, 1) := by simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

variable {n : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

/-- The planner's objective `∑ θᵢ Wⁱ(c₀ⁱ, Rⁱ(s ↦ uⁱ(c₁(s)ⁱ)))`. -/
def pa_planner (θ : Fin n → ℝ) (W : Fin n → ℝ × ℝ → ℝ) (R : Fin n → (S → ℝ) → ℝ)
    (u : Fin n → ℝ → ℝ) (c0 : Fin n → ℝ) (c1 : S → Fin n → ℝ) : ℝ :=
  ∑ i, θ i * W i (c0 i, R i fun s => u i (c1 s i))

/-- The derivative of the planner's objective along differentiable paths `p₀`, `p₁` through the
allocation `(c₀, c₁)`. -/
theorem pa_planner_hasDerivAt (θ : Fin n → ℝ) {W : Fin n → ℝ × ℝ → ℝ}
    {R : Fin n → (S → ℝ) → ℝ} {u : Fin n → ℝ → ℝ} {c0 : Fin n → ℝ} {c1 : S → Fin n → ℝ}
    {DW : Fin n → ℝ × ℝ →L[ℝ] ℝ} {DR : Fin n → (S → ℝ) →L[ℝ] ℝ} {du : Fin n → S → ℝ}
    (hW : ∀ i, HasFDerivAt (W i) (DW i) (c0 i, R i fun s => u i (c1 s i)))
    (hR : ∀ i, HasFDerivAt (R i) (DR i) fun s => u i (c1 s i))
    (hu : ∀ i s, HasDerivAt (u i) (du i s) (c1 s i))
    {p0 : Fin n → ℝ → ℝ} {p1 : S → Fin n → ℝ → ℝ} {d0 : Fin n → ℝ} {d1 : S → Fin n → ℝ}
    (hp0 : ∀ i, HasDerivAt (p0 i) (d0 i) 0) (hp1 : ∀ s i, HasDerivAt (p1 s i) (d1 s i) 0)
    (h00 : ∀ i, p0 i 0 = c0 i) (h10 : ∀ s i, p1 s i 0 = c1 s i) :
    HasDerivAt (fun t => pa_planner θ W R u (fun i => p0 i t) fun s i => p1 s i t)
      (∑ i, θ i * (d0 i * DW i (1, 0)
        + DW i (0, 1) * ∑ s, DR i (Pi.single s 1) * (du i s * d1 s i))) 0 := by
  unfold pa_planner
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.const_mul (θ i) ?_
  have hv : HasDerivAt (fun t => fun s => u i (p1 s i t)) (fun s => du i s * d1 s i) 0 := by
    refine hasDerivAt_pi.2 fun s => ?_
    exact (hu i s).comp_of_eq 0 (hp1 s i) (h10 s i).symm
  have hr := (hR i).comp_hasDerivAt_of_eq 0 hv (by funext s; rw [h10])
  have hpair := (hp0 i).prodMk hr
  have := (hW i).comp_hasDerivAt_of_eq 0 hpair (by simp [Function.comp_apply, h00, h10])
  refine this.congr_deriv ?_
  rw [pa_clm_prod_apply (DW i) (d0 i) (DR i fun s => du i s * d1 s i),
    pa_clm_pi_apply (DR i) (fun s => du i s * d1 s i)]
  ring

omit [Fintype S] [DecidableEq S] in
/-- **Exercise 20.6** (Miao, p. 735), date-0 risk sharing: at an optimum of the planner's
problem with production, `θᵢ W₁ⁱ = θⱼ W₁ʲ`. -/
theorem ex_20_6_sharing0 [Finite S] (θ : Fin n → ℝ) {W : Fin n → ℝ × ℝ → ℝ}
    {R : Fin n → (S → ℝ) → ℝ} {u : Fin n → ℝ → ℝ} {F : ℝ → ℝ} {z0 k0 : ℝ} {z1 : S → ℝ}
    {c0 : Fin n → ℝ} {k1 : ℝ} {c1 : S → Fin n → ℝ}
    (hopt : ∀ c0' k1' c1', ∑ i, c0' i + k1' = z0 * F k0 → (∀ s, ∑ i, c1' s i = z1 s * F k1') →
      pa_planner θ W R u c0' c1' ≤ pa_planner θ W R u c0 c1)
    (hf0 : ∑ i, c0 i + k1 = z0 * F k0) (hf1 : ∀ s, ∑ i, c1 s i = z1 s * F k1)
    {DW : Fin n → ℝ × ℝ →L[ℝ] ℝ} {DR : Fin n → (S → ℝ) →L[ℝ] ℝ} {du : Fin n → S → ℝ}
    (hW : ∀ i, HasFDerivAt (W i) (DW i) (c0 i, R i fun s => u i (c1 s i)))
    (hR : ∀ i, HasFDerivAt (R i) (DR i) fun s => u i (c1 s i))
    (hu : ∀ i s, HasDerivAt (u i) (du i s) (c1 s i)) {i j : Fin n} :
    θ i * DW i (1, 0) = θ j * DW j (1, 0) := by
  have := Fintype.ofFinite S
  classical
  set d : Fin n → ℝ := fun l => (if l = i then 1 else 0) - (if l = j then 1 else 0) with hd
  have hD := pa_planner_hasDerivAt θ hW hR hu (p0 := fun l t => c0 l + t * d l)
    (p1 := fun s l _ => c1 s l) (d0 := d) (d1 := fun _ _ => 0)
    (fun l => by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d l)).const_add (c0 l))
    (fun s l => hasDerivAt_const _ _) (fun l => by simp) (fun s l => rfl)
  have hmax : IsLocalMax (fun t => pa_planner θ W R u (fun l => c0 l + t * d l)
      fun s l => c1 s l) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_mul, add_zero]
    refine hopt _ k1 c1 ?_ hf1
    rw [← hf0, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hd, Finset.sum_sub_distrib]
  have h0 := hmax.hasDerivAt_eq_zero hD
  simp only [mul_zero, Finset.sum_const_zero, add_zero] at h0
  simp only [hd, sub_mul, ite_mul, one_mul, zero_mul, mul_sub, mul_ite, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
  linarith

omit [Fintype S] in
/-- **Exercise 20.6** (Miao, p. 735), date-1 risk sharing in state `s`:
`θᵢ W₂ⁱ Rₛⁱ uⁱ'(c₁ⁱ(s)) = θⱼ W₂ʲ Rₛʲ uʲ'(c₁ʲ(s))`. -/
theorem ex_20_6_sharing1 [Finite S] (θ : Fin n → ℝ) {W : Fin n → ℝ × ℝ → ℝ}
    {R : Fin n → (S → ℝ) → ℝ} {u : Fin n → ℝ → ℝ} {F : ℝ → ℝ} {z0 k0 : ℝ} {z1 : S → ℝ}
    {c0 : Fin n → ℝ} {k1 : ℝ} {c1 : S → Fin n → ℝ}
    (hopt : ∀ c0' k1' c1', ∑ i, c0' i + k1' = z0 * F k0 → (∀ s, ∑ i, c1' s i = z1 s * F k1') →
      pa_planner θ W R u c0' c1' ≤ pa_planner θ W R u c0 c1)
    (hf0 : ∑ i, c0 i + k1 = z0 * F k0) (hf1 : ∀ s, ∑ i, c1 s i = z1 s * F k1)
    {DW : Fin n → ℝ × ℝ →L[ℝ] ℝ} {DR : Fin n → (S → ℝ) →L[ℝ] ℝ} {du : Fin n → S → ℝ}
    (hW : ∀ i, HasFDerivAt (W i) (DW i) (c0 i, R i fun s => u i (c1 s i)))
    (hR : ∀ i, HasFDerivAt (R i) (DR i) fun s => u i (c1 s i))
    (hu : ∀ i s, HasDerivAt (u i) (du i s) (c1 s i)) {i j : Fin n} (s : S) :
    θ i * DW i (0, 1) * DR i (Pi.single s 1) * du i s
      = θ j * DW j (0, 1) * DR j (Pi.single s 1) * du j s := by
  have := Fintype.ofFinite S
  set d : S → Fin n → ℝ := fun s' l => if s' = s then
    (if l = i then 1 else 0) - (if l = j then 1 else 0) else 0 with hd
  have hD := pa_planner_hasDerivAt θ hW hR hu (p0 := fun l _ => c0 l)
    (p1 := fun s' l t => c1 s' l + t * d s' l) (d0 := fun _ => 0) (d1 := d)
    (fun l => hasDerivAt_const _ _)
    (fun s' l => by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d s' l)).const_add (c1 s' l))
    (fun l => rfl) (fun s' l => by simp)
  have hmax : IsLocalMax (fun t => pa_planner θ W R u (fun l => c0 l)
      fun s' l => c1 s' l + t * d s' l) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_mul, add_zero]
    refine hopt _ k1 _ hf0 fun s' => ?_
    rw [← hf1 s', Finset.sum_add_distrib, ← Finset.mul_sum]
    by_cases hs : s' = s
    · simp [hd, hs, Finset.sum_sub_distrib]
    · simp [hd, hs]
  have h0 := hmax.hasDerivAt_eq_zero hD
  simp only [zero_mul, zero_add] at h0
  simp only [hd, mul_ite, mul_zero, mul_sub, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, Finset.sum_sub_distrib] at h0
  linear_combination h0

/-- **Exercise 20.6** (Miao, p. 735), the Euler equation for capital: for an agent with
`θᵢ > 0`, `W₁ⁱ = W₂ⁱ ∑ₛ Rₛⁱ uⁱ'(c₁ⁱ(s)) z₁(s) F'(k₁)`. -/
theorem ex_20_6_euler (θ : Fin n → ℝ) {W : Fin n → ℝ × ℝ → ℝ}
    {R : Fin n → (S → ℝ) → ℝ} {u : Fin n → ℝ → ℝ} {F : ℝ → ℝ} {z0 k0 : ℝ} {z1 : S → ℝ}
    {c0 : Fin n → ℝ} {k1 : ℝ} {c1 : S → Fin n → ℝ}
    (hopt : ∀ c0' k1' c1', ∑ i, c0' i + k1' = z0 * F k0 → (∀ s, ∑ i, c1' s i = z1 s * F k1') →
      pa_planner θ W R u c0' c1' ≤ pa_planner θ W R u c0 c1)
    (hf0 : ∑ i, c0 i + k1 = z0 * F k0) (hf1 : ∀ s, ∑ i, c1 s i = z1 s * F k1)
    {DW : Fin n → ℝ × ℝ →L[ℝ] ℝ} {DR : Fin n → (S → ℝ) →L[ℝ] ℝ} {du : Fin n → S → ℝ}
    {dF : ℝ} (hW : ∀ i, HasFDerivAt (W i) (DW i) (c0 i, R i fun s => u i (c1 s i)))
    (hR : ∀ i, HasFDerivAt (R i) (DR i) fun s => u i (c1 s i))
    (hu : ∀ i s, HasDerivAt (u i) (du i s) (c1 s i)) (hF : HasDerivAt F dF k1) {i : Fin n}
    (hθ : 0 < θ i) :
    DW i (1, 0) = DW i (0, 1) * ∑ s, DR i (Pi.single s 1) * du i s * z1 s * dF := by
  set δ : Fin n → ℝ := fun l => if l = i then 1 else 0 with hδ
  have hFt : HasDerivAt (fun t => F (k1 + t)) dF 0 := by
    have := HasDerivAt.comp_add_const 0 k1 (by rwa [zero_add])
    simpa [add_comm] using this
  have hD := pa_planner_hasDerivAt θ hW hR hu (p0 := fun l t => c0 l - t * δ l)
    (p1 := fun s l t => c1 s l + δ l * z1 s * (F (k1 + t) - F k1))
    (d0 := fun l => -δ l) (d1 := fun s l => δ l * z1 s * dF)
    (fun l => by
      have := ((hasDerivAt_id (0 : ℝ)).mul_const (δ l)).const_sub (c0 l)
      simpa using this)
    (fun s l => by
      have := ((hFt.sub_const (F k1)).const_mul (δ l * z1 s)).const_add (c1 s l)
      simpa using this)
    (fun l => by simp) (fun s l => by simp)
  have hmax : IsLocalMax (fun t => pa_planner θ W R u (fun l => c0 l - t * δ l)
      fun s l => c1 s l + δ l * z1 s * (F (k1 + t) - F k1)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_mul, sub_zero, add_zero, sub_self, mul_zero]
    refine hopt _ (k1 + t) _ ?_ fun s => ?_
    · rw [← hf0, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [hδ]
    · rw [Finset.sum_add_distrib, hf1 s, ← Finset.sum_mul, ← Finset.sum_mul]
      simp [hδ]
      ring
  have h0 := hmax.hasDerivAt_eq_zero hD
  rw [Finset.sum_eq_single i (fun l _ hl => by simp [hδ, hl]) (by simp)] at h0
  simp only [hδ, ↓reduceIte, neg_mul, one_mul] at h0
  have hsum : ∑ s, DR i (Pi.single s 1) * (du i s * (z1 s * dF))
      = ∑ s, DR i (Pi.single s 1) * du i s * z1 s * dF :=
    Finset.sum_congr rfl fun s _ => by ring
  rw [hsum] at h0
  have := (mul_eq_zero.1 h0).resolve_left hθ.ne'
  linarith

/-! ### Exercise 20.7 -/

/-- The multiplier certainty equivalent `−ϑ ln ∑ₛ p(s) exp(−v(s)/ϑ)`. -/
noncomputable def pa_multCE (ϑ : ℝ) (p v : S → ℝ) : ℝ :=
  -ϑ * Real.log (∑ s, p s * Real.exp (-v s / ϑ))

/-- The worst-case distortion `m(s) = e^{−v(s)/ϑ}/∑ p e^{−v/ϑ}`. -/
noncomputable def pa_distortion (ϑ : ℝ) (p v : S → ℝ) (s : S) : ℝ :=
  Real.exp (-v s / ϑ) / ∑ s', p s' * Real.exp (-v s' / ϑ)

/-- Exercise 20.7: perturbing the continuation value in state `s` by `t·d`, the multiplier
certainty equivalent has derivative `p(s) m(s) d`. -/
theorem pa_multiplier_hasDerivAt {ϑ : ℝ} (hϑ : ϑ ≠ 0) {p v : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) (s : S) (d : ℝ) :
    HasDerivAt (fun t => pa_multCE ϑ p (fun s' => v s' + if s' = s then t * d else 0))
      (p s * pa_distortion ϑ p v s * d) 0 := by
  have hpos : 0 < ∑ s', p s' * Real.exp (-v s' / ϑ) :=
    pa_E_pos hp hp1 fun s' => Real.exp_pos _
  have hterm : ∀ s', HasDerivAt
      (fun t => p s' * Real.exp (-(v s' + if s' = s then t * d else 0) / ϑ))
      (if s' = s then p s' * (Real.exp (-v s' / ϑ) * (-d / ϑ)) else 0) 0 := by
    intro s'
    by_cases hs : s' = s
    · subst hs
      simp only [↓reduceIte]
      have h := ((((hasDerivAt_id (0 : ℝ)).mul_const d).const_add (v s')).neg.div_const ϑ).exp
      have := h.const_mul (p s')
      simpa using this
    · simp only [hs, ↓reduceIte, add_zero]
      exact hasDerivAt_const _ _
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun s' _ => hterm s'
  have h0 : (∑ s', p s' * Real.exp (-(v s' + if s' = s then (0 : ℝ) * d else 0) / ϑ))
      = ∑ s', p s' * Real.exp (-v s' / ϑ) := by simp
  have hlog := (hsum.log (by rw [h0]; exact hpos.ne')).const_mul (-ϑ)
  unfold pa_multCE
  convert hlog using 1
  rw [h0]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, pa_distortion]
  field_simp

/-- Multiplier preferences `Uⁱ = uⁱ(c₀ⁱ) − βϑᵢ ln E exp(−uⁱ(c₁ⁱ)/ϑᵢ)` and the planner's
objective `∑ λᵢ Uⁱ`. -/
noncomputable def pa_multPlanner (lam ϑ : Fin n → ℝ) (β : ℝ) (p : S → ℝ) (u : Fin n → ℝ → ℝ)
    (c0 : Fin n → ℝ) (c1 : S → Fin n → ℝ) : ℝ :=
  ∑ i, lam i * (u i (c0 i) + β * pa_multCE (ϑ i) p fun s => u i (c1 s i))

omit [DecidableEq S] in
/-- **Exercise 20.7(a)** (Miao, p. 736): first-order conditions for a Pareto optimum with
multiplier preferences in the pure exchange economy (`∑ᵢ c₀ⁱ = e₀`, `∑ᵢ c₁ⁱ(s) = e₁(s)`):
`λᵢ uⁱ'(c₀ⁱ) = λⱼ uʲ'(c₀ʲ)` and, in each state with `p(s) > 0`,
`λᵢ mᵢ(s) uⁱ'(c₁ⁱ(s)) = λⱼ mⱼ(s) uʲ'(c₁ʲ(s))`. -/
theorem ex_20_7 {lam ϑ : Fin n → ℝ} {β : ℝ} (hβ : 0 < β) {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) (hϑ : ∀ i, ϑ i ≠ 0) {u du0 : Fin n → ℝ → ℝ} {du1 : Fin n → S → ℝ}
    {e0 : ℝ} {e1 : S → ℝ} {c0 : Fin n → ℝ} {c1 : S → Fin n → ℝ}
    (hopt : ∀ c0' c1', ∑ i, c0' i = e0 → (∀ s, ∑ i, c1' s i = e1 s) →
      pa_multPlanner lam ϑ β p u c0' c1' ≤ pa_multPlanner lam ϑ β p u c0 c1)
    (hf0 : ∑ i, c0 i = e0) (hf1 : ∀ s, ∑ i, c1 s i = e1 s)
    (hu0 : ∀ i, HasDerivAt (u i) (du0 i (c0 i)) (c0 i))
    (hu1 : ∀ i s, HasDerivAt (u i) (du1 i s) (c1 s i)) {i j : Fin n} :
    lam i * du0 i (c0 i) = lam j * du0 j (c0 j) ∧
    ∀ s, 0 < p s → lam i * pa_distortion (ϑ i) p (fun s => u i (c1 s i)) s * du1 i s
      = lam j * pa_distortion (ϑ j) p (fun s => u j (c1 s j)) s * du1 j s := by
  classical
  set d : Fin n → ℝ := fun l => (if l = i then 1 else 0) - (if l = j then 1 else 0) with hd
  have hdsum : ∑ l, d l = 0 := by simp [hd, Finset.sum_sub_distrib]
  constructor
  · have hD : HasDerivAt (fun t => pa_multPlanner lam ϑ β p u (fun l => c0 l + t * d l) c1)
        (∑ l, lam l * (du0 l (c0 l) * d l)) 0 := by
      unfold pa_multPlanner
      refine HasDerivAt.fun_sum fun l _ => HasDerivAt.const_mul (lam l) ?_
      have := ((hu0 l).comp_of_eq 0 (((hasDerivAt_id (0 : ℝ)).mul_const (d l)).const_add (c0 l))
        (by simp)).add_const (β * pa_multCE (ϑ l) p fun s => u l (c1 s l))
      simpa using this
    have hmax : IsLocalMax (fun t => pa_multPlanner lam ϑ β p u (fun l => c0 l + t * d l) c1)
        0 := by
      refine Filter.Eventually.of_forall fun t => ?_
      simp only [zero_mul, add_zero]
      refine hopt _ c1 ?_ hf1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdsum, mul_zero, add_zero, hf0]
    have h0 := hmax.hasDerivAt_eq_zero hD
    simp only [hd, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
    linarith
  · intro s hs
    have hD : HasDerivAt (fun t => pa_multPlanner lam ϑ β p u c0
          fun s' l => c1 s' l + if s' = s then t * d l else 0)
        (∑ l, lam l * (β * (p s * pa_distortion (ϑ l) p (fun s => u l (c1 s l)) s
          * (du1 l s * d l)))) 0 := by
      unfold pa_multPlanner
      refine HasDerivAt.fun_sum fun l _ => HasDerivAt.const_mul (lam l) ?_
      refine HasDerivAt.const_add _ (HasDerivAt.const_mul β ?_)
      -- the continuation value moves only in state `s`, to first order by `t u'(c₁(s)) d`
      have hcomp : HasDerivAt (fun t => pa_multCE (ϑ l) p
          fun s' => u l (c1 s' l + if s' = s then t * d l else 0))
          (p s * pa_distortion (ϑ l) p (fun s => u l (c1 s l)) s * (du1 l s * d l)) 0 := by
        have hus : HasDerivAt (fun t => u l (c1 s l + t * d l)) (du1 l s * d l) 0 := by
          have := (hu1 l s).comp_of_eq 0
            (((hasDerivAt_id (0 : ℝ)).mul_const (d l)).const_add (c1 s l)) (by simp)
          rw [one_mul] at this
          exact this
        have hpos : 0 < ∑ s', p s' * Real.exp (-u l (c1 s' l) / ϑ l) :=
          pa_E_pos hp hp1 fun s' => Real.exp_pos _
        have hterm : ∀ s', HasDerivAt (fun t => p s' *
            Real.exp (-u l (c1 s' l + if s' = s then t * d l else 0) / ϑ l))
            (if s' = s then p s' * (Real.exp (-u l (c1 s' l) / ϑ l) *
              (-(du1 l s * d l) / ϑ l)) else 0) 0 := by
          intro s'
          by_cases h : s' = s
          · subst h
            simp only [↓reduceIte]
            have := (((hus.neg).div_const (ϑ l)).exp).const_mul (p s')
            simpa using this
          · simp only [h, ↓reduceIte, add_zero]
            exact hasDerivAt_const _ _
        have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun s' _ => hterm s'
        have h0 : (∑ s', p s' * Real.exp (-u l (c1 s' l + if s' = s then (0 : ℝ) * d l else 0)
            / ϑ l)) = ∑ s', p s' * Real.exp (-u l (c1 s' l) / ϑ l) := by simp
        have hlog := (hsum.log (by rw [h0]; exact hpos.ne')).const_mul (-ϑ l)
        unfold pa_multCE
        convert hlog using 1
        rw [h0]
        have := hϑ l
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, pa_distortion]
        field_simp
      exact hcomp
    have hmax : IsLocalMax (fun t => pa_multPlanner lam ϑ β p u c0
        fun s' l => c1 s' l + if s' = s then t * d l else 0) 0 := by
      refine Filter.Eventually.of_forall fun t => ?_
      simp only [zero_mul, ite_self, add_zero]
      refine hopt _ _ hf0 fun s' => ?_
      rw [Finset.sum_add_distrib, hf1 s']
      by_cases h : s' = s
      · simp only [h, ↓reduceIte, ← Finset.mul_sum, hdsum, mul_zero, add_zero]
      · simp [h]
    have h0 := hmax.hasDerivAt_eq_zero hD
    simp only [hd, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
    have hk : 0 < β * p s := mul_pos hβ hs
    have : β * p s * (lam i * pa_distortion (ϑ i) p (fun s => u i (c1 s i)) s * du1 i s
        - lam j * pa_distortion (ϑ j) p (fun s => u j (c1 s j)) s * du1 j s) = 0 := by
      rw [← h0]; ring
    have := (mul_eq_zero.1 this).resolve_left hk.ne'
    linarith

end Miao.RecursiveUtility
