/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.IndirectInterior

/-!
# An economy satisfying `InteriorHyp`

SLP §18.1, pp. 543–546 (the economy is not in the book). `U(c) = 1 − e^{−√c}` (`inadaU`) and
`f(k) = √k` on `K = [0, 1]` satisfy every hypothesis of `ex_18_1_interior` and
`indirect_equilibrium_interior`, so those hypotheses are consistent.

* `inadaU_strictConcaveOn`, `inadaU_monotoneOn`, `abs_inadaU_le`, `differentiableAt_inadaU`:
  `U` is strictly concave, nondecreasing and bounded on `[0, ∞)`, and differentiable on `(0, ∞)`.
* `inadaU_inada`: `(U(c) − U(0))/c → ∞` as `c → 0+`.
* `inadaU_not_differentiableAt_zero`: `U` is not differentiable at `0`, so the economy is outside
  `plannerHyp_of_differentiable`, `ex_18_1_constructed` and `indirect_equilibrium_constructed`.
* `inada_interiorHyp`: `InteriorHyp inadaU √ b 1` for every `b ∈ (0, 1)`.
* `inada_example_interior`, `inada_example_ex_18_1`, `inada_example_equilibrium`: the constructed
  policies are interior on `(0, 1]`; Exercise 18.1 and the recursive competitive equilibrium of
  the taxed economy hold there.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set

/-- The utility `U(c) = 1 − e^{−√c}`: bounded, strictly concave, with `U′(0+) = ∞`. -/
noncomputable def inadaU (c : ℝ) : ℝ := 1 - Real.exp (-Real.sqrt c)

/-- `U(0) = 0`. -/
theorem inadaU_zero : inadaU 0 = 0 := by
  simp [inadaU]

/-- `U` is continuous. -/
theorem continuous_inadaU : Continuous inadaU := by
  unfold inadaU
  fun_prop

/-- `U` is nondecreasing on `[0, ∞)`. -/
theorem inadaU_monotoneOn : MonotoneOn inadaU (Ici 0) := fun c _ d _ h => by
  have h1 := Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt h))
  simp only [inadaU]
  linarith

/-- `U` is strictly concave on `[0, ∞)`: `s ↦ 1 − e^{−s}` is concave and strictly increasing, and
`√` is strictly concave. -/
theorem inadaU_strictConcaveOn : StrictConcaveOn ℝ (Ici 0) inadaU := by
  have himg : Real.sqrt '' Ici 0 = Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact Real.sqrt_nonneg x
    · intro hy
      exact ⟨y ^ 2, sq_nonneg y, Real.sqrt_sq hy⟩
  have hg : ConcaveOn ℝ (Real.sqrt '' Ici 0) (fun s : ℝ => 1 - Real.exp (-s)) := by
    rw [himg]
    refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
    have h := convexOn_exp.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    have e : -(a * x + b * y) = a * -x + b * -y := by ring
    rw [e]
    nlinarith
  have hg' : StrictMonoOn (fun s : ℝ => 1 - Real.exp (-s)) (Real.sqrt '' Ici 0) :=
    fun x _ y _ h => by
      have := Real.exp_lt_exp.2 (neg_lt_neg h)
      simp only
      linarith
  exact hg.comp_strictConcaveOn Real.strictConcaveOn_sqrt hg'

/-- `0 ≤ U < 1` (on all of `ℝ`, since `√c = 0` for `c < 0`), so `|U| ≤ 1`. -/
theorem abs_inadaU_le (c : ℝ) : |inadaU c| ≤ 1 := by
  have h1 : Real.exp (-Real.sqrt c) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg c))
  have h2 := Real.exp_pos (-Real.sqrt c)
  have h0 : 0 ≤ inadaU c := by simp only [inadaU]; linarith
  rw [abs_of_nonneg h0]
  simp only [inadaU]
  linarith

/-- `U` is differentiable on `(0, ∞)`. -/
theorem differentiableAt_inadaU {c : ℝ} (hc : 0 < c) : DifferentiableAt ℝ inadaU c :=
  ((Real.hasDerivAt_sqrt hc.ne').differentiableAt.neg.exp).const_sub 1

/-- **The Inada condition** `(U(c) − U(0))/c → ∞` as `c → 0+`: with `s = √c ≤ 1`,
`1 − e^{−s} ≥ s/(1 + s) ≥ s/2`, so the quotient is at least `1/(2s)`. -/
theorem inadaU_inada : Tendsto (fun c => (inadaU c - inadaU 0) / c) (𝓝[>] 0) atTop := by
  rw [inadaU_zero]
  refine tendsto_atTop.2 fun L => ?_
  set L' := max L 1 with hL'
  have hL'0 : 0 < L' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hδ : (0 : ℝ) < min 1 ((1 / (2 * L')) ^ 2) := lt_min zero_lt_one (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with c hc
  have hc0 : 0 < c := hc.1
  set s := Real.sqrt c with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hc0
  have hs1 : s < 1 := (Real.sqrt_lt' zero_lt_one).2 (by
    have := hc.2.trans_le (min_le_left _ _); linarith)
  have hs2 : s < 1 / (2 * L') := (Real.sqrt_lt' (by positivity)).2
    (hc.2.trans_le (min_le_right _ _))
  have hsc : s ^ 2 = c := Real.sq_sqrt hc0.le
  have hexp : Real.exp (-s) * (1 + s) ≤ 1 := by
    have h1 := Real.add_one_le_exp s
    have h2 := Real.exp_pos (-s)
    have h3 : Real.exp (-s) * Real.exp s = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith
  have hE1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hhalf : s / 2 ≤ 1 - Real.exp (-s) := by nlinarith
  have h2Ls : 2 * L' * s < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hs2
    linarith
  rw [sub_zero, le_div_iff₀ hc0]
  have hLL : L * c ≤ L' * c := mul_le_mul_of_nonneg_right (le_max_left _ _) hc0.le
  simp only [inadaU]
  rw [← hs]
  nlinarith

/-- **`U` is not differentiable at `0`**: a derivative there would be the finite limit of the
quotients of `inadaU_inada`. So `U` violates the hypotheses of `plannerHyp_of_differentiable`,
`ex_18_1_constructed` and `indirect_equilibrium_constructed`. -/
theorem inadaU_not_differentiableAt_zero : ¬ DifferentiableAt ℝ inadaU 0 := by
  intro hd
  have h := hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt
  have h' : Tendsto (slope inadaU 0) (𝓝[>] 0) (𝓝 (deriv inadaU 0)) :=
    h.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt (mem_Ioi.1 hx))
  have hI : Tendsto (slope inadaU 0) (𝓝[>] 0) atTop := by
    refine inadaU_inada.congr fun c => ?_
    rw [slope_def_field, sub_zero]
  exact not_tendsto_nhds_of_tendsto_atTop hI _ h'

/-- **The example satisfies `InteriorHyp`**: for `b ∈ (0, 1)`, `U(c) = 1 − e^{−√c}`,
`f(k) = √k` and `k̄ = 1`. -/
theorem inada_interiorHyp {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    InteriorHyp inadaU Real.sqrt b 1 where
  planner :=
    { b_nonneg := hb0.le
      b_lt_one := hb1
      kbar_nonneg := zero_le_one
      U_cont := continuous_inadaU.continuousOn
      U_mono := inadaU_monotoneOn
      U_strictConcave := inadaU_strictConcaveOn
      f_cont := Real.continuous_sqrt.continuousOn
      f_concave := Real.strictConcaveOn_sqrt.concaveOn.subset Icc_subset_Ici_self (convex_Icc 0 1)
      f_nonneg := fun k _ => Real.sqrt_nonneg k
      f_le := fun _ hk => Real.sqrt_le_one.2 hk.2 }
  b_pos := hb0
  U_inada := inadaU_inada
  f_zero := Real.sqrt_zero
  f_pos := fun _ hk => Real.sqrt_pos.2 hk.1

/-- `f(k) = √k` is differentiable on `(0, 1]` with `f′ ≥ 0` there. -/
theorem sqrt_deriv_facts : (∀ k ∈ Ioc (0 : ℝ) 1, DifferentiableAt ℝ Real.sqrt k) ∧
    ∀ k ∈ Ioc (0 : ℝ) 1, 0 ≤ deriv Real.sqrt k :=
  ⟨fun k hk => (Real.hasDerivAt_sqrt hk.1.ne').differentiableAt, fun k hk => by
    rw [(Real.hasDerivAt_sqrt hk.1.ne').deriv]
    positivity⟩

/-- **The constructed policy of the example is interior** on `(0, 1]`:
`0 < g(k) < √k`. -/
theorem inada_example_interior {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ k ∈ Ioc (0 : ℝ) 1, 0 < plannerPolicy (inada_interiorHyp hb0 hb1).planner k ∧
      plannerPolicy (inada_interiorHyp hb0 hb1).planner k < Real.sqrt k :=
  fun _ hk => (inada_interiorHyp hb0 hb1).policy_interior hk

/-- **Exercise 18.1 in the example** (p. 544): for `β ∈ (0, 1)`, the bounded solution `V` of (2)
on `[0, ∞) × (0, 1]` exists, `V(k, k; g) = v(k)` and `G(k, k; g) = g(k)` for the constructed `g`,
which is interior. -/
theorem inada_example_ex_18_1 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ k ∈ Ioc (0 : ℝ) 1, 0 < plannerPolicy (inada_interiorHyp hβ0 hβ1).planner k ∧
      plannerPolicy (inada_interiorHyp hβ0 hβ1).planner k < Real.sqrt k) ∧
    ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Ioc (0 : ℝ) 1, |V x k| ≤ M) ∧
      SolvesBellman inadaU (fun k => Real.sqrt k - k * deriv Real.sqrt k) (deriv Real.sqrt)
        (plannerPolicy (inada_interiorHyp hβ0 hβ1).planner) V β (Ioc 0 1) ∧
      ∀ k ∈ Ioc (0 : ℝ) 1, V k k = plannerValue (inada_interiorHyp hβ0 hβ1).planner k ∧
        ∀ y ∈ feasY (fun k => Real.sqrt k - k * deriv Real.sqrt k) (deriv Real.sqrt) k k,
          (inadaU (Real.sqrt k + (k - k) * deriv Real.sqrt k - y) +
            β * V y (plannerPolicy (inada_interiorHyp hβ0 hβ1).planner k) = V k k ↔
              y = plannerPolicy (inada_interiorHyp hβ0 hβ1).planner k) := by
  obtain ⟨hint, -, -, -, -, V, M, hVb, hsol, -, hall, -⟩ := ex_18_1_interior
    (inada_interiorHyp hβ0 hβ1) (fun c hc => differentiableAt_inadaU hc)
    (fun c _ => abs_inadaU_le c) Real.strictConcaveOn_sqrt.concaveOn sqrt_deriv_facts.1
    sqrt_deriv_facts.2
  exact ⟨hint, V, M, hVb, hsol, fun k hk => ⟨(hall k hk).1, (hall k hk).2.2⟩⟩

/-- **The indirect equilibrium in the example** (p. 546): for `β ∈ (0, 1)` and `θ ∈ [0, 1)`, the
pseudo-planner's policy `ĥ` (discount factor `(1 − θ)β`) is interior on `(0, 1]`, and it is a
recursive competitive equilibrium of the taxed economy: the bounded solution `W` of (3) with
`h = ĥ` has `H(k, k; ĥ) = ĥ(k)` for `k ∈ (0, 1]`. -/
theorem inada_example_equilibrium {β θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) :
    ∃ I : InteriorHyp inadaU Real.sqrt ((1 - θ) * β) 1,
      (∀ k ∈ Ioc (0 : ℝ) 1, 0 < plannerPolicy I.planner k ∧
        plannerPolicy I.planner k < Real.sqrt k) ∧
      ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Ioc (0 : ℝ) 1, |W x k| ≤ M) ∧
        SolvesBellman inadaU (fun k => Real.sqrt k - (1 - θ) * k * deriv Real.sqrt k)
          (fun k => (1 - θ) * deriv Real.sqrt k) (plannerPolicy I.planner) W β (Ioc 0 1) ∧
        ∀ k ∈ Ioc (0 : ℝ) 1, ∀ y ∈ feasY (fun k => Real.sqrt k - (1 - θ) * k * deriv Real.sqrt k)
            (fun k => (1 - θ) * deriv Real.sqrt k) k k,
          (inadaU (Real.sqrt k + (1 - θ) * (k - k) * deriv Real.sqrt k - y) +
            β * W y (plannerPolicy I.planner k) = W k k ↔ y = plannerPolicy I.planner k) := by
  have hb0 : 0 < (1 - θ) * β := mul_pos (by linarith) hβ0
  have hb1 : (1 - θ) * β < 1 := by nlinarith
  have I := inada_interiorHyp hb0 hb1
  obtain ⟨hint, -, -, -, -, -, W, M, hWb, hsol, -, hall, -⟩ := indirect_equilibrium_interior I
    hβ1 hθ0 hθ1 (fun c hc => differentiableAt_inadaU hc) (fun c _ => abs_inadaU_le c)
    Real.strictConcaveOn_sqrt.concaveOn sqrt_deriv_facts.1 sqrt_deriv_facts.2
  exact ⟨I, hint, W, M, hWb, hsol, fun k hk => (hall k hk).2⟩

end StokeyLucasPrescott.EquilibriaWithDistortions
