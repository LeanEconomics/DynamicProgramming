/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.IndirectInteriorGeneral

/-!
# Economies for `IndirectInteriorGeneral`

SLP §18.1, pp. 543–546 (the economies are not in the book). They show that the hypotheses
`PosOutputInadaHyp` and `FiniteMarginalHyp` are consistent, and that the added conditions are
needed.

* `expU`, `U(c) = 1 − e^{−c}`: bounded, strictly concave, with finite `U′(0) = 1`
  (`expU_strictConcaveOn`, `hasDerivWithinAt_expU_zero`, `abs_expU_le`).
* `sqrtTech`, `f(k) = 4 + 4√(1 + k)` on `K = [0, 24]`: concave, nondecreasing, `f(0) = 8`,
  `f′(0) = 2`, `1`-Lipschitz on `[3, 24]` (`sqrtTech_concaveOn`, `hasDerivAt_sqrtTech_zero`,
  `sqrtTech_lipschitz`).
* `sqrtTech_posOutputInadaHyp`: `U(c) = 1 − e^{−√c}` (`U′(0+) = ∞`) and `sqrtTech` satisfy
  `PosOutputInadaHyp` for `b ∈ (1/2, 1)`; `sqrtTech_inada_ex_18_1`, `sqrtTech_inada_equilibrium`:
  the policies are interior on all of `[0, 24]`, the transversality conditions hold from `k = 0`,
  and Exercise 18.1 and the recursive competitive equilibrium hold on `[0, 24]`.
* `sqrtTech_finiteMarginalHyp`: `expU` and `sqrtTech` satisfy `FiniteMarginalHyp` for
  `b ∈ (1/2, 1)`; `sqrtTech_finite_ex_18_1`, `sqrtTech_finite_equilibrium`: likewise.
* `rootTech_posOutputInadaHyp`, `rootTech_interior`: `U(c) = 1 − e^{−√c}` and `f(k) = 1 + √k` on
  `[0, 4]` (`f′(0+) = ∞`) satisfy `PosOutputInadaHyp` for every `b ∈ (0, 1)`, and the policy is
  interior on all of `[0, 4]`.

**Counterexamples** (the added hypotheses are needed).

* `inada_const_counterexample`: `U(c) = 1 − e^{−√c}`, `f ≡ 1`: `U′(0+) = ∞` and `f(0) > 0`, but
  the slope condition fails and `g ≡ 0`.
* `finite_const_counterexample`: `expU`, `f ≡ 1`: everything in `FiniteMarginalHyp` but the slope
  condition holds, and `g ≡ 0`.
* `corner_counterexample`: `expU`, `f(k) = min{1/100 + 10k, 1}` (`cornerF`), `b = 1/2`:
  everything in `FiniteMarginalHyp` but the Lipschitz condition holds, and `g = f` on
  `[0, 1/1000]`: the planner consumes nothing.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set BoundedContinuousFunction

/-- The utility `U(c) = 1 − e^{−c}`: bounded, strictly concave, with finite `U′(0) = 1`. -/
noncomputable def expU (c : ℝ) : ℝ := 1 - Real.exp (-c)

/-- `U` is continuous. -/
theorem continuous_expU : Continuous expU := by
  unfold expU
  fun_prop

/-- `U′(c) = e^{−c}`. -/
theorem hasDerivAt_expU (c : ℝ) : HasDerivAt expU (Real.exp (-c)) c := by
  have h := ((hasDerivAt_neg c).exp).const_sub 1
  have e : expU = fun x => 1 - Real.exp (-x) := rfl
  rw [e]
  convert h using 1
  ring

/-- `U′(0) = 1`, finite. -/
theorem hasDerivWithinAt_expU_zero : HasDerivWithinAt expU 1 (Ici 0) 0 := by
  have h := (hasDerivAt_expU 0).hasDerivWithinAt (s := Ici 0)
  rwa [neg_zero, Real.exp_zero] at h

/-- `U` is nondecreasing on `[0, ∞)`. -/
theorem expU_monotoneOn : MonotoneOn expU (Ici 0) := fun c _ d _ h => by
  have := Real.exp_le_exp.2 (neg_le_neg h)
  simp only [expU]
  linarith

/-- `U` is strictly concave on `[0, ∞)` (`e^{−c}` is strictly convex). -/
theorem expU_strictConcaveOn : StrictConcaveOn ℝ (Ici 0) expU := by
  refine ⟨convex_Ici 0, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have h := strictConvexOn_exp.2 (mem_univ (-x)) (mem_univ (-y))
    (fun h => hxy (neg_injective h)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  simp only [expU]
  have e : -(a * x + b * y) = a * -x + b * -y := by ring
  rw [e]
  nlinarith

/-- `|U| ≤ 1` on `[0, ∞)`. -/
theorem abs_expU_le {c : ℝ} (hc : 0 ≤ c) : |expU c| ≤ 1 := by
  have h1 : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 := Real.exp_pos (-c)
  rw [abs_le]
  simp only [expU]
  constructor <;> linarith

/-- The slope of `U` on `[c′, c] ⊆ [0, 1]` is at least `e^{−1}`. -/
theorem expU_sub_ge {c c' : ℝ} (hcc : c' ≤ c) (hc1 : c ≤ 1) :
    Real.exp (-1) * (c - c') ≤ expU c - expU c' := by
  have h1 := Real.add_one_le_exp (c - c')
  have h2 : Real.exp (-c') = Real.exp (-c) * Real.exp (c - c') := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-1) ≤ Real.exp (-c) := Real.exp_le_exp.2 (by linarith)
  have h4 := Real.exp_pos (-c)
  simp only [expU]
  nlinarith

/-- The slope of `U` on `[c′, c] ⊆ [0, ∞)` is at most `1`. -/
theorem expU_sub_le {c c' : ℝ} (hc' : 0 ≤ c') (hcc : c' ≤ c) : expU c - expU c' ≤ c - c' := by
  have h1 := Real.add_one_le_exp (-(c - c'))
  have h2 : Real.exp (-c) = Real.exp (-c') * Real.exp (-(c - c')) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-c') ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h4 := Real.exp_pos (-c')
  have h5 : Real.exp (-(c - c')) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  simp only [expU]
  nlinarith

/-- `e ≤ 5`, i.e. `5 e^{−1} ≥ 1`. -/
theorem one_le_five_mul_exp_neg_one : 1 ≤ 5 * Real.exp (-1) := by
  have h1 := Real.add_one_le_exp (-1 / 2)
  have h2 : Real.exp (-1) = Real.exp (-1 / 2) * Real.exp (-1 / 2) := by
    rw [← Real.exp_add]; ring_nf
  nlinarith

/-- The technology `f(k) = 4 + 4√(1 + k)`: `f(0) = 8 > 0`, `f′(0) = 2` finite, on `K = [0, 24]`. -/
noncomputable def sqrtTech (k : ℝ) : ℝ := 4 + 4 * Real.sqrt (1 + k)

/-- `f` is continuous. -/
theorem continuous_sqrtTech : Continuous sqrtTech := by
  unfold sqrtTech
  fun_prop

/-- `f(0) = 8`. -/
theorem sqrtTech_zero : sqrtTech 0 = 8 := by
  simp only [sqrtTech, add_zero, Real.sqrt_one]
  norm_num

/-- `f′(k) = 2/√(1 + k)` for `k > −1`. -/
theorem hasDerivAt_sqrtTech {k : ℝ} (hk : -1 < k) :
    HasDerivAt sqrtTech (4 * (1 / (2 * Real.sqrt (1 + k)) * 1)) k := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 k := (hasDerivAt_id k).const_add 1
  have h2 := (Real.hasDerivAt_sqrt (by linarith : (1 + k) ≠ 0)).comp k h1
  have h3 := (h2.const_mul 4).const_add 4
  exact h3

/-- `f′(0) = 2`. -/
theorem hasDerivAt_sqrtTech_zero : HasDerivAt sqrtTech 2 0 := by
  have h := hasDerivAt_sqrtTech (by norm_num : (-1 : ℝ) < 0)
  rw [add_zero, Real.sqrt_one] at h
  convert h using 1
  norm_num

/-- `f` is differentiable with `f′ ≥ 0` on `[0, ∞)`. -/
theorem sqrtTech_deriv_facts : (∀ k : ℝ, 0 ≤ k → DifferentiableAt ℝ sqrtTech k) ∧
    ∀ k : ℝ, 0 ≤ k → 0 ≤ deriv sqrtTech k :=
  ⟨fun _ hk => (hasDerivAt_sqrtTech (by linarith)).differentiableAt, fun k hk => by
    rw [(hasDerivAt_sqrtTech (by linarith)).deriv]
    positivity⟩

/-- `f` is concave on `[0, ∞)`. -/
theorem sqrtTech_concaveOn : ConcaveOn ℝ (Ici 0) sqrtTech := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have h := Real.strictConcaveOn_sqrt.concaveOn.2 (mem_Ici.2 (by linarith [mem_Ici.1 hx]) :
    (1 + x) ∈ Ici 0) (mem_Ici.2 (by linarith [mem_Ici.1 hy]) : (1 + y) ∈ Ici 0) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have e : a * (1 + x) + b * (1 + y) = 1 + (a * x + b * y) := by
    have : b = 1 - a := by linarith
    subst this; ring
  rw [e] at h
  simp only [sqrtTech]
  nlinarith

/-- `f` is nondecreasing on `[0, ∞)`. -/
theorem sqrtTech_monotoneOn {S : Set ℝ} : MonotoneOn sqrtTech S := fun x _ y _ h => by
  have := Real.sqrt_le_sqrt (by linarith : 1 + x ≤ 1 + y)
  simp only [sqrtTech]
  linarith

/-- `0 ≤ f ≤ 24` on `[0, 24]`. -/
theorem sqrtTech_mem {k : ℝ} (hk : k ∈ Icc (0 : ℝ) 24) : 0 ≤ sqrtTech k ∧ sqrtTech k ≤ 24 := by
  have h1 := Real.sqrt_nonneg (1 + k)
  have h2 : Real.sqrt (1 + k) ≤ 5 := by
    rw [show (5 : ℝ) = Real.sqrt (5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith [hk.2])
  simp only [sqrtTech]
  constructor <;> linarith

/-- `f` is `1`-Lipschitz on `[3, 24]`: `|4√(1 + k) − 4√(1 + k′)| ≤ |k − k′|` since
`√(1 + k) + √(1 + k′) ≥ 4`. -/
theorem sqrtTech_lipschitz : ∀ k ∈ Icc (3 : ℝ) 24, ∀ k' ∈ Icc (3 : ℝ) 24,
    |sqrtTech k - sqrtTech k'| ≤ 1 * |k - k'| := by
  intro k hk k' hk'
  set s := Real.sqrt (1 + k) with hs
  set s' := Real.sqrt (1 + k') with hs'
  have h2 : ∀ x : ℝ, 3 ≤ x → 2 ≤ Real.sqrt (1 + x) := fun x hx => by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs2 := h2 k hk.1
  have hs2' := h2 k' hk'.1
  have hsq : s ^ 2 = 1 + k := Real.sq_sqrt (by linarith [hk.1])
  have hsq' : s' ^ 2 = 1 + k' := Real.sq_sqrt (by linarith [hk'.1])
  have e1 : sqrtTech k - sqrtTech k' = 4 * (s - s') := by simp only [sqrtTech, hs, hs']; ring
  have e2 : k - k' = (s - s') * (s + s') := by nlinarith
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (by linarith : 0 < s + s'), one_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

/-- The slope condition at `0` for `f = sqrtTech` when `b > 1/2`: with `m = (1 + 2b)/(2b)`,
`b m > 1` and `m < f′(0) = 2`. -/
theorem sqrtTech_slope {b : ℝ} (hb : 1 / 2 < b) :
    ∃ m, 1 < b * m ∧ ∀ᶠ y in 𝓝[>] 0, sqrtTech 0 + m * y ≤ sqrtTech y := by
  have hb0 : 0 < b := by linarith
  refine ⟨(1 + 2 * b) / (2 * b), ?_, eventually_add_mul_le_of_hasDerivAt hasDerivAt_sqrtTech_zero
    ?_⟩
  · rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity)]
    linarith

/-- **The economy `U(c) = 1 − e^{−√c}`, `f(k) = 4 + 4√(1 + k)` on `[0, 24]` satisfies
`PosOutputInadaHyp`** for every `b ∈ (1/2, 1)`: `f(0) = 8 > 0`, `U′(0+) = ∞`, `b f′(0) = 2b > 1`.
-/
theorem sqrtTech_posOutputInadaHyp {b : ℝ} (hb0 : 1 / 2 < b) (hb1 : b < 1) :
    PosOutputInadaHyp inadaU sqrtTech b 24 where
  planner :=
    { b_nonneg := by linarith
      b_lt_one := hb1
      kbar_nonneg := by norm_num
      U_cont := continuous_inadaU.continuousOn
      U_mono := inadaU_monotoneOn
      U_strictConcave := inadaU_strictConcaveOn
      f_cont := continuous_sqrtTech.continuousOn
      f_concave := sqrtTech_concaveOn.subset Icc_subset_Ici_self (convex_Icc 0 24)
      f_nonneg := fun _ hk => (sqrtTech_mem hk).1
      f_le := fun _ hk => (sqrtTech_mem hk).2 }
  b_pos := by linarith
  U_inada := inadaU_inada
  U_diff := fun _ hc => differentiableAt_inadaU hc
  f_zero_pos := by rw [sqrtTech_zero]; norm_num
  f_mono := sqrtTech_monotoneOn
  f_slope := sqrtTech_slope hb0

/-- **The economy `U(c) = 1 − e^{−c}`, `f(k) = 4 + 4√(1 + k)` on `[0, 24]` satisfies
`FiniteMarginalHyp`** for every `b ∈ (1/2, 1)`: `U′(0) = 1`, `b f′(0) = 2b > 1`, and `f` is
`1`-Lipschitz on `[3, 24]` with `3 < f(0) = 8` and `b · 1 < 1`. -/
theorem sqrtTech_finiteMarginalHyp {b : ℝ} (hb0 : 1 / 2 < b) (hb1 : b < 1) :
    FiniteMarginalHyp expU sqrtTech b 24 where
  planner :=
    { b_nonneg := by linarith
      b_lt_one := hb1
      kbar_nonneg := by norm_num
      U_cont := continuous_expU.continuousOn
      U_mono := expU_monotoneOn
      U_strictConcave := expU_strictConcaveOn
      f_cont := continuous_sqrtTech.continuousOn
      f_concave := sqrtTech_concaveOn.subset Icc_subset_Ici_self (convex_Icc 0 24)
      f_nonneg := fun _ hk => (sqrtTech_mem hk).1
      f_le := fun _ hk => (sqrtTech_mem hk).2 }
  b_pos := by linarith
  U_deriv_zero := ⟨1, one_pos, hasDerivWithinAt_expU_zero⟩
  U_diff := fun c _ => (hasDerivAt_expU c).differentiableAt
  f_mono := sqrtTech_monotoneOn
  f_slope := sqrtTech_slope hb0
  f_lip := ⟨3, 1, by norm_num, by rw [sqrtTech_zero]; norm_num, zero_le_one, by linarith,
    sqrtTech_lipschitz⟩

/-- **Exercise 18.1 on all of `K` in the economy `U(c) = 1 − e^{−√c}`, `f(k) = 4 + 4√(1 + k)`**
(`U′(0+) = ∞`, `f(0) = 8 > 0`), for `β ∈ (1/2, 1)`: the constructed policy is interior on
`[0, 24]`, the transversality condition holds from every `k ∈ [0, 24]` including `k = 0`, and the
bounded solution `V` of (2) on `[0, ∞) × [0, 24]` has `V(k, k; g) = v(k)` and `G(k, k; g) = g(k)`.
-/
theorem sqrtTech_inada_ex_18_1 {β : ℝ} (hβ0 : 1 / 2 < β) (hβ1 : β < 1) :
    ∃ I : PosOutputInadaHyp inadaU sqrtTech β 24,
      (∀ k ∈ Icc (0 : ℝ) 24, 0 < plannerPolicy I.planner k ∧
        plannerPolicy I.planner k < sqrtTech k) ∧
      (∀ k ∈ Icc (0 : ℝ) 24, Tendsto (fun t => β ^ t *
        deriv inadaU (sqrtTech ((plannerPolicy I.planner)^[t] k) -
          plannerPolicy I.planner ((plannerPolicy I.planner)^[t] k)) *
          deriv sqrtTech ((plannerPolicy I.planner)^[t] k) * (plannerPolicy I.planner)^[t] k)
            atTop (𝓝 0)) ∧
      ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc (0 : ℝ) 24, |V x k| ≤ M) ∧
        SolvesBellman inadaU (fun k => sqrtTech k - k * deriv sqrtTech k) (deriv sqrtTech)
          (plannerPolicy I.planner) V β (Icc 0 24) ∧
        ∀ k ∈ Icc (0 : ℝ) 24, V k k = plannerValue I.planner k ∧
          ∀ y ∈ feasY (fun k => sqrtTech k - k * deriv sqrtTech k) (deriv sqrtTech) k k,
            (inadaU (sqrtTech k + (k - k) * deriv sqrtTech k - y) +
              β * V y (plannerPolicy I.planner k) = V k k ↔ y = plannerPolicy I.planner k) := by
  have I := sqrtTech_posOutputInadaHyp hβ0 hβ1
  obtain ⟨hint, -, -, -, -, -, htvc, V, M, hVb, hsol, -, hall, -⟩ := I.ex_18_1 (B₀ := 1)
    (fun c _ => abs_inadaU_le c) sqrtTech_concaveOn (fun k hk => sqrtTech_deriv_facts.1 k hk.1)
    (fun k hk => sqrtTech_deriv_facts.2 k hk.1)
  exact ⟨I, hint, htvc, V, M, hVb, hsol, fun k hk => ⟨(hall k hk).1, (hall k hk).2.2⟩⟩

/-- **The indirect equilibrium on all of `K` in the economy `U(c) = 1 − e^{−√c}`,
`f(k) = 4 + 4√(1 + k)`** (p. 546), for `β < 1`, `θ ∈ [0, 1)` with `(1 − θ)β > 1/2`: the
pseudo-planner's policy `ĥ` is interior on `[0, 24]`, the individual's transversality condition
holds from every `k ∈ [0, 24]`, and `H(k, k; ĥ) = ĥ(k)` there. -/
theorem sqrtTech_inada_equilibrium {β θ : ℝ} (hb : 1 / 2 < (1 - θ) * β) (hβ1 : β < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ I : PosOutputInadaHyp inadaU sqrtTech ((1 - θ) * β) 24,
      (∀ k ∈ Icc (0 : ℝ) 24, 0 < plannerPolicy I.planner k ∧
        plannerPolicy I.planner k < sqrtTech k) ∧
      (∀ k ∈ Icc (0 : ℝ) 24, Tendsto (fun t => β ^ t *
        ((1 - θ) * deriv sqrtTech ((plannerPolicy I.planner)^[t] k)) *
        deriv inadaU (sqrtTech ((plannerPolicy I.planner)^[t] k) -
          plannerPolicy I.planner ((plannerPolicy I.planner)^[t] k)) *
          (plannerPolicy I.planner)^[t] k) atTop (𝓝 0)) ∧
      ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc (0 : ℝ) 24, |W x k| ≤ M) ∧
        SolvesBellman inadaU (fun k => sqrtTech k - (1 - θ) * k * deriv sqrtTech k)
          (fun k => (1 - θ) * deriv sqrtTech k) (plannerPolicy I.planner) W β (Icc 0 24) ∧
        ∀ k ∈ Icc (0 : ℝ) 24, ∀ y ∈ feasY (fun k => sqrtTech k - (1 - θ) * k * deriv sqrtTech k)
            (fun k => (1 - θ) * deriv sqrtTech k) k k,
          (inadaU (sqrtTech k + (1 - θ) * (k - k) * deriv sqrtTech k - y) +
            β * W y (plannerPolicy I.planner k) = W k k ↔ y = plannerPolicy I.planner k) := by
  have hb1 : (1 - θ) * β < 1 := by nlinarith
  have I := sqrtTech_posOutputInadaHyp hb hb1
  obtain ⟨hint, -, -, -, -, -, -, htvc, W, M, hWb, hsol, -, hall, -⟩ :=
    I.indirect_equilibrium (B₀ := 1) hβ1 hθ0 hθ1 (fun c _ => abs_inadaU_le c) sqrtTech_concaveOn
      (fun k hk => sqrtTech_deriv_facts.1 k hk.1) (fun k hk => sqrtTech_deriv_facts.2 k hk.1)
  exact ⟨I, hint, htvc, W, M, hWb, hsol, fun k hk => (hall k hk).2⟩

/-- **Exercise 18.1 on all of `K` in the economy `U(c) = 1 − e^{−c}`, `f(k) = 4 + 4√(1 + k)`**
(`U′(0) = 1` finite, `f(0) = 8 > 0`), for `β ∈ (1/2, 1)`: as `sqrtTech_inada_ex_18_1`. -/
theorem sqrtTech_finite_ex_18_1 {β : ℝ} (hβ0 : 1 / 2 < β) (hβ1 : β < 1) :
    ∃ I : FiniteMarginalHyp expU sqrtTech β 24,
      (∀ k ∈ Icc (0 : ℝ) 24, 0 < plannerPolicy I.planner k ∧
        plannerPolicy I.planner k < sqrtTech k) ∧
      (∀ k ∈ Icc (0 : ℝ) 24, Tendsto (fun t => β ^ t *
        deriv expU (sqrtTech ((plannerPolicy I.planner)^[t] k) -
          plannerPolicy I.planner ((plannerPolicy I.planner)^[t] k)) *
          deriv sqrtTech ((plannerPolicy I.planner)^[t] k) * (plannerPolicy I.planner)^[t] k)
            atTop (𝓝 0)) ∧
      ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc (0 : ℝ) 24, |V x k| ≤ M) ∧
        SolvesBellman expU (fun k => sqrtTech k - k * deriv sqrtTech k) (deriv sqrtTech)
          (plannerPolicy I.planner) V β (Icc 0 24) ∧
        ∀ k ∈ Icc (0 : ℝ) 24, V k k = plannerValue I.planner k ∧
          ∀ y ∈ feasY (fun k => sqrtTech k - k * deriv sqrtTech k) (deriv sqrtTech) k k,
            (expU (sqrtTech k + (k - k) * deriv sqrtTech k - y) +
              β * V y (plannerPolicy I.planner k) = V k k ↔ y = plannerPolicy I.planner k) := by
  have I := sqrtTech_finiteMarginalHyp hβ0 hβ1
  obtain ⟨hint, -, -, -, -, -, htvc, V, M, hVb, hsol, -, hall, -⟩ := I.ex_18_1 (B₀ := 1)
    (fun _ hc => abs_expU_le hc) sqrtTech_concaveOn (fun k hk => sqrtTech_deriv_facts.1 k hk.1)
    (fun k hk => sqrtTech_deriv_facts.2 k hk.1)
  exact ⟨I, hint, htvc, V, M, hVb, hsol, fun k hk => ⟨(hall k hk).1, (hall k hk).2.2⟩⟩

/-- **The indirect equilibrium on all of `K` in the economy `U(c) = 1 − e^{−c}`,
`f(k) = 4 + 4√(1 + k)`** (p. 546), for `β < 1`, `θ ∈ [0, 1)` with `(1 − θ)β > 1/2`: as
`sqrtTech_inada_equilibrium`. -/
theorem sqrtTech_finite_equilibrium {β θ : ℝ} (hb : 1 / 2 < (1 - θ) * β) (hβ1 : β < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ I : FiniteMarginalHyp expU sqrtTech ((1 - θ) * β) 24,
      (∀ k ∈ Icc (0 : ℝ) 24, 0 < plannerPolicy I.planner k ∧
        plannerPolicy I.planner k < sqrtTech k) ∧
      (∀ k ∈ Icc (0 : ℝ) 24, Tendsto (fun t => β ^ t *
        ((1 - θ) * deriv sqrtTech ((plannerPolicy I.planner)^[t] k)) *
        deriv expU (sqrtTech ((plannerPolicy I.planner)^[t] k) -
          plannerPolicy I.planner ((plannerPolicy I.planner)^[t] k)) *
          (plannerPolicy I.planner)^[t] k) atTop (𝓝 0)) ∧
      ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc (0 : ℝ) 24, |W x k| ≤ M) ∧
        SolvesBellman expU (fun k => sqrtTech k - (1 - θ) * k * deriv sqrtTech k)
          (fun k => (1 - θ) * deriv sqrtTech k) (plannerPolicy I.planner) W β (Icc 0 24) ∧
        ∀ k ∈ Icc (0 : ℝ) 24, ∀ y ∈ feasY (fun k => sqrtTech k - (1 - θ) * k * deriv sqrtTech k)
            (fun k => (1 - θ) * deriv sqrtTech k) k k,
          (expU (sqrtTech k + (1 - θ) * (k - k) * deriv sqrtTech k - y) +
            β * W y (plannerPolicy I.planner k) = W k k ↔ y = plannerPolicy I.planner k) := by
  have hb1 : (1 - θ) * β < 1 := by nlinarith
  have I := sqrtTech_finiteMarginalHyp hb hb1
  obtain ⟨hint, -, -, -, -, -, -, htvc, W, M, hWb, hsol, -, hall, -⟩ :=
    I.indirect_equilibrium (B₀ := 1) hβ1 hθ0 hθ1 (fun _ hc => abs_expU_le hc) sqrtTech_concaveOn
      (fun k hk => sqrtTech_deriv_facts.1 k hk.1) (fun k hk => sqrtTech_deriv_facts.2 k hk.1)
  exact ⟨I, hint, htvc, W, M, hWb, hsol, fun k hk => (hall k hk).2⟩

/-- **The slope condition is needed when `U′(0+) = ∞`** (counterexample for
`PosOutputInadaHyp`). For `b ∈ (0, 1)`, `U(c) = 1 − e^{−√c}` and the constant technology
`f ≡ 1` on `K = [0, 1]` satisfy `PlannerHyp`, `U′(0+) = ∞`, `f(0) > 0` and monotonicity, but not
the slope condition at `0`; and the constructed policy is `g ≡ 0` on `K`, so it is not interior
anywhere. Hence `f(0) > 0` with `U′(0+) = ∞` alone does not give interiority. -/
theorem inada_const_counterexample {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ P : PlannerHyp inadaU (fun _ => 1) b 1,
      Tendsto (fun c => (inadaU c - inadaU 0) / c) (𝓝[>] 0) atTop ∧
      MonotoneOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 1) ∧
      (¬ ∃ m, 1 < b * m ∧ ∀ᶠ y in 𝓝[>] (0 : ℝ), (1 : ℝ) + m * y ≤ 1) ∧
      ∀ k ∈ Icc (0 : ℝ) 1, plannerPolicy P k = 0 := by
  let P : PlannerHyp inadaU (fun _ => 1) b 1 :=
    { b_nonneg := hb0.le
      b_lt_one := hb1
      kbar_nonneg := zero_le_one
      U_cont := continuous_inadaU.continuousOn
      U_mono := inadaU_monotoneOn
      U_strictConcave := inadaU_strictConcaveOn
      f_cont := continuousOn_const
      f_concave := concaveOn_const 1 (convex_Icc 0 1)
      f_nonneg := fun _ _ => zero_le_one
      f_le := fun _ _ => le_rfl }
  refine ⟨P, inadaU_inada, fun _ _ _ _ _ => le_rfl, ?_, fun k hk =>
    P.plannerPolicy_eq_zero_of_const (a := 1) (fun _ _ => rfl) hk⟩
  rintro ⟨m, hm, hev⟩
  have hm0 : 0 < m := by nlinarith
  obtain ⟨y, hy1, hy2⟩ := (hev.and self_mem_nhdsWithin).exists
  have := mul_pos hm0 (mem_Ioi.1 hy2)
  linarith

/-- **The slope condition is needed when `U′(0)` is finite** (counterexample for
`FiniteMarginalHyp`). For `b ∈ (0, 1)`, `U(c) = 1 − e^{−c}` (`U′(0) = 1`) and `f ≡ 1` on
`K = [0, 1]` satisfy every hypothesis of `FiniteMarginalHyp` except the slope condition at `0`
(the Lipschitz condition holds with `r = 1/2`, `φ = 0`), and the constructed policy is `g ≡ 0`. -/
theorem finite_const_counterexample {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ P : PlannerHyp expU (fun _ => 1) b 1,
      HasDerivWithinAt expU 1 (Ici 0) 0 ∧ MonotoneOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 1) ∧
      (∀ k ∈ Icc (1 / 2 : ℝ) 1, ∀ k' ∈ Icc (1 / 2 : ℝ) 1,
        |(fun _ : ℝ => (1 : ℝ)) k - (fun _ : ℝ => (1 : ℝ)) k'| ≤ 0 * |k - k'|) ∧
      (¬ ∃ m, 1 < b * m ∧ ∀ᶠ y in 𝓝[>] (0 : ℝ), (1 : ℝ) + m * y ≤ 1) ∧
      ∀ k ∈ Icc (0 : ℝ) 1, plannerPolicy P k = 0 := by
  let P : PlannerHyp expU (fun _ => 1) b 1 :=
    { b_nonneg := hb0.le
      b_lt_one := hb1
      kbar_nonneg := zero_le_one
      U_cont := continuous_expU.continuousOn
      U_mono := expU_monotoneOn
      U_strictConcave := expU_strictConcaveOn
      f_cont := continuousOn_const
      f_concave := concaveOn_const 1 (convex_Icc 0 1)
      f_nonneg := fun _ _ => zero_le_one
      f_le := fun _ _ => le_rfl }
  refine ⟨P, hasDerivWithinAt_expU_zero, fun _ _ _ _ _ => le_rfl, fun _ _ _ _ => by simp, ?_,
    fun k hk => P.plannerPolicy_eq_zero_of_const (a := 1) (fun _ _ => rfl) hk⟩
  rintro ⟨m, hm, hev⟩
  have hm0 : 0 < m := by nlinarith
  obtain ⟨y, hy1, hy2⟩ := (hev.and self_mem_nhdsWithin).exists
  have := mul_pos hm0 (mem_Ioi.1 hy2)
  linarith

/-- The technology `f(k) = min{1/100 + 10k, 1}`: `f(0) > 0`, very productive below `k = 99/1000`,
flat above. -/
noncomputable def cornerF (k : ℝ) : ℝ := min (1 / 100 + 10 * k) 1

/-- `f(k) = 1/100 + 10k` for `k ≤ 99/1000`. -/
theorem cornerF_of_le {k : ℝ} (hk : k ≤ 99 / 1000) : cornerF k = 1 / 100 + 10 * k :=
  min_eq_left (by linarith)

/-- `f` is nondecreasing. -/
theorem cornerF_monotoneOn {S : Set ℝ} : MonotoneOn cornerF S := fun _ _ _ _ h =>
  min_le_min (by linarith) le_rfl

/-- `U(c) = 1 − e^{−c}`, `f(k) = min{1/100 + 10k, 1}`, `b = 1/2` and `K = [0, 1]` satisfy
`PlannerHyp`. -/
theorem cornerF_plannerHyp : PlannerHyp expU cornerF (1 / 2) 1 where
  b_nonneg := by norm_num
  b_lt_one := by norm_num
  kbar_nonneg := zero_le_one
  U_cont := continuous_expU.continuousOn
  U_mono := expU_monotoneOn
  U_strictConcave := expU_strictConcaveOn
  f_cont := (by unfold cornerF; fun_prop : Continuous cornerF).continuousOn
  f_concave := by
    refine ⟨convex_Icc 0 1, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, cornerF]
    have h1 := mul_le_mul_of_nonneg_left (min_le_left (1 / 100 + 10 * x) 1) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_left (1 / 100 + 10 * y) 1) hb
    have h3 := mul_le_mul_of_nonneg_left (min_le_right (1 / 100 + 10 * x) 1) ha
    have h4 := mul_le_mul_of_nonneg_left (min_le_right (1 / 100 + 10 * y) 1) hb
    refine le_min ?_ ?_
    · have : b = 1 - a := by linarith
      subst this
      nlinarith
    · nlinarith
  f_nonneg := fun _ hk => le_min (by linarith [hk.1]) zero_le_one
  f_le := fun _ _ => min_le_right _ _

/-- **Without a bound on the return to saving, a finite `U′(0)` lets the policy hit `g = f`**
(counterexample for `FiniteMarginalHyp`). The economy `U(c) = 1 − e^{−c}` (`U′(0) = 1`),
`f(k) = min{1/100 + 10k, 1}`, `b = 1/2` on `K = [0, 1]` satisfies `PlannerHyp`, `f(0) > 0`,
monotonicity and the slope condition at `0` (`b · 10 > 1`), but no `0 ≤ r < f(0)` and `φ` with
`b φ < 1` make `f` `φ`-Lipschitz on `[r, 1]`; and on `[0, 1/1000]` the constructed policy saves
all output, `g(k) = f(k)`, so it is not interior. (Saving `y` more raises `v` by at least
`10 e^{−1} y`, worth `5 e^{−1} y ≥ y` today, while consuming `y` raises utility by at most `y`.) -/
theorem corner_counterexample :
    ∃ P : PlannerHyp expU cornerF (1 / 2) 1,
      HasDerivWithinAt expU 1 (Ici 0) 0 ∧ 0 < cornerF 0 ∧ MonotoneOn cornerF (Icc 0 1) ∧
      (∃ m, 1 < 1 / 2 * m ∧ ∀ᶠ y in 𝓝[>] 0, cornerF 0 + m * y ≤ cornerF y) ∧
      (¬ ∃ r φ, 0 ≤ r ∧ r < cornerF 0 ∧ 0 ≤ φ ∧ 1 / 2 * φ < 1 ∧
        ∀ k ∈ Icc r 1, ∀ k' ∈ Icc r 1, |cornerF k - cornerF k'| ≤ φ * |k - k'|) ∧
      (∀ k ∈ Icc (0 : ℝ) (1 / 1000), plannerPolicy P k = cornerF k) ∧
      ¬ ∀ k ∈ Icc (0 : ℝ) 1, plannerPolicy P k < cornerF k := by
  set P := cornerF_plannerHyp with hP
  have h0 : cornerF 0 = 1 / 100 := by rw [cornerF_of_le (by norm_num)]; norm_num
  -- the marginal value of capital below `99/1000` is at least `10 e^{−1}`
  have hgain : ∀ y' y : ℝ, 0 ≤ y' → y' ≤ y → y ≤ 99 / 1000 →
      10 * Real.exp (-1) * (y - y') ≤ plannerValue P y - plannerValue P y' := by
    intro y' y hy' hyy hy
    have hy'K : y' ∈ Icc (0 : ℝ) 1 := ⟨hy', by linarith⟩
    have hyK : y ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    obtain ⟨hz, -, hv'⟩ := P.plannerPolicy_spec hy'K
    obtain ⟨hgy, hmy, hvy⟩ := P.plannerPolicy_spec hyK
    have hfyy : cornerF y' ≤ cornerF y :=
      cornerF_monotoneOn (S := univ) (mem_univ _) (mem_univ _) hyy
    have h1 := isMaxOn_iff.1 hmy (plannerPolicy P y') ⟨hz.1, hz.2.trans hfyy⟩
    change expU (cornerF y - plannerPolicy P y') + 1 / 2 * plannerValue P (plannerPolicy P y') ≤
      expU (cornerF y - plannerPolicy P y) + 1 / 2 * plannerValue P (plannerPolicy P y) at h1
    have h2 := expU_sub_ge (c := cornerF y - plannerPolicy P y')
      (c' := cornerF y' - plannerPolicy P y') (by linarith)
      (by linarith [hz.1, P.f_le y hyK])
    have hd : cornerF y - plannerPolicy P y' - (cornerF y' - plannerPolicy P y') =
        10 * (y - y') := by
      rw [cornerF_of_le hy, cornerF_of_le (hyy.trans hy)]; ring
    rw [hd] at h2
    linarith
  have hlast : ∀ k ∈ Icc (0 : ℝ) (1 / 1000), plannerPolicy P k = cornerF k := by
    intro k hk
    have hkK : k ∈ Icc (0 : ℝ) 1 := ⟨hk.1, by linarith [hk.2]⟩
    set Y := cornerF k with hYdef
    have hY : Y = 1 / 100 + 10 * k := cornerF_of_le (by linarith [hk.2])
    have hY1 : Y ≤ 99 / 1000 := by rw [hY]; linarith [hk.2]
    have hY0 : 0 ≤ Y := by rw [hY]; linarith [hk.1]
    have hmaxY : ∀ y' ∈ Icc 0 Y, expU (Y - y') + 1 / 2 * plannerValue P y' ≤
        expU (Y - Y) + 1 / 2 * plannerValue P Y := by
      intro y' hy'
      have h1 := expU_sub_le (c := Y - y') (c' := 0) le_rfl (by linarith [hy'.2])
      have h2 := hgain y' Y hy'.1 hy'.2 hY1
      have h3 := one_le_five_mul_exp_neg_one
      have h4 : 0 ≤ Y - y' := by linarith [hy'.2]
      rw [sub_self]
      nlinarith
    obtain ⟨hg, hmax, hv⟩ := P.plannerPolicy_spec hkK
    have h1 := hmaxY _ hg
    have h2 := isMaxOn_iff.1 hmax Y ⟨hY0, le_rfl⟩
    change expU (Y - Y) + 1 / 2 * plannerValue P Y ≤
      expU (Y - plannerPolicy P k) + 1 / 2 * plannerValue P (plannerPolicy P k) at h2
    exact ((P.plannerPolicy_unique hkK ⟨hY0, le_rfl⟩).1 (by linarith)).symm
  refine ⟨P, hasDerivWithinAt_expU_zero, by rw [h0]; norm_num, cornerF_monotoneOn,
    ⟨10, by norm_num, ?_⟩, ?_, hlast, fun h => ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 99 / 1000)] with y hy
    rw [h0, cornerF_of_le hy.2.le]
  · rintro ⟨r, φ, hr0, hr, hφ0, hφ, hL⟩
    rw [h0] at hr
    have := hL (1 / 50) ⟨by linarith, by norm_num⟩ (1 / 100) ⟨by linarith, by norm_num⟩
    rw [cornerF_of_le (by norm_num), cornerF_of_le (by norm_num)] at this
    norm_num at this
    linarith
  · have h1 := h 0 ⟨le_rfl, zero_le_one⟩
    rw [hlast 0 ⟨le_rfl, by norm_num⟩] at h1
    exact lt_irrefl _ h1

/-- **The economy `U(c) = 1 − e^{−√c}`, `f(k) = 1 + √k` on `K = [0, 4]` satisfies
`PosOutputInadaHyp`** for every `b ∈ (0, 1)`: `f(0) = 1 > 0`, and `f′(0+) = ∞` gives the slope
condition with `m = 2/b` (`f(y) − f(0) = √y ≥ m y` for `y ≤ 1/m²`). -/
theorem rootTech_posOutputInadaHyp {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    PosOutputInadaHyp inadaU (fun k => 1 + Real.sqrt k) b 4 where
  planner :=
    { b_nonneg := hb0.le
      b_lt_one := hb1
      kbar_nonneg := by norm_num
      U_cont := continuous_inadaU.continuousOn
      U_mono := inadaU_monotoneOn
      U_strictConcave := inadaU_strictConcaveOn
      f_cont := (continuous_const.add Real.continuous_sqrt).continuousOn
      f_concave := (concaveOn_const 1 (convex_Icc 0 4)).add
        (Real.strictConcaveOn_sqrt.concaveOn.subset Icc_subset_Ici_self (convex_Icc 0 4))
      f_nonneg := fun k _ => by have := Real.sqrt_nonneg k; linarith
      f_le := fun k hk => by
        have h2 : Real.sqrt k ≤ 2 := by
          rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by linarith [hk.2])
        linarith }
  b_pos := hb0
  U_inada := inadaU_inada
  U_diff := fun _ hc => differentiableAt_inadaU hc
  f_zero_pos := by simp
  f_mono := fun x _ y _ h => by
    have := Real.sqrt_le_sqrt h
    dsimp only
    linarith
  f_slope := by
    refine ⟨2 / b, by rw [mul_div_cancel₀ _ hb0.ne']; norm_num, ?_⟩
    have hδ : 0 < (b / 2) ^ 2 := by positivity
    filter_upwards [Ioo_mem_nhdsGT hδ] with y hy
    set s := Real.sqrt y with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg y
    have hsq : s ^ 2 = y := Real.sq_sqrt hy.1.le
    have hsb : s < b / 2 := by nlinarith [hy.2]
    have hm : 2 / b * s ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hb0]
      linarith
    simp only [Real.sqrt_zero, add_zero]
    rw [← hsq]
    nlinarith

/-- **Interiority on all of `K = [0, 4]` in the economy `U(c) = 1 − e^{−√c}`, `f(k) = 1 + √k`**
for every `b ∈ (0, 1)`: `0 < g(k) < f(k)`, including at `k = 0` (contrast
`InteriorHyp.not_interior_zero` for `f(k) = √k`). -/
theorem rootTech_interior {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ k ∈ Icc (0 : ℝ) 4, 0 < plannerPolicy (rootTech_posOutputInadaHyp hb0 hb1).planner k ∧
      plannerPolicy (rootTech_posOutputInadaHyp hb0 hb1).planner k < 1 + Real.sqrt k :=
  fun _ hk => (rootTech_posOutputInadaHyp hb0 hb1).policy_interior hk

end StokeyLucasPrescott.EquilibriaWithDistortions
