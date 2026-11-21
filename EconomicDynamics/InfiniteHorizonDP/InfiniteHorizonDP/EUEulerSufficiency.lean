/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.EUEuler

/-!
# §7.5: Theorem 7.5.2, sufficiency of the Euler and transversality conditions

Miao, §7.5, pp. 226–227, in the Euler class `eu_EulerModel` with `X ⊆ ℝⁿ₊`.

* `eu_euler_sufficient`: the proof of Theorem 7.5.2 under minimal hypotheses. Let `x*` be a
  feasible plan satisfying the Euler equation (7.34) and the transversality condition (7.35), with
  `u(·, z_t, ·)` concave on a set containing `(x*_t, x*_{t+1})` and `(x_t, x_{t+1})` and
  differentiable at `(x*_t, x*_{t+1})`, `u_x ≥ 0` along `x*`, and `x ≥ 0`. Then
  `S_T(x) ≤ S_T(x*) + w_T` with `w_T = −E βᵀ u_a(x*_T, z_T, x*_{T+1}) · x*_{T+1} → 0`.
* **Theorem 7.5.2** (`theorem_7_5_2`): the book's hypotheses (Assumptions 7.3.2–7.3.4, interior
  plan, `X ⊆ ℝⁿ₊` convex) imply those of `eu_euler_sufficient`; `theorem_7_5_2_limit`: the limit
  step in `[−∞, +∞]`; `theorem_7_5_2_eventually`: optimality in the sense of `IsOptimal`.

**Corrections.** (1) "By Assumption 7.3.2 and the Euler equation, we deduce that `u_a < 0`":
strict monotonicity gives only `u_x ≥ 0` (`eu_ux_nonneg`; `eu_strictMono_deriv_zero`), hence
`u_a = −β E_t u_x ≤ 0` almost surely, which is all the proof needs (with `x_{T+1} ≥ 0`). With
concavity, `u_x > 0` at interior points (`eu_ux_pos`), so the strict sign holds in the
deterministic case. (2) The displayed identity has two misprints: the sum of the Euler terms runs
to `T − 1`, not `T` (the date-`T` term is the boundary term written separately), and `u_x` carries
the factor `β`: `Σ_{t<T} βᵗ (u_a(t) + β u_x(t + 1)) · (x*_{t+1} − x_{t+1})`. (3) The proof uses the
derivative of `u` at `(x*_0, x*_1)`, so `x₀ ∈ int X` is needed (the hypothesis
`x*_{t+1} ∈ int Γ(x*_t, z_t)` covers only `t ≥ 1`); and `Γ ⊆ X`. (4) Integrability of the rewards
and of the products in the telescoping is assumed (`EulerInt`). (5) Only concavity, not the strict
part of Assumption 7.3.3, and only `β ≥ 0` are used; Assumption 6.4.3 is not used.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

namespace eu_EulerModel

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z] {Ω : Type*} {m0 : MeasurableSpace Ω}

variable (P : Measure Ω) (z : ℕ → Ω → Z) (M : eu_EulerModel n Z) (xs x : ℕ → Ω → (Fin n → ℝ)) in
/-- The integrability used in the proof of Theorem 7.5.2, for the candidate `xs` and a competing
plan `x`, at every date and coordinate. -/
structure EulerInt : Prop where
  r_s : ∀ t, Integrable (fun ω => M.u (xs t ω) (z t ω) (xs (t + 1) ω)) P
  r_c : ∀ t, Integrable (fun ω => M.u (x t ω) (z t ω) (x (t + 1) ω)) P
  uxΔ : ∀ t i, Integrable (fun ω => (xs t ω i - x t ω i) *
    M.ux (xs t ω) (z t ω) (xs (t + 1) ω) i) P
  uaΔ : ∀ t i, Integrable (fun ω => (xs (t + 1) ω i - x (t + 1) ω i) *
    M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i) P
  uxn : ∀ t i, Integrable (fun ω => M.ux (xs (t + 1) ω) (z (t + 1) ω) (xs (t + 2) ω) i) P
  uax : ∀ t i, Integrable (fun ω => M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i * xs (t + 1) ω i) P

variable {M : eu_EulerModel n Z} {P : Measure Ω} {ℱ : Filtration ℕ m0} {z : ℕ → Ω → Z}

/-- **The proof of Theorem 7.5.2** (Miao, pp. 226–227), under minimal hypotheses: concavity of
`u(·, z_t, ·)` on a set `C(z_t)` containing `(x*_t, x*_{t+1})` and `(x_t, x_{t+1})`,
differentiability at `(x*_t, x*_{t+1})`, (7.34), `u_x ≥ 0` along `x*`, `x ≥ 0` and (7.35). Then
`S_T(x) ≤ S_T(x*) + w_T` with `w_T → 0`. -/
theorem eu_euler_sufficient [IsProbabilityMeasure P] (hβ : 0 ≤ M.β) {x₀ : Fin n → ℝ}
    {xs x : ℕ → Ω → (Fin n → ℝ)} (hxs : M.IsPlan ℱ z x₀ xs) (hx : M.IsPlan ℱ z x₀ x)
    (C : Z → Set ((Fin n → ℝ) × (Fin n → ℝ))) (hcon : ∀ z', ConcaveOn ℝ (C z') (M.uu z'))
    (hmem : ∀ t ω, (xs t ω, xs (t + 1) ω) ∈ C (z t ω) ∧ (x t ω, x (t + 1) ω) ∈ C (z t ω))
    (hd : ∀ t ω, DifferentiableAt ℝ (M.uu (z t ω)) (xs t ω, xs (t + 1) ω))
    (heuler : M.IsEuler P ℱ z xs)
    (hux : ∀ t ω i, 0 ≤ M.ux (xs (t + 1) ω) (z (t + 1) ω) (xs (t + 2) ω) i)
    (hpos : ∀ t ω i, 0 ≤ x (t + 1) ω i) (hint : EulerInt P z M xs x) (htvc : M.TVC735 P z xs) :
    ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 0) ∧
      ∀ T, M.eu_partialJ P z x T ≤ M.eu_partialJ P z xs T + w T := by
  set A : ℕ → ℝ := fun t => ∑ i, ∫ ω, (xs t ω i - x t ω i) *
    M.ux (xs t ω) (z t ω) (xs (t + 1) ω) i ∂P with hAdef
  set B : ℕ → ℝ := fun t => ∑ i, ∫ ω, (xs (t + 1) ω i - x (t + 1) ω i) *
    M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i ∂P with hBdef
  -- the period inequality (supergradient)
  have hper : ∀ t, A t + B t ≤ (∫ ω, M.u (xs t ω) (z t ω) (xs (t + 1) ω) ∂P) -
      ∫ ω, M.u (x t ω) (z t ω) (x (t + 1) ω) ∂P := by
    intro t
    have hpath : ∀ ω, (∑ i, (xs t ω i - x t ω i) * M.ux (xs t ω) (z t ω) (xs (t + 1) ω) i) +
        (∑ i, (xs (t + 1) ω i - x (t + 1) ω i) * M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i) ≤
        M.u (xs t ω) (z t ω) (xs (t + 1) ω) - M.u (x t ω) (z t ω) (x (t + 1) ω) := by
      intro ω
      have h := eu_concave_le_fderiv (hcon (z t ω)) (hmem t ω).1 (hmem t ω).2 (hd t ω).hasFDerivAt
      have hdec := eu_clm_pair (fderiv ℝ (M.uu (z t ω)) (xs t ω, xs (t + 1) ω))
        (xs t ω - x t ω) (xs (t + 1) ω - x (t + 1) ω)
      have hneg : (x t ω, x (t + 1) ω) - (xs t ω, xs (t + 1) ω) =
          -(xs t ω - x t ω, xs (t + 1) ω - x (t + 1) ω) := by ext <;> simp
      rw [hneg, map_neg, hdec] at h
      simp only [uu, Pi.sub_apply] at h
      simp only [ux, ua]
      linarith
    have hi1 : Integrable (fun ω => ∑ i, (xs t ω i - x t ω i) *
        M.ux (xs t ω) (z t ω) (xs (t + 1) ω) i) P :=
      integrable_finsetSum _ fun i _ => hint.uxΔ t i
    have hi2 : Integrable (fun ω => ∑ i, (xs (t + 1) ω i - x (t + 1) ω i) *
        M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i) P :=
      integrable_finsetSum _ fun i _ => hint.uaΔ t i
    have hm : ∫ ω, ((∑ i, (xs t ω i - x t ω i) * M.ux (xs t ω) (z t ω) (xs (t + 1) ω) i) +
        (∑ i, (xs (t + 1) ω i - x (t + 1) ω i) * M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i)) ∂P ≤
        ∫ ω, (M.u (xs t ω) (z t ω) (xs (t + 1) ω) - M.u (x t ω) (z t ω) (x (t + 1) ω)) ∂P :=
      integral_mono (hi1.add hi2) ((hint.r_s t).sub (hint.r_c t)) hpath
    rw [integral_add hi1 hi2, integral_sub (hint.r_s t) (hint.r_c t),
      integral_finsetSum _ fun i _ => hint.uxΔ t i,
      integral_finsetSum _ fun i _ => hint.uaΔ t i] at hm
    exact hm
  -- the Euler equation: `B_t = −β A_{t+1}`
  have heul : ∀ t, B t = -(M.β * A (t + 1)) := by
    intro t
    simp only [hAdef, hBdef, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hΔ : StronglyMeasurable[ℱ t] fun ω => xs (t + 1) ω i - x (t + 1) ω i :=
      (((measurable_pi_apply i).comp (hxs.2.1 t)).sub
        ((measurable_pi_apply i).comp (hx.2.1 t))).stronglyMeasurable
    obtain ⟨_, heq⟩ := OCModel.oc_integral_mul_condExp hΔ (hint.uxΔ (t + 1) i) (hint.uxn t i)
    have hae : (fun ω => (xs (t + 1) ω i - x (t + 1) ω i) *
        M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i) =ᵐ[P] fun ω => -M.β *
          ((xs (t + 1) ω i - x (t + 1) ω i) * (P[fun ω' => M.ux (xs (t + 1) ω') (z (t + 1) ω')
            (xs (t + 2) ω') i | ℱ t]) ω) := by
      filter_upwards [heuler t i] with ω hω
      simp only [Pi.zero_apply] at hω
      have : M.ua (xs t ω) (z t ω) (xs (t + 1) ω) i = -(M.β * (P[fun ω' => M.ux (xs (t + 1) ω')
          (z (t + 1) ω') (xs (t + 2) ω') i | ℱ t]) ω) := by linarith
      rw [this]; ring
    rw [integral_congr_ae hae, integral_const_mul, ← heq]
    ring
  have hA0 : A 0 = 0 := by
    simp only [hAdef]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [hxs.1, hx.1]
  -- telescoping
  have htel : ∀ T, ∑ t ∈ Finset.range (T + 1), M.β ^ t * (A t + B t) = M.β ^ T * B T := by
    intro T
    have h1 : ∑ t ∈ Finset.range (T + 1), M.β ^ t * (A t + B t) =
        ∑ t ∈ Finset.range (T + 1), (M.β ^ t * A t - M.β ^ (t + 1) * A (t + 1)) :=
      Finset.sum_congr rfl fun t _ => by rw [heul t]; ring
    rw [h1, Finset.sum_range_sub' (fun t => M.β ^ t * A t) (T + 1), hA0, heul T]
    ring
  -- the sign: `B_T ≥ E u_a(T) · x*_{T+1}`
  have hsign : ∀ T, ∑ i, ∫ ω, M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i * xs (T + 1) ω i ∂P ≤ B T := by
    intro T
    simp only [hBdef]
    refine Finset.sum_le_sum fun i _ => ?_
    have hneg : ∀ᵐ ω ∂P, M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i ≤ 0 := by
      have hce := condExp_nonneg (m := ℱ T) (μ := P)
        (f := fun ω' => M.ux (xs (T + 1) ω') (z (T + 1) ω') (xs (T + 2) ω') i)
        (Eventually.of_forall fun ω => hux T ω i)
      filter_upwards [heuler T i, hce] with ω hω hc
      simp only [Pi.zero_apply] at hω hc
      nlinarith [mul_nonneg hβ hc]
    refine integral_mono_ae ((hint.uax T i)) (hint.uaΔ T i) ?_
    filter_upwards [hneg] with ω hω
    have := mul_nonpos_of_nonneg_of_nonpos (hpos T ω i) hω
    nlinarith
  refine ⟨fun T => -(M.β ^ T * ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω))
    (xs (T + 1) ω) ∂P), by simpa using htvc.neg, fun T => ?_⟩
  have hsum : (∑ t ∈ Finset.range (T + 1), M.β ^ t * (A t + B t)) ≤
      ∑ t ∈ Finset.range (T + 1), M.β ^ t * ((∫ ω, M.u (xs t ω) (z t ω) (xs (t + 1) ω) ∂P) -
        ∫ ω, M.u (x t ω) (z t ω) (x (t + 1) ω) ∂P) :=
    Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hper t) (pow_nonneg hβ t)
  rw [htel] at hsum
  have hdot : ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω)) (xs (T + 1) ω) ∂P =
      ∑ i, ∫ ω, M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i * xs (T + 1) ω i ∂P := by
    simp only [eu_dot]
    exact integral_finsetSum _ fun i _ => hint.uax T i
  have hB := mul_le_mul_of_nonneg_left (hsign T) (pow_nonneg hβ T)
  rw [← hdot] at hB
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum
  simp only [eu_partialJ]
  linarith

/-- **Theorem 7.5.2 (sufficiency of the Euler and transversality conditions)** (Miao, p. 226).
Let `X ⊆ ℝⁿ₊` be convex, `Γ ⊆ X`, and Assumptions 5.1.2 (`β ≥ 0` is used), 7.3.2, 7.3.3 and 7.3.4
hold. Let the feasible plan `x*` with `x*_{t+1} ∈ int Γ(x*_t, z_t)` and `x₀ ∈ int X` satisfy the
Euler equation (7.34) and the transversality condition (7.35). Then every feasible plan `x` with
the integrability `EulerInt` satisfies `S_T(x) ≤ S_T(x*) + w_T` with `w_T → 0`. -/
theorem theorem_7_5_2 [IsProbabilityMeasure P] (hXpos : ∀ y ∈ M.X, 0 ≤ y) (hXc : Convex ℝ M.X)
    (hΓX : ∀ y z', M.Γ y z' ⊆ M.X) (h512 : 0 < M.β ∧ M.β < 1) (h732 : M.eu_Assumption732)
    (h733 : M.eu_Assumption733) (h734 : M.eu_Assumption734) {x₀ : Fin n → ℝ}
    {xs x : ℕ → Ω → (Fin n → ℝ)} (hxs : M.IsPlan ℱ z x₀ xs) (hx0 : x₀ ∈ interior M.X)
    (hinter : ∀ t ω, xs (t + 1) ω ∈ interior (M.Γ (xs t ω) (z t ω)))
    (heuler : M.IsEuler P ℱ z xs) (htvc : M.TVC735 P z xs) (hx : M.IsPlan ℱ z x₀ x)
    (hint : EulerInt P z M xs x) :
    ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 0) ∧
      ∀ T, M.eu_partialJ P z x T ≤ M.eu_partialJ P z xs T + w T := by
  have hin : ∀ t ω, xs t ω ∈ interior M.X := by
    intro t ω
    cases t with
    | zero => rw [hxs.1 ω]; exact hx0
    | succ t => exact interior_mono (hΓX _ _) (hinter t ω)
  have hmemI : ∀ t ω, (xs t ω, xs (t + 1) ω) ∈ interior (M.X ×ˢ M.X) := fun t ω => by
    rw [interior_prod_eq]; exact ⟨hin t ω, hin (t + 1) ω⟩
  have hd : ∀ t ω, DifferentiableAt ℝ (M.uu (z t ω)) (xs t ω, xs (t + 1) ω) := fun t ω =>
    ((h734 (z t ω)).differentiableOn one_ne_zero).differentiableAt
      (isOpen_interior.mem_nhds (hmemI t ω))
  refine eu_euler_sufficient h512.1.le hxs hx (fun _ => M.X ×ˢ M.X)
    (fun z' => concaveOn_of_733 h733 hXc z')
    (fun t ω => ⟨interior_subset (hmemI t ω), (hx.2.2 t ω).1, hΓX _ _ (hx.2.2 t ω).2⟩)
    hd heuler (fun t ω i => ?_) (fun t ω i => hXpos _ (hx.2.2 (t + 1) ω).1 i) hint htvc
  exact eu_ux_nonneg (h732 _ _).monotoneOn (hin (t + 1) ω) (hd (t + 1) ω) i

/-- **Theorem 7.5.2, the limit step** (Miao, p. 227): under the hypotheses of `theorem_7_5_2`,
if the partial sums of `x*` and of `x` converge in `[−∞, +∞]`, then `J(x) ≤ J(x*)`. -/
theorem theorem_7_5_2_limit [IsProbabilityMeasure P] (hXpos : ∀ y ∈ M.X, 0 ≤ y)
    (hXc : Convex ℝ M.X) (hΓX : ∀ y z', M.Γ y z' ⊆ M.X) (h512 : 0 < M.β ∧ M.β < 1)
    (h732 : M.eu_Assumption732) (h733 : M.eu_Assumption733) (h734 : M.eu_Assumption734)
    {x₀ : Fin n → ℝ} {xs x : ℕ → Ω → (Fin n → ℝ)} (hxs : M.IsPlan ℱ z x₀ xs)
    (hx0 : x₀ ∈ interior M.X) (hinter : ∀ t ω, xs (t + 1) ω ∈ interior (M.Γ (xs t ω) (z t ω)))
    (heuler : M.IsEuler P ℱ z xs) (htvc : M.TVC735 P z xs) (hx : M.IsPlan ℱ z x₀ x)
    (hint : EulerInt P z M xs x) {J J' : EReal}
    (hJ : Tendsto (fun T => (M.eu_partialJ P z xs T : EReal)) atTop (𝓝 J))
    (hJ' : Tendsto (fun T => (M.eu_partialJ P z x T : EReal)) atTop (𝓝 J')) : J' ≤ J := by
  obtain ⟨w, hw, hle⟩ := theorem_7_5_2 hXpos hXc hΓX h512 h732 h733 h734 hxs hx0 hinter heuler
    htvc hx hint
  exact eu_le_of_le_add_tendsto_zero hJ hJ' hw hle

/-- **Theorem 7.5.2, optimality** (Miao, p. 227): under the hypotheses of `theorem_7_5_2` for
every competing plan, if the rewards of `x*` are integrable and `S_T(x*) → J*`, then `x*` is
optimal in the sense of `IsOptimal` among the plans with the integrability `EulerInt`. -/
theorem theorem_7_5_2_eventually [IsProbabilityMeasure P] (hXpos : ∀ y ∈ M.X, 0 ≤ y)
    (hXc : Convex ℝ M.X) (hΓX : ∀ y z', M.Γ y z' ⊆ M.X) (h512 : 0 < M.β ∧ M.β < 1)
    (h732 : M.eu_Assumption732) (h733 : M.eu_Assumption733) (h734 : M.eu_Assumption734)
    {x₀ : Fin n → ℝ} {xs : ℕ → Ω → (Fin n → ℝ)} (hxs : M.IsPlan ℱ z x₀ xs)
    (hx0 : x₀ ∈ interior M.X) (hinter : ∀ t ω, xs (t + 1) ω ∈ interior (M.Γ (xs t ω) (z t ω)))
    (heuler : M.IsEuler P ℱ z xs) (htvc : M.TVC735 P z xs) {J : ℝ}
    (hJ : Tendsto (M.eu_partialJ P z xs) atTop (𝓝 J)) {x : ℕ → Ω → (Fin n → ℝ)}
    (hx : M.IsPlan ℱ z x₀ x) (hint : EulerInt P z M xs x) :
    ∀ ε > 0, ∀ᶠ T in atTop, M.eu_partialJ P z x T ≤ J + ε := by
  obtain ⟨w, hw, hle⟩ := theorem_7_5_2 hXpos hXc hΓX h512 h732 h733 h734 hxs hx0 hinter heuler
    htvc hx hint
  exact eu_limsup_le hJ hw hle

end eu_EulerModel

end Miao.InfiniteHorizonDP
