/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDP.Theorem92

/-!
# Lemma 9.3: the value of a plan and of its continuations

SLP §9.1, pp. 248–250, Exercises 9.1 and 9.5a.

* The finite recursion `uₙ₊₁(π, s₀) = F(x₀, π₀, z₀) + β ∫ uₙ[C(π, z₁), s₁] Q(z₀, dz₁)`
  (`uN_succ`), from splitting `μᵗ⁺¹` at its first date (Exercise 8.8).
* **Exercise 9.1**: `z₁ ↦ uₙ[C(π, z₁), s₁(z₁)]` is measurable, and so is
  `z₁ ↦ u[C(π, z₁), s₁(z₁)]` when the limits exist (`ex_9_1`).
* **Lemma 9.3** (and **Exercise 9.5a**) `u(π, s₀) = F(x₀, π₀, z₀) + β ∫ u[C(π, z₁), s₁] Q(z₀, dz₁)`:
  under Assumption 9.3 — returns bounded by `L_t` with `Σ βᵗ L_t < ∞` — by dominated convergence
  (`lemma_9_3`); and for nonnegative returns, with values in `[0, +∞]`, by monotone convergence
  (`lemma_9_3_nonneg`), which gives the case `F ≤ 0` by symmetry.
* The real series `uR` with its bounds (`tendsto_uN`, `abs_uR_le`) and the continuation bounds
  `L_{t+1}` (`bounds_cont`), used by Theorem 9.4.
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (M : Model X Y Z) [IsMarkovKernel M.Q]

/-- The expected return of the continuation at date `t`, as a function of the first shock. -/
theorem integral_ret_succ (s₀ : X × Z) (π : Plan Y Z) (t : ℕ)
    (hI : Integrable (ret M s₀ π (t + 1)) (hist M.Q (t + 1) s₀.2)) :
    ∫ h, ret M s₀ π (t + 1) h ∂hist M.Q (t + 1) s₀.2 =
      ∫ z₁, ∫ h, ret M (start₁ M s₀ π z₁) (cont π z₁) t h ∂hist M.Q t z₁ ∂M.Q s₀.2 := by
  rw [ex_8_8c_first M.Q t s₀.2 hI]
  simp_rw [ret_cons]

theorem integrable_ret_cont (s₀ : X × Z) (π : Plan Y Z) (t : ℕ)
    (hI : Integrable (ret M s₀ π (t + 1)) (hist M.Q (t + 1) s₀.2)) :
    Integrable (fun z₁ => ∫ h, ret M (start₁ M s₀ π z₁) (cont π z₁) t h ∂hist M.Q t z₁)
      (M.Q s₀.2) := by
  have := integrable_first M.Q t s₀.2 hI
  simp_rw [ret_cons] at this
  exact this

/-- **The finite recursion** behind Lemma 9.3:
`uₙ₊₁(π, s₀) = F(x₀, π₀, z₀) + β ∫ uₙ[C(π, z₁), s₁] Q(z₀, dz₁)`. -/
theorem uN_succ (s₀ : X × Z) (π : Plan Y Z)
    (hI : ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2)) (n : ℕ) :
    uN M s₀ π (n + 1) = ret M s₀ π 0 Fin.elim0 +
      M.β * ∫ z₁, uN M (start₁ M s₀ π z₁) (cont π z₁) n ∂M.Q s₀.2 := by
  have hs : ∀ z₁, (start₁ M s₀ π z₁).2 = z₁ := fun _ => rfl
  simp only [uN, hs]
  rw [integral_finsetSum _ fun t _ => (integrable_ret_cont M s₀ π t (hI (t + 1))).const_mul _,
    Finset.sum_range_succ', Finset.mul_sum, integral_hist_zero]
  simp only [pow_zero, one_mul, add_comm (ret M s₀ π 0 Fin.elim0)]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, integral_ret_succ M s₀ π t (hI (t + 1)), pow_succ]
  ring

omit [IsMarkovKernel M.Q] in
/-- Joint measurability of the continuation returns in `(z₁, zᵗ)`. -/
theorem measurable_ret_cont (hφ : Measurable M.φ) (hF : Measurable M.F) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (t : ℕ) :
    Measurable fun p : Z × (Fin t → Z) => ret M (start₁ M s₀ π p.1) (cont π p.1) t p.2 := by
  have := (measurable_ret M hφ hF s₀ hπ (t + 1)).comp (measurable_cons t)
  simp_rw [Function.comp_def, ret_cons] at this
  exact this

/-- **Exercise 9.1.** `z₁ ↦ uₙ[C(π, z₁), (φ(x₀, π₀, z₁), z₁)]` is measurable, and so is its
limit `z₁ ↦ u[C(π, z₁), (φ(x₀, π₀, z₁), z₁)]` when the limits exist. -/
theorem ex_9_1 (hφ : Measurable M.φ) (hF : Measurable M.F) (s₀ : X × Z) {π : Plan Y Z}
    (hπ : ∀ t, Measurable (π t)) :
    (∀ n, Measurable fun z₁ => uN M (start₁ M s₀ π z₁) (cont π z₁) n) ∧
      ((∀ z₁, ∃ L, Tendsto (fun n => (uN M (start₁ M s₀ π z₁) (cont π z₁) n : EReal)) atTop
        (𝓝 L)) → Measurable fun z₁ => planValue M (start₁ M s₀ π z₁) (cont π z₁)) := by
  have hn : ∀ n, Measurable fun z₁ => uN M (start₁ M s₀ π z₁) (cont π z₁) n := by
    intro n
    refine Finset.measurable_sum _ fun t _ => measurable_const.mul ?_
    have := ex_8_8a M.Q t
    exact ((measurable_ret_cont M hφ hF s₀ hπ t).stronglyMeasurable.integral_kernel_prod_right'
      (κ := hist M.Q t)).measurable
  refine ⟨hn, fun hconv => ?_⟩
  have heq : (fun z₁ => planValue M (start₁ M s₀ π z₁) (cont π z₁)) =
      fun z₁ => liminf (fun n => (uN M (start₁ M s₀ π z₁) (cont π z₁) n : EReal)) atTop := by
    funext z₁
    obtain ⟨L, hL⟩ := hconv z₁
    rw [planValue_eq M hL, hL.liminf_eq]
  rw [heq]
  exact Measurable.liminf fun n => measurable_coe_real_ereal.comp (hn n)

/-- The value of a plan as the real series `Σ βᵗ ∫ F(x_t, π_t, z_t) dμᵗ` (under Assumption 9.3
the series converges absolutely). -/
noncomputable def uR (s₀ : X × Z) (π : Plan Y Z) : ℝ :=
  ∑' t, M.β ^ t * ∫ h, ret M s₀ π t h ∂hist M.Q t s₀.2

omit [IsMarkovKernel M.Q] in
/-- Bounds `L_t` on the returns are nonnegative. -/
theorem bound_nonneg (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (t : ℕ) : 0 ≤ K t :=
  (abs_nonneg _).trans (hK t fun _ => s.2)

/-- Bounded returns are integrable. -/
theorem integrable_ret_of_bound (hφ : Measurable M.φ) (hF : Measurable M.F) (s : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (t : ℕ) : Integrable (ret M s π t) (hist M.Q t s.2) := by
  have := ex_8_8a M.Q t
  refine (integrable_const (K t)).mono' (measurable_ret M hφ hF s hπ t).aestronglyMeasurable
    (Eventually.of_forall fun h => ?_)
  rw [Real.norm_eq_abs]
  exact hK t h

/-- Under Assumption 9.3, `|βᵗ ∫ F dμᵗ| ≤ βᵗ L_t`. -/
theorem abs_term_le (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (t : ℕ) :
    |M.β ^ t * ∫ h, ret M s π t h ∂hist M.Q t s.2| ≤ M.β ^ t * K t := by
  have := ex_8_8a M.Q t
  rw [abs_mul, abs_of_nonneg (pow_nonneg hβ t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ t)
  have := norm_integral_le_of_norm_le_const (μ := hist M.Q t s.2) (C := K t)
    (f := ret M s π t) (Eventually.of_forall fun h => by rw [Real.norm_eq_abs]; exact hK t h)
  simpa [Real.norm_eq_abs, measureReal_def] using this

theorem summable_terms (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (hK' : Summable fun t => M.β ^ t * K t) :
    Summable fun t => M.β ^ t * ∫ h, ret M s π t h ∂hist M.Q t s.2 :=
  Summable.of_norm_bounded hK' fun t => by
    rw [Real.norm_eq_abs]; exact abs_term_le M hβ s π hK t

/-- Under Assumption 9.3, `uₙ(π, s) → Σ βᵗ ∫ F dμᵗ`. -/
theorem tendsto_uN (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (hK' : Summable fun t => M.β ^ t * K t) :
    Tendsto (fun n => uN M s π n) atTop (𝓝 (uR M s π)) :=
  (summable_terms M hβ s π hK hK').hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem planValue_eq_uR (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (hK' : Summable fun t => M.β ^ t * K t) :
    planValue M s π = (uR M s π : EReal) :=
  planValue_eq M ((continuous_coe_real_ereal.tendsto _).comp (tendsto_uN M hβ s π hK hK'))

theorem abs_uN_le (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (hK' : Summable fun t => M.β ^ t * K t) (n : ℕ) :
    |uN M s π n| ≤ ∑' t, M.β ^ t * K t := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun t _ => abs_term_le M hβ s π hK t).trans ?_
  exact hK'.sum_le_tsum _ fun t _ => mul_nonneg (pow_nonneg hβ t) (bound_nonneg M s π hK t)

theorem abs_uR_le (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (hK' : Summable fun t => M.β ^ t * K t) :
    |uR M s π| ≤ ∑' t, M.β ^ t * K t :=
  le_of_tendsto' ((continuous_abs.tendsto _).comp (tendsto_uN M hβ s π hK hK'))
    (abs_uN_le M hβ s π hK hK')

omit [IsMarkovKernel M.Q] in
/-- The continuations of a plan satisfying Assumption 9.3 with bounds `L_t` satisfy it with the
shifted bounds `L_{t+1}`. -/
theorem bounds_cont (hβ : 0 ≤ M.β) (s₀ : X × Z) (π : Plan Y Z) {L : ℕ → ℝ}
    (hL : ∀ t h, |ret M s₀ π t h| ≤ L t) (hsum : Summable fun t => M.β ^ t * L t) :
    (∀ z₁ t h, |ret M (start₁ M s₀ π z₁) (cont π z₁) t h| ≤ L (t + 1)) ∧
      Summable fun t => M.β ^ t * L (t + 1) := by
  refine ⟨fun z₁ t h => by rw [← ret_cons]; exact hL (t + 1) _, ?_⟩
  by_cases hβ0 : M.β = 0
  · refine summable_of_ne_finset_zero (s := {0}) fun t ht => ?_
    have : t ≠ 0 := by simpa using ht
    simp [hβ0, this]
  · have := (summable_nat_add_iff 1).2 hsum
    refine (this.mul_left (M.β)⁻¹).congr fun t => ?_
    rw [pow_succ]
    field_simp

/-- `z₁ ↦ Σ βᵗ ∫ F dμᵗ` along the continuations is measurable (Exercise 9.1). -/
theorem measurable_uR_cont (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) {L : ℕ → ℝ}
    (hL : ∀ t h, |ret M s₀ π t h| ≤ L t) (hsum : Summable fun t => M.β ^ t * L t) :
    Measurable fun z₁ => uR M (start₁ M s₀ π z₁) (cont π z₁) := by
  obtain ⟨hLc, hsumc⟩ := bounds_cont M hβ s₀ π hL hsum
  exact measurable_of_tendsto_metrizable (ex_9_1 M hφ hF s₀ hπ).1
    (tendsto_pi_nhds.2 fun z₁ => tendsto_uN M hβ _ _ (hLc z₁) hsumc)

/-- **Lemma 9.3** (and **Exercise 9.5a**) under Assumption 9.3: if the returns of `π` are bounded,
`|F(x_t, π_t, z_t)| ≤ L_t`, with `Σ βᵗ L_t < ∞`, then `u(π, s₀)` is the real number
`Σ βᵗ ∫ F dμᵗ`, and `u(π, s₀) = F(x₀, π₀, z₀) + β ∫ u[C(π, z₁), s₁] Q(z₀, dz₁)`. The book's
proof: pass to the limit in the finite recursion under the integral, by dominated convergence. -/
theorem lemma_9_3 (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) {L : ℕ → ℝ}
    (hL : ∀ t h, |ret M s₀ π t h| ≤ L t) (hsum : Summable fun t => M.β ^ t * L t) :
    planValue M s₀ π = (uR M s₀ π : EReal) ∧
      uR M s₀ π = ret M s₀ π 0 Fin.elim0 +
        M.β * ∫ z₁, uR M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 := by
  refine ⟨planValue_eq_uR M hβ s₀ π hL hsum, ?_⟩
  obtain ⟨hLc, hsumc⟩ := bounds_cont M hβ s₀ π hL hsum
  have hmeas := (ex_9_1 M hφ hF s₀ hπ).1
  have hDCT : Tendsto (fun n => ∫ z₁, uN M (start₁ M s₀ π z₁) (cont π z₁) n ∂M.Q s₀.2) atTop
      (𝓝 (∫ z₁, uR M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∑' t, M.β ^ t * L (t + 1))
      (fun n => (hmeas n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun z₁ => by
        rw [Real.norm_eq_abs]; exact abs_uN_le M hβ _ _ (hLc z₁) hsumc n)
      (Eventually.of_forall fun z₁ => tendsto_uN M hβ _ _ (hLc z₁) hsumc)
  have hrec : Tendsto (fun n => uN M s₀ π (n + 1)) atTop (𝓝 (ret M s₀ π 0 Fin.elim0 +
      M.β * ∫ z₁, uR M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2)) := by
    simp_rw [uN_succ M s₀ π (integrable_ret_of_bound M hφ hF s₀ hπ hL)]
    exact tendsto_const_nhds.add (hDCT.const_mul _)
  exact tendsto_nhds_unique ((tendsto_uN M hβ s₀ π hL hsum).comp (tendsto_add_atTop_nat 1)) hrec

/-- The total expected discounted return of a plan with nonnegative returns, in `[0, +∞]`. -/
noncomputable def planValuePos (s₀ : X × Z) (π : Plan Y Z) : ℝ≥0∞ :=
  ∑' t, ENNReal.ofReal (M.β ^ t) * ∫⁻ h, ENNReal.ofReal (ret M s₀ π t h) ∂hist M.Q t s₀.2

/-- **Lemma 9.3 for `F ≥ 0`** (the book's monotone convergence case): with values in `[0, +∞]`,
`u(π, s₀) = F(x₀, π₀, z₀) + β ∫ u[C(π, z₁), s₁] Q(z₀, dz₁)`. No integrability is needed. -/
theorem lemma_9_3_nonneg (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) :
    planValuePos M s₀ π = ENNReal.ofReal (ret M s₀ π 0 Fin.elim0) +
      ENNReal.ofReal M.β * ∫⁻ z₁, planValuePos M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 := by
  have hinner : ∀ t, Measurable fun z₁ =>
      ∫⁻ h, ENNReal.ofReal (ret M (start₁ M s₀ π z₁) (cont π z₁) t h) ∂hist M.Q t z₁ := by
    intro t
    have := ex_8_8a M.Q t
    exact (measurable_ret_cont M hφ hF s₀ hπ t).ennreal_ofReal.lintegral_kernel_prod_right'
      (κ := hist M.Q t)
  have hsplit : ∀ t, ∫⁻ h, ENNReal.ofReal (ret M s₀ π (t + 1) h) ∂hist M.Q (t + 1) s₀.2 =
      ∫⁻ z₁, ∫⁻ h, ENNReal.ofReal (ret M (start₁ M s₀ π z₁) (cont π z₁) t h) ∂hist M.Q t z₁
        ∂M.Q s₀.2 := fun t => by
    rw [hist_succ_lintegral M.Q t s₀.2 (measurable_ret M hφ hF s₀ hπ (t + 1)).ennreal_ofReal]
    simp_rw [ret_cons]
  rw [planValuePos, tsum_eq_zero_add' ENNReal.summable, hist_zero_lintegral]
  simp only [pow_zero, ENNReal.ofReal_one, one_mul, hsplit]
  congr 1
  have hs : ∀ z₁, (start₁ M s₀ π z₁).2 = z₁ := fun _ => rfl
  simp only [planValuePos, hs]
  rw [lintegral_tsum fun t => ((hinner t).const_mul _).aemeasurable, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun t => ?_
  rw [lintegral_const_mul _ (hinner t), ← mul_assoc, ← ENNReal.ofReal_mul hβ, pow_succ,
    mul_comm (M.β ^ t)]

/-! ### Absolutely summable plans -/

/-- The model with returns `|F|`. -/
abbrev Model.absF (M : Model X Y Z) : Model X Y Z := { M with F := fun p => |M.F p| }

omit [IsMarkovKernel M.Q] in
theorem xState_absF (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) :
    xState M.absF s₀ π t = xState M s₀ π t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext h
    simp only [xState, ih]

omit [IsMarkovKernel M.Q] in
theorem ret_absF (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) :
    ret M.absF s₀ π t = fun h => |ret M s₀ π t h| := by
  funext h
  simp only [ret, state, xState_absF]

/-- `Σ βᵗ ∫ |F(x_t, π_t, z_t)| dμᵗ ∈ [0, +∞]`. Plans for which it is finite generalize
Assumption 9.3. -/
noncomputable def planAbs (s₀ : X × Z) (π : Plan Y Z) : ℝ≥0∞ := planValuePos M.absF s₀ π

omit [IsMarkovKernel M.Q] in
theorem planAbs_eq (s₀ : X × Z) (π : Plan Y Z) : planAbs M s₀ π =
    ∑' t, ENNReal.ofReal (M.β ^ t) * ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2 := by
  simp only [planAbs, planValuePos, ret_absF]

omit [IsMarkovKernel M.Q] in
theorem measurable_cont_plan {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (z₁ : Z) :
    ∀ t, Measurable (cont π z₁ t) := fun t =>
  (hπ (t + 1)).comp ((measurable_cons t).comp (measurable_const.prodMk measurable_id))

/-- The recursion for `Σ βᵗ ∫ |F| dμᵗ` (Lemma 9.3 for `|F|`). -/
theorem planAbs_rec (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) :
    planAbs M s₀ π = ENNReal.ofReal |ret M s₀ π 0 Fin.elim0| +
      ENNReal.ofReal M.β * ∫⁻ z₁, planAbs M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 :=
  lemma_9_3_nonneg M.absF hφ (continuous_abs.measurable.comp hF) hβ s₀ hπ

theorem measurable_planAbs_cont (hφ : Measurable M.φ) (hF : Measurable M.F) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) :
    Measurable fun z₁ => planAbs M (start₁ M s₀ π z₁) (cont π z₁) := by
  refine Measurable.tsum fun t => measurable_const.mul ?_
  have := ex_8_8a M.Q t
  exact (measurable_ret_cont M.absF hφ (continuous_abs.measurable.comp hF) s₀ hπ t
    ).ennreal_ofReal.lintegral_kernel_prod_right' (κ := hist M.Q t)

omit [IsMarkovKernel M.Q] in
theorem term_le_planAbs (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) :
    ENNReal.ofReal (M.β ^ t) * ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2 ≤
      planAbs M s₀ π := by
  rw [planAbs_eq]
  exact ENNReal.le_tsum (f := fun t => ENNReal.ofReal (M.β ^ t) *
    ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2) t

/-- With `Σ βᵗ ∫ |F| dμᵗ < ∞` and `β > 0`, every return is integrable. -/
theorem integrable_ret_of_planAbs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤)
    (t : ℕ) : Integrable (ret M s₀ π t) (hist M.Q t s₀.2) := by
  have := ex_8_8a M.Q t
  have hm := measurable_ret M hφ hF s₀ hπ t
  have hlt := (term_le_planAbs M s₀ π t).trans_lt hfin.lt_top
  have hne : ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2 ≠ ⊤ := by
    rcases ENNReal.mul_lt_top_iff.1 hlt with h | h | h
    · exact h.2.ne
    · exact absurd h (ENNReal.ofReal_pos.2 (pow_pos hβ t)).ne'
    · rw [h]; exact ENNReal.zero_ne_top
  have hI : Integrable (fun h => |ret M s₀ π t h|) (hist M.Q t s₀.2) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.abs.aestronglyMeasurable
      (Eventually.of_forall fun h => abs_nonneg _)).1 hne
  refine (integrable_norm_iff hm.aestronglyMeasurable).1 ?_
  simpa only [Real.norm_eq_abs] using hI

theorem abs_term_le_planAbs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (t : ℕ) :
    |M.β ^ t * ∫ h, ret M s₀ π t h ∂hist M.Q t s₀.2| ≤
      (ENNReal.ofReal (M.β ^ t) *
        ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2).toReal := by
  have := ex_8_8a M.Q t
  have hm := measurable_ret M hφ hF s₀ hπ t
  rw [abs_mul, abs_of_nonneg (pow_nonneg hβ t), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hβ t), ← integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun h => abs_nonneg _) hm.abs.aestronglyMeasurable]
  exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (pow_nonneg hβ t)

/-- With `Σ βᵗ ∫ |F| dμᵗ < ∞`, the series `Σ βᵗ ∫ F dμᵗ` converges absolutely. -/
theorem summable_of_planAbs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤) :
    Summable fun t => M.β ^ t * ∫ h, ret M s₀ π t h ∂hist M.Q t s₀.2 := by
  rw [planAbs_eq] at hfin
  exact Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun t => by
    rw [Real.norm_eq_abs]; exact abs_term_le_planAbs M hφ hF hβ s₀ hπ t

theorem tendsto_uN_abs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤) :
    Tendsto (fun n => uN M s₀ π n) atTop (𝓝 (uR M s₀ π)) :=
  (summable_of_planAbs M hφ hF hβ s₀ hπ hfin).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)

theorem planValue_eq_uR_abs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤) :
    planValue M s₀ π = (uR M s₀ π : EReal) :=
  planValue_eq M ((continuous_coe_real_ereal.tendsto _).comp
    (tendsto_uN_abs M hφ hF hβ s₀ hπ hfin))

theorem abs_uN_le_planAbs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤)
    (n : ℕ) : |uN M s₀ π n| ≤ (planAbs M s₀ π).toReal := by
  have hfin' := hfin
  rw [planAbs_eq] at hfin' ⊢
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun t _ => abs_term_le_planAbs M hφ hF hβ s₀ hπ t).trans ?_
  rw [← ENNReal.toReal_sum fun t _ => ne_top_of_le_ne_top hfin' (ENNReal.le_tsum t)]
  exact ENNReal.toReal_mono hfin' (ENNReal.sum_le_tsum _)

/-- With `β > 0`, the continuations of an absolutely summable plan are absolutely summable for
`Q(z₀, ·)`-almost every `z₁`. -/
theorem ae_planAbs_cont (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤) :
    ∫⁻ z₁, planAbs M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 ≠ ⊤ ∧
      ∀ᵐ z₁ ∂M.Q s₀.2, planAbs M (start₁ M s₀ π z₁) (cont π z₁) ≠ ⊤ := by
  have hrec := planAbs_rec M hφ hF hβ.le s₀ hπ
  have hle : ENNReal.ofReal M.β * ∫⁻ z₁, planAbs M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 ≤
      planAbs M s₀ π := by rw [hrec]; exact le_add_self
  have hlt := hle.trans_lt hfin.lt_top
  have hne : ∫⁻ z₁, planAbs M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 ≠ ⊤ := by
    rcases ENNReal.mul_lt_top_iff.1 hlt with h | h | h
    · exact h.2.ne
    · exact absurd h (ENNReal.ofReal_pos.2 hβ).ne'
    · rw [h]; exact ENNReal.zero_ne_top
  exact ⟨hne, (ae_lt_top (measurable_planAbs_cont M hφ hF s₀ hπ) hne).mono fun _ h => h.ne⟩

/-- **Lemma 9.3 for absolutely summable plans.** If `Σ βᵗ ∫ |F| dμᵗ < ∞` and `β > 0`, then
`z₁ ↦ u[C(π, z₁), s₁]` is integrable and
`u(π, s₀) = F(x₀, π₀, z₀) + β ∫ u[C(π, z₁), s₁] Q(z₀, dz₁)`, by dominated convergence with the
dominating function `Σ βᵗ ∫ |F| dμᵗ` of the continuations. -/
theorem lemma_9_3_abs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤) :
    Integrable (fun z₁ => uR M (start₁ M s₀ π z₁) (cont π z₁)) (M.Q s₀.2) ∧
      uR M s₀ π = ret M s₀ π 0 Fin.elim0 +
        M.β * ∫ z₁, uR M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 := by
  obtain ⟨hne, hae⟩ := ae_planAbs_cont M hφ hF hβ s₀ hπ hfin
  have hmeas := (ex_9_1 M hφ hF s₀ hπ).1
  have hGm := measurable_planAbs_cont M hφ hF s₀ hπ
  have hG : Integrable (fun z₁ => (planAbs M (start₁ M s₀ π z₁) (cont π z₁)).toReal)
      (M.Q s₀.2) := integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hne
  have hbound : ∀ n, ∀ᵐ z₁ ∂M.Q s₀.2, ‖uN M (start₁ M s₀ π z₁) (cont π z₁) n‖ ≤
      (planAbs M (start₁ M s₀ π z₁) (cont π z₁)).toReal := fun n => by
    filter_upwards [hae] with z₁ hz₁
    rw [Real.norm_eq_abs]
    exact abs_uN_le_planAbs M hφ hF hβ.le _ (measurable_cont_plan hπ z₁) hz₁ n
  have hlim : ∀ᵐ z₁ ∂M.Q s₀.2, Tendsto (fun n => uN M (start₁ M s₀ π z₁) (cont π z₁) n) atTop
      (𝓝 (uR M (start₁ M s₀ π z₁) (cont π z₁))) := by
    filter_upwards [hae] with z₁ hz₁
    exact tendsto_uN_abs M hφ hF hβ.le _ (measurable_cont_plan hπ z₁) hz₁
  have hIu : Integrable (fun z₁ => uR M (start₁ M s₀ π z₁) (cont π z₁)) (M.Q s₀.2) := by
    refine hG.mono' (aestronglyMeasurable_of_tendsto_ae _
      (fun n => (hmeas n).aestronglyMeasurable) hlim) ?_
    filter_upwards [hlim, hae] with z₁ hz₁ hfz
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp hz₁) fun n => by
      rw [Function.comp_apply, Real.norm_eq_abs]
      exact abs_uN_le_planAbs M hφ hF hβ.le _ (measurable_cont_plan hπ z₁) hfz n
  refine ⟨hIu, ?_⟩
  have hDCT := tendsto_integral_of_dominated_convergence _
    (fun n => (hmeas n).aestronglyMeasurable) hG hbound hlim
  have hrec : Tendsto (fun n => uN M s₀ π (n + 1)) atTop (𝓝 (ret M s₀ π 0 Fin.elim0 +
      M.β * ∫ z₁, uR M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2)) := by
    simp_rw [uN_succ M s₀ π (integrable_ret_of_planAbs M hφ hF hβ s₀ hπ hfin)]
    exact tendsto_const_nhds.add (hDCT.const_mul _)
  exact tendsto_nhds_unique ((tendsto_uN_abs M hφ hF hβ.le s₀ hπ hfin).comp
    (tendsto_add_atTop_nat 1)) hrec

/-- Assumption 9.3 implies absolute summability. -/
theorem planAbs_ne_top_of_bound (hβ : 0 ≤ M.β) (s₀ : X × Z) (π : Plan Y Z) {L : ℕ → ℝ}
    (hL : ∀ t h, |ret M s₀ π t h| ≤ L t) (hsum : Summable fun t => M.β ^ t * L t) :
    planAbs M s₀ π ≠ ⊤ := by
  have hL0 := bound_nonneg M s₀ π hL
  rw [planAbs_eq]
  refine ne_top_of_le_ne_top (ENNReal.ofReal_tsum_of_nonneg
    (fun t => mul_nonneg (pow_nonneg hβ t) (hL0 t)) hsum ▸ ENNReal.ofReal_ne_top) ?_
  refine ENNReal.tsum_le_tsum fun t => ?_
  have := ex_8_8a M.Q t
  rw [ENNReal.ofReal_mul (pow_nonneg hβ t)]
  gcongr
  calc ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2
      ≤ ∫⁻ _h, ENNReal.ofReal (L t) ∂hist M.Q t s₀.2 :=
        lintegral_mono fun h => ENNReal.ofReal_le_ofReal (hL t h)
    _ = ENNReal.ofReal (L t) := by simp

end StokeyLucasPrescott.StochasticDP
