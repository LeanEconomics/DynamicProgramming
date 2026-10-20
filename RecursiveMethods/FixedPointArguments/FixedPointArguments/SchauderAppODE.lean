/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.SchauderBoundedContinuous

/-!
# Exercise 17.5: Peano-type existence via Schauder

SLP §17.4, Exercise 17.5, p. 520: the initial-value problem `x′(t) = f(x(t))`, `x(0) = c`.

* `fpOdeOp` the integral operator `(Tx)(t) = c + ∫₀ᵗ f(x(s)) ds` on `C[0, t₀]`, and
  `fp_ode_exists`: if `|f| ≤ M` on `[c − δ, c + δ]` and `t₀ M ≤ δ`, Schauder's theorem on the
  closed `δ`-ball about the constant `c` in `C[0, t₀]` gives a solution on `[0, t₀]` (the manual's
  argument; total boundedness of `T(D)` is `totallyBounded_of_equicontinuous`, the half of
  Arzelà–Ascoli behind `theorem_17_4`).
* `ex_17_5a_local` (**Exercise 17.5a, corrected**): for continuous `f` there is `t₀ ∈ (0, 1]` and
  a solution on `[0, t₀]`.
* `ex_17_5a_of_bounded` (**Exercise 17.5a, corrected**): for continuous bounded `f` there is a
  solution on all of `[0, 1]`.
* `ex_17_5a_counterexample`, `ex_17_5a_false`: the book's claim is false.
* `ex_17_5a_blowup_solution`: `x(t) = 2/(1 − 2t)` is the local solution for `f(x) = x²`, `c = 2`.
* `ex_17_5b` (**Exercise 17.5b**): `x ≡ 0` and `x(t) = t²/4` both solve `x′ = √x`, `x(0) = 0`
  on `[0, 1]`; `ex_17_5b_family`: so does `((t − s)⁺)²/4` for every `s ∈ [0, 1]`.
* `ex_17_5b_manual_counterexample`: the manual's `t²/2` is not a solution.
* `ex_17_5c` (**Exercise 17.5c**): `√·` is not Lipschitz on `ℝ₊`, which is the hypothesis of
  Exercise 3.10 that the equation violates.

**Corrections.**
* Exercise 17.5a is false as stated: continuity of `f` gives only local existence.
  `ex_17_5a_counterexample`: for `f(x) = x²`, `c = 2` there is no solution on `[0, 1]`, even with
  one-sided derivatives at the end points (`t + 1/x(t)` would be constant, forcing
  `1/x(1/2) = 0`). Corrected statements: `ex_17_5a_local` (the manual's local result) and
  `ex_17_5a_of_bounded`.
* The manual's ball `D` must be centred at the constant function `c`, not at `0`
  (`fp_ode_exists` uses the ball about `c`).
* The manual's second solution to 17.5b, `t²/2`, is wrong (`ex_17_5b_manual_counterexample`); the
  correct one is `t²/4`, and there are infinitely many (`ex_17_5b_family`).
* In 17.5c the book's "Exercise 3.8" should be "Exercise 3.10" (the Lipschitz ODE exercise,
  p. 53).
-/

namespace StokeyLucasPrescott.FixedPointArguments

open Set Filter Topology Metric BoundedContinuousFunction

/-! ### The integral operator and local existence -/

/-- The integral operator of Exercise 17.5, `(Tx)(t) = c + ∫₀ᵗ f(x(s)) ds`, on `C[0, t₀]`. The
function `x` on `[0, t₀]` is extended to `ℝ` by constants (`IccExtend`). -/
noncomputable def fpOdeOp (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ) {t₀ : ℝ} (h0 : 0 ≤ t₀)
    (x : Icc (0 : ℝ) t₀ →ᵇ ℝ) : Icc (0 : ℝ) t₀ →ᵇ ℝ :=
  mkOfCompact
    ⟨fun t => c + ∫ s in (0 : ℝ)..(t : ℝ), f (IccExtend h0 x s),
      continuous_const.add <| (continuous_iff_continuousAt.2 fun u =>
        ((hf.comp (Continuous.Icc_extend' (h := h0) x.continuous)).integral_hasStrictDerivAt
          0 u).hasDerivAt.continuousAt).comp continuous_subtype_val⟩

/-- **Existence on `[0, t₀]` via Schauder** (manual, Exercise 17.5a). If `f` is continuous,
`|f| ≤ M` on `[c − δ, c + δ]` and `t₀ M ≤ δ`, then `x′ = f(x)`, `x(0) = c` has a solution on
`[0, t₀]`. -/
theorem fp_ode_exists {f : ℝ → ℝ} (hf : Continuous f) {c δ M t₀ : ℝ} (ht₀ : 0 < t₀)
    (hδ : 0 ≤ δ) (hM : ∀ z, |z - c| ≤ δ → |f z| ≤ M) (htM : t₀ * M ≤ δ) :
    ∃ x : ℝ → ℝ, x 0 = c ∧ ∀ t ∈ Icc 0 t₀, HasDerivAt x (f (x t)) t := by
  have h0 : (0 : ℝ) ≤ t₀ := ht₀.le
  set D : Set (Icc (0 : ℝ) t₀ →ᵇ ℝ) := closedBall (const _ c) δ with hD
  set T := fpOdeOp f hf c h0 with hT
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c (by simpa using hδ))
  have hval : ∀ x ∈ D, ∀ s : ℝ, |IccExtend h0 x s - c| ≤ δ := by
    intro x hx s
    rw [IccExtend_apply]
    have h1 := dist_coe_le_dist (f := x) (g := const _ c) (projIcc 0 t₀ h0 s)
    rw [Real.dist_eq, const_apply] at h1
    exact h1.trans (mem_closedBall.1 hx)
  have hg : ∀ x : Icc (0 : ℝ) t₀ →ᵇ ℝ, Continuous fun s => f (IccExtend h0 x s) := fun x =>
    hf.comp (Continuous.Icc_extend' (h := h0) x.continuous)
  have hTapp : ∀ (x : Icc (0 : ℝ) t₀ →ᵇ ℝ) (t : Icc (0 : ℝ) t₀),
      T x t = c + ∫ s in (0 : ℝ)..(t : ℝ), f (IccExtend h0 x s) := fun _ _ => rfl
  have hfb : ∀ x ∈ D, ∀ s : ℝ, ‖f (IccExtend h0 x s)‖ ≤ M := fun x hx s => by
    rw [Real.norm_eq_abs]
    exact hM _ (hval x hx s)
  -- `T(D) ⊆ D`
  have hmaps : MapsTo T D D := by
    intro x hx
    rw [mem_closedBall]
    refine (BoundedContinuousFunction.dist_le hδ).2 fun t => ?_
    rw [hTapp, const_apply, Real.dist_eq, add_sub_cancel_left]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
      (C := M) (f := fun s => f (IccExtend h0 x s)) fun s _ => hfb x hx s
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.2.1] at this
    calc _ ≤ M * t := this
      _ ≤ M * t₀ := mul_le_mul_of_nonneg_left t.2.2 hM0
      _ ≤ δ := by linarith
  -- `T(D)` is equicontinuous
  have hequi : ∀ ε > 0, ∃ η > 0, ∀ t t' : Icc (0 : ℝ) t₀, dist t t' < η →
      ∀ g ∈ T '' D, |g t - g t'| < ε := by
    intro ε hε
    refine ⟨ε / (M + 1), by positivity, fun t t' htt' => ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hTapp, hTapp, add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      ((hg x).intervalIntegrable _ _) ((hg x).intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (t' : ℝ)) (b := (t : ℝ))
      (C := M) (f := fun s => f (IccExtend h0 x s)) fun s _ => hfb x hx s
    rw [Real.norm_eq_abs] at this
    have hd : |(t : ℝ) - t'| < ε / (M + 1) := by rwa [Subtype.dist_eq, Real.dist_eq] at htt'
    have hlt : M * (ε / (M + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    calc _ ≤ M * |(t : ℝ) - t'| := this
      _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hd.le hM0
      _ < ε := hlt
  -- `T` is continuous on `D`
  have hcont : ContinuousOn T D := by
    have huc := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc (a := c - δ) (b := c + δ)).uniformContinuousOn_of_continuous
        hf.continuousOn)
    refine Metric.continuousOn_iff.2 fun y hy ε hε => ?_
    obtain ⟨η, hη, hηf⟩ := huc (ε / (2 * (t₀ + 1))) (by positivity)
    refine ⟨η, hη, fun x hx hxy => ?_⟩
    have hpt : ∀ s : ℝ,
        ‖f (IccExtend h0 x s) - f (IccExtend h0 y s)‖ ≤ ε / (2 * (t₀ + 1)) := by
      intro s
      have hxs := abs_le.1 (hval x hx s)
      have hys := abs_le.1 (hval y hy s)
      have hmx : IccExtend h0 x s ∈ Icc (c - δ) (c + δ) := ⟨by linarith, by linarith⟩
      have hmy : IccExtend h0 y s ∈ Icc (c - δ) (c + δ) := ⟨by linarith, by linarith⟩
      have hd : dist (IccExtend h0 x s) (IccExtend h0 y s) < η := by
        rw [IccExtend_apply, IccExtend_apply]
        exact (dist_coe_le_dist _).trans_lt hxy
      have := hηf _ hmx _ hmy hd
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      exact this.le
    have hle : dist (T x) (T y) ≤ ε / 2 := by
      refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun t => ?_
      rw [hTapp, hTapp, Real.dist_eq, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
        ((hg x).intervalIntegrable _ _) ((hg y).intervalIntegrable _ _)]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
        (C := ε / (2 * (t₀ + 1)))
        (f := fun s => f (IccExtend h0 x s) - f (IccExtend h0 y s)) fun s _ => hpt s
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.2.1] at this
      calc _ ≤ ε / (2 * (t₀ + 1)) * t := this
        _ ≤ ε / (2 * (t₀ + 1)) * (t₀ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [t.2.2]) (by positivity)
        _ = ε / 2 := by field_simp
    linarith
  -- Schauder
  have hXtb : TotallyBounded (univ : Set (Icc (0 : ℝ) t₀)) :=
    (isCompact_iff_isCompact_univ.1 isCompact_Icc).totallyBounded
  have hbdd : Bornology.IsBounded (T '' D) := isBounded_closedBall.subset hmaps.image_subset
  have htb := totallyBounded_of_equicontinuous hXtb hbdd hequi
  obtain ⟨x, -, hTx⟩ := schauder_closed isClosed_closedBall (convex_closedBall _ _)
    (nonempty_closedBall.2 hδ) hcont hmaps (htb.closure.isCompact_of_isClosed isClosed_closure)
  refine ⟨fun u => c + ∫ s in (0 : ℝ)..u, f (IccExtend h0 x s), by simp, fun t ht => ?_⟩
  have hd := ((hg x).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add c
  have hxt : c + ∫ s in (0 : ℝ)..t, f (IccExtend h0 x s) = IccExtend h0 x t := by
    have := congrArg (fun g : Icc (0 : ℝ) t₀ →ᵇ ℝ => g ⟨t, ht⟩) hTx
    rw [hTapp] at this
    rw [IccExtend_of_mem _ _ ht, ← this]
  simp only
  rw [hxt]
  exact hd

/-- **Exercise 17.5a, corrected: local existence** (the manual's result). If `f` is continuous,
there is `t₀ ∈ (0, 1]` such that `x′ = f(x)`, `x(0) = c` has a solution on `[0, t₀]`. -/
theorem ex_17_5a_local {f : ℝ → ℝ} (hf : Continuous f) (c : ℝ) :
    ∃ t₀ ∈ Ioc (0 : ℝ) 1, ∃ x : ℝ → ℝ, x 0 = c ∧ ∀ t ∈ Icc 0 t₀, HasDerivAt x (f (x t)) t := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.1 hf c 1 one_pos
  set M := |f c| + 1 with hMdef
  have hM0 : 0 < M := by positivity
  have hM : ∀ z, |z - c| ≤ δ / 2 → |f z| ≤ M := fun z hz => by
    have h1 := hδf z (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at h1
    have h2 := abs_sub_abs_le_abs_sub (f z) (f c)
    linarith
  have ht₀ : 0 < min 1 (δ / 2 / M) := lt_min one_pos (by positivity)
  refine ⟨min 1 (δ / 2 / M), ⟨ht₀, min_le_left _ _⟩,
    fp_ode_exists hf ht₀ (by positivity) hM ?_⟩
  calc min 1 (δ / 2 / M) * M ≤ δ / 2 / M * M :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hM0.le
    _ = δ / 2 := by field_simp

/-- **Exercise 17.5a, corrected: bounded `f`.** If `f` is continuous and bounded, then
`x′ = f(x)`, `x(0) = c` has a solution on all of `[0, 1]`. -/
theorem ex_17_5a_of_bounded {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ z, |f z| ≤ M)
    (c : ℝ) : ∃ x : ℝ → ℝ, x 0 = c ∧ ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (f (x t)) t :=
  fp_ode_exists hf one_pos ((abs_nonneg _).trans (hM 0)) (fun z _ => hM z) (by rw [one_mul])

/-! ### The counterexample to Exercise 17.5a -/

/-- **Counterexample to Exercise 17.5a.** For `f(x) = x²` and `c = 2` there is no solution of
`x′ = x²`, `x(0) = 2` on `[0, 1]`, even allowing one-sided derivatives at the end points. -/
theorem ex_17_5a_counterexample :
    ¬ ∃ x : ℝ → ℝ, x 0 = 2 ∧ ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x (x t ^ 2) (Icc 0 1) t := by
  rintro ⟨x, hx0, hx⟩
  have hcont : ContinuousOn x (Icc 0 1) := fun t ht => (hx t ht).continuousWithinAt
  have hmono : MonotoneOn x (Icc 0 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont
      (fun t ht => (hx t (interior_subset ht)).mono interior_subset) fun t _ => sq_nonneg _
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 2 ≤ x t := fun t ht => by
    rw [← hx0]
    exact hmono (left_mem_Icc.2 zero_le_one) ht ht.1
  -- `g(t) = t + 1/x(t)` has derivative `0`
  set g : ℝ → ℝ := fun t => t + (x t)⁻¹ with hg
  have hgd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g 0 (Icc 0 1) t := by
    intro t ht
    have hxt : x t ≠ 0 := by linarith [hpos t ht]
    have := (hasDerivWithinAt_id t (Icc 0 1)).add ((hx t ht).inv hxt)
    have h0 : (1 : ℝ) + -(x t ^ 2) / x t ^ 2 = 0 := by field_simp; ring
    rw [h0] at this
    exact this
  have hsub : Icc (0 : ℝ) (1 / 2) ⊆ Icc 0 1 := Icc_subset_Icc_right (by norm_num)
  have hconst := constant_of_has_deriv_right_zero (a := 0) (b := 1 / 2)
    (fun t ht => (hgd t (hsub ht)).continuousWithinAt.mono hsub) fun t ht =>
      (hgd t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht.1, by linarith [ht.2]⟩)
  have h := hconst (1 / 2) (right_mem_Icc.2 (by norm_num))
  simp only [hg, hx0] at h
  have h2 := hpos (1 / 2) (hsub (right_mem_Icc.2 (by norm_num)))
  have h3 : (x (1 / 2))⁻¹ = 0 := by linarith
  rw [inv_eq_zero] at h3
  linarith

/-- **Exercise 17.5a is false**: not every continuous `f` gives a solution on `[0, 1]`. -/
theorem ex_17_5a_false :
    ¬ ∀ f : ℝ → ℝ, Continuous f → ∀ c : ℝ, ∃ x : ℝ → ℝ, x 0 = c ∧
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x (f (x t)) (Icc 0 1) t := fun h =>
  ex_17_5a_counterexample (h (fun y => y ^ 2) (continuous_pow 2) 2)

/-- The local solution of `x′ = x²`, `x(0) = 2` is `x(t) = 2/(1 − 2t)`, which blows up as
`t ↑ 1/2`. -/
theorem ex_17_5a_blowup_solution {t : ℝ} (ht : t < 1 / 2) :
    HasDerivAt (fun t : ℝ => 2 / (1 - 2 * t)) ((2 / (1 - 2 * t)) ^ 2) t := by
  have hne : 1 - 2 * t ≠ 0 := by linarith
  have := (hasDerivAt_const t (2 : ℝ)).div (((hasDerivAt_id' t).const_mul 2).const_sub 1) hne
  convert this using 1
  field_simp
  ring

/-! ### Exercise 17.5b and 17.5c -/

/-- **Exercise 17.5b.** `x ≡ 0` and `x(t) = t²/4` are two different solutions of `x′ = √x`,
`x(0) = 0` on `[0, 1]`. -/
theorem ex_17_5b :
    ∃ x₁ x₂ : ℝ → ℝ, x₁ 0 = 0 ∧ x₂ 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x₁ (√(x₁ t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x₂ (√(x₂ t)) t) ∧ x₁ 1 ≠ x₂ 1 := by
  refine ⟨fun _ => 0, fun t => t ^ 2 / 4, rfl, by norm_num, fun t _ => ?_, fun t ht => ?_,
    by norm_num⟩
  · simpa using hasDerivAt_const t (0 : ℝ)
  · have h1 : √(t ^ 2 / 4) = t / 2 := by
      rw [show t ^ 2 / 4 = (t / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by linarith [ht.1])
    rw [h1]
    have := (hasDerivAt_pow 2 t).div_const 4
    convert this using 1
    norm_num
    ring

/-- **Exercise 17.5b, all solutions of this shape.** For every `s ∈ [0, 1]`,
`xₛ(t) = ((t − s)⁺)²/4` solves `x′ = √x`, `x(0) = 0` (on all of `ℝ`). -/
theorem ex_17_5b_family {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (fun t : ℝ => max (t - s) 0 ^ 2 / 4) 0 = 0 ∧
      ∀ t : ℝ, HasDerivAt (fun t : ℝ => max (t - s) 0 ^ 2 / 4) (√(max (t - s) 0 ^ 2 / 4)) t := by
  refine ⟨by simp [hs.1], fun t => ?_⟩
  have hsq : √(max (t - s) 0 ^ 2 / 4) = max (t - s) 0 / 2 := by
    rw [show max (t - s) 0 ^ 2 / 4 = (max (t - s) 0 / 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  have hq : ∀ u : ℝ, HasDerivAt (fun t : ℝ => (t - s) ^ 2 / 4) ((u - s) / 2) u := fun u => by
    have := (((hasDerivAt_id' u).sub_const s).pow 2).div_const 4
    convert this using 1
    norm_num
    ring
  rcases lt_trichotomy t s with h | h | h
  · have hev : (fun t : ℝ => max (t - s) 0 ^ 2 / 4) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with u hu
      simp [max_eq_right (by linarith [mem_Iio.1 hu] : u - s ≤ 0)]
    rw [max_eq_right (by linarith : t - s ≤ 0), zero_div]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · subst h
    rw [sub_self, max_self, zero_div]
    have h1 : HasDerivWithinAt (fun u : ℝ => max (u - t) 0 ^ 2 / 4) 0 (Ici t) t := by
      have := (hq t).hasDerivWithinAt (s := Ici t)
      rw [sub_self, zero_div] at this
      refine this.congr (fun u hu => ?_) (by simp)
      simp [max_eq_left (by linarith [mem_Ici.1 hu] : 0 ≤ u - t)]
    have h2 : HasDerivWithinAt (fun u : ℝ => max (u - t) 0 ^ 2 / 4) 0 (Iic t) t := by
      refine (hasDerivWithinAt_const t (Iic t) (0 : ℝ)).congr (fun u hu => ?_) (by simp)
      simp [max_eq_right (by linarith [mem_Iic.1 hu] : u - t ≤ 0)]
    have := h2.union h1
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have hev : (fun t : ℝ => max (t - s) 0 ^ 2 / 4) =ᶠ[𝓝 t] fun t => (t - s) ^ 2 / 4 := by
      filter_upwards [Ioi_mem_nhds h] with u hu
      simp [max_eq_left (by linarith [mem_Ioi.1 hu] : 0 ≤ u - s)]
    rw [max_eq_left (by linarith : 0 ≤ t - s)]
    exact (hq t).congr_of_eventuallyEq hev

/-- **The manual's answer to Exercise 17.5b is wrong**: `x(t) = t²/2` does not solve `x′ = √x` on
`[0, 1]` (at `t = 1`, `x′(1) = 1 ≠ √(1/2)`). -/
theorem ex_17_5b_manual_counterexample :
    ¬ ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => t ^ 2 / 2) (√(t ^ 2 / 2)) (Icc 0 1) t := by
  intro h
  have h1 := h 1 (right_mem_Icc.2 zero_le_one)
  have h2 : HasDerivWithinAt (fun t : ℝ => t ^ 2 / 2) 1 (Icc 0 1) 1 := by
    have := (hasDerivAt_pow 2 (1 : ℝ)).div_const 2
    convert this.hasDerivWithinAt using 1
    norm_num
  have := (uniqueDiffOn_Icc zero_lt_one 1 (right_mem_Icc.2 zero_le_one)).eq_deriv _ h1 h2
  rw [Real.sqrt_eq_one] at this
  norm_num at this

/-- **Exercise 17.5c.** The equation `x′ = √x` violates the Lipschitz condition of Exercise 3.10
(the book says "Exercise 3.8"): there is no `B` with `|√y − √z| ≤ B|y − z|` on `ℝ₊`. -/
theorem ex_17_5c : ¬ ∃ B : ℝ, ∀ y z : ℝ, 0 ≤ y → 0 ≤ z → |√y - √z| ≤ B * |y - z| := by
  rintro ⟨B, hB⟩
  set k := |B| + 1 with hk
  have hk0 : 0 < k := by positivity
  have h := hB ((1 / k) ^ 2) 0 (by positivity) le_rfl
  rw [Real.sqrt_sq (by positivity), Real.sqrt_zero, sub_zero, sub_zero,
    abs_of_pos (by positivity), abs_of_pos (by positivity)] at h
  have h2 : k ≤ B := by
    have h3 : 1 / k * k ^ 2 ≤ B * (1 / k) ^ 2 * k ^ 2 :=
      mul_le_mul_of_nonneg_right h (by positivity)
    have e1 : 1 / k * k ^ 2 = k := by field_simp
    have e2 : B * (1 / k) ^ 2 * k ^ 2 = B := by field_simp
    linarith
  linarith [le_abs_self B]

end StokeyLucasPrescott.FixedPointArguments
