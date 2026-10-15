/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.IndustryInvestment

/-!
# Industry investment under uncertainty: results

SLP §10.4, Exercise 10.4b–c, pp. 294–295. Let `v` be the fixed point of the truncated operator
of `UpperBounded` for (2′), and `β = 1/(1 + r)`, `R = A/(1 − β)`.

* `ind_rhs_le`: on nonnegative functions bounded by `R` and nondecreasing in `x`, no `y > 0`
  beats the maximum over `Γ(x)`: below `(1 − δ′)x` the cost is `0` and `(1 − δ)x` does better;
  above `max{M, x}` the cost exceeds `R`.
* **Exercise 10.4b** (`ex_10_4b`): `v` is the unique bounded continuous solution of (2′),
  `0 ≤ v ≤ R`, and `v` also solves (2), the problem over all of `X`.
* **Exercise 10.4c** (`ex_10_4c`): `v` is strictly increasing in `x` and, for monotone `Q`, in
  `z`; strictly concave in `x`; the policy is a continuous function `g` with `g(x, z)` in the
  interior of `Γ(x)` (indeed `(1 − δ)x ≤ g(x, z) < max{M, x}`); and where `U(·, z)` and `c` are
  differentiable, `v_x = U_x − c(g/x) + (g/x)c′(g/x)` (Benveniste–Scheinkman). Because
  Assumptions 9.9 and 9.11 fail for (2′) (`ind_Γ_not_mono`, `ind_Γ_not_convex`), Theorems 9.7
  and 9.8 do not apply directly; the proofs go through (2), whose constraint set is all of `X`.
* **Exercise 10.4d** (`ex_10_4d`): `g` is nondecreasing in `x`, by Topkis's argument: `Γ` is
  ascending and the cost `x c(y/x)` has decreasing differences (`ind_cost_submod`). The
  manual's further claims (strict increase, `g(x, z)/x` decreasing) rest on first-order
  conditions and are not formalised.
* **Exercise 10.4f** (`ex_10_4f`, `ex_10_4f_monotone`, `ex_10_4f_tendsto`): under i.i.d. shocks
  `g` does not depend on `z`, and every optimal capacity path is monotone and converges.
  Exercise 10.4e is not formalised: the manual's step "`D` increasing in `z` implies `v_x`
  increasing in `z`" ignores the dependence of `g` on `z`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

variable {U : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {δ δ' M r A z₁ z₂ : ℝ}

/-- The right side of (2) at any `y > 0`. -/
theorem ind_rhs (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) (f : Ioi (0 : ℝ) × Icc z₁ z₂ → ℝ)
    (s : Ioi (0 : ℝ) × Icc z₁ z₂) (y : Ioi (0 : ℝ)) :
    rhs (indModel Q U c δ' M r) f s y =
      indF U c (s.1, y, s.2) + 1 / (1 + r) * ∫ z', f (y, z') ∂Q s.2 := rfl

theorem integrable_ind {Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)} [IsMarkovKernel Q]
    (f : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ) (y : Ioi (0 : ℝ)) (z : Icc z₁ z₂) :
    Integrable (fun z' => f (y, z')) (Q z) :=
  integrable_section_v (Q z) f y

/-- **No `y > 0` beats `Γ(x)`.** On functions with values in `[0, R]`, nondecreasing in `x`, the
right side of (2) at any `y > 0` is at most the truncated maximum over `Γ(x)`. -/
theorem ind_rhs_le (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {f : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hfR : ∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - 1 / (1 + r)))
    (hfm : ∀ z, Monotone fun x => f (x, z)) (s : Ioi (0 : ℝ) × Icc z₁ z₂) (y : Ioi (0 : ℝ)) :
    rhs (indModel Q U c δ' M r) f s y ≤ truncT (h.upperDP Q hQ) f s := by
  have hd := h.upperDP Q hQ
  obtain ⟨y', hy', hval, hmax⟩ := trunc_bellman_argmax hd hfR s
  obtain ⟨x, z⟩ := s
  have hx : 0 < x.1 := x.2
  have hy : 0 < y.1 := y.2
  have hb : 0 < 1 / (1 + r) := one_div_pos.2 (by linarith [h.r_pos])
  have hb1 : 1 / (1 + r) < 1 := (div_lt_one (by linarith [h.r_pos])).2 (by linarith [h.r_pos])
  have hEle : ∀ y'' : Ioi (0 : ℝ), ∫ z', f (y'', z') ∂Q z ≤ A / (1 - 1 / (1 + r)) :=
    fun y'' => by
    have := integral_mono (integrable_ind (Q := Q) f y'' z)
      (integrable_const (A / (1 - 1 / (1 + r)))) fun z' => (hfR _).2
    simpa using this
  have hT0 : 0 ≤ truncT hd f (x, z) := (truncT_mapsTo hd hfR (x, z)).1
  by_cases hlow : y.1 < (1 - δ') * x.1
  · -- below `Γ(x)`: the cost is zero, and `(1 − δ)x` is feasible and better
    obtain ⟨hsm, hsF⟩ := h.safe_mem x z
    refine le_trans ?_ (hmax _ hsm)
    rw [ind_rhs, ind_rhs]
    have hc0 : c (y.1 / x.1) = 0 := h.c_zero _ (div_nonneg hy.le hx.le) (by
      rw [div_le_iff₀ hx]; linarith [h.δ_lt, mul_lt_mul_of_pos_right h.δ_lt hx])
    have hF : indF U c (x, y, z) = U x.1 z.1 := by simp only [indF, hc0, mul_zero, sub_zero]
    simp only at hsF ⊢
    rw [hF, hsF]
    have hmono : ∫ z', f (y, z') ∂Q z ≤ ∫ z', f (h.safeY x, z') ∂Q z :=
      integral_mono (integrable_ind (Q := Q) f y z) (integrable_ind (Q := Q) f _ z) fun z' =>
        hfm z' (by
        change y.1 ≤ (1 - δ) * x.1
        nlinarith [h.δ_lt])
    nlinarith [mul_le_mul_of_nonneg_left hmono hb.le]
  by_cases hhigh : max M x.1 < y.1
  · -- above `Γ(x)`: the cost exceeds `R`, so the value is negative
    refine le_trans ?_ hT0
    rw [ind_rhs]
    have hyx : 1 ≤ y.1 / x.1 := by rw [le_div_iff₀ hx]; linarith [le_max_right M x.1]
    have hcost : y.1 * c 1 ≤ x.1 * c (y.1 / x.1) := by
      have := mul_le_mul_of_nonneg_left (h.c_ge_mul hyx) hx.le
      rwa [← mul_assoc, mul_div_cancel₀ _ hx.ne'] at this
    have hMy : M * c 1 ≤ y.1 * c 1 :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_left M x.1]) h.c_one_pos.le
    have hUA := h.U_le x.1 z.1 hx.le z.2
    have hR := h.M_big
    have hE := mul_le_mul_of_nonneg_left (hEle y) hb.le
    have hden : (1 : ℝ) - 1 / (1 + r) ≠ 0 := (sub_pos.2 hb1).ne'
    have e' : ∀ b : ℝ, 1 - b ≠ 0 → A / (1 - b) = A + b * (A / (1 - b)) := fun b hb => by
      field_simp; ring
    have e := e' _ hden
    simp only [indF]
    nlinarith
  · exact hmax y ⟨not_lt.1 hlow, not_lt.1 hhigh⟩

/-- Choosing `y ≥ max{M, x}` gives a negative value on functions with values in `[0, R]`. -/
theorem ind_rhs_neg (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] {f : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hfR : ∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - 1 / (1 + r))) (s : Ioi (0 : ℝ) × Icc z₁ z₂)
    {y : Ioi (0 : ℝ)} (hy : max M s.1.1 ≤ y.1) : rhs (indModel Q U c δ' M r) f s y < 0 := by
  obtain ⟨x, z⟩ := s
  have hx : 0 < x.1 := x.2
  have hb : 0 < 1 / (1 + r) := one_div_pos.2 (by linarith [h.r_pos])
  have hb1 : 1 / (1 + r) < 1 := (div_lt_one (by linarith [h.r_pos])).2 (by linarith [h.r_pos])
  have hEle : ∫ z', f (y, z') ∂Q z ≤ A / (1 - 1 / (1 + r)) := by
    have := integral_mono (integrable_ind (Q := Q) f y z)
      (integrable_const (A / (1 - 1 / (1 + r)))) fun z' => (hfR _).2
    simpa using this
  rw [ind_rhs]
  have hyx : 1 ≤ y.1 / x.1 := by rw [le_div_iff₀ hx]; linarith [le_max_right M x.1]
  have hcost : y.1 * c 1 ≤ x.1 * c (y.1 / x.1) := by
    have := mul_le_mul_of_nonneg_left (h.c_ge_mul hyx) hx.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hx.ne'] at this
  have hMy : M * c 1 ≤ y.1 * c 1 :=
    mul_le_mul_of_nonneg_right (by linarith [le_max_left M x.1]) h.c_one_pos.le
  have hUA := h.U_le x.1 z.1 hx.le z.2
  have hR := h.M_big
  have hE := mul_le_mul_of_nonneg_left hEle hb.le
  have hden : (1 : ℝ) - 1 / (1 + r) ≠ 0 := (sub_pos.2 hb1).ne'
  have e' : ∀ b : ℝ, 1 - b ≠ 0 → A / (1 - b) = A + b * (A / (1 - b)) := fun b hb => by
    field_simp; ring
  have e := e' _ hden
  simp only [indF]
  nlinarith

theorem isClosed_monoX :
    IsClosed {f : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ | ∀ z, Monotone fun x => f (x, z)} := by
  have := isClosed_pointwise_le (S := Ioi (0 : ℝ) × Icc z₁ z₂)
    (ι := {q : Ioi (0 : ℝ) × Ioi (0 : ℝ) × Icc z₁ z₂ // q.1 ≤ q.2.1})
    (fun q => (q.1.1, q.1.2.2)) (fun q => (q.1.2.1, q.1.2.2))
  convert this using 1
  ext f
  exact ⟨fun hf q => hf q.1.2.2 q.2, fun hf z x x' hxx' => hf ⟨(x, x', z), hxx'⟩⟩

/-- `T̃` maps functions with values in `[0, R]`, nondecreasing in `x`, to functions strictly
increasing in `x`: compare the optimal `y` at `x` with the same `y` at `x′`, using (2). -/
theorem ind_T_strictMono_x (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {f : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hfR : ∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - 1 / (1 + r)))
    (hfm : ∀ z, Monotone fun x => f (x, z)) (z : Icc z₁ z₂) :
    StrictMono fun x => truncT (h.upperDP Q hQ) f (x, z) := by
  intro x x' hxx'
  obtain ⟨y, -, hval, -⟩ := trunc_bellman_argmax (h.upperDP Q hQ) hfR (x, z)
  have hle := ind_rhs_le h Q hQ hfR hfm (x', z) y
  dsimp only
  rw [hval]
  refine lt_of_lt_of_le ?_ hle
  rw [ind_rhs, ind_rhs]
  have hx : 0 < x.1 := x.2
  have hU := h.U_mono z.1 z.2 (mem_Ici.2 hx.le) (mem_Ici.2 (le_of_lt x'.2)) hxx'
  have hp := h.persp_anti hx (le_of_lt hxx') (le_of_lt y.2)
  simp only [indF] at hU ⊢
  linarith

/-- The fixed point is strictly increasing in `x`. -/
theorem ind_strictMono_x (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v) :
    (∀ s, 0 ≤ v s ∧ v s ≤ A / (1 - 1 / (1 + r))) ∧ ∀ z, StrictMono fun x => v (x, z) := by
  have hd := h.upperDP Q hQ
  have hb := truncModel_boundedDP hd (truncK_pos hd).le
  set S' : Set (Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ) :=
    {f | (∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - 1 / (1 + r))) ∧ ∀ z, Monotone fun x => f (x, z)}
  have hclosed : IsClosed S' := (isClosed_bounds _).inter isClosed_monoX
  have hmaps : ∀ f ∈ S', truncT hd f ∈ {f : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ |
      (∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - 1 / (1 + r))) ∧ ∀ z, StrictMono fun x => f (x, z)} :=
    fun f hf => ⟨truncT_mapsTo hd hf.1, fun z => ind_T_strictMono_x h Q hQ hf.1 hf.2 z⟩
  have := (corollary_1 (S' := S') (bellman_contraction _ hb) hv
    ⟨0, fun _ => ⟨le_rfl, div_nonneg hd.A_nonneg (by linarith [hd.β_lt])⟩,
      fun _ _ _ _ => le_rfl⟩ hclosed (fun f hf => ⟨(hmaps f hf).1,
        fun z => ((hmaps f hf).2 z).monotone⟩) hmaps).2
  exact this

/-- **Exercise 10.4b.** There is a unique bounded continuous `v` solving (2′); it satisfies
`0 ≤ v ≤ R` and also solves (2): the maximum over `Γ(x)` is the supremum over all `y > 0`. -/
theorem ex_10_4b (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) :
    ∃ v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ, truncT (h.upperDP Q hQ) v = v ∧
      (∀ s, 0 ≤ v s ∧ v s ≤ A / (1 - 1 / (1 + r))) ∧ SolvesFE (indModel Q U c δ' M r) v ∧
      (∀ w : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ, SolvesFE (indModel Q U c δ' M r) w → w = v) ∧
      ∀ s, IsLUB (Set.range fun y : Ioi (0 : ℝ) => rhs (indModel Q U c δ' M r) v s y) (v s) := by
  obtain ⟨v, hv, hvR, hatt, -, hFE, huniq⟩ := upper_fixed (h.upperDP Q hQ)
  refine ⟨v, hv, hvR, hFE, huniq, fun s => ?_⟩
  obtain ⟨y, -, hval⟩ := hatt s
  have hvm := (ind_strictMono_x h Q hQ hv).2
  refine IsGreatest.isLUB ⟨⟨y, hval.symm⟩, ?_⟩
  rintro _ ⟨y', rfl⟩
  have := ind_rhs_le h Q hQ hvR (fun z => (hvm z).monotone) s y'
  rwa [hv] at this

theorem isClosed_monoZ :
    IsClosed {f : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ | ∀ x, Monotone fun z => f (x, z)} := by
  have := isClosed_pointwise_le (S := Ioi (0 : ℝ) × Icc z₁ z₂)
    (ι := {q : Ioi (0 : ℝ) × Icc z₁ z₂ × Icc z₁ z₂ // q.2.1 ≤ q.2.2})
    (fun q => (q.1.1, q.1.2.1)) (fun q => (q.1.1, q.1.2.2))
  convert this using 1
  ext f
  exact ⟨fun hf q => hf q.1.1 q.2, fun hf x z z' hzz' => hf ⟨(x, z, z'), hzz'⟩⟩

/-- **Exercise 10.4c** (monotonicity in `z`). For `Q` monotone, `v(x, ·)` is strictly
increasing. -/
theorem ind_strictMono_z (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hQm : IsMonotoneTF Q) {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) (x : Ioi (0 : ℝ)) :
    StrictMono fun z => v (x, z) := by
  have hd := h.upperDP Q hQ
  have hb := truncModel_boundedDP hd (truncK_pos hd).le
  set B : Set (Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ) :=
    {f | (∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - 1 / (1 + r))) ∧ ∀ z, Monotone fun x => f (x, z)}
  set S' := B ∩ {f | ∀ x, Monotone fun z => f (x, z)}
  have hclosed : IsClosed S' :=
    ((isClosed_bounds _).inter isClosed_monoX).inter isClosed_monoZ
  have hstrict : ∀ f ∈ S', ∀ x, StrictMono fun z => truncT hd f (x, z) := by
    intro f hf x z z' hzz'
    obtain ⟨y, -, hval, -⟩ := trunc_bellman_argmax hd hf.1.1 (x, z)
    have hle := ind_rhs_le h Q hQ hf.1.1 hf.1.2 (x, z') y
    dsimp only
    rw [hval]
    refine lt_of_lt_of_le ?_ hle
    rw [ind_rhs, ind_rhs]
    have hU := h.U_mono_z x.1 x.2 z.2 z'.2 hzz'
    have hE : ∫ z'', f (y, z'') ∂Q z ≤ ∫ z'', f (y, z'') ∂Q z' :=
      hQm (fun z'' => f (y, z'')) (f.continuous.comp (Continuous.prodMk_right y)).measurable
        ⟨‖f‖, fun z'' => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _⟩ (hf.2 y)
        (le_of_lt hzz')
    have hb0 : 0 < 1 / (1 + r) := one_div_pos.2 (by linarith [h.r_pos])
    simp only [indF]
    nlinarith [mul_le_mul_of_nonneg_left hE hb0.le]
  have hmaps : MapsTo (truncT hd) S' S' := fun f hf =>
    ⟨⟨truncT_mapsTo hd hf.1.1, fun z => (ind_T_strictMono_x h Q hQ hf.1.1 hf.1.2 z).monotone⟩,
      fun x => (hstrict f hf x).monotone⟩
  have hv' := (corollary_1 (S' := S') (S'' := S') (bellman_contraction _ hb) hv
    ⟨0, ⟨fun _ => ⟨le_rfl, div_nonneg hd.A_nonneg (by linarith [hd.β_lt])⟩,
      fun _ _ _ _ => le_rfl⟩, fun _ _ _ _ => le_rfl⟩ hclosed hmaps hmaps).1
  have := hstrict v hv' x
  rwa [hv] at this

theorem cmb_Ioi_val {x x' : Ioi (0 : ℝ)} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (cmb (convex_Ioi (0 : ℝ)) h0 h1 x x').1 = θ * x.1 + (1 - θ) * x'.1 := by
  simp [cmb]

/-- **Exercise 10.4c** (strict concavity). `v(·, z)` is strictly concave. -/
theorem ind_strictConcave (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v) (z : Icc z₁ z₂) :
    IsStrictConcaveS (convex_Ioi (0 : ℝ)) fun x => v (x, z) := by
  have hd := h.upperDP Q hQ
  have hb := truncModel_boundedDP hd (truncK_pos hd).le
  have hb0 : 0 < 1 / (1 + r) := one_div_pos.2 (by linarith [h.r_pos])
  set B : Set (Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ) :=
    {f | (∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - 1 / (1 + r))) ∧ ∀ z, Monotone fun x => f (x, z)}
  set S' := B ∩ {f | ∀ z, IsConcaveS (convex_Ioi (0 : ℝ)) fun x => f (x, z)}
  have hclosed : IsClosed S' :=
    ((isClosed_bounds _).inter isClosed_monoX).inter (isClosed_concaveX _)
  have hstrict : ∀ f ∈ S', ∀ z, IsStrictConcaveS (convex_Ioi (0 : ℝ))
      fun x => truncT hd f (x, z) := by
    intro f hf z x₀ x₁ hne θ h0 h1
    obtain ⟨y₀, -, hv₀, -⟩ := trunc_bellman_argmax hd hf.1.1 (x₀, z)
    obtain ⟨y₁, -, hv₁, -⟩ := trunc_bellman_argmax hd hf.1.1 (x₁, z)
    set yθ := cmb (convex_Ioi (0 : ℝ)) h0.le h1.le y₀ y₁
    set xθ := cmb (convex_Ioi (0 : ℝ)) h0.le h1.le x₀ x₁
    have hle := ind_rhs_le h Q hQ hf.1.1 hf.1.2 (xθ, z) yθ
    dsimp only
    rw [hv₀, hv₁]
    refine lt_of_lt_of_le ?_ hle
    rw [ind_rhs, ind_rhs, ind_rhs]
    -- the return: strict concavity of `U` and convexity of the adjustment cost
    have hU := (h.U_conc z.1 z.2).2 (mem_Ici.2 (le_of_lt x₀.2)) (mem_Ici.2 (le_of_lt x₁.2))
      (fun he => hne (Subtype.ext he)) h0 (by linarith : (0 : ℝ) < 1 - θ) (by ring)
    simp only [smul_eq_mul] at hU
    have hp := h.persp_convex x₀.2 x₁.2 (le_of_lt y₀.2) (le_of_lt y₁.2) h0.le h1.le
    have hxθ : xθ.1 = θ * x₀.1 + (1 - θ) * x₁.1 := cmb_Ioi_val h0.le h1.le
    have hyθ : yθ.1 = θ * y₀.1 + (1 - θ) * y₁.1 := cmb_Ioi_val h0.le h1.le
    -- the continuation value: concavity of `f(·, z′)`
    have hE : θ * ∫ z', f (y₀, z') ∂Q z + (1 - θ) * ∫ z', f (y₁, z') ∂Q z ≤
        ∫ z', f (yθ, z') ∂Q z := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add
        ((integrable_ind (Q := Q) f y₀ z).const_mul θ)
        ((integrable_ind (Q := Q) f y₁ z).const_mul _)]
      exact integral_mono (((integrable_ind (Q := Q) f y₀ z).const_mul θ).add
        ((integrable_ind (Q := Q) f y₁ z).const_mul _)) (integrable_ind (Q := Q) f yθ z)
        fun z' => hf.2 z' y₀ y₁ θ h0.le h1.le
    simp only [indF]
    rw [hxθ, hyθ]
    nlinarith [mul_le_mul_of_nonneg_left hE hb0.le]
  have hmaps : MapsTo (truncT hd) S' S' := fun f hf =>
    ⟨⟨truncT_mapsTo hd hf.1.1, fun z => (ind_T_strictMono_x h Q hQ hf.1.1 hf.1.2 z).monotone⟩,
      fun z => (hstrict f hf z).isConcaveS⟩
  have hv' := (corollary_1 (S' := S') (S'' := S') (bellman_contraction _ hb) hv
    ⟨0, ⟨fun _ => ⟨le_rfl, div_nonneg hd.A_nonneg (by linarith [hd.β_lt])⟩,
      fun _ _ _ _ => le_rfl⟩, fun _ _ _ _ _ _ => by simp⟩ hclosed hmaps hmaps).1
  have := hstrict v hv' z
  rwa [hv] at this

/-- The objective of (2′) is continuous on the graph of `Γ`. -/
theorem ind_continuousOn_objG (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (f : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ) :
    ContinuousOn (objG (indModel Q U c δ' M r) f) (graph (indΓ δ' M)) := by
  have hd := h.upperDP Q hQ
  set MM := indModel Q U c δ' M r
  have hF : ContinuousOn (fun p : (Ioi (0 : ℝ) × Icc z₁ z₂) × Ioi (0 : ℝ) =>
      MM.F (p.1.1, p.2, p.1.2)) (graph MM.Γ) :=
    (h.continuous_F.comp (continuous_fst.fst.prodMk
      (continuous_snd.prodMk continuous_fst.snd))).continuousOn
  have hE : ContinuousOn (fun p : (Ioi (0 : ℝ) × Icc z₁ z₂) × Ioi (0 : ℝ) =>
      expV MM f p.1 p.2) (graph MM.Γ) :=
    (hd.contExp f f.continuous ⟨‖f‖, fun p => f.norm_coe_le_norm p⟩).comp
      ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd).continuousOn
      fun p hp => ⟨mem_domD MM hp, mem_univ _⟩
  exact hF.add (continuousOn_const.mul hE)

/-- At the fixed point the maximum of (2′) is attained and equals `v`. -/
theorem ind_max (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) (s : Ioi (0 : ℝ) × Icc z₁ z₂) :
    (∃ y ∈ indΓ δ' M s, v s = rhs (indModel Q U c δ' M r) v s y) ∧
      (∀ y ∈ indΓ δ' M s, rhs (indModel Q U c δ' M r) v s y ≤ v s) ∧
      maxValue (objG (indModel Q U c δ' M r) v) (indΓ δ' M) s = v s := by
  obtain ⟨y, hy, hval, hmax⟩ := trunc_bellman_argmax (h.upperDP Q hQ)
    (ind_strictMono_x h Q hQ hv).1 s
  rw [hv] at hval hmax
  refine ⟨⟨y, hy, hval⟩, hmax, ?_⟩
  exact IsGreatest.csSup_eq ⟨⟨y, hy, hval.symm⟩, by rintro _ ⟨y', hy', rfl⟩; exact hmax y' hy'⟩

/-- **Exercise 10.4c** (the policy function). The maximizer in (2′) is unique; it is a continuous
function `g`, and `(1 − δ)x ≤ g(x, z) < max{M, x}`, so `g(x, z)` is interior to `Γ(x)`. -/
theorem ind_policy (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) :
    UniqueArgmax (indΓ δ' M) (objG (indModel Q U c δ' M r) v) ∧
      (∀ s, policy (indModel Q U c δ' M r) v s = argmax (objG (indModel Q U c δ' M r) v)
        (indΓ δ' M) s) ∧
      ∀ s, ∀ y ∈ policy (indModel Q U c δ' M r) v s,
        (1 - δ) * s.1.1 ≤ y.1 ∧ y.1 < max M s.1.1 := by
  have hd := h.upperDP Q hQ
  have hb0 : 0 < 1 / (1 + r) := one_div_pos.2 (by linarith [h.r_pos])
  have hvR := (ind_strictMono_x h Q hQ hv).1
  have hvm := (ind_strictMono_x h Q hQ hv).2
  have hpol : ∀ s, policy (indModel Q U c δ' M r) v s =
      argmax (objG (indModel Q U c δ' M r) v) (indΓ δ' M) s := fun s => by
    ext y
    change y ∈ indΓ δ' M s ∧ v s = rhs _ v s y ↔ y ∈ indΓ δ' M s ∧ objG _ v (s, y) = _
    rw [(ind_max h Q hQ hv s).2.2, eq_comm]
    rfl
  refine ⟨⟨hd.nonempty, hd.compact, hd.lhc, hd.uhc, ind_continuousOn_objG h Q hQ v,
    fun s y₁ hy₁ y₂ hy₂ => ?_⟩, hpol, fun s y hy => ⟨?_, ?_⟩⟩
  · -- uniqueness: at the midpoint the return is at least the average and the continuation
    -- value strictly more
    obtain ⟨x, z⟩ := s
    by_contra hne
    have hx : 0 < x.1 := x.2
    have hh0 : (0 : ℝ) < 1 / 2 := by norm_num
    have hh1 : (1 / 2 : ℝ) < 1 := by norm_num
    set ym := cmb (convex_Ioi (0 : ℝ)) hh0.le hh1.le y₁ y₂
    have hymv : ym.1 = 1 / 2 * y₁.1 + (1 - 1 / 2) * y₂.1 := cmb_Ioi_val hh0.le hh1.le
    have hym : ym ∈ indΓ δ' M (x, z) := by
      have h1 := hy₁.1; have h2 := hy₂.1
      exact ⟨by rw [hymv]; linarith [h1.1, h2.1], by rw [hymv]; linarith [h1.2, h2.2]⟩
    have hle := (ind_max h Q hQ hv (x, z)).2.1 ym hym
    have e1 : rhs (indModel Q U c δ' M r) v (x, z) y₁ = v (x, z) := by
      rw [← (ind_max h Q hQ hv (x, z)).2.2]; exact hy₁.2
    have e2 : rhs (indModel Q U c δ' M r) v (x, z) y₂ = v (x, z) := by
      rw [← (ind_max h Q hQ hv (x, z)).2.2]; exact hy₂.2
    rw [ind_rhs] at hle e1 e2
    have hc := h.c_conv.2 (mem_Ici.2 (div_nonneg (le_of_lt y₁.2) hx.le))
      (mem_Ici.2 (div_nonneg (le_of_lt y₂.2) hx.le)) hh0.le hh0.le (by norm_num)
    simp only [smul_eq_mul] at hc
    have hcm : ym.1 / x.1 = 1 / 2 * (y₁.1 / x.1) + 1 / 2 * (y₂.1 / x.1) := by
      rw [hymv]; field_simp; ring
    have hE : 1 / 2 * ∫ z', v (y₁, z') ∂Q z + (1 - 1 / 2) * ∫ z', v (y₂, z') ∂Q z <
        ∫ z', v (ym, z') ∂Q z := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add
        ((integrable_ind (Q := Q) v y₁ z).const_mul _)
        ((integrable_ind (Q := Q) v y₂ z).const_mul _)]
      exact integral_lt_integral_of_lt (((integrable_ind (Q := Q) v y₁ z).const_mul _).add
        ((integrable_ind (Q := Q) v y₂ z).const_mul _)) (integrable_ind (Q := Q) v ym z)
        fun z' => ind_strictConcave h Q hQ hv z' y₁ y₂ hne (1 / 2) hh0 hh1
    simp only [indF] at hle e1 e2
    rw [hcm] at hle
    nlinarith [mul_lt_mul_of_pos_left hE hb0, mul_le_mul_of_nonneg_left hc hx.le]
  · -- below `(1 − δ)x` the cost is zero and `(1 − δ)x` is strictly better
    obtain ⟨x, z⟩ := s
    by_contra hlt
    rw [not_le] at hlt
    have hx : 0 < x.1 := x.2
    obtain ⟨hsm, hsF⟩ := h.safe_mem x z
    have hle := (ind_max h Q hQ hv (x, z)).2.1 _ hsm
    have hyv := hy.2
    rw [ind_rhs] at hle hyv
    have hc0 : c (y.1 / x.1) = 0 := h.c_zero _ (div_nonneg (le_of_lt y.2) hx.le) (by
      rw [div_le_iff₀ hx]; linarith)
    have hF : indF U c (x, y, z) = U x.1 z.1 := by simp only [indF, hc0, mul_zero, sub_zero]
    rw [hF] at hyv
    rw [hsF] at hle
    have hE : ∫ z', v (y, z') ∂Q z < ∫ z', v (h.safeY x, z') ∂Q z :=
      integral_lt_integral_of_lt (integrable_ind (Q := Q) v y z)
        (integrable_ind (Q := Q) v _ z) fun z' => hvm z' (show y.1 < (1 - δ) * x.1 from hlt)
    nlinarith [mul_lt_mul_of_pos_left hE hb0]
  · -- at `max{M, x}` the value is negative
    by_contra hge
    rw [not_lt] at hge
    have hneg := ind_rhs_neg h Q hvR s hge
    have hyv := hy.2
    have := (hvR s).1
    linarith

/-- **Exercise 10.4c** (differentiability, Benveniste–Scheinkman). If `y₀` is optimal at
`(x₀, z₀)`, `U(·, z₀)` has derivative `U_x` at `x₀` and `c` has derivative `c′` at `a = y₀/x₀`,
then `v_x(x₀, z₀) = U_x − c(a) + a c′(a)`. -/
theorem ind_hasDerivAt_x (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    {x₀ y₀ : Ioi (0 : ℝ)} {z₀ : Icc z₁ z₂}
    (hy₀ : y₀ ∈ policy (indModel Q U c δ' M r) v (x₀, z₀)) {Ux c' : ℝ}
    (hUx : HasDerivAt (fun q => U q z₀.1) Ux x₀.1) (hc' : HasDerivAt c c' (y₀.1 / x₀.1)) :
    HasDerivAt (liftS fun x => v (x, z₀)) (Ux - c (y₀.1 / x₀.1) + y₀.1 / x₀.1 * c') x₀.1 := by
  have hx₀ : 0 < x₀.1 := x₀.2
  have hvR := (ind_strictMono_x h Q hQ hv).1
  have hvm := (ind_strictMono_x h Q hQ hv).2
  set E := ∫ z', v (y₀, z') ∂Q z₀
  have hin : HasDerivAt (fun x => y₀.1 / x) (-(y₀.1 / x₀.1 ^ 2)) x₀.1 := by
    have := (hasDerivAt_inv hx₀.ne').const_mul y₀.1
    simp only [div_eq_mul_inv] at this ⊢
    convert this using 1; ring
  have hcost : HasDerivAt (fun x => x * c (y₀.1 / x))
      (c (y₀.1 / x₀.1) - y₀.1 / x₀.1 * c') x₀.1 := by
    refine ((hasDerivAt_id x₀.1).mul (hc'.comp x₀.1 hin)).congr_deriv ?_
    simp only [id, Function.comp_apply]
    field_simp
    ring
  have hL : HasDerivAt (fun x => U x z₀.1 - x * c (y₀.1 / x) + 1 / (1 + r) * E)
      (Ux - c (y₀.1 / x₀.1) + y₀.1 / x₀.1 * c') x₀.1 := by
    have := (hUx.sub hcost).add_const (1 / (1 + r) * E)
    convert this using 1; ring
  refine hasDerivAt_of_concaveOn_of_le (concaveOn_liftS (ind_strictConcave h Q hQ hv z₀).isConcaveS)
    (Ioi_mem_nhds hx₀) hL ?_ ?_
  · rw [liftS_of_mem _ x₀.2, hy₀.2, ind_rhs]
    rfl
  · filter_upwards [Ioi_mem_nhds hx₀] with x hx
    rw [liftS_of_mem _ hx]
    have := ind_rhs_le h Q hQ hvR (fun z => (hvm z).monotone) (⟨x, hx⟩, z₀) y₀
    rw [hv, ind_rhs] at this
    exact this

/-- **Exercise 10.4c**, bundled: `v` is strictly increasing in `x` and, when `Q` is monotone, in
`z`; strictly concave in `x`; the maximizer is unique, with `(1 − δ)x ≤ g(x, z) < max{M, x}`;
and `v_x = U_x − c(g/x) + (g/x)c′(g/x)` wherever `U(·, z)` and `c` are differentiable. -/
theorem ex_10_4c (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) :
    (∀ z, StrictMono fun x => v (x, z)) ∧
      (IsMonotoneTF Q → ∀ x, StrictMono fun z => v (x, z)) ∧
      (∀ z, IsStrictConcaveS (convex_Ioi (0 : ℝ)) fun x => v (x, z)) ∧
      UniqueArgmax (indΓ δ' M) (objG (indModel Q U c δ' M r) v) ∧
      (∀ s, ∀ y ∈ policy (indModel Q U c δ' M r) v s,
        (1 - δ) * s.1.1 ≤ y.1 ∧ y.1 < max M s.1.1) ∧
      ∀ (x₀ y₀ : Ioi (0 : ℝ)) (z₀ : Icc z₁ z₂) (Ux c' : ℝ),
        y₀ ∈ policy (indModel Q U c δ' M r) v (x₀, z₀) →
        HasDerivAt (fun q => U q z₀.1) Ux x₀.1 → HasDerivAt c c' (y₀.1 / x₀.1) →
        HasDerivAt (liftS fun x => v (x, z₀)) (Ux - c (y₀.1 / x₀.1) + y₀.1 / x₀.1 * c') x₀.1 :=
  ⟨(ind_strictMono_x h Q hQ hv).2, fun hQm => ind_strictMono_z h Q hQ hQm hv,
    ind_strictConcave h Q hQ hv, (ind_policy h Q hQ hv).1, (ind_policy h Q hQ hv).2.2,
    fun _ _ _ _ _ hy hUx hc' => ind_hasDerivAt_x h Q hQ hv hy hUx hc'⟩

/-- Membership in the policy correspondence: `y` is optimal iff it is feasible and no feasible
`y′` does better. -/
theorem ind_mem_policy_iff (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    (s : Ioi (0 : ℝ) × Icc z₁ z₂) (y : Ioi (0 : ℝ)) :
    y ∈ policy (indModel Q U c δ' M r) v s ↔ y ∈ indΓ δ' M s ∧
      ∀ y' ∈ indΓ δ' M s, rhs (indModel Q U c δ' M r) v s y' ≤
        rhs (indModel Q U c δ' M r) v s y := by
  obtain ⟨⟨y₀, hy₀, hval⟩, hmax, -⟩ := ind_max h Q hQ hv s
  constructor
  · rintro ⟨hy, hyv⟩
    exact ⟨hy, fun y' hy' => (hmax y' hy').trans_eq hyv⟩
  · rintro ⟨hy, hge⟩
    exact ⟨hy, le_antisymm (hval.trans_le (hge y₀ hy₀)) (hmax y hy)⟩

/-- **Exercise 10.4f**. If the shocks are i.i.d. (`Q(z, ·)` does not depend on `z`), the
investment policy does not depend on `z`: `g(x, z) = g(x, z′)`. The current shock enters the
return only through the additive term `U(x, z)`, which does not move the maximizer. -/
theorem ex_10_4f (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) (hiid : ∀ z z', Q z = Q z')
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    (x : Ioi (0 : ℝ)) (z z' : Icc z₁ z₂) :
    policy (indModel Q U c δ' M r) v (x, z) = policy (indModel Q U c δ' M r) v (x, z') := by
  ext y
  rw [ind_mem_policy_iff h Q hQ hv, ind_mem_policy_iff h Q hQ hv]
  have hΓ : indΓ δ' M (x, z) = indΓ δ' M (x, z') := rfl
  have key : ∀ y' : Ioi (0 : ℝ), rhs (indModel Q U c δ' M r) v (x, z) y' =
      rhs (indModel Q U c δ' M r) v (x, z') y' + (U x.1 z.1 - U x.1 z'.1) := fun y' => by
    rw [ind_rhs, ind_rhs]
    change U x.1 z.1 - x.1 * c (y'.1 / x.1) + 1 / (1 + r) * ∫ z'', v (y', z'') ∂Q z =
      U x.1 z'.1 - x.1 * c (y'.1 / x.1) + 1 / (1 + r) * ∫ z'', v (y', z'') ∂Q z' +
        (U x.1 z.1 - U x.1 z'.1)
    rw [hiid z z']
    ring
  rw [hΓ]
  simp only [key, add_le_add_iff_right]

/-- The cost `x c(y/x)` has decreasing differences: for `0 < x ≤ x′` and `0 < y′ < y`,
`x′[c(y/x′) − c(y′/x′)] ≤ x[c(y/x) − c(y′/x)]`. Both sides are `(y − y′)` times a secant slope
of the convex `c`, and the slope over `[y′/x′, y/x′]` is below the one over `[y′/x, y/x]`. -/
theorem ind_cost_submod (h : IndHyp U c δ δ' M r A z₁ z₂) {x x' y y' : ℝ} (hx : 0 < x)
    (hxx : x ≤ x') (hy' : 0 < y') (hyy : y' < y) :
    x' * (c (y / x') - c (y' / x')) ≤ x * (c (y / x) - c (y' / x)) := by
  have hx' : 0 < x' := hx.trans_le hxx
  have hd : 0 < y - y' := by linarith
  have ha : y' / x' < y / x' := div_lt_div_of_pos_right hyy hx'
  have hb : y / x' ≤ y / x := div_le_div_of_nonneg_left (by linarith) hx hxx
  have ha' : y' / x' ≤ y' / x := div_le_div_of_nonneg_left hy'.le hx hxx
  have hab' : y' / x < y / x := div_lt_div_of_pos_right hyy hx
  have m0 : ∀ q : ℝ, 0 < q → q ∈ Ici (0 : ℝ) := fun q hq => mem_Ici.2 hq.le
  have p1 := h.c_conv.secant_mono (m0 _ (div_pos hy' hx')) (m0 _ (div_pos (hy'.trans hyy) hx'))
    (m0 _ (div_pos (hy'.trans hyy) hx)) ha.ne' (ha.trans_le hb).ne' hb
  have p2 := h.c_conv.secant_mono (m0 _ (div_pos (hy'.trans hyy) hx)) (m0 _ (div_pos hy' hx'))
    (m0 _ (div_pos hy' hx)) (ha.trans_le hb).ne (hab'.ne) ha'
  have e1 : x' * (c (y / x') - c (y' / x')) =
      (y - y') * ((c (y / x') - c (y' / x')) / (y / x' - y' / x')) := by
    rw [show y / x' - y' / x' = (y - y') / x' by ring]
    field_simp
  have e2 : x * (c (y / x) - c (y' / x)) =
      (y - y') * ((c (y' / x) - c (y / x)) / (y' / x - y / x)) := by
    rw [show y' / x - y / x = -((y - y') / x) by ring, div_neg, ← neg_div, neg_sub]
    field_simp
  have e3 : (c (y / x) - c (y' / x')) / (y / x - y' / x') =
      (c (y' / x') - c (y / x)) / (y' / x' - y / x) := by
    rw [← neg_div_neg_eq, neg_sub, neg_sub]
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (p1.trans (e3 ▸ p2)) hd.le

/-- **Exercise 10.4d** (monotonicity in `x`). Investment is nondecreasing in capacity:
`x ≤ x′` implies `g(x, z) ≤ g(x′, z)`. The proof is Topkis's: `Γ` is ascending, and the
cost `x c(y/x)` has decreasing differences (`ind_cost_submod`), so if `g(x′, z) < g(x, z)` then
`g(x, z)` is also optimal at `x′`, contradicting uniqueness. -/
theorem ex_10_4d (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) {x x' y y' : Ioi (0 : ℝ)} (hxx : x.1 ≤ x'.1)
    (z : Icc z₁ z₂) (hy : y ∈ policy (indModel Q U c δ' M r) v (x, z))
    (hy' : y' ∈ policy (indModel Q U c δ' M r) v (x', z)) : y.1 ≤ y'.1 := by
  by_contra hlt
  rw [not_le] at hlt
  have hx : 0 < x.1 := x.2
  have hy'0 : 0 < y'.1 := y'.2
  have hδ : 0 ≤ 1 - δ' := by linarith [h.δ'_lt]
  have key : ∀ (s : Ioi (0 : ℝ) × Icc z₁ z₂) (w : Ioi (0 : ℝ)),
      rhs (indModel Q U c δ' M r) v s w =
        U s.1.1 s.2.1 - s.1.1 * c (w.1 / s.1.1) + 1 / (1 + r) * ∫ z', v (w, z') ∂Q s.2 :=
    fun _ _ => rfl
  have hyΓ : y ∈ indΓ δ' M (x', z) := by
    have h1 := hy'.1; have h2 := hy.1
    exact ⟨h1.1.trans hlt.le, h2.2.trans (max_le_max le_rfl hxx)⟩
  have hy'Γ : y' ∈ indΓ δ' M (x, z) := by
    have h1 := hy'.1; have h2 := hy.1
    exact ⟨(mul_le_mul_of_nonneg_left hxx hδ).trans h1.1, hlt.le.trans h2.2⟩
  have h0 := ((ind_mem_policy_iff h Q hQ hv _ _).1 hy).2 y' hy'Γ
  have hsub := ind_cost_submod h hx hxx hy'0 hlt
  rw [key, key] at h0
  have hopt : y ∈ policy (indModel Q U c δ' M r) v (x', z) := by
    refine (ind_mem_policy_iff h Q hQ hv _ _).2 ⟨hyΓ, fun w hw => ?_⟩
    refine (((ind_mem_policy_iff h Q hQ hv _ _).1 hy').2 w hw).trans ?_
    rw [key, key]
    change U x'.1 z.1 - x'.1 * c (y'.1 / x'.1) + 1 / (1 + r) * ∫ z', v (y', z') ∂Q z ≤
      U x'.1 z.1 - x'.1 * c (y.1 / x'.1) + 1 / (1 + r) * ∫ z', v (y, z') ∂Q z
    change U x.1 z.1 - x.1 * c (y'.1 / x.1) + 1 / (1 + r) * ∫ z', v (y', z') ∂Q z ≤
      U x.1 z.1 - x.1 * c (y.1 / x.1) + 1 / (1 + r) * ∫ z', v (y, z') ∂Q z at h0
    linarith
  have hpol := (ind_policy h Q hQ hv).2.1
  have := (ind_policy h Q hQ hv).1.unique (x', z) y (hpol (x', z) ▸ hopt) y'
    (hpol (x', z) ▸ hy')
  rw [this] at hlt
  exact lt_irrefl _ hlt

/-- **Exercise 10.4f** (capacity paths). Under i.i.d. shocks, any optimal path
`x_{t+1} ∈ g(x_t, z_t)` is monotone, whatever the shock realizations: nonincreasing if
`x₁ ≤ x₀` and nondecreasing if `x₀ ≤ x₁`. -/
theorem ex_10_4f_monotone (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hiid : ∀ z z', Q z = Q z') {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) (xs : ℕ → Ioi (0 : ℝ)) (zs : ℕ → Icc z₁ z₂)
    (hseq : ∀ t, xs (t + 1) ∈ policy (indModel Q U c δ' M r) v (xs t, zs t)) :
    ((xs 1).1 ≤ (xs 0).1 → Antitone fun t => (xs t).1) ∧
      ((xs 0).1 ≤ (xs 1).1 → Monotone fun t => (xs t).1) := by
  have hmove : ∀ t, xs (t + 1) ∈ policy (indModel Q U c δ' M r) v (xs t, zs (t + 1)) :=
    fun t => ex_10_4f h Q hQ hiid hv (xs t) (zs t) (zs (t + 1)) ▸ hseq t
  constructor
  · intro h10
    have : ∀ t, (xs (t + 1)).1 ≤ (xs t).1 := by
      intro t
      induction t with
      | zero => exact h10
      | succ t ih => exact ex_10_4d h Q hQ hv ih (zs (t + 1)) (hseq (t + 1)) (hmove t)
    exact antitone_nat_of_succ_le this
  · intro h01
    have : ∀ t, (xs t).1 ≤ (xs (t + 1)).1 := by
      intro t
      induction t with
      | zero => exact h01
      | succ t ih => exact ex_10_4d h Q hQ hv ih (zs (t + 1)) (hmove t) (hseq (t + 1))
    exact monotone_nat_of_le_succ this

/-- **Exercise 10.4f** (convergence). Under i.i.d. shocks every optimal capacity path converges:
it is monotone (`ex_10_4f_monotone`), bounded below by `0`, and bounded above by `max{M, x₀}`
because `g(x, z) < max{M, x}`. -/
theorem ex_10_4f_tendsto (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hiid : ∀ z z', Q z = Q z') {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) (xs : ℕ → Ioi (0 : ℝ)) (zs : ℕ → Icc z₁ z₂)
    (hseq : ∀ t, xs (t + 1) ∈ policy (indModel Q U c δ' M r) v (xs t, zs t)) :
    ∃ L, Tendsto (fun t => (xs t).1) atTop (𝓝 L) := by
  obtain ⟨hanti, hmono⟩ := ex_10_4f_monotone h Q hQ hiid hv xs zs hseq
  have hup : ∀ t, (xs t).1 ≤ max M (xs 0).1 := by
    intro t
    induction t with
    | zero => exact le_max_right _ _
    | succ t ih =>
      have := ((ind_policy h Q hQ hv).2.2 _ _ (hseq t)).2
      exact (this.trans_le (max_le (le_max_left _ _) ih)).le
  rcases le_total (xs 1).1 (xs 0).1 with h10 | h01
  · exact ⟨_, tendsto_atTop_ciInf (hanti h10) ⟨0, by rintro _ ⟨t, rfl⟩; exact (xs t).2.le⟩⟩
  · exact ⟨_, tendsto_atTop_ciSup (hmono h01) ⟨_, by rintro _ ⟨t, rfl⟩; exact hup t⟩⟩

end StokeyLucasPrescott.StochasticApplications
