/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.AAGradients
import RecursiveUtility.AASmoothAmbiguity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Pricing kernels: Examples 20.3.1–20.3.3 and Exercise 20.2

Miao, §20.3.3, pp. 709–710, and Exercise 20.2 (p. 735).

* **Example 20.3.1** (Epstein–Zin): the partial derivatives of the CES aggregator
  `W₁ = (1 − β)c^{−ρ}W^ρ`, `W₂ = βy^{−ρ}W^ρ` (`aa_W_hasFDerivAt`), the derivative of the
  Kreps–Porteus certainty equivalent `κ_s = (x_s/M)^{−γ}` (`aa_KP_hasCEDeriv`), the algebra of
  (20.20) (`eq_20_20`), and on the event tree: the hypotheses of Proposition 20.3.2 hold and the
  pricing kernel is `β(c_{t+1}/c_t)^{−ρ}(U_{t+1}/M_t(U_{t+1}))^{ρ−γ}` (`example_20_3_1`); for
  `γ > ρ` it is decreasing in the continuation value (`aa_ez_kernel_antitone`).
* **Example 20.3.2** (generalized smooth ambiguity): the derivative of (20.15) with respect to the
  joint measure `μ(z)π_z(s)`, `κ_{z,s} = (x_s/M)^{−γ}(Y_z/M)^{−(η−γ)}`,
  `Y_z = (E_{π_z} x^{1−γ})^{1/(1−γ)}` (`aa_ju_hasFDerivAt`), and the kernel
  `M_{z,t+1} = β(c'/c)^{−ρ}(U'/M)^{ρ−γ}(Y_z/M)^{−(η−γ)}` (`example_20_3_2`), decreasing in `Y_z`
  for `η > γ` (`aa_smooth_kernel_antitone`).
* **Example 20.3.3** (recursive multiple priors): for concave `u` with supergradient `u'` and any
  selection of minimising priors `q*`, `π_t = β^t u'(c_t)M*_t` with `M*` the product of the
  densities `m* = dq*/dp` is a utility supergradient (`example_20_3_3`); such a selection exists for
  finite sets of priors (`example_20_3_3_exists`). The book prints `π_t = u'(c_t)m*_t`: the
  discount factor and the cumulated density are implicit. Not formalised: the reverse inclusion
  (every supergradient is of this form), which the text cites from Epstein and Wang (1994).
* **Exercise 20.2**: Epstein–Zin (`example_20_3_1`), divergence utility — in the multiplier
  (relative entropy) case the aggregator `R = −θ ln E exp(−x/θ)` has derivative `κ = m*`, the
  minimising density (`aa_riskSensitive_hasCEDeriv`, `aa_klDensity_attains`), so the kernel is
  `βu'(c_{t+1})/u'(c_t) · m*_{t+1}` (`ex_20_2_divergence`); for a general divergence the
  minimising density is a supergradient of `R` (`aa_divR_supergradient`) — and generalized smooth
  ambiguity (`example_20_3_2`).
-/

namespace Miao.RecursiveUtility

open Finset Filter Topology

variable {S Z : Type*} [Fintype S] [Fintype Z]

/-! ### Example 20.3.1: Epstein–Zin -/

/-- The partial derivatives of the CES aggregator at `(c, y) ∈ (0, ∞)²`:
`W₁ = (1 − β)c^{−ρ}W^ρ`, `W₂ = βy^{−ρ}W^ρ`. -/
theorem aa_W_hasFDerivAt {β ρ c y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hc : 0 < c)
    (hy : 0 < y) :
    HasFDerivAt (fun z : ℝ × ℝ => aa_W β ρ z.1 z.2)
      (((1 - β) * c ^ (-ρ) * aa_W β ρ c y ^ ρ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (β * y ^ (-ρ) * aa_W β ρ c y ^ ρ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (c, y) := by
  have hr : 1 - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hb : 0 < 1 - β := by linarith
  set A := (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) with hA
  have hA0 : 0 < A := add_pos (mul_pos hb (Real.rpow_pos_of_pos hc _))
    (mul_pos hβ0 (Real.rpow_pos_of_pos hy _))
  have h1 : HasFDerivAt (fun z : ℝ × ℝ => z.1 ^ (1 - ρ))
      (((1 - ρ) * c ^ (1 - ρ - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ) (c, y) :=
    (hasFDerivAt_fst (p := (c, y))).rpow_const (Or.inl hc.ne')
  have h2 : HasFDerivAt (fun z : ℝ × ℝ => z.2 ^ (1 - ρ))
      (((1 - ρ) * y ^ (1 - ρ - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (c, y) :=
    (hasFDerivAt_snd (p := (c, y))).rpow_const (Or.inl hy.ne')
  have hW := ((h1.const_mul (1 - β)).add (h2.const_mul β)).rpow_const (p := (1 - ρ)⁻¹)
    (Or.inl hA0.ne')
  have e1 : A ^ ((1 - ρ)⁻¹ - 1) = aa_W β ρ c y ^ ρ := by
    rw [aa_W, ← hA, ← Real.rpow_mul hA0.le]
    congr 1
    field_simp
    ring
  have e2 : ∀ t : ℝ, 0 < t → t ^ (1 - ρ - 1) = t ^ (-ρ) := fun t _ => by congr 1; ring
  refine hW.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Pi.add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [← hA, e1, e2 c hc, e2 y hy]
  field_simp

/-- **Example 20.3.1**, the certainty equivalent: the Kreps–Porteus `M(x) = (E x^{1−γ})^{1/(1−γ)}`
has derivative `κ_s = (x_s/M(x))^{−γ}` at a positive `x`. -/
theorem aa_KP_hasCEDeriv [Nonempty S] {γ : ℝ} (hγ : γ ≠ 1) {p : S → ℝ}
    (hp : SS.IsDistribution p) {x : S → ℝ} (hx : ∀ s, 0 < x s) :
    aa_HasCEDeriv (aa_KP γ p) p (fun s => (x s / aa_KP γ p x) ^ (-γ)) x := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  set B := aa_E p fun s => x s ^ (1 - γ) with hB
  have hB0 : 0 < B := aa_E_pos hp fun s => Real.rpow_pos_of_pos (hx s) _
  have hin : HasFDerivAt (fun y : S → ℝ => aa_E p fun s => y s ^ (1 - γ))
      (∑ s, p s • (((1 - γ) * x s ^ (1 - γ - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s)) x :=
    HasFDerivAt.fun_sum fun s _ =>
      ((hasFDerivAt_apply s x).rpow_const (Or.inl (hx s).ne')).const_mul (p s)
  have hW := hin.rpow_const (p := (1 - γ)⁻¹) (Or.inl hB0.ne')
  have hK : aa_KP γ p x = B ^ (1 - γ)⁻¹ := rfl
  have hK0 : 0 < aa_KP γ p x := aa_KP_pos γ hp hx
  unfold aa_HasCEDeriv
  refine hW.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [_root_.smul_apply, smul_eq_mul, _root_.sum_apply,
    ContinuousLinearMap.proj_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.div_rpow (hx s).le hK0.le, Real.rpow_neg hK0.le, hK, ← Real.rpow_mul hB0.le,
    show 1 - γ - 1 = -γ by ring]
  have e : B ^ ((1 - γ)⁻¹ - 1) = B ^ ((1 - γ)⁻¹ * γ) := by congr 1; field_simp; ring
  rw [e]
  have h1 := Real.rpow_pos_of_pos hB0 ((1 - γ)⁻¹ * γ)
  field_simp

/-- **(20.20)** (Miao, p. 709), the algebra: with `λ_t = (1 − β)c_t^{−ρ}U_t^ρ`,
`W₂ = βM^{−ρ}U_t^ρ` and `κ = (U_{t+1}/M)^{−γ}`,
`(λ_{t+1}/λ_t)W₂κ = β(c_{t+1}/c_t)^{−ρ}(U_{t+1}/M)^{ρ−γ}`. -/
theorem eq_20_20 {β ρ γ c c' U U' M : ℝ} (hβ1 : β < 1) (hc : 0 < c) (hc' : 0 < c') (hU : 0 < U)
    (hU' : 0 < U') (hM : 0 < M) :
    (1 - β) * c' ^ (-ρ) * U' ^ ρ / ((1 - β) * c ^ (-ρ) * U ^ ρ) * (β * M ^ (-ρ) * U ^ ρ) *
        (U' / M) ^ (-γ) = β * (c' / c) ^ (-ρ) * (U' / M) ^ (ρ - γ) := by
  have hb : 1 - β ≠ 0 := by linarith
  rw [Real.rpow_sub (div_pos hU' hM)]
  simp only [Real.div_rpow hc'.le hc.le, Real.div_rpow hU'.le hM.le, Real.rpow_neg hM.le,
    Real.rpow_neg hU'.le, Real.rpow_neg hc.le, Real.rpow_neg hc'.le]
  have h1 := Real.rpow_pos_of_pos hc ρ
  have h1' := Real.rpow_pos_of_pos hc' ρ
  have h2 := Real.rpow_pos_of_pos hU ρ
  have h3 := Real.rpow_pos_of_pos hM ρ
  have h4 := Real.rpow_pos_of_pos hM γ
  have h5 := Real.rpow_pos_of_pos hU' γ
  have h6 := Real.rpow_pos_of_pos hU' ρ
  field_simp

/-- The Epstein–Zin certainty equivalent at the node `h` of the horizon-`N` tree. -/
noncomputable def aa_ezMh (β ρ γ : ℝ) (p : List S → S → ℝ) (c : List S → ℝ) (N : ℕ)
    (h : List S) : ℝ :=
  aa_KP γ (p h) fun s => aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c (N - h.length - 1) (s :: h)

/-- `λ_t = W₁(c_t, M_t)` for Epstein–Zin. -/
noncomputable def aa_ezW₁ (β ρ γ : ℝ) (p : List S → S → ℝ) (c : List S → ℝ) (N : ℕ)
    (h : List S) : ℝ :=
  (1 - β) * c h ^ (-ρ) * aa_W β ρ (c h) (aa_ezMh β ρ γ p c N h) ^ ρ

/-- `W₂(c_t, M_t)` for Epstein–Zin. -/
noncomputable def aa_ezW₂ (β ρ γ : ℝ) (p : List S → S → ℝ) (c : List S → ℝ) (N : ℕ)
    (h : List S) : ℝ :=
  β * aa_ezMh β ρ γ p c N h ^ (-ρ) * aa_W β ρ (c h) (aa_ezMh β ρ γ p c N h) ^ ρ

/-- `κ_{t+1} = (U_{t+1}/M_t)^{−γ}` for Epstein–Zin. -/
noncomputable def aa_ezκ (β ρ γ : ℝ) (p : List S → S → ℝ) (c : List S → ℝ) (N : ℕ)
    (h : List S) (s : S) : ℝ :=
  (aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c (N - h.length - 1) (s :: h) /
    aa_ezMh β ρ γ p c N h) ^ (-γ)

omit [Fintype S] in
theorem aa_M_pos {m : List S → S → ℝ} (hm : ∀ h s, 0 < m h s) : ∀ h, 0 < aa_M m h
  | [] => one_pos
  | s :: h => mul_pos (hm h s) (aa_M_pos hm h)

/-- **Example 20.3.1** (Miao, p. 709). For the finite-horizon Epstein–Zin utility (20.3) and a
positive plan, the hypotheses of Proposition 20.3.2 hold with `W₁, W₂, κ` as above, so
`π = ℰλ` is the utility gradient, and the pricing kernel is (20.20):
`π_{t+1}/π_t = β(c_{t+1}/c_t)^{−ρ}(U_{t+1}/M_t(U_{t+1}))^{ρ−γ}`. -/
theorem example_20_3_1 [Nonempty S] {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1)
    (hγ : γ ≠ 1) {p : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h)) {c : List S → ℝ}
    (hc : ∀ h, 0 < c h) (N : ℕ) :
    aa_GradHyp (aa_W β ρ) (fun h => aa_KP γ (p h)) p c N (aa_ezW₁ β ρ γ p c N)
        (aa_ezW₂ β ρ γ p c N) (aa_ezκ β ρ γ p c N) ∧
      ∀ (h : List S) (s : S), h.length + 1 < N →
        aa_gradπ (aa_ezW₁ β ρ γ p c N) (aa_ezW₂ β ρ γ p c N) (aa_ezκ β ρ γ p c N) N (s :: h) /
            aa_gradπ (aa_ezW₁ β ρ γ p c N) (aa_ezW₂ β ρ γ p c N) (aa_ezκ β ρ γ p c N) N h =
          β * (c (s :: h) / c h) ^ (-ρ) *
            (aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c (N - h.length - 1) (s :: h) /
              aa_ezMh β ρ γ p c N h) ^ (ρ - γ) := by
  have hU : ∀ n h, 0 < aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c n h := fun n h => by
    rw [← aa_ezU_eq_recU]; exact aa_ezU_pos hβ0 hβ1 hp hc n h
  have hMh : ∀ h, 0 < aa_ezMh β ρ γ p c N h := fun h => aa_KP_pos γ (hp h) fun s => hU _ _
  have hWp : ∀ h, 0 < aa_W β ρ (c h) (aa_ezMh β ρ γ p c N h) := fun h =>
    aa_W_pos hβ0 hβ1 (hc h) (hMh h)
  refine ⟨fun h _ => ⟨aa_W_hasFDerivAt hβ0 hβ1 hρ (hc h) (hMh h),
    aa_KP_hasCEDeriv hγ (hp h) fun s => hU _ _⟩, fun h s hlen => ?_⟩
  have hW₁ : ∀ h, 0 < aa_ezW₁ β ρ γ p c N h := fun h =>
    mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos (hc h) _))
      (Real.rpow_pos_of_pos (hWp h) _)
  have hm : ∀ h s, 0 < aa_ezW₂ β ρ γ p c N h * aa_ezκ β ρ γ p c N h s := fun h s =>
    mul_pos (mul_pos (mul_pos hβ0 (Real.rpow_pos_of_pos (hMh h) _))
      (Real.rpow_pos_of_pos (hWp h) _)) (Real.rpow_pos_of_pos (div_pos (hU _ _) (hMh h)) _)
  rw [aa_pricingKernel _ _ _ N h s hlen (aa_M_pos hm h).ne' (hW₁ h).ne']
  -- the child's utility is `W(c', M(s :: h))`
  have hchild : aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c (N - h.length - 1) (s :: h) =
      aa_W β ρ (c (s :: h)) (aa_ezMh β ρ γ p c N (s :: h)) := by
    obtain ⟨k, hk⟩ : ∃ k, N - h.length - 1 = k + 1 := ⟨N - h.length - 2, by omega⟩
    have hk2 : N - (s :: h).length - 1 = k := by simp only [List.length_cons]; omega
    rw [hk, aa_recU, aa_ezMh, hk2]
  unfold aa_ezW₁ aa_ezW₂ aa_ezκ
  rw [hchild, eq_20_20 hβ1 (hc h) (hc _) (hWp h) (hWp _) (hMh h)]

/-- Miao, pp. 709–710: when `γ > ρ` (preference for earlier resolution) the Epstein–Zin pricing
kernel puts more weight on low continuation values: it is strictly decreasing in `U_{t+1}`. -/
theorem aa_ez_kernel_antitone {β ρ γ c c' M : ℝ} (hβ : 0 < β) (hc : 0 < c) (hc' : 0 < c')
    (hM : 0 < M) (hργ : ρ < γ) :
    StrictAntiOn (fun U' => β * (c' / c) ^ (-ρ) * (U' / M) ^ (ρ - γ)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have h1 : (y / M) ^ (ρ - γ) < (x / M) ^ (ρ - γ) :=
    Real.rpow_lt_rpow_of_neg (div_pos hx' hM) (div_lt_div_of_pos_right hxy hM) (by linarith)
  have h2 : 0 < β * (c' / c) ^ (-ρ) := mul_pos hβ (Real.rpow_pos_of_pos (div_pos hc' hc) _)
  exact mul_lt_mul_of_pos_left h1 h2

/-! ### Example 20.3.2: generalized smooth ambiguity -/

/-- **Example 20.3.2**, the certainty equivalent (Miao, p. 710): the derivative of (20.15) at a
positive `x` is `h ↦ ∑_{z,s} μ(z)π_z(s)κ_{z,s}h_s` with
`κ_{z,s} = (x_s/M)^{−γ}(Y_z/M)^{−(η−γ)}`, `Y_z = (E_{π_z} x^{1−γ})^{1/(1−γ)}`. -/
theorem aa_ju_hasFDerivAt [Nonempty S] [Nonempty Z] {γ η : ℝ} (hγ : γ ≠ 1) (hη : η ≠ 1)
    {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z))
    {x : S → ℝ} (hx : ∀ s, 0 < x s) :
    HasFDerivAt (aa_ju γ η μ π)
      (∑ s, (∑ z, μ z * π z s * ((x s / aa_ju γ η μ π x) ^ (-γ) *
          (aa_KP γ (π z) x / aa_ju γ η μ π x) ^ (-(η - γ)))) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s) x := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have he : 1 - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη)
  set a := (1 - η) / (1 - γ) with ha
  set A : Z → ℝ := fun z => aa_E (π z) fun s => x s ^ (1 - γ) with hA
  have hA0 : ∀ z, 0 < A z := fun z => aa_E_pos (hπ z) fun s => Real.rpow_pos_of_pos (hx s) _
  set T := ∑ z, μ z * A z ^ a with hT
  have hT0 : 0 < T := aa_E_pos hμ fun z => Real.rpow_pos_of_pos (hA0 z) _
  have hAd : ∀ z, HasFDerivAt (fun y : S → ℝ => aa_E (π z) fun s => y s ^ (1 - γ))
      (∑ s, π z s • (((1 - γ) * x s ^ (1 - γ - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s)) x := fun z =>
    HasFDerivAt.fun_sum fun s _ =>
      ((hasFDerivAt_apply s x).rpow_const (Or.inl (hx s).ne')).const_mul (π z s)
  have hTd := HasFDerivAt.fun_sum (u := Finset.univ) fun z _ =>
    (((hAd z).rpow_const (p := a) (Or.inl (hA0 z).ne')).const_mul (μ z))
  have hMd := hTd.rpow_const (p := (1 - η)⁻¹) (Or.inl hT0.ne')
  have hMx : aa_ju γ η μ π x = T ^ (1 - η)⁻¹ := rfl
  have hM0 : 0 < aa_ju γ η μ π x := by rw [hMx]; exact Real.rpow_pos_of_pos hT0 _
  have hY : ∀ z, aa_KP γ (π z) x = A z ^ (1 - γ)⁻¹ := fun z => rfl
  refine hMd.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [_root_.smul_apply, smul_eq_mul, _root_.sum_apply,
    ContinuousLinearMap.proj_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  -- the exponent algebra
  have e1 : (x s / aa_ju γ η μ π x) ^ (-γ) = x s ^ (-γ) * aa_ju γ η μ π x ^ γ := by
    rw [Real.div_rpow (hx s).le hM0.le, Real.rpow_neg hM0.le]
    field_simp
  have e2 : (aa_KP γ (π z) x / aa_ju γ η μ π x) ^ (-(η - γ)) =
      A z ^ (a - 1) * aa_ju γ η μ π x ^ (η - γ) := by
    have hY0 : 0 < aa_KP γ (π z) x := aa_KP_pos γ (hπ z) hx
    have hk : (1 - γ)⁻¹ * (η - γ) = -(a - 1) := by rw [ha]; field_simp; ring
    rw [Real.div_rpow hY0.le hM0.le, Real.rpow_neg hY0.le, Real.rpow_neg hM0.le, hY,
      ← Real.rpow_mul (hA0 z).le, hk, Real.rpow_neg (hA0 z).le, inv_inv]
    have := Real.rpow_pos_of_pos hM0 (η - γ)
    field_simp
  have e3 : aa_ju γ η μ π x ^ γ * aa_ju γ η μ π x ^ (η - γ) = T ^ ((1 - η)⁻¹ - 1) := by
    rw [← Real.rpow_add hM0, hMx, ← Real.rpow_mul hT0.le]
    congr 1
    field_simp
    ring
  rw [e1, e2, show 1 - γ - 1 = -γ by ring]
  have hone : (1 - η)⁻¹ * a * (1 - γ) = 1 := by rw [ha]; field_simp
  calc (1 - η)⁻¹ * T ^ ((1 - η)⁻¹ - 1) *
        (μ z * (a * A z ^ (a - 1) * (π z s * ((1 - γ) * x s ^ (-γ) * v s))))
      = ((1 - η)⁻¹ * a * (1 - γ)) * T ^ ((1 - η)⁻¹ - 1) * μ z * π z s * x s ^ (-γ) *
          A z ^ (a - 1) * v s := by ring
    _ = μ z * π z s * (x s ^ (-γ) * aa_ju γ η μ π x ^ γ *
          (A z ^ (a - 1) * aa_ju γ η μ π x ^ (η - γ))) * v s := by
        rw [hone, ← e3]; ring

/-- **Example 20.3.2** (Miao, p. 710), the pricing kernel: with `λ_t = (1 − β)c_t^{−ρ}U_t^ρ`,
`W₂ = βM^{−ρ}U_t^ρ` and `κ_{z,s} = (U'/M)^{−γ}(Y_z/M)^{−(η−γ)}`,
`M_{z,t+1} = β(c'/c)^{−ρ}(U'/M)^{ρ−γ}(Y_z/M)^{−(η−γ)}`. -/
theorem example_20_3_2 {β ρ γ η c c' U U' M Y : ℝ} (hβ1 : β < 1) (hc : 0 < c) (hc' : 0 < c')
    (hU : 0 < U) (hU' : 0 < U') (hM : 0 < M) :
    (1 - β) * c' ^ (-ρ) * U' ^ ρ / ((1 - β) * c ^ (-ρ) * U ^ ρ) * (β * M ^ (-ρ) * U ^ ρ) *
        ((U' / M) ^ (-γ) * (Y / M) ^ (-(η - γ))) =
      β * (c' / c) ^ (-ρ) * (U' / M) ^ (ρ - γ) * (Y / M) ^ (-(η - γ)) := by
  rw [← mul_assoc, eq_20_20 hβ1 hc hc' hU hU' hM]

/-- Miao, p. 710: for `η > γ` (ambiguity aversion) the kernel puts more weight on models `z` with
low certainty-equivalent continuation value `Y_z`. -/
theorem aa_smooth_kernel_antitone {k M γ η : ℝ} (hk : 0 < k) (hM : 0 < M) (hγη : γ < η) :
    StrictAntiOn (fun Y => k * (Y / M) ^ (-(η - γ))) (Set.Ioi 0) := by
  intro x hx y _ hxy
  have hx' : (0 : ℝ) < x := hx
  exact mul_lt_mul_of_pos_left
    (Real.rpow_lt_rpow_of_neg (div_pos hx' hM) (div_lt_div_of_pos_right hxy hM) (by linarith)) hk

/-! ### Example 20.3.3: recursive multiple priors -/

/-- Linearity of `t`-step expectations. -/
theorem aa_Ex_smul (q : List S → S → ℝ) (a : ℝ) (f : List S → ℝ) :
    ∀ t h, aa_Ex q t (fun h' => a * f h') h = a * aa_Ex q t f h
  | 0, _ => rfl
  | t + 1, h => by
    simp only [aa_Ex, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [aa_Ex_smul q a f t (s :: h)]; ring

/-- **Example 20.3.3** (Miao, p. 710; Epstein and Wang 1994). For the recursive multiple-priors
utility (20.7) with `u` concave (`u'` a supergradient of `u`), `β ≥ 0`, a full-support reference
`p`, and a selection `q*` of priors attaining the minimum at every node, the process
`π_t = β^t u'(c_t) M*_t`, `M*_t = ∏ dq*/dp`, is a utility supergradient at `c`. -/
theorem example_20_3_3 {u u' : ℝ → ℝ} (hu : ∀ x y, u y ≤ u x + u' x * (y - x)) {β : ℝ}
    (hβ : 0 ≤ β) {P : List S → Set (S → ℝ)} (hP : ∀ h, ∀ q ∈ P h, SS.IsDistribution q)
    {p : List S → S → ℝ} (hpos : ∀ h s, 0 < p h s) (c : List S → ℝ) (N : ℕ)
    (qs : List S → S → ℝ) (hqs : ∀ h, qs h ∈ P h)
    (hmin : ∀ h : List S, h.length < N →
      aa_E (qs h) (fun s => aa_rmpU u β P c (N - h.length - 1) (s :: h)) =
        aa_maxmin (P h) (fun s => aa_rmpU u β P c (N - h.length - 1) (s :: h))) :
    aa_IsSupergradient (fun c' => aa_rmpU u β P c' N []) p N c
      (fun h => β ^ h.length * aa_M (fun h s => qs h s / p h s) h * u' (c h)) := by
  intro c'
  let g : List S → ℝ := fun h => u' (c h) * (c' h - c h)
  have key : ∀ k h, h.length + k = N →
      aa_rmpU u β P c' k h ≤ aa_rmpU u β P c k h +
        ∑ t ∈ Finset.range (k + 1), β ^ t * aa_Ex qs t g h := by
    intro k
    induction k with
    | zero =>
      intro h _
      simp only [aa_rmpU, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
        aa_Ex, g]
      exact hu _ _
    | succ k ih =>
      intro h hlen
      have hidx : N - h.length - 1 = k := by omega
      have hm := hmin h (by omega)
      rw [hidx] at hm
      simp only [aa_rmpU]
      have hD := hP h _ (hqs h)
      have h1 : aa_maxmin (P h) (fun s => aa_rmpU u β P c' k (s :: h)) ≤
          aa_E (qs h) fun s => aa_rmpU u β P c k (s :: h) +
            ∑ t ∈ Finset.range (k + 1), β ^ t * aa_Ex qs t g (s :: h) :=
        (aa_maxmin_le (hP h) _ (hqs h)).trans (aa_E_mono hD fun s =>
          ih (s :: h) (by simp only [List.length_cons]; omega))
      rw [aa_E_add, hm] at h1
      have h2 : (aa_E (qs h) fun s => ∑ t ∈ Finset.range (k + 1), β ^ t * aa_Ex qs t g (s :: h)) =
          ∑ t ∈ Finset.range (k + 1), β ^ t * aa_Ex qs (t + 1) g h := by
        simp only [aa_E, aa_Ex, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
      rw [h2] at h1
      have h3 := mul_le_mul_of_nonneg_left h1 hβ
      have h4 := hu (c h) (c' h)
      rw [Finset.sum_range_succ' _ (k + 1)]
      rw [show aa_Ex qs 0 g h = g h from rfl]
      simp only [pow_zero, one_mul, pow_succ, g]
      have h5 : β * ∑ t ∈ Finset.range (k + 1), β ^ t * aa_Ex qs (t + 1) g h =
          ∑ t ∈ Finset.range (k + 1), β ^ t * β * aa_Ex qs (t + 1) g h := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      simp only [g] at h5 h3
      linarith
  have hk := key N [] (by simp)
  refine hk.trans (add_le_add le_rfl (le_of_eq ?_))
  refine Finset.sum_congr rfl fun t ht => ?_
  have hdist : aa_distort p (fun h s => qs h s / p h s) = qs := by
    funext h s
    simp only [aa_distort]
    field_simp [(hpos h s).ne']
  have hch := aa_Ex_change p (fun h s => qs h s / p h s) g t []
  rw [hdist, aa_M, one_mul] at hch
  rw [hch, ← aa_Ex_smul]
  refine aa_Ex_congr p t [] fun h' hh' => ?_
  simp only [List.length_nil, zero_add] at hh'
  simp only [hh', g]
  ring

/-- For finite nonempty sets of priors a minimising selection exists, so the recursive
multiple-priors utility has the supergradient of Example 20.3.3. -/
theorem example_20_3_3_exists {u u' : ℝ → ℝ} (hu : ∀ x y, u y ≤ u x + u' x * (y - x)) {β : ℝ}
    (hβ : 0 ≤ β) {P : List S → Set (S → ℝ)} (hP : ∀ h, ∀ q ∈ P h, SS.IsDistribution q)
    (hfin : ∀ h, (P h).Finite) (hne : ∀ h, (P h).Nonempty) {p : List S → S → ℝ}
    (hpos : ∀ h s, 0 < p h s) (c : List S → ℝ) (N : ℕ) :
    ∃ π, aa_IsSupergradient (fun c' => aa_rmpU u β P c' N []) p N c π := by
  classical
  let qs : List S → S → ℝ := fun h =>
    (aa_maxmin_attained (hP h) (hfin h) (hne h)
      fun s => aa_rmpU u β P c (N - h.length - 1) (s :: h)).choose
  have hspec := fun h => (aa_maxmin_attained (hP h) (hfin h) (hne h)
      fun s => aa_rmpU u β P c (N - h.length - 1) (s :: h)).choose_spec
  exact ⟨_, example_20_3_3 hu hβ hP hpos c N qs (fun h => (hspec h).1)
    fun h _ => ((hspec h).2).symm⟩

/-! ### Exercise 20.2: divergence utility -/

/-- The minimising density of the multiplier problem, `m*_s = e^{−x_s/θ}/E e^{−x/θ}`. -/
noncomputable def aa_klDensity (θ : ℝ) (p x : S → ℝ) : S → ℝ :=
  fun s => Real.exp (-x s / θ) / ∑ s', p s' * Real.exp (-x s' / θ)

/-- `m*` is admissible and attains `R(x) = −θ ln E e^{−x/θ}` (relative entropy, `w = 1`). -/
theorem aa_klDensity_attains [Nonempty S] {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ}
    (hp : SS.IsDistribution p) (x : S → ℝ) :
    aa_Admissible p (aa_klDensity θ p x) ∧
      aa_divObj p (fun _ => 1) θ aa_klPhi x (aa_klDensity θ p x) =
        -θ * Real.log (∑ s, p s * Real.exp (-x s / θ)) := by
  set Zs := ∑ s, p s * Real.exp (-x s / θ) with hZ
  have hZ0 : 0 < Zs := aa_E_pos hp fun s => Real.exp_pos _
  refine ⟨⟨fun s => div_nonneg (Real.exp_pos _).le hZ0.le, ?_⟩, ?_⟩
  · simp only [aa_klDensity, ← hZ, mul_div_assoc', ← Finset.sum_div]
    exact div_self hZ0.ne'
  · have hlog : ∀ s, Real.log (aa_klDensity θ p x s) = -x s / θ - Real.log Zs := fun s => by
      rw [aa_klDensity, ← hZ, Real.log_div (Real.exp_pos _).ne' hZ0.ne', Real.log_exp]
    have hsum : ∑ s, p s * aa_klDensity θ p x s = 1 := by
      simp only [aa_klDensity, ← hZ, mul_div_assoc', ← Finset.sum_div]
      exact div_self hZ0.ne'
    unfold aa_divObj aa_klPhi
    simp only [hlog, mul_one]
    have e : ∀ s, p s * (aa_klDensity θ p x s * x s + θ * (aa_klDensity θ p x s *
        (-x s / θ - Real.log Zs) - aa_klDensity θ p x s + 1)) =
        p s * aa_klDensity θ p x s * (-θ * Real.log Zs - θ) + θ * p s := fun s => by
      field_simp
      ring
    rw [Finset.sum_congr rfl fun s _ => e s, Finset.sum_add_distrib, ← Finset.sum_mul, hsum,
      ← Finset.mul_sum, hp.sum_eq_one]
    ring

/-- Exercise 20.2, divergence utility, the certainty equivalent: the multiplier aggregator
`R(x) = −θ ln E e^{−x/θ}` has derivative `κ = m*`, the minimising density. -/
theorem aa_riskSensitive_hasCEDeriv [Nonempty S] {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ}
    (hp : SS.IsDistribution p) (x : S → ℝ) :
    aa_HasCEDeriv (fun y => -θ * Real.log (∑ s, p s * Real.exp (-y s / θ))) p
      (aa_klDensity θ p x) x := by
  set Zs := ∑ s, p s * Real.exp (-x s / θ) with hZ
  have hZ0 : 0 < Zs := aa_E_pos hp fun s => Real.exp_pos _
  have hf : (fun y : S → ℝ => ∑ s, p s * Real.exp (-y s / θ)) =
      fun y => ∑ s, p s * Real.exp ((-1 / θ) * y s) := by
    funext y
    exact Finset.sum_congr rfl fun s _ => by ring_nf
  have hin : HasFDerivAt (fun y : S → ℝ => ∑ s, p s * Real.exp (-y s / θ))
      (∑ s, p s • (Real.exp ((-1 / θ) * x s) • ((-1 / θ) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s))) x := by
    rw [hf]
    exact HasFDerivAt.fun_sum fun s _ =>
      (((hasFDerivAt_apply s x).const_mul (-1 / θ)).exp.const_mul (p s))
  have hR := (hin.log hZ0.ne').const_mul (-θ)
  unfold aa_HasCEDeriv
  refine hR.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [_root_.smul_apply, smul_eq_mul, _root_.sum_apply,
    ContinuousLinearMap.proj_apply, Finset.mul_sum, aa_klDensity]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← hZ]
  field_simp

omit [Fintype S] in
/-- **Exercise 20.2**, divergence utility (Miao, p. 735). With `W(c, y) = u(c) + βy`
(`W₁ = u'(c)`, `W₂ = β`) and the multiplier aggregator, whose derivative is the minimising density
`m*` (`aa_riskSensitive_hasCEDeriv`), the pricing kernel of Proposition 20.3.2 is
`M_{t+1} = βu'(c_{t+1})/u'(c_t) · m*_{t+1}`. -/
theorem ex_20_2_divergence (u' : ℝ → ℝ) (c : List S → ℝ) (β : ℝ) (m : List S → S → ℝ) (N : ℕ)
    (h : List S) (s : S) (hlen : h.length + 1 < N) (hβ : 0 < β) (hm : ∀ h s, 0 < m h s)
    (hu : u' (c h) ≠ 0) :
    aa_gradπ (fun h => u' (c h)) (fun _ => β) m N (s :: h) /
        aa_gradπ (fun h => u' (c h)) (fun _ => β) m N h =
      β * (u' (c (s :: h)) / u' (c h)) * m h s := by
  rw [aa_pricingKernel _ _ _ N h s hlen (aa_M_pos (fun h s => mul_pos hβ (hm h s)) h).ne' hu]
  ring

/-- Exercise 20.2, divergence utility with a general divergence (Miao, p. 696): a density `m*`
attaining `R_t(x)` is a supergradient of `R_t` at `x`:
`R_t(y) ≤ R_t(x) + E_t[m*(y − x)]` (envelope inequality). -/
theorem aa_divR_supergradient {p w : S → ℝ} (hp : SS.IsDistribution p) (hw : ∀ s, 0 ≤ w s)
    {θ : ℝ} (hθ : 0 ≤ θ) {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {x : S → ℝ} {m : S → ℝ}
    (hm : aa_Admissible p m) (hatt : aa_divObj p w θ φ x m = aa_divR p w θ φ x) (y : S → ℝ) :
    aa_divR p w θ φ y ≤ aa_divR p w θ φ x + ∑ s, p s * m s * (y s - x s) := by
  have h1 := aa_divR_le hp hw hθ hφ y hm
  have h2 := aa_divObj_sub p w θ φ y x m
  linarith

end Miao.RecursiveUtility
