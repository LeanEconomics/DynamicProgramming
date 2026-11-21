/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.AADivergence
import RecursiveUtility.AAConcavity
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Order.OrderClosed

/-!
# Utility gradients and pricing kernels

Miao, §20.3.3, pp. 706–709, on the finite event tree with horizon `N` (`aa_recU`, `U_N = c_N`).
Plans are `c : List S → ℝ`, `p h` is the one-step-ahead distribution at the node `h`, and
`E[∑_t π_t x_t] = ∑_{t ≤ N} E_t-step[π x]` is computed with `aa_Ex`.

* **Definition 20.3.1**: gradient densities (`aa_IsGradientDensity`).
* **Definition 20.3.2**: the derivative `κ` of a conditional certainty equivalent. As printed
  (`aa_CEDerivPrinted`) the condition `E h² < δ ⇒ |M(z + h) − M(z) − E[κh]| < ε` only says that `M`
  is continuous: for `M = E` both `κ = 1` and `κ = 0` satisfy it (`aa_CEDerivPrinted_not_unique`).
  The intended notion is Fréchet differentiability, `|M(z + h) − M(z) − E[κh]| = o(‖h‖)`
  (`aa_HasCEDeriv`), for which `κ = 1` is the derivative of `E` and `κ = 0` is not
  (`aa_HasCEDeriv_expectation`, `aa_not_HasCEDeriv_expectation_zero`). For `M = u⁻¹E u`,
  `κ(x) = u'(x)/u'(M(x))` (`aa_euCE_hasCEDeriv`; the book's `u'(v_t(x_{t+1}))` is
`u'(M_t(x_{t+1}))`).
* **Proposition 20.3.2**: the recursion `φ'_t(0) = W₁(t)x_t + W₂(t)E_t[κ_{t+1}φ'_{t+1}(0)]`
  (`aa_gradV_hasDerivAt`) and the gradient density `π = ℰλ`,
  `ℰ_t = ∏_{s ≤ t} W₂(s − 1)κ_s`, `λ_t = W₁(t)` (`proposition_20_3_2`,
  `proposition_20_3_2_gradient`). With a finite horizon the transversality condition
  `E[π_t x_t] → 0` is not needed; `λ_N = 1` since `U_N = c_N`.
* The pricing kernel `π_{t+1}/π_t = (λ_{t+1}/λ_t)W₂(t)κ_{t+1}` (`aa_pricingKernel`).
* The marginal value of wealth (p. 708): the envelope argument `J'(w₀) = μ` with
  `W₁(c₀, M₀) = λ₀ = μ` (`aa_marginal_value_wealth`, `aa_lambda0_eq_mu`).
* Utility supergradients (p. 709) (`aa_IsSupergradient`).
-/

namespace Miao.RecursiveUtility

open Finset Filter Topology

variable {S : Type*} [Fintype S]

/-- **Definition 20.3.1** (Miao, p. 707): `π` is a gradient density of `U₀` at `c` if
`lim_{α↓0} (U₀(c + αx) − U₀(c))/α = E[∑_{t ≤ N} π_t x_t]` for every direction `x`. -/
def aa_IsGradientDensity (U₀ : (List S → ℝ) → ℝ) (p : List S → S → ℝ) (N : ℕ)
    (c π : List S → ℝ) : Prop :=
  ∀ x : List S → ℝ, Tendsto (fun α => (U₀ (c + α • x) - U₀ c) / α) (𝓝[>] 0)
    (𝓝 (∑ t ∈ Finset.range (N + 1), aa_Ex p t (fun h => π h * x h) []))

/-- Utility supergradients (Miao, p. 709): `U₀(c') ≤ U₀(c) + E[∑_t π_t(c'_t − c_t)]` for all `c'`.
-/
def aa_IsSupergradient (U₀ : (List S → ℝ) → ℝ) (p : List S → S → ℝ) (N : ℕ)
    (c π : List S → ℝ) : Prop :=
  ∀ c' : List S → ℝ,
    U₀ c' ≤ U₀ c + ∑ t ∈ Finset.range (N + 1), aa_Ex p t (fun h => π h * (c' h - c h)) []

/-- **Definition 20.3.2** as printed (Miao, p. 707): for every `ε > 0` there is `δ > 0` with
`E[h²] < δ ⇒ |M(z + h) − M(z) − E[κh]| < ε`. -/
def aa_CEDerivPrinted (M : (S → ℝ) → ℝ) (p κ z : S → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ v : S → ℝ, aa_E p (fun s => v s ^ 2) < δ →
    |M (z + v) - M z - aa_E p (fun s => κ s * v s)| < ε

/-- **Definition 20.3.2**, corrected: `κ` is the derivative of the certainty equivalent `M` at `z`
if `M` is Fréchet differentiable at `z` with derivative `h ↦ E[κh]`. -/
def aa_HasCEDeriv (M : (S → ℝ) → ℝ) (p κ z : S → ℝ) : Prop :=
  HasFDerivAt M (∑ s, (p s * κ s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s) z

theorem aa_cePrinted_apply (p κ v : S → ℝ) :
    (∑ s, (p s * κ s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s) v =
      aa_E p (fun s => κ s * v s) := by
  simp [aa_E, mul_assoc]

/-- The printed Definition 20.3.2 does not determine `κ`: for the expectation `M = E_p`, both
`κ = 1` (the true derivative) and `κ = 0` satisfy it. -/
theorem aa_CEDerivPrinted_not_unique {p : S → ℝ} (hp : SS.IsDistribution p) (z : S → ℝ) :
    aa_CEDerivPrinted (aa_E p) p (fun _ => 1) z ∧ aa_CEDerivPrinted (aa_E p) p (fun _ => 0) z := by
  constructor
  · intro ε hε
    refine ⟨1, one_pos, fun v _ => ?_⟩
    have : aa_E p (z + v) - aa_E p z - aa_E p (fun s => 1 * v s) = 0 := by
      simp only [one_mul]
      rw [show aa_E p (z + v) = aa_E p (fun s => z s + v s) from rfl, aa_E_add]
      ring
    rw [this, abs_zero]
    exact hε
  · intro ε hε
    refine ⟨ε ^ 2, by positivity, fun v hv => ?_⟩
    have hvar : aa_E p v ^ 2 ≤ aa_E p (fun s => v s ^ 2) := by
      have h0 : 0 ≤ aa_E p (fun s => (v s - aa_E p v) ^ 2) :=
        Finset.sum_nonneg fun s _ => mul_nonneg (hp.nonneg s) (sq_nonneg _)
      have e : aa_E p (fun s => (v s - aa_E p v) ^ 2) =
          aa_E p (fun s => v s ^ 2) - aa_E p v ^ 2 := by
        simp only [aa_E, sub_sq, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have h1 : ∑ s, p s * (2 * v s * ∑ s', p s' * v s') = 2 * (∑ s, p s * v s) ^ 2 := by
          calc ∑ s, p s * (2 * v s * ∑ s', p s' * v s') =
              ∑ s, (2 * ∑ s', p s' * v s') * (p s * v s) :=
                Finset.sum_congr rfl fun s _ => by ring
            _ = 2 * (∑ s, p s * v s) ^ 2 := by rw [← Finset.mul_sum]; ring
        have h2 : ∑ s, p s * (∑ s', p s' * v s') ^ 2 = (∑ s, p s * v s) ^ 2 := by
          rw [← Finset.sum_mul, hp.sum_eq_one, one_mul]
        rw [h1, h2]
        ring
      linarith
    have : aa_E p (z + v) - aa_E p z - aa_E p (fun s => 0 * v s) = aa_E p v := by
      simp only [zero_mul]
      rw [show aa_E p (z + v) = aa_E p (fun s => z s + v s) from rfl, aa_E_add,
        aa_E_const hp]
      ring
    rw [this]
    exact abs_lt_of_sq_lt_sq' (by linarith) hε.le |>.elim (fun h1 h2 => abs_lt.2 ⟨h1, h2⟩)

/-- The expectation has the corrected derivative `κ = 1`. -/
theorem aa_HasCEDeriv_expectation (p z : S → ℝ) : aa_HasCEDeriv (aa_E p) p (fun _ => 1) z := by
  unfold aa_HasCEDeriv
  have h : HasFDerivAt (fun x : S → ℝ => ∑ s, p s * x s)
      (∑ s, p s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s) z :=
    HasFDerivAt.fun_sum fun s _ => (hasFDerivAt_apply s z).const_mul (p s)
  have e : aa_E p = fun x : S → ℝ => ∑ s, p s * x s := rfl
  rw [e]
  simpa using h

/-- With the corrected Definition 20.3.2, `κ = 0` is not the derivative of `E_p`. -/
theorem aa_not_HasCEDeriv_expectation_zero {p : S → ℝ} (hp : SS.IsDistribution p) (z : S → ℝ) :
    ¬ aa_HasCEDeriv (aa_E p) p (fun _ => 0) z := by
  intro h
  have h1 := (aa_HasCEDeriv_expectation p z).unique h
  have := congrArg (fun L : (S → ℝ) →L[ℝ] ℝ => L fun _ => 1) h1
  simp only [aa_cePrinted_apply] at this
  rw [aa_E_const hp, aa_E_const hp] at this
  norm_num at this

/-- Miao, p. 707: for `M(x) = u⁻¹(E u(x))` with `u` an order isomorphism of `ℝ` differentiable with
`u' ≠ 0` at `M(x)`, the derivative of the certainty equivalent is `κ(x) = u'(x)/u'(M(x))`. -/
theorem aa_euCE_hasCEDeriv (u : ℝ ≃o ℝ) (u' : ℝ → ℝ) (hu : ∀ y, HasDerivAt u (u' y) y)
    (p x : S → ℝ) (hM : u' (u.symm (aa_E p fun s => u (x s))) ≠ 0) :
    aa_HasCEDeriv (fun y => u.symm (aa_E p fun s => u (y s))) p
      (fun s => u' (x s) / u' (u.symm (aa_E p fun s => u (x s)))) x := by
  set a := aa_E p fun s => u (x s) with ha
  have hinv : HasDerivAt u.symm (u' (u.symm a))⁻¹ a :=
    HasDerivAt.of_local_left_inverse u.symm.continuous.continuousAt (hu _) hM
      (Eventually.of_forall fun y => u.apply_symm_apply y)
  have hin : HasFDerivAt (fun y : S → ℝ => aa_E p fun s => u (y s))
      (∑ s, p s • (u' (x s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s)) x :=
    HasFDerivAt.fun_sum fun s _ =>
      ((hu (x s)).hasFDerivAt.comp x (hasFDerivAt_apply s x)).const_mul (p s) |>.congr_fderiv
        (by ext v; simp [mul_comm])
  have hcomp := hinv.hasFDerivAt.comp x hin
  have hL : (ContinuousLinearMap.toSpanSingleton ℝ (u' (u.symm a))⁻¹).comp
      (∑ s, p s • (u' (x s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s)) =
      ∑ s, (p s * (u' (x s) / u' (u.symm a))) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply, _root_.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, map_sum,
      ContinuousLinearMap.toSpanSingleton_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    field_simp
  exact hcomp.congr_fderiv hL

/-! ### Proposition 20.3.2 -/

/-- The derivative recursion of Proposition 20.3.2:
`V_{n+1}(h) = W₁(h)x(h) + W₂(h)E_h[κ_h V_n]`, `V_0(h) = x(h)`. -/
def aa_gradV (W₁ W₂ : List S → ℝ) (p κ : List S → S → ℝ) (x : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => x h
  | n + 1, h => W₁ h * x h + W₂ h * ∑ s, p h s * κ h s * aa_gradV W₁ W₂ p κ x n (s :: h)

/-- The differentiability hypotheses of Proposition 20.3.2 along the plan `c`, horizon `N`: at
every non-terminal node `h`, `W` has partial derivatives `W₁(h), W₂(h)` at
`(c_h, M_h(U_{h+1}))` and `M_h` has derivative `κ_h` at `U_{h+1}`. -/
def aa_GradHyp (W : ℝ → ℝ → ℝ) (M : List S → (S → ℝ) → ℝ) (p : List S → S → ℝ) (c : List S → ℝ)
    (N : ℕ) (W₁ W₂ : List S → ℝ) (κ : List S → S → ℝ) : Prop :=
  ∀ h : List S, h.length < N →
    HasFDerivAt (fun z : ℝ × ℝ => W z.1 z.2)
      (W₁ h • ContinuousLinearMap.fst ℝ ℝ ℝ + W₂ h • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (c h, M h fun s => aa_recU W M c (N - h.length - 1) (s :: h)) ∧
    aa_HasCEDeriv (M h) (p h) (κ h) fun s => aa_recU W M c (N - h.length - 1) (s :: h)

/-- **Proposition 20.3.2, the recursion** (Miao, p. 708): with `φ_t(α) = U_t(c + αx)`,
`φ'_t(0) = W₁(t)x_t + W₂(t)E_t[κ_{t+1}φ'_{t+1}(0)]`, at every node `h` with `|h| + k = N`. -/
theorem aa_gradV_hasDerivAt {W : ℝ → ℝ → ℝ} {M : List S → (S → ℝ) → ℝ} {p : List S → S → ℝ}
    {c : List S → ℝ} {N : ℕ} {W₁ W₂ : List S → ℝ} {κ : List S → S → ℝ}
    (hyp : aa_GradHyp W M p c N W₁ W₂ κ) (x : List S → ℝ) :
    ∀ k h, h.length + k = N →
      HasDerivAt (fun α : ℝ => aa_recU W M (c + α • x) k h) (aa_gradV W₁ W₂ p κ x k h) 0 := by
  intro k
  induction k with
  | zero =>
    intro h _
    simp only [aa_recU, aa_gradV, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (x h)).const_add (c h)
  | succ k ih =>
    intro h hlen
    have hlt : h.length < N := by omega
    have hidx : N - h.length - 1 = k := by omega
    obtain ⟨hW, hM⟩ := hyp h hlt
    rw [hidx] at hW hM
    have hchild : HasDerivAt (fun α : ℝ => fun s => aa_recU W M (c + α • x) k (s :: h))
        (fun s => aa_gradV W₁ W₂ p κ x k (s :: h)) 0 :=
      hasDerivAt_pi.2 fun s => ih (s :: h) (by simp only [List.length_cons]; omega)
    have h0 : (fun s => aa_recU W M (c + (0 : ℝ) • x) k (s :: h)) =
        fun s => aa_recU W M c k (s :: h) := by simp
    have hMc := HasFDerivAt.comp_hasDerivAt_of_eq 0 hM hchild h0.symm
    have hc0 : HasDerivAt (fun α : ℝ => (c + α • x) h) (x h) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (x h)).const_add (c h)
    have hpair := hc0.prodMk hMc
    have hpt : ((c + (0 : ℝ) • x) h,
        (M h ∘ fun α : ℝ => fun s => aa_recU W M (c + α • x) k (s :: h)) 0) =
        (c h, M h fun s => aa_recU W M c k (s :: h)) := by simp
    have hall := HasFDerivAt.comp_hasDerivAt_of_eq 0 hW hpair hpt.symm
    simp only [aa_recU, aa_gradV]
    convert hall using 1
    · rfl
    · simp [mul_assoc]

/-- `t`-step expectations from `h` only see nodes of length `|h| + t`. -/
theorem aa_Ex_congr (q : List S → S → ℝ) {f g : List S → ℝ} :
    ∀ t h, (∀ h', h'.length = h.length + t → f h' = g h') → aa_Ex q t f h = aa_Ex q t g h
  | 0, h, hfg => hfg h (by simp)
  | t + 1, h, hfg => by
    simp only [aa_Ex]
    exact Finset.sum_congr rfl fun s _ => by
      rw [aa_Ex_congr q t (s :: h) fun h' hh' => hfg h' (by simp at hh'; omega)]

/-- The gradient density `π = ℰλ` of Proposition 20.3.2: `ℰ_t = ∏ W₂κ` along the path and
`λ_t = W₁(t)` (`λ_N = 1`, since `U_N = c_N`). -/
def aa_gradπ (W₁ W₂ : List S → ℝ) (κ : List S → S → ℝ) (N : ℕ) (h : List S) : ℝ :=
  aa_M (fun h' s => W₂ h' * κ h' s) h * if h.length < N then W₁ h else 1

/-- **Proposition 20.3.2** (Miao, p. 708). Under the differentiability hypotheses, the derivative of
`α ↦ U₀(c + αx)` at `0` is `E[∑_{t ≤ N} π_t x_t]` with `π = ℰλ` (`aa_gradπ`). -/
theorem proposition_20_3_2 {W : ℝ → ℝ → ℝ} {M : List S → (S → ℝ) → ℝ} {p : List S → S → ℝ}
    {c : List S → ℝ} {N : ℕ} {W₁ W₂ : List S → ℝ} {κ : List S → S → ℝ}
    (hyp : aa_GradHyp W M p c N W₁ W₂ κ) (x : List S → ℝ) :
    HasDerivAt (fun α : ℝ => aa_recU W M (c + α • x) N [])
      (∑ t ∈ Finset.range (N + 1), aa_Ex p t (fun h => aa_gradπ W₁ W₂ κ N h * x h) []) 0 := by
  have hd := aa_gradV_hasDerivAt hyp x N [] (by simp)
  convert hd using 1
  set m : List S → S → ℝ := fun h' s => W₂ h' * κ h' s with hm
  have hun := aa_linear_unroll (aa_distort p m) 1 (fun h => W₁ h * x h) x
    (aa_gradV W₁ W₂ p κ x) (fun _ => rfl) (fun n h => by
      simp only [aa_gradV, aa_distort, hm, one_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by ring) N []
  rw [hun, Finset.sum_range_succ]
  simp only [one_pow, one_mul]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    have := aa_Ex_change p m (fun h => W₁ h * x h) t []
    rw [aa_M, one_mul] at this
    rw [this]
    refine aa_Ex_congr p t [] fun h' hh' => ?_
    have : h'.length < N := by simp at hh' ht; omega
    simp only [aa_gradπ, this, ↓reduceIte, hm]
    ring
  · have := aa_Ex_change p m x N []
    rw [aa_M, one_mul] at this
    rw [this]
    refine aa_Ex_congr p N [] fun h' hh' => ?_
    have : ¬ h'.length < N := by simp at hh'; omega
    simp only [aa_gradπ, this, ↓reduceIte, hm, mul_one]

/-- **Proposition 20.3.2** in the form of Definition 20.3.1: `π = ℰλ` is the utility gradient
density of `U₀` at `c`. -/
theorem proposition_20_3_2_gradient {W : ℝ → ℝ → ℝ} {M : List S → (S → ℝ) → ℝ}
    {p : List S → S → ℝ} {c : List S → ℝ} {N : ℕ} {W₁ W₂ : List S → ℝ} {κ : List S → S → ℝ}
    (hyp : aa_GradHyp W M p c N W₁ W₂ κ) :
    aa_IsGradientDensity (fun c' => aa_recU W M c' N []) p N c (aa_gradπ W₁ W₂ κ N) := by
  intro x
  have h := hasDerivAt_iff_tendsto_slope_zero.1 (proposition_20_3_2 hyp x)
  have h2 := h.mono_left (nhdsWithin_mono _ fun t (ht : 0 < t) => ne_of_gt ht)
  refine h2.congr fun α => ?_
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  ring

omit [Fintype S] in
/-- The pricing kernel (Miao, p. 709): `π_{t+1}/π_t = (λ_{t+1}/λ_t)W₂(t)κ_{t+1}`. -/
theorem aa_pricingKernel (W₁ W₂ : List S → ℝ) (κ : List S → S → ℝ) (N : ℕ) (h : List S) (s : S)
    (hlen : h.length + 1 < N) (hM : aa_M (fun h' s => W₂ h' * κ h' s) h ≠ 0) (hlam : W₁ h ≠ 0) :
    aa_gradπ W₁ W₂ κ N (s :: h) / aa_gradπ W₁ W₂ κ N h =
      W₁ (s :: h) / W₁ h * W₂ h * κ h s := by
  have h1 : h.length < N := by omega
  have h2 : (s :: h).length < N := by simpa using hlen
  simp only [aa_gradπ, h1, h2, ↓reduceIte, aa_M]
  field_simp

/-- The marginal value of wealth (Miao, p. 708). If `c*(w)` solves
`max U₀(c)` s.t. `E[∑ p_t c_t] ≤ w` near `w₀` with a binding budget, `U₀` has derivative `L` at
`c*(w₀)` with the first-order condition `L = μB` (`B` the budget functional), and `c*` is
differentiable at `w₀`, then `J(w) = U₀(c*(w))` has `J'(w₀) = μ`. -/
theorem aa_marginal_value_wealth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : E → ℝ} {L B : E →L[ℝ] ℝ} {cstar : ℝ → E} {v : E} {w₀ μ : ℝ}
    (hU : HasFDerivAt U L (cstar w₀)) (hc : HasDerivAt cstar v w₀)
    (hbud : ∀ᶠ w in 𝓝 w₀, B (cstar w) = w) (hfoc : L = μ • B) :
    HasDerivAt (fun w => U (cstar w)) μ w₀ := by
  have h1 : HasDerivAt (fun w => B (cstar w)) (B v) w₀ := B.hasFDerivAt.comp_hasDerivAt w₀ hc
  have h2 : HasDerivAt (fun w => B (cstar w)) 1 w₀ :=
    (hasDerivAt_id w₀).congr_of_eventuallyEq hbud
  have hBv : B v = 1 := h1.unique h2
  have := hU.comp_hasDerivAt w₀ hc
  rw [hfoc] at this
  simpa [hBv, Function.comp_def] using this

omit [Fintype S] in
/-- Miao, p. 709: `λ₀ = W₁(c₀, M₀(U₁(c)))`: the gradient density at the root is `λ₀`, so the
first-order condition `π = μ p` with state-price density `p₀ = 1` gives `λ₀ = μ = J'(w₀)`. -/
theorem aa_lambda0_eq_mu (W₁ W₂ : List S → ℝ) (κ : List S → S → ℝ) {N : ℕ} (hN : 0 < N)
    (price : List S → ℝ) (μ : ℝ) (hfoc : ∀ h, aa_gradπ W₁ W₂ κ N h = μ * price h)
    (hp0 : price [] = 1) : W₁ [] = μ := by
  have := hfoc []
  simp only [aa_gradπ, aa_M, List.length_nil, hN, ↓reduceIte, one_mul, hp0, mul_one] at this
  exact this

end Miao.RecursiveUtility
