/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCreditFrictions.Dividend
import InfiniteHorizonDP.SLPEnvelope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The firm's first-order conditions

AKMM, §19.4.1, the firm's problem (19.3) and its first-order conditions (19.4)–(19.6),
pp. 574–575, with Appendix 19.A.1, p. 877.

The firm at `(k, b)` chooses `(d, ℓ, k′, b′)` subject to the budget
`F(z, k, ℓ) − wℓ + b′/R̃ = b + p[k′ − (1 − δ)k] + ϕ(d)` and the borrowing limit `ξpk′ ≥ b′/R̃`,
to maximise `d + E[m′Ω(S′; k′, b′)]`.

**The envelope conditions** (p. 877). If `Ω(S; ·, ·)` is concave near `(k₀, b₀)` and
`(d₀, ℓ₀, k₀′, b₀′)` is optimal there with `ϕ′(d₀) > 0`, then `Ω` is differentiable at
`(k₀, b₀)` with `Ω_k = λ[(1 − δ)p + F_k]` and `Ω_b = −λ`, `λ = 1/ϕ′(d₀)` (`env_firm`,
`appendix_19_A_1_envelope`). The proof applies the Benveniste–Scheinkman lemma
(`Miao.InfiniteHorizonDP.theorem_4_10`) to the plan that keeps `(ℓ₀, k₀′, b₀′)` and pays out
the dividend `cfDiv` that the budget then allows.

**Kuhn–Tucker conditions** (p. 877). If the continuation `C(k′, b′) = E[m′Ω(S′; k′, b′)]` is
differentiable at the optimum, variations of the plan along feasible directions give
`F_ℓ = w` (19.4) and a multiplier `μ ≥ 0`, zero when the limit is slack, with
`C_k − λp + μλξp = 0` and `C_b + λ/R̃ − μλ/R̃ = 0` (`kkt_firm`): the four first-order
conditions of 19.A.1, derived rather than assumed.

**(19.5)–(19.6).** Substituting the envelope conditions, updated one period, and `λ = 1/ϕ′(d)`
gives `E[m′(ϕ′(d)/ϕ′(d′))((1 − δ)p′ + F_k′)] = (1 − μξ)p` (`eq_19_5`) and
`E[m′(ϕ′(d)/ϕ′(d′))]R̃ = 1 − μ` (`eq_19_6`); `firm_focs` chains everything. Expectations are
over a finite set of next-period states `s` with probabilities `πₛ`.
-/

namespace AKMM.CreditFrictions

open Filter Topology

/-! ### The envelope conditions -/

open Miao.InfiniteHorizonDP in
/-- AKMM, Appendix 19.A.1, p. 877 (envelope conditions). `Y` is output `F(z, ·, ℓ₀)` as a
function of capital, `wl = wℓ₀`, and `cont = E[m′Ω(S′; k′, b′)]` at the optimal `(k′, b′)`. If
`Ω` is concave on a neighbourhood of `(k₀, b₀)`, every plan keeping `(ℓ₀, k′, b′)` is worth at
most `Ω`, and the optimal plan pays `d₀` with `ϕ′(d₀) > 0`, then `Ω` is differentiable at
`(k₀, b₀)` with derivative `(1/ϕ′(d₀))((F_k + p(1 − δ))dk − db)`. -/
theorem env_firm {Y : ℝ → ℝ} {Yk : ℝ} {Ω : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {κ φ wl p δ Rt k' b' cont d₀ k₀ b₀ : ℝ}
    (hΩ : ConcaveOn ℝ U Ω) (hU : U ∈ 𝓝 (k₀, b₀)) (hY : HasDerivAt Y Yk k₀)
    (hle : ∀ (k b d : ℝ), cfPhi κ φ d = Y k - wl + b' / Rt - b - p * (k' - (1 - δ) * k) →
      d + cont ≤ Ω (k, b))
    (hbud : cfPhi κ φ d₀ = Y k₀ - wl + b' / Rt - b₀ - p * (k' - (1 - δ) * k₀))
    (hd₀ : 0 < cfPhiD κ φ d₀) (heq : Ω (k₀, b₀) = d₀ + cont) :
    HasFDerivAt Ω ((cfPhiD κ φ d₀)⁻¹ • ((Yk + p * (1 - δ)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
      ContinuousLinearMap.snd ℝ ℝ ℝ)) (k₀, b₀) := by
  set X : ℝ × ℝ → ℝ := fun x => Y x.1 - wl + b' / Rt - x.2 - p * (k' - (1 - δ) * x.1)
    with hXdef
  have hX : HasFDerivAt X ((Yk + p * (1 - δ)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
      ContinuousLinearMap.snd ℝ ℝ ℝ) (k₀, b₀) := by
    have h1 : HasFDerivAt (fun x : ℝ × ℝ => Y x.1) (Yk • ContinuousLinearMap.fst ℝ ℝ ℝ)
        (k₀, b₀) := hY.comp_hasFDerivAt (k₀, b₀) hasFDerivAt_fst
    have h2 : HasFDerivAt (fun x : ℝ × ℝ => x.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (k₀, b₀) :=
      hasFDerivAt_snd
    have h3 : HasFDerivAt (fun x : ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (k₀, b₀) :=
      hasFDerivAt_fst
    have h4 := (((h1.sub_const wl).add_const (b' / Rt)).sub h2).add (h3.const_mul (p * (1 - δ)))
    convert h4.sub_const (p * k') using 1
    · funext x
      simp only [hXdef, Pi.add_apply, Pi.sub_apply]
      ring
    · ext
      · simp
      · simp
  have hX0 : X (k₀, b₀) = cfPhi κ φ d₀ := hbud.symm
  have hrad : 0 < 1 + 4 * κ * (X (k₀, b₀) - φ) := by
    rw [hX0, div_radicand_phi]
    positivity
  have hdiv0 : cfDiv κ φ (X (k₀, b₀)) = d₀ := by rw [hX0]; exact div_div_phi hd₀.le
  have hW : HasFDerivAt (fun x => cfDiv κ φ (X x) + cont)
      ((cfPhiD κ φ d₀)⁻¹ • ((Yk + p * (1 - δ)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
        ContinuousLinearMap.snd ℝ ℝ ℝ)) (k₀, b₀) := by
    have h := (div_hasDerivAt_div hrad).comp_hasFDerivAt (k₀, b₀) hX
    rw [hdiv0] at h
    exact h.add_const cont
  refine theorem_4_10 hΩ hU hW (by rw [heq, hdiv0]) ?_
  have hc : ContinuousAt (fun x => 1 + 4 * κ * (X x - φ)) (k₀, b₀) :=
    continuousAt_const.add (continuousAt_const.mul (hX.continuousAt.sub continuousAt_const))
  filter_upwards [hc.eventually_const_lt hrad] with x hx
  exact hle x.1 x.2 _ (div_phi_div hx.le)

open Miao.InfiniteHorizonDP in
/-- **Appendix 19.A.1** (AKMM, p. 877): the envelope conditions
`Ω_k(S; k, b) = λ[(1 − δ)p + F_k(z, k, ℓ)]` and `Ω_b(S; k, b) = −λ`, with `λ = 1/ϕ′(d)` (the
first-order condition `1 = λϕ_d(d)`), under the hypotheses of `env_firm`. -/
theorem appendix_19_A_1_envelope {Y : ℝ → ℝ} {Yk : ℝ} {Ω : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {κ φ wl p δ Rt k' b' cont d₀ k₀ b₀ : ℝ}
    (hΩ : ConcaveOn ℝ U Ω) (hU : U ∈ 𝓝 (k₀, b₀)) (hY : HasDerivAt Y Yk k₀)
    (hle : ∀ (k b d : ℝ), cfPhi κ φ d = Y k - wl + b' / Rt - b - p * (k' - (1 - δ) * k) →
      d + cont ≤ Ω (k, b))
    (hbud : cfPhi κ φ d₀ = Y k₀ - wl + b' / Rt - b₀ - p * (k' - (1 - δ) * k₀))
    (hd₀ : 0 < cfPhiD κ φ d₀) (heq : Ω (k₀, b₀) = d₀ + cont) :
    1 = (cfPhiD κ φ d₀)⁻¹ * cfPhiD κ φ d₀ ∧
    HasDerivAt (fun k => Ω (k, b₀)) ((cfPhiD κ φ d₀)⁻¹ * ((1 - δ) * p + Yk)) k₀ ∧
    HasDerivAt (fun b => Ω (k₀, b)) (-(cfPhiD κ φ d₀)⁻¹) b₀ := by
  have h := env_firm hΩ hU hY hle hbud hd₀ heq
  refine ⟨(inv_mul_cancel₀ hd₀.ne').symm, ?_, ?_⟩
  · have hp : HasDerivAt (fun k : ℝ => (k, b₀)) ((1 : ℝ), (0 : ℝ)) k₀ :=
      (hasDerivAt_id k₀).prodMk (hasDerivAt_const k₀ b₀)
    refine (h.comp_hasDerivAt k₀ hp).congr_deriv ?_
    simp only [FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply,
      Pi.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  · have hp : HasDerivAt (fun b : ℝ => (k₀, b)) ((0 : ℝ), (1 : ℝ)) b₀ :=
      (hasDerivAt_const b₀ k₀).prodMk (hasDerivAt_id b₀)
    refine (h.comp_hasDerivAt b₀ hp).congr_deriv ?_
    simp

/-! ### The Kuhn–Tucker conditions from optimality -/

/-- A one-sided maximum: if `f` is differentiable at `0` and `f t ≤ f 0` for small `t ≥ 0`,
then `f′(0) ≤ 0`. -/
theorem kkt_deriv_nonpos {f : ℝ → ℝ} {D : ℝ} (hf : HasDerivAt f D 0)
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t → f t ≤ f 0) : D ≤ 0 := by
  have hs := hf.tendsto_slope_zero_right
  refine le_of_tendsto hs ?_
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with t ht htpos
  have htp : (0 : ℝ) < t := htpos
  rw [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 htp.le) (by linarith [ht htp.le])

/-- The firm's resources for dividends, `F(z, k, ℓ) − wℓ + b′/R̃ − b − p[k′ − (1 − δ)k]`
(the budget of (19.3), p. 574, solved for `ϕ(d)`). -/
noncomputable def kktRes (Yl : ℝ → ℝ) (w Rt b p δ k ℓ k' b' : ℝ) : ℝ :=
  Yl ℓ - w * ℓ + b' / Rt - b - p * (k' - (1 - δ) * k)

/-- AKMM, p. 877: the value of the plan moved from the optimum `(ℓ₀, k₀′, b₀′)` in the direction
`(aℓ, ak, ab)`, paying the largest dividend the budget allows, is differentiable at `0` with
derivative `(F_ℓaℓ − waℓ + ab/R̃ − pak)/ϕ′(d₀) + C′(ak, ab)`, and is at most the optimum
wherever the moved plan satisfies the borrowing limit. -/
theorem kkt_dir {Yl : ℝ → ℝ} {Fl : ℝ} {C : ℝ × ℝ → ℝ} {C' : ℝ × ℝ →L[ℝ] ℝ}
    {κ φ w Rt b p δ k ξ ℓ₀ k₀ b₀ d₀ : ℝ} (hY : HasDerivAt Yl Fl ℓ₀)
    (hC : HasFDerivAt C C' (k₀, b₀))
    (hopt : ∀ d ℓ k' b', cfPhi κ φ d = kktRes Yl w Rt b p δ k ℓ k' b' → b' / Rt ≤ ξ * p * k' →
      d + C (k', b') ≤ d₀ + C (k₀, b₀))
    (hbud : cfPhi κ φ d₀ = kktRes Yl w Rt b p δ k ℓ₀ k₀ b₀) (hq : 0 < cfPhiD κ φ d₀)
    (aℓ ak ab : ℝ) :
    ∃ f : ℝ → ℝ, HasDerivAt f ((cfPhiD κ φ d₀)⁻¹ * (Fl * aℓ - w * aℓ + ab / Rt - p * ak) +
      C' (ak, ab)) 0 ∧ ∀ᶠ t in 𝓝 (0 : ℝ),
        (b₀ + ab * t) / Rt ≤ ξ * p * (k₀ + ak * t) → f t ≤ f 0 := by
  set Xt : ℝ → ℝ := fun t => kktRes Yl w Rt b p δ k (ℓ₀ + aℓ * t) (k₀ + ak * t) (b₀ + ab * t)
    with hXt
  have hlin : ∀ (x a : ℝ), HasDerivAt (fun t : ℝ => x + a * t) a 0 := fun x a => by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).const_add x
  have hYt : HasDerivAt (fun t => Yl (ℓ₀ + aℓ * t)) (Fl * aℓ) 0 :=
    hY.comp_of_eq 0 (hlin ℓ₀ aℓ) (by ring)
  have hX : HasDerivAt Xt (Fl * aℓ - w * aℓ + ab / Rt - p * ak) 0 := by
    have h := ((((hYt.sub ((hlin ℓ₀ aℓ).const_mul w)).add ((hlin b₀ ab).div_const Rt)).sub_const
      b).sub ((hlin (k₀ - (1 - δ) * k) ak).const_mul p))
    convert h using 1
    funext t
    simp only [hXt, kktRes, Pi.add_apply, Pi.sub_apply]
    ring
  have hX0 : Xt 0 = cfPhi κ φ d₀ := by
    simp only [hXt, mul_zero, add_zero]
    exact hbud.symm
  have hrad : 0 < 1 + 4 * κ * (Xt 0 - φ) := by
    rw [hX0, div_radicand_phi]
    positivity
  have hdiv0 : cfDiv κ φ (Xt 0) = d₀ := by rw [hX0]; exact div_div_phi hq.le
  have hD := (div_hasDerivAt_div hrad).comp (0 : ℝ) hX
  rw [hdiv0] at hD
  have hp : HasDerivAt (fun t : ℝ => (k₀ + ak * t, b₀ + ab * t)) (ak, ab) 0 :=
    (hlin k₀ ak).prodMk (hlin b₀ ab)
  have hCt := hC.comp_hasDerivAt_of_eq 0 hp (by simp)
  refine ⟨fun t => cfDiv κ φ (Xt t) + C (k₀ + ak * t, b₀ + ab * t), hD.add hCt, ?_⟩
  have hc : ContinuousAt (fun t => 1 + 4 * κ * (Xt t - φ)) 0 :=
    continuousAt_const.add (continuousAt_const.mul (hX.continuousAt.sub continuousAt_const))
  filter_upwards [hc.eventually_const_lt hrad] with t ht hfeas
  have h0 : cfDiv κ φ (Xt 0) + C (k₀ + ak * 0, b₀ + ab * 0) = d₀ + C (k₀, b₀) := by
    rw [hdiv0]
    simp
  rw [h0]
  exact hopt _ _ _ _ (div_phi_div ht.le) hfeas

/-- A continuous linear functional on `ℝ × ℝ` is determined by its values on `(1, 0)` and
`(0, 1)`. -/
theorem kkt_clm_apply (L : ℝ × ℝ →L[ℝ] ℝ) (a c : ℝ) :
    L (a, c) = a * L (1, 0) + c * L (0, 1) := by
  have h : ((a, c) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + c • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **The firm's first-order conditions of Appendix 19.A.1** (AKMM, p. 877), derived from
optimality. Let `(d₀, ℓ₀, k₀′, b₀′)` solve (19.3) at `(k, b)` (every feasible plan is worth at
most it), with `ϕ′(d₀) > 0`, `R̃ > 0`, output `F(z, k, ·)` differentiable at `ℓ₀` and the
continuation `C(k′, b′) = E[m′Ω(S′; k′, b′)]` differentiable at `(k₀′, b₀′)`, with partial
derivatives `C_k = C′(1, 0)`, `C_b = C′(0, 1)`. With `λ = 1/ϕ′(d₀)`: `F_ℓ = w` (19.4), and
there is `μ ≥ 0` with `μ(ξpk₀′ − b₀′/R̃) = 0` (zero when the limit is slack),
`C_k − λp + μλξp = 0` and `C_b + λ/R̃ − μλ/R̃ = 0`. -/
theorem kkt_firm {Yl : ℝ → ℝ} {Fl : ℝ} {C : ℝ × ℝ → ℝ} {C' : ℝ × ℝ →L[ℝ] ℝ}
    {κ φ w Rt b p δ k ξ ℓ₀ k₀ b₀ d₀ : ℝ} (hRt : 0 < Rt) (hY : HasDerivAt Yl Fl ℓ₀)
    (hC : HasFDerivAt C C' (k₀, b₀))
    (hopt : ∀ d ℓ k' b', cfPhi κ φ d = kktRes Yl w Rt b p δ k ℓ k' b' → b' / Rt ≤ ξ * p * k' →
      d + C (k', b') ≤ d₀ + C (k₀, b₀))
    (hbud : cfPhi κ φ d₀ = kktRes Yl w Rt b p δ k ℓ₀ k₀ b₀) (hq : 0 < cfPhiD κ φ d₀)
    (hfeas : b₀ / Rt ≤ ξ * p * k₀) :
    Fl = w ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ * (ξ * p * k₀ - b₀ / Rt) = 0 ∧
      C' (1, 0) - (cfPhiD κ φ d₀)⁻¹ * p + μ * (cfPhiD κ φ d₀)⁻¹ * ξ * p = 0 ∧
      C' (0, 1) + (cfPhiD κ φ d₀)⁻¹ / Rt - μ * (cfPhiD κ φ d₀)⁻¹ / Rt = 0 := by
  obtain ⟨f1, hf1, hle1⟩ := kkt_dir hY hC hopt hbud hq 1 0 0
  have h1 : IsLocalMax f1 0 := by
    filter_upwards [hle1] with t ht
    exact ht (by simpa using hfeas)
  have e1 := h1.hasDerivAt_eq_zero hf1
  obtain ⟨f2, hf2, hle2⟩ := kkt_dir hY hC hopt hbud hq 0 0 (-1)
  have e2 := kkt_deriv_nonpos hf2 (by
    filter_upwards [hle2] with t ht htpos
    refine ht ?_
    have : (b₀ + -1 * t) / Rt ≤ b₀ / Rt := div_le_div_of_nonneg_right (by linarith) hRt.le
    linarith)
  obtain ⟨f3, hf3, hle3⟩ := kkt_dir hY hC hopt hbud hq 0 1 (Rt * ξ * p)
  have h3 : IsLocalMax f3 0 := by
    filter_upwards [hle3] with t ht
    refine ht ?_
    have : (b₀ + Rt * ξ * p * t) / Rt = b₀ / Rt + ξ * p * t := by field_simp
    rw [this]
    nlinarith
  have e3 := h3.hasDerivAt_eq_zero hf3
  have e4 : b₀ / Rt < ξ * p * k₀ →
      (cfPhiD κ φ d₀)⁻¹ * (Fl * 0 - w * 0 + 1 / Rt - p * 0) + C' (0, 1) = 0 := by
    intro hs
    obtain ⟨f4, hf4, hle4⟩ := kkt_dir hY hC hopt hbud hq 0 0 1
    have hc : ContinuousAt (fun t : ℝ => ξ * p * (k₀ + 0 * t) - (b₀ + 1 * t) / Rt) 0 := by
      fun_prop
    have hpos : 0 < ξ * p * (k₀ + 0 * 0) - (b₀ + 1 * 0) / Rt := by simp; linarith
    have h4 : IsLocalMax f4 0 := by
      filter_upwards [hle4, hc.eventually_const_lt hpos] with t ht ht2
      exact ht (by linarith)
    have := h4.hasDerivAt_eq_zero hf4
    rw [kkt_clm_apply C' 0 1] at this
    linear_combination this
  rw [kkt_clm_apply] at e1 e2 e3
  have hRi : Rt * Rt⁻¹ = 1 := mul_inv_cancel₀ hRt.ne'
  have hRR : Rt * ξ * p / Rt = ξ * p := by field_simp
  rw [hRR] at e3
  generalize cfPhiD κ φ d₀ = q at hq e1 e2 e3 e4 ⊢
  generalize C' (1, 0) = Ck at e1 e2 e3 e4 ⊢
  generalize C' (0, 1) = Cb at e1 e2 e3 e4 ⊢
  have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq.ne'
  have hμ : 1 + Rt * Cb * q = Rt * q * (q⁻¹ / Rt + Cb) := by
    linear_combination (-1 : ℝ) * hqq + (-(q * q⁻¹)) * hRi
  have hl : Fl = w := by
    have : q⁻¹ * (Fl - w) = 0 := by linear_combination e1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (inv_pos.2 hq).ne'
    · linarith
  refine ⟨hl, 1 + Rt * Cb * q, ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ q⁻¹ / Rt + Cb := by
      have : q⁻¹ * (Fl * 0 - w * 0 + -1 / Rt - p * 0) + (0 * Ck + -1 * Cb) =
          -(q⁻¹ / Rt + Cb) := by ring
      linarith
    rw [hμ]
    exact mul_nonneg (mul_nonneg hRt.le hq.le) this
  · rcases hfeas.lt_or_eq with hs | hs
    · have h2 : q⁻¹ / Rt + Cb = 0 := by linear_combination e4 hs
      rw [hμ, h2]
      ring
    · rw [hs]
      ring
  · linear_combination e3 + (Rt * Cb * ξ * p) * hqq
  · linear_combination (-Cb) * hqq + (-Cb * q * q⁻¹) * hRi

/-! ### (19.5)–(19.6) -/

variable {S : Type*} [Fintype S]

/-- **(19.5)** (AKMM, p. 575, via Appendix 19.A.1). From the first-order condition for `k′`,
`E[m′Ω_k′] − λp + μλξp = 0`, the updated envelope condition
`Ω_k(s) = λₛ[(1 − δ)p′ₛ + F_k(s)]`, `1 = λϕ′(d)` and `1 = λₛϕ′(d′ₛ)`:
`E[m′(ϕ′(d)/ϕ′(d′))((1 − δ)p′ + F_k′)] = (1 − μξ)p`. Here `q = ϕ′(d)`, `q′ₛ = ϕ′(d′ₛ)`. -/
theorem eq_19_5 (pr m lams Ωk p' Fk q' : S → ℝ) (lam q μ ξ p δ : ℝ) (hq : 1 = lam * q)
    (hqs : ∀ s, 1 = lams s * q' s)
    (hfoc : ∑ s, pr s * (m s * Ωk s) - lam * p + μ * lam * ξ * p = 0)
    (henv : ∀ s, Ωk s = lams s * ((1 - δ) * p' s + Fk s)) :
    ∑ s, pr s * (m s * (q / q' s * ((1 - δ) * p' s + Fk s))) = (1 - μ * ξ) * p := by
  have hlam : lam ≠ 0 := by rintro h; rw [h] at hq; simp at hq
  have hrat : ∀ s, q / q' s = lams s / lam := by
    intro s
    have hq's : q' s ≠ 0 := by rintro h; have := hqs s; rw [h] at this; simp at this
    field_simp
    linear_combination (hqs s) - hq
  have e : ∑ s, pr s * (m s * (q / q' s * ((1 - δ) * p' s + Fk s))) =
      (∑ s, pr s * (m s * Ωk s)) / lam := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hrat, henv]
    field_simp
  rw [e, div_eq_iff hlam]
  linear_combination hfoc

/-- **(19.6)** (AKMM, p. 575, via Appendix 19.A.1). From the first-order condition for `b′`,
`E[m′Ω_b′] + λ/R̃ − μλ/R̃ = 0`, the updated envelope condition `Ω_b(s) = −λₛ`, `1 = λϕ′(d)` and
`1 = λₛϕ′(d′ₛ)`: `E[m′(ϕ′(d)/ϕ′(d′))]R̃ = 1 − μ`. -/
theorem eq_19_6 (pr m lams Ωb q' : S → ℝ) (lam q μ Rt : ℝ) (hRt : Rt ≠ 0) (hq : 1 = lam * q)
    (hqs : ∀ s, 1 = lams s * q' s)
    (hfoc : ∑ s, pr s * (m s * Ωb s) + lam / Rt - μ * lam / Rt = 0)
    (henv : ∀ s, Ωb s = -lams s) :
    (∑ s, pr s * (m s * (q / q' s))) * Rt = 1 - μ := by
  have hlam : lam ≠ 0 := by rintro h; rw [h] at hq; simp at hq
  have hrat : ∀ s, q / q' s = lams s / lam := by
    intro s
    have hq's : q' s ≠ 0 := by rintro h; have := hqs s; rw [h] at this; simp at this
    field_simp
    linear_combination (hqs s) - hq
  have e : ∑ s, pr s * (m s * (q / q' s)) = -(∑ s, pr s * (m s * Ωb s)) / lam := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hrat, henv]
    ring
  have hRi : Rt * Rt⁻¹ = 1 := mul_inv_cancel₀ hRt
  rw [e, div_mul_eq_mul_div, div_eq_iff hlam]
  linear_combination (-Rt) * hfoc + (lam * (1 - μ)) * hRi

/-- **(19.4)–(19.6) from optimality** (AKMM, pp. 574–575 and 877). Let `(d₀, ℓ₀, k₀′, b₀′)`
solve (19.3) as in `kkt_firm`, and let the continuation be `C = Σₛ πₛm′ₛΩₛ` where each
next-period value `Ωₛ` is differentiable at `(k₀′, b₀′)` with the envelope derivative of
`env_firm`, `(1/ϕ′(d′ₛ))((F_k(s) + p′ₛ(1 − δ))dk − db)`. Then `F_ℓ = w` (19.4) and there is
`μ ≥ 0`, zero when the limit is slack, with (19.5) and (19.6). -/
theorem firm_focs {Yl : ℝ → ℝ} {Fl : ℝ} {Ω : S → ℝ × ℝ → ℝ} (pr m p' Fk q' : S → ℝ)
    {κ φ w Rt b p δ k ξ ℓ₀ k₀ b₀ d₀ : ℝ} (hRt : 0 < Rt) (hY : HasDerivAt Yl Fl ℓ₀)
    (hΩ : ∀ s, HasFDerivAt (Ω s) ((q' s)⁻¹ • ((Fk s + p' s * (1 - δ)) •
      ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ)) (k₀, b₀))
    (hq' : ∀ s, q' s ≠ 0)
    (hopt : ∀ d ℓ k' b', cfPhi κ φ d = kktRes Yl w Rt b p δ k ℓ k' b' → b' / Rt ≤ ξ * p * k' →
      d + ∑ s, pr s * (m s * Ω s (k', b')) ≤ d₀ + ∑ s, pr s * (m s * Ω s (k₀, b₀)))
    (hbud : cfPhi κ φ d₀ = kktRes Yl w Rt b p δ k ℓ₀ k₀ b₀) (hq : 0 < cfPhiD κ φ d₀)
    (hfeas : b₀ / Rt ≤ ξ * p * k₀) :
    Fl = w ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ * (ξ * p * k₀ - b₀ / Rt) = 0 ∧
      ∑ s, pr s * (m s * (cfPhiD κ φ d₀ / q' s * ((1 - δ) * p' s + Fk s))) =
        (1 - μ * ξ) * p ∧
      (∑ s, pr s * (m s * (cfPhiD κ φ d₀ / q' s))) * Rt = 1 - μ := by
  set L : S → ℝ × ℝ →L[ℝ] ℝ := fun s => (q' s)⁻¹ • ((Fk s + p' s * (1 - δ)) •
      ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ) with hL
  have hC : HasFDerivAt (fun x => ∑ s, pr s * (m s * Ω s x))
      (∑ s, (pr s * m s) • L s) (k₀, b₀) := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun s _ => (hΩ s).const_mul (pr s * m s))
    convert this using 1
    funext x
    exact Finset.sum_congr rfl fun s _ => by ring
  obtain ⟨hl, μ, hμ, hcs, hk, hb⟩ := kkt_firm hRt hY hC hopt hbud hq hfeas
  refine ⟨hl, μ, hμ, hcs, ?_, ?_⟩
  · refine eq_19_5 pr m (fun s => (q' s)⁻¹) (fun s => (q' s)⁻¹ * ((1 - δ) * p' s + Fk s)) p' Fk
      q' (cfPhiD κ φ d₀)⁻¹ (cfPhiD κ φ d₀) μ ξ p δ (inv_mul_cancel₀ hq.ne').symm
      (fun s => (inv_mul_cancel₀ (hq' s)).symm) ?_ (fun _ => rfl)
    rw [← hk]
    congr 1
    congr 1
    simp only [hL, sum_apply, smul_apply, sub_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
      mul_one, ContinuousLinearMap.coe_snd', sub_zero]
    exact Finset.sum_congr rfl fun s _ => by ring
  · refine eq_19_6 pr m (fun s => (q' s)⁻¹) (fun s => -(q' s)⁻¹) q' (cfPhiD κ φ d₀)⁻¹
      (cfPhiD κ φ d₀) μ Rt hRt.ne' (inv_mul_cancel₀ hq.ne').symm
      (fun s => (inv_mul_cancel₀ (hq' s)).symm) ?_ (fun _ => rfl)
    rw [← hb]
    congr 1
    congr 1
    simp only [mul_neg, Finset.sum_neg_distrib, hL, sum_apply, smul_apply, sub_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul, mul_zero, ContinuousLinearMap.coe_snd', zero_sub,
      mul_one, neg_inj]
    exact Finset.sum_congr rfl fun s _ => by ring

end AKMM.CreditFrictions
