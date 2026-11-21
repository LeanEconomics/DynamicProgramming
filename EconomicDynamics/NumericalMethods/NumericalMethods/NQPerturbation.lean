/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Perturbation methods: recursive utility with unit EIS (Miao, §11.4, pp. 366–369)

Miao, §11.4 (the example of Hansen, Heaton and Li (2008)): recursive utility (11.3)
`V_t = [(1 − β) C_t^{1−ρ} + β R_t(V_{t+1})^{1−ρ}]^{1/(1−ρ)}`,
`R_t(V_{t+1}) = (E_t V_{t+1}^{1−γ})^{1/(1−γ)}`, is solved by perturbing the EIS parameter `ρ`
around the special case `ρ = 1`.

* `eq_11_4`: in logs, `v_t = ln(V_t/C_t)` satisfies (11.4)
  `v_t = (1 − ρ)^{−1} ln((1 − β) + β exp[(1 − ρ) Q_t(v_{t+1} + c_{t+1} − c_t)])`,
  `Q_t(y) = (1 − γ)^{−1} ln E_t exp[(1 − γ) y]` (`nqQ`; `nqCertEquiv` is `R_t`).
* `eq_11_5`: as `ρ → 1` the right side of (11.4) tends to `β Q_t(·)`: the unit-EIS equation
  (11.5) `v_t = β Q_t(v_{t+1} + c_{t+1} − c_t)`.
* `eq_11_7_s` (the perturbation step, in `s = 1 − ρ`): if `s v(s) = ln((1 − β) + β e^{s q(s)})`
  near `s = 0` (this is (11.4) multiplied by `1 − ρ`, i.e. `F(v_t(ρ), v_{t+1}(ρ), ρ) = 0`, with
  `q(s) = Q_t(v_{t+1}(ρ) + c_{t+1} − c_t)`) and `v`, `q` are twice differentiable, then
  differentiating twice at `s = 0` gives `v(0) = β q(0)` ((11.5)) and
  `v'(0) = β q'(0) + β(1 − β) q(0)²/2`. `eq_11_7` restates this in `ρ` as the book's (11.7)
  `v_t'(1) = −β(1 − β)/2 · Q_t(·)² + β Ẽ_t v_{t+1}'(1)`, given `q'(0) = −Ẽ_t v_{t+1}'(1)`.
* `nq_pert_taylor_first_order`: the first-order approximation `v_t(ρ) ≃ v_t(1) + (ρ − 1)v_t'(1)`
  has error `o(ρ − 1)`.
* `nq_Q_hasDerivAt`: the derivative of `Q_t` along `Y₀ + s Y₁` at `s = 0` is the expectation
  of `Y₁` under the tilted density `e^{(1−γ)Y₀}/E e^{(1−γ)Y₀}` (differentiation under the
  integral sign, with an integrable dominating function): this is the book's `Ẽ_t`, whose
  density `V_{t+1}(1)^{1−γ}/E_t V_{t+1}(1)^{1−γ}` equals `e^{(1−γ)Y₀}/E_t e^{(1−γ)Y₀}` for
  `Y₀ = v_{t+1}(1) + c_{t+1} − c_t = ln(V_{t+1}(1)/C_t)`.

**Departures.** Expectations `E_t` are integrals over a probability space `(Ω, P)` (next-period
shocks). The book's `F₁, F₂, F₃` chain rule is replaced by differentiating the identity
`s v(s) = h(s q(s))`, `h(u) = ln((1 − β) + β eᵘ)`; the smoothness of `ρ ↦ v_t(ρ)` is assumed as
in the book. `nq_Q_hasDerivAt` treats families affine in `s`, which is what the first
derivative sees. The closed form for the example is in `NQPerturbationExercise`.
-/

namespace Miao.NumericalMethods

open MeasureTheory Filter Topology Asymptotics

/-- Miao, p. 367: the certainty equivalent `R_t(V_{t+1}) = (E_t V_{t+1}^{1−γ})^{1/(1−γ)}`. -/
noncomputable def nqCertEquiv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (V : Ω → ℝ) : ℝ :=
  (∫ ω, V ω ^ (1 - γ) ∂P) ^ (1 / (1 - γ))

/-- Miao, p. 368: `Q_t(y) = (1 − γ)^{−1} ln E_t exp[(1 − γ) y]`. -/
noncomputable def nqQ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (y : Ω → ℝ) : ℝ :=
  1 / (1 - γ) * Real.log (∫ ω, Real.exp ((1 - γ) * y ω) ∂P)

/-- Miao, (11.4), p. 368: with `V_t` given by (11.3) from `C_t > 0` and a positive next-period
utility `V_{t+1}`, `v_t = ln(V_t/C_t)` satisfies
`v_t = (1 − ρ)^{−1} ln((1 − β) + β exp[(1 − ρ) Q_t(v_{t+1} + c_{t+1} − c_t)])`,
where `v_{t+1} = ln(V_{t+1}/C_{t+1})`, `c = ln C`. -/
theorem eq_11_4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β γ ρ C : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : γ ≠ 1) (hρ : ρ ≠ 1) (hC : 0 < C)
    {V' C' : Ω → ℝ} (hV' : ∀ ω, 0 < V' ω) (hC' : ∀ ω, 0 < C' ω)
    (hint : Integrable (fun ω => V' ω ^ (1 - γ)) P) :
    Real.log (((1 - β) * C ^ (1 - ρ) + β * nqCertEquiv P γ V' ^ (1 - ρ)) ^ (1 / (1 - ρ)) / C) =
      1 / (1 - ρ) * Real.log ((1 - β) + β * Real.exp ((1 - ρ) *
        nqQ P γ (fun ω => Real.log (V' ω / C' ω) + Real.log (C' ω) - Real.log C))) := by
  have hγ' : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have hρ' : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  set I : ℝ := ∫ ω, V' ω ^ (1 - γ) ∂P
  have hVexp : ∀ ω, V' ω ^ (1 - γ) = Real.exp ((1 - γ) * Real.log (V' ω)) := fun ω => by
    rw [Real.rpow_def_of_pos (hV' ω), mul_comm]
  have hI : 0 < I := by
    have hint' : Integrable (fun ω => Real.exp ((1 - γ) * Real.log (V' ω))) P := by
      simpa only [hVexp] using hint
    simpa only [I, hVexp] using integral_exp_pos hint'
  -- the integral defining `Q_t`
  have hy : ∀ ω, Real.exp ((1 - γ) * (Real.log (V' ω / C' ω) + Real.log (C' ω) - Real.log C)) =
      V' ω ^ (1 - γ) * Real.exp (-(1 - γ) * Real.log C) := by
    intro ω
    rw [hVexp, ← Real.exp_add, Real.log_div (hV' ω).ne' (hC' ω).ne']
    congr 1; ring
  have hM : ∫ ω, Real.exp ((1 - γ) *
      (Real.log (V' ω / C' ω) + Real.log (C' ω) - Real.log C)) ∂P =
      I * Real.exp (-(1 - γ) * Real.log C) := by
    simp only [hy]
    rw [integral_mul_const]
  have hQ : nqQ P γ (fun ω => Real.log (V' ω / C' ω) + Real.log (C' ω) - Real.log C) =
      1 / (1 - γ) * Real.log I - Real.log C := by
    rw [nqQ, hM, Real.log_mul hI.ne' (Real.exp_pos _).ne', Real.log_exp]
    field_simp
    ring
  -- `log R = log I / (1 − γ)`
  set R : ℝ := nqCertEquiv P γ V'
  have hR : 0 < R := Real.rpow_pos_of_pos hI _
  have hlogR : Real.log R = 1 / (1 - γ) * Real.log I := by
    simp only [R, nqCertEquiv]
    rw [Real.log_rpow hI]
  set S : ℝ := (1 - β) * C ^ (1 - ρ) + β * R ^ (1 - ρ)
  have hS : 0 < S := by
    have := Real.rpow_pos_of_pos hC (1 - ρ)
    have := Real.rpow_pos_of_pos hR (1 - ρ)
    have : 0 < 1 - β := by linarith
    positivity
  have hinside : (1 - β) + β * Real.exp ((1 - ρ) *
      nqQ P γ (fun ω => Real.log (V' ω / C' ω) + Real.log (C' ω) - Real.log C)) =
      S / Real.exp ((1 - ρ) * Real.log C) := by
    rw [hQ, ← hlogR]
    simp only [S]
    rw [Real.rpow_def_of_pos hC, Real.rpow_def_of_pos hR]
    have he : Real.exp ((1 - ρ) * (Real.log R - Real.log C)) =
        Real.exp (Real.log R * (1 - ρ)) / Real.exp ((1 - ρ) * Real.log C) := by
      rw [← Real.exp_sub]; congr 1; ring
    rw [he, mul_comm (Real.log C) (1 - ρ)]
    field_simp
  rw [hinside, Real.log_div hS.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_div (Real.rpow_pos_of_pos hS _).ne' hC.ne', Real.log_rpow hS]
  field_simp

/-- Miao, (11.5), p. 368: as `ρ → 1` the right side of (11.4) tends to `β Q`: for every value
`q` of `Q_t(v_{t+1} + c_{t+1} − c_t)`,
`(1 − ρ)^{−1} ln((1 − β) + β e^{(1−ρ)q}) → β q` (the unit-EIS equation (11.5)); no restriction
on `β` is needed. -/
theorem eq_11_5 (β q : ℝ) :
    Tendsto (fun ρ => 1 / (1 - ρ) * Real.log ((1 - β) + β * Real.exp ((1 - ρ) * q)))
      (𝓝[≠] 1) (𝓝 (β * q)) := by
  have hk : HasDerivAt (fun s => (1 - β) + β * Real.exp (s * q)) (β * (Real.exp (0 * q) * q)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const q).exp.const_mul β).const_add (1 - β) |>.congr_deriv
      (by simp)
  have hk0 : (1 - β) + β * Real.exp (0 * q) = 1 := by simp
  have hg : HasDerivAt (fun s => Real.log ((1 - β) + β * Real.exp (s * q))) (β * q) 0 := by
    have := hk.log (by rw [hk0]; exact one_ne_zero)
    rw [hk0] at this
    simpa using this
  have hslope := hg.tendsto_slope_zero
  have hsub : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_const.sub continuous_id).tendsto' 1 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun ρ hρ => sub_ne_zero.mpr (Ne.symm hρ)
  refine (hslope.comp hsub).congr fun ρ => ?_
  simp only [Function.comp_apply, zero_add, smul_eq_mul, zero_mul, Real.exp_zero, mul_one,
    sub_add_cancel, Real.log_one, sub_zero, one_div]

/-- Miao, p. 369 ("by Taylor expansion, the approximate solution is given by
`v_t(ρ) ≃ v_t(1) + (ρ − 1) v_t'(1)`"): if `v_t` is differentiable at `ρ = 1` the error of the
first-order approximation is `o(ρ − 1)`. -/
theorem nq_pert_taylor_first_order {v : ℝ → ℝ} {v1 : ℝ} (hv : HasDerivAt v v1 1) :
    (fun ρ => v ρ - (v 1 + (ρ - 1) * v1)) =o[𝓝 1] fun ρ => ρ - 1 := by
  have h := hasDerivAt_iff_isLittleO.mp hv
  refine h.congr_left fun ρ => ?_
  simp only [smul_eq_mul]
  ring

/-- `h(u) = ln((1 − β) + β eᵘ)` has derivative `β eᵘ/((1 − β) + β eᵘ)`. -/
theorem nq_h_hasDerivAt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.log ((1 - β) + β * Real.exp u))
      (β * Real.exp u / ((1 - β) + β * Real.exp u)) u := by
  have hpos : 0 < (1 - β) + β * Real.exp u := by
    have := Real.exp_pos u; nlinarith
  exact ((Real.hasDerivAt_exp u).const_mul β).const_add (1 - β) |>.log hpos.ne'

/-- `h'(u) = β eᵘ/((1 − β) + β eᵘ)` has derivative `β(1 − β)` at `u = 0`. -/
theorem nq_h'_hasDerivAt_zero {β : ℝ} :
    HasDerivAt (fun u => β * Real.exp u / ((1 - β) + β * Real.exp u)) (β * (1 - β)) 0 := by
  have h1 := (Real.hasDerivAt_exp 0).const_mul β
  have h2 := ((Real.hasDerivAt_exp 0).const_mul β).const_add (1 - β)
  have hd := h1.div h2 (by simp)
  simp only [Real.exp_zero, mul_one, sub_add_cancel, one_pow, div_one] at hd
  convert hd using 1
  ring

/-- Miao, (11.7), p. 369 (the perturbation step, in `s = 1 − ρ`): if
`s v(s) = ln((1 − β) + β e^{s q(s)})` for `s` near `0` — equation (11.4) multiplied by `1 − ρ`,
i.e. `F(v_t(ρ), v_{t+1}(ρ), ρ) = 0`, with `v(s) = v_t(1 − s)` and
`q(s) = Q_t(v_{t+1}(1 − s) + c_{t+1} − c_t)` — and `v`, `q` are twice differentiable at `0`,
then differentiating once and twice at `s = 0` gives `v(0) = β q(0)` (equation (11.5)) and
`v'(0) = β q'(0) + β(1 − β) q(0)²/2`. -/
theorem eq_11_7_s {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {v q v1 q1 : ℝ → ℝ} {v2 q2 : ℝ}
    (hv : ∀ᶠ s in 𝓝 0, HasDerivAt v (v1 s) s) (hq : ∀ᶠ s in 𝓝 0, HasDerivAt q (q1 s) s)
    (hv1 : HasDerivAt v1 v2 0) (hq1 : HasDerivAt q1 q2 0)
    (hid : ∀ᶠ s in 𝓝 0, s * v s = Real.log ((1 - β) + β * Real.exp (s * q s))) :
    v 0 = β * q 0 ∧ v1 0 = β * q1 0 + β * (1 - β) / 2 * q 0 ^ 2 := by
  set hp : ℝ → ℝ := fun u => β * Real.exp u / ((1 - β) + β * Real.exp u)
  -- first derivatives of both sides agree near `0`
  have hD : ∀ᶠ s in 𝓝 0, v s + s * v1 s = hp (s * q s) * (q s + s * q1 s) := by
    filter_upwards [hv, hq, eventually_eventually_nhds.mpr hid] with s hvs hqs hids
    have hL : HasDerivAt (fun t => t * v t) (v s + s * v1 s) s :=
      ((hasDerivAt_id s).mul hvs).congr_deriv (by simp)
    have hm : HasDerivAt (fun t => t * q t) (q s + s * q1 s) s :=
      ((hasDerivAt_id s).mul hqs).congr_deriv (by simp)
    have hR : HasDerivAt (fun t => Real.log ((1 - β) + β * Real.exp (t * q t)))
        (hp (s * q s) * (q s + s * q1 s)) s :=
      by have h3 := (nq_h_hasDerivAt hβ0 hβ1 (s * q s)).comp s hm; exact h3
    exact hL.unique (hR.congr_of_eventuallyEq hids)
  have hp0 : hp 0 = β := by simp [hp]
  refine ⟨?_, ?_⟩
  · have := hD.self_of_nhds
    simp only [zero_mul, add_zero, hp0] at this
    exact this
  · -- second derivatives at `0`
    have hv0 : HasDerivAt v (v1 0) 0 := hv.self_of_nhds
    have hq0 : HasDerivAt q (q1 0) 0 := hq.self_of_nhds
    have hDL : HasDerivAt (fun s => v s + s * v1 s) (2 * v1 0) 0 :=
      (hv0.add ((hasDerivAt_id 0).mul hv1)).congr_deriv (by simp; ring)
    have hm0 : HasDerivAt (fun t => t * q t) (q 0) 0 :=
      ((hasDerivAt_id 0).mul hq0).congr_deriv (by simp)
    have hhp : HasDerivAt (fun s => hp (s * q s)) (β * (1 - β) * q 0) 0 := by
      have := (nq_h'_hasDerivAt_zero (β := β)).comp_of_eq 0 hm0 (by simp)
      exact this
    have hlin : HasDerivAt (fun s => q s + s * q1 s) (2 * q1 0) 0 :=
      (hq0.add ((hasDerivAt_id 0).mul hq1)).congr_deriv (by simp; ring)
    have hDR : HasDerivAt (fun s => hp (s * q s) * (q s + s * q1 s))
        (β * (1 - β) * q 0 * q 0 + β * (2 * q1 0)) 0 := by
      have := hhp.mul hlin
      simp only [zero_mul, hp0, add_zero] at this
      exact this
    have := hDL.unique (hDR.congr_of_eventuallyEq hD)
    linarith

/-- Miao, (11.7), p. 369: in terms of `ρ` (`v_t(ρ) = v(1 − ρ)`, so `v_t'(1) = −v'(0)`), and with
`q'(0) = −Ẽ_t v_{t+1}'(1)` (`nq_Q_hasDerivAt`),
`v_t'(1) = −β(1 − β)/2 · [Q_t(v_{t+1}(1) + c_{t+1} − c_t)]² + β Ẽ_t v_{t+1}'(1)`. -/
theorem eq_11_7 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {v q v1 q1 : ℝ → ℝ} {v2 q2 Et : ℝ}
    (hv : ∀ᶠ s in 𝓝 0, HasDerivAt v (v1 s) s) (hq : ∀ᶠ s in 𝓝 0, HasDerivAt q (q1 s) s)
    (hv1 : HasDerivAt v1 v2 0) (hq1 : HasDerivAt q1 q2 0)
    (hid : ∀ᶠ s in 𝓝 0, s * v s = Real.log ((1 - β) + β * Real.exp (s * q s)))
    (hE : q1 0 = -Et) :
    -v1 0 = -(β * (1 - β)) / 2 * q 0 ^ 2 + β * Et := by
  have h := (eq_11_7_s hβ0 hβ1 hv hq hv1 hq1 hid).2
  rw [h, hE]
  ring

/-- Miao, p. 369 (the tilted expectation `Ẽ_t`): along `Y₀ + s Y₁`,
`d/ds Q_t(Y₀ + s Y₁)|_{s=0} = E[Y₁ e^{(1−γ)Y₀}]/E[e^{(1−γ)Y₀}]`, the expectation of `Y₁` under the
density `e^{(1−γ)Y₀}/E e^{(1−γ)Y₀}` (given an integrable dominating function). -/
theorem nq_Q_hasDerivAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} (hγ : γ ≠ 1) {Y0 Y1 : Ω → ℝ} (hY0 : AEStronglyMeasurable Y0 P)
    (hY1 : AEStronglyMeasurable Y1 P)
    (hB : Integrable (fun ω => Real.exp ((1 - γ) * Y0 ω + |1 - γ| * |Y1 ω|)) P)
    (hB' : Integrable (fun ω => |Y1 ω| * Real.exp ((1 - γ) * Y0 ω + |1 - γ| * |Y1 ω|)) P) :
    HasDerivAt (fun s => nqQ P γ (fun ω => Y0 ω + s * Y1 ω))
      ((∫ ω, Y1 ω * Real.exp ((1 - γ) * Y0 ω) ∂P) / ∫ ω, Real.exp ((1 - γ) * Y0 ω) ∂P) 0 := by
  set c : ℝ := 1 - γ with hc
  have hc0 : c ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  set F : ℝ → Ω → ℝ := fun s ω => Real.exp (c * (Y0 ω + s * Y1 ω))
  set F' : ℝ → Ω → ℝ := fun s ω => c * Y1 ω * Real.exp (c * (Y0 ω + s * Y1 ω))
  have hmeasF : ∀ s, AEStronglyMeasurable (F s) P := fun s =>
    Real.continuous_exp.comp_aestronglyMeasurable ((hY0.add (hY1.const_mul s)).const_mul c)
  have hle : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ ω,
      Real.exp (c * (Y0 ω + s * Y1 ω)) ≤ Real.exp (c * Y0 ω + |c| * |Y1 ω|) := by
    intro s hs ω
    apply Real.exp_le_exp.mpr
    have hs' : |s| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs; exact hs.le
    have : c * (s * Y1 ω) ≤ |c| * |Y1 ω| := by
      calc c * (s * Y1 ω) ≤ |c * (s * Y1 ω)| := le_abs_self _
        _ = |c| * (|s| * |Y1 ω|) := by rw [abs_mul, abs_mul]
        _ ≤ |c| * (1 * |Y1 ω|) := by gcongr
        _ = |c| * |Y1 ω| := by ring
    linarith [mul_add c (Y0 ω) (s * Y1 ω)]
  have hint0 : Integrable (F 0) P := by
    refine hB.mono' (hmeasF 0) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hle 0 (Metric.mem_ball_self one_pos) ω
  have hmeasF' : AEStronglyMeasurable (F' 0) P :=
    ((hY1.const_mul c).mul (hmeasF 0))
  have hbound : ∀ᵐ ω ∂P, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖F' s ω‖ ≤ |c| * (|Y1 ω| * Real.exp (c * Y0 ω + |c| * |Y1 ω|)) := by
    refine ae_of_all _ fun ω s hs => ?_
    simp only [F', Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have := hle s hs ω
    have h1 : 0 ≤ |c| * |Y1 ω| := by positivity
    calc |c| * |Y1 ω| * Real.exp (c * (Y0 ω + s * Y1 ω))
        ≤ |c| * |Y1 ω| * Real.exp (c * Y0 ω + |c| * |Y1 ω|) :=
          mul_le_mul_of_nonneg_left this h1
      _ = |c| * (|Y1 ω| * Real.exp (c * Y0 ω + |c| * |Y1 ω|)) := by ring
  have hdiff : ∀ᵐ ω ∂P, ∀ s ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (F · ω) (F' s ω) s := by
    refine ae_of_all _ fun ω s _ => ?_
    have := ((((hasDerivAt_id s).mul_const (Y1 ω)).const_add (Y0 ω)).const_mul c).exp
    exact this.congr_deriv (by simp [F']; ring)
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) (Eventually.of_forall hmeasF) hint0 hmeasF'
    hbound (hB'.const_mul |c|) hdiff).2
  have hF0 : ∫ ω, F 0 ω ∂P = ∫ ω, Real.exp (c * Y0 ω) ∂P := by simp [F]
  have hpos : 0 < ∫ ω, F 0 ω ∂P := integral_exp_pos hint0
  have hF'0 : ∫ ω, F' 0 ω ∂P = c * ∫ ω, Y1 ω * Real.exp (c * Y0 ω) ∂P := by
    rw [← integral_const_mul]
    congr 1; funext ω; simp [F']; ring
  have hlog := (hmain.log hpos.ne').const_mul (1 / c)
  refine hlog.congr_deriv ?_
  rw [hF'0, hF0]
  rw [hF0] at hpos
  field_simp

end Miao.NumericalMethods
