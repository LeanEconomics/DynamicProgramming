/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The worst-case distortion and the risk-sensitive operator

Miao, §9.6, pp. 319–321, (9.47)–(9.49). Fix a state `x` and control `u`; the shock `ε` has law
`ν` (the density `π`) and `W(ε) = V(f(x, u, ε))` is the continuation value. The minimising agent
chooses a likelihood ratio `m(ε) ≥ 0` with `E m = 1` (`rcAdm`) to minimise
`∫ (m W + θ m ln m) dν` (`rcObj`).

* `eq_9_47_9_48` (Gibbs variational principle): for `θ > 0` with `E exp(−W/θ) < ∞`, the minimiser is
  `m* = exp(−W/θ)/E exp(−W/θ)` (9.47) (`rcWorst`), uniquely (a.e.), and the minimum is
  `R(V) = −θ ln E exp(−W/θ)` (9.48) (`rcR`).
* `eq_9_47_foc`, `eq_9_47_log`: the first-order condition. The derivative of the pointwise
  integrand `mW + θ m ln m` at `m*(ε)` is the same constant `θ(1 − ln E exp(−W/θ))` for every `ε`
  (the Lagrange multiplier of `E m = 1`), i.e. `ln m*(ε) = −W(ε)/θ + λ`. The book prints
  `m*(ε) = −V(f(x, u, ε))/θ + λ`; `eq_9_47_misprint` shows that the printed rule can give a
  negative "likelihood ratio".
* `rc_R_le_mean` (p. 320): `R(V) ≤ E W`: the adjustment is a risk-sensitive certainty equivalent,
  `1/θ` enhancing risk aversion.
* `eq_9_49` (p. 320): the recursive multiplier problem
  `V(x) = max_u {r(x, u) + β min_m ∫ (m V(f) + θ m ln m) π}` is the risk-sensitive problem
  `V(x) = max_u {r(x, u) + βR(V)(x, u)}`.

The entropy term uses Lean's `0 · ln 0 = 0`; admissible distortions must have an integrable
objective (otherwise the book's integral is not defined).
-/

open MeasureTheory Real

namespace Miao.LinearQuadratic

variable {Eps : Type*} [MeasurableSpace Eps]

/-- The admissible likelihood ratios: measurable, nonnegative, `E m = 1`, and the objective
`m W + θ m ln m` integrable. -/
def rcAdm (ν : Measure Eps) (W : Eps → ℝ) (θ : ℝ) : Set (Eps → ℝ) :=
  {m | Measurable m ∧ (∀ e, 0 ≤ m e) ∧ Integrable m ν ∧ ∫ e, m e ∂ν = 1 ∧
    Integrable (fun e => m e * W e + θ * (m e * log (m e))) ν}

/-- The inner objective `∫ (m(ε)W(ε) + θ m(ε) ln m(ε)) π(ε) dε` (Miao, p. 320). -/
noncomputable def rcObj (ν : Measure Eps) (W : Eps → ℝ) (θ : ℝ) (m : Eps → ℝ) : ℝ :=
  ∫ e, (m e * W e + θ * (m e * log (m e))) ∂ν

/-- The normaliser `∫ exp(−W/θ) π`. -/
noncomputable def rcZ (ν : Measure Eps) (W : Eps → ℝ) (θ : ℝ) : ℝ := ∫ e, exp (-W e / θ) ∂ν

/-- The worst-case likelihood ratio (9.47): `m*(ε) = exp(−W(ε)/θ)/∫ exp(−W/θ) π`. -/
noncomputable def rcWorst (ν : Measure Eps) (W : Eps → ℝ) (θ : ℝ) (e : Eps) : ℝ :=
  exp (-W e / θ) / rcZ ν W θ

/-- The risk-sensitive adjustment (9.48): `R(V) = −θ ln ∫ exp(−W/θ) π`. -/
noncomputable def rcR (ν : Measure Eps) (W : Eps → ℝ) (θ : ℝ) : ℝ := -θ * log (rcZ ν W θ)

/-- The pointwise identity behind (9.47)–(9.48): with `b > 0`,
`a ln a − a ln b = b·klFun(a/b) + a − b`, where `klFun x = x ln x + 1 − x ≥ 0`. -/
theorem rc_mul_log_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a * log a - a * log b = b * InformationTheory.klFun (a / b) + a - b := by
  rw [InformationTheory.klFun_apply]
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_div h.ne' hb.ne']
    field_simp
    ring

variable (ν : Measure Eps) [IsProbabilityMeasure ν]

theorem rcZ_pos {W : Eps → ℝ} {θ : ℝ} (hZ : Integrable (fun e => exp (-W e / θ)) ν) :
    0 < rcZ ν W θ :=
  integral_exp_pos hZ

theorem rcWorst_pos {W : Eps → ℝ} {θ : ℝ} (hZ : Integrable (fun e => exp (-W e / θ)) ν)
    (e : Eps) : 0 < rcWorst ν W θ e :=
  div_pos (exp_pos _) (rcZ_pos ν hZ)

/-- `ln m*(ε) = −W(ε)/θ − ln ∫ exp(−W/θ) π`. -/
theorem rcWorst_log {W : Eps → ℝ} {θ : ℝ} (hZ : Integrable (fun e => exp (-W e / θ)) ν)
    (e : Eps) : log (rcWorst ν W θ e) = -W e / θ - log (rcZ ν W θ) := by
  rw [rcWorst, Real.log_div (exp_pos _).ne' (rcZ_pos ν hZ).ne', log_exp]

/-- **(9.47)–(9.48)** (Miao, p. 320), the Gibbs variational principle: for `θ > 0` and
`∫ exp(−W/θ) π < ∞`, the worst-case ratio `m* = exp(−W/θ)/∫ exp(−W/θ) π` is admissible, it
attains `R(V) = −θ ln ∫ exp(−W/θ) π`, every admissible `m` has objective at least `R(V)`, and
`m*` is the unique minimiser (a.e.). -/
theorem eq_9_47_9_48 {W : Eps → ℝ} {θ : ℝ} (hθ : 0 < θ) (hW : Measurable W)
    (hZ : Integrable (fun e => exp (-W e / θ)) ν) :
    rcWorst ν W θ ∈ rcAdm ν W θ ∧ rcObj ν W θ (rcWorst ν W θ) = rcR ν W θ ∧
      (∀ m ∈ rcAdm ν W θ, rcR ν W θ ≤ rcObj ν W θ m) ∧
      ∀ m ∈ rcAdm ν W θ, rcObj ν W θ m = rcR ν W θ → m =ᵐ[ν] rcWorst ν W θ := by
  have hZp := rcZ_pos ν hZ
  set Z := rcZ ν W θ with hZdef
  set ms := rcWorst ν W θ with hms
  have hmsi : Integrable ms ν := hZ.div_const Z
  have hms1 : ∫ e, ms e ∂ν = 1 := by
    simp only [hms, rcWorst]
    rw [integral_div]
    exact div_self hZp.ne'
  have hmsm : Measurable ms := ((hW.neg.div_const θ).exp).div_const Z
  have hpt : ∀ e, ms e * W e + θ * (ms e * log (ms e)) = -θ * log Z * ms e := by
    intro e
    rw [rcWorst_log ν hZ e]
    field_simp
    ring
  have hobj : rcObj ν W θ ms = rcR ν W θ := by
    simp only [rcObj, hpt, rcR]
    rw [integral_const_mul, hms1, mul_one]
  have hadm : ms ∈ rcAdm ν W θ := by
    refine ⟨hmsm, fun e => (rcWorst_pos ν hZ e).le, hmsi, hms1, ?_⟩
    simp only [hpt]
    exact hmsi.const_mul _
  -- the decomposition of the objective of an admissible `m`
  have hdec : ∀ m : Eps → ℝ, (∀ e, 0 ≤ m e) → ∀ e,
      m e * W e + θ * (m e * log (m e)) =
        θ * (ms e * InformationTheory.klFun (m e / ms e)) + θ * (m e - ms e) -
          θ * log Z * m e := by
    intro m hm0 e
    have h := rc_mul_log_sub (hm0 e) (rcWorst_pos ν hZ e)
    rw [rcWorst_log ν hZ e] at h
    have : θ * (m e * log (m e)) = θ * (ms e * InformationTheory.klFun (m e / ms e) + m e - ms e) +
        θ * (m e * (-W e / θ - log Z)) := by rw [← h]; ring
    rw [this]
    field_simp
    ring
  have hg : ∀ m ∈ rcAdm ν W θ, Integrable
      (fun e => ms e * InformationTheory.klFun (m e / ms e)) ν ∧
      rcObj ν W θ m = θ * ∫ e, ms e * InformationTheory.klFun (m e / ms e) ∂ν + rcR ν W θ := by
    rintro m ⟨-, hm0, hmi, hm1, hoi⟩
    have hgi : Integrable (fun e => ms e * InformationTheory.klFun (m e / ms e)) ν := by
      have h1 : (fun e => ms e * InformationTheory.klFun (m e / ms e)) = fun e =>
          θ⁻¹ * ((m e * W e + θ * (m e * log (m e))) + θ * log Z * m e) - (m e - ms e) := by
        funext e
        rw [hdec m hm0 e]
        field_simp
        ring
      rw [h1]
      exact ((hoi.add (hmi.const_mul _)).const_mul _).sub (hmi.sub hmsi)
    refine ⟨hgi, ?_⟩
    have i1 : Integrable (fun e => θ * (ms e * InformationTheory.klFun (m e / ms e))) ν :=
      hgi.const_mul θ
    have i2 : Integrable (fun e => θ * (m e - ms e)) ν := (hmi.sub hmsi).const_mul θ
    have i3 : Integrable (fun e => θ * log Z * m e) ν := hmi.const_mul _
    simp only [rcObj, hdec m hm0, rcR]
    rw [integral_sub (f := fun e => θ * (ms e * InformationTheory.klFun (m e / ms e)) +
        θ * (m e - ms e)) (i1.add i2) i3,
      integral_add (f := fun e => θ * (ms e * InformationTheory.klFun (m e / ms e))) i1 i2,
      integral_const_mul,
      integral_const_mul, integral_const_mul, integral_sub hmi hmsi, hm1, hms1]
    ring
  have hkl0 : ∀ m ∈ rcAdm ν W θ, ∀ e, 0 ≤ ms e * InformationTheory.klFun (m e / ms e) :=
    fun m hm e => mul_nonneg (rcWorst_pos ν hZ e).le
      (InformationTheory.klFun_nonneg (div_nonneg (hm.2.1 e) (rcWorst_pos ν hZ e).le))
  refine ⟨hadm, hobj, fun m hm => ?_, fun m hm heq => ?_⟩
  · rw [(hg m hm).2]
    have := integral_nonneg (μ := ν)
      (f := fun e => ms e * InformationTheory.klFun (m e / ms e)) fun e => hkl0 m hm e
    nlinarith
  · rw [(hg m hm).2, add_eq_right, mul_eq_zero] at heq
    rcases heq with h | h
    · exact absurd h hθ.ne'
    rw [integral_eq_zero_iff_of_nonneg (hkl0 m hm) (hg m hm).1] at h
    filter_upwards [h] with e he
    have hp := rcWorst_pos ν hZ e
    have he' : ms e * InformationTheory.klFun (m e / ms e) = 0 := he
    rcases mul_eq_zero.1 he' with h0 | h0
    · exact absurd h0 hp.ne'
    rw [InformationTheory.klFun_eq_zero_iff (div_nonneg (hm.2.1 e) hp.le),
      div_eq_one_iff_eq hp.ne'] at h0
    exact h0

/-- The first-order condition of the minimisation (Miao, p. 320), corrected: the derivative of the
pointwise Lagrangian integrand `m ↦ mW(ε) + θ m ln m` at `m*(ε)` is
`W(ε) + θ(ln m*(ε) + 1) = θ(1 − ln ∫ exp(−W/θ) π)`, the same for every `ε` (the multiplier of the
constraint `E m = 1`). -/
theorem eq_9_47_foc {W : Eps → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hZ : Integrable (fun e => exp (-W e / θ)) ν) (e : Eps) :
    HasDerivAt (fun y => y * W e + θ * (y * log y)) (θ * (1 - log (rcZ ν W θ)))
      (rcWorst ν W θ e) := by
  have hp := rcWorst_pos ν hZ e
  have h : HasDerivAt (fun y => y * W e + θ * (y * log y))
      (1 * W e + θ * (log (rcWorst ν W θ e) + 1)) (rcWorst ν W θ e) :=
    ((hasDerivAt_id' (rcWorst ν W θ e)).mul_const (W e)).add
      ((Real.hasDerivAt_mul_log hp.ne').const_mul θ)
  convert h using 1
  rw [rcWorst_log ν hZ e]
  field_simp
  ring

/-- (9.47), the corrected first-order condition: `ln m*(ε) = −W(ε)/θ + λ` with the constant
`λ = −ln ∫ exp(−W/θ) π` chosen so that `E m* = 1`. -/
theorem eq_9_47_log {W : Eps → ℝ} {θ : ℝ} (hZ : Integrable (fun e => exp (-W e / θ)) ν) :
    ∃ lam : ℝ, ∀ e, log (rcWorst ν W θ e) = -W e / θ + lam :=
  ⟨-log (rcZ ν W θ), fun e => by rw [rcWorst_log ν hZ e, sub_eq_add_neg]⟩

/-- The printed first-order condition is false (Miao, p. 320): the book's
`m*(ε) = −V(f(x, u, ε))/θ + λ`, with `λ` chosen so that `E m* = 1`, can be negative. For the
two-point law `ν = (δ_true + δ_false)/2` with `W(true) = 0`, `W(false) = 4θ`, `λ = 3` and the
printed rule takes the value `−1`. -/
theorem eq_9_47_misprint {θ : ℝ} (hθ : 0 < θ) :
    let ν₂ : Measure Bool := (1 / 2 : ENNReal) • (Measure.dirac true + Measure.dirac false)
    let W : Bool → ℝ := fun b => if b then 0 else 4 * θ
    let lam : ℝ := 1 + (∫ b, W b ∂ν₂) / θ
    ∫ b, (-W b / θ + lam) ∂ν₂ = 1 ∧ -W false / θ + lam < 0 := by
  intro ν₂ W lam
  have hint : ∀ f : Bool → ℝ, ∫ b, f b ∂ν₂ = (f true + f false) / 2 := by
    intro f
    simp only [ν₂]
    rw [integral_smul_measure, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
      integral_dirac, integral_dirac]
    simp
    ring
  have hW : ∫ b, W b ∂ν₂ = 2 * θ := by rw [hint]; simp [W]; ring
  have hlam : lam = 3 := by simp only [lam, hW]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [hint, hlam]
    simp only [W, ite_true, Bool.false_eq_true, ite_false]
    field_simp
    ring
  · rw [hlam]
    simp only [W, Bool.false_eq_true, ite_false]
    rw [neg_div, mul_div_assoc, div_self hθ.ne']
    norm_num

/-- Miao, p. 320: the risk-sensitive adjustment is at most the expectation, `R(V) ≤ E W`
(`m = 1` is admissible); `1/θ` acts as extra risk aversion. -/
theorem rc_R_le_mean {W : Eps → ℝ} {θ : ℝ} (hθ : 0 < θ) (hW : Measurable W) (hWi : Integrable W ν)
    (hZ : Integrable (fun e => exp (-W e / θ)) ν) : rcR ν W θ ≤ ∫ e, W e ∂ν := by
  have h1 : (fun _ : Eps => (1 : ℝ)) ∈ rcAdm ν W θ := by
    refine ⟨measurable_const, fun _ => zero_le_one, integrable_const 1, by simp, ?_⟩
    simpa using hWi
  have := (eq_9_47_9_48 ν hθ hW hZ).2.2.1 _ h1
  simpa [rcObj] using this

/-- **(9.49)** (Miao, p. 320): the recursive multiplier problem is the risk-sensitive control
problem. For a return `r`, transition `f` and value `V` with `E exp(−V(f)/θ) < ∞`,
`V(x) = max_u {r(x, u) + βR(V)(x, u)}` iff `V(x) = max_u {r(x, u) + β min_m ∫(mV(f) + θ m ln m) π}`
(the inner minimum taken over admissible likelihood ratios). -/
theorem eq_9_49 {X U : Type*} (r : X → U → ℝ) (f : X → U → Eps → X) (V : X → ℝ) {β θ : ℝ}
    (hθ : 0 < θ) (hmeas : ∀ x u, Measurable fun e => V (f x u e))
    (hint : ∀ x u, Integrable (fun e => exp (-V (f x u e) / θ)) ν) (x : X) :
    IsGreatest (Set.range fun u => r x u + β * rcR ν (fun e => V (f x u e)) θ) (V x) ↔
      ∃ w : U → ℝ, (∀ u, IsLeast (rcObj ν (fun e => V (f x u e)) θ ''
          rcAdm ν (fun e => V (f x u e)) θ) (w u)) ∧
        IsGreatest (Set.range fun u => r x u + β * w u) (V x) := by
  have hR : ∀ u, IsLeast (rcObj ν (fun e => V (f x u e)) θ '' rcAdm ν (fun e => V (f x u e)) θ)
      (rcR ν (fun e => V (f x u e)) θ) := by
    intro u
    obtain ⟨hadm, hobj, hle, -⟩ := eq_9_47_9_48 ν hθ (hmeas x u) (hint x u)
    refine ⟨⟨_, hadm, hobj⟩, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    exact hle m hm
  constructor
  · intro h
    exact ⟨_, hR, h⟩
  · rintro ⟨w, hw, h⟩
    have : w = fun u => rcR ν (fun e => V (f x u e)) θ := funext fun u => (hw u).unique (hR u)
    rw [this] at h
    exact h

end Miao.LinearQuadratic
