/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.EXCARA
import Applications.SIWCTransitionFunctions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exercise 8.11: the Schechtman–Escudero CARA model with AR(1) income

Miao, §8.7, Exercise 11, pp. 289–290: maximise `E Σ −e^{−γc_t}` subject to
`x_{t+1} = R(x_t − c_t) + y_{t+1}`, `y_{t+1} = ρy_t + ε_{t+1}`, `ε` iid with law `ν` on a bounded
interval; solve explicitly, and show that for `ρ = 0` there is no stationary distribution.

* **The solution** (`ex_8_11`). With `κ = ρ/(R − ρ)` and `z = x + κy` ("cash on hand plus the
  annuity value of expected income"), the problem in `(z, s + κy)` is the iid problem of
  Exercise 7.7 with income `ε̃ = (R/(R − ρ))ε` (law `si_arLaw`), because
  `Rs + ρy + ε + κ(ρy + ε) = R(s + κy) + (R/(R − ρ))ε`. Hence `V(x, y) = −Āe^{−ᾱ(x + κy)}`
  (`si_arV`, `ᾱ = γ(1 − 1/R)`) solves the Bellman equation
  `V(x, y) = sup_s −e^{−γ(x − s)} + β E V(Rs + ρy + ε, ρy + ε)`, the supremum is attained only
  at `s(x, y) = s̄(x + κy) − κy` (`si_arSav`), and consumption is
  `c(x, y) = (1 − 1/R)(x + ρy/(R − ρ)) − L̄/(γR)` (`ex_8_11_consumption`), with
  `L̄ = R ln(βRM̄)/(R − 1)` (`si_caraLbar_eq`), `M̄ = E e^{−ᾱε̃}`.
* **`ρ = 0`** (`ex_8_11_rho_zero`): `x_{t+1} = R s(x_t) + ε_{t+1} = x_t + L̄/γ + ε_{t+1}`, a
  random walk; `ex_8_11_no_stationary`: if `L̄/γ + ε` is not almost surely `0`, the
  cash-on-hand process has no stationary distribution (`si_no_stationary`, by characteristic
  functions: `φ_π(t)φ_ξ(t) = φ_π(t)` near `t = 0` forces `ξ = 0`).

**Departures and corrections.** (1) The printed constraint `x_{t+1} = R(x − c_t) + y_t` is read
as `x_{t+1} = R(x_t − c_t) + y_{t+1}` (the timing of §8.3 and Exercise 7.7); "`a₀` given" is
`x₀, y₀` given. We take `ρ < R`. (2) "Explicitly solve the optimal policies" is proved at the
level of the Bellman equation; Exercise 7.7 (`ex_7_7`, `ex_7_7_ponzi`) shows that without a
no-Ponzi condition the policy is optimal only among plans satisfying (7.4), and the value is
not attained otherwise. (3) **The no-stationarity claim is false as stated**: if `ε` is
degenerate at `e₀` and `βR = 1`, then `L̄/γ + e₀ = 0`, the policy keeps cash on hand constant, and
every point mass is stationary (`ex_8_11_counterexample`). It holds iff `L̄/γ + ε` is not a.s.
`0`.
-/

namespace Miao.Applications

open MeasureTheory ProbabilityTheory Filter Topology

/-! ### Exercise 8.11: the Bellman equation with AR(1) income -/

/-- The law of `ε̃ = (R/(R − ρ))ε`. -/
noncomputable def si_arLaw (R ρ : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  ν.map fun e => R / (R - ρ) * e

/-- The value function `V(x, y) = −Āe^{−ᾱ(x + ρy/(R − ρ))}`. -/
noncomputable def si_arV (γ β R ρ : ℝ) (ν : Measure ℝ) (x y : ℝ) : ℝ :=
  -(ex7_caraAlim γ β R (si_arLaw R ρ ν) *
    Real.exp (-(ex7_caraAbar γ R * (x + ρ / (R - ρ) * y))))

/-- The saving policy `s(x, y) = s̄(x + κy) − κy`, `κ = ρ/(R − ρ)`. -/
noncomputable def si_arSav (γ β R ρ : ℝ) (ν : Measure ℝ) (x y : ℝ) : ℝ :=
  ex7_caraSbar γ β R (si_arLaw R ρ ν) (x + ρ / (R - ρ) * y) - ρ / (R - ρ) * y

/-- The Bellman objective `−e^{−γ(x − s)} + β E V(Rs + ρy + ε, ρy + ε)`. -/
noncomputable def si_arObj (γ β R ρ : ℝ) (ν : Measure ℝ) (x y s : ℝ) : ℝ :=
  -Real.exp (-(γ * (x - s))) +
    β * ∫ e, si_arV γ β R ρ ν (R * s + (ρ * y + e)) (ρ * y + e) ∂ν

theorem si_arLaw_ae {R ρ emin emax : ℝ} (hR : 0 < R) (hρ : ρ < R) {ν : Measure ℝ}
    (hν : ∀ᵐ e ∂ν, e ∈ Set.Icc emin emax) :
    ∀ᵐ e ∂si_arLaw R ρ ν, e ∈ Set.Icc (R / (R - ρ) * emin) (R / (R - ρ) * emax) := by
  have hk : 0 ≤ R / (R - ρ) := div_nonneg hR.le (by linarith)
  refine (ae_map_iff (measurable_const_mul _).aemeasurable measurableSet_Icc).2 ?_
  filter_upwards [hν] with e he
  exact ⟨mul_le_mul_of_nonneg_left he.1 hk, mul_le_mul_of_nonneg_left he.2 hk⟩

/-- The objective of Exercise 8.11 is that of Exercise 7.7 in `z = x + κy`, `t = s + κy`. -/
theorem si_arObj_eq {γ β R ρ : ℝ} (hρ : ρ < R) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (x y s : ℝ) :
    si_arObj γ β R ρ ν x y s =
      -Real.exp (-(γ * (x + ρ / (R - ρ) * y - (s + ρ / (R - ρ) * y)))) +
        β * ∫ e, -(ex7_caraAlim γ β R (si_arLaw R ρ ν) *
          Real.exp (-(ex7_caraAbar γ R * (R * (s + ρ / (R - ρ) * y) + e)))) ∂si_arLaw R ρ ν := by
  have hRρ : R - ρ ≠ 0 := by linarith
  have hmeas : Measurable fun e : ℝ => R / (R - ρ) * e := measurable_const_mul _
  rw [si_arObj, si_arLaw, integral_map hmeas.aemeasurable (by fun_prop : Continuous fun e =>
    -(ex7_caraAlim γ β R (ν.map fun e => R / (R - ρ) * e) *
      Real.exp (-(ex7_caraAbar γ R * (R * (s + ρ / (R - ρ) * y) + e))))).aestronglyMeasurable]
  congr 2
  · ring_nf
  · refine integral_congr_ae (Eventually.of_forall fun e => ?_)
    simp only [si_arV, si_arLaw]
    congr 4
    field_simp
    ring

/-- **Exercise 8.11, the solution** (Miao, p. 289). Let `γ, β > 0`, `R > 1`, `ρ < R`, and `ε`
iid with law `ν` concentrated on `[e_min, e_max]`. Then `V(x, y) = −Āe^{−ᾱ(x + ρy/(R − ρ))}`
solves the Bellman equation `V(x, y) = sup_s −e^{−γ(x − s)} + β E V(Rs + ρy + ε, ρy + ε)`, and
the supremum is attained only at the saving `s(x, y) = s̄(x + κy) − κy`. -/
theorem ex_8_11 {γ β R ρ emin emax : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν] (hγ : 0 < γ)
    (hβ : 0 < β) (hR : 1 < R) (hρ : ρ < R) (hν : ∀ᵐ e ∂ν, e ∈ Set.Icc emin emax) (x y : ℝ) :
    (∀ s, s ≠ si_arSav γ β R ρ ν x y →
      si_arObj γ β R ρ ν x y s < si_arObj γ β R ρ ν x y (si_arSav γ β R ρ ν x y)) ∧
    si_arV γ β R ρ ν x y = si_arObj γ β R ρ ν x y (si_arSav γ β R ρ ν x y) := by
  have : IsProbabilityMeasure (si_arLaw R ρ ν) := by rw [si_arLaw]; infer_instance
  obtain ⟨hmax, hval, -, -⟩ :=
    ex_7_7_bellman hγ hβ hR (si_arLaw_ae (by linarith) hρ hν) (x + ρ / (R - ρ) * y)
  have hs : si_arSav γ β R ρ ν x y + ρ / (R - ρ) * y =
      ex7_caraSbar γ β R (si_arLaw R ρ ν) (x + ρ / (R - ρ) * y) := by
    rw [si_arSav]; ring
  refine ⟨fun s hne => ?_, ?_⟩
  · rw [si_arObj_eq hρ, si_arObj_eq hρ, hs]
    refine hmax _ fun h => hne ?_
    rw [si_arSav, ← h]; ring
  · rw [si_arObj_eq hρ, hs]
    exact hval

/-- `L̄ = R ln(βRM̄)/(R − 1)`: the constant of the limit policy in closed form. -/
theorem si_caraLbar_eq {γ β R : ℝ} {μ : Measure ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 1 < R)
    (hM : 0 < ex7_caraMbar γ R μ) :
    ex7_caraLbar γ β R μ = R * Real.log (β * R * ex7_caraMbar γ R μ) / (R - 1) := by
  have hR0 : 0 < R := by linarith
  have hR1 : R - 1 ≠ 0 := by linarith
  obtain ⟨hγR, hc⟩ := ex7_caraAbar_R (γ := γ) hR
  have hα := ex7_caraAbar_pos hγ hR
  set α := ex7_caraAbar γ R
  set M := ex7_caraMbar γ R μ
  have hαR : α * R / γ = R - 1 := by
    simp only [α, ex7_caraAbar]; field_simp
  have h1 : 1 + γ / (α * R) = R / (R - 1) := by
    have : γ / (α * R) = 1 / (R - 1) := by
      rw [div_eq_div_iff (by positivity) hR1]
      have : α * R = γ * (R - 1) := by rw [← hαR]; field_simp
      linarith
    rw [this]; field_simp; ring
  have hlogA : Real.log (ex7_caraAlim γ β R μ) =
      (Real.log (R / (R - 1)) + R⁻¹ * Real.log (β * M * (R - 1))) / (1 - R⁻¹) := by
    rw [ex7_caraAlim, Real.log_exp, ex7_caraDbar, hc hγ, h1,
      show β * M * α * R / γ = β * M * (α * R / γ) by ring, hαR]
  have hpos : 0 < β * ex7_caraAlim γ β R μ * M * α * R / γ := by
    have := Real.exp_pos (ex7_caraDbar γ β R μ / (1 - ex7_caraCbar γ R))
    have hA : 0 < ex7_caraAlim γ β R μ := this
    positivity
  rw [ex7_caraLbar]
  have e1 : β * ex7_caraAlim γ β R μ * M * α * R / γ =
      ex7_caraAlim γ β R μ * (β * M * (R - 1)) := by
    rw [← hαR]; ring
  have hX : 0 < β * M * (R - 1) := by
    have : 0 < R - 1 := by linarith
    positivity
  have hA : 0 < ex7_caraAlim γ β R μ := Real.exp_pos _
  rw [e1, Real.log_mul hA.ne' hX.ne', hlogA,
    show β * R * M = β * M * (R - 1) * (R / (R - 1)) by field_simp,
    Real.log_mul hX.ne' (by positivity : R / (R - 1) ≠ 0)]
  field_simp
  ring

/-- Exercise 8.11: **the consumption policy**
`c(x, y) = x − s(x, y) = (1 − 1/R)(x + ρy/(R − ρ)) − L̄/(γR)`. -/
theorem ex_8_11_consumption {γ β R ρ : ℝ} (hγ : 0 < γ) (hR : 1 < R) (ν : Measure ℝ) (x y : ℝ) :
    x - si_arSav γ β R ρ ν x y =
      (1 - R⁻¹) * (x + ρ / (R - ρ) * y) - ex7_caraLbar γ β R (si_arLaw R ρ ν) / (γ * R) := by
  have hR0 : R ≠ 0 := by linarith
  obtain ⟨hγR, -⟩ := ex7_caraAbar_R (γ := γ) hR
  rw [si_arSav, ex7_caraSbar, hγR]
  field_simp
  ring

/-! ### `ρ = 0`: a random walk -/

/-- Exercise 8.11 with `ρ = 0`: `ε̃ = ε`, `s(x, y) = s̄(x)`, and
`x_{t+1} = R s(x_t) + ε_{t+1} = x_t + L̄/γ + ε_{t+1}`. -/
theorem ex_8_11_rho_zero {γ β R : ℝ} (hγ : 0 < γ) (hR : 1 < R) (ν : Measure ℝ) (x y e : ℝ) :
    si_arLaw R 0 ν = ν ∧ si_arSav γ β R 0 ν x y = ex7_caraSbar γ β R ν x ∧
      R * ex7_caraSbar γ β R ν x + e = x + (ex7_caraLbar γ β R ν / γ + e) := by
  have hR0 : R ≠ 0 := by linarith
  have hlaw : si_arLaw R 0 ν = ν := by
    rw [si_arLaw]
    have : (fun e : ℝ => R / (R - 0) * e) = id := by funext e; simp [div_self hR0]
    rw [this, Measure.map_id]
  obtain ⟨hγR, -⟩ := ex7_caraAbar_R (γ := γ) hR
  refine ⟨hlaw, by rw [si_arSav, hlaw]; simp, ?_⟩
  rw [ex7_caraSbar, hγR]
  field_simp
  ring

/-- The transition kernel `x ↦ law of g(x, ε)`, `ε ~ ν`, of an iid-driven process. -/
noncomputable def si_iidKernel (ν : Measure ℝ) [IsProbabilityMeasure ν] (g : ℝ → ℝ → ℝ)
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) : Kernel ℝ ℝ where
  toFun x := ν.map (g x)
  measurable' := Measure.measurable_of_measurable_coe _ fun A hA => by
    have : ∀ x, (ν.map (g x)) A = ν (Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => g p.1 p.2) ⁻¹' A)) :=
      fun x => Measure.map_apply (hg.comp (Continuous.prodMk_right x)).measurable hA
    simp_rw [this]
    exact measurable_measure_prodMk_left (hg.measurable hA)

theorem si_iidKernel_apply (ν : Measure ℝ) [IsProbabilityMeasure ν] (g : ℝ → ℝ → ℝ)
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) (x : ℝ) :
    si_iidKernel ν g hg x = ν.map (g x) := rfl

theorem si_isMarkovKernel_iidKernel (ν : Measure ℝ) [IsProbabilityMeasure ν] (g : ℝ → ℝ → ℝ)
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) : IsMarkovKernel (si_iidKernel ν g hg) where
  isProbabilityMeasure x := by
    rw [si_iidKernel_apply]
    infer_instance

/-- **No stationary distribution for a non-degenerate random walk.** If
`g(x, ε) = x + ξ`, `ξ = d + ε` with `|ε| ≤ K` a.s., and `ξ` is not almost surely `0`, then the
process `x_{t+1} = g(x_t, ε_{t+1})` has no stationary distribution: `T*π ≠ π` for every
probability measure `π` on `ℝ`. -/
theorem si_no_stationary (ν : Measure ℝ) [IsProbabilityMeasure ν] {K : ℝ}
    (hK : ∀ᵐ e ∂ν, |e| ≤ K) (d : ℝ) (g : ℝ → ℝ → ℝ)
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) (hgd : ∀ x e, g x e = x + (d + e))
    (hnd : ¬ ∀ᵐ e ∂ν, d + e = 0) (pm : Measure ℝ) [IsProbabilityMeasure pm] :
    SIWC.adjointOp (si_iidKernel ν g hg) pm ≠ pm := by
  intro hinv
  set κ := si_iidKernel ν g hg
  have := si_isMarkovKernel_iidKernel ν g hg
  -- `∫ Tf dπ = ∫ f dπ` for bounded continuous `f`
  have hT : ∀ f : ℝ → ℝ, Continuous f → (∀ z, |f z| ≤ 1) →
      ∫ x, f x ∂pm = ∫ x, (∫ e, f (x + (d + e)) ∂ν) ∂pm := by
    intro f hf hb
    have h := SIWC.theorem_8_3_cor κ pm hf.measurable hb
    rw [hinv] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hgx : Measurable (g x) := (hg.comp (Continuous.prodMk_right x)).measurable
    change ∫ z, f z ∂(ν.map (g x)) = _
    rw [integral_map hgx.aemeasurable hf.aestronglyMeasurable]
    simp only [hgd]
  have hcos : ∀ t z, |Real.cos (t * z)| ≤ 1 := fun t z => Real.abs_cos_le_one _
  have hsin : ∀ t z, |Real.sin (t * z)| ≤ 1 := fun t z => Real.abs_sin_le_one _
  have hint : ∀ (μ' : Measure ℝ) [IsProbabilityMeasure μ'] (f : ℝ → ℝ), Continuous f →
      (∀ z, |f z| ≤ 1) → Integrable f μ' := fun μ' _ f hf hb =>
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb z)
  set a : ℝ → ℝ := fun t => ∫ x, Real.cos (t * x) ∂pm
  set b : ℝ → ℝ := fun t => ∫ x, Real.sin (t * x) ∂pm
  set p : ℝ → ℝ := fun t => ∫ e, Real.cos (t * (d + e)) ∂ν
  set q : ℝ → ℝ := fun t => ∫ e, Real.sin (t * (d + e)) ∂ν
  have hcc : ∀ t, Continuous fun z => Real.cos (t * z) := fun t => by fun_prop
  have hsc : ∀ t, Continuous fun z => Real.sin (t * z) := fun t => by fun_prop
  have hpi : ∀ t, Integrable (fun e => Real.cos (t * (d + e))) ν := fun t =>
    hint ν _ (by fun_prop) fun e => hcos t _
  have hqi : ∀ t, Integrable (fun e => Real.sin (t * (d + e))) ν := fun t =>
    hint ν _ (by fun_prop) fun e => hsin t _
  -- `a = pa − qb` and `b = pb + qa`
  have hab : ∀ t, a t = p t * a t - q t * b t ∧ b t = p t * b t + q t * a t := by
    intro t
    have e1 : ∀ x, ∫ e, Real.cos (t * (x + (d + e))) ∂ν =
        Real.cos (t * x) * p t - Real.sin (t * x) * q t := fun x => by
      simp only [mul_add t x, Real.cos_add]
      rw [integral_sub ((hpi t).const_mul _) ((hqi t).const_mul _), integral_const_mul,
        integral_const_mul]
    have e2 : ∀ x, ∫ e, Real.sin (t * (x + (d + e))) ∂ν =
        Real.sin (t * x) * p t + Real.cos (t * x) * q t := fun x => by
      simp only [mul_add t x, Real.sin_add]
      rw [integral_add ((hpi t).const_mul _) ((hqi t).const_mul _), integral_const_mul,
        integral_const_mul]
    have ha := hT _ (hcc t) (hcos t)
    have hb := hT _ (hsc t) (hsin t)
    simp only [e1, e2] at ha hb
    rw [integral_sub ((hint pm _ (hcc t) (hcos t)).mul_const _)
      ((hint pm _ (hsc t) (hsin t)).mul_const _), integral_mul_const, integral_mul_const] at ha
    rw [integral_add ((hint pm _ (hsc t) (hsin t)).mul_const _)
      ((hint pm _ (hcc t) (hcos t)).mul_const _), integral_mul_const, integral_mul_const] at hb
    constructor
    · simp only [a, b]; linear_combination ha
    · simp only [a, b]; linear_combination hb
  -- `a` is continuous with `a(0) = 1`
  have hacont : Continuous a := continuous_of_dominated (bound := fun _ => 1)
    (fun t => (hcc t).aestronglyMeasurable)
    (fun t => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hcos t x)
    (integrable_const _) (Eventually.of_forall fun x => by fun_prop)
  have ha0 : a 0 = 1 := by simp [a]
  set B := |d| + |K| + 1
  have hB : 0 < B := by positivity
  obtain ⟨t, ht, ht0⟩ := (((hacont.tendsto 0).eventually (lt_mem_nhds (show (1 : ℝ) / 2 < a 0 by
    rw [ha0]; norm_num))).filter_mono nhdsWithin_le_nhds |>.and
      (Ioo_mem_nhdsGT (div_pos Real.pi_pos hB)) :
      ∀ᶠ s in 𝓝[>] (0 : ℝ), 1 / 2 < a s ∧ s ∈ Set.Ioo 0 (Real.pi / B)).exists
  -- `(a² + b²)(1 − p) = 0`, so `p(t) = 1`
  obtain ⟨h1, h2⟩ := hab t
  have hkey : (a t ^ 2 + b t ^ 2) * (1 - p t) = 0 := by linear_combination a t * h1 + b t * h2
  have hp : p t = 1 := by
    have : a t ^ 2 + b t ^ 2 ≠ 0 := by nlinarith
    have := (mul_eq_zero.1 hkey).resolve_left this
    linarith
  -- `cos(t ξ) = 1` a.s., hence `ξ = 0` a.s.
  have hnn : 0 ≤ᵐ[ν] fun e => 1 - Real.cos (t * (d + e)) :=
    Eventually.of_forall fun e => sub_nonneg.2 (Real.cos_le_one _)
  have hzero : ∫ e, (1 - Real.cos (t * (d + e))) ∂ν = 0 := by
    rw [integral_sub (integrable_const _) (hpi t)]
    simp only [integral_const, probReal_univ, one_smul]
    change 1 - p t = 0
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn ((integrable_const _).sub (hpi t))).1 hzero
  refine hnd ?_
  filter_upwards [hae, hK] with e he heK
  simp only [Pi.zero_apply, sub_eq_zero] at he
  have hbd : |t * (d + e)| < 2 * Real.pi := by
    rw [abs_mul, abs_of_pos ht0.1]
    have h3 : |d + e| ≤ |d| + |K| := (abs_add_le d e).trans (by
      linarith [heK.trans (le_abs_self K)])
    have h4 : t * |d + e| ≤ t * B := mul_le_mul_of_nonneg_left (by linarith) ht0.1.le
    have h5 : t * B < Real.pi := by rw [← lt_div_iff₀ hB]; exact ht0.2
    linarith [Real.pi_pos]
  have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [neg_abs_le (t * (d + e))])
    (by linarith [le_abs_self (t * (d + e))])).1 he.symm
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h ht0.1.ne'
  · exact h

/-- **Exercise 8.11, `ρ = 0`** (Miao, p. 290): along the optimal policy, cash on hand
`x_{t+1} = R s(x_t) + ε_{t+1}` has no stationary distribution, provided `L̄/γ + ε` is not almost
surely `0`. -/
theorem ex_8_11_no_stationary {γ β R emin emax : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hγ : 0 < γ) (hR : 1 < R) (hν : ∀ᵐ e ∂ν, e ∈ Set.Icc emin emax)
    (hnd : ¬ ∀ᵐ e ∂ν, ex7_caraLbar γ β R ν / γ + e = 0)
    (hg : Continuous fun p : ℝ × ℝ => R * si_arSav γ β R 0 ν p.1 0 + p.2)
    (pm : Measure ℝ) [IsProbabilityMeasure pm] :
    SIWC.adjointOp (si_iidKernel ν (fun x e => R * si_arSav γ β R 0 ν x 0 + e) hg) pm ≠ pm := by
  refine si_no_stationary ν (K := |emin| + |emax|) ?_ (ex7_caraLbar γ β R ν / γ) _ hg
    (fun x e => ?_) hnd pm
  · filter_upwards [hν] with e he
    rw [abs_le]
    constructor <;> linarith [he.1, he.2, neg_abs_le emin, le_abs_self emax, abs_nonneg emin,
      abs_nonneg emax]
  · obtain ⟨-, h2, h3⟩ := ex_8_11_rho_zero (β := β) hγ hR ν x 0 e
    rw [h2, h3]

/-- The optimal cash-on-hand map for `ρ = 0` is continuous (it is affine). -/
theorem si_arSav_zero_continuous {γ β R : ℝ} (ν : Measure ℝ) :
    Continuous fun p : ℝ × ℝ => R * si_arSav γ β R 0 ν p.1 0 + p.2 := by
  simp only [si_arSav, ex7_caraSbar]
  fun_prop

/-- **Exercise 8.11, `ρ = 0`, the counterexample**: if `ε = e₀` almost surely and `βR = 1`, then
`L̄/γ + e₀ = 0`, the optimal policy keeps cash on hand constant, and every point mass `δ_x` is a
stationary distribution. -/
theorem ex_8_11_counterexample {γ β R e₀ : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 1 < R)
    (hβR : β * R = 1) (x : ℝ) :
    ex7_caraLbar γ β R (Measure.dirac e₀) / γ + e₀ = 0 ∧
      SIWC.adjointOp (si_iidKernel (Measure.dirac e₀) (fun x e => R * si_arSav γ β R 0
        (Measure.dirac e₀) x 0 + e) (si_arSav_zero_continuous _)) (Measure.dirac x) =
        Measure.dirac x := by
  have hR1 : R - 1 ≠ 0 := by linarith
  have hM : ex7_caraMbar γ R (Measure.dirac e₀) = Real.exp (-(ex7_caraAbar γ R * e₀)) := by
    rw [ex7_caraMbar, integral_dirac]
  have hMpos : 0 < ex7_caraMbar γ R (Measure.dirac e₀) := by rw [hM]; exact Real.exp_pos _
  have hL := si_caraLbar_eq (μ := Measure.dirac e₀) hγ hβ hR hMpos
  have hzero : ex7_caraLbar γ β R (Measure.dirac e₀) / γ + e₀ = 0 := by
    rw [hL, hM, hβR, one_mul, Real.log_exp, ex7_caraAbar]
    field_simp
    ring
  refine ⟨hzero, ?_⟩
  rw [SIWC.adjointOp, Measure.dirac_bind (Kernel.measurable _), si_iidKernel_apply,
    Measure.map_dirac' (measurable_const_add _)]
  obtain ⟨-, h2, h3⟩ := ex_8_11_rho_zero (β := β) hγ hR (Measure.dirac e₀) x 0 e₀
  rw [h2, h3, hzero, add_zero]

end Miao.Applications
