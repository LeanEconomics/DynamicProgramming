/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.OCDifferentiable
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# §6.5: the Maximum Principle

Miao, §6.5, pp. 180–183, with `X = A = ℝ` and `Γ(x, z) = A` (p. 180). The stochastic setting is a
probability space `(Ω, P)` with a filtration `(ℱ_t)` to which the shocks `z_t` are adapted; a
plan is an adapted process `(a_t)`, its states `x_t` follow (5.14) (`OCModel.path`), and the
objective is the Bolza form (6.28) (`OCModel.bolza`). `E_t` is the conditional expectation
`P[· | ℱ_t]` (Mathlib's `condExp`), so `E_t` conditions on the history of shocks; under the
Markov property (`IsMarkovCond`) it reduces to integration against `Q(z_t, ·)`.

* `Ha`, `Hx`: the derivatives of the Hamiltonian (6.37), `∂H_t/∂a = ∂u_t/∂a + β E_t[μ_{t+1} ∂φ/∂a]`
  and `∂H_t/∂x = ∂u_t/∂x + β E_t[μ_{t+1} ∂φ/∂x]`, the derivative taken inside `E_t` as in the
  book; `hamiltonian` is (6.37) itself. `MaxPrinciple`: the system (6.36), (6.38) (= (6.34)) and
  (6.39) (= (6.35)) along the states (5.14) of a plan.
* **Theorem 6.5.1** (`theorem_6_5_1`): a plan satisfying the system is optimal. **Departures.**
  (1) The book's hypothesis "`H_t(·, ·, z_t, μ_{t+1})` is concave" involves `E_t` of a function of
  the arguments, which is not well defined at the random arguments `(x_t, a_t)` the proof
  substitutes; we assume the pathwise Hamiltonian (`pathHam`)
  `u_t(x, z_t, a) + β μ_{t+1} φ(x, a, z_t, z_{t+1})` concave in `(x, a)` for every `ω`, which is
  what the sufficient conditions of p. 183 give (`OCMaxPrincipleLinks`). (2) The telescoping
  needs integrability of the rewards and of `μ_{t+1}(x*_{t+1} − x_{t+1})`,
  `(x*_t − x_t) ∂u_t/∂x`, … for the optimal and the competing plan (`MPIntegrable`);
  optimality is among the plans for which these hold. (3) `β ≥ 0` is used.
* `oc_tangent_le`, `oc_supergradient`: tangent-line inequalities for differentiable concave
  functions on `ℝ` and `ℝ²`; `path_measurable`: the states of an adapted plan are adapted.

The sufficient conditions of p. 183, the link with dynamic programming and the deterministic
case (6.40) are in `OCMaxPrincipleLinks`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

/-! ### Two tangent-line inequalities for concave functions -/

/-- A differentiable concave function lies below its tangent line. -/
theorem oc_tangent_le {f : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ f) {p : ℝ}
    (hd : DifferentiableAt ℝ f p) (q : ℝ) : f q ≤ f p + deriv f p * (q - p) := by
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · have := hc.slope_le_deriv (Set.mem_univ p) (Set.mem_univ q) hpq hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · simp
  · have := hc.deriv_le_slope (Set.mem_univ q) (Set.mem_univ p) hqp hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- **The supergradient inequality on `ℝ²`**: a concave function differentiable at `p` satisfies
`h(q) ≤ h(p) + (q₁ − p₁) ∂₁h(p) + (q₂ − p₂) ∂₂h(p)`. -/
theorem oc_supergradient {h : ℝ × ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ h) {p : ℝ × ℝ}
    (hd : DifferentiableAt ℝ h p) (q : ℝ × ℝ) :
    h q ≤ h p + (q.1 - p.1) * deriv (fun y => h (y, p.2)) p.1 +
      (q.2 - p.2) * deriv (fun b => h (p.1, b)) p.2 := by
  set L := fderiv ℝ h p
  have hL : HasFDerivAt h L p := hd.hasFDerivAt
  have h1 : deriv (fun y => h (y, p.2)) p.1 = L (1, 0) := by
    have : HasDerivAt (fun y : ℝ => (y, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    exact (hL.comp_hasDerivAt p.1 this).deriv
  have h2 : deriv (fun b => h (p.1, b)) p.2 = L (0, 1) := by
    have : HasDerivAt (fun b : ℝ => (p.1, b)) ((0 : ℝ), (1 : ℝ)) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (hL.comp_hasDerivAt p.2 this).deriv
  -- restrict to the segment from `p` to `q`
  set g : ℝ → ℝ := h ∘ AffineMap.lineMap p q
  have hgc : ConcaveOn ℝ Set.univ g := by
    have := hc.comp_affineMap (AffineMap.lineMap p q)
    rwa [Set.preimage_univ] at this
  have hgd : HasDerivAt g (L (q - p)) 0 := by
    have hl : HasDerivAt (AffineMap.lineMap p q : ℝ → ℝ × ℝ) (q - p) 0 :=
      AffineMap.hasDerivAt_lineMap
    have hL0 : HasFDerivAt h L (AffineMap.lineMap p q (0 : ℝ)) := by
      rw [AffineMap.lineMap_apply_zero]; exact hL
    exact hL0.comp_hasDerivAt 0 hl
  have ht := oc_tangent_le hgc hgd.differentiableAt 1
  simp only [g, Function.comp_apply, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero,
    hgd.deriv, sub_zero, mul_one] at ht
  have hdec : q - p = (q.1 - p.1) • ((1 : ℝ), (0 : ℝ)) + (q.2 - p.2) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hdec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at ht
  rw [h1, h2]
  linarith

namespace OCModel

variable {Z : Type*} [MeasurableSpace Z] {Ω : Type*} {m0 : MeasurableSpace Ω}
  (M : OCModel ℝ ℝ Z) (P : Measure Ω) (ℱ : Filtration ℕ m0) (z : ℕ → Ω → Z)

/-- The states of an adapted plan are adapted when `φ` is measurable. -/
theorem path_measurable (hz : ∀ t, Measurable[ℱ t] (z t))
    (hφm : Measurable fun p : ℝ × ℝ × Z × Z => M.φ p.1 p.2.1 p.2.2.1 p.2.2.2)
    {a : ℕ → Ω → ℝ} (ha : ∀ t, Measurable[ℱ t] (a t)) (x₀ : ℝ) :
    ∀ t, Measurable[ℱ t] (M.path z a x₀ t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hle : ℱ t ≤ ℱ (t + 1) := ℱ.mono (Nat.le_succ t)
    exact hφm.comp ((ih.mono hle le_rfl).prodMk ((ha t |>.mono hle le_rfl).prodMk
      ((hz t |>.mono hle le_rfl).prodMk (hz (t + 1)))))

/-- `∂H_t/∂a` along a plan, (6.34)/(6.38): `∂u_t(x_t, z_t, a_t)/∂a +
β E_t[μ_{t+1} ∂φ(x_t, a_t, z_t, z_{t+1})/∂a]`. -/
noncomputable def Ha (μ x a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω =>
  deriv (fun b => M.u t (x t ω) (z t ω) b) (a t ω) + M.β * (P[fun ω' => μ (t + 1) ω' *
    deriv (fun b => M.φ (x t ω') b (z t ω') (z (t + 1) ω')) (a t ω') | ℱ t]) ω

/-- `∂H_t/∂x` along a plan, (6.35)/(6.39): `∂u_t(x_t, z_t, a_t)/∂x +
β E_t[μ_{t+1} ∂φ(x_t, a_t, z_t, z_{t+1})/∂x]`. -/
noncomputable def Hx (μ x a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω =>
  deriv (fun y => M.u t y (z t ω) (a t ω)) (x t ω) + M.β * (P[fun ω' => μ (t + 1) ω' *
    deriv (fun y => M.φ y (a t ω') (z t ω') (z (t + 1) ω')) (x t ω') | ℱ t]) ω

/-- **The Hamiltonian (6.37)** (Miao, p. 181) at a deterministic `(x, a)`:
`H_t(x, a, z_t, μ_{t+1}) = u_t(x, z_t, a) + β E_t[μ_{t+1} φ(x, a, z_t, z_{t+1})]`. -/
noncomputable def hamiltonian (μ : ℕ → Ω → ℝ) (t : ℕ) (x a : ℝ) : Ω → ℝ := fun ω =>
  M.u t x (z t ω) a + M.β * (P[fun ω' => μ (t + 1) ω' * M.φ x a (z t ω') (z (t + 1) ω') | ℱ t]) ω

/-- The **pathwise Hamiltonian** `u_t(x, z_t, a) + β μ_{t+1} φ(x, a, z_t, z_{t+1})` at `ω`. -/
def pathHam (μ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) (p : ℝ × ℝ) : ℝ :=
  M.u t p.1 (z t ω) p.2 + M.β * (μ (t + 1) ω * M.φ p.1 p.2 (z t ω) (z (t + 1) ω))

/-- **The Maximum Principle system** (Miao, pp. 181–182): along the states `x` of the plan `a`,
(6.38) `∂H_t/∂a = 0` (`t < T`), (6.39) `∂H_t/∂x = μ_t` (`1 ≤ t < T`) and (6.36)
`μ_T = ∂u_T(x_T, z_T)/∂x`, almost surely. -/
structure MaxPrinciple (μ x a : ℕ → Ω → ℝ) : Prop where
  foc_a : ∀ t < M.T, M.Ha P ℱ z μ x a t =ᵐ[P] 0
  foc_x : ∀ t, 1 ≤ t → t < M.T → μ t =ᵐ[P] M.Hx P ℱ z μ x a t
  terminal : μ M.T =ᵐ[P] fun ω => deriv (fun y => M.uT y (z M.T ω)) (x M.T ω)

/-- The integrability needed for the telescoping in the proof of Theorem 6.5.1, for the
candidate `(xs, as)` with multipliers `μ` and a competing plan `(x, a)`. -/
structure MPIntegrable (μ xs as x a : ℕ → Ω → ℝ) : Prop where
  u_s : ∀ t < M.T, Integrable (fun ω => M.u t (xs t ω) (z t ω) (as t ω)) P
  u_c : ∀ t < M.T, Integrable (fun ω => M.u t (x t ω) (z t ω) (a t ω)) P
  uT_s : Integrable (fun ω => M.uT (xs M.T ω) (z M.T ω)) P
  uT_c : Integrable (fun ω => M.uT (x M.T ω) (z M.T ω)) P
  μΔ : ∀ t < M.T, Integrable (fun ω => μ (t + 1) ω * (xs (t + 1) ω - x (t + 1) ω)) P
  ux : ∀ t < M.T,
    Integrable (fun ω => (xs t ω - x t ω) * deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω)) P
  φx : ∀ t < M.T, Integrable (fun ω => μ (t + 1) ω *
    deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω)) P
  φxΔ : ∀ t < M.T, Integrable (fun ω => (xs t ω - x t ω) * (μ (t + 1) ω *
    deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω))) P
  ua : ∀ t < M.T,
    Integrable (fun ω => (as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω)) P
  φa : ∀ t < M.T, Integrable (fun ω => μ (t + 1) ω *
    deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)) P
  φaΔ : ∀ t < M.T, Integrable (fun ω => (as t ω - a t ω) * (μ (t + 1) ω *
    deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω))) P
  uTx : Integrable (fun ω => (xs M.T ω - x M.T ω) * deriv (fun y => M.uT y (z M.T ω)) (xs M.T ω)) P

variable {M P ℱ z}

/-- `E[Δ W] = E[Δ E_t W]` for `ℱ_t`-measurable `Δ` (the tower property used in the proof). -/
theorem oc_integral_mul_condExp [IsFiniteMeasure P] {t : ℕ} {Δ W : Ω → ℝ}
    (hΔ : StronglyMeasurable[ℱ t] Δ) (hΔW : Integrable (fun ω => Δ ω * W ω) P)
    (hW : Integrable W P) :
    Integrable (fun ω => Δ ω * (P[W | ℱ t]) ω) P ∧
      ∫ ω, Δ ω * W ω ∂P = ∫ ω, Δ ω * (P[W | ℱ t]) ω ∂P := by
  have hpull : P[fun ω => Δ ω * W ω | ℱ t] =ᵐ[P] fun ω => Δ ω * (P[W | ℱ t]) ω :=
    condExp_mul_of_stronglyMeasurable_left hΔ hΔW hW
  refine ⟨integrable_condExp.congr hpull, ?_⟩
  rw [← integral_condExp (ℱ.le t)]
  exact integral_congr_ae hpull

/-- **Theorem 6.5.1 (sufficiency of the Maximum Principle)** (Miao, p. 182), with `X = A = ℝ` and
`Γ = A`, so that every adapted plan is feasible. Let the plan `as` with states `xs` (5.14) and
multipliers `μ` satisfy (6.36), (6.38) and (6.39); let the pathwise Hamiltonian
`u_t(x, z_t, a) + β μ_{t+1} φ(x, a, z_t, z_{t+1})` be concave in `(x, a)` and `u_T(·, z)` be
concave; let Assumptions 6.4.13–6.4.14 hold and `β ≥ 0`. Then for every adapted plan `a` with the
integrability `MPIntegrable`, the objective (6.28) of `a` is at most that of `as`. -/
theorem theorem_6_5_1 [IsProbabilityMeasure P] (hz : ∀ t, Measurable[ℱ t] (z t))
    (hφm : Measurable fun p : ℝ × ℝ × Z × Z => M.φ p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hX : M.X = Set.univ) (hA : M.A = Set.univ) (h6413 : M.Assumption6413)
    (h6414 : M.Assumption6414) (hβ : 0 ≤ M.β) (x₀ : ℝ) {μ as a : ℕ → Ω → ℝ}
    (has : ∀ t, Measurable[ℱ t] (as t)) (ha : ∀ t, Measurable[ℱ t] (a t))
    (hmp : M.MaxPrinciple P ℱ z μ (M.path z as x₀) as)
    (hH : ∀ t < M.T, ∀ ω, ConcaveOn ℝ Set.univ (M.pathHam z μ t ω))
    (huT : ∀ z', ConcaveOn ℝ Set.univ fun x => M.uT x z')
    (hint : M.MPIntegrable P z μ (M.path z as x₀) as (M.path z a x₀) a) :
    M.bolza P z a x₀ ≤ M.bolza P z as x₀ := by
  set xs := M.path z as x₀ with hxsdef
  set x := M.path z a x₀ with hxdef
  have hU : interior (M.X ×ˢ M.A) = Set.univ := by
    rw [hX, hA, Set.univ_prod_univ, interior_univ]
  have hud : ∀ t < M.T, ∀ z0 (p : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => M.u t p.1 z0 p.2) p := fun t ht z0 p => by
    have := (h6413.2 t ht z0).differentiableOn one_ne_zero
    rw [hU] at this
    exact this.differentiableAt Filter.univ_mem
  have hφd : ∀ z0 z1 (p : ℝ × ℝ), DifferentiableAt ℝ (fun p : ℝ × ℝ => M.φ p.1 p.2 z0 z1) p :=
    fun z0 z1 p => by
      have := h6414 z0 z1
      rw [hU] at this
      exact this.differentiableAt Filter.univ_mem
  have huTd : ∀ z0 (y : ℝ), DifferentiableAt ℝ (fun y => M.uT y z0) y := fun z0 y => by
    have := h6413.1 z0
    rw [hX, interior_univ] at this
    exact this.differentiableAt Filter.univ_mem
  have hxs : ∀ t, Measurable[ℱ t] (xs t) := M.path_measurable ℱ z hz hφm has x₀
  have hx : ∀ t, Measurable[ℱ t] (x t) := M.path_measurable ℱ z hz hφm ha x₀
  set c : ℕ → ℝ := fun t => ∫ ω, μ t ω * (xs t ω - x t ω) ∂P with hcdef
  have hc0 : c 0 = 0 := by simp [c, xs, x, path]
  -- the period-`t` inequality
  have hper : ∀ t < M.T, c t - M.β * c (t + 1) ≤
      (∫ ω, M.u t (xs t ω) (z t ω) (as t ω) ∂P) - ∫ ω, M.u t (x t ω) (z t ω) (a t ω) ∂P := by
    intro t ht
    -- pathwise: the supergradient inequality for the pathwise Hamiltonian
    have hpath : ∀ ω, (xs t ω - x t ω) * deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) +
        M.β * ((xs t ω - x t ω) * (μ (t + 1) ω *
          deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω))) +
        ((as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) +
          M.β * ((as t ω - a t ω) * (μ (t + 1) ω *
            deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)))) ≤
        M.u t (xs t ω) (z t ω) (as t ω) - M.u t (x t ω) (z t ω) (a t ω) +
          M.β * (μ (t + 1) ω * (xs (t + 1) ω - x (t + 1) ω)) := by
      intro ω
      set p : ℝ × ℝ := (xs t ω, as t ω)
      have hdH : DifferentiableAt ℝ (M.pathHam z μ t ω) p :=
        (hud t ht _ p).add ((hφd _ _ p).const_mul _ |>.const_mul _)
      have hsg := oc_supergradient (hH t ht ω) hdH (x t ω, a t ω)
      have hdx : deriv (fun y => M.pathHam z μ t ω (y, p.2)) p.1 =
          deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) + M.β * (μ (t + 1) ω *
            deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω)) := by
        have h1 : DifferentiableAt ℝ (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) := by
          have hg := hud t ht (z t ω) p
          exact hg.comp (xs t ω)
            (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y, as t ω)) (xs t ω))
        have h2 : DifferentiableAt ℝ (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω) := by
          have hg := hφd (z t ω) (z (t + 1) ω) p
          exact hg.comp (xs t ω)
            (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y, as t ω)) (xs t ω))
        exact (h1.hasDerivAt.add ((h2.hasDerivAt.const_mul (μ (t + 1) ω)).const_mul M.β)).deriv
      have hda : deriv (fun b => M.pathHam z μ t ω (p.1, b)) p.2 =
          deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) + M.β * (μ (t + 1) ω *
            deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)) := by
        have h1 : DifferentiableAt ℝ (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) := by
          have hg := hud t ht (z t ω) p
          exact hg.comp (as t ω)
            (by fun_prop : DifferentiableAt ℝ (fun b : ℝ => (xs t ω, b)) (as t ω))
        have h2 : DifferentiableAt ℝ (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω) := by
          have hg := hφd (z t ω) (z (t + 1) ω) p
          exact hg.comp (as t ω)
            (by fun_prop : DifferentiableAt ℝ (fun b : ℝ => (xs t ω, b)) (as t ω))
        exact (h1.hasDerivAt.add ((h2.hasDerivAt.const_mul (μ (t + 1) ω)).const_mul M.β)).deriv
      rw [hdx, hda] at hsg
      have e1 : xs (t + 1) ω = M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω) := rfl
      have e2 : x (t + 1) ω = M.φ (x t ω) (a t ω) (z t ω) (z (t + 1) ω) := rfl
      simp only [pathHam, p] at hsg
      rw [e1, e2]
      nlinarith [hsg]
    -- integrate
    have hΔx : StronglyMeasurable[ℱ t] fun ω => xs t ω - x t ω :=
      ((hxs t).sub (hx t)).stronglyMeasurable
    have hΔa : StronglyMeasurable[ℱ t] fun ω => as t ω - a t ω :=
      ((has t).sub (ha t)).stronglyMeasurable
    obtain ⟨iX, eX⟩ := oc_integral_mul_condExp hΔx (hint.φxΔ t ht) (hint.φx t ht)
    obtain ⟨iA, eA⟩ := oc_integral_mul_condExp hΔa (hint.φaΔ t ht) (hint.φa t ht)
    have hmono := integral_mono (((hint.ux t ht).add ((hint.φxΔ t ht).const_mul M.β)).add
      ((hint.ua t ht).add ((hint.φaΔ t ht).const_mul M.β)))
      (((hint.u_s t ht).sub (hint.u_c t ht)).add ((hint.μΔ t ht).const_mul M.β)) hpath
    rw [integral_add' ((hint.ux t ht).add ((hint.φxΔ t ht).const_mul M.β))
        ((hint.ua t ht).add ((hint.φaΔ t ht).const_mul M.β)),
      integral_add' (hint.ux t ht) ((hint.φxΔ t ht).const_mul M.β),
      integral_add' (hint.ua t ht) ((hint.φaΔ t ht).const_mul M.β),
      integral_add' ((hint.u_s t ht).sub (hint.u_c t ht)) ((hint.μΔ t ht).const_mul M.β),
      integral_sub' (hint.u_s t ht) (hint.u_c t ht), integral_const_mul, integral_const_mul,
      integral_const_mul, eX, eA] at hmono
    -- the `a`-terms vanish by (6.38)
    have hAzero : (∫ ω, (as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) ∂P)
        + M.β * ∫ ω, (as t ω - a t ω) * (P[fun ω' => μ (t + 1) ω' *
          deriv (fun b => M.φ (xs t ω') b (z t ω') (z (t + 1) ω')) (as t ω') | ℱ t]) ω ∂P = 0 := by
      rw [← integral_const_mul, ← integral_add (hint.ua t ht) (iA.const_mul M.β)]
      have : (fun ω => (as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) +
          M.β * ((as t ω - a t ω) * (P[fun ω' => μ (t + 1) ω' *
            deriv (fun b => M.φ (xs t ω') b (z t ω') (z (t + 1) ω')) (as t ω') | ℱ t]) ω)) =ᵐ[P]
          fun _ => (0 : ℝ) := by
        filter_upwards [hmp.foc_a t ht] with ω hω
        simp only [Ha, Pi.zero_apply] at hω
        linear_combination (as t ω - a t ω) * hω
      rw [integral_congr_ae this, integral_zero]
    -- the `x`-terms are `c t` by (6.39), or vanish at `t = 0`
    have hXc : (∫ ω, (xs t ω - x t ω) * deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) ∂P)
        + M.β * ∫ ω, (xs t ω - x t ω) * (P[fun ω' => μ (t + 1) ω' *
          deriv (fun y => M.φ y (as t ω') (z t ω') (z (t + 1) ω')) (xs t ω') | ℱ t]) ω ∂P =
          c t := by
      rw [← integral_const_mul, ← integral_add (hint.ux t ht) (iX.const_mul M.β)]
      rcases Nat.eq_zero_or_pos t with rfl | ht1
      · rw [hc0]
        have : ∀ ω, xs 0 ω - x 0 ω = 0 := fun ω => by simp [xs, x, path]
        simp [this]
      · refine integral_congr_ae ?_
        filter_upwards [hmp.foc_x t ht1 ht] with ω hω
        simp only [Hx] at hω
        rw [hω]
        ring
    linarith [hmono]
  -- the terminal inequality
  have hterm : c M.T ≤ (∫ ω, M.uT (xs M.T ω) (z M.T ω) ∂P) - ∫ ω, M.uT (x M.T ω) (z M.T ω) ∂P := by
    have hpath : ∀ ω, (xs M.T ω - x M.T ω) * deriv (fun y => M.uT y (z M.T ω)) (xs M.T ω) ≤
        M.uT (xs M.T ω) (z M.T ω) - M.uT (x M.T ω) (z M.T ω) := fun ω => by
      have := oc_tangent_le (huT (z M.T ω)) (huTd _ (xs M.T ω)) (x M.T ω)
      nlinarith [this]
    have hmono := integral_mono hint.uTx (hint.uT_s.sub hint.uT_c) hpath
    rw [integral_sub' hint.uT_s hint.uT_c] at hmono
    refine le_trans (le_of_eq ?_) hmono
    refine integral_congr_ae ?_
    filter_upwards [hmp.terminal] with ω hω
    rw [hω]
    ring
  -- assemble: `D ≥ Σ βᵗ (c_t − β c_{t+1}) + β^T c_T = c_0 = 0`
  have hbolza : ∀ (b : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ),
      (∀ t < M.T, Integrable (fun ω => M.u t (y t ω) (z t ω) (b t ω)) P) →
      Integrable (fun ω => M.uT (y M.T ω) (z M.T ω)) P →
      ∫ ω, ((∑ t ∈ Finset.range M.T, M.β ^ t * M.u t (y t ω) (z t ω) (b t ω)) +
        M.β ^ M.T * M.uT (y M.T ω) (z M.T ω)) ∂P =
      (∑ t ∈ Finset.range M.T, M.β ^ t * ∫ ω, M.u t (y t ω) (z t ω) (b t ω) ∂P) +
        M.β ^ M.T * ∫ ω, M.uT (y M.T ω) (z M.T ω) ∂P := fun b y hi hT => by
    have hi' : ∀ t ∈ Finset.range M.T,
        Integrable (fun ω => M.β ^ t * M.u t (y t ω) (z t ω) (b t ω)) P :=
      fun t htm => (hi t (Finset.mem_range.1 htm)).const_mul _
    rw [integral_add (integrable_finsetSum _ hi') (hT.const_mul _), integral_finsetSum _ hi',
      integral_const_mul]
    simp only [integral_const_mul]
  have hs := hbolza as xs hint.u_s hint.uT_s
  have hc := hbolza a x hint.u_c hint.uT_c
  simp only [bolza]
  rw [hs, hc]
  have htel : (∑ t ∈ Finset.range M.T, M.β ^ t * (c t - M.β * c (t + 1))) + M.β ^ M.T * c M.T =
      c 0 := by
    have h1 : ∑ t ∈ Finset.range M.T, M.β ^ t * (c t - M.β * c (t + 1)) =
        ∑ t ∈ Finset.range M.T, (M.β ^ t * c t - M.β ^ (t + 1) * c (t + 1)) :=
      Finset.sum_congr rfl fun t _ => by ring
    rw [h1, Finset.sum_range_sub' (fun t => M.β ^ t * c t) M.T]
    simp
  have hsum : (∑ t ∈ Finset.range M.T, M.β ^ t * (c t - M.β * c (t + 1))) ≤
      ∑ t ∈ Finset.range M.T, M.β ^ t * ((∫ ω, M.u t (xs t ω) (z t ω) (as t ω) ∂P) -
        ∫ ω, M.u t (x t ω) (z t ω) (a t ω) ∂P) :=
    Finset.sum_le_sum fun t htm =>
      mul_le_mul_of_nonneg_left (hper t (Finset.mem_range.1 htm)) (pow_nonneg hβ t)
  have hT := mul_le_mul_of_nonneg_left hterm (pow_nonneg hβ M.T)
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum hT ⊢
  rw [hc0] at htel
  simp only [mul_sub, Finset.sum_sub_distrib] at htel
  linarith

end OCModel

end Miao.FiniteHorizonDP
