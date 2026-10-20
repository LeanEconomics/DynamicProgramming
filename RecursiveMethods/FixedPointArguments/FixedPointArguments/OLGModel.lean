/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# An overlapping-generations model

SLP §17.1, pp. 502–508.

SLP §17.1, pp. 502–508. The state space is `X = [a, b]` with `0 < a`, a transition function is
a Markov kernel `π : Kernel X X`, and the derivatives `H'`, `H''`, `V'`, `V''` are explicit
functions (derivatives within `[0, L)` and `[0, ∞)`, so one-sided at `0`).

* **Assumption 17.1** (`Assumption17_1`, p. 503), split into a labour part `Assumption17_1H`
  and a utility part `Assumption17_1V`, with the derived facts used throughout (`H'` strictly
  increasing and positive on `(0, L)`, `H'' ≥ 0`, `V' > 0` strictly decreasing, continuity).
* **Exercise 17.1** (`ex_17_1`, p. 504): for a measurable price `p ≥ pmin > 0` the young agent's
  problem has a unique solution `n(x) ∈ (0, L)`, characterised by the first-order condition. The
  abstract form is `consumer_problem` (differentiation under the integral sign:
  `hasDerivAt_utility`; the first-order condition has a unique root: `exists_unique_foc`).
* **Stationary equilibrium** (`IsStationaryEqm`, p. 503) and its reduction to (3) (p. 504):
  `eq3_of_isStationaryEqm` (equilibrium ⇒ (3), `p = M/(x n)`) and `isStationaryEqm_of_eq3`
  (the book's claim: a measurable `n : X → (0, L)` solving (3) is an equilibrium with
  `p = M/(x n)`); `eq3_iff_eq4` restates (3) as (4) with `ζ = olgZeta`, `φ = olgPhi`.
* **Proposition 1** (`proposition_1`, p. 505): with serially independent shocks (5) has exactly
  one solution in `(0, L)`.
* `olgZetaInv`, the inverse `ζ⁻¹ : ℝ₊ → [0, L)` (p. 507), continuous and strictly increasing,
  differentiable on `(0, ∞)` with `(ζ⁻¹)' = 1/ζ'(ζ⁻¹)`; `eq8_iff_eq4`: the change of variable
  `f = ζ ∘ n` turns (4) into the fixed-point equation (8).

**Correction (Proposition 1, step 4).** The case `φ(0) > 0` cannot occur under Assumption 17.1:
`φ(0) = 0 · V'(0) = 0` (`proposition_1_phi_zero_counterexample`). Only the book's second case
is relevant, and it is what `exists_unique_foc` proves.

**Correction (Proposition 1, (6)).** The elasticity `l ζ'(l)/ζ(l) = (H' + l H'')/H'` is `≥ 1`
on `(0, L)` (`zeta_elasticity_ge_one`) but **not** "`> 1` except at `0`": strict convexity allows
`H''(l₀) = 0`. Counterexample `proposition_1_elasticity_counterexample`, with
`olgExH(l) = l − 2 log(2 − l) + 6(2 − l) − 3(2 − l)² + (2/3)(2 − l)³` on `[0, 2)`, which satisfies
Assumption 17.1 (`olgExH_assumption`) and has elasticity exactly `1` at `l = 1`. The uniqueness
step is repaired as in the transcription's NOTE: the log-ratio `log ζ(l) − log ∫ φ(x' l) dμ` is
strictly increasing (`proposition_1_logRatio_strictMonoOn`), because it equals
`log H'(l) − log ∫ x' V'(x' l) dμ`.

**Correction (p. 515).** "Strict monotonicity and strict concavity imply `−y V''/V' > 0` on
`ℝ₊`" is false at `y = 0`, where the ratio is `0` (`rra_pos_counterexample`).

**Hypothesis made explicit (p. 504).** The converse "(3) ⇒ equilibrium" needs `n < L` (so that
`H'(n)` is defined and `p = M/(xn) ≥ M/(bL) > 0`, as Exercise 17.1 requires); the book says only
"strictly positive".
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Set Filter Topology

/-! ### Assumption 17.1 -/

/-- **Assumption 17.1, labour part** (p. 503). The disutility of labour `H : [0, L) → ℝ₊` is
twice continuously differentiable (derivatives `H'`, `H''`, taken within `[0, L)`, so one-sided
at `0`), strictly increasing and strictly convex, with `H'(0) = 0` and `H'(l) → +∞` as `l → L`. -/
structure Assumption17_1H (L : ℝ) (H H' H'' : ℝ → ℝ) : Prop where
  L_pos : 0 < L
  H_nonneg : ∀ l ∈ Ico 0 L, 0 ≤ H l
  H_deriv : ∀ l ∈ Ico 0 L, HasDerivWithinAt H (H' l) (Ico 0 L) l
  H'_deriv : ∀ l ∈ Ico 0 L, HasDerivWithinAt H' (H'' l) (Ico 0 L) l
  H''_cont : ContinuousOn H'' (Ico 0 L)
  H_mono : StrictMonoOn H (Ico 0 L)
  H_conv : StrictConvexOn ℝ (Ico 0 L) H
  H'_zero : H' 0 = 0
  H'_tendsto : Tendsto H' (𝓝[<] L) atTop

/-- **Assumption 17.1, utility part** (p. 503). The utility of consumption `V : ℝ₊ → ℝ₊` is
twice continuously differentiable on `ℝ₊ = [0, ∞)` (derivatives `V'`, `V''` within `[0, ∞)`),
strictly increasing and strictly concave. -/
structure Assumption17_1V (V V' V'' : ℝ → ℝ) : Prop where
  V_nonneg : ∀ y, 0 ≤ y → 0 ≤ V y
  V_deriv : ∀ y, 0 ≤ y → HasDerivWithinAt V (V' y) (Ici 0) y
  V'_deriv : ∀ y, 0 ≤ y → HasDerivWithinAt V' (V'' y) (Ici 0) y
  V''_cont : ContinuousOn V'' (Ici 0)
  V_mono : StrictMonoOn V (Ici 0)
  V_conc : StrictConcaveOn ℝ (Ici 0) V

/-- **Assumption 17.1** (p. 503): labour lies in `[0, L)` with `L < ∞`, and `H`, `V` satisfy
`Assumption17_1H` and `Assumption17_1V`. -/
structure Assumption17_1 (L : ℝ) (H H' H'' V V' V'' : ℝ → ℝ) : Prop where
  hH : Assumption17_1H L H H' H''
  hV : Assumption17_1V V V' V''

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-! ### Consequences of Assumption 17.1 -/

namespace Assumption17_1H

variable (hH : Assumption17_1H L H H' H'')
include hH

/-- `H'` is strictly increasing on `[0, L)` (strict convexity of `H`). -/
theorem H'_strictMonoOn : StrictMonoOn H' (Ico 0 L) := fun _ hx _ hy hxy =>
  (hH.H_conv.lt_slope_of_hasDerivWithinAt hx hy hxy (hH.H_deriv _ hx)).trans
    (hH.H_conv.slope_lt_of_hasDerivWithinAt hx hy hxy (hH.H_deriv _ hy))

/-- `H'(l) > 0` for `0 < l < L`. -/
theorem H'_pos {l : ℝ} (hl : l ∈ Ioo 0 L) : 0 < H' l := by
  have := hH.H'_strictMonoOn (left_mem_Ico.2 hH.L_pos) (Ioo_subset_Ico_self hl) hl.1
  rwa [hH.H'_zero] at this

/-- `H' ≥ 0` on `[0, L)`. -/
theorem H'_nonneg {l : ℝ} (hl : l ∈ Ico 0 L) : 0 ≤ H' l := by
  rcases hl.1.eq_or_lt with h | h
  · rw [← h, hH.H'_zero]
  · exact (hH.H'_pos ⟨h, hl.2⟩).le

/-- `H` is continuous on `[0, L)`. -/
theorem H_continuousOn : ContinuousOn H (Ico 0 L) := fun l hl =>
  (hH.H_deriv l hl).continuousWithinAt

/-- `H'` is continuous on `[0, L)`. -/
theorem H'_continuousOn : ContinuousOn H' (Ico 0 L) := fun l hl =>
  (hH.H'_deriv l hl).continuousWithinAt

/-- At interior points the derivative of `H` is two-sided. -/
theorem H_hasDerivAt {l : ℝ} (hl : l ∈ Ioo 0 L) : HasDerivAt H (H' l) l :=
  (hH.H_deriv l (Ioo_subset_Ico_self hl)).hasDerivAt (Ico_mem_nhds hl.1 hl.2)

/-- At interior points the derivative of `H'` is two-sided. -/
theorem H'_hasDerivAt {l : ℝ} (hl : l ∈ Ioo 0 L) : HasDerivAt H' (H'' l) l :=
  (hH.H'_deriv l (Ioo_subset_Ico_self hl)).hasDerivAt (Ico_mem_nhds hl.1 hl.2)

/-- `H'' ≥ 0` on `(0, L)` (`H'` is increasing). -/
theorem H''_nonneg {l : ℝ} (hl : l ∈ Ioo 0 L) : 0 ≤ H'' l := by
  have h := (hH.H'_hasDerivAt hl).deriv
  rw [← h, ← derivWithin_of_mem_nhds (Ico_mem_nhds hl.1 hl.2)]
  exact hH.H'_strictMonoOn.monotoneOn.derivWithin_nonneg

/-- For every `M` there is `l ∈ (0, L)` with `M < H' l`. -/
theorem exists_H'_gt (M : ℝ) : ∃ l ∈ Ioo 0 L, M < H' l := by
  have h1 : ∀ᶠ l in 𝓝[<] L, M < H' l := hH.H'_tendsto.eventually (eventually_gt_atTop M)
  have h2 : ∀ᶠ l in 𝓝[<] L, l ∈ Ioo 0 L := Ioo_mem_nhdsLT hH.L_pos
  obtain ⟨l, hl1, hl2⟩ := (h1.and h2).exists
  exact ⟨l, hl2, hl1⟩

end Assumption17_1H

namespace Assumption17_1V

variable (hV : Assumption17_1V V V' V'')
include hV

/-- `V'(y) > 0` for `y ≥ 0`: the derivative at the left end of a secant of a strictly
concave function exceeds the (positive) slope. -/
theorem V'_pos {y : ℝ} (hy : 0 ≤ y) : 0 < V' y := by
  have hy' : y ∈ Ici (0 : ℝ) := hy
  have hy1 : y + 1 ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have h1 := hV.V_conc.slope_lt_of_hasDerivWithinAt hy' hy1 (by linarith) (hV.V_deriv y hy)
  have h2 : 0 < slope V y (y + 1) := by
    rw [slope_def_field]
    exact div_pos (sub_pos.2 (hV.V_mono hy' hy1 (by linarith))) (by linarith)
  linarith

/-- `V'` is strictly decreasing on `[0, ∞)` (strict concavity of `V`). -/
theorem V'_strictAntiOn : StrictAntiOn V' (Ici 0) := fun _ hx _ hy hxy =>
  (hV.V_conc.slope_lt_of_hasDerivWithinAt hx hy hxy (hV.V_deriv _ hx)).trans'
    (hV.V_conc.lt_slope_of_hasDerivWithinAt hx hy hxy (hV.V_deriv _ hy))

/-- `V` is continuous on `[0, ∞)`. -/
theorem V_continuousOn : ContinuousOn V (Ici 0) := fun y hy =>
  (hV.V_deriv y hy).continuousWithinAt

/-- `V'` is continuous on `[0, ∞)`. -/
theorem V'_continuousOn : ContinuousOn V' (Ici 0) := fun y hy =>
  (hV.V'_deriv y hy).continuousWithinAt

/-- At `y > 0` the derivative of `V` is two-sided. -/
theorem V_hasDerivAt {y : ℝ} (hy : 0 < y) : HasDerivAt V (V' y) y :=
  (hV.V_deriv y hy.le).hasDerivAt (Ici_mem_nhds hy)

/-- `V'(y) ≤ V'(0)` for `y ≥ 0`. -/
theorem V'_le_V'_zero {y : ℝ} (hy : 0 ≤ y) : V' y ≤ V' 0 :=
  hV.V'_strictAntiOn.antitoneOn (mem_Ici.2 le_rfl) hy hy

end Assumption17_1V

/-! ### The consumer's problem (Exercise 17.1)

For a fixed current state the young agent's problem is `max_{l ∈ [0, L)} −H(l) + ∫ V(l c) dμ`,
where `μ = π(x, ·)` and `c(x') = x p(x)/p(x')` is the (random) real return on money. We treat
a general probability space `Ω`, a measurable `c` with `0 < c ≤ C`. -/

/-- A function continuous on `[0, ∞)` composed with a nonnegative measurable function is
measurable. -/
theorem measurable_comp_of_continuousOn_Ici {Ω : Type*} [MeasurableSpace Ω] {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 0)) {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) :
    Measurable fun ω => g (f ω) := by
  have hc : Continuous fun y : ℝ => g (max y 0) :=
    hg.comp_continuous (continuous_id.max continuous_const) fun y => le_max_right y 0
  have := hc.measurable.comp hf
  convert this using 1
  funext ω
  simp [max_eq_left (hf0 ω)]

/-- The integral of a strictly positive integrable function against a probability measure is
strictly positive. -/
theorem integral_pos_of_forall_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) (hpos : ∀ ω, 0 < f ω) :
    0 < ∫ ω, f ω ∂μ := by
  refine (integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hf).2 ?_
  have : Function.support f = univ :=
    eq_univ_of_forall fun ω => Function.mem_support.2 (hpos ω).ne'
  rw [this, measure_univ]
  exact one_pos

/-- Expected marginal utility of labour, `l ↦ ∫ c V'(l c) dμ`. -/
noncomputable def margUtil {Ω : Type*} [MeasurableSpace Ω] (V' : ℝ → ℝ) (μ : Measure Ω)
    (c : Ω → ℝ) (l : ℝ) : ℝ :=
  ∫ ω, c ω * V' (l * c ω) ∂μ

/-- The young agent's objective, `l ↦ −H(l) + ∫ V(l c) dμ`. -/
noncomputable def consumerObj {Ω : Type*} [MeasurableSpace Ω] (H V : ℝ → ℝ) (μ : Measure Ω)
    (c : Ω → ℝ) (l : ℝ) : ℝ :=
  -H l + ∫ ω, V (l * c ω) ∂μ

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {c : Ω → ℝ}
  {C : ℝ}

omit [IsProbabilityMeasure μ] in
/-- The marginal-utility integrand is integrable and bounded by `C V'(0)`. -/
theorem integrable_margUtil (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) [IsFiniteMeasure μ] {l : ℝ} (hl : 0 ≤ l) :
    Integrable (fun ω => c ω * V' (l * c ω)) μ := by
  have hm : Measurable fun ω => c ω * V' (l * c ω) :=
    hc.mul (measurable_comp_of_continuousOn_Ici hV.V'_continuousOn (measurable_const.mul hc)
      fun ω => mul_nonneg hl (hcpos ω).le)
  refine Integrable.mono' (integrable_const (C * V' 0)) hm.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have h0 : 0 ≤ l * c ω := mul_nonneg hl (hcpos ω).le
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hcpos ω) (hV.V'_pos h0))]
  exact mul_le_mul (hcle ω) (hV.V'_le_V'_zero h0) (hV.V'_pos h0).le
    ((hcpos ω).le.trans (hcle ω))

omit [IsProbabilityMeasure μ] in
/-- `l ↦ ∫ c V'(l c) dμ` is continuous on `[0, ∞)` (dominated convergence). -/
theorem continuousOn_margUtil (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) [IsFiniteMeasure μ] :
    ContinuousOn (margUtil V' μ c) (Ici 0) := by
  refine continuousOn_of_dominated (bound := fun _ => C * V' 0)
    (fun l hl => (integrable_margUtil hV hc hcpos hcle hl).aestronglyMeasurable)
    (fun l hl => ae_of_all _ fun ω => ?_) (integrable_const _) (ae_of_all _ fun ω => ?_)
  · have h0 : 0 ≤ l * c ω := mul_nonneg hl (hcpos ω).le
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hcpos ω) (hV.V'_pos h0))]
    exact mul_le_mul (hcle ω) (hV.V'_le_V'_zero h0) (hV.V'_pos h0).le
      ((hcpos ω).le.trans (hcle ω))
  · exact continuousOn_const.mul (hV.V'_continuousOn.comp (continuousOn_id.mul continuousOn_const)
      fun l hl => mul_nonneg hl (hcpos ω).le)

/-- `l ↦ ∫ c V'(l c) dμ` is strictly decreasing on `[0, ∞)`. -/
theorem margUtil_strictAntiOn (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) : StrictAntiOn (margUtil V' μ c) (Ici 0) := by
  intro l₁ hl₁ l₂ hl₂ hlt
  have hl₁' : (0 : ℝ) ≤ l₁ := hl₁
  have hl₂' : (0 : ℝ) ≤ l₂ := hl₂
  rw [← sub_pos, margUtil, margUtil, ← integral_sub (integrable_margUtil hV hc hcpos hcle hl₁')
    (integrable_margUtil hV hc hcpos hcle hl₂')]
  refine integral_pos_of_forall_pos ((integrable_margUtil hV hc hcpos hcle hl₁').sub
    (integrable_margUtil hV hc hcpos hcle hl₂')) fun ω => ?_
  rw [← mul_sub]
  refine mul_pos (hcpos ω) (sub_pos.2 (hV.V'_strictAntiOn ?_ ?_ ?_))
  · exact mul_nonneg hl₁' (hcpos ω).le
  · exact mul_nonneg hl₂' (hcpos ω).le
  · exact mul_lt_mul_of_pos_right hlt (hcpos ω)

/-- `∫ c V'(0) dμ > 0`. -/
theorem margUtil_zero_pos (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) : 0 < margUtil V' μ c 0 :=
  integral_pos_of_forall_pos (integrable_margUtil hV hc hcpos hcle le_rfl) fun ω =>
    mul_pos (hcpos ω) (hV.V'_pos (by rw [zero_mul]))

/-- `∫ c V'(l c) dμ ≤ C V'(0)`. -/
theorem margUtil_le (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) {l : ℝ} (hl : 0 ≤ l) :
    margUtil V' μ c l ≤ C * V' 0 := by
  have h := integral_mono (integrable_margUtil (μ := μ) hV hc hcpos hcle hl)
    (integrable_const (C * V' 0))
    (fun ω => mul_le_mul (hcle ω) (hV.V'_le_V'_zero (mul_nonneg hl (hcpos ω).le))
      (hV.V'_pos (mul_nonneg hl (hcpos ω).le)).le ((hcpos ω).le.trans (hcle ω)))
  simpa [margUtil] using h

/-- **The first-order condition has exactly one root.** `H'(n) = ∫ c V'(n c) dμ` has a unique
solution `n ∈ [0, L)`, and it lies in `(0, L)`. -/
theorem exists_unique_foc (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1V V V' V'')
    (hc : Measurable c) (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) :
    ∃ n ∈ Ioo 0 L, H' n = margUtil V' μ c n ∧
      ∀ m ∈ Ico 0 L, H' m = margUtil V' μ c m → m = n := by
  set foc : ℝ → ℝ := fun l => H' l - margUtil V' μ c l with hfoc
  have hmono : StrictMonoOn foc (Ico 0 L) := fun x hx y hy hxy => by
    have h1 := hH.H'_strictMonoOn hx hy hxy
    have h2 := margUtil_strictAntiOn (μ := μ) hV hc hcpos hcle (Ico_subset_Ici_self hx)
      (Ico_subset_Ici_self hy) hxy
    simp only [hfoc]
    linarith
  have hcont : ContinuousOn foc (Ico 0 L) :=
    hH.H'_continuousOn.sub ((continuousOn_margUtil (μ := μ) hV hc hcpos hcle).mono
      Ico_subset_Ici_self)
  obtain ⟨l₁, hl₁, hl₁M⟩ := hH.exists_H'_gt (C * V' 0)
  have h0 : foc 0 < 0 := by
    simp only [hfoc, hH.H'_zero, zero_sub, neg_neg_iff_pos]
    exact margUtil_zero_pos hV hc hcpos hcle
  have h1 : 0 < foc l₁ := by
    have := margUtil_le (μ := μ) hV hc hcpos hcle hl₁.1.le
    simp only [hfoc]
    linarith
  have hsub : Icc 0 l₁ ⊆ Ico 0 L := fun y hy => ⟨hy.1, hy.2.trans_lt hl₁.2⟩
  obtain ⟨n, hn, hn0⟩ := intermediate_value_Icc hl₁.1.le (hcont.mono hsub) ⟨h0.le, h1.le⟩
  have hnpos : 0 < n := by
    rcases hn.1.eq_or_lt with h | h
    · rw [← h] at hn0; linarith
    · exact h
  refine ⟨n, ⟨hnpos, hn.2.trans_lt hl₁.2⟩, by simpa [hfoc, sub_eq_zero] using hn0, ?_⟩
  intro m hm hfm
  have hfm' : foc m = foc n := by simp only [hfoc]; rw [hfm, sub_self]; exact hn0.symm
  exact hmono.injOn hm (hsub hn) hfm'

omit [IsProbabilityMeasure μ] in
/-- The utility integrand `V(l c)` is integrable. -/
theorem integrable_utility (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) [IsFiniteMeasure μ] {l : ℝ} (hl : 0 ≤ l) :
    Integrable (fun ω => V (l * c ω)) μ := by
  have hm : Measurable fun ω => V (l * c ω) :=
    measurable_comp_of_continuousOn_Ici hV.V_continuousOn (measurable_const.mul hc)
      fun ω => mul_nonneg hl (hcpos ω).le
  refine Integrable.mono' (integrable_const (V (l * C))) hm.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have h0 : 0 ≤ l * c ω := mul_nonneg hl (hcpos ω).le
  rw [Real.norm_eq_abs, abs_of_nonneg (hV.V_nonneg _ h0)]
  exact hV.V_mono.monotoneOn h0 (mul_nonneg hl ((hcpos ω).le.trans (hcle ω)))
    (mul_le_mul_of_nonneg_left (hcle ω) hl)

omit [IsProbabilityMeasure μ] in
/-- `l ↦ ∫ V(l c) dμ` is continuous on `[0, B]`. -/
theorem continuousOn_utility (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) [IsFiniteMeasure μ] (B : ℝ) :
    ContinuousOn (fun l => ∫ ω, V (l * c ω) ∂μ) (Icc 0 B) := by
  refine continuousOn_of_dominated (bound := fun _ => V (B * C))
    (fun l hl => (integrable_utility hV hc hcpos hcle hl.1).aestronglyMeasurable)
    (fun l hl => ae_of_all _ fun ω => ?_) (integrable_const _) (ae_of_all _ fun ω => ?_)
  · have h0 : 0 ≤ l * c ω := mul_nonneg hl.1 (hcpos ω).le
    rw [Real.norm_eq_abs, abs_of_nonneg (hV.V_nonneg _ h0)]
    have hC : 0 ≤ C := (hcpos ω).le.trans (hcle ω)
    exact hV.V_mono.monotoneOn h0 (mul_nonneg (hl.1.trans hl.2) hC)
      (mul_le_mul hl.2 (hcle ω) (hcpos ω).le (hl.1.trans hl.2))
  · exact hV.V_continuousOn.comp (continuousOn_id.mul continuousOn_const)
      fun l hl => mul_nonneg hl.1 (hcpos ω).le

omit [IsProbabilityMeasure μ] in
/-- Differentiation under the integral sign: for `l > 0`,
`d/dl ∫ V(l c) dμ = ∫ c V'(l c) dμ`. -/
theorem hasDerivAt_utility (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) [IsFiniteMeasure μ] {l : ℝ} (hl : 0 < l) :
    HasDerivAt (fun l => ∫ ω, V (l * c ω) ∂μ) (margUtil V' μ c l) l := by
  have hs : Ioi (l / 2) ∈ 𝓝 l := Ioi_mem_nhds (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun l ω => V (l * c ω)) (F' := fun l ω => c ω * V' (l * c ω))
    (bound := fun _ => C * V' 0) hs
    (Filter.mem_of_superset hs fun x hx =>
      (integrable_utility hV hc hcpos hcle (by simp only [mem_Ioi] at hx; linarith)
        ).aestronglyMeasurable)
    (integrable_utility hV hc hcpos hcle hl.le)
    (integrable_margUtil hV hc hcpos hcle hl.le).aestronglyMeasurable
    (ae_of_all _ fun ω x hx => by
      have hx0 : 0 ≤ x * c ω := mul_nonneg (by simp only [mem_Ioi] at hx; linarith) (hcpos ω).le
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hcpos ω) (hV.V'_pos hx0))]
      exact mul_le_mul (hcle ω) (hV.V'_le_V'_zero hx0) (hV.V'_pos hx0).le
        ((hcpos ω).le.trans (hcle ω)))
    (integrable_const _)
    (ae_of_all _ fun ω x hx => by
      have hx0 : 0 < x * c ω := mul_pos (by simp only [mem_Ioi] at hx; linarith) (hcpos ω)
      have h1 : HasDerivAt (fun y => y * c ω) (c ω) x := by
        simpa using (hasDerivAt_id x).mul_const (c ω)
      have := (hV.V_hasDerivAt hx0).comp x h1
      rw [mul_comm] at this
      exact this)
  exact key.2

/-- **The consumer's problem** (Exercise 17.1, abstract form). With `0 < c ≤ C` measurable, the
problem `max_{l ∈ [0, L)} −H(l) + ∫ V(l c) dμ` has a unique solution `n`; it is strictly
positive and is the unique root in `[0, L)` of the first-order condition
`H'(n) = ∫ c V'(n c) dμ`. -/
theorem consumer_problem (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1V V V' V'')
    (hc : Measurable c) (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) :
    ∃ n ∈ Ioo 0 L, H' n = margUtil V' μ c n ∧
      (∀ l ∈ Ico 0 L, l ≠ n → consumerObj H V μ c l < consumerObj H V μ c n) ∧
      ∀ m ∈ Ico 0 L, H' m = margUtil V' μ c m → m = n := by
  obtain ⟨n, hn, hfoc, huniq⟩ := exists_unique_foc (μ := μ) hH hV hc hcpos hcle
  refine ⟨n, hn, hfoc, ?_, huniq⟩
  have hcont : ContinuousOn (consumerObj H V μ c) (Ico 0 L) :=
    hH.H_continuousOn.neg.add ((continuousOn_utility hV hc hcpos hcle L).mono
      Ico_subset_Icc_self)
  have hderiv : ∀ x ∈ Ioo 0 L,
      HasDerivAt (consumerObj H V μ c) (-H' x + margUtil V' μ c x) x := fun x hx =>
    (hH.H_hasDerivAt hx).neg.add (hasDerivAt_utility hV hc hcpos hcle hx.1)
  have hstrict : StrictMonoOn (fun l => H' l - margUtil V' μ c l) (Ico 0 L) :=
    fun x hx y hy hxy => by
      have h1 := hH.H'_strictMonoOn hx hy hxy
      have h2 := margUtil_strictAntiOn (μ := μ) hV hc hcpos hcle (Ico_subset_Ici_self hx)
        (Ico_subset_Ici_self hy) hxy
      linarith
  have hn' : n ∈ Ico 0 L := Ioo_subset_Ico_self hn
  have hfn : H' n - margUtil V' μ c n = 0 := by rw [hfoc, sub_self]
  have hup : StrictMonoOn (consumerObj H V μ c) (Icc 0 n) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 n)
      (hcont.mono fun y hy => ⟨hy.1, hy.2.trans_lt hn.2⟩) fun x hx => ?_
    rw [interior_Icc] at hx
    have hxL : x ∈ Ioo 0 L := ⟨hx.1, hx.2.trans hn.2⟩
    rw [(hderiv x hxL).deriv]
    have := hstrict (Ioo_subset_Ico_self hxL) hn' hx.2
    simp only [hfn] at this
    linarith
  have hdown : StrictAntiOn (consumerObj H V μ c) (Ico n L) := by
    refine strictAntiOn_of_deriv_neg (convex_Ico n L)
      (hcont.mono fun y hy => ⟨hn.1.le.trans hy.1, hy.2⟩) fun x hx => ?_
    rw [interior_Ico] at hx
    have hxL : x ∈ Ioo 0 L := ⟨hn.1.trans hx.1, hx.2⟩
    rw [(hderiv x hxL).deriv]
    have := hstrict hn' (Ioo_subset_Ico_self hxL) hx.1
    simp only [hfn] at this
    linarith
  intro l hl hln
  rcases lt_or_gt_of_ne hln with h | h
  · exact hup ⟨hl.1, h.le⟩ ⟨hn.1.le, le_rfl⟩ h
  · exact hdown ⟨le_rfl, hn.2⟩ ⟨h.le, hl.2⟩ h

/-! ### Exercise 17.1 and the equilibrium conditions -/

/-- **Exercise 17.1** (p. 504). Let `p : X → ℝ` be a measurable price function bounded away from
zero (`p ≥ pmin > 0`; no upper bound is needed). For each `x ∈ X = [a, b]` the young agent's
problem `max_{l ∈ [0, L)} −H(l) + ∫ V(x l p(x)/p(x')) π(x, dx')` has a unique solution `n`
(any other `l` does strictly worse), `n > 0`, `n` satisfies the first-order condition
`H'(n) = ∫ (x p(x)/p(x')) V'(x n p(x)/p(x')) π(x, dx')`, and `n` is the only root of that
condition in `[0, L)`. -/
theorem ex_17_1 {a b : ℝ} (ha : 0 < a) (hA : Assumption17_1 L H H' H'' V V' V'')
    (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ] {p : Icc a b → ℝ} (hp : Measurable p)
    {pmin : ℝ} (hpmin : 0 < pmin) (hpge : ∀ x, pmin ≤ p x) (x : Icc a b) :
    ∃ n ∈ Ioo 0 L,
      (∀ l ∈ Ico 0 L, l ≠ n → -H l + ∫ x', V (x.1 * l * p x / p x') ∂κ x <
        -H n + ∫ x', V (x.1 * n * p x / p x') ∂κ x) ∧
      H' n = ∫ x', x.1 * p x / p x' * V' (x.1 * n * p x / p x') ∂κ x ∧
      ∀ m ∈ Ico 0 L, H' m = ∫ x', x.1 * p x / p x' * V' (x.1 * m * p x / p x') ∂κ x → m = n := by
  set c : Icc a b → ℝ := fun x' => x.1 * p x / p x' with hcdef
  have hx : 0 < x.1 := ha.trans_le x.2.1
  have hppos : ∀ x', 0 < p x' := fun x' => hpmin.trans_le (hpge x')
  have hc : Measurable c := measurable_const.div hp
  have hcpos : ∀ x', 0 < c x' := fun x' => div_pos (mul_pos hx (hppos x)) (hppos x')
  have hcle : ∀ x', c x' ≤ x.1 * p x / pmin := fun x' =>
    div_le_div_of_nonneg_left (mul_pos hx (hppos x)).le hpmin (hpge x')
  have e : ∀ (l : ℝ) (x' : Icc a b), x.1 * l * p x / p x' = l * c x' := fun l x' => by
    simp only [hcdef]; ring
  obtain ⟨n, hn, hfoc, hmax, huniq⟩ :=
    consumer_problem (μ := κ x) hA.hH hA.hV hc hcpos hcle
  refine ⟨n, hn, ?_, ?_, ?_⟩
  · intro l hl hln
    simpa only [e, consumerObj] using hmax l hl hln
  · simpa only [e, margUtil] using hfoc
  · intro m hm hfm
    exact huniq m hm (by simpa only [e, margUtil] using hfm)

variable {a b : ℝ} (κ : Kernel (Icc a b) (Icc a b)) in
/-- A **stationary competitive equilibrium with valued money** (p. 503): a strictly positive
measurable price function `p` and a labour supply `n : X → [0, L)` such that (1) `n(x)`
maximises `−H(l) + ∫ V(x l p(x)/p(x')) π(x, dx')` over `l ∈ [0, L)`, and (2) the goods market
clears, `x n(x) = M/p(x)`. -/
structure IsStationaryEqm (L M : ℝ) (H V : ℝ → ℝ) (p n : Icc a b → ℝ) : Prop where
  p_pos : ∀ x, 0 < p x
  p_meas : Measurable p
  n_mem : ∀ x, n x ∈ Ico 0 L
  optimal : ∀ x, ∀ l ∈ Ico 0 L, -H l + ∫ x', V (x.1 * l * p x / p x') ∂κ x ≤
    -H (n x) + ∫ x', V (x.1 * n x * p x / p x') ∂κ x
  clearing : ∀ x, x.1 * n x = M / p x

/-- **Equilibrium implies (3)** (p. 504). In a stationary equilibrium `0 < n(x) < L`,
`p(x) = M/(x n(x))`, and `n` satisfies
`n(x) H'(n(x)) = ∫ x' n(x') V'(x' n(x')) π(x, dx')`. The price is automatically bounded away
from zero (`p ≥ M/(bL)`), so Exercise 17.1 applies. -/
theorem eq3_of_isStationaryEqm {a b M : ℝ} (ha : 0 < a) (hM : 0 < M)
    (hA : Assumption17_1 L H H' H'' V V' V'') {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    {p n : Icc a b → ℝ} (h : IsStationaryEqm κ L M H V p n) :
    (∀ x, n x ∈ Ioo 0 L) ∧ (∀ x, p x = M / (x.1 * n x)) ∧
      ∀ x, n x * H' (n x) = ∫ x', x'.1 * n x' * V' (x'.1 * n x') ∂κ x := by
  have hxpos : ∀ x : Icc a b, 0 < x.1 := fun x => ha.trans_le x.2.1
  have hnpos : ∀ x, 0 < n x := fun x => by
    have h1 : 0 < x.1 * n x := by rw [h.clearing x]; exact div_pos hM (h.p_pos x)
    exact pos_of_mul_pos_right h1 (hxpos x).le
  have hnmem : ∀ x, n x ∈ Ioo 0 L := fun x => ⟨hnpos x, (h.n_mem x).2⟩
  have hpeq : ∀ x, p x = M / (x.1 * n x) := fun x => by
    rw [h.clearing x, div_div_cancel₀ hM.ne']
  have hbL : ∀ x : Icc a b, x.1 * n x ≤ b * L := fun x =>
    mul_le_mul x.2.2 (h.n_mem x).2.le (hnpos x).le ((hxpos x).le.trans x.2.2)
  refine ⟨hnmem, hpeq, fun x => ?_⟩
  have hb : 0 < b := (hxpos x).trans_le x.2.2
  have hpmin : ∀ x', M / (b * L) ≤ p x' := fun x' => by
    rw [hpeq x']
    exact div_le_div_of_nonneg_left hM.le (mul_pos (hxpos x') (hnpos x')) (hbL x')
  obtain ⟨n₀, hn₀, hmax, hfoc, -⟩ :=
    ex_17_1 ha hA κ h.p_meas (div_pos hM (mul_pos hb hA.hH.L_pos)) hpmin x
  have heq : n x = n₀ := by
    by_contra hne
    have h1 := hmax (n x) (h.n_mem x) hne
    have h2 := h.optimal x n₀ (Ioo_subset_Ico_self hn₀)
    linarith
  rw [← heq] at hfoc
  rw [hfoc, ← integral_const_mul]
  congr 1
  funext x'
  have hk : x.1 * n x * p x / p x' = x'.1 * n x' := by
    rw [h.clearing x, h.clearing x', div_mul_cancel₀ M (h.p_pos x).ne']
  have e : n x * (x.1 * p x / p x' * V' (x.1 * n x * p x / p x')) =
      (x.1 * n x * p x / p x') * V' (x.1 * n x * p x / p x') := by ring
  rw [e, hk]

/-- **(3) implies equilibrium** (p. 504, the book's claim). If `n : X → (0, L)` is measurable
and satisfies `n(x) H'(n(x)) = ∫ x' n(x') V'(x' n(x')) π(x, dx')`, then `p(x) = M/(x n(x))`
and `n` form a stationary competitive equilibrium. (The book says only "strictly positive";
`n < L` is needed for `H'(n)` to be defined, and gives `p ≥ M/(bL) > 0`.) -/
theorem isStationaryEqm_of_eq3 {a b M : ℝ} (ha : 0 < a) (hM : 0 < M)
    (hA : Assumption17_1 L H H' H'' V V' V'') {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    {n : Icc a b → ℝ} (hn : Measurable n) (hnmem : ∀ x, n x ∈ Ioo 0 L)
    (h3 : ∀ x, n x * H' (n x) = ∫ x', x'.1 * n x' * V' (x'.1 * n x') ∂κ x) :
    IsStationaryEqm κ L M H V (fun x => M / (x.1 * n x)) n := by
  have hxpos : ∀ x : Icc a b, 0 < x.1 := fun x => ha.trans_le x.2.1
  have hxn : ∀ x, 0 < x.1 * n x := fun x => mul_pos (hxpos x) (hnmem x).1
  have hppos : ∀ x : Icc a b, 0 < M / (x.1 * n x) := fun x => div_pos hM (hxn x)
  have hpm : Measurable fun x : Icc a b => M / (x.1 * n x) :=
    measurable_const.div (measurable_subtype_coe.mul hn)
  refine ⟨hppos, hpm, fun x => Ioo_subset_Ico_self (hnmem x), fun x l hl => ?_, fun x => ?_⟩
  · have hb : 0 < b := (hxpos x).trans_le x.2.2
    have hbL : ∀ x' : Icc a b, x'.1 * n x' ≤ b * L := fun x' =>
      mul_le_mul x'.2.2 (hnmem x').2.le (hnmem x').1.le hb.le
    have hpmin : ∀ x' : Icc a b, M / (b * L) ≤ M / (x'.1 * n x') := fun x' =>
      div_le_div_of_nonneg_left hM.le (hxn x') (hbL x')
    obtain ⟨n₀, -, hmax, -, huniq⟩ :=
      ex_17_1 ha hA κ hpm (div_pos hM (mul_pos hb hA.hH.L_pos)) hpmin x
    have hk : ∀ x' : Icc a b, x.1 * (M / (x.1 * n x)) / (M / (x'.1 * n x')) =
        (n x)⁻¹ * (x'.1 * n x') := fun x' => by
      have := (hxpos x).ne'; have := (hnmem x).1.ne'; have := (hxn x').ne'
      field_simp
    have hk2 : ∀ x' : Icc a b, x.1 * n x * (M / (x.1 * n x)) / (M / (x'.1 * n x')) =
        x'.1 * n x' := fun x' => by
      have e1 : x.1 * n x * (M / (x.1 * n x)) = M := by
        have := (hxn x).ne'
        rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self this, mul_one]
      rw [e1, div_div_cancel₀ hM.ne']
    have hint : ∫ x', x.1 * (M / (x.1 * n x)) / (M / (x'.1 * n x')) *
        V' (x.1 * n x * (M / (x.1 * n x)) / (M / (x'.1 * n x'))) ∂κ x =
        (n x)⁻¹ * ∫ x', x'.1 * n x' * V' (x'.1 * n x') ∂κ x := by
      rw [← integral_const_mul]
      congr 1
      funext x'
      rw [hk, hk2]
      ring
    have heq : n x = n₀ := by
      refine huniq (n x) (Ioo_subset_Ico_self (hnmem x)) ?_
      rw [hint, ← h3 x, inv_mul_cancel_left₀ (hnmem x).1.ne']
    rcases eq_or_ne l (n x) with rfl | hne
    · exact le_rfl
    · have := hmax l hl (heq ▸ hne)
      rw [← heq] at this
      exact this.le
  · rw [div_div_cancel₀ hM.ne']

/-! ### Equation (4) and Proposition 1 -/

/-- `ζ(l) = l H'(l)` (p. 504). -/
def olgZeta (H' : ℝ → ℝ) (l : ℝ) : ℝ := l * H' l

/-- `φ(y) = y V'(y)` (p. 504). -/
def olgPhi (V' : ℝ → ℝ) (y : ℝ) : ℝ := y * V' y

/-- Equation (3) is equation (4), `ζ(n(x)) = ∫ φ(x' n(x')) π(x, dx')` (p. 504). -/
theorem eq3_iff_eq4 {a b : ℝ} (κ : Kernel (Icc a b) (Icc a b)) (n : Icc a b → ℝ) (x : Icc a b) :
    n x * H' (n x) = ∫ x', x'.1 * n x' * V' (x'.1 * n x') ∂κ x ↔
      olgZeta H' (n x) = ∫ x', olgPhi V' (x'.1 * n x') ∂κ x :=
  Iff.rfl

/-- `∫ c V'(l c) dμ > 0` for `l ≥ 0`. -/
theorem margUtil_pos (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) {l : ℝ} (hl : 0 ≤ l) :
    0 < margUtil V' μ c l :=
  integral_pos_of_forall_pos (integrable_margUtil hV hc hcpos hcle hl) fun ω =>
    mul_pos (hcpos ω) (hV.V'_pos (mul_nonneg hl (hcpos ω).le))

/-- With serially independent shocks, `∫ φ(x' l) dμ = l ∫ x' V'(l x') dμ`. -/
theorem integral_olgPhi {a b : ℝ} (μ : Measure (Icc a b)) (l : ℝ) :
    ∫ x', olgPhi V' (x'.1 * l) ∂μ = l * margUtil V' μ (fun x' => x'.1) l := by
  rw [margUtil, ← integral_const_mul]
  congr 1
  funext x'
  simp only [olgPhi]
  rw [mul_comm x'.1 l]
  ring

/-- **Proposition 1** (p. 505). With serially independent shocks (`π(x, ·) = μ` a probability
measure on `X = [a, b]`, `a > 0`) and Assumption 17.1, equation (5),
`ζ(n) = ∫ φ(x' n) μ(dx')`, has exactly one solution `n ∈ (0, L)`. For `n > 0`, (5) is the
first-order condition `H'(n) = ∫ x' V'(x' n) dμ`, whose left side is strictly increasing and
right side strictly decreasing (`exists_unique_foc`). -/
theorem proposition_1 {a b : ℝ} (ha : 0 < a) (hA : Assumption17_1 L H H' H'' V V' V'')
    (μ : Measure (Icc a b)) [IsProbabilityMeasure μ] :
    ∃! n, n ∈ Ioo 0 L ∧ olgZeta H' n = ∫ x', olgPhi V' (x'.1 * n) ∂μ := by
  have hc : Measurable fun x' : Icc a b => x'.1 := measurable_subtype_coe
  have hcpos : ∀ x' : Icc a b, 0 < x'.1 := fun x' => ha.trans_le x'.2.1
  have hcle : ∀ x' : Icc a b, x'.1 ≤ b := fun x' => x'.2.2
  have hiff : ∀ l, 0 < l → (olgZeta H' l = ∫ x', olgPhi V' (x'.1 * l) ∂μ ↔
      H' l = margUtil V' μ (fun x' => x'.1) l) := fun l hl => by
    rw [integral_olgPhi, olgZeta]
    exact ⟨fun h => mul_left_cancel₀ hl.ne' h, fun h => by rw [h]⟩
  obtain ⟨n, hn, hfoc, huniq⟩ := exists_unique_foc (μ := μ) hA.hH hA.hV hc hcpos hcle
  exact ⟨n, ⟨hn, (hiff n hn.1).2 hfoc⟩, fun m hm =>
    huniq m (Ioo_subset_Ico_self hm.1) ((hiff m hm.1.1).1 hm.2)⟩

/-- **The NOTE's repair of the uniqueness step of Proposition 1.** The log-ratio
`h(l) = log ζ(l) − log ∫ φ(x' l) dμ` is strictly increasing on `(0, L)`, so the two curves of
Figure 17.1 cross at most once. (Indeed `h(l) = log H'(l) − log ∫ x' V'(x' l) dμ`.) The book's
pointwise "crosses from below" argument through the elasticities (6)–(7) is not needed. -/
theorem proposition_1_logRatio_strictMonoOn {a b : ℝ} (ha : 0 < a)
    (hA : Assumption17_1 L H H' H'' V V' V'') (μ : Measure (Icc a b)) [IsProbabilityMeasure μ] :
    StrictMonoOn (fun l => Real.log (olgZeta H' l) - Real.log (∫ x', olgPhi V' (x'.1 * l) ∂μ))
      (Ioo 0 L) := by
  have hc : Measurable fun x' : Icc a b => x'.1 := measurable_subtype_coe
  have hcpos : ∀ x' : Icc a b, 0 < x'.1 := fun x' => ha.trans_le x'.2.1
  have hcle : ∀ x' : Icc a b, x'.1 ≤ b := fun x' => x'.2.2
  intro x hx y hy hxy
  simp only [integral_olgPhi, olgZeta]
  have hHx := hA.hH.H'_pos hx
  have hHy := hA.hH.H'_pos hy
  have hmx := margUtil_pos (μ := μ) hA.hV hc hcpos hcle hx.1.le
  have hmy := margUtil_pos (μ := μ) hA.hV hc hcpos hcle hy.1.le
  rw [Real.log_mul hx.1.ne' hHx.ne', Real.log_mul hx.1.ne' hmx.ne', Real.log_mul hy.1.ne' hHy.ne',
    Real.log_mul hy.1.ne' hmy.ne']
  have h1 := Real.log_lt_log hHx (hA.hH.H'_strictMonoOn (Ioo_subset_Ico_self hx)
    (Ioo_subset_Ico_self hy) hxy)
  have h2 := Real.log_lt_log hmy (margUtil_strictAntiOn (μ := μ) hA.hV hc hcpos hcle
    (mem_Ici.2 hx.1.le) (mem_Ici.2 hy.1.le) hxy)
  linarith

/-- **Correction (Proposition 1, step 4).** Under Assumption 17.1, `φ(0) = 0 · V'(0) = 0`, so the
first case of the existence argument (`φ(0) > 0`, top panel of Figure 17.1) cannot occur. -/
theorem proposition_1_phi_zero_counterexample : ¬ 0 < olgPhi V' 0 := by
  simp [olgPhi]

/-- **Correction (p. 515).** Strict monotonicity and strict concavity of `V` do not make the
relative risk aversion `−y V''(y)/V'(y)` strictly positive on all of `ℝ₊`: it is `0` at
`y = 0` (for every `V`, in particular every `V` satisfying Assumption 17.1). -/
theorem rra_pos_counterexample :
    ¬ ∀ y : ℝ, 0 ≤ y → 0 < -(y * V'' y) / V' y := fun h => by
  have := h 0 le_rfl
  simp at this

/-! ### The elasticity of `ζ` (equation (6)) -/

/-- The counterexample disutility `H(l) = l − 2 log(2 − l) + 6(2 − l) − 3(2 − l)² + (2/3)(2 − l)³`
on `[0, 2)`. -/
noncomputable def olgExH (l : ℝ) : ℝ :=
  l - 2 * Real.log (2 - l) + 6 * (2 - l) - 3 * (2 - l) ^ 2 + 2 / 3 * (2 - l) ^ 3
/-- Its derivative `H'(l) = 1 + 2(l − 1)³/(2 − l)`. -/
noncomputable def olgExH1 (l : ℝ) : ℝ := 1 + 2 * (l - 1) ^ 3 / (2 - l)
/-- Its second derivative `H''(l) = 2(l − 1)²(5 − 2l)/(2 − l)²`, which vanishes at `l = 1`. -/
noncomputable def olgExH2 (l : ℝ) : ℝ := 2 * (l - 1) ^ 2 * (5 - 2 * l) / (2 - l) ^ 2

/-- `H' ` is the derivative of the counterexample `H`. -/
theorem olgExH_hasDerivAt {l : ℝ} (hl : l < 2) : HasDerivAt olgExH (olgExH1 l) l := by
  have h2 : (2 - l) ≠ 0 := by linarith
  have hd : HasDerivAt (fun l : ℝ => 2 - l) (-1) l := by
    simpa using (hasDerivAt_id' l).const_sub (2 : ℝ)
  have := ((((hasDerivAt_id' l).sub ((hd.log h2).const_mul 2)).add (hd.const_mul 6)).sub
    ((hd.pow 2).const_mul 3)).add ((hd.pow 3).const_mul (2 / 3))
  convert this using 1
  · funext y
    simp only [olgExH, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
  · simp only [olgExH1]
    field_simp
    ring

/-- `H''` is the derivative of the counterexample `H'`. -/
theorem olgExH1_hasDerivAt {l : ℝ} (hl : l < 2) : HasDerivAt olgExH1 (olgExH2 l) l := by
  have h2 : (2 - l) ≠ 0 := by linarith
  have hd : HasDerivAt (fun l : ℝ => 2 - l) (-1) l := by
    simpa using (hasDerivAt_id' l).const_sub (2 : ℝ)
  have hn : HasDerivAt (fun l : ℝ => (l - 1) ^ 3) (3 * (l - 1) ^ 2) l := by
    convert ((hasDerivAt_id' l).sub_const 1).pow 3 using 1
    norm_num
  have := (hasDerivAt_const l (1:ℝ)).add ((hn.const_mul 2).div hd h2)
  convert this using 1
  · funext y
    simp only [olgExH1, Pi.add_apply, Pi.div_apply]
  · simp only [olgExH2]
    field_simp
    ring

/-- The counterexample `H'` is positive on `(0, 2)`. -/
theorem olgExH1_pos {l : ℝ} (h0 : 0 < l) (hl : l < 2) : 0 < olgExH1 l := by
  simp only [olgExH1]
  have h2 : 0 < 2 - l := by linarith
  have : 0 < (2 - l) + 2 * (l - 1) ^ 3 := by
    rcases le_or_gt 1 l with h | h
    · nlinarith [pow_nonneg (sub_nonneg.2 h) 3]
    · nlinarith [mul_pos h0 h0, mul_pos (sub_pos.2 h) (sub_pos.2 h)]
  have e : 1 + 2 * (l - 1) ^ 3 / (2 - l) = ((2 - l) + 2 * (l - 1) ^ 3) / (2 - l) := by
    field_simp
  rw [e]
  exact div_pos this h2

/-- The counterexample `H''` is positive on `(−∞, 2)` except at `1`. -/
theorem olgExH2_pos {l : ℝ} (hl : l < 2) (h1 : l ≠ 1) : 0 < olgExH2 l := by
  simp only [olgExH2]
  have h2 : 0 < 2 - l := by linarith
  have : 0 < (l - 1) ^ 2 := by positivity
  apply div_pos _ (by positivity)
  have : 0 < 5 - 2 * l := by linarith
  positivity

/-- The counterexample `H'` tends to `+∞` at `2⁻`. -/
theorem olgExH1_tendsto : Tendsto olgExH1 (𝓝[<] 2) atTop := by
  have h1 : Tendsto (fun l : ℝ => 2 * (l - 1) ^ 3) (𝓝[<] 2) (𝓝 2) := by
    have : Tendsto (fun l : ℝ => 2 * (l - 1) ^ 3) (𝓝 2) (𝓝 (2 * (2 - 1) ^ 3)) :=
      ((continuous_const.mul ((continuous_id.sub continuous_const).pow 3)).tendsto 2)
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun l : ℝ => (2 - l)⁻¹) (𝓝[<] 2) atTop := by
    have : Tendsto (fun l : ℝ => 2 - l) (𝓝[<] 2) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun l : ℝ => 2 - l) (𝓝 2) (𝓝 (2 - 2)) :=
          (continuous_const.sub continuous_id).tendsto 2
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with l hl
        simp only [mem_Ioi, sub_pos]; exact hl
    exact tendsto_inv_nhdsGT_zero.comp this
  have := tendsto_atTop_add_const_left _ 1 (h1.pos_mul_atTop (by norm_num) h2)
  refine this.congr fun l => ?_
  simp only [olgExH1, div_eq_mul_inv]

/-- The counterexample `H'` is strictly increasing on `(−∞, 2)` (although `H''(1) = 0`). -/
theorem olgExH1_strictMonoOn : StrictMonoOn olgExH1 (Iio 2) := by
  have hc : ∀ s ⊆ Iio (2 : ℝ), ContinuousOn olgExH1 s := fun s hs l hl =>
    (olgExH1_hasDerivAt (hs hl)).continuousAt.continuousWithinAt
  have h1 : StrictMonoOn olgExH1 (Iic 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Iic 1) (hc _ fun l hl => ?_) fun l hl => ?_
    · exact lt_of_le_of_lt (mem_Iic.1 hl) (by norm_num)
    · rw [interior_Iic] at hl
      have hl2 : l < 2 := lt_trans hl (by norm_num)
      rw [(olgExH1_hasDerivAt hl2).deriv]
      exact olgExH2_pos hl2 (ne_of_lt hl)
  have h2 : StrictMonoOn olgExH1 (Ico 1 2) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico 1 2) (hc _ fun l hl => hl.2) fun l hl => ?_
    rw [interior_Ico] at hl
    rw [(olgExH1_hasDerivAt hl.2).deriv]
    exact olgExH2_pos hl.2 (ne_of_gt hl.1)
  intro x hx y hy hxy
  rcases le_or_gt y 1 with hy1 | hy1
  · exact h1 (mem_Iic.2 (hxy.le.trans hy1)) (mem_Iic.2 hy1) hxy
  rcases le_or_gt 1 x with hx1 | hx1
  · exact h2 ⟨hx1, hx⟩ ⟨hx1.trans hxy.le, hy⟩ hxy
  · exact (h1 (mem_Iic.2 hx1.le) (mem_Iic.2 le_rfl) hx1).trans
      (h2 ⟨le_rfl, by norm_num⟩ ⟨hy1.le, hy⟩ hy1)

/-- The counterexample satisfies the labour part of Assumption 17.1 with `L = 2`. -/
theorem olgExH_assumption : Assumption17_1H 2 olgExH olgExH1 olgExH2 := by
  have hcont : ContinuousOn olgExH (Ico 0 2) := fun l hl =>
    (olgExH_hasDerivAt hl.2).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn olgExH (Ico 0 2) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico 0 2) hcont fun l hl => ?_
    rw [interior_Ico] at hl
    rw [(olgExH_hasDerivAt hl.2).deriv]
    exact olgExH1_pos hl.1 hl.2
  refine ⟨by norm_num, fun l hl => ?_, fun l hl => (olgExH_hasDerivAt hl.2).hasDerivWithinAt,
    fun l hl => (olgExH1_hasDerivAt hl.2).hasDerivWithinAt, ?_, hmono, ?_, by norm_num [olgExH1],
    olgExH1_tendsto⟩
  · have h0 : 0 < olgExH 0 := by
      simp only [olgExH]
      have := Real.log_two_lt_d9
      norm_num
      linarith
    exact h0.le.trans (hmono.monotoneOn (left_mem_Ico.2 (by norm_num)) hl hl.1)
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun l hl => ?_
    have : (2 : ℝ) - l ≠ 0 := by linarith [hl.2]
    exact pow_ne_zero 2 this
  · refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ico 0 2) hcont ?_
    rw [interior_Ico]
    intro x hx y hy hxy
    rw [(olgExH_hasDerivAt hx.2).deriv, (olgExH_hasDerivAt hy.2).deriv]
    exact olgExH1_strictMonoOn hx.2 hy.2 hxy

/-- **Correction (Proposition 1, (6)).** The book says the elasticity
`l ζ'(l)/ζ(l) = (H'(l) + l H''(l))/H'(l)` is `≥ 1` "with equality only at `l = 0`". This is
false: strict convexity allows `H''(l₀) = 0` at `l₀ > 0`. For `olgExH` (Assumption 17.1 with
`L = 2`) the elasticity equals `1` at `l = 1`. -/
theorem proposition_1_elasticity_counterexample :
    ¬ ∀ (L : ℝ) (H H' H'' : ℝ → ℝ), Assumption17_1H L H H' H'' →
      ∀ l ∈ Ioo 0 L, 1 < l * (H' l + l * H'' l) / olgZeta H' l := fun h => by
  have := h 2 olgExH olgExH1 olgExH2 olgExH_assumption 1 ⟨by norm_num, by norm_num⟩
  norm_num [olgExH1, olgExH2, olgZeta] at this

/-- **Equation (6), corrected.** For `l ∈ (0, L)` the elasticity of `ζ` is at least one. -/
theorem zeta_elasticity_ge_one (hH : Assumption17_1H L H H' H'') {l : ℝ} (hl : l ∈ Ioo 0 L) :
    1 ≤ l * (H' l + l * H'' l) / olgZeta H' l := by
  have hz : 0 < olgZeta H' l := mul_pos hl.1 (hH.H'_pos hl)
  rw [le_div_iff₀ hz, one_mul, olgZeta]
  have := mul_nonneg (mul_nonneg hl.1.le hl.1.le) (hH.H''_nonneg hl)
  nlinarith

/-! ### The inverse of `ζ` (p. 507) -/

/-- `ζ⁻¹ : ℝ₊ → [0, L)`, the inverse of `ζ(l) = l H'(l)` on `[0, L)` (p. 507). -/
noncomputable def olgZetaInv (L : ℝ) (H' : ℝ → ℝ) (y : ℝ) : ℝ :=
  Function.invFunOn (olgZeta H') (Ico 0 L) y

namespace Assumption17_1H

variable (hH : Assumption17_1H L H H' H'')
include hH

/-- `ζ` is strictly increasing on `[0, L)`. -/
theorem zeta_strictMonoOn : StrictMonoOn (olgZeta H') (Ico 0 L) := by
  intro x hx y hy hxy
  have hy0 : 0 < y := hx.1.trans_lt hxy
  have h1 : H' x < H' y := hH.H'_strictMonoOn hx hy hxy
  have h2 : 0 < H' y := hH.H'_pos ⟨hy0, hy.2⟩
  simp only [olgZeta]
  nlinarith [hx.1]

/-- `ζ` is continuous on `[0, L)`. -/
theorem zeta_continuousOn : ContinuousOn (olgZeta H') (Ico 0 L) :=
  continuousOn_id.mul hH.H'_continuousOn

/-- `ζ(l) ≥ 0` on `[0, L)`, with equality only at `0`. -/
theorem zeta_pos {l : ℝ} (hl : l ∈ Ioo 0 L) : 0 < olgZeta H' l :=
  mul_pos hl.1 (hH.H'_pos hl)

/-- `ζ` maps `[0, L)` onto `ℝ₊`. -/
theorem zeta_surj {y : ℝ} (hy : 0 ≤ y) : ∃ l ∈ Ico 0 L, olgZeta H' l = y := by
  have hL := hH.L_pos
  have h1 : ∀ᶠ l in 𝓝[<] L, 2 * y / L < H' l :=
    hH.H'_tendsto.eventually (eventually_gt_atTop _)
  have h2 : ∀ᶠ l in 𝓝[<] L, l ∈ Ioo (L / 2) L := Ioo_mem_nhdsLT (by linarith)
  obtain ⟨l₁, hl₁, hl₁'⟩ := (h1.and h2).exists
  have hz : y ≤ olgZeta H' l₁ := by
    simp only [olgZeta]
    have : 2 * y / L * (L / 2) = y := by field_simp
    have h3 : 0 ≤ 2 * y / L := by positivity
    nlinarith [hl₁'.1]
  have hsub : Icc 0 l₁ ⊆ Ico 0 L := fun z hz => ⟨hz.1, hz.2.trans_lt hl₁'.2⟩
  obtain ⟨l, hl, hly⟩ := intermediate_value_Icc (by linarith [hl₁'.1] : (0 : ℝ) ≤ l₁)
    (hH.zeta_continuousOn.mono hsub) ⟨by simp [olgZeta, hy], hz⟩
  exact ⟨l, hsub hl, hly⟩

/-- `ζ⁻¹(y) ∈ [0, L)` for `y ≥ 0`. -/
theorem zetaInv_mem {y : ℝ} (hy : 0 ≤ y) : olgZetaInv L H' y ∈ Ico 0 L :=
  Function.invFunOn_mem (hH.zeta_surj hy)

/-- `ζ(ζ⁻¹(y)) = y` for `y ≥ 0`. -/
theorem zeta_zetaInv {y : ℝ} (hy : 0 ≤ y) : olgZeta H' (olgZetaInv L H' y) = y :=
  Function.invFunOn_eq (hH.zeta_surj hy)

/-- `ζ⁻¹(ζ(l)) = l` for `l ∈ [0, L)`. -/
theorem zetaInv_zeta {l : ℝ} (hl : l ∈ Ico 0 L) : olgZetaInv L H' (olgZeta H' l) = l := by
  have h0 : 0 ≤ olgZeta H' l := mul_nonneg hl.1 (hH.H'_nonneg hl)
  exact hH.zeta_strictMonoOn.injOn (hH.zetaInv_mem h0) hl (hH.zeta_zetaInv h0)

/-- `ζ⁻¹(0) = 0`. -/
theorem zetaInv_zero : olgZetaInv L H' 0 = 0 := by
  have := hH.zetaInv_zeta (left_mem_Ico.2 hH.L_pos)
  simpa [olgZeta] using this

/-- `ζ⁻¹` is strictly increasing on `ℝ₊`. -/
theorem zetaInv_strictMonoOn : StrictMonoOn (olgZetaInv L H') (Ici 0) := by
  intro x hx y hy hxy
  by_contra h
  have h' := hH.zeta_strictMonoOn.monotoneOn (hH.zetaInv_mem hy) (hH.zetaInv_mem hx)
    (not_lt.1 h)
  rw [hH.zeta_zetaInv hx, hH.zeta_zetaInv hy] at h'
  linarith

/-- `ζ⁻¹(y) > 0` for `y > 0`. -/
theorem zetaInv_pos {y : ℝ} (hy : 0 < y) : 0 < olgZetaInv L H' y := by
  have := hH.zetaInv_strictMonoOn (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le) hy
  rwa [hH.zetaInv_zero] at this

/-- `ζ⁻¹` maps `ℝ₊` onto `[0, L)`. -/
theorem zetaInv_image_Ici : olgZetaInv L H' '' Ici 0 = Ico 0 L := by
  refine Subset.antisymm (image_subset_iff.2 fun y hy => hH.zetaInv_mem hy) fun l hl => ?_
  exact ⟨olgZeta H' l, mul_nonneg hl.1 (hH.H'_nonneg hl), hH.zetaInv_zeta hl⟩

/-- `ζ⁻¹` maps `(0, ∞)` onto `(0, L)`. -/
theorem zetaInv_image_Ioi : olgZetaInv L H' '' Ioi 0 = Ioo 0 L := by
  refine Subset.antisymm (image_subset_iff.2 fun y hy =>
    ⟨hH.zetaInv_pos hy, (hH.zetaInv_mem (le_of_lt hy)).2⟩) fun l hl => ?_
  exact ⟨olgZeta H' l, hH.zeta_pos hl, hH.zetaInv_zeta (Ioo_subset_Ico_self hl)⟩

/-- `ζ⁻¹` is continuous on `ℝ₊` (p. 507). -/
theorem zetaInv_continuousOn : ContinuousOn (olgZetaInv L H') (Ici 0) := by
  intro y hy
  rcases (mem_Ici.1 hy).eq_or_lt with h | h
  · rw [← h]
    refine continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin
      hH.zetaInv_strictMonoOn.monotoneOn self_mem_nhdsWithin ?_
    rw [hH.zetaInv_image_Ici, hH.zetaInv_zero]
    exact Ico_mem_nhdsGE hH.L_pos
  · refine (continuousAt_of_monotoneOn_of_image_mem_nhds
      (hH.zetaInv_strictMonoOn.monotoneOn.mono Ioi_subset_Ici_self) (Ioi_mem_nhds h)
      ?_).continuousWithinAt
    rw [hH.zetaInv_image_Ioi]
    exact Ioo_mem_nhds (hH.zetaInv_pos h) (hH.zetaInv_mem h.le).2

/-- `ζ'(l) = H'(l) + l H''(l)` on `(0, L)`. -/
theorem zeta_hasDerivAt {l : ℝ} (hl : l ∈ Ioo 0 L) :
    HasDerivAt (olgZeta H') (H' l + l * H'' l) l := by
  have h := (hasDerivAt_id' l).mul (hH.H'_hasDerivAt hl)
  exact h.congr_deriv (by ring)

/-- `ζ'(l) > 0` on `(0, L)`. -/
theorem zeta_deriv_pos {l : ℝ} (hl : l ∈ Ioo 0 L) : 0 < H' l + l * H'' l :=
  add_pos_of_pos_of_nonneg (hH.H'_pos hl) (mul_nonneg hl.1.le (hH.H''_nonneg hl))

/-- `ζ⁻¹` is differentiable at `y > 0`, with `(ζ⁻¹)'(y) = 1/ζ'(ζ⁻¹(y))`. -/
theorem zetaInv_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (olgZetaInv L H')
      (H' (olgZetaInv L H' y) + olgZetaInv L H' y * H'' (olgZetaInv L H' y))⁻¹ y := by
  have hl : olgZetaInv L H' y ∈ Ioo 0 L := ⟨hH.zetaInv_pos hy, (hH.zetaInv_mem hy.le).2⟩
  refine HasDerivAt.of_local_left_inverse
    ((hH.zetaInv_continuousOn y (mem_Ici.2 hy.le)).continuousAt (Ici_mem_nhds hy))
    (hH.zeta_hasDerivAt hl) (hH.zeta_deriv_pos hl).ne' ?_
  filter_upwards [Ioi_mem_nhds hy] with z hz
  exact hH.zeta_zetaInv (le_of_lt hz)

end Assumption17_1H

/-! ### The change of variable `f = ζ ∘ n` (p. 507) -/

/-- **(8) ⇔ (4)** (p. 507). For `n : X → [0, L)`, `n` satisfies (4) iff `f = ζ ∘ n` satisfies
(8), `f(x) = ∫ φ[x' ζ⁻¹(f(x'))] π(x, dx')`; i.e. iff `f` is a fixed point of the operator (9). -/
theorem eq8_iff_eq4 (hH : Assumption17_1H L H H' H'') {a b : ℝ} (κ : Kernel (Icc a b) (Icc a b))
    (n : Icc a b → ℝ) (hn : ∀ x, n x ∈ Ico 0 L) :
    (∀ x, olgZeta H' (n x) = ∫ x', olgPhi V' (x'.1 * n x') ∂κ x) ↔
      ∀ x, olgZeta H' (n x) =
        ∫ x', olgPhi V' (x'.1 * olgZetaInv L H' (olgZeta H' (n x'))) ∂κ x := by
  have h : ∀ x', olgZetaInv L H' (olgZeta H' (n x')) = n x' := fun x' => hH.zetaInv_zeta (hn x')
  simp only [h]

end StokeyLucasPrescott.FixedPointArguments
