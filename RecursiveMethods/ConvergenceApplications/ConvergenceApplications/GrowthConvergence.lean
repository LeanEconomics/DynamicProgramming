/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.RealIntervals
import ConvergenceApplications.GrowthOutput

/-!
# The one-sector model of optimal growth: convergence of the output process

SLP §13.3, pp. 393–395. Output follows `x_{t+1} = f(g(x_t)) z_{t+1}` on `X = [0, x̄]`, with
i.i.d. shocks `z ~ μ` on `Z = [1, z̄]`.

* **The transition function** (p. 393, Theorem 8.9): `GrowthLaw` (`f` continuous and
  nondecreasing with `f(0) ≥ 0`, `z̄ f(x̄) ≤ x̄`, a measurable policy `0 ≤ g(x) ≤ x`),
  `growthNext`, `growthP` with `P(x, A) = μ{z : f(g(x)) z ∈ A}` (`growthP_apply`); `P` is a
  Markov kernel (`isMarkovKernel_growthP`), `(TF)(x) = ∫ F(f(g(x)) z) μ(dz)`
  (`markovOpR_growthP`), Feller if `g` is continuous (`growthP_isFeller`), so that it has an
  invariant measure (`growth_exists_invariant`, Theorem 12.10), and
  **Exercise 13.3d** (`ex_13_3d`): monotone if `g` is nondecreasing.
* **The paths `φₙ(x, z)`** (p. 393): `growthPhi`; `n ↦ φₙ` is monotone when `φ₀ ≤ φ₁` or
  `φ₁ ≤ φ₀` (`GrowthLaw.phi_monotone`, `GrowthLaw.phi_antitone`), `z ↦ φₙ(x, z)` is continuous
  (`GrowthLaw.continuousOn_phi`), and limits are fixed points (`GrowthLaw.phi_limit`).
* **(3a), (3b)** (p. 393): `kpow_succ_ge_pow` (a lower bound for `Pⁿ⁺¹` along a chain of sets),
  `growth_kpow_Ioc` and `growth_kpow_Ioc_real` (`Pⁿ(x, (φₙ(x, a), φₙ(x, b)]) ≥ αⁿ(b − a)ⁿ`
  under (Z3), `ShockZ3`), `growth_3a`, `growth_3b`. As the NOTE says, the argument needs the
  `n`-step map to be monotone in each shock separately (strictly in the last); it holds with
  `g` only nondecreasing, because `f(g(·)) ≥ f(0) > 0`.
* **The Euler argument** (p. 394): `zstar` (`z* = ∫ z dμ ≥ 1`), `GrowthEuler` (the Euler
  equation as a hypothesis on `g`, with the Kuhn–Tucker inequality at a corner `g(x) = 0`, and
  `c(x) > 0` for `x > 0`); `growth_xi` (`φₙ(0, z̄) ↑ ξ = f(g(ξ)) z̄`), `growth_euler_xi`
  (`βf′(g(ξ)) z* < 1`, also at a corner), `growth_xstar_exists`, `growth_xstar_between`
  (`ϑ < x* < ξ` for every `x*`), `growth_bottom_delta`, `growth_case_zero`
  (`Pᴺ(0, (x*, x̄]) ≥ αᴺδᴺ`); `growth_theta` (`φₙ(x̄, 1) ↓ ϑ = f(g(ϑ))`), `growth_euler_theta`,
  `growth_top_delta` and **Exercise 13.3e** (`ex_13_3e`: `Pᴺ(x̄, (0, x*]) ≥ αᴺδᴺ`).
* **Theorem 12.12 applied** (`growth_invariant_unique`): a unique invariant probability measure
  `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every `λ₀`. For the optimal policy of Ex. 13.3b
  (`outPolicyR`, `outPolicyR_growthLaw`): `growth_optimal_invariant_unique`, with the
  monotonicity of consumption supplied by `out_consumption_strictMono`.
* **The role of `f(0) > 0`** (pp. 394–395): if `f(0) = 0`, `δ₀` is invariant, `Pⁿ(0, ·) = δ₀`
  and `Pⁿ(0, [c, x̄]) = 0` for all `c > 0` (`growth_f_zero`), so uniqueness fails as soon as
  another invariant measure exists (`growth_f_zero_not_unique`); if `f(g(ε)) ≥ ε`, the interval
  `[ε, x̄]` is invariant (`growth_invariant_interval`).

**Corrections and gaps filled.**
* `x*` (p. 393): "the unique value with `βf′(g(x*)) z* = 1`" is not justified, since `f` is only
  weakly concave; and its existence is not argued. Existence follows from the intermediate value
  theorem (`growth_xstar_exists`), and every such `x*` satisfies `ϑ < x* < ξ`
  (`growth_xstar_between`), which is all the argument needs.
* The strict inequality in the chain at `ξ` needs `μ{z < z̄} > 0` (and at `ϑ`, `μ{z > 1} > 0`);
  (Z3) gives both (`ShockZ3.pos`).
* The Euler equation (2) holds with equality only at interior choices; at a corner `g(ξ) = 0`
  the inequality `U′(c) ≥ RHS` still gives `βf′(g(ξ)) z* < 1`, and at a corner `g(ϑ) = 0` one
  has `ϑ < x*` because `g(x*) > 0` (the NOTE's repair, formalised).
* `g` need only be nondecreasing, not strictly increasing (which fails: `ex_13_3b_counterexample`),
  and `f` need only be nondecreasing for the transition function and (3a)/(3b).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {f g : ℝ → ℝ} {xbar zbar : ℝ}

/-- The law of motion `x′ = f(g(x)) z′` on `X = [0, x̄]` with shocks `z′ ∈ Z = [1, z̄]`
(SLP p. 393): `f` continuous and nondecreasing on `[0, ∞)` with `f(0) ≥ 0`, `z̄ f(x̄) ≤ x̄`
(the book takes `x̄ = z̄ f(x̄)`), and a measurable policy `g` with `0 ≤ g(x) ≤ x`. -/
structure GrowthLaw (f g : ℝ → ℝ) (xbar zbar : ℝ) : Prop where
  zbar_gt : 1 < zbar
  xbar_pos : 0 < xbar
  f_cont : ContinuousOn f (Ici 0)
  f_mono : MonotoneOn f (Ici 0)
  f_zero : 0 ≤ f 0
  xbar_maintain : zbar * f xbar ≤ xbar
  g_nonneg : ∀ x ∈ Icc 0 xbar, 0 ≤ g x
  g_le : ∀ x ∈ Icc 0 xbar, g x ≤ x
  g_meas : Measurable g

theorem mem_Z {z : ℝ} (hz : z ∈ Icc 1 zbar) : z ∈ Icc 0 zbar := ⟨by linarith [hz.1], hz.2⟩

namespace GrowthLaw

variable (h : GrowthLaw f g xbar zbar)
include h

theorem g_mem {x : ℝ} (hx : x ∈ Icc 0 xbar) : g x ∈ Ici (0 : ℝ) := h.g_nonneg x hx

theorem fg_nonneg {x : ℝ} (hx : x ∈ Icc 0 xbar) : 0 ≤ f (g x) :=
  h.f_zero.trans (h.f_mono (mem_Ici.2 le_rfl) (h.g_mem hx) (h.g_nonneg x hx))

theorem fg_le_f {x : ℝ} (hx : x ∈ Icc 0 xbar) : f (g x) ≤ f xbar :=
  h.f_mono (h.g_mem hx) (mem_Ici.2 h.xbar_pos.le) ((h.g_le x hx).trans hx.2)

theorem f0_le_fg {x : ℝ} (hx : x ∈ Icc 0 xbar) : f 0 ≤ f (g x) :=
  h.f_mono (mem_Ici.2 le_rfl) (h.g_mem hx) (h.g_nonneg x hx)

/-- `f(g(x)) z ∈ [0, x̄]` for `x ∈ [0, x̄]` and `z ∈ [0, z̄]`: `f(g(x)) z ≤ z̄ f(x̄) ≤ x̄`. -/
theorem mem {x z : ℝ} (hx : x ∈ Icc 0 xbar) (hz : z ∈ Icc 0 zbar) :
    f (g x) * z ∈ Icc 0 xbar := by
  refine ⟨mul_nonneg (h.fg_nonneg hx) hz.1, ?_⟩
  calc f (g x) * z ≤ f xbar * zbar :=
        mul_le_mul (h.fg_le_f hx) hz.2 hz.1 ((h.fg_nonneg hx).trans (h.fg_le_f hx))
    _ = zbar * f xbar := mul_comm _ _
    _ ≤ xbar := h.xbar_maintain

theorem measurable_fg : Measurable fun x : Icc (0 : ℝ) xbar => f (g x.1) := by
  have hk : Measurable fun x : Icc (0 : ℝ) xbar => (⟨g x.1, h.g_mem x.2⟩ : Ici (0 : ℝ)) :=
    (h.g_meas.comp measurable_subtype_coe).subtype_mk
  exact h.f_cont.domRestrict.measurable.comp hk

theorem continuous_fg (hgc : ContinuousOn g (Icc 0 xbar)) :
    Continuous fun x : Icc (0 : ℝ) xbar => f (g x.1) :=
  h.f_cont.comp_continuous (hgc.comp_continuous continuous_subtype_val fun x => x.2)
    fun x => h.g_mem x.2

theorem continuousOn_fg (hgc : ContinuousOn g (Icc 0 xbar)) :
    ContinuousOn (fun x => f (g x)) (Icc 0 xbar) :=
  h.f_cont.comp hgc fun _ hx => h.g_mem hx

end GrowthLaw

/-- The law of motion `(x, z′) ↦ f(g(x)) z′` as a map `X × Z → X`. -/
def growthNext (h : GrowthLaw f g xbar zbar) (p : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) :
    Icc (0 : ℝ) xbar :=
  ⟨f (g p.1.1) * p.2.1, h.mem p.1.2 (mem_Z p.2.2)⟩

theorem measurable_growthNext (h : GrowthLaw f g xbar zbar) : Measurable (growthNext h) :=
  ((h.measurable_fg.comp measurable_fst).mul
    (measurable_subtype_coe.comp measurable_snd)).subtype_mk

theorem measurable_growthNext_x (h : GrowthLaw f g xbar zbar) (x : Icc (0 : ℝ) xbar) :
    Measurable fun z => growthNext h (x, z) :=
  (measurable_growthNext h).comp measurable_prodMk_left

theorem continuous_growthNext (h : GrowthLaw f g xbar zbar) (hgc : ContinuousOn g (Icc 0 xbar)) :
    Continuous (growthNext h) :=
  ((h.continuous_fg hgc).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _

/-- The transition function of output (SLP p. 393, Theorem 8.9):
`P(x, A) = μ{z′ ∈ Z : f(g(x)) z′ ∈ A}`. -/
noncomputable def growthP (h : GrowthLaw f g xbar zbar) (μ : Measure (Icc (1 : ℝ) zbar))
    [IsProbabilityMeasure μ] : Kernel (Icc (0 : ℝ) xbar) (Icc (0 : ℝ) xbar) where
  toFun x := μ.map fun z => growthNext h (x, z)
  measurable' := Measure.measurable_of_measurable_coe _ fun A hA => by
    have : ∀ x, (μ.map fun z => growthNext h (x, z)) A =
        μ (Prod.mk x ⁻¹' (growthNext h ⁻¹' A)) := fun x =>
      Measure.map_apply (measurable_growthNext_x h x) hA
    simp_rw [this]
    exact measurable_measure_prodMk_left (measurable_growthNext h hA)

variable (h : GrowthLaw f g xbar zbar) (μ : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure μ]

theorem growthP_eq (x : Icc (0 : ℝ) xbar) :
    growthP h μ x = μ.map fun z => growthNext h (x, z) := rfl

/-- `P(x, A) = μ{z′ : f(g(x)) z′ ∈ A}`. -/
theorem growthP_apply (x : Icc (0 : ℝ) xbar) {A : Set (Icc (0 : ℝ) xbar)} (hA : MeasurableSet A) :
    growthP h μ x A = μ {z | growthNext h (x, z) ∈ A} :=
  Measure.map_apply (measurable_growthNext_x h x) hA

/-- `P` is a transition function (Theorem 8.9). -/
theorem isMarkovKernel_growthP : IsMarkovKernel (growthP h μ) :=
  ⟨fun x => by rw [growthP_eq]; infer_instance⟩

/-- `(TF)(x) = ∫ F(f(g(x)) z′) μ(dz′)`. -/
theorem markovOpR_growthP {F : Icc (0 : ℝ) xbar → ℝ} (hF : Measurable F) (x : Icc (0 : ℝ) xbar) :
    markovOpR (growthP h μ) F x = ∫ z, F (growthNext h (x, z)) ∂μ := by
  rw [markovOpR, growthP_eq, integral_map
    (measurable_growthNext_x h x).aemeasurable
    hF.aestronglyMeasurable]

/-- **Exercise 13.3d.** If `g` is nondecreasing, `P` is monotone: for nondecreasing bounded `F`,
`∫ F(f(g(x)) z′) μ(dz′)` is nondecreasing in `x` (the manual's argument). -/
theorem ex_13_3d (hgm : MonotoneOn g (Icc 0 xbar)) : IsMonotoneTF (growthP h μ) := by
  intro F hF ⟨M, hM⟩ hmono x x' hxx'
  rw [markovOpR_growthP h μ hF, markovOpR_growthP h μ hF]
  refine integral_mono (integrable_of_bounded (hF.comp
      (measurable_growthNext_x h x)) fun _ => hM _)
    (integrable_of_bounded (hF.comp
      (measurable_growthNext_x h x')) fun _ => hM _) fun z => hmono ?_
  change f (g x.1) * z.1 ≤ f (g x'.1) * z.1
  exact mul_le_mul_of_nonneg_right (h.f_mono (h.g_mem x.2) (h.g_mem x'.2) (hgm x.2 x'.2 hxx'))
    (by linarith [z.2.1])

/-- If `g` is continuous, `P` has the Feller property (SLP p. 393, Exercise 8.10). -/
theorem growthP_isFeller (hgc : ContinuousOn g (Icc 0 xbar)) : IsFeller (growthP h μ) := by
  intro F hF ⟨M, hM⟩
  have heq : markovOpR (growthP h μ) F = fun x => ∫ z, F (growthNext h (x, z)) ∂μ :=
    funext (markovOpR_growthP h μ hF.measurable)
  rw [heq]
  have hc := hF.comp (continuous_growthNext h hgc)
  exact continuous_of_dominated (bound := fun _ => M)
    (fun x => (hc.comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun _ => by rw [Real.norm_eq_abs]; exact hM _)
    (integrable_const _) (Eventually.of_forall fun z => hc.comp (Continuous.prodMk_left z))

/-- With `g` continuous, `P` has at least one invariant probability measure (SLP p. 393,
Theorem 12.10: `X` is compact and `P` is Feller). -/
theorem growth_exists_invariant (hgc : ContinuousOn g (Icc 0 xbar)) :
    ∃ lam : Measure (Icc (0 : ℝ) xbar), IsProbabilityMeasure lam ∧
      adjointOp (growthP h μ) lam = lam := by
  have := isMarkovKernel_growthP h μ
  have : Nonempty (Icc (0 : ℝ) xbar) := ⟨⟨0, le_rfl, h.xbar_pos.le⟩⟩
  exact theorem_12_10 (κ := growthP h μ) (growthP_isFeller h μ hgc)

/-! ### The paths `φₙ(x, z)` under a constant shock -/

/-- Output at the start of period `n` from output `x` if the shock is constant at `z` and `g` is
followed (SLP p. 393): `φ₀(x, z) = x`, `φₙ₊₁(x, z) = f(g(φₙ(x, z))) z`. -/
noncomputable def growthPhi (f g : ℝ → ℝ) (x z : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => f (g (growthPhi f g x z n)) * z

theorem growthPhi_zero (x z : ℝ) : growthPhi f g x z 0 = x := rfl

theorem growthPhi_succ (x z : ℝ) (n : ℕ) :
    growthPhi f g x z (n + 1) = f (g (growthPhi f g x z n)) * z := rfl

namespace GrowthLaw

include h

theorem fg_mono (hgm : MonotoneOn g (Icc 0 xbar)) : MonotoneOn (fun x => f (g x)) (Icc 0 xbar) :=
  fun _ hx _ hy hxy => h.f_mono (h.g_mem hx) (h.g_mem hy) (hgm hx hy hxy)

theorem phi_mem {x z : ℝ} (hx : x ∈ Icc 0 xbar) (hz : z ∈ Icc 0 zbar) (n : ℕ) :
    growthPhi f g x z n ∈ Icc 0 xbar := by
  induction n with
  | zero => exact hx
  | succ n ih => exact h.mem ih hz

/-- If `φ₀ ≤ φ₁`, the path `n ↦ φₙ(x, z)` is nondecreasing. -/
theorem phi_monotone (hgm : MonotoneOn g (Icc 0 xbar)) {x z : ℝ} (hx : x ∈ Icc 0 xbar)
    (hz : z ∈ Icc 0 zbar) (h01 : x ≤ f (g x) * z) : Monotone (growthPhi f g x z) := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero => exact h01
  | succ n ih =>
    exact mul_le_mul_of_nonneg_right (h.fg_mono hgm (h.phi_mem hx hz n) (h.phi_mem hx hz (n + 1))
      ih) hz.1

/-- If `φ₁ ≤ φ₀`, the path `n ↦ φₙ(x, z)` is nonincreasing. -/
theorem phi_antitone (hgm : MonotoneOn g (Icc 0 xbar)) {x z : ℝ} (hx : x ∈ Icc 0 xbar)
    (hz : z ∈ Icc 0 zbar) (h01 : f (g x) * z ≤ x) : Antitone (growthPhi f g x z) := by
  refine antitone_nat_of_succ_le fun n => ?_
  induction n with
  | zero => exact h01
  | succ n ih =>
    exact mul_le_mul_of_nonneg_right (h.fg_mono hgm (h.phi_mem hx hz (n + 1)) (h.phi_mem hx hz n)
      ih) hz.1

/-- `z ↦ φₙ(x, z)` is continuous on `[0, z̄]` if `g` is continuous. -/
theorem continuousOn_phi (hgc : ContinuousOn g (Icc 0 xbar)) {x : ℝ} (hx : x ∈ Icc 0 xbar)
    (n : ℕ) : ContinuousOn (fun z => growthPhi f g x z n) (Icc 0 zbar) := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih =>
    exact ((h.continuousOn_fg hgc).comp ih fun z hz => h.phi_mem hx hz n).mul continuousOn_id

/-- A limit of `φₙ(x, z)` is a fixed point `ξ = f(g(ξ)) z` in `X`. -/
theorem phi_limit (hgc : ContinuousOn g (Icc 0 xbar)) {x z ξ : ℝ} (hx : x ∈ Icc 0 xbar)
    (hz : z ∈ Icc 0 zbar) (hlim : Tendsto (growthPhi f g x z) atTop (𝓝 ξ)) :
    ξ ∈ Icc 0 xbar ∧ ξ = f (g ξ) * z := by
  have hmem : ∀ n, growthPhi f g x z n ∈ Icc 0 xbar := h.phi_mem hx hz
  have hξ : ξ ∈ Icc 0 xbar := isClosed_Icc.mem_of_tendsto hlim (Eventually.of_forall hmem)
  have hT : Tendsto (fun n => f (g (growthPhi f g x z n)) * z) atTop (𝓝 (f (g ξ) * z)) :=
    (((h.continuousOn_fg hgc).mul continuousOn_const).continuousWithinAt hξ).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hmem⟩)
  have hS : Tendsto (fun n => growthPhi f g x z (n + 1)) atTop (𝓝 ξ) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  exact ⟨hξ, tendsto_nhds_unique hS hT⟩

end GrowthLaw

/-! ### Lower bounds on `Pⁿ` along a chain of sets -/

/-- If `P(x₀, B₀) ≥ p` and `P(y, Bₙ₊₁) ≥ p` for all `y ∈ Bₙ`, then `Pⁿ⁺¹(x₀, Bₙ) ≥ pⁿ⁺¹`. -/
theorem kpow_succ_ge_pow {S : Type*} [MeasurableSpace S] (κ : Kernel S S) {B : ℕ → Set S}
    (hB : ∀ n, MeasurableSet (B n)) {p : ℝ≥0∞} {x₀ : S} (h0 : p ≤ κ x₀ (B 0))
    (hstep : ∀ n, ∀ y ∈ B n, p ≤ κ y (B (n + 1))) (n : ℕ) :
    p ^ (n + 1) ≤ kpow κ (n + 1) x₀ (B n) := by
  induction n with
  | zero => simpa [kpow_one] using h0
  | succ n ih =>
    rw [kpow_add κ (n + 1) 1, kpow_one, Kernel.comp_apply' _ _ _ (hB (n + 1))]
    calc p ^ (n + 1 + 1) = p * p ^ (n + 1) := pow_succ' _ _
      _ ≤ p * kpow κ (n + 1) x₀ (B n) := by gcongr
      _ = ∫⁻ y, (B n).indicator (fun _ => p) y ∂(kpow κ (n + 1) x₀) :=
          (lintegral_indicator_const (hB n) p).symm
      _ ≤ ∫⁻ y, κ y (B (n + 1)) ∂(kpow κ (n + 1) x₀) := lintegral_mono fun y => by
          by_cases hy : y ∈ B n
          · rw [indicator_of_mem hy]; exact hstep n y hy
          · rw [indicator_of_notMem hy]; exact zero_le

/-- If all of the first `n + 1` shocks lie in `(a, b]`, output at `n + 1` lies in
`(φₙ₊₁(x, a), φₙ₊₁(x, b)]`: the `n`-step map is nondecreasing in every shock and, because
`f(g(·)) ≥ f(0) > 0`, strictly increasing in the last one. Hence
`Pⁿ⁺¹(x, (φₙ₊₁(x, a), φₙ₊₁(x, b)]) ≥ μ((a, b])ⁿ⁺¹`. Only `g` nondecreasing is needed. -/
theorem growth_kpow_Ioc (hgm : MonotoneOn g (Icc 0 xbar)) (hf0 : 0 < f 0) (x : Icc (0 : ℝ) xbar)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ zbar) (n : ℕ) :
    μ {z | a < z.1 ∧ z.1 ≤ b} ^ (n + 1) ≤ kpow (growthP h μ) (n + 1) x
      (Subtype.val ⁻¹' Ioc (growthPhi f g x a (n + 1)) (growthPhi f g x b (n + 1))) := by
  have haZ : a ∈ Icc 0 zbar := ⟨by linarith, by linarith⟩
  have hbZ : b ∈ Icc 0 zbar := ⟨by linarith, hb⟩
  have hpos : ∀ y ∈ Icc 0 xbar, 0 < f (g y) := fun y hy => hf0.trans_le (h.f0_le_fg hy)
  refine kpow_succ_ge_pow (growthP h μ) (B := fun n => Subtype.val ⁻¹'
    Ioc (growthPhi f g x a (n + 1)) (growthPhi f g x b (n + 1)))
    (fun n => measurable_subtype_coe measurableSet_Ioc) ?_ ?_ n
  · rw [growthP_apply h μ x (measurable_subtype_coe measurableSet_Ioc)]
    refine measure_mono fun z hz => ?_
    change f (g x.1) * a < f (g x.1) * z.1 ∧ f (g x.1) * z.1 ≤ f (g x.1) * b
    exact ⟨mul_lt_mul_of_pos_left hz.1 (hpos x x.2),
      mul_le_mul_of_nonneg_left hz.2 (hpos x x.2).le⟩
  · intro m y hy
    rw [growthP_apply h μ y (measurable_subtype_coe measurableSet_Ioc)]
    refine measure_mono fun z hz => ?_
    change f (g (growthPhi f g x a (m + 1))) * a < f (g y.1) * z.1 ∧
      f (g y.1) * z.1 ≤ f (g (growthPhi f g x b (m + 1))) * b
    have hya := h.fg_mono hgm (h.phi_mem x.2 haZ (m + 1)) y.2 hy.1.le
    have hyb := h.fg_mono hgm y.2 (h.phi_mem x.2 hbZ (m + 1)) hy.2
    constructor
    · calc f (g (growthPhi f g x a (m + 1))) * a ≤ f (g y.1) * a :=
            mul_le_mul_of_nonneg_right hya haZ.1
        _ < f (g y.1) * z.1 := mul_lt_mul_of_pos_left hz.1 (hpos y y.2)
    · calc f (g y.1) * z.1 ≤ f (g y.1) * b := mul_le_mul_of_nonneg_left hz.2 (hpos y y.2).le
        _ ≤ f (g (growthPhi f g x b (m + 1))) * b := mul_le_mul_of_nonneg_right hyb hbZ.1

/-- **Assumption (Z3)** (SLP p. 392): `μ((a, b]) ≥ α(b − a)` for all `(a, b] ⊆ Z`, `α > 0`. -/
def ShockZ3 (μ : Measure (Icc (1 : ℝ) zbar)) (α : ℝ) : Prop :=
  0 < α ∧ ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ zbar → α * (b - a) ≤ μ.real {z | a < z.1 ∧ z.1 ≤ b}

/-- Under (Z3), `Pⁿ(x, (φₙ(x, a), φₙ(x, b)]) ≥ αⁿ(b − a)ⁿ` for `n ≥ 1` and `(a, b] ⊆ Z`. -/
theorem growth_kpow_Ioc_real {α : ℝ} (hZ : ShockZ3 μ α) (hgm : MonotoneOn g (Icc 0 xbar))
    (hf0 : 0 < f 0) (x : Icc (0 : ℝ) xbar) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ zbar)
    {n : ℕ} (hn : 1 ≤ n) :
    (α * (b - a)) ^ n ≤ (kpow (growthP h μ) n x).real
      (Subtype.val ⁻¹' Ioc (growthPhi f g x a n) (growthPhi f g x b n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := isMarkovKernel_growthP h μ
  have := ex_8_4a (growthP h μ) (m + 1)
  have h0 : 0 ≤ α * (b - a) := mul_nonneg hZ.1.le (by linarith)
  have h1 : ENNReal.ofReal (α * (b - a)) ≤ μ {z | a < z.1 ∧ z.1 ≤ b} :=
    ENNReal.ofReal_le_of_le_toReal (hZ.2 a b ha hab hb)
  have h2 := growth_kpow_Ioc h μ hgm hf0 x ha hab hb m
  rw [measureReal_def, ← ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _),
    ENNReal.ofReal_pow h0]
  exact (pow_le_pow_left' h1 _).trans h2

/-- **(3a)** (SLP p. 393): `Pⁿ(x, (φₙ(x, z̄ − δ), φₙ(x, z̄)]) ≥ αⁿδⁿ` for `0 < δ ≤ z̄ − 1`,
`n ≥ 1`, `x ∈ X`. -/
theorem growth_3a {α : ℝ} (hZ : ShockZ3 μ α) (hgm : MonotoneOn g (Icc 0 xbar)) (hf0 : 0 < f 0)
    (x : Icc (0 : ℝ) xbar) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ zbar - 1) {n : ℕ} (hn : 1 ≤ n) :
    (α * δ) ^ n ≤ (kpow (growthP h μ) n x).real
      (Subtype.val ⁻¹' Ioc (growthPhi f g x (zbar - δ) n) (growthPhi f g x zbar n)) := by
  have := growth_kpow_Ioc_real h μ hZ hgm hf0 x (a := zbar - δ) (b := zbar) (by linarith)
    (by linarith) le_rfl hn
  rwa [show zbar - (zbar - δ) = δ by ring] at this

/-- **(3b)** (SLP p. 393): `Pⁿ(x, (φₙ(x, 1), φₙ(x, 1 + δ)]) ≥ αⁿδⁿ` for `0 < δ ≤ z̄ − 1`,
`n ≥ 1`, `x ∈ X`. -/
theorem growth_3b {α : ℝ} (hZ : ShockZ3 μ α) (hgm : MonotoneOn g (Icc 0 xbar)) (hf0 : 0 < f 0)
    (x : Icc (0 : ℝ) xbar) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ zbar - 1) {n : ℕ} (hn : 1 ≤ n) :
    (α * δ) ^ n ≤ (kpow (growthP h μ) n x).real
      (Subtype.val ⁻¹' Ioc (growthPhi f g x 1 n) (growthPhi f g x (1 + δ) n)) := by
  have := growth_kpow_Ioc_real h μ hZ hgm hf0 x (a := 1) (b := 1 + δ) le_rfl (by linarith)
    (by linarith) hn
  rwa [show 1 + δ - 1 = δ by ring] at this

/-! ### The Euler equation and the critical output `x*` -/

/-- The mean shock `z* = ∫ z μ(dz)` (SLP p. 393). -/
noncomputable def zstar (μ : Measure (Icc (1 : ℝ) zbar)) : ℝ := ∫ z, z.1 ∂μ

omit [IsProbabilityMeasure μ] in
theorem integrable_of_continuous_Z [IsFiniteMeasure μ] {F : Icc (1 : ℝ) zbar → ℝ}
    (hF : Continuous F) : Integrable F μ :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem one_le_zstar : 1 ≤ zstar μ := by
  have := integral_mono (integrable_const (1 : ℝ) (μ := μ))
    (integrable_of_continuous_Z μ continuous_subtype_val) fun z => z.2.1
  simpa [zstar] using this

omit [IsProbabilityMeasure μ] in
/-- `∫ F < ∫ G` if `F ≤ G` everywhere and `F < G` on a set of positive measure. -/
theorem integral_lt_of_lt_on [IsFiniteMeasure μ] {F G : Icc (1 : ℝ) zbar → ℝ}
    (hF : Continuous F) (hG : Continuous G) (hle : ∀ z, F z ≤ G z) {S : Set (Icc (1 : ℝ) zbar)}
    (hS : 0 < μ S) (hlt : ∀ z ∈ S, F z < G z) : ∫ z, F z ∂μ < ∫ z, G z ∂μ := by
  have hi : Integrable (fun z => G z - F z) μ := integrable_of_continuous_Z μ (hG.sub hF)
  have hpos : 0 < ∫ z, (G z - F z) ∂μ := by
    refine (integral_pos_iff_support_of_nonneg (fun z => sub_nonneg.2 (hle z)) hi).2
      (hS.trans_le (measure_mono fun z hz => ?_))
    exact (sub_pos.2 (hlt z hz)).ne'
  rw [integral_sub (integrable_of_continuous_Z μ hG) (integrable_of_continuous_Z μ hF)] at hpos
  linarith

omit [IsProbabilityMeasure μ] in
/-- (Z3) gives `μ((a, b]) > 0` for `1 ≤ a < b ≤ z̄`. -/
theorem ShockZ3.pos {α : ℝ} (hZ : ShockZ3 μ α) {a b : ℝ} (ha : 1 ≤ a) (hab : a < b)
    (hb : b ≤ zbar) {S : Set (Icc (1 : ℝ) zbar)} (hS : {z | a < z.1 ∧ z.1 ≤ b} ⊆ S) :
    0 < μ S := by
  have h1 := hZ.2 a b ha hab.le hb
  have h2 : 0 < α * (b - a) := mul_pos hZ.1 (by linarith)
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have : μ {z | a < z.1 ∧ z.1 ≤ b} = 0 := measure_mono_null hS h0
  rw [measureReal_def, this, ENNReal.toReal_zero] at h1
  linarith

/-- The Euler-equation hypotheses on the policy `g` (SLP (2), p. 392, with the corner caveat of
the NOTE on Ex. 13.3b). `dU` stands for `U′` and `df` for `f′`; consumption is
`c(x) = x − g(x)`.
* `U′ > 0` is strictly decreasing and continuous on `(0, ∞)` (`U` strictly concave, `C¹`);
* `f′` is nonincreasing and continuous on `[0, ∞)` (`f` concave, `C¹`), and `βf′(0) > 1`;
* `c(x) > 0` for `x > 0` (e.g. an Inada condition) and `c` is strictly increasing;
* the Euler inequality `U′(c(x)) ≥ β ∫ U′(c(f(g(x)) z)) f′(g(x)) z μ(dz)` for all `x > 0`, with
  equality when `g(x) > 0` (Kuhn–Tucker: at the corner `g(x) = 0` only `≥` holds). -/
structure GrowthEuler (f g df dU : ℝ → ℝ) (β xbar zbar : ℝ) (μ : Measure (Icc 1 zbar)) : Prop where
  β_pos : 0 < β
  βdf : 1 < β * df 0
  dU_pos : ∀ c, 0 < c → 0 < dU c
  dU_anti : StrictAntiOn dU (Ioi 0)
  dU_cont : ContinuousOn dU (Ioi 0)
  df_anti : AntitoneOn df (Ici 0)
  df_cont : ContinuousOn df (Ici 0)
  c_pos : ∀ x ∈ Ioc 0 xbar, 0 < x - g x
  c_mono : StrictMonoOn (fun x => x - g x) (Icc 0 xbar)
  euler_ge : ∀ x ∈ Ioc 0 xbar,
    β * ∫ z, dU (f (g x) * z.1 - g (f (g x) * z.1)) * df (g x) * z.1 ∂μ ≤ dU (x - g x)
  euler_eq : ∀ x ∈ Ioc 0 xbar, 0 < g x →
    dU (x - g x) = β * ∫ z, dU (f (g x) * z.1 - g (f (g x) * z.1)) * df (g x) * z.1 ∂μ

variable {df dU : ℝ → ℝ} {β : ℝ}

omit [IsProbabilityMeasure μ] in
theorem euler_integral_eq (x : ℝ) :
    ∫ z, dU (f (g x) * z.1 - g (f (g x) * z.1)) * df (g x) * z.1 ∂μ =
      df (g x) * ∫ z, dU (f (g x) * z.1 - g (f (g x) * z.1)) * z.1 ∂μ := by
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

omit [IsProbabilityMeasure μ] in
/-- The Euler integrand `z ↦ U′(c(k z)) z` is continuous for `0 < k`, `k z̄ ≤ x̄`. -/
theorem continuous_euler_integrand (hE : GrowthEuler f g df dU β xbar zbar μ)
    (hgc : ContinuousOn g (Icc 0 xbar)) {k : ℝ} (hk : 0 < k) (hkz : ∀ z : Icc (1 : ℝ) zbar,
      k * z.1 ≤ xbar) :
    Continuous fun z : Icc (1 : ℝ) zbar => dU (k * z.1 - g (k * z.1)) * z.1 := by
  have hkpos : ∀ z : Icc (1 : ℝ) zbar, 0 < k * z.1 := fun z => mul_pos hk (by linarith [z.2.1])
  refine (hE.dU_cont.comp_continuous ((continuousOn_id.sub hgc).comp_continuous
    (continuous_const.mul continuous_subtype_val) fun z => ⟨(hkpos z).le, hkz z⟩)
    fun z => hE.c_pos _ ⟨hkpos z, hkz z⟩).mul continuous_subtype_val

include h in
/-- **The case `x = 0`** (SLP p. 394). At a fixed point `ξ = f(g(ξ)) z̄`, the Euler inequality
gives `U′(c(ξ)) ≥ βf′(g(ξ)) ∫ U′(c(ξ z/z̄)) z μ(dz) > βf′(g(ξ)) U′(c(ξ)) z*`, so
`βf′(g(ξ)) z* < 1`. The strict step needs `μ{z < z̄} > 0`, which (Z3) gives. It holds also at a
corner `g(ξ) = 0`, since the corner Euler inequality points the right way. -/
theorem growth_euler_xi {α : ℝ} (hZ : ShockZ3 μ α) (hgc : ContinuousOn g (Icc 0 xbar))
    (hf0 : 0 < f 0) (hE : GrowthEuler f g df dU β xbar zbar μ) {ξ : ℝ} (hξ : ξ ∈ Icc 0 xbar)
    (hfix : ξ = f (g ξ) * zbar) : β * df (g ξ) * zstar μ < 1 := by
  have hk : 0 < f (g ξ) := hf0.trans_le (h.f0_le_fg hξ)
  have hξpos : 0 < ξ := by rw [hfix]; exact mul_pos hk (by linarith [h.zbar_gt])
  have hξ' : ξ ∈ Ioc 0 xbar := ⟨hξpos, hξ.2⟩
  have hz1 := one_le_zstar μ
  by_cases hd : df (g ξ) ≤ 0
  · have : β * df (g ξ) * zstar μ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hE.β_pos.le hd)
        (by linarith)
    linarith
  replace hd := not_le.1 hd
  have hkz : ∀ z : Icc (1 : ℝ) zbar, f (g ξ) * z.1 ≤ ξ := fun z => by
    rw [hfix] at *
    nlinarith [z.2.2]
  have hkzx : ∀ z : Icc (1 : ℝ) zbar, f (g ξ) * z.1 ≤ xbar := fun z => (hkz z).trans hξ.2
  have hkzpos : ∀ z : Icc (1 : ℝ) zbar, 0 < f (g ξ) * z.1 := fun z =>
    mul_pos hk (by linarith [z.2.1])
  have hcξ := hE.c_pos ξ hξ'
  have hG := continuous_euler_integrand μ hE hgc hk hkzx
  have hF : Continuous fun z : Icc (1 : ℝ) zbar => dU (ξ - g ξ) * z.1 :=
    continuous_const.mul continuous_subtype_val
  have hlt : ∫ z, dU (ξ - g ξ) * z.1 ∂μ <
      ∫ z, dU (f (g ξ) * z.1 - g (f (g ξ) * z.1)) * z.1 ∂μ := by
    refine integral_lt_of_lt_on μ hF hG (fun z => ?_)
      (hZ.pos μ le_rfl (a := 1) (b := (1 + zbar) / 2) (by linarith [h.zbar_gt])
        (by linarith [h.zbar_gt]) (S := {z | z.1 < zbar}) fun z hz => by
          change z.1 < zbar; linarith [hz.2, h.zbar_gt]) fun z hz => ?_
    · have hc : f (g ξ) * z.1 - g (f (g ξ) * z.1) ≤ ξ - g ξ :=
        hE.c_mono.monotoneOn ⟨(hkzpos z).le, hkzx z⟩ hξ (hkz z)
      exact mul_le_mul_of_nonneg_right (hE.dU_anti.antitoneOn (hE.c_pos _ ⟨hkzpos z, hkzx z⟩)
        (mem_Ioi.2 hcξ) hc) (by linarith [z.2.1])
    · have hzlt : f (g ξ) * z.1 < ξ := by
        have : f (g ξ) * z.1 < f (g ξ) * zbar := mul_lt_mul_of_pos_left hz hk
        rwa [← hfix] at this
      have hc : f (g ξ) * z.1 - g (f (g ξ) * z.1) < ξ - g ξ :=
        hE.c_mono ⟨(hkzpos z).le, hkzx z⟩ hξ hzlt
      exact mul_lt_mul_of_pos_right (hE.dU_anti (hE.c_pos _ ⟨hkzpos z, hkzx z⟩)
        (mem_Ioi.2 hcξ) hc) (by linarith [z.2.1])
  have heul := hE.euler_ge ξ hξ'
  rw [euler_integral_eq μ] at heul
  rw [integral_const_mul] at hlt
  have hdU := hE.dU_pos _ hcξ
  have hβd : 0 < β * df (g ξ) := mul_pos hE.β_pos hd
  have : β * df (g ξ) * zstar μ * dU (ξ - g ξ) < 1 * dU (ξ - g ξ) := by
    have := mul_lt_mul_of_pos_left hlt hβd
    rw [zstar]
    nlinarith
  exact lt_of_mul_lt_mul_right this hdU.le

include h in
/-- **The case `x = x̄`** (Ex. 13.3e, the manual's mirror argument). At a fixed point
`ϑ = f(g(ϑ))`, either `g(ϑ) = 0` or the Euler equation (with equality, as `g(ϑ) > 0`) gives
`U′(c(ϑ)) = βf′(g(ϑ)) ∫ U′(c(ϑ z)) z μ(dz) < βf′(g(ϑ)) U′(c(ϑ)) z*`, so `βf′(g(ϑ)) z* > 1`. The
strict step needs `μ{z > 1} > 0`, which (Z3) gives. -/
theorem growth_euler_theta {α : ℝ} (hZ : ShockZ3 μ α) (hgc : ContinuousOn g (Icc 0 xbar))
    (hf0 : 0 < f 0) (hE : GrowthEuler f g df dU β xbar zbar μ) {θ : ℝ} (hθ : θ ∈ Icc 0 xbar)
    (hfix : θ = f (g θ) * 1) : g θ = 0 ∨ 1 < β * df (g θ) * zstar μ := by
  rcases (h.g_nonneg θ hθ).eq_or_lt with h0 | hgpos
  · exact Or.inl h0.symm
  right
  rw [mul_one] at hfix
  have hk : 0 < f (g θ) := hf0.trans_le (h.f0_le_fg hθ)
  have hθpos : 0 < θ := hfix ▸ hk
  have hθ' : θ ∈ Ioc 0 xbar := ⟨hθpos, hθ.2⟩
  have hz1 := one_le_zstar μ
  have hkzx : ∀ z : Icc (1 : ℝ) zbar, f (g θ) * z.1 ≤ xbar := fun z =>
    (h.mem hθ (mem_Z z.2)).2
  have hkz : ∀ z : Icc (1 : ℝ) zbar, θ ≤ f (g θ) * z.1 := fun z => by
    rw [← hfix]; nlinarith [z.2.1]
  have hkzpos : ∀ z : Icc (1 : ℝ) zbar, 0 < f (g θ) * z.1 := fun z =>
    mul_pos hk (by linarith [z.2.1])
  have hcθ := hE.c_pos θ hθ'
  have hG := continuous_euler_integrand μ hE hgc hk hkzx
  have hF : Continuous fun z : Icc (1 : ℝ) zbar => dU (θ - g θ) * z.1 :=
    continuous_const.mul continuous_subtype_val
  have hlt : ∫ z, dU (f (g θ) * z.1 - g (f (g θ) * z.1)) * z.1 ∂μ <
      ∫ z, dU (θ - g θ) * z.1 ∂μ := by
    refine integral_lt_of_lt_on μ hG hF (fun z => ?_)
      (hZ.pos μ (a := (1 + zbar) / 2) (b := zbar) (by linarith [h.zbar_gt])
        (by linarith [h.zbar_gt]) le_rfl (S := {z | 1 < z.1}) fun z hz => by
          change 1 < z.1; linarith [hz.1, h.zbar_gt]) fun z hz => ?_
    · have hc : θ - g θ ≤ f (g θ) * z.1 - g (f (g θ) * z.1) :=
        hE.c_mono.monotoneOn hθ ⟨(hkzpos z).le, hkzx z⟩ (hkz z)
      exact mul_le_mul_of_nonneg_right (hE.dU_anti.antitoneOn (mem_Ioi.2 hcθ)
        (hE.c_pos _ ⟨hkzpos z, hkzx z⟩) hc) (by linarith [z.2.1])
    · have hzlt : θ < f (g θ) * z.1 := by
        have : f (g θ) * 1 < f (g θ) * z.1 := mul_lt_mul_of_pos_left hz hk
        linarith
      have hc : θ - g θ < f (g θ) * z.1 - g (f (g θ) * z.1) :=
        hE.c_mono hθ ⟨(hkzpos z).le, hkzx z⟩ hzlt
      exact mul_lt_mul_of_pos_right (hE.dU_anti (mem_Ioi.2 hcθ)
        (hE.c_pos _ ⟨hkzpos z, hkzx z⟩) hc) (by linarith [z.2.1])
  have heul := hE.euler_eq θ hθ' hgpos
  rw [euler_integral_eq μ] at heul
  have hdU := hE.dU_pos _ hcθ
  rw [integral_const_mul, ← zstar] at hlt
  have hGnn : 0 ≤ ∫ z, dU (f (g θ) * z.1 - g (f (g θ) * z.1)) * z.1 ∂μ :=
    integral_nonneg fun z => (mul_pos (hE.dU_pos _ (hE.c_pos _ ⟨hkzpos z, hkzx z⟩))
      (by linarith [z.2.1])).le
  have hd : 0 < df (g θ) := by
    by_contra hd
    replace hd := not_lt.1 hd
    have : β * (df (g θ) * ∫ z, dU (f (g θ) * z.1 - g (f (g θ) * z.1)) * z.1 ∂μ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hE.β_pos.le (mul_nonpos_of_nonpos_of_nonneg hd hGnn)
    linarith
  have hβd : 0 < β * df (g θ) := mul_pos hE.β_pos hd
  have : 1 * dU (θ - g θ) < β * df (g θ) * zstar μ * dU (θ - g θ) := by
    have := mul_lt_mul_of_pos_left hlt hβd
    nlinarith
  exact lt_of_mul_lt_mul_right this hdU.le

include h in
/-- **Existence of `x*`** (NOTE p. 393–394; the book only asserts it). If
`βf′(g(ξ)) z* < 1` at some `ξ ∈ X`, the intermediate value theorem gives `x* ∈ [0, ξ]` with
`βf′(g(x*)) z* = 1`, because `g(0) = 0` and `βf′(0) z* ≥ βf′(0) > 1`. -/
theorem growth_xstar_exists (hgc : ContinuousOn g (Icc 0 xbar))
    (hE : GrowthEuler f g df dU β xbar zbar μ) {ξ : ℝ} (hξ : ξ ∈ Icc 0 xbar)
    (hlt : β * df (g ξ) * zstar μ < 1) :
    ∃ xs ∈ Icc 0 ξ, β * df (g xs) * zstar μ = 1 := by
  have hg0 : g 0 = 0 :=
    le_antisymm (h.g_le 0 ⟨le_rfl, h.xbar_pos.le⟩) (h.g_nonneg 0 ⟨le_rfl, h.xbar_pos.le⟩)
  have hsub : Icc 0 ξ ⊆ Icc 0 xbar := Icc_subset_Icc le_rfl hξ.2
  have hcont : ContinuousOn (fun x => β * df (g x) * zstar μ) (Icc 0 ξ) :=
    (continuousOn_const.mul (hE.df_cont.comp (hgc.mono hsub) fun x hx => h.g_mem (hsub hx))).mul
      continuousOn_const
  have h0 : 1 ≤ β * df (g 0) * zstar μ := by
    rw [hg0]
    have := one_le_zstar μ
    nlinarith [hE.βdf]
  obtain ⟨xs, hxs, hval⟩ := intermediate_value_Icc' hξ.1 hcont ⟨hlt.le, h0⟩
  exact ⟨xs, hxs, hval⟩

include h in
/-- **`ϑ < x* < ξ` for every `x*`** (NOTE p. 393–394). `x*` need not be unique since `f` is only
weakly concave; but `βf′(g(ξ)) z* < 1 = βf′(g(x*)) z*` gives `f′(g(ξ)) < f′(g(x*))`, hence
`g(ξ) > g(x*)` and `ξ > x*`; and at `ϑ` either `g(ϑ) = 0 < g(x*)` (`g(x*) = 0` would give
`βf′(0) z* = 1`) or `f′(g(ϑ)) > f′(g(x*))`, so `ϑ < x*`. -/
theorem growth_xstar_between (hgm : MonotoneOn g (Icc 0 xbar))
    (hE : GrowthEuler f g df dU β xbar zbar μ) {xs ξ θ : ℝ} (hxs : xs ∈ Icc 0 xbar)
    (hξ : ξ ∈ Icc 0 xbar) (hθ : θ ∈ Icc 0 xbar) (hH : β * df (g xs) * zstar μ = 1)
    (hHξ : β * df (g ξ) * zstar μ < 1) (hHθ : g θ = 0 ∨ 1 < β * df (g θ) * zstar μ) :
    θ < xs ∧ xs < ξ := by
  have hz : 0 < β * zstar μ := mul_pos hE.β_pos (by linarith [one_le_zstar μ])
  constructor
  · by_contra hle
    replace hle := not_lt.1 hle
    have hg := hgm hxs hθ hle
    rcases hHθ with h0 | h1
    · have : g xs = 0 := le_antisymm (h0 ▸ hg) (h.g_nonneg xs hxs)
      rw [this] at hH
      have := one_le_zstar μ
      nlinarith [hE.βdf]
    · have hd := hE.df_anti (h.g_mem hxs) (h.g_mem hθ) hg
      nlinarith
  · by_contra hle
    replace hle := not_lt.1 hle
    have hg := hgm hξ hxs hle
    have hd := hE.df_anti (h.g_mem hξ) (h.g_mem hxs) hg
    nlinarith

/-! ### Assumption 12.1 at both endpoints, and Theorem 12.12 -/

include h in
/-- `φₙ(0, z̄)` increases to a fixed point `ξ = f(g(ξ)) z̄` (SLP (4), p. 394). -/
theorem growth_xi (hgm : MonotoneOn g (Icc 0 xbar)) (hgc : ContinuousOn g (Icc 0 xbar)) :
    ∃ ξ, Monotone (growthPhi f g 0 zbar) ∧ Tendsto (growthPhi f g 0 zbar) atTop (𝓝 ξ) ∧
      ξ ∈ Icc 0 xbar ∧ ξ = f (g ξ) * zbar := by
  have h0 : (0 : ℝ) ∈ Icc 0 xbar := ⟨le_rfl, h.xbar_pos.le⟩
  have hz : zbar ∈ Icc 0 zbar := ⟨by linarith [h.zbar_gt], le_rfl⟩
  have hmono := h.phi_monotone hgm h0 hz (mul_nonneg (h.fg_nonneg h0) hz.1)
  have hlim := tendsto_atTop_ciSup hmono ⟨xbar, by
    rintro _ ⟨n, rfl⟩; exact (h.phi_mem h0 hz n).2⟩
  obtain ⟨hξ, hfix⟩ := h.phi_limit hgc h0 hz hlim
  exact ⟨_, hmono, hlim, hξ, hfix⟩

include h in
/-- `φₙ(x̄, 1)` decreases to a fixed point `ϑ = f(g(ϑ))` (the manual, Ex. 13.3e):
`φ₁(x̄, 1) = f(g(x̄)) ≤ f(x̄) ≤ x̄`. -/
theorem growth_theta (hgm : MonotoneOn g (Icc 0 xbar)) (hgc : ContinuousOn g (Icc 0 xbar)) :
    ∃ θ, Antitone (growthPhi f g xbar 1) ∧ Tendsto (growthPhi f g xbar 1) atTop (𝓝 θ) ∧
      θ ∈ Icc 0 xbar ∧ θ = f (g θ) * 1 := by
  have hx : xbar ∈ Icc 0 xbar := ⟨h.xbar_pos.le, le_rfl⟩
  have hz : (1 : ℝ) ∈ Icc 0 zbar := ⟨zero_le_one, h.zbar_gt.le⟩
  have hanti := h.phi_antitone hgm hx hz (h.mem hx hz).2
  have hlim := tendsto_atTop_ciInf hanti ⟨0, by
    rintro _ ⟨n, rfl⟩; exact (h.phi_mem hx hz n).1⟩
  obtain ⟨hθ, hfix⟩ := h.phi_limit hgc hx hz hlim
  exact ⟨_, hanti, hlim, hθ, hfix⟩

include h in
/-- From `ξ > x*`: for all large `N` there is `δ ∈ (0, z̄ − 1]` with `φ_N(0, z̄ − δ) > x*`
(continuity of `φ_N(0, ·)`). -/
theorem growth_bottom_delta (hgc : ContinuousOn g (Icc 0 xbar)) {xs ξ : ℝ}
    (hmono : Monotone (growthPhi f g 0 zbar)) (hlim : Tendsto (growthPhi f g 0 zbar) atTop (𝓝 ξ))
    (hxs : xs < ξ) : ∃ N₁, ∀ N ≥ N₁, ∃ δ, 0 < δ ∧ δ ≤ zbar - 1 ∧
      xs < growthPhi f g 0 (zbar - δ) N := by
  have h0 : (0 : ℝ) ∈ Icc 0 xbar := ⟨le_rfl, h.xbar_pos.le⟩
  have hz : zbar ∈ Icc 0 zbar := ⟨by linarith [h.zbar_gt], le_rfl⟩
  obtain ⟨N₁, hN₁⟩ := (hlim.eventually (lt_mem_nhds hxs)).exists
  refine ⟨N₁, fun N hN => ?_⟩
  have hlt : xs < growthPhi f g 0 zbar N := hN₁.trans_le (hmono hN)
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.continuousOn_iff.1 (h.continuousOn_phi hgc h0 N) zbar hz _
    (sub_pos.2 hlt)
  have hm1 := min_le_left (δ₀ / 2) (zbar - 1)
  have hm2 := min_le_right (δ₀ / 2) (zbar - 1)
  have hδpos : 0 < min (δ₀ / 2) (zbar - 1) := lt_min (by linarith) (by linarith [h.zbar_gt])
  refine ⟨min (δ₀ / 2) (zbar - 1), hδpos, hm2, ?_⟩
  have hmem : zbar - min (δ₀ / 2) (zbar - 1) ∈ Icc 0 zbar := ⟨by linarith, by linarith⟩
  have hd : dist (zbar - min (δ₀ / 2) (zbar - 1)) zbar < δ₀ := by
    rw [Real.dist_eq, show zbar - min (δ₀ / 2) (zbar - 1) - zbar = -min (δ₀ / 2) (zbar - 1) by
      ring, abs_neg, abs_of_pos hδpos]
    linarith
  have := hδ _ hmem hd
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.1]

include h in
/-- From `ϑ < x*`: for all large `N` there is `δ ∈ (0, z̄ − 1]` with `φ_N(x̄, 1 + δ) < x*`. -/
theorem growth_top_delta (hgc : ContinuousOn g (Icc 0 xbar)) {xs θ : ℝ}
    (hanti : Antitone (growthPhi f g xbar 1)) (hlim : Tendsto (growthPhi f g xbar 1) atTop (𝓝 θ))
    (hxs : θ < xs) : ∃ N₂, ∀ N ≥ N₂, ∃ δ, 0 < δ ∧ δ ≤ zbar - 1 ∧
      growthPhi f g xbar (1 + δ) N < xs := by
  have hx : xbar ∈ Icc 0 xbar := ⟨h.xbar_pos.le, le_rfl⟩
  have hz : (1 : ℝ) ∈ Icc 0 zbar := ⟨zero_le_one, h.zbar_gt.le⟩
  obtain ⟨N₂, hN₂⟩ := (hlim.eventually (gt_mem_nhds hxs)).exists
  refine ⟨N₂, fun N hN => ?_⟩
  have hlt : growthPhi f g xbar 1 N < xs := (hanti hN).trans_lt hN₂
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.continuousOn_iff.1 (h.continuousOn_phi hgc hx N) 1 hz _
    (sub_pos.2 hlt)
  have hm1 := min_le_left (δ₀ / 2) (zbar - 1)
  have hm2 := min_le_right (δ₀ / 2) (zbar - 1)
  have hδpos : 0 < min (δ₀ / 2) (zbar - 1) := lt_min (by linarith) (by linarith [h.zbar_gt])
  refine ⟨min (δ₀ / 2) (zbar - 1), hδpos, hm2, ?_⟩
  have hmem : 1 + min (δ₀ / 2) (zbar - 1) ∈ Icc 0 zbar := ⟨by linarith, by linarith⟩
  have hd : dist (1 + min (δ₀ / 2) (zbar - 1)) 1 < δ₀ := by
    rw [Real.dist_eq, show 1 + min (δ₀ / 2) (zbar - 1) - 1 = min (δ₀ / 2) (zbar - 1) by ring,
      abs_of_pos hδpos]
    linarith
  have := hδ _ hmem hd
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.2]

/-- **The case `x = 0`** (SLP p. 394), in the book's form: for some `N ≥ 1` and `δ > 0`,
`Pᴺ(0, (x*, x̄]) ≥ Pᴺ(0, (φ_N(0, z̄ − δ), φ_N(0, z̄)]) ≥ αᴺδᴺ`, for every `x*` with
`βf′(g(x*)) z* = 1`. -/
theorem growth_case_zero {α : ℝ} (hZ : ShockZ3 μ α) (hgm : MonotoneOn g (Icc 0 xbar))
    (hgc : ContinuousOn g (Icc 0 xbar)) (hf0 : 0 < f 0) (hE : GrowthEuler f g df dU β xbar zbar μ)
    {xs : ℝ} (hxs : xs ∈ Icc 0 xbar) (hH : β * df (g xs) * zstar μ = 1) :
    ∃ N, 1 ≤ N ∧ ∃ δ, 0 < δ ∧
      (α * δ) ^ N ≤ (kpow (growthP h μ) N ⟨0, le_rfl, h.xbar_pos.le⟩).real (Subtype.val ⁻¹'
        Ioc (growthPhi f g 0 (zbar - δ) N) (growthPhi f g 0 zbar N)) ∧
      (kpow (growthP h μ) N ⟨0, le_rfl, h.xbar_pos.le⟩).real (Subtype.val ⁻¹'
        Ioc (growthPhi f g 0 (zbar - δ) N) (growthPhi f g 0 zbar N)) ≤
      (kpow (growthP h μ) N ⟨0, le_rfl, h.xbar_pos.le⟩).real (Subtype.val ⁻¹' Ioc xs xbar) := by
  have := isMarkovKernel_growthP h μ
  obtain ⟨ξ, hmono, hlim, hξ, hfix⟩ := growth_xi h hgm hgc
  obtain ⟨θ, -, -, hθ, hθfix⟩ := growth_theta h hgm hgc
  have hlt := (growth_xstar_between h μ hgm hE hxs hξ hθ hH (growth_euler_xi h μ hZ hgc hf0 hE hξ
    hfix) (growth_euler_theta h μ hZ hgc hf0 hE hθ hθfix)).2
  obtain ⟨N₁, hN₁⟩ := growth_bottom_delta h hgc hmono hlim hlt
  obtain ⟨δ, hδ, hδ1, hlo⟩ := hN₁ (max N₁ 1) (le_max_left _ _)
  have := ex_8_4a (growthP h μ) (max N₁ 1)
  refine ⟨max N₁ 1, le_max_right _ _, δ, hδ, growth_3a h μ hZ hgm hf0 _ hδ.le hδ1
    (le_max_right _ _), measureReal_mono fun x hx => ⟨hlo.trans hx.1, x.2.2⟩⟩

/-- **Exercise 13.3e.** For some `N ≥ 1` and `δ > 0`,
`Pᴺ(x̄, (0, x*]) ≥ Pᴺ(x̄, (φ_N(x̄, 1), φ_N(x̄, 1 + δ)]) ≥ αᴺδᴺ`, for every `x*` with
`βf′(g(x*)) z* = 1`. -/
theorem ex_13_3e {α : ℝ} (hZ : ShockZ3 μ α) (hgm : MonotoneOn g (Icc 0 xbar))
    (hgc : ContinuousOn g (Icc 0 xbar)) (hf0 : 0 < f 0) (hE : GrowthEuler f g df dU β xbar zbar μ)
    {xs : ℝ} (hxs : xs ∈ Icc 0 xbar) (hH : β * df (g xs) * zstar μ = 1) :
    ∃ N, 1 ≤ N ∧ ∃ δ, 0 < δ ∧
      (α * δ) ^ N ≤ (kpow (growthP h μ) N ⟨xbar, h.xbar_pos.le, le_rfl⟩).real (Subtype.val ⁻¹'
        Ioc (growthPhi f g xbar 1 N) (growthPhi f g xbar (1 + δ) N)) ∧
      (kpow (growthP h μ) N ⟨xbar, h.xbar_pos.le, le_rfl⟩).real (Subtype.val ⁻¹'
        Ioc (growthPhi f g xbar 1 N) (growthPhi f g xbar (1 + δ) N)) ≤
      (kpow (growthP h μ) N ⟨xbar, h.xbar_pos.le, le_rfl⟩).real (Subtype.val ⁻¹' Ioc 0 xs) := by
  have := isMarkovKernel_growthP h μ
  obtain ⟨ξ, -, -, hξ, hfix⟩ := growth_xi h hgm hgc
  obtain ⟨θ, hanti, hlim, hθ, hθfix⟩ := growth_theta h hgm hgc
  have hlt := (growth_xstar_between h μ hgm hE hxs hξ hθ hH (growth_euler_xi h μ hZ hgc hf0 hE hξ
    hfix) (growth_euler_theta h μ hZ hgc hf0 hE hθ hθfix)).1
  obtain ⟨N₂, hN₂⟩ := growth_top_delta h hgc hanti hlim hlt
  obtain ⟨δ, hδ, hδ1, hhi⟩ := hN₂ (max N₂ 1) (le_max_left _ _)
  have := ex_8_4a (growthP h μ) (max N₂ 1)
  have hx : xbar ∈ Icc 0 xbar := ⟨h.xbar_pos.le, le_rfl⟩
  have hz : (1 : ℝ) ∈ Icc 0 zbar := ⟨zero_le_one, h.zbar_gt.le⟩
  refine ⟨max N₂ 1, le_max_right _ _, δ, hδ, growth_3b h μ hZ hgm hf0 _ hδ.le hδ1
    (le_max_right _ _), measureReal_mono fun x hx' =>
      ⟨(h.phi_mem hx hz _).1.trans_lt hx'.1, hx'.2.trans hhi.le⟩⟩

/-- **Uniqueness and global stability of the invariant distribution of output** (SLP §13.3,
pp. 393–394). Under (Z3), with `f(0) > 0`, a continuous nondecreasing policy `g` satisfying the
Euler hypotheses `GrowthEuler`: some `x*` has `βf′(g(x*)) z* = 1`; Assumption 12.1 holds with
`c = x*` (`Pᴺ(0, [x*, x̄]) ≥ ε` and `Pᴺ(x̄, [0, x*]) ≥ ε`); and so (Theorem 12.12, with
Ex. 13.3d and the Feller property) `P` has a unique invariant probability measure `λ*`, and
`T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem growth_invariant_unique {α : ℝ} (hZ : ShockZ3 μ α) (hgm : MonotoneOn g (Icc 0 xbar))
    (hgc : ContinuousOn g (Icc 0 xbar)) (hf0 : 0 < f 0)
    (hE : GrowthEuler f g df dU β xbar zbar μ) :
    ∃ xs : Icc (0 : ℝ) xbar, β * df (g xs.1) * zstar μ = 1 ∧
      (∃ ε : ℝ, ∃ N : ℕ, 0 < ε ∧ 1 ≤ N ∧
        ε ≤ (kpow (growthP h μ) N ⟨0, le_rfl, h.xbar_pos.le⟩).real (Ici xs) ∧
        ε ≤ (kpow (growthP h μ) N ⟨xbar, h.xbar_pos.le, le_rfl⟩).real (Iic xs)) ∧
      ∃ lam : Measure (Icc (0 : ℝ) xbar), IsProbabilityMeasure lam ∧
        adjointOp (growthP h μ) lam = lam ∧
        (∀ ν : Measure (Icc (0 : ℝ) xbar), IsProbabilityMeasure ν →
          adjointOp (growthP h μ) ν = ν → ν = lam) ∧
        ∀ lam₀ : Measure (Icc (0 : ℝ) xbar), IsProbabilityMeasure lam₀ →
          ConvWeak (fun n => (adjointOp (growthP h μ))^[n] lam₀) lam := by
  have := isMarkovKernel_growthP h μ
  obtain ⟨ξ, hmono, hlim, hξ, hfix⟩ := growth_xi h hgm hgc
  obtain ⟨θ, hanti, hlimθ, hθ, hθfix⟩ := growth_theta h hgm hgc
  have hHξ := growth_euler_xi h μ hZ hgc hf0 hE hξ hfix
  obtain ⟨xs, hxs0, hH⟩ := growth_xstar_exists h μ hgc hE hξ hHξ
  have hxs : xs ∈ Icc 0 xbar := ⟨hxs0.1, hxs0.2.trans hξ.2⟩
  obtain ⟨hθx, hxξ⟩ := growth_xstar_between h μ hgm hE hxs hξ hθ hH hHξ
    (growth_euler_theta h μ hZ hgc hf0 hE hθ hθfix)
  obtain ⟨N₁, hN₁⟩ := growth_bottom_delta h hgc hmono hlim hxξ
  obtain ⟨N₂, hN₂⟩ := growth_top_delta h hgc hanti hlimθ hθx
  set N := max (max N₁ N₂) 1
  have hN : 1 ≤ N := le_max_right _ _
  obtain ⟨δ₁, hδ₁, hδ₁', hlo⟩ := hN₁ N ((le_max_left _ _).trans (le_max_left _ _))
  obtain ⟨δ₂, hδ₂, hδ₂', hhi⟩ := hN₂ N ((le_max_right _ _).trans (le_max_left _ _))
  have := ex_8_4a (growthP h μ) N
  set ε := min ((α * δ₁) ^ N) ((α * δ₂) ^ N)
  have hε : 0 < ε := lt_min (pow_pos (mul_pos hZ.1 hδ₁) N) (pow_pos (mul_pos hZ.1 hδ₂) N)
  have hbot : ε ≤ (kpow (growthP h μ) N ⟨0, le_rfl, h.xbar_pos.le⟩).real (Ici ⟨xs, hxs⟩) :=
    (min_le_left _ _).trans ((growth_3a h μ hZ hgm hf0 _ hδ₁.le hδ₁' hN).trans
      (measureReal_mono fun x hx' => (hlo.trans hx'.1).le))
  have htop : ε ≤ (kpow (growthP h μ) N ⟨xbar, h.xbar_pos.le, le_rfl⟩).real (Iic ⟨xs, hxs⟩) :=
    (min_le_right _ _).trans ((growth_3b h μ hZ hgm hf0 _ hδ₂.le hδ₂' hN).trans
      (measureReal_mono fun x hx' => hx'.2.trans hhi.le))
  exact ⟨⟨xs, hxs⟩, hH, ⟨ε, N, hε, hN, hbot, htop⟩, theorem_12_12_real h.xbar_pos.le
    (growthP h μ) (ex_13_3d h μ hgm) (growthP_isFeller h μ hgc) hε hN hbot htop⟩

/-! ### The role of `f(0) > 0` -/

/-- **If `f(0) = 0`, `{0}` is invariant** (SLP pp. 394–395): `g(0) = 0` and `f(0) = 0` give
`P(0, ·) = δ₀`, so `δ₀` is an invariant measure, `Pⁿ(0, ·) = δ₀` for all `n`, and
`Pⁿ(0, [c, x̄]) = 0` for every `c > 0`: inequality (4) and the first half of Assumption 12.1
fail for every `c > 0`. -/
theorem growth_f_zero (hf : f 0 = 0) :
    growthP h μ ⟨0, le_rfl, h.xbar_pos.le⟩ = Measure.dirac ⟨0, le_rfl, h.xbar_pos.le⟩ ∧
      adjointOp (growthP h μ) (Measure.dirac ⟨0, le_rfl, h.xbar_pos.le⟩) =
        Measure.dirac ⟨0, le_rfl, h.xbar_pos.le⟩ ∧
      (∀ n, kpow (growthP h μ) n ⟨0, le_rfl, h.xbar_pos.le⟩ =
        Measure.dirac ⟨0, le_rfl, h.xbar_pos.le⟩) ∧
      ∀ c : Icc (0 : ℝ) xbar, 0 < c.1 → ∀ n,
        kpow (growthP h μ) n ⟨0, le_rfl, h.xbar_pos.le⟩ (Ici c) = 0 := by
  have hg0 : g 0 = 0 :=
    le_antisymm (h.g_le 0 ⟨le_rfl, h.xbar_pos.le⟩) (h.g_nonneg 0 ⟨le_rfl, h.xbar_pos.le⟩)
  have hP : growthP h μ ⟨0, le_rfl, h.xbar_pos.le⟩ = Measure.dirac ⟨0, le_rfl, h.xbar_pos.le⟩ := by
    have : (fun z => growthNext h (⟨0, le_rfl, h.xbar_pos.le⟩, z)) =
        fun _ => (⟨0, le_rfl, h.xbar_pos.le⟩ : Icc (0 : ℝ) xbar) :=
      funext fun z => Subtype.ext (by simp [growthNext, hg0, hf])
    rw [growthP_eq, this, Measure.map_const, measure_univ, one_smul]
  have hadj : adjointOp (growthP h μ) (Measure.dirac ⟨0, le_rfl, h.xbar_pos.le⟩) =
      Measure.dirac ⟨0, le_rfl, h.xbar_pos.le⟩ := by
    rw [adjointOp_dirac, hP]
  have hk : ∀ n, kpow (growthP h μ) n ⟨0, le_rfl, h.xbar_pos.le⟩ =
      Measure.dirac ⟨0, le_rfl, h.xbar_pos.le⟩ := fun n => by
    rw [← iterate_dirac, Function.iterate_fixed hadj]
  refine ⟨hP, hadj, hk, fun c hc n => ?_⟩
  rw [hk, Measure.dirac_apply' _ measurableSet_Ici, indicator_of_notMem]
  exact fun h0 => absurd (h0 : c ≤ ⟨0, le_rfl, h.xbar_pos.le⟩) (not_le.2 hc)

/-- **The repair for `f(0) = 0`** (SLP p. 395): if `g` is nondecreasing and `f(g(ε)) ≥ ε`, then
`[ε, x̄]` is invariant: `P(x, [ε, x̄]) = 1` for `x ≥ ε`, since `f(g(x)) z ≥ f(g(ε)) ≥ ε`. -/
theorem growth_invariant_interval (hgm : MonotoneOn g (Icc 0 xbar)) {ε : ℝ}
    (hε : ε ∈ Icc 0 xbar) (hfε : ε ≤ f (g ε)) (x : Icc (0 : ℝ) xbar) (hx : ε ≤ x.1) :
    growthP h μ x {y | ε ≤ y.1} = 1 := by
  have hm : MeasurableSet {y : Icc (0 : ℝ) xbar | ε ≤ y.1} :=
    measurableSet_le measurable_const measurable_subtype_coe
  rw [growthP_apply h μ x hm]
  have : {z | growthNext h (x, z) ∈ {y : Icc (0 : ℝ) xbar | ε ≤ y.1}} = univ := by
    ext z
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    change ε ≤ f (g x.1) * z.1
    have h1 := h.fg_mono hgm hε x.2 hx
    have h2 := h.fg_nonneg x.2
    nlinarith [z.2.1]
  rw [this, measure_univ]

/-- If `f(0) = 0` and some other invariant probability measure `ν ≠ δ₀` exists (another
ergodic set), the invariant measure is not unique (SLP p. 395). -/
theorem growth_f_zero_not_unique (hf : f 0 = 0) {ν : Measure (Icc (0 : ℝ) xbar)}
    (hν : adjointOp (growthP h μ) ν = ν) (hne : ν ≠ Measure.dirac ⟨0, le_rfl, h.xbar_pos.le⟩) :
    ¬ ∀ ν₁ ν₂ : Measure (Icc (0 : ℝ) xbar), adjointOp (growthP h μ) ν₁ = ν₁ →
      adjointOp (growthP h μ) ν₂ = ν₂ → ν₁ = ν₂ :=
  fun hu => hne (hu _ _ hν (growth_f_zero h μ hf).2.1)

/-! ### The optimal policy of §13.3 -/

/-- The policy function of Ex. 13.3b as a function on `ℝ` (constant off `X`). -/
noncomputable def outPolicyR {U : ℝ → ℝ} {β : ℝ} (hO : OutputHyp U f β xbar zbar)
    (μ : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure μ] [Nonempty (Icc (0 : ℝ) xbar)]
    (v : Icc (0 : ℝ) xbar →ᵇ ℝ) (x : ℝ) : ℝ :=
  (outPolicy hO μ v (projIcc 0 xbar hO.xbar_pos.le x)).1

variable {U : ℝ → ℝ} (hO : OutputHyp U f β xbar zbar) [Nonempty (Icc (0 : ℝ) xbar)]

theorem outPolicyR_eq (v : Icc (0 : ℝ) xbar →ᵇ ℝ) {x : ℝ} (hx : x ∈ Icc 0 xbar) :
    outPolicyR hO μ v x = (outPolicy hO μ v ⟨x, hx⟩).1 := by
  rw [outPolicyR, projIcc_of_mem _ hx]

/-- The optimal policy (Ex. 13.3b) satisfies the hypotheses `GrowthLaw` of the law of motion. -/
theorem outPolicyR_growthLaw (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ} (hv : outT hO μ v = v) :
    GrowthLaw f (outPolicyR hO μ v) xbar zbar := by
  obtain ⟨-, hfix, -, hgc, -, -⟩ := ex_13_3b hO μ hU hf hv
  exact ⟨hO.zbar_gt, hO.xbar_pos, hO.f_cont, hO.f_mono.monotoneOn, hO.f_pos.le,
    hO.xbar_maintain, fun x hx => by rw [outPolicyR_eq μ hO v hx]; exact (outPolicy _ _ _ _).2.1,
    fun x hx => by rw [outPolicyR_eq μ hO v hx]; exact (hfix ⟨x, hx⟩).1,
    (continuous_subtype_val.comp (hgc.comp continuous_projIcc)).measurable⟩

/-- **Uniqueness and global stability for the optimal policy** (SLP §13.3). Under the
primitives (`OutputHyp`, `U` strictly concave and differentiable, `f` concave), (Z3), and the
hypotheses of `GrowthEuler` other than the monotonicity of consumption — which the optimal
policy satisfies (`out_consumption_strictMono`) once consumption is positive — the output
process under the optimal policy `g` of Ex. 13.3b has a unique invariant probability measure,
and `T*ⁿλ₀ ⇒ λ*` for every `λ₀`. The Euler equation (with the corner inequality) and positive
consumption remain hypotheses: the first-order conditions are not derived here. -/
theorem growth_optimal_invariant_unique {α : ℝ} (hZ : ShockZ3 μ α)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : outT hO μ v = v) (hdU : ∀ c, 0 < c → HasDerivAt U (dU c) c)
    (hdU_pos : ∀ c, 0 < c → 0 < dU c) (hdU_anti : StrictAntiOn dU (Ioi 0))
    (hdU_cont : ContinuousOn dU (Ioi 0)) (hdf_anti : AntitoneOn df (Ici 0))
    (hdf_cont : ContinuousOn df (Ici 0)) (hβdf : 1 < β * df 0)
    (hc_pos : ∀ x ∈ Ioc 0 xbar, 0 < x - outPolicyR hO μ v x)
    (heuler_ge : ∀ x ∈ Ioc 0 xbar, β * ∫ z, dU (f (outPolicyR hO μ v x) * z.1 -
        outPolicyR hO μ v (f (outPolicyR hO μ v x) * z.1)) * df (outPolicyR hO μ v x) * z.1 ∂μ ≤
      dU (x - outPolicyR hO μ v x))
    (heuler_eq : ∀ x ∈ Ioc 0 xbar, 0 < outPolicyR hO μ v x → dU (x - outPolicyR hO μ v x) =
      β * ∫ z, dU (f (outPolicyR hO μ v x) * z.1 -
        outPolicyR hO μ v (f (outPolicyR hO μ v x) * z.1)) * df (outPolicyR hO μ v x) * z.1 ∂μ) :
    ∃ lam : Measure (Icc (0 : ℝ) xbar), IsProbabilityMeasure lam ∧
      adjointOp (growthP (outPolicyR_growthLaw μ hO hU hf hv) μ) lam = lam ∧
      (∀ ν : Measure (Icc (0 : ℝ) xbar), IsProbabilityMeasure ν →
        adjointOp (growthP (outPolicyR_growthLaw μ hO hU hf hv) μ) ν = ν → ν = lam) ∧
      ∀ lam₀ : Measure (Icc (0 : ℝ) xbar), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp (growthP (outPolicyR_growthLaw μ hO hU hf hv) μ))^[n] lam₀)
          lam := by
  obtain ⟨-, -, -, hgc, hgm, -⟩ := ex_13_3b hO μ hU hf hv
  have hL := outPolicyR_growthLaw μ hO hU hf hv
  have hgmR : MonotoneOn (outPolicyR hO μ v) (Icc 0 xbar) := fun x hx y hy hxy => by
    rw [outPolicyR_eq μ hO v hx, outPolicyR_eq μ hO v hy]
    exact hgm (show (⟨x, hx⟩ : Icc (0 : ℝ) xbar) ≤ ⟨y, hy⟩ from hxy)
  have hgcR : ContinuousOn (outPolicyR hO μ v) (Icc 0 xbar) :=
    (continuous_subtype_val.comp (hgc.comp continuous_projIcc)).continuousOn
  have hcm : StrictMonoOn (fun x => x - outPolicyR hO μ v x) (Icc 0 xbar) :=
    fun x hx y hy hxy => by
      have hy0 : 0 < y := lt_of_le_of_lt hx.1 hxy
      have hcy := hc_pos y ⟨hy0, hy.2⟩
      simp only [outPolicyR_eq μ hO v hx, outPolicyR_eq μ hO v hy] at hcy ⊢
      exact out_consumption_strictMono hO μ hU hf hv hdU
        (show (⟨x, hx⟩ : Icc (0 : ℝ) xbar) < ⟨y, hy⟩ from hxy) hcy
  have hE : GrowthEuler f (outPolicyR hO μ v) df dU β xbar zbar μ :=
    ⟨hO.β_pos, hβdf, hdU_pos, hdU_anti, hdU_cont, hdf_anti, hdf_cont, hc_pos, hcm, heuler_ge,
      heuler_eq⟩
  obtain ⟨-, -, -, hres⟩ := growth_invariant_unique hL μ hZ hgmR hgcR hO.f_pos hE
  exact hres

end StokeyLucasPrescott.ConvergenceApplications
