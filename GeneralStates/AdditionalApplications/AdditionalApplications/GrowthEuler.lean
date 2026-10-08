/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.SolutionProperties
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Euler equation methods: the stochastic growth model

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.3.3 (pp. 284–290), with the
envelope results used in §8.3.4.

Income evolves as `y' = f(y − c)ξ'` (8.58) and the Bellman equation is (8.59). We take the
state and action spaces to be `ℝ` with `Γ(y) = [0, y ∨ 0]`, so that negative states are
inert, and write `B(y, c, v) = u(c) + β ∫ v(f((y − c) ∨ 0) z) φ(dz)`; on `ℝ₊` this is the book's
aggregator. The shock distribution `φ` is any probability measure on `(0, ∞)` (the book's
continuous density is not used).

* **Exercise 8.3.5**: `u'(c) → 0` as `c → ∞`.
* **Exercise 8.3.6** is false as stated: for `v = 𝟙_(0, ∞) ∈ bX`, `(y, c) ↦ B(y, c, v)` is
  discontinuous at `(y, y)`, and `v` has no greedy policy, so the ADP on `bX` is not regular.
  The continuity holds for `v ∈ bcX` (`exercise_8_3_6`).
* **Proposition 8.3.7** (**Exercise 8.3.7**): the fundamental optimality properties hold,
  `v* ∈ bcX` and VFI converges on `bcX` (Proposition 7.2.2). The book's OPI and HPI claims rest
  on Exercise 8.3.6 for all `v ∈ bX` and are not established.
* **Lemma 8.3.8** (**Exercise 8.3.8**): `v*` is increasing, concave on `ℝ₊` and continuous, and
  the optimal policy is unique (and continuous).
* **Proposition 8.3.9** and **Corollary 8.3.10** (envelope condition), proved with the
  differentiable sandwich of Clausen and Strub (2020): `σ(y) > 0`, `Tv` is strictly increasing,
  and `(Tv)' = u' ∘ σ` on `(0, ∞)`. The interiority claim `σ(y) < y` is false (`v = 0`).
* **Exercises 8.3.9, 8.3.10** and the comparison step of **Exercise 8.3.12**: solutions of the
  functional Euler equation, uniqueness and monotonicity of the Coleman–Reffett map.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- The differentiable sandwich in the concave case (Clausen and Strub, 2020): if `g` is concave
near `y`, `W ≤ g` near `y` with `W(y) = g(y)`, and `W` is differentiable at `y`, then `g` is
differentiable at `y` with the same derivative. -/
theorem hasDerivAt_of_concave_sandwich {g W : ℝ → ℝ} {s : Set ℝ} {y d : ℝ}
    (hg : ConcaveOn ℝ s g) (hs : s ∈ 𝓝 y) (hWg : ∀ᶠ t in 𝓝 y, W t ≤ g t) (hy : W y = g y)
    (hW : HasDerivAt W d y) : HasDerivAt g d y := by
  rw [hasDerivAt_iff_tendsto_slope] at hW ⊢
  have hr : Tendsto (fun t => 2 * y - t) (𝓝 y) (𝓝 y) := by
    have h : Tendsto (fun t : ℝ => 2 * y - t) (𝓝 y) (𝓝 (2 * y - y)) :=
      tendsto_const_nhds.sub tendsto_id
    rwa [show 2 * y - y = y by ring] at h
  have hr' : Tendsto (fun t => 2 * y - t) (𝓝[≠] y) (𝓝[≠] y) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hr.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff] at ht ⊢
        intro h
        exact ht (by linarith))
  have hW2 : Tendsto (fun t => slope W y (2 * y - t)) (𝓝[≠] y) (𝓝 d) := hW.comp hr'
  have hev1 : ∀ᶠ t in 𝓝[≠] y, t ∈ s ∧ W t ≤ g t :=
    (Filter.Eventually.and hs hWg).filter_mono nhdsWithin_le_nhds
  have hev2 : ∀ᶠ t in 𝓝[≠] y, 2 * y - t ∈ s ∧ W (2 * y - t) ≤ g (2 * y - t) := hr'.eventually hev1
  have hev3 : ∀ᶠ t in 𝓝[≠] y, t ≠ y := self_mem_nhdsWithin
  have hlo := hW.min hW2
  have hhi := hW.max hW2
  rw [min_self] at hlo
  rw [max_self] at hhi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hev1, hev2, hev3] with t ⟨ht, h1⟩ ⟨ht', h2⟩ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine (min_le_right _ _).trans ?_
      have hadj := hg.slope_anti_adjacent ht ht' hlt (by linarith : y < 2 * y - t)
      rw [slope_comm g, slope_def_field, slope_def_field]
      exact (div_le_div_of_nonneg_right (by linarith) (by linarith)).trans hadj
    · refine (min_le_left _ _).trans ?_
      rw [slope_def_field, slope_def_field]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · filter_upwards [hev1, hev2, hev3] with t ⟨ht, h1⟩ ⟨ht', h2⟩ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine le_trans ?_ (le_max_left _ _)
      rw [slope_comm g, slope_comm W, slope_def_field, slope_def_field]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    · refine le_trans ?_ (le_max_right _ _)
      have hadj := hg.slope_anti_adjacent ht' ht (by linarith : 2 * y - t < y) hgt
      rw [slope_comm W, slope_def_field, slope_def_field]
      exact hadj.trans (div_le_div_of_nonneg_right (by linarith) (by linarith))

/-- The stochastic optimal growth model of §8.3.3.1 under Assumption 8.3.1. -/
structure Growth where
  /-- utility -/
  u : ℝ → ℝ
  /-- production -/
  f : ℝ → ℝ
  /-- the shock distribution, on `(0, ∞)` -/
  φ : Measure ℝ
  [isProb : IsProbabilityMeasure φ]
  shock_pos : ∀ᵐ z ∂φ, 0 < z
  /-- the discount factor -/
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  measurable_u : Measurable u
  u_continuousOn : ContinuousOn u (Set.Ici 0)
  u_strictMonoOn : StrictMonoOn u (Set.Ici 0)
  u_strictConcaveOn : StrictConcaveOn ℝ (Set.Ici 0) u
  u_differentiableAt : ∀ c, 0 < c → DifferentiableAt ℝ u c
  u_deriv_continuousOn : ContinuousOn (deriv u) (Set.Ioi 0)
  u_bdd : ∃ C, ∀ c, 0 ≤ c → |u c| ≤ C
  u_zero : u 0 = 0
  /-- `u'(0) = ∞` -/
  u_inada : Tendsto (deriv u) (𝓝[>] 0) atTop
  measurable_f : Measurable f
  f_continuousOn : ContinuousOn f (Set.Ici 0)
  f_strictMonoOn : StrictMonoOn f (Set.Ici 0)
  f_concaveOn : ConcaveOn ℝ (Set.Ici 0) f
  f_differentiableAt : ∀ k, 0 < k → DifferentiableAt ℝ f k
  f_zero : f 0 = 0

namespace Growth

variable (G : Growth)

attribute [local instance] Growth.isProb

theorem u_concaveOn : ConcaveOn ℝ (Set.Ici 0) G.u := G.u_strictConcaveOn.concaveOn

theorem u_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : G.u a ≤ G.u b :=
  G.u_strictMonoOn.monotoneOn ha (ha.trans hab) hab

theorem f_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : G.f a ≤ G.f b :=
  G.f_strictMonoOn.monotoneOn ha (ha.trans hab) hab

theorem f_nonneg {k : ℝ} (hk : 0 ≤ k) : 0 ≤ G.f k := by
  have := G.f_mono le_rfl hk
  rwa [G.f_zero] at this

theorem f_pos {k : ℝ} (hk : 0 < k) : 0 < G.f k := by
  have := G.f_strictMonoOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk.le) hk
  rwa [G.f_zero] at this

theorem deriv_u_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ deriv G.u c := by
  have h := G.u_concaveOn.slope_le_deriv (mem_Ici.2 hc.le) (mem_Ici.2 (by linarith : 0 ≤ c + 1))
    (by linarith : c < c + 1) (G.u_differentiableAt c hc)
  rw [slope_def_field] at h
  exact (div_nonneg (sub_nonneg.2 (G.u_mono hc.le (by linarith))) (by linarith)).trans h

theorem deriv_f_nonneg {k : ℝ} (hk : 0 < k) : 0 ≤ deriv G.f k := by
  have h := G.f_concaveOn.slope_le_deriv (mem_Ici.2 hk.le) (mem_Ici.2 (by linarith : 0 ≤ k + 1))
    (by linarith : k < k + 1) (G.f_differentiableAt k hk)
  rw [slope_def_field] at h
  exact (div_nonneg (sub_nonneg.2 (G.f_mono hk.le (by linarith))) (by linarith)).trans h

theorem deriv_u_strictAntiOn : StrictAntiOn (deriv G.u) (Set.Ioi 0) :=
  (G.u_strictConcaveOn.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    fun c hc => G.u_differentiableAt c hc

theorem deriv_f_antitoneOn : AntitoneOn (deriv G.f) (Set.Ioi 0) :=
  (G.f_concaveOn.subset Ioi_subset_Ici_self (convex_Ioi 0)).antitoneOn_deriv
    fun k hk => G.f_differentiableAt k hk

/-- **Exercise 8.3.5** (p. 285): under Assumption 8.3.1, `u'(c) → 0` as `c → ∞`. (The book's
solution uses the tangent inequality in the wrong direction for concave `u`; we use
`u(c) − u(c₀) ≥ u'(c)(c − c₀)`.) -/
theorem exercise_8_3_5 : Tendsto (deriv G.u) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := G.u_bdd
  have hanti : AntitoneOn (deriv G.u) (Set.Ioi 0) := G.deriv_u_strictAntiOn.antitoneOn
  have hsmall : ∀ ε > 0, ∃ c > 0, deriv G.u c < ε := by
    intro ε hε
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    set c := 1 + (2 * C + 1) / ε
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 le_rfl)
    have hc1 : 1 < c := by
      have : 0 < (2 * C + 1) / ε := div_pos (by linarith) hε
      linarith
    have h := G.u_concaveOn.deriv_le_slope (mem_Ici.2 zero_le_one) (mem_Ici.2 (by linarith))
      hc1 (G.u_differentiableAt c (by linarith))
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    have h2 := hcon c (by linarith)
    have h3 : ε * (c - 1) = 2 * C + 1 := by
      simp only [c]
      field_simp
      ring
    have h4 := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ c - 1)
    have h5 := abs_le.1 (hC c (by linarith))
    have h6 := abs_le.1 (hC 1 zero_le_one)
    linarith
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with c hc
    exact ha.trans_le (G.deriv_u_nonneg hc)
  · obtain ⟨c₀, hc₀, hlt⟩ := hsmall a ha
    filter_upwards [eventually_ge_atTop c₀] with c hc
    exact (hanti hc₀ (hc₀.trans_le hc) hc).trans_lt hlt

/-! ### The RDP of §8.3.3.1 -/

/-- The feasible correspondence `Γ(y) = [0, y ∨ 0]`. -/
def Γ (y : ℝ) : Set ℝ := Set.Icc 0 (max y 0)

/-- The continuation term `∫ v(f((y − c) ∨ 0) z) φ(dz)`. -/
noncomputable def cont (v : ℝ → ℝ) (y c : ℝ) : ℝ := ∫ z, v (G.f (max (y - c) 0) * z) ∂G.φ

/-- The aggregator `B(y, c, v) = u(c) + β ∫ v(f(y − c) z) φ(dz)`. -/
noncomputable def B (y c : ℝ) (v : ℝ → ℝ) : ℝ := G.u c + G.β * G.cont v y c

theorem measurable_integrand (v : BM ℝ) :
    Measurable fun q : (ℝ × ℝ) × ℝ => v.toFun (G.f (max (q.1.1 - q.1.2) 0) * q.2) :=
  v.measurable'.comp ((G.measurable_f.comp ((measurable_fst.fst.sub measurable_fst.snd).max
    measurable_const)).mul measurable_snd)

theorem integrable_cont (v : BM ℝ) (k : ℝ) : Integrable (fun z => v.toFun (k * z)) G.φ :=
  Integrable.of_bound (v.measurable'.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
    ‖v‖ (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)

theorem abs_cont_le (v : BM ℝ) (y c : ℝ) : |G.cont v.toFun y c| ≤ ‖v‖ := by
  have := norm_integral_le_of_norm_le_const (μ := G.φ)
    (f := fun z => v.toFun (G.f (max (y - c) 0) * z)) (C := ‖v‖)
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)
  unfold cont
  simpa using this

theorem cont_add_const (v : BM ℝ) (κ y c : ℝ) :
    G.cont (fun x => v.toFun x + κ) y c = G.cont v.toFun y c + κ := by
  unfold cont
  rw [integral_add (G.integrable_cont v _) (integrable_const κ)]
  simp

/-- The RDP `(Γ, bX, B)` of §8.3.3.1. -/
noncomputable def brdp : BRDP ℝ ℝ where
  Γ := Γ
  B := G.B
  measurable v := (G.measurable_u.comp measurable_snd).add (measurable_const.mul
    (G.measurable_integrand v).stronglyMeasurable.integral_prod_right'.measurable)
  mono y c hc v w hvw := add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (integral_mono (G.integrable_cont v _) (G.integrable_cont w _) fun z => BM.le_def.1 hvw _)
    G.β_pos.le)
  bdd v := by
    obtain ⟨C, hC⟩ := G.u_bdd
    refine ⟨C + G.β * ‖v‖, fun y c hc => (abs_add_le _ _).trans (add_le_add (hC c hc.1) ?_)⟩
    rw [abs_mul, abs_of_pos G.β_pos]
    exact mul_le_mul_of_nonneg_left (G.abs_cont_le v y c) G.β_pos.le
  exists_policy := ⟨fun _ => 0, measurable_const, fun y => ⟨le_rfl, le_max_right _ _⟩⟩

theorem isBlackwell : G.brdp.IsBlackwell G.β := fun y c _ v κ _ => by
  change G.u c + G.β * G.cont (fun x => v.toFun x + κ) y c ≤ G.u c + G.β * G.cont v.toFun y c +
    G.β * κ
  rw [G.cont_add_const]
  linarith

theorem hasMaxSelections : HasMaxSelections G.brdp.Γ :=
  hasMaxSelections_Icc (g := fun _ => 0) (h := fun y => max y 0) continuous_const
    (continuous_id.max continuous_const) fun y => le_max_right y 0

/-- **Exercise 8.3.6**, corrected (p. 285): `(y, c) ↦ B(y, c, v)` is continuous on `G` for every
`v ∈ bcX` (dominated convergence; the book's proof uses continuity of `v`). -/
theorem exercise_8_3_6 (v : BM ℝ) (hv : Continuous v.toFun) :
    ContinuousOn (fun p : ℝ × ℝ => G.B p.1 p.2 v.toFun) {p | p.2 ∈ G.brdp.Γ p.1} := by
  have hu : ContinuousOn (fun p : ℝ × ℝ => G.u p.2) {p | p.2 ∈ G.brdp.Γ p.1} :=
    G.u_continuousOn.comp continuousOn_snd fun p hp => mem_Ici.2 hp.1
  have hfk : Continuous fun p : ℝ × ℝ => G.f (max (p.1 - p.2) 0) :=
    G.f_continuousOn.comp_continuous ((continuous_fst.sub continuous_snd).max continuous_const)
      fun p => mem_Ici.2 (le_max_right _ _)
  have hc : Continuous fun p : ℝ × ℝ => G.cont v.toFun p.1 p.2 :=
    continuous_of_dominated (bound := fun _ => ‖v‖)
      (fun p => (v.measurable'.comp (measurable_const.mul measurable_id)).aestronglyMeasurable)
      (fun p => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact BM.abs_le_norm v _)
      (integrable_const _) (Eventually.of_forall fun z => hv.comp (hfk.mul continuous_const))
  exact hu.add (continuous_const.mul hc).continuousOn

/-- `𝟙_(0, ∞)` as an element of `bX`. -/
noncomputable def indPos : BM ℝ :=
  ⟨(Set.Ioi 0).indicator 1, measurable_const.indicator measurableSet_Ioi, ⟨1, fun x => by
    by_cases hx : x ∈ Set.Ioi (0 : ℝ)
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]⟩⟩

theorem cont_indPos_lt {y c : ℝ} (hcy : c < y) : G.cont indPos.toFun y c = 1 := by
  have hf := G.f_pos (lt_max_of_lt_left (sub_pos.2 hcy) : 0 < max (y - c) 0)
  have h : (fun z => indPos.toFun (G.f (max (y - c) 0) * z)) =ᵐ[G.φ] fun _ => (1 : ℝ) :=
    G.shock_pos.mono fun z hz => by
      change (Set.Ioi (0 : ℝ)).indicator 1 (G.f (max (y - c) 0) * z) = 1
      rw [Set.indicator_of_mem (Set.mem_Ioi.2 (mul_pos hf hz))]
      rfl
  unfold cont
  rw [integral_congr_ae h]
  simp

theorem cont_indPos_self (y : ℝ) : G.cont indPos.toFun y y = 0 := by
  unfold cont
  rw [sub_self, max_self, G.f_zero]
  simp only [zero_mul]
  change ∫ _, (Set.Ioi (0 : ℝ)).indicator 1 0 ∂G.φ = 0
  rw [Set.indicator_of_notMem (s := Set.Ioi (0 : ℝ)) (lt_irrefl (0 : ℝ))]
  simp

theorem tendsto_u_left : Tendsto G.u (𝓝[<] 1) (𝓝 (G.u 1)) :=
  ((G.u_continuousOn 1 (mem_Ici.2 zero_le_one)).mono_of_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds zero_lt_one))).tendsto

/-- **Exercise 8.3.6** is false for discontinuous `v ∈ bX`: with `v = 𝟙_(0, ∞)`,
`B(y, c, v) = u(c) + β𝟙{c < y}` jumps at `c = y`. -/
theorem exercise_8_3_6_false :
    ¬ ContinuousOn (fun p : ℝ × ℝ => G.B p.1 p.2 indPos.toFun) {p | p.2 ∈ G.brdp.Γ p.1} := by
  intro hc
  have hp0 : ((1 : ℝ), (1 : ℝ)) ∈ {p : ℝ × ℝ | p.2 ∈ G.brdp.Γ p.1} :=
    ⟨zero_le_one, le_max_left 1 0⟩
  have hpath : Tendsto (fun t : ℝ => ((1 : ℝ), t)) (𝓝[<] 1)
      (𝓝[{p : ℝ × ℝ | p.2 ∈ G.brdp.Γ p.1}] ((1 : ℝ), (1 : ℝ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_const.prodMk continuous_id).tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
      exact ⟨ht.1.le, ht.2.le.trans (le_max_left _ _)⟩
  have hlim := (hc _ hp0).tendsto.comp hpath
  have heq : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      ((fun p : ℝ × ℝ => G.B p.1 p.2 indPos.toFun) ∘ fun t : ℝ => ((1 : ℝ), t)) t =
        G.u t + G.β := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
    simp only [Function.comp_apply, B]
    rw [G.cont_indPos_lt ht.2, mul_one]
  have h2 := tendsto_nhds_unique (hlim.congr' heq) (G.tendsto_u_left.add tendsto_const_nhds)
  simp only [B, G.cont_indPos_self, mul_zero, add_zero] at h2
  linarith [G.β_pos]

/-- With `v = 𝟙_(0, ∞)` no policy is `v`-greedy (`sup_{c < y} u(c) + β = u(y) + β` is not
attained), so the ADP `(bX, 𝕋)` is not regular. -/
theorem not_regular : ¬ G.brdp.toRDP.adp.Regular := by
  intro hreg
  obtain ⟨σ, hσ⟩ := hreg indPos
  have hg := (G.brdp.toRDP.isGreedy_iff indPos σ).1 hσ
  have hτ : ∀ c, 0 ≤ c → G.B 1 (min c (max 1 0)) indPos.toFun ≤ G.B 1 (σ.1 1) indPos.toFun :=
    fun c hc => hg ⟨fun y => min c (max y 0), measurable_const.min (measurable_id.max
      measurable_const), fun y => ⟨le_min hc (le_max_right _ _), min_le_right _ _⟩⟩ 1
  have h10 : max (1 : ℝ) 0 = 1 := max_eq_left zero_le_one
  have ha := σ.2.2 1
  change σ.1 1 ∈ Set.Icc 0 (max 1 0) at ha
  rw [h10] at ha hτ
  rcases ha.2.lt_or_eq with hlt | heq
  · have hc := hτ ((σ.1 1 + 1) / 2) (by linarith [ha.1])
    rw [min_eq_left (by linarith), B, B, G.cont_indPos_lt (by linarith), G.cont_indPos_lt hlt]
      at hc
    have := G.u_strictMonoOn (mem_Ici.2 ha.1) (mem_Ici.2 (by linarith [ha.1]) :
      (σ.1 1 + 1) / 2 ∈ Set.Ici (0 : ℝ)) (by linarith : σ.1 1 < (σ.1 1 + 1) / 2)
    linarith
  · have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), G.u 1 - G.β < G.u t ∧ t ∈ Set.Ioo 0 1 :=
      (G.tendsto_u_left.eventually (lt_mem_nhds (by linarith [G.β_pos]))).and
        (Ioo_mem_nhdsLT zero_lt_one)
    obtain ⟨t, ht1, ht2⟩ := hev.exists
    have hc := hτ t ht2.1.le
    rw [min_eq_left ht2.2.le, heq, B, B, G.cont_indPos_lt ht2.2, G.cont_indPos_self] at hc
    linarith

/-- **Proposition 8.3.7** (p. 285) and **Exercise 8.3.7**: under Assumption 8.3.1, the
fundamental optimality properties hold, `v* ∈ bcX`, and VFI converges geometrically on `bcX`
(Proposition 7.2.2 with Exercise 8.3.6 for `v ∈ bcX`). The ADP is not regular on `bX`
(`not_regular`), so the convergence of OPI and HPI claimed in the book is not covered. -/
theorem proposition_8_3_7 :
    ∃ hw : G.brdp.toRDP.adp.WellPosed, G.brdp.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc ℝ, G.brdp.toRDP.adp.VFIGeometric (LDP.bc ℝ) vstar := by
  obtain ⟨hw, hFO, vstar, hv, hgeo, -⟩ := G.brdp.proposition_7_2_2 G.hasMaxSelections
    G.β_pos.le G.β_lt_one G.isBlackwell fun v hv => G.exercise_8_3_6 v hv
  exact ⟨hw, hFO, vstar, hv, hgeo⟩

/-! ### Properties of the value function (Lemma 8.3.8) -/

/-- The continuous, increasing functions in `bX` that are concave on `ℝ₊`. -/
def ICC : Set (BM ℝ) :=
  {v | Continuous v.toFun ∧ Monotone v.toFun ∧ ConcaveOn ℝ (Set.Ici 0) v.toFun}

theorem isClosed_ICC : IsClosed ICC := by
  refine isSeqClosed_iff_isClosed.1 fun vs v hvs hlim => ?_
  have hu := BM.tendstoUniformly_of_tendsto hlim
  have hpt : ∀ x, Tendsto (fun n => (vs n).toFun x) atTop (𝓝 (v.toFun x)) := fun x =>
    hu.tendsto_at x
  refine ⟨hu.continuous (Frequently.of_forall fun n => (hvs n).1), fun x y hxy =>
    le_of_tendsto_of_tendsto' (hpt x) (hpt y) fun n => (hvs n).2.1 hxy, convex_Ici 0,
    fun x hx y hy a b ha hb hab => ?_⟩
  exact le_of_tendsto_of_tendsto' (((hpt x).const_smul a).add ((hpt y).const_smul b)) (hpt _)
    fun n => (hvs n).2.2.2 hx hy ha hb hab

theorem zero_mem_ICC : (0 : BM ℝ) ∈ ICC :=
  ⟨continuous_const, monotone_const, concaveOn_const 0 (convex_Ici 0)⟩

theorem cont_mono {v : BM ℝ} (hv : Monotone v.toFun) {y y' : ℝ} (hyy : y ≤ y') (c : ℝ) :
    G.cont v.toFun y c ≤ G.cont v.toFun y' c :=
  integral_mono_ae (G.integrable_cont v _) (G.integrable_cont v _) (G.shock_pos.mono fun _ hz =>
    hv (mul_le_mul_of_nonneg_right (G.f_mono (le_max_right _ _)
      (max_le_max (sub_le_sub_right hyy c) le_rfl)) hz.le))

/-- `(y, c) ↦ ∫ v(f(y − c)z) φ(dz)` is concave on `{0 ≤ c ≤ y}` for increasing `v` concave on
`ℝ₊`. -/
theorem cont_concave {v : BM ℝ} (hvm : Monotone v.toFun) (hvc : ConcaveOn ℝ (Set.Ici 0) v.toFun)
    {y₁ c₁ y₂ c₂ a b : ℝ} (h₁ : c₁ ≤ y₁) (h₂ : c₂ ≤ y₂) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    a * G.cont v.toFun y₁ c₁ + b * G.cont v.toFun y₂ c₂ ≤
      G.cont v.toFun (a * y₁ + b * y₂) (a * c₁ + b * c₂) := by
  have hk₁ : max (y₁ - c₁) 0 = y₁ - c₁ := max_eq_left (sub_nonneg.2 h₁)
  have hk₂ : max (y₂ - c₂) 0 = y₂ - c₂ := max_eq_left (sub_nonneg.2 h₂)
  have hkl : max (a * y₁ + b * y₂ - (a * c₁ + b * c₂)) 0 = a * (y₁ - c₁) + b * (y₂ - c₂) := by
    have h0 : 0 ≤ a * y₁ + b * y₂ - (a * c₁ + b * c₂) := by
      nlinarith [mul_nonneg ha (sub_nonneg.2 h₁), mul_nonneg hb (sub_nonneg.2 h₂)]
    rw [max_eq_left h0]
    ring
  unfold cont
  rw [hk₁, hk₂, hkl, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((G.integrable_cont v _).const_mul a) ((G.integrable_cont v _).const_mul b)]
  refine integral_mono_ae (((G.integrable_cont v _).const_mul a).add
    ((G.integrable_cont v _).const_mul b)) (G.integrable_cont v _)
    (G.shock_pos.mono fun z hz => ?_)
  have hf := G.f_concaveOn.2 (mem_Ici.2 (sub_nonneg.2 h₁)) (mem_Ici.2 (sub_nonneg.2 h₂)) ha hb
    hab
  simp only [smul_eq_mul] at hf
  have hp₁ : 0 ≤ G.f (y₁ - c₁) * z := mul_nonneg (G.f_nonneg (sub_nonneg.2 h₁)) hz.le
  have hp₂ : 0 ≤ G.f (y₂ - c₂) * z := mul_nonneg (G.f_nonneg (sub_nonneg.2 h₂)) hz.le
  have hv := hvc.2 (mem_Ici.2 hp₁) (mem_Ici.2 hp₂) ha hb hab
  simp only [smul_eq_mul] at hv
  exact hv.trans (hvm (by nlinarith [mul_le_mul_of_nonneg_right hf hz.le]))

/-- `(y, c) ↦ B(y, c, v)` is concave on `{0 ≤ c ≤ y}` for increasing `v` concave on `ℝ₊`
(Assumption 7.2.9). -/
theorem B_concave {v : BM ℝ} (hvm : Monotone v.toFun) (hvc : ConcaveOn ℝ (Set.Ici 0) v.toFun)
    {y₁ c₁ y₂ c₂ a b : ℝ} (h₁ : c₁ ∈ Set.Icc 0 y₁) (h₂ : c₂ ∈ Set.Icc 0 y₂) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    a * G.B y₁ c₁ v.toFun + b * G.B y₂ c₂ v.toFun ≤
      G.B (a * y₁ + b * y₂) (a * c₁ + b * c₂) v.toFun := by
  have hu := G.u_concaveOn.2 (mem_Ici.2 h₁.1) (mem_Ici.2 h₂.1) ha hb hab
  have hc := G.cont_concave hvm hvc h₁.2 h₂.2 ha hb hab
  simp only [smul_eq_mul] at hu
  unfold B
  nlinarith [mul_le_mul_of_nonneg_left hc G.β_pos.le]

/-- `T` maps the continuous increasing functions concave on `ℝ₊` into themselves
(Propositions 7.2.6 and 7.2.7). -/
theorem bellman_mem_ICC {v : BM ℝ} (hv : v ∈ ICC) : G.brdp.toRDP.adp.bellman v ∈ ICC := by
  obtain ⟨-, -, -, hTc, hgr, -⟩ :=
    G.brdp.toRDP.lemma_7_1_2 G.hasMaxSelections v (G.exercise_8_3_6 v hv.1)
  have hw : ∀ y, IsGreatest ((fun c => G.B y c v.toFun) '' Γ y)
      ((G.brdp.toRDP.adp.bellman v).toFun y) := hgr
  refine ⟨hTc, fun y y' hyy => ?_, convex_Ici 0, fun y₁ hy₁ y₂ hy₂ a b ha hb hab => ?_⟩
  · obtain ⟨⟨c, hc, hcy⟩, -⟩ := hw y
    rw [← hcy]
    refine le_trans ?_ ((hw y').2 ⟨c, ⟨hc.1, hc.2.trans (max_le_max hyy le_rfl)⟩, rfl⟩)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (G.cont_mono hv.2.1 hyy c) G.β_pos.le)
  · obtain ⟨⟨c₁, hc₁, e₁⟩, -⟩ := hw y₁
    obtain ⟨⟨c₂, hc₂, e₂⟩, -⟩ := hw y₂
    rw [Γ, max_eq_left (mem_Ici.1 hy₁)] at hc₁
    rw [Γ, max_eq_left (mem_Ici.1 hy₂)] at hc₂
    simp only [smul_eq_mul]
    rw [← e₁, ← e₂]
    have hmem : a * c₁ + b * c₂ ∈ Γ (a * y₁ + b * y₂) :=
      ⟨by nlinarith [hc₁.1, hc₂.1], le_max_of_le_left (by nlinarith [hc₁.2, hc₂.2])⟩
    exact (G.B_concave hv.2.1 hv.2.2 hc₁ hc₂ ha hb hab).trans ((hw _).2 ⟨_, hmem, rfl⟩)

/-- `c ↦ B(y, c, v)` is strictly concave on `Γ(y)` (Assumption 7.2.10). -/
theorem strictConcaveOn_B {v : BM ℝ} (hv : v ∈ ICC) (y : ℝ) :
    StrictConcaveOn ℝ (G.brdp.Γ y) fun c => G.B y c v.toFun := by
  have hΓ : Γ y ⊆ Set.Ici 0 := fun c hc => hc.1
  refine (G.u_strictConcaveOn.subset hΓ (convex_Icc _ _)).add_concaveOn
    ⟨convex_Icc _ _, fun c₁ hc₁ c₂ hc₂ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases le_or_gt 0 y with hy | hy
  · have hc₁' : c₁ ≤ y := hc₁.2.trans (max_eq_left hy).le
    have hc₂' : c₂ ≤ y := hc₂.2.trans (max_eq_left hy).le
    have h := G.cont_concave hv.2.1 hv.2.2 hc₁' hc₂' ha hb hab
    rw [show a * y + b * y = y by rw [← add_mul, hab, one_mul]] at h
    nlinarith [mul_le_mul_of_nonneg_left h G.β_pos.le]
  · have h₁ : c₁ = 0 := le_antisymm (hc₁.2.trans (max_eq_right hy.le).le) hc₁.1
    have h₂ : c₂ = 0 := le_antisymm (hc₂.2.trans (max_eq_right hy.le).le) hc₂.1
    subst h₁ h₂
    simp only [mul_zero, add_zero]
    rw [← add_mul, hab, one_mul]

/-- **Lemma 8.3.8** (p. 286) and **Exercise 8.3.8**: under Assumption 8.3.1, (i) the value
function `v*` is increasing, concave (on `ℝ₊`) and continuous, and (ii) the optimal policy is
unique; it attains `max_{0 ≤ c ≤ y} B(y, c, v*)` and is continuous. -/
theorem lemma_8_3_8 :
    ∃ hw : G.brdp.toRDP.adp.WellPosed, G.brdp.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar : BM ℝ, G.brdp.toRDP.adp.IsValueFunction vstar ∧ vstar ∈ ICC ∧
      ∃ σ, G.brdp.toRDP.adp.IsOptimal hw σ ∧ (∀ τ, G.brdp.toRDP.adp.IsOptimal hw τ → τ = σ) ∧
        G.brdp.toRDP.IsArgmax vstar σ ∧ Continuous σ.1 := by
  obtain ⟨hw, hFO, vstar, -, hgeo⟩ := G.proposition_8_3_7
  have hv : vstar ∈ ICC := lemma_A_2_6 (fun u hu => hgeo.tendsto hu.1) isClosed_ICC
    (fun v hv => G.bellman_mem_ICC hv) ⟨0, zero_mem_ICC⟩
  have hvf := hgeo.1
  obtain ⟨hiff, ⟨σ₀, hσ₀⟩, -, -, -, hcont⟩ :=
    G.brdp.toRDP.lemma_7_1_2 G.hasMaxSelections vstar (G.exercise_8_3_6 vstar hv.1)
  have hσ := (hiff σ₀).1 hσ₀
  have huniq : ∀ y, ∀ c ∈ G.brdp.Γ y, G.B y (σ₀.1 y) vstar.toFun ≤ G.B y c vstar.toFun →
      c = σ₀.1 y := fun y c hc hle =>
    eq_of_isMax_of_strictConcaveOn (G.strictConcaveOn_B hv y) hc (σ₀.2.2 y)
      (fun c' hc' => (hσ y c' hc').trans hle) (hσ y)
  have hopt : ∀ τ, G.brdp.toRDP.adp.IsOptimal hw τ ↔ G.brdp.toRDP.IsArgmax vstar τ := fun τ => by
    rw [hFO.2.2 τ]
    constructor
    · rintro ⟨w, hw', hg⟩
      rw [hw'.unique hvf] at hg
      exact (hiff τ).1 hg
    · exact fun h => ⟨vstar, hvf, (hiff τ).2 h⟩
  refine ⟨hw, hFO, vstar, hvf, hv, σ₀, (hopt σ₀).2 hσ, fun τ hτ => ?_, hσ,
    hcont (hasContinuousUniqueMax_Icc continuous_const (continuous_id.max continuous_const)
      fun y => le_max_right y 0) σ₀ hσ huniq⟩
  have hτ' := (hopt τ).1 hτ
  exact Subtype.ext (funext fun y => huniq y _ (τ.2.2 y) (hτ' y _ (σ₀.2.2 y)))

theorem exercise_8_3_8 :
    ∃ hw : G.brdp.toRDP.adp.WellPosed, G.brdp.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar : BM ℝ, G.brdp.toRDP.adp.IsValueFunction vstar ∧ vstar ∈ ICC ∧
      ∃ σ, G.brdp.toRDP.adp.IsOptimal hw σ ∧ (∀ τ, G.brdp.toRDP.adp.IsOptimal hw τ → τ = σ) ∧
        G.brdp.toRDP.IsArgmax vstar σ ∧ Continuous σ.1 :=
  G.lemma_8_3_8

/-! ### Envelope theorems (Proposition 8.3.9 and Corollary 8.3.10) -/

/-- A `v`-maximizing policy consumes a positive amount at positive income: `u'(0) = ∞`, while
`c ↦ ∫ v(f(y − c)z) φ(dz)` is concave with a finite slope at `c = 0`. -/
theorem argmax_pos {v : BM ℝ} (hv : v ∈ ICC) {σ : G.brdp.toRDP.Policy}
    (hσ : G.brdp.toRDP.IsArgmax v σ) {y : ℝ} (hy : 0 < y) : 0 < σ.1 y := by
  have hmem := σ.2.2 y
  change σ.1 y ∈ Set.Icc 0 (max y 0) at hmem
  refine lt_of_le_of_ne hmem.1 fun h0 => ?_
  set L := 2 * ‖v‖ / y
  have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), G.β * L < deriv G.u c ∧ c ∈ Set.Ioo 0 y :=
    (G.u_inada.eventually (eventually_gt_atTop _)).and (Ioo_mem_nhdsGT hy)
  obtain ⟨c, hcL, hc⟩ := hev.exists
  have hmax := hσ y c ⟨hc.1.le, hc.2.le.trans (le_max_left _ _)⟩
  change G.B y c v.toFun ≤ G.B y (σ.1 y) v.toFun at hmax
  rw [← h0] at hmax
  -- the chord of the concave map `c ↦ ∫ v(f(y − c)z)` from `0` to `y`
  have hchord := G.cont_concave hv.2.1 hv.2.2 (y₁ := y) (c₁ := y) (y₂ := y) (c₂ := 0) le_rfl
    hy.le (div_nonneg hc.1.le hy.le) (sub_nonneg.2 ((div_le_one hy).2 hc.2.le))
    (by ring)
  rw [show c / y * y + (1 - c / y) * y = y by ring,
    show c / y * y + (1 - c / y) * 0 = c by rw [mul_zero, add_zero, div_mul_cancel₀ c hy.ne']]
    at hchord
  have hb1 := abs_le.1 (G.abs_cont_le v y y)
  have hb2 := abs_le.1 (G.abs_cont_le v y 0)
  -- `u(c) ≥ u'(c)c`
  have hslope := G.u_concaveOn.deriv_le_slope (mem_Ici.2 le_rfl) (mem_Ici.2 hc.1.le) hc.1
    (G.u_differentiableAt c hc.1)
  rw [slope_def_field, G.u_zero, sub_zero, sub_zero, le_div_iff₀ hc.1] at hslope
  have hcy : c / y * (G.cont v.toFun y 0 - G.cont v.toFun y y) ≤ c * L := by
    rw [show c * L = c / y * (2 * ‖v‖) by simp only [L]; ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hc.1.le hy.le)
  unfold B at hmax
  rw [G.u_zero] at hmax
  nlinarith [mul_lt_mul_of_pos_right hcL hc.1, G.β_pos]

/-- **Proposition 8.3.9** (p. 286), corrected. Let `v ∈ bcℝ₊` be increasing and concave and let
`σ` be a `v`-greedy (maximizing) policy. Then `σ(y) > 0` for `y > 0`, `Tv` is concave and strictly
increasing on `ℝ₊`, and `Tv` is differentiable on `(0, ∞)` with `(Tv)' = u' ∘ σ` (8.60), a
continuous function. The claim that `σ` is interior (`σ(y) < y`) is false in general
(`proposition_8_3_9_not_interior`). The derivative is obtained from the concave sandwich
`u(t − (y − σ(y))) + β ∫ v(f(y − σ(y))z) φ(dz) ≤ (Tv)(t)`, with equality at `t = y`. -/
theorem proposition_8_3_9 {v : BM ℝ} (hv : v ∈ ICC) {σ : G.brdp.toRDP.Policy}
    (hσ : G.brdp.toRDP.IsArgmax v σ) :
    (∀ y, 0 < y → 0 < σ.1 y) ∧ ConcaveOn ℝ (Set.Ici 0) (G.brdp.toRDP.adp.bellman v).toFun ∧
      StrictMonoOn (G.brdp.toRDP.adp.bellman v).toFun (Set.Ici 0) ∧
      (∀ y, 0 < y → HasDerivAt (G.brdp.toRDP.adp.bellman v).toFun (deriv G.u (σ.1 y)) y) ∧
      ContinuousOn (fun y => deriv G.u (σ.1 y)) (Set.Ioi 0) := by
  obtain ⟨-, hval, -⟩ := G.brdp.toRDP.bellman_of_isArgmax hσ
  have hval' : ∀ y, (G.brdp.toRDP.adp.bellman v).toFun y = G.B y (σ.1 y) v.toFun := hval
  have hpos : ∀ y, 0 < y → 0 < σ.1 y := fun y hy => G.argmax_pos hv hσ hy
  have hconc := (G.bellman_mem_ICC hv).2.2
  have hle : ∀ y, 0 ≤ y → σ.1 y ≤ y := fun y hy => by
    have : σ.1 y ≤ max y 0 := (σ.2.2 y).2
    rwa [max_eq_left hy] at this
  -- keeping savings `y − σ(y)` fixed is feasible at income `t ≥ y − σ(y)`
  have hkeep : ∀ y t, 0 ≤ y → y - σ.1 y ≤ t →
      G.u (t - (y - σ.1 y)) + G.β * G.cont v.toFun y (σ.1 y) ≤
        (G.brdp.toRDP.adp.bellman v).toFun t := fun y t hy ht => by
    have hc : t - (y - σ.1 y) ∈ G.brdp.Γ t :=
      ⟨by linarith, le_max_of_le_left (by linarith [hle y hy])⟩
    have h := hσ t _ hc
    change G.B t (t - (y - σ.1 y)) v.toFun ≤ G.B t (σ.1 t) v.toFun at h
    rw [hval']
    refine le_trans (le_of_eq ?_) h
    unfold B cont
    rw [sub_sub_cancel]
  refine ⟨hpos, hconc, fun y hy y' hy' hyy => ?_, fun y hy => ?_, ?_⟩
  · have h := hkeep y y' hy (by linarith [(σ.2.2 y).1])
    rw [hval' y]
    refine lt_of_lt_of_le ?_ h
    unfold B
    have := G.u_strictMonoOn (mem_Ici.2 (σ.2.2 y).1)
      (mem_Ici.2 (by linarith [(σ.2.2 y).1, hle y hy] : (0 : ℝ) ≤ y' - (y - σ.1 y)))
      (by linarith : σ.1 y < y' - (y - σ.1 y))
    linarith
  · have hσy := hpos y hy
    have hW : HasDerivAt (fun t => G.u (t - (y - σ.1 y)) + G.β * G.cont v.toFun y (σ.1 y))
        (deriv G.u (σ.1 y)) y := by
      have hd : HasDerivAt G.u (deriv G.u (σ.1 y)) (y - (y - σ.1 y)) := by
        rw [sub_sub_cancel]
        exact (G.u_differentiableAt _ hσy).hasDerivAt
      exact (hd.comp_sub_const y (y - σ.1 y)).add_const _
    refine hasDerivAt_of_concave_sandwich hconc (Ici_mem_nhds hy) ?_ ?_ hW
    · filter_upwards [Ioi_mem_nhds (by linarith : y - σ.1 y < y)] with t ht
      exact hkeep y t hy.le (le_of_lt ht)
    · rw [hval', sub_sub_cancel]
      rfl
  · obtain ⟨-, -, -, -, -, hcont⟩ :=
      G.brdp.toRDP.lemma_7_1_2 G.hasMaxSelections v (G.exercise_8_3_6 v hv.1)
    have huniq : ∀ y, ∀ c ∈ G.brdp.Γ y, G.B y (σ.1 y) v.toFun ≤ G.B y c v.toFun →
        c = σ.1 y := fun y c hc hle' =>
      eq_of_isMax_of_strictConcaveOn (G.strictConcaveOn_B hv y) hc (σ.2.2 y)
        (fun c' hc' => (hσ y c' hc').trans hle') (hσ y)
    have hσc := hcont (hasContinuousUniqueMax_Icc continuous_const
      (continuous_id.max continuous_const) fun y => le_max_right y 0) σ hσ huniq
    exact G.u_deriv_continuousOn.comp hσc.continuousOn fun y hy => hpos y hy

/-- The interiority claim of Proposition 8.3.9 (i) fails: `v = 0` is increasing, concave and
continuous, and its greedy policy consumes everything, `σ(y) = y`. -/
theorem proposition_8_3_9_not_interior {σ : G.brdp.toRDP.Policy}
    (hσ : G.brdp.toRDP.IsArgmax 0 σ) {y : ℝ} (hy : 0 ≤ y) : σ.1 y = y := by
  have hmem := σ.2.2 y
  change σ.1 y ∈ Set.Icc 0 (max y 0) at hmem
  rw [max_eq_left hy] at hmem
  have h := hσ y y ⟨hy, le_max_left _ _⟩
  change G.B y y (fun _ => 0) ≤ G.B y (σ.1 y) (fun _ => 0) at h
  simp only [B, cont, integral_zero, mul_zero, add_zero] at h
  by_contra hne
  have := G.u_strictMonoOn (mem_Ici.2 hmem.1) (mem_Ici.2 hy) (lt_of_le_of_ne hmem.2 hne)
  linarith

/-- **Corollary 8.3.10** (p. 286), the envelope condition: with `σ` the unique optimal policy and
`v*` the value function, `σ(y) > 0` for `y > 0`, `v*` is concave and strictly increasing on `ℝ₊`,
and `v*` is continuously differentiable on `(0, ∞)` with `(v*)' = u' ∘ σ` (8.61). -/
theorem corollary_8_3_10 :
    ∃ hw : G.brdp.toRDP.adp.WellPosed, ∃ vstar : BM ℝ, ∃ σ : G.brdp.toRDP.Policy,
      G.brdp.toRDP.adp.IsValueFunction vstar ∧ G.brdp.toRDP.adp.IsOptimal hw σ ∧
      (∀ τ, G.brdp.toRDP.adp.IsOptimal hw τ → τ = σ) ∧
      (∀ y, 0 < y → 0 < σ.1 y) ∧ ConcaveOn ℝ (Set.Ici 0) vstar.toFun ∧
      StrictMonoOn vstar.toFun (Set.Ici 0) ∧
      (∀ y, 0 < y → HasDerivAt vstar.toFun (deriv G.u (σ.1 y)) y) ∧
      ContinuousOn (fun y => deriv G.u (σ.1 y)) (Set.Ioi 0) := by
  obtain ⟨hw, hFO, vstar, hvf, hv, σ, hopt, huniq, hσ, -⟩ := G.lemma_8_3_8
  obtain ⟨w, hwv, hwG, hws, -⟩ := hFO.2.1
  have hfix : G.brdp.toRDP.adp.bellman vstar = vstar := by
    rw [hvf.unique hwv]
    exact (G.brdp.toRDP.adp.solvesBellman_iff hwG).1 hws
  obtain ⟨h1, h2, h3, h4, h5⟩ := G.proposition_8_3_9 hv hσ
  rw [hfix] at h2 h3 h4
  exact ⟨hw, vstar, σ, hvf, hopt, huniq, h1, h2, h3, h4, h5⟩

/-! ### The Euler equation and the Coleman–Reffett operator -/

/-- `Σ𝒞`: continuous, strictly increasing policies with `0 < σ(y) < y` for `y > 0`. -/
def SigmaC (σ : ℝ → ℝ) : Prop :=
  ContinuousOn σ (Set.Ici 0) ∧ StrictMonoOn σ (Set.Ici 0) ∧ ∀ y, 0 < y → 0 < σ y ∧ σ y < y

/-- The integrand `(u' ∘ σ)(f(y − c)z) f'(y − c) z` of (8.63). -/
noncomputable def eulerIntegrand (σ : ℝ → ℝ) (y c z : ℝ) : ℝ :=
  deriv G.u (σ (G.f (y - c) * z)) * deriv G.f (y - c) * z

/-- `c ∈ (0, y)` solves `u'(c) = β ∫ (u' ∘ σ)(f(y − c)z) f'(y − c) z φ(dz)`, the integral
existing; for the Coleman–Reffett operator, `c = Kσ(y)`. -/
def SolvesEuler (β : ℝ) (σ : ℝ → ℝ) (y c : ℝ) : Prop :=
  c ∈ Set.Ioo 0 y ∧ Integrable (G.eulerIntegrand σ y c) G.φ ∧
    deriv G.u c = β * ∫ z, G.eulerIntegrand σ y c z ∂G.φ

/-- (8.63): `σ` satisfies the Euler equation. -/
def SatisfiesEuler (σ : ℝ → ℝ) : Prop := ∀ y, 0 < y → G.SolvesEuler G.β σ y (σ y)

/-- **Exercise 8.3.9** (p. 287): if `σ` satisfies (8.63) and `c_t = σ(y_t)` with
`y_{t+1} = f(y_t − c_t)ξ_{t+1}` (8.58), then `u'(c_t) = β ∫ g_t(z) φ(dz)` where the integrand at the
realised shock is `g_t(ξ_{t+1}) = u'(c_{t+1}) f'(y_t − c_t) ξ_{t+1}`: this is (8.62) with `𝔼_t`
the expectation over `ξ_{t+1} ~ φ`. -/
theorem exercise_8_3_9 {σ : ℝ → ℝ} (hσ : G.SatisfiesEuler σ) (y ξ : ℕ → ℝ)
    (hy : ∀ t, 0 < y t) (hlaw : ∀ t, y (t + 1) = G.f (y t - σ (y t)) * ξ (t + 1)) (t : ℕ) :
    deriv G.u (σ (y t)) = G.β * ∫ z, G.eulerIntegrand σ (y t) (σ (y t)) z ∂G.φ ∧
      G.eulerIntegrand σ (y t) (σ (y t)) (ξ (t + 1)) =
        deriv G.u (σ (y (t + 1))) * deriv G.f (y t - σ (y t)) * ξ (t + 1) := by
  refine ⟨(hσ _ (hy t)).2.2, ?_⟩
  rw [hlaw]
  rfl

theorem eulerIntegrand_nonneg {σ : ℝ → ℝ} (hσ : ∀ x, 0 < x → 0 < σ x) {y c z : ℝ}
    (hc : c ∈ Set.Ioo 0 y) (hz : 0 < z) : 0 ≤ G.eulerIntegrand σ y c z := by
  have hk : 0 < y - c := sub_pos.2 hc.2
  exact mul_nonneg (mul_nonneg (G.deriv_u_nonneg (hσ _ (mul_pos (G.f_pos hk) hz)))
    (G.deriv_f_nonneg hk)) hz.le

/-- The integrand of (8.63) increases with consumption `c` (savings and hence next income
fall). -/
theorem eulerIntegrand_mono {σ : ℝ → ℝ} (hσm : MonotoneOn σ (Set.Ici 0))
    (hσ : ∀ x, 0 < x → 0 < σ x) {y c₁ c₂ z : ℝ} (hc₂ : c₂ ∈ Set.Ioo 0 y)
    (h12 : c₁ ≤ c₂) (hz : 0 < z) : G.eulerIntegrand σ y c₁ z ≤ G.eulerIntegrand σ y c₂ z := by
  have hk₂ : 0 < y - c₂ := sub_pos.2 hc₂.2
  have hk : y - c₂ ≤ y - c₁ := by linarith
  have hx₂ : 0 < G.f (y - c₂) * z := mul_pos (G.f_pos hk₂) hz
  have hx : G.f (y - c₂) * z ≤ G.f (y - c₁) * z :=
    mul_le_mul_of_nonneg_right (G.f_mono hk₂.le hk) hz.le
  have hs : σ (G.f (y - c₂) * z) ≤ σ (G.f (y - c₁) * z) :=
    hσm (mem_Ici.2 hx₂.le) (mem_Ici.2 (hx₂.le.trans hx)) hx
  have hu : deriv G.u (σ (G.f (y - c₁) * z)) ≤ deriv G.u (σ (G.f (y - c₂) * z)) :=
    G.deriv_u_strictAntiOn.antitoneOn (hσ _ hx₂) (hσ _ (hx₂.trans_le hx)) hs
  have hf : deriv G.f (y - c₁) ≤ deriv G.f (y - c₂) :=
    G.deriv_f_antitoneOn hk₂ (hk₂.trans_le hk) hk
  unfold eulerIntegrand
  exact mul_le_mul_of_nonneg_right (mul_le_mul hu hf (G.deriv_f_nonneg (hk₂.trans_le hk))
    (G.deriv_u_nonneg (hσ _ hx₂))) hz.le

/-- **Exercise 8.3.10** (p. 288): the Coleman–Reffett operator is order preserving on `Σ𝒞`: if
`σ_a ≤ σ_b` and `c_a = Kσ_a(y)`, `c_b = Kσ_b(y)` solve the Euler equation at `y`, then
`c_a ≤ c_b`. -/
theorem exercise_8_3_10 {σa σb : ℝ → ℝ} (ha : SigmaC σa) (hb : SigmaC σb)
    (hab : ∀ x, 0 < x → σa x ≤ σb x) {y ca cb : ℝ} (hca : G.SolvesEuler G.β σa y ca)
    (hcb : G.SolvesEuler G.β σb y cb) : ca ≤ cb := by
  by_contra h
  have hlt := not_le.1 h
  have hpa : ∀ x, 0 < x → 0 < σa x := fun x hx => (ha.2.2 x hx).1
  have hpb : ∀ x, 0 < x → 0 < σb x := fun x hx => (hb.2.2 x hx).1
  have hI : ∫ z, G.eulerIntegrand σb y cb z ∂G.φ ≤ ∫ z, G.eulerIntegrand σa y ca z ∂G.φ :=
    integral_mono_ae hcb.2.1 hca.2.1 (G.shock_pos.mono fun z hz => by
      refine (G.eulerIntegrand_mono hb.2.1.monotoneOn hpb hca.1 hlt.le hz).trans ?_
      have hk : 0 < y - ca := sub_pos.2 hca.1.2
      have hx : 0 < G.f (y - ca) * z := mul_pos (G.f_pos hk) hz
      unfold eulerIntegrand
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (G.deriv_u_strictAntiOn.antitoneOn (hpa _ hx) (hpb _ hx) (hab _ hx))
        (G.deriv_f_nonneg hk)) hz.le)
  have hu := G.deriv_u_strictAntiOn hcb.1.1 hca.1.1 hlt
  rw [hca.2.2, hcb.2.2] at hu
  nlinarith [mul_le_mul_of_nonneg_left hI G.β_pos.le]

/-- The Euler equation at `y` has at most one solution `c ∈ (0, y)`: `K` is well defined where a
solution exists. -/
theorem solvesEuler_unique {σ : ℝ → ℝ} (hσ : SigmaC σ) {y c₁ c₂ : ℝ}
    (h₁ : G.SolvesEuler G.β σ y c₁) (h₂ : G.SolvesEuler G.β σ y c₂) : c₁ = c₂ :=
  le_antisymm (G.exercise_8_3_10 hσ hσ (fun _ _ => le_rfl) h₁ h₂)
    (G.exercise_8_3_10 hσ hσ (fun _ _ => le_rfl) h₂ h₁)

/-- The comparison step of **Exercise 8.3.12** (p. 293): for `β_a ≤ β_b`, `K_b σ ≤ K_a σ`. (The
conclusion `σ_b ≤ σ_a` also needs the global stability of `K` from Proposition 8.3.13.) -/
theorem exercise_8_3_12_step {σ : ℝ → ℝ} (hσ : SigmaC σ) {βa βb : ℝ} (hβa : 0 < βa)
    (hβ : βa ≤ βb) {y ca cb : ℝ} (hca : G.SolvesEuler βa σ y ca)
    (hcb : G.SolvesEuler βb σ y cb) : cb ≤ ca := by
  by_contra h
  have hlt := not_le.1 h
  have hp : ∀ x, 0 < x → 0 < σ x := fun x hx => (hσ.2.2 x hx).1
  have hI : ∫ z, G.eulerIntegrand σ y ca z ∂G.φ ≤ ∫ z, G.eulerIntegrand σ y cb z ∂G.φ :=
    integral_mono_ae hca.2.1 hcb.2.1 (G.shock_pos.mono fun z hz =>
      G.eulerIntegrand_mono hσ.2.1.monotoneOn hp hcb.1 hlt.le hz)
  have h0 : 0 ≤ ∫ z, G.eulerIntegrand σ y ca z ∂G.φ :=
    integral_nonneg_of_ae (G.shock_pos.mono fun z hz => G.eulerIntegrand_nonneg hp hca.1 hz)
  have hu := G.deriv_u_strictAntiOn hca.1.1 hcb.1.1 hlt
  rw [hca.2.2, hcb.2.2] at hu
  nlinarith [mul_le_mul_of_nonneg_right hβ h0, mul_le_mul_of_nonneg_left hI (hβa.le.trans hβ)]

end Growth

end SargentStachurski.AdditionalApplications
