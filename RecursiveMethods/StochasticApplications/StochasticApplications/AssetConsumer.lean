/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.AssetPricing

/-!
# Asset prices: the consumer's problem

SLP §10.6, Exercise 10.6a–d, pp. 300–303. A consumer holds `x ∈ X = [0, x̄]ᵏ` shares (`x̄ > 1`);
in state `z` asset `i` pays the dividend `dᵢ(z) > 0` and sells at `pᵢ(z) > 0` (`p` continuous);
consumption is `c = d(z)·x + p(z)·(x − y)` for end-of-period holdings `y`. In the first
formulation of Chapter 9, `Γ(x, z) = {y ∈ X : p(z)·y ≤ [d(z) + p(z)]·x}` and `F(x, y, z) = U(c)`.

* **Exercise 10.6a–b** (`asset_boundedDP`, `ex_10_6ab`): the hypotheses of §9.2 hold, so the
  functional equation has a unique bounded continuous solution `vᵖ`, which is the supremum
  function `v*`. `vᵖ(·, z)` is strictly increasing and concave; `Gᵖ` is nonempty,
  compact-valued, u.h.c. and convex-valued; and any two optimal portfolios cost the same
  (`p(z)·y = p(z)·y′`, by strict concavity of `U`). `vᵖ` is only weakly concave because `c` is
  linear in `(x, y)`; portfolios of equal cost and equal continuation value tie.
* **Exercise 10.6c** (`ex_10_6c_deriv`, `ex_10_6c_euler`): at an interior `x` with an optimal
  `y` leaving positive consumption, `vᵖᵢ(x, z) = U′(c)[dᵢ(z) + pᵢ(z)]` (1). If moreover `y` is
  interior and each `vᵖ(·, z′)` has partial derivative `vᵖᵢ(y, z′)`, then
  `U′(c) pᵢ(z) = β ∫ vᵖᵢ(y, z′) Q(z, dz′)` (2). The integral is differentiated under the integral
  sign, using that a concave bounded function is Lipschitz inside its domain.
* **Exercise 10.6d** (`ex_10_6d`): if holding one share of each asset is optimal in every state
  (equilibrium), then (3) `vᵢ(1, z) = U′(z·1)[zᵢ + pᵢ(z)]` and (4)–(5)
  `U′(z·1)pᵢ(z) = β ∫ U′(z′·1)[z′ᵢ + pᵢ(z′)] Q(z, dz′)`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction Metric

/-- The portfolios `X = [0, x̄]ᵏ`. -/
def assetX (k : ℕ) (xbar : ℝ) : Set (Fin k → ℝ) := Set.pi univ fun _ => Icc 0 xbar

/-- The inner product `a·b`. -/
def dotR {k : ℕ} (a b : Fin k → ℝ) : ℝ := ∑ i, a i * b i

/-- `x ↦ a·x` as a continuous linear functional. -/
noncomputable def dotCLM {k : ℕ} (a : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • ContinuousLinearMap.proj i

variable {k : ℕ} {xbar : ℝ}

theorem dotCLM_apply (a x : Fin k → ℝ) : dotCLM a x = dotR a x := by
  simp [dotCLM, dotR]

theorem continuous_dotR : Continuous fun q : (Fin k → ℝ) × (Fin k → ℝ) => dotR q.1 q.2 :=
  continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)

theorem dotR_cmb (a x x' : Fin k → ℝ) (θ : ℝ) :
    dotR a (θ • x + (1 - θ) • x') = θ * dotR a x + (1 - θ) * dotR a x' := by
  simp only [dotR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dotR_nonneg {a x : Fin k → ℝ} (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ dotR a x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hx i)

theorem dotR_le {a x x' : Fin k → ℝ} (ha : ∀ i, 0 ≤ a i) (h : x ≤ x') : dotR a x ≤ dotR a x' :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (ha i)

theorem dotR_lt {a x x' : Fin k → ℝ} (ha : ∀ i, 0 < a i) (h : x < x') : dotR a x < dotR a x' := by
  obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.1 h
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  exact Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (ha j).le)
    ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left (lt_of_le_of_ne (hle i) hi) (ha i)⟩

theorem mem_assetX {x : Fin k → ℝ} : x ∈ assetX k xbar ↔ ∀ i, 0 ≤ x i ∧ x i ≤ xbar := by
  simp only [assetX, Set.mem_univ_pi, mem_Icc]

theorem convex_assetX : Convex ℝ (assetX k xbar) := convex_pi fun _ _ => convex_Icc 0 xbar

theorem isCompact_assetX : IsCompact (assetX k xbar) := isCompact_univ_pi fun _ => isCompact_Icc

/-- The budget correspondence `s ↦ {y ∈ X : q(s)·y ≤ b(s)}`, for continuous `q > 0` and
`b ≥ 0`, is l.h.c.: scale `y` by `min{1, b(sₙ)/q(sₙ)·y}`. -/
theorem isLHC_budget {S : Type*} [MetricSpace S] {q : S → Fin k → ℝ} {b : S → ℝ}
    (hq : Continuous q) (hqpos : ∀ s i, 0 < q s i) (hb : Continuous b) (hb0 : ∀ s, 0 ≤ b s)
    (hx : 0 ≤ xbar) (s : S) :
    IsLHC (fun s => {y : assetX k xbar | dotR (q s) y.1 ≤ b s}) s := by
  have h0 : (0 : Fin k → ℝ) ∈ assetX k xbar := mem_assetX.2 fun _ => ⟨le_rfl, hx⟩
  have hd0 : ∀ s, dotR (q s) (0 : Fin k → ℝ) = 0 := fun _ => by simp [dotR]
  refine ⟨⟨⟨0, h0⟩, by simp only [mem_ofPred_eq, hd0]; exact hb0 s⟩, fun y hy xs hxs => ?_⟩
  have hy' : dotR (q s) y.1 ≤ b s := hy
  have hynn : ∀ i, 0 ≤ y.1 i := fun i => (mem_assetX.1 y.2 i).1
  set σ : ℕ → ℝ := fun n => dotR (q (xs n)) y.1
  have hσ0 : ∀ n, 0 ≤ σ n := fun n => dotR_nonneg (fun i => (hqpos _ i).le) hynn
  rcases (dotR_nonneg (fun i => (hqpos s i).le) hynn).lt_or_eq with hpos | hzero
  · set t : ℕ → ℝ := fun n => min 1 (b (xs n) / σ n)
    have ht0 : ∀ n, 0 ≤ t n := fun n => le_min zero_le_one (div_nonneg (hb0 _) (hσ0 n))
    have ht1 : ∀ n, t n ≤ 1 := fun n => min_le_left _ _
    have hmem : ∀ n, t n • y.1 ∈ assetX k xbar := fun n => mem_assetX.2 fun i => by
      have := mem_assetX.1 y.2 i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact ⟨mul_nonneg (ht0 n) this.1, by nlinarith [ht0 n, ht1 n]⟩
    refine ⟨0, fun n => ⟨t n • y.1, hmem n⟩, fun n _ => ?_, ?_⟩
    · change dotR (q (xs n)) (t n • y.1) ≤ b (xs n)
      have e : dotR (q (xs n)) (t n • y.1) = t n * σ n := by
        simp only [dotR, Pi.smul_apply, smul_eq_mul, σ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      rcases (hσ0 n).lt_or_eq with hσ | hσ
      · have := mul_le_mul_of_nonneg_right (min_le_right 1 (b (xs n) / σ n)) hσ.le
        rwa [div_mul_cancel₀ _ hσ.ne'] at this
      · rw [← hσ, mul_zero]; exact hb0 _
    · have hσl : Tendsto σ atTop (𝓝 (dotR (q s) y.1)) :=
        (continuous_dotR.comp (hq.prodMk continuous_const)).tendsto s |>.comp hxs
      have htl : Tendsto t atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).min
          (((hb.tendsto s).comp hxs).div hσl hpos.ne')
        rwa [min_eq_left ((one_le_div hpos).2 hy')] at this
      refine tendsto_subtype_rng.2 ?_
      simpa using htl.smul_const y.1
  · -- `q(s)·y = 0` forces `y = 0`
    have hy0 : y.1 = 0 := by
      funext i
      have hs := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hqpos s j).le (hynn j))
        |>.1 hzero.symm i (Finset.mem_univ _)
      exact (mul_eq_zero.1 hs).resolve_left (hqpos s i).ne'
    refine ⟨0, fun _ => y, fun n _ => ?_, tendsto_const_nhds⟩
    change dotR (q (xs n)) y.1 ≤ b (xs n)
    rw [hy0, hd0]
    exact hb0 _

/-- The budget correspondence is u.h.c. -/
theorem isUHC_budget {S : Type*} [MetricSpace S] {q : S → Fin k → ℝ} {b : S → ℝ}
    (hq : Continuous q) (hb : Continuous b) (hb0 : ∀ s, 0 ≤ b s) (hx : 0 ≤ xbar) (s : S) :
    IsUHC (fun s => {y : assetX k xbar | dotR (q s) y.1 ≤ b s}) s := by
  have : CompactSpace (assetX k xbar) := isCompact_iff_compactSpace.1 isCompact_assetX
  have h0 : (0 : Fin k → ℝ) ∈ assetX k xbar := mem_assetX.2 fun _ => ⟨le_rfl, hx⟩
  refine ⟨⟨⟨0, h0⟩, by simp [dotR, hb0 s]⟩, fun xs hxs ys hys => ?_⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
  refine ⟨y, ?_, φ, hφ, hlim⟩
  have hc : Continuous fun p : S × assetX k xbar => dotR (q p.1) p.2.1 :=
    continuous_dotR.comp ((hq.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  exact le_of_tendsto_of_tendsto ((hc.tendsto (s, y)).comp
    ((hxs.comp hφ.tendsto_atTop).prodMk_nhds hlim))
    ((hb.tendsto s).comp (hxs.comp hφ.tendsto_atTop)) (Eventually.of_forall fun n => hys (φ n))

variable {Z : Type*} [MetricSpace Z]

/-- The hypotheses of SLP §10.6: `U` continuous, strictly increasing and strictly concave on
`[0, ∞)`; `0 < β < 1`; `x̄ > 1`; dividends and prices continuous and positive. -/
structure AssetHyp (U : ℝ → ℝ) (d p : Z → Fin k → ℝ) (β xbar : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  xbar_gt : 1 < xbar
  U_cont : ContinuousOn U (Ici 0)
  U_mono : StrictMonoOn U (Ici 0)
  U_conc : StrictConcaveOn ℝ (Ici 0) U
  d_cont : Continuous d
  d_pos : ∀ z i, 0 < d z i
  p_cont : Continuous p
  p_pos : ∀ z i, 0 < p z i

variable [MeasurableSpace Z] {U : ℝ → ℝ} {d p : Z → Fin k → ℝ} {β : ℝ}

/-- `Γ(x, z) = {y ∈ X : p(z)·y ≤ [d(z) + p(z)]·x}`. -/
def assetΓ (d p : Z → Fin k → ℝ) (xbar : ℝ) (s : assetX k xbar × Z) : Set (assetX k xbar) :=
  {y | dotR (p s.2) y.1 ≤ dotR (d s.2 + p s.2) s.1.1}

/-- Consumption `c = [d(z) + p(z)]·x − p(z)·y`. -/
def assetC (d p : Z → Fin k → ℝ) (x y : Fin k → ℝ) (z : Z) : ℝ :=
  dotR (d z + p z) x - dotR (p z) y

/-- `F(x, y, z) = U(c)`, with consumption clamped at `0` off the graph. -/
def assetF (U : ℝ → ℝ) (d p : Z → Fin k → ℝ) (xbar : ℝ)
    (q : assetX k xbar × assetX k xbar × Z) : ℝ :=
  U (max (assetC d p q.1.1 q.2.1.1 q.2.2) 0)

/-- The consumer's problem in the first formulation of Chapter 9. -/
abbrev assetModel (Q : Kernel Z Z) (U : ℝ → ℝ) (d p : Z → Fin k → ℝ) (β xbar : ℝ) :
    Model (assetX k xbar) (assetX k xbar) Z :=
  Model.first Q (assetΓ d p xbar) (assetF U d p xbar) β

omit [MetricSpace Z] [MeasurableSpace Z] in
theorem assetF_of_mem {x y : assetX k xbar} {z : Z} (hy : y ∈ assetΓ d p xbar (x, z)) :
    assetF U d p xbar (x, y, z) = U (assetC d p x.1 y.1 z) := by
  have : 0 ≤ assetC d p x.1 y.1 z := sub_nonneg.2 hy
  simp only [assetF, max_eq_left this]

omit [MeasurableSpace Z] in
theorem AssetHyp.continuous_F (h : AssetHyp U d p β xbar) :
    Continuous (assetF U d p xbar) := by
  have hc : Continuous fun q : assetX k xbar × assetX k xbar × Z =>
      assetC d p q.1.1 q.2.1.1 q.2.2 :=
    (continuous_dotR.comp (((h.d_cont.add h.p_cont).comp continuous_snd.snd).prodMk
      (continuous_subtype_val.comp continuous_fst))).sub
    (continuous_dotR.comp ((h.p_cont.comp continuous_snd.snd).prodMk
      (continuous_subtype_val.comp continuous_snd.fst)))
  exact h.U_cont.comp_continuous (hc.max continuous_const) fun _ => mem_Ici.2 (le_max_right _ _)

/-- The hypotheses of §9.2 hold for the consumer's problem, for any Feller `Q` on a compact `Z`
(Exercise 10.6b). -/
theorem asset_boundedDP [CompactSpace Z] [OpensMeasurableSpace Z] (h : AssetHyp U d p β xbar)
    (Q : Kernel Z Z)
    [IsMarkovKernel Q] (hQ : IsFeller Q) : BoundedDP (assetModel Q U d p β xbar) := by
  have : CompactSpace (assetX k xbar) := isCompact_iff_compactSpace.1 isCompact_assetX
  have hb : Continuous fun s : assetX k xbar × Z => dotR (d s.2 + p s.2) s.1.1 :=
    continuous_dotR.comp (((h.d_cont.add h.p_cont).comp continuous_snd).prodMk
      (continuous_subtype_val.comp continuous_fst))
  have hb0 : ∀ s : assetX k xbar × Z, 0 ≤ dotR (d s.2 + p s.2) s.1.1 := fun s =>
    dotR_nonneg (fun i => (add_pos (h.d_pos _ i) (h.p_pos _ i)).le)
      fun i => (mem_assetX.1 s.1.2 i).1
  have hx : 0 ≤ xbar := by linarith [h.xbar_gt]
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn h.continuous_F.continuousOn
  have hcl : ∀ s : assetX k xbar × Z, IsClosed (assetΓ d p xbar s) := fun s =>
    isClosed_le (continuous_dotR.comp (continuous_const.prodMk continuous_subtype_val))
      continuous_const
  have hq : Continuous fun s : assetX k xbar × Z => p s.2 := h.p_cont.comp continuous_snd
  have hl := isLHC_budget hq (fun s => h.p_pos s.2) hb hb0 hx
  exact ⟨fun s => (hl s).1, fun s => (hcl s).isCompact, hl, isUHC_budget hq hb hb0 hx,
    h.continuous_F.continuousOn,
    ⟨B, fun q _ => by simpa [Real.norm_eq_abs] using hB q (mem_univ _)⟩, h.β_pos, h.β_lt,
    continuous_fst.snd.continuousOn, contExp_first Q _ _ β (lemma_9_5_compact Q hQ)⟩

omit [MeasurableSpace Z] in
/-- The graph of `Γ(·, z)` is convex and `F(·, ·, z)` is concave on it. -/
theorem asset_cmb (h : AssetHyp U d p β xbar) {x x' y y' : assetX k xbar} {z : Z}
    (hy : y ∈ assetΓ d p xbar (x, z)) (hy' : y' ∈ assetΓ d p xbar (x', z)) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    cmb convex_assetX h0 h1 y y' ∈ assetΓ d p xbar (cmb convex_assetX h0 h1 x x', z) ∧
      assetC d p (cmb convex_assetX h0 h1 x x').1 (cmb convex_assetX h0 h1 y y').1 z =
        θ * assetC d p x.1 y.1 z + (1 - θ) * assetC d p x'.1 y'.1 z ∧
      θ * assetF U d p xbar (x, y, z) + (1 - θ) * assetF U d p xbar (x', y', z) ≤
        assetF U d p xbar (cmb convex_assetX h0 h1 x x', cmb convex_assetX h0 h1 y y', z) := by
  have hc : assetC d p (cmb convex_assetX h0 h1 x x').1 (cmb convex_assetX h0 h1 y y').1 z =
      θ * assetC d p x.1 y.1 z + (1 - θ) * assetC d p x'.1 y'.1 z := by
    simp only [assetC, cmb, dotR_cmb]; ring
  have e0 : 0 ≤ assetC d p x.1 y.1 z := sub_nonneg.2 hy
  have e1 : 0 ≤ assetC d p x'.1 y'.1 z := sub_nonneg.2 hy'
  have hθ1 : 0 ≤ 1 - θ := by linarith
  have hmem : cmb convex_assetX h0 h1 y y' ∈
      assetΓ d p xbar (cmb convex_assetX h0 h1 x x', z) := by
    have hpos : 0 ≤ assetC d p (cmb convex_assetX h0 h1 x x').1
        (cmb convex_assetX h0 h1 y y').1 z := by
      rw [hc]; positivity
    exact sub_nonneg.1 hpos
  refine ⟨hmem, hc, ?_⟩
  rw [assetF_of_mem hy, assetF_of_mem hy', assetF_of_mem hmem, hc]
  have := h.U_conc.concaveOn.2 e0 e1 h0 hθ1 (by ring)
  simpa only [smul_eq_mul] using this

variable [CompactSpace Z] [OpensMeasurableSpace Z]

/-- The rhs of the functional equation at a feasible `y` is at most `v`, with equality on `G`. -/
theorem asset_rhs_le (h : AssetHyp U d p β xbar) {Q : Kernel Z Z} [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : assetX k xbar × Z →ᵇ ℝ}
    (hv : bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v)
    {s : assetX k xbar × Z} {y : assetX k xbar} (hy : y ∈ assetΓ d p xbar s) :
    rhs (assetModel Q U d p β xbar) v s y ≤ v s := by
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax _ (asset_boundedDP h Q hQ) v s
  have := hmax y hy
  rwa [hv] at this

/-- `v(·, z)` is concave: `T` maps functions concave in `x` into themselves. -/
theorem asset_concave (h : AssetHyp U d p β xbar) {Q : Kernel Z Z} [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : assetX k xbar × Z →ᵇ ℝ}
    (hv : bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v) :
    ∀ z, IsConcaveS convex_assetX fun x => v (x, z) := by
  set M := assetModel Q U d p β xbar
  have hb := asset_boundedDP h Q hQ
  have hmaps : ∀ w : assetX k xbar × Z →ᵇ ℝ, (∀ z, IsConcaveS convex_assetX fun x => w (x, z)) →
      ∀ z, IsConcaveS convex_assetX fun x => bellman M hb w (x, z) := by
    intro w hw z x₀ x₁ θ h0 h1
    obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax M hb w (x₀, z)
    obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax M hb w (x₁, z)
    obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb w (cmb convex_assetX h0 h1 x₀ x₁, z)
    obtain ⟨hyθ, -, hF⟩ := asset_cmb h hy₀ hy₁ h0 h1
    have hE := expV_comb M hb (hX := convex_assetX) (hY := convex_assetX)
      (fun _ _ _ _ _ _ _ _ => rfl) hw hy₀ hy₁ h0 h1 hyθ
    have hm := hmax _ hyθ
    have hβE := mul_le_mul_of_nonneg_left hE h.β_pos.le
    simp only [rhs] at hv₀ hv₁ hm
    dsimp only
    rw [hv₀, hv₁]
    change _ ≤ M.β * _ at hβE
    change θ * (assetF U d p xbar (x₀, y₀, z) + M.β * _) +
      (1 - θ) * (assetF U d p xbar (x₁, y₁, z) + M.β * _) ≤ _
    linarith
  exact (corollary_1 (S' := {w : assetX k xbar × Z →ᵇ ℝ | ∀ z,
      IsConcaveS convex_assetX fun x => w (x, z)})
    (S'' := {w : assetX k xbar × Z →ᵇ ℝ | ∀ z, IsConcaveS convex_assetX fun x => w (x, z)})
    (bellman_contraction M hb) hv ⟨0, fun _ _ _ _ _ _ => by simp⟩ (isClosed_concaveX _)
    hmaps hmaps).1

/-- **Exercise 10.6a–b.** There is a unique bounded continuous `vᵖ` solving the functional
equation; it is the supremum function `v*`; `vᵖ(·, z)` is strictly increasing and concave;
`Gᵖ` is nonempty, compact-valued, u.h.c. and convex-valued; and all optimal portfolios have the
same cost `p(z)·y`. -/
theorem ex_10_6ab [BorelSpace Z] [SecondCountableTopology Z] (h : AssetHyp U d p β xbar)
    (Q : Kernel Z Z) [IsMarkovKernel Q] (hQ : IsFeller Q) :
    ∃ v : assetX k xbar × Z →ᵇ ℝ,
      bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v ∧
      (∀ w, bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) w = w → w = v) ∧
      (∀ s, vStar (assetModel Q U d p β xbar) s = v s) ∧
      (∀ z, StrictMono fun x => v (x, z)) ∧
      (∀ z, IsConcaveS convex_assetX fun x => v (x, z)) ∧
      (∀ s, (policy (assetModel Q U d p β xbar) v s).Nonempty ∧
        IsCompact (policy (assetModel Q U d p β xbar) v s) ∧
        IsUHC (policy (assetModel Q U d p β xbar) v) s) ∧
      (∀ s, Convex ℝ (Subtype.val '' policy (assetModel Q U d p β xbar) v s)) ∧
      ∀ s y y', y ∈ policy (assetModel Q U d p β xbar) v s →
        y' ∈ policy (assetModel Q U d p β xbar) v s → dotR (p s.2) y.1 = dotR (p s.2) y'.1 := by
  set M := assetModel Q U d p β xbar
  have hb := asset_boundedDP h Q hQ
  obtain ⟨v, hv, huniq, -, hG⟩ := ex_9_7b M hb
  have hvc := asset_concave h hQ hv
  -- `v = v*`, through a measurable selection from `G`
  obtain ⟨g, hgm, hgG⟩ := exists_measurableSelection (fun s => (hG s).2.2) fun s => (hG s).2.1
  have hopt := fun s₀ => bounded_vStar M hb measurable_snd.fst h.continuous_F.measurable hv
    (g := fun _ => g) (fun _ => hgm) (fun _ => hgG) s₀
  -- the objective at a mixture of two optimal portfolios
  have hmix : ∀ (s : assetX k xbar × Z) (y y' : assetX k xbar), y ∈ policy M v s →
      y' ∈ policy M v s → ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
        cmb convex_assetX h0 h1 y y' ∈ assetΓ d p xbar s ∧
        θ * U (assetC d p s.1.1 y.1 s.2) + (1 - θ) * U (assetC d p s.1.1 y'.1 s.2) +
          β * (θ * expV M v s y + (1 - θ) * expV M v s y') ≤
          rhs M v s (cmb convex_assetX h0 h1 y y') := by
    rintro ⟨x, z⟩ y y' hy hy' θ h0 h1
    obtain ⟨hyθ, -, hF⟩ := asset_cmb h hy.1 hy'.1 h0 h1
    rw [cmb_self] at hyθ hF
    have hE := expV_comb M hb (hX := convex_assetX) (hY := convex_assetX)
      (fun _ _ _ _ _ _ _ _ => rfl) hvc hy.1 hy'.1 h0 h1 (by rw [cmb_self]; exact hyθ)
    rw [cmb_self] at hE
    refine ⟨hyθ, ?_⟩
    rw [assetF_of_mem hy.1, assetF_of_mem hy'.1] at hF
    simp only [rhs]
    change _ ≤ assetF U d p xbar (x, cmb convex_assetX h0 h1 y y', z) + β * _
    nlinarith [mul_le_mul_of_nonneg_left hE h.β_pos.le]
  have hval : ∀ (s : assetX k xbar × Z) y, y ∈ policy M v s →
      v s = U (assetC d p s.1.1 y.1 s.2) + β * expV M v s y := by
    rintro ⟨x, z⟩ y hy
    have := hy.2
    simp only [rhs] at this
    rw [this]
    change assetF U d p xbar (x, y, z) + β * _ = _
    rw [assetF_of_mem hy.1]
  refine ⟨v, hv, huniq, fun s => (hopt s).2.2, fun z => ?_, hvc, hG, fun s => ?_,
    fun s y y' hy hy' => ?_⟩
  · -- strict monotonicity (Theorem 9.7)
    refine theorem_9_7 Q _ _ β hb (fun x x' y z hxx' hy => ?_) (fun x x' z hxx' y hy => ?_) hv z
    · have hlt : dotR (d z + p z) x.1 < dotR (d z + p z) x'.1 :=
        dotR_lt (fun i => add_pos (h.d_pos z i) (h.p_pos z i)) hxx'
      have hy' : y ∈ assetΓ d p xbar (x', z) := (show _ ≤ _ from hy).trans hlt.le
      rw [assetF_of_mem hy, assetF_of_mem hy']
      exact h.U_mono (mem_Ici.2 (sub_nonneg.2 hy)) (mem_Ici.2 (sub_nonneg.2 hy'))
        (by unfold assetC; linarith)
    · exact (show _ ≤ _ from hy).trans
        (dotR_le (fun i => (add_pos (h.d_pos z i) (h.p_pos z i)).le) hxx')
  · -- `G` is convex-valued
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ a b ha hb' hab
    obtain rfl : b = 1 - a := by linarith
    obtain ⟨hmem, hle⟩ := hmix s y y' hy hy' a ha (by linarith)
    refine ⟨cmb convex_assetX ha (by linarith) y y', ⟨hmem, le_antisymm ?_ ?_⟩, rfl⟩
    · have e1 := congrArg (fun t => a * t) (hval s y hy)
      have e2 := congrArg (fun t => (1 - a) * t) (hval s y' hy')
      linarith
    · exact asset_rhs_le h hQ hv hmem
  · -- equal cost, by strict concavity of `U`
    by_contra hne
    have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have h1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
    obtain ⟨hmem, hle⟩ := hmix s y y' hy hy' (1 / 2) h0 h1
    have hc : assetC d p s.1.1 y.1 s.2 ≠ assetC d p s.1.1 y'.1 s.2 := fun he => by
      apply hne; unfold assetC at he; linarith
    have hU := h.U_conc.2 (mem_Ici.2 (sub_nonneg.2 hy.1)) (mem_Ici.2 (sub_nonneg.2 hy'.1)) hc
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hcm : assetC d p s.1.1 (cmb convex_assetX h0 h1 y y').1 s.2 =
        1 / 2 * assetC d p s.1.1 y.1 s.2 + 1 / 2 * assetC d p s.1.1 y'.1 s.2 := by
      have := (asset_cmb h (z := s.2) (x := s.1) (x' := s.1) hy.1 hy'.1 h0 h1).2.1
      rw [cmb_self] at this
      rw [this]; ring
    have hrhs : rhs M v s (cmb convex_assetX h0 h1 y y') =
        U (assetC d p s.1.1 (cmb convex_assetX h0 h1 y y').1 s.2) +
          β * expV M v s (cmb convex_assetX h0 h1 y y') := by
      obtain ⟨x, z⟩ := s
      simp only [rhs]
      change assetF U d p xbar (x, _, z) + β * _ = _
      rw [assetF_of_mem hmem]
    have hE : (1 / 2) * expV M v s y + (1 - 1 / 2) * expV M v s y' ≤
        expV M v s (cmb convex_assetX h0 h1 y y') := by
      have := expV_comb M hb (hX := convex_assetX) (hY := convex_assetX)
        (fun _ _ _ _ _ _ _ _ => rfl) hvc (x := s.1) (x' := s.1) (z := s.2) hy.1 hy'.1 h0 h1
        (by rw [cmb_self]; exact hmem)
      rwa [cmb_self] at this
    have hlt := asset_rhs_le h hQ hv hmem
    rw [hrhs, hcm] at hlt
    simp only [smul_eq_mul] at hU
    have e1 := hval s y hy
    have e2 := hval s y' hy'
    have hβE := mul_le_mul_of_nonneg_left hE h.β_pos.le
    change 1 / 2 * U (assetC d p s.1.1 y.1 s.2) + 1 / 2 * U (assetC d p s.1.1 y'.1 s.2) <
      U (1 / 2 * assetC d p s.1.1 y.1 s.2 + 1 / 2 * assetC d p s.1.1 y'.1 s.2) at hU
    linarith

theorem assetX_mem_nhds {x : Fin k → ℝ} (hx : ∀ i, 0 < x i ∧ x i < xbar) :
    assetX k xbar ∈ 𝓝 x :=
  set_pi_mem_nhds finite_univ fun i _ => Icc_mem_nhds (hx i).1 (hx i).2

omit [CompactSpace Z] [OpensMeasurableSpace Z] in
/-- The value of a feasible choice: `rhs = U(c) + β ∫ v(y, z′) Q(z, dz′)`. -/
theorem asset_rhs_eq {Q : Kernel Z Z} (v : assetX k xbar × Z →ᵇ ℝ) {x y : assetX k xbar} {z : Z}
    (hy : y ∈ assetΓ d p xbar (x, z)) :
    rhs (assetModel Q U d p β xbar) v (x, z) y =
      U (assetC d p x.1 y.1 z) + β * ∫ z', v (y, z') ∂Q z := by
  simp only [rhs, expV]
  rw [assetF_of_mem hy]

/-- **Exercise 10.6c** (1). At an interior `x₀` with an optimal `y₀` leaving positive consumption
`c`, `vᵖ(·, z₀)` is differentiable with `vᵖᵢ(x₀, z₀) = U′(c)[dᵢ(z₀) + pᵢ(z₀)]`
(Benveniste–Scheinkman). -/
theorem ex_10_6c_deriv (h : AssetHyp U d p β xbar) {Q : Kernel Z Z} [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : assetX k xbar × Z →ᵇ ℝ}
    (hv : bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v)
    {x₀ y₀ : assetX k xbar} {z₀ : Z} (hint : ∀ i, 0 < x₀.1 i ∧ x₀.1 i < xbar)
    (hy₀ : y₀ ∈ policy (assetModel Q U d p β xbar) v (x₀, z₀))
    (hc : 0 < assetC d p x₀.1 y₀.1 z₀) {U' : ℝ}
    (hU' : HasDerivAt U U' (assetC d p x₀.1 y₀.1 z₀)) :
    HasFDerivAt (liftS fun x => v (x, z₀)) (U' • dotCLM (d z₀ + p z₀)) x₀.1 := by
  set a := d z₀ + p z₀
  set E := ∫ z', v (y₀, z') ∂Q z₀
  have hcx : ∀ x, assetC d p x y₀.1 z₀ = dotCLM a x - dotR (p z₀) y₀.1 := fun x => by
    rw [dotCLM_apply]; rfl
  have hL : HasFDerivAt (fun x => U (dotCLM a x - dotR (p z₀) y₀.1) + β * E)
      (U' • dotCLM a) x₀.1 := by
    rw [hcx] at hU'
    exact (hU'.comp_hasFDerivAt x₀.1 ((dotCLM a).hasFDerivAt.sub_const _)).add_const _
  refine theorem_4_10 (concaveOn_liftS (asset_concave h hQ hv z₀)) (assetX_mem_nhds hint) hL ?_ ?_
  · rw [liftS_of_mem _ x₀.2, ← hcx, hy₀.2, asset_rhs_eq v hy₀.1]
  · have hev : ∀ᶠ x in 𝓝 x₀.1, 0 < dotCLM a x - dotR (p z₀) y₀.1 := by
      rw [hcx] at hc
      exact ((dotCLM a).continuous.sub continuous_const).continuousAt.eventually (lt_mem_nhds hc)
    filter_upwards [hev, assetX_mem_nhds hint] with x hx hxS
    rw [liftS_of_mem _ hxS]
    have hy : y₀ ∈ assetΓ d p xbar (⟨x, hxS⟩, z₀) := by
      have := hx.le; rw [← hcx] at this; exact sub_nonneg.1 this
    have := asset_rhs_le h hQ hv hy
    rw [asset_rhs_eq v hy] at this
    rw [← hcx]
    exact this

/-- `p·(y + t eᵢ) = p·y + t pᵢ`. -/
theorem dotR_add_single (a y : Fin k → ℝ) (i : Fin k) (t : ℝ) :
    dotR a (y + t • Pi.single i 1) = dotR a y + t * a i := by
  simp only [dotR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
    (fun hi => absurd (Finset.mem_univ i) hi)]
  simp; ring

/-- **Exercise 10.6c** (2), the Euler equation. If moreover `y₀` is interior and each `vᵖ(·, z′)`
has partial derivative `vᵢ(z′)` at `y₀` (measurable in `z′`), then
`U′(c) pᵢ(z₀) = β ∫ vᵢ(z′) Q(z₀, dz′)`. -/
theorem ex_10_6c_euler (h : AssetHyp U d p β xbar) {Q : Kernel Z Z} [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : assetX k xbar × Z →ᵇ ℝ}
    (hv : bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v)
    {x₀ y₀ : assetX k xbar} {z₀ : Z} (hy₀ : y₀ ∈ policy (assetModel Q U d p β xbar) v (x₀, z₀))
    (hyint : ∀ i, 0 < y₀.1 i ∧ y₀.1 i < xbar) (hc : 0 < assetC d p x₀.1 y₀.1 z₀) {U' : ℝ}
    (hU' : HasDerivAt U U' (assetC d p x₀.1 y₀.1 z₀)) (i : Fin k) {vi : Z → ℝ}
    (hvim : AEStronglyMeasurable vi (Q z₀))
    (hvi : ∀ z', HasDerivAt (fun t : ℝ => liftS (fun y => v (y, z')) (y₀.1 + t • Pi.single i 1))
      (vi z') 0) :
    U' * p z₀ i = β * ∫ z', vi z' ∂Q z₀ := by
  set e : Fin k → ℝ := Pi.single i 1
  set r := min (y₀.1 i) (xbar - y₀.1 i)
  have hr : 0 < r := lt_min (hyint i).1 (by linarith [(hyint i).2])
  -- `y₀ + t eᵢ` stays in `X` for `|t| < r`
  have hmemX : ∀ t ∈ ball (0 : ℝ) r, y₀.1 + t • e ∈ assetX k xbar := by
    intro t ht
    rw [mem_ball, Real.dist_eq, sub_zero] at ht
    refine mem_assetX.2 fun j => ?_
    by_cases hj : j = i
    · subst hj
      have h1 := min_le_left (y₀.1 j) (xbar - y₀.1 j)
      have h2 := min_le_right (y₀.1 j) (xbar - y₀.1 j)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, Pi.single_eq_same, mul_one]
      constructor <;> linarith [neg_abs_le t, le_abs_self t]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, Pi.single_eq_of_ne hj, mul_zero,
        add_zero]
      exact mem_assetX.1 y₀.2 j
  set f : Z → ℝ → ℝ := fun z' t => liftS (fun y => v (y, z')) (y₀.1 + t • e)
  -- each `f(z′, ·)` is concave and bounded by `‖v‖` on `(−r, r)`, hence Lipschitz on `(−r/2, r/2)`
  have hconc : ∀ z', ConcaveOn ℝ (ball (0 : ℝ) r) (f z') := fun z' => by
    have hV := concaveOn_liftS (asset_concave h hQ hv z')
    refine ⟨convex_ball 0 r, fun a ha b hb θ η hθ hη hθη => ?_⟩
    have e1 : y₀.1 + (θ • a + η • b) • e = θ • (y₀.1 + a • e) + η • (y₀.1 + b • e) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(y₀.1 j)) * hθη
    have := hV.2 (hmemX a ha) (hmemX b hb) hθ hη hθη
    simp only [f]
    rw [e1]
    exact this
  have hbd : ∀ z' t, t ∈ ball (0 : ℝ) r → |f z' t| ≤ ‖v‖ := fun z' t ht => by
    simp only [f]
    rw [liftS_of_mem _ (hmemX t ht), ← Real.norm_eq_abs]
    exact v.norm_coe_le_norm _
  have hr2 : (0 : ℝ) < r / 2 := by positivity
  have hlip : ∀ z', LipschitzOnWith (Real.nnabs (2 * ‖v‖ / (r / 2))) (f z') (ball 0 (r - r / 2)) :=
    fun z' => by
      rw [Real.nnabs_of_nonneg (by positivity)]
      exact (hconc z').lipschitzOnWith_of_abs_le hr2 fun a ha => hbd z' a ha
  have hball : ball (0 : ℝ) (r - r / 2) ∈ 𝓝 0 := ball_mem_nhds 0 (by linarith)
  -- differentiate under the integral sign
  have hmeas : ∀ t ∈ ball (0 : ℝ) r, AEStronglyMeasurable (fun z' => f z' t) (Q z₀) := by
    intro t ht
    have : (fun z' => f z' t) = fun z' => v (⟨y₀.1 + t • e, hmemX t ht⟩, z') := by
      funext z'; simp only [f]; rw [liftS_of_mem _ (hmemX t ht)]
    rw [this]
    exact (v.continuous.comp (Continuous.prodMk_right _)).aestronglyMeasurable
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_lip (μ := Q z₀)
    (F := fun t z' => f z' t)
    (bound := fun _ => 2 * ‖v‖ / (r / 2)) hball
    (eventually_of_mem (ball_mem_nhds 0 hr) hmeas)
    (integrable_of_abs_le (by
      have := hmeas 0 (mem_ball_self hr)
      have e0 : (fun z' => f z' 0) = fun z' => v (y₀, z') := by
        funext z'; simp only [f, zero_smul, add_zero]; rw [liftS_of_mem _ y₀.2]
      rw [e0]
      exact (v.continuous.comp (Continuous.prodMk_right _)).measurable)
      fun z' => hbd z' 0 (mem_ball_self hr))
    hvim (Eventually.of_forall hlip) (integrable_const _) (Eventually.of_forall hvi)
  -- the objective along `y₀ + t eᵢ`
  set c₀ := assetC d p x₀.1 y₀.1 z₀
  set Φ : ℝ → ℝ := fun t => U (c₀ - t * p z₀ i) + β * ∫ z', f z' t ∂Q z₀
  have hΦ : HasDerivAt Φ (U' * (-p z₀ i) + β * ∫ z', vi z' ∂Q z₀) 0 := by
    have hin : HasDerivAt (fun t : ℝ => c₀ - t * p z₀ i) (-p z₀ i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (p z₀ i)).const_sub c₀
    have := hU'
    rw [show c₀ = c₀ - 0 * p z₀ i by ring] at this
    exact (this.comp 0 hin).add (hderiv.const_mul β)
  have hmax : IsLocalMax Φ 0 := by
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ c₀ - t * p z₀ i :=
      ((continuous_const.sub (continuous_id.mul continuous_const)).continuousAt.eventually
        (lt_mem_nhds (show 0 < c₀ - 0 * p z₀ i by simpa using hc))).mono fun _ ht => ht.le
    filter_upwards [hev, ball_mem_nhds (0 : ℝ) hr] with t ht htr
    set yt : assetX k xbar := ⟨y₀.1 + t • e, hmemX t htr⟩
    have hct : assetC d p x₀.1 yt.1 z₀ = c₀ - t * p z₀ i := by
      change dotR (d z₀ + p z₀) x₀.1 - dotR (p z₀) (y₀.1 + t • e) =
        assetC d p x₀.1 y₀.1 z₀ - t * p z₀ i
      rw [dotR_add_single]; unfold assetC; ring
    have hyt : yt ∈ assetΓ d p xbar (x₀, z₀) := sub_nonneg.1 (hct ▸ ht)
    have hle := asset_rhs_le h hQ hv hyt
    rw [asset_rhs_eq v hyt, hct] at hle
    have h0 : Φ 0 = v (x₀, z₀) := by
      simp only [Φ, zero_mul, sub_zero, f, zero_smul, add_zero]
      rw [hy₀.2, asset_rhs_eq v hy₀.1]
      congr 2
      exact integral_congr_ae (Eventually.of_forall fun z' => by
        simp only; rw [liftS_of_mem _ y₀.2])
    rw [h0]
    simp only [Φ, f]
    convert hle using 3
    exact integral_congr_ae (Eventually.of_forall fun z' => by
      simp only; rw [liftS_of_mem _ (hmemX t htr)])
  have := hmax.hasDerivAt_eq_zero hΦ
  linarith

/-- The portfolio of one share of each asset. -/
def oneX (h1 : 1 ≤ xbar) : assetX k xbar := ⟨fun _ => 1, mem_assetX.2 fun _ => ⟨zero_le_one, h1⟩⟩

omit [MetricSpace Z] [MeasurableSpace Z] [CompactSpace Z] [OpensMeasurableSpace Z] in
theorem assetC_one (h1 : 1 ≤ xbar) (z : Z) :
    assetC d p (oneX (k := k) h1).1 (oneX h1).1 z = ∑ j, d z j := by
  simp [assetC, dotR, oneX, Finset.sum_add_distrib]

theorem dotR_single (a : Fin k → ℝ) (i : Fin k) : dotR a (Pi.single i 1) = a i := by
  have := dotR_add_single a 0 i 1
  simpa [dotR] using this

/-- **Exercise 10.6d.** If holding one share of each asset is optimal in every state (the
equilibrium condition), then (3) `vᵢ(1, z) = U′(z·1)[zᵢ + pᵢ(z)]` and (4)–(5)
`U′(z·1) pᵢ(z) = β ∫ U′(z′·1)[z′ᵢ + pᵢ(z′)] Q(z, dz′)`. -/
theorem ex_10_6d (h : AssetHyp U d p β xbar) (hk : 0 < k) {Q : Kernel Z Z} [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : assetX k xbar × Z →ᵇ ℝ}
    (hv : bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v) {Up : ℝ → ℝ}
    (hUp : Continuous Up) (hUd : ∀ c, 0 < c → HasDerivAt U (Up c) c)
    (heq : ∀ z, oneX h.xbar_gt.le ∈ policy (assetModel Q U d p β xbar) v (oneX h.xbar_gt.le, z)) :
    (∀ z, HasFDerivAt (liftS fun x => v (x, z)) (Up (∑ j, d z j) • dotCLM (d z + p z))
      (fun _ => 1)) ∧
    ∀ z i, Up (∑ j, d z j) * p z i =
      β * ∫ z', Up (∑ j, d z' j) * (d z' i + p z' i) ∂Q z := by
  set one := oneX (k := k) h.xbar_gt.le
  have hint : ∀ i, 0 < one.1 i ∧ one.1 i < xbar := fun _ => ⟨one_pos, h.xbar_gt⟩
  have hc' : ∀ z, assetC d p one.1 one.1 z = ∑ j, d z j := fun z => assetC_one _ z
  have hsum : ∀ z, 0 < ∑ j, d z j := fun z => by
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact Finset.sum_pos (fun j _ => h.d_pos z j) Finset.univ_nonempty
  have hc : ∀ z, 0 < assetC d p one.1 one.1 z := fun z => by rw [hc' z]; exact hsum z
  have hU'' : ∀ z, HasDerivAt U (Up (∑ j, d z j)) (assetC d p one.1 one.1 z) := fun z => by
    rw [hc' z]; exact hUd _ (hsum z)
  have h3 : ∀ z, HasFDerivAt (liftS fun x => v (x, z)) (Up (∑ j, d z j) • dotCLM (d z + p z))
      (fun _ => 1) := fun z => ex_10_6c_deriv h hQ hv hint (heq z) (hc z) (hU'' z)
  refine ⟨h3, fun z i => ?_⟩
  set e : Fin k → ℝ := Pi.single i 1
  have hvi : ∀ z', HasDerivAt (fun t : ℝ => liftS (fun y => v (y, z')) (one.1 + t • e))
      (Up (∑ j, d z' j) * (d z' i + p z' i)) 0 := fun z' => by
    have hline : HasDerivAt (fun t : ℝ => one.1 + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add one.1
    have h3' := h3 z'
    rw [show (fun _ : Fin k => (1 : ℝ)) = one.1 + (0 : ℝ) • e by simp [one, oneX]] at h3'
    refine (h3'.comp_hasDerivAt (0 : ℝ) hline).congr_deriv ?_
    simp only [_root_.smul_apply, smul_eq_mul, dotCLM_apply, e, dotR_single, Pi.add_apply]
  have hvim : AEStronglyMeasurable (fun z' => Up (∑ j, d z' j) * (d z' i + p z' i)) (Q z) :=
    ((hUp.comp (continuous_finsetSum _ fun j _ => (continuous_apply j).comp h.d_cont)).mul
      (((continuous_apply i).comp h.d_cont).add
        ((continuous_apply i).comp h.p_cont))).aestronglyMeasurable
  exact ex_10_6c_euler h hQ hv (heq z) hint (hc z) (hU'' z) i hvim hvi

end StokeyLucasPrescott.StochasticApplications
