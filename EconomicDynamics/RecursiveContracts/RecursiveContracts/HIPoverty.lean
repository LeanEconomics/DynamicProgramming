/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.HIOptimal
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Uniform

/-!
# Long-run poverty: Proposition 22.3.4

Miao, §22.3.2, pp. 796–797: under the optimal contract the promised value `vₜ` converges to
`−∞` almost surely (immiseration).

The shocks are an iid sequence `ξₜ : Ω → Fin n` on a probability space with
`Pr(ξₜ = i) = πᵢ`; the promised value evolves by `vₜ₊₁ = w_{ξₜ}(vₜ)` (`hi_vseq`) for policy
functions `wᵢ(v)`. The function `G` plays the role of `P'`.

* `hi_poverty_det`: the deterministic core. If `G(xₜ)` converges, `G` is continuous, strictly
  decreasing and negative on `(−∞, vmax)` with `G → 0` at `−∞` and `G → −∞` at `vmax`, and
  infinitely often `xₜ₊₁ = wₙ(xₜ)` where `wₙ` is continuous with `wₙ(v) > v` (Lemma 22.3.3),
  then `xₜ → −∞`. A finite negative limit would give a fixed point `v* = wₙ(v*)`.
* `hi_poverty_martingale`: `−G(vₜ₊₁)` is a nonnegative martingale for the natural filtration of
  the shocks (the martingale property (22.30) of the policies and independence of the shocks).
* `proposition_22_3_4`: `vₜ → −∞` almost surely, by the martingale convergence theorem
  (`Submartingale.ae_tendsto_limitProcess`) and the second Borel–Cantelli lemma (the top shock
  occurs infinitely often).
* `hi_poverty_example`: the hypotheses hold for the CARA example (`G(v) = 1/v`,
  `w₁(v) = 2v`, `w₂(v) = 2v/3`) with iid fair-coin shocks, so the proposition is not vacuous.

Departure: the continuity of the top policy `wₙ(v)` is assumed (the book uses it implicitly).
-/

namespace Miao.RecursiveContracts

open Finset Filter Topology MeasureTheory ProbabilityTheory

/-- Miao, p. 797: the promised values `v₀, v₁ = w_{s₀}(v₀), …` along a shock path `s`. -/
def hi_vseq (M : HIModel) (W : Fin (M.N + 1) → ℝ → ℝ) (v0 : ℝ) (s : ℕ → Fin (M.N + 1)) :
    ℕ → ℝ
  | 0 => v0
  | t + 1 => W (s t) (hi_vseq M W v0 s t)

/-- `vₜ` depends only on the shocks before `t`. -/
theorem hi_vseq_congr (M : HIModel) (W : Fin (M.N + 1) → ℝ → ℝ) (v0 : ℝ)
    {s s' : ℕ → Fin (M.N + 1)} (t : ℕ) (h : ∀ j < t, s j = s' j) :
    hi_vseq M W v0 s t = hi_vseq M W v0 s' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [hi_vseq]
    rw [h t (lt_add_one t), ih fun j hj => h j (by omega)]

/-- The promised values stay in `(−∞, vmax)`. -/
theorem hi_vseq_lt (M : HIModel) {W : Fin (M.N + 1) → ℝ → ℝ} {v0 : ℝ} (hv0 : v0 < hi_vmax M)
    (hWV : ∀ i, ∀ v < hi_vmax M, W i v < hi_vmax M) (s : ℕ → Fin (M.N + 1)) (t : ℕ) :
    hi_vseq M W v0 s t < hi_vmax M := by
  induction t with
  | zero => exact hv0
  | succ t ih => exact hWV _ _ ih

/-- Miao, p. 797 (proof of Proposition 22.3.4, deterministic part). If `G(xₜ)` converges,
`G` is continuous, strictly decreasing and negative on `(−∞, vmax)`, `G → 0` at `−∞`,
`G → −∞` at `vmax`, `wₙ` is continuous with `wₙ(v) > v` (Lemma 22.3.3), and infinitely often
`xₜ₊₁ = wₙ(xₜ)`, then `xₜ → −∞`. -/
theorem hi_poverty_det (M : HIModel) {G Wn : ℝ → ℝ} (hGneg : ∀ v < hi_vmax M, G v < 0)
    (hGanti : StrictAntiOn G (Set.Iio (hi_vmax M)))
    (hGcont : ContinuousOn G (Set.Iio (hi_vmax M))) (hGbot : Tendsto G atBot (𝓝 0))
    (hGtop : Tendsto G (𝓝[<] hi_vmax M) atBot) (hWcont : ContinuousOn Wn (Set.Iio (hi_vmax M)))
    (hlemma : ∀ v < hi_vmax M, v < Wn v) {x : ℕ → ℝ} (hx : ∀ t, x t < hi_vmax M) {ℓ : ℝ}
    (hℓ : Tendsto (fun t => G (x t)) atTop (𝓝 ℓ))
    (hfreq : ∃ᶠ t in atTop, x (t + 1) = Wn (x t)) : Tendsto x atTop atBot := by
  have hℓ0 : ℓ ≤ 0 := le_of_tendsto' hℓ fun t => (hGneg _ (hx t)).le
  rcases hℓ0.lt_or_eq with hneg | hzero
  · exfalso
    obtain ⟨A, hA, hAV⟩ : ∃ A, ℓ < G A ∧ A < hi_vmax M :=
      ((hGbot.eventually (lt_mem_nhds hneg)).and (eventually_lt_atBot _)).exists
    obtain ⟨B, hB, hBV⟩ : ∃ B, G B < ℓ ∧ B < hi_vmax M :=
      ((hGtop.eventually (eventually_lt_atBot ℓ)).and self_mem_nhdsWithin).exists
    have hAB : A < B := by
      by_contra h
      push Not at h
      have := hGanti.antitoneOn hBV hAV h
      linarith
    have hcont : ContinuousOn G (Set.Icc A B) := hGcont.mono fun y hy => lt_of_le_of_lt hy.2 hBV
    obtain ⟨vs, hvsI, hvs⟩ := intermediate_value_Icc' hAB.le hcont ⟨hB.le, hA.le⟩
    have hvsV : vs < hi_vmax M := lt_of_le_of_lt hvsI.2 hBV
    -- `xₜ → v*`
    have hxlim : Tendsto x atTop (𝓝 vs) := by
      rw [tendsto_order]
      constructor
      · intro a ha
        have haV : a < hi_vmax M := lt_trans ha hvsV
        have h1 : ℓ < G a := by rw [← hvs]; exact hGanti haV hvsV ha
        filter_upwards [hℓ.eventually (gt_mem_nhds h1)] with t ht
        by_contra h
        push Not at h
        have := hGanti.antitoneOn (hx t) haV h
        linarith
      · intro b hb
        set b' := min b ((vs + hi_vmax M) / 2)
        have hb'V : b' < hi_vmax M := lt_of_le_of_lt (min_le_right _ _) (by linarith)
        have hvsb' : vs < b' := lt_min hb (by linarith)
        have h1 : G b' < ℓ := by rw [← hvs]; exact hGanti hvsV hb'V hvsb'
        filter_upwards [hℓ.eventually (lt_mem_nhds h1)] with t ht
        by_contra h
        push Not at h
        have := hGanti.antitoneOn hb'V (hx t) (le_trans (min_le_left _ _) h)
        linarith
    have hW1 : Tendsto (fun t => Wn (x t)) atTop (𝓝 (Wn vs)) :=
      ((hWcont.continuousAt (Iio_mem_nhds hvsV)).tendsto).comp hxlim
    have hx1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 vs) := hxlim.comp (tendsto_add_atTop_nat 1)
    have hd : Tendsto (fun t => x (t + 1) - Wn (x t)) atTop (𝓝 (vs - Wn vs)) := hx1.sub hW1
    have hne : vs - Wn vs ≠ 0 := by linarith [hlemma vs hvsV]
    obtain ⟨t, h1, h2⟩ := (hfreq.and_eventually (hd.eventually_ne hne)).exists
    exact h2 (by rw [h1]; ring)
  · rw [tendsto_atBot]
    intro K
    by_cases hK : K < hi_vmax M
    · have hGK : G K < ℓ := by rw [hzero]; exact hGneg K hK
      filter_upwards [hℓ.eventually (lt_mem_nhds hGK)] with t ht
      by_contra h
      push Not at h
      have := hGanti.antitoneOn hK (hx t) h.le
      linarith
    · push Not at hK
      exact Eventually.of_forall fun t => by linarith [hx t]

/-- The natural filtration of the shocks: `ℱₜ = σ(ξ₀, …, ξₜ)`. -/
def hi_filt (M : HIModel) {Ω : Type*} [m0 : MeasurableSpace Ω] (ξ : ℕ → Ω → Fin (M.N + 1))
    (hξ : ∀ t, Measurable (ξ t)) : Filtration ℕ m0 where
  seq t := ⨆ j ≤ t, MeasurableSpace.comap (ξ j) inferInstance
  mono' _ _ hst := biSup_mono fun _ hj => le_trans hj hst
  le' _ := iSup₂_le fun j _ => (hξ j).comap_le

/-- `ξⱼ` is `ℱₜ`-measurable for `j ≤ t`. -/
theorem hi_filt_meas (M : HIModel) {Ω : Type*} [MeasurableSpace Ω] {ξ : ℕ → Ω → Fin (M.N + 1)}
    (hξ : ∀ t, Measurable (ξ t)) {j t : ℕ} (hj : j ≤ t) :
    Measurable[hi_filt M ξ hξ t] (ξ j) :=
  Measurable.of_comap_le
    (le_iSup₂ (f := fun j (_ : j ≤ t) => MeasurableSpace.comap (ξ j) inferInstance) j hj)

/-- A function of finitely many measurable shocks is strongly measurable. -/
theorem hi_tuple_sm_aux (M : HIModel) {Ω : Type*} [mΩ : MeasurableSpace Ω] (t : ℕ)
    (g : (Fin (t + 1) → Fin (M.N + 1)) → ℝ) (f : Fin (t + 1) → Ω → Fin (M.N + 1))
    (hf : ∀ j, Measurable (f j)) : StronglyMeasurable fun ω => g fun j => f j ω :=
  ((measurable_of_countable g).comp (measurable_pi_iff.2 hf)).stronglyMeasurable

/-- A function of `(ξ₀, …, ξₜ)` is `ℱₜ`-strongly measurable. -/
theorem hi_tuple_sm (M : HIModel) {Ω : Type*} [MeasurableSpace Ω] {ξ : ℕ → Ω → Fin (M.N + 1)}
    (hξ : ∀ t, Measurable (ξ t)) (t : ℕ) (g : (Fin (t + 1) → Fin (M.N + 1)) → ℝ) :
    StronglyMeasurable[hi_filt M ξ hξ t] fun ω => g fun j => ξ j ω := by
  exact hi_tuple_sm_aux M (mΩ := hi_filt M ξ hξ t) t g (fun j ω => ξ j ω)
    fun j => hi_filt_meas M hξ (Nat.lt_succ_iff.1 j.isLt)

/-- A function of `(ξ₀, …, ξₜ)` is integrable (it takes finitely many values). -/
theorem hi_tuple_int (M : HIModel) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {ξ : ℕ → Ω → Fin (M.N + 1)} (hξ : ∀ t, Measurable (ξ t)) (t : ℕ)
    (g : (Fin (t + 1) → Fin (M.N + 1)) → ℝ) : Integrable (fun ω => g fun j => ξ j ω) μ :=
  by
    have h1 := hi_tuple_sm M hξ t g
    have h2 : StronglyMeasurable fun ω => g fun j => ξ j ω :=
      StronglyMeasurable.mono h1 ((hi_filt M ξ hξ).le t)
    exact Integrable.of_bound h2.aestronglyMeasurable (∑ a, |g a|) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun a => |g a|) (fun a _ => abs_nonneg _)
        (Finset.mem_univ _))

/-- `vₜ₊₁` as a function of `(ξ₀, …, ξₜ)`. -/
def hi_Fseq (M : HIModel) (W : Fin (M.N + 1) → ℝ → ℝ) (v0 : ℝ) (t : ℕ)
    (a : Fin (t + 1) → Fin (M.N + 1)) : ℝ :=
  hi_vseq M W v0 (fun s => if h : s < t + 1 then a ⟨s, h⟩ else 0) (t + 1)

/-- `vₜ₊₁ = Fₜ(ξ₀, …, ξₜ)`. -/
theorem hi_vseq_eq_Fseq (M : HIModel) (W : Fin (M.N + 1) → ℝ → ℝ) (v0 : ℝ) {Ω : Type*}
    (ξ : ℕ → Ω → Fin (M.N + 1)) (t : ℕ) (ω : Ω) :
    hi_vseq M W v0 (fun s => ξ s ω) (t + 1) = hi_Fseq M W v0 t fun j => ξ j ω := by
  unfold hi_Fseq
  exact hi_vseq_congr M W v0 (t + 1) fun j hj => by simp [hj]

/-- Miao, p. 797: `−G(vₜ₊₁)` is a martingale for the natural filtration of the shocks, when the
policies satisfy the martingale property `Σ πᵢ G(wᵢ(v)) = G(v)` of (22.30). -/
theorem hi_poverty_martingale (M : HIModel) {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Fin (M.N + 1))
    (hξ : ∀ t, Measurable (ξ t)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ t i, μ (ξ t ⁻¹' {i}) = ENNReal.ofReal (M.prob i)) (W : Fin (M.N + 1) → ℝ → ℝ)
    (G : ℝ → ℝ) {v0 : ℝ} (hv0 : v0 < hi_vmax M)
    (hWV : ∀ i, ∀ v < hi_vmax M, W i v < hi_vmax M)
    (hmart : ∀ v < hi_vmax M, ∑ i, M.prob i * G (W i v) = G v) :
    Martingale (fun t ω => -G (hi_vseq M W v0 (fun s => ξ s ω) (t + 1))) (hi_filt M ξ hξ) μ := by
  set ℱ := hi_filt M ξ hξ
  set Y : ℕ → Ω → ℝ := fun t ω => -G (hi_vseq M W v0 (fun s => ξ s ω) (t + 1))
  have hrep : ∀ t, Y t = fun ω => (fun a => -G (hi_Fseq M W v0 t a)) fun j => ξ j ω :=
    fun t => funext fun ω => by simp only [Y, hi_vseq_eq_Fseq]
  have hadp : StronglyAdapted ℱ Y := fun t => by
    rw [hrep t]; exact hi_tuple_sm M hξ t (fun a => -G (hi_Fseq M W v0 t a))
  have hint : ∀ t, Integrable (Y t) μ := fun t => by
    rw [hrep t]; exact hi_tuple_int M hξ t (fun a => -G (hi_Fseq M W v0 t a))
  refine martingale_nat hadp hint fun t => ?_
  -- the decomposition `Y_{t+1} = Σᵢ hᵢ eᵢ`
  set h : Fin (M.N + 1) → Ω → ℝ := fun i ω => -G (W i (hi_vseq M W v0 (fun s => ξ s ω) (t + 1)))
  set e : Fin (M.N + 1) → Ω → ℝ := fun i => (ξ (t + 1) ⁻¹' {i}).indicator 1
  have hdec : Y (t + 1) = ∑ i, h i * e i := by
    funext ω
    rw [Finset.sum_apply, Finset.sum_eq_single (ξ (t + 1) ω)]
    · simp [Y, h, e, hi_vseq]
    · intro b _ hb
      simp [e, Set.indicator, Ne.symm hb]
    · simp
  have hhrep : ∀ i, h i = fun ω => (fun a => -G (W i (hi_Fseq M W v0 t a))) fun j => ξ j ω :=
    fun i => funext fun ω => by simp only [h, hi_vseq_eq_Fseq]
  have hhsm : ∀ i, StronglyMeasurable[ℱ t] (h i) := fun i => by
    rw [hhrep i]; exact hi_tuple_sm M hξ t (fun a => -G (W i (hi_Fseq M W v0 t a)))
  have hhint : ∀ i, Integrable (h i) μ := fun i => by
    rw [hhrep i]; exact hi_tuple_int M hξ t (fun a => -G (W i (hi_Fseq M W v0 t a)))
  have hemeas : ∀ i, MeasurableSet (ξ (t + 1) ⁻¹' {i}) := fun i =>
    hξ (t + 1) (MeasurableSpace.measurableSet_top)
  have heint : ∀ i, Integrable (e i) μ := fun i =>
    (integrable_const (1 : ℝ)).indicator (hemeas i)
  have hebdd : ∀ i, ∀ ω, ‖e i ω‖ ≤ 1 := fun i ω => by
    simp only [e, Set.indicator]; split_ifs <;> simp
  have hheint : ∀ i, Integrable (h i * e i) μ := fun i =>
    (hhint i).mul_bdd ((heint i).aestronglyMeasurable) (ae_of_all _ (hebdd i))
  -- independence of `ξ_{t+1}` from `ℱₜ`
  have hindep : Indep (MeasurableSpace.comap (ξ (t + 1)) inferInstance) (ℱ t) μ := by
    have := indep_iSup_of_disjoint (m := fun j => MeasurableSpace.comap (ξ j) inferInstance)
      (fun j => (hξ j).comap_le) ((iIndepFun_iff_iIndep _ _ _).1 hind)
      (S := {t + 1}) (T := {k | k ≤ t}) (by simp)
    rwa [_root_.iSup_singleton] at this
  have hesm : ∀ i, StronglyMeasurable[MeasurableSpace.comap (ξ (t + 1)) inferInstance] (e i) :=
    fun i => by
      have hm : Measurable[MeasurableSpace.comap (ξ (t + 1)) inferInstance] (ξ (t + 1)) :=
        Measurable.of_comap_le le_rfl
      have : e i = (fun a : Fin (M.N + 1) => ({i} : Set (Fin (M.N + 1))).indicator 1 a) ∘
          ξ (t + 1) := by
        funext ω; simp [e, Set.indicator]
      rw [this]
      exact ((measurable_of_countable _).comp hm).stronglyMeasurable
  have hEe : ∀ i, μ[e i] = M.prob i := fun i => by
    simp only [e]
    rw [integral_indicator_one (hemeas i), measureReal_def, hlaw,
      ENNReal.toReal_ofReal (M.prob_pos i).le]
  have hce : ∀ i, μ[e i | ℱ t] =ᵐ[μ] fun _ => M.prob i := fun i => by
    have := condExp_indep_eq (hξ (t + 1)).comap_le (ℱ.le t) (hesm i) hindep
    rw [hEe i] at this
    exact this
  have hpull : ∀ i, μ[h i * e i | ℱ t] =ᵐ[μ] h i * μ[e i | ℱ t] := fun i =>
    condExp_mul_of_stronglyMeasurable_left (hhsm i) (hheint i) (heint i)
  have hsum := condExp_finsetSum (μ := μ) (m := ℱ t) (s := Finset.univ)
    (f := fun i => h i * e i) fun i _ => hheint i
  rw [hdec]
  filter_upwards [hsum, ae_all_iff.2 hpull, ae_all_iff.2 hce] with ω h1 h2 h3
  rw [h1, Finset.sum_apply]
  simp only [Pi.mul_apply] at h2
  simp only [h2, h3]
  have hv := hi_vseq_lt M hv0 hWV (fun s => ξ s ω) (t + 1)
  have := hmart _ hv
  simp only [Y, h]
  rw [← this, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Proposition 22.3.4** (Miao, p. 796). The promised value `vₜ` converges to `−∞` almost
surely. Here `G` is the derivative `P'` of the value function, `W i` the policy `wᵢ(v)` of the
optimal contract, satisfying the martingale property (22.30), Lemma 22.3.3 (`wₙ(v) > v`), and
the endpoint limits `P'(−∞) = 0`, `P'(vmax) = −∞` of p. 797; `P'` is continuous, strictly
decreasing and negative, and `wₙ` is continuous. -/
theorem proposition_22_3_4 (M : HIModel) {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Fin (M.N + 1))
    (hξ : ∀ t, Measurable (ξ t)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ t i, μ (ξ t ⁻¹' {i}) = ENNReal.ofReal (M.prob i)) (W : Fin (M.N + 1) → ℝ → ℝ)
    (G : ℝ → ℝ) {v0 : ℝ} (hv0 : v0 < hi_vmax M)
    (hWV : ∀ i, ∀ v < hi_vmax M, W i v < hi_vmax M)
    (hmart : ∀ v < hi_vmax M, ∑ i, M.prob i * G (W i v) = G v)
    (hGneg : ∀ v < hi_vmax M, G v < 0) (hGanti : StrictAntiOn G (Set.Iio (hi_vmax M)))
    (hGcont : ContinuousOn G (Set.Iio (hi_vmax M))) (hGbot : Tendsto G atBot (𝓝 0))
    (hGtop : Tendsto G (𝓝[<] hi_vmax M) atBot)
    (hWcont : ContinuousOn (W (Fin.last M.N)) (Set.Iio (hi_vmax M)))
    (hlemma : ∀ v < hi_vmax M, v < W (Fin.last M.N) v) :
    ∀ᵐ ω ∂μ, Tendsto (fun t => hi_vseq M W v0 (fun s => ξ s ω) t) atTop atBot := by
  set Y : ℕ → Ω → ℝ := fun t ω => -G (hi_vseq M W v0 (fun s => ξ s ω) (t + 1))
  have hM := hi_poverty_martingale M ξ hξ hind hlaw W G hv0 hWV hmart
  have hY0 : ∀ t ω, 0 ≤ Y t ω := fun t ω => by
    have := hGneg _ (hi_vseq_lt M hv0 hWV (fun s => ξ s ω) (t + 1)); simp only [Y]; linarith
  -- L¹ bound
  have hbdd : ∀ n, eLpNorm (Y n) 1 μ ≤ (∫ ω, Y 0 ω ∂μ).toNNReal := by
    intro n
    have h1 : ∫ ω, Y n ω ∂μ = ∫ ω, Y 0 ω ∂μ := by
      rw [← integral_condExp ((hi_filt M ξ hξ).le 0)]
      exact integral_congr_ae (hM.2 0 n (Nat.zero_le n))
    rw [eLpNorm_one_eq_lintegral_enorm (hM.integrable n).aestronglyMeasurable]
    have h2 : ∫⁻ ω, ‖Y n ω‖ₑ ∂μ = ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂μ :=
      lintegral_congr fun ω => Real.enorm_eq_ofReal (hY0 n ω)
    rw [h2, ← ofReal_integral_eq_lintegral_ofReal (hM.integrable n) (ae_of_all _ (hY0 n)), h1]
    rfl
  have hconv := hM.submartingale.ae_tendsto_limitProcess hbdd
  -- the top shock occurs infinitely often
  set s : ℕ → Set Ω := fun t => ξ t ⁻¹' {Fin.last M.N}
  have hsm : ∀ t, MeasurableSet (s t) := fun t => hξ t MeasurableSpace.measurableSet_top
  have hsind : iIndepSet s μ := by
    rw [iIndepSet_iff_meas_biInter hsm]
    intro S
    exact hind.meas_biInter fun i _ => ⟨{Fin.last M.N}, MeasurableSpace.measurableSet_top, rfl⟩
  have hsum : ∑' t, μ (s t) = ⊤ := by
    simp only [s, hlaw]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by
      simpa using M.prob_pos (Fin.last M.N))
  have hBC := measure_limsup_eq_one hsm hsind hsum
  have hae : ∀ᵐ ω ∂μ, ω ∈ limsup s atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hsm)).2 hBC
  filter_upwards [hconv, hae] with ω h1 h2
  rw [Filter.mem_limsup_iff_frequently_mem] at h2
  set x : ℕ → ℝ := fun t => hi_vseq M W v0 (fun s => ξ s ω) (t + 1)
  have hx : ∀ t, x t < hi_vmax M := fun t => hi_vseq_lt M hv0 hWV _ _
  have hGx : Tendsto (fun t => G (x t)) atTop
      (𝓝 (-(hi_filt M ξ hξ).limitProcess Y μ ω)) := by
    have := h1.neg
    simp only [neg_neg] at this
    exact this
  have hfreq : ∃ᶠ t in atTop, x (t + 1) = W (Fin.last M.N) (x t) := by
    rw [Filter.frequently_atTop] at h2 ⊢
    intro a
    obtain ⟨b, hb, hbs⟩ := h2 (a + 1)
    refine ⟨b - 1, by omega, ?_⟩
    have hb1 : b - 1 + 1 = b := by omega
    simp only [x, hi_vseq]
    rw [hb1]
    simp only [s, Set.mem_preimage, Set.mem_singleton_iff] at hbs
    rw [hbs]
  have := hi_poverty_det M hGneg hGanti hGcont hGbot hGtop hWcont hlemma hx hGx hfreq
  exact (tendsto_add_atTop_iff_nat 1).1 this

/-- In the concrete CARA instance, `vmax = sup u / (1 − β) = 0`. -/
theorem hi_exampleModel_vmax : hi_vmax hi_exampleModel = 0 := by
  change sSup (Set.range (hi_cara 1)) / (1 - 1 / 2) = 0
  rw [hi_cara_sSup one_pos, zero_div]

/-- The example policies `w₁(v) = 2v`, `w₂(v) = 2v/3`. -/
noncomputable def hi_exampleW (i : Fin (hi_exampleModel.N + 1)) (v : ℝ) : ℝ :=
  if i = 0 then 2 * v else 2 / 3 * v

/-- Non-vacuity of Proposition 22.3.4: in the concrete CARA instance (two equally likely income
states), with `G(v) = 1/v` and the policies `w₁(v) = 2v`, `w₂(v) = 2v/3` (which satisfy
`½·1/(2v) + ½·3/(2v) = 1/v`), and iid fair-coin shocks on some probability space, every
hypothesis of `proposition_22_3_4` holds, and the promised value starting from `v₀ = −1`
converges to `−∞` almost surely. -/
theorem hi_poverty_example : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (ξ : ℕ → Ω → Fin (hi_exampleModel.N + 1)), IsProbabilityMeasure P ∧
      (∀ t, Measurable (ξ t)) ∧ iIndepFun ξ P ∧
      (∀ t i, P (ξ t ⁻¹' {i}) = ENNReal.ofReal (hi_exampleModel.prob i)) ∧
      ∀ᵐ ω ∂P, Tendsto (fun t => hi_vseq hi_exampleModel hi_exampleW (-1) (fun s => ξ s ω) t)
        atTop atBot := by
  set M := hi_exampleModel
  have hprob : ∀ i, M.prob i = 1 / 2 := fun i => by
    fin_cases i <;> simp [M, hi_exampleModel, hi_caraModel]
  obtain ⟨Ω, mΩ, P, ξ, hξ, hlaw, hind, hP⟩ :=
    exists_iid ℕ (PMF.uniformOfFintype (Fin (M.N + 1))).toMeasure
  have hlaw' : ∀ t i, P (ξ t ⁻¹' {i}) = ENNReal.ofReal (M.prob i) := by
    intro t i
    rw [← Measure.map_apply (hξ t) (MeasurableSpace.measurableSet_top), (hlaw t).map_eq,
      PMF.toMeasure_apply_singleton _ _ (MeasurableSpace.measurableSet_top),
      PMF.uniformOfFintype_apply, hprob, Fintype.card_fin, show M.N + 1 = 2 from rfl,
      ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, one_div]
    norm_num
  have hv : hi_vmax M = 0 := hi_exampleModel_vmax
  have hlast : (Fin.last M.N) ≠ 0 := by decide
  refine ⟨Ω, mΩ, P, ξ, hP, hξ, hind, hlaw', ?_⟩
  refine proposition_22_3_4 M ξ hξ hind hlaw' hi_exampleW (fun v => 1 / v) (by rw [hv]; norm_num)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i v hv0
    rw [hv] at hv0 ⊢
    unfold hi_exampleW
    split_ifs <;> linarith
  · intro v hv0
    rw [hv] at hv0
    have h1 : (1 : Fin (M.N + 1)) ≠ 0 := by decide
    have huniv : (Finset.univ : Finset (Fin (M.N + 1))) = {0, 1} := by
      ext j; fin_cases j <;> decide
    rw [huniv, Finset.sum_pair h1.symm]
    simp only [hprob, hi_exampleW, ↓reduceIte, h1]
    field_simp
    ring
  · intro v hv0
    rw [hv] at hv0
    exact one_div_neg.2 hv0
  · rw [hv]
    intro a ha b hb hab
    exact one_div_lt_one_div_of_neg_of_lt hb hab
  · rw [hv]
    exact continuousOn_const.div continuousOn_id fun x hx => ne_of_lt hx
  · simpa only [one_div] using tendsto_inv_atBot_zero
  · rw [hv]
    simpa only [one_div] using tendsto_inv_nhdsLT_zero
  · unfold hi_exampleW
    simp only [hlast, ↓reduceIte]
    exact (continuous_const.mul continuous_id).continuousOn
  · intro v hv0
    rw [hv] at hv0
    unfold hi_exampleW
    simp only [hlast, ↓reduceIte]
    linarith

end Miao.RecursiveContracts
