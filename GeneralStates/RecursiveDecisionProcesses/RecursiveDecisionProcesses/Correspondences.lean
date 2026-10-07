/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.BoundedMeasurable
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Correspondences and maximization

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §A.3.1.3 (pp. 350–351), as used in
Chapter 6.

* Lower and upper hemicontinuous, continuous and compact-valued correspondences, in the book's
  sequential form.
* **Exercise A.3.1**: `Γ(x) = [g(x), h(x)]` with `g ≤ h` continuous is compact-valued and continuous
  (for any topological state space; actions in `ℝ`).
* `HasMaxSelections Γ`: the conclusion of **Theorem A.3.3** (Berge's maximum theorem with a
  measurable selection): for every `q` continuous on `G = graph Γ`, a measurable selection `σ`
  attains `m(x) = max_{a ∈ Γ(x)} q(x, a)` and `m` is continuous. The book cites Aliprantis and
  Border; it is proved here for the interval correspondences of Exercise A.3.1
  (`hasMaxSelections_Icc`, for any sequential state space), which cover every application in
  Chapter 6, using the largest
  maximizer, which is upper semicontinuous and hence Borel.
-/

open Set Function Filter Topology

namespace SargentStachurski.RecursiveDecisionProcesses

variable {X A : Type*}

/-- `Γ` is lower hemicontinuous at `x`: every `y ∈ Γ(x)` is a limit of `yₙ ∈ Γ(xₙ)` along any
`xₙ → x`. -/
def IsLHC [TopologicalSpace X] [TopologicalSpace A] (Γ : X → Set A) (x : X) : Prop :=
  ∀ y ∈ Γ x, ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) →
    ∃ ys : ℕ → A, (∀ n, ys n ∈ Γ (xs n)) ∧ Tendsto ys atTop (𝓝 y)

/-- `Γ` is upper hemicontinuous at `x`: along any `xₙ → x`, every `yₙ ∈ Γ(xₙ)` has a subsequence
converging in `Γ(x)`. -/
def IsUHC [TopologicalSpace X] [TopologicalSpace A] (Γ : X → Set A) (x : X) : Prop :=
  ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) → ∀ ys : ℕ → A, (∀ n, ys n ∈ Γ (xs n)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y ∈ Γ x, Tendsto (ys ∘ φ) atTop (𝓝 y)

/-- `Γ` is continuous: lower and upper hemicontinuous everywhere. -/
def IsContinuousCorr [TopologicalSpace X] [TopologicalSpace A] (Γ : X → Set A) : Prop :=
  ∀ x, IsLHC Γ x ∧ IsUHC Γ x

/-- The clamp of `y` into `[g, h]`. -/
theorem clamp_mem {g h : ℝ} (hgh : g ≤ h) (y : ℝ) : max g (min y h) ∈ Icc g h :=
  ⟨le_max_left _ _, max_le hgh (min_le_right _ _)⟩

theorem clamp_eq {g h y : ℝ} (hy : y ∈ Icc g h) : max g (min y h) = y := by
  rw [min_eq_left hy.2, max_eq_right hy.1]

/-- A sequence `yₙ ∈ [g(xₙ), h(xₙ)]` with `xₙ → x` has a subsequence converging in
`[g(x), h(x)]`. -/
theorem exists_subseq_Icc [TopologicalSpace X] {g h : X → ℝ} (hg : Continuous g)
    (hh : Continuous h) {xs : ℕ → X} {x : X} (hx : Tendsto xs atTop (𝓝 x)) {ys : ℕ → ℝ}
    (hys : ∀ n, ys n ∈ Icc (g (xs n)) (h (xs n))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y ∈ Icc (g x) (h x), Tendsto (ys ∘ φ) atTop (𝓝 y) := by
  obtain ⟨Bg, hBg⟩ := ((hg.tendsto x).comp hx).bddBelow_range
  obtain ⟨Bh, hBh⟩ := ((hh.tendsto x).comp hx).bddAbove_range
  have hmem : ∀ n, ys n ∈ Icc Bg Bh := fun n =>
    ⟨(hBg ⟨n, rfl⟩).trans (hys n).1, (hys n).2.trans (hBh ⟨n, rfl⟩)⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  refine ⟨φ, hφ, y, ⟨?_, ?_⟩, hlim⟩
  · exact le_of_tendsto_of_tendsto' ((hg.tendsto x).comp (hx.comp hφ.tendsto_atTop)) hlim
      fun k => (hys (φ k)).1
  · exact le_of_tendsto_of_tendsto' hlim ((hh.tendsto x).comp (hx.comp hφ.tendsto_atTop))
      fun k => (hys (φ k)).2

/-- **Exercise A.3.1** (p. 350): if `g ≤ h` are continuous, `Γ(x) = [g(x), h(x)]` is
compact-valued and continuous. -/
theorem exercise_A_3_1 [TopologicalSpace X] {g h : X → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hgh : ∀ x, g x ≤ h x) :
    (∀ x, IsCompact (Icc (g x) (h x))) ∧ IsContinuousCorr fun x => Icc (g x) (h x) := by
  refine ⟨fun x => isCompact_Icc, fun x => ⟨fun y hy xs hx => ?_, fun xs hx ys hys => ?_⟩⟩
  · refine ⟨fun n => max (g (xs n)) (min y (h (xs n))), fun n => clamp_mem (hgh _) y, ?_⟩
    have := ((hg.tendsto x).comp hx).max
      ((tendsto_const_nhds (x := y)).min ((hh.tendsto x).comp hx))
    rwa [clamp_eq hy] at this
  · exact exists_subseq_Icc hg hh hx hys

/-- The conclusion of **Theorem A.3.3** for `Γ`: for every `q` continuous on `G = graph Γ`, a
measurable selection `σ` attains `m(x) = max_{a ∈ Γ(x)} q(x, a)`, and `m` is continuous. -/
def HasMaxSelections [TopologicalSpace X] [TopologicalSpace A] [MeasurableSpace X]
    [MeasurableSpace A] (Γ : X → Set A) : Prop :=
  ∀ q : X × A → ℝ, ContinuousOn q {p | p.2 ∈ Γ p.1} →
    ∃ σ : X → A, Measurable σ ∧ (∀ x, σ x ∈ Γ x) ∧ (∀ x, ∀ a ∈ Γ x, q (x, a) ≤ q (x, σ x)) ∧
      Continuous fun x => q (x, σ x)

namespace IccMax

variable [TopologicalSpace X] [SequentialSpace X] {g h : X → ℝ} {q : X × ℝ → ℝ}

/-- The maximizers of `q(x, ·)` on `[g(x), h(x)]`. -/
def argmax (g h : X → ℝ) (q : X × ℝ → ℝ) (x : X) : Set ℝ :=
  {a | a ∈ Icc (g x) (h x) ∧ ∀ b ∈ Icc (g x) (h x), q (x, b) ≤ q (x, a)}

/-- The largest maximizer. -/
noncomputable def sel (g h : X → ℝ) (q : X × ℝ → ℝ) (x : X) : ℝ := sSup (argmax g h q x)

variable (hg : Continuous g) (hh : Continuous h) (hgh : ∀ x, g x ≤ h x)
  (hq : ContinuousOn q {p | p.2 ∈ Icc (g p.1) (h p.1)})
include hg hh hgh hq

omit hg hh hgh [SequentialSpace X] in
theorem continuousOn_section (x : X) : ContinuousOn (fun a => q (x, a)) (Icc (g x) (h x)) :=
  hq.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ha => ha

omit hg hh [SequentialSpace X] in
theorem argmax_nonempty (x : X) : (argmax g h q x).Nonempty := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (hgh x))
    (continuousOn_section hq x)
  exact ⟨c, hc, fun b hb => hmax hb⟩

omit hg hh hgh [SequentialSpace X] in
theorem isClosed_argmax (x : X) : IsClosed (argmax g h q x) := by
  have hc := continuousOn_section hq x
  have heq : argmax g h q x = Icc (g x) (h x) ∩
      ⋂ b ∈ Icc (g x) (h x), (Icc (g x) (h x) ∩ (fun a => q (x, a)) ⁻¹' Ici (q (x, b))) := by
    ext a
    simp only [argmax, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_Ici]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨ha, fun b hbm => ⟨ha, hb b hbm⟩⟩
    · rintro ⟨ha, hb⟩
      exact ⟨ha, fun b hbm => (hb b hbm).2⟩
  rw [heq]
  exact isClosed_Icc.inter (isClosed_biInter fun b _ =>
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)

omit hg hh [SequentialSpace X] in
theorem sel_mem (x : X) : sel g h q x ∈ argmax g h q x :=
  (isClosed_argmax hq x).csSup_mem (argmax_nonempty hgh hq x)
    ⟨h x, fun _ ha => ha.1.2⟩

/-- The largest maximizer is upper semicontinuous: `{x | a ≤ σ(x)}` is closed. -/
theorem isClosed_le_sel (a : ℝ) : IsClosed {x | a ≤ sel g h q x} := by
  refine isSeqClosed_iff_isClosed.1 fun xs x hxs hlim => ?_
  have hmem : ∀ n, sel g h q (xs n) ∈ Icc (g (xs n)) (h (xs n)) := fun n =>
    (sel_mem hgh hq (xs n)).1
  obtain ⟨φ, hφ, c, hc, hcφ⟩ := exists_subseq_Icc hg hh hlim hmem
  have hxφ : Tendsto (xs ∘ φ) atTop (𝓝 x) := hlim.comp hφ.tendsto_atTop
  have hcmax : c ∈ argmax g h q x := by
    refine ⟨hc, fun b hb => ?_⟩
    -- clamp `b` into the feasible intervals along the subsequence
    let bs : ℕ → ℝ := fun k => max (g (xs (φ k))) (min b (h (xs (φ k))))
    have hbs : Tendsto bs atTop (𝓝 b) := by
      have := ((hg.tendsto x).comp hxφ).max
        ((tendsto_const_nhds (x := b)).min ((hh.tendsto x).comp hxφ))
      rwa [clamp_eq hb] at this
    have hG1 : Tendsto (fun k => ((xs ∘ φ) k, bs k)) atTop
        (𝓝[{p : X × ℝ | p.2 ∈ Icc (g p.1) (h p.1)}] (x, b)) :=
      tendsto_nhdsWithin_iff.2 ⟨hxφ.prodMk_nhds hbs, Eventually.of_forall fun k =>
        clamp_mem (hgh _) b⟩
    have hG2 : Tendsto (fun k => ((xs ∘ φ) k, sel g h q (xs (φ k)))) atTop
        (𝓝[{p : X × ℝ | p.2 ∈ Icc (g p.1) (h p.1)}] (x, c)) :=
      tendsto_nhdsWithin_iff.2 ⟨hxφ.prodMk_nhds hcφ, Eventually.of_forall fun k => hmem _⟩
    exact le_of_tendsto_of_tendsto' ((hq (x, b) hb).tendsto.comp hG1)
      ((hq (x, c) hc).tendsto.comp hG2) fun k =>
        (sel_mem hgh hq (xs (φ k))).2 _ (clamp_mem (hgh _) b)
  have hac : a ≤ c := ge_of_tendsto' hcφ fun k => hxs (φ k)
  exact hac.trans (le_csSup ⟨h x, fun _ ha => ha.1.2⟩ hcmax)

omit hg hh hgh hq in
/-- Points of `[g(x), h(x)]` as `g(x) + t(h(x) − g(x))` with `t ∈ [0, 1]`. -/
theorem exists_param {gx hx a : ℝ} (ha : a ∈ Icc gx hx) :
    ∃ t ∈ Icc (0 : ℝ) 1, gx + max 0 (min t 1) * (hx - gx) = a := by
  rcases eq_or_lt_of_le (ha.1.trans ha.2) with heq | hlt
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    have : a = gx := le_antisymm (ha.2.trans heq.symm.le) ha.1
    simp [this]
  · refine ⟨(a - gx) / (hx - gx), ⟨div_nonneg (sub_nonneg.2 ha.1) (sub_pos.2 hlt).le,
      (div_le_one (sub_pos.2 hlt)).2 (sub_le_sub_right ha.2 _)⟩, ?_⟩
    have h0 : 0 ≤ (a - gx) / (hx - gx) := div_nonneg (sub_nonneg.2 ha.1) (sub_pos.2 hlt).le
    have h1 : (a - gx) / (hx - gx) ≤ 1 := (div_le_one (sub_pos.2 hlt)).2 (sub_le_sub_right ha.2 _)
    rw [min_eq_left h1, max_eq_right h0, div_mul_cancel₀ _ (sub_pos.2 hlt).ne']
    ring

omit [SequentialSpace X] in
/-- The maximum `m(x) = q(x, σ(x))` is continuous (Berge). -/
theorem continuous_max : Continuous fun x => q (x, sel g h q x) := by
  let κ : X × ℝ → X × ℝ := fun p => (p.1, g p.1 + max 0 (min p.2 1) * (h p.1 - g p.1))
  have hκ : Continuous κ := continuous_fst.prodMk ((hg.comp continuous_fst).add
    ((continuous_const.max (continuous_snd.min continuous_const)).mul
      ((hh.comp continuous_fst).sub (hg.comp continuous_fst))))
  have hκG : ∀ p, κ p ∈ {p : X × ℝ | p.2 ∈ Icc (g p.1) (h p.1)} := fun p => by
    have ht0 : 0 ≤ max 0 (min p.2 1) := le_max_left _ _
    have ht1 : max 0 (min p.2 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
    have hd : 0 ≤ h p.1 - g p.1 := sub_nonneg.2 (hgh p.1)
    exact ⟨le_add_of_nonneg_right (mul_nonneg ht0 hd), by nlinarith⟩
  have hQ : Continuous (q ∘ κ) := hq.comp_continuous hκ hκG
  have hm := isCompact_Icc.continuous_sSup (f := fun (x : X) (t : ℝ) => (q ∘ κ) (x, t))
    (K := Icc (0 : ℝ) 1) hQ
  refine hm.congr fun x => ?_
  -- the supremum over `t` is attained at the largest maximizer
  have hs := sel_mem hgh hq x
  obtain ⟨t₀, ht₀, ht₀eq⟩ := exists_param hs.1
  refine (IsGreatest.csSup_eq ⟨⟨t₀, ht₀, ?_⟩, ?_⟩)
  · simp only [Function.comp_apply, κ]
    rw [ht₀eq]
  · rintro _ ⟨t, -, rfl⟩
    exact hs.2 _ (hκG (x, t))

/-- The largest maximizer is Borel. -/
theorem measurable_sel [MeasurableSpace X] [OpensMeasurableSpace X] :
    Measurable (sel g h q) :=
  measurable_of_Ici fun a => (isClosed_le_sel hg hh hgh hq a).measurableSet

end IccMax

/-- **Theorem A.3.3** for the interval correspondences of Exercise A.3.1: if `g ≤ h` are
continuous, then `Γ(x) = [g(x), h(x)]` has measurable maximizing selections with continuous
maximum. -/
theorem hasMaxSelections_Icc [TopologicalSpace X] [SequentialSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    {g h : X → ℝ} (hg : Continuous g) (hh : Continuous h) (hgh : ∀ x, g x ≤ h x) :
    HasMaxSelections fun x => Icc (g x) (h x) := fun q hq =>
  ⟨IccMax.sel g h q, IccMax.measurable_sel hg hh hgh hq, fun x => (IccMax.sel_mem hgh hq x).1,
    fun x a ha => (IccMax.sel_mem hgh hq x).2 a ha, IccMax.continuous_max hg hh hgh hq⟩

end SargentStachurski.RecursiveDecisionProcesses
