/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.MonotoneOperators

/-!
# Total-variation continuity of a transition function (Assumption 17.3) and its consequences

SLP §17.4, pp. 520–522, as used in §17.5 (general application, p. 529, and Proposition 5,
p. 530). These are the facts about operators `(Tf)(x) = ∫ G[x, x', f(x')] π(x, dx')` that the
monotone-operator results of §17.5 need; they are proved here from scratch so that the §17.5
modules are self-contained.

* `IsFinMeasPartition`, `TVDistLE`: `‖μ − ν‖_TV ≤ ε` in the book's sense (p. 521, as in
  §11.3): `Σᵢ |μ(Aᵢ) − ν(Aᵢ)| ≤ ε` for every finite measurable partition `{Aᵢ}` of `X`.
* **Assumption 17.3** (`MonoAssumption17_3`, pp. 520–521): `x ↦ π(x, ·)` is uniformly
  continuous in the total-variation norm. (The book's `< ε` for all `ε` is equivalent to
  `≤ ε` for all `ε`; the boundedness of `X` is imposed separately where it is used.)
* `abs_integral_sub_le_of_tvDistLE`: `|∫ h dμ − ∫ h dν| ≤ c ‖μ − ν‖_TV` for `|h| ≤ c` measurable,
  the inequality `|∫ h dλ| ≤ sup|h| · ‖λ‖_TV` quoted on p. 521. The proof uses the Hahn
  decomposition: the two-set partition `{s, sᶜ}` already attains the bound.
* `uniformEquicontinuous_integral`: under Assumption 17.3, `{x ↦ ∫ g_i dπ(x, ·)}` is uniformly
  equicontinuous for any uniformly bounded family of measurable `g_i`
  (Lemma 17.5 with `G` independent of `x`); `continuous_integral_of_assumption17_3` for one `g`.
* **Lemma 17.5** (`kernelIntegral_uniformEquicontinuous`, p. 521): the family `T(F)` is
  equicontinuous when `G` is continuous on `X × X × D`, bounded on it, and uniformly continuous
  in its first argument.
* **Exercise 17.6** (`kernelIntegral_dist_le`, p. 522): if moreover `G` is uniformly continuous in
  its third argument (uniformly over `(x, x')`), `f ↦ Tf` is uniformly continuous in the sup
  norm on `F`.
* `kernelOp`: the operator `T` as a map `C(X) → C(X)`; `kernelOp_apply` (the formula on `F`) and
  `kernelOp_apply_of_continuous`.
* **General application of Theorem 17.7** (`kernelOp_monotone_fixedPoints`, p. 529): for
  `D = [c, d]`, `G : X × X × D → D` continuous, uniformly continuous in its first and third
  arguments and nondecreasing in its third, `F = {f : X → D}` is closed and bounded, `T` maps `F`
  to itself continuously and monotonically, `T(F)` is equicontinuous, and iterating from the
  constants `c` and `d` gives the least and greatest fixed points of `T` in `F`.

The facts of this file overlap the §17.4 modules (Lemma 17.5, Exercise 17.6 there); they are
reproved here, with their own names, so that the §17.5 modules do not depend on §17.4.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

/-- A finite measurable partition `A₀, …, A_{n-1}` of `X`. -/
def IsFinMeasPartition {n : ℕ} (A : Fin n → Set X) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ Pairwise (Function.onFun Disjoint A) ∧ (⋃ i, A i) = univ

/-- `‖μ − ν‖_TV ≤ ε` for the book's total-variation norm (SLP p. 521, §11.3): every finite
measurable partition `{Aᵢ}` of `X` has `Σᵢ |μ(Aᵢ) − ν(Aᵢ)| ≤ ε`. -/
def TVDistLE (μ ν : Measure X) (ε : ℝ) : Prop :=
  ∀ (n : ℕ) (A : Fin n → Set X), IsFinMeasPartition A →
    ∑ i, |μ.real (A i) - ν.real (A i)| ≤ ε

/-- **Assumption 17.3** (SLP pp. 520–521): for every `ε > 0` there is `δ > 0` such that
`d(x, x̂) < δ` implies `‖π(x, ·) − π(x̂, ·)‖_TV ≤ ε`. -/
def MonoAssumption17_3 [PseudoMetricSpace X] (π : Kernel X X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x x', dist x x' < δ → TVDistLE (π x) (π x') ε

/-- A two-set partition `{s, sᶜ}` of `X`. -/
theorem isFinMeasPartition_pair {s : Set X} (hs : MeasurableSet s) :
    IsFinMeasPartition ![s, sᶜ] := by
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
  · fin_cases i
    · exact hs
    · exact hs.compl
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact disjoint_compl_right
    · exact disjoint_compl_left
    · exact absurd rfl hij
  · ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    by_cases hx : x ∈ s
    · exact ⟨0, by simpa using hx⟩
    · exact ⟨1, by simpa using hx⟩

/-- If `ν ≤ μ` are finite measures and `|h| ≤ c`, then
`|∫ h dμ − ∫ h dν| ≤ c (μ(X) − ν(X))`. -/
theorem abs_integral_sub_le_of_le {μ ν : Measure X} [IsFiniteMeasure μ] (hνμ : ν ≤ μ)
    {h : X → ℝ} (hm : Measurable h) {c : ℝ} (hc : ∀ x, |h x| ≤ c) :
    |∫ x, h x ∂μ - ∫ x, h x ∂ν| ≤ c * (μ.real univ - ν.real univ) := by
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hνμ
  have e : μ - ν + ν = μ := Measure.sub_add_cancel_of_le hνμ
  have hint : ∀ ρ : Measure X, IsFiniteMeasure ρ → Integrable h ρ := fun ρ _ =>
    Integrable.of_bound hm.aestronglyMeasurable c (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hc x)
  have hsplit : ∫ x, h x ∂μ = ∫ x, h x ∂(μ - ν) + ∫ x, h x ∂ν := by
    conv_lhs => rw [← e]
    exact integral_add_measure (hint _ inferInstance) (hint _ inferInstance)
  have hreal : μ.real univ = (μ - ν).real univ + ν.real univ := by
    conv_lhs => rw [← e]
    exact measureReal_add_apply
  rw [hsplit, add_sub_cancel_right, hreal, add_sub_cancel_right, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hc x)

/-- `|∫ h dμ − ∫ h dν| ≤ c ‖μ − ν‖_TV` for measurable `h` with `|h| ≤ c` and finite `μ, ν`
(SLP p. 521: `|∫ h dλ| ≤ sup|h| · ‖λ‖_TV`). -/
theorem abs_integral_sub_le_of_tvDistLE {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {h : X → ℝ} (hm : Measurable h) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x, |h x| ≤ c) {ε : ℝ} (hTV : TVDistLE μ ν ε) :
    |∫ x, h x ∂μ - ∫ x, h x ∂ν| ≤ c * ε := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have hsm := hs.measurableSet
  have hint : ∀ ρ : Measure X, IsFiniteMeasure ρ → Integrable h ρ := fun ρ _ =>
    Integrable.of_bound hm.aestronglyMeasurable c (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hc x)
  have h1 := abs_integral_sub_le_of_le hs.le_on hm hc
  have h2 := abs_integral_sub_le_of_le hs.ge_on_compl hm hc
  rw [measureReal_restrict_apply_univ, measureReal_restrict_apply_univ] at h1 h2
  have hpart := hTV 2 ![s, sᶜ] (isFinMeasPartition_pair hsm)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hpart
  have hsplit : ∫ x, h x ∂μ - ∫ x, h x ∂ν = -(∫ x in s, h x ∂ν - ∫ x in s, h x ∂μ) +
      (∫ x in sᶜ, h x ∂μ - ∫ x in sᶜ, h x ∂ν) := by
    rw [← integral_add_compl hsm (hint μ inferInstance),
      ← integral_add_compl hsm (hint ν inferInstance)]
    ring
  rw [hsplit]
  calc |-(∫ x in s, h x ∂ν - ∫ x in s, h x ∂μ) + (∫ x in sᶜ, h x ∂μ - ∫ x in sᶜ, h x ∂ν)|
      ≤ |∫ x in s, h x ∂ν - ∫ x in s, h x ∂μ| + |∫ x in sᶜ, h x ∂μ - ∫ x in sᶜ, h x ∂ν| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ ≤ c * (ν.real s - μ.real s) + c * (μ.real sᶜ - ν.real sᶜ) := add_le_add h1 h2
    _ ≤ c * (|μ.real s - ν.real s| + |μ.real sᶜ - ν.real sᶜ|) := by
        rw [mul_add]
        gcongr
        · rw [abs_sub_comm]; exact le_abs_self _
        · exact le_abs_self _
    _ ≤ c * ε := by gcongr

variable [PseudoMetricSpace X]

/-- Under Assumption 17.3, for any family of measurable functions `gᵢ` with `|gᵢ| ≤ c`, the
conditional expectations `x ↦ ∫ gᵢ(x') π(x, dx')` form a uniformly equicontinuous family
(Lemma 17.5 for a kernel `G` not depending on `x`). -/
theorem uniformEquicontinuous_integral {π : Kernel X X} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) {ι : Type*} {g : ι → X → ℝ} (hg : ∀ i, Measurable (g i))
    {c : ℝ} (hc : ∀ i x, |g i x| ≤ c) :
    UniformEquicontinuous fun i x => ∫ x', g i x' ∂(π x) := by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  have hc' : 0 < |c| + 1 := by positivity
  obtain ⟨δ, hδ, hπδ⟩ := hπ (ε / (|c| + 1)) (by positivity)
  refine ⟨δ, hδ, fun x y hxy i => ?_⟩
  rw [Real.dist_eq]
  calc |∫ x', g i x' ∂(π x) - ∫ x', g i x' ∂(π y)|
      ≤ |c| * (ε / (|c| + 1)) :=
        abs_integral_sub_le_of_tvDistLE (hg i) (abs_nonneg c)
          (fun x => (hc i x).trans (le_abs_self c)) (hπδ x y hxy)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hc']
        nlinarith [abs_nonneg c]

/-- Under Assumption 17.3, `x ↦ ∫ g(x') π(x, dx')` is continuous for bounded measurable `g`. -/
theorem continuous_integral_of_assumption17_3 {π : Kernel X X} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) {g : X → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : ∀ x, |g x| ≤ c) : Continuous fun x => ∫ x', g x' ∂(π x) := by
  have := uniformEquicontinuous_integral hπ (ι := Unit) (g := fun _ => g) (fun _ => hg)
    (fun _ => hc)
  exact (this.uniformContinuous ()).continuous

/-- **Lemma 17.5** (SLP p. 521). Let `π` satisfy Assumption 17.3, `D ⊆ ℝ`, and
`F = {f ∈ C(X) : f(X) ⊆ D}`. Let `G : X × X × D → ℝ` be continuous, bounded by `B`, and
uniformly continuous in its first argument (uniformly in `x', y`). Then the family of functions
`x ↦ ∫ G[x, x', f(x')] π(x, dx')`, `f ∈ F`, is uniformly equicontinuous. -/
theorem kernelIntegral_uniformEquicontinuous [OpensMeasurableSpace X] {π : Kernel X X}
    [IsMarkovKernel π] (hπ : MonoAssumption17_3 π) {D : Set ℝ} {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    {B : ℝ} (hGb : ∀ x x' y, y ∈ D → |G x x' y| ≤ B)
    (hG1 : ∀ ε > 0, ∃ δ > 0, ∀ x z, dist x z < δ → ∀ x' y, y ∈ D →
      |G x x' y - G z x' y| < ε) :
    UniformEquicontinuous fun f : {f : X →ᵇ ℝ // ∀ x, f x ∈ D} =>
      fun x => ∫ x', G x x' (f.1 x') ∂(π x) := by
  have hmeas : ∀ (f : {f : X →ᵇ ℝ // ∀ x, f x ∈ D}) (x : X),
      Measurable fun x' => G x x' (f.1 x') := by
    intro f x
    refine (hGc.comp_continuous (f := fun x' => (x, x', f.1 x'))
      (continuous_const.prodMk (continuous_id.prodMk f.1.continuous)) fun x' => ?_).measurable
    exact ⟨mem_univ _, mem_univ _, f.2 x'⟩
  have hint : ∀ (f : {f : X →ᵇ ℝ // ∀ x, f x ∈ D}) (x z : X),
      Integrable (fun x' => G x x' (f.1 x')) (π z) := fun f x z =>
    Integrable.of_bound (hmeas f x).aestronglyMeasurable B (Eventually.of_forall fun x' => by
      rw [Real.norm_eq_abs]; exact hGb _ _ _ (f.2 x'))
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hG1δ⟩ := hG1 (ε / 2) (by positivity)
  have hB : 0 < |B| + 1 := by positivity
  obtain ⟨δ₂, hδ₂, hπδ⟩ := hπ (ε / (2 * (|B| + 1))) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x y hxy f => ?_⟩
  rw [Real.dist_eq]
  have e1 : |∫ x', G x x' (f.1 x') ∂(π x) - ∫ x', G y x' (f.1 x') ∂(π x)| ≤ ε / 2 := by
    rw [← integral_sub (hint f x x) (hint f y x), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ε / 2)
      (Eventually.of_forall fun x' => ?_)).trans (by simp)
    rw [Real.norm_eq_abs]
    exact (hG1δ x y (lt_of_lt_of_le hxy (min_le_left _ _)) x' _ (f.2 x')).le
  have e2 : |∫ x', G y x' (f.1 x') ∂(π x) - ∫ x', G y x' (f.1 x') ∂(π y)| ≤
      |B| * (ε / (2 * (|B| + 1))) :=
    abs_integral_sub_le_of_tvDistLE (hmeas f y) (abs_nonneg B)
      (fun x' => (hGb _ _ _ (f.2 x')).trans (le_abs_self B))
      (hπδ x y (lt_of_lt_of_le hxy (min_le_right _ _)))
  have e3 : |B| * (ε / (2 * (|B| + 1))) < ε / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith [abs_nonneg B]
  calc |∫ x', G x x' (f.1 x') ∂(π x) - ∫ x', G y x' (f.1 x') ∂(π y)|
      ≤ |∫ x', G x x' (f.1 x') ∂(π x) - ∫ x', G y x' (f.1 x') ∂(π x)| +
        |∫ x', G y x' (f.1 x') ∂(π x) - ∫ x', G y x' (f.1 x') ∂(π y)| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt e1 (e2.trans_lt e3)
    _ = ε := add_halves ε

/-- Integrands `x' ↦ G[x, x', f(x')]` are measurable for `f ∈ F` when `G` is continuous on
`X × X × D`. -/
theorem measurable_kernelIntegrand [OpensMeasurableSpace X] {D : Set ℝ} {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    {f : X →ᵇ ℝ} (hf : ∀ x, f x ∈ D) (x : X) : Measurable fun x' => G x x' (f x') :=
  (hGc.comp_continuous (f := fun x' => (x, x', f x'))
    (continuous_const.prodMk (continuous_id.prodMk f.continuous))
    fun x' => ⟨mem_univ _, mem_univ _, hf x'⟩).measurable

/-- **Exercise 17.6** (SLP p. 522). If in addition `G` is uniformly continuous in its third
argument, uniformly over `(x, x')`, then `f ↦ Tf` is uniformly continuous on `F` for the sup norm:
`‖f − g‖ < δ` implies `|(Tf)(x) − (Tg)(x)| ≤ ε` for all `x`. -/
theorem kernelIntegral_dist_le [OpensMeasurableSpace X] {π : Kernel X X} [IsMarkovKernel π]
    {D : Set ℝ} {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    {B : ℝ} (hGb : ∀ x x' y, y ∈ D → |G x x' y| ≤ B)
    (hG3 : ∀ ε > 0, ∃ δ > 0, ∀ x x' y y', y ∈ D → y' ∈ D → |y - y'| < δ →
      |G x x' y - G x x' y'| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ f g : X →ᵇ ℝ, (∀ x, f x ∈ D) → (∀ x, g x ∈ D) → dist f g < δ →
      ∀ x, |∫ x', G x x' (f x') ∂(π x) - ∫ x', G x x' (g x') ∂(π x)| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hG3δ⟩ := hG3 ε hε
  refine ⟨δ, hδ, fun f g hf hg hfg x => ?_⟩
  have hint : ∀ {k : X →ᵇ ℝ}, (∀ x, k x ∈ D) → Integrable (fun x' => G x x' (k x')) (π x) :=
    fun {k} hk => Integrable.of_bound (measurable_kernelIntegrand hGc hk x).aestronglyMeasurable
      B (Eventually.of_forall fun x' => by rw [Real.norm_eq_abs]; exact hGb _ _ _ (hk x'))
  rw [← integral_sub (hint hf) (hint hg), ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ε) (Eventually.of_forall fun x' => ?_)).trans
    (by simp)
  rw [Real.norm_eq_abs]
  refine (hG3δ x x' _ _ (hf x') (hg x') ?_).le
  rw [← Real.dist_eq]
  exact lt_of_le_of_lt (dist_coe_le_dist x') hfg

open Classical in
/-- The operator `(Tf)(x) = ∫ G[x, x', f(x')] π(x, dx')` of SLP §17.4 (1) and p. 529, as a map
`C(X) → C(X)`. Where the right side is not a bounded continuous function of `x` (which can
happen only off the set `F` of the book), the value is `0`; the book's `T` is defined only on
`F`, where `kernelOp_apply` shows that the formula holds. -/
noncomputable def kernelOp (π : Kernel X X) (G : X → X → ℝ → ℝ) (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  if h : Continuous (fun x => ∫ x', G x x' (f x') ∂(π x)) ∧
      ∃ C, ∀ x y, dist (∫ x', G x x' (f x') ∂(π x)) (∫ x', G y x' (f x') ∂(π y)) ≤ C then
    BoundedContinuousFunction.mkOfBound ⟨_, h.1⟩ h.2.choose h.2.choose_spec
  else 0

/-- `kernelOp` is given by its formula whenever the formula defines a continuous function
bounded by `B`. -/
theorem kernelOp_apply_of_continuous {π : Kernel X X} {G : X → X → ℝ → ℝ} {f : X →ᵇ ℝ}
    (hc : Continuous fun x => ∫ x', G x x' (f x') ∂(π x)) {B : ℝ}
    (hb : ∀ x, |∫ x', G x x' (f x') ∂(π x)| ≤ B) (x : X) :
    kernelOp π G f x = ∫ x', G x x' (f x') ∂(π x) := by
  have h : Continuous (fun x => ∫ x', G x x' (f x') ∂(π x)) ∧
      ∃ C, ∀ x y, dist (∫ x', G x x' (f x') ∂(π x)) (∫ x', G y x' (f x') ∂(π y)) ≤ C :=
    ⟨hc, 2 * B, fun x y => by
      rw [Real.dist_eq]
      linarith [abs_sub (∫ x', G x x' (f x') ∂(π x)) (∫ x', G y x' (f x') ∂(π y)), hb x, hb y]⟩
  simp only [kernelOp, h]
  rfl

/-- Under Assumption 17.3, for `f ∈ F` the operator `kernelOp` is given by its formula. -/
theorem kernelOp_apply [OpensMeasurableSpace X] {π : Kernel X X} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) {D : Set ℝ} {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    {B : ℝ} (hGb : ∀ x x' y, y ∈ D → |G x x' y| ≤ B)
    (hG1 : ∀ ε > 0, ∃ δ > 0, ∀ x z, dist x z < δ → ∀ x' y, y ∈ D →
      |G x x' y - G z x' y| < ε) {f : X →ᵇ ℝ} (hf : ∀ x, f x ∈ D) (x : X) :
    kernelOp π G f x = ∫ x', G x x' (f x') ∂(π x) := by
  have heq := kernelIntegral_uniformEquicontinuous hπ hGc hGb hG1
  refine kernelOp_apply_of_continuous ((heq.uniformContinuous ⟨f, hf⟩).continuous) (B := B)
    (fun x => ?_) x
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := B) (Eventually.of_forall fun x' => ?_)).trans
    (by simp)
  rw [Real.norm_eq_abs]
  exact hGb _ _ _ (hf x')

/-- **General application of Theorem 17.7** (SLP p. 529). Let `X` be totally bounded, `π`
satisfy Assumption 17.3, `D = [c, d]`, `F = {f ∈ C(X) : f(X) ⊆ D}`, and
`G : X × X × D → D` continuous, uniformly continuous in its first and third arguments and weakly
increasing in its third argument. Then `T = kernelOp π G` maps `F` into itself, is continuous and
monotone on `F`, and `T(F)` is equicontinuous; `F` is closed and bounded, with least element
`c` and greatest element `d`. Hence (Theorem 17.7 and its Corollary) `Tⁿc → f` and `Tⁿd → g` in
`C(X)`, `f` and `g` are fixed points in `F`, and every fixed point `h ∈ F` has `f ≤ h ≤ g`. -/
theorem kernelOp_monotone_fixedPoints [OpensMeasurableSpace X]
    (hX : TotallyBounded (univ : Set X)) {π : Kernel X X} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) {c d : ℝ} (hcd : c ≤ d) {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ Icc c d))
    (hGD : ∀ x x' y, y ∈ Icc c d → G x x' y ∈ Icc c d)
    (hG1 : ∀ ε > 0, ∃ δ > 0, ∀ x z, dist x z < δ → ∀ x' y, y ∈ Icc c d →
      |G x x' y - G z x' y| < ε)
    (hG3 : ∀ ε > 0, ∃ δ > 0, ∀ x x' y y', y ∈ Icc c d → y' ∈ Icc c d → |y - y'| < δ →
      |G x x' y - G x x' y'| < ε)
    (hGmono : ∀ x x' y y', y ∈ Icc c d → y' ∈ Icc c d → y ≤ y' → G x x' y ≤ G x x' y') :
    let F : Set (X →ᵇ ℝ) := {f | ∀ x, f x ∈ Icc c d}
    IsClosed F ∧ Bornology.IsBounded F ∧ MapsTo (kernelOp π G) F F ∧
      ContinuousOn (kernelOp π G) F ∧ MonotoneOn (kernelOp π G) F ∧
      UniformEquicontinuous (fun f : F => ⇑(kernelOp π G f)) ∧
      IsLeast F (const X c) ∧ IsGreatest F (const X d) ∧
      ∃ f ∈ F, ∃ g ∈ F, kernelOp π G f = f ∧ kernelOp π G g = g ∧
        Tendsto (fun n => (kernelOp π G)^[n] (const X c)) atTop (𝓝 f) ∧
        Tendsto (fun n => (kernelOp π G)^[n] (const X d)) atTop (𝓝 g) ∧
        ∀ h ∈ F, kernelOp π G h = h → f ≤ h ∧ h ≤ g := by
  intro F
  set B := max |c| |d| with hB
  have hGb : ∀ x x' y, y ∈ Icc c d → |G x x' y| ≤ B := fun x x' y hy => by
    have := hGD x x' y hy
    exact abs_le.2 ⟨by rw [hB]; linarith [neg_abs_le c, le_max_left |c| |d|, this.1],
      by rw [hB]; linarith [le_abs_self d, le_max_right |c| |d|, this.2]⟩
  have happ : ∀ f ∈ F, ∀ x, kernelOp π G f x = ∫ x', G x x' (f x') ∂(π x) :=
    fun f hf x => kernelOp_apply hπ hGc hGb hG1 hf x
  have hint : ∀ f ∈ F, ∀ x, Integrable (fun x' => G x x' (f x')) (π x) := fun f hf x =>
    Integrable.of_bound (measurable_kernelIntegrand hGc hf x).aestronglyMeasurable B
      (Eventually.of_forall fun x' => by rw [Real.norm_eq_abs]; exact hGb _ _ _ (hf x'))
  have hFc : IsClosed F := by
    have : F = ⋂ x, (fun f : X →ᵇ ℝ => f x) ⁻¹' Icc c d := by ext f; simp [F]
    rw [this]
    exact isClosed_iInter fun x => isClosed_Icc.preimage (continuous_eval_const x)
  have hFb : Bornology.IsBounded F := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨B, fun f hf => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (BoundedContinuousFunction.norm_le (le_trans (abs_nonneg c) (le_max_left _ _))).2
      fun x => ?_
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [neg_abs_le c, le_max_left |c| |d|, (hf x).1],
      by linarith [le_abs_self d, le_max_right |c| |d|, (hf x).2]⟩
  have hmaps : MapsTo (kernelOp π G) F F := fun f hf x => by
    rw [happ f hf x]
    constructor
    · calc c = ∫ _, c ∂(π x) := by simp
        _ ≤ _ := integral_mono (integrable_const c) (hint f hf x) fun x' => (hGD _ _ _ (hf x')).1
    · calc ∫ x', G x x' (f x') ∂(π x) ≤ ∫ _, d ∂(π x) :=
            integral_mono (hint f hf x) (integrable_const d) fun x' => (hGD _ _ _ (hf x')).2
        _ = d := by simp
  have hcont : ContinuousOn (kernelOp π G) F := by
    rw [Metric.continuousOn_iff]
    intro f hf ε hε
    obtain ⟨δ, hδ, hδ'⟩ := kernelIntegral_dist_le (π := π) hGc hGb hG3 (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun g hg hgf => ?_⟩
    refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity)).2 fun x => ?_)
      (half_lt_self hε)
    rw [happ g hg, happ f hf, Real.dist_eq]
    exact hδ' g f hg hf hgf x
  have hmono : MonotoneOn (kernelOp π G) F := fun f hf g hg hfg x => by
    change kernelOp π G f x ≤ kernelOp π G g x
    rw [happ f hf, happ g hg]
    exact integral_mono (hint f hf x) (hint g hg x) fun x' =>
      hGmono _ _ _ _ (hf x') (hg x') (hfg x')
  have hequi : UniformEquicontinuous (fun f : F => ⇑(kernelOp π G f)) := by
    have e : (fun f : F => ⇑(kernelOp π G f)) =
        fun f : F => fun x => ∫ x', G x x' (f.1 x') ∂(π x) := by
      funext f x
      exact happ f.1 f.2 x
    rw [e]
    exact kernelIntegral_uniformEquicontinuous hπ hGc hGb hG1
  have hleast : IsLeast F (const X c) :=
    ⟨fun x => ⟨le_rfl, hcd⟩, fun f hf x => (hf x).1⟩
  have hgreatest : IsGreatest F (const X d) :=
    ⟨fun x => ⟨hcd, le_rfl⟩, fun f hf x => (hf x).2⟩
  exact ⟨hFc, hFb, hmaps, hcont, hmono, hequi, hleast, hgreatest,
    corollary_17_7 hX hFc hFb hmaps hcont hmono hequi hleast hgreatest⟩

end StokeyLucasPrescott.FixedPointArguments
