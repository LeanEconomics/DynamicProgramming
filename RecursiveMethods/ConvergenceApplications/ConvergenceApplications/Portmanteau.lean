/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.WeakBasics

/-!
# Characterizations of weak convergence

SLP §12.1, Theorem 12.3, pp. 358–360. For probability measures `λₙ`, `λ` on a metric space the
following are equivalent (`theorem_12_3`):

* (a) `λₙ ⇒ λ`;
* (b) `limsup λₙ(F) ≤ λ(F)` for closed `F`;
* (c) `liminf λₙ(G) ≥ λ(G)` for open `G`;
* (d) `λₙ(A) → λ(A)` whenever `λ(∂A) = 0`.

`limsup ≤` and `liminf ≥` are written as: for every `ε > 0`, eventually `λₙ(F) < λ(F) + ε`
(`LimsupLe`), respectively `λₙ(G) > λ(G) − ε`. The proofs follow the book: (a) ⇒ (b) by
Lemma 12.1, (b) ⇒ (a) by Lemma 12.2, (b) ⇔ (c) by complements, (b) ⇒ (d) through the interior and
the closure, and (d) ⇒ (b) through thickenings with null boundaries.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-- `limsup uₙ ≤ c`, written without `limsup`. -/
def LimsupLe (u : ℕ → ℝ) (c : ℝ) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, u n < c + ε

/-- `liminf uₙ ≥ c`, written without `liminf`. -/
def LiminfGe (u : ℕ → ℝ) (c : ℝ) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, c - ε < u n

theorem tendsto_of_limsup_liminf {u : ℕ → ℝ} {c : ℝ} (h1 : LimsupLe u c) (h2 : LiminfGe u c) :
    Tendsto u atTop (𝓝 c) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [h2 (c - a) (by linarith)] with n hn; linarith
  · filter_upwards [h1 (a - c) (by linarith)] with n hn; linarith

/-- A continuous function with values in `[0, 1]` as a bounded continuous function. -/
noncomputable def toBCF {f : S → ℝ} (hc : Continuous f) (h : ∀ s, 0 ≤ f s ∧ f s ≤ 1) : S →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨f, hc⟩ 1 fun x y => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]; constructor <;> linarith [h x, h y]

/-- (a) ⇒ (b). -/
theorem limsup_closed_of_weak {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] (h : ConvWeak ls l) {F : Set S}
    (hF : IsClosed F) : LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  obtain ⟨f, hc, -, h1, h01, hlim⟩ := lemma_12_1 hF
  obtain ⟨m, hm⟩ := ((hlim l).eventually (gt_mem_nhds (show l.real F < l.real F + ε / 2 by
    linarith))).exists
  set g := toBCF (hc m) (h01 m)
  have hint : ∀ (μ : Measure S) [IsProbabilityMeasure μ], μ.real F ≤ ∫ s, g s ∂μ := by
    intro μ _
    rw [← integral_indicator_one hF.measurableSet]
    refine integral_mono (integrable_const (1 : ℝ) |>.indicator hF.measurableSet)
      (g.integrable μ) fun s => ?_
    by_cases hs : s ∈ F
    · simp [indicator_of_mem hs, g, toBCF, h1 m s hs]
    · simp [indicator_of_notMem hs, g, toBCF, (h01 m s).1]
  filter_upwards [(h g).eventually (gt_mem_nhds (show ∫ s, g s ∂l < l.real F + ε by
    change ∫ s, f m s ∂l < _; linarith))] with n hn
  exact (hint (ls n)).trans_lt hn

/-- The upper half of (b) ⇒ (a), through Lemma 12.2. -/
theorem limsup_integral_of_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) (g : S →ᵇ ℝ) :
    LimsupLe (fun n => ∫ s, g s ∂ls n) (∫ s, g s ∂l) := by
  intro ε hε
  set a := -‖g‖ - 1
  set b := ‖g‖ + 1
  have hab : ∀ s, a ≤ g s ∧ g s < b := fun s => by
    have := abs_le.1 ((Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm s)
    constructor <;> linarith
  have hc : 0 < b - a := by simp only [a, b]; linarith [norm_nonneg g]
  obtain ⟨k, hk, F, -, hFc, hF⟩ :=
    lemma_12_2 g.continuous.measurable hab (ε := ε / 3) (by positivity)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set δ := ε / (3 * (b - a))
  have hδ : 0 < δ := by positivity
  have hev : ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc 1 k, (ls n).real (F i) < l.real (F i) + δ :=
    (Filter.eventually_all_finset _).2 fun i _ => hb (F i) (hFc g.continuous i) δ hδ
  filter_upwards [hev] with n hn
  obtain ⟨-, hup⟩ := hF (ls n)
  obtain ⟨hlo, -⟩ := hF l
  have hsum : ∑ i ∈ Finset.Icc 1 k, (ls n).real (F i) ≤
      ∑ i ∈ Finset.Icc 1 k, l.real (F i) + k * δ := by
    calc _ ≤ ∑ i ∈ Finset.Icc 1 k, (l.real (F i) + δ) :=
          Finset.sum_le_sum fun i hi => (hn i hi).le
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  have hkδ : (b - a) / k * (k * δ) = ε / 3 := by
    simp only [δ]; field_simp
  have := mul_le_mul_of_nonneg_left hsum (div_nonneg hc.le hk'.le)
  rw [mul_add, hkδ] at this
  linarith

/-- (b) ⇒ (a). -/
theorem weak_of_limsup_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) : ConvWeak ls l := by
  intro g
  refine tendsto_of_limsup_liminf (limsup_integral_of_closed hb g) fun ε hε => ?_
  filter_upwards [limsup_integral_of_closed hb (-g) ε hε] with n hn
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply, integral_neg] at hn
  linarith

/-- (b) ⇒ (c), by complements. -/
theorem liminf_open_of_limsup_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) {G : Set S}
    (hG : IsOpen G) : LiminfGe (fun n => (ls n).real G) (l.real G) := by
  intro ε hε
  filter_upwards [hb Gᶜ hG.isClosed_compl ε hε] with n hn
  rw [probReal_compl_eq_one_sub hG.measurableSet,
    probReal_compl_eq_one_sub hG.measurableSet] at hn
  linarith

/-- (c) ⇒ (b), by complements. -/
theorem limsup_closed_of_liminf_open {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hc : ∀ G, IsOpen G → LiminfGe (fun n => (ls n).real G) (l.real G)) {F : Set S}
    (hF : IsClosed F) : LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  filter_upwards [hc Fᶜ hF.isOpen_compl ε hε] with n hn
  rw [probReal_compl_eq_one_sub hF.measurableSet,
    probReal_compl_eq_one_sub hF.measurableSet] at hn
  linarith

/-- (b) ⇒ (d): `λ(Å) = λ(A) = λ(Ā)` when `λ(∂A) = 0`. -/
theorem tendsto_of_null_frontier {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) {A : Set S}
    (h0 : l (frontier A) = 0) :
    Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A)) := by
  have hcl : l.real (closure A) ≤ l.real (interior A) := by
    rw [closure_eq_interior_union_frontier]
    refine (measureReal_union_le _ _).trans ?_
    rw [measureReal_def (s := frontier A), h0, ENNReal.toReal_zero, add_zero]
  have h1 : l.real (interior A) ≤ l.real A := measureReal_mono interior_subset
  have h2 : l.real A ≤ l.real (closure A) := measureReal_mono subset_closure
  refine tendsto_of_limsup_liminf (fun ε hε => ?_) (fun ε hε => ?_)
  · filter_upwards [hb _ isClosed_closure ε hε] with n hn
    have := measureReal_mono (μ := ls n) (subset_closure (s := A))
    linarith
  · filter_upwards [liminf_open_of_limsup_closed hb isOpen_interior ε hε] with n hn
    have := measureReal_mono (μ := ls n) (interior_subset (s := A))
    linarith

/-- (d) ⇒ (b), through thickenings `{ρ(·, F) < r}` with null boundaries. -/
theorem limsup_closed_of_null_frontier {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hd : ∀ A, MeasurableSet A → l (frontier A) = 0 →
      Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) {F : Set S} (hF : IsClosed F) :
    LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  obtain ⟨rs, hrs, hpos⟩ := exists_null_frontiers_thickening l F
  have hlim :=
    tendsto_measure_thickening_of_isClosed (μ := l) ⟨1, one_pos, measure_ne_top _ _⟩ hF
  have hrs' : Tendsto rs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hrs, Eventually.of_forall fun n => (hpos n).1⟩
  have hlim' : Tendsto (fun n => l.real (Metric.thickening (rs n) F)) atTop (𝓝 (l.real F)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (hlim.comp hrs')
  obtain ⟨m, hm⟩ := (hlim'.eventually (gt_mem_nhds (show l.real F < l.real F + ε / 2 by
    linarith))).exists
  have hA := hd _ Metric.isOpen_thickening.measurableSet (hpos m).2
  filter_upwards [hA.eventually (gt_mem_nhds (show l.real (Metric.thickening (rs m) F) <
    l.real (Metric.thickening (rs m) F) + ε / 2 by linarith))] with n hn
  have := measureReal_mono (μ := ls n) (Metric.self_subset_thickening (hpos m).1 F)
  linarith

/-- **Theorem 12.3.** For probability measures on a metric space, the following are equivalent:
(a) `λₙ ⇒ λ`; (b) `limsup λₙ(F) ≤ λ(F)` for closed `F`; (c) `liminf λₙ(G) ≥ λ(G)` for open
`G`; (d) `λₙ(A) → λ(A)` whenever `λ(∂A) = 0`. -/
theorem theorem_12_3 (ls : ℕ → Measure S) (l : Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] :
    (ConvWeak ls l ↔ ∀ F, IsClosed F → LimsupLe (fun n => (ls n).real F) (l.real F)) ∧
      (ConvWeak ls l ↔ ∀ G, IsOpen G → LiminfGe (fun n => (ls n).real G) (l.real G)) ∧
      (ConvWeak ls l ↔ ∀ A, MeasurableSet A → l (frontier A) = 0 →
        Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) := by
  refine ⟨⟨fun h F hF => limsup_closed_of_weak h hF, weak_of_limsup_closed⟩, ⟨fun h G hG =>
    liminf_open_of_limsup_closed (fun F hF => limsup_closed_of_weak h hF) hG,
    fun hc => weak_of_limsup_closed fun F hF => limsup_closed_of_liminf_open hc hF⟩,
    ⟨fun h A _ h0 => tendsto_of_null_frontier (fun F hF => limsup_closed_of_weak h hF) h0,
    fun hd => weak_of_limsup_closed fun F hF => limsup_closed_of_null_frontier hd hF⟩⟩

end StokeyLucasPrescott.ConvergenceApplications
