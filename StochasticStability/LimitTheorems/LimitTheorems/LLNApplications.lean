/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.AtomCLT

/-!
# Applications of the LLN (MT §17.3.2–§17.3.3)

Meyn and Tweedie, Theorems 17.3.2–17.3.3 and Proposition 17.3.4, pp. 436–438, for positive
Harris chains, where the law of large numbers of Theorem 17.1.7 is available from every initial
state.

* `theorem_17_3_2_positive`, Theorem 17.3.2 (iii) ⇒ (i) for a positive Harris chain with
  invariant probability `π` (p. 436): `Sₙ(f)/Sₙ(g) → π(f)/π(g)` from every initial state, for
  `f, g ∈ L¹(π)` with `π(g) ≠ 0`.
* `tendsto_iSup_div_of_tendsto_term`: if `uⱼ ≥ 0` and `uⱼ/(j + 1) → 0` then
  `(1/n) max_{k<n} uₖ → 0`.
* **Theorem 17.3.3** (`theorem_17_3_3`, p. 437), the running maximum: for `π(|g|) < ∞`,
  `(1/n) max_{1≤k≤n} |g(Φₖ)| → 0` almost surely from every initial state.
* **Proposition 17.3.4** (`proposition_17_3_4`, p. 438), the LLN when only the positive part is
  integrable: if `π(f⁺) < ∞` and `π(f⁻) = ∞`, then `(1/n) Sₙ(f) → −∞` almost surely from every
  initial state (with `π(f⁻) < ∞` this is the LLN of Theorem 17.1.7).

**Reading.** Theorem 17.3.2 (i) asks `∫ g dπ ≠ 0` (p. 436); the PDF's text layer drops the `≠`
sign, so extracted text shows `= 0`. The book's hypothesis is the one assumed here.

**Elsewhere.** Theorem 17.3.2 for null recurrent chains (the ratio limit theorem with a
σ-finite `π`, which the book proves through the split `m`-skeleton (17.21)) is
`theorem_17_3_2_harris` in `GapsChaconOrnstein`, for every Harris chain, and `theorem_17_3_2` in
`SplitLimitTheorems` for chains with a one-step minorization; the book's (i) ⇔ (ii) is
`theorem_17_3_2_tfae` there, for recurrent chains (with the counterexamples
`theorem_17_3_2_counterexample` and `theorem_17_3_2_counterexample_irreducible`).
Proposition 17.3.4 is stated by the book for the parameter process `θ` of the
dependent parameter bilinear model (DBL1)–(DBL2); the statement here is the general fact for any
positive Harris chain that the proof uses, and the book's setting is `proposition_17_3_4_dbl` in
`GapsBilinear` (with Proposition 11.4.2). The backward LLN (17.26) for the two-sided stationary
version (`theorem_17_26`) and Proposition 17.3.5 (`proposition_17_3_5`, through the stationary
solution rather than tightness, the Feller property and Theorem 12.1.2) are in `GapsBilinear`.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]

/-! ### Theorem 17.3.2 for positive Harris chains -/

/-- **Theorem 17.3.2** (iii) ⇒ (i) (MT p. 436) for a positive Harris chain with invariant
probability `π`: for `f, g ∈ L¹(π)` with `π(g) ≠ 0`, `Sₙ(f)/Sₙ(g) → π(f)/π(g)` almost surely from
every initial state. -/
theorem theorem_17_3_2_positive {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f g : X → ℝ} (hfm : Measurable f) (hgm : Measurable g) (hfi : Integrable f π)
    (hgi : Integrable g π) (hg : ∫ y, g y ∂π ≠ 0) (x : X) :
    ∀ᵐ ω ∂pathKernel P x, Tendsto (fun n => pathSum f n ω / pathSum g n ω) atTop
      (𝓝 ((∫ y, f y ∂π) / ∫ y, g y ∂π)) := by
  filter_upwards [lln_of_harris hH hπ hfm hfi x, lln_of_harris hH hπ hgm hgi x] with ω hf hg'
  refine (hf.div hg' hg).congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hn]

/-! ### Theorem 17.3.3: the running maximum -/

omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- If `uⱼ ≥ 0` and `uⱼ/(j + 1) → 0`, then `(1/n) max_{k<n} uₖ → 0`. -/
theorem tendsto_iSup_div_of_tendsto_term {u : ℕ → ℝ} (hu0 : ∀ j, 0 ≤ u j)
    (hu : Tendsto (fun j : ℕ => u j / ((j : ℝ) + 1)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (⨆ k : Fin n, u k) / n) atTop (𝓝 0) := by
  have hk : ∀ n : ℕ, ∃ j, j ≤ n ∧ ∀ i ≤ n, u i ≤ u j := fun n => by
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1)) u
      ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
    exact ⟨j, Nat.lt_succ_iff.1 (Finset.mem_range.1 hj),
      fun i hi => hmax i (Finset.mem_range.2 (Nat.lt_succ_of_le hi))⟩
  choose k hkn hkmax using hk
  have h := tendsto_index_div_of_le hu0 hu hkn
  rw [← tendsto_add_atTop_iff_nat 1]
  refine h.congr fun n => ?_
  have hsup : (⨆ i : Fin (n + 1), u i) = u (k n) := by
    refine le_antisymm (ciSup_le fun i => hkmax n i (Nat.lt_succ_iff.1 i.isLt)) ?_
    exact le_ciSup (f := fun i : Fin (n + 1) => u i) (Set.finite_range _).bddAbove
      ⟨k n, Nat.lt_succ_of_le (hkn n)⟩
  rw [hsup, Nat.cast_succ]

/-- **Theorem 17.3.3** (MT p. 437), the running maximum: for a positive Harris chain (Harris with
an invariant probability `π`) and `π(|g|) < ∞`, `(1/n) max_{1≤k≤n} |g(Φₖ)| → 0` almost surely from
every initial state. -/
theorem theorem_17_3_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g : X → ℝ}
    (hgm : Measurable g) (hgi : Integrable g π) (x : X) :
    ∀ᵐ ω ∂pathKernel P x,
      Tendsto (fun n : ℕ => (⨆ k : Fin n, |g (ω (k + 1))|) / n) atTop (𝓝 0) := by
  filter_upwards [lln_of_harris hH hπ (measurable_abs_of_measurable hgm) hgi.abs x] with ω hl
  exact tendsto_iSup_div_of_tendsto_term (u := fun j => |g (ω (j + 1))|) (fun j => abs_nonneg _)
    (tendsto_term_div_of_tendsto_average hl)

/-! ### Proposition 17.3.4: the LLN with an infinite negative part -/

omit [MeasurableSpace.CountablyGenerated X] in
/-- If `π(f⁺) < ∞` and `π(f⁻) = ∞`, then `π(max(f, −M)) → −∞` as `M → ∞`. -/
theorem exists_integral_max_lt {π : Measure X} [IsFiniteMeasure π] {f : X → ℝ}
    (hfm : Measurable f) (hpos : ∫⁻ x, ENNReal.ofReal (f x) ∂π ≠ ∞)
    (hneg : ∫⁻ x, ENNReal.ofReal (-f x) ∂π = ∞) (L : ℝ) :
    ∃ M : ℕ, ∫ x, max (f x) (-(M : ℝ)) ∂π < L := by
  set fp : X → ℝ := fun x => max (f x) 0 with hfp
  have hfpm : Measurable fp := hfm.max measurable_const
  have hfpi : Integrable fp π :=
    (integrable_toReal_of_lintegral_ne_top hfm.ennreal_ofReal.aemeasurable hpos).congr
      (Eventually.of_forall fun _ => ENNReal.toReal_ofReal')
  set q : ℕ → X → ℝ := fun M x => min (max (-f x) 0) M with hq
  have hqm : ∀ M, Measurable (q M) := fun M => (hfm.neg.max measurable_const).min measurable_const
  have hq0 : ∀ M x, 0 ≤ q M x := fun M x => le_min (le_max_right _ _) (Nat.cast_nonneg M)
  have hqi : ∀ M, Integrable (q M) π := fun M =>
    Integrable.of_bound (hqm M).aestronglyMeasurable M (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 M x)]; exact min_le_right _ _)
  have hdecomp : ∀ M : ℕ, ∀ x, max (f x) (-(M : ℝ)) = fp x - q M x := by
    intro M x
    simp only [hfp, hq]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left (show -(M : ℝ) ≤ f x by linarith), max_eq_left h,
        max_eq_right (show -f x ≤ 0 by linarith), min_eq_left hM0]
      ring
    · rw [max_eq_right h, max_eq_left (show (0 : ℝ) ≤ -f x by linarith)]
      rcases le_total (-f x) M with h' | h'
      · rw [min_eq_left h', max_eq_left (show -(M : ℝ) ≤ f x by linarith)]; ring
      · rw [min_eq_right h', max_eq_right (show f x ≤ -(M : ℝ) by linarith)]; ring
  -- `∫⁻ q_M ↑ ∞`
  have hpt : ∀ x, ⨆ M : ℕ, ENNReal.ofReal (q M x) = ENNReal.ofReal (-f x) := by
    intro x
    refine le_antisymm (iSup_le fun M => ?_) ?_
    · calc ENNReal.ofReal (q M x) ≤ ENNReal.ofReal (max (-f x) 0) :=
            ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = ENNReal.ofReal (-f x) := by
            rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
    · obtain ⟨M, hM⟩ := exists_nat_ge (max (-f x) 0)
      refine le_iSup_of_le M ?_
      simp only [hq]
      rw [min_eq_left hM]
      exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hsup : ⨆ M : ℕ, ∫⁻ x, ENNReal.ofReal (q M x) ∂π = ∞ := by
    rw [← lintegral_iSup (fun M => (hqm M).ennreal_ofReal) fun M N hMN x =>
      ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hMN))]
    simp_rw [hpt]
    exact hneg
  have hlt : ENNReal.ofReal (∫ x, fp x ∂π - L) < ⨆ M : ℕ, ∫⁻ x, ENNReal.ofReal (q M x) ∂π := by
    rw [hsup]; exact ENNReal.ofReal_lt_top
  obtain ⟨M, hM⟩ := lt_iSup_iff.1 hlt
  rw [← ofReal_integral_eq_lintegral_ofReal (hqi M) (Eventually.of_forall (hq0 M)),
    ENNReal.ofReal_lt_ofReal_iff'] at hM
  refine ⟨M, ?_⟩
  have hint : ∫ x, max (f x) (-(M : ℝ)) ∂π = ∫ x, fp x ∂π - ∫ x, q M x ∂π := by
    rw [← integral_sub hfpi (hqi M)]
    exact integral_congr_ae (Eventually.of_forall fun x => hdecomp M x)
  rw [hint]
  linarith [hM.1]

/-- **Proposition 17.3.4** (MT p. 438), the general fact behind it: for a positive Harris chain
with invariant probability `π` and `f` with `π(f⁺) < ∞`, `(1/n) Sₙ(f) → π(f)` almost surely from
every initial state, the limit being `−∞` when `π(f⁻) = ∞`. The case `π(f⁻) < ∞` is
`lln_of_harris`; this is the case `π(f) = −∞`. -/
theorem proposition_17_3_4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ} (hfm : Measurable f) (hpos : ∫⁻ x, ENNReal.ofReal (f x) ∂π ≠ ∞)
    (hneg : ∫⁻ x, ENNReal.ofReal (-f x) ∂π = ∞) (x : X) :
    ∀ᵐ ω ∂pathKernel P x, Tendsto (fun n => pathSum f n ω / n) atTop atBot := by
  have hfMm : ∀ M : ℕ, Measurable fun y => max (f y) (-(M : ℝ)) := fun M =>
    hfm.max measurable_const
  have hfMi : ∀ M : ℕ, Integrable (fun y => max (f y) (-(M : ℝ))) π := fun M => by
    refine ⟨(hfMm M).aestronglyMeasurable, ?_⟩
    have hb : ∀ y, ‖max (f y) (-(M : ℝ))‖ₑ ≤ ENNReal.ofReal (f y) + M := fun y => by
      rw [← ofReal_norm, Real.norm_eq_abs]
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      calc ENNReal.ofReal |max (f y) (-(M : ℝ))| ≤ ENNReal.ofReal (max (f y) 0 + M) := by
            refine ENNReal.ofReal_le_ofReal (abs_le.2 ⟨?_, ?_⟩)
            · have := le_max_right (f y) (-(M : ℝ)); linarith [le_max_right (f y) 0]
            · rcases le_total (f y) (-(M : ℝ)) with h | h
              · rw [max_eq_right h]; linarith [le_max_right (f y) 0]
              · rw [max_eq_left h]; linarith [le_max_left (f y) 0]
        _ = ENNReal.ofReal (max (f y) 0) + ENNReal.ofReal M :=
            ENNReal.ofReal_add (le_max_right _ _) hM0
        _ ≤ ENNReal.ofReal (f y) + M := by
            rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le,
              ENNReal.ofReal_natCast]
    refine lt_of_le_of_lt (lintegral_mono hb) ?_
    rw [lintegral_add_right _ measurable_const, lintegral_const]
    exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hpos, ENNReal.mul_lt_top
      (ENNReal.natCast_lt_top M) (measure_lt_top _ _)⟩
  have hall := ae_all_iff.2 fun M : ℕ => lln_of_harris hH hπ (hfMm M) (hfMi M) x
  filter_upwards [hall] with ω hω
  rw [tendsto_atBot]
  intro L
  obtain ⟨M, hM⟩ := exists_integral_max_lt hfm hpos hneg L
  filter_upwards [(hω M).eventually (gt_mem_nhds hM)] with n hn
  refine le_trans ?_ hn.le
  have hle : pathSum f n ω ≤ pathSum (fun y => max (f y) (-(M : ℝ))) n ω :=
    Finset.sum_le_sum fun k _ => le_max_left _ _
  exact div_le_div_of_nonneg_right hle (Nat.cast_nonneg n)
end MeynTweedie.LimitTheorems
