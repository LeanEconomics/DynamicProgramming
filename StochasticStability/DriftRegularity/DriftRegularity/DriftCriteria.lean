/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DriftRegularity.Dichotomy

/-!
# Classification using drift criteria (MT §8.0, §8.4.1–8.4.2)

Meyn and Tweedie, Theorem 8.0.2 (p. 172) and §8.4.1–8.4.2, pp. 187–190. `ψ` is a maximal
irreducibility measure.

* `drift P V` (8.1), p. 172: the (extended valued) drift `ΔV(x) = ∫ P(x, dy) V(y) − V(x)` of a
  nonnegative `V`, valued in `EReal`; `drift_nonpos_iff`, `drift_nonneg_iff`. `driftR` is the
  real drift of a real function (for bounded `V`, where it is well defined).
* `hitProbZero P C x = P_x(σ_C < ∞)`, with `hitProbZero_of_mem` (`= 1` on `C`) and
  `hitProbZero_of_notMem` (`= L(x, C)` off `C`).
* **Proposition 8.4.1** (`proposition_8_4_1`, p. 187): `h*(x) = P_x(σ_C < ∞)` solves (8.39) with
  equality off `C`, and is the pointwise minimal nonnegative solution of (8.39).
* `isTransientChain_of_drift`: the drift argument common to Theorems 8.0.2 (i) and 8.4.2: a
  bounded `V ≥ 0` with `ΔV ≥ 0` off `C ∈ B⁺(X)`, `V ≤ r` on `C` and `{V > r} ∈ B⁺(X)` gives
  `L(x, C) ≤ (M − V(x))/(M − r) < 1` on `{V > r}`, hence transience (Theorem 8.3.6 (ii)).
* `IsTransientChain.exists_compl_hitProb_lt_one`: a transient chain has a uniformly transient
  `C ∈ B⁺(X)` with `{y ∉ C : L(y, C) < 1} ∈ B⁺(X)`.
* **Theorem 8.4.2** (`theorem_8_4_2`, p. 188): a `ψ`-irreducible chain is transient iff there are
  a bounded `V ≥ 0` and `r ≥ 0` with `C_V(r), C_V(r)ᶜ ∈ B⁺(X)` and `ΔV ≥ 0` on `C_V(r)ᶜ`.
* **Theorem 8.0.2 (i)** (`theorem_8_0_2_i`, p. 172): transience iff a bounded `V ≥ 0` and
  `C ∈ B⁺(X)` with `ΔV ≥ 0` on `Cᶜ` and `{V > sup_C V} ∈ B⁺(X)`.
* `lemma_8_4_3_hitProb`: under (V1) with `C ∈ B⁺(X)` and `V` unbounded off petite sets,
  `L(x, C) = 1` for every `x`; **Theorem 8.4.3** (`theorem_8_4_3`, p. 190) and
  **Theorem 8.0.2 (ii)** (`theorem_8_0_2_ii`): with `C` petite, the chain is recurrent.
* `unboundedOffPetite_of_cover` (8.43), p. 189: on a countably generated space, `V` is unbounded
  off petite sets if each `C_V(n)` lies in a finite union of petite sets.

**Corrections.**
* Theorem 8.4.2 is stated with the strict inequality `ΔV > 0` on `C_V(r)ᶜ`. The sufficiency proof
  only uses `ΔV ≥ 0`, and for the converse the book's function `V = 1 − P_x(σ_C < ∞)` has
  `ΔV = 0` off `C` (Proposition 8.4.1), so the converse it proves is the one with `ΔV ≥ 0`; the
  book's own application, Proposition 8.4.5, uses `ΔV = 0`. The theorem is proved here with
  `ΔV ≥ 0`, the form of Theorem 8.0.2 (i).
* Theorem 8.4.3 claims `L(x, C) ≡ 1` for the petite set `C` of (V1). The proof enlarges `C` to
  `C ∪ C_V(n)` to put it in `B⁺(X)`, and proves `L ≡ 1` only for the enlarged set. The claim
  fails for `C = ∅` (a petite set): on the one-point space with `V = 0`, (V1) holds, the chain is
  recurrent, and `L(x, ∅) = 0` (`theorem_8_4_3_counterexample`). It holds for `C ∈ B⁺(X)`
  (`lemma_8_4_3_hitProb`, which needs no petiteness of `C`), and the recurrence conclusion holds
  as stated.
* The book's proof of Theorem 8.4.3 argues by contradiction from transience; the argument here
  is direct: it bounds the killed chain `P I_{Cᶜ}` by the drift, `∫ (P I_{Cᶜ})ⁿ(x, dy) V(y) ≤ V(x)`,
  and uses that a petite `C_V(M)` reaches `C` with probability bounded below, so that the tail
  `P_x(n < τ_C < ∞)`, which tends to `0`, is bounded below if `L(x, C) < 1`.
-/

namespace MeynTweedie.DriftRegularity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The drift operator -/

/-- The **drift operator** (8.1), MT p. 172: `ΔV(x) = ∫ P(x, dy) V(y) − V(x)` for a nonnegative
measurable `V`, possibly extended valued. -/
noncomputable def drift (P : Kernel X X) (V : X → ℝ≥0∞) (x : X) : EReal :=
  ((∫⁻ y, V y ∂P x : ℝ≥0∞) : EReal) - ((V x : ℝ≥0∞) : EReal)

/-- `ΔV(x) ≤ 0` iff `PV(x) ≤ V(x)`. -/
theorem drift_nonpos_iff (P : Kernel X X) (V : X → ℝ≥0∞) (x : X) :
    drift P V x ≤ 0 ↔ ∫⁻ y, V y ∂P x ≤ V x := by
  rw [drift, EReal.sub_nonpos, EReal.coe_ennreal_le_coe_ennreal_iff]

/-- `ΔV(x) ≥ 0` iff `PV(x) ≥ V(x)`, when `V(x) < ∞`. -/
theorem drift_nonneg_iff (P : Kernel X X) (V : X → ℝ≥0∞) {x : X} (hV : V x ≠ ∞) :
    0 ≤ drift P V x ↔ V x ≤ ∫⁻ y, V y ∂P x := by
  rw [drift, EReal.sub_nonneg (Or.inr (by rwa [ne_eq, EReal.coe_ennreal_eq_top_iff]))
    (Or.inr (EReal.coe_ennreal_ne_bot _)), EReal.coe_ennreal_le_coe_ennreal_iff]

/-- The drift of a real function, `ΔV(x) = ∫ P(x, dy) V(y) − V(x)`; it is the drift (8.1) for
bounded `V`, where the integral is finite (MT p. 188: "`Δ` is well-defined if `V` is bounded"). -/
noncomputable def driftR (P : Kernel X X) (V : X → ℝ) (x : X) : ℝ := ∫ y, V y ∂P x - V x

/-! ### Proposition 8.4.1 -/

/-- `h*(x) = P_x(σ_C < ∞)`, the probability of ever being in `C`, time `0` included. -/
noncomputable def hitProbZero (P : Kernel X X) [IsMarkovKernel P] (C : Set X) (x : X) : ℝ≥0∞ :=
  pathKernel P x {ω | firstHit C ω ≠ ⊤}

/-- `x ↦ P_x(σ_C < ∞)` is measurable. -/
theorem measurable_hitProbZero (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) : Measurable (hitProbZero P C) :=
  Kernel.measurable_coe _ (measurableSet_ne_top (proposition_3_4_4 hC).2)

/-- `P_x(σ_C < ∞) = 1` for `x ∈ C`. -/
theorem hitProbZero_of_mem (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) {x : X} (hx : x ∈ C) : hitProbZero P C x = 1 := by
  have := isMarkovKernel_pathKernel P
  refine le_antisymm prob_le_one ?_
  calc (1 : ℝ≥0∞) = pathKernel P x {ω | ω 0 ∈ C} := by
        rw [pathKernel_zero_mem P x hC, indicator_of_mem hx, Pi.one_apply]
    _ ≤ hitProbZero P C x := measure_mono fun ω hω => by
        change firstHit C ω ≠ ⊤
        rw [(firstHit_eq_zero_iff C ω).2 hω]
        exact WithTop.coe_ne_top

/-- `P_x(σ_C < ∞) = L(x, C)` for `x ∉ C`. -/
theorem hitProbZero_of_notMem (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) {x : X} (hx : x ∉ C) : hitProbZero P C x = hitProb P C x := by
  have hnull : pathKernel P x {ω : ℕ → X | ω 0 ∈ Cᶜ}ᶜ = 0 := by
    have : {ω : ℕ → X | ω 0 ∈ Cᶜ}ᶜ = {ω | ω 0 ∈ C} := by ext ω; simp
    rw [this, pathKernel_zero_mem P x hC, indicator_of_notMem hx]
  rw [hitProbZero, hitProb, ← measure_inter_conull (s := {ω | firstHit C ω ≠ ⊤}) hnull,
    ← measure_inter_conull (s := {ω | firstReturn C ω ≠ ⊤}) hnull]
  congr 1
  ext ω
  simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by rwa [← firstHit_eq_firstReturn C h2], h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by rwa [firstHit_eq_firstReturn C h2], h2⟩

/-- `P_x(σ_C < ∞) ≤ 1`. -/
theorem hitProbZero_le_one (P : Kernel X X) [IsMarkovKernel P] (C : Set X) (x : X) :
    hitProbZero P C x ≤ 1 := by
  have := isMarkovKernel_pathKernel P
  exact prob_le_one

/-- **Proposition 8.4.1** (MT p. 187): `h*(x) = P_x(σ_C < ∞)` satisfies the inequalities (8.39),
`∫ P(x, dy) h(y) ≤ h(x)` for `x ∉ C` and `h ≥ 1` on `C`, with equality, and it is the pointwise
minimal nonnegative solution of (8.39). -/
theorem proposition_8_4_1 (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) :
    (∀ x ∉ C, ∫⁻ y, hitProbZero P C y ∂P x = hitProbZero P C x) ∧
      (∀ x ∈ C, hitProbZero P C x = 1) ∧
      ∀ h : X → ℝ≥0∞, (∀ x ∉ C, ∫⁻ y, h y ∂P x ≤ h x) → (∀ x ∈ C, 1 ≤ h x) →
        ∀ x, hitProbZero P C x ≤ h x := by
  refine ⟨fun x hx => ?_, fun x hx => hitProbZero_of_mem P hC hx, fun h hsup hC1 x => ?_⟩
  · rw [hitProbZero_of_notMem P hC hx, hitProb_first_step P hC x, ← lintegral_add_compl _ hC,
      setLIntegral_congr_fun hC fun y hy => hitProbZero_of_mem P hC hy,
      setLIntegral_congr_fun hC.compl fun y hy => hitProbZero_of_notMem P hC hy,
      setLIntegral_const, one_mul]
  · by_cases hx : x ∈ C
    · rw [hitProbZero_of_mem P hC hx]; exact hC1 x hx
    rw [hitProbZero_of_notMem P hC hx, hitProb_eq_tsum P hC x, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    induction N generalizing x with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ', tabooKernel_zero]
      simp_rw [tabooKernel_succ_apply P hC _ x hC]
      rw [← lintegral_finsetSum _ fun n _ => Kernel.measurable_coe _ hC]
      calc ∫⁻ y in Cᶜ, ∑ n ∈ Finset.range N, tabooKernel P hC n y C ∂P x + P x C
          ≤ ∫⁻ y in Cᶜ, h y ∂P x + ∫⁻ y in C, h y ∂P x := by
            refine add_le_add (setLIntegral_mono' hC.compl fun y hy => ih y hy) ?_
            calc P x C = ∫⁻ _ in C, 1 ∂P x := by rw [setLIntegral_const, one_mul]
              _ ≤ _ := setLIntegral_mono' hC fun y hy => hC1 y hy
        _ = ∫⁻ y, h y ∂P x := by rw [add_comm, lintegral_add_compl _ hC]
        _ ≤ h x := hsup x hx

/-! ### The drift criterion for transience -/

/-- **The drift argument for transience** (proofs of Theorems 8.0.2 (i) and 8.4.2, MT p. 188).
Let `V ≥ 0` be measurable and bounded by `M`, `C ∈ B⁺(X)`, `V ≤ r` on `C`, `ΔV ≥ 0` off `C` and
`{V > r} ∈ B⁺(X)`. Then `h_V = (M − V)/(M − r)` (and `1` on `C`) solves (8.39), so
`L(x, C) ≤ h_V(x) < 1` on `{V > r}`, and the chain is transient. -/
theorem isTransientChain_of_drift (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : MeasurableSet C) (hψC : 0 < ψ C)
    {V : X → ℝ} (hVm : Measurable V) (hV0 : ∀ x, 0 ≤ V x) {M : ℝ} (hVM : ∀ x, V x ≤ M)
    {r : ℝ} (hVr : ∀ y ∈ C, V y ≤ r) (hdrift : ∀ x ∉ C, 0 ≤ driftR P V x)
    (hD : 0 < ψ {x | r < V x}) : IsTransientChain P ψ := by
  classical
  have hDm : MeasurableSet {x | r < V x} := measurableSet_lt measurable_const hVm
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hD.ne'
  have hMr : 0 < M - r := sub_pos.2 (lt_of_lt_of_le hx₀ (hVM x₀))
  set g : X → ℝ≥0∞ := fun y => ENNReal.ofReal ((M - V y) / (M - r)) with hg
  set h : X → ℝ≥0∞ := C.piecewise 1 g with hh
  have hint : ∀ x, Integrable V (P x) := fun x =>
    Integrable.of_bound hVm.aestronglyMeasurable M (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hV0 y)]; exact hVM y)
  have hhg : ∀ y, h y ≤ g y := fun y => by
    by_cases hy : y ∈ C
    · rw [hh, piecewise_eq_of_mem _ _ _ hy, Pi.one_apply, hg, ENNReal.one_le_ofReal,
        one_le_div hMr]
      linarith [hVr y hy]
    · rw [hh, piecewise_eq_of_notMem _ _ _ hy]
  have hsup : ∀ x ∉ C, ∫⁻ y, h y ∂P x ≤ h x := fun x hx => by
    have hgint : Integrable (fun y => (M - V y) / (M - r)) (P x) :=
      ((integrable_const M).sub (hint x)).div_const _
    calc ∫⁻ y, h y ∂P x ≤ ∫⁻ y, g y ∂P x := lintegral_mono hhg
      _ = ENNReal.ofReal (∫ y, (M - V y) / (M - r) ∂P x) := by
          rw [ofReal_integral_eq_lintegral_ofReal hgint (Eventually.of_forall fun y =>
            div_nonneg (by linarith [hVM y]) hMr.le)]
      _ = ENNReal.ofReal ((M - ∫ y, V y ∂P x) / (M - r)) := by
          rw [integral_div, integral_sub (integrable_const M) (hint x), integral_const]
          simp
      _ ≤ ENNReal.ofReal ((M - V x) / (M - r)) := by
          refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hMr.le)
          have := hdrift x hx
          rw [driftR] at this
          linarith
      _ = h x := by rw [hh, piecewise_eq_of_notMem _ _ _ hx]
  have hmin := (proposition_8_4_1 P hC).2.2 h hsup fun x hx => by
    rw [hh, piecewise_eq_of_mem _ _ _ hx]; exact le_rfl
  refine (theorem_8_3_6_ii P hψ).2 ⟨C, {x | r < V x}, hC, hDm, hψC, hD, fun x hx => ?_⟩
  have hxC : x ∉ C := fun hxC => absurd (hVr x hxC) (not_le.2 hx)
  rw [← hitProbZero_of_notMem P hC hxC]
  calc hitProbZero P C x ≤ h x := hmin x
    _ = ENNReal.ofReal ((M - V x) / (M - r)) := by rw [hh, piecewise_eq_of_notMem _ _ _ hxC]
    _ < 1 := by
        rw [ENNReal.ofReal_lt_one, div_lt_one hMr]
        change r < V x at hx
        linarith

/-- A transient chain has a uniformly transient `C ∈ B⁺(X)` such that
`{y ∉ C : L(y, C) < 1} ∈ B⁺(X)` (the set `D` of the proof of Theorem 8.4.2). -/
theorem IsTransientChain.exists_compl_hitProb_lt_one {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (h : IsTransientChain P ψ) :
    ∃ B, IsUniformlyTransient P B ∧ 0 < ψ B ∧ 0 < ψ {y | y ∉ B ∧ hitProb P B y < 1} := by
  have hψ := h.1
  obtain ⟨B, hB, hψB⟩ := h.exists_uniformlyTransient
  refine ⟨B, hB, hψB, ?_⟩
  have hDm : MeasurableSet {y | y ∉ B ∧ hitProb P B y < 1} :=
    hB.1.compl.inter (measurableSet_lt (measurable_hitProb P hB.1) measurable_const)
  rw [pos_iff_ne_zero]
  intro h0
  have hfull : IsFull ψ {y | y ∉ B ∧ hitProb P B y < 1}ᶜ := by rw [IsFull, compl_compl]; exact h0
  obtain ⟨F, hFsub, hFne, hFm, habs, hFfull⟩ := proposition_4_2_3_ii hψ hDm.compl hfull
  -- `L(·, B) = 1` on `F`
  have hL1 : ∀ y ∈ F, hitProb P B y = 1 := fun y hy => by
    refine le_antisymm (hitProb_le_one P B y) ?_
    calc (1 : ℝ≥0∞) = P y F := (habs y hy).symm
      _ = P y (F ∩ B) + P y (F \ B) := (measure_inter_add_sdiff F hB.1).symm
      _ ≤ P y B + ∫⁻ z in Bᶜ, hitProb P B z ∂P y := by
          refine add_le_add (measure_mono inter_subset_right) ?_
          calc P y (F \ B) = ∫⁻ z in Bᶜ, F.indicator 1 z ∂P y := by
                rw [lintegral_indicator_one hFm, Measure.restrict_apply hFm, sdiff_eq]
            _ ≤ _ := setLIntegral_mono' hB.1.compl fun z hz => by
                by_cases hzF : z ∈ F
                · rw [indicator_of_mem hzF, Pi.one_apply]
                  have := hFsub hzF
                  simp only [mem_compl_iff, mem_ofPred_eq, not_and, not_lt] at this
                  exact this hz
                · rw [indicator_of_notMem hzF]; exact zero_le
      _ = hitProb P B y := (hitProb_first_step P hB.1 y).symm
  have hL1' : ∀ x ∈ F, hitProb P (B ∩ F) x = 1 := fun x hx =>
    le_antisymm (hitProb_le_one P _ x) ((hL1 x hx) ▸ hitProb_inter_absorbing P hFm habs hx)
  have hpos : 0 < ψ (B ∩ F) := by
    rw [pos_iff_ne_zero]
    intro h0'
    have : ψ B ≤ ψ (B ∩ F) + ψ Fᶜ := by
      calc ψ B ≤ ψ ((B ∩ F) ∪ Fᶜ) := measure_mono fun y hy => by
            by_cases hyF : y ∈ F
            · exact Or.inl ⟨hy, hyF⟩
            · exact Or.inr hyF
        _ ≤ _ := measure_union_le _ _
    rw [h0', hFfull, add_zero] at this
    exact hψB.ne' (nonpos_iff_eq_zero.1 this)
  obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hpos.ne'
  have hrec := proposition_8_3_1_ii P (hB.1.inter hFm) fun x hx => hL1' x hx.2
  obtain ⟨M, hM, hb⟩ := hB.exists_bound
  exact hM (top_le_iff.1 (hrec y hy ▸ (measure_mono inter_subset_left).trans (hb y)))

/-- The function `V = 1 − P_x(σ_C < ∞)` of the converse halves of Theorems 8.0.2 (i) and 8.4.2:
`0 ≤ V ≤ 1`, `V = 0` on `C`, `V(y) = 1 − L(y, C)` off `C`, and `ΔV = 0` off `C`. -/
theorem drift_one_sub_hitProbZero (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) :
    Measurable (fun x => 1 - (hitProbZero P C x).toReal) ∧
      (∀ x, 0 ≤ 1 - (hitProbZero P C x).toReal) ∧ (∀ x, 1 - (hitProbZero P C x).toReal ≤ 1) ∧
      (∀ x ∈ C, 1 - (hitProbZero P C x).toReal = 0) ∧
      (∀ x ∉ C, hitProb P C x < 1 → 0 < 1 - (hitProbZero P C x).toReal) ∧
      ∀ x ∉ C, driftR P (fun x => 1 - (hitProbZero P C x).toReal) x = 0 := by
  have hm := measurable_hitProbZero P hC
  have hfin : ∀ x, hitProbZero P C x ≠ ∞ := fun x =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hitProbZero_le_one P C x)
  refine ⟨measurable_const.sub hm.ennreal_toReal, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun x hx hL => ?_, fun x hx => ?_⟩
  · have := ENNReal.toReal_le_of_le_ofReal zero_le_one
      ((hitProbZero_le_one P C x).trans_eq ENNReal.ofReal_one.symm)
    linarith
  · linarith [ENNReal.toReal_nonneg (a := hitProbZero P C x)]
  · rw [hitProbZero_of_mem P hC hx, ENNReal.toReal_one, sub_self]
  · rw [hitProbZero_of_notMem P hC hx, sub_pos]
    have := (ENNReal.toReal_lt_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (hitProb_le_one P C x)) ENNReal.one_ne_top).2 hL
    rwa [ENNReal.toReal_one] at this
  · have hint : Integrable (fun y => (hitProbZero P C y).toReal) (P x) :=
      Integrable.of_bound hm.ennreal_toReal.aestronglyMeasurable 1
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one
            ((hitProbZero_le_one P C y).trans_eq ENNReal.ofReal_one.symm))
    rw [driftR, integral_sub (integrable_const 1) hint, integral_const,
      integral_toReal hm.aemeasurable (Eventually.of_forall fun y => (hfin y).lt_top),
      (proposition_8_4_1 P hC).1 x hx]
    simp

/-- **Theorem 8.4.2** (MT p. 188): a `ψ`-irreducible chain is transient iff there are a bounded
measurable `V : X → ℝ₊` and `r ≥ 0` such that (i) `C_V(r) = {V ≤ r}` and `C_V(r)ᶜ` are in
`B⁺(X)` and (ii) `ΔV ≥ 0` on `C_V(r)ᶜ`. -/
theorem theorem_8_4_2 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    IsTransientChain P ψ ↔ ∃ (V : X → ℝ) (r : ℝ), Measurable V ∧ (∀ x, 0 ≤ V x) ∧
      (∃ M, ∀ x, V x ≤ M) ∧ 0 ≤ r ∧ 0 < ψ {x | V x ≤ r} ∧ 0 < ψ {x | V x ≤ r}ᶜ ∧
      ∀ x ∈ {x | V x ≤ r}ᶜ, 0 ≤ driftR P V x := by
  constructor
  · intro h
    obtain ⟨B, hB, hψB, hD⟩ := h.exists_compl_hitProb_lt_one
    obtain ⟨hm, h0, h1, hBz, hpos, hdr⟩ := drift_one_sub_hitProbZero P hB.1
    refine ⟨_, 0, hm, h0, ⟨1, h1⟩, le_rfl, ?_, ?_, fun x hx => ?_⟩
    · exact hψB.trans_le (measure_mono fun x hx => by
        simp only [mem_ofPred_eq]; rw [hBz x hx])
    · exact hD.trans_le (measure_mono fun x hx => by
        simp only [mem_compl_iff, mem_ofPred_eq, not_le]
        exact hpos x hx.1 hx.2)
    · have hxB : x ∉ B := fun hxB => hx (by simp only [mem_ofPred_eq]; rw [hBz x hxB])
      rw [hdr x hxB]
  · rintro ⟨V, r, hVm, hV0, ⟨M, hVM⟩, -, hC, hD, hdr⟩
    refine isTransientChain_of_drift P hψ (measurableSet_le hVm measurable_const) hC hVm hV0
      hVM (fun y hy => hy) hdr ?_
    have : {x | r < V x} = {x | V x ≤ r}ᶜ := by ext x; simp
    rwa [this]

/-- **Theorem 8.0.2 (i)** (MT p. 172): a `ψ`-irreducible chain is transient iff there are a
bounded measurable `V ≥ 0` and `C ∈ B⁺(X)` with `ΔV ≥ 0` on `Cᶜ` (8.2) and
`D = {V > sup_C V} ∈ B⁺(X)` (8.3). -/
theorem theorem_8_0_2_i (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    IsTransientChain P ψ ↔ ∃ (V : X → ℝ) (C : Set X), Measurable V ∧ (∀ x, 0 ≤ V x) ∧
      (∃ M, ∀ x, V x ≤ M) ∧ MeasurableSet C ∧ 0 < ψ C ∧ (∀ x ∈ Cᶜ, 0 ≤ driftR P V x) ∧
      0 < ψ {x | sSup (V '' C) < V x} := by
  constructor
  · intro h
    obtain ⟨B, hB, hψB, hD⟩ := h.exists_compl_hitProb_lt_one
    obtain ⟨hm, h0, h1, hBz, hpos, hdr⟩ := drift_one_sub_hitProbZero P hB.1
    obtain ⟨b, hb⟩ := nonempty_of_measure_ne_zero hψB.ne'
    have hsup : sSup ((fun x => 1 - (hitProbZero P B x).toReal) '' B) = 0 := by
      have : (fun x => 1 - (hitProbZero P B x).toReal) '' B = {0} := by
        ext t
        simp only [mem_image, mem_singleton_iff]
        exact ⟨fun ⟨x, hx, hxt⟩ => hxt ▸ hBz x hx, fun ht => ⟨b, hb, ht ▸ hBz b hb⟩⟩
      rw [this, csSup_singleton]
    refine ⟨_, B, hm, h0, ⟨1, h1⟩, hB.1, hψB, fun x hx => (hdr x hx).ge, ?_⟩
    rw [hsup]
    exact hD.trans_le (measure_mono fun x hx => hpos x hx.1 hx.2)
  · rintro ⟨V, C, hVm, hV0, ⟨M, hVM⟩, hC, hψC, hdr, hD⟩
    refine isTransientChain_of_drift P hψ hC hψC hVm hV0 hVM (fun y hy =>
      le_csSup ⟨M, by rintro _ ⟨z, -, rfl⟩; exact hVM z⟩ (mem_image_of_mem V hy))
      (fun x hx => hdr x hx) hD

/-! ### The drift criterion for recurrence -/

/-- The killed kernel `P I_{Cᶜ}`: move by `P` and kill the path if it lands in `C`. Its powers
satisfy `(P I_{Cᶜ})ⁿ⁺¹(x, B) = P_x(Φₙ₊₁ ∈ B, τ_C > n + 1)`. -/
noncomputable abbrev killedKernel (P : Kernel X X) {C : Set X} (hC : MeasurableSet C) :
    Kernel X X :=
  indKernel hC.compl ∘ₖ P

/-- **The drift inequality for the killed chain**: if `PV ≤ V` off `C`, then
`∫ (P I_{Cᶜ})ⁿ(x, dy) V(y) ≤ V(x)` for `x ∉ C`. -/
theorem lintegral_killedKernel_pow_le (P : Kernel X X) {C : Set X} (hC : MeasurableSet C)
    {V : X → ℝ≥0∞} (hV : Measurable V) (hdrift : ∀ x ∉ C, ∫⁻ y, V y ∂P x ≤ V x) (n : ℕ) :
    ∀ x ∉ C, ∫⁻ y, V y ∂(killedKernel P hC ^ n) x ≤ V x := by
  induction n with
  | zero => intro x _; rw [pow_zero_apply, lintegral_dirac' _ hV]
  | succ n ih =>
    intro x hx
    rw [pow_succ]
    change ∫⁻ y, V y ∂((killedKernel P hC ^ n) ∘ₖ killedKernel P hC) x ≤ V x
    rw [Kernel.lintegral_comp _ _ _ hV, comp_indKernel_eq_restrict]
    calc ∫⁻ y in Cᶜ, ∫⁻ z, V z ∂(killedKernel P hC ^ n) y ∂P x
        ≤ ∫⁻ y in Cᶜ, V y ∂P x := setLIntegral_mono' hC.compl fun y hy => ih y hy
      _ ≤ ∫⁻ y, V y ∂P x := setLIntegral_le_lintegral _ _
      _ ≤ V x := hdrift x hx

/-- The killed chain never charges `C` after time `0`: `(P I_{Cᶜ})ⁿ⁺¹(x, C) = 0`. -/
theorem killedKernel_pow_succ_apply_self (P : Kernel X X) {C : Set X} (hC : MeasurableSet C)
    (n : ℕ) (x : X) : (killedKernel P hC ^ (n + 1)) x C = 0 := by
  rw [pow_succ']
  change ((killedKernel P hC) ∘ₖ (killedKernel P hC ^ n)) x C = 0
  rw [Kernel.comp_apply' _ _ _ hC]
  refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun y => ?_)
  change (indKernel hC.compl ∘ₖ P) y C = 0
  rw [comp_indKernel_apply P hC.compl y hC, inter_compl_self, measure_empty]

/-- `(P I_{Cᶜ})ᵏ(x, X) = _CPᵏ(x, C) + (P I_{Cᶜ})ᵏ⁺¹(x, X)`: from time `k` the chain either
enters `C` at time `k + 1` or survives. -/
theorem killedKernel_pow_univ (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) (k : ℕ) (x : X) :
    (killedKernel P hC ^ k) x univ =
      tabooKernel P hC k x C + (killedKernel P hC ^ (k + 1)) x univ := by
  rw [pow_succ']
  change _ = (P ∘ₖ (killedKernel P hC ^ k)) x C +
    ((killedKernel P hC) ∘ₖ (killedKernel P hC ^ k)) x univ
  rw [Kernel.comp_apply' _ _ _ hC, Kernel.comp_apply' _ _ _ MeasurableSet.univ,
    ← lintegral_add_left (Kernel.measurable_coe _ hC)]
  simp_rw [comp_indKernel_apply P hC.compl _ MeasurableSet.univ, univ_inter]
  rw [← lintegral_one]
  refine lintegral_congr fun y => ?_
  rw [measure_add_measure_compl hC, measure_univ]

/-- `Σ_{k < n} _CPᵏ⁺¹(x, C) + (P I_{Cᶜ})ⁿ(x, X) = 1`: before time `n` the chain has entered `C`
or it survives to time `n`. -/
theorem sum_tabooKernel_add_killed (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) (n : ℕ) (x : X) :
    ∑ k ∈ Finset.range n, tabooKernel P hC k x C + (killedKernel P hC ^ n) x univ = 1 := by
  induction n with
  | zero => rw [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero_apply, measure_univ]
  | succ n ih =>
    rw [Finset.sum_range_succ, add_assoc, ← killedKernel_pow_univ P hC n x, ih]

/-- `∫ (P I_{Cᶜ})ⁿ(x, dy) L(y, C) = Σ_k _CPⁿ⁺ᵏ⁺¹(x, C) = P_x(n < τ_C < ∞)`. -/
theorem lintegral_killedKernel_hitProb (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) (n : ℕ) (x : X) :
    ∫⁻ y, hitProb P C y ∂(killedKernel P hC ^ n) x = ∑' k, tabooKernel P hC (k + n) x C := by
  simp_rw [hitProb_eq_tsum P hC]
  rw [lintegral_tsum fun k => (Kernel.measurable_coe _ hC).aemeasurable]
  refine tsum_congr fun k => ?_
  rw [← Kernel.comp_apply' _ _ _ hC, tabooKernel, tabooKernel, Kernel.comp_assoc]
  congr 3
  rw [pow_add]
  rfl

/-- A petite set reaches a set `C ∈ B⁺(X)` with probability bounded below: if `A` is petite and
`φ(C) > 0` for an irreducibility measure `φ`, there is `δ > 0` with `L(y, C) ≥ δ` for
`y ∈ A \ C`. -/
theorem IsPetite.hitProb_ge (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {A C : Set X} (hA : IsPetite P A) (hC : MeasurableSet C)
    (hφC : 0 < φ C) : ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ y ∈ A, y ∉ C → δ ≤ hitProb P C y := by
  have := isMarkovKernel_pathKernel P
  obtain ⟨a, ν, hAm, ha, hν, hle⟩ := hA
  have hK : ∀ z, 0 < resolventHalf P z C := fun z =>
    (proposition_4_2_1 P φ).2.2.1 hφ C hC hφC z
  refine ⟨∫⁻ z, resolventHalf P z C ∂ν, lintegral_pos_of_pos hν (Kernel.measurable_coe _ hC) hK,
    fun y hy hyC => ?_⟩
  calc ∫⁻ z, resolventHalf P z C ∂ν ≤ ∫⁻ z, resolventHalf P z C ∂sampledKernel P a y :=
        lintegral_mono' (hle y hy) le_rfl
    _ = sampledKernel P (sampleConv a (geomDist 2⁻¹)) y C := by
        rw [lemma_5_5_2_i P a _ y hC]; rfl
    _ ≤ pathKernel P y {ω | ∃ n, ω n ∈ C} :=
        lemma_5_5_1_firstHit P (isSamplingDist_sampleConv ha isSamplingDist_geomDist_half) hC y
    _ ≤ pathKernel P y {ω | ω 0 ∈ C} + hitProb P C y := by
        refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
        obtain ⟨n, hn⟩ := hω
        rcases n with _ | n
        · exact Or.inl hn
        · exact Or.inr ((firstReturn_ne_top_iff C ω).2 ⟨n + 1, by omega, hn⟩)
    _ = hitProb P C y := by rw [pathKernel_zero_mem P y hC, indicator_of_notMem hyC, zero_add]

/-- **The hitting conclusion of Theorem 8.4.3** (MT p. 190), for `C ∈ B⁺(X)`: if `V : X → ℝ₊` is
unbounded off petite sets and `ΔV ≤ 0` off `C` (V1), then `L(x, C) = 1` for every `x`. -/
theorem lemma_8_4_3_hitProb (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {C : Set X} (hC : MeasurableSet C) (hφC : 0 < φ C)
    {V : X → ℝ≥0} (hVm : Measurable V) (hpet : ∀ n : ℕ, IsPetite P {x | V x ≤ n})
    (hdrift : ∀ x ∉ C, drift P (fun y => (V y : ℝ≥0∞)) x ≤ 0) (x : X) :
    hitProb P C x = 1 := by
  have hVm' : Measurable fun y => (V y : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hVm
  have hdr : ∀ x ∉ C, ∫⁻ y, (V y : ℝ≥0∞) ∂P x ≤ V x := fun x hx =>
    (drift_nonpos_iff P _ x).1 (hdrift x hx)
  -- first, `L(x, C) = 1` off `C`
  have hoff : ∀ x ∉ C, hitProb P C x = 1 := by
    intro x hx
    by_contra hne
    have hlt : hitProb P C x < 1 := lt_of_le_of_ne (hitProb_le_one P C x) hne
    set q := 1 - hitProb P C x with hq
    have hq0 : 0 < q := tsub_pos_of_lt hlt
    have hq2 : q / 2 ≠ 0 := (ENNReal.div_pos_iff.2 ⟨hq0.ne', ENNReal.ofNat_ne_top⟩).ne'
    -- choose `M` with `V(x) < M q / 2`
    obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top ENNReal.coe_ne_top hq2)
    have hVM : (V x : ℝ≥0∞) < M * (q / 2) := by
      rwa [ENNReal.div_lt_iff (Or.inl hq2) (Or.inr ENNReal.coe_ne_top)] at hM
    set A := {y | V y ≤ M} with hA
    have hAm : MeasurableSet A := measurableSet_le hVm measurable_const
    obtain ⟨δ, hδ, hδA⟩ := IsPetite.hitProb_ge P hφ (hpet M) hC hφC
    -- for every `n`, `∫ (P I_{Cᶜ})ⁿ(x, dy) L(y, C) ≥ δ q / 2`
    have hlow : ∀ n, δ * (q / 2) ≤ ∑' k, tabooKernel P hC (k + n) x C := by
      intro n
      have hKn := lintegral_killedKernel_pow_le P hC hVm' hdr n x hx
      have hAc : (killedKernel P hC ^ n) x Aᶜ ≤ q / 2 := by
        by_contra hc
        push Not at hc
        have : (M : ℝ≥0∞) * (q / 2) ≤ V x := by
          calc (M : ℝ≥0∞) * (q / 2) ≤ M * (killedKernel P hC ^ n) x Aᶜ :=
                mul_le_mul' le_rfl hc.le
            _ = ∫⁻ _ in Aᶜ, (M : ℝ≥0∞) ∂(killedKernel P hC ^ n) x := by rw [setLIntegral_const,
                mul_comm]
            _ ≤ ∫⁻ y in Aᶜ, (V y : ℝ≥0∞) ∂(killedKernel P hC ^ n) x :=
                setLIntegral_mono' hAm.compl fun y hy => by
                  simp only [hA, mem_compl_iff, mem_ofPred_eq, not_le] at hy
                  exact_mod_cast hy.le
            _ ≤ ∫⁻ y, (V y : ℝ≥0∞) ∂(killedKernel P hC ^ n) x := setLIntegral_le_lintegral _ _
            _ ≤ V x := hKn
        exact absurd hVM (not_lt.2 this)
      have huniv : q ≤ (killedKernel P hC ^ n) x univ := by
        have h1 := sum_tabooKernel_add_killed P hC n x
        have h2 : ∑ k ∈ Finset.range n, tabooKernel P hC k x C ≤ hitProb P C x := by
          rw [hitProb_eq_tsum P hC x]; exact ENNReal.sum_le_tsum _
        rw [hq]
        calc 1 - hitProb P C x ≤ 1 - ∑ k ∈ Finset.range n, tabooKernel P hC k x C :=
              tsub_le_tsub_left h2 1
          _ ≤ _ := by rw [← h1]; exact tsub_le_iff_left.2 le_rfl
      have hAn : q / 2 ≤ (killedKernel P hC ^ n) x (A ∩ Cᶜ) := by
        have h1 : (killedKernel P hC ^ n) x univ ≤
            (killedKernel P hC ^ n) x (A ∩ Cᶜ) + (killedKernel P hC ^ n) x C +
              (killedKernel P hC ^ n) x Aᶜ := by
          refine (measure_mono fun y _ => ?_).trans ((measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) le_rfl))
          by_cases hyA : y ∈ A
          · by_cases hyC : y ∈ C
            · exact Or.inl (Or.inr hyC)
            · exact Or.inl (Or.inl ⟨hyA, hyC⟩)
          · exact Or.inr hyA
        have hC0 : (killedKernel P hC ^ n) x C = 0 := by
          rcases n with _ | n
          · rw [pow_zero_apply, Measure.dirac_apply' _ hC, indicator_of_notMem hx]
          · exact killedKernel_pow_succ_apply_self P hC n x
        rw [hC0, add_zero] at h1
        have h2 : q ≤ (killedKernel P hC ^ n) x (A ∩ Cᶜ) + q / 2 :=
          huniv.trans (h1.trans (add_le_add le_rfl hAc))
        calc q / 2 = q - q / 2 := (ENNReal.sub_half (ne_top_of_le_ne_top ENNReal.one_ne_top
              tsub_le_self)).symm
          _ ≤ _ := tsub_le_iff_right.2 h2
      rw [← lintegral_killedKernel_hitProb P hC n x]
      calc δ * (q / 2) ≤ δ * (killedKernel P hC ^ n) x (A ∩ Cᶜ) := mul_le_mul' le_rfl hAn
        _ = ∫⁻ _ in A ∩ Cᶜ, δ ∂(killedKernel P hC ^ n) x := by rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ y in A ∩ Cᶜ, hitProb P C y ∂(killedKernel P hC ^ n) x :=
            setLIntegral_mono' (hAm.inter hC.compl) fun y hy => hδA y hy.1 hy.2
        _ ≤ _ := setLIntegral_le_lintegral _ _
    -- the tail of a convergent series tends to `0`
    have hfinL : ∑' k, tabooKernel P hC k x C ≠ ∞ := by
      rw [← hitProb_eq_tsum P hC x]
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (hitProb_le_one P C x)
    have htend := ENNReal.tendsto_sum_nat_add (fun k => tabooKernel P hC k x C) hfinL
    have hpos : 0 < δ * (q / 2) := ENNReal.mul_pos hδ.ne' hq2
    have := (htend.eventually (gt_mem_nhds hpos)).exists
    obtain ⟨n, hn⟩ := this
    exact absurd (hlow n) (not_le.2 hn)
  by_cases hx : x ∈ C
  · rw [hitProb_first_step P hC x, setLIntegral_congr_fun hC.compl fun y hy => hoff y hy,
      setLIntegral_const, one_mul, measure_add_measure_compl hC, measure_univ]
  · exact hoff x hx

/-- **Theorem 8.4.3** (MT p. 190): if a `ψ`-irreducible chain has a petite set `C` and a function
`V : X → ℝ₊` unbounded off petite sets (every `C_V(n) = {V ≤ n}` petite) with `ΔV ≤ 0` on `Cᶜ`
(V1), then the chain is recurrent; and `L(x, C) = 1` for every `x` when `C ∈ B⁺(X)`. -/
theorem theorem_8_4_3 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : IsPetite P C) {V : X → ℝ≥0}
    (hVm : Measurable V) (hpet : ∀ n : ℕ, IsPetite P {x | V x ≤ n})
    (hdrift : ∀ x ∉ C, drift P (fun y => (V y : ℝ≥0∞)) x ≤ 0) :
    IsRecurrentChain P ψ ∧ (0 < ψ C → ∀ x, hitProb P C x = 1) := by
  have hCm : MeasurableSet C := by obtain ⟨a, ν, h, -⟩ := hC; exact h
  refine ⟨?_, fun hψC x => lemma_8_4_3_hitProb P hψ.2.1 hCm hψC hVm hpet hdrift x⟩
  -- some `C_V(n₀)` lies in `B⁺(X)`
  have hcov : ⋃ n : ℕ, {x | V x ≤ n} = univ := eq_univ_of_forall fun x => by
    obtain ⟨n, hn⟩ := exists_nat_ge (V x)
    exact mem_iUnion.2 ⟨n, hn⟩
  have : ∃ n : ℕ, 0 < ψ {x | V x ≤ n} := by
    by_contra hc
    push Not at hc
    have h0 : ψ (⋃ n : ℕ, {x | V x ≤ n}) = 0 :=
      measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc n)
    rw [hcov] at h0
    exact hψ.1 (Measure.measure_univ_eq_zero.1 h0)
  obtain ⟨n₀, hn₀⟩ := this
  have hn₀m : MeasurableSet {x | V x ≤ n₀} := measurableSet_le hVm measurable_const
  set C' := C ∪ {x | V x ≤ n₀}
  have hC'm : MeasurableSet C' := hCm.union hn₀m
  have hψC' : 0 < ψ C' := hn₀.trans_le (measure_mono subset_union_right)
  have hL : ∀ x, hitProb P C' x = 1 := lemma_8_4_3_hitProb P hψ.2.1 hC'm hψC' hVm hpet
    (fun x hx => hdrift x fun hxC => hx (Or.inl hxC))
  rcases theorem_8_3_4 P hψ with h | h
  · exact h
  · obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hψC'.ne'
    have hrec := proposition_8_3_1_ii P hC'm fun x _ => hL x
    obtain ⟨M, hM, hb⟩ :=
      ((theorem_8_3_5 P h.2 hC).union (theorem_8_3_5 P h.2 (hpet n₀))).exists_bound
    exact absurd (top_le_iff.1 (hrec y hy ▸ hb y)) hM

/-- **Theorem 8.0.2 (ii)** (MT p. 172): a `ψ`-irreducible chain with a petite set `C` and a
function `V` unbounded off petite sets with `ΔV ≤ 0` on `Cᶜ` (8.4) is recurrent. -/
theorem theorem_8_0_2_ii (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : IsPetite P C) {V : X → ℝ≥0}
    (hVm : Measurable V) (hpet : ∀ n : ℕ, IsPetite P {x | V x ≤ n})
    (hdrift : ∀ x ∉ C, drift P (fun y => (V y : ℝ≥0∞)) x ≤ 0) : IsRecurrentChain P ψ :=
  (theorem_8_4_3 P hψ hC hVm hpet hdrift).1

/-- **Correction to Theorem 8.4.3**: `L(x, C) ≡ 1` fails for the petite set `C = ∅`. On the
one-point space, `V = 0` satisfies (V1) with `C = ∅` and every `C_V(n) = X` is petite, but
`L(x, ∅) = 0`. -/
theorem theorem_8_4_3_counterexample :
    let P : Kernel Unit Unit := Kernel.id
    IsPetite P (∅ : Set Unit) ∧ (∀ n : ℕ, IsPetite P {_x : Unit | (0 : ℝ≥0) ≤ n}) ∧
      (∀ x ∉ (∅ : Set Unit), drift P (fun _ => ((0 : ℝ≥0) : ℝ≥0∞)) x ≤ 0) ∧
      ∃ x, hitProb P (∅ : Set Unit) x ≠ 1 := by
  intro P
  have hpet : IsPetite P (univ : Set Unit) :=
    ⟨diracDist 1, Measure.dirac (), MeasurableSet.univ, isSamplingDist_diracDist 1,
      by simp, fun x _ => by
        rw [sampledKernel_diracDist, pow_one]
        change Measure.dirac () ≤ Kernel.id x
        rw [Kernel.id_apply, Subsingleton.elim x ()]⟩
  refine ⟨⟨diracDist 1, Measure.dirac (), MeasurableSet.empty, isSamplingDist_diracDist 1,
    by simp, fun x hx => absurd hx (notMem_empty x)⟩, fun n => ?_, fun x _ => ?_, (), ?_⟩
  · have : {_x : Unit | (0 : ℝ≥0) ≤ n} = univ := eq_univ_of_forall fun _ => by simp
    rw [this]; exact hpet
  · rw [drift_nonpos_iff]; simp
  · have := isMarkovKernel_pathKernel P
    have h0 : {ω : ℕ → Unit | firstReturn ∅ ω ≠ ⊤} = ∅ := by
      ext ω; simp [firstReturn, hittingAfter_empty]
    rw [hitProb, h0, measure_empty]
    exact zero_ne_one

/-- **(8.43)**, MT p. 189: on a countably generated space, for a `ψ`-irreducible chain, `V` is
unbounded off petite sets as soon as every sublevel set `C_V(n)` is contained in a finite union
of petite sets (a finite union of petite sets is petite, Proposition 5.5.5 (ii), and a measurable
subset of a petite set is petite). -/
theorem unboundedOffPetite_of_cover [MeasurableSpace.CountablyGenerated X] (P : Kernel X X)
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0}
    (hVm : Measurable V) {Cj : ℕ → Set X} (hCj : ∀ j, IsPetite P (Cj j))
    (hcov : ∀ n : ℕ, ∃ N, {x | V x ≤ n} ⊆ ⋃ j ∈ Finset.range N, Cj j) :
    ∀ n : ℕ, IsPetite P {x | V x ≤ n} := by
  have hfin : ∀ N, IsPetite P (⋃ j ∈ Finset.range (N + 1), Cj j) := by
    intro N
    induction N with
    | zero => simpa using hCj 0
    | succ N ih =>
      rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
      exact proposition_5_5_5_ii P hψ ih (hCj (N + 1))
  intro n
  obtain ⟨N, hN⟩ := hcov n
  obtain ⟨a, ν, -, ha, hν, hle⟩ := hfin N
  exact ⟨a, ν, measurableSet_le hVm measurable_const, ha, hν, fun x hx =>
    hle x (biUnion_subset_biUnion_left (Finset.coe_subset.2
      (Finset.range_subset_range.2 (Nat.le_succ N))) (hN hx))⟩

end MeynTweedie.DriftRegularity
