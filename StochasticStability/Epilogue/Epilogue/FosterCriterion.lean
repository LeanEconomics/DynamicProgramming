/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.RegularSets
import Epilogue.PositiveNull

/-!
# Foster's criterion: drift criteria for regularity (MT §11.3)

Copied for Chapter 13 from the Chapter 11 project
(`DriftRegularity/FosterCriterion.lean`), with the namespace changed to
`MeynTweedie.Epilogue` and the imports to this project's modules.

Meyn and Tweedie, §11.3, pp. 263–272. `ψ` is a maximal irreducibility measure; where small sets
are needed (Theorem 5.2.2) the state space is countably generated.

**The drift condition (V2)** (11.17), p. 263. `DriftV2 P V b C` is `PV ≤ V − 1 + b 1_C`, in the
form `PV + 1 ≤ V + b 1_C`, for `V : X → [0, ∞]`; `driftV2_iff_drift` shows that it is the book's
`ΔV ≤ −1 + b 1_C` for the extended-valued drift `ΔV` of Chapter 8.

**Results.**
* **Theorem 11.3.4** (p. 266): `theorem_11_3_4`, under (V2), `E_x[τ_C] ≤ V(x) + b 1_C(x)`;
  `theorem_11_3_4_positiveHarris`: if `C` is petite and `V` is finite, and bounded on `C`, the
  chain is positive Harris.
* **Lemma 11.3.6** (`lemma_11_3_6`, p. 268): a solution of (V2) is finite `ψ`-a.e. or infinite
  everywhere; `isAbsorbing_finite_of_driftV2`: `{V < ∞}` is absorbing.
* **Lemma 11.3.7** (`lemma_11_3_7`, p. 268): for petite `C` the sublevel sets of `V_C` are petite
  (`V_C` is unbounded off petite sets); `isPetite_meanHitTime_le` is the core estimate.
* **Proposition 11.3.8** (`proposition_11_3_8`, p. 268): a regular set is petite.
* **Lemma 11.3.9** (`lemma_11_3_9`, p. 269): under (V2),
  `E_x[τ_B] ≤ V(x) + b E_x[Σ_{k<τ_B} 1_C(Φ_k)]`.
* **Theorem 11.3.11** (p. 270): (i) `theorem_11_3_11_i`, under (V2) with `C` petite, every
  `B ∈ B⁺(X)` has `E_x[τ_B] ≤ V(x) + c(B)`, and `theorem_11_3_11_i_regular`: every measurable set on
  which `V` is bounded is regular; (ii) `theorem_11_3_11_ii`, a regular `C ∈ B⁺(X)` is petite and
  `V_C` solves (V2), bounded on every regular set.
* **Theorem 11.3.12** (p. 271): `theorem_11_3_12_i` and `theorem_11_3_12_ii`, the same for regular
  initial measures.
* **Proposition 11.3.13** (`proposition_11_3_13`, p. 271): if a regular `C ∈ B⁺(X)` exists, the
  sublevel sets of `V_C` are regular and `S_C = {V_C < ∞}` is full, absorbing and covered by them.
* **Theorem 11.3.14** (`theorem_11_3_14`, p. 271): `C` is petite, non-empty, with
  `sup_C E_x[τ_C] < ∞` iff `C` is regular and `C ∈ B⁺(X)`.
* **Theorem 11.3.15** (`theorem_11_3_15`, p. 271): the chain is regular iff (V2) holds for a petite
  set and a finite `V`, iff some petite `C` has `E_x[τ_C]` finite everywhere and bounded on `C`.

**Correction.** Theorem 11.3.14 (i) ⇒ (ii) fails for `C = ∅`, which is petite with
`sup_{x ∈ ∅} E_x[τ_∅] = 0` but is not in `B⁺(X)` (`theorem_11_3_14_counterexample`); the book's
proof uses that `C` is Harris recurrent, which for `C = ∅` gives nothing. The theorem holds for
non-empty `C`.

**Hypotheses.** The bound `b` in (V2) is finite (`b ≠ ∞`), as in the book (`b < ∞`). Test
functions are measurable, which the book uses implicitly (for `PV` to be defined).
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X}

/-! ### The drift condition (V2) -/

/-- **The drift condition (V2)** (11.17), MT p. 263: `PV ≤ V − 1 + b 1_C`, written
`PV + 1 ≤ V + b 1_C` for `V : X → [0, ∞]`. -/
def DriftV2 (P : Kernel X X) (V : X → ℝ≥0∞) (b : ℝ≥0∞) (C : Set X) : Prop :=
  ∀ x, ∫⁻ y, V y ∂P x + 1 ≤ V x + C.indicator (fun _ => b) x

omit [MeasurableSpace X] in
/-- In `[0, ∞]`, `a + 1 ≤ v + c` iff `a − v ≤ −1 + c` in the extended reals. -/
theorem add_one_le_iff_ereal (a v c : ℝ≥0∞) :
    a + 1 ≤ v + c ↔ (a : EReal) - (v : EReal) ≤ -1 + (c : EReal) := by
  have hm1 : (-1 : EReal) = ((-1 : ℝ) : EReal) := by norm_num
  have e : ∀ r : NNReal, ((r : ℝ≥0∞) : EReal) = ((r : ℝ) : EReal) := fun r => rfl
  rcases eq_or_ne v ⊤ with rfl | hv
  · simp
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp only [add_top, le_top, true_iff, EReal.coe_ennreal_top]
    rw [hm1, EReal.coe_add_top]
    exact le_top
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp only [top_add, top_le_iff, ENNReal.add_eq_top, hv, hc, or_self, false_iff, not_le,
      EReal.coe_ennreal_top]
    lift v to NNReal using hv
    lift c to NNReal using hc
    rw [e, e, EReal.top_sub_coe, hm1, ← EReal.coe_add]
    exact EReal.coe_lt_top _
  lift v to NNReal using hv
  lift c to NNReal using hc
  lift a to NNReal using ha
  rw [e, e, e, hm1, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff,
    ← ENNReal.coe_one, ← ENNReal.coe_add, ← ENNReal.coe_add, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe]
  push_cast
  constructor <;> intro h <;> linarith

/-- (V2) is the book's `ΔV ≤ −1 + b 1_C` (11.17) for the extended-valued drift
`ΔV = PV − V` of (8.1) (with `ΔV(x) = −∞` where `V(x) = ∞` and `PV(x) < ∞`). -/
theorem driftV2_iff_drift (P : Kernel X X) (V : X → ℝ≥0∞) (b : ℝ≥0∞) (C : Set X) :
    DriftV2 P V b C ↔ ∀ x, drift P V x ≤ -1 + ((C.indicator (fun _ => b) x : ℝ≥0∞) : EReal) :=
  forall_congr' fun _ => add_one_le_iff_ereal _ _ _

/-- Off `C`, (V2) is `PV + 1 ≤ V` (11.18). -/
theorem DriftV2.of_notMem {V : X → ℝ≥0∞} {b : ℝ≥0∞} {C : Set X} (h : DriftV2 P V b C) {x : X}
    (hx : x ∉ C) : ∫⁻ y, V y ∂P x + 1 ≤ V x := by
  simpa [indicator_of_notMem hx] using h x

/-- On `C`, (V2) gives `PV ≤ V + b` (11.19). -/
theorem DriftV2.le_add {V : X → ℝ≥0∞} {b : ℝ≥0∞} {C : Set X} (h : DriftV2 P V b C) (x : X) :
    ∫⁻ y, V y ∂P x ≤ V x + b :=
  le_self_add.trans ((h x).trans (add_le_add le_rfl (indicator_le_self' (fun _ _ => zero_le) x)))

/-! ### Theorem 11.3.4 and Lemma 11.3.9 -/

/-- `E_x[τ_A] = E_x[Σ_{k<τ_A} 1]`. -/
theorem meanReturnTime_eq_sumBefore [IsMarkovKernel P] (A : Set X) (x : X) :
    meanReturnTime P A x = ∫⁻ ω, sumBefore (firstReturn A) (fun _ _ => 1) ω ∂pathKernel P x := by
  simp_rw [meanReturnTime, toENNReal_eq_sumBefore_one]

/-- **Theorem 11.3.4** (MT p. 266): under (V2), `E_x[τ_C] ≤ V(x) + b 1_C(x)` for every `x`. -/
theorem theorem_11_3_4 [IsMarkovKernel P] {V : X → ℝ≥0∞} (hV : Measurable V) {b : ℝ≥0∞}
    {C : Set X} (hC : MeasurableSet C) (h : DriftV2 P V b C) (x : X) :
    meanReturnTime P C x ≤ V x + C.indicator (fun _ => b) x := by
  have h2 := (proposition_11_3_3 P hC (z := fun _ => V) (ε := fun _ _ => 1) (c := 1)
    (fun _ => hV) (fun _ => measurable_const) (fun _ _ _ => by rw [one_mul])
    (fun _ y hy => h.of_notMem hy)).2 x
  rw [meanReturnTime_eq_sumBefore]
  refine h2.trans ?_
  rw [one_mul, add_comm]
  exact h x

/-- **Lemma 11.3.9** (MT p. 269): under (V2), for every measurable `B`,
`E_x[τ_B] ≤ V(x) + b E_x[Σ_{k<τ_B} 1_C(Φ_k)]`. -/
theorem lemma_11_3_9 [IsMarkovKernel P] {V : X → ℝ≥0∞} (hV : Measurable V) {b : ℝ≥0∞}
    {C : Set X} (hC : MeasurableSet C) (h : DriftV2 P V b C) {B : Set X} (hB : MeasurableSet B)
    (x : X) :
    meanReturnTime P B x ≤ V x +
      b * ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => C.indicator 1 (ω k)) ω ∂pathKernel P x := by
  have hc := comparison_theorem_pathKernel P hV measurable_const
    (measurable_const.indicator hC) (D := univ) (fun y _ => h y) (proposition_3_4_4 hB).1
    (fun _ _ _ => mem_univ _) x
  have hs : ∀ ω : ℕ → X, sumBefore (firstReturn B) (fun k ω => C.indicator (fun _ => b) (ω k)) ω
      = b * sumBefore (firstReturn B) (fun k ω => C.indicator 1 (ω k)) ω := fun ω => by
    rw [← sumBefore_const_mul]
    refine sumBefore_congr _ fun k _ => ?_
    by_cases hk : ω k ∈ C <;> simp [hk]
  simp_rw [hs] at hc
  rw [lintegral_const_mul _ (measurable_sumBefore (measurableSet_lt_firstReturn hB)
    (F := fun k ω => C.indicator 1 (ω k))
    fun k => (measurable_one.indicator hC).comp (measurable_pi_apply k))] at hc
  rw [meanReturnTime_eq_sumBefore]
  exact hc

/-- If `E_x[τ_C] < ∞` for every `x` then `C` is non-empty (when `X` is). -/
theorem nonempty_of_meanReturnTime_ne_top [IsMarkovKernel P] {C : Set X} (hC : MeasurableSet C)
    {x : X} (hx : meanReturnTime P C x ≠ ∞) : C.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  have h := hitProb_eq_one_of_meanReturnTime_ne_top hC hx
  have h0 : hitProb P ∅ x = 0 := by
    have : {ω : ℕ → X | firstReturn ∅ ω ≠ ⊤} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, firstReturn_ne_top_iff]
      simp
    rw [hitProb, this, measure_empty]
  rw [h0] at h
  exact zero_ne_one h

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.3.4**, positivity (MT p. 266): if (V2) holds for a petite set `C` and a function
`V` that is finite everywhere and bounded on `C`, the chain is positive Harris recurrent. -/
theorem theorem_11_3_4_positiveHarris [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0∞} (hV : Measurable V) {b : ℝ≥0∞}
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV2 P V b C) (hfin : ∀ x, V x ≠ ∞)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hVC : ∀ x ∈ C, V x ≤ M) : IsPositiveHarris P ψ := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hbound : ∀ x, meanReturnTime P C x ≠ ∞ := fun x =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin x, by
      by_cases hx : x ∈ C <;> simp [hx, hb]⟩) (theorem_11_3_4 hV hCm h x)
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    exact hψ.1 (Measure.eq_zero_of_isEmpty ψ)
  have hne := nonempty_of_meanReturnTime_ne_top hCm (hbound x₀)
  have hL : ∀ y ∈ C, hitProb P C y = 1 := fun y _ =>
    hitProb_eq_one_of_meanReturnTime_ne_top hCm (hbound y)
  have hψC := (theorem_8_3_6_i P hψ hC hne hL).2
  have hsup : ∀ y ∈ C, meanReturnTime P C y ≤ M + b := fun y hy =>
    (theorem_11_3_4 hV hCm h y).trans (by
      rw [indicator_of_mem hy]; exact add_le_add (hVC y hy) le_rfl)
  exact (theorem_10_4_10_ii hψ hC hψC (ENNReal.add_ne_top.2 ⟨hM, hb⟩) hsup).2.2 hbound

/-! ### Lemma 11.3.6 -/

/-- Under (V2) with `b < ∞`, the set `{V < ∞}` is absorbing. -/
theorem isAbsorbing_finite_of_driftV2 [IsMarkovKernel P] {V : X → ℝ≥0∞} (hV : Measurable V)
    {b : ℝ≥0∞}
    (hb : b ≠ ∞) {C : Set X} (h : DriftV2 P V b C) : IsAbsorbing P {x | V x ≠ ∞} := by
  intro x hx
  have hPV : ∫⁻ y, V y ∂P x ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hx, hb⟩) (h.le_add x)
  have hae := ae_lt_top hV hPV
  have hm : MeasurableSet {y | V y ≠ ∞} := (measurableSet_singleton ∞).compl.preimage hV
  have h0 : P x {y | V y ≠ ∞}ᶜ = 0 := by
    have h1 : P x {y | ¬ V y < ∞} = 0 := ae_iff.1 hae
    have h2 : {y | V y ≠ ∞}ᶜ = {y | ¬ V y < ∞} := by
      ext y; simp [lt_top_iff_ne_top]
    rw [h2, h1]
  exact (prob_compl_eq_zero_iff hm).1 h0

/-- **Lemma 11.3.6** (MT p. 268): a solution `V` of (V2) (with `b < ∞`) is finite `ψ`-almost
everywhere, or infinite everywhere. -/
theorem lemma_11_3_6 [IsMarkovKernel P] {φ : Measure X} (hφ : IsPhiIrreducible P φ)
    {V : X → ℝ≥0∞} (hV : Measurable V) {b : ℝ≥0∞} (hb : b ≠ ∞) {C : Set X}
    (h : DriftV2 P V b C) : IsFull φ {x | V x ≠ ∞} ∨ ∀ x, V x = ∞ := by
  by_cases hne : {x | V x ≠ ∞}.Nonempty
  · exact Or.inl (proposition_4_2_3_i hφ ((measurableSet_singleton ∞).compl.preimage hV) hne
      (isAbsorbing_finite_of_driftV2 hV hb h))
  · refine Or.inr fun x => ?_
    by_contra hx
    exact hne ⟨x, hx⟩

/-! ### Petite sublevel sets: Lemma 11.3.7 and Proposition 11.3.8 -/

omit [MeasurableSpace X] in
/-- If `σ_A < n` then the path visits `A` at some time `j < n`. -/
theorem exists_mem_of_toENNReal_firstHit_lt {A : Set X} {ω : ℕ → X} {n : ℕ}
    (h : ENat.toENNReal (firstHit A ω) < n) : ∃ j < n, ω j ∈ A := by
  by_contra hc
  push Not at hc
  have hle := (le_firstHit_iff A ω n).2 hc
  have : (n : ℝ≥0∞) ≤ ENat.toENNReal (firstHit A ω) := by
    rw [← toENNReal_some]; exact ENat.toENNReal_mono hle
  exact absurd h (not_lt.2 this)

/-- A measurable subset of a petite set is petite. -/
theorem IsPetite.subset {C D : Set X} (hC : IsPetite P C) (hD : MeasurableSet D) (hDC : D ⊆ C) :
    IsPetite P D := by
  obtain ⟨a, ν, hpet⟩ := hC
  exact ⟨a, ν, hD, hpet.2.1, hpet.2.2.1, fun x hx => hpet.2.2.2 x (hDC hx)⟩

/-- **The core of Lemma 11.3.7 and Proposition 11.3.8.** For a petite `C` and `ℓ < ∞`, the set
`{x : E_x[σ_C] ≤ ℓ}` is petite: from it the chain reaches `C` within `n` steps with probability
at least `1/2` (Chebyshev), so it leads uniformly to `C` (Proposition 5.5.4). -/
theorem isPetite_meanHitTime_le [IsMarkovKernel P] {C : Set X} (hC : IsPetite P C)
    {ℓ : ℝ≥0∞} (hℓ : ℓ ≠ ∞) : IsPetite P {x | meanHitTime P C x ≤ ℓ} := by
  have := isMarkovKernel_pathKernel P
  obtain ⟨a, ν, hpet⟩ := hC
  have hCm := hpet.1
  set D := {x | meanHitTime P C x ≤ ℓ} with hDdef
  have hDm : MeasurableSet D := measurableSet_le (measurable_meanHitTime P hCm) measurable_const
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hℓ :
    (2 : ℝ≥0∞) * ℓ ≠ ∞)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := (lt_of_le_of_lt zero_le hn).ne'
  -- for `x ∈ D`, `Σ_{j<n} Pʲ(x, C) ≥ 1/2`
  have hhalf : ∀ x ∈ D, (2⁻¹ : ℝ≥0∞) ≤ ∑ j ∈ Finset.range n, (P ^ j) x C := by
    intro x hx
    have hmeas := measurable_toENNReal_firstHit (X := X) hCm
    have hcheb := mul_meas_ge_le_lintegral₀ hmeas.aemeasurable (μ := pathKernel P x) (n : ℝ≥0∞)
    set E := {ω : ℕ → X | (n : ℝ≥0∞) ≤ ENat.toENNReal (firstHit C ω)} with hEdef
    have hEm : MeasurableSet E := measurableSet_le measurable_const hmeas
    have hbig : pathKernel P x E ≤ 2⁻¹ := by
      have h1 : (n : ℝ≥0∞) * pathKernel P x E ≤ ℓ := hcheb.trans hx
      have h2 : ℓ ≤ (n : ℝ≥0∞) * 2⁻¹ := by
        calc ℓ = 2⁻¹ * (2 * ℓ) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
          _ ≤ 2⁻¹ * n := by gcongr
          _ = (n : ℝ≥0∞) * 2⁻¹ := mul_comm _ _
      exact (ENNReal.mul_le_mul_iff_right hn0 (ENNReal.natCast_ne_top n)).1 (h1.trans h2)
    have hsmall : 2⁻¹ ≤ pathKernel P x Eᶜ := by
      rw [prob_compl_eq_one_sub hEm, ← ENNReal.one_sub_inv_two]
      exact tsub_le_tsub_left hbig 1
    refine hsmall.trans ?_
    calc pathKernel P x Eᶜ ≤ pathKernel P x (⋃ j ∈ Finset.range n, {ω | ω j ∈ C}) := by
          refine measure_mono fun ω hω => ?_
          have hlt : ENat.toENNReal (firstHit C ω) < n := not_le.1 hω
          obtain ⟨j, hj, hjC⟩ := exists_mem_of_toENNReal_firstHit_lt hlt
          exact mem_biUnion (Finset.mem_range.2 hj) hjC
      _ ≤ ∑ j ∈ Finset.range n, pathKernel P x {ω | ω j ∈ C} := measure_biUnion_finset_le _ _
      _ = ∑ j ∈ Finset.range n, (P ^ j) x C := by
          simp_rw [pathKernel_coord_mem P x _ hCm]
  -- `D` leads uniformly to `C` under the geometric sampling `a_{1/2}`
  set δ : ℝ≥0∞ := 2⁻¹ * (2⁻¹) ^ n * 2⁻¹ with hδdef
  have hδ : 0 < δ :=
    ENNReal.mul_pos (ENNReal.mul_pos (by simp) (pow_ne_zero _ (by simp))).ne' (by simp)
  have hacc : SampledAccessible P (geomDist 2⁻¹) D C := by
    refine ⟨δ, hδ, fun x hx => ?_⟩
    rw [sampledKernel_apply P _ x hCm]
    calc δ ≤ 2⁻¹ * (2⁻¹) ^ n * ∑ j ∈ Finset.range n, (P ^ j) x C := by
          rw [hδdef]; gcongr; exact hhalf x hx
      _ = ∑ j ∈ Finset.range n, 2⁻¹ * (2⁻¹) ^ n * (P ^ j) x C := Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ Finset.range n, geomDist 2⁻¹ j * (P ^ j) x C := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [geomDist, ENNReal.one_sub_inv_two]
          exact mul_le_mul' (mul_le_mul' le_rfl (pow_le_pow_right_of_le_one'
            (ENNReal.inv_le_one.2 one_le_two) (Finset.mem_range.1 hj).le)) le_rfl
      _ ≤ ∑' j, geomDist 2⁻¹ j * (P ^ j) x C := ENNReal.sum_le_tsum _
  obtain ⟨δ', -, hD⟩ := proposition_5_5_4_i P hpet hDm isSamplingDist_geomDist_half hacc
  exact ⟨_, _, hD⟩

/-- **Lemma 11.3.7** (MT p. 268): if `C` is petite then `V_C` is unbounded off petite sets: every
sublevel set `C_V(ℓ) = {x : V_C(x) ≤ ℓ}`, `ℓ < ∞`, is petite. -/
theorem lemma_11_3_7 [IsMarkovKernel P] {C : Set X} (hC : IsPetite P C) {ℓ : ℝ≥0∞}
    (hℓ : ℓ ≠ ∞) : IsPetite P {x | regV P C x ≤ ℓ} := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  refine (isPetite_meanHitTime_le hC hℓ).subset
    (measurableSet_le (measurable_regV P hCm) measurable_const) fun x hx => ?_
  exact le_trans le_add_self (show 1 + meanHitTime P C x ≤ ℓ from hx)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 11.3.8** (MT p. 268): a regular set is petite. -/
theorem proposition_11_3_8 [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {A : Set X} (hA : IsRegularSet P ψ A) : IsPetite P A := by
  obtain ⟨C, hC, hψC⟩ := exists_petite_pos hψ
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨M, hM, hbound⟩ := hA.2 C hCm hψC
  exact (isPetite_meanHitTime_le hC hM).subset hA.1 fun x hx =>
    (meanHitTime_le_meanReturnTime P hCm x).trans (hbound x hx)

/-! ### Theorem 11.3.11 -/

omit [MeasurableSpace X] in
/-- Before `τ_B` the shifted path `Φ_{k+i}` visits `B` at most `i + 1` times:
`Σ_{k<τ_B} 1_B(Φ_{k+i}) ≤ i + 1` (proof of Theorem 11.3.11). -/
theorem sumBefore_firstReturn_shift_le (B : Set X) (i : ℕ) (ω : ℕ → X) :
    sumBefore (firstReturn B) (fun k ω => B.indicator 1 (ω (k + i))) ω ≤ i + 1 := by
  classical
  -- a visit `Φ_{k+i} ∈ B` with `k < τ_B` has `k + i = 0` or `k + i ≥ τ_B`
  have key : ∀ k : ℕ, (k : WithTop ℕ) < firstReturn B ω → ω (k + i) ∈ B →
      k + i = 0 ∨ firstReturn B ω ≤ WithTop.some (k + i) := by
    intro k _ hB
    by_contra hc
    push Not at hc
    have hle : WithTop.some (k + i + 1) ≤ firstReturn B ω := by
      cases h : firstReturn B ω with
      | top => exact le_top
      | coe t =>
        rw [h] at hc
        have : k + i < t := WithTop.coe_lt_coe.1 hc.2
        exact WithTop.coe_le_coe.2 this
    exact (le_firstReturn_iff B ω (k + i + 1)).1 hle (k + i) (by omega) (by omega) hB
  -- the indices of the visits lie in a set of at most `i + 1` elements
  obtain ⟨S, hS, hcard⟩ : ∃ S : Finset ℕ, (∀ k : ℕ, (k : WithTop ℕ) < firstReturn B ω →
      ω (k + i) ∈ B → k ∈ S) ∧ S.card ≤ i + 1 := by
    cases h : firstReturn B ω with
    | top =>
      refine ⟨{0}, fun k hk hB => ?_, by simp⟩
      rcases key k (by rw [h]; exact hk) hB with h0 | h0
      · simp; omega
      · rw [h] at h0; exact absurd h0 (by simp)
    | coe t =>
      refine ⟨insert 0 (Finset.Ico (t - i) t), fun k hk hB => ?_, ?_⟩
      · rcases key k (by rw [h]; exact hk) hB with h0 | h0
        · exact Finset.mem_insert.2 (Or.inl (by omega))
        · rw [h] at h0
          have h1 : t ≤ k + i := WithTop.coe_le_coe.1 h0
          rw [Nat.cast_withTop] at hk
          have h2 : k < t := WithTop.coe_lt_coe.1 hk
          exact Finset.mem_insert.2 (Or.inr (Finset.mem_Ico.2 ⟨by omega, h2⟩))
      · refine (Finset.card_insert_le _ _).trans ?_
        rw [Nat.card_Ico]
        omega
  unfold sumBefore
  rw [tsum_eq_sum (s := S) fun k hk => ?_]
  · calc ∑ k ∈ S, {ω | (k : WithTop ℕ) < firstReturn B ω}.indicator
          (fun ω => B.indicator 1 (ω (k + i))) ω
        ≤ ∑ _k ∈ S, (1 : ℝ≥0∞) := Finset.sum_le_sum fun k _ => by
          by_cases h1 : (k : WithTop ℕ) < firstReturn B ω
          · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < firstReturn B ω} from h1)]
            exact indicator_le_self' (fun _ _ => zero_le) _ |>.trans (by simp)
          · rw [indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < firstReturn B ω} from h1)]
            exact zero_le
      _ = S.card := by simp
      _ ≤ i + 1 := by exact_mod_cast hcard
  · by_cases h1 : (k : WithTop ℕ) < firstReturn B ω
    · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < firstReturn B ω} from h1)]
      exact indicator_of_notMem (fun hB => hk (hS k h1 hB)) _
    · exact indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < firstReturn B ω} from h1) _

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.3.11 (i)** (MT p. 270): if (V2) holds for a petite set `C`, then for every
`B ∈ B⁺(X)` there is `c(B) < ∞` with `E_x[τ_B] ≤ V(x) + c(B)` for every `x`. -/
theorem theorem_11_3_11_i [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {V : X → ℝ≥0∞} (hV : Measurable V) {b : ℝ≥0∞} (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    (h : DriftV2 P V b C) {B : Set X} (hB : MeasurableSet B) (hψB : 0 < ψ B) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ x, meanReturnTime P B x ≤ V x + c := by
  have := isMarkovKernel_pathKernel P
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨a, ν, hpet⟩ := hC
  obtain ⟨b', ψb, hpet', hmax⟩ := proposition_5_5_5_i P hψ hpet
  have ht : 0 < ψb B := pos_iff_ne_zero.2 fun h0 => hψB.ne' ((hψ.equiv hmax).1 h0)
  obtain ⟨hε0, hεt, h2⟩ := half_min_spec ht
  set ε₀ := 2⁻¹ * min (ψb B) 1 with hε₀
  obtain ⟨K, hK⟩ := exists_tail_le hpet'.2.1 hε0
  have hb1 : ∀ k, b' k ≤ 1 := fun k => hpet'.2.1 ▸ ENNReal.le_tsum k
  -- the truncated weights `w = 1_{[0, K)}`
  set w : ℕ → ℝ≥0∞ := fun i => if i < K then 1 else 0 with hwdef
  have hwK : ∀ y, ∫⁻ z, B.indicator 1 z ∂sampledKernel P w y =
      ∑ i ∈ Finset.range K, (P ^ i) y B := fun y => by
    rw [lintegral_indicator_one hB, sampledKernel_apply P w y hB,
      tsum_eq_sum (s := Finset.range K) fun i hi => by
        simp [hwdef, Finset.mem_range.not.1 hi]]
    exact Finset.sum_congr rfl fun i hi => by simp [hwdef, Finset.mem_range.1 hi]
  -- (11.27): `1_C ≤ ε₀⁻¹ K_w(·, B)`
  have hC1 : ∀ y, C.indicator 1 y ≤ ε₀⁻¹ * ∫⁻ z, B.indicator 1 z ∂sampledKernel P w y := by
    intro y
    by_cases hy : y ∈ C
    · rw [indicator_of_mem hy, Pi.one_apply, hwK]
      have hhead := le_sum_head P K y hB hεt hK h2 (hpet'.2.2.2 y hy B)
      have hsum : ε₀ ≤ ∑ i ∈ Finset.range K, (P ^ i) y B := hhead.trans
        (Finset.sum_le_sum fun k _ => mul_le_of_le_one_left' (hb1 k))
      calc (1 : ℝ≥0∞) = ε₀⁻¹ * ε₀ := (ENNReal.inv_mul_cancel hε0.ne' hεt).symm
        _ ≤ _ := mul_le_mul' le_rfl hsum
    · rw [indicator_of_notMem hy]; exact zero_le
  set c : ℝ≥0∞ := b * (ε₀⁻¹ * ∑' i, w i * ((i : ℝ≥0∞) + 1)) with hcdef
  have hc : c ≠ ∞ := by
    refine ENNReal.mul_ne_top hb (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hε0.ne') ?_)
    rw [tsum_eq_sum (s := Finset.range K) fun i hi => by
      simp [hwdef, Finset.mem_range.not.1 hi]]
    exact ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top (by simp [hwdef]; split_ifs <;> simp)
      (by simp)
  refine ⟨c, hc, fun x => (lemma_11_3_9 hV hCm h hB x).trans (add_le_add le_rfl ?_)⟩
  refine mul_le_mul' le_rfl ?_
  calc ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => C.indicator 1 (ω k)) ω ∂pathKernel P x
      ≤ ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => ε₀⁻¹ *
          ∫⁻ z, B.indicator 1 z ∂sampledKernel P w (ω k)) ω ∂pathKernel P x :=
        lintegral_mono fun ω => sumBefore_mono _ (fun k ω => hC1 (ω k)) ω
    _ = ε₀⁻¹ * ∫⁻ ω, sumBefore (firstReturn B) (fun k ω =>
          ∫⁻ z, B.indicator 1 z ∂sampledKernel P w (ω k)) ω ∂pathKernel P x := by
        simp_rw [sumBefore_const_mul]
        exact lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hε0.ne')
    _ = ε₀⁻¹ * ∑' i, w i * ∫⁻ ω, sumBefore (firstReturn B)
          (fun k ω => B.indicator 1 (ω (k + i))) ω ∂pathKernel P x := by
        rw [lemma_11_3_10 P x (proposition_3_4_4 hB).1 w (measurable_one.indicator hB)]
    _ ≤ ε₀⁻¹ * ∑' i, w i * ((i : ℝ≥0∞) + 1) := by
        refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun i => mul_le_mul' le_rfl ?_)
        calc ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => B.indicator 1 (ω (k + i))) ω
              ∂pathKernel P x ≤ ∫⁻ _, ((i : ℝ≥0∞) + 1) ∂pathKernel P x :=
              lintegral_mono fun ω => by exact_mod_cast sumBefore_firstReturn_shift_le B i ω
          _ = (i : ℝ≥0∞) + 1 := by rw [lintegral_const, measure_univ, mul_one]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.3.11 (i)**, regularity (MT p. 270): under (V2) with `C` petite, every measurable
set on which `V` is bounded is regular. -/
theorem theorem_11_3_11_i_regular [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0∞} (hV : Measurable V) {b : ℝ≥0∞}
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV2 P V b C) {A : Set X}
    (hA : MeasurableSet A) {M : ℝ≥0∞} (hM : M ≠ ∞) (hVA : ∀ x ∈ A, V x ≤ M) :
    IsRegularSet P ψ A := by
  refine ⟨hA, fun B hB hψB => ?_⟩
  obtain ⟨c, hc, hbound⟩ := theorem_11_3_11_i hψ hV hb hC h hB hψB
  exact ⟨M + c, ENNReal.add_ne_top.2 ⟨hM, hc⟩, fun x hx =>
    (hbound x).trans (add_le_add (hVA x hx) le_rfl)⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.3.11 (ii)** (MT p. 270): a regular set `C ∈ B⁺(X)` is petite, and `V_C` solves
(V2) for `C` with a finite `b`; `V_C` is bounded on every regular set. -/
theorem theorem_11_3_11_ii [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {C : Set X} (hC : IsRegularSet P ψ C) (hψC : 0 < ψ C) :
    IsPetite P C ∧ ∃ b : ℝ≥0∞, b ≠ ∞ ∧ DriftV2 P (regV P C) b C ∧
      ∀ A, IsRegularSet P ψ A → ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ A, regV P C x ≤ M := by
  obtain ⟨b, hb, hbound⟩ := hC.2 C hC.1 hψC
  refine ⟨proposition_11_3_8 hψ hC, b, hb, regV_drift P hC.1 hbound, fun A hA => ?_⟩
  obtain ⟨M, hM, hAM⟩ := hA.2 C hC.1 hψC
  exact ⟨1 + M, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hM⟩, fun x hx =>
    (regV_le P hC.1 x).trans (add_le_add le_rfl (hAM x hx))⟩

/-! ### Theorem 11.3.12: regular measures -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.3.12 (i)** (MT p. 271): if (V2) holds for a petite `C` and `μ(V) < ∞` for a
probability measure `μ`, then `μ` is regular. -/
theorem theorem_11_3_12_i [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {V : X → ℝ≥0∞} (hV : Measurable V) {b : ℝ≥0∞} (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    (h : DriftV2 P V b C) {μ : Measure X} [IsProbabilityMeasure μ] (hμV : ∫⁻ x, V x ∂μ ≠ ∞) :
    IsRegularMeasure P ψ μ := by
  intro B hB hψB
  obtain ⟨c, hc, hbound⟩ := theorem_11_3_11_i hψ hV hb hC h hB hψB
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hμV, hc⟩) ?_
  calc ∫⁻ x, meanReturnTime P B x ∂μ ≤ ∫⁻ x, (V x + c) ∂μ := lintegral_mono hbound
    _ = ∫⁻ x, V x ∂μ + c := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- **Theorem 11.3.12 (ii)** (MT p. 271): if `μ` is a regular (finite) measure and a regular set
`C ∈ B⁺(X)` exists, then `V = V_C` solves (V2) with `μ(V) < ∞`. -/
theorem theorem_11_3_12_ii [IsMarkovKernel P] {ψ : Measure X} {μ : Measure X}
    [IsFiniteMeasure μ] (hμ : IsRegularMeasure P ψ μ) {C : Set X} (hC : IsRegularSet P ψ C)
    (hψC : 0 < ψ C) :
    ∃ (V : X → ℝ≥0∞) (b : ℝ≥0∞), Measurable V ∧ b ≠ ∞ ∧ DriftV2 P V b C ∧
      ∫⁻ x, V x ∂μ ≠ ∞ := by
  obtain ⟨b, hb, hbound⟩ := hC.2 C hC.1 hψC
  refine ⟨regV P C, b, measurable_regV P hC.1, hb, regV_drift P hC.1 hbound, ?_⟩
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨measure_ne_top μ univ, hμ C hC.1 hψC⟩) ?_
  calc ∫⁻ x, regV P C x ∂μ ≤ ∫⁻ x, (1 + meanReturnTime P C x) ∂μ :=
        lintegral_mono (regV_le P hC.1)
    _ = μ univ + ∫⁻ x, meanReturnTime P C x ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, one_mul]

/-! ### Proposition 11.3.13, Theorems 11.3.14 and 11.3.15 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 11.3.13** (MT p. 271): if `C ∈ B⁺(X)` is regular, every sublevel set
`{V_C ≤ ℓ}`, `ℓ < ∞`, is regular, and `S_C = {V_C < ∞}` is full and absorbing and the chain is
regular on it. -/
theorem proposition_11_3_13 [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {C : Set X} (hC : IsRegularSet P ψ C) (hψC : 0 < ψ C) :
    (∀ ℓ : ℝ≥0∞, ℓ ≠ ∞ → IsRegularSet P ψ {x | regV P C x ≤ ℓ}) ∧
      IsFull ψ {x | regV P C x ≠ ∞} ∧ IsAbsorbing P {x | regV P C x ≠ ∞} ∧
      IsRegularOn P ψ {x | regV P C x ≠ ∞} := by
  obtain ⟨hpet, b, hb, hdrift, -⟩ := theorem_11_3_11_ii hψ hC hψC
  have hVm := measurable_regV P hC.1
  have hsub : ∀ ℓ : ℝ≥0∞, ℓ ≠ ∞ → IsRegularSet P ψ {x | regV P C x ≤ ℓ} := fun ℓ hℓ =>
    theorem_11_3_11_i_regular hψ hVm hb hpet hdrift (measurableSet_le hVm measurable_const) hℓ
      fun _ hx => hx
  refine ⟨hsub, ?_, isAbsorbing_finite_of_driftV2 hVm hb hdrift, fun n => {x | regV P C x ≤ n},
    fun n => hsub n (ENNReal.natCast_ne_top n), ?_⟩
  · rcases lemma_11_3_6 hψ.2.1 hVm hb hdrift with h | h
    · exact h
    · obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hψC.ne'
      exact absurd (h x) (by rw [regV_of_mem P hC.1 hx]; exact ENNReal.one_ne_top)
  · ext x
    simp only [mem_iUnion, mem_ofPred_eq]
    refine ⟨fun ⟨n, hn⟩ => ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) hn, fun hx => ?_⟩
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    exact ⟨n, hn.le⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.3.14** (MT p. 271), corrected: for a `ψ`-irreducible chain, a set `C` is petite,
non-empty and has `sup_{x ∈ C} E_x[τ_C] < ∞` iff `C` is regular and `C ∈ B⁺(X)`. -/
theorem theorem_11_3_14 [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {C : Set X} :
    (IsPetite P C ∧ C.Nonempty ∧ ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, meanReturnTime P C x ≤ M) ↔
      (IsRegularSet P ψ C ∧ 0 < ψ C) := by
  constructor
  · rintro ⟨hpet, hne, M, hM, hbound⟩
    have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hpet; exact h.1
    have hL : ∀ y ∈ C, hitProb P C y = 1 := fun y hy =>
      hitProb_eq_one_of_meanReturnTime_ne_top hCm (ne_top_of_le_ne_top hM (hbound y hy))
    refine ⟨theorem_11_3_11_i_regular hψ (measurable_regV P hCm) hM hpet
      (regV_drift P hCm hbound) hCm ENNReal.one_ne_top fun x hx => ?_,
      (theorem_8_3_6_i P hψ hpet hne hL).2⟩
    rw [regV_of_mem P hCm hx]
  · rintro ⟨hC, hψC⟩
    exact ⟨proposition_11_3_8 hψ hC, nonempty_of_measure_ne_zero hψC.ne', hC.2 C hC.1 hψC⟩

/-- **The counterexample to Theorem 11.3.14 as stated** (`C = ∅`): `∅` is petite and
`sup_{x ∈ ∅} E_x[τ_∅] = 0 < ∞`, but `∅ ∉ B⁺(X)`. -/
theorem theorem_11_3_14_counterexample [IsMarkovKernel P] (ψ : Measure X) (x : X) :
    IsPetite P ∅ ∧ (∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ y ∈ (∅ : Set X), meanReturnTime P ∅ y ≤ M) ∧
      ¬ 0 < ψ ∅ :=
  ⟨⟨diracDist 0, Measure.dirac x, MeasurableSet.empty, isSamplingDist_diracDist 0,
    Measure.dirac_ne_zero, fun y hy => absurd hy (notMem_empty y)⟩,
    ⟨0, ENNReal.zero_ne_top, fun y hy => absurd hy (notMem_empty y)⟩, by simp⟩

/-- A countable cover of `X` by measurable sets has a member in `B⁺(X)`. -/
theorem exists_pos_of_iUnion_eq_univ {ψ : Measure X} (hψ : ψ ≠ 0) {C : ℕ → Set X}
    (hcov : ⋃ n, C n = univ) : ∃ n, 0 < ψ (C n) := by
  by_contra h
  push Not at h
  apply hψ
  rw [← Measure.measure_univ_eq_zero, ← hcov]
  exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (h n)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.3.15** (MT p. 271): for a `ψ`-irreducible chain the following are equivalent:
(i) the chain is regular; (ii) (V2) holds for a petite set `C` and an everywhere finite `V`;
(iii) some petite set `C` has `E_x[τ_C] < ∞` for every `x`, uniformly bounded on `C`. -/
theorem theorem_11_3_15 [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) :
    (IsRegularChain P ψ ↔ ∃ (C : Set X) (V : X → ℝ≥0∞) (b : ℝ≥0∞), IsPetite P C ∧
      Measurable V ∧ b ≠ ∞ ∧ (∀ x, V x ≠ ∞) ∧ DriftV2 P V b C) ∧
    (IsRegularChain P ψ ↔ ∃ C : Set X, IsPetite P C ∧ (∀ x, meanReturnTime P C x ≠ ∞) ∧
      ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, meanReturnTime P C x ≤ M) := by
  -- (ii) ⇒ (i)
  have h21 : (∃ (C : Set X) (V : X → ℝ≥0∞) (b : ℝ≥0∞), IsPetite P C ∧ Measurable V ∧ b ≠ ∞ ∧
      (∀ x, V x ≠ ∞) ∧ DriftV2 P V b C) → IsRegularChain P ψ := by
    rintro ⟨C, V, b, hC, hV, hb, hfin, h⟩
    refine ⟨fun n => {x | V x ≤ n}, fun n => theorem_11_3_11_i_regular hψ hV hb hC h
      (measurableSet_le hV measurable_const) (ENNReal.natCast_ne_top n) fun _ hx => hx, ?_⟩
    ext x
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hfin x)
    exact ⟨n, hn.le⟩
  -- (i) gives a regular set in `B⁺(X)` and bounds on the cover
  have h1 : IsRegularChain P ψ → ∃ R : Set X, IsRegularSet P ψ R ∧ 0 < ψ R ∧
      ∀ x, meanReturnTime P R x ≠ ∞ := by
    rintro ⟨Cs, hCs, hcov⟩
    obtain ⟨n, hn⟩ := exists_pos_of_iUnion_eq_univ hψ.1 hcov
    refine ⟨Cs n, hCs n, hn, fun x => ?_⟩
    obtain ⟨m, hm⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ n, Cs n)
    obtain ⟨M, hM, hbound⟩ := (hCs m).2 (Cs n) (hCs n).1 hn
    exact ne_top_of_le_ne_top hM (hbound x hm)
  refine ⟨⟨fun hreg => ?_, h21⟩, ⟨fun hreg => ?_, fun ⟨C, hC, hfin, M, hM, hbound⟩ => ?_⟩⟩
  · obtain ⟨R, hR, hψR, hfin⟩ := h1 hreg
    obtain ⟨hpet, b, hb, hdrift, -⟩ := theorem_11_3_11_ii hψ hR hψR
    exact ⟨R, regV P R, b, hpet, measurable_regV P hR.1, hb, fun x =>
      ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hfin x⟩)
        (regV_le P hR.1 x), hdrift⟩
  · obtain ⟨R, hR, hψR, hfin⟩ := h1 hreg
    exact ⟨R, proposition_11_3_8 hψ hR, hfin, hR.2 R hR.1 hψR⟩
  · have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
    exact h21 ⟨C, regV P C, M, hC, measurable_regV P hCm, hM, fun x =>
      ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hfin x⟩)
        (regV_le P hCm x), regV_drift P hCm hbound⟩

end MeynTweedie.Epilogue
