/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.SumsNoAtom

/-!
# The Aperiodic Ergodic Theorem in full (MT Theorem 13.0.1)

Meyn and Tweedie, Theorem 13.0.1, pp. 313–314. The state space is countably generated.
`AperiodicErgodic` proves the equivalence of (i), (ii) and (13.4); this module adds the
conditions (iii) and (iv), which come from Chapter 11 (Theorem 11.0.1), and the summability
(13.5), which is Theorem 13.4.4 (`SumsNoAtom`).

**Results.**
* **Theorem 13.0.1** (`theorem_13_0_1_full`, p. 313): for an aperiodic Harris chain the following
  are equivalent:
  (i) the chain is positive;
  (ii) there are a small set `C ∈ B⁺(X)` and `P^∞(C) > 0` with `Pⁿ(x, C) → P^∞(C)` for `x ∈ C`;
  (13.4) there is an invariant probability `π` with `sup_A |Pⁿ(x, A) − π(A)| → 0` for every `x`;
  (iii) there is a regular set in `B⁺(X)`;
  (iii′) there is a non-empty petite set `C` with `sup_{x ∈ C} E_x[τ_C] < ∞` (13.2);
  (iv) there are a petite set `C`, `b < ∞` and `V ≥ 0` finite at some `x₀` with
  `PV ≤ V − 1 + b 1_C` (13.3).
* `theorem_13_0_1_finite` (p. 313, (i)): for a Harris chain with a nonzero invariant measure
  `π`, `π(X) < ∞` iff the chain is positive (Theorem 11.0.1).
* `theorem_13_0_1_sum` ((13.5), p. 314): under these conditions, for regular initial
  distributions `λ`, `μ`, `∫ λ(dx) ∫ μ(dy) Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞`.

**Corrections.** In (iii) the petite set must be non-empty: `∅` is petite with
`sup_{x ∈ ∅} E_x[τ_∅] = 0`, for every chain (`theorem_11_3_14_counterexample`), so (13.2) for
`C = ∅` does not imply positivity; this is the correction of Theorems 11.0.1 and 11.3.14.

**Hypotheses.** Condition (iv) is the drift condition (V2) of Chapter 11, `PV + 1 ≤ V + b 1_C`
for a measurable `V : X → [0, ∞]` (`driftV2_iff_drift` shows it is `ΔV ≤ −1 + b 1_C`). The
summability (13.5) needs only positivity and aperiodicity, not the Harris property.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Positivity and regular sets** (Theorems 11.1.4 and 11.3.14): for a `ψ`-irreducible chain,
positivity, a regular set in `B⁺(X)`, (13.2) for a non-empty petite set, and (V2) for a petite set
with `V` finite somewhere are equivalent. -/
theorem isPositive_tfae_regular {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    List.TFAE [IsPositive P ψ,
      ∃ R, IsRegularSet P ψ R ∧ 0 < ψ R,
      ∃ C, IsPetite P C ∧ C.Nonempty ∧ ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, meanReturnTime P C x ≤ M,
      ∃ (C : Set X) (V : X → ℝ≥0∞) (b : ℝ≥0∞), IsPetite P C ∧ Measurable V ∧ b ≠ ∞ ∧
        (∃ x, V x ≠ ∞) ∧ DriftV2 P V b C] := by
  tfae_have 1 → 2 := fun hpos => exists_regularSet_of_isPositive hpos
  tfae_have 2 → 1 := fun ⟨R, hR, hψR⟩ => isPositive_of_isRegularSet hψ hR hψR
  tfae_have 2 ↔ 3 := by
    constructor
    · rintro ⟨R, hR, hψR⟩
      exact ⟨R, (theorem_11_3_14 hψ).2 ⟨hR, hψR⟩⟩
    · rintro ⟨C, hC⟩
      exact ⟨C, (theorem_11_3_14 hψ).1 hC⟩
  tfae_have 2 → 4 := by
    rintro ⟨R, hR, hψR⟩
    obtain ⟨hpet, b, hb, hdrift, -⟩ := theorem_11_3_11_ii hψ hR hψR
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hψR.ne'
    refine ⟨R, regV P R, b, hpet, measurable_regV P hR.1, hb, ⟨x, ?_⟩, hdrift⟩
    rw [regV_of_mem P hR.1 hx]
    exact ENNReal.one_ne_top
  tfae_have 4 → 2 := by
    rintro ⟨C, V, b, hC, hV, hb, hx, h⟩
    obtain ⟨hfull, -, hon, -⟩ := theorem_11_0_1_sublevel hψ hV hb hC h hx
    exact hon.exists_pos hψ.1 hfull
  tfae_finish

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.0.1** (the Aperiodic Ergodic Theorem, MT p. 313), all conditions: for an
aperiodic Harris chain the following are equivalent:
(i) the chain is positive;
(ii) there are a small set `C ∈ B⁺(X)` and `P^∞(C) > 0` with `Pⁿ(x, C) → P^∞(C)` for `x ∈ C`;
(13.4) there is an invariant probability `π` with `sup_A |Pⁿ(x, A) − π(A)| → 0` for every `x`;
(iii) there is a regular set in `B⁺(X)`;
(iii′) some non-empty petite set `C` has `sup_{x ∈ C} E_x[τ_C] < ∞` (13.2);
(iv) (V2) holds for a petite set `C` and a `V` finite at some state (13.3). -/
theorem theorem_13_0_1_full {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) (hap : IsAperiodic P ψ) :
    List.TFAE [IsPositive P ψ,
      ∃ (C : Set X) (m : ℕ) (ν : Measure X) (c : ℝ), IsSmallSet P m ν C ∧ 0 < ψ C ∧ 0 < c ∧
        ∀ x ∈ C, Tendsto (fun n => ((P ^ n : Kernel X X) x C).toReal) atTop (𝓝 c),
      ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π ∧
        ∀ x, Tendsto (fun n => tvSup ((P ^ n : Kernel X X) x) π) atTop (𝓝 0),
      ∃ R, IsRegularSet P ψ R ∧ 0 < ψ R,
      ∃ C, IsPetite P C ∧ C.Nonempty ∧ ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, meanReturnTime P C x ≤ M,
      ∃ (C : Set X) (V : X → ℝ≥0∞) (b : ℝ≥0∞), IsPetite P C ∧ Measurable V ∧ b ≠ ∞ ∧
        (∃ x, V x ≠ ∞) ∧ DriftV2 P V b C] := by
  have h1 := theorem_13_0_1 hH hap
  have h2 := isPositive_tfae_regular hH.1
  tfae_have 1 ↔ 2 := h1.out 1 2
  tfae_have 1 ↔ 3 := h1.out 1 3
  tfae_have 1 ↔ 4 := h2.out 1 2
  tfae_have 1 ↔ 5 := h2.out 1 3
  tfae_have 1 ↔ 6 := h2.out 1 4
  tfae_finish

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.0.1 (i)** (MT p. 313): for a Harris chain with a nonzero invariant measure `π`,
`π(X) < ∞` iff the chain is positive (Theorem 11.0.1; aperiodicity is not needed). -/
theorem theorem_13_0_1_finite {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0) :
    π univ ≠ ∞ ↔ IsPositive P ψ :=
  (theorem_11_0_1 hH hπ hπ0).1.trans ((isPositive_tfae_regular hH.1).out 1 3).symm

variable [MeasurableSpace.CountablyGenerated X] in
/-- **(13.5)** (MT p. 314): under the conditions of Theorem 13.0.1, for regular initial
distributions `λ`, `μ`, `∫ λ(dx) ∫ μ(dy) Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞` (Theorem 13.4.4). -/
theorem theorem_13_0_1_sum {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsRegularMeasure P ψ μ) (hν : IsRegularMeasure P ψ ν) :
    ∫⁻ x, ∫⁻ y, ∑' n, ENNReal.ofReal (tvNorm ((P ^ (n + 1) : Kernel X X) x)
      ((P ^ (n + 1) : Kernel X X) y)) ∂ν ∂μ ≠ ∞ :=
  theorem_13_4_4 hpos hap μ ν hμ hν

end MeynTweedie.VUniformErgodicity
