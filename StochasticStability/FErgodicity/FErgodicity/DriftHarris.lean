/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.TopologicalRecurrence
import FErgodicity.SupermartingaleDrift
import FErgodicity.RandomWalkHalfLine

/-!
# Criteria for stability on a topological space (MT §9.4)

Meyn and Tweedie, §9.4, pp. 213–218.

* `IsCoercive V` (p. 213): the sublevel sets `{V ≤ r}` are precompact.
* `pathKernel_shift_preimage`: `P_x(θⁿ ∈ E) = ∫ Pⁿ(x, dy) P_y(E)`.
* **Theorem 9.4.1** (`theorem_9_4_1`, p. 214): (V1) for a coercive `V` off a compact `C` makes
  the chain non-evanescent. The proof is the book's: the killed process
  `V(Φₖ) 1{σ_C ≥ k}` is a nonnegative supermartingale (`SupermartingaleDrift`), so `V(Φₖ)` stays
  bounded on `{σ_C = ∞}`, which is incompatible with `Φ → ∞`.
* `isHarris_of_coercive` (p. 214): for a `ψ`-irreducible T-chain, (V1) for a coercive `V` off a
  compact set gives Harris recurrence (Theorems 9.4.1 and 9.2.2), and `C` is Harris recurrent if
  `ψ(C) > 0`.
* `example_9_4_1` (p. 214): the chain on `ℝ` with `P(0, {1}) = 1` and `P(x, {x}) = 1` for
  `x ≠ 0` satisfies (V1) with `V(x) = |x|` and `C = {0}`, is non-evanescent, and never enters
  `C` (`L(x, C) = 0` for every `x`), so `C` is not Harris recurrent.
* **Theorem 9.4.2** (`theorem_9_4_2`, p. 215): for a weak Feller chain and a compact `C` with
  `P_x(σ_C < ∞) = 1` for every `x`, there are a compact `C₀ ⊇ C` and a coercive `V`, bounded on
  compacta, with `ΔV ≤ 0` off `C₀`. The proof is the book's, `V = Σᵢ V_{nᵢ}` with
  `Vₙ(x) = P_x(σ_{Dₙ} < σ_{A₀})`; the uniform convergence on compacta is a Dini argument for
  lower semicontinuous functions (`exists_index_lt_of_lsc`).
* **Lemma 9.4.3** (`lemma_9_4_3`, p. 216): `E[log(−s + tW); B] ≤ P(B)(log s − 2) + (t/s) E[W; B]`
  for `B ⊆ {−s + tW > 0}`.
* **Lemma 9.4.4** (`lemma_9_4_4_i`, `lemma_9_4_4_ii`, p. 217): the `lim sup` bounds (9.40) and
  (9.41), from `x² Γ(−∞, t + sx) → 0` (`tendsto_sq_mul_lowerTail`).
* **Proposition 9.4.5** (`proposition_9_4_5`, p. 217): random walk on `ℝ` with mean zero and
  finite variance is non-evanescent, with `V(x) = log(1 + |x|)` (`isCoercive_log_one_add_abs`);
  the drift estimate is `randomWalk_log_drift` / `randomWalk_log_drift_abs`.

**Hypotheses.** Theorems 9.4.1 and 9.4.2 assume, as the book does, a locally compact separable
metric-type space: here locally compact, second countable and Hausdorff with the Borel σ-algebra.
Lemma 9.4.3 assumes `log(−s + tW)` and `W` integrable on `B` (otherwise the left side is not
defined).

**Corrections.**
* Proposition 9.4.5 is stated for the walk "on `ℝ₊`"; it is the unrestricted walk on `ℝ`.
* Lemma 9.4.4 asserts `lim … ≤ 0`; the limit need not exist, and the statement proved is the
  `lim sup` form (every `ε > 0` eventually bounds the expression), which is what the book's proof
  shows (its proof of (i) writes `x → ∞` for `x → −∞`).
* The proof of Proposition 9.4.5 here does not go through Lemma 9.4.4: it bounds
  `log(1 + |x + w|)` pointwise by `log a + w/a − (w²/2a²)1{−x < w < 0} + (w²/2x²)1{w ≤ −x}`
  (`a = 1 + x`) and integrates, using only `E[W²; W ≤ −x] → 0`; no cut-off `R` in the test
  function is needed.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

/-- `P_x(θⁿΦ ∈ E) = ∫ Pⁿ(x, dy) P_y(E)` (the Markov property at time `n`). -/
theorem pathKernel_shift_preimage (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ)
    {E : Set (ℕ → X)} (hE : MeasurableSet E) :
    pathKernel P x (shift n ⁻¹' E) = ∫⁻ y, pathKernel P y E ∂(P ^ n) x := by
  have hi : Measurable (E.indicator (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hE
  have h := markov_lintegral_univ P (Measure.dirac x) n hi
  rw [pathMeasure_dirac] at h
  simp_rw [lintegral_indicator_one hE] at h
  have hpre : MeasurableSet (shift n ⁻¹' E) := measurable_shift n hE
  have e1 : ∫⁻ ω, E.indicator 1 (shift n ω) ∂pathKernel P x = pathKernel P x (shift n ⁻¹' E) := by
    change ∫⁻ ω, (shift n ⁻¹' E).indicator 1 ω ∂pathKernel P x = _
    rw [lintegral_indicator_one hpre]
  rw [← e1, h, ← lintegral_map (Kernel.measurable_coe _ hE) (measurable_pi_apply n),
    pathKernel_map_coord]

/-! ### Coercive functions and Theorem 9.4.1 -/

variable [TopologicalSpace X] in
/-- `V` is **coercive** (MT p. 213): `V(x) → ∞` as `x → ∞`, i.e. every sublevel set
`{x : V(x) ≤ r}` is precompact. -/
def IsCoercive (V : X → ℝ≥0) : Prop := ∀ r : ℝ≥0, IsCompact (closure {x | V x ≤ r})

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X] [WeaklyLocallyCompactSpace X]
  [SigmaCompactSpace X] in
/-- **Theorem 9.4.1** (MT p. 214): if (V1) holds, `ΔV ≤ 0` off a compact set `C`, for a coercive
measurable `V`, then the chain is non-evanescent. No irreducibility is needed. -/
theorem theorem_9_4_1 {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0} (hVm : Measurable V)
    (hV : IsCoercive V) {C : Set X} (hC : IsCompact C)
    (hdrift : ∀ x ∉ C, drift P (fun y => (V y : ℝ≥0∞)) x ≤ 0) : IsNonEvanescent P := by
  have := isMarkovKernel_pathKernel P
  have hCm := hC.measurableSet
  have hdr : ∀ x ∉ C, ∫⁻ y, (V y : ℝ≥0∞) ∂P x ≤ V x := fun x hx =>
    (drift_nonpos_iff P _ x).1 (hdrift x hx)
  set Av := {ω : ℕ → X | ∀ i, ω i ∉ C}
  have hAv : MeasurableSet Av := by
    have : Av = ⋂ i, {ω : ℕ → X | ω i ∈ Cᶜ} := by ext ω; simp [Av]
    rw [this]; exact MeasurableSet.iInter fun i => measurable_pi_apply i hCm.compl
  have hTm : MeasurableSet (tendsToInfty (X := X)) := measurableSet_tendsToInfty
  -- from every `y`, `{σ_C = ∞} ∩ {Φ → ∞}` is null
  have step1 : ∀ y, pathKernel P y (Av ∩ tendsToInfty) = 0 := by
    intro y
    have hfin : ∫⁻ x, (V x : ℝ≥0∞) ∂Measure.dirac y ≠ ∞ := by
      have hVe : Measurable fun x => (V x : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hVm
      rw [lintegral_dirac' y hVe]; exact ENNReal.coe_ne_top
    have h := ae_bddAbove_of_avoid P (Measure.dirac y) hVm hCm hdr hfin
    rw [pathMeasure_dirac] at h
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with ω hω hmem
    obtain ⟨hav, hT⟩ := hmem
    obtain ⟨r, hr⟩ := hω hav
    refine hT _ (hV r.toNNReal) fun N => ⟨N, le_rfl, subset_closure ?_⟩
    change V (ω N) ≤ r.toNNReal
    rw [← Real.toNNReal_coe (r := V (ω N))]
    exact Real.toNNReal_le_toNNReal (hr N)
  -- `{Φ → ∞}` is covered by the shifts of `{σ_C = ∞} ∩ {Φ → ∞}`
  intro x
  have hcov : tendsToInfty (X := X) ⊆ ⋃ M, shift M ⁻¹' (Av ∩ tendsToInfty) := by
    intro ω hω
    have hnio : ω ∉ ioSet C := hω C hC
    simp only [ioSet, mem_ofPred_eq, not_forall, not_exists, not_and] at hnio
    obtain ⟨M, hM⟩ := hnio
    refine mem_iUnion.2 ⟨M, ?_, (isShiftInvariant_tendsToInfty M ω).2 hω⟩
    intro i
    simp only [shift_apply]
    exact hM (M + i) (by omega)
  refine measure_mono_null hcov (measure_iUnion_null fun M => ?_)
  rw [pathKernel_shift_preimage P x M (hAv.inter hTm)]
  simp [step1]

variable [TopologicalSpace X] [T2Space X] [BorelSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
/-- Harris recurrence from a coercive drift (MT p. 214): for a `ψ`-irreducible T-chain, (V1) for
a coercive `V` off a compact set `C` makes the chain Harris recurrent, and `C` itself Harris
recurrent when `ψ(C) > 0`. -/
theorem isHarris_of_coercive {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hT : IsTChain P) {V : X → ℝ≥0} (hVm : Measurable V)
    (hV : IsCoercive V) {C : Set X} (hC : IsCompact C)
    (hdrift : ∀ x ∉ C, drift P (fun y => (V y : ℝ≥0∞)) x ≤ 0) :
    IsHarris P ψ ∧ (0 < ψ C → IsHarrisRecurrentSet P C) := by
  have hH := (theorem_9_2_2_ii hψ hT).2 (theorem_9_4_1 hVm hV hC hdrift)
  exact ⟨hH, fun hψC => hH.2 C hC.measurableSet hψC⟩

/-! ### The example on p. 214 -/

/-- `Pⁿ(x, ·) = δ_{fⁿ(x)}` for the deterministic kernel of `f`. -/
theorem deterministic_pow_apply {f : X → X} (hf : Measurable f) (n : ℕ) (x : X) :
    (Kernel.deterministic f hf ^ n) x = Measure.dirac (f^[n] x) := by
  induction n generalizing x with
  | zero => rw [pow_zero_apply]; rfl
  | succ n ih =>
    ext A hA
    rw [pow_succ_apply _ n x hA, Kernel.deterministic_apply,
      lintegral_dirac' _ (Kernel.measurable_coe _ hA), ih, Function.iterate_succ_apply]

/-- Under the deterministic kernel of `f`, the path is the orbit: `Φₙ = fⁿ(x)`, `P_x`-a.s. -/
theorem ae_orbit_deterministic [MeasurableSingletonClass X] {f : X → X} (hf : Measurable f)
    (x : X) : ∀ᵐ ω ∂pathKernel (Kernel.deterministic f hf) x, ∀ n, ω n = f^[n] x := by
  have := isMarkovKernel_pathKernel (Kernel.deterministic f hf)
  refine ae_all_iff.2 fun n => ?_
  have h : pathKernel (Kernel.deterministic f hf) x {ω | ω n ∈ ({f^[n] x} : Set X)ᶜ} = 0 := by
    rw [pathKernel_coord_mem _ x n (measurableSet_singleton _).compl, deterministic_pow_apply,
      Measure.dirac_apply' _ (measurableSet_singleton _).compl]
    simp
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h
  simpa using hω

/-- The map of the example: `f(0) = 1` and `f(x) = x` for `x ≠ 0`. -/
noncomputable def exampleMap941 (x : ℝ) : ℝ := if x = 0 then 1 else x

/-- `f` is measurable. -/
theorem measurable_exampleMap941 : Measurable exampleMap941 :=
  Measurable.ite (measurableSet_singleton 0) measurable_const measurable_id

/-- `f(x) ≠ 0`. -/
theorem exampleMap941_ne_zero (x : ℝ) : exampleMap941 x ≠ 0 := by
  unfold exampleMap941; split_ifs with h
  · exact one_ne_zero
  · exact h

/-- `f(y) = y` for `y ≠ 0`. -/
theorem exampleMap941_of_ne {y : ℝ} (hy : y ≠ 0) : exampleMap941 y = y := by
  simp [exampleMap941, hy]

/-- `fⁿ⁺¹(x) = f(x)`. -/
theorem exampleMap941_iterate_succ (n : ℕ) (x : ℝ) : exampleMap941^[n + 1] x = exampleMap941 x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, exampleMap941_of_ne (exampleMap941_ne_zero x)]

/-- **The example on p. 214**: on `ℝ`, the chain with `P(0, {1}) = 1` and `P(x, {x}) = 1` for
`x ≠ 0` satisfies (V1) with the coercive `V(x) = |x|` and the compact `C = {0}`, is
non-evanescent, and never enters `C`: `L(x, C) = 0` for every `x` (so `C` is not Harris
recurrent, nor reached from any initial condition). -/
theorem example_9_4_1 :
    haveI : IsMarkovKernel (Kernel.deterministic exampleMap941 measurable_exampleMap941) :=
      inferInstance
    (∀ x ∉ ({0} : Set ℝ), drift (Kernel.deterministic exampleMap941 measurable_exampleMap941)
        (fun y => ((‖y‖₊ : ℝ≥0) : ℝ≥0∞)) x ≤ 0) ∧
      IsCoercive (fun y : ℝ => ‖y‖₊) ∧
      IsNonEvanescent (Kernel.deterministic exampleMap941 measurable_exampleMap941) ∧
      ∀ x, hitProb (Kernel.deterministic exampleMap941 measurable_exampleMap941) {0} x = 0 := by
  set P := Kernel.deterministic exampleMap941 measurable_exampleMap941
  have := isMarkovKernel_pathKernel P
  refine ⟨fun x hx => ?_, fun r => ?_, fun x => ?_, fun x => ?_⟩
  · rw [drift_nonpos_iff, Kernel.deterministic_apply, lintegral_dirac]
    simp only [mem_singleton_iff] at hx
    simp [exampleMap941, hx]
  · refine (isCompact_closedBall (0 : ℝ) r).of_isClosed_subset isClosed_closure ?_
    refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
    simp only [mem_ofPred_eq] at hy
    rw [Metric.mem_closedBall, dist_zero_right]
    exact_mod_cast hy
  · rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_orbit_deterministic measurable_exampleMap941 x] with ω hω hT
    refine hT {exampleMap941 x} isCompact_singleton fun N => ⟨N + 1, by omega, ?_⟩
    rw [hω, exampleMap941_iterate_succ]
    rfl
  · rw [hitProb, measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_orbit_deterministic measurable_exampleMap941 x] with ω hω hmem
    simp only [firstReturn_ne_top_iff] at hmem
    obtain ⟨n, hn, hn0⟩ := hmem
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hω, exampleMap941_iterate_succ, mem_singleton_iff] at hn0
    exact exampleMap941_ne_zero x hn0

/-! ### Lemma 9.4.3 -/

/-- **Lemma 9.4.3** (MT p. 216): for `s > 0`, `t ∈ ℝ` and `B ⊆ {w : −s + tw > 0}`,
`E[log(−s + tW); B] ≤ P(B)(log s − 2) + (t/s) E[W; B]` (with `W` and `log(−s + tW)` integrable on
`B`). The proof is `log(−1 + u) ≤ u − 2` for `u > 1`. -/
theorem lemma_9_4_3 (Γ : Measure ℝ) [IsFiniteMeasure Γ] {s t : ℝ} (hs : 0 < s) {B : Set ℝ}
    (hBm : MeasurableSet B) (hB : B ⊆ {w | 0 < -s + t * w})
    (hlog : IntegrableOn (fun w => Real.log (-s + t * w)) B Γ)
    (hW : IntegrableOn (fun w => w) B Γ) :
    ∫ w in B, Real.log (-s + t * w) ∂Γ ≤
      (Γ B).toReal * (Real.log s - 2) + (t / s) * ∫ w in B, w ∂Γ := by
  have hpt : ∀ w ∈ B, Real.log (-s + t * w) ≤ (Real.log s - 2) + (t / s) * w := by
    intro w hw
    have hpos : 0 < -s + t * w := hB hw
    have hu : 0 < -1 + t * w / s := by
      have : -1 + t * w / s = (-s + t * w) / s := by field_simp
      rw [this]; exact div_pos hpos hs
    have hsplit : -s + t * w = s * (-1 + t * w / s) := by field_simp
    rw [hsplit, Real.log_mul hs.ne' hu.ne']
    have := Real.log_le_sub_one_of_pos hu
    have e : t / s * w = t * w / s := by ring
    rw [e]
    linarith
  have hconst : IntegrableOn (fun _ : ℝ => Real.log s - 2) B Γ := integrableOn_const
  calc ∫ w in B, Real.log (-s + t * w) ∂Γ
      ≤ ∫ w in B, ((Real.log s - 2) + (t / s) * w) ∂Γ :=
        setIntegral_mono_on hlog (hconst.add (hW.const_mul (t / s))) hBm hpt
    _ = (Γ B).toReal * (Real.log s - 2) + (t / s) * ∫ w in B, w ∂Γ := by
        rw [integral_add hconst (hW.const_mul (t / s)), setIntegral_const, integral_const_mul]
        simp [smul_eq_mul, Measure.real]

/-! ### Theorem 9.4.2 -/

/-- The event `{σ_D < σ_A}`: the path is in `D` at some time `n` and avoids `A` up to time `n`. -/
def beforeEvent (D A : Set X) : Set (ℕ → X) := {ω | ∃ n, ω n ∈ D ∧ ∀ k ≤ n, ω k ∉ A}

/-- `{σ_D < σ_A}` is an event. -/
theorem measurableSet_beforeEvent {D A : Set X} (hD : MeasurableSet D) (hA : MeasurableSet A) :
    MeasurableSet (beforeEvent D A) := by
  have : beforeEvent D A = ⋃ n, ({ω : ℕ → X | ω n ∈ D} ∩
      ⋂ k ∈ Finset.range (n + 1), {ω : ℕ → X | ω k ∈ Aᶜ}) := by
    ext ω
    simp only [beforeEvent, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter,
      Finset.mem_range, mem_compl_iff, Nat.lt_succ_iff]
  rw [this]
  exact MeasurableSet.iUnion fun n => (measurable_pi_apply n hD).inter
    (Finset.measurableSet_biInter _ fun k _ => measurable_pi_apply k hA.compl)

omit [MeasurableSpace X] in
/-- If `Φ₀ ∉ D ∪ A`, then `σ_D < σ_A` for the path iff it holds for the shifted path. -/
theorem shift_one_mem_beforeEvent {D A : Set X} {ω : ℕ → X} (h0D : ω 0 ∉ D) (h0A : ω 0 ∉ A) :
    shift 1 ω ∈ beforeEvent D A ↔ ω ∈ beforeEvent D A := by
  constructor
  · rintro ⟨n, hn, hk⟩
    refine ⟨n + 1, by simpa [shift_apply, add_comm] using hn, fun k hk' => ?_⟩
    rcases k with _ | k
    · exact h0A
    · have := hk k (by omega)
      simpa [shift_apply, add_comm] using this
  · rintro ⟨n, hn, hk⟩
    rcases n with _ | n
    · exact absurd hn h0D
    · refine ⟨n, by simpa [shift_apply, add_comm] using hn, fun k hk' => ?_⟩
      have := hk (k + 1) (by omega)
      simpa [shift_apply, add_comm] using this

omit [MeasurableSpace X] in
/-- A path starting in `D ∩ Aᶜ` has `σ_D = 0 < σ_A`. -/
theorem subset_beforeEvent_zero (D A : Set X) :
    {ω : ℕ → X | ω 0 ∈ D ∩ Aᶜ} ⊆ beforeEvent D A := fun ω hω =>
  ⟨0, hω.1, fun k hk => by rw [Nat.le_zero.1 hk]; exact hω.2⟩

/-- `1 − ε < g` implies `1 − g ≤ ε`. -/
theorem one_sub_le_of_one_sub_lt {g ε : ℝ≥0∞} (h : 1 - ε < g) : 1 - g ≤ ε := by
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) ≤ (1 - ε) + ε := le_tsub_add
    _ ≤ g + ε := by gcongr
    _ = ε + g := add_comm _ _

/-- **The first-step equation (9.33)**: for `x ∉ D ∪ A`,
`P_x(σ_D < σ_A) = ∫ P(x, dy) P_y(σ_D < σ_A)`. -/
theorem beforeEvent_first_step (P : Kernel X X) [IsMarkovKernel P] {D A : Set X}
    (hD : MeasurableSet D) (hA : MeasurableSet A) {x : X} (hxD : x ∉ D) (hxA : x ∉ A) :
    pathKernel P x (beforeEvent D A) = ∫⁻ y, pathKernel P y (beforeEvent D A) ∂P x := by
  have := isMarkovKernel_pathKernel P
  have hE := measurableSet_beforeEvent hD hA
  have hG : MeasurableSet {ω : ℕ → X | ω 0 ∈ (D ∪ A)ᶜ} :=
    measurable_pi_apply 0 (hD.union hA).compl
  have hGc : pathKernel P x {ω : ℕ → X | ω 0 ∈ (D ∪ A)ᶜ}ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff hG, pathKernel_zero_mem P x (hD.union hA).compl]
    simp [hxD, hxA]
  have hset : beforeEvent D A ∩ {ω : ℕ → X | ω 0 ∈ (D ∪ A)ᶜ} =
      shift 1 ⁻¹' beforeEvent D A ∩ {ω : ℕ → X | ω 0 ∈ (D ∪ A)ᶜ} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_compl_iff, mem_union, not_or]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(shift_one_mem_beforeEvent h2.1 h2.2).2 h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(shift_one_mem_beforeEvent h2.1 h2.2).1 h1, h2⟩
  rw [← measure_inter_conull hGc, hset, measure_inter_conull hGc,
    pathKernel_shift_preimage P x 1 hE, pow_one]

omit [MeasurableSpace X] in
variable [TopologicalSpace X] in
/-- **Dini's argument** for lower semicontinuous functions: if `gₙ` increases pointwise, each
`gₙ` is lower semicontinuous and `c < sup_n gₙ` everywhere, then on a compact set `c < g_N` for a
single `N`. -/
theorem exists_index_lt_of_lsc {g : ℕ → X → ℝ≥0∞} (hmono : ∀ x, Monotone fun n => g n x)
    (hlsc : ∀ n, LowerSemicontinuous (g n)) {c : ℝ≥0∞} (hsup : ∀ x, c < ⨆ n, g n x)
    {K : Set X} (hK : IsCompact K) : ∃ N, ∀ x ∈ K, c < g N x := by
  set U : ℕ → Set X := fun n => {x | c < g n x}
  have hUo : ∀ n, IsOpen (U n) := fun n => (hlsc n).isOpen_preimage c
  have hUm : Monotone U := fun m n hmn x hx => lt_of_lt_of_le hx (hmono x hmn)
  have hcov : K ⊆ ⋃ n, U n := fun x _ => mem_iUnion.2 (lt_iSup_iff.1 (hsup x))
  exact hK.elim_directed_cover U hUo hcov hUm.directed_le

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- For a weak Feller chain and open `A`, `x ↦ P_x(Φₖ ∈ A for some k ≤ m)` is lower
semicontinuous. -/
theorem lsc_exists_le {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P) {A : Set X}
    (hA : IsOpen A) (m : ℕ) :
    LowerSemicontinuous fun x => pathKernel P x {ω | ∃ k ≤ m, ω k ∈ A} := by
  have := isMarkovKernel_pathKernel P
  have hAm := hA.measurableSet
  have heq : (fun x => pathKernel P x {ω | ∃ k ≤ m, ω k ∈ A}) =
      fun x => max (A.indicator (fun _ => (1 : ℝ≥0∞)) x) (hitWithin P A m x) := by
    funext x
    have hsub : {ω : ℕ → X | firstReturn A ω ≤ WithTop.some m} ⊆ {ω | ∃ k ≤ m, ω k ∈ A} := by
      intro ω hω
      simp only [mem_ofPred_eq, firstReturn] at hω
      obtain ⟨j, hj, hjA⟩ := (hittingAfter_le_iff).1 hω
      exact ⟨j, hj.2, hjA⟩
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, max_eq_left (hitWithin_le_one P A m x)]
      refine le_antisymm prob_le_one ?_
      calc (1 : ℝ≥0∞) = pathKernel P x {ω | ω 0 ∈ A} := by
            rw [pathKernel_zero_mem P x hAm, indicator_of_mem hx]; rfl
        _ ≤ pathKernel P x {ω | ∃ k ≤ m, ω k ∈ A} :=
            measure_mono fun ω hω => ⟨0, Nat.zero_le m, hω⟩
    · rw [indicator_of_notMem hx, max_eq_right zero_le]
      refine le_antisymm ?_ (measure_mono hsub)
      have h0 : pathKernel P x {ω | ω 0 ∈ A} = 0 := by
        rw [pathKernel_zero_mem P x hAm, indicator_of_notMem hx]
      calc pathKernel P x {ω | ∃ k ≤ m, ω k ∈ A}
          ≤ pathKernel P x ({ω | ω 0 ∈ A} ∪ {ω | firstReturn A ω ≤ WithTop.some m}) := by
            refine measure_mono fun ω hω => ?_
            obtain ⟨k, hk, hkA⟩ := hω
            rcases k with _ | k
            · exact Or.inl hkA
            · refine Or.inr ?_
              simp only [mem_ofPred_eq, firstReturn]
              exact (hittingAfter_le_iff).2 ⟨k + 1, ⟨by omega, hk⟩, hkA⟩
        _ ≤ _ := measure_union_le _ _
        _ = hitWithin P A m x := by rw [h0, zero_add]; rfl
  rw [heq]
  exact (hA.lowerSemicontinuous_indicator zero_le).sup ((proposition_6_1_1_iii hP hA).1 m)

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- For a weak Feller chain and open `A`, `x ↦ P_x(Φₖ ∈ A for every k < m)` is lower
semicontinuous (`m ≥ 1`). -/
theorem lsc_forall_lt {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P) {A : Set X}
    (hA : IsOpen A) {m : ℕ} (hm : 1 ≤ m) :
    LowerSemicontinuous fun x => pathKernel P x {ω | ∀ k < m, ω k ∈ A} := by
  have := isMarkovKernel_pathKernel P
  have hAm := hA.measurableSet
  have heq : (fun x => pathKernel P x {ω | ∀ k < m, ω k ∈ A}) = A.indicator (tailProb P Aᶜ m) := by
    funext x
    have hG : MeasurableSet {ω : ℕ → X | ω 0 ∈ A} := measurable_pi_apply 0 hAm
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, tailProb]
      have hGc : pathKernel P x {ω : ℕ → X | ω 0 ∈ A}ᶜ = 0 := by
        rw [prob_compl_eq_zero_iff hG, pathKernel_zero_mem P x hAm, indicator_of_mem hx]; rfl
      rw [← measure_inter_conull hGc (s := {ω | ∀ k < m, ω k ∈ A}),
        ← measure_inter_conull hGc (s := {ω | WithTop.some m ≤ firstReturn Aᶜ ω})]
      congr 1
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, le_firstReturn_iff, mem_compl_iff, not_not]
      constructor
      · rintro ⟨h, h0⟩; exact ⟨fun j _ hj => h j hj, h0⟩
      · rintro ⟨h, h0⟩
        refine ⟨fun k hk => ?_, h0⟩
        rcases k with _ | k
        · exact h0
        · exact h (k + 1) (by omega) hk
    · rw [indicator_of_notMem hx]
      refine measure_mono_null (fun ω hω => ?_) (show pathKernel P x {ω | ω 0 ∈ A} = 0 by
        rw [pathKernel_zero_mem P x hAm, indicator_of_notMem hx])
      exact hω 0 (by omega)
  rw [heq]
  exact lowerSemicontinuous_indicator_of_isOpen hA
    (proposition_6_1_1_ii_tail hP hA.isClosed_compl m)

variable [TopologicalSpace X] [T2Space X] [BorelSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
/-- **Theorem 9.4.2** (MT p. 215): for a weak Feller chain and a compact set `C` with
`σ_C < ∞` almost surely from every starting point, there are a compact `C₀ ⊇ C` and a coercive
measurable `V`, bounded on compact sets, with `ΔV(x) ≤ 0` for `x ∉ C₀` (9.31). -/
theorem theorem_9_4_2 {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P) {C : Set X}
    (hC : IsCompact C) (hσ : ∀ x, hitProbZero P C x = 1) :
    ∃ (C₀ : Set X) (V : X → ℝ≥0), IsCompact C₀ ∧ C ⊆ C₀ ∧ Measurable V ∧ IsCoercive V ∧
      (∀ K : Set X, IsCompact K → ∃ M : ℝ≥0, ∀ x ∈ K, V x ≤ M) ∧
      ∀ x ∉ C₀, drift P (fun y => (V y : ℝ≥0∞)) x ≤ 0 := by
  have := isMarkovKernel_pathKernel P
  -- an increasing cover by open precompact sets `Aₙ` with `C ⊆ A₀`
  set Kx := CompactExhaustion.choice X
  obtain ⟨n₀, hn₀⟩ := Kx.exists_superset_of_isCompact hC
  set A : ℕ → Set X := fun n => interior (Kx (n + n₀ + 1))
  have hAo : ∀ n, IsOpen (A n) := fun n => isOpen_interior
  have hAm : ∀ n, MeasurableSet (A n) := fun n => (hAo n).measurableSet
  have hAmono : Monotone A := fun m n hmn => interior_mono (Kx.subset (by omega))
  have hAcl : ∀ n, IsCompact (closure (A n)) := fun n =>
    (Kx.isCompact _).of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset (Kx.isCompact _).isClosed)
  have hsucc : ∀ n, Kx n ⊆ A n := fun n =>
    (Kx.subset_interior_succ n).trans (interior_mono (Kx.subset (by omega)))
  have hCA : C ⊆ A 0 := hn₀.trans ((Kx.subset_interior_succ n₀).trans
    (interior_mono (Kx.subset (by omega))))
  have hAcov : ∀ L : Set X, IsCompact L → ∃ n, L ⊆ A n := fun L hL => by
    obtain ⟨n, hn⟩ := Kx.exists_superset_of_isCompact hL
    exact ⟨n, hn.trans (hsucc n)⟩
  have hApt : ∀ x, ∃ n, x ∈ A n := fun x => by
    obtain ⟨n, hn⟩ := hAcov {x} isCompact_singleton
    exact ⟨n, hn rfl⟩
  -- `Vₙ(x) = P_x(σ_{Aₙᶜ} < σ_{A₀})`
  set Vn : ℕ → X → ℝ≥0∞ := fun n x => pathKernel P x (beforeEvent (A n)ᶜ (A 0))
  have hEm : ∀ n, MeasurableSet (beforeEvent (A n)ᶜ (A 0)) := fun n =>
    measurableSet_beforeEvent (hAm n).compl (hAm 0)
  have hVnm : ∀ n, Measurable (Vn n) := fun n => Kernel.measurable_coe _ (hEm n)
  have hVn1 : ∀ n x, Vn n x ≤ 1 := fun n x => prob_le_one
  -- `Vₙ = 1` off `Aₙ ∪ A₀`
  have hVn_eq_one : ∀ n x, x ∉ A n → x ∉ A 0 → Vn n x = 1 := by
    intro n x hxn hx0
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = pathKernel P x {ω | ω 0 ∈ (A n)ᶜ ∩ (A 0)ᶜ} := by
          rw [pathKernel_zero_mem P x ((hAm n).compl.inter (hAm 0).compl),
            indicator_of_mem (show x ∈ (A n)ᶜ ∩ (A 0)ᶜ from ⟨hxn, hx0⟩)]; rfl
      _ ≤ pathKernel P x (beforeEvent (A n)ᶜ (A 0)) :=
          measure_mono (subset_beforeEvent_zero _ _)
  -- (9.34): `∫ P(x, dy) Vₙ(y) ≤ Vₙ(x)` off `A₀`
  have hVndrift : ∀ n, ∀ x ∉ A 0, ∫⁻ y, Vn n y ∂P x ≤ Vn n x := by
    intro n x hx
    by_cases hxn : x ∈ A n
    · exact le_of_eq (beforeEvent_first_step P (hAm n).compl (hAm 0) (not_not.2 hxn) hx).symm
    · rw [hVn_eq_one n x hxn hx]
      calc ∫⁻ y, Vn n y ∂P x ≤ ∫⁻ _, 1 ∂P x := lintegral_mono fun y => hVn1 n y
        _ = 1 := by simp
  -- (9.36): `Vₙ ≤ P_x(σ_{Aₙᶜ} < m) + P_x(σ_{A₀} > m)`
  have h936 : ∀ n m x, Vn n x ≤ (1 - pathKernel P x {ω | ∀ k < m, ω k ∈ A n}) +
      (1 - pathKernel P x {ω | ∃ k ≤ m, ω k ∈ A 0}) := by
    intro n m x
    have hm1 : MeasurableSet {ω : ℕ → X | ∀ k < m, ω k ∈ A n} := by
      have : {ω : ℕ → X | ∀ k < m, ω k ∈ A n} = ⋂ k ∈ Finset.range m, {ω | ω k ∈ A n} := by
        ext ω; simp
      rw [this]; exact Finset.measurableSet_biInter _ fun k _ => measurable_pi_apply k (hAm n)
    have hm2 : MeasurableSet {ω : ℕ → X | ∃ k ≤ m, ω k ∈ A 0} := by
      have : {ω : ℕ → X | ∃ k ≤ m, ω k ∈ A 0} = ⋃ k ∈ Finset.range (m + 1), {ω | ω k ∈ A 0} := by
        ext ω; simp
      rw [this]; exact Finset.measurableSet_biUnion _ fun k _ => measurable_pi_apply k (hAm 0)
    rw [← prob_compl_eq_one_sub hm1, ← prob_compl_eq_one_sub hm2]
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    obtain ⟨j, hj, hk⟩ := hω
    by_cases hjm : j < m
    · exact Or.inl fun h => hj (h j hjm)
    · exact Or.inr fun ⟨k, hk', hkA⟩ => hk k (by omega) hkA
  -- the probabilities in (9.36) increase to `1`
  have hg1sup : ∀ m x, (1 : ℝ≥0∞) ≤ ⨆ n, pathKernel P x {ω | ∀ k < m, ω k ∈ A n} := by
    intro m x
    have hmono : Monotone fun n => {ω : ℕ → X | ∀ k < m, ω k ∈ A n} :=
      fun a b hab ω hω k hk => hAmono hab (hω k hk)
    rw [← hmono.measure_iUnion]
    have hU : (⋃ n, {ω : ℕ → X | ∀ k < m, ω k ∈ A n}) = univ := by
      refine eq_univ_of_forall fun ω => mem_iUnion.2 ?_
      choose N hN using fun k => hApt (ω k)
      refine ⟨(Finset.range m).sup N, fun k hk => hAmono ?_ (hN k)⟩
      exact Finset.le_sup (Finset.mem_range.2 hk)
    rw [hU, measure_univ]
  have hg2sup : ∀ x, (1 : ℝ≥0∞) ≤ ⨆ m, pathKernel P x {ω | ∃ k ≤ m, ω k ∈ A 0} := by
    intro x
    have hmono : Monotone fun m => {ω : ℕ → X | ∃ k ≤ m, ω k ∈ A 0} :=
      fun a b hab ω ⟨k, hk, hkA⟩ => ⟨k, hk.trans hab, hkA⟩
    rw [← hmono.measure_iUnion, ← hσ x, hitProbZero_eq_exists]
    exact measure_mono fun ω ⟨k, hk⟩ => mem_iUnion.2 ⟨k, k, le_rfl, hCA hk⟩
  -- choose `mᵢ` and then `nᵢ` (Dini)
  set ε : ℕ → ℝ≥0∞ := fun i => 2⁻¹ ^ (i + 1)
  have hε0 : ∀ i, 0 < ε i := fun i => ENNReal.pow_pos (by simp) _
  have hε1 : ∀ i, ε i ≤ 1 := fun i => pow_le_one₀ zero_le (by norm_num)
  have hlt1 : ∀ i, 1 - ε i < 1 := fun i =>
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (hε0 i).ne'
  have hm : ∀ i, ∃ m, ∀ x ∈ closure (A i),
      1 - ε i < pathKernel P x {ω | ∃ k ≤ m, ω k ∈ A 0} := fun i =>
    exists_index_lt_of_lsc (g := fun m x => pathKernel P x {ω | ∃ k ≤ m, ω k ∈ A 0})
      (fun x a b hab => measure_mono fun ω ⟨k, hk, hkA⟩ => ⟨k, hk.trans hab, hkA⟩)
      (fun m => lsc_exists_le hP (hAo 0) m) (fun x => (hlt1 i).trans_le (hg2sup x)) (hAcl i)
  choose m hmspec using hm
  have hn : ∀ i, ∃ n, ∀ x ∈ closure (A i),
      1 - ε i < pathKernel P x {ω | ∀ k < m i + 1, ω k ∈ A n} := fun i =>
    exists_index_lt_of_lsc (g := fun n x => pathKernel P x {ω | ∀ k < m i + 1, ω k ∈ A n})
      (fun x a b hab => measure_mono fun ω hω k hk => hAmono hab (hω k hk))
      (fun n => lsc_forall_lt hP (hAo n) (by omega)) (fun x => (hlt1 i).trans_le (hg1sup _ x))
      (hAcl i)
  choose n hnspec using hn
  have hsmall : ∀ i, ∀ x ∈ A i, Vn (n i) x ≤ 2⁻¹ ^ i := by
    intro i x hx
    have hxc := subset_closure hx
    have hb1 : 1 - pathKernel P x {ω | ∀ k < m i + 1, ω k ∈ A (n i)} ≤ ε i :=
      one_sub_le_of_one_sub_lt (hnspec i x hxc)
    have hmono2 : pathKernel P x {ω | ∃ k ≤ m i, ω k ∈ A 0} ≤
        pathKernel P x {ω | ∃ k ≤ m i + 1, ω k ∈ A 0} :=
      measure_mono fun ω ⟨k, hk, hkA⟩ => ⟨k, by omega, hkA⟩
    have hb2 : 1 - pathKernel P x {ω | ∃ k ≤ m i + 1, ω k ∈ A 0} ≤ ε i :=
      one_sub_le_of_one_sub_lt ((hmspec i x hxc).trans_le hmono2)
    calc Vn (n i) x ≤ _ := h936 (n i) (m i + 1) x
      _ ≤ ε i + ε i := add_le_add hb1 hb2
      _ = 2⁻¹ ^ i := by
          simp only [ε, pow_succ]
          rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
  -- `V = Σᵢ V_{nᵢ}`
  set V : X → ℝ≥0∞ := fun x => ∑' i, Vn (n i) x
  have hVm : Measurable V := Measurable.tsum fun i => hVnm (n i)
  have hVbound : ∀ k, ∀ x ∈ A k, V x ≤ k + 2 := by
    intro k x hx
    have hterm : ∀ i, Vn (n i) x ≤ (Finset.range k : Set ℕ).indicator (fun _ => 1) i +
        2⁻¹ ^ i := by
      intro i
      by_cases hi : i < k
      · rw [indicator_of_mem (Finset.mem_coe.2 (Finset.mem_range.2 hi))]
        exact (hVn1 _ _).trans le_self_add
      · rw [indicator_of_notMem (by simpa using hi), zero_add]
        exact hsmall i x (hAmono (by omega) hx)
    calc V x ≤ ∑' i, ((Finset.range k : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)) i + 2⁻¹ ^ i) :=
          ENNReal.tsum_le_tsum hterm
      _ = ∑' i, (Finset.range k : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)) i + ∑' i, 2⁻¹ ^ i :=
          ENNReal.tsum_add
      _ = k + 2 := by
          rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
            tsum_eq_sum (s := Finset.range k) fun b hb => indicator_of_notMem (by simpa using hb) _]
          congr 1
          rw [Finset.sum_congr rfl fun b hb => indicator_of_mem (Finset.mem_coe.2 hb) _]
          simp
  have hVfin : ∀ x, V x ≠ ∞ := fun x => by
    obtain ⟨k, hk⟩ := hApt x
    exact ne_top_of_le_ne_top (by simp) (hVbound k x hk)
  set Vr : X → ℝ≥0 := fun x => (V x).toNNReal
  have hVr : ∀ x, (Vr x : ℝ≥0∞) = V x := fun x => ENNReal.coe_toNNReal (hVfin x)
  refine ⟨closure (A 0), Vr, hAcl 0, hCA.trans subset_closure, ENNReal.measurable_toNNReal.comp hVm,
    fun r => ?_, fun K hK => ?_, fun x hx => ?_⟩
  · -- coercivity
    set j := ⌈(r : ℝ)⌉₊
    set N := (Finset.range (j + 1)).sup n
    refine (hAcl N).of_isClosed_subset isClosed_closure (closure_mono fun x hx => ?_)
    by_contra hxN
    have hx0 : x ∉ A 0 := fun h => hxN (hAmono zero_le h)
    have hge : ((j + 1 : ℕ) : ℝ≥0∞) ≤ V x := by
      calc ((j + 1 : ℕ) : ℝ≥0∞) = ∑ i ∈ Finset.range (j + 1), Vn (n i) x := by
            rw [Finset.sum_congr rfl fun i hi => hVn_eq_one (n i) x
              (fun h => hxN (hAmono (Finset.le_sup hi) h)) hx0]
            simp
        _ ≤ V x := ENNReal.sum_le_tsum _
    simp only [mem_ofPred_eq] at hx
    have : ((j + 1 : ℕ) : ℝ≥0∞) ≤ r := by
      rw [← hVr x] at hge
      exact hge.trans (by exact_mod_cast hx)
    have hjr : (r : ℝ) ≤ j := Nat.le_ceil _
    have : ((j + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast this
    push_cast at this
    linarith
  · -- bounded on compacta
    obtain ⟨k, hk⟩ := hAcov K hK
    refine ⟨k + 2, fun x hx => ?_⟩
    have h := hVbound k x (hk hx)
    rw [← hVr x] at h
    exact_mod_cast h
  · -- the drift condition off `C₀ = closure A₀`
    have hx0 : x ∉ A 0 := fun h => hx (subset_closure h)
    rw [drift_nonpos_iff]
    simp_rw [hVr]
    calc ∫⁻ y, V y ∂P x = ∑' i, ∫⁻ y, Vn (n i) y ∂P x :=
          lintegral_tsum fun i => (hVnm (n i)).aemeasurable
      _ ≤ ∑' i, Vn (n i) x := ENNReal.tsum_le_tsum fun i => hVndrift (n i) x hx0

/-! ### Proposition 9.4.5: non-evanescence of random walk -/

/-- `log(1 + |x + w|)` is integrable for an integrable increment. -/
theorem integrable_log_one_add_abs (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (x : ℝ) :
    Integrable (fun w => Real.log (1 + |x + w|)) Γ :=
  ((integrable_const (1 + |x|)).add hW.abs).mono'
    ((Real.measurable_log.comp (measurable_const.add
      (continuous_abs.measurable.comp (measurable_const.add measurable_id))))).aestronglyMeasurable
    (Eventually.of_forall fun w => by
      have hpos : 0 < 1 + |x + w| := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith [abs_nonneg (x + w)]))]
      have h1 := Real.log_le_sub_one_of_pos hpos
      have h2 := abs_add_le x w
      simp only [Pi.add_apply]
      linarith)

/-- **The drift estimate behind Proposition 9.4.5** (MT p. 217): for an increment with mean zero
and finite variance, `∫ log(1 + |x + w|) Γ(dw) ≤ log(1 + x)` for all large `x > 0`. The pointwise
bound is `log(1 + x + w) ≤ log a + w/a − (w²/2a²) 1{w < 0}` (`a = 1 + x`) for `w > −x`
(`log_one_add_le`) and `log(1 − x − w) ≤ log a + w²/2x²` for `w ≤ −x`. -/
theorem randomWalk_log_drift (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW2 : Integrable (fun w => w ^ 2) Γ) (hβ : ∫ w, w ∂Γ = 0) :
    ∃ x₁ : ℝ, 1 ≤ x₁ ∧ ∀ x : ℝ, x₁ ≤ x → ∫ w, Real.log (1 + |x + w|) ∂Γ ≤ Real.log (1 + x) := by
  have hW := integrable_of_integrable_sq Γ hW2
  set c := ∫ w in Iio 0, w ^ 2 ∂Γ with hc
  have hT := tendsto_setIntegral_zero Γ hW2 (S := fun x => Iic (-x))
    (fun x => measurableSet_Iic)
    (fun w => (eventually_gt_atTop (-w)).mono fun x hx => by simp only [mem_Iic]; linarith)
  have hTc : ∀ x : ℝ, 0 < x → ∫ w in Iic (-x), w ^ 2 ∂Γ ≤ c := fun x hx =>
    setIntegral_mono_set hW2.integrableOn (Eventually.of_forall fun w => sq_nonneg w)
      (Eventually.of_forall fun w (hw : w ∈ Iic (-x)) => show w ∈ Iio (0 : ℝ) by
        simp only [mem_Iic] at hw; simp only [mem_Iio]; linarith)
  -- a threshold with `T(x) ≤ c/9`
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, ∀ x, a₀ ≤ x → 0 < x → ∫ w in Iic (-x), w ^ 2 ∂Γ ≤ c / 9 := by
    rcases (setIntegral_nonneg measurableSet_Iio fun w _ => sq_nonneg w : 0 ≤ c).lt_or_eq
      with hcpos | hc0
    · obtain ⟨a₀, h⟩ := eventually_atTop.1 (hT.eventually (ge_mem_nhds (show (0 : ℝ) < c / 9 by
        positivity)))
      exact ⟨a₀, fun x hx _ => h x hx⟩
    · have hc0' : c = 0 := hc.trans hc0.symm
      exact ⟨0, fun x _ hx => by rw [hc0', zero_div]; exact (hTc x hx).trans hc0'.le⟩
  refine ⟨max a₀ 1, le_max_right _ _, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := (le_max_right a₀ 1).trans hx
  have hx0 : (0 : ℝ) < x := by linarith
  set T := ∫ w in Iic (-x), w ^ 2 ∂Γ with hTdef
  have hT9 : T ≤ c / 9 := ha₀ x ((le_max_left a₀ 1).trans hx) hx0
  have hT0 : 0 ≤ T := setIntegral_nonneg measurableSet_Iic fun w _ => sq_nonneg w
  set a : ℝ := 1 + x with ha
  have ha0 : 0 < a := by linarith
  have hm1 : MeasurableSet (Ioi (-x)) := measurableSet_Ioi
  have hm2 : MeasurableSet (Ioo (-x) 0) := measurableSet_Ioo
  have hm3 : MeasurableSet (Iic (-x)) := measurableSet_Iic
  set h : ℝ → ℝ := fun w => Real.log a + 1 / a * (Ioi (-x)).indicator (fun w => w) w -
    1 / (2 * a ^ 2) * (Ioo (-x) 0).indicator (fun w => w ^ 2) w +
    1 / (2 * x ^ 2) * (Iic (-x)).indicator (fun w => w ^ 2) w with hh
  have hhint : Integrable h Γ :=
    (((integrable_const _).add ((hW.indicator hm1).const_mul _)).sub
      ((hW2.indicator hm2).const_mul _)).add ((hW2.indicator hm3).const_mul _)
  have hgh : ∀ w, Real.log (1 + |x + w|) ≤ h w := fun w => by
    simp only [hh]
    by_cases hw : -x < w
    · have hxw : 0 ≤ x + w := by linarith
      rw [abs_of_nonneg hxw, indicator_of_mem (show w ∈ Ioi (-x) from hw),
        indicator_of_notMem (show w ∉ Iic (-x) by simp only [mem_Iic, not_le]; exact hw),
        mul_zero, add_zero]
      have hu : -1 < w / a := by rw [lt_div_iff₀ ha0]; linarith
      have hsplit : Real.log (1 + (x + w)) = Real.log a + Real.log (1 + w / a) := by
        rw [← Real.log_mul ha0.ne' (ne_of_gt (by linarith))]
        congr 1; field_simp; ring
      rw [hsplit]
      have := log_one_add_le hu
      by_cases hw0 : w < 0
      · have hu0 : w / a < 0 := div_neg_of_neg_of_pos hw0 ha0
        simp only [hu0, ite_true, mul_one] at this
        rw [indicator_of_mem (show w ∈ Ioo (-x) 0 from ⟨hw, hw0⟩)]
        have e : (w / a) ^ 2 / 2 = 1 / (2 * a ^ 2) * w ^ 2 := by field_simp
        have e2 : w / a = 1 / a * w := by ring
        linarith
      · have hu0 : ¬ w / a < 0 := fun h' => hw0 (by
          rcases div_neg_iff.1 h' with ⟨_, h2⟩ | ⟨h1, _⟩
          · linarith
          · exact h1)
        simp only [hu0, ite_false, mul_zero, sub_zero] at this
        rw [indicator_of_notMem (show w ∉ Ioo (-x) 0 from fun h' => hw0 h'.2), mul_zero,
          sub_zero]
        have e2 : w / a = 1 / a * w := by ring
        linarith
    · have hwx : w ≤ -x := not_lt.1 hw
      have hxw : x + w ≤ 0 := by linarith
      rw [abs_of_nonpos hxw, indicator_of_notMem (show w ∉ Ioi (-x) from hw),
        indicator_of_notMem (show w ∉ Ioo (-x) 0 from fun h' => hw h'.1),
        indicator_of_mem (show w ∈ Iic (-x) from hwx), mul_zero, mul_zero, add_zero, sub_zero]
      -- `log(1 − x − w) ≤ log a + log(−w/x)` and `log t ≤ t²/2`
      have hpos1 : 0 < 1 + -(x + w) := by linarith
      have hratio : 1 + -(x + w) ≤ a * (-w / x) := by
        rw [ha, mul_div_assoc', le_div_iff₀ hx0]
        nlinarith
      have ht : 0 < -w / x := div_pos (by linarith) hx0
      have hlog1 : Real.log (1 + -(x + w)) ≤ Real.log a + Real.log (-w / x) := by
        rw [← Real.log_mul ha0.ne' ht.ne']
        exact Real.log_le_log hpos1 hratio
      have hlog2 : Real.log (-w / x) ≤ 1 / (2 * x ^ 2) * w ^ 2 := by
        have := Real.log_le_sub_one_of_pos ht
        have e : 1 / (2 * x ^ 2) * w ^ 2 = (-w / x) ^ 2 / 2 := by field_simp
        rw [e]
        nlinarith [sq_nonneg (-w / x - 1)]
      linarith
  -- the pieces of `∫ h`
  have hI1 : ∫ w in Ioi (-x), w ∂Γ ≤ T / x := by
    have hcompl : Ioi (-x) = (Iic (-x))ᶜ := by ext; simp
    have hsum := integral_add_compl (measurableSet_Iic (a := -x)) hW
    rw [hβ, ← hcompl] at hsum
    have hle : -∫ w in Iic (-x), w ∂Γ ≤ T / x := by
      rw [← integral_neg, hTdef, ← integral_div]
      refine setIntegral_mono_on hW.neg.integrableOn (hW2.div_const _).integrableOn
        measurableSet_Iic fun w hw => ?_
      simp only [mem_Iic] at hw
      rw [le_div_iff₀ hx0]
      nlinarith
    linarith
  have hI2 : ∫ w in Ioo (-x) 0, w ^ 2 ∂Γ = c - T := by
    have hunion : Iio (0 : ℝ) = Iic (-x) ∪ Ioo (-x) 0 := by
      ext w; simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
      constructor
      · intro h; by_cases hw : w ≤ -x
        · exact Or.inl hw
        · exact Or.inr ⟨by linarith, h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint (Iic (-x)) (Ioo (-x) 0) :=
      Set.disjoint_left.2 fun w h1 h2 => by simp only [mem_Iic, mem_Ioo] at h1 h2; linarith
    rw [hc, hunion, setIntegral_union hdisj hm2 hW2.integrableOn hW2.integrableOn, hTdef]
    ring
  have hint_h : ∫ w, h w ∂Γ = Real.log a + 1 / a * ∫ w in Ioi (-x), w ∂Γ -
      1 / (2 * a ^ 2) * ∫ w in Ioo (-x) 0, w ^ 2 ∂Γ + 1 / (2 * x ^ 2) * T := by
    simp only [hh]
    have i0 : Integrable (fun _ : ℝ => Real.log a) Γ := integrable_const _
    have i1 : Integrable (fun w => 1 / a * (Ioi (-x)).indicator (fun w => w) w) Γ :=
      (hW.indicator hm1).const_mul _
    have i2 : Integrable (fun w => 1 / (2 * a ^ 2) * (Ioo (-x) 0).indicator (fun w => w ^ 2) w)
      Γ := (hW2.indicator hm2).const_mul _
    have i3 : Integrable (fun w => 1 / (2 * x ^ 2) * (Iic (-x)).indicator (fun w => w ^ 2) w)
      Γ := (hW2.indicator hm3).const_mul _
    have i01 : Integrable (fun w => Real.log a + 1 / a * (Ioi (-x)).indicator (fun w => w) w)
      Γ := i0.add i1
    have i012 : Integrable (fun w => Real.log a + 1 / a * (Ioi (-x)).indicator (fun w => w) w -
      1 / (2 * a ^ 2) * (Ioo (-x) 0).indicator (fun w => w ^ 2) w) Γ := i01.sub i2
    rw [integral_add i012 i3, integral_sub i01 i2, integral_add i0 i1,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_indicator hm1, integral_indicator hm2, integral_indicator hm3, integral_const]
    simp [hTdef]
  calc ∫ w, Real.log (1 + |x + w|) ∂Γ ≤ ∫ w, h w ∂Γ :=
        integral_mono (integrable_log_one_add_abs Γ hW x) hhint hgh
    _ = Real.log a + 1 / a * ∫ w in Ioi (-x), w ∂Γ - 1 / (2 * a ^ 2) * (c - T) +
          1 / (2 * x ^ 2) * T := by rw [hint_h, hI2]
    _ ≤ Real.log a + 1 / a * (T / x) - 1 / (2 * a ^ 2) * (c - T) + 1 / (2 * x ^ 2) * T := by
        gcongr
    _ ≤ Real.log a := by
        have key : 1 / a * (T / x) - 1 / (2 * a ^ 2) * (c - T) + 1 / (2 * x ^ 2) * T ≤ 0 := by
          have hc9 : 9 * T ≤ c := by linarith
          have hax : a ≤ 2 * x := by linarith
          have e : 1 / a * (T / x) - 1 / (2 * a ^ 2) * (c - T) + 1 / (2 * x ^ 2) * T =
              (2 * a * x * T - x ^ 2 * (c - T) + a ^ 2 * T) / (2 * a ^ 2 * x ^ 2) := by
            field_simp
          rw [e]
          refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
          nlinarith [mul_le_mul_of_nonneg_right hax hT0, mul_nonneg hT0 (sq_nonneg x),
            mul_nonneg hT0 ha0.le, mul_le_mul hax hax ha0.le (by linarith)]
        linarith

/-- `V(y) = log(1 + |y|)` is coercive on `ℝ`. -/
theorem isCoercive_log_one_add_abs :
    IsCoercive (fun y : ℝ => Real.toNNReal (Real.log (1 + |y|))) := by
  intro r
  refine (isCompact_closedBall (0 : ℝ) (Real.exp r)).of_isClosed_subset isClosed_closure
    (closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall)
  simp only [mem_ofPred_eq] at hy
  have h1 : Real.log (1 + |y|) ≤ r := by
    have := NNReal.coe_le_coe.2 hy
    rwa [Real.coe_toNNReal _ (Real.log_nonneg (by linarith [abs_nonneg y]))] at this
  have h2 : 1 + |y| ≤ Real.exp r := by
    rw [← Real.log_le_iff_le_exp (by positivity)]; exact h1
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  linarith

/-- Converting the real drift bound for `log(1 + |·|)` into the `[0, ∞]`-valued (V1). -/
theorem lintegral_log_one_add_abs_le (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (x : ℝ) {c : ℝ}
    (h : ∫ w, Real.log (1 + |c + w|) ∂Γ ≤ Real.log (1 + |x|)) :
    ∫⁻ w, ((Real.toNNReal (Real.log (1 + |c + w|)) : ℝ≥0) : ℝ≥0∞) ∂Γ ≤
      ((Real.toNNReal (Real.log (1 + |x|)) : ℝ≥0) : ℝ≥0∞) := by
  have hint := integrable_log_one_add_abs Γ hW c
  have heq : ∀ y : ℝ, ((Real.toNNReal (Real.log (1 + |y|)) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Real.log (1 + |y|)) := fun y => rfl
  simp_rw [heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun w => Real.log_nonneg (by linarith [abs_nonneg (c + w)]))]
  exact ENNReal.ofReal_le_ofReal h

/-- The drift estimate on both sides: for an increment with mean zero and finite variance,
`∫ log(1 + |x + w|) Γ(dw) ≤ log(1 + |x|)` for all `|x|` large (the case `x < 0` is the case
`x > 0` for the reflected law `Γ ∘ (−·)⁻¹`). -/
theorem randomWalk_log_drift_abs (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW2 : Integrable (fun w => w ^ 2) Γ) (hβ : ∫ w, w ∂Γ = 0) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x : ℝ, R < |x| →
      ∫ w, Real.log (1 + |x + w|) ∂Γ ≤ Real.log (1 + |x|) := by
  set Γ' := Γ.map Neg.neg
  have hneg : Measurable (Neg.neg : ℝ → ℝ) := measurable_neg
  have : IsProbabilityMeasure Γ' := inferInstance
  have hW2' : Integrable (fun w => w ^ 2) Γ' := by
    rw [integrable_map_measure (by fun_prop) hneg.aemeasurable]
    simpa [Function.comp_def] using hW2
  have hβ' : ∫ w, w ∂Γ' = 0 := by
    rw [show (∫ w, w ∂Γ') = ∫ w, -w ∂Γ from
      integral_map hneg.aemeasurable measurable_id.aestronglyMeasurable, integral_neg, hβ,
      neg_zero]
  obtain ⟨x₁, hx₁, hdr⟩ := randomWalk_log_drift Γ hW2 hβ
  obtain ⟨x₂, hx₂, hdr'⟩ := randomWalk_log_drift Γ' hW2' hβ'
  refine ⟨max x₁ x₂, hx₁.trans (le_max_left _ _), fun x hx => ?_⟩
  rcases lt_or_ge x 0 with hneg0 | hpos0
  · rw [abs_of_neg hneg0] at hx
    have hxpos : x₂ ≤ -x := by linarith [le_max_right x₁ x₂]
    have := hdr' (-x) hxpos
    have hmeas : Measurable fun w : ℝ => Real.log (1 + |-x + w|) :=
      Real.measurable_log.comp (measurable_const.add (continuous_abs.measurable.comp
        (measurable_const.add measurable_id)))
    have e : ∫ w, Real.log (1 + |-x + w|) ∂Γ' = ∫ w, Real.log (1 + |-x + -w|) ∂Γ :=
      integral_map hneg.aemeasurable hmeas.aestronglyMeasurable
    rw [e] at this
    have e1 : ∀ w : ℝ, |-x + -w| = |x + w| := fun w => by
      rw [← neg_add, abs_neg]
    simp only [e1] at this
    rwa [abs_of_neg hneg0]
  · rw [abs_of_nonneg hpos0] at hx ⊢
    exact hdr x (by linarith [le_max_left x₁ x₂])

/-- **Proposition 9.4.5** (MT p. 217): random walk on `ℝ` whose increment has mean `β = 0` and
`E[W²] < ∞` is non-evanescent; the test function is `V(x) = log(1 + |x|)`, coercive, with
(V1) off a compact interval (Theorem 9.4.1). -/
theorem proposition_9_4_5 (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW2 : Integrable (fun w => w ^ 2) Γ) (hβ : ∫ w, w ∂Γ = 0) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    IsNonEvanescent (randomWalkKernel Γ) := by
  have := isMarkovKernel_randomWalkKernel Γ
  have hW := integrable_of_integrable_sq Γ hW2
  obtain ⟨R, hR1, hdr⟩ := randomWalk_log_drift_abs Γ hW2 hβ
  set V : ℝ → ℝ≥0 := fun y => Real.toNNReal (Real.log (1 + |y|))
  have hVm : Measurable V :=
    (Real.measurable_log.comp (measurable_const.add continuous_abs.measurable)).real_toNNReal
  refine theorem_9_4_1 hVm (isCoercive_log_one_add_abs) (isCompact_Icc (a := -R) (b := R))
    fun x hx => ?_
  have hxR : R < |x| := by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]
      linarith
    · exact lt_of_lt_of_le hx (le_abs_self x)
  have hVe : Measurable fun y => ((V y : ℝ≥0) : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hVm
  rw [drift_nonpos_iff, randomWalkKernel_apply, lintegral_map hVe (measurable_const_add x)]
  exact lintegral_log_one_add_abs_le Γ hW x (hdr x hxR)

/-! ### Lemma 9.4.4 -/

/-- `x² Γ(−∞, t + sx) → 0` as `x → −∞` when `E[W²] < ∞` and `s > 0`. -/
theorem tendsto_sq_mul_lowerTail (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW2 : Integrable (fun w => w ^ 2) Γ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Tendsto (fun x => x ^ 2 * (Γ (Iio (t + s * x))).toReal) atBot (𝓝 0) := by
  -- the dominating tail integral
  have hT := tendsto_setIntegral_zero Γ hW2 (S := fun y => Iio (t - s * y))
    (fun y => measurableSet_Iio)
    (fun w => (eventually_gt_atTop ((t - w) / s)).mono fun y hy => by
      simp only [mem_Iio, not_lt]
      rw [div_lt_iff₀ hs] at hy; linarith)
  have hT' : Tendsto (fun x => 4 / s ^ 2 * ∫ w in Iio (t - s * -x), w ^ 2 ∂Γ) atBot (𝓝 0) := by
    simpa using (hT.comp tendsto_neg_atBot_atTop).const_mul (4 / s ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT'
    (Eventually.of_forall fun x => by positivity) ?_
  filter_upwards [eventually_le_atBot (min (-1) (-2 * |t| / s))] with x hx
  have hx1 : x ≤ -2 * |t| / s := hx.trans (min_le_right _ _)
  have hxneg : x < 0 := lt_of_le_of_lt (hx.trans (min_le_left _ _)) (by norm_num)
  have hsx : 2 * |t| ≤ -(s * x) := by rw [le_div_iff₀ hs] at hx1; linarith
  rw [show t - s * -x = t + s * x by ring]
  rw [← Measure.real, ← setIntegral_one_eq_measureReal (s := Iio (t + s * x)), ← integral_const_mul,
    ← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_const) ((hW2.integrableOn).const_mul _)
    measurableSet_Iio fun w hw => ?_
  simp only [mem_Iio] at hw
  have hw' : -(s * x) / 2 ≤ -w := by linarith [le_abs_self t]
  have hpos : 0 ≤ -(s * x) / 2 := by nlinarith
  have h1 : (s * x) ^ 2 / 4 ≤ w ^ 2 := by nlinarith
  rw [mul_one, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- **Lemma 9.4.4 (i)** (MT p. 217): for `E[W²] < ∞`, `s, u₂, v₂ > 0` and `t₁ ≥ t₂`,
`lim sup_{x → −∞} x²[−Γ(−∞, t₁ + sx) log(u₁ − u₂x) + Γ(−∞, t₂ + sx)(log(v₁ − v₂x) − c)] ≤ 0`;
stated as: for every `ε > 0` the expression is eventually `≤ ε`. -/
theorem lemma_9_4_4_i (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW2 : Integrable (fun w => w ^ 2) Γ) {s u₁ u₂ v₁ v₂ t₁ t₂ c : ℝ} (hs : 0 < s)
    (hu₂ : 0 < u₂) (hv₂ : 0 < v₂) (ht : t₂ ≤ t₁) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atBot, x ^ 2 * (-(Γ (Iio (t₁ + s * x))).toReal * Real.log (u₁ - u₂ * x) +
      (Γ (Iio (t₂ + s * x))).toReal * (Real.log (v₁ - v₂ * x) - c)) ≤ ε := by
  -- the log ratio converges
  have hratio : Tendsto (fun x => (v₁ - v₂ * x) / (u₁ - u₂ * x)) atBot (𝓝 (v₂ / u₂)) := by
    have h1 : Tendsto (fun x : ℝ => v₁ / x - v₂) atBot (𝓝 (0 - v₂)) :=
      (tendsto_const_nhds.div_atBot tendsto_id).sub tendsto_const_nhds
    have h2 : Tendsto (fun x : ℝ => u₁ / x - u₂) atBot (𝓝 (0 - u₂)) :=
      (tendsto_const_nhds.div_atBot tendsto_id).sub tendsto_const_nhds
    have h3 := h1.div h2 (by simp only [zero_sub, ne_eq, neg_eq_zero]; exact hu₂.ne')
    rw [show (0 - v₂) / (0 - u₂) = v₂ / u₂ by ring] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_lt_atBot 0] with x hx
    have hx0 : x ≠ 0 := hx.ne
    have e1 : v₁ / x - v₂ = (v₁ - v₂ * x) / x := by
      rw [sub_div, mul_div_assoc, div_self hx0, mul_one]
    have e2 : u₁ / x - u₂ = (u₁ - u₂ * x) / x := by
      rw [sub_div, mul_div_assoc, div_self hx0, mul_one]
    simp only [Pi.div_apply]
    rw [e1, e2, div_div_div_cancel_right₀ hx0]
  have hlog : Tendsto (fun x => Real.log (v₁ - v₂ * x) - c - Real.log (u₁ - u₂ * x)) atBot
      (𝓝 (Real.log (v₂ / u₂) - c)) := by
    have h := ((Real.continuousAt_log (by positivity)).tendsto.comp hratio).sub_const c
    refine h.congr' ?_
    filter_upwards [eventually_le_atBot ((u₁ - 1) / u₂), eventually_le_atBot ((v₁ - 1) / v₂)]
      with x hxu hxv
    have hu : 0 < u₁ - u₂ * x := by rw [le_div_iff₀ hu₂] at hxu; linarith
    have hv : 0 < v₁ - v₂ * x := by rw [le_div_iff₀ hv₂] at hxv; linarith
    simp only [Function.comp_apply]
    rw [Real.log_div hv.ne' hu.ne']
    ring
  have hprod := (tendsto_sq_mul_lowerTail Γ hW2 hs t₂).mul hlog
  rw [zero_mul] at hprod
  filter_upwards [hprod.eventually (gt_mem_nhds hε), eventually_le_atBot ((u₁ - 1) / u₂)]
    with x hx hxu
  have hu : 1 ≤ u₁ - u₂ * x := by rw [le_div_iff₀ hu₂] at hxu; linarith
  have hL1 : 0 ≤ Real.log (u₁ - u₂ * x) := Real.log_nonneg hu
  have hF : (Γ (Iio (t₂ + s * x))).toReal ≤ (Γ (Iio (t₁ + s * x))).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iio_subset_Iio (by linarith)))
  have hle : -(Γ (Iio (t₁ + s * x))).toReal * Real.log (u₁ - u₂ * x) +
      (Γ (Iio (t₂ + s * x))).toReal * (Real.log (v₁ - v₂ * x) - c) ≤
      (Γ (Iio (t₂ + s * x))).toReal * (Real.log (v₁ - v₂ * x) - c - Real.log (u₁ - u₂ * x)) := by
    nlinarith [mul_le_mul_of_nonneg_right hF hL1]
  calc _ ≤ x ^ 2 * ((Γ (Iio (t₂ + s * x))).toReal *
        (Real.log (v₁ - v₂ * x) - c - Real.log (u₁ - u₂ * x))) :=
        mul_le_mul_of_nonneg_left hle (sq_nonneg x)
    _ ≤ ε := by rw [← mul_assoc]; exact hx.le

/-- **Lemma 9.4.4 (ii)** (MT p. 217): the reflected statement as `x → ∞`,
`lim sup x²[−Γ(t₂ + sx, ∞) log(v₁ + v₂x) + Γ(t₁ + sx, ∞)(log(u₁ + u₂x) − c)] ≤ 0`. -/
theorem lemma_9_4_4_ii (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW2 : Integrable (fun w => w ^ 2) Γ) {s u₁ u₂ v₁ v₂ t₁ t₂ c : ℝ} (hs : 0 < s)
    (hu₂ : 0 < u₂) (hv₂ : 0 < v₂) (ht : t₂ ≤ t₁) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, x ^ 2 * (-(Γ (Ioi (t₂ + s * x))).toReal * Real.log (v₁ + v₂ * x) +
      (Γ (Ioi (t₁ + s * x))).toReal * (Real.log (u₁ + u₂ * x) - c)) ≤ ε := by
  set Γ' := Γ.map Neg.neg
  have hneg : Measurable (Neg.neg : ℝ → ℝ) := measurable_neg
  have : IsProbabilityMeasure Γ' := inferInstance
  have hW2' : Integrable (fun w => w ^ 2) Γ' := by
    rw [integrable_map_measure (by fun_prop) hneg.aemeasurable]
    simpa [Function.comp_def] using hW2
  have hrefl : ∀ a : ℝ, Γ (Ioi a) = Γ' (Iio (-a)) := fun a => by
    rw [Measure.map_apply hneg measurableSet_Iio]
    congr 1; ext w; simp
  have h := lemma_9_4_4_i Γ' hW2' (u₁ := v₁) (u₂ := v₂) (v₁ := u₁) (v₂ := u₂) (t₁ := -t₂)
    (t₂ := -t₁) (c := c) hs hv₂ hu₂ (by linarith) hε
  filter_upwards [tendsto_neg_atTop_atBot.eventually h] with x hx
  have e1 : -t₂ + s * -x = -(t₂ + s * x) := by ring
  have e2 : -t₁ + s * -x = -(t₁ + s * x) := by ring
  have e3 : v₁ - v₂ * -x = v₁ + v₂ * x := by ring
  have e4 : u₁ - u₂ * -x = u₁ + u₂ * x := by ring
  rw [e1, e2, e3, e4, neg_sq, ← hrefl, ← hrefl] at hx
  exact hx

end MeynTweedie.FErgodicity
