/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.Comparison
import LimitTheorems.HarrisLLN
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw

/-!
# Regeneration at an atom: the i.i.d. cycles (MT §17.2, (17.9)–(17.10))

Meyn and Tweedie, §17.2, p. 428: "by the strong Markov property the random variables
`{sⱼ(f) : j ≥ 0}` are i.i.d." This module proves that statement, in the strongest form: the
whole excursions of the chain between consecutive visits to an atom are i.i.d. random elements of
path space.

**Definitions.** For a set `α`:
* `hitNat α ω = σ_α` as a natural number (`0` if `α` is never hit);
* `excursion α ω`: the path frozen at time `σ_α`, `i ↦ Φ_{min(i, σ_α)}` (the whole path if `α` is
  never hit);
* `restart α ω = θ^{σ_α + 1} ω`, the path after its first visit to `α`;
* `cycle α j = excursion α ∘ restartʲ`: `cycle α 0` is the initial segment up to `σ_α`, and
  `cycle α (j + 1)` is the `(j + 1)`-th full cycle, from just after the `j`-th visit to `α` up to
  the `(j + 1)`-th;
* `renewalTime α j`: the time `σ_α(j)` of the `(j + 1)`-th visit to `α` (from time `0`);
* `cycleSum α g e = Σ_{i ≤ σ_α(e)} g(eᵢ)`, a cycle functional, so that `cycleSum α g (cycle α j)`
  is the book's `s_{j−1}(g)` (17.9) for `j ≥ 1`.

**Pathwise identities.**
* `firstHit_excursion`: an excursion has the same first hitting time as its path;
  `cycleSum_excursion`.
* `sum_range_renewalTime`: `Σ_{i ≤ σ_α(j)} g(Φᵢ) = Σ_{i ≤ j} cycleSum g (cycle i)`;
  `renewalTime_add_one`: `σ_α(j) + 1 = Σ_{i ≤ j} (σ_α(cycle i) + 1)`;
  `renewalTime_lt_succ`: the visit times increase strictly.

**The regeneration theorem.** Let `α` be an atom, `a ∈ α`, `ν = P(a, ·)`, and suppose that `α`
is reached almost surely from `ν` and from the initial law `μ`.
* `lintegral_mul_restart` (the strong Markov property at `σ_α`): for `𝓕_{σ_α}`-measurable
  `F ≥ 0` and measurable `K ≥ 0`, `E_μ[F · K(θ^{σ_α+1}Φ)] = E_μ[F] E_ν[K]`.
* `pathMeasure_cycles_box`: under `P_ν` the cycles `cycle α j`, `j ≥ 0`, are independent with
  common law `ρ = P_ν ∘ excursion⁻¹` (`cycleLaw`).
* **`map_cycles_eq_infinitePi`**: under `P_μ`, the law of the sequence of full cycles
  `(cycle α (j + 1))_{j ≥ 0}` is the product `ρ^{⊗ℕ}`.
* `ae_cycles_of_ae_infinitePi`: an almost sure property of an i.i.d. `ρ`-sequence holds for the
  cycles; `tendsto_cycle_average`: the strong law for a cycle functional.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### First hitting times -/

omit [MeasurableSpace X] in
/-- `σ_α = n` iff `Φₙ ∈ α` and `Φⱼ ∉ α` for `j < n`. -/
theorem firstHit_eq_coe_iff (α : Set X) (ω : ℕ → X) (n : ℕ) :
    firstHit α ω = n ↔ ω n ∈ α ∧ ∀ j < n, ω j ∉ α := by
  constructor
  · intro h
    refine ⟨?_, (le_firstHit_iff α ω n).1 h.ge⟩
    have hne : firstHit α ω ≠ ⊤ := by rw [h]; exact WithTop.coe_ne_top
    have := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := α) (n := 0)
      (ω := ω) hne
    rw [← firstHit, h] at this
    exact this
  · rintro ⟨h1, h2⟩
    exact le_antisymm (hittingAfter_le_of_mem (Nat.zero_le n) h1) ((le_firstHit_iff α ω n).2 h2)

/-- `σ_α` as a natural number (a junk value if `α` is never hit). -/
noncomputable def hitNat (α : Set X) (ω : ℕ → X) : ℕ := (firstHit α ω).untopA

omit [MeasurableSpace X] in
/-- If `α` is hit, `σ_α = hitNat α`. -/
theorem firstHit_eq_hitNat {α : Set X} {ω : ℕ → X} (h : firstHit α ω ≠ ⊤) :
    firstHit α ω = WithTop.some (hitNat α ω) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h
  rw [hitNat, ← hn]
  rfl

/-- `σ_α` is a stopping time. -/
theorem isStoppingTime_firstHit {α : Set X} (hα : MeasurableSet α) :
    IsStoppingTime (natFilt (X := X)) (firstHit α) :=
  (proposition_3_4_4 hα).2

/-- `hitNat α` is measurable. -/
theorem measurable_hitNat {α : Set X} (hα : MeasurableSet α) : Measurable (hitNat α) := by
  have hτ := isStoppingTime_firstHit hα
  refine measurable_of_stopping_pieces hτ (fun n _ => n) (fun _ => (⊤ : WithTop ℕ).untopA)
    (fun _ => measurable_const) measurable_const (fun n ω h => ?_) (fun ω h => ?_)
  · rw [hitNat, h]; rfl
  · rw [hitNat, h]

/-! ### Excursions, restarts and cycles -/

/-- The excursion: the path frozen at its first visit to `α`, `i ↦ Φ_{min(i, σ_α)}`. -/
noncomputable def excursion (α : Set X) (ω : ℕ → X) : ℕ → X :=
  fun i => ω (min (firstHit α ω) (WithTop.some i)).untopA

/-- The path restarted just after its first visit to `α`: `θ^{σ_α + 1} ω`. -/
noncomputable def restart (α : Set X) (ω : ℕ → X) : ℕ → X := shift (hitNat α ω + 1) ω

/-- The cycles: `cycle α 0` is the initial segment, `cycle α (j + 1)` the `(j + 1)`-th full
cycle between visits to `α`. -/
noncomputable def cycle (α : Set X) (j : ℕ) (ω : ℕ → X) : ℕ → X :=
  excursion α ((restart α)^[j] ω)

/-- The visit times: `renewalTime α 0 = σ_α`, `renewalTime α (j + 1) = σ_α + 1 + renewalTime α j ∘
restart`, the time of the `(j + 1)`-th visit to `α`. -/
noncomputable def renewalTime (α : Set X) : ℕ → (ℕ → X) → ℕ
  | 0 => hitNat α
  | j + 1 => fun ω => hitNat α ω + 1 + renewalTime α j (restart α ω)

/-- A cycle functional: the sum `Σ_{i ≤ σ_α(e)} g(eᵢ)` over an excursion `e`. -/
noncomputable def cycleSum (α : Set X) (g : X → ℝ) (e : ℕ → X) : ℝ :=
  ∑ i ∈ Finset.range (hitNat α e + 1), g (e i)

/-- `(min n i).untopA = min n i` in `ℕ ∪ {∞}`. -/
theorem untopA_min_coe (n i : ℕ) :
    (min (WithTop.some n) (WithTop.some i)).untopA = min n i := by
  rcases le_total n i with h | h
  · rw [min_eq_left (WithTop.coe_le_coe.2 h), min_eq_left h]; rfl
  · rw [min_eq_right (WithTop.coe_le_coe.2 h), min_eq_right h]; rfl

omit [MeasurableSpace X] in
/-- The excursion agrees with the path up to `hitNat`. -/
theorem excursion_apply_of_le_hitNat {α : Set X} {ω : ℕ → X} {i : ℕ}
    (hi : i ≤ hitNat α ω) : excursion α ω i = ω i := by
  unfold excursion
  cases h : firstHit α ω with
  | top => rfl
  | coe n =>
    have hn : hitNat α ω = n := by rw [hitNat, h]; rfl
    rw [hn] at hi
    rw [untopA_min_coe, min_eq_right hi]

omit [MeasurableSpace X] in
/-- An excursion has the same first hitting time as its path. -/
theorem firstHit_excursion (α : Set X) (ω : ℕ → X) :
    firstHit α (excursion α ω) = firstHit α ω := by
  cases h : firstHit α ω with
  | top =>
    have : excursion α ω = ω := by
      ext i; unfold excursion; rw [h]; rfl
    rw [this, h]
  | coe n =>
    have hn : hitNat α ω = n := by rw [hitNat, h]; rfl
    have h2 := (firstHit_eq_coe_iff α ω n).1 h
    refine (firstHit_eq_coe_iff α _ n).2 ⟨?_, fun j hj => ?_⟩
    · rw [excursion_apply_of_le_hitNat (by omega)]; exact h2.1
    · rw [excursion_apply_of_le_hitNat (by omega)]; exact h2.2 j hj

omit [MeasurableSpace X] in
/-- `hitNat` of an excursion. -/
theorem hitNat_excursion (α : Set X) (ω : ℕ → X) : hitNat α (excursion α ω) = hitNat α ω := by
  rw [hitNat, hitNat, firstHit_excursion]

omit [MeasurableSpace X] in
/-- `cycleSum g (excursion ω) = Σ_{i ≤ σ_α} g(Φᵢ)`. -/
theorem cycleSum_excursion (α : Set X) (g : X → ℝ) (ω : ℕ → X) :
    cycleSum α g (excursion α ω) = ∑ i ∈ Finset.range (hitNat α ω + 1), g (ω i) := by
  unfold cycleSum
  rw [hitNat_excursion]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [excursion_apply_of_le_hitNat (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

omit [MeasurableSpace X] in
/-- `cycle α (j + 1) = cycle α j ∘ restart`. -/
theorem cycle_succ (α : Set X) (j : ℕ) (ω : ℕ → X) :
    cycle α (j + 1) ω = cycle α j (restart α ω) := by
  rw [cycle, cycle, Function.iterate_succ_apply]

omit [MeasurableSpace X] in
/-- **The cycle decomposition of the partial sums**:
`Σ_{i ≤ σ_α(j)} g(Φᵢ) = Σ_{i ≤ j} cycleSum g (cycle i)`. -/
theorem sum_range_renewalTime (α : Set X) (g : X → ℝ) (j : ℕ) (ω : ℕ → X) :
    ∑ i ∈ Finset.range (renewalTime α j ω + 1), g (ω i) =
      ∑ i ∈ Finset.range (j + 1), cycleSum α g (cycle α i ω) := by
  induction j generalizing ω with
  | zero =>
    simp only [renewalTime, zero_add, Finset.range_one, Finset.sum_singleton, cycle,
      Function.iterate_zero, id_eq]
    rw [cycleSum_excursion]
  | succ j ih =>
    have e : renewalTime α (j + 1) ω + 1 =
        (hitNat α ω + 1) + (renewalTime α j (restart α ω) + 1) := by
      simp only [renewalTime]; ring
    rw [e, Finset.sum_range_add, Finset.sum_range_succ' _ (j + 1)]
    have h2 : ∑ x ∈ Finset.range (renewalTime α j (restart α ω) + 1),
        g (ω (hitNat α ω + 1 + x)) =
        ∑ x ∈ Finset.range (renewalTime α j (restart α ω) + 1), g (restart α ω x) := rfl
    rw [h2, ih (restart α ω)]
    simp only [cycle_succ]
    rw [show cycle α 0 ω = excursion α ω from rfl, cycleSum_excursion, add_comm]

omit [MeasurableSpace X] in
/-- `cycleSum 1 e = σ_α(e) + 1`, the cycle length. -/
theorem cycleSum_one (α : Set X) (e : ℕ → X) : cycleSum α 1 e = hitNat α e + 1 := by
  simp [cycleSum]

omit [MeasurableSpace X] in
/-- `σ_α(j) + 1 = Σ_{i ≤ j} (σ_α(cycle i) + 1)`. -/
theorem renewalTime_add_one (α : Set X) (j : ℕ) (ω : ℕ → X) :
    (renewalTime α j ω : ℝ) + 1 =
      ∑ i ∈ Finset.range (j + 1), ((hitNat α (cycle α i ω) : ℝ) + 1) := by
  have h := sum_range_renewalTime α 1 j ω
  simp only [Pi.one_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  rw [← Nat.cast_add_one, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cycleSum_one]

omit [MeasurableSpace X] in
/-- The visit times increase: `σ_α(j + 1) = σ_α(j) + σ_α(cycle (j + 1)) + 1`. -/
theorem renewalTime_succ (α : Set X) (j : ℕ) (ω : ℕ → X) :
    renewalTime α (j + 1) ω = renewalTime α j ω + hitNat α (cycle α (j + 1) ω) + 1 := by
  have h1 := renewalTime_add_one α (j + 1) ω
  have h2 := renewalTime_add_one α j ω
  rw [Finset.sum_range_succ, ← h2] at h1
  have : ((renewalTime α (j + 1) ω : ℕ) : ℝ) =
      ((renewalTime α j ω + hitNat α (cycle α (j + 1) ω) + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

omit [MeasurableSpace X] in
/-- The visit times increase strictly. -/
theorem renewalTime_lt_succ (α : Set X) (j : ℕ) (ω : ℕ → X) :
    renewalTime α j ω < renewalTime α (j + 1) ω := by
  rw [renewalTime_succ]; omega

omit [MeasurableSpace X] in
/-- `j ≤ σ_α(j)`. -/
theorem le_renewalTime (α : Set X) (j : ℕ) (ω : ℕ → X) : j ≤ renewalTime α j ω := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih => exact (Nat.succ_le_of_lt (lt_of_le_of_lt ih (renewalTime_lt_succ α j ω)))

/-! ### Measurability -/

/-- The excursion map is measurable. -/
theorem measurable_excursion {α : Set X} (hα : MeasurableSet α) :
    Measurable (excursion α) := by
  refine measurable_pi_iff.2 fun i => ?_
  exact measurable_stoppedState ((isStoppingTime_firstHit hα).min_const i)

omit [MeasurableSpace X] in
/-- The restart map is `θ¹ ∘ θ^{σ_α}`. -/
theorem restart_eq (α : Set X) (ω : ℕ → X) :
    restart α ω = shift 1 (shiftAt (firstHit α) ω) := by
  rw [restart, shiftAt, shift_shift]
  rfl

/-- The restart map is measurable. -/
theorem measurable_restart {α : Set X} (hα : MeasurableSet α) : Measurable (restart α) := by
  have : restart α = fun ω => shift 1 (shiftAt (firstHit α) ω) := funext (restart_eq α)
  rw [this]
  exact (measurable_shift 1).comp (measurable_shiftAt (isStoppingTime_firstHit hα))

/-- Every cycle map is measurable. -/
theorem measurable_cycle {α : Set X} (hα : MeasurableSet α) (j : ℕ) :
    Measurable (cycle α j) :=
  (measurable_excursion hα).comp ((measurable_restart hα).iterate j)

/-- A cycle functional is measurable. -/
theorem measurable_cycleSum {α : Set X} (hα : MeasurableSet α) {g : X → ℝ} (hg : Measurable g) :
    Measurable (cycleSum α g) := by
  have hF : Measurable fun p : (ℕ → X) × ℕ => ∑ i ∈ Finset.range (p.2 + 1), g (p.1 i) :=
    measurable_from_prod_countable_left fun n => by
      dsimp only
      exact Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i)
  exact hF.comp (measurable_id.prodMk (measurable_hitNat hα))

/-- The excursion is `𝓕_{σ_α}`-measurable: it only depends on the path up to `σ_α`. -/
theorem measurable_stoppedField_excursion {α : Set X} (hα : MeasurableSet α) :
    Measurable[(isStoppingTime_firstHit hα).measurableSpace] (excursion α) := by
  intro S hS
  rw [measurableSet_stoppedField_iff]
  refine ⟨measurable_excursion hα hS, fun n => ?_⟩
  set stop : (ℕ → X) → ℕ → X := fun ω i => ω (min n i) with hstop
  have hstopm : Measurable[natFilt n] stop := by
    refine (@measurable_pi_iff (ℕ → X) ℕ (fun _ => X) (natFilt n) _ stop).2 fun i => ?_
    exact (measurable_coord_natFilt (min n i)).mono ((natFilt (X := X)).mono (min_le_left n i))
      le_rfl
  have : excursion α ⁻¹' S ∩ {ω | firstHit α ω = n} = stop ⁻¹' S ∩ {ω | firstHit α ω = n} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have : excursion α ω = stop ω := by
        ext i; simp only [excursion, h2, hstop, Nat.cast_withTop]; rw [untopA_min_coe]
      rwa [← this]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have : excursion α ω = stop ω := by
        ext i; simp only [excursion, h2, hstop, Nat.cast_withTop]; rw [untopA_min_coe]
      rwa [this]
  rw [this]
  exact (hstopm hS).inter ((isStoppingTime_firstHit hα).measurableSet_eq_of_countable n)

/-! ### The strong Markov property at the atom -/

/-- `P_y ∘ (θ¹)⁻¹ = P_{P(y, ·)}`. -/
theorem pathKernel_map_shift_one (P : Kernel X X) [IsMarkovKernel P] (y : X) :
    (pathKernel P y).map (shift 1) = pathMeasure P (P y) := by
  have := isMarkovKernel_pathKernel P
  have h := markov_measure P (Measure.dirac y) (n := 1) (G := univ) MeasurableSet.univ
  simp only [Measure.restrict_univ, pathMeasure_dirac] at h
  rw [h, pathKernel_map_coord, pow_one, pathMeasure_eq_comp]

/-- **The strong Markov property at `σ_α`** for an atom `α`, `a ∈ α`, `ν = P(a, ·)`: if `α` is
reached `P_μ`-a.s., then for `𝓕_{σ_α}`-measurable `F ≥ 0` and measurable `K ≥ 0`,
`E_μ[F · K(θ^{σ_α + 1}Φ)] = E_μ[F] · E_ν[K]`. -/
theorem lintegral_mul_restart (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤) {F : (ℕ → X) → ℝ≥0∞}
    (hF : Measurable[(isStoppingTime_firstHit hα.1).measurableSpace] F)
    {K : (ℕ → X) → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ ω, F ω * K (restart α ω) ∂pathMeasure P μ =
      (∫⁻ ω, F ω ∂pathMeasure P μ) * ∫⁻ ω, K ω ∂pathMeasure P (P a) := by
  have := isMarkovKernel_pathKernel P
  have hτ := isStoppingTime_firstHit (X := X) hα.1
  have hfull : (pathMeasure P μ).restrict {ω | firstHit α ω ≠ ⊤} = pathMeasure P μ :=
    Measure.restrict_eq_self_of_ae_mem hμ
  obtain ⟨ν, hν⟩ := hα.2
  have hKs : Measurable fun ω => K (shift 1 ω) := hK.comp (measurable_shift 1)
  have hsm := strong_markov_lintegral_mul P μ hτ hF hKs
  simp only [← restart_eq] at hsm
  rw [← hfull, hsm]
  have hconst : ∀ ω ∈ {ω | firstHit α ω ≠ ⊤},
      F ω * ∫⁻ ω', K (shift 1 ω') ∂pathKernel P (stoppedState (firstHit α) ω) =
        F ω * ∫⁻ ω, K ω ∂pathMeasure P (P a) := by
    intro ω hω
    have hmem : stoppedState (firstHit α) ω ∈ α :=
      hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := α) (n := 0) hω
    rw [← lintegral_map hK (measurable_shift 1), pathKernel_map_shift_one, hν _ hmem, hν a ha]
  rw [setLIntegral_congr_fun (measurableSet_ne_top hτ) hconst, lintegral_mul_const _
    (hF.mono hτ.measurableSpace_le le_rfl)]

/-! ### The law of the cycles -/

/-- The common law `ρ = P_ν ∘ excursion⁻¹` of the full cycles, `ν = P(a, ·)`. -/
noncomputable def cycleLaw (P : Kernel X X) [IsMarkovKernel P] (α : Set X) (a : X) :
    Measure (ℕ → X) :=
  (pathMeasure P (P a)).map (excursion α)

/-- `ρ` is a probability measure. -/
theorem isProbabilityMeasure_cycleLaw (P : Kernel X X) [IsMarkovKernel P] (α : Set X)
    (a : X) : IsProbabilityMeasure (cycleLaw P α a) := by
  have := isProbabilityMeasure_pathMeasure P (P a)
  unfold cycleLaw
  infer_instance

/-- `F = 1_{excursion ∈ t}` is `𝓕_{σ_α}`-measurable. -/
theorem measurable_stoppedField_indicator_excursion {α : Set X} (hα : MeasurableSet α)
    {t : Set (ℕ → X)} (ht : MeasurableSet t) :
    Measurable[(isStoppingTime_firstHit hα).measurableSpace]
      (fun ω => (excursion α ⁻¹' t).indicator (1 : (ℕ → X) → ℝ≥0∞) ω) :=
  Measurable.indicator (m := (isStoppingTime_firstHit hα).measurableSpace)
    (f := fun _ => (1 : ℝ≥0∞)) measurable_const (measurable_stoppedField_excursion hα ht)

/-- Under `P_ν` (`ν = P(a, ·)`, with `α` reached `P_ν`-a.s.), the cycles `cycle α j`, `j ≥ 0`,
are independent with common law `ρ`: `P_ν(cycle j ∈ tⱼ, j ≤ n) = Π_{j ≤ n} ρ(tⱼ)`. -/
theorem pathMeasure_cycles_box (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α)
    (hν : ∀ᵐ ω ∂pathMeasure P (P a), firstHit α ω ≠ ⊤) (n : ℕ) (t : ℕ → Set (ℕ → X))
    (ht : ∀ j, MeasurableSet (t j)) :
    pathMeasure P (P a) {ω | ∀ j ≤ n, cycle α j ω ∈ t j} =
      ∏ j ∈ Finset.range (n + 1), cycleLaw P α a (t j) := by
  have := isProbabilityMeasure_pathMeasure P (P a)
  induction n generalizing t with
  | zero =>
    have : {ω | ∀ j ≤ 0, cycle α j ω ∈ t j} = excursion α ⁻¹' t 0 := by
      ext ω; simp [cycle]
    rw [this, Finset.prod_range_one, cycleLaw, Measure.map_apply (measurable_excursion hα.1)
      (ht 0)]
  | succ n ih =>
    set G := {ω | ∀ j ≤ n, cycle α j ω ∈ t (j + 1)} with hG
    have hGm : MeasurableSet G := by
      have : G = ⋂ j ∈ Finset.range (n + 1), cycle α j ⁻¹' t (j + 1) := by
        ext ω; simp [hG]
      rw [this]
      exact Finset.measurableSet_biInter _ fun j _ => measurable_cycle hα.1 j (ht (j + 1))
    have hset : {ω | ∀ j ≤ n + 1, cycle α j ω ∈ t j} =
        excursion α ⁻¹' t 0 ∩ restart α ⁻¹' G := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, hG]
      constructor
      · intro h
        exact ⟨h 0 (Nat.zero_le _), fun j hj => by
          rw [← cycle_succ]; exact h (j + 1) (by omega)⟩
      · rintro ⟨h0, h⟩ j hj
        rcases j with _ | j
        · exact h0
        · rw [cycle_succ]; exact h j (by omega)
    have hpeel := lintegral_mul_restart P hα ha (P a) hν
      (measurable_stoppedField_indicator_excursion hα.1 (ht 0))
      (K := G.indicator 1) (measurable_one.indicator hGm)
    have hlhs : ∫⁻ ω, (excursion α ⁻¹' t 0).indicator (1 : (ℕ → X) → ℝ≥0∞) ω *
        G.indicator 1 (restart α ω) ∂pathMeasure P (P a) =
        pathMeasure P (P a) {ω | ∀ j ≤ n + 1, cycle α j ω ∈ t j} := by
      rw [hset, ← lintegral_indicator_one ((measurable_excursion hα.1 (ht 0)).inter
        (measurable_restart hα.1 hGm))]
      refine lintegral_congr fun ω => ?_
      by_cases h1 : ω ∈ excursion α ⁻¹' t 0 <;> by_cases h2 : restart α ω ∈ G <;>
        simp [h1, h2, indicator, mem_inter_iff]
    rw [← hlhs, hpeel, lintegral_indicator_one (measurable_excursion hα.1 (ht 0)),
      lintegral_indicator_one hGm, ih (fun j => t (j + 1)) (fun j => ht (j + 1)),
      Finset.prod_range_succ' _ (n + 1), cycleLaw,
      Measure.map_apply (measurable_excursion hα.1) (ht 0)]
    ring

/-- Under `P_μ` (with `α` reached `P_μ`-a.s.), `P_μ(cycle (j + 1) ∈ tⱼ, j ≤ n) =
P_ν(cycle j ∈ tⱼ, j ≤ n)`. -/
theorem pathMeasure_cycles_succ_box (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤) (n : ℕ) (t : ℕ → Set (ℕ → X))
    (ht : ∀ j, MeasurableSet (t j)) :
    pathMeasure P μ {ω | ∀ j ≤ n, cycle α (j + 1) ω ∈ t j} =
      pathMeasure P (P a) {ω | ∀ j ≤ n, cycle α j ω ∈ t j} := by
  have := isProbabilityMeasure_pathMeasure P μ
  set G := {ω | ∀ j ≤ n, cycle α j ω ∈ t j} with hG
  have hGm : MeasurableSet G := by
    have : G = ⋂ j ∈ Finset.range (n + 1), cycle α j ⁻¹' t j := by
      ext ω; simp [hG]
    rw [this]
    exact Finset.measurableSet_biInter _ fun j _ => measurable_cycle hα.1 j (ht j)
  have hset : {ω | ∀ j ≤ n, cycle α (j + 1) ω ∈ t j} = restart α ⁻¹' G := by
    ext ω; simp [hG, cycle_succ]
  have hpeel := lintegral_mul_restart P hα ha μ hμ (F := 1) measurable_const
    (K := G.indicator 1) (measurable_one.indicator hGm)
  simp only [Pi.one_apply, one_mul, lintegral_const, measure_univ, mul_one] at hpeel
  rw [hset, ← lintegral_indicator_one (measurable_restart hα.1 hGm),
    ← lintegral_indicator_one hGm, ← hpeel]
  rfl

/-- **The regeneration theorem** (MT p. 428): if `α` is an atom, `a ∈ α`, and `α` is reached
almost surely from `ν = P(a, ·)` and from `μ`, then under `P_μ` the full cycles
`(cycle α (j + 1))_{j ≥ 0}` are i.i.d. with law `ρ = cycleLaw P α a`. -/
theorem map_cycles_eq_infinitePi (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α)
    (hν : ∀ᵐ ω ∂pathMeasure P (P a), firstHit α ω ≠ ⊤) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤) :
    (pathMeasure P μ).map (fun ω j => cycle α (j + 1) ω) =
      Measure.infinitePi fun _ : ℕ => cycleLaw P α a := by
  have := isProbabilityMeasure_cycleLaw P α a
  have hΞ : Measurable fun ω j => cycle α (j + 1) ω :=
    measurable_pi_iff.2 fun j => measurable_cycle hα.1 (j + 1)
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  classical
  set n := s.sup id with hn
  set t' : ℕ → Set (ℕ → X) := fun j => if j ∈ s then t j else univ with ht'
  have ht'm : ∀ j, MeasurableSet (t' j) := fun j => by
    by_cases hj : j ∈ s <;> simp [ht', hj, ht j]
  have hsub : s ⊆ Finset.range (n + 1) := fun j hj =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  have hpi : Set.pi (s : Set ℕ) t = {f : ℕ → ℕ → X | ∀ j ≤ n, f j ∈ t' j} := by
    ext f
    simp only [Set.mem_pi, Finset.mem_coe, mem_ofPred_eq, ht']
    constructor
    · intro h j _
      by_cases hj : j ∈ s
      · simp only [hj, ite_true]; exact h j hj
      · simp only [hj, ite_false, mem_univ]
    · intro h j hj
      have := h j (Finset.le_sup (f := id) hj)
      simpa [hj] using this
  have hpim : MeasurableSet {f : ℕ → ℕ → X | ∀ j ≤ n, f j ∈ t' j} := by
    have : {f : ℕ → ℕ → X | ∀ j ≤ n, f j ∈ t' j} =
        ⋂ j ∈ Finset.range (n + 1), (fun f : ℕ → ℕ → X => f j) ⁻¹' t' j := by
      ext f; simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun j _ => measurable_pi_apply j (ht'm j)
  rw [Measure.map_apply hΞ (by rw [hpi]; exact hpim), hpi]
  have h1 : (fun ω j => cycle α (j + 1) ω) ⁻¹' {f : ℕ → ℕ → X | ∀ j ≤ n, f j ∈ t' j} =
      {ω | ∀ j ≤ n, cycle α (j + 1) ω ∈ t' j} := rfl
  rw [h1, pathMeasure_cycles_succ_box P hα ha μ hμ n t' ht'm,
    pathMeasure_cycles_box P hα ha hν n t' ht'm]
  rw [← Finset.prod_subset hsub (fun j _ hj => by simp [ht', hj])]
  refine Finset.prod_congr rfl fun j hj => ?_
  simp [ht', hj]

/-! ### Consequences: almost sure properties and the strong law for cycles -/

/-- An almost sure property of an i.i.d. `ρ`-sequence holds for the full cycles. -/
theorem ae_cycles_of_ae_infinitePi (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α)
    (hν : ∀ᵐ ω ∂pathMeasure P (P a), firstHit α ω ≠ ⊤) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤)
    {p : (ℕ → ℕ → X) → Prop}
    (h : ∀ᵐ s ∂Measure.infinitePi (fun _ : ℕ => cycleLaw P α a), p s) :
    ∀ᵐ ω ∂pathMeasure P μ, p fun j => cycle α (j + 1) ω := by
  have hΞ : Measurable fun ω j => cycle α (j + 1) ω :=
    measurable_pi_iff.2 fun j => measurable_cycle hα.1 (j + 1)
  rw [← map_cycles_eq_infinitePi P hα ha hν μ hμ] at h
  exact ae_of_ae_map hΞ.aemeasurable h

/-- **The strong law for cycle functionals**: for measurable `φ` integrable for `ρ`,
`(1/n) Σ_{j<n} φ(cycle (j + 1)) → ∫ φ dρ`, `P_μ`-a.s. -/
theorem tendsto_cycle_average (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α)
    (hν : ∀ᵐ ω ∂pathMeasure P (P a), firstHit α ω ≠ ⊤) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤)
    {φ : (ℕ → X) → ℝ} (hφm : Measurable φ) (hφi : Integrable φ (cycleLaw P α a)) :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, φ (cycle α (j + 1) ω)) / n)
      atTop (𝓝 (∫ e, φ e ∂cycleLaw P α a)) := by
  have := isProbabilityMeasure_cycleLaw P α a
  refine ae_cycles_of_ae_infinitePi P hα ha hν μ hμ
    (p := fun s => Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, φ (s j)) / n) atTop
      (𝓝 (∫ e, φ e ∂cycleLaw P α a))) ?_
  set Q := Measure.infinitePi fun _ : ℕ => cycleLaw P α a
  have hind : iIndepFun (fun j (s : ℕ → ℕ → X) => φ (s j)) Q :=
    iIndepFun_infinitePi (P := fun _ => cycleLaw P α a) (X := fun _ => φ) fun _ => hφm
  have hlaw : ∀ j, Q.map (fun s => s j) = cycleLaw P α a := fun j =>
    Measure.infinitePi_map_eval _ j
  have hident : ∀ j, IdentDistrib (fun s : ℕ → ℕ → X => φ (s j)) (fun s => φ (s 0)) Q Q :=
    fun j => ⟨(hφm.comp (measurable_pi_apply j)).aemeasurable,
      (hφm.comp (measurable_pi_apply 0)).aemeasurable, by
        rw [show (fun s : ℕ → ℕ → X => φ (s j)) = φ ∘ fun s => s j from rfl,
          show (fun s : ℕ → ℕ → X => φ (s 0)) = φ ∘ fun s => s 0 from rfl,
          ← Measure.map_map hφm (measurable_pi_apply j),
          ← Measure.map_map hφm (measurable_pi_apply 0), hlaw j, hlaw 0]⟩
  have hint0 : Integrable (fun s : ℕ → ℕ → X => φ (s 0)) Q := by
    have : Integrable φ (Q.map fun s => s 0) := by rw [hlaw 0]; exact hφi
    exact this.comp_measurable (measurable_pi_apply 0)
  have hmean : ∫ s, φ (s 0) ∂Q = ∫ e, φ e ∂cycleLaw P α a := by
    rw [← hlaw 0, integral_map (measurable_pi_apply 0).aemeasurable hφm.aestronglyMeasurable]
  have hsl := strong_law_ae_real (fun j (s : ℕ → ℕ → X) => φ (s j)) hint0
    (fun i j hij => hind.indepFun hij) hident
  rw [hmean] at hsl
  exact hsl

end MeynTweedie.LimitTheorems
