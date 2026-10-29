/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.GeometricErgodicTheorem
import GeneralizedDrift.SupermartingaleDrift
import GeneralizedDrift.HarrisDecomposition
import GeneralizedDrift.DriftHarris

/-!
# State-dependent drift criteria (MT §19.1.1)

Meyn and Tweedie, §19.1.1, pp. 482–487. A measurable `n : X → ℕ` gives the number of steps
after which the drift from `x` is examined.

**The embedded chain** (19.2)–(19.5), p. 483.
* `stateKernel P hn`: the kernel `P̂(x, ·) = P^{n(x)}(x, ·)` of (19.2).
* `embTime n k`: the iterates `s(0) = 0`, `s(k + 1) = s(k) + n(Φ_{s(k)})`; `embPath n ω` is the
  embedded path `Φ̂ₖ = Φ_{s(k)}` of (19.3).
* `isStoppingTime_embTime`: each `s(k)` is a stopping time; `embFilt`: the filtration
  `𝓕̂ₖ = 𝓕_{s(k)}`.
* `embPath_isMarkovChain`, `pathKernel_map_embPath`: by the strong Markov property, `Φ̂` is a
  Markov chain with kernel `P̂`, so the law of `Φ̂` under `P_x` is `P̂_x`.
* `embTime_eq_sum` (19.4): `s(k) = Σ_{j<k} n(Φ̂ⱼ)`; `firstReturn_le_embTime` (19.5): when
  `n ≥ 1`, `τ_C ≤ s(τ̂_C)`.

**Results.**
* **Theorem 19.1.1** (`theorem_19_1_1`, p. 484): `P̂V ≤ V` off a petite set `C`, for `V`
  unbounded off petite sets, gives Harris recurrence. `ae_hit_or_bdd` is the supermartingale step
  of the proof: almost surely the embedded chain enters `C` or `V(Φ̂ₖ)` stays bounded.
* **Theorem 19.1.2** (`theorem_19_1_2`, p. 485): `P̂V ≤ V − n + b 1_C` with `C` petite and `V`
  finite and bounded on `C` gives positive Harris recurrence and (19.11),
  `E_x[τ_C] ≤ V(x) + b 1_C(x)`; `meanReturnTime_le_stateDrift` is (19.11) alone (no
  irreducibility needed).
* **Theorem 19.1.3** (`theorem_19_1_3`, p. 486): `P̂V ≤ λ^{n} (V + b 1_C)` with `V ≥ 1` gives, for
  an aperiodic chain, positivity and (19.16), `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖ ≤ R V(x)`;
  `kendallMoment_le_stateDrift` is (19.19), `E_x[κ^{τ_C}] ≤ 2V(x) + 2b 1_C(x)` with `κ = λ⁻¹`.

**Hypotheses.** The book takes `n : X → ℤ₊ = {0, 1, …}`. The theorems need `n ≥ 1`: the
inequality `τ_C ≤ s(τ̂_C)` (19.5) fails where `n = 0`, since the embedded chain then stays put.
`n` is measurable, which the book uses implicitly (for `P̂` to be a kernel).

**Elsewhere.** The random walk on `ℝ²₊` (§19.1.2, Theorem 19.1.4) is in `OrthantWalk`; the
invasion/antibody model of §19.1.3, under a precise reading of (A1)–(A3) and (19.29), is in
`InvasionModel`.

**Corrections.**
* With `n = 0` allowed, Theorem 19.1.2 is false: `n ≡ 0`, `V ≡ 0`, `C = ∅` satisfy (19.10) on
  every chain, while `E_x[τ_∅] = ∞` (`theorem_19_1_2_counterexample`). In Theorem 19.1.1,
  `n ≡ 0` makes (19.6) an identity, so the hypothesis carries no information; the theorem is
  proved for `n ≥ 1`.
* Theorem 19.1.3 (19.16) is proved here for the norm `‖·‖ = ‖·‖_1`, the total variation norm the
  book uses; the bound is `R V(x)` with the `V` of (19.15).
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The kernel `P̂` -/

/-- The kernel `(m, x) ↦ Pᵐ(x, ·)` on `ℕ × X`. -/
noncomputable def powKernel (P : Kernel X X) : Kernel (ℕ × X) X where
  toFun p := (P ^ p.1) p.2
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    exact measurable_from_prod_countable_right (f := fun p : ℕ × X => (P ^ p.1) p.2 s)
      fun m => Kernel.measurable_coe (P ^ m) hs

/-- `(m, x) ↦ Pᵐ(x, ·)`. -/
theorem powKernel_apply (P : Kernel X X) (p : ℕ × X) : powKernel P p = (P ^ p.1) p.2 := rfl

/-- **The state-dependent kernel** (19.2), MT p. 483: `P̂(x, A) = P^{n(x)}(x, A)`. -/
noncomputable def stateKernel (P : Kernel X X) {n : X → ℕ} (hn : Measurable n) : Kernel X X :=
  (powKernel P).comap (fun x => (n x, x)) (hn.prodMk measurable_id)

/-- `P̂(x, ·) = P^{n(x)}(x, ·)`. -/
theorem stateKernel_apply (P : Kernel X X) {n : X → ℕ} (hn : Measurable n) (x : X) :
    stateKernel P hn x = (P ^ n x) x := rfl

/-- `P̂` is a Markov kernel. -/
theorem isMarkovKernel_stateKernel (P : Kernel X X) [IsMarkovKernel P] {n : X → ℕ}
    (hn : Measurable n) : IsMarkovKernel (stateKernel P hn) :=
  ⟨fun x => by
    have := isMarkovKernel_pow P (n x)
    rw [stateKernel_apply]
    infer_instance⟩

/-! ### The embedded times and path -/

/-- **The embedded times** (MT p. 483): `s(0) = 0` and `s(k + 1) = s(k) + n(Φ_{s(k)})`. -/
def embTime (n : X → ℕ) : ℕ → (ℕ → X) → ℕ
  | 0, _ => 0
  | k + 1, ω => embTime n k ω + n (ω (embTime n k ω))

/-- **The embedded path** (19.3), MT p. 483: `Φ̂ₖ = Φ_{s(k)}`. -/
def embPath (n : X → ℕ) (ω : ℕ → X) : ℕ → X := fun k => ω (embTime n k ω)

omit [MeasurableSpace X] in
/-- `s(0) = 0`. -/
theorem embTime_zero (n : X → ℕ) (ω : ℕ → X) : embTime n 0 ω = 0 := rfl

omit [MeasurableSpace X] in
/-- `s(k + 1) = s(k) + n(Φ̂ₖ)`. -/
theorem embTime_succ (n : X → ℕ) (k : ℕ) (ω : ℕ → X) :
    embTime n (k + 1) ω = embTime n k ω + n (embPath n ω k) := rfl

omit [MeasurableSpace X] in
/-- (19.4): `s(k) = Σ_{j<k} n(Φ̂ⱼ)`. -/
theorem embTime_eq_sum (n : X → ℕ) (k : ℕ) (ω : ℕ → X) :
    embTime n k ω = ∑ j ∈ Finset.range k, n (embPath n ω j) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [embTime_succ, ih, Finset.sum_range_succ]

omit [MeasurableSpace X] in
/-- `Φ̂₀ = Φ₀`. -/
theorem embPath_zero (n : X → ℕ) (ω : ℕ → X) : embPath n ω 0 = ω 0 := rfl

omit [MeasurableSpace X] in
/-- When `n ≥ 1`, `s(k) ≥ k`. -/
theorem le_embTime {n : X → ℕ} (hn1 : ∀ x, 1 ≤ n x) (k : ℕ) (ω : ℕ → X) : k ≤ embTime n k ω := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [embTime_succ]; have := hn1 (embPath n ω k); omega

/-- `{s(k) = m} ∈ 𝓕_m^Φ`. -/
theorem measurableSet_embTime_eq {n : X → ℕ} (hn : Measurable n) (k m : ℕ) :
    MeasurableSet[natFilt (X := X) m] {ω | embTime n k ω = m} := by
  induction k generalizing m with
  | zero =>
    by_cases hm : m = 0
    · subst hm
      have : {ω : ℕ → X | embTime n 0 ω = 0} = univ := by ext ω; simp [embTime_zero]
      rw [this]; exact @MeasurableSet.univ _ (natFilt (X := X) 0)
    · have : {ω : ℕ → X | embTime n 0 ω = m} = ∅ := by
        ext ω; simp [embTime_zero, Ne.symm hm]
      rw [this]; exact @MeasurableSet.empty _ (natFilt (X := X) m)
  | succ k ih =>
    have hset : {ω : ℕ → X | embTime n (k + 1) ω = m} =
        ⋃ j ∈ Finset.range (m + 1), ({ω | embTime n k ω = j} ∩ {ω | n (ω j) = m - j}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, mem_inter_iff, exists_prop]
      constructor
      · intro h
        refine ⟨embTime n k ω, by rw [embTime_succ] at h; omega, rfl, ?_⟩
        rw [embTime_succ] at h
        change n (embPath n ω k) = m - embTime n k ω
        omega
      · rintro ⟨j, hj, hk, hn'⟩
        rw [embTime_succ]
        change embTime n k ω + n (ω (embTime n k ω)) = m
        rw [hk, hn']
        omega
    rw [hset]
    refine Finset.measurableSet_biUnion _ fun j hj => ?_
    have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
    exact ((natFilt (X := X)).mono hjm _ (ih j)).inter
      (measurableSet_coord_natFilt hjm (hn (measurableSet_singleton (m - j))))

/-- **Each `s(k)` is a stopping time** (MT p. 483). -/
theorem isStoppingTime_embTime {n : X → ℕ} (hn : Measurable n) (k : ℕ) :
    IsStoppingTime (natFilt (X := X)) fun ω => ((embTime n k ω : ℕ) : WithTop ℕ) := by
  intro i
  change MeasurableSet[natFilt (X := X) i] {ω : ℕ → X | ((embTime n k ω : ℕ) : WithTop ℕ) ≤ i}
  have hset : {ω : ℕ → X | ((embTime n k ω : ℕ) : WithTop ℕ) ≤ i} =
      ⋃ m ∈ Finset.range (i + 1), {ω | embTime n k ω = m} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop, exists_eq_right']
    norm_cast
    omega
  rw [hset]
  exact Finset.measurableSet_biUnion _ fun m hm =>
    (natFilt (X := X)).mono (Nat.le_of_lt_succ (Finset.mem_range.1 hm)) _
      (measurableSet_embTime_eq hn k m)

omit [MeasurableSpace X] in
/-- The embedded times increase. -/
theorem embTime_mono (n : X → ℕ) (ω : ℕ → X) : Monotone fun k => embTime n k ω :=
  monotone_nat_of_le_succ fun k => by rw [embTime_succ]; exact Nat.le_add_right _ _

/-- **The filtration `𝓕̂ₖ = 𝓕_{s(k)}`** of the embedded chain (MT p. 483). -/
noncomputable def embFilt {n : X → ℕ} (hn : Measurable n) :
    Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → X)) where
  seq k := (isStoppingTime_embTime hn k).measurableSpace
  mono' _ _ hij := IsStoppingTime.measurableSpace_mono _ _ fun ω =>
    WithTop.coe_le_coe.2 (embTime_mono n ω hij)
  le' k := (isStoppingTime_embTime hn k).measurableSpace_le

/-- `Φ̂ₖ = Φ_{s(k)}` is `𝓕_{s(k)}`-measurable. -/
theorem measurable_embPath_embFilt {n : X → ℕ} (hn : Measurable n) (k : ℕ) :
    Measurable[embFilt hn k] fun ω : ℕ → X => embPath n ω k := by
  intro A hA
  change MeasurableSet[(isStoppingTime_embTime hn k).measurableSpace] _
  rw [measurableSet_stoppedField_iff]
  have hpre : ∀ m : ℕ, (fun ω : ℕ → X => embPath n ω k) ⁻¹' A ∩
      {ω | ((embTime n k ω : ℕ) : WithTop ℕ) = m} =
      {ω | ω m ∈ A} ∩ {ω | embTime n k ω = m} := fun m => by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, Nat.cast_inj, embPath]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2 ▸ h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2.symm ▸ h1, h2⟩
  refine ⟨?_, fun m => ?_⟩
  · have : (fun ω : ℕ → X => embPath n ω k) ⁻¹' A =
        ⋃ m : ℕ, ({ω | ω m ∈ A} ∩ {ω | embTime n k ω = m}) := by
      ext ω
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq, embPath]
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨m, h1, h2⟩ => h2 ▸ h1⟩
    rw [this]
    exact MeasurableSet.iUnion fun m => (measurable_pi_apply m hA).inter
      ((natFilt (X := X)).le m _ (measurableSet_embTime_eq hn k m))
  · rw [hpre]
    exact (measurable_coord_natFilt m hA).inter (measurableSet_embTime_eq hn k m)

/-- The embedded path is measurable. -/
theorem measurable_embPath {n : X → ℕ} (hn : Measurable n) :
    Measurable (embPath (X := X) n) :=
  measurable_pi_iff.2 fun k => (measurable_embPath_embFilt hn k).mono
    ((embFilt hn).le k) le_rfl

/-- `E_y[f(Φ_{n(Φ₀)})] = P^{n(y)} f(y)`: under `P_y`, `Φ₀ = y` almost surely. -/
theorem lintegral_pathKernel_stateTime (P : Kernel X X) [IsMarkovKernel P] {n : X → ℕ}
    (hn : Measurable n) {f : X → ℝ≥0∞} (hf : Measurable f) (y : X) :
    ∫⁻ ω, f (ω (n (ω 0))) ∂pathKernel P y = ∫⁻ z, f z ∂stateKernel P hn y := by
  have := isMarkovKernel_pathKernel P
  have hnull : pathKernel P y {ω | ω 0 ∈ n ⁻¹' {n y}ᶜ} = 0 := by
    rw [pathKernel_zero_mem P y (hn (measurableSet_singleton _).compl),
      indicator_of_notMem (by simp)]
  have hae : (fun ω : ℕ → X => f (ω (n (ω 0)))) =ᵐ[pathKernel P y] fun ω => f (ω (n y)) := by
    refine measure_eq_zero_iff_ae_notMem.1 hnull |>.mono fun ω hω => ?_
    simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff, mem_singleton_iff, not_not] at hω
    change f (ω (n (ω 0))) = f (ω (n y))
    rw [hω]
  rw [lintegral_congr_ae hae, ← lintegral_map hf (measurable_pi_apply (n y)),
    pathKernel_map_coord, stateKernel_apply]

/-- **The embedded chain is a Markov chain with kernel `P̂`** (19.3), MT p. 483, by the strong
Markov property at the times `s(k)`. -/
theorem embPath_isMarkovChain (P : Kernel X X) [IsMarkovKernel P] {n : X → ℕ}
    (hn : Measurable n) (μ : Measure X) [IsProbabilityMeasure μ] :
    IsMarkovChain (stateKernel P hn) μ (pathMeasure P μ) fun k ω => embPath n ω k := by
  refine isMarkovChain_of_step (𝓖 := embFilt hn) _ μ (measurable_embPath_embFilt hn)
    (by simpa [embPath, embTime_zero] using pathMeasure_map_zero P μ) fun k G hG f hf => ?_
  have hτ := isStoppingTime_embTime (X := X) hn k
  have hH : Measurable fun ω : ℕ → X => f (ω (n (ω 0))) := by
    refine measurable_from_prod_countable_right (f := fun p : ℕ × (ℕ → X) => f (p.2 p.1))
      (fun m => hf.comp (measurable_pi_apply m)) |>.comp
      ((hn.comp (measurable_pi_apply 0)).prodMk measurable_id)
  have hfin : {ω : ℕ → X | ((embTime n k ω : ℕ) : WithTop ℕ) ≠ ⊤} = univ := by
    ext ω; simp
  have h := strong_markov_lintegral P μ hτ (A := G) hG hH
  rw [hfin, inter_univ] at h
  have e1 : ∀ ω : ℕ → X, f (shiftAt (fun ω => ((embTime n k ω : ℕ) : WithTop ℕ)) ω
      (n (shiftAt (fun ω => ((embTime n k ω : ℕ) : WithTop ℕ)) ω 0))) =
      f (embPath n ω (k + 1)) := fun ω => by
    rw [shiftAt_of_eq (n := embTime n k ω) rfl]
    simp only [shift, add_zero, embPath, embTime_succ]
  have e2 : ∀ ω : ℕ → X, stoppedState (fun ω => ((embTime n k ω : ℕ) : WithTop ℕ)) ω =
      embPath n ω k := fun ω => by
    rw [stoppedState_of_eq (n := embTime n k ω) rfl]; rfl
  simp_rw [e1, e2, lintegral_pathKernel_stateTime P hn hf] at h
  exact h

/-- **The law of the embedded chain** (MT p. 483): under `P_x`, `Φ̂` has law `P̂_x`. -/
theorem pathKernel_map_embPath (P : Kernel X X) [IsMarkovKernel P] {n : X → ℕ}
    (hn : Measurable n) (x : X) :
    haveI := isMarkovKernel_stateKernel P hn
    (pathKernel P x).map (embPath n) = pathKernel (stateKernel P hn) x := by
  have := isMarkovKernel_stateKernel P hn
  have h := law_eq_pathMeasure (stateKernel P hn) (Measure.dirac x)
    (embPath_isMarkovChain P hn (Measure.dirac x))
  rw [pathMeasure_dirac, pathMeasure_dirac] at h
  exact h

/-! ### Hitting times of the embedded chain -/

omit [MeasurableSpace X] in
/-- (19.5): if `n ≥ 1` and `Φ̂ₖ ∈ C` for some `k ≥ 1`, then `τ_C ≤ s(k)`. -/
theorem firstReturn_le_embTime {n : X → ℕ} (hn1 : ∀ x, 1 ≤ n x) {C : Set X} {ω : ℕ → X}
    {k : ℕ} (hk : 1 ≤ k) (hC : embPath n ω k ∈ C) :
    firstReturn C ω ≤ ((embTime n k ω : ℕ) : WithTop ℕ) :=
  hittingAfter_le_of_mem (le_trans hk (le_embTime hn1 k ω)) hC

omit [MeasurableSpace X] in
/-- If the embedded chain returns to `C` at the index `k`, then `k ≥ 1` and `Φ̂ₖ ∈ C`. -/
theorem embPath_mem_of_firstReturn_eq {n : X → ℕ} {C : Set X} {ω : ℕ → X} {k : ℕ}
    (h : firstReturn C (embPath n ω) = k) : 1 ≤ k ∧ embPath n ω k ∈ C := by
  have hk : 1 ≤ k := by
    have := one_le_firstReturn C (embPath n ω)
    rw [h] at this
    exact WithTop.coe_le_coe.1 this
  refine ⟨hk, ?_⟩
  have h' : firstReturn C (embPath n ω) = WithTop.some (k - 1 + 1) := by
    rw [h, show k - 1 + 1 = k by omega]; rfl
  have := ((firstReturn_eq_iff C (embPath n ω) (k - 1)).1 h').2
  rwa [show k - 1 + 1 = k by omega] at this

omit [MeasurableSpace X] in
/-- (19.5) for return times: when `n ≥ 1`, `τ_C ≤ s(τ̂_C) = Σ_{k<τ̂_C} n(Φ̂ₖ)`, where `τ̂_C` is
the return time of the embedded path. -/
theorem toENNReal_firstReturn_le_sumBefore {n : X → ℕ} (hn1 : ∀ x, 1 ≤ n x) (C : Set X)
    (ω : ℕ → X) :
    ENat.toENNReal (firstReturn C ω) ≤
      sumBefore (firstReturn C) (fun k ω' => (n (ω' k) : ℝ≥0∞)) (embPath n ω) := by
  cases h : firstReturn C (embPath n ω) with
  | top =>
    rw [sumBefore_eq_of_eq (τ' := fun _ => (⊤ : WithTop ℕ)) h, sumBefore_top_eq]
    have htop : ∑' k : ℕ, (n (embPath n ω k) : ℝ≥0∞) = ∞ := by
      refine top_le_iff.1 ?_
      rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) one_ne_zero]
      exact ENNReal.tsum_le_tsum fun k => by exact_mod_cast hn1 (embPath n ω k)
    rw [htop]; exact le_top
  | coe k =>
    obtain ⟨hk, hkC⟩ := embPath_mem_of_firstReturn_eq h
    rw [sumBefore_of_eq' h]
    have hle := firstReturn_le_embTime hn1 hk hkC
    calc ENat.toENNReal (firstReturn C ω) ≤ ENat.toENNReal ((embTime n k ω : ℕ) : WithTop ℕ) :=
          ENat.toENNReal_le.2 hle
      _ = ∑ j ∈ Finset.range k, (n (embPath n ω j) : ℝ≥0∞) := by
          change ENat.toENNReal ((embTime n k ω : ℕ) : ℕ∞) = _
          rw [ENat.toENNReal_coe, embTime_eq_sum, Nat.cast_sum]

/-! ### Theorem 19.1.2 -/

/-- **(19.11)** (MT p. 485): if `n ≥ 1` and `P̂V + n ≤ V + b 1_C` (19.10), then
`E_x[τ_C] ≤ V(x) + b 1_C(x)` for every `x`. The proof is the book's: (19.13) for the embedded
chain with `f = n` gives (19.14), `E_x[s(τ̂_C)] ≤ V(x) + b 1_C(x)`, and `τ_C ≤ s(τ̂_C)`. -/
theorem meanReturnTime_le_stateDrift (P : Kernel X X) [IsMarkovKernel P] {n : X → ℕ}
    (hn : Measurable n) (hn1 : ∀ x, 1 ≤ n x) {V : X → ℝ≥0∞} (hV : Measurable V) {b : ℝ≥0∞}
    {C : Set X} (hC : MeasurableSet C)
    (h : ∀ x, ∫⁻ y, V y ∂(P ^ n x) x + n x ≤ V x + C.indicator (fun _ => b) x) (x : X) :
    meanReturnTime P C x ≤ V x + C.indicator (fun _ => b) x := by
  have := isMarkovKernel_stateKernel P hn
  have hnm : Measurable fun y => (n y : ℝ≥0∞) := measurable_from_nat.comp hn
  have h14 := (proposition_11_3_3 (stateKernel P hn) hC (z := fun _ => V)
    (ε := fun _ y => (n y : ℝ≥0∞)) (c := 1) (fun _ => hV) (fun _ => hnm)
    (fun _ _ _ => by rw [one_mul]) (fun _ y hy => by
      have := h y
      rw [indicator_of_notMem hy, add_zero] at this
      rwa [stateKernel_apply])).2 x
  have hS : Measurable (sumBefore (firstReturn C) fun k (ω' : ℕ → X) => (n (ω' k) : ℝ≥0∞)) :=
    measurable_sumBefore (measurableSet_lt_firstReturn hC) fun k =>
      hnm.comp (measurable_pi_apply k)
  calc meanReturnTime P C x = ∫⁻ ω, ENat.toENNReal (firstReturn C ω) ∂pathKernel P x := rfl
    _ ≤ ∫⁻ ω, sumBefore (firstReturn C) (fun k ω' => (n (ω' k) : ℝ≥0∞)) (embPath n ω)
          ∂pathKernel P x := lintegral_mono fun ω => toENNReal_firstReturn_le_sumBefore hn1 C ω
    _ = ∫⁻ ω', sumBefore (firstReturn C) (fun k ω' => (n (ω' k) : ℝ≥0∞)) ω'
          ∂pathKernel (stateKernel P hn) x := by
        rw [← pathKernel_map_embPath P hn x, lintegral_map hS (measurable_embPath hn)]
    _ ≤ n x + 1 * ∫⁻ y, V y ∂stateKernel P hn x := h14
    _ ≤ V x + C.indicator (fun _ => b) x := by
        rw [one_mul, add_comm, stateKernel_apply]; exact h x

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 19.1.2** (MT p. 485): for a `ψ`-irreducible chain, a measurable `n : X → ℕ` with
`n ≥ 1`, a petite set `C`, a finite `V ≥ 0` bounded on `C` and `b < ∞` with
`∫ P^{n(x)}(x, dy) V(y) ≤ V(x) − n(x) + b 1_C(x)` (19.10), the chain is positive Harris
recurrent and `E_x[τ_C] ≤ V(x) + b 1_C(x)` (19.11). The positivity step is the book's: (19.11)
with `V` bounded on the petite set `C` is the regularity criterion of Theorem 10.4.10. -/
theorem theorem_19_1_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {n : X → ℕ} (hn : Measurable n) (hn1 : ∀ x, 1 ≤ n x)
    {V : X → ℝ≥0∞} (hV : Measurable V) (hfin : ∀ x, V x ≠ ∞) {b : ℝ≥0∞} (hb : b ≠ ∞)
    {C : Set X} (hC : IsPetite P C) {M : ℝ≥0∞} (hM : M ≠ ∞) (hVC : ∀ x ∈ C, V x ≤ M)
    (h : ∀ x, ∫⁻ y, V y ∂(P ^ n x) x + n x ≤ V x + C.indicator (fun _ => b) x) :
    IsPositiveHarris P ψ ∧ ∀ x, meanReturnTime P C x ≤ V x + C.indicator (fun _ => b) x := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have h11 := meanReturnTime_le_stateDrift P hn hn1 hV hCm h
  refine ⟨?_, h11⟩
  have hbound : ∀ x, meanReturnTime P C x ≠ ∞ := fun x =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin x, by
      by_cases hx : x ∈ C <;> simp [hx, hb]⟩) (h11 x)
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    exact hψ.1 (Measure.eq_zero_of_isEmpty ψ)
  have hne := nonempty_of_meanReturnTime_ne_top hCm (hbound x₀)
  have hL : ∀ y ∈ C, hitProb P C y = 1 := fun y _ =>
    hitProb_eq_one_of_meanReturnTime_ne_top hCm (hbound y)
  have hψC := (theorem_8_3_6_i P hψ hC hne hL).2
  have hsup : ∀ y ∈ C, meanReturnTime P C y ≤ M + b := fun y hy =>
    (h11 y).trans (by rw [indicator_of_mem hy]; exact add_le_add (hVC y hy) le_rfl)
  exact (theorem_10_4_10_ii hψ hC hψC (ENNReal.add_ne_top.2 ⟨hM, hb⟩) hsup).2.2 hbound

/-- **The case `n = 0` in Theorem 19.1.2** (correction): with `n ≡ 0`, `V ≡ 0`, `b = 1` and the
petite set `C = ∅`, (19.10) holds on the one-point chain, but `E_x[τ_∅] = ∞`, so (19.11) fails.
Hence the theorem needs `n ≥ 1`, not `n ∈ ℤ₊`. -/
theorem theorem_19_1_2_counterexample :
    let P : Kernel Unit Unit := Kernel.id
    IsPetite P (∅ : Set Unit) ∧
      (∀ x, ∫⁻ _y, (0 : ℝ≥0∞) ∂(P ^ (0 : ℕ)) x + ((0 : ℕ) : ℝ≥0∞) ≤
        0 + (∅ : Set Unit).indicator (fun _ => 1) x) ∧
      ∀ x, ¬ meanReturnTime P (∅ : Set Unit) x ≤ 0 + (∅ : Set Unit).indicator (fun _ => 1) x := by
  intro P
  refine ⟨⟨diracDist 1, Measure.dirac (), MeasurableSet.empty, isSamplingDist_diracDist 1,
    by simp, fun x hx => absurd hx (notMem_empty x)⟩, fun x => by simp, fun x => ?_⟩
  have htop : ∀ ω : ℕ → Unit, firstReturn (∅ : Set Unit) ω = ⊤ := fun ω => by
    by_contra hne
    obtain ⟨k, -, hk⟩ := (firstReturn_ne_top_iff ∅ ω).1 hne
    exact notMem_empty _ hk
  have := isMarkovKernel_pathKernel P
  have h' : ∀ ω : ℕ → Unit, ENat.toENNReal (firstReturn (∅ : Set Unit) ω) = ∞ := fun ω => by
    rw [htop]; rfl
  rw [meanReturnTime]
  simp_rw [h']
  simp

/-! ### Theorem 19.1.1 -/

/-- **The supermartingale step of Theorem 19.1.1** (MT p. 485): if `P̂V ≤ V` off `C`, then
`P_x`-almost surely either the embedded chain enters `C` or `V(Φ̂ₖ)` stays bounded. The proof is
the book's: `V(Φ̂ₖ) 1{σ̂_C ≥ k}` is a nonnegative supermartingale for the embedded chain. -/
theorem ae_hit_or_bdd (P : Kernel X X) [IsMarkovKernel P] {n : X → ℕ} (hn : Measurable n)
    {V : X → ℝ≥0} (hV : Measurable V) {C : Set X} (hC : MeasurableSet C)
    (h : ∀ x ∉ C, ∫⁻ y, (V y : ℝ≥0∞) ∂(P ^ n x) x ≤ V x) (x : X) :
    ∀ᵐ ω ∂pathKernel P x, (∀ i, embPath n ω i ∉ C) →
      ∃ r : ℝ, ∀ k, (V (embPath n ω k) : ℝ) ≤ r := by
  have := isMarkovKernel_stateKernel P hn
  have h1 := ae_bddAbove_of_avoid (stateKernel P hn) (Measure.dirac x) hV hC
    (fun y hy => by rw [stateKernel_apply]; exact h y hy)
    (by
      rw [lintegral_dirac' x (f := fun y => (V y : ℝ≥0∞)) (measurable_coe_nnreal_ennreal.comp hV)]
      exact ENNReal.coe_ne_top)
  rw [pathMeasure_dirac, ← pathKernel_map_embPath P hn x] at h1
  exact ae_of_ae_map (measurable_embPath hn).aemeasurable h1

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 19.1.1** (MT p. 484): for a `ψ`-irreducible chain, a measurable `n : X → ℕ` with
`n ≥ 1`, a petite set `C` and `V : X → ℝ₊` unbounded off petite sets (every `{V ≤ m}` petite)
with `∫ P^{n(x)}(x, dy) V(y) ≤ V(x)` for `x ∉ C` (19.6), the chain is Harris recurrent.

The proof follows the book's supermartingale argument (`ae_hit_or_bdd`): almost surely the
embedded chain enters `C`, or it stays in some petite `{V ≤ m}` at the infinitely many times
`s(k)`, and then (Theorem 9.1.3) the chain enters `C ∪ {V ≤ n₀} ∈ B⁺(X)`. So
`P_y(σ_{C'} < ∞) = 1` everywhere, and the petite set `C'` gives Harris recurrence
(Proposition 9.1.7). This replaces the book's case analysis through Theorems 8.3.5 and 9.0.1. -/
theorem theorem_19_1_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {n : X → ℕ} (hn : Measurable n) (hn1 : ∀ x, 1 ≤ n x)
    {C : Set X} (hC : IsPetite P C) {V : X → ℝ≥0} (hVm : Measurable V)
    (hpet : ∀ m : ℕ, IsPetite P {x | V x ≤ m})
    (hdrift : ∀ x ∉ C, ∫⁻ y, (V y : ℝ≥0∞) ∂(P ^ n x) x ≤ V x) : IsHarris P ψ := by
  have := isMarkovKernel_pathKernel P
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hcov : (⋃ m : ℕ, {x | V x ≤ m}) = univ := by
    ext x; simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    obtain ⟨m, hm⟩ := exists_nat_ge (V x)
    exact ⟨m, hm⟩
  have hψu : 0 < ψ (⋃ m : ℕ, {x | V x ≤ m}) := by
    rw [hcov]; exact pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨n₀, hn₀⟩ := exists_measure_pos_of_iUnion hψu
  set C' := C ∪ {x | V x ≤ n₀} with hC'
  have hC'm : MeasurableSet C' := hCm.union (hVm measurableSet_Iic)
  have hC'pet : IsPetite P C' := proposition_5_5_5_ii P hψ hC (hpet n₀)
  have hψC' : 0 < ψ C' := hn₀.trans_le (measure_mono subset_union_right)
  -- every `{V ≤ m}` reaches `C'` with probability bounded below
  have hreach : ∀ m : ℕ, ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ y ∈ {x | V x ≤ m}, δ ≤ hitProbZero P C' y := by
    intro m
    obtain ⟨δ, hδ, hge⟩ := IsPetite.hitProb_ge P hψ.2.1 (hpet m) hC'm hψC'
    refine ⟨min δ 1, lt_min hδ one_pos, fun y hy => ?_⟩
    by_cases hyC : y ∈ C'
    · rw [hitProbZero_of_mem P hC'm hyC]; exact min_le_right _ _
    · exact (min_le_left _ _).trans ((hge y hy hyC).trans (hitProb_le_hitProbZero P C' y))
  -- `P_y(σ_{C'} < ∞) = 1` for every `y`
  have hzero : ∀ y, hitProbZero P C' y = 1 := by
    intro y
    have hio : ∀ᵐ ω ∂pathKernel P y, ∀ m : ℕ, ω ∈ ioSet {x | V x ≤ m} → ω ∈ ioSet C' := by
      rw [ae_all_iff]
      intro m
      obtain ⟨δ, hδ, hD⟩ := hreach m
      have := theorem_9_1_3_ae P (Measure.dirac y) hC'm hδ hD
      rwa [pathMeasure_dirac] at this
    have hbd := ae_hit_or_bdd P hn hVm hCm hdrift y
    have hae : ∀ᵐ ω ∂pathKernel P y, firstHit C' ω ≠ ⊤ := by
      filter_upwards [hio, hbd] with ω hio hbd
      have hhit : ∀ k, ω k ∈ C' → firstHit C' ω ≠ ⊤ := fun k hk =>
        ne_top_of_le_ne_top WithTop.coe_ne_top (hittingAfter_le_of_mem (Nat.zero_le k) hk)
      by_cases hav : ∀ i, embPath n ω i ∉ C
      · obtain ⟨r, hr⟩ := hbd hav
        obtain ⟨m, hm⟩ := exists_nat_ge r
        have hiom : ω ∈ ioSet {x | V x ≤ m} := fun N =>
          ⟨embTime n N ω, le_embTime hn1 N ω, by
            change V (embPath n ω N) ≤ (m : ℝ≥0)
            exact_mod_cast (hr N).trans hm⟩
        obtain ⟨k, -, hk⟩ := hio m hiom 0
        exact hhit k hk
      · push Not at hav
        obtain ⟨i, hi⟩ := hav
        exact hhit _ (Or.inl hi)
    have hmeas : MeasurableSet {ω : ℕ → X | firstHit C' ω ≠ ⊤} :=
      measurableSet_ne_top (proposition_3_4_4 hC'm).2
    rw [hitProbZero, ← measure_univ (μ := pathKernel P y)]
    exact (ae_iff_measure_eq hmeas.nullMeasurableSet).1 hae
  -- hence `L(x, C') = 1` for every `x`
  have hL : ∀ x, hitProb P C' x = 1 := by
    intro x
    have hmeas : MeasurableSet {ω : ℕ → X | firstHit C' ω ≠ ⊤} :=
      measurableSet_ne_top (proposition_3_4_4 hC'm).2
    refine le_antisymm (hitProb_le_one P C' x) ?_
    have := isMarkovKernel_pow P 1
    calc (1 : ℝ≥0∞) = ∫⁻ y, hitProbZero P C' y ∂(P ^ 1) x := by simp_rw [hzero]; simp
      _ = ∫⁻ y, pathKernel P y {ω | firstHit C' ω ≠ ⊤} ∂(P ^ 1) x := rfl
      _ = pathKernel P x (shift 1 ⁻¹' {ω | firstHit C' ω ≠ ⊤}) :=
          (pathKernel_shift_preimage P x 1 hmeas).symm
      _ ≤ hitProb P C' x := by
          refine measure_mono fun ω hω => ?_
          simp only [mem_preimage, mem_ofPred_eq] at hω
          obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.1 hω
          have hmem := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n)
            (s := C') (n := 0) (ω := shift 1 ω) hω
          rw [← firstHit, ← hj] at hmem
          change ω (1 + j) ∈ C' at hmem
          exact (firstReturn_ne_top_iff C' ω).2 ⟨1 + j, by omega, hmem⟩
  exact proposition_9_1_7_ii hψ hC'pet hL

/-! ### Theorem 19.1.3 -/

/-- The partial sums `S_k(ω) = Σ_{j<k} n(ω_j)` along a path; on the embedded path they are the
times `s(k)` (`embTime_eq_sum`). -/
def partialN (n : X → ℕ) (k : ℕ) (ω : ℕ → X) : ℕ := ∑ j ∈ Finset.range k, n (ω j)

/-- The increments `κ^{S_{k+1}} − κ^{S_k} = κ^{S_k} (κ^{n(ω_k)} − 1)` of the proof of
Theorem 19.1.3. -/
noncomputable def geoIncr (n : X → ℕ) (κ : ℝ≥0∞) (k : ℕ) (ω : ℕ → X) : ℝ≥0∞ :=
  κ ^ partialN n k ω * (κ ^ n (ω k) - 1)

/-- `κ^{S_k}` is `𝓕_m^Φ`-measurable for `k ≤ m + 1`. -/
theorem measurable_pow_partialN {n : X → ℕ} (hn : Measurable n) (κ : ℝ≥0∞) {k m : ℕ}
    (hkm : k ≤ m + 1) : Measurable[natFilt (X := X) m] fun ω : ℕ → X => κ ^ partialN n k ω := by
  have : (fun ω : ℕ → X => κ ^ partialN n k ω) = fun ω => ∏ j ∈ Finset.range k, κ ^ n (ω j) := by
    funext ω; rw [partialN, Finset.prod_pow_eq_pow_sum]
  rw [this]
  refine Finset.measurable_prod _ fun j hj => ?_
  have hjm : j ≤ m := by have := Finset.mem_range.1 hj; omega
  exact measurable_from_nat.comp (hn.comp ((measurable_coord_natFilt j).mono
    ((natFilt (X := X)).mono hjm) le_rfl))

/-- `κ^{S_k}` is measurable. -/
theorem measurable_pow_partialN' {n : X → ℕ} (hn : Measurable n) (κ : ℝ≥0∞) (k : ℕ) :
    Measurable fun ω : ℕ → X => κ ^ partialN n k ω :=
  (measurable_pow_partialN hn κ (m := k) (by omega)).mono ((natFilt (X := X)).le k) le_rfl

/-- The increments `geoIncr` are measurable. -/
theorem measurable_geoIncr {n : X → ℕ} (hn : Measurable n) (κ : ℝ≥0∞) (k : ℕ) :
    Measurable (geoIncr (X := X) n κ k) :=
  (measurable_pow_partialN' hn κ k).mul ((measurable_from_nat (f := fun m : ℕ => κ ^ m - 1)).comp
    (hn.comp (measurable_pi_apply k)))

omit [MeasurableSpace X] in
/-- The increments telescope: `1 + Σ_{k<t} (κ^{S_{k+1}} − κ^{S_k}) = κ^{S_t}`. -/
theorem one_add_sum_geoIncr {κ : ℝ≥0∞} (hκ : 1 ≤ κ) (n : X → ℕ) (ω : ℕ → X) (t : ℕ) :
    1 + ∑ k ∈ Finset.range t, geoIncr n κ k ω = κ ^ partialN n t ω := by
  induction t with
  | zero => simp [partialN]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    have h1 : 1 ≤ κ ^ n (ω t) := one_le_pow₀ hκ
    calc κ ^ partialN n t ω + geoIncr n κ t ω = κ ^ partialN n t ω * (1 + (κ ^ n (ω t) - 1)) := by
          rw [geoIncr, mul_add, mul_one]
      _ = κ ^ partialN n (t + 1) ω := by
          rw [add_tsub_cancel_of_le h1]
          simp only [partialN, Finset.sum_range_succ, pow_add]

omit [MeasurableSpace X] in
/-- `σ_A ≤ τ_A`. -/
theorem firstHit_le_firstReturn' (A : Set X) (ω : ℕ → X) : firstHit A ω ≤ firstReturn A ω := by
  cases h : firstReturn A ω with
  | top => exact le_top
  | coe m =>
    have hmem := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := A)
      (n := 1) (ω := ω) (by rw [← firstReturn, h]; exact WithTop.coe_ne_top)
    rw [← firstReturn, h] at hmem
    exact hittingAfter_le_of_mem (Nat.zero_le m) hmem

omit [MeasurableSpace X] in
/-- (19.5) for generating functions: when `n ≥ 1` and `κ > 1`,
`κ^{τ_C} ≤ κ^{s(τ̂_C)} = 1 + Σ_{k<τ̂_C} (κ^{s(k+1)} − κ^{s(k)})`. -/
theorem tpow_firstReturn_le {n : X → ℕ} (hn1 : ∀ x, 1 ≤ n x) {κ : ℝ≥0∞} (hκ : 1 < κ)
    (C : Set X) (ω : ℕ → X) :
    tpow κ (firstReturn C ω) ≤ 1 + sumBefore (firstReturn C) (geoIncr n κ) (embPath n ω) := by
  cases h : firstReturn C (embPath n ω) with
  | top =>
    rw [sumBefore_eq_of_eq (τ' := fun _ => (⊤ : WithTop ℕ)) h, sumBefore_top_eq]
    have htop : ∑' k : ℕ, geoIncr n κ k (embPath n ω) = ∞ := by
      refine top_le_iff.1 ?_
      rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) (tsub_pos_iff_lt.2 hκ).ne']
      refine ENNReal.tsum_le_tsum fun k => ?_
      calc κ - 1 = 1 * (κ ^ 1 - 1) := by rw [one_mul, pow_one]
        _ ≤ _ := mul_le_mul' (one_le_pow₀ hκ.le)
            (tsub_le_tsub_right (pow_le_pow_right₀ hκ.le (hn1 _)) 1)
    rw [htop, add_top]
    exact le_top
  | coe k =>
    obtain ⟨hk, hkC⟩ := embPath_mem_of_firstReturn_eq h
    rw [sumBefore_of_eq' h, one_add_sum_geoIncr hκ.le]
    calc tpow κ (firstReturn C ω) ≤ tpow κ ((embTime n k ω : ℕ) : WithTop ℕ) :=
          tpow_mono hκ.le (firstReturn_le_embTime hn1 hk hkC)
      _ = κ ^ partialN n k (embPath n ω) := by rw [tpow_coe, embTime_eq_sum]; rfl

/-- **The comparison step of Theorem 19.1.3** (MT p. 486): for a chain with kernel `Q`, if
`κ^{n(x)} (QW(x) + 1) ≤ W(x) + 1 + b 1_C(x)` for every `x` ((19.18) with `κ = λ⁻¹`), then
`E_x[Σ_{k<τ_C} (κ^{S_{k+1}} − κ^{S_k})] ≤ W(x) + b 1_C(x)`. This is the book's application of
Proposition 11.3.2 to `Zₖ = κ^{s(k)} V(Φ̂ₖ)`. -/
theorem lintegral_sumBefore_geoIncr_le (Q : Kernel X X) [IsMarkovKernel Q] {n : X → ℕ}
    (hn : Measurable n) {W : X → ℝ≥0∞} (hW : Measurable W) {κ b : ℝ≥0∞} (hκ : 1 ≤ κ)
    (hκt : κ ≠ ∞) {C : Set X} (hC : MeasurableSet C)
    (h : ∀ x, κ ^ n x * (∫⁻ y, W y ∂Q x + 1) ≤ W x + 1 + C.indicator (fun _ => b) x) (x : X) :
    ∫⁻ ω, sumBefore (firstReturn C) (geoIncr n κ) ω ∂pathKernel Q x ≤
      W x + C.indicator (fun _ => b) x := by
  have := isMarkovKernel_pathKernel Q
  -- measurability of the weights
  have hpowm : ∀ k m, k ≤ m + 1 →
      Measurable[natFilt (X := X) m] fun ω : ℕ → X => κ ^ partialN n k ω := fun k m hkm =>
    measurable_pow_partialN hn κ hkm
  have hpowA : ∀ k, Measurable fun ω : ℕ → X => κ ^ partialN n k ω :=
    measurable_pow_partialN' hn κ
  have hFm : ∀ k, Measurable (geoIncr n κ k) := measurable_geoIncr hn κ
  have hind : Measurable (C.indicator fun _ => b) := measurable_const.indicator hC
  set Z : ℕ → (ℕ → X) → ℝ≥0∞ := fun k ω => κ ^ partialN n k ω * W (ω k) with hZ
  set S : ℕ → (ℕ → X) → ℝ≥0∞ := fun k ω => κ ^ partialN n k ω * C.indicator (fun _ => b) (ω k)
    with hS
  have hZm : ∀ k, Measurable (Z k) := fun k => (hpowA k).mul (hW.comp (measurable_pi_apply k))
  have hSm : ∀ k, Measurable (S k) := fun k => (hpowA k).mul (hind.comp (measurable_pi_apply k))
  have hQW : Measurable fun y => ∫⁻ z, W z ∂Q y := hW.lintegral_kernel
  -- the one-step inequality
  have hstep : ∀ m : ℕ, ∫⁻ ω in {ω | (m : WithTop ℕ) < firstReturn C ω}, Z (m + 1) ω
        ∂pathKernel Q x + ∫⁻ ω in {ω | (m : WithTop ℕ) < firstReturn C ω}, geoIncr n κ m ω
        ∂pathKernel Q x ≤
      ∫⁻ ω in {ω | (m : WithTop ℕ) < firstReturn C ω}, Z m ω ∂pathKernel Q x +
        ∫⁻ ω in {ω | (m : WithTop ℕ) < firstReturn C ω}, S m ω ∂pathKernel Q x := by
    intro m
    set G := {ω : ℕ → X | (m : WithTop ℕ) < firstReturn C ω} with hGdef
    have hG : MeasurableSet[natFilt (X := X) m] G :=
      measurableSet_lt_of_isStoppingTime (proposition_3_4_4 hC).1 m
    have hGm : MeasurableSet G := measurableSet_lt_firstReturn hC m
    -- the Markov property at time `m`
    have hmark : ∫⁻ ω in G, Z (m + 1) ω ∂pathKernel Q x =
        ∫⁻ ω in G, κ ^ partialN n (m + 1) ω * ∫⁻ z, W z ∂Q (ω m) ∂pathKernel Q x := by
      have hF : Measurable[natFilt (X := X) m]
          (G.indicator fun ω => κ ^ partialN n (m + 1) ω) := (hpowm (m + 1) m le_rfl).indicator hG
      have hH : Measurable fun ω' : ℕ → X => W (ω' 1) := hW.comp (measurable_pi_apply 1)
      have hmk := markov_lintegral_mul Q (Measure.dirac x) hF hH
      rw [pathMeasure_dirac] at hmk
      have e1 : ∀ y, ∫⁻ ω', W (ω' 1) ∂pathKernel Q y = ∫⁻ z, W z ∂Q y := fun y => by
        rw [← lintegral_map hW (measurable_pi_apply 1), pathKernel_map_coord, pow_one]
      have hL : ∀ ω : ℕ → X, G.indicator (fun ω => κ ^ partialN n (m + 1) ω) ω *
          W (shift m ω 1) = G.indicator (fun ω => Z (m + 1) ω) ω := fun ω => by
        by_cases hω : ω ∈ G <;> simp [hω, hZ, shift]
      have hR : ∀ ω : ℕ → X, G.indicator (fun ω => κ ^ partialN n (m + 1) ω) ω *
          ∫⁻ ω', W (ω' 1) ∂pathKernel Q (ω m) =
          G.indicator (fun ω => κ ^ partialN n (m + 1) ω * ∫⁻ z, W z ∂Q (ω m)) ω := fun ω => by
        by_cases hω : ω ∈ G <;> simp [hω, e1]
      calc ∫⁻ ω in G, Z (m + 1) ω ∂pathKernel Q x
          = ∫⁻ ω, G.indicator (fun ω => Z (m + 1) ω) ω ∂pathKernel Q x :=
            (lintegral_indicator hGm _).symm
        _ = ∫⁻ ω, G.indicator (fun ω => κ ^ partialN n (m + 1) ω) ω * W (shift m ω 1)
            ∂pathKernel Q x := (lintegral_congr hL).symm
        _ = ∫⁻ ω, G.indicator (fun ω => κ ^ partialN n (m + 1) ω) ω *
            ∫⁻ ω', W (ω' 1) ∂pathKernel Q (ω m) ∂pathKernel Q x := hmk
        _ = ∫⁻ ω, G.indicator (fun ω => κ ^ partialN n (m + 1) ω * ∫⁻ z, W z ∂Q (ω m)) ω
            ∂pathKernel Q x := lintegral_congr hR
        _ = _ := lintegral_indicator hGm _
    -- the pointwise inequality
    have hpt : ∀ ω : ℕ → X, κ ^ partialN n (m + 1) ω * ∫⁻ z, W z ∂Q (ω m) + geoIncr n κ m ω ≤
        Z m ω + S m ω := by
      intro ω
      set d := κ ^ partialN n m ω
      set c := κ ^ n (ω m)
      have hdt : d ≠ ∞ := ENNReal.pow_ne_top hκt
      have hdc : κ ^ partialN n (m + 1) ω = d * c := by
        rw [partialN, Finset.sum_range_succ, pow_add]; rfl
      have hc1 : 1 ≤ c := one_le_pow₀ hκ
      have hmul : d * (c * (∫⁻ z, W z ∂Q (ω m) + 1)) ≤ d * (W (ω m) + 1 +
          C.indicator (fun _ => b) (ω m)) := mul_le_mul' le_rfl (h (ω m))
      have hle : d * c * ∫⁻ z, W z ∂Q (ω m) + d * c ≤
          d * W (ω m) + d * C.indicator (fun _ => b) (ω m) + d := by
        calc d * c * ∫⁻ z, W z ∂Q (ω m) + d * c = d * (c * (∫⁻ z, W z ∂Q (ω m) + 1)) := by ring
          _ ≤ d * (W (ω m) + 1 + C.indicator (fun _ => b) (ω m)) := hmul
          _ = d * W (ω m) + d * C.indicator (fun _ => b) (ω m) + d := by ring
      have hgeo : geoIncr n κ m ω = d * c - d := by
        rw [geoIncr, ENNReal.mul_sub (fun _ _ => hdt), mul_one]
      rw [hdc, hgeo]
      refine ENNReal.le_of_add_le_add_right hdt ?_
      calc d * c * ∫⁻ z, W z ∂Q (ω m) + (d * c - d) + d =
          d * c * ∫⁻ z, W z ∂Q (ω m) + d * c := by
            rw [add_assoc, tsub_add_cancel_of_le (le_mul_of_one_le_right zero_le hc1)]
        _ ≤ _ := hle
    rw [hmark, ← lintegral_add_left (f := fun ω => κ ^ partialN n (m + 1) ω *
      ∫⁻ z, W z ∂Q (ω m)) ((hpowA (m + 1)).mul (hQW.comp (measurable_pi_apply m))),
      ← lintegral_add_left (hZm m)]
    exact setLIntegral_mono ((hZm m).add (hSm m)) fun ω _ => hpt ω
  have hcomp := comparison_lintegral (pathKernel Q x) (measurableSet_lt_firstReturn hC) hFm hSm
    hstep
  -- the two terms on the right
  have hZ0 : ∫⁻ ω, Z 0 ω ∂pathKernel Q x = W x := by
    have : ∀ ω : ℕ → X, Z 0 ω = W (ω 0) := fun ω => by simp [hZ, partialN]
    simp_rw [this]
    exact lintegral_coord_zero Q x hW
  have hnot : ∀ (ω : ℕ → X) (k : ℕ), 1 ≤ k → (k : WithTop ℕ) < firstReturn C ω → ω k ∉ C := by
    intro ω k hk hlt
    have hle : WithTop.some (k + 1) ≤ firstReturn C ω := by
      cases ht : firstReturn C ω with
      | top => exact le_top
      | coe t => rw [ht] at hlt; exact WithTop.coe_le_coe.2 (WithTop.coe_lt_coe.1 hlt)
    exact (le_firstReturn_iff C ω (k + 1)).1 hle k hk (Nat.lt_succ_self k)
  have hS0 : ∀ ω : ℕ → X, sumBefore (firstReturn C) S ω ≤ C.indicator (fun _ => b) (ω 0) := by
    intro ω
    rw [sumBefore, tsum_eq_single 0 fun k hk => ?_]
    · refine (indicator_le_self' (fun _ _ => zero_le) ω).trans ?_
      simp [hS, partialN]
    · by_cases hlt : (k : WithTop ℕ) < firstReturn C ω
      · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < firstReturn C ω} from hlt)]
        simp [hS, indicator_of_notMem (hnot ω k (Nat.one_le_iff_ne_zero.2 hk) hlt)]
      · exact indicator_of_notMem (s := {ω | (k : WithTop ℕ) < firstReturn C ω}) hlt _
  calc ∫⁻ ω, sumBefore (firstReturn C) (geoIncr n κ) ω ∂pathKernel Q x
      ≤ ∫⁻ ω, Z 0 ω ∂pathKernel Q x + ∫⁻ ω, sumBefore (firstReturn C) S ω ∂pathKernel Q x :=
        hcomp
    _ ≤ W x + ∫⁻ ω, C.indicator (fun _ => b) (ω 0) ∂pathKernel Q x :=
        add_le_add (le_of_eq hZ0) (lintegral_mono hS0)
    _ = W x + C.indicator (fun _ => b) x := by rw [lintegral_coord_zero Q x hind]

/-- **(19.19)** (MT p. 487): if `n ≥ 1`, `V ≥ 1` and `P̂V ≤ λ^{n} (V + b 1_C)` (19.15) with
`0 < λ < 1`, then with `κ = λ⁻¹`, `E_x[κ^{τ_C}] ≤ 2V(x) + 2b 1_C(x)` for every `x`. The book's
`V' = 2V − 1 ≥ 1` turns (19.15) into (19.18). -/
theorem kendallMoment_le_stateDrift (P : Kernel X X) [IsMarkovKernel P] {n : X → ℕ}
    (hn : Measurable n) (hn1 : ∀ x, 1 ≤ n x) {V : X → ℝ≥0∞} (hV : Measurable V)
    (hV1 : ∀ x, 1 ≤ V x) {ρ b : ℝ≥0∞} (hρ0 : ρ ≠ 0) (hρ : ρ < 1) {C : Set X}
    (hC : MeasurableSet C)
    (h : ∀ x, ∫⁻ y, V y ∂(P ^ n x) x ≤ ρ ^ n x * (V x + C.indicator (fun _ => b) x)) (x : X) :
    kendallMoment P C ρ⁻¹ x ≤ 2 * V x + 2 * C.indicator (fun _ => b) x := by
  have := isMarkovKernel_stateKernel P hn
  have := isMarkovKernel_pathKernel P
  set κ := ρ⁻¹ with hκdef
  have hκ : 1 < κ := ENNReal.one_lt_inv.2 hρ
  have hκt : κ ≠ ∞ := ENNReal.inv_ne_top.2 hρ0
  have hρt : ρ ≠ ∞ := ne_top_of_lt hρ
  set W : X → ℝ≥0∞ := fun y => 2 * V y - 1 with hWdef
  have hW : Measurable W := (hV.const_mul 2).sub measurable_const
  have h2V : ∀ y, 1 ≤ 2 * V y := fun y =>
    (hV1 y).trans (le_mul_of_one_le_left zero_le (by norm_num))
  have hW1 : ∀ y, W y + 1 = 2 * V y := fun y => tsub_add_cancel_of_le (h2V y)
  have hQW : ∀ y, ∫⁻ z, W z ∂stateKernel P hn y + 1 = 2 * ∫⁻ z, V z ∂stateKernel P hn y := by
    intro y
    have hsub : ∫⁻ z, W z ∂stateKernel P hn y =
        ∫⁻ z, 2 * V z ∂stateKernel P hn y - ∫⁻ _z, (1 : ℝ≥0∞) ∂stateKernel P hn y :=
      lintegral_sub measurable_const (by simp) (Eventually.of_forall h2V)
    have hge : 1 ≤ 2 * ∫⁻ z, V z ∂stateKernel P hn y := by
      calc (1 : ℝ≥0∞) = ∫⁻ _z, (1 : ℝ≥0∞) ∂stateKernel P hn y := by simp
        _ ≤ ∫⁻ z, 2 * V z ∂stateKernel P hn y := lintegral_mono h2V
        _ = 2 * ∫⁻ z, V z ∂stateKernel P hn y := lintegral_const_mul 2 hV
    rw [hsub, lintegral_const_mul 2 hV, lintegral_const, measure_univ, mul_one,
      tsub_add_cancel_of_le hge]
  have hind2 : ∀ y, C.indicator (fun _ => 2 * b) y = 2 * C.indicator (fun _ => b) y := fun y => by
    by_cases hy : y ∈ C <;> simp [hy]
  have hdrift : ∀ y, κ ^ n y * (∫⁻ z, W z ∂stateKernel P hn y + 1) ≤
      W y + 1 + C.indicator (fun _ => 2 * b) y := by
    intro y
    have hκρ : κ ^ n y * ρ ^ n y = 1 := by
      rw [← mul_pow, hκdef, ENNReal.inv_mul_cancel hρ0 hρt, one_pow]
    rw [hQW, hW1, hind2, stateKernel_apply]
    calc κ ^ n y * (2 * ∫⁻ z, V z ∂(P ^ n y) y)
        = 2 * (κ ^ n y * ∫⁻ z, V z ∂(P ^ n y) y) := by ring
      _ ≤ 2 * (κ ^ n y * (ρ ^ n y * (V y + C.indicator (fun _ => b) y))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (h y))
      _ = 2 * V y + 2 * C.indicator (fun _ => b) y := by
          rw [← mul_assoc (κ ^ n y), hκρ, one_mul, mul_add]
  have hcomp := lintegral_sumBefore_geoIncr_le (stateKernel P hn) hn hW hκ.le hκt hC hdrift x
  have hg : Measurable (sumBefore (firstReturn C) (geoIncr (X := X) n κ)) :=
    measurable_sumBefore (measurableSet_lt_firstReturn hC) (measurable_geoIncr hn κ)
  calc kendallMoment P C κ x = ∫⁻ ω, tpow κ (firstReturn C ω) ∂pathKernel P x := rfl
    _ ≤ ∫⁻ ω, (1 + sumBefore (firstReturn C) (geoIncr n κ) (embPath n ω)) ∂pathKernel P x :=
        lintegral_mono fun ω => tpow_firstReturn_le hn1 hκ C ω
    _ = 1 + ∫⁻ ω', sumBefore (firstReturn C) (geoIncr n κ) ω'
          ∂pathKernel (stateKernel P hn) x := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          ← pathKernel_map_embPath P hn x, lintegral_map hg (measurable_embPath hn)]
    _ ≤ 1 + (W x + C.indicator (fun _ => 2 * b) x) := add_le_add le_rfl hcomp
    _ = 2 * V x + 2 * C.indicator (fun _ => b) x := by
        rw [← add_assoc, add_comm 1, hW1, hind2]

/-- `G_C^{(κ)}(x, 1) ≤ κ (κ − 1)⁻¹ E_x[κ^{τ_C}]`, since `σ_C ≤ τ_C`. -/
theorem geomG_one_le_kendallMoment (P : Kernel X X) [IsMarkovKernel P] (C : Set X)
    {κ : ℝ≥0∞} (hκ : 1 < κ) (hκt : κ ≠ ∞) (x : X) :
    geomG P C κ (fun _ => 1) x ≤ κ * (κ - 1)⁻¹ * kendallMoment P C κ x := by
  have hκ1 : κ - 1 ≠ 0 := (tsub_pos_iff_lt.2 hκ).ne'
  have hκ1t : κ - 1 ≠ ∞ := ENNReal.sub_ne_top hκt
  rw [geomG, kendallMoment, ← lintegral_const_mul' _ _
    (ENNReal.mul_ne_top hκt (ENNReal.inv_ne_top.2 hκ1))]
  refine lintegral_mono fun ω => ?_
  set t := firstReturn C ω
  have hmono := sumBefore_mono_time (τ := fun ω => firstHit C ω + 1)
    (τ' := fun ω => firstReturn C ω + 1)
    (fun ω => add_le_add_left (firstHit_le_firstReturn' C ω) 1) (fun k (_ : ℕ → X) => κ ^ k * 1) ω
  refine hmono.trans ?_
  rw [sumBefore_eq_tsum]
  simp only [mul_one]
  set Ssum := ∑' k : ℕ, {k : ℕ | (k : WithTop ℕ) < t + 1}.indicator (fun k => κ ^ k) k
  have h1 := tpow_eq_one_add hκ (t + 1)
  rw [tpow_add hκ.le, show tpow κ 1 = κ from pow_one κ] at h1
  calc Ssum = (κ - 1)⁻¹ * ((κ - 1) * Ssum) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hκ1 hκ1t, one_mul]
    _ ≤ (κ - 1)⁻¹ * (tpow κ t * κ) := mul_le_mul' le_rfl (h1 ▸ le_add_self)
    _ = κ * (κ - 1)⁻¹ * tpow κ t := by ring

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 19.1.3** (MT p. 486): for a `ψ`-irreducible aperiodic chain, a measurable
`n : X → ℕ` with `n ≥ 1`, a petite set `C`, `V ≥ 1` bounded on `C` and finite at some point, and
constants `λ < 1`, `b < ∞` with `∫ P^{n(x)}(x, dy) V(y) ≤ λ^{n(x)} [V(x) + b 1_C(x)]` (19.15),
the chain is positive (geometrically ergodic), and for every invariant probability `π` there are
`r > 1` and `R < ∞` with `Σₖ rᵏ ‖Pᵏ(x, ·) − π‖ ≤ R V(x)` for every `x` (19.16).

The proof is the book's: (19.19) makes `C` a Kendall set, and the Geometric Ergodic Theorem
(Theorem 15.4.1) gives the bound with `G_C^{(κ)}(x, 1) ≤ c E_x[κ^{τ_C}] ≤ c (2 + 2b) V(x)`. -/
theorem theorem_19_1_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {n : X → ℕ} (hn : Measurable n)
    (hn1 : ∀ x, 1 ≤ n x) {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) {x₀ : X}
    (hx₀ : V x₀ ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hVC : ∀ x ∈ C, V x ≤ M)
    (h : ∀ x, ∫⁻ y, V y ∂(P ^ n x) x ≤ ρ ^ n x * (V x + C.indicator (fun _ => b) x)) :
    IsPositive P ψ ∧ ∀ (π : Measure X) [IsProbabilityMeasure π], IsInvariant P π →
      ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
        ∑' k, r ^ k * fNorm (fun _ => 1) ((P ^ k : Kernel X X) x) π ≤ R * V x := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  -- replace `λ` by `λ' = max λ ½ ∈ (0, 1)`
  set ρ' := max ρ 2⁻¹ with hρ'def
  have hρ'1 : ρ' < 1 := max_lt hρ (ENNReal.inv_lt_one.2 (by norm_num))
  have hρ'0 : ρ' ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 2⁻¹) (le_max_right _ _)).ne'
  have h' : ∀ x, ∫⁻ y, V y ∂(P ^ n x) x ≤ ρ' ^ n x * (V x + C.indicator (fun _ => b) x) :=
    fun x => (h x).trans (mul_le_mul' (pow_le_pow_left₀ zero_le (le_max_left _ _) _) le_rfl)
  set κ := ρ'⁻¹ with hκdef
  have hκ : 1 < κ := ENNReal.one_lt_inv.2 hρ'1
  have hκt : κ ≠ ∞ := ENNReal.inv_ne_top.2 hρ'0
  have hK := kendallMoment_le_stateDrift P hn hn1 hV hV1 hρ'0 hρ'1 hCm h'
  -- `C` is non-empty
  have hne : C.Nonempty := by
    have hfin : kendallMoment P C κ x₀ ≠ ∞ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hx₀, ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (by by_cases hx : x₀ ∈ C <;> simp [hx, hb])⟩) (hK x₀)
    have hL := hitProb_eq_one_of_kendallMoment_ne_top P hCm hfin
    rw [nonempty_iff_ne_empty]
    rintro rfl
    have h0 : hitProb P ∅ x₀ = 0 := by
      have : {ω : ℕ → X | firstReturn ∅ ω ≠ ⊤} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, firstReturn_ne_top_iff]
        simp
      rw [hitProb, this, measure_empty]
    rw [h0] at hL
    exact zero_ne_one hL
  -- `C` is a Kendall set
  have hKen : IsKendall P C κ := ⟨hCm, hκ, hκt, 2 * M + 2 * b,
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hM,
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top hb⟩, fun x hx => (hK x).trans (by
        rw [indicator_of_mem hx]; exact add_le_add (mul_le_mul' le_rfl (hVC x hx)) le_rfl)⟩
  obtain ⟨-, -, hpos, hgeo⟩ := theorem_15_4_1 hψ hap measurable_const (fun _ => le_rfl) hC hne
    hKen.isFKendall_one
  refine ⟨hpos, fun π _ hπ => ?_⟩
  obtain ⟨-, r, hr, R, hR, hbd⟩ := hgeo π hπ
  set c := κ * (κ - 1)⁻¹ * (2 + 2 * b) with hc
  have hct : c ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hκt (ENNReal.inv_ne_top.2
    (tsub_pos_iff_lt.2 hκ).ne')) (ENNReal.add_ne_top.2 ⟨ENNReal.ofNat_ne_top,
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top hb⟩)
  refine ⟨r, hr, R * c, ENNReal.mul_ne_top hR hct, fun x => (hbd x).trans ?_⟩
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  calc geomG P C κ (fun _ => 1) x ≤ κ * (κ - 1)⁻¹ * kendallMoment P C κ x :=
        geomG_one_le_kendallMoment P C hκ hκt x
    _ ≤ κ * (κ - 1)⁻¹ * (2 * V x + 2 * C.indicator (fun _ => b) x) := mul_le_mul' le_rfl (hK x)
    _ ≤ κ * (κ - 1)⁻¹ * ((2 + 2 * b) * V x) := by
        refine mul_le_mul' le_rfl ?_
        rw [add_mul]
        refine add_le_add le_rfl ?_
        calc 2 * C.indicator (fun _ => b) x ≤ 2 * b :=
              mul_le_mul' le_rfl (indicator_le_self' (fun _ _ => zero_le) x)
          _ = 2 * b * 1 := (mul_one _).symm
          _ ≤ 2 * b * V x := mul_le_mul' le_rfl (hV1 x)
    _ = c * V x := by rw [hc]; ring

end MeynTweedie.GeneralizedDrift
