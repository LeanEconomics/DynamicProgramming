/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.NonPositivity
import GeneralizedDrift.RandomWalkHalfLine
import GeneralizedDrift.CountableInvariant
import GeneralizedDrift.TChainModels

/-!
# Drift and regularity: deterministic models and applications (MT §11.2, §11.4, §11.5.2)

Copied for Chapter 19 from the Chapter 11 project
(`DriftRegularity/DriftExamples.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to this project's modules.

Meyn and Tweedie, §11.2, pp. 261–263, §11.4, pp. 272–278, and §11.5.2, pp. 279–284.

**The semi-dynamical system (DS1)** (§11.2). For a continuous `F : X → X` on a topological space:
`IsDSRecurrent F` (some compact set is reached from every point), `IsUltimatelyBounded F`, and
the drift condition `DS2 F` (DS2).
* **Theorem 11.2.1** (p. 262): (i) `theorem_11_2_1_i`, (DS2) implies ultimate boundedness, with
  the compact absorbing set `C ∪ ⋃_{1 ≤ i ≤ ⌊M⌋₊+1} F^i(C)` (`ds_return`, `ds_hits`); (ii)
  `theorem_11_2_1_ii`, a recurrent system satisfies (DS2) with `V = σ_O` (`dsHit`); (iii)
  `theorem_11_2_1_iii`, recurrence and ultimate boundedness are equivalent.

**Random walk on a half line** (`halfLineWalkKernel Γ`, increment law `Γ`, `E|W| < ∞`).
* **Proposition 11.4.1** (`proposition_11_4_1`, p. 272): if `β < 0` the walk is regular and every
  compact set is regular (test function `V(x) = x/ε`).
* **Proposition 11.5.3** (`proposition_11_5_3`, p. 279): the walk is regular iff `β < 0`; for
  `β ≥ 0`, `V(x) = x` satisfies (11.42)–(11.43), every `(c, ∞)` is in `B⁺` (`halfLine_pos_Ioi`,
  through `halfLine_pow_climb`, `Pⁿ(x, [nδ, ∞)) ≥ Γ(δ, ∞)ⁿ`), and Theorem 11.5.2 applies.

**The forward recurrence time chain** (p. 273). `fwdRec_drift`: (11.28)–(11.29) for `V(x) = x`,
`E_j[σ_0] = j`, `E_0[τ_0] = Σₙ n p(n)`, and (V2) with `V(x) = x`, `C = {0}` holds iff
`Σₙ n p(n) < ∞`.

**Linear models.** **Proposition 11.4.2** (`proposition_11_4_2`, p. 273): the simple linear
model with `|α| < 1` and `E log(1 + |W|) < ∞` is regular and every compact set is regular, with
`V(x) = log(1 + ε|x|)`.

**The SETAR model** (`setarKernel`; regime noises `W(j)` with zero mean, (SETAR1), and
densities positive on `ℝ`, (SETAR2)).
* `regular_of_real_drift`: on `ℝ`, the real drift (11.41) `PV ≤ V − 1` off `[−R, R]` with `PV`
  bounded on `[−R, R]` gives (V2) and regularity.
* The test function `pwLin a b = a x⁺ + b x⁻`; `setar_pwLin_step`, `integral_pwLin_shift_pos`,
  `integral_pwLin_shift_neg` (the exact one-step means for zero-mean noise),
  `exists_tail_posPart_le`; `setar_top_drift`, `setar_bot_drift`: the drift at `±∞` for a
  contracting end or a unit-slope end pushed inwards by its constant; `setar_regular_of_ends`.
* **Proposition 11.4.5** (`proposition_11_4_5`, p. 276): the SETAR model is regular, and every
  compact set is regular, in the whole interior (11.36)–(11.40). `setar_regular_36_39` covers
  (11.36)–(11.39) with `V = a x⁺ + b x⁻` (`setar_interior_slopes` is the book's "straightforward
  calculation" of the slopes for (11.36)); `setar_regular_eq_11_40` covers (11.40) in one step
  with the kinked `V = max(x + c, d − bx)` (`kinkV_eq_top`, `kinkV_eq_bot`), where the book uses
  the two-step kernel.
* **Proposition 11.5.5** (`proposition_11_5_5`, p. 283): the SETAR model is null when
  `θ(1) < 0`, `θ(1)θ(M) = 1` and `φ(M) + θ(M)φ(1) ≤ 0`, the case the book proves (it contains
  the margin (11.49)). The test function is `kinkV b c d = max(x + c, d − bx)` with `b = −θ(1)`:
  its two affine minorants give `ΔV ≥ 0` at both ends from zero-mean noise, and
  `kink_top_incr`, `kink_bot_incr`, `kink_mid_incr` give (11.43); Theorem 11.5.2 then applies.

**Corrections.** In the proof of Proposition 11.5.5 the book swaps the roles of `φ` and `θ`
(its `φ(1)φ(M) = 1` is the slope condition `θ(1)θ(M) = 1`, and `P(x, dy) = Γ_M(dy − θ(M) −
φ(M)x)` has intercept `θ(M)`), and it proves the result only for the region (11.49) (in the weak
form `φ(M) + θ(M)φ(1) ≤ 0`), not for the other margins (11.45)–(11.48). The bump `I_{kR}` of (11.59)
is not needed when `V_{cd}` is written as the maximum of its two affine pieces.

**Hypotheses.** Theorem 11.2.1 (ii) needs an open precompact neighbourhood of the recurrence
set; it is stated on a locally compact Hausdorff space. In Propositions 11.4.1 and 11.5.3 the walk
is assumed `ψ`-irreducible (the book's standing assumption for regularity). In Proposition 11.4.2
the `ψ`-irreducibility and the petiteness of compact sets are hypotheses: the book takes them from
Proposition 6.3.5, which is formalised for the matrix model on `Fin n → ℝ`, not for the scalar
model on `ℝ`. In the SETAR results the noises are integrable with mean zero (part of (SETAR1)).

**Elsewhere.** Propositions 11.4.3 and 11.4.4 (the GI/G/1 queue with re-entry) are in
`GIG1Reentry`; Proposition 11.5.4 (recurrence on the margins, with the correction of the slope
`a = −bθ(M)` in the region (11.45) to `a = −b/θ(1)`) is in `SetarMarginRecurrence`; and
Proposition 11.5.5 on the other margins (11.45)–(11.48) is in `SetarNullMargins`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-! ### §11.2: the semi-dynamical system (DS1) -/

variable {X : Type*} [TopologicalSpace X]

/-- The semi-dynamical system (DS1) `Φ_{k+1} = F(Φ_k)` is **recurrent** (MT p. 261): some compact
set is reached from every initial condition. -/
def IsDSRecurrent (F : X → X) : Prop :=
  ∃ C : Set X, IsCompact C ∧ ∀ x, ∃ n, F^[n] x ∈ C

/-- The semi-dynamical system is **ultimately bounded** (MT p. 261): every trajectory eventually
enters and remains in a fixed compact set. -/
def IsUltimatelyBounded (F : X → X) : Prop :=
  ∃ C : Set X, IsCompact C ∧ ∀ x, ∃ N, ∀ n, N ≤ n → F^[n] x ∈ C

/-- The drift condition (DS2) (MT p. 262): a function `V ≥ 0`, a compact `C` and `M < ∞` with
`V(F(x)) − V(x) ≤ −1` off `C` and `sup_{x ∈ C} V(F(x)) ≤ M`. -/
def DS2 (F : X → X) : Prop :=
  ∃ (V : X → ℝ) (C : Set X) (M : ℝ), (∀ x, 0 ≤ V x) ∧ IsCompact C ∧
    (∀ x, x ∉ C → V (F x) ≤ V x - 1) ∧ ∀ x ∈ C, V (F x) ≤ M

omit [TopologicalSpace X] in
/-- Under the decrease `V(F(x)) ≤ V(x) − 1` off `C`: if `F^[1], …, F^[n]` of `x` avoid `C`, then
`V(F^[n+1] x) ≤ V(F x) − n`. -/
theorem ds_decrease {F : X → X} {V : X → ℝ} {C : Set X}
    (hdec : ∀ x, x ∉ C → V (F x) ≤ V x - 1) (x : X) (n : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ n → F^[i] x ∉ C) : V (F^[n + 1] x) ≤ V (F x) - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := ih fun i hi1 hin => h i hi1 (by omega)
    have h2 := hdec (F^[n + 1] x) (h (n + 1) (by omega) le_rfl)
    rw [← Function.iterate_succ_apply' F (n + 1) x] at h2
    push_cast
    linarith

omit [TopologicalSpace X] in
/-- Under the decrease off `C`, every trajectory enters `C`: if `x, F x, …, F^[n] x` avoid `C`
then `V(F^[n+1] x) ≤ V(x) − (n + 1)`, impossible for `n ≥ V(x)` since `V ≥ 0`. -/
theorem ds_hits {F : X → X} {V : X → ℝ} {C : Set X} (hV : ∀ x, 0 ≤ V x)
    (hdec : ∀ x, x ∉ C → V (F x) ≤ V x - 1) (x : X) : ∃ n, F^[n] x ∈ C := by
  by_contra hc
  push Not at hc
  have key : ∀ n : ℕ, V (F^[n] x) ≤ V x - n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hdec _ (hc n)
      rw [← Function.iterate_succ_apply' F n x] at this
      push_cast
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (V x)
  linarith [key n, hV (F^[n] x)]

omit [TopologicalSpace X] in
/-- Under (DS2), from `C` the trajectory returns to `C` within `⌊M⌋₊ + 1` steps. -/
theorem ds_return {F : X → X} {V : X → ℝ} {C : Set X} {M : ℝ} (hV : ∀ x, 0 ≤ V x)
    (hdec : ∀ x, x ∉ C → V (F x) ≤ V x - 1) (hM : ∀ x ∈ C, V (F x) ≤ M) {x : X} (hx : x ∈ C) :
    ∃ i, 1 ≤ i ∧ i ≤ ⌊M⌋₊ + 1 ∧ F^[i] x ∈ C := by
  by_contra hc
  push Not at hc
  have h := ds_decrease hdec x (⌊M⌋₊ + 1) fun i hi1 hin => hc i hi1 hin
  have hlt : M < ⌊M⌋₊ + 1 := Nat.lt_floor_add_one M
  push_cast at h
  linarith [hV (F^[⌊M⌋₊ + 1 + 1] x), hM x hx]

/-- **Theorem 11.2.1 (i)** (MT p. 262): under (DS2) the semi-dynamical system (DS1), with `F`
continuous, is ultimately bounded. The trajectories are eventually in the compact set
`C ∪ ⋃_{1 ≤ i ≤ ⌊M⌋₊+1} F^i(C)`. -/
theorem theorem_11_2_1_i {F : X → X} (hF : Continuous F) (h : DS2 F) : IsUltimatelyBounded F := by
  obtain ⟨V, C, M, hV, hC, hdec, hM⟩ := h
  set m := ⌊M⌋₊ + 1
  set C' := C ∪ ⋃ i ∈ Finset.Icc 1 m, F^[i] '' C with hC'
  have hC'c : IsCompact C' :=
    hC.union (Finset.isCompact_biUnion _ fun i _ => hC.image (hF.iterate i))
  -- forward invariance from `C`
  have hinv : ∀ j, ∀ x ∈ C, F^[j] x ∈ C' := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro x hx
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact Or.inl hx
      obtain ⟨i, hi1, him, hiC⟩ := ds_return hV hdec hM hx
      by_cases hji : j ≤ i
      · exact Or.inr (mem_biUnion (Finset.mem_Icc.2 ⟨hj, hji.trans him⟩) ⟨x, hx, rfl⟩)
      · have := ih (j - i) (by omega) _ hiC
        rwa [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)] at this
  refine ⟨C', hC'c, fun x => ?_⟩
  obtain ⟨n, hn⟩ := ds_hits hV hdec x
  refine ⟨n, fun k hk => ?_⟩
  have := hinv (k - n) _ hn
  rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hk] at this

/-- The first hitting time `σ_O(x) = min{n ≥ 0 : F^n(x) ∈ O}` of the deterministic system
(`0` if `O` is never reached). -/
noncomputable def dsHit (F : X → X) (O : Set X) (x : X) : ℕ := sInf {n | F^[n] x ∈ O}

/-- **Theorem 11.2.1 (ii)** (MT p. 262): on a locally compact Hausdorff space, a recurrent
semi-dynamical system with continuous `F` satisfies (DS2), with `V = σ_O` for an open
precompact `O` containing the recurrence set and `C = cl O`. -/
theorem theorem_11_2_1_ii [T2Space X] [WeaklyLocallyCompactSpace X] {F : X → X}
    (hF : Continuous F) (h : IsDSRecurrent F) : DS2 F := by
  classical
  obtain ⟨C₁, hC₁, hrec⟩ := h
  obtain ⟨K, hK, hC₁K⟩ := exists_compact_superset hC₁
  set O := interior K
  have hO : IsOpen O := isOpen_interior
  have hreach : ∀ x, ∃ n, F^[n] x ∈ O := fun x => by
    obtain ⟨n, hn⟩ := hrec x; exact ⟨n, hC₁K hn⟩
  set C := closure O
  have hC : IsCompact C := hK.of_isClosed_subset isClosed_closure
    (closure_minimal interior_subset hK.isClosed)
  set V : X → ℝ := fun x => (dsHit F O x : ℝ)
  -- `σ_O(F x) = σ_O(x) − 1` off `O`
  have hstep : ∀ x, x ∉ O → dsHit F O (F x) + 1 = dsHit F O x := by
    intro x hx
    unfold dsHit
    refine le_antisymm ?_ ?_
    · set s := sInf {n | F^[n] x ∈ O} with hs
      have h1 : F^[s] x ∈ O := Nat.sInf_mem (hreach x)
      have hs0 : s ≠ 0 := fun h0 => hx (by rw [h0] at h1; simpa using h1)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hs0
      rw [hk] at h1 ⊢
      rw [Function.iterate_succ_apply] at h1
      exact Nat.succ_le_succ (Nat.sInf_le h1)
    · refine Nat.sInf_le ?_
      change F^[_ + 1] x ∈ O
      rw [Function.iterate_succ_apply]
      exact Nat.sInf_mem (hreach (F x))
  -- `σ_O ∘ F` is bounded on the compact `C`
  have hcover : C ⊆ ⋃ N : ℕ, {x | dsHit F O (F x) < N} := fun x _ =>
    mem_iUnion.2 ⟨dsHit F O (F x) + 1, Nat.lt_succ_self _⟩
  have hopen : ∀ N : ℕ, IsOpen {x | dsHit F O (F x) < N} := fun N => by
    have : {x | dsHit F O (F x) < N} = ⋃ k ∈ Finset.range N, (F^[k] ∘ F) ⁻¹' O := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_preimage, Function.comp_apply, Finset.mem_range,
        exists_prop]
      constructor
      · intro hx
        exact ⟨_, hx, Nat.sInf_mem (hreach (F x))⟩
      · rintro ⟨k, hk, hkO⟩
        exact lt_of_le_of_lt (Nat.sInf_le hkO) hk
    rw [this]
    exact isOpen_biUnion fun k _ => hO.preimage ((hF.iterate k).comp hF)
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover _ hopen hcover
  refine ⟨V, C, ∑ N ∈ t, (N : ℝ), fun x => Nat.cast_nonneg _, hC, fun x hx => ?_,
    fun x hx => ?_⟩
  · have hxO : x ∉ O := fun h => hx (subset_closure h)
    have := hstep x hxO
    simp only [V]
    rw [← this]
    push_cast
    linarith
  · obtain ⟨N, hN, hxN⟩ := mem_iUnion₂.1 (ht hx)
    simp only [V]
    have h1 : (dsHit F O (F x) : ℝ) < N := by exact_mod_cast hxN
    have h2 : (N : ℝ) ≤ ∑ N ∈ t, (N : ℝ) :=
      Finset.single_le_sum (f := fun N : ℕ => (N : ℝ)) (fun _ _ => Nat.cast_nonneg _) hN
    linarith

/-- **Theorem 11.2.1 (iii)** (MT p. 262): on a locally compact Hausdorff space, a semi-dynamical
system with continuous `F` is recurrent iff it is ultimately bounded. -/
theorem theorem_11_2_1_iii [T2Space X] [WeaklyLocallyCompactSpace X] {F : X → X}
    (hF : Continuous F) : IsDSRecurrent F ↔ IsUltimatelyBounded F := by
  refine ⟨fun h => theorem_11_2_1_i hF (theorem_11_2_1_ii hF h), fun ⟨C, hC, h⟩ =>
    ⟨C, hC, fun x => ?_⟩⟩
  obtain ⟨N, hN⟩ := h x
  exact ⟨N, hN N le_rfl⟩

/-! ### §11.4.1: random walk on a half line -/

/-- `[x + W]⁺` is integrable when `E|W| < ∞`, with `[x + W]⁺ ≤ x + |W|`. -/
theorem halfLine_integrable_max (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (x : ℝ≥0) :
    Integrable (fun w => max ((x : ℝ) + w) 0) Γ := by
  refine Integrable.mono' ((integrable_const (x : ℝ)).add hW.abs)
    ((measurable_const.add measurable_id).max measurable_const).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  change max ((x : ℝ) + w) 0 ≤ (x : ℝ) + |w|
  exact max_le (by linarith [le_abs_self w]) (by positivity)

/-- `y ↦ y` is integrable for every `P(x, ·)` of the walk on `ℝ₊` when `E|W| < ∞`. -/
theorem halfLine_integrable_coe (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (x : ℝ≥0) :
    Integrable (fun y : ℝ≥0 => (y : ℝ)) (halfLineWalkKernel Γ x) := by
  have hm : Measurable fun w : ℝ => halfLineStep (x, w) :=
    measurable_halfLineStep.comp measurable_prodMk_left
  rw [halfLineWalkKernel, recursionKernel_apply Γ measurable_halfLineStep x,
    integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable hm.aemeasurable]
  have := halfLine_integrable_max Γ hW x
  refine this.congr (Eventually.of_forall fun w => ?_)
  simp [halfLineStep, Real.coe_toNNReal']

/-- `∫ P(x, dy) y = E[[x + W]⁺]`. -/
theorem halfLine_integral_coe (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (x : ℝ≥0) :
    ∫ y, (y : ℝ) ∂halfLineWalkKernel Γ x = ∫ w, max ((x : ℝ) + w) 0 ∂Γ := by
  rw [integral_halfLine Γ x measurable_coe_nnreal_real]
  simp only [Real.coe_toNNReal']

/-- **Proposition 11.4.1** (MT p. 272): random walk on a half line with finite mean increment
`β < 0` is regular, and every compact set is regular. The test function is `V(x) = x/ε`, with
`C = [0, x₀]` from the drift (8.54). -/
theorem proposition_11_4_1 (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0) {ψ : Measure ℝ≥0}
    (hψ : haveI := isMarkovKernel_halfLineWalkKernel Γ
      IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    IsRegularChain (halfLineWalkKernel Γ) ψ ∧
      ∀ K : Set ℝ≥0, IsCompact K → IsRegularSet (halfLineWalkKernel Γ) ψ K := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  obtain ⟨x₀, ε, hε, hdr⟩ := halfLine_drift_neg Γ hW hβ
  have hC : IsPetite (halfLineWalkKernel Γ) (Iic x₀) :=
    halfLine_isPetite_Iic Γ (halfLine_neg_pos_of_mean_neg Γ hβ) x₀
  set V : ℝ≥0 → ℝ≥0∞ := fun y => ENNReal.ofReal ((y : ℝ) / ε) with hVdef
  have hVm : Measurable V := ENNReal.measurable_ofReal.comp
    (measurable_coe_nnreal_real.div_const ε)
  have hPV : ∀ x, ∫⁻ y, V y ∂halfLineWalkKernel Γ x =
      ENNReal.ofReal ((∫ y, (y : ℝ) ∂halfLineWalkKernel Γ x) / ε) := fun x => by
    rw [← integral_div, ofReal_integral_eq_lintegral_ofReal
      ((halfLine_integrable_coe Γ hW x).div_const ε)
      (Eventually.of_forall fun y => div_nonneg y.2 hε.le)]
  set K := (x₀ : ℝ) + ∫ w, |w| ∂Γ with hKdef
  have hbound : ∀ x : ℝ≥0, x ≤ x₀ → ∫ y, (y : ℝ) ∂halfLineWalkKernel Γ x ≤ K := fun x hx => by
    rw [halfLine_integral_coe, hKdef]
    calc ∫ w, max ((x : ℝ) + w) 0 ∂Γ ≤ ∫ w, ((x₀ : ℝ) + |w|) ∂Γ :=
          integral_mono (halfLine_integrable_max Γ hW x) ((integrable_const _).add hW.abs)
            fun w => max_le (by have : (x : ℝ) ≤ x₀ := hx; linarith [le_abs_self w])
              (by positivity)
      _ = (x₀ : ℝ) + ∫ w, |w| ∂Γ := by
          rw [integral_add (integrable_const _) hW.abs, integral_const]; simp
  set b := ENNReal.ofReal (K / ε) + 1 with hbdef
  have hb : b ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
  have hdrift : DriftV2 (halfLineWalkKernel Γ) V b (Iic x₀) := by
    intro x
    rw [hPV x]
    have hI0 : 0 ≤ ∫ y, (y : ℝ) ∂halfLineWalkKernel Γ x :=
      integral_nonneg fun y => y.2
    by_cases hx : x ∈ Iic x₀
    · rw [indicator_of_mem hx]
      refine le_trans ?_ le_add_self
      exact add_le_add (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hbound x hx)
        hε.le)) le_rfl
    · rw [indicator_of_notMem hx, add_zero]
      have hlt : x₀ < x := not_le.1 hx
      have h1 := hdr x hlt
      have hx1 : 1 ≤ (x : ℝ) / ε := by
        rw [le_div_iff₀ hε]; linarith
      calc ENNReal.ofReal ((∫ y, (y : ℝ) ∂halfLineWalkKernel Γ x) / ε) + 1
          ≤ ENNReal.ofReal ((x : ℝ) / ε - 1) + ENNReal.ofReal 1 := by
            rw [ENNReal.ofReal_one]
            refine add_le_add (ENNReal.ofReal_le_ofReal ?_) le_rfl
            rw [div_le_iff₀ hε, sub_mul, div_mul_cancel₀ _ hε.ne']
            linarith
        _ = V x := by
            rw [← ENNReal.ofReal_add (by linarith) zero_le_one, sub_add_cancel]
  have hfin : ∀ x, V x ≠ ∞ := fun x => ENNReal.ofReal_ne_top
  refine ⟨(theorem_11_3_15 hψ).1.2 ⟨Iic x₀, V, b, hC, hVm, hb, hfin, hdrift⟩, fun K' hK' => ?_⟩
  obtain ⟨c, hc⟩ := hK'.bddAbove
  exact theorem_11_3_11_i_regular hψ hVm hb hC hdrift hK'.measurableSet
    (M := ENNReal.ofReal ((c : ℝ) / ε)) ENNReal.ofReal_ne_top fun y hy =>
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by exact_mod_cast hc hy) hε.le)

/-! ### §11.5.2: random walk on a half line is regular iff `β < 0` -/

/-- With `Γ(0, ∞) = 0` and `β ≥ 0` the walk does not move, so it is not `ψ`-irreducible. -/
theorem halfLine_pos_Ioi_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : 0 ≤ ∫ w, w ∂Γ) {ψ : Measure ℝ≥0}
    (hψ : haveI := isMarkovKernel_halfLineWalkKernel Γ
      IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ) : 0 < Γ (Ioi 0) := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  by_contra h0
  have h0' : Γ (Ioi 0) = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h0)
  have hle : ∀ᵐ w ∂Γ, w ≤ 0 := (measure_eq_zero_iff_ae_notMem.1 h0').mono fun w hw => not_lt.1 hw
  have hzero : (fun w : ℝ => -w) =ᵐ[Γ] 0 := by
    have hint : ∫ w, -w ∂Γ = 0 := le_antisymm (by rw [integral_neg]; linarith)
      (integral_nonneg_of_ae (hle.mono fun w hw => by simpa using hw))
    exact (integral_eq_zero_iff_of_nonneg_ae (hle.mono fun w hw => by simpa using hw)
      hW.neg).1 hint
  -- the walk does not move
  have hstay : ∀ x : ℝ≥0, halfLineWalkKernel Γ x = Measure.dirac x := fun x => by
    rw [halfLineWalkKernel, recursionKernel_apply Γ measurable_halfLineStep x]
    have : (fun w => halfLineStep (x, w)) =ᵐ[Γ] fun _ => x := by
      filter_upwards [hzero] with w hw
      have hw0 : w = 0 := by simpa using hw
      simp [halfLineStep, hw0]
    rw [Measure.map_congr this, Measure.map_const, measure_univ, one_smul]
  have hpow : ∀ (n : ℕ) (x : ℝ≥0), (halfLineWalkKernel Γ ^ n) x = Measure.dirac x := by
    intro n
    induction n with
    | zero => intro x; exact pow_zero_apply _ x
    | succ n ih =>
      intro x
      ext A hA
      rw [pow_succ_apply _ n x hA, hstay x, lintegral_dirac' _ (Kernel.measurable_coe _ hA), ih]
  -- a set of positive `ψ`-measure would contain every state
  have hall : ∀ A, MeasurableSet A → 0 < ψ A → ∀ x, x ∈ A := fun A hA hψA x => by
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hA x).1 (hψ.2.1 A hA hψA x)
    rw [hpow, Measure.dirac_apply' _ hA] at hn
    by_contra hx
    rw [indicator_of_notMem hx] at hn
    exact lt_irrefl 0 hn
  have h1 : ψ (Ioi 0) = 0 := by
    by_contra h
    exact absurd (hall _ measurableSet_Ioi (pos_iff_ne_zero.2 h) 0) (by simp)
  have h2 : ψ (Iic 0) = 0 := by
    by_contra h
    exact absurd (hall _ measurableSet_Iic (pos_iff_ne_zero.2 h) 1) (by simp)
  apply hψ.1
  rw [← Measure.measure_univ_eq_zero, ← Iic_union_Ioi (a := (0 : ℝ≥0))]
  exact measure_union_null h2 h1

/-- For `y ≥ nδ`, one step of the walk climbs by more than `δ` with probability at least
`Γ(δ, ∞)`: `Pⁿ(x, [nδ, ∞)) ≥ Γ(δ, ∞)ⁿ`. -/
theorem halfLine_pow_climb (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {δ : ℝ} (hδ : 0 < δ)
    (n : ℕ) (x : ℝ≥0) :
    Γ (Ioi δ) ^ n ≤ (halfLineWalkKernel Γ ^ n) x {y | (n : ℝ) * δ ≤ y} := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  have hS : ∀ m : ℕ, MeasurableSet {y : ℝ≥0 | (m : ℝ) * δ ≤ y} := fun m =>
    measurableSet_le measurable_const measurable_coe_nnreal_real
  induction n generalizing x with
  | zero =>
    rw [pow_zero_apply, Measure.dirac_apply' _ (hS 0)]
    simp
  | succ n ih =>
    rw [pow_succ_apply' _ n x (hS (n + 1))]
    have hstep : ∀ y ∈ {y : ℝ≥0 | (n : ℝ) * δ ≤ y},
        Γ (Ioi δ) ≤ halfLineWalkKernel Γ y {y | ((n + 1 : ℕ) : ℝ) * δ ≤ y} := fun y hy => by
      rw [halfLineWalkKernel_apply' Γ y (hS (n + 1))]
      refine measure_mono fun w hw => ?_
      simp only [mem_Ioi] at hw
      simp only [mem_ofPred_eq] at hy ⊢
      have hpos : 0 ≤ (y : ℝ) + w := by linarith [NNReal.coe_nonneg y]
      rw [Real.coe_toNNReal _ hpos]
      push_cast
      linarith
    calc Γ (Ioi δ) ^ (n + 1) = Γ (Ioi δ) * Γ (Ioi δ) ^ n := pow_succ' _ _
      _ ≤ Γ (Ioi δ) * (halfLineWalkKernel Γ ^ n) x {y | (n : ℝ) * δ ≤ y} :=
          mul_le_mul' le_rfl (ih x)
      _ = ∫⁻ y in {y | (n : ℝ) * δ ≤ y}, Γ (Ioi δ) ∂(halfLineWalkKernel Γ ^ n) x := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in {y | (n : ℝ) * δ ≤ y}, halfLineWalkKernel Γ y
            {y | ((n + 1 : ℕ) : ℝ) * δ ≤ y} ∂(halfLineWalkKernel Γ ^ n) x :=
          setLIntegral_mono' (hS n) hstep
      _ ≤ _ := setLIntegral_le_lintegral _ _

/-- If `β ≥ 0` and the walk is `ψ`-irreducible, every half line `(c, ∞)` is in `B⁺`. -/
theorem halfLine_pos_Ioi (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : 0 ≤ ∫ w, w ∂Γ) {ψ : Measure ℝ≥0}
    (hψ : haveI := isMarkovKernel_halfLineWalkKernel Γ
      IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ) (c : ℝ≥0) : 0 < ψ (Ioi c) := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  have h0 := halfLine_pos_Ioi_zero Γ hW hβ hψ
  -- some `Γ(δ, ∞) > 0`
  obtain ⟨δ, hδ, hΓδ⟩ : ∃ δ : ℝ, 0 < δ ∧ 0 < Γ (Ioi δ) := by
    by_contra hc
    push Not at hc
    have : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioi (1 / ((n : ℝ) + 1)) := by
      ext w
      simp only [mem_Ioi, mem_iUnion]
      constructor
      · intro hw
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hw
        exact ⟨n, hn⟩
      · rintro ⟨n, hn⟩
        exact lt_trans (by positivity) hn
    rw [this] at h0
    exact absurd (measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc _ (by positivity)))
      h0.ne'
  refine (hψ.pos_iff_hitProb_pos measurableSet_Ioi).2 fun x => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt ((c : ℝ) / δ)
  refine (hitProb_pos_iff _ measurableSet_Ioi x).2 ⟨n, ?_⟩
  refine lt_of_lt_of_le (ENNReal.pow_pos hΓδ _) ((halfLine_pow_climb Γ hδ (n + 1) x).trans
    (measure_mono fun y hy => ?_))
  simp only [mem_ofPred_eq, mem_Ioi] at hy ⊢
  have : (c : ℝ) < (n + 1 : ℕ) * δ := by
    rw [div_lt_iff₀ hδ] at hn; push_cast; nlinarith
  exact_mod_cast this.trans_le hy

/-- **Proposition 11.5.3** (MT p. 279): random walk on a half line with finite mean increment `β`
(and `ψ`-irreducible) is regular iff `β < 0`. For `β ≥ 0`, `V(x) = x` has `ΔV ≥ 0` and bounded
mean increments, so the chain is null by Theorem 11.5.2. -/
theorem proposition_11_5_3 (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) {ψ : Measure ℝ≥0}
    (hψ : haveI := isMarkovKernel_halfLineWalkKernel Γ
      IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    IsRegularChain (halfLineWalkKernel Γ) ψ ↔ ∫ w, w ∂Γ < 0 := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  refine ⟨fun hreg => ?_, fun hβ => (proposition_11_4_1 Γ hW hβ hψ).1⟩
  by_contra hβ
  have hβ' : 0 ≤ ∫ w, w ∂Γ := not_lt.1 hβ
  -- some `[0, c]` is in `B⁺`
  obtain ⟨c, hc⟩ : ∃ c : ℕ, 0 < ψ (Iic (c : ℝ≥0)) := by
    refine exists_pos_of_iUnion_eq_univ hψ.1 ?_
    ext y
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge y
    exact ⟨n, hn⟩
  have hCp : {x : ℝ≥0 | ∀ y ∈ Iic (c : ℝ≥0), (y : ℝ) < x} = Ioi (c : ℝ≥0) := by
    ext x
    simp only [mem_ofPred_eq, mem_Iic, mem_Ioi]
    refine ⟨fun h => by exact_mod_cast h c le_rfl, fun h y hy => ?_⟩
    exact_mod_cast lt_of_le_of_lt hy h
  have hnull := theorem_11_5_2 hψ measurable_coe_nnreal_real measurableSet_Iic hc
    (fun x _ => ?_) (B := ∫⁻ w, ‖w‖ₑ ∂Γ) hW.2.ne (fun x => ?_)
    (by rw [hCp]; exact halfLine_pos_Ioi Γ hW hβ' hψ _)
  · exact hnull.2 (hreg.isPositiveHarris hψ).2.2
  · rw [halfLine_integral_coe]
    calc (x : ℝ) ≤ ∫ w, ((x : ℝ) + w) ∂Γ := by
          rw [integral_add (integrable_const _) hW, integral_const]; simp; linarith
      _ ≤ _ := integral_mono ((integrable_const _).add hW) (halfLine_integrable_max Γ hW x)
          fun w => le_max_left _ _
  · rw [lintegral_halfLine Γ x (f := fun y : ℝ≥0 => ‖(y : ℝ) - x‖ₑ)
      (measurable_coe_nnreal_real.sub measurable_const).enorm]
    refine lintegral_mono fun w => ?_
    simp only [Real.coe_toNNReal', Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_total 0 ((x : ℝ) + w) with h | h
    · rw [max_eq_left h, add_sub_cancel_left]
    · rw [max_eq_right h, zero_sub, abs_neg, abs_of_nonneg (NNReal.coe_nonneg x),
        abs_of_nonpos (by linarith [NNReal.coe_nonneg x] : w ≤ 0)]
      linarith

/-! ### §11.4.1: the forward recurrence time chain -/

/-- `∫ f dP(0, ·) = ∫ p(dn) f(n − 1)` for the forward recurrence time chain. -/
theorem lintegral_fwdRec_zero (p : Measure ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ y, f y ∂fwdRecKernel p 0 = ∫⁻ n, f (n - 1) ∂p := by
  change ∫⁻ y, f y ∂fwdRecMeas p 0 = _
  simp only [fwdRecMeas, ↓reduceIte]
  exact lintegral_map (measurable_of_countable _) (measurable_of_countable _)

/-- `P(j, ·) = δ_{j−1}` for `j ≥ 1`. -/
theorem fwdRecKernel_pos (p : Measure ℕ) {j : ℕ} (hj : j ≠ 0) :
    fwdRecKernel p j = Measure.dirac (j - 1) := by
  change fwdRecMeas p j = _
  simp [fwdRecMeas, hj]

/-- (11.28)–(11.29), MT p. 273: for the forward recurrence time chain and `V(x) = x`,
`PV(x) = V(x) − 1` for `x ≥ 1` and `PV(0) = Σₙ p(n)(n − 1)` (the book's `Σ_y p(y) y`, with states
shifted by one); `E_j[σ_0] = j`, and `E_0[τ_0] = Σₙ n p(n)`. Hence (V2) holds for `V(x) = x`,
`C = {0}` with a finite `b` iff `Σₙ n p(n) < ∞`, iff the chain is positive: the bound (11.19) on
`C` is needed. -/
theorem fwdRec_drift (p : Measure ℕ) [IsProbabilityMeasure p] (hp0 : p {0} = 0) :
    haveI := isMarkovKernel_fwdRecKernel p
    (∀ x : ℕ, x ≠ 0 → ∫⁻ y, (y : ℝ≥0∞) ∂fwdRecKernel p x + 1 = x) ∧
      ∫⁻ y, (y : ℝ≥0∞) ∂fwdRecKernel p 0 = ∫⁻ n, ((n - 1 : ℕ) : ℝ≥0∞) ∂p ∧
      (∀ j, meanHitTime (fwdRecKernel p) {0} j = j) ∧
      meanReturnTime (fwdRecKernel p) {0} 0 = ∫⁻ n, (n : ℝ≥0∞) ∂p ∧
      ((∃ b : ℝ≥0∞, b ≠ ∞ ∧ DriftV2 (fwdRecKernel p) (fun x => (x : ℝ≥0∞)) b {0}) ↔
        ∫⁻ n, (n : ℝ≥0∞) ∂p ≠ ∞) := by
  have := isMarkovKernel_fwdRecKernel p
  have h0 : MeasurableSet ({0} : Set ℕ) := measurableSet_singleton 0
  have hstep : ∀ x : ℕ, x ≠ 0 → ∫⁻ y, (y : ℝ≥0∞) ∂fwdRecKernel p x + 1 = x := fun x hx => by
    rw [fwdRecKernel_pos p hx, lintegral_dirac]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hx
    simp
  have hzero : ∫⁻ y, (y : ℝ≥0∞) ∂fwdRecKernel p 0 = ∫⁻ n, ((n - 1 : ℕ) : ℝ≥0∞) ∂p :=
    lintegral_fwdRec_zero p _
  have hhit : ∀ j, meanHitTime (fwdRecKernel p) {0} j = j := by
    intro j
    induction j with
    | zero => rw [meanHitTime_of_mem _ h0 (mem_singleton 0)]; simp
    | succ k ih =>
      rw [meanHitTime_of_notMem _ h0 (by simp), meanReturnTime_eq_one_add _ h0,
        fwdRecKernel_pos p (Nat.succ_ne_zero k), lintegral_dirac, Nat.succ_sub_one, ih]
      push_cast; ring
  have hae : ∀ᵐ n ∂p, n ≠ 0 := measure_mono_null (fun n hn => by simpa using hn) hp0
  have hret : meanReturnTime (fwdRecKernel p) {0} 0 = ∫⁻ n, (n : ℝ≥0∞) ∂p := by
    rw [meanReturnTime_eq_one_add _ h0, lintegral_fwdRec_zero]
    simp_rw [hhit]
    have h1 : ∫⁻ _ : ℕ, (1 : ℝ≥0∞) ∂p = 1 := by simp
    rw [← h1, ← lintegral_add_left measurable_const]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    simp [add_comm]
  refine ⟨hstep, hzero, hhit, hret, ⟨fun ⟨b, hb, h⟩ => ?_, fun hfin => ?_⟩⟩
  · rw [← hret]
    exact ne_top_of_le_ne_top (by simpa using hb) ((theorem_11_3_4
      (measurable_of_countable _) h0 h 0).trans (by simp))
  · refine ⟨∫⁻ n, (n : ℝ≥0∞) ∂p, hfin, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      rw [indicator_of_mem (mem_singleton 0), hzero]
      simp only [CharP.cast_eq_zero, zero_add]
      refine le_of_eq ?_
      calc ∫⁻ n, ((n - 1 : ℕ) : ℝ≥0∞) ∂p + 1 = meanReturnTime (fwdRecKernel p) {0} 0 := by
            rw [meanReturnTime_eq_one_add _ h0, lintegral_fwdRec_zero, add_comm]
            simp_rw [hhit]
        _ = _ := hret
    · rw [indicator_of_notMem (by simpa using hx), add_zero]
      exact (hstep x hx).le

/-! ### §11.4.1: linear models -/

/-- `log(1 + ε|x|)` is subadditive. -/
theorem logAbs_add_le {ε : ℝ} (hε : 0 ≤ ε) (a b : ℝ) :
    Real.log (1 + ε * |a + b|) ≤ Real.log (1 + ε * |a|) + Real.log (1 + ε * |b|) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (by positivity) ?_
  have := abs_add_le a b
  nlinarith [mul_nonneg hε (abs_nonneg a), mul_nonneg hε (abs_nonneg b),
    mul_nonneg (mul_nonneg hε (abs_nonneg a)) (mul_nonneg hε (abs_nonneg b))]

/-- For `0 < ρ < 1`, `log(1 + ερ|x|) ≤ log(1 + ε|x|) + ½ log ρ` once `|x|` is large. -/
theorem logAbs_contract {ε ρ : ℝ} (hε : 0 < ε) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ r : ℝ, ∀ x : ℝ, r ≤ |x| →
      Real.log (1 + ε * (ρ * |x|)) ≤ Real.log (1 + ε * |x|) + Real.log ρ / 2 := by
  set s := Real.sqrt ρ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hρ0
  have hs1 : s < 1 := by rw [hs, Real.sqrt_lt' one_pos]; simpa using hρ1
  have hss : s * s = ρ := Real.mul_self_sqrt hρ0.le
  have hρs : ρ < s := by nlinarith
  refine ⟨(1 - s) / (ε * (s - ρ)), fun x hx => ?_⟩
  have hden : 0 < ε * (s - ρ) := mul_pos hε (by linarith)
  rw [div_le_iff₀ hden] at hx
  have hkey : 1 + ε * (ρ * |x|) ≤ s * (1 + ε * |x|) := by nlinarith
  have hlog : Real.log ρ / 2 = Real.log s := by
    rw [hs, Real.log_sqrt hρ0.le]
  rw [hlog, ← Real.log_mul (by positivity) hs0.ne']
  refine Real.log_le_log (by positivity) ?_
  linarith [mul_comm s (1 + ε * |x|)]

/-- For an integrable `log(1 + |W|)`, `E log(1 + ε|W|) < η` for a small `ε ∈ (0, 1]`. -/
theorem exists_small_logAbs (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => Real.log (1 + |w|)) Γ) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∫ w, Real.log (1 + ε * |w|) ∂Γ < η := by
  have hc : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => ∫ w, Real.log (1 + 1 / ((n : ℝ) + 1) * |w|) ∂Γ) atTop
      (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂Γ)) := by
    refine tendsto_integral_of_dominated_convergence (fun w => Real.log (1 + |w|))
      (fun n => (Real.measurable_log.comp (measurable_const.add (measurable_const.mul
        (measurable_id.norm : Measurable fun w : ℝ => ‖w‖)))).aestronglyMeasurable) hW
      (fun n => Eventually.of_forall fun w => ?_) (Eventually.of_forall fun w => ?_)
    · have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by
        have := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1)) (abs_nonneg w)
        linarith))]
      refine Real.log_le_log (by positivity) ?_
      have := mul_le_of_le_one_left (abs_nonneg w) h1
      linarith
    · have : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1) * |w|) atTop (𝓝 (1 + 0 * |w|)) :=
        tendsto_const_nhds.add (hc.mul tendsto_const_nhds)
      simpa using this.log (by norm_num)
  rw [integral_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds hη)).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_, hn⟩
  rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- **Proposition 11.4.2** (MT p. 273): for the simple linear model `Xₙ = αXₙ₋₁ + Wₙ` with
`|α| < 1` and `E log(1 + |W|) < ∞`, every compact set is regular and the chain is regular. The test
function is `V(x) = log(1 + ε|x|)`, subadditive (`logAbs_add_le`) with
`V(x) − V(ρx) ≥ −½ log ρ` for large `|x|` (`logAbs_contract`, `ρ = max(|α|, ½)`) and
`E V(W) < −¼ log ρ` for small `ε` (`exists_small_logAbs`). The `ψ`-irreducibility and the
petiteness of compact sets, which the book takes from Proposition 6.3.5 (non-singular `W`), are
hypotheses. -/
theorem proposition_11_4_2 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ} (hα : |α| < 1)
    (hW : Integrable (fun w => Real.log (1 + |w|)) Γ) {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_ar1Kernel Γ α; IsMaximalIrreducibility (ar1Kernel Γ α) ψ)
    (hpet : ∀ K : Set ℝ, IsCompact K → IsPetite (ar1Kernel Γ α) K) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    (∀ K : Set ℝ, IsCompact K → IsRegularSet (ar1Kernel Γ α) ψ K) ∧
      IsRegularChain (ar1Kernel Γ α) ψ := by
  have := isMarkovKernel_ar1Kernel Γ α
  set ρ := max |α| 2⁻¹ with hρdef
  have hρ0 : 0 < ρ := lt_max_of_lt_right (by norm_num)
  have hρ1 : ρ < 1 := max_lt hα (by norm_num)
  have hαρ : |α| ≤ ρ := le_max_left _ _
  set L := -Real.log ρ with hLdef
  have hL : 0 < L := by rw [hLdef, neg_pos]; exact Real.log_neg hρ0 hρ1
  obtain ⟨ε, hε0, hε1, hεW⟩ := exists_small_logAbs Γ hW (η := L / 4) (by positivity)
  obtain ⟨r, hr⟩ := logAbs_contract hε0 hρ0 hρ1
  set V : ℝ → ℝ := fun x => Real.log (1 + ε * |x|) with hVdef
  have hVm : Measurable V := Real.measurable_log.comp (measurable_const.add
    (measurable_const.mul (measurable_id.norm : Measurable fun w : ℝ => ‖w‖)))
  have hV0 : ∀ x, 0 ≤ V x := fun x => Real.log_nonneg (by
    have := mul_nonneg hε0.le (abs_nonneg x); linarith)
  have hVmono : ∀ x y, |x| ≤ |y| → V x ≤ V y := fun x y h =>
    Real.log_le_log (by positivity) (by nlinarith)
  -- `V(W)` is integrable
  have hVW : Integrable (fun w => V w) Γ := by
    refine Integrable.mono' hW hVm.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 w)]
    refine Real.log_le_log (by positivity) ?_
    have := mul_le_of_le_one_left (abs_nonneg w) hε1
    linarith
  -- the one-step law
  have hker : ∀ x, ar1Kernel Γ α x = Γ.map fun w => α * x + w := fun x =>
    recursionKernel_apply Γ (measurable_ar1Step α) x
  have hstepm : ∀ x : ℝ, Measurable fun w : ℝ => α * x + w := fun x =>
    measurable_const.add measurable_id
  have hint : ∀ x, Integrable (fun w => V (α * x + w)) Γ := fun x => by
    refine Integrable.mono' ((integrable_const (V (α * x))).add hVW)
      (hVm.comp (hstepm x)).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 _)]
    exact logAbs_add_le hε0.le _ _
  have hPV : ∀ x, ∫ y, V y ∂ar1Kernel Γ α x ≤ V (α * x) + L / 4 := fun x => by
    rw [hker, integral_map (hstepm x).aemeasurable hVm.aestronglyMeasurable]
    calc ∫ w, V (α * x + w) ∂Γ ≤ ∫ w, (V (α * x) + V w) ∂Γ :=
          integral_mono (hint x) ((integrable_const _).add hVW)
            fun w => logAbs_add_le hε0.le _ _
      _ = V (α * x) + ∫ w, V w ∂Γ := by
          rw [integral_add (integrable_const _) hVW, integral_const]; simp
      _ ≤ V (α * x) + L / 4 := by linarith
  -- the drift off `C = [−r', r']`
  set r' := max r 0
  have hoff : ∀ x, r' < |x| → ∫ y, V y ∂ar1Kernel Γ α x ≤ V x - L / 4 := fun x hx => by
    have h1 : V (α * x) ≤ Real.log (1 + ε * (ρ * |x|)) := by
      refine Real.log_le_log (by positivity) ?_
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_right hαρ (abs_nonneg x)]
    have h2 := hr x ((le_max_left _ _).trans hx.le)
    have h3 := hPV x
    rw [hLdef] at h3 ⊢
    simp only [hVdef] at h1 h2 h3 ⊢
    linarith
  -- the scaled test function
  set c₄ := 4 / L with hc₄
  have hc₄pos : 0 < c₄ := by positivity
  set W : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (V x * c₄) with hWdef
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp (hVm.mul_const _)
  have hPW : ∀ x, ∫⁻ y, W y ∂ar1Kernel Γ α x =
      ENNReal.ofReal ((∫ y, V y ∂ar1Kernel Γ α x) * c₄) := fun x => by
    have hiV : Integrable V (ar1Kernel Γ α x) := by
      rw [hker, integrable_map_measure hVm.aestronglyMeasurable (hstepm x).aemeasurable]
      exact hint x
    rw [← integral_mul_const, ofReal_integral_eq_lintegral_ofReal (hiV.mul_const _)
      (Eventually.of_forall fun y => mul_nonneg (hV0 y) hc₄pos.le)]
  set C := Icc (-r') r' with hCdef
  have hmemC : ∀ x, x ∈ C ↔ |x| ≤ r' := fun x => by rw [hCdef, mem_Icc, abs_le]
  have hCpet : IsPetite (ar1Kernel Γ α) C := hpet C isCompact_Icc
  set K := V r' + L / 4 with hKdef
  set b := ENNReal.ofReal (K * c₄) + 1 with hbdef
  have hb : b ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
  have hdrift : DriftV2 (ar1Kernel Γ α) W b C := by
    intro x
    rw [hPW x]
    have hI0 : 0 ≤ ∫ y, V y ∂ar1Kernel Γ α x := integral_nonneg hV0
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx]
      refine le_trans ?_ le_add_self
      refine add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hc₄pos.le))
        le_rfl
      have hx' := (hmemC x).1 hx
      have : V (α * x) ≤ V r' := hVmono _ _ (by
        rw [abs_mul, abs_of_nonneg (le_max_right r 0)]
        nlinarith [abs_nonneg x, abs_nonneg α, hα])
      rw [hKdef]
      linarith [hPV x]
    · rw [indicator_of_notMem hx, add_zero]
      have hx' : r' < |x| := not_le.1 fun h => hx ((hmemC x).2 h)
      have h1 := hoff x hx'
      have hVx : 1 ≤ V x * c₄ := by
        rw [hc₄, ← mul_div_assoc, le_div_iff₀ hL]; linarith
      calc ENNReal.ofReal ((∫ y, V y ∂ar1Kernel Γ α x) * c₄) + 1
          ≤ ENNReal.ofReal (V x * c₄ - 1) + ENNReal.ofReal 1 := by
            rw [ENNReal.ofReal_one]
            refine add_le_add (ENNReal.ofReal_le_ofReal ?_) le_rfl
            have : (∫ y, V y ∂ar1Kernel Γ α x) * c₄ ≤ (V x - L / 4) * c₄ :=
              mul_le_mul_of_nonneg_right h1 hc₄pos.le
            have h4 : L / 4 * c₄ = 1 := by rw [hc₄]; field_simp
            rw [sub_mul, h4] at this
            linarith
        _ = W x := by rw [← ENNReal.ofReal_add (by linarith) zero_le_one, sub_add_cancel]
  have hWfin : ∀ x, W x ≠ ∞ := fun x => ENNReal.ofReal_ne_top
  refine ⟨fun K' hK' => ?_, (theorem_11_3_15 hψ).1.2 ⟨C, W, b, hCpet, hWm, hb, hWfin, hdrift⟩⟩
  obtain ⟨c, hc⟩ := hK'.isBounded.exists_norm_le
  exact theorem_11_3_11_i_regular hψ hWm hb hCpet hdrift hK'.measurableSet
    (M := ENNReal.ofReal (V c * c₄)) ENNReal.ofReal_ne_top fun y hy =>
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hVmono _ _ (by
        have := hc y hy; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self c)))
        hc₄pos.le)

/-! ### §11.4.3: the SETAR model -/

/-- **(V2) from a real drift on `ℝ`** (the form (11.41) used in §11.4): if `ΔV ≤ −1` outside
`[−R, R]`, `PV` is bounded on `[−R, R]`, `V ≥ 0` is bounded on compacta, and compact sets are
petite, then every compact set is regular and the chain is regular. -/
theorem regular_of_real_drift {P : Kernel ℝ ℝ} [IsMarkovKernel P] {ψ : Measure ℝ}
    (hψ : IsMaximalIrreducibility P ψ) (hpet : ∀ K : Set ℝ, IsCompact K → IsPetite P K)
    {V : ℝ → ℝ} (hVm : Measurable V) (hV0 : ∀ x, 0 ≤ V x) (hVint : ∀ x, Integrable V (P x))
    (hVbdd : ∀ c : ℝ, ∃ M : ℝ, ∀ x, |x| ≤ c → V x ≤ M) {R K : ℝ}
    (hout : ∀ x, R < |x| → ∫ y, V y ∂P x ≤ V x - 1) (hin : ∀ x, |x| ≤ R → ∫ y, V y ∂P x ≤ K) :
    (∀ K' : Set ℝ, IsCompact K' → IsRegularSet P ψ K') ∧ IsRegularChain P ψ := by
  set W : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (V x) with hWdef
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp hVm
  have hPW : ∀ x, ∫⁻ y, W y ∂P x = ENNReal.ofReal (∫ y, V y ∂P x) := fun x =>
    (ofReal_integral_eq_lintegral_ofReal (hVint x) (Eventually.of_forall hV0)).symm
  set C := Icc (-R) R with hCdef
  have hmemC : ∀ x, x ∈ C ↔ |x| ≤ R := fun x => by rw [hCdef, mem_Icc, abs_le]
  have hCpet : IsPetite P C := hpet C isCompact_Icc
  set b := ENNReal.ofReal K + 1 with hbdef
  have hb : b ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
  have hdrift : DriftV2 P W b C := by
    intro x
    rw [hPW x]
    have hI0 : 0 ≤ ∫ y, V y ∂P x := integral_nonneg hV0
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx]
      exact le_trans (add_le_add (ENNReal.ofReal_le_ofReal (hin x ((hmemC x).1 hx))) le_rfl)
        le_add_self
    · rw [indicator_of_notMem hx, add_zero]
      have h1 := hout x (not_le.1 fun h => hx ((hmemC x).2 h))
      calc ENNReal.ofReal (∫ y, V y ∂P x) + 1 ≤ ENNReal.ofReal (V x - 1) + ENNReal.ofReal 1 := by
            rw [ENNReal.ofReal_one]; exact add_le_add (ENNReal.ofReal_le_ofReal h1) le_rfl
        _ = W x := by rw [← ENNReal.ofReal_add (by linarith) zero_le_one, sub_add_cancel]
  refine ⟨fun K' hK' => ?_, (theorem_11_3_15 hψ).1.2 ⟨C, W, b, hCpet, hWm, hb,
    fun x => ENNReal.ofReal_ne_top, hdrift⟩⟩
  obtain ⟨c, hc⟩ := hK'.isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := hVbdd c
  exact theorem_11_3_11_i_regular hψ hWm hb hCpet hdrift hK'.measurableSet
    (M := ENNReal.ofReal M) ENNReal.ofReal_ne_top fun y hy =>
      ENNReal.ofReal_le_ofReal (hM y (by have := hc y hy; rwa [Real.norm_eq_abs] at this))

/-- The SETAR kernel at `x` is the law of `φ(j) + θ(j)x + W(j)`, `j` the regime of `x`. -/
theorem setarKernel_eq_map {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) (x : ℝ) :
    setarKernel Γ φ θ r x = (Γ (setarRegime r x)).map
      fun w => φ (setarRegime r x) + θ (setarRegime r x) * x + w := by
  ext A hA
  rw [setarKernel_apply' Γ φ θ r x hA, Measure.map_apply (measurable_const_add _) hA]
  rfl

/-- Above every threshold, the regime is the top one. -/
theorem setarRegime_of_gt {m : ℕ} (r : Fin m → ℝ) {x : ℝ} (hx : ∀ i, r i < x) :
    setarRegime r x = Fin.last m :=
  (setarRegime_eq_iff r x _).2 ⟨fun i _ => hx i, fun h => absurd h (by simp)⟩

/-- Below every threshold, the regime is the bottom one. -/
theorem setarRegime_of_le {m : ℕ} (r : Fin m → ℝ) {x : ℝ} (hx : ∀ i, x ≤ r i) :
    setarRegime r x = 0 :=
  (setarRegime_eq_iff r x _).2 ⟨fun i hi => absurd hi (by simp), fun h => hx _⟩

/-- The piecewise linear test function `V(y) = a y⁺ + b y⁻` of §11.4.3. -/
noncomputable def pwLin (a b : ℝ) (y : ℝ) : ℝ := a * max y 0 + b * max (-y) 0

/-- `V(y) = a y⁺ + b y⁻` is Lipschitz (with constant `a + b`). -/
theorem pwLin_lipschitz {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (y z : ℝ) :
    pwLin a b y ≤ pwLin a b z + (a + b) * |y - z| := by
  unfold pwLin
  have h1 : max y 0 ≤ max z 0 + |y - z| := by
    rcases le_total 0 y with hy | hy <;> rcases le_total 0 z with hz | hz <;>
      simp only [max_eq_left, max_eq_right, hy, hz] <;>
      linarith [le_abs_self (y - z), neg_abs_le (y - z)]
  have h2 : max (-y) 0 ≤ max (-z) 0 + |y - z| := by
    rcases le_total 0 y with hy | hy <;> rcases le_total 0 z with hz | hz <;>
      simp only [max_eq_left, max_eq_right, neg_nonneg, neg_nonpos, hy, hz] <;>
      linarith [le_abs_self (y - z), neg_abs_le (y - z)]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- `V ≥ 0`. -/
theorem pwLin_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (y : ℝ) : 0 ≤ pwLin a b y := by
  unfold pwLin; positivity

/-- `V(y) ≤ (a + b)|y|`. -/
theorem pwLin_le_abs {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (y : ℝ) :
    pwLin a b y ≤ (a + b) * |y| := by
  have := pwLin_lipschitz ha hb y 0
  simpa [pwLin] using this

/-- `V` is measurable. -/
theorem measurable_pwLin (a b : ℝ) : Measurable (pwLin a b) := by
  unfold pwLin
  exact (measurable_const.mul (measurable_id.max measurable_const)).add
    (measurable_const.mul (measurable_id.neg.max measurable_const))

/-- On `x ≥ 0`, `V(θx) = (a θ⁺ + b θ⁻) x`. -/
theorem pwLin_mul_of_nonneg (a b θ : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    pwLin a b (θ * x) = (a * max θ 0 + b * max (-θ) 0) * x := by
  unfold pwLin
  rcases le_total 0 θ with h | h
  · rw [max_eq_left (mul_nonneg h hx), max_eq_right (by nlinarith : -(θ * x) ≤ 0),
      max_eq_left h, max_eq_right (by linarith : -θ ≤ 0)]; ring
  · rw [max_eq_right (by nlinarith : θ * x ≤ 0), max_eq_left (by nlinarith : 0 ≤ -(θ * x)),
      max_eq_right h, max_eq_left (by linarith : 0 ≤ -θ)]; ring

/-- On `x ≤ 0`, `V(θx) = (b θ⁺ + a θ⁻)(−x)`. -/
theorem pwLin_mul_of_nonpos (a b θ : ℝ) {x : ℝ} (hx : x ≤ 0) :
    pwLin a b (θ * x) = (b * max θ 0 + a * max (-θ) 0) * -x := by
  unfold pwLin
  rcases le_total 0 θ with h | h
  · rw [max_eq_right (by nlinarith : θ * x ≤ 0), max_eq_left (by nlinarith : 0 ≤ -(θ * x)),
      max_eq_left h, max_eq_right (by linarith : -θ ≤ 0)]; ring
  · rw [max_eq_left (by nlinarith : 0 ≤ θ * x), max_eq_right (by nlinarith : -(θ * x) ≤ 0),
      max_eq_right h, max_eq_left (by linarith : 0 ≤ -θ)]; ring

/-- (11.36) gives slopes `a, b > 0` with `a θ(M)⁺ + b θ(M)⁻ < a` and `b θ(1)⁺ + a θ(1)⁻ < b` (the
book's "straightforward calculation", p. 276). -/
theorem setar_interior_slopes {θ₁ θM : ℝ} (h1 : θ₁ < 1) (hM : θM < 1) (h : θ₁ * θM < 1) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a * max θM 0 + b * max (-θM) 0 < a ∧
      b * max θ₁ 0 + a * max (-θ₁) 0 < b := by
  rcases le_total 0 θM with hM0 | hM0 <;> rcases le_total 0 θ₁ with h10 | h10
  · refine ⟨1, 1, one_pos, one_pos, ?_, ?_⟩ <;>
      simp only [max_eq_left, max_eq_right, hM0, h10, neg_nonpos] <;> linarith
  · refine ⟨1, 1 - θ₁, one_pos, by linarith, ?_, ?_⟩
    · rw [max_eq_left hM0, max_eq_right (by linarith : -θM ≤ 0)]; linarith
    · rw [max_eq_right h10, max_eq_left (by linarith : 0 ≤ -θ₁)]; linarith
  · refine ⟨1 - θM, 1, by linarith, one_pos, ?_, ?_⟩
    · rw [max_eq_right hM0, max_eq_left (by linarith : 0 ≤ -θM)]; linarith
    · rw [max_eq_left h10, max_eq_right (by linarith : -θ₁ ≤ 0)]; linarith
  · -- both slopes negative: `|θ(M)| < a/b < 1/|θ(1)|`
    rcases eq_or_lt_of_le hM0 with hMz | hMn
    · refine ⟨1, 1 - θ₁, one_pos, by linarith, ?_, ?_⟩
      · rw [hMz]; simp
      · rw [max_eq_right h10, max_eq_left (by linarith : 0 ≤ -θ₁)]; linarith
    · refine ⟨1, (-θ₁ + 1 / -θM) / 2, one_pos, ?_, ?_, ?_⟩
      · have : 0 < 1 / -θM := one_div_pos.2 (by linarith)
        linarith
      · rw [max_eq_right hM0, max_eq_left (by linarith : 0 ≤ -θM)]
        have hp : 0 < -θM := by linarith
        have : -θ₁ * -θM < 1 := by nlinarith
        have h2 : -θ₁ < 1 / -θM := by rw [lt_div_iff₀ hp]; linarith
        have h3 : (-θ₁ + 1 / -θM) / 2 * -θM < 1 / -θM * -θM := by
          apply mul_lt_mul_of_pos_right _ hp; linarith
        rw [div_mul_cancel₀ _ hp.ne'] at h3
        linarith
      · rw [max_eq_right h10, max_eq_left (by linarith : 0 ≤ -θ₁)]
        have hp : 0 < -θM := by linarith
        have h2 : -θ₁ < 1 / -θM := by
          rw [lt_div_iff₀ hp]; nlinarith
        nlinarith

/-- One step of the SETAR model for `V = pwLin a b`: `V` is integrable and
`PV(x) ≤ V(φ(j) + θ(j)x) + (a + b) E|W(j)|`, `j` the regime of `x`. -/
theorem setar_pwLin_step {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hW : ∀ j, Integrable (fun w => w) (Γ j)) (x : ℝ) :
    Integrable (pwLin a b) (setarKernel Γ φ θ r x) ∧
      ∫ y, pwLin a b y ∂setarKernel Γ φ θ r x ≤
        pwLin a b (φ (setarRegime r x) + θ (setarRegime r x) * x) +
          (a + b) * ∫ w, |w| ∂Γ (setarRegime r x) := by
  set j := setarRegime r x
  set c := φ j + θ j * x
  have hm : Measurable fun w : ℝ => c + w := measurable_const_add c
  have hb' : ∀ w, pwLin a b (c + w) ≤ pwLin a b c + (a + b) * |w| := fun w => by
    have := pwLin_lipschitz ha hb (c + w) c
    rwa [add_sub_cancel_left] at this
  have hint : Integrable (fun w => pwLin a b (c + w)) (Γ j) :=
    Integrable.mono' ((integrable_const _).add ((hW j).abs.const_mul (a + b)))
      ((measurable_pwLin a b).comp hm).aestronglyMeasurable (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pwLin_nonneg ha hb _)]; exact hb' w)
  rw [setarKernel_eq_map]
  refine ⟨(integrable_map_measure (measurable_pwLin a b).aestronglyMeasurable
    hm.aemeasurable).2 hint, ?_⟩
  rw [integral_map hm.aemeasurable (measurable_pwLin a b).aestronglyMeasurable]
  calc ∫ w, pwLin a b (c + w) ∂Γ j ≤ ∫ w, (pwLin a b c + (a + b) * |w|) ∂Γ j :=
        integral_mono hint ((integrable_const _).add ((hW j).abs.const_mul (a + b))) hb'
    _ = pwLin a b c + (a + b) * ∫ w, |w| ∂Γ j := by
        rw [integral_add (integrable_const _) ((hW j).abs.const_mul (a + b)), integral_const,
          integral_const_mul]
        simp

/-- The positive part `E[(t + g(W))⁺]` vanishes as `t → −∞`, for integrable `g(W)`. -/
theorem exists_tail_posPart_le (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {g : ℝ → ℝ}
    (hg : Integrable g Γ) (hgm : Measurable g) {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, ∀ t, t ≤ -T → ∫ w, max (t + g w) 0 ∂Γ ≤ η := by
  have hlim : Tendsto (fun n : ℕ => ∫ w, max (-(n : ℝ) + g w) 0 ∂Γ) atTop
      (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂Γ)) := by
    refine tendsto_integral_of_dominated_convergence (fun w => |g w|)
      (fun n => ((measurable_const.add hgm).max measurable_const).aestronglyMeasurable) hg.abs
      (fun n => Eventually.of_forall fun w => ?_) (Eventually.of_forall fun w => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self (g w), (n.cast_nonneg : (0 : ℝ) ≤ n)])
        (abs_nonneg _)
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_gt (g w)
      filter_upwards [eventually_ge_atTop N] with n hn
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      rw [max_eq_right (by linarith)]
  rw [integral_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (Iic_mem_nhds hη)).exists
  have hposint : ∀ s : ℝ, Integrable (fun w => max (s + g w) 0) Γ := fun s =>
    Integrable.mono' ((integrable_const |s|).add hg.abs)
      ((measurable_const.add hgm).max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        change max (s + g w) 0 ≤ |s| + |g w|
        exact max_le (by linarith [le_abs_self s, le_abs_self (g w)])
          (add_nonneg (abs_nonneg _) (abs_nonneg _)))
  refine ⟨n, fun t ht => le_trans (integral_mono_of_nonneg (Eventually.of_forall fun w =>
    le_max_right _ _) (hposint _) (Eventually.of_forall fun w => ?_)) hn⟩
  exact max_le_max (by linarith) le_rfl

/-- For zero-mean `W`: `E V(c + W) = a c + (a + b) E[(−c − W)⁺]`. -/
theorem integral_pwLin_shift_pos (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hW0 : ∫ w, w ∂Γ = 0) (a b c : ℝ) :
    ∫ w, pwLin a b (c + w) ∂Γ = a * c + (a + b) * ∫ w, max (-c + -w) 0 ∂Γ := by
  have hpos : Integrable (fun w => max (-c + -w) 0) Γ :=
    Integrable.mono' ((integrable_const |c|).add hW.abs)
      ((measurable_const.add measurable_neg).max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        change max (-c + -w) 0 ≤ |c| + |w|
        exact max_le (by linarith [neg_abs_le c, neg_abs_le w]) (by positivity))
  have hpt : ∀ w, pwLin a b (c + w) = a * c + a * w + (a + b) * max (-c + -w) 0 := fun w => by
    unfold pwLin
    rcases le_total 0 (c + w) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -(c + w) ≤ 0),
        max_eq_right (by linarith : -c + -w ≤ 0)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -(c + w)),
        max_eq_left (by linarith : 0 ≤ -c + -w)]; ring
  simp_rw [hpt]
  rw [integral_add (f := fun w => a * c + a * w) (g := fun w => (a + b) * max (-c + -w) 0)
    ((integrable_const _).add (hW.const_mul a)) (hpos.const_mul _),
    integral_add (f := fun _ => a * c) (g := fun w => a * w) (integrable_const _)
      (hW.const_mul a), integral_const, integral_const_mul, integral_const_mul, hW0]
  simp

/-- For zero-mean `W`: `E V(c + W) = −b c + (a + b) E[(c + W)⁺]`. -/
theorem integral_pwLin_shift_neg (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hW0 : ∫ w, w ∂Γ = 0) (a b c : ℝ) :
    ∫ w, pwLin a b (c + w) ∂Γ = -b * c + (a + b) * ∫ w, max (c + w) 0 ∂Γ := by
  have hpos : Integrable (fun w => max (c + w) 0) Γ :=
    Integrable.mono' ((integrable_const |c|).add hW.abs)
      ((measurable_const.add measurable_id).max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        change max (c + w) 0 ≤ |c| + |w|
        exact max_le (by linarith [le_abs_self c, le_abs_self w]) (by positivity))
  have hpt : ∀ w, pwLin a b (c + w) = -b * c + -b * w + (a + b) * max (c + w) 0 := fun w => by
    unfold pwLin
    rcases le_total 0 (c + w) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -(c + w) ≤ 0)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -(c + w))]; ring
  simp_rw [hpt]
  rw [integral_add (f := fun w => -b * c + -b * w) (g := fun w => (a + b) * max (c + w) 0)
    ((integrable_const _).add (hW.const_mul _)) (hpos.const_mul _),
    integral_add (f := fun _ => -b * c) (g := fun w => -b * w) (integrable_const _)
      (hW.const_mul _), integral_const, integral_const_mul, integral_const_mul, hW0]
  simp

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **The drift at `+∞`** for `V = a x⁺ + b x⁻`: either the top regime contracts
(`θ(M) < 1` with `a θ(M)⁺ + b θ(M)⁻ < a`) or it is a unit-slope random walk pushed down by its
constant (`θ(M) = 1`, `a φ(M) ≤ −2`, zero-mean noise). Then `PV ≤ V − 1` far to the right. -/
theorem setar_top_drift {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (htop : (θ (Fin.last m) < 1 ∧
        a * max (θ (Fin.last m)) 0 + b * max (-θ (Fin.last m)) 0 < a) ∨
      (θ (Fin.last m) = 1 ∧ a * φ (Fin.last m) ≤ -2)) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ x, T < x →
      ∫ y, pwLin a b y ∂setarKernel Γ φ θ r x ≤ pwLin a b x - 1 := by
  set M := Fin.last m
  set Tr := ∑ i, |r i|
  have hTr : ∀ i, r i ≤ Tr := fun i => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |r i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))
  have hTr0 : 0 ≤ Tr := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hreg : ∀ x, Tr < x → setarRegime r x = M := fun x hx =>
    setarRegime_of_gt r fun i => (hTr i).trans_lt hx
  have hV : ∀ x, 0 ≤ x → pwLin a b x = a * x := fun x hx => by
    have := pwLin_mul_of_nonneg a b 1 hx; simpa using this
  rcases htop with ⟨-, hκ⟩ | ⟨hθ1, hφ⟩
  · set κ := a * max (θ M) 0 + b * max (-θ M) 0
    set D := (a + b) * (|φ M| + ∫ w, |w| ∂Γ M)
    refine ⟨max Tr ((1 + D) / (a - κ)), le_max_of_le_left hTr0, fun x hx => ?_⟩
    have hx1 : Tr < x := (le_max_left _ _).trans_lt hx
    have hx0 : 0 ≤ x := hTr0.trans hx1.le
    have h := (setar_pwLin_step Γ φ θ r ha.le hb.le hW x).2
    rw [hreg x hx1] at h
    have hsh := pwLin_lipschitz ha.le hb.le (φ M + θ M * x) (θ M * x)
    rw [add_sub_cancel_right] at hsh
    have hθx := pwLin_mul_of_nonneg a b (θ M) hx0
    have hgap : 0 < a - κ := by linarith
    have hxR : (1 + D) / (a - κ) < x := (le_max_right _ _).trans_lt hx
    rw [div_lt_iff₀ hgap] at hxR
    rw [hV x hx0]
    nlinarith
  · obtain ⟨T₀, hT₀⟩ := exists_tail_posPart_le (Γ M) (hW M).neg measurable_neg
      (η := 1 / (a + b)) (by positivity)
    refine ⟨max Tr (max (T₀ - φ M) 0), le_max_of_le_left hTr0, fun x hx => ?_⟩
    have hx1 : Tr < x := (le_max_left _ _).trans_lt hx
    have hx0 : 0 ≤ x := hTr0.trans hx1.le
    have hxT : T₀ - φ M < x := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hx
    rw [setarKernel_eq_map, hreg x hx1, integral_map (measurable_const_add _).aemeasurable
      (measurable_pwLin a b).aestronglyMeasurable, hθ1, one_mul,
      integral_pwLin_shift_pos (Γ M) (hW M) (hW0 M), hV x hx0]
    have htail := hT₀ (-(φ M + x)) (by linarith)
    have hab : (a + b) * ∫ w, max (-(φ M + x) + -w) 0 ∂Γ M ≤ 1 := by
      calc (a + b) * ∫ w, max (-(φ M + x) + -w) 0 ∂Γ M ≤ (a + b) * (1 / (a + b)) :=
            mul_le_mul_of_nonneg_left htail (by linarith)
        _ = 1 := by field_simp
    nlinarith

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **The drift at `−∞`**, the mirror image of `setar_top_drift`. -/
theorem setar_bot_drift {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hbot : (θ 0 < 1 ∧ b * max (θ 0) 0 + a * max (-θ 0) 0 < b) ∨ (θ 0 = 1 ∧ 2 ≤ b * φ 0)) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ x, x < -T →
      ∫ y, pwLin a b y ∂setarKernel Γ φ θ r x ≤ pwLin a b x - 1 := by
  set Tr := ∑ i, |r i|
  have hTr : ∀ i, -Tr ≤ r i := fun i => by
    have := Finset.single_le_sum (f := fun i => |r i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    linarith [neg_abs_le (r i)]
  have hTr0 : 0 ≤ Tr := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hreg : ∀ x, x < -Tr → setarRegime r x = 0 := fun x hx =>
    setarRegime_of_le r fun i => (hx.trans_le (hTr i)).le
  have hV : ∀ x, x ≤ 0 → pwLin a b x = b * -x := fun x hx => by
    have := pwLin_mul_of_nonpos a b 1 hx; simpa using this
  rcases hbot with ⟨-, hκ⟩ | ⟨hθ1, hφ⟩
  · set κ := b * max (θ 0) 0 + a * max (-θ 0) 0
    set D := (a + b) * (|φ 0| + ∫ w, |w| ∂Γ 0)
    refine ⟨max Tr ((1 + D) / (b - κ)), le_max_of_le_left hTr0, fun x hx => ?_⟩
    have hx1 : x < -Tr := hx.trans_le (neg_le_neg (le_max_left _ _))
    have hx0 : x ≤ 0 := by linarith
    have h := (setar_pwLin_step Γ φ θ r ha.le hb.le hW x).2
    rw [hreg x hx1] at h
    have hsh := pwLin_lipschitz ha.le hb.le (φ 0 + θ 0 * x) (θ 0 * x)
    rw [add_sub_cancel_right] at hsh
    have hθx := pwLin_mul_of_nonpos a b (θ 0) hx0
    have hgap : 0 < b - κ := by linarith
    have hxR : (1 + D) / (b - κ) < -x := by
      have := neg_lt_neg hx; rw [neg_neg] at this; exact (le_max_right _ _).trans_lt this
    rw [div_lt_iff₀ hgap] at hxR
    rw [hV x hx0]
    nlinarith
  · obtain ⟨T₀, hT₀⟩ := exists_tail_posPart_le (Γ 0) (hW 0) measurable_id
      (η := 1 / (a + b)) (by positivity)
    refine ⟨max Tr (max (T₀ + φ 0) 0), le_max_of_le_left hTr0, fun x hx => ?_⟩
    have hx1 : x < -Tr := hx.trans_le (neg_le_neg (le_max_left _ _))
    have hx0 : x ≤ 0 := by linarith
    have hxT : x < -(T₀ + φ 0) :=
      hx.trans_le (neg_le_neg ((le_max_left _ _).trans (le_max_right _ _)))
    rw [setarKernel_eq_map, hreg x hx1, integral_map (measurable_const_add _).aemeasurable
      (measurable_pwLin a b).aestronglyMeasurable, hθ1, one_mul,
      integral_pwLin_shift_neg (Γ 0) (hW 0) (hW0 0), hV x hx0]
    have htail := hT₀ (φ 0 + x) (by linarith)
    have hab : (a + b) * ∫ w, max (φ 0 + x + w) 0 ∂Γ 0 ≤ 1 := by
      calc (a + b) * ∫ w, max (φ 0 + x + w) 0 ∂Γ 0 ≤ (a + b) * (1 / (a + b)) :=
            mul_le_mul_of_nonneg_left htail (by linarith)
        _ = 1 := by field_simp
    nlinarith

/-- A contracting end: `a θ⁺ + b θ⁻ < a` for `a = b θ⁻ + 1` when `θ < 1`. -/
theorem contract_slope {θ b : ℝ} (hθ : θ < 1) :
    (b * max (-θ) 0 + 1) * max θ 0 + b * max (-θ) 0 < b * max (-θ) 0 + 1 := by
  rcases le_total 0 θ with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -θ ≤ 0)]; simp; linarith
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -θ)]; simp

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **SETAR regularity from the drift at both ends.** Under (SETAR1)–(SETAR2), if the test function
`V = a x⁺ + b x⁻` drifts down at `+∞` and at `−∞` (`setar_top_drift`, `setar_bot_drift`), then
every compact set is regular and the chain is regular. -/
theorem setar_regular_of_ends (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (htop : (θ (Fin.last m) < 1 ∧
        a * max (θ (Fin.last m)) 0 + b * max (-θ (Fin.last m)) 0 < a) ∨
      (θ (Fin.last m) = 1 ∧ a * φ (Fin.last m) ≤ -2))
    (hbot : (θ 0 < 1 ∧ b * max (θ 0) 0 + a * max (-θ 0) 0 < b) ∨ (θ 0 = 1 ∧ 2 ≤ b * φ 0)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    (∀ K : Set ℝ, IsCompact K → IsRegularSet (setarKernel Γ φ θ r) volume K) ∧
      IsRegularChain (setarKernel Γ φ θ r) volume := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  obtain ⟨_, hψ, hsmall, -⟩ := proposition_6_3_6 Γ φ θ r h1 h2
  obtain ⟨T₁, hT₁0, hT₁⟩ := setar_top_drift Γ φ θ r ha hb hW hW0 htop
  obtain ⟨T₂, hT₂0, hT₂⟩ := setar_bot_drift Γ φ θ r ha hb hW hW0 hbot
  set R := max T₁ T₂
  have hstep := setar_pwLin_step Γ φ θ r ha.le hb.le hW
  set E : Fin (m + 1) → ℝ := fun j => (a + b) * ∫ w, |w| ∂Γ j with hEdef
  have hE0 : ∀ j, 0 ≤ E j := fun j => mul_nonneg (by linarith)
    (integral_nonneg fun w => abs_nonneg w)
  set K := ∑ j, ((a + b) * (|φ j| + |θ j| * R) + E j) with hKdef
  refine regular_of_real_drift hψ (fun K' hK' => (hsmall K' hK').isPetite) (measurable_pwLin a b)
    (pwLin_nonneg ha.le hb.le) (fun x => (hstep x).1) (fun c => ⟨(a + b) * c, fun x hx =>
      (pwLin_le_abs ha.le hb.le x).trans (mul_le_mul_of_nonneg_left hx (by linarith))⟩)
    (R := R) (K := K) (fun x hx => ?_) (fun x hx => ?_)
  · rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0] at hx
      exact hT₁ x ((le_max_left _ _).trans_lt hx)
    · rw [abs_of_neg hx0] at hx
      exact hT₂ x (by linarith [le_max_right T₁ T₂])
  · set j := setarRegime r x
    have h := (hstep x).2
    have hb1 : pwLin a b (φ j + θ j * x) ≤ (a + b) * (|φ j| + |θ j| * R) := by
      refine (pwLin_le_abs ha.le hb.le _).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      calc |φ j + θ j * x| ≤ |φ j| + |θ j| * |x| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ |φ j| + |θ j| * R := by gcongr
    have hterm : (a + b) * (|φ j| + |θ j| * R) + E j ≤ K :=
      Finset.single_le_sum (f := fun j => (a + b) * (|φ j| + |θ j| * R) + E j)
        (fun i _ => add_nonneg (mul_nonneg (by linarith) (add_nonneg (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) ((abs_nonneg x).trans hx)))) (hE0 i)) (Finset.mem_univ j)
    simp only [hEdef] at hterm
    linarith

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **Proposition 11.4.5** for the regions (11.36)–(11.39) (MT p. 276): under (SETAR1)–(SETAR2),
the SETAR model is regular, and every compact set is regular, if (11.36) `θ(1) < 1, θ(M) < 1,
θ(1)θ(M) < 1`; (11.37) `θ(1) = 1, θ(M) < 1, φ(1) > 0`; (11.38) `θ(1) < 1, θ(M) = 1,
φ(M) < 0`; or (11.39) `θ(1) = θ(M) = 1, φ(M) < 0 < φ(1)`. -/
theorem setar_regular_36_39 (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hint : (θ 0 < 1 ∧ θ (Fin.last m) < 1 ∧ θ 0 * θ (Fin.last m) < 1) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) < 1 ∧ 0 < φ 0) ∨
      (θ 0 < 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) < 0) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) < 0 ∧ 0 < φ 0)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    (∀ K : Set ℝ, IsCompact K → IsRegularSet (setarKernel Γ φ θ r) volume K) ∧
      IsRegularChain (setarKernel Γ φ θ r) volume := by
  rcases hint with ⟨hθ1, hθM, hθ⟩ | ⟨hθ1, hθM, hφ⟩ | ⟨hθ1, hθM, hφ⟩ | ⟨hθ1, hθM, hφM, hφ1⟩
  · obtain ⟨a, b, ha, hb, hκM, hκ1⟩ := setar_interior_slopes hθ1 hθM hθ
    exact setar_regular_of_ends Γ φ θ r h1 h2 hW hW0 ha hb (Or.inl ⟨hθM, hκM⟩)
      (Or.inl ⟨hθ1, hκ1⟩)
  · set b := 2 / φ 0
    have hb : 0 < b := by positivity
    exact setar_regular_of_ends Γ φ θ r h1 h2 hW hW0 (a := b * max (-θ (Fin.last m)) 0 + 1)
      (by positivity) hb (Or.inl ⟨hθM, contract_slope hθM⟩)
      (Or.inr ⟨hθ1, by rw [div_mul_cancel₀ _ hφ.ne']⟩)
  · set a := 2 / -φ (Fin.last m)
    have ha : 0 < a := div_pos two_pos (by linarith)
    refine setar_regular_of_ends Γ φ θ r h1 h2 hW hW0 (b := a * max (-θ 0) 0 + 1) ha
      (by positivity) (Or.inr ⟨hθM, ?_⟩) (Or.inl ⟨hθ1, contract_slope hθ1⟩)
    have hne : -φ (Fin.last m) ≠ 0 := by linarith
    have : a * φ (Fin.last m) = -2 := by
      rw [show a * φ (Fin.last m) = -(a * -φ (Fin.last m)) by ring, div_mul_cancel₀ _ hne]
    linarith
  · set a := 2 / -φ (Fin.last m)
    have ha : 0 < a := div_pos two_pos (by linarith)
    set b := 2 / φ 0
    have hb : 0 < b := by positivity
    have hne : -φ (Fin.last m) ≠ 0 := by linarith
    have hM : a * φ (Fin.last m) = -2 := by
      rw [show a * φ (Fin.last m) = -(a * -φ (Fin.last m)) by ring, div_mul_cancel₀ _ hne]
    exact setar_regular_of_ends Γ φ θ r h1 h2 hW hW0 ha hb (Or.inr ⟨hθM, hM.le⟩)
      (Or.inr ⟨hθ1, by rw [div_mul_cancel₀ _ hφ1.ne']⟩)

/-! ### §11.5.2: the SETAR model on the margins -/

/-- The test function of Proposition 11.5.5, `V(y) = max(y + c, d − b y)`: the book's
`V_{cd}` (11.59) with `a = 1`, written as a maximum so that no bump `I_{kR}` is needed. -/
noncomputable def kinkV (b c d : ℝ) (y : ℝ) : ℝ := max (y + c) (-b * y + d)

/-- `V` is measurable. -/
theorem measurable_kinkV (b c d : ℝ) : Measurable (kinkV b c d) :=
  (measurable_id.add measurable_const).max (measurable_const.mul measurable_id |>.add
    measurable_const)

/-- `V(y) ≤ (1 + b)|y| + c + d`. -/
theorem kinkV_le {b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (y : ℝ) :
    kinkV b c d y ≤ (1 + b) * |y| + c + d := by
  unfold kinkV
  refine max_le ?_ ?_
  · nlinarith [le_abs_self y, abs_nonneg y]
  · nlinarith [neg_abs_le y, abs_nonneg y, mul_le_mul_of_nonneg_left (neg_abs_le y) hb]

/-- `V ≥ 0`. -/
theorem kinkV_nonneg {b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (y : ℝ) :
    0 ≤ kinkV b c d y := by
  unfold kinkV
  rcases le_total 0 y with h | h
  · exact le_max_of_le_left (by linarith)
  · exact le_max_of_le_right (by nlinarith)

/-- `V` is Lipschitz with constant `1 + b`. -/
theorem kinkV_lipschitz (b c d y z : ℝ) (hb : 0 ≤ b) :
    |kinkV b c d y - kinkV b c d z| ≤ (1 + b) * |y - z| := by
  unfold kinkV
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [show y + c - (z + c) = y - z by ring]; nlinarith [abs_nonneg (y - z)]
  · rw [show -b * y + d - (-b * z + d) = -b * (y - z) by ring, abs_mul, abs_neg,
      abs_of_nonneg hb]; nlinarith [abs_nonneg (y - z)]

/-- `E[α + βW] = α` for zero-mean `W`. -/
theorem integral_affine_zeroMean (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hW0 : ∫ w, w ∂Γ = 0) (α β : ℝ) :
    ∫ w, (α + β * w) ∂Γ = α := by
  rw [integral_add (f := fun _ => α) (g := fun w => β * w) (integrable_const _)
    (hW.const_mul β), integral_const, integral_const_mul, hW0]
  simp


/-- The increment bound at `+∞` for Proposition 11.5.5. -/
theorem kink_top_incr {b c d δ φM θM x : ℝ} (hb : 0 < b) (hcd : d - c = δ)
    (hδ : δ = b * φM) (hbθ : b * θM = -1) (hθx : θM * x ≤ 0) (hVx : kinkV b c d x = x + c) (w : ℝ) :
    |kinkV b c d (φM + θM * x + w) - kinkV b c d x| ≤ (1 + b) * (|φM| + |w|) + |δ| + b * |w| := by
  set Y := φM + θM * x + w
  have hA : -b * Y + d ≤ kinkV b c d Y := le_max_right _ _
  have hY : (1 + b) * Y ≤ (1 + b) * (|φM| + |w|) := by
    have : Y ≤ |φM| + |w| := by
      simp only [Y]; linarith [le_abs_self φM, le_abs_self w]
    exact mul_le_mul_of_nonneg_left this (by linarith)
  have hB : kinkV b c d Y ≤ -b * Y + d + ((1 + b) * (|φM| + |w|) + |δ|) := by
    refine max_le ?_ ?_
    · have : Y + c - (-b * Y + d) = (1 + b) * Y - δ := by rw [← hcd]; ring
      linarith [neg_le_abs δ]
    · have : 0 ≤ (1 + b) * (|φM| + |w|) := by positivity
      linarith [abs_nonneg δ]
  have hC : -b * Y + d - kinkV b c d x = -b * w := by
    rw [hVx]
    have : -b * (θM * x) = x := by rw [← mul_assoc, neg_mul, hbθ]; ring
    have e : -b * Y = -b * φM + -b * (θM * x) + -b * w := by simp only [Y]; ring
    rw [e, this]
    linarith [hcd]
  have hsplit : kinkV b c d Y - kinkV b c d x =
      (kinkV b c d Y - (-b * Y + d)) + (-b * Y + d - kinkV b c d x) := by ring
  rw [hsplit, hC]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (by linarith), abs_mul, abs_neg, abs_of_nonneg hb.le]
  linarith

/-- The increment bound at `−∞` for Proposition 11.5.5. -/
theorem kink_bot_incr {b c d δ φ1 θ1 x : ℝ} (hb : 0 < b) (hcd : d - c = δ)
    (hbθ : b = -θ1) (hθx : 0 ≤ θ1 * x) (hVx : kinkV b c d x = -b * x + d) (w : ℝ) :
    |kinkV b c d (φ1 + θ1 * x + w) - kinkV b c d x| ≤
      (1 + b) * (|φ1| + |w|) + |δ| + (|φ1| + |w| + |δ|) := by
  set Y := φ1 + θ1 * x + w
  have hA : Y + c ≤ kinkV b c d Y := le_max_left _ _
  have hY : -((1 + b) * (|φ1| + |w|)) ≤ (1 + b) * Y := by
    have : -(|φ1| + |w|) ≤ Y := by
      simp only [Y]; linarith [neg_abs_le φ1, neg_abs_le w]
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 1 + b)
    linarith
  have hB : kinkV b c d Y ≤ Y + c + ((1 + b) * (|φ1| + |w|) + |δ|) := by
    refine max_le ?_ ?_
    · have : 0 ≤ (1 + b) * (|φ1| + |w|) := by positivity
      linarith [abs_nonneg δ]
    · have : -b * Y + d - (Y + c) = δ - (1 + b) * Y := by rw [← hcd]; ring
      linarith [le_abs_self δ]
  have hC : Y + c - kinkV b c d x = φ1 + w - δ := by
    rw [hVx]; simp only [Y]; rw [hbθ]; linarith [hcd]
  have hsplit : kinkV b c d Y - kinkV b c d x =
      (kinkV b c d Y - (Y + c)) + (Y + c - kinkV b c d x) := by ring
  rw [hsplit, hC]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (by linarith)]
  have : |φ1 + w - δ| ≤ |φ1| + |w| + |δ| :=
    (abs_sub _ _).trans (by linarith [abs_add_le φ1 w])
  linarith

/-- The increment bound on `[−R, R]` for Proposition 11.5.5. -/
theorem kink_mid_incr {b c d φj θj x R : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : |x| ≤ R) (w : ℝ) :
    |kinkV b c d (φj + θj * x + w) - kinkV b c d x| ≤
      (1 + b) * (|φj| + |θj| * R + |w|) + c + d + ((1 + b) * R + c + d) := by
  have hY : |φj + θj * x + w| ≤ |φj| + |θj| * R + |w| := by
    have h1 : |θj * x| ≤ |θj| * R := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    linarith [abs_add_le (φj + θj * x) w, abs_add_le φj (θj * x)]
  have h1 := kinkV_le hb hc hd (φj + θj * x + w)
  have h2 := kinkV_le hb hc hd x
  have h3 := kinkV_nonneg hb hc hd (φj + θj * x + w)
  have h4 := kinkV_nonneg hb hc hd x
  have e1 : (1 + b) * |φj + θj * x + w| ≤ (1 + b) * (|φj| + |θj| * R + |w|) :=
    mul_le_mul_of_nonneg_left hY (by linarith)
  have e2 : (1 + b) * |x| ≤ (1 + b) * R := mul_le_mul_of_nonneg_left hx (by linarith)
  rw [abs_le]; constructor <;> linarith

/-- Bookkeeping for the constants of Proposition 11.5.5 (top end). -/
theorem kink_K_le {b w' p t R c d δ S : ℝ} (hb : 0 ≤ b) (hw : 0 ≤ w') (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hR : 0 ≤ R) (hc : 0 ≤ c) (hd : 0 ≤ d) (hδ : 0 ≤ δ)
    (hS : (1 + b) * (p + t * R) + p ≤ S) :
    (1 + b) * (p + w') + δ + b * w' ≤
      S + (1 + b) * R + 2 * (c + d) + 2 * δ + (3 * (1 + b) + 1) * w' := by
  have e1 : 0 ≤ (1 + b) * (t * R) := by positivity
  have e2 : 0 ≤ (1 + b) * R := by positivity
  nlinarith

/-- Bookkeeping for the constants of Proposition 11.5.5 (bottom end). -/
theorem kink_K_le' {b w' p t R c d δ S : ℝ} (hb : 0 ≤ b) (hw : 0 ≤ w') (ht : 0 ≤ t)
    (hR : 0 ≤ R) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hS : (1 + b) * (p + t * R) + p ≤ S) :
    (1 + b) * (p + w') + δ + (p + w' + δ) ≤
      S + (1 + b) * R + 2 * (c + d) + 2 * δ + (3 * (1 + b) + 1) * w' := by
  have e1 : 0 ≤ (1 + b) * (t * R) := by positivity
  have e2 : 0 ≤ (1 + b) * R := by positivity
  nlinarith

/-- Bookkeeping for the constants of Proposition 11.5.5 (centre). -/
theorem kink_K_le'' {b w' p t R c d δ S : ℝ} (hb : 0 ≤ b) (hw : 0 ≤ w') (hp : 0 ≤ p)
    (hδ : 0 ≤ δ)
    (hS : (1 + b) * (p + t * R) + p ≤ S) :
    (1 + b) * (p + t * R + w') + c + d + ((1 + b) * R + c + d) ≤
      S + (1 + b) * R + 2 * (c + d) + 2 * δ + (3 * (1 + b) + 1) * w' := by
  nlinarith

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **Proposition 11.5.5** (MT p. 283), in the case the book proves: under (SETAR1)–(SETAR2), if
`θ(1) < 0`, `θ(1)θ(M) = 1` and `φ(M) + θ(M)φ(1) ≤ 0` (this contains the margin (11.49)), the
SETAR model is non-positive (null). -/
theorem proposition_11_5_5 (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hθ1 : θ 0 < 0) (hθ : θ 0 * θ (Fin.last m) = 1)
    (hφ : φ (Fin.last m) + θ (Fin.last m) * φ 0 ≤ 0) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsNull (setarKernel Γ φ θ r) volume := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  obtain ⟨_, hψ, -, -⟩ := proposition_6_3_6 Γ φ θ r h1 h2
  set M := Fin.last m
  set b := -θ 0 with hbdef
  have hb : 0 < b := by linarith
  have hbθ : b * θ M = -1 := by rw [hbdef, neg_mul, hθ]
  have hθM : θ M < 0 := by
    by_contra h; push Not at h; nlinarith
  set δ := b * φ M with hδdef
  have hδ : δ ≤ φ 0 := by
    have := mul_le_mul_of_nonneg_left hφ hb.le
    rw [mul_add, ← mul_assoc, hbθ, mul_zero] at this
    linarith
  set c := max 0 (-δ) with hcdef
  set d := max 0 δ with hddef
  have hc : 0 ≤ c := le_max_left _ _
  have hd : 0 ≤ d := le_max_left _ _
  have hcd : d - c = δ := by
    rcases le_total 0 δ with h | h
    · rw [hddef, hcdef, max_eq_right h, max_eq_left (by linarith : -δ ≤ 0)]; ring
    · rw [hddef, hcdef, max_eq_left h, max_eq_right (by linarith : 0 ≤ -δ)]; ring
  set V := kinkV b c d with hVdef
  have hVm : Measurable V := measurable_kinkV b c d
  have hV1 : ∀ y, y + c ≤ V y := fun y => le_max_left _ _
  have hV2 : ∀ y, -b * y + d ≤ V y := fun y => le_max_right _ _
  -- thresholds and the size of the central set
  set T := ∑ i, |r i| with hTdef
  have hTr : ∀ i, |r i| ≤ T := fun i =>
    Finset.single_le_sum (f := fun i => |r i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => abs_nonneg _
  set R := max T (|δ| / (1 + b)) + 1 with hRdef
  have hRT : T < R := by rw [hRdef]; linarith [le_max_left T (|δ| / (1 + b))]
  have hRδ : |δ| / (1 + b) < R := by rw [hRdef]; linarith [le_max_right T (|δ| / (1 + b))]
  have hR0 : 0 < R := lt_of_le_of_lt hT0 hRT
  have hregM : ∀ x, R < x → setarRegime r x = M := fun x hx =>
    setarRegime_of_gt r fun i => (le_abs_self _).trans_lt ((hTr i).trans_lt (hRT.trans hx))
  have hreg0 : ∀ x, x < -R → setarRegime r x = 0 := fun x hx =>
    setarRegime_of_le r fun i => by linarith [neg_abs_le (r i), hTr i]
  have hVtop : ∀ x, R < x → V x = x + c := fun x hx => by
    refine max_eq_left ?_
    have h1' : |δ| < (1 + b) * x := by
      rw [div_lt_iff₀ (by linarith)] at hRδ; nlinarith
    linarith [le_abs_self δ]
  have hVbot : ∀ x, x < -R → V x = -b * x + d := fun x hx => by
    refine max_eq_right ?_
    have h1' : |δ| < (1 + b) * -x := by
      rw [div_lt_iff₀ (by linarith)] at hRδ; nlinarith
    linarith [neg_abs_le δ]
  -- the one-step law
  have hmap : ∀ x, setarKernel Γ φ θ r x = (Γ (setarRegime r x)).map
      fun w => φ (setarRegime r x) + θ (setarRegime r x) * x + w := setarKernel_eq_map Γ φ θ r
  have hVi : ∀ j (c0 : ℝ), Integrable (fun w => V (c0 + w)) (Γ j) := fun j c0 =>
    Integrable.mono' (((integrable_const ((1 + b) * |c0| + c + d)).add
      ((hW j).abs.const_mul (1 + b))))
      (hVm.comp (measurable_const_add c0)).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (kinkV_nonneg hb.le hc hd _)]
        refine (kinkV_le hb.le hc hd _).trans ?_
        change (1 + b) * |c0 + w| + c + d ≤ (1 + b) * |c0| + c + d + (1 + b) * |w|
        nlinarith [abs_add_le c0 w])
  have hPV : ∀ x, ∫ y, V y ∂setarKernel Γ φ θ r x =
      ∫ w, V (φ (setarRegime r x) + θ (setarRegime r x) * x + w) ∂Γ (setarRegime r x) :=
    fun x => by
      rw [hmap, integral_map (measurable_const_add _).aemeasurable hVm.aestronglyMeasurable]
  set C := Icc (-R) R with hCdef
  have hnotC : ∀ x, x ∉ C → R < x ∨ x < -R := fun x hx => by
    simp only [hCdef, mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · exact Or.inr h
    · exact Or.inl h
  -- (11.42): `ΔV ≥ 0` off `C`
  have hdrift : ∀ x ∉ C, V x ≤ ∫ y, V y ∂setarKernel Γ φ θ r x := fun x hx => by
    rw [hPV]
    rcases hnotC x hx with hx | hx
    · rw [hregM x hx, hVtop x hx]
      calc x + c = -b * (φ M + θ M * x) + d + -b * 0 := by
            have : -b * (θ M * x) = x := by rw [← mul_assoc, neg_mul, hbθ]; ring
            rw [mul_add, this]; linarith
        _ = ∫ w, (-b * (φ M + θ M * x) + d + -b * w) ∂Γ M := by
            rw [integral_affine_zeroMean (Γ M) (hW M) (hW0 M)]; ring
        _ ≤ _ := integral_mono ((integrable_const _).add ((hW M).const_mul _))
            (hVi M _) fun w => by
              have := hV2 (φ M + θ M * x + w); simp only at this ⊢; linarith
    · rw [hreg0 x hx, hVbot x hx]
      calc -b * x + d ≤ φ 0 + θ 0 * x + c + 1 * 0 := by
            rw [hbdef]; linarith
        _ = ∫ w, (φ 0 + θ 0 * x + c + 1 * w) ∂Γ 0 := by
            rw [integral_affine_zeroMean (Γ 0) (hW 0) (hW0 0)]; ring
        _ ≤ _ := integral_mono ((integrable_const _).add ((hW 0).const_mul _))
            (hVi 0 _) fun w => by
              have := hV1 (φ 0 + θ 0 * x + w); simp only at this ⊢; linarith
  -- (11.43): increments bounded in mean
  set K₁ := 3 * (1 + b) + 1 with hK₁
  set K₀ := ∑ j, ((1 + b) * (|φ j| + |θ j| * R) + |φ j|) + (1 + b) * R + 2 * (c + d) +
    2 * |δ| with hK₀
  have hterm : ∀ j, (1 + b) * (|φ j| + |θ j| * R) + |φ j| ≤
      ∑ j, ((1 + b) * (|φ j| + |θ j| * R) + |φ j|) := fun j =>
    Finset.single_le_sum (f := fun j => (1 + b) * (|φ j| + |θ j| * R) + |φ j|)
      (fun i _ => by positivity) (Finset.mem_univ j)
  have hVle := kinkV_le hb.le hc hd
  have hVnn := kinkV_nonneg hb.le hc hd
  have hpt : ∀ x w, |V (φ (setarRegime r x) + θ (setarRegime r x) * x + w) - V x| ≤
      K₀ + K₁ * |w| := fun x w => by
    have hw := abs_nonneg w
    by_cases hxR : R < x
    · rw [hregM x hxR]
      have h := kink_top_incr (φM := φ M) hb hcd hδdef hbθ
        (mul_nonpos_of_nonpos_of_nonneg hθM.le (hR0.trans hxR).le) (hVtop x hxR) w
      have := hterm M
      exact h.trans (kink_K_le hb.le hw (abs_nonneg _) (abs_nonneg _) hR0.le hc hd
        (abs_nonneg δ) this)
    by_cases hxR' : x < -R
    · rw [hreg0 x hxR']
      have h := kink_bot_incr (φ1 := φ 0) hb hcd hbdef
        (mul_nonneg_of_nonpos_of_nonpos hθ1.le (by linarith)) (hVbot x hxR') w
      have := hterm 0
      exact h.trans (kink_K_le' hb.le hw (abs_nonneg _) hR0.le hc hd this)
    · have hx : |x| ≤ R := abs_le.2 ⟨by linarith, by linarith⟩
      have := hterm (setarRegime r x)
      exact (kink_mid_incr (φj := φ (setarRegime r x)) (θj := θ (setarRegime r x)) hb.le hc hd
        hx w).trans (kink_K_le'' hb.le hw (abs_nonneg _) (abs_nonneg δ) this)
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; linarith
  set B := ENNReal.ofReal (K₀ + K₁ * ∑ j, ∫ w, |w| ∂Γ j) with hBdef
  have hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂setarKernel Γ φ θ r x ≤ B := fun x => by
    set j := setarRegime r x
    have hm : Measurable fun y => ‖V y - V x‖ₑ := (hVm.sub measurable_const).enorm
    rw [hmap, lintegral_map hm (measurable_const_add _)]
    have hint : Integrable (fun w : ℝ => K₀ + K₁ * |w|) (Γ j) :=
      (integrable_const _).add ((hW j).abs.const_mul _)
    calc ∫⁻ w, ‖V (φ j + θ j * x + w) - V x‖ₑ ∂Γ j
        ≤ ∫⁻ w, ENNReal.ofReal (K₀ + K₁ * |w|) ∂Γ j := lintegral_mono fun w => by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (hpt x w)
      _ = ENNReal.ofReal (∫ w, (K₀ + K₁ * |w|) ∂Γ j) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w =>
            add_nonneg (by
              have := kink_K_le'' (c := c) (d := d) (R := R) hb.le (le_refl (0 : ℝ))
                (abs_nonneg (φ j)) (abs_nonneg δ) (hterm j)
              have h0 : 0 ≤ (1 + b) * (|φ j| + |θ j| * R + 0) + c + d + ((1 + b) * R + c + d) := by
                positivity
              linarith) (mul_nonneg hK₁0 (abs_nonneg w)))).symm
      _ ≤ B := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_add (integrable_const _) ((hW j).abs.const_mul _), integral_const,
            integral_const_mul]
          simp only [probReal_univ, smul_eq_mul, one_mul]
          have : ∫ w, |w| ∂Γ j ≤ ∑ j, ∫ w, |w| ∂Γ j :=
            Finset.single_le_sum (f := fun j => ∫ w, |w| ∂Γ j)
              (fun i _ => integral_nonneg fun w => abs_nonneg w) (Finset.mem_univ j)
          nlinarith
  -- `C ∈ B⁺` and `C⁺ ∈ B⁺`
  have hψC : 0 < volume C := by
    rw [hCdef, Real.volume_Icc]; simp; linarith
  set N := max R ((1 + b) * R + c + d) with hNdef
  have hCp : Ioi N ⊆ {x | ∀ y ∈ C, V y < V x} := fun x hx y hy => by
    have hxN : N < x := hx
    have hxR : R < x := (le_max_left _ _).trans_lt hxN
    have hy' : |y| ≤ R := abs_le.2 ⟨hy.1, hy.2⟩
    have h1 := hVle y
    have h2 : (1 + b) * |y| ≤ (1 + b) * R := mul_le_mul_of_nonneg_left hy' (by linarith)
    rw [hVtop x hxR]
    have := (le_max_right R ((1 + b) * R + c + d)).trans_lt hxN
    linarith
  have hψCp : 0 < volume {x | ∀ y ∈ C, V y < V x} :=
    lt_of_lt_of_le (by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top) (measure_mono hCp)
  exact theorem_11_5_2 hψ hVm measurableSet_Icc hψC hdrift ENNReal.ofReal_ne_top hinc hψCp


/-! ### §11.4.3: the SETAR model in the region (11.40) -/

/-- `max(y + c, d − by) = (d − by) + ((1 + b)y − δ)⁺` when `d − c = δ`. -/
theorem kinkV_eq_top {b c d δ : ℝ} (hcd : d - c = δ) (y : ℝ) :
    kinkV b c d y = -b * y + d + max ((1 + b) * y - δ) 0 := by
  unfold kinkV
  rw [← max_add_add_left, add_zero]
  congr 1; rw [← hcd]; ring

/-- `max(y + c, d − by) = (y + c) + (δ − (1 + b)y)⁺` when `d − c = δ`. -/
theorem kinkV_eq_bot {b c d δ : ℝ} (hcd : d - c = δ) (y : ℝ) :
    kinkV b c d y = y + c + max (δ - (1 + b) * y) 0 := by
  unfold kinkV
  rw [← max_add_add_left, add_zero, max_comm]
  congr 1; rw [← hcd]; ring

/-- `E[(t + βW)⁺]` is integrable. -/
theorem integrable_posPart_affine (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (t β : ℝ) :
    Integrable (fun w => max (t + β * w) 0) Γ :=
  Integrable.mono' ((integrable_const |t|).add (hW.abs.const_mul |β|))
    ((measurable_const.add (measurable_const.mul measurable_id)).max
      measurable_const).aestronglyMeasurable
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      change max (t + β * w) 0 ≤ |t| + |β| * |w|
      refine max_le ?_ (by positivity)
      rw [← abs_mul]; linarith [le_abs_self t, le_abs_self (β * w)])

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **Proposition 11.4.5**, the region (11.40): `θ(1) < 0`, `θ(1)θ(M) = 1` and
`φ(M) + θ(M)φ(1) > 0`. The chain jumps from one end to the other; the book passes to the two-step
kernel, but one step suffices for the kinked test function `max(x + c, d − bx)`, `b = −θ(1)`,
with `d − c` the midpoint of `(φ(1), bφ(M))`: the drift is `−(bφ(M) − φ(1))/2 + o(1)` at both
ends. -/
theorem setar_regular_eq_11_40 (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hθ1 : θ 0 < 0) (hθ : θ 0 * θ (Fin.last m) = 1)
    (hφ : 0 < φ (Fin.last m) + θ (Fin.last m) * φ 0) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    (∀ K : Set ℝ, IsCompact K → IsRegularSet (setarKernel Γ φ θ r) volume K) ∧
      IsRegularChain (setarKernel Γ φ θ r) volume := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  obtain ⟨_, hψ, hsmall, -⟩ := proposition_6_3_6 Γ φ θ r h1 h2
  set M := Fin.last m
  set b := -θ 0 with hbdef
  have hb : 0 < b := by linarith
  have hbθ : b * θ M = -1 := by rw [hbdef, neg_mul, hθ]
  have hθM : θ M = -1 / b := by field_simp; linarith
  set η := (b * φ M - φ 0) / 2 with hηdef
  have hη : 0 < η := by
    have := mul_pos hb hφ
    rw [mul_add, ← mul_assoc, hbθ] at this
    rw [hηdef]; linarith
  set δ := (φ 0 + b * φ M) / 2 with hδdef
  set c := max 0 (-δ) with hcdef
  set d := max 0 δ with hddef
  have hc : 0 ≤ c := le_max_left _ _
  have hd : 0 ≤ d := le_max_left _ _
  have hcd : d - c = δ := by
    rcases le_total 0 δ with h | h
    · rw [hddef, hcdef, max_eq_right h, max_eq_left (by linarith : -δ ≤ 0)]; ring
    · rw [hddef, hcdef, max_eq_left h, max_eq_right (by linarith : 0 ≤ -δ)]; ring
  set V := kinkV b c d with hVdef
  have hVm : Measurable V := measurable_kinkV b c d
  have hmap : ∀ x, setarKernel Γ φ θ r x = (Γ (setarRegime r x)).map
      fun w => φ (setarRegime r x) + θ (setarRegime r x) * x + w := setarKernel_eq_map Γ φ θ r
  have hVi : ∀ j (c0 : ℝ), Integrable (fun w => V (c0 + w)) (Γ j) := fun j c0 =>
    Integrable.mono' (((integrable_const ((1 + b) * |c0| + c + d)).add
      ((hW j).abs.const_mul (1 + b))))
      (hVm.comp (measurable_const_add c0)).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (kinkV_nonneg hb.le hc hd _)]
        refine (kinkV_le hb.le hc hd _).trans ?_
        change (1 + b) * |c0 + w| + c + d ≤ (1 + b) * |c0| + c + d + (1 + b) * |w|
        nlinarith [abs_add_le c0 w])
  have hPV : ∀ x, ∫ y, V y ∂setarKernel Γ φ θ r x =
      ∫ w, V (φ (setarRegime r x) + θ (setarRegime r x) * x + w) ∂Γ (setarRegime r x) :=
    fun x => by
      rw [hmap, integral_map (measurable_const_add _).aemeasurable hVm.aestronglyMeasurable]
  -- the tails
  obtain ⟨T₁, hT₁⟩ := exists_tail_posPart_le (Γ M) ((hW M).const_mul (1 + b))
    (measurable_const.mul measurable_id) (η := η / 2) (by positivity)
  obtain ⟨T₂, hT₂⟩ := exists_tail_posPart_le (Γ 0) ((hW 0).const_mul (-(1 + b)))
    (measurable_const.mul measurable_id) (η := η / 2) (by positivity)
  set T := ∑ i, |r i| with hTdef
  have hTr : ∀ i, |r i| ≤ T := fun i =>
    Finset.single_le_sum (f := fun i => |r i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => abs_nonneg _
  set X₁ := b * (|φ M| + |T₁| + |δ|) with hX₁
  set X₂ := (|δ| + (1 + b) * |φ 0| + |T₂|) / b with hX₂
  set R := max (max T (|δ| / (1 + b))) (max X₁ X₂) + 1 with hRdef
  have hRT : T < R := by
    rw [hRdef]; linarith [le_max_left T (|δ| / (1 + b)),
      le_max_left (max T (|δ| / (1 + b))) (max X₁ X₂)]
  have hRδ : |δ| / (1 + b) < R := by
    rw [hRdef]; linarith [le_max_right T (|δ| / (1 + b)),
      le_max_left (max T (|δ| / (1 + b))) (max X₁ X₂)]
  have hRX₁ : X₁ < R := by
    rw [hRdef]; linarith [le_max_left X₁ X₂, le_max_right (max T (|δ| / (1 + b))) (max X₁ X₂)]
  have hRX₂ : X₂ < R := by
    rw [hRdef]; linarith [le_max_right X₁ X₂, le_max_right (max T (|δ| / (1 + b))) (max X₁ X₂)]
  have hR0 : 0 < R := lt_of_le_of_lt hT0 hRT
  have hregM : ∀ x, R < x → setarRegime r x = M := fun x hx =>
    setarRegime_of_gt r fun i => (le_abs_self _).trans_lt ((hTr i).trans_lt (hRT.trans hx))
  have hreg0 : ∀ x, x < -R → setarRegime r x = 0 := fun x hx =>
    setarRegime_of_le r fun i => by linarith [neg_abs_le (r i), hTr i]
  have hVtop : ∀ x, R < x → V x = x + c := fun x hx => by
    refine max_eq_left ?_
    have h1' : |δ| < (1 + b) * x := by
      rw [div_lt_iff₀ (by linarith)] at hRδ; nlinarith
    linarith [le_abs_self δ]
  have hVbot : ∀ x, x < -R → V x = -b * x + d := fun x hx => by
    refine max_eq_right ?_
    have h1' : |δ| < (1 + b) * -x := by
      rw [div_lt_iff₀ (by linarith)] at hRδ; nlinarith
    linarith [neg_abs_le δ]
  -- the drift at the two ends
  have hout : ∀ x, R < |x| → ∫ y, V y ∂setarKernel Γ φ θ r x ≤ V x - η / 2 := by
    intro x hx
    rw [hPV]
    rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0] at hx
      rw [hregM x hx, hVtop x hx]
      have hsplit : ∀ w, V (φ M + θ M * x + w) =
          (-b * (φ M + θ M * x) + d + -b * w) + max (((1 + b) * (φ M + θ M * x) - δ) +
            (1 + b) * w) 0 := fun w => by
        rw [hVdef, kinkV_eq_top hcd]; ring_nf
      simp_rw [hsplit]
      rw [integral_add (f := fun w => -b * (φ M + θ M * x) + d + -b * w)
          (g := fun w => max (((1 + b) * (φ M + θ M * x) - δ) + (1 + b) * w) 0)
          ((integrable_const _).add ((hW M).const_mul _))
          (integrable_posPart_affine (Γ M) (hW M) _ _),
        integral_affine_zeroMean (Γ M) (hW M) (hW0 M)]
      have ht : (1 + b) * (φ M + θ M * x) - δ ≤ -T₁ := by
        have hxX : X₁ < x := hRX₁.trans hx
        rw [hθM]
        have e : (1 + b) * (φ M + -1 / b * x) = (1 + b) * φ M - (1 + b) * (x / b) := by ring
        rw [e]
        have hxb : |φ M| + |T₁| + |δ| < x / b := by rw [lt_div_iff₀ hb]; linarith
        have h4 : (1 + b) * (|φ M| + |T₁| + |δ|) ≤ (1 + b) * (x / b) :=
          mul_le_mul_of_nonneg_left hxb.le (by linarith)
        have h5 : (1 + b) * φ M ≤ (1 + b) * |φ M| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
        have h6 : 0 ≤ b * (|T₁| + |δ|) := by positivity
        have e3 : (1 + b) * (|φ M| + |T₁| + |δ|) = (1 + b) * |φ M| + (|T₁| + |δ|) +
          b * (|T₁| + |δ|) := by ring
        linarith [le_abs_self T₁, neg_abs_le δ]
      have htail := hT₁ _ ht
      have e2 : -b * (φ M + θ M * x) + d = x + c + (δ - b * φ M) := by
        have : -b * (θ M * x) = x := by rw [← mul_assoc, neg_mul, hbθ]; ring
        rw [mul_add, this]; linarith
      rw [e2]
      have : δ - b * φ M = -η := by rw [hδdef, hηdef]; ring
      linarith
    · rw [abs_of_neg hx0] at hx
      have hx' : x < -R := by linarith
      rw [hreg0 x hx', hVbot x hx']
      have hsplit : ∀ w, V (φ 0 + θ 0 * x + w) =
          (φ 0 + θ 0 * x + c + 1 * w) + max ((δ - (1 + b) * (φ 0 + θ 0 * x)) +
            -(1 + b) * w) 0 := fun w => by
        rw [hVdef, kinkV_eq_bot hcd]; ring_nf
      simp_rw [hsplit]
      rw [integral_add (f := fun w => φ 0 + θ 0 * x + c + 1 * w)
          (g := fun w => max ((δ - (1 + b) * (φ 0 + θ 0 * x)) + -(1 + b) * w) 0)
          ((integrable_const _).add ((hW 0).const_mul _))
          (integrable_posPart_affine (Γ 0) (hW 0) _ _),
        integral_affine_zeroMean (Γ 0) (hW 0) (hW0 0)]
      have ht : δ - (1 + b) * (φ 0 + θ 0 * x) ≤ -T₂ := by
        have hxX : X₂ < -x := hRX₂.trans hx
        rw [hX₂, div_lt_iff₀ hb] at hxX
        have e : θ 0 * x = b * -x := by rw [hbdef]; ring
        rw [e]
        have hx0' : 0 < -x := by linarith
        have h3 : b * -x ≤ (1 + b) * (b * -x) := by
          have : 0 ≤ b * (b * -x) := by positivity
          linarith
        have h5 : -((1 + b) * |φ 0|) ≤ (1 + b) * φ 0 := by
          have := mul_le_mul_of_nonneg_left (neg_abs_le (φ 0)) (by linarith : (0 : ℝ) ≤ 1 + b)
          linarith
        have e3 : (1 + b) * (φ 0 + b * -x) = (1 + b) * φ 0 + (1 + b) * (b * -x) := by ring
        have e4 : -x * b = b * -x := by ring
        rw [e4] at hxX
        linarith [le_abs_self δ, le_abs_self T₂]
      have htail := hT₂ _ ht
      have e2 : φ 0 + θ 0 * x + c = -b * x + d + (φ 0 - δ) := by
        rw [hbdef]; linarith
      rw [e2]
      have : φ 0 - δ = -η := by rw [hδdef, hηdef]; ring
      linarith
  -- the bound on `[−R, R]`
  have hcen : ∀ j (c0 : ℝ), ∫ w, V (c0 + w) ∂Γ j ≤
      (1 + b) * |c0| + c + d + (1 + b) * ∫ w, |w| ∂Γ j := fun j c0 => by
    calc ∫ w, V (c0 + w) ∂Γ j ≤ ∫ w, ((1 + b) * |c0| + c + d + (1 + b) * |w|) ∂Γ j :=
          integral_mono (hVi j c0) ((integrable_const _).add ((hW j).abs.const_mul _))
            fun w => by
              have := kinkV_le hb.le hc hd (c0 + w)
              have h2 : (1 + b) * |c0 + w| ≤ (1 + b) * (|c0| + |w|) :=
                mul_le_mul_of_nonneg_left (abs_add_le _ _) (by linarith)
              change V (c0 + w) ≤ (1 + b) * |c0| + c + d + (1 + b) * |w|
              linarith
      _ = (1 + b) * |c0| + c + d + (1 + b) * ∫ w, |w| ∂Γ j := by
          rw [integral_add (integrable_const _) ((hW j).abs.const_mul _), integral_const,
            integral_const_mul]
          simp
  set K := ∑ j, ((1 + b) * (|φ j| + |θ j| * R) + c + d + (1 + b) * ∫ w, |w| ∂Γ j) with hKdef
  have hin : ∀ x, |x| ≤ R → ∫ y, V y ∂setarKernel Γ φ θ r x ≤ K := fun x hx => by
    rw [hPV]
    set j := setarRegime r x
    refine (hcen j _).trans ?_
    have hc0 : |φ j + θ j * x| ≤ |φ j| + |θ j| * R := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
    have hterm := Finset.single_le_sum
      (f := fun j => (1 + b) * (|φ j| + |θ j| * R) + c + d + (1 + b) * ∫ w, |w| ∂Γ j)
      (fun i _ => by
        have : 0 ≤ ∫ w, |w| ∂Γ i := integral_nonneg fun w => abs_nonneg w
        have : 0 ≤ (1 + b) * (|φ i| + |θ i| * R) := by positivity
        positivity) (Finset.mem_univ j)
    have := mul_le_mul_of_nonneg_left hc0 (by linarith : (0 : ℝ) ≤ 1 + b)
    linarith
  -- rescale the drift to `−1`
  have hη2 : 0 < 2 / η := by positivity
  refine regular_of_real_drift hψ (fun K' hK' => (hsmall K' hK').isPetite)
    (V := fun y => V y * (2 / η)) (hVm.mul_const _)
    (fun y => mul_nonneg (kinkV_nonneg hb.le hc hd y) hη2.le)
    (fun x => by
      rw [hmap, integrable_map_measure (hVm.mul_const _).aestronglyMeasurable
        (measurable_const_add _).aemeasurable]
      exact (hVi _ _).mul_const _)
    (fun c' => ⟨((1 + b) * c' + c + d) * (2 / η), fun x hx => by
      refine mul_le_mul_of_nonneg_right ((kinkV_le hb.le hc hd x).trans ?_) hη2.le
      have := mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ 1 + b)
      linarith⟩)
    (R := R) (K := K * (2 / η)) (fun x hx => ?_) (fun x hx => ?_)
  · rw [integral_mul_const]
    have h := hout x hx
    have := mul_le_mul_of_nonneg_right h hη2.le
    have e : (V x - η / 2) * (2 / η) = V x * (2 / η) - 1 := by field_simp
    linarith
  · rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (hin x hx) hη2.le

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **Proposition 11.4.5** (MT p. 276): under (SETAR1)–(SETAR2), the SETAR model is regular, and
every compact set is regular, in the interior (11.36)–(11.40) of the parameter space. -/
theorem proposition_11_4_5 (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hint : (θ 0 < 1 ∧ θ (Fin.last m) < 1 ∧ θ 0 * θ (Fin.last m) < 1) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) < 1 ∧ 0 < φ 0) ∨
      (θ 0 < 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) < 0) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) < 0 ∧ 0 < φ 0) ∨
      (θ 0 < 0 ∧ θ 0 * θ (Fin.last m) = 1 ∧
        0 < φ (Fin.last m) + θ (Fin.last m) * φ 0)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    (∀ K : Set ℝ, IsCompact K → IsRegularSet (setarKernel Γ φ θ r) volume K) ∧
      IsRegularChain (setarKernel Γ φ θ r) volume := by
  rcases hint with h | h | h | h | ⟨hθ1, hθ, hφ⟩
  · exact setar_regular_36_39 Γ φ θ r h1 h2 hW hW0 (Or.inl h)
  · exact setar_regular_36_39 Γ φ θ r h1 h2 hW hW0 (Or.inr (Or.inl h))
  · exact setar_regular_36_39 Γ φ θ r h1 h2 hW hW0 (Or.inr (Or.inr (Or.inl h)))
  · exact setar_regular_36_39 Γ φ θ r h1 h2 hW hW0 (Or.inr (Or.inr (Or.inr h)))
  · exact setar_regular_eq_11_40 Γ φ θ r h1 h2 hW hW0 hθ1 hθ hφ

end MeynTweedie.GeneralizedDrift
