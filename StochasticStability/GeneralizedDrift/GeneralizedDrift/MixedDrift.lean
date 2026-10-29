/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.HistoryDependentDrift
import GeneralizedDrift.PositivityPn
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Mixed drift conditions (MT §19.3.1)

Meyn and Tweedie, §19.3.1, pp. 498–502. `V : X → ℝ` is a non-negative test function with
increments bounded in mean, (19.46): `∫ P(x, dy) |V(y) − V(x)| ≤ B < ∞` for every `x`, written
with the extended norm. `ΔV = driftR P V` is the (real) drift `∫ P(x, dy) V(y) − V(x)`.

**Preliminaries.**
* `lintegral_enorm_pow_le`: `∫ Pᵏ(x, dy) |V(y)| ≤ |V(x)| + kB`, so `V` is `Pᵏ(x, ·)`-integrable
  (`integrable_pow_of_increments`); `abs_driftR_le`: `|ΔV| ≤ B`; `measurable_driftR`.
* `integral_pow_driftR` ((19.49), p. 499): `∫ Pᵏ(x, dy) ΔV(y) = Pᵏ⁺¹V(x) − PᵏV(x)`, so that
  `sum_integral_pow_driftR`: `Σ_{k=1}^n ∫ Pᵏ ΔV = P^{n+1}V(x) − PV(x)`.
* `eventually_cesaro_drift_ge` ((19.50), p. 499): for every `η > 0`, eventually
  `n⁻¹ Σ_{k=1}^n ∫ Pᵏ(x, dy) ΔV(y) ≥ −η`.

**Results.**
* **Theorem 19.3.1** (`theorem_19_3_1`, p. 499): (19.48) for some `x` and a petite `C` makes the
  chain positive. `not_tendsto_pow_of_mixedDrift` is the core of the proof: (19.48) is
  incompatible with `Pⁿ(x, C) → 0`.
* **Theorem 19.3.2** (`theorem_19_3_2`, p. 500): for an invariant probability `π`,
  `∫ π(dy) ΔV(y) = 0`. The proof is the book's: `M_z(x) = ∫ P(x, dy) [z^{V(x)} − z^{V(y)}]/(1 − z)`
  has `π(M_z) = 0`, `|M_z| ≤ 2B` for `z ∈ [½, 1)` (`abs_rpow_sub_rpow_le`,
  `abs_log_le_two_mul`) and `M_z → ΔV` as `z ↑ 1` (`tendsto_rpow_slope`).
* **Theorem 19.3.3** (`theorem_19_3_3`, p. 501): for a positive `ψ`-irreducible chain and a
  sublevel set `C = {V ≤ b}` with `C, Cᶜ ∈ B⁺(X)`, `∫_{Cᶜ} π(dw) ΔV(w) < 0` (19.56). The steps are
  the balanced flow (19.63) (`flow_balance`), the positivity of the flow
  (`flow_pos`), and `∫_C π(dw) ΔV(w) > 0` (19.64) (`setIntegral_driftR_pos`).
  `tendsto_cesaro_setIntegral_driftR` is (19.57): off a `ψ`-null set the averages
  `n⁻¹ Σ_{k=1}^n ∫_{Cᶜ} Pᵏ(x, dy) ΔV(y)` converge to `∫_{Cᶜ} π ΔV`, by the Cesàro ergodic theorem
  `tendsto_cesaro_integral_of_isPositive` (Theorem 13.3.4 (ii) and `tendsto_cesaro_of_phase`,
  Cesàro averages from phase averages); `theorem_19_3_3_iff`:
  "(19.48) is necessary and sufficient for positivity".

**Hypotheses.**
* Theorem 19.3.1 uses Theorem 18.2.2 (a null chain has `Pⁿ(x, C) → 0` for petite `C`), copied in
  `PositivityPn`; the space is countably generated, as there.
* (19.48), `lim inf n⁻¹ Σ_{k=1}^n ∫_{Cᶜ} Pᵏ(x, dy) ΔV(y) < 0`, is used in the equivalent form
  "for some `η > 0`, the averages are `≤ −η` frequently" (the averages are bounded by `B`).
* Theorem 19.3.2 needs only an invariant probability `π`: neither irreducibility nor positivity
  in the book's sense is used.

**Corrections.**
* In the proof of Theorem 19.3.1 the book writes (19.50) with `Pⁿ` in the sum; it is `Pᵏ`.

**Elsewhere.** §19.3.2–19.3.3: Theorem 19.3.4 is in `LadderDrift`, the example (19.78)–(19.80)
in `LadderExample`, and Theorem 19.3.5 (the GI/G/1 queue) in `GIG1Drift`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### Preliminaries -/

/-- `∫ Pᵏ(x, dy) |V(y)| ≤ |V(x)| + kB` under (19.46). -/
theorem lintegral_enorm_pow_le (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ}
    (hV : Measurable V) {B : ℝ≥0∞} (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) (x : X)
    (k : ℕ) : ∫⁻ y, ‖V y‖ₑ ∂(P ^ k) x ≤ ‖V x‖ₑ + k * B := by
  induction k with
  | zero => rw [pow_zero_apply, lintegral_dirac' x hV.enorm]; simp
  | succ k ih =>
    have := isMarkovKernel_pow P k
    rw [pow_add_eq, pow_one, Kernel.lintegral_comp _ _ _ hV.enorm]
    calc ∫⁻ y, ∫⁻ z, ‖V z‖ₑ ∂P y ∂(P ^ k) x ≤ ∫⁻ y, (‖V y‖ₑ + B) ∂(P ^ k) x := by
          refine lintegral_mono fun y => ?_
          calc ∫⁻ z, ‖V z‖ₑ ∂P y ≤ ∫⁻ z, (‖V z - V y‖ₑ + ‖V y‖ₑ) ∂P y :=
                lintegral_mono fun z => by
                  calc ‖V z‖ₑ = ‖(V z - V y) + V y‖ₑ := by rw [sub_add_cancel]
                    _ ≤ _ := enorm_add_le _ _
            _ = ∫⁻ z, ‖V z - V y‖ₑ ∂P y + ‖V y‖ₑ := by
                rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ,
                  mul_one]
            _ ≤ ‖V y‖ₑ + B := by rw [add_comm]; exact add_le_add le_rfl (hinc y)
      _ = ∫⁻ y, ‖V y‖ₑ ∂(P ^ k) x + B := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ‖V x‖ₑ + k * B + B := add_le_add ih le_rfl
      _ = ‖V x‖ₑ + (k + 1 : ℕ) * B := by push_cast; ring

/-- Under (19.46), `V` is integrable for every `Pᵏ(x, ·)`. -/
theorem integrable_pow_of_increments (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ}
    (hV : Measurable V) {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B)
    (x : X) (k : ℕ) : Integrable V ((P ^ k) x) := by
  have := isMarkovKernel_pow P k
  refine ⟨hV.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  exact (lintegral_enorm_pow_le P hV hinc x k).trans_lt (ENNReal.add_lt_top.2 ⟨enorm_lt_top,
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top k) hB.lt_top⟩)

/-- `ΔV` is measurable. -/
theorem measurable_driftR (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ}
    (hV : Measurable V) : Measurable (driftR P V) :=
  (measurable_kfunR P hV).sub hV

/-- `ΔV(x) = ∫ P(x, dy) (V(y) − V(x))`. -/
theorem driftR_eq_integral (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ}
    (hV : Measurable V) {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B)
    (x : X) : driftR P V x = ∫ y, (V y - V x) ∂P x := by
  rw [driftR, integral_sub (integrable_of_increments hV hB hinc x) (integrable_const _),
    integral_const, smul_eq_mul, probReal_univ, one_mul]

/-- `|ΔV| ≤ B` under (19.46). -/
theorem abs_driftR_le (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ}
    (hV : Measurable V) {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B)
    (x : X) : |driftR P V x| ≤ B.toReal := by
  rw [driftR_eq_integral P hV hB hinc x, ← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono hB ?_)
  calc ∫⁻ a, ENNReal.ofReal ‖V a - V x‖ ∂P x = ∫⁻ a, ‖V a - V x‖ₑ ∂P x :=
        lintegral_congr fun a => ofReal_norm _
    _ ≤ B := hinc x

/-- `ΔV` is integrable for every finite measure. -/
theorem integrable_driftR (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ}
    (hV : Measurable V) {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B)
    (μ : Measure X) [IsFiniteMeasure μ] : Integrable (driftR P V) μ :=
  Integrable.of_bound (measurable_driftR P hV).aestronglyMeasurable B.toReal
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_driftR_le P hV hB hinc x)

/-- (19.49), MT p. 499: `∫ Pᵏ(x, dy) ΔV(y) = P^{k+1}V(x) − PᵏV(x)`. -/
theorem integral_pow_driftR (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ}
    (hV : Measurable V) {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B)
    (x : X) (k : ℕ) :
    ∫ y, driftR P V y ∂(P ^ k) x = ∫ y, V y ∂(P ^ (k + 1)) x - ∫ y, V y ∂(P ^ k) x := by
  have := isMarkovKernel_pow P k
  have hVk := integrable_pow_of_increments P hV hB hinc x k
  have hD := integrable_driftR P hV hB hinc ((P ^ k) x)
  have hK : Integrable (kfunR P V) ((P ^ k) x) := by
    have : kfunR P V = fun y => driftR P V y + V y := funext fun y => by simp [driftR, kfunR]
    rw [this]; exact hD.add hVk
  have hcomp : ∫ y, V y ∂(P ^ (k + 1)) x = ∫ y, kfunR P V y ∂(P ^ k) x := by
    have hint : Integrable V ((P ∘ₖ (P ^ k)) x) := by
      have h := integrable_pow_of_increments P hV hB hinc x (k + 1)
      rwa [pow_add_eq, pow_one] at h
    rw [pow_add_eq, pow_one]
    exact Kernel.integral_comp hint
  rw [hcomp, ← integral_sub hK hVk]
  rfl

/-- `Σ_{k=1}^n ∫ Pᵏ(x, dy) ΔV(y) = P^{n+1}V(x) − PV(x)`. -/
theorem sum_integral_pow_driftR (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ}
    (hV : Measurable V) {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B)
    (x : X) (n : ℕ) :
    ∑ k ∈ range n, ∫ y, driftR P V y ∂(P ^ (k + 1)) x =
      ∫ y, V y ∂(P ^ (n + 1)) x - ∫ y, V y ∂(P ^ 1) x := by
  simp_rw [integral_pow_driftR P hV hB hinc x]
  exact sum_range_sub (fun k => ∫ y, V y ∂(P ^ (k + 1)) x) n

/-- **(19.50)** (MT p. 499): for `V ≥ 0` with (19.46), for every `η > 0`, eventually
`n⁻¹ Σ_{k=1}^n ∫ Pᵏ(x, dy) ΔV(y) ≥ −η`, i.e. `lim inf ≥ 0`. -/
theorem eventually_cesaro_drift_ge (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ}
    (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) (x : X) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, -η ≤ (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ y, driftR P V y ∂(P ^ (k + 1)) x := by
  set a := ∫ y, V y ∂(P ^ 1) x
  obtain ⟨N, hN⟩ := exists_nat_gt (a / η)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [sum_integral_pow_driftR P hV hB hinc x n]
  have hpos : 0 ≤ ∫ y, V y ∂(P ^ (n + 1)) x := integral_nonneg hV0
  have hlt : a < η * n := by
    have : a / η < n := hN.trans (by exact_mod_cast (by omega : N < n))
    rwa [div_lt_iff₀ hη, mul_comm] at this
  rw [inv_mul_eq_div, le_div_iff₀ hn0]
  linarith

/-! ### Theorem 19.3.1 -/

/-- **The core of Theorem 19.3.1** (MT p. 499): under (19.46), if for some `η > 0` the averages
`n⁻¹ Σ_{k=1}^n ∫_{Cᶜ} Pᵏ(x, dy) ΔV(y)` are `≤ −η` infinitely often ((19.48)), then `Pⁿ(x, C)`
does not tend to `0`: the set `C` is not null. -/
theorem not_tendsto_pow_of_mixedDrift (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ}
    (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) {C : Set X} (hC : MeasurableSet C) {x : X}
    {η : ℝ} (hη : 0 < η)
    (h48 : ∃ᶠ n : ℕ in atTop,
      (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ y in Cᶜ, driftR P V y ∂(P ^ (k + 1)) x ≤ -η) :
    ¬ Tendsto (fun n => ((P ^ n) x C).toReal) atTop (𝓝 0) := by
  intro hnull
  set d := B.toReal
  have hD := abs_driftR_le P hV hB hinc
  -- the Cesàro averages of `∫_C Pᵏ ΔV` tend to `0`
  have hC0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n,
      ∫ y in C, driftR P V y ∂(P ^ (k + 1)) x) atTop (𝓝 0) := by
    have hu : Tendsto (fun k : ℕ => ∫ y in C, driftR P V y ∂(P ^ (k + 1)) x) atTop (𝓝 0) := by
      have hb : Tendsto (fun k : ℕ => d * ((P ^ (k + 1)) x C).toReal) atTop (𝓝 0) := by
        simpa using (hnull.comp (tendsto_add_atTop_nat 1)).const_mul d
      refine squeeze_zero_norm (fun k => ?_) hb
      have := isMarkovKernel_pow P (k + 1)
      calc ‖∫ y in C, driftR P V y ∂(P ^ (k + 1)) x‖ ≤ d * ((P ^ (k + 1)) x).real C := by
            refine (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun y _ => ?_)
            rw [Real.norm_eq_abs]; exact hD y
        _ = d * ((P ^ (k + 1)) x C).toReal := rfl
    exact hu.cesaro
  have hsplit : ∀ n : ℕ, ∑ k ∈ range n, ∫ y in Cᶜ, driftR P V y ∂(P ^ (k + 1)) x =
      ∑ k ∈ range n, ∫ y, driftR P V y ∂(P ^ (k + 1)) x -
        ∑ k ∈ range n, ∫ y in C, driftR P V y ∂(P ^ (k + 1)) x := fun n => by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    have := isMarkovKernel_pow P (k + 1)
    rw [eq_sub_iff_add_eq, add_comm,
      integral_add_compl hC (integrable_driftR P hV hB hinc ((P ^ (k + 1)) x))]
  have hev := eventually_cesaro_drift_ge P hV hV0 hB hinc x (half_pos hη)
  have hev2 := (hC0.eventually (gt_mem_nhds (half_pos hη)))
  obtain ⟨n, hn1, hn2, hn3⟩ := (h48.and_eventually (hev.and hev2)).exists
  rw [hsplit, mul_sub] at hn1
  linarith

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 19.3.1** (MT p. 499): for a `ψ`-irreducible chain and `V ≥ 0` with increments
bounded in mean (19.46), if for some `x` and some petite `C` the averages
`n⁻¹ Σ_{k=1}^n ∫_{Cᶜ} Pᵏ(x, dy) ΔV(y)` have negative `lim inf` (19.48) (here: `≤ −η`
infinitely often), the chain is positive. If it were null, Theorem 18.2.2 would give
`Pⁿ(x, C) → 0` (`IsNull.tendsto_pow_of_isPetite`), contradicting
`not_tendsto_pow_of_mixedDrift`. -/
theorem theorem_19_3_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ} (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) {C : Set X}
    (hC : IsPetite P C) {x : X} {η : ℝ} (hη : 0 < η)
    (h48 : ∃ᶠ n : ℕ in atTop,
      (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ y in Cᶜ, driftR P V y ∂(P ^ (k + 1)) x ≤ -η) :
    IsPositive P ψ := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  rcases isPositive_or_isNull hψ with h | h
  · exact h
  · have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (h.tendsto_pow_of_isPetite hC x)
    rw [ENNReal.toReal_zero] at h0
    exact absurd h0 (not_tendsto_pow_of_mixedDrift P hV hV0 hB hinc hCm hη h48)

/-! ### Theorem 19.3.2 -/

omit [MeasurableSpace X] in
/-- `|eᵘ − eʷ| ≤ |u − w|` for `u, w ≤ 0`. -/
theorem abs_exp_sub_exp_le {u w : ℝ} (hu : u ≤ 0) (hw : w ≤ 0) :
    |Real.exp u - Real.exp w| ≤ |u - w| := by
  wlog h : u ≤ w generalizing u w
  · rw [abs_sub_comm, abs_sub_comm u]; exact this hw hu (le_of_not_ge h)
  have h1 : Real.exp u ≤ Real.exp w := Real.exp_le_exp.2 h
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  have h2 : 1 + (u - w) ≤ Real.exp (u - w) := by linarith [Real.add_one_le_exp (u - w)]
  have h3 : Real.exp u = Real.exp w * Real.exp (u - w) := by rw [← Real.exp_add]; ring_nf
  have h4 : Real.exp w ≤ 1 := Real.exp_le_one_iff.2 hw
  have hA := mul_nonneg (Real.exp_pos w).le (sub_nonneg.2 h2)
  have hB := mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 h)
  nlinarith [hA, hB, h3]

omit [MeasurableSpace X] in
/-- (19.52), MT p. 500: for `0 < z ≤ 1` and `a, b ≥ 0`, `|z^a − z^b| ≤ |log z| |a − b|`. -/
theorem abs_rpow_sub_rpow_le {z a b : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |z ^ a - z ^ b| ≤ |Real.log z| * |a - b| := by
  have hl : Real.log z ≤ 0 := Real.log_nonpos hz0.le hz1
  rw [Real.rpow_def_of_pos hz0, Real.rpow_def_of_pos hz0]
  refine (abs_exp_sub_exp_le (mul_nonpos_of_nonpos_of_nonneg hl ha)
    (mul_nonpos_of_nonpos_of_nonneg hl hb)).trans (le_of_eq ?_)
  rw [← mul_sub, abs_mul]

omit [MeasurableSpace X] in
/-- `|log z| ≤ 2(1 − z)` for `½ ≤ z ≤ 1` (from (19.53)). -/
theorem abs_log_le_two_mul {z : ℝ} (hz : 1 / 2 ≤ z) (hz1 : z ≤ 1) :
    |Real.log z| ≤ 2 * (1 - z) := by
  have hz0 : 0 < z := by linarith
  rw [abs_of_nonpos (Real.log_nonpos hz0.le hz1), ← Real.log_inv]
  refine (Real.log_le_sub_one_of_pos (inv_pos.2 hz0)).trans ?_
  rw [inv_eq_one_div, div_sub_one hz0.ne', div_le_iff₀ hz0]
  nlinarith

/-- The points `z_n = 1 − 1/(n + 2) ∈ [½, 1)`, increasing to `1`. -/
noncomputable def zSeq (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

omit [MeasurableSpace X] in
/-- `½ ≤ z_n < 1`. -/
theorem zSeq_mem (n : ℕ) : 1 / 2 ≤ zSeq n ∧ zSeq n < 1 := by
  have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  refine ⟨?_, by unfold zSeq; linarith⟩
  unfold zSeq
  have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  linarith

omit [MeasurableSpace X] in
/-- `z_n → 1` with `z_n ≠ 1`. -/
theorem tendsto_zSeq : Tendsto zSeq atTop (𝓝[≠] (1 : ℝ)) := by
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp only [Function.comp, Nat.cast_add, Nat.cast_one]
    ring_nf
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (zSeq_mem n).2.ne⟩
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  rw [sub_zero] at this
  exact this

omit [MeasurableSpace X] in
/-- (19.54), MT p. 500: `[z^a − z^b]/(1 − z) → b − a` as `z ↑ 1`, along `z_n`. -/
theorem tendsto_rpow_slope (a b : ℝ) :
    Tendsto (fun n => (zSeq n ^ a - zSeq n ^ b) / (1 - zSeq n)) atTop (𝓝 (b - a)) := by
  have hd : HasDerivAt (fun t : ℝ => t ^ b - t ^ a) (b - a) 1 := by
    have h := (Real.hasDerivAt_rpow_const (x := 1) (p := b) (Or.inl one_ne_zero)).sub
      (Real.hasDerivAt_rpow_const (x := 1) (p := a) (Or.inl one_ne_zero))
    simp only [Real.one_rpow, mul_one] at h
    exact h
  have hs := (hasDerivAt_iff_tendsto_slope.1 hd).comp tendsto_zSeq
  refine hs.congr fun n => ?_
  have hne : zSeq n - 1 ≠ 0 := sub_ne_zero.2 (zSeq_mem n).2.ne
  simp only [Function.comp, slope_def_field, Real.one_rpow, sub_self, sub_zero]
  rw [div_eq_div_iff hne (by linarith [(zSeq_mem n).2])]
  ring

/-- `∫ P(x, dy) |V(y) − V(x)| ≤ B` as a real integral. -/
theorem integral_abs_sub_le (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ}
    (hV : Measurable V) {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B)
    (x : X) : ∫ y, |V y - V x| ∂P x ≤ B.toReal := by
  have h := integral_norm_eq_lintegral_enorm (μ := P x) (f := fun y => V y - V x)
    (hV.sub measurable_const).aestronglyMeasurable
  simp only [Real.norm_eq_abs] at h
  rw [h]
  exact ENNReal.toReal_mono hB (hinc x)

/-- **Theorem 19.3.2** (MT p. 500): if `π` is an invariant probability and `V ≥ 0` has
increments bounded in mean (19.46), then `∫ π(dy) ΔV(y) = 0` (19.51). The proof is the book's,
through `M_z(x) = ∫ P(x, dy) [z^{V(x)} − z^{V(y)}]/(1 − z)` along `z_n ↑ 1`: `π(M_z) = 0` by
invariance, `|M_z| ≤ 2B` and `M_z → ΔV`, and dominated convergence twice. -/
theorem theorem_19_3_2 (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {V : X → ℝ} (hV : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) :
    ∫ x, driftR P V x ∂π = 0 := by
  set z := zSeq
  have hz0 : ∀ n, 0 < z n := fun n => by linarith [(zSeq_mem n).1]
  have hz1 : ∀ n, z n ≤ 1 := fun n => (zSeq_mem n).2.le
  have hzm : ∀ n, Measurable fun y => z n ^ V y := fun n => measurable_const.pow hV
  have hzb : ∀ n y, |z n ^ V y| ≤ 1 := fun n y => by
    rw [abs_of_nonneg (Real.rpow_nonneg (hz0 n).le _)]
    exact Real.rpow_le_one (hz0 n).le (hz1 n) (hV0 y)
  have hzi : ∀ n (μ : Measure X) [IsFiniteMeasure μ], Integrable (fun y => z n ^ V y) μ :=
    fun n μ _ => Integrable.of_bound (hzm n).aestronglyMeasurable 1
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hzb n y)
  -- `M_z(x)` in closed form
  set M : ℕ → X → ℝ := fun n x => (z n ^ V x - ∫ y, z n ^ V y ∂P x) / (1 - z n) with hMdef
  have hMint : ∀ n x, M n x = ∫ y, (z n ^ V x - z n ^ V y) / (1 - z n) ∂P x := fun n x => by
    rw [integral_div, integral_sub (integrable_const _) (hzi n (P x)), integral_const,
      smul_eq_mul, probReal_univ, one_mul]
  have hMm : ∀ n, Measurable (M n) := fun n =>
    ((hzm n).sub (measurable_kfunR P (hzm n))).div_const _
  -- (a) `π(M_z) = 0`
  have hM0 : ∀ n, ∫ x, M n x ∂π = 0 := fun n => by
    have hcomp : ∫ x, ∫ y, z n ^ V y ∂P x ∂π = ∫ y, z n ^ V y ∂π := by
      rw [← integral_measure_comp P π, hπ]
      rw [hπ]; exact hzi n π
    rw [integral_div, integral_sub (hzi n π) ?_, hcomp, sub_self, zero_div]
    exact Integrable.of_bound (measurable_kfunR P (hzm n)).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact abs_kfunR_le P (fun y => hzb n y) x)
  -- (b) the pointwise bound `|[z^{V(x)} − z^{V(y)}]/(1 − z)| ≤ 2|V(y) − V(x)|`
  have hG : ∀ n x y, |(z n ^ V x - z n ^ V y) / (1 - z n)| ≤ 2 * |V y - V x| := by
    intro n x y
    have h1z : 0 < 1 - z n := by linarith [(zSeq_mem n).2]
    rw [abs_div, abs_of_pos h1z, div_le_iff₀ h1z]
    calc |z n ^ V x - z n ^ V y| ≤ |Real.log (z n)| * |V x - V y| :=
          abs_rpow_sub_rpow_le (hz0 n) (hz1 n) (hV0 x) (hV0 y)
      _ ≤ 2 * (1 - z n) * |V x - V y| :=
          mul_le_mul_of_nonneg_right (abs_log_le_two_mul (zSeq_mem n).1 (hz1 n)) (abs_nonneg _)
      _ = 2 * |V y - V x| * (1 - z n) := by rw [abs_sub_comm]; ring
  -- (d) `M_z(x) → ΔV(x)`
  have hMlim : ∀ x, Tendsto (fun n => M n x) atTop (𝓝 (driftR P V x)) := fun x => by
    simp_rw [hMint, driftR_eq_integral P hV hB hinc x]
    refine tendsto_integral_of_dominated_convergence (fun y => 2 * |V y - V x|)
      (fun n => (((measurable_const.sub (hzm n)).div_const _)).aestronglyMeasurable)
      (((integrable_of_increments hV hB hinc x).sub (integrable_const _)).abs.const_mul 2)
      (fun n => Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hG n x y)
      (Eventually.of_forall fun y => tendsto_rpow_slope (V x) (V y))
  -- (e) `|M_z| ≤ 2B`
  have hMb : ∀ n x, ‖M n x‖ ≤ 2 * B.toReal := fun n x => by
    rw [hMint]
    calc ‖∫ y, (z n ^ V x - z n ^ V y) / (1 - z n) ∂P x‖ ≤ ∫ y, 2 * |V y - V x| ∂P x :=
          norm_integral_le_of_norm_le
            (((integrable_of_increments hV hB hinc x).sub (integrable_const _)).abs.const_mul 2)
            (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hG n x y)
      _ = 2 * ∫ y, |V y - V x| ∂P x := integral_const_mul _ _
      _ ≤ 2 * B.toReal := by
          have := integral_abs_sub_le P hV hB hinc x
          linarith
  -- (f) dominated convergence for `π`
  have hlim := tendsto_integral_of_dominated_convergence (μ := π) (fun _ => 2 * B.toReal)
    (fun n => (hMm n).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall (hMb n)) (Eventually.of_forall hMlim)
  simp_rw [hM0] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-! ### Theorem 19.3.3 -/

/-- Invariance in `[0, ∞]`: `∫ π(dx) ∫ P(x, dy) h(y) = ∫ π(dy) h(y)`. -/
theorem lintegral_kernel_of_invariant (P : Kernel X X) {π : Measure X} (hπ : IsInvariant P π)
    {h : X → ℝ≥0∞} (hh : Measurable h) : ∫⁻ x, ∫⁻ y, h y ∂P x ∂π = ∫⁻ y, h y ∂π := by
  conv_rhs => rw [← hπ]
  exact (Measure.lintegral_bind (Kernel.aemeasurable _) hh.aemeasurable).symm

/-- **The balanced flow** (19.63), MT p. 502: `∫_C π(dx) P(x, Cᶜ) = ∫_{Cᶜ} π(dx) P(x, C)`. -/
theorem flow_balance (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {C : Set X} (hC : MeasurableSet C) :
    ∫⁻ x in C, P x Cᶜ ∂π = ∫⁻ x in Cᶜ, P x C ∂π := by
  have h1 := lintegral_kernel_of_invariant P hπ (measurable_one.indicator hC)
  simp_rw [lintegral_indicator_one hC] at h1
  have hsplit : ∫⁻ x, P x C ∂π = ∫⁻ x in C, P x C ∂π + ∫⁻ x in Cᶜ, P x C ∂π :=
    (lintegral_add_compl _ hC).symm
  have hC' : π C = ∫⁻ x in C, P x C ∂π + ∫⁻ x in C, P x Cᶜ ∂π := by
    rw [← lintegral_add_left (Kernel.measurable_coe P hC),
      setLIntegral_congr_fun hC (fun x _ => by rw [measure_add_measure_compl hC, measure_univ]),
      setLIntegral_const, one_mul]
  have hfin : ∫⁻ x in C, P x C ∂π ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top π C) (by
      calc ∫⁻ x in C, P x C ∂π ≤ ∫⁻ _ in C, 1 ∂π := lintegral_mono fun x => prob_le_one
        _ = π C := by rw [setLIntegral_const, one_mul])
  rw [hsplit, hC'] at h1
  exact ((ENNReal.add_right_inj hfin).1 h1).symm

/-- **The flow between `C` and `Cᶜ` is positive** (MT p. 501): for a `ψ`-irreducible chain with
invariant probability `π` and `C, Cᶜ ∈ B⁺(X)`, `∫_C π(dx) P(x, Cᶜ) > 0`. Otherwise, by (19.63)
and invariance, `∫_{Cᶜ} π(dx) Pⁿ(x, C) = 0` for every `n ≥ 1`, so `L(x, C) = 0` on a set of
positive `π`-measure, contradicting irreducibility (`ψ ≪ π`, Proposition 10.1.2). -/
theorem flow_pos {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {C : Set X} (hC : MeasurableSet C) (hψC : 0 < ψ C)
    (hψC' : 0 < ψ Cᶜ) : 0 < ∫⁻ x in C, P x Cᶜ ∂π := by
  have hψπ : ψ ≪ π :=
    proposition_10_1_2_ii hψ.2.1 hπ.isSubinvariant (IsProbabilityMeasure.ne_zero π)
  have hπC' : 0 < π Cᶜ := pos_iff_ne_zero.2 fun h => hψC'.ne' (hψπ h)
  by_contra h0
  have hF : ∫⁻ x in Cᶜ, P x C ∂π = 0 := by
    rw [← flow_balance P hπ hC]; exact nonpos_iff_eq_zero.1 (not_lt.1 h0)
  have hind : ∀ n : ℕ, ∫⁻ x in Cᶜ, (P ^ (n + 1)) x C ∂π = 0 := by
    intro n
    induction n with
    | zero => simpa using hF
    | succ n ih =>
      have := isMarkovKernel_pow P (n + 1)
      set g := fun y => (P ^ (n + 1)) y C with hgdef
      have hg : Measurable g := Kernel.measurable_coe _ hC
      have hpt : ∀ x, (P ^ (n + 1 + 1)) x C ≤ P x C + ∫⁻ y, Cᶜ.indicator g y ∂P x := fun x => by
        rw [pow_succ_apply P (n + 1) x hC, ← lintegral_add_compl g hC]
        refine add_le_add ?_ ?_
        · calc ∫⁻ y in C, g y ∂P x ≤ ∫⁻ _ in C, 1 ∂P x := lintegral_mono fun y => prob_le_one
            _ = P x C := by rw [setLIntegral_const, one_mul]
        · rw [lintegral_indicator hC.compl]
      refine nonpos_iff_eq_zero.1 ?_
      calc ∫⁻ x in Cᶜ, (P ^ (n + 1 + 1)) x C ∂π
          ≤ ∫⁻ x in Cᶜ, (P x C + ∫⁻ y, Cᶜ.indicator g y ∂P x) ∂π := lintegral_mono hpt
        _ = ∫⁻ x in Cᶜ, P x C ∂π + ∫⁻ x in Cᶜ, ∫⁻ y, Cᶜ.indicator g y ∂P x ∂π :=
            lintegral_add_left (Kernel.measurable_coe P hC) _
        _ ≤ 0 + ∫⁻ x, ∫⁻ y, Cᶜ.indicator g y ∂P x ∂π :=
            add_le_add hF.le (setLIntegral_le_lintegral _ _)
        _ = ∫⁻ y, Cᶜ.indicator g y ∂π := by
            rw [zero_add, lintegral_kernel_of_invariant P hπ (hg.indicator hC.compl)]
        _ = 0 := by rw [lintegral_indicator hC.compl]; exact ih
  have hae : ∀ᵐ x ∂π.restrict Cᶜ, ∀ n : ℕ, (P ^ (n + 1)) x C = 0 := by
    rw [ae_all_iff]
    intro n
    exact (lintegral_eq_zero_iff (Kernel.measurable_coe _ hC)).1 (hind n)
  have hfalse : ∀ᵐ _x ∂π.restrict Cᶜ, False := hae.mono fun x hx => by
    obtain ⟨n, hn⟩ := (hitProb_pos_iff P hC x).1 (hψ.2.1 C hC hψC x)
    exact hn.ne' (hx n)
  have h0' : π.restrict Cᶜ = 0 := ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hfalse)
  rw [Measure.restrict_eq_zero] at h0'
  exact hπC'.ne' h0'

/-- **(19.64)** (MT p. 502): for a `ψ`-irreducible chain with invariant probability `π`, `V ≥ 0`
with (19.46), and a sublevel set `C = {V ≤ b}` with `C, Cᶜ ∈ B⁺(X)`, `∫_C π(dw) ΔV(w) > 0`.
The proof is the book's (19.60)–(19.63): `∫_C πΔV = ∫_C π(dx) ∫_{Cᶜ} P(x, dw) V(w) −
∫_{Cᶜ} π(dx) ∫_C P(x, dw) V(w)`, where the first term exceeds `b` times the flow out of `C` and
the second is at most `b` times the (equal) flow into `C`. -/
theorem setIntegral_driftR_pos {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {V : X → ℝ} (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) {b : ℝ}
    (hψC : 0 < ψ {x | V x ≤ b}) (hψC' : 0 < ψ {x | V x ≤ b}ᶜ) :
    0 < ∫ x in {x | V x ≤ b}, driftR P V x ∂π := by
  set C := {x | V x ≤ b} with hCdef
  have hC : MeasurableSet C := measurableSet_le hV measurable_const
  have hVi := integrable_of_increments hV hB hinc
  have hb0 : 0 ≤ b := by
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hψC.ne'
    exact (hV0 y).trans hy
  set f1 : X → ℝ := fun x => ∫ y in Cᶜ, V y ∂P x with hf1def
  set f2 : X → ℝ := fun x => ∫ y in C, V y ∂P x with hf2def
  set h : X → ℝ := fun x => ∫ y in Cᶜ, (V y - b) ∂P x with hhdef
  -- measurability
  have hf1m : Measurable f1 := by
    have : f1 = kfunR P (Cᶜ.indicator V) := funext fun x => (integral_indicator hC.compl).symm
    rw [this]; exact measurable_kfunR P (hV.indicator hC.compl)
  have hf2m : Measurable f2 := by
    have : f2 = kfunR P (C.indicator V) := funext fun x => (integral_indicator hC).symm
    rw [this]; exact measurable_kfunR P (hV.indicator hC)
  have hhm : Measurable h := by
    have : h = kfunR P (Cᶜ.indicator fun y => V y - b) :=
      funext fun x => (integral_indicator hC.compl).symm
    rw [this]; exact measurable_kfunR P ((hV.sub measurable_const).indicator hC.compl)
  -- pointwise facts
  have hsplit : ∀ x, driftR P V x = f1 x + f2 x - V x := fun x => by
    simp only [driftR, hf1def, hf2def]
    rw [add_comm, integral_add_compl hC (hVi x)]
  have hf1 : ∀ x, f1 x = h x + (P x).real Cᶜ * b := fun x => by
    simp only [hf1def, hhdef]
    rw [integral_sub (hVi x).integrableOn (integrable_const b).integrableOn, setIntegral_const,
      smul_eq_mul]
    ring
  have hf2le : ∀ x, f2 x ≤ (P x).real C * b := fun x => by
    calc f2 x ≤ ∫ _ in C, b ∂P x :=
          setIntegral_mono_on (hVi x).integrableOn (integrable_const b).integrableOn hC
            fun y hy => hy
      _ = (P x).real C * b := by rw [setIntegral_const, smul_eq_mul]
  have hf2nn : ∀ x, 0 ≤ f2 x := fun x => setIntegral_nonneg hC fun y _ => hV0 y
  have hhnn : ∀ x, 0 ≤ h x := fun x => setIntegral_nonneg hC.compl fun y hy => by
    simp only [hCdef, mem_compl_iff, mem_ofPred_eq, not_le] at hy
    linarith
  have hreal : ∀ x (A : Set X), 0 ≤ (P x).real A ∧ (P x).real A ≤ 1 := fun x A =>
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hf2b : ∀ x, ‖f2 x‖ ≤ b := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf2nn x)]
    exact (hf2le x).trans (by nlinarith [(hreal x C).2])
  -- bounds on `C`
  have hDb := abs_driftR_le P hV hB hinc
  have hf1C : ∀ x ∈ C, ‖f1 x‖ ≤ B.toReal + b := fun x hx => by
    have hf1nn : 0 ≤ f1 x := by rw [hf1 x]; nlinarith [hhnn x, (hreal x Cᶜ).1]
    rw [Real.norm_eq_abs, abs_of_nonneg hf1nn]
    have := hsplit x
    have h1 := (abs_le.1 (hDb x)).2
    have h2 : V x ≤ b := hx
    linarith [hf2nn x]
  have hhC : ∀ x ∈ C, ‖h x‖ ≤ B.toReal + b := fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hhnn x)]
    have := hf1C x hx
    rw [Real.norm_eq_abs, hf1 x] at this
    have := le_abs_self (h x + (P x).real Cᶜ * b)
    nlinarith [(hreal x Cᶜ).1]
  have hIC : ∀ {g : X → ℝ}, Measurable g → (∀ x ∈ C, ‖g x‖ ≤ B.toReal + b) →
      IntegrableOn g C π := fun {g} hg hgb =>
    Integrable.of_bound hg.aestronglyMeasurable (B.toReal + b)
      ((ae_restrict_iff' hC).2 (Eventually.of_forall hgb))
  have hf1i := hIC hf1m hf1C
  have hhi := hIC hhm hhC
  have hf2i : Integrable f2 π := Integrable.of_bound hf2m.aestronglyMeasurable b
    (Eventually.of_forall hf2b)
  have hVC : IntegrableOn V C π := Integrable.of_bound hV.aestronglyMeasurable b
    ((ae_restrict_iff' hC).2 (Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hV0 x)]; exact hx))
  -- (19.60): invariance for `V 1_C`
  have hinv : ∫ x, f2 x ∂π = ∫ x in C, V x ∂π := by
    have hint : Integrable (C.indicator V) (P ∘ₘ π) := by
      rw [hπ]; exact hVC.integrable_indicator hC
    have := integral_measure_comp P π hint
    rw [hπ] at this
    rw [← integral_indicator hC, this]
    exact integral_congr_ae (Eventually.of_forall fun x => (integral_indicator hC).symm)
  have hC1 : ∫ x in C, driftR P V x ∂π = ∫ x in C, f1 x ∂π - ∫ x in Cᶜ, f2 x ∂π := by
    have h2 := integral_add_compl hC hf2i
    rw [setIntegral_congr_fun hC fun x _ => hsplit x,
      integral_sub (f := fun x => f1 x + f2 x) (hf1i.add hf2i.integrableOn) hVC,
      integral_add hf1i hf2i.integrableOn]
    linarith
  -- the flows
  have hmC : Measurable fun x => (P x).real C :=
    (Kernel.measurable_coe P hC).ennreal_toReal
  have hmC' : Measurable fun x => (P x).real Cᶜ :=
    (Kernel.measurable_coe P hC.compl).ennreal_toReal
  have hflow : ∫ x in C, (P x).real Cᶜ ∂π = ∫ x in Cᶜ, (P x).real C ∂π := by
    have h1 := integral_toReal (μ := π.restrict C) (Kernel.measurable_coe P hC.compl).aemeasurable
      (Eventually.of_forall fun x => measure_lt_top _ _)
    have h2 := integral_toReal (μ := π.restrict Cᶜ) (Kernel.measurable_coe P hC).aemeasurable
      (Eventually.of_forall fun x => measure_lt_top _ _)
    change ∫ x in C, (P x Cᶜ).toReal ∂π = ∫ x in Cᶜ, (P x C).toReal ∂π
    rw [h1, h2, flow_balance P hπ hC]
  have hbd1 : ∀ x, ‖(P x).real Cᶜ‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hreal x Cᶜ).1]; exact (hreal x Cᶜ).2
  have hbd2 : ∀ x, ‖(P x).real C‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hreal x C).1]; exact (hreal x C).2
  have hpi1 : Integrable (fun x => (P x).real Cᶜ) π :=
    Integrable.of_bound hmC'.aestronglyMeasurable 1 (Eventually.of_forall hbd1)
  have hpi2 : Integrable (fun x => (P x).real C) π :=
    Integrable.of_bound hmC.aestronglyMeasurable 1 (Eventually.of_forall hbd2)
  have hA1 : ∫ x in C, f1 x ∂π = ∫ x in C, h x ∂π + (∫ x in C, (P x).real Cᶜ ∂π) * b := by
    rw [setIntegral_congr_fun hC fun x _ => hf1 x, integral_add hhi (hpi1.integrableOn.mul_const b),
      integral_mul_const]
  have hA4 : ∫ x in Cᶜ, f2 x ∂π ≤ (∫ x in Cᶜ, (P x).real C ∂π) * b := by
    rw [← integral_mul_const]
    exact setIntegral_mono_on hf2i.integrableOn (hpi2.integrableOn.mul_const b) hC.compl
      fun x _ => hf2le x
  -- `∫_C h > 0`
  have hhpos : 0 < ∫ x in C, h x ∂π := by
    refine lt_of_le_of_ne (setIntegral_nonneg hC fun x _ => hhnn x) fun h0 => ?_
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hhnn) hhi).1 h0.symm
    have hzero : ∀ᵐ x ∂π.restrict C, P x Cᶜ = 0 := hae.mono fun x hx => by
      have hx' : ∫ y in Cᶜ, (V y - b) ∂P x = 0 := hx
      have hnn : 0 ≤ᵐ[(P x).restrict Cᶜ] fun y => V y - b :=
        (ae_restrict_iff' hC.compl).2 (Eventually.of_forall fun y hy => by
          simp only [hCdef, mem_compl_iff, mem_ofPred_eq, not_le] at hy
          exact (sub_pos.2 hy).le)
      have h0y := (setIntegral_eq_zero_iff_of_nonneg_ae hnn
        ((hVi x).sub (integrable_const b)).integrableOn).1 hx'
      have hf : ∀ᵐ _y ∂(P x).restrict Cᶜ, False := by
        filter_upwards [h0y, ae_restrict_mem hC.compl] with y hy hyC
        simp only [hCdef, mem_compl_iff, mem_ofPred_eq, not_le] at hyC
        have : V y - b = 0 := hy
        linarith
      have := ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hf)
      rwa [Measure.restrict_eq_zero] at this
    have hl : ∫⁻ x in C, P x Cᶜ ∂π = 0 := by
      rw [lintegral_congr_ae hzero, lintegral_zero]
    exact (flow_pos hψ hπ hC hψC hψC').ne' hl
  rw [hC1, hA1]
  rw [hflow] at hA1 ⊢
  linarith

/-- **Theorem 19.3.3** (MT p. 501): for a `ψ`-irreducible chain with invariant probability `π`
(a positive chain), `V ≥ 0` with increments bounded in mean (19.46), and a sublevel set
`C = {V ≤ b}` with `C, Cᶜ ∈ B⁺(X)`, the drift is inward on average off `C`:
`∫_{Cᶜ} π(dw) ΔV(w) < 0` (19.56). It follows from (19.51) and (19.64). -/
theorem theorem_19_3_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {V : X → ℝ} (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) {b : ℝ}
    (hψC : 0 < ψ {x | V x ≤ b}) (hψC' : 0 < ψ {x | V x ≤ b}ᶜ) :
    ∫ x in {x | V x ≤ b}ᶜ, driftR P V x ∂π < 0 := by
  have hC : MeasurableSet {x | V x ≤ b} := measurableSet_le hV measurable_const
  have h0 := theorem_19_3_2 P π hπ hV hV0 hB hinc
  have hpos := setIntegral_driftR_pos hψ hπ hV hV0 hB hinc hψC hψC'
  have hsum := integral_add_compl hC (integrable_driftR P hV hB hinc π)
  linarith

/-! ### (19.57): the Cesàro form of (19.56) -/

omit [MeasurableSpace X] in
/-- Cesàro averages from phase averages: if `|uₖ| ≤ K` and the phase averages
`d⁻¹ Σ_{r<d} u_{dn+r}` tend to `L`, so do the Cesàro averages `n⁻¹ Σ_{k<n} uₖ`. -/
theorem tendsto_cesaro_of_phase {u : ℕ → ℝ} {K : ℝ} (hu : ∀ k, |u k| ≤ K) {d : ℕ} (hd : 0 < d)
    {L : ℝ}
    (h : Tendsto (fun n : ℕ => (d : ℝ)⁻¹ * ∑ r ∈ Finset.range d, u (d * n + r)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, u k) atTop (𝓝 L) := by
  set w : ℕ → ℝ := fun n : ℕ => (d : ℝ)⁻¹ * ∑ r ∈ Finset.range d, u (d * n + r) with hw
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hblock : ∀ N, ∑ k ∈ Finset.range (d * N), u k = d * ∑ n ∈ Finset.range N, w n := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show d * (N + 1) = d * N + d by ring, Finset.sum_range_add, ih, sum_range_succ, mul_add]
      congr 1
      rw [hw, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
  have hK : 0 ≤ K := (abs_nonneg _).trans (hu 0)
  -- the decomposition along `n = d ⌊n/d⌋ + (n mod d)`
  have hdecomp : ∀ n : ℕ, (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, u k =
      ((d * (n / d) : ℕ) : ℝ) / n * (((n / d : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range (n / d), w m) +
        (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (n % d), u (d * (n / d) + j) := by
    intro n
    have hn : n = d * (n / d) + n % d := (Nat.div_add_mod n d).symm
    conv_lhs => rw [hn, Finset.sum_range_add, ← hn]
    rw [hblock, mul_add]
    congr 1
    rcases Nat.eq_zero_or_pos (n / d) with h0 | h0
    · rw [h0]; simp
    · have h0' : ((n / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
      push_cast
      field_simp
  -- the two pieces
  have hNtop : Tendsto (fun n : ℕ => n / d) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * d, fun n hn => (Nat.le_div_iff_mul_le hd).2 hn⟩
  have hc := h.cesaro.comp hNtop
  have hratio : Tendsto (fun n : ℕ => ((d * (n / d) : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h2 : Tendsto (fun n : ℕ => (1 : ℝ) - (d : ℝ) / n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat
        (d : ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn', one_mul]
      have : n < d * (n / d) + d := by
        have := Nat.mod_lt n hd
        have := Nat.div_add_mod n d
        omega
      exact_mod_cast this.le
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_one hn']
      exact_mod_cast Nat.mul_div_le n d
  have hrem : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (n % d), u (d * (n / d) + j))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat ((d : ℝ) * K))
    rw [norm_mul, norm_inv, Real.norm_natCast, inv_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
    calc ‖∑ j ∈ Finset.range (n % d), u (d * (n / d) + j)‖
        ≤ ∑ j ∈ Finset.range (n % d), ‖u (d * (n / d) + j)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (n % d), K :=
          sum_le_sum fun j _ => by rw [Real.norm_eq_abs]; exact hu _
      _ = (n % d : ℕ) * K := by rw [sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ d * K := mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mod_lt n hd).le) hK
  have := (hratio.mul hc).add hrem
  rw [one_mul, add_zero] at this
  exact this.congr fun n => (hdecomp n).symm

omit [MeasurableSpace X] in
/-- Shifting a Cesàro average by one: if `n⁻¹ Σ_{k<n} uₖ → L`, then `n⁻¹ Σ_{k<n} u_{k+1} → L`. -/
theorem tendsto_cesaro_shift {u : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n, u k) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n, u (k + 1)) atTop (𝓝 L) := by
  have e : ∀ n : ℕ, (n : ℝ)⁻¹ * ∑ k ∈ range n, u (k + 1) =
      ((n + 1 : ℕ) : ℝ) / n * (((n + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ range (n + 1), u k) -
        (n : ℝ)⁻¹ * u 0 := fun n => by
    rw [sum_range_succ']
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · have : (n : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
      push_cast
      field_simp
      ring
  have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  have h2 := h.comp (tendsto_add_atTop_nat 1)
  have h3 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * u 0) atTop (𝓝 0) := by
    simpa [div_eq_inv_mul] using tendsto_const_div_atTop_nhds_zero_nat (u 0)
  have := (h1.mul h2).sub h3
  rw [one_mul, sub_zero] at this
  exact this.congr fun n => (e n).symm

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The Cesàro ergodic theorem for positive chains** (from Theorem 13.3.4 (ii)): off a
`ψ`-null set `N`, for every bounded measurable `g`, `n⁻¹ Σ_{k<n} ∫ Pᵏ(x, dy) g(y) → π(g)`. -/
theorem tendsto_cesaro_integral_of_isPositive {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (hpos : IsPositive P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    ∃ N : Set X, MeasurableSet N ∧ ψ N = 0 ∧ ∀ x ∉ N, ∀ g : X → ℝ, Measurable g →
      ∀ K : ℝ, (∀ y, |g y| ≤ K) →
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ y, g y ∂(P ^ k) x) atTop
          (𝓝 (∫ y, g y ∂π)) := by
  obtain ⟨d, hper⟩ := exists_isPeriod P hψ
  obtain ⟨N, hNm, hψN, hconv⟩ := theorem_13_3_4_ii hpos hper hπ
  refine ⟨N, hNm, hψN, fun x hx g hg K hgK => ?_⟩
  have hd : 0 < d := hper.1
  set K' := max K 0 + 1 with hK'
  have hK'pos : 0 < K' := by rw [hK']; linarith [le_max_right K 0]
  have hgb : ∀ y, |g y| ≤ K' := fun y => (hgK y).trans (by rw [hK']; linarith [le_max_left K 0])
  have hpow : ∀ m, IsMarkovKernel (P ^ m) := isMarkovKernel_pow P
  set u : ℕ → ℝ := fun k => ∫ y, g y ∂(P ^ k) x with hu
  have hub : ∀ k, |u k| ≤ K' := fun k => by
    have := hpow k
    have h := abs_integral_le_measureReal (μ := (P ^ k) x) (f := fun y => g y / K')
      (fun y => by
        rw [abs_div, abs_of_pos hK'pos]
        exact (div_le_one hK'pos).2 (hgb y))
    rw [integral_div, probReal_univ, abs_div, abs_of_pos hK'pos, div_le_one hK'pos] at h
    exact h
  have hx0 : Measure.dirac x N = 0 := by
    rw [Measure.dirac_apply' _ hNm, indicator_of_notMem hx]
  have hph := hconv (Measure.dirac x) hx0
  have hfinμ : ∀ n, IsFiniteMeasure ((d : ℝ≥0∞)⁻¹ • ∑ r ∈ Finset.range d,
      (P ^ (d * n + r) : Kernel X X) ∘ₘ Measure.dirac x) := fun n => by
    refine ⟨?_⟩
    simp only [dirac_kernel, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      smul_eq_mul]
    refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by exact_mod_cast hd))
      (ENNReal.sum_lt_top.2 fun r _ => ?_)
    have := hpow (d * n + r)
    exact measure_lt_top _ _
  have hphase : Tendsto (fun n : ℕ => (d : ℝ)⁻¹ * ∑ r ∈ Finset.range d, u (d * n + r)) atTop
      (𝓝 (∫ y, g y ∂π)) := by
    have hlim := tendsto_integral_of_tendsto_tvNorm hph hg hK'pos hgb
    refine hlim.congr fun n => ?_
    rw [integral_smul_measure, integral_finsetSum_measure fun r _ => ?_]
    · simp only [hu, dirac_kernel, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
    · rw [dirac_kernel]
      exact Integrable.of_bound hg.aestronglyMeasurable _
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hgb y)
  exact tendsto_cesaro_of_phase hub hd hphase

variable [MeasurableSpace.CountablyGenerated X] in
/-- **(19.57)** (MT p. 501): for a positive `ψ`-irreducible chain with invariant probability `π`
and `V ≥ 0` with (19.46), off a `ψ`-null set the averages `n⁻¹ Σ_{k=1}^n ∫_{Cᶜ} Pᵏ(x, dy) ΔV(y)`
converge to `∫_{Cᶜ} π(dy) ΔV(y)`, for every measurable `C`. The book says "(19.57) is actually
identical to (19.56)"; the step is the ergodic theorem for positive chains
(`tendsto_cesaro_integral_of_isPositive`). -/
theorem tendsto_cesaro_setIntegral_driftR {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hpos : IsPositive P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {V : X → ℝ} (hV : Measurable V)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) {C : Set X}
    (hC : MeasurableSet C) :
    ∃ N : Set X, MeasurableSet N ∧ ψ N = 0 ∧ ∀ x ∉ N,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ y in Cᶜ, driftR P V y ∂(P ^ (k + 1)) x)
        atTop (𝓝 (∫ y in Cᶜ, driftR P V y ∂π)) := by
  obtain ⟨N, hNm, hψN, hconv⟩ := tendsto_cesaro_integral_of_isPositive hψ hpos hπ
  refine ⟨N, hNm, hψN, fun x hx => ?_⟩
  set f : X → ℝ := Cᶜ.indicator (driftR P V) with hf
  have hfm : Measurable f := (measurable_driftR P hV).indicator hC.compl
  have hfb : ∀ y, |f y| ≤ B.toReal := fun y => by
    by_cases hy : y ∈ Cᶜ
    · rw [hf, indicator_of_mem hy]; exact abs_driftR_le P hV hB hinc y
    · rw [hf, indicator_of_notMem hy, abs_zero]; positivity
  have hshift := tendsto_cesaro_shift (hconv x hx f hfm _ hfb)
  rw [hf, integral_indicator hC.compl] at hshift
  refine hshift.congr fun n => ?_
  congr 1
  refine sum_congr rfl fun k _ => ?_
  exact integral_indicator hC.compl

variable [MeasurableSpace.CountablyGenerated X] in
/-- **"(19.48) is necessary and sufficient for positivity"** (MT p. 501): for a `ψ`-irreducible
chain, `V ≥ 0` with (19.46) and a petite sublevel set `C = {V ≤ b}` with `C, Cᶜ ∈ B⁺(X)`, the chain
is positive iff (19.48) holds at some `x`. The direction (19.48) ⇒ positive is Theorem 19.3.1; the
converse is (19.56)–(19.57). -/
theorem theorem_19_3_3_iff {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ} (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) {b : ℝ}
    (hpet : IsPetite P {x | V x ≤ b}) (hψC : 0 < ψ {x | V x ≤ b})
    (hψC' : 0 < ψ {x | V x ≤ b}ᶜ) :
    IsPositive P ψ ↔ ∃ x, ∃ η : ℝ, 0 < η ∧ ∃ᶠ n : ℕ in atTop,
      (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ y in {x | V x ≤ b}ᶜ, driftR P V y ∂(P ^ (k + 1)) x ≤ -η := by
  have hC : MeasurableSet {x | V x ≤ b} := measurableSet_le hV measurable_const
  constructor
  · intro hpos
    obtain ⟨-, π, hπp, hπ⟩ := id hpos
    have hneg := theorem_19_3_3 hψ hπ hV hV0 hB hinc hψC hψC'
    obtain ⟨N, -, hψN, hconv⟩ := tendsto_cesaro_setIntegral_driftR hψ hpos hπ hV hB hinc hC
    have hNc : ∃ x, x ∉ N := by
      by_contra h
      push Not at h
      have : N = Set.univ := eq_univ_of_forall h
      rw [this] at hψN
      exact hψ.1 (Measure.measure_univ_eq_zero.1 hψN)
    obtain ⟨x, hx⟩ := hNc
    set L := ∫ y in {x | V x ≤ b}ᶜ, driftR P V y ∂π
    refine ⟨x, -L / 2, by linarith, (((hconv x hx).eventually (gt_mem_nhds (by linarith :
      L < -(-L / 2)))).mono fun n hn => ?_).frequently⟩
    linarith
  · rintro ⟨x, η, hη, h48⟩
    exact theorem_19_3_1 hψ hV hV0 hB hinc hpet hη h48

end MeynTweedie.GeneralizedDrift
