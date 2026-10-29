/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.VUniformErgodic
import Epilogue.GeometricModels

/-!
# Geometric ergodicity by increment analysis (MT §16.3.1, Theorem 16.3.1)

Meyn and Tweedie, §16.3.1, pp. 407–409. `V : X → [0, ∞)` is Foster's test function (16.25):
`PV ≤ V − 1` off a petite set `C` and `PV ≤ b` on `C`.

* `exp_le_one_add_add_sq`: `eᵗ ≤ 1 + t + t² e^{max(t, 0)}` (from `1 − t ≤ e^{−t}` twice; it
  replaces the second-order Taylor expansion (16.28)).
* `exp_mul_le_increment`: for `0 < δ ≤ β/2`,
  `e^{δu} ≤ 1 + δu + δ² (u² 1{u < 0} + 32 β⁻² e^{βu} 1{u ≥ 0})`, the bound (16.29).
* `increment_driftV4`: (16.25)–(16.27) give (V4) for `V* = e^{δV}` and some `δ ∈ (0, β)`, with
  the petite set `C ∩ {V < b + 1}`.
* **Theorem 16.3.1** (`theorem_16_3_1`, p. 407): for a `ψ`-irreducible aperiodic chain,
  (16.25)–(16.27) make the chain `V*`-uniformly ergodic, `V* = e^{δV}`, `δ < β`.
* `theorem_16_3_1_bounded_range` (p. 420, (16.50)): increments `|V(Φ₁) − V(x)| < B` of bounded
  range give (16.26) and (16.27), so an ergodic chain with such a test function is geometrically
  ergodic.
* **The need for (16.27)** (p. 409): for the chain (15.20) (`nonGeomKernel`) the minimal solution
  `V₀(j) = E_j[σ_0] = (1 − β_j)⁻¹` of (16.25) has right increments bounded for `j > 0`
  (`nonGeom_right_increments`), but `∫_{V₀ < V₀(i)} P(i, dy)(V₀(y) − V₀(i))² = (1 − β_i)⁻¹`
  (`nonGeom_left_increments`), unbounded when `β_j → 1` (`nonGeom_left_increments_unbounded`),
  and the chain is then not geometrically ergodic (`nonGeom_not_geomErgodic`).

**Corrections.**
* The book concludes (V4) for `V*` with the set `C`; when `V` is unbounded on `C` the constant
  `b` of (V4) would be infinite. Since `PV ≤ b` on `C`, the points of `C` with `V ≥ b + 1` have
  `PV ≤ V − 1` and satisfy the same bound as `Cᶜ`, so (V4) holds with the petite set
  `C ∩ {V < b + 1}`, on which `V*` is bounded.
* "Ergodic" in the theorem is used for aperiodicity, which is a hypothesis here; the rest of the
  ergodicity assumption is not needed beyond (16.25).

**Hypotheses.** The integrals in (16.25)–(16.27) are real integrals and their integrability is
assumed, as the statement of finite bounds presupposes.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### Elementary bounds for the exponential -/

/-- `eᵗ − 1 − t ≤ t (eᵗ − 1)` for every real `t` (from `1 − t ≤ e^{−t}`). -/
theorem exp_sub_one_sub_le (t : ℝ) : Real.exp t - 1 - t ≤ t * (Real.exp t - 1) := by
  have h := Real.add_one_le_exp (-t)
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos t).le
  nlinarith

/-- **The second-order bound** `eᵗ ≤ 1 + t + t² e^{max(t, 0)}` (the role of the Taylor expansion
(16.28)). -/
theorem exp_le_one_add_add_sq (t : ℝ) :
    Real.exp t ≤ 1 + t + t ^ 2 * Real.exp (max t 0) := by
  have key := exp_sub_one_sub_le t
  rcases le_total t 0 with ht | ht
  · have h1 : t ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
    have h2 : t * (Real.exp t - 1) ≤ t * t := mul_le_mul_of_nonpos_left h1 ht
    rw [max_eq_right ht, Real.exp_zero]
    nlinarith
  · have h := Real.add_one_le_exp (-t)
    have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_left h (Real.exp_pos t).le
    have h2 : Real.exp t - 1 ≤ t * Real.exp t := by nlinarith
    have h4 : t * (Real.exp t - 1) ≤ t * (t * Real.exp t) := mul_le_mul_of_nonneg_left h2 ht
    rw [max_eq_left ht]
    nlinarith

/-- `u² ≤ 32 β⁻² e^{βu/4}` for `u ≥ 0`, `β > 0`. -/
theorem sq_le_exp_mul {β u : ℝ} (hβ : 0 < β) (hu : 0 ≤ u) :
    u ^ 2 ≤ 32 / β ^ 2 * Real.exp (β * u / 4) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := β * u / 4) (by positivity)
  have hβ2 : 0 < β ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hβ2]
  nlinarith [mul_nonneg hβ.le hu]

/-- **The increment bound (16.29)**: for `0 < δ ≤ β/2` and every real `u`,
`e^{δu} ≤ 1 + δu + δ² R_β(u)`, `R_β(u) = u² 1{u < 0} + 32 β⁻² e^{βu} 1{u ≥ 0}`. -/
theorem exp_mul_le_increment {β δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hδβ : δ ≤ β / 2) (u : ℝ) :
    Real.exp (δ * u) ≤ 1 + δ * u +
      δ ^ 2 * ((if u < 0 then u ^ 2 else 0) + 32 / β ^ 2 * (if 0 ≤ u then Real.exp (β * u)
        else 0)) := by
  have h := exp_le_one_add_add_sq (δ * u)
  rcases lt_or_ge u 0 with hu | hu
  · have hm : max (δ * u) 0 = 0 := max_eq_right (mul_nonpos_of_nonneg_of_nonpos hδ.le hu.le)
    rw [hm, Real.exp_zero, mul_one] at h
    simp only [hu, ite_true, not_le.2 hu, ite_false, mul_zero, add_zero]
    calc Real.exp (δ * u) ≤ 1 + δ * u + (δ * u) ^ 2 := h
      _ = 1 + δ * u + δ ^ 2 * u ^ 2 := by ring
  · have hm : max (δ * u) 0 = δ * u := max_eq_left (mul_nonneg hδ.le hu)
    rw [hm] at h
    simp only [not_lt.2 hu, ite_false, hu, ite_true, zero_add]
    have h1 := sq_le_exp_mul hβ hu
    have h2 : Real.exp (δ * u) ≤ Real.exp (β * u / 2) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 : Real.exp (β * u / 4) * Real.exp (β * u / 2) ≤ Real.exp (β * u) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hβ.le hu])
    have h4 : u ^ 2 * Real.exp (δ * u) ≤ 32 / β ^ 2 * Real.exp (β * u) := by
      calc u ^ 2 * Real.exp (δ * u) ≤ (32 / β ^ 2 * Real.exp (β * u / 4)) *
            Real.exp (β * u / 2) :=
            mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
        _ = 32 / β ^ 2 * (Real.exp (β * u / 4) * Real.exp (β * u / 2)) := by ring
        _ ≤ 32 / β ^ 2 * Real.exp (β * u) := mul_le_mul_of_nonneg_left h3 (by positivity)
    calc Real.exp (δ * u) ≤ 1 + δ * u + (δ * u) ^ 2 * Real.exp (δ * u) := h
      _ = 1 + δ * u + δ ^ 2 * (u ^ 2 * Real.exp (δ * u)) := by ring
      _ ≤ 1 + δ * u + δ ^ 2 * (32 / β ^ 2 * Real.exp (β * u)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left h4 (by positivity))

/-! ### The drift for `e^{δV}` -/

/-- **(16.25)–(16.27) give (V4) for `V* = e^{δV}`** (the proof of Theorem 16.3.1, MT p. 408):
there is `δ ∈ (0, β)` with `PV* ≤ ρ V* + b' 1_{C'}` for `ρ < 1`, `b' < ∞` and
`C' = C ∩ {V < b + 1}`. -/
theorem increment_driftV4 {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ} (hV : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) {C : Set X} {b c d β : ℝ} (hβ : 0 < β)
    (hint : ∀ x, Integrable V (P x))
    (hF1 : ∀ x ∉ C, ∫ y, V y ∂P x ≤ V x - 1) (hF2 : ∀ x ∈ C, ∫ y, V y ∂P x ≤ b)
    (h26i : ∀ x, IntegrableOn (fun y => Real.exp (β * (V y - V x))) {y | V x ≤ V y} (P x))
    (h26 : ∀ x, ∫ y in {y | V x ≤ V y}, Real.exp (β * (V y - V x)) ∂P x ≤ c)
    (h27i : ∀ x, IntegrableOn (fun y => (V y - V x) ^ 2) {y | V y < V x} (P x))
    (h27 : ∀ x, ∫ y in {y | V y < V x}, (V y - V x) ^ 2 ∂P x ≤ d) :
    ∃ δ : ℝ, 0 < δ ∧ δ < β ∧ ∃ ρ b' : ℝ≥0∞, ρ < 1 ∧ b' ≠ ∞ ∧
      DriftV4 P (fun y => ENNReal.ofReal (Real.exp (δ * V y))) ρ b' (C ∩ {y | V y < b + 1}) := by
  set K : ℝ := 32 / β ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set M : ℝ := |d| + K * |c| + 1 with hM
  have hM0 : 0 < M := by positivity
  set δ : ℝ := min (β / 2) (1 / (2 * M)) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδβ : δ ≤ β / 2 := min_le_left _ _
  have hδM : δ * M ≤ 1 / 2 := by
    calc δ * M ≤ 1 / (2 * M) * M := mul_le_mul_of_nonneg_right (min_le_right _ _) hM0.le
      _ = 1 / 2 := by field_simp
  -- the bound on `P(e^{δ(V − V(x))})`
  have hmain : ∀ x, Integrable (fun y => Real.exp (δ * (V y - V x))) (P x) ∧
      ∫ y, Real.exp (δ * (V y - V x)) ∂P x ≤
        1 + δ * (∫ y, V y ∂P x - V x) + δ ^ 2 * M := fun x => by
    set u : X → ℝ := fun y => V y - V x with hu
    have hum : Measurable u := hV.sub_const _
    have hSp : MeasurableSet {y | V x ≤ V y} := measurableSet_le measurable_const hV
    have hSm : MeasurableSet {y | V y < V x} := measurableSet_lt hV measurable_const
    set R : X → ℝ := fun y => (if u y < 0 then u y ^ 2 else 0) +
      K * (if 0 ≤ u y then Real.exp (β * u y) else 0) with hR
    have hR1 : (fun y => if u y < 0 then u y ^ 2 else 0) =
        {y | V y < V x}.indicator (fun y => (V y - V x) ^ 2) := by
      funext y; simp only [hu, Set.indicator, Set.mem_ofPred_eq, sub_neg]
    have hR2 : (fun y => if 0 ≤ u y then Real.exp (β * u y) else 0) =
        {y | V x ≤ V y}.indicator (fun y => Real.exp (β * (V y - V x))) := by
      funext y; simp only [hu, Set.indicator, Set.mem_ofPred_eq, sub_nonneg]
    have hRint : Integrable R (P x) := by
      have e : R = fun y => {y | V y < V x}.indicator (fun y => (V y - V x) ^ 2) y +
          K * {y | V x ≤ V y}.indicator (fun y => Real.exp (β * (V y - V x))) y := by
        funext y; rw [hR]; simp only; rw [← hR1, ← hR2]
      rw [e]
      exact ((h27i x).integrable_indicator hSm).add
        (((h26i x).integrable_indicator hSp).const_mul K)
    have hRbd : ∫ y, R y ∂P x ≤ M := by
      have e : ∫ y, R y ∂P x = ∫ y in {y | V y < V x}, (V y - V x) ^ 2 ∂P x +
          K * ∫ y in {y | V x ≤ V y}, Real.exp (β * (V y - V x)) ∂P x := by
        have e1 : R = fun y => {y | V y < V x}.indicator (fun y => (V y - V x) ^ 2) y +
            K * {y | V x ≤ V y}.indicator (fun y => Real.exp (β * (V y - V x))) y := by
          funext y; rw [hR]; simp only; rw [← hR1, ← hR2]
        rw [e1, integral_add ((h27i x).integrable_indicator hSm)
          (((h26i x).integrable_indicator hSp).const_mul K), integral_const_mul,
          integral_indicator hSm, integral_indicator hSp]
      rw [e]
      have h1 := h27 x
      have h2 := h26 x
      calc ∫ y in {y | V y < V x}, (V y - V x) ^ 2 ∂P x +
            K * ∫ y in {y | V x ≤ V y}, Real.exp (β * (V y - V x)) ∂P x
          ≤ |d| + K * |c| := add_le_add (h1.trans (le_abs_self d))
            (mul_le_mul_of_nonneg_left (h2.trans (le_abs_self c)) hK0)
        _ ≤ M := by linarith
    have hpt : ∀ y, Real.exp (δ * u y) ≤ 1 + δ * u y + δ ^ 2 * R y := fun y =>
      exp_mul_le_increment hβ hδ0 hδβ (u y)
    have hEint : Integrable (fun y => Real.exp (δ * u y)) (P x) := by
      refine Integrable.mono' ((integrable_const (1 : ℝ)).add
        ((h26i x).integrable_indicator hSp)) (by fun_prop) (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply]
      by_cases hy : V x ≤ V y
      · rw [Set.indicator_of_mem (show y ∈ {y | V x ≤ V y} from hy)]
        have : Real.exp (δ * u y) ≤ Real.exp (β * (V y - V x)) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (by simp [hu]; linarith))
        linarith
      · rw [Set.indicator_of_notMem (show y ∉ {y | V x ≤ V y} from hy), add_zero]
        exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hδ0.le
          (by simp only [hu]; linarith [not_le.1 hy]))
    have huint : Integrable u (P x) := (hint x).sub (integrable_const _)
    refine ⟨hEint, ?_⟩
    calc ∫ y, Real.exp (δ * (V y - V x)) ∂P x = ∫ y, Real.exp (δ * u y) ∂P x := rfl
      _ ≤ ∫ y, (1 + δ * u y + δ ^ 2 * R y) ∂P x :=
          integral_mono hEint (((integrable_const 1).add (huint.const_mul δ)).add
            (hRint.const_mul _)) hpt
      _ = 1 + δ * (∫ y, V y ∂P x - V x) + δ ^ 2 * ∫ y, R y ∂P x := by
          have i1 : Integrable (fun y => 1 + δ * u y) (P x) :=
            (integrable_const 1).add (huint.const_mul δ)
          have i2 : Integrable (fun y => δ ^ 2 * R y) (P x) := hRint.const_mul _
          rw [integral_add (f := fun y => 1 + δ * u y) (g := fun y => δ ^ 2 * R y) i1 i2,
            integral_add (f := fun _ => (1 : ℝ)) (g := fun y => δ * u y) (integrable_const 1)
              (huint.const_mul δ), integral_const_mul, integral_const_mul, integral_const,
            probReal_univ, one_smul, hu,
            integral_sub (f := V) (g := fun _ => V x) (hint x) (integrable_const _),
            integral_const, probReal_univ, one_smul]
      _ ≤ 1 + δ * (∫ y, V y ∂P x - V x) + δ ^ 2 * M :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hRbd (by positivity))
  -- `δ² M ≤ δ/2`
  have hδ2 : δ ^ 2 * M ≤ δ / 2 := by nlinarith
  have hM1 : 1 ≤ M := by rw [hM]; have := abs_nonneg d; have := abs_nonneg c; nlinarith
  have hδhalf : δ ≤ 1 / 2 := by nlinarith
  set ρr : ℝ := 1 - δ / 2 with hρr
  set B : ℝ := Real.exp (δ * (b + 1)) * (1 + δ * |b| + δ ^ 2 * M) with hB
  refine ⟨δ, hδ0, lt_of_le_of_lt hδβ (by linarith), ENNReal.ofReal ρr, ENNReal.ofReal B,
    ENNReal.ofReal_lt_one.2 (by linarith), ENNReal.ofReal_ne_top, fun x => ?_⟩
  obtain ⟨hEint, hEbd⟩ := hmain x
  have hfac : ∀ y, Real.exp (δ * V y) = Real.exp (δ * V x) * Real.exp (δ * (V y - V x)) :=
    fun y => by rw [← Real.exp_add]; ring_nf
  have hlin : ∫⁻ y, ENNReal.ofReal (Real.exp (δ * V y)) ∂P x =
      ENNReal.ofReal (Real.exp (δ * V x) * ∫ y, Real.exp (δ * (V y - V x)) ∂P x) := by
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hEint.const_mul _)
      (Eventually.of_forall fun y => by positivity)]
    exact lintegral_congr fun y => by rw [hfac y]
  rw [hlin]
  by_cases hneg : ∫ y, V y ∂P x - V x ≤ -1
  · -- the geometric case
    have hI : ∫ y, Real.exp (δ * (V y - V x)) ∂P x ≤ ρr := by
      calc _ ≤ 1 + δ * (∫ y, V y ∂P x - V x) + δ ^ 2 * M := hEbd
        _ ≤ 1 + δ * (-1) + δ / 2 := add_le_add (add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hneg hδ0.le)) hδ2
        _ = ρr := by rw [hρr]; ring
    calc ENNReal.ofReal (Real.exp (δ * V x) * ∫ y, Real.exp (δ * (V y - V x)) ∂P x)
        ≤ ENNReal.ofReal (Real.exp (δ * V x) * ρr) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hI (Real.exp_pos _).le)
      _ = ENNReal.ofReal ρr * ENNReal.ofReal (Real.exp (δ * V x)) := by
          rw [mul_comm, ENNReal.ofReal_mul (by rw [hρr]; linarith)]
      _ ≤ _ := le_self_add
  · -- then `x ∈ C` and `V(x) < b + 1`
    have hxC : x ∈ C := by
      by_contra hx
      exact hneg (by linarith [hF1 x hx])
    have hxb : V x < b + 1 := by
      by_contra hx
      exact hneg (by linarith [hF2 x hxC, not_lt.1 hx])
    have hmem : x ∈ C ∩ {y | V y < b + 1} := ⟨hxC, hxb⟩
    rw [indicator_of_mem hmem]
    refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
    have hI : ∫ y, Real.exp (δ * (V y - V x)) ∂P x ≤ 1 + δ * |b| + δ ^ 2 * M := by
      calc _ ≤ 1 + δ * (∫ y, V y ∂P x - V x) + δ ^ 2 * M := hEbd
        _ ≤ 1 + δ * |b| + δ ^ 2 * M := by
            have : ∫ y, V y ∂P x - V x ≤ |b| := by
              linarith [hF2 x hxC, hV0 x, le_abs_self b]
            nlinarith
    have hI0 : 0 ≤ ∫ y, Real.exp (δ * (V y - V x)) ∂P x :=
      integral_nonneg fun y => (Real.exp_pos _).le
    calc Real.exp (δ * V x) * ∫ y, Real.exp (δ * (V y - V x)) ∂P x
        ≤ Real.exp (δ * (b + 1)) * (1 + δ * |b| + δ ^ 2 * M) :=
          mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxb.le hδ0.le)) hI hI0
            (Real.exp_pos _).le
      _ = B := rfl

/-! ### Theorem 16.3.1 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 16.3.1** (MT p. 407): let `Φ` be `ψ`-irreducible and aperiodic, and `V ≥ 0` a test
function satisfying (16.25) with a petite set `C`. If the right increments have uniformly bounded
exponential moments (16.26) and the left increments uniformly bounded second moments (16.27),
then for some `δ < β` the chain is `V*`-uniformly ergodic, `V* = e^{δV}`: it is positive, and
every invariant probability `μ` has `Σ rⁿ |||Pⁿ − 1 ⊗ μ|||_{V*} < ∞` for some `r > 1`. -/
theorem theorem_16_3_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ} (hV : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) {C : Set X} (hC : IsPetite P C) {b c d β : ℝ} (hβ : 0 < β)
    (hint : ∀ x, Integrable V (P x))
    (hF1 : ∀ x ∉ C, ∫ y, V y ∂P x ≤ V x - 1) (hF2 : ∀ x ∈ C, ∫ y, V y ∂P x ≤ b)
    (h26i : ∀ x, IntegrableOn (fun y => Real.exp (β * (V y - V x))) {y | V x ≤ V y} (P x))
    (h26 : ∀ x, ∫ y in {y | V x ≤ V y}, Real.exp (β * (V y - V x)) ∂P x ≤ c)
    (h27i : ∀ x, IntegrableOn (fun y => (V y - V x) ^ 2) {y | V y < V x} (P x))
    (h27 : ∀ x, ∫ y in {y | V y < V x}, (V y - V x) ^ 2 ∂P x ≤ d) :
    ∃ δ : ℝ, 0 < δ ∧ δ < β ∧ IsPositive P ψ ∧
      ∀ (μ : Measure X) [IsProbabilityMeasure μ], IsInvariant P μ →
        (∀ n, vErgDist (fun y => ENNReal.ofReal (Real.exp (δ * V y))) P μ n ≠ ∞) ∧
        IsVUniformlyErgodic (fun y => ENNReal.ofReal (Real.exp (δ * V y))) P μ ∧
        ∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧
          ∑' n, r ^ n * vErgDist (fun y => ENNReal.ofReal (Real.exp (δ * V y))) P μ n ≠ ∞ := by
  obtain ⟨δ, hδ0, hδβ, ρ, b', hρ, hb', hd⟩ :=
    increment_driftV4 hV hV0 hβ hint hF1 hF2 h26i h26 h27i h27
  set W : X → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (δ * V y)) with hW
  have hWm : Measurable W := (Real.measurable_exp.comp (hV.const_mul δ)).ennreal_ofReal
  have hW1 : ∀ x, 1 ≤ W x := fun x => by
    rw [hW, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hδ0.le (hV0 x)))
  have hWt : ∀ x, W x ≠ ∞ := fun x => ENNReal.ofReal_ne_top
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hC' : IsPetite P (C ∩ {y | V y < b + 1}) := by
    obtain ⟨a, ν, -, ha, hν, hle⟩ := hC
    exact ⟨a, ν, hCm.inter (measurableSet_lt hV measurable_const), ha, hν, fun x hx =>
      hle x hx.1⟩
  refine ⟨δ, hδ0, hδβ, ?_, fun μ _ hμ => ?_⟩
  · rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
    · exact absurd hψ.1 (by simp [Measure.eq_zero_of_isEmpty])
    exact (geometric_ergodic_of_driftV4 hψ hap hWm hW1 hρ hb' hC' hd (hWt x₀)).1
  obtain ⟨-, r, hr, -, R, hR, hbd⟩ := vErgDist_le_of_driftV4 hψ hap hWm hW1 hWt hρ hb' hC' hd μ hμ
  obtain ⟨hsum, hlim⟩ := theorem_16_1_2 hψ hap hWm hW1 hWt hρ hb' hC' hd μ hμ
  exact ⟨fun n => ne_top_of_le_ne_top (ENNReal.mul_ne_top hR (ENNReal.pow_ne_top
    (ENNReal.inv_ne_top.2 (zero_lt_one.trans hr).ne'))) (hbd n), ⟨hμ, hlim⟩, hsum⟩

/-! ### Increments of bounded range -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Increments of bounded range** (MT p. 420, (16.50)): if `|V(Φ₁) − V(x)| < B` almost surely
from every `x`, then (16.26) and (16.27) hold (with `β = 1`, `c = e^B`, `d = B²`), so a
`ψ`-irreducible aperiodic chain satisfying (16.25) is `e^{δV}`-uniformly ergodic for some
`δ > 0`. -/
theorem theorem_16_3_1_bounded_range {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ} (hV : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) {C : Set X} (hC : IsPetite P C) {b B : ℝ}
    (hint : ∀ x, Integrable V (P x))
    (hF1 : ∀ x ∉ C, ∫ y, V y ∂P x ≤ V x - 1) (hF2 : ∀ x ∈ C, ∫ y, V y ∂P x ≤ b)
    (hB : ∀ x, ∀ᵐ y ∂P x, |V y - V x| < B) :
    ∃ δ : ℝ, 0 < δ ∧ IsPositive P ψ ∧
      ∀ (μ : Measure X) [IsProbabilityMeasure μ], IsInvariant P μ →
        (∀ n, vErgDist (fun y => ENNReal.ofReal (Real.exp (δ * V y))) P μ n ≠ ∞) ∧
        IsVUniformlyErgodic (fun y => ENNReal.ofReal (Real.exp (δ * V y))) P μ := by
  have hle : ∀ x (S : Set X) (f : X → ℝ) (M : ℝ), 0 ≤ M → Measurable f →
      (∀ᵐ y ∂P x, |f y| ≤ M) → IntegrableOn f S (P x) ∧ ∫ y in S, f y ∂P x ≤ M := by
    intro x S f M hM hf hfM
    have hfM' : ∀ᵐ y ∂(P x).restrict S, ‖f y‖ ≤ M :=
      ae_restrict_of_ae (hfM.mono fun y hy => by rw [Real.norm_eq_abs]; exact hy)
    have hI : IntegrableOn f S (P x) :=
      Measure.integrableOn_of_bounded (measure_ne_top (P x) S) hf.aestronglyMeasurable hfM'
    refine ⟨hI, ?_⟩
    calc ∫ y in S, f y ∂P x ≤ ∫ y in S, M ∂P x :=
          integral_mono_ae hI (integrable_const M)
            (hfM'.mono fun y hy => (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at hy))
      _ = (P x).real S * M := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right (by
          rw [measureReal_def]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one))
          hM
      _ = M := one_mul M
  have hB0 : ∀ x, 0 ≤ B := fun x => by
    obtain ⟨y, hy⟩ := (hB x).exists
    exact (abs_nonneg _).trans hy.le
  have h26 : ∀ x, IntegrableOn (fun y => Real.exp (1 * (V y - V x))) {y | V x ≤ V y} (P x) ∧
      ∫ y in {y | V x ≤ V y}, Real.exp (1 * (V y - V x)) ∂P x ≤ Real.exp B := fun x =>
    hle x _ _ _ (Real.exp_pos B).le (Real.measurable_exp.comp ((hV.sub_const _).const_mul 1))
      ((hB x).mono fun y hy => by
        rw [abs_of_pos (Real.exp_pos _), one_mul]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans hy.le))
  have h27 : ∀ x, IntegrableOn (fun y => (V y - V x) ^ 2) {y | V y < V x} (P x) ∧
      ∫ y in {y | V y < V x}, (V y - V x) ^ 2 ∂P x ≤ B ^ 2 := fun x =>
    hle x _ _ _ (sq_nonneg B) ((hV.sub_const _).pow_const 2) ((hB x).mono fun y hy => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hy.le 2)
  obtain ⟨δ, hδ0, -, hpos, hU⟩ := theorem_16_3_1 hψ hap hV hV0 hC one_pos hint hF1 hF2
    (fun x => (h26 x).1) (fun x => (h26 x).2) (fun x => (h27 x).1) (fun x => (h27 x).2)
  exact ⟨δ, hδ0, hpos, fun μ _ hμ => ⟨(hU μ hμ).1, (hU μ hμ).2.1⟩⟩

/-! ### The need for (16.27): the chain (15.20) -/

/-- The minimal solution of (16.25) for the chain (15.20) (MT p. 409): `V₀(0) = 0` and
`V₀(j) = (1 − β_j)⁻¹ = E_j[σ_0]` for `j ≥ 1`. -/
noncomputable def nonGeomV₀ (β : ℕ → ℝ≥0∞) (j : ℕ) : ℝ :=
  if j = 0 then 0 else (1 - (β j).toReal)⁻¹

/-- `V₀(j) = E_j[σ_0]` (MT p. 409; `E_j[τ_0] = (1 − β_j)⁻¹`, `nonGeom_meanReturnTime_pos`). -/
theorem nonGeomV₀_eq_meanHitTime (γ : Measure ℕ) [IsProbabilityMeasure γ] {β : ℕ → ℝ≥0∞}
    (hβ : ∀ j, β j ≤ 1) {j : ℕ} (hj : j ≠ 0) (hβj : β j < 1) :
    haveI := isMarkovKernel_nonGeomKernel γ hβ
    ENNReal.ofReal (nonGeomV₀ β j) = meanHitTime (nonGeomKernel γ β) {0} j := by
  have := isMarkovKernel_nonGeomKernel γ hβ
  rw [meanHitTime_of_notMem _ (measurableSet_singleton 0) (by simpa using hj),
    nonGeom_meanReturnTime_pos γ hβ hj, nonGeomV₀]
  simp only [hj, ite_false]
  have hlt : (β j).toReal < 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hβj
  rw [ENNReal.ofReal_inv_of_pos (by linarith), ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
    ENNReal.ofReal_one, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hβ j))]

/-- `V₀(j) ≥ 1` for `j ≥ 1`. -/
theorem one_le_nonGeomV₀ {β : ℕ → ℝ≥0∞} (hβ : ∀ j, β j ≤ 1) {j : ℕ} (hj : j ≠ 0)
    (hβj : β j < 1) : 1 ≤ nonGeomV₀ β j := by
  have hlt : (β j).toReal < 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hβj
  have h0 : 0 ≤ (β j).toReal := ENNReal.toReal_nonneg
  have _ := hβ j
  simp only [nonGeomV₀, hj, ite_false]
  rw [le_inv_comm₀ one_pos (by linarith), inv_one]
  linarith

/-- The integral of `f` over `S` for `P(j, ·) = β_j δ_j + (1 − β_j) δ_0`, `j ≥ 1`. -/
theorem nonGeom_setIntegral (γ : Measure ℕ) {β : ℕ → ℝ≥0∞} (hβ : ∀ j, β j ≤ 1) {j : ℕ}
    (hj : j ≠ 0) (S : Set ℕ) (f : ℕ → ℝ) :
    ∫ y in S, f y ∂nonGeomKernel γ β j =
      (β j).toReal * S.indicator f j + (1 - (β j).toReal) * S.indicator f 0 := by
  rw [← integral_indicator (measurableSet_of_countable S), nonGeomKernel_pos γ β hj,
    integral_add_measure (Integrable.smul_measure (integrable_dirac enorm_lt_top)
      (by simpa using ne_top_of_le_ne_top ENNReal.one_ne_top (hβ j)))
      (Integrable.smul_measure (integrable_dirac enorm_lt_top) (by simp)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_sub_of_le (hβ j) ENNReal.one_ne_top, ENNReal.toReal_one, smul_eq_mul,
    smul_eq_mul]

/-- **The right increments of `V₀` are bounded for `j > 0`** (MT p. 409): from `j ≥ 1` the chain
stays or jumps to `0`, where `V₀` is smaller, so `∫_{V₀ ≥ V₀(j)} P(j, dy) e^{θ(V₀(y) − V₀(j))}
= β_j ≤ 1` for every `θ`. -/
theorem nonGeom_right_increments (γ : Measure ℕ) {β : ℕ → ℝ≥0∞} (hβ : ∀ j, β j ≤ 1) {j : ℕ}
    (hj : j ≠ 0) (hβj : β j < 1) (θ : ℝ) :
    ∫ y in {y | nonGeomV₀ β j ≤ nonGeomV₀ β y},
      Real.exp (θ * (nonGeomV₀ β y - nonGeomV₀ β j)) ∂nonGeomKernel γ β j = (β j).toReal := by
  rw [nonGeom_setIntegral γ hβ hj]
  have h1 := one_le_nonGeomV₀ hβ hj hβj
  have hV00 : nonGeomV₀ β 0 = 0 := by simp [nonGeomV₀]
  have h0 : (0 : ℕ) ∉ {y | nonGeomV₀ β j ≤ nonGeomV₀ β y} := fun h => by
    have h' : nonGeomV₀ β j ≤ nonGeomV₀ β 0 := h
    rw [hV00] at h'; linarith
  rw [Set.indicator_of_mem (s := {y | nonGeomV₀ β j ≤ nonGeomV₀ β y})
    (le_refl (nonGeomV₀ β j)), Set.indicator_of_notMem h0]
  simp

/-- **The left increments of `V₀`** (MT p. 409): for `j ≥ 1`,
`∫_{V₀ < V₀(j)} P(j, dy) (V₀(y) − V₀(j))² = P(j, 0) (1 − β_j)⁻² = (1 − β_j)⁻¹`. -/
theorem nonGeom_left_increments (γ : Measure ℕ) {β : ℕ → ℝ≥0∞} (hβ : ∀ j, β j ≤ 1) {j : ℕ}
    (hj : j ≠ 0) (hβj : β j < 1) :
    ∫ y in {y | nonGeomV₀ β y < nonGeomV₀ β j},
      (nonGeomV₀ β y - nonGeomV₀ β j) ^ 2 ∂nonGeomKernel γ β j = (1 - (β j).toReal)⁻¹ := by
  rw [nonGeom_setIntegral γ hβ hj]
  have h1 := one_le_nonGeomV₀ hβ hj hβj
  have hV00 : nonGeomV₀ β 0 = 0 := by simp [nonGeomV₀]
  have h0 : (0 : ℕ) ∈ {y | nonGeomV₀ β y < nonGeomV₀ β j} := by
    have : nonGeomV₀ β 0 < nonGeomV₀ β j := by rw [hV00]; linarith
    exact this
  rw [Set.indicator_of_notMem (s := {y | nonGeomV₀ β y < nonGeomV₀ β j})
    (lt_irrefl (nonGeomV₀ β j)), Set.indicator_of_mem h0]
  have hlt : (β j).toReal < 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hβj
  have hpos : 0 < 1 - (β j).toReal := by linarith
  simp only [nonGeomV₀, hj, ite_false, ite_true, mul_zero, zero_add, zero_sub, neg_sq]
  field_simp

/-- **(16.27) fails for the chain (15.20) when `β_j → 1`** (MT p. 409): no `d` bounds the left
increments of `V₀`. Together with `nonGeom_not_geomErgodic` this shows that (16.27) cannot be
dropped from Theorem 16.3.1. -/
theorem nonGeom_left_increments_unbounded (γ : Measure ℕ) {β : ℕ → ℝ≥0∞} (hβ : ∀ j, β j ≤ 1)
    (hβ1 : ∀ j, j ≠ 0 → β j < 1) (hlim : Tendsto β atTop (𝓝 1)) :
    ¬ ∃ d : ℝ, ∀ j, j ≠ 0 → ∫ y in {y | nonGeomV₀ β y < nonGeomV₀ β j},
      (nonGeomV₀ β y - nonGeomV₀ β j) ^ 2 ∂nonGeomKernel γ β j ≤ d := by
  rintro ⟨d, hd⟩
  have hlimr : Tendsto (fun j => (β j).toReal) atTop (𝓝 1) := by
    have h := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim
    rw [ENNReal.toReal_one] at h
    exact h
  set ε : ℝ := (|d| + 1)⁻¹ with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨j, hj⟩ := ((hlimr.eventually (lt_mem_nhds (show 1 - ε < 1 by linarith))).and
    (eventually_ge_atTop 1)).exists
  have hj0 : j ≠ 0 := by omega
  have h := hd j hj0
  rw [nonGeom_left_increments γ hβ hj0 (hβ1 j hj0)] at h
  have hlt : (β j).toReal < 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_strict_mono ENNReal.one_ne_top (hβ1 j hj0)
  have hpos : 0 < 1 - (β j).toReal := by linarith
  have hsmall : 1 - (β j).toReal < ε := by linarith [hj.1]
  have hbig : |d| + 1 < (1 - (β j).toReal)⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hpos]; exact hsmall
  linarith [le_abs_self d]

end MeynTweedie.Epilogue
