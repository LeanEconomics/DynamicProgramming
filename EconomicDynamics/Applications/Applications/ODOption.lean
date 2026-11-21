/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.ODBasic
import Applications.MDPStoppingExamples
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Mul

/-!
# Option exercise: the Bellman equation and the investment threshold

Miao, §8.1, pp. 231–233. The lump-sum payoff `z` of an irreversible project is drawn i.i.d. from
a distribution `F` on `[0, B]` (a probability measure on `ℝ` concentrated on `[0, B]`), the
investment cost is `I < B`, and `β ∈ (0, 1)`. The Bellman equation (p. 231) is
`V(z) = max(β ∫ V dF, z − I)` on `[0, B]` (`od_OptionBellman`). It is the stationary Bellman
equation of the stopping problem `optionExercise` of §5.2.2 (`od_option_bellman_iff_stopping`).

* `od_option_exists_unique`: the Bellman equation has exactly one solution on `[0, B]`, namely
  `V(z) = max(q, z − I)` with `q` the unique fixed point of `q = β ∫ max(q, z − I) dF`.
* `od_option_mono_convex` (Figure 8.1): `V` is increasing and convex.
* `od_option_threshold` (p. 232): with `z* = β∫V dF + I`, `V(z) = z − I` for `z > z*` and
  `V(z) = β ∫ V dF` for `z ≤ z*`; `od_option_threshold_unique_set`: `z*` is the only point of
  `[0, B]` beyond which investing is strictly optimal.
* `od_option_at_threshold` (p. 232): the chain of equalities for `V(z*)`.
* `od_option_threshold_eq` (p. 232): `z* − I = β/(1 − β) ∫_{z*}^B (z′ − z*) dF(z′)`.
* `od_option_threshold_root_unique` (p. 233): this equation has exactly one root, it lies in
  `[I, B)`, and in `(0, B)` when `I > 0`.
* `od_option_threshold_gt_iff` (p. 233): `z* > I` iff `F` puts positive mass above `I`.
  **Correction.** The book says `z* > I` without qualification; if `F` puts no mass above `I`
  then `z* = I` (`od_option_threshold_dirac`, with `F` the point mass at `0`).
* `od_option_npv` (p. 233): projects with `I < z ≤ z*` have positive net present value but are
  not undertaken.

The identification of the solution of the Bellman equation with the value of the stopping
problem (the book's "by the dynamic programming theory of Section 7.3.1") is not formalised; the
book only uses the Bellman equation.
-/

namespace Miao.Applications

open MeasureTheory ProbabilityTheory

/-- The Bellman equation of the option exercise problem (Miao, p. 231) on `[0, B]`. -/
def od_OptionBellman (F : Measure ℝ) (B I β : ℝ) (V : ℝ → ℝ) : Prop :=
  ∀ z ∈ Set.Icc 0 B, V z = max (β * ∫ z', V z' ∂F) (z - I)

/-- The scalar Bellman map for the continuation value, `q ↦ β ∫ max(q, z − I) dF`. -/
noncomputable def od_optΦ (F : Measure ℝ) (I β q : ℝ) : ℝ := β * ∫ z, max q (z - I) ∂F

/-- Miao, p. 231: the option exercise Bellman equation is the stationary Bellman equation
`V(z) = max(g(z), f(z) + β ∫ V dQ(z))` of the stopping problem `optionExercise` of §5.2.2 with
i.i.d. payoffs `Q(z, ·) = F` and `y(z) = z`. -/
theorem od_option_bellman_iff_stopping (F : Measure ℝ) [IsProbabilityMeasure F] (B I β : ℝ)
    (V : ℝ → ℝ) (t : ℕ) :
    od_OptionBellman F B I β V ↔ ∀ z ∈ Set.Icc 0 B,
      V z = max ((optionExercise (Kernel.const ℝ F) id I β).f t z +
        (optionExercise (Kernel.const ℝ F) id I β).β *
          ∫ z', V z' ∂((optionExercise (Kernel.const ℝ F) id I β).Q t z))
        ((optionExercise (Kernel.const ℝ F) id I β).g t z) := by
  simp [od_OptionBellman, optionExercise]

variable {F : Measure ℝ} [IsProbabilityMeasure F] {B I β : ℝ}

theorem od_integrable_sub (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (I : ℝ) :
    Integrable (fun z => z - I) F :=
  od_integrable_of_continuous hF (continuous_id.sub continuous_const)

theorem od_optΦ_lipschitz (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 ≤ β) (x y : ℝ) :
    |od_optΦ F I β x - od_optΦ F I β y| ≤ β * |x - y| := by
  have := od_lipschitz_stop (od_integrable_sub hF I) 0 hβ0 x y
  simpa [od_optΦ] using this

/-- The scalar fixed-point equation has exactly one solution. -/
theorem od_optΦ_exists_unique (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃! q, od_optΦ F I β q = q :=
  od_scalar_fixed hβ0 hβ1 (od_optΦ_lipschitz hF hβ0.le)

/-- The continuation value is nonnegative: `q = β∫ max(q, z − I) dF ≥ βq`. -/
theorem od_optΦ_fixed_nonneg (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    {q : ℝ} (hq : od_optΦ F I β q = q) : 0 ≤ q := by
  have hle : q ≤ ∫ z, max q (z - I) ∂F := by
    have := integral_mono (integrable_const q) ((integrable_const q).sup (od_integrable_sub hF I))
      fun z => le_max_left q (z - I)
    simpa using this
  unfold od_optΦ at hq
  nlinarith [mul_le_mul_of_nonneg_left hle hβ0.le]

omit [IsProbabilityMeasure F] in
/-- A solution of the Bellman equation is `max(q, z − I)` on `[0, B]`, so its integral is that
of `max(q, z − I)`. -/
theorem od_option_integral_eq (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) {V : ℝ → ℝ}
    (hV : od_OptionBellman F B I β V) :
    ∫ z, V z ∂F = ∫ z, max (β * ∫ z', V z' ∂F) (z - I) ∂F :=
  integral_congr_ae (hF.mono fun z hz => hV z hz)

omit [IsProbabilityMeasure F] in
/-- The continuation value `β∫V dF` of a solution is a fixed point of the scalar map. -/
theorem od_option_cont_fixed (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) {V : ℝ → ℝ}
    (hV : od_OptionBellman F B I β V) :
    od_optΦ F I β (β * ∫ z, V z ∂F) = β * ∫ z, V z ∂F := by
  unfold od_optΦ
  rw [← od_option_integral_eq hF hV]

omit [IsProbabilityMeasure F] in
/-- A fixed point `q` gives the solution `V(z) = max(q, z − I)`. -/
theorem od_option_fixed_bellman {q : ℝ} (hq : od_optΦ F I β q = q) :
    od_OptionBellman F B I β (fun z => max q (z - I)) := by
  intro z _
  change max q (z - I) = max (od_optΦ F I β q) (z - I)
  rw [hq]

/-- Miao, p. 231 ("there exists a unique solution `V` to the Bellman equation"): the option
exercise Bellman equation has a solution, `max(q, z − I)` with `q = β∫ max(q, z′ − I) dF(z′)`,
and every solution agrees with it on `[0, B]`. -/
theorem od_option_exists_unique (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ q, od_optΦ F I β q = q ∧ od_OptionBellman F B I β (fun z => max q (z - I)) ∧
      ∀ W, od_OptionBellman F B I β W → ∀ z ∈ Set.Icc 0 B, W z = max q (z - I) := by
  obtain ⟨q, hq, huniq⟩ := od_optΦ_exists_unique (I := I) hF hβ0 hβ1
  refine ⟨q, hq, od_option_fixed_bellman hq, fun W hW z hz => ?_⟩
  rw [hW z hz, huniq _ (od_option_cont_fixed hF hW)]

omit [IsProbabilityMeasure F] in
/-- **Figure 8.1** (Miao, pp. 231–232): the option value is increasing and convex on `[0, B]`. -/
theorem od_option_mono_convex {V : ℝ → ℝ} (hV : od_OptionBellman F B I β V) :
    MonotoneOn V (Set.Icc 0 B) ∧ ConvexOn ℝ (Set.Icc 0 B) V := by
  set q := β * ∫ z', V z' ∂F
  refine ⟨fun x hx y hy hxy => ?_, ?_⟩
  · rw [hV x hx, hV y hy]
    exact max_le_max le_rfl (by linarith)
  · have hc : ConvexOn ℝ (Set.Icc 0 B) (fun z => max q (z - I)) := by
      have h1 : ConvexOn ℝ (Set.Icc (0 : ℝ) B) (fun z => z - I) :=
        (convexOn_id (convex_Icc 0 B)).sub (concaveOn_const I (convex_Icc 0 B))
      exact (convexOn_const q (convex_Icc 0 B)).sup h1
    exact hc.congr fun z hz => (hV z hz).symm

omit [IsProbabilityMeasure F] in
/-- Miao, p. 232: with the threshold `z* = β∫V dF + I`, the value function is `z − I` above `z*`
and the constant `β ∫ V dF` at and below `z*`. -/
theorem od_option_threshold {V : ℝ → ℝ} (hV : od_OptionBellman F B I β V) :
    ∀ z ∈ Set.Icc 0 B,
      (β * ∫ z', V z' ∂F + I < z → V z = z - I) ∧
      (z ≤ β * ∫ z', V z' ∂F + I → V z = β * ∫ z', V z' ∂F) := by
  intro z hz
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hV z hz, max_eq_right (by linarith)]
  · rw [hV z hz, max_eq_left (by linarith)]

omit [IsProbabilityMeasure F] in
/-- `∫_{Ioi x} (z − x) dF = ∫ max(z − x, 0) dF`. -/
theorem od_setIntegral_Ioi_eq (x : ℝ) :
    ∫ z in Set.Ioi x, (z - x) ∂F = ∫ z, max (z - x) 0 ∂F := by
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext z
  by_cases hz : x < z
  · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hz), max_eq_left (by linarith)]
  · rw [Set.indicator_of_notMem (by simpa using hz), max_eq_right (by linarith [not_lt.1 hz])]

/-- Miao, p. 232: the chain of equalities at the threshold `z* = β∫V dF + I`:
`V(z*) = β∫V dF = z* − I = β∫_{[0, z*]} (z* − I) dF + β∫_{(z*, B]} (z′ − I) dF
= β∫ (z* − I) dF + β∫_{(z*, B]} (z′ − z*) dF`. -/
theorem od_option_at_threshold (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) {V : ℝ → ℝ}
    (hV : od_OptionBellman F B I β V) (hzs : β * ∫ z', V z' ∂F + I ∈ Set.Icc 0 B) :
    let zs := β * ∫ z', V z' ∂F + I
    V zs = β * ∫ z', V z' ∂F ∧ β * ∫ z', V z' ∂F = zs - I ∧
      zs - I = β * ∫ _z' in Set.Iic zs, (zs - I) ∂F + β * ∫ z' in Set.Ioi zs, (z' - I) ∂F ∧
      zs - I = β * ∫ _z', (zs - I) ∂F + β * ∫ z' in Set.Ioi zs, (z' - zs) ∂F := by
  intro zs
  have hV' : ∀ z ∈ Set.Icc 0 B, V z = max (zs - I) (z - I) := fun z hz => by
    rw [hV z hz]; congr 1; simp only [zs]; ring
  have hint : ∫ z', V z' ∂F = ∫ z', max (zs - I) (z' - I) ∂F :=
    integral_congr_ae (hF.mono fun z hz => hV' z hz)
  have hiM : Integrable (fun z' => max (zs - I) (z' - I)) F :=
    (integrable_const _).sup (od_integrable_sub hF I)
  have hsplit : ∫ z', max (zs - I) (z' - I) ∂F =
      ∫ z' in Set.Iic zs, (zs - I) ∂F + ∫ z' in Set.Ioi zs, (z' - I) ∂F := by
    rw [← integral_add_compl (s := Set.Ioi zs) measurableSet_Ioi hiM, Set.compl_Ioi, add_comm]
    congr 1
    · refine setIntegral_congr_fun measurableSet_Iic fun z hz => ?_
      exact max_eq_left (by linarith [Set.mem_Iic.1 hz])
    · refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
      exact max_eq_right (by linarith [Set.mem_Ioi.1 hz])
  have hsplit2 : ∫ z' in Set.Iic zs, (zs - I) ∂F + ∫ z' in Set.Ioi zs, (z' - I) ∂F =
      ∫ _z', (zs - I) ∂F + ∫ z' in Set.Ioi zs, (z' - zs) ∂F := by
    have h1 : ∫ z' in Set.Ioi zs, (z' - I) ∂F =
        ∫ z' in Set.Ioi zs, (zs - I) ∂F + ∫ z' in Set.Ioi zs, (z' - zs) ∂F := by
      rw [← integral_add (integrable_const _).integrableOn
        ((od_integrable_sub hF zs).integrableOn)]
      congr 1; funext z; ring
    have h2 := integral_add_compl (μ := F) (f := fun _ : ℝ => zs - I) (s := Set.Ioi zs)
      measurableSet_Ioi (integrable_const _)
    rw [Set.compl_Ioi] at h2
    rw [h1, ← h2]
    ring
  have hzI : β * ∫ z', V z' ∂F = zs - I := by simp only [zs]; ring
  refine ⟨?_, hzI, ?_, ?_⟩
  · rw [hV' zs hzs, max_self, hzI]
  · rw [← mul_add, ← hsplit, ← hint, hzI]
  · rw [← mul_add, ← hsplit2, ← hsplit, ← hint, hzI]

/-- Miao, p. 232: the threshold equation `z* − I = β/(1 − β) ∫_{z*}^B (z′ − z*) dF(z′)`, for the
threshold `z* = β∫V dF + I` of the solution of the Bellman equation. -/
theorem od_option_threshold_eq (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ1 : β < 1) {V : ℝ → ℝ}
    (hV : od_OptionBellman F B I β V) :
    (β * ∫ z', V z' ∂F + I) - I =
      β / (1 - β) * ∫ z' in Set.Ioi (β * ∫ z', V z' ∂F + I), (z' - (β * ∫ z', V z' ∂F + I)) ∂F := by
  set q := β * ∫ z', V z' ∂F
  have hfix : od_optΦ F I β q = q := od_option_cont_fixed hF hV
  unfold od_optΦ at hfix
  rw [od_integral_max_eq (od_integrable_sub hF I) q] at hfix
  rw [od_setIntegral_Ioi_eq]
  have hfun : (fun z : ℝ => max (z - I - q) 0) = fun z => max (z - (q + I)) 0 := by
    funext z; congr 1; ring
  rw [hfun] at hfix
  have hne : (1 - β) ≠ 0 := by linarith
  field_simp
  linarith

/-- The function whose roots are the thresholds,
`ψ(x) = x − I − β/(1 − β) ∫_{Ioi x} (z′ − x) dF`. -/
noncomputable def od_threshψ (F : Measure ℝ) (I β x : ℝ) : ℝ :=
  x - I - β / (1 - β) * ∫ z' in Set.Ioi x, (z' - x) ∂F

/-- `ψ` is strictly increasing. -/
theorem od_threshψ_strictMono (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) :
    StrictMono (od_threshψ F I β) := by
  intro x y hxy
  unfold od_threshψ
  rw [od_setIntegral_Ioi_eq, od_setIntegral_Ioi_eq]
  have hmono : ∫ z, max (z - y) 0 ∂F ≤ ∫ z, max (z - x) 0 ∂F :=
    integral_mono ((od_integrable_sub hF y).sup (integrable_const 0))
      ((od_integrable_sub hF x).sup (integrable_const 0))
      fun z => max_le_max (by linarith) le_rfl
  have hc : 0 ≤ β / (1 - β) := div_nonneg hβ0.le (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hmono hc]

/-- Miao, p. 233 ("one can verify that there exists a unique solution in `(0, B)`"): when
`I < B`, the threshold equation has exactly one root `z*`, the threshold of the solution of the
Bellman equation; it lies in `[I, B)`, hence in `(0, B)` when `I > 0`. -/
theorem od_option_threshold_root_unique (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hIB : I < B) {V : ℝ → ℝ} (hV : od_OptionBellman F B I β V) :
    (∀ x, od_threshψ F I β x = 0 ↔ x = β * ∫ z', V z' ∂F + I) ∧
      β * ∫ z', V z' ∂F + I ∈ Set.Ico I B ∧
      (0 < I → β * ∫ z', V z' ∂F + I ∈ Set.Ioo 0 B) := by
  set zs := β * ∫ z', V z' ∂F + I
  have hroot : od_threshψ F I β zs = 0 := by
    have := od_option_threshold_eq hF hβ1 hV
    unfold od_threshψ
    simp only [zs] at this ⊢
    linarith
  have hsm := od_threshψ_strictMono (I := I) hF hβ0 hβ1
  have hq0 : 0 ≤ β * ∫ z', V z' ∂F :=
    od_optΦ_fixed_nonneg hF hβ0 hβ1 (od_option_cont_fixed hF hV)
  have hB : od_threshψ F I β B = B - I := by
    unfold od_threshψ
    rw [od_setIntegral_Ioi_eq]
    have : ∫ z, max (z - B) 0 ∂F = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (hF.mono fun z hz => by
        simp only
        exact max_eq_right (by linarith [hz.2]))]
      simp
    rw [this]; ring
  have hzsB : zs < B := hsm.lt_iff_lt.1 (by rw [hroot, hB]; linarith)
  refine ⟨fun x => ⟨fun hx => hsm.injective (hx.trans hroot.symm), fun hx => hx ▸ hroot⟩,
    ⟨by simp only [zs]; linarith, hzsB⟩, fun hI => ⟨by simp only [zs]; linarith, hzsB⟩⟩

/-- Miao, p. 232 ("there exists a unique threshold value `z*`"): when `0 ≤ I < B`, the set of
payoffs in `[0, B]` at which investing is strictly better than waiting is `(z*, B]`, and `z*` is
the only `t ∈ [0, B]` with this property. -/
theorem od_option_threshold_unique_set (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hI : 0 ≤ I) (hIB : I < B) {V : ℝ → ℝ} (hV : od_OptionBellman F B I β V) :
    let zs := β * ∫ z', V z' ∂F + I
    {z ∈ Set.Icc 0 B | β * ∫ z', V z' ∂F < z - I} = Set.Ioc zs B ∧
      ∀ t ∈ Set.Icc 0 B, {z ∈ Set.Icc 0 B | β * ∫ z', V z' ∂F < z - I} = Set.Ioc t B →
        t = zs := by
  intro zs
  obtain ⟨-, ⟨hIzs, hzsB⟩, -⟩ := od_option_threshold_root_unique hF hβ0 hβ1 hIB hV
  have hset : {z ∈ Set.Icc 0 B | β * ∫ z', V z' ∂F < z - I} = Set.Ioc zs B := by
    ext z
    simp only [Set.mem_Icc, Set.mem_Ioc, zs]
    constructor
    · rintro ⟨⟨-, hzB⟩, h⟩; exact ⟨by linarith, hzB⟩
    · rintro ⟨h, hzB⟩
      refine ⟨⟨?_, hzB⟩, by linarith⟩
      have : zs ≥ I := hIzs
      simp only [zs] at this
      linarith
  refine ⟨hset, fun t ht htset => ?_⟩
  rw [hset] at htset
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : zs ∈ Set.Ioc t B := ⟨hlt, hzsB.le⟩
    rw [← htset] at this
    exact lt_irrefl _ this.1
  · have : t ∈ Set.Ioc zs B := ⟨hlt, ht.2⟩
    rw [htset] at this
    exact lt_irrefl _ this.1

/-- Miao, p. 233 ("we see that `z* > I`"), corrected: the threshold exceeds the cost `I` if and
only if `F` puts positive mass on payoffs above `I`. -/
theorem od_option_threshold_gt_iff (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    {V : ℝ → ℝ} (hV : od_OptionBellman F B I β V) :
    I < β * ∫ z', V z' ∂F + I ↔ 0 < F (Set.Ioi I) := by
  have heq := od_option_threshold_eq hF hβ1 hV
  rw [od_setIntegral_Ioi_eq] at heq
  set q := β * ∫ z', V z' ∂F
  have hpos : ∀ x, 0 < ∫ z, max (z - x) 0 ∂F ↔ 0 < F (Set.Ioi x) := fun x => by
    rw [integral_pos_iff_support_of_nonneg (f := fun z => max (z - x) 0) (fun z => le_max_right _ _)
      ((od_integrable_sub hF x).sup (integrable_const 0))]
    have : Function.support (fun z => max (z - x) 0) = Set.Ioi x := by
      ext z
      simp only [Function.mem_support, Set.mem_Ioi, ne_eq]
      constructor
      · intro h; by_contra h'; exact h (max_eq_right (by linarith [not_lt.1 h']))
      · intro h; rw [max_eq_left (by linarith)]; linarith
    rw [this]
  have hc : 0 < β / (1 - β) := div_pos hβ0 (by linarith)
  have hq0 : 0 ≤ q := od_optΦ_fixed_nonneg hF hβ0 hβ1 (od_option_cont_fixed hF hV)
  constructor
  · intro h
    have hq : 0 < q := by linarith
    have hint : 0 < ∫ z, max (z - (q + I)) 0 ∂F := by
      by_contra h'
      push Not at h'
      have : β / (1 - β) * ∫ z, max (z - (q + I)) 0 ∂F ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc.le h'
      linarith
    exact lt_of_lt_of_le ((hpos _).1 hint) (measure_mono (Set.Ioi_subset_Ioi (by linarith)))
  · intro h
    by_contra h'
    have hq : q = 0 := le_antisymm (by linarith [not_lt.1 h']) hq0
    rw [hq, zero_add] at heq
    have := mul_pos hc ((hpos I).2 h)
    linarith

/-- Miao, p. 233, counterexample to "`z* > I`" as printed: with all payoffs at `0`
(`F = δ₀`, `0 ≤ I < B`), the continuation value is `0` and the threshold is exactly `I`. -/
theorem od_option_threshold_dirac (hβ0 : 0 < β) (hβ1 : β < 1) (hI : 0 ≤ I) (hIB : I < B)
    {V : ℝ → ℝ} (hV : od_OptionBellman (Measure.dirac 0) B I β V) :
    β * ∫ z', V z' ∂(Measure.dirac 0) + I = I ∧
      ¬ I < β * ∫ z', V z' ∂(Measure.dirac 0) + I := by
  have hF : ∀ᵐ z ∂(Measure.dirac (0 : ℝ)), z ∈ Set.Icc 0 B :=
    (ae_dirac_iff measurableSet_Icc).2 ⟨le_rfl, by linarith⟩
  have h := (od_option_threshold_gt_iff hF hβ0 hβ1 hV).not
  have hm : ¬ 0 < Measure.dirac (0 : ℝ) (Set.Ioi I) := by
    rw [Measure.dirac_apply' _ measurableSet_Ioi]
    simp [Set.indicator, not_lt.2 hI]
  have hn := h.2 hm
  have hq0 : 0 ≤ β * ∫ z', V z' ∂(Measure.dirac 0) :=
    od_optΦ_fixed_nonneg hF hβ0 hβ1 (od_option_cont_fixed hF hV)
  exact ⟨le_antisymm (not_lt.1 hn) (by linarith), hn⟩

omit [IsProbabilityMeasure F] in
/-- Miao, p. 233 (the net present value rule): a project with `I < z ≤ z*` has positive net
present value `z − I`, but waiting is optimal: `V(z) = β∫V dF ≥ z − I`. -/
theorem od_option_npv {V : ℝ → ℝ} (hV : od_OptionBellman F B I β V) {z : ℝ}
    (hz : z ∈ Set.Icc 0 B) (hIz : I < z) (hzs : z ≤ β * ∫ z', V z' ∂F + I) :
    0 < z - I ∧ z - I ≤ β * ∫ z', V z' ∂F ∧ V z = β * ∫ z', V z' ∂F :=
  ⟨by linarith, by linarith, (od_option_threshold hV z hz).2 hzs⟩

end Miao.Applications
