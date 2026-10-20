/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.ShocksContraction
import FixedPointArguments.SchauderBoundedContinuous
import FixedPointArguments.Brouwer

/-!
# Partially observed shocks: Proposition 7 (Schauder), (7), and finite `Z` (Brouwer)

SLP §17.6, pp. 535–539: Assumption 17.6, Proposition 7, Exercises 17.11 and 17.13 and the
equicontinuity argument (Step 4), **with the correct conditional weights** `2θ/(b² − a²)`
(Exercise 17.12 is false, `ex_17_12_counterexample` in `FixedPointArguments.ShocksModel`).
The operator `shocksOpT` and the bounds `ShocksBounds` are from
`FixedPointArguments.ShocksContraction`; Schauder's theorem is `schauder_closed`, Brouwer's
`theorem_17_3`.

* `shocksWAvg φ a b`: the `θ`-weighted average of `φ` over `[a, b]` (`φ(a)` if `a = b`), with
  `shocksWAvg_extend_right`, `shocksWAvg_extend_left`, `abs_sub_shocksWAvg_le`, and the direct
  Lipschitz bound `shocksWAvg_lipschitz`: if `φ` is `B`-Lipschitz on `[c, d]`, `0 < c`, then
  `|wavg(a, b) − wavg(a′, b′)| ≤ (d/c) B (|a − a′| + |b − b′|)`.
* `shocksA_lipschitz`, `shocksB_lipschitz`, `shocksA_shocksB_mem`: `a`, `b` are Lipschitz on `Z`
  and `θ̲ ≤ a ≤ b ≤ θ̄`.
* **(6a)–(6b), corrected** (`shocksUnif_integral_condLaw`, p. 537): under Assumptions 17.5–17.6,
  `∫ k dG(·|z) = wavg(k; a(z), b(z))` for all `z ∈ Z` (degenerate at `z̲`, `z̄`).
* **Exercise 17.11** (p. 536): Steps 1–2 are `ShocksBounds.opT_mem`
  (`FixedPointArguments.ShocksContraction`), Step 3 is `ShocksBounds.ex_17_11_step3`; as the book
  says, they need neither Assumption 17.6 nor any property of `μ` beyond being a probability.
* **Exercise 17.13** (`ShocksBounds.ex_17_13`, p. 537), in Lipschitz form: all `φ_f`, `f ∈ F`,
  are `K`-Lipschitz on `Θ` with one `K` (the derivative form is in
  `FixedPointArguments.ShocksMonotone`).
* **Step 4** (`shocksUnif_opT_lipschitz`, pp. 537–539): every `Tf`, `f ∈ F`, is Lipschitz on `Z`
  with the common constant `(θ̄/θ̲) K (x̲ + x̄)/z̲²`, so `T(F)` is equicontinuous.
* **(7), corrected** (`eq7_corrected`, p. 537): on `Ẑ` (interior points off the kinks
  `x̲/z = θ̲`, `x̄/z = θ̄`), `W(z) = wavg(φ; a(z), b(z))` (`= Tf(z)` by (6a)) is differentiable with
  `W′ = [b b′(φ(b) − W) − a a′(φ(a) − W)]/((b² − a²)/2)`, for every continuous `φ` (in particular
  `φ_f`); from the abstract `shocksWAvg_hasDerivAt` and the one-sided pieces
  `shocksA_hasDerivAt`, `shocksB_hasDerivAt` (`a′ = −x̲/z²` or `0`, `b′ = −x̄/z²` or `0`).
* **Finite `Z`** (`shocks_finite_Z`, p. 539): with finitely many values of `z`, for any `μ` and
  any conditional laws, `T` has a fixed point bounded away from zero, by Brouwer
  (`theorem_17_3`) using Steps 1–3 only.
* **Proposition 7** (`proposition_7`, p. 536), corrected: a continuous fixed point bounded away
  from `0`, for every law `μ` of `(θ′, z′)`; `proposition_7_islands`: under the book's
  Assumption 17.1 (`shocks_assumption17_1VR_of_V`) with `μ` the joint law.

**Correction (Exercise 17.12 and (6a), (7)).** The conditional law in (6a) is the `θ`-weighted
one; (6a) becomes `Tf(z) = ∫_a^b φ_f(θ) θ dθ / ((b² − a²)/2)` (`shocksUnif_integral_condLaw`) and
(7) becomes `(Tf)' = [b b′(φ_f(b) − Tf) − a a′(φ_f(a) − Tf)]/((b² − a²)/2)` on `Ẑ`
(`eq7_corrected`; the proof of Proposition 7 here does not need it). Proposition 7 still holds.

**Correction (Step 4: the L'Hôpital argument).** The book solves `L = φ_f′(θ̄) a′(z̲) − L` for
`L = lim (Tf)′`, presupposing that the limit exists, and a limit value is not a uniform bound.
We use instead the direct uniform estimate `shocksWAvg_lipschitz` (from
`|φ_f(θ) − Tf(z)| ≤ K (b − a)` and `∫_a^b θ dθ ≥ θ̲ (b − a)`), which also covers the kinks
`x̲/θ̲`, `x̄/θ̄` of `a`, `b` and needs no differentiability. Typos in Step 4 (high confidence, not
formalised): (7) holds on `Ẑ`, not on all of `Z`; "`z → x̲/z̄`" should be "`z → x̲/θ̄`";
"the numerator in (8)" should be "(7)"; the left-derivative formula at `x̲/θ̲` lost a minus sign.

**Correction (Proposition 7, "a fixed point in `C(Z)`").** `T0 = 0`
(`proposition_6_zero_fixedPoint`), so the statement as written is trivial; the substantive
claim, proved here, is a fixed point bounded away from zero.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology BoundedContinuousFunction

/-! ### `θ`-weighted averages over intervals -/

/-- The `θ`-weighted average `∫_a^b θ φ(θ) dθ / ∫_a^b θ dθ` of `φ` over `[a, b]` (`φ(a)` if
`a = b`): the expectation of `φ(θ)` when `θ` has density `2θ/(b² − a²)` on `[a, b]`. -/
noncomputable def shocksWAvg (φ : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a < b then (∫ θ in a..b, θ * φ θ) / ∫ θ in a..b, θ else φ a

variable {φ : ℝ → ℝ} {a b c d : ℝ}

/-- The weighted average on a nondegenerate interval. -/
theorem shocksWAvg_of_lt (h : a < b) :
    shocksWAvg φ a b = (∫ θ in a..b, θ * φ θ) / ∫ θ in a..b, θ := by
  simp [shocksWAvg, h]

/-- `∫_a^b θ dθ = (b² − a²)/2`. -/
theorem shocks_integral_id (a b : ℝ) : ∫ θ in a..b, θ = (b ^ 2 - a ^ 2) / 2 := integral_id

/-- `∫_a^b θ dθ ≥ a (b − a)` for `0 ≤ a ≤ b`. -/
theorem shocks_integral_id_ge (_ha : 0 ≤ a) (hab : a ≤ b) : a * (b - a) ≤ ∫ θ in a..b, θ := by
  rw [shocks_integral_id]; nlinarith

/-- `∫_a^b θ φ(θ) dθ = wavg · ∫_a^b θ dθ` for `0 < a ≤ b`. -/
theorem shocksWAvg_mul_eq (ha : 0 < a) (hab : a ≤ b) :
    ∫ θ in a..b, θ * φ θ = shocksWAvg φ a b * ∫ θ in a..b, θ := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  · have hW : 0 < ∫ θ in a..b, θ := by
      rw [shocks_integral_id]; nlinarith
    rw [shocksWAvg_of_lt h, div_mul_cancel₀ _ hW.ne']

/-- Interval integrability of `θ ↦ θ (φ(θ) − M)` for `φ` continuous on `[c, d] ⊇ [a, b]`. -/
theorem shocks_intervalIntegrable (hφ : ContinuousOn φ (Icc c d)) (hca : c ≤ a) (hab : a ≤ b)
    (hbd : b ≤ d) (M : ℝ) : IntervalIntegrable (fun θ => θ * (φ θ - M)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact continuousOn_id.mul ((hφ.mono (Icc_subset_Icc hca hbd)).sub continuousOn_const)

/-- If `φ` is within `K` of `φ(t)` on `[a, b]`, then so is its weighted average. -/
theorem abs_sub_shocksWAvg_le (hφ : ContinuousOn φ (Icc a b)) (ha : 0 < a) (hab : a ≤ b)
    {t K : ℝ} (hK : ∀ θ ∈ Icc a b, |φ t - φ θ| ≤ K) : |φ t - shocksWAvg φ a b| ≤ K := by
  rcases hab.eq_or_lt with h | h
  · subst h
    simpa [shocksWAvg] using hK a ⟨le_rfl, le_rfl⟩
  have hW : 0 < ∫ θ in a..b, θ := by rw [shocks_integral_id]; nlinarith
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a ⟨le_rfl, h.le⟩)
  have i1 : IntervalIntegrable (fun θ => φ t * θ) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ => θ * φ θ) volume a b :=
    (continuousOn_id.mul hφ).intervalIntegrable_of_Icc h.le
  have e : φ t - shocksWAvg φ a b =
      (∫ θ in a..b, θ * (φ t - φ θ)) / ∫ θ in a..b, θ := by
    have h1 : ∫ θ in a..b, θ * (φ t - φ θ) = φ t * (∫ θ in a..b, θ) - ∫ θ in a..b, θ * φ θ := by
      have : (fun θ => θ * (φ t - φ θ)) = fun θ => φ t * θ - θ * φ θ := by ext θ; ring
      rw [this, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul]
    rw [h1, shocksWAvg_mul_eq ha h.le]
    field_simp
  rw [e, abs_div, abs_of_pos hW, div_le_iff₀ hW]
  have := intervalIntegral.norm_integral_le_of_norm_le h.le (g := fun θ => θ * K)
    (f := fun θ => θ * (φ t - φ θ)) (μ := volume)
    (ae_of_all _ fun θ hθ => by
      have h1 := hK θ (Ioc_subset_Icc_self hθ)
      have h2 : 0 < θ := ha.trans hθ.1
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos h2]
      nlinarith [abs_nonneg (φ t - φ θ)])
    ((continuous_id.mul continuous_const).intervalIntegrable _ _)
  rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const] at this
  linarith

/-- Extending `[a, b]` to the right:
`wavg(a, b') − wavg(a, b) = ∫_b^{b'} θ(φ − wavg(a, b)) / W(a, b')`. -/
theorem shocksWAvg_extend_right (hφ : ContinuousOn φ (Icc a d)) (ha : 0 < a) (hab : a ≤ b)
    {b' : ℝ} (hbb : b ≤ b') (hbd : b' ≤ d) (hab' : a < b') :
    shocksWAvg φ a b' - shocksWAvg φ a b =
      (∫ θ in b..b', θ * (φ θ - shocksWAvg φ a b)) / ∫ θ in a..b', θ := by
  set M := shocksWAvg φ a b
  have hW : 0 < ∫ θ in a..b', θ := by rw [shocks_integral_id]; nlinarith
  have i1 : IntervalIntegrable (fun θ => θ * φ θ) volume a b :=
    (continuousOn_id.mul (hφ.mono (Icc_subset_Icc le_rfl
      (hbb.trans hbd)))).intervalIntegrable_of_Icc hab
  have i2 : IntervalIntegrable (fun θ => θ * φ θ) volume b b' :=
    (continuousOn_id.mul (hφ.mono (Icc_subset_Icc hab hbd))).intervalIntegrable_of_Icc hbb
  have eS := intervalIntegral.integral_add_adjacent_intervals i1 i2
  have eW := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegral.intervalIntegrable_id (a := a) (b := b) (μ := volume))
    (intervalIntegral.intervalIntegrable_id (a := b) (b := b') (μ := volume))
  have e2 : ∫ θ in b..b', θ * (φ θ - M) = (∫ θ in b..b', θ * φ θ) - M * ∫ θ in b..b', θ := by
    have : (fun θ => θ * (φ θ - M)) = fun θ => θ * φ θ - M * θ := by ext θ; ring
    rw [this, intervalIntegral.integral_sub i2 (intervalIntegral.intervalIntegrable_id.const_mul _),
      intervalIntegral.integral_const_mul]
  have hS := shocksWAvg_mul_eq (φ := φ) ha hab
  rw [shocksWAvg_of_lt hab', e2, eq_div_iff hW.ne', sub_mul, div_mul_cancel₀ _ hW.ne', ← eS,
    ← eW, hS]
  ring

/-- Extending `[a, b]` to the left:
`wavg(A, b) − wavg(a, b) = ∫_A^a θ(φ − wavg(a, b)) / W(A, b)`. -/
theorem shocksWAvg_extend_left (hφ : ContinuousOn φ (Icc c b)) {A : ℝ} (hA : 0 < A) (hcA : c ≤ A)
    (hAa : A ≤ a) (hab : a ≤ b) (hAb : A < b) :
    shocksWAvg φ A b - shocksWAvg φ a b =
      (∫ θ in A..a, θ * (φ θ - shocksWAvg φ a b)) / ∫ θ in A..b, θ := by
  set M := shocksWAvg φ a b
  have ha : 0 < a := hA.trans_le hAa
  have hW : 0 < ∫ θ in A..b, θ := by rw [shocks_integral_id]; nlinarith
  have i1 : IntervalIntegrable (fun θ => θ * φ θ) volume A a :=
    (continuousOn_id.mul (hφ.mono (Icc_subset_Icc hcA (hab)))).intervalIntegrable_of_Icc hAa
  have i2 : IntervalIntegrable (fun θ => θ * φ θ) volume a b :=
    (continuousOn_id.mul (hφ.mono (Icc_subset_Icc (hcA.trans hAa)
      le_rfl))).intervalIntegrable_of_Icc hab
  have eS := intervalIntegral.integral_add_adjacent_intervals i1 i2
  have eW := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegral.intervalIntegrable_id (a := A) (b := a) (μ := volume))
    (intervalIntegral.intervalIntegrable_id (a := a) (b := b) (μ := volume))
  have e2 : ∫ θ in A..a, θ * (φ θ - M) = (∫ θ in A..a, θ * φ θ) - M * ∫ θ in A..a, θ := by
    have : (fun θ => θ * (φ θ - M)) = fun θ => θ * φ θ - M * θ := by ext θ; ring
    rw [this, intervalIntegral.integral_sub i1 (intervalIntegral.intervalIntegrable_id.const_mul _),
      intervalIntegral.integral_const_mul]
  have hS := shocksWAvg_mul_eq (φ := φ) ha hab
  rw [shocksWAvg_of_lt hAb, e2, eq_div_iff hW.ne', sub_mul, div_mul_cancel₀ _ hW.ne', ← eS,
    ← eW, hS]
  ring

/-- The algebra of the extension bound: if `|N| ≤ d K |e|`, `W ≥ c w > 0` and `K = B w`, then
`|N/W| ≤ (d/c) B |e|`. -/
theorem shocks_abs_div_le {N W K e w B : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hw : 0 < w)
    (hB : 0 ≤ B) (hK : K = B * w) (hN : |N| ≤ d * K * |e|) (hW : c * w ≤ W) :
    |N / W| ≤ d / c * B * |e| := by
  have hW0 : 0 < W := (mul_pos hc hw).trans_le hW
  rw [abs_div, abs_of_pos hW0, div_le_iff₀ hW0]
  calc |N| ≤ d * K * |e| := hN
    _ = d / c * B * |e| * (c * w) := by rw [hK]; field_simp
    _ ≤ d / c * B * |e| * W := mul_le_mul_of_nonneg_left hW (by positivity)

/-- **Lipschitz in the right endpoint.** If `φ` is `B`-Lipschitz on `[c, d]`, `0 < c`, then for
`c ≤ a ≤ b ≤ b' ≤ d`: `|wavg(a, b') − wavg(a, b)| ≤ (d/c) B (b' − b)`. -/
theorem shocksWAvg_lip_right (hc : 0 < c) (hφc : ContinuousOn φ (Icc c d)) {B : ℝ}
    (hφ : ∀ s ∈ Icc c d, ∀ t ∈ Icc c d, |φ s - φ t| ≤ B * |s - t|) (hca : c ≤ a) (hab : a ≤ b)
    {b' : ℝ} (hbb : b ≤ b') (hbd : b' ≤ d) :
    |shocksWAvg φ a b' - shocksWAvg φ a b| ≤ d / c * B * (b' - b) := by
  rcases (hab.trans hbb).eq_or_lt with h | hab'
  · have h1 : b = b' := le_antisymm hbb (h ▸ hab)
    subst h1; simp
  have ha : 0 < a := hc.trans_le hca
  have hd : 0 ≤ d := ha.le.trans (hab.trans (hbb.trans hbd))
  have hB : 0 ≤ B := by
    have := hφ b' ⟨hca.trans (hab.trans hbb), hbd⟩ a ⟨hca, (hab.trans hbb).trans hbd⟩
    rw [abs_of_pos (sub_pos.2 hab')] at this
    nlinarith [abs_nonneg (φ b' - φ a)]
  rw [shocksWAvg_extend_right (hφc.mono (Icc_subset_Icc hca le_rfl)) ha hab hbb hbd hab']
  have hdev : ∀ θ ∈ Icc b b', |φ θ - shocksWAvg φ a b| ≤ B * (b' - a) := fun θ hθ =>
    abs_sub_shocksWAvg_le (hφc.mono (Icc_subset_Icc hca (hbb.trans hbd))) ha hab fun s hs => by
      refine (hφ θ ⟨hca.trans (hab.trans hθ.1), hθ.2.trans hbd⟩ s
        ⟨hca.trans hs.1, hs.2.trans (hbb.trans hbd)⟩).trans (mul_le_mul_of_nonneg_left ?_ hB)
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2, hθ.1, hθ.2]
  have hN : |∫ θ in b..b', θ * (φ θ - shocksWAvg φ a b)| ≤ d * (B * (b' - a)) * |b' - b| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
    rw [uIoc_of_le hbb] at hθ
    have h0 : 0 < θ := ha.trans_le (hab.trans hθ.1.le)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos h0]
    exact mul_le_mul (hθ.2.trans hbd) (hdev θ (Ioc_subset_Icc_self hθ)) (abs_nonneg _) hd
  have := shocks_abs_div_le hc hd (sub_pos.2 hab') hB rfl hN
    ((mul_le_mul_of_nonneg_right hca (sub_pos.2 hab').le).trans
      (shocks_integral_id_ge ha.le hab'.le))
  rwa [abs_of_nonneg (sub_nonneg.2 hbb)] at this

/-- **Lipschitz in the left endpoint.** If `φ` is `B`-Lipschitz on `[c, d]`, `0 < c`, then for
`c ≤ A ≤ a ≤ b ≤ d`: `|wavg(A, b) − wavg(a, b)| ≤ (d/c) B (a − A)`. -/
theorem shocksWAvg_lip_left (hc : 0 < c) (hφc : ContinuousOn φ (Icc c d)) {B : ℝ}
    (hφ : ∀ s ∈ Icc c d, ∀ t ∈ Icc c d, |φ s - φ t| ≤ B * |s - t|) {A : ℝ} (hcA : c ≤ A)
    (hAa : A ≤ a) (hab : a ≤ b) (hbd : b ≤ d) :
    |shocksWAvg φ A b - shocksWAvg φ a b| ≤ d / c * B * (a - A) := by
  rcases (hAa.trans hab).eq_or_lt with h | hAb
  · have h1 : A = a := le_antisymm hAa (h ▸ hab)
    subst h1; simp
  have hA : 0 < A := hc.trans_le hcA
  have ha : 0 < a := hA.trans_le hAa
  have hd : 0 ≤ d := ha.le.trans (hab.trans hbd)
  have hB : 0 ≤ B := by
    have := hφ b ⟨hcA.trans (hAa.trans hab), hbd⟩ A ⟨hcA, (hAa.trans hab).trans hbd⟩
    rw [abs_of_pos (sub_pos.2 hAb)] at this
    nlinarith [abs_nonneg (φ b - φ A)]
  rw [shocksWAvg_extend_left (hφc.mono (Icc_subset_Icc le_rfl hbd)) hA hcA hAa hab hAb]
  have hdev : ∀ θ ∈ Icc A a, |φ θ - shocksWAvg φ a b| ≤ B * (b - A) := fun θ hθ =>
    abs_sub_shocksWAvg_le (hφc.mono (Icc_subset_Icc (hcA.trans hAa) hbd)) ha hab fun s hs => by
      refine (hφ θ ⟨hcA.trans hθ.1, hθ.2.trans (hab.trans hbd)⟩ s
        ⟨hcA.trans (hAa.trans hs.1), hs.2.trans hbd⟩).trans (mul_le_mul_of_nonneg_left ?_ hB)
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2, hθ.1, hθ.2]
  have hN : |∫ θ in A..a, θ * (φ θ - shocksWAvg φ a b)| ≤ d * (B * (b - A)) * |a - A| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
    rw [uIoc_of_le hAa] at hθ
    have h0 : 0 < θ := hA.trans hθ.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos h0]
    exact mul_le_mul (hθ.2.trans (hab.trans hbd)) (hdev θ (Ioc_subset_Icc_self hθ)) (abs_nonneg _)
      hd
  have := shocks_abs_div_le hc hd (sub_pos.2 hAb) hB rfl hN
    ((mul_le_mul_of_nonneg_right hcA (sub_pos.2 hAb).le).trans
      (shocks_integral_id_ge hA.le hAb.le))
  rwa [abs_of_nonneg (sub_nonneg.2 hAa)] at this

/-- **The weighted average is Lipschitz in both endpoints.** If `φ` is `B`-Lipschitz on `[c, d]`,
`0 < c`, then `|wavg(a, b) − wavg(a', b')| ≤ (d/c) B (|a − a'| + |b − b'|)` for subintervals
`[a, b]`, `[a', b']` of `[c, d]`. (This is the direct uniform bound replacing the book's
L'Hôpital argument in Step 4 of Proposition 7.) -/
theorem shocksWAvg_lipschitz (hc : 0 < c) (hφc : ContinuousOn φ (Icc c d)) {B : ℝ}
    (hφ : ∀ s ∈ Icc c d, ∀ t ∈ Icc c d, |φ s - φ t| ≤ B * |s - t|) {a' b' : ℝ}
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) (hca' : c ≤ a') (hab' : a' ≤ b') (hbd' : b' ≤ d) :
    |shocksWAvg φ a b - shocksWAvg φ a' b'| ≤ d / c * B * (|a - a'| + |b - b'|) := by
  set A := min a a'
  set E := max b b'
  have hcA : c ≤ A := le_min hca hca'
  have hEd : E ≤ d := max_le hbd hbd'
  have h1 := shocksWAvg_lip_right hc hφc hφ hca hab (le_max_left b b') hEd
  have h2 := shocksWAvg_lip_left hc hφc hφ hcA (min_le_left a a') (hab.trans (le_max_left b b'))
    hEd
  have h3 := shocksWAvg_lip_right hc hφc hφ hca' hab' (le_max_right b b') hEd
  have h4 := shocksWAvg_lip_left hc hφc hφ hcA (min_le_right a a')
    (hab'.trans (le_max_right b b')) hEd
  have e1 : (E - b) + (E - b') = |b - b'| := by
    simp only [E]; rcases le_total b b' with h | h
    · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.2 h)]; ring
    · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.2 h)]; ring
  have e2 : (a - A) + (a' - A) = |a - a'| := by
    simp only [A]; rcases le_total a a' with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring
  rw [← e1, ← e2]
  set K := d / c * B
  have k1 := abs_le.1 h1
  have k2 := abs_le.1 h2
  have k3 := abs_le.1 h3
  have k4 := abs_le.1 h4
  rw [abs_le]
  constructor <;> nlinarith [k1.1, k1.2, k2.1, k2.2, k3.1, k3.2, k4.1, k4.2]

/-! ### The uniform model: (6a)–(6b) with the correct weights -/

variable {xlo xhi θlo θhi : ℝ}

/-- `a(z)` is Lipschitz on `z ≥ z₀ > 0` with constant `x̲/z₀²`. -/
theorem shocksA_lipschitz {z₀ z z' : ℝ} (hx : 0 ≤ xlo) (hz₀ : 0 < z₀) (hz : z₀ ≤ z)
    (hz' : z₀ ≤ z') : |shocksA xlo θlo z - shocksA xlo θlo z'| ≤ xlo / z₀ ^ 2 * |z - z'| := by
  have h0 : 0 < z := hz₀.trans_le hz
  have h0' : 0 < z' := hz₀.trans_le hz'
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [div_sub_div _ _ h0.ne' h0'.ne', abs_div, abs_of_pos (mul_pos h0 h0'),
    show xlo * z' - z * xlo = xlo * (z' - z) by ring, abs_mul, abs_of_nonneg hx, abs_sub_comm,
    div_le_iff₀ (mul_pos h0 h0')]
  have h1 : z₀ ^ 2 ≤ z * z' := by nlinarith
  calc xlo * |z - z'| = xlo / z₀ ^ 2 * |z - z'| * z₀ ^ 2 := by field_simp
    _ ≤ xlo / z₀ ^ 2 * |z - z'| * (z * z') :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

/-- `b(z)` is Lipschitz on `z ≥ z₀ > 0` with constant `x̄/z₀²`. -/
theorem shocksB_lipschitz {z₀ z z' : ℝ} (hx : 0 ≤ xhi) (hz₀ : 0 < z₀) (hz : z₀ ≤ z)
    (hz' : z₀ ≤ z') : |shocksB xhi θhi z - shocksB xhi θhi z'| ≤ xhi / z₀ ^ 2 * |z - z'| := by
  have h0 : 0 < z := hz₀.trans_le hz
  have h0' : 0 < z' := hz₀.trans_le hz'
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
  rw [div_sub_div _ _ h0.ne' h0'.ne', abs_div, abs_of_pos (mul_pos h0 h0'),
    show xhi * z' - z * xhi = xhi * (z' - z) by ring, abs_mul, abs_of_nonneg hx, abs_sub_comm,
    div_le_iff₀ (mul_pos h0 h0')]
  have h1 : z₀ ^ 2 ≤ z * z' := by nlinarith
  calc xhi * |z - z'| = xhi / z₀ ^ 2 * |z - z'| * z₀ ^ 2 := by field_simp
    _ ≤ xhi / z₀ ^ 2 * |z - z'| * (z * z') :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

/-- On `Z`, `θ̲ ≤ a(z) ≤ b(z) ≤ θ̄`. -/
theorem shocksA_shocksB_mem (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    {z : ℝ} (hz : z ∈ Icc (xlo / θhi) (xhi / θlo)) :
    θlo ≤ shocksA xlo θlo z ∧ shocksA xlo θlo z ≤ shocksB xhi θhi z ∧
      shocksB xhi θhi z ≤ θhi := by
  have hθhi : 0 < θhi := hθ0.trans hθ
  have hz0 : 0 < z := (div_pos hx0 hθhi).trans_le hz.1
  refine ⟨le_max_right _ _, max_le (le_min (div_le_div_of_nonneg_right hx.le hz0.le) ?_)
    (le_min ?_ hθ.le), min_le_right _ _⟩
  · rw [div_le_iff₀ hz0]; have := (div_le_iff₀ hθhi).1 hz.1; linarith
  · rw [le_div_iff₀ hz0]; have := (le_div_iff₀ hθ0).1 hz.2; linarith

/-- **(6a)–(6b), corrected** (p. 537). Under Assumptions 17.5 and 17.6, for every `z ∈ Z` and
every `k`, `∫ k dG(·|z)` is the `θ`-weighted average of `k` over `[a(z), b(z)]` (at `z̲`, `z̄`
the interval degenerates to `{θ̄}`, `{θ̲}`, which is (6b)). The book's (6a) has the unweighted
average `(b − a)⁻¹ ∫_a^b`, which is wrong (`ex_17_12_counterexample`). -/
theorem shocksUnif_integral_condLaw (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo)
    (hθ : θlo < θhi) (hθ2 : θhi < 2) {z : ℝ} (hz : z ∈ Icc (xlo / θhi) (xhi / θlo))
    (k : ℝ → ℝ) :
    ∫ θ, k θ ∂shocksCondLaw xlo xhi θlo θhi (shocksUnif xlo xhi) (shocksUnif θlo θhi) z =
      shocksWAvg k (shocksA xlo θlo z) (shocksB xhi θhi z) := by
  have hA := shocksUnif_assumption17_5 hx0 hx hθ0 hθ hθ2
  have hθhi : 0 < θhi := hθ0.trans hθ
  have hxhi : 0 < xhi := hx0.trans hx
  by_cases hzZ : xlo / θhi < z ∧ z < xhi / θlo
  · have hπ := hA.pi_pos (fun x hx' => by rw [shocksUnif, indicator_of_mem hx']; simp [hx])
      (fun θ hθ' => by rw [shocksUnif, indicator_of_mem hθ']; simp [hθ]) hzZ
    obtain ⟨-, hab⟩ := shocksA_lt_shocksB hx0 hx hθ0 hθ hzZ
    have ha0 : 0 < shocksA xlo θlo z := hθ0.trans_le (le_max_right _ _)
    rw [hA.integral_condLaw hzZ hπ]
    simp_rw [ex_17_12 hx0 hx hθ0 hθ hzZ]
    have e : (fun θ => k θ * (Icc (shocksA xlo θlo z) (shocksB xhi θhi z)).indicator
        (fun θ => 2 * θ / (shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2)) θ) =
        (Icc (shocksA xlo θlo z) (shocksB xhi θhi z)).indicator
        (fun θ => 2 / (shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2) * (θ * k θ)) := by
      ext θ
      by_cases h : θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z)
      · rw [indicator_of_mem h, indicator_of_mem h]; ring
      · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
    rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_const_mul,
      shocksWAvg_of_lt hab, shocks_integral_id]
    field_simp
  · rcases eq_or_lt_of_le hz.1 with h | h
    · subst h
      have h1 : shocksA xlo θlo (xlo / θhi) = θhi := by
        simp only [shocksA]; rw [div_div_cancel₀ hx0.ne']; exact max_eq_left hθ.le
      have h2 : shocksB xhi θhi (xlo / θhi) = θhi := by
        simp only [shocksB]; refine min_eq_right ?_
        rw [le_div_iff₀ (div_pos hx0 hθhi), mul_div_assoc', div_le_iff₀ hθhi]
        nlinarith
      simp only [shocksCondLaw, lt_irrefl, false_and, ↓reduceIte, le_refl, integral_dirac, h1,
        h2, shocksWAvg]
    · have h3 : z = xhi / θlo := by
        by_contra h3
        exact hzZ ⟨h, lt_of_le_of_ne hz.2 h3⟩
      subst h3
      have hZ : xlo / θhi < xhi / θlo := h
      have h1 : shocksA xlo θlo (xhi / θlo) = θlo := by
        simp only [shocksA]; refine max_eq_right ?_
        rw [div_le_iff₀ (div_pos hxhi hθ0), mul_div_assoc', le_div_iff₀ hθ0]
        nlinarith
      have h2 : shocksB xhi θhi (xhi / θlo) = θlo := by
        simp only [shocksB]; rw [div_div_cancel₀ hxhi.ne']; exact min_eq_left hθ.le
      simp only [shocksCondLaw, lt_irrefl, and_false, ↓reduceIte, not_le.mpr hZ, integral_dirac,
        h1, h2, shocksWAvg]

/-! ### Exercises 17.11 and 17.13 -/

variable {Z : Type*} {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- The book's Assumption 17.1 for `V` implies the repaired one, so results proved under
`Assumption17_1VR` hold under Assumption 17.1 as stated. -/
theorem shocks_assumption17_1VR_of_V (hV : Assumption17_1V V V' V'') :
    Assumption17_1VR V V' V'' :=
  ⟨hV.V_nonneg, hV.V_continuousOn, fun _ hy => hV.V_hasDerivAt hy,
    fun y hy => (hV.V'_deriv y hy.le).hasDerivAt (Ici_mem_nhds hy),
    hV.V''_cont.mono Ioi_subset_Ici_self, hV.V_mono, hV.V_conc⟩

namespace ShocksBounds

variable {l₀ l : ℝ} (hS : ShocksBounds L θlo θhi l₀ H H' H'' V V' V'')
include hS

/-- `φ` is Lipschitz on `[(θ̲/θ̄) l, (θ̄/θ̲) L]` (mean value theorem; `φ' = V' + yV''` is
continuous on `ℝ₊₊`). -/
theorem exists_phi_lipschitz (hl : l ∈ Ioc 0 l₀) : ∃ M, 0 ≤ M ∧
    ∀ y ∈ Icc (θlo / θhi * l) (θhi / θlo * L), ∀ y' ∈ Icc (θlo / θhi * l) (θhi / θlo * L),
      |olgPhi V' y - olgPhi V' y'| ≤ M * |y - y'| := by
  obtain ⟨ha, -⟩ := hS.ratio_bounds
  have hpos : ∀ y ∈ Icc (θlo / θhi * l) (θhi / θlo * L), 0 < y := fun y hy =>
    (mul_pos ha hl.1).trans_le hy.1
  have hc : ContinuousOn (fun y => V' y + y * V'' y) (Icc (θlo / θhi * l) (θhi / θlo * L)) :=
    (hS.hV.V'_continuousOn.mono fun y hy => hpos y hy).add
      (continuousOn_id.mul (hS.hV.V''_cont.mono fun y hy => hpos y hy))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, fun y hy y' hy' => ?_⟩
  have := (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := olgPhi V') (f' := fun y => V' y + y * V'' y)
    (fun x hx => (hS.hV.phi_hasDerivAt (hpos x hx)).hasDerivWithinAt)
    (fun x hx => (hM x hx).trans (le_max_left M 0)) hy' hy
  simpa only [Real.norm_eq_abs] using this

/-- **Exercise 17.13** (p. 537), in Lipschitz form: there is `K` such that every `φ_f`,
`f ∈ F = {f : ζ(l) ≤ f}`, is `K`-Lipschitz on `Θ`, for every law `μ` of `(θ′, z′)`
(`K = M L θ̄/θ̲²`, `M` a bound for `|φ'|` on `[(θ̲/θ̄) l, (θ̄/θ̲) L]`; the manual's
`(θ̄/θ̲²) L max|φ'|`). -/
theorem ex_17_13 [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (hl : l ∈ Ioc 0 l₀) : ∃ K, 0 ≤ K ∧ ∀ (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
      (f : Z → ℝ), Continuous f → (∀ z, olgZeta H' l ≤ f z) →
      ∀ s ∈ Icc θlo θhi, ∀ t ∈ Icc θlo θhi,
        |shocksPhiF L H' V' θlo θhi μ f s - shocksPhiF L H' V' θlo θhi μ f t| ≤ K * |s - t| := by
  obtain ⟨ha, hab⟩ := hS.ratio_bounds
  obtain ⟨M, hM0, hM⟩ := hS.exists_phi_lipschitz hl
  obtain ⟨B, -, hB⟩ := hS.exists_integrand_le (Z := Z) hl
  have hl' : l ∈ Ioo 0 L := ⟨hl.1, hl.2.trans_lt hS.l₀_mem.2⟩
  have hθ0 := hS.θlo_pos
  have hθhi : 0 < θhi := hθ0.trans_le hS.θlo_le
  refine ⟨M * (L * θhi / θlo ^ 2), mul_nonneg hM0 (by have := hS.hH.L_pos; positivity),
    fun μ _ f hfc hfl s hs t ht => ?_⟩
  have hpt : ∀ ω : ℝ × Z, |shocksIntegrand L H' V' θlo θhi f s ω -
      shocksIntegrand L H' V' θlo θhi f t ω| ≤ M * (L * θhi / θlo ^ 2) * |s - t| := fun ω => by
    have hy0 : 0 ≤ f ω.2 := (hS.zeta_pos hl).le.trans (hfl ω.2)
    have hm := hS.hH.zetaInv_mem hy0
    set m := olgZetaInv L H' (f ω.2)
    have hlm : l ≤ m := by
      have := hS.hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 (hS.zeta_pos hl).le)
        (mem_Ici.2 hy0) (hfl ω.2)
      rwa [hS.hH.zetaInv_zeta (Ioo_subset_Ico_self hl')] at this
    have hmem : ∀ u, shocksRatio θlo θhi ω.1 u * m ∈ Icc (θlo / θhi * l) (θhi / θlo * L) :=
      fun u => by
        have hr := shocksRatio_mem hθ0 hS.θlo_le ω.1 u
        exact ⟨mul_le_mul hr.1 hlm hl.1.le (ha.le.trans hr.1),
          mul_le_mul hr.2 hm.2.le hm.1 (ha.le.trans hab)⟩
    refine (hM _ (hmem s) _ (hmem t)).trans ?_
    have hc := shocksClamp_mem hS.θlo_le ω.1
    have hs0 : 0 < s := hθ0.trans_le hs.1
    have ht0 : 0 < t := hθ0.trans_le ht.1
    have e : shocksRatio θlo θhi ω.1 s * m - shocksRatio θlo θhi ω.1 t * m =
        shocksClamp θlo θhi ω.1 * m * (t - s) / (s * t) := by
      simp only [shocksRatio, shocksClamp_of_mem hs, shocksClamp_of_mem ht]
      field_simp
    suffices hd : |shocksRatio θlo θhi ω.1 s * m - shocksRatio θlo θhi ω.1 t * m| ≤
        L * θhi / θlo ^ 2 * |s - t| by
      calc M * |shocksRatio θlo θhi ω.1 s * m - shocksRatio θlo θhi ω.1 t * m|
          ≤ M * (L * θhi / θlo ^ 2 * |s - t|) := mul_le_mul_of_nonneg_left hd hM0
        _ = M * (L * θhi / θlo ^ 2) * |s - t| := by ring
    rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hs0 ht0), abs_of_nonneg (mul_nonneg
      (hθ0.le.trans hc.1) hm.1), abs_sub_comm t s]
    rw [div_le_iff₀ (mul_pos hs0 ht0)]
    have h1 : θlo ^ 2 ≤ s * t := by nlinarith [hs.1, ht.1]
    have h2 : shocksClamp θlo θhi ω.1 * m ≤ θhi * L :=
      mul_le_mul hc.2 hm.2.le hm.1 hθhi.le
    calc shocksClamp θlo θhi ω.1 * m * |s - t| ≤ θhi * L * |s - t| :=
          mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      _ = L * θhi / θlo ^ 2 * |s - t| * θlo ^ 2 := by field_simp
      _ ≤ L * θhi / θlo ^ 2 * |s - t| * (s * t) :=
          mul_le_mul_of_nonneg_left h1 (by have := hS.hH.L_pos; positivity)
  simp only [shocksPhiF]
  rw [← integral_sub (hS.integrable_integrand hl hB hfc hfl μ s)
    (hS.integrable_integrand hl hB hfc hfl μ t), ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := M * (L * θhi / θlo ^ 2) * |s - t|)
    (f := fun ω => shocksIntegrand L H' V' θlo θhi f s ω - shocksIntegrand L H' V' θlo θhi f t ω)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hpt ω)
  simpa using this

/-- **Exercise 17.11, Step 3** (p. 536): `T` is uniformly continuous on
`F = {f ∈ C(Z) : ζ(l) ≤ f ≤ B}`, uniformly over the laws `μ`, `ν` (uniform continuity of
`(r, y) ↦ φ(r ζ⁻¹(y))` on the compact `[θ̲/θ̄, θ̄/θ̲] × [ζ(l), B]`, as in Exercise 17.6). -/
theorem ex_17_11_step3 [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (hl : l ∈ Ioc 0 l₀) {B : ℝ} (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) :
    ∀ ε > 0, ∃ δ > 0, ∀ f g : Z → ℝ, Continuous f → Continuous g →
      (∀ z, olgZeta H' l ≤ f z ∧ f z ≤ B) → (∀ z, olgZeta H' l ≤ g z ∧ g z ≤ B) →
      (∀ z, |f z - g z| < δ) → ∀ (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
        (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)] (z : Z),
        |shocksOpT L H' V' θlo θhi μ ν f z - shocksOpT L H' V' θlo θhi μ ν g z| ≤ ε := by
  intro ε hε
  obtain ⟨ha, hab⟩ := hS.ratio_bounds
  have hzl := hS.zeta_pos hl
  set K : Set (ℝ × ℝ) := Icc (θlo / θhi) (θhi / θlo) ×ˢ Icc (olgZeta H' l) B
  have hcont : ContinuousOn (fun p : ℝ × ℝ => olgPhi V' (p.1 * olgZetaInv L H' p.2)) K := by
    refine hS.hV.phi_continuousOn.comp (continuousOn_fst.mul
      (hS.hH.zetaInv_continuousOn.comp continuousOn_snd fun p hp => mem_Ici.2
        (hzl.le.trans hp.2.1))) fun p hp => ?_
    exact mul_pos (ha.trans_le hp.1.1) (hS.hH.zetaInv_pos (hzl.trans_le hp.2.1))
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨δ, hδ, fun f g hfc hgc hf hg hfg μ _ ν _ z => ?_⟩
  have hfl : ∀ z, olgZeta H' l ≤ f z := fun z => (hf z).1
  have hgl : ∀ z, olgZeta H' l ≤ g z := fun z => (hg z).1
  have hpt : ∀ θt (ω : ℝ × Z), |shocksIntegrand L H' V' θlo θhi f θt ω -
      shocksIntegrand L H' V' θlo θhi g θt ω| ≤ ε := fun θt ω => by
    have hr := shocksRatio_mem hS.θlo_pos hS.θlo_le ω.1 θt
    have := hu (shocksRatio θlo θhi ω.1 θt, f ω.2) ⟨hr, hf ω.2⟩
      (shocksRatio θlo θhi ω.1 θt, g ω.2) ⟨hr, hg ω.2⟩ (by
        rw [Prod.dist_eq, dist_self, Real.dist_eq]
        exact max_lt hδ (hfg ω.2))
    rw [Real.dist_eq] at this
    exact this.le
  have hφ : ∀ θt, |shocksPhiF L H' V' θlo θhi μ f θt - shocksPhiF L H' V' θlo θhi μ g θt| ≤ ε :=
    fun θt => by
      simp only [shocksPhiF]
      rw [← integral_sub (hS.integrable_integrand hl hB hfc hfl μ θt)
        (hS.integrable_integrand hl hB hgc hgl μ θt), ← Real.norm_eq_abs]
      have := norm_integral_le_of_norm_le_const (μ := μ) (C := ε)
        (f := fun ω => shocksIntegrand L H' V' θlo θhi f θt ω -
          shocksIntegrand L H' V' θlo θhi g θt ω)
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hpt θt ω)
      simpa using this
  have i1 : Integrable (shocksPhiF L H' V' θlo θhi μ f) (ν z) :=
    (hS.phiFBCF hl hB hfc hfl μ).integrable (ν z)
  have i2 : Integrable (shocksPhiF L H' V' θlo θhi μ g) (ν z) :=
    (hS.phiFBCF hl hB hgc hgl μ).integrable (ν z)
  simp only [shocksOpT]
  rw [← integral_sub i1 i2, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := ν z) (C := ε)
    (f := fun θt => shocksPhiF L H' V' θlo θhi μ f θt - shocksPhiF L H' V' θlo θhi μ g θt)
    (ae_of_all _ fun θt => by rw [Real.norm_eq_abs]; exact hφ θt)
  simpa using this

end ShocksBounds

/-! ### Proposition 7 by Schauder's theorem -/

/-- **Step 4 of Proposition 7, with the correct weights** (pp. 537–539). Under Assumptions 17.5
and 17.6, if every `φ_f` is `K`-Lipschitz on `Θ` (Exercise 17.13), then every `Tf` is
Lipschitz on `Z` with the common constant `(θ̄/θ̲) K (x̲ + x̄)/z̲²`. This replaces the book's
piecewise derivative bound and its circular L'Hôpital step at `z̲`, `z̄` by the direct estimate
`shocksWAvg_lipschitz` (valid across the kinks of `a`, `b` and at the endpoints). -/
theorem shocksUnif_opT_lipschitz (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo)
    (hθ : θlo < θhi) (hθ2 : θhi < 2) (μ : Measure (ℝ × Icc (xlo / θhi) (xhi / θlo)))
    (f : Icc (xlo / θhi) (xhi / θlo) → ℝ) {K : ℝ}
    (hφc : ContinuousOn (shocksPhiF L H' V' θlo θhi μ f) (Icc θlo θhi))
    (hφ : ∀ s ∈ Icc θlo θhi, ∀ t ∈ Icc θlo θhi,
      |shocksPhiF L H' V' θlo θhi μ f s - shocksPhiF L H' V' θlo θhi μ f t| ≤ K * |s - t|)
    (z z' : Icc (xlo / θhi) (xhi / θlo)) :
    |shocksOpT L H' V' θlo θhi μ (fun z => shocksCondLaw xlo xhi θlo θhi (shocksUnif xlo xhi)
        (shocksUnif θlo θhi) z.1) f z -
      shocksOpT L H' V' θlo θhi μ (fun z => shocksCondLaw xlo xhi θlo θhi (shocksUnif xlo xhi)
        (shocksUnif θlo θhi) z.1) f z'| ≤
      θhi / θlo * K * ((xlo + xhi) / (xlo / θhi) ^ 2) * dist z z' := by
  have hθhi : 0 < θhi := hθ0.trans hθ
  have hzlo : 0 < xlo / θhi := div_pos hx0 hθhi
  have hK : 0 ≤ K := by
    have := hφ θhi ⟨hθ.le, le_rfl⟩ θlo ⟨le_rfl, hθ.le⟩
    rw [abs_of_pos (sub_pos.2 hθ)] at this
    nlinarith [abs_nonneg (shocksPhiF L H' V' θlo θhi μ f θhi -
      shocksPhiF L H' V' θlo θhi μ f θlo)]
  simp only [shocksOpT]
  rw [shocksUnif_integral_condLaw hx0 hx hθ0 hθ hθ2 z.2,
    shocksUnif_integral_condLaw hx0 hx hθ0 hθ hθ2 z'.2]
  obtain ⟨h1, h2, h3⟩ := shocksA_shocksB_mem hx0 hx hθ0 hθ z.2
  obtain ⟨h1', h2', h3'⟩ := shocksA_shocksB_mem hx0 hx hθ0 hθ z'.2
  refine (shocksWAvg_lipschitz hθ0 hφc hφ h1 h2 h3 h1' h2' h3').trans ?_
  have ha := shocksA_lipschitz (θlo := θlo) hx0.le hzlo z.2.1 z'.2.1
  have hb := shocksB_lipschitz (θhi := θhi) (hx0.trans hx).le hzlo z.2.1 z'.2.1
  rw [Subtype.dist_eq, Real.dist_eq]
  have hC : 0 ≤ θhi / θlo * K := by positivity
  calc θhi / θlo * K * (|shocksA xlo θlo z - shocksA xlo θlo z'| +
        |shocksB xhi θhi z - shocksB xhi θhi z'|)
      ≤ θhi / θlo * K * (xlo / (xlo / θhi) ^ 2 * |z.1 - z'.1| +
        xhi / (xlo / θhi) ^ 2 * |z.1 - z'.1|) := mul_le_mul_of_nonneg_left (add_le_add ha hb) hC
    _ = θhi / θlo * K * ((xlo + xhi) / (xlo / θhi) ^ 2) * |z.1 - z'.1| := by ring

/-- **Proposition 7** (p. 536), corrected. Let `H` satisfy Assumption 17.1 and `V` the (repaired,
weaker) utility part of Assumption 17.1, `Ψ`, `G` uniform on `X = [x̲, x̄]`, `Θ = [θ̲, θ̄]`
(Assumptions 17.5, 17.6), `G(·|z)` the correct conditional law (density `2θ/(b² − a²)` on
`[a(z), b(z)]`, Exercise 17.12 corrected) and `μ` any probability law of `(θ′, z′)` (e.g. their
joint law, `shocksJointLaw`). Then `T` has a continuous fixed point bounded away from zero.
(The book's "a fixed point in `C(Z)`" is trivial: `T0 = 0`, `proposition_6_zero_fixedPoint`.)

Proof (Schauder, `schauder_closed`): `F = {f : ζ(l₀) ≤ f ≤ B}` is closed, bounded, convex and
nonempty; `T(F) ⊆ F` (`ShocksBounds.opT_mem`, Exercise 17.11 Steps 1–2); `T` is continuous
(`ShocksBounds.ex_17_11_step3`); `T(F)` is uniformly Lipschitz (`ShocksBounds.ex_17_13` and
`shocksUnif_opT_lipschitz`), hence equicontinuous. -/
theorem proposition_7 (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    (hθ2 : θhi < 2) (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (μ : Measure (ℝ × Icc (xlo / θhi) (xhi / θlo))) [IsProbabilityMeasure μ] :
    ∃ f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∃ ε > 0, ∀ z, ε ≤ f z) ∧
      ∀ z, f z = shocksOpT L H' V' θlo θhi μ (fun z => shocksCondLaw xlo xhi θlo θhi
        (shocksUnif xlo xhi) (shocksUnif θlo θhi) z.1) f z := by
  classical
  set ν : Icc (xlo / θhi) (xhi / θlo) → Measure ℝ := fun z =>
    shocksCondLaw xlo xhi θlo θhi (shocksUnif xlo xhi) (shocksUnif θlo θhi) z.1
  have hA := shocksUnif_assumption17_5 hx0 hx hθ0 hθ hθ2
  have hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo →
      0 < shocksPi (shocksUnif xlo xhi) (shocksUnif θlo θhi) z := fun z hz =>
    hA.pi_pos (fun x hx' => by rw [shocksUnif, indicator_of_mem hx']; simp [hx])
      (fun θ hθ' => by rw [shocksUnif, indicator_of_mem hθ']; simp [hθ]) hz
  have hνp : ∀ z : Icc (xlo / θhi) (xhi / θlo), IsProbabilityMeasure (ν z) := fun z =>
    hA.isProbabilityMeasure_condLaw' hπ z.1
  have hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z : Icc (xlo / θhi) (xhi / θlo) => ∫ θ, h θ ∂ν z :=
    fun h => (hA.ex_17_8b hπ h).domRestrict
  obtain ⟨l₀, hS⟩ := shocksBounds_exists hθ0 hθ.le hH hV
  have hl : l₀ ∈ Ioc 0 l₀ := ⟨hS.l₀_mem.1, le_rfl⟩
  obtain ⟨B, hB0, hB⟩ := hS.exists_integrand_le (Z := Icc (xlo / θhi) (xhi / θlo)) hl
  obtain ⟨K, -, hK⟩ := hS.ex_17_13 (Z := Icc (xlo / θhi) (xhi / θlo)) hl
  have hzl := hS.zeta_pos hl
  set F : Set (Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ) :=
    {f | ∀ z, f z ∈ Icc (olgZeta H' l₀) B} with hF
  have hTc : ∀ f ∈ F, Continuous (shocksOpT L H' V' θlo θhi μ ν f) := fun f hf =>
    (hS.opT_mem hl hB f.continuous (fun z => (hf z).1) μ ν hν).1
  have hTb : ∀ f ∈ F, ∀ z, ‖shocksOpT L H' V' θlo θhi μ ν f z‖ ≤ B := fun f hf z => by
    have h := (hS.opT_mem hl hB f.continuous (fun z => (hf z).1) μ ν hν).2 z
    rw [Real.norm_eq_abs, abs_of_pos (hzl.trans_le h.1)]
    exact h.2
  set T : (Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ) → (Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ) :=
    fun f => if hf : f ∈ F then
      ofNormedAddCommGroup (shocksOpT L H' V' θlo θhi μ ν f) (hTc f hf) B (hTb f hf) else f
  have hTF : ∀ f ∈ F, ⇑(T f) = shocksOpT L H' V' θlo θhi μ ν f := fun f hf => by
    simp only [T, hf, ↓reduceDIte, coe_ofNormedAddCommGroup]
  have hFcl : IsClosed F := by
    have : F = ⋂ z, (fun f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ => f z) ⁻¹'
        Icc (olgZeta H' l₀) B := by
      ext f; simp [hF]
    rw [this]
    exact isClosed_iInter fun z => isClosed_Icc.preimage ((continuous_apply z).comp
      continuous_coe)
  have hFconv : Convex ℝ F := fun f hf g hg a b ha hb hab z => by
    simpa using (convex_Icc _ _) (hf z) (hg z) ha hb hab
  have hFb : Bornology.IsBounded F := isBounded_iff_forall_norm_le.2
    ⟨B, fun f hf => (norm_le hB0.le).2 fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (hzl.trans_le (hf z).1)]; exact (hf z).2⟩
  have hz₀ : xlo / θhi ∈ Icc (xlo / θhi) (xhi / θlo) :=
    left_mem_Icc.2 (div_le_div₀ (hx0.trans hx).le hx.le hθ0 hθ.le)
  have hFne : F.Nonempty := ⟨const _ (olgZeta H' l₀), fun _ =>
    ⟨le_rfl, (hS.integrand_ge hl (f := fun _ : Icc (xlo / θhi) (xhi / θlo) => olgZeta H' l₀)
      (θt := 0) (ω := (0, ⟨_, hz₀⟩)) le_rfl).trans (hB _ _ _ le_rfl)⟩⟩
  have hmaps : MapsTo T F F := fun f hf z => by
    rw [hTF f hf]
    exact (hS.opT_mem hl hB f.continuous (fun z => (hf z).1) μ ν hν).2 z
  have hcont : ContinuousOn T F := by
    refine Metric.continuousOn_iff.2 fun g hg ε hε => ?_
    obtain ⟨δ, hδ, h⟩ := hS.ex_17_11_step3 (Z := Icc (xlo / θhi) (xhi / θlo)) hl hB (ε / 2)
      (half_pos hε)
    refine ⟨δ, hδ, fun f hf hfg => ?_⟩
    have hle : dist (T f) (T g) ≤ ε / 2 := by
      refine (BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun z => ?_
      rw [hTF f hf, hTF g hg, Real.dist_eq]
      exact h f g f.continuous g.continuous hf hg (fun z => by
        rw [← Real.dist_eq]; exact (dist_coe_le_dist z).trans_lt hfg) μ ν z
    linarith
  have hequi : ∀ ε > 0, ∃ δ > 0, ∀ x y : Icc (xlo / θhi) (xhi / θlo), dist x y < δ →
      ∀ g ∈ T '' F, |g x - g y| < ε := by
    intro ε hε
    set C := θhi / θlo * K * ((xlo + xhi) / (xlo / θhi) ^ 2)
    refine ⟨ε / (|C| + 1), by positivity, fun x y hxy => ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    rw [hTF f hf]
    have hfl : ∀ z, olgZeta H' l₀ ≤ f z := fun z => (hf z).1
    have h := shocksUnif_opT_lipschitz hx0 hx hθ0 hθ hθ2 μ f
      ((hS.continuous_phiF hl hB f.continuous hfl μ).continuousOn)
      (hK μ f f.continuous hfl) x y
    calc _ ≤ C * dist x y := h
      _ ≤ |C| * dist x y := mul_le_mul_of_nonneg_right (le_abs_self C) dist_nonneg
      _ ≤ |C| * (ε / (|C| + 1)) := mul_le_mul_of_nonneg_left hxy.le (abs_nonneg _)
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [abs_nonneg C]
  have htb := totallyBounded_of_equicontinuous isCompact_univ.totallyBounded
    (hFb.subset hmaps.image_subset) hequi
  obtain ⟨f, hf, hTf⟩ := schauder_closed hFcl hFconv hFne hcont hmaps
    (htb.closure.isCompact_of_isClosed isClosed_closure)
  refine ⟨f, ⟨olgZeta H' l₀, hzl, fun z => (hf z).1⟩, fun z => ?_⟩
  have := congrArg (fun g : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ => g z) hTf
  rw [← this, hTF f hf]

/-- **Proposition 7 for the islands model**, under the book's Assumption 17.1 and uniform
`Ψ`, `G`, with `μ` the joint law of `(θ′, z′)`: `T` has a continuous fixed point bounded away from
zero. -/
theorem proposition_7_islands (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    (hθ2 : θhi < 2) (hA1 : Assumption17_1 L H H' H'' V V' V'') (hZ : xlo / θhi ≤ xhi / θlo) :
    ∃ f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∃ ε > 0, ∀ z, ε ≤ f z) ∧
      ∀ z, f z = shocksOpT L H' V' θlo θhi
        (shocksJointLaw xlo xhi θlo θhi hZ (shocksUnif xlo xhi) (shocksUnif θlo θhi))
        (fun z => shocksCondLaw xlo xhi θlo θhi (shocksUnif xlo xhi) (shocksUnif θlo θhi) z.1)
        f z := by
  have := isProbabilityMeasure_shocksJointLaw (shocksUnif_assumption17_5 hx0 hx hθ0 hθ hθ2) hZ
  exact proposition_7 hx0 hx hθ0 hθ hθ2 hA1.hH (shocks_assumption17_1VR_of_V hA1.hV) _

/-! ### (7), corrected -/

/-- **(7), corrected, abstract form.** If `φ` is continuous, `A`, `B` are differentiable at `z`
with `0 < A(z) < B(z)`, and `W(w) = wavg(φ; A(w), B(w))` (the `θ`-weighted average), then
`W'(z) = [B B′ (φ(B) − W) − A A′ (φ(A) − W)] / ((B² − A²)/2)`, all at `z`. -/
theorem shocksWAvg_hasDerivAt {φ : ℝ → ℝ} (hφ : Continuous φ) {A Bf : ℝ → ℝ} {z a' b' : ℝ}
    (ha : HasDerivAt A a' z) (hb : HasDerivAt Bf b' z) (ha0 : 0 < A z) (hab : A z < Bf z) :
    HasDerivAt (fun w => shocksWAvg φ (A w) (Bf w))
      ((Bf z * b' * (φ (Bf z) - shocksWAvg φ (A z) (Bf z)) -
          A z * a' * (φ (A z) - shocksWAvg φ (A z) (Bf z))) / ((Bf z ^ 2 - A z ^ 2) / 2)) z := by
  have hc : Continuous fun θ : ℝ => θ * φ θ := continuous_id.mul hφ
  set G : ℝ → ℝ := fun u => ∫ θ in (0 : ℝ)..u, θ * φ θ
  have hG : ∀ u, HasDerivAt G (u * φ u) u := fun u => (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hS : HasDerivAt (fun w => G (Bf w) - G (A w))
      (Bf z * φ (Bf z) * b' - A z * φ (A z) * a') z :=
    ((hG (Bf z)).comp z hb).sub ((hG (A z)).comp z ha)
  have hN : HasDerivAt (fun w => (Bf w ^ 2 - A w ^ 2) / 2) (Bf z * b' - A z * a') z := by
    have := ((hb.pow 2).sub (ha.pow 2)).div_const 2
    convert this using 1
    simp only [Nat.cast_ofNat]
    ring
  have hN0 : (Bf z ^ 2 - A z ^ 2) / 2 ≠ 0 := by nlinarith
  have hq := hS.div hN hN0
  have hev : (fun w => shocksWAvg φ (A w) (Bf w)) =ᶠ[𝓝 z]
      fun w => (G (Bf w) - G (A w)) / ((Bf w ^ 2 - A w ^ 2) / 2) := by
    have hlt : ∀ᶠ w in 𝓝 z, A w < Bf w :=
      ha.continuousAt.eventually_lt hb.continuousAt hab
    filter_upwards [hlt] with w hw
    rw [shocksWAvg_of_lt hw, shocks_integral_id]
    congr 1
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
  have hW : shocksWAvg φ (A z) (Bf z) = (G (Bf z) - G (A z)) / ((Bf z ^ 2 - A z ^ 2) / 2) :=
    hev.eq_of_nhds
  rw [hW]
  have hD : Bf z ^ 2 - A z ^ 2 ≠ 0 := by nlinarith
  generalize G (Bf z) - G (A z) = S at *
  generalize Bf z ^ 2 - A z ^ 2 = D at *
  field_simp
  ring

/-- `x/w` has derivative `−x/z²` at `z ≠ 0`. -/
theorem shocks_hasDerivAt_const_div (x : ℝ) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun w => x / w) (-x / z ^ 2) z := by
  have := (hasDerivAt_inv hz).const_mul x
  convert this using 1
  · ext w; rw [div_eq_mul_inv]
  · field_simp

/-- Off the kink `x̲/z = θ̲`, `a` is differentiable: `a′(z) = −x̲/z²` if `x̲/z > θ̲` and `0` if
`x̲/z < θ̲`. -/
theorem shocksA_hasDerivAt {z : ℝ} (hz : 0 < z) (hk : xlo / z ≠ θlo) :
    HasDerivAt (shocksA xlo θlo) (if θlo < xlo / z then -xlo / z ^ 2 else 0) z := by
  have hc : ContinuousAt (fun w => xlo / w) z := continuousAt_const.div continuousAt_id hz.ne'
  rcases lt_or_gt_of_ne hk with h | h
  · simp only [not_lt.2 h.le, ↓reduceIte]
    refine (hasDerivAt_const z θlo).congr_of_eventuallyEq ?_
    filter_upwards [hc.eventually_lt continuousAt_const h] with w hw
    exact max_eq_right hw.le
  · simp only [h, ↓reduceIte]
    refine (shocks_hasDerivAt_const_div xlo hz.ne').congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_const.eventually_lt hc h] with w hw
    exact max_eq_left hw.le

/-- Off the kink `x̄/z = θ̄`, `b` is differentiable: `b′(z) = −x̄/z²` if `x̄/z < θ̄` and `0` if
`x̄/z > θ̄`. -/
theorem shocksB_hasDerivAt {z : ℝ} (hz : 0 < z) (hk : xhi / z ≠ θhi) :
    HasDerivAt (shocksB xhi θhi) (if xhi / z < θhi then -xhi / z ^ 2 else 0) z := by
  have hc : ContinuousAt (fun w => xhi / w) z := continuousAt_const.div continuousAt_id hz.ne'
  rcases lt_or_gt_of_ne hk with h | h
  · simp only [h, ↓reduceIte]
    refine (shocks_hasDerivAt_const_div xhi hz.ne').congr_of_eventuallyEq ?_
    filter_upwards [hc.eventually_lt continuousAt_const h] with w hw
    exact min_eq_left hw.le
  · simp only [not_lt.2 h.le, ↓reduceIte]
    refine (hasDerivAt_const z θhi).congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_const.eventually_lt hc h] with w hw
    exact min_eq_right hw.le

/-- **(7), corrected** (p. 537). Under Assumptions 17.5–17.6, by (6a) corrected
(`shocksUnif_integral_condLaw`) `(Tf)(w) = W(w) := wavg(φ_f; a(w), b(w))` for `w ∈ Z`. At every
`z ∈ Ẑ` (i.e. `z ∈ int Z` with `x̲/z ≠ θ̲` and `x̄/z ≠ θ̄`, the points where `a` and `b` are
differentiable) and for every continuous `φ` (e.g. `φ_f`, `ShocksBounds.continuous_phiF`),
`W'(z) = [b b′(φ(b) − W) − a a′(φ(a) − W)] / ((b² − a²)/2)` with `a′`, `b′` as in
`shocksA_hasDerivAt`, `shocksB_hasDerivAt`. The book's (7) has the uniform weights (denominator
`b − a` and no factors `a`, `b`) and is claimed "for all `z ∈ Z`"; at `z̲`, `z̄` the denominator
vanishes and at the kinks `a`, `b` are not differentiable. -/
theorem eq7_corrected (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    {φ : ℝ → ℝ} (hφ : Continuous φ) {z : ℝ} (hzZ : xlo / θhi < z ∧ z < xhi / θlo)
    (hka : xlo / z ≠ θlo) (hkb : xhi / z ≠ θhi) :
    HasDerivAt (fun w => shocksWAvg φ (shocksA xlo θlo w) (shocksB xhi θhi w))
      ((shocksB xhi θhi z * (if xhi / z < θhi then -xhi / z ^ 2 else 0) *
          (φ (shocksB xhi θhi z) - shocksWAvg φ (shocksA xlo θlo z) (shocksB xhi θhi z)) -
        shocksA xlo θlo z * (if θlo < xlo / z then -xlo / z ^ 2 else 0) *
          (φ (shocksA xlo θlo z) - shocksWAvg φ (shocksA xlo θlo z) (shocksB xhi θhi z))) /
        ((shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2) / 2)) z := by
  obtain ⟨hz0, hab⟩ := shocksA_lt_shocksB hx0 hx hθ0 hθ hzZ
  exact shocksWAvg_hasDerivAt hφ (shocksA_hasDerivAt hz0 hka) (shocksB_hasDerivAt hz0 hkb)
    (hθ0.trans_le (le_max_right _ _)) hab

/-! ### Finite `Z` (p. 539): Brouwer -/

/-- **The finite-`Z` remark** (p. 539). If `z` takes finitely many values (`Z` a finite metric
space, e.g. a finite subset of `ℝ`), then for **any** law `μ` of `(θ′, z′)` and **any**
conditional laws `G(·|z)` (no continuity in `z` and no Assumption 17.6 needed), `T` has a fixed
point bounded away from zero. As the book says, only Steps 1–3 are needed: `T` maps the compact
convex `F = {f : Z → [ζ(l₀), B]}` ⊂ `ℝ^Z` continuously into itself (`ShocksBounds.opT_mem`,
`ShocksBounds.ex_17_11_step3`), and Brouwer's theorem (`theorem_17_3`) applies. -/
theorem shocks_finite_Z {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ} {Z : Type*} [MetricSpace Z]
    [Finite Z] [Nonempty Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (hθ0 : 0 < θlo) (hθ : θlo ≤ θhi) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)] :
    ∃ f : Z → ℝ, (∃ ε > 0, ∀ z, ε ≤ f z) ∧ ∀ z, f z = shocksOpT L H' V' θlo θhi μ ν f z := by
  have := Fintype.ofFinite Z
  obtain ⟨l₀, hS⟩ := shocksBounds_exists hθ0 hθ hH hV
  have hl : l₀ ∈ Ioc 0 l₀ := ⟨hS.l₀_mem.1, le_rfl⟩
  obtain ⟨B, hB0, hB⟩ := hS.exists_integrand_le (Z := Z) hl
  have hzl := hS.zeta_pos hl
  have hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z := fun _ =>
    continuous_of_discreteTopology
  set F : Set (Z → ℝ) := {f | ∀ z, f z ∈ Icc (olgZeta H' l₀) B} with hF
  have hmem : ∀ f : F, ∀ z, shocksOpT L H' V' θlo θhi μ ν f.1 z ∈ Icc (olgZeta H' l₀) B :=
    fun f => (hS.opT_mem hl hB continuous_of_discreteTopology (fun z => (f.2 z).1) μ ν hν).2
  let T : F → F := fun f => ⟨shocksOpT L H' V' θlo θhi μ ν f.1, hmem f⟩
  have hFne : F.Nonempty := ⟨fun _ => olgZeta H' l₀, fun _ => ⟨le_rfl,
    (hS.integrand_ge hl (f := fun _ : Z => olgZeta H' l₀) (θt := 0)
      (ω := (0, Classical.arbitrary Z)) le_rfl).trans (hB _ _ _ le_rfl)⟩⟩
  have hFcl : IsClosed F := by
    have : F = ⋂ z, (fun f : Z → ℝ => f z) ⁻¹' Icc (olgZeta H' l₀) B := by ext f; simp [hF]
    rw [this]
    exact isClosed_iInter fun z => isClosed_Icc.preimage (continuous_apply z)
  have hFb : Bornology.IsBounded F := isBounded_iff_forall_norm_le.2
    ⟨B, fun f hf => (pi_norm_le_iff_of_nonneg hB0.le).2 fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (hzl.trans_le (hf z).1)]; exact (hf z).2⟩
  have hFconv : Convex ℝ F := fun f hf g hg a b ha hb hab z => by
    simpa using (convex_Icc _ _) (hf z) (hg z) ha hb hab
  have hTc : Continuous T := by
    refine Metric.continuous_iff.2 fun g ε hε => ?_
    obtain ⟨δ, hδ, h⟩ := hS.ex_17_11_step3 (Z := Z) hl hB (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun f hfg => ?_⟩
    have hle : dist (T f) (T g) ≤ ε / 2 := by
      rw [Subtype.dist_eq]
      refine (dist_pi_le_iff (half_pos hε).le).2 fun z => ?_
      rw [Real.dist_eq]
      exact h f.1 g.1 continuous_of_discreteTopology continuous_of_discreteTopology f.2 g.2
        (fun z => by
          rw [← Real.dist_eq]
          exact (dist_le_pi_dist f.1 g.1 z).trans_lt (by rwa [Subtype.dist_eq] at hfg)) μ ν z
    linarith
  obtain ⟨f, hf⟩ := theorem_17_3 hFne hFcl hFb hFconv hTc
  refine ⟨f.1, ⟨olgZeta H' l₀, hzl, fun z => (f.2 z).1⟩, fun z => ?_⟩
  have := congrArg (fun g : F => g.1 z) hf
  exact this.symm

end StokeyLucasPrescott.FixedPointArguments
