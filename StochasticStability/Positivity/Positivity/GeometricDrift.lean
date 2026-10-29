/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.KendallSets

/-!
# The geometric drift condition (V4) (MT §15.2.2–15.2.3, §15.3.1)

Meyn and Tweedie, pp. 375–382. `ψ` is a maximal irreducibility measure and the state space is
countably generated where petite sets are used through Theorem 15.2.1.

**The drift condition (V4)** (15.28), p. 376. `DriftV4 P V ρ b C` is `PV ≤ ρ V + b 1_C` for
`V : X → [0, ∞]`; with `ρ = 1 − β` it is the book's `ΔV ≤ −βV + b 1_C`, `β > 0` (a `β > 1` gives
the same condition with `ρ = 0`, since `PV ≥ 0`). `IsUnboundedOffPetite P V`: every sublevel set
`{V ≤ ℓ}`, `ℓ < ∞`, is petite.
* `DriftV4.le_add`, `DriftV4.driftV3` (with `f = (1 − ρ) V`, (V4) is (V3), p. 376),
  `DriftV4.driftV3_scaled`, `DriftV4.driftV2_scaled` (`V/(1 − ρ)` solves (V2) for `V ≥ 1`).

**Results.**
* **Lemma 15.2.2** (p. 376): (i) `lemma_15_2_2_i`, `{V < ∞}` is absorbing, and full when
  non-empty; (ii) `lemma_15_2_2_ii`, for petite `C`, `V` is unbounded off petite sets.
* **Lemma 15.2.3** (`lemma_15_2_3`, p. 376): `r P G_C^{(r)} + I = G_C^{(r)} + I_C U_C^{(r)}`, and
  (15.30), `P G_C^{(r)} ≤ r⁻¹ G_C^{(r)} + r⁻¹ I_C U_C^{(r)}`.
* **Theorem 15.2.4** (`theorem_15_2_4`, p. 377): for an `f`-Kendall `C`, `V = G_C^{(κ)}(·, f) ≥ f`
  solves (V4), with `V = f` bounded on `C`.
* **Theorem 15.2.5** (`theorem_15_2_5`, p. 377), the geometric comparison theorem, from the
  multiplied form `geom_comparison`: for `1 < r < ρ⁻¹` and `ε = r⁻¹ − ρ`,
  `E_x[Σ_{k<τ_B} V(Φ_k) rᵏ] ≤ ε⁻¹ r⁻¹ V(x) + ε⁻¹ b E_x[Σ_{k<τ_B} 1_C(Φ_k) rᵏ]`, and (15.32).
* **Theorem 15.2.6** (`theorem_15_2_6`, p. 378): under (V4) with petite `C`, every set on which `V`
  is bounded is `V`-geometrically regular; `exists_kendall_sublevel`: the sets `D` of (15.33).
* **Theorem 15.2.7** (`theorem_15_2_7`, p. 379), corrected (`C` petite and non-empty): there are
  `V ≥ f` and increasing `V`-geometrically regular sets `C_V(n)` whose union is full and absorbing.
* **Lemma 15.2.8** (`lemma_15_2_8`, p. 379): (V4) with a petite set iff `V` is unbounded off petite
  sets and `PV ≤ λV + L`, `λ < 1`.
* **Lemma 15.2.9** (`lemma_15_2_9`, p. 380): (V4) for `V` gives (V4) for `√V`.
* `IsFGeomRegularOn P f S` (15.36), p. 381: the chain restricted to `S` is `f`-geometrically
  regular; `IsFGeomRegularChain P f` for `S = X`.
* **Proposition 15.3.1** (`proposition_15_3_1`, p. 381): `U_B^{(r)}(x, f) ≤ c(B) U_C^{(κ)}(x, f)`.
* **Proposition 15.3.2** (`proposition_15_3_2`, p. 381): one petite non-empty `f`-Kendall set gives
  a full absorbing `S_f` on which the chain is `f`-geometrically regular.
* **Theorem 15.3.3** (`theorem_15_3_3`, `theorem_15_3_3_converse`, p. 382).

**Corrections.**
* Theorem 15.2.7 needs `C` petite (as Theorem 15.2.6, which its proof uses): every set `X` is
  Kendall (`τ_X = 1`), so the theorem as stated would make every `ψ`-irreducible chain
  geometrically regular on a full set, hence positive. `theorem_15_2_7_counterexample` is the null
  recurrent forward recurrence time chain of `heavyRenewal`, for which `X` is a `1`-Kendall set
  in `B⁺(X)` and no `V`-geometrically regular set lies in `B⁺(X)`.
* Proposition 15.3.1: the right side is `c(B) U_C^{(κ)}(x, f)` with the rate `κ` of (15.36); the
  book writes the rate `r = r(B)` of the left side on both sides, which the proof does not give.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### The drift condition (V4) -/

/-- **The geometric drift condition (V4)** (15.28), MT p. 376: `PV ≤ ρ V + b 1_C`, the book's
`ΔV ≤ −βV + b 1_C` with `ρ = 1 − β`. -/
def DriftV4 (P : Kernel X X) (V : X → ℝ≥0∞) (ρ b : ℝ≥0∞) (C : Set X) : Prop :=
  ∀ x, ∫⁻ y, V y ∂P x ≤ ρ * V x + C.indicator (fun _ => b) x

/-- `V` is **unbounded off petite sets** (MT p. 191): every sublevel set `{V ≤ ℓ}`, `ℓ < ∞`, is
petite. -/
def IsUnboundedOffPetite (P : Kernel X X) (V : X → ℝ≥0∞) : Prop :=
  ∀ ℓ : ℝ≥0∞, ℓ ≠ ∞ → IsPetite P {x | V x ≤ ℓ}

/-- Under (V4) with `ρ ≤ 1`, `PV ≤ V + b`. -/
theorem DriftV4.le_add {P : Kernel X X} {V : X → ℝ≥0∞} {ρ b : ℝ≥0∞} {C : Set X}
    (h : DriftV4 P V ρ b C) (hρ : ρ ≤ 1) (x : X) : ∫⁻ y, V y ∂P x ≤ V x + b :=
  (h x).trans (add_le_add (mul_le_of_le_one_left' hρ) (indicator_le_self' (fun _ _ => zero_le) x))

/-- (V4) is (V3) with `f = (1 − ρ) V` (MT p. 376). -/
theorem DriftV4.driftV3 {P : Kernel X X} {V : X → ℝ≥0∞} {ρ b : ℝ≥0∞} {C : Set X}
    (h : DriftV4 P V ρ b C) (hρ : ρ ≤ 1) : DriftV3 P V (fun x => (1 - ρ) * V x) b C := fun x => by
  calc ∫⁻ y, V y ∂P x + (1 - ρ) * V x ≤ ρ * V x + C.indicator (fun _ => b) x + (1 - ρ) * V x :=
        add_le_add (h x) le_rfl
    _ = (ρ + (1 - ρ)) * V x + C.indicator (fun _ => b) x := by ring
    _ = V x + C.indicator (fun _ => b) x := by rw [add_tsub_cancel_of_le hρ, one_mul]

/-- (V4) gives (V3) for `V/(1 − ρ)` with `f = V`: `P(cV) + V ≤ cV + cb 1_C`, `c = (1 − ρ)⁻¹`. -/
theorem DriftV4.driftV3_scaled {P : Kernel X X} {V : X → ℝ≥0∞} (hV : Measurable V)
    {ρ b : ℝ≥0∞} {C : Set X} (h : DriftV4 P V ρ b C) (hρ : ρ < 1) :
    DriftV3 P (fun x => (1 - ρ)⁻¹ * V x) V ((1 - ρ)⁻¹ * b) C := fun x => by
  have h1 : 1 - ρ ≠ 0 := (tsub_pos_iff_lt.2 hρ).ne'
  have h2 : 1 - ρ ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have h3 := h.driftV3 hρ.le x
  rw [lintegral_const_mul _ hV]
  calc (1 - ρ)⁻¹ * ∫⁻ y, V y ∂P x + V x
      = (1 - ρ)⁻¹ * (∫⁻ y, V y ∂P x + (1 - ρ) * V x) := by
        rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel h1 h2, one_mul]
    _ ≤ (1 - ρ)⁻¹ * (V x + C.indicator (fun _ => b) x) := mul_le_mul' le_rfl h3
    _ = (1 - ρ)⁻¹ * V x + C.indicator (fun _ => (1 - ρ)⁻¹ * b) x := by
        rw [mul_add]
        by_cases hx : x ∈ C
        · rw [indicator_of_mem hx, indicator_of_mem hx]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- For `V ≥ 1`, (V4) gives (V2) for `V/(1 − ρ)` (MT p. 376). -/
theorem DriftV4.driftV2_scaled {P : Kernel X X} {V : X → ℝ≥0∞} (hV : Measurable V)
    (hV1 : ∀ x, 1 ≤ V x) {ρ b : ℝ≥0∞} {C : Set X} (h : DriftV4 P V ρ b C) (hρ : ρ < 1) :
    DriftV2 P (fun x => (1 - ρ)⁻¹ * V x) ((1 - ρ)⁻¹ * b) C :=
  (h.driftV3_scaled hV hρ).driftV2 hV1

/-- (V4) for a set `C` gives (V4) for every larger set. -/
theorem DriftV4.mono_set {P : Kernel X X} {V : X → ℝ≥0∞} {ρ b : ℝ≥0∞} {C D : Set X}
    (h : DriftV4 P V ρ b C) (hCD : C ⊆ D) : DriftV4 P V ρ b D := fun x =>
  (h x).trans (add_le_add le_rfl (indicator_le_indicator_of_subset hCD (fun _ => zero_le) x))

/-- (V4) gives (V4) for every larger `ρ` and `b`. -/
theorem DriftV4.mono {P : Kernel X X} {V : X → ℝ≥0∞} {ρ ρ' b b' : ℝ≥0∞} {C : Set X}
    (h : DriftV4 P V ρ b C) (hρ : ρ ≤ ρ') (hb : b ≤ b') : DriftV4 P V ρ' b' C := fun x =>
  (h x).trans (add_le_add (mul_le_mul' hρ le_rfl) (by
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx, indicator_of_mem hx]; exact hb
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]))

/-! ### Lemma 15.2.2 -/

/-- **Lemma 15.2.2 (i)** (MT p. 376): under (V4) (`ρ ≤ 1`, `b < ∞`), `{V < ∞}` is absorbing, and
it is full for every irreducibility measure as soon as it is non-empty. -/
theorem lemma_15_2_2_i {P : Kernel X X} [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {V : X → ℝ≥0∞} (hV : Measurable V) {ρ b : ℝ≥0∞} (hρ : ρ ≤ 1)
    (hb : b ≠ ∞) {C : Set X} (h : DriftV4 P V ρ b C) :
    IsAbsorbing P {x | V x ≠ ∞} ∧ ({x | V x ≠ ∞}.Nonempty → IsFull φ {x | V x ≠ ∞}) :=
  ⟨isAbsorbing_finite_of_driftV3 hV hb (h.driftV3 hρ), fun ⟨_, hx₀⟩ =>
    (lemma_14_2_1 hφ hV hb (h.driftV3 hρ) hx₀).2⟩

/-- **Lemma 15.2.2 (ii)** (MT p. 376): if (V4) holds for a petite `C` (`V ≥ 1`, `ρ < 1`,
`b < ∞`), then `V` is unbounded off petite sets: `E_x[σ_C] ≤ E_x[τ_C] ≤ V(x)/(1 − ρ) + b'`
(Theorem 11.3.4) and the sublevel sets of `E_·[σ_C]` are petite (Lemma 11.3.7). -/
theorem lemma_15_2_2_ii {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0∞} (hV : Measurable V)
    (hV1 : ∀ x, 1 ≤ V x) {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    (h : DriftV4 P V ρ b C) : IsUnboundedOffPetite P V := by
  intro ℓ hℓ
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hct : (1 - ρ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ).ne'
  have h2 := h.driftV2_scaled hV hV1 hρ
  have hle : ∀ x, meanHitTime P C x ≤ (1 - ρ)⁻¹ * V x + (1 - ρ)⁻¹ * b := fun x =>
    (meanHitTime_le_meanReturnTime P hCm x).trans ((theorem_11_3_4 (hV.const_mul _) hCm h2 x).trans
      (add_le_add le_rfl (indicator_le_self' (fun _ _ => zero_le) x)))
  refine (isPetite_meanHitTime_le hC (ℓ := (1 - ρ)⁻¹ * ℓ + (1 - ρ)⁻¹ * b)
    (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hct hℓ, ENNReal.mul_ne_top hct hb⟩)).subset
    (measurableSet_le hV measurable_const) fun x hx => ?_
  exact (hle x).trans (add_le_add (mul_le_mul' le_rfl hx) le_rfl)

/-! ### Lemma 15.2.3 and Theorem 15.2.4 -/

/-- **Lemma 15.2.3** (MT p. 376):
`r P G_C^{(r)}(x, f) + f(x) = G_C^{(r)}(x, f) + 1_C(x) U_C^{(r)}(x, f)` (the identity
`P G_C^{(r)} = r⁻¹ G_C^{(r)} − r⁻¹ I + r⁻¹ I_C U_C^{(r)}`), and the drift (15.30),
`P G_C^{(r)} ≤ r⁻¹ G_C^{(r)} + r⁻¹ I_C U_C^{(r)}`. -/
theorem lemma_15_2_3 (P : Kernel X X) [IsMarkovKernel P] {C : Set X} (hC : MeasurableSet C)
    {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrt : r ≠ ∞) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    r * ∫⁻ y, geomG P C r f y ∂P x + f x = geomG P C r f x + C.indicator (geomTaboo P C r f) x ∧
      ∫⁻ y, geomG P C r f y ∂P x ≤
        r⁻¹ * geomG P C r f x + r⁻¹ * C.indicator (geomTaboo P C r f) x := by
  have hid : r * ∫⁻ y, geomG P C r f y ∂P x + f x =
      geomG P C r f x + C.indicator (geomTaboo P C r f) x := by
    rw [← geomTaboo_eq P hC r hf, geomG_eq P hC r hf, add_assoc,
      indicator_compl_add_self_apply, add_comm]
  refine ⟨hid, ?_⟩
  calc ∫⁻ y, geomG P C r f y ∂P x = r⁻¹ * (r * ∫⁻ y, geomG P C r f y ∂P x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hr0 hrt, one_mul]
    _ ≤ r⁻¹ * (geomG P C r f x + C.indicator (geomTaboo P C r f) x) :=
        mul_le_mul' le_rfl (hid ▸ le_self_add)
    _ = _ := mul_add _ _ _

/-- **Theorem 15.2.4** (MT p. 377): if `C` is `f`-Kendall of rate `κ` (`f ≥ 1`), then
`V = G_C^{(κ)}(·, f) ≥ f` solves (V4), `PV ≤ κ⁻¹ V + κ⁻¹ M 1_C`, and `V = f ≤ M` on `C`. The book's
hypotheses that the chain is `ψ`-irreducible and `C ∈ B⁺(X)` are not used. -/
theorem theorem_15_2_4 {P : Kernel X X} [IsMarkovKernel P] {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {κ : ℝ≥0∞} (hK : IsFKendall P f C κ) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ DriftV4 P (geomG P C κ f) κ⁻¹ (κ⁻¹ * M) C ∧
      (∀ x, f x ≤ geomG P C κ f x) ∧ ∀ x ∈ C, geomG P C κ f x ≤ M := by
  obtain ⟨hCm, hκ, hκ', M, hM, hb⟩ := hK
  obtain ⟨hfC, -, hU⟩ := fKendall_bounds P hCm hκ hf hf1 hb
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hκ).ne'
  set M' := M + M * (1 + (κ - 1) * M) with hM'
  have hM't : M' ≠ ∞ := ENNReal.add_ne_top.2 ⟨hM, ENNReal.mul_ne_top hM
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (ENNReal.sub_ne_top hκ') hM⟩)⟩
  refine ⟨max M M', max_ne_top hM hM't, fun x => ?_, le_geomG P hCm κ hf, fun x hx => ?_⟩
  · refine (lemma_15_2_3 P hCm hκ0 hκ' hf x).2.trans (add_le_add le_rfl ?_)
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      exact mul_le_mul' le_rfl ((hU x hx).trans (le_max_right _ _))
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  · rw [geomG_of_mem P hCm κ hf hx]; exact (hfC x hx).trans (le_max_left _ _)

/-! ### Theorem 15.2.5: the geometric comparison theorem -/

/-- **The geometric comparison theorem, multiplied form.** If (V4) holds and `ρ ≤ r⁻¹`
(`0 < r < ∞`), then for every stopping time `τ`, with `ε = r⁻¹ − ρ`,
`ε r E_x[Σ_{k<τ} V(Φ_k) rᵏ] ≤ V(x) + b r E_x[Σ_{k<τ} 1_C(Φ_k) rᵏ]`. -/
theorem geom_comparison (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ≥0∞} (hV : Measurable V)
    {ρ b : ℝ≥0∞} {C : Set X} (hC : MeasurableSet C) (h : DriftV4 P V ρ b C) {r : ℝ≥0∞}
    (hr0 : r ≠ 0) (hrt : r ≠ ∞) (hρr : ρ ≤ r⁻¹) {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) (x : X) :
    (r⁻¹ - ρ) * r * ∫⁻ ω, sumBefore τ (fun k ω => r ^ k * V (ω k)) ω ∂pathKernel P x ≤
      V x + b * r * ∫⁻ ω, sumBefore τ (fun k ω => r ^ k * C.indicator 1 (ω k)) ω
        ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  set ε := r⁻¹ - ρ with hε
  have hτm : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | (n : WithTop ℕ) < τ ω} :=
    fun n => (natFilt (X := X)).le n _ (measurableSet_lt_of_isStoppingTime hτ n)
  have hdrift : ∀ k : ℕ, ∀ y ∈ (univ : Set X), ∫⁻ z, r ^ (k + 1) * V z ∂P y +
      ε * r ^ (k + 1) * V y ≤ r ^ k * V y + r ^ (k + 1) * C.indicator (fun _ => b) y :=
    fun k y _ => by
    rw [lintegral_const_mul _ hV]
    calc r ^ (k + 1) * ∫⁻ z, V z ∂P y + ε * r ^ (k + 1) * V y
        = r ^ (k + 1) * (∫⁻ z, V z ∂P y + ε * V y) := by ring
      _ ≤ r ^ (k + 1) * (ρ * V y + C.indicator (fun _ => b) y + ε * V y) :=
          mul_le_mul' le_rfl (add_le_add (h y) le_rfl)
      _ = r ^ (k + 1) * ((ρ + ε) * V y) + r ^ (k + 1) * C.indicator (fun _ => b) y := by ring
      _ = r ^ k * V y + r ^ (k + 1) * C.indicator (fun _ => b) y := by
          rw [hε, add_tsub_cancel_of_le hρr, pow_succ, ← mul_assoc, mul_assoc (r ^ k),
            ENNReal.mul_inv_cancel hr0 hrt, mul_one]
  have hc := comparison_theorem P (Measure.dirac x) (V := fun k y => r ^ k * V y)
    (f := fun k y => ε * r ^ (k + 1) * V y)
    (s := fun k y => r ^ (k + 1) * C.indicator (fun _ => b) y) (fun _ => measurable_const.mul hV)
    (fun _ => (measurable_const.mul measurable_const).mul hV)
    (fun _ => measurable_const.mul (measurable_const.indicator hC)) hdrift hτ
    (fun _ _ _ => mem_univ _)
  rw [pathMeasure_dirac, lintegral_dirac' x (f := fun y => r ^ 0 * V y) (measurable_const.mul hV),
    pow_zero, one_mul] at hc
  have e1 : ∀ ω, sumBefore τ (fun k ω => ε * r ^ (k + 1) * V (ω k)) ω =
      ε * r * sumBefore τ (fun k ω => r ^ k * V (ω k)) ω := fun ω => by
    rw [← sumBefore_const_mul]; exact sumBefore_congr _ fun k _ => by rw [pow_succ]; ring
  have e2 : ∀ ω, sumBefore τ (fun k ω => r ^ (k + 1) * C.indicator (fun _ => b) (ω k)) ω =
      b * r * sumBefore τ (fun k ω => r ^ k * C.indicator 1 (ω k)) ω := fun ω => by
    rw [← sumBefore_const_mul]
    refine sumBefore_congr _ fun k _ => ?_
    by_cases hk : ω k ∈ C
    · rw [indicator_of_mem hk, indicator_of_mem hk, pow_succ, Pi.one_apply]; ring
    · rw [indicator_of_notMem hk, indicator_of_notMem hk]; simp only [mul_zero]
  have hS1 : Measurable (sumBefore τ fun k (ω : ℕ → X) => r ^ k * V (ω k)) :=
    measurable_sumBefore hτm fun k => measurable_const.mul (hV.comp (measurable_pi_apply k))
  have hS2 : Measurable (sumBefore τ fun k (ω : ℕ → X) => r ^ k * C.indicator 1 (ω k)) :=
    measurable_sumBefore hτm fun k =>
      measurable_const.mul ((measurable_one.indicator hC).comp (measurable_pi_apply k))
  simp_rw [e1, e2] at hc
  rwa [lintegral_const_mul _ hS1, lintegral_const_mul _ hS2] at hc

omit [MeasurableSpace X] in
/-- Before `τ_C` only the time `0` can be in `C`: `Σ_{k<τ_C} 1_C(Φ_k) rᵏ ≤ 1_C(Φ₀)`. -/
theorem sumBefore_indicator_firstReturn_le (C : Set X) (r : ℝ≥0∞) (ω : ℕ → X) :
    sumBefore (firstReturn C) (fun k ω => r ^ k * C.indicator 1 (ω k)) ω ≤ C.indicator 1 (ω 0) := by
  rw [sumBefore_eq_tsum, tsum_eq_zero_add' ENNReal.summable]
  have htail : ∀ k : ℕ, {k : ℕ | (k : WithTop ℕ) < firstReturn C ω}.indicator
      (fun k => r ^ k * C.indicator 1 (ω k)) (k + 1) = 0 := fun k => by
    by_cases hk : ((k + 1 : ℕ) : WithTop ℕ) < firstReturn C ω
    · rw [indicator_of_mem (show k + 1 ∈ {k : ℕ | (k : WithTop ℕ) < firstReturn C ω} from hk)]
      have hnot := (le_firstReturn_iff C ω (k + 2)).1 (succ_le_of_lt_withTop hk) (k + 1)
        (by omega) (by omega)
      simp [indicator_of_notMem hnot]
    · exact indicator_of_notMem (show k + 1 ∉ {k : ℕ | (k : WithTop ℕ) < firstReturn C ω}
        from hk) _
  rw [tsum_congr htail, tsum_zero, add_zero]
  refine (indicator_le_self _ _ 0).trans (le_of_eq ?_)
  simp only [pow_zero, one_mul]

/-- `E_x[Σ_{k<τ_C} 1_C(Φ_k) rᵏ] ≤ 1_C(x)`. -/
theorem geomSum_indicator_le (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) (r : ℝ≥0∞) (x : X) :
    geomSum P C r (C.indicator 1) x ≤ C.indicator 1 x := by
  rw [← lintegral_coord_zero P x (measurable_one.indicator hC)]
  exact lintegral_mono fun ω => sumBefore_indicator_firstReturn_le C r ω

/-- **Theorem 15.2.5** (MT p. 377), the geometric comparison theorem: if (V4) holds and
`1 < r < ρ⁻¹`, then with `ε = r⁻¹ − ρ > 0`, for every measurable `B`,
`E_x[Σ_{k<τ_B} V(Φ_k) rᵏ] ≤ ε⁻¹ r⁻¹ V(x) + ε⁻¹ b E_x[Σ_{k<τ_B} 1_C(Φ_k) rᵏ]`, and in particular
(15.32), `V(x) ≤ E_x[Σ_{k<τ_C} V(Φ_k) rᵏ] ≤ ε⁻¹ r⁻¹ V(x) + ε⁻¹ b 1_C(x)`. -/
theorem theorem_15_2_5 (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ≥0∞} (hV : Measurable V)
    {ρ b : ℝ≥0∞} {C : Set X} (hC : MeasurableSet C) (h : DriftV4 P V ρ b C) {r : ℝ≥0∞}
    (hr : 1 < r) (hrt : r ≠ ∞) (hρr : ρ < r⁻¹) :
    0 < r⁻¹ - ρ ∧
    (∀ B, MeasurableSet B → ∀ x, geomSum P B r V x ≤ (r⁻¹ - ρ)⁻¹ * r⁻¹ * V x +
      (r⁻¹ - ρ)⁻¹ * b * geomSum P B r (C.indicator 1) x) ∧
    ∀ x, V x ≤ geomSum P C r V x ∧
      geomSum P C r V x ≤ (r⁻¹ - ρ)⁻¹ * r⁻¹ * V x + (r⁻¹ - ρ)⁻¹ * b * C.indicator 1 x := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  have hε : 0 < r⁻¹ - ρ := tsub_pos_iff_lt.2 hρr
  have hεt : r⁻¹ - ρ ≠ ∞ := ENNReal.sub_ne_top (ENNReal.inv_ne_top.2 hr0)
  have key : ∀ B, MeasurableSet B → ∀ x, geomSum P B r V x ≤ (r⁻¹ - ρ)⁻¹ * r⁻¹ * V x +
      (r⁻¹ - ρ)⁻¹ * b * geomSum P B r (C.indicator 1) x := fun B hB x => by
    have hc := geom_comparison P hV hC h hr0 hrt hρr.le (proposition_3_4_4 hB).1 x
    set S := geomSum P B r V x
    set T := geomSum P B r (C.indicator 1) x
    change (r⁻¹ - ρ) * r * S ≤ V x + b * r * T at hc
    have ha0 : (r⁻¹ - ρ) * r ≠ 0 := mul_ne_zero hε.ne' hr0
    have hat : (r⁻¹ - ρ) * r ≠ ∞ := ENNReal.mul_ne_top hεt hrt
    calc S = ((r⁻¹ - ρ) * r)⁻¹ * ((r⁻¹ - ρ) * r * S) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul]
      _ ≤ ((r⁻¹ - ρ) * r)⁻¹ * (V x + b * r * T) := mul_le_mul' le_rfl hc
      _ = (r⁻¹ - ρ)⁻¹ * r⁻¹ * V x + (r⁻¹ - ρ)⁻¹ * b * T := by
          rw [ENNReal.mul_inv (Or.inl hε.ne') (Or.inl hεt), mul_add]
          congr 1
          calc (r⁻¹ - ρ)⁻¹ * r⁻¹ * (b * r * T) = (r⁻¹ - ρ)⁻¹ * b * T * (r⁻¹ * r) := by ring
            _ = (r⁻¹ - ρ)⁻¹ * b * T := by rw [ENNReal.inv_mul_cancel hr0 hrt, mul_one]
  refine ⟨hε, key, fun x => ⟨le_geomSum P C r hV x, (key C hC x).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl (geomSum_indicator_le P hC r x)))⟩⟩

/-! ### Theorem 15.2.6 -/

/-- For `ρ < 1` there is `r > 1`, `r < ∞`, with `ρ r < 1`. -/
theorem exists_one_lt_mul_lt_one {ρ : ℝ≥0∞} (hρ : ρ < 1) : ∃ r, 1 < r ∧ r ≠ ∞ ∧ ρ * r < 1 := by
  have h := ENNReal.Tendsto.const_mul tendsto_seqOneLt (a := ρ)
    (Or.inr (hρ.trans ENNReal.one_lt_top).ne)
  rw [mul_one] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds hρ)).exists
  exact ⟨seqOneLt n, one_lt_seqOneLt n, seqOneLt_ne_top n, hn⟩

/-- `ρ r < 1` gives `ρ < r⁻¹` (`0 < r < ∞`). -/
theorem lt_inv_of_mul_lt_one {ρ r : ℝ≥0∞} (hr0 : r ≠ 0) (hrt : r ≠ ∞) (h : ρ * r < 1) :
    ρ < r⁻¹ := by
  have h1 := ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.2 hrt) (ENNReal.inv_ne_top.2 hr0) h
  rwa [mul_assoc, ENNReal.mul_inv_cancel hr0 hrt, mul_one, one_mul] at h1

/-- For a nonzero `ψ` and `V` finite `ψ`-a.e., some sublevel set is in `B⁺(X)`. -/
theorem exists_sublevel_pos {ψ : Measure X} (hψ : ψ ≠ 0) {V : X → ℝ≥0∞}
    (hfull : IsFull ψ {x | V x ≠ ∞}) : ∃ n : ℕ, 0 < ψ {x | V x ≤ n} := by
  by_contra hcon
  push Not at hcon
  apply hψ
  rw [← Measure.measure_univ_eq_zero]
  refine le_antisymm ?_ zero_le
  calc ψ univ ≤ ψ (⋃ n : ℕ, {x | V x ≤ n}) + ψ {x | V x ≠ ∞}ᶜ := by
        refine (measure_mono fun x _ => ?_).trans (measure_union_le _ _)
        by_cases hx : V x = ∞
        · exact Or.inr (by simpa using hx)
        · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
          exact Or.inl (mem_iUnion.2 ⟨n, hn.le⟩)
    _ = 0 := by
        rw [hfull, add_zero]
        exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hcon n)

/-- **The sets (15.33)** (the proof of Theorem 15.2.6): under (V4) with a petite `C` (`V ≥ 1`,
`ρ < 1`, `b < ∞`) and `V` finite somewhere, for every `M < ∞` there is `ℓ ≥ M` such that
`D = {V ≤ ℓ}` is petite, in `B⁺(X)`, satisfies (V4) for some `ρ' < 1`, and, for some `s > 1` and
`d < ∞`, `E_x[Σ_{k<τ_D} V(Φ_k) sᵏ] ≤ d V(x)` for every `x` ((15.34)). -/
theorem exists_kendall_sublevel {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    (h : DriftV4 P V ρ b C) {x₀ : X} (hx₀ : V x₀ ≠ ∞) {M : ℝ≥0∞} (hM : M ≠ ∞) :
    ∃ ℓ : ℝ≥0∞, ℓ ≠ ∞ ∧ M ≤ ℓ ∧ 0 < ψ {x | V x ≤ ℓ} ∧ IsPetite P {x | V x ≤ ℓ} ∧
      (∃ ρ', ρ' < 1 ∧ DriftV4 P V ρ' b {x | V x ≤ ℓ}) ∧
      ∃ s, 1 < s ∧ s ≠ ∞ ∧ ∃ d : ℝ≥0∞, d ≠ ∞ ∧ ∀ x, geomSum P {x | V x ≤ ℓ} s V x ≤ d * V x := by
  obtain ⟨r, hr1, hrt, hρr⟩ := exists_one_lt_mul_lt_one hρ
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr1).ne'
  have hρr' : ρ < r⁻¹ := lt_inv_of_mul_lt_one hr0 hrt hρr
  have hrinv : r⁻¹ < 1 := ENNReal.inv_lt_one.2 hr1
  have hfull := (lemma_15_2_2_i hψ.2.1 hV hρ.le hb h).2 ⟨x₀, hx₀⟩
  obtain ⟨n, hn⟩ := exists_sublevel_pos hψ.1 hfull
  set ε := r⁻¹ - ρ with hε
  have hε0 : ε ≠ 0 := (tsub_pos_iff_lt.2 hρr').ne'
  have hεt : ε ≠ ∞ := ENNReal.sub_ne_top (ENNReal.inv_ne_top.2 hr0)
  set ℓ := max (max M (b / ε)) (n : ℝ≥0∞) with hℓ
  have hℓt : ℓ ≠ ∞ := max_ne_top (max_ne_top hM (ENNReal.div_ne_top hb hε0))
    (ENNReal.natCast_ne_top n)
  set D := {x | V x ≤ ℓ} with hD
  have hDm : MeasurableSet D := measurableSet_le hV measurable_const
  have hψD : 0 < ψ D := hn.trans_le (measure_mono fun x hx =>
    (show V x ≤ n from hx).trans (le_max_right _ _))
  have hpet : IsPetite P D := lemma_15_2_2_ii hV hV1 hρ hb hC h ℓ hℓt
  have hdrift : DriftV4 P V r⁻¹ b D := fun x => by
    by_cases hx : x ∈ D
    · rw [indicator_of_mem hx]
      exact (h x).trans (add_le_add (mul_le_mul' hρr'.le le_rfl)
        (indicator_le_self' (fun _ _ => zero_le) x))
    · rw [indicator_of_notMem hx, add_zero]
      have hlt : b / ε < V x := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _))
        (not_le.1 hx)
      have hbV : b ≤ V x * ε := (ENNReal.div_le_iff_le_mul (Or.inl hε0) (Or.inl hεt)).1 hlt.le
      calc ∫⁻ y, V y ∂P x ≤ ρ * V x + C.indicator (fun _ => b) x := h x
        _ ≤ ρ * V x + V x * ε := add_le_add le_rfl
            ((indicator_le_self' (fun _ _ => zero_le) x).trans hbV)
        _ = (ρ + ε) * V x := by ring
        _ = r⁻¹ * V x := by rw [hε, add_tsub_cancel_of_le hρr'.le]
  obtain ⟨s, hs1, hst, hrs⟩ := exists_one_lt_mul_lt_one hrinv
  have hs0 : s ≠ 0 := (zero_lt_one.trans hs1).ne'
  obtain ⟨-, -, h32⟩ := theorem_15_2_5 P hV hDm hdrift hs1 hst
    (lt_inv_of_mul_lt_one hs0 hst hrs)
  set c := (s⁻¹ - r⁻¹)⁻¹ with hc
  have hct : c ≠ ∞ :=
    ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 (lt_inv_of_mul_lt_one hs0 hst hrs)).ne'
  refine ⟨ℓ, hℓt, (le_max_left _ _).trans (le_max_left _ _), hψD, hpet, ⟨r⁻¹, hrinv, hdrift⟩,
    s, hs1, hst, c * s⁻¹ + c * b, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hct
      (ENNReal.inv_ne_top.2 hs0), ENNReal.mul_ne_top hct hb⟩, fun x => ?_⟩
  calc geomSum P D s V x ≤ c * s⁻¹ * V x + c * b * D.indicator 1 x := (h32 x).2
    _ ≤ c * s⁻¹ * V x + c * b * V x := add_le_add le_rfl (mul_le_mul' le_rfl
        ((indicator_le (fun _ _ => le_rfl) x).trans (by simpa using hV1 x)))
    _ = (c * s⁻¹ + c * b) * V x := by ring

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.2.6** (MT p. 378): for a `ψ`-irreducible chain, if (V4) holds for a petite `C`
(`V ≥ 1`, `ρ < 1`, `b < ∞`) and `V ≤ M < ∞` on a measurable `A`, then `A` is `V`-geometrically
regular. -/
theorem theorem_15_2_6 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    (h : DriftV4 P V ρ b C) {A : Set X} (hA : MeasurableSet A) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hVA : ∀ x ∈ A, V x ≤ M) : IsFGeomRegularSet P ψ V A := by
  rcases A.eq_empty_or_nonempty with h0 | ⟨x₀, hx₀⟩
  · subst h0
    exact ⟨MeasurableSet.empty, fun _ _ _ => ⟨2, by norm_num, ENNReal.ofNat_ne_top, 0,
      ENNReal.zero_ne_top, fun x hx => absurd hx (notMem_empty x)⟩⟩
  obtain ⟨ℓ, hℓt, hMℓ, hψD, hpet, -, s, hs1, hst, d, hd, hbd⟩ :=
    exists_kendall_sublevel hψ hV hV1 hρ hb hC h (ne_top_of_le_ne_top hM (hVA x₀ hx₀)) hM
  have hDm : MeasurableSet {x | V x ≤ ℓ} := measurableSet_le hV measurable_const
  have hK : IsFKendall P V {x | V x ≤ ℓ} s := ⟨hDm, hs1, hst, d * ℓ, ENNReal.mul_ne_top hd hℓt,
    fun x hx => (hbd x).trans (mul_le_mul' le_rfl hx)⟩
  have hreg := ((theorem_15_2_1 hψ hV hV1).1 ⟨hpet, nonempty_of_measure_ne_zero hψD.ne',
    s, hK⟩).1
  exact hreg.subset hA fun x hx => (hVA x hx).trans hMℓ

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.2.7** (MT p. 379), corrected: if `C` is a **petite**, non-empty `f`-Kendall set
(`f ≥ 1`), then `V = G_C^{(κ)}(·, f) ≥ f` has increasing `V`-geometrically regular sublevel sets
`C_V(n) = {V ≤ n}`, whose union `{V < ∞}` is full and absorbing. -/
theorem theorem_15_2_7 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} (hC : IsPetite P C) (hne : C.Nonempty) {κ : ℝ≥0∞} (hK : IsFKendall P f C κ) :
    ∃ V : X → ℝ≥0∞, Measurable V ∧ (∀ x, f x ≤ V x) ∧
      (∀ n : ℕ, IsFGeomRegularSet P ψ V {x | V x ≤ n}) ∧
      Monotone (fun n : ℕ => {x | V x ≤ n}) ∧ ⋃ n : ℕ, {x | V x ≤ n} = {x | V x ≠ ∞} ∧
      IsFull ψ {x | V x ≠ ∞} ∧ IsAbsorbing P {x | V x ≠ ∞} := by
  obtain ⟨hCm, hκ, hκ', -⟩ := id hK
  obtain ⟨M, hM, hdrift, hfV, hVC⟩ := theorem_15_2_4 hf hf1 hK
  have hVm := measurable_geomG P hCm κ hf
  have hV1 : ∀ x, 1 ≤ geomG P C κ f x := fun x => (hf1 x).trans (hfV x)
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hκ).ne'
  have hρ : κ⁻¹ < 1 := ENNReal.inv_lt_one.2 hκ
  have hb : κ⁻¹ * M ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hκ0) hM
  obtain ⟨x₀, hx₀⟩ := hne
  have hfin : geomG P C κ f x₀ ≠ ∞ := ne_top_of_le_ne_top hM (hVC x₀ hx₀)
  obtain ⟨habs, hfull⟩ := lemma_15_2_2_i hψ.2.1 hVm hρ.le hb hdrift
  refine ⟨geomG P C κ f, hVm, hfV, fun n => theorem_15_2_6 hψ hVm hV1 hρ hb hC hdrift
    (measurableSet_le hVm measurable_const) (ENNReal.natCast_ne_top n) fun _ hx => hx,
    fun m n hmn x hx => le_trans (show geomG P C κ f x ≤ m from hx) (by exact_mod_cast hmn), ?_,
    hfull ⟨x₀, hfin⟩, habs⟩
  ext x
  simp only [mem_iUnion, mem_ofPred_eq]
  refine ⟨fun ⟨n, hn⟩ => ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) hn, fun hx => ?_⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
  exact ⟨n, hn.le⟩


/-- `τ_X = 1`, so `X` is Kendall: `E_x[Σ_{k<τ_X} f(Φ_k) κᵏ] = f(Φ₀)`; in particular `X` is a
`1`-Kendall set of every rate. -/
theorem geomSum_univ_one (P : Kernel X X) [IsMarkovKernel P] (κ : ℝ≥0∞) (x : X) :
    geomSum P univ κ (fun _ => 1) x = 1 := by
  have := isMarkovKernel_pathKernel P
  have h1 : ∀ ω : ℕ → X, firstReturn univ ω = ((1 : ℕ) : WithTop ℕ) := fun ω =>
    (firstReturn_eq_iff univ ω 0).2 ⟨one_le_firstReturn univ ω, mem_univ _⟩
  rw [geomSum, lintegral_congr fun ω => sumBefore_of_eq' (h1 ω)]
  simp

/-- **The counterexample to Theorem 15.2.7 as stated.** For the forward recurrence time chain of
`heavyRenewal` (null recurrent, `ψ = count`), `X = ℕ` is a `1`-Kendall set in `B⁺(X)`, but there
are no `V ≥ 1` and `V`-geometrically regular sets whose union is full: a `V`-geometrically
regular set containing `0` would make `{0}` regular, and the chain positive
(Proposition 14.1.1). -/
theorem theorem_15_2_7_counterexample :
    haveI := isProbabilityMeasure_heavyRenewal
    haveI := isMarkovKernel_fwdRecKernel heavyRenewal
    IsFKendallSet (fwdRecKernel heavyRenewal) (fun _ => 1) univ ∧
      0 < Measure.count (univ : Set ℕ) ∧
      ¬ ∃ V : ℕ → ℝ≥0∞, (∀ x, 1 ≤ V x) ∧ ∃ S : ℕ → Set ℕ,
        (∀ i, IsFGeomRegularSet (fwdRecKernel heavyRenewal) Measure.count V (S i)) ∧
          IsFull Measure.count (⋃ i, S i) := by
  have := isProbabilityMeasure_heavyRenewal
  have := isMarkovKernel_fwdRecKernel heavyRenewal
  obtain ⟨hrec, -, -, hinv, htop, hnpos⟩ := theorem_10_0_1_counterexample
  refine ⟨⟨2, MeasurableSet.univ, by norm_num, ENNReal.ofNat_ne_top, 1, ENNReal.one_ne_top,
    fun x _ => (geomSum_univ_one _ 2 x).le⟩, ?_, ?_⟩
  · calc (0 : ℝ≥0∞) < Measure.count ({0} : Set ℕ) := by rw [Measure.count_singleton]; exact one_pos
      _ ≤ Measure.count univ := measure_mono (subset_univ _)
  · rintro ⟨V, hV1, S, hS, hfull⟩
    have hU : ⋃ i, S i = univ := by
      have h0 := Measure.count_eq_zero_iff.1 hfull
      exact compl_empty_iff.1 h0
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hU.symm ▸ mem_univ (0 : ℕ) : (0 : ℕ) ∈ ⋃ i, S i)
    have hreg := (hS i).subset (measurableSet_singleton 0) (singleton_subset_iff.2 hi)
    obtain ⟨r, hr, -, M, hM, hb⟩ := hreg.2 {0} (measurableSet_singleton 0)
      (by rw [Measure.count_singleton]; exact one_pos)
    have hbound : ∀ x ∈ ({0} : Set ℕ), fSumReturn (fwdRecKernel heavyRenewal) {0}
        (fun _ => 1) x ≤ M := fun x hx =>
      ((fSumReturn_le_geomSum _ {0} hr.le _ x).trans (geomSum_mono_f _ {0} r hV1 x)).trans
        (hb x hx)
    have hπ0 : fwdRecInv heavyRenewal ≠ 0 := fun h0 => by simp [h0] at htop
    have hπC : fwdRecInv heavyRenewal {0} ≠ ∞ := by
      rw [fwdRecInv_singleton]; exact measure_ne_top _ _
    exact hnpos (proposition_14_1_1 hrec hinv hπ0 measurable_const (fun _ => le_rfl)
      (measurableSet_singleton 0) ⟨0, rfl⟩ hπC hM hbound).2.2.2

/-! ### Lemmas 15.2.8 and 15.2.9 -/

/-- **Lemma 15.2.8** (MT p. 379): for `V ≥ 1`, (V4) holds for some petite set iff `V` is
unbounded off petite sets and `PV ≤ λV + L` for some `λ < 1`, `L < ∞` (15.35). -/
theorem lemma_15_2_8 {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0∞} (hV : Measurable V)
    (hV1 : ∀ x, 1 ≤ V x) :
    (∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧ ∃ C, IsPetite P C ∧ DriftV4 P V ρ b C) ↔
      (IsUnboundedOffPetite P V ∧ ∃ lam L : ℝ≥0∞, lam < 1 ∧ L ≠ ∞ ∧
        ∀ x, ∫⁻ y, V y ∂P x ≤ lam * V x + L) := by
  constructor
  · rintro ⟨ρ, b, hρ, hb, C, hC, h⟩
    exact ⟨lemma_15_2_2_ii hV hV1 hρ hb hC h, ρ, b, hρ, hb, fun x =>
      (h x).trans (add_le_add le_rfl (indicator_le_self' (fun _ _ => zero_le) x))⟩
  · rintro ⟨hU, lam, L, hlam, hL, h⟩
    obtain ⟨ρ, hlρ, hρ1⟩ := exists_between hlam
    set ε := ρ - lam with hε
    have hε0 : ε ≠ 0 := (tsub_pos_iff_lt.2 hlρ).ne'
    have hεt : ε ≠ ∞ := ENNReal.sub_ne_top (hρ1.trans ENNReal.one_lt_top).ne
    refine ⟨ρ, L, hρ1, hL, {x | V x ≤ L / ε}, hU _ (ENNReal.div_ne_top hL hε0), fun x => ?_⟩
    by_cases hx : x ∈ {x | V x ≤ L / ε}
    · rw [indicator_of_mem hx]
      exact (h x).trans (add_le_add (mul_le_mul' hlρ.le le_rfl) le_rfl)
    · rw [indicator_of_notMem hx, add_zero]
      have hLV : L ≤ V x * ε :=
        (ENNReal.div_le_iff_le_mul (Or.inl hε0) (Or.inl hεt)).1 (not_le.1 hx).le
      calc ∫⁻ y, V y ∂P x ≤ lam * V x + L := h x
        _ ≤ lam * V x + V x * ε := add_le_add le_rfl hLV
        _ = (lam + ε) * V x := by ring
        _ = ρ * V x := by rw [hε, add_tsub_cancel_of_le hlρ.le]

/-- **Jensen's inequality for `√`**: `∫ √g dμ ≤ √(∫ g dμ)` for a probability `μ`. -/
theorem lintegral_rpow_half_le {μ : Measure X} [IsProbabilityMeasure μ] {g : X → ℝ≥0∞}
    (hg : Measurable g) : ∫⁻ y, g y ^ (1 / 2 : ℝ) ∂μ ≤ (∫⁻ y, g y ∂μ) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hg.pow_const (1 / 2 : ℝ)).aemeasurable (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  have e : ∀ y, (g y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = g y := fun y => by
    rw [← ENNReal.rpow_mul]; norm_num
  simp_rw [e] at h
  simpa using h

/-- **Lemma 15.2.9** (MT p. 380): if (V4) holds for `V ≥ 1` and a petite set, it holds for `√V`
and some petite set. The bound `P√V ≤ √λ √V + √L` replaces the book's
`P√V ≤ √λ √V + L/(2√λ)`; either form gives (15.35). -/
theorem lemma_15_2_9 {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0∞} (hV : Measurable V)
    (hV1 : ∀ x, 1 ≤ V x) {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    (h : DriftV4 P V ρ b C) :
    ∃ ρ' b' : ℝ≥0∞, ρ' < 1 ∧ b' ≠ ∞ ∧ ∃ C', IsPetite P C' ∧
      DriftV4 P (fun x => V x ^ (1 / 2 : ℝ)) ρ' b' C' := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hsq : ∀ x, (V x ^ (1 / 2 : ℝ)) ^ 2 = V x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hWm : Measurable fun x => V x ^ (1 / 2 : ℝ) := hV.pow_const _
  have hW1 : ∀ x, 1 ≤ V x ^ (1 / 2 : ℝ) := fun x => by
    simpa using ENNReal.rpow_le_rpow (hV1 x) hhalf.le
  refine (lemma_15_2_8 hWm hW1).2 ⟨fun ℓ hℓ => ?_, ρ ^ (1 / 2 : ℝ), b ^ (1 / 2 : ℝ),
    ENNReal.rpow_lt_one hρ hhalf, ENNReal.rpow_ne_top_of_nonneg hhalf.le hb, fun x => ?_⟩
  · refine (lemma_15_2_2_ii hV hV1 hρ hb hC h (ℓ ^ 2) (ENNReal.pow_ne_top hℓ)).subset
      (measurableSet_le hWm measurable_const) fun y hy => ?_
    change V y ≤ ℓ ^ 2
    rw [← hsq y]
    exact pow_le_pow_left₀ zero_le hy 2
  · calc ∫⁻ y, V y ^ (1 / 2 : ℝ) ∂P x ≤ (∫⁻ y, V y ∂P x) ^ (1 / 2 : ℝ) := lintegral_rpow_half_le hV
      _ ≤ (ρ * V x + b) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow ((h x).trans (add_le_add le_rfl
          (indicator_le_self' (fun _ _ => zero_le) x))) hhalf.le
      _ ≤ (ρ * V x) ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_add_le_add_rpow _ _ hhalf.le (by norm_num)
      _ = ρ ^ (1 / 2 : ℝ) * V x ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf.le]

/-! ### `f`-geometric regularity of the chain -/

/-- **The chain restricted to `S` is `f`-geometrically regular** (15.36), MT p. 381: there are a
petite set `C` and `κ > 1` such that `E_x[Σ_{k<τ_C} f(Φ_k) κᵏ]` is finite for `x ∈ S` and bounded
on `C`. -/
def IsFGeomRegularOn (P : Kernel X X) [IsMarkovKernel P] (f : X → ℝ≥0∞) (S : Set X) : Prop :=
  ∃ C, IsPetite P C ∧ ∃ κ : ℝ≥0∞, 1 < κ ∧ κ ≠ ∞ ∧ (∀ x ∈ S, geomSum P C κ f x ≠ ∞) ∧
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, geomSum P C κ f x ≤ M

/-- **The chain is `f`-geometrically regular** (15.36), MT p. 381. -/
def IsFGeomRegularChain (P : Kernel X X) [IsMarkovKernel P] (f : X → ℝ≥0∞) : Prop :=
  IsFGeomRegularOn P f univ

/-- `f`-geometric regularity on `S` passes to `g ≤ f`. -/
theorem IsFGeomRegularOn.mono {P : Kernel X X} [IsMarkovKernel P] {f g : X → ℝ≥0∞}
    {S : Set X} (h : IsFGeomRegularOn P f S) (hgf : g ≤ f) : IsFGeomRegularOn P g S := by
  obtain ⟨C, hC, κ, hκ, hκ', hfin, M, hM, hb⟩ := h
  exact ⟨C, hC, κ, hκ, hκ', fun x hx => ne_top_of_le_ne_top (hfin x hx)
    (geomSum_mono_f P C κ hgf x), M, hM, fun x hx => (geomSum_mono_f P C κ hgf x).trans (hb x hx)⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 15.3.1** (MT p. 381): if `C` is petite and `f`-Kendall of rate `κ` (as in
(15.36), `f ≥ 1`), then for every `B ∈ B⁺(X)` there are `r > 1` and `c(B) < ∞` with
`U_B^{(r)}(x, f) ≤ c(B) U_C^{(κ)}(x, f)` (15.37) for every `x`. -/
theorem proposition_15_3_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} (hC : IsPetite P C) {κ : ℝ≥0∞} (hK : IsFKendall P f C κ) {B : Set X}
    (hB : MeasurableSet B) (hψB : 0 < ψ B) :
    ∃ r, 1 < r ∧ r ≤ κ ∧ ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ x,
      geomTaboo P B r f x ≤ c * geomTaboo P C κ f x := by
  obtain ⟨r, hr, hrκ, K, hK', hbd⟩ := theorem_15_2_1_bound hψ hf hf1 hC hK hB hψB
  have := isMarkovKernel_pathKernel P
  have hκ1 : 1 ≤ κ := hK.2.1.le
  refine ⟨r, hr, hrκ, 1 + K + K, ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨ENNReal.one_ne_top, hK'⟩, hK'⟩, fun x => ?_⟩
  have h1 : kendallMoment P C κ x ≤ geomTaboo P C κ f x := kendallMoment_le_geomTaboo P C hκ1 hf1 x
  have h2 : 1 ≤ geomTaboo P C κ f x := by
    refine le_trans ?_ h1
    rw [← (measure_univ (μ := pathKernel P x)), ← lintegral_one]
    exact lintegral_mono fun ω => one_le_tpow hκ1 _
  calc geomTaboo P B r f x ≤ geomTaboo P C κ f x + K * kendallMoment P C κ x + K := hbd x
    _ ≤ geomTaboo P C κ f x + K * geomTaboo P C κ f x + K * geomTaboo P C κ f x :=
        add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl h1)) (le_mul_of_one_le_right' h2)
    _ = (1 + K + K) * geomTaboo P C κ f x := by ring

/-- **Proposition 15.3.2** (MT p. 381): if there is one petite, non-empty `f`-Kendall set `C`
(`f ≥ 1`), there is a full absorbing set `S_f = {V < ∞}`, `V = G_C^{(κ)}(·, f)`, on which the chain
is `f`-geometrically regular (and even `V`-geometrically regular, (15.38)). -/
theorem proposition_15_3_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} (hC : IsPetite P C) (hne : C.Nonempty) {κ : ℝ≥0∞} (hK : IsFKendall P f C κ) :
    ∃ S : Set X, MeasurableSet S ∧ IsFull ψ S ∧ IsAbsorbing P S ∧
      IsFGeomRegularOn P (geomG P C κ f) S ∧ IsFGeomRegularOn P f S := by
  obtain ⟨hCm, hκ, hκ', -⟩ := id hK
  obtain ⟨M, hM, hdrift, hfV, hVC⟩ := theorem_15_2_4 hf hf1 hK
  have hVm := measurable_geomG P hCm κ hf
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hκ).ne'
  have hρ : κ⁻¹ < 1 := ENNReal.inv_lt_one.2 hκ
  have hb : κ⁻¹ * M ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hκ0) hM
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨habs, hfull⟩ := lemma_15_2_2_i hψ.2.1 hVm hρ.le hb hdrift
  obtain ⟨s, hs1, hst, hκs⟩ := exists_one_lt_mul_lt_one hρ
  have hs0 : s ≠ 0 := (zero_lt_one.trans hs1).ne'
  have hlt := lt_inv_of_mul_lt_one hs0 hst hκs
  obtain ⟨-, -, h32⟩ := theorem_15_2_5 P hVm hCm hdrift hs1 hst hlt
  set c := (s⁻¹ - κ⁻¹)⁻¹ with hc
  have hct : c ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hlt).ne'
  have hreg : IsFGeomRegularOn P (geomG P C κ f) {x | geomG P C κ f x ≠ ∞} := by
    refine ⟨C, hC, s, hs1, hst, fun x hx => ?_, c * s⁻¹ * M + c * (κ⁻¹ * M) * 1, ?_,
      fun x hx => ?_⟩
    · refine ne_top_of_le_ne_top ?_ (h32 x).2
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top hct
        (ENNReal.inv_ne_top.2 hs0)) hx, ENNReal.mul_ne_top (ENNReal.mul_ne_top hct hb)
          (ne_top_of_le_ne_top ENNReal.one_ne_top (indicator_le (fun _ _ => le_rfl) x))⟩
    · exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top hct
        (ENNReal.inv_ne_top.2 hs0)) hM, ENNReal.mul_ne_top (ENNReal.mul_ne_top hct hb)
          ENNReal.one_ne_top⟩
    · exact (h32 x).2.trans (add_le_add (mul_le_mul' le_rfl (hVC x hx))
        (mul_le_mul' le_rfl (indicator_le (fun _ _ => le_rfl) x)))
  exact ⟨{x | geomG P C κ f x ≠ ∞}, (measurableSet_singleton ∞).compl.preimage hVm,
    hfull ⟨x₀, ne_top_of_le_ne_top hM (hVC x₀ hx₀)⟩, habs, hreg, hreg.mono hfV⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.3.3** (MT p. 382): if (V4) holds for a petite set and an everywhere finite
`V ≥ 1` (`ρ < 1`, `b < ∞`), the chain is `V`-geometrically regular, and for every `B ∈ B⁺(X)`
there are `r > 1` and `c(B) < ∞` with `U_B^{(r)}(x, V) ≤ c(B) V(x)` for every `x`. -/
theorem theorem_15_3_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    (h : DriftV4 P V ρ b C) {x₀ : X} (hx₀ : V x₀ ≠ ∞) :
    IsFGeomRegularOn P V {x | V x ≠ ∞} ∧ ∀ B, MeasurableSet B → 0 < ψ B →
      ∃ r, 1 < r ∧ ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ x, geomTaboo P B r V x ≤ c * V x := by
  obtain ⟨ℓ, hℓt, -, hψD, hpet, -, s, hs1, hst, d, hd, hbd⟩ :=
    exists_kendall_sublevel hψ hV hV1 hρ hb hC h hx₀ ENNReal.one_ne_top
  set D := {x | V x ≤ ℓ} with hD
  have hDm : MeasurableSet D := measurableSet_le hV measurable_const
  have hK : IsFKendall P V D s := ⟨hDm, hs1, hst, d * ℓ, ENNReal.mul_ne_top hd hℓt,
    fun x hx => (hbd x).trans (mul_le_mul' le_rfl hx)⟩
  refine ⟨⟨D, hpet, s, hs1, hst, fun x hx => ne_top_of_le_ne_top (ENNReal.mul_ne_top hd hx)
    (hbd x), d * ℓ, ENNReal.mul_ne_top hd hℓt, fun x hx => (hbd x).trans
      (mul_le_mul' le_rfl hx)⟩, fun B hB hψB => ?_⟩
  obtain ⟨r, hr, -, K, hK', hbdB⟩ := theorem_15_2_1_bound hψ hV hV1 hpet hK hB hψB
  have hst1 : s - 1 ≠ ∞ := ENNReal.sub_ne_top hst
  set c₁ := d + ℓ * (1 + (s - 1) * d) with hc₁
  refine ⟨r, hr, c₁ + K * (1 + (s - 1) * d) + K, ?_, fun x => ?_⟩
  · have h1 : 1 + (s - 1) * d ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top hst1 hd⟩
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hd,
      ENNReal.mul_ne_top hℓt h1⟩, ENNReal.mul_ne_top hK' h1⟩, hK'⟩
  have hkm : kendallMoment P D s x ≤ (1 + (s - 1) * d) * V x := by
    calc kendallMoment P D s x ≤ 1 + (s - 1) * geomSum P D s V x :=
          kendallMoment_le_one_add P hDm hs1 hV1 x
      _ ≤ V x + (s - 1) * (d * V x) := add_le_add (hV1 x) (mul_le_mul' le_rfl (hbd x))
      _ = (1 + (s - 1) * d) * V x := by ring
  have hU : geomTaboo P D s V x ≤ c₁ * V x := by
    calc geomTaboo P D s V x ≤ geomSum P D s V x + ℓ * kendallMoment P D s x :=
          geomTaboo_le_geomSum_add P hDm hs1 hV (fun y hy => hy) x
      _ ≤ d * V x + ℓ * ((1 + (s - 1) * d) * V x) :=
          add_le_add (hbd x) (mul_le_mul' le_rfl hkm)
      _ = c₁ * V x := by ring
  calc geomTaboo P B r V x ≤ geomTaboo P D s V x + K * kendallMoment P D s x + K := hbdB x
    _ ≤ c₁ * V x + K * ((1 + (s - 1) * d) * V x) + K * V x :=
        add_le_add (add_le_add hU (mul_le_mul' le_rfl hkm)) (le_mul_of_one_le_right' (hV1 x))
    _ = (c₁ + K * (1 + (s - 1) * d) + K) * V x := by ring

/-- **The converse in Theorem 15.3.3** (MT p. 382): if the chain is `f`-geometrically regular
(`f ≥ 1`), there are a petite `C` and an everywhere finite `V = G_C^{(κ)}(·, f) ≥ f` solving
(V4). -/
theorem theorem_15_3_3_converse {P : Kernel X X} [IsMarkovKernel P] {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (h : IsFGeomRegularChain P f) :
    ∃ C, IsPetite P C ∧ ∃ V : X → ℝ≥0∞, Measurable V ∧ (∀ x, f x ≤ V x) ∧ (∀ x, V x ≠ ∞) ∧
      ∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧ DriftV4 P V ρ b C := by
  obtain ⟨C, hC, κ, hκ, hκ', hfin, M, hM, hb⟩ := h
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hK : IsFKendall P f C κ := ⟨hCm, hκ, hκ', M, hM, hb⟩
  obtain ⟨M', hM', hdrift, hfV, -⟩ := theorem_15_2_4 hf hf1 hK
  obtain ⟨hfC, -, -⟩ := fKendall_bounds P hCm hκ hf hf1 hb
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hκ).ne'
  refine ⟨C, hC, geomG P C κ f, measurable_geomG P hCm κ hf, hfV, fun x => ?_, κ⁻¹, κ⁻¹ * M',
    ENNReal.inv_lt_one.2 hκ, ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hκ0) hM', hdrift⟩
  have hx := hfin x (mem_univ x)
  refine ne_top_of_le_ne_top ?_ (geomG_le P hCm κ hf x)
  refine ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top hx (le_geomSum P C κ hf x), ?_⟩
  refine ne_top_of_le_ne_top ?_ (geomTaboo_le_geomSum_add P hCm hκ hf hfC x)
  refine ENNReal.add_ne_top.2 ⟨hx, ENNReal.mul_ne_top hM ?_⟩
  refine ne_top_of_le_ne_top ?_ (kendallMoment_le_one_add P hCm hκ hf1 x)
  exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (ENNReal.sub_ne_top hκ') hx⟩

end MeynTweedie.Positivity
