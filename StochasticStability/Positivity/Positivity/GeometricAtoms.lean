/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.GeometricDrift

/-!
# Geometric ergodicity of chains with atoms (MT §15.1)

Meyn and Tweedie, §15.1, pp. 364–372. `α` is an atom with a point `a ∈ α`; `p(n) = P_a(τ_α = n)`
is its return-time law (`entryLaw P hα (δ_a)`), `u(n) = Pⁿ(a, α)` its renewal sequence
(`atomRenewal`), `a_λ(n) = P_λ(τ_α = n)` the entry law of `λ`, and
`t_f(j + 1) = ∫ f d(_αP^{j+1}(a, ·))`.

**Generating functions.**
* `tsum_pow_tabooKernel_le_kendallMoment`: `Σₙ r^{n+1} P_x(τ_A = n + 1) ≤ E_x[r^{τ_A}]`;
  `hitProb_eq_one_of_kendallMoment_ne_top`: a finite Kendall moment forces `τ_A < ∞` a.s.;
  `tsum_entryLaw_mul_pow_le`, `summable_entryLaw_mul_pow`: `Σₙ a_λ(n) rⁿ ≤ E_λ[r^{τ_A}]`.
* `tsum_pow_lintegral_tabooKernel` ((15.9)): `Σₙ r^{n+1} ∫ f d(_AP^{n+1}(x, ·)) = U_A^{(r)}(x, f)`;
  `tsum_pow_lintegral_tabooSeq`: the same from an initial law.

**The geometric regenerative bound** (15.8)–(15.11).
* `tsum_fNorm_le_geom_atom`: if `π = π(α) μ°_α`, `L(a, α) = 1`, the return-time law is aperiodic
  and `U_α^{(κ)}(a, f) < ∞` (`f ≥ 1`), then for some `r ∈ (1, κ]` and `R < ∞`, for every initial
  probability `λ`, `Σₙ r^{n+1} ‖λPⁿ⁺¹ − π‖_f ≤ R E_λ[U_α^{(κ)}(Φ₀, f)]`. The rate is
  `min(κ, r_α)`, `r_α` from Kendall's theorem.

**Definitions** (p. 368). `IsGeomErgodicAtom P π α`: `Σₙ r_αⁿ |Pⁿ(α, α) − π(α)| < ∞` for some
`r_α > 1`; Kendall atoms and `f`-Kendall atoms are `IsKendall P α κ` and `IsFKendall P f α κ` for an
atom `α`.

**Results.**
* **Proposition 15.1.2** (`proposition_15_1_2`, p. 369).
* **Proposition 15.1.3** (`proposition_15_1_3`, p. 369), with the corrected identity
  `proposition_15_1_3_identity`:
  `P U_α^{(κ)}(·, f) + Pf = κ⁻¹ U_α^{(κ)}(·, f) + P(·, α) U_α^{(κ)}(α, f)`.
* **Theorem 15.1.4** (`theorem_15_1_4`, p. 369), corrected: the chain must be aperiodic.
* **Theorem 15.1.5** (`theorem_15_1_5`, p. 370), whose proof the book omits.
* `isAperiodicLaw_of_tendsto_pos`: a renewal sequence converging to a positive limit has an
  aperiodic increment law (used for Theorem 15.1.5).

**Corrections.**
* Proposition 15.1.3: the identity printed in the proof omits the term `−P(x, B)`
  (`proposition_15_1_3_counterexample`: on a one-point space it would give `κ = 1 + κ`); the
  conclusion holds, through `proposition_15_1_3_identity`.
* Theorem 15.1.4 needs aperiodicity (used through Proposition 15.1.2):
  `theorem_15_1_4_counterexample` is the period-`2` flip chain on `Bool`, whose atom `{true}` is
  `1`-Kendall but `‖Pⁿ(x, ·) − π‖ = 1` for every `n`.
* (15.18) holds with the sum over `n ≥ 1`; the term `n = 0` is `‖δ_x − π‖_f`, which
  `U_α^{(κ)}(x, f)` does not control. The proofs only use `n ≥ 1`.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### Kendall moments and the return-time law -/

/-- Pathwise: `Σₙ r^{n+1} 1{τ = n + 1} ≤ r^τ`. -/
theorem tsum_indicator_pow_le_tpow {Ω : Type*} (τ : Ω → WithTop ℕ) (r : ℝ≥0∞) (ω : Ω) :
    ∑' n : ℕ, {ω | τ ω = WithTop.some (n + 1)}.indicator (fun _ => r ^ (n + 1)) ω ≤
      tpow r (τ ω) := by
  cases h : τ ω with
  | top => exact le_top
  | coe t =>
    rw [tsum_eq_single (t - 1) fun n hn => indicator_of_notMem (fun hmem => hn (by
      have h2 : WithTop.some t = WithTop.some (n + 1) := h.symm.trans hmem
      have := WithTop.coe_inj.1 h2
      omega)) _]
    by_cases hmem : ω ∈ {ω | τ ω = WithTop.some (t - 1 + 1)}
    · rw [indicator_of_mem hmem]
      have h2 : WithTop.some t = WithTop.some (t - 1 + 1) := h.symm.trans hmem
      rw [← WithTop.coe_inj.1 h2]
      exact le_of_eq rfl
    · rw [indicator_of_notMem hmem]; exact zero_le

/-- **`Σₙ r^{n+1} P_x(τ_A = n + 1) ≤ E_x[r^{τ_A}]`**. -/
theorem tsum_pow_tabooKernel_le_kendallMoment (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (r : ℝ≥0∞) (x : X) :
    ∑' n, r ^ (n + 1) * tabooKernel P hA n x A ≤ kendallMoment P A r x := by
  have := isMarkovKernel_pathKernel P
  have hm : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | firstReturn A ω = WithTop.some (n + 1)} :=
    fun n => (natFilt (X := X)).le (n + 1) _
      ((proposition_3_4_4 hA).1.measurableSet_eq_of_countable (n + 1))
  calc ∑' n, r ^ (n + 1) * tabooKernel P hA n x A
      = ∑' n, ∫⁻ ω, {ω | firstReturn A ω = WithTop.some (n + 1)}.indicator
          (fun _ => r ^ (n + 1)) ω ∂pathKernel P x := tsum_congr fun n => by
        rw [lintegral_indicator_const (hm n), firstReturn_eq_tabooKernel]
    _ = ∫⁻ ω, ∑' n, {ω | firstReturn A ω = WithTop.some (n + 1)}.indicator
          (fun _ => r ^ (n + 1)) ω ∂pathKernel P x :=
        (lintegral_tsum fun n => (measurable_const.indicator (hm n)).aemeasurable).symm
    _ ≤ kendallMoment P A r x :=
        lintegral_mono fun ω => tsum_indicator_pow_le_tpow (firstReturn A) r ω

/-- A finite Kendall moment forces `τ_A < ∞` almost surely: `L(x, A) = 1`. -/
theorem hitProb_eq_one_of_kendallMoment_ne_top (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {r : ℝ≥0∞} {x : X} (h : kendallMoment P A r x ≠ ∞) :
    hitProb P A x = 1 := by
  have := isMarkovKernel_pathKernel P
  have hS := measurableSet_ne_top (proposition_3_4_4 hA).1 (X := X)
  have h0 : pathKernel P x {ω | firstReturn A ω ≠ ⊤}ᶜ = 0 := by
    by_contra hne
    apply h
    refine top_le_iff.1 ?_
    calc ∞ = ∫⁻ _ in {ω | firstReturn A ω ≠ ⊤}ᶜ, ∞ ∂pathKernel P x := by
          rw [setLIntegral_const, ENNReal.top_mul hne]
      _ ≤ ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤}ᶜ, tpow r (firstReturn A ω) ∂pathKernel P x :=
          setLIntegral_mono' hS.compl fun ω hω => by
            have : firstReturn A ω = ⊤ := by simpa using hω
            rw [this, tpow_top]
      _ ≤ kendallMoment P A r x := setLIntegral_le_lintegral _ _
  exact (prob_compl_eq_zero_iff hS).1 h0

/-- **`Σₙ a_λ(n) rⁿ ≤ E_λ[r^{τ_A}]`** in `[0, ∞]`, for a finite measure `λ`. -/
theorem tsum_entryLaw_mul_pow_le (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (μ : Measure X) [IsFiniteMeasure μ] (r : ℝ≥0∞) :
    ∑' n, ENNReal.ofReal (entryLaw P hA μ n) * r ^ n ≤ ∫⁻ x, kendallMoment P A r x ∂μ := by
  rw [tsum_eq_zero_add' ENNReal.summable, entryLaw_zero, ENNReal.ofReal_zero, zero_mul, zero_add]
  have hfin : ∀ n, tabooSeq P hA μ n A ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (measure_ne_top μ univ) (tabooSeq_apply_le P hA μ n A)
  calc ∑' n, ENNReal.ofReal (entryLaw P hA μ (n + 1)) * r ^ (n + 1)
      = ∑' n, ∫⁻ x, r ^ (n + 1) * tabooKernel P hA n x A ∂μ := tsum_congr fun n => by
        rw [entryLaw_succ, ENNReal.ofReal_toReal (hfin n), tabooSeq,
          Measure.bind_apply hA (Kernel.aemeasurable _), lintegral_const_mul _
            (Kernel.measurable_coe _ hA), mul_comm]
    _ = ∫⁻ x, ∑' n, r ^ (n + 1) * tabooKernel P hA n x A ∂μ :=
        (lintegral_tsum fun n => (measurable_const.mul
          (Kernel.measurable_coe _ hA)).aemeasurable).symm
    _ ≤ ∫⁻ x, kendallMoment P A r x ∂μ :=
        lintegral_mono fun x => tsum_pow_tabooKernel_le_kendallMoment P hA r x

/-- **The entry law has a geometric moment**: if `E_λ[r^{τ_A}] < ∞` (`r ≥ 0` real), then
`Σₙ a_λ(n) rⁿ` converges, with sum at most `E_λ[r^{τ_A}]`. -/
theorem summable_entryLaw_mul_pow (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (μ : Measure X) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 ≤ r)
    (h : ∫⁻ x, kendallMoment P A (ENNReal.ofReal r) x ∂μ ≠ ∞) :
    Summable (fun n => entryLaw P hA μ n * r ^ n) ∧
      ∑' n, entryLaw P hA μ n * r ^ n ≤ (∫⁻ x, kendallMoment P A (ENNReal.ofReal r) x ∂μ).toReal
    := by
  have hle := tsum_entryLaw_mul_pow_le P hA μ (ENNReal.ofReal r)
  have e : ∀ n, ENNReal.ofReal (entryLaw P hA μ n) * ENNReal.ofReal r ^ n =
      ENNReal.ofReal (entryLaw P hA μ n * r ^ n) := fun n => by
    rw [ENNReal.ofReal_mul (entryLaw_nonneg P hA μ n), ENNReal.ofReal_pow hr]
  simp_rw [e] at hle
  have hne : ∑' n, ENNReal.ofReal (entryLaw P hA μ n * r ^ n) ≠ ∞ := ne_top_of_le_ne_top h hle
  have hnn : ∀ n, 0 ≤ entryLaw P hA μ n * r ^ n := fun n =>
    mul_nonneg (entryLaw_nonneg P hA μ n) (pow_nonneg hr n)
  have hs : Summable (fun n => entryLaw P hA μ n * r ^ n) := by
    have := ENNReal.summable_toReal hne
    exact this.congr fun n => ENNReal.toReal_ofReal (hnn n)
  refine ⟨hs, ?_⟩
  rw [← ENNReal.ofReal_le_iff_le_toReal h, ENNReal.ofReal_tsum_of_nonneg hnn hs]
  exact hle

/-! ### Geometric sums of the taboo kernels -/

/-- **(15.9)**: `Σₙ r^{n+1} ∫ f d(_AP^{n+1}(x, ·)) = U_A^{(r)}(x, f)`. -/
theorem tsum_pow_lintegral_tabooKernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    ∑' n, r ^ (n + 1) * ∫⁻ y, f y ∂tabooKernel P hA n x = geomTaboo P A r f x := by
  rw [geomTaboo, lintegral_sumBefore _ (measurableSet_lt_firstReturn hA)
      (F := fun k (ω : ℕ → X) => r ^ (k + 1) * f (ω (k + 1)))
      fun k => measurable_const.mul (hf.comp (measurable_pi_apply (k + 1)))]
  refine tsum_congr fun n => ?_
  rw [← map_restrict_le_firstReturn P hA n x, lintegral_map hf (measurable_pi_apply (n + 1)),
    ← lintegral_const_mul (f := fun ω : ℕ → X => f (ω (n + 1))) _
      (hf.comp (measurable_pi_apply (n + 1)))]
  congr 1
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  cases h : firstReturn A ω with
  | top => simp
  | coe m =>
    rw [Nat.cast_withTop, WithTop.coe_lt_coe, WithTop.coe_le_coe]
    omega

/-- `Σₙ r^{n+1} ∫ f d(λ_AP^{n+1}) = E_λ[U_A^{(r)}(Φ₀, f)]`. -/
theorem tsum_pow_lintegral_tabooSeq (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) (μ : Measure X) :
    ∑' n, r ^ (n + 1) * ∫⁻ y, f y ∂tabooSeq P hA μ n = ∫⁻ x, geomTaboo P A r f x ∂μ := by
  calc ∑' n, r ^ (n + 1) * ∫⁻ y, f y ∂tabooSeq P hA μ n
      = ∑' n, ∫⁻ x, r ^ (n + 1) * ∫⁻ y, f y ∂tabooKernel P hA n x ∂μ := tsum_congr fun n => by
        rw [tabooSeq, ← lintegral_comp_kernel _ μ hf,
          lintegral_const_mul _ (hf.lintegral_kernel (κ := tabooKernel P hA n))]
    _ = ∫⁻ x, ∑' n, r ^ (n + 1) * ∫⁻ y, f y ∂tabooKernel P hA n x ∂μ :=
        (lintegral_tsum fun n => (measurable_const.mul
          (hf.lintegral_kernel (κ := tabooKernel P hA n))).aemeasurable).symm
    _ = ∫⁻ x, geomTaboo P A r f x ∂μ :=
        lintegral_congr fun x => tsum_pow_lintegral_tabooKernel P hA r hf x

/-! ### The geometric regenerative bound -/

/-- **The geometric regenerative bound** (15.8)–(15.11). Let `α` be an atom, `a ∈ α`, with
`π = π(α) μ°_α` a probability, `L(a, α) = 1`, an aperiodic return-time law, and
`U_α^{(κ)}(a, f) < ∞` for some `κ > 1` (`f ≥ 1`). Then there are `r ∈ (1, κ]` and `R < ∞` such
that for every initial probability `λ`,
`Σₙ r^{n+1} ‖λPⁿ⁺¹ − π‖_f ≤ R ∫ λ(dx) U_α^{(κ)}(x, f)`. -/
theorem tsum_fNorm_le_geom_atom {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα.1 a) (hLa : hitProb P α a = 1)
    (hap : IsAperiodicLaw (entryLaw P hα.1 (Measure.dirac a))) {κ : ℝ≥0∞} (hκ : 1 < κ)
    (hκ' : κ ≠ ∞) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hUa : geomTaboo P α κ f a ≠ ∞) :
    ∃ r : ℝ≥0∞, 1 < r ∧ r ≤ κ ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ (μ : Measure X) [IsProbabilityMeasure μ],
      ∑' n, r ^ (n + 1) * fNorm f ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) π ≤
        R * ∫⁻ x, geomTaboo P α κ f x ∂μ := by
  have := isMarkovKernel_pathKernel P
  set p := entryLaw P hα.1 (Measure.dirac a) with hpdef
  have hp : IsIncrementLaw p := isIncrementLaw_entryLaw P hα.1 hLa
  have hm := meanReturnTime_ne_top_of_rep P hα.1 a hπ
  set c := (π α).toReal with hcdef
  have hc : c = (incrMean p)⁻¹ := by
    rw [hcdef, measure_atom_toReal_of_rep P hα.1 a hπ, incrMean_entryLaw P hα.1 hLa hm]
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  -- Kendall: the return-time law has a geometric moment
  have hκR : 1 < κ.toReal := by
    have := ENNReal.toReal_strict_mono hκ' hκ; rwa [ENNReal.toReal_one] at this
  have hKa : kendallMoment P α κ a ≠ ∞ :=
    ne_top_of_le_ne_top hUa (kendallMoment_le_geomTaboo P α hκ.le hf1 a)
  have hKa' : ∫⁻ x, kendallMoment P α (ENNReal.ofReal κ.toReal) x ∂Measure.dirac a ≠ ∞ := by
    rw [ENNReal.ofReal_toReal hκ']
    exact ne_top_of_le_ne_top hKa (lintegral_dirac_le a _)
  obtain ⟨hsum, -⟩ := summable_entryLaw_mul_pow P hα.1 (Measure.dirac a) (by linarith) hKa'
  obtain ⟨r₁, hr₁, hsum₁⟩ := kendall_geometric_of_moment hp hap hκR hsum
  rw [← atomRenewal_eq_realRenewalSeq hα ha, ← hc] at hsum₁
  set rR := min r₁ κ.toReal with hrR
  have hrR1 : 1 < rR := lt_min hr₁ hκR
  have hrR0 : 0 ≤ rR := by linarith
  have hD : Summable fun n => |atomRenewal P α a n - c| * rR ^ n :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg hrR0 n))
      (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrR0 (min_le_left _ _) n)
        (abs_nonneg _)) hsum₁
  set D := ∑' n, |atomRenewal P α a n - c| * rR ^ n with hDdef
  set r := ENNReal.ofReal rR with hrdef
  have hr1 : 1 < r := by rw [hrdef]; exact ENNReal.one_lt_ofReal.2 hrR1
  have hrt : r ≠ ∞ := ENNReal.ofReal_ne_top
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr1).ne'
  have hrκ : r ≤ κ := ENNReal.ofReal_le_of_le_toReal (min_le_right _ _)
  set Ua := geomTaboo P α κ f a with hUadef
  set t : ℕ → ℝ≥0∞ := fun j => ∫⁻ y, f y ∂tabooKernel P hα.1 j a with htdef
  have ht : ∑' j, r ^ j * t j ≤ Ua := by
    calc ∑' j, r ^ j * t j ≤ ∑' j, r ^ (j + 1) * t j := ENNReal.tsum_le_tsum fun j =>
          mul_le_mul' (pow_le_pow_right₀ hr1.le (Nat.le_succ j)) le_rfl
      _ = geomTaboo P α r f a := tsum_pow_lintegral_tabooKernel P hα.1 r hf a
      _ ≤ Ua := geomTaboo_mono_r P α hrκ f a
  have hinv : r⁻¹ < 1 := ENNReal.inv_lt_one.2 hr1
  set R := 1 + r * (ENNReal.ofReal D + ENNReal.ofReal (c * (rR / (rR - 1)))) * Ua +
    π α * (1 - r⁻¹)⁻¹ * Ua with hRdef
  have hRt : R ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hrt (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩)) hUa⟩, ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top π α)
        (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hinv).ne')) hUa⟩
  refine ⟨r, hr1, hrκ, R, hRt, fun μ _ => ?_⟩
  set Uμ := ∫⁻ x, geomTaboo P α κ f x ∂μ with hUμ
  have hUμ1 : 1 ≤ Uμ := by
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂μ := by rw [lintegral_const, measure_univ, one_mul]
      _ ≤ Uμ := lintegral_mono fun x => le_trans (by
          rw [← (measure_univ (μ := pathKernel P x)), ← lintegral_one]
          exact lintegral_mono fun ω => one_le_tpow hκ.le _)
          (kendallMoment_le_geomTaboo P α hκ.le hf1 x)
  by_cases hUμt : Uμ = ∞
  · have hR0 : R ≠ 0 := (zero_lt_one.trans_le (le_self_add.trans le_self_add)).ne'
    rw [hUμt, ENNReal.mul_top hR0]; exact le_top
  -- the initial law reaches `α` almost surely
  have hKμ : ∫⁻ x, kendallMoment P α r x ∂μ ≤ Uμ := lintegral_mono fun x =>
    (kendallMoment_mono_r P α hrκ x).trans (kendallMoment_le_geomTaboo P α hκ.le hf1 x)
  have hKm := measurable_kendallMoment P hα.1 hr1
  have hL : ∫⁻ x, hitProb P α x ∂μ = 1 := by
    have hae : ∀ᵐ x ∂μ, kendallMoment P α r x < ∞ :=
      ae_lt_top hKm (ne_top_of_le_ne_top hUμt hKμ)
    rw [lintegral_congr_ae (hae.mono fun x hx =>
      hitProb_eq_one_of_kendallMoment_ne_top P hα.1 hx.ne), lintegral_const, measure_univ,
      one_mul]
  have hE := hasSum_entryLaw P hα.1 μ
  rw [hL, ENNReal.toReal_one] at hE
  have hKμ' : ∫⁻ x, kendallMoment P α (ENNReal.ofReal rR) x ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hUμt hKμ
  obtain ⟨har, harle⟩ := summable_entryLaw_mul_pow P hα.1 μ hrR0 hKμ'
  obtain ⟨hws, hwle⟩ := geometric_delayed_bound (entryLaw_nonneg P hα.1 μ) hE hc0 hrR1 har hD
  set A := ∑' n, entryLaw P hα.1 μ n * rR ^ n with hAdef
  have hA0 : 0 ≤ A := tsum_nonneg fun n => mul_nonneg (entryLaw_nonneg P hα.1 μ n)
    (pow_nonneg hrR0 n)
  have hAU : ENNReal.ofReal A ≤ Uμ := by
    rw [ENNReal.ofReal_le_iff_le_toReal hUμt]
    exact harle.trans (ENNReal.toReal_mono hUμt hKμ)
  set w : ℕ → ℝ := fun k => |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - c| with hwdef
  have hW : ∑' k, r ^ k * ENNReal.ofReal (w k) ≤
      Uμ * (ENNReal.ofReal D + ENNReal.ofReal (c * (rR / (rR - 1)))) := by
    have e : ∀ k, r ^ k * ENNReal.ofReal (w k) = ENNReal.ofReal (w k * rR ^ k) := fun k => by
      rw [hrdef, ← ENNReal.ofReal_pow hrR0, ← ENNReal.ofReal_mul (pow_nonneg hrR0 k), mul_comm]
    simp_rw [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (abs_nonneg _) (pow_nonneg hrR0 k))
      hws]
    have hD0 : 0 ≤ D := tsum_nonneg fun n => mul_nonneg (abs_nonneg _) (pow_nonneg hrR0 n)
    have hq0 : 0 ≤ c * (rR / (rR - 1)) := mul_nonneg hc0 (div_nonneg hrR0 (by linarith))
    calc ENNReal.ofReal (∑' k, w k * rR ^ k) ≤ ENNReal.ofReal (A * D + c * (rR / (rR - 1) * A)) :=
          ENNReal.ofReal_le_ofReal hwle
      _ = ENNReal.ofReal A * (ENNReal.ofReal D + ENNReal.ofReal (c * (rR / (rR - 1)))) := by
          rw [← ENNReal.ofReal_add hD0 hq0, ← ENNReal.ofReal_mul hA0]; ring_nf
      _ ≤ Uμ * (ENNReal.ofReal D + ENNReal.ofReal (c * (rR / (rR - 1)))) :=
          mul_le_mul' hAU le_rfl
  -- the three sums
  have hbd := fun n => fNorm_comp_pow_succ_le hα ha hπ μ n f
  have hsumA : ∑' n, r ^ (n + 1) * ∫⁻ y, f y ∂tabooSeq P hα.1 μ n ≤ Uμ := by
    rw [tsum_pow_lintegral_tabooSeq P hα.1 r hf μ]
    exact lintegral_mono fun x => geomTaboo_mono_r P α hrκ f x
  have hsumB : ∑' n, r ^ (n + 1) * ∑ k ∈ range (n + 1), ENNReal.ofReal (w k) * t (n - k) =
      r * ((∑' k, r ^ k * ENNReal.ofReal (w k)) * ∑' j, r ^ j * t j) := by
    rw [← tsum_sum_range_mul, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    calc r ^ (n + 1) * (ENNReal.ofReal (w k) * t (n - k))
        = r * (r ^ k * r ^ (n - k)) * (ENNReal.ofReal (w k) * t (n - k)) := by
          rw [← pow_add, Nat.add_sub_cancel' hkn, pow_succ, mul_comm (r ^ n)]
      _ = r * (r ^ k * ENNReal.ofReal (w k) * (r ^ (n - k) * t (n - k))) := by ring
  have hsumC : ∑' n, r ^ (n + 1) * (π α * ∑' i, t (i + n + 1)) ≤ π α * (1 - r⁻¹)⁻¹ * Ua := by
    have e : ∀ n i, r⁻¹ ^ i * (r ^ (i + n + 1) * t (i + n + 1)) = r ^ (n + 1) * t (i + n + 1) :=
      fun n i => by
      rw [← mul_assoc, ← ENNReal.inv_pow, show i + n + 1 = i + (n + 1) by ring, pow_add,
        ← mul_assoc, ENNReal.inv_mul_cancel (pow_ne_zero _ hr0) (ENNReal.pow_ne_top hrt), one_mul]
    calc ∑' n, r ^ (n + 1) * (π α * ∑' i, t (i + n + 1))
        = π α * ∑' n, ∑' i, r⁻¹ ^ i * (r ^ (i + n + 1) * t (i + n + 1)) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun n => ?_
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun i => ?_
          rw [e n i]; ring
      _ = π α * ∑' i, r⁻¹ ^ i * ∑' n, r ^ (i + n + 1) * t (i + n + 1) := by
          rw [ENNReal.tsum_comm]
          simp_rw [ENNReal.tsum_mul_left]
      _ ≤ π α * ∑' i, r⁻¹ ^ i * ∑' j, r ^ j * t j := by
          refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun i => mul_le_mul' le_rfl ?_)
          exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun n => i + n + 1)
            (fun m n hmn => by simpa using hmn) (fun j => r ^ j * t j)
      _ ≤ π α * (1 - r⁻¹)⁻¹ * Ua := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_assoc]
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl ht)
  calc ∑' n, r ^ (n + 1) * fNorm f ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) π
      ≤ ∑' n, (r ^ (n + 1) * ∫⁻ y, f y ∂tabooSeq P hα.1 μ n +
          r ^ (n + 1) * ∑ k ∈ range (n + 1), ENNReal.ofReal (w k) * t (n - k) +
          r ^ (n + 1) * (π α * ∑' i, t (i + n + 1))) := ENNReal.tsum_le_tsum fun n => by
        rw [← mul_add, ← mul_add]
        exact mul_le_mul' le_rfl (hbd n)
    _ = ∑' n, r ^ (n + 1) * ∫⁻ y, f y ∂tabooSeq P hα.1 μ n +
          ∑' n, r ^ (n + 1) * ∑ k ∈ range (n + 1), ENNReal.ofReal (w k) * t (n - k) +
          ∑' n, r ^ (n + 1) * (π α * ∑' i, t (i + n + 1)) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ Uμ + r * (Uμ * (ENNReal.ofReal D + ENNReal.ofReal (c * (rR / (rR - 1)))) * Ua) +
          π α * (1 - r⁻¹)⁻¹ * Ua := by
        refine add_le_add (add_le_add hsumA ?_) hsumC
        rw [hsumB]
        exact mul_le_mul' le_rfl (mul_le_mul' hW ht)
    _ ≤ R * Uμ := by
        rw [hRdef, add_mul, add_mul, one_mul]
        refine add_le_add (add_le_add le_rfl (le_of_eq (by ring))) ?_
        exact le_mul_of_one_le_right' hUμ1

/-! ### Kendall atoms and geometrically ergodic atoms -/

/-- An atom is **geometrically ergodic** (MT p. 368): `Σₙ r_αⁿ |Pⁿ(α, α) − π(α)| < ∞` for some
`r_α > 1`. -/
def IsGeomErgodicAtom (P : Kernel X X) (π : Measure X) (α : Set X) : Prop :=
  ∃ r : ℝ, 1 < r ∧ ∀ a ∈ α, Summable fun n => |atomRenewal P α a n - (π α).toReal| * r ^ n

/-- On an atom, `U_α^{(r)}(y, f)` does not depend on `y ∈ α`. -/
theorem IsAtom.geomTaboo_const {P : Kernel X X} [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) {x y : X} (hx : x ∈ α) (hy : y ∈ α) :
    geomTaboo P α r f x = geomTaboo P α r f y := by
  obtain ⟨hm, ν, hν⟩ := hα
  rw [geomTaboo_eq P hm r hf, geomTaboo_eq P hm r hf, hν x hx, hν y hy]

/-- On an atom, `Pⁿ(y, α)` does not depend on `y ∈ α`. -/
theorem IsAtom.atomRenewal_eq {P : Kernel X X} {α : Set X} (hα : IsAtom P α) {a b : X}
    (ha : a ∈ α) (hb : b ∈ α) (n : ℕ) : atomRenewal P α a n = atomRenewal P α b n := by
  cases n with
  | zero => rw [atomRenewal_zero P hα.1 ha, atomRenewal_zero P hα.1 hb]
  | succ n => rw [atomRenewal, atomRenewal, hα.pow_succ_eq ha hb n]

/-- When `L(x, A) = 1`, `E_x[r^{τ_A}] = Σₙ r^{n+1} P_x(τ_A = n + 1)`. -/
theorem kendallMoment_eq_tsum (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (r : ℝ≥0∞) {x : X} (hL : hitProb P A x = 1) :
    kendallMoment P A r x = ∑' n, r ^ (n + 1) * tabooKernel P hA n x A := by
  have := isMarkovKernel_pathKernel P
  refine le_antisymm ?_ (tsum_pow_tabooKernel_le_kendallMoment P hA r x)
  have hm : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | firstReturn A ω = WithTop.some (n + 1)} :=
    fun n => (natFilt (X := X)).le (n + 1) _
      ((proposition_3_4_4 hA).1.measurableSet_eq_of_countable (n + 1))
  have hS := measurableSet_ne_top (proposition_3_4_4 hA).1 (X := X)
  have h1 : pathKernel P x {ω | firstReturn A ω ≠ ⊤}ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff hS]; exact hL
  have hae : ∀ᵐ ω ∂pathKernel P x, firstReturn A ω ≠ ⊤ :=
    ae_iff.2 (by rw [← compl_ofPred]; exact h1)
  calc kendallMoment P A r x
      ≤ ∫⁻ ω, ∑' n, {ω | firstReturn A ω = WithTop.some (n + 1)}.indicator
          (fun _ => r ^ (n + 1)) ω ∂pathKernel P x := lintegral_mono_ae (hae.mono fun ω hω => by
        obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
        have ht1 : 1 ≤ t := by
          have := one_le_firstReturn A ω; rw [← ht] at this; exact WithTop.coe_le_coe.1 this
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (t - 1))
        rw [indicator_of_mem (show ω ∈ {ω | firstReturn A ω = WithTop.some (t - 1 + 1)} from by
          change firstReturn A ω = WithTop.some (t - 1 + 1)
          rw [← ht, Nat.sub_add_cancel ht1]), ← ht, Nat.sub_add_cancel ht1]
        rfl)
    _ = ∑' n, r ^ (n + 1) * tabooKernel P hA n x A := by
        rw [lintegral_tsum fun n => (measurable_const.indicator (hm n)).aemeasurable]
        refine tsum_congr fun n => ?_
        rw [lintegral_indicator_const (hm n), firstReturn_eq_tabooKernel]

/-- `U_A^{(r)}(x, 1) ≤ r (r − 1)⁻¹ E_x[r^{τ_A}]` for `1 < r < ∞`. -/
theorem geomTaboo_one_le_kendallMoment (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {r : ℝ≥0∞} (hr : 1 < r) (hrt : r ≠ ∞) (x : X) :
    geomTaboo P A r (fun _ => 1) x ≤ r * (r - 1)⁻¹ * kendallMoment P A r x := by
  have hr1 : r - 1 ≠ 0 := (tsub_pos_iff_lt.2 hr).ne'
  have hr1t : r - 1 ≠ ∞ := ENNReal.sub_ne_top hrt
  have hpt : ∀ ω : ℕ → X, sumBefore (firstReturn A) (fun k ω => r ^ (k + 1) * 1) ω ≤
      r * (r - 1)⁻¹ * tpow r (firstReturn A ω) := fun ω => by
    have e : sumBefore (firstReturn A) (fun k (ω : ℕ → X) => r ^ (k + 1) * 1) ω =
        r * sumBefore (firstReturn A) (fun k _ => r ^ k) ω := by
      rw [← sumBefore_const_mul]; exact sumBefore_congr _ fun k _ => by rw [pow_succ]; ring
    rw [e, mul_assoc]
    refine mul_le_mul' le_rfl ?_
    rw [tpow_eq_one_add hr, ← sumBefore_eq_tsum (firstReturn A) (fun k _ => r ^ k) ω]
    calc sumBefore (firstReturn A) (fun k _ => r ^ k) ω
        = (r - 1)⁻¹ * ((r - 1) * sumBefore (firstReturn A) (fun k _ => r ^ k) ω) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hr1 hr1t, one_mul]
      _ ≤ (r - 1)⁻¹ * (1 + (r - 1) * sumBefore (firstReturn A) (fun k _ => r ^ k) ω) :=
          mul_le_mul' le_rfl le_add_self
  rw [geomTaboo, kendallMoment, ← lintegral_const_mul _
    (measurable_tpow_comp (measurableSet_lt_firstReturn hA) hr)]
  exact lintegral_mono hpt

/-- **The atom data of a positive chain**: for an accessible atom `α ∋ a` and an invariant
probability `π`, `π = π(α) μ°_α` and `L(a, α) = 1`. -/
theorem atom_rep_of_invariant {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (h : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) : π = π α • atomMeasure P h.1.1 a ∧ hitProb P α a = 1 := by
  have hrec := proposition_10_1_1 (P := P) ⟨h.2.1, π, inferInstance, hπ⟩
  exact ⟨eq_smul_atomMeasure_of_accessible h hrec ha hπ, (h.isRecurrentChain_iff ha).1 hrec⟩

/-! ### Proposition 15.1.2 -/

/-- **Proposition 15.1.2** (MT p. 369), the Markov chain part: for a `ψ`-irreducible aperiodic
chain with invariant probability `π` and an accessible Kendall atom `α`, there are `ρ < 1`
(`r_α = ρ⁻¹ > 1`) and `R` with `|Pⁿ(α, α) − π(α)| ≤ R ρⁿ` for all `n`. The renewal part is
`kendall_geometric_bound`. -/
theorem proposition_15_1_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hap : IsAperiodic P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α) {κ : ℝ≥0∞}
    (hK : IsKendall P α κ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∃ R : ℝ, ∀ a ∈ α, ∀ n,
      |((P ^ n : Kernel X X) a α).toReal - (π α).toReal| ≤ R * ρ ^ n := by
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero h.2.2.ne'
  obtain ⟨hrep, hLa⟩ := atom_rep_of_invariant h ha hπ
  obtain ⟨-, hκ, hκ', M, hM, hb⟩ := hK
  set p := entryLaw P h.1.1 (Measure.dirac a)
  have hp : IsIncrementLaw p := isIncrementLaw_entryLaw P h.1.1 hLa
  have hap' := isAperiodicLaw_entryLaw h hap ha
  have hκR : 1 < κ.toReal := by
    have := ENNReal.toReal_strict_mono hκ' hκ; rwa [ENNReal.toReal_one] at this
  have hKa' : ∫⁻ x, kendallMoment P α (ENNReal.ofReal κ.toReal) x ∂Measure.dirac a ≠ ∞ := by
    rw [ENNReal.ofReal_toReal hκ']
    exact ne_top_of_le_ne_top hM ((lintegral_dirac_le a _).trans (hb a ha))
  obtain ⟨hsum, -⟩ := summable_entryLaw_mul_pow P h.1.1 (Measure.dirac a) (by linarith) hKa'
  obtain ⟨ρ, hρ0, hρ1, R, hR⟩ := kendall_geometric_bound hp hap' hκR hsum
  have hm := meanReturnTime_ne_top_of_rep P h.1.1 a hrep
  have hc : (π α).toReal = (incrMean p)⁻¹ := by
    rw [measure_atom_toReal_of_rep P h.1.1 a hrep, incrMean_entryLaw P h.1.1 hLa hm]
  refine ⟨ρ, hρ0, hρ1, R, fun b hb n => ?_⟩
  have e := h.1.atomRenewal_eq hb ha n
  change |atomRenewal P α b n - (π α).toReal| ≤ R * ρ ^ n
  rw [e, atomRenewal_eq_realRenewalSeq h.1 ha, hc]
  exact hR n

/-! ### Proposition 15.1.3 -/

/-- **The identity in the proof of Proposition 15.1.3**, corrected (MT p. 369): for an atom `α ∋ a`
and `κ ∈ (0, ∞)`, `P U_α^{(κ)}(x, f) + P f(x) = κ⁻¹ U_α^{(κ)}(x, f) + P(x, α) U_α^{(κ)}(a, f)`. -/
theorem proposition_15_1_3_identity {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκt : κ ≠ ∞)
    {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    ∫⁻ y, geomTaboo P α κ f y ∂P x + ∫⁻ y, f y ∂P x =
      κ⁻¹ * geomTaboo P α κ f x + P x α * geomTaboo P α κ f a := by
  have hUm := measurable_geomTaboo P hα.1 κ hf
  set U := geomTaboo P α κ f with hU
  have hsplit : ∀ y, U y = α.indicator (fun _ => U a) y + αᶜ.indicator U y := fun y => by
    by_cases hy : y ∈ α
    · rw [indicator_of_mem hy, indicator_of_notMem (show y ∉ αᶜ from fun h => h hy), add_zero]
      exact hα.geomTaboo_const κ hf hy ha
    · rw [indicator_of_notMem hy, indicator_of_mem (show y ∈ αᶜ from hy), zero_add]
  have hG : ∀ y, αᶜ.indicator U y + f y = geomG P α κ f y := fun y => by
    rw [geomG_eq P hα.1 κ hf, add_comm]
  have hPG : ∫⁻ y, geomG P α κ f y ∂P x = κ⁻¹ * U x := by
    rw [hU, geomTaboo_eq P hα.1 κ hf, ← mul_assoc, ENNReal.inv_mul_cancel hκ0 hκt, one_mul]
  calc ∫⁻ y, U y ∂P x + ∫⁻ y, f y ∂P x
      = ∫⁻ y, α.indicator (fun _ => U a) y ∂P x + (∫⁻ y, αᶜ.indicator U y ∂P x +
          ∫⁻ y, f y ∂P x) := by
        rw [lintegral_congr hsplit, lintegral_add_left (measurable_const.indicator hα.1),
          add_assoc]
    _ = U a * P x α + ∫⁻ y, geomG P α κ f y ∂P x := by
        rw [lintegral_indicator_const hα.1, ← lintegral_add_left (hUm.indicator hα.1.compl)]
        simp_rw [hG]
    _ = κ⁻¹ * U x + P x α * U a := by rw [hPG]; ring

/-- **The counterexample to the identity printed in the proof of Proposition 15.1.3**
(`P U_α^{(κ)} = κ⁻¹ U_α^{(κ)} + P(·, α) U_α^{(κ)}(α, ·)`, without `−P`): on the one-point space,
with `α = X`, `κ = 2` and `f = 1`, the left side is `2` and the right side is `3`. -/
theorem proposition_15_1_3_counterexample :
    ∫⁻ y, geomTaboo (Kernel.const Unit (Measure.dirac ())) univ 2 (fun _ => 1) y
        ∂(Kernel.const Unit (Measure.dirac ())) () ≠
      2⁻¹ * geomTaboo (Kernel.const Unit (Measure.dirac ())) univ 2 (fun _ => 1) () +
        (Kernel.const Unit (Measure.dirac ())) () univ *
          geomTaboo (Kernel.const Unit (Measure.dirac ())) univ 2 (fun _ => 1) () := by
  have hU : ∀ y, geomTaboo (Kernel.const Unit (Measure.dirac ())) univ 2 (fun _ => 1) y = 2 :=
    fun y => by
    have := isMarkovKernel_pathKernel (Kernel.const Unit (Measure.dirac ()))
    have h1 : ∀ ω : ℕ → Unit, firstReturn univ ω = ((1 : ℕ) : WithTop ℕ) := fun ω =>
      (firstReturn_eq_iff univ ω 0).2 ⟨one_le_firstReturn univ ω, mem_univ _⟩
    rw [geomTaboo, lintegral_congr fun ω => sumBefore_of_eq' (h1 ω)]
    simp
  simp only [hU]
  rw [lintegral_const, measure_univ, mul_one, one_mul,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  norm_num

/-- **`U_α^{(κ)}(·, f) < ∞` is absorbing** for an atom with `U_α^{(κ)}(a, f) < ∞`. -/
theorem isAbsorbing_geomTaboo_finite {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκt : κ ≠ ∞)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hUa : geomTaboo P α κ f a ≠ ∞) :
    IsAbsorbing P {x | geomTaboo P α κ f x ≠ ∞} := by
  intro x hx
  have hUm := measurable_geomTaboo P hα.1 κ hf
  have hPU : ∫⁻ y, geomTaboo P α κ f y ∂P x ≠ ∞ := by
    have h := proposition_15_1_3_identity hα ha hκ0 hκt hf x
    refine ne_top_of_le_ne_top ?_ (le_self_add.trans (le_of_eq h))
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hκ0) hx,
      ENNReal.mul_ne_top (measure_ne_top _ _) hUa⟩
  have hae := ae_lt_top hUm hPU
  have hm : MeasurableSet {y | geomTaboo P α κ f y ≠ ∞} :=
    (measurableSet_singleton ∞).compl.preimage hUm
  have h0 : P x {y | geomTaboo P α κ f y ≠ ∞}ᶜ = 0 := by
    have h1 : P x {y | ¬ geomTaboo P α κ f y < ∞} = 0 := ae_iff.1 hae
    have h2 : {y | geomTaboo P α κ f y ≠ ∞}ᶜ = {y | ¬ geomTaboo P α κ f y < ∞} := by
      ext y; simp [lt_top_iff_ne_top]
    rw [h2, h1]
  exact (prob_compl_eq_zero_iff hm).1 h0

/-- **Proposition 15.1.3** (MT p. 369): for a `φ`-irreducible chain with an `f`-Kendall atom `α` of
rate `κ` (`f ≥ 1`), the set `S_f^κ = {x : U_α^{(κ)}(x, f) < ∞}` is full and absorbing. -/
theorem proposition_15_1_3 {P : Kernel X X} [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {α : Set X} (hα : IsAtom P α) (hne : α.Nonempty)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {κ : ℝ≥0∞}
    (hK : IsFKendall P f α κ) :
    IsFull φ {x | geomTaboo P α κ f x ≠ ∞} ∧ IsAbsorbing P {x | geomTaboo P α κ f x ≠ ∞} := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨hm, hκ, hκ', M, hM, hb⟩ := hK
  obtain ⟨-, -, hU⟩ := fKendall_bounds P hm hκ hf hf1 hb
  have hUa : geomTaboo P α κ f a ≠ ∞ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hM,
    ENNReal.mul_ne_top hM (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top (ENNReal.sub_ne_top hκ') hM⟩)⟩) (hU a ha)
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hκ).ne'
  have habs := isAbsorbing_geomTaboo_finite hα ha hκ0 hκ' hf hUa
  exact ⟨proposition_4_2_3_i hφ ((measurableSet_singleton ∞).compl.preimage
    (measurable_geomTaboo P hm κ hf)) ⟨a, hUa⟩ habs, habs⟩

/-! ### Theorems 15.1.4 and 15.1.5 -/

/-- **Theorem 15.1.4** (MT p. 369), corrected: for a `ψ`-irreducible **aperiodic** chain with
invariant probability `π` and an accessible `f`-Kendall atom `α` of rate `κ` (`f ≥ 1`), the set
`S^κ = {U_α^{(κ)}(·, f) < ∞}` is full and absorbing, and for some `r > 1`, `R < ∞`,
`Σ_{n ≥ 1} rⁿ ‖Pⁿ(x, ·) − π‖_f ≤ R U_α^{(κ)}(x, f)` for every `x` (15.18). -/
theorem theorem_15_1_4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hap : IsAperiodic P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {κ : ℝ≥0∞} (hK : IsFKendall P f α κ) :
    IsFull ψ {x | geomTaboo P α κ f x ≠ ∞} ∧ IsAbsorbing P {x | geomTaboo P α κ f x ≠ ∞} ∧
      ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
        ∑' n, r ^ (n + 1) * fNorm f ((P ^ (n + 1) : Kernel X X) x) π ≤
          R * geomTaboo P α κ f x := by
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero h.2.2.ne'
  obtain ⟨hrep, hLa⟩ := atom_rep_of_invariant h ha hπ
  obtain ⟨hfull, habs⟩ := proposition_15_1_3 h.2.1.2.1 h.1 ⟨a, ha⟩ hf hf1 hK
  obtain ⟨hm, hκ, hκ', M, hM, hb⟩ := hK
  obtain ⟨-, -, hU⟩ := fKendall_bounds P hm hκ hf hf1 hb
  have hUa : geomTaboo P α κ f a ≠ ∞ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hM,
    ENNReal.mul_ne_top hM (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top (ENNReal.sub_ne_top hκ') hM⟩)⟩) (hU a ha)
  obtain ⟨r, hr, -, R, hR, hbd⟩ := tsum_fNorm_le_geom_atom h.1 ha hrep hLa
    (isAperiodicLaw_entryLaw h hap ha) hκ hκ' hf hf1 hUa
  refine ⟨hfull, habs, r, hr, R, hR, fun x => ?_⟩
  have h1 := hbd (Measure.dirac x)
  simp_rw [dirac_kernel] at h1
  exact h1.trans (mul_le_mul' le_rfl (lintegral_dirac_le x _))

/-- **A renewal sequence with a positive limit has an aperiodic increment law**: if
`Pⁿ(a, α) → c > 0`, the return-time law of `α` is aperiodic. -/
theorem isAperiodicLaw_of_tendsto_pos {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (atomRenewal P α a) atTop (𝓝 c)) :
    IsAperiodicLaw (entryLaw P hα.1 (Measure.dirac a)) := by
  intro d hd
  have hdvd := dvd_of_atomRenewal_pos hα ha hd
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hlim).1 0 hc).exists_forall_of_atTop
  have h1 := hdvd N (hN N le_rfl)
  have h2 := hdvd (N + 1) (hN (N + 1) (Nat.le_succ N))
  exact Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 h2)

/-- **Theorem 15.1.5** (MT p. 370), whose proof the book omits: for a `ψ`-irreducible chain with
invariant probability `π` and a geometrically ergodic accessible atom `α`, there are `κ > 1`,
`r > 1` and `R < ∞` such that `S^κ = {E_·[κ^{τ_α}] < ∞}` is full and absorbing and
`Σ_{n ≥ 1} rⁿ ‖Pⁿ(x, ·) − π‖ ≤ R E_x[κ^{τ_α}]` for every `x` (15.19), in the total variation norm
`‖·‖_1`. Aperiodicity is not assumed: it follows from `Pⁿ(α, α) → π(α) > 0`. -/
theorem theorem_15_1_5 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (h : IsAccessibleAtom P ψ α) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hge : IsGeomErgodicAtom P π α) :
    ∃ κ : ℝ≥0∞, 1 < κ ∧ κ ≠ ∞ ∧ IsFull ψ {x | kendallMoment P α κ x ≠ ∞} ∧
      IsAbsorbing P {x | kendallMoment P α κ x ≠ ∞} ∧
      ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
        ∑' n, r ^ (n + 1) * fNorm (fun _ => 1) ((P ^ (n + 1) : Kernel X X) x) π ≤
          R * kendallMoment P α κ x := by
  have := isMarkovKernel_pathKernel P
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero h.2.2.ne'
  obtain ⟨hrep, hLa⟩ := atom_rep_of_invariant h ha hπ
  obtain ⟨rg, hrg, hsum⟩ := hge
  set p := entryLaw P h.1.1 (Measure.dirac a)
  have hp : IsIncrementLaw p := isIncrementLaw_entryLaw P h.1.1 hLa
  have hm := meanReturnTime_ne_top_of_rep P h.1.1 a hrep
  have hc : (π α).toReal = (incrMean p)⁻¹ := by
    rw [measure_atom_toReal_of_rep P h.1.1 a hrep, incrMean_entryLaw P h.1.1 hLa hm]
  have hsum' : Summable fun n => |realRenewalSeq p n - (incrMean p)⁻¹| * rg ^ n := by
    have := hsum a ha
    rwa [atomRenewal_eq_realRenewalSeq h.1 ha, hc] at this
  obtain ⟨κR, hκR, hκsum⟩ := kendall_moment_of_geometric hp hrg hsum'
  -- the atom is Kendall of rate `κ`
  set κ := ENNReal.ofReal κR with hκdef
  have hκ : 1 < κ := ENNReal.one_lt_ofReal.2 hκR
  have hκt : κ ≠ ∞ := ENNReal.ofReal_ne_top
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hκ).ne'
  have hKa : kendallMoment P α κ a ≠ ∞ := by
    rw [kendallMoment_eq_tsum P h.1.1 κ hLa]
    have e : ∀ n, κ ^ (n + 1) * tabooKernel P h.1.1 n a α =
        ENNReal.ofReal (p (n + 1) * κR ^ (n + 1)) := fun n => by
      have hfin : tabooKernel P h.1.1 n a α ≠ ∞ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (tabooKernel_apply_le_one P h.1.1 n a α)
      rw [ENNReal.ofReal_mul (entryLaw_nonneg P h.1.1 _ _), entryLaw_dirac_succ,
        ENNReal.ofReal_toReal hfin, ENNReal.ofReal_pow (by linarith), mul_comm]
    simp_rw [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (entryLaw_nonneg P h.1.1 _ _)
      (pow_nonneg (by linarith) _)) ((summable_nat_add_iff 1).2 hκsum)]
    exact ENNReal.ofReal_ne_top
  have hUa : geomTaboo P α κ (fun _ => 1) a ≠ ∞ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hκt (ENNReal.inv_ne_top.2
      (tsub_pos_iff_lt.2 hκ).ne')) hKa) (geomTaboo_one_le_kendallMoment P h.1.1 hκ hκt a)
  -- aperiodicity from the positive limit
  have hlim : Tendsto (atomRenewal P α a) atTop (𝓝 (π α).toReal) := by
    have h0 : Tendsto (fun n => |atomRenewal P α a n - (π α).toReal| * rg ^ n) atTop (𝓝 0) :=
      (hsum a ha).tendsto_atTop_zero
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun n => ?_) h0)
    rw [Real.norm_eq_abs]
    exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ hrg.le)
  have hπα : 0 < (π α).toReal := ENNReal.toReal_pos
    (measure_atom_ne_zero_of_rep P h.1.1 a hrep) (measure_ne_top π α)
  have hap := isAperiodicLaw_of_tendsto_pos h.1 ha hπα hlim
  obtain ⟨r, hr, -, R, hR, hbd⟩ := tsum_fNorm_le_geom_atom h.1 ha hrep hLa hap hκ hκt
    measurable_const (fun _ => le_rfl) hUa
  -- the set where the Kendall moment is finite
  have hset : {x | kendallMoment P α κ x ≠ ∞} = {x | geomTaboo P α κ (fun _ => 1) x ≠ ∞} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor
    · intro hx
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hκt (ENNReal.inv_ne_top.2
        (tsub_pos_iff_lt.2 hκ).ne')) hx) (geomTaboo_one_le_kendallMoment P h.1.1 hκ hκt x)
    · intro hx
      exact ne_top_of_le_ne_top hx (kendallMoment_le_geomTaboo P α hκ.le (fun _ => le_rfl) x)
  have habs := isAbsorbing_geomTaboo_finite h.1 ha hκ0 hκt measurable_const hUa
  set c := κ * (κ - 1)⁻¹ with hcdef
  refine ⟨κ, hκ, hκt, ?_, ?_, r, hr, R * c, ENNReal.mul_ne_top hR (ENNReal.mul_ne_top hκt
    (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hκ).ne')), fun x => ?_⟩
  · rw [hset]
    exact proposition_4_2_3_i h.2.1.2.1 ((measurableSet_singleton ∞).compl.preimage
      (measurable_geomTaboo P h.1.1 κ measurable_const)) ⟨a, hUa⟩ habs
  · rw [hset]; exact habs
  · have h1 := hbd (Measure.dirac x)
    simp_rw [dirac_kernel] at h1
    calc ∑' n, r ^ (n + 1) * fNorm (fun _ => 1) ((P ^ (n + 1) : Kernel X X) x) π
        ≤ R * ∫⁻ y, geomTaboo P α κ (fun _ => 1) y ∂Measure.dirac x := h1
      _ ≤ R * (c * kendallMoment P α κ x) := mul_le_mul' le_rfl ((lintegral_dirac_le x _).trans
          (geomTaboo_one_le_kendallMoment P h.1.1 hκ hκt x))
      _ = R * c * kendallMoment P α κ x := by ring

/-! ### The counterexample to Theorem 15.1.4 without aperiodicity -/

/-- The period-`2` **flip chain** on `Bool`: `P(x, ·) = δ_{¬x}`. -/
noncomputable def flipKernel : Kernel Bool Bool :=
  ⟨fun x => Measure.dirac (!x), measurable_of_countable _⟩

/-- `P(x, ·) = δ_{¬x}`. -/
theorem flipKernel_apply (x : Bool) : flipKernel x = Measure.dirac (!x) := rfl

/-- The flip chain is a transition kernel. -/
theorem isMarkovKernel_flipKernel : IsMarkovKernel flipKernel :=
  ⟨fun x => by rw [flipKernel_apply]; infer_instance⟩

/-- Every `Pⁿ(x, ·)` is a point mass. -/
theorem flipKernel_pow (n : ℕ) (x : Bool) : ∃ y, (flipKernel ^ n) x = Measure.dirac y := by
  induction n generalizing x with
  | zero => exact ⟨x, pow_zero_apply flipKernel x⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih (!x)
    refine ⟨y, ?_⟩
    rw [pow_succ]
    change ((flipKernel ^ n) ∘ₖ flipKernel) x = _
    rw [Kernel.comp_apply, flipKernel_apply, Measure.dirac_bind (Kernel.measurable _), hy]

/-- The uniform law `π = (δ_true + δ_false)/2`, invariant for the flip chain. -/
noncomputable def flipPi : Measure Bool := (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

/-- `π` is a probability. -/
theorem isProbabilityMeasure_flipPi : IsProbabilityMeasure flipPi := by
  refine ⟨?_⟩
  rw [flipPi, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- `π` is invariant for the flip chain. -/
theorem isInvariant_flipPi : IsInvariant flipKernel flipPi := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), flipPi, lintegral_smul_measure,
    lintegral_add_measure, lintegral_dirac, lintegral_dirac, flipKernel_apply, flipKernel_apply,
    Measure.smul_apply, Measure.add_apply, smul_eq_mul, add_comm]
  rfl

/-- `‖δ_y − π‖_1 ≥ 1/2` for every `y`. -/
theorem half_le_fNorm_flip (y : Bool) :
    2⁻¹ ≤ fNorm (fun _ => 1) (Measure.dirac y) flipPi := by
  have := isProbabilityMeasure_flipPi
  set g : Bool → ℝ := ({y} : Set Bool).indicator 1 with hg
  have hgt : IsFTest (fun _ => 1) (Measure.dirac y) flipPi g := by
    refine ⟨measurable_of_countable _, fun x => ?_, Integrable.of_finite, Integrable.of_finite⟩
    by_cases hx : x ∈ ({y} : Set Bool)
    · rw [hg, indicator_of_mem hx, Pi.one_apply, abs_one, ENNReal.ofReal_one]
    · rw [hg, indicator_of_notMem hx, abs_zero, ENNReal.ofReal_zero]; exact zero_le
  refine le_trans (le_of_eq ?_) (ofReal_abs_integral_sub_le_fNorm hgt)
  have h1 : ∫ x, g x ∂Measure.dirac y = 1 := by
    rw [integral_dirac]; simp [hg]
  have h2 : ∫ x, g x ∂flipPi = 2⁻¹ := by
    rw [flipPi, integral_smul_measure, integral_add_measure Integrable.of_finite
      Integrable.of_finite, integral_dirac, integral_dirac]
    cases y <;> simp [hg]
  rw [h1, h2, show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, abs_of_pos (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- **The counterexample to Theorem 15.1.4 without aperiodicity.** For the flip chain on `Bool`
(irreducible, period `2`), `{true}` is an accessible atom which is `1`-Kendall of rate `2`,
`π = (δ_true + δ_false)/2` is an invariant probability and `U_{true}^{(2)}(true, 1) = 6 < ∞`, but
`Σₙ rⁿ⁺¹ ‖Pⁿ⁺¹(true, ·) − π‖ = ∞` for every `r ≥ 1`. -/
theorem theorem_15_1_4_counterexample :
    haveI := isMarkovKernel_flipKernel
    IsAccessibleAtom flipKernel Measure.count {true} ∧
      IsFKendall flipKernel (fun _ => 1) {true} 2 ∧ IsInvariant flipKernel flipPi ∧
      geomTaboo flipKernel {true} 2 (fun _ => 1) true = 6 ∧
      ∀ r : ℝ≥0∞, 1 ≤ r →
        ∑' n, r ^ (n + 1) * fNorm (fun _ => 1) ((flipKernel ^ (n + 1) : Kernel Bool Bool) true)
          flipPi = ∞ := by
  have := isMarkovKernel_flipKernel
  have hm : MeasurableSet ({true} : Set Bool) := measurableSet_singleton true
  have hU : ∀ x, geomTaboo flipKernel {true} 2 (fun _ => 1) x =
      if x = true then 6 else 2 := fun x => by
    have hGt : geomG flipKernel {true} 2 (fun _ => 1) true = 1 :=
      geomG_of_mem flipKernel hm 2 measurable_const rfl
    have hUf : geomTaboo flipKernel {true} 2 (fun _ => 1) false = 2 := by
      rw [geomTaboo_eq flipKernel hm 2 measurable_const, flipKernel_apply,
        lintegral_dirac' _ (measurable_of_countable _)]
      simp [hGt]
    cases x
    · simpa using hUf
    · rw [geomTaboo_eq flipKernel hm 2 measurable_const, flipKernel_apply, Bool.not_true,
        lintegral_dirac' _ (measurable_of_countable _), geomG_eq flipKernel hm 2 measurable_const,
        indicator_of_mem (show false ∈ ({true} : Set Bool)ᶜ from by simp), hUf]
      norm_num
  have hirr : IsIrreducibleChain flipKernel := by
    have hleads : ∀ x y : Bool, Leads flipKernel x y := fun x y => by
      by_cases hxy : x = y
      · exact Or.inl hxy
      · refine (leads_iff_exists_pow flipKernel x y).2 ⟨1, ?_⟩
        have hy : y = !x := by cases x <;> cases y <;> simp_all
        rw [pow_one, flipKernel_apply, hy, Measure.dirac_apply_of_mem (mem_singleton _)]
        exact one_pos
    exact ⟨true, eq_univ_of_forall fun y => ⟨hleads true y, hleads y true⟩⟩
  refine ⟨⟨isAtom_singleton _ true, isMaximalIrreducibility_count _ hirr, by simp⟩,
    ⟨hm, by norm_num, ENNReal.ofNat_ne_top, 7, by norm_num, fun x hx => ?_⟩, isInvariant_flipPi,
    by simp [hU], fun r hr => ?_⟩
  · rw [show x = true from hx]
    calc geomSum flipKernel {true} 2 (fun _ => 1) true ≤
          1 + geomTaboo flipKernel {true} 2 (fun _ => 1) true :=
          geomSum_le_add_geomTaboo flipKernel {true} 2 measurable_const true
      _ = 7 := by rw [hU]; norm_num
  · refine top_le_iff.1 ?_
    calc ∞ = ∑' _ : ℕ, (2⁻¹ : ℝ≥0∞) :=
          (ENNReal.tsum_const_eq_top_of_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)).symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun n => by
          obtain ⟨y, hy⟩ := flipKernel_pow (n + 1) true
          rw [hy]
          exact (half_le_fNorm_flip y).trans (le_mul_of_one_le_left' (one_le_pow₀ hr))

end MeynTweedie.Positivity
