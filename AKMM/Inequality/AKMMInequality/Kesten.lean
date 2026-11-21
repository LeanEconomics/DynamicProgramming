/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInequality.Uninsurable
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.IdentDistrib

/-!
# §21.2.3: Kesten's random growth process `aₜ₊₁ = sₜaₜ + εₜ`

AKMM, §21.2.3, p. 651 and fn 31. Beyond the text (decision 5): the book states Kesten's theorem
without proof. The Kesten–Goldie tail asymptotics `P(A > a) ~ C a^{−ζ}` need the implicit
renewal theorem and are NOT formalised; what is proved is the stationary solution, the
convergence of the law of `aₜ`, and the moment characterisation of the tail index.

The setting is the canonical i.i.d. space `kp_P ν = infinitePi ν` on `ℕ → ℝ × ℝ`, coordinate `n`
being `(sₙ, εₙ)`, for any law `ν` of `(s, ε)` (every i.i.d. sequence has this law). Moments are
`E|s|^κ = ∫⁻ ‖x.1‖ₑ^κ ∂ν`, `E|ε|^κ = ∫⁻ ‖x.2‖ₑ^κ ∂ν`.

* **The stationary solution.** If `E|s|^κ < 1` and `E|ε|^κ < ∞` for some `κ > 0`, the perpetuity
  `A = Σₖ s₀⋯s_{k−1} εₖ` (`kp_perp`) converges absolutely a.s. (`kp_perp_hasSum_ae`) and in `L^κ`
  (`kp_perp_tendsto_Lp`); a.s. `A = ε₀ + s₀A′` with `A′ = A ∘ shift =ᵈ A` independent of
  `(s₀, ε₀)` (`kp_fixed_point`). For any `a₀` the law of `aₜ` (`kp_iter`) converges weakly to the
  law of `A`: `E f(aₜ) → E f(A)` for bounded continuous `f` (`kp_iter_tendsto_law`), because `aₜ`
  has the law of the backward iterate (`kp_iter_identDistrib`), which converges a.s. to `A`
  (`kp_back_tendsto_ae`).
* **Moments.** `E|A|^κ < ∞` when `E|s|^κ < 1`, `E|ε|^κ < ∞` (`kp_lintegral_perp_lt_top`, via
  subadditivity of `x^κ` for `κ ≤ 1` and Minkowski for `κ ≥ 1`, `kp_lintegral_tsum_rpow_le`), with
  the Markov bound `P(|A| ≥ a) ≤ C_κ a^{−κ}` (`kp_tail_bound`); `E A^κ = ∞` when `s, ε ≥ 0`,
  `E s^κ > 1`, `E ε^κ > 0` (`kp_lintegral_abs_eq_top`, `kp_lintegral_perp_eq_top`). Hence
  `sup {κ > 0 : E A^κ < ∞} = ζ` (`kp_tail_index`).
* **Finitely supported shocks.** For `s` finitely supported, not identically `1`, the root `ζ` of
  `E s^ζ = 1` separates `E s^κ < 1` from `E s^κ > 1` (`kp_moment_root`); for finitely supported
  `(s, ε)` with `ε ≥ 0` not a.s. `0` the tail index is the root of `ke_moment_exists`
  (`kp_finite_tail_index`, `kp_finite_tail_index_ke`); the two-point example `s ∈ {1/2, 3/2}`,
  `ε = 1` has tail index `1` (`kp_two_point`, `kp_two_point_ke`).

The moment condition `E s^ζ = 1` is weaker than the conclusion "Pareto tail with exponent `ζ`";
`kp_tail_index` proves exactly the moment-sense content of that conclusion. At `κ = ζ` itself
nothing is claimed.
-/

namespace AKMM.Inequality

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-! ### The i.i.d. space and its shift -/

/-- The canonical i.i.d. space for Kesten's process: `Ω = ℕ → ℝ × ℝ`, coordinate `n` being the
pair `(sₙ, εₙ)`, under the product of copies of the law `ν` of `(s, ε)`. -/
noncomputable abbrev kp_P (ν : Measure (ℝ × ℝ)) : Measure (ℕ → ℝ × ℝ) :=
  Measure.infinitePi fun _ : ℕ => ν

/-- The shift `(ωₙ)ₙ ↦ (ωₙ₊₁)ₙ`. -/
def kp_shift (ω : ℕ → ℝ × ℝ) : ℕ → ℝ × ℝ := fun n => ω (n + 1)

variable {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]

theorem kp_shift_measurable : Measurable kp_shift :=
  Measurable.of_eval fun n => measurable_pi_apply (n + 1)

/-- The shift preserves the i.i.d. law. -/
theorem kp_shift_mp : MeasurePreserving kp_shift (kp_P ν) (kp_P ν) :=
  ⟨kp_shift_measurable, Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν)
    (f := Nat.succ) Nat.succ_injective⟩

/-- The first pair `ω 0` is independent of the shifted sequence. -/
theorem kp_indep_head_shift : IndepFun (fun ω : ℕ → ℝ × ℝ => ω 0) kp_shift (kp_P ν) := by
  have hI : iIndepFun (fun i (ω : ℕ → ℝ × ℝ) => ω i) (kp_P ν) :=
    iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id
  rw [iIndepFun_iff_iIndep] at hI
  have hle : ∀ i, MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → ℝ × ℝ)) := fun i => (measurable_pi_apply i).comap_le
  have h := indep_iSup_of_disjoint hle hI (S := {0}) (T := {n | 1 ≤ n})
    (Set.disjoint_left.2 fun a ha hb => by simp_all)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · exact le_iSup₂_of_le (f := fun i (_ : i ∈ ({0} : Set ℕ)) =>
      MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance) 0 rfl le_rfl
  · refine Measurable.comap_le ?_
    refine @Measurable.of_eval _ _ _ (⨆ i ∈ {n | 1 ≤ n}, MeasurableSpace.comap
      (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance) _ _ fun n => ?_
    exact Measurable.of_comap_le (le_iSup₂_of_le (f := fun i (_ : i ∈ {n : ℕ | 1 ≤ n}) =>
      MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance) (n + 1)
      (by simp) le_rfl)

/-- Independence of the first pair and the shift, in integral form. -/
theorem kp_lintegral_head_shift {F : ℝ × ℝ → ℝ≥0∞} {G : (ℕ → ℝ × ℝ) → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ ω, F (ω 0) * G (kp_shift ω) ∂kp_P ν = (∫⁻ x, F x ∂ν) * ∫⁻ ω, G ω ∂kp_P ν := by
  have h := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hF.comp (measurable_pi_apply 0)) (hG.comp kp_shift_measurable)
    ((kp_indep_head_shift (ν := ν)).comp hF hG)
  simp only [Pi.mul_apply, Function.comp_apply] at h
  rw [h, (kp_shift_mp (ν := ν)).lintegral_comp hG,
    (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0).lintegral_comp hF]

/-- The moment formula for i.i.d. coordinates: `E[f(X₀)⋯f(X_{k−1}) g(X_k)] = (E f)^k E g`. -/
theorem kp_lintegral_prod_mul {f g : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (k : ℕ) : ∫⁻ ω, (∏ j ∈ Finset.range k, f (ω j)) * g (ω k) ∂kp_P ν =
      (∫⁻ x, f x ∂ν) ^ k * ∫⁻ x, g x ∂ν := by
  induction k with
  | zero =>
    simpa using (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0).lintegral_comp hg
  | succ k ih =>
    have e : ∀ ω : ℕ → ℝ × ℝ, (∏ j ∈ Finset.range (k + 1), f (ω j)) * g (ω (k + 1)) =
        f (ω 0) * ((∏ j ∈ Finset.range k, f (kp_shift ω j)) * g (kp_shift ω k)) := by
      intro ω
      rw [Finset.prod_range_succ']
      simp only [kp_shift]
      ring
    simp_rw [e]
    have h2 := kp_lintegral_head_shift (ν := ν)
      (G := fun ω => (∏ j ∈ Finset.range k, f (ω j)) * g (ω k)) hf (by fun_prop)
    rw [h2, ih, pow_succ]
    ring

/-! ### Moments of a series of nonnegative functions -/

/-- Subadditivity of `x ↦ x^κ` for `0 < κ ≤ 1`, for finite sums. -/
theorem kp_rpow_sum_le_sum_rpow {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (x : ℕ → ℝ≥0∞) (n : ℕ) :
    (∑ k ∈ Finset.range n, x k) ^ κ ≤ ∑ k ∈ Finset.range n, x k ^ κ := by
  induction n with
  | zero => simp [ENNReal.zero_rpow_of_pos hκ0]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hκ0.le hκ1).trans (add_le_add ih le_rfl)

/-- Minkowski's inequality in `L^κ`, `κ ≥ 1`, for finite sums of nonnegative functions. -/
theorem kp_lintegral_sum_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {κ : ℝ}
    (hκ : 1 ≤ κ) (T : ℕ → α → ℝ≥0∞) (hT : ∀ k, Measurable (T k)) (n : ℕ) :
    (∫⁻ a, (∑ k ∈ Finset.range n, T k a) ^ κ ∂μ) ^ (1 / κ) ≤
      ∑ k ∈ Finset.range n, (∫⁻ a, T k a ^ κ ∂μ) ^ (1 / κ) := by
  induction n with
  | zero =>
    have : (0 : ℝ) < κ := by linarith
    simp [ENNReal.zero_rpow_of_pos this, this]
  | succ n ih =>
    simp_rw [Finset.sum_range_succ]
    have hm : Measurable fun a => ∑ k ∈ Finset.range n, T k a :=
      Finset.measurable_sum _ fun k _ => hT k
    exact (ENNReal.lintegral_Lp_add_le hm.aemeasurable (hT n).aemeasurable hκ).trans
      (add_le_add ih le_rfl)

/-- **Geometric moment bounds sum.** If `E Tₖ^κ ≤ rᵏ c` with `r < 1`, then
`E (Σₖ Tₖ)^κ ≤ K c` with `K < ∞` depending only on `r` and `κ` (subadditivity of `x^κ` for
`κ ≤ 1`, Minkowski for `κ ≥ 1`). -/
theorem kp_lintegral_tsum_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {κ : ℝ}
    (hκ : 0 < κ) {r : ℝ≥0∞} (hr : r < 1) : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (T : ℕ → α → ℝ≥0∞) (c : ℝ≥0∞), (∀ k, Measurable (T k)) →
        (∀ k, ∫⁻ a, T k a ^ κ ∂μ ≤ r ^ k * c) → ∫⁻ a, (∑' k, T k a) ^ κ ∂μ ≤ K * c := by
  have hred : ∀ (T : ℕ → α → ℝ≥0∞), (∀ k, Measurable (T k)) →
      ∫⁻ a, (∑' k, T k a) ^ κ ∂μ = ⨆ n, ∫⁻ a, (∑ k ∈ Finset.range n, T k a) ^ κ ∂μ := by
    intro T hT
    have e : ∀ a, (∑' k, T k a) ^ κ = ⨆ n, (∑ k ∈ Finset.range n, T k a) ^ κ := by
      intro a
      rw [ENNReal.tsum_eq_iSup_nat]
      exact Monotone.map_iSup_of_continuousAt ENNReal.continuous_rpow_const.continuousAt
        (ENNReal.monotone_rpow_of_nonneg hκ.le) (ENNReal.zero_rpow_of_pos hκ)
    simp_rw [e]
    refine lintegral_iSup (fun n => (Finset.measurable_sum _ fun k _ => hT k).pow_const κ) ?_
    intro m n hmn a
    exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.range_mono hmn)) hκ.le
  rcases le_total κ 1 with h1 | h1
  · refine ⟨(1 - r)⁻¹, ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hr).ne', fun T c hT hc => ?_⟩
    rw [hred T hT]
    refine iSup_le fun n => ?_
    calc ∫⁻ a, (∑ k ∈ Finset.range n, T k a) ^ κ ∂μ
        ≤ ∫⁻ a, ∑ k ∈ Finset.range n, T k a ^ κ ∂μ :=
          lintegral_mono fun a => kp_rpow_sum_le_sum_rpow hκ h1 _ n
      _ = ∑ k ∈ Finset.range n, ∫⁻ a, T k a ^ κ ∂μ :=
          lintegral_finsetSum _ fun k _ => (hT k).pow_const κ
      _ ≤ ∑ k ∈ Finset.range n, r ^ k * c := Finset.sum_le_sum fun k _ => hc k
      _ ≤ ∑' k, r ^ k * c := ENNReal.sum_le_tsum _
      _ = (1 - r)⁻¹ * c := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  · set q := r ^ (1 / κ) with hq
    have hq1 : q < 1 := ENNReal.rpow_lt_one hr (by positivity)
    refine ⟨((1 - q)⁻¹) ^ κ, (ENNReal.rpow_lt_top_of_nonneg hκ.le
      (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hq1).ne')).ne, fun T c hT hc => ?_⟩
    rw [hred T hT]
    refine iSup_le fun n => ?_
    have hb : (∫⁻ a, (∑ k ∈ Finset.range n, T k a) ^ κ ∂μ) ^ (1 / κ) ≤
        (1 - q)⁻¹ * c ^ (1 / κ) := by
      calc _ ≤ ∑ k ∈ Finset.range n, (∫⁻ a, T k a ^ κ ∂μ) ^ (1 / κ) :=
            kp_lintegral_sum_rpow_le h1 T hT n
        _ ≤ ∑ k ∈ Finset.range n, q ^ k * c ^ (1 / κ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          calc _ ≤ (r ^ k * c) ^ (1 / κ) := ENNReal.rpow_le_rpow (hc k) (by positivity)
            _ = q ^ k * c ^ (1 / κ) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hq, ← ENNReal.rpow_natCast,
                ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm,
                mul_comm (1 / κ)]
              exact mul_comm _ _
        _ ≤ ∑' k, q ^ k * c ^ (1 / κ) := ENNReal.sum_le_tsum _
        _ = (1 - q)⁻¹ * c ^ (1 / κ) := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    have := ENNReal.rpow_le_rpow hb hκ.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hκ.ne', ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ hκ.le, ← ENNReal.rpow_mul, one_div_mul_cancel hκ.ne',
      ENNReal.rpow_one] at this

/-! ### The perpetuity `A = Σₖ s₀⋯s_{k−1} εₖ` -/

/-- The `k`th term `s₀⋯s_{k−1} εₖ` of the perpetuity (the book's `s₁⋯s_k ε_{k+1}`, with time
indexed from `0`). -/
noncomputable def kp_term (ω : ℕ → ℝ × ℝ) (k : ℕ) : ℝ :=
  (∏ j ∈ Finset.range k, (ω j).1) * (ω k).2

/-- The absolute series `Σₖ |s₀⋯s_{k−1} εₖ|`, in `[0, ∞]`. -/
noncomputable def kp_abs (ω : ℕ → ℝ × ℝ) : ℝ≥0∞ :=
  ∑' k, ‖kp_term ω k‖ₑ

/-- The perpetuity `A = Σₖ s₀⋯s_{k−1} εₖ` (Lean's `tsum`: the sum where the series converges,
`0` elsewhere; it converges almost surely, `kp_perp_hasSum_ae`). -/
noncomputable def kp_perp (ω : ℕ → ℝ × ℝ) : ℝ :=
  ∑' k, kp_term ω k

theorem kp_term_measurable (k : ℕ) : Measurable fun ω : ℕ → ℝ × ℝ => kp_term ω k := by
  unfold kp_term
  fun_prop

theorem kp_abs_measurable : Measurable kp_abs :=
  Measurable.tsum fun k => (kp_term_measurable k).enorm

theorem kp_perp_measurable : Measurable kp_perp :=
  Measurable.tsum fun k => kp_term_measurable k

/-- Where the absolute series is finite, `A` is the sum of the series. -/
theorem kp_hasSum {ω : ℕ → ℝ × ℝ} (h : kp_abs ω ≠ ⊤) : HasSum (kp_term ω) (kp_perp ω) := by
  refine (Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1 ?_)).hasSum
  simpa [kp_abs, enorm_eq_nnnorm] using h

/-- `|s₀⋯s_{n−1}|^κ = |s₀|^κ⋯|s_{n−1}|^κ`. -/
theorem kp_enorm_prod_rpow (ω : ℕ → ℝ × ℝ) (n : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖∏ j ∈ Finset.range n, (ω j).1‖ₑ ^ κ = ∏ j ∈ Finset.range n, ‖(ω j).1‖ₑ ^ κ := by
  have hp : ‖∏ j ∈ Finset.range n, (ω j).1‖ₑ = ∏ j ∈ Finset.range n, ‖(ω j).1‖ₑ := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.prod_range_succ, Finset.prod_range_succ, enorm_mul, ih]
  rw [hp, ENNReal.prod_rpow_of_nonneg hκ]

/-- `|s₀⋯s_{k−1} εₖ|^κ = |s₀|^κ⋯|s_{k−1}|^κ |εₖ|^κ`. -/
theorem kp_enorm_term_rpow (ω : ℕ → ℝ × ℝ) (k : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖kp_term ω k‖ₑ ^ κ = (∏ j ∈ Finset.range k, ‖(ω j).1‖ₑ ^ κ) * ‖(ω k).2‖ₑ ^ κ := by
  rw [kp_term, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hκ, kp_enorm_prod_rpow _ _ hκ]

/-- `E|s₀⋯s_{k−1} εₖ|^κ = (E|s|^κ)^k E|ε|^κ`. -/
theorem kp_lintegral_term {κ : ℝ} (hκ : 0 ≤ κ) (k : ℕ) :
    ∫⁻ ω, ‖kp_term ω k‖ₑ ^ κ ∂kp_P ν =
      (∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν) ^ k * ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν := by
  simp_rw [kp_enorm_term_rpow _ _ hκ]
  exact kp_lintegral_prod_mul (f := fun x => ‖x.1‖ₑ ^ κ) (g := fun x => ‖x.2‖ₑ ^ κ)
    (by fun_prop) (by fun_prop) k

/-- `E(Σₖ |s₀⋯s_{k−1} εₖ|)^κ < ∞` when `E|s|^κ < 1` and `E|ε|^κ < ∞`. -/
theorem kp_lintegral_abs_lt_top {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) : ∫⁻ ω, kp_abs ω ^ κ ∂kp_P ν < ⊤ := by
  obtain ⟨K, hK, hb⟩ := kp_lintegral_tsum_rpow_le (μ := kp_P ν) hκ hρ
  exact (hb (fun k ω => ‖kp_term ω k‖ₑ) _ (fun k => (kp_term_measurable k).enorm)
    (fun k => (kp_lintegral_term hκ.le k).le)).trans_lt (ENNReal.mul_lt_top hK.lt_top hm.lt_top)

/-- The absolute series is finite almost surely. -/
theorem kp_abs_ae_lt_top {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) : ∀ᵐ ω ∂kp_P ν, kp_abs ω < ⊤ := by
  have h := ae_lt_top' (kp_abs_measurable.pow_const κ).aemeasurable
    (kp_lintegral_abs_lt_top hκ hρ hm).ne
  filter_upwards [h] with ω hω
  exact (ENNReal.rpow_lt_top_iff_of_pos hκ).1 hω

/-- **AKMM, p. 651 (beyond the text): the perpetuity converges almost surely.** If
`E|s|^κ < 1` and `E|ε|^κ < ∞` for some `κ > 0`, the series `Σₖ s₀⋯s_{k−1} εₖ` converges
absolutely almost surely, with sum `A`. -/
theorem kp_perp_hasSum_ae {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) : ∀ᵐ ω ∂kp_P ν, HasSum (kp_term ω) (kp_perp ω) := by
  filter_upwards [kp_abs_ae_lt_top hκ hρ hm] with ω hω using kp_hasSum hω.ne

/-- **AKMM, p. 651 (beyond the text): the perpetuity converges in `L^κ`.** Under the same
hypotheses, `E|A − Σ_{k<n} s₀⋯s_{k−1} εₖ|^κ → 0`. -/
theorem kp_perp_tendsto_Lp {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) :
    Tendsto (fun n => ∫⁻ ω, ‖kp_perp ω - ∑ k ∈ Finset.range n, kp_term ω k‖ₑ ^ κ ∂kp_P ν)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := kp_lintegral_tsum_rpow_le (μ := kp_P ν) hκ hρ
  have hbound : ∀ n, ∫⁻ ω, ‖kp_perp ω - ∑ k ∈ Finset.range n, kp_term ω k‖ₑ ^ κ ∂kp_P ν ≤
      K * ((∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν) ^ n * ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν) := by
    intro n
    have htail := hb (fun k ω => ‖kp_term ω (k + n)‖ₑ) _ (fun k => (kp_term_measurable _).enorm)
      (fun k => by rw [kp_lintegral_term hκ.le, pow_add, mul_assoc])
    refine le_trans (lintegral_mono_ae ?_) htail
    filter_upwards [kp_perp_hasSum_ae hκ hρ hm] with ω hω
    have h' := (hasSum_nat_add_iff' n).2 hω
    rw [← h'.tsum_eq]
    exact ENNReal.rpow_le_rpow enorm_tsum_le_tsum_enorm hκ.le
  have h0 : Tendsto (fun n => K * ((∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν) ^ n * ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν)) atTop
      (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := K) (ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ) (Or.inr hm)) (Or.inr hK)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le)
    hbound

/-! ### The fixed-point law `A = ε₀ + s₀A′` -/

theorem kp_term_zero (ω : ℕ → ℝ × ℝ) : kp_term ω 0 = (ω 0).2 := by
  simp [kp_term]

theorem kp_term_succ (ω : ℕ → ℝ × ℝ) (k : ℕ) :
    kp_term ω (k + 1) = (ω 0).1 * kp_term (kp_shift ω) k := by
  simp only [kp_term, kp_shift, Finset.prod_range_succ']
  ring

/-- The absolute series satisfies `Σ = |ε₀| + |s₀| Σ′` pathwise, `Σ′` the series of the shift. -/
theorem kp_abs_eq (ω : ℕ → ℝ × ℝ) :
    kp_abs ω = ‖(ω 0).2‖ₑ + ‖(ω 0).1‖ₑ * kp_abs (kp_shift ω) := by
  rw [kp_abs, tsum_eq_zero_add' ENNReal.summable]
  simp_rw [kp_term_succ, enorm_mul, ENNReal.tsum_mul_left, kp_term_zero]
  rfl

/-- **AKMM, p. 651 (beyond the text): the stationary law is a fixed point of
`A ↦ sA + ε`.** Under the hypotheses of `kp_perp_hasSum_ae`, almost surely
`A = ε₀ + s₀A′` where `A′ = A ∘ shift` is the perpetuity of the shifted sequence `(sₙ₊₁, εₙ₊₁)`;
`A′` has the law of `A` and is independent of `(s₀, ε₀)`. So `A =ᵈ sA′ + ε` with `A′ =ᵈ A`
independent of `(s, ε)`. -/
theorem kp_fixed_point {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) :
    (∀ᵐ ω ∂kp_P ν, kp_perp ω = (ω 0).2 + (ω 0).1 * kp_perp (kp_shift ω)) ∧
      IdentDistrib (fun ω => kp_perp (kp_shift ω)) kp_perp (kp_P ν) (kp_P ν) ∧
      IndepFun (fun ω : ℕ → ℝ × ℝ => ω 0) (fun ω => kp_perp (kp_shift ω)) (kp_P ν) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := kp_perp_hasSum_ae hκ hρ hm
    have h' := (kp_shift_mp (ν := ν)).quasiMeasurePreserving.ae h
    filter_upwards [h, h'] with ω hω hω'
    have h1 : HasSum (fun k => kp_term ω (k + 1)) ((ω 0).1 * kp_perp (kp_shift ω)) := by
      simp_rw [kp_term_succ]
      exact hω'.mul_left _
    have h2 : HasSum (kp_term ω) ((ω 0).2 + (ω 0).1 * kp_perp (kp_shift ω)) := by
      refine (hasSum_nat_add_iff' 1).1 ?_
      rw [Finset.sum_range_one, kp_term_zero, add_sub_cancel_left]
      exact h1
    exact hω.unique h2
  · refine ⟨(kp_perp_measurable.comp kp_shift_measurable).aemeasurable,
      kp_perp_measurable.aemeasurable, ?_⟩
    change Measure.map (kp_perp ∘ kp_shift) _ = _
    rw [← Measure.map_map kp_perp_measurable kp_shift_measurable, (kp_shift_mp (ν := ν)).map_eq]
  · exact (kp_indep_head_shift (ν := ν)).comp measurable_id kp_perp_measurable

/-! ### Convergence of the law of `aₜ` -/

/-- Kesten's process `aₜ₊₁ = sₜaₜ + εₜ` from `a₀` (AKMM, p. 651). -/
noncomputable def kp_iter (a₀ : ℝ) (ω : ℕ → ℝ × ℝ) : ℕ → ℝ
  | 0 => a₀
  | t + 1 => (ω t).1 * kp_iter a₀ ω t + (ω t).2

/-- The backward iterate `Σ_{k<t} s₀⋯s_{k−1} εₖ + s₀⋯s_{t−1} a₀`. -/
noncomputable def kp_back (a₀ : ℝ) (ω : ℕ → ℝ × ℝ) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range t, kp_term ω k + (∏ j ∈ Finset.range t, (ω j).1) * a₀

/-- The index reversal `j ↦ t − 1 − j` on `{0, …, t − 1}`, the identity elsewhere. -/
def kp_rev (t j : ℕ) : ℕ := if j < t then t - 1 - j else j

theorem kp_rev_injective (t : ℕ) : Function.Injective (kp_rev t) := by
  intro i j h
  unfold kp_rev at h
  split_ifs at h <;> omega

/-- Reversing the first `t` coordinates preserves the i.i.d. law. -/
theorem kp_rev_mp (t : ℕ) :
    MeasurePreserving (fun (ω : ℕ → ℝ × ℝ) j => ω (kp_rev t j)) (kp_P ν) (kp_P ν) :=
  ⟨Measurable.of_eval fun _ => measurable_pi_apply _,
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν) (kp_rev_injective t)⟩

theorem kp_back_congr {a₀ : ℝ} {ω ω' : ℕ → ℝ × ℝ} {t : ℕ} (h : ∀ j < t, ω j = ω' j) :
    kp_back a₀ ω t = kp_back a₀ ω' t := by
  have hp : ∀ k ≤ t, ∏ j ∈ Finset.range k, (ω j).1 = ∏ j ∈ Finset.range k, (ω' j).1 :=
    fun k hk => Finset.prod_congr rfl fun j hj => by
      rw [h j (by have := Finset.mem_range.1 hj; omega)]
  unfold kp_back
  rw [hp t le_rfl]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < t := Finset.mem_range.1 hk
  unfold kp_term
  rw [hp k hk'.le, h k hk']

theorem kp_back_succ (a₀ : ℝ) (ω : ℕ → ℝ × ℝ) (t : ℕ) :
    kp_back a₀ ω (t + 1) = (ω 0).2 + (ω 0).1 * kp_back a₀ (kp_shift ω) t := by
  unfold kp_back
  rw [Finset.sum_range_succ', Finset.prod_range_succ']
  simp_rw [kp_term_succ, kp_term_zero]
  rw [← Finset.mul_sum]
  simp only [kp_shift]
  ring

/-- The forward iterate is the backward iterate of the time-reversed shocks. -/
theorem kp_iter_eq_back (a₀ : ℝ) (ω : ℕ → ℝ × ℝ) (t : ℕ) :
    kp_iter a₀ ω t = kp_back a₀ (fun j => ω (kp_rev t j)) t := by
  induction t with
  | zero => simp [kp_iter, kp_back]
  | succ t ih =>
    have h0 : kp_rev (t + 1) 0 = t := by simp [kp_rev]
    have hc : kp_back a₀ (kp_shift fun j => ω (kp_rev (t + 1) j)) t =
        kp_back a₀ (fun j => ω (kp_rev t j)) t := by
      refine kp_back_congr fun j hj => ?_
      simp only [kp_shift, kp_rev]
      congr 1
      split_ifs <;> omega
    rw [kp_iter, ih, kp_back_succ, h0, hc]
    ring

theorem kp_back_measurable (a₀ : ℝ) (t : ℕ) : Measurable fun ω => kp_back a₀ ω t := by
  unfold kp_back kp_term
  fun_prop

/-- The forward and backward iterates have the same law. -/
theorem kp_iter_identDistrib (a₀ : ℝ) (t : ℕ) :
    IdentDistrib (fun ω => kp_iter a₀ ω t) (fun ω => kp_back a₀ ω t) (kp_P ν) (kp_P ν) := by
  have e : (fun ω => kp_iter a₀ ω t) =
      (fun ω => kp_back a₀ ω t) ∘ (fun (ω : ℕ → ℝ × ℝ) j => ω (kp_rev t j)) :=
    funext fun ω => kp_iter_eq_back a₀ ω t
  rw [e]
  refine ⟨((kp_back_measurable a₀ t).comp (kp_rev_mp (ν := ν) t).measurable).aemeasurable,
    (kp_back_measurable a₀ t).aemeasurable, ?_⟩
  rw [← Measure.map_map (kp_back_measurable a₀ t) (kp_rev_mp (ν := ν) t).measurable,
    (kp_rev_mp t).map_eq]

/-- `s₀⋯s_{t−1} → 0` almost surely when `E|s|^κ < 1`. -/
theorem kp_prod_tendsto_zero {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1) :
    ∀ᵐ ω ∂kp_P ν, Tendsto (fun t => ∏ j ∈ Finset.range t, (ω j).1) atTop (𝓝 0) := by
  have hmeas : ∀ t, Measurable fun ω : ℕ → ℝ × ℝ => ‖∏ j ∈ Finset.range t, (ω j).1‖ₑ ^ κ :=
    fun t => by fun_prop
  have hint : ∫⁻ ω, ∑' t, ‖∏ j ∈ Finset.range t, (ω j).1‖ₑ ^ κ ∂kp_P ν ≠ ⊤ := by
    rw [lintegral_tsum fun t => (hmeas t).aemeasurable]
    have e : ∀ t, ∫⁻ ω, ‖∏ j ∈ Finset.range t, (ω j).1‖ₑ ^ κ ∂kp_P ν =
        (∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν) ^ t := by
      intro t
      have := kp_lintegral_prod_mul (ν := ν) (f := fun x => ‖x.1‖ₑ ^ κ) (g := fun _ => 1)
        (by fun_prop) measurable_const t
      simpa [kp_enorm_prod_rpow _ _ hκ.le] using this
    simp_rw [e, ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ).ne'
  filter_upwards [ae_lt_top' (Measurable.tsum hmeas).aemeasurable hint] with ω hω
  have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 := ((ENNReal.continuous_rpow_const (y := 1 / κ)).tendsto 0).comp h1
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at h2
  refine tendsto_zero_iff_enorm_tendsto_zero.2 ?_
  refine h2.congr fun t => ?_
  simp only [Function.comp_apply]
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hκ.ne', ENNReal.rpow_one]

/-- **AKMM, p. 651 (beyond the text): the backward iterates converge almost surely to `A`.** -/
theorem kp_back_tendsto_ae (a₀ : ℝ) {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) :
    ∀ᵐ ω ∂kp_P ν, Tendsto (fun t => kp_back a₀ ω t) atTop (𝓝 (kp_perp ω)) := by
  filter_upwards [kp_perp_hasSum_ae hκ hρ hm, kp_prod_tendsto_zero hκ hρ] with ω h1 h2
  simpa [kp_back] using h1.tendsto_sum_nat.add (h2.mul_const a₀)

/-- **AKMM, p. 651 (beyond the text, corrections 3): the law of `aₜ` converges weakly to the
law of `A` from any `a₀`.** If `E|s|^κ < 1` and `E|ε|^κ < ∞` for some `κ > 0`, then for every
bounded continuous `f`, `E f(aₜ) → E f(A)`. (Convergence in distribution, not in probability.) -/
theorem kp_iter_tendsto_law (a₀ : ℝ) {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun t => ∫ ω, f (kp_iter a₀ ω t) ∂kp_P ν) atTop
      (𝓝 (∫ ω, f (kp_perp ω) ∂kp_P ν)) := by
  have e : ∀ t, ∫ ω, f (kp_iter a₀ ω t) ∂kp_P ν = ∫ ω, f (kp_back a₀ ω t) ∂kp_P ν :=
    fun t => ((kp_iter_identDistrib (ν := ν) a₀ t).comp f.continuous.measurable).integral_eq
  simp_rw [e]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖) (fun t =>
    (f.continuous.measurable.comp (kp_back_measurable a₀ t)).aestronglyMeasurable)
    (integrable_const _) (fun t => ae_of_all _ fun ω => f.norm_coe_le_norm _) ?_
  filter_upwards [kp_back_tendsto_ae a₀ hκ hρ hm] with ω hω
  exact (f.continuous.tendsto _).comp hω

/-! ### Moment bounds that fix the tail index -/

/-- **AKMM, p. 651 (beyond the text): moments of `A` of order `κ` are finite when
`E|s|^κ < 1`.** If `E|s|^κ < 1` and `E|ε|^κ < ∞` then `E|A|^κ < ∞` (subadditivity of `x^κ` for
`κ < 1`, Minkowski for `κ ≥ 1`). -/
theorem kp_lintegral_perp_lt_top {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) : ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν < ⊤ :=
  lt_of_le_of_lt (lintegral_mono fun _ => ENNReal.rpow_le_rpow enorm_tsum_le_tsum_enorm hκ.le)
    (kp_lintegral_abs_lt_top hκ hρ hm)

/-- **AKMM, p. 651 (beyond the text): Pareto-type tail bound.** Under the hypotheses of
`kp_lintegral_perp_lt_top`, `P(|A| ≥ a) ≤ C_κ a^{−κ}` for all `a > 0` (Markov). -/
theorem kp_tail_bound {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a →
      kp_P ν {ω | a ≤ |kp_perp ω|} ≤ C * ENNReal.ofReal (a ^ (-κ)) := by
  refine ⟨∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν, (kp_lintegral_perp_lt_top hκ hρ hm).ne,
    fun a ha => ?_⟩
  have hM := mul_meas_ge_le_lintegral₀ (μ := kp_P ν)
    (kp_perp_measurable.enorm.pow_const κ).aemeasurable (ENNReal.ofReal (a ^ κ))
  have hset : {ω | a ≤ |kp_perp ω|} ⊆
      {ω | ENNReal.ofReal (a ^ κ) ≤ ‖kp_perp ω‖ₑ ^ κ} := by
    intro ω (hω : a ≤ |kp_perp ω|)
    change ENNReal.ofReal (a ^ κ) ≤ ‖kp_perp ω‖ₑ ^ κ
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hκ.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ha.le hω hκ.le)
  calc kp_P ν {ω | a ≤ |kp_perp ω|}
      ≤ kp_P ν {ω | ENNReal.ofReal (a ^ κ) ≤ ‖kp_perp ω‖ₑ ^ κ} := measure_mono hset
    _ = ENNReal.ofReal (a ^ (-κ)) * (ENNReal.ofReal (a ^ κ) *
          kp_P ν {ω | ENNReal.ofReal (a ^ κ) ≤ ‖kp_perp ω‖ₑ ^ κ}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add ha,
          neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (a ^ (-κ)) * ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν := by gcongr
    _ = _ := mul_comm _ _

/-- **AKMM, p. 651 (beyond the text): moments above the tail index are infinite.** If
`E|s|^κ > 1` and `E|ε|^κ > 0`, then `E(Σₖ |s₀⋯s_{k−1} εₖ|)^κ = ∞`: the series `Σ` satisfies
`Σ ≥ |s₀| Σ′` with `Σ′ =ᵈ Σ` independent of `s₀`, and `E Σ^κ ≥ E|ε|^κ > 0`, so a finite
`E Σ^κ` would give `E Σ^κ ≥ E|s|^κ E Σ^κ > E Σ^κ`. -/
theorem kp_lintegral_abs_eq_top {κ : ℝ} (hκ : 0 < κ) (hρ : 1 < ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ 0) : ∫⁻ ω, kp_abs ω ^ κ ∂kp_P ν = ⊤ := by
  set I := ∫⁻ ω, kp_abs ω ^ κ ∂kp_P ν with hI
  have hge : (∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν) * I ≤ I := by
    have h := kp_lintegral_head_shift (ν := ν) (F := fun x => ‖x.1‖ₑ ^ κ)
      (G := fun ω => kp_abs ω ^ κ) (by fun_prop) (kp_abs_measurable.pow_const κ)
    rw [hI, ← h]
    refine lintegral_mono fun ω => ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hκ.le]
    refine ENNReal.rpow_le_rpow ?_ hκ.le
    rw [kp_abs_eq ω]
    exact le_add_self
  have hpos : I ≠ 0 := by
    have h1 : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≤ I := by
      rw [← (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0).lintegral_comp
        (by fun_prop : Measurable fun x : ℝ × ℝ => ‖x.2‖ₑ ^ κ)]
      refine lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ hκ.le
      rw [kp_abs_eq ω]
      exact le_self_add
    exact (lt_of_lt_of_le (pos_iff_ne_zero.2 hm) h1).ne'
  by_contra htop
  have := ENNReal.mul_lt_mul_right hpos htop hρ
  rw [mul_one, mul_comm] at this
  exact absurd hge (not_le.2 this)

/-- With `s, ε ≥ 0` and the series a.s. finite, `|A| = Σₖ s₀⋯s_{k−1} εₖ` almost surely. -/
theorem kp_enorm_perp_ae (hs : ∀ᵐ x ∂ν, 0 ≤ x.1) (he : ∀ᵐ x ∂ν, 0 ≤ x.2)
    (hfin : ∀ᵐ ω ∂kp_P ν, kp_abs ω < ⊤) : ∀ᵐ ω ∂kp_P ν, ‖kp_perp ω‖ₑ = kp_abs ω := by
  have hall : ∀ᵐ ω ∂kp_P ν, ∀ j, 0 ≤ (ω j).1 ∧ 0 ≤ (ω j).2 := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) j).quasiMeasurePreserving.ae
      (hs.and he)
  filter_upwards [hall, hfin] with ω hω hf
  have hnn : ∀ k, 0 ≤ kp_term ω k := fun k =>
    mul_nonneg (Finset.prod_nonneg fun j _ => (hω j).1) (hω k).2
  have hsum := kp_hasSum hf.ne
  rw [kp_abs, kp_perp, Real.enorm_eq_ofReal_abs, abs_of_nonneg (tsum_nonneg hnn),
    ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable]
  congr 1
  ext k
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn k)]

/-- **AKMM, p. 651 (beyond the text): `E A^κ = ∞` above the tail index.** If `s, ε ≥ 0`, the
series converges a.s. (some `κ₀ > 0` with `E s^{κ₀} < 1`, `E ε^{κ₀} < ∞`), `E s^κ > 1` and
`E ε^κ > 0`, then `E A^κ = ∞`. -/
theorem kp_lintegral_perp_eq_top {κ κ₀ : ℝ} (hκ : 0 < κ) (hρ : 1 < ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ 0) (hs : ∀ᵐ x ∂ν, 0 ≤ x.1) (he : ∀ᵐ x ∂ν, 0 ≤ x.2)
    (hκ₀ : 0 < κ₀) (hρ₀ : ∫⁻ x, ‖x.1‖ₑ ^ κ₀ ∂ν < 1) (hm₀ : ∫⁻ x, ‖x.2‖ₑ ^ κ₀ ∂ν ≠ ⊤) :
    ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν = ⊤ := by
  have h : (fun ω => ‖kp_perp ω‖ₑ ^ κ) =ᵐ[kp_P ν] fun ω => kp_abs ω ^ κ := by
    filter_upwards [kp_enorm_perp_ae hs he (kp_abs_ae_lt_top hκ₀ hρ₀ hm₀)] with ω hω
    rw [hω]
  rw [lintegral_congr_ae h]
  exact kp_lintegral_abs_eq_top hκ hρ hm

omit [IsProbabilityMeasure ν] in
/-- If `ε` is not almost surely `0`, `E|ε|^κ > 0`. -/
theorem kp_moment_ne_zero {κ : ℝ} (hκ : 0 < κ) (hε : ¬ ∀ᵐ x ∂ν, x.2 = 0) :
    ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ 0 := by
  intro h0
  rw [lintegral_eq_zero_iff (by fun_prop)] at h0
  refine hε (h0.mono fun x hx => ?_)
  have hx' : ‖x.2‖ₑ ^ κ = 0 := hx
  rcases ENNReal.rpow_eq_zero_iff.1 hx' with h | h
  · exact enorm_eq_zero.1 h.1
  · exact absurd h.2 (not_lt.2 hκ.le)

/-- **AKMM, p. 651 (beyond the text): the tail index of `A` is `ζ` in the moment sense.**
Suppose `s, ε ≥ 0`, `ε` not a.s. `0`, and `ζ > 0` is such that `E s^κ < 1` and `E ε^κ < ∞` for
`0 < κ < ζ` and `E s^κ > 1` for `κ > ζ` (as for the root of `E s^ζ = 1`, `kp_moment_root`).
Then `E A^κ < ∞` for `0 < κ < ζ`, `E A^κ = ∞` for `κ > ζ`, and
`sup {κ > 0 : E A^κ < ∞} = ζ`: the exponent a Pareto tail `P(A > a) ∝ a^{−ζ}` would have. -/
theorem kp_tail_index {ζ : ℝ} (hζ : 0 < ζ)
    (hlow : ∀ κ, 0 < κ → κ < ζ → ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1 ∧ ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤)
    (hhigh : ∀ κ, ζ < κ → 1 < ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν)
    (hs : ∀ᵐ x ∂ν, 0 ≤ x.1) (he : ∀ᵐ x ∂ν, 0 ≤ x.2) (hε : ¬ ∀ᵐ x ∂ν, x.2 = 0) :
    (∀ κ, 0 < κ → κ < ζ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν < ⊤) ∧
      (∀ κ, ζ < κ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν = ⊤) ∧
      sSup {κ : ℝ | 0 < κ ∧ ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν < ⊤} = ζ := by
  have h1 : ∀ κ, 0 < κ → κ < ζ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν < ⊤ := fun κ hκ hκζ =>
    kp_lintegral_perp_lt_top hκ (hlow κ hκ hκζ).1 (hlow κ hκ hκζ).2
  have h2 : ∀ κ, ζ < κ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν = ⊤ := by
    intro κ hκ
    have hκ0 : 0 < κ := hζ.trans hκ
    have h0 := hlow (ζ / 2) (by positivity) (by linarith)
    exact kp_lintegral_perp_eq_top hκ0 (hhigh κ hκ) (kp_moment_ne_zero hκ0 hε) hs he
      (by positivity : (0 : ℝ) < ζ / 2) h0.1 h0.2
  refine ⟨h1, h2, ?_⟩
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨ζ / 2, by positivity,
    h1 _ (by positivity) (by linarith)⟩ (fun κ hκ => ?_) (fun w hw => ?_)
  · by_contra hlt
    exact (h2 κ (not_le.1 hlt) ▸ hκ.2).ne rfl
  · refine ⟨(max w 0 + ζ) / 2, ⟨by positivity, h1 _ (by positivity) ?_⟩, ?_⟩
    · have : max w 0 < ζ := max_lt hw hζ
      linarith
    · have : w ≤ max w 0 := le_max_left _ _
      have : max w 0 < ζ := max_lt hw hζ
      linarith

/-! ### Finitely supported shocks: the root `ζ` of `E s^ζ = 1` -/

/-- **AKMM, fn 31: the moment function crosses `1` at its root.** For a finitely supported
`s > 0` (probabilities `pₖ > 0`) not identically `1`, if `ζ > 0` solves `E s^ζ = 1` then
`E s^κ < 1` for `0 < κ < ζ` and `E s^κ > 1` for `κ > ζ` (strict convexity of
`κ ↦ Σₖ pₖ sₖ^κ`, which is `1` at `0` and at `ζ`). -/
theorem kp_moment_root {ι : Type*} [Fintype ι] {p s : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (hs : ∀ k, 0 < s k) (k₀ : ι) (hk₀ : s k₀ ≠ 1) {ζ : ℝ} (hζ : 0 < ζ)
    (hζ1 : ∑ k, p k * s k ^ ζ = 1) :
    (∀ κ, 0 < κ → κ < ζ → ∑ k, p k * s k ^ κ < 1) ∧ (∀ κ, ζ < κ → 1 < ∑ k, p k * s k ^ κ) := by
  have hpt : ∀ k, ∀ z t : ℝ, 0 < z → 0 < t → t < 1 →
      s k ^ (t * z) ≤ (1 - t) + t * s k ^ z ∧
        (s k ≠ 1 → s k ^ (t * z) < (1 - t) + t * s k ^ z) := by
    intro k z t hz ht ht1
    have e1 : Real.log (s k) * (t * z) = (1 - t) • (0 : ℝ) + t • (Real.log (s k) * z) := by
      simp only [smul_eq_mul]
      ring
    rw [Real.rpow_def_of_pos (hs k), Real.rpow_def_of_pos (hs k), e1]
    refine ⟨?_, fun hne => ?_⟩
    · have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log (s k) * z))
        (by linarith : (0 : ℝ) ≤ 1 - t) ht.le (by ring)
      simpa using this
    · have hl : Real.log (s k) ≠ 0 := fun h0 =>
        hne (Real.eq_one_of_pos_of_log_eq_zero (hs k) h0)
      have hne' : (0 : ℝ) ≠ Real.log (s k) * z := (mul_ne_zero hl hz.ne').symm
      have := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log (s k) * z))
        hne' (by linarith : (0 : ℝ) < 1 - t) ht (by ring)
      simpa using this
  have hmix : ∀ z t : ℝ, 0 < z → 0 < t → t < 1 →
      ∑ k, p k * s k ^ (t * z) < (1 - t) + t * ∑ k, p k * s k ^ z := by
    intro z t hz ht ht1
    have h1 : (1 - t) + t * ∑ k, p k * s k ^ z = ∑ k, p k * ((1 - t) + t * s k ^ z) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1]
    apply Finset.sum_lt_sum
    · exact fun k _ => mul_le_mul_of_nonneg_left (hpt k z t hz ht ht1).1 (hp k).le
    · exact ⟨k₀, Finset.mem_univ _,
        mul_lt_mul_of_pos_left ((hpt k₀ z t hz ht ht1).2 hk₀) (hp k₀)⟩
  refine ⟨fun κ hκ hκζ => ?_, fun κ hκ => ?_⟩
  · have := hmix ζ (κ / ζ) hζ (div_pos hκ hζ) ((div_lt_one hζ).2 hκζ)
    rw [show κ / ζ * ζ = κ by field_simp, hζ1] at this
    linarith
  · have hκ0 : 0 < κ := hζ.trans hκ
    have := hmix κ (ζ / κ) hκ0 (div_pos hζ hκ0) ((div_lt_one hκ0).2 hκ)
    rw [show ζ / κ * κ = ζ by field_simp, hζ1] at this
    have h2 : 0 < ζ / κ := div_pos hζ hκ0
    nlinarith

/-- The law of a finitely supported pair `(s, ε)`: `(sₖ, eₖ)` with probability `pₖ`. -/
noncomputable def kp_finite {ι : Type*} [Fintype ι] (p s e : ι → ℝ) : Measure (ℝ × ℝ) :=
  ∑ k, ENNReal.ofReal (p k) • Measure.dirac (s k, e k)

theorem kp_finite_lintegral {ι : Type*} [Fintype ι] (p s e : ι → ℝ) (g : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂kp_finite p s e = ∑ k, ENNReal.ofReal (p k) * g (s k, e k) := by
  simp [kp_finite, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac]

theorem kp_finite_isProb {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (s e : ι → ℝ) : IsProbabilityMeasure (kp_finite p s e) := by
  constructor
  have h := kp_finite_lintegral p s e (fun _ => 1)
  rw [lintegral_one] at h
  rw [h]
  simp only [mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => (hp k).le, hp1, ENNReal.ofReal_one]

theorem kp_finite_ae {ι : Type*} [Fintype ι] {p s e : ι → ℝ} {Q : ℝ × ℝ → Prop}
    (hQ : MeasurableSet {x | Q x}) (h : ∀ k, Q (s k, e k)) : ∀ᵐ x ∂kp_finite p s e, Q x := by
  rw [ae_iff]
  have hc : MeasurableSet {x | ¬ Q x} := hQ.compl
  simp only [kp_finite, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hc, smul_eq_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp [Set.indicator, h k]

/-- **AKMM, p. 651 and fn 31 (beyond the text): a finitely supported instance.** Let `(s, ε)` take
the values `(sₖ, eₖ)` with probabilities `pₖ > 0`, `sₖ > 0` not all `1`, `eₖ ≥ 0` not all `0`, and
let `ζ > 0` solve `E s^ζ = 1` (Kesten's moment condition, fn 31). Then the tail index of the
stationary `A` is exactly `ζ`: `E A^κ < ∞` for `0 < κ < ζ`, `E A^κ = ∞` for `κ > ζ`, and
`sup {κ > 0 : E A^κ < ∞} = ζ`. -/
theorem kp_finite_tail_index {ι : Type*} [Fintype ι] {p s e : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (hs : ∀ k, 0 < s k) (k₀ : ι) (hk₀ : s k₀ ≠ 1) (he : ∀ k, 0 ≤ e k)
    (k₁ : ι) (hk₁ : 0 < e k₁) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ∑ k, p k * s k ^ ζ = 1) :
    (∀ κ, 0 < κ → κ < ζ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P (kp_finite p s e) < ⊤) ∧
      (∀ κ, ζ < κ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P (kp_finite p s e) = ⊤) ∧
      sSup {κ : ℝ | 0 < κ ∧ ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P (kp_finite p s e) < ⊤} = ζ := by
  have := kp_finite_isProb hp hp1 s e
  have hρ : ∀ κ : ℝ, 0 ≤ κ → ∫⁻ x, ‖x.1‖ₑ ^ κ ∂kp_finite p s e =
      ENNReal.ofReal (∑ k, p k * s k ^ κ) := by
    intro κ hκ
    rw [kp_finite_lintegral, ENNReal.ofReal_sum_of_nonneg fun k _ =>
      mul_nonneg (hp k).le (Real.rpow_nonneg (hs k).le _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_mul (hp k).le, Real.enorm_eq_ofReal_abs, abs_of_pos (hs k),
      ENNReal.ofReal_rpow_of_nonneg (hs k).le hκ]
  have hm : ∀ κ : ℝ, 0 ≤ κ → ∫⁻ x, ‖x.2‖ₑ ^ κ ∂kp_finite p s e ≠ ⊤ := by
    intro κ hκ
    rw [kp_finite_lintegral]
    exact ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hκ enorm_ne_top)
  obtain ⟨hlo, hhi⟩ := kp_moment_root hp hp1 hs k₀ hk₀ hζ hζ1
  refine kp_tail_index hζ (fun κ hκ hκζ => ⟨?_, hm κ hκ.le⟩) (fun κ hκ => ?_)
    (kp_finite_ae (measurableSet_le measurable_const measurable_fst) fun k => (hs k).le)
    (kp_finite_ae (measurableSet_le measurable_const measurable_snd) he) ?_
  · rw [hρ κ hκ.le, ENNReal.ofReal_lt_one]
    exact hlo κ hκ hκζ
  · rw [hρ κ (hζ.trans hκ).le, ENNReal.one_lt_ofReal]
    exact hhi κ hκ
  · intro h0
    rw [ae_iff] at h0
    have hpos : 0 < kp_finite p s e {x | ¬ x.2 = 0} := by
      have hc : MeasurableSet {x : ℝ × ℝ | ¬ x.2 = 0} :=
        (measurableSet_eq_fun measurable_snd measurable_const).compl
      simp only [kp_finite, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
        Measure.dirac_apply' _ hc, smul_eq_mul]
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun k _ => bot_le) (Finset.mem_univ k₁))
      simp [Set.indicator, hk₁.ne', hp k₁]
    exact hpos.ne' h0

/-- **AKMM, p. 651 (beyond the text): a two-point example.** `s ∈ {1/2, 3/2}` with
probability `1/2` each and `ε = 1`: Kesten's hypotheses hold (`E log s < 0`, `P(s > 1) > 0`),
`ζ = 1` solves `E s^ζ = 1`, and the tail index of `A` is exactly `1`. -/
theorem kp_two_point :
    (∑ k : Fin 2, (1 / 2 : ℝ) * Real.log (![1 / 2, 3 / 2] k) < 0) ∧ (1 : ℝ) < ![1 / 2, 3 / 2] 1 ∧
      ∑ k : Fin 2, (1 / 2 : ℝ) * ![1 / 2, 3 / 2] k ^ (1 : ℝ) = 1 ∧
      sSup {κ : ℝ | 0 < κ ∧ ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P
        (kp_finite (fun _ : Fin 2 => 1 / 2) ![1 / 2, 3 / 2] fun _ => 1) < ⊤} = 1 := by
  have hroot : ∑ k : Fin 2, (1 / 2 : ℝ) * ![1 / 2, 3 / 2] k ^ (1 : ℝ) = 1 := by
    simp [Fin.sum_univ_two]
    norm_num
  refine ⟨?_, by norm_num, hroot, ?_⟩
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← mul_add, ← Real.log_mul (by norm_num) (by norm_num)]
    have : Real.log (1 / 2 * (3 / 2)) < 0 := Real.log_neg (by norm_num) (by norm_num)
    linarith
  · exact (kp_finite_tail_index (fun _ => by norm_num) (by simp)
      (fun k => by fin_cases k <;> norm_num) 0 (by norm_num) (fun _ => zero_le_one) 0 one_pos
      one_pos hroot).2.2

/-- **AKMM, p. 651 and fn 31 (beyond the text): the tail index is the root of
`ke_moment_exists`.** For finitely supported `(s, ε)` with `pₖ > 0`, `sₖ > 0`, `E log s < 0`,
some `sₖ > 1`, and `eₖ ≥ 0` not all `0`, the root `ζ > 0` of `E s^ζ = 1` given by
`ke_moment_exists` is the tail index of `A`: `sup {κ > 0 : E A^κ < ∞} = ζ`. -/
theorem kp_finite_tail_index_ke {ι : Type*} [Fintype ι] {p s e : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (hs : ∀ k, 0 < s k) (hlog : ∑ k, p k * Real.log (s k) < 0) (k₁ : ι)
    (hk₁ : 1 < s k₁) (he : ∀ k, 0 ≤ e k) (k₂ : ι) (hk₂ : 0 < e k₂) :
    ∃ ζ, 0 < ζ ∧ ke_moment p s ζ = 1 ∧
      sSup {κ : ℝ | 0 < κ ∧ ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P (kp_finite p s e) < ⊤} = ζ := by
  obtain ⟨ζ, hζ, hζ1⟩ := ke_moment_exists hp hp1 hs hlog k₁ hk₁
  exact ⟨ζ, hζ, hζ1, (kp_finite_tail_index hp hp1 hs k₁ hk₁.ne' he k₂ hk₂ hζ hζ1).2.2⟩

/-- AKMM, fn 31: in the two-point example of `kp_two_point` the root of `ke_moment_exists` is
`ζ = 1` (`ke_moment_unique`). -/
theorem kp_two_point_ke {ζ : ℝ} (hζ : 0 < ζ)
    (hζ1 : ke_moment (fun _ : Fin 2 => (1 / 2 : ℝ)) ![1 / 2, 3 / 2] ζ = 1) : ζ = 1 :=
  ke_moment_unique (fun _ => by norm_num) (by simp) (fun k => by fin_cases k <;> norm_num) 0
    (by norm_num) hζ one_pos hζ1 kp_two_point.2.2.1

end AKMM.Inequality
