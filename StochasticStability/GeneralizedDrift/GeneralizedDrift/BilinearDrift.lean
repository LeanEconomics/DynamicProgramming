/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.HistoryDependentDrift
import GeneralizedDrift.ModelNonlinearModels

/-!
# The dependent parameter bilinear model (MT §19.2.4)

Meyn and Tweedie, §19.2.4, pp. 496–498: Theorem 19.2.6 for the dependent parameter bilinear
model `θₖ₊₁ = αθₖ + Zₖ₊₁`, `Yₖ₊₁ = θₖYₖ + Wₖ₊₁` (`dblKernel Γz Γw α`, state `(θ, Y)`), through
the history-dependent drift criterion Theorem 19.2.3. The innovations are read off the path,
`Zₖ₊₁ = θₖ₊₁ − αθₖ` (`dblZ`) and `Wₖ₊₁ = Yₖ₊₁ − θₖYₖ` (`dblW`), so the pathwise bounds hold for
every path; `s = 1/(1 − |α|)` (`dblS`).

**Pathwise bounds.** `abs_prod_le_prod_exp` (19.42); `sum_le_of_ar_bound` and
`abs_prod_theta_le` (19.43); `abs_prod_Ico_theta_le` (19.44); `dbl_Y_expand` ((17.28) along the
path); **`dbl_Y_sq_le` (19.45)**, `Y²ₖ₊₁ ≤ 3Aₖ + 3Bₖ + 3W²ₖ₊₁`, with `Aₖ = dblA`, `Bₖ = dblB`.
`dblSqrtA_succ`, `dblB_succ`, `dblA_succ_le` (the recursions behind the conditional bounds).

**The conditional bounds the book takes from [275]** (p. 497), proved here in integrated form
`∫_G Xₖ₊₁ dP_x ≤ ∫_G (bound) dP_x` for `G ∈ 𝓕ₖ^Φ`, with `ζ = E exp(2s|Z₁| − 2)` (the book's
`ζ_z²` of (19.41)): `dbl_condA` (`E[Aₖ₊₁ | 𝓕ₖ] ≤ ζ{(1 + ε)Aₖ + (1 + ε⁻¹)E[W²] exp(2|α|s|θₖ|)}`),
`dbl_condB` (`E[Bₖ₊₁ | 𝓕ₖ] = ζBₖ`), `dbl_condC` (`E[Cₖ₊₁ | 𝓕ₖ] ≤ |α|Cₖ + (1 − |α|)(E e^{c|Z₁|})^s`
for `Cₖ = exp(c|θₖ|)`, any `c ≥ 0`; the book's is `c = 2|α|s`), and `dbl_condY`
(`E[Y²ₖ₊₁ | 𝓕ₖ] ≤ 3Aₖ + 3Bₖ + 3E[W²]`). The tools are `lintegral_pathKernel_two` and
`setLIntegral_mul_step` (the one-step Markov identity with an `𝓕ₖ^Φ`-measurable weight),
`lintegral_dblKernel`, and the weighted AM–GM step `rpow_mul_le_amgm`.

**The drift (19.37).** `dblVs` (`Vₖ = ε³Yₖ² + ε²Aₖ + Bₖ + Cₖ`), `dbl_drift`:
`E[Vₖ₊₁ | 𝓕ₖ] ≤ λVₖ + L` with `λ = dblLam` the book's `max(…)`; `exists_dblLam_lt_one`: `λ < 1`
for small `ε`; `isCoercive_dblV`; `dblV0`, `dblVs_zero` (`V₀ = v(Φ₀)`, `v` continuous).

**Theorem 19.2.6** (`theorem_19_2_6`): positivity, the unique invariant probability `π`,
geometric ergodicity (`Σₙ rⁿ ‖Pⁿ(x, ·) − π‖ < ∞`), `∫ y² dπ < ∞` and
`|E_x[Yₖ²] − ∫ y² dπ| ≤ M(x)ρᵏ` with `M` continuous.

**Corrections.**
* p. 498: the book takes `Cₖ = exp(2|α|s|θₖ|)` and asserts that `V(y, θ) = ε³y² + exp(2|α|s|θ|)`
  is coercive; for `α = 0` it is `ε³y² + 1`, which is not (`dbl_bookV_not_coercive`). Here
  `Cₖ = exp(2s|θₖ|)`: it dominates the book's `Cₖ`, so the first bound still closes, satisfies
  the third bound (`dbl_condC` with `c = 2s`, finite by (19.41)), and makes `V` coercive for all
  `|α| < 1`.
* p. 498: the first display bounding `E[Vₖ₊₁ | 𝓕ₖ]` has `3ε³Aₖ²`; it is `3ε³Aₖ` (from (19.45);
  the rearranged display uses `Aₖ`).

**Hypotheses.** The book takes the `ψ`-irreducible aperiodic T-chain property "as in the proof of
Proposition 17.3.5", which rests on Proposition 7.4.1 under (7.24); neither Chapter 17's
`GapsBilinear` (where `ψ`-irreducibility is a hypothesis) nor this project proves it, so
`ψ`-irreducibility, aperiodicity and the T-chain property are hypotheses. (DBL2) enters only
through `E W² < ∞` and (19.41) (which gives `E exp(2s|Z₁|) < ∞`).

**Elsewhere.** The CLT and LIL for `Y` and `θ` and the almost sure limit
`(1/N) Σ Yₖ² → ∫ y² dπ` of Theorem 19.2.6 are `theorem_19_2_6_limits` in `BilinearLimits`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal NNReal Topology

/-- `s = 1/(1 − |α|)`. -/
noncomputable def dblS (α : ℝ) : ℝ := (1 - |α|)⁻¹

/-- The parameter innovation `Zₖ₊₁ = θₖ₊₁ − αθₖ`, read off the path. -/
def dblZ (α : ℝ) (ω : ℕ → ℝ × ℝ) (k : ℕ) : ℝ := (ω (k + 1)).1 - α * (ω k).1

/-- The output noise `Wₖ₊₁ = Yₖ₊₁ − θₖYₖ`, read off the path. -/
def dblW (ω : ℕ → ℝ × ℝ) (k : ℕ) : ℝ := (ω (k + 1)).2 - (ω k).1 * (ω k).2

/-- The factor `exp(s|Zᵢ₊₁| − 1)`. -/
noncomputable def dblE (α : ℝ) (ω : ℕ → ℝ × ℝ) (i : ℕ) : ℝ :=
  Real.exp (dblS α * |dblZ α ω i| - 1)

/-- `√Aₖ = Σⱼ |Wⱼ| exp(|α|s|θⱼ₋₁|) Πᵢ exp(s|Zᵢ| − 1)` (MT p. 497, shifted to start at `0`). -/
noncomputable def dblSqrtA (α : ℝ) (ω : ℕ → ℝ × ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range k, |dblW ω j| * Real.exp (|α| * dblS α * |(ω j).1|) * ∏ i ∈ Ico j k, dblE α ω i

/-- `Aₖ` (MT p. 497). -/
noncomputable def dblA (α : ℝ) (ω : ℕ → ℝ × ℝ) (k : ℕ) : ℝ := dblSqrtA α ω k ^ 2

/-- `Bₖ` (MT p. 497). -/
noncomputable def dblB (α : ℝ) (ω : ℕ → ℝ × ℝ) (k : ℕ) : ℝ :=
  (ω 0).1 ^ 2 * (ω 0).2 ^ 2 * Real.exp (2 * |α| * dblS α * |(ω 0).1|) *
    ∏ i ∈ range k, Real.exp (2 * dblS α * |dblZ α ω i| - 2)

/-- `C⁽ᶜ⁾ₖ = exp(c|θₖ|)`; the book's `Cₖ` is `c = 2|α|s`. -/
noncomputable def dblC (c : ℝ) (ω : ℕ → ℝ × ℝ) (k : ℕ) : ℝ := Real.exp (c * |(ω k).1|)

/-- `s > 0`. -/
theorem dblS_pos {α : ℝ} (hα : |α| < 1) : 0 < dblS α := inv_pos.2 (by linarith)

/-- (19.42): `|Πᵢ xᵢ| ≤ Πᵢ exp(|xᵢ| − 1)`, from `x ≤ e⁻¹eˣ`. -/
theorem abs_prod_le_prod_exp (s : Finset ℕ) (x : ℕ → ℝ) :
    |∏ i ∈ s, x i| ≤ ∏ i ∈ s, Real.exp (|x i| - 1) := by
  rw [Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
  have := Real.add_one_le_exp (|x i| - 1)
  linarith

/-- (19.43) for a sequence: if `tᵢ₊₁ ≤ a tᵢ + zᵢ` with `0 ≤ a < 1`, then
`Σ_{i<n} t_{j+i+1} ≤ (1 − a)⁻¹ (a tⱼ + Σ_{i<n} z_{j+i})`. -/
theorem sum_le_of_ar_bound {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {t z : ℕ → ℝ}
    (ht : ∀ i, 0 ≤ t i) (htz : ∀ i, t (i + 1) ≤ a * t i + z i) (j n : ℕ) :
    ∑ i ∈ range n, t (j + i + 1) ≤ (1 - a)⁻¹ * (a * t j + ∑ i ∈ range n, z (j + i)) := by
  have h1 : ∑ i ∈ range n, t (j + i + 1) ≤
      a * ∑ i ∈ range n, t (j + i) + ∑ i ∈ range n, z (j + i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => htz (j + i)
  have h2 : ∑ i ∈ range n, t (j + i) ≤ t j + ∑ i ∈ range n, t (j + i + 1) := by
    cases n with
    | zero => simp [ht j]
    | succ m =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ (fun i => t (j + i + 1))]
      have := ht (j + m + 1)
      simp only [add_zero]
      have e : ∀ i, t (j + (i + 1)) = t (j + i + 1) := fun i => by rw [add_assoc]
      simp only [e]
      linarith
  rw [le_inv_mul_iff₀ (by linarith)]
  nlinarith

/-- (19.43)–(19.44) along the path:
`|Π_{i<n} θ_{j+i+1}| ≤ exp(|α|s|θⱼ|) Π_{i<n} exp(s|Z_{j+i+1}| − 1)`. -/
theorem abs_prod_theta_le {α : ℝ} (hα : |α| < 1) (ω : ℕ → ℝ × ℝ) (j n : ℕ) :
    |∏ i ∈ range n, (ω (j + i + 1)).1| ≤
      Real.exp (|α| * dblS α * |(ω j).1|) * ∏ i ∈ range n, dblE α ω (j + i) := by
  have hs := dblS_pos hα
  have hsum := sum_le_of_ar_bound (abs_nonneg α) hα (t := fun i => |(ω i).1|)
    (z := fun i => |dblZ α ω i|) (fun i => abs_nonneg _) (fun i => by
      have : (ω (i + 1)).1 = α * (ω i).1 + dblZ α ω i := by simp only [dblZ]; ring
      rw [this]
      calc |α * (ω i).1 + dblZ α ω i| ≤ |α * (ω i).1| + |dblZ α ω i| := abs_add_le _ _
        _ = |α| * |(ω i).1| + |dblZ α ω i| := by rw [abs_mul]) j n
  refine (abs_prod_le_prod_exp _ _).trans ?_
  simp only [dblE]
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have : dblS α = (1 - |α|)⁻¹ := rfl
  rw [this] at hs ⊢
  nlinarith [mul_le_mul_of_nonneg_left (le_refl (∑ i ∈ range n, |dblZ α ω (j + i)|)) hs.le]

/-- (17.28) along the path: `Yₖ₊₁ = Wₖ₊₁ + Σ_{j<k} (Π_{i=j+1}^{k} θᵢ) Wⱼ₊₁ + (Π_{i ≤ k} θᵢ) Y₀`. -/
theorem dbl_Y_expand (ω : ℕ → ℝ × ℝ) (k : ℕ) :
    (ω (k + 1)).2 = dblW ω k + ∑ j ∈ range k, (∏ i ∈ Ico (j + 1) (k + 1), (ω i).1) * dblW ω j +
      (∏ i ∈ range (k + 1), (ω i).1) * (ω 0).2 := by
  induction k with
  | zero => simp [dblW]
  | succ k ih =>
    have hY : (ω (k + 1 + 1)).2 = dblW ω (k + 1) + (ω (k + 1)).1 * (ω (k + 1)).2 := by
      simp only [dblW]; ring
    rw [hY, ih, Finset.sum_range_succ, Finset.prod_range_succ _ (k + 1)]
    have hsum : ∑ j ∈ range k, (∏ i ∈ Ico (j + 1) (k + 1 + 1), (ω i).1) * dblW ω j =
        (ω (k + 1)).1 * ∑ j ∈ range k, (∏ i ∈ Ico (j + 1) (k + 1), (ω i).1) * dblW ω j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.prod_Ico_succ_top (by have := Finset.mem_range.1 hj; omega)]
      ring
    rw [hsum, Nat.Ico_succ_singleton (k + 1),
      Finset.prod_singleton]
    ring

/-- `|Π_{i=j+1}^{k} θᵢ| ≤ exp(|α|s|θⱼ|) Π_{i=j}^{k-1} exp(s|Zᵢ₊₁| − 1)`, (19.44). -/
theorem abs_prod_Ico_theta_le {α : ℝ} (hα : |α| < 1) (ω : ℕ → ℝ × ℝ) {j k : ℕ} (hjk : j ≤ k) :
    |∏ i ∈ Ico (j + 1) (k + 1), (ω i).1| ≤
      Real.exp (|α| * dblS α * |(ω j).1|) * ∏ i ∈ Ico j k, dblE α ω i := by
  rw [Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range (f := dblE α ω),
    show k + 1 - (j + 1) = k - j by omega]
  have e : ∀ i, j + 1 + i = j + i + 1 := fun i => by omega
  simp only [e]
  exact abs_prod_theta_le hα ω j (k - j)

/-- `(x + y)² ≤ (1 + ε)x² + (1 + ε⁻¹)y²`. -/
theorem sq_add_le_eps {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    (x + y) ^ 2 ≤ (1 + ε) * x ^ 2 + (1 + ε⁻¹) * y ^ 2 := by
  have h : 0 ≤ (ε * x - y) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
  have e : (1 + ε) * x ^ 2 + (1 + ε⁻¹) * y ^ 2 - (x + y) ^ 2 = (ε * x - y) ^ 2 / ε := by
    field_simp; ring
  linarith

/-- **(19.45)** (MT p. 497): `Y²ₖ₊₁ ≤ 3Aₖ + 3Bₖ + 3W²ₖ₊₁`, for every path. -/
theorem dbl_Y_sq_le {α : ℝ} (hα : |α| < 1) (ω : ℕ → ℝ × ℝ) (k : ℕ) :
    (ω (k + 1)).2 ^ 2 ≤ 3 * dblA α ω k + 3 * dblB α ω k + 3 * dblW ω k ^ 2 := by
  set u := ∑ j ∈ range k, (∏ i ∈ Ico (j + 1) (k + 1), (ω i).1) * dblW ω j with hu
  set v := (∏ i ∈ range (k + 1), (ω i).1) * (ω 0).2 with hv
  have hu' : |u| ≤ dblSqrtA α ω k := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hjk : j ≤ k := (Finset.mem_range.1 hj).le
    rw [abs_mul]
    have h := abs_prod_Ico_theta_le hα ω hjk
    calc |∏ i ∈ Ico (j + 1) (k + 1), (ω i).1| * |dblW ω j|
        ≤ Real.exp (|α| * dblS α * |(ω j).1|) * (∏ i ∈ Ico j k, dblE α ω i) * |dblW ω j| :=
          mul_le_mul_of_nonneg_right h (abs_nonneg _)
      _ = _ := by ring
  have hv' : v ^ 2 ≤ dblB α ω k := by
    have hθ := abs_prod_theta_le hα ω 0 k
    simp only [zero_add] at hθ
    have hsq : (∏ i ∈ range k, (ω (i + 1)).1) ^ 2 ≤
        (Real.exp (|α| * dblS α * |(ω 0).1|) * ∏ i ∈ range k, dblE α ω i) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
    have hE : (Real.exp (|α| * dblS α * |(ω 0).1|) * ∏ i ∈ range k, dblE α ω i) ^ 2 =
        Real.exp (2 * |α| * dblS α * |(ω 0).1|) *
          ∏ i ∈ range k, Real.exp (2 * dblS α * |dblZ α ω i| - 2) := by
      rw [mul_pow, ← Finset.prod_pow]
      congr 1
      · rw [sq, ← Real.exp_add]; ring_nf
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [dblE, sq, ← Real.exp_add]; ring_nf
    rw [hv, Finset.prod_range_succ', dblB]
    calc ((∏ i ∈ range k, (ω (i + 1)).1) * (ω 0).1 * (ω 0).2) ^ 2
        = (ω 0).1 ^ 2 * (ω 0).2 ^ 2 * (∏ i ∈ range k, (ω (i + 1)).1) ^ 2 := by ring
      _ ≤ (ω 0).1 ^ 2 * (ω 0).2 ^ 2 *
          (Real.exp (|α| * dblS α * |(ω 0).1|) * ∏ i ∈ range k, dblE α ω i) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by rw [hE]; ring
  have huA : u ^ 2 ≤ dblA α ω k := by
    rw [dblA, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hu' 2
  rw [dbl_Y_expand ω k, ← hu, ← hv]
  nlinarith [sq_nonneg (dblW ω k - u), sq_nonneg (u - v), sq_nonneg (dblW ω k - v)]

/-- The recursion `√Aₖ₊₁ = exp(s|Zₖ₊₁| − 1)(√Aₖ + |Wₖ₊₁| exp(|α|s|θₖ|))`. -/
theorem dblSqrtA_succ (α : ℝ) (ω : ℕ → ℝ × ℝ) (k : ℕ) :
    dblSqrtA α ω (k + 1) =
      dblE α ω k * (dblSqrtA α ω k + |dblW ω k| * Real.exp (|α| * dblS α * |(ω k).1|)) := by
  unfold dblSqrtA
  rw [Finset.sum_range_succ, Nat.Ico_succ_singleton, Finset.prod_singleton, mul_add,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.prod_Ico_succ_top (Finset.mem_range.1 hj).le]
    ring
  · ring

/-- `Bₖ₊₁ = Bₖ exp(2s|Zₖ₊₁| − 2)`. -/
theorem dblB_succ (α : ℝ) (ω : ℕ → ℝ × ℝ) (k : ℕ) :
    dblB α ω (k + 1) = dblB α ω k * Real.exp (2 * dblS α * |dblZ α ω k| - 2) := by
  unfold dblB
  rw [Finset.prod_range_succ]
  ring

/-- `exp(s|Z| − 1)² = exp(2s|Z| − 2)`. -/
theorem dblE_sq (α : ℝ) (ω : ℕ → ℝ × ℝ) (i : ℕ) :
    dblE α ω i ^ 2 = Real.exp (2 * dblS α * |dblZ α ω i| - 2) := by
  rw [dblE, sq, ← Real.exp_add]; ring_nf

/-- The pathwise bound behind the first conditional bound of p. 497: for `ε > 0`,
`Aₖ₊₁ ≤ exp(2s|Zₖ₊₁| − 2) ((1 + ε)Aₖ + (1 + ε⁻¹) W²ₖ₊₁ exp(2|α|s|θₖ|))`. -/
theorem dblA_succ_le (α : ℝ) (ω : ℕ → ℝ × ℝ) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    dblA α ω (k + 1) ≤ Real.exp (2 * dblS α * |dblZ α ω k| - 2) *
      ((1 + ε) * dblA α ω k + (1 + ε⁻¹) * dblW ω k ^ 2 *
        Real.exp (2 * |α| * dblS α * |(ω k).1|)) := by
  rw [dblA, dblSqrtA_succ, mul_pow, dblE_sq]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h := sq_add_le_eps hε (dblSqrtA α ω k) (|dblW ω k| * Real.exp (|α| * dblS α * |(ω k).1|))
  have e : (|dblW ω k| * Real.exp (|α| * dblS α * |(ω k).1|)) ^ 2 =
      dblW ω k ^ 2 * Real.exp (2 * |α| * dblS α * |(ω k).1|) := by
    rw [mul_pow, sq_abs, sq (Real.exp _), ← Real.exp_add]; ring_nf
  rw [e] at h
  rw [dblA]
  linarith

variable {X : Type*} [MeasurableSpace X] in
/-- Under `P_x`, `E_x[h(Φ₀, Φ₁)] = ∫ h(x, z) P(x, dz)`. -/
theorem lintegral_pathKernel_two [MeasurableSingletonClass X] (P : Kernel X X) [IsMarkovKernel P]
    (x : X) {h : X × X → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ ω, h (ω 0, ω 1) ∂pathKernel P x = ∫⁻ z, h (x, z) ∂P x := by
  have hx : Measurable fun z => h (x, z) := hh.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_congr_ae (g := fun ω => h (x, ω 1))
    ((ae_pathKernel_zero P x).mono fun ω hω => by rw [hω])]
  have h1 := setLIntegral_succ P (Measure.dirac x) (n := 0) (G := univ) MeasurableSet.univ hx
  rw [Measure.restrict_univ, pathMeasure_dirac] at h1
  exact h1.trans (lintegral_coord_zero P x hx.lintegral_kernel)

variable {X : Type*} [MeasurableSpace X] in
/-- **The one-step Markov identity with a weight from the past.** For `G ∈ 𝓕ₖ^Φ`, an
`𝓕ₖ^Φ`-measurable `g ≥ 0` and measurable `h ≥ 0`,
`∫_G g · h(Φₖ, Φₖ₊₁) dP_x = ∫_G g · ∫ h(Φₖ, z) P(Φₖ, dz) dP_x`. -/
theorem setLIntegral_mul_step [MeasurableSingletonClass X] (P : Kernel X X) [IsMarkovKernel P]
    (x : X) {k : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt k] G)
    {g : (ℕ → X) → ℝ≥0∞} (hg : Measurable[natFilt k] g) {h : X × X → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ ω in G, g ω * h (ω k, ω (k + 1)) ∂pathKernel P x =
      ∫⁻ ω in G, g ω * ∫⁻ z, h (ω k, z) ∂P (ω k) ∂pathKernel P x := by
  have hle := (natFilt (X := X)).le k
  have hF : Measurable[natFilt k] (G.indicator g) := hg.indicator hG
  have hH : Measurable fun ω' : ℕ → X => h (ω' 0, ω' 1) :=
    hh.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  have hm := markov_lintegral_mul P (Measure.dirac x) hF hH
  rw [pathMeasure_dirac] at hm
  calc ∫⁻ ω in G, g ω * h (ω k, ω (k + 1)) ∂pathKernel P x
      = ∫⁻ ω, G.indicator g ω * h (ω k, ω (k + 1)) ∂pathKernel P x := by
        rw [← lintegral_indicator (hle _ hG)]
        refine lintegral_congr fun ω => ?_
        by_cases hω : ω ∈ G <;> simp [hω]
    _ = ∫⁻ ω, G.indicator g ω * ∫⁻ ω', h (ω' 0, ω' 1) ∂pathKernel P (ω k) ∂pathKernel P x := hm
    _ = ∫⁻ ω in G, g ω * ∫⁻ z, h (ω k, z) ∂P (ω k) ∂pathKernel P x := by
        rw [← lintegral_indicator (hle _ hG)]
        refine lintegral_congr fun ω => ?_
        rw [lintegral_pathKernel_two P _ hh]
        by_cases hω : ω ∈ G <;> simp [hω]

/-- The one-step integrals of the bilinear model: `∫ f d(dblKernel)(x) = E f(F(x, (Z, W)))`. -/
theorem lintegral_dblKernel (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz]
    [IsProbabilityMeasure Γw] (α : ℝ) (x : ℝ × ℝ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂dblKernel Γz Γw α x = ∫⁻ p, f (dblStep α (x, p)) ∂(Γz.prod Γw) := by
  have hF := (contDiff_dblStep α).continuous.measurable
  rw [dblKernel, recursionKernel_apply _ hF x,
    lintegral_map (g := fun w : ℝ × ℝ => dblStep α (x, w)) hf
      (hF.comp (measurable_const.prodMk measurable_id))]

/-- `E[g(Z) h(W)] = E g(Z) · E h(W)` for the independent disturbances. -/
theorem lintegral_prod_mul_dbl (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz]
    [IsProbabilityMeasure Γw] {g h : ℝ → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) :
    ∫⁻ p, g p.1 * h p.2 ∂(Γz.prod Γw) = (∫⁻ z, g z ∂Γz) * ∫⁻ w, h w ∂Γw :=
  lintegral_prod_mul hg.aemeasurable hh.aemeasurable

variable {X : Type*} [MeasurableSpace X] in
/-- `Φᵢ` is `𝓕ₖ^Φ`-measurable for `i ≤ k`. -/
theorem measurable_coord_natFilt_le {i k : ℕ} (h : i ≤ k) :
    Measurable[natFilt (X := X) k] fun ω : ℕ → X => ω i :=
  (measurable_coord_natFilt i).mono ((natFilt (X := X)).mono h) le_rfl

/-- `Zᵢ₊₁` is `𝓕ₖ^Φ`-measurable for `i < k`. -/
theorem measurable_dblZ_natFilt (α : ℝ) {i k : ℕ} (h : i < k) :
    Measurable[natFilt k] fun ω => dblZ α ω i := by
  have a := (measurable_coord_natFilt_le (X := ℝ × ℝ) (show i + 1 ≤ k by omega)).fst
  have b := (measurable_coord_natFilt_le (X := ℝ × ℝ) h.le).fst
  unfold dblZ; fun_prop

/-- `Wᵢ₊₁` is `𝓕ₖ^Φ`-measurable for `i < k`. -/
theorem measurable_dblW_natFilt {i k : ℕ} (h : i < k) :
    Measurable[natFilt k] fun ω => dblW ω i := by
  have a := (measurable_coord_natFilt_le (X := ℝ × ℝ) (show i + 1 ≤ k by omega)).snd
  have b := (measurable_coord_natFilt_le (X := ℝ × ℝ) h.le).fst
  have c := (measurable_coord_natFilt_le (X := ℝ × ℝ) h.le).snd
  unfold dblW; fun_prop

/-- `Bₖ` is `𝓕ₖ^Φ`-measurable. -/
theorem measurable_dblB_natFilt (α : ℝ) (k : ℕ) :
    Measurable[natFilt k] fun ω => ENNReal.ofReal (dblB α ω k) := by
  have a := (measurable_coord_natFilt_le (X := ℝ × ℝ) (Nat.zero_le k)).fst
  have b := (measurable_coord_natFilt_le (X := ℝ × ℝ) (Nat.zero_le k)).snd
  have hp : Measurable[natFilt k] fun ω =>
      ∏ i ∈ range k, Real.exp (2 * dblS α * |dblZ α ω i| - 2) :=
    Finset.measurable_prod _ fun i hi => by
      have c := measurable_dblZ_natFilt α (Finset.mem_range.1 hi)
      fun_prop
  unfold dblB; fun_prop

/-- `Aₖ` is `𝓕ₖ^Φ`-measurable. -/
theorem measurable_dblA_natFilt (α : ℝ) (k : ℕ) :
    Measurable[natFilt k] fun ω => ENNReal.ofReal (dblA α ω k) := by
  have hs : Measurable[natFilt k] fun ω => dblSqrtA α ω k := by
    unfold dblSqrtA
    refine Finset.measurable_sum _ fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have a := measurable_dblW_natFilt hj'
    have b := (measurable_coord_natFilt_le (X := ℝ × ℝ) hj'.le).fst
    have hp : Measurable[natFilt k] fun ω => ∏ i ∈ Ico j k, dblE α ω i :=
      Finset.measurable_prod _ fun i hi => by
        have c := measurable_dblZ_natFilt α (Finset.mem_Ico.1 hi).2
        unfold dblE; fun_prop
    fun_prop
  unfold dblA; fun_prop

/-- `θₖ`, `Yₖ` are `𝓕ₖ^Φ`-measurable. -/
theorem measurable_dblCoord_natFilt (k : ℕ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable[natFilt k] fun ω : ℕ → ℝ × ℝ => f (ω k) :=
  hf.comp (measurable_coord_natFilt k)

/-- **The second conditional bound** (MT p. 497): `E[Bₖ₊₁ | 𝓕ₖ^Φ] = ζ Bₖ` with
`ζ = E exp(2s|Z₁| − 2)` (the book's `ζ_z²`, (19.41)), in integrated form. -/
theorem dbl_condB (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz] [IsProbabilityMeasure Γw]
    (α : ℝ) [IsMarkovKernel (dblKernel Γz Γw α)] (x : ℝ × ℝ) {k : ℕ} {G : Set (ℕ → ℝ × ℝ)}
    (hG : MeasurableSet[natFilt k] G) :
    ∫⁻ ω in G, ENNReal.ofReal (dblB α ω (k + 1)) ∂pathKernel (dblKernel Γz Γw α) x =
      (∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz) *
        ∫⁻ ω in G, ENNReal.ofReal (dblB α ω k) ∂pathKernel (dblKernel Γz Γw α) x := by
  set h : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (Real.exp (2 * dblS α * |q.2.1 - α * q.1.1| - 2)) with hhdef
  have hh : Measurable h := by rw [hhdef]; fun_prop
  have hB0 : ∀ ω, 0 ≤ dblB α ω k := fun ω => by unfold dblB; positivity
  have e : ∀ ω, ENNReal.ofReal (dblB α ω (k + 1)) =
      ENNReal.ofReal (dblB α ω k) * h (ω k, ω (k + 1)) := fun ω => by
    rw [dblB_succ, ENNReal.ofReal_mul (hB0 ω)]; rfl
  simp_rw [e]
  rw [setLIntegral_mul_step _ x hG (measurable_dblB_natFilt α k) hh]
  have hk : ∀ y : ℝ × ℝ, ∫⁻ z, h (y, z) ∂dblKernel Γz Γw α y =
      ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz := by
    intro y
    rw [lintegral_dblKernel _ _ α y (f := fun z => h (y, z))
      (hh.comp (measurable_const.prodMk measurable_id))]
    simp only [hhdef, dblStep, add_sub_cancel_left]
    have := lintegral_prod_mul_dbl Γz Γw
      (g := fun z => ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2))) (h := fun _ => 1)
      (by fun_prop) measurable_const
    simpa using this
  simp_rw [hk]
  rw [lintegral_mul_const _ ((measurable_dblB_natFilt α k).mono ((natFilt (X := ℝ × ℝ)).le k)
    le_rfl), mul_comm]

/-- The weighted AM–GM step: `u^a m ≤ a u + (1 − a) m^{1/(1−a)}` for `0 ≤ a < 1`. -/
theorem rpow_mul_le_amgm {a u m : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hu : 0 ≤ u) (hm : 0 ≤ m) :
    u ^ a * m ≤ a * u + (1 - a) * m ^ (1 - a)⁻¹ := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := a) (w₂ := 1 - a) (p₁ := u)
    (p₂ := m ^ (1 - a)⁻¹) ha0 (by linarith) hu (Real.rpow_nonneg hm _) (by ring)
  rwa [← Real.rpow_mul hm, inv_mul_cancel₀ (by linarith), Real.rpow_one] at h

/-- **The third conditional bound** (MT p. 497), for `C⁽ᶜ⁾ₖ = exp(c|θₖ|)`, `c ≥ 0`:
`E[Cₖ₊₁ | 𝓕ₖ^Φ] ≤ |α|Cₖ + (1 − |α|)(E exp(c|Z₁|))^{1/(1−|α|)}`, in integrated form. The book's
`Cₖ` is `c = 2|α|/(1 − |α|)`. -/
theorem dbl_condC (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz] [IsProbabilityMeasure Γw]
    {α : ℝ} (hα : |α| < 1) [IsMarkovKernel (dblKernel Γz Γw α)] {c : ℝ} (hc : 0 ≤ c)
    (hM : ∫⁻ z, ENNReal.ofReal (Real.exp (c * |z|)) ∂Γz ≠ ∞) (x : ℝ × ℝ) {k : ℕ}
    {G : Set (ℕ → ℝ × ℝ)} (hG : MeasurableSet[natFilt k] G) :
    ∫⁻ ω in G, ENNReal.ofReal (dblC c ω (k + 1)) ∂pathKernel (dblKernel Γz Γw α) x ≤
      ENNReal.ofReal |α| *
          ∫⁻ ω in G, ENNReal.ofReal (dblC c ω k) ∂pathKernel (dblKernel Γz Γw α) x +
        ENNReal.ofReal ((1 - |α|) *
          (∫⁻ z, ENNReal.ofReal (Real.exp (c * |z|)) ∂Γz).toReal ^ dblS α) *
          pathKernel (dblKernel Γz Γw α) x G := by
  set M := ∫⁻ z, ENNReal.ofReal (Real.exp (c * |z|)) ∂Γz with hMdef
  set f : ℝ × ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (c * |y.1|)) with hfdef
  have hf : Measurable f := by rw [hfdef]; fun_prop
  have h1 := setLIntegral_succ (dblKernel Γz Γw α) (Measure.dirac x) hG hf
  rw [pathMeasure_dirac] at h1
  have hK : ∀ y : ℝ × ℝ, ∫⁻ z, f z ∂dblKernel Γz Γw α y ≤
      ENNReal.ofReal (|α| * Real.exp (c * |y.1|) + (1 - |α|) * M.toReal ^ dblS α) := by
    intro y
    rw [lintegral_dblKernel _ _ α y hf]
    calc ∫⁻ p, f (dblStep α (y, p)) ∂(Γz.prod Γw)
        ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (c * |y.1|) ^ |α|) *
            ENNReal.ofReal (Real.exp (c * |p.1|)) * 1 ∂(Γz.prod Γw) := by
          refine lintegral_mono fun p => ?_
          rw [mul_one, ← ENNReal.ofReal_mul (by positivity), ← Real.exp_mul, ← Real.exp_add]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          simp only [dblStep]
          have := abs_add_le (α * y.1) p.1
          rw [abs_mul] at this
          nlinarith [abs_nonneg y.1, abs_nonneg α]
      _ = ENNReal.ofReal (Real.exp (c * |y.1|) ^ |α|) * M := by
          have := lintegral_prod_mul_dbl Γz Γw
            (g := fun z => ENNReal.ofReal (Real.exp (c * |y.1|) ^ |α|) *
              ENNReal.ofReal (Real.exp (c * |z|))) (h := fun _ => 1) (by fun_prop)
            measurable_const
          rw [this, lintegral_const_mul _ (by fun_prop)]
          simp [hMdef]
      _ = ENNReal.ofReal (Real.exp (c * |y.1|) ^ |α| * M.toReal) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hM]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (rpow_mul_le_amgm (abs_nonneg α) hα (by positivity)
          ENNReal.toReal_nonneg)
  have hC : ∀ ω, ENNReal.ofReal (dblC c ω (k + 1)) = f (ω (k + 1)) := fun ω => rfl
  simp_rw [hC]
  rw [h1]
  calc ∫⁻ ω in G, ∫⁻ y, f y ∂dblKernel Γz Γw α (ω k) ∂pathKernel (dblKernel Γz Γw α) x
      ≤ ∫⁻ ω in G, (ENNReal.ofReal |α| * ENNReal.ofReal (dblC c ω k) +
          ENNReal.ofReal ((1 - |α|) * M.toReal ^ dblS α)) ∂pathKernel (dblKernel Γz Γw α) x := by
        refine lintegral_mono fun ω => (hK (ω k)).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_add (by positivity) (by
          have := Real.rpow_nonneg (ENNReal.toReal_nonneg (a := M)) (dblS α)
          nlinarith), ENNReal.ofReal_mul (abs_nonneg _)]
        rfl
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ (by
          have := measurable_dblCoord_natFilt k hf
          exact this.mono ((natFilt (X := ℝ × ℝ)).le k) le_rfl), setLIntegral_const]

/-- **The first conditional bound** (MT p. 497): for `ε > 0`,
`E[Aₖ₊₁ | 𝓕ₖ^Φ] ≤ ζ{(1 + ε)Aₖ + (1 + ε⁻¹) E[W²] exp(2|α|s|θₖ|)}`, in integrated form. -/
theorem dbl_condA (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz] [IsProbabilityMeasure Γw]
    (α : ℝ) [IsMarkovKernel (dblKernel Γz Γw α)] {ε : ℝ} (hε : 0 < ε) (x : ℝ × ℝ) {k : ℕ}
    {G : Set (ℕ → ℝ × ℝ)} (hG : MeasurableSet[natFilt k] G) :
    ∫⁻ ω in G, ENNReal.ofReal (dblA α ω (k + 1)) ∂pathKernel (dblKernel Γz Γw α) x ≤
      ENNReal.ofReal (1 + ε) * (∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz) *
        ∫⁻ ω in G, ENNReal.ofReal (dblA α ω k) ∂pathKernel (dblKernel Γz Γw α) x +
      ENNReal.ofReal (1 + ε⁻¹) * (∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz) *
        (∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw) *
        ∫⁻ ω in G, ENNReal.ofReal (Real.exp (2 * |α| * dblS α * |(ω k).1|))
          ∂pathKernel (dblKernel Γz Γw α) x := by
  set P := dblKernel Γz Γw α
  set ζ := ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz with hζ
  set m2 := ∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw with hm2
  set h1 : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal ((1 + ε) * Real.exp (2 * dblS α * |q.2.1 - α * q.1.1| - 2)) with hh1
  set h2 : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ := fun q => ENNReal.ofReal ((1 + ε⁻¹) *
      Real.exp (2 * |α| * dblS α * |q.1.1|)) * ENNReal.ofReal ((q.2.2 - q.1.1 * q.1.2) ^ 2 *
        Real.exp (2 * dblS α * |q.2.1 - α * q.1.1| - 2)) with hh2
  have hm1 : Measurable h1 := by rw [hh1]; fun_prop
  have hm2' : Measurable h2 := by rw [hh2]; fun_prop
  have hle := (natFilt (X := ℝ × ℝ)).le k
  have hA := measurable_dblA_natFilt α k
  have hpt : ∀ ω, ENNReal.ofReal (dblA α ω (k + 1)) ≤
      ENNReal.ofReal (dblA α ω k) * h1 (ω k, ω (k + 1)) + 1 * h2 (ω k, ω (k + 1)) := by
    intro ω
    rw [one_mul, hh1, hh2]
    simp only
    rw [← ENNReal.ofReal_mul (by unfold dblA; positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by unfold dblA; positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((dblA_succ_le α ω k hε).trans (le_of_eq ?_))
    simp only [dblZ, dblW]
    ring
  have hK1 : ∀ y : ℝ × ℝ, ∫⁻ z, h1 (y, z) ∂P y = ENNReal.ofReal (1 + ε) * ζ := by
    intro y
    rw [lintegral_dblKernel _ _ α y (f := fun z => h1 (y, z))
      (hm1.comp (measurable_const.prodMk measurable_id))]
    simp only [hh1, dblStep, add_sub_cancel_left]
    have := lintegral_prod_mul_dbl Γz Γw
      (g := fun z => ENNReal.ofReal ((1 + ε) * Real.exp (2 * dblS α * |z| - 2)))
      (h := fun _ => 1) (by fun_prop) measurable_const
    simp only [mul_one, lintegral_const, measure_univ] at this
    rw [this]
    simp_rw [ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 + ε)]
    rw [lintegral_const_mul _ (by fun_prop)]
  have hK2 : ∀ y : ℝ × ℝ, ∫⁻ z, h2 (y, z) ∂P y = ENNReal.ofReal ((1 + ε⁻¹) *
      Real.exp (2 * |α| * dblS α * |y.1|)) * (ζ * m2) := by
    intro y
    rw [lintegral_dblKernel _ _ α y (f := fun z => h2 (y, z))
      (hm2'.comp (measurable_const.prodMk measurable_id))]
    simp only [hh2, dblStep, add_sub_cancel_left]
    rw [lintegral_const_mul _ (by fun_prop)]
    congr 1
    have := lintegral_prod_mul_dbl Γz Γw
      (g := fun z => ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)))
      (h := fun w => ENNReal.ofReal (w ^ 2)) (by fun_prop) (by fun_prop)
    rw [← this]
    refine lintegral_congr fun p => ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  calc ∫⁻ ω in G, ENNReal.ofReal (dblA α ω (k + 1)) ∂pathKernel P x
      ≤ ∫⁻ ω in G, (ENNReal.ofReal (dblA α ω k) * h1 (ω k, ω (k + 1)) +
          1 * h2 (ω k, ω (k + 1))) ∂pathKernel P x := lintegral_mono fun ω => hpt ω
    _ = ∫⁻ ω in G, ENNReal.ofReal (dblA α ω k) * h1 (ω k, ω (k + 1)) ∂pathKernel P x +
          ∫⁻ ω in G, 1 * h2 (ω k, ω (k + 1)) ∂pathKernel P x := by
        refine lintegral_add_left ?_ _
        exact (hA.mono hle le_rfl).mul (hm1.comp ((measurable_pi_apply k).prodMk
          (measurable_pi_apply (k + 1))))
    _ = ∫⁻ ω in G, ENNReal.ofReal (dblA α ω k) * (ENNReal.ofReal (1 + ε) * ζ) ∂pathKernel P x +
          ∫⁻ ω in G, 1 * (ENNReal.ofReal ((1 + ε⁻¹) * Real.exp (2 * |α| * dblS α * |(ω k).1|)) *
            (ζ * m2)) ∂pathKernel P x := by
        rw [setLIntegral_mul_step P x hG hA hm1,
          setLIntegral_mul_step P x hG measurable_const hm2']
        simp_rw [hK1, hK2]
    _ = _ := by
        simp_rw [one_mul, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 + ε⁻¹)]
        rw [lintegral_mul_const _ (hA.mono hle le_rfl), lintegral_mul_const _ (by
            have := measurable_dblCoord_natFilt k
              (f := fun y => ENNReal.ofReal (1 + ε⁻¹) *
                ENNReal.ofReal (Real.exp (2 * |α| * dblS α * |y.1|))) (by fun_prop)
            exact this.mono hle le_rfl),
          lintegral_const_mul _ (by
            have := measurable_dblCoord_natFilt k
              (f := fun y => ENNReal.ofReal (Real.exp (2 * |α| * dblS α * |y.1|))) (by fun_prop)
            exact this.mono hle le_rfl)]
        ring

/-- The first part of the drift: `E[Y²ₖ₊₁ | 𝓕ₖ^Φ] ≤ 3Aₖ + 3Bₖ + 3E[W²]`, in integrated form, from
(19.45). -/
theorem dbl_condY (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz] [IsProbabilityMeasure Γw]
    {α : ℝ} (hα : |α| < 1) [IsMarkovKernel (dblKernel Γz Γw α)] (x : ℝ × ℝ) {k : ℕ}
    {G : Set (ℕ → ℝ × ℝ)} (hG : MeasurableSet[natFilt k] G) :
    ∫⁻ ω in G, ENNReal.ofReal ((ω (k + 1)).2 ^ 2) ∂pathKernel (dblKernel Γz Γw α) x ≤
      3 * ∫⁻ ω in G, ENNReal.ofReal (dblA α ω k) ∂pathKernel (dblKernel Γz Γw α) x +
        3 * ∫⁻ ω in G, ENNReal.ofReal (dblB α ω k) ∂pathKernel (dblKernel Γz Γw α) x +
        3 * (∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw) * pathKernel (dblKernel Γz Γw α) x G := by
  set P := dblKernel Γz Γw α
  set hW : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (3 * (q.2.2 - q.1.1 * q.1.2) ^ 2) with hhW
  have hmW : Measurable hW := by rw [hhW]; fun_prop
  have hle := (natFilt (X := ℝ × ℝ)).le k
  have hA := (measurable_dblA_natFilt α k).mono hle le_rfl
  have hB := (measurable_dblB_natFilt α k).mono hle le_rfl
  have hpt : ∀ ω, ENNReal.ofReal ((ω (k + 1)).2 ^ 2) ≤
      3 * ENNReal.ofReal (dblA α ω k) + 3 * ENNReal.ofReal (dblB α ω k) +
        1 * hW (ω k, ω (k + 1)) := by
    intro ω
    rw [one_mul, hhW]
    simp only
    have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by simp
    rw [h3, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by unfold dblA; positivity) (by unfold dblB; positivity),
      ← ENNReal.ofReal_add (by unfold dblA dblB; positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal ((dbl_Y_sq_le hα ω k).trans (le_of_eq (by simp only [dblW])))
  have hKW : ∀ y : ℝ × ℝ, ∫⁻ z, hW (y, z) ∂P y = 3 * ∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw := by
    intro y
    rw [lintegral_dblKernel _ _ α y (f := fun z => hW (y, z))
      (hmW.comp (measurable_const.prodMk measurable_id))]
    simp only [hhW, dblStep]
    have := lintegral_prod_mul_dbl Γz Γw (g := fun _ => 1)
      (h := fun w => ENNReal.ofReal (3 * w ^ 2)) measurable_const (by fun_prop)
    simp only [one_mul, lintegral_const, measure_univ] at this
    have e : ∀ p : ℝ × ℝ, (y.1 * y.2 + p.2 - y.1 * y.2) = p.2 := fun p => by ring
    simp_rw [e, this, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [lintegral_const_mul _ (by fun_prop)]
    simp
  calc ∫⁻ ω in G, ENNReal.ofReal ((ω (k + 1)).2 ^ 2) ∂pathKernel P x
      ≤ ∫⁻ ω in G, (3 * ENNReal.ofReal (dblA α ω k) + 3 * ENNReal.ofReal (dblB α ω k) +
          1 * hW (ω k, ω (k + 1))) ∂pathKernel P x := lintegral_mono fun ω => hpt ω
    _ = ∫⁻ ω in G, (3 * ENNReal.ofReal (dblA α ω k) + 3 * ENNReal.ofReal (dblB α ω k))
          ∂pathKernel P x + ∫⁻ ω in G, 1 * hW (ω k, ω (k + 1)) ∂pathKernel P x :=
        lintegral_add_left ((hA.const_mul 3).add (hB.const_mul 3)) _
    _ = _ := by
        rw [setLIntegral_mul_step P x hG measurable_const hmW, lintegral_add_left
          (hA.const_mul 3), lintegral_const_mul _ hA, lintegral_const_mul _ hB]
        simp_rw [hKW, one_mul]
        rw [setLIntegral_const]

/-- The history-dependent test function `Vₖ = ε³Yₖ² + ε²Aₖ + Bₖ + Cₖ` (MT p. 498), with
`Cₖ = exp(2s|θₖ|)` in place of the book's `exp(2|α|s|θₖ|)` (see the module docstring). -/
noncomputable def dblVs (α ε : ℝ) (k : ℕ) (ω : ℕ → ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (ε ^ 3) * ENNReal.ofReal ((ω k).2 ^ 2) +
    ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (dblA α ω k) + ENNReal.ofReal (dblB α ω k) +
    ENNReal.ofReal (dblC (2 * dblS α) ω k)

/-- The rate `λ` of p. 498. -/
noncomputable def dblLam (α ζ m ε : ℝ) : ℝ :=
  max (max (3 * ε + (1 + ε) * ζ) (3 * ε ^ 3 + ζ)) (|α| + ε ^ 2 * (1 + ε⁻¹) * ζ * m)

/-- `Vₖ` is `𝓕ₖ^Φ`-measurable. -/
theorem measurable_dblVs_natFilt (α ε : ℝ) (k : ℕ) :
    Measurable[natFilt k] (dblVs α ε k) := by
  have hY := measurable_dblCoord_natFilt k (f := fun y => ENNReal.ofReal (y.2 ^ 2)) (by fun_prop)
  have hC := measurable_dblCoord_natFilt k
    (f := fun y => ENNReal.ofReal (Real.exp (2 * dblS α * |y.1|))) (by fun_prop)
  have hA := measurable_dblA_natFilt α k
  have hB := measurable_dblB_natFilt α k
  exact (((hY.const_mul _).add (hA.const_mul _)).add hB).add hC

/-- **The generalized geometric drift (19.37) for the bilinear model** (MT p. 498): for `ε > 0`,
`E[Vₖ₊₁ | 𝓕ₖ^Φ] ≤ λVₖ + L` with `λ = dblLam` and `L = 3ε³E[W²] + (1 − |α|)(E e^{2s|Z|})^s`, in
integrated form. -/
theorem dbl_drift (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz] [IsProbabilityMeasure Γw]
    {α : ℝ} (hα : |α| < 1) [IsMarkovKernel (dblKernel Γz Γw α)]
    (hζ : ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz ≠ ∞)
    (hW : ∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw ≠ ∞)
    (hM : ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z|)) ∂Γz ≠ ∞) {ε : ℝ} (hε : 0 < ε)
    (y : ℝ × ℝ) (k : ℕ) (G : Set (ℕ → ℝ × ℝ)) (hG : MeasurableSet[natFilt k] G) :
    ∫⁻ ω in G, dblVs α ε (k + 1) ω ∂pathKernel (dblKernel Γz Γw α) y ≤
      ENNReal.ofReal (dblLam α (∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz).toReal
        (∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw).toReal ε) *
        ∫⁻ ω in G, dblVs α ε k ω ∂pathKernel (dblKernel Γz Γw α) y +
      ENNReal.ofReal (ε ^ 3 * (3 * (∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw).toReal) + (1 - |α|) *
        (∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z|)) ∂Γz).toReal ^ dblS α) *
        pathKernel (dblKernel Γz Γw α) y G := by
  set P := dblKernel Γz Γw α
  set μ := pathKernel P y
  set ζ := ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz with hζdef
  set m2 := ∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw with hm2def
  set M := ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z|)) ∂Γz with hMdef
  set lam := dblLam α ζ.toReal m2.toReal ε with hlam
  set K := (1 - |α|) * M.toReal ^ dblS α with hK
  have hs := dblS_pos hα
  have hζe : ζ = ENNReal.ofReal ζ.toReal := (ENNReal.ofReal_toReal hζ).symm
  have hm2e : m2 = ENNReal.ofReal m2.toReal := (ENNReal.ofReal_toReal hW).symm
  have hζ0 : 0 ≤ ζ.toReal := ENNReal.toReal_nonneg
  have hm0 : 0 ≤ m2.toReal := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ K := mul_nonneg (by linarith [abs_nonneg α])
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hlam0 : 0 ≤ lam := le_trans (by positivity) (le_trans (le_max_right _ _)
    (le_max_left _ _) : 3 * ε ^ 3 + ζ.toReal ≤ lam)
  have hle := (natFilt (X := ℝ × ℝ)).le
  -- measurability of the pieces
  have mY : ∀ j, Measurable fun ω : ℕ → ℝ × ℝ => ENNReal.ofReal ((ω j).2 ^ 2) := fun j =>
    (measurable_dblCoord_natFilt j (f := fun y => ENNReal.ofReal (y.2 ^ 2))
      (by fun_prop)).mono (hle j) le_rfl
  have mC : ∀ j, Measurable fun ω : ℕ → ℝ × ℝ => ENNReal.ofReal (dblC (2 * dblS α) ω j) :=
    fun j => (measurable_dblCoord_natFilt j
      (f := fun y => ENNReal.ofReal (Real.exp (2 * dblS α * |y.1|))) (by fun_prop)).mono
      (hle j) le_rfl
  have mA : ∀ j, Measurable fun ω => ENNReal.ofReal (dblA α ω j) := fun j =>
    (measurable_dblA_natFilt α j).mono (hle j) le_rfl
  have mB : ∀ j, Measurable fun ω => ENNReal.ofReal (dblB α ω j) := fun j =>
    (measurable_dblB_natFilt α j).mono (hle j) le_rfl
  have hsplit : ∀ j, ∫⁻ ω in G, dblVs α ε j ω ∂μ =
      ENNReal.ofReal (ε ^ 3) * ∫⁻ ω in G, ENNReal.ofReal ((ω j).2 ^ 2) ∂μ +
      ENNReal.ofReal (ε ^ 2) * ∫⁻ ω in G, ENNReal.ofReal (dblA α ω j) ∂μ +
      ∫⁻ ω in G, ENNReal.ofReal (dblB α ω j) ∂μ +
      ∫⁻ ω in G, ENNReal.ofReal (dblC (2 * dblS α) ω j) ∂μ := fun j => by
    unfold dblVs
    rw [lintegral_add_right _ (mC j), lintegral_add_right _ (mB j),
      lintegral_add_right _ ((mA j).const_mul _), lintegral_const_mul _ (mY j),
      lintegral_const_mul _ (mA j)]
  -- the four conditional bounds
  have hY := dbl_condY Γz Γw hα y hG
  have hA := dbl_condA Γz Γw α hε y hG
  have hB := dbl_condB Γz Γw α y hG
  have hC := dbl_condC Γz Γw hα (c := 2 * dblS α) (by positivity) hM y hG
  have hE : ∫⁻ ω in G, ENNReal.ofReal (Real.exp (2 * |α| * dblS α * |(ω k).1|)) ∂μ ≤
      ∫⁻ ω in G, ENNReal.ofReal (dblC (2 * dblS α) ω k) ∂μ := by
    refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : |α| * |(ω k).1| ≤ |(ω k).1| :=
      mul_le_of_le_one_left (abs_nonneg _) hα.le
    nlinarith
  set IY := ∫⁻ ω in G, ENNReal.ofReal ((ω k).2 ^ 2) ∂μ
  set IA := ∫⁻ ω in G, ENNReal.ofReal (dblA α ω k) ∂μ
  set IB := ∫⁻ ω in G, ENNReal.ofReal (dblB α ω k) ∂μ
  set IC := ∫⁻ ω in G, ENNReal.ofReal (dblC (2 * dblS α) ω k) ∂μ
  set p := μ G
  have hA' : ∫⁻ ω in G, ENNReal.ofReal (dblA α ω (k + 1)) ∂μ ≤
      ENNReal.ofReal (1 + ε) * ζ * IA + ENNReal.ofReal (1 + ε⁻¹) * ζ * m2 * IC :=
    hA.trans (add_le_add le_rfl (mul_le_mul' le_rfl hE))
  -- the coefficients
  have cA : ENNReal.ofReal (ε ^ 3) * 3 + ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (1 + ε) * ζ) ≤
      ENNReal.ofReal lam * ENNReal.ofReal (ε ^ 2) := by
    rw [hζe, ← ENNReal.ofReal_mul (p := 1 + ε) (by linarith),
      ← ENNReal.ofReal_mul (p := ε ^ 2) (by positivity), ← ENNReal.ofReal_ofNat (n := 3),
      ← ENNReal.ofReal_mul (p := ε ^ 3) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (p := lam) hlam0]
    refine ENNReal.ofReal_le_ofReal ?_
    have h : 3 * ε + (1 + ε) * ζ.toReal ≤ lam :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    calc ε ^ 3 * 3 + ε ^ 2 * ((1 + ε) * ζ.toReal) = ε ^ 2 * (3 * ε + (1 + ε) * ζ.toReal) := by
          ring
      _ ≤ ε ^ 2 * lam := mul_le_mul_of_nonneg_left h (by positivity)
      _ = lam * ε ^ 2 := by ring
  have cB : ENNReal.ofReal (ε ^ 3) * 3 + ζ ≤ ENNReal.ofReal lam := by
    rw [hζe, ← ENNReal.ofReal_ofNat (n := 3), ← ENNReal.ofReal_mul (p := ε ^ 3) (by positivity),
      ← ENNReal.ofReal_add (by positivity) hζ0]
    refine ENNReal.ofReal_le_ofReal ?_
    have h : 3 * ε ^ 3 + ζ.toReal ≤ lam := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have cC : ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (1 + ε⁻¹) * ζ * m2) + ENNReal.ofReal |α| ≤
      ENNReal.ofReal lam := by
    have hε1 : 0 ≤ 1 + ε⁻¹ := by positivity
    rw [hζe, hm2e, ← ENNReal.ofReal_mul (p := 1 + ε⁻¹) hε1,
      ← ENNReal.ofReal_mul (p := (1 + ε⁻¹) * ζ.toReal) (by positivity),
      ← ENNReal.ofReal_mul (p := ε ^ 2) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h : |α| + ε ^ 2 * (1 + ε⁻¹) * ζ.toReal * m2.toReal ≤ lam := le_max_right _ _
    linarith
  have cp : ENNReal.ofReal (ε ^ 3) * (3 * m2) + ENNReal.ofReal K =
      ENNReal.ofReal (ε ^ 3 * (3 * m2.toReal) + K) := by
    rw [hm2e, ← ENNReal.ofReal_ofNat (n := 3), ← ENNReal.ofReal_mul (p := 3) (by norm_num),
      ← ENNReal.ofReal_mul (p := ε ^ 3) (by positivity),
      ← ENNReal.ofReal_add (by positivity) hK0, ENNReal.toReal_ofReal hm0]
  rw [hsplit (k + 1), hsplit k]
  calc ENNReal.ofReal (ε ^ 3) * ∫⁻ ω in G, ENNReal.ofReal ((ω (k + 1)).2 ^ 2) ∂μ +
        ENNReal.ofReal (ε ^ 2) * ∫⁻ ω in G, ENNReal.ofReal (dblA α ω (k + 1)) ∂μ +
        ∫⁻ ω in G, ENNReal.ofReal (dblB α ω (k + 1)) ∂μ +
        ∫⁻ ω in G, ENNReal.ofReal (dblC (2 * dblS α) ω (k + 1)) ∂μ
      ≤ ENNReal.ofReal (ε ^ 3) * (3 * IA + 3 * IB + 3 * m2 * p) +
        ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (1 + ε) * ζ * IA +
          ENNReal.ofReal (1 + ε⁻¹) * ζ * m2 * IC) + ζ * IB +
        (ENNReal.ofReal |α| * IC + ENNReal.ofReal K * p) :=
        add_le_add (add_le_add (add_le_add (mul_le_mul' le_rfl hY) (mul_le_mul' le_rfl hA'))
          hB.le) hC
    _ = (ENNReal.ofReal (ε ^ 3) * 3 + ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (1 + ε) * ζ)) *
          IA + (ENNReal.ofReal (ε ^ 3) * 3 + ζ) * IB +
        (ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (1 + ε⁻¹) * ζ * m2) + ENNReal.ofReal |α|) *
          IC + (ENNReal.ofReal (ε ^ 3) * (3 * m2) + ENNReal.ofReal K) * p := by ring
    _ ≤ ENNReal.ofReal lam * ENNReal.ofReal (ε ^ 2) * IA + ENNReal.ofReal lam * IB +
          ENNReal.ofReal lam * IC + ENNReal.ofReal (ε ^ 3 * (3 * m2.toReal) + K) * p := by
        rw [← cp]
        exact add_le_add (add_le_add (add_le_add (mul_le_mul' cA le_rfl) (mul_le_mul' cB le_rfl))
          (mul_le_mul' cC le_rfl)) le_rfl
    _ = ENNReal.ofReal lam * (ENNReal.ofReal (ε ^ 2) * IA + IB + IC) +
          ENNReal.ofReal (ε ^ 3 * (3 * m2.toReal) + K) * p := by ring
    _ ≤ _ := by
        gcongr
        exact le_add_self

/-- `V₀ = v(Φ₀)`: `v(θ, y) = ε³y² + θ²y² exp(2|α|s|θ|) + exp(2s|θ|)` (`A₀ = 0`). -/
noncomputable def dblV0 (α ε : ℝ) (x : ℝ × ℝ) : ℝ :=
  ε ^ 3 * x.2 ^ 2 + x.1 ^ 2 * x.2 ^ 2 * Real.exp (2 * |α| * dblS α * |x.1|) +
    Real.exp (2 * dblS α * |x.1|)

/-- `v` is continuous. -/
theorem continuous_dblV0 (α ε : ℝ) : Continuous (dblV0 α ε) := by
  unfold dblV0; fun_prop

/-- `V₀ = v(Φ₀)`. -/
theorem dblVs_zero (α : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (ω : ℕ → ℝ × ℝ) :
    dblVs α ε 0 ω = ENNReal.ofReal (dblV0 α ε (ω 0)) := by
  unfold dblVs dblV0 dblA dblSqrtA dblB dblC
  simp only [Finset.sum_range_zero, Finset.prod_range_zero, mul_one, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.ofReal_zero, mul_zero, add_zero]
  rw [ENNReal.ofReal_add (by have := pow_nonneg hε 3; positivity) (by positivity),
    ENNReal.ofReal_add (by have := pow_nonneg hε 3; positivity) (by positivity),
    ENNReal.ofReal_mul (p := ε ^ 3) (pow_nonneg hε 3)]

/-- The test function `V(θ, y) = ε³y² + exp(2s|θ|)` is coercive (`ε > 0`). -/
theorem isCoercive_dblV {α ε : ℝ} (hα : |α| < 1) (hε : 0 < ε) :
    IsCoercive fun x : ℝ × ℝ => (ε ^ 3 * x.2 ^ 2 + Real.exp (2 * dblS α * |x.1|)).toNNReal := by
  intro r
  have hs := dblS_pos hα
  set R : ℝ := r / (2 * dblS α) + 1 + r / ε ^ 3 with hR
  have hsub : {x : ℝ × ℝ | (ε ^ 3 * x.2 ^ 2 + Real.exp (2 * dblS α * |x.1|)).toNNReal ≤ r} ⊆
      Icc (-R) R ×ˢ Icc (-R) R := by
    intro x hx
    simp only [mem_ofPred_eq, Real.toNNReal_le_iff_le_coe] at hx
    have he := Real.add_one_le_exp (2 * dblS α * |x.1|)
    have hy : ε ^ 3 * x.2 ^ 2 ≤ r := by linarith [Real.exp_pos (2 * dblS α * |x.1|)]
    have hθ : 2 * dblS α * |x.1| ≤ r := by nlinarith [sq_nonneg x.2, pow_pos hε 3]
    have hr0 : (0 : ℝ) ≤ r := r.2
    have h1 : |x.1| ≤ r / (2 * dblS α) := by rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : x.2 ^ 2 ≤ r / ε ^ 3 := by rw [le_div_iff₀ (by positivity)]; linarith
    have h3 : |x.2| ≤ 1 + x.2 ^ 2 := by
      rcases le_or_gt |x.2| 1 with h | h
      · nlinarith [sq_nonneg x.2]
      · nlinarith [sq_abs x.2]
    have hR1 : |x.1| ≤ R := by rw [hR]; have := div_nonneg hr0 (pow_pos hε 3).le; linarith
    have hR2 : |x.2| ≤ R := by
      rw [hR]; have := div_nonneg hr0 (by positivity : (0 : ℝ) ≤ 2 * dblS α); linarith
    exact ⟨abs_le.1 hR1, abs_le.1 hR2⟩
  have hK : IsCompact (Icc (-R) R ×ˢ Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)

/-- **The choice of `ε`** (MT p. 498): under (19.41) and `E W² < ∞`, some `ε > 0` gives `λ < 1`. -/
theorem exists_dblLam_lt_one {α ζ m : ℝ} (hα : |α| < 1) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1) (hm : 0 ≤ m) :
    ∃ ε : ℝ, 0 < ε ∧ dblLam α ζ m ε < 1 := by
  set ε := min (1 / 2) (min ((1 - ζ) / 8) ((1 - |α|) / (4 * (m + 1)))) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (lt_min (by linarith) (div_pos (by linarith)
    (by positivity)))
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hε2 : ε ≤ (1 - ζ) / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ (1 - |α|) / (4 * (m + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at hε3
  refine ⟨ε, hε0, max_lt (max_lt ?_ ?_) ?_⟩
  · have := mul_le_mul_of_nonneg_left hζ.le hε0.le
    linarith
  · have h2 : ε ^ 2 ≤ 1 := by nlinarith
    have : ε ^ 3 ≤ ε := by
      calc ε ^ 3 = ε * ε ^ 2 := by ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left h2 hε0.le
        _ = ε := mul_one _
    linarith
  · have e : ε ^ 2 * (1 + ε⁻¹) = ε ^ 2 + ε := by field_simp
    rw [e]
    have h1 : (ε ^ 2 + ε) * ζ * m ≤ 2 * ε * m := by
      have : ε ^ 2 + ε ≤ 2 * ε := by nlinarith
      have h2 : (ε ^ 2 + ε) * ζ ≤ 2 * ε := by nlinarith
      nlinarith
    nlinarith

/-- **Theorem 19.2.6** (MT p. 496): for the dependent parameter bilinear model with `|α| < 1`,
`ζ = E exp(2|Z₁|/(1 − |α|) − 2) < 1` (19.41) and `E W² < ∞`, if the chain is a `ψ`-irreducible
aperiodic T-chain, then it is positive with a unique invariant probability `π`, it is
geometrically ergodic (`Σₙ rⁿ ‖Pⁿ(x, ·) − π‖ < ∞` for some `r > 1` and every `x`),
`∫ y² dπ < ∞`, and `|E_x[Yₖ²] − ∫ y² dπ| ≤ M(x)ρᵏ` with `M` continuous and `0 < ρ < 1`. -/
theorem theorem_19_2_6 (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz] [IsProbabilityMeasure Γw]
    {α : ℝ} (hα : |α| < 1) [IsMarkovKernel (dblKernel Γz Γw α)] {ψ : Measure (ℝ × ℝ)}
    (hψ : IsMaximalIrreducibility (dblKernel Γz Γw α) ψ) (hap : IsAperiodic (dblKernel Γz Γw α) ψ)
    (hT : IsTChain (dblKernel Γz Γw α))
    (hζ : ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz < 1)
    (hW : ∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw ≠ ∞) :
    IsPositive (dblKernel Γz Γw α) ψ ∧ ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      IsInvariant (dblKernel Γz Γw α) π ∧
      (∀ π' : Measure (ℝ × ℝ), IsProbabilityMeasure π' → IsInvariant (dblKernel Γz Γw α) π' →
        π' = π) ∧
      (∃ r : ℝ≥0∞, 1 < r ∧ ∀ x, ∑' n, r ^ n *
        fNorm (fun _ => 1) ((dblKernel Γz Γw α ^ n) x) π ≠ ∞) ∧
      ∫⁻ z, ENNReal.ofReal (z.2 ^ 2) ∂π ≠ ∞ ∧
      ∃ M : ℝ × ℝ → ℝ, Continuous M ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ x k,
        |∫ z, z.2 ^ 2 ∂(dblKernel Γz Γw α ^ k) x - ∫ z, z.2 ^ 2 ∂π| ≤ M x * ρ ^ k := by
  set P := dblKernel Γz Γw α with hPdef
  set ζ := ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz with hζdef
  have hζt : ζ ≠ ∞ := ne_top_of_lt hζ
  have hs := dblS_pos hα
  have hM : ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z|)) ∂Γz ≠ ∞ := by
    have e : ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z|)) ∂Γz =
        ENNReal.ofReal (Real.exp 2) * ζ := by
      rw [hζdef, ← lintegral_const_mul _ (by fun_prop)]
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      ring_nf
    rw [e]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hζt
  have hζ1 : ζ.toReal < 1 := by
    have := (ENNReal.toReal_lt_toReal hζt ENNReal.one_ne_top).2 hζ
    simpa using this
  obtain ⟨ε, hε, hlam⟩ := exists_dblLam_lt_one hα ENNReal.toReal_nonneg hζ1
    (ENNReal.toReal_nonneg (a := ∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw))
  have hε3 : 0 < ε ^ 3 := pow_pos hε 3
  set V : ℝ × ℝ → ℝ≥0 := fun x => (ε ^ 3 * x.2 ^ 2 + Real.exp (2 * dblS α * |x.1|)).toNNReal
    with hVdef
  have hVm : Measurable V := by rw [hVdef]; fun_prop
  have hVcoe : ∀ x, (V x : ℝ≥0∞) =
      ENNReal.ofReal (ε ^ 3 * x.2 ^ 2 + Real.exp (2 * dblS α * |x.1|)) := fun x => rfl
  have hVV : ∀ k ω, (V (ω k) : ℝ≥0∞) ≤ dblVs α ε k ω := by
    intro k ω
    rw [hVcoe, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (p := ε ^ 3) hε3.le]
    unfold dblVs dblC
    exact add_le_add (le_self_add.trans le_self_add) le_rfl
  have hvc : ∀ K : Set (ℝ × ℝ), IsCompact K → ∃ M : ℝ≥0∞, M ≠ ∞ ∧
      ∀ x ∈ K, ENNReal.ofReal (dblV0 α ε x) ≤ M := fun K hK => by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_dblV0 α ε).continuousOn
    exact ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun x hx => ENNReal.ofReal_le_ofReal
      ((le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hC x hx))⟩
  have hdrift := dbl_drift Γz Γw hα hζt hW hM hε
  have h23 := theorem_19_2_3 hψ hap hT (Vs := dblVs α ε)
    (fun k => (measurable_dblVs_natFilt α ε k).mono ((natFilt (X := ℝ × ℝ)).le k) le_rfl)
    hVm (isCoercive_dblV hα hε) hVV (v := fun x => ENNReal.ofReal (dblV0 α ε x))
    (dblVs_zero α hε.le) hvc (ENNReal.ofReal_lt_one.2 hlam) ENNReal.ofReal_ne_top hdrift
  obtain ⟨hpos, hall⟩ := h23
  obtain ⟨π, hπp, hπ⟩ := hpos.2
  obtain ⟨hfπ, r, hr1, R, hR, hsum⟩ := hall π hπ
  refine ⟨hpos, π, hπp, hπ, fun π' hπ'p hπ' => hpos.invariant_prob_unique hπ' hπ, ?_, ?_, ?_⟩
  · -- geometric ergodicity in total variation
    refine ⟨r, hr1, fun x => ne_top_of_le_ne_top (ENNReal.mul_ne_top hR (ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩)) ((ENNReal.tsum_le_tsum fun n =>
        mul_le_mul' le_rfl (fNorm_mono (fun y => le_add_self) _ _)).trans (hsum x))⟩
  · -- `∫ y² dπ < ∞`
    have hb : ∀ z : ℝ × ℝ, ENNReal.ofReal (z.2 ^ 2) ≤
        ENNReal.ofReal ((ε ^ 3)⁻¹) * ((V z : ℝ≥0∞) + 1) := fun z => by
      calc ENNReal.ofReal (z.2 ^ 2)
          = ENNReal.ofReal ((ε ^ 3)⁻¹) * ENNReal.ofReal (ε ^ 3 * z.2 ^ 2) := by
            rw [← ENNReal.ofReal_mul (inv_nonneg.2 hε3.le), ← mul_assoc,
              inv_mul_cancel₀ hε3.ne', one_mul]
        _ ≤ ENNReal.ofReal ((ε ^ 3)⁻¹) * ((V z : ℝ≥0∞) + 1) := by
            refine mul_le_mul' le_rfl (le_trans ?_ le_self_add)
            rw [hVcoe]
            exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (Real.exp_pos _).le)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfπ)
      ((lintegral_mono hb).trans (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).le)
  · -- the moments
    have := isMarkovKernel_pathKernel P
    have hfinVs : ∀ x k, ∫⁻ ω, dblVs α ε k ω ∂pathKernel P x ≠ ∞ := by
      intro x k
      induction k with
      | zero =>
        rw [lintegral_congr (dblVs_zero α hε.le), lintegral_coord_zero P x
          (continuous_dblV0 α ε).measurable.ennreal_ofReal]
        exact ENNReal.ofReal_ne_top
      | succ k ih =>
        have h := hdrift x k univ MeasurableSet.univ
        simp only [Measure.restrict_univ, measure_univ, mul_one] at h
        exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ih, ENNReal.ofReal_ne_top⟩) h
    have hfm : Measurable fun y => (V y : ℝ≥0∞) + 1 := by fun_prop
    have hfk : ∀ x k, ∫⁻ y, ((V y : ℝ≥0∞) + 1) ∂(P ^ k) x ≠ ∞ := by
      intro x k
      rw [← pathKernel_map_coord P x k, lintegral_map hfm (measurable_pi_apply k),
        lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      refine ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top (hfinVs x k)
        (lintegral_mono fun ω => hVV k ω), ENNReal.one_ne_top⟩
    set g : ℝ × ℝ → ℝ := fun z => ε ^ 3 * z.2 ^ 2 with hgdef
    have hgm : Measurable g := by rw [hgdef]; fun_prop
    have hgle : ∀ z, ENNReal.ofReal |g z| ≤ (V z : ℝ≥0∞) + 1 := fun z => by
      rw [abs_of_nonneg (by positivity), hVcoe]
      exact le_trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (Real.exp_pos _).le))
        le_self_add
    -- the rate
    set r' := min r 2 with hr'
    have hr'1 : 1 < r' := lt_min hr1 (by norm_num)
    have hr't : r' ≠ ∞ := ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
    have hr'r : 1 < r'.toReal := by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hr't).2 hr'1
      simpa using this
    refine ⟨fun x => (ε ^ 3)⁻¹ * R.toReal * (dblV0 α ε x + 1),
      by have := continuous_dblV0 α ε; fun_prop, r'.toReal⁻¹, inv_pos.2 (by linarith),
      inv_lt_one_of_one_lt₀ hr'r, fun x k => ?_⟩
    have hV0 : 0 ≤ dblV0 α ε x := by unfold dblV0; positivity
    have htest : IsFTest (fun y => (V y : ℝ≥0∞) + 1) ((P ^ k) x) π g :=
      ⟨hgm, hgle, integrable_of_ofReal_abs_le hgm hgle (hfk x k),
        integrable_of_ofReal_abs_le hgm hgle hfπ⟩
    have h1 := ofReal_abs_integral_sub_le_fNorm htest
    have h2 : r' ^ k * fNorm (fun y => (V y : ℝ≥0∞) + 1) ((P ^ k) x) π ≤
        R * (ENNReal.ofReal (dblV0 α ε x) + 1) :=
      (mul_le_mul' (pow_le_pow_left₀ zero_le (min_le_left _ _) k) le_rfl).trans
        ((ENNReal.le_tsum k).trans (hsum x))
    set d := ∫ z, g z ∂(P ^ k) x - ∫ z, g z ∂π with hd
    have h3 : ENNReal.ofReal (|d| * r'.toReal ^ k) ≤
        ENNReal.ofReal (R.toReal * (dblV0 α ε x + 1)) := by
      rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (by linarith),
        ENNReal.ofReal_toReal hr't, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hR, ENNReal.ofReal_add hV0 zero_le_one, ENNReal.ofReal_one,
        mul_comm]
      exact (mul_le_mul' le_rfl h1).trans h2
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    have hpos' : 0 < r'.toReal ^ k := pow_pos (by linarith) k
    have h4 : |d| ≤ R.toReal * (dblV0 α ε x + 1) * r'.toReal⁻¹ ^ k := by
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos']
      exact h3
    have hd' : d = ε ^ 3 * (∫ z, z.2 ^ 2 ∂(P ^ k) x - ∫ z, z.2 ^ 2 ∂π) := by
      rw [hd, hgdef, integral_const_mul, integral_const_mul, mul_sub]
    rw [hd', abs_mul, abs_of_pos hε3] at h4
    beta_reduce
    calc |∫ z, z.2 ^ 2 ∂(P ^ k) x - ∫ z, z.2 ^ 2 ∂π|
        ≤ R.toReal * (dblV0 α ε x + 1) * r'.toReal⁻¹ ^ k / ε ^ 3 := by
          rw [le_div_iff₀ hε3]; linarith
      _ = (ε ^ 3)⁻¹ * R.toReal * (dblV0 α ε x + 1) * r'.toReal⁻¹ ^ k := by ring

/-- **Correction** (MT p. 498): with the book's `Cₖ = exp(2|α|s|θₖ|)`, the claimed coercive
`V(y, θ) = ε³y² + exp(2|α|s|θ|)` is not coercive when `α = 0` (then `V = ε³y² + 1`). -/
theorem dbl_bookV_not_coercive (ε : ℝ) :
    ¬ IsCoercive fun x : ℝ × ℝ =>
      (ε ^ 3 * x.2 ^ 2 + Real.exp (2 * |(0 : ℝ)| * dblS 0 * |x.1|)).toNNReal := by
  intro h
  have hK := (h 1).image continuous_fst
  have e : Prod.fst '' closure {x : ℝ × ℝ |
      (ε ^ 3 * x.2 ^ 2 + Real.exp (2 * |(0 : ℝ)| * dblS 0 * |x.1|)).toNNReal ≤ 1} = univ :=
    eq_univ_of_forall fun t => ⟨(t, 0), subset_closure (by simp), rfl⟩
  rw [e] at hK
  exact noncompact_univ ℝ hK

end MeynTweedie.GeneralizedDrift
