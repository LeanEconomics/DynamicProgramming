/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NQAR1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Discretising an AR(1) process: the Tauchen method

AKMM, §10.4–10.4.1, pp. 270–271. The AR(1) `z_{t+1} = ρz_t + ε_{t+1}` with `0 < ρ < 1` has
unconditional variance `σ_z² = σ_ε²/(1 − ρ²)` (`ar1_uncond_var`, from Miao's
`nq_ar1_variance_fixed`). Tauchen's matrix on an equally spaced grid with spacing `ω`, for any
distribution function `F` of the normalised shock (`F` nondecreasing with values in `[0, 1]`),
assigns to each interior point the probability of `[z̄ʲ − ω/2, z̄ʲ + ω/2]` and to the end
points the tails (`tauchenProb`); every row is a probability vector (`tauchen_stochastic`).

The interior entries are printed as `F((z̄ʲ − ρz̄ⁱ − ω/2)/σ_ε) − F((z̄ʲ − ρz̄ⁱ + ω/2)/σ_ε)`, the
negative of the probability of the interval: for strictly increasing `F` they are negative and
the rows sum to `1 + 2(F(u₁) − F(u_{N−1})) ≠ 1` (`tauchen_printed_neg`,
`tauchen_printed_row_sum`), with the Cauchy distribution function as a concrete strictly
increasing `F` (`tauchenCauchyCdf_strictMono`). Miao's Gaussian version, with the cells as
measurable sets, is `Miao.NumericalMethods.nq_tauchen_stochastic`.
-/

namespace AKMM.ComputationalTools

open Finset

/-- AKMM, p. 270: "this specification implies the unconditional variance of `z_t` is
`σ_z² = σ_ε²/(1 − ρ²)`": it is the only stationary variance `s = ρ²s + σ_ε²`. -/
theorem ar1_uncond_var {ρ σε s : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    s = ρ ^ 2 * s + σε ^ 2 ↔ s = σε ^ 2 / (1 - ρ ^ 2) :=
  Miao.NumericalMethods.nq_ar1_variance_fixed (by rw [abs_of_pos hρ0]; exact hρ1)

/-- AKMM, p. 270, step 1: the equally spaced grid `z̄ʲ = z̄¹ + (j − 1)ω`, indexed here from
`j = 0`. -/
def tauchenGrid (z₁ ω : ℝ) (j : ℕ) : ℝ := z₁ + j * ω

/-- AKMM, p. 270: with `z̄¹ = −mσ_z` and `ω = 2mσ_z/(N − 1)`, the last point is `z̄ᴺ = mσ_z`. -/
theorem tauchenGrid_last {N : ℕ} (hN : 2 ≤ N) (m σz : ℝ) :
    tauchenGrid (-(m * σz)) (2 * m * σz / (N - 1 : ℕ)) (N - 1) = m * σz := by
  have h : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 1 ≤ N - 1 := by omega
    positivity
  unfold tauchenGrid
  field_simp
  ring

/-- The normalised upper end `(z̄ʲ − ρz̄ⁱ + ω/2)/σ_ε` of the cell of `z̄ʲ`. -/
noncomputable def tauchenUpper (ρ σε z₁ ω zi : ℝ) (j : ℕ) : ℝ :=
  (tauchenGrid z₁ ω j - ρ * zi + ω / 2) / σε

/-- The normalised lower end `(z̄ʲ − ρz̄ⁱ − ω/2)/σ_ε` of the cell of `z̄ʲ`. -/
noncomputable def tauchenLower (ρ σε z₁ ω zi : ℝ) (j : ℕ) : ℝ :=
  (tauchenGrid z₁ ω j - ρ * zi - ω / 2) / σε

/-- Adjacent cells share their boundary: the lower end of `j + 1` is the upper end of `j`. -/
theorem tauchen_lower_succ (ρ σε z₁ ω zi : ℝ) (j : ℕ) :
    tauchenLower ρ σε z₁ ω zi (j + 1) = tauchenUpper ρ σε z₁ ω zi j := by
  unfold tauchenLower tauchenUpper tauchenGrid
  push_cast
  ring

/-- AKMM, p. 271, step 2 (corrected): Tauchen's transition probability from the state with value
`zi` to the grid point `j ∈ {0, …, N − 1}`: `F(u₀)` for the first point, `1 − F(l_{N−1})` for the
last, and `F(u_j) − F(l_j)` in between. -/
noncomputable def tauchenProb (F : ℝ → ℝ) (ρ σε z₁ ω : ℝ) (N : ℕ) (zi : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then F (tauchenUpper ρ σε z₁ ω zi 0)
  else if j = N - 1 then 1 - F (tauchenLower ρ σε z₁ ω zi j)
  else F (tauchenUpper ρ σε z₁ ω zi j) - F (tauchenLower ρ σε z₁ ω zi j)

/-- AKMM, p. 271: each row of Tauchen's matrix is a probability vector, for any distribution
function `F` (nondecreasing, values in `[0, 1]`), spacing `ω ≥ 0`, `σ_ε > 0` and `N ≥ 2`. -/
theorem tauchen_stochastic {F : ℝ → ℝ} (hF : Monotone F) (hF0 : ∀ x, 0 ≤ F x)
    (hF1 : ∀ x, F x ≤ 1) {ρ σε z₁ ω : ℝ} (hσ : 0 < σε) (hω : 0 ≤ ω) {N : ℕ} (hN : 2 ≤ N)
    (zi : ℝ) :
    (∀ j, 0 ≤ tauchenProb F ρ σε z₁ ω N zi j) ∧
      ∑ j ∈ range N, tauchenProb F ρ σε z₁ ω N zi j = 1 := by
  constructor
  · intro j
    unfold tauchenProb
    split_ifs
    · exact hF0 _
    · linarith [hF1 (tauchenLower ρ σε z₁ ω zi j)]
    · refine sub_nonneg.2 (hF ?_)
      unfold tauchenUpper tauchenLower
      gcongr
      linarith
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
    set u : ℕ → ℝ := fun j => F (tauchenUpper ρ σε z₁ ω zi j)
    rw [sum_range_succ, sum_range_succ']
    have hlast : tauchenProb F ρ σε z₁ ω (M + 2) zi (M + 1) = 1 - u M := by
      unfold tauchenProb
      rw [show M + 2 - 1 = M + 1 by omega]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, tauchen_lower_succ, u]
    have hfirst : tauchenProb F ρ σε z₁ ω (M + 2) zi 0 = u 0 := by
      simp [tauchenProb, u]
    have hmid : ∀ k ∈ range M, tauchenProb F ρ σε z₁ ω (M + 2) zi (k + 1) = u (k + 1) - u k := by
      intro k hk
      have hk' := mem_range.1 hk
      unfold tauchenProb
      simp only [Nat.add_one_ne_zero, show k + 1 ≠ M + 2 - 1 by omega, ↓reduceIte,
        tauchen_lower_succ, u]
    rw [sum_congr rfl hmid, sum_range_sub, hlast, hfirst]
    ring

/-- AKMM, p. 271, the interior entries as printed: `F((z̄ʲ − ρz̄ⁱ − ω/2)/σ_ε) − F((z̄ʲ − ρz̄ⁱ +
ω/2)/σ_ε)`. -/
noncomputable def tauchenPrinted (F : ℝ → ℝ) (ρ σε z₁ ω : ℝ) (N : ℕ) (zi : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then F (tauchenUpper ρ σε z₁ ω zi 0)
  else if j = N - 1 then 1 - F (tauchenLower ρ σε z₁ ω zi j)
  else F (tauchenLower ρ σε z₁ ω zi j) - F (tauchenUpper ρ σε z₁ ω zi j)

/-- AKMM, p. 271: the printed interior entries are negative for a strictly increasing `F` and a
grid with positive spacing. -/
theorem tauchen_printed_neg {F : ℝ → ℝ} (hF : StrictMono F) {ρ σε z₁ ω : ℝ} (hσ : 0 < σε)
    (hω : 0 < ω) {N j : ℕ} (hj0 : j ≠ 0) (hjN : j ≠ N - 1) (zi : ℝ) :
    tauchenPrinted F ρ σε z₁ ω N zi j < 0 := by
  unfold tauchenPrinted
  simp only [hj0, hjN, ↓reduceIte, sub_neg]
  apply hF
  unfold tauchenUpper tauchenLower
  gcongr
  linarith

/-- AKMM, p. 271: with the printed interior entries the rows of an `N = M + 2`-point grid sum
to `1 + 2(F(u₀) − F(u_M))`, which differs from `1` whenever `M ≥ 1` and `F` is strictly
increasing. -/
theorem tauchen_printed_row_sum {F : ℝ → ℝ} (hF : StrictMono F) {ρ σε z₁ ω : ℝ} (hσ : 0 < σε)
    (hω : 0 < ω) {M : ℕ} (hM : 1 ≤ M) (zi : ℝ) :
    ∑ j ∈ range (M + 2), tauchenPrinted F ρ σε z₁ ω (M + 2) zi j =
        1 + 2 * (F (tauchenUpper ρ σε z₁ ω zi 0) - F (tauchenUpper ρ σε z₁ ω zi M)) ∧
      ∑ j ∈ range (M + 2), tauchenPrinted F ρ σε z₁ ω (M + 2) zi j < 1 := by
  set u : ℕ → ℝ := fun j => F (tauchenUpper ρ σε z₁ ω zi j)
  have hsum : ∑ j ∈ range (M + 2), tauchenPrinted F ρ σε z₁ ω (M + 2) zi j =
      1 + 2 * (u 0 - u M) := by
    rw [sum_range_succ, sum_range_succ']
    have hlast : tauchenPrinted F ρ σε z₁ ω (M + 2) zi (M + 1) = 1 - u M := by
      unfold tauchenPrinted
      rw [show M + 2 - 1 = M + 1 by omega]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, tauchen_lower_succ, u]
    have hfirst : tauchenPrinted F ρ σε z₁ ω (M + 2) zi 0 = u 0 := by
      simp [tauchenPrinted, u]
    have hmid : ∀ k ∈ range M,
        tauchenPrinted F ρ σε z₁ ω (M + 2) zi (k + 1) = -(u (k + 1) - u k) := by
      intro k hk
      have hk' := mem_range.1 hk
      unfold tauchenPrinted
      simp only [Nat.add_one_ne_zero, show k + 1 ≠ M + 2 - 1 by omega, ↓reduceIte,
        tauchen_lower_succ, u]
      ring
    rw [sum_congr rfl hmid, sum_neg_distrib, sum_range_sub, hlast, hfirst]
    ring
  refine ⟨hsum, ?_⟩
  rw [hsum]
  have : u 0 < u M := by
    apply hF
    unfold tauchenUpper tauchenGrid
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    gcongr
    nlinarith
  linarith

/-- The Cauchy distribution function `1/2 + arctan(x)/π`, a concrete strictly increasing
distribution function with values in `[0, 1]` for the counterexamples. -/
noncomputable def tauchenCauchyCdf (x : ℝ) : ℝ := 1 / 2 + Real.arctan x / Real.pi

/-- The Cauchy distribution function is strictly increasing with values in `[0, 1]`. -/
theorem tauchenCauchyCdf_strictMono :
    StrictMono tauchenCauchyCdf ∧ ∀ x, 0 ≤ tauchenCauchyCdf x ∧ tauchenCauchyCdf x ≤ 1 := by
  refine ⟨fun x y h => ?_, fun x => ?_⟩
  · unfold tauchenCauchyCdf
    have := Real.arctan_strictMono h
    have hpi := Real.pi_pos
    gcongr
  · unfold tauchenCauchyCdf
    have h1 := Real.neg_pi_div_two_lt_arctan x
    have h2 := Real.arctan_lt_pi_div_two x
    have hpi := Real.pi_pos
    constructor
    · rw [← sub_nonneg]
      have : Real.arctan x / Real.pi > -(1 / 2) := by
        rw [gt_iff_lt, lt_div_iff₀ hpi]; linarith
      linarith
    · have : Real.arctan x / Real.pi < 1 / 2 := by
        rw [div_lt_iff₀ hpi]; linarith
      linarith

end AKMM.ComputationalTools
