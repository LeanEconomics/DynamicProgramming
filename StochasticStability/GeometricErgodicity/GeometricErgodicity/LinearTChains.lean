/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeometricErgodicity.TChainModels
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed

/-!
# Linear models as ψ-irreducible T-chains (MT §6.3.3)

Meyn and Tweedie, §6.3.3, pp. 137–138.

* **Lemma 6.3.4** (p. 137): in a complex Banach algebra, in particular for complex matrices with
  any complete algebra norm, `‖Fᵏ‖^{1/k} → ρ(F)` (`lemma_6_3_4`, Gelfand's formula), the log form
  (6.14) when `ρ(F) > 0` (`lemma_6_3_4_log`), and the bounds (6.15),
  `c⁻¹ ρ₁ᵏ ≤ ‖Fᵏ‖ ≤ c ρ₂ᵏ` for `0 ≤ ρ₁ < ρ(F) < ρ₂` (`lemma_6_3_4_bounds`, with the upper half
  `lemma_6_3_4_upper`). The spectral radius is the largest modulus of an eigenvalue: the spectrum
  of a matrix is the set of roots of its characteristic polynomial
  (`Matrix.mem_spectrum_iff_isRoot_charpoly`).
* `IsStableMatrix F`: the eigenvalue condition (LSS5), `ρ(F) < 1` for `F` as a complex matrix;
  `isStableMatrix_geometric`: then `‖Fᵏx‖ ≤ C rᵏ ‖x‖` with `r < 1`.
* `lss_position_split`, `lss_uniform_reach`: the reachability estimate of the proof of
  Proposition 6.3.5: from every bounded set the chain enters any neighbourhood of
  `x* = Σₖ Fᵏ G w` (`w ∈ supp Γ`) in `N` steps with probability at least `Γ(B(w, ε))ᴺ`.
* **Proposition 6.3.5** (`proposition_6_3_5`, p. 138): under (LSS4), (LSS5) and controllability,
  LSS(F, G) is a `ψ`-irreducible T-chain and every compact set is small.

**Corrections.** In (6.15) the lower bound needs `ρ₁ ≥ 0`: `lemma_6_3_4_bounds_counterexample`
(`F = 0`, `ρ₁ = −1`).

**Hypotheses.** The log form (6.14) is stated for `ρ(F) > 0`: for a nilpotent `F` the book's
`log ρ(F) = −∞` has no counterpart with Lean's `Real.log 0 = 0`.

**Not formalised.** The remark that (LSS5) and (LSS4) are related to Athreya–Pantula's spread-out
condition (commentary, p. 145).
-/

namespace MeynTweedie.GeometricErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal Matrix

/-! ### Lemma 6.3.4: the spectral radius formula -/

/-- **Lemma 6.3.4** (MT p. 137), root form: in a complex Banach algebra (for instance the `n × n`
complex matrices with any complete algebra norm), `‖Fᵏ‖^{1/k} → ρ(F)`, the spectral radius (for a
matrix, the largest modulus of an eigenvalue: `Matrix.mem_spectrum_iff_isRoot_charpoly`). -/
theorem lemma_6_3_4 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] (a : 𝔸) :
    Tendsto (fun k : ℕ => ENNReal.ofReal (‖a ^ k‖ ^ (1 / k : ℝ))) atTop
      (𝓝 (spectralRadius ℂ a)) :=
  spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a

/-- `log(x^{1/k}) = (1/k) log x` for `x ≥ 0`, with Lean's conventions `log 0 = 0`, `1/0 = 0`. -/
theorem log_rpow_one_div {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    Real.log (x ^ (1 / k : ℝ)) = 1 / k * Real.log x := by
  rcases hx.lt_or_eq with hx | hx
  · exact Real.log_rpow hx _
  · subst hx
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · rw [Real.zero_rpow (by positivity)]; simp

/-- **Lemma 6.3.4** (6.14), log form: if `ρ(a) = ρ > 0` then `(1/k) log ‖aᵏ‖ → log ρ`. (For
`ρ = 0` the book's formula reads `−∞ = lim`, which has no counterpart with Lean's `log 0 = 0`.) -/
theorem lemma_6_3_4_log {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (a : 𝔸) {ρ : ℝ} (hρ : 0 < ρ) (h : spectralRadius ℂ a = ENNReal.ofReal ρ) :
    Tendsto (fun k : ℕ => 1 / k * Real.log ‖a ^ k‖) atTop (𝓝 (Real.log ρ)) := by
  have h1 := lemma_6_3_4 a
  rw [h] at h1
  have h2 : Tendsto (fun k : ℕ => ‖a ^ k‖ ^ (1 / k : ℝ)) atTop (𝓝 ρ) := by
    have := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h1
    simp only [Function.comp_def, ENNReal.toReal_ofReal hρ.le] at this
    refine this.congr fun k => ?_
    exact ENNReal.toReal_ofReal (by positivity)
  have h3 := (Real.continuousAt_log hρ.ne').tendsto.comp h2
  refine h3.congr fun k => ?_
  simp only [Function.comp_apply]
  exact log_rpow_one_div (norm_nonneg _) k

/-- The upper half of (6.15): if `ρ(a) = ρ < ρ₂` there is `c ≥ 1` with `‖aᵏ‖ ≤ c ρ₂ᵏ` for every
`k`. -/
theorem lemma_6_3_4_upper {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (a : 𝔸) {ρ ρ₂ : ℝ} (h : spectralRadius ℂ a = ENNReal.ofReal ρ) (h0 : 0 ≤ ρ) (h2 : ρ < ρ₂) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ k : ℕ, ‖a ^ k‖ ≤ c * ρ₂ ^ k := by
  have hρ₂ : 0 < ρ₂ := by linarith
  have hev : ∀ᶠ k : ℕ in atTop, ENNReal.ofReal (‖a ^ k‖ ^ (1 / k : ℝ)) < ENNReal.ofReal ρ₂ := by
    refine (lemma_6_3_4 a).eventually (gt_mem_nhds ?_)
    rw [h]; exact (ENNReal.ofReal_lt_ofReal_iff hρ₂).2 h2
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hup : ∀ k, max N 1 ≤ k → ‖a ^ k‖ ≤ ρ₂ ^ k := fun k hk => by
    have hk1 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have := (ENNReal.ofReal_lt_ofReal_iff hρ₂).1 (hN k (by omega))
    have h3 : (‖a ^ k‖ ^ (1 / k : ℝ)) ^ (k : ℝ) ≤ ρ₂ ^ (k : ℝ) :=
      Real.rpow_le_rpow (by positivity) this.le (by positivity)
    rw [← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hk1.ne', Real.rpow_one,
      Real.rpow_natCast] at h3
    exact h3
  set c₂ : ℝ := 1 + ∑ k ∈ Finset.range (max N 1), ‖a ^ k‖ / ρ₂ ^ k
  have hc₂ : ∀ k, ‖a ^ k‖ ≤ c₂ * ρ₂ ^ k := fun k => by
    have hpow : 0 < ρ₂ ^ k := pow_pos hρ₂ k
    by_cases hk : max N 1 ≤ k
    · calc ‖a ^ k‖ ≤ ρ₂ ^ k := hup k hk
        _ ≤ c₂ * ρ₂ ^ k := by
          refine le_mul_of_one_le_left hpow.le ?_
          have : 0 ≤ ∑ k ∈ Finset.range (max N 1), ‖a ^ k‖ / ρ₂ ^ k :=
            Finset.sum_nonneg fun _ _ => by positivity
          linarith
    · have hmem : k ∈ Finset.range (max N 1) := Finset.mem_range.2 (by omega)
      have hle : ‖a ^ k‖ / ρ₂ ^ k ≤ c₂ := by
        have := Finset.single_le_sum (f := fun k => ‖a ^ k‖ / ρ₂ ^ k)
          (fun _ _ => by positivity) hmem
        linarith
      calc ‖a ^ k‖ = ‖a ^ k‖ / ρ₂ ^ k * ρ₂ ^ k := by field_simp
        _ ≤ c₂ * ρ₂ ^ k := mul_le_mul_of_nonneg_right hle hpow.le
  refine ⟨c₂, ?_, hc₂⟩
  have : 0 ≤ ∑ k ∈ Finset.range (max N 1), ‖a ^ k‖ / ρ₂ ^ k :=
    Finset.sum_nonneg fun _ _ => by positivity
  linarith

/-- **(6.15)** (MT p. 137): if `0 ≤ ρ₁ < ρ(a) < ρ₂` there is `c ≥ 1` with
`c⁻¹ ρ₁ᵏ ≤ ‖aᵏ‖ ≤ c ρ₂ᵏ` for every `k`. -/
theorem lemma_6_3_4_bounds {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (a : 𝔸) {ρ ρ₁ ρ₂ : ℝ} (h : spectralRadius ℂ a = ENNReal.ofReal ρ) (h0 : 0 ≤ ρ₁)
    (h1 : ρ₁ < ρ) (h2 : ρ < ρ₂) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ k : ℕ, c⁻¹ * ρ₁ ^ k ≤ ‖a ^ k‖ ∧ ‖a ^ k‖ ≤ c * ρ₂ ^ k := by
  have hρ₂ : 0 < ρ₂ := by linarith
  obtain ⟨c₂, -, hc₂⟩ := lemma_6_3_4_upper a h (by linarith) h2
  -- the lower bound, from `ρ ≤ ‖aᵏ‖^{1/k} ‖1‖^{1/k}`
  have hρpos : 0 < ρ := by linarith
  have hnt : Nontrivial 𝔸 := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have h3 := spectralRadius_le_nnnorm (𝕜 := ℂ) a
    rw [h, Subsingleton.elim a 0, nnnorm_zero, ENNReal.coe_zero, nonpos_iff_eq_zero,
      ENNReal.ofReal_eq_zero] at h3
    linarith
  have hone : 1 ≤ ‖(1 : 𝔸)‖ := one_le_norm_one 𝔸
  have hlow : ∀ k, ρ₁ ^ k ≤ ‖(1 : 𝔸)‖ * ‖a ^ k‖ := fun k => by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp only [pow_zero]; nlinarith
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h4 := spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ a j
      rw [h, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at h4
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have h5 := ENNReal.rpow_le_rpow h4 hj.le
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hj.ne', ENNReal.rpow_one,
        show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.rpow_natCast,
        ← ENNReal.ofReal_pow hρpos.le, ← ENNReal.coe_mul] at h5
      have h6 : ρ ^ (j + 1) ≤ ‖a ^ (j + 1)‖ * ‖(1 : 𝔸)‖ := by
        rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h5
        simpa using h5
      calc ρ₁ ^ (j + 1) ≤ ρ ^ (j + 1) := pow_le_pow_left₀ h0 h1.le _
        _ ≤ _ := by rw [mul_comm]; exact h6
  refine ⟨max c₂ ‖(1 : 𝔸)‖, le_max_of_le_right hone, fun k => ⟨?_, ?_⟩⟩
  · have hc : 0 < max c₂ ‖(1 : 𝔸)‖ := lt_of_lt_of_le one_pos (le_max_of_le_right hone)
    rw [inv_mul_le_iff₀ hc]
    exact (hlow k).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · exact (hc₂ k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- **Correction to (6.15)** (MT p. 137): the lower bound `c⁻¹ ρ₁ⁿ ≤ ‖Fⁿ‖` needs `ρ₁ ≥ 0`. For
`F = 0` (in `ℂ`, a `1 × 1` matrix), `ρ(F) = 0 < 1` and `ρ₁ = −1 < ρ(F)`, but no `c ≥ 1` has
`c⁻¹ (−1)ⁿ ≤ ‖0ⁿ‖` for `n = 2`. -/
theorem lemma_6_3_4_bounds_counterexample :
    spectralRadius ℂ (0 : ℂ) = ENNReal.ofReal 0 ∧
      ¬ ∃ c : ℝ, 1 ≤ c ∧ ∀ k : ℕ, c⁻¹ * (-1 : ℝ) ^ k ≤ ‖(0 : ℂ) ^ k‖ := by
  refine ⟨le_antisymm ((spectralRadius_le_nnnorm (𝕜 := ℂ) (0 : ℂ)).trans (by simp))
    (by rw [ENNReal.ofReal_zero]; exact zero_le), ?_⟩
  rintro ⟨c, hc, h⟩
  have := h 2
  norm_num at this
  linarith [inv_pos.2 (lt_of_lt_of_le one_pos hc)]

/-! ### The eigenvalue condition (LSS5) -/

variable {n p : ℕ}

/-- **(LSS5)** (MT p. 137): the eigenvalues of `F` lie in the open unit disk, i.e. the spectral
radius of `F`, as a complex matrix, is less than one (`Matrix.mem_spectrum_iff_isRoot_charpoly`:
the spectrum consists of the roots of the characteristic polynomial). -/
def IsStableMatrix (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  spectralRadius ℂ (F.map (algebraMap ℝ ℂ)) < 1

/-- Under (LSS5), `Fᵏ → 0` geometrically (MT p. 137, after (6.15)): `‖Fᵏ x‖ ≤ C rᵏ ‖x‖` with
`r < 1`, for the sup norm on `ℝⁿ`. -/
theorem isStableMatrix_geometric {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ (k : ℕ) (x : Fin n → ℝ),
      ‖(F ^ k) *ᵥ x‖ ≤ C * r ^ k * ‖x‖ := by
  let : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  set Fc := F.map (algebraMap ℝ ℂ)
  have hne : spectralRadius ℂ Fc ≠ ⊤ := ne_top_of_lt hF
  set ρ := (spectralRadius ℂ Fc).toReal
  have hρ : spectralRadius ℂ Fc = ENNReal.ofReal ρ := (ENNReal.ofReal_toReal hne).symm
  have hρ1 : ρ < 1 := by
    have : spectralRadius ℂ Fc < 1 := hF
    rw [hρ, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff one_pos] at this
    exact this
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  obtain ⟨c, hc, hbound⟩ := lemma_6_3_4_upper Fc hρ hρ0 (show ρ < (ρ + 1) / 2 by linarith)
  refine ⟨c, (ρ + 1) / 2, by linarith, by linarith, by linarith, fun k x => ?_⟩
  set xc : Fin n → ℂ := fun i => (x i : ℂ)
  have hxc : ‖xc‖ ≤ ‖x‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
    simp only [xc, Complex.norm_real]; exact norm_le_pi_norm x i
  have hmap : (Fc ^ k) *ᵥ xc = fun i => (((F ^ k) *ᵥ x) i : ℂ) := by
    ext i
    rw [show Fc ^ k = (F ^ k).map (algebraMap ℝ ℂ) from (Matrix.map_pow F _ k).symm]
    exact (RingHom.map_mulVec (algebraMap ℝ ℂ) (F ^ k) x i).symm
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h1 : ‖((F ^ k) *ᵥ x) i‖ = ‖((Fc ^ k) *ᵥ xc) i‖ := by
    rw [hmap, Complex.norm_real]
  rw [h1]
  calc ‖((Fc ^ k) *ᵥ xc) i‖ ≤ ‖(Fc ^ k) *ᵥ xc‖ := norm_le_pi_norm _ i
    _ ≤ ‖Fc ^ k‖ * ‖xc‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ c * ((ρ + 1) / 2) ^ k * ‖x‖ :=
        mul_le_mul (hbound k) hxc (norm_nonneg _) (by positivity)

/-! ### Proposition 6.3.5 -/

/-- The `N`-step position of LSS(F, G) splits as the deterministic path driven by `w`, plus
`C_N (u − w)`: `Fᴺx + Σᵢ F^{N−1−i} G uᵢ = Fᴺx + Σ_{k<N} Fᵏ G w + C_N(u − w)`. -/
theorem lss_position_split (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (N : ℕ) (x : Fin n → ℝ) (w : Fin p → ℝ) (u : Fin N → Fin p → ℝ) :
    (F ^ N) *ᵥ x + ∑ i : Fin N, (F ^ (N - 1 - i) * G) *ᵥ u i =
      (F ^ N) *ᵥ x + (∑ k ∈ Finset.range N, (F ^ k) *ᵥ (G *ᵥ w)) +
        ctrbMap F G N (fun i => u i - w) := by
  rw [ctrbMap_apply, add_assoc]
  congr 1
  have h1 : ∑ i : Fin N, (F ^ (N - 1 - i) * G) *ᵥ u i =
      ∑ i : Fin N, (F ^ (N - 1 - i) * G) *ᵥ w +
        ∑ i : Fin N, (F ^ (N - 1 - (i : ℕ)) * G) *ᵥ (u i - w) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_sub]; abel
  rw [h1]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => (F ^ (N - 1 - i) * G) *ᵥ w) N,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Matrix.mulVec_mulVec]
  have := Finset.mem_range.1 hk
  rw [show N - 1 - (N - 1 - k) = k by omega]

/-- The uniform reachability estimate in the proof of Proposition 6.3.5 (MT p. 138): under (LSS5),
with `w` in the support of `Γ` and `x* = Σₖ Fᵏ G w`, for every `R` and every open `O ∋ x*`
there are `N ≥ 1` and `δ > 0` with `Pᴺ(x₀, O) ≥ δ` whenever `‖x₀‖ ≤ R`. -/
theorem lss_uniform_reach (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} (G : Matrix (Fin n) (Fin p) ℝ) {C r : ℝ} (hC : 0 ≤ C)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hgeo : ∀ (k : ℕ) (x : Fin n → ℝ), ‖(F ^ k) *ᵥ x‖ ≤ C * r ^ k * ‖x‖)
    {w : Fin p → ℝ} (hw : w ∈ Γ.support)
    (hsum : Summable fun k => (F ^ k) *ᵥ (G *ᵥ w)) (R : ℝ) {O : Set (Fin n → ℝ)} (hO : IsOpen O)
    (hxO : (∑' k, (F ^ k) *ᵥ (G *ᵥ w)) ∈ O) :
    ∃ N, 1 ≤ N ∧ ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ x₀ : Fin n → ℝ, ‖x₀‖ ≤ R →
      δ ≤ (lssMatrixKernel Γ F G ^ N) x₀ O := by
  set xs := ∑' k, (F ^ k) *ᵥ (G *ᵥ w)
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hO xs hxO
  -- choose `N`
  have hlim : Tendsto (fun N : ℕ => C * r ^ N * max R 0 +
      ‖xs - ∑ k ∈ Finset.range N, (F ^ k) *ᵥ (G *ᵥ w)‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => C * r ^ N * max R 0) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul C).mul_const
        (max R 0)
      simpa using this
    have h2 : Tendsto (fun N : ℕ => ‖xs - ∑ k ∈ Finset.range N, (F ^ k) *ᵥ (G *ᵥ w)‖) atTop
        (𝓝 0) := by
      have := (hsum.hasSum.tendsto_sum_nat).const_sub xs
      rw [sub_self] at this
      simpa using this.norm
    simpa using h1.add h2
  obtain ⟨N, hN1, hNsmall⟩ := ((eventually_ge_atTop 1).and
    (hlim.eventually (gt_mem_nhds (half_pos hη)))).exists
  -- choose `ε`
  have hcont : Continuous (ctrbMap F G N) := LinearMap.continuous_of_finiteDimensional _
  obtain ⟨ε, hε, hεball⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := 0)) (η / 2)
    (half_pos hη)
  set δ : ℝ≥0∞ := Γ (Metric.ball w ε) ^ N
  have hδ : 0 < δ := ENNReal.pow_pos ((Measure.mem_support_iff_forall w).1 hw _
    (Metric.ball_mem_nhds w hε)) N
  refine ⟨N, hN1, δ, hδ, fun x₀ hx₀ => ?_⟩
  rw [lssMatrixKernel_pow_apply, Measure.map_apply (by fun_prop) hO.measurableSet]
  refine le_trans (le_of_eq ?_) (measure_mono (s := Set.pi univ fun _ => Metric.ball w ε)
    fun u hu => ?_)
  · rw [Measure.pi_pi]; simp [δ]
  · apply hball
    change dist ((F ^ N) *ᵥ x₀ + ∑ i : Fin N, (F ^ (N - 1 - i) * G) *ᵥ u i) xs < η
    rw [lss_position_split F G N x₀ w u, dist_eq_norm]
    have hv : ‖fun i => u i - w‖ < ε := by
      rw [pi_norm_lt_iff hε]
      intro i
      have := hu i (mem_univ i)
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have hL : ‖ctrbMap F G N (fun i => u i - w)‖ < η / 2 := by
      have := hεball (x := fun i => u i - w) (by rwa [dist_zero_right])
      rwa [map_zero, dist_zero_right] at this
    have hx : ‖(F ^ N) *ᵥ x₀‖ ≤ C * r ^ N * max R 0 :=
      (hgeo N x₀).trans (mul_le_mul_of_nonneg_left (hx₀.trans (le_max_left _ _))
        (by positivity))
    calc ‖(F ^ N) *ᵥ x₀ + ∑ k ∈ Finset.range N, (F ^ k) *ᵥ (G *ᵥ w) +
          ctrbMap F G N (fun i => u i - w) - xs‖
        = ‖(F ^ N) *ᵥ x₀ - (xs - ∑ k ∈ Finset.range N, (F ^ k) *ᵥ (G *ᵥ w)) +
          ctrbMap F G N (fun i => u i - w)‖ := by congr 1; abel
      _ ≤ ‖(F ^ N) *ᵥ x₀‖ + ‖xs - ∑ k ∈ Finset.range N, (F ^ k) *ᵥ (G *ᵥ w)‖ +
          ‖ctrbMap F G N (fun i => u i - w)‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ < η / 2 + η / 2 := by
          refine add_lt_add_of_le_of_lt ?_ hL
          linarith [hNsmall]
      _ = η := add_halves η

/-- **Proposition 6.3.5** (MT p. 138): if LSS(F, G) satisfies the density condition (LSS4) and the
eigenvalue condition (LSS5), and LCM(F, G) is controllable, then it is a `ψ`-irreducible T-chain
and every compact set is small. As in the book, `x* = Σₖ Fᵏ G w` (for `w` in the support of `Γ`)
is reachable, so Proposition 6.2.1 applies to the component of Proposition 6.3.3; a small set `C`
charged by `T(x*, ·)` makes a neighbourhood `O` of `x*` small, and every compact set reaches `O`
uniformly. -/
theorem proposition_6_3_5 (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G)
    (hns : ¬ Γ ⟂ₘ volume) (hF : IsStableMatrix F) :
    ∃ _ : IsMarkovKernel (lssMatrixKernel Γ F G),
      (∃ ψ : Measure (Fin n → ℝ), ψ ≠ 0 ∧ IsPhiIrreducible (lssMatrixKernel Γ F G) ψ) ∧
      IsTChain (lssMatrixKernel Γ F G) ∧
      ∀ K : Set (Fin n → ℝ), IsCompact K → IsSmall (lssMatrixKernel Γ F G) K := by
  have hM := isMarkovKernel_lssMatrixKernel Γ F G
  set P := lssMatrixKernel Γ F G
  obtain ⟨⟨T, hT, hTpos⟩, hTchain⟩ := proposition_6_3_3 Γ hc hns
  obtain ⟨C, r, hC, hr0, hr1, hgeo⟩ := isStableMatrix_geometric hF
  obtain ⟨w, hw⟩ := Measure.nonempty_support (IsProbabilityMeasure.ne_zero Γ)
  have hsum : Summable fun k => (F ^ k) *ᵥ (G *ᵥ w) := by
    refine Summable.of_norm_bounded (g := fun k => C * ‖G *ᵥ w‖ * r ^ k) ?_ fun k => ?_
    · exact (summable_geometric_of_lt_one hr0.le hr1).mul_left _
    · calc ‖(F ^ k) *ᵥ (G *ᵥ w)‖ ≤ C * r ^ k * ‖G *ᵥ w‖ := hgeo k _
        _ = C * ‖G *ᵥ w‖ * r ^ k := by ring
  set xs := ∑' k, (F ^ k) *ᵥ (G *ᵥ w)
  have hreach : IsReachable P xs := by
    intro O hO hxO y
    obtain ⟨N, hN1, δ, hδ, hle⟩ := lss_uniform_reach Γ G hC hr0 hr1 hgeo hw hsum ‖y‖ hO hxO
    have hOm := hO.measurableSet
    refine (potKernel_pos_iff P hOm y).2 ⟨N - 1, ?_⟩
    rw [Nat.sub_add_cancel hN1]
    exact lt_of_lt_of_le hδ (hle y le_rfl)
  have hirr : IsPhiIrreducible P (T xs) := proposition_6_2_1 hT hreach
  have hT0 : T xs ≠ 0 := fun h => by have := hTpos xs; rw [h] at this; simp at this
  refine ⟨hM, ⟨T xs, hT0, hirr⟩, hTchain, fun K hK => ?_⟩
  -- a small set charged by `T(x*, ·)`
  have hmax := isMaximalIrreducibility_maxIrrMeasure P hirr hT0
  obtain ⟨Cs, hCs, hcover⟩ := proposition_5_2_4_ii P hmax
  have hpos : 0 < T xs (⋃ i, ⋃ j, Cs i j) := by rw [hcover]; exact hTpos xs
  obtain ⟨i, hi⟩ := exists_measure_pos_of_iUnion hpos
  obtain ⟨j, hj⟩ := exists_measure_pos_of_iUnion hi
  obtain ⟨mC, νC, hsmallC⟩ := hCs i j
  set c := T xs (Cs i j)
  have hcfin : c ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((measure_mono (subset_univ _)).trans (hT.1 xs))
  set O := {x | c / 2 < T x (Cs i j)}
  have hO : IsOpen O := (hT.2.2 _ hsmallC.1).isOpen_preimage _
  have hxO : xs ∈ O := ENNReal.half_lt_self hj.ne' hcfin
  have hOsmall : IsSmallSet P (n + mC) ((c / 2) • νC) O :=
    proposition_5_2_4_i P hsmallC hO.measurableSet (ENNReal.half_pos hj.ne') fun x hx => by
      have := (hT.2.1 x (Cs i j))
      rw [sampledKernel_diracDist] at this
      exact hx.le.trans this
  obtain ⟨R, hR⟩ := (hK.isBounded.subset_closedBall 0)
  obtain ⟨N, -, δ, hδ, hle⟩ := lss_uniform_reach Γ G hC hr0 hr1 hgeo hw hsum R hO hxO
  exact ⟨N + (n + mC), _, proposition_5_2_4_i P hOsmall hK.measurableSet hδ fun x hx => hle x
    (by have := hR hx; rwa [Metric.mem_closedBall, dist_zero_right] at this)⟩

end MeynTweedie.GeometricErgodicity
