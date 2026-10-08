/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDiscounting.Resolvent
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The Perron–Frobenius theorem for nonnegative matrices

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Theorem 2.3.1
(p. 69), the part for nonnegative matrices: if `A ≥ 0` then `ρ(A)` is an
eigenvalue of `A` with a nonnegative, nonzero right eigenvector `e` and a
nonnegative, nonzero left eigenvector `ε`. The book quotes the theorem from
Meyer (2000); the proof here is through the resolvent.

* A complex eigenvalue `μ` of modulus `ρ(A)` exists, since the spectrum is
  finite and nonempty.
* For `|z| = t > ρ(A)` the complex resolvent `(zI − A)⁻¹ = ∑ z^{−(k+1)}Aᵏ` is
  dominated entrywise by the real resolvent `(tI − A)⁻¹ ≥ 0`.
* If the real resolvent stayed bounded on `(ρ, ρ + δ)`, then along `z = (1+s)μ`
  the complex resolvent would stay bounded while `z → μ`, and a Neumann-series
  perturbation would make `μI − A` invertible: `μ` could not be in the
  spectrum. Hence the real resolvent is unbounded near `ρ`.
* Normalising `(tI − A)⁻¹𝟙` to the simplex and letting `t ↓ ρ` along a sequence
  where the entries blow up, compactness of the simplex yields a limit `e ≥ 0`
  with `∑ e = 1` and `(ρI − A)e = 0`.

The statements for irreducible and everywhere-positive matrices (positivity and
uniqueness of the eigenvectors, the convergence (2.11)) are not claimed here;
they are proved in `Irreducible` and `PositiveMatrices`.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- A complex eigenvalue of maximal modulus exists: `‖μ‖ = ρ(A)` for some `μ` in the spectrum. -/
theorem exists_mem_spectrum_norm_eq (A : Matrix X X ℝ) :
    ∃ μ ∈ spectrum ℂ (complexify A), ‖μ‖ = specRad A := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  have hne : (spectrum ℂ (complexify A)).Nonempty := spectrum.nonempty _
  have hfin : (spectrum ℂ (complexify A)).Finite := Matrix.finite_spectrum _
  obtain ⟨μ₀, hμ₀⟩ := hne
  obtain ⟨μ, hμ, hmax⟩ := hfin.toFinset.exists_max_image (fun z => ‖z‖)
    ⟨μ₀, hfin.mem_toFinset.2 hμ₀⟩
  have hμ' : μ ∈ spectrum ℂ (complexify A) := hfin.mem_toFinset.1 hμ
  refine ⟨μ, hμ', le_antisymm (norm_le_specRad_of_mem_spectrum A hμ') ?_⟩
  have h1 : spectralRadius ℂ (complexify A) ≤ (‖μ‖₊ : ENNReal) := by
    rw [spectralRadius_eq_of_unital (𝕜 := ℂ) (complexify A)]
    refine iSup₂_le fun z hz => ?_
    exact_mod_cast hmax z (hfin.mem_toFinset.2 hz)
  have := ENNReal.toReal_mono ENNReal.coe_ne_top h1
  rwa [ENNReal.coe_toReal, coe_nnnorm] at this

/-- Entrywise Gelfand bound for the complexification. -/
theorem eventually_norm_entry_pow_complexify_le (A : Matrix X X ℝ) {r : ℝ}
    (hr : specRad A < r) (i j : X) :
    ∀ᶠ k : ℕ in atTop, ‖((complexify A) ^ k) i j‖ ≤ r ^ k :=
  (eventually_abs_entry_pow_le A hr i j).mono fun k hk => by
    rw [← complexify_pow, complexify_apply, Complex.norm_real, Real.norm_eq_abs]
    exact hk

/-- The real resolvent series at `t > ρ(A)` is a two-sided inverse of `tI − A`. -/
theorem smul_one_sub_mul_res_real (A : Matrix X X ℝ) {t : ℝ} (hρ : specRad A < t) :
    (t • (1 : Matrix X X ℝ) - A) * res A t = 1 ∧
      res A t * (t • (1 : Matrix X X ℝ) - A) = 1 := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  have hrt : r < ‖t‖ := by rwa [Real.norm_eq_abs, abs_of_pos (hr0.trans_lt hr2)]
  have hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(A ^ k) i j‖ ≤ r ^ k := fun i j =>
    (eventually_abs_entry_pow_le A hr1 i j).mono fun k hk => by rwa [Real.norm_eq_abs]
  exact ⟨smul_one_sub_mul_res A hr0 hrt hM, res_mul_smul_one_sub A hr0 hrt hM⟩

/-- Domination: for `|z| = t > ρ(A)`, `|R_ℂ(z)ᵢⱼ| ≤ R_ℝ(t)ᵢⱼ`. -/
theorem norm_res_complexify_le (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) {z : ℂ}
    {t : ℝ} (hzt : ‖z‖ = t) (hρ : specRad A < t) (i j : X) :
    ‖res (complexify A) z i j‖ ≤ res A t i j := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  have ht0 : 0 < t := hr0.trans_lt hr2
  have hterm : ∀ k : ℕ, ‖(z⁻¹) ^ (k + 1) * ((complexify A) ^ k) i j‖ =
      (t⁻¹) ^ (k + 1) * (A ^ k) i j := by
    intro k
    rw [norm_mul, norm_pow, norm_inv, hzt, ← complexify_pow, complexify_apply, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg_entries hA k i j)]
  have hreal : Summable fun k : ℕ => (t⁻¹) ^ (k + 1) * (A ^ k) i j :=
    summable_res_entry A hr0 (by rwa [Real.norm_eq_abs, abs_of_pos ht0]) i j
      ((eventually_abs_entry_pow_le A hr1 i j).mono fun k hk => by rwa [Real.norm_eq_abs])
  have hnorm : Summable fun k : ℕ => ‖(z⁻¹) ^ (k + 1) * ((complexify A) ^ k) i j‖ := by
    simp_rw [hterm]
    exact hreal
  rw [res_apply, res_apply]
  refine (norm_tsum_le_tsum_norm hnorm).trans (le_of_eq ?_)
  exact tsum_congr hterm

omit [Nonempty X] in
/-- The ℓ∞ operator norm of a complex matrix is bounded by `n` times a bound on its entries. -/
theorem norm_le_card_mul_of_entry_norm_le (M' : Matrix X X ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i j, ‖M' i j‖ ≤ M) : ‖M'‖ ≤ Fintype.card X * M := by
  rw [Matrix.linfty_opNorm_def]
  have hnM : (0 : ℝ) ≤ Fintype.card X * M := by positivity
  have hrow : ∀ i, (∑ j, ‖M' i j‖₊ : NNReal) ≤ (Fintype.card X * M).toNNReal := by
    intro i
    refine (NNReal.coe_le_coe (r₁ := ∑ j, ‖M' i j‖₊) (r₂ := (Fintype.card X * M).toNNReal)).1 ?_
    rw [NNReal.coe_sum, Real.coe_toNNReal _ hnM]
    simp only [coe_nnnorm]
    calc ∑ j, ‖M' i j‖ ≤ ∑ _j : X, M := sum_le_sum fun j _ => h i j
      _ = Fintype.card X * M := by simp
  have hsup : (univ.sup fun i => ∑ j, ‖M' i j‖₊) ≤ (Fintype.card X * M).toNNReal :=
    Finset.sup_le fun i _ => hrow i
  have := NNReal.coe_le_coe.2 hsup
  rwa [Real.coe_toNNReal _ hnM] at this

/-- If the real resolvent were bounded on `(ρ, ρ + δ)`, no complex number of modulus `ρ > 0`
could be in the spectrum: along `z = (1 + s)μ → μ` the complex resolvent stays bounded, and a
Neumann perturbation makes `μI − A` invertible. -/
theorem notMem_spectrum_of_res_bounded (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hρpos : 0 < specRad A) {μ : ℂ} (hμ : ‖μ‖ = specRad A) {M δ : ℝ} (hδ : 0 < δ) (hM0 : 0 ≤ M)
    (hM : ∀ t, specRad A < t → t < specRad A + δ → ∀ i j, res A t i j ≤ M) :
    μ ∉ spectrum ℂ (complexify A) := by
  set ρ := specRad A with hρ
  set C : ℝ := Fintype.card X * M + 1 with hC
  have hCpos : 0 < C := by positivity
  -- the step `s`
  set ε : ℝ := min δ (1 / C) with hε
  have hεpos : 0 < ε := lt_min hδ (by positivity)
  set s : ℝ := ε / (2 * ρ) with hs
  have hspos : 0 < s := by positivity
  have hsρ : s * ρ = ε / 2 := by rw [hs]; field_simp
  have hsρδ : s * ρ < δ := by rw [hsρ]; linarith [min_le_left δ (1 / C)]
  have hsρC : s * ρ * C < 1 := by
    rw [hsρ]
    have : ε ≤ 1 / C := min_le_right _ _
    have : ε * C ≤ 1 := by rwa [le_div_iff₀ hCpos] at this
    linarith
  -- the point `z = (1 + s) μ`, of modulus `t = (1 + s) ρ`
  set z : ℂ := ((1 + s : ℝ) : ℂ) * μ with hz
  set t : ℝ := (1 + s) * ρ with ht
  have hzt : ‖z‖ = t := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hμ]
  have hρt : ρ < t := by rw [ht]; nlinarith
  have htδ : t < ρ + δ := by rw [ht]; nlinarith
  -- the complex resolvent at `z` is a two-sided inverse and is bounded
  obtain ⟨r, hr1, hr2⟩ := exists_between hρt
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  have hrz : r < ‖z‖ := by rw [hzt]; exact hr2
  have hMc : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖((complexify A) ^ k) i j‖ ≤ r ^ k := fun i j =>
    eventually_norm_entry_pow_complexify_le A hr1 i j
  set R := res (complexify A) z with hR
  have hR1 : (z • (1 : Matrix X X ℂ) - complexify A) * R = 1 :=
    smul_one_sub_mul_res (complexify A) hr0 hrz hMc
  have hR2 : R * (z • (1 : Matrix X X ℂ) - complexify A) = 1 :=
    res_mul_smul_one_sub (complexify A) hr0 hrz hMc
  have hRnorm : ‖R‖ ≤ Fintype.card X * M :=
    norm_le_card_mul_of_entry_norm_le R hM0 fun i j =>
      (norm_res_complexify_le A hA hzt hρt i j).trans (hM t hρt htδ i j)
  -- the perturbation `(z − μ) • R` has norm `< 1`
  have hzμ : z - μ = ((s : ℝ) : ℂ) * μ := by rw [hz]; push_cast; ring
  have hpert : ‖(z - μ) • R‖ < 1 := by
    rw [norm_smul, hzμ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hspos.le, hμ]
    calc s * ρ * ‖R‖ ≤ s * ρ * (Fintype.card X * M) := by gcongr
      _ < s * ρ * C := by rw [hC]; nlinarith
      _ < 1 := hsρC
  -- `μI − A = (zI − A)(I − (z − μ)R)`, a product of units
  have hfactor : (z • (1 : Matrix X X ℂ) - complexify A) * (1 - (z - μ) • R) =
      μ • (1 : Matrix X X ℂ) - complexify A := by
    calc (z • (1 : Matrix X X ℂ) - complexify A) * (1 - (z - μ) • R)
        = (z • (1 : Matrix X X ℂ) - complexify A) -
            (z - μ) • ((z • (1 : Matrix X X ℂ) - complexify A) * R) := by
          rw [mul_sub, mul_one, Matrix.mul_smul]
      _ = (z • (1 : Matrix X X ℂ) - complexify A) -
            (z - μ) • (1 : Matrix X X ℂ) := by rw [hR1]
      _ = μ • (1 : Matrix X X ℂ) - complexify A := by
          rw [sub_smul]
          abel
  have hunit1 : IsUnit (z • (1 : Matrix X X ℂ) - complexify A) :=
    ⟨⟨z • 1 - complexify A, R, hR1, hR2⟩, rfl⟩
  have hunit2 : IsUnit (1 - (z - μ) • R) := (Units.oneSub ((z - μ) • R) hpert).isUnit
  rw [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one, ← hfactor]
  exact hunit1.mul hunit2

/-- The real resolvent is unbounded as `t ↓ ρ(A)`: for every bound `M` and every `δ > 0` some
entry of `R(t)` exceeds `M` at some `t ∈ (ρ, ρ + δ)`. -/
theorem exists_res_entry_gt (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) (M : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t, specRad A < t ∧ t < specRad A + δ ∧ ∃ i j, M < res A t i j := by
  rcases (specRad_nonneg A).lt_or_eq with hρpos | hρ0
  · by_contra hcon
    have hM : ∀ t, specRad A < t → t < specRad A + δ → ∀ i j, res A t i j ≤ M :=
      fun t h1 h2 i j => le_of_not_gt fun hgt => hcon ⟨t, h1, h2, i, j, hgt⟩
    have hM0 : 0 ≤ M := by
      have h1 : specRad A < specRad A + δ / 2 := by linarith
      have h2 : specRad A + δ / 2 < specRad A + δ := by linarith
      exact (res_nonneg hA (hρpos.trans h1) (Classical.arbitrary X) (Classical.arbitrary X)).trans
        (hM _ h1 h2 _ _)
    obtain ⟨μ, hμmem, hμ⟩ := exists_mem_spectrum_norm_eq A
    exact notMem_spectrum_of_res_bounded A hA hρpos hμ hδ hM0 hM hμmem
  · -- `ρ = 0`: the diagonal entries are at least `1/t`
    have hρ : specRad A = 0 := hρ0.symm
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (δ / 2) (1 / (2 * (|M| + 1))) := ⟨_, rfl⟩
    have htpos : 0 < t := by rw [ht]; exact lt_min (by linarith) (by positivity)
    have htδ : t < δ := by rw [ht]; exact (min_le_left _ _).trans_lt (by linarith)
    have htM : t ≤ 1 / (2 * (|M| + 1)) := by rw [ht]; exact min_le_right _ _
    refine ⟨t, by rw [hρ]; exact htpos, by rw [hρ]; linarith, (Classical.arbitrary X),
      (Classical.arbitrary X), ?_⟩
    have hbound : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(A ^ k) i j‖ ≤ (t / 2) ^ k := fun i j =>
      (eventually_abs_entry_pow_le A (r := t / 2) (by rw [hρ]; positivity) i j).mono
        fun k hk => by rwa [Real.norm_eq_abs]
    have hdiag := inv_le_res_diag hA (r := t / 2) (by positivity) (half_lt_self htpos) hbound
      (Classical.arbitrary X)
    have h2 : 2 * (|M| + 1) ≤ t⁻¹ := by
      rw [le_inv_comm₀ (by positivity) htpos]
      simpa [one_div] using htM
    have hMabs : M ≤ |M| := le_abs_self M
    have habs0 : 0 ≤ |M| := abs_nonneg M
    linarith

omit [Nonempty X] [DecidableEq X] in
/-- The simplex `{y ≥ 0 : ∑ y = 1}` is compact. -/
theorem isCompact_simplex :
    IsCompact {y : X → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
  classical
  have hsub : {y : X → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} ⊆ Set.Icc 0 1 := by
    rintro y ⟨hy0, hy1⟩
    refine ⟨fun i => hy0 i, fun i => ?_⟩
    calc y i ≤ ∑ j, y j := single_le_sum (fun j _ => hy0 j) (mem_univ i)
      _ = 1 := hy1
  have hclosed : IsClosed {y : X → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
    have h1 : IsClosed {y : X → ℝ | ∀ i, 0 ≤ y i} := by
      have : {y : X → ℝ | ∀ i, 0 ≤ y i} = ⋂ i, {y | 0 ≤ y i} := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {y : X → ℝ | ∑ i, y i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  exact isCompact_Icc.of_isClosed_subset hclosed hsub

omit [DecidableEq X] in
/-- **Theorem 2.3.1 (Perron–Frobenius), nonnegative case** (p. 69): if `A ≥ 0` then `ρ(A)` is an
eigenvalue of `A` with a nonnegative, nonzero right eigenvector. -/
theorem perron_frobenius (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ∃ e : X → ℝ, (∀ i, 0 ≤ e i) ∧ e ≠ 0 ∧ A *ᵥ e = specRad A • e := by
  classical
  set ρ := specRad A with hρ
  -- a sequence `tₖ ↓ ρ` along which some entry of `R(tₖ)` exceeds `k`
  choose t ht using fun k : ℕ => exists_res_entry_gt A hA (k : ℝ) (δ := 1 / (k + 1))
    (by positivity)
  have htρ : ∀ k, ρ < t k := fun k => (ht k).1
  have htlim : Tendsto t atTop (𝓝 ρ) := by
    have h1 : ∀ k, t k ≤ ρ + 1 / ((k : ℝ) + 1) := fun k => (ht k).2.1.le
    have h2 : Tendsto (fun k : ℕ => ρ + 1 / ((k : ℝ) + 1)) atTop (𝓝 (ρ + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun k => (htρ k).le) h1
  -- the row-sum vectors `vₖ = R(tₖ)𝟙 ≥ 0` and their totals `Nₖ > k`
  set v : ℕ → X → ℝ := fun k i => ∑ j, res A (t k) i j with hv
  have hv_eq : ∀ k, v k = res A (t k) *ᵥ fun _ => 1 := by
    intro k
    funext i
    simp [hv, mulVec, dotProduct]
  have hv0 : ∀ k i, 0 ≤ v k i := fun k i =>
    sum_nonneg fun j _ => res_nonneg hA ((specRad_nonneg A).trans_lt (htρ k)) i j
  set N : ℕ → ℝ := fun k => ∑ i, v k i with hN
  have hNgt : ∀ k : ℕ, (k : ℝ) < N k := by
    intro k
    obtain ⟨i, j, hij⟩ := (ht k).2.2
    calc (k : ℝ) < res A (t k) i j := hij
      _ ≤ v k i := single_le_sum
            (fun j _ => res_nonneg hA ((specRad_nonneg A).trans_lt (htρ k)) i j) (mem_univ j)
      _ ≤ N k := single_le_sum (fun i _ => hv0 k i) (mem_univ i)
  have hNpos : ∀ k, 0 < N k := fun k => (Nat.cast_nonneg k).trans_lt (hNgt k)
  -- `(tₖ I − A) vₖ = 𝟙`
  have hres : ∀ k, (t k • (1 : Matrix X X ℝ) - A) *ᵥ v k = fun _ => 1 := by
    intro k
    rw [hv_eq, mulVec_mulVec, (smul_one_sub_mul_res_real A (htρ k)).1, one_mulVec]
  -- the normalised vectors lie in the simplex
  set y : ℕ → X → ℝ := fun k => (N k)⁻¹ • v k with hy
  have hyS : ∀ k, y k ∈ {y : X → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
    intro k
    refine ⟨fun i => mul_nonneg (inv_nonneg.2 (hNpos k).le) (hv0 k i), ?_⟩
    simp only [hy, Pi.smul_apply, smul_eq_mul, ← mul_sum]
    exact inv_mul_cancel₀ (hNpos k).ne'
  obtain ⟨e, heS, φ, hφ, hlim⟩ := isCompact_simplex.tendsto_subseq hyS
  refine ⟨e, heS.1, ?_, ?_⟩
  · intro he
    have := heS.2
    rw [he] at this
    simp at this
  · -- `(tₖ I − A) yₖ = Nₖ⁻¹ 𝟙 → 0`, and the left side tends to `(ρI − A) e`
    have hφlim : Tendsto (fun k => t (φ k)) atTop (𝓝 ρ) := htlim.comp hφ.tendsto_atTop
    have hNinv : Tendsto (fun k => (N (φ k))⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => N (φ k)) atTop atTop :=
        tendsto_atTop_mono (fun k => (hNgt (φ k)).le)
          (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
      exact tendsto_inv_atTop_zero.comp h1
    funext i
    -- the `i`-th coordinate of `(tₖI − A) yₖ`
    have hcoord : ∀ k, (t (φ k) • (1 : Matrix X X ℝ) - A) *ᵥ y (φ k) =
        (N (φ k))⁻¹ • fun _ => (1 : ℝ) := by
      intro k
      simp only [hy, mulVec_smul, hres]
    have h1 : Tendsto (fun k => ((t (φ k) • (1 : Matrix X X ℝ) - A) *ᵥ y (φ k)) i)
        atTop (𝓝 (((ρ • (1 : Matrix X X ℝ) - A) *ᵥ e) i)) := by
      simp only [mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      refine tendsto_finsetSum _ fun x _ => ?_
      exact ((hφlim.mul tendsto_const_nhds).sub tendsto_const_nhds).mul
        (tendsto_pi_nhds.1 hlim x)
    have h2 : Tendsto (fun k => ((t (φ k) • (1 : Matrix X X ℝ) - A) *ᵥ y (φ k)) i)
        atTop (𝓝 0) := by
      simp only [hcoord, Pi.smul_apply, smul_eq_mul, mul_one]
      exact hNinv
    have h3 := tendsto_nhds_unique h1 h2
    rw [sub_mulVec, smul_mulVec, one_mulVec] at h3
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h3
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith

omit [DecidableEq X] in
/-- Theorem 2.3.1 (p. 69), left eigenvector: `εA = ρ(A)ε` for some nonnegative, nonzero `ε`,
by applying the right-eigenvector statement to `Aᵀ`. -/
theorem perron_frobenius_left (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ∃ ε : X → ℝ, (∀ i, 0 ≤ ε i) ∧ ε ≠ 0 ∧ ε ᵥ* A = specRad A • ε := by
  classical
  obtain ⟨ε, hε0, hεne, hε⟩ := perron_frobenius Aᵀ fun i j => hA j i
  refine ⟨ε, hε0, hεne, ?_⟩
  rw [← mulVec_transpose, hε, specRad_transpose]



/-! ### Lemma 2.3.2 -/

omit [DecidableEq X] in
/-- Lemma 2.3.2 (ii), p. 70, lower bound: if every column sum of `A ≥ 0` is at least `c`, then
`ρ(A) ≥ c`. Summing `Ae = ρe` over the coordinates of a nonnegative eigenvector `e` with `∑ e = S`
gives `ρS = ∑ⱼ colsumⱼ eⱼ ≥ cS`. -/
theorem le_specRad_of_colsum_ge (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) {c : ℝ}
    (hc : ∀ j, c ≤ ∑ i, A i j) : c ≤ specRad A := by
  classical
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA
  have hS : 0 < ∑ j, e j := by
    rcases (sum_nonneg fun j _ => he0 j).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hene
      funext j
      exact (sum_eq_zero_iff_of_nonneg fun j _ => he0 j).1 h.symm j (mem_univ j)
  have hsum : specRad A * ∑ j, e j = ∑ j, (∑ i, A i j) * e j := by
    calc specRad A * ∑ j, e j = ∑ i, (A *ᵥ e) i := by
          rw [he]
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
      _ = ∑ i, ∑ j, A i j * e j := rfl
      _ = ∑ j, ∑ i, A i j * e j := sum_comm
      _ = ∑ j, (∑ i, A i j) * e j := by simp only [sum_mul]
  have hge : c * ∑ j, e j ≤ ∑ j, (∑ i, A i j) * e j := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (he0 j)
  rw [← hsum] at hge
  exact le_of_mul_le_mul_right hge hS

omit [DecidableEq X] in
/-- Lemma 2.3.2 (ii), p. 70, upper bound: if every column sum of `A ≥ 0` is at most `C`, then
`ρ(A) ≤ C`. -/
theorem specRad_le_of_colsum_le (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) {C : ℝ}
    (hC : ∀ j, ∑ i, A i j ≤ C) : specRad A ≤ C := by
  classical
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA
  have hS : 0 < ∑ j, e j := by
    rcases (sum_nonneg fun j _ => he0 j).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hene
      funext j
      exact (sum_eq_zero_iff_of_nonneg fun j _ => he0 j).1 h.symm j (mem_univ j)
  have hsum : specRad A * ∑ j, e j = ∑ j, (∑ i, A i j) * e j := by
    calc specRad A * ∑ j, e j = ∑ i, (A *ᵥ e) i := by
          rw [he]
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
      _ = ∑ i, ∑ j, A i j * e j := rfl
      _ = ∑ j, ∑ i, A i j * e j := sum_comm
      _ = ∑ j, (∑ i, A i j) * e j := by simp only [sum_mul]
  have hle : ∑ j, (∑ i, A i j) * e j ≤ C * ∑ j, e j := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hC j) (he0 j)
  rw [← hsum] at hle
  exact le_of_mul_le_mul_right hle hS

omit [DecidableEq X] in
/-- Lemma 2.3.2 (i), p. 70: `ρ(A)` lies between the smallest and largest row sums of `A ≥ 0`, by
transposition. -/
theorem le_specRad_of_rowsum_ge (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) {c : ℝ}
    (hc : ∀ i, c ≤ ∑ j, A i j) : c ≤ specRad A := by
  classical
  rw [← specRad_transpose]
  exact le_specRad_of_colsum_ge Aᵀ (fun i j => hA j i) hc

omit [DecidableEq X] in
theorem specRad_le_of_rowsum_le (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) {C : ℝ}
    (hC : ∀ i, ∑ j, A i j ≤ C) : specRad A ≤ C := by
  classical
  rw [← specRad_transpose]
  exact specRad_le_of_colsum_le Aᵀ (fun i j => hA j i) hC

/-! ### Lemma 2.3.3: the local spectral radius -/

/-- `c^{1/k} → 1` for `c > 0`. -/
theorem tendsto_rpow_one_div_natCast {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => c ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun k : ℕ => Real.log c * (1 / (k : ℝ))) atTop (𝓝 (Real.log c * 0)) :=
    tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at h1
  have h2 := (Real.continuous_exp.tendsto 0).comp h1
  rw [Real.exp_zero] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp]
  rw [Real.rpow_def_of_pos hc, mul_comm]

omit [Nonempty X] in
/-- For `A ≥ 0` and `h ≥ m𝟙 > 0`, the row sums of `Aᵏ` are bounded by `(Aᵏh)ᵢ/m`, hence
`m‖Aᵏ‖ ≤ ‖Aᵏh‖`. -/
theorem norm_pow_mul_le_norm_mulVec (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {h : X → ℝ} {m : ℝ} (hm : 0 < m) (hmh : ∀ j, m ≤ h j) (k : ℕ) :
    m * ‖A ^ k‖ ≤ ‖A ^ k *ᵥ h‖ := by
  have hAk := pow_nonneg_entries hA k
  rw [← le_div_iff₀' hm]
  refine norm_le_of_rowsum_abs_le (A ^ k) (div_nonneg (norm_nonneg _) hm.le) fun i => ?_
  rw [le_div_iff₀ hm]
  calc (∑ j, |(A ^ k) i j|) * m = ∑ j, (A ^ k) i j * m := by
        rw [sum_mul]
        exact sum_congr rfl fun j _ => by rw [abs_of_nonneg (hAk i j)]
    _ ≤ ∑ j, (A ^ k) i j * h j := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmh j) (hAk i j)
    _ = (A ^ k *ᵥ h) i := rfl
    _ ≤ ‖A ^ k *ᵥ h‖ := by
        have := norm_le_pi_norm (A ^ k *ᵥ h) i
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this

/-- Lemma 2.3.3 (p. 70): for `A ≥ 0` and `h ≫ 0`, `‖Aᵏh‖^{1/k} → ρ(A)`, in the supremum norm. -/
theorem tendsto_norm_pow_mulVec_rpow (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {h : X → ℝ} (hh : ∀ j, 0 < h j) :
    Tendsto (fun k : ℕ => ‖A ^ k *ᵥ h‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  -- the minimum `m` of `h` and the norm `‖h‖`
  obtain ⟨j₀, -, hj₀⟩ := exists_min_image univ h univ_nonempty
  set m := h j₀ with hm
  have hmpos : 0 < m := hh j₀
  have hmh : ∀ j, m ≤ h j := fun j => hj₀ j (mem_univ j)
  have hhnorm : 0 < ‖h‖ := by
    have := norm_le_pi_norm h j₀
    rw [Real.norm_eq_abs, abs_of_pos (hh j₀)] at this
    exact hmpos.trans_le this
  have hG := tendsto_norm_pow_rpow A
  -- upper: `‖Aᵏh‖^{1/k} ≤ ‖Aᵏ‖^{1/k} ‖h‖^{1/k}`
  have hup : Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ)) * ‖h‖ ^ (1 / (k : ℝ))) atTop
      (𝓝 (specRad A * 1)) := hG.mul (tendsto_rpow_one_div_natCast hhnorm)
  -- lower: `m^{1/k} ‖Aᵏ‖^{1/k} ≤ ‖Aᵏh‖^{1/k}`
  have hlo : Tendsto (fun k : ℕ => m ^ (1 / (k : ℝ)) * ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop
      (𝓝 (1 * specRad A)) := (tendsto_rpow_one_div_natCast hmpos).mul hG
  rw [mul_one] at hup
  rw [one_mul] at hlo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun k => ?_) (fun k => ?_)
  · rw [← Real.mul_rpow hmpos.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) (norm_pow_mul_le_norm_mulVec A hA hmpos hmh k)
      (by positivity)
  · rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (Matrix.linfty_opNorm_mulVec _ _) (by positivity)

/-! ### Markov matrices (§2.3.1.3) -/

omit [DecidableEq X] in
/-- Exercise 2.3.2 (ii), p. 71: `ρ(P) = 1` for a Markov matrix. -/
theorem IsMarkov.specRad_eq_one {P : Matrix X X ℝ} (hP : IsMarkov P) : specRad P = 1 := by
  classical
  exact
  specRad_eq_of_rowsum_eq P hP.nonneg zero_le_one hP.rowsum

omit [DecidableEq X] in
/-- Exercise 2.3.2 (iii), p. 71: a Markov matrix has a stationary distribution, a row vector
`ψ ≥ 0` with `ψ𝟙 = 1` and `ψP = ψ`, by the left Perron–Frobenius eigenvector for `ρ(P) = 1`. -/
theorem IsMarkov.exists_stationary {P : Matrix X X ℝ} (hP : IsMarkov P) :
    ∃ ψ : X → ℝ, (∀ i, 0 ≤ ψ i) ∧ ∑ i, ψ i = 1 ∧ ψ ᵥ* P = ψ := by
  classical
  obtain ⟨ε, hε0, hεne, hε⟩ := perron_frobenius_left P hP.nonneg
  rw [hP.specRad_eq_one, one_smul] at hε
  have hS : 0 < ∑ i, ε i := by
    rcases (sum_nonneg fun i _ => hε0 i).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hεne
      funext i
      exact (sum_eq_zero_iff_of_nonneg fun i _ => hε0 i).1 h.symm i (mem_univ i)
  refine ⟨(∑ i, ε i)⁻¹ • ε, fun i => mul_nonneg (inv_nonneg.2 hS.le) (hε0 i), ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
    exact inv_mul_cancel₀ hS.ne'
  · rw [smul_vecMul, hε]

omit [DecidableEq X] in
/-- Exercise 2.3.3 (p. 71): for a Markov matrix `P` and `ε > 0` there is no `h` with
`Ph ≥ h + ε`: at a maximiser `x̄` of `h`, `(Ph)(x̄) ≤ h(x̄)`. -/
theorem IsMarkov.not_mulVec_ge_add {P : Matrix X X ℝ} (hP : IsMarkov P) {ε : ℝ}
    (hε : 0 < ε) : ¬ ∃ h : X → ℝ, ∀ x, h x + ε ≤ (P *ᵥ h) x := by
  classical
  rintro ⟨h, hh⟩
  obtain ⟨x, -, hx⟩ := exists_max_image univ h univ_nonempty
  have : (P *ᵥ h) x ≤ h x := by
    calc (P *ᵥ h) x = ∑ y, P x y * h y := rfl
      _ ≤ ∑ y, P x y * h x :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hx y (mem_univ y)) (hP.nonneg x y)
      _ = h x := by rw [← sum_mul, hP.rowsum, one_mul]
  linarith [hh x]

end SargentStachurski.StochasticDiscounting
