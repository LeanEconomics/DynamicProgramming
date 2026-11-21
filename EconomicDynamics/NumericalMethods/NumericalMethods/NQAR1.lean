/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NQHermite
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Discretizing AR(1) processes (Miao, §11.2, pp. 350–354)

Miao, §11.2: the AR(1) process (11.1) `z_{t+1} = μ(1 − ρ) + ρ z_t + σ ε_{t+1}`, `ε` IID
`N(0, 1)`, is approximated by a finite Markov chain on `{z¹, …, z^N}` with transition matrix
`(π_{ij})`, by the methods of Tauchen (1986) and Tauchen and Hussey (1991); a Markov chain is
simulated by inverting its cumulative transition probabilities.

* The AR(1) (p. 351): `nq_ar1_mean_fixed` (`μ` is the only stationary mean),
  `nq_ar1_variance_fixed` (`σ_z² = σ²/(1 − ρ²)` is the only stationary variance), and
  `nq_ar1_stationary_law` (`N(μ, σ²/(1 − ρ²))` is a stationary law of (11.1)).
* Tauchen (pp. 351): the grid `nqTauchenGrid` (`nq_tauchen_grid_first`, `nq_tauchen_grid_last`,
  `nq_tauchen_grid_step`: `N` equally spaced points from `z_min = −mσ_z` to `z_max = mσ_z`), the
  cut points `nqTauchenCut` (midpoints of consecutive grid points, `nq_tauchen_cut_midpoint`,
  `nq_tauchen_cut_monotone`), the intervals `nqCell` (`nq_cell_eq`), the transition
  probabilities `nqTauchenProb` with `nq_tauchen_law` and `nq_tauchen_prob_eq` (Step 3:
  `π_{ij} = Pr(z_{t+1} ∈ I_j | z_t = zⁱ)` computed from (11.1)) and
  `nq_tauchen_stochastic` (the Tauchen matrix is stochastic, for any nondecreasing cut points).
  `nq_tauchen_printed_I2_upper`, `nq_tauchen_printed_IN_lower`: the printed interval endpoints
  are not the midpoints (correction).
* Tauchen–Hussey (pp. 352–353): `nq_th_ratio`, `nq_th_change_of_measure` (the transformation
  `∫ v f(·|z) = ∫ v (f(·|z)/f(·|0)) f(·|0)`), `nq_th_conditional_expectation` (the Gauss–Hermite
  form of `E[v(z')|z]`), `nq_th_exact` (with a Gauss–Hermite rule exact for the integrand,
  `E[v(z')|zⁱ] = ∑ⱼ π̃_{ij} v(zʲ)`), `nq_th_rowsum_integral` (the row sums `∑ⱼ π̃_{ij}` are the
  Gauss–Hermite approximation of `1`), `nq_th_rowsum_lt_one` ("we may have `∑ⱼ π̃_{ij} ≠ 1`": the
  two-point rule gives `e^{−ρ²/2} cosh ρ < 1` for every `ρ ≠ 0`), `nq_normalize_stochastic`
  and `nq_th_normalized_stochastic` (the normalised matrix `π_{ij}` is stochastic).
* Simulation (p. 353): `nq_sim_interval_volume` (`Pr(Π^c_{i,j−1} < p ≤ Π^c_{ij}) = π_{ij}` for
  `p` uniform on `[0, 1]`) and `nq_sim_unique` (every `p ∈ (0, 1]` selects exactly one state).

**Departures.** States and intervals are indexed `0, …, N − 1`; `nqCell c N j` is
`(−∞, c₁)` for `j = 0`, `[c_j, c_{j+1})` in between and `[c_{N−1}, ∞)` for `j = N − 1`. The
convergence `∑ⱼ π̃_{ij} → 1` as `N → ∞` (p. 353) needs the convergence theory of Gaussian
quadrature, which the book does not develop: not formalised. The steps of the algorithms
("in practice `m = 3` or `4`", the Matlab codes) are not formalised. The text of this draft has
no Rouwenhorst method.
-/

namespace Miao.NumericalMethods

open MeasureTheory Polynomial Real ProbabilityTheory

/-! ### The AR(1) process (11.1) -/

/-- Miao, (11.1), p. 351: `μ` is the unconditional mean of (11.1): for `ρ ≠ 1` it is the only
`m` with `m = μ(1 − ρ) + ρ m`. -/
theorem nq_ar1_mean_fixed {μ ρ m : ℝ} (hρ : ρ ≠ 1) : m = μ * (1 - ρ) + ρ * m ↔ m = μ := by
  constructor
  · intro h
    have h1 : (1 - ρ) * (m - μ) = 0 := by linarith
    have h2 : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
    linarith [(mul_eq_zero.mp h1).resolve_left h2]
  · rintro rfl; ring

/-- Miao, p. 351: for `|ρ| < 1` the unconditional variance `σ_z² = σ²/(1 − ρ²)` of (11.1) is the
only `s` with `s = ρ² s + σ²` (variance of `ρ z_t + σ ε_{t+1}` with `ε` independent of `z_t`). -/
theorem nq_ar1_variance_fixed {ρ σ s : ℝ} (hρ : |ρ| < 1) :
    s = ρ ^ 2 * s + σ ^ 2 ↔ s = σ ^ 2 / (1 - ρ ^ 2) := by
  have h1 : 0 < 1 - ρ ^ 2 := by
    have := sq_lt_one_iff_abs_lt_one ρ |>.mpr hρ; linarith
  rw [eq_div_iff h1.ne']
  constructor <;> intro h <;> linarith

/-- Miao, (11.1), p. 351: `N(μ, σ_z²)`, `σ_z² = σ²/(1 − ρ²)`, is a stationary law of (11.1): if
`z_t ~ N(μ, σ_z²)` and `ε_{t+1} ~ N(0, 1)` is independent of `z_t`, then
`z_{t+1} = μ(1 − ρ) + ρ z_t + σ ε_{t+1} ~ N(μ, σ_z²)`. -/
theorem nq_ar1_stationary_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z ε : Ω → ℝ} {μ ρ σ : ℝ} (hρ : |ρ| < 1)
    (hZ : HasLaw Z (gaussianReal μ (Real.toNNReal (σ ^ 2 / (1 - ρ ^ 2)))) P)
    (hε : HasLaw ε (gaussianReal 0 1) P) (hind : IndepFun Z ε P) :
    HasLaw (fun ω => μ * (1 - ρ) + ρ * Z ω + σ * ε ω)
      (gaussianReal μ (Real.toNNReal (σ ^ 2 / (1 - ρ ^ 2)))) P := by
  have h1 : 0 < 1 - ρ ^ 2 := by
    have := sq_lt_one_iff_abs_lt_one ρ |>.mpr hρ; linarith
  set s : ℝ := σ ^ 2 / (1 - ρ ^ 2)
  have hs : 0 ≤ s := div_nonneg (sq_nonneg σ) h1.le
  have hX := gaussianReal_const_add (gaussianReal_const_mul hZ ρ) (μ * (1 - ρ))
  have hY := gaussianReal_const_mul hε σ
  have hind' : IndepFun (fun ω => μ * (1 - ρ) + ρ * Z ω) (fun ω => σ * ε ω) P :=
    hind.comp (φ := fun x => μ * (1 - ρ) + ρ * x) (ψ := fun x => σ * x)
      (by fun_prop) (by fun_prop)
  have hmap := gaussianReal_add_gaussianReal_of_indepFun hind' hX hY
  refine ⟨(hX.aemeasurable.add hY.aemeasurable), ?_⟩
  have hfun : (fun ω => μ * (1 - ρ) + ρ * Z ω + σ * ε ω) =
      (fun ω => μ * (1 - ρ) + ρ * Z ω) + (fun ω => σ * ε ω) := rfl
  rw [hfun, hmap]
  congr 1
  · ring
  · apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ hs, mul_one]
    have := (nq_ar1_variance_fixed (σ := σ) (s := s) hρ).mpr rfl
    linarith

/-! ### Tauchen's method -/

/-- Miao, p. 351 (Tauchen, Step 1): the `N` equally spaced grid points
`zⁱ = z_min + i (z_max − z_min)/(N − 1)`, `i = 0, …, N − 1`. -/
noncomputable def nqTauchenGrid (N : ℕ) (zmin zmax : ℝ) (i : ℕ) : ℝ :=
  zmin + i * (zmax - zmin) / (N - 1)

/-- Miao, p. 351: the first grid point is `z_min`. -/
theorem nq_tauchen_grid_first (N : ℕ) (zmin zmax : ℝ) : nqTauchenGrid N zmin zmax 0 = zmin := by
  simp [nqTauchenGrid]

/-- Miao, p. 351: the last grid point is `z_max` (`N ≥ 2`). -/
theorem nq_tauchen_grid_last {N : ℕ} (hN : 2 ≤ N) (zmin zmax : ℝ) :
    nqTauchenGrid N zmin zmax (N - 1) = zmax := by
  have h : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  simp only [nqTauchenGrid, h]
  field_simp
  ring

/-- Miao, p. 351: consecutive grid points are `(z_max − z_min)/(N − 1)` apart. -/
theorem nq_tauchen_grid_step (N : ℕ) (zmin zmax : ℝ) (i : ℕ) :
    nqTauchenGrid N zmin zmax (i + 1) - nqTauchenGrid N zmin zmax i = (zmax - zmin) / (N - 1) := by
  simp only [nqTauchenGrid]
  push_cast
  ring

/-- Miao, p. 351: the grid is symmetric for `z_max = mσ_z = −z_min`: `z^{N−1−i} = −zⁱ`. -/
theorem nq_tauchen_grid_symm {N : ℕ} (hN : 2 ≤ N) (m σz : ℝ) {i : ℕ} (hi : i ≤ N - 1) :
    nqTauchenGrid N (-(m * σz)) (m * σz) (N - 1 - i) = -nqTauchenGrid N (-(m * σz)) (m * σz) i := by
  have h : ((N - 1 - i : ℕ) : ℝ) = (N : ℝ) - 1 - i := by
    rw [Nat.cast_sub hi, Nat.cast_sub (by omega)]; simp
  have h1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  simp only [nqTauchenGrid, h]
  field_simp
  ring

/-- Miao, p. 351 (Tauchen, Step 2): the cut points `c_j = z_min + (2j − 1)(z_max − z_min)/(2(N−1))`,
`j = 1, …, N − 1`, separating the intervals `I_j`. -/
noncomputable def nqTauchenCut (N : ℕ) (zmin zmax : ℝ) (j : ℕ) : ℝ :=
  zmin + (2 * j - 1) * (zmax - zmin) / (2 * (N - 1))

/-- Miao, p. 351: each cut point is the midpoint of two consecutive grid points. -/
theorem nq_tauchen_cut_midpoint (N : ℕ) (zmin zmax : ℝ) (j : ℕ) :
    nqTauchenCut N zmin zmax (j + 1) =
      (nqTauchenGrid N zmin zmax j + nqTauchenGrid N zmin zmax (j + 1)) / 2 := by
  simp only [nqTauchenCut, nqTauchenGrid]
  push_cast
  by_cases h : (N : ℝ) - 1 = 0
  · simp [h]
  · field_simp
    ring

/-- Miao, p. 351: the cut points are nondecreasing when `z_min ≤ z_max` and `N ≥ 2`. -/
theorem nq_tauchen_cut_monotone {N : ℕ} (hN : 2 ≤ N) {zmin zmax : ℝ} (h : zmin ≤ zmax) :
    Monotone (nqTauchenCut N zmin zmax) := by
  intro i j hij
  have hN' : (0 : ℝ) < 2 * ((N : ℝ) - 1) := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  simp only [nqTauchenCut]
  have : (2 * (i : ℝ) - 1) * (zmax - zmin) ≤ (2 * (j : ℝ) - 1) * (zmax - zmin) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have := div_le_div_of_nonneg_right this hN'.le
  linarith

/-- Miao, p. 351 (correction): the printed upper endpoint `z_min + (z_max − z_min)/(N − 1)` of
`I₂` is not the cut point between `z²` and `z³` (book's numbering), which is
`z_min + 3(z_max − z_min)/(2(N − 1))` (here `nqTauchenCut N z_min z_max 2`). -/
theorem nq_tauchen_printed_I2_upper {N : ℕ} (hN : 2 ≤ N) {zmin zmax : ℝ} (h : zmin < zmax) :
    zmin + (zmax - zmin) / (N - 1) ≠ nqTauchenCut N zmin zmax 2 := by
  have hN' : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  simp only [nqTauchenCut]
  intro heq
  have : (zmax - zmin) / (N - 1) = 3 * (zmax - zmin) / (2 * (N - 1)) := by
    push_cast at heq ⊢; linarith
  field_simp at this
  linarith

/-- Miao, p. 351 (correction): the printed lower endpoint `z_min + N(z_max − z_min)/(2(N − 1))` of
`I_N` is not the last cut point `z_min + (2N − 3)(z_max − z_min)/(2(N − 1))` (the midpoint of
the two largest grid points) when `N ≥ 4`. -/
theorem nq_tauchen_printed_IN_lower {N : ℕ} (hN : 4 ≤ N) {zmin zmax : ℝ} (h : zmin < zmax) :
    zmin + N * (zmax - zmin) / (2 * (N - 1)) ≠ nqTauchenCut N zmin zmax (N - 1) := by
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hN' : (0 : ℝ) < 2 * ((N : ℝ) - 1) := by linarith
  have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  simp only [nqTauchenCut, hc]
  intro heq
  have h2 : (N : ℝ) * (zmax - zmin) / (2 * ((N : ℝ) - 1)) =
      (2 * ((N : ℝ) - 1) - 1) * (zmax - zmin) / (2 * ((N : ℝ) - 1)) := by linarith
  rw [div_left_inj' hN'.ne'] at h2
  have h3 : (N : ℝ) = 2 * ((N : ℝ) - 1) - 1 :=
    mul_right_cancel₀ (sub_ne_zero.mpr h.ne') h2
  linarith

/-- Miao, p. 351 (Tauchen, Step 2): the intervals `I_j` determined by cut points `c`:
`(−∞, c₁)` for `j = 0`, `[c_j, c_{j+1})` for `0 < j < N − 1`, `[c_{N−1}, ∞)` for `j = N − 1`. -/
def nqCell (c : ℕ → ℝ) (N j : ℕ) : Set ℝ :=
  {z | (j = 0 ∨ c j ≤ z) ∧ (j + 1 = N ∨ z < c (j + 1))}

/-- The four shapes of the intervals `I_j`. -/
theorem nq_cell_eq (c : ℕ → ℝ) (N j : ℕ) :
    nqCell c N j =
      if j = 0 then (if j + 1 = N then Set.univ else Set.Iio (c (j + 1)))
      else (if j + 1 = N then Set.Ici (c j) else Set.Ico (c j) (c (j + 1))) := by
  ext z
  by_cases h0 : j = 0 <;> by_cases h1 : j + 1 = N <;>
    simp [nqCell, h0, h1, Set.mem_Ico] <;> tauto

/-- The intervals `I_j` are Borel sets. -/
theorem nq_cell_measurable (c : ℕ → ℝ) (N j : ℕ) : MeasurableSet (nqCell c N j) := by
  rw [nq_cell_eq]
  split_ifs
  · exact MeasurableSet.univ
  · exact measurableSet_Iio
  · exact measurableSet_Ici
  · exact measurableSet_Ico

/-- Miao, p. 351: for any probability measure and nondecreasing cut points, the probabilities of
the `N` intervals `I_j` sum to one (they telescope through the distribution function). -/
theorem nq_cells_sum_one (P : Measure ℝ) [IsProbabilityMeasure P] {c : ℕ → ℝ} (hc : Monotone c)
    {N : ℕ} (hN : 0 < N) : ∑ j ∈ Finset.range N, P.real (nqCell c N j) = 1 := by
  set G : ℕ → ℝ := fun k => if k = 0 then 0 else if k = N then 1 else P.real (Set.Iio (c k))
  have hG : ∀ j ∈ Finset.range N, P.real (nqCell c N j) = G (j + 1) - G j := by
    intro j hj
    have hjN := Finset.mem_range.mp hj
    have hN0 : N ≠ 0 := by omega
    rw [nq_cell_eq]
    by_cases h0 : j = 0 <;> by_cases h1 : j + 1 = N
    · subst h0
      simp [G, ← h1]
    · subst h0
      have h1' : (1 : ℕ) ≠ N := by simpa using h1
      simp [G, h1']
    · have hjN' : j ≠ N := by omega
      simp only [G, h0, h1, hjN', hN0, ↓reduceIte]
      rw [← Set.compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ]
    · have hjN' : j ≠ N := by omega
      simp only [G, h0, h1, hjN', ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
      have hdisj : Disjoint (Set.Iio (c j)) (Set.Ico (c j) (c (j + 1))) :=
        Set.disjoint_left.mpr fun z hz hz' => absurd hz'.1 (not_le.mpr hz)
      rw [← Set.Iio_union_Ico_eq_Iio (hc (Nat.le_add_right j 1)),
        measureReal_union (μ := P) hdisj measurableSet_Ico]
      ring
  rw [Finset.sum_congr rfl hG, Finset.sum_range_sub (f := G)]
  simp [G, hN.ne']

/-- Miao, p. 351 (Tauchen, Step 3): the transition probability
`π_{ij} = Pr(z_{t+1} ∈ I_j | z_t = zⁱ)`, the `N(ρ zⁱ, σ²)` probability of `I_j` (`μ = 0`). -/
noncomputable def nqTauchenProb (ρ σ : ℝ) (c : ℕ → ℝ) (N : ℕ) (zi : ℝ) (j : ℕ) : ℝ :=
  (gaussianReal (ρ * zi) (Real.toNNReal (σ ^ 2))).real (nqCell c N j)

/-- Miao, (11.1), p. 351: given `z_t = z`, `z_{t+1} = ρ z + σ ε_{t+1}` (`μ = 0`) has law
`N(ρ z, σ²)`: the image of `N(0, 1)` under `e ↦ ρ z + σ e`. -/
theorem nq_tauchen_law (ρ σ z : ℝ) :
    (gaussianReal 0 1).map (fun e => ρ * z + σ * e) =
      gaussianReal (ρ * z) (Real.toNNReal (σ ^ 2)) := by
  have hcomp : (fun e => ρ * z + σ * e) = (fun y => ρ * z + y) ∘ (fun e => σ * e) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  congr 1
  · ring
  · apply NNReal.eq
    simp [Real.coe_toNNReal _ (sq_nonneg σ)]

/-- Miao, p. 351 (Step 3, "by (11.1), these transition probabilities can be easily computed"):
`π_{ij} = Pr(ρ zⁱ + σ ε ∈ I_j)` with `ε ~ N(0, 1)`. -/
theorem nq_tauchen_prob_eq (ρ σ : ℝ) (c : ℕ → ℝ) (N : ℕ) (zi : ℝ) (j : ℕ) :
    nqTauchenProb ρ σ c N zi j =
      (gaussianReal 0 1).real ((fun e => ρ * zi + σ * e) ⁻¹' nqCell c N j) := by
  rw [nqTauchenProb, ← nq_tauchen_law, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) (nq_cell_measurable c N j)]

/-- Miao, p. 351: the Tauchen matrix is stochastic: `π_{ij} ≥ 0` and `∑ⱼ π_{ij} = 1` for every
state `zⁱ`, for any nondecreasing cut points (in particular `nqTauchenCut`). -/
theorem nq_tauchen_stochastic (ρ σ : ℝ) {c : ℕ → ℝ} (hc : Monotone c) {N : ℕ} (hN : 0 < N)
    (zi : ℝ) :
    (∀ j, 0 ≤ nqTauchenProb ρ σ c N zi j) ∧
      ∑ j ∈ Finset.range N, nqTauchenProb ρ σ c N zi j = 1 :=
  ⟨fun _ => measureReal_nonneg, nq_cells_sum_one _ hc hN⟩

/-! ### The Tauchen–Hussey method -/

/-- Miao, p. 352: the conditional density `f(z'|z)` of `z_{t+1}` given `z_t = z` (`μ = 0`), the
`N(ρ z, σ²)` density. -/
noncomputable def nqCondDens (ρ σ z' z : ℝ) : ℝ :=
  gaussianPDFReal (ρ * z) (Real.toNNReal (σ ^ 2)) z'

/-- Miao, p. 352: `f(z'|z)/f(z'|0) = exp((z'² − (z' − ρz)²)/(2σ²))`. -/
theorem nq_th_ratio (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (z' z : ℝ) :
    nqCondDens ρ σ z' z / nqCondDens ρ σ z' 0 =
      Real.exp ((z' ^ 2 - (z' - ρ * z) ^ 2) / (2 * σ ^ 2)) := by
  simp only [nqCondDens, gaussianPDFReal_def, Real.coe_toNNReal _ (sq_nonneg σ), mul_zero,
    sub_zero]
  have hA : (√(2 * π * σ ^ 2))⁻¹ ≠ 0 := by
    have : 0 < 2 * π * σ ^ 2 := by positivity
    positivity
  rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]
  congr 1
  ring

/-- Miao, p. 352 (the Tauchen–Hussey transformation):
`∫ v(z') f(z'|z) dz' = ∫ v(z') (f(z'|z)/f(z'|0)) f(z'|0) dz'`. -/
theorem nq_th_change_of_measure (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (v : ℝ → ℝ) (z : ℝ) :
    ∫ z', v z' * nqCondDens ρ σ z' z =
      ∫ z', v z' * (nqCondDens ρ σ z' z / nqCondDens ρ σ z' 0) * nqCondDens ρ σ z' 0 := by
  congr 1
  funext z'
  have hpos : 0 < nqCondDens ρ σ z' 0 :=
    gaussianPDFReal_pos _ _ _ (by rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity)
  field_simp

/-- Miao, p. 352: `E[v(z')|z] = π^{−1/2} ∫ v(√2σx) f(√2σx|z)/f(√2σx|0) e^{−x²} dx`, the
Gauss–Hermite form of the conditional expectation after the transformation. -/
theorem nq_th_conditional_expectation (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (v : ℝ → ℝ) (z : ℝ) :
    ∫ z', v z' ∂(gaussianReal (ρ * z) (Real.toNNReal (σ ^ 2))) =
      (√π)⁻¹ * ∫ x, v (√2 * σ * x) *
        (nqCondDens ρ σ (√2 * σ * x) z / nqCondDens ρ σ (√2 * σ * x) 0) *
          Real.exp (-x ^ 2) := by
  have hv : Real.toNNReal (σ ^ 2) ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  have h0 := nq_normal_expectation_hermite 0 hσ
    (fun z' => v z' * (nqCondDens ρ σ z' z / nqCondDens ρ σ z' 0))
  simp only [add_zero] at h0
  rw [← h0, integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  have h1 := nq_th_change_of_measure ρ hσ v z
  simp only [nqCondDens, mul_zero] at h1
  simp only [smul_eq_mul]
  rw [show (fun x => gaussianPDFReal (ρ * z) (Real.toNNReal (σ ^ 2)) x * v x) =
    fun x => v x * gaussianPDFReal (ρ * z) (Real.toNNReal (σ ^ 2)) x from
      funext fun x => mul_comm _ _, h1]
  congr 1
  funext x
  simp only [nqCondDens, mul_zero]
  ring

/-- Miao, p. 352: the Tauchen–Hussey weights
`π̃_{ij} = π^{−1/2} wⱼ f(zʲ|zⁱ)/f(zʲ|0)`, `zʲ = √2 σ xⱼ` (Gauss–Hermite nodes `xⱼ`, weights
`wⱼ`); the book prints a spurious `∑ⱼ` in front (correction). -/
noncomputable def nqTHTilde {N : ℕ} (w x : Fin N → ℝ) (ρ σ zi : ℝ) (j : Fin N) : ℝ :=
  (√π)⁻¹ * w j * (nqCondDens ρ σ (√2 * σ * x j) zi / nqCondDens ρ σ (√2 * σ * x j) 0)

/-- Miao, p. 352: if the Gauss–Hermite rule `(x, w)` is exact for the transformed integrand
`g(x) = v(√2σx) f(√2σx|zⁱ)/f(√2σx|0)`, then `E[v(z')|zⁱ] = ∑ⱼ π̃_{ij} v(zʲ)`. -/
theorem nq_th_exact (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (v : ℝ → ℝ) (zi : ℝ) {N : ℕ}
    {w x : Fin N → ℝ}
    (hex : ∫ y, (fun t => v (√2 * σ * t) *
        (nqCondDens ρ σ (√2 * σ * t) zi / nqCondDens ρ σ (√2 * σ * t) 0)) y *
          Real.exp (-y ^ 2) =
      nqQuad w x (fun t => v (√2 * σ * t) *
        (nqCondDens ρ σ (√2 * σ * t) zi / nqCondDens ρ σ (√2 * σ * t) 0))) :
    ∫ z', v z' ∂(gaussianReal (ρ * zi) (Real.toNNReal (σ ^ 2))) =
      ∑ j, nqTHTilde w x ρ σ zi j * v (√2 * σ * x j) := by
  rw [nq_th_conditional_expectation ρ hσ v zi, hex, nqQuad, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [nqTHTilde]
  ring

/-- Miao, p. 353: the row sums `∑ⱼ π̃_{ij}` are the Gauss–Hermite approximation of
`π^{−1/2} ∫ f(√2σx|zⁱ)/f(√2σx|0) e^{−x²} dx`, which equals `1` exactly. -/
theorem nq_th_rowsum_integral (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (zi : ℝ) :
    (√π)⁻¹ * ∫ x, (nqCondDens ρ σ (√2 * σ * x) zi / nqCondDens ρ σ (√2 * σ * x) 0) *
      Real.exp (-x ^ 2) = 1 := by
  have h := nq_th_conditional_expectation ρ hσ (fun _ => 1) zi
  simp only [integral_const, probReal_univ, one_smul, one_mul] at h
  exact h.symm

/-- Miao, p. 352 ("we may have `∑ⱼ π̃_{ij} ≠ 1`"): with the two-point Gauss–Hermite rule
(`nq_hermite_two_point`), the state `z = σ` and any `ρ ≠ 0`, the row sum is
`e^{−ρ²/2} cosh ρ < 1`. -/
theorem nq_th_rowsum_lt_one {ρ σ : ℝ} (hσ : 0 < σ) (hρ : ρ ≠ 0) :
    ∑ j, nqTHTilde (fun _ : Fin 2 => √π / 2) ![-(1 / √2), 1 / √2] ρ σ σ j < 1 := by
  have h2 : √2 * σ * (1 / √2) = σ := by field_simp
  have h2' : √2 * σ * -(1 / √2) = -σ := by field_simp
  have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
  simp only [nqTHTilde, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, h2, h2', nq_th_ratio ρ hσ]
  have e1 : ((-σ) ^ 2 - (-σ - ρ * σ) ^ 2) / (2 * σ ^ 2) = -ρ - ρ ^ 2 / 2 := by
    field_simp; ring
  have e2 : (σ ^ 2 - (σ - ρ * σ) ^ 2) / (2 * σ ^ 2) = ρ - ρ ^ 2 / 2 := by
    field_simp; ring
  rw [e1, e2]
  have hsum : (√π)⁻¹ * (√π / 2) * Real.exp (-ρ - ρ ^ 2 / 2) +
      (√π)⁻¹ * (√π / 2) * Real.exp (ρ - ρ ^ 2 / 2) =
      Real.exp (-(ρ ^ 2 / 2)) * Real.cosh ρ := by
    rw [Real.cosh_eq]
    have ea : Real.exp (-ρ - ρ ^ 2 / 2) = Real.exp (-ρ) * Real.exp (-(ρ ^ 2 / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have eb : Real.exp (ρ - ρ ^ 2 / 2) = Real.exp ρ * Real.exp (-(ρ ^ 2 / 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [ea, eb]
    field_simp
    ring
  rw [hsum]
  -- `cosh ρ = 2 cosh²(ρ/2) − 1 ≤ 2 exp(ρ²/4) − 1 < exp(ρ²/2)`
  have hc2 : Real.cosh ρ = 2 * Real.cosh (ρ / 2) ^ 2 - 1 := by
    have := Real.cosh_two_mul (ρ / 2)
    rw [show 2 * (ρ / 2) = ρ by ring, Real.cosh_sq] at this
    rw [this, Real.cosh_sq]; ring
  have hle : Real.cosh (ρ / 2) ≤ Real.exp ((ρ / 2) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
  have hpos : 0 ≤ Real.cosh (ρ / 2) := (Real.cosh_pos _).le
  set t : ℝ := Real.exp (ρ ^ 2 / 4)
  have ht : Real.exp ((ρ / 2) ^ 2 / 2) ^ 2 = t := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsq : Real.cosh (ρ / 2) ^ 2 ≤ t := by
    rw [← ht]; exact pow_le_pow_left₀ hpos hle 2
  have ht1 : t ≠ 1 := by
    intro h
    have : ρ ^ 2 / 4 = 0 := by
      have := congrArg Real.log h
      rwa [Real.log_exp, Real.log_one] at this
    exact hρ (by nlinarith [sq_nonneg ρ])
  have hlt : 2 * t - 1 < t ^ 2 := by
    have : 0 < (t - 1) ^ 2 := by positivity
    nlinarith
  have hexp : Real.exp (ρ ^ 2 / 2) = t ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hcosh : Real.cosh ρ < Real.exp (ρ ^ 2 / 2) := by
    rw [hc2, hexp]; linarith
  have hE : Real.exp (-(ρ ^ 2 / 2)) * Real.exp (ρ ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hEpos : 0 < Real.exp (-(ρ ^ 2 / 2)) := Real.exp_pos _
  nlinarith

/-- Miao, p. 352: normalising nonnegative weights with positive sum, `q_j / ∑ₖ q_k`, gives a
probability vector. -/
theorem nq_normalize_stochastic {N : ℕ} (q : Fin N → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hpos : 0 < ∑ j, q j) :
    (∀ j, 0 ≤ q j / ∑ k, q k) ∧ ∑ j, q j / ∑ k, q k = 1 := by
  refine ⟨fun j => div_nonneg (hq j) hpos.le, ?_⟩
  rw [← Finset.sum_div, div_self hpos.ne']

/-- Miao, p. 352: with positive Gauss–Hermite weights and `N ≥ 1`, the normalised Tauchen–Hussey
matrix `π_{ij} = π̃_{ij} / ∑ⱼ π̃_{ij}` is stochastic. -/
theorem nq_th_normalized_stochastic {N : ℕ} (hN : 0 < N) {w : Fin N → ℝ} (hw : ∀ j, 0 < w j)
    (x : Fin N → ℝ) (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (zi : ℝ) :
    (∀ j, 0 ≤ nqTHTilde w x ρ σ zi j / ∑ k, nqTHTilde w x ρ σ zi k) ∧
      ∑ j, nqTHTilde w x ρ σ zi j / ∑ k, nqTHTilde w x ρ σ zi k = 1 := by
  have hpos : ∀ j, 0 < nqTHTilde w x ρ σ zi j := by
    intro j
    have hv : Real.toNNReal (σ ^ 2) ≠ 0 := by
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
    have h1 := gaussianPDFReal_pos (ρ * zi) _ (√2 * σ * x j) hv
    have h2 := gaussianPDFReal_pos (ρ * 0) _ (√2 * σ * x j) hv
    have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
    simp only [nqTHTilde, nqCondDens]
    have := hw j
    positivity
  refine nq_normalize_stochastic _ (fun j => (hpos j).le) ?_
  exact Finset.sum_pos (fun j _ => hpos j) ⟨⟨0, hN⟩, Finset.mem_univ _⟩

/-! ### Simulating a Markov chain -/

/-- Miao, p. 353 (simulation, Step 3): for a uniform draw `p` on `[0, 1]`, the probability of
`Π^c_{i,j−1} < p ≤ Π^c_{ij}` (cumulative sums `Π^c_{ij} = ∑_{k ≤ j} π_{ik}`, `Π^c_{i,−1} = 0`)
is `π_{ij}`: the algorithm draws state `j` with the correct probability. -/
theorem nq_sim_interval_volume {N : ℕ} {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hsum : ∑ k ∈ Finset.range N, p k = 1) {j : ℕ} (hj : j < N) :
    (volume.restrict (Set.Icc (0 : ℝ) 1))
        (Set.Ioc (∑ k ∈ Finset.range j, p k) (∑ k ∈ Finset.range (j + 1), p k)) =
      ENNReal.ofReal (p j) := by
  have h0 : 0 ≤ ∑ k ∈ Finset.range j, p k := Finset.sum_nonneg fun k _ => hp k
  have h1 : ∑ k ∈ Finset.range (j + 1), p k ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hj)
      (fun k _ _ => hp k)
  rw [Measure.restrict_apply measurableSet_Ioc]
  have hsub : Set.Ioc (∑ k ∈ Finset.range j, p k) (∑ k ∈ Finset.range (j + 1), p k) ∩
      Set.Icc 0 1 = Set.Ioc (∑ k ∈ Finset.range j, p k) (∑ k ∈ Finset.range (j + 1), p k) :=
    Set.inter_eq_left.mpr fun u hu => ⟨by linarith [hu.1], hu.2.trans h1⟩
  rw [hsub, Real.volume_Ioc, Finset.sum_range_succ]
  congr 1
  ring

/-- Miao, p. 353 (simulation, Step 3): every `p ∈ (0, 1]` selects exactly one state `j < N` with
`Π^c_{i,j−1} < p ≤ Π^c_{ij}` (the case `j = 0` is the book's "if `p_t ≤ π_{i1}`"). -/
theorem nq_sim_unique {N : ℕ} {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hsum : ∑ k ∈ Finset.range N, p k = 1) {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    ∃! j, j < N ∧ ∑ k ∈ Finset.range j, p k < u ∧ u ≤ ∑ k ∈ Finset.range (j + 1), p k := by
  classical
  have hmono : Monotone (fun m => ∑ k ∈ Finset.range m, p k) := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hab)
      (fun k _ _ => hp k)
  have hex : ∃ m, u ≤ ∑ k ∈ Finset.range m, p k := ⟨N, hsum ▸ hu.2⟩
  set m := Nat.find hex
  have hm : u ≤ ∑ k ∈ Finset.range m, p k := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    simp at hm
    linarith [hu.1]
  have hmN : m ≤ N := Nat.find_min' hex (hsum ▸ hu.2)
  refine ⟨m - 1, ⟨by omega, ?_, ?_⟩, ?_⟩
  · have := Nat.find_min hex (show m - 1 < m by omega)
    exact lt_of_not_ge this
  · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]; exact hm
  · rintro j ⟨_, hj1, hj2⟩
    have hjm : j + 1 ≥ m := Nat.find_min' hex hj2
    by_contra hne
    have hjm' : m ≤ j := by omega
    have := hmono hjm'
    simp only at this
    linarith

end Miao.NumericalMethods
