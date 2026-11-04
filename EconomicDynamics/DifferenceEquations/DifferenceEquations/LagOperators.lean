/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DifferenceEquations.Basics
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Lag operators (scalar case)

Miao, §1.2, pp. 10–12, for two-sided real sequences `X : ℤ → ℝ`.

* The lag operator `lagOp n X = Lⁿ X`, `(LⁿX)_t = X_{t−n}` for every integer `n`, with
  `Lᵐ Lⁿ = L^{m+n}` (`lagOp_lagOp`), `L⁰ = id` (`lagOp_zero`), `Lⁿ = (L¹)ⁿ` for `n ∈ ℕ`
  (`lagOp_iterate`), `L⁻ⁿLⁿ = id` (`lagOp_neg_lagOp`) and `Lⁿ c = c` (`lagOp_const`).
* `1/(1 − λLⁿ) = Σ λʲ L^{nj}` (`lag_inverse_geom`): for `|λ| < 1` and bounded `X`,
  `Y_t = Σ_j λʲ X_{t−nj}` (`geomLagSum`) is bounded, solves `Y − λLⁿY = X`, and is the unique
  bounded solution.
* `1/(1 − λLⁿ)² = Σ (j + 1)λʲ L^{nj}` (`lag_inverse_geom_sq`): `Y_t = Σ_j (j+1)λʲ X_{t−nj}`
  (`geomLagSum2`) is the unique bounded solution of `(1 − λLⁿ)²Y = X`.
* The scalar identities `1/(1 − λ) = Σ λʲ` and `1/(1 − λ)² = Σ (j + 1)λʲ`
  (`lag_scalar_geom`, `lag_scalar_geom_sq`).

The book states the operator identities formally; here they are made precise as statements
about the unique bounded solution, which is how they are used. The integer `n` is arbitrary
(`n < 0` gives lead operators, `n = 0` gives `Y = X/(1 − λ)`).
The matrix version `(I − ALⁿ)⁻¹ = Σ Aʲ L^{nj}` is not in this module.
-/

open Filter Topology

namespace Miao.DifferenceEquations

/-- The lag operator `Lⁿ` (Miao, p. 11): `(LⁿX)_t = X_{t−n}` for `n ∈ ℤ`. -/
def lagOp (n : ℤ) (X : ℤ → ℝ) : ℤ → ℝ :=
  fun t => X (t - n)

/-- A two-sided real sequence is bounded. -/
def BddZSeq (X : ℤ → ℝ) : Prop :=
  ∃ M, ∀ t, |X t| ≤ M

/-- Miao, p. 11: `Lᵐ(LⁿX) = L^{m+n}X`. -/
theorem lagOp_lagOp (m n : ℤ) (X : ℤ → ℝ) : lagOp m (lagOp n X) = lagOp (m + n) X := by
  ext t; simp only [lagOp]; congr 1; ring

/-- Miao, p. 11: `L⁰X = X`. -/
theorem lagOp_zero (X : ℤ → ℝ) : lagOp 0 X = X := by
  ext t; simp [lagOp]

/-- Miao, p. 11: `Lⁿ` is the `n`-th power of `L = L¹` for `n ∈ ℕ`. -/
theorem lagOp_iterate (n : ℕ) (X : ℤ → ℝ) : (lagOp 1)^[n] X = lagOp n X := by
  induction n with
  | zero => simp [lagOp_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, lagOp_lagOp]
    push_cast; ring_nf

/-- Miao, p. 11: `L⁻ⁿ` inverts `Lⁿ`. -/
theorem lagOp_neg_lagOp (n : ℤ) (X : ℤ → ℝ) : lagOp (-n) (lagOp n X) = X := by
  rw [lagOp_lagOp, neg_add_cancel, lagOp_zero]

/-- Miao, p. 11: `Lⁿ c = c` for a constant sequence. -/
theorem lagOp_const (n : ℤ) (c : ℝ) : lagOp n (fun _ => c) = fun _ => c := rfl

/-- The operator `1 − λLⁿ`: `((1 − λLⁿ)Y)_t = Y_t − λ Y_{t−n}`. -/
def oneSubLag (lam : ℝ) (n : ℤ) (Y : ℤ → ℝ) : ℤ → ℝ :=
  fun t => Y t - lam * lagOp n Y t

/-- `Y_t = Σ_j λʲ (L^{nj}X)_t = Σ_j λʲ X_{t−nj}`, the right side of `1/(1 − λLⁿ) = Σ λʲL^{nj}`
(Miao, p. 11). -/
noncomputable def geomLagSum (lam : ℝ) (n : ℤ) (X : ℤ → ℝ) (t : ℤ) : ℝ :=
  ∑' j : ℕ, lam ^ j * lagOp (n * j) X t

/-- `Y_t = Σ_j (j + 1)λʲ X_{t−nj}`, the right side of `1/(1 − λLⁿ)² = Σ (j+1)λʲL^{nj}`
(Miao, p. 11). -/
noncomputable def geomLagSum2 (lam : ℝ) (n : ℤ) (X : ℤ → ℝ) (t : ℤ) : ℝ :=
  ∑' j : ℕ, ((j : ℝ) + 1) * lam ^ j * lagOp (n * j) X t

theorem summable_of_abs_le {f g : ℕ → ℝ} {M : ℝ} (hg : Summable g) (h : ∀ j, |f j| ≤ M * g j) :
    Summable f :=
  Summable.of_norm_bounded (hg.mul_left M) (fun j => by rw [Real.norm_eq_abs]; exact h j)

theorem abs_tsum_le_of_abs_le {f g : ℕ → ℝ} {M : ℝ} (hg : Summable g)
    (h : ∀ j, |f j| ≤ M * g j) : |∑' j, f j| ≤ M * ∑' j, g j := by
  have hs : Summable (fun j => |f j|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) h (hg.mul_left M)
  calc |∑' j, f j| ≤ ∑' j, |f j| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := f)
          (by simpa [Real.norm_eq_abs] using hs)
    _ ≤ ∑' j, M * g j := hs.tsum_le_tsum h (hg.mul_left M)
    _ = M * ∑' j, g j := tsum_mul_left

theorem summable_succ_mul_geom {r : ℝ} (hr : |r| < 1) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) * r ^ j) := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r) (by rwa [Real.norm_eq_abs])
  have h2 := summable_geometric_of_abs_lt_one hr
  refine (h1.add h2).congr (fun j => ?_)
  simp only [pow_one]; ring

theorem abs_lagOp_le {X : ℤ → ℝ} {M : ℝ} (hX : ∀ t, |X t| ≤ M) (n t : ℤ) :
    |lagOp n X t| ≤ M := hX _

/-- Summability of the series in `geomLagSum`. -/
theorem geomLagSum_summable {lam : ℝ} (hl : |lam| < 1) {X : ℤ → ℝ} (hX : BddZSeq X) (n t : ℤ) :
    Summable (fun j : ℕ => lam ^ j * lagOp (n * j) X t) := by
  obtain ⟨M, hM⟩ := hX
  refine summable_of_abs_le (M := M) (summable_geometric_of_lt_one (abs_nonneg _) hl)
    (fun j => ?_)
  rw [abs_mul, abs_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_lagOp_le hM _ _) (by positivity)

/-- Summability of the series in `geomLagSum2`. -/
theorem geomLagSum2_summable {lam : ℝ} (hl : |lam| < 1) {X : ℤ → ℝ} (hX : BddZSeq X)
    (n t : ℤ) : Summable (fun j : ℕ => ((j : ℝ) + 1) * lam ^ j * lagOp (n * j) X t) := by
  obtain ⟨M, hM⟩ := hX
  refine summable_of_abs_le (M := M) (summable_succ_mul_geom (r := |lam|) (by simpa using hl))
    (fun j => ?_)
  rw [abs_mul, abs_mul, abs_pow, mul_comm, abs_of_nonneg (by positivity : (0 : ℝ) ≤ j + 1)]
  exact mul_le_mul_of_nonneg_right (abs_lagOp_le hM _ _) (by positivity)

theorem geomLagSum_bdd {lam : ℝ} (hl : |lam| < 1) {X : ℤ → ℝ} (hX : BddZSeq X) (n : ℤ) :
    BddZSeq (geomLagSum lam n X) := by
  obtain ⟨M, hM⟩ := hX
  refine ⟨M * ∑' j : ℕ, |lam| ^ j, fun t => ?_⟩
  refine abs_tsum_le_of_abs_le (summable_geometric_of_lt_one (abs_nonneg _) hl) (fun j => ?_)
  rw [abs_mul, abs_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_lagOp_le hM _ _) (by positivity)

theorem geomLagSum2_bdd {lam : ℝ} (hl : |lam| < 1) {X : ℤ → ℝ} (hX : BddZSeq X) (n : ℤ) :
    BddZSeq (geomLagSum2 lam n X) := by
  obtain ⟨M, hM⟩ := hX
  refine ⟨M * ∑' j : ℕ, ((j : ℝ) + 1) * |lam| ^ j, fun t => ?_⟩
  refine abs_tsum_le_of_abs_le (summable_succ_mul_geom (r := |lam|) (by simpa using hl))
    (fun j => ?_)
  rw [abs_mul, abs_mul, abs_pow, mul_comm, abs_of_nonneg (by positivity : (0 : ℝ) ≤ j + 1)]
  exact mul_le_mul_of_nonneg_right (abs_lagOp_le hM _ _) (by positivity)

/-- The first term and the shifted tail of `geomLagSum`:
`Y_t = X_t + λ Y_{t−n}`. -/
theorem geomLagSum_eq {lam : ℝ} (hl : |lam| < 1) {X : ℤ → ℝ} (hX : BddZSeq X) (n t : ℤ) :
    geomLagSum lam n X t = X t + lam * geomLagSum lam n X (t - n) := by
  simp only [geomLagSum]
  rw [(geomLagSum_summable hl hX n t).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [lagOp, pow_zero, one_mul, Nat.cast_zero, mul_zero, sub_zero]
  congr 1
  congr 1; ext j
  rw [pow_succ]
  push_cast
  rw [show t - n * ((j : ℤ) + 1) = t - n - n * j by ring]
  ring

/-- Uniqueness: a bounded `D` with `D_t = λ D_{t−n}`, `|λ| < 1`, is zero. -/
theorem eq_zero_of_bdd_of_lag {lam : ℝ} (hl : |lam| < 1) {n : ℤ} {D : ℤ → ℝ} (hD : BddZSeq D)
    (h : ∀ t, D t = lam * D (t - n)) : D = 0 := by
  obtain ⟨M, hM⟩ := hD
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have key : ∀ (k : ℕ) t, D t = lam ^ k * D (t - n * k) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [ih t, h (t - n * k), pow_succ]
      push_cast
      rw [show t - n * k - n = t - n * (k + 1) by ring]
      ring
  ext t
  have hle : ∀ k : ℕ, |D t| ≤ |lam| ^ k * M := fun k => by
    rw [key k t, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM _) (by positivity)
  have hlim : Tendsto (fun k : ℕ => |lam| ^ k * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg lam) hl).mul_const M
  have := ge_of_tendsto' hlim hle
  simpa using abs_nonpos_iff.1 this

/-- **Lag-operator expansion** (Miao, p. 11): `1/(1 − λLⁿ) = Σ_{j≥0} λʲ L^{nj}` for `|λ| < 1`.
For bounded `X`, `Y = Σ λʲ L^{nj} X` is bounded, solves `(1 − λLⁿ)Y = X`, and is the unique
bounded solution. -/
theorem lag_inverse_geom {lam : ℝ} (hl : |lam| < 1) (n : ℤ) {X : ℤ → ℝ} (hX : BddZSeq X) :
    oneSubLag lam n (geomLagSum lam n X) = X ∧ BddZSeq (geomLagSum lam n X) ∧
      ∀ Y, BddZSeq Y → oneSubLag lam n Y = X → Y = geomLagSum lam n X := by
  have hsol : oneSubLag lam n (geomLagSum lam n X) = X := by
    ext t
    simp only [oneSubLag, lagOp]
    rw [geomLagSum_eq hl hX n t]
    ring
  refine ⟨hsol, geomLagSum_bdd hl hX n, fun Y hY hYX => ?_⟩
  have hD : BddZSeq (fun t => Y t - geomLagSum lam n X t) := by
    obtain ⟨M, hM⟩ := hY
    obtain ⟨M', hM'⟩ := geomLagSum_bdd hl hX n
    exact ⟨M + M', fun t => (abs_sub _ _).trans (add_le_add (hM t) (hM' t))⟩
  have h0 := eq_zero_of_bdd_of_lag hl hD (n := n) (fun t => by
    have h1 := congrFun hYX t
    have h2 := congrFun hsol t
    simp only [oneSubLag, lagOp] at h1 h2
    linarith)
  ext t
  have := congrFun h0 t
  simp only [Pi.zero_apply] at this
  linarith

/-- `(1 − λLⁿ)` applied to `Σ (j+1)λʲ L^{nj}X` gives `Σ λʲ L^{nj}X`. -/
theorem oneSubLag_geomLagSum2 {lam : ℝ} (hl : |lam| < 1) (n : ℤ) {X : ℤ → ℝ}
    (hX : BddZSeq X) : oneSubLag lam n (geomLagSum2 lam n X) = geomLagSum lam n X := by
  ext t
  simp only [oneSubLag]
  rw [show lagOp n (geomLagSum2 lam n X) t = geomLagSum2 lam n X (t - n) from rfl]
  simp only [geomLagSum2, geomLagSum]
  set A : ℕ → ℝ := fun j => ((j : ℝ) + 1) * lam ^ j * lagOp (n * j) X t with hAdef
  set B : ℕ → ℝ := fun j => ((j : ℝ) + 1) * lam ^ j * lagOp (n * j) X (t - n) with hBdef
  set C : ℕ → ℝ := fun j => lam ^ j * lagOp (n * j) X t with hCdef
  have hA : Summable A := geomLagSum2_summable hl hX n t
  have hB : Summable (fun j => lam * B j) := (geomLagSum2_summable hl hX n (t - n)).mul_left lam
  have hC : Summable C := geomLagSum_summable hl hX n t
  have hA' : Summable (fun j => A (j + 1)) := (summable_nat_add_iff 1).2 hA
  have e1 : ∑' j, A j = A 0 + ∑' j, A (j + 1) := hA.tsum_eq_zero_add
  have e2 : ∑' j, C j = C 0 + ∑' j, C (j + 1) := hC.tsum_eq_zero_add
  have e3 : ∑' j, (A (j + 1) - lam * B j) = ∑' j, A (j + 1) - ∑' j, lam * B j :=
    hA'.tsum_sub hB
  have e4 : ∑' j, (A (j + 1) - lam * B j) = ∑' j, C (j + 1) := by
    refine tsum_congr (fun j => ?_)
    simp only [hAdef, hBdef, hCdef, lagOp]
    push_cast
    rw [show t - n * ((j : ℤ) + 1) = t - n - n * j by ring, pow_succ]
    ring
  have e5 : ∑' j, lam * B j = lam * ∑' j, B j := tsum_mul_left
  have e6 : A 0 = C 0 := by simp [hAdef, hCdef]
  linarith

/-- **Lag-operator expansion** (Miao, p. 11): `1/(1 − λLⁿ)² = Σ_{j≥0} (j + 1)λʲ L^{nj}` for
`|λ| < 1`. For bounded `X`, `Y = Σ (j+1)λʲ L^{nj} X` is bounded, solves `(1 − λLⁿ)²Y = X`, and
is the unique bounded solution. -/
theorem lag_inverse_geom_sq {lam : ℝ} (hl : |lam| < 1) (n : ℤ) {X : ℤ → ℝ} (hX : BddZSeq X) :
    oneSubLag lam n (oneSubLag lam n (geomLagSum2 lam n X)) = X ∧
      BddZSeq (geomLagSum2 lam n X) ∧
      ∀ Y, BddZSeq Y → oneSubLag lam n (oneSubLag lam n Y) = X → Y = geomLagSum2 lam n X := by
  obtain ⟨h1, h1B, h1U⟩ := lag_inverse_geom hl n hX
  have h2 := oneSubLag_geomLagSum2 hl n hX
  refine ⟨by rw [h2, h1], geomLagSum2_bdd hl hX n, fun Y hY hYX => ?_⟩
  have hVB : BddZSeq (oneSubLag lam n Y) := by
    obtain ⟨M, hM⟩ := hY
    refine ⟨M + |lam| * M, fun t => ?_⟩
    simp only [oneSubLag, lagOp]
    refine (abs_sub _ _).trans (add_le_add (hM t) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
  have hV := h1U _ hVB hYX
  obtain ⟨-, -, hU⟩ := lag_inverse_geom hl n h1B
  rw [hU Y hY hV, hU _ (geomLagSum2_bdd hl hX n) h2]

/-- Miao, p. 11, scalar form: `1/(1 − λ) = Σ_{j≥0} λʲ` for `|λ| < 1`. -/
theorem lag_scalar_geom {lam : ℝ} (hl : |lam| < 1) : 1 / (1 - lam) = ∑' j : ℕ, lam ^ j := by
  rw [tsum_geometric_of_abs_lt_one hl, one_div]

/-- Miao, p. 11, scalar form: `1/(1 − λ)² = Σ_{j≥0} (j + 1)λʲ` for `|λ| < 1`. -/
theorem lag_scalar_geom_sq {lam : ℝ} (hl : |lam| < 1) :
    1 / (1 - lam) ^ 2 = ∑' j : ℕ, ((j : ℝ) + 1) * lam ^ j := by
  have hl1 : 1 - lam ≠ 0 := by
    intro h; have : lam = 1 := by linarith
    rw [this] at hl; norm_num at hl
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := lam) (by rwa [Real.norm_eq_abs])
  have h2 := summable_geometric_of_abs_lt_one hl
  have : (fun j : ℕ => ((j : ℝ) + 1) * lam ^ j) = fun j : ℕ => (j : ℝ) * lam ^ j + lam ^ j := by
    ext j; ring
  rw [this, (by simpa using h1 : Summable (fun j : ℕ => (j : ℝ) * lam ^ j)).tsum_add h2,
    tsum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs]),
    tsum_geometric_of_abs_lt_one hl]
  field_simp
  ring

end Miao.DifferenceEquations
