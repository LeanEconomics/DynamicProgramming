/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ApproximationAndLearning.BoundedMeasurable
import ApproximationAndLearning.FittedVI
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Approximation methods

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.1.1 (pp. 296–299), with
Lemma 9.1.6 and Remark 9.1.2 (p. 303).

* Kernel averagers (9.2)–(9.3): `(Lf)(x) = ∑ᵢ f(xᵢ)κᵢ(x)` with nonnegative weights summing to
  one. **Lemma 9.1.1**: `L` maps `bX` into itself and is nonexpansive in the supremum norm.
  **Lemma 9.1.6**: `L` is order preserving. **Remark 9.1.2**: so fitted value iteration with a
  kernel averager satisfies the hypotheses of §9.1.2.
* **Example 9.1.1**: Gaussian kernel averagers satisfy (9.2).
* **Example 9.1.2**: the hat functions of a grid `x₀ < ⋯ < xₙ` satisfy (9.2); the kernel
  averager interpolates `f` at the grid points, is affine between them, and is the unique such
  function.
* Global approximation (p. 299): with `Z` of full column rank, `θ̂ = (ZᵀZ)⁻¹Zᵀy` is the unique
  minimizer of the sum of squared residuals.
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

/-- A kernel averager (9.2)–(9.3): grid points `xᵢ` and measurable weights `κᵢ ≥ 0` with
`∑ᵢ κᵢ = 1`. -/
structure KernelAverager (X : Type*) [MeasurableSpace X] (n : ℕ) where
  /-- the grid points -/
  grid : Fin n → X
  /-- the weighting functions -/
  κ : Fin n → X → ℝ
  measurable_κ : ∀ i, Measurable (κ i)
  κ_nonneg : ∀ i x, 0 ≤ κ i x
  sum_κ : ∀ x, ∑ i, κ i x = 1

namespace KernelAverager

variable {X : Type*} [MeasurableSpace X] {n : ℕ} (K : KernelAverager X n)

/-- (9.3): `(Lf)(x) = ∑ᵢ f(xᵢ)κᵢ(x)`. -/
noncomputable def Lfun (f : X → ℝ) (x : X) : ℝ := ∑ i, f (K.grid i) * K.κ i x

theorem κ_le_one (i : Fin n) (x : X) : K.κ i x ≤ 1 := by
  have h := Finset.single_le_sum (fun j _ => K.κ_nonneg j x) (Finset.mem_univ i)
  rwa [K.sum_κ] at h

/-- `|Lf| ≤ C` when `|f| ≤ C`: `Lf(x)` is an average. -/
theorem abs_Lfun_le {f : X → ℝ} {C : ℝ} (hf : ∀ y, |f y| ≤ C) (x : X) : |K.Lfun f x| ≤ C := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |f (K.grid i) * K.κ i x| ≤ ∑ i, C * K.κ i x := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (K.κ_nonneg i x)]
        exact mul_le_mul_of_nonneg_right (hf _) (K.κ_nonneg i x)
    _ = C := by rw [← Finset.mul_sum, K.sum_κ, mul_one]

theorem Lfun_sub (f g : X → ℝ) (x : X) : K.Lfun f x - K.Lfun g x = K.Lfun (f - g) x := by
  unfold Lfun
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, sub_mul]

theorem Lfun_const (c : ℝ) (x : X) : K.Lfun (fun _ => c) x = c := by
  rw [Lfun, ← Finset.mul_sum, K.sum_κ, mul_one]

theorem measurable_Lfun (f : X → ℝ) : Measurable (K.Lfun f) :=
  Finset.measurable_sum _ fun i _ => measurable_const.mul (K.measurable_κ i)

/-- **Lemma 9.1.1** (p. 298), first part: `L` maps `bX` into itself. -/
noncomputable def L (f : BM X) : BM X :=
  ⟨K.Lfun f.toFun, K.measurable_Lfun _, ⟨‖f‖, fun x => K.abs_Lfun_le (BM.abs_le_norm f) x⟩⟩

theorem L_apply (f : BM X) (x : X) : (K.L f).toFun x = K.Lfun f.toFun x := rfl

/-- **Lemma 9.1.1** (p. 298), second part: `L` is nonexpansive under the supremum norm. -/
theorem lemma_9_1_1 (f g : BM X) : dist (K.L f) (K.L g) ≤ dist f g :=
  BM.dist_le dist_nonneg fun x => by
    rw [L_apply, L_apply, Lfun_sub]
    exact K.abs_Lfun_le (fun y => BM.abs_sub_le_dist f g y) x

/-- **Lemma 9.1.6** (p. 303): `L` is order preserving on `(bX, ≤)`. -/
theorem lemma_9_1_6 : Monotone K.L := fun f g hfg => BM.le_def.2 fun x => by
  change ∑ i, f.toFun (K.grid i) * K.κ i x ≤ ∑ i, g.toFun (K.grid i) * K.κ i x
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (BM.le_def.1 hfg _) (K.κ_nonneg i x)

/-- **Remark 9.1.2** (p. 303): a kernel averager is nonexpansive and order preserving on `bX`, so
Lemma 9.1.2, Theorems 9.1.3–9.1.4 and Proposition 9.1.5 apply to it. -/
theorem remark_9_1_2 : ADP.Nonexpansive K.L ∧ Monotone K.L := ⟨K.lemma_9_1_1, K.lemma_9_1_6⟩

end KernelAverager

/-! ### Example 9.1.1: Gaussian kernels -/

/-- The Gaussian kernel `K_h(x, xᵢ) = exp(−‖x − xᵢ‖²/(2h²))`. -/
noncomputable def gaussKernel {E : Type*} [NormedAddCommGroup E] (h : ℝ) (x y : E) : ℝ :=
  Real.exp (-(‖x - y‖ ^ 2) / (2 * h ^ 2))

/-- **Example 9.1.1** (p. 297): `κᵢ(x) = K_h(x, xᵢ)/∑ⱼ K_h(x, xⱼ)` satisfies (9.2), so it defines a
kernel averager. -/
noncomputable def gaussianAverager {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {n : ℕ} [NeZero n] (grid : Fin n → E) (h : ℝ) :
    KernelAverager E n where
  grid := grid
  κ i x := gaussKernel h x (grid i) / ∑ j, gaussKernel h x (grid j)
  measurable_κ i := by
    have hc : ∀ j, Continuous fun x : E => gaussKernel h x (grid j) := fun j =>
      Real.continuous_exp.comp (((continuous_id.sub continuous_const).norm.pow 2).neg.div_const _)
    exact ((hc i).div (continuous_finsetSum _ fun j _ => hc j) fun x =>
      (Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty).ne').measurable
  κ_nonneg i x := div_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le)
  sum_κ x := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ (Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty).ne'

/-! ### Example 9.1.2: piecewise linear interpolation -/

/-- The hat function `κᵢ` of the grid `x₀ < x₁ < ⋯ < xₙ`, extended by `1` beyond the end points
(the "obvious modifications"). -/
noncomputable def hat (x : ℕ → ℝ) (n i : ℕ) (t : ℝ) : ℝ :=
  if t ≤ x i then (if i = 0 then 1 else max 0 ((t - x (i - 1)) / (x i - x (i - 1))))
  else (if i = n then 1 else max 0 ((x (i + 1) - t) / (x (i + 1) - x i)))

namespace Hat

variable {x : ℕ → ℝ} (hx : StrictMono x) {n : ℕ}

theorem hat_nonneg (i : ℕ) (t : ℝ) : 0 ≤ hat x n i t := by
  unfold hat
  split_ifs <;> first | exact zero_le_one | exact le_max_left _ _

include hx in
/-- On `[xⱼ, xⱼ₊₁]` only `κⱼ` and `κⱼ₊₁` are nonzero, and they are the linear weights. -/
theorem hat_on {j : ℕ} (hj : j < n) {t : ℝ} (ht : t ∈ Set.Icc (x j) (x (j + 1))) (i : ℕ) :
    hat x n i t = if i = j then (x (j + 1) - t) / (x (j + 1) - x j)
      else if i = j + 1 then (t - x j) / (x (j + 1) - x j) else 0 := by
  have hΔ : 0 < x (j + 1) - x j := sub_pos.2 (hx (Nat.lt_succ_self j))
  unfold hat
  rcases lt_trichotomy i j with hij | rfl | hij
  · -- `i < j`
    have hti : ¬ t ≤ x i := not_le.2 ((hx hij).trans_le ht.1)
    have hin : i ≠ n := by omega
    have h1 : x (i + 1) ≤ t := (hx.monotone (by omega : i + 1 ≤ j)).trans ht.1
    have hd : 0 < x (i + 1) - x i := sub_pos.2 (hx (Nat.lt_succ_self i))
    have h2 : i ≠ j := by omega
    have h3 : i ≠ j + 1 := by omega
    simp only [hti, hin, h2, h3, ↓reduceIte]
    exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
  · -- `i = j`
    simp only [↓reduceIte]
    by_cases htj : t ≤ x i
    · have hteq : t = x i := le_antisymm htj ht.1
      subst hteq
      simp only [htj, ↓reduceIte, div_self hΔ.ne']
      split_ifs with h0
      · rfl
      · have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
        rw [div_self hd.ne', max_eq_right zero_le_one]
    · have hin : i ≠ n := by omega
      simp only [htj, hin, ↓reduceIte]
      exact max_eq_right (div_nonneg (by linarith [ht.2]) hΔ.le)
  · rcases (Nat.succ_le_of_lt hij).eq_or_lt with hij' | hij'
    · -- `i = j + 1`
      subst hij'
      have h0 : j + 1 ≠ j := by omega
      have h1 : j + 1 ≠ 0 := by omega
      simp only [ht.2, ↓reduceIte, h0, h1, Nat.succ_sub_one]
      exact max_eq_right (div_nonneg (by linarith [ht.1]) hΔ.le)
    · -- `i > j + 1`
      have hti : t ≤ x i := ht.2.trans (hx hij').le
      have h1 : t ≤ x (i - 1) := ht.2.trans (hx.monotone (by omega))
      have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
      have h2 : i ≠ 0 := by omega
      have h3 : i ≠ j := by omega
      have h4 : i ≠ j + 1 := by omega
      simp only [hti, ↓reduceIte, h2, h3, h4]
      exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)

include hx in
theorem hat_left {t : ℝ} (ht : t ≤ x 0) (i : ℕ) : hat x n i t = if i = 0 then 1 else 0 := by
  unfold hat
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [ht]
  · have hti : t ≤ x i := ht.trans (hx.monotone (Nat.zero_le i))
    have h1 : t ≤ x (i - 1) := ht.trans (hx.monotone (Nat.zero_le _))
    have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
    have h2 : i ≠ 0 := by omega
    simp only [hti, ↓reduceIte, h2]
    exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)

include hx in
theorem hat_right (hn : 1 ≤ n) {t : ℝ} (ht : x n ≤ t) {i : ℕ} (hi : i ≤ n) :
    hat x n i t = if i = n then 1 else 0 := by
  unfold hat
  rcases hi.lt_or_eq with hi | rfl
  · have hti : ¬ t ≤ x i := not_le.2 ((hx hi).trans_le ht)
    have h1 : x (i + 1) ≤ t := (hx.monotone (by omega)).trans ht
    have hd : 0 < x (i + 1) - x i := sub_pos.2 (hx (Nat.lt_succ_self i))
    have hin : i ≠ n := by omega
    simp only [hti, hin, ↓reduceIte]
    exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
  · simp only [↓reduceIte]
    split_ifs with h1 h2
    · omega
    · have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
      rw [le_antisymm h1 ht, div_self hd.ne', max_eq_right zero_le_one]
    · rfl

/-- Every `t ∈ [x₀, xₙ]` lies in some `[xⱼ, xⱼ₊₁]`, `j < n`. -/
theorem exists_interval (hn : 1 ≤ n) {t : ℝ} (h0 : x 0 ≤ t) (hn' : t ≤ x n) :
    ∃ j < n, t ∈ Set.Icc (x j) (x (j + 1)) := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨0, one_pos, h0, hn'⟩
  | succ m hm ih =>
    by_cases htm : t ≤ x m
    · obtain ⟨j, hj, hjt⟩ := ih htm
      exact ⟨j, by omega, hjt⟩
    · exact ⟨m, by omega, (not_le.1 htm).le, hn'⟩

/-- The sum of `f(i)` over `Fin (n + 1)` for a function vanishing off `{j, j + 1}`. -/
theorem sum_two {n j : ℕ} (hj : j < n) (a b : ℝ) :
    ∑ i : Fin (n + 1), (if (i : ℕ) = j then a else if (i : ℕ) = j + 1 then b else 0) = a + b := by
  have e : ∀ i : ℕ, (if i = j then a else if i = j + 1 then b else 0) =
      (if i = j then a else 0) + (if i = j + 1 then b else 0) := fun i => by
    split_ifs <;> first | omega | ring
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = j then a else if i = j + 1 then b else 0)]
  have h1 : j < n + 1 := by omega
  have h2 : j + 1 < n + 1 := by omega
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, h1, h2,
    ↓reduceIte]

include hx in
/-- (9.2) for the hat functions: they sum to one everywhere. -/
theorem sum_hat (hn : 1 ≤ n) (t : ℝ) : ∑ i : Fin (n + 1), hat x n i t = 1 := by
  by_cases h0 : t ≤ x 0
  · simp only [hat_left hx h0]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i = 0 then (1 : ℝ) else 0),
      Finset.sum_ite_eq' (Finset.range (n + 1)) 0 fun _ => (1 : ℝ)]
    simp
  by_cases hn' : x n ≤ t
  · rw [Finset.sum_congr rfl fun i _ => hat_right hx hn hn' (Nat.lt_succ_iff.1 i.2),
      Fin.sum_univ_eq_sum_range (fun i => if i = n then (1 : ℝ) else 0),
      Finset.sum_ite_eq' (Finset.range (n + 1)) n fun _ => (1 : ℝ)]
    simp
  obtain ⟨j, hj, hjt⟩ := exists_interval hn (not_le.1 h0).le (not_le.1 hn').le
  have hΔ : 0 < x (j + 1) - x j := sub_pos.2 (hx (Nat.lt_succ_self j))
  rw [Finset.sum_congr rfl fun (i : Fin (n + 1)) _ => hat_on hx hj hjt (i : ℕ), sum_two hj]
  field_simp
  ring

include hx in
/-- The hat functions interpolate: `κᵢ(xⱼ) = 𝟙{i = j}`. -/
theorem hat_grid (hn : 1 ≤ n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    hat x n i (x j) = if i = j then 1 else 0 := by
  rcases hj.lt_or_eq with hj | rfl
  · have hΔ : 0 < x (j + 1) - x j := sub_pos.2 (hx (Nat.lt_succ_self j))
    rw [hat_on hx hj ⟨le_rfl, (hx (Nat.lt_succ_self j)).le⟩ i]
    split_ifs <;> first | omega | rfl | (rw [div_self hΔ.ne']) | (rw [sub_self, zero_div])
  · exact hat_right hx hn le_rfl hi

include hx in
theorem continuous_hat (i : ℕ) : Continuous (hat x n i) := by
  unfold hat
  refine Continuous.if_le ?_ ?_ continuous_id continuous_const fun t ht => ?_
  · split_ifs
    · exact continuous_const
    · exact continuous_const.max ((continuous_id.sub continuous_const).div_const _)
  · split_ifs
    · exact continuous_const
    · exact continuous_const.max ((continuous_const.sub continuous_id).div_const _)
  · subst ht
    split_ifs with h1 h2
    · rfl
    · have hd : 0 < x (i + 1) - x i := sub_pos.2 (hx (Nat.lt_succ_self i))
      rw [div_self hd.ne', max_eq_right zero_le_one]
    · have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
      rw [div_self hd.ne', max_eq_right zero_le_one]
    · have hd : 0 < x i - x (i - 1) := sub_pos.2 (hx (by omega))
      have hd' : 0 < x (i + 1) - x i := sub_pos.2 (hx (Nat.lt_succ_self i))
      rw [div_self hd.ne', div_self hd'.ne']

end Hat

open Hat

/-- **Example 9.1.2** (p. 297): the hat functions of a strictly increasing grid
`x₀ < x₁ < ⋯ < xₙ` define a kernel averager on `ℝ`. -/
noncomputable def hatAverager {x : ℕ → ℝ} (hx : StrictMono x) {n : ℕ} (hn : 1 ≤ n) :
    KernelAverager ℝ (n + 1) where
  grid i := x i
  κ i := hat x n i
  measurable_κ i := (continuous_hat hx i).measurable
  κ_nonneg i t := hat_nonneg i t
  sum_κ t := sum_hat hx hn t


variable {x : ℕ → ℝ} (hx : StrictMono x) {n : ℕ} (hn : 1 ≤ n)

include hx hn in
/-- **Example 9.1.2**: the kernel averager agrees with `f` at the grid points. -/
theorem example_9_1_2_interpolates (f : ℝ → ℝ) {j : ℕ} (hj : j ≤ n) :
    (hatAverager hx hn).Lfun f (x j) = f (x j) := by
  change ∑ i : Fin (n + 1), f (x i) * hat x n i (x j) = f (x j)
  simp only [hat_grid hx hn (Nat.lt_succ_iff.1 (Fin.is_lt _)) hj, mul_ite, mul_one, mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = j then f (x i) else 0),
    Finset.sum_ite_eq' (Finset.range (n + 1)) j fun i => f (x i)]
  simp [Nat.lt_succ_iff.2 hj]

include hx hn in
/-- **Example 9.1.2**: between grid points the kernel averager is the linear interpolant. -/
theorem example_9_1_2_linear (f : ℝ → ℝ) {j : ℕ} (hj : j < n) {t : ℝ}
    (ht : t ∈ Set.Icc (x j) (x (j + 1))) :
    (hatAverager hx hn).Lfun f t =
      f (x j) * ((x (j + 1) - t) / (x (j + 1) - x j)) +
        f (x (j + 1)) * ((t - x j) / (x (j + 1) - x j)) := by
  change ∑ i : Fin (n + 1), f (x i) * hat x n i t = _
  simp only [hat_on hx hj ht, mul_ite, mul_zero]
  have e : ∀ i : ℕ, (if i = j then f (x i) * ((x (j + 1) - t) / (x (j + 1) - x j)) else
      if i = j + 1 then f (x i) * ((t - x j) / (x (j + 1) - x j)) else 0) =
      (if i = j then f (x j) * ((x (j + 1) - t) / (x (j + 1) - x j)) else
      if i = j + 1 then f (x (j + 1)) * ((t - x j) / (x (j + 1) - x j)) else 0) := fun i => by
    split_ifs with h1 h2 <;> first | rfl | (subst h1; rfl) | (subst h2; rfl)
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = j then f (x i) * ((x (j + 1) - t) /
    (x (j + 1) - x j)) else if i = j + 1 then f (x i) * ((t - x j) / (x (j + 1) - x j)) else 0)]
  simp only [e]
  rw [← Fin.sum_univ_eq_sum_range (fun i => if i = j then f (x j) * ((x (j + 1) - t) /
    (x (j + 1) - x j)) else if i = j + 1 then f (x (j + 1)) * ((t - x j) / (x (j + 1) - x j))
    else 0), sum_two hj]

include hx hn in
/-- **Example 9.1.2**: `Lf` is continuous, and it is the unique function that agrees with `f` at
the grid points and is affine on each `[xⱼ, xⱼ₊₁]`. -/
theorem example_9_1_2_unique (f : ℝ → ℝ) :
    Continuous ((hatAverager hx hn).Lfun f) ∧
      ∀ g : ℝ → ℝ, (∀ j ≤ n, g (x j) = f (x j)) →
        (∀ j < n, ∃ c d : ℝ, ∀ t ∈ Set.Icc (x j) (x (j + 1)), g t = c + d * t) →
        ∀ t ∈ Set.Icc (x 0) (x n), g t = (hatAverager hx hn).Lfun f t := by
  refine ⟨continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_hat hx i),
    fun g hg haff t ht => ?_⟩
  obtain ⟨j, hj, hjt⟩ := exists_interval hn ht.1 ht.2
  obtain ⟨c, d, hcd⟩ := haff j hj
  have hΔ : 0 < x (j + 1) - x j := sub_pos.2 (hx (Nat.lt_succ_self j))
  have h1 := hcd (x j) ⟨le_rfl, (hx (Nat.lt_succ_self j)).le⟩
  have h2 := hcd (x (j + 1)) ⟨(hx (Nat.lt_succ_self j)).le, le_rfl⟩
  rw [hg j hj.le] at h1
  rw [hg (j + 1) hj] at h2
  rw [example_9_1_2_linear hx hn f hj hjt, hcd t hjt, h1, h2]
  field_simp
  ring

/-! ### Global approximation by least squares -/

/-- The least squares coefficients `θ̂ = (ZᵀZ)⁻¹Zᵀy`. -/
noncomputable def lsq {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) : Fin k → ℝ :=
  (Z.transpose * Z)⁻¹.mulVec (Z.transpose.mulVec y)

/-- The sum of squared residuals `∑ᵢ [(G_θ f)(xᵢ) − f(xᵢ)]²` with `Zᵢⱼ = bⱼ(xᵢ)`. -/
def ssr {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) (θ : Fin k → ℝ) : ℝ :=
  ∑ i, (Z.mulVec θ i - y i) ^ 2

/-- Global approximation (p. 299): if `Z` has full column rank (`θ ↦ Zθ` is injective), then
`θ̂ = (ZᵀZ)⁻¹Zᵀy` minimizes the sum of squared residuals, uniquely. -/
theorem least_squares {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ)
    (hZ : Injective Z.mulVec) (θ : Fin k → ℝ) :
    ssr Z y (lsq Z y) ≤ ssr Z y θ ∧ (ssr Z y θ = ssr Z y (lsq Z y) → θ = lsq Z y) := by
  have hdot : ∀ v : Fin n → ℝ, ∑ i, v i ^ 2 = v ⬝ᵥ v := fun v => by
    simp only [dotProduct, sq]
  -- `ZᵀZ` is invertible
  have hinj : Injective (Z.transpose * Z).mulVec := by
    intro a b hab
    have h0 : (Z.transpose * Z).mulVec (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    have h1 : Z.mulVec (a - b) ⬝ᵥ Z.mulVec (a - b) = 0 := by
      have := congrArg (dotProduct (a - b)) h0
      rwa [dotProduct_zero, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose] at this
    have h2 : Z.mulVec (a - b) = Z.mulVec 0 := by
      rw [dotProduct_self_eq_zero.1 h1, Matrix.mulVec_zero]
    exact sub_eq_zero.1 (hZ h2)
  have hunit : IsUnit (Z.transpose * Z) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit (Z.transpose * Z).det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  -- the normal equations `Zᵀ(Zθ̂ − y) = 0`
  have hnormal : Z.transpose.mulVec (Z.mulVec (lsq Z y) - y) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, lsq, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, sub_self]
  set r := Z.mulVec (lsq Z y) - y
  have hsplit : Z.mulVec θ - y = Z.mulVec (θ - lsq Z y) + r := by
    simp only [r, Matrix.mulVec_sub]
    abel
  have hcross : Z.mulVec (θ - lsq Z y) ⬝ᵥ r = 0 := by
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, hnormal, dotProduct_zero]
  have hpy : ssr Z y θ = Z.mulVec (θ - lsq Z y) ⬝ᵥ Z.mulVec (θ - lsq Z y) + ssr Z y (lsq Z y) := by
    have e1 : ssr Z y θ = (Z.mulVec θ - y) ⬝ᵥ (Z.mulVec θ - y) := hdot (Z.mulVec θ - y)
    have e2 : ssr Z y (lsq Z y) = r ⬝ᵥ r := hdot r
    rw [e1, e2, hsplit, add_dotProduct, dotProduct_add, dotProduct_add, hcross,
      dotProduct_comm r, hcross]
    ring
  refine ⟨?_, fun h => ?_⟩
  · rw [hpy]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  · rw [hpy] at h
    have h0 : Z.mulVec (θ - lsq Z y) ⬝ᵥ Z.mulVec (θ - lsq Z y) = 0 := by linarith
    have h2 : Z.mulVec (θ - lsq Z y) = Z.mulVec 0 := by
      rw [dotProduct_self_eq_zero.1 h0, Matrix.mulVec_zero]
    exact sub_eq_zero.1 (hZ h2)

end SargentStachurski.ApproximationAndLearning
