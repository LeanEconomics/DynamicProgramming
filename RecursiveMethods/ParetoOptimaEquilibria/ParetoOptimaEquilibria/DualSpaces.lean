/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Dual spaces and the Hahn–Banach theorem

SLP §15.1, pp. 445–451 (and one remark from the chapter introduction, p. 444). `S` is a real
normed space and `S*` is `StrongDual ℝ S`, the continuous linear functionals with the operator
norm. The sequence spaces are Mathlib's `lp`: `ellInfSp = ℓ∞`, `ellOneSp = ℓ₁`, `ellTwoSp = ℓ₂`
(sequences indexed by `ℕ`). `L_p(Z, 𝒵, μ)` is `MeasureTheory.Lp ℝ p μ`.

* **Theorem 15.1** (p. 446). The book's continuity is sequential (`SeqContAt`).
  (a) `theorem_15_1a`: a linear functional continuous at one point is continuous at every point.
  (b) `theorem_15_1b`: it is continuous iff it is bounded, `|φ x| ≤ M ‖x‖`.
  `continuous_iff_seqContAt` links the book's continuity with Mathlib's.
  `dual_norm_eq`: the dual norm (1) is the infimum of the bounds, equals the supremum of `|φ x|`
  over the unit sphere, and is itself a bound.
* **Exercise 15.1** (`ex_15_1`, p. 447): `S*` is complete.
* **Example 1** (`example_15_1`, p. 447): `y ↦ (x ↦ y · x)` is an isometric isomorphism from
  `ℝⁿ` onto `(ℝⁿ)*`.
* **Exercise 15.2** (p. 448). (a) `ex_15_2a`: `ℓ₂* = ℓ₂` and (b) `ex_15_2b`: `ℓ₁* = ℓ∞`. In both,
  `y ↦ (x ↦ Σ yᵢ xᵢ)` is an isometric isomorphism onto the dual.
* **Example 2** (`example_15_2`, p. 448): for `1 < p < ∞` and `1/p + 1/q = 1`,
  `y ↦ (x ↦ Σ yᵢ xᵢ)` is an isometric isomorphism from `ℓ_q` onto `ℓ_p*` (`dualEllP`). The
  test vectors `sgn(yᵢ)|yᵢ|^{q−1}` give `‖y‖_q ≤ ‖φ‖` (`sum_rpow_le_of_dual_ellP`).
* **Exercise 15.3** (`ex_15_3`, p. 448): each `y ∈ ℓ₁` gives a continuous linear functional
  `x ↦ Σ yᵢ xᵢ` on `ℓ∞`, of norm `≤ ‖y‖₁`.
* **Exercise 15.4** (p. 448). `cZero` is `c₀` as a subspace of `ℓ∞`, so it is a normed space with
  the sup norm. (a) `ex_15_4a`: it is closed, hence complete. (b) `ex_15_4b`: `c₀* = ℓ₁`, again
  by an isometric isomorphism `y ↦ (x ↦ Σ yᵢ xᵢ)`.
* **Exercise 15.5** (p. 450). (a) `ex_15_5a`: each `f ∈ L₁` gives `φ(x) = ∫ f x dμ` in `L∞*`, of
  norm `≤ ‖f‖₁`. (b) `ex_15_5b`: the same `φ` is `x ↦ ∫ x dν` for the signed measure
  `ν = f μ`, which is absolutely continuous with respect to `μ`.
* **`L₁* = L∞`** (p. 449). `l1_dual_sigmaFinite`: for a σ-finite measure,
  `y ↦ (x ↦ ∫ y x dμ)` is an isometric isomorphism from `L∞` onto `L₁*` (`dualL1`). The proof
  (`exists_preimage_pairLinfL1`) applies Riesz representation in `L₂` to `x ↦ φ(√w x)`, where
  `w > 0` is integrable.
* **Example (p. 450)** (`example_15_4_linf_nat`): if `ν` is a finite measure on `ℕ` with
  `ν {n} > 0` for all `n`, then `L∞(ℕ, ν) ≅ ℓ∞` isometrically.
* **Theorem 15.2** (`theorem_15_2`, the geometric Hahn–Banach theorem, pp. 450–451), with the
  nonemptiness hypotheses added. The two cases are `theorem_15_2_interior` and
  `theorem_15_2_finiteDimensional`.
* **Exercise 15.6** (`ex_15_6`, p. 451): in `S = {x : Σ βᵗ |xₜ| < ∞}`, every ball about `θ` has
  points outside the box `B = {|xₜ| ≤ 1}`. `weightToEllOne` maps `S` isometrically onto `ℓ₁`,
  `xₜ ↦ βᵗ xₜ`, and maps `B` onto `ex156Box β = {z : |zₜ| ≤ βᵗ}`. On that side,
  `interior_ex156Box` shows `B̊ = ∅`, `eq_zero_of_le_zero_on_ex156Box` shows that only `φ = 0` is
  `≤ 0` on `B`, and `ex_15_6_no_separation` shows that Theorem 15.2 fails for `A = {θ}` and this
  `B`, although `A ∩ B̊ = ∅`.

**Corrections.**
* p. 444: convex upper contour sets do not make `U` concave. `intro_concavity_counterexample`:
  `U(l, c) = l³` is quasi-concave on `ℝ²` (all upper contour sets are convex) but not concave.
  Only quasi-concavity is needed.
* p. 445, (1): over `S = {θ}` the unit sphere is empty. With Mathlib's `sSup ∅ = 0` the formula
  still holds (`dual_norm_eq` has no nontriviality hypothesis).
* p. 446: the proof of Theorem 15.1(b) needs `|φ(x)| ≤ 1`, not `φ(x) ≤ 1`. The bound used in
  `theorem_15_1b` is on `|φ x|`.
* p. 449: `L₁(Z, 𝒵, μ)* = L∞(Z, 𝒵, μ)` is false without σ-finiteness. `l1_dual_counterexample`:
  for one point of mass `∞` (`infAtom`), `L₁ = {0}` and `L∞ ≅ ℝ`, so there is no linear
  isomorphism `L∞ ≃ L₁*`. `l1_dual_pairing_counterexample`: the map `y ↦ (x ↦ ∫ y x)` is not
  injective there. Corrected statement: `l1_dual_sigmaFinite`.
* p. 450: "`μ(A) > 0` for all `A ∈ 𝒵`" is impossible, since `μ(∅) = 0`
  (`positive_measure_counterexample`). It must say all nonempty `A`.
* p. 450, Theorem 15.2: `A` must be nonempty, and in the finite-dimensional case `B` too.
  `theorem_15_2_counterexample`: the book's statement (`BookTheorem15_2`) fails on `ℝ` with
  `A = ∅`, `B = ℝ`. `theorem_15_2_counterexample_finiteDimensional`: `A = ℝ`, `B = ∅` satisfy
  the finite-dimensional hypotheses, but no nonzero functional separates them. Corrected
  statement: `theorem_15_2`.
* Manual, Exercise 15.3: the manual gets the convergence of `Σ yₙ xₙ` from convergence of `Σ yₙ`
  and boundedness of `x`. That is not enough (`ex_15_3_manual_counterexample`:
  `yₙ = (−1)ⁿ/(n+1)`, `xₙ = (−1)ⁿ`). The proof here uses absolute summability, `Σ |yₙ| < ∞`
  (`summable_mul_of_one_inf`).
* Manual, Exercise 15.5(b): the manual never checks that `ν` represents `φ`. `ex_15_5b` proves
  `φ(x) = ∫ x dν`, using Mathlib's integral against a signed measure.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Metric Set MeasureTheory
open scoped ENNReal Pointwise symmDiff

/-! ### Theorem 15.1 and Exercise 15.1 -/

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The book's continuity at a point (p. 445): `xₙ → s` implies `f(xₙ) → f(s)`. -/
def SeqContAt (f : S → ℝ) (s : S) : Prop :=
  ∀ xs : ℕ → S, Tendsto xs atTop (𝓝 s) → Tendsto (fun n => f (xs n)) atTop (𝓝 (f s))

/-- **Theorem 15.1(a)**: a linear functional continuous at one point `s` is continuous at every
point. The proof is the book's, with `sₙ = s + xₙ − x`. -/
theorem theorem_15_1a (φ : S →ₗ[ℝ] ℝ) {s : S} (h : SeqContAt φ s) (x : S) : SeqContAt φ x := by
  intro xs hxs
  have hs : Tendsto (fun n => s + xs n - x) atTop (𝓝 s) := by
    have := (tendsto_const_nhds (x := s)).add (hxs.sub (tendsto_const_nhds (x := x)))
    simpa [add_sub_assoc] using this
  have h1 := ((h _ hs).add (tendsto_const_nhds (x := φ x))).sub (tendsto_const_nhds (x := φ s))
  have e : ∀ n, φ (s + xs n - x) + φ x - φ s = φ (xs n) := fun n => by
    rw [map_sub, map_add]; ring
  simpa [e] using h1

/-- On a normed space the book's (sequential) continuity at every point is ordinary
continuity. -/
theorem continuous_iff_seqContAt (φ : S →ₗ[ℝ] ℝ) : Continuous φ ↔ ∀ x, SeqContAt φ x := by
  rw [continuous_iff_seqContinuous]
  exact ⟨fun h x xs hxs => h hxs, fun h x p hx => h p x hx⟩

/-- **Theorem 15.1(b)**: a linear functional is continuous iff it is bounded. -/
theorem theorem_15_1b (φ : S →ₗ[ℝ] ℝ) :
    (∀ x, SeqContAt φ x) ↔ ∃ M, 0 ≤ M ∧ ∀ x, |φ x| ≤ M * ‖x‖ := by
  rw [← continuous_iff_seqContAt]
  constructor
  · intro hc
    let ψ : StrongDual ℝ S := ⟨φ, hc⟩
    exact ⟨‖ψ‖, norm_nonneg _, fun x => ψ.le_opNorm x⟩
  · rintro ⟨M, -, hM⟩
    exact AddMonoidHomClass.continuous_of_bound φ M fun x => hM x

/-- The dual norm (1), p. 445: `‖φ‖` is the infimum of the bounds `M ≥ 0`, equals the supremum
of `|φ x|` over the unit sphere, and is itself a bound. -/
theorem dual_norm_eq (φ : StrongDual ℝ S) :
    ‖φ‖ = sInf {M | 0 ≤ M ∧ ∀ x, |φ x| ≤ M * ‖x‖} ∧
      ‖φ‖ = sSup ((fun x => |φ x|) '' sphere (0 : S) 1) ∧ ∀ x, |φ x| ≤ ‖φ‖ * ‖x‖ := by
  refine ⟨by simp [ContinuousLinearMap.norm_def, Real.norm_eq_abs], ?_,
    fun x => by simpa using φ.le_opNorm x⟩
  simpa [Real.norm_eq_abs] using (φ.sSup_sphere_eq_norm).symm

/-- **Exercise 15.1**: the dual `S*`, with the norm (1), is complete (even if `S` is not). -/
theorem ex_15_1 : CompleteSpace (StrongDual ℝ S) := inferInstance

/-! ### The introduction (p. 444) -/

/-- **Correction (p. 444)**: convex upper contour sets do not give concavity. `U(l, c) = l³` is
quasi-concave on `ℝ²` but not concave. -/
theorem intro_concavity_counterexample :
    QuasiconcaveOn ℝ univ (fun p : ℝ × ℝ => p.1 ^ 3) ∧
      ¬ ConcaveOn ℝ univ (fun p : ℝ × ℝ => p.1 ^ 3) := by
  have hmono : Monotone (fun x : ℝ => x ^ 3) := (Odd.strictMono_pow (by decide)).monotone
  refine ⟨fun r => ?_, fun h => ?_⟩
  · intro p hp q hq a b ha hb hab
    refine ⟨trivial, ?_⟩
    have h1 : min p.1 q.1 ≤ a * p.1 + b * q.1 := by
      calc min p.1 q.1 = a * min p.1 q.1 + b * min p.1 q.1 := by rw [← add_mul, hab, one_mul]
        _ ≤ a * p.1 + b * q.1 := add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)
    have h2 : r ≤ (min p.1 q.1) ^ 3 := by
      rcases min_choice p.1 q.1 with h | h <;> rw [h]
      exacts [hp.2, hq.2]
    exact h2.trans (by simpa using hmono h1)
  · have := h.2 (mem_univ ((0 : ℝ), (0 : ℝ))) (mem_univ ((2 : ℝ), (0 : ℝ)))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    norm_num at this

/-! ### Example 1: `ℝⁿ` -/

/-- **Example 1** (p. 447): `y ↦ (x ↦ Σ yᵢ xᵢ)` is an isometric isomorphism from `ℝⁿ` (Euclidean
norm) onto its dual. -/
theorem example_15_1 (n : ℕ) :
    ∃ e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ y x, e y x = ∑ i, y i * x i := by
  let T : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    { toFun := fun y => InnerProductSpace.toDual ℝ _ y
      map_add' := fun y z => map_add _ y z
      map_smul' := fun c y => by ext; simp
      norm_map' := fun y => LinearIsometryEquiv.norm_map _ y }
  refine ⟨LinearIsometryEquiv.ofSurjective T fun φ =>
    ⟨(InnerProductSpace.toDual ℝ _).symm φ, by simp [T]⟩, fun y x => ?_⟩
  change InnerProductSpace.toDual ℝ _ y x = _
  rw [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply]
  simp [mul_comm]

/-! ### Sequence spaces: Exercises 15.2 and 15.3 -/

/-- `ℓ∞`: bounded real sequences with the sup norm. -/
abbrev ellInfSp := lp (fun _ : ℕ => ℝ) ∞

/-- `ℓ₁`: absolutely summable real sequences. -/
abbrev ellOneSp := lp (fun _ : ℕ => ℝ) 1

/-- `ℓ₂`: square-summable real sequences. -/
abbrev ellTwoSp := lp (fun _ : ℕ => ℝ) 2

/-- The pairing `(y, x) ↦ Σ yᵢ xᵢ` of `ℓ∞` with `ℓ₁` (Mathlib's `lp.dualPairing`). -/
noncomputable def pairInfOne : ellInfSp →L[ℝ] ellOneSp →L[ℝ] ℝ :=
  lp.dualPairing ∞ 1 (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

/-- The pairing `(y, x) ↦ Σ yᵢ xᵢ` of `ℓ₁` with `ℓ∞`. -/
noncomputable def pairOneInf : ellOneSp →L[ℝ] ellInfSp →L[ℝ] ℝ :=
  lp.dualPairing 1 ∞ (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

/-- The pairing `(y, x) ↦ Σ yᵢ xᵢ` of `ℓ₂` with itself. -/
noncomputable def pairTwo : ellTwoSp →L[ℝ] ellTwoSp →L[ℝ] ℝ :=
  lp.dualPairing 2 2 (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

/-- `pairInfOne y x = Σ yᵢ xᵢ`. -/
theorem pairInfOne_apply (y : ellInfSp) (x : ellOneSp) : pairInfOne y x = ∑' i, y i * x i := rfl

/-- `pairOneInf y x = Σ yᵢ xᵢ`. -/
theorem pairOneInf_apply (y : ellOneSp) (x : ellInfSp) : pairOneInf y x = ∑' i, y i * x i := rfl

/-- `pairTwo y x = Σ yᵢ xᵢ`. -/
theorem pairTwo_apply (y x : ellTwoSp) : pairTwo y x = ∑' i, y i * x i := rfl

/-- Hölder's inequality for `ℓ∞ × ℓ₁`: the pairing has norm `≤ 1`. -/
theorem norm_pairInfOne_le : ‖pairInfOne‖ ≤ 1 :=
  (lp.norm_dualPairing (ι := ℕ) (E := fun _ => ℝ) (F := fun _ => ℝ) (p := ∞) (q := 1) _ _).trans
    (by simp)

/-- Hölder's inequality for `ℓ₁ × ℓ∞`: the pairing has norm `≤ 1`. -/
theorem norm_pairOneInf_le : ‖pairOneInf‖ ≤ 1 :=
  (lp.norm_dualPairing (ι := ℕ) (E := fun _ => ℝ) (F := fun _ => ℝ) (p := 1) (q := ∞) _ _).trans
    (by simp)

/-- The unit sequence `eᵢ` has norm `1` in every `ℓ_p`. -/
theorem norm_single_one {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : ℕ) :
    ‖lp.single (E := fun _ : ℕ => ℝ) p i (1 : ℝ)‖ = 1 := by
  rw [lp.norm_single (zero_lt_one.trans_le Fact.out)]; simp

/-- `Σⱼ yⱼ (a eᵢ)ⱼ = yᵢ a`. -/
theorem tsum_mul_single (y : ℕ → ℝ) (i : ℕ) (a : ℝ) :
    ∑' j, y j * (Pi.single i a : ℕ → ℝ) j = y i * a := by
  rw [tsum_eq_single i]
  · simp
  · intro j hj; simp [hj]

/-- The `ℓ₁` norm is `Σ |yᵢ|`. -/
theorem norm_ellOneSp_eq_tsum (y : ellOneSp) : ‖y‖ = ∑' i, |y i| := by
  rw [lp.norm_eq_tsum_rpow (by simp)]; simp

/-- An element of `ℓ₁` is absolutely summable. -/
theorem summable_abs_ellOneSp (y : ellOneSp) : Summable fun i => |y i| := by
  simpa using (lp.memℓp y).summable (p := 1) (by simp)

/-- For `y ∈ ℓ₁` and bounded `x`, `Σ yᵢ xᵢ` converges absolutely. This uses `Σ |yᵢ| < ∞`, not
just convergence of `Σ yᵢ` (see `ex_15_3_manual_counterexample`). -/
theorem summable_mul_of_one_inf (y : ellOneSp) (x : ellInfSp) : Summable fun i => y i * x i := by
  refine Summable.of_norm_bounded ((summable_abs_ellOneSp y).mul_right ‖x‖) fun i => ?_
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) x i) (abs_nonneg _)

/-- **Exercise 15.3**: each `y ∈ ℓ₁` defines a continuous linear functional `x ↦ Σ yᵢ xᵢ` on
`ℓ∞`, with norm at most `‖y‖₁`. -/
theorem ex_15_3 (y : ellOneSp) :
    (∀ x : ellInfSp, Summable fun i => y i * x i) ∧
      ∃ φ : StrongDual ℝ ellInfSp, (∀ x, φ x = ∑' i, y i * x i) ∧ ‖φ‖ ≤ ‖y‖ := by
  refine ⟨summable_mul_of_one_inf y, pairOneInf y, fun x => rfl, ?_⟩
  calc ‖pairOneInf y‖ ≤ ‖pairOneInf‖ * ‖y‖ := pairOneInf.le_opNorm y
    _ ≤ 1 * ‖y‖ := by gcongr; exact norm_pairOneInf_le
    _ = ‖y‖ := one_mul _

/-- **Correction (manual, Exercise 15.3)**: convergence of `Σ yₙ` together with `|xₙ| ≤ 1` does
not make `Σ yₙ xₙ` converge (`yₙ = (−1)ⁿ/(n+1)`, `xₙ = (−1)ⁿ`). -/
theorem ex_15_3_manual_counterexample :
    ∃ y x : ℕ → ℝ, (∃ l, Tendsto (fun N => ∑ n ∈ Finset.range N, y n) atTop (𝓝 l)) ∧
      (∀ n, |x n| ≤ 1) ∧
      ¬ ∃ l, Tendsto (fun N => ∑ n ∈ Finset.range N, y n * x n) atTop (𝓝 l) := by
  refine ⟨fun n => (-1) ^ n * (1 / ((n : ℝ) + 1)), fun n => (-1) ^ n, ?_, fun n => by simp, ?_⟩
  · refine Antitone.tendsto_alternating_series_of_tendsto_zero ?_ ?_
    · intro m n hmn
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      dsimp only
      gcongr
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · rintro ⟨l, hl⟩
    have e : ∀ n : ℕ, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1)) * (-1) ^ n = 1 / ((n : ℝ) + 1) :=
      fun n => by
        rw [mul_comm, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
    simp only [e] at hl
    exact not_tendsto_nhds_of_tendsto_atTop Real.tendsto_sum_range_one_div_nat_succ_atTop l hl

/-- `y ↦ (x ↦ Σ yᵢ xᵢ)` preserves norms from `ℓ∞` to `ℓ₁*`. -/
theorem norm_pairInfOne (y : ellInfSp) : ‖pairInfOne y‖ = ‖y‖ := by
  apply le_antisymm
  · calc ‖pairInfOne y‖ ≤ ‖pairInfOne‖ * ‖y‖ := pairInfOne.le_opNorm y
      _ ≤ 1 * ‖y‖ := by gcongr; exact norm_pairInfOne_le
      _ = ‖y‖ := one_mul _
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun i => ?_
    have h := (pairInfOne y).le_opNorm (lp.single 1 i 1)
    rw [norm_single_one, mul_one, pairInfOne_apply, lp.coeFn_single, tsum_mul_single,
      mul_one] at h
    exact h

/-- Every `φ ∈ ℓ₁*` is `x ↦ Σ yᵢ xᵢ` with `yᵢ = φ(eᵢ)`. -/
theorem pairInfOne_surjective : Function.Surjective pairInfOne := by
  intro φ
  let y : ellInfSp := ⟨fun i => φ (lp.single 1 i 1), memℓp_infty_iff.2 ⟨‖φ‖, by
    rintro _ ⟨i, rfl⟩
    simpa [norm_single_one] using φ.le_opNorm (lp.single 1 i 1)⟩⟩
  refine ⟨y, lp.ext_continuousLinearMap (by simp) fun i => ?_⟩
  ext
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rw [pairInfOne_apply, lp.coeFn_single, tsum_mul_single, mul_one]

/-- `ℓ₁* = ℓ∞` as normed spaces. -/
noncomputable def dualEllOne : ellInfSp ≃ₗᵢ[ℝ] StrongDual ℝ ellOneSp :=
  LinearIsometryEquiv.ofSurjective ⟨pairInfOne.toLinearMap, norm_pairInfOne⟩ pairInfOne_surjective

/-- **Exercise 15.2(b)**: the dual of `ℓ₁` is `ℓ∞`. Each `y ∈ ℓ∞` gives `x ↦ Σ yᵢ xᵢ` in `ℓ₁*`,
every element of `ℓ₁*` arises from exactly one `y`, and norms are preserved. -/
theorem ex_15_2b :
    ∃ e : ellInfSp ≃ₗᵢ[ℝ] StrongDual ℝ ellOneSp, ∀ y x, e y x = ∑' i, y i * x i :=
  ⟨dualEllOne, fun _ _ => rfl⟩

/-- On `ℓ₂` the pairing is the Riesz map `y ↦ ⟪y, ·⟫`. -/
theorem pairTwo_eq_toDual (y : ellTwoSp) : pairTwo y = InnerProductSpace.toDual ℝ ellTwoSp y := by
  ext x
  rw [InnerProductSpace.toDual_apply_apply, lp.inner_eq_tsum]
  change ∑' i, y i * x i = _
  congr 1
  ext i
  simp [mul_comm]

/-- `y ↦ (x ↦ Σ yᵢ xᵢ)` preserves norms on `ℓ₂`. -/
theorem norm_pairTwo (y : ellTwoSp) : ‖pairTwo y‖ = ‖y‖ := by
  rw [pairTwo_eq_toDual, LinearIsometryEquiv.norm_map]

/-- Every `φ ∈ ℓ₂*` is `x ↦ Σ yᵢ xᵢ` for some `y ∈ ℓ₂` (Riesz representation). -/
theorem pairTwo_surjective : Function.Surjective pairTwo := fun φ =>
  ⟨(InnerProductSpace.toDual ℝ ellTwoSp).symm φ, by rw [pairTwo_eq_toDual]; simp⟩

/-- `ℓ₂* = ℓ₂` as normed spaces. -/
noncomputable def dualEllTwo : ellTwoSp ≃ₗᵢ[ℝ] StrongDual ℝ ellTwoSp :=
  LinearIsometryEquiv.ofSurjective ⟨pairTwo.toLinearMap, norm_pairTwo⟩ pairTwo_surjective

/-- **Exercise 15.2(a)**: the dual of `ℓ₂` is `ℓ₂`, with `y` acting by `x ↦ Σ yᵢ xᵢ`. -/
theorem ex_15_2a :
    ∃ e : ellTwoSp ≃ₗᵢ[ℝ] StrongDual ℝ ellTwoSp, ∀ y x, e y x = ∑' i, y i * x i :=
  ⟨dualEllTwo, fun _ _ => rfl⟩

/-! ### Example 2: `ℓ_p* = ℓ_q` for `1 < p < ∞` -/

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The pairing `(y, x) ↦ Σ yᵢ xᵢ` of `ℓ_q` with `ℓ_p` (Mathlib's `lp.dualPairing`). -/
noncomputable def pairEllP (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] :
    lp (fun _ : ℕ => ℝ) q →L[ℝ] lp (fun _ : ℕ => ℝ) p →L[ℝ] ℝ :=
  lp.dualPairing q p (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

/-- `pairEllP p q y x = Σ yᵢ xᵢ`. -/
theorem pairEllP_apply (y : lp (fun _ : ℕ => ℝ) q) (x : lp (fun _ : ℕ => ℝ) p) :
    pairEllP p q y x = ∑' i, y i * x i := rfl

/-- Hölder's inequality for `ℓ_q × ℓ_p`: the pairing has norm `≤ 1`. -/
theorem norm_pairEllP_le : ‖pairEllP p q‖ ≤ 1 :=
  (lp.norm_dualPairing (ι := ℕ) (E := fun _ => ℝ) (F := fun _ => ℝ) (p := q) (q := p) _ _).trans
    (by simp)

omit [Fact (1 ≤ q)] in
/-- For `φ ∈ ℓ_p*` and `yᵢ = φ(eᵢ)`, `Σ_{i<N} |yᵢ|^q ≤ ‖φ‖^q`. The test vector is
`xᵢ = sgn(yᵢ) |yᵢ|^{q−1}` for `i < N`, which has `φ(x) = Σ_{i<N} |yᵢ|^q = ‖x‖_p^p`. -/
theorem sum_rpow_le_of_dual_ellP (hp : p ≠ ∞) (hq : q ≠ ∞)
    (φ : StrongDual ℝ (lp (fun _ : ℕ => ℝ) p)) (N : ℕ) :
    ∑ i ∈ Finset.range N, |φ (lp.single p i 1)| ^ q.toReal ≤ ‖φ‖ ^ q.toReal := by
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  set P := p.toReal
  set Q := q.toReal
  set y : ℕ → ℝ := fun i => φ (lp.single p i 1) with hy
  have hQ1 : 0 < Q - 1 := hPQ.symm.sub_one_pos
  have hQP : (Q - 1) * P = Q := hPQ.symm.sub_one_mul_conj
  let a : ℕ → ℝ := fun i => if 0 ≤ y i then |y i| ^ (Q - 1) else -(|y i| ^ (Q - 1))
  set S := ∑ i ∈ Finset.range N, |y i| ^ Q
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hay : ∀ i, a i * y i = |y i| ^ Q := fun i => by
    have e : |y i| ^ Q = |y i| ^ (Q - 1) * |y i| := by
      conv_lhs => rw [show Q = (Q - 1) + 1 by ring]
      rw [Real.rpow_add' (abs_nonneg _) (by linarith), Real.rpow_one]
    rw [e]
    simp only [a]
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.1 h)]; ring
  have hna : ∀ i, ‖a i‖ ^ P = |y i| ^ Q := fun i => by
    have : ‖a i‖ = |y i| ^ (Q - 1) := by
      simp only [a]; split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ |y i| ^ (Q - 1))]
    rw [this, ← Real.rpow_mul (abs_nonneg _), hQP]
  set x := ∑ i ∈ Finset.range N, lp.single p i (a i)
  have hφx : φ x = S := by
    simp only [x, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : lp.single p i (a i) = a i • lp.single (E := fun _ : ℕ => ℝ) p i 1 := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, ← hay i]
  have hxP : ‖x‖ ^ P = S := by
    rw [lp.norm_sum_single hPQ.pos]
    exact Finset.sum_congr rfl fun i _ => hna i
  have hx : ‖x‖ = S ^ (1 / P) := by
    rw [← hxP, ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hPQ.ne_zero, Real.rpow_one]
  have hb : S ≤ ‖φ‖ * S ^ (1 / P) := by
    calc S = φ x := hφx.symm
      _ ≤ ‖φ‖ * ‖x‖ := (le_abs_self _).trans (φ.le_opNorm x)
      _ = ‖φ‖ * S ^ (1 / P) := by rw [hx]
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have hsplit : S = S ^ (1 / P) * S ^ (1 / Q) := by
      have h11 : 1 / P + 1 / Q = 1 := by rw [one_div, one_div, hPQ.inv_add_inv_eq_one]
      rw [← Real.rpow_add hpos, h11, Real.rpow_one]
    have h1 : S ^ (1 / Q) ≤ ‖φ‖ := by
      have hp' : 0 < S ^ (1 / P) := Real.rpow_pos_of_pos hpos _
      nth_rewrite 1 [hsplit] at hb
      rw [mul_comm (S ^ (1 / P)) (S ^ (1 / Q))] at hb
      exact le_of_mul_le_mul_right hb hp'
    calc S = (S ^ (1 / Q)) ^ Q := by
          rw [← Real.rpow_mul hS0, one_div_mul_cancel hPQ.symm.ne_zero, Real.rpow_one]
      _ ≤ ‖φ‖ ^ Q := Real.rpow_le_rpow (by positivity) h1 hPQ.symm.nonneg

/-- For `1 < p < ∞`, every `φ ∈ ℓ_p*` is `x ↦ Σ yᵢ xᵢ` with `yᵢ = φ(eᵢ)`, `y ∈ ℓ_q` and
`‖y‖_q ≤ ‖φ‖`. -/
theorem exists_preimage_pairEllP (hp : p ≠ ∞) (hq : q ≠ ∞)
    (φ : StrongDual ℝ (lp (fun _ : ℕ => ℝ) p)) :
    ∃ y : lp (fun _ : ℕ => ℝ) q, pairEllP p q y = φ ∧ ‖y‖ ≤ ‖φ‖ := by
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hsum : Summable fun i => ‖φ (lp.single p i 1)‖ ^ q.toReal :=
    summable_of_sum_range_le (fun i => by positivity) fun N => by
      simpa [Real.norm_eq_abs] using sum_rpow_le_of_dual_ellP hp hq φ N
  let y : lp (fun _ : ℕ => ℝ) q :=
    ⟨fun i => φ (lp.single p i 1), (memℓp_gen_iff hPQ.symm.pos).2 hsum⟩
  refine ⟨y, lp.ext_continuousLinearMap hp fun i => ?_, ?_⟩
  · ext
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      lp.singleContinuousLinearMap_apply]
    rw [pairEllP_apply, lp.coeFn_single, tsum_mul_single, mul_one]
  · refine lp.norm_le_of_tsum_le hPQ.symm.pos (norm_nonneg _) ?_
    refine Real.tsum_le_of_sum_range_le (fun i => by positivity) fun N => ?_
    simpa [Real.norm_eq_abs] using sum_rpow_le_of_dual_ellP hp hq φ N

/-- `y ↦ (x ↦ Σ yᵢ xᵢ)` preserves norms from `ℓ_q` to `ℓ_p*` (`1 < p < ∞`). -/
theorem norm_pairEllP (hp : p ≠ ∞) (hq : q ≠ ∞) (y : lp (fun _ : ℕ => ℝ) q) :
    ‖pairEllP p q y‖ = ‖y‖ := by
  apply le_antisymm
  · calc ‖pairEllP p q y‖ ≤ ‖pairEllP p q‖ * ‖y‖ := (pairEllP p q).le_opNorm y
      _ ≤ 1 * ‖y‖ := by gcongr; exact norm_pairEllP_le
      _ = ‖y‖ := one_mul _
  · obtain ⟨y', hy', hn⟩ := exists_preimage_pairEllP hp hq (pairEllP p q y)
    have e : y' = y := by
      refine lp.ext (funext fun i => ?_)
      have := congrArg (fun φ => φ (lp.single p i 1)) hy'
      simp only [pairEllP_apply, lp.coeFn_single, tsum_mul_single, mul_one] at this
      exact this
    calc ‖y‖ = ‖y'‖ := by rw [e]
      _ ≤ ‖pairEllP p q y‖ := hn

/-- `ℓ_p* = ℓ_q` as normed spaces, for conjugate `1 < p, q < ∞`. -/
noncomputable def dualEllP (hp : p ≠ ∞) (hq : q ≠ ∞) :
    lp (fun _ : ℕ => ℝ) q ≃ₗᵢ[ℝ] StrongDual ℝ (lp (fun _ : ℕ => ℝ) p) :=
  LinearIsometryEquiv.ofSurjective ⟨(pairEllP p q).toLinearMap, norm_pairEllP hp hq⟩
    fun φ => (exists_preimage_pairEllP hp hq φ).imp fun _ h => h.1

/-- **Example 2** (p. 448): for `1 < p < ∞` and `1/p + 1/q = 1`, the dual of `ℓ_p` is `ℓ_q`.
Each `y ∈ ℓ_q` gives `x ↦ Σ yᵢ xᵢ` in `ℓ_p*`, every element of `ℓ_p*` arises from exactly one
`y`, and norms are preserved. (`p = 1` is `ex_15_2b`.) -/
theorem example_15_2 (hp : p ≠ ∞) (hq : q ≠ ∞) :
    ∃ e : lp (fun _ : ℕ => ℝ) q ≃ₗᵢ[ℝ] StrongDual ℝ (lp (fun _ : ℕ => ℝ) p),
      ∀ y x, e y x = ∑' i, y i * x i :=
  ⟨dualEllP hp hq, fun _ _ => rfl⟩

/-! ### `c₀`: Exercise 15.4 -/

/-- `c₀`: the sequences in `ℓ∞` that tend to `0`, as a subspace of `ℓ∞`. It inherits the sup
norm, so it is a normed space. -/
def cZero : Submodule ℝ ellInfSp where
  carrier := {x | Tendsto (fun n => x n) atTop (𝓝 0)}
  add_mem' {x y} hx hy := by simpa using hx.add hy
  zero_mem' := by simp
  smul_mem' c x hx := by simpa using hx.const_mul c

/-- Membership in `c₀`. -/
theorem mem_cZero {x : ellInfSp} : x ∈ cZero ↔ Tendsto (fun n => x n) atTop (𝓝 0) := Iff.rfl

/-- `c₀` is closed in `ℓ∞`. -/
theorem isClosed_cZero : IsClosed (cZero : Set ellInfSp) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  change Tendsto (fun n => x n) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hy : Tendsto (fun n => y n) atTop (𝓝 0)) (ε / 2)
    (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 : ‖x n - y n‖ ≤ ‖x - y‖ := by
    have := lp.norm_apply_le_norm (p := ∞) (by simp) (x - y) n
    simpa using this
  rw [dist_eq_norm] at hxy
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  rw [Real.norm_eq_abs] at h2
  calc |x n| = |(x n - y n) + y n| := by ring_nf
    _ ≤ |x n - y n| + |y n| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := add_halves ε

/-- **Exercise 15.4(a)**: `c₀` with the sup norm is a normed space (the norm of `x ∈ c₀` is its
norm in `ℓ∞`). It is also closed in `ℓ∞`, so it is complete. -/
theorem ex_15_4a : (∀ x : cZero, ‖x‖ = ‖(x : ellInfSp)‖) ∧ CompleteSpace cZero :=
  ⟨fun _ => rfl, isClosed_cZero.completeSpace_coe⟩

/-- The truncated sign vector `(sgn y₀, …, sgn y_{N−1}, 0, 0, …)`, with `sgn 0 = 1`. -/
noncomputable def signTrunc (y : ℕ → ℝ) (N : ℕ) : ellInfSp :=
  ⟨fun i => if i < N then (if 0 ≤ y i then 1 else -1) else 0, memℓp_infty_iff.2 ⟨1, by
    rintro _ ⟨i, rfl⟩
    dsimp only
    split_ifs <;> simp⟩⟩

/-- The truncated sign vector lies in `c₀`. -/
theorem signTrunc_mem (y : ℕ → ℝ) (N : ℕ) : signTrunc y N ∈ cZero := by
  rw [mem_cZero]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with i hi
  simp [signTrunc, not_lt.2 hi]

/-- The truncated sign vector has sup norm `≤ 1`. -/
theorem norm_signTrunc_le (y : ℕ → ℝ) (N : ℕ) : ‖signTrunc y N‖ ≤ 1 :=
  lp.norm_le_of_forall_le zero_le_one fun i => by
    simp only [signTrunc]
    change ‖(if i < N then (if 0 ≤ y i then (1 : ℝ) else -1) else 0)‖ ≤ 1
    split_ifs <;> simp

/-- `Σ yᵢ (signTrunc y N)ᵢ = Σ_{i<N} |yᵢ|`. -/
theorem tsum_mul_signTrunc (y : ℕ → ℝ) (N : ℕ) :
    ∑' i, y i * signTrunc y N i = ∑ i ∈ Finset.range N, |y i| := by
  rw [tsum_eq_sum (s := Finset.range N)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N := Finset.mem_range.1 hi
    change y i * (if i < N then (if 0 ≤ y i then (1 : ℝ) else -1) else 0) = _
    by_cases h : 0 ≤ y i
    · simp [hi', h, abs_of_nonneg h]
    · simp [hi', h, abs_of_neg (not_le.1 h)]
  · intro i hi
    have hi' : ¬ i < N := fun h => hi (Finset.mem_range.2 h)
    change y i * (if i < N then (if 0 ≤ y i then (1 : ℝ) else -1) else 0) = 0
    simp [hi']

/-- The map `ℓ₁ → c₀*`, `y ↦ (x ↦ Σ yᵢ xᵢ)`. -/
noncomputable def pairOneCZero : ellOneSp →ₗ[ℝ] StrongDual ℝ cZero where
  toFun y := (pairOneInf y).comp cZero.subtypeL
  map_add' y z := by ext; simp
  map_smul' c y := by ext; simp

/-- `pairOneCZero y x = Σ yᵢ xᵢ`. -/
theorem pairOneCZero_apply (y : ellOneSp) (x : cZero) :
    pairOneCZero y x = ∑' i, y i * (x : ellInfSp) i := rfl

/-- `y ↦ (x ↦ Σ yᵢ xᵢ)` preserves norms from `ℓ₁` to `c₀*`. The lower bound uses the
truncated sign vectors, as in the manual. -/
theorem norm_pairOneCZero (y : ellOneSp) : ‖pairOneCZero y‖ = ‖y‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [pairOneCZero_apply, ← pairOneInf_apply]
    calc ‖pairOneInf y (x : ellInfSp)‖ ≤ ‖pairOneInf y‖ * ‖(x : ellInfSp)‖ :=
          (pairOneInf y).le_opNorm _
      _ ≤ (1 * ‖y‖) * ‖x‖ := by
          gcongr
          · exact (pairOneInf.le_opNorm y).trans (by gcongr; exact norm_pairOneInf_le)
          · exact le_rfl
      _ = ‖y‖ * ‖x‖ := by rw [one_mul]
  · rw [norm_ellOneSp_eq_tsum]
    refine (summable_abs_ellOneSp y).tsum_le_of_sum_range_le fun N => ?_
    have h := (pairOneCZero y).le_opNorm ⟨signTrunc y N, signTrunc_mem y N⟩
    rw [pairOneCZero_apply] at h
    change ‖∑' i, y i * signTrunc y N i‖ ≤ _ at h
    rw [tsum_mul_signTrunc] at h
    have h2 : ‖(⟨signTrunc y N, signTrunc_mem y N⟩ : cZero)‖ ≤ 1 := norm_signTrunc_le y N
    calc ∑ i ∈ Finset.range N, |y i| ≤ ‖∑ i ∈ Finset.range N, |y i|‖ := le_abs_self _
      _ ≤ ‖pairOneCZero y‖ * ‖(⟨signTrunc y N, signTrunc_mem y N⟩ : cZero)‖ := h
      _ ≤ ‖pairOneCZero y‖ * 1 := by gcongr
      _ = ‖pairOneCZero y‖ := mul_one _

/-- The unit sequence `eᵢ` as an element of `c₀`. -/
noncomputable def unitCZero (i : ℕ) : cZero :=
  ⟨lp.single ∞ i 1, by
    rw [mem_cZero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop i] with j hj
    simp [lp.single_apply, hj.ne']⟩

/-- In `c₀` (unlike `ℓ∞`), `x = lim_N Σ_{i<N} xᵢ eᵢ` in the sup norm. -/
theorem tendsto_trunc_cZero (x : cZero) :
    Tendsto (fun N => ∑ i ∈ Finset.range N, (x : ellInfSp) i • unitCZero i) atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hx := mem_cZero.1 x.2
  rw [Metric.tendsto_atTop] at hx ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := hx (ε / 2) (half_pos hε)
  refine ⟨N0, fun N hN => ?_⟩
  have key : ‖∑ i ∈ Finset.range N, (x : ellInfSp) i • unitCZero i - x‖ ≤ ε / 2 := by
    change ‖((∑ i ∈ Finset.range N, (x : ellInfSp) i • unitCZero i - x : cZero) :
      ellInfSp)‖ ≤ ε / 2
    rw [Submodule.coe_sub, Submodule.coe_sum]
    refine lp.norm_le_of_forall_le (half_pos hε).le fun j => ?_
    rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply]
    simp only [Submodule.coe_smul, unitCZero, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_range]
    by_cases hj : j < N
    · simp [hj, (half_pos hε).le]
    · have := hN0 j (hN.trans (not_lt.1 hj))
      rw [Real.dist_eq, sub_zero] at this
      simpa [hj] using this.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact key.trans_lt (half_lt_self hε)

/-- Every `φ ∈ c₀*` is `x ↦ Σ yᵢ xᵢ` with `yᵢ = φ(eᵢ)` and `y ∈ ℓ₁`. -/
theorem pairOneCZero_surjective : Function.Surjective pairOneCZero := by
  intro φ
  obtain ⟨yf, hyf⟩ : ∃ yf : ℕ → ℝ, ∀ i, φ (unitCZero i) = yf i := ⟨_, fun _ => rfl⟩
  have hpart : ∀ N, ∑ i ∈ Finset.range N, |yf i| ≤ ‖φ‖ := fun N => by
    have hz : (⟨signTrunc yf N, signTrunc_mem yf N⟩ : cZero) =
        ∑ i ∈ Finset.range N, (if 0 ≤ yf i then (1 : ℝ) else -1) • unitCZero i := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      ext j
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp only [Submodule.coe_smul, unitCZero, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_range]
      rfl
    have h := φ.le_opNorm ⟨signTrunc yf N, signTrunc_mem yf N⟩
    rw [hz, map_sum] at h
    simp only [map_smul, smul_eq_mul, hyf] at h
    have e : ∀ i, (if 0 ≤ yf i then (1 : ℝ) else -1) * yf i = |yf i| := fun i => by
      split_ifs with hi
      · rw [one_mul, abs_of_nonneg hi]
      · rw [neg_one_mul, abs_of_neg (not_le.1 hi)]
    simp only [e] at h
    rw [← hz] at h
    calc ∑ i ∈ Finset.range N, |yf i| ≤ ‖∑ i ∈ Finset.range N, |yf i|‖ := le_abs_self _
      _ ≤ ‖φ‖ * ‖(⟨signTrunc yf N, signTrunc_mem yf N⟩ : cZero)‖ := h
      _ ≤ ‖φ‖ * 1 := by gcongr; exact norm_signTrunc_le yf N
      _ = ‖φ‖ := mul_one _
  have hsum : Summable fun i => |yf i| :=
    summable_of_sum_range_le (fun i => abs_nonneg _) hpart
  let y : ellOneSp := ⟨yf, by
    refine memℓp_gen_iff (p := 1) (by simp) |>.2 ?_
    simpa using hsum⟩
  refine ⟨y, ContinuousLinearMap.ext fun x => ?_⟩
  have h1 := ((pairOneCZero y).continuous.tendsto x).comp (tendsto_trunc_cZero x)
  have h2 := (φ.continuous.tendsto x).comp (tendsto_trunc_cZero x)
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  simp only [Function.comp_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pairOneCZero_apply, hyf i]
  congr 1
  change _ = ∑' j, yf j * (Pi.single i (1 : ℝ) : ℕ → ℝ) j
  rw [tsum_mul_single, mul_one]

/-- `c₀* = ℓ₁` as normed spaces. -/
noncomputable def dualCZero : ellOneSp ≃ₗᵢ[ℝ] StrongDual ℝ cZero :=
  LinearIsometryEquiv.ofSurjective ⟨pairOneCZero, norm_pairOneCZero⟩ pairOneCZero_surjective

/-- **Exercise 15.4(b)**: the dual of `c₀` is `ℓ₁`. Each `y ∈ ℓ₁` gives `x ↦ Σ yᵢ xᵢ` in `c₀*`,
every element of `c₀*` arises from exactly one `y`, and norms are preserved. -/
theorem ex_15_4b :
    ∃ e : ellOneSp ≃ₗᵢ[ℝ] StrongDual ℝ cZero, ∀ y x, e y x = ∑' i, y i * (x : ellInfSp) i :=
  ⟨dualCZero, fun _ _ => rfl⟩

/-! ### `L_p` spaces: Exercise 15.5 and `L₁* = L∞` -/

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-- The pairing `(f, x) ↦ ∫ f x dμ` of `L₁` with `L∞` (Mathlib's `lpPairing`). -/
noncomputable def pairL1Linf (μ : Measure Z) : Lp ℝ 1 μ →L[ℝ] Lp ℝ ∞ μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 1 ∞

/-- The pairing `(y, x) ↦ ∫ y x dμ` of `L∞` with `L₁`. -/
noncomputable def pairLinfL1 (μ : Measure Z) : Lp ℝ ∞ μ →L[ℝ] Lp ℝ 1 μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1

/-- `pairL1Linf μ f x = ∫ f x dμ`. -/
theorem pairL1Linf_apply (f : Lp ℝ 1 μ) (x : Lp ℝ ∞ μ) :
    pairL1Linf μ f x = ∫ z, f z * x z ∂μ := by
  rw [pairL1Linf, ContinuousLinearMap.lpPairing_eq_integral]; rfl

/-- `pairLinfL1 μ y x = ∫ y x dμ`. -/
theorem pairLinfL1_apply (y : Lp ℝ ∞ μ) (x : Lp ℝ 1 μ) :
    pairLinfL1 μ y x = ∫ z, y z * x z ∂μ := by
  rw [pairLinfL1, ContinuousLinearMap.lpPairing_eq_integral]; rfl

/-- Hölder's inequality: `|∫ f x dμ| ≤ ‖f‖₁ ‖x‖∞`. -/
theorem abs_pairL1Linf_le (f : Lp ℝ 1 μ) (x : Lp ℝ ∞ μ) :
    |pairL1Linf μ f x| ≤ ‖f‖ * ‖x‖ := by
  have h1 : pairL1Linf μ f x = L1.integral ((ContinuousLinearMap.mul ℝ ℝ).holder 1 f x) := by
    rw [pairL1Linf_apply, L1.integral_eq_integral]
    exact integral_congr_ae ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder f x).symm
  rw [h1, ← Real.norm_eq_abs]
  refine (L1.norm_integral_le _).trans ?_
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le f x).trans ?_
  have := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖f‖ * ‖x‖ ≤ 1 * ‖f‖ * ‖x‖ := by gcongr
    _ = ‖f‖ * ‖x‖ := by rw [one_mul]

/-- Hölder's inequality: `|∫ y x dμ| ≤ ‖y‖∞ ‖x‖₁`. -/
theorem abs_pairLinfL1_le (y : Lp ℝ ∞ μ) (x : Lp ℝ 1 μ) :
    |pairLinfL1 μ y x| ≤ ‖y‖ * ‖x‖ := by
  have h1 : pairLinfL1 μ y x = L1.integral ((ContinuousLinearMap.mul ℝ ℝ).holder 1 y x) := by
    rw [pairLinfL1_apply, L1.integral_eq_integral]
    exact integral_congr_ae ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder y x).symm
  rw [h1, ← Real.norm_eq_abs]
  refine (L1.norm_integral_le _).trans ?_
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le y x).trans ?_
  have := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖y‖ * ‖x‖ ≤ 1 * ‖y‖ * ‖x‖ := by gcongr
    _ = ‖y‖ * ‖x‖ := by rw [one_mul]

/-- **Exercise 15.5(a)**: each `f ∈ L₁(Z, 𝒵, μ)` defines a continuous linear functional
`φ(x) = ∫ f x dμ` on `L∞(Z, 𝒵, μ)`, of norm at most `‖f‖₁`. -/
theorem ex_15_5a (f : Lp ℝ 1 μ) :
    ∃ φ : StrongDual ℝ (Lp ℝ ∞ μ), (∀ x, φ x = ∫ z, f z * x z ∂μ) ∧ ‖φ‖ ≤ ‖f‖ :=
  ⟨pairL1Linf μ f, pairL1Linf_apply f, ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    fun x => by rw [Real.norm_eq_abs]; exact abs_pairL1Linf_le f x⟩

/-- **Exercise 15.5(b)**: the functional of part (a) is `x ↦ ∫ x dν` for the signed measure
`ν(A) = ∫_A f dμ`, which is absolutely continuous with respect to `μ`. The integral is Mathlib's
integral against a signed measure. The proof writes `ν = ν⁺ − ν⁻` with `ν^± = f^± μ`; this
representation step is the one the manual leaves out. -/
theorem ex_15_5b (f : Lp ℝ 1 μ) :
    ∃ ν : SignedMeasure Z, ν ≪ᵥ μ.toENNRealVectorMeasure ∧
      ∀ x : Lp ℝ ∞ μ, pairL1Linf μ f x = ∫ᵛ z, x z ∂<•ν := by
  have hfi : Integrable f μ := L1.integrable_coeFn f
  have hfm : Measurable fun z => f z := (Lp.stronglyMeasurable f).measurable
  have hfm' : Measurable fun z => -f z := hfm.neg
  set νp := μ.withDensity fun z => ENNReal.ofReal (f z)
  set νn := μ.withDensity fun z => ENNReal.ofReal (-f z)
  have : IsFiniteMeasure νp := isFiniteMeasure_withDensity_ofReal hfi.2
  have : IsFiniteMeasure νn := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  refine ⟨μ.withDensityᵥ f, Measure.withDensityᵥ_absolutelyContinuous μ f, fun x => ?_⟩
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hfi]
  have hlt : ∀ g : Z → ℝ, ∀ᵐ z ∂μ, ENNReal.ofReal (g z) < ∞ := fun g =>
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hx : MemLp (fun z => x z) ∞ μ := Lp.memLp x
  have ip : Integrable (fun z => max (f z) 0 * x z) μ := (hfi.pos_part).mul_of_top_left hx
  have ineg : Integrable (fun z => max (-f z) 0 * x z) μ := (hfi.neg.pos_part).mul_of_top_left hx
  have hp : νp.toSignedMeasure.Integrable fun z => x z := by
    simp only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    rw [integrable_withDensity_iff_integrable_smul' hfm.ennreal_ofReal (hlt _)]
    simpa [ENNReal.toReal_ofReal'] using ip
  have hn : νn.toSignedMeasure.Integrable fun z => x z := by
    simp only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    rw [integrable_withDensity_iff_integrable_smul' hfm'.ennreal_ofReal (hlt _)]
    simpa [ENNReal.toReal_ofReal'] using ineg
  rw [VectorMeasure.integral_sub_vectorMeasure hp hn, VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure,
    integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal (hlt _),
    integral_withDensity_eq_integral_toReal_smul hfm'.ennreal_ofReal (hlt _),
    pairL1Linf_apply]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [← integral_sub ip ineg]
  congr 1
  ext z
  rw [← sub_mul, max_zero_sub_eq_self]

/-- `1_A c = c · 1_A` in `L₁`. -/
theorem indicatorConstLp_one_eq_smul {s : Set Z} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) :
    indicatorConstLp 1 hs hμs c = c • indicatorConstLp 1 hs hμs (1 : ℝ) := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := c),
    Lp.coeFn_smul c (indicatorConstLp 1 hs hμs (1 : ℝ)),
    indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  by_cases hz : z ∈ s <;> simp [hz]

/-- `∫ y (c 1_A) dμ = (∫_A y dμ) c`. -/
theorem pairLinfL1_indicator (y : Lp ℝ ∞ μ) {s : Set Z} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (c : ℝ) : pairLinfL1 μ y (indicatorConstLp 1 hs hμs c) = (∫ z in s, y z ∂μ) * c := by
  rw [pairLinfL1_apply, ← integral_mul_const, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := c)] with z hz
  rw [hz]
  by_cases h : z ∈ s <;> simp [h]

/-- For a σ-finite measure, `y ↦ (x ↦ ∫ y x dμ)` is injective from `L∞` to `L₁*`. -/
theorem pairLinfL1_injective [SigmaFinite μ] : Function.Injective (pairLinfL1 μ) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  have hint : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (fun z => y z) s μ :=
    fun s hs hμs => by
      have : Fact (μ s < ∞) := ⟨hμs⟩
      have hm : MemLp (fun z => y z) ∞ (μ.restrict s) := (Lp.memLp y).restrict s
      exact hm.integrable le_top
  have h0 := ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hint fun s hs hμs => by
    have := pairLinfL1_indicator y hs hμs.ne 1
    rw [hy, mul_one] at this
    exact this.symm
  exact (Lp.eq_zero_iff_ae_eq_zero).2 h0

/-- For a σ-finite measure, every `φ ∈ L₁*` is `x ↦ ∫ y x dμ` for some `y ∈ L∞` with
`‖y‖∞ ≤ ‖φ‖`. Proof: take a weight `w > 0` with `∫ w dμ < ∞` and `r = √w ∈ L₂`. Then
`J x = r x` maps `L₂` into `L₁`, and Riesz representation of `φ ∘ J` gives `g ∈ L₂`. For every
measurable `s`, `|∫_s g r| ≤ ‖φ‖ ∫_s w`, so `h = g / r` has `|h| ≤ ‖φ‖` a.e. For `μ s < ∞`,
`φ(1_s) = ∫_s h`: this holds on `s ∩ {w > 1/(n+1)}` (where `1_s / r ∈ L₂`) and passes to the
limit. Indicators are dense in `L₁`. -/
theorem exists_preimage_pairLinfL1 [SigmaFinite μ] (φ : StrongDual ℝ (Lp ℝ 1 μ)) :
    ∃ y : Lp ℝ ∞ μ, pairLinfL1 μ y = φ ∧ ‖y‖ ≤ ‖φ‖ := by
  obtain ⟨w0, hw0pos, hw0m, hw0int⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  set w : Z → ℝ := fun z => (w0 z : ℝ) with hwdef
  have hwpos : ∀ z, 0 < w z := fun z => NNReal.coe_pos.2 (hw0pos z)
  have hwm : Measurable w := hw0m.coe_nnreal_real
  have hwi : Integrable w μ := by
    refine ⟨hwm.aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral, hwdef, Real.enorm_of_nonneg (NNReal.coe_nonneg _),
      ENNReal.ofReal_coe_nnreal]
    exact hw0int.trans ENNReal.one_lt_top
  -- the square root of the weight, an element of `L₂`
  set r : Z → ℝ := fun z => Real.sqrt (w z) with hrdef
  have hrpos : ∀ z, 0 < r z := fun z => Real.sqrt_pos.2 (hwpos z)
  have hrm : Measurable r := hwm.sqrt
  have hrr : ∀ z, r z * r z = w z := fun z => Real.mul_self_sqrt (hwpos z).le
  have hr2 : MemLp r 2 μ := by
    refine (memLp_two_iff_integrable_sq hrm.aestronglyMeasurable).2 ?_
    refine hwi.congr (Eventually.of_forall fun z => ?_)
    change w z = r z ^ 2
    rw [sq, hrr]
  set J := (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (hr2.toLp r) with hJdef
  have hJ : ∀ (u v : Z → ℝ) (hu : MemLp u 2 μ) (hv : MemLp v 1 μ),
      (∀ z, r z * u z = v z) → J (hu.toLp u) = hv.toLp v := fun u v hu hv huv => by
    refine Lp.ext ?_
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) (hr2.toLp r)
      (hu.toLp u), hr2.coeFn_toLp, hu.coeFn_toLp, hv.coeFn_toLp] with z h1 h2 h3 h4
    change (ContinuousLinearMap.mul ℝ ℝ).holder 1 _ _ z = _
    rw [h1, ContinuousLinearMap.mul_apply', h2, h3, h4, huv]
  set g := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm (φ.comp J) with hg
  have key : ∀ (u : Z → ℝ) (hu : MemLp u 2 μ), φ (J (hu.toLp u)) = ∫ z, g z * u z ∂μ := by
    intro u hu
    have : φ (J (hu.toLp u)) = InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) g (hu.toLp u) := by
      rw [hg, LinearIsometryEquiv.apply_symm_apply]; rfl
    rw [this, InnerProductSpace.toDual_apply_apply, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp] with z hz
    rw [hz]; simp [mul_comm]
  -- `|∫_s g r| ≤ ‖φ‖ ∫_s w` for every measurable `s`
  have hgr : Integrable (fun z => g z * r z) μ := (Lp.memLp g).integrable_mul hr2
  have hwc : Integrable (fun z => ‖φ‖ * w z) μ := hwi.const_mul _
  have hset : ∀ s, MeasurableSet s → |∫ z in s, g z * r z ∂μ| ≤ ∫ z in s, ‖φ‖ * w z ∂μ := by
    intro s hs
    have hu : MemLp (s.indicator r) 2 μ := hr2.indicator hs
    have hv : MemLp (s.indicator w) 1 μ := (memLp_one_iff_integrable.2 hwi).indicator hs
    have huv : ∀ z, r z * s.indicator r z = s.indicator w z := fun z => by
      by_cases hz : z ∈ s <;> simp [hz, hrr]
    have e1 : φ (hv.toLp _) = ∫ z in s, g z * r z ∂μ := by
      rw [← hJ _ _ hu hv huv, key, ← integral_indicator hs]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ s <;> simp [hz]
    have e2 : ‖hv.toLp (s.indicator w)‖ = ∫ z in s, w z ∂μ := by
      rw [L1.norm_eq_integral_norm, ← integral_indicator hs]
      refine integral_congr_ae ?_
      filter_upwards [hv.coeFn_toLp] with z hz
      rw [hz]
      by_cases hzs : z ∈ s <;> simp [hzs, abs_of_pos (hwpos z)]
    rw [← e1, integral_const_mul, ← e2, ← Real.norm_eq_abs]
    exact φ.le_opNorm _
  have hle : (fun z => g z * r z) ≤ᵐ[μ] fun z => ‖φ‖ * w z :=
    ae_le_of_forall_setIntegral_le hgr hwc fun s hs _ => (le_abs_self _).trans (hset s hs)
  have hge : (fun z => -(‖φ‖ * w z)) ≤ᵐ[μ] fun z => g z * r z :=
    ae_le_of_forall_setIntegral_le hwc.neg hgr fun s hs _ => by
      rw [integral_neg]; linarith [neg_abs_le (∫ z in s, g z * r z ∂μ), hset s hs]
  set h : Z → ℝ := fun z => g z / r z with hhdef
  have hb : ∀ᵐ z ∂μ, ‖h z‖ ≤ ‖φ‖ := by
    filter_upwards [hle, hge] with z h1 h2
    have hr := hrpos z
    rw [Real.norm_eq_abs, hhdef, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    have h4 : |g z * r z| ≤ ‖φ‖ * w z := abs_le.2 ⟨h2, h1⟩
    rw [abs_mul, abs_of_pos hr, ← hrr, ← mul_assoc] at h4
    exact le_of_mul_le_mul_right h4 hr
  have hhm : AEStronglyMeasurable h μ :=
    ((Lp.aestronglyMeasurable g).aemeasurable.div hrm.aemeasurable).aestronglyMeasurable
  have hm : MemLp h ∞ μ := memLp_top_of_bound hhm ‖φ‖ hb
  -- `φ(1_s) = ∫_s h` for `μ s < ∞`, by exhausting `s` with `tₙ = s ∩ {w > 1/(n+1)}`
  have hind : ∀ s (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      φ (indicatorConstLp 1 hs hμs (1 : ℝ)) = ∫ z in s, h z ∂μ := by
    intro s hs hμs
    set t : ℕ → Set Z := fun n => s ∩ {z | 1 / ((n : ℝ) + 1) < w z} with htdef
    have ht : ∀ n, MeasurableSet (t n) := fun n =>
      hs.inter (measurableSet_lt measurable_const hwm)
    have hμt : ∀ n, μ (t n) ≠ ∞ := fun n =>
      ne_top_of_le_ne_top hμs (measure_mono inter_subset_left)
    have hmono : Monotone t := fun m n hmn z hz => by
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have h2 : 1 / ((m : ℝ) + 1) < w z := hz.2
      exact ⟨hz.1, lt_of_le_of_lt (by gcongr) h2⟩
    have hunion : (⋃ n, t n) = s := by
      refine Subset.antisymm (iUnion_subset fun n => inter_subset_left) fun z hz => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hwpos z)
      exact mem_iUnion.2 ⟨n, hz, hn⟩
    have hval : ∀ n, φ (indicatorConstLp 1 (ht n) (hμt n) (1 : ℝ)) = ∫ z in t n, h z ∂μ := by
      intro n
      have hcm : MemLp ((t n).indicator fun _ => Real.sqrt ((n : ℝ) + 1)) 2 μ :=
        memLp_indicator_const 2 (ht n) _ (Or.inr (hμt n))
      have hu : MemLp ((t n).indicator fun z => 1 / r z) 2 μ := by
        refine hcm.of_le (((hrm.const_div 1).indicator (ht n)).aestronglyMeasurable)
          (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ t n
        · have hr := hrpos z
          simp only [indicator_of_mem hz, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 hr),
            abs_of_nonneg (Real.sqrt_nonneg _)]
          rw [div_le_iff₀ hr]
          have h1 : 1 ≤ ((n : ℝ) + 1) * w z := by
            have h2 : 1 / ((n : ℝ) + 1) < w z := hz.2
            rw [div_lt_iff₀ (by positivity)] at h2
            linarith
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ Real.sqrt (((n : ℝ) + 1) * w z) := Real.sqrt_le_sqrt h1
            _ = Real.sqrt ((n : ℝ) + 1) * r z := Real.sqrt_mul (by positivity) _
        · simp [indicator_of_notMem hz]
      have huv : ∀ z, r z * (t n).indicator (fun z => 1 / r z) z = (t n).indicator (fun _ => 1) z :=
        fun z => by
          by_cases hz : z ∈ t n
          · simp [hz, (hrpos z).ne']
          · simp [hz]
      have := hJ _ _ hu (memLp_indicator_const 1 (ht n) (1 : ℝ) (Or.inr (hμt n))) huv
      change φ (MemLp.toLp _ (memLp_indicator_const 1 (ht n) (1 : ℝ) (Or.inr (hμt n)))) = _
      rw [← this, key, ← integral_indicator (ht n)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ t n
      · simp [hz, hhdef, div_eq_mul_inv]
      · simp [hz]
    have hsd : Tendsto (fun n => μ (t n ∆ s)) atTop (𝓝 0) := by
      have e : ∀ n, t n ∆ s = s \ t n := fun n => symmDiff_of_le inter_subset_left
      simp only [e]
      have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := fun n => s \ t n)
        (fun n => (hs.diff (ht n)).nullMeasurableSet)
        (fun m n hmn z hz => ⟨hz.1, fun h' => hz.2 (hmono hmn h')⟩)
        ⟨0, ne_top_of_le_ne_top hμs (measure_mono sdiff_subset)⟩
      have hempty : (⋂ n, s \ t n) = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
        have hzs : z ∈ s := (mem_iInter.1 hz 0).1
        rw [← hunion] at hzs
        obtain ⟨n, hn⟩ := mem_iUnion.1 hzs
        exact (mem_iInter.1 hz n).2 hn
      rw [hempty, measure_empty] at hlim
      exact hlim
    have h1 := (φ.continuous.tendsto _).comp
      (tendsto_indicatorConstLp_set (hs := hs) (hμs := hμs) (c := (1 : ℝ)) (ht := ht)
        (hμt := hμt) ENNReal.one_ne_top hsd)
    have hio : IntegrableOn h (⋃ n, t n) μ := by
      rw [hunion]
      have : Fact (μ s < ∞) := ⟨hμs.lt_top⟩
      exact (hm.restrict s).integrable le_top
    have h2 := tendsto_setIntegral_of_monotone ht hmono hio
    rw [hunion] at h2
    exact tendsto_nhds_unique h1 (h2.congr fun n => (hval n).symm)
  refine ⟨hm.toLp h, ?_, ?_⟩
  · refine (Lp.induction (p := 1) ENNReal.one_ne_top
      (fun x => pairLinfL1 μ (hm.toLp h) x = φ x) ?_ ?_
      (isClosed_eq (pairLinfL1 μ (hm.toLp h)).continuous φ.continuous) ·) |>
      ContinuousLinearMap.ext
    · intro c s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst, pairLinfL1_indicator, indicatorConstLp_one_eq_smul,
        map_smul, smul_eq_mul, hind s hs hμs.ne, mul_comm]
      congr 1
      exact setIntegral_congr_ae hs (by
        filter_upwards [hm.coeFn_toLp] with z hz _ using hz)
    · intro f f' hf hf' _ h1 h2
      simp only [map_add, h1, h2]
  · rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
    refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg φ) (eLpNormEssSup_le_of_ae_bound ?_)
    filter_upwards [hm.coeFn_toLp, hb] with z h1 h2
    rw [h1]; exact h2

/-- For a σ-finite measure, `y ↦ (x ↦ ∫ y x dμ)` preserves norms from `L∞` to `L₁*`. -/
theorem norm_pairLinfL1 [SigmaFinite μ] (y : Lp ℝ ∞ μ) : ‖pairLinfL1 μ y‖ = ‖y‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
      rw [Real.norm_eq_abs]; exact abs_pairLinfL1_le y x
  · obtain ⟨y', hy', hn⟩ := exists_preimage_pairLinfL1 (pairLinfL1 μ y)
    calc ‖y‖ = ‖y'‖ := by rw [pairLinfL1_injective hy']
      _ ≤ ‖pairLinfL1 μ y‖ := hn

/-- `L₁* = L∞` for a σ-finite measure. -/
noncomputable def dualL1 (μ : Measure Z) [SigmaFinite μ] :
    Lp ℝ ∞ μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ 1 μ) :=
  LinearIsometryEquiv.ofSurjective ⟨(pairLinfL1 μ).toLinearMap, norm_pairLinfL1⟩
    fun φ => (exists_preimage_pairLinfL1 φ).imp fun _ h => h.1

/-- **Corrected `L₁* = L∞`** (p. 449): for a σ-finite measure, every `y ∈ L∞` gives
`x ↦ ∫ y x dμ` in `L₁*`, every element of `L₁*` arises from exactly one `y`, and norms are
preserved. -/
theorem l1_dual_sigmaFinite [SigmaFinite μ] :
    ∃ e : Lp ℝ ∞ μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ 1 μ), ∀ y x, e y x = ∫ z, y z * x z ∂μ :=
  ⟨dualL1 μ, fun y x => pairLinfL1_apply y x⟩

/-- One point of infinite mass: the measure `∞ · δ` on `Unit`. It is not σ-finite. -/
noncomputable def infAtom : Measure Unit := (∞ : ℝ≥0∞) • Measure.dirac ()

/-- For `infAtom`, `L₁ = {0}`: an integrable function must vanish at the atom. -/
theorem subsingleton_L1_infAtom : Subsingleton (Lp ℝ 1 infAtom) := by
  refine ⟨fun f g => ?_⟩
  have h0 : ∀ h : Lp ℝ 1 infAtom, h = 0 := fun h => by
    have hi : Integrable h infAtom := L1.integrable_coeFn h
    have hlt := hi.2
    change ∫⁻ a, ‖h a‖ₑ ∂((∞ : ℝ≥0∞) • Measure.dirac ()) < ∞ at hlt
    rw [lintegral_smul_measure, lintegral_dirac] at hlt
    have hz : ‖h ()‖ₑ = 0 := by
      by_contra hne
      exact (ENNReal.mul_lt_top_iff.1 hlt).elim (fun h' => absurd h'.1 (lt_irrefl _))
        (fun h' => h'.elim (fun h'' => absurd h'' (by simp)) hne)
    rw [Lp.eq_zero_iff_ae_eq_zero]
    refine Eventually.of_forall fun u => ?_
    cases u
    simpa using hz
  rw [h0 f, h0 g]

/-- For `infAtom`, `L∞ ≠ {0}`: the constant `1` is not `0`. -/
theorem nontrivial_Linf_infAtom : Nontrivial (Lp ℝ ∞ infAtom) := by
  refine ⟨⟨(memLp_top_const (μ := infAtom) (1 : ℝ)).toLp _, 0, fun h => ?_⟩⟩
  have := (MemLp.toLp_eq_toLp_iff _ (memLp_top_const (μ := infAtom) (0 : ℝ))).1
    (h.trans (MemLp.toLp_zero _).symm)
  rw [EventuallyEq, ae_iff] at this
  simp [infAtom] at this

/-- **Correction (p. 449)**: without σ-finiteness the dual of `L₁` is not `L∞`. For `infAtom`
there is no linear isomorphism `L∞ ≃ L₁*` at all. -/
theorem l1_dual_counterexample :
    IsEmpty (Lp ℝ ∞ infAtom ≃ₗ[ℝ] StrongDual ℝ (Lp ℝ 1 infAtom)) := by
  refine ⟨fun e => ?_⟩
  have h1 := subsingleton_L1_infAtom
  have hd : Subsingleton (StrongDual ℝ (Lp ℝ 1 infAtom)) :=
    ⟨fun φ ψ => ContinuousLinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  have h2 := nontrivial_Linf_infAtom
  obtain ⟨a, b, hab⟩ := h2.exists_pair_ne
  exact hab (e.injective (Subsingleton.elim _ _))

/-- **Correction (p. 449)**: for `infAtom` the map `y ↦ (x ↦ ∫ y x dμ)` from `L∞` to `L₁*` is
not injective. -/
theorem l1_dual_pairing_counterexample : ¬ Function.Injective (pairLinfL1 infAtom) := by
  intro hinj
  have h1 := subsingleton_L1_infAtom
  obtain ⟨a, b, hab⟩ := nontrivial_Linf_infAtom.exists_pair_ne
  refine hab (hinj (ContinuousLinearMap.ext fun x => ?_))
  rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- **Correction (p. 450)**: no measure has `μ(A) > 0` for every measurable `A`, since
`μ(∅) = 0`. -/
theorem positive_measure_counterexample (μ : Measure Z) : ¬ ∀ A : Set Z, 0 < μ A :=
  fun h => by simpa using h ∅

/-! ### The example on p. 450: `L∞(ℕ, μ) = ℓ∞` -/

variable {ν : Measure ℕ}

/-- If every point has positive mass, an a.e. property holds everywhere. -/
theorem of_ae_of_atoms_pos (hν : ∀ n, ν {n} ≠ 0) {P : ℕ → Prop} (h : ∀ᵐ n ∂ν, P n) (m : ℕ) :
    P m := by
  by_contra hm
  rw [ae_iff] at h
  exact hν m (measure_mono_null (fun n hn => by rw [mem_singleton_iff.1 hn]; exact hm) h)

/-- An element of `L∞` is bounded a.e. by its norm. -/
theorem ae_norm_le_norm_Linf (f : Lp ℝ ∞ ν) : ∀ᵐ n ∂ν, ‖f n‖ ≤ ‖f‖ := by
  have h := ae_le_eLpNormEssSup (f := fun n => f n) (μ := ν)
  have hfin : eLpNormEssSup (fun n => f n) ν ≠ ∞ := by
    have := Lp.eLpNorm_ne_top f
    rwa [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] at this
  filter_upwards [h] with n hn
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  rw [← ofReal_norm] at hn
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hn

/-- A bounded sequence is an element of `L∞(ℕ, ν)`. -/
theorem memLp_ellInfSp (x : ellInfSp) : MemLp (fun n => x n) ∞ ν :=
  memLp_top_of_bound Measurable.of_discrete.aestronglyMeasurable ‖x‖
    (Eventually.of_forall fun n => lp.norm_apply_le_norm (by simp) x n)

/-- The map `ℓ∞ → L∞(ℕ, ν)` sending a bounded sequence to its class. -/
noncomputable def ellInfToLinf (ν : Measure ℕ) : ellInfSp →ₗ[ℝ] Lp ℝ ∞ ν where
  toFun x := (memLp_ellInfSp x).toLp _
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' _ _ := MemLp.toLp_const_smul _ _

/-- The class of `x` is represented by `x`. -/
theorem coeFn_ellInfToLinf (x : ellInfSp) : ellInfToLinf ν x =ᵐ[ν] fun n => x n :=
  (memLp_ellInfSp x).coeFn_toLp

/-- If every point has positive mass, `ℓ∞ → L∞(ℕ, ν)` preserves norms. -/
theorem norm_ellInfToLinf [IsFiniteMeasure ν] (hν : ∀ n, ν {n} ≠ 0) (x : ellInfSp) :
    ‖ellInfToLinf ν x‖ = ‖x‖ := by
  apply le_antisymm
  · have := Lp.norm_le_of_ae_bound (p := ∞) (f := ellInfToLinf ν x) (norm_nonneg x) (by
      filter_upwards [coeFn_ellInfToLinf (ν := ν) x] with n h
      rw [h]; exact lp.norm_apply_le_norm (by simp) x n)
    simpa using this
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun n => ?_
    obtain ⟨h3, h4⟩ := of_ae_of_atoms_pos hν
      ((ae_norm_le_norm_Linf (ellInfToLinf ν x)).and (coeFn_ellInfToLinf (ν := ν) x)) n
    rw [h4] at h3
    exact h3

/-- If every point has positive mass, every class in `L∞(ℕ, ν)` comes from a bounded
sequence. -/
theorem ellInfToLinf_surjective (hν : ∀ n, ν {n} ≠ 0) :
    Function.Surjective (ellInfToLinf ν) := by
  intro f
  let x : ellInfSp := ⟨fun n => f n, memℓp_infty_iff.2 ⟨‖f‖, by
    rintro _ ⟨n, rfl⟩
    exact of_ae_of_atoms_pos hν (ae_norm_le_norm_Linf f) n⟩⟩
  refine ⟨x, Lp.ext ?_⟩
  filter_upwards [coeFn_ellInfToLinf (ν := ν) x] with n hn
  exact hn

/-- **Example (p. 450)**, with the typo corrected: if `ν` is a finite measure on `ℕ` (all
subsets measurable) with `ν {n} > 0` for every `n`, then `L∞(ℕ, ν)` is `ℓ∞`. The isometric
isomorphism sends a bounded sequence to its class. -/
theorem example_15_4_linf_nat [IsFiniteMeasure ν] (hν : ∀ n, ν {n} ≠ 0) :
    ∃ e : ellInfSp ≃ₗᵢ[ℝ] Lp ℝ ∞ ν, ∀ x, e x =ᵐ[ν] fun n => x n :=
  ⟨LinearIsometryEquiv.ofSurjective ⟨ellInfToLinf ν, norm_ellInfToLinf hν⟩
    (ellInfToLinf_surjective hν), fun x => coeFn_ellInfToLinf x⟩

/-! ### Theorem 15.2: the geometric Hahn–Banach theorem -/

/-- If `φ(b) ≤ φ(a)` for all `a ∈ A`, `b ∈ B` (both nonempty), a constant `c` fits between:
`φ(b) ≤ c ≤ φ(a)`. -/
theorem exists_const_between_of_le {A B : Set S} (hA : A.Nonempty) (hB : B.Nonempty)
    (φ : StrongDual ℝ S) (h : ∀ x ∈ A, ∀ y ∈ B, φ y ≤ φ x) :
    ∃ c : ℝ, (∀ x ∈ A, c ≤ φ x) ∧ ∀ y ∈ B, φ y ≤ c := by
  obtain ⟨a, ha⟩ := hA
  have hbdd : BddAbove (φ '' B) := ⟨φ a, by rintro _ ⟨y, hy, rfl⟩; exact h a ha y hy⟩
  refine ⟨sSup (φ '' B), fun x hx => csSup_le (hB.image _) ?_, fun y hy =>
    le_csSup hbdd (mem_image_of_mem _ hy)⟩
  rintro _ ⟨y, hy, rfl⟩
  exact h x hx y hy

/-- **Theorem 15.2, interior-point case**: if `A, B` are convex, `A ≠ ∅`, `B̊ ≠ ∅` and
`A ∩ B̊ = ∅`, then some nonzero `φ ∈ S*` and `c` satisfy `φ(y) ≤ c ≤ φ(x)` for `x ∈ A`,
`y ∈ B`. This is Mathlib's `geometric_hahn_banach_of_nonempty_interior`. -/
theorem theorem_15_2_interior {A B : Set S} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hAne : A.Nonempty) (hBint : (interior B).Nonempty) (hAB : A ∩ interior B = ∅) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ A, c ≤ φ x) ∧ ∀ y ∈ B, φ y ≤ c := by
  obtain ⟨f, u, hf, hB', hA'⟩ := geometric_hahn_banach_of_nonempty_interior hB hA
    (Set.disjoint_iff_inter_eq_empty.2 (by rw [inter_comm]; exact hAB)) hBint hAne
  exact ⟨f, hf, u, hA', hB'⟩

/-- **Theorem 15.2, finite-dimensional case**: in a finite-dimensional space, disjoint nonempty
convex sets are separated by a nonzero functional. Proof with `C = A − B` (convex, `0 ∉ C`): if
`C̊ ≠ ∅`, separate `0` from `C` with the interior-point case. Otherwise the affine span of `C` is
a proper affine subspace, and a nonzero functional vanishing on its direction is constant
on `C`. -/
theorem theorem_15_2_finiteDimensional [FiniteDimensional ℝ S] {A B : Set S} (hA : Convex ℝ A)
    (hB : Convex ℝ B) (hAne : A.Nonempty) (hBne : B.Nonempty) (hAB : A ∩ B = ∅) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ A, c ≤ φ x) ∧ ∀ y ∈ B, φ y ≤ c := by
  suffices h : ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∀ x ∈ A, ∀ y ∈ B, φ y ≤ φ x by
    obtain ⟨φ, hφ, h⟩ := h
    exact ⟨φ, hφ, exists_const_between_of_le hAne hBne φ h⟩
  have hC : Convex ℝ (A - B) := hA.sub hB
  have h0 : (0 : S) ∉ A - B := by
    rintro ⟨a, ha, b, hb, hab⟩
    have : a = b := sub_eq_zero.1 hab
    exact (Set.eq_empty_iff_forall_notMem.1 hAB) a ⟨ha, this ▸ hb⟩
  by_cases hint : (interior (A - B)).Nonempty
  · obtain ⟨f, u, hf, hC', h0'⟩ := geometric_hahn_banach_of_nonempty_interior hC
      (convex_singleton 0) (disjoint_singleton_right.2 fun h => h0 (interior_subset h)) hint
      (singleton_nonempty 0)
    refine ⟨-f, neg_ne_zero.2 hf, fun x hx y hy => ?_⟩
    have h1 := hC' (x - y) (sub_mem_sub hx hy)
    have h2 := h0' 0 rfl
    simp only [map_zero, map_sub] at h1 h2
    simp only [neg_apply]
    linarith
  · have hspan : affineSpan ℝ (A - B) ≠ ⊤ := fun h =>
      hint (hC.interior_nonempty_iff_affineSpan_eq_top.2 h)
    obtain ⟨a0, ha0⟩ := hAne
    obtain ⟨b0, hb0⟩ := hBne
    have hc0 : a0 - b0 ∈ A - B := sub_mem_sub ha0 hb0
    have hdir : (affineSpan ℝ (A - B)).direction < ⊤ := by
      refine lt_top_iff_ne_top.2 fun h => hspan ?_
      exact (AffineSubspace.direction_eq_top_iff_of_nonempty
        ((affineSpan_nonempty ℝ).2 ⟨_, hc0⟩)).1 h
    obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hdir
    let g : StrongDual ℝ S := LinearMap.toContinuousLinearMap f
    have hg0 : g ≠ 0 := fun h => hf0 (LinearMap.ext fun x => congrArg (fun φ => φ x) h)
    have hconst : ∀ x ∈ A, ∀ y ∈ B, g (x - y) = g (a0 - b0) := fun x hx y hy => by
      have hm : (x - y) -ᵥ (a0 - b0) ∈ (affineSpan ℝ (A - B)).direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan _ _ (sub_mem_sub hx hy))
          (subset_affineSpan _ _ hc0)
      have := hker hm
      rw [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at this
      exact this
    by_cases hk : 0 ≤ g (a0 - b0)
    · refine ⟨g, hg0, fun x hx y hy => ?_⟩
      have := hconst x hx y hy
      rw [map_sub] at this
      linarith
    · refine ⟨-g, neg_ne_zero.2 hg0, fun x hx y hy => ?_⟩
      have := hconst x hx y hy
      rw [map_sub] at this
      simp only [neg_apply]
      linarith

/-- **Theorem 15.2** (corrected, with `A ≠ ∅` and, in the finite-dimensional case, `B ≠ ∅`):
for convex `A, B ⊆ S` with either `B̊ ≠ ∅` and `A ∩ B̊ = ∅`, or `S` finite dimensional and
`A ∩ B = ∅`, some nonzero `φ ∈ S*` and `c ∈ ℝ` satisfy `φ(y) ≤ c ≤ φ(x)` for all `x ∈ A`,
`y ∈ B`. -/
theorem theorem_15_2 {A B : Set S} (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne : A.Nonempty)
    (h : ((interior B).Nonempty ∧ A ∩ interior B = ∅) ∨
      (FiniteDimensional ℝ S ∧ B.Nonempty ∧ A ∩ B = ∅)) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ A, c ≤ φ x) ∧ ∀ y ∈ B, φ y ≤ c := by
  rcases h with ⟨hBint, hAB⟩ | ⟨hfin, hBne, hAB⟩
  · exact theorem_15_2_interior hA hB hAne hBint hAB
  · exact theorem_15_2_finiteDimensional hA hB hAne hBne hAB

/-- The book's statement of Theorem 15.2 (pp. 450–451), with no nonemptiness hypotheses. -/
def BookTheorem15_2 (S : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S] : Prop :=
  ∀ A B : Set S, Convex ℝ A → Convex ℝ B →
    (((interior B).Nonempty ∧ A ∩ interior B = ∅) ∨ (FiniteDimensional ℝ S ∧ A ∩ B = ∅)) →
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ A, c ≤ φ x) ∧ ∀ y ∈ B, φ y ≤ c

/-- A nonzero continuous linear functional is unbounded above. -/
theorem exists_lt_apply_of_ne_zero {φ : StrongDual ℝ S} (hφ : φ ≠ 0) (c : ℝ) :
    ∃ y, c < φ y := by
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    exact hφ (ContinuousLinearMap.ext fun v => not_not.1 fun hv => h ⟨v, hv⟩)
  refine ⟨((|c| + 1) / φ v) • v, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  linarith [le_abs_self c]

/-- **Correction (p. 450)**: the book's Theorem 15.2 is false on `ℝ`. Take `A = ∅` and `B = ℝ`:
`B` has interior points and `A ∩ B̊ = ∅`, but no nonzero `φ` is bounded above on `B`. -/
theorem theorem_15_2_counterexample : ¬ BookTheorem15_2 ℝ := by
  intro h
  obtain ⟨φ, hφ, c, -, hB⟩ := h ∅ univ convex_empty convex_univ
    (Or.inl ⟨by simp, by simp⟩)
  obtain ⟨y, hy⟩ := exists_lt_apply_of_ne_zero hφ c
  exact absurd (hB y trivial) (not_le.2 hy)

/-- **Correction (p. 450)**, finite-dimensional case: `A = ℝ`, `B = ∅` satisfy the book's
hypotheses (`ℝ` is finite dimensional and `A ∩ B = ∅`), but no nonzero `φ` is bounded below
on `A`. -/
theorem theorem_15_2_counterexample_finiteDimensional :
    FiniteDimensional ℝ ℝ ∧ (univ : Set ℝ) ∩ ∅ = ∅ ∧
      ¬ ∃ φ : StrongDual ℝ ℝ, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ (univ : Set ℝ), c ≤ φ x) ∧
        ∀ y ∈ (∅ : Set ℝ), φ y ≤ c := by
  refine ⟨inferInstance, by simp, ?_⟩
  rintro ⟨φ, hφ, c, hA, -⟩
  obtain ⟨y, hy⟩ := exists_lt_apply_of_ne_zero (neg_ne_zero.2 hφ) (-c)
  have := hA y trivial
  simp only [neg_apply] at hy
  linarith

/-! ### Exercise 15.6 -/

variable {β : ℝ}

/-- **Exercise 15.6** (book form): for `0 < β < 1` and every `ε > 0` there is a sequence `y`
with `Σ βᵗ |yₜ| < ε` and some `|yₜ| > 1`. So every ball about `θ` in
`S = {x : Σ βᵗ |xₜ| < ∞}` leaves `B = {x : |xₜ| ≤ 1 for all t}`, and `θ ∉ B̊`. The book's
witness has one entry `ε/β^{T−1}`; here it is `2` at a `T` with `βᵀ < ε/2`. -/
theorem ex_15_6 (hβ0 : 0 < β) (hβ1 : β < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℕ → ℝ, Summable (fun t => β ^ t * |y t|) ∧ ∑' t, β ^ t * |y t| < ε ∧
      ¬ ∀ t, |y t| ≤ 1 := by
  obtain ⟨T, hT⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).eventually
    (gt_mem_nhds (half_pos hε))).exists
  have hs : ∀ t, t ≠ T → β ^ t * |(Pi.single T (2 : ℝ) : ℕ → ℝ) t| = 0 := fun t ht => by
    simp [Pi.single_eq_of_ne ht]
  refine ⟨Pi.single T 2, summable_of_ne_finset_zero (s := {T}) fun t ht =>
    hs t (by simpa using ht), ?_, fun h => ?_⟩
  · rw [tsum_eq_single T hs, Pi.single_eq_same]
    norm_num
    linarith
  · have := h T
    rw [Pi.single_eq_same] at this
    norm_num at this

/-- The isometry from the book's space `S = {x : Σ βᵗ |xₜ| < ∞}` onto `ℓ₁`, `xₜ ↦ βᵗ xₜ`. -/
noncomputable def weightToEllOne (β : ℝ) (x : ℕ → ℝ) (hx : Summable fun t => β ^ t * |x t|)
    (hβ : 0 ≤ β) : ellOneSp :=
  ⟨fun t => β ^ t * x t, (memℓp_gen_iff (p := 1) (by simp)).2 (by
    refine hx.congr fun t => ?_
    simp [abs_of_nonneg hβ])⟩

/-- `weightToEllOne` is an isometry: `‖x − x'‖_S = Σ βᵗ |xₜ − x'ₜ|` is the `ℓ₁` distance of
the images. -/
theorem dist_weightToEllOne (hβ : 0 ≤ β) {x x' : ℕ → ℝ} (hx : Summable fun t => β ^ t * |x t|)
    (hx' : Summable fun t => β ^ t * |x' t|) :
    dist (weightToEllOne β x hx hβ) (weightToEllOne β x' hx' hβ) =
      ∑' t, β ^ t * |x t - x' t| := by
  rw [dist_eq_norm, lp.norm_eq_tsum_rpow (by simp)]
  simp only [ENNReal.toReal_one, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]
  congr 1
  ext t
  change ‖β ^ t * x t - β ^ t * x' t‖ = _
  rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hβ t)]

/-- `weightToEllOne` maps the book's space `S` onto `ℓ₁`. -/
theorem weightToEllOne_surjective (hβ : 0 < β) (z : ellOneSp) :
    ∃ x : ℕ → ℝ, ∃ hx : Summable (fun t => β ^ t * |x t|), weightToEllOne β x hx hβ.le = z := by
  refine ⟨fun t => z t / β ^ t, (summable_abs_ellOneSp z).congr fun t => ?_, ?_⟩
  · rw [abs_div, abs_of_pos (pow_pos hβ t), mul_div_cancel₀ _ (pow_pos hβ t).ne']
  · refine lp.ext (funext fun t => ?_)
    change β ^ t * (z t / β ^ t) = z t
    rw [mul_div_cancel₀ _ (pow_pos hβ t).ne']

/-- The image of the box `B = {|xₜ| ≤ 1}` under `weightToEllOne`: `{z ∈ ℓ₁ : |zₜ| ≤ βᵗ}`. -/
def ex156Box (β : ℝ) : Set ellOneSp := {z | ∀ t, |z t| ≤ β ^ t}

/-- `weightToEllOne` maps `B` exactly onto `ex156Box β`. -/
theorem weightToEllOne_mem_ex156Box_iff (hβ : 0 < β) {x : ℕ → ℝ}
    (hx : Summable fun t => β ^ t * |x t|) :
    weightToEllOne β x hx hβ.le ∈ ex156Box β ↔ ∀ t, |x t| ≤ 1 := by
  refine forall_congr' fun t => ?_
  change |β ^ t * x t| ≤ β ^ t ↔ _
  rw [abs_mul, abs_of_pos (pow_pos hβ t)]
  constructor
  · intro h; exact le_of_mul_le_mul_left (by simpa using h) (pow_pos hβ t)
  · intro h; exact mul_le_of_le_one_right (pow_pos hβ t).le h

/-- The box is convex. -/
theorem convex_ex156Box : Convex ℝ (ex156Box β) := by
  intro x hx y hy a b ha hb hab t
  change |a * x t + b * y t| ≤ β ^ t
  calc |a * x t + b * y t| ≤ a * |x t| + b * |y t| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * β ^ t + b * β ^ t := by gcongr; exacts [hx t, hy t]
    _ = β ^ t := by rw [← add_mul, hab, one_mul]

/-- `θ` lies in the box. -/
theorem zero_mem_ex156Box (hβ : 0 < β) : (0 : ellOneSp) ∈ ex156Box β := fun t => by
  simp [(pow_pos hβ t).le]

/-- The box has empty interior: from any `z` in it, `z + 3βᵗ eₜ` is within `3βᵗ` but outside
it. -/
theorem interior_ex156Box (hβ0 : 0 < β) (hβ1 : β < 1) : interior (ex156Box β) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hz)
  have hzB : z ∈ ex156Box β := interior_subset hz
  obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).eventually
    (gt_mem_nhds (div_pos hε three_pos))).exists
  have hw : z + lp.single 1 t (3 * β ^ t) ∈ ball z ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, lp.norm_single (by simp), Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have h1 := hball hw t
  have h2 := hzB t
  change |z t + (Pi.single t (3 * β ^ t) : ℕ → ℝ) t| ≤ β ^ t at h1
  rw [Pi.single_eq_same] at h1
  have hp := pow_pos hβ0 t
  have := neg_abs_le (z t)
  have := abs_le.1 h1
  have := abs_le.1 h2
  linarith

/-- **Exercise 15.6** (in `ℓ₁` coordinates): `θ` is not an interior point of `B`. -/
theorem ex_15_6_zero_notMem_interior (hβ0 : 0 < β) (hβ1 : β < 1) :
    (0 : ellOneSp) ∉ interior (ex156Box β) := by
  rw [interior_ex156Box hβ0 hβ1]; exact notMem_empty _

/-- The only continuous linear `φ` with `φ ≤ 0` on `B` is `φ = 0` (the book's claim on p. 451):
`B = −B`, `βᵗ eₜ ∈ B`, and the `eₜ` determine `φ`. -/
theorem eq_zero_of_le_zero_on_ex156Box (hβ0 : 0 < β) {φ : StrongDual ℝ ellOneSp}
    (h : ∀ z ∈ ex156Box β, φ z ≤ 0) : φ = 0 := by
  have hs : ∀ t, φ (lp.single 1 t 1) = 0 := fun t => by
    have hp := pow_pos hβ0 t
    have mem : ∀ a : ℝ, |a| ≤ 1 → lp.single 1 t (a * β ^ t) ∈ ex156Box β := fun a ha s => by
      change |(Pi.single t (a * β ^ t) : ℕ → ℝ) s| ≤ β ^ s
      by_cases hst : s = t
      · subst hst
        rw [Pi.single_eq_same, abs_mul, abs_of_pos hp]
        exact mul_le_of_le_one_left hp.le ha
      · rw [Pi.single_eq_of_ne hst]; simp [(pow_pos hβ0 s).le]
    have e : ∀ a : ℝ, φ (lp.single 1 t (a * β ^ t)) = a * β ^ t * φ (lp.single 1 t 1) :=
      fun a => by
        have hsm : lp.single 1 t (a * β ^ t) =
            (a * β ^ t) • lp.single (E := fun _ : ℕ => ℝ) 1 t 1 := by
          rw [← lp.single_smul, smul_eq_mul, mul_one]
        rw [hsm, map_smul, smul_eq_mul]
    have h1 := h _ (mem 1 (by simp))
    have h2 := h _ (mem (-1) (by simp))
    rw [e] at h1 h2
    have : β ^ t * φ (lp.single 1 t 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hp.ne'
    · exact h
  refine lp.ext_continuousLinearMap (by simp) fun t => ?_
  ext
  simp [hs t]

/-- Without an interior point Theorem 15.2 fails (p. 451): `A = {θ}` and `B` are convex and
`A ∩ B̊ = ∅`, but no nonzero `φ` and `c` give `φ(y) ≤ c ≤ φ(x)` on `B` and `A`. -/
theorem ex_15_6_no_separation (hβ0 : 0 < β) (hβ1 : β < 1) :
    Convex ℝ ({0} : Set ellOneSp) ∧ Convex ℝ (ex156Box β) ∧
      ({0} : Set ellOneSp) ∩ interior (ex156Box β) = ∅ ∧
      ¬ ∃ φ : StrongDual ℝ ellOneSp, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ ({0} : Set ellOneSp), c ≤ φ x) ∧
        ∀ y ∈ ex156Box β, φ y ≤ c := by
  refine ⟨convex_singleton 0, convex_ex156Box, by simp [interior_ex156Box hβ0 hβ1], ?_⟩
  rintro ⟨φ, hφ, c, hA, hB⟩
  have hc : c ≤ 0 := by simpa using hA 0 rfl
  exact hφ (eq_zero_of_le_zero_on_ex156Box hβ0 fun z hz => (hB z hz).trans hc)

end StokeyLucasPrescott.ParetoOptimaEquilibria
