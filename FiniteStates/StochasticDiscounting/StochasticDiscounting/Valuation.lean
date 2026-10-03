/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDiscounting.PositiveMatrices
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Lifetime valuation with time-varying discount factors

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.1.1–§6.1.2
(pp. 182–189).

* The discount operator `L(x, x') = b(x, x')P(x, x')` of (6.4). In operator
  form the `t`-period discounted expectation `E_x[β₁⋯βₜ h(Xₜ)]` of (6.6) is
  `(Lᵗh)(x)`, with the recursion (6.7) `Lᵗ⁺¹h = Lᵗ(Lh)`.
* Theorem 6.1.1: if `ρ(L) < 1` then `∑ₜ Lᵗh` converges and equals
  `(I − L)⁻¹h`, the unique solution of `v = h + Lv`. With `b ≡ β` this is
  Lemma 3.2.1, since `ρ(βP) = β`.
* Exercise 6.1.1: firm valuation with state-dependent interest rates;
  Exercise 6.1.2: the value is increasing when `P` is monotone, profits are
  increasing and nonnegative, and the interest rate is decreasing. The book
  omits nonnegativity of profits, without which the claim fails
  (see `docs/corrections.md`).
* Lemma 6.1.2: `ρ(L) = lim ℓₜ^{1/t}` with `ℓₜ = max_x (Lᵗ𝟙)(x)`, and
  `ρ(L) < 1` iff some `ℓₜ < 1`.
* Lemma 6.1.3: on a product state space `Y × Z` with the discount factor
  depending on the `Z` component only, `ρ(L) = ρ(L_Z)`. The kernel on `Y` may
  depend on the whole state, which §6.2.1.5 needs.
* Lemma 6.1.4: for `L ≥ 0` and `h ≫ 0`, `ρ(L) < 1` iff `v = h + Lv` has a
  unique solution in `(0, ∞)^X`, by the Perron–Frobenius left eigenvector.
-/

open Matrix Finset Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The discount operator (6.4) -/

omit [Fintype X] [DecidableEq X] in
/-- The discount operator (6.4): `L(x, x') = b(x, x')P(x, x')`. -/
def discountOp (b : X → X → ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => b x x' * P x x'

omit [Fintype X] [DecidableEq X] in
theorem discountOp_apply (b : X → X → ℝ) (P : Matrix X X ℝ) (x x' : X) :
    discountOp b P x x' = b x x' * P x x' := rfl

omit [Fintype X] [DecidableEq X] in
theorem discountOp_nonneg {b : X → X → ℝ} {P : Matrix X X ℝ} (hb : ∀ x x', 0 ≤ b x x')
    (hP : ∀ x x', 0 ≤ P x x') (x x' : X) : 0 ≤ discountOp b P x x' :=
  mul_nonneg (hb x x') (hP x x')

/-- (6.7): the `(t+1)`-period discounted expectation of `h` is the `t`-period discounted
expectation of `f = Lh`, in operator form `Lᵗ⁺¹h = Lᵗ(Lh)`. -/
theorem pow_succ_mulVec (L : Matrix X X ℝ) (h : X → ℝ) (t : ℕ) :
    L ^ (t + 1) *ᵥ h = L ^ t *ᵥ (L *ᵥ h) := by
  rw [pow_succ, ← mulVec_mulVec]

omit [Fintype X] [DecidableEq X] in
/-- Constant discounting `b ≡ β` gives `L = βP`. -/
theorem discountOp_const (β : ℝ) (P : Matrix X X ℝ) : discountOp (fun _ _ => β) P = β • P := by
  ext x x'
  simp [discountOp]

omit [DecidableEq X] in
/-- `ρ(βP) = β` for a Markov matrix `P` and `β ≥ 0`, so Theorem 6.1.1 contains Lemma 3.2.1. -/
theorem specRad_smul_isMarkov [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ}
    (hβ : 0 ≤ β) : specRad (β • P) = β := by
  classical
  exact
  specRad_eq_of_rowsum_eq _ (fun x x' => mul_nonneg hβ (hP.nonneg x x')) hβ fun x => by
    simp only [← mul_sum, hP.rowsum, mul_one]

/-! ### Theorem 6.1.1 -/

variable [Nonempty X]

/-- Under `ρ(L) < 1` the entries of `Lᵗ` are summable in `t`. -/
theorem summable_pow_apply {L : Matrix X X ℝ} (hρ : specRad L < 1) (x x' : X) :
    Summable fun t : ℕ => (L ^ t) x x' := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg L).trans hr1.le
  refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0 hr2) ?_
  exact (eventually_abs_entry_pow_le L hr1 x x').mono fun t ht => by rwa [Real.norm_eq_abs]

/-- Under `ρ(L) < 1` the series `∑ₜ Lᵗh` converges. -/
theorem summable_pow_mulVec {L : Matrix X X ℝ} (hρ : specRad L < 1) (h : X → ℝ) :
    Summable fun t : ℕ => L ^ t *ᵥ h := by
  rw [Pi.summable]
  intro x
  simp only [mulVec, dotProduct]
  exact summable_sum fun x' _ => (summable_pow_apply hρ x x').mul_right (h x')

/-- `L ∑ₜ Lᵗh = ∑ₜ Lᵗ⁺¹h`. -/
theorem mulVec_tsum_pow_mulVec {L : Matrix X X ℝ} (hρ : specRad L < 1) (h : X → ℝ) :
    L *ᵥ (∑' t : ℕ, L ^ t *ᵥ h) = ∑' t : ℕ, L ^ (t + 1) *ᵥ h := by
  have hs := summable_pow_mulVec hρ h
  let f : (X → ℝ) →L[ℝ] (X → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  have hf : L *ᵥ (∑' t : ℕ, L ^ t *ᵥ h) = f (∑' t : ℕ, L ^ t *ᵥ h) := rfl
  rw [hf, f.map_tsum hs]
  refine tsum_congr fun t => ?_
  change L *ᵥ (L ^ t *ᵥ h) = _
  rw [mulVec_mulVec, ← pow_succ']

/-- (6.5): `v = ∑ₜ Lᵗh` solves `v = h + Lv`. -/
theorem tsum_pow_mulVec_eq {L : Matrix X X ℝ} (hρ : specRad L < 1) (h : X → ℝ) :
    (∑' t : ℕ, L ^ t *ᵥ h) = h + L *ᵥ ∑' t : ℕ, L ^ t *ᵥ h := by
  rw [mulVec_tsum_pow_mulVec hρ h, (summable_pow_mulVec hρ h).tsum_eq_zero_add]
  simp

omit [DecidableEq X] in
/-- Uniqueness in Theorem 6.1.1: `I − L` is invertible, so `v = h + Lv` has at most one
solution. -/
theorem eq_of_eq_add_mulVec {L : Matrix X X ℝ} (hρ : specRad L < 1) {h v w : X → ℝ}
    (hv : v = h + L *ᵥ v) (hw : w = h + L *ᵥ w) : v = w := by
  classical
  have hunit := (neumann_series L hρ).1
  apply Matrix.mulVec_injective_iff_isUnit.2 hunit
  change (1 - L) *ᵥ v = (1 - L) *ᵥ w
  rw [sub_mulVec, one_mulVec, sub_mulVec, one_mulVec, sub_eq_of_eq_add hv, sub_eq_of_eq_add hw]

/-- `(I − L)⁻¹h` solves `v = h + Lv`. -/
theorem inv_mulVec_eq_add {L : Matrix X X ℝ} (hρ : specRad L < 1) (h : X → ℝ) :
    (1 - L)⁻¹ *ᵥ h = h + L *ᵥ ((1 - L)⁻¹ *ᵥ h) := by
  have hunit := (neumann_series L hρ).1
  have h1 : (1 - L) *ᵥ ((1 - L)⁻¹ *ᵥ h) = h := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
      one_mulVec]
  rw [sub_mulVec, one_mulVec] at h1
  exact eq_add_of_sub_eq h1

/-- **Theorem 6.1.1** (p. 185), the formula (6.5): `∑ₜ Lᵗh = (I − L)⁻¹h` when `ρ(L) < 1`. -/
theorem inv_mulVec_eq_tsum {L : Matrix X X ℝ} (hρ : specRad L < 1) (h : X → ℝ) :
    (1 - L)⁻¹ *ᵥ h = ∑' t : ℕ, L ^ t *ᵥ h :=
  eq_of_eq_add_mulVec hρ (inv_mulVec_eq_add hρ h) (tsum_pow_mulVec_eq hρ h)

/-- **Theorem 6.1.1** (p. 185), the equation: `v = h + Lv` iff `v = (I − L)⁻¹h`. -/
theorem eq_add_mulVec_iff {L : Matrix X X ℝ} (hρ : specRad L < 1) (h v : X → ℝ) :
    v = h + L *ᵥ v ↔ v = (1 - L)⁻¹ *ᵥ h :=
  ⟨fun hv => eq_of_eq_add_mulVec hρ hv (inv_mulVec_eq_add hρ h), fun hv => by
    rw [hv]; exact inv_mulVec_eq_add hρ h⟩

/-- **Theorem 6.1.1** (p. 185) for the discount operator (6.4): the lifetime value (6.3), in its
operator form `∑ₜ Lᵗh`, converges and equals `(I − L)⁻¹h`. -/
theorem discountOp_value {b : X → X → ℝ} {P : Matrix X X ℝ} (hρ : specRad (discountOp b P) < 1)
    (h : X → ℝ) :
    (Summable fun t : ℕ => discountOp b P ^ t *ᵥ h) ∧
      (1 - discountOp b P)⁻¹ *ᵥ h = ∑' t : ℕ, discountOp b P ^ t *ᵥ h :=
  ⟨summable_pow_mulVec hρ h, inv_mulVec_eq_tsum hρ h⟩

omit [DecidableEq X] in
/-- Theorem 6.1.1 with `b ≡ β ∈ [0, 1)` is Lemma 3.2.1: `ρ(βP) = β < 1`. -/
theorem specRad_discountOp_const_lt_one {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) : specRad (discountOp (fun _ _ => β) P) < 1 := by
  classical
  rw [discountOp_const, specRad_smul_isMarkov hP hβ0]
  exact hβ1

/-! ### Exercises 6.1.1 and 6.1.2: firm valuation -/

omit [DecidableEq X] [Nonempty X] in
/-- Exercise 6.1.1 (p. 186): with `rₜ = r(Xₜ)` and `βₜ = 1/(1 + rₜ)`, the discount operator is
`L(x, x') = P(x, x')/(1 + r(x'))`. -/
noncomputable def firmDiscountOp (r : X → ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  discountOp (fun _ x' => 1 / (1 + r x')) P

/-- Exercise 6.1.1 (p. 186): if `ρ(L) < 1` the firm's value is finite and equals
`(I − L)⁻¹π = ∑ₜ Lᵗπ`, computable by solving the linear system `v = π + Lv`. -/
theorem firmValue_eq {r : X → ℝ} {P : Matrix X X ℝ} (hρ : specRad (firmDiscountOp r P) < 1)
    (π : X → ℝ) :
    (1 - firmDiscountOp r P)⁻¹ *ᵥ π = ∑' t : ℕ, firmDiscountOp r P ^ t *ᵥ π ∧
      ∀ v, v = π + firmDiscountOp r P *ᵥ v ↔ v = (1 - firmDiscountOp r P)⁻¹ *ᵥ π :=
  ⟨inv_mulVec_eq_tsum hρ π, eq_add_mulVec_iff hρ π⟩

omit [DecidableEq X] [Nonempty X] in
/-- `Lg = P(b ⊙ g)` with `b(x') = 1/(1 + r(x'))`. -/
theorem firmDiscountOp_mulVec (r : X → ℝ) (P : Matrix X X ℝ) (g : X → ℝ) :
    firmDiscountOp r P *ᵥ g = P *ᵥ fun x' => 1 / (1 + r x') * g x' := by
  funext x
  simp only [firmDiscountOp, discountOp, mulVec, dotProduct, Matrix.of_apply]
  exact sum_congr rfl fun x' _ => by ring

omit [DecidableEq X] [Nonempty X] in
/-- A monotone increasing Markov matrix (Vol. 1, §3.2.2): `Ph` is increasing whenever `h` is. -/
def MonotoneKernel [Preorder X] (P : Matrix X X ℝ) : Prop :=
  ∀ h : X → ℝ, Monotone h → Monotone (P *ᵥ h)

/-- Exercise 6.1.2 (p. 186), with the hypothesis `π ≥ 0` that the book omits: if `P` is monotone
increasing, `π` is increasing and nonnegative, `r > −1` is decreasing and `ρ(L) < 1`, then the
firm's value `v = (I − L)⁻¹π` is increasing. Each term `Lᵗπ` is increasing and nonnegative, and so
is the sum. -/
theorem monotone_firmValue [Preorder X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hPm : MonotoneKernel P) {r π : X → ℝ} (hr : Antitone r) (hr1 : ∀ x, -1 < r x)
    (hπ : Monotone π) (hπ0 : ∀ x, 0 ≤ π x) (hρ : specRad (firmDiscountOp r P) < 1) :
    Monotone ((1 - firmDiscountOp r P)⁻¹ *ᵥ π) := by
  rw [inv_mulVec_eq_tsum hρ]
  have hb : Monotone fun x => 1 / (1 + r x) := fun x y hxy =>
    one_div_le_one_div_of_le (by linarith [hr1 y]) (by linarith [hr hxy])
  have hb0 : ∀ x, 0 ≤ 1 / (1 + r x) := fun x =>
    div_nonneg zero_le_one (by linarith [hr1 x])
  have key : ∀ t : ℕ, Monotone (firmDiscountOp r P ^ t *ᵥ π) ∧
      ∀ x, 0 ≤ (firmDiscountOp r P ^ t *ᵥ π) x := by
    intro t
    induction t with
    | zero => simpa using ⟨hπ, hπ0⟩
    | succ t ih =>
      rw [pow_succ', ← mulVec_mulVec, firmDiscountOp_mulVec]
      have hg : Monotone fun x' => 1 / (1 + r x') * (firmDiscountOp r P ^ t *ᵥ π) x' :=
        hb.mul ih.1 hb0 ih.2
      exact ⟨hPm _ hg, fun x => sum_nonneg fun x' _ =>
        mul_nonneg (hP.nonneg x x') (mul_nonneg (hb0 x') (ih.2 x'))⟩
  intro x y hxy
  have hs := summable_pow_mulVec hρ π
  rw [Pi.tsum_apply hs, Pi.tsum_apply hs]
  exact Summable.tsum_le_tsum (fun t => (key t).1 hxy) (Pi.summable.1 hs x) (Pi.summable.1 hs y)

/-! ### Lemma 6.1.2: the spectral radius via expectations -/

omit [Nonempty X] in
/-- `Lᵗ𝟙 ≥ 0` for `L ≥ 0`. -/
theorem pow_mulVec_one_nonneg {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') (t : ℕ) (x : X) :
    0 ≤ (L ^ t *ᵥ fun _ => (1 : ℝ)) x :=
  sum_nonneg fun x' _ => mul_nonneg (pow_nonneg_entries hL t x x') zero_le_one

/-- `ℓₜ = max_x E_x[β₁⋯βₜ] = max_x (Lᵗ𝟙)(x)` equals `‖Lᵗ𝟙‖_∞`, as in the proof of Lemma 6.1.2. -/
theorem sup'_pow_mulVec_one_eq_norm {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') (t : ℕ) :
    (univ.sup' univ_nonempty fun x => (L ^ t *ᵥ fun _ => (1 : ℝ)) x) =
      ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ := by
  have hnn := pow_mulVec_one_nonneg hL t
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun x _ => ?_
    have := norm_le_pi_norm (L ^ t *ᵥ fun _ => (1 : ℝ)) x
    rwa [Real.norm_eq_abs, abs_of_nonneg (hnn x)] at this
  · rw [pi_norm_le_iff_of_nonneg
      ((hnn (Classical.arbitrary X)).trans (Finset.le_sup' _ (mem_univ _)))]
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
    exact Finset.le_sup' (fun x => (L ^ t *ᵥ fun _ => (1 : ℝ)) x) (mem_univ x)

/-- **Lemma 6.1.2** (p. 186), the formula (6.10): `ρ(L) = lim ℓₜ^{1/t}` with
`ℓₜ = max_x E_x[β₁⋯βₜ] = max_x (Lᵗ𝟙)(x)`, by the local spectral radius (Lemma 2.3.3). -/
theorem tendsto_sup'_pow_mulVec_one_rpow {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') :
    Tendsto (fun t : ℕ =>
      (univ.sup' univ_nonempty fun x => (L ^ t *ᵥ fun _ => (1 : ℝ)) x) ^ (1 / (t : ℝ)))
      atTop (𝓝 (specRad L)) := by
  simp only [sup'_pow_mulVec_one_eq_norm hL]
  exact tendsto_norm_pow_mulVec_rpow L hL fun _ => one_pos

/-- For `L ≥ 0`, `‖Lᵗ‖ = ‖Lᵗ𝟙‖_∞`: the operator norm is the largest row sum. -/
theorem norm_pow_eq_norm_pow_mulVec_one {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') (t : ℕ) :
    ‖L ^ t‖ = ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ := by
  have hnn := pow_mulVec_one_nonneg hL t
  apply le_antisymm
  · refine norm_le_of_rowsum_abs_le _ (norm_nonneg _) fun x => ?_
    have h1 : ∑ x', |(L ^ t) x x'| = (L ^ t *ᵥ fun _ => (1 : ℝ)) x := by
      simp only [mulVec, dotProduct, mul_one]
      exact sum_congr rfl fun x' _ => abs_of_nonneg (pow_nonneg_entries hL t x x')
    rw [h1]
    have h2 := norm_le_pi_norm (L ^ t *ᵥ fun _ => (1 : ℝ)) x
    rwa [Real.norm_eq_abs, abs_of_nonneg (hnn x)] at h2
  · calc ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ ≤ ‖L ^ t‖ * ‖fun _ : X => (1 : ℝ)‖ :=
          Matrix.linfty_opNorm_mulVec _ _
      _ = ‖L ^ t‖ := by rw [pi_norm_const (1 : ℝ), norm_one, mul_one]

/-- `ρ(L) ≤ ‖Lⁿ⁺¹‖^{1/(n+1)}` for every `n`, the finite-step form of Gelfand's formula. -/
theorem specRad_le_norm_pow_rpow (L : Matrix X X ℝ) (n : ℕ) :
    specRad L ≤ ‖L ^ (n + 1)‖ ^ (1 / ((n : ℝ) + 1)) := by
  have h := spectrum.spectralRadius_le_pow_nnnorm_pow_one_div (𝕜 := ℂ) (complexify L) n
  have hone : ‖(1 : Matrix X X ℂ)‖₊ = 1 := by
    have h1 : (1 : Matrix X X ℂ) = complexify 1 := by
      rw [← pow_zero (complexify L), ← complexify_pow, pow_zero]
    rw [h1, nnnorm_complexify]
    apply NNReal.eq
    rw [coe_nnnorm, NNReal.coe_one]
    refine norm_eq_of_rowsum_eq (1 : Matrix X X ℝ) (fun i j => ?_) zero_le_one fun i => ?_
    · rw [Matrix.one_apply]
      split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  rw [hone, ENNReal.coe_one, ENNReal.one_rpow, mul_one, ← complexify_pow, nnnorm_complexify] at h
  have h2 := ENNReal.toReal_mono
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.coe_ne_top) h
  rw [← ENNReal.toReal_rpow, ENNReal.coe_toReal, coe_nnnorm] at h2
  exact_mod_cast h2

/-- **Lemma 6.1.2** (p. 187), second claim: for `L ≥ 0`, `ρ(L) < 1` iff `ℓₜ = ‖Lᵗ𝟙‖_∞ < 1` for
some `t ≥ 1`. The book cites Stachurski and Zhang (2021); the proof here is that `‖Lᵗ‖ = ℓₜ` for
`L ≥ 0`, `‖Lᵗ‖ → 0` when `ρ(L) < 1`, and `ρ(L) ≤ ‖Lᵗ‖^{1/t}`. -/
theorem specRad_lt_one_iff_exists_norm_pow_mulVec_one_lt {L : Matrix X X ℝ}
    (hL : ∀ x x', 0 ≤ L x x') :
    specRad L < 1 ↔ ∃ t : ℕ, 0 < t ∧ ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ < 1 := by
  constructor
  · intro hρ
    obtain ⟨t, ht1, ht0⟩ := (((tendsto_norm_pow_zero L hρ).eventually (gt_mem_nhds one_pos)).and
      (eventually_gt_atTop 0)).exists
    exact ⟨t, ht0, by rw [← norm_pow_eq_norm_pow_mulVec_one hL]; exact ht1⟩
  · rintro ⟨t, ht, hlt⟩
    rw [← norm_pow_eq_norm_pow_mulVec_one hL] at hlt
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    calc specRad L ≤ ‖L ^ (n + 1)‖ ^ (1 / ((n : ℝ) + 1)) := specRad_le_norm_pow_rpow L n
      _ < 1 := Real.rpow_lt_one (norm_nonneg _) hlt (by positivity)

/-- The spectral radius of `L ≥ 0` is the limit of `‖Lᵗ𝟙‖^{1/t}` with `𝟙` replaced by any
`h ≫ 0`, as in Lemma 2.3.3; with `h = ψ*` for a stationary distribution this is the content of
Exercise 6.1.3 (`∑ₓ(Lᵗ𝟙)(x)ψ*(x)` is the `ψ*`-weighted ℓ¹ norm, equivalent to `‖·‖_∞`). -/
theorem tendsto_norm_pow_mulVec_rpow' {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') {h : X → ℝ}
    (hh : ∀ x, 0 < h x) :
    Tendsto (fun t : ℕ => ‖L ^ t *ᵥ h‖ ^ (1 / (t : ℝ))) atTop (𝓝 (specRad L)) :=
  tendsto_norm_pow_mulVec_rpow L hL hh

/-- Exercise 6.1.3 (p. 187): for an irreducible Markov matrix `P` with stationary distribution
`ψ*`, `ρ(L) = lim (E_{ψ*}[β₁⋯βₜ])^{1/t}` where `E_{ψ*}[β₁⋯βₜ] = ∑ₓ ψ*(x)(Lᵗ𝟙)(x) = ⟨ψ*, Lᵗ𝟙⟩`.
Since `ψ* ≫ 0` (Exercise 2.3.2 (iv)), the weighted sum is squeezed between
`(min ψ*)‖Lᵗ𝟙‖` and `‖Lᵗ𝟙‖`, and both have `t`-th roots converging to `ρ(L)`. -/
theorem tendsto_dotProduct_pow_mulVec_one_rpow {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hirr : Irreducible P) {b : X → X → ℝ} (hb : ∀ x x', 0 ≤ b x x') {ψ : X → ℝ}
    (hψ : IsDistribution ψ) (hψP : ψ ᵥ* P = ψ) :
    Tendsto (fun t : ℕ => (ψ ⬝ᵥ (discountOp b P ^ t *ᵥ fun _ => (1 : ℝ))) ^ (1 / (t : ℝ)))
      atTop (𝓝 (specRad (discountOp b P))) := by
  set L := discountOp b P with hLdef
  have hL : ∀ x x', 0 ≤ L x x' := discountOp_nonneg hb hP.nonneg
  -- `ψ* ≫ 0`
  obtain ⟨ψ', -, -, hψ'pos, huniq⟩ := hP.exists_unique_stationary_of_irreducible hirr
  have hψpos : ∀ x, 0 < ψ x := by
    rw [huniq ψ hψ hψP]
    exact hψ'pos
  obtain ⟨x₀, -, hx₀⟩ := exists_min_image univ ψ univ_nonempty
  set m := ψ x₀ with hm
  have hmpos : 0 < m := hψpos x₀
  have hnn := pow_mulVec_one_nonneg hL
  -- the weighted sum lies between `m‖Lᵗ𝟙‖` and `‖Lᵗ𝟙‖`
  have hupper : ∀ t, ψ ⬝ᵥ (L ^ t *ᵥ fun _ => (1 : ℝ)) ≤ ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ := by
    intro t
    calc ψ ⬝ᵥ (L ^ t *ᵥ fun _ => (1 : ℝ)) = ∑ x, ψ x * (L ^ t *ᵥ fun _ => (1 : ℝ)) x := rfl
      _ ≤ ∑ x, ψ x * ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ := sum_le_sum fun x _ => by
          refine mul_le_mul_of_nonneg_left ?_ (hψ.nonneg x)
          have := norm_le_pi_norm (L ^ t *ᵥ fun _ => (1 : ℝ)) x
          rwa [Real.norm_eq_abs, abs_of_nonneg (hnn t x)] at this
      _ = ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ := by rw [← sum_mul, hψ.sum_eq_one, one_mul]
  have hlower : ∀ t, m * ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ ≤ ψ ⬝ᵥ (L ^ t *ᵥ fun _ => (1 : ℝ)) := by
    intro t
    obtain ⟨x, -, hx⟩ := exists_max_image univ (fun x => (L ^ t *ᵥ fun _ => (1 : ℝ)) x)
      univ_nonempty
    have hnorm : ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ = (L ^ t *ᵥ fun _ => (1 : ℝ)) x := by
      rw [← sup'_pow_mulVec_one_eq_norm hL]
      exact le_antisymm (Finset.sup'_le _ _ fun y _ => hx y (mem_univ y))
        (Finset.le_sup' (fun x => (L ^ t *ᵥ fun _ => (1 : ℝ)) x) (mem_univ x))
    rw [hnorm]
    calc m * (L ^ t *ᵥ fun _ => (1 : ℝ)) x ≤ ψ x * (L ^ t *ᵥ fun _ => (1 : ℝ)) x :=
          mul_le_mul_of_nonneg_right (hx₀ x (mem_univ x)) (hnn t x)
      _ ≤ ∑ y, ψ y * (L ^ t *ᵥ fun _ => (1 : ℝ)) y :=
          single_le_sum (fun y _ => mul_nonneg (hψ.nonneg y) (hnn t y)) (mem_univ x)
      _ = ψ ⬝ᵥ (L ^ t *ᵥ fun _ => (1 : ℝ)) := rfl
  have hG := tendsto_norm_pow_mulVec_rpow L hL fun _ : X => one_pos
  have hlo : Tendsto (fun t : ℕ => m ^ (1 / (t : ℝ)) * ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ ^ (1 / (t : ℝ)))
      atTop (𝓝 (1 * specRad L)) := (tendsto_rpow_one_div_natCast hmpos).mul hG
  rw [one_mul] at hlo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hG (fun t => ?_) (fun t => ?_)
  · rw [← Real.mul_rpow hmpos.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) (hlower t) (by positivity)
  · exact Real.rpow_le_rpow (dotProduct_nonneg_of_nonneg hψ.nonneg (hnn t)) (hupper t)
      (by positivity)

/-! ### Lemma 6.1.3: discounting that depends on a component of the state -/

variable {Y Z : Type*} [Fintype Y] [Fintype Z] [DecidableEq Y] [DecidableEq Z]

omit [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] in
/-- The discount operator on `X = Y × Z` when the discount factor depends only on the `Z`
component (p. 188): `L((y, z), (y', z')) = b(z, z')Q(z, z')R((y, z), y')`. The kernel `R` on `Y` is
allowed to depend on the whole current state, as in §6.2.1.5; the book's Lemma 6.1.3 has
`R(y, y')`. -/
def productDiscountOp (b : Z → Z → ℝ) (Q : Matrix Z Z ℝ) (R : Y × Z → Y → ℝ) :
    Matrix (Y × Z) (Y × Z) ℝ :=
  Matrix.of fun x x' => b x.2 x'.2 * Q x.2 x'.2 * R x x'.1

omit [DecidableEq Y] [DecidableEq Z] in
/-- `L(g ∘ snd) = (L_Z g) ∘ snd` when the rows of `R` sum to one. -/
theorem productDiscountOp_mulVec_comp_snd (b : Z → Z → ℝ) (Q : Matrix Z Z ℝ) {R : Y × Z → Y → ℝ}
    (hR : ∀ x, ∑ y', R x y' = 1) (g : Z → ℝ) :
    productDiscountOp b Q R *ᵥ (fun x => g x.2) = fun x => (discountOp b Q *ᵥ g) x.2 := by
  funext x
  simp only [mulVec, dotProduct, productDiscountOp, discountOp, Matrix.of_apply]
  rw [Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun z' _ => ?_
  have h : ∀ y', b x.2 z' * Q x.2 z' * R x y' * g z' = b x.2 z' * Q x.2 z' * g z' * R x y' :=
    fun y' => by ring
  simp only [h]
  rw [← mul_sum, hR, mul_one]

/-- `Lᵗ𝟙 = (L_Zᵗ𝟙) ∘ snd`: the expected discount factor does not depend on `y`. -/
theorem productDiscountOp_pow_mulVec_one (b : Z → Z → ℝ) (Q : Matrix Z Z ℝ) {R : Y × Z → Y → ℝ}
    (hR : ∀ x, ∑ y', R x y' = 1) (t : ℕ) :
    productDiscountOp b Q R ^ t *ᵥ (fun _ => (1 : ℝ)) =
      fun x => (discountOp b Q ^ t *ᵥ fun _ => (1 : ℝ)) x.2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, productDiscountOp_mulVec_comp_snd b Q hR]
    funext x
    rw [pow_succ', ← mulVec_mulVec]

omit [DecidableEq Y] [DecidableEq Z] in
/-- `‖g ∘ snd‖_∞ = ‖g‖_∞`. -/
theorem norm_comp_snd [Nonempty Y] (g : Z → ℝ) : ‖fun x : Y × Z => g x.2‖ = ‖g‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro x
    exact norm_le_pi_norm g x.2
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro z
    exact norm_le_pi_norm (fun x : Y × Z => g x.2) (Classical.arbitrary Y, z)

omit [DecidableEq Y] [DecidableEq Z] in
/-- **Lemma 6.1.3** (p. 188), in the general form with `R` depending on the whole state:
`ρ(L) = ρ(L_Z)`, since `Lᵗ𝟙 = (L_Zᵗ𝟙) ∘ snd` and both spectral radii are the limits of
Lemma 6.1.2. -/
theorem specRad_productDiscountOp [Nonempty Y] [Nonempty Z] {b : Z → Z → ℝ}
    (hb : ∀ z z', 0 ≤ b z z') {Q : Matrix Z Z ℝ} (hQ : ∀ z z', 0 ≤ Q z z') {R : Y × Z → Y → ℝ}
    (hR0 : ∀ x y', 0 ≤ R x y') (hR : ∀ x, ∑ y', R x y' = 1) :
    specRad (productDiscountOp b Q R) = specRad (discountOp b Q) := by
  classical
  have hL : ∀ x x', 0 ≤ productDiscountOp b Q R x x' := fun x x' =>
    mul_nonneg (mul_nonneg (hb _ _) (hQ _ _)) (hR0 _ _)
  have h1 := tendsto_norm_pow_mulVec_rpow (productDiscountOp b Q R) hL fun _ : Y × Z => one_pos
  have h2 := tendsto_norm_pow_mulVec_rpow (discountOp b Q) (discountOp_nonneg hb hQ)
    fun _ : Z => one_pos
  refine tendsto_nhds_unique h1 (h2.congr fun t => ?_)
  rw [productDiscountOp_pow_mulVec_one b Q hR, norm_comp_snd]

omit [DecidableEq Y] [DecidableEq Z] in
/-- **Lemma 6.1.3** (p. 188) as stated in the book: `R` is a Markov matrix on `Y`. -/
theorem specRad_productDiscountOp_isMarkov [Nonempty Y] [Nonempty Z] {b : Z → Z → ℝ}
    (hb : ∀ z z', 0 ≤ b z z') {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) {Rm : Matrix Y Y ℝ}
    (hRm : IsMarkov Rm) :
    specRad (productDiscountOp b Q fun x y' => Rm x.1 y') = specRad (discountOp b Q) :=
  specRad_productDiscountOp hb hQ.nonneg (fun x y' => hRm.nonneg x.1 y') fun x => hRm.rowsum x.1

/-! ### Lemma 6.1.4: necessity of the spectral radius condition -/

omit [DecidableEq X] in
/-- **Lemma 6.1.4** (p. 189): for a positive linear operator `L ≥ 0` and `h ≫ 0`, `ρ(L) < 1` iff
`v = h + Lv` has a unique solution in `V = (0, ∞)^X`. Sufficiency is Theorem 6.1.1 with
`v = ∑ Lᵗh ≥ h ≫ 0`; necessity pairs any positive solution with a Perron–Frobenius left eigenvector
`ε ≥ 0`, `ε ≠ 0`: `⟨ε, v⟩ = ρ(L)⟨ε, v⟩ + ⟨ε, h⟩` with `⟨ε, h⟩, ⟨ε, v⟩ > 0`. -/
theorem specRad_lt_one_iff_existsUnique_pos {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    {h : X → ℝ} (hh : ∀ x, 0 < h x) :
    specRad L < 1 ↔ ∃! v : X → ℝ, (∀ x, 0 < v x) ∧ v = h + L *ᵥ v := by
  classical
  constructor
  · intro hρ
    have hv0 : ∀ x, 0 ≤ ((1 - L)⁻¹ *ᵥ h) x := by
      intro x
      rw [inv_mulVec_eq_tsum hρ, Pi.tsum_apply (summable_pow_mulVec hρ h)]
      exact tsum_nonneg fun t =>
        sum_nonneg fun x' _ => mul_nonneg (pow_nonneg_entries hL t x x') (hh x').le
    refine ⟨(1 - L)⁻¹ *ᵥ h, ⟨fun x => ?_, inv_mulVec_eq_add hρ h⟩,
      fun v hv => (eq_add_mulVec_iff hρ h v).1 hv.2⟩
    have := congrFun (inv_mulVec_eq_add hρ h) x
    rw [this, Pi.add_apply]
    exact add_pos_of_pos_of_nonneg (hh x)
      (sum_nonneg fun x' _ => mul_nonneg (hL x x') (hv0 x'))
  · rintro ⟨v, ⟨hvpos, hv⟩, -⟩
    obtain ⟨ε, hε0, hεne, hεL⟩ := perron_frobenius_left L hL
    have hεv : ε ⬝ᵥ v = ε ⬝ᵥ h + specRad L * (ε ⬝ᵥ v) := by
      conv_lhs => rw [hv]
      rw [dotProduct_add, dotProduct_mulVec, hεL, smul_dotProduct, smul_eq_mul]
    obtain ⟨y, hy⟩ : ∃ y, 0 < ε y := by
      by_contra hcon
      exact hεne (funext fun x => le_antisymm (not_lt.1 fun hx => hcon ⟨x, hx⟩) (hε0 x))
    have hεh : 0 < ε ⬝ᵥ h :=
      sum_pos' (fun x _ => mul_nonneg (hε0 x) (hh x).le) ⟨y, mem_univ y, mul_pos hy (hh y)⟩
    have hεv' : 0 < ε ⬝ᵥ v :=
      sum_pos' (fun x _ => mul_nonneg (hε0 x) (hvpos x).le) ⟨y, mem_univ y, mul_pos hy (hvpos y)⟩
    by_contra hcon
    have h1 : 1 ≤ specRad L := not_lt.1 hcon
    nlinarith

end SargentStachurski.StochasticDiscounting
