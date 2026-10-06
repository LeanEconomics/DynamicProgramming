/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AbstractDynamicProgramming.Irreducible
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Linear valuation and eventual contractions, restated

Facts from Vol. 1, Chapter 6 used in Chapters 7–9, restated from the
`FiniteStates/StochasticDiscounting` project: the discount operator, Theorem 6.1.1
(`v = h + Lv` has the unique solution `(I − L)⁻¹h = ∑ₜ Lᵗh` when `ρ(L) < 1`),
`ρ(βP) = β`, Lemma 6.1.4 (for `L ≥ 0` and `h ≫ 0`, `ρ(L) < 1` iff `v = h + Lv` has a
unique positive solution), Theorem 6.1.5 (eventual contractions are globally
stable), Example 6.1.2 (affine maps) and Proposition 6.1.6.
-/

open Matrix Finset Filter Topology Function

namespace SargentStachurski.AbstractDynamicProgramming

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

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

/-! ### Eventual contractions -/

variable {E : Type*} [NormedAddCommGroup E]

/-- **Theorem 6.1.5** (p. 190), Exercise 6.1.4: if `T` maps the closed set `U` into itself and
`Tᵏ` is a contraction on `U` for some `k ≥ 1`, then `T` is globally stable on `U`: it has a unique
fixed point `u*` in `U`, and `Tⁿu → u*` for every `u ∈ U`. -/
theorem globallyStable_of_iterate_contraction [CompleteSpace E] {T : E → E} {U : Set E}
    (hU : IsClosed U) (hne : U.Nonempty) (hT : Set.MapsTo T U U) {k : ℕ} (hk : 0 < k) {L : ℝ}
    (hc : IsContractionOn (T^[k]) U L) :
    ∃ u' ∈ U, IsFixedPt T u' ∧ (∀ v ∈ U, IsFixedPt T v → v = u') ∧
      ∀ u ∈ U, Tendsto (fun n : ℕ => T^[n] u) atTop (𝓝 u') := by
  obtain ⟨u', hu'U, hfix⟩ := hc.exists_fixedPt hU hne
  -- `T u'` is a fixed point of `Tᵏ` in `U`, hence equals `u'`
  have hTfix : IsFixedPt T u' := by
    have h1 : IsFixedPt (T^[k]) (T u') := by
      change T^[k] (T u') = T u'
      rw [← iterate_succ_apply, iterate_succ_apply', hfix.eq]
    exact hc.fixedPt_unique (hT hu'U) hu'U h1 hfix
  refine ⟨u', hu'U, hTfix, fun v hv hvfix => hc.fixedPt_unique hv hu'U (hvfix.iterate k) hfix,
    fun u hu => ?_⟩
  -- `Tⁿu = (Tᵏ)^{n/k}(T^{n%k}u)`, and `‖T^{n%k}u − u'‖ ≤ M := ∑_{r<k} ‖Tʳu − u'‖`
  set M : ℝ := ∑ r ∈ range k, ‖T^[r] u - u'‖ with hM
  have hM0 : 0 ≤ M := sum_nonneg fun _ _ => norm_nonneg _
  have hbound : ∀ n : ℕ, ‖T^[n] u - u'‖ ≤ L ^ (n / k) * M := by
    intro n
    have hn : n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
    have h1 : T^[n] u = (T^[k])^[n / k] (T^[n % k] u) := by
      conv_lhs => rw [hn]
      rw [iterate_add_apply, iterate_mul]
    rw [h1]
    have h2 := hc.norm_iterate_sub_fixedPt_le (hT.iterate (n % k) hu) hu'U hfix (n / k)
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hc.nonneg _))
    exact single_le_sum (fun r _ => norm_nonneg (T^[r] u - u')) (mem_range.2 (Nat.mod_lt n hk))
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
  have h3 : Tendsto (fun n : ℕ => L ^ (n / k)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc.nonneg hc.lt_one).comp
      (Nat.tendsto_div_const_atTop hk.ne')
  simpa using h3.mul_const M

/-- Theorem 6.1.5 on the whole space, in the vocabulary of §1.2.2: an eventual contraction of
a complete space is globally stable. -/
theorem globallyStable_of_iterate_contraction_univ [CompleteSpace E] {T : E → E} {k : ℕ}
    (hk : 0 < k) {L : ℝ} (hc : IsContractionOn (T^[k]) Set.univ L) : GloballyStable T := by
  obtain ⟨u', -, hfix, huniq, hconv⟩ := globallyStable_of_iterate_contraction isClosed_univ
    ⟨0, Set.mem_univ 0⟩ (Set.mapsTo_univ T Set.univ) hk hc
  exact ⟨u', hfix, fun v hv => huniq v (Set.mem_univ v) hv, fun u => hconv u (Set.mem_univ u)⟩

omit [Fintype X] [DecidableEq X] in
/-- The affine map `Tu = Au + b` of Example 6.1.2. -/
def affineOp (A : Matrix X X ℝ) (b : X → ℝ) (u : X → ℝ) : X → ℝ := A *ᵥ u + b

omit [Nonempty X] in
/-- `Tᵏu − Tᵏv = Aᵏ(u − v)`. -/
theorem affineOp_iterate_sub (A : Matrix X X ℝ) (b u v : X → ℝ) (k : ℕ) :
    (affineOp A b)^[k] u - (affineOp A b)^[k] v = A ^ k *ᵥ (u - v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', affineOp, affineOp, add_sub_add_right_eq_sub,
      ← mulVec_sub, ih, mulVec_mulVec, ← pow_succ']

/-- Example 6.1.2 (p. 190): if `ρ(A) < 1` then some `Tᵏ` is a contraction under the supremum
norm, with modulus `‖Aᵏ‖ < 1`. -/
theorem exists_isContractionOn_iterate_affineOp {A : Matrix X X ℝ}
    (hρ : specRad A < 1) (b : X → ℝ) :
    ∃ k : ℕ, 0 < k ∧ IsContractionOn ((affineOp A b)^[k]) Set.univ ‖A ^ k‖ := by
  obtain ⟨k, hk1, hk0⟩ := (((tendsto_norm_pow_zero A hρ).eventually (gt_mem_nhds one_pos)).and
    (eventually_gt_atTop 0)).exists
  refine ⟨k, hk0, Set.mapsTo_univ _ _, norm_nonneg _, hk1, fun u _ v _ => ?_⟩
  rw [affineOp_iterate_sub]
  exact Matrix.linfty_opNorm_mulVec _ _

omit [DecidableEq X] in
/-- Example 6.1.2 (p. 190): `Tu = Au + b` with `ρ(A) < 1` is globally stable, by Theorem 6.1.5. -/
theorem globallyStable_affineOp {A : Matrix X X ℝ} (hρ : specRad A < 1)
    (b : X → ℝ) : GloballyStable (affineOp A b) := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_affineOp hρ b
  exact globallyStable_of_iterate_contraction_univ hk hc

/-- Example 6.1.2 (p. 190): the fixed point is `(I − A)⁻¹b`, by the Neumann series lemma. -/
theorem isFixedPt_affineOp_inv {A : Matrix X X ℝ} (hρ : specRad A < 1)
    (b : X → ℝ) : IsFixedPt (affineOp A b) ((1 - A)⁻¹ *ᵥ b) := by
  change A *ᵥ ((1 - A)⁻¹ *ᵥ b) + b = (1 - A)⁻¹ *ᵥ b
  rw [add_comm]
  exact (inv_mulVec_eq_add hρ b).symm

omit [DecidableEq X] [Nonempty X] in
/-- A nonnegative matrix preserves `≤`. -/
theorem mulVec_le_mulVec_of_nonneg {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') {f g : X → ℝ}
    (hfg : f ≤ g) : L *ᵥ f ≤ L *ᵥ g := fun x =>
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hfg x') (hL x x')

omit [DecidableEq X] [Nonempty X] in
/-- `‖|f|‖_∞ = ‖f‖_∞`. -/
theorem norm_abs_fun (f : X → ℝ) : ‖fun y => |f y|‖ = ‖f‖ := by
  simp only [Pi.norm_def, Real.nnnorm_abs]

omit [DecidableEq X] [Nonempty X] in
/-- If `|u| ≤ w` pointwise with `w ≥ 0`, then `‖u‖_∞ ≤ ‖w‖_∞`. -/
theorem norm_le_norm_of_abs_le_fun {u w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (h : ∀ x, |u x| ≤ w x) :
    ‖u‖ ≤ ‖w‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Real.norm_eq_abs]
  refine (h x).trans ?_
  have := norm_le_pi_norm w x
  rwa [Real.norm_eq_abs, abs_of_nonneg (hw x)] at this

omit [Nonempty X] in
/-- Iterating (6.13): `|Tᵏv − Tᵏw| ≤ Lᵏ|v − w|`, (6.14). -/
theorem abs_iterate_sub_le_pow_mulVec {T : (X → ℝ) → (X → ℝ)} {U : Set (X → ℝ)}
    (hT : Set.MapsTo T U U) {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hdom : ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x) (k : ℕ) :
    ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T^[k] v x - T^[k] w x| ≤ (L ^ k *ᵥ fun y => |v y - w y|) x := by
  induction k with
  | zero => intro v _ w _ x; simp
  | succ k ih =>
    intro v hv w hw x
    rw [iterate_succ_apply', iterate_succ_apply']
    refine (hdom _ (hT.iterate k hv) _ (hT.iterate k hw) x).trans ?_
    have h1 := mulVec_le_mulVec_of_nonneg hL (fun y => ih v hv w hw y) x
    rw [mulVec_mulVec, ← pow_succ'] at h1
    exact h1

/-- **Proposition 6.1.6** (p. 191): if `T` maps `U` into itself and `|Tv − Tw| ≤ L|v − w|` for a
positive linear `L` with `ρ(L) < 1`, then some `Tᵏ` is a contraction on `U` under the supremum norm,
with modulus `‖Lᵏ‖ < 1`. -/
theorem exists_isContractionOn_iterate_of_abs_sub_le {T : (X → ℝ) → (X → ℝ)}
    {U : Set (X → ℝ)} (hT : Set.MapsTo T U U) {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hρ : specRad L < 1)
    (hdom : ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x) :
    ∃ k : ℕ, 0 < k ∧ IsContractionOn (T^[k]) U ‖L ^ k‖ := by
  obtain ⟨k, hk1, hk0⟩ := (((tendsto_norm_pow_zero L hρ).eventually (gt_mem_nhds one_pos)).and
    (eventually_gt_atTop 0)).exists
  refine ⟨k, hk0, hT.iterate k, norm_nonneg _, hk1, fun v hv w hw => ?_⟩
  have hLk := pow_nonneg_entries hL k
  calc ‖T^[k] v - T^[k] w‖ ≤ ‖L ^ k *ᵥ fun y => |v y - w y|‖ :=
        norm_le_norm_of_abs_le_fun
          (fun x => sum_nonneg fun y _ => mul_nonneg (hLk x y) (abs_nonneg _))
          (abs_iterate_sub_le_pow_mulVec hT hL hdom k v hv w hw)
    _ ≤ ‖L ^ k‖ * ‖fun y => |v y - w y|‖ := Matrix.linfty_opNorm_mulVec _ _
    _ = ‖L ^ k‖ * ‖v - w‖ := by
        rw [show (fun y => |v y - w y|) = fun y => |(v - w) y| from rfl, norm_abs_fun]

omit [DecidableEq X] in
/-- Proposition 6.1.6 with Theorem 6.1.5: under (6.13) on a closed `U`, `T` is globally stable on
`U`. -/
theorem globallyStable_of_abs_sub_le {T : (X → ℝ) → (X → ℝ)} {U : Set (X → ℝ)}
    (hU : IsClosed U) (hne : U.Nonempty) (hT : Set.MapsTo T U U) {L : Matrix X X ℝ}
    (hL : ∀ x x', 0 ≤ L x x') (hρ : specRad L < 1)
    (hdom : ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x) :
    ∃ u' ∈ U, IsFixedPt T u' ∧ (∀ v ∈ U, IsFixedPt T v → v = u') ∧
      ∀ u ∈ U, Tendsto (fun n : ℕ => T^[n] u) atTop (𝓝 u') := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_of_abs_sub_le hT hL hρ hdom
  exact globallyStable_of_iterate_contraction hU hne hT hk hc

end SargentStachurski.AbstractDynamicProgramming
