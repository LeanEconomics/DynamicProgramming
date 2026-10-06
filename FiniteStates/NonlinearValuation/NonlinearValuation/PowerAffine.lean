/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NonlinearValuation.OneDimensional
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# A power-transformed affine equation

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.1.3 (pp. 218–219).

For `A ≥ 0` irreducible, `h ≫ 0` and `θ ≠ 0`, the map (7.2)
`Gv = [h + (Av)^{1/θ}]^θ` on `V = (0, ∞)^X`.

* Exercise 7.1.7: `F(t) = (h + t^{1/θ})^θ` is increasing on `(0, ∞)`, convex for
  `θ ∈ (0, 1]` and concave otherwise. Its derivative simplifies to
  `F'(t) = (1 + h t^{−1/θ})^{θ−1}`, whose monotonicity in each case gives the shape.
* Exercise 7.1.8: `G` is an order-preserving self-map of `V`, convex for
  `θ ∈ (0, 1]` and concave otherwise.
* Theorem 7.1.4: `ρ(A)^{1/θ} < 1` iff `G` is globally stable on `V`, and when
  `ρ(A)^{1/θ} ≥ 1`, `G` has no fixed point in `V`. Necessity pairs a fixed point with
  the positive left Perron–Frobenius eigenvector. Sufficiency, which the book
  proves in Stachurski et al. (2022), is proved here with Du's theorem on order
  intervals `[ce, Ce]` around any finite set of points, `e ≫ 0` the right
  Perron–Frobenius eigenvector: `G(se) ≫ se` for small `s` and `G(se) ≪ se` for large
  `s`, so `G` is a convex or concave self-map of each such interval satisfying
  Du's strict condition.
* Exercise 7.1.9: the consumption rate equation of Kleinman et al. (2023) has a
  unique positive Markov solution iff `ρ(A)^ψ < 1`.
-/

open Matrix Finset Filter Topology Function Set

namespace SargentStachurski.NonlinearValuation

/-! ### The positive cone -/

/-- The interior `(0, ∞)^X` of the positive cone of `ℝ^X`. -/
def posCone (X : Type*) : Set (X → ℝ) := {v | ∀ x, 0 < v x}

variable {X : Type*}

theorem convex_posCone : Convex ℝ (posCone X) := by
  intro u hu w hw a b ha hb hab x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hu' := hu x
  have hw' := hw x
  have hm := lt_min hu' hw'
  nlinarith [mul_le_mul_of_nonneg_left (min_le_left (u x) (w x)) ha,
    mul_le_mul_of_nonneg_left (min_le_right (u x) (w x)) hb]

variable [Fintype X] [DecidableEq X]

/-- An irreducible matrix has a positive entry in every row. -/
theorem Irreducible.exists_pos_row {A : Matrix X X ℝ} (hA : Irreducible A) (x : X) :
    ∃ x', 0 < A x x' := by
  obtain ⟨k, hk, hpos⟩ := hA.2 x x
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ', Matrix.mul_apply] at hpos
  by_contra hcon
  have : ∑ y, A x y * (A ^ j) y x ≤ 0 := sum_nonpos fun y _ => by
    have h1 : A x y ≤ 0 := not_lt.1 fun h => hcon ⟨y, h⟩
    rw [le_antisymm h1 (hA.1 x y), zero_mul]
  linarith

omit [DecidableEq X] in
/-- `Av ≫ 0` for `v ≫ 0` when every row of `A ≥ 0` has a positive entry. -/
theorem mulVec_pos_of_row {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x')
    (hrow : ∀ x, ∃ x', 0 < A x x') {v : X → ℝ} (hv : v ∈ posCone X) (x : X) :
    0 < (A *ᵥ v) x := by
  obtain ⟨x', hx'⟩ := hrow x
  calc 0 < A x x' * v x' := mul_pos hx' (hv x')
    _ ≤ ∑ y, A x y * v y :=
        single_le_sum (fun y _ => mul_nonneg (hA x y) (hv y).le) (mem_univ x')

/-- Multiplying the entries of an irreducible matrix by positive numbers preserves
irreducibility. -/
theorem Irreducible.of_pos_mul {P : Matrix X X ℝ} (hP : Irreducible P) {c : X → X → ℝ}
    (hc : ∀ x x', 0 < c x x') : Irreducible (Matrix.of fun x x' => c x x' * P x x') := by
  set B : Matrix X X ℝ := Matrix.of fun x x' => c x x' * P x x' with hB
  have hB0 : ∀ x x', 0 ≤ B x x' := fun x x' => mul_nonneg (hc x x').le (hP.1 x x')
  have key : ∀ k x x', 0 < (P ^ k) x x' → 0 < (B ^ k) x x' := by
    intro k
    induction k with
    | zero => intro x x' h; simpa using h
    | succ k ih =>
      intro x x' h
      rw [pow_succ', Matrix.mul_apply] at h ⊢
      obtain ⟨y, hy⟩ : ∃ y, 0 < P x y * (P ^ k) y x' := by
        by_contra hcon
        have : ∑ y, P x y * (P ^ k) y x' ≤ 0 :=
          sum_nonpos fun y _ => not_lt.1 fun h' => hcon ⟨y, h'⟩
        linarith
      have hPxy : 0 < P x y := by
        rcases (hP.1 x y).lt_or_eq with h1 | h1
        · exact h1
        · rw [← h1, zero_mul] at hy; exact absurd hy (lt_irrefl 0)
      have hPk : 0 < (P ^ k) y x' := by
        rcases (pow_nonneg_entries hP.1 k y x').lt_or_eq with h1 | h1
        · exact h1
        · rw [← h1, mul_zero] at hy; exact absurd hy (lt_irrefl 0)
      calc 0 < B x y * (B ^ k) y x' := mul_pos (mul_pos (hc x y) hPxy) (ih y x' hPk)
        _ ≤ ∑ z, B x z * (B ^ k) z x' :=
            single_le_sum (fun z _ => mul_nonneg (hB0 x z) (pow_nonneg_entries hB0 k z x'))
              (mem_univ y)
  exact ⟨hB0, fun x x' => by
    obtain ⟨k, hk, hpos⟩ := hP.2 x x'
    exact ⟨k, hk, key k x x' hpos⟩⟩

/-! ### Exercise 7.1.7: the scalar map `F(t) = (h + t^{1/θ})^θ` -/

/-- The scalar map `F(t) = (h + t^{1/θ})^θ` of Exercise 7.1.7. -/
noncomputable def powF (h θ t : ℝ) : ℝ := (h + t ^ θ⁻¹) ^ θ

omit [Fintype X] [DecidableEq X] in
theorem powF_pos {h θ t : ℝ} (hh : 0 ≤ h) (ht : 0 < t) : 0 < powF h θ t :=
  Real.rpow_pos_of_pos (add_pos_of_nonneg_of_pos hh (Real.rpow_pos_of_pos ht _)) _

omit [Fintype X] [DecidableEq X] in
/-- Exercise 7.1.7 (p. 218): `F` is increasing on `(0, ∞)`. -/
theorem powF_monotoneOn {h θ : ℝ} (hh : 0 ≤ h) (hθ : θ ≠ 0) : MonotoneOn (powF h θ) (Ioi 0) := by
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  have hbs : 0 < h + s ^ θ⁻¹ := add_pos_of_nonneg_of_pos hh (Real.rpow_pos_of_pos hs' _)
  unfold powF
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have hp : θ⁻¹ ≤ 0 := (inv_lt_zero.2 hneg).le
    have h1 : t ^ θ⁻¹ ≤ s ^ θ⁻¹ := Real.rpow_le_rpow_of_nonpos hs' hst hp
    have hbt : 0 < h + t ^ θ⁻¹ := add_pos_of_nonneg_of_pos hh (Real.rpow_pos_of_pos ht' _)
    exact Real.rpow_le_rpow_of_nonpos hbt (by linarith) hneg.le
  · have h1 : s ^ θ⁻¹ ≤ t ^ θ⁻¹ := Real.rpow_le_rpow hs'.le hst (inv_nonneg.2 hpos.le)
    exact Real.rpow_le_rpow hbs.le (by linarith) hpos.le

omit [Fintype X] [DecidableEq X] in
/-- The derivative of `F`: `F'(t) = (1 + h t^{−1/θ})^{θ−1}` for `t > 0`. -/
theorem hasDerivAt_powF {h θ t : ℝ} (hh : 0 ≤ h) (hθ : θ ≠ 0) (ht : 0 < t) :
    HasDerivAt (powF h θ) ((1 + h * t ^ (-θ⁻¹)) ^ (θ - 1)) t := by
  have htp : 0 < t ^ θ⁻¹ := Real.rpow_pos_of_pos ht _
  have htn : 0 < t ^ (-θ⁻¹) := Real.rpow_pos_of_pos ht _
  have hB : 0 < 1 + h * t ^ (-θ⁻¹) := by positivity
  have hbase : 0 < h + t ^ θ⁻¹ := add_pos_of_nonneg_of_pos hh htp
  have h1 : HasDerivAt (fun t => h + t ^ θ⁻¹) (θ⁻¹ * t ^ (θ⁻¹ - 1)) t :=
    (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_add h
  have h2 := h1.rpow_const (p := θ) (Or.inl hbase.ne')
  have hF : powF h θ = fun y => (h + y ^ θ⁻¹) ^ θ := rfl
  rw [hF]
  convert h2 using 1
  have e1 : h + t ^ θ⁻¹ = t ^ θ⁻¹ * (1 + h * t ^ (-θ⁻¹)) := by
    rw [Real.rpow_neg ht.le]
    field_simp
    ring
  have e2 : (t ^ θ⁻¹ * (1 + h * t ^ (-θ⁻¹))) ^ (θ - 1) =
      t ^ (θ⁻¹ * (θ - 1)) * (1 + h * t ^ (-θ⁻¹)) ^ (θ - 1) := by
    rw [Real.mul_rpow htp.le hB.le, ← Real.rpow_mul ht.le]
  have e3 : θ⁻¹ * (θ - 1) = 1 - θ⁻¹ := by field_simp
  have e4 : t ^ (θ⁻¹ - 1) * t ^ (1 - θ⁻¹) = 1 := by
    rw [← Real.rpow_add ht]
    simp
  have e5 : θ⁻¹ * θ = 1 := inv_mul_cancel₀ hθ
  rw [e1, e2, e3]
  calc (1 + h * t ^ (-θ⁻¹)) ^ (θ - 1)
      = (θ⁻¹ * θ) * (t ^ (θ⁻¹ - 1) * t ^ (1 - θ⁻¹)) * (1 + h * t ^ (-θ⁻¹)) ^ (θ - 1) := by
        rw [e5, e4]; ring
    _ = θ⁻¹ * t ^ (θ⁻¹ - 1) * θ * (t ^ (1 - θ⁻¹) * (1 + h * t ^ (-θ⁻¹)) ^ (θ - 1)) := by ring

omit [Fintype X] [DecidableEq X] in
theorem continuousOn_powF {h θ : ℝ} (hh : 0 ≤ h) (hθ : θ ≠ 0) :
    ContinuousOn (powF h θ) (Ioi 0) :=
  fun _ ht => (hasDerivAt_powF hh hθ ht).continuousAt.continuousWithinAt

omit [Fintype X] [DecidableEq X] in
theorem differentiableOn_powF {h θ : ℝ} (hh : 0 ≤ h) (hθ : θ ≠ 0) :
    DifferentiableOn ℝ (powF h θ) (interior (Ioi 0)) := by
  rw [interior_Ioi]
  exact fun _ ht => (hasDerivAt_powF hh hθ ht).differentiableAt.differentiableWithinAt

omit [Fintype X] [DecidableEq X] in
/-- Exercise 7.1.7 (i) (p. 218): `F` is convex on `(0, ∞)` when `θ ∈ (0, 1]`. -/
theorem convexOn_powF {h θ : ℝ} (hh : 0 ≤ h) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ConvexOn ℝ (Ioi 0) (powF h θ) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0) (continuousOn_powF hh hθ0.ne')
    (differentiableOn_powF hh hθ0.ne') ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  rw [(hasDerivAt_powF hh hθ0.ne' hs').deriv, (hasDerivAt_powF hh hθ0.ne' ht').deriv]
  have h1 : t ^ (-θ⁻¹) ≤ s ^ (-θ⁻¹) :=
    Real.rpow_le_rpow_of_nonpos hs' hst (by have := inv_pos.2 hθ0; linarith)
  have hBt : 0 < 1 + h * t ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos ht' (-θ⁻¹); positivity
  exact Real.rpow_le_rpow_of_nonpos hBt (by nlinarith) (by linarith)

omit [Fintype X] [DecidableEq X] in
/-- Exercise 7.1.7 (ii) (p. 218): `F` is concave on `(0, ∞)` when `θ > 1` or `θ < 0`. -/
theorem concaveOn_powF {h θ : ℝ} (hh : 0 ≤ h) (hθ : θ ≠ 0) (hθ1 : ¬ (0 < θ ∧ θ ≤ 1)) :
    ConcaveOn ℝ (Ioi 0) (powF h θ) := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) (continuousOn_powF hh hθ)
    (differentiableOn_powF hh hθ) ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  rw [(hasDerivAt_powF hh hθ hs').deriv, (hasDerivAt_powF hh hθ ht').deriv]
  have hBs : 0 < 1 + h * s ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos hs' (-θ⁻¹); positivity
  have hBt : 0 < 1 + h * t ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos ht' (-θ⁻¹); positivity
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · -- `θ < 0`: `B` increasing, exponent `θ − 1 < 0`
    have h1 : s ^ (-θ⁻¹) ≤ t ^ (-θ⁻¹) :=
      Real.rpow_le_rpow hs'.le hst (by have := inv_lt_zero.2 hneg; linarith)
    exact Real.rpow_le_rpow_of_nonpos hBs (by nlinarith) (by linarith)
  · -- `θ > 1`: `B` decreasing, exponent `θ − 1 > 0`
    have hθ1' : 1 < θ := by
      by_contra hle
      exact hθ1 ⟨hpos, not_lt.1 hle⟩
    have h1 : t ^ (-θ⁻¹) ≤ s ^ (-θ⁻¹) :=
      Real.rpow_le_rpow_of_nonpos hs' hst (by have := inv_pos.2 hpos; linarith)
    exact Real.rpow_le_rpow hBt.le (by nlinarith) (by linarith)

/-! ### Exercise 7.1.8: the map `G` -/

/-- The map (7.2): `(Gv)(x) = [h(x) + (Av)(x)^{1/θ}]^θ`. -/
noncomputable def powG (A : Matrix X X ℝ) (h : X → ℝ) (θ : ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => powF (h x) θ ((A *ᵥ v) x)

omit [DecidableEq X] in
theorem powG_apply (A : Matrix X X ℝ) (h : X → ℝ) (θ : ℝ) (v : X → ℝ) (x : X) :
    powG A h θ v x = (h x + (A *ᵥ v) x ^ θ⁻¹) ^ θ := by
  classical
  exact rfl

omit [DecidableEq X] in
/-- Exercise 7.1.8 (p. 219): `G` maps `V = (0, ∞)^X` into itself. -/
theorem powG_mapsTo {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x') (hrow : ∀ x, ∃ x', 0 < A x x')
    {h : X → ℝ} (hh : ∀ x, 0 ≤ h x) (θ : ℝ) : MapsTo (powG A h θ) (posCone X) (posCone X) :=
  fun _ hv x => powF_pos (hh x) (mulVec_pos_of_row hA hrow hv x)

omit [DecidableEq X] in
/-- Exercise 7.1.8 (p. 219): `G` is order preserving on `V`. -/
theorem powG_monotoneOn {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x')
    (hrow : ∀ x, ∃ x', 0 < A x x') {h : X → ℝ} (hh : ∀ x, 0 ≤ h x) {θ : ℝ} (hθ : θ ≠ 0) :
    MonotoneOn (powG A h θ) (posCone X) := by
  intro u hu w hw huw x
  exact powF_monotoneOn (hh x) hθ (mulVec_pos_of_row hA hrow hu x)
    (mulVec_pos_of_row hA hrow hw x)
    (sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (huw y) (hA x y))

omit [DecidableEq X] in
/-- Exercise 7.1.8 (p. 219): `G` is convex on `V` when `θ ∈ (0, 1]`. -/
theorem convexOn_powG {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x')
    (hrow : ∀ x, ∃ x', 0 < A x x') {h : X → ℝ} (hh : ∀ x, 0 ≤ h x) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) : ConvexOn ℝ (posCone X) (powG A h θ) := by
  refine ⟨convex_posCone, fun u hu w hw a b ha hb hab x => ?_⟩
  have := (convexOn_powF (hh x) hθ0 hθ1).2 (mulVec_pos_of_row hA hrow hu x)
    (mulVec_pos_of_row hA hrow hw x) ha hb hab
  simpa [powG, mulVec_add, mulVec_smul] using this

omit [DecidableEq X] in
/-- Exercise 7.1.8 (p. 219): `G` is concave on `V` when `θ > 1` or `θ < 0`. -/
theorem concaveOn_powG {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x')
    (hrow : ∀ x, ∃ x', 0 < A x x') {h : X → ℝ} (hh : ∀ x, 0 ≤ h x) {θ : ℝ} (hθ : θ ≠ 0)
    (hθ1 : ¬ (0 < θ ∧ θ ≤ 1)) : ConcaveOn ℝ (posCone X) (powG A h θ) := by
  refine ⟨convex_posCone, fun u hu w hw a b ha hb hab x => ?_⟩
  have := (concaveOn_powF (hh x) hθ hθ1).2 (mulVec_pos_of_row hA hrow hu x)
    (mulVec_pos_of_row hA hrow hw x) ha hb hab
  simpa [powG, mulVec_add, mulVec_smul] using this

/-! ### Theorem 7.1.4 -/

variable [Nonempty X]

/-- Theorem 7.1.4 (p. 218), necessity: if `G` has a fixed point in `V`, then `ρ(A)^{1/θ} < 1`.
With `ε ≫ 0` the left Perron–Frobenius eigenvector, `v = Gv` gives `v^{1/θ} = h + (Av)^{1/θ}`, so
`Av ≪ v` (`θ > 0`) or `Av ≫ v` (`θ < 0`), and pairing with `ε` gives `ρ(A) < 1` or `ρ(A) > 1`. -/
theorem specRad_rpow_lt_one_of_isFixedPt {A : Matrix X X ℝ} (hA : Irreducible A) {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) {v : X → ℝ} (hv : v ∈ posCone X)
    (hfix : IsFixedPt (powG A h θ) v) : specRad A ^ θ⁻¹ < 1 := by
  obtain ⟨ε, hε, hεA⟩ := hA.exists_pos_left_eigenvector
  have hρ := hA.specRad_pos
  have hAv := mulVec_pos_of_row hA.1 hA.exists_pos_row hv
  have key : ∀ x, (A *ᵥ v) x ^ θ⁻¹ < v x ^ θ⁻¹ := fun x => by
    have h1 : v x = (h x + (A *ᵥ v) x ^ θ⁻¹) ^ θ := (congrFun hfix x).symm
    have hb : 0 ≤ h x + (A *ᵥ v) x ^ θ⁻¹ :=
      add_nonneg (hh x).le (Real.rpow_nonneg (hAv x).le _)
    have h2 : v x ^ θ⁻¹ = h x + (A *ᵥ v) x ^ θ⁻¹ := by rw [h1, Real.rpow_rpow_inv hb hθ]
    linarith [hh x]
  have hpair : ε ⬝ᵥ (A *ᵥ v) = specRad A * (ε ⬝ᵥ v) := by
    rw [dotProduct_mulVec, hεA, smul_dotProduct, smul_eq_mul]
  have hεv : 0 < ε ⬝ᵥ v := sum_pos (fun x _ => mul_pos (hε x) (hv x)) univ_nonempty
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have hp : θ⁻¹ < 0 := inv_lt_zero.2 hneg
    have hlt : ∀ x, v x < (A *ᵥ v) x := fun x =>
      (Real.rpow_lt_rpow_iff_of_neg (hAv x) (hv x) hp).1 (key x)
    have h1 : ε ⬝ᵥ v < ε ⬝ᵥ (A *ᵥ v) :=
      sum_lt_sum_of_nonempty univ_nonempty fun x _ => mul_lt_mul_of_pos_left (hlt x) (hε x)
    have hρ1 : 1 < specRad A := by nlinarith
    exact Real.rpow_lt_one_of_one_lt_of_neg hρ1 hp
  · have hp : 0 < θ⁻¹ := inv_pos.2 hpos
    have hlt : ∀ x, (A *ᵥ v) x < v x := fun x =>
      (Real.rpow_lt_rpow_iff (hAv x).le (hv x).le hp).1 (key x)
    have h1 : ε ⬝ᵥ (A *ᵥ v) < ε ⬝ᵥ v :=
      sum_lt_sum_of_nonempty univ_nonempty fun x _ => mul_lt_mul_of_pos_left (hlt x) (hε x)
    have hρ1 : specRad A < 1 := by nlinarith
    exact Real.rpow_lt_one (specRad_nonneg A) hρ1 hp

/-- **Theorem 7.1.4** (p. 218): if `ρ(A)^{1/θ} ≥ 1`, then `G` has no fixed point in `V`. -/
theorem not_isFixedPt_powG {A : Matrix X X ℝ} (hA : Irreducible A) {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) (h1 : 1 ≤ specRad A ^ θ⁻¹) {v : X → ℝ}
    (hv : v ∈ posCone X) : ¬ IsFixedPt (powG A h θ) v := fun hfix =>
  absurd (specRad_rpow_lt_one_of_isFixedPt hA hh hθ hv hfix) (not_lt.2 h1)

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- The scalar comparison behind Theorem 7.1.4: with `r = ρ^{1/θ} < 1`, `K = h/(1 − r)` and `y > 0`,
`y < (h + r y^{1/θ})^θ` below `min(h^θ, K^θ)` and `(h + r y^{1/θ})^θ < y` above `max(h^θ, K^θ)`. -/
theorem scalar_bounds {h θ r y : ℝ} (hh : 0 < h) (hθ : θ ≠ 0) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hy : 0 < y) :
    (y < min (h ^ θ) ((h / (1 - r)) ^ θ) → y < (h + r * y ^ θ⁻¹) ^ θ) ∧
      (max (h ^ θ) ((h / (1 - r)) ^ θ) < y → (h + r * y ^ θ⁻¹) ^ θ < y) := by
  have hK : 0 < h / (1 - r) := div_pos hh (by linarith)
  have hyp : 0 < y ^ θ⁻¹ := Real.rpow_pos_of_pos hy _
  have hyinv : (y ^ θ⁻¹) ^ θ = y := Real.rpow_inv_rpow hy.le hθ
  have hhinv : (h ^ θ) ^ θ⁻¹ = h := Real.rpow_rpow_inv hh.le hθ
  have hKinv : ((h / (1 - r)) ^ θ) ^ θ⁻¹ = h / (1 - r) := Real.rpow_rpow_inv hK.le hθ
  have hb : 0 < h + r * y ^ θ⁻¹ := by positivity
  have hKy : ∀ z, h / (1 - r) < z → h + r * z < z := fun z hz => by
    rw [div_lt_iff₀ (by linarith)] at hz
    linarith
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have hp : θ⁻¹ < 0 := inv_lt_zero.2 hneg
    constructor
    · intro hlt
      have h1 : y < (h / (1 - r)) ^ θ := lt_of_lt_of_le hlt (min_le_right _ _)
      have h2 : h / (1 - r) < y ^ θ⁻¹ := by
        have := Real.rpow_lt_rpow_of_neg hy h1 hp
        rwa [hKinv] at this
      have h3 := Real.rpow_lt_rpow_of_neg hb (hKy _ h2) hneg
      rwa [hyinv] at h3
    · intro hlt
      have h1 : h ^ θ < y := lt_of_le_of_lt (le_max_left _ _) hlt
      have h2 : y ^ θ⁻¹ < h := by
        have := Real.rpow_lt_rpow_of_neg (Real.rpow_pos_of_pos hh θ) h1 hp
        rwa [hhinv] at this
      have h3 := Real.rpow_lt_rpow_of_neg hyp (by nlinarith : y ^ θ⁻¹ < h + r * y ^ θ⁻¹) hneg
      rwa [hyinv] at h3
  · have hp : 0 < θ⁻¹ := inv_pos.2 hpos
    constructor
    · intro hlt
      have h1 : y < h ^ θ := lt_of_lt_of_le hlt (min_le_left _ _)
      have h2 : y ^ θ⁻¹ < h := by
        have := Real.rpow_lt_rpow hy.le h1 hp
        rwa [hhinv] at this
      have h3 := Real.rpow_lt_rpow hyp.le (by nlinarith : y ^ θ⁻¹ < h + r * y ^ θ⁻¹) hpos
      rwa [hyinv] at h3
    · intro hlt
      have h1 : (h / (1 - r)) ^ θ < y := lt_of_le_of_lt (le_max_right _ _) hlt
      have h2 : h / (1 - r) < y ^ θ⁻¹ := by
        have := Real.rpow_lt_rpow (Real.rpow_pos_of_pos hK θ).le h1 hp
        rwa [hKinv] at this
      have h3 := Real.rpow_lt_rpow hb.le (hKy _ h2) hpos
      rwa [hyinv] at h3

omit [Nonempty X] [DecidableEq X] in
/-- `G(se)(x) = (h(x) + ρ^{1/θ}(s e(x))^{1/θ})^θ` for an eigenvector `Ae = ρe`. -/
theorem powG_smul_eigen {A : Matrix X X ℝ} {h : X → ℝ} {θ ρ : ℝ} (hρ : 0 ≤ ρ) {e : X → ℝ}
    (he0 : ∀ x, 0 ≤ e x) (he : A *ᵥ e = ρ • e) {s : ℝ} (hs : 0 ≤ s) (x : X) :
    powG A h θ (s • e) x = (h x + ρ ^ θ⁻¹ * (s * e x) ^ θ⁻¹) ^ θ := by
  classical
  rw [powG_apply, mulVec_smul, he]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show s * (ρ * e x) = ρ * (s * e x) by ring, Real.mul_rpow hρ (mul_nonneg hs (he0 x))]

omit [DecidableEq X] in
/-- Below a positive threshold, `se ≪ G(se)`; above another, `G(se) ≪ se`. -/
theorem exists_thresholds {A : Matrix X X ℝ} {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) (hρ1 : specRad A ^ θ⁻¹ < 1) {e : X → ℝ}
    (he0 : ∀ x, 0 < e x) (he : A *ᵥ e = specRad A • e) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ (∀ s, 0 < s → s < c₀ → ∀ x, (s • e) x < powG A h θ (s • e) x) ∧
      ∀ s, C₀ < s → ∀ x, powG A h θ (s • e) x < (s • e) x := by
  set r := specRad A ^ θ⁻¹ with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (specRad_nonneg A) _
  set m : X → ℝ := fun x => min (h x ^ θ) ((h x / (1 - r)) ^ θ) / e x with hm
  set M : X → ℝ := fun x => max (h x ^ θ) ((h x / (1 - r)) ^ θ) / e x with hM
  have hmpos : ∀ x, 0 < m x := fun x =>
    div_pos (lt_min (Real.rpow_pos_of_pos (hh x) _)
      (Real.rpow_pos_of_pos (div_pos (hh x) (by linarith)) _)) (he0 x)
  refine ⟨univ.inf' univ_nonempty m, univ.sup' univ_nonempty M, ?_, fun s hs hsc x => ?_,
    fun s hsC x => ?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun x _ => hmpos x
  · have hsx : s < m x := hsc.trans_le (Finset.inf'_le _ (mem_univ x))
    have hy : 0 < s * e x := mul_pos hs (he0 x)
    have h1 : s * e x < min (h x ^ θ) ((h x / (1 - r)) ^ θ) := by
      rwa [hm, lt_div_iff₀ (he0 x)] at hsx
    rw [powG_smul_eigen (specRad_nonneg A) (fun x => (he0 x).le) he hs.le x]
    exact (scalar_bounds (hh x) hθ hr0 hρ1 hy).1 h1
  · have hsx : M x < s := lt_of_le_of_lt (Finset.le_sup' _ (mem_univ x)) hsC
    have hM0 : 0 < M x := div_pos (lt_max_of_lt_left (Real.rpow_pos_of_pos (hh x) _)) (he0 x)
    have hs : 0 < s := hM0.trans hsx
    have hy : 0 < s * e x := mul_pos hs (he0 x)
    have h1 : max (h x ^ θ) ((h x / (1 - r)) ^ θ) < s * e x := by
      rwa [hM, div_lt_iff₀ (he0 x)] at hsx
    rw [powG_smul_eigen (specRad_nonneg A) (fun x => (he0 x).le) he hs.le x]
    exact (scalar_bounds (hh x) hθ hr0 hρ1 hy).2 h1

omit [Nonempty X] in
/-- On an order interval `[ce, Ce]` whose endpoints satisfy `ce ≪ G(ce)` and `G(Ce) ≪ Ce`, `G` is
globally stable, by Du's theorem. -/
theorem globallyStableOn_powG_Icc {A : Matrix X X ℝ} (hA : Irreducible A) {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) {e : X → ℝ} (he0 : ∀ x, 0 < e x) {c C : ℝ}
    (hc : 0 < c) (hcC : c • e ≤ C • e) (hlo : ∀ x, (c • e) x < powG A h θ (c • e) x)
    (hhi : ∀ x, powG A h θ (C • e) x < (C • e) x) :
    GloballyStableOn (powG A h θ) (Set.Icc (c • e) (C • e)) := by
  have hrow := hA.exists_pos_row
  have hh' : ∀ x, 0 ≤ h x := fun x => (hh x).le
  have hsub : Set.Icc (c • e) (C • e) ⊆ posCone X := fun z hz x =>
    lt_of_lt_of_le (by simpa using mul_pos hc (he0 x)) (hz.1 x)
  have hce : c • e ∈ posCone X := hsub ⟨le_rfl, hcC⟩
  have hCe : C • e ∈ posCone X := hsub ⟨hcC, le_rfl⟩
  have hmono := (powG_monotoneOn hA.1 hrow hh' hθ).mono hsub
  have hmaps : MapsTo (powG A h θ) (Set.Icc (c • e) (C • e)) (Set.Icc (c • e) (C • e)) := by
    intro z hz
    exact ⟨fun x => (hlo x).le.trans (powG_monotoneOn hA.1 hrow hh' hθ hce (hsub hz) hz.1 x),
      fun x => (powG_monotoneOn hA.1 hrow hh' hθ (hsub hz) hCe hz.2 x).trans (hhi x).le⟩
  by_cases hθc : 0 < θ ∧ θ ≤ 1
  · exact du_convex_of_lt hcC hmaps hmono
      ((convexOn_powG hA.1 hrow hh' hθc.1 hθc.2).subset hsub (convex_Icc _ _)) hhi
  · exact du_concave_of_lt hcC hmaps hmono
      ((concaveOn_powG hA.1 hrow hh' hθ hθc).subset hsub (convex_Icc _ _)) hlo

omit [DecidableEq X] in
/-- Any two points of `V` lie in a common interval `[ce, Ce]` with `ce ≪ G(ce)` and
`G(Ce) ≪ Ce`. -/
theorem exists_interval {A : Matrix X X ℝ} {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) (hρ1 : specRad A ^ θ⁻¹ < 1) {e : X → ℝ}
    (he0 : ∀ x, 0 < e x) (he : A *ᵥ e = specRad A • e) {v w : X → ℝ} (hv : v ∈ posCone X)
    (hw : w ∈ posCone X) :
    ∃ c C : ℝ, 0 < c ∧ c • e ≤ C • e ∧ (∀ x, (c • e) x < powG A h θ (c • e) x) ∧
      (∀ x, powG A h θ (C • e) x < (C • e) x) ∧ v ∈ Set.Icc (c • e) (C • e) ∧
      w ∈ Set.Icc (c • e) (C • e) := by
  obtain ⟨c₀, C₀, hc₀, hsmall, hlarge⟩ := exists_thresholds hh hθ hρ1 he0 he
  set lo : X → ℝ := fun x => min (v x) (w x) / e x with hlo
  set hi : X → ℝ := fun x => max (v x) (w x) / e x with hhi
  set c := min (c₀ / 2) (univ.inf' univ_nonempty lo) with hc
  set C := max (C₀ + 1) (univ.sup' univ_nonempty hi) with hC
  have hlopos : ∀ x, 0 < lo x := fun x => div_pos (lt_min (hv x) (hw x)) (he0 x)
  have hcpos : 0 < c :=
    lt_min (by linarith) ((Finset.lt_inf'_iff _).2 fun x _ => hlopos x)
  have hclo : ∀ x, c * e x ≤ min (v x) (w x) := fun x => by
    have : c ≤ lo x := (min_le_right _ _).trans (Finset.inf'_le _ (mem_univ x))
    rwa [hlo, le_div_iff₀ (he0 x)] at this
  have hChi : ∀ x, max (v x) (w x) ≤ C * e x := fun x => by
    have : hi x ≤ C := (Finset.le_sup' _ (mem_univ x)).trans (le_max_right _ _)
    rwa [hhi, div_le_iff₀ (he0 x)] at this
  have hvI : v ∈ Set.Icc (c • e) (C • e) := ⟨fun x => by
      simpa using (hclo x).trans (min_le_left _ _), fun x => by
      simpa using (le_max_left _ _).trans (hChi x)⟩
  have hwI : w ∈ Set.Icc (c • e) (C • e) := ⟨fun x => by
      simpa using (hclo x).trans (min_le_right _ _), fun x => by
      simpa using (le_max_right _ _).trans (hChi x)⟩
  exact ⟨c, C, hcpos, hvI.1.trans hvI.2,
    hsmall c hcpos (lt_of_le_of_lt (min_le_left _ _) (by linarith)),
    hlarge C (lt_of_lt_of_le (by linarith) (le_max_left _ _)), hvI, hwI⟩

/-- **Theorem 7.1.4** (p. 218), sufficiency: if `A ≥ 0` is irreducible, `h ≫ 0` and
`ρ(A)^{1/θ} < 1`, then `G` is globally stable on `V = (0, ∞)^X`. -/
theorem globallyStableOn_powG {A : Matrix X X ℝ} (hA : Irreducible A) {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) (hρ1 : specRad A ^ θ⁻¹ < 1) :
    GloballyStableOn (powG A h θ) (posCone X) := by
  obtain ⟨e, he0, he⟩ := hA.exists_pos_eigenvector
  have hepos : e ∈ posCone X := he0
  obtain ⟨c, C, hc, hcC, hlo, hhi, -, -⟩ := exists_interval hh hθ hρ1 he0 he hepos hepos
  obtain ⟨u, hu, hufix, -, -⟩ := globallyStableOn_powG_Icc hA hh hθ he0 hc hcC hlo hhi
  have hupos : u ∈ posCone X := fun x =>
    lt_of_lt_of_le (by simpa using mul_pos hc (he0 x)) (hu.1 x)
  refine ⟨u, hupos, hufix, fun w hw hwfix => ?_, fun v hv => ?_⟩
  · obtain ⟨c', C', hc', hcC', hlo', hhi', huI, hwI⟩ := exists_interval hh hθ hρ1 he0 he hupos hw
    obtain ⟨u', -, -, huniq, -⟩ := globallyStableOn_powG_Icc hA hh hθ he0 hc' hcC' hlo' hhi'
    rw [huniq w hwI hwfix, huniq u huI hufix]
  · obtain ⟨c', C', hc', hcC', hlo', hhi', hvI, huI⟩ := exists_interval hh hθ hρ1 he0 he hv hupos
    obtain ⟨u', -, -, huniq, hconv⟩ := globallyStableOn_powG_Icc hA hh hθ he0 hc' hcC' hlo' hhi'
    rw [huniq u huI hufix]
    exact hconv v hvI

/-- **Theorem 7.1.4** (p. 218): for `A ≥ 0` irreducible and `h ≫ 0`, `ρ(A)^{1/θ} < 1` iff `G` is
globally stable on `V`. -/
theorem globallyStableOn_powG_iff {A : Matrix X X ℝ} (hA : Irreducible A) {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) :
    specRad A ^ θ⁻¹ < 1 ↔ GloballyStableOn (powG A h θ) (posCone X) := by
  refine ⟨globallyStableOn_powG hA hh hθ, fun hst => ?_⟩
  obtain ⟨v, hv, hfix, -, -⟩ := hst
  exact specRad_rpow_lt_one_of_isFixedPt hA hh hθ hv hfix

/-! ### Exercise 7.1.9: a migration model with savings -/

/-- The operator of Exercise 7.1.9: `(Av)(x) = β ∑ f(x')^{(ψ−1)/ψ} v(x') P(x, x')`. -/
noncomputable def kleinmanA (β : ℝ) (f : X → ℝ) (ψ : ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => β * f x' ^ ((ψ - 1) / ψ) * P x x'

/-- Equation (7.3) in Markov form, `σₜ = σ(Xₜ)`, `Rₜ = f(Xₜ)`:
`σ(x)⁻¹ = 1 + β^ψ [∑ f(x')^{(ψ−1)/ψ} σ(x')^{−1/ψ} P(x, x')]^ψ`. -/
def IsKleinmanSol (β : ℝ) (f : X → ℝ) (ψ : ℝ) (P : Matrix X X ℝ) (σ : X → ℝ) : Prop :=
  ∀ x, (σ x)⁻¹ = 1 + β ^ ψ * (∑ x', f x' ^ ((ψ - 1) / ψ) * σ x' ^ (-ψ⁻¹) * P x x') ^ ψ

omit [Nonempty X] [DecidableEq X] in
/-- `σ ≫ 0` solves (7.3) iff `w = σ^{−1/ψ}` is a fixed point of `G` with `h = 1` and `θ = 1/ψ`. -/
theorem isKleinmanSol_iff {β : ℝ} (hβ : 0 < β) {f : X → ℝ} (hf : ∀ x, 0 < f x) {ψ : ℝ}
    (hψ : ψ ≠ 0) {P : Matrix X X ℝ} (hP : ∀ x x', 0 ≤ P x x') {σ : X → ℝ} (hσ : σ ∈ posCone X) :
    IsKleinmanSol β f ψ P σ ↔
      IsFixedPt (powG (kleinmanA β f ψ P) (fun _ => 1) ψ⁻¹) fun x => σ x ^ (-ψ⁻¹) := by
  classical
  have hwpos : ∀ x, 0 < σ x ^ (-ψ⁻¹) := fun x => Real.rpow_pos_of_pos (hσ x) _
  have hwψ : ∀ x, (σ x ^ (-ψ⁻¹)) ^ ψ = (σ x)⁻¹ := fun x => by
    rw [← Real.rpow_mul (hσ x).le, neg_mul, inv_mul_cancel₀ hψ, Real.rpow_neg_one]
  have hS0 : ∀ x, 0 ≤ ∑ x', f x' ^ ((ψ - 1) / ψ) * σ x' ^ (-ψ⁻¹) * P x x' := fun x =>
    sum_nonneg fun x' _ => mul_nonneg (mul_nonneg (Real.rpow_nonneg (hf x').le _)
      (Real.rpow_nonneg (hσ x').le _)) (hP x x')
  have hAw : ∀ x, (kleinmanA β f ψ P *ᵥ fun x => σ x ^ (-ψ⁻¹)) x =
      β * ∑ x', f x' ^ ((ψ - 1) / ψ) * σ x' ^ (-ψ⁻¹) * P x x' := fun x => by
    change ∑ x', kleinmanA β f ψ P x x' * σ x' ^ (-ψ⁻¹) = _
    rw [mul_sum]
    exact sum_congr rfl fun x' _ => by simp only [kleinmanA, Matrix.of_apply]; ring
  have hAwψ : ∀ x, (kleinmanA β f ψ P *ᵥ fun x => σ x ^ (-ψ⁻¹)) x ^ ψ =
      β ^ ψ * (∑ x', f x' ^ ((ψ - 1) / ψ) * σ x' ^ (-ψ⁻¹) * P x x') ^ ψ := fun x => by
    rw [hAw, Real.mul_rpow hβ.le (hS0 x)]
  constructor
  · intro hsol
    funext x
    rw [powG_apply, inv_inv, hAwψ x, ← hsol x, ← hwψ x, Real.rpow_rpow_inv (hwpos x).le hψ]
  · intro hfix x
    have h1 := congrFun hfix x
    rw [powG_apply, inv_inv, hAwψ x] at h1
    have hb : 0 ≤ 1 + β ^ ψ * (∑ x', f x' ^ ((ψ - 1) / ψ) * σ x' ^ (-ψ⁻¹) * P x x') ^ ψ :=
      add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg hβ.le _) (Real.rpow_nonneg (hS0 x) _))
    have h2 := congrArg (fun t => t ^ ψ) h1
    rw [Real.rpow_inv_rpow hb hψ, hwψ x] at h2
    exact h2.symm

/-- **Exercise 7.1.9** (p. 219): if `β > 0`, `ψ ≠ 0`, `f ≫ 0` and `P` is irreducible, then (7.3)
has a unique solution of the form `σₜ = σ(Xₜ)` with `σ ≫ 0` iff `ρ(A)^ψ < 1`. -/
theorem existsUnique_kleinmanSol_iff {β : ℝ} (hβ : 0 < β) {f : X → ℝ} (hf : ∀ x, 0 < f x)
    {ψ : ℝ} (hψ : ψ ≠ 0) {P : Matrix X X ℝ} (hP : Irreducible P) :
    (∃! σ, σ ∈ posCone X ∧ IsKleinmanSol β f ψ P σ) ↔ specRad (kleinmanA β f ψ P) ^ ψ < 1 := by
  have hA : Irreducible (kleinmanA β f ψ P) :=
    hP.of_pos_mul (c := fun _ x' => β * f x' ^ ((ψ - 1) / ψ))
      fun _ x' => mul_pos hβ (Real.rpow_pos_of_pos (hf x') _)
  have hψ' : ψ⁻¹ ≠ 0 := inv_ne_zero hψ
  have h1 : ∀ x : X, (0 : ℝ) < (fun _ => (1 : ℝ)) x := fun _ => one_pos
  constructor
  · rintro ⟨σ, ⟨hσ, hsol⟩, -⟩
    have hwpos : (fun x => σ x ^ (-ψ⁻¹)) ∈ posCone X := fun x => Real.rpow_pos_of_pos (hσ x) _
    have := specRad_rpow_lt_one_of_isFixedPt hA h1 hψ' hwpos
      ((isKleinmanSol_iff hβ hf hψ hP.1 hσ).1 hsol)
    rwa [inv_inv] at this
  · intro hρ
    have hρ' : specRad (kleinmanA β f ψ P) ^ (ψ⁻¹)⁻¹ < 1 := by rwa [inv_inv]
    obtain ⟨w, hw, hwfix, hwuniq, -⟩ := globallyStableOn_powG hA h1 hψ' hρ'
    -- `σ = w^{−ψ}` and back
    have hback : ∀ x, (w x ^ (-ψ)) ^ (-ψ⁻¹) = w x := fun x => by
      rw [← Real.rpow_mul (hw x).le, neg_mul_neg, mul_inv_cancel₀ hψ, Real.rpow_one]
    have hσpos : (fun x => w x ^ (-ψ)) ∈ posCone X := fun x => Real.rpow_pos_of_pos (hw x) _
    refine ⟨fun x => w x ^ (-ψ), ⟨hσpos, ?_⟩, fun σ ⟨hσ, hsol⟩ => ?_⟩
    · rw [isKleinmanSol_iff hβ hf hψ hP.1 hσpos]
      convert hwfix using 1
      funext x
      exact hback x
    · have hwσ := hwuniq _ (fun x => Real.rpow_pos_of_pos (hσ x) _)
        ((isKleinmanSol_iff hβ hf hψ hP.1 hσ).1 hsol)
      funext x
      have := congrFun hwσ x
      rw [← this, ← Real.rpow_mul (hσ x).le, neg_mul_neg, inv_mul_cancel₀ hψ, Real.rpow_one]

end SargentStachurski.NonlinearValuation
