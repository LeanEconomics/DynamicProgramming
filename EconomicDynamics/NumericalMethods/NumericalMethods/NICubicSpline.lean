/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fin.VecNotation
import NumericalMethods.NISplines

/-!
# Cubic splines (Miao, §11.3.2, p. 361)

A cubic spline with nodes `x₀ < ⋯ < xₙ` is given by cubic pieces
`φ(x) = aᵢ + bᵢx + cᵢx² + dᵢx³` on `[xᵢ, xᵢ₊₁]` (`q : Fin n → Fin 4 → ℝ` holds the coefficients),
with (i) interpolation `φ(xᵢ) = yᵢ` and continuity, and (iii) continuity of `φ'` and `φ''` at the
interior nodes. These are `4n − 2` conditions for `4n` coefficients (`ni_cubic_condition_count`);
two end conditions are added:

* natural: `φ''(x₀) = φ''(xₙ) = 0`;
* Hermite (clamped): `φ'(x₀) = f'(x₀)`, `φ'(xₙ) = f'(xₙ)`;
* not-a-knot: `φ'''` continuous at `x₁` and at `xₙ₋₁`.

Main results (existence and uniqueness of the cubic spline for every data set):
`ni_natural_spline_existsUnique` (`n ≥ 1`), `ni_clamped_spline_existsUnique` (`n ≥ 1`),
`ni_notAKnot_spline_existsUnique` (`n ≥ 3`), and `ni_notAKnot_not_unique_two` (for `n = 2`
the not-a-knot conditions do not determine the spline). The proofs reduce, by the linear-algebra
lemma `ni_spline_existsUnique_of_homogeneous`, to the homogeneous problem, which is settled by the
second-derivative ("moment") equations `hᵢ₋₁Mᵢ₋₁ + 2(hᵢ₋₁ + hᵢ)Mᵢ + hᵢMᵢ₊₁ = 0` and a maximum
principle (diagonal dominance).

The pieces are recorded by their coefficients, as in the book's (ii); the one-sided limits of (iii)
are the values of the two adjacent pieces at the node.
-/

namespace Miao.NumericalMethods

/-- The cubic piece `q₀ + q₁t + q₂t² + q₃t³`. -/
def ni_cub (q : Fin 4 → ℝ) (t : ℝ) : ℝ := q 0 + q 1 * t + q 2 * t ^ 2 + q 3 * t ^ 3

/-- Its first derivative. -/
def ni_cub1 (q : Fin 4 → ℝ) (t : ℝ) : ℝ := q 1 + 2 * q 2 * t + 3 * q 3 * t ^ 2

/-- Its second derivative. -/
def ni_cub2 (q : Fin 4 → ℝ) (t : ℝ) : ℝ := 2 * q 2 + 6 * q 3 * t

/-- Its third derivative. -/
def ni_cub3 (q : Fin 4 → ℝ) : ℝ := 6 * q 3

theorem ni_hasDerivAt_cub (q : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (ni_cub q) (ni_cub1 q t) t := by
  unfold ni_cub ni_cub1
  have h := ((((hasDerivAt_const t (q 0)).add ((hasDerivAt_id t).const_mul (q 1))).add
    ((hasDerivAt_pow 2 t).const_mul (q 2))).add ((hasDerivAt_pow 3 t).const_mul (q 3)))
  convert h using 1
  · funext y
    simp only [Pi.add_apply, id]
  · norm_num
    ring

theorem ni_hasDerivAt_cub1 (q : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (ni_cub1 q) (ni_cub2 q t) t := by
  unfold ni_cub1 ni_cub2
  have h := (((hasDerivAt_const t (q 1)).add ((hasDerivAt_id t).const_mul (2 * q 2))).add
    ((hasDerivAt_pow 2 t).const_mul (3 * q 3)))
  convert h using 1
  · funext y
    simp only [Pi.add_apply, id]
  · norm_num
    ring

theorem ni_hasDerivAt_cub2 (q : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (ni_cub2 q) (ni_cub3 q) t := by
  unfold ni_cub2 ni_cub3
  have h := (hasDerivAt_const t (2 * q 2)).add ((hasDerivAt_id t).const_mul (6 * q 3))
  convert h using 1
  · funext y
    simp only [Pi.add_apply, id]
  · ring

/-- Miao, p. 361: (i) and (iii) impose `(n + 1) + 3(n − 1) = 4n − 2` conditions on the `4n`
coefficients of (ii). -/
theorem ni_cubic_condition_count (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (Fin (n + 1) ⊕ Fin (n - 1) × Fin 3) = 4 * n - 2 ∧
      Fintype.card (Fin n × Fin 4) = 4 * n := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

/-- The `i`th piece (zero for `i ≥ n`). -/
def ni_piece {n : ℕ} (q : Fin n → Fin 4 → ℝ) (i : ℕ) : Fin 4 → ℝ :=
  if h : i < n then q ⟨i, h⟩ else 0

/-- (i): interpolation, `φ(xᵢ) = yᵢ` and `φ(xᵢ₊₁) = yᵢ₊₁` on every piece (this includes the
continuity of `φ`). -/
def ni_CubicInterp {n : ℕ} (x y : ℕ → ℝ) (q : Fin n → Fin 4 → ℝ) : Prop :=
  ∀ i < n, ni_cub (ni_piece q i) (x i) = y i ∧ ni_cub (ni_piece q i) (x (i + 1)) = y (i + 1)

/-- (iii): continuity of `φ'` and `φ''` at the interior nodes. -/
def ni_CubicSmooth {n : ℕ} (x : ℕ → ℝ) (q : Fin n → Fin 4 → ℝ) : Prop :=
  ∀ j, 1 ≤ j → j < n →
    ni_cub1 (ni_piece q (j - 1)) (x j) = ni_cub1 (ni_piece q j) (x j) ∧
      ni_cub2 (ni_piece q (j - 1)) (x j) = ni_cub2 (ni_piece q j) (x j)

/-- The left side of the interpolation and smoothness conditions as a linear map. -/
def ni_splineL (n : ℕ) (x : ℕ → ℝ) :
    (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin n → Fin 2 → ℝ) × (Fin (n - 1) → Fin 2 → ℝ) where
  toFun q := (fun i r => ni_cub (q i) (x (i + r)), fun j r =>
    if r = 0 then ni_cub1 (ni_piece q j) (x (j + 1)) - ni_cub1 (ni_piece q (j + 1)) (x (j + 1))
    else ni_cub2 (ni_piece q j) (x (j + 1)) - ni_cub2 (ni_piece q (j + 1)) (x (j + 1)))
  map_add' q q' := by
    ext i r
    · simp only [Pi.add_apply, ni_cub, Prod.fst_add]
      ring
    · simp only [ni_piece, ni_cub1, ni_cub2, Prod.snd_add, Pi.add_apply]
      split_ifs <;> simp <;> ring
  map_smul' c q := by
    ext i r
    · simp only [Pi.smul_apply, ni_cub, smul_eq_mul, Prod.smul_fst, RingHom.id_apply]
      ring
    · simp only [ni_piece, ni_cub1, ni_cub2, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      split_ifs <;> simp <;> ring

/-- The right side for data `y`. -/
def ni_splineTarget (n : ℕ) (y : ℕ → ℝ) :
    (Fin n → Fin 2 → ℝ) × (Fin (n - 1) → Fin 2 → ℝ) :=
  (fun i r => y (i + r), fun _ _ => 0)

theorem ni_splineL_eq_iff {n : ℕ} (x y : ℕ → ℝ) (q : Fin n → Fin 4 → ℝ) :
    ni_splineL n x q = ni_splineTarget n y ↔ ni_CubicInterp x y q ∧ ni_CubicSmooth x q := by
  have hp : ∀ i (h : i < n), ni_piece q i = q ⟨i, h⟩ := fun i h => by simp [ni_piece, h]
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine ⟨fun i hi => ?_, fun j hj1 hj2 => ?_⟩
    · have a := congrFun (congrFun h1 ⟨i, hi⟩) 0
      have b := congrFun (congrFun h1 ⟨i, hi⟩) 1
      simp only [ni_splineL, ni_splineTarget, LinearMap.coe_mk, AddHom.coe_mk] at a b
      simp only [Fin.val_zero, add_zero, Fin.val_one] at a b
      rw [hp i hi]
      exact ⟨a, b⟩
    · have a := congrFun (congrFun h2 ⟨j - 1, by omega⟩) 0
      have b := congrFun (congrFun h2 ⟨j - 1, by omega⟩) 1
      simp only [ni_splineL, ni_splineTarget, LinearMap.coe_mk, AddHom.coe_mk] at a b
      have e : j - 1 + 1 = j := by omega
      simp only [ite_true, e, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false] at a b
      exact ⟨sub_eq_zero.mp a, sub_eq_zero.mp b⟩
  · rintro ⟨h1, h2⟩
    refine Prod.ext (funext fun i => funext fun r => ?_) (funext fun j => funext fun r => ?_)
    · simp only [ni_splineL, ni_splineTarget, LinearMap.coe_mk, AddHom.coe_mk]
      have := h1 i i.2
      rw [hp i i.2] at this
      fin_cases r
      · simpa using this.1
      · simpa using this.2
    · simp only [ni_splineL, ni_splineTarget, LinearMap.coe_mk, AddHom.coe_mk]
      have := h2 (j + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at this
      fin_cases r
      · simp [this.1]
      · simp [this.2]

/-- Linear algebra: if the homogeneous problem (zero data, zero end data) has only the zero
solution, then for all data and end data the spline exists and is unique. -/
theorem ni_spline_existsUnique_of_homogeneous {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ)
    (E : (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (hhom : ∀ q, ni_CubicInterp x (fun _ => 0) q → ni_CubicSmooth x q → E q = 0 → q = 0)
    (y : ℕ → ℝ) (e : Fin 2 → ℝ) :
    ∃! q : Fin n → Fin 4 → ℝ, ni_CubicInterp x y q ∧ ni_CubicSmooth x q ∧ E q = e := by
  set F := (ni_splineL n x).prod E
  have hF : ∀ q y e, F q = (ni_splineTarget n y, e) ↔
      ni_CubicInterp x y q ∧ ni_CubicSmooth x q ∧ E q = e := by
    intro q y e
    change (ni_splineL n x q, E q) = (ni_splineTarget n y, e) ↔ _
    rw [Prod.mk.injEq, ni_splineL_eq_iff, and_assoc]
  have hzero : ni_splineTarget n (fun _ => 0) = 0 := by
    simp only [ni_splineTarget]
    rfl
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    have : F q = (ni_splineTarget n (fun _ => 0), 0) := by
      rw [hq, hzero]
      rfl
    obtain ⟨h1, h2, h3⟩ := (hF q _ _).mp this
    exact hhom q h1 h2 h3
  have hdim : Module.finrank ℝ (Fin n → Fin 4 → ℝ) =
      Module.finrank ℝ (((Fin n → Fin 2 → ℝ) × (Fin (n - 1) → Fin 2 → ℝ)) × (Fin 2 → ℝ)) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hsurj : Function.Surjective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨q, hq⟩ := hsurj (ni_splineTarget n y, e)
  refine ⟨q, (hF q y e).mp hq, fun q' hq' => hinj ?_⟩
  rw [hq, (hF q' y e).mpr hq']

/-- Two cubic identities (Taylor expansion of a cubic): with `h = v − u`,
`φ(v) − φ(u) = h φ'(u) + h²(2φ''(u) + φ''(v))/6 = h φ'(v) − h²(φ''(u) + 2φ''(v))/6`. -/
theorem ni_cub_taylor (q : Fin 4 → ℝ) (u v : ℝ) :
    ni_cub q v - ni_cub q u =
        (v - u) * ni_cub1 q u + (v - u) ^ 2 * (2 * ni_cub2 q u + ni_cub2 q v) / 6 ∧
      ni_cub q v - ni_cub q u =
        (v - u) * ni_cub1 q v - (v - u) ^ 2 * (ni_cub2 q u + 2 * ni_cub2 q v) / 6 ∧
      ni_cub3 q * (v - u) = ni_cub2 q v - ni_cub2 q u := by
  unfold ni_cub ni_cub1 ni_cub2 ni_cub3
  refine ⟨by ring, by ring, by ring⟩

/-- The moments `Mᵢ = φ''(xᵢ)`, `i = 0, …, n`. -/
def ni_moment {n : ℕ} (x : ℕ → ℝ) (q : Fin n → Fin 4 → ℝ) (i : ℕ) : ℝ :=
  if i < n then ni_cub2 (ni_piece q i) (x i) else ni_cub2 (ni_piece q (n - 1)) (x n)

/-- The moment equations of the homogeneous problem. -/
theorem ni_moment_facts {n : ℕ} {x : ℕ → ℝ} (hx : StrictMono x) {q : Fin n → Fin 4 → ℝ}
    (hI : ni_CubicInterp x (fun _ => 0) q) (hS : ni_CubicSmooth x q) :
    (∀ i < n, ni_cub2 (ni_piece q i) (x (i + 1)) = ni_moment x q (i + 1)) ∧
    (∀ i < n, ni_cub2 (ni_piece q i) (x i) = ni_moment x q i) ∧
    (∀ i < n, 6 * ni_cub1 (ni_piece q i) (x i) =
      -(x (i + 1) - x i) * (2 * ni_moment x q i + ni_moment x q (i + 1))) ∧
    (∀ i < n, 6 * ni_cub1 (ni_piece q i) (x (i + 1)) =
      (x (i + 1) - x i) * (ni_moment x q i + 2 * ni_moment x q (i + 1))) ∧
    (∀ i < n, ni_cub3 (ni_piece q i) * (x (i + 1) - x i) =
      ni_moment x q (i + 1) - ni_moment x q i) ∧
    (∀ j, 1 ≤ j → j < n →
      (x j - x (j - 1)) * ni_moment x q (j - 1) +
        2 * ((x j - x (j - 1)) + (x (j + 1) - x j)) * ni_moment x q j +
          (x (j + 1) - x j) * ni_moment x q (j + 1) = 0) := by
  have hR : ∀ i < n, ni_cub2 (ni_piece q i) (x (i + 1)) = ni_moment x q (i + 1) := by
    intro i hi
    unfold ni_moment
    split_ifs with h
    · have := (hS (i + 1) (by omega) h).2
      simpa using this
    · have : i = n - 1 := by omega
      subst this
      rw [show n - 1 + 1 = n by omega]
  have hL : ∀ i < n, ni_cub2 (ni_piece q i) (x i) = ni_moment x q i := by
    intro i hi
    simp [ni_moment, hi]
  have hD0 : ∀ i < n, 6 * ni_cub1 (ni_piece q i) (x i) =
      -(x (i + 1) - x i) * (2 * ni_moment x q i + ni_moment x q (i + 1)) := by
    intro i hi
    have hh : x (i + 1) - x i ≠ 0 := (sub_pos.mpr (hx (Nat.lt_succ_self i))).ne'
    have t := (ni_cub_taylor (ni_piece q i) (x i) (x (i + 1))).1
    rw [(hI i hi).1, (hI i hi).2, hR i hi, hL i hi, sub_self] at t
    have : (x (i + 1) - x i) * (6 * ni_cub1 (ni_piece q i) (x i) +
        (x (i + 1) - x i) * (2 * ni_moment x q i + ni_moment x q (i + 1))) = 0 := by
      linear_combination (-6) * t
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hh
    · linarith
  have hD1 : ∀ i < n, 6 * ni_cub1 (ni_piece q i) (x (i + 1)) =
      (x (i + 1) - x i) * (ni_moment x q i + 2 * ni_moment x q (i + 1)) := by
    intro i hi
    have hh : x (i + 1) - x i ≠ 0 := (sub_pos.mpr (hx (Nat.lt_succ_self i))).ne'
    have t := (ni_cub_taylor (ni_piece q i) (x i) (x (i + 1))).2.1
    rw [(hI i hi).1, (hI i hi).2, hR i hi, hL i hi, sub_self] at t
    have : (x (i + 1) - x i) * (6 * ni_cub1 (ni_piece q i) (x (i + 1)) -
        (x (i + 1) - x i) * (ni_moment x q i + 2 * ni_moment x q (i + 1))) = 0 := by
      linear_combination (-6) * t
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hh
    · linarith
  refine ⟨hR, hL, hD0, hD1, fun i hi => ?_, fun j hj1 hj2 => ?_⟩
  · rw [(ni_cub_taylor (ni_piece q i) (x i) (x (i + 1))).2.2, hR i hi, hL i hi]
  · have e1 := (hS j hj1 hj2).1
    have a := hD1 (j - 1) (by omega)
    have b := hD0 j hj2
    have e : j - 1 + 1 = j := by omega
    rw [e] at a
    rw [e1] at a
    linear_combination b - a

/-- If all moments vanish (and the data are zero), all pieces vanish. -/
theorem ni_moments_zero {n : ℕ} {x : ℕ → ℝ} (hx : StrictMono x) {q : Fin n → Fin 4 → ℝ}
    (hI : ni_CubicInterp x (fun _ => 0) q) (hS : ni_CubicSmooth x q)
    (hM : ∀ i ≤ n, ni_moment x q i = 0) : q = 0 := by
  obtain ⟨hR, hL, -, -, -, -⟩ := ni_moment_facts hx hI hS
  funext i r
  have hi := i.2
  have hp : ni_piece q i = q i := by simp [ni_piece, hi]
  have h2u := hL i hi
  have h2v := hR i hi
  have h0u := (hI i hi).1
  have h0v := (hI i hi).2
  rw [hp, hM i hi.le] at h2u
  rw [hp, hM (i + 1) hi] at h2v
  rw [hp] at h0u h0v
  have hlt : x i < x (i + 1) := hx (Nat.lt_succ_self _)
  have hne : x (i + 1) - x i ≠ 0 := (sub_pos.mpr hlt).ne'
  unfold ni_cub2 at h2u h2v
  unfold ni_cub at h0u h0v
  have q3 : q i 3 = 0 := by
    have : (x (i + 1) - x i) * (6 * q i 3) = 0 := by linear_combination h2v - h2u
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · linarith
  have q2 : q i 2 = 0 := by rw [q3] at h2u; linarith
  have q1 : q i 1 = 0 := by
    have : (x (i + 1) - x i) * q i 1 = 0 := by
      rw [q3, q2] at h0u h0v
      linear_combination h0v - h0u
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · exact h
  have q0 : q i 0 = 0 := by rw [q3, q2, q1] at h0u; linarith
  fin_cases r <;> simp [q0, q1, q2, q3]

/-- Interior maximum principle for the moment equations. -/
theorem ni_moment_interior {M h₁ h₂ m : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) {a b : ℝ}
    (hrow : h₁ * a + 2 * (h₁ + h₂) * m + h₂ * b = 0) (ha : |a| ≤ |m|) (hb : |b| ≤ |m|)
    (hmax : |m| = M) : M = 0 := by
  have h1 : 2 * (h₁ + h₂) * |m| ≤ h₁ * |a| + h₂ * |b| := by
    have e : 2 * (h₁ + h₂) * m = -(h₁ * a + h₂ * b) := by linarith
    calc 2 * (h₁ + h₂) * |m| = |2 * (h₁ + h₂) * m| := by
          rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 * (h₁ + h₂) by positivity)]
      _ = |h₁ * a + h₂ * b| := by rw [e, abs_neg]
      _ ≤ |h₁ * a| + |h₂ * b| := abs_add_le _ _
      _ = h₁ * |a| + h₂ * |b| := by rw [abs_mul, abs_mul, abs_of_pos hh₁, abs_of_pos hh₂]
  have : (h₁ + h₂) * |m| ≤ 0 := by nlinarith
  have hm : |m| ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < (h₁ + h₂) * |m| := mul_pos (by positivity) hc
    linarith
  rw [← hmax]
  exact le_antisymm hm (abs_nonneg _)

/-- The natural end conditions `φ''(x₀) = φ''(xₙ) = 0` as a linear map. -/
def ni_naturalE (n : ℕ) (x : ℕ → ℝ) : (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun q := ![ni_cub2 (ni_piece q 0) (x 0), ni_cub2 (ni_piece q (n - 1)) (x n)]
  map_add' q q' := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub2] <;> split_ifs <;> simp <;> ring
  map_smul' c q := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub2] <;> split_ifs <;> simp <;> ring

/-- Uniqueness for the homogeneous natural spline. -/
theorem ni_natural_homogeneous {n : ℕ} (hn : 1 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (q : Fin n → Fin 4 → ℝ) (hI : ni_CubicInterp x (fun _ => 0) q) (hS : ni_CubicSmooth x q)
    (hE : ni_naturalE n x q = 0) : q = 0 := by
  obtain ⟨hR, hL, -, -, -, hrow⟩ := ni_moment_facts hx hI hS
  have hE0 := congrFun hE 0
  have hE1 := congrFun hE 1
  simp only [ni_naturalE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply] at hE0 hE1
  have hM0 : ni_moment x q 0 = 0 := by rw [← hL 0 hn]; exact hE0
  have hMn : ni_moment x q n = 0 := by simp [ni_moment, hE1]
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun i => |ni_moment x q i|) ⟨0, by simp⟩
  have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
  have hzero : |ni_moment x q j| = 0 := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [hM0, abs_zero]
    rcases lt_or_eq_of_le hj' with hjn | rfl
    · exact ni_moment_interior (sub_pos.mpr (hx (by omega)))
        (sub_pos.mpr (hx (Nat.lt_succ_self j))) (hrow j hjpos hjn)
        (hmax (j - 1) (Finset.mem_range.mpr (by omega)))
        (hmax (j + 1) (Finset.mem_range.mpr (by omega))) rfl
    · rw [hMn, abs_zero]
  apply ni_moments_zero hx hI hS
  intro i hi
  have := hmax i (Finset.mem_range.mpr (by omega))
  rw [hzero] at this
  exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))

/-- Miao, p. 361 (natural cubic spline): for strictly increasing nodes `x₀ < ⋯ < xₙ`, `n ≥ 1`, and
any data `y`, there is exactly one cubic spline with `φ(xᵢ) = yᵢ` and `φ''(x₀) = φ''(xₙ) = 0`. -/
theorem ni_natural_spline_existsUnique {n : ℕ} (hn : 1 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (y : ℕ → ℝ) :
    ∃! q : Fin n → Fin 4 → ℝ, ni_CubicInterp x y q ∧ ni_CubicSmooth x q ∧
      ni_cub2 (ni_piece q 0) (x 0) = 0 ∧ ni_cub2 (ni_piece q (n - 1)) (x n) = 0 := by
  have h := ni_spline_existsUnique_of_homogeneous hn x (ni_naturalE n x)
    (ni_natural_homogeneous hn hx) y 0
  have hiff : ∀ q, ni_naturalE n x q = 0 ↔
      ni_cub2 (ni_piece q 0) (x 0) = 0 ∧ ni_cub2 (ni_piece q (n - 1)) (x n) = 0 := by
    intro q
    constructor
    · intro hq
      have a := congrFun hq 0
      have b := congrFun hq 1
      simp only [ni_naturalE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Pi.zero_apply] at a b
      exact ⟨a, b⟩
    · rintro ⟨a, b⟩
      ext r
      fin_cases r <;> simp [ni_naturalE, a, b]
  simpa only [hiff] using h

/-- The clamped (Hermite) end conditions `φ'(x₀)`, `φ'(xₙ)` as a linear map. -/
def ni_clampedE (n : ℕ) (x : ℕ → ℝ) : (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun q := ![ni_cub1 (ni_piece q 0) (x 0), ni_cub1 (ni_piece q (n - 1)) (x n)]
  map_add' q q' := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub1] <;> split_ifs <;> simp <;> ring
  map_smul' c q := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub1] <;> split_ifs <;> simp <;> ring

/-- Uniqueness for the homogeneous clamped spline. -/
theorem ni_clamped_homogeneous {n : ℕ} (hn : 1 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (q : Fin n → Fin 4 → ℝ) (hI : ni_CubicInterp x (fun _ => 0) q) (hS : ni_CubicSmooth x q)
    (hE : ni_clampedE n x q = 0) : q = 0 := by
  obtain ⟨-, -, hD0, hD1, -, hrow⟩ := ni_moment_facts hx hI hS
  have hE0 := congrFun hE 0
  have hE1 := congrFun hE 1
  simp only [ni_clampedE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply] at hE0 hE1
  have h0 : 2 * ni_moment x q 0 + ni_moment x q 1 = 0 := by
    have a := hD0 0 hn
    rw [hE0, mul_zero] at a
    have hh : 0 < x (0 + 1) - x 0 := sub_pos.mpr (hx (Nat.lt_succ_self 0))
    nlinarith
  have hnn : ni_moment x q (n - 1) + 2 * ni_moment x q n = 0 := by
    have a := hD1 (n - 1) (by omega)
    have e : n - 1 + 1 = n := by omega
    rw [e, hE1, mul_zero] at a
    have hh : 0 < x n - x (n - 1) := by
      have := hx (show n - 1 < n by omega)
      linarith
    nlinarith
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun i => |ni_moment x q i|) ⟨0, by simp⟩
  have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
  have hzero : |ni_moment x q j| = 0 := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have hb := hmax 1 (Finset.mem_range.mpr (by omega))
      have e : |ni_moment x q 1| = 2 * |ni_moment x q 0| := by
        rw [show ni_moment x q 1 = -(2 * ni_moment x q 0) by linarith, abs_neg, abs_mul,
          abs_two]
      linarith [abs_nonneg (ni_moment x q 0)]
    rcases lt_or_eq_of_le hj' with hjn | rfl
    · exact ni_moment_interior (sub_pos.mpr (hx (by omega)))
        (sub_pos.mpr (hx (Nat.lt_succ_self j))) (hrow j hjpos hjn)
        (hmax (j - 1) (Finset.mem_range.mpr (by omega)))
        (hmax (j + 1) (Finset.mem_range.mpr (by omega))) rfl
    · have hb := hmax (j - 1) (Finset.mem_range.mpr (by omega))
      have e : |ni_moment x q (j - 1)| = 2 * |ni_moment x q j| := by
        rw [show ni_moment x q (j - 1) = -(2 * ni_moment x q j) by linarith, abs_neg, abs_mul,
          abs_two]
      linarith [abs_nonneg (ni_moment x q j)]
  apply ni_moments_zero hx hI hS
  intro i hi
  have := hmax i (Finset.mem_range.mpr (by omega))
  rw [hzero] at this
  exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))

/-- Miao, p. 361 (Hermite or clamped cubic spline): for strictly increasing nodes, `n ≥ 1`, any
data `y` and any end slopes `s₀ = f'(x₀)`, `sₙ = f'(xₙ)`, there is exactly one cubic spline with
`φ(xᵢ) = yᵢ`, `φ'(x₀) = s₀` and `φ'(xₙ) = sₙ`. -/
theorem ni_clamped_spline_existsUnique {n : ℕ} (hn : 1 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (y : ℕ → ℝ) (s₀ sₙ : ℝ) :
    ∃! q : Fin n → Fin 4 → ℝ, ni_CubicInterp x y q ∧ ni_CubicSmooth x q ∧
      ni_cub1 (ni_piece q 0) (x 0) = s₀ ∧ ni_cub1 (ni_piece q (n - 1)) (x n) = sₙ := by
  have h := ni_spline_existsUnique_of_homogeneous hn x (ni_clampedE n x)
    (ni_clamped_homogeneous hn hx) y ![s₀, sₙ]
  have hiff : ∀ q, ni_clampedE n x q = ![s₀, sₙ] ↔
      ni_cub1 (ni_piece q 0) (x 0) = s₀ ∧ ni_cub1 (ni_piece q (n - 1)) (x n) = sₙ := by
    intro q
    constructor
    · intro hq
      have a := congrFun hq 0
      have b := congrFun hq 1
      simp only [ni_clampedE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one] at a b
      exact ⟨a, b⟩
    · rintro ⟨a, b⟩
      ext r
      fin_cases r <;> simp [ni_clampedE, a, b]
  simpa only [hiff] using h

/-- The not-a-knot end conditions (`φ'''` continuous at `x₁` and `xₙ₋₁`) as a linear map. -/
def ni_notAKnotE (n : ℕ) : (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun q := ![ni_cub3 (ni_piece q 0) - ni_cub3 (ni_piece q 1),
    ni_cub3 (ni_piece q (n - 2)) - ni_cub3 (ni_piece q (n - 1))]
  map_add' q q' := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub3] <;> split_ifs <;> simp <;> ring
  map_smul' c q := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub3] <;> split_ifs <;> simp <;> ring

/-- The first not-a-knot row after eliminating `M₀`:
`(h₀ + 2h₁)M₁ + (h₁ − h₀)M₂ = 0`. -/
theorem ni_notAKnot_row {h₀ h₁ M₀ M₁ M₂ : ℝ} (hh₀ : 0 < h₀) (hh₁ : 0 < h₁)
    (hrow : h₀ * M₀ + 2 * (h₀ + h₁) * M₁ + h₁ * M₂ = 0)
    (hknot : h₁ * (M₁ - M₀) = h₀ * (M₂ - M₁)) :
    (h₀ + 2 * h₁) * M₁ + (h₁ - h₀) * M₂ = 0 := by
  have : (h₀ + h₁) * ((h₀ + 2 * h₁) * M₁ + (h₁ - h₀) * M₂) = 0 := by
    linear_combination h₁ * hrow + h₀ * hknot
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact h

/-- Maximum principle at a not-a-knot end row. -/
theorem ni_notAKnot_end {h₀ h₁ M₁ M₂ : ℝ} (hh₀ : 0 < h₀) (hh₁ : 0 < h₁)
    (hrow : (h₀ + 2 * h₁) * M₁ + (h₁ - h₀) * M₂ = 0) (hb : |M₂| ≤ |M₁|) : |M₁| = 0 := by
  have e : (h₀ + 2 * h₁) * |M₁| = |h₁ - h₀| * |M₂| := by
    rw [← abs_of_pos (show 0 < h₀ + 2 * h₁ by linarith), ← abs_mul, ← abs_mul,
      show (h₀ + 2 * h₁) * M₁ = -((h₁ - h₀) * M₂) by linarith, abs_neg]
  have hlt : |h₁ - h₀| < h₀ + 2 * h₁ := by
    rw [abs_lt]; constructor <;> linarith
  have : (h₀ + 2 * h₁ - |h₁ - h₀|) * |M₁| ≤ 0 := by
    nlinarith [abs_nonneg (h₁ - h₀), abs_nonneg M₁]
  have hm : |M₁| ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < (h₀ + 2 * h₁ - |h₁ - h₀|) * |M₁| := mul_pos (by linarith) hc
    linarith
  exact le_antisymm hm (abs_nonneg _)

/-- Uniqueness for the homogeneous not-a-knot spline (`n ≥ 3`). -/
theorem ni_notAKnot_homogeneous {n : ℕ} (hn : 3 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (q : Fin n → Fin 4 → ℝ) (hI : ni_CubicInterp x (fun _ => 0) q) (hS : ni_CubicSmooth x q)
    (hE : ni_notAKnotE n q = 0) : q = 0 := by
  obtain ⟨-, -, -, -, hT, hrow⟩ := ni_moment_facts hx hI hS
  have hE0 := congrFun hE 0
  have hE1 := congrFun hE 1
  simp only [ni_notAKnotE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply] at hE0 hE1
  set M := ni_moment x q
  have hpos : ∀ i, 0 < x (i + 1) - x i := fun i => sub_pos.mpr (hx (Nat.lt_succ_self i))
  -- the knot relations
  have hk0 : (x 2 - x 1) * (M 1 - M 0) = (x 1 - x 0) * (M 2 - M 1) := by
    have a := hT 0 (by omega)
    have b := hT 1 (by omega)
    have e : ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) := by linarith
    rw [e] at a
    linear_combination (x 1 - x 0) * b - (x 2 - x 1) * a
  have hkn : (x n - x (n - 1)) * (M (n - 1) - M (n - 2)) =
      (x (n - 1) - x (n - 2)) * (M n - M (n - 1)) := by
    have a := hT (n - 2) (by omega)
    have b := hT (n - 1) (by omega)
    have e1 : n - 2 + 1 = n - 1 := by omega
    have e2 : n - 1 + 1 = n := by omega
    rw [e1] at a
    rw [e2] at b
    have e : ni_cub3 (ni_piece q (n - 2)) = ni_cub3 (ni_piece q (n - 1)) := by linarith
    rw [e] at a
    linear_combination (x (n - 1) - x (n - 2)) * b - (x n - x (n - 1)) * a
  -- the two end rows
  have hr1 : ((x 1 - x 0) + 2 * (x 2 - x 1)) * M 1 + ((x 2 - x 1) - (x 1 - x 0)) * M 2 = 0 := by
    have r := hrow 1 le_rfl (by omega)
    simp only [Nat.sub_self] at r
    exact ni_notAKnot_row (hpos 0) (hpos 1) r hk0
  have hrn : ((x n - x (n - 1)) + 2 * (x (n - 1) - x (n - 2))) * M (n - 1) +
      ((x (n - 1) - x (n - 2)) - (x n - x (n - 1))) * M (n - 2) = 0 := by
    have r := hrow (n - 1) (by omega) (by omega)
    have e1 : n - 1 - 1 = n - 2 := by omega
    have e2 : n - 1 + 1 = n := by omega
    rw [e1, e2] at r
    have hp1 : 0 < x n - x (n - 1) := by have := hpos (n - 1); rwa [e2] at this
    have hp2 : 0 < x (n - 1) - x (n - 2) := by
      have := hpos (n - 2); rwa [show n - 2 + 1 = n - 1 by omega] at this
    exact ni_notAKnot_row (M₀ := M n) (M₁ := M (n - 1)) (M₂ := M (n - 2)) hp1 hp2
      (by linear_combination r) (by linear_combination hkn)
  -- maximum principle on `1, …, n − 1`
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.Icc 1 (n - 1))
    (fun i => |M i|) ⟨1, by simp; omega⟩
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  have hzero : |M j| = 0 := by
    rcases eq_or_ne j 1 with rfl | hne1
    · exact ni_notAKnot_end (hpos 0) (hpos 1) hr1 (hmax 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    rcases eq_or_ne j (n - 1) with rfl | hne2
    · have hp1 : 0 < x n - x (n - 1) := by
        have := hpos (n - 1); rwa [show n - 1 + 1 = n by omega] at this
      have hp2 : 0 < x (n - 1) - x (n - 2) := by
        have := hpos (n - 2); rwa [show n - 2 + 1 = n - 1 by omega] at this
      exact ni_notAKnot_end hp1 hp2 hrn (hmax (n - 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    · exact ni_moment_interior (sub_pos.mpr (hx (by omega)))
        (sub_pos.mpr (hx (Nat.lt_succ_self j))) (hrow j hj1 (by omega))
        (hmax (j - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        (hmax (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) rfl
  have hin : ∀ i, 1 ≤ i → i ≤ n - 1 → M i = 0 := by
    intro i hi1 hi2
    have := hmax i (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [hzero] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  apply ni_moments_zero hx hI hS
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [hin 1 le_rfl (by omega), hin 2 (by omega) (by omega)] at hk0
    have := hpos 1
    nlinarith
  rcases lt_or_eq_of_le hi with hin' | rfl
  · exact hin i hipos (by omega)
  · rw [hin (i - 1) (by omega) le_rfl, hin (i - 2) (by omega) (by omega)] at hkn
    have := hpos (i - 2)
    rw [show i - 2 + 1 = i - 1 by omega] at this
    nlinarith

/-- Miao, p. 361 (not-a-knot cubic spline): for strictly increasing nodes, `n ≥ 3`, and any data
`y`, there is exactly one cubic spline with `φ(xᵢ) = yᵢ` and `φ'''` continuous at `x₁` and
`xₙ₋₁`. -/
theorem ni_notAKnot_spline_existsUnique {n : ℕ} (hn : 3 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (y : ℕ → ℝ) :
    ∃! q : Fin n → Fin 4 → ℝ, ni_CubicInterp x y q ∧ ni_CubicSmooth x q ∧
      ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) ∧
        ni_cub3 (ni_piece q (n - 2)) = ni_cub3 (ni_piece q (n - 1)) := by
  have h := ni_spline_existsUnique_of_homogeneous (by omega) x (ni_notAKnotE n)
    (ni_notAKnot_homogeneous hn hx) y 0
  have hiff : ∀ q, ni_notAKnotE n q = 0 ↔
      ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) ∧
        ni_cub3 (ni_piece q (n - 2)) = ni_cub3 (ni_piece q (n - 1)) := by
    intro q
    constructor
    · intro hq
      have a := congrFun hq 0
      have b := congrFun hq 1
      simp only [ni_notAKnotE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Pi.zero_apply] at a b
      exact ⟨sub_eq_zero.mp a, sub_eq_zero.mp b⟩
    · rintro ⟨a, b⟩
      ext r
      fin_cases r <;> simp [ni_notAKnotE, a, b]
  simpa only [hiff] using h

/-- Miao, p. 361 (correction): with only two pieces (`n = 2`, nodes `0, 1, 2`) the not-a-knot
conditions do not determine the cubic spline: both pieces equal to `t(t − 1)(t − 2)` and both
equal to `0` interpolate the zero data. -/
theorem ni_notAKnot_not_unique_two :
    ¬ ∃! q : Fin 2 → Fin 4 → ℝ, ni_CubicInterp (fun i => (i : ℝ)) (fun _ => 0) q ∧
      ni_CubicSmooth (fun i => (i : ℝ)) q ∧
      ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) ∧
        ni_cub3 (ni_piece q (2 - 2)) = ni_cub3 (ni_piece q (2 - 1)) := by
  rintro ⟨q₀, -, huniq⟩
  set c : Fin 4 → ℝ := ![0, 2, -3, 1]
  set q : Fin 2 → Fin 4 → ℝ := fun _ => c
  have hpq : ∀ i < 2, ni_piece q i = c := fun i hi => by simp [ni_piece, hi, q]
  have h0 : ∀ i, ni_piece (0 : Fin 2 → Fin 4 → ℝ) i = 0 := fun i => by
    simp only [ni_piece]
    split_ifs <;> rfl
  have goodq : ni_CubicInterp (fun i => (i : ℝ)) (fun _ => 0) q ∧
      ni_CubicSmooth (fun i => (i : ℝ)) q ∧
      ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) ∧
        ni_cub3 (ni_piece q (2 - 2)) = ni_cub3 (ni_piece q (2 - 1)) := by
    refine ⟨fun i hi => ?_, fun j hj1 hj2 => ?_, ?_, ?_⟩
    · rw [hpq i hi]
      interval_cases i <;> simp [ni_cub, c] <;> norm_num
    · rw [hpq j hj2, hpq (j - 1) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [hpq 0 (by norm_num), hpq 1 (by norm_num)]
    · rw [hpq 0 (by norm_num), hpq 1 (by norm_num)]
  have good0 : ni_CubicInterp (fun i => (i : ℝ)) (fun _ => 0) (0 : Fin 2 → Fin 4 → ℝ) ∧
      ni_CubicSmooth (fun i => (i : ℝ)) (0 : Fin 2 → Fin 4 → ℝ) ∧
      ni_cub3 (ni_piece (0 : Fin 2 → Fin 4 → ℝ) 0) =
        ni_cub3 (ni_piece (0 : Fin 2 → Fin 4 → ℝ) 1) ∧
        ni_cub3 (ni_piece (0 : Fin 2 → Fin 4 → ℝ) (2 - 2)) =
          ni_cub3 (ni_piece (0 : Fin 2 → Fin 4 → ℝ) (2 - 1)) := by
    refine ⟨fun i _ => ?_, fun j _ _ => ?_, ?_, ?_⟩ <;>
      simp [h0, ni_cub, ni_cub1, ni_cub2, ni_cub3]
  have h1 := huniq q goodq
  have h2 := huniq 0 good0
  have : q = 0 := h1.trans h2.symm
  have := congrFun (congrFun this 0) 3
  simp [q, c] at this

end Miao.NumericalMethods
