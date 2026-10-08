/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NonlinearValuation.RiskSensitive

/-!
# Epstein–Zin preferences

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.2.3 (pp. 227–232),
Exercise 7.3.16 and §7.3.3.3 (p. 243).

The Epstein–Zin Koopmans operator with state-dependent discounting (7.23),
`Kv = (h + b(Pv^γ)^{α/γ})^{1/α}` on `V = (0, ∞)^X`, contains (7.14), `b ≡ β`, which in
turn is (7.13) when `h = (1 − β)c^α`.

* Exercise 7.2.7 and Exercise 7.3.21: `K` is a self-map of `V`.
* Lemma 7.2.4, Exercise 7.2.8 and Exercise 7.3.22: with `θ = γ/α`, `Φv = v^γ` is a
  homeomorphism of `V` conjugating `K` to `K̂v = (h + (Bv)^{1/θ})^θ`,
  `B(x, x') = b(x)^θP(x, x')`, the map of Theorem 7.1.4.
* Proposition 7.3.5: for `h, b ≫ 0` and `P` irreducible, `K` is globally stable on
  `V` iff `ρ(B)^{α/γ} < 1`.
* Proposition 7.2.3: for `b ≡ β ∈ (0, 1)`, `ρ(B)^{1/θ} = (β^θ)^{1/θ} = β < 1`, so the
  Epstein–Zin Koopmans operator is globally stable.
* Exercise 7.2.9: `F(t) = (h + βt^{1/θ})^θ` with `θ = 5`, `h = β = 1/2` has
  `F'(t) → ∞` as `t ↓ 0`, so `K̂` is not a contraction near zero.
* Exercise 7.3.16: if `P` is monotone increasing and `c` is increasing, Epstein–Zin
  lifetime utility (7.13) is increasing.
-/

open Matrix Finset Filter Topology Function Set

namespace SargentStachurski.NonlinearValuation

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X]

/-- The Epstein–Zin Koopmans operator with state-dependent discounting (7.23):
`(Kv)(x) = (h(x) + b(x)(R_γ v)(x)^α)^{1/α}`, with `R_γ v = (Pv^γ)^{1/γ}`. -/
noncomputable def ezK (h b : X → ℝ) (α γ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => (h x + b x * kpR γ P v x ^ α) ^ α⁻¹

/-- (7.23) is the Koopmans operator of the CES–Uzawa aggregator and the Kreps–Porteus certainty
equivalent, with `r = h^{1/α}` (§7.3.3.3). -/
theorem ezK_eq_koopmans (h b : X → ℝ) (α γ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) :
    ezK h b α γ P v = koopmans (fun x y => (h x + b x * y ^ α) ^ α⁻¹) (kpR γ P) v := rfl

/-- (7.13) as an instance of (7.14): with `h = (1 − β)c^α` and `b ≡ β`,
`(Kv)(x) = ((1 − β)c(x)^α + β[∑ v(x')^γ P(x, x')]^{α/γ})^{1/α}`. -/
theorem ezK_apply_ez (c : X → ℝ) (β α γ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) (x : X)
    (hpos : 0 ≤ (P *ᵥ fun x' => v x' ^ γ) x) :
    ezK (fun x => (1 - β) * c x ^ α) (fun _ => β) α γ P v x =
      ((1 - β) * c x ^ α + β * ((P *ᵥ fun x' => v x' ^ γ) x) ^ (α / γ)) ^ α⁻¹ := by
  simp only [ezK, kpR]
  rw [← Real.rpow_mul hpos, div_eq_inv_mul]

/-- Exercise 7.2.7 (p. 228) and Exercise 7.3.21 (p. 243): for `P` Markov, `h ≥ 0` and `b ≫ 0`,
`K` is a self-map of `V = (0, ∞)^X`. -/
theorem ezK_mapsTo {P : Matrix X X ℝ} (hP : IsMarkov P) {h b : X → ℝ} (hh : ∀ x, 0 ≤ h x)
    (hb : ∀ x, 0 < b x) (α γ : ℝ) : MapsTo (ezK h b α γ P) (posCone X) (posCone X) := by
  intro v hv x
  have hR := kpR_pos (γ := γ) hP hv x
  exact Real.rpow_pos_of_pos (add_pos_of_nonneg_of_pos (hh x)
    (mul_pos (hb x) (Real.rpow_pos_of_pos hR _))) _

/-- The conjugating map `Φv = v^γ` of Lemma 7.2.4. -/
noncomputable def powMap (γ : ℝ) (v : X → ℝ) : X → ℝ := fun x => v x ^ γ

omit [Fintype X] in
theorem powMap_mapsTo (γ : ℝ) : MapsTo (powMap γ) (posCone X) (posCone X) :=
  fun _ hv x => Real.rpow_pos_of_pos (hv x) _

omit [Fintype X] in
theorem powMap_inv {γ : ℝ} (hγ : γ ≠ 0) {v : X → ℝ} (hv : v ∈ posCone X) :
    powMap γ⁻¹ (powMap γ v) = v := by
  funext x
  exact Real.rpow_rpow_inv (hv x).le hγ

omit [Fintype X] in
theorem powMap_inv' {γ : ℝ} (hγ : γ ≠ 0) {v : X → ℝ} (hv : v ∈ posCone X) :
    powMap γ (powMap γ⁻¹ v) = v := by
  funext x
  exact Real.rpow_inv_rpow (hv x).le hγ

omit [Fintype X] in
/-- Lemma 7.2.4 (p. 230): `Φ` is continuous on `V`; with `powMap_inv` and `powMap_inv'` it is a
homeomorphism of `V` with inverse `v ↦ v^{1/γ}`. -/
theorem continuousOn_powMap (γ : ℝ) : ContinuousOn (powMap γ) (posCone X) :=
  continuousOn_pi.2 fun x => (continuous_apply x).continuousOn.rpow_const
    fun _ hv => Or.inl (hv x).ne'

/-- The discount matrix `B(x, x') = b(x)^θP(x, x')` of Proposition 7.3.5. -/
noncomputable def ezB (b : X → ℝ) (θ : ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => b x ^ θ * P x x'

/-- Exercise 7.3.22 (p. 243), and Lemma 7.2.4 and Exercise 7.2.8 for `b ≡ β`: with `θ = γ/α`,
`Φ(Kv) = K̂(Φv)` on `V`, where `K̂v = (h + (Bv)^{1/θ})^θ`. -/
theorem powMap_ezK {P : Matrix X X ℝ} (hP : IsMarkov P) {h b : X → ℝ} (hh : ∀ x, 0 ≤ h x)
    (hb : ∀ x, 0 < b x) {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0) {v : X → ℝ} (hv : v ∈ posCone X) :
    powMap γ (ezK h b α γ P v) = powG (ezB b (γ / α) P) h (γ / α) (powMap γ v) := by
  classical
  have hθ : γ / α ≠ 0 := div_ne_zero hγ hα
  funext x
  have hS := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') γ) x
  have hbase : 0 ≤ h x + b x * kpR γ P v x ^ α :=
    add_nonneg (hh x) (mul_nonneg (hb x).le (Real.rpow_nonneg (kpR_pos hP hv x).le _))
  -- `(Bv^γ)(x) = b(x)^θ (Pv^γ)(x)`
  have hB : (ezB b (γ / α) P *ᵥ powMap γ v) x = b x ^ (γ / α) * (P *ᵥ fun x' => v x' ^ γ) x := by
    simp only [mulVec, dotProduct, ezB, Matrix.of_apply, powMap, mul_sum]
    exact sum_congr rfl fun x' _ => by ring
  have hinv : (γ / α)⁻¹ = γ⁻¹ * α := by rw [inv_div, div_eq_inv_mul]
  have hBθ : (ezB b (γ / α) P *ᵥ powMap γ v) x ^ (γ / α)⁻¹ = b x * kpR γ P v x ^ α := by
    rw [hB, Real.mul_rpow (Real.rpow_nonneg (hb x).le _) hS.le,
      Real.rpow_rpow_inv (hb x).le hθ, kpR, ← Real.rpow_mul hS.le, hinv]
  simp only [powMap, ezK]
  rw [powG_apply, hBθ, ← Real.rpow_mul hbase, inv_mul_eq_div]

/-- `B` is irreducible when `b ≫ 0` and `P` is irreducible. -/
theorem irreducible_ezB {b : X → ℝ} (hb : ∀ x, 0 < b x) (θ : ℝ) {P : Matrix X X ℝ}
    [DecidableEq X] (hP : Irreducible P) : Irreducible (ezB b θ P) :=
  hP.of_pos_mul (c := fun x _ => b x ^ θ) fun x _ => Real.rpow_pos_of_pos (hb x) _

/-- **Proposition 7.3.5** (p. 243): for `h, b ≫ 0` and `P` irreducible Markov, the Epstein–Zin
Koopmans operator with state-dependent discounting is globally stable on `V = (0, ∞)^X` iff
`ρ(B)^{α/γ} < 1`. -/
theorem globallyStableOn_ezK_iff [DecidableEq X] [Nonempty X] {P : Matrix X X ℝ}
    (hP : IsMarkov P) (hirr : Irreducible P) {h b : X → ℝ} (hh : ∀ x, 0 < h x)
    (hb : ∀ x, 0 < b x) {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0) :
    GloballyStableOn (ezK h b α γ P) (posCone X) ↔ specRad (ezB b (γ / α) P) ^ (α / γ) < 1 := by
  have hθ : γ / α ≠ 0 := div_ne_zero hγ hα
  rw [globallyStableOn_iff_of_conj (powMap γ) (powMap γ⁻¹) (powMap_mapsTo γ) (powMap_mapsTo γ⁻¹)
    (fun u hu => powMap_inv' hγ hu) (fun u hu => powMap_inv hγ hu) (continuousOn_powMap γ)
    (continuousOn_powMap γ⁻¹) (ezK_mapsTo hP (fun x => (hh x).le) hb α γ)
    (fun u hu => powMap_ezK hP (fun x => (hh x).le) hb hα hγ hu),
    ← globallyStableOn_powG_iff (irreducible_ezB hb _ hirr) hh hθ, inv_div]

/-- **Proposition 7.2.3** (p. 228): for `P` irreducible Markov, `h ≫ 0` and `0 < β < 1`, the
Epstein–Zin Koopmans operator (7.14) is globally stable on `V = (0, ∞)^X`. -/
theorem globallyStableOn_ez [DecidableEq X] [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hirr : Irreducible P) {h : X → ℝ} (hh : ∀ x, 0 < h x) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0) :
    GloballyStableOn (ezK h (fun _ => β) α γ P) (posCone X) := by
  rw [globallyStableOn_ezK_iff hP hirr hh (fun _ => hβ0) hα hγ]
  have hB : ezB (fun _ => β) (γ / α) P = β ^ (γ / α) • P := by
    ext x x'
    simp [ezB]
  rw [hB, specRad_smul_isMarkov hP (Real.rpow_nonneg hβ0.le _), ← Real.rpow_mul hβ0.le,
    div_mul_div_cancel₀ hα, div_self hγ, Real.rpow_one]
  exact hβ1

/-- Exercise 7.2.9 (p. 232): `F(t) = (1/2 + (1/2)t^{1/5})^5` has derivative
`F'(t) = (1/2)(1/2 + (1/2)t^{1/5})^4 t^{−4/5}`, which tends to `∞` as `t ↓ 0`; so `K̂` has infinite
slope at zero and is not a contraction. -/
theorem ez_deriv_tendsto_atTop :
    (∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => (1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹) ^ (5 : ℝ))
      (1 / 2 * (1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹) ^ (4 : ℝ) * t ^ (-(4 / 5 : ℝ))) t) ∧
      Tendsto (fun t : ℝ => 1 / 2 * (1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹) ^ (4 : ℝ) * t ^ (-(4 / 5 : ℝ)))
        (𝓝[>] 0) atTop := by
  constructor
  · intro t ht
    have hb : 0 < 1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹ := by
      have := Real.rpow_pos_of_pos ht (5 : ℝ)⁻¹; positivity
    have h1 : HasDerivAt (fun t : ℝ => 1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹)
        (1 / 2 * ((5 : ℝ)⁻¹ * t ^ ((5 : ℝ)⁻¹ - 1))) t :=
      ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul (1 / 2)).const_add _
    convert h1.rpow_const (p := 5) (Or.inl hb.ne') using 1
    have e1 : ((5 : ℝ)⁻¹ - 1) = -(4 / 5) := by norm_num
    have e2 : (5 : ℝ) - 1 = 4 := by norm_num
    rw [e1, e2]
    ring
  · -- the factor `(1/2 + t^{1/5}/2)^4 ≥ 1/16` and `t^{−4/5} → ∞`
    have hlim := tendsto_rpow_neg_nhdsGT_zero (y := -(4 / 5 : ℝ)) (by norm_num)
    refine tendsto_atTop_mono' _ ?_ (hlim.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 32))
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : (1 / 2 : ℝ) ≤ 1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹ := by
      have := Real.rpow_pos_of_pos ht' (5 : ℝ)⁻¹; linarith
    have h2 : (1 / 2 : ℝ) ^ (4 : ℝ) ≤ (1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹) ^ (4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
    have h3 : (1 / 2 : ℝ) ^ (4 : ℝ) = 1 / 16 := by norm_num
    have h4 := Real.rpow_pos_of_pos ht' (-(4 / 5 : ℝ))
    rw [h3] at h2
    nlinarith

/-- Exercise 7.3.16 (p. 239): if `P` is irreducible, Markov and monotone increasing, `c ≫ 0` is
increasing and `0 < β < 1`, then Epstein–Zin lifetime utility (7.13) is increasing in the state. -/
theorem monotone_ez_lifetimeValue [Preorder X] [DecidableEq X] [Nonempty X] {P : Matrix X X ℝ}
    (hP : IsMarkov P) (hirr : Irreducible P) (hPm : MonotoneKernel P) {c : X → ℝ}
    (hc : ∀ x, 0 < c x) (hcm : Monotone c) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {α γ : ℝ}
    (hα : α ≠ 0) (hγ : γ ≠ 0) {v : X → ℝ} (hv : v ∈ posCone X)
    (hfix : IsFixedPt (ezK (fun x => (1 - β) * c x ^ α) (fun _ => β) α γ P) v) : Monotone v := by
  have hh : ∀ x, 0 < (1 - β) * c x ^ α := fun x =>
    mul_pos (by linarith) (Real.rpow_pos_of_pos (hc x) _)
  have hst := globallyStableOn_ez hP hirr hh hβ0 hβ1 hα hγ
  refine monotone_of_globallyStableOn hst (ezK_mapsTo hP (fun x => (hh x).le) (fun _ => hβ0) α γ)
    (v₀ := fun _ => 1) (fun _ => one_pos) (fun _ _ _ => le_rfl) (fun w hw hwm x y hxy => ?_) hv
    hfix
  have hR := monotone_kpR hγ hP hPm hw hwm hxy
  have hRx := kpR_pos (γ := γ) hP hw x
  have hRy := kpR_pos (γ := γ) hP hw y
  have hcx := hc x
  have hcy := hc y
  have hbx : 0 < (1 - β) * c x ^ α + β * kpR γ P w x ^ α := by
    have := Real.rpow_pos_of_pos hcx α; have := Real.rpow_pos_of_pos hRx α
    have : 0 < 1 - β := by linarith
    positivity
  have hby : 0 < (1 - β) * c y ^ α + β * kpR γ P w y ^ α := by
    have := Real.rpow_pos_of_pos hcy α; have := Real.rpow_pos_of_pos hRy α
    have : 0 < 1 - β := by linarith
    positivity
  simp only [ezK]
  have h1β : 0 < 1 - β := by linarith
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · have h1 : c y ^ α ≤ c x ^ α := Real.rpow_le_rpow_of_nonpos hcx (hcm hxy) hneg.le
    have h2 : kpR γ P w y ^ α ≤ kpR γ P w x ^ α := Real.rpow_le_rpow_of_nonpos hRx hR hneg.le
    exact Real.rpow_le_rpow_of_nonpos hby (by nlinarith) (inv_lt_zero.2 hneg).le
  · have h1 : c x ^ α ≤ c y ^ α := Real.rpow_le_rpow hcx.le (hcm hxy) hpos.le
    have h2 : kpR γ P w x ^ α ≤ kpR γ P w y ^ α := Real.rpow_le_rpow hRx.le hR hpos.le
    exact Real.rpow_le_rpow hbx.le (by nlinarith) (inv_pos.2 hpos).le

end SargentStachurski.NonlinearValuation
