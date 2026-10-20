/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.SequencePrices

/-!
# Discounted sums, the tail distance, and functionals with all their weight at infinity

Tools for the examples and counterexamples of SLP §15.4, pp. 463–467, on `S = ℓ∞ = BddSeq ℝ`.

* `halfSum` : the discounted sum `σ(x) = Σ_t (1/2)ᵗ x_t`, a continuous linear functional on `ℓ∞`
  with no weight at infinity: `σ(xᵀ) → σ(x)` (`tendsto_halfSum_seqTrunc`).
* `tailDist x` : the distance from `x` to the eventually zero sequences `seqC00`; it is convex
  (`tailDist_convex`), `1`-Lipschitz, zero on `seqC00`, eventually at least the size of the
  coordinates (`eventually_norm_lt_tailDist_add`), and `tailDist 1 = 1` (`tailDist_oneSeq`).
  (It equals `limsup_t ‖x_t‖`.)
* `exists_seq_functional_at_infinity` (Hahn–Banach): there is `φ ∈ (ℓ∞)*` with `‖φ‖ ≤ 1`,
  `φ = 0` on `seqC00`, `φ(1) = 1`; such a `φ` is positive (`seq_apply_nonpos_of_nonpos`) and its
  regular part (Lemma 15.5) is zero (`seqRegularPart_eq_zero_of_seqC00`): all of its weight is at
  infinity.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Metric
open scoped ENNReal

/-! ### The discounted sum `σ(x) = Σ (1/2)ᵗ x_t` -/

/-- `Σ_t |(1/2)ᵗ x_t|` converges. -/
theorem summable_half_mul (x : BddSeq ℝ) : Summable fun t => |(1 / 2 : ℝ) ^ t * x t| := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun t => ?_)
    ((summable_geometric_two).mul_right ‖x‖)
  rw [abs_mul, abs_of_nonneg (by positivity), one_div, inv_pow]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_seq_coord_le x t) (by positivity)

/-- `σ` as a linear map. -/
noncomputable def halfSumLinear : BddSeq ℝ →ₗ[ℝ] ℝ where
  toFun x := ∑' t, (1 / 2 : ℝ) ^ t * x t
  map_add' x y := by
    have h : ∀ t, (1 / 2 : ℝ) ^ t * (x + y) t = (1 / 2) ^ t * x t + (1 / 2) ^ t * y t :=
      fun t => by rw [lp.coeFn_add, Pi.add_apply, mul_add]
    simp only [h]
    exact (summable_half_mul x).of_abs.tsum_add (summable_half_mul y).of_abs
  map_smul' c x := by
    have h : ∀ t, (1 / 2 : ℝ) ^ t * (c • x) t = c * ((1 / 2) ^ t * x t) := fun t => by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring
    simp only [h, RingHom.id_apply, smul_eq_mul]
    exact tsum_mul_left

/-- `|σ(x)| ≤ 2 ‖x‖`. -/
theorem norm_halfSumLinear_le (x : BddSeq ℝ) : ‖halfSumLinear x‖ ≤ 2 * ‖x‖ := by
  change |∑' t, (1 / 2 : ℝ) ^ t * x t| ≤ 2 * ‖x‖
  have h := norm_tsum_le_tsum_norm (f := fun t => (1 / 2 : ℝ) ^ t * x t)
    (by simpa only [Real.norm_eq_abs] using summable_half_mul x)
  simp only [Real.norm_eq_abs] at h
  refine h.trans ?_
  have hb : ∀ t, |(1 / 2 : ℝ) ^ t * x t| ≤ (1 / 2) ^ t * ‖x‖ := fun t => by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by simpa using norm_seq_coord_le x t) (by positivity)
  calc ∑' t, |(1 / 2 : ℝ) ^ t * x t| ≤ ∑' t, (1 / 2 : ℝ) ^ t * ‖x‖ :=
        (summable_half_mul x).tsum_le_tsum hb
          ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _)
    _ = 2 * ‖x‖ := by rw [tsum_mul_right, tsum_geometric_two]

/-- The **discounted sum** `σ(x) = Σ_t (1/2)ᵗ x_t` on `ℓ∞`. -/
noncomputable def halfSum : StrongDual ℝ (BddSeq ℝ) :=
  halfSumLinear.mkContinuous 2 norm_halfSumLinear_le

/-- Value of `σ`. -/
theorem halfSum_apply (x : BddSeq ℝ) : halfSum x = ∑' t, (1 / 2 : ℝ) ^ t * x t := rfl

/-- `σ(x) = Σ_t (1/2)ᵗ x_t` as a `HasSum`. -/
theorem hasSum_halfSum (x : BddSeq ℝ) : HasSum (fun t => (1 / 2 : ℝ) ^ t * x t) (halfSum x) :=
  (summable_half_mul x).of_abs.hasSum

/-- The coordinate functionals of `σ` are `a ↦ (1/2)ᵗ a`. -/
theorem halfSum_single (t : ℕ) (a : ℝ) : halfSum (lp.single ∞ t a) = (1 / 2 : ℝ) ^ t * a := by
  rw [halfSum_apply, tsum_eq_single t]
  · rw [lp.single_apply, Pi.single_eq_same]
  · intro s hs
    rw [lp.single_apply, Pi.single_eq_of_ne hs, mul_zero]

/-- `σ` has no weight at infinity: `σ(xᵀ) → σ(x)`. -/
theorem tendsto_halfSum_seqTrunc (x : BddSeq ℝ) :
    Tendsto (fun T => halfSum (seqTrunc T x)) atTop (𝓝 (halfSum x)) := by
  have h : ∀ T, halfSum (seqTrunc T x) = ∑ t ∈ Finset.range (T + 1), (1 / 2 : ℝ) ^ t * x t :=
    fun T => by
      rw [apply_seqTrunc_eq_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [coordFunctional_apply, halfSum_single]
  simp only [h]
  exact (hasSum_halfSum x).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-! ### The tail distance -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **tail distance** `d(x) = inf {‖x − m‖ : m eventually zero}` (`= limsup_t ‖x_t‖`). -/
noncomputable def tailDist (x : BddSeq E) : ℝ := infDist x (seqC00 E : Set (BddSeq E))

/-- `seqC00` is nonempty. -/
theorem seqC00_nonempty : (seqC00 E : Set (BddSeq E)).Nonempty := ⟨0, (seqC00 E).zero_mem⟩

/-- `d ≥ 0`. -/
theorem tailDist_nonneg (x : BddSeq E) : 0 ≤ tailDist x := infDist_nonneg

/-- `d` vanishes on `seqC00`. -/
theorem tailDist_of_mem {x : BddSeq E} (hx : x ∈ seqC00 E) : tailDist x = 0 :=
  infDist_zero_of_mem hx

/-- `d` is continuous. -/
theorem continuous_tailDist : Continuous (tailDist (E := E)) := continuous_infDist_pt _

/-- `d` is convex. -/
theorem tailDist_convex (x x' : BddSeq E) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    tailDist (θ • x + (1 - θ) • x') ≤ θ * tailDist x + (1 - θ) * tailDist x' := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨m, hm, hdm⟩ := (infDist_lt_iff seqC00_nonempty).1
    (lt_add_of_pos_right (tailDist x) hε)
  obtain ⟨m', hm', hdm'⟩ := (infDist_lt_iff seqC00_nonempty).1
    (lt_add_of_pos_right (tailDist x') hε)
  have hmem : θ • m + (1 - θ) • m' ∈ seqC00 E :=
    (seqC00 E).add_mem ((seqC00 E).smul_mem θ hm) ((seqC00 E).smul_mem (1 - θ) hm')
  have h1θ : 0 ≤ 1 - θ := by linarith
  calc tailDist (θ • x + (1 - θ) • x')
      ≤ dist (θ • x + (1 - θ) • x') (θ • m + (1 - θ) • m') := infDist_le_dist_of_mem hmem
    _ ≤ θ * dist x m + (1 - θ) * dist x' m' := by
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
        calc ‖θ • x + (1 - θ) • x' - (θ • m + (1 - θ) • m')‖
            = ‖θ • (x - m) + (1 - θ) • (x' - m')‖ := by
              congr 1; simp only [smul_sub]; abel
          _ ≤ ‖θ • (x - m)‖ + ‖(1 - θ) • (x' - m')‖ := norm_add_le _ _
          _ = θ * ‖x - m‖ + (1 - θ) * ‖x' - m'‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg h0, Real.norm_of_nonneg h1θ]
    _ ≤ θ * (tailDist x + ε) + (1 - θ) * (tailDist x' + ε) := by
        gcongr
    _ = θ * tailDist x + (1 - θ) * tailDist x' + ε := by ring

/-- The coordinates are eventually at most `d(x) + ε`. -/
theorem eventually_norm_lt_tailDist_add (x : BddSeq E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ‖x T‖ < tailDist x + ε := by
  obtain ⟨m, hm, hdm⟩ := (infDist_lt_iff seqC00_nonempty).1
    (lt_add_of_pos_right (tailDist x) hε)
  filter_upwards [hm] with T hT
  calc ‖x T‖ = ‖(x - m) T‖ := by rw [lp.coeFn_sub, Pi.sub_apply, hT, sub_zero]
    _ ≤ ‖x - m‖ := norm_seq_coord_le _ T
    _ = dist x m := (dist_eq_norm x m).symm
    _ < tailDist x + ε := hdm

/-- `d(1) = 1`. -/
theorem tailDist_oneSeq : tailDist oneSeq = 1 := by
  refine le_antisymm ?_ ?_
  · calc tailDist oneSeq ≤ dist oneSeq 0 := infDist_le_dist_of_mem (seqC00 ℝ).zero_mem
      _ = ‖oneSeq‖ := dist_zero_right _
      _ ≤ 1 := norm_oneSeq_le
  · refine (le_infDist seqC00_nonempty).2 fun m hm => ?_
    obtain ⟨t, ht⟩ := (hm : ∀ᶠ t in atTop, m t = 0).exists
    calc (1 : ℝ) = ‖(oneSeq - m) t‖ := by
          rw [lp.coeFn_sub, Pi.sub_apply, ht, sub_zero]; simp [oneSeq]
      _ ≤ ‖oneSeq - m‖ := norm_seq_coord_le _ t
      _ = dist oneSeq m := (dist_eq_norm _ _).symm

/-! ### A functional with all its weight at infinity -/

/-- The quotient norm is the distance to the subspace. -/
theorem norm_quotient_seqC00_mk (x : BddSeq ℝ) :
    ‖(Submodule.Quotient.mk x : BddSeq ℝ ⧸ seqC00 ℝ)‖ = tailDist x :=
  QuotientAddGroup.norm_mk (S := (seqC00 ℝ).toAddSubgroup) x

/-- **A functional at infinity** (Hahn–Banach): some `φ ∈ (ℓ∞)*` has `‖φ‖ ≤ 1`, vanishes on the
eventually zero sequences, and has `φ(1) = 1`. -/
theorem exists_seq_functional_at_infinity :
    ∃ φ : StrongDual ℝ (BddSeq ℝ), ‖φ‖ ≤ 1 ∧ (∀ x ∈ seqC00 ℝ, φ x = 0) ∧ φ oneSeq = 1 := by
  obtain ⟨g, hg1, hgx⟩ :=
    exists_dual_vector'' ℝ (Submodule.Quotient.mk oneSeq : BddSeq ℝ ⧸ seqC00 ℝ)
  have hb : ∀ y : BddSeq ℝ, ‖(g.toLinearMap.comp (seqC00 ℝ).mkQ) y‖ ≤ 1 * ‖y‖ := fun y => by
    change ‖g (Submodule.Quotient.mk y)‖ ≤ 1 * ‖y‖
    calc ‖g (Submodule.Quotient.mk y)‖ ≤ ‖g‖ * ‖(Submodule.Quotient.mk y : BddSeq ℝ ⧸ seqC00 ℝ)‖ :=
          g.le_opNorm _
      _ ≤ 1 * ‖y‖ := mul_le_mul hg1 (Submodule.Quotient.norm_mk_le (seqC00 ℝ) y) (norm_nonneg _)
          zero_le_one
  refine ⟨(g.toLinearMap.comp (seqC00 ℝ).mkQ).mkContinuous 1 hb,
    LinearMap.mkContinuous_norm_le _ zero_le_one hb, fun y hy => ?_, ?_⟩
  · change g (Submodule.Quotient.mk y) = 0
    rw [(Submodule.Quotient.mk_eq_zero (seqC00 ℝ)).2 hy, map_zero]
  · change g (Submodule.Quotient.mk oneSeq) = 1
    rw [hgx, norm_quotient_seqC00_mk, tailDist_oneSeq]
    simp

/-- A functional with `‖φ‖ ≤ 1` and `φ(1) = 1` is positive: `y ≤ 0` implies `φ(y) ≤ 0`. -/
theorem seq_apply_nonpos_of_nonpos {φ : StrongDual ℝ (BddSeq ℝ)} (hφ1 : ‖φ‖ ≤ 1)
    (hφone : φ oneSeq = 1) {y : BddSeq ℝ} (hy : ∀ t, y t ≤ 0) : φ y ≤ 0 := by
  rcases (norm_nonneg y).eq_or_lt with h0 | hpos
  · rw [norm_eq_zero.1 h0.symm, map_zero]
  set M := ‖y‖ with hM
  have hz : ‖oneSeq + M⁻¹ • y‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one fun t => by
    have hyt : |y t| ≤ M := by simpa using norm_seq_coord_le y t
    have h1 : -M ≤ y t := (abs_le.1 hyt).1
    have hv : (oneSeq + M⁻¹ • y) t = 1 + M⁻¹ * y t := by
      rw [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; simp [oneSeq]
    rw [hv, Real.norm_eq_abs, abs_le]
    have h2 : M⁻¹ * y t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hpos.le) (hy t)
    have h3 : -1 ≤ M⁻¹ * y t := by
      rw [le_inv_mul_iff₀ hpos]; linarith
    constructor <;> linarith
  have h := (le_abs_self _).trans ((φ.le_opNorm _).trans
    ((mul_le_mul hφ1 hz (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)))
  rw [map_add, map_smul, hφone, smul_eq_mul] at h
  by_contra hc
  have := mul_pos (inv_pos.2 hpos) (not_le.1 hc)
  linarith [le_abs_self (1 + M⁻¹ * φ y)]

/-- A functional vanishing on `seqC00` has zero regular part (Lemma 15.5): all its weight is at
infinity. -/
theorem seqRegularPart_eq_zero_of_seqC00 {φ : StrongDual ℝ (BddSeq E)}
    (hφ : ∀ x ∈ seqC00 E, φ x = 0) :
    seqRegularPart φ = 0 := by
  ext x
  rw [seqRegularPart_apply, zero_apply]
  refine (tsum_congr fun t => ?_).trans tsum_zero
  rw [coordFunctional_apply]
  refine hφ _ ((eventually_gt_atTop t).mono fun s hs => ?_)
  rw [lp.single_apply, Pi.single_eq_of_ne (ne_of_gt hs)]

end StokeyLucasPrescott.ParetoOptimaEquilibria
