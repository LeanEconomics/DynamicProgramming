/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.SustainedGrowthUtility
import EquilibriumApplications.WelfareSecond

/-!
# Sustained growth: equilibria and optima (Exercise 16.3(e))

SLP §16.3, p. 487. The economy has one consumer and one firm. The commodity space is `S_θ`,
identified with `ℓ_∞ = BddSeq ℝ` by `sgOfBdd θ` (module `SustainedGrowth`); the consumption set
is `X = sgXa θ a` (`x_t ≥ a θᵗ`), utility `u(x) = Σ βᵗ U(x_t)` with CRRA `U` (`σ > 0`,
`βθ^{1−σ} < 1`), and the production set is `Y ∩ S_θ` (`sgTechθ`). These are `sgX`, `sgU`, `sgY`.

* `sg_feasible_unit`, `sg_aggTech_unit`: with one consumer and one firm, feasibility is
  `x ∈ X`, `y ∈ Y`, `x = y`, and the aggregate technology is `Y`.
* `sg_paretoOptimal_iff`: `(x, x)` is Pareto optimal iff `x` solves the planning problem
  `max {u(z) : z ∈ X ∩ Y}`.
* Properties used: `sg_localNonsatiation` (local nonsatiation), `sg_convex_sgXa` (15.1),
  `sg_assumption15_2` (from `sg_utility_concave`), continuity (15.3, Exercise 16.3(d)),
  `sg_convex_sgTechθ` (15.4, from concavity of `k ↦ kᵅ`), and the interior point of
  Exercise 16.3(b) at `θ = θ̂` (15.5).
* **Exercise 16.3(e)(i)** (`ex_16_3e_i`): if `(x, y, φ)` is a competitive equilibrium (any
  continuous linear price `φ` on `S_θ`), then `x = y` and `(x, y)` is Pareto optimal.
* **Exercise 16.3(e)(ii)** (`ex_16_3e_ii`): at `θ = θ̂`, if `(x, x)` is Pareto optimal and the
  lower bound of `X` does not bind uniformly (`x_t ≥ a′θᵗ` for some `a′ > a`), there is a
  continuous linear price `φ` on `S_θ` with `(x, x, φ)` a competitive equilibrium.
  `sg_support_nonneg` and `sg_support_one_pos`: any supporting price is a positive functional
  with `φ(θᵗ)_t > 0`, which yields the cheaper point.

**Corrections and comments.**
* The book asks for a "direct" proof; (i) is the argument of Theorem 15.3 and (ii) uses
  Theorem 15.4 with the Remark on cheaper points, with every hypothesis verified for this economy.
  The [Derived] direct proof of (ii) with the inner-product price `p_t = βᵗ U′(x_t)` is in
  `SustainedGrowthPrices` (`ex_16_3e_ii_direct`).
* (ii) needs the cheaper point of the Remark to Theorem 15.4. It is obtained here from the
  hypothesis that the lower bound `x_t ≥ aθᵗ` of `X` does not bind (the book: "with luck the
  lower bound does not bind"); without it, the supporting price may have no cheaper point in `X`.
* The price is a continuous linear functional on `S_θ`, not necessarily of inner-product form:
  Theorem 15.6 cannot be used to remove a weight at infinity, because `X` is not closed under
  truncation (`xᵀ_t = 0 < aθᵗ` for `t > T`), so Assumption 15.6 fails for `X`.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

/-- The consumption set of the §16.3 economy (one consumer). -/
def sgX (θ a : ℝ) : Unit → Set (BddSeq ℝ) := fun _ => sgXa θ a

/-- The utility of the §16.3 economy, `u(x) = Σ βᵗ U(x_t)` with CRRA `U`. -/
noncomputable def sgU (β σ θ : ℝ) : Unit → BddSeq ℝ → ℝ :=
  fun _ w => sgUtility β (sgCRRA σ) (sgOfBdd θ w)

/-- The production set of the §16.3 economy (one firm), `Y ∩ S_θ`. -/
def sgY (θ γ α k0 : ℝ) : Unit → Set (BddSeq ℝ) := fun _ => sgTechθ θ γ α k0

/-- With one consumer and one firm, feasibility means `x ∈ X`, `y ∈ Y` and `x = y`. -/
theorem sg_feasible_unit {S : Type*} [NormedAddCommGroup S] {X Y : Unit → Set S}
    {x y : Unit → S} : Feasible X Y x y ↔ x () ∈ X () ∧ y () ∈ Y () ∧ x () = y () := by
  simp only [Feasible, Finset.univ_unique, Finset.sum_singleton, sub_eq_zero]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1 (), h2 (), h3⟩, fun ⟨h1, h2, h3⟩ => ⟨fun _ => h1, fun _ => h2, h3⟩⟩

/-- With one firm the aggregate technology is the firm's production set. -/
theorem sg_aggTech_unit {S : Type*} [NormedAddCommGroup S] (A : Set S) :
    aggTech (fun _ : Unit => A) = A := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy ()
  · intro hw
    exact ⟨fun _ => w, fun _ => hw, by simp⟩

/-- Coordinates of a linear combination under `sgOfBdd`. -/
theorem sgOfBdd_combo (θ s r : ℝ) (w w' : BddSeq ℝ) (t : ℕ) :
    sgOfBdd θ (s • w + r • w') t = s * sgOfBdd θ w t + r * sgOfBdd θ w' t := by
  change θ ^ t * (s • w + r • w') t = s * (θ ^ t * w t) + r * (θ ^ t * w' t)
  rw [seq_coord_combo, smul_eq_mul, smul_eq_mul]
  ring

/-- Points of `X` have positive coordinates `θᵗ w_t > 0`. -/
theorem sgXa_pos {θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a) {w : BddSeq ℝ} (hw : w ∈ sgXa θ a)
    (t : ℕ) : 0 < sgOfBdd θ w t :=
  lt_of_lt_of_le (mul_pos ha (pow_pos hθ t)) (hw t)

/-- **Assumption 15.1**: `X` is convex. -/
theorem sg_convex_sgXa {θ a : ℝ} (hθ : 0 < θ) : Convex ℝ (sgXa θ a) := by
  intro w hw w' hw' s r hs hr hsr
  refine (mem_sgXa_iff hθ).2 fun t => ?_
  rw [seq_coord_combo, smul_eq_mul, smul_eq_mul]
  have h1 := (mem_sgXa_iff hθ).1 hw t
  have h2 := (mem_sgXa_iff hθ).1 hw' t
  have : a = s * a + r * a := by rw [← add_mul, hsr, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 hr]

/-- `X` is closed under adding a nonnegative path. -/
theorem sgXa_add_nonneg {θ a : ℝ} (hθ : 0 < θ) {w e : BddSeq ℝ} (hw : w ∈ sgXa θ a)
    (he : ∀ t, 0 ≤ e t) : w + e ∈ sgXa θ a :=
  (mem_sgXa_iff hθ).2 fun t => by
    rw [lp.coeFn_add, Pi.add_apply]
    linarith [(mem_sgXa_iff hθ).1 hw t, he t]

/-- `u` is nondecreasing on `X`: `u(w) ≤ u(w + e)` for `e ≥ 0`. -/
theorem sg_utility_le_add {β θ σ a : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : 0 < θ)
    (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) {w e : BddSeq ℝ} (hw : w ∈ sgXa θ a)
    (he : ∀ t, 0 ≤ e t) :
    sgUtility β (sgCRRA σ) (sgOfBdd θ w) ≤ sgUtility β (sgCRRA σ) (sgOfBdd θ (w + e)) := by
  have hwe := sgXa_add_nonneg hθ hw he
  refine (ex_16_3d_summable hσ hβ0 hβ1 hθ hρ1 ha hw).tsum_le_tsum (fun t => ?_)
    (ex_16_3d_summable hσ hβ0 hβ1 hθ hρ1 ha hwe)
  refine mul_le_mul_of_nonneg_left ((sgCRRA_strictMonoOn hσ).monotoneOn
    (sgXa_pos hθ ha hw t) (sgXa_pos hθ ha hwe t) ?_) (pow_nonneg hβ0 t)
  rw [sgOfBdd_add]
  exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hθ.le t) (he t))

/-- `u` strictly increases when a positive constant `c𝟙` is added. -/
theorem sg_utility_lt_add_const {β θ σ a c : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) (hc : 0 < c) {w : BddSeq ℝ}
    (hw : w ∈ sgXa θ a) :
    sgUtility β (sgCRRA σ) (sgOfBdd θ w) <
      sgUtility β (sgCRRA σ) (sgOfBdd θ (w + sgConst c)) := by
  have he : ∀ t, 0 ≤ sgConst c t := fun _ => hc.le
  have hwe := sgXa_add_nonneg hθ hw he
  have hmono := (sgCRRA_strictMonoOn hσ)
  refine (ex_16_3d_summable hσ hβ0 hβ1 hθ hρ1 ha hw).tsum_lt_tsum (i := 0) (fun t => ?_) ?_
    (ex_16_3d_summable hσ hβ0 hβ1 hθ hρ1 ha hwe)
  · refine mul_le_mul_of_nonneg_left (hmono.monotoneOn (sgXa_pos hθ ha hw t)
      (sgXa_pos hθ ha hwe t) ?_) (pow_nonneg hβ0 t)
    rw [sgOfBdd_add]
    exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hθ.le t) hc.le)
  · simp only [pow_zero, one_mul]
    refine hmono (sgXa_pos hθ ha hw 0) (sgXa_pos hθ ha hwe 0) ?_
    rw [sgOfBdd_add]
    change sgOfBdd θ w 0 < sgOfBdd θ w 0 + θ ^ 0 * c
    rw [pow_zero, one_mul]
    linarith

/-- **Local nonsatiation** on `X`: `w + 𝟙/(n+1) → w` with strictly higher utility. -/
theorem sg_localNonsatiation {β θ σ a : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) :
    LocalNonsatiation (sgX θ a) (sgU β σ θ) := by
  intro i z hz
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  refine ⟨fun n => z + sgConst (1 / ((n : ℝ) + 1)),
    fun n => sgXa_add_nonneg hθ hz fun _ => (hpos n).le, ?_,
    fun n => sg_utility_lt_add_const hσ hβ0 hβ1 hθ hρ1 ha (hpos n) hz⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [add_sub_cancel_left]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (norm_sgConst_le _).trans
    (le_of_eq (abs_of_pos (hpos n)))) tendsto_one_div_add_atTop_nhds_zero_nat

/-- `u` is concave on `X`. -/
theorem sg_utility_concave {β θ σ a : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) {w w' : BddSeq ℝ}
    (hw : w ∈ sgXa θ a) (hw' : w' ∈ sgXa θ a) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    s * sgUtility β (sgCRRA σ) (sgOfBdd θ w) + (1 - s) * sgUtility β (sgCRRA σ) (sgOfBdd θ w')
      ≤ sgUtility β (sgCRRA σ) (sgOfBdd θ (s • w + (1 - s) • w')) := by
  have hs := ex_16_3d_summable hσ hβ0 hβ1 hθ hρ1 ha hw
  have hs' := ex_16_3d_summable hσ hβ0 hβ1 hθ hρ1 ha hw'
  have hmem : s • w + (1 - s) • w' ∈ sgXa θ a :=
    sg_convex_sgXa hθ hw hw' h0 (by linarith) (by ring)
  have hs'' := ex_16_3d_summable hσ hβ0 hβ1 hθ hρ1 ha hmem
  unfold sgUtility
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hs.mul_left s).tsum_add (hs'.mul_left (1 - s))]
  refine ((hs.mul_left s).add (hs'.mul_left (1 - s))).tsum_le_tsum (fun t => ?_) hs''
  have hc := (sgCRRA_concaveOn hσ).2 (sgXa_pos hθ ha hw t) (sgXa_pos hθ ha hw' t) h0
    (by linarith : 0 ≤ 1 - s) (by ring)
  simp only [smul_eq_mul] at hc
  rw [sgOfBdd_combo]
  calc s * (β ^ t * sgCRRA σ (sgOfBdd θ w t)) + (1 - s) * (β ^ t * sgCRRA σ (sgOfBdd θ w' t))
      = β ^ t * (s * sgCRRA σ (sgOfBdd θ w t) + (1 - s) * sgCRRA σ (sgOfBdd θ w' t)) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (pow_nonneg hβ0 t)

/-- **Assumption 15.2** for the §16.3 consumer (from concavity of `u`). -/
theorem sg_assumption15_2 {β θ σ a : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) :
    Assumption15_2 (sgX θ a) (sgU β σ θ) := by
  intro i z hz z' hz' hlt s hs0 hs1
  have := sg_utility_concave hσ hβ0 hβ1 hθ hρ1 ha hz hz' hs0.le hs1.le
  change sgUtility β (sgCRRA σ) (sgOfBdd θ z') <
    sgUtility β (sgCRRA σ) (sgOfBdd θ (s • z + (1 - s) • z'))
  change sgUtility β (sgCRRA σ) (sgOfBdd θ z') < sgUtility β (sgCRRA σ) (sgOfBdd θ z) at hlt
  nlinarith

/-- **Assumption 15.4**: `Y ∩ S_θ` is convex (concavity of `k ↦ kᵅ`). -/
theorem sg_convex_sgTechθ {θ γ α k0 : ℝ} (hγ : 0 < γ) (hα0 : 0 < α) (hα1 : α < 1) :
    Convex ℝ (sgTechθ θ γ α k0) := by
  intro w hw w' hw' s r hs hr hsr
  obtain ⟨hy, k, hk0, hkn, hcap⟩ := hw
  obtain ⟨hy', k', hk0', hkn', hcap'⟩ := hw'
  refine ⟨fun t => ?_, fun t => s * k t + r * k' t, ?_, fun t => ?_, fun t => ?_⟩
  · rw [sgOfBdd_combo]
    exact add_nonneg (mul_nonneg hs (hy t)) (mul_nonneg hr (hy' t))
  · simp only
    rw [hk0, hk0', ← add_mul, hsr, one_mul]
  · exact add_nonneg (mul_nonneg hs (hkn t)) (mul_nonneg hr (hkn' t))
  · rw [sgOfBdd_combo]
    have hc := (Real.concaveOn_rpow hα0.le hα1.le).2 (show k t ∈ Ici 0 from hkn t)
      (show k' t ∈ Ici 0 from hkn' t) hs hr hsr
    simp only [smul_eq_mul] at hc
    have hγt : 0 ≤ γ ^ t := pow_nonneg hγ.le t
    calc s * k (t + 1) + r * k' (t + 1) + (s * sgOfBdd θ w t + r * sgOfBdd θ w' t)
        = s * (k (t + 1) + sgOfBdd θ w t) + r * (k' (t + 1) + sgOfBdd θ w' t) := by ring
      _ ≤ s * (γ ^ t * k t ^ α) + r * (γ ^ t * k' t ^ α) :=
          add_le_add (mul_le_mul_of_nonneg_left (hcap t) hs)
            (mul_le_mul_of_nonneg_left (hcap' t) hr)
      _ = γ ^ t * (s * k t ^ α + r * k' t ^ α) := by ring
      _ ≤ γ ^ t * (s * k t + r * k' t) ^ α := mul_le_mul_of_nonneg_left hc hγt

/-- `(x, x)` is **Pareto optimal** iff `x` solves the planning problem `max_{X ∩ Y} u`. -/
theorem sg_paretoOptimal_iff {θ a β σ γ α k0 : ℝ} {x : BddSeq ℝ} :
    ParetoOptimal (sgX θ a) (sgU β σ θ) (sgY θ γ α k0) (fun _ => x) (fun _ => x) ↔
      x ∈ sgXa θ a ∩ sgTechθ θ γ α k0 ∧ ∀ z ∈ sgXa θ a ∩ sgTechθ θ γ α k0,
        sgU β σ θ () z ≤ sgU β σ θ () x := by
  constructor
  · rintro ⟨hF, hno⟩
    obtain ⟨hx, hy, -⟩ := sg_feasible_unit.1 hF
    refine ⟨⟨hx, hy⟩, fun z ⟨hzX, hzY⟩ => ?_⟩
    by_contra h
    push Not at h
    exact hno ⟨fun _ => z, fun _ => z, sg_feasible_unit.2 ⟨hzX, hzY, rfl⟩,
      fun _ => h.le, (), h⟩
  · rintro ⟨⟨hx, hy⟩, hmax⟩
    refine ⟨sg_feasible_unit.2 ⟨hx, hy, rfl⟩, ?_⟩
    rintro ⟨x', y', hF', -, i, hi⟩
    obtain ⟨hx', hy', he⟩ := sg_feasible_unit.1 hF'
    have := hmax (x' ()) ⟨hx', he ▸ hy'⟩
    exact absurd hi (not_lt.2 this)

/-- **Exercise 16.3(e)(i)**: if `(x, y, φ)` is a competitive equilibrium of the §16.3 economy
(for any continuous linear price `φ` on `S_θ`), then `x = y` and `(x, y)` is Pareto optimal. -/
theorem ex_16_3e_i {β θ σ a γ α k0 : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) {x y : Unit → BddSeq ℝ}
    {φ : StrongDual ℝ (BddSeq ℝ)}
    (hCE : CompetitiveEq (sgX θ a) (sgU β σ θ) (sgY θ γ α k0) x y φ) :
    x () = y () ∧ ParetoOptimal (sgX θ a) (sgU β σ θ) (sgY θ γ α k0) x y :=
  ⟨(sg_feasible_unit.1 hCE.1).2.2,
    theorem_15_3 (sg_localNonsatiation hσ hβ0 hβ1 hθ hρ1 ha) hCE⟩

/-- A supporting price (condition (3) of Theorem 15.4) is **positive**: `φ(e) ≥ 0` for `e ≥ 0`. -/
theorem sg_support_nonneg {β θ σ a γ α k0 : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) {x y : Unit → BddSeq ℝ}
    {φ : StrongDual ℝ (BddSeq ℝ)}
    (hsup : SupportsAllocation (sgX θ a) (sgU β σ θ) (sgY θ γ α k0) x y φ)
    (hx : x () ∈ sgXa θ a) {e : BddSeq ℝ} (he : ∀ t, 0 ≤ e t) : 0 ≤ φ e := by
  have := hsup.1 () (x () + e) (sgXa_add_nonneg hθ hx he)
    (sg_utility_le_add hσ hβ0 hβ1 hθ hρ1 ha hx he)
  rw [map_add] at this
  linarith

/-- A nonzero positive functional on `ℓ_∞` is positive at `𝟙`. -/
theorem sg_support_one_pos {φ : StrongDual ℝ (BddSeq ℝ)} (hφ : φ ≠ 0)
    (hpos : ∀ e : BddSeq ℝ, (∀ t, 0 ≤ e t) → 0 ≤ φ e) : 0 < φ (sgConst 1) := by
  rcases (hpos (sgConst 1) fun _ => by simp).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hφ
    ext v
    have hc : φ (sgConst ‖v‖) = ‖v‖ * φ (sgConst 1) := by
      rw [show sgConst ‖v‖ = ‖v‖ • sgConst 1 by ext t; simp, map_smul, smul_eq_mul]
    have hv : ∀ t, |v t| ≤ ‖v‖ := fun t => by
      rw [← Real.norm_eq_abs]; exact norm_seq_coord_le v t
    have h1 := hpos (sgConst ‖v‖ - v) fun t => by
      rw [lp.coeFn_sub, Pi.sub_apply, sgConst_apply]
      linarith [le_abs_self (v t), hv t]
    have h2 := hpos (sgConst ‖v‖ + v) fun t => by
      rw [lp.coeFn_add, Pi.add_apply, sgConst_apply]
      linarith [neg_abs_le (v t), hv t]
    rw [map_sub] at h1
    rw [map_add] at h2
    rw [hc, ← h, mul_zero] at h1 h2
    change φ v = 0
    linarith

/-- **Exercise 16.3(e)(ii)**: at `θ = θ̂`, if `(x, x)` is Pareto optimal (i.e. `x` solves the
planning problem, `sg_paretoOptimal_iff`) and the lower bound of `X` does not bind
(`x_t ≥ a′ θᵗ` with `a′ > a`), then there is a continuous linear price `φ` on `S_θ` such that
`(x, x, φ)` is a competitive equilibrium. -/
theorem ex_16_3e_ii {β σ a γ α k0 : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ : 1 < γ)
    (hα0 : 0 < α) (hα1 : α < 1) (hk0 : 0 < k0)
    (hρ1 : β * sgThetaHat γ α ^ (1 - σ) < 1) (ha : 0 < a) {x : BddSeq ℝ}
    (hPO : ParetoOptimal (sgX (sgThetaHat γ α) a) (sgU β σ (sgThetaHat γ α))
      (sgY (sgThetaHat γ α) γ α k0) (fun _ => x) (fun _ => x))
    (hslack : ∃ a' > a, ∀ t, a' ≤ x t) :
    ∃ φ : StrongDual ℝ (BddSeq ℝ), CompetitiveEq (sgX (sgThetaHat γ α) a)
      (sgU β σ (sgThetaHat γ α)) (sgY (sgThetaHat γ α) γ α k0) (fun _ => x) (fun _ => x) φ := by
  set θ := sgThetaHat γ α
  have hθ : 0 < θ := sgThetaHat_pos (by linarith)
  have h1 : Assumption15_1 (sgX θ a) := fun _ => sg_convex_sgXa hθ
  have h2 := sg_assumption15_2 hσ hβ0 hβ1 hθ hρ1 ha
  have h3 : Assumption15_3 (sgX θ a) (sgU β σ θ) := fun _ =>
    ex_16_3d_continuousOn hσ hβ0 hβ1 hθ hρ1 ha
  have h4 : Assumption15_4 (sgY θ γ α k0) := by
    unfold Assumption15_4 sgY
    rw [sg_aggTech_unit]
    exact sg_convex_sgTechθ (by linarith) hα0 hα1
  have h5 : Assumption15_5 (BddSeq ℝ) (sgY θ γ α k0) := by
    left
    unfold sgY
    rw [sg_aggTech_unit]
    exact (ex_16_3b hγ hα0 hα1 hk0 hθ).2 le_rfl
  have hx : x ∈ sgXa θ a := hPO.1.1 ()
  have hxhat : x + sgConst 1 ∈ sgX θ a () := sgXa_add_nonneg hθ hx fun _ => zero_le_one
  have hsat : sgU β σ θ () x < sgU β σ θ () (x + sgConst 1) :=
    sg_utility_lt_add_const hσ hβ0 hβ1 hθ hρ1 ha one_pos hx
  obtain ⟨φ, hφ0, hsup⟩ := theorem_15_4 h1 h2 h3 h4 h5 hPO (h := ()) hxhat hsat
  refine ⟨φ, remark_cheaper_point h1 h3 hPO.1 hsup fun _ => ?_⟩
  obtain ⟨a', ha', hxa'⟩ := hslack
  have hone := sg_support_one_pos hφ0 fun e he => sg_support_nonneg hσ hβ0 hβ1 hθ hρ1 ha hsup
    hx he
  refine ⟨x - sgConst (a' - a), (mem_sgXa_iff hθ).2 fun t => ?_, ?_⟩
  · rw [lp.coeFn_sub, Pi.sub_apply, sgConst_apply]
    linarith [hxa' t]
  · have hc : φ (sgConst (a' - a)) = (a' - a) * φ (sgConst 1) := by
      rw [show sgConst (a' - a) = (a' - a) • sgConst 1 by ext t; simp, map_smul, smul_eq_mul]
    rw [map_sub, hc]
    have : 0 < (a' - a) * φ (sgConst 1) := mul_pos (by linarith) hone
    linarith

end StokeyLucasPrescott.EquilibriumApplications
