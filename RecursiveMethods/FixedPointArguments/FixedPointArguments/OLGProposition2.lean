/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.OLGModel
import FixedPointArguments.OLGContraction

/-!
# Proposition 2: the OLG model by the contraction mapping theorem

SLP §17.2, pp. 510–516: Exercise 17.3, Assumption 17.2 and Proposition 2.

* **Exercise 17.3** (`ex_17_3`, p. 510): under Assumption 17.1, `G(x, x', y) = φ[x' ζ⁻¹(y)]`
  violates condition (2) of Lemma 17.1 on `D = ℝ₊` (no derivative bound `|G₃| ≤ β < 1`).
* **Assumption 17.2** as stated (`Assumption17_2`, p. 513) and repaired (`Assumption17_2R`, the
  bounds (5) for `y > 0` only); the repaired utility assumption `Assumption17_1VR` (`V`
  continuous on `ℝ₊`, `C²` on `(0, ∞)`).
* `crra_assumption17_1VR`, `crra_assumption17_2R`: `V(y) = y^{1−σ}/(1 − σ)`, `0 < σ < 1`,
  satisfies both repaired assumptions (relative risk aversion `≡ σ`, `β = 1 − σ`);
  `repaired_assumptions_nonvacuous`.
* `proposition_1_repaired`: Proposition 1 still holds under the repaired utility assumption
  (`V'(0+) = ∞` allowed), as the transcription's NOTE claims.
* **Proposition 2** (`proposition_2`, p. 513), under the repaired assumptions: exactly one
  bounded continuous strictly positive solution `f*` of (6). Proof steps: `olgG_ge` ((7)),
  `olgG_hyp` (step 4), `olgG_hasDerivAt`, `olgG_elasticity_le` (step 5, condition (4)), then
  `lemma_17_2_fixedPoint`.

**Correction (Assumption 17.2 contradicts Assumption 17.1).** At `y = 0` the middle term of (5)
is `0 < 1 − β`, so Assumption 17.2 never holds (`assumption17_2_counterexample`) and Proposition
2 as stated is vacuous. Restricting (5) to `y > 0` does not help under Assumption 17.1: the lower
bound forces `V'(0+) = ∞` (`assumption17_2R_inconsistent`). The repair (NOTE in the
transcription): `V` only `C²` on `(0, ∞)` and (5) only for `y > 0`; Proposition 2 is proved
under it.

**Correction (Proposition 2, zero fixed point and uniqueness).** `f ≡ 0` also solves (6)
(`proposition_2_zero_fixedPoint`), so uniqueness holds only among strictly positive solutions
(`proposition_2_nonneg_counterexample`). The book's "any `K > 1/C` could have been used" needs
`ε_k → 0`, which it does not state; it is true (`epsK_exists`, `epsK_tendsto_zero`:
`ζ⁻¹(ε_k) = k ε_k < L`). `proposition_2` uses instead the sets `[ζ(l), ∞)`, `0 < l ≤ l₀`, which
exhaust `(0, ∞)` as `l → 0`.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- For every `C > 0` there is `l ∈ (0, L)` with `H'(l) < C` (`H'` is continuous with
`H'(0) = 0`). -/
theorem Assumption17_1H.exists_H'_lt (hH : Assumption17_1H L H H' H'') {C : ℝ} (hC : 0 < C) :
    ∃ l ∈ Ioo 0 L, H' l < C := by
  have hcont := hH.H'_continuousOn 0 (left_mem_Ico.2 hH.L_pos)
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, h⟩ := hcont C hC
  set l := min (δ / 2) (L / 2) with hl
  have hl0 : 0 < l := lt_min (half_pos hδ) (half_pos hH.L_pos)
  have hlL : l < L := (min_le_right _ _).trans_lt (half_lt_self hH.L_pos)
  have hlδ : l < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  refine ⟨l, ⟨hl0, hlL⟩, ?_⟩
  have := h ⟨hl0.le, hlL⟩ (by rw [Real.dist_eq, sub_zero, abs_of_pos hl0]; exact hlδ)
  rw [Real.dist_eq, hH.H'_zero, sub_zero] at this
  exact (le_abs_self _).trans_lt this

/-! ### Exercise 17.3 -/

/-- **Exercise 17.3** (p. 510). Under Assumption 17.1, with `X = [a, b]` (`0 < a ≤ b`),
`D = ℝ₊` and `G(x, x', y) = φ[x' ζ⁻¹(y)]`, condition (2) of Lemma 17.1 fails: there is no
`β < 1` and no derivative `G₃` of `G(x, x', ·)` on `ℝ₊` with `|G₃| ≤ β`. Indeed (2) would make
`G(x, x', ·)` `β`-Lipschitz, but `G(x, x', 0) = 0` while `G(x, x', ζ(l)) ≥ a l V'(aL) > ζ(l)`
for small `l > 0`. (The manual writes `1/ζ'(y)` for `(ζ⁻¹)'(y) = 1/ζ'(ζ⁻¹(y))`.) -/
theorem ex_17_3 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hA : Assumption17_1 L H H' H'' V V' V'') :
    ¬ ∃ β < 1, ∃ G3 : Icc a b → Icc a b → ℝ → ℝ,
      (∀ x x', ∀ y ∈ Ici (0 : ℝ), HasDerivWithinAt (fun y => olgPhi V' (x'.1 * olgZetaInv L H' y))
        (G3 x x' y) (Ici 0) y) ∧ ∀ x x', ∀ y ∈ Ici (0 : ℝ), |G3 x x' y| ≤ β := by
  rintro ⟨β, hβ, G3, hder, hbd⟩
  have hH := hA.hH
  have hV := hA.hV
  set x₀ : Icc a b := ⟨a, le_rfl, hab⟩
  have hC : 0 < a * V' (a * L) := mul_pos ha (hV.V'_pos (mul_pos ha hH.L_pos).le)
  obtain ⟨l, hl, hlC⟩ := hH.exists_H'_lt hC
  have hy : 0 ≤ olgZeta H' l := (hH.zeta_pos hl).le
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (hder x₀ x₀)
    (fun y hy => by rw [Real.norm_eq_abs]; exact hbd x₀ x₀ y hy) (convex_Ici 0)
    (mem_Ici.2 le_rfl) (mem_Ici.2 hy)
  rw [hH.zetaInv_zeta (Ioo_subset_Ico_self hl), hH.zetaInv_zero, mul_zero, sub_zero,
    Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hx0 : (x₀ : ℝ) = a := rfl
  simp only [olgPhi, zero_mul, sub_zero, hx0] at hmvt
  have hal : 0 < a * l := mul_pos ha hl.1
  have hV'le : V' (a * L) ≤ V' (a * l) :=
    hV.V'_strictAntiOn.antitoneOn (mem_Ici.2 hal.le) (mem_Ici.2 (mul_pos ha hH.L_pos).le)
      (mul_le_mul_of_nonneg_left hl.2.le ha.le)
  have hpos : 0 < a * l * V' (a * l) := mul_pos hal (hV.V'_pos hal.le)
  rw [abs_of_pos hpos, abs_of_nonneg hy] at hmvt
  have h1 : olgZeta H' l < a * l * V' (a * l) := by
    simp only [olgZeta]
    have : l * H' l < l * (a * V' (a * L)) := mul_lt_mul_of_pos_left hlC hl.1
    nlinarith
  have h2 : β * olgZeta H' l ≤ olgZeta H' l := by
    rcases le_or_gt β 0 with h | h
    · nlinarith
    · nlinarith
  linarith

/-! ### Assumption 17.2 and its inconsistency with Assumption 17.1 -/

/-- **Assumption 17.2** (p. 513), as stated: for some `β ∈ [0, 1)`,
`1 − β ≤ −y V''(y)/V'(y) ≤ 1 + β` for all `y ∈ ℝ₊`. -/
structure Assumption17_2 (β : ℝ) (V' V'' : ℝ → ℝ) : Prop where
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  lower : ∀ y, 0 ≤ y → 1 - β ≤ -(y * V'' y) / V' y
  upper : ∀ y, 0 ≤ y → -(y * V'' y) / V' y ≤ 1 + β

/-- **Assumption 17.2, repaired**: the bounds (5) only for `y > 0`. -/
structure Assumption17_2R (β : ℝ) (V' V'' : ℝ → ℝ) : Prop where
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  lower : ∀ y, 0 < y → 1 - β ≤ -(y * V'' y) / V' y
  upper : ∀ y, 0 < y → -(y * V'' y) / V' y ≤ 1 + β

/-- **Correction (Assumption 17.2).** As stated, Assumption 17.2 can never hold: at `y = 0`
the middle term of (5) is `−0 · V''(0)/V'(0) = 0 < 1 − β`. Hence no `(H, V)` satisfies
Assumptions 17.1 and 17.2, and Proposition 2 as stated is vacuous. -/
theorem assumption17_2_counterexample {β : ℝ} : ¬ Assumption17_2 β V' V'' := fun h => by
  have := h.lower 0 le_rfl
  simp only [zero_mul, neg_zero, zero_div] at this
  linarith [h.β_lt_one]

/-- **Correction (Assumption 17.2), continued.** Restricting (5) to `y > 0` does not reconcile it
with Assumption 17.1 either: the lower bound forces `V'(y) ≥ V'(1) y^{−(1−β)} → ∞` as `y ↓ 0`,
while under Assumption 17.1 `V'` is bounded by `V'(0)`. Proof: `u(t) = ln V'(t) + (1 − β) ln t`
is nonincreasing on `(0, ∞)`. -/
theorem assumption17_2R_inconsistent (hV : Assumption17_1V V V' V'') {β : ℝ} :
    ¬ Assumption17_2R β V' V'' := fun h => by
  have hβ : 0 < 1 - β := sub_pos.2 h.β_lt_one
  set u : ℝ → ℝ := fun t => Real.log (V' t) + (1 - β) * Real.log t with hu
  have hderiv : ∀ t, 0 < t → HasDerivAt u (V'' t / V' t + (1 - β) * t⁻¹) t := fun t ht => by
    have h1 : HasDerivAt V' (V'' t) t := (hV.V'_deriv t ht.le).hasDerivAt (Ici_mem_nhds ht)
    exact (h1.log (hV.V'_pos ht.le).ne').add ((Real.hasDerivAt_log ht.ne').const_mul (1 - β))
  have hanti : AntitoneOn u (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) (fun t ht =>
      (hderiv t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Ioi] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi] at ht
      rw [(hderiv t ht).deriv]
      have hl := h.lower t ht
      have hVp := hV.V'_pos ht.le
      rw [le_div_iff₀ hVp] at hl
      rw [div_add' _ _ _ hVp.ne', div_nonpos_iff]
      right
      refine ⟨?_, hVp.le⟩
      have : (1 - β) * t⁻¹ * V' t ≤ -V'' t := by
        rw [mul_comm (1 - β), mul_assoc, ← le_div_iff₀' (inv_pos.2 ht), div_inv_eq_mul]
        nlinarith
      linarith
  have hV0 := hV.V'_pos (le_refl (0 : ℝ))
  have hV1 := hV.V'_pos (zero_le_one' ℝ)
  have hle : V' 1 ≤ V' 0 := hV.V'_le_V'_zero zero_le_one
  set M := (Real.log (V' 0) - Real.log (V' 1) + 1) / (1 - β) with hM
  have hMpos : 0 < M := div_pos (by linarith [Real.log_le_log hV1 hle]) hβ
  set t := Real.exp (-M)
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have key := hanti (mem_Ioi.2 ht) (mem_Ioi.2 one_pos) ht1
  simp only [hu, Real.log_one, mul_zero, add_zero] at key
  have hlt : Real.log t = -M := Real.log_exp _
  have e : (1 - β) * -M = -(Real.log (V' 0) - Real.log (V' 1) + 1) := by
    rw [hM]; field_simp
  rw [hlt, e] at key
  have hVt : V' t ≤ V' 0 := hV.V'_le_V'_zero ht.le
  have := Real.log_le_log (hV.V'_pos ht.le) hVt
  linarith

/-! ### Repaired Assumption 17.1 -/

/-- **Assumption 17.1, utility part, repaired**: `V : ℝ₊ → ℝ₊` continuous, strictly increasing
and strictly concave, and twice continuously differentiable on `ℝ₊₊ = (0, ∞)` only (so
`V'(0+) = +∞` is allowed). -/
structure Assumption17_1VR (V V' V'' : ℝ → ℝ) : Prop where
  V_nonneg : ∀ y, 0 ≤ y → 0 ≤ V y
  V_cont : ContinuousOn V (Ici 0)
  V_deriv : ∀ y, 0 < y → HasDerivAt V (V' y) y
  V'_deriv : ∀ y, 0 < y → HasDerivAt V' (V'' y) y
  V''_cont : ContinuousOn V'' (Ioi 0)
  V_mono : StrictMonoOn V (Ici 0)
  V_conc : StrictConcaveOn ℝ (Ici 0) V

namespace Assumption17_1VR

variable (hV : Assumption17_1VR V V' V'')
include hV

/-- `V'(y) > 0` for `y > 0`. -/
theorem V'_pos {y : ℝ} (hy : 0 < y) : 0 < V' y := by
  have hy' : y ∈ Ici (0 : ℝ) := mem_Ici.2 hy.le
  have hy1 : y + 1 ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have h1 := hV.V_conc.slope_lt_of_hasDerivWithinAt hy' hy1 (by linarith)
    (hV.V_deriv y hy).hasDerivWithinAt
  have h2 : 0 < slope V y (y + 1) := by
    rw [slope_def_field]
    exact div_pos (sub_pos.2 (hV.V_mono hy' hy1 (by linarith))) (by linarith)
  linarith

/-- `V'` is strictly decreasing on `(0, ∞)`. -/
theorem V'_strictAntiOn : StrictAntiOn V' (Ioi 0) := fun x hx y hy hxy =>
  (hV.V_conc.slope_lt_of_hasDerivWithinAt (mem_Ici.2 (le_of_lt hx)) (mem_Ici.2 (le_of_lt hy))
    hxy (hV.V_deriv x hx).hasDerivWithinAt).trans'
    (hV.V_conc.lt_slope_of_hasDerivWithinAt (mem_Ici.2 (le_of_lt hx)) (mem_Ici.2 (le_of_lt hy))
      hxy (hV.V_deriv y hy).hasDerivWithinAt)

/-- `V'` is continuous on `(0, ∞)`. -/
theorem V'_continuousOn : ContinuousOn V' (Ioi 0) := fun y hy =>
  (hV.V'_deriv y hy).continuousAt.continuousWithinAt

/-- `φ(y) = y V'(y)` is continuous on `(0, ∞)`. -/
theorem phi_continuousOn : ContinuousOn (olgPhi V') (Ioi 0) :=
  continuousOn_id.mul hV.V'_continuousOn

/-- `φ'(y) = V'(y) + y V''(y)` for `y > 0`. -/
theorem phi_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (olgPhi V') (V' y + y * V'' y) y :=
  ((hasDerivAt_id' y).mul (hV.V'_deriv y hy)).congr_deriv (by ring)

end Assumption17_1VR

/-- **Example satisfying the repaired assumptions.** For `0 < σ < 1`,
`V(y) = y^{1−σ}/(1 − σ)` (with `V'(y) = y^{−σ}`, `V''(y) = −σ y^{−σ−1}`) satisfies the
repaired utility part of Assumption 17.1. -/
theorem crra_assumption17_1VR {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Assumption17_1VR (fun y => y ^ (1 - σ) / (1 - σ)) (fun y => y ^ (-σ))
      (fun y => -σ * y ^ (-σ - 1)) := by
  have hc : 0 < 1 - σ := sub_pos.2 hσ1
  refine ⟨fun y hy => div_nonneg (Real.rpow_nonneg hy _) hc.le,
    ((Real.continuous_rpow_const hc.le).div_const _).continuousOn, fun y hy => ?_,
    fun y hy => ?_, ?_, fun x hx y hy hxy => ?_, ?_⟩
  · have := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hy.ne')).div_const (1 - σ)
    convert this using 1
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp
  · have := Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hy.ne')
    exact this
  · intro y hy
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const y _
      (Or.inl (ne_of_gt hy)))).continuousWithinAt
  · exact div_lt_div_of_pos_right (Real.rpow_lt_rpow hx hxy hc) hc
  · refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have := (Real.strictConcaveOn_rpow hc (by linarith : 1 - σ < 1)).2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at this ⊢
    calc a * (x ^ (1 - σ) / (1 - σ)) + b * (y ^ (1 - σ) / (1 - σ))
        = (a * x ^ (1 - σ) + b * y ^ (1 - σ)) / (1 - σ) := by ring
      _ < (a * x + b * y) ^ (1 - σ) / (1 - σ) := div_lt_div_of_pos_right this hc

/-- The CRRA example has constant relative risk aversion `σ` and satisfies the repaired
Assumption 17.2 with `β = 1 − σ`. -/
theorem crra_assumption17_2R {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Assumption17_2R (1 - σ) (fun y => y ^ (-σ)) (fun y => -σ * y ^ (-σ - 1)) := by
  have hrra : ∀ y : ℝ, 0 < y → -(y * (-σ * y ^ (-σ - 1))) / y ^ (-σ) = σ := fun y hy => by
    have h1 : y * y ^ (-σ - 1) = y ^ (-σ) := by
      rw [Real.rpow_sub_one hy.ne', mul_div_cancel₀ _ hy.ne']
    have h2 : 0 < y ^ (-σ) := Real.rpow_pos_of_pos hy _
    rw [show -(y * (-σ * y ^ (-σ - 1))) = σ * (y * y ^ (-σ - 1)) by ring, h1,
      mul_div_assoc, div_self h2.ne', mul_one]
  refine ⟨by linarith, by linarith, fun y hy => ?_, fun y hy => ?_⟩
  · rw [hrra y hy]; linarith
  · rw [hrra y hy]; linarith

/-- The repaired assumptions are not vacuous: `olgExH` (with `L = 2`) and the CRRA utility with
`σ = 1/2` satisfy all of them. -/
theorem repaired_assumptions_nonvacuous :
    ∃ (L : ℝ) (H H' H'' V V' V'' : ℝ → ℝ) (β : ℝ), Assumption17_1H L H H' H'' ∧
      Assumption17_1VR V V' V'' ∧ Assumption17_2R β V' V'' :=
  ⟨2, olgExH, olgExH1, olgExH2, _, _, _, _, olgExH_assumption,
    crra_assumption17_1VR (σ := 1 / 2) (by norm_num) (by norm_num),
    crra_assumption17_2R (σ := 1 / 2) (by norm_num) (by norm_num)⟩

/-! ### Proposition 1 survives the repair -/

/-- Under the repaired Assumption 17.1, `x' ↦ x' V'(l x')` is a bounded continuous function on
`X = [a, b]` for `l > 0`. -/
noncomputable def olgMargBCF {a b : ℝ} (ha : 0 < a) (hV : Assumption17_1VR V V' V'') {l : ℝ}
    (hl : 0 < l) : Icc a b →ᵇ ℝ :=
  mkOfCompact ⟨fun x' => x'.1 * V' (l * x'.1), continuous_subtype_val.mul
    (hV.V'_continuousOn.comp_continuous (continuous_const.mul continuous_subtype_val)
      fun x' => mul_pos hl (ha.trans_le x'.2.1))⟩

/-- Under the repaired Assumption 17.1, `l ↦ ∫ x' V'(l x') dμ` is continuous on `(0, ∞)`. -/
theorem continuousOn_margUtil_R {a b : ℝ} (ha : 0 < a) (hV : Assumption17_1VR V V' V'')
    (μ : Measure (Icc a b)) [IsProbabilityMeasure μ] :
    ContinuousOn (margUtil V' μ (fun x' : Icc a b => x'.1)) (Ioi 0) := by
  intro l₀ hl₀
  have hl₀' : 0 < l₀ := hl₀
  have hs : Ioi (l₀ / 2) ∈ 𝓝 l₀ := Ioi_mem_nhds (by linarith)
  refine (ContinuousOn.continuousAt ?_ hs).continuousWithinAt
  refine continuousOn_of_dominated (bound := fun _ => b * V' (l₀ / 2 * a))
    (fun l hl => (olgMargBCF ha hV (lt_trans (half_pos hl₀') hl)).integrable μ
      |>.aestronglyMeasurable) (fun l hl => ae_of_all _ fun x' => ?_) (integrable_const _)
    (ae_of_all _ fun x' => ?_)
  · have hl' : l₀ / 2 < l := hl
    have hx : 0 < x'.1 := ha.trans_le x'.2.1
    have hlx : 0 < l * x'.1 := mul_pos (lt_trans (half_pos hl₀') hl') hx
    have h1 : l₀ / 2 * a ≤ l * x'.1 := mul_le_mul hl'.le x'.2.1 ha.le (by linarith)
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hx (hV.V'_pos hlx))]
    exact mul_le_mul x'.2.2 (hV.V'_strictAntiOn.antitoneOn (mul_pos (half_pos hl₀') ha) hlx h1)
      (hV.V'_pos hlx).le ((ha.trans_le x'.2.1).le.trans x'.2.2)
  · have hx : 0 < x'.1 := ha.trans_le x'.2.1
    exact continuousOn_const.mul (hV.V'_continuousOn.comp (continuousOn_id.mul continuousOn_const)
      fun l hl => mul_pos (lt_trans (half_pos hl₀') hl) hx)

/-- Under the repaired Assumption 17.1, `l ↦ ∫ x' V'(l x') dμ` is strictly decreasing on
`(0, ∞)`. -/
theorem margUtil_R_strictAntiOn {a b : ℝ} (ha : 0 < a) (hV : Assumption17_1VR V V' V'')
    (μ : Measure (Icc a b)) [IsProbabilityMeasure μ] :
    StrictAntiOn (margUtil V' μ (fun x' : Icc a b => x'.1)) (Ioi 0) := by
  intro l₁ hl₁ l₂ hl₂ hlt
  have i1 : Integrable (fun x' : Icc a b => x'.1 * V' (l₁ * x'.1)) μ :=
    (olgMargBCF ha hV hl₁).integrable μ
  have i2 : Integrable (fun x' : Icc a b => x'.1 * V' (l₂ * x'.1)) μ :=
    (olgMargBCF ha hV hl₂).integrable μ
  rw [← sub_pos, margUtil, margUtil, ← integral_sub i1 i2]
  refine integral_pos_of_forall_pos (i1.sub i2) fun x' => ?_
  have hx : 0 < x'.1 := ha.trans_le x'.2.1
  change 0 < x'.1 * V' (l₁ * x'.1) - x'.1 * V' (l₂ * x'.1)
  rw [← mul_sub]
  exact mul_pos hx (sub_pos.2 (hV.V'_strictAntiOn (mul_pos hl₁ hx) (mul_pos hl₂ hx)
    (mul_lt_mul_of_pos_right hlt hx)))

/-- **Proposition 1 under the repaired assumptions** (the transcription's NOTE: Proposition 1
survives the repair). With `V` only `C²` on `(0, ∞)` (so `V'(0+) = ∞` is allowed), (5) still
has exactly one solution in `(0, L)`; existence now uses `∫ x' V'(x' l) dμ ≥ a V'(bL)` on
`(0, L)` while `H'(l) → 0` as `l → 0`. -/
theorem proposition_1_repaired {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (μ : Measure (Icc a b)) [IsProbabilityMeasure μ] :
    ∃! n, n ∈ Ioo 0 L ∧ olgZeta H' n = ∫ x', olgPhi V' (x'.1 * n) ∂μ := by
  have hb : 0 < b := ha.trans_le hab
  set m := margUtil V' μ (fun x' : Icc a b => x'.1)
  have hiff : ∀ l, 0 < l → (olgZeta H' l = ∫ x', olgPhi V' (x'.1 * l) ∂μ ↔ H' l = m l) :=
    fun l hl => by
      rw [integral_olgPhi, olgZeta]
      exact ⟨fun h => mul_left_cancel₀ hl.ne' h, fun h => by rw [h]⟩
  have hfoc : StrictMonoOn (fun l => H' l - m l) (Ioo 0 L) := fun x hx y hy hxy => by
    have h1 := hH.H'_strictMonoOn (Ioo_subset_Ico_self hx) (Ioo_subset_Ico_self hy) hxy
    have h2 := margUtil_R_strictAntiOn ha hV μ (mem_Ioi.2 hx.1) (mem_Ioi.2 hy.1) hxy
    linarith
  have hlow : ∀ l ∈ Ioo 0 L, a * V' (b * L) ≤ m l := fun l hl => by
    have i : Integrable (fun x' : Icc a b => x'.1 * V' (l * x'.1)) μ :=
      (olgMargBCF ha hV hl.1).integrable μ
    have h := integral_mono (integrable_const (a * V' (b * L))) i fun x' => by
        have hx : 0 < x'.1 := ha.trans_le x'.2.1
        have hlx : 0 < l * x'.1 := mul_pos hl.1 hx
        change a * V' (b * L) ≤ x'.1 * V' (l * x'.1)
        exact mul_le_mul x'.2.1 (hV.V'_strictAntiOn.antitoneOn hlx
          (mem_Ioi.2 (mul_pos hb hH.L_pos))
          (by rw [mul_comm b L]; exact mul_le_mul hl.2.le x'.2.2 hx.le hH.L_pos.le))
          (hV.V'_pos (mul_pos hb hH.L_pos)).le hx.le
    simpa [m, margUtil] using h
  obtain ⟨l₀, hl₀, hl₀C⟩ := hH.exists_H'_lt (mul_pos ha (hV.V'_pos (mul_pos hb hH.L_pos)))
  obtain ⟨l₁, hl₁, hl₁M⟩ := hH.exists_H'_gt (m l₀)
  have h0 : H' l₀ - m l₀ < 0 := by linarith [hlow l₀ hl₀]
  have hlt : l₀ < l₁ := by
    by_contra h
    have := hH.H'_strictMonoOn.monotoneOn (Ioo_subset_Ico_self hl₁) (Ioo_subset_Ico_self hl₀)
      (not_lt.1 h)
    linarith [hlow l₀ hl₀]
  have h1 : 0 < H' l₁ - m l₁ := by
    have := margUtil_R_strictAntiOn ha hV μ (mem_Ioi.2 hl₀.1) (mem_Ioi.2 hl₁.1) hlt
    linarith
  have hsub : Icc l₀ l₁ ⊆ Ioo 0 L := fun y hy => ⟨hl₀.1.trans_le hy.1, hy.2.trans_lt hl₁.2⟩
  have hcont : ContinuousOn (fun l => H' l - m l) (Icc l₀ l₁) :=
    (hH.H'_continuousOn.mono (hsub.trans Ioo_subset_Ico_self)).sub
      ((continuousOn_margUtil_R ha hV μ).mono fun y hy => (hsub hy).1)
  obtain ⟨n, hn, hn0⟩ := intermediate_value_Icc hlt.le hcont ⟨h0.le, h1.le⟩
  have hnL := hsub hn
  refine ⟨n, ⟨hnL, (hiff n hnL.1).2 (by linarith [hn0])⟩, fun k hk => ?_⟩
  have hk' := (hiff k hk.1.1).1 hk.2
  refine hfoc.injOn hk.1 hnL ?_
  rw [hk', sub_self]
  exact hn0.symm

/-! ### Proposition 2 -/

/-- The kernel function `G(x, x', y) = φ[x' ζ⁻¹(y)]` of the OLG operator (9) (p. 509). -/
noncomputable def olgG {a b : ℝ} (L : ℝ) (H' V' : ℝ → ℝ) (_x x' : Icc a b) (y : ℝ) : ℝ :=
  olgPhi V' (x'.1 * olgZetaInv L H' y)

/-- **Step 2 of the proof of Proposition 2, (7).** Let `C = a V'(bL)` and `H'(l₀) < C`. For
`0 < l ≤ l₀` and `y ≥ ζ(l)`, `G(x, x', y) ≥ a l V'(bL) > ζ(l)`, so `G` maps `[ζ(l), ∞)` into
itself. -/
theorem olgG_ge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') {l₀ : ℝ} (hl₀ : l₀ ∈ Ioo 0 L)
    (hC : H' l₀ < a * V' (b * L)) {l : ℝ} (hl : l ∈ Ioc 0 l₀) {y : ℝ}
    (hy : olgZeta H' l ≤ y) (x x' : Icc a b) : olgZeta H' l ≤ olgG L H' V' x x' y := by
  have hb : 0 < b := ha.trans_le hab
  have hl' : l ∈ Ioo 0 L := ⟨hl.1, hl.2.trans_lt hl₀.2⟩
  have hzl := hH.zeta_pos hl'
  have hy0 : 0 < y := hzl.trans_le hy
  set m := olgZetaInv L H' y
  have hm : m ∈ Ico 0 L := hH.zetaInv_mem hy0.le
  have hlm : l ≤ m := by
    have := hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 hzl.le) (mem_Ici.2 hy0.le) hy
    rwa [hH.zetaInv_zeta (Ioo_subset_Ico_self hl')] at this
  have hx' : a ≤ x'.1 := x'.2.1
  have hz1 : a * l ≤ x'.1 * m := mul_le_mul hx' hlm hl.1.le (ha.le.trans hx')
  have hz0 : 0 < x'.1 * m := (mul_pos ha hl.1).trans_le hz1
  have hz2 : x'.1 * m < b * L :=
    (mul_le_mul_of_nonneg_right x'.2.2 hm.1).trans_lt (mul_lt_mul_of_pos_left hm.2 hb)
  have hV' : V' (b * L) ≤ V' (x'.1 * m) :=
    hV.V'_strictAntiOn.antitoneOn hz0 (mem_Ioi.2 (mul_pos hb hH.L_pos)) hz2.le
  have hVbL := hV.V'_pos (mul_pos hb hH.L_pos)
  have hH'l : H' l ≤ H' l₀ := hH.H'_strictMonoOn.monotoneOn (Ioo_subset_Ico_self hl')
    (Ioo_subset_Ico_self hl₀) hl.2
  simp only [olgG, olgPhi, olgZeta]
  calc l * H' l ≤ l * (a * V' (b * L)) := mul_le_mul_of_nonneg_left (hH'l.trans hC.le) hl.1.le
    _ = a * l * V' (b * L) := by ring
    _ ≤ x'.1 * m * V' (x'.1 * m) := mul_le_mul hz1 hV' hVbL.le hz0.le

/-- **Step 4 of the proof of Proposition 2.** The hypotheses of Exercise 17.2a hold for `G` on
`D = [ζ(l), ∞)`, `0 < l ≤ l₀`. -/
theorem olgG_hyp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') {l₀ : ℝ} (hl₀ : l₀ ∈ Ioo 0 L)
    (hC : H' l₀ < a * V' (b * L)) {l : ℝ} (hl : l ∈ Ioc 0 l₀) {κ : Kernel (Icc a b) (Icc a b)}
    (hκ : IsFellerKernel κ) : OLGOperatorHyp (Ici (olgZeta H' l)) (olgG L H' V') κ := by
  have hzl := hH.zeta_pos ⟨hl.1, hl.2.trans_lt hl₀.2⟩
  refine ⟨convex_Ici _, ?_, fun x x' y hy => olgG_ge ha hab hH hV hl₀ hC hl hy x x', hκ⟩
  have hin : ContinuousOn (fun p : Icc a b × Icc a b × ℝ => p.2.1.1 * olgZetaInv L H' p.2.2)
      {p | p.2.2 ∈ Ici (olgZeta H' l)} :=
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).continuousOn.mul
      (hH.zetaInv_continuousOn.comp (continuous_snd.comp continuous_snd).continuousOn
        fun p hp => mem_Ici.2 (hzl.le.trans hp))
  exact hV.phi_continuousOn.comp hin fun p hp =>
    mul_pos (ha.trans_le p.2.1.2.1) (hH.zetaInv_pos (hzl.trans_le hp))

/-- **Step 4, differentiability.** For `y > 0`, `G(x, x', ·)` has derivative
`G₃ = φ'(x' ζ⁻¹(y)) · x' / ζ'(ζ⁻¹(y))`. -/
theorem olgG_hasDerivAt {a b : ℝ} (ha : 0 < a) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') (x x' : Icc a b) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (olgG L H' V' x x')
      ((V' (x'.1 * olgZetaInv L H' y) + x'.1 * olgZetaInv L H' y *
          V'' (x'.1 * olgZetaInv L H' y)) *
        (x'.1 * (H' (olgZetaInv L H' y) + olgZetaInv L H' y * H'' (olgZetaInv L H' y))⁻¹)) y := by
  have hz : 0 < x'.1 * olgZetaInv L H' y := mul_pos (ha.trans_le x'.2.1) (hH.zetaInv_pos hy)
  exact (hV.phi_hasDerivAt hz).comp y ((hH.zetaInv_hasDerivAt hy).const_mul x'.1)

/-- **Step 5 of the proof of Proposition 2.** Under the repaired Assumption 17.2, the elasticity
bound (4) holds: `|y G₃/G| = |x'ζ⁻¹ φ'/φ| · |y (ζ⁻¹)'/ζ⁻¹| ≤ β · 1` for `y > 0`. -/
theorem olgG_elasticity_le {a b : ℝ} (ha : 0 < a) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') {β : ℝ} (h2 : Assumption17_2R β V' V'') (x x' : Icc a b)
    {y : ℝ} (hy : 0 < y) :
    |y * ((V' (x'.1 * olgZetaInv L H' y) + x'.1 * olgZetaInv L H' y *
          V'' (x'.1 * olgZetaInv L H' y)) *
        (x'.1 * (H' (olgZetaInv L H' y) + olgZetaInv L H' y * H'' (olgZetaInv L H' y))⁻¹)) /
      olgG L H' V' x x' y| ≤ β := by
  set m := olgZetaInv L H' y with hmdef
  have hm : m ∈ Ioo 0 L := ⟨hH.zetaInv_pos hy, (hH.zetaInv_mem hy.le).2⟩
  have hx' : 0 < x'.1 := ha.trans_le x'.2.1
  set z := x'.1 * m with hzdef
  have hz : 0 < z := mul_pos hx' hm.1
  have hVz := hV.V'_pos hz
  have hH'm := hH.H'_pos hm
  have hH''m := hH.H''_nonneg hm
  have hζ' := hH.zeta_deriv_pos hm
  have hyz : y = m * H' m := (hH.zeta_zetaInv hy.le).symm
  have e : y * ((V' z + z * V'' z) * (x'.1 * (H' m + m * H'' m)⁻¹)) / olgG L H' V' x x' y =
      (H' m / (H' m + m * H'' m)) * (1 - -(z * V'' z) / V' z) := by
    simp only [olgG, olgPhi]
    rw [← hmdef, ← hzdef, hyz]
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos (div_pos hH'm hζ')]
  have hle1 : H' m / (H' m + m * H'' m) ≤ 1 :=
    (div_le_one hζ').2 (le_add_of_nonneg_right (mul_nonneg hm.1.le hH''m))
  have hr : |1 - -(z * V'' z) / V' z| ≤ β := by
    rw [abs_le]
    constructor <;> linarith [h2.lower z hz, h2.upper z hz]
  calc H' m / (H' m + m * H'' m) * |1 - -(z * V'' z) / V' z|
      ≤ 1 * β := mul_le_mul hle1 hr (abs_nonneg _) zero_le_one
    _ = β := one_mul β

/-- **Proposition 2** (p. 513), under the repaired assumptions (see
`assumption17_2_counterexample`, `assumption17_2R_inconsistent`). Let `X = [a, b]`,
`0 < a ≤ b`, `π` a Feller transition function, `H` as in Assumption 17.1, `V` as in the
repaired Assumption 17.1 (`Assumption17_1VR`) and the repaired Assumption 17.2. Then there is
exactly one bounded continuous strictly positive `f* : X → ℝ₊₊` with
`f*(x) = ∫ φ[x' ζ⁻¹(f*(x'))] π(x, dx')` (6).

The proof applies Lemma 17.2 on `D = [ζ(l), ∞)`. The book's `ε_K` (any `K > 1/C`) is replaced
by `ζ(l)` for `0 < l ≤ l₀`, where `H'(l₀) < C = a V'(bL)`; since `ζ(l) → 0` as `l → 0`, every
strictly positive continuous solution (whose minimum on compact `X` is positive) lies in some
such `D`, where the fixed point is unique. -/
theorem proposition_2 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') {β : ℝ} (h2 : Assumption17_2R β V' V'')
    (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ] (hκ : IsFellerKernel κ) :
    ∃! f : Icc a b →ᵇ ℝ, (∀ x, 0 < f x) ∧
      ∀ x, f x = ∫ x', olgPhi V' (x'.1 * olgZetaInv L H' (f x')) ∂κ x := by
  have hb : 0 < b := ha.trans_le hab
  have hC : 0 < a * V' (b * L) := mul_pos ha (hV.V'_pos (mul_pos hb hH.L_pos))
  obtain ⟨l₀, hl₀, hl₀C⟩ := hH.exists_H'_lt hC
  have hfix : ∀ l ∈ Ioc 0 l₀, ∃! f : Icc a b →ᵇ ℝ, (∀ x, f x ∈ Ici (olgZeta H' l)) ∧
      ∀ x, f x = olgOpT (olgG L H' V') κ f x := fun l hl => by
    have hzl := hH.zeta_pos ⟨hl.1, hl.2.trans_lt hl₀.2⟩
    exact lemma_17_2_fixedPoint (olgG_hyp ha hab hH hV hl₀ hl₀C hl hκ) isClosed_Ici
      nonempty_Ici (fun y hy => hzl.trans_le hy) h2.β_nonneg h2.β_lt_one
      (fun x x' y hy => (olgG_hasDerivAt ha hH hV x x' (hzl.trans_le hy)).hasDerivWithinAt)
      (fun x x' y hy => olgG_elasticity_le ha hH hV h2 x x' (hzl.trans_le hy))
  obtain ⟨f₀, ⟨hf₀D, hf₀fix⟩, -⟩ := hfix l₀ ⟨hl₀.1, le_rfl⟩
  have hz0 := hH.zeta_pos hl₀
  refine ⟨f₀, ⟨fun x => hz0.trans_le (hf₀D x), hf₀fix⟩, ?_⟩
  rintro f ⟨hfpos, hffix⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn
    ⟨(⟨a, le_rfl, hab⟩ : Icc a b), mem_univ _⟩ f.continuous.continuousOn
  set l := min l₀ (olgZetaInv L H' (f m))
  have hl : l ∈ Ioc 0 l₀ := ⟨lt_min hl₀.1 (hH.zetaInv_pos (hfpos m)), min_le_left _ _⟩
  have hlL : l ∈ Ico 0 L := ⟨hl.1.le, hl.2.trans_lt hl₀.2⟩
  have hzl : olgZeta H' l ≤ f m :=
    calc olgZeta H' l ≤ olgZeta H' (olgZetaInv L H' (f m)) :=
          hH.zeta_strictMonoOn.monotoneOn hlL (hH.zetaInv_mem (hfpos m).le) (min_le_right _ _)
      _ = f m := hH.zeta_zetaInv (hfpos m).le
  have hzl0 : olgZeta H' l ≤ olgZeta H' l₀ :=
    hH.zeta_strictMonoOn.monotoneOn hlL (Ioo_subset_Ico_self hl₀) (min_le_left _ _)
  obtain ⟨g, -, hg⟩ := hfix l hl
  have e1 := hg f ⟨fun x => hzl.trans (isMinOn_iff.1 hm x (mem_univ x)), hffix⟩
  have e2 := hg f₀ ⟨fun x => hzl0.trans (hf₀D x), hf₀fix⟩
  rw [e1, e2]

/-- **Correction (Proposition 2: the zero fixed point).** `f ≡ 0` also satisfies (6), since
`ζ⁻¹(0) = 0` and `φ(0) = 0`; this is why uniqueness must be stated among strictly positive
`f` (the book's `F` excludes it through `D = [ε_K, ∞)`). -/
theorem proposition_2_zero_fixedPoint (hH : Assumption17_1H L H H' H'') {a b : ℝ}
    (κ : Kernel (Icc a b) (Icc a b)) (x : Icc a b) :
    (0 : Icc a b →ᵇ ℝ) x =
      ∫ x', olgPhi V' (x'.1 * olgZetaInv L H' ((0 : Icc a b →ᵇ ℝ) x')) ∂κ x := by
  simp [hH.zetaInv_zero, olgPhi]

/-- **Correction (Proposition 2), continued.** Among nonnegative bounded continuous `f`, the
solution of (6) is *not* unique: both `0` and the strictly positive `f*` solve it. -/
theorem proposition_2_nonneg_counterexample {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'') {β : ℝ}
    (h2 : Assumption17_2R β V' V'') (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ]
    (hκ : IsFellerKernel κ) :
    ¬ ∃! f : Icc a b →ᵇ ℝ, (∀ x, 0 ≤ f x) ∧
      ∀ x, f x = ∫ x', olgPhi V' (x'.1 * olgZetaInv L H' (f x')) ∂κ x := by
  rintro ⟨g, -, hg⟩
  obtain ⟨f, ⟨hfpos, hffix⟩, -⟩ := proposition_2 ha hab hH hV h2 κ hκ
  have e1 := hg f ⟨fun x => (hfpos x).le, hffix⟩
  have e2 := hg 0 ⟨fun _ => le_rfl, proposition_2_zero_fixedPoint hH κ⟩
  have := hfpos ⟨a, le_rfl, hab⟩
  rw [e1, ← e2] at this
  simp at this

/-! ### The NOTE on `ε_k` (step 6 of the proof of Proposition 2) -/

/-- The book's `ε_k`: for every `k > 0` the equation `ζ⁻¹(ε) = k ε` has a solution `ε > 0`. -/
theorem epsK_exists (hH : Assumption17_1H L H H' H'') {k : ℝ} (hk : 0 < k) :
    ∃ ε > 0, olgZetaInv L H' ε = k * ε := by
  obtain ⟨l₁, hl₁, hl₁k⟩ := hH.exists_H'_lt (inv_pos.2 hk)
  set ε₁ := olgZeta H' l₁
  have hε₁ := hH.zeta_pos hl₁
  have h1 : olgZetaInv L H' ε₁ = l₁ := hH.zetaInv_zeta (Ioo_subset_Ico_self hl₁)
  have hkε₁ : k * ε₁ < l₁ := by
    have := mul_lt_mul_of_pos_left hl₁k hk
    rw [mul_inv_cancel₀ hk.ne'] at this
    simp only [ε₁, olgZeta]
    nlinarith [hl₁.1]
  have hLk : ε₁ ≤ L / k := by
    rw [le_div_iff₀ hk, mul_comm]
    linarith [hl₁.2]
  have hcont : ContinuousOn (fun e => olgZetaInv L H' e - k * e) (Icc ε₁ (L / k)) :=
    (hH.zetaInv_continuousOn.mono fun e he => mem_Ici.2 (hε₁.le.trans he.1)).sub
      (continuousOn_const.mul continuousOn_id)
  have hA : 0 < olgZetaInv L H' ε₁ - k * ε₁ := by rw [h1]; linarith
  have hB : olgZetaInv L H' (L / k) - k * (L / k) < 0 := by
    rw [mul_div_cancel₀ _ hk.ne']
    linarith [(hH.zetaInv_mem (div_pos hH.L_pos hk).le).2]
  obtain ⟨e, he, he0⟩ := intermediate_value_Icc' hLk hcont ⟨hB.le, hA.le⟩
  exact ⟨e, hε₁.trans_le he.1, by linarith⟩

/-- **The NOTE's gap in step 6 of Proposition 2, closed.** Any positive `ε_k` with
`ζ⁻¹(ε_k) = (k + 1) ε_k` satisfies `ε_k < L/(k + 1)`, so `ε_k → 0`. (The proof of
`proposition_2` uses the equivalent `ζ(l) → 0` directly.) -/
theorem epsK_tendsto_zero (hH : Assumption17_1H L H H' H'') {ε : ℕ → ℝ}
    (hpos : ∀ k, 0 < ε k) (heq : ∀ k, olgZetaInv L H' (ε k) = (k + 1) * ε k) :
    Tendsto ε atTop (𝓝 0) := by
  have hbound : ∀ k : ℕ, ε k ≤ L / ((k : ℝ) + 1) := fun k => by
    rw [le_div_iff₀ (by positivity), mul_comm, ← heq k]
    exact (hH.zetaInv_mem (hpos k).le).2.le
  have hlim : Tendsto (fun k : ℕ => L / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat L).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun k => ?_
    simp [Nat.cast_add, Nat.cast_one]
  exact squeeze_zero (fun k => (hpos k).le) hbound hlim

end StokeyLucasPrescott.FixedPointArguments
