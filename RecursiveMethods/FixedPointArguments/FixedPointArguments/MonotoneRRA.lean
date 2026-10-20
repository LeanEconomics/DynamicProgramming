/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.MonotoneOLGExamples

/-!
# Relative risk aversion: the claims on pp. 515, 530 and 541

SLP §17.2 (p. 515), §17.5 (p. 530) and §17.6 (p. 541) compare the restrictions on the relative
risk aversion `−yV″(y)/V′(y)` (`monoRRA`) used for the Contraction Mapping Theorem
(Assumption 17.2) and for monotone operators (Assumption 17.4).

* `monoRRA_zero`: `−yV″/V′ = 0` at `y = 0`, for any `V`.
* **pp. 515 and 530** ("strict monotonicity and concavity imply `0 < −yV″(y)/V′(y)` for all
  `y ∈ ℝ₊`"): false. `monoRRA_pos_counterexample` (`V = log(1 + y)`, ratio `0` at `y = 0`) and
  `monoRRA_interior_zero_counterexample` (`V(y) = 3 − e^{−y}(y² + 2y + 3)`, which satisfies
  Assumption 17.1 and has `V″(1) = 0`, so the ratio is `0` at the interior point `y = 1`).
  Corrected statement: `MonoAssumption17_1V.rra_nonneg` (the ratio is `≥ 0` on `ℝ₊`) and
  `MonoAssumption17_1V.exists_rra_pos` (it is `> 0` somewhere in every open interval, i.e. off a
  set with empty interior).
* **Assumption 17.2** (`MonoAssumption17_2`, p. 513): `1 − β ≤ −yV″/V′ ≤ 1 + β` on `ℝ₊` for some
  `β ∈ [0, 1)`. `not_monoAssumption17_2`: no `V` at all satisfies it (the ratio is `0` at `0`).
* **p. 541** ("Assumption 17.2 is a very mild strengthening of Assumption 17.4"): as literally
  stated, 17.2 implies 17.4 only vacuously (`monoAssumption17_2_imp_17_4`), while 17.4 does not
  imply 17.2 (`assumption17_4_not_imp_17_2_counterexample`). On `ℝ₊₊` (the repair of
  Assumption 17.2 with `V` smooth only on `ℝ₊₊`; `MonoAssumption17_2Pos`, `MonoAssumption17_4Pos`)
  **neither implies the other**: `V(y) = 2 arctan √y` has relative risk aversion
  `(1 + 3y)/(2(1 + y)) ∈ [1/2, 3/2)`, so it satisfies 17.2 with `β = 1/2` but violates 17.4
  (`assumption17_2Pos_not_imp_17_4Pos_counterexample`, with `monoArcV_repaired_utility`), and
  `V(y) = log(1 + y)` satisfies 17.4 but not 17.2
  (`assumption17_4Pos_not_imp_17_2Pos_counterexample`). Corrected statement
  (`monoAssumption17_2Pos_of_17_4Pos`): 17.4 plus a uniform lower bound `ε ≤ −yV″/V′` implies
  17.2 with `β = 1 − ε`.

**Correction (pp. 515, 530).** Assumption 17.1 gives only `−yV″/V′ ≥ 0`, with equality at
`y = 0` always and possibly at isolated `y > 0`.

**Correction (p. 541).** Assumptions 17.2 and 17.4 are not nested; what holds is
"17.4 + a uniform positive lower bound on relative risk aversion ⇒ 17.2".
-/

namespace StokeyLucasPrescott.FixedPointArguments

open Filter Topology Set

/-- Relative risk aversion vanishes at `y = 0`, whatever `V` is. -/
theorem monoRRA_zero (V' V'' : ℝ → ℝ) : monoRRA V' V'' 0 = 0 := by simp [monoRRA]

/-- No `V` has strictly positive relative risk aversion at every `y ∈ ℝ₊`. -/
theorem monoRRA_not_forall_pos (V' V'' : ℝ → ℝ) : ¬ ∀ y, 0 ≤ y → 0 < monoRRA V' V'' y :=
  fun h => by simpa [monoRRA_zero] using h 0 le_rfl

/-- **Counterexample (SLP pp. 515 and 530).** `V(y) = log(1 + y)` satisfies the utility half of
Assumption 17.1, yet `0 < −yV″(y)/V′(y)` fails (at `y = 0`). -/
theorem monoRRA_pos_counterexample :
    MonoAssumption17_1V monoCexV monoCexV' monoCexV'' ∧
      ¬ ∀ y, 0 ≤ y → 0 < monoRRA monoCexV' monoCexV'' y :=
  ⟨monoCexV_assumption17_1V, monoRRA_not_forall_pos _ _⟩

/-- `W(y) = 3 − e^{−y}(y² + 2y + 3)`. -/
noncomputable def monoCexW (y : ℝ) : ℝ := 3 - Real.exp (-y) * (y ^ 2 + 2 * y + 3)

/-- `W'(y) = e^{−y}(1 + y²)`. -/
noncomputable def monoCexW' (y : ℝ) : ℝ := Real.exp (-y) * (1 + y ^ 2)

/-- `W''(y) = −e^{−y}(y − 1)²`. -/
noncomputable def monoCexW'' (y : ℝ) : ℝ := -(Real.exp (-y) * (y - 1) ^ 2)

/-- `W'` is the derivative of `W`. -/
theorem hasDerivAt_monoCexW (y : ℝ) : HasDerivAt monoCexW (monoCexW' y) y := by
  have h := ((hasDerivAt_neg y).exp.mul (((hasDerivAt_pow 2 y).add
    ((hasDerivAt_id' y).const_mul 2)).add_const 3)).const_sub 3
  refine h.congr_deriv ?_
  rw [monoCexW']
  simp only [Pi.add_apply]
  push_cast
  ring

/-- `W''` is the derivative of `W'`. -/
theorem hasDerivAt_monoCexW' (y : ℝ) : HasDerivAt monoCexW' (monoCexW'' y) y := by
  have h := (hasDerivAt_neg y).exp.mul ((hasDerivAt_pow 2 y).const_add 1)
  refine h.congr_deriv ?_
  rw [monoCexW'']
  push_cast
  ring

/-- `W'` is strictly decreasing on `ℝ₊` (its derivative `−e^{−y}(y − 1)²` vanishes only at `1`). -/
theorem monoCexW'_strictAntiOn : StrictAntiOn monoCexW' (Ici 0) := by
  have hc : Continuous monoCexW' := by unfold monoCexW'; fun_prop
  have hneg : ∀ x, x ≠ 1 → deriv monoCexW' x < 0 := fun x hx => by
    rw [(hasDerivAt_monoCexW' x).deriv, monoCexW'', neg_lt_zero]
    exact mul_pos (Real.exp_pos _) (by positivity)
  have h1 : StrictAntiOn monoCexW' (Icc 0 1) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 1) hc.continuousOn fun x hx => by
      rw [interior_Icc] at hx; exact hneg x hx.2.ne
  have h2 : StrictAntiOn monoCexW' (Ici 1) :=
    strictAntiOn_of_deriv_neg (convex_Ici 1) hc.continuousOn fun x hx => by
      rw [interior_Ici] at hx; exact hneg x (ne_of_gt hx)
  intro x hx y hy hxy
  rcases le_or_gt y 1 with hy1 | hy1
  · exact h1 ⟨hx, hxy.le.trans hy1⟩ ⟨hy, hy1⟩ hxy
  rcases le_or_gt 1 x with hx1 | hx1
  · exact h2 hx1 (hx1.trans hxy.le) hxy
  · exact (h2 (le_refl (1 : ℝ)) hy1.le hy1).trans (h1 ⟨hx, hx1.le⟩ ⟨zero_le_one, le_rfl⟩ hx1)

/-- `W(y) = 3 − e^{−y}(y² + 2y + 3)` satisfies the utility half of **Assumption 17.1**. -/
theorem monoCexW_assumption17_1V : MonoAssumption17_1V monoCexW monoCexW' monoCexW'' := by
  have hc : Continuous monoCexW := by unfold monoCexW; fun_prop
  have hmono : StrictMonoOn monoCexW (Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hc.continuousOn fun x _ => by
      rw [(hasDerivAt_monoCexW x).deriv, monoCexW']
      positivity
  refine ⟨fun y _ => (hasDerivAt_monoCexW y).hasDerivWithinAt,
    fun y _ => (hasDerivAt_monoCexW' y).hasDerivWithinAt,
    (by unfold monoCexW''; fun_prop : Continuous monoCexW'').continuousOn, fun y hy => ?_, hmono,
    ?_⟩
  · have h0 : monoCexW 0 = 0 := by simp [monoCexW]
    rw [← h0]
    exact hmono.monotoneOn (mem_Ici.2 le_rfl) hy hy
  · refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hc.continuousOn
      fun x hx y hy hxy => ?_
    rw [(hasDerivAt_monoCexW x).deriv, (hasDerivAt_monoCexW y).deriv]
    exact monoCexW'_strictAntiOn (interior_subset hx) (interior_subset hy) hxy

/-- **Counterexample (SLP pp. 515 and 530), interior point.** `W(y) = 3 − e^{−y}(y² + 2y + 3)`
satisfies the utility half of Assumption 17.1 and its relative risk aversion vanishes at the
interior point `y = 1` (`W″(1) = 0`): strict concavity does not give `V″ < 0`. -/
theorem monoRRA_interior_zero_counterexample :
    MonoAssumption17_1V monoCexW monoCexW' monoCexW'' ∧ monoRRA monoCexW' monoCexW'' 1 = 0 :=
  ⟨monoCexW_assumption17_1V, by simp [monoRRA, monoCexW'']⟩

variable {V V' V'' : ℝ → ℝ}

/-- **Corrected claim (pp. 515, 530).** Under Assumption 17.1, relative risk aversion is
nonnegative on `ℝ₊`. -/
theorem MonoAssumption17_1V.rra_nonneg (hV : MonoAssumption17_1V V V' V'') {y : ℝ}
    (hy : 0 ≤ y) : 0 ≤ monoRRA V' V'' y := by
  have hV'' : V'' y ≤ 0 := by
    have := (hV.strictAntiOn_V'.antitoneOn).derivWithin_nonpos (x := y)
    rwa [(hV.hasDeriv_V' y hy).derivWithin (uniqueDiffOn_Ici 0 y hy)] at this
  rw [monoRRA]
  exact div_nonneg (by nlinarith) (hV.V'_pos hy).le

/-- **Corrected claim (pp. 515, 530).** Under Assumption 17.1, relative risk aversion is
strictly positive somewhere in every open interval of `ℝ₊` (so it vanishes only on a set with
empty interior). -/
theorem MonoAssumption17_1V.exists_rra_pos (hV : MonoAssumption17_1V V V' V'') {u w : ℝ}
    (hu : 0 ≤ u) (huw : u < w) : ∃ y ∈ Ioo u w, 0 < monoRRA V' V'' y := by
  by_contra hcon
  have hzero : ∀ y ∈ Ioo u w, V'' y = 0 := fun y hy => by
    have hy0 : 0 < y := lt_of_le_of_lt hu hy.1
    have h1 : monoRRA V' V'' y ≤ 0 := le_of_not_gt fun h => hcon ⟨y, hy, h⟩
    have h2 := hV.rra_nonneg hy0.le
    have h3 : monoRRA V' V'' y = 0 := le_antisymm h1 h2
    rw [monoRRA, div_eq_zero_iff] at h3
    rcases h3 with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd (neg_eq_zero.1 h4) hy0.ne'
      · exact h4
    · exact absurd h3 (hV.V'_pos hy0.le).ne'
  set u' := (2 * u + w) / 3
  set w' := (u + 2 * w) / 3
  have hu' : u < u' := by simp only [u']; linarith
  have hw' : w' < w := by simp only [w']; linarith
  have huw' : u' < w' := by simp only [u', w']; linarith
  have hconst := constant_of_has_deriv_right_zero (f := V') (a := u') (b := w')
    (hV.continuousOn_V'.mono fun x hx => mem_Ici.2 (hu.trans (hu'.le.trans hx.1)))
    (fun x hx => by
      have hx0 : 0 ≤ x := hu.trans (hu'.le.trans hx.1)
      have := (hV.hasDeriv_V' x hx0).mono (Ici_subset_Ici.2 hx0)
      rwa [hzero x ⟨hu'.trans_le hx.1, hx.2.trans hw'⟩] at this)
    w' ⟨huw'.le, le_rfl⟩
  have := hV.strictAntiOn_V' (mem_Ici.2 (hu.trans hu'.le)) (mem_Ici.2 (hu.trans (hu'.trans
    huw').le)) huw'
  linarith

/-! ### Assumption 17.2 versus Assumption 17.4 (p. 541) -/

/-- **Assumption 17.2** (SLP p. 513): for some `β ∈ [0, 1)`,
`1 − β ≤ −yV″(y)/V′(y) ≤ 1 + β` for all `y ∈ ℝ₊`. -/
def MonoAssumption17_2 (V' V'' : ℝ → ℝ) : Prop :=
  ∃ β, 0 ≤ β ∧ β < 1 ∧ ∀ y, 0 ≤ y → 1 - β ≤ monoRRA V' V'' y ∧ monoRRA V' V'' y ≤ 1 + β

/-- Assumption 17.2 as stated (on `ℝ₊`) is never satisfied: the ratio is `0` at `y = 0`. -/
theorem not_monoAssumption17_2 (V' V'' : ℝ → ℝ) : ¬ MonoAssumption17_2 V' V'' := by
  rintro ⟨β, -, hβ, h⟩
  have := (h 0 le_rfl).1
  rw [monoRRA_zero] at this
  linarith

/-- As stated, Assumption 17.2 implies Assumption 17.4, but only vacuously. -/
theorem monoAssumption17_2_imp_17_4 (h : MonoAssumption17_2 V' V'') :
    MonoAssumption17_4 V' V'' :=
  absurd h (not_monoAssumption17_2 V' V'')

/-- **Counterexample (p. 541), literal version.** `V = log(1 + y)` satisfies Assumptions 17.1
and 17.4 but not Assumption 17.2: 17.4 does not imply 17.2. -/
theorem assumption17_4_not_imp_17_2_counterexample :
    MonoAssumption17_1V monoCexV monoCexV' monoCexV'' ∧ MonoAssumption17_4 monoCexV' monoCexV'' ∧
      ¬ MonoAssumption17_2 monoCexV' monoCexV'' :=
  ⟨monoCexV_assumption17_1V, monoCexV_assumption17_4, not_monoAssumption17_2 _ _⟩

/-- Assumption 17.2 on `ℝ₊₊` (the repair, with `V` twice differentiable only on `ℝ₊₊`). -/
def MonoAssumption17_2Pos (V' V'' : ℝ → ℝ) : Prop :=
  ∃ β, 0 ≤ β ∧ β < 1 ∧ ∀ y, 0 < y → 1 - β ≤ monoRRA V' V'' y ∧ monoRRA V' V'' y ≤ 1 + β

/-- Assumption 17.4 on `ℝ₊₊`. -/
def MonoAssumption17_4Pos (V' V'' : ℝ → ℝ) : Prop := ∀ y, 0 < y → monoRRA V' V'' y ≤ 1

/-- **Corrected claim (p. 541).** Assumption 17.4 together with a uniform positive lower bound
`ε ≤ −yV″/V′` implies Assumption 17.2 (with `β = 1 − ε`). -/
theorem monoAssumption17_2Pos_of_17_4Pos (h4 : MonoAssumption17_4Pos V' V'') {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hlow : ∀ y, 0 < y → ε ≤ monoRRA V' V'' y) :
    MonoAssumption17_2Pos V' V'' :=
  ⟨1 - ε, by linarith, by linarith, fun y hy =>
    ⟨by linarith [hlow y hy], by linarith [h4 y hy]⟩⟩

/-- **Counterexample (p. 541), repaired version.** `V = log(1 + y)` satisfies Assumption 17.4
on `ℝ₊₊` but not Assumption 17.2 on `ℝ₊₊` (its relative risk aversion `y/(1 + y) → 0`). -/
theorem assumption17_4Pos_not_imp_17_2Pos_counterexample :
    MonoAssumption17_4Pos monoCexV' monoCexV'' ∧ ¬ MonoAssumption17_2Pos monoCexV' monoCexV'' := by
  refine ⟨fun y hy => monoCexV_assumption17_4 y hy.le, ?_⟩
  rintro ⟨β, -, hβ, h⟩
  have hy : (0 : ℝ) < (1 - β) / 2 := by linarith
  have := (h _ hy).1
  rw [monoRRA_monoCexV hy.le, le_div_iff₀ (by linarith)] at this
  nlinarith

/-- `V(y) = 2 arctan √y`. -/
noncomputable def monoArcV (y : ℝ) : ℝ := 2 * Real.arctan (√y)

/-- `V'(y) = 1/(√y (1 + y))` for `y > 0`. -/
noncomputable def monoArcV' (y : ℝ) : ℝ := (√y * (1 + y))⁻¹

/-- `V''(y)` for `y > 0`. -/
noncomputable def monoArcV'' (y : ℝ) : ℝ :=
  -(1 / (2 * √y) * (1 + y) + √y * 1) / (√y * (1 + y)) ^ 2

/-- `V'` is the derivative of `V = 2 arctan √y` on `ℝ₊₊`. -/
theorem hasDerivAt_monoArcV {y : ℝ} (hy : 0 < y) : HasDerivAt monoArcV (monoArcV' y) y := by
  have hs : 0 < √y := Real.sqrt_pos.2 hy
  have h := ((Real.hasDerivAt_sqrt hy.ne').arctan).const_mul 2
  refine h.congr_deriv ?_
  rw [monoArcV', Real.sq_sqrt hy.le]
  field_simp

/-- `V''` is the derivative of `V'` on `ℝ₊₊`. -/
theorem hasDerivAt_monoArcV' {y : ℝ} (hy : 0 < y) : HasDerivAt monoArcV' (monoArcV'' y) y := by
  have hs : 0 < √y := Real.sqrt_pos.2 hy
  have hne : √y * (1 + y) ≠ 0 := by positivity
  exact ((Real.hasDerivAt_sqrt hy.ne').mul ((hasDerivAt_id' y).const_add 1)).inv hne

/-- `V = 2 arctan √y` is a utility function in the repaired sense of Assumption 17.1: continuous
on `ℝ₊` with `V(0) = 0`, `V ≥ 0`, strictly increasing and strictly concave on `ℝ₊`, and twice
continuously differentiable on `ℝ₊₊` (with `V'(0+) = +∞`). -/
theorem monoArcV_repaired_utility :
    ContinuousOn monoArcV (Ici 0) ∧ monoArcV 0 = 0 ∧ (∀ y, 0 ≤ y → 0 ≤ monoArcV y) ∧
      StrictMonoOn monoArcV (Ici 0) ∧ StrictConcaveOn ℝ (Ici 0) monoArcV ∧
      (∀ y, 0 < y → HasDerivAt monoArcV (monoArcV' y) y) ∧
      (∀ y, 0 < y → HasDerivAt monoArcV' (monoArcV'' y) y) ∧ ContinuousOn monoArcV'' (Ioi 0) := by
  have hc : Continuous monoArcV := by unfold monoArcV; fun_prop
  have hmono : StrictMonoOn monoArcV (Ici 0) := fun x hx y _ hxy => by
    have := Real.arctan_strictMono (Real.sqrt_lt_sqrt (mem_Ici.1 hx) hxy)
    simp only [monoArcV]
    linarith
  refine ⟨hc.continuousOn, by simp [monoArcV], fun y hy => ?_, hmono, ?_,
    fun y hy => hasDerivAt_monoArcV hy, fun y hy => hasDerivAt_monoArcV' hy, ?_⟩
  · have := Real.arctan_strictMono.monotone (Real.sqrt_nonneg y)
    rw [Real.arctan_zero] at this
    simp only [monoArcV]
    linarith
  · refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hc.continuousOn
      fun x hx y hy hxy => ?_
    rw [interior_Ici] at hx hy
    rw [(hasDerivAt_monoArcV hx).deriv, (hasDerivAt_monoArcV hy).deriv, monoArcV', monoArcV']
    have hsx : 0 < √x := Real.sqrt_pos.2 hx
    have hsy : 0 < √y := Real.sqrt_pos.2 hy
    have hsxy : √x < √y := Real.sqrt_lt_sqrt (le_of_lt hx) hxy
    rw [inv_lt_inv₀ (mul_pos hsy (by linarith [mem_Ioi.1 hy]))
      (mul_pos hsx (by linarith [mem_Ioi.1 hx]))]
    exact mul_lt_mul'' hsxy (by linarith) hsx.le (by linarith [mem_Ioi.1 hx])
  · intro y hy
    have hs : 0 < √y := Real.sqrt_pos.2 hy
    have hne : √y * (1 + y) ≠ 0 := (mul_pos hs (by linarith [mem_Ioi.1 hy])).ne'
    refine ContinuousAt.continuousWithinAt ?_
    unfold monoArcV''
    have hsq : ContinuousAt (fun x : ℝ => √x) y := Real.continuous_sqrt.continuousAt
    exact ((((continuousAt_const.div (continuousAt_const.mul hsq) (mul_pos two_pos hs).ne').mul
      (continuousAt_const.add continuousAt_id)).add (hsq.mul continuousAt_const)).neg).div
      ((hsq.mul (continuousAt_const.add continuousAt_id)).pow 2) (pow_ne_zero 2 hne)

/-- Relative risk aversion of `2 arctan √y` is `(1 + 3y)/(2(1 + y))` on `ℝ₊₊`. -/
theorem monoRRA_monoArcV {y : ℝ} (hy : 0 < y) :
    monoRRA monoArcV' monoArcV'' y = (1 + 3 * y) / (2 * (1 + y)) := by
  have hs : 0 < √y := Real.sqrt_pos.2 hy
  have hy' : y = √y ^ 2 := (Real.sq_sqrt hy.le).symm
  rw [monoRRA, monoArcV', monoArcV'']
  set s := √y
  rw [hy']
  field_simp
  ring

/-- **Counterexample (p. 541), repaired version.** `V = 2 arctan √y` satisfies Assumption 17.2
on `ℝ₊₊` (with `β = 1/2`: relative risk aversion lies in `[1/2, 3/2]`) but violates
Assumption 17.4 (relative risk aversion `7/6 > 1` at `y = 2`): 17.2 does not imply 17.4, so it
is not a "strengthening" of 17.4. -/
theorem assumption17_2Pos_not_imp_17_4Pos_counterexample :
    MonoAssumption17_2Pos monoArcV' monoArcV'' ∧ ¬ MonoAssumption17_4Pos monoArcV' monoArcV'' := by
  refine ⟨⟨1 / 2, by norm_num, by norm_num, fun y hy => ?_⟩, fun h => ?_⟩
  · rw [monoRRA_monoArcV hy, le_div_iff₀ (by linarith), div_le_iff₀ (by linarith)]
    constructor <;> nlinarith
  · have := h 2 two_pos
    rw [monoRRA_monoArcV two_pos] at this
    norm_num at this

end StokeyLucasPrescott.FixedPointArguments
