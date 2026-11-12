/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSovereignDefault.UniqueEquilibrium

/-!
# Two Markov perfect equilibria with long-term debt and a continuum of debt levels

AKMM, Appendix 24.A.1, p. 901: "Aguiar and Amador (2020) show that there can be multiple
Markov equilibria in the model with long-term debt (`δ ∈ (0, 1)`)". Beyond the text.

**The equilibrium with long-term debt** (`IsLongMPE`) is the book's definition (§24.4.3,
(a)–(c)) with the long-term bond of (24.7)–(24.8): the repaying sovereign with debt `B` choosing
`B′` consumes `C = Y − δB + q(B′, Y)(B′ − (1 − δ)B)` ((24.11)), and the price is (24.12),
`q(B′, Y) = (1 + r)⁻¹ E[(1 − D̂(B′, Y′))(δ + (1 − δ)q(B̂(B′, Y′), Y′))]`. The setting is that
of departure D10 (`UEModel`: permanent exclusion `ψ = 0`, any `B′ ≤ B̄` including saving,
states `B ∈ ℝ`, bounded values). At `δ = 1` the definition is exactly `IsOneMPE`
(`ld_one_iff`), so by `ue_mpe_exists_unique` an economy satisfying its hypotheses has exactly
one equilibrium with one-period debt.

**The economy** (`ld_econ`): deterministic income `Y = 2`, utility `u(c) = min(c, 1)`
(satiated at `c̄ = 1`), default cost `φ = 1/2`, `β = 1/2`, `r = 1/4`, borrowing limit
`B̄ = 7`. With `δ = 1/2` it has two Markov perfect equilibria (`ld_two_mpe`), both verified
against every condition of the definition:

* **no dilution**: the sovereign always issues up to the safe level `6` (or `7` when it
  defaults anyway), never defaults on debt `B ≤ 6`, and every safe bond trades at the
  risk-free price `δ/(r + δ) = 2/3`;
* **self-fulfilling dilution**: a sovereign with little debt (`B ≤ 2`) issues up to `B̄ = 7`,
  diluting its creditors, and defaults the next period; lenders anticipate it, so bonds
  `B′ ≤ 2` trade at `δ/(1 + r) = 2/5` (one coupon, then nothing), while `B′ ∈ (2, 6]` still
  trade at `2/3`.

The value functions and the default rule coincide (`V ≡ 2`, default iff `B > 6`); the prices
and the borrowing rules differ. The mechanism is that with `δ < 1` the price depends on the
borrowing rule lenders expect (`bp_long_term_depends_on_borrowing`): the low-debt sovereign is
satiated whichever debt it issues, and default at `7` costs it no utility (`Y − φ ≥ c̄`), so it
is indifferent, and lenders' beliefs select the rule. With `δ = 1` the price does not depend on
the borrowing rule, and the same economy has a unique equilibrium (`ld_one_period_unique`).

This is a multiplicity through indifference: it isolates the dilution channel of long-term
debt but is not Aguiar and Amador's (2020) construction, where the sovereign strictly prefers to
dilute and values differ across equilibria; that construction is not formalised.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

variable {Y : Type*} [Fintype Y]

namespace UEModel

variable (M : UEModel Y)

/-- AKMM, (24.11) with the long-term bond of (24.7)–(24.8): the objective
`u(Y − δB + q(B′, Y)(B′ − (1 − δ)B)) + βE V(B′, Y′)`. -/
def ldObj (δ : ℝ) (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) (b' : ℝ) : ℝ :=
  M.u (M.inc y - δ * b + q b' y * (b' - (1 - δ) * b)) + M.β * ∑ j, M.P y j * V b' j

/-- With one-period debt the long-term objective is the one-period objective. -/
theorem ld_obj_one (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) (b' : ℝ) :
    M.ldObj 1 q V b y b' = M.obj q V b y b' := by
  unfold ldObj obj
  simp only [one_mul, sub_self, zero_mul, sub_zero]

end UEModel

variable (M : UEModel Y) (δ : ℝ) (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D Bh q : ℝ → Y → ℝ) in
/-- **AKMM, §24.4.3**, pp. 744–745, Markov perfect equilibrium with long-term debt of decay `δ`
((24.7)–(24.12)), permanent exclusion (`ψ = 0`) and a continuum of debt levels `B′ ≤ B̄`
(departure D10): bounded values `V`, `V^R`, `V^D`, a default rule `D̂`, a borrowing rule `B̂`
and a price `q` with (a) (24.9)–(24.11), (b) (24.12), (c) `D̂` and `B̂` optimal. -/
structure IsLongMPE : Prop where
  /-- Values lie in the space of bounded functions. -/
  bdd : ∃ K, ∀ b y, V b y ≤ K
  /-- (a) (24.9). -/
  eq_24_9 : ∀ b y, V b y = max (VD y) (VR b y)
  /-- (a) (24.10) with `ψ = 0`. -/
  eq_24_10 : ∀ y, VD y = M.defaultRHS VD y
  /-- (a) (24.11): `V^R` bounds the objective over `B′ ≤ B̄` ... -/
  eq_24_11 : ∀ b y b', b' ≤ M.bmax → M.ldObj δ q V b y b' ≤ VR b y
  /-- (b) (24.12). -/
  eq_24_12 : ∀ b' y, b' ≤ M.bmax → q b' y =
    (1 + M.r)⁻¹ * ∑ j, M.P y j * ((1 - D b' j) * (δ + (1 - δ) * q (Bh b' j) j))
  /-- (c) the default rule is optimal (ties repaid). -/
  default_opt : ∀ b y, D b y = if VR b y < VD y then 1 else 0
  /-- The borrowing rule is feasible. -/
  borrow_le : ∀ b y, Bh b y ≤ M.bmax
  /-- (c) ... and attains it. -/
  borrow_opt : ∀ b y, M.ldObj δ q V b y (Bh b y) = VR b y

/-- **The definition at `δ = 1`**: a Markov perfect equilibrium with long-term debt of decay
`δ = 1` is exactly a Markov perfect equilibrium with one-period debt (`IsOneMPE`). -/
theorem ld_one_iff (M : UEModel Y) (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D Bh q : ℝ → Y → ℝ) :
    IsLongMPE M 1 V VR VD D Bh q ↔ IsOneMPE M V VR VD D Bh q := by
  have hp : ∀ b' y, (1 + M.r)⁻¹ * ∑ j, M.P y j * ((1 - D b' j) * (1 + (1 - 1) * q (Bh b' j) j))
      = (1 + M.r)⁻¹ * ∑ j, M.P y j * (1 - D b' j) := fun b' y => by
    simp only [sub_self, zero_mul, add_zero, mul_one]
  constructor
  · intro h
    exact { bdd := h.bdd
            eq_24_9 := h.eq_24_9
            eq_24_10 := h.eq_24_10
            eq_24_11 := fun b y b' hb' => by rw [← M.ld_obj_one]; exact h.eq_24_11 b y b' hb'
            eq_24_12 := fun b' y hb' => by rw [h.eq_24_12 b' y hb', hp]
            default_opt := h.default_opt
            borrow_le := h.borrow_le
            borrow_opt := fun b y => by rw [← M.ld_obj_one]; exact h.borrow_opt b y }
  · intro h
    exact { bdd := h.bdd
            eq_24_9 := h.eq_24_9
            eq_24_10 := h.eq_24_10
            eq_24_11 := fun b y b' hb' => by rw [M.ld_obj_one]; exact h.eq_24_11 b y b' hb'
            eq_24_12 := fun b' y hb' => by rw [h.eq_24_12 b' y hb', hp]
            default_opt := h.default_opt
            borrow_le := h.borrow_le
            borrow_opt := fun b y => by rw [M.ld_obj_one]; exact h.borrow_opt b y }

/-- The economy of the long-term multiplicity example: one income level `Y = 2`, utility
`u(c) = min(c, 1)`, default cost `φ = 1/2`, `β = 1/2`, `r = 1/4`, borrowing limit `B̄ = 7`. -/
noncomputable def ld_econ : UEModel Unit where
  inc := fun _ => 2
  P := fun _ _ => 1
  markov := ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
  u := fun c => min c 1
  φ := fun _ => 1 / 2
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  r := 1 / 4
  r_pos := by norm_num
  bmax := 7
  bmax_nonneg := by norm_num

/-- The repayment value of the example (both equilibria):
`V^R(B) = min(2 − B/2 + max(4 − B/3, 0), 1) + 1`. -/
noncomputable def ld_VR (b : ℝ) (_ : Unit) : ℝ := min (2 - b / 2 + max (4 - b / 3) 0) 1 + 1

/-- The default rule of the example (both equilibria): default iff `B > 6`. -/
noncomputable def ld_D (b : ℝ) (_ : Unit) : ℝ := if 6 < b then 1 else 0

/-- The no-dilution prices: `2/3` on `B′ ≤ 6`, `0` above. -/
noncomputable def ld_qG (b' : ℝ) (_ : Unit) : ℝ := if b' ≤ 6 then 2 / 3 else 0

/-- The dilution prices: `2/5` on `B′ ≤ 2`, `2/3` on `(2, 6]`, `0` above. -/
noncomputable def ld_qB (b' : ℝ) (_ : Unit) : ℝ :=
  if b' ≤ 2 then 2 / 5 else if b' ≤ 6 then 2 / 3 else 0

/-- The no-dilution borrowing rule: issue up to `6`, or `7` when `B > 12`. -/
noncomputable def ld_BG (b : ℝ) (_ : Unit) : ℝ := if b ≤ 12 then 6 else 7

/-- The dilution borrowing rule: issue up to `B̄ = 7` when `B ≤ 2`, else as without dilution. -/
noncomputable def ld_BB (b : ℝ) (_ : Unit) : ℝ := if b ≤ 2 then 7 else if b ≤ 12 then 6 else 7

/-- The repayment value is below the default value `2`, and below it exactly when `B > 6`. -/
theorem ld_VR_lt_iff (b : ℝ) : ld_VR b () ≤ 2 ∧ (ld_VR b () < 2 ↔ 6 < b) := by
  unfold ld_VR
  refine ⟨by linarith [min_le_right (2 - b / 2 + max (4 - b / 3) 0) 1], ?_⟩
  constructor
  · intro h
    by_contra hb
    have h1 : 1 ≤ 2 - b / 2 + max (4 - b / 3) 0 := by
      linarith [le_max_left (4 - b / 3) 0, not_lt.1 hb]
    rw [min_eq_right h1] at h
    linarith
  · intro hb
    have h1 : 2 - b / 2 + max (4 - b / 3) 0 < 1 := by
      rcases le_total (4 - b / 3) 0 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    linarith [min_le_left (2 - b / 2 + max (4 - b / 3) 0) 1]

/-- The objective of the example at `δ = 1/2` with continuation value `2`. -/
theorem ld_obj_eq (q : ℝ → Unit → ℝ) (b b' : ℝ) :
    ld_econ.ldObj (1 / 2) q (fun _ _ => 2) b () b' =
      min (2 - b / 2 + q b' () * (b' - b / 2)) 1 + 1 := by
  simp only [UEModel.ldObj, ld_econ, univ_unique, sum_singleton]
  norm_num
  ring_nf

/-- The default value of the example is `2`. -/
theorem ld_VD_eq : ld_econ.defaultRHS (fun _ => 2) () = 2 := by
  simp only [UEModel.defaultRHS, ld_econ, univ_unique, sum_singleton]
  norm_num

/-- **Two Markov perfect equilibria with long-term debt** (`δ = 1/2`) in the continuous-debt
economy `ld_econ` (AKMM, p. 901, beyond the text). Both have `V ≡ V^D ≡ 2`, the repayment
value `ld_VR` and default iff `B > 6`. Without dilution (`ld_qG`, `ld_BG`) every safe bond
trades at `δ/(r + δ) = 2/3`; with self-fulfilling dilution (`ld_qB`, `ld_BB`) a sovereign
with debt `B ≤ 2` issues `B̄ = 7` and bonds `B′ ≤ 2` trade at `δ/(1 + r) = 2/5`. The prices
of debt `1` differ, and so do the borrowing rules at debt `0`. -/
theorem ld_two_mpe :
    IsLongMPE ld_econ (1 / 2) (fun _ _ => 2) ld_VR (fun _ => 2) ld_D ld_BG ld_qG ∧
      IsLongMPE ld_econ (1 / 2) (fun _ _ => 2) ld_VR (fun _ => 2) ld_D ld_BB ld_qB ∧
      ld_qG 1 () ≠ ld_qB 1 () ∧ ld_BG 0 () ≠ ld_BB 0 () := by
  have hbm : ld_econ.bmax = 7 := rfl
  have hr : (1 + ld_econ.r)⁻¹ = 4 / 5 := by simp only [ld_econ]; norm_num
  have h9 : ∀ b (_ : Unit), (2 : ℝ) = max 2 (ld_VR b ()) := fun b _ =>
    (max_eq_left (ld_VR_lt_iff b).1).symm
  have hdef : ∀ b (_ : Unit), ld_D b () = if ld_VR b () < 2 then 1 else 0 := fun b _ => by
    unfold ld_D
    by_cases h : 6 < b
    · simp only [h, (ld_VR_lt_iff b).2.2 h, ↓reduceIte]
    · have h' : ¬ ld_VR b () < 2 := fun h' => h ((ld_VR_lt_iff b).2.1 h')
      simp only [h, h', ↓reduceIte]
  have hsum : ∀ (f : Unit → ℝ), ∑ j, ld_econ.P () j * f j = f () := fun f => by
    simp only [ld_econ, univ_unique, sum_singleton, one_mul]
  -- the objective is bounded by the repayment value whenever `q(B′)(B′ − B/2) ≤ max(4 − B/3, 0)`
  have hle : ∀ (q : ℝ → Unit → ℝ) (b b' : ℝ), q b' () * (b' - b / 2) ≤ max (4 - b / 3) 0 →
      ld_econ.ldObj (1 / 2) q (fun _ _ => 2) b () b' ≤ ld_VR b () := fun q b b' h => by
    rw [ld_obj_eq]
    unfold ld_VR
    linarith [min_le_min_right 1 (show 2 - b / 2 + q b' () * (b' - b / 2) ≤
      2 - b / 2 + max (4 - b / 3) 0 by linarith)]
  have hrev : ∀ c b b' : ℝ, 0 ≤ c → c ≤ 2 / 3 → b' ≤ 6 → c * (b' - b / 2) ≤ max (4 - b / 3) 0 :=
    fun c b b' hc0 hc1 hb' => by
      rcases le_total 0 (b' - b / 2) with h | h
      · have : c * (b' - b / 2) ≤ 2 / 3 * (6 - b / 2) :=
          mul_le_mul hc1 (by linarith) h (by norm_num)
        exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right (mul_nonpos_of_nonneg_of_nonpos hc0 h)
  -- the repayment value at the safe issue `6`
  have hat6 : ∀ b : ℝ, b ≤ 12 → min (2 - b / 2 + 2 / 3 * (6 - b / 2)) 1 + 1 = ld_VR b () :=
    fun b hb => by
      unfold ld_VR
      rw [max_eq_left (by linarith : (0 : ℝ) ≤ 4 - b / 3)]
      ring_nf
  have hat7 : ∀ b : ℝ, 12 < b → min (2 - b / 2 + 0 * (7 - b / 2)) 1 + 1 = ld_VR b () :=
    fun b hb => by
      unfold ld_VR
      rw [max_eq_right (by linarith : 4 - b / 3 ≤ (0 : ℝ))]
      ring_nf
  refine ⟨⟨⟨2, fun _ _ => le_rfl⟩, h9, fun _ => ld_VD_eq.symm, fun b _ b' hb' => ?_,
    fun b' _ hb' => ?_, hdef, fun b _ => ?_, fun b _ => ?_⟩,
    ⟨⟨2, fun _ _ => le_rfl⟩, h9, fun _ => ld_VD_eq.symm, fun b _ b' hb' => ?_,
    fun b' _ hb' => ?_, hdef, fun b _ => ?_, fun b _ => ?_⟩, ?_, ?_⟩
  · -- good: (24.11)
    refine hle _ b b' ?_
    unfold ld_qG
    split_ifs with h
    · exact hrev _ b b' (by norm_num) le_rfl h
    · rw [zero_mul]; exact le_max_right _ _
  · -- good: (24.12)
    rw [hsum, hr]
    unfold ld_qG ld_D ld_BG
    split_ifs <;> (try norm_num) <;> linarith
  · -- good: feasibility
    unfold ld_BG; rw [hbm]; split_ifs <;> norm_num
  · -- good: optimality
    rw [ld_obj_eq]
    unfold ld_BG ld_qG
    by_cases h : b ≤ 12
    · simp only [h, le_refl (6 : ℝ), ↓reduceIte]; exact hat6 b h
    · simp only [h, (by norm_num : ¬ (7 : ℝ) ≤ 6), ↓reduceIte]; exact hat7 b (not_le.1 h)
  · -- dilution: (24.11)
    refine hle _ b b' ?_
    unfold ld_qB
    split_ifs with h1 h2
    · exact hrev _ b b' (by norm_num) (by norm_num) (by linarith)
    · exact hrev _ b b' (by norm_num) le_rfl h2
    · rw [zero_mul]; exact le_max_right _ _
  · -- dilution: (24.12)
    rw [hsum, hr]
    unfold ld_qB ld_D ld_BB
    split_ifs <;> (try norm_num) <;> linarith
  · -- dilution: feasibility
    unfold ld_BB; rw [hbm]; split_ifs <;> norm_num
  · -- dilution: optimality
    rw [ld_obj_eq]
    unfold ld_BB ld_qB
    by_cases h2 : b ≤ 2
    · simp only [h2, (by norm_num : ¬ (7 : ℝ) ≤ 2), (by norm_num : ¬ (7 : ℝ) ≤ 6), ↓reduceIte]
      unfold ld_VR
      rw [min_eq_right (by linarith : (1 : ℝ) ≤ 2 - b / 2 + 0 * (7 - b / 2)),
        min_eq_right (by linarith [le_max_left (4 - b / 3) 0] :
          (1 : ℝ) ≤ 2 - b / 2 + max (4 - b / 3) 0)]
    · simp only [h2, ↓reduceIte]
      by_cases h : b ≤ 12
      · simp only [h, (by norm_num : ¬ (6 : ℝ) ≤ 2), le_refl (6 : ℝ), ↓reduceIte]
        exact hat6 b h
      · simp only [h, (by norm_num : ¬ (7 : ℝ) ≤ 2),
          (by norm_num : ¬ (7 : ℝ) ≤ 6), ↓reduceIte]
        exact hat7 b (not_le.1 h)
  · unfold ld_qG ld_qB; norm_num
  · unfold ld_BG ld_BB; norm_num

/-- The dilution prices are never above the no-dilution prices, and strictly below them on
`B′ ≤ 2`. -/
theorem ld_dilution_lowers_prices (b' : ℝ) :
    ld_qB b' () ≤ ld_qG b' () ∧ (b' ≤ 2 → ld_qB b' () < ld_qG b' ()) := by
  unfold ld_qB ld_qG
  constructor
  · split_ifs <;> first | (norm_num; done) | (norm_num; linarith)
  · intro h
    simp only [h, (by linarith : b' ≤ 6), ↓reduceIte]
    norm_num

/-- The example meets the hypotheses of `ue_mpe_exists_unique`: `u = min(·, 1)` nondecreasing,
uniformly continuous and satiated at `1`, `φ ≥ 0`. -/
theorem ld_econ_hyp : Monotone ld_econ.u ∧ UniformContinuous ld_econ.u ∧
    (∀ c, 1 ≤ c → ld_econ.u c = ld_econ.u 1) ∧ ∀ y, 0 ≤ ld_econ.φ (ld_econ.inc y) := by
  refine ⟨fun a b h => min_le_min_right 1 h, (LipschitzWith.id.min_const 1).uniformContinuous,
    fun c hc => ?_, fun _ => by change (0 : ℝ) ≤ 1 / 2; norm_num⟩
  change min c 1 = min 1 1
  rw [min_eq_right hc, min_self]

/-- **With one-period debt the same economy has exactly one Markov perfect equilibrium**
(AKMM, p. 901; `ue_mpe_exists_unique` through `ld_one_iff`): it exists, and any two share
their values, default rule and prices. So the multiplicity of `ld_two_mpe` is due to `δ < 1`. -/
theorem ld_one_period_unique :
    (∃ (V VR : ℝ → Unit → ℝ) (VD : Unit → ℝ) (D Bh q : ℝ → Unit → ℝ),
      IsLongMPE ld_econ 1 V VR VD D Bh q) ∧
      ∀ {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Unit → ℝ} {VD₁ VD₂ : Unit → ℝ},
        IsLongMPE ld_econ 1 V₁ VR₁ VD₁ D₁ Bh₁ q₁ → IsLongMPE ld_econ 1 V₂ VR₂ VD₂ D₂ Bh₂ q₂ →
        V₁ = V₂ ∧ VR₁ = VR₂ ∧ VD₁ = VD₂ ∧ D₁ = D₂ ∧
          ∀ b' y, b' ≤ ld_econ.bmax → q₁ b' y = q₂ b' y := by
  obtain ⟨h1, h2, h3, h4⟩ := ld_econ_hyp
  obtain ⟨hex, huniq⟩ := ld_econ.ue_mpe_exists_unique h1 h2 h3 h4
  obtain ⟨V, VR, VD, D, Bh, q, h⟩ := hex
  exact ⟨⟨V, VR, VD, D, Bh, q, (ld_one_iff _ _ _ _ _ _ _).2 h⟩, fun h₁ h₂ =>
    huniq ((ld_one_iff _ _ _ _ _ _ _).1 h₁) ((ld_one_iff _ _ _ _ _ _ _).1 h₂)⟩

end AKMM.SovereignDefault
