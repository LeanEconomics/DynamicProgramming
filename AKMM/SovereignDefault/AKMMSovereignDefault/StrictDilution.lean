/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSovereignDefault.LongTermMultiplicity

/-!
# Self-fulfilling debt dilution: strict multiplicity with long-term debt

AKMM, Appendix 24.A.1, p. 901: "Aguiar and Amador (2020) show that there can be multiple
Markov equilibria in the model with long-term debt (`δ ∈ (0, 1)`)". Beyond the text.

**Setting** (departure D13). The book's model of §24.4 with the book's own asset lower bound
`B′ ≥ 0` (p. 744) and the borrowing limit `B′ ≤ B̄`: states and choices lie in `[0, B̄]`
(`IsBoundedLongMPE`, otherwise the definition `IsLongMPE` of (24.7)–(24.12), with permanent
exclusion `ψ = 0`). The same definition is used for `δ < 1` and for `δ = 1`.

**The economy** (`sfd_econ`). Two income states: normal times `H` (`true`, income `2`, default
cost `3/2`) and an absorbing crisis `L` (`false`, income `1`, default cost `1/7`), reached from
`H` with probability `λ = 1/5`; linear utility `u(c) = c`, `β = 1/2`, `r = 1/5`, `B̄ = 3/2`. With
`δ = 1/2` the risk-free price is `q* = δ/(r + δ) = 5/7`, and in the crisis the sovereign repays
exactly the debts `B ≤ 1` (the *safe zone*). Debt above `1` is lost when the crisis comes.

**Two Markov perfect equilibria at `δ = 1/2`** (`sfd_two_mpe`), both verified against every
condition at every state and every admissible `B′`:

* **no dilution** (`sfd_VRN`, `sfd_qN`, `sfd_BhN`): a sovereign in the safe zone keeps its
  debt at `1` and pays the risk-free price `5/7`; one with debt in `(1, 10/9]` deleverages to
  `1`; above `10/9` it stays at `B̄`;
* **self-fulfilling dilution** (`sfd_VRS`, `sfd_qS`, `sfd_BhS`): lenders expect a sovereign
  with debt in `(3/5, 1]` to borrow up to `B̄ = 3/2`, so they pay only `9/14 < 5/7` for such
  debt; at these prices diluting is strictly optimal (`sfd_strict_preference`), and debt below
  `3/5`, which is diluted one period later, trades at `29/42 < 5/7`.

The default rule is the same, but the **values differ** (`sfd_values_differ`: strictly lower
under dilution on `[0, 10/9)`), as do the prices (`sfd_dilution_lowers_prices`) and borrowing
rules. Higher legacy debt `(1 − δ)B` makes the low-price issue more attractive (the objective
contains `−(1 − δ)B q(B′)`): that is the dilution channel, and it is absent at `δ = 1`.

**With one-period debt the same economy has exactly one equilibrium** (`sfd_one_period_unique`,
proved directly: with `δ = 1` and linear utility `V^R(B, Y) = V^R(0, Y) − B`, the crisis capacity
is pinned at `6/7` and then prices and values are determined). So the multiplicity is due to
long-term debt.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

variable {Y : Type*} [Fintype Y]

variable (M : UEModel Y) (δ : ℝ) (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D Bh q : ℝ → Y → ℝ) in
/-- **AKMM, §24.4.3**, pp. 744–745, Markov perfect equilibrium with long-term debt of decay `δ`
((24.7)–(24.12)) and permanent exclusion (`ψ = 0`), with the book's asset lower bound `B′ ≥ 0`
and the borrowing limit `B′ ≤ B̄` (departure D13): states and choices in `[0, B̄]`; bounded
values `V`, `V^R`, `V^D`, a default rule `D̂`, a borrowing rule `B̂` and a price `q` with
(a) (24.9)–(24.11), (b) (24.12), (c) `D̂` and `B̂` optimal. -/
structure IsBoundedLongMPE : Prop where
  /-- Values are bounded. -/
  bdd : ∃ K, ∀ b y, 0 ≤ b → b ≤ M.bmax → V b y ≤ K
  /-- (a) (24.9). -/
  eq_24_9 : ∀ b y, 0 ≤ b → b ≤ M.bmax → V b y = max (VD y) (VR b y)
  /-- (a) (24.10) with `ψ = 0`. -/
  eq_24_10 : ∀ y, VD y = M.defaultRHS VD y
  /-- (a) (24.11): `V^R` bounds the objective over `0 ≤ B′ ≤ B̄` ... -/
  eq_24_11 : ∀ b y b', 0 ≤ b → b ≤ M.bmax → 0 ≤ b' → b' ≤ M.bmax →
    M.ldObj δ q V b y b' ≤ VR b y
  /-- (b) (24.12). -/
  eq_24_12 : ∀ b' y, 0 ≤ b' → b' ≤ M.bmax → q b' y =
    (1 + M.r)⁻¹ * ∑ j, M.P y j * ((1 - D b' j) * (δ + (1 - δ) * q (Bh b' j) j))
  /-- (c) the default rule is optimal (ties repaid). -/
  default_opt : ∀ b y, 0 ≤ b → b ≤ M.bmax → D b y = if VR b y < VD y then 1 else 0
  /-- The borrowing rule is feasible. -/
  borrow_mem : ∀ b y, 0 ≤ b → b ≤ M.bmax → 0 ≤ Bh b y ∧ Bh b y ≤ M.bmax
  /-- (c) ... and attains it. -/
  borrow_opt : ∀ b y, 0 ≤ b → b ≤ M.bmax → M.ldObj δ q V b y (Bh b y) = VR b y

/-- The economy of the strict multiplicity example: normal times `true` (income `2`, default
cost `3/2`) and an absorbing crisis `false` (income `1`, default cost `1/7`), reached with
probability `1/5`; `u(c) = c`, `β = 1/2`, `r = 1/5`, borrowing limit `B̄ = 3/2`. -/
noncomputable def sfd_econ : UEModel Bool where
  inc := fun y => if y then 2 else 1
  P := fun y j => if y then (if j then 4 / 5 else 1 / 5) else (if j then 0 else 1)
  markov := ⟨fun y j => by cases y <;> cases j <;> norm_num,
    fun y => by cases y <;> norm_num [Fintype.sum_bool]⟩
  u := fun c => c
  φ := fun c => if c = 1 then 1 / 7 else 3 / 2
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  r := 1 / 5
  r_pos := by norm_num
  bmax := 3 / 2
  bmax_nonneg := by norm_num

theorem sfd_bmax : sfd_econ.bmax = 3 / 2 := rfl

/-- The objective in normal times. -/
theorem sfd_obj_true (δ : ℝ) (q V : ℝ → Bool → ℝ) (b b' : ℝ) :
    sfd_econ.ldObj δ q V b true b' = 2 - δ * b + q b' true * (b' - (1 - δ) * b) +
      1 / 2 * (4 / 5 * V b' true + 1 / 5 * V b' false) := by
  simp only [UEModel.ldObj, sfd_econ, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]

/-- The objective in the crisis. -/
theorem sfd_obj_false (δ : ℝ) (q V : ℝ → Bool → ℝ) (b b' : ℝ) :
    sfd_econ.ldObj δ q V b false b' = 1 - δ * b + q b' false * (b' - (1 - δ) * b) +
      1 / 2 * V b' false := by
  simp only [UEModel.ldObj, sfd_econ, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  ring

/-- The price recursion (24.12) in normal times. -/
theorem sfd_price_true (δ : ℝ) (q D Bh : ℝ → Bool → ℝ) (b' : ℝ) :
    (1 + sfd_econ.r)⁻¹ * ∑ j, sfd_econ.P true j * ((1 - D b' j) * (δ + (1 - δ) * q (Bh b' j) j))
      = 5 / 6 * (4 / 5 * ((1 - D b' true) * (δ + (1 - δ) * q (Bh b' true) true)) +
        1 / 5 * ((1 - D b' false) * (δ + (1 - δ) * q (Bh b' false) false))) := by
  simp only [sfd_econ, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  norm_num

/-- The price recursion (24.12) in the crisis. -/
theorem sfd_price_false (δ : ℝ) (q D Bh : ℝ → Bool → ℝ) (b' : ℝ) :
    (1 + sfd_econ.r)⁻¹ * ∑ j, sfd_econ.P false j * ((1 - D b' j) * (δ + (1 - δ) * q (Bh b' j) j))
      = 5 / 6 * ((1 - D b' false) * (δ + (1 - δ) * q (Bh b' false) false)) := by
  simp only [sfd_econ, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  norm_num

/-- The default values: (24.10) in normal times and in the crisis. -/
theorem sfd_defaultRHS (VD : Bool → ℝ) :
    sfd_econ.defaultRHS VD true = 1 / 2 + 1 / 2 * (4 / 5 * VD true + 1 / 5 * VD false) ∧
      sfd_econ.defaultRHS VD false = 6 / 7 + 1 / 2 * VD false := by
  simp only [UEModel.defaultRHS, sfd_econ, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  norm_num

/-- The default values of the example: `47/42` in normal times, `12/7` in the crisis. -/
noncomputable def sfd_VD (y : Bool) : ℝ := if y then 47 / 42 else 12 / 7

/-- `sfd_VD` solves (24.10), and it is the only solution. -/
theorem sfd_VD_iff (VD : Bool → ℝ) : (∀ y, VD y = sfd_econ.defaultRHS VD y) ↔ VD = sfd_VD := by
  obtain ⟨h1, h2⟩ := sfd_defaultRHS VD
  constructor
  · intro h
    have ht := h true
    have hf := h false
    rw [h1] at ht
    rw [h2] at hf
    funext y
    cases y <;> simp only [sfd_VD, ↓reduceIte, Bool.false_eq_true] <;> linarith
  · rintro rfl y
    cases y
    · rw [h2]; simp only [sfd_VD, ↓reduceIte, Bool.false_eq_true]; norm_num
    · rw [h1]; simp only [sfd_VD, ↓reduceIte, Bool.false_eq_true]; norm_num

/-- The default rule of both equilibria at `δ = 1/2`: never in normal times; in the crisis
exactly on debt above the safe level `1`. -/
noncomputable def sfd_D (b : ℝ) (y : Bool) : ℝ := if y then 0 else if 1 < b then 1 else 0

/-- The crisis repayment value of both equilibria at `δ = 1/2`: `18/7 − (6/7)B`. -/
noncomputable def sfd_VRL (b : ℝ) : ℝ := 18 / 7 - 6 / 7 * b

/-- The crisis price of both equilibria at `δ = 1/2`: risk-free `5/7` on the safe zone. -/
noncomputable def sfd_qL (b : ℝ) : ℝ := if b ≤ 1 then 5 / 7 else 0

/-- The crisis value: `max(12/7, 18/7 − (6/7)B)` is `18/7 − (6/7)B` on the safe zone. -/
theorem sfd_VL_eq (b : ℝ) :
    max (sfd_VD false) (sfd_VRL b) = if b ≤ 1 then 18 / 7 - 6 / 7 * b else 12 / 7 := by
  simp only [sfd_VD, sfd_VRL, Bool.false_eq_true, ↓reduceIte]
  split_ifs with h
  · exact max_eq_right (by linarith)
  · exact max_eq_left (by linarith)

/-- **The crisis block at `δ = 1/2`** (both equilibria): with the crisis price `sfd_qL` and the
crisis value `max(12/7, sfd_VRL)`, issuing up to the safe level `1` is optimal at every debt
`B ∈ [0, 3/2]`, with value `sfd_VRL B`. -/
theorem sfd_crisis_block (q V : ℝ → Bool → ℝ) (hq : ∀ b', q b' false = sfd_qL b')
    (hV : ∀ b', V b' false = max (sfd_VD false) (sfd_VRL b')) (b : ℝ) (hb1 : b ≤ 3 / 2) :
    (∀ b', 0 ≤ b' → b' ≤ 3 / 2 → sfd_econ.ldObj (1 / 2) q V b false b' ≤ sfd_VRL b) ∧
      sfd_econ.ldObj (1 / 2) q V b false 1 = sfd_VRL b := by
  constructor
  · intro b' _ _
    rw [sfd_obj_false, hq, hV, sfd_VL_eq]
    unfold sfd_qL sfd_VRL
    split_ifs <;> linarith
  · rw [sfd_obj_false, hq, hV, sfd_VL_eq]
    unfold sfd_qL sfd_VRL
    norm_num
    ring

/-- The crisis block of the price recursion: with the crisis default rule `sfd_D` and borrowing
`1`, (24.12) gives `sfd_qL`. -/
theorem sfd_crisis_price (q Bh : ℝ → Bool → ℝ) (hq : ∀ b', q b' false = sfd_qL b')
    (hBh : ∀ b', Bh b' false = 1) (b' : ℝ) :
    q b' false = (1 + sfd_econ.r)⁻¹ * ∑ j, sfd_econ.P false j *
      ((1 - sfd_D b' j) * (1 / 2 + (1 - 1 / 2) * q (Bh b' j) j)) := by
  rw [sfd_price_false, hBh, hq, hq]
  unfold sfd_qL sfd_D
  simp only [Bool.false_eq_true, ↓reduceIte, le_refl]
  by_cases h : b' ≤ 1
  · simp only [h, not_lt.2 h, ↓reduceIte]
    norm_num
  · simp only [h, lt_of_not_ge h, ↓reduceIte]
    norm_num

/-- The crisis default rule: `sfd_VRL B < 12/7` iff `B > 1`. -/
theorem sfd_crisis_default (b : ℝ) :
    sfd_D b false = if sfd_VRL b < sfd_VD false then 1 else 0 := by
  unfold sfd_D sfd_VRL sfd_VD
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h : 1 < b
  · have h' : 18 / 7 - 6 / 7 * b < 12 / 7 := by linarith
    simp only [h, h', ↓reduceIte]
  · have h' : ¬ 18 / 7 - 6 / 7 * b < 12 / 7 := by linarith
    simp only [h, h', ↓reduceIte]

/-- The no-dilution repayment values: in normal times `89/21 − (6/7)B` up to `10/9` (the
sovereign holds or brings its debt to the safe level `1`) and `173/42 − (3/4)B` above (it stays
at `B̄`); in the crisis `sfd_VRL`. -/
noncomputable def sfd_VRN (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 10 / 9 then 89 / 21 - 6 / 7 * b else 173 / 42 - 3 / 4 * b) else sfd_VRL b

/-- The no-dilution prices: in normal times `5/7` (risk-free) on the safe zone `[0, 1]`, `4/7`
on `(1, 10/9]` (repaid unless the crisis comes, then deleveraged), `1/2` above; in the crisis
`sfd_qL`. -/
noncomputable def sfd_qN (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 1 then 5 / 7 else if b ≤ 10 / 9 then 4 / 7 else 1 / 2) else sfd_qL b

/-- The no-dilution borrowing rule: in normal times debt `1` from `B ≤ 10/9`, `B̄ = 3/2`
above; debt `1` in the crisis. -/
noncomputable def sfd_BhN (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 10 / 9 then 1 else 3 / 2) else 1

/-- The self-fulfilling-dilution repayment values: in normal times `437/105 − (23/28)B` up to
`3/5` and `173/42 − (3/4)B` above (the sovereign dilutes to `B̄`); in the crisis `sfd_VRL`. -/
noncomputable def sfd_VRS (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 3 / 5 then 437 / 105 - 23 / 28 * b else 173 / 42 - 3 / 4 * b) else sfd_VRL b

/-- The self-fulfilling-dilution prices: in normal times `29/42` on `[0, 3/5]`, `9/14` on
`(3/5, 1]` (lenders expect dilution to `B̄`), `1/2` above; in the crisis `sfd_qL`. -/
noncomputable def sfd_qS (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 3 / 5 then 29 / 42 else if b ≤ 1 then 9 / 14 else 1 / 2) else sfd_qL b

/-- The self-fulfilling-dilution borrowing rule: in normal times debt `1` from `B ≤ 3/5`,
`B̄ = 3/2` above; debt `1` in the crisis. -/
noncomputable def sfd_BhS (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 3 / 5 then 1 else 3 / 2) else 1

/-- In normal times the no-dilution repayment value exceeds the default value `47/42`. -/
theorem sfd_VN_true (b : ℝ) (hb1 : b ≤ 3 / 2) :
    max (sfd_VD true) (sfd_VRN b true) = sfd_VRN b true := by
  apply max_eq_right
  unfold sfd_VD sfd_VRN
  simp only [↓reduceIte]
  split_ifs <;> linarith

/-- In normal times the dilution repayment value exceeds the default value `47/42`. -/
theorem sfd_VS_true (b : ℝ) (hb1 : b ≤ 3 / 2) :
    max (sfd_VD true) (sfd_VRS b true) = sfd_VRS b true := by
  apply max_eq_right
  unfold sfd_VD sfd_VRS
  simp only [↓reduceIte]
  split_ifs <;> linarith

/-- **No dilution is a Markov perfect equilibrium** at `δ = 1/2` (AKMM, p. 901, beyond the
text): `sfd_VRN`, `sfd_D`, `sfd_BhN`, `sfd_qN` satisfy every condition of the definition at
every state `B ∈ [0, 3/2]` and against every `B′ ∈ [0, 3/2]`. -/
theorem sfd_no_dilution_mpe :
    IsBoundedLongMPE sfd_econ (1 / 2) (fun b y => max (sfd_VD y) (sfd_VRN b y)) sfd_VRN sfd_VD
      sfd_D sfd_BhN sfd_qN := by
  have hqL : ∀ b', sfd_qN b' false = sfd_qL b' := fun _ => rfl
  have hVL : ∀ b', (fun b y => max (sfd_VD y) (sfd_VRN b y)) b' false =
      max (sfd_VD false) (sfd_VRL b') := fun _ => rfl
  have hRL : ∀ b', sfd_VRN b' false = sfd_VRL b' := fun _ => rfl
  refine ⟨⟨5, fun b y _ hb1 => ?_⟩, fun _ _ _ _ => rfl, (sfd_VD_iff _).2 rfl,
    fun b y b' hb0 hb1 hb0' hb1' => ?_, fun b' y hb0' hb1' => ?_, fun b y _ hb1 => ?_,
    fun b y _ _ => ?_, fun b y hb0 hb1 => ?_⟩
  · -- bounded values
    rw [sfd_bmax] at hb1
    apply max_le
    · unfold sfd_VD; split_ifs <;> norm_num
    · unfold sfd_VRN sfd_VRL; split_ifs <;> linarith
  · -- (24.11)
    rw [sfd_bmax] at hb1 hb1'
    cases y
    · exact (sfd_crisis_block _ _ hqL hVL b hb1).1 b' hb0' hb1'
    · rw [sfd_obj_true, sfd_VN_true b' hb1', hRL, sfd_VL_eq]
      unfold sfd_VRN sfd_qN
      simp only [↓reduceIte]
      split_ifs <;> linarith
  · -- (24.12)
    cases y
    · exact sfd_crisis_price _ _ hqL (fun _ => rfl) b'
    · rw [sfd_price_true]
      unfold sfd_qN sfd_D sfd_BhN sfd_qL
      simp only [↓reduceIte, Bool.false_eq_true]
      rw [sfd_bmax] at hb1'
      by_cases h1 : b' ≤ 1
      · have h2 : b' ≤ 10 / 9 := by linarith
        simp only [h1, h2, not_lt.2 h1, ↓reduceIte]
        norm_num
      · by_cases h2 : b' ≤ 10 / 9
        · simp only [h1, h2, lt_of_not_ge h1, ↓reduceIte]
          norm_num
        · simp only [h1, h2, lt_of_not_ge h1, ↓reduceIte]
          norm_num
  · -- the default rule
    cases y
    · exact sfd_crisis_default b
    · rw [sfd_bmax] at hb1
      have h : ¬ sfd_VRN b true < sfd_VD true := by
        rw [not_lt, ← sfd_VN_true b hb1]
        exact le_max_left _ _
      simp only [sfd_D, h, ↓reduceIte]
  · -- feasibility
    rw [sfd_bmax]
    unfold sfd_BhN
    cases y
    · norm_num
    · simp only [↓reduceIte]
      split_ifs <;> norm_num
  · -- optimality
    rw [sfd_bmax] at hb1
    cases y
    · exact (sfd_crisis_block _ _ hqL hVL b hb1).2
    · rw [sfd_obj_true]
      unfold sfd_BhN
      simp only [↓reduceIte]
      by_cases h : b ≤ 10 / 9
      · simp only [h, ↓reduceIte]
        rw [sfd_VN_true 1 (by norm_num), hRL, sfd_VL_eq]
        unfold sfd_VRN sfd_qN
        simp only [h, ↓reduceIte]
        norm_num
        ring
      · simp only [h, ↓reduceIte]
        rw [sfd_VN_true (3 / 2) (by norm_num), hRL, sfd_VL_eq]
        unfold sfd_VRN sfd_qN
        simp only [h, ↓reduceIte]
        norm_num
        ring

/-- **Self-fulfilling dilution is a Markov perfect equilibrium** at `δ = 1/2` (AKMM, p. 901,
beyond the text): `sfd_VRS`, `sfd_D`, `sfd_BhS`, `sfd_qS` satisfy every condition of the
definition at every state `B ∈ [0, 3/2]` and against every `B′ ∈ [0, 3/2]`. -/
theorem sfd_dilution_mpe :
    IsBoundedLongMPE sfd_econ (1 / 2) (fun b y => max (sfd_VD y) (sfd_VRS b y)) sfd_VRS sfd_VD
      sfd_D sfd_BhS sfd_qS := by
  have hqL : ∀ b', sfd_qS b' false = sfd_qL b' := fun _ => rfl
  have hVL : ∀ b', (fun b y => max (sfd_VD y) (sfd_VRS b y)) b' false =
      max (sfd_VD false) (sfd_VRL b') := fun _ => rfl
  have hRL : ∀ b', sfd_VRS b' false = sfd_VRL b' := fun _ => rfl
  refine ⟨⟨5, fun b y _ hb1 => ?_⟩, fun _ _ _ _ => rfl, (sfd_VD_iff _).2 rfl,
    fun b y b' hb0 hb1 hb0' hb1' => ?_, fun b' y hb0' hb1' => ?_, fun b y _ hb1 => ?_,
    fun b y _ _ => ?_, fun b y hb0 hb1 => ?_⟩
  · -- bounded values
    rw [sfd_bmax] at hb1
    apply max_le
    · unfold sfd_VD; split_ifs <;> norm_num
    · unfold sfd_VRS sfd_VRL; split_ifs <;> linarith
  · -- (24.11)
    rw [sfd_bmax] at hb1 hb1'
    cases y
    · exact (sfd_crisis_block _ _ hqL hVL b hb1).1 b' hb0' hb1'
    · rw [sfd_obj_true, sfd_VS_true b' hb1', hRL, sfd_VL_eq]
      unfold sfd_VRS sfd_qS
      simp only [↓reduceIte]
      split_ifs <;> linarith
  · -- (24.12)
    cases y
    · exact sfd_crisis_price _ _ hqL (fun _ => rfl) b'
    · rw [sfd_price_true]
      unfold sfd_qS sfd_D sfd_BhS sfd_qL
      simp only [↓reduceIte, Bool.false_eq_true]
      rw [sfd_bmax] at hb1'
      by_cases h1 : b' ≤ 3 / 5
      · have h2 : b' ≤ 1 := by linarith
        simp only [h1, not_lt.2 h2, ↓reduceIte]
        norm_num
      · by_cases h2 : b' ≤ 1
        · simp only [h1, h2, not_lt.2 h2, ↓reduceIte]
          norm_num
        · simp only [h1, h2, lt_of_not_ge h2, ↓reduceIte]
          norm_num
  · -- the default rule
    cases y
    · exact sfd_crisis_default b
    · rw [sfd_bmax] at hb1
      have h : ¬ sfd_VRS b true < sfd_VD true := by
        rw [not_lt, ← sfd_VS_true b hb1]
        exact le_max_left _ _
      simp only [sfd_D, h, ↓reduceIte]
  · -- feasibility
    rw [sfd_bmax]
    unfold sfd_BhS
    cases y
    · norm_num
    · simp only [↓reduceIte]
      split_ifs <;> norm_num
  · -- optimality
    rw [sfd_bmax] at hb1
    cases y
    · exact (sfd_crisis_block _ _ hqL hVL b hb1).2
    · rw [sfd_obj_true]
      unfold sfd_BhS
      simp only [↓reduceIte]
      by_cases h : b ≤ 3 / 5
      · simp only [h, ↓reduceIte]
        rw [sfd_VS_true 1 (by norm_num), hRL, sfd_VL_eq]
        unfold sfd_VRS sfd_qS
        simp only [h, ↓reduceIte]
        norm_num
        ring
      · simp only [h, ↓reduceIte]
        rw [sfd_VS_true (3 / 2) (by norm_num), hRL, sfd_VL_eq]
        unfold sfd_VRS sfd_qS
        simp only [h, ↓reduceIte]
        norm_num
        ring

/-- **The two equilibria have different values**: in normal times the repayment value (and
the value) under self-fulfilling dilution is strictly below the no-dilution value at every debt
below `10/9`, and equal from `10/9` on. -/
theorem sfd_values_differ (b : ℝ) :
    (b < 10 / 9 → sfd_VRS b true < sfd_VRN b true) ∧
      (10 / 9 ≤ b → sfd_VRS b true = sfd_VRN b true) := by
  unfold sfd_VRS sfd_VRN
  simp only [↓reduceIte]
  constructor
  · intro h
    split_ifs <;> linarith
  · intro h
    have h1 : ¬ b ≤ 3 / 5 := by linarith
    by_cases h2 : b ≤ 10 / 9
    · have h3 : b = 10 / 9 := le_antisymm h2 h
      simp only [h1, h2, ↓reduceIte]
      rw [h3]
      norm_num
    · simp only [h1, h2, ↓reduceIte]

/-- **Expected dilution lowers prices**: the dilution prices are never above the no-dilution
prices, and in normal times strictly below them on `[0, 10/9]`. -/
theorem sfd_dilution_lowers_prices (b' : ℝ) (y : Bool) :
    sfd_qS b' y ≤ sfd_qN b' y ∧ (b' ≤ 10 / 9 → sfd_qS b' true < sfd_qN b' true) := by
  unfold sfd_qS sfd_qN
  constructor
  · cases y
    · exact le_rfl
    · simp only [↓reduceIte]
      split_ifs <;> linarith
  · intro h
    simp only [↓reduceIte]
    split_ifs <;> linarith

/-- **The sovereign strictly prefers to dilute when lenders expect it, and strictly prefers not
to when they do not**: at every debt `B ∈ (3/5, 10/9)` in normal times, facing the no-dilution
prices the sovereign strictly prefers debt `1` (safe) to `B̄ = 3/2`, and facing the dilution
prices it strictly prefers `B̄` to `1`. -/
theorem sfd_strict_preference (b : ℝ) (hb : 3 / 5 < b) (hb' : b < 10 / 9) :
    sfd_econ.ldObj (1 / 2) sfd_qN (fun b y => max (sfd_VD y) (sfd_VRN b y)) b true (3 / 2) <
        sfd_econ.ldObj (1 / 2) sfd_qN (fun b y => max (sfd_VD y) (sfd_VRN b y)) b true 1 ∧
      sfd_econ.ldObj (1 / 2) sfd_qS (fun b y => max (sfd_VD y) (sfd_VRS b y)) b true 1 <
        sfd_econ.ldObj (1 / 2) sfd_qS (fun b y => max (sfd_VD y) (sfd_VRS b y)) b true (3 / 2) := by
  have hRN : ∀ b', sfd_VRN b' false = sfd_VRL b' := fun _ => rfl
  have hRS : ∀ b', sfd_VRS b' false = sfd_VRL b' := fun _ => rfl
  rw [sfd_obj_true, sfd_obj_true, sfd_obj_true, sfd_obj_true, sfd_VN_true 1 (by norm_num),
    sfd_VN_true (3 / 2) (by norm_num), sfd_VS_true 1 (by norm_num),
    sfd_VS_true (3 / 2) (by norm_num), hRN, hRN, hRS, hRS, sfd_VL_eq, sfd_VL_eq]
  unfold sfd_qN sfd_qS sfd_VRN sfd_VRS
  norm_num
  constructor <;> linarith

/-- **Two Markov perfect equilibria with long-term debt and strictly different values** (AKMM,
p. 901, beyond the text; Aguiar–Amador's self-fulfilling debt dilution): at `δ = 1/2` the
economy `sfd_econ` has the no-dilution equilibrium and the self-fulfilling-dilution
equilibrium, with the same default rule, and the value at zero debt is strictly lower under
dilution. -/
theorem sfd_two_mpe :
    IsBoundedLongMPE sfd_econ (1 / 2) (fun b y => max (sfd_VD y) (sfd_VRN b y)) sfd_VRN sfd_VD
        sfd_D sfd_BhN sfd_qN ∧
      IsBoundedLongMPE sfd_econ (1 / 2) (fun b y => max (sfd_VD y) (sfd_VRS b y)) sfd_VRS
        sfd_VD sfd_D sfd_BhS sfd_qS ∧
      max (sfd_VD true) (sfd_VRS 0 true) < max (sfd_VD true) (sfd_VRN 0 true) := by
  refine ⟨sfd_no_dilution_mpe, sfd_dilution_mpe, ?_⟩
  rw [sfd_VN_true 0 (by norm_num), sfd_VS_true 0 (by norm_num)]
  exact (sfd_values_differ 0).1 (by norm_num)

/-- The objective at `δ = 1` in normal times. -/
theorem sfd_obj_one_true (q V : ℝ → Bool → ℝ) (b b' : ℝ) :
    sfd_econ.ldObj 1 q V b true b' =
      2 - b + q b' true * b' + 1 / 2 * (4 / 5 * V b' true + 1 / 5 * V b' false) := by
  rw [sfd_obj_true]
  ring

/-- The objective at `δ = 1` in the crisis. -/
theorem sfd_obj_one_false (q V : ℝ → Bool → ℝ) (b b' : ℝ) :
    sfd_econ.ldObj 1 q V b false b' = 1 - b + q b' false * b' + 1 / 2 * V b' false := by
  rw [sfd_obj_false]
  ring

/-- With one-period debt and linear utility the objective is the objective at zero debt
minus the debt. -/
theorem sfd_obj_one_shift (q V : ℝ → Bool → ℝ) (b b' : ℝ) (y : Bool) :
    sfd_econ.ldObj 1 q V b y b' = sfd_econ.ldObj 1 q V 0 y b' - b := by
  cases y
  · rw [sfd_obj_one_false, sfd_obj_one_false]; ring
  · rw [sfd_obj_one_true, sfd_obj_one_true]; ring

/-- The repayment values of the one-period-debt equilibrium: `30/7 − B` in normal times,
`18/7 − B` in the crisis. -/
noncomputable def sfd_VR1 (b : ℝ) (y : Bool) : ℝ := if y then 30 / 7 - b else 18 / 7 - b

/-- The default rule of the one-period-debt equilibrium: never in normal times; in the crisis
on debt above `6/7`. -/
noncomputable def sfd_D1 (b : ℝ) (y : Bool) : ℝ := if y then 0 else if 6 / 7 < b then 1 else 0

/-- The prices of the one-period-debt equilibrium: `5/6` on `[0, 6/7]`; above, `2/3` in normal
times and `0` in the crisis. -/
noncomputable def sfd_q1 (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 6 / 7 then 5 / 6 else 2 / 3) else (if b ≤ 6 / 7 then 5 / 6 else 0)

/-- The borrowing rule of the one-period-debt equilibrium: `B̄ = 3/2` in normal times, `6/7` in
the crisis. -/
noncomputable def sfd_Bh1 (_ : ℝ) (y : Bool) : ℝ := if y then 3 / 2 else 6 / 7

/-- **With one-period debt the economy has a Markov perfect equilibrium** (`δ = 1`): the
crisis capacity is `6/7`, and in normal times the sovereign borrows up to `B̄`. -/
theorem sfd_one_period_mpe :
    IsBoundedLongMPE sfd_econ 1 (fun b y => max (sfd_VD y) (sfd_VR1 b y)) sfd_VR1 sfd_VD sfd_D1
      sfd_Bh1 sfd_q1 := by
  have hVH : ∀ b', b' ≤ 3 / 2 → max (sfd_VD true) (sfd_VR1 b' true) = 30 / 7 - b' :=
    fun b' h => by
      unfold sfd_VD sfd_VR1
      simp only [↓reduceIte]
      exact max_eq_right (by linarith)
  have hVL : ∀ b', max (sfd_VD false) (sfd_VR1 b' false) =
      if b' ≤ 6 / 7 then 18 / 7 - b' else 12 / 7 := fun b' => by
    unfold sfd_VD sfd_VR1
    simp only [↓reduceIte, Bool.false_eq_true]
    split_ifs with h
    · exact max_eq_right (by linarith)
    · exact max_eq_left (by linarith)
  refine ⟨⟨5, fun b y _ hb1 => ?_⟩, fun _ _ _ _ => rfl, (sfd_VD_iff _).2 rfl,
    fun b y b' hb0 hb1 hb0' hb1' => ?_, fun b' y hb0' hb1' => ?_, fun b y _ hb1 => ?_,
    fun b y _ _ => ?_, fun b y hb0 hb1 => ?_⟩
  · apply max_le
    · unfold sfd_VD; split_ifs <;> norm_num
    · unfold sfd_VR1; split_ifs <;> linarith
  · rw [sfd_bmax] at hb1'
    cases y
    · rw [sfd_obj_one_false, hVL]
      unfold sfd_q1 sfd_VR1
      simp only [↓reduceIte, Bool.false_eq_true]
      split_ifs <;> linarith
    · rw [sfd_obj_one_true, hVH b' hb1', hVL]
      unfold sfd_q1 sfd_VR1
      simp only [↓reduceIte]
      split_ifs <;> linarith
  · cases y
    · rw [sfd_price_false]
      unfold sfd_q1 sfd_D1
      simp only [↓reduceIte, Bool.false_eq_true]
      by_cases h : b' ≤ 6 / 7
      · simp only [h, not_lt.2 h, ↓reduceIte]; norm_num
      · simp only [h, lt_of_not_ge h, ↓reduceIte]; norm_num
    · rw [sfd_price_true]
      unfold sfd_q1 sfd_D1
      simp only [↓reduceIte, Bool.false_eq_true]
      by_cases h : b' ≤ 6 / 7
      · simp only [h, not_lt.2 h, ↓reduceIte]; norm_num
      · simp only [h, lt_of_not_ge h, ↓reduceIte]; norm_num
  · rw [sfd_bmax] at hb1
    unfold sfd_D1 sfd_VR1 sfd_VD
    cases y
    · simp only [↓reduceIte, Bool.false_eq_true]
      by_cases h : 6 / 7 < b
      · have h' : 18 / 7 - b < 12 / 7 := by linarith
        simp only [h, h', ↓reduceIte]
      · have h' : ¬ 18 / 7 - b < 12 / 7 := by linarith
        simp only [h, h', ↓reduceIte]
    · have h' : ¬ 30 / 7 - b < 47 / 42 := by linarith
      simp only [h', ↓reduceIte]
  · rw [sfd_bmax]
    unfold sfd_Bh1
    cases y <;> norm_num
  · rw [sfd_bmax] at hb1
    cases y
    · rw [sfd_obj_one_false, hVL]
      unfold sfd_q1 sfd_VR1 sfd_Bh1
      norm_num
      ring
    · rw [sfd_obj_one_true, hVH _ (by unfold sfd_Bh1; norm_num), hVL]
      unfold sfd_q1 sfd_VR1 sfd_Bh1
      norm_num
      ring

/-- **Every Markov perfect equilibrium with one-period debt is the one of
`sfd_one_period_mpe`** (on the state space `[0, 3/2]`). With `δ = 1` and linear utility the
repayment value is `V^R(0, Y) − B` (the objective is the objective at zero debt minus `B`). The
default value solves (24.10); in normal times repaying at least matches defaulting (`φ ≥ B̄`).
In the crisis the debt capacity `V^R(0, L) − 12/7` is pinned at `6/7`: a larger value could not
be financed, a smaller one leaves a profitable debt issue below the capacity unused. Then prices
are determined, and so is `V^R(0, H) = 30/7`. -/
theorem sfd_one_period_char {V VR D Bh q : ℝ → Bool → ℝ} {VD : Bool → ℝ}
    (h : IsBoundedLongMPE sfd_econ 1 V VR VD D Bh q) :
    VD = sfd_VD ∧ ∀ b y, 0 ≤ b → b ≤ sfd_econ.bmax →
      VR b y = sfd_VR1 b y ∧ D b y = sfd_D1 b y ∧ q b y = sfd_q1 b y ∧
        V b y = max (sfd_VD y) (sfd_VR1 b y) := by
  have hVD : VD = sfd_VD := (sfd_VD_iff VD).1 h.eq_24_10
  have hbm := sfd_bmax
  have hVDt : VD true = 47 / 42 := by rw [hVD]; rfl
  have hVDf : VD false = 12 / 7 := by rw [hVD]; rfl
  -- the repayment value is `V^R(0, Y) − B`
  have hVR : ∀ b y, 0 ≤ b → b ≤ 3 / 2 → VR b y = VR 0 y - b := by
    intro b y hb0 hb1
    obtain ⟨hm0, hm1⟩ := h.borrow_mem b y hb0 (by rw [hbm]; exact hb1)
    obtain ⟨hn0, hn1⟩ := h.borrow_mem 0 y le_rfl (by rw [hbm]; norm_num)
    have e1 := h.borrow_opt b y hb0 (by rw [hbm]; exact hb1)
    have i1 := h.eq_24_11 0 y (Bh b y) le_rfl (by rw [hbm]; norm_num) hm0 hm1
    have e0 := h.borrow_opt 0 y le_rfl (by rw [hbm]; norm_num)
    have i0 := h.eq_24_11 b y (Bh 0 y) hb0 (by rw [hbm]; exact hb1) hn0 hn1
    rw [sfd_obj_one_shift] at e1 i0
    linarith
  have hVge : ∀ b y, 0 ≤ b → b ≤ 3 / 2 → VD y ≤ V b y := fun b y hb0 hb1 => by
    rw [h.eq_24_9 b y hb0 (by rw [hbm]; exact hb1)]
    exact le_max_left _ _
  have hdef : ∀ b y, 0 ≤ b → b ≤ 3 / 2 → D b y = if VR b y < VD y then 1 else 0 :=
    fun b y hb0 hb1 => h.default_opt b y hb0 (by rw [hbm]; exact hb1)
  have hprice : ∀ b' y, 0 ≤ b' → b' ≤ 3 / 2 → q b' y = (1 + sfd_econ.r)⁻¹ *
      ∑ j, sfd_econ.P y j * ((1 - D b' j) * (1 + (1 - 1) * q (Bh b' j) j)) :=
    fun b' y hb0 hb1 => h.eq_24_12 b' y hb0 (by rw [hbm]; exact hb1)
  -- in normal times the sovereign repays
  have hH : ∀ b, 0 ≤ b → b ≤ 3 / 2 → 47 / 42 ≤ VR b true := by
    intro b hb0 hb1
    have i := h.eq_24_11 b true 0 hb0 (by rw [hbm]; exact hb1) le_rfl (by rw [hbm]; norm_num)
    rw [sfd_obj_one_true, mul_zero] at i
    have h1 := hVge 0 true le_rfl (by norm_num)
    have h2 := hVge 0 false le_rfl (by norm_num)
    rw [hVDt] at h1
    rw [hVDf] at h2
    linarith
  have hDt : ∀ b, 0 ≤ b → b ≤ 3 / 2 → D b true = 0 := fun b hb0 hb1 => by
    rw [hdef b true hb0 hb1, hVDt]
    simp only [not_lt.2 (hH b hb0 hb1), ↓reduceIte]
  -- the crisis
  have hVf : ∀ b, 0 ≤ b → b ≤ 3 / 2 → V b false = max (12 / 7) (VR 0 false - b) :=
    fun b hb0 hb1 => by
      rw [h.eq_24_9 b false hb0 (by rw [hbm]; exact hb1), hVDf, hVR b false hb0 hb1]
  have hDf : ∀ b, 0 ≤ b → b ≤ 3 / 2 →
      D b false = if VR 0 false - b < 12 / 7 then 1 else 0 := fun b hb0 hb1 => by
    rw [hdef b false hb0 hb1, hVDf, hVR b false hb0 hb1]
  have hqf : ∀ b', 0 ≤ b' → b' ≤ 3 / 2 → q b' false = 5 / 6 * (1 - D b' false) :=
    fun b' hb0 hb1 => by
      rw [hprice b' false hb0 hb1, sfd_price_false]
      ring
  have hcL : VR 0 false = 18 / 7 := by
    obtain ⟨hn0, hn1⟩ := h.borrow_mem 0 false le_rfl (by rw [hbm]; norm_num)
    rw [hbm] at hn1
    have e := h.borrow_opt 0 false le_rfl (by rw [hbm]; norm_num)
    rw [sfd_obj_one_false, hqf _ hn0 hn1, hDf _ hn0 hn1, hVf _ hn0 hn1] at e
    apply le_antisymm
    · by_cases hlt : VR 0 false - Bh 0 false < 12 / 7
      · rw [max_eq_left hlt.le] at e
        simp only [hlt, ↓reduceIte] at e
        linarith
      · rw [max_eq_right (not_lt.1 hlt)] at e
        simp only [hlt, ↓reduceIte] at e
        linarith
    · by_contra hc
      rw [not_le] at hc
      by_cases h12 : 12 / 7 ≤ VR 0 false
      · have hs0 : 0 ≤ VR 0 false - 12 / 7 := by linarith
        have hs1 : VR 0 false - 12 / 7 ≤ 3 / 2 := by linarith
        have i := h.eq_24_11 0 false (VR 0 false - 12 / 7) le_rfl (by rw [hbm]; norm_num) hs0
          (by rw [hbm]; exact hs1)
        have hne : ¬ VR 0 false - (VR 0 false - 12 / 7) < 12 / 7 := by linarith
        rw [sfd_obj_one_false, hqf _ hs0 hs1, hDf _ hs0 hs1, hVf _ hs0 hs1] at i
        simp only [hne, ↓reduceIte] at i
        rw [max_eq_left (by linarith)] at i
        linarith
      · have i := h.eq_24_11 0 false 0 le_rfl (by rw [hbm]; norm_num) le_rfl
          (by rw [hbm]; norm_num)
        rw [sfd_obj_one_false, mul_zero] at i
        have h2 := hVge 0 false le_rfl (by norm_num)
        rw [hVDf] at h2
        linarith
  have hDf' : ∀ b, 0 ≤ b → b ≤ 3 / 2 → D b false = sfd_D1 b false := fun b hb0 hb1 => by
    rw [hDf b hb0 hb1, hcL]
    unfold sfd_D1
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hb : 6 / 7 < b
    · have h' : 18 / 7 - b < 12 / 7 := by linarith
      simp only [hb, h', ↓reduceIte]
    · have h' : ¬ 18 / 7 - b < 12 / 7 := by linarith
      simp only [hb, h', ↓reduceIte]
  have hqt : ∀ b', 0 ≤ b' → b' ≤ 3 / 2 → q b' true = 5 / 6 * (4 / 5 + 1 / 5 * (1 - D b' false)) :=
    fun b' hb0 hb1 => by
      rw [hprice b' true hb0 hb1, sfd_price_true, hDt b' hb0 hb1]
      ring
  -- normal times
  have hVt : ∀ b, 0 ≤ b → b ≤ 3 / 2 → V b true = VR 0 true - b := fun b hb0 hb1 => by
    rw [h.eq_24_9 b true hb0 (by rw [hbm]; exact hb1), hVDt, hVR b true hb0 hb1]
    exact max_eq_right (by rw [← hVR b true hb0 hb1]; exact hH b hb0 hb1)
  have hcH : VR 0 true = 30 / 7 := by
    obtain ⟨hn0, hn1⟩ := h.borrow_mem 0 true le_rfl (by rw [hbm]; norm_num)
    rw [hbm] at hn1
    have e := h.borrow_opt 0 true le_rfl (by rw [hbm]; norm_num)
    rw [sfd_obj_one_true, hqt _ hn0 hn1, hDf' _ hn0 hn1, hVt _ hn0 hn1, hVf _ hn0 hn1,
      hcL] at e
    have i := h.eq_24_11 0 true (3 / 2) le_rfl (by rw [hbm]; norm_num) (by norm_num)
      (by rw [hbm])
    rw [sfd_obj_one_true, hqt _ (by norm_num) le_rfl, hDf' _ (by norm_num) le_rfl,
      hVt _ (by norm_num) le_rfl, hVf _ (by norm_num) le_rfl, hcL] at i
    unfold sfd_D1 at e i
    simp only [Bool.false_eq_true, ↓reduceIte] at e i
    norm_num at i
    apply le_antisymm
    · by_cases hb : 6 / 7 < Bh 0 true
      · simp only [hb, ↓reduceIte] at e
        rw [max_eq_left (by linarith)] at e
        linarith
      · simp only [hb, ↓reduceIte] at e
        rw [max_eq_right (by linarith)] at e
        linarith
    · linarith
  refine ⟨hVD, fun b y hb0 hb1 => ?_⟩
  rw [hbm] at hb1
  have hq1 : q b y = sfd_q1 b y := by
    cases y
    · rw [hqf b hb0 hb1, hDf' b hb0 hb1]
      unfold sfd_D1 sfd_q1
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hb : b ≤ 6 / 7
      · simp only [hb, not_lt.2 hb, ↓reduceIte]; norm_num
      · simp only [hb, lt_of_not_ge hb, ↓reduceIte]; norm_num
    · rw [hqt b hb0 hb1, hDf' b hb0 hb1]
      unfold sfd_D1 sfd_q1
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hb : b ≤ 6 / 7
      · simp only [hb, not_lt.2 hb, ↓reduceIte]; norm_num
      · simp only [hb, lt_of_not_ge hb, ↓reduceIte]; norm_num
  have hVR1 : VR b y = sfd_VR1 b y := by
    rw [hVR b y hb0 hb1]
    unfold sfd_VR1
    cases y
    · rw [hcL]; rfl
    · rw [hcH]; rfl
  refine ⟨hVR1, ?_, hq1, ?_⟩
  · cases y
    · exact hDf' b hb0 hb1
    · rw [hDt b hb0 hb1]; rfl
  · rw [h.eq_24_9 b y hb0 (by rw [hbm]; exact hb1), hVR1, hVD]

/-- **With one-period debt the same economy has exactly one Markov perfect equilibrium**
(AKMM, p. 901, beyond the text): it exists (`sfd_one_period_mpe`), and any two equilibria have
the same default values and, at every state in `[0, B̄]`, the same values, repayment values,
default rule and prices (`sfd_one_period_char`). So the multiplicity of `sfd_two_mpe` is due to
long-term debt. -/
theorem sfd_one_period_unique :
    (∃ (V VR : ℝ → Bool → ℝ) (VD : Bool → ℝ) (D Bh q : ℝ → Bool → ℝ),
      IsBoundedLongMPE sfd_econ 1 V VR VD D Bh q) ∧
      ∀ {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Bool → ℝ} {VD₁ VD₂ : Bool → ℝ},
        IsBoundedLongMPE sfd_econ 1 V₁ VR₁ VD₁ D₁ Bh₁ q₁ →
        IsBoundedLongMPE sfd_econ 1 V₂ VR₂ VD₂ D₂ Bh₂ q₂ →
        VD₁ = VD₂ ∧ ∀ b y, 0 ≤ b → b ≤ sfd_econ.bmax →
          V₁ b y = V₂ b y ∧ VR₁ b y = VR₂ b y ∧ D₁ b y = D₂ b y ∧ q₁ b y = q₂ b y := by
  refine ⟨⟨_, _, _, _, _, _, sfd_one_period_mpe⟩, fun h₁ h₂ => ?_⟩
  obtain ⟨e₁, f₁⟩ := sfd_one_period_char h₁
  obtain ⟨e₂, f₂⟩ := sfd_one_period_char h₂
  refine ⟨e₁.trans e₂.symm, fun b y hb0 hb1 => ?_⟩
  obtain ⟨a₁, b₁, c₁, d₁⟩ := f₁ b y hb0 hb1
  obtain ⟨a₂, b₂, c₂, d₂⟩ := f₂ b y hb0 hb1
  exact ⟨d₁.trans d₂.symm, a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm⟩

/-- **Strict multiplicity due to long-term debt** (AKMM, p. 901; Aguiar and Amador 2020,
beyond the text): the economy `sfd_econ` has two Markov perfect equilibria at `δ = 1/2` with
strictly different values (`sfd_two_mpe`), and exactly one at `δ = 1`
(`sfd_one_period_unique`). -/
theorem sfd_strict_multiplicity :
    (∃ (V₁ VR₁ V₂ VR₂ : ℝ → Bool → ℝ) (VD : Bool → ℝ) (D Bh₁ q₁ Bh₂ q₂ : ℝ → Bool → ℝ),
      IsBoundedLongMPE sfd_econ (1 / 2) V₁ VR₁ VD D Bh₁ q₁ ∧
        IsBoundedLongMPE sfd_econ (1 / 2) V₂ VR₂ VD D Bh₂ q₂ ∧ V₂ 0 true < V₁ 0 true) ∧
      (∃ (V VR : ℝ → Bool → ℝ) (VD : Bool → ℝ) (D Bh q : ℝ → Bool → ℝ),
        IsBoundedLongMPE sfd_econ 1 V VR VD D Bh q) ∧
      ∀ {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Bool → ℝ} {VD₁ VD₂ : Bool → ℝ},
        IsBoundedLongMPE sfd_econ 1 V₁ VR₁ VD₁ D₁ Bh₁ q₁ →
        IsBoundedLongMPE sfd_econ 1 V₂ VR₂ VD₂ D₂ Bh₂ q₂ →
        ∀ b y, 0 ≤ b → b ≤ sfd_econ.bmax → V₁ b y = V₂ b y := by
  obtain ⟨h1, h2, h3⟩ := sfd_two_mpe
  refine ⟨⟨_, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩, sfd_one_period_unique.1,
    fun h₁ h₂ b y hb0 hb1 => ((sfd_one_period_unique.2 h₁ h₂).2 b y hb0 hb1).1⟩

end AKMM.SovereignDefault
