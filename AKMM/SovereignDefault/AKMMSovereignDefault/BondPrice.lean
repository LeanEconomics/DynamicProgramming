/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.Basics
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The bond price recursion (24.12), (24.A.2) and (24.A.6)

AKMM, §24.4.2, (24.12), p. 744; Appendix 24.A.1, (24.A.2), p. 897 and (24.A.6), p. 900;
§24.4.4, p. 748 (one-period debt).

On a finite debt grid `Bd` and a finite income grid `Y` with Markov matrix `P` (Sargent and
Stachurski's `IsMarkov`, imported), the zero-profit price of a long-term bond given the
lenders' expected next-period behaviour is the fixed point of
`(Tq)(m, y) = (1 + r)⁻¹ Σ_j P(y, j)[1 − D(m, j)][δ + (1 − δ) Σ_h q(h, j) B(h | m, j)]`
(24.A.6), with a default probability `D ∈ [0, 1]` and a distribution `B(· | m, j)` over next
debt choices. The deterministic rules of (24.12)/(24.A.2) are the special case `D ∈ {0, 1}`,
`B(h | m, j) = 1{h = B̂(m, j)}`.

* `T` is a contraction of modulus `(1 − δ)/(1 + r) < 1` in the sup norm (`bp_contracting`), so
  the price exists, is unique and is the limit of the iteration (24.A.2) from any initial guess
  (`eq_24_A_6`, `eq_24_A_2`, `eq_24_12`); it lies in `[0, δ/(δ + r)]`, the upper end being the
  risk-free price, attained when the sovereign never defaults (`bp_riskfree`).
* **One-period debt** (`δ = 1`, p. 748): `q(m, y) = (1 + r)⁻¹ Σ_j P(y, j)[1 − D(m, j)]` depends
  only on the next-period default rule, not on the borrowing rule (`bp_one_period`,
  `bp_one_period_independent`); with long-term debt (`0 < δ < 1`) the borrowing rule of the
  next government changes today's price (`bp_long_term_depends_on_borrowing`), the source of
  the second time-inconsistency problem.

Departure: the book states (24.12) with a continuous income distribution `F(dY′ | Y)` and a
continuous debt choice; here both are on finite grids, the setting of Appendix 24.A.1.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

variable {Bd Y : Type*} [Fintype Bd] [Fintype Y]

/-- AKMM, (24.A.6), p. 900: the price operator with default probabilities `Dp` and borrowing
probabilities `Bp`. -/
noncomputable def bp_op (P : Matrix Y Y ℝ) (r δ : ℝ) (Dp : Bd → Y → ℝ) (Bp : Bd → Y → Bd → ℝ)
    (q : Bd → Y → ℝ) : Bd → Y → ℝ :=
  fun m y => (1 + r)⁻¹ * ∑ j, P y j * ((1 - Dp m j) * (δ + (1 - δ) * ∑ h, q h j * Bp m j h))

variable (P : Matrix Y Y ℝ) (r δ : ℝ) (Dp : Bd → Y → ℝ) (Bp : Bd → Y → Bd → ℝ) in
/-- The admissibility conditions of (24.A.6): `P` Markov, `D ∈ [0, 1]`, `B(· | m, j)` a
probability distribution, `δ ∈ [0, 1]`, `r > −1` and `δ + r > 0`. -/
structure BPAdmissible : Prop where
  markov : IsMarkov P
  D_nonneg : ∀ m j, 0 ≤ Dp m j
  D_le_one : ∀ m j, Dp m j ≤ 1
  B_nonneg : ∀ m j h, 0 ≤ Bp m j h
  B_sum : ∀ m j, ∑ h, Bp m j h = 1
  δ_nonneg : 0 ≤ δ
  δ_le_one : δ ≤ 1
  r_gt : -1 < r
  δr_pos : 0 < δ + r

/-- A concrete admissible specification: no default and staying at the current debt level,
for any Markov `P`, `δ ∈ [0, 1]`, `r > 0`. -/
theorem bp_admissible_example [DecidableEq Bd] {P : Matrix Y Y ℝ} (hP : IsMarkov P) {r δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : 0 < r) :
    BPAdmissible P r δ (fun _ _ => 0) (fun (m : Bd) (_ : Y) (h : Bd) => if m = h then 1 else 0)
    where
  markov := hP
  D_nonneg := fun _ _ => le_rfl
  D_le_one := fun _ _ => zero_le_one
  B_nonneg := fun _ _ _ => by split_ifs <;> norm_num
  B_sum := fun m _ => by simp
  δ_nonneg := hδ0
  δ_le_one := hδ1
  r_gt := by linarith
  δr_pos := by linarith

/-- The pointwise contraction estimate:
`|(Tq)(m, y) − (Tq′)(m, y)| ≤ (1 − δ)/(1 + r) ‖q − q′‖`. -/
theorem bp_op_sub_le {P : Matrix Y Y ℝ} {r δ : ℝ} {Dp : Bd → Y → ℝ} {Bp : Bd → Y → Bd → ℝ}
    (hA : BPAdmissible P r δ Dp Bp) (q q' : Bd → Y → ℝ) (m : Bd) (y : Y) :
    |bp_op P r δ Dp Bp q m y - bp_op P r δ Dp Bp q' m y| ≤ (1 - δ) / (1 + r) * ‖q - q'‖ := by
  have hr1 : 0 < 1 + r := by linarith [hA.r_gt]
  have hδ' : 0 ≤ 1 - δ := by linarith [hA.δ_le_one]
  have hcomp : ∀ h j, |q h j - q' h j| ≤ ‖q - q'‖ := fun h j => by
    have h1 := norm_le_pi_norm ((q - q') h) j
    have h2 := norm_le_pi_norm (q - q') h
    rw [Real.norm_eq_abs] at h1
    exact h1.trans h2
  have hinner : ∀ j, |∑ h, q h j * Bp m j h - ∑ h, q' h j * Bp m j h| ≤ ‖q - q'‖ := by
    intro j
    rw [← sum_sub_distrib]
    calc |∑ h, (q h j * Bp m j h - q' h j * Bp m j h)|
        ≤ ∑ h, |q h j * Bp m j h - q' h j * Bp m j h| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ h, ‖q - q'‖ * Bp m j h := sum_le_sum fun h _ => by
          rw [← sub_mul, abs_mul, abs_of_nonneg (hA.B_nonneg m j h)]
          exact mul_le_mul_of_nonneg_right (hcomp h j) (hA.B_nonneg m j h)
      _ = ‖q - q'‖ := by rw [← mul_sum, hA.B_sum, mul_one]
  have hdiff : bp_op P r δ Dp Bp q m y - bp_op P r δ Dp Bp q' m y =
      (1 + r)⁻¹ * ∑ j, P y j * ((1 - Dp m j) * ((1 - δ) *
        (∑ h, q h j * Bp m j h - ∑ h, q' h j * Bp m j h))) := by
    unfold bp_op
    rw [← mul_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 hr1), div_eq_inv_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hr1.le)
  calc |∑ j, P y j * ((1 - Dp m j) * ((1 - δ) *
        (∑ h, q h j * Bp m j h - ∑ h, q' h j * Bp m j h)))|
      ≤ ∑ j, |P y j * ((1 - Dp m j) * ((1 - δ) *
        (∑ h, q h j * Bp m j h - ∑ h, q' h j * Bp m j h)))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, P y j * ((1 - δ) * ‖q - q'‖) := sum_le_sum fun j _ => by
        have hD0 : 0 ≤ 1 - Dp m j := by linarith [hA.D_le_one m j]
        have hD1 : 1 - Dp m j ≤ 1 := by linarith [hA.D_nonneg m j]
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hA.markov.nonneg y j), abs_of_nonneg hD0,
          abs_of_nonneg hδ']
        refine mul_le_mul_of_nonneg_left ?_ (hA.markov.nonneg y j)
        calc (1 - Dp m j) * ((1 - δ) * |∑ h, q h j * Bp m j h - ∑ h, q' h j * Bp m j h|)
            ≤ 1 * ((1 - δ) * ‖q - q'‖) := mul_le_mul hD1
              (mul_le_mul_of_nonneg_left (hinner j) hδ')
              (mul_nonneg hδ' (abs_nonneg _)) zero_le_one
          _ = (1 - δ) * ‖q - q'‖ := one_mul _
    _ = (1 - δ) * ‖q - q'‖ := by rw [← sum_mul, hA.markov.rowsum, one_mul]

/-- AKMM, (24.12), (24.A.2), (24.A.6): the price operator is a contraction of modulus
`(1 − δ)/(1 + r) < 1` in the sup norm. -/
theorem bp_contracting {P : Matrix Y Y ℝ} {r δ : ℝ} {Dp : Bd → Y → ℝ} {Bp : Bd → Y → Bd → ℝ}
    (hA : BPAdmissible P r δ Dp Bp) :
    ContractingWith (Real.toNNReal ((1 - δ) / (1 + r))) (bp_op P r δ Dp Bp) := by
  have hr1 : 0 < 1 + r := by linarith [hA.r_gt]
  have hk0 : 0 ≤ (1 - δ) / (1 + r) := div_nonneg (by linarith [hA.δ_le_one]) hr1.le
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun q q' => ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hk0, NNReal.coe_one, div_lt_one hr1]
    linarith [hA.δr_pos]
  · rw [Real.coe_toNNReal _ hk0, dist_eq_norm, dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hk0 (norm_nonneg _))).2 fun m => ?_
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hk0 (norm_nonneg _))).2 fun y => ?_
    rw [Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs]
    exact bp_op_sub_le hA q q' m y

/-- The set of prices in `[0, δ/(δ + r)]` is mapped into itself. -/
theorem bp_op_mapsTo {P : Matrix Y Y ℝ} {r δ : ℝ} {Dp : Bd → Y → ℝ} {Bp : Bd → Y → Bd → ℝ}
    (hA : BPAdmissible P r δ Dp Bp) (q : Bd → Y → ℝ)
    (hq : ∀ m y, 0 ≤ q m y ∧ q m y ≤ δ / (δ + r)) (m : Bd) (y : Y) :
    0 ≤ bp_op P r δ Dp Bp q m y ∧ bp_op P r δ Dp Bp q m y ≤ δ / (δ + r) := by
  have hr1 : 0 < 1 + r := by linarith [hA.r_gt]
  have hδ' : 0 ≤ 1 - δ := by linarith [hA.δ_le_one]
  have hM : 0 ≤ δ / (δ + r) := div_nonneg hA.δ_nonneg hA.δr_pos.le
  have hin : ∀ j, 0 ≤ ∑ h, q h j * Bp m j h ∧ ∑ h, q h j * Bp m j h ≤ δ / (δ + r) := by
    intro j
    refine ⟨sum_nonneg fun h _ => mul_nonneg (hq h j).1 (hA.B_nonneg m j h), ?_⟩
    calc ∑ h, q h j * Bp m j h ≤ ∑ h, δ / (δ + r) * Bp m j h :=
          sum_le_sum fun h _ => mul_le_mul_of_nonneg_right (hq h j).2 (hA.B_nonneg m j h)
      _ = δ / (δ + r) := by rw [← mul_sum, hA.B_sum, mul_one]
  have hterm : ∀ j, 0 ≤ (1 - Dp m j) * (δ + (1 - δ) * ∑ h, q h j * Bp m j h) ∧
      (1 - Dp m j) * (δ + (1 - δ) * ∑ h, q h j * Bp m j h) ≤ δ + (1 - δ) * (δ / (δ + r)) := by
    intro j
    have hD0 : 0 ≤ 1 - Dp m j := by linarith [hA.D_le_one m j]
    have hD1 : 1 - Dp m j ≤ 1 := by linarith [hA.D_nonneg m j]
    have hX0 : 0 ≤ δ + (1 - δ) * ∑ h, q h j * Bp m j h :=
      add_nonneg hA.δ_nonneg (mul_nonneg hδ' (hin j).1)
    refine ⟨mul_nonneg hD0 hX0, ?_⟩
    calc (1 - Dp m j) * (δ + (1 - δ) * ∑ h, q h j * Bp m j h)
        ≤ 1 * (δ + (1 - δ) * ∑ h, q h j * Bp m j h) := mul_le_mul_of_nonneg_right hD1 hX0
      _ ≤ δ + (1 - δ) * (δ / (δ + r)) := by
          rw [one_mul]; linarith [mul_le_mul_of_nonneg_left (hin j).2 hδ']
  unfold bp_op
  refine ⟨mul_nonneg (inv_nonneg.2 hr1.le)
    (sum_nonneg fun j _ => mul_nonneg (hA.markov.nonneg y j) (hterm j).1), ?_⟩
  calc (1 + r)⁻¹ * ∑ j, P y j * ((1 - Dp m j) * (δ + (1 - δ) * ∑ h, q h j * Bp m j h))
      ≤ (1 + r)⁻¹ * ∑ j, P y j * (δ + (1 - δ) * (δ / (δ + r))) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hterm j).2 (hA.markov.nonneg y j)) (inv_nonneg.2 hr1.le)
    _ = δ / (δ + r) := by
        rw [← sum_mul, hA.markov.rowsum, one_mul]
        have : δ + r ≠ 0 := hA.δr_pos.ne'
        field_simp
        ring

/-- **AKMM, (24.A.6)**, p. 900: with default probabilities and borrowing probabilities, the
equilibrium bond price exists and is unique, and lies in `[0, δ/(δ + r)]`. -/
theorem eq_24_A_6 {P : Matrix Y Y ℝ} {r δ : ℝ} {Dp : Bd → Y → ℝ} {Bp : Bd → Y → Bd → ℝ}
    (hA : BPAdmissible P r δ Dp Bp) :
    ∃! q : Bd → Y → ℝ, Function.IsFixedPt (bp_op P r δ Dp Bp) q ∧
      ∀ m y, 0 ≤ q m y ∧ q m y ≤ δ / (δ + r) := by
  have hc := bp_contracting hA
  set S : Set (Bd → Y → ℝ) :=
    ⋂ m, ⋂ y, {q | 0 ≤ q m y ∧ q m y ≤ δ / (δ + r)} with hSdef
  have hSm : ∀ q, q ∈ S ↔ ∀ m y, 0 ≤ q m y ∧ q m y ≤ δ / (δ + r) := fun q => by
    simp only [hSdef, Set.mem_iInter, Set.mem_ofPred_eq]
  have hS : IsClosed S := by
    refine isClosed_iInter fun m => isClosed_iInter fun y => ?_
    have hc : Continuous fun q : Bd → Y → ℝ => q m y := by fun_prop
    exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  have h0 : (fun _ _ => (0 : ℝ)) ∈ S := (hSm _).2 fun _ _ =>
    ⟨le_rfl, div_nonneg hA.δ_nonneg hA.δr_pos.le⟩
  have hit : ∀ n, (bp_op P r δ Dp Bp)^[n] (fun _ _ => 0) ∈ S := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (hSm _).2 fun m y => bp_op_mapsTo hA _ ((hSm _).1 ih) m y
  have hmem := hS.mem_of_tendsto (hc.tendsto_iterate_fixedPoint (fun _ _ => 0))
    (Filter.Eventually.of_forall hit)
  exact ⟨_, ⟨hc.fixedPoint_isFixedPt, (hSm _).1 hmem⟩, fun q hq => hc.fixedPoint_unique hq.1⟩

/-- **AKMM, (24.A.2)**, pp. 897–898: the price iteration `q_{I+1} = T q_I` converges from any
initial guess to the unique equilibrium price (for fixed default and borrowing rules). -/
theorem eq_24_A_2 {P : Matrix Y Y ℝ} {r δ : ℝ} {Dp : Bd → Y → ℝ} {Bp : Bd → Y → Bd → ℝ}
    (hA : BPAdmissible P r δ Dp Bp) (q₀ q : Bd → Y → ℝ)
    (hq : Function.IsFixedPt (bp_op P r δ Dp Bp) q) :
    Filter.Tendsto (fun n => (bp_op P r δ Dp Bp)^[n] q₀) Filter.atTop (nhds q) := by
  have hc := bp_contracting hA
  rw [hc.fixedPoint_unique hq]
  exact hc.tendsto_iterate_fixedPoint q₀

/-- AKMM, (24.12), p. 744: the price operator with deterministic rules `D̂` and `B̂`. -/
noncomputable def bp_op12 (P : Matrix Y Y ℝ) (r δ : ℝ) (D : Bd → Y → ℝ) (Bh : Bd → Y → Bd)
    (q : Bd → Y → ℝ) : Bd → Y → ℝ :=
  fun m y => (1 + r)⁻¹ * ∑ j, P y j * ((1 - D m j) * (δ + (1 - δ) * q (Bh m j) j))

/-- Deterministic rules are degenerate probabilities: (24.12) is (24.A.6) with
`B(h | m, j) = 1{h = B̂(m, j)}`. -/
theorem bp_op12_eq [DecidableEq Bd] (P : Matrix Y Y ℝ) (r δ : ℝ) (D : Bd → Y → ℝ)
    (Bh : Bd → Y → Bd) :
    bp_op12 P r δ D Bh = bp_op P r δ D (fun m j h => if Bh m j = h then 1 else 0) := by
  funext q m y
  unfold bp_op12 bp_op
  congr 1
  refine sum_congr rfl fun j _ => ?_
  simp [mul_ite, mul_one, mul_zero, sum_ite_eq]

omit [Fintype Bd] in
/-- **AKMM, (24.12)**, p. 744: given a default rule `D̂ ∈ {0, 1}` and a borrowing rule `B̂`, the
bond price function exists, is unique and lies in `[0, δ/(δ + r)]` (with `P` Markov,
`δ ∈ [0, 1]`, `r > −1`, `δ + r > 0`). -/
theorem eq_24_12 [Finite Bd] {P : Matrix Y Y ℝ} (hP : IsMarkov P) {r δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : -1 < r) (hδr : 0 < δ + r) (D : Bd → Y → ℝ)
    (hD : ∀ m j, D m j = 0 ∨ D m j = 1) (Bh : Bd → Y → Bd) :
    ∃! q : Bd → Y → ℝ, (∀ m y, q m y =
        (1 + r)⁻¹ * ∑ j, P y j * ((1 - D m j) * (δ + (1 - δ) * q (Bh m j) j))) ∧
      ∀ m y, 0 ≤ q m y ∧ q m y ≤ δ / (δ + r) := by
  classical
  let _ := Fintype.ofFinite Bd
  have hA : BPAdmissible P r δ D (fun m j h => if Bh m j = h then 1 else 0) :=
    { markov := hP
      D_nonneg := fun m j => by rcases hD m j with h | h <;> simp [h]
      D_le_one := fun m j => by rcases hD m j with h | h <;> simp [h]
      B_nonneg := fun _ _ _ => by split_ifs <;> norm_num
      B_sum := fun m j => by simp
      δ_nonneg := hδ0
      δ_le_one := hδ1
      r_gt := hr
      δr_pos := hδr }
  have he := eq_24_A_6 hA
  rw [← bp_op12_eq] at he
  have hiff : ∀ q : Bd → Y → ℝ, Function.IsFixedPt (bp_op12 P r δ D Bh) q ↔ ∀ m y, q m y =
      (1 + r)⁻¹ * ∑ j, P y j * ((1 - D m j) * (δ + (1 - δ) * q (Bh m j) j)) := fun q => by
    constructor
    · intro h m y
      exact (congrFun (congrFun h m) y).symm
    · intro h
      funext m y
      exact (h m y).symm
  simpa only [hiff] using he

/-- AKMM, p. 903: without default the bond sells at the risk-free price `δ/(δ + r)`. -/
theorem bp_riskfree {P : Matrix Y Y ℝ} (hP : IsMarkov P) {r : ℝ} (δ : ℝ) (hr : -1 < r)
    (hδr : 0 < δ + r) (Bp : Bd → Y → Bd → ℝ) (hBs : ∀ m j, ∑ h, Bp m j h = 1) :
    Function.IsFixedPt (bp_op P r δ (fun _ _ => 0) Bp) (fun _ _ => δ / (δ + r)) := by
  funext m y
  unfold bp_op
  have hr1 : 1 + r ≠ 0 := by linarith
  have hδr' : δ + r ≠ 0 := hδr.ne'
  simp only [sub_zero, one_mul, ← mul_sum, hBs, mul_one, ← sum_mul, hP.rowsum, one_mul]
  field_simp
  ring

omit [Fintype Bd] in
/-- **AKMM, p. 748: one-period debt.** With `δ = 1` the price operator does not depend on the
continuation price or the borrowing rule: `(Tq)(m, y) = (1 + r)⁻¹ Σ_j P(y, j)[1 − D̂(m, j)]`;
the period-`t` price depends only on the period-`t+1` default rule. -/
theorem bp_one_period (P : Matrix Y Y ℝ) (r : ℝ) (D : Bd → Y → ℝ) (Bh : Bd → Y → Bd)
    (q : Bd → Y → ℝ) (m : Bd) (y : Y) :
    bp_op12 P r 1 D Bh q m y = (1 + r)⁻¹ * ∑ j, P y j * (1 - D m j) := by
  unfold bp_op12
  simp only [sub_self, zero_mul, add_zero, mul_one]

omit [Fintype Bd] in
/-- AKMM, p. 748: with one-period debt two borrowing rules lead to the same equilibrium
price: the second time-inconsistency problem does not arise. -/
theorem bp_one_period_independent (P : Matrix Y Y ℝ) (r : ℝ) (D : Bd → Y → ℝ)
    (Bh Bh' : Bd → Y → Bd) (q q' : Bd → Y → ℝ)
    (hq : Function.IsFixedPt (bp_op12 P r 1 D Bh) q)
    (hq' : Function.IsFixedPt (bp_op12 P r 1 D Bh') q') : q = q' := by
  funext m y
  rw [← hq, ← hq']
  simp only [bp_one_period]

/-- AKMM, p. 748: **with long-term debt the next government's borrowing changes today's
price.** One income state, two debt levels (`false` low, `true` high); the sovereign repays at
low debt and defaults at high debt. If the next government stays at low debt the low-debt bond
sells at the risk-free `δ/(δ + r)`; if it moves to high debt (and then defaults) it sells at
`δ/(1 + r)`, which is strictly lower for `0 < δ < 1`. -/
theorem bp_long_term_depends_on_borrowing {r δ : ℝ} (hr : 0 ≤ r) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let P : Matrix Unit Unit ℝ := fun _ _ => 1
    let D : Bool → Unit → ℝ := fun b _ => if b then 1 else 0
    Function.IsFixedPt (bp_op12 P r δ D (fun _ _ => false))
        (fun b _ => if b then 0 else δ / (δ + r)) ∧
      Function.IsFixedPt (bp_op12 P r δ D (fun _ _ => true))
        (fun b _ => if b then 0 else δ / (1 + r)) ∧
      δ / (1 + r) < δ / (δ + r) := by
  intro P D
  have hr1 : 0 < 1 + r := by linarith
  have hδr : 0 < δ + r := by linarith
  refine ⟨?_, ?_, div_lt_div_of_pos_left hδ0 hδr (by linarith)⟩
  · funext b u
    cases b <;> simp only [bp_op12, P, D, Finset.univ_unique, Finset.sum_singleton, one_mul,
      Bool.false_eq_true, ↓reduceIte, sub_zero, sub_self, zero_mul, mul_zero]
    field_simp
    ring
  · funext b u
    cases b <;> simp only [bp_op12, P, D, Finset.univ_unique, Finset.sum_singleton, one_mul,
      Bool.false_eq_true, ↓reduceIte, sub_zero, sub_self, zero_mul, mul_zero, add_zero]
    field_simp

end AKMM.SovereignDefault
