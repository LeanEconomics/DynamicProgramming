/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.DGPublicMonitoring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Example 21.1.2: the noisy prisoner's dilemma

Miao, Example 21.1.2, pp. 751–753. Two players, actions `C` (`true`) and `D` (`false`); public
signal `G` (`true`) or `B` (`false`) with `Pr(G | a) = p, q, r` when two, one, none of the players
cooperate. The realised rewards `r_i(a_i, y)` of the text give the ex ante payoffs of the
prisoner's dilemma of Example 21.1.1 (`example_21_1_2_payoffs`).

The text's claim that `W = {(v, v), (v', v')}`, `v = δr/(1 − δ(p − r))`,
`v' = (1 − δ + δr)/(1 − δ(p − r))`, is self-generating when `1/(p − r) ≥ δ ≥ 1/(p + q − 2r)` is
misprinted. Its own proof shows that the four displayed conditions hold iff
`1/(p − q + p − r) ≤ δ ≤ 1/(p − r + q − r)` (`example_21_1_2_DD_ic_iff`,
`example_21_1_2_CC_ic_iff`), and `W` is self-generating on that interval (`example_21_1_2`),
hence consists of PPE payoffs (`example_21_1_2_ppe`). With `p = 9/10`, `q = 2/5`, `r = 1/10`,
`δ = 19/20` the printed hypotheses hold but `W` is not self-generating
(`example_21_1_2_printed_false`). The assumption `p − q > q − r` is exactly what makes the
corrected interval nonempty (`example_21_1_2_interval`).
-/

namespace Miao.DynamicGames

/-- `Pr(G | a)` in Example 21.1.2: `p` if both cooperate, `q` if one does, `r` if neither. -/
def dg_pdProbG (p q r : ℝ) (a : Fin 2 → Bool) : ℝ :=
  if a 0 && a 1 then p else if a 0 || a 1 then q else r

/-- The signal law `f(y | a)` of Example 21.1.2. -/
def dg_pdF (p q r : ℝ) (a : Fin 2 → Bool) (y : Bool) : ℝ :=
  if y then dg_pdProbG p q r a else 1 - dg_pdProbG p q r a

/-- The realised rewards `r_i(a_i, y)` of Example 21.1.2 (Miao, p. 751). -/
noncomputable def dg_pdR (p q r : ℝ) (ai y : Bool) : ℝ :=
  if ai then (if y then 1 + (2 - 2 * p) / (p - q) else 1 - 2 * p / (p - q))
  else (if y then (2 - 2 * r) / (q - r) else -2 * r / (q - r))

/-- A bound on the rewards of Example 21.1.2. -/
noncomputable def dg_pdM (p q r : ℝ) : ℝ :=
  |1 + (2 - 2 * p) / (p - q)| + |1 - 2 * p / (p - q)| + |(2 - 2 * r) / (q - r)| +
    |-2 * r / (q - r)|

/-- `Pr(G | a) ∈ [0, 1]` when `0 ≤ r < q < p ≤ 1`. -/
theorem dg_pdProbG_mem {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    (a : Fin 2 → Bool) : 0 ≤ dg_pdProbG p q r a ∧ dg_pdProbG p q r a ≤ 1 := by
  unfold dg_pdProbG
  split_ifs <;> constructor <;> linarith

/-- The noisy prisoner's dilemma as a repeated game with imperfect public monitoring. -/
noncomputable def dg_noisyPD (p q r : ℝ) (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p)
    (hp : p ≤ 1) : DGPublicGame (Fin 2) (fun _ => Bool) Bool where
  f := dg_pdF p q r
  f_nonneg a y := by
    have := dg_pdProbG_mem hr hrq hqp hp a
    unfold dg_pdF
    split_ifs <;> linarith
  f_sum a := by simp only [Fintype.sum_bool, dg_pdF, ↓reduceIte, Bool.false_eq_true]; ring
  r _ := dg_pdR p q r
  M := dg_pdM p q r
  r_bound _ ai y := by
    unfold dg_pdR dg_pdM
    have h1 := abs_nonneg (1 + (2 - 2 * p) / (p - q))
    have h2 := abs_nonneg (1 - 2 * p / (p - q))
    have h3 := abs_nonneg ((2 - 2 * r) / (q - r))
    have h4 := abs_nonneg (-2 * r / (q - r))
    cases ai <;> cases y <;> simp only [↓reduceIte, Bool.false_eq_true] <;> linarith

/-- The ex ante payoff of player `i` in Example 21.1.2, as a function of `Pr(G | a)`:
`1 + (2 Pr(G|a) − 2p)/(p − q)` if `i` cooperates, `(2 Pr(G|a) − 2r)/(q − r)` if `i` defects. -/
theorem dg_noisyPD_u {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    (i : Fin 2) (a : Fin 2 → Bool) :
    dg_u (dg_noisyPD p q r hr hrq hqp hp) i a =
      if a i then 1 + (2 * dg_pdProbG p q r a - 2 * p) / (p - q)
      else (2 * dg_pdProbG p q r a - 2 * r) / (q - r) := by
  have hpq : p - q ≠ 0 := by linarith
  have hqr : q - r ≠ 0 := by linarith
  simp only [dg_u, dg_noisyPD, Fintype.sum_bool, dg_pdF, dg_pdR, ↓reduceIte,
    Bool.false_eq_true]
  cases a i <;> simp only [↓reduceIte, Bool.false_eq_true] <;> field_simp <;> ring

/-- The prisoner's dilemma matrix of Example 21.1.1: own action, other's action. -/
def dg_pdMatrix (ai aj : Bool) : ℝ :=
  if ai then (if aj then 1 else -1) else (if aj then 2 else 0)

/-- **Example 21.1.2** (Miao, p. 752): the ex ante payoffs `u_i(a) = ∑_y f(y|a) r_i(a_i, y)` are
those of the prisoner's dilemma of Example 21.1.1. -/
theorem example_21_1_2_payoffs {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p)
    (hp : p ≤ 1) (a : Fin 2 → Bool) :
    dg_u (dg_noisyPD p q r hr hrq hqp hp) 0 a = dg_pdMatrix (a 0) (a 1) ∧
      dg_u (dg_noisyPD p q r hr hrq hqp hp) 1 a = dg_pdMatrix (a 1) (a 0) := by
  have hpq : p - q ≠ 0 := by linarith
  have hqr : q - r ≠ 0 := by linarith
  rw [dg_noisyPD_u, dg_noisyPD_u]
  unfold dg_pdProbG dg_pdMatrix
  cases a 0 <;> cases a 1 <;>
    simp only [↓reduceIte, Bool.false_eq_true, Bool.and_self, Bool.or_self, Bool.and_false,
      Bool.and_true, Bool.or_false, Bool.or_true] <;>
    constructor <;> field_simp <;> ring

/-- The ex ante payoffs of Example 21.1.2 as the prisoner's dilemma matrix, for either player. -/
theorem dg_noisyPD_u_matrix {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    (i : Fin 2) (a : Fin 2 → Bool) :
    dg_u (dg_noisyPD p q r hr hrq hqp hp) i a =
      dg_pdMatrix (a i) (if i = 0 then a 1 else a 0) := by
  have h := example_21_1_2_payoffs hr hrq hqp hp a
  fin_cases i
  · exact h.1
  · exact h.2

/-- The bad continuation payoff `v = δr/(1 − δ(p − r))` of Example 21.1.2. -/
noncomputable def dg_pdV (p r δ : ℝ) : ℝ := δ * r / (1 - δ * (p - r))

/-- The good continuation payoff `v' = (1 − δ + δr)/(1 − δ(p − r))` of Example 21.1.2. -/
noncomputable def dg_pdV' (p r δ : ℝ) : ℝ := (1 - δ + δ * r) / (1 - δ * (p - r))

/-- The candidate set `W = {(v, v), (v', v')}` of Example 21.1.2. -/
noncomputable def dg_pdW (p r δ : ℝ) : Set (Fin 2 → ℝ) :=
  {fun _ => dg_pdV p r δ, fun _ => dg_pdV' p r δ}

/-- **Example 21.1.2** (Miao, p. 752): the promise-keeping equation for `v` under `(D, D)`,
`v = (1 − δ)·0 + δ((1 − r)v + rv')`. -/
theorem example_21_1_2_DD_eq {p r δ : ℝ} (hD : 1 - δ * (p - r) ≠ 0) :
    dg_pdV p r δ = (1 - δ) * 0 + δ * ((1 - r) * dg_pdV p r δ + r * dg_pdV' p r δ) := by
  unfold dg_pdV dg_pdV'
  field_simp
  ring

/-- **Example 21.1.2** (Miao, p. 752): the promise-keeping equation for `v'` under `(C, C)`,
`v' = (1 − δ)·1 + δ((1 − p)v + pv')`. -/
theorem example_21_1_2_CC_eq {p r δ : ℝ} (hD : 1 - δ * (p - r) ≠ 0) :
    dg_pdV' p r δ = (1 - δ) * 1 + δ * ((1 - p) * dg_pdV p r δ + p * dg_pdV' p r δ) := by
  unfold dg_pdV dg_pdV'
  field_simp
  ring

/-- **Example 21.1.2** (Miao, p. 752): the incentive constraint for `(D, D)`,
`v ≥ (1 − δ)(−1) + δ((1 − q)v + qv')`, holds iff `δ ≤ 1/(p − r + q − r)`. -/
theorem example_21_1_2_DD_ic_iff {p q r δ : ℝ} (hrq : r < q) (hqp : q < p) (hδ1 : δ < 1)
    (hD : 0 < 1 - δ * (p - r)) :
    (1 - δ) * (-1) + δ * ((1 - q) * dg_pdV p r δ + q * dg_pdV' p r δ) ≤ dg_pdV p r δ ↔
      δ ≤ 1 / (p - r + q - r) := by
  have key : dg_pdV p r δ - ((1 - δ) * (-1) + δ * ((1 - q) * dg_pdV p r δ + q * dg_pdV' p r δ))
      = (1 - δ) / (1 - δ * (p - r)) * (1 - δ * (p - r + q - r)) := by
    unfold dg_pdV dg_pdV'
    field_simp
    ring
  have hc : 0 < (1 - δ) / (1 - δ * (p - r)) := div_pos (by linarith) hD
  rw [le_div_iff₀ (by linarith), ← sub_nonneg, key]
  rw [mul_nonneg_iff_of_pos_left hc]
  constructor <;> intro h <;> linarith

/-- **Example 21.1.2** (Miao, pp. 752–753): the incentive constraint for `(C, C)`,
`v' ≥ (1 − δ)·2 + δ((1 − q)v + qv')`, holds iff `δ ≥ 1/(p − q + p − r)`. -/
theorem example_21_1_2_CC_ic_iff {p q r δ : ℝ} (hrq : r < q) (hqp : q < p) (hδ1 : δ < 1)
    (hD : 0 < 1 - δ * (p - r)) :
    (1 - δ) * 2 + δ * ((1 - q) * dg_pdV p r δ + q * dg_pdV' p r δ) ≤ dg_pdV' p r δ ↔
      1 / (p - q + p - r) ≤ δ := by
  have key : dg_pdV' p r δ - ((1 - δ) * 2 + δ * ((1 - q) * dg_pdV p r δ + q * dg_pdV' p r δ))
      = (1 - δ) / (1 - δ * (p - r)) * (δ * (p - q + p - r) - 1) := by
    unfold dg_pdV dg_pdV'
    field_simp
    ring
  have hc : 0 < (1 - δ) / (1 - δ * (p - r)) := div_pos (by linarith) hD
  rw [div_le_iff₀ (by linarith), ← sub_nonneg, key]
  rw [mul_nonneg_iff_of_pos_left hc]
  constructor <;> intro h <;> linarith

/-- Example 21.1.2 (Miao, p. 751): the assumption `p − q > q − r` is what makes the corrected
interval `[1/(p − q + p − r), 1/(p − r + q − r)]` nonempty. -/
theorem example_21_1_2_interval {p q r : ℝ} (hrq : r < q) (hqp : q < p) :
    1 / (p - q + p - r) < 1 / (p - r + q - r) ↔ q - r < p - q := by
  rw [one_div_lt_one_div (by linarith) (by linarith)]
  constructor <;> intro h <;> linarith

/-- The generated payoff in the noisy prisoner's dilemma: with `Pr(G | a) = P`,
`(1 − δ) u_i(a) + δ(P w_i(G) + (1 − P) w_i(B))`. -/
theorem dg_noisyPD_gen {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    (δ : ℝ) (a : Fin 2 → Bool) (w : Bool → Fin 2 → ℝ) (i : Fin 2) :
    dg_gen (dg_noisyPD p q r hr hrq hqp hp) δ a w i =
      (1 - δ) * dg_u (dg_noisyPD p q r hr hrq hqp hp) i a +
        δ * (dg_pdProbG p q r a * w true i + (1 - dg_pdProbG p q r a) * w false i) := by
  simp only [dg_gen, Fintype.sum_bool]
  rfl

/-- **Example 21.1.2** (Miao, pp. 751–753), corrected. If
`1/(p − q + p − r) ≤ δ ≤ 1/(p − r + q − r)` and `δ < 1`, the set
`W = {(v, v), (v', v')}` is self-generating: `(v, v)` is enforced by `(D, D)` and `(v', v')` by
`(C, C)`, both with `w(G) = (v', v')`, `w(B) = (v, v)`. -/
theorem example_21_1_2 {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    {δ : ℝ} (hδ1 : δ < 1) (hlo : 1 / (p - q + p - r) ≤ δ)
    (hhi : δ ≤ 1 / (p - r + q - r)) :
    dg_pdW p r δ ⊆ dg_B (dg_noisyPD p q r hr hrq hqp hp) δ (dg_pdW p r δ) := by
  have hD : 0 < 1 - δ * (p - r) := by nlinarith
  have hpq : p - q ≠ 0 := by linarith
  have hqr : q - r ≠ 0 := by linarith
  let w : Bool → Fin 2 → ℝ := fun y =>
    if y then (fun _ => dg_pdV' p r δ) else (fun _ => dg_pdV p r δ)
  have hw : ∀ y, w y ∈ dg_pdW p r δ := by
    intro y; cases y
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hDDic := (example_21_1_2_DD_ic_iff hrq hqp hδ1 hD).mpr hhi
  have hCCic := (example_21_1_2_CC_ic_iff hrq hqp hδ1 hD).mpr hlo
  have hDDeq := example_21_1_2_DD_eq (p := p) (r := r) hD.ne'
  have hCCeq := example_21_1_2_CC_eq (p := p) (r := r) hD.ne'
  rintro x (rfl | rfl)
  · refine ⟨fun _ => false, w, ⟨hw, ?_⟩, ?_⟩
    · intro i b
      cases b
      · rw [Function.update_eq_self]
      · rw [dg_noisyPD_gen, dg_noisyPD_gen, dg_noisyPD_u_matrix, dg_noisyPD_u_matrix]
        fin_cases i <;> simp [dg_pdMatrix, dg_pdProbG, Function.update, w] <;> linarith
    · funext i
      rw [dg_noisyPD_gen, dg_noisyPD_u_matrix]
      simp only [dg_pdMatrix, dg_pdProbG, w, Bool.and_self, Bool.or_self, Bool.false_eq_true,
        ↓reduceIte, ite_self]
      linarith
  · refine ⟨fun _ => true, w, ⟨hw, ?_⟩, ?_⟩
    · intro i b
      cases b
      · rw [dg_noisyPD_gen, dg_noisyPD_gen, dg_noisyPD_u_matrix, dg_noisyPD_u_matrix]
        fin_cases i <;> simp [dg_pdMatrix, dg_pdProbG, Function.update, w] <;> linarith
      · rw [Function.update_eq_self]
    · funext i
      rw [dg_noisyPD_gen, dg_noisyPD_u_matrix]
      simp only [dg_pdMatrix, dg_pdProbG, w, Bool.and_self, Bool.false_eq_true, ↓reduceIte,
        ite_self]
      linarith

/-- **Example 21.1.2** (Miao, p. 752), with Lemma 21.1.2 for PPE: on the corrected interval the
payoffs `(v, v)` and `(v', v')` are PPE payoffs. -/
theorem example_21_1_2_ppe {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    {δ : ℝ} (hδ1 : δ < 1) (hlo : 1 / (p - q + p - r) ≤ δ)
    (hhi : δ ≤ 1 / (p - r + q - r)) :
    dg_pdW p r δ ⊆ dg_PPEPayoffs (dg_noisyPD p q r hr hrq hqp hp) δ := by
  have hfin : (dg_pdW p r δ).Finite := (Set.finite_singleton _).insert _
  have hδ0 : 0 ≤ δ := le_trans (one_div_pos.mpr (by linarith)).le hlo
  exact dg_selfGenerating_subset_ppe _ hδ0 hδ1 hfin.isBounded
    (example_21_1_2 hr hrq hqp hp hδ1 hlo hhi)

/-- The corrected Example 21.1.2 is not vacuous: `p = 9/10`, `q = 2/5`, `r = 1/10`, `δ = 4/5`
satisfy its hypotheses (with full support and `p − q > q − r`), so `(v, v) = (2/9, 2/9)` and
`(v', v') = (7/9, 7/9)` are PPE payoffs. -/
theorem example_21_1_2_instance :
    ∃ (hr : (0 : ℝ) ≤ 1 / 10) (hrq : (1 / 10 : ℝ) < 2 / 5) (hqp : (2 / 5 : ℝ) < 9 / 10)
      (hp : (9 / 10 : ℝ) ≤ 1),
      dg_pdW (9 / 10) (1 / 10) (4 / 5) ⊆
        dg_PPEPayoffs (dg_noisyPD (9 / 10) (2 / 5) (1 / 10) hr hrq hqp hp) (4 / 5) ∧
      dg_pdV (9 / 10) (1 / 10) (4 / 5) = 2 / 9 ∧ dg_pdV' (9 / 10) (1 / 10) (4 / 5) = 7 / 9 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · exact example_21_1_2_ppe _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
  · unfold dg_pdV; norm_num
  · unfold dg_pdV'; norm_num

/-- **Example 21.1.2** (Miao, p. 752): the printed claim is false. For `p = 9/10`, `q = 2/5`,
`r = 1/10` (so `p − q > q − r`) and `δ = 19/20`, the printed hypotheses
`1/(p − r) ≥ δ ≥ 1/(p + q − 2r)` hold, but `W = {(v, v), (v', v')}` is not self-generating:
`(v, v)` is not in `B(W)`. -/
theorem example_21_1_2_printed_false :
    ∃ (hr : (0 : ℝ) ≤ 1 / 10) (hrq : (1 / 10 : ℝ) < 2 / 5) (hqp : (2 / 5 : ℝ) < 9 / 10)
      (hp : (9 / 10 : ℝ) ≤ 1),
      (2 / 5 : ℝ) - 1 / 10 < 9 / 10 - 2 / 5 ∧
      (19 / 20 : ℝ) ≤ 1 / (9 / 10 - 1 / 10) ∧ 1 / (9 / 10 + 2 / 5 - 2 * (1 / 10)) ≤ (19 / 20 : ℝ) ∧
      ¬ dg_pdW (9 / 10) (1 / 10) (19 / 20) ⊆
        dg_B (dg_noisyPD (9 / 10) (2 / 5) (1 / 10) hr hrq hqp hp) (19 / 20)
          (dg_pdW (9 / 10) (1 / 10) (19 / 20)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_⟩
  intro hsub
  have hV : dg_pdV (9 / 10) (1 / 10) (19 / 20) = 19 / 48 := by unfold dg_pdV; norm_num
  have hV' : dg_pdV' (9 / 10) (1 / 10) (19 / 20) = 29 / 48 := by unfold dg_pdV'; norm_num
  obtain ⟨a, w, ⟨hw, hic⟩, he⟩ := hsub (Or.inl rfl)
  have e0 := congrFun he 0
  have e1 := congrFun he 1
  rw [dg_noisyPD_gen, dg_noisyPD_u] at e0 e1
  have ic0 := hic 0 true
  rw [dg_noisyPD_gen, dg_noisyPD_gen, dg_noisyPD_u, dg_noisyPD_u] at ic0
  have hw' : ∀ y, w y = (fun _ => (19 / 48 : ℝ)) ∨ w y = (fun _ => (29 / 48 : ℝ)) := by
    intro y
    rcases hw y with h | h
    · left; rw [h, hV]
    · right; rw [Set.mem_singleton_iff.mp h, hV']
  rcases hw' true with ht | ht <;> rcases hw' false with hf | hf <;>
    simp only [ht, hf, hV] at e0 e1 ic0 <;>
    cases h0 : a 0 <;> cases h1 : a 1 <;>
    simp [dg_pdProbG, Function.update, h0, h1] at e0 e1 ic0 <;>
    linarith

end Miao.DynamicGames
