/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.RDCounter
import Mathlib.Analysis.PSeries

/-!
# Example 13.5.1 (Magill and Quinzii)

Miao, Example 13.5.1, pp. 436–437. A deterministic economy (`S = Unit`, one node per date; the
date-`t` node is `List.replicate t ()`) with two agents (`true` = agent 1, `false` = agent 2):
`U¹(c) = c₀`, `U²(c) = ∑_{t≥1} (2/t²) √cₜ`, `y¹ = (0, 1, 1, …)`, `y² = (ζ, 0, 0, …)` with
`ζ = ∑_{t≥1} 1/t²`.

* `example_13_5_1_AD`: the Arrow–Debreu equilibrium `c¹* = y²`, `c²* = y¹`, `π₀ = 1`,
  `π_t = 1/t²`.
* `example_13_5_1_prices`: with a one-period bond the prices are `p₀ = 1`,
  `p_t = t²/(t + 1)²`.
* `example_13_5_1_CETVC`: the allocation, the strategy `θ¹_t = −(t + 1)² ∑_{n>t} 1/n²`
  (`θ² = −θ¹`), `π` and `p` form a competitive equilibrium with transversality condition.
* `example_13_5_1_TVC`: `π_T p_T θ¹_T = −∑_{n>T} 1/n² → 0`.
* `example_13_5_1_unlimited`: `p_T θ¹_T = −∑_{s≥1} T²/(T + s)² → −∞`, so the equilibrium is not
  a Radner equilibrium with any bounded borrowing limits (`example_13_5_1_not_Radner`).
* `example_13_5_1_patience`: `t²/(t + 1)²` increases with `t`, and the present value at `T` of
  agent 1's future endowment, `∑_{s≥1} π_{T+s}/π_T = ∑_{s≥1} T²/(T + s)²`, tends to infinity.
-/

namespace Miao.CompleteMarkets

open Filter Topology

/-- In a deterministic economy the date-`t` sum is the value at the unique date-`t` node. -/
theorem rd_dsum_unit (F : List Unit → ℝ) (t : ℕ) :
    rd_dsum F [] t = F (List.replicate t ()) := by
  rw [rd_dsum, Finset.sum_eq_single_of_mem (List.replicate t ())
    ((rd_mem_paths _ _).2 (List.length_replicate ..))]
  · simp
  · intro l hl hne
    rw [rd_mem_paths] at hl
    exact absurd (List.eq_replicate_iff.2 ⟨hl, fun b _ => rfl⟩) hne

/-- The tail sums `R(k) = ∑_{n ≥ k} 1/n²`. -/
noncomputable def rd_exR (k : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n + k : ℕ) : ℝ) ^ 2

/-- `ζ = ∑_{t ≥ 1} 1/t²`. -/
noncomputable def rd_exζ : ℝ := rd_exR 1

theorem rd_exR_summable (k : ℕ) : Summable fun n : ℕ => 1 / ((n + k : ℕ) : ℝ) ^ 2 :=
  (summable_nat_add_iff k).2 (Real.summable_one_div_nat_pow.2 one_lt_two)

theorem rd_exR_succ (k : ℕ) : rd_exR k = 1 / (k : ℝ) ^ 2 + rd_exR (k + 1) := by
  rw [rd_exR, (rd_exR_summable k).tsum_eq_zero_add, rd_exR]
  simp only [zero_add]
  congr 1
  exact tsum_congr fun n => by rw [show n + 1 + k = n + (k + 1) by ring]

theorem rd_exR_nonneg (k : ℕ) : 0 ≤ rd_exR k :=
  tsum_nonneg fun n => by positivity

theorem rd_exR_tendsto : Tendsto (fun T => rd_exR T) atTop (𝓝 0) :=
  tendsto_sum_nat_add fun n : ℕ => 1 / (n : ℝ) ^ 2

/-- `R(0) = R(1) = ζ` (the `n = 0` term `1/0²` is `0`). -/
theorem rd_exR_zero : rd_exR 0 = rd_exζ := by
  rw [rd_exR_succ 0]
  simp [rd_exζ]

/-- The Arrow–Debreu prices `q⁰₀ = 1`, `q⁰_t = 1/t²` by date. -/
noncomputable def rd_exqd (t : ℕ) : ℝ := if t = 0 then 1 else 1 / (t : ℝ) ^ 2

/-- The Arrow–Debreu prices as a process (`π = q⁰`, as `Pr ≡ 1`). -/
noncomputable def rd_exq (g : List Unit) : ℝ := rd_exqd g.length

theorem rd_exqd_pos (t : ℕ) : 0 < rd_exqd t := by
  unfold rd_exqd
  split_ifs with h
  · exact one_pos
  · have : (0 : ℝ) < t := Nat.cast_pos.2 (Nat.pos_of_ne_zero h)
    positivity

/-- The prices `q⁰_t` decrease. -/
theorem rd_exqd_succ_le (t : ℕ) : rd_exqd (t + 1) ≤ rd_exqd t := by
  unfold rd_exqd
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h
    norm_num
  · have h0 : (0 : ℝ) < t := Nat.cast_pos.2 h
    simp only [Nat.add_one_ne_zero, ↓reduceIte, h.ne', Nat.cast_add, Nat.cast_one]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- The utilities: `U¹(c) = c₀` and `U²(c) = ∑ₜ (2/t²) √cₜ`. -/
noncomputable def rd_exU (i : Bool) (c : List Unit → ℝ) : ℝ :=
  if i then c [] else ∑' t : ℕ, 2 / (t : ℝ) ^ 2 * rd_dsum (fun g => Real.sqrt (c g)) [] t

/-- The endowments `y¹ = (0, 1, 1, …)`, `y² = (ζ, 0, 0, …)`. -/
noncomputable def rd_exy (i : Bool) (g : List Unit) : ℝ :=
  if i then (if g.length = 0 then 0 else 1) else (if g.length = 0 then rd_exζ else 0)

/-- The equilibrium allocation `c¹* = y²`, `c²* = y¹`. -/
noncomputable def rd_exc (i : Bool) : List Unit → ℝ := rd_exy (!i)

theorem rd_exy_pos (i : Bool) : rd_LinfPos (rd_exy i) := by
  have hz : 0 ≤ rd_exζ := rd_exR_nonneg 1
  refine ⟨⟨1 + rd_exζ, fun g => ?_⟩, fun g => ?_⟩
  · cases i <;> simp only [rd_exy, Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;>
      simp [abs_of_nonneg hz] <;> linarith
  · cases i <;> simp only [rd_exy, Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;>
      simp [hz]

theorem rd_exq_L1 : rd_L1 rd_exq := by
  simp only [rd_L1, rd_dsum_unit, rd_exq, List.length_replicate]
  have e : (fun t => |rd_exqd t|) = fun t : ℕ => 1 / (t : ℝ) ^ 2 + if t = 0 then 1 else 0 := by
    funext t
    rw [abs_of_pos (rd_exqd_pos t), rd_exqd]
    split_ifs with h
    · simp [h]
    · simp
  rw [e]
  exact (Real.summable_one_div_nat_pow.2 one_lt_two).add (hasSum_ite_eq 0 1).summable

/-- The present value of a process under `q⁰`. -/
theorem rd_ex_pv (x : List Unit → ℝ) :
    ∑' t, rd_dsum (fun g => rd_exq g * x g) [] t =
      ∑' t, rd_exqd t * x (List.replicate t ()) := by
  simp [rd_dsum_unit, rd_exq]

theorem rd_ex_pv_y1 : ∑' t, rd_dsum (fun g => rd_exq g * rd_exy true g) [] t = rd_exζ := by
  rw [rd_ex_pv, ← rd_exR_zero, rd_exR]
  refine tsum_congr fun t => ?_
  simp only [rd_exy, ↓reduceIte, List.length_replicate, rd_exqd, add_zero]
  split_ifs with h <;> simp [h]

theorem rd_ex_pv_y2 : ∑' t, rd_dsum (fun g => rd_exq g * rd_exy false g) [] t = rd_exζ := by
  rw [rd_ex_pv]
  have : (fun t => rd_exqd t * rd_exy false (List.replicate t ())) =
      fun t => if t = 0 then rd_exζ else 0 := by
    funext t
    simp only [rd_exy, Bool.false_eq_true, ↓reduceIte, List.length_replicate, rd_exqd]
    split_ifs <;> simp
  rw [this, tsum_ite_eq]

/-- **Example 13.5.1** (Miao, p. 436): `c¹* = y²`, `c²* = y¹`, `π₀ = 1`, `π_t = 1/t²` is an
Arrow–Debreu equilibrium. -/
theorem example_13_5_1_AD : rd_ADEqm rd_exU rd_exy rd_exq rd_exc := by
  have hz : 0 ≤ rd_exζ := rd_exR_nonneg 1
  refine ⟨rd_exq_L1, fun i => ?_, fun h => ?_⟩
  · cases i with
    | true =>
      refine ⟨⟨rd_exy_pos false, ?_⟩, fun c' ⟨hc', hb⟩ => ?_⟩
      · rw [rd_ADBudget, rd_exc, Bool.not_true, rd_ex_pv_y2, rd_ex_pv_y1]
      · rw [rd_ADBudget, rd_ex_pv_y1] at hb
        simp only [rd_exU, ↓reduceIte, rd_exc, Bool.not_true, rd_exy, Bool.false_eq_true,
          List.length_nil]
        have hs := rd_L1_mul rd_exq_L1 hc'.1
        have := hs.le_tsum 0 fun t _ =>
          rd_dsum_nonneg (fun g => mul_nonneg (rd_exqd_pos _).le (hc'.2 g)) _ _
        simp only [rd_dsum_zero] at this
        have e0 : rd_exq [] * c' [] = c' [] := by simp [rd_exq, rd_exqd]
        linarith
    | false =>
      refine ⟨⟨rd_exy_pos true, ?_⟩, fun c' ⟨hc', hb⟩ => ?_⟩
      · rw [rd_ADBudget, rd_exc, Bool.not_false, rd_ex_pv_y1, rd_ex_pv_y2]
      · rw [rd_ADBudget, rd_ex_pv_y2, rd_ex_pv] at hb
        simp only [rd_exU, Bool.false_eq_true, ↓reduceIte, rd_exc, Bool.not_false, rd_dsum_unit]
        have hval : ∑' t : ℕ, 2 / (t : ℝ) ^ 2 * Real.sqrt (rd_exy true (List.replicate t ())) =
            2 * rd_exζ := by
          rw [← rd_exR_zero, rd_exR, ← tsum_mul_left]
          refine tsum_congr fun t => ?_
          simp only [rd_exy, ↓reduceIte, List.length_replicate, add_zero]
          split_ifs with h <;> simp [h, div_eq_mul_inv]
        rw [hval]
        obtain ⟨⟨M, hM⟩, h0⟩ := hc'
        have hsx : Summable fun t => rd_exqd t * c' (List.replicate t ()) := by
          have := rd_L1_mul rd_exq_L1 ⟨M, hM⟩
          simpa [rd_dsum_unit, rd_exq] using this
        have hs1 := Real.summable_one_div_nat_pow.2 one_lt_two
        have hle : ∀ t : ℕ, 2 / (t : ℝ) ^ 2 * Real.sqrt (c' (List.replicate t ())) ≤
            1 / (t : ℝ) ^ 2 + rd_exqd t * c' (List.replicate t ()) := by
          intro t
          set x := c' (List.replicate t ())
          have hx := h0 (List.replicate t ())
          have hsq : Real.sqrt x ≤ (1 + x) / 2 := by
            nlinarith [Real.sq_sqrt hx, sq_nonneg (Real.sqrt x - 1), Real.sqrt_nonneg x]
          have hq : x / (t : ℝ) ^ 2 ≤ rd_exqd t * x := by
            unfold rd_exqd
            split_ifs with h
            · simp only [h, Nat.cast_zero]
              simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
                one_mul]
              exact hx
            · rw [div_eq_mul_inv, mul_comm, one_div]
          calc 2 / (t : ℝ) ^ 2 * Real.sqrt x ≤ 2 / (t : ℝ) ^ 2 * ((1 + x) / 2) :=
                mul_le_mul_of_nonneg_left hsq (by positivity)
            _ = 1 / (t : ℝ) ^ 2 + x / (t : ℝ) ^ 2 := by ring
            _ ≤ _ := by linarith
        have hsum := Summable.tsum_le_tsum hle
          (Summable.of_nonneg_of_le (fun t => by positivity) hle (hs1.add hsx)) (hs1.add hsx)
        rw [Summable.tsum_add hs1 hsx] at hsum
        have hR : ∑' t : ℕ, 1 / (t : ℝ) ^ 2 = rd_exζ := by
          rw [← rd_exR_zero, rd_exR]
          simp
        rw [hR] at hsum
        linarith
  · cases h with
    | nil => simp [rd_exc, rd_exy]
    | cons s g => simp [rd_exc, rd_exy]

/-- The bond price `p_t = q⁰_{t+1}/q⁰_t`. -/
noncomputable def rd_exp (g : List Unit) (_j : Unit) : ℝ :=
  rd_exqd (g.length + 1) / rd_exqd g.length

/-- **Example 13.5.1** (Miao, p. 436): the one-period bond prices are `p₀ = 1` and
`p_t = t²/(t + 1)²`, and they satisfy (13.16) with `q⁰`. -/
theorem example_13_5_1_prices :
    rd_StatePrice rd_exp (fun _ _ => 1) rd_exq ∧ rd_exp [] () = 1 ∧
      ∀ g : List Unit, g ≠ [] →
        rd_exp g () = (g.length : ℝ) ^ 2 / ((g.length : ℝ) + 1) ^ 2 := by
  refine ⟨⟨fun h => rd_exqd_pos _, fun h j => ?_⟩, by simp [rd_exp, rd_exqd], fun g hg => ?_⟩
  · simp only [rd_exp, rd_exq, List.length_cons, Finset.univ_unique, Finset.sum_singleton,
      mul_one]
    rw [div_eq_inv_mul]
  · have hl : g.length ≠ 0 := fun h => hg (List.length_eq_zero_iff.1 h)
    have hpos : (0 : ℝ) < g.length := Nat.cast_pos.2 (Nat.pos_of_ne_zero hl)
    simp only [rd_exp, rd_exqd, hl, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.cast_add, Nat.cast_one]
    field_simp

/-- The strategies `θ¹_t = −(t + 1)² ∑_{n > t} 1/n²`, `θ² = −θ¹`. -/
noncomputable def rd_exθ (i : Bool) (g : List Unit) (_j : Unit) : ℝ :=
  (if i then -1 else 1) * (((g.length : ℝ) + 1) ^ 2 * rd_exR (g.length + 1))

/-- The value of agent 1's position: `p_t θ¹_t = −t² ∑_{n>t} 1/n²` for `t ≥ 1`. -/
theorem rd_ex_value (g : List Unit) (hg : g ≠ []) :
    rd_exp g ⬝ᵥ rd_exθ true g = -((g.length : ℝ) ^ 2 * rd_exR (g.length + 1)) := by
  simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, rd_exp, rd_exθ, ↓reduceIte]
  have hl : g.length ≠ 0 := fun h => hg (List.length_eq_zero_iff.1 h)
  · have hpos : (0 : ℝ) < g.length := Nat.cast_pos.2 (Nat.pos_of_ne_zero hl)
    simp only [rd_exqd, hl, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.cast_add, Nat.cast_one]
    field_simp

/-- The budgets of Example 13.5.1 bind under the bond strategies. -/
theorem rd_ex_budget (i : Bool) :
    rd_BudgetEq rd_exp (fun _ _ => 1) (rd_exy i) 0 (rd_exc i) (rd_exθ i) := by
  intro h
  cases h with
  | nil =>
    cases i <;> simp [rd_fz, rd_prev, rd_exc, rd_exy, rd_exζ, rd_exp, rd_exqd, rd_exθ,
      dotProduct]
  | cons s g =>
    have hv : rd_exp (s :: g) ⬝ᵥ rd_exθ i (s :: g) = (if i then 1 else -1) *
        -(((g.length : ℝ) + 1) ^ 2 * rd_exR (g.length + 2)) := by
      have := rd_ex_value (s :: g) (List.cons_ne_nil _ _)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at this
      rw [← this]
      cases i <;> simp [dotProduct, rd_exθ]
    rw [hv]
    simp only [rd_fz, rd_prev, dotProduct, Finset.univ_unique, Finset.sum_singleton, one_mul,
      rd_exθ]
    have hR := rd_exR_succ (g.length + 1)
    have hpos : (0 : ℝ) < (g.length : ℝ) + 1 := by positivity
    push_cast at hR
    cases i <;> simp only [rd_exc, rd_exy, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, List.length_cons, Nat.add_eq_zero_iff, one_ne_zero, and_false] <;>
      rw [hR] <;> field_simp <;> ring

/-- **Example 13.5.1** (Miao, p. 436): the transversality condition holds,
`π_T p_T θ¹_T = −∑_{n > T} 1/n² → 0`. -/
theorem example_13_5_1_TVC :
    (∀ T, rd_dsum (fun g => rd_exq g * (rd_exp g ⬝ᵥ rd_exθ true g)) [] T = -rd_exR (T + 1)) ∧
      ∀ i, rd_TVC rd_exq rd_exp (rd_exθ i) := by
  have hval : ∀ T, rd_dsum (fun g => rd_exq g * (rd_exp g ⬝ᵥ rd_exθ true g)) [] T =
      -rd_exR (T + 1) := by
    intro T
    rw [rd_dsum_unit]
    simp only [rd_exq, rd_exp, rd_exθ, dotProduct, Finset.univ_unique, Finset.sum_singleton,
      List.length_replicate, ↓reduceIte]
    have hq0 := (rd_exqd_pos T).ne'
    have h1 : rd_exqd (T + 1) = 1 / ((T : ℝ) + 1) ^ 2 := by
      simp [rd_exqd]
    have hpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    rw [h1]
    field_simp
  refine ⟨hval, fun i => ?_⟩
  have e : ∀ T, rd_dsum (fun g => rd_exq g * (rd_exp g ⬝ᵥ rd_exθ i g)) [] T =
      (if i then 1 else -1) * -rd_exR (T + 1) := by
    intro T
    rw [← hval]
    cases i
    · simp only [Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul, ← rd_dsum_neg]
      refine rd_dsum_congr (fun g => ?_) _ _
      simp [dotProduct, rd_exθ]
    · simp
  simp only [rd_TVC, e]
  have := (rd_exR_tendsto.comp (tendsto_add_atTop_nat 1)).neg.const_mul (if i then 1 else -1)
  simpa using this

/-- **Example 13.5.1** (Miao, p. 436): the allocation `(c¹*, c²*)`, the bond strategies, `π` and
`p` form a competitive equilibrium with transversality condition. -/
theorem example_13_5_1_CETVC :
    rd_CETVC (rd_uniformTree Unit) rd_exU rd_exy (fun _ => 0) (fun _ _ => 1) rd_exc rd_exθ
      rd_exq rd_exp := by
  have hPr : ∀ g, rd_exq g * (rd_uniformTree Unit).Pr g = rd_exq g := fun g => by
    simp [rd_uniformTree]
  simp only [rd_CETVC, hPr]
  obtain ⟨hL, hopt, hclear⟩ := example_13_5_1_AD
  have hsp := example_13_5_1_prices.1
  refine ⟨fun i => (hopt i).1.1, hL, fun h => rd_exqd_pos _, fun h j => ?_, fun j => ?_,
    fun i => ⟨⟨(hopt i).1.1, fun h => ((rd_ex_budget i) h).le, example_13_5_1_TVC.2 i⟩,
      fun c' θ' ⟨hc', hB, hT⟩ => (hopt i).2 c' ⟨hc', ?_⟩⟩,
    fun i => ⟨⟨(hopt i).1.1, by simpa [rd_ADBudget] using (hopt i).1.2⟩,
      fun c' ⟨hc', hb⟩ => (hopt i).2 c' ⟨hc', by simpa [rd_ADBudget] using hb⟩⟩,
    hsp, hclear, fun h => ?_⟩
  · exact div_nonneg (rd_exqd_pos _).le (rd_exqd_pos _).le
  · refine ⟨1, fun h => ?_⟩
    change |rd_exp h j| ≤ 1
    rw [rd_exp, abs_of_nonneg (div_nonneg (rd_exqd_pos _).le (rd_exqd_pos _).le),
      div_le_one (rd_exqd_pos _)]
    exact rd_exqd_succ_le _
  · have := eq_13_22 hsp hB hT (rd_L1_mul hL hc'.1) (rd_L1_mul hL (rd_exy_pos i).1)
    simpa [rd_ADBudget] using this
  · funext j
    simp [rd_exθ]

/-- **Example 13.5.1** (Miao, p. 436): agent 1's borrowing is unlimited,
`p_T θ¹_T = −∑_{s≥1} T²/(T + s)² → −∞`. -/
theorem example_13_5_1_unlimited :
    (∀ T : ℕ, 1 ≤ T → rd_exp (List.replicate T ()) ⬝ᵥ rd_exθ true (List.replicate T ()) =
      -∑' s : ℕ, (T : ℝ) ^ 2 / ((T : ℝ) + (s + 1)) ^ 2) ∧
      Tendsto (fun T : ℕ => rd_exp (List.replicate T ()) ⬝ᵥ rd_exθ true (List.replicate T ()))
        atTop atBot := by
  have hne : ∀ T : ℕ, 1 ≤ T → List.replicate T () ≠ [] := fun T hT => by
    intro e
    have := congrArg List.length e
    simp at this
    omega
  have hform : ∀ T : ℕ, 1 ≤ T → rd_exp (List.replicate T ()) ⬝ᵥ
      rd_exθ true (List.replicate T ()) =
      -∑' s : ℕ, (T : ℝ) ^ 2 / ((T : ℝ) + (s + 1)) ^ 2 := by
    intro T hT
    rw [rd_ex_value _ (hne T hT), List.length_replicate, rd_exR, ← tsum_mul_left]
    congr 1
    refine tsum_congr fun s => ?_
    push_cast
    ring
  refine ⟨hform, ?_⟩
  -- `T² R(T + 1) ≥ T/4`
  have hlow : ∀ T : ℕ, 1 ≤ T → (T : ℝ) / 4 ≤ (T : ℝ) ^ 2 * rd_exR (T + 1) := by
    intro T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have hpart : ∑ n ∈ Finset.range T, 1 / ((n + (T + 1) : ℕ) : ℝ) ^ 2 ≤ rd_exR (T + 1) :=
      (rd_exR_summable (T + 1)).sum_le_tsum _ fun n _ => by positivity
    have hterm : ∀ n ∈ Finset.range T, 1 / (2 * (T : ℝ)) ^ 2 ≤
        1 / ((n + (T + 1) : ℕ) : ℝ) ^ 2 := by
      intro n hn
      rw [Finset.mem_range] at hn
      apply one_div_le_one_div_of_le (by positivity)
      have : ((n + (T + 1) : ℕ) : ℝ) ≤ 2 * T := by
        have : n + (T + 1) ≤ 2 * T := by omega
        exact_mod_cast this
      have h0 : (0 : ℝ) ≤ ((n + (T + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have : (T : ℝ) * (1 / (2 * (T : ℝ)) ^ 2) = 1 / (4 * T) := by
      field_simp
      ring
    rw [this] at hsum
    have h1 : 1 / (4 * (T : ℝ)) ≤ rd_exR (T + 1) := hsum.trans hpart
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (T : ℝ))
    calc (T : ℝ) / 4 = (T : ℝ) ^ 2 * (1 / (4 * T)) := by field_simp
      _ ≤ _ := this
  have hv : ∀ T : ℕ, 1 ≤ T → rd_exp (List.replicate T ()) ⬝ᵥ
      rd_exθ true (List.replicate T ()) = -((T : ℝ) ^ 2 * rd_exR (T + 1)) := fun T hT => by
    rw [rd_ex_value _ (hne T hT), List.length_replicate]
  refine tendsto_atBot_mono' atTop (f₁ := fun T : ℕ => -((T : ℝ) / 4)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with T hT
    rw [hv T hT]
    linarith [hlow T hT]
  · exact tendsto_neg_atTop_atBot.comp
      ((tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num))

/-- **Example 13.5.1** (Miao, p. 436): "the equilibrium with transversality condition is not a
Radner equilibrium with borrowing constraints": no bounded borrowing limits admit the bond
strategies. -/
theorem example_13_5_1_not_Radner :
    ¬ ∃ Bbar : Bool → List Unit → ℝ, (∀ i, rd_Bdd (Bbar i)) ∧
      rd_RadnerBC rd_exU rd_exy (fun _ => 0) rd_exp (fun _ _ => 1) Bbar rd_exc rd_exθ := by
  rintro ⟨Bbar, hBb, hsol, -, -⟩
  obtain ⟨M, hM⟩ := hBb true
  have hbound : ∀ T : ℕ, -M ≤ rd_exp (List.replicate T ()) ⬝ᵥ rd_exθ true (List.replicate T ()) :=
    fun T => by
      have := (hsol true).1.2.2 (List.replicate T ())
      linarith [(le_abs_self _).trans (hM (List.replicate T ()))]
  have := example_13_5_1_unlimited.2.eventually (eventually_lt_atBot (-M))
  obtain ⟨T, hT⟩ := this.exists
  linarith [hbound T]

/-- **Example 13.5.1** (Miao, pp. 436–437): agent 2 becomes progressively more patient
(`t²/(t + 1)²` increases), and the present value at `T` of agent 1's future endowment,
`∑_{s≥1} π_{T+s}/π_T = ∑_{s≥1} T²/(T + s)²`, tends to infinity. -/
theorem example_13_5_1_patience :
    StrictMono (fun t : ℕ => (t : ℝ) ^ 2 / ((t : ℝ) + 1) ^ 2) ∧
      (∀ T : ℕ, 1 ≤ T → ∑' s : ℕ, rd_exqd (T + (s + 1)) / rd_exqd T =
        ∑' s : ℕ, (T : ℝ) ^ 2 / ((T : ℝ) + (s + 1)) ^ 2) ∧
      Tendsto (fun T : ℕ => ∑' s : ℕ, (T : ℝ) ^ 2 / ((T : ℝ) + (s + 1)) ^ 2) atTop atTop := by
  refine ⟨?_, fun T hT => ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ fun t => ?_
    have h1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [sq_nonneg (t : ℝ)]
  · refine tsum_congr fun s => ?_
    have hT0 : T ≠ 0 := by omega
    simp only [rd_exqd, hT0, ↓reduceIte, Nat.add_eq_zero_iff, Nat.add_one_ne_zero, and_false]
    push_cast
    field_simp
  · have := tendsto_neg_atBot_atTop.comp example_13_5_1_unlimited.2
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    simp only [Function.comp_apply, example_13_5_1_unlimited.1 T hT, neg_neg]

end Miao.CompleteMarkets
