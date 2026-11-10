/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.BPDeterministic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Real

/-!
# A bubble on an asset in positive supply (Werner 2012)

Miao, §13.6, Example 13.6.2, pp. 443–444. Two agents (`true` = agent 1, `false` = agent 2) with
`∑ βᵗ ln cⁱ_t`, one asset paying nothing (money) in unit supply held by agent 1, short-sales
constraints `θⁱ_t ≥ −1`, endowments alternating between `B` and `A > B > 0` with `βA > B`, and
date-0 endowments `y¹_0 = B + η/3`, `y²_0 = A − η/3`, where `η = (βA − B)/(β + 1)`.

* `example_13_6_2`: `p_t = η/3`, `c¹ = (B + η, A − η, …)`, `c² = (A − η, B + η, …)`,
  `θ¹ = (−1, 2, −1, …)`, `θ² = (2, −1, 2, …)` is an equilibrium. Optimality is proved by the
  Euler–Kuhn–Tucker argument (`bp_werner_optimal`), using `B + η = β(A − η)`
  (`bp_werner_eta`).
* `example_13_6_2_prices`: the state price deflator is `π_t = 1`, the fundamental value is `0`,
  the bubble is `p_t = η/3 > 0`, and the present value of aggregate endowments is infinite
  (`∑ (y¹_t + y²_t)` diverges), so Theorem 13.6.1 does not apply.
* `example_13_6_2_binds`: the short-sales constraint of agent 1 binds infinitely often.
* `example_13_6_2_tvc`: each agent's transversality condition
  `lim βᵗ u'(cⁱ_t) p_t (θⁱ_t + 1) = 0` (the form (13.40)) holds. The state price form
  `lim π_t p_t θⁱ_t = 0` of (13.21) fails (`example_13_6_2_tvc_21_fails`), so "the transversality
  condition holds" must be read as (13.40).
* `example_13_6_2_autarky`: the equilibrium with `p = 0`, no trade.
-/

open Filter Topology

namespace Miao.CompleteMarkets

/-- An alternating sequence `(a, b, a, b, …)`. -/
def bp_alt (a b : ℝ) (t : ℕ) : ℝ := if t % 2 = 0 then a else b

/-- `η = (βA − B)/(β + 1)`. -/
noncomputable def bp_werner_eta (β A B : ℝ) : ℝ := (β * A - B) / (β + 1)

/-- Agent `i`'s endowment: `y¹ = (B + η/3, A, B, A, …)`, `y² = (A − η/3, B, A, B, …)`. -/
noncomputable def bp_werner_y (β A B : ℝ) (i : Bool) (t : ℕ) : ℝ :=
  if t = 0 then (if i then B + bp_werner_eta β A B / 3 else A - bp_werner_eta β A B / 3)
  else (if i then bp_alt B A t else bp_alt A B t)

/-- Equilibrium consumption. -/
noncomputable def bp_werner_c (β A B : ℝ) (i : Bool) : ℕ → ℝ :=
  if i then bp_alt (B + bp_werner_eta β A B) (A - bp_werner_eta β A B)
  else bp_alt (A - bp_werner_eta β A B) (B + bp_werner_eta β A B)

/-- Equilibrium asset holdings. -/
def bp_werner_θ (i : Bool) : ℕ → ℝ := if i then bp_alt (-1) 2 else bp_alt 2 (-1)

theorem bp_werner_eta_facts (β A B : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hAB : B < A) (hB : 0 < B)
    (hβAB : B < β * A) :
    0 < bp_werner_eta β A B ∧ B + bp_werner_eta β A B = β * (A - bp_werner_eta β A B) ∧
      0 < A - bp_werner_eta β A B ∧ B + bp_werner_eta β A B < A - bp_werner_eta β A B := by
  unfold bp_werner_eta
  have h1 : 0 < β + 1 := by linarith
  refine ⟨div_pos (by linarith) h1, ?_, ?_, ?_⟩
  · field_simp
    ring
  · rw [sub_pos, div_lt_iff₀ h1]
    nlinarith
  · rw [← sub_pos]
    have : A - (β * A - B) / (β + 1) - (B + (β * A - B) / (β + 1)) =
        ((1 - β) * (A + B)) / (β + 1) := by field_simp; ring
    rw [this]
    exact div_pos (mul_pos (by linarith) (by linarith)) h1

/-- The optimality argument for one agent of Example 13.6.2: consumption alternates between
`lo = β·hi` and `hi`, the short-sales constraint binds at the low dates, and the budget
constraints hold with equality. Then the plan beats every feasible admissible plan. -/
theorem bp_werner_optimal (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (lo hi P θ0 : ℝ) (hlo : 0 < lo)
    (hhi : 0 < hi) (hlohi : lo = β * hi) (hP : 0 < P) (y c θ : ℕ → ℝ)
    (hcase : ∀ t, (c t = lo ∧ θ t = -1 ∧ c (t + 1) = hi) ∨ (c t = hi ∧ c (t + 1) = lo))
    (hθ : ∀ t, θ t ≤ 2) (hc : ∀ t, 0 < c t) (hclo : ∀ t, lo ≤ c t)
    (hb0 : c 0 + P * θ 0 = (P + 0) * θ0 + y 0)
    (hb : ∀ t, c (t + 1) + P * θ (t + 1) = (P + 0) * θ t + y (t + 1))
    (hadm : bp_detAdm β Real.log c) (c' θ' : ℕ → ℝ)
    (hb' : bp_detBudget (fun _ => P) (fun _ => 0) y θ0 (fun _ _ x => -1 ≤ x) c' θ')
    (hadm' : bp_detAdm β Real.log c') : bp_detU β Real.log c' ≤ bp_detU β Real.log c := by
  obtain ⟨hc', hb0', hbs', hcon'⟩ := hb'
  refine bp_det_sufficiency β hβ.le Real.log (fun x => 1 / x)
    (fun x x' hx hx' => bp_log_supergradient x x' hx hx') (fun _ => P) (fun _ => 0) y θ0 c θ c' θ'
    hc hc' (fun t => (one_div_pos.2 (hc t)).le) hb0 hb hb0' hbs' (fun t => ?_)
    (fun T => β ^ T * (1 / lo) * P * 3) ?_ (fun T => ?_) hadm hadm'
  · rcases hcase t with ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
    · rw [h1, h2, h3, add_zero]
      have hθ' : 0 ≤ θ' t - -1 := by linarith [hcon' t]
      have hneg : β ^ (t + 1) * (1 / hi) * P - β ^ t * (1 / lo) * P ≤ 0 := by
        rw [hlohi, pow_succ]
        have : β ^ t * β * (1 / hi) * P - β ^ t * (1 / (β * hi)) * P =
            β ^ t * P * (β ^ 2 - 1) / (β * hi) := by field_simp
        rw [this]
        refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
        refine mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_
        nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos hθ' hneg
    · rw [h1, h3, add_zero, hlohi, pow_succ]
      have : β ^ t * β * (1 / (β * hi)) * P - β ^ t * (1 / hi) * P = 0 := by
        field_simp
        ring
      rw [this, mul_zero]
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const (1 / lo * P * 3)
    simp only [zero_mul] at this
    convert this using 2 with T
    ring
  · have h1 : -(θ' T - θ T) ≤ 3 := by linarith [hcon' T, hθ T]
    have h2 : 1 / c T ≤ 1 / lo := one_div_le_one_div_of_le hlo (hclo T)
    have h3 : 0 ≤ β ^ T * (1 / c T) * P := by
      have := hc T
      positivity
    calc -(β ^ T * (1 / c T) * P * (θ' T - θ T))
        = β ^ T * (1 / c T) * P * (-(θ' T - θ T)) := by ring
      _ ≤ β ^ T * (1 / c T) * P * 3 := mul_le_mul_of_nonneg_left h1 h3
      _ ≤ β ^ T * (1 / lo) * P * 3 := by
        have : 0 ≤ β ^ T := pow_nonneg hβ.le T
        gcongr

/-- The utility of a bounded positive alternating plan converges. -/
theorem bp_werner_adm (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (a b : ℝ) :
    bp_detAdm β Real.log (bp_alt a b) := by
  unfold bp_detAdm
  refine Summable.of_norm_bounded (g := fun t => β ^ t * (|Real.log a| + |Real.log b|))
    ((summable_geometric_of_lt_one hβ.le hβ1).mul_right _) (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ.le t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ.le t)
  unfold bp_alt
  split_ifs
  · linarith [abs_nonneg (Real.log b)]
  · linarith [abs_nonneg (Real.log a)]

theorem bp_alt_succ (a b : ℝ) (t : ℕ) :
    (t % 2 = 0 ∧ bp_alt a b t = a ∧ bp_alt a b (t + 1) = b) ∨
      (t % 2 = 1 ∧ bp_alt a b t = b ∧ bp_alt a b (t + 1) = a) := by
  unfold bp_alt
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · left
    have h' : (t + 1) % 2 = 1 := by omega
    simp [h, h']
  · right
    have h' : (t + 1) % 2 = 0 := by omega
    simp [h, h']

/-- **Example 13.6.2** (Werner 2012, Miao, p. 443). With `A > B > 0`, `0 < β < 1` and `βA > B`,
the price `p_t = η/3`, `η = (βA − B)/(β + 1)`, with the book's consumption and portfolios, is an
equilibrium of the money economy with short-sales constraints `θⁱ_t ≥ −1`. -/
theorem example_13_6_2 (β A B : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hAB : B < A) (hB : 0 < B)
    (hβAB : B < β * A) :
    BPDetEqm (fun _ => bp_detU β Real.log) (fun _ => bp_detAdm β Real.log)
      (bp_werner_y β A B) (fun _ => 0) (fun i => if i then 1 else 0)
      (fun _ _ _ x => -1 ≤ x) (bp_werner_c β A B) bp_werner_θ
      (fun _ => bp_werner_eta β A B / 3) := by
  obtain ⟨hη, hlohi, hhi, hlt⟩ := bp_werner_eta_facts β A B hβ hβ1 hAB hB hβAB
  set η := bp_werner_eta β A B with hηdef
  have hlo : 0 < B + η := by linarith
  have hbud : ∀ i, (bp_werner_c β A B i 0 + η / 3 * bp_werner_θ i 0 =
      (η / 3 + 0) * (if i then 1 else 0) + bp_werner_y β A B i 0) ∧
      ∀ t, bp_werner_c β A B i (t + 1) + η / 3 * bp_werner_θ i (t + 1) =
        (η / 3 + 0) * bp_werner_θ i t + bp_werner_y β A B i (t + 1) := by
    intro i
    refine ⟨?_, fun t => ?_⟩
    · cases i <;> simp [bp_werner_c, bp_werner_θ, bp_werner_y, bp_alt, ← hηdef] <;> ring
    · have ht1 : t + 1 ≠ 0 := by omega
      rcases Nat.mod_two_eq_zero_or_one t with h | h
      · have h' : (t + 1) % 2 = 1 := by omega
        cases i <;> simp [bp_werner_c, bp_werner_θ, bp_werner_y, bp_alt, h, h', ← hηdef] <;> ring
      · have h' : (t + 1) % 2 = 0 := by omega
        cases i <;> simp [bp_werner_c, bp_werner_θ, bp_werner_y, bp_alt, h, h', ← hηdef] <;> ring
  have hcpos : ∀ i t, 0 < bp_werner_c β A B i t := by
    intro i t
    cases i <;> simp only [bp_werner_c, Bool.false_eq_true, ↓reduceIte, bp_alt] <;>
      split_ifs <;> linarith
  have hcon : ∀ i t, -1 ≤ bp_werner_θ i t := by
    intro i t
    cases i <;> simp only [bp_werner_θ, Bool.false_eq_true, ↓reduceIte, bp_alt] <;>
      split_ifs <;> norm_num
  have hadm : ∀ i, bp_detAdm β Real.log (bp_werner_c β A B i) := by
    intro i
    cases i
    · exact bp_werner_adm β hβ hβ1 _ _
    · exact bp_werner_adm β hβ hβ1 _ _
  refine ⟨fun i => ⟨hcpos i, ((hbud i).1).le, fun t => ((hbud i).2 t).le, fun t => hcon i t⟩,
    hadm, fun i c' θ' hb hadm' => ?_, fun t => ?_, fun t => ?_⟩
  · refine bp_werner_optimal β hβ hβ1 (B + η) (A - η) (η / 3) (if i then 1 else 0) hlo hhi
      hlohi (by linarith) (bp_werner_y β A B i) (bp_werner_c β A B i) (bp_werner_θ i)
      (fun t => ?_) (fun t => ?_) (hcpos i) (fun t => ?_) ((hbud i).1) ((hbud i).2) (hadm i)
      c' θ' hb hadm'
    · cases i
      · rcases bp_alt_succ (A - η) (B + η) t with ⟨h, h1, h2⟩ | ⟨h, h1, h2⟩
        · right
          exact ⟨h1, h2⟩
        · left
          refine ⟨h1, ?_, h2⟩
          simp [bp_werner_θ, bp_alt, h]
      · rcases bp_alt_succ (B + η) (A - η) t with ⟨h, h1, h2⟩ | ⟨h, h1, h2⟩
        · left
          refine ⟨h1, ?_, h2⟩
          simp [bp_werner_θ, bp_alt, h]
        · right
          exact ⟨h1, h2⟩
    · cases i <;> simp only [bp_werner_θ, Bool.false_eq_true, ↓reduceIte, bp_alt] <;>
        split_ifs <;> norm_num
    · cases i <;> simp only [bp_werner_c, Bool.false_eq_true, ↓reduceIte, bp_alt] <;>
        split_ifs <;> linarith
  · simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton, ↓reduceIte, bp_werner_θ, Bool.false_eq_true,
      bp_alt]
    split_ifs <;> norm_num
  · simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton, ↓reduceIte, bp_werner_c, bp_werner_y,
      Bool.false_eq_true, bp_alt, mul_zero, add_zero]
    split_ifs <;> ring

/-- Example 13.6.2, p. 444: the state price deflator `π_t = 1` prices the asset
(`π_{t+1} = (p_t/p_{t+1}) π_t`), its fundamental value is zero (no payoff), so the whole price
`p_t = η/3 > 0` is a bubble, and the present value of the aggregate endowment
`∑ π_t (y¹_t + y²_t)` is infinite (`π ∉ L¹`). -/
theorem example_13_6_2_prices (β A B : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hAB : B < A) (hB : 0 < B)
    (hβAB : B < β * A) :
    (∀ _t : ℕ, (1 : ℝ) * (bp_werner_eta β A B / 3) = 1 * (bp_werner_eta β A B / 3 + 0)) ∧
      (∀ t : ℕ, 1 / (1 : ℝ) * bp_tail (fun _ => (1 : ℝ) * 0) t = 0) ∧
      0 < bp_werner_eta β A B / 3 ∧
      ¬ Summable (fun t => (1 : ℝ) * (bp_werner_y β A B true t + bp_werner_y β A B false t)) := by
  obtain ⟨hη, -, -, -⟩ := bp_werner_eta_facts β A B hβ hβ1 hAB hB hβAB
  refine ⟨fun _ => by ring, fun t => by simp [bp_tail], by linarith, fun hs => ?_⟩
  have h0 := hs.tendsto_atTop_zero
  have hconst : ∀ t, 1 ≤ t → (1 : ℝ) * (bp_werner_y β A B true t + bp_werner_y β A B false t) =
      A + B := by
    intro t ht
    have ht0 : t ≠ 0 := by omega
    simp only [bp_werner_y, ht0, ↓reduceIte, bp_alt, one_mul]
    split_ifs <;> first | ring1 | (exfalso; assumption)
  have hlim : Tendsto (fun t => (1 : ℝ) * (bp_werner_y β A B true t +
      bp_werner_y β A B false t)) atTop (𝓝 (A + B)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with t ht
      exact (hconst t ht).symm)
  have := tendsto_nhds_unique hlim h0
  linarith

/-- Example 13.6.2, p. 444: "the bubbly equilibrium occurs when the short-sales constraint binds
infinitely often": agent 1's constraint `θ¹_t ≥ −1` binds at every even date. -/
theorem example_13_6_2_binds (N : ℕ) : ∃ t, N ≤ t ∧ bp_werner_θ true t = -1 :=
  ⟨2 * N, by omega, by simp [bp_werner_θ, bp_alt]⟩

/-- Example 13.6.2, p. 444: each agent's transversality condition
`lim βᵗ u'(cⁱ_t) p_t (θⁱ_t + 1) = 0` (the form (13.40) for short-sales constraints) holds. -/
theorem example_13_6_2_tvc (β A B : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hAB : B < A) (hB : 0 < B)
    (hβAB : B < β * A) (i : Bool) :
    Tendsto (fun t => β ^ t * (1 / bp_werner_c β A B i t) * (bp_werner_eta β A B / 3) *
      (bp_werner_θ i t + 1)) atTop (𝓝 0) := by
  obtain ⟨hη, -, hhi, hlt⟩ := bp_werner_eta_facts β A B hβ hβ1 hAB hB hβAB
  set η := bp_werner_eta β A B
  have hlo : 0 < B + η := by linarith
  set K := 1 / (B + η) * (η / 3) * 3 with hK
  have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const K
  rw [zero_mul] at hg
  refine squeeze_zero (fun t => ?_) (fun t => ?_) hg
  · have hc : 0 < bp_werner_c β A B i t := by
      cases i <;> simp only [bp_werner_c, Bool.false_eq_true, ↓reduceIte, bp_alt] <;>
        split_ifs <;> linarith
    have hθ : 0 ≤ bp_werner_θ i t + 1 := by
      cases i <;> simp only [bp_werner_θ, Bool.false_eq_true, ↓reduceIte, bp_alt] <;>
        split_ifs <;> norm_num
    have := pow_nonneg hβ.le t
    have : 0 < 1 / bp_werner_c β A B i t := one_div_pos.2 hc
    positivity
  · have hc : B + η ≤ bp_werner_c β A B i t := by
      cases i <;> simp only [bp_werner_c, Bool.false_eq_true, ↓reduceIte, bp_alt] <;>
        split_ifs <;> linarith
    have hθ : bp_werner_θ i t + 1 ≤ 3 := by
      cases i <;> simp only [bp_werner_θ, Bool.false_eq_true, ↓reduceIte, bp_alt] <;>
        split_ifs <;> norm_num
    have hθ0 : 0 ≤ bp_werner_θ i t + 1 := by
      cases i <;> simp only [bp_werner_θ, Bool.false_eq_true, ↓reduceIte, bp_alt] <;>
        split_ifs <;> norm_num
    have h1 : 1 / bp_werner_c β A B i t ≤ 1 / (B + η) := one_div_le_one_div_of_le hlo hc
    have hpow := pow_nonneg hβ.le t
    have hη3 : 0 ≤ η / 3 := by linarith
    calc β ^ t * (1 / bp_werner_c β A B i t) * (η / 3) * (bp_werner_θ i t + 1)
        ≤ β ^ t * (1 / (B + η)) * (η / 3) * 3 := by gcongr
      _ = β ^ t * K := by rw [hK]; ring

/-- Example 13.6.2: the state price form `lim π_t p_t θ¹_t = 0` of the transversality condition
(13.21) fails (`π_t = 1`, `p_t θ¹_t` alternates between `−η/3` and `2η/3`). -/
theorem example_13_6_2_tvc_21_fails (β A B : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hAB : B < A)
    (hB : 0 < B) (hβAB : B < β * A) :
    ¬ Tendsto (fun t => (1 : ℝ) * (bp_werner_eta β A B / 3) * bp_werner_θ true t) atTop
      (𝓝 0) := by
  obtain ⟨hη, -, -, -⟩ := bp_werner_eta_facts β A B hβ hβ1 hAB hB hβAB
  intro h
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  have := h.comp h2
  have hev : (fun t => (1 : ℝ) * (bp_werner_eta β A B / 3) * bp_werner_θ true t) ∘
      (fun k : ℕ => 2 * k) = fun _ => -(bp_werner_eta β A B / 3) := by
    funext k
    simp [bp_werner_θ, bp_alt]
  rw [hev] at this
  have := tendsto_nhds_unique tendsto_const_nhds this
  linarith

/-- Example 13.6.2, p. 444: "there is another equilibrium in which `p = 0`": the asset has no
value and no trade occurs. -/
theorem example_13_6_2_autarky (β A B : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hAB : B < A)
    (hB : 0 < B) (hβAB : B < β * A) :
    BPDetEqm (fun _ => bp_detU β Real.log) (fun _ => bp_detAdm β Real.log)
      (bp_werner_y β A B) (fun _ => 0) (fun i => if i then 1 else 0)
      (fun _ _ _ x => -1 ≤ x) (bp_werner_y β A B) (fun i _ => if i then 1 else 0)
      (fun _ => 0) := by
  obtain ⟨hη, -, hhi, -⟩ := bp_werner_eta_facts β A B hβ hβ1 hAB hB hβAB
  have hypos : ∀ i t, 0 < bp_werner_y β A B i t := by
    intro i t
    cases i <;> simp only [bp_werner_y, Bool.false_eq_true, ↓reduceIte, bp_alt] <;>
      split_ifs <;> linarith
  have hyadm : ∀ i, bp_detAdm β Real.log (bp_werner_y β A B i) := by
    intro i
    unfold bp_detAdm
    set K := |Real.log A| + |Real.log B| + |Real.log (bp_werner_y β A B i 0)| with hK
    refine Summable.of_norm_bounded (g := fun t => β ^ t * K)
      ((summable_geometric_of_lt_one hβ.le hβ1).mul_right _) (fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ.le t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ.le t)
    have hA := abs_nonneg (Real.log A)
    have hB' := abs_nonneg (Real.log B)
    have h0 := abs_nonneg (Real.log (bp_werner_y β A B i 0))
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      linarith
    · have ht0 : t ≠ 0 := ht.ne'
      cases i <;> simp only [bp_werner_y, ht0, Bool.false_eq_true, ↓reduceIte, bp_alt] <;>
        split_ifs <;> linarith
  refine ⟨fun i => ⟨hypos i, by simp, fun t => by simp, fun t => ?_⟩, hyadm,
    fun i c' θ' hb hadm' => ?_, fun t => by simp, fun t => by simp⟩
  · split_ifs <;> norm_num
  · obtain ⟨hc', hb0, hbs, -⟩ := hb
    have hle : ∀ t, c' t ≤ bp_werner_y β A B i t := by
      intro t
      cases t with
      | zero => simpa using hb0
      | succ t => simpa using hbs t
    unfold bp_detU
    refine Summable.tsum_le_tsum (fun t => ?_) hadm' (hyadm i)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (hc' t) (hle t)) (pow_nonneg hβ.le t)

end Miao.CompleteMarkets
