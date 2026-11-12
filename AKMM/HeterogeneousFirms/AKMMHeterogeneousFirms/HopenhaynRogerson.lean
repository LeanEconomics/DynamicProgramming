/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.Option

/-!
# Hopenhayn–Rogerson: block recursivity (AKMM §22.5)

AKMM, §22.5.1, pp. 673–675, with footnote 11. The firm's problem (22.13) is posed on a finite
grid: productivity states `a ∈ A` with values `aᵥ(a) > 0` and a Markov matrix `Q`, employment
choices `ℓ ∈ L` with values `ℓᵥ`, and lagged employment in `Option L` (`none` is the entrant's
`ℓ₋₁ = 0`).

* **The Bellman equation (22.12)–(22.13)** at the wage `w` has a unique solution `W_w`
  (`hr_bellman_existsUnique`); the operator is a `β`-contraction (`hr_T_sub_le`).
* **Monotonicity in the wage**: `W_w` is antitone in `w`, strictly when every employment level
  is positive, with an explicit gap (`hr_value_wage_gap`), and `W_w` is Lipschitz in `w`
  (`hr_value_lipschitz`).
* **Block recursivity and free entry (22.14)**: the entry value `Wᵉ(w)` depends on `w` only; it
  is strictly decreasing and continuous (`hr_entry_strictAnti`, `hr_entry_continuous`), so free
  entry `Wᵉ(w) = c_e + κ` has at most one solution (`hr_free_entry_unique`), one exists when
  `Wᵉ` brackets `c_e + κ` (`hr_free_entry_exists`), and higher entry barriers `κ` lower the
  wage (`hr_entry_barrier_wage`).
* **The stationary distribution for a given entry mass `M`**: with a survivor matrix whose row
  sums are at most `q < 1`, `μ = μQ + Mν` has a unique solution, it is nonnegative, and it is
  `M` times the solution for `M = 1` (`hr_stationary_existsUnique`, `hr_stationary_nonneg`,
  `hr_stationary_linear`); aggregates are linear in `M` (`hr_aggregate_linear`).
* **The labour market (22.15)** with `u = log`: labour supply is `1/χ − (Π + R)/w`
  (`eq_22_15`), and the entry mass clearing the market is unique (`hr_entry_mass`).
* **Footnote 11**: the steady-state Euler equation gives the gross interest rate `1/β`
  (`hr_footnote_11`).
-/

namespace AKMM.HeterogeneousFirms

/-! ### The firm's problem -/

/-- The primitives of the Hopenhayn–Rogerson firm on a grid (AKMM, p. 673): discount factor,
firing tax, fixed cost, returns `γ`, productivity values, employment values, productivity
transition matrix. -/
structure HRFirm (A L : Type*) where
  β : ℝ
  τ : ℝ
  cf : ℝ
  γ : ℝ
  av : A → ℝ
  lv : L → ℝ
  Q : A → A → ℝ

variable {A L : Type*} [Fintype A] [Fintype L] [Nonempty L]

/-- Lagged employment: `none` is `ℓ₋₁ = 0`. -/
def hrLag {L : Type*} (lv : L → ℝ) (o : Option L) : ℝ := o.elim 0 lv

/-- AKMM, (22.12), p. 673: the flow profit `aℓ^γ − wℓ − c_f − τ max(0, ℓ₋₁ − ℓ)`. -/
noncomputable def hrProfit (F : HRFirm A L) (w : ℝ) (l0 : Option L) (l : L) (a : A) : ℝ :=
  F.av a * F.lv l ^ F.γ - w * F.lv l - F.cf - F.τ * max 0 (hrLag F.lv l0 - F.lv l)

/-- AKMM, (22.13), p. 674: the Bellman operator
`(TW)(a, ℓ₋₁) = max_ℓ π(ℓ₋₁, ℓ, a) + β max{E[W(a', ℓ)|a], −τℓ}`. -/
noncomputable def hrT (F : HRFirm A L) (w : ℝ) (W : A → Option L → ℝ) (a : A)
    (l0 : Option L) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun l =>
    hrProfit F w l0 l a + F.β * max (∑ a', F.Q a a' * W a' (some l)) (-(F.τ * F.lv l))

/-- `max x c − max y c ≤ max (x − y) 0`. -/
theorem hr_max_sub_le (x y c : ℝ) : max x c - max y c ≤ max (x - y) 0 := by
  have h1 : max x c ≤ max y c + max (x - y) 0 := max_le (by
    linarith [le_max_left y c, le_max_left (x - y) 0]) (by
    linarith [le_max_right y c, le_max_right (x - y) 0])
  linarith

/-- The key estimate: if `W − W' ≤ D` with `D ≥ 0`, and `(w' − w)k ≤ (w' − w)ℓᵥ` for every
`ℓ`, then `T_{w'}W − T_wW' ≤ βD − (w' − w)k`. -/
theorem hr_T_sub_le (F : HRFirm A L) (hβ : 0 ≤ F.β) (hQ0 : ∀ a a', 0 ≤ F.Q a a')
    (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {W W' : A → Option L → ℝ} {D : ℝ}
    (hD : ∀ a l0, W a l0 - W' a l0 ≤ D) (hD0 : 0 ≤ D) {w w' k : ℝ}
    (hk : ∀ l, (w' - w) * k ≤ (w' - w) * F.lv l) (a : A) (l0 : Option L) :
    hrT F w' W a l0 - hrT F w W' a l0 ≤ F.β * D - (w' - w) * k := by
  unfold hrT
  rw [sub_le_iff_le_add]
  refine Finset.sup'_le _ _ fun l _ => ?_
  refine le_trans ?_ (add_le_add le_rfl (Finset.le_sup' (fun l =>
    hrProfit F w l0 l a + F.β * max (∑ a', F.Q a a' * W' a' (some l)) (-(F.τ * F.lv l)))
    (Finset.mem_univ l)))
  have hE : ∑ a', F.Q a a' * W a' (some l) - ∑ a', F.Q a a' * W' a' (some l) ≤ D := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ a', (F.Q a a' * W a' (some l) - F.Q a a' * W' a' (some l))
        ≤ ∑ a', F.Q a a' * D := Finset.sum_le_sum fun a' _ => by
          rw [← mul_sub]; exact mul_le_mul_of_nonneg_left (hD a' _) (hQ0 a a')
      _ = D := by rw [← Finset.sum_mul, hQ1, one_mul]
  have hM := hr_max_sub_le (∑ a', F.Q a a' * W a' (some l))
    (∑ a', F.Q a a' * W' a' (some l)) (-(F.τ * F.lv l))
  have hM' : max (∑ a', F.Q a a' * W a' (some l) - ∑ a', F.Q a a' * W' a' (some l)) 0 ≤ D :=
    max_le hE hD0
  have hπ : hrProfit F w' l0 l a = hrProfit F w l0 l a - (w' - w) * F.lv l := by
    unfold hrProfit; ring
  rw [hπ]
  nlinarith [mul_le_mul_of_nonneg_left (hM.trans hM') hβ, hk l]

/-- The Bellman operator is a `β`-contraction in the sup metric. -/
theorem hr_T_dist_le (F : HRFirm A L) (hβ : 0 ≤ F.β) (hQ0 : ∀ a a', 0 ≤ F.Q a a')
    (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) (w : ℝ) (W W' : A → Option L → ℝ) :
    dist (hrT F w W) (hrT F w W') ≤ F.β * dist W W' := by
  have hd : ∀ (U V : A → Option L → ℝ) a l0, U a l0 - V a l0 ≤ dist U V := fun U V a l0 =>
    (le_abs_self _).trans (by
      rw [← Real.dist_eq]; exact (dist_le_pi_dist (U a) (V a) l0).trans (dist_le_pi_dist U V a))
  have hk : ∀ l, (w - w) * 0 ≤ (w - w) * F.lv l := fun l => by simp
  rw [dist_pi_le_iff (mul_nonneg hβ dist_nonneg)]
  intro a
  rw [dist_pi_le_iff (mul_nonneg hβ dist_nonneg)]
  intro l0
  rw [Real.dist_eq, abs_le]
  have h1 := hr_T_sub_le F hβ hQ0 hQ1 (hd W W') dist_nonneg hk a l0
  have h2 := hr_T_sub_le F hβ hQ0 hQ1 (hd W' W) dist_nonneg hk a l0
  rw [dist_comm W' W] at h2
  constructor <;> linarith

/-- AKMM, (22.13), p. 674: **the firm's Bellman equation has a unique solution** at every wage,
for `0 ≤ β < 1` and a Markov matrix `Q`. -/
theorem hr_bellman_existsUnique (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) (w : ℝ) :
    ∃! W : A → Option L → ℝ, hrT F w W = W := by
  have hK : ContractingWith (Real.toNNReal F.β) (hrT F w) := by
    refine ⟨by rw [Real.toNNReal_lt_one]; exact hβ1, LipschitzWith.of_dist_le' fun W W' =>
      hr_T_dist_le F hβ hQ0 hQ1 w W W'⟩
  refine ⟨ContractingWith.fixedPoint _ hK, ContractingWith.fixedPoint_isFixedPt hK,
    fun W hW => ContractingWith.fixedPoint_unique hK hW⟩

/-- The value function `W_w` (chosen by `Classical.epsilon`; it solves the Bellman equation
under the hypotheses of `hr_bellman_existsUnique`, see `hr_value_spec`). -/
noncomputable def hrValue (F : HRFirm A L) (w : ℝ) : A → Option L → ℝ :=
  Classical.epsilon fun W => hrT F w W = W

theorem hr_value_spec (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) (w : ℝ) :
    hrT F w (hrValue F w) = hrValue F w :=
  Classical.epsilon_spec (hr_bellman_existsUnique F hβ hβ1 hQ0 hQ1 w).exists

/-- A fixed-point comparison: if `W = T_wW`, `W' = T_{w'}W'` and `(w' − w)k ≤ (w' − w)ℓᵥ` for
all `ℓ`, then `W' − W ≤ max(0, −(w' − w)k)/(1 − β)`; in particular `W' ≤ W − (w' − w)k` when
`(w' − w)k ≥ 0`. -/
theorem hr_fixed_compare [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {w w' k : ℝ}
    {W W' : A → Option L → ℝ} (hW : hrT F w W = W) (hW' : hrT F w' W' = W')
    (hk : ∀ l, (w' - w) * k ≤ (w' - w) * F.lv l) :
    ∀ a l0, W' a l0 - W a l0 ≤ F.β * max (-(w' - w) * k) 0 / (1 - F.β) - (w' - w) * k := by
  obtain ⟨⟨a1, o1⟩, hmax⟩ := Finite.exists_max fun s : A × Option L => W' s.1 s.2 - W s.1 s.2
  set D := max (W' a1 o1 - W a1 o1) 0
  have hD : ∀ a l0, W' a l0 - W a l0 ≤ D := fun a l0 =>
    (hmax (a, l0)).trans (le_max_left _ _)
  have hD0 : 0 ≤ D := le_max_right _ _
  have hstep : ∀ a l0, W' a l0 - W a l0 ≤ F.β * D - (w' - w) * k := fun a l0 => by
    have := hr_T_sub_le F hβ hQ0 hQ1 hD hD0 hk a l0
    rwa [hW, hW'] at this
  have h1β : 0 < 1 - F.β := by linarith
  have hDle : D ≤ F.β * D + max (-(w' - w) * k) 0 := max_le
    (by linarith [hstep a1 o1, le_max_left (-(w' - w) * k) 0])
    (by nlinarith [le_max_right (-(w' - w) * k) 0])
  have hDb : D ≤ max (-(w' - w) * k) 0 / (1 - F.β) := by
    rw [le_div_iff₀ h1β]; linarith
  intro a l0
  have := hstep a l0
  have := mul_le_mul_of_nonneg_left hDb hβ
  rw [mul_div_assoc]
  linarith

/-- AKMM, p. 675: **the value falls with the wage, with a gap**. If every employment level is at
least `m ≥ 0` and `w ≤ w'`, then `W_{w'} ≤ W_w − (w' − w)m`. -/
theorem hr_value_wage_gap [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {m : ℝ} (hm : 0 ≤ m)
    (hlm : ∀ l, m ≤ F.lv l) {w w' : ℝ} (hww : w ≤ w') (a : A) (l0 : Option L) :
    hrValue F w' a l0 ≤ hrValue F w a l0 - (w' - w) * m := by
  have h := hr_fixed_compare F hβ hβ1 hQ0 hQ1 (hr_value_spec F hβ hβ1 hQ0 hQ1 w)
    (hr_value_spec F hβ hβ1 hQ0 hQ1 w') (k := m)
    (fun l => mul_le_mul_of_nonneg_left (hlm l) (by linarith)) a l0
  have : max (-(w' - w) * m) 0 = 0 := max_eq_right (by nlinarith)
  rw [this, mul_zero, zero_div, zero_sub] at h
  linarith

/-- The value is Lipschitz in the wage: with employment levels in `[0, ℓ̄]`,
`|W_w − W_{w'}| ≤ ℓ̄|w − w'|/(1 − β)`. -/
theorem hr_value_lipschitz [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {lbar : ℝ}
    (hl0 : ∀ l, 0 ≤ F.lv l) (hlb : ∀ l, F.lv l ≤ lbar) {w w' : ℝ} (hww : w ≤ w') (a : A)
    (l0 : Option L) :
    |hrValue F w a l0 - hrValue F w' a l0| ≤ lbar * (w' - w) / (1 - F.β) := by
  have h1β : 0 < 1 - F.β := by linarith
  have hlb0 : 0 ≤ lbar := (hl0 (Classical.arbitrary L)).trans (hlb _)
  have hW := hr_value_spec F hβ hβ1 hQ0 hQ1 w
  have hW' := hr_value_spec F hβ hβ1 hQ0 hQ1 w'
  -- `W_w − W_{w'}`: compare with the roles of the wages swapped, `k = ℓ̄`
  have h1 := hr_fixed_compare F hβ hβ1 hQ0 hQ1 hW' hW (k := lbar)
    (fun l => mul_le_mul_of_nonpos_left (hlb l) (by linarith)) a l0
  have hmx : max (-(w - w') * lbar) 0 = lbar * (w' - w) := by
    rw [max_eq_left (by nlinarith [mul_nonneg (sub_nonneg.mpr hww) hlb0])]; ring
  rw [hmx] at h1
  have e : F.β * (lbar * (w' - w)) / (1 - F.β) - (w - w') * lbar = lbar * (w' - w) / (1 - F.β) :=
    by field_simp; ring
  rw [e] at h1
  have h2 := hr_value_wage_gap F hβ hβ1 hQ0 hQ1 le_rfl hl0 hww a l0
  rw [abs_le]
  constructor
  · have : 0 ≤ lbar * (w' - w) / (1 - F.β) := by
      apply div_nonneg _ h1β.le; nlinarith
    linarith
  · linarith

/-! ### Free entry (22.14) -/

/-- AKMM, p. 674: the value of entry `Wᵉ(w) = Σ_a ν(a)(W_w(a, 0) + c_f)`. It depends on the wage
only: **block recursivity**. -/
noncomputable def hrEntry (F : HRFirm A L) (ν : A → ℝ) (w : ℝ) : ℝ :=
  ∑ a, ν a * (hrValue F w a none + F.cf)

/-- AKMM, p. 675: with positive employment levels (`ℓᵥ ≥ m > 0`) and an entrant distribution
`ν`, the entry value is strictly decreasing in the wage. -/
theorem hr_entry_strictAnti [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {m : ℝ} (hm : 0 < m)
    (hlm : ∀ l, m ≤ F.lv l) {ν : A → ℝ} (hν0 : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1) :
    StrictAnti (hrEntry F ν) := by
  intro w w' hww
  unfold hrEntry
  have h : ∑ a, ν a * (hrValue F w' a none + F.cf) ≤
      ∑ a, ν a * (hrValue F w a none + F.cf) - (w' - w) * m := by
    rw [show (w' - w) * m = ∑ a, ν a * ((w' - w) * m) by rw [← Finset.sum_mul, hν1, one_mul],
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (hν0 a)
    linarith [hr_value_wage_gap F hβ hβ1 hQ0 hQ1 hm.le hlm hww.le a none]
  have : 0 < (w' - w) * m := mul_pos (by linarith) hm
  linarith

/-- The entry value is continuous in the wage. -/
theorem hr_entry_continuous [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {lbar : ℝ}
    (hl0 : ∀ l, 0 ≤ F.lv l) (hlb : ∀ l, F.lv l ≤ lbar) (ν : A → ℝ) :
    Continuous (hrEntry F ν) := by
  have h1β : 0 < 1 - F.β := by linarith
  have hlb0 : 0 ≤ lbar := (hl0 (Classical.arbitrary L)).trans (hlb _)
  have hc : ∀ a, Continuous fun w => hrValue F w a none := fun a => by
    refine (LipschitzWith.of_dist_le' (K := lbar / (1 - F.β)) fun w w' => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total w w' with h | h
    · have := hr_value_lipschitz F hβ hβ1 hQ0 hQ1 hl0 hlb h a none
      rw [abs_of_nonpos (by linarith : w - w' ≤ 0)]
      calc _ ≤ lbar * (w' - w) / (1 - F.β) := this
        _ = lbar / (1 - F.β) * -(w - w') := by ring
    · have := hr_value_lipschitz F hβ hβ1 hQ0 hQ1 hl0 hlb h a none
      rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ w - w')]
      calc _ ≤ lbar * (w - w') / (1 - F.β) := this
        _ = lbar / (1 - F.β) * (w - w') := by ring
  unfold hrEntry
  exact continuous_finsetSum _ fun a _ => continuous_const.mul ((hc a).add continuous_const)

/-- AKMM, (22.14), p. 674: **free entry pins down the wage**: at most one `w` satisfies
`Wᵉ(w) = c_e + κ`. -/
theorem hr_free_entry_unique [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {m : ℝ} (hm : 0 < m)
    (hlm : ∀ l, m ≤ F.lv l) {ν : A → ℝ} (hν0 : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1)
    {ce κ w w' : ℝ} (hw : hrEntry F ν w = ce + κ) (hw' : hrEntry F ν w' = ce + κ) :
    w = w' :=
  (hr_entry_strictAnti F hβ hβ1 hQ0 hQ1 hm hlm hν0 hν1).injective (hw.trans hw'.symm)

/-- AKMM, (22.14): a free-entry wage exists when `Wᵉ` brackets `c_e + κ` on `[w₀, w₁]`. -/
theorem hr_free_entry_exists [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {lbar : ℝ}
    (hl0 : ∀ l, 0 ≤ F.lv l) (hlb : ∀ l, F.lv l ≤ lbar) (ν : A → ℝ) {ce κ w0 w1 : ℝ}
    (h01 : w0 ≤ w1) (hlo : ce + κ ≤ hrEntry F ν w0) (hhi : hrEntry F ν w1 ≤ ce + κ) :
    ∃ w ∈ Set.Icc w0 w1, hrEntry F ν w = ce + κ := by
  have hc := (hr_entry_continuous F hβ hβ1 hQ0 hQ1 hl0 hlb ν).continuousOn (s := Set.Icc w0 w1)
  exact intermediate_value_Icc' h01 hc ⟨hhi, hlo⟩

/-- AKMM, p. 677: **entry barriers lower the wage**: if `w` and `w'` clear free entry with
barriers `κ < κ'`, then `w' < w`. -/
theorem hr_entry_barrier_wage [Nonempty A] (F : HRFirm A L) (hβ : 0 ≤ F.β) (hβ1 : F.β < 1)
    (hQ0 : ∀ a a', 0 ≤ F.Q a a') (hQ1 : ∀ a, ∑ a', F.Q a a' = 1) {m : ℝ} (hm : 0 < m)
    (hlm : ∀ l, m ≤ F.lv l) {ν : A → ℝ} (hν0 : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1)
    {ce κ κ' w w' : ℝ} (hκ : κ < κ') (hw : hrEntry F ν w = ce + κ)
    (hw' : hrEntry F ν w' = ce + κ') : w' < w :=
  (hr_entry_strictAnti F hβ hβ1 hQ0 hQ1 hm hlm hν0 hν1).lt_iff_gt.mp (by linarith)

/-! ### The stationary distribution for a given entry mass -/

variable {S : Type*} [Fintype S]

/-- AKMM, p. 675: the stationary condition with entry mass `M`: `μ(s') = Σ_s μ(s)Q(s,s') + Mν(s')`,
where `Q` is the survivor transition under the decision rule of (22.13) (row sums `< 1` through
exit) and `ν` the entrants' distribution over states. -/
def HRStationary (Q : S → S → ℝ) (ν : S → ℝ) (M : ℝ) (μ : S → ℝ) : Prop :=
  ∀ s', μ s' = ∑ s, μ s * Q s s' + M * ν s'

/-- A solution with no entry and a strictly substochastic `Q` is zero. -/
theorem hr_stationary_zero {Q : S → S → ℝ} (hQ0 : ∀ s s', 0 ≤ Q s s') {q : ℝ} (hq : q < 1)
    (hQq : ∀ s, ∑ s', Q s s' ≤ q) {d : S → ℝ} (hd : ∀ s', d s' = ∑ s, d s * Q s s') :
    d = 0 := by
  have habs : ∀ s', |d s'| ≤ ∑ s, |d s| * Q s s' := fun s' => by
    rw [hd s']
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun s _ => by rw [abs_mul, abs_of_nonneg (hQ0 s s')]
  have hsum : ∑ s', |d s'| ≤ q * ∑ s, |d s| := by
    calc ∑ s', |d s'| ≤ ∑ s', ∑ s, |d s| * Q s s' := Finset.sum_le_sum fun s' _ => habs s'
      _ = ∑ s, |d s| * ∑ s', Q s s' := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
      _ ≤ ∑ s, |d s| * q := Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hQq s) (abs_nonneg _)
      _ = q * ∑ s, |d s| := by rw [← Finset.sum_mul, mul_comm]
  have h0 : ∑ s, |d s| = 0 := by
    have := Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) => abs_nonneg (d s)
    nlinarith
  funext s
  have := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => abs_nonneg (d s)).mp h0 s
    (Finset.mem_univ s)
  simpa using this

/-- AKMM, p. 675: **for a given entry mass the stationary distribution exists and is unique**
(survivor matrix with row sums at most `q < 1`). -/
theorem hr_stationary_existsUnique {Q : S → S → ℝ} (hQ0 : ∀ s s', 0 ≤ Q s s') {q : ℝ}
    (hq : q < 1) (hQq : ∀ s, ∑ s', Q s s' ≤ q) (ν : S → ℝ) (M : ℝ) :
    ∃! μ, HRStationary Q ν M μ := by
  let T : (S → ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun μ s' => μ s' - ∑ s, μ s * Q s s'
      map_add' := fun μ μ' => by
        funext s'; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
      map_smul' := fun c μ => by
        funext s'
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]
        ring }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    refine hr_stationary_zero hQ0 hq hQq fun s' => ?_
    have := congrFun hd s'
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    linarith
  obtain ⟨μ, hμ⟩ := (LinearMap.injective_iff_surjective.mp hinj) (fun s' => M * ν s')
  refine ⟨μ, fun s' => ?_, fun μ' hμ' => ?_⟩
  · have := congrFun hμ s'
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk] at this
    linarith
  · have h := hr_stationary_zero hQ0 hq hQq (d := μ' - μ) fun s' => by
      have h1 := hμ' s'
      have h2 := congrFun hμ s'
      simp only [T, LinearMap.coe_mk, AddHom.coe_mk] at h2
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      linarith
    exact (sub_eq_zero.mp h)

/-- The stationary distribution is nonnegative when `ν ≥ 0` and `M ≥ 0`. -/
theorem hr_stationary_nonneg {Q : S → S → ℝ} (hQ0 : ∀ s s', 0 ≤ Q s s') {q : ℝ}
    (hq : q < 1) (hQq : ∀ s, ∑ s', Q s s' ≤ q) {ν : S → ℝ} (hν : ∀ s, 0 ≤ ν s) {M : ℝ}
    (hM : 0 ≤ M) {μ : S → ℝ} (hμ : HRStationary Q ν M μ) : ∀ s, 0 ≤ μ s := by
  set n : S → ℝ := fun s => max (-μ s) 0
  have hn : ∀ s', n s' ≤ ∑ s, n s * Q s s' := fun s' => by
    refine max_le ?_ (Finset.sum_nonneg fun s _ => mul_nonneg (le_max_right _ _) (hQ0 s s'))
    rw [hμ s', neg_add]
    have h1 : -∑ s, μ s * Q s s' ≤ ∑ s, n s * Q s s' := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun s _ => by
        rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hQ0 s s')
    nlinarith [mul_nonneg hM (hν s')]
  have hsum : ∑ s', n s' ≤ q * ∑ s, n s := by
    calc ∑ s', n s' ≤ ∑ s', ∑ s, n s * Q s s' := Finset.sum_le_sum fun s' _ => hn s'
      _ = ∑ s, n s * ∑ s', Q s s' := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
      _ ≤ ∑ s, n s * q := Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hQq s) (le_max_right _ _)
      _ = q * ∑ s, n s := by rw [← Finset.sum_mul, mul_comm]
  have hn0 : ∀ s, 0 ≤ n s := fun s => le_max_right _ _
  have h0 : ∑ s, n s = 0 := by
    have := Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) => hn0 s
    nlinarith
  intro s
  have := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => hn0 s).mp h0 s (Finset.mem_univ s)
  have hle : -μ s ≤ 0 := by rw [← this]; exact le_max_left _ _
  linarith

/-- AKMM, p. 675: **the stationary distribution is linear in the entry mass**: if `μ₁` is
stationary for `M = 1`, then `Mμ₁` is stationary for `M`, and it is the only one. -/
theorem hr_stationary_linear {Q : S → S → ℝ} (hQ0 : ∀ s s', 0 ≤ Q s s') {q : ℝ}
    (hq : q < 1) (hQq : ∀ s, ∑ s', Q s s' ≤ q) {ν μ1 : S → ℝ} (h1 : HRStationary Q ν 1 μ1)
    (M : ℝ) {μ : S → ℝ} (hμ : HRStationary Q ν M μ) : μ = fun s => M * μ1 s := by
  have hM : HRStationary Q ν M fun s => M * μ1 s := fun s' => by
    change M * μ1 s' = ∑ s, M * μ1 s * Q s s' + M * ν s'
    rw [h1 s']; simp only [Finset.mul_sum, mul_add]
    rw [one_mul]; congr 1; exact Finset.sum_congr rfl fun s _ => by ring
  exact (hr_stationary_existsUnique hQ0 hq hQq ν M).unique hμ hM

/-- AKMM, p. 675: labour demand, profits and firing taxes are aggregates `Σ μ(s)g(s)` of the
stationary distribution, hence `M` times their value at `M = 1`. -/
theorem hr_aggregate_linear {Q : S → S → ℝ} (hQ0 : ∀ s s', 0 ≤ Q s s') {q : ℝ}
    (hq : q < 1) (hQq : ∀ s, ∑ s', Q s s' ≤ q) {ν μ1 : S → ℝ} (h1 : HRStationary Q ν 1 μ1)
    (M : ℝ) {μ : S → ℝ} (hμ : HRStationary Q ν M μ) (g : S → ℝ) :
    ∑ s, μ s * g s = M * ∑ s, μ1 s * g s := by
  rw [hr_stationary_linear hQ0 hq hQq h1 M hμ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-! ### The labour market -/

/-- AKMM, (22.15), p. 675, with `u = log` (the calibration, p. 675): the household's condition
`w u'(wLˢ + Π + R) = χ` holds iff `Lˢ = 1/χ − (Π + R)/w` (with positive consumption). -/
theorem eq_22_15 {w χ Ls PR : ℝ} (hw : 0 < w) (hχ : 0 < χ) (hC : 0 < w * Ls + PR) :
    w * (1 / (w * Ls + PR)) = χ ↔ Ls = 1 / χ - PR / w := by
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    have e : w * Ls + PR = w / χ := by rw [h]; field_simp; ring
    rw [e]; field_simp

/-- AKMM, p. 675: **the entry mass**. With labour demand `M ℓ̂` and profits plus taxes `M ϖ̂`
(linear in `M`, `hr_aggregate_linear`), the market clears, `M ℓ̂ = 1/χ − Mϖ̂/w`, iff
`M = 1/(χ(ℓ̂ + ϖ̂/w))`: the entry mass is unique. -/
theorem hr_entry_mass {w χ lhat phat M : ℝ} (hχ : 0 < χ)
    (hpos : 0 < lhat + phat / w) :
    M * lhat = 1 / χ - M * phat / w ↔ M = 1 / (χ * (lhat + phat / w)) := by
  have e : M * phat / w = M * (phat / w) := mul_div_assoc M phat w
  rw [eq_div_iff (by positivity)]
  constructor
  · intro h
    have h2 : M * (lhat + phat / w) = 1 / χ := by rw [mul_add]; linarith
    rw [show M * (χ * (lhat + phat / w)) = χ * (M * (lhat + phat / w)) by ring, h2]
    field_simp
  · intro h
    have h2 : M * (lhat + phat / w) = 1 / χ := by
      rw [eq_div_iff hχ.ne']; linarith [show M * (χ * (lhat + phat / w)) =
        M * (lhat + phat / w) * χ by ring]
    rw [mul_add] at h2
    linarith

/-- AKMM, p. 674, footnote 11: in a steady state with constant consumption the Euler equation
`u'(C) = β(1 + r)u'(C)` gives the gross interest rate `1 + r = 1/β`. -/
theorem hr_footnote_11 {β r up : ℝ} (hβ : 0 < β) (hup : 0 < up) (h : up = β * (1 + r) * up) :
    1 + r = 1 / β := by
  have : β * (1 + r) = 1 := by
    have := mul_right_cancel₀ hup.ne' (h.symm.trans (one_mul up).symm)
    exact this
  field_simp; linarith

end AKMM.HeterogeneousFirms
