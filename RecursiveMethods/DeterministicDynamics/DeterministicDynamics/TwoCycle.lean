/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.CobbDouglasConcave

/-!
# The cyclical example: optimal two-cycles

SLP Exercise 6.7e, p. 158. The sequence problem is `max Σ βᵗF(k_t, k_{t+1})` with
`F(k, y) = k^a(1 − y)^b` and `k_t ∈ [0, 1]` (`cdΓ`). A two-cycle `(x, y)`, `x ≠ y`, is the plan
`x, y, x, y, …` (`cyc`).

* **Exercise 6.7e** (`ex_6_7e`): for `x, y ∈ (0, 1)`, the two-cycle is optimal from `k₀ = x` iff
  `F_y(x, y) + βF_x(y, x) = 0` and `F_y(y, x) + βF_x(x, y) = 0`.
  * Sufficiency is Theorem 4.15's argument (`euler_sufficient`): `F` is concave on `[0, 1]²` and
    the boundary terms are at most a constant times `βᵗ⁺¹`.
  * Necessity moves a single `k_t` and leaves the rest of the plan alone; only two terms of the
    sum change, so their sum is maximized at the cycle, and its derivative vanishes there.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

variable {a b β : ℝ}

/-- `Γ(k) = [0, 1]` for `k ∈ [0, 1]` (and empty off `[0, 1]`). -/
def cdΓ (k : ℝ) : Set ℝ := {y | k ∈ Icc (0 : ℝ) 1 ∧ y ∈ Icc (0 : ℝ) 1}

/-- The two-cycle `x, y, x, y, …`. -/
def cyc (x y : ℝ) (t : ℕ) : ℝ := if Even t then x else y

theorem cyc_succ (x y : ℝ) (t : ℕ) : cyc x y (t + 1) = cyc y x t := by
  simp only [cyc, Nat.even_add_one]
  split_ifs <;> rfl

theorem cdF_mem (ha : 0 < a) (hb : 0 < b) {k y : ℝ} (hk : k ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ cdF a b k y ∧ cdF a b k y ≤ 1 := by
  have h1 : 0 ≤ k ^ a := Real.rpow_nonneg hk.1 _
  have h2 : k ^ a ≤ 1 := Real.rpow_le_one hk.1 hk.2 ha.le
  have h3 : 0 ≤ (1 - y) ^ b := Real.rpow_nonneg (by linarith [hy.2]) _
  have h4 : (1 - y) ^ b ≤ 1 := Real.rpow_le_one (by linarith [hy.2]) (by linarith [hy.1]) hb.le
  exact ⟨mul_nonneg h1 h3, by unfold cdF; nlinarith⟩

theorem feasible_mem {x₀ : ℝ} {p : ℕ → ℝ} (hp : p ∈ Feasible cdΓ x₀) (t : ℕ) :
    p t ∈ Icc (0 : ℝ) 1 := by
  cases t with
  | zero => have := (hp.2 0).1; rwa [hp.1] at this ⊢
  | succ t => exact (hp.2 t).2

/-- Partial sums along a feasible plan converge to the (real) sum of the series. -/
theorem summable_plan (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x₀ : ℝ}
    {p : ℕ → ℝ} (hp : p ∈ Feasible cdΓ x₀) :
    Summable fun t => β ^ t * cdF a b (p t) (p (t + 1)) := by
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ0 t)
    (cdF_mem ha hb (feasible_mem hp t) (feasible_mem hp (t + 1))).1) (fun t => ?_)
    (summable_geometric_of_lt_one hβ0 hβ1)
  have := (cdF_mem ha hb (feasible_mem hp t) (feasible_mem hp (t + 1))).2
  have := pow_nonneg hβ0 t
  nlinarith

theorem tendsto_partialSum (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x₀ : ℝ}
    {p : ℕ → ℝ} (hp : p ∈ Feasible cdΓ x₀) :
    Tendsto (fun n => partialSum (fun k y => cdF a b k y) β p n) atTop
      (𝓝 (∑' t, β ^ t * cdF a b (p t) (p (t + 1)))) := by
  simp only [partialSum]
  exact (summable_plan ha hb hβ0 hβ1 hp).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem cd_assumption42 (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Assumption42 cdΓ (fun k y => cdF a b k y) β := fun _ _ hp =>
  ⟨_, EReal.tendsto_coe.2 (tendsto_partialSum ha hb hβ0 hβ1 hp)⟩

theorem total_eq (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x₀ : ℝ} {p : ℕ → ℝ}
    (hp : p ∈ Feasible cdΓ x₀) :
    total (fun k y => cdF a b k y) β p = ((∑' t, β ^ t * cdF a b (p t) (p (t + 1)) : ℝ) : EReal) :=
  tendsto_nhds_unique (tendsto_total (cd_assumption42 ha hb hβ0 hβ1) hp)
    (EReal.tendsto_coe.2 (tendsto_partialSum ha hb hβ0 hβ1 hp))

theorem cyc_mem {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (t : ℕ) :
    cyc x y t ∈ Icc (0 : ℝ) 1 := by
  unfold cyc; split_ifs <;> assumption

theorem cyc_feasible {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    cyc x y ∈ Feasible cdΓ x :=
  ⟨by simp [cyc], fun t => ⟨cyc_mem hx hy t, cyc_mem hx hy (t + 1)⟩⟩

/-- The derivative of `F` at `(k_t, k_{t+1})` along the cycle. -/
noncomputable def cycD (a b x y : ℝ) (t : ℕ) : ℝ × ℝ →L[ℝ] ℝ :=
  cdFx a b (cyc x y t) (cyc x y (t + 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    cdFy a b (cyc x y t) (cyc x y (t + 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- **Exercise 6.7e (sufficiency).** A two-cycle in `(0, 1)` satisfying both Euler equations is
optimal from `x`. -/
theorem cyc_sufficient (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (h1 : cdFy a b x y + β * cdFx a b y x = 0) (h2 : cdFy a b y x + β * cdFx a b x y = 0) :
    total (fun k y => cdF a b k y) β (cyc x y) = vstar cdΓ (fun k y => cdF a b k y) β x := by
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hyI : y ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hy
  have hpos : ∀ t, cyc x y t ∈ Ioo (0 : ℝ) 1 := fun t => by unfold cyc; split_ifs <;> assumption
  refine euler_sufficient (F := fun p : ℝ × ℝ => cdF a b p.1 p.2) (cd_assumption42 ha hb hβ0 hβ1)
    (cyc_feasible hxI hyI) (cycD a b x y) (fun t x' y' hy' => ?_) (fun t v => ?_) hβ0
    (fun x' hx' _ => ?_)
  · -- `F` lies below its tangent plane on `[0, 1]²`
    exact concave_le_fderiv (cd_concave ha hb hab)
      (show (cyc x y t, cyc x y (t + 1)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from
        ⟨cyc_mem hxI hyI t, cyc_mem hxI hyI (t + 1)⟩)
      (show (x', y') ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from ⟨hy'.1, hy'.2⟩)
      (hasFDerivAt_cd (hpos t).1 (hpos (t + 1)).2)
  · -- the Euler equations along the cycle
    simp only [Fy, Fx, cycD, _root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero,
      add_zero, zero_add]
    rw [cyc_succ, cyc_succ, cyc_succ y x]
    unfold cyc
    split_ifs
    · linear_combination v * h1
    · linear_combination v * h2
  · -- the boundary terms are at most `βᵀ⁺¹(|F_x(x, y)| + |F_x(y, x)|)`
    set C := |cdFx a b x y| + |cdFx a b y x|
    refine ⟨fun T => β ^ (T + 1) * C, ?_, fun T => ?_⟩
    · simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).comp
        (tendsto_add_atTop_nat 1)).mul_const C
    · simp only [Fx, cycD, _root_.add_apply, _root_.smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero,
        add_zero]
      have hd : |cyc x y (T + 1) - x' (T + 1)| ≤ 1 := by
        have h1' := cyc_mem hxI hyI (T + 1)
        have h2' := feasible_mem hx' (T + 1)
        rw [abs_le]; constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
      have hc : |cdFx a b (cyc x y (T + 1)) (cyc x y (T + 1 + 1))| ≤ C := by
        have e : cyc x y (T + 1 + 1) = cyc x y T := by rw [cyc_succ, cyc_succ]
        rw [e, cyc_succ]
        unfold cyc
        split_ifs <;> simp only [C] <;>
          linarith [abs_nonneg (cdFx a b x y), abs_nonneg (cdFx a b y x)]
      have hb' := pow_nonneg hβ0 (T + 1)
      calc β ^ (T + 1) * (cdFx a b (cyc x y (T + 1)) (cyc x y (T + 1 + 1)) *
            (cyc x y (T + 1) - x' (T + 1)))
          ≤ β ^ (T + 1) * |cdFx a b (cyc x y (T + 1)) (cyc x y (T + 1 + 1)) *
            (cyc x y (T + 1) - x' (T + 1))| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hb'
        _ ≤ β ^ (T + 1) * (C * 1) := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (mul_le_mul hc hd (abs_nonneg _)
              (le_trans (abs_nonneg _) hc)) hb'
        _ = β ^ (T + 1) * C := by ring

/-- Changing a feasible plan at the single date `j + 1` changes the value by the two affected
terms. -/
theorem sum_update (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x₀ : ℝ}
    {p : ℕ → ℝ} (hp : p ∈ Feasible cdΓ x₀) (j : ℕ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    Function.update p (j + 1) z ∈ Feasible cdΓ x₀ ∧
      ∑' t, β ^ t * cdF a b (Function.update p (j + 1) z t)
          (Function.update p (j + 1) z (t + 1)) =
        ∑' t, β ^ t * cdF a b (p t) (p (t + 1)) +
          (β ^ j * (cdF a b (p j) z - cdF a b (p j) (p (j + 1))) +
            β ^ (j + 1) * (cdF a b z (p (j + 2)) - cdF a b (p (j + 1)) (p (j + 2)))) := by
  set p' := Function.update p (j + 1) z
  have hmem : ∀ t, p' t ∈ Icc (0 : ℝ) 1 := fun t => by
    simp only [p', Function.update_apply]
    split_ifs
    · exact hz
    · exact feasible_mem hp t
  have hp' : p' ∈ Feasible cdΓ x₀ := ⟨by simp [p', hp.1], fun t => ⟨hmem t, hmem (t + 1)⟩⟩
  refine ⟨hp', ?_⟩
  have hs := summable_plan ha hb hβ0 hβ1 hp
  have hs' := summable_plan (a := a) (b := b) ha hb hβ0 hβ1 hp'
  rw [← sub_eq_iff_eq_add', ← hs'.tsum_sub hs]
  rw [tsum_eq_sum (s := {j, j + 1}) fun t ht => ?_]
  · rw [Finset.sum_pair (by omega)]
    simp only [p', Function.update_self, Function.update_of_ne (show j ≠ j + 1 by omega),
      Function.update_of_ne (show j + 1 + 1 ≠ j + 1 by omega)]
    ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp only [p', Function.update_of_ne (show t ≠ j + 1 from ht.2),
      Function.update_of_ne (show t + 1 ≠ j + 1 by omega), sub_self]

/-- **Exercise 6.7e (necessity).** An optimal two-cycle in `(0, 1)` satisfies both Euler
equations. -/
theorem cyc_necessary (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β) (hβ1 : β < 1) {x y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hopt : total (fun k y => cdF a b k y) β (cyc x y) = vstar cdΓ (fun k y => cdF a b k y) β x) :
    cdFy a b x y + β * cdFx a b y x = 0 ∧ cdFy a b y x + β * cdFx a b x y = 0 := by
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hyI : y ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hy
  have hfeas := cyc_feasible hxI hyI
  -- the change at date `j + 1` is never positive
  have hle : ∀ j : ℕ, ∀ z ∈ Icc (0 : ℝ) 1,
      β ^ j * (cdF a b (cyc x y j) z - cdF a b (cyc x y j) (cyc x y (j + 1))) +
        β ^ (j + 1) * (cdF a b z (cyc x y (j + 2)) - cdF a b (cyc x y (j + 1)) (cyc x y (j + 2)))
        ≤ 0 := by
    intro j z hz
    obtain ⟨hp', hsum⟩ := sum_update ha hb hβ0.le hβ1 hfeas j hz
    have h1 : total (fun k y => cdF a b k y) β (Function.update (cyc x y) (j + 1) z) ≤
        vstar cdΓ (fun k y => cdF a b k y) β x := le_biSup (total (fun k y => cdF a b k y) β) hp'
    rw [← hopt, total_eq ha hb hβ0.le hβ1 hp', total_eq ha hb hβ0.le hβ1 hfeas, hsum,
      EReal.coe_le_coe_iff] at h1
    linarith
  have hc0 : cyc x y 0 = x := by simp [cyc]
  have hc1 : cyc x y 1 = y := by simp [cyc]
  have hc2 : cyc x y 2 = x := by simp [cyc]
  have hc3 : cyc x y 3 = y := by simp [cyc, Nat.even_iff]
  -- Fermat's theorem in the moved coordinate
  have fermat : ∀ u v : ℝ, u ∈ Ioo (0 : ℝ) 1 → v ∈ Ioo (0 : ℝ) 1 →
      (∀ z ∈ Icc (0 : ℝ) 1, cdF a b u z + β * cdF a b z u ≤ cdF a b u v + β * cdF a b v u) →
      cdFy a b u v + β * cdFx a b v u = 0 := fun u v hu hv hmax => by
    have hd : HasDerivAt (fun z => cdF a b u z + β * cdF a b z u)
        (cdFy a b u v + β * cdFx a b v u) v :=
      (hasDerivAt_cdF_y u hv.2).add ((hasDerivAt_cdF_k hv.1 u).const_mul β)
    refine IsLocalMax.hasDerivAt_eq_zero ?_ hd
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with z hz
    exact hmax z (Ioo_subset_Icc_self hz)
  refine ⟨fermat x y hx hy fun z hz => ?_, fermat y x hy hx fun z hz => ?_⟩
  · have := hle 0 z hz
    rw [hc0, hc1, hc2] at this
    simp only [pow_zero, one_mul, zero_add, pow_one] at this
    linarith
  · have := hle 1 z hz
    rw [hc1, show (1 + 1 : ℕ) = 2 from rfl, hc2, show (1 + 2 : ℕ) = 3 from rfl, hc3] at this
    have h2 : β * (cdF a b y z - cdF a b y x + β * (cdF a b z y - cdF a b x y)) ≤ 0 := by
      simp only [pow_one, pow_two] at this
      linarith
    have := nonpos_of_mul_nonpos_right h2 hβ0
    linarith

/-- **Exercise 6.7e.** For `x, y ∈ (0, 1)`, the two-cycle `(x, y)` is optimal from `k₀ = x` iff
`F_y(x, y) + βF_x(y, x) = 0` and `F_y(y, x) + βF_x(x, y) = 0`. -/
theorem ex_6_7e (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    total (fun k y => cdF a b k y) β (cyc x y) = vstar cdΓ (fun k y => cdF a b k y) β x ↔
      cdFy a b x y + β * cdFx a b y x = 0 ∧ cdFy a b y x + β * cdFx a b x y = 0 :=
  ⟨cyc_necessary ha hb hβ0 hβ1 hx hy, fun h =>
    cyc_sufficient ha hb hab hβ0.le hβ1 hx hy h.1 h.2⟩

end StokeyLucasPrescott.DeterministicDynamics
