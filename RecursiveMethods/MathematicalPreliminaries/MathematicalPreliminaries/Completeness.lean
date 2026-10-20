/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MathematicalPreliminaries.NormedSpaces
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Completeness

SLP §3.1, pp. 46–49: Theorem 3.1 and Exercise 3.6.

* `theorem_3_1`: the bounded continuous functions `C(X)` on a topological space, with the sup
  norm, are complete; the proof follows the book's three steps (pointwise limit, uniform
  convergence, the limit bounded and continuous).
* `isCompleteFor_of_completeSpace`: Mathlib's completeness of a metric space is the book's.
* Ex 3.6a, complete: `isComplete_int`, `isComplete_discrete` (3.3a–b), `isComplete_euclid`,
  `isComplete_max`, `isComplete_sum` (3.4a–c), `isComplete_ellInf` (3.4d), `isComplete_sup`
  (3.4e), `isComplete_sup_monotone` (3.3c with "nondecreasing").
* Ex 3.6a, not complete: `not_isComplete_sup_strictMono` (3.3c), `not_isComplete_l1_strictMono`
  (3.3d), `not_isComplete_rat` (3.3e), `not_isComplete_l1` (3.4f).
* `IsClosedFor`, `isComplete_subset` (Ex 3.6b): a closed subset of a complete space is complete.
-/

open Set Filter Topology Finset BoundedContinuousFunction

namespace StokeyLucasPrescott.MathematicalPreliminaries

/-! ### Theorem 3.1 -/

/-- **Theorem 3.1.** The space of bounded continuous real functions on a topological space, with the
sup norm, is complete: every Cauchy sequence converges. -/
theorem theorem_3_1 {X : Type*} [TopologicalSpace X] (f : ℕ → X →ᵇ ℝ) (hf : CauchySeq f) :
    ∃ g : X →ᵇ ℝ, Tendsto f atTop (𝓝 g) := by
  rw [Metric.cauchySeq_iff] at hf
  -- Step 1: the candidate, the pointwise limit
  have hpt : ∀ x, CauchySeq fun n => f n x := fun x => Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hf ε hε
    exact ⟨N, fun m hm n hn => (dist_coe_le_dist x).trans_lt (hN m hm n hn)⟩
  choose g0 hg0 using fun x => cauchySeq_tendsto_of_complete (hpt x)
  -- Step 2: uniform convergence
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, dist (f n x) (g0 x) ≤ ε := fun ε hε => by
    obtain ⟨N, hN⟩ := hf ε hε
    refine ⟨N, fun n hn x => ?_⟩
    have hlim : Tendsto (fun m => dist (f n x) (f m x)) atTop (𝓝 (dist (f n x) (g0 x))) :=
      tendsto_const_nhds.dist (hg0 x)
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
    exact ((dist_coe_le_dist x).trans (hN n hn m hm).le)
  -- Step 3: the limit is continuous and bounded
  have hcont : Continuous g0 := by
    refine TendstoUniformly.continuous (F := fun n x => f n x) ?_
      (Frequently.of_forall (f := atTop) fun n => (f n).continuous)
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun n hn x => ?_⟩
    rw [dist_comm]
    exact (hN n hn x).trans_lt (half_lt_self hε)
  obtain ⟨N₁, hN₁⟩ := hunif 1 one_pos
  have hbdd : ∀ x, ‖g0 x‖ ≤ ‖f N₁‖ + 1 := fun x => by
    have h1 := hN₁ N₁ le_rfl x
    have h2 := (f N₁).norm_coe_le_norm x
    rw [Real.dist_eq] at h1
    rw [Real.norm_eq_abs] at h2 ⊢
    have := abs_sub_abs_le_abs_sub (g0 x) (f N₁ x)
    rw [abs_sub_comm] at h1
    linarith
  refine ⟨ofNormedAddCommGroup g0 hcont _ hbdd, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  exact (dist_le (half_pos hε).le).2 fun x => hN n hn x

/-- Mathlib's completeness of a metric space is completeness in the book's sense. -/
theorem isCompleteFor_of_completeSpace {E : Type*} [MetricSpace E] [CompleteSpace E] :
    IsCompleteFor (dist : E → E → ℝ) := fun x hx => by
  have hc : CauchySeq x := Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hx ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn⟩
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨l, fun ε hε => (Metric.tendsto_atTop.1 hl ε hε)⟩

/-! ### Exercise 3.6a: complete spaces -/

/-- An integer- or discrete-valued Cauchy sequence is eventually constant. -/
theorem isComplete_of_eventually_const {S : Type*} {ρ : S → S → ℝ} (hρ : IsMetric ρ)
    (hsep : ∀ x y, ρ x y < 1 / 2 → x = y) : IsCompleteFor ρ := fun x hx => by
  obtain ⟨N, hN⟩ := hx (1 / 2) (by norm_num)
  refine ⟨x N, fun ε hε => ⟨N, fun n hn => ?_⟩⟩
  rw [hsep _ _ (hN n hn N le_rfl), hρ.self]
  exact hε

/-- **Ex 3.6a (Ex 3.3a).** The integers are complete. -/
theorem isComplete_int : IsCompleteFor fun x y : ℤ => |(x : ℝ) - y| :=
  isComplete_of_eventually_const isMetric_int fun x y h => by
    by_contra hne
    have : (1 : ℝ) ≤ |(x : ℝ) - y| := by
      have h1 : (1 : ℤ) ≤ |x - y| := Int.one_le_abs (sub_ne_zero.2 hne)
      exact_mod_cast h1
    linarith

/-- **Ex 3.6a (Ex 3.3b).** A discrete metric space is complete. -/
theorem isComplete_discrete (T : Type*) [DecidableEq T] :
    IsCompleteFor fun x y : T => if x = y then (0 : ℝ) else 1 :=
  isComplete_of_eventually_const (isMetric_discrete T) fun x y h => by
    by_contra hne
    simp [hne] at h
    linarith

/-- A norm on `ℝ^l` bounded above and below by multiples of the max norm is complete. -/
theorem isComplete_of_equiv_max {l : ℕ} {N : (Fin l → ℝ) → ℝ} {c C : ℝ} (hc : 0 < c)
    (hlow : ∀ x, c * ‖x‖ ≤ N x) (hup : ∀ x, N x ≤ C * ‖x‖) :
    IsCompleteFor fun x y => N (x - y) := fun x hx => by
  have hcs : CauchySeq x := Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨M, hM⟩ := hx (c * ε) (mul_pos hc hε)
    refine ⟨M, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have := (hlow (x m - x n)).trans_lt (hM m hm n hn)
    exact lt_of_mul_lt_mul_left this hc.le
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨L, fun ε hε => ?_⟩
  have hC : 0 < |C| + 1 := by positivity
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hL (ε / (|C| + 1)) (div_pos hε hC)
  refine ⟨M, fun n hn => ?_⟩
  have h1 := hM n hn
  rw [dist_eq_norm] at h1
  calc N (x n - L) ≤ C * ‖x n - L‖ := hup _
    _ ≤ (|C| + 1) * ‖x n - L‖ := mul_le_mul_of_nonneg_right (by linarith [le_abs_self C])
          (norm_nonneg _)
    _ < (|C| + 1) * (ε / (|C| + 1)) := mul_lt_mul_of_pos_left h1 hC
    _ = ε := by field_simp

theorem sum_abs_le_card_mul_max {l : ℕ} (x : Fin l → ℝ) : ∑ i, |x i| ≤ l * ‖x‖ := by
  calc ∑ i, |x i| ≤ ∑ _i : Fin l, ‖x‖ := sum_le_sum fun i _ => abs_le_max_norm x i
    _ = l * ‖x‖ := by simp

theorem max_le_sum_abs {l : ℕ} (x : Fin l → ℝ) : ‖x‖ ≤ ∑ i, |x i| :=
  max_norm_le x (sum_nonneg fun _ _ => abs_nonneg _) fun i =>
    single_le_sum (f := fun i => |x i|) (fun _ _ => abs_nonneg _) (mem_univ i)

/-- **Ex 3.6a (Ex 3.4c).** `ℝ^l` with the sum norm is complete. -/
theorem isComplete_sum (l : ℕ) : IsCompleteFor fun x y : Fin l → ℝ => ∑ i, |(x - y) i| :=
  isComplete_of_equiv_max one_pos (fun x => by rw [one_mul]; exact max_le_sum_abs x)
    sum_abs_le_card_mul_max

/-- **Ex 3.6a (Ex 3.4b).** `ℝ^l` with the max norm is complete. -/
theorem isComplete_max (l : ℕ) : IsCompleteFor fun x y : Fin l → ℝ => ‖x - y‖ :=
  isComplete_of_equiv_max one_pos (fun x => by rw [one_mul]) (fun x => by rw [one_mul])

/-- **Ex 3.6a (Ex 3.4a).** `ℝ^l` with the Euclidean norm is complete. -/
theorem isComplete_euclid (l : ℕ) :
    IsCompleteFor fun x y : Fin l → ℝ => Real.sqrt (∑ i, (x - y) i ^ 2) := by
  refine isComplete_of_equiv_max (N := fun x : Fin l → ℝ => Real.sqrt (∑ i, x i ^ 2)) (C := l)
    one_pos (fun x => ?_) (fun x => ?_)
  · rw [one_mul]
    refine max_norm_le x (Real.sqrt_nonneg _) fun i => ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (single_le_sum (f := fun i => x i ^ 2) (fun _ _ => sq_nonneg _)
      (mem_univ i))
  · refine le_trans ?_ (sum_abs_le_card_mul_max x)
    rw [Real.sqrt_le_left (sum_nonneg fun _ _ => abs_nonneg _)]
    calc ∑ i, x i ^ 2 = ∑ i, |x i| ^ 2 := by simp
      _ ≤ (∑ i, |x i|) ^ 2 := sum_sq_le_sq_sum_of_nonneg fun _ _ => abs_nonneg _

/-- **Ex 3.6a (Ex 3.4d).** `ℓ∞` is complete. -/
theorem isComplete_ellInf : IsCompleteFor fun x y : ellInf => supNorm (x - y) := fun x hx => by
  -- pointwise limits
  have hpt : ∀ k, CauchySeq fun n => (x n : ℕ → ℝ) k := fun k =>
    Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hx ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    exact (abs_le_supNorm (x m - x n) k).trans_lt (hN m hm n hn)
  choose L hL using fun k => cauchySeq_tendsto_of_complete (hpt k)
  -- uniform convergence
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k, |(x n : ℕ → ℝ) k - L k| ≤ ε := fun ε hε => by
    obtain ⟨N, hN⟩ := hx ε hε
    refine ⟨N, fun n hn k => le_of_tendsto ((tendsto_const_nhds.sub (hL k)).abs)
      (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)⟩
    exact (abs_le_supNorm (x n - x m) k).trans (hN n hn m hm).le
  -- the limit is bounded
  obtain ⟨N₁, hN₁⟩ := hunif 1 one_pos
  have hLb : L ∈ ellInf := ⟨supNorm (x N₁) + 1, by
    rintro _ ⟨k, rfl⟩
    have h1 := hN₁ N₁ le_rfl k
    have h2 := abs_le_supNorm (x N₁) k
    have := abs_sub_abs_le_abs_sub (L k) ((x N₁ : ℕ → ℝ) k)
    rw [abs_sub_comm] at h1
    simp only
    linarith⟩
  refine ⟨⟨L, hLb⟩, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  exact ⟨N, fun n hn => (supNorm_le _ fun k => hN n hn k).trans_lt (half_lt_self hε)⟩

/-- **Ex 3.6a (Ex 3.4e).** `C[a, b]` with the sup norm is complete. -/
theorem isComplete_sup (a b : ℝ) : IsCompleteFor fun x y : C(Icc a b, ℝ) => ‖x - y‖ := by
  have h : (fun x y : C(Icc a b, ℝ) => ‖x - y‖) = dist := by
    funext x y
    rw [dist_eq_norm]
  rw [h]
  exact isCompleteFor_of_completeSpace

/-! ### Exercise 3.6b -/

/-- A subset is closed when it contains the limits of its convergent sequences. -/
def IsClosedFor {S : Type*} (ρ : S → S → ℝ) (V : Set S) : Prop :=
  ∀ (x : ℕ → S) (l : S), (∀ n, x n ∈ V) → Converges ρ x l → l ∈ V

/-- **Ex 3.6b.** A closed subset of a complete metric space is complete. -/
theorem isComplete_subset {S : Type*} {ρ : S → S → ℝ} (hc : IsCompleteFor ρ) {V : Set S}
    (hV : IsClosedFor ρ V) : IsCompleteFor fun x y : V => ρ x y := fun x hx => by
  obtain ⟨l, hl⟩ := hc (fun n => x n) hx
  exact ⟨⟨l, hV _ l (fun n => (x n).2) hl⟩, hl⟩

/-- **Ex 3.6a (Ex 3.3c with "nondecreasing").** The continuous nondecreasing functions on `[a, b]`
with the sup metric are complete. -/
theorem isComplete_sup_monotone (a b : ℝ) :
    IsCompleteFor fun x y : {x : C(Icc a b, ℝ) // Monotone x} => ‖x.1 - y.1‖ := by
  refine isComplete_subset (isComplete_sup a b) fun x l hx hl s t hst => ?_
  have hpt : ∀ u, Tendsto (fun n => x n u) atTop (𝓝 (l u)) := fun u => by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hl ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have := (x n - l).norm_coe_le_norm u
    simp only [ContinuousMap.sub_apply] at this
    exact this.trans_lt (hN n hn)
  exact le_of_tendsto_of_tendsto (hpt s) (hpt t) (Eventually.of_forall fun n => hx n hst)

/-! ### Exercise 3.6a: spaces that are not complete -/

variable {a b : ℝ}

/-- The ramps `x_n(t) = (t − a)/(n + 1)`: strictly increasing, shrinking to `0`. -/
noncomputable def ramp (a b : ℝ) (n : ℕ) : C(Icc a b, ℝ) :=
  ⟨fun t => ((t : ℝ) - a) / (n + 1), by fun_prop⟩

theorem ramp_strictMono (n : ℕ) : StrictMono (ramp a b n) := fun s t hst => by
  simp only [ramp, ContinuousMap.coe_mk]
  have : (s : ℝ) < t := hst
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

theorem norm_ramp_le (hab : a ≤ b) (n : ℕ) : ‖ramp a b n‖ ≤ (b - a) / (n + 1) := by
  have : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  refine (ContinuousMap.norm_le_of_nonempty _).2 fun t => ?_
  simp only [ramp, ContinuousMap.coe_mk, Real.norm_eq_abs]
  rw [abs_of_nonneg (div_nonneg (by linarith [t.2.1]) (by positivity))]
  exact div_le_div_of_nonneg_right (by linarith [t.2.2]) (by positivity)

theorem norm_ramp_tendsto (hab : a ≤ b) : Tendsto (fun n => ‖ramp a b n‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => norm_nonneg _) (norm_ramp_le hab) ?_
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a)
  rw [mul_zero] at h
  exact h.congr fun n => by rw [mul_one_div]

/-- A sequence whose sizes tend to `0` is Cauchy for any norm-like `N`. -/
theorem isCauchy_of_tendsto_zero {E : Type*} [AddCommGroup E] [Module ℝ E] {N : E → ℝ}
    (hN : IsNorm N) {x : ℕ → E} (hx : Tendsto (fun n => N (x n)) atTop (𝓝 0)) :
    IsCauchy (fun u v => N (u - v)) x := fun ε hε => by
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hx (ε / 2) (half_pos hε)
  refine ⟨M, fun n hn m hm => ?_⟩
  have h1 := hM n hn
  have h2 := hM m hm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hN.nonneg _)] at h1 h2
  have := hN.triangle (x n) (-x m)
  rw [← sub_eq_add_neg, show N (-x m) = N (x m) by
    rw [show -x m = (-1 : ℝ) • x m by simp, hN.smul]; simp] at this
  linarith

/-- **Ex 3.6a (Ex 3.3c).** The continuous strictly increasing functions with the sup metric are not
complete (`a < b`). -/
theorem not_isComplete_sup_strictMono (hab : a < b) :
    ¬ IsCompleteFor fun x y : StrictIncr a b => ‖x.1 - y.1‖ := by
  intro hc
  set x : ℕ → StrictIncr a b := fun n => ⟨ramp a b n, ramp_strictMono n⟩
  obtain ⟨l, hl⟩ := hc x (isCauchy_of_tendsto_zero (isNorm_sup a b) (norm_ramp_tendsto hab.le))
  -- the limit is `0`, which is not strictly increasing
  have hl0 : l.1 = 0 := by
    rw [← norm_eq_zero]
    refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
    obtain ⟨N₁, hN₁⟩ := hl (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (norm_ramp_tendsto hab.le) (ε / 2) (half_pos hε)
    have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
    have h2 := hN₂ (max N₁ N₂) (le_max_right _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h2
    have := norm_sub_le (x (max N₁ N₂)).1 ((x (max N₁ N₂)).1 - l.1)
    rw [sub_sub_cancel] at this
    linarith
  have := l.2 (show (⟨a, le_rfl, hab.le⟩ : Icc a b) < ⟨b, hab.le, le_rfl⟩ from hab)
  rw [hl0] at this
  simp at this

/-- **Ex 3.6a (Ex 3.3d).** The continuous strictly increasing functions with the `L¹` metric are not
complete (`a < b`). -/
theorem not_isComplete_l1_strictMono (hab : a < b) :
    ¬ IsCompleteFor fun x y : StrictIncr a b => l1 hab.le (x.1 - y.1) := by
  intro hc
  set x : ℕ → StrictIncr a b := fun n => ⟨ramp a b n, ramp_strictMono n⟩
  have hl1 : Tendsto (fun n => l1 hab.le (ramp a b n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => l1_nonneg _ _) (fun n => l1_le_norm hab.le _) ?_
    simpa using (norm_ramp_tendsto hab.le).const_mul (b - a)
  obtain ⟨l, hl⟩ := hc x (isCauchy_of_tendsto_zero (isNorm_l1 hab) hl1)
  have hl0 : l.1 = 0 := by
    rw [← l1_eq_zero_iff hab]
    refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (l1_nonneg _ _)
    obtain ⟨N₁, hN₁⟩ := hl (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hl1 (ε / 2) (half_pos hε)
    have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
    have h2 := hN₂ (max N₁ N₂) (le_max_right _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (l1_nonneg _ _)] at h2
    have := l1_add_le hab.le (-(x (max N₁ N₂)).1) ((x (max N₁ N₂)).1 - l.1)
    rw [show -(x (max N₁ N₂)).1 + ((x (max N₁ N₂)).1 - l.1) = -l.1 by abel, l1_neg] at this
    have h4 : l1 hab.le (-(x (max N₁ N₂)).1) = l1 hab.le (ramp a b (max N₁ N₂)) := l1_neg _ _
    simp only at h1
    linarith
  have := l.2 (show (⟨a, le_rfl, hab.le⟩ : Icc a b) < ⟨b, hab.le, le_rfl⟩ from hab)
  rw [hl0] at this
  simp at this

/-- **Ex 3.6a (Ex 3.3e).** The rationals are not complete: rational approximations of `√2` form a
Cauchy sequence with no rational limit. -/
theorem not_isComplete_rat : ¬ IsCompleteFor fun x y : ℚ => |(x : ℝ) - y| := by
  intro hc
  have hq : ∀ n : ℕ, ∃ q : ℚ, |(q : ℝ) - Real.sqrt 2| < 1 / (n + 1) := fun n => by
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show Real.sqrt 2 < Real.sqrt 2 + 1 / (n + 1) by
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith)
    refine ⟨q, ?_⟩
    rw [abs_of_pos (by linarith)]
    linarith
  choose q hq using hq
  have hlim : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (Real.sqrt 2)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact (hq n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hcauchy : IsCauchy (fun x y : ℚ => |(x : ℝ) - y|) q := fun ε hε => by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
    exact ⟨N, fun n hn m hm => by simpa [Real.dist_eq] using hN n hn m hm⟩
  obtain ⟨r, hr⟩ := hc q hcauchy
  have hlim' : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (r : ℝ)) :=
    Metric.tendsto_atTop.2 fun ε hε => by
      obtain ⟨N, hN⟩ := hr ε hε
      exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact hN n hn⟩
  have := tendsto_nhds_unique hlim hlim'
  exact irrational_sqrt_two ⟨r, this.symm⟩

end StokeyLucasPrescott.MathematicalPreliminaries
