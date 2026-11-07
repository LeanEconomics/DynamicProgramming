/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The Contraction Mapping Theorem and Blackwell's conditions

Copied from `RecursiveMethods/StochasticDP` (modules `Contraction`, `BoundedReturns` and
`BoundedMonotone`), with the namespace renamed and the names prefixed `br_`.

Tools for Miao, §§7.2–7.3, pp. 204–211 ("the powerful Contraction Mapping Theorem", the
Blackwell Theorem and the Closed Subspace Theorem; SLP Theorems 3.2, 3.3 and Corollary 1 of
Theorem 3.2).

* `br_IsContraction`, `br_theorem_3_2` (**Contraction Mapping Theorem**: a contraction of a
  complete metric space has exactly one fixed point `v`, and `ρ(Tⁿv₀, v) ≤ βⁿρ(v₀, v)`).
* `br_corollary_1` (**Closed Subspace Theorem**): the fixed point lies in every nonempty closed
  `S′` with `T(S′) ⊆ S′`, and in every `S″` with `T(S′) ⊆ S″`.
* `br_blackwell` (**Blackwell's sufficient conditions**, SLP Theorem 3.3) on the bounded
  continuous functions on a topological space.
* `br_isClosed_comb`: sets of bounded continuous functions cut out by inequalities
  `c f(a) + d f(b) ≤ f(e)` are closed (used for the sets of monotone and concave functions).
-/

open Filter Topology BoundedContinuousFunction

namespace Miao.InfiniteHorizonDP

variable {S : Type*} [MetricSpace S]

/-- `T` is a contraction with modulus `β ∈ (0, 1)` (SLP p. 50). -/
def br_IsContraction (T : S → S) (β : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧ ∀ x y, dist (T x) (T y) ≤ β * dist x y

/-- A contraction is uniformly continuous (SLP Ex 3.8). -/
theorem br_IsContraction.uniformContinuous {T : S → S} {β : ℝ} (hT : br_IsContraction T β) :
    UniformContinuous T :=
  Metric.uniformContinuous_iff.2 fun ε hε => ⟨ε, hε, fun {x y} h =>
    lt_of_le_of_lt (hT.2.2 x y) (by
      calc β * dist x y ≤ 1 * dist x y := mul_le_mul_of_nonneg_right hT.2.1.le dist_nonneg
        _ < ε := by rw [one_mul]; exact h)⟩

/-- SLP (1), p. 51: `ρ(v_{n+1}, v_n) ≤ βⁿ ρ(v₁, v₀)`. -/
theorem br_dist_iterate_succ_le {T : S → S} {β : ℝ} (hT : br_IsContraction T β) (v₀ : S)
    (n : ℕ) : dist (T^[n + 1] v₀) (T^[n] v₀) ≤ β ^ n * dist (T v₀) v₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    calc dist (T^[n + 1 + 1] v₀) (T^[n + 1] v₀) = dist (T (T^[n + 1] v₀)) (T (T^[n] v₀)) := by
          rw [Function.iterate_succ_apply' T (n + 1), Function.iterate_succ_apply' T n]
      _ ≤ β * dist (T^[n + 1] v₀) (T^[n] v₀) := hT.2.2 _ _
      _ ≤ β * (β ^ n * dist (T v₀) v₀) := mul_le_mul_of_nonneg_left ih hT.1.le
      _ = β * β ^ n * dist (T v₀) v₀ := by ring

/-- SLP (2), p. 51: `ρ(v_m, v_n) ≤ βⁿ/(1 − β) ρ(v₁, v₀)` for `m ≥ n`. -/
theorem br_dist_iterate_le {T : S → S} {β : ℝ} (hT : br_IsContraction T β) (v₀ : S) {m n : ℕ}
    (hmn : n ≤ m) : dist (T^[m] v₀) (T^[n] v₀) ≤ β ^ n / (1 - β) * dist (T v₀) v₀ := by
  have h1β : 0 < 1 - β := sub_pos.2 hT.2.1
  have key : ∀ j, dist (T^[n + j] v₀) (T^[n] v₀) ≤
      β ^ n * (1 - β ^ j) / (1 - β) * dist (T v₀) v₀ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h := br_dist_iterate_succ_le hT v₀ (n + j)
      have htri := dist_triangle (T^[n + (j + 1)] v₀) (T^[n + j] v₀) (T^[n] v₀)
      rw [← add_assoc] at htri ⊢
      have e : β ^ n * (1 - β ^ (j + 1)) / (1 - β) =
          β ^ n * (1 - β ^ j) / (1 - β) + β ^ (n + j) := by
        field_simp
        ring
      rw [e, add_mul]
      linarith
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine (key j).trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
  have := pow_nonneg hT.1.le j
  rw [div_le_div_iff_of_pos_right h1β]
  nlinarith [pow_nonneg hT.1.le n]

/-- The successive approximations `vₙ = Tⁿv₀` form a Cauchy sequence. -/
theorem br_cauchySeq_iterate {T : S → S} {β : ℝ} (hT : br_IsContraction T β) (v₀ : S) :
    CauchySeq fun n => T^[n] v₀ := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hlim : Tendsto (fun n => β ^ n / (1 - β) * dist (T v₀) v₀) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hT.1.le hT.2.1).div_const (1 - β)).mul_const
      (dist (T v₀) v₀)
    simpa using this
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  exact ⟨N, fun n hn => (br_dist_iterate_le hT v₀ hn).trans_lt (hN N le_rfl)⟩

/-- **The Contraction Mapping Theorem** (SLP Theorem 3.2). If `(S, ρ)` is complete and nonempty
and `T` is a contraction with modulus `β`, then `T` has exactly one fixed point `v`, and
`ρ(Tⁿv₀, v) ≤ βⁿρ(v₀, v)` for every `v₀`. -/
theorem br_theorem_3_2 [CompleteSpace S] [Nonempty S] {T : S → S} {β : ℝ}
    (hT : br_IsContraction T β) :
    ∃ v, T v = v ∧ (∀ w, T w = w → w = v) ∧
      ∀ v₀ (n : ℕ), dist (T^[n] v₀) v ≤ β ^ n * dist v₀ v := by
  obtain ⟨v₀⟩ : Nonempty S := inferInstance
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete (br_cauchySeq_iterate hT v₀)
  have hfix : T v = v := by
    have h1 : Tendsto (fun n => T (T^[n] v₀)) atTop (𝓝 (T v)) :=
      (hT.uniformContinuous.continuous.tendsto v).comp hv
    have h2 : Tendsto (fun n => T (T^[n] v₀)) atTop (𝓝 v) := by
      have := hv.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, Function.iterate_succ_apply'] using this
    exact tendsto_nhds_unique h1 h2
  have huniq : ∀ w, T w = w → w = v := fun w hw => by
    by_contra hne
    have hpos : 0 < dist w v := dist_pos.2 hne
    have := hT.2.2 w v
    rw [hw, hfix] at this
    nlinarith [hT.2.1]
  refine ⟨v, hfix, huniq, fun v₁ n => ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    calc dist (T (T^[n] v₁)) v = dist (T (T^[n] v₁)) (T v) := by rw [hfix]
      _ ≤ β * dist (T^[n] v₁) v := hT.2.2 _ _
      _ ≤ β * (β ^ n * dist v₁ v) := mul_le_mul_of_nonneg_left ih hT.1.le
      _ = β * β ^ n * dist v₁ v := by ring

/-- **The Closed Subspace Theorem** (SLP Corollary 1 of Theorem 3.2). The fixed point of a
contraction lies in every nonempty closed set `S′` with `T(S′) ⊆ S′`, and in every `S″` with
`T(S′) ⊆ S″`. -/
theorem br_corollary_1 {T : S → S} {β : ℝ} (hT : br_IsContraction T β) {v : S} (hv : T v = v)
    {S' S'' : Set S} (hne : S'.Nonempty) (hclosed : IsClosed S') (hmaps : Set.MapsTo T S' S')
    (hS'' : Set.MapsTo T S' S'') : v ∈ S' ∧ v ∈ S'' := by
  obtain ⟨v₀, hv₀⟩ := hne
  have hmem : ∀ n, T^[n] v₀ ∈ S' := fun n => hmaps.iterate n hv₀
  have hlim : Tendsto (fun n => T^[n] v₀) atTop (𝓝 v) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hrate : ∀ n, dist (T^[n] v₀) v ≤ β ^ n * dist v₀ v := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', pow_succ']
        calc dist (T (T^[n] v₀)) v = dist (T (T^[n] v₀)) (T v) := by rw [hv]
          _ ≤ β * dist (T^[n] v₀) v := hT.2.2 _ _
          _ ≤ β * (β ^ n * dist v₀ v) := mul_le_mul_of_nonneg_left ih hT.1.le
          _ = β * β ^ n * dist v₀ v := by ring
    refine squeeze_zero (fun _ => dist_nonneg) hrate ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hT.1.le hT.2.1).mul_const (dist v₀ v)
  have hvS' : v ∈ S' := hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
  refine ⟨hvS', ?_⟩
  rw [← hv]
  exact hS'' hvS'

/-- **Blackwell's sufficient conditions** (SLP Theorem 3.3) on the bounded continuous functions
on any topological space: a monotone operator that discounts is a contraction of modulus `β`. -/
theorem br_blackwell {X : Type*} [TopologicalSpace X] {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)} {β : ℝ}
    (hβ : 0 ≤ β) (hmono : ∀ f g, f ≤ g → T f ≤ T g)
    (hdisc : ∀ f a, 0 ≤ a → T (f + const X a) ≤ T f + const X (β * a)) (f g : X →ᵇ ℝ) :
    dist (T f) (T g) ≤ β * dist f g := by
  have hle : ∀ f g : X →ᵇ ℝ, f ≤ g + const X (dist f g) := fun f g x => by
    change f x ≤ (g + const X (dist f g)) x
    rw [BoundedContinuousFunction.add_apply, const_apply]
    have := dist_coe_le_dist (f := f) (g := g) x
    rw [Real.dist_eq] at this
    linarith [le_abs_self (f x - g x)]
  have h1 : ∀ f g : X →ᵇ ℝ, ∀ x, T f x ≤ T g x + β * dist f g := fun f g x => by
    have : T f x ≤ (T g + const X (β * dist f g)) x :=
      (hmono _ _ (hle f g)).trans (hdisc g _ dist_nonneg) x
    rwa [BoundedContinuousFunction.add_apply, const_apply] at this
  refine (dist_le (mul_nonneg hβ dist_nonneg)).2 fun x => ?_
  rw [Real.dist_eq, abs_le]
  have a := h1 f g x
  have b := h1 g f x
  rw [dist_comm] at b
  constructor <;> linarith

/-- Sets of bounded continuous functions cut out by inequalities `c f(a) + d f(b) ≤ f(e)`
(each imposed under a condition `p`) are closed. -/
theorem br_isClosed_comb {X ι : Type*} [TopologicalSpace X] (p : ι → Prop) (c d : ι → ℝ)
    (a b e : ι → X) :
    IsClosed {f : X →ᵇ ℝ | ∀ i, p i → c i * f (a i) + d i * f (b i) ≤ f (e i)} := by
  have : {f : X →ᵇ ℝ | ∀ i, p i → c i * f (a i) + d i * f (b i) ≤ f (e i)} =
      ⋂ i, {f : X →ᵇ ℝ | p i → c i * f (a i) + d i * f (b i) ≤ f (e i)} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [this]
  refine isClosed_iInter fun i => ?_
  by_cases hp : p i
  · simp only [hp, true_imp_iff]
    exact isClosed_le (((continuous_eval_const (a i)).const_mul (c i)).add
      ((continuous_eval_const (b i)).const_mul (d i))) (continuous_eval_const (e i))
  · simp only [hp, false_imp_iff, Set.ofPred_true]
    exact isClosed_univ

end Miao.InfiniteHorizonDP
