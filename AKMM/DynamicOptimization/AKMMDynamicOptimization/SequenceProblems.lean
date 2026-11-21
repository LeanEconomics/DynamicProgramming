/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases

/-!
# A dynamic optimization problem

AKMM, §4.1, pp. 94–99. The reduced-form finite-horizon problem
`max Σ_{t=0}^{T} βᵗ F(x_t, x_{t+1})` with `x_{t+1} ∈ Γ(x_t)` and `x₀` given, the
consumption–saving problem (P2) and the planning problem (4.3) of the neoclassical growth model
(NGM).

* `seq_weierstrass` (p. 95, the Weierstrass argument): with `F` continuous and
  `Γ(x) = [x̲, γ(x)]`, `γ` continuous and `x̲ ≤ γ`, the finite-horizon problem has a maximizer.
  The proof works in the product space `ℕ → ℝ`, where the feasible plans form a closed subset
  of a product of compact intervals (Tychonoff).
* `seq_weierstrass_counterexample`: the book's condition (iii), that each `Γ(x)` is nonempty,
  closed and bounded, is not enough; with `Γ` not continuous the supremum need not be attained.
* (P2): `Γ(a) = [a̲, w + (1 + r)a]` encodes `c ≥ 0` and `a' ≥ a̲` (`cs_gamma_iff`).
* (4.1)–(4.2) (`eq_4_2`), the NGM's `Γ(k) = [0, f(k) + (1 − δ)k]` (`ngm_gamma_iff`) and the
  resource constraint holding with equality at an optimum (`ngm_resource_binds`).

Departure: the book derives continuity of the reduced return `F` from continuity of `F̂` and of
`h`, strictly monotone in `y`; here `F` is assumed continuous.
-/

namespace AKMM.DynamicOptimization

open Filter Topology

/-- AKMM, p. 100: the finite-horizon objective `Σ_{t=0}^{T} βᵗ F(x_t, x_{t+1})`. -/
noncomputable def objective (F : ℝ → ℝ → ℝ) (β : ℝ) (x : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (T + 1), β ^ t * F (x t) (x (t + 1))

/-- AKMM, (P1), p. 94: a plan feasible from `x₀` up to the horizon `T`. -/
def FeasibleT (Γ : ℝ → Set ℝ) (x0 : ℝ) (T : ℕ) (x : ℕ → ℝ) : Prop :=
  x 0 = x0 ∧ ∀ t ≤ T, x (t + 1) ∈ Γ (x t)

/-- The objective only depends on `x_0, …, x_{T+1}`. -/
theorem seq_objective_congr {F : ℝ → ℝ → ℝ} {β : ℝ} {x y : ℕ → ℝ} {T : ℕ}
    (h : ∀ t ≤ T + 1, x t = y t) : objective F β x T = objective F β y T := by
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  rw [h t (by omega), h (t + 1) (by omega)]

/-- **The Weierstrass argument** (AKMM, p. 95). If `F` is continuous, `Γ(x) = [x̲, γ(x)]` with
`γ` continuous and `x̲ ≤ γ(x)`, then the finite-horizon problem (P1) has a maximizer. -/
theorem seq_weierstrass {F : ℝ → ℝ → ℝ} (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    {γ : ℝ → ℝ} (hγ : Continuous γ) {lo : ℝ} (hlo : ∀ x, lo ≤ γ x) (β x0 : ℝ) (T : ℕ) :
    ∃ xs, FeasibleT (fun x => Set.Icc lo (γ x)) x0 T xs ∧
      ∀ x, FeasibleT (fun x => Set.Icc lo (γ x)) x0 T x →
        objective F β x T ≤ objective F β xs T := by
  set m := min x0 lo
  -- upper bounds for each coordinate
  let ub : ℕ → ℝ := fun t => Nat.rec (max x0 lo)
    (fun _ b => max lo (sSup (γ '' Set.Icc m b))) t
  have hub0 : ub 0 = max x0 lo := rfl
  have hubs : ∀ t, ub (t + 1) = max lo (sSup (γ '' Set.Icc m (ub t))) := fun _ => rfl
  set S : Set (ℕ → ℝ) := {x | x 0 = x0 ∧ (∀ t ≤ T, lo ≤ x (t + 1) ∧ x (t + 1) ≤ γ (x t)) ∧
    ∀ t, T < t → x (t + 1) = lo} with hS
  have hbound : ∀ x ∈ S, ∀ t, x t ∈ Set.Icc m (ub t) := by
    intro x hx t
    induction t with
    | zero => rw [hx.1, hub0]; exact ⟨min_le_left _ _, le_max_left _ _⟩
    | succ t ih =>
      rw [hubs]
      have hbdd : BddAbove (γ '' Set.Icc m (ub t)) :=
        (isCompact_Icc.image hγ).bddAbove
      by_cases ht : t ≤ T
      · obtain ⟨h1, h2⟩ := hx.2.1 t ht
        refine ⟨(min_le_right _ _).trans h1, le_max_of_le_right (h2.trans ?_)⟩
        exact le_csSup hbdd ⟨x t, ih, rfl⟩
      · rw [hx.2.2 t (by omega)]
        exact ⟨min_le_right _ _, le_max_left _ _⟩
  have hclosed : IsClosed S := by
    have e : S = {x : ℕ → ℝ | x 0 = x0} ∩
        ((⋂ t ∈ Set.Iic T, {x : ℕ → ℝ | lo ≤ x (t + 1)} ∩ {x | x (t + 1) ≤ γ (x t)}) ∩
          ⋂ t ∈ Set.Ioi T, {x : ℕ → ℝ | x (t + 1) = lo}) := by
      ext x
      simp only [hS, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_Iic,
        Set.mem_Ioi]
    rw [e]
    refine (isClosed_eq (continuous_apply 0) continuous_const).inter
      ((isClosed_biInter fun t _ => ?_).inter (isClosed_biInter fun t _ => ?_))
    · exact (isClosed_le continuous_const (continuous_apply (t + 1))).inter
        (isClosed_le (continuous_apply (t + 1)) (hγ.comp (continuous_apply t)))
    · exact isClosed_eq (continuous_apply (t + 1)) continuous_const
  have hcompact : IsCompact S :=
    (isCompact_univ_pi fun t => isCompact_Icc (a := m) (b := ub t)).of_isClosed_subset
      hclosed fun x hx => Set.mem_univ_pi.2 fun t => hbound x hx t
  have hne : S.Nonempty := by
    refine ⟨fun t => if t = 0 then x0 else lo, by simp, fun t _ => ?_, fun t _ => by simp⟩
    simp only [Nat.add_one_ne_zero, ↓reduceIte, le_refl, true_and]
    split_ifs
    · exact hlo x0
    · exact hlo lo
  have hcont : Continuous fun x : ℕ → ℝ => objective F β x T :=
    continuous_finsetSum _ fun t _ => continuous_const.mul
      (by exact hF.comp ((continuous_apply t : Continuous fun x : ℕ → ℝ => x t).prodMk
        (continuous_apply (t + 1) : Continuous fun x : ℕ → ℝ => x (t + 1))))
  obtain ⟨xs, hxs, hmax⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
  refine ⟨xs, ⟨hxs.1, fun t ht => hxs.2.1 t ht⟩, fun x hx => ?_⟩
  set x' : ℕ → ℝ := fun t => if t ≤ T + 1 then x t else lo
  have hx' : x' ∈ S := by
    refine ⟨by simp [x', hx.1], fun t ht => ?_, fun t ht => ?_⟩
    · have h := hx.2 t ht
      simp only [x', show t + 1 ≤ T + 1 by omega, show t ≤ T + 1 by omega, ↓reduceIte]
      exact h
    · simp only [x', show ¬ t + 1 ≤ T + 1 by omega, ↓reduceIte]
  rw [seq_objective_congr (y := x') fun t ht => by simp [x', ht]]
  exact hmax hx'

/-- The constraint correspondence of the counterexample: `Γ(0) = [0, 1]`, `Γ(x) = [0, x]` for
`0 < x < 1`, and `Γ(x) = {0}` otherwise. -/
def seqCounterGamma (x : ℝ) : Set ℝ :=
  if x = 0 then Set.Icc 0 1 else if 0 < x ∧ x < 1 then Set.Icc 0 x else {0}

/-- AKMM, p. 95, condition (iii) is not sufficient. With `F(x, x') = x'`, `T = 1`, `x₀ = 0` and
`seqCounterGamma` (nonempty, closed and bounded at every `x`, but not continuous at `1`), the
objective `x₁ + βx₂` has supremum `1 + β` and no maximizer. -/
theorem seq_weierstrass_counterexample {β : ℝ} (hβ : 0 < β) :
    (∀ x, (seqCounterGamma x).Nonempty ∧ IsClosed (seqCounterGamma x) ∧
      Bornology.IsBounded (seqCounterGamma x)) ∧
    (∀ x, FeasibleT seqCounterGamma 0 1 x → objective (fun _ y => y) β x 1 < 1 + β) ∧
    ¬ ∃ xs, FeasibleT seqCounterGamma 0 1 xs ∧ ∀ x, FeasibleT seqCounterGamma 0 1 x →
      objective (fun _ y => y) β x 1 ≤ objective (fun _ y => y) β xs 1 := by
  have hobj : ∀ x : ℕ → ℝ, objective (fun _ y => y) β x 1 = x 1 + β * x 2 := by
    intro x; simp [objective, Finset.sum_range_succ]
  have hlt : ∀ x, FeasibleT seqCounterGamma 0 1 x → objective (fun _ y => y) β x 1 < 1 + β := by
    intro x hx
    rw [hobj]
    have h1 : x 1 ∈ seqCounterGamma (x 0) := hx.2 0 (by norm_num)
    have h2 : x 2 ∈ seqCounterGamma (x 1) := hx.2 1 le_rfl
    rw [hx.1] at h1
    simp only [seqCounterGamma, ↓reduceIte, Set.mem_Icc] at h1
    simp only [seqCounterGamma] at h2
    split_ifs at h2 with ha hb
    · rw [ha]; nlinarith [h2.2]
    · nlinarith [h2.2, hb.2]
    · rw [Set.mem_singleton_iff] at h2
      rw [h2]
      have : x 1 ≤ 1 := h1.2
      nlinarith
  refine ⟨fun x => ?_, hlt, fun ⟨xs, hxs, hmax⟩ => ?_⟩
  · simp only [seqCounterGamma]
    split_ifs
    · exact ⟨⟨0, by norm_num⟩, isClosed_Icc, Metric.isBounded_Icc 0 1⟩
    · exact ⟨⟨0, by simp; linarith⟩, isClosed_Icc, Metric.isBounded_Icc 0 x⟩
    · exact ⟨Set.singleton_nonempty 0, isClosed_singleton, Bornology.isBounded_singleton⟩
  · set v := objective (fun _ y => y) β xs 1
    have hv := hlt xs hxs
    set s := max (1 / 2) ((1 + v / (1 + β)) / 2)
    have hq : v / (1 + β) < 1 := by rw [div_lt_one (by linarith)]; exact hv
    have hs1 : s < 1 := max_lt (by norm_num) (by linarith)
    have hs0 : 0 < s := lt_max_of_lt_left (by norm_num)
    have hsv : v < (1 + β) * s := by
      have : v / (1 + β) < s := lt_max_of_lt_right (by linarith)
      rwa [div_lt_iff₀ (by linarith), mul_comm] at this
    set x : ℕ → ℝ := fun t => if t = 0 then 0 else s
    have hx : FeasibleT seqCounterGamma 0 1 x := by
      refine ⟨rfl, fun t ht => ?_⟩
      interval_cases t
      · simpa [x, seqCounterGamma] using And.intro hs0.le hs1.le
      · simp [x, seqCounterGamma, hs0.ne', hs0, hs1, hs0.le]
    have := hmax x hx
    rw [hobj x] at this
    simp only [x, one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero] at this
    linarith

/-- AKMM, §4.1.1, p. 97: in (P2) the feasible set `Γ(a) = [a̲, w + (1 + r)a]` says exactly that
consumption `c = w + (1 + r)a − a'` is nonnegative and the borrowing limit `a' ≥ a̲` holds. -/
theorem cs_gamma_iff {w r a alo a' : ℝ} :
    a' ∈ Set.Icc alo (w + (1 + r) * a) ↔ 0 ≤ w + (1 + r) * a - a' ∧ alo ≤ a' := by
  rw [Set.mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- AKMM, (4.1)–(4.2), p. 98: the law of motion `k_{t+1} = (1 − δ)k_t + i_t` and the resource
constraint `c_t + i_t ≤ f(k_t)` give `c_t + k_{t+1} ≤ f(k_t) + (1 − δ)k_t`. -/
theorem eq_4_2 {f : ℝ → ℝ} {δ : ℝ} {c i k : ℕ → ℝ} (hk : ∀ t, k (t + 1) = (1 - δ) * k t + i t)
    (hres : ∀ t, c t + i t ≤ f (k t)) (t : ℕ) : c t + k (t + 1) ≤ f (k t) + (1 - δ) * k t := by
  rw [hk t]; linarith [hres t]

/-- AKMM, p. 99: in the NGM, `Γ(k) = [0, f(k) + (1 − δ)k]` says exactly that `k' ≥ 0` and
consumption `c = f(k) + (1 − δ)k − k'` is nonnegative. -/
theorem ngm_gamma_iff {f : ℝ → ℝ} {δ k k' : ℝ} :
    k' ∈ Set.Icc 0 (f k + (1 - δ) * k) ↔ 0 ≤ k' ∧ 0 ≤ f k + (1 - δ) * k - k' := by
  rw [Set.mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- AKMM, p. 98: "because we assume strictly positive marginal utility of consumption, the
resource constraint always holds with equality". If `u` is strictly increasing, `β > 0`, and a
feasible allocation of (4.3) leaves resources unused at some `s ≤ T`, then consuming them gives a
feasible allocation with strictly higher welfare. -/
theorem ngm_resource_binds {u f : ℝ → ℝ} {β δ : ℝ} (hβ : 0 < β) (hu : StrictMonoOn u (Set.Ici 0))
    {T s : ℕ} (hsT : s ≤ T) {c k : ℕ → ℝ} (hc : ∀ t, 0 ≤ c t)
    (hslack : c s + k (s + 1) < f (k s) + (1 - δ) * k s) :
    ∃ c' : ℕ → ℝ, (∀ t, 0 ≤ c' t) ∧
      (∀ t, c t + k (t + 1) ≤ f (k t) + (1 - δ) * k t →
        c' t + k (t + 1) ≤ f (k t) + (1 - δ) * k t) ∧
      ∑ t ∈ Finset.range (T + 1), β ^ t * u (c t) <
        ∑ t ∈ Finset.range (T + 1), β ^ t * u (c' t) := by
  set e := f (k s) + (1 - δ) * k s - k (s + 1)
  refine ⟨Function.update c s e, fun t => ?_, fun t ht => ?_, ?_⟩
  · rcases eq_or_ne t s with rfl | h
    · simp only [Function.update_self]; linarith [hc t]
    · rw [Function.update_of_ne h]; exact hc t
  · rcases eq_or_ne t s with rfl | h
    · simp only [Function.update_self, e]; linarith
    · rw [Function.update_of_ne h]; exact ht
  · have hs : s ∈ Finset.range (T + 1) := Finset.mem_range.2 (by omega)
    rw [← Finset.add_sum_erase _ _ hs, ← Finset.add_sum_erase _ _ hs]
    have hrest : ∑ t ∈ (Finset.range (T + 1)).erase s, β ^ t * u (Function.update c s e t) =
        ∑ t ∈ (Finset.range (T + 1)).erase s, β ^ t * u (c t) :=
      Finset.sum_congr rfl fun t ht => by rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
    rw [hrest, Function.update_self]
    have hlt : u (c s) < u e := hu (Set.mem_Ici.2 (hc s)) (Set.mem_Ici.2 (by linarith [hc s]))
      (by simp only [e]; linarith)
    have := mul_lt_mul_of_pos_left hlt (pow_pos hβ s)
    linarith

end AKMM.DynamicOptimization
