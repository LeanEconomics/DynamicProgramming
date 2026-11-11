import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import DeterministicDynamics.GrowthStability
import DeterministicDP.EulerEquations
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import EulerTransversality.GrowthModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import DeterministicDP.Principle
import DeterministicDP.BoundedReturns
import DeterministicDP.Concavity
import DeterministicDP.Envelope
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two-period consumption–saving model

AKMM, §4.2.1, pp. 99–100. Endowments `w₀, w₁`, a constant interest rate `r`, no initial assets
and a borrowing constraint `a₁ ≥ 0`; `c₀ = w₀ − a₁` and `c₁ = w₁ + (1 + r)a₁`.

* The lifetime budget constraint `c₀ + c₁/(1 + r) = w₀ + w₁/(1 + r)` (`twoPeriod_lifetime_budget`).
* The Kuhn–Tucker conditions (4.4)–(4.6) are sufficient for a maximum when `u` is concave
  (`eq_4_4_to_4_6`), and with `λ = 0` they give the Euler equation
  `u'(c₀) = β(1 + r)u'(c₁)` (`twoPeriod_euler`).
* With a decreasing endowment `w₀ > w₁`, strictly decreasing marginal utility and `β(1 + r) ≥ 1`,
  the borrowing constraint does not bind at a maximum (`twoPeriod_interior`).
* When `β(1 + r) = 1`: `c₀ = c₁ = (w₀ + βw₁)/(1 + β)` and `a₁ = (w₀ − w₁)/(2 + r) > 0`
  (`twoPeriod_closed_form`, `twoPeriod_closed_form_optimal`).

The concavity tools (`tangent_le`) are imported from SLP `DeterministicDynamics`.
-/

namespace AKMM.DynamicOptimization

open Filter Topology StokeyLucasPrescott.DeterministicDynamics

/-- The two-period objective as a function of saving `a₁`:
`u(w₀ − a₁) + βu(w₁ + (1 + r)a₁)`. -/
noncomputable def twoPeriodValue (u : ℝ → ℝ) (β r w0 w1 a : ℝ) : ℝ :=
  u (w0 - a) + β * u (w1 + (1 + r) * a)

/-- AKMM, p. 99: combining `c₀ = w₀ − a₁` and `c₁ = w₁ + (1 + r)a₁` gives the lifetime budget
constraint `c₀ + c₁/(1 + r) = w₀ + w₁/(1 + r)`. -/
theorem twoPeriod_lifetime_budget {w0 w1 r a1 c0 c1 : ℝ} (hr : -1 < r) (h0 : c0 = w0 - a1)
    (h1 : c1 = w1 + (1 + r) * a1) : c0 + c1 / (1 + r) = w0 + w1 / (1 + r) := by
  have : (1 + r) ≠ 0 := by linarith
  rw [h0, h1]
  field_simp
  ring

/-- **AKMM, (4.4)–(4.6), p. 100: the Kuhn–Tucker conditions are sufficient.** Let `u` be concave
on `[0, ∞)` with derivative `u'(cᵢ)` at the candidate consumptions. If multipliers `μ` and
`λ ≥ 0` satisfy `u'(c₀) − μ − λ = 0`, `βu'(c₁) − μ/(1 + r) = 0` and `λ(w₀ − c₀) = 0` with
`w₀ − c₀ ≥ 0`, then `a₁ = w₀ − c₀` maximizes `u(w₀ − a) + βu(w₁ + (1 + r)a)` over all `a ≥ 0`
with nonnegative consumption. -/
theorem eq_4_4_to_4_6 {u : ℝ → ℝ} (hu : ConcaveOn ℝ (Set.Ici 0) u) {β r w0 w1 a1 d0 d1 μ lam : ℝ}
    (hβ : 0 ≤ β) (hr : -1 < r) (hc0 : 0 ≤ w0 - a1) (hc1 : 0 ≤ w1 + (1 + r) * a1)
    (hd0 : HasDerivAt u d0 (w0 - a1)) (hd1 : HasDerivAt u d1 (w1 + (1 + r) * a1))
    (h44 : d0 - μ - lam = 0) (h45 : β * d1 - μ / (1 + r) = 0)
    (h46 : lam * a1 = 0) (ha1 : 0 ≤ a1) (hlam : 0 ≤ lam) {a : ℝ} (ha : 0 ≤ a)
    (hca0 : 0 ≤ w0 - a) (hca1 : 0 ≤ w1 + (1 + r) * a) :
    twoPeriodValue u β r w0 w1 a ≤ twoPeriodValue u β r w0 w1 a1 := by
  have t0 := tangent_le hu (Set.mem_Ici.2 hc0) (Set.mem_Ici.2 hca0) hd0
  have t1 := tangent_le hu (Set.mem_Ici.2 hc1) (Set.mem_Ici.2 hca1) hd1
  have hr' : (0 : ℝ) < 1 + r := by linarith
  have hμ : μ = β * d1 * (1 + r) := by field_simp at h45; linarith
  unfold twoPeriodValue
  have key : β * u (w1 + (1 + r) * a) ≤
      β * u (w1 + (1 + r) * a1) + β * d1 * ((1 + r) * (a - a1)) := by
    have := mul_le_mul_of_nonneg_left t1 hβ
    nlinarith
  nlinarith [mul_nonneg hlam ha]

/-- AKMM, p. 100: with `λ = 0` (an interior solution), (4.4) and (4.5) give the Euler equation
`u'(c₀) = β(1 + r)u'(c₁)`. -/
theorem twoPeriod_euler {β r d0 d1 μ : ℝ} (hr : -1 < r) (h44 : d0 - μ - 0 = 0)
    (h45 : β * d1 - μ / (1 + r) = 0) : d0 = β * (1 + r) * d1 := by
  have : (1 + r) ≠ 0 := by linarith
  field_simp at h45
  linarith

/-- AKMM, p. 100: "a decreasing wage path `w₀ > w₁` and strictly decreasing marginal utility can
guarantee the solution to be interior when `β(1 + r) ≥ 1`". If `u' > 0` is strictly decreasing
on `(0, ∞)`, `0 < w₁ < w₀` and `β(1 + r) ≥ 1`, then `a₁ = 0` is not a maximizer over `[0, w₀]`. -/
theorem twoPeriod_interior {u u' : ℝ → ℝ} (hd : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) (hanti : StrictAntiOn u' (Set.Ioi 0)) {β r w0 w1 : ℝ}
    (hw1 : 0 < w1) (hw : w1 < w0) (hβr : 1 ≤ β * (1 + r)) :
    ∃ a, 0 < a ∧ a < w0 ∧ twoPeriodValue u β r w0 w1 0 < twoPeriodValue u β r w0 w1 a := by
  have hw0 : 0 < w0 := hw1.trans hw
  obtain ⟨D, hDdef⟩ : ∃ D, D = -u' w0 + β * (1 + r) * u' w1 := ⟨_, rfl⟩
  have hD : 0 < D := by
    rw [hDdef]
    have h1 : u' w0 < u' w1 := hanti (Set.mem_Ioi.2 hw1) (Set.mem_Ioi.2 hw0) hw
    have h2 := hpos w1 hw1
    nlinarith
  have hV : HasDerivAt (twoPeriodValue u β r w0 w1) D 0 := by
    have e0 : HasDerivAt (fun a : ℝ => w0 - a) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub w0
    have e1 : HasDerivAt (fun a : ℝ => w1 + (1 + r) * a) (1 + r) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + r)).const_add w1
    have h0 : HasDerivAt (fun a => u (w0 - a)) (u' w0 * -1) 0 := by
      have := hd w0 hw0
      exact (show HasDerivAt u (u' w0) (w0 - 0) by simpa using this).comp 0 e0
    have h1 : HasDerivAt (fun a => u (w1 + (1 + r) * a)) (u' w1 * (1 + r)) 0 := by
      have := hd w1 hw1
      exact (show HasDerivAt u (u' w1) (w1 + (1 + r) * 0) by simpa using this).comp 0 e1
    have := h0.add (h1.const_mul β)
    convert this using 1
    · funext a; simp [twoPeriodValue]
    · rw [hDdef]; ring
  have hslope := hV.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (twoPeriodValue u β r w0 w1 (0 + t) -
      twoPeriodValue u β r w0 w1 0) ∧ t < w0 := by
    refine (hslope.eventually (lt_mem_nhds hD)).and ?_
    exact nhdsWithin_le_nhds (gt_mem_nhds hw0)
  have hev' := hev.and self_mem_nhdsWithin
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := hev'.exists
  refine ⟨t, ht, h2, ?_⟩
  rw [zero_add, smul_eq_mul] at h1
  have := (pos_iff_pos_of_mul_pos h1).1 (inv_pos.2 ht)
  linarith

/-- AKMM, p. 100: when `β(1 + r) = 1`, the Euler equation with strictly decreasing marginal
utility gives `c₀ = c₁`, hence `a₁ = (w₀ − w₁)/(2 + r)` and `c₀ = c₁ = (w₀ + βw₁)/(1 + β)`; the
saving is positive exactly when `w₀ > w₁`. -/
theorem twoPeriod_closed_form {u' : ℝ → ℝ} (hinj : Set.InjOn u' (Set.Ioi 0)) {β r w0 w1 a1 : ℝ}
    (hr : -1 < r) (hβr : β * (1 + r) = 1) (hc0 : 0 < w0 - a1) (hc1 : 0 < w1 + (1 + r) * a1)
    (heuler : u' (w0 - a1) = β * (1 + r) * u' (w1 + (1 + r) * a1)) :
    w0 - a1 = w1 + (1 + r) * a1 ∧ a1 = (w0 - w1) / (2 + r) ∧
      w0 - a1 = (w0 + β * w1) / (1 + β) ∧ (0 < a1 ↔ w1 < w0) := by
  rw [hβr, one_mul] at heuler
  have he := hinj hc0 hc1 heuler
  have h2r : (2 + r) ≠ 0 := by linarith
  have ha : a1 = (w0 - w1) / (2 + r) := by field_simp; linarith
  have h1r : (1 + r) ≠ 0 := by linarith
  have hβ : β = 1 / (1 + r) := by rw [eq_div_iff h1r]; exact hβr
  refine ⟨he, ha, ?_, ?_⟩
  · have hβ0 : 0 < β := by rw [hβ]; exact div_pos one_pos (by linarith)
    have h1β : (1 + β) ≠ 0 := by linarith
    rw [ha, eq_div_iff h1β, hβ]
    field_simp
    ring
  · rw [ha, div_pos_iff_of_pos_right (by linarith), sub_pos]

/-- AKMM, p. 100: when `β(1 + r) = 1` and `w₀ ≥ w₁`, the plan `a₁ = (w₀ − w₁)/(2 + r)` with
`c₀ = c₁` is optimal for concave `u` (the Kuhn–Tucker conditions hold with `λ = 0`). -/
theorem twoPeriod_closed_form_optimal {u : ℝ → ℝ} (hu : ConcaveOn ℝ (Set.Ici 0) u) {β r w0 w1 d : ℝ}
    (hβ : 0 ≤ β) (hr : -1 < r) (hβr : β * (1 + r) = 1) (hw : w1 ≤ w0) (hw1 : 0 ≤ w1)
    (hd : HasDerivAt u d (((1 + r) * w0 + w1) / (2 + r))) {a : ℝ} (ha : 0 ≤ a)
    (hca0 : 0 ≤ w0 - a) (hca1 : 0 ≤ w1 + (1 + r) * a) :
    twoPeriodValue u β r w0 w1 a ≤ twoPeriodValue u β r w0 w1 ((w0 - w1) / (2 + r)) := by
  have h2r : (0 : ℝ) < 2 + r := by linarith
  have hc0 : w0 - (w0 - w1) / (2 + r) = ((1 + r) * w0 + w1) / (2 + r) := by
    field_simp; ring
  have hc1 : w1 + (1 + r) * ((w0 - w1) / (2 + r)) = ((1 + r) * w0 + w1) / (2 + r) := by
    field_simp; ring
  have hpos : 0 ≤ ((1 + r) * w0 + w1) / (2 + r) :=
    div_nonneg (by nlinarith) h2r.le
  refine eq_4_4_to_4_6 hu hβ hr (by rw [hc0]; exact hpos) (by rw [hc1]; exact hpos)
    (by rw [hc0]; exact hd) (by rw [hc1]; exact hd) (μ := d) (lam := 0) (by ring) ?_ (by ring)
    (div_nonneg (by linarith) h2r.le) le_rfl ha hca0 hca1
  have : (1 + r) ≠ 0 := by linarith
  field_simp
  linear_combination d * hβr

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite horizon: Result 1 and the finite-horizon neoclassical growth model

AKMM, §4.2.2–4.2.3, pp. 100–102. States are real, `Γ(x) = [x̲, γ(x)]`, and `F` has derivative
`D_t` at `(x*_t, x*_{t+1})` with partial derivatives `F₁ = D_t(1, 0)`, `F₂ = D_t(0, 1)`.

* `finite_telescope`: under the Euler equation (i) for `t < T`, the first-order terms of
  `Σ_{t≤T} βᵗ[F(x*_t, x*_{t+1}) − F(x_t, x_{t+1})]` telescope to `βᵀF₂(T)(x*_{T+1} − x_{T+1})`.
* **Result 1** (`result_1`): a concave `F` with the Euler equation (i) for `t < T` and the
  terminal condition (ii) `x*_{T+1} = x̲` gives a maximizer. The book's hypotheses that `F` is
  increasing in its first argument and that `x*` is interior are not needed; `F` decreasing in
  its second argument enters only through `F₂(T) ≤ 0` (`result_1_of_antitone`).
* The NGM return `u(f(k) + (1 − δ)k − k')` is concave in `(k, k')`, strictly when `u` and `f`
  are (fn. 4 and fn. 16; `ngm_return_concave`, `ngm_return_strictConcave`), with partial
  derivatives `u'(c)(f'(k) + 1 − δ)` and `−u'(c)` (`ngm_hasFDerivAt`).
* (P3): at a maximum `k_{T+1} = 0` ((4.8)–(4.9), `ngm_terminal_zero`); at an interior maximum the
  Euler equation (4.10) holds (`eq_4_10`, Fermat's theorem in place of the Lagrangian (4.7)); the
  Euler equation with `k_{T+1} = 0` is sufficient (`ngm_finite_sufficient`), and the solution is
  unique (`finite_unique_max`, `ngm_finite_unique`).

The tangent-plane inequality `concave_le_fderiv` is imported from SLP `DeterministicDP`.
-/

namespace AKMM.DynamicOptimization

open Filter Topology StokeyLucasPrescott.DeterministicDP

/-- A linear map on `ℝ × ℝ` in terms of its partial derivatives:
`D(a, b) = aD(1, 0) + bD(0, 1)`. -/
theorem finite_fderiv_apply (D : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    D (a, b) = a * D (1, 0) + b * D (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **The telescoping step** (AKMM, App. 4.A.3 adapted to a finite horizon). If `d₀ = 0` and the
Euler equation `F₂(t) + βF₁(t + 1) = 0` holds for `t < T`, then for `n ≤ T`
`Σ_{t≤n} βᵗD_t(d_t, d_{t+1}) = βⁿd_{n+1}F₂(n)`. -/
theorem finite_telescope (D : ℕ → ℝ × ℝ →L[ℝ] ℝ) {β : ℝ} (d : ℕ → ℝ) (hd0 : d 0 = 0) {T : ℕ}
    (heuler : ∀ t < T, D t (0, 1) + β * D (t + 1) (1, 0) = 0) :
    ∀ n ≤ T, ∑ t ∈ Finset.range (n + 1), β ^ t * D t (d t, d (t + 1)) =
      β ^ n * (d (n + 1) * D n (0, 1)) := by
  intro n hn
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, hd0]
    rw [finite_fderiv_apply]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega), finite_fderiv_apply (D (n + 1))]
    have he := heuler n (by omega)
    rw [pow_succ]
    linear_combination (β ^ n * d (n + 1)) * he

/-- **Result 1** (AKMM, p. 100). Let `F` be concave on a convex set `A` containing every pair
`(x_t, x_{t+1})` of the plans considered, with derivative `D_t` at `(x*_t, x*_{t+1})`. If `x*` is
feasible for `Γ(x) = [x̲, γ(x)]`, satisfies the Euler equation (i)
`F₂(x*_t, x*_{t+1}) + βF₁(x*_{t+1}, x*_{t+2}) = 0` for `t < T` and the terminal condition (ii)
`x*_{T+1} = x̲`, and `F₂(x*_T, x*_{T+1}) ≤ 0`, then `x*` maximizes the objective. -/
theorem result_1 {F : ℝ × ℝ → ℝ} {A : Set (ℝ × ℝ)} (hA : ConcaveOn ℝ A F) {β : ℝ} (hβ : 0 ≤ β)
    {lo : ℝ} {γ : ℝ → ℝ} {x0 : ℝ} {T : ℕ} {xs : ℕ → ℝ}
    (hxs : FeasibleT (fun x => Set.Icc lo (γ x)) x0 T xs) (hxsA : ∀ t ≤ T, (xs t, xs (t + 1)) ∈ A)
    (D : ℕ → ℝ × ℝ →L[ℝ] ℝ) (hD : ∀ t ≤ T, HasFDerivAt F (D t) (xs t, xs (t + 1)))
    (heuler : ∀ t < T, D t (0, 1) + β * D (t + 1) (1, 0) = 0) (hterm : xs (T + 1) = lo)
    (hF2 : D T (0, 1) ≤ 0) {x : ℕ → ℝ} (hx : FeasibleT (fun x => Set.Icc lo (γ x)) x0 T x)
    (hxA : ∀ t ≤ T, (x t, x (t + 1)) ∈ A) :
    objective (fun a b => F (a, b)) β x T ≤ objective (fun a b => F (a, b)) β xs T := by
  set d : ℕ → ℝ := fun t => xs t - x t
  have hd0 : d 0 = 0 := by simp [d, hxs.1, hx.1]
  have htel := finite_telescope D d hd0 heuler T le_rfl
  have hterm' : ∀ t ∈ Finset.range (T + 1), β ^ t * F (x t, x (t + 1)) ≤
      β ^ t * F (xs t, xs (t + 1)) - β ^ t * D t (d t, d (t + 1)) := fun t ht => by
    have htT : t ≤ T := by have := Finset.mem_range.1 ht; omega
    have h := concave_le_fderiv hA (hxsA t htT) (hxA t htT) (hD t htT)
    have e : D t ((x t, x (t + 1)) - (xs t, xs (t + 1))) = -D t (d t, d (t + 1)) := by
      rw [← map_neg]; congr 1; ext <;> simp [d]
    rw [e] at h
    have := mul_le_mul_of_nonneg_left h (pow_nonneg hβ t)
    linarith
  have hsum := Finset.sum_le_sum hterm'
  rw [Finset.sum_sub_distrib, htel] at hsum
  have hdT : d (T + 1) ≤ 0 := by
    have := (hx.2 T le_rfl).1
    simp only [d, hterm]; linarith
  have : 0 ≤ β ^ T * (d (T + 1) * D T (0, 1)) :=
    mul_nonneg (pow_nonneg hβ T) (mul_nonneg_of_nonpos_of_nonpos hdT hF2)
  unfold objective
  linarith

/-- AKMM, p. 100: if `F` is decreasing in its second argument then `F₂ ≤ 0`, so the last
hypothesis of `result_1` follows from the book's monotonicity assumption. -/
theorem result_1_F2_nonpos {F : ℝ × ℝ → ℝ} {a b : ℝ} {D : ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt F D (a, b)) (hdec : Antitone fun y => F (a, y)) : D (0, 1) ≤ 0 := by
  have hline : HasDerivAt (fun y : ℝ => ((a, y) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) b :=
    (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  have hcomp : HasDerivAt (fun y => F (a, y)) (D (0, 1)) b := hD.comp_hasDerivAt b hline
  rw [← hcomp.deriv]
  exact hdec.deriv_nonpos

/-- **Result 1 with the book's monotonicity hypothesis** (AKMM, p. 100): `F` decreasing in its
second argument replaces `F₂(T) ≤ 0`. -/
theorem result_1_of_antitone {F : ℝ × ℝ → ℝ} {A : Set (ℝ × ℝ)} (hA : ConcaveOn ℝ A F) {β : ℝ}
    (hβ : 0 ≤ β) (hdec : ∀ a, Antitone fun y => F (a, y)) {lo : ℝ} {γ : ℝ → ℝ} {x0 : ℝ} {T : ℕ}
    {xs : ℕ → ℝ} (hxs : FeasibleT (fun x => Set.Icc lo (γ x)) x0 T xs)
    (hxsA : ∀ t ≤ T, (xs t, xs (t + 1)) ∈ A)
    (D : ℕ → ℝ × ℝ →L[ℝ] ℝ) (hD : ∀ t ≤ T, HasFDerivAt F (D t) (xs t, xs (t + 1)))
    (heuler : ∀ t < T, D t (0, 1) + β * D (t + 1) (1, 0) = 0) (hterm : xs (T + 1) = lo)
    {x : ℕ → ℝ} (hx : FeasibleT (fun x => Set.Icc lo (γ x)) x0 T x)
    (hxA : ∀ t ≤ T, (x t, x (t + 1)) ∈ A) :
    objective (fun a b => F (a, b)) β x T ≤ objective (fun a b => F (a, b)) β xs T :=
  result_1 hA hβ hxs hxsA D hD heuler hterm (result_1_F2_nonpos (hD T le_rfl) (hdec _)) hx hxA

/-- **AKMM, fn. 4 (p. 101) and fn. 16 (p. 124): the NGM return is jointly concave.** If `u` is
concave and nondecreasing on a convex upward-closed set `S` (`[0, ∞)` or `(0, ∞)`) and
`h(k) = f(k) + (1 − δ)k` is concave on `[0, ∞)`, then `(k, k') ↦ u(h(k) − k')` is concave on
`{(k, k') : k ≥ 0, h(k) − k' ∈ S}`, which is convex. No Hessian is needed. -/
theorem ngm_return_concave {u h : ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hup : ∀ x ∈ S, ∀ y, x ≤ y → y ∈ S) (hu : ConcaveOn ℝ S u) (hmono : MonotoneOn u S)
    (hh : ConcaveOn ℝ (Set.Ici 0) h) :
    ConcaveOn ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ h p.1 - p.2 ∈ S} fun p => u (h p.1 - p.2) := by
  have hkey : ∀ p q : ℝ × ℝ, 0 ≤ p.1 → 0 ≤ q.1 → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a * (h p.1 - p.2) + b * (h q.1 - q.2) ≤ h (a * p.1 + b * q.1) - (a * p.2 + b * q.2) := by
    intro p q hp hq a b ha hb hab
    have := hh.2 (Set.mem_Ici.2 hp) (Set.mem_Ici.2 hq) ha hb hab
    simp only [smul_eq_mul] at this
    linarith
  have hconv : Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ h p.1 - p.2 ∈ S} := by
    intro p hp q hq a b ha hb hab
    refine ⟨by simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; nlinarith [hp.1, hq.1], ?_⟩
    have hin : a * (h p.1 - p.2) + b * (h q.1 - q.2) ∈ S := by
      have := hS hp.2 hq.2 ha hb hab
      simpa only [smul_eq_mul] using this
    refine hup _ hin _ ?_
    simpa only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      using hkey p q hp.1 hq.1 a b ha hb hab
  refine ⟨hconv, fun p hp q hq a b ha hb hab => ?_⟩
  have hin : a * (h p.1 - p.2) + b * (h q.1 - q.2) ∈ S := by
    have := hS hp.2 hq.2 ha hb hab
    simpa only [smul_eq_mul] using this
  have hmid := (hconv hp hq ha hb hab).2
  have h1 := hu.2 hp.2 hq.2 ha hb hab
  simp only [smul_eq_mul] at h1 ⊢
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hmid ⊢
  exact h1.trans (hmono hin hmid (hkey p q hp.1 hq.1 a b ha hb hab))

/-- **The NGM return is strictly concave** when `u` is strictly concave and strictly increasing
on `S` and `h` is strictly concave (AKMM, fn. 4, p. 101). -/
theorem ngm_return_strictConcave {u h : ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hup : ∀ x ∈ S, ∀ y, x ≤ y → y ∈ S) (hu : StrictConcaveOn ℝ S u) (hmono : StrictMonoOn u S)
    (hh : StrictConcaveOn ℝ (Set.Ici 0) h) :
    StrictConcaveOn ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ h p.1 - p.2 ∈ S} fun p => u (h p.1 - p.2) := by
  have hc := ngm_return_concave hS hup hu.concaveOn hmono.monotoneOn hh.concaveOn
  refine ⟨hc.1, fun p hp q hq hpq a b ha hb hab => ?_⟩
  have hin : a * (h p.1 - p.2) + b * (h q.1 - q.2) ∈ S := by
    have := hS hp.2 hq.2 ha.le hb.le hab
    simpa only [smul_eq_mul] using this
  have hmid := (hc.1 hp hq ha.le hb.le hab).2
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hmid ⊢
  have hweak := hh.concaveOn.2 (Set.mem_Ici.2 hp.1) (Set.mem_Ici.2 hq.1) ha.le hb.le hab
  simp only [smul_eq_mul] at hweak
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
    have hne : h p.1 - p.2 ≠ h q.1 - q.2 := by rw [h1]; intro h; exact h2 (by linarith)
    have hs := hu.2 hp.2 hq.2 hne ha hb hab
    simp only [smul_eq_mul] at hs
    refine hs.trans_le (hmono.monotoneOn hin hmid ?_)
    linarith
  · have hstrict := hh.2 (Set.mem_Ici.2 hp.1) (Set.mem_Ici.2 hq.1) h1 ha hb hab
    simp only [smul_eq_mul] at hstrict
    have hw := hu.concaveOn.2 hp.2 hq.2 ha.le hb.le hab
    simp only [smul_eq_mul] at hw
    exact hw.trans_lt (hmono hin hmid (by linarith))

/-- AKMM, pp. 101, 110: the partial derivatives of the NGM return `u(h(k) − k')`, with
`h(k) = f(k) + (1 − δ)k`, are `F₁ = u'(c)h'(k)` and `F₂ = −u'(c)`. -/
theorem ngm_hasFDerivAt {u h : ℝ → ℝ} {k k' du dh : ℝ} (hu : HasDerivAt u du (h k - k'))
    (hh : HasDerivAt h dh k) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => u (h p.1 - p.2)) D (k, k') ∧
      D (1, 0) = du * dh ∧ D (0, 1) = -du := by
  have hin := (hh.hasFDerivAt.comp (k, k')
    (hasFDerivAt_fst (𝕜 := ℝ) (p := ((k, k') : ℝ × ℝ)))).sub
    (hasFDerivAt_snd (𝕜 := ℝ) (p := ((k, k') : ℝ × ℝ)))
  have hout := hu.hasFDerivAt.comp (k, k') hin
  refine ⟨_, hout, ?_, ?_⟩ <;> simp [mul_comm]

/-- AKMM, (P3), p. 101: a capital plan feasible from `k₀` up to `T`, with
`0 ≤ k_{t+1} ≤ h(k_t) = f(k_t) + (1 − δ)k_t`. -/
abbrev NGMFeasible (h : ℝ → ℝ) (k0 : ℝ) (T : ℕ) (k : ℕ → ℝ) : Prop :=
  FeasibleT (fun k => Set.Icc 0 (h k)) k0 T k

/-- The objective of (P3), `Σ_{t≤T} βᵗu(h(k_t) − k_{t+1})`. -/
noncomputable abbrev ngmObjective (u h : ℝ → ℝ) (β : ℝ) (k : ℕ → ℝ) (T : ℕ) : ℝ :=
  objective (fun a b => u (h a - b)) β k T

/-- **AKMM, (4.8)–(4.9), p. 102: the terminal condition `k_{T+1} = 0`.** If `u` is strictly
increasing on `[0, ∞)` and `β > 0`, a maximizer of (P3) leaves no capital after `T`. -/
theorem ngm_terminal_zero {u h : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) (hu : StrictMonoOn u (Set.Ici 0))
    {k0 : ℝ} {T : ℕ} {ks : ℕ → ℝ} (hks : NGMFeasible h k0 T ks)
    (hmax : ∀ k, NGMFeasible h k0 T k → ngmObjective u h β k T ≤ ngmObjective u h β ks T) :
    ks (T + 1) = 0 := by
  by_contra hne
  have hT := hks.2 T le_rfl
  have hpos : 0 < ks (T + 1) := lt_of_le_of_ne hT.1 (Ne.symm hne)
  have hz : NGMFeasible h k0 T (Function.update ks (T + 1) 0) := by
    refine ⟨by rw [Function.update_of_ne (by omega)]; exact hks.1, fun t ht => ?_⟩
    rcases eq_or_lt_of_le ht with rfl | hlt
    · rw [Function.update_self, Function.update_of_ne (show t ≠ t + 1 by omega)]
      exact ⟨le_rfl, hT.1.trans hT.2⟩
    · rw [Function.update_of_ne (show t + 1 ≠ T + 1 by omega),
        Function.update_of_ne (show t ≠ T + 1 by omega)]
      exact hks.2 t ht
  have h1 := hmax _ hz
  simp only [ngmObjective, objective] at h1
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at h1
  have hsame : ∑ t ∈ Finset.range T, β ^ t * u (h (Function.update ks (T + 1) 0 t) -
      Function.update ks (T + 1) 0 (t + 1)) =
      ∑ t ∈ Finset.range T, β ^ t * u (h (ks t) - ks (t + 1)) :=
    Finset.sum_congr rfl fun t ht => by
      have := Finset.mem_range.1 ht
      rw [Function.update_of_ne (show t ≠ T + 1 by omega),
        Function.update_of_ne (show t + 1 ≠ T + 1 by omega)]
  rw [hsame, Function.update_self, Function.update_of_ne (show T ≠ T + 1 by omega)] at h1
  have hlt : u (h (ks T) - ks (T + 1)) < u (h (ks T) - 0) :=
    hu (Set.mem_Ici.2 (by linarith [hT.2])) (Set.mem_Ici.2 (by linarith [hT.2])) (by linarith)
  have := mul_lt_mul_of_pos_left hlt (pow_pos hβ T)
  linarith

/-- **AKMM, (4.10), p. 102: the Euler equation at an interior maximum.** If `k*` maximizes (P3)
and, at some `t < T`, `k*_{t+1} > 0` and consumption is positive at `t` and `t + 1`, then
`u'(c_t) = βu'(c_{t+1})(f'(k_{t+1}) + 1 − δ)` (here `h' = f' + 1 − δ`). This is (4.7) with
`μ_t = 0`, proved by Fermat's theorem in the direction `k_{t+1}`. -/
theorem eq_4_10 {u u' h : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) {k0 : ℝ} {T : ℕ} {ks : ℕ → ℝ}
    (hks : NGMFeasible h k0 T ks)
    (hmax : ∀ k, NGMFeasible h k0 T k → ngmObjective u h β k T ≤ ngmObjective u h β ks T)
    {t : ℕ} (ht : t < T) (hk : 0 < ks (t + 1)) (hc0 : ks (t + 1) < h (ks t))
    (hc1 : ks (t + 2) < h (ks (t + 1)))
    (hu0 : HasDerivAt u (u' (h (ks t) - ks (t + 1))) (h (ks t) - ks (t + 1)))
    (hu1 : HasDerivAt u (u' (h (ks (t + 1)) - ks (t + 2))) (h (ks (t + 1)) - ks (t + 2)))
    {dh : ℝ} (hh : HasDerivAt h dh (ks (t + 1))) :
    u' (h (ks t) - ks (t + 1)) = β * u' (h (ks (t + 1)) - ks (t + 2)) * dh := by
  set y0 := ks (t + 1)
  set g : ℝ → ℝ := fun y => β ^ t * u (h (ks t) - y) + β ^ (t + 1) * u (h y - ks (t + 2))
  have hobj : ∀ y, ngmObjective u h β (Function.update ks (t + 1) y) T =
      ngmObjective u h β ks T + (g y - g y0) := by
    intro y
    simp only [ngmObjective, objective]
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_add_of_mem t (t + 1) (Finset.mem_range.2 (by omega))
      (Finset.mem_range.2 (by omega)) (by omega)]
    · rw [Function.update_of_ne (show t ≠ t + 1 by omega), Function.update_self,
        Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega)]
      simp only [g, y0]
      ring
    · intro c _ hc
      rw [Function.update_of_ne (show c ≠ t + 1 from hc.2),
        Function.update_of_ne (show c + 1 ≠ t + 1 by omega), sub_self]
  have hloc : IsLocalMax g y0 := by
    have e1 : ∀ᶠ y in 𝓝 y0, 0 < y := lt_mem_nhds hk
    have e2 : ∀ᶠ y in 𝓝 y0, y < h (ks t) := gt_mem_nhds hc0
    have e3 : ∀ᶠ y in 𝓝 y0, ks (t + 2) < h y := hh.continuousAt.eventually (lt_mem_nhds hc1)
    filter_upwards [e1, e2, e3] with y hy1 hy2 hy3
    have hz : NGMFeasible h k0 T (Function.update ks (t + 1) y) := by
      refine ⟨by rw [Function.update_of_ne (by omega)]; exact hks.1, fun s hs => ?_⟩
      by_cases hst : s = t
      · subst hst
        rw [Function.update_self, Function.update_of_ne (show s ≠ s + 1 by omega)]
        exact ⟨hy1.le, hy2.le⟩
      by_cases hst' : s = t + 1
      · subst hst'
        rw [Function.update_self, Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega)]
        exact ⟨(hks.2 (t + 1) (by omega)).1, hy3.le⟩
      rw [Function.update_of_ne (show s + 1 ≠ t + 1 by omega), Function.update_of_ne hst']
      exact hks.2 s hs
    have := hmax _ hz
    rw [hobj] at this
    linarith
  have hg : HasDerivAt g (β ^ t * (u' (h (ks t) - y0) * -1) +
      β ^ (t + 1) * (u' (h y0 - ks (t + 2)) * dh)) y0 := by
    have i1 : HasDerivAt (fun y => h (ks t) - y) (-1) y0 := by
      simpa using (hasDerivAt_id y0).const_sub (h (ks t))
    have i2 : HasDerivAt (fun y => h y - ks (t + 2)) dh y0 := hh.sub_const _
    exact ((hu0.comp y0 i1).const_mul _).add ((hu1.comp y0 i2).const_mul _)
  have h0 := hloc.hasDerivAt_eq_zero hg
  have hbt : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have : β ^ t * (u' (h (ks t) - y0) - β * u' (h y0 - ks (t + 2)) * dh) = 0 := by
    linear_combination -h0
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hbt.ne'
  · linarith

/-- **The Euler equation and `k_{T+1} = 0` are sufficient in (P3)** (AKMM, p. 102, via
Result 1). Let `u` be concave and nondecreasing on a convex upward-closed set `S` of consumption
levels and `h = f + (1 − δ)·id` concave on `[0, ∞)`. A feasible plan with consumption in `S`,
satisfying (4.10) for `t < T` and `k_{T+1} = 0`, maximizes (P3) among feasible plans with
consumption in `S`. -/
theorem ngm_finite_sufficient {u h : ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hup : ∀ x ∈ S, ∀ y, x ≤ y → y ∈ S) (hu : ConcaveOn ℝ S u) (hmono : MonotoneOn u S)
    (hh : ConcaveOn ℝ (Set.Ici 0) h) {β : ℝ} (hβ : 0 ≤ β) {k0 : ℝ} (hk0 : 0 ≤ k0) {T : ℕ}
    {ks : ℕ → ℝ} (hks : NGMFeasible h k0 T ks) (hksS : ∀ t ≤ T, h (ks t) - ks (t + 1) ∈ S)
    {du dh : ℕ → ℝ} (hdu : ∀ t ≤ T, HasDerivAt u (du t) (h (ks t) - ks (t + 1)))
    (hdh : ∀ t ≤ T, HasDerivAt h (dh t) (ks t)) (hdu0 : 0 ≤ du T)
    (heuler : ∀ t < T, du t = β * du (t + 1) * dh (t + 1)) (hterm : ks (T + 1) = 0)
    {k : ℕ → ℝ} (hk : NGMFeasible h k0 T k) (hkS : ∀ t ≤ T, h (k t) - k (t + 1) ∈ S) :
    ngmObjective u h β k T ≤ ngmObjective u h β ks T := by
  have hex : ∀ t, ∃ D : ℝ × ℝ →L[ℝ] ℝ, t ≤ T →
      HasFDerivAt (fun p : ℝ × ℝ => u (h p.1 - p.2)) D (ks t, ks (t + 1)) ∧
        D (1, 0) = du t * dh t ∧ D (0, 1) = -du t := by
    intro t
    by_cases ht : t ≤ T
    · obtain ⟨D, hD⟩ := ngm_hasFDerivAt (hdu t ht) (hdh t ht)
      exact ⟨D, fun _ => hD⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose D hD using hex
  have hnn : ∀ x : ℕ → ℝ, NGMFeasible h k0 T x → ∀ t ≤ T, 0 ≤ x t := by
    intro x hx t ht
    rcases t with _ | t
    · rw [hx.1]; exact hk0
    · exact (hx.2 t (by omega)).1
  refine result_1 (ngm_return_concave hS hup hu hmono hh) hβ hks
    (fun t ht => ⟨hnn ks hks t ht, hksS t ht⟩) D (fun t ht => (hD t ht).1)
    (fun t ht => ?_) hterm ?_ hk (fun t ht => ⟨hnn k hk t ht, hkS t ht⟩)
  · rw [(hD t ht.le).2.2, (hD (t + 1) ht).2.1, heuler t ht]
    ring
  · rw [(hD T le_rfl).2.2]
    linarith

/-- **Uniqueness of the maximizer** (AKMM, p. 101). Let `P` be a set of plans, all starting at
`x₀`, closed under midpoints, whose pairs `(x_t, x_{t+1})`, `t ≤ T`, lie in a set `A` on which `F`
is strictly concave. If `β > 0`, two maximizers over `P` agree on `0, …, T + 1`. -/
theorem finite_unique_max {F : ℝ × ℝ → ℝ} {A : Set (ℝ × ℝ)} (hA : StrictConcaveOn ℝ A F)
    {β : ℝ} (hβ : 0 < β) {T : ℕ} {x0 : ℝ} {P : Set (ℕ → ℝ)} (hP0 : ∀ x ∈ P, x 0 = x0)
    (hPA : ∀ x ∈ P, ∀ t ≤ T, (x t, x (t + 1)) ∈ A)
    (hPmid : ∀ x ∈ P, ∀ y ∈ P, (fun t => (x t + y t) / 2) ∈ P) {xs ys : ℕ → ℝ} (hxs : xs ∈ P)
    (hys : ys ∈ P)
    (hxmax : ∀ x ∈ P, objective (fun a b => F (a, b)) β x T ≤
      objective (fun a b => F (a, b)) β xs T)
    (hymax : ∀ x ∈ P, objective (fun a b => F (a, b)) β x T ≤
      objective (fun a b => F (a, b)) β ys T) :
    ∀ t ≤ T + 1, xs t = ys t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, hne⟩ := hcon
  have hs0 : s ≠ 0 := by rintro rfl; exact hne (by rw [hP0 xs hxs, hP0 ys hys])
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  set m : ℕ → ℝ := fun t => (xs t + ys t) / 2
  have hm := hPmid xs hxs ys hys
  have hpair : ∀ r, ((m r, m (r + 1)) : ℝ × ℝ) =
      (1 / 2 : ℝ) • (xs r, xs (r + 1)) + (1 / 2 : ℝ) • (ys r, ys (r + 1)) := fun r => by
    ext <;> simp [m] <;> ring
  have hle : ∀ r ∈ Finset.range (T + 1), β ^ r * ((F (xs r, xs (r + 1)) +
      F (ys r, ys (r + 1))) / 2) ≤ β ^ r * F (m r, m (r + 1)) := fun r hr => by
    have hrT : r ≤ T := by have := Finset.mem_range.1 hr; omega
    have := hA.concaveOn.2 (hPA xs hxs r hrT) (hPA ys hys r hrT) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [← hpair] at this
    simp only [smul_eq_mul] at this
    exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hβ.le r)
  have hlt : β ^ t * ((F (xs t, xs (t + 1)) + F (ys t, ys (t + 1))) / 2) <
      β ^ t * F (m t, m (t + 1)) := by
    have hpne : ((xs t, xs (t + 1)) : ℝ × ℝ) ≠ (ys t, ys (t + 1)) := fun h =>
      hne (congrArg Prod.snd h)
    have := hA.2 (hPA xs hxs t (by omega)) (hPA ys hys t (by omega)) hpne
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    rw [← hpair] at this
    simp only [smul_eq_mul] at this
    exact mul_lt_mul_of_pos_left (by linarith) (pow_pos hβ t)
  have hsum := Finset.sum_lt_sum hle ⟨t, Finset.mem_range.2 (by omega), hlt⟩
  have havg : ∑ r ∈ Finset.range (T + 1), β ^ r * ((F (xs r, xs (r + 1)) +
      F (ys r, ys (r + 1))) / 2) = (objective (fun a b => F (a, b)) β xs T +
        objective (fun a b => F (a, b)) β ys T) / 2 := by
    unfold objective
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [havg] at hsum
  have h1 := hxmax m hm
  have h2 := hxmax ys hys
  have h3 := hymax xs hxs
  unfold objective at h1 h2 h3 hsum
  linarith

/-- **Uniqueness in (P3)** (AKMM, p. 102: "there is a unique solution to the difference equation
(4.10)"). With `u` strictly concave and strictly increasing on `S` and `h` strictly concave, two
feasible plans with consumption in `S` that satisfy (4.10) for `t < T` and `k_{T+1} = 0` agree on
`0, …, T + 1`. -/
theorem ngm_finite_unique {u h : ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hup : ∀ x ∈ S, ∀ y, x ≤ y → y ∈ S) (hu : StrictConcaveOn ℝ S u) (hmono : StrictMonoOn u S)
    (hh : StrictConcaveOn ℝ (Set.Ici 0) h) {β : ℝ} (hβ : 0 < β) {k0 : ℝ} (hk0 : 0 ≤ k0) {T : ℕ}
    {ks ks' : ℕ → ℝ} {du dh du' dh' : ℕ → ℝ}
    (hks : NGMFeasible h k0 T ks) (hksS : ∀ t ≤ T, h (ks t) - ks (t + 1) ∈ S)
    (hdu : ∀ t ≤ T, HasDerivAt u (du t) (h (ks t) - ks (t + 1)))
    (hdh : ∀ t ≤ T, HasDerivAt h (dh t) (ks t)) (hdu0 : 0 ≤ du T)
    (heuler : ∀ t < T, du t = β * du (t + 1) * dh (t + 1)) (hterm : ks (T + 1) = 0)
    (hks' : NGMFeasible h k0 T ks') (hksS' : ∀ t ≤ T, h (ks' t) - ks' (t + 1) ∈ S)
    (hdu' : ∀ t ≤ T, HasDerivAt u (du' t) (h (ks' t) - ks' (t + 1)))
    (hdh' : ∀ t ≤ T, HasDerivAt h (dh' t) (ks' t)) (hdu0' : 0 ≤ du' T)
    (heuler' : ∀ t < T, du' t = β * du' (t + 1) * dh' (t + 1)) (hterm' : ks' (T + 1) = 0) :
    ∀ t ≤ T + 1, ks t = ks' t := by
  set P : Set (ℕ → ℝ) := {k | NGMFeasible h k0 T k ∧ ∀ t ≤ T, h (k t) - k (t + 1) ∈ S}
  have hnn : ∀ x : ℕ → ℝ, NGMFeasible h k0 T x → ∀ t ≤ T, 0 ≤ x t := by
    intro x hx t ht
    rcases t with _ | t
    · rw [hx.1]; exact hk0
    · exact (hx.2 t (by omega)).1
  have hmid : ∀ x ∈ P, ∀ y ∈ P, (fun t => (x t + y t) / 2) ∈ P := by
    intro x hx y hy
    refine ⟨⟨by simp only [hx.1.1, hy.1.1]; ring, fun t ht => ?_⟩, fun t ht => ?_⟩ <;>
    · have hc := hh.concaveOn.2 (Set.mem_Ici.2 (hnn x hx.1 t ht)) (Set.mem_Ici.2 (hnn y hy.1 t ht))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hc
      have e : (1 / 2 : ℝ) * x t + 1 / 2 * y t = (x t + y t) / 2 := by ring
      rw [e] at hc
      first
      | exact ⟨by linarith [(hx.1.2 t ht).1, (hy.1.2 t ht).1],
          by linarith [(hx.1.2 t ht).2, (hy.1.2 t ht).2]⟩
      | have hin := hS (hx.2 t ht) (hy.2 t ht) (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        simp only [smul_eq_mul] at hin
        exact hup _ hin _ (by linarith)
  have hmaxP : ∀ ks₀ : ℕ → ℝ, ∀ du₀ dh₀ : ℕ → ℝ, NGMFeasible h k0 T ks₀ →
      (∀ t ≤ T, h (ks₀ t) - ks₀ (t + 1) ∈ S) →
      (∀ t ≤ T, HasDerivAt u (du₀ t) (h (ks₀ t) - ks₀ (t + 1))) →
      (∀ t ≤ T, HasDerivAt h (dh₀ t) (ks₀ t)) → 0 ≤ du₀ T →
      (∀ t < T, du₀ t = β * du₀ (t + 1) * dh₀ (t + 1)) → ks₀ (T + 1) = 0 →
      ∀ x ∈ P, ngmObjective u h β x T ≤ ngmObjective u h β ks₀ T :=
    fun ks₀ _ _ a b c d e f g x hx => ngm_finite_sufficient hS hup hu.concaveOn
      hmono.monotoneOn hh.concaveOn hβ.le hk0 a b c d e f g hx.1 hx.2
  exact finite_unique_max (ngm_return_strictConcave hS hup hu hmono hh) hβ (x0 := k0)
    (fun x hx => hx.1.1) (fun x hx t ht => ⟨hnn x hx.1 t ht, hx.2 t ht⟩) hmid
    ⟨hks, hksS⟩ ⟨hks', hksS'⟩
    (hmaxP ks du dh hks hksS hdu hdh hdu0 heuler hterm)
    (hmaxP ks' du' dh' hks' hksS' hdu' hdh' hdu0' heuler' hterm')

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Interior capital in the finite-horizon NGM

AKMM, §4.2.3, p. 102: "Given the Inada conditions, in particular `lim_{k→0} f'(k) = ∞` and
`lim_{c→0} u'(c) = ∞`, it is optimal to set `k_{t+1} > 0` for all `t < T`."

* `ngm_objective_update`: changing `k_{t+1}` alone changes the objective of (P3) only through the
  periods `t` and `t + 1`.
* `ngm_finite_interior`: under the Inada conditions every maximizer of (P3) from `k₀ > 0` has
  `k_{t+1} > 0` for `t < T`. If `k_{t+1} = 0` at the first such date, then `c_{t+1} = 0`, and
  saving a little, `ε`, more at `t` gains `β^{t+1}[u(h(ε)) − u(0)] ≥ β^{t+1}εu'(h(ε))` while losing
  at most `βᵗεu'(c_t/2)`; for small `ε` the gain wins since `u'(h(ε)) → ∞`.
-/

namespace AKMM.DynamicOptimization

open Filter Topology StokeyLucasPrescott.DeterministicDynamics

/-- Changing `k_{t+1}` to `y` changes the (P3) objective by
`βᵗ[u(h(k_t) − y) − u(h(k_t) − k_{t+1})] + β^{t+1}[u(h(y) − k_{t+2}) − u(h(k_{t+1}) − k_{t+2})]`. -/
theorem ngm_objective_update {u h : ℝ → ℝ} {β : ℝ} {T t : ℕ} (ht : t < T) (ks : ℕ → ℝ) (y : ℝ) :
    ngmObjective u h β (Function.update ks (t + 1) y) T = ngmObjective u h β ks T +
      (β ^ t * u (h (ks t) - y) + β ^ (t + 1) * u (h y - ks (t + 2)) -
        (β ^ t * u (h (ks t) - ks (t + 1)) + β ^ (t + 1) * u (h (ks (t + 1)) - ks (t + 2)))) := by
  simp only [ngmObjective, objective]
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_add_of_mem t (t + 1) (Finset.mem_range.2 (by omega))
    (Finset.mem_range.2 (by omega)) (by omega)]
  · rw [Function.update_of_ne (show t ≠ t + 1 by omega), Function.update_self,
      Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega)]
    ring
  · intro c _ hc
    rw [Function.update_of_ne (show c ≠ t + 1 from hc.2),
      Function.update_of_ne (show c + 1 ≠ t + 1 by omega), sub_self]

/-- **AKMM, p. 102: under the Inada conditions capital is positive before `T`.** Let
`h(k) = f(k) + (1 − δ)k` with `δ ≤ 1`; `f(0) = 0`, `f` concave and strictly increasing on
`[0, ∞)`, continuous at `0` from the right, with derivative `f'` on `(0, ∞)` and
`f'(k) → ∞` as `k → 0⁺`; `u` concave on `[0, ∞)` with derivative `u' > 0` on `(0, ∞)` and
`u'(c) → ∞` as `c → 0⁺`; `β > 0`. Then every maximizer of (P3) from `k₀ > 0` has
`k_{t+1} > 0` for all `t < T`. -/
theorem ngm_finite_interior {u u' f f' : ℝ → ℝ} {β δ : ℝ} (hβ : 0 < β) (hδ1 : δ ≤ 1)
    (hu : ConcaveOn ℝ (Set.Ici 0) u) (hdu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu'pos : ∀ c, 0 < c → 0 < u' c) (hinada : Tendsto u' (𝓝[>] 0) atTop) (hf0 : f 0 = 0)
    (hfc : ConcaveOn ℝ (Set.Ici 0) f) (hfmono : StrictMonoOn f (Set.Ici 0))
    (hfcont : ContinuousWithinAt f (Set.Ioi 0) 0) (hdf : ∀ k, 0 < k → HasDerivAt f (f' k) k)
    (hf'0 : Tendsto f' (𝓝[>] 0) atTop) {k0 : ℝ} (hk0 : 0 < k0) {T : ℕ} {ks : ℕ → ℝ}
    (hks : NGMFeasible (fun k => f k + (1 - δ) * k) k0 T ks)
    (hmax : ∀ k, NGMFeasible (fun k => f k + (1 - δ) * k) k0 T k →
      ngmObjective u (fun k => f k + (1 - δ) * k) β k T ≤
        ngmObjective u (fun k => f k + (1 - δ) * k) β ks T) :
    ∀ t < T, 0 < ks (t + 1) := by
  set h : ℝ → ℝ := fun k => f k + (1 - δ) * k
  have hh0 : h 0 = 0 := by simp [h, hf0]
  have hhpos : ∀ k, 0 < k → 0 < h k := fun k hk => by
    have := hfmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hk.le) hk
    simp only [h]; rw [hf0] at this; nlinarith
  by_contra hcon
  push Not at hcon
  -- the first date with `k_{t+1} = 0`
  have hex : ∃ t, t < T ∧ ks (t + 1) = 0 := by
    obtain ⟨t, ht, hle⟩ := hcon
    exact ⟨t, ht, le_antisymm hle (hks.2 t ht.le).1⟩
  classical
  let t := Nat.find hex
  have ht : t < T := (Nat.find_spec hex).1
  have hkt1 : ks (t + 1) = 0 := (Nat.find_spec hex).2
  have hkt : 0 < ks t := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · rw [h0, hks.1]; exact hk0
    · obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have hmin := Nat.find_min hex (show s < t by omega)
      have hnn := (hks.2 s (by omega)).1
      rw [hs]
      by_contra hle
      push Not at hle
      exact hmin ⟨by omega, le_antisymm hle hnn⟩
  have hkt2 : ks (t + 2) = 0 := by
    have := hks.2 (t + 1) (by omega)
    simp only [Set.mem_Icc] at this
    rw [hkt1, hh0] at this
    exact le_antisymm this.2 this.1
  set ct := h (ks t)
  have hct : 0 < ct := hhpos _ hkt
  -- `h(ε) ≥ ε` for small `ε`, since `f(ε) ≥ εf'(ε)` and `f'(ε) → ∞`
  have hhge : ∀ᶠ ε in 𝓝[>] 0, ε ≤ h ε := by
    filter_upwards [hf'0.eventually (eventually_ge_atTop δ), self_mem_nhdsWithin] with ε hε hε0
    have htan := tangent_le hfc (Set.mem_Ici.2 (le_of_lt hε0)) (Set.mem_Ici.2 le_rfl)
      (hdf ε hε0)
    rw [hf0] at htan
    have hε0' : 0 < ε := hε0
    have := mul_le_mul_of_nonneg_left hε hε0'.le
    simp only [h]
    nlinarith
  -- `h(ε) → 0⁺`, so `u'(h(ε)) → ∞`
  have hhlim : Tendsto h (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun k => f k + (1 - δ) * k) (𝓝[>] 0) (𝓝 (f 0 + (1 - δ) * 0)) :=
        hfcont.tendsto.add ((continuous_const.mul continuous_id).continuousWithinAt.tendsto)
      simpa [hf0] using this
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hhpos ε hε
  have hbig := (hinada.comp hhlim).eventually (eventually_gt_atTop (u' (ct / 2) / β))
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ct / 2 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by linarith))
  obtain ⟨ε, ⟨⟨h1, h2⟩, h3⟩, hε0⟩ :=
    (((hhge.and hbig).and hsmall).and self_mem_nhdsWithin).exists
  have hε : 0 < ε := hε0
  simp only [Function.comp_apply] at h2
  -- the perturbed plan is feasible
  have hz : NGMFeasible h k0 T (Function.update ks (t + 1) ε) := by
    refine ⟨by rw [Function.update_of_ne (by omega)]; exact hks.1, fun s hs => ?_⟩
    by_cases hst : s = t
    · rw [hst, Function.update_self, Function.update_of_ne (show t ≠ t + 1 by omega)]
      exact ⟨hε.le, by linarith⟩
    by_cases hst' : s = t + 1
    · rw [hst', Function.update_self, Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega)]
      have : ks (t + 1 + 1) = 0 := hkt2
      rw [this]
      exact ⟨le_rfl, (hhpos ε hε).le⟩
    rw [Function.update_of_ne (show s + 1 ≠ t + 1 by omega), Function.update_of_ne hst']
    exact hks.2 s hs
  have hcmp := hmax _ hz
  rw [ngm_objective_update ht, hkt1, hkt2, hh0, sub_zero, sub_zero, sub_zero] at hcmp
  -- the two tangent bounds
  have hcte : 0 < ct - ε := by linarith
  have ta := tangent_le hu (Set.mem_Ici.2 hcte.le) (Set.mem_Ici.2 hct.le) (hdu _ hcte)
  have tb := tangent_le hu (Set.mem_Ici.2 (hhpos ε hε).le) (Set.mem_Ici.2 le_rfl)
    (hdu _ (hhpos ε hε))
  have hdec : u' (ct - ε) ≤ u' (ct / 2) :=
    deriv_le_of_concave hu (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 hcte.le)
      (by linarith) (hdu _ (by linarith)) (hdu _ hcte)
  have hpos2 := hu'pos (h ε) (hhpos ε hε)
  have hbt : 0 < β ^ t := pow_pos hβ t
  -- gain `≥ βᵗε[βu'(h(ε)) − u'(c_t/2)] > 0`
  have hgain : 0 < β * (h ε * u' (h ε)) - ε * u' (ct / 2) := by
    have : u' (ct / 2) < β * u' (h ε) := by
      have := (div_lt_iff₀ hβ).1 h2; linarith
    have a := mul_lt_mul_of_pos_left this hε
    have b := mul_le_mul_of_nonneg_right h1 (mul_pos hβ hpos2).le
    nlinarith
  have hloss : u ct - u (ct - ε) ≤ ε * u' (ct / 2) := by
    have : u ct ≤ u (ct - ε) + u' (ct - ε) * ε := by
      have := ta; rw [show ct - (ct - ε) = ε by ring] at this; exact this
    nlinarith
  have hwin : β * (h ε * u' (h ε)) ≤ β * (u (h ε) - u 0) := by
    have : h ε * u' (h ε) ≤ u (h ε) - u 0 := by linarith
    exact mul_le_mul_of_nonneg_left this hβ.le
  rw [pow_succ] at hcmp
  nlinarith [mul_pos hbt hgain]

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Example 4.1: the finite-horizon model in closed form

AKMM, §4.2.4, Example 4.1, pp. 103–104: `u(c) = log c`, `f(k) = Ak^α`, `δ = 1`. With
`q = αβ` and `n = T − t` periods left after `t`, the saving rate is
`s_n = q(1 − qⁿ)/(1 − qⁿ⁺¹)`.

* `example41_rate_recursion`: `s_{n+1} = q/(1 + q − s_n)`, the backward-induction step, and
  `example41_rate_geometric`: `s_n = q(1 + q + ⋯ + q^{n−1})/(1 + q + ⋯ + qⁿ)`, the book's
  intermediate forms (`example41_kT`, `example41_kTminus1`).
* `example41_consumption_share`: `1 − s_n = (1 − q)/(1 − qⁿ⁺¹)`, the book's `c_t`.
* `eq_4_11`: the plan `k_{t+1} = s_{T−t}Ak_t^α` satisfies the Euler equation (4.11) for `t < T`,
  and `k_{T+1} = 0`.
* `example_4_1`: it is the unique maximizer of (P3) (via `ngm_finite_sufficient` and
  `ngm_finite_unique`).
-/

namespace AKMM.DynamicOptimization

open Real

/-- AKMM, p. 103: the saving rate with `n` periods left, `s_n = q(1 − qⁿ)/(1 − qⁿ⁺¹)`. -/
noncomputable def example41Rate (q : ℝ) (n : ℕ) : ℝ := q * (1 - q ^ n) / (1 - q ^ (n + 1))

theorem example41_rate_zero (q : ℝ) : example41Rate q 0 = 0 := by simp [example41Rate]

/-- AKMM, p. 103: the backward-induction step `s_{n+1} = q/(1 + q − s_n)`. -/
theorem example41_rate_recursion {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    example41Rate q (n + 1) = q / (1 + q - example41Rate q n) := by
  have h1 : 0 < 1 - q ^ (n + 1) := sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))
  have h2 : 0 < 1 - q ^ (n + 1 + 1) := sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))
  unfold example41Rate
  have e : 1 + q - q * (1 - q ^ n) / (1 - q ^ (n + 1)) =
      (1 - q ^ (n + 1 + 1)) / (1 - q ^ (n + 1)) := by
    field_simp; ring
  rw [e]
  field_simp

/-- AKMM, p. 103: the saving rate in geometric-sum form,
`s_n = q(1 + q + ⋯ + q^{n−1})/(1 + q + ⋯ + qⁿ)`. -/
theorem example41_rate_geometric {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    example41Rate q n = q * (∑ i ∈ Finset.range n, q ^ i) / ∑ i ∈ Finset.range (n + 1), q ^ i := by
  have hq : q ≠ 1 := hq1.ne
  rw [geom_sum_eq hq, geom_sum_eq hq, example41Rate]
  have h1 : (q - 1) ≠ 0 := sub_ne_zero.2 hq
  have h2 : 1 - q ^ (n + 1) ≠ 0 := (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))).ne'
  have h3 : q ^ (n + 1) - 1 ≠ 0 := by intro h; apply h2; linarith
  field_simp
  ring

/-- AKMM, p. 103: `k_T = (αβ/(1 + αβ))Ak_{T−1}^α`, i.e. `s₁ = q/(1 + q)`. -/
theorem example41_kT {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : example41Rate q 1 = q / (1 + q) := by
  rw [example41_rate_geometric hq0 hq1]; simp [Finset.sum_range_succ]

/-- AKMM, p. 103: `k_{T−1} = (αβ(1 + αβ)/(1 + αβ + (αβ)²))Ak_{T−2}^α`. -/
theorem example41_kTminus1 {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    example41Rate q 2 = q * (1 + q) / (1 + q + q ^ 2) := by
  rw [example41_rate_geometric hq0 hq1]; simp [Finset.sum_range_succ]

/-- AKMM, p. 103: the consumption share `1 − s_n = (1 − q)/(1 − qⁿ⁺¹)`, so
`c_t = ((1 − αβ)/(1 − (αβ)^{T−t+1}))Ak_t^α`. -/
theorem example41_consumption_share {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    1 - example41Rate q n = (1 - q) / (1 - q ^ (n + 1)) := by
  have h2 : 1 - q ^ (n + 1) ≠ 0 := (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))).ne'
  unfold example41Rate
  field_simp
  ring

theorem example41_rate_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    0 ≤ example41Rate q n :=
  div_nonneg (mul_nonneg hq0.le (sub_nonneg.2 (pow_le_one₀ hq0.le hq1.le)))
    (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))).le

theorem example41_rate_lt_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    example41Rate q n < 1 := by
  have h := example41_consumption_share hq0 hq1 n
  have : 0 < (1 - q) / (1 - q ^ (n + 1)) :=
    div_pos (by linarith) (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega)))
  linarith

theorem example41_rate_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {n : ℕ} (hn : 0 < n) :
    0 < example41Rate q n :=
  div_pos (mul_pos hq0 (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))))
    (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega)))

/-- The plan of Example 4.1: `k₀` given and `k_{t+1} = s_{T−t}Ak_t^α`. -/
noncomputable def example41Plan (A α β : ℝ) (T : ℕ) (k0 : ℝ) : ℕ → ℝ
  | 0 => k0
  | t + 1 => example41Rate (α * β) (T - t) * (A * example41Plan A α β T k0 t ^ α)

theorem example41_plan_succ (A α β : ℝ) (T : ℕ) (k0 : ℝ) (t : ℕ) :
    example41Plan A α β T k0 (t + 1) =
      example41Rate (α * β) (T - t) * (A * example41Plan A α β T k0 t ^ α) := rfl

variable {A α β : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
include hA hα0 hα1 hβ0 hβ1

theorem example41_plan_pos {T : ℕ} {k0 : ℝ} (hk0 : 0 < k0) {t : ℕ} (ht : t ≤ T) :
    0 < example41Plan A α β T k0 t := by
  have hq0 : 0 < α * β := mul_pos hα0 hβ0
  have hq1 : α * β < 1 := by nlinarith
  induction t with
  | zero => exact hk0
  | succ t ih =>
    rw [example41_plan_succ]
    exact mul_pos (example41_rate_pos hq0 hq1 (by omega))
      (mul_pos hA (rpow_pos_of_pos (ih (by omega)) α))

/-- **AKMM, (4.11), p. 103.** The plan `k_{t+1} = s_{T−t}Ak_t^α` satisfies the Euler equation
`1/(Ak_t^α − k_{t+1}) = β · αAk_{t+1}^{α−1}/(Ak_{t+1}^α − k_{t+2})` for `t < T`, and
`k_{T+1} = 0`. -/
theorem eq_4_11 {T : ℕ} {k0 : ℝ} (hk0 : 0 < k0) :
    (∀ t < T, 1 / (A * example41Plan A α β T k0 t ^ α - example41Plan A α β T k0 (t + 1)) =
      β * (α * A * example41Plan A α β T k0 (t + 1) ^ (α - 1)) /
        (A * example41Plan A α β T k0 (t + 1) ^ α - example41Plan A α β T k0 (t + 2))) ∧
    example41Plan A α β T k0 (T + 1) = 0 := by
  have hq0 : 0 < α * β := mul_pos hα0 hβ0
  have hq1 : α * β < 1 := by nlinarith
  refine ⟨fun t ht => ?_, by rw [example41_plan_succ, Nat.sub_self, example41_rate_zero,
    zero_mul]⟩
  have hk : 0 < example41Plan A α β T k0 t := example41_plan_pos hA hα0 hα1 hβ0 hβ1 hk0 ht.le
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  have hk1 := example41_plan_succ A α β T k0 t
  have hk2 := example41_plan_succ A α β T k0 (t + 1)
  rw [hn] at hk1
  rw [hn'] at hk2
  rw [show t + 2 = t + 1 + 1 by rfl, hk2, hk1]
  set Y := A * example41Plan A α β T k0 t ^ α
  have hY : 0 < Y := mul_pos hA (rpow_pos_of_pos hk α)
  set s := example41Rate (α * β) (n + 1)
  set s' := example41Rate (α * β) n
  have hs0 : 0 < s := example41_rate_pos hq0 hq1 (by omega)
  have hs1 : s < 1 := example41_rate_lt_one hq0 hq1 _
  have hs'1 : s' < 1 := example41_rate_lt_one hq0 hq1 _
  have hrec : s * (1 - s') = α * β * (1 - s) := by
    have hthis : s = α * β / (1 + α * β - s') := example41_rate_recursion hq0 hq1 n
    have hne : 1 + α * β - s' ≠ 0 := by linarith
    rw [hthis]
    field_simp
    ring
  have hsY : 0 < s * Y := mul_pos hs0 hY
  have hpow : (s * Y) ^ (α - 1) = (s * Y) ^ α / (s * Y) := rpow_sub_one hsY.ne' α
  rw [hpow]
  have hP : 0 < (s * Y) ^ α := rpow_pos_of_pos hsY α
  have h1 : Y - s * Y ≠ 0 := by nlinarith
  have h2 : A * (s * Y) ^ α - s' * (A * (s * Y) ^ α) ≠ 0 := by
    have : 0 < A * (s * Y) ^ α := mul_pos hA hP
    nlinarith
  rw [div_eq_div_iff h1 h2]
  field_simp
  linear_combination hrec

/-- **Example 4.1** (AKMM, pp. 103–104): the plan `k_{t+1} = αβ(1 − (αβ)^{T−t})/(1 − (αβ)^{T−t+1})
Ak_t^α` is the unique maximizer of (P3) with `u = log`, `f(k) = Ak^α`, `δ = 1`, among feasible
plans with positive consumption (the others have value `−∞` in the book). -/
theorem example_4_1 {T : ℕ} {k0 : ℝ} (hk0 : 0 < k0) {k : ℕ → ℝ}
    (hk : NGMFeasible (fun k => A * k ^ α) k0 T k)
    (hkS : ∀ t ≤ T, A * k t ^ α - k (t + 1) ∈ Set.Ioi 0) :
    NGMFeasible (fun k => A * k ^ α) k0 T (example41Plan A α β T k0) ∧
      ngmObjective Real.log (fun k => A * k ^ α) β k T ≤
        ngmObjective Real.log (fun k => A * k ^ α) β (example41Plan A α β T k0) T ∧
      ((∀ x : ℕ → ℝ, NGMFeasible (fun k => A * k ^ α) k0 T x →
        (∀ t ≤ T, A * x t ^ α - x (t + 1) ∈ Set.Ioi 0) →
          ngmObjective Real.log (fun k => A * k ^ α) β x T ≤
            ngmObjective Real.log (fun k => A * k ^ α) β k T) →
        ∀ t ≤ T + 1, k t = example41Plan A α β T k0 t) := by
  have hq0 : 0 < α * β := mul_pos hα0 hβ0
  have hq1 : α * β < 1 := by nlinarith
  set h : ℝ → ℝ := fun k => A * k ^ α
  set ks := example41Plan A α β T k0
  have hpos : ∀ t ≤ T, 0 < ks t := fun t ht => example41_plan_pos hA hα0 hα1 hβ0 hβ1 hk0 ht
  have hc : ∀ t ≤ T, h (ks t) - ks (t + 1) = (1 - example41Rate (α * β) (T - t)) * h (ks t) :=
    fun t _ => by simp only [h, ks, example41_plan_succ]; ring
  have hhpos : ∀ t ≤ T, 0 < h (ks t) := fun t ht => mul_pos hA (rpow_pos_of_pos (hpos t ht) α)
  have hcpos : ∀ t ≤ T, 0 < h (ks t) - ks (t + 1) := fun t ht => by
    rw [hc t ht]
    exact mul_pos (by linarith [example41_rate_lt_one hq0 hq1 (T - t)]) (hhpos t ht)
  have hfeas : NGMFeasible h k0 T ks := by
    refine ⟨rfl, fun t ht => ⟨?_, ?_⟩⟩
    · rw [show ks (t + 1) = _ from example41_plan_succ A α β T k0 t]
      exact mul_nonneg (example41_rate_nonneg hq0 hq1 _) (hhpos t ht).le
    · linarith [hcpos t ht]
  have hS : Convex ℝ (Set.Ioi (0 : ℝ)) := convex_Ioi 0
  have hup : ∀ x ∈ Set.Ioi (0 : ℝ), ∀ y, x ≤ y → y ∈ Set.Ioi (0 : ℝ) :=
    fun x hx y hxy => lt_of_lt_of_le hx hxy
  have hhc : StrictConcaveOn ℝ (Set.Ici 0) h := by
    refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have := (strictConcaveOn_rpow hα0 hα1).2 hx hy hxy ha hb hab
    simp only [smul_eq_mul, h] at this ⊢
    have := mul_lt_mul_of_pos_left this hA
    linarith
  have hdu : ∀ t ≤ T, HasDerivAt Real.log (h (ks t) - ks (t + 1))⁻¹ (h (ks t) - ks (t + 1)) :=
    fun t ht => hasDerivAt_log (hcpos t ht).ne'
  have hdh : ∀ t ≤ T, HasDerivAt h (A * (α * ks t ^ (α - 1))) (ks t) := fun t ht =>
    (hasDerivAt_rpow_const (Or.inl (hpos t ht).ne')).const_mul A
  have heuler : ∀ t < T, (h (ks t) - ks (t + 1))⁻¹ =
      β * (h (ks (t + 1)) - ks (t + 1 + 1))⁻¹ * (A * (α * ks (t + 1) ^ (α - 1))) := by
    intro t ht
    have := (eq_4_11 hA hα0 hα1 hβ0 hβ1 (T := T) hk0).1 t ht
    rw [← one_div, this]
    simp only [h, ks]
    ring
  have hterm : ks (T + 1) = 0 := (eq_4_11 hA hα0 hα1 hβ0 hβ1 (T := T) hk0).2
  have hdu0 : 0 ≤ (h (ks T) - ks (T + 1))⁻¹ := (inv_pos.2 (hcpos T le_rfl)).le
  have hopt := fun (x : ℕ → ℝ) (hx : NGMFeasible h k0 T x)
      (hxS : ∀ t ≤ T, h (x t) - x (t + 1) ∈ Set.Ioi 0) =>
    ngm_finite_sufficient hS hup strictConcaveOn_log_Ioi.concaveOn
      strictMonoOn_log.monotoneOn hhc.concaveOn hβ0.le hk0.le hfeas (fun t ht => hcpos t ht)
      hdu hdh hdu0 heuler hterm hx hxS
  refine ⟨hfeas, hopt k hk hkS, fun hkmax => ?_⟩
  refine finite_unique_max (ngm_return_strictConcave hS hup strictConcaveOn_log_Ioi strictMonoOn_log
      hhc) hβ0 (x0 := k0)
    (P := {x | NGMFeasible h k0 T x ∧ ∀ t ≤ T, h (x t) - x (t + 1) ∈ Set.Ioi 0})
    (fun x hx => hx.1.1) (fun x hx t ht => ⟨?_, hx.2 t ht⟩) ?_ ⟨hk, hkS⟩
    ⟨hfeas, fun t ht => hcpos t ht⟩ (fun x hx => hkmax x hx.1 hx.2) (fun x hx => hopt x hx.1 hx.2)
  · rcases t with _ | t
    · rw [hx.1.1]; exact hk0.le
    · exact (hx.1.2 t (by omega)).1
  · intro x hx y hy
    have hnn : ∀ z : ℕ → ℝ, NGMFeasible h k0 T z → ∀ t ≤ T, 0 ≤ z t := by
      intro z hz t ht
      rcases t with _ | t
      · rw [hz.1]; exact hk0.le
      · exact (hz.2 t (by omega)).1
    refine ⟨⟨by simp only [hx.1.1, hy.1.1]; ring, fun t ht => ?_⟩, fun t ht => ?_⟩
    · have hcc := hhc.concaveOn.2 (Set.mem_Ici.2 (hnn x hx.1 t ht))
        (Set.mem_Ici.2 (hnn y hy.1 t ht)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hcc
      rw [show (1 / 2 : ℝ) * x t + 1 / 2 * y t = (x t + y t) / 2 by ring] at hcc
      exact ⟨by linarith [(hx.1.2 t ht).1, (hy.1.2 t ht).1],
        by linarith [(hx.1.2 t ht).2, (hy.1.2 t ht).2]⟩
    · have hcc := hhc.concaveOn.2 (Set.mem_Ici.2 (hnn x hx.1 t ht))
        (Set.mem_Ici.2 (hnn y hy.1 t ht)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hcc
      rw [show (1 / 2 : ℝ) * x t + 1 / 2 * y t = (x t + y t) / 2 by ring] at hcc
      have h1 := hx.2 t ht
      have h2 := hy.2 t ht
      simp only [Set.mem_Ioi] at h1 h2 ⊢
      linarith

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# CRRA utility and the elasticity of intertemporal substitution

AKMM, §4.2.4, the CRRA box (p. 104), the EIS (p. 105) and Example 4.2 (p. 105); also fn. 31 of
App. 4.A.2 (p. 830).

* `crra_tendsto_log`: `(c^{1−σ} − 1)/(1 − σ) → log c` as `σ → 1` (the box and fn. 31).
* As `σ → ∞` the CRRA utility tends to `0` for `c ≥ 1` (`crra_tendsto_zero_of_one_le`) but to
  `−∞` for `0 < c < 1` (`crra_tendsto_atBot_of_lt_one`): the box's "converges to zero for all
  `c`" is false.
* The Leontief limit: `(Σ_{t<n} βᵗc_t^{1−σ})^{1/(1−σ)} → min_t c_t` as `σ → ∞`
  (`crra_leontief_limit`), proved for finitely many periods.
* Example 4.2: repeated substitution in the Euler equation (`example42_repeated`), the ratio
  `c_{t+s}/c_t = (βˢ)^{1/σ}R_{t,t+s}^{1/σ}` (`example42_ratio`), the EIS `1/σ`
  (`example42_eis`), constant expenditure shares under log utility (`example42_log_shares`), and
  the income and substitution effects: `c_t` rises with the return when `σ > 1` and falls when
  `σ < 1` (`example42_income_effect`, `example42_substitution_effect`).
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real

/-- AKMM, CRRA box, p. 104: `u(c) = (c^{1−σ} − 1)/(1 − σ)`. -/
noncomputable def crra (σ c : ℝ) : ℝ := (c ^ (1 - σ) - 1) / (1 - σ)

/-- AKMM, CRRA box (p. 104) and fn. 31 (p. 830): `σ → 1` gives logarithmic utility,
`(c^{1−σ} − 1)/(1 − σ) → log c`. -/
theorem crra_tendsto_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun σ => crra σ c) (𝓝[≠] 1) (𝓝 (Real.log c)) := by
  have hd : HasDerivAt (fun s : ℝ => c ^ s) (c ^ (0 : ℝ) * Real.log c) 0 :=
    (hasStrictDerivAt_const_rpow hc 0).hasDerivAt
  rw [rpow_zero, one_mul] at hd
  have hslope := hd.tendsto_slope
  have hmap : Tendsto (fun σ : ℝ => 1 - σ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun σ : ℝ => 1 - σ) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact sub_ne_zero.2 (Ne.symm hσ)
  refine (hslope.comp hmap).congr fun σ => ?_
  simp only [Function.comp_apply, slope_def_field, sub_zero, rpow_zero, crra]

/-- AKMM, CRRA box, p. 104: for `c ≥ 1` the CRRA utility tends to `0` as `σ → ∞`. -/
theorem crra_tendsto_zero_of_one_le {c : ℝ} (hc : 1 ≤ c) :
    Tendsto (fun σ => crra σ c) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hc with rfl | hc1
  · simp [crra]
  have hc0 : 0 < c := by linarith
  have hlog : 0 < Real.log c := Real.log_pos hc1
  have hnum : Tendsto (fun σ : ℝ => 1 - c ^ (1 - σ)) atTop (𝓝 (1 - 0)) := by
    refine tendsto_const_nhds.sub ?_
    have : Tendsto (fun σ : ℝ => (1 - σ) * Real.log c) atTop atBot :=
      (tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot)).atBot_mul_const hlog
        |>.congr fun σ => by ring
    exact (Real.tendsto_exp_atBot.comp this).congr fun σ => by
      simp [Function.comp_apply, rpow_def_of_pos hc0, mul_comm]
  have hden : Tendsto (fun σ : ℝ => σ - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  refine (hnum.div_atTop hden).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with σ hσ
  simp only [crra]
  have : (1 - σ) ≠ 0 := by linarith
  have : (σ - 1) ≠ 0 := by linarith
  field_simp
  ring

/-- **AKMM, CRRA box, p. 104, corrected.** For `0 < c < 1` the CRRA utility tends to `−∞` as
`σ → ∞`, so the box's "utility converges to zero for all `c`" fails. -/
theorem crra_tendsto_atBot_of_lt_one {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto (fun σ => crra σ c) atTop atBot := by
  set a := -Real.log c
  have ha : 0 < a := neg_pos.2 (Real.log_neg hc0 hc1)
  -- `c^{1−σ} = exp(a(σ − 1))` and `exp(ax)/x → ∞`
  have hx : Tendsto (fun σ : ℝ => σ - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hexp : Tendsto (fun x : ℝ => Real.exp (a * x) / x) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => a * x) atTop atTop := tendsto_id.const_mul_atTop ha
    have h2 := (tendsto_exp_div_pow_atTop 1).comp h1
    have h3 := h2.const_mul_atTop ha
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply, pow_one]
    field_simp
  have hmain : Tendsto (fun σ : ℝ => Real.exp (a * (σ - 1)) / (σ - 1) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hexp.comp hx)
  refine tendsto_atBot_mono' _ ?_ (tendsto_neg_atTop_atBot.comp hmain)
  filter_upwards [eventually_ge_atTop 2] with σ hσ
  have hpow : c ^ (1 - σ) = Real.exp (a * (σ - 1)) := by
    rw [rpow_def_of_pos hc0]; congr 1; simp only [a]; ring
  simp only [Function.comp_apply, crra, hpow]
  have hs : 0 < σ - 1 := by linarith
  have e : (Real.exp (a * (σ - 1)) - 1) / (1 - σ) =
      -(Real.exp (a * (σ - 1)) / (σ - 1)) + 1 / (σ - 1) := by
    have : (1 - σ) ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  have : 1 / (σ - 1) ≤ 1 := by rw [div_le_one hs]; linarith
  linarith

/-- **AKMM, CRRA box, p. 104: the Leontief limit.** For finitely many periods, positive
consumption and `β > 0`, `(Σ_{t<n} βᵗc_t^{1−σ})^{1/(1−σ)} → min_{t<n} c_t` as `σ → ∞`. (The book
states it for infinite sums, where the minimum need not exist.) -/
theorem crra_leontief_limit {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : (Finset.range n).Nonempty)
    {c : ℕ → ℝ} (hc : ∀ t, 0 < c t) :
    Tendsto (fun σ : ℝ => (∑ t ∈ Finset.range n, β ^ t * c t ^ (1 - σ)) ^ (1 / (1 - σ))) atTop
      (𝓝 ((Finset.range n).inf' hn c)) := by
  set m := (Finset.range n).inf' hn c
  obtain ⟨j, hj, hjm⟩ := Finset.exists_mem_eq_inf' hn c
  have hmj : m = c j := hjm
  have hm : 0 < m := by rw [hmj]; exact hc j
  have hmle : ∀ t ∈ Finset.range n, m ≤ c t := fun t ht => Finset.inf'_le c ht
  set W := ∑ t ∈ Finset.range n, β ^ t
  have hW : 0 < W := Finset.sum_pos (fun t _ => pow_pos hβ t) hn
  set w := β ^ j
  have hw : 0 < w := pow_pos hβ j
  have he : Tendsto (fun σ : ℝ => 1 / (1 - σ)) atTop (𝓝 0) := by
    have : Tendsto (fun σ : ℝ => 1 - σ) atTop atBot :=
      tendsto_atBot_add_const_left _ 1 tendsto_neg_atTop_atBot
    have h2 := tendsto_inv_atBot_zero.comp this
    simpa only [one_div, Function.comp_def] using h2
  have hlim : ∀ x : ℝ, 0 < x → Tendsto (fun σ : ℝ => x ^ (1 / (1 - σ)) * m) atTop (𝓝 m) := by
    intro x hx
    have := ((continuousAt_const_rpow hx.ne' (b := 0)).tendsto.comp he).mul_const m
    simpa only [Function.comp_def, rpow_zero, one_mul] using this
  have hscale : ∀ x : ℝ, 0 < x → ∀ σ : ℝ, 1 < σ →
      (x * m ^ (1 - σ)) ^ (1 / (1 - σ)) = x ^ (1 / (1 - σ)) * m := by
    intro x hx σ hσ
    rw [mul_rpow hx.le (rpow_nonneg hm.le _), ← rpow_mul hm.le]
    have : (1 - σ) * (1 / (1 - σ)) = 1 := by field_simp [show (1 - σ) ≠ 0 by linarith]
    rw [this, rpow_one]
  have hbounds : ∀ σ : ℝ, 1 < σ →
      W ^ (1 / (1 - σ)) * m ≤ (∑ t ∈ Finset.range n, β ^ t * c t ^ (1 - σ)) ^ (1 / (1 - σ)) ∧
      (∑ t ∈ Finset.range n, β ^ t * c t ^ (1 - σ)) ^ (1 / (1 - σ)) ≤ w ^ (1 / (1 - σ)) * m := by
    intro σ hσ
    have hp : 1 - σ ≤ 0 := by linarith
    have he0 : 1 / (1 - σ) ≤ 0 := div_nonpos_of_nonneg_of_nonpos zero_le_one hp
    have hupper : ∑ t ∈ Finset.range n, β ^ t * c t ^ (1 - σ) ≤ W * m ^ (1 - σ) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_nonpos hm (hmle t ht) hp) (pow_nonneg hβ.le t)
    have hlower : w * m ^ (1 - σ) ≤ ∑ t ∈ Finset.range n, β ^ t * c t ^ (1 - σ) := by
      have := Finset.single_le_sum (f := fun t => β ^ t * c t ^ (1 - σ))
        (fun t _ => mul_nonneg (pow_nonneg hβ.le t) (rpow_nonneg (hc t).le _)) hj
      simpa only [w, hmj] using this
    have hpos : 0 < w * m ^ (1 - σ) := mul_pos hw (rpow_pos_of_pos hm _)
    rw [← hscale W hW σ hσ, ← hscale w hw σ hσ]
    exact ⟨rpow_le_rpow_of_nonpos (hpos.trans_le hlower) hupper he0,
      rpow_le_rpow_of_nonpos hpos hlower he0⟩
  have hW' := hlim W hW
  have hw' := hlim w hw
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hW' hw'
    ((eventually_gt_atTop 1).mono fun σ hσ => (hbounds σ hσ).1)
    ((eventually_gt_atTop 1).mono fun σ hσ => (hbounds σ hσ).2)

/-- **AKMM, Example 4.2, p. 105: repeated substitution.** The Euler equation
`u'(c_t) = βu'(c_{t+1})R_{t+1}` gives `u'(c_t) = βˢu'(c_{t+s})R_{t+1}⋯R_{t+s}`. -/
theorem example42_repeated {u' : ℝ → ℝ} {β : ℝ} {c R : ℕ → ℝ}
    (heuler : ∀ t, u' (c t) = β * u' (c (t + 1)) * R (t + 1)) (t s : ℕ) :
    u' (c t) = β ^ s * u' (c (t + s)) * ∏ i ∈ Finset.range s, R (t + i + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [ih, heuler (t + s), Finset.prod_range_succ, pow_succ, ← add_assoc]
    ring

/-- **AKMM, Example 4.2, p. 105.** With `u'(c) = c^{−σ}`, `σ > 0`, the Euler relation
`c_t^{−σ} = βˢc_{t+s}^{−σ}R_{t,t+s}` gives `c_{t+s}/c_t = (βˢ)^{1/σ}R_{t,t+s}^{1/σ}`. -/
theorem example42_ratio {σ B R c0 c1 : ℝ} (hσ : 0 < σ) (hB : 0 < B) (hR : 0 < R) (hc0 : 0 < c0)
    (hc1 : 0 < c1) (h : c0 ^ (-σ) = B * c1 ^ (-σ) * R) :
    c1 / c0 = B ^ (1 / σ) * R ^ (1 / σ) := by
  have h' : (c1 / c0) ^ σ = B * R := by
    rw [div_rpow hc1.le hc0.le, rpow_neg hc0.le, rpow_neg hc1.le] at *
    have h0 : 0 < c0 ^ σ := rpow_pos_of_pos hc0 σ
    have h1 : 0 < c1 ^ σ := rpow_pos_of_pos hc1 σ
    field_simp at h
    rw [div_eq_iff h0.ne']
    linarith
  have hq : 0 < c1 / c0 := div_pos hc1 hc0
  rw [← mul_rpow hB.le hR.le, ← h', ← rpow_mul hq.le, mul_one_div_cancel hσ.ne', rpow_one]

/-- **AKMM, Example 4.2, p. 105: the EIS of CRRA utility is `1/σ`.** Writing the return as
`R = eˣ`, `log(c_{t+s}/c_t) = log((βˢ)^{1/σ}R^{1/σ})` has derivative `1/σ` in `x = log R`. -/
theorem example42_eis {σ B : ℝ} (hB : 0 < B) (x : ℝ) :
    HasDerivAt (fun x => Real.log (B ^ (1 / σ) * Real.exp x ^ (1 / σ))) (1 / σ) x := by
  have e : (fun x => Real.log (B ^ (1 / σ) * Real.exp x ^ (1 / σ))) =
      fun x => Real.log (B ^ (1 / σ)) + x * (1 / σ) := by
    funext x
    rw [Real.log_mul (rpow_pos_of_pos hB _).ne' (rpow_pos_of_pos (exp_pos x) _).ne',
      Real.log_rpow (exp_pos x), Real.log_exp, mul_comm]
  rw [e]
  simpa using ((hasDerivAt_id x).mul_const (1 / σ)).const_add (Real.log (B ^ (1 / σ)))

/-- AKMM, Example 4.2, p. 105: with log utility (`σ = 1`) the expenditure ratio
`c_t/(c_{t+s}/R_{t,t+s}) = 1/βˢ` does not depend on the return. -/
theorem example42_log_shares {B R c0 c1 : ℝ} (hB : 0 < B) (hR : 0 < R) (hc0 : 0 < c0)
    (h : c1 = B * R * c0) : c0 / (c1 / R) = 1 / B := by
  rw [h]; field_simp

/-- AKMM, Example 4.2, p. 105: with `c_{t+s} = (βˢR)^{1/σ}c_t` and the budget
`c_t + c_{t+s}/R = W`, consumption is `c_t = W/(1 + (βˢ)^{1/σ}R^{1/σ−1})`. -/
theorem example42_consumption {σ B R W c0 c1 : ℝ} (hB : 0 < B) (hR : 0 < R)
    (hratio : c1 = B ^ (1 / σ) * R ^ (1 / σ) * c0) (hbudget : c0 + c1 / R = W) :
    c0 = W / (1 + B ^ (1 / σ) * R ^ (1 / σ - 1)) := by
  have hpos : 0 < 1 + B ^ (1 / σ) * R ^ (1 / σ - 1) := by positivity
  rw [eq_div_iff hpos.ne', ← hbudget, hratio, rpow_sub_one hR.ne']
  field_simp

/-- **AKMM, Example 4.2, p. 105: the income effect dominates for `σ > 1`.** Then
`c_t = W/(1 + (βˢ)^{1/σ}R^{1/σ−1})` rises with the return `R` (and saving falls). -/
theorem example42_income_effect {σ B W : ℝ} (hσ : 1 < σ) (hB : 0 < B) (hW : 0 < W) :
    StrictMonoOn (fun R => W / (1 + B ^ (1 / σ) * R ^ (1 / σ - 1))) (Set.Ioi 0) := by
  intro R hR R' hR' hlt
  have he : 1 / σ - 1 < 0 := by
    rw [sub_neg, div_lt_one (by linarith)]; exact hσ
  have h1 : R' ^ (1 / σ - 1) < R ^ (1 / σ - 1) := rpow_lt_rpow_of_neg hR hlt he
  have hb : 0 < B ^ (1 / σ) := rpow_pos_of_pos hB _
  have hd' : 0 < 1 + B ^ (1 / σ) * R' ^ (1 / σ - 1) := by
    have := rpow_pos_of_pos (show (0 : ℝ) < R' from hR') (1 / σ - 1); positivity
  exact div_lt_div_of_pos_left hW hd' (by nlinarith)

/-- **AKMM, Example 4.2, p. 105: the substitution effect dominates for `σ < 1`.** Then `c_t`
falls with the return `R` (and saving rises). -/
theorem example42_substitution_effect {σ B W : ℝ} (hσ0 : 0 < σ) (hσ : σ < 1) (hB : 0 < B)
    (hW : 0 < W) :
    StrictAntiOn (fun R => W / (1 + B ^ (1 / σ) * R ^ (1 / σ - 1))) (Set.Ioi 0) := by
  intro R hR R' hR' hlt
  have he : 0 < 1 / σ - 1 := by rw [sub_pos, lt_div_iff₀ hσ0]; linarith
  have h1 : R ^ (1 / σ - 1) < R' ^ (1 / σ - 1) := rpow_lt_rpow (le_of_lt hR) hlt he
  have hb : 0 < B ^ (1 / σ) := rpow_pos_of_pos hB _
  have hd : 0 < 1 + B ^ (1 / σ) * R ^ (1 / σ - 1) := by
    have := rpow_pos_of_pos (show (0 : ℝ) < R from hR) (1 / σ - 1); positivity
  exact div_lt_div_of_pos_left hW hd (by nlinarith)

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Infinite horizon: boundedness, Ponzi schemes and the budget constraint

AKMM, §4.3.1, pp. 106–109.

* Unbounded utility: a constant stream has finite utility iff `β < 1`
  (`infinite_constant_summable_iff`); a stream growing at rate `γ` with CRRA utility has finite
  utility iff `β(1 + γ)^{1−σ} < 1` (`infinite_growth_summable_iff`), which holds for every
  `γ > 0` when `σ > 1` (`infinite_growth_sigma_gt_one`), is an upper bound on `γ` when `σ < 1`
  (`infinite_growth_sigma_lt_one`), and fails for fast enough negative growth when `σ > 1`
  (`infinite_growth_negative_fails`).
* The Ponzi scheme: with only the flow budget constraint every plan can be strictly improved
  (`ponzi_improvement`), so no plan is optimal (`ponzi_no_maximum`); the improvement lowers the
  discounted terminal assets by `ε`, so it violates the no-Ponzi-game condition (4.12) whenever
  the original plan satisfies the transversality condition.
* The consolidated budget: `eq_4_13_finite`, (4.13) under (4.12) (`eq_4_13`) and (4.14) when the
  TVC (4.15) holds too (`eq_4_14`).
* Example 4.3: `c_t = [β(1 + r)]ᵗc₀` and `c₀ = (1 − β)(1 + r)a₀` (`example_4_3_path`,
  `example_4_3_c0`), and this plan is optimal (`example_4_3`).
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real

/-- AKMM, p. 106: a constant stream `c̄` with `u(c̄) ≠ 0` has finite lifetime utility
`Σ βᵗu(c̄)` iff `β < 1` (for `β ≥ 0`). -/
theorem infinite_constant_summable_iff {β v : ℝ} (hβ : 0 ≤ β) (hv : v ≠ 0) :
    (Summable fun t : ℕ => β ^ t * v) ↔ β < 1 := by
  rw [summable_mul_right_iff hv, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
    abs_of_nonneg hβ]

/-- CRRA utility along a growing stream: `β^t u(c₀(1 + γ)^t)` in geometric form. -/
theorem infinite_growth_term {σ β c0 g : ℝ} (hc0 : 0 < c0) (hg : 0 < g) (t : ℕ) :
    β ^ t * crra σ (c0 * g ^ t) =
      (c0 ^ (1 - σ) * (β * g ^ (1 - σ)) ^ t - β ^ t) / (1 - σ) := by
  unfold crra
  have e : (g ^ t) ^ (1 - σ) = (g ^ (1 - σ)) ^ t := by
    rw [← rpow_natCast, ← rpow_mul hg.le, mul_comm, rpow_mul hg.le, rpow_natCast]
  rw [mul_rpow hc0.le (pow_nonneg hg.le t), e, mul_pow]
  ring

/-- **AKMM, p. 107: boundedness of CRRA utility along a growing path.** With `σ ≠ 1`, `c₀ > 0`,
`1 + γ > 0` and `0 < β < 1`, `Σ βᵗu(c₀(1 + γ)ᵗ)` is finite iff `β(1 + γ)^{1−σ} < 1`. -/
theorem infinite_growth_summable_iff {σ β c0 γ : ℝ} (hσ : σ ≠ 1) (hc0 : 0 < c0)
    (hγ : 0 < 1 + γ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (Summable fun t : ℕ => β ^ t * crra σ (c0 * (1 + γ) ^ t)) ↔ β * (1 + γ) ^ (1 - σ) < 1 := by
  have h1σ : (1 - σ) ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  simp_rw [infinite_growth_term (σ := σ) (β := β) hc0 hγ]
  have hgeo : Summable fun t : ℕ => β ^ t := summable_geometric_of_lt_one hβ0.le hβ1
  have hq : 0 < β * (1 + γ) ^ (1 - σ) := mul_pos hβ0 (rpow_pos_of_pos hγ _)
  have hc : c0 ^ (1 - σ) ≠ 0 := (rpow_pos_of_pos hc0 _).ne'
  constructor
  · intro hs
    have h2 : Summable fun t : ℕ => c0 ^ (1 - σ) * (β * (1 + γ) ^ (1 - σ)) ^ t := by
      have := (hs.mul_right (1 - σ)).add hgeo
      refine this.congr fun t => ?_
      field_simp
      ring
    rw [summable_mul_left_iff hc, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
      abs_of_pos hq] at h2
    exact h2
  · intro h
    have h2 : Summable fun t : ℕ => (β * (1 + γ) ^ (1 - σ)) ^ t :=
      summable_geometric_of_lt_one hq.le h
    exact ((h2.mul_left (c0 ^ (1 - σ))).sub hgeo).div_const _

/-- AKMM, p. 107: if `σ > 1` and `0 < β < 1`, positive growth `γ > 0` meets the boundedness
condition. -/
theorem infinite_growth_sigma_gt_one {σ β γ : ℝ} (hσ : 1 < σ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) : β * (1 + γ) ^ (1 - σ) < 1 := by
  have : (1 + γ) ^ (1 - σ) < 1 := rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  nlinarith [rpow_pos_of_pos (show (0 : ℝ) < 1 + γ by linarith) (1 - σ)]

/-- AKMM, p. 107: if `σ < 1` the boundedness condition is an upper bound on the growth factor,
`1 + γ < β^{−1/(1−σ)}`. -/
theorem infinite_growth_sigma_lt_one {σ β γ : ℝ} (hσ : σ < 1) (hβ0 : 0 < β) (hγ : 0 < 1 + γ) :
    β * (1 + γ) ^ (1 - σ) < 1 ↔ 1 + γ < β ^ (-(1 / (1 - σ))) := by
  have hp : 0 < 1 - σ := by linarith
  have hb : 0 < β ^ (-(1 / (1 - σ))) := rpow_pos_of_pos hβ0 _
  have key : (β ^ (-(1 / (1 - σ)))) ^ (1 - σ) = β⁻¹ := by
    rw [← rpow_mul hβ0.le, show -(1 / (1 - σ)) * (1 - σ) = -1 by field_simp, rpow_neg_one]
  rw [← rpow_lt_rpow_iff hγ.le hb.le hp, key]
  have hx := rpow_pos_of_pos hγ (1 - σ)
  constructor <;> intro h
  · calc (1 + γ) ^ (1 - σ) = β⁻¹ * (β * (1 + γ) ^ (1 - σ)) := by field_simp
      _ < β⁻¹ * 1 := mul_lt_mul_of_pos_left h (inv_pos.2 hβ0)
      _ = β⁻¹ := mul_one _
  · calc β * (1 + γ) ^ (1 - σ) < β * β⁻¹ := mul_lt_mul_of_pos_left h hβ0
      _ = 1 := mul_inv_cancel₀ hβ0.ne'

/-- AKMM, p. 107: if `σ > 1`, negative growth at a high enough rate violates the boundedness
condition: `γ = β^{1/(σ−1)} − 1 ∈ (−1, 0)` gives `β(1 + γ)^{1−σ} = 1`. -/
theorem infinite_growth_negative_fails {σ β : ℝ} (hσ : 1 < σ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ γ, -1 < γ ∧ γ < 0 ∧ 1 ≤ β * (1 + γ) ^ (1 - σ) := by
  have hp : 0 < 1 / (σ - 1) := by apply div_pos one_pos; linarith
  refine ⟨β ^ (1 / (σ - 1)) - 1, by linarith [rpow_pos_of_pos hβ0 (1 / (σ - 1))],
    by linarith [rpow_lt_one hβ0.le hβ1 hp], ?_⟩
  rw [show 1 + (β ^ (1 / (σ - 1)) - 1) = β ^ (1 / (σ - 1)) by ring, ← rpow_mul hβ0.le,
    show 1 / (σ - 1) * (1 - σ) = -1 by field_simp [show σ - 1 ≠ 0 by linarith]; ring,
    rpow_neg_one, mul_inv_cancel₀ hβ0.ne']

/-- AKMM, p. 107: the Ponzi perturbation of an asset path: `ã₀ = a₀` and
`ã_{t+1} = a_{t+1} − ε(1 + r)ᵗ`. -/
noncomputable def ponziAssets (a : ℕ → ℝ) (r ε : ℝ) : ℕ → ℝ
  | 0 => a 0
  | s + 1 => a (s + 1) - ε * (1 + r) ^ s

/-- **AKMM, p. 107: the Ponzi scheme.** Given any plan satisfying `c_t + a_{t+1} = (1 + r)a_t`,
consuming `ε > 0` more at `t = 0` and rolling the debt over, `ã_{t+1} = a_{t+1} − ε(1 + r)ᵗ`,
satisfies the budget constraint, raises every partial sum of utility, and lowers the discounted
terminal assets `a_{t+1}/(1 + r)ᵗ` by `ε`. -/
theorem ponzi_improvement {u : ℝ → ℝ} (hu : StrictMono u) {β r ε : ℝ} (hr : -1 < r)
    (hε : 0 < ε) {c a : ℕ → ℝ} (hbudget : ∀ t, c t + a (t + 1) = (1 + r) * a t) :
    (∀ t, Function.update c 0 (c 0 + ε) t + ponziAssets a r ε (t + 1) =
      (1 + r) * ponziAssets a r ε t) ∧
    (∀ T, ∑ t ∈ Finset.range (T + 1), β ^ t * u (c t) <
      ∑ t ∈ Finset.range (T + 1), β ^ t * u (Function.update c 0 (c 0 + ε) t)) ∧
    ∀ t, ponziAssets a r ε (t + 1) / (1 + r) ^ t = a (t + 1) / (1 + r) ^ t - ε := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  refine ⟨fun t => ?_, fun T => ?_, fun t => ?_⟩
  · rcases t with _ | s
    · simp only [Function.update_self, ponziAssets, pow_zero, mul_one]
      linarith [hbudget 0]
    · rw [Function.update_of_ne (by omega)]
      simp only [ponziAssets]
      have := hbudget (s + 1)
      rw [pow_succ]
      linarith
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hrest : ∑ t ∈ Finset.range T, β ^ (t + 1) * u (Function.update c 0 (c 0 + ε) (t + 1)) =
        ∑ t ∈ Finset.range T, β ^ (t + 1) * u (c (t + 1)) :=
      Finset.sum_congr rfl fun t _ => by rw [Function.update_of_ne (by omega)]
    rw [hrest, Function.update_self, pow_zero, one_mul, one_mul]
    have := hu (show c 0 < c 0 + ε by linarith)
    linarith
  · simp only [ponziAssets]
    have : (1 + r) ^ t ≠ 0 := (pow_pos hr' t).ne'
    field_simp

/-- **AKMM, pp. 107–108: without a no-Ponzi condition there is no maximum.** If `u` is strictly
increasing, `β ≥ 0` and `r > −1`, no plan satisfying only the flow budget constraint, with finite
utility, is at least as good as every other such plan. -/
theorem ponzi_no_maximum {u : ℝ → ℝ} (hu : StrictMono u) {β r a0 : ℝ} (hr : -1 < r) :
    ¬ ∃ c a : ℕ → ℝ, a 0 = a0 ∧ (∀ t, c t + a (t + 1) = (1 + r) * a t) ∧
      (Summable fun t => β ^ t * u (c t)) ∧
      ∀ c' a' : ℕ → ℝ, a' 0 = a0 → (∀ t, c' t + a' (t + 1) = (1 + r) * a' t) →
        (Summable fun t => β ^ t * u (c' t)) →
        ∑' t, β ^ t * u (c' t) ≤ ∑' t, β ^ t * u (c t) := by
  rintro ⟨c, a, ha0, hbud, hsum, hmax⟩
  obtain ⟨hbud', -, -⟩ := ponzi_improvement (β := β) hu hr one_pos hbud
  set c' := Function.update c 0 (c 0 + 1)
  have hsucc : ∀ t, β ^ (t + 1) * u (c' (t + 1)) = β ^ (t + 1) * u (c (t + 1)) := fun t => by
    change β ^ (t + 1) * u (Function.update c 0 (c 0 + 1) (t + 1)) = _
    rw [Function.update_of_ne (by omega)]
  have hsum' : Summable fun t => β ^ t * u (c' t) := by
    rw [← summable_nat_add_iff 1]
    simp only [hsucc]
    exact (summable_nat_add_iff 1).2 hsum
  have h := hmax c' (ponziAssets a r 1) (by simp [ponziAssets, ha0]) hbud' hsum'
  rw [hsum'.tsum_eq_zero_add, hsum.tsum_eq_zero_add] at h
  simp only [hsucc, c', Function.update_self, pow_zero, one_mul] at h
  have := hu (show c 0 < c 0 + 1 by linarith)
  linarith

/-- AKMM, p. 108: consolidating `T + 1` flow budget constraints `c_t + a_{t+1} = (1 + r)a_t`
gives `Σ_{t≤T} c_t/(1 + r)ᵗ = a₀(1 + r) − a_{T+1}/(1 + r)ᵀ`. -/
theorem eq_4_13_finite {r : ℝ} (hr : -1 < r) {c a : ℕ → ℝ}
    (hbudget : ∀ t, c t + a (t + 1) = (1 + r) * a t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t = a 0 * (1 + r) - a (T + 1) / (1 + r) ^ T := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  induction T with
  | zero => simp only [zero_add, Finset.sum_range_one, pow_zero, div_one]; linarith [hbudget 0]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    have := hbudget (T + 1)
    have h1 : (1 + r) ^ T ≠ 0 := (pow_pos hr' T).ne'
    have h2 : (1 + r) ^ (T + 1) ≠ 0 := (pow_pos hr' (T + 1)).ne'
    rw [eq_sub_of_add_eq this]
    field_simp
    ring

/-- **AKMM, (4.13), p. 108.** If consumption is nonnegative and the no-Ponzi-game condition
(4.12) holds, `a_{T+1}/(1 + r)ᵀ → L ≥ 0`, then `Σ c_t/(1 + r)ᵗ = a₀(1 + r) − L ≤ a₀(1 + r)`. -/
theorem eq_4_13 {r : ℝ} (hr : -1 < r) {c a : ℕ → ℝ} (hc : ∀ t, 0 ≤ c t)
    (hbudget : ∀ t, c t + a (t + 1) = (1 + r) * a t) {L : ℝ}
    (hlim : Tendsto (fun T => a (T + 1) / (1 + r) ^ T) atTop (𝓝 L)) (hL : 0 ≤ L) :
    HasSum (fun t => c t / (1 + r) ^ t) (a 0 * (1 + r) - L) ∧
      a 0 * (1 + r) - L ≤ a 0 * (1 + r) := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  refine ⟨(hasSum_iff_tendsto_nat_of_nonneg (fun t => div_nonneg (hc t)
    (pow_pos hr' t).le) _).2 ?_, by linarith⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  simp only [eq_4_13_finite hr hbudget]
  exact tendsto_const_nhds.sub hlim

/-- **AKMM, (4.14)–(4.15), p. 109.** With the transversality condition (4.15) `L ≤ 0` as well,
the lifetime budget constraint holds with equality: `Σ c_t/(1 + r)ᵗ = a₀(1 + r)`. -/
theorem eq_4_14 {r : ℝ} (hr : -1 < r) {c a : ℕ → ℝ} (hc : ∀ t, 0 ≤ c t)
    (hbudget : ∀ t, c t + a (t + 1) = (1 + r) * a t) {L : ℝ}
    (hlim : Tendsto (fun T => a (T + 1) / (1 + r) ^ T) atTop (𝓝 L)) (hnpg : 0 ≤ L)
    (htvc : L ≤ 0) : HasSum (fun t => c t / (1 + r) ^ t) (a 0 * (1 + r)) := by
  have := (eq_4_13 hr hc hbudget hlim hnpg).1
  rwa [le_antisymm htvc hnpg, sub_zero] at this

/-- AKMM, Example 4.3, p. 109: the first-order conditions `βᵗ/c_t = λ(1/(1 + r))ᵗ` give
`c_t = [β(1 + r)]ᵗc₀`. -/
theorem example_4_3_path {β r lam : ℝ} (hr : -1 < r) {c : ℕ → ℝ} (hc : ∀ t, c t ≠ 0)
    (hfoc : ∀ t, β ^ t * (1 / c t) = lam * (1 / (1 + r)) ^ t) (t : ℕ) :
    c t = (β * (1 + r)) ^ t * c 0 := by
  have hr' : (1 + r) ≠ 0 := by linarith
  have h0 := hfoc 0
  simp only [pow_zero, one_mul, mul_one] at h0
  have ht := hfoc t
  rw [← h0] at ht
  have hc0 := hc 0
  have hct := hc t
  have h2 : c t = β ^ t * c 0 * (1 + r) ^ t := by
    simp only [one_div, inv_pow] at ht
    field_simp at ht
    linarith
  rw [h2, mul_pow]
  ring

/-- AKMM, Example 4.3, p. 109: substituting `c_t = [β(1 + r)]ᵗc₀` into the consolidated budget
`Σ c_t/(1 + r)ᵗ = a₀(1 + r)` gives `c₀ = (1 − β)(1 + r)a₀`. -/
theorem example_4_3_c0 {β r a0 c0 : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hr : -1 < r)
    (h : HasSum (fun t : ℕ => (β * (1 + r)) ^ t * c0 / (1 + r) ^ t) (a0 * (1 + r))) :
    c0 = (1 - β) * (1 + r) * a0 := by
  have hr' : (1 + r) ≠ 0 := by linarith
  have e : (fun t : ℕ => (β * (1 + r)) ^ t * c0 / (1 + r) ^ t) = fun t => c0 * β ^ t := by
    funext t; rw [mul_pow]; field_simp
  rw [e] at h
  have h2 := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left c0
  have := h.unique h2
  have h1β : (1 - β) ≠ 0 := by linarith
  field_simp at this
  linarith

/-- **AKMM, Example 4.3, p. 109: the solution is optimal.** With `u = log`, `0 < β < 1`,
`r > −1` and `a₀ > 0`, the plan `c*_t = [β(1 + r)]ᵗ(1 − β)(1 + r)a₀` exhausts the lifetime budget
(4.14), and every positive plan with `Σ c_t/(1 + r)ᵗ ≤ a₀(1 + r)` and finite utility has
`Σ βᵗ log c_t ≤ Σ βᵗ log c*_t`. -/
theorem example_4_3 {β r a0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hr : -1 < r) (ha0 : 0 < a0) :
    HasSum (fun t : ℕ => (β * (1 + r)) ^ t * ((1 - β) * (1 + r) * a0) / (1 + r) ^ t)
      (a0 * (1 + r)) ∧
    ∀ c : ℕ → ℝ, (∀ t, 0 < c t) → (Summable fun t => c t / (1 + r) ^ t) →
      ∑' t, c t / (1 + r) ^ t ≤ a0 * (1 + r) → (Summable fun t => β ^ t * Real.log (c t)) →
      ∑' t, β ^ t * Real.log (c t) ≤
        ∑' t : ℕ, β ^ t * Real.log ((β * (1 + r)) ^ t * ((1 - β) * (1 + r) * a0)) := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  set K := (1 - β) * (1 + r) * a0
  have hK : 0 < K := mul_pos (mul_pos (by linarith) hr') ha0
  have e : ∀ t : ℕ, (β * (1 + r)) ^ t * K / (1 + r) ^ t = K * β ^ t := fun t => by
    rw [mul_pow]; field_simp
  have hgeo := hasSum_geometric_of_lt_one hβ0.le hβ1
  refine ⟨?_, fun c hc hcs hbud hu => ?_⟩
  · simp only [e]
    have := hgeo.mul_left K
    convert this using 1
    simp only [K]; field_simp [show (1 - β) ≠ 0 by linarith]
  set cs : ℕ → ℝ := fun t => (β * (1 + r)) ^ t * K
  have hcs0 : ∀ t, 0 < cs t := fun t => mul_pos (pow_pos (mul_pos hβ0 hr') t) hK
  have hlogcs : ∀ t, β ^ t * Real.log (cs t) =
      Real.log (β * (1 + r)) * ((t : ℝ) ^ 1 * β ^ t) + Real.log K * β ^ t := fun t => by
    simp only [cs]
    rw [Real.log_mul (pow_pos (mul_pos hβ0 hr') t).ne' hK.ne', Real.log_pow]
    ring
  have hnorm : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
  have hsumcs : Summable fun t => β ^ t * Real.log (cs t) := by
    simp only [hlogcs]
    exact ((summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).mul_left _).add
      (hgeo.summable.mul_left _)
  -- the tangent inequality `log x ≤ log y + x/y − 1`, weighted by `βᵗ`
  have hle : ∀ t, β ^ t * Real.log (c t) ≤ β ^ t * Real.log (cs t) +
      (c t / (1 + r) ^ t) / K - β ^ t := fun t => by
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hc t) (hcs0 t))
    rw [Real.log_div (hc t).ne' (hcs0 t).ne'] at h1
    have hb := pow_pos hβ0 t
    have h2 : β ^ t * (c t / cs t) = (c t / (1 + r) ^ t) / K := by
      simp only [cs]; rw [mul_pow]; field_simp
    nlinarith
  have hsumR : Summable fun t => β ^ t * Real.log (cs t) + (c t / (1 + r) ^ t) / K - β ^ t :=
    (hsumcs.add (hcs.div_const K)).sub hgeo.summable
  have := hu.tsum_le_tsum hle hsumR
  rw [Summable.tsum_sub (hsumcs.add (hcs.div_const K)) hgeo.summable,
    Summable.tsum_add hsumcs (hcs.div_const K), tsum_div_const, hgeo.tsum_eq] at this
  have hbudK : (∑' t, c t / (1 + r) ^ t) / K ≤ (1 - β)⁻¹ := by
    rw [div_le_iff₀ hK]
    calc ∑' t, c t / (1 + r) ^ t ≤ a0 * (1 + r) := hbud
      _ = (1 - β)⁻¹ * K := by simp only [K]; field_simp [show (1 - β) ≠ 0 by linarith]
  linarith

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Proposition 4.4: the Euler equation and the transversality condition are sufficient

AKMM, §4.3.1, pp. 110–111, with the proof of App. 4.A.3, pp. 830–831.

* **Proposition 4.4** (`proposition_4_4`): a plan satisfying the Euler equation (i) and the TVC
  (ii) `βᵗF₁(x*_t, x*_{t+1})x*_t → 0`, with `F` concave and `F₁ ≥ 0`, is optimal: catching-up
  optimal, and of largest value whenever values are finite. It is proved from EulerTransversality's
  `euler_tvc_sufficient` (the book's telescoping argument of 4.A.3, in supergradient form). The
  book's "increasing in its first argument" gives `F₁ ≥ 0` (`proposition_4_4_F1_nonneg`).
* The book omits a hypothesis that its proof uses: the competing plans must be nonnegative
  (the last step of 4.A.3 needs `F₁ · x_{T+1} ≥ 0`). Without it the proposition is false
  (`proposition_4_4_counterexample`: `F(x, y) = x − βy`, `Γ(x) = ℝ`, `x* = 0`). The book's
  restriction to interior competitors is not needed.
* The NGM form of the TVC, `lim βᵗu'(c_t)[f'(k_t) + 1 − δ]k_t = 0` (p. 110), and sufficiency in the
  NGM (`proposition_4_4_ngm`, from EulerTransversality's `growth_sufficient`).
* A stationary plan satisfies the TVC automatically when `β < 1` (`tvc_stationary`), and the
  modified-golden-rule steady state is optimal (`ngm_steady_state_optimal`).
* On a balanced path with gross growth `γ`, `βᵗu'(c_t)k_t` grows at the gross rate `βγ^{1−σ}`,
  and the TVC holds iff `βγ^{1−σ} < 1` (`tvc_balanced_growth`), the boundedness condition of
  `infinite_growth_summable_iff`.
-/

namespace AKMM.DynamicOptimization

open Filter Topology StokeyLucasPrescott.DeterministicDP DPExtensions.EulerTransversality

/-- **Proposition 4.4** (AKMM, p. 110; proof in App. 4.A.3, pp. 830–831). Let `F` be concave on
a convex set `A` containing the graph of `Γ`, with derivative `D_t` at `(x*_t, x*_{t+1})` along a
feasible plan `x*`, `F₁ = D_t(1, 0) ≥ 0`, the Euler equation
`F₂(x*_t, x*_{t+1}) + βF₁(x*_{t+1}, x*_{t+2}) = 0` and the transversality condition
`βᵗF₁(x*_t, x*_{t+1})x*_t → 0`. If every feasible plan from `x*_0` is nonnegative (a hypothesis
missing from the book), then `x*` is catching-up optimal, and its value is the largest whenever
the values are finite. Interiority is not needed. -/
theorem proposition_4_4 {F : ℝ × ℝ → ℝ} {Γ : ℝ → Set ℝ} {A : Set (ℝ × ℝ)}
    (hA : ConcaveOn ℝ A F) (hGA : ∀ x, ∀ y ∈ Γ x, (x, y) ∈ A) {β : ℝ} (hβ : 0 ≤ β)
    {xs : ℕ → ℝ} (hxs : ∀ t, xs (t + 1) ∈ Γ (xs t)) (D : ℕ → ℝ × ℝ →L[ℝ] ℝ)
    (hD : ∀ t, HasFDerivAt F (D t) (xs t, xs (t + 1))) (hF1 : ∀ t, 0 ≤ D t (1, 0))
    (heuler : ∀ t, D t (0, 1) + β * D (t + 1) (1, 0) = 0)
    (htvc : Tendsto (fun t => β ^ t * (D t (1, 0) * xs t)) atTop (𝓝 0))
    (hnn : ∀ x : ℕ → ℝ, Feasible {p | p.2 ∈ Γ p.1} (xs 0) x → ∀ t, 0 ≤ x t) :
    CatchingUp {p | p.2 ∈ Γ p.1} (fun a b => F (a, b)) β xs ∧
      ∀ x, Feasible {p | p.2 ∈ Γ p.1} (xs 0) x →
        (Summable fun t => β ^ t * F (x t, x (t + 1))) →
        (Summable fun t => β ^ t * F (xs t, xs (t + 1))) →
        ∑' t, β ^ t * F (x t, x (t + 1)) ≤ ∑' t, β ^ t * F (xs t, xs (t + 1)) := by
  refine euler_tvc_sufficient hβ (p := fun t => D t (1, 0) • LinearMap.id)
    (q := fun t => D t (0, 1) • LinearMap.id) (fun t a b hab => ?_) (fun t v => ?_)
    (fun x hx t => ?_) ?_
  · have h := concave_le_fderiv hA (hGA _ _ (hxs t)) (hGA a b hab) (hD t)
    rw [Prod.mk_sub_mk, finite_fderiv_apply] at h
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    linarith
  · simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    linear_combination v * heuler t
  · simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    exact mul_nonneg (hF1 t) (hnn x hx t)
  · simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] using htvc

/-- AKMM, p. 110: if `F` is increasing in its first argument, `F₁ ≥ 0`, as Proposition 4.4
requires. -/
theorem proposition_4_4_F1_nonneg {F : ℝ × ℝ → ℝ} {a b : ℝ} {D : ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt F D (a, b)) (hinc : Monotone fun x => F (x, b)) : 0 ≤ D (1, 0) := by
  have hline : HasDerivAt (fun x : ℝ => ((x, b) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) a :=
    (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
  have hcomp : HasDerivAt (fun x => F (x, b)) (D (1, 0)) a := hD.comp_hasDerivAt a hline
  rw [← hcomp.deriv]
  exact hinc.deriv_nonneg

/-- The return of the counterexample to Proposition 4.4 as printed: `F(x, y) = x − βy`. -/
def prop44CounterF (β : ℝ) (p : ℝ × ℝ) : ℝ := p.1 - β * p.2

/-- **Proposition 4.4 needs nonnegative states** (AKMM, p. 110 and App. 4.A.3). With
`0 < β < 1`, `F(x, y) = x − βy` (linear, so concave, and increasing in `x`), `Γ(x) = ℝ` (convex,
every choice interior) and `x* = 0`, the Euler equation and the TVC hold, but the plan
`x₀ = 0`, `x_t = −β^{−t}` has value `1 > 0`; so `x*` is not optimal. -/
theorem proposition_4_4_counterexample {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ConcaveOn ℝ Set.univ (prop44CounterF β) ∧ (∀ y, Monotone fun x => prop44CounterF β (x, y)) ∧
    (∀ p, HasFDerivAt (prop44CounterF β)
      (ContinuousLinearMap.fst ℝ ℝ ℝ - β • ContinuousLinearMap.snd ℝ ℝ ℝ) p) ∧
    (ContinuousLinearMap.fst ℝ ℝ ℝ - β • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 1) +
      β * (ContinuousLinearMap.fst ℝ ℝ ℝ - β • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) = 0 ∧
    Tendsto (fun t : ℕ => β ^ t * ((ContinuousLinearMap.fst ℝ ℝ ℝ -
      β • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) * (0 : ℝ))) atTop (𝓝 0) ∧
    ∃ x : ℕ → ℝ, Feasible {p : ℝ × ℝ | p.2 ∈ (Set.univ : Set ℝ)} 0 x ∧
      HasSum (fun t => β ^ t * prop44CounterF β (x t, x (t + 1))) 1 ∧
      HasSum (fun t => β ^ t * prop44CounterF β ((fun _ => (0 : ℝ)) t, (0 : ℝ))) 0 ∧
      ¬ CatchingUp {p : ℝ × ℝ | p.2 ∈ (Set.univ : Set ℝ)} (fun a b => prop44CounterF β (a, b)) β
        fun _ => 0 := by
  set L := ContinuousLinearMap.fst ℝ ℝ ℝ - β • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : ∀ p, L p = prop44CounterF β p := fun p => by
    simp [L, prop44CounterF]
  have hFL : prop44CounterF β = ⇑L := funext fun p => (hL p).symm
  set x : ℕ → ℝ := fun t => if t = 0 then 0 else -(β ^ t)⁻¹
  have hterm : ∀ t, β ^ t * prop44CounterF β (x t, x (t + 1)) = if t = 0 then 1 else 0 := by
    intro t
    have hb : β ≠ 0 := hβ0.ne'
    rcases t with _ | s
    · simp [x, prop44CounterF, hb]
    · simp only [x, prop44CounterF, Nat.add_one_ne_zero, ↓reduceIte]
      field_simp
      ring
  have hsum : HasSum (fun t => β ^ t * prop44CounterF β (x t, x (t + 1))) 1 := by
    simp only [hterm]
    convert hasSum_ite_eq 0 (1 : ℝ) using 1
  refine ⟨?_, fun y a b hab => ?_, fun p => ?_, ?_, ?_, x, ⟨rfl, fun _ => Set.mem_univ _⟩,
    hsum, ?_, fun h => ?_⟩
  · rw [hFL]; exact L.toLinearMap.concaveOn convex_univ
  · simp only [prop44CounterF]; linarith
  · rw [hFL]; exact L.hasFDerivAt
  · simp [L]
  · simp
  · simp [prop44CounterF, hasSum_zero]
  · have := h x ⟨rfl, fun _ => Set.mem_univ _⟩ (1 / 2) (by norm_num)
    obtain ⟨T, hT⟩ := (this.and (eventually_ge_atTop 1)).exists
    have h1 : partialValue (fun a b => prop44CounterF β (a, b)) β x T = 1 := by
      unfold partialValue
      simp only [hterm]
      rw [Finset.sum_ite_eq' (Finset.range T) 0 fun _ => (1 : ℝ)]
      simp [Finset.mem_range, show 0 < T by omega]
    have h0 : partialValue (fun a b => prop44CounterF β (a, b)) β (fun _ => (0 : ℝ)) T = 0 := by
      simp [partialValue, prop44CounterF]
    linarith [hT.1]

/-- **Proposition 4.4 in the NGM** (AKMM, p. 110). With `h(k) = f(k) + (1 − δ)k`, `u` concave and
nondecreasing and `h` concave on `[0, ∞)`, a feasible capital path satisfying the Euler equation
(4.10) and the TVC `lim βᵗu'(c_t)[f'(k_t) + 1 − δ]k_t = 0` is catching-up optimal
(EulerTransversality's `growth_sufficient`). -/
theorem proposition_4_4_ngm {u h : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) (hu : ConcaveOn ℝ (Set.Ici 0) u)
    (humono : MonotoneOn u (Set.Ici 0)) (hh : ConcaveOn ℝ (Set.Ici 0) h) {ks : ℕ → ℝ}
    (hks : ∀ t, 0 ≤ ks t ∧ 0 ≤ ks (t + 1) ∧ ks (t + 1) ≤ h (ks t)) {du dh : ℕ → ℝ}
    (hdu : ∀ t, HasDerivAt u (du t) (h (ks t) - ks (t + 1)))
    (hdh : ∀ t, HasDerivAt h (dh t) (ks t)) (hdu0 : ∀ t, 0 ≤ du t) (hdh0 : ∀ t, 0 ≤ dh t)
    (heuler : ∀ t, du t = β * du (t + 1) * dh (t + 1))
    (htvc : Tendsto (fun t => β ^ t * (du t * dh t * ks t)) atTop (𝓝 0)) :
    CatchingUp {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.2 ≤ h x.1} (fun k k' => u (h k - k')) β ks :=
  (GrowthModel.mk u h β hβ hu humono hh).growth_sufficient hks hdu hdh hdu0 hdh0 heuler htvc

/-- AKMM, p. 111: along a stationary plan the TVC is satisfied automatically when `0 ≤ β < 1`. -/
theorem tvc_stationary {β C : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun t : ℕ => β ^ t * C) atTop (𝓝 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const C

/-- AKMM, (4.16) and p. 111: in the NGM the steady state `1 = β(f'(k̄) + 1 − δ)` (with
`c̄ = h(k̄) − k̄ ≥ 0`) is optimal from `k̄` (EulerTransversality's `steady_state_optimal`). -/
theorem ngm_steady_state_optimal {u h : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hu : ConcaveOn ℝ (Set.Ici 0) u) (humono : MonotoneOn u (Set.Ici 0))
    (hh : ConcaveOn ℝ (Set.Ici 0) h) {kbar du dh : ℝ} (hk : 0 ≤ kbar) (hc : kbar ≤ h kbar)
    (hdu : HasDerivAt u du (h kbar - kbar)) (hdh : HasDerivAt h dh kbar) (hdu0 : 0 ≤ du)
    (hdh0 : 0 ≤ dh) (h416 : 1 = β * dh) :
    CatchingUp {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.2 ≤ h x.1} (fun k k' => u (h k - k')) β
      fun _ => kbar :=
  (GrowthModel.mk u h β hβ hu humono hh).steady_state_optimal hβ1 hk hc hdu hdh hdu0 hdh0
    h416.symm

/-- **AKMM, p. 111: the TVC on a balanced path.** With `c_t = c₀γᵗ`, `k_t = k₀γᵗ` (gross growth
`γ > 0`) and `u'(c) = c^{−σ}`, `βᵗu'(c_t)k_t` grows at the gross rate `βγ^{1−σ}`, and it tends to
`0` iff `βγ^{1−σ} < 1`. -/
theorem tvc_balanced_growth {β γ σ c0 k0 : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hc0 : 0 < c0)
    (hk0 : 0 < k0) :
    (∀ t : ℕ, β ^ (t + 1) * ((c0 * γ ^ (t + 1)) ^ (-σ) * (k0 * γ ^ (t + 1))) =
      β * γ ^ (1 - σ) * (β ^ t * ((c0 * γ ^ t) ^ (-σ) * (k0 * γ ^ t)))) ∧
    (Tendsto (fun t : ℕ => β ^ t * ((c0 * γ ^ t) ^ (-σ) * (k0 * γ ^ t))) atTop (𝓝 0) ↔
      β * γ ^ (1 - σ) < 1) := by
  have hform : ∀ t : ℕ, β ^ t * ((c0 * γ ^ t) ^ (-σ) * (k0 * γ ^ t)) =
      c0 ^ (-σ) * k0 * (β * γ ^ (1 - σ)) ^ t := by
    intro t
    have e1 : (γ ^ t) ^ (-σ) = (γ ^ (-σ)) ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hγ.le, mul_comm, Real.rpow_mul hγ.le,
        Real.rpow_natCast]
    have e2 : γ ^ (1 - σ) = γ ^ (-σ) * γ := by
      rw [sub_eq_neg_add, Real.rpow_add hγ, Real.rpow_one]
    rw [Real.mul_rpow hc0.le (pow_nonneg hγ.le t), e1, e2, mul_pow, mul_pow]
    ring
  have hC : 0 < c0 ^ (-σ) * k0 := mul_pos (Real.rpow_pos_of_pos hc0 _) hk0
  have hq : 0 < β * γ ^ (1 - σ) := mul_pos hβ (Real.rpow_pos_of_pos hγ _)
  refine ⟨fun t => by rw [hform, hform, pow_succ]; ring, ?_⟩
  simp only [hform]
  constructor
  · intro h
    have h2 := h.div_const (c0 ^ (-σ) * k0)
    simp only [zero_div] at h2
    have h3 : Tendsto (fun t : ℕ => (β * γ ^ (1 - σ)) ^ t) atTop (𝓝 0) :=
      h2.congr fun t => by field_simp
    have := tendsto_pow_atTop_nhds_zero_iff.1 h3
    rwa [abs_of_pos hq] at this
  · intro h
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le h).const_mul (c0 ^ (-σ) * k0)

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The infinite-horizon neoclassical growth model

AKMM, §4.3.2, pp. 111–113.

* (4.16): a steady state with positive consumption satisfies `1 = β(f'(k̄) + 1 − δ)`
  (`eq_4_16_of_euler`), and under strict concavity and the Inada conditions there is exactly one
  (`eq_4_16`).
* Example 4.5: the truncated saving rates converge to `αβ` (`example_4_5_limit`), giving (4.17)
  `k_{t+1} = αβAk_t^α`; along it `βᵗu'(c_t)f'(k_t)k_t = βᵗα/(1 − αβ)`, so the TVC holds
  (`example_4_5_tvc`), and by Proposition 4.4 the plan is optimal (`example_4_5`).
* Example 4.6: the guess `k_{t+1} = sAk_t^α` satisfies the Euler equation iff `s = αβ`
  (`example_4_6`).
* p. 112: `k̄ = (αβA)^{1/(1−α)}` is the steady state of (4.17) (`example_4_5_steady`), and every
  path of (4.17) from `k₀ > 0` converges to it (`example_4_5_convergence`).
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real DPExtensions.EulerTransversality

/-- AKMM, (4.16), p. 111: with constant positive consumption `c̄` (`u'(c̄) ≠ 0`), the Euler
equation (4.10) at a steady state reduces to `1 = β(f'(k̄) + 1 − δ)`. -/
theorem eq_4_16_of_euler {β du dh : ℝ} (hdu : du ≠ 0) (heuler : du = β * du * dh) :
    1 = β * dh := by
  have : du * (1 - β * dh) = 0 := by linear_combination heuler
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hdu
  · linarith

/-- **AKMM, (4.16), p. 111: the steady state is unique.** If `f'` is continuous and strictly
decreasing on `(0, ∞)`, `f'(k) → ∞` as `k → 0⁺` and `f'(k) → 0` as `k → ∞`, `0 < β < 1` and
`0 ≤ δ`, there is exactly one `k̄ > 0` with `1 = β(f'(k̄) + 1 − δ)`. -/
theorem eq_4_16 {f' : ℝ → ℝ} (hcont : ContinuousOn f' (Set.Ioi 0))
    (hanti : StrictAntiOn f' (Set.Ioi 0)) (h0 : Tendsto f' (𝓝[>] 0) atTop)
    (htop : Tendsto f' atTop (𝓝 0)) {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) :
    ∃! k, 0 < k ∧ 1 = β * (f' k + 1 - δ) := by
  set ρ := 1 / β - 1 + δ
  have hρ : 0 < ρ := by
    have : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
    simp only [ρ]; linarith
  have hiff : ∀ k, 1 = β * (f' k + 1 - δ) ↔ f' k = ρ := fun k => by
    simp only [ρ]
    constructor <;> intro h
    · field_simp; linarith
    · rw [h]; field_simp; ring
  obtain ⟨a, ha, ha0⟩ := ((h0.eventually (eventually_gt_atTop ρ)).and
    self_mem_nhdsWithin).exists
  obtain ⟨b, hb, hab⟩ := ((htop.eventually (gt_mem_nhds hρ)).and
    (eventually_ge_atTop a)).exists
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hivt := intermediate_value_Icc' hab (hcont.mono fun x hx =>
    (lt_of_lt_of_le (Set.mem_Ioi.1 ha0) hx.1))
  obtain ⟨k, hk, hfk⟩ := hivt ⟨hb.le, ha.le⟩
  refine ⟨k, ⟨lt_of_lt_of_le ha0 hk.1, (hiff k).2 hfk⟩, fun k' ⟨hk'0, hk'⟩ => ?_⟩
  have h1 := (hiff k').1 hk'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := hanti (Set.mem_Ioi.2 hk'0) (Set.mem_Ioi.2 (lt_of_lt_of_le ha0 hk.1)) hlt
    linarith
  · have := hanti (Set.mem_Ioi.2 (lt_of_lt_of_le ha0 hk.1)) (Set.mem_Ioi.2 hk'0) hlt
    linarith

/-- **AKMM, Example 4.5, p. 112: the limit of the truncated solutions.** As `T → ∞`,
`αβ(1 − (αβ)^{T−t})/(1 − (αβ)^{T−t+1}) → αβ`, which gives (4.17) `k_{t+1} = αβAk_t^α`. -/
theorem example_4_5_limit {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (t : ℕ) :
    Tendsto (fun T : ℕ => example41Rate q (T - t)) atTop (𝓝 q) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
  have hlim : Tendsto (fun n : ℕ => example41Rate q n) atTop (𝓝 q) := by
    have h1 : Tendsto (fun n : ℕ => q * (1 - q ^ n) / (1 - q ^ (n + 1))) atTop
        (𝓝 (q * (1 - 0) / (1 - 0))) := by
      refine ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hpow)).div
        (tendsto_const_nhds.sub ((tendsto_add_atTop_iff_nat 1).2 hpow)) (by norm_num))
    simpa [example41Rate] using h1
  exact hlim.comp (tendsto_sub_atTop_nat t)

variable {A α β : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
include hA hα0 hα1 hβ0 hβ1

/-- **AKMM, Example 4.5, p. 112: the TVC along (4.17).** With `c_t = Ak_t^α − k_{t+1}` and
`k_{t+1} = αβAk_t^α`, `βᵗu'(c_t)f'(k_t)k_t = βᵗα/(1 − αβ)`, which tends to `0`. -/
theorem example_4_5_tvc {k : ℕ → ℝ} (hk : ∀ t, 0 < k t)
    (hplan : ∀ t, k (t + 1) = α * β * A * k t ^ α) :
    (∀ t, β ^ t * ((1 / (A * k t ^ α - k (t + 1))) * (α * A * k t ^ (α - 1)) * k t) =
      β ^ t * (α / (1 - α * β))) ∧
    Tendsto (fun t => β ^ t * ((1 / (A * k t ^ α - k (t + 1))) * (α * A * k t ^ (α - 1)) * k t))
      atTop (𝓝 0) := by
  have hq1 : α * β < 1 := by nlinarith
  have hid : ∀ t, β ^ t * ((1 / (A * k t ^ α - k (t + 1))) * (α * A * k t ^ (α - 1)) * k t) =
      β ^ t * (α / (1 - α * β)) := by
    intro t
    have hkt := hk t
    have hP : 0 < k t ^ α := rpow_pos_of_pos hkt α
    rw [hplan t, rpow_sub_one hkt.ne']
    have h1 : A * k t ^ α - α * β * A * k t ^ α ≠ 0 := by
      have : 0 < A * k t ^ α * (1 - α * β) := mul_pos (mul_pos hA hP) (by linarith)
      nlinarith
    have h2 : (1 - α * β) ≠ 0 := by linarith
    field_simp
  refine ⟨hid, ?_⟩
  simp only [hid]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (α / (1 - α * β))

omit hα1 hβ1 in
/-- **AKMM, Example 4.6, p. 112: guess and verify.** For `0 < s < 1` and `k > 0`, the guess
`k' = sAk^α`, `k'' = sAk'^α` satisfies the Euler equation
`1/(Ak^α − sAk^α) = βαAk'^{α−1}/(Ak'^α − sAk'^α)` iff `s = αβ`. -/
theorem example_4_6 {s k : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hk : 0 < k) :
    1 / (A * k ^ α - s * A * k ^ α) =
        β * α * A * (s * A * k ^ α) ^ (α - 1) /
          (A * (s * A * k ^ α) ^ α - s * A * (s * A * k ^ α) ^ α) ↔ s = α * β := by
  have hP : 0 < k ^ α := rpow_pos_of_pos hk α
  set k' := s * A * k ^ α
  have hk' : 0 < k' := mul_pos (mul_pos hs0 hA) hP
  have hP' : 0 < k' ^ α := rpow_pos_of_pos hk' α
  rw [rpow_sub_one hk'.ne']
  have h1 : A * k ^ α - s * A * k ^ α ≠ 0 := by
    have : 0 < A * k ^ α * (1 - s) := mul_pos (mul_pos hA hP) (by linarith)
    nlinarith
  have h2 : A * k' ^ α - s * A * k' ^ α ≠ 0 := by
    have : 0 < A * k' ^ α * (1 - s) := mul_pos (mul_pos hA hP') (by linarith)
    nlinarith
  have h3 : (1 - s) ≠ 0 := by linarith
  rw [div_eq_div_iff h1 h2]
  have e : β * α * A * (k' ^ α / k') * (A * k ^ α - s * A * k ^ α) =
      α * β * (1 / s) * (A * k' ^ α - s * A * k' ^ α) := by
    simp only [k']
    field_simp
  rw [e, one_mul]
  have h4 : 0 < A * k' ^ α - s * A * k' ^ α := by
    have : 0 < A * k' ^ α * (1 - s) := mul_pos (mul_pos hA hP') (by linarith)
    nlinarith
  constructor
  · intro h
    have : α * β * (1 / s) = 1 := by
      have := mul_right_cancel₀ h4.ne' (h.symm.trans (one_mul _).symm)
      exact this
    field_simp at this
    linarith
  · intro h
    rw [h]
    field_simp [show α * β ≠ 0 from (mul_pos hα0 hβ0).ne']

omit hβ1 in
/-- AKMM, p. 112: `k̄ = (αβA)^{1/(1−α)}` is a steady state of (4.17), `k̄ = αβAk̄^α`, and
satisfies (4.16) with `δ = 1`: `1 = β · αAk̄^{α−1}`. -/
theorem example_4_5_steady :
    (α * β * A) ^ (1 / (1 - α)) = α * β * A * ((α * β * A) ^ (1 / (1 - α))) ^ α ∧
      1 = β * (α * A * ((α * β * A) ^ (1 / (1 - α))) ^ (α - 1)) := by
  have hq : 0 < α * β * A := mul_pos (mul_pos hα0 hβ0) hA
  have h1α : (1 - α) ≠ 0 := by linarith
  set kb := (α * β * A) ^ (1 / (1 - α))
  have hkb : 0 < kb := rpow_pos_of_pos hq _
  have hkey : kb ^ (α - 1) = (α * β * A)⁻¹ := by
    simp only [kb]
    rw [← rpow_mul hq.le, show 1 / (1 - α) * (α - 1) = -1 by field_simp; ring, rpow_neg_one]
  have hkα : kb ^ α = kb ^ (α - 1) * kb := by
    rw [← rpow_add_one hkb.ne']; ring_nf
  refine ⟨?_, ?_⟩
  · rw [hkα, hkey]; field_simp
  · rw [hkey]; field_simp

omit hβ1 in
/-- AKMM, p. 112: every path of (4.17) from `k₀ > 0` converges to `k̄ = (αβA)^{1/(1−α)}`; in logs,
`log k_t − log k̄ = αᵗ(log k₀ − log k̄)`. -/
theorem example_4_5_convergence {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hplan : ∀ t, k (t + 1) = α * β * A * k t ^ α) :
    (∀ t, Real.log (k t) - Real.log ((α * β * A) ^ (1 / (1 - α))) =
      α ^ t * (Real.log (k 0) - Real.log ((α * β * A) ^ (1 / (1 - α))))) ∧
    Tendsto k atTop (𝓝 ((α * β * A) ^ (1 / (1 - α)))) := by
  have hq : 0 < α * β * A := mul_pos (mul_pos hα0 hβ0) hA
  set kb := (α * β * A) ^ (1 / (1 - α))
  have hkb : 0 < kb := rpow_pos_of_pos hq _
  have hpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih => rw [hplan]; exact mul_pos hq (rpow_pos_of_pos ih α)
  have hsteady : kb = α * β * A * kb ^ α := (example_4_5_steady hA hα0 hα1 hβ0).1
  have hlogkb : Real.log kb = Real.log (α * β * A) + α * Real.log kb := by
    conv_lhs => rw [hsteady]
    rw [Real.log_mul hq.ne' (rpow_pos_of_pos hkb α).ne', Real.log_rpow hkb]
  have hlog : ∀ t, Real.log (k t) - Real.log kb = α ^ t * (Real.log (k 0) - Real.log kb) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hplan, Real.log_mul hq.ne' (rpow_pos_of_pos (hpos t) α).ne', Real.log_rpow (hpos t),
        pow_succ]
      linear_combination α * ih - hlogkb
  refine ⟨hlog, ?_⟩
  have hdiff : Tendsto (fun t => Real.log (k t) - Real.log kb) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hα0.le hα1).mul_const
      (Real.log (k 0) - Real.log kb)
    rw [zero_mul] at this
    exact this.congr fun t => (hlog t).symm
  have hl : Tendsto (fun t => Real.log (k t)) atTop (𝓝 (Real.log kb)) := by
    simpa using hdiff.add_const (Real.log kb)
  have := (Real.continuous_exp.tendsto _).comp hl
  simpa [Function.comp_def, Real.exp_log (hpos _), Real.exp_log hkb] using this

/-- **Example 4.5** (AKMM, pp. 111–112): with `u = log`, `f(k) = Ak^α`, `δ = 1`, the plan (4.17)
`k_{t+1} = αβAk_t^α` from `k₀ > 0` is catching-up optimal among plans with positive capital and
consumption, by Proposition 4.4: it satisfies the Euler equation (Example 4.6) and the TVC. -/
theorem example_4_5 {k0 : ℝ} (hk0 : 0 < k0) :
    CatchingUp {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 < p.2 ∧ p.2 < A * p.1 ^ α}
      (fun a b => Real.log (A * a ^ α - b)) β
      (fun t => (fun k => α * β * A * k ^ α)^[t] k0) := by
  have hq1 : α * β < 1 := by nlinarith
  set k : ℕ → ℝ := fun t => (fun k => α * β * A * k ^ α)^[t] k0
  have hplan : ∀ t, k (t + 1) = α * β * A * k t ^ α := fun t =>
    Function.iterate_succ_apply' _ _ _
  have hpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih => rw [hplan]; exact mul_pos (mul_pos (mul_pos hα0 hβ0) hA) (rpow_pos_of_pos ih α)
  set h : ℝ → ℝ := fun x => A * x ^ α
  have hc : ∀ t, h (k t) - k (t + 1) = (1 - α * β) * (A * k t ^ α) := fun t => by
    simp only [h, hplan]; ring
  have hcpos : ∀ t, 0 < h (k t) - k (t + 1) := fun t => by
    rw [hc]; exact mul_pos (by linarith) (mul_pos hA (rpow_pos_of_pos (hpos t) α))
  have hhc : ConcaveOn ℝ (Set.Ici 0) h := (concaveOn_rpow hα0.le hα1.le).smul hA.le
  have hconc := ngm_return_concave (convex_Ioi (0 : ℝ)) (fun x hx y hxy => lt_of_lt_of_le hx hxy)
    strictConcaveOn_log_Ioi.concaveOn strictMonoOn_log.monotoneOn hhc
  have hex : ∀ t, ∃ D : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun p : ℝ × ℝ => Real.log (h p.1 - p.2)) D (k t, k (t + 1)) ∧
        D (1, 0) = (h (k t) - k (t + 1))⁻¹ * (A * (α * k t ^ (α - 1))) ∧
        D (0, 1) = -(h (k t) - k (t + 1))⁻¹ := fun t =>
    ngm_hasFDerivAt (Real.hasDerivAt_log (hcpos t).ne')
      ((hasDerivAt_rpow_const (Or.inl (hpos t).ne')).const_mul A)
  choose D hD using hex
  have htvc := (example_4_5_tvc hA hα0 hα1 hβ0 hβ1 hpos hplan).2
  refine (proposition_4_4 (Γ := fun x => {y | 0 ≤ x ∧ 0 < y ∧ y < A * x ^ α}) hconc
    (fun x y hy => ⟨hy.1, by simp only [h, Set.mem_Ioi]; linarith [hy.2.2]⟩) hβ0.le
    (fun t => ⟨(hpos t).le, hpos (t + 1), by linarith [hcpos t]⟩) D (fun t => (hD t).1)
    (fun t => ?_) (fun t => ?_) ?_ (fun x hx t => ?_)).1
  · rw [(hD t).2.1]
    exact mul_nonneg (inv_pos.2 (hcpos t)).le
      (mul_nonneg hA.le (mul_nonneg hα0.le (rpow_pos_of_pos (hpos t) _).le))
  · -- the Euler equation is Example 4.6 with `s = αβ`
    rw [(hD t).2.2, (hD (t + 1)).2.1]
    have he := (example_4_6 hA hα0 hβ0 (s := α * β) (k := k t) (mul_pos hα0 hβ0) hq1
      (hpos t)).2 rfl
    have e1 : h (k t) - k (t + 1) = A * k t ^ α - α * β * A * k t ^ α := by
      simp only [h, hplan]
    have e2 : h (k (t + 1)) - k (t + 1 + 1) =
        A * (α * β * A * k t ^ α) ^ α - α * β * A * (α * β * A * k t ^ α) ^ α := by
      simp only [h, hplan]
    rw [e1, e2, hplan t]
    rw [← one_div, ← one_div, he]
    ring
  · refine htvc.congr fun t => ?_
    rw [(hD t).2.1]
    simp only [h, one_div]
    ring
  · rcases t with _ | t
    · rw [hx.1]; exact (hpos 0).le
    · exact (hx.2 t).2.1.le

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Balanced growth in the neoclassical growth model

AKMM, §4.3.3, pp. 113–114. Technology `A_t` grows at rate `γ`, population `L_t` at rate `n`;
`x̃ = X/(AL)`, `f(k) = F(k, 1)` for a constant-returns `F`; utilitarian welfare
`Σ βᵗL_tu(c_t)` with CRRA `u(c) = c^{1−σ}/(1 − σ)`.

* (4.18): `c̃_t = f(k̃_t) + (1 − δ)k̃_t − (1 + γ)(1 + n)k̃_{t+1}` (`eq_4_18`).
* (4.19)–(4.20): `βᵗL_tc_t^{1−σ}/(1 − σ) = β̃ᵗc̃_t^{1−σ}/(1 − σ)` with
  `β̃ = β(1 + n)(1 + γ)^{1−σ}` (`eq_4_19`, `adjustedDiscount`).
* The detrended problem's partial derivatives (`bgp_hasFDerivAt`) and its Euler equation
  `(1 + n)(1 + γ)c̃_t^{−σ} = β̃c̃_{t+1}^{−σ}(f'(k̃_{t+1}) + 1 − δ)` (`bgp_euler_detrended`); written
  with `β` the factor `1 + n` drops out, and it is the Euler equation of per-capita consumption
  `c_t = (1 + γ)ᵗc̃_t` (`bgp_euler_original`).
* The balanced-growth condition `(1 + n)(1 + γ) = β̃(f'(k̃) + 1 − δ)` (`bgp_condition`), which
  for `n = γ = 0` is (4.16) (`bgp_no_growth`), and its Cobb–Douglas solution (`bgp_cobbDouglas`).
-/

namespace AKMM.DynamicOptimization

open Real

/-- **AKMM, (4.18), p. 113.** With constant returns `F(lK, lN) = lF(K, N)` (`l > 0`),
`A_{t+1} = (1 + γ)A_t`, `L_{t+1} = (1 + n)L_t` and `C_t = F(K_t, A_tL_t) + (1 − δ)K_t − K_{t+1}`,
variables per efficiency unit satisfy `c̃_t = f(k̃_t) + (1 − δ)k̃_t − (1 + γ)(1 + n)k̃_{t+1}`. -/
theorem eq_4_18 {F : ℝ → ℝ → ℝ} (hcrs : ∀ l : ℝ, 0 < l → ∀ K N, F (l * K) (l * N) = l * F K N)
    {δ γ n : ℝ} {A L K C : ℕ → ℝ} (hA : ∀ t, A (t + 1) = (1 + γ) * A t)
    (hL : ∀ t, L (t + 1) = (1 + n) * L t) (hpos : ∀ t, 0 < A t * L t)
    (hC : ∀ t, C t = F (K t) (A t * L t) + (1 - δ) * K t - K (t + 1)) (t : ℕ) :
    C t / (A t * L t) = F (K t / (A t * L t)) 1 + (1 - δ) * (K t / (A t * L t)) -
      (1 + γ) * (1 + n) * (K (t + 1) / (A (t + 1) * L (t + 1))) := by
  have h := hpos t
  have hA0 : A t ≠ 0 := left_ne_zero_of_mul h.ne'
  have hL0 : L t ≠ 0 := right_ne_zero_of_mul h.ne'
  have hF : F (K t) (A t * L t) = A t * L t * F (K t / (A t * L t)) 1 := by
    rw [← hcrs _ h]
    congr 1
    · field_simp
    · ring
  have hnext : (1 + γ) * (1 + n) * (K (t + 1) / (A (t + 1) * L (t + 1))) =
      K (t + 1) / (A t * L t) := by
    have h1 : 0 < A (t + 1) * L (t + 1) := hpos (t + 1)
    rw [hA, hL] at h1 ⊢
    have h2 : (1 + γ) * (1 + n) ≠ 0 := by
      intro h0
      rw [show (1 + γ) * A t * ((1 + n) * L t) = (1 + γ) * (1 + n) * (A t * L t) by ring,
        h0, zero_mul] at h1
      exact lt_irrefl 0 h1
    have hg : (1 + γ) ≠ 0 := left_ne_zero_of_mul h2
    have hn' : (1 + n) ≠ 0 := right_ne_zero_of_mul h2
    field_simp
  rw [hnext, hC, hF]
  field_simp

/-- AKMM, (4.20), p. 114: the adjusted discount factor `β̃ = β(1 + n)(1 + γ)^{1−σ}`. -/
noncomputable def adjustedDiscount (β n γ σ : ℝ) : ℝ := β * (1 + n) * (1 + γ) ^ (1 - σ)

/-- **AKMM, (4.19), p. 114.** With `L_t = (1 + n)ᵗ`, `A_t = (1 + γ)ᵗ` and per-capita consumption
`c_t = A_tc̃_t`, `βᵗL_tc_t^{1−σ}/(1 − σ) = β̃ᵗc̃_t^{1−σ}/(1 − σ)`. -/
theorem eq_4_19 {β n γ σ c : ℝ} (hγ : 0 < 1 + γ) (hc : 0 ≤ c) (t : ℕ) :
    β ^ t * (1 + n) ^ t * ((1 + γ) ^ t * c) ^ (1 - σ) / (1 - σ) =
      adjustedDiscount β n γ σ ^ t * c ^ (1 - σ) / (1 - σ) := by
  have e : ((1 + γ) ^ t) ^ (1 - σ) = ((1 + γ) ^ (1 - σ)) ^ t := by
    rw [← rpow_natCast, ← rpow_mul hγ.le, mul_comm, rpow_mul hγ.le, rpow_natCast]
  rw [mul_rpow (pow_nonneg hγ.le t) hc, e, adjustedDiscount, mul_pow, mul_pow]
  ring

/-- AKMM, p. 114: the detrended return `u(f(k̃) + (1 − δ)k̃ − (1 + γ)(1 + n)k̃')`, with
`h = f + (1 − δ)·id` and `m = (1 + γ)(1 + n)`, has partial derivatives `F̃₁ = u'(c̃)h'(k̃)` and
`F̃₂ = −mu'(c̃)`. -/
theorem bgp_hasFDerivAt {u h : ℝ → ℝ} {m k k' du dh : ℝ} (hu : HasDerivAt u du (h k - m * k'))
    (hh : HasDerivAt h dh k) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => u (h p.1 - m * p.2)) D (k, k') ∧
      D (1, 0) = du * dh ∧ D (0, 1) = -(m * du) := by
  have hin := (hh.hasFDerivAt.comp (k, k')
    (hasFDerivAt_fst (𝕜 := ℝ) (p := ((k, k') : ℝ × ℝ)))).sub
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := ((k, k') : ℝ × ℝ))).const_mul m)
  have hout := hu.hasFDerivAt.comp (k, k') hin
  refine ⟨_, hout, ?_, ?_⟩ <;> simp [mul_comm]

/-- **AKMM, p. 114: the detrended Euler equation.** In terms of the partial derivatives of the
detrended return, `F̃₂(t) + β̃F̃₁(t + 1) = 0` is
`(1 + n)(1 + γ)u'(c̃_t) = β̃u'(c̃_{t+1})(f'(k̃_{t+1}) + 1 − δ)`. -/
theorem bgp_euler_detrended {m βt du0 du1 dh1 : ℝ} :
    -(m * du0) + βt * (du1 * dh1) = 0 ↔ m * du0 = βt * du1 * dh1 := by
  constructor <;> intro h <;> linarith

/-- **AKMM, p. 114: `1 + n` drops out.** For `c̃ > 0`, `1 + γ > 0`, `1 + n > 0`, the detrended
Euler equation `(1 + n)(1 + γ)c̃_t^{−σ} = β̃c̃_{t+1}^{−σ}R` holds iff per-capita consumption
`c_t = (1 + γ)ᵗc̃_t` satisfies the Euler equation `c_t^{−σ} = βc_{t+1}^{−σ}R` with the original
`β`. -/
theorem bgp_euler_original {β n γ σ R c0 c1 : ℝ} (hγ : 0 < 1 + γ) (hn : 0 < 1 + n)
    (hc0 : 0 < c0) (hc1 : 0 < c1) (t : ℕ) :
    (1 + n) * (1 + γ) * c0 ^ (-σ) = adjustedDiscount β n γ σ * c1 ^ (-σ) * R ↔
      ((1 + γ) ^ t * c0) ^ (-σ) = β * ((1 + γ) ^ (t + 1) * c1) ^ (-σ) * R := by
  set x := (1 + γ) ^ (-σ)
  have hx : 0 < x := rpow_pos_of_pos hγ _
  have hpow : ∀ s : ℕ, ((1 + γ) ^ s) ^ (-σ) = x ^ s := fun s => by
    rw [← rpow_natCast, ← rpow_mul hγ.le, mul_comm, rpow_mul hγ.le, rpow_natCast]
  have hβt : adjustedDiscount β n γ σ = β * (1 + n) * (1 + γ) * x := by
    rw [adjustedDiscount, sub_eq_neg_add, rpow_add hγ, rpow_one]; ring
  rw [mul_rpow (pow_nonneg hγ.le t) hc0.le, mul_rpow (pow_nonneg hγ.le (t + 1)) hc1.le, hpow,
    hpow, hβt, pow_succ]
  have hxt : 0 < x ^ t := pow_pos hx t
  have hm : 0 < (1 + n) * (1 + γ) := mul_pos hn hγ
  constructor <;> intro h
  · have : c0 ^ (-σ) = β * x * c1 ^ (-σ) * R := by
      have := congrArg (fun y => y / ((1 + n) * (1 + γ))) h
      rw [mul_div_cancel_left₀ _ hm.ne'] at this
      rw [this]; field_simp
    rw [this]; ring
  · have : c0 ^ (-σ) = β * x * c1 ^ (-σ) * R := by
      have := congrArg (fun y => y / x ^ t) h
      rw [mul_comm, mul_div_assoc, div_self hxt.ne', mul_one] at this
      rw [this]; field_simp
    rw [this]; ring

/-- **AKMM, p. 114: the balanced-growth condition.** With constant `c̃ > 0`
(`u'(c̃_t) = u'(c̃_{t+1}) ≠ 0`), the detrended Euler equation reduces to
`(1 + n)(1 + γ) = β̃(f'(k̃) + 1 − δ)`. -/
theorem bgp_condition {m βt du dh : ℝ} (hdu : du ≠ 0) (h : m * du = βt * du * dh) :
    m = βt * dh := by
  have : du * (m - βt * dh) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hdu
  · linarith

/-- AKMM, p. 114: with `n = γ = 0`, `β̃ = β` and the balanced-growth condition is (4.16),
`1 = β(f'(k̄) + 1 − δ)`. -/
theorem bgp_no_growth {β σ d : ℝ} :
    adjustedDiscount β 0 0 σ = β ∧
      ((1 + 0) * (1 + 0) = adjustedDiscount β 0 0 σ * d ↔ 1 = β * d) := by
  have : adjustedDiscount β 0 0 σ = β := by simp [adjustedDiscount]
  rw [this]
  exact ⟨rfl, by norm_num⟩

/-- **AKMM, p. 114: Cobb–Douglas balanced growth.** With `f(k) = k^α`, `0 < α < 1`, and
`D = (1 + n)(1 + γ)/β̃ − 1 + δ > 0`, `k̃ = (α/D)^{1/(1−α)}` satisfies the balanced-growth condition
`(1 + n)(1 + γ) = β̃(αk̃^{α−1} + 1 − δ)`. -/
theorem bgp_cobbDouglas {α βt m δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβt : 0 < βt)
    (hD : 0 < m / βt - 1 + δ) :
    m = βt * (α * ((α / (m / βt - 1 + δ)) ^ (1 / (1 - α))) ^ (α - 1) + 1 - δ) := by
  set D := m / βt - 1 + δ
  have hq : 0 < α / D := div_pos hα0 hD
  have hkey : ((α / D) ^ (1 / (1 - α))) ^ (α - 1) = D / α := by
    rw [← rpow_mul hq.le, show 1 / (1 - α) * (α - 1) = -1 by
      field_simp [show (1 - α) ≠ 0 by linarith]; ring, rpow_neg_one, inv_div]
  rw [hkey, mul_div_cancel₀ _ hα0.ne']
  simp only [D]
  field_simp
  ring

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive methods: the Bellman equation and the properties of the value function

AKMM, §4.4.1–4.4.3, pp. 114–120. The sequence-problem machinery is SLP's (`DeterministicDP`):
`Feasible`, `vstar` (the value `V` of (4.21), in the extended reals), `SatisfiesFE`, the Bellman
operator `bellman` on bounded continuous functions.

* (4.21)–(4.22): `V` satisfies the Bellman equation (`eq_4_22`, SLP Theorem 4.2), and along an
  optimal plan `V(x) = F(x, g(x)) + βV(g(x))` (`eq_4_22_policy`, SLP Theorem 4.4).
* The periodic NGM (p. 117) is recursive in the state `(k, parity)` (`periodic_bellman`); the
  printed constraint set `Γ_i(k) = [0, A_if(k) + (1 − δ)k − k']` is wrong
  (`periodic_printed_gamma`).
* The delayed-depreciation NGM (p. 118) is recursive in `(i_{t−1}, i_{t−2})`, with the discount
  factor the printed equation omits (`delayed_bellman`); without `β` the Bellman operator is not
  a contraction (`delayed_no_discount_not_contraction`).
* The properties of `V` (pp. 119–120): 1. value-function iteration converges, with
  `‖V_{n+1} − V‖ ≤ β‖V_n − V‖` (`property_1`, SLP Theorem 4.6); 2. `V` strictly increasing
  (`property_2`, SLP Theorem 4.7); 3. `V` strictly concave and the policy unique and continuous
  (`property_3`, SLP Theorem 4.8); 4. `V` differentiable at interior choices, with the envelope
  formula (`property_4`, from SLP Theorem 4.10).
* Property 5 ("`g` strictly increasing") is false under the stated conditions
  (`property_5_counterexample`); it holds with increasing differences (`property_5_corrected`,
  monotone policy) and in the NGM (`property_5_ngm`, SLP Exercise 6.1b).
-/

namespace AKMM.DynamicOptimization

open Filter Topology BoundedContinuousFunction StokeyLucasPrescott.DeterministicDP

/-- **AKMM, (4.21)–(4.22), pp. 115–116: the Bellman equation.** The value function
`V(x₀) = sup Σ βᵗF(x_t, x_{t+1})` satisfies `V(x) = sup_{x' ∈ Γ(x)} {F(x, x') + βV(x')}`, given
nonempty `Γ` and convergent partial sums (SLP Theorem 4.2). -/
theorem eq_4_22 {X : Type*} {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (h41 : Assumption41 Γ) (h42 : Assumption42 Γ F β) : SatisfiesFE Γ F β (vstar Γ F β) :=
  theorem_4_2 hβ h41 h42

/-- AKMM, p. 117: along an optimal plan `x_{t+1} = g(x_t)`, `V(x_t) = F(x_t, x_{t+1}) +
βV(x_{t+1})` (SLP Theorem 4.4). -/
theorem eq_4_22_policy {X : Type*} {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ} (hβ : 0 < β)
    (h42 : Assumption42 Γ F β) {x₀ : X} {xs : ℕ → X} (hxs : xs ∈ Feasible Γ x₀)
    (hopt : total F β xs = vstar Γ F β x₀) (t : ℕ) :
    vstar Γ F β (xs t) = (F (xs t) (xs (t + 1)) : EReal) + (β : EReal) * vstar Γ F β (xs (t + 1)) :=
  theorem_4_4 hβ h42 hxs hopt t

/-- The periodic NGM in the state `(k, i)`: `Γ̃(k, i) = {(k', ¬i) : 0 ≤ k' ≤ A_if(k) + (1 − δ)k}`
(`i = true` for the even periods with `A_h`). -/
def periodicGamma (A : Bool → ℝ) (f : ℝ → ℝ) (δ : ℝ) (s : ℝ × Bool) : Set (ℝ × Bool) :=
  (fun k' => (k', !s.2)) '' Set.Icc 0 (A s.2 * f s.1 + (1 - δ) * s.1)

/-- The periodic NGM's return `u(A_if(k) + (1 − δ)k − k')`. -/
noncomputable def periodicF (A : Bool → ℝ) (u f : ℝ → ℝ) (δ : ℝ) (s s' : ℝ × Bool) : ℝ :=
  u (A s.2 * f s.1 + (1 - δ) * s.1 - s'.1)

/-- **AKMM, p. 117: the periodic NGM is recursive** in `(k, parity)`: the value functions
`V_h(k) = V(k, true)` and `V_l(k) = V(k, false)` satisfy
`V_h(k) = max_{k' ∈ Γ_h(k)} {u(A_hf(k) + (1 − δ)k − k') + βV_l(k')}` and symmetrically, with
`Γ_i(k) = [0, A_if(k) + (1 − δ)k]`. -/
theorem periodic_bellman {A : Bool → ℝ} {u f : ℝ → ℝ} {δ β : ℝ} (hβ : 0 ≤ β)
    (h41 : Assumption41 (periodicGamma A f δ))
    (h42 : Assumption42 (periodicGamma A f δ) (periodicF A u f δ) β) (k : ℝ) (i : Bool) :
    vstar (periodicGamma A f δ) (periodicF A u f δ) β (k, i) =
      ⨆ k' ∈ Set.Icc 0 (A i * f k + (1 - δ) * k),
        ((u (A i * f k + (1 - δ) * k - k') : ℝ) : EReal) +
          (β : EReal) * vstar (periodicGamma A f δ) (periodicF A u f δ) β (k', !i) := by
  rw [eq_4_22 hβ h41 h42 (k, i), periodicGamma, iSup_image]
  rfl

/-- **AKMM, p. 118, corrected.** The printed `Γ_i(k) = [0, A_if(k) + (1 − δ)k − k']`, read as a
constraint on `k'`, is `0 ≤ k' ≤ (A_if(k) + (1 − δ)k)/2`: it excludes, e.g., consuming nothing,
`k' = A_if(k) + (1 − δ)k > 0`, which the resource constraint allows. -/
theorem periodic_printed_gamma {R : ℝ} (hR : 0 < R) :
    (∀ k', k' ∈ Set.Icc 0 (R - k') ↔ 0 ≤ k' ∧ 2 * k' ≤ R) ∧ R ∈ Set.Icc 0 R ∧
      R ∉ Set.Icc 0 (R - R) := by
  refine ⟨fun k' => ?_, ⟨hR.le, le_rfl⟩, fun h => ?_⟩
  · rw [Set.mem_Icc]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · have := h.2; linarith

/-- The delayed-depreciation NGM in the state `(i_{t−1}, i_{t−2})`, with
`k_t = i_{t−1} + i_{t−2}`: `Γ̃(i', i) = {(i'', i') : 0 ≤ i'' ≤ f(i' + i)}`. -/
def delayedGamma (f : ℝ → ℝ) (s : ℝ × ℝ) : Set (ℝ × ℝ) :=
  (fun i'' => (i'', s.1)) '' Set.Icc 0 (f (s.1 + s.2))

/-- The delayed-depreciation return `u(f(i' + i) − i'')`. -/
noncomputable def delayedF (u f : ℝ → ℝ) (s s' : ℝ × ℝ) : ℝ := u (f (s.1 + s.2) - s'.1)

/-- **AKMM, p. 118, corrected: the delayed-depreciation NGM.** The value function satisfies
`V(i', i) = max_{0 ≤ i'' ≤ f(i' + i)} {u(f(i' + i) − i'') + βV(i'', i')}`; the book omits `β`. -/
theorem delayed_bellman {u f : ℝ → ℝ} {β : ℝ} (hβ : 0 ≤ β) (h41 : Assumption41 (delayedGamma f))
    (h42 : Assumption42 (delayedGamma f) (delayedF u f) β) (i' i : ℝ) :
    vstar (delayedGamma f) (delayedF u f) β (i', i) =
      ⨆ i'' ∈ Set.Icc 0 (f (i' + i)), ((u (f (i' + i) - i'') : ℝ) : EReal) +
        (β : EReal) * vstar (delayedGamma f) (delayedF u f) β (i'', i') := by
  rw [eq_4_22 hβ h41 h42 (i', i), delayedGamma, iSup_image]
  rfl

/-- The undiscounted operator printed on p. 118:
`(Tv)(i', i) = sup_{0 ≤ i'' ≤ f(i' + i)} {u(f(i' + i) − i'') + v(i'', i')}`. -/
noncomputable def delayedPrinted (u f : ℝ → ℝ) (v : ℝ × ℝ → ℝ) (s : ℝ × ℝ) : ℝ :=
  ⨆ y : Set.Icc (0 : ℝ) (f (s.1 + s.2)), u (f (s.1 + s.2) - y.1) + v (y.1, s.1)

/-- **AKMM, p. 118 and fn. 15: without `β` the Bellman operator is not a contraction.** With `u`
nondecreasing and `f ≥ 0`, the printed operator satisfies `T(0 + c) = T0 + c`, so no modulus
`β' < 1` bounds `|Tv − Tw|` by `β'` times a bound on `|v − w|`. -/
theorem delayed_no_discount_not_contraction {u f : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0))
    (hf : ∀ x, 0 ≤ f x) :
    (∀ c s, delayedPrinted u f (fun _ => c) s = delayedPrinted u f (fun _ => 0) s + c) ∧
    ¬ ∃ β' < 1, ∀ v w : ℝ × ℝ → ℝ, (∀ s, |v s - w s| ≤ 1) →
      ∀ s, |delayedPrinted u f v s - delayedPrinted u f w s| ≤ β' := by
  have hshift : ∀ c s, delayedPrinted u f (fun _ => c) s =
      delayedPrinted u f (fun _ => 0) s + c := by
    intro c s
    have hne : Nonempty (Set.Icc (0 : ℝ) (f (s.1 + s.2))) :=
      ⟨⟨0, le_rfl, hf _⟩⟩
    have hbdd : BddAbove (Set.range fun y : Set.Icc (0 : ℝ) (f (s.1 + s.2)) =>
        u (f (s.1 + s.2) - y.1) + 0) := by
      refine ⟨u (f (s.1 + s.2)) + 0, ?_⟩
      rintro _ ⟨y, rfl⟩
      have := hu (Set.mem_Ici.2 (by linarith [y.2.2])) (Set.mem_Ici.2 (hf _))
        (by linarith [y.2.1] : f (s.1 + s.2) - y.1 ≤ f (s.1 + s.2))
      simp only [add_zero]
      exact this
    have := (OrderIso.addRight c).map_ciSup hbdd
    simp only [OrderIso.addRight_apply] at this
    simp only [delayedPrinted]
    rw [this]
    simp only [add_zero]
  refine ⟨hshift, fun ⟨β', hβ', h⟩ => ?_⟩
  have := h (fun _ => 1) (fun _ => 0) (fun _ => by norm_num) (0, 0)
  rw [hshift 1] at this
  simp only [add_sub_cancel_left, abs_one] at this
  linarith

/-- **AKMM, p. 119, property 1: value-function iteration.** Under SLP's Assumptions 4.3–4.4
(`Γ` nonempty, compact-valued and continuous; `F` bounded and continuous; `0 < β < 1`) the
Bellman operator has a unique fixed point `V`, the iterates satisfy
`‖V_{n+1} − V‖ ≤ β‖V_n − V‖`, and so `‖V_n − V‖ ≤ βⁿ‖V_0 − V‖ → 0` (SLP Theorem 4.6). -/
theorem property_1 {X : Type*} [MetricSpace X] [Nonempty X] {Γ : X → Set X} {F : X × X → ℝ}
    {β : ℝ} (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) :
    ∃ V : X →ᵇ ℝ, bellman h43 h44 V = V ∧ (∀ W, bellman h43 h44 W = W → W = V) ∧
      (∀ V₀ (n : ℕ), dist ((bellman h43 h44)^[n + 1] V₀) V ≤
        β * dist ((bellman h43 h44)^[n] V₀) V) ∧
      (∀ V₀ (n : ℕ), dist ((bellman h43 h44)^[n] V₀) V ≤ β ^ n * dist V₀ V) ∧
      ∀ V₀, Tendsto (fun n => (bellman h43 h44)^[n] V₀) atTop (𝓝 V) := by
  obtain ⟨V, hV, huniq, hrate, -⟩ := theorem_4_6 h43 h44
  have hc := bellman_contraction h43 h44
  refine ⟨V, hV, huniq, fun V₀ n => ?_, hrate, fun V₀ => ?_⟩
  · rw [Function.iterate_succ_apply']
    conv_lhs => rw [← hV]
    exact hc.2.2 _ _
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (hrate V₀) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h44.β_pos.le h44.β_lt).mul_const
      (dist V₀ V)

/-- **AKMM, p. 120, property 2.** If `F` is strictly increasing in its first argument and `Γ` is
monotone (`x ≤ x̃ ⇒ Γ(x) ⊆ Γ(x̃)`), `V` is strictly increasing (SLP Theorem 4.7). -/
theorem property_2 {X : Type*} [MetricSpace X] [Nonempty X] [PartialOrder X] {Γ : X → Set X}
    {F : X × X → ℝ} {β : ℝ} (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h45 : ∀ x x' y, x < x' → y ∈ Γ x → F (x, y) < F (x', y))
    (h46 : ∀ x x', x ≤ x' → Γ x ⊆ Γ x') {V : X →ᵇ ℝ} (hV : bellman h43 h44 V = V) :
    StrictMono V :=
  theorem_4_7 h43 h44 h45 h46 hV

/-- **AKMM, p. 120, property 3.** If `F` is strictly concave and `Γ` convex
(`x' ∈ Γ(x), x̃' ∈ Γ(x̃) ⇒ θx' + (1 − θ)x̃' ∈ Γ(θx + (1 − θ)x̃)`), `V` is strictly concave and the
policy is unique (and continuous) (SLP Theorem 4.8). -/
theorem property_3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    [Nonempty S] {hS : Convex ℝ S} {Γ : S → Set S} {F : S × S → ℝ} {β : ℝ}
    (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) (h47 : Assumption47 hS Γ F)
    (h48 : Assumption48 hS Γ) {V : S →ᵇ ℝ} (hV : bellman h43 h44 V = V) :
    IsStrictConcaveS hS V ∧ (∀ x, argmax (obj F β V) Γ x = {argmaxFn Γ (obj F β V) x}) ∧
      Continuous (argmaxFn Γ (obj F β V)) := by
  obtain ⟨h1, -, h3, h4⟩ := theorem_4_8 h43 h44 h47 h48 hV
  exact ⟨h1, h3, h4⟩

/-- **AKMM, p. 120, property 4, and the envelope theorem (p. 122).** Let `V` be concave near
`x₀`, satisfy the Bellman inequality `F(x, x') + βV(x') ≤ V(x)` for `x' ∈ Γ(x)`, with equality at
`x' = g(x₀)`, and let the choice be interior (`g(x₀) ∈ Γ(x)` for `x` near `x₀`). If `F(·, g(x₀))`
is differentiable at `x₀`, then `V` is differentiable there and `V'(x₀) = F₁(x₀, g(x₀))`
(Benveniste–Scheinkman, SLP Theorem 4.10). -/
theorem property_4 {V : ℝ → ℝ} {S : Set ℝ} (hV : ConcaveOn ℝ S V) {x₀ y₀ : ℝ} (hS : S ∈ 𝓝 x₀)
    {Γ : ℝ → Set ℝ} {F : ℝ → ℝ → ℝ} {β F1 : ℝ}
    (hbell : ∀ x, ∀ y ∈ Γ x, F x y + β * V y ≤ V x) (heq : V x₀ = F x₀ y₀ + β * V y₀)
    (hint : ∀ᶠ x in 𝓝 x₀, y₀ ∈ Γ x) (hF : HasDerivAt (fun x => F x y₀) F1 x₀) :
    HasDerivAt V F1 x₀ := by
  have hW : HasDerivAt (fun x => F x y₀ + β * V y₀) F1 x₀ := hF.add_const _
  have := theorem_4_10 hV hS hW.hasFDerivAt heq.symm
    (hint.mono fun x hx => hbell x y₀ hx)
  simpa using this.hasDerivAt

/-- The return of the counterexample to property 5: `F(x, y) = 3x − x² − (y − 1 + x/2)²` on
`[0, 1]²`. -/
noncomputable def prop5F (x y : ℝ) : ℝ := 3 * x - x ^ 2 - (y - 1 + x / 2) ^ 2

/-- **AKMM, p. 120, property 5 is false as stated.** `F(x, y) = 3x − x² − (y − 1 + x/2)²` with
`X = [0, 1]` and `Γ(x) = [0, 1]` (monotone and convex) is jointly strictly concave, strictly
increasing in `x` and smooth. Yet for every continuous `V` on `[0, 1]` — in particular the
solution of the Bellman equation — a policy `g` (a maximizer of `F(x, y) + βV(y)` over `y`)
exists, and no policy is strictly increasing: since `F₁₂ < 0`, maximizers move down as `x`
rises. -/
theorem property_5_counterexample :
    StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (fun p => prop5F p.1 p.2) ∧
    (∀ y ∈ Set.Icc (0 : ℝ) 1, StrictMonoOn (fun x => prop5F x y) (Set.Icc 0 1)) ∧
    ContDiff ℝ 1 (fun p : ℝ × ℝ => prop5F p.1 p.2) ∧
    ∀ (β : ℝ) (V : ℝ → ℝ), ContinuousOn V (Set.Icc 0 1) →
      (∃ g : ℝ → ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ∈ Set.Icc (0 : ℝ) 1 ∧
        ∀ y ∈ Set.Icc (0 : ℝ) 1, prop5F x y + β * V y ≤ prop5F x (g x) + β * V (g x)) ∧
      ∀ g : ℝ → ℝ, (∀ x ∈ Set.Icc (0 : ℝ) 1, g x ∈ Set.Icc (0 : ℝ) 1 ∧
        ∀ y ∈ Set.Icc (0 : ℝ) 1, prop5F x y + β * V y ≤ prop5F x (g x) + β * V (g x)) →
        ¬ StrictMonoOn g (Set.Icc 0 1) := by
  refine ⟨⟨(convex_Icc 0 1).prod (convex_Icc 0 1), fun p hp q hq hpq a b ha hb hab => ?_⟩,
    fun y hy x hx x' hx' hxx' => ?_, ?_, fun β V hV => ⟨?_, fun g hg hmono => ?_⟩⟩
  · -- `θF(p) + (1 − θ)F(q) = F(θp + (1 − θ)q) − θ(1 − θ)Q(p − q)`, `Q` positive definite
    simp only [prop5F, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    have hQ : 0 < (p.1 - q.1) ^ 2 + (p.2 - q.2 + (p.1 - q.1) / 2) ^ 2 := by
      by_contra hcon
      push Not at hcon
      have h1 : (p.1 - q.1) ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (p.2 - q.2 +
        (p.1 - q.1) / 2)]) (sq_nonneg _)
      have h1' : p.1 = q.1 := by nlinarith [sq_nonneg (p.1 - q.1)]
      have h2 : (p.2 - q.2 + (p.1 - q.1) / 2) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1)]
      have h2' : p.2 = q.2 := by rw [h1'] at h2; nlinarith [sq_nonneg (p.2 - q.2)]
      exact hpq (Prod.ext h1' h2')
    have hab' : 0 < a * (1 - a) := mul_pos ha hb
    nlinarith [mul_pos hab' hQ]
  · simp only [prop5F]
    have := hx.1; have := hx'.2; have := hy.2
    nlinarith [mul_pos (sub_pos.2 hxx') (show 0 < 4 - y - 5 / 4 * (x + x') by linarith)]
  · simp only [prop5F]
    fun_prop
  · -- a maximizer exists for each `x`: continuity on the compact `[0, 1]`
    have hex : ∀ x : ℝ, ∃ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
        prop5F x z + β * V z ≤ prop5F x y + β * V y := by
      intro x
      have hc : ContinuousOn (fun z => prop5F x z + β * V z) (Set.Icc 0 1) :=
        (Continuous.continuousOn (by unfold prop5F; fun_prop)).add (continuousOn_const.mul hV)
      obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 zero_le_one) hc
      exact ⟨y, hy, fun z hz => hmax hz⟩
    choose g hg using hex
    exact ⟨g, fun x _ => ⟨(hg x).1, (hg x).2⟩⟩
  · have h0 := hg 0 ⟨le_rfl, zero_le_one⟩
    have h1 := hg 1 ⟨zero_le_one, le_rfl⟩
    have hlt := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
    have a1 := h0.2 (g 1) h1.1
    have a2 := h1.2 (g 0) h0.1
    simp only [prop5F] at a1 a2
    nlinarith

/-- **AKMM, p. 120, property 5, corrected (Topkis).** With `Γ(x) = [x̲, γ(x)]`, `γ` nondecreasing,
and strictly increasing differences
`F(x₂, y₂) − F(x₂, y₁) > F(x₁, y₂) − F(x₁, y₁)` for `x₁ < x₂`, `y₁ < y₂` (`F₁₂ > 0` for smooth
`F`), maximizers of `F(x, y) + βV(y)` are nondecreasing in `x`, for every `V`. -/
theorem property_5_corrected {F : ℝ → ℝ → ℝ} {V : ℝ → ℝ} {β lo : ℝ} {γ : ℝ → ℝ}
    (hγ : Monotone γ)
    (hid : ∀ x₁ x₂ y₁ y₂, x₁ < x₂ → y₁ < y₂ → F x₁ y₂ - F x₁ y₁ < F x₂ y₂ - F x₂ y₁)
    {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ < x₂) (hy₁ : y₁ ∈ Set.Icc lo (γ x₁))
    (hy₂ : y₂ ∈ Set.Icc lo (γ x₂))
    (hmax₁ : ∀ y ∈ Set.Icc lo (γ x₁), F x₁ y + β * V y ≤ F x₁ y₁ + β * V y₁)
    (hmax₂ : ∀ y ∈ Set.Icc lo (γ x₂), F x₂ y + β * V y ≤ F x₂ y₂ + β * V y₂) : y₁ ≤ y₂ := by
  by_contra hcon
  push Not at hcon
  have a1 := hmax₁ y₂ ⟨hy₂.1, by linarith [hy₁.2]⟩
  have a2 := hmax₂ y₁ ⟨hy₁.1, hy₁.2.trans (hγ hx.le)⟩
  have := hid x₁ x₂ y₂ y₁ hx hcon
  linarith

/-- **AKMM, p. 120, property 5 in the NGM.** In SLP's §6.1 setting (`U`, `f` strictly increasing,
strictly concave, `C¹`, with Inada conditions; `f` is total resources), the optimal policy is
strictly increasing on `[0, k̄]` (SLP Exercise 6.1b). -/
theorem property_5_ngm {U f U' f' : ℝ → ℝ} {β kbar : ℝ} [Nonempty (Set.Icc (0 : ℝ) kbar)]
    {v : Set.Icc (0 : ℝ) kbar →ᵇ ℝ}
    (S : StokeyLucasPrescott.DeterministicDynamics.Setting61 U f U' f' β kbar v) :
    StrictMonoOn (StokeyLucasPrescott.DeterministicDynamics.gpol U f β kbar v) (Set.Icc 0 kbar) :=
  StokeyLucasPrescott.DeterministicDynamics.ex_6_1b S

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Solving for the value function and the functional Euler equation

AKMM, §4.4.4–4.4.5, Examples 4.7–4.8, pp. 120–123. `u = log`, `f(k) = Ak^α`, `δ = 1`; choices
`k' ∈ (0, Ak^α)` (consumption and next capital positive, as the logarithm requires).

* `vfe_log_max`: `log(Y − k') + B log k'` is maximized over `(0, Y)` at `k' = BY/(1 + B)`.
* (4.23): `V₁(k) = log A + α log k`, attained at `k' = 0` (`eq_4_23`).
* `V₂(k) = a₂ + b₂ log k` with the book's `a₂`, `b₂ = α + α²β`, attained at
  `k' = αβAk^α/(1 + αβ)` (`example_4_7_V2`); in general `T` maps `a' + b' log k` to
  `a'' + α(1 + βb') log k` (`example_4_7_iterate`), so `b_n = α(1 − (αβ)ⁿ)/(1 − αβ) → b`
  (`example_4_7_coefficients`).
* Guess and verify: `V = a + b log k` with `b = α/(1 − αβ)` and the printed `a` solves the
  Bellman equation, with policy `k' = αβAk^α` (`example_4_7`).
* (4.25): the first-order condition and the envelope condition give the functional Euler
  equation (`eq_4_25`); Example 4.8: `g(k) = sAk^α` solves it iff `s = αβ` (`example_4_8`).
-/

namespace AKMM.DynamicOptimization

open Real

/-- AKMM, p. 121: for `Y > 0`, `B > 0`, `log(Y − k') + B log k'` is maximized over `(0, Y)` at
`k' = BY/(1 + B)` (the first-order condition `1/(Y − k') = B/k'`). -/
theorem vfe_log_max {Y B : ℝ} (hY : 0 < Y) (hB : 0 < B) {k' : ℝ} (hk0 : 0 < k') (hk1 : k' < Y) :
    Real.log (Y - k') + B * Real.log k' ≤
      Real.log (Y - B * Y / (1 + B)) + B * Real.log (B * Y / (1 + B)) := by
  set ks := B * Y / (1 + B)
  have hks : 0 < ks := by positivity
  have hY' : Y - ks = Y / (1 + B) := by simp only [ks]; field_simp; ring
  have hYks : 0 < Y - ks := by rw [hY']; positivity
  have h1 := Real.log_le_sub_one_of_pos (div_pos (sub_pos.2 hk1) hYks)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hk0 hks)
  rw [Real.log_div (sub_pos.2 hk1).ne' hYks.ne'] at h1
  rw [Real.log_div hk0.ne' hks.ne'] at h2
  have e : (Y - k') / (Y - ks) - 1 + B * (k' / ks - 1) = 0 := by
    rw [hY']; simp only [ks]; field_simp; ring
  nlinarith

/-- **AKMM, (4.23), p. 121.** `V₁(k) = max_{k' ≥ 0} log(Ak^α − k') = log A + α log k`, attained at
`k' = 0`. -/
theorem eq_4_23 {A α k : ℝ} (hA : 0 < A) (hk : 0 < k) :
    (∀ k' ∈ Set.Ico 0 (A * k ^ α), Real.log (A * k ^ α - k') ≤ Real.log (A * k ^ α - 0)) ∧
      Real.log (A * k ^ α - 0) = Real.log A + α * Real.log k := by
  have hP : 0 < A * k ^ α := mul_pos hA (rpow_pos_of_pos hk α)
  refine ⟨fun k' hk' => Real.log_le_log (by linarith [hk'.2]) (by linarith [hk'.1]), ?_⟩
  rw [sub_zero, Real.log_mul hA.ne' (rpow_pos_of_pos hk α).ne', Real.log_rpow hk]

/-- **AKMM, Example 4.7, p. 121: one Bellman step on `a' + b' log k`.** For `b' > 0`,
`max_{0<k'<Ak^α} {log(Ak^α − k') + β(a' + b' log k')}` is attained at
`k' = βb'Ak^α/(1 + βb')`, with value `a'' + α(1 + βb') log k`, where
`a'' = log(A − βb'A/(1 + βb')) + βa' + βb' log(βb'A/(1 + βb'))`. -/
theorem example_4_7_iterate {A α β a' b' k : ℝ} (hA : 0 < A) (hβ : 0 < β) (hb : 0 < b')
    (hk : 0 < k) :
    (∀ k' ∈ Set.Ioo 0 (A * k ^ α), Real.log (A * k ^ α - k') + β * (a' + b' * Real.log k') ≤
      Real.log (A * k ^ α - β * b' * (A * k ^ α) / (1 + β * b')) +
        β * (a' + b' * Real.log (β * b' * (A * k ^ α) / (1 + β * b')))) ∧
    Real.log (A * k ^ α - β * b' * (A * k ^ α) / (1 + β * b')) +
        β * (a' + b' * Real.log (β * b' * (A * k ^ α) / (1 + β * b'))) =
      (Real.log (A - β * b' * A / (1 + β * b')) + β * a' +
        β * b' * Real.log (β * b' * A / (1 + β * b'))) + α * (1 + β * b') * Real.log k := by
  have hB : 0 < β * b' := mul_pos hβ hb
  have hP : 0 < k ^ α := rpow_pos_of_pos hk α
  have hY : 0 < A * k ^ α := mul_pos hA hP
  refine ⟨fun k' hk' => ?_, ?_⟩
  · have := vfe_log_max hY hB hk'.1 hk'.2
    nlinarith
  · have hc : 0 < A - β * b' * A / (1 + β * b') := by
      rw [show A - β * b' * A / (1 + β * b') = A / (1 + β * b') by field_simp; ring]
      positivity
    have hd : 0 < β * b' * A / (1 + β * b') := by positivity
    rw [show A * k ^ α - β * b' * (A * k ^ α) / (1 + β * b') =
        (A - β * b' * A / (1 + β * b')) * k ^ α by ring,
      show β * b' * (A * k ^ α) / (1 + β * b') = β * b' * A / (1 + β * b') * k ^ α by ring,
      Real.log_mul hc.ne' hP.ne', Real.log_mul hd.ne' hP.ne', Real.log_rpow hk]
    ring

/-- **AKMM, Example 4.7, p. 121: `V₂`.** With `V₁ = log A + α log k`, the second iterate is
`V₂(k) = a₂ + b₂ log k`, `a₂ = log(A − αβA/(1 + αβ)) + β log A + αβ log(αβA/(1 + αβ))`,
`b₂ = α + α²β`, attained at `k' = αβAk^α/(1 + αβ)`. -/
theorem example_4_7_V2 {A α β k : ℝ} (hA : 0 < A) (hα : 0 < α) (hβ : 0 < β) (hk : 0 < k) :
    (∀ k' ∈ Set.Ioo 0 (A * k ^ α), Real.log (A * k ^ α - k') + β * (Real.log A + α * Real.log k') ≤
      Real.log (A * k ^ α - α * β * A * k ^ α / (1 + α * β)) +
        β * (Real.log A + α * Real.log (α * β * A * k ^ α / (1 + α * β)))) ∧
    Real.log (A * k ^ α - α * β * A * k ^ α / (1 + α * β)) +
        β * (Real.log A + α * Real.log (α * β * A * k ^ α / (1 + α * β))) =
      (Real.log (A - α * β * A / (1 + α * β)) + β * Real.log A +
        α * β * Real.log (α * β * A / (1 + α * β))) + (α + α ^ 2 * β) * Real.log k := by
  obtain ⟨h1, h2⟩ := example_4_7_iterate (a' := Real.log A) hA hβ hα hk
  have e1 : β * α * (A * k ^ α) / (1 + β * α) = α * β * A * k ^ α / (1 + α * β) := by ring
  have e2 : β * α * A / (1 + β * α) = α * β * A / (1 + α * β) := by ring
  rw [e1] at h1 h2
  rw [e2] at h2
  refine ⟨h1, ?_⟩
  rw [h2]
  ring

/-- AKMM, Example 4.7, p. 121: the coefficients `b_n = α(1 − (αβ)ⁿ)/(1 − αβ)` of
`V_n = a_n + b_n log k` start at `b₁ = α`, `b₂ = α + α²β`, satisfy `b_{n+1} = α(1 + βb_n)`, and
converge to `b = α/(1 − αβ)`. -/
theorem example_4_7_coefficients {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    (α * (1 - (α * β) ^ 1) / (1 - α * β) = α) ∧
    (α * (1 - (α * β) ^ 2) / (1 - α * β) = α + α ^ 2 * β) ∧
    (∀ n : ℕ, α * (1 - (α * β) ^ (n + 1)) / (1 - α * β) =
      α * (1 + β * (α * (1 - (α * β) ^ n) / (1 - α * β)))) ∧
    Filter.Tendsto (fun n : ℕ => α * (1 - (α * β) ^ n) / (1 - α * β)) Filter.atTop
      (nhds (α / (1 - α * β))) := by
  have hq0 : 0 < α * β := mul_pos hα0 hβ0
  have hq1 : α * β < 1 := by nlinarith
  have hne : (1 - α * β) ≠ 0 := by linarith
  refine ⟨by rw [div_eq_iff hne]; ring, by rw [div_eq_iff hne]; ring, fun n => ?_, ?_⟩
  · have hne' : 1 - β * α ≠ 0 := by rw [mul_comm]; exact hne
    field_simp
    ring
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_sub 1).const_mul α
  simpa using this.div_const (1 - α * β)

/-- **Example 4.7** (AKMM, p. 121): guess and verify. With `b = α/(1 − αβ)` and
`a = (1/(1 − β))(1/(1 − αβ))(log A + (1 − αβ) log(1 − αβ) + αβ log(αβ))`, `V(k) = a + b log k`
solves the Bellman equation `V(k) = max_{0<k'<Ak^α} {log(Ak^α − k') + βV(k')}`, and the maximum is
attained at `k' = αβAk^α`, the policy of the sequential approach. -/
theorem example_4_7 {A α β k : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hk : 0 < k) :
    (∀ k' ∈ Set.Ioo 0 (A * k ^ α), Real.log (A * k ^ α - k') +
        β * ((1 / (1 - β)) * (1 / (1 - α * β)) * (Real.log A + (1 - α * β) *
          Real.log (1 - α * β) + α * β * Real.log (α * β)) +
          α / (1 - α * β) * Real.log k') ≤
      (1 / (1 - β)) * (1 / (1 - α * β)) * (Real.log A + (1 - α * β) * Real.log (1 - α * β) +
        α * β * Real.log (α * β)) + α / (1 - α * β) * Real.log k) ∧
    Real.log (A * k ^ α - α * β * A * k ^ α) +
        β * ((1 / (1 - β)) * (1 / (1 - α * β)) * (Real.log A + (1 - α * β) *
          Real.log (1 - α * β) + α * β * Real.log (α * β)) +
          α / (1 - α * β) * Real.log (α * β * A * k ^ α)) =
      (1 / (1 - β)) * (1 / (1 - α * β)) * (Real.log A + (1 - α * β) * Real.log (1 - α * β) +
        α * β * Real.log (α * β)) + α / (1 - α * β) * Real.log k := by
  have hq0 : 0 < α * β := mul_pos hα0 hβ0
  have hq1 : α * β < 1 := by nlinarith
  have h1q : 0 < 1 - α * β := by linarith
  set a := (1 / (1 - β)) * (1 / (1 - α * β)) * (Real.log A + (1 - α * β) *
    Real.log (1 - α * β) + α * β * Real.log (α * β))
  set b := α / (1 - α * β)
  have hb : 0 < b := div_pos hα0 h1q
  have hβb : β * b / (1 + β * b) = α * β := by
    have hne' : 1 - β * α ≠ 0 := by nlinarith
    rw [div_eq_iff (by positivity)]
    simp only [b]
    field_simp
    ring
  have hP : 0 < k ^ α := rpow_pos_of_pos hk α
  have hpol : β * b * (A * k ^ α) / (1 + β * b) = α * β * A * k ^ α := by
    rw [show β * b * (A * k ^ α) / (1 + β * b) = β * b / (1 + β * b) * (A * k ^ α) by ring,
      hβb]; ring
  have hval : Real.log (A * k ^ α - α * β * A * k ^ α) +
      β * (a + b * Real.log (α * β * A * k ^ α)) = a + b * Real.log k := by
    rw [show A * k ^ α - α * β * A * k ^ α = (1 - α * β) * A * k ^ α by ring,
      Real.log_mul (mul_pos h1q hA).ne' hP.ne', Real.log_mul h1q.ne' hA.ne',
      show α * β * A * k ^ α = (α * β) * A * k ^ α by ring,
      Real.log_mul (mul_pos hq0 hA).ne' hP.ne', Real.log_mul hq0.ne' hA.ne', Real.log_rpow hk]
    simp only [a, b]
    have h1β : (1 - β) ≠ 0 := by linarith
    field_simp
    ring
  obtain ⟨h1, -⟩ := example_4_7_iterate (a' := a) hA hβ0 hb hk
  rw [hpol] at h1
  exact ⟨fun k' hk' => (h1 k' hk').trans_eq hval, hval⟩

/-- **AKMM, (4.25), p. 122: the functional Euler equation.** If the policy satisfies the
first-order condition `F₂(x, g(x)) + βV'(g(x)) = 0` and the envelope condition
`V'(x) = F₁(x, g(x))` (`property_4`) for all `x`, then
`F₂(x, g(x)) + βF₁(g(x), g(g(x))) = 0` for all `x`. -/
theorem eq_4_25 {g V' : ℝ → ℝ} {F1 F2 : ℝ → ℝ → ℝ} {β : ℝ}
    (hfoc : ∀ x, F2 x (g x) + β * V' (g x) = 0) (henv : ∀ x, V' x = F1 x (g x)) (x : ℝ) :
    F2 x (g x) + β * F1 (g x) (g (g x)) = 0 := by
  rw [← henv]; exact hfoc x

/-- **Example 4.8** (AKMM, p. 123). With `F(k, k') = log(Ak^α − k')`,
`F₁ = αAk^{α−1}/(Ak^α − k')` and `F₂ = −1/(Ak^α − k')`, the guess `g(k) = sAk^α`, `0 < s < 1`,
solves the functional Euler equation (4.25) at `k > 0` iff `s = αβ` (Example 4.6, with
`g(g(k)) = sA(sAk^α)^α`). -/
theorem example_4_8 {A α β s k : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hβ0 : 0 < β) (hs0 : 0 < s)
    (hs1 : s < 1) (hk : 0 < k) :
    -(1 / (A * k ^ α - s * A * k ^ α)) +
        β * (α * A * (s * A * k ^ α) ^ (α - 1) /
          (A * (s * A * k ^ α) ^ α - s * A * (s * A * k ^ α) ^ α)) = 0 ↔ s = α * β := by
  rw [← example_4_6 hA hα0 hβ0 hs0 hs1 hk]
  constructor <;> intro h
  · rw [mul_div_assoc] at *; linarith
  · rw [h]; ring

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dynamics in the optimizing neoclassical growth model

AKMM, §4.4.6, pp. 123–127. `h(k) = f(k) + (1 − δ)k` are total resources, `c = h(k) − g(k)`.

* The maximum sustainable capital `k^u`: the only positive solution of `h(k) = k`, and
  `k ≤ k^u ⇒ h(k) ≤ k^u` (`ngm_max_capital`).
* (4.26)–(4.27): the functional Euler equation of the NGM (`eq_4_26`) and its steady state
  `1 = β(f'(k̄) + 1 − δ)` (`eq_4_27`).
* (4.28): concavity of `V` with the envelope and first-order conditions gives
  `u'(c)[f'(k) + 1 − δ − 1/β][k − g(k)] ≤ 0` (`eq_4_28`); with `c = f(k) + (1 − δ)k − g(k)`, not
  `f(k) − g(k)` as printed. With `V` strictly concave, `g(k) < k` above `k̄` and `g(k) > k` below
  (`ngm_policy_direction`), and then every path converges monotonically to `k̄`
  (`ngm_global_convergence`). For `δ = 1` this is unconditional (`ngm_global_convergence_full`,
  SLP Proposition 6.1).
* (4.29): differentiating (4.26) at `k̄` gives `u''[1 − βa₁] = u''[a₁ − βa₁²] + β²u'f''a₁` for
  `a₁ = g'(k̄)` (`eq_4_29`), i.e. `βa₁² − (1 + β + Θ)a₁ + 1 = 0`, `Θ = β²u'f''/u''`
  (`eq_4_29_quadratic`).
* (4.30): the root `a₁ = (1 + β + Θ − √((1 + β + Θ)² − 4β))/(2β)` (`slopeRoot`): it solves the
  quadratic (`slopeRoot_isRoot`), lies in `(0, 1)` with the other root above `1` for `Θ > 0`
  (`slopeRoot_mem`), equals `1` at `Θ = 0` (`slopeRoot_zero`), is decreasing in `Θ`
  (`slopeRoot_strictAnti`), tends to `0` as `Θ → ∞` (`slopeRoot_tendsto_zero`) and to `1` as
  `Θ → 0` (`slopeRoot_tendsto_one`).
* Calibration: with CRRA utility `Θ = −β²f''(k̄)(f(k̄) − δk̄)/σ` (`theta_crra`), positive and
  decreasing in `σ` (`theta_crra_strictAnti`); with `f(k) = k^α` the book's closed form
  (`theta_cobbDouglas`), decreasing in `α` (`theta_cobbDouglas_strictAnti_alpha`) and increasing
  in `δ` (`theta_cobbDouglas_strictMono_delta`).
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real BoundedContinuousFunction

/-- **AKMM, pp. 123–124: the maximum sustainable capital stock.** Let `f(0) = 0`, `f` strictly
concave on `[0, ∞)`, continuous on `(0, ∞)`, with `f(k)/k → ∞` as `k → 0⁺` and `f(k)/k → 0` as
`k → ∞`, and `0 < δ`. There is a unique `k^u > 0` with `f(k^u) + (1 − δ)k^u = k^u`; the solutions of
`h(k) = k` on `[0, ∞)` are `0` and `k^u`; and if `h` is nondecreasing, `0 ≤ k ≤ k^u` implies
`h(k) ≤ k^u`. -/
theorem ngm_max_capital {f : ℝ → ℝ} (hf0 : f 0 = 0) (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hcont : ContinuousOn f (Set.Ioi 0)) (h0 : Tendsto (fun k => f k / k) (𝓝[>] 0) atTop)
    (htop : Tendsto (fun k => f k / k) atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ku, 0 < ku ∧ f ku + (1 - δ) * ku = ku ∧
      (∀ k, 0 ≤ k → (f k + (1 - δ) * k = k ↔ k = 0 ∨ k = ku)) ∧
      (MonotoneOn (fun k => f k + (1 - δ) * k) (Set.Ici 0) →
        ∀ k, 0 ≤ k → k ≤ ku → f k + (1 - δ) * k ≤ ku) := by
  -- the average product `f(k)/k` is strictly decreasing
  have hanti : StrictAntiOn (fun k => f k / k) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := hx
    have hy0 : 0 < y := hy
    have ht : 0 < x / y := div_pos hx0 hy0
    have ht1 : x / y < 1 := (div_lt_one hy0).2 hxy
    have := hconc.2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy0.le) hy0.ne
      (by linarith : 0 < 1 - x / y)
      ht (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, hf0] at this
    rw [div_mul_cancel₀ x hy0.ne'] at this
    simp only
    rw [div_lt_div_iff₀ hy0 hx0]
    have := mul_lt_mul_of_pos_right this hy0
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hy0.ne'] at this
    linarith
  have hfix : ∀ k, 0 < k → (f k + (1 - δ) * k = k ↔ f k / k = δ) := fun k hk => by
    rw [div_eq_iff hk.ne']; constructor <;> intro h <;> linarith
  obtain ⟨a, ha, ha0⟩ := ((h0.eventually (eventually_gt_atTop δ)).and
    self_mem_nhdsWithin).exists
  obtain ⟨b, hb, hab⟩ := ((htop.eventually (gt_mem_nhds hδ)).and
    (eventually_ge_atTop a)).exists
  have ha0' : 0 < a := ha0
  have hcont' : ContinuousOn (fun k => f k / k) (Set.Icc a b) :=
    ((hcont.mono fun x hx => lt_of_lt_of_le ha0' hx.1).div continuousOn_id fun x hx =>
      (lt_of_lt_of_le ha0' hx.1).ne')
  obtain ⟨ku, hku, hfku⟩ := intermediate_value_Icc' hab hcont' ⟨hb.le, ha.le⟩
  have hku0 : 0 < ku := lt_of_lt_of_le ha0' hku.1
  have hfix_ku : f ku + (1 - δ) * ku = ku := (hfix ku hku0).2 hfku
  refine ⟨ku, hku0, hfix_ku, fun k hk => ⟨fun h => ?_, ?_⟩, fun hmono k hk hkk => ?_⟩
  · rcases eq_or_lt_of_le hk with rfl | hpos
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h1 := (hfix k hpos).1 h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := hanti hpos hku0 hlt; simp only at this; linarith
      · have := hanti hku0 hpos hlt; simp only at this; linarith
  · rintro (rfl | rfl)
    · simp [hf0]
    · exact hfix_ku
  · have := hmono (Set.mem_Ici.2 hk) (Set.mem_Ici.2 hku0.le) hkk
    simp only at this
    linarith

/-- **AKMM, (4.26), p. 124: the functional Euler equation of the NGM.** If the policy satisfies
the first-order condition `u'(h(k) − g(k)) = βV'(g(k))` and the envelope condition
`V'(k) = u'(h(k) − g(k))h'(k)` for all `k`, then
`u'(h(k) − g(k)) = βu'(h(g(k)) − g(g(k)))h'(g(k))`. -/
theorem eq_4_26 {u' h h' g V' : ℝ → ℝ} {β : ℝ}
    (hfoc : ∀ k, u' (h k - g k) = β * V' (g k))
    (henv : ∀ k, V' k = u' (h k - g k) * h' k) (k : ℝ) :
    u' (h k - g k) = β * u' (h (g k) - g (g k)) * h' (g k) := by
  rw [hfoc, henv]; ring

/-- **AKMM, (4.27), p. 124.** At a steady state `g(k̄) = k̄` with `u'(c̄) ≠ 0`, (4.26) gives
`1 = β(f'(k̄) + 1 − δ)`. -/
theorem eq_4_27 {u' h h' g : ℝ → ℝ} {β kbar : ℝ} (hss : g kbar = kbar)
    (h426 : u' (h kbar - g kbar) = β * u' (h (g kbar) - g (g kbar)) * h' (g kbar))
    (hu : u' (h kbar - kbar) ≠ 0) : 1 = β * h' kbar := by
  rw [hss, hss] at h426
  exact eq_4_16_of_euler hu h426

/-- **AKMM, (4.28), p. 124, corrected.** If `V` is concave on a convex set `S` containing `k` and
`g(k)`, differentiable there, and the envelope condition `V'(k) = u'(c)h'(k)` and the first-order
condition `V'(g(k)) = u'(c)/β` hold with `c = h(k) − g(k)` (the book writes `f(k) − g(k)`,
dropping the undepreciated capital), then `u'(c)[h'(k) − 1/β][k − g(k)] ≤ 0`. -/
theorem eq_4_28 {V : ℝ → ℝ} {S : Set ℝ} (hV : ConcaveOn ℝ S V) {k gk Vk Vgk du dh β : ℝ}
    (hk : k ∈ S) (hgk : gk ∈ S) (hdk : HasDerivAt V Vk k) (hdgk : HasDerivAt V Vgk gk)
    (henv : Vk = du * dh) (hfoc : Vgk = du / β) :
    du * (dh - 1 / β) * (k - gk) ≤ 0 := by
  have hmono : (Vk - Vgk) * (k - gk) ≤ 0 := by
    rcases le_total k gk with h | h
    · have := StokeyLucasPrescott.DeterministicDynamics.deriv_le_of_concave hV hk hgk h hdk hdgk
      nlinarith
    · have := StokeyLucasPrescott.DeterministicDynamics.deriv_le_of_concave hV hgk hk h hdgk hdk
      nlinarith
  rw [henv, hfoc] at hmono
  have : du * (dh - 1 / β) = du * dh - du / β := by ring
  rw [this]
  exact hmono

/-- **AKMM, p. 124: the direction of motion.** With `V` strictly concave (differentiable, with
the envelope and first-order conditions), `u'(c) > 0` and `h'` strictly decreasing with
`βh'(k̄) = 1`: if `k > k̄` then `g(k) < k`, and if `0 < k < k̄` then `g(k) > k`. -/
theorem ngm_policy_direction {V : ℝ → ℝ} {S : Set ℝ} (hV : StrictConcaveOn ℝ S V)
    {k gk Vk Vgk du dh dhbar β kbar : ℝ} (hβ : 0 < β) (hk : k ∈ S) (hgk : gk ∈ S)
    (hdk : HasDerivAt V Vk k) (hdgk : HasDerivAt V Vgk gk) (henv : Vk = du * dh)
    (hfoc : Vgk = du / β) (hdu : 0 < du) (hbar : β * dhbar = 1)
    (hanti : k < kbar → dhbar < dh) (hanti' : kbar < k → dh < dhbar) :
    (kbar < k → gk < k) ∧ (k < kbar → k < gk) := by
  have hstrict : gk ≠ k → (Vk - Vgk) * (k - gk) < 0 := by
    intro hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := StokeyLucasPrescott.DeterministicDynamics.deriv_lt_of_strictConcave hV hgk hk h
        hdgk hdk
      nlinarith
    · have := StokeyLucasPrescott.DeterministicDynamics.deriv_lt_of_strictConcave hV hk hgk h
        hdk hdgk
      nlinarith
  have hdb : dhbar = 1 / β := by field_simp; linarith
  have hfix : gk = k → dh = dhbar := by
    intro he
    have : Vk = Vgk := by rw [hdk.unique (he ▸ hdgk)]
    rw [henv, hfoc] at this
    rw [hdb]
    field_simp at this ⊢
    nlinarith
  constructor
  · intro hlt
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with he | hgt
    · exact absurd (hfix he.symm) (hanti' hlt).ne
    · have := hstrict hgt.ne'
      rw [henv, hfoc] at this
      have hd : dh < 1 / β := hdb ▸ hanti' hlt
      have : du * dh - du / β < 0 := by
        rw [show du / β = du * (1 / β) by ring]; nlinarith
      nlinarith
  · intro hlt
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hle with he | hlt'
    · exact absurd (hfix he) (hanti hlt).ne'
    · have := hstrict hlt'.ne
      rw [henv, hfoc] at this
      have hd : 1 / β < dh := hdb ▸ hanti hlt
      have : 0 < du * dh - du / β := by
        rw [show du / β = du * (1 / β) by ring]; nlinarith
      nlinarith

/-- **AKMM, p. 124: global monotone convergence.** If `g` maps `(0, ∞)` into itself, is
nondecreasing and continuous there, `g(k̄) = k̄`, `g(k) > k` on `(0, k̄)` and `g(k) < k` on
`(k̄, ∞)`, then from every `k₀ > 0` the path `k_{t+1} = g(k_t)` is monotone and converges to
`k̄`. -/
theorem ngm_global_convergence {g : ℝ → ℝ} {kbar : ℝ} (hkbar : 0 < kbar)
    (hpos : ∀ k, 0 < k → 0 < g k) (hmono : MonotoneOn g (Set.Ioi 0))
    (hcont : ContinuousOn g (Set.Ioi 0)) (hfix : g kbar = kbar)
    (hbelow : ∀ k, 0 < k → k < kbar → k < g k) (habove : ∀ k, kbar < k → g k < k)
    {k0 : ℝ} (hk0 : 0 < k0) :
    (Monotone (fun t => g^[t] k0) ∨ Antitone (fun t => g^[t] k0)) ∧
      Tendsto (fun t => g^[t] k0) atTop (𝓝 kbar) := by
  set x : ℕ → ℝ := fun t => g^[t] k0
  have hstep : ∀ t, x (t + 1) = g (x t) := fun t => Function.iterate_succ_apply' _ _ _
  have hxpos : ∀ t, 0 < x t := by
    intro t; induction t with
    | zero => exact hk0
    | succ t ih => rw [hstep]; exact hpos _ ih
  -- a fixed point in `(0, ∞)` is `k̄`
  have huniq : ∀ L, 0 < L → g L = L → L = kbar := by
    intro L hL hgL
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hbelow L hL h; linarith
    · have := habove L h; linarith
  have hlim : ∀ L, 0 < L → Tendsto x atTop (𝓝 L) → L = kbar := by
    intro L hL hx
    refine huniq L hL (tendsto_nhds_unique ?_ ((tendsto_add_atTop_iff_nat 1).2 hx))
    have := (hcont L hL).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall hxpos⟩)
    refine (this.congr fun t => ?_)
    simp [Function.comp_apply, hstep]
  rcases le_total k0 kbar with hle | hge
  · -- below: nondecreasing and bounded by `k̄`
    have hbd : ∀ t, x t ≤ kbar := by
      intro t; induction t with
      | zero => exact hle
      | succ t ih => rw [hstep, ← hfix]; exact hmono (hxpos t) hkbar ih
    have hm : Monotone x := monotone_nat_of_le_succ fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hbd t) with he | hlt
      · rw [he, hfix]
      · exact (hbelow _ (hxpos t) hlt).le
    have hx := tendsto_atTop_ciSup hm ⟨kbar, by rintro _ ⟨t, rfl⟩; exact hbd t⟩
    have hL : 0 < ⨆ t, x t := lt_of_lt_of_le hk0 (le_ciSup ⟨kbar, by
      rintro _ ⟨t, rfl⟩; exact hbd t⟩ 0)
    exact ⟨Or.inl hm, hlim _ hL hx ▸ hx⟩
  · -- above: nonincreasing and bounded below by `k̄`
    have hbd : ∀ t, kbar ≤ x t := by
      intro t; induction t with
      | zero => exact hge
      | succ t ih => rw [hstep, ← hfix]; exact hmono hkbar (hxpos t) ih
    have ha : Antitone x := antitone_nat_of_succ_le fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hbd t) with he | hlt
      · rw [← he, hfix]
      · exact (habove _ hlt).le
    have hx := tendsto_atTop_ciInf ha ⟨kbar, by rintro _ ⟨t, rfl⟩; exact hbd t⟩
    have hL : 0 < ⨅ t, x t := lt_of_lt_of_le hkbar (le_ciInf hbd)
    exact ⟨Or.inr ha, hlim _ hL hx ▸ hx⟩

/-- **AKMM, p. 124, for `δ = 1`: global convergence, unconditionally.** In SLP's §6.1 setting
(`f` total resources, strictly concave and increasing, Inada conditions, `f'(∞) = 0`), the
stationary points of the optimal policy on `[0, k̄]` are `0` and `k*`, where `βf'(k*) = 1`, and
from every `k₀ ∈ (0, k̄]` the path converges monotonically to `k*` (SLP Proposition 6.1). -/
theorem ngm_global_convergence_full {U f U' f' : ℝ → ℝ} {β kbar : ℝ}
    [Nonempty (Set.Icc (0 : ℝ) kbar)] {v : Set.Icc (0 : ℝ) kbar →ᵇ ℝ}
    (S : StokeyLucasPrescott.DeterministicDynamics.Setting61 U f U' f' β kbar v) {kstar : ℝ}
    (hks0 : 0 < kstar) (hks : f' kstar = 1 / β) :
    kstar < kbar ∧
      (∀ k ∈ Set.Icc 0 kbar,
        StokeyLucasPrescott.DeterministicDynamics.gpol U f β kbar v k = k ↔ k = 0 ∨ k = kstar) ∧
      ∀ k₀, 0 < k₀ → k₀ ≤ kbar →
        (Monotone (fun t => (StokeyLucasPrescott.DeterministicDynamics.gpol U f β kbar v)^[t] k₀) ∨
          Antitone (fun t => (StokeyLucasPrescott.DeterministicDynamics.gpol U f β kbar v)^[t]
            k₀)) ∧
        Tendsto (fun t => (StokeyLucasPrescott.DeterministicDynamics.gpol U f β kbar v)^[t] k₀)
          atTop (𝓝 kstar) :=
  StokeyLucasPrescott.DeterministicDynamics.prop_6_1 S hks0 hks

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The slope of the policy function at the steady state

AKMM, §4.4.6, "Approximating the policy function" and "Calibration", pp. 125–127.

* (4.29) (`eq_4_29`): if the policy `g` is differentiable at the steady state `k̄` with slope
  `a₁`, differentiating the functional Euler equation (4.26) at `k̄` gives
  `u''(c̄)[1 − βa₁] = u''(c̄)[a₁ − βa₁²] + β²u'(c̄)f''(k̄)a₁`. Differentiability of `g` is a
  hypothesis, as in the book (fn. 17); in SLP's setting it is proved in `DeterministicDynamics`
  (`growth_policy_deriv`).
* (4.29) is the quadratic `βa² − (1 + β + Θ)a + 1 = 0`, `Θ = β²u'f''/u''`
  (`eq_4_29_quadratic`), whose roots are `slopeRoot` and `slopeRootOther`, with product `1/β`.
* (4.30) and the claims after it: see `slopeRoot_isRoot`, `slopeRoot_mem`, `slopeRoot_zero`,
  `slopeRoot_strictAnti`, `slopeRoot_tendsto_zero`, `slopeRoot_tendsto_one`.
* Calibration: `theta_crra`, `theta_crra_strictAnti`, `crra_slope_limits`, `theta_cobbDouglas`,
  `theta_cobbDouglas_strictAnti_alpha`, `theta_cobbDouglas_strictMono_delta` and
  `cobbDouglas_slope_mono` (convergence is slower for larger `α` and smaller `δ`).
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real

/-- **AKMM, (4.29), p. 125.** Let `h = f + (1 − δ)·id`, `g(k̄) = k̄`, `g'(k̄) = a₁`, `u''(c̄) = u₂`,
`h''(k̄) = f''(k̄) = f₂`, and `βh'(k̄) = 1` (4.27). If (4.26)
`u'(h(k) − g(k)) = βu'(h(g(k)) − g(g(k)))h'(g(k))` holds for `k` near `k̄`, then
`u₂(1 − βa₁) = u₂(a₁ − βa₁²) + β²u'(c̄)f₂a₁`. -/
theorem eq_4_29 {u' h h' g : ℝ → ℝ} {β kbar a1 u2 f2 : ℝ} (hβ : 0 < β) (hss : g kbar = kbar)
    (hg : HasDerivAt g a1 kbar) (hu' : HasDerivAt u' u2 (h kbar - kbar))
    (hh : HasDerivAt h (h' kbar) kbar) (hh' : HasDerivAt h' f2 kbar) (h427 : β * h' kbar = 1)
    (h426 : ∀ᶠ k in 𝓝 kbar, u' (h k - g k) = β * u' (h (g k) - g (g k)) * h' (g k)) :
    u2 * (1 - β * a1) = u2 * (a1 - β * a1 ^ 2) + β ^ 2 * u' (h kbar - kbar) * f2 * a1 := by
  have hg' : HasDerivAt g a1 (g kbar) := by rw [hss]; exact hg
  have hhg : HasDerivAt h (h' kbar) (g kbar) := by rw [hss]; exact hh
  have hh'g : HasDerivAt h' f2 (g kbar) := by rw [hss]; exact hh'
  -- the left-hand side
  have hL : HasDerivAt (fun k => u' (h k - g k)) (u2 * (h' kbar - a1)) kbar := by
    have hin := hh.sub hg
    have hu : HasDerivAt u' u2 (h kbar - g kbar) := by rw [hss]; exact hu'
    exact hu.comp kbar hin
  -- the right-hand side
  have hR : HasDerivAt (fun k => β * u' (h (g k) - g (g k)) * h' (g k))
      (β * (u2 * (h' kbar * a1 - a1 * a1)) * h' kbar + β * u' (h kbar - kbar) * (f2 * a1))
      kbar := by
    have hin : HasDerivAt (fun k => h (g k) - g (g k)) (h' kbar * a1 - a1 * a1) kbar :=
      (hhg.comp kbar hg).sub (hg'.comp kbar hg)
    have hu : HasDerivAt u' u2 (h (g kbar) - g (g kbar)) := by rw [hss, hss]; exact hu'
    have h1 := (hu.comp kbar hin).const_mul β
    have h2 := hh'g.comp kbar hg
    have := h1.mul h2
    convert this using 1
    · funext k; simp only [Pi.mul_apply, Function.comp_apply]
    · simp only [Function.comp_apply, hss]
  have hEq := hL.unique (hR.congr_of_eventuallyEq h426)
  have hh1 : h' kbar = 1 / β := by field_simp; linarith
  rw [hh1] at hEq
  field_simp at hEq
  linear_combination hEq

/-- **AKMM, p. 125.** With `u'' ≠ 0` and `Θ = β²u'f''/u''`, (4.29) is the quadratic
`βa² − (1 + β + Θ)a + 1 = 0`. -/
theorem eq_4_29_quadratic {β a u1 u2 f2 : ℝ} (hu2 : u2 ≠ 0) :
    u2 * (1 - β * a) = u2 * (a - β * a ^ 2) + β ^ 2 * u1 * f2 * a ↔
      β * a ^ 2 - (1 + β + β ^ 2 * u1 * f2 / u2) * a + 1 = 0 := by
  constructor <;> intro h
  · field_simp
    linear_combination h
  · field_simp at h
    linear_combination h

/-- AKMM, (4.30), p. 125: the stable root `a₁ = (1 + β + Θ − √((1 + β + Θ)² − 4β))/(2β)`. -/
noncomputable def slopeRoot (β Θ : ℝ) : ℝ :=
  (1 + β + Θ - √((1 + β + Θ) ^ 2 - 4 * β)) / (2 * β)

/-- The other root `(1 + β + Θ + √((1 + β + Θ)² − 4β))/(2β)`. -/
noncomputable def slopeRootOther (β Θ : ℝ) : ℝ :=
  (1 + β + Θ + √((1 + β + Θ) ^ 2 - 4 * β)) / (2 * β)

theorem slopeRoot_disc_nonneg {β Θ : ℝ} (hβ : 0 < β) (hΘ : 0 ≤ Θ) :
    0 ≤ (1 + β + Θ) ^ 2 - 4 * β := by nlinarith [sq_nonneg (1 - β)]

/-- AKMM, p. 125: both formulas solve `βa² − (1 + β + Θ)a + 1 = 0`, and their product is `1/β`. -/
theorem slopeRoot_isRoot {β Θ : ℝ} (hβ : 0 < β) (hΘ : 0 ≤ Θ) :
    β * slopeRoot β Θ ^ 2 - (1 + β + Θ) * slopeRoot β Θ + 1 = 0 ∧
      β * slopeRootOther β Θ ^ 2 - (1 + β + Θ) * slopeRootOther β Θ + 1 = 0 ∧
      slopeRoot β Θ * slopeRootOther β Θ = 1 / β := by
  have hs := Real.sq_sqrt (slopeRoot_disc_nonneg hβ hΘ)
  unfold slopeRoot slopeRootOther
  obtain ⟨s, hsd⟩ : ∃ s, s = √((1 + β + Θ) ^ 2 - 4 * β) := ⟨_, rfl⟩
  rw [← hsd] at hs ⊢
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination hs
  · field_simp
    linear_combination hs
  · field_simp
    linear_combination -1 * hs

theorem slopeRoot_sqrt_pos {β Θ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hΘ : 0 < Θ) :
    1 - β < √((1 + β + Θ) ^ 2 - 4 * β) := by
  rw [show 1 - β = √((1 - β) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)

/-- The stable root in rationalized form, `a₁ = 2/(1 + β + Θ + √((1 + β + Θ)² − 4β))`. -/
theorem slopeRoot_eq {β Θ : ℝ} (hβ : 0 < β) (hΘ : 0 ≤ Θ) :
    slopeRoot β Θ = 2 / (1 + β + Θ + √((1 + β + Θ) ^ 2 - 4 * β)) := by
  have hs := Real.sq_sqrt (slopeRoot_disc_nonneg hβ hΘ)
  have hs0 := Real.sqrt_nonneg ((1 + β + Θ) ^ 2 - 4 * β)
  unfold slopeRoot
  obtain ⟨s, hsd⟩ : ∃ s, s = √((1 + β + Θ) ^ 2 - 4 * β) := ⟨_, rfl⟩
  rw [← hsd] at hs hs0 ⊢
  have hpos : 0 < 1 + β + Θ + s := by linarith
  rw [div_eq_div_iff (by positivity) hpos.ne']
  linear_combination -1 * hs

/-- **AKMM, p. 125: "one root strictly between zero and one, the other strictly greater than
one"** (for `Θ > 0`, `0 < β < 1`). -/
theorem slopeRoot_mem {β Θ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hΘ : 0 < Θ) :
    0 < slopeRoot β Θ ∧ slopeRoot β Θ < 1 ∧ 1 < slopeRootOther β Θ := by
  have hsq := slopeRoot_sqrt_pos hβ hβ1 hΘ
  have hs0 := Real.sqrt_nonneg ((1 + β + Θ) ^ 2 - 4 * β)
  rw [slopeRoot_eq hβ hΘ.le]
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]; linarith
  · unfold slopeRootOther
    rw [one_lt_div (by positivity)]; linarith

/-- **AKMM, p. 125: `a₁ = 1` when `Θ = 0`** (for `0 < β < 1`; the other root is `1/β`). -/
theorem slopeRoot_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    slopeRoot β 0 = 1 ∧ slopeRootOther β 0 = 1 / β := by
  have e : √((1 + β + 0) ^ 2 - 4 * β) = 1 - β := by
    rw [show (1 + β + 0) ^ 2 - 4 * β = (1 - β) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  unfold slopeRoot slopeRootOther
  rw [e]
  constructor <;> field_simp <;> ring

/-- **AKMM, p. 125: `a₁` is decreasing in `Θ`** on `[0, ∞)`. -/
theorem slopeRoot_strictAnti {β : ℝ} (hβ : 0 < β) :
    StrictAntiOn (slopeRoot β) (Set.Ici 0) := by
  intro Θ hΘ Θ' hΘ' hlt
  have hΘ0 : (0 : ℝ) ≤ Θ := hΘ
  have hΘ0' : (0 : ℝ) ≤ Θ' := hΘ'
  rw [slopeRoot_eq hβ hΘ0, slopeRoot_eq hβ hΘ0']
  have hs : √((1 + β + Θ) ^ 2 - 4 * β) ≤ √((1 + β + Θ') ^ 2 - 4 * β) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h0 := Real.sqrt_nonneg ((1 + β + Θ) ^ 2 - 4 * β)
  exact div_lt_div_of_pos_left two_pos (by positivity) (by linarith)

/-- **AKMM, p. 125: `a₁ → 0` as `Θ → ∞`.** -/
theorem slopeRoot_tendsto_zero {β : ℝ} (hβ : 0 < β) :
    Tendsto (slopeRoot β) atTop (𝓝 0) := by
  have hden : Tendsto (fun Θ : ℝ => 1 + β + Θ + √((1 + β + Θ) ^ 2 - 4 * β)) atTop atTop := by
    refine tendsto_atTop_mono (fun Θ => ?_) (tendsto_atTop_add_const_left _ (1 + β) tendsto_id)
    have := Real.sqrt_nonneg ((1 + β + Θ) ^ 2 - 4 * β)
    simp only [id]; linarith
  refine ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop hden).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with Θ hΘ
  exact (slopeRoot_eq hβ hΘ).symm

/-- **AKMM, p. 125: `a₁ → 1` as `Θ → 0`** (continuity of (4.30)). -/
theorem slopeRoot_tendsto_one {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (slopeRoot β) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (slopeRoot β) := by
    unfold slopeRoot
    exact ((continuous_const.add continuous_id).sub
      (Real.continuous_sqrt.comp (((continuous_const.add continuous_id).pow 2).sub
        continuous_const))).div_const _
  have := hc.tendsto 0
  rwa [(slopeRoot_zero hβ hβ1).1] at this

/-- **AKMM, p. 126: `Θ` under CRRA utility.** With `u'(c) = c^{−σ}`, `u''(c) = −σc^{−σ−1}`,
`c̄ > 0`, `σ > 0`: `Θ = β²u'f''/u'' = −β²f''(k̄)c̄/σ`, where `c̄ = f(k̄) − δk̄`. -/
theorem theta_crra {β σ c f2 : ℝ} (hσ : 0 < σ) (hc : 0 < c) :
    β ^ 2 * c ^ (-σ) * f2 / (-σ * c ^ (-σ - 1)) = -(β ^ 2 * f2 * c) / σ := by
  have hP : 0 < c ^ (-σ) := rpow_pos_of_pos hc _
  rw [rpow_sub_one hc.ne']
  field_simp

/-- **AKMM, p. 126.** With `f'' < 0` and `c̄ > 0`, the CRRA `Θ = −β²f''c̄/σ` is positive and
strictly decreasing in `σ > 0`. -/
theorem theta_crra_strictAnti {β c f2 : ℝ} (hβ : 0 < β) (hc : 0 < c) (hf2 : f2 < 0) :
    (∀ σ, 0 < σ → 0 < -(β ^ 2 * f2 * c) / σ) ∧
      StrictAntiOn (fun σ => -(β ^ 2 * f2 * c) / σ) (Set.Ioi 0) := by
  have hK : 0 < -(β ^ 2 * f2 * c) := by
    have : β ^ 2 * f2 * c < 0 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity)
      hf2) hc
    linarith
  exact ⟨fun σ hσ => div_pos hK hσ, fun σ hσ σ' _ hlt => div_lt_div_of_pos_left hK hσ hlt⟩

/-- **AKMM, p. 126: the limits in `σ`.** As `σ → 0⁺`, `Θ → ∞` and `a₁ → 0` (immediate
convergence); as `σ → ∞`, `Θ → 0` and `a₁ → 1` (infinitely slow convergence). -/
theorem crra_slope_limits {β c f2 : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hc : 0 < c) (hf2 : f2 < 0) :
    Tendsto (fun σ => slopeRoot β (-(β ^ 2 * f2 * c) / σ)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun σ => slopeRoot β (-(β ^ 2 * f2 * c) / σ)) atTop (𝓝 1) := by
  have hK : 0 < -(β ^ 2 * f2 * c) := by
    have : β ^ 2 * f2 * c < 0 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity)
      hf2) hc
    linarith
  refine ⟨(slopeRoot_tendsto_zero hβ).comp ?_, (slopeRoot_tendsto_one hβ hβ1).comp ?_⟩
  · have := tendsto_inv_nhdsGT_zero.const_mul_atTop hK
    exact this.congr fun σ => (div_eq_mul_inv _ _).symm
  · exact (tendsto_const_nhds (x := -(β ^ 2 * f2 * c))).div_atTop tendsto_id

/-- **AKMM, p. 126: `Θ` with `f(k) = k^α`.** If `k̄ > 0` and `αk̄^{α−1} = ρ = 1/β − 1 + δ`, then
`−β²f''(k̄)(f(k̄) − δk̄)/σ = (β²(1 − α)/σ)ρ(ρ/α − δ)`, the book's formula. -/
theorem theta_cobbDouglas {α β δ σ kbar : ℝ} (hα0 : 0 < α) (hk : 0 < kbar)
    (hss : α * kbar ^ (α - 1) = 1 / β - 1 + δ) :
    -(β ^ 2 * (α * (α - 1) * kbar ^ (α - 2)) * (kbar ^ α - δ * kbar)) / σ =
      β ^ 2 * (1 - α) / σ * (1 / β - 1 + δ) * ((1 / β - 1 + δ) / α - δ) := by
  have h2 : kbar ^ (α - 2) = kbar ^ (α - 1) / kbar := by
    rw [show α - 2 = (α - 1) - 1 by ring, rpow_sub_one hk.ne']
  have h3 : kbar ^ α = kbar ^ (α - 1) * kbar := by
    rw [← rpow_add_one hk.ne']; ring_nf
  have hk1 : kbar ^ (α - 1) = (1 / β - 1 + δ) / α := by
    field_simp; linarith
  rw [h2, h3, hk1]
  field_simp
  ring

/-- The Cobb–Douglas `Θ(α, δ) = (β²(1 − α)/σ)ρ(ρ/α − δ)`, `ρ = 1/β − 1 + δ`. -/
noncomputable def thetaCD (β σ α δ : ℝ) : ℝ :=
  β ^ 2 * (1 - α) / σ * (1 / β - 1 + δ) * ((1 / β - 1 + δ) / α - δ)

theorem thetaCD_pos {β σ α δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hα0 : 0 < α)
    (hα1 : α < 1) (hδ : 0 ≤ δ) : 0 < thetaCD β σ α δ := by
  have hρ : 0 < 1 / β - 1 := by rw [sub_pos, lt_div_iff₀ hβ0]; linarith
  have h2 : 0 < (1 / β - 1 + δ) / α - δ := by
    rw [sub_pos, lt_div_iff₀ hα0]; nlinarith
  unfold thetaCD
  have : 0 < β ^ 2 * (1 - α) / σ := div_pos (mul_pos (by positivity) (by linarith)) hσ
  positivity

/-- **AKMM, p. 127: `Θ` is decreasing in `α`** on `(0, 1)`. -/
theorem theta_cobbDouglas_strictAnti_alpha {β σ δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hδ : 0 ≤ δ) : StrictAntiOn (fun α => thetaCD β σ α δ) (Set.Ioo 0 1) := by
  intro α hα α' hα' hlt
  have hρ : 0 < 1 / β - 1 := by rw [sub_pos, lt_div_iff₀ hβ0]; linarith
  set ρ := 1 / β - 1 + δ
  have hρ' : 0 < ρ := by simp only [ρ]; linarith
  have hd' : 0 < ρ / α' - δ := by rw [sub_pos, lt_div_iff₀ hα'.1]; nlinarith [hα'.2]
  have hdlt : ρ / α' - δ < ρ / α - δ := by
    have := div_lt_div_of_pos_left hρ' hα.1 hlt; linarith
  have h1 : 0 < 1 - α' := by linarith [hα'.2]
  have hc : 0 < β ^ 2 / σ * ρ := by positivity
  simp only [thetaCD]
  have e : ∀ x : ℝ, β ^ 2 * (1 - x) / σ * ρ * (ρ / x - δ) =
      β ^ 2 / σ * ρ * ((1 - x) * (ρ / x - δ)) := fun x => by ring
  rw [e, e]
  exact mul_lt_mul_of_pos_left (mul_lt_mul'' (by linarith) hdlt h1.le hd'.le) hc

/-- **AKMM, p. 127: `Θ` is increasing in `δ`** on `[0, ∞)`. -/
theorem theta_cobbDouglas_strictMono_delta {β σ α : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hα0 : 0 < α) (hα1 : α < 1) :
    StrictMonoOn (fun δ => thetaCD β σ α δ) (Set.Ici 0) := by
  intro δ hδ δ' hδ' hlt
  have hδ0 : (0 : ℝ) ≤ δ := hδ
  have hρ : 0 < 1 / β - 1 := by rw [sub_pos, lt_div_iff₀ hβ0]; linarith
  have hc : 0 < β ^ 2 * (1 - α) / σ := div_pos (mul_pos (by positivity) (by linarith)) hσ
  have h2 : 0 < (1 / β - 1 + δ) / α - δ := by rw [sub_pos, lt_div_iff₀ hα0]; nlinarith
  have h3 : (1 / β - 1 + δ) / α - δ < (1 / β - 1 + δ') / α - δ' := by
    have e : ∀ x : ℝ, (1 / β - 1 + x) / α - x = (1 / β - 1) / α + x * (1 / α - 1) := fun x => by
      field_simp; ring
    rw [e, e]
    have : 0 < 1 / α - 1 := by rw [sub_pos, lt_div_iff₀ hα0]; linarith
    nlinarith
  simp only [thetaCD]
  rw [mul_assoc, mul_assoc (β ^ 2 * (1 - α) / σ)]
  exact mul_lt_mul_of_pos_left (mul_lt_mul'' (by linarith) h3 (by linarith) h2.le) hc

/-- **AKMM, p. 127: convergence is slower when production is closer to linear and depreciation
is small.** With Cobb–Douglas technology, `a₁ = slopeRoot β Θ(α, δ)` is increasing in `α` and
decreasing in `δ`. -/
theorem cobbDouglas_slope_mono {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) :
    (∀ δ, 0 ≤ δ → StrictMonoOn (fun α => slopeRoot β (thetaCD β σ α δ)) (Set.Ioo 0 1)) ∧
      ∀ α, 0 < α → α < 1 → StrictAntiOn (fun δ => slopeRoot β (thetaCD β σ α δ)) (Set.Ici 0) := by
  refine ⟨fun δ hδ α hα α' hα' hlt => ?_, fun α hα0 hα1 δ hδ δ' hδ' hlt => ?_⟩
  · exact slopeRoot_strictAnti hβ0 (thetaCD_pos hβ0 hβ1 hσ hα'.1 hα'.2 hδ).le
      (thetaCD_pos hβ0 hβ1 hσ hα.1 hα.2 hδ).le
      (theta_cobbDouglas_strictAnti_alpha hβ0 hβ1 hσ hδ hα hα' hlt)
  · exact slopeRoot_strictAnti hβ0 (thetaCD_pos hβ0 hβ1 hσ hα0 hα1 hδ).le
      (thetaCD_pos hβ0 hβ1 hσ hα0 hα1 hδ').le
      (theta_cobbDouglas_strictMono_delta hβ0 hβ1 hσ hα0 hα1 hδ hδ' hlt)

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Constraints in the consumption–saving problem: Theorem .3

AKMM, App. 4.A.1, pp. 827–829. Flow budget `a_{t+1} = (1 + r)a_t + w_t − c_t` (4.A.1), `r > −1`,
consumption `c_t ≥ 0`, and discounted wages `Σ w_t/(1 + r)ᵗ` finite.

* (4.A.2): `Σ_{t≤T} c_t/(1 + r)ᵗ + a_{T+1}/(1 + r)ᵀ = (1 + r)a₀ + Σ_{t≤T} w_t/(1 + r)ᵗ`
  (`eq_4A_2`).
* p. 827: `lim a_{T+1} ≥ 0` is too restrictive — a constant debt `−ε` is feasible and repaid
  forever (`appendix_4A_too_restrictive`).
* **Theorem .3** (`theorem_4A_3`): for a consumption plan, (i) the flow budget with the no-Ponzi
  condition (4.A.3), (ii) the flow budget with the natural borrowing limit (4.A.5) at every `t`,
  and (iii) the lifetime budget constraint (4.A.4) are equivalent. The nPg condition is read as
  "`a_{T+1}/(1 + r)ᵀ` converges to a limit `≥ 0`", as printed.
-/

namespace AKMM.DynamicOptimization

open Filter Topology

variable {r : ℝ} {a w c : ℕ → ℝ}

/-- **AKMM, (4.A.2), p. 827.** Combining the flow budget constraints (4.A.1) up to `T`. -/
theorem eq_4A_2 (hr : -1 < r) (hflow : ∀ t, a (t + 1) = (1 + r) * a t + w t - c t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t + a (T + 1) / (1 + r) ^ T =
      (1 + r) * a 0 + ∑ t ∈ Finset.range (T + 1), w t / (1 + r) ^ t := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  induction T with
  | zero => simp only [zero_add, Finset.sum_range_one, pow_zero, div_one, hflow 0]; ring
  | succ T ih =>
    rw [Finset.sum_range_succ (fun t => c t / (1 + r) ^ t) (T + 1),
      Finset.sum_range_succ (fun t => w t / (1 + r) ^ t) (T + 1)]
    have h1 : (1 + r) ^ T ≠ 0 := (pow_pos hr' T).ne'
    have h2 : (1 + r) ^ (T + 1) ≠ 0 := (pow_pos hr' (T + 1)).ne'
    have e : a (T + 1 + 1) / (1 + r) ^ (T + 1) =
        a (T + 1) / (1 + r) ^ T + (w (T + 1) - c (T + 1)) / (1 + r) ^ (T + 1) := by
      rw [hflow (T + 1), pow_succ]; field_simp; ring
    rw [e, sub_div]
    linarith

/-- **AKMM, p. 827: `lim a_{T+1} ≥ 0` is too restrictive.** With a constant wage `w̄ > 0`, `r > 0`
and `0 < ε < w̄/(1 + r)`, holding the debt `a_t = −ε` forever with `c_t = w̄ − rε > 0` satisfies the
flow budget and the no-Ponzi condition (`a_{T+1}/(1 + r)ᵀ → 0`), but `a_{T+1} → −ε < 0`. -/
theorem appendix_4A_too_restrictive {wbar ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hεw : ε < wbar / (1 + r)) :
    (∀ t : ℕ, (fun _ : ℕ => -ε) (t + 1) = (1 + r) * (fun _ : ℕ => -ε) t + wbar -
      (wbar - r * ε)) ∧ 0 < wbar - r * ε ∧
      Tendsto (fun T : ℕ => -ε / (1 + r) ^ T) atTop (𝓝 0) ∧
      Tendsto (fun _ : ℕ => -ε) atTop (𝓝 (-ε)) ∧ -ε < 0 := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  refine ⟨fun t => by ring, ?_, ?_, tendsto_const_nhds, by linarith⟩
  · rw [lt_div_iff₀ hr'] at hεw; nlinarith
  · have : Tendsto (fun T : ℕ => (1 + r) ^ T) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by linarith)
    exact tendsto_const_nhds.div_atTop this

/-- The partial sums of `c_t/(1 + r)ᵗ` from the flow budget: `(4.A.2)` rearranged. -/
theorem appendix_4A_partial (hr : -1 < r) (hflow : ∀ t, a (t + 1) = (1 + r) * a t + w t - c t)
    (T : ℕ) : ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t =
      (1 + r) * a 0 + ∑ t ∈ Finset.range (T + 1), w t / (1 + r) ^ t -
        a (T + 1) / (1 + r) ^ T := by
  linarith [eq_4A_2 hr hflow T]

/-- **Theorem .3** (AKMM, App. 4.A.1, p. 828). Let `r > −1`, `c ≥ 0`, `Σ w_t/(1 + r)ᵗ` summable,
and let `a` follow the flow budget (4.A.1). The following are equivalent:
(i) the no-Ponzi-game condition (4.A.3): `a_{T+1}/(1 + r)ᵀ → L` for some `L ≥ 0`;
(ii) the natural borrowing limit (4.A.5): `a_{t+1} ≥ −Σ_{s>t} w_s/(1 + r)^{s−t}` for all `t`;
(iii) the lifetime budget constraint (4.A.4): `Σ c_t/(1 + r)ᵗ` is finite and
`Σ c_t/(1 + r)ᵗ ≤ (1 + r)a₀ + Σ w_t/(1 + r)ᵗ`. -/
theorem theorem_4A_3 (hr : -1 < r) (hc : ∀ t, 0 ≤ c t)
    (hw : Summable fun t => w t / (1 + r) ^ t)
    (hflow : ∀ t, a (t + 1) = (1 + r) * a t + w t - c t) :
    List.TFAE [∃ L, 0 ≤ L ∧ Tendsto (fun T => a (T + 1) / (1 + r) ^ T) atTop (𝓝 L),
      ∀ t, -∑' j, w (j + (t + 1)) / (1 + r) ^ (j + 1) ≤ a (t + 1),
      (Summable fun t => c t / (1 + r) ^ t) ∧
        ∑' t, c t / (1 + r) ^ t ≤ (1 + r) * a 0 + ∑' t, w t / (1 + r) ^ t] := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  have hcn : ∀ t, 0 ≤ c t / (1 + r) ^ t := fun t => div_nonneg (hc t) (pow_pos hr' t).le
  set W := ∑' t, w t / (1 + r) ^ t
  have hWlim : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), w t / (1 + r) ^ t) atTop (𝓝 W) :=
    (tendsto_add_atTop_iff_nat 1).2 hw.hasSum.tendsto_sum_nat
  -- the natural limit in discounted form (4.A.7)
  have hdisc : ∀ t, ∑' j, w (j + (t + 1)) / (1 + r) ^ (j + (t + 1)) =
      (∑' j, w (j + (t + 1)) / (1 + r) ^ (j + 1)) / (1 + r) ^ t := by
    intro t
    rw [← tsum_div_const]
    congr 1; funext j
    rw [show j + (t + 1) = (j + 1) + t by ring, pow_add]
    field_simp
  tfae_have 1 → 3 := by
    rintro ⟨L, hL, hlim⟩
    have hpart : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t) atTop
        (𝓝 ((1 + r) * a 0 + W - L)) := by
      simp only [appendix_4A_partial hr hflow]
      exact (tendsto_const_nhds.add hWlim).sub hlim
    have hs : HasSum (fun t => c t / (1 + r) ^ t) ((1 + r) * a 0 + W - L) :=
      (hasSum_iff_tendsto_nat_of_nonneg hcn _).2 ((tendsto_add_atTop_iff_nat 1).1 hpart)
    exact ⟨hs.summable, by rw [hs.tsum_eq]; linarith⟩
  tfae_have 3 → 1 := by
    rintro ⟨hs, hle⟩
    refine ⟨(1 + r) * a 0 + W - ∑' t, c t / (1 + r) ^ t, by linarith, ?_⟩
    have h1 := (tendsto_add_atTop_iff_nat 1).2 hs.hasSum.tendsto_sum_nat
    have : ∀ T, a (T + 1) / (1 + r) ^ T = (1 + r) * a 0 +
        ∑ t ∈ Finset.range (T + 1), w t / (1 + r) ^ t -
          ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t := fun T => by
      linarith [eq_4A_2 hr hflow T]
    simp only [this]
    exact (tendsto_const_nhds.add hWlim).sub h1
  tfae_have 1 → 2 := by
    intro h1
    obtain ⟨hs, -⟩ := (tfae_1_to_3 h1)
    obtain ⟨L, hL, hlim⟩ := h1
    have hLval : L = (1 + r) * a 0 + W - ∑' t, c t / (1 + r) ^ t := by
      have hpart : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t) atTop
          (𝓝 ((1 + r) * a 0 + W - L)) := by
        simp only [appendix_4A_partial hr hflow]
        exact (tendsto_const_nhds.add hWlim).sub hlim
      have := tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).2 hs.hasSum.tendsto_sum_nat)
        hpart
      linarith
    intro t
    have hsplitw := hw.sum_add_tsum_nat_add (t + 1)
    have hsplitc := hs.sum_add_tsum_nat_add (t + 1)
    have hat : a (t + 1) / (1 + r) ^ t = (1 + r) * a 0 +
        ∑ s ∈ Finset.range (t + 1), w s / (1 + r) ^ s -
          ∑ s ∈ Finset.range (t + 1), c s / (1 + r) ^ s := by
      linarith [eq_4A_2 hr hflow t]
    have htc : 0 ≤ ∑' j, c (j + (t + 1)) / (1 + r) ^ (j + (t + 1)) :=
      tsum_nonneg fun j => hcn _
    -- `a_{t+1}/(1 + r)ᵗ = L − Σ_{s>t}(w_s − c_s)/(1 + r)ˢ ≥ −Σ_{s>t} w_s/(1 + r)ˢ`
    have hge : -∑' j, w (j + (t + 1)) / (1 + r) ^ (j + (t + 1)) ≤ a (t + 1) / (1 + r) ^ t := by
      rw [hat]; linarith
    rw [hdisc t, ← neg_div, div_le_div_iff_of_pos_right (pow_pos hr' t)] at hge
    exact hge
  tfae_have 2 → 3 := by
    intro h2
    -- (4.A.7): `a_{T+1}/(1 + r)ᵀ ≥ −Σ_{s>T} w_s/(1 + r)ˢ`, and the tail tends to `0`
    have h7 : ∀ T, -∑' j, w (j + (T + 1)) / (1 + r) ^ (j + (T + 1)) ≤
        a (T + 1) / (1 + r) ^ T := fun T => by
      rw [hdisc T, ← neg_div, div_le_div_iff_of_pos_right (pow_pos hr' T)]
      exact h2 T
    have hbound : ∀ T, ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t ≤ (1 + r) * a 0 + W := by
      intro T
      have := hw.sum_add_tsum_nat_add (T + 1)
      rw [appendix_4A_partial hr hflow T]
      linarith [h7 T]
    have hs : Summable fun t => c t / (1 + r) ^ t := by
      refine summable_of_sum_range_le (c := (1 + r) * a 0 + W) hcn fun n => ?_
      rcases n with _ | n
      · have h0 := hbound 0
        rw [zero_add, Finset.sum_range_one] at h0
        rw [Finset.range_zero, Finset.sum_empty]
        linarith [hcn 0]
      · exact hbound n
    refine ⟨hs, ?_⟩
    exact le_of_tendsto' ((tendsto_add_atTop_iff_nat 1).2 hs.hasSum.tendsto_sum_nat) hbound
  tfae_finish

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Balanced growth and CRRA utility: Theorem .4

AKMM, App. 4.A.2, pp. 829–830.

* `bgp_marginal_ratio`: on a balanced path `c_{t+1} = (1 + γ)c_t` the Euler equation
  `u'(c_t) = β(1 + r)u'(c_{t+1})` gives `u'((1 + γ)c)/u'(c) = 1/(β(1 + r))`; the book prints
  `(1 + r)/β` (the constancy in `c`, which is all the proof uses, is unaffected).
* **Theorem .4** (`theorem_4A_4`): if `u` is twice differentiable on `(0, ∞)`, `u' > 0`, and for
  every growth rate `γ > −1` the ratio `u'((1 + γ)c)/u'(c)` does not depend on `c`, then
  `u'(c) = u'(1)c^{−σ}` and `u` is a positive affine transformation of `log c` (`σ = 1`) or of
  `c^{1−σ}/(1 − σ)`; and `σ > 0` iff `u'` is strictly decreasing (`theorem_4A_4_sigma_pos`).
* The book's statement — `u = log c` or `u = c^{1−σ}/(1 − σ)` with `σ > 0` — holds only up to
  positive affine transformations (`theorem_4A_4_affine_counterexample`, `u = 2 log c`) and needs
  concavity for `σ > 0` (`u = c²/2` has `σ = −1`, `theorem_4A_4_convex_example`).
-/

namespace AKMM.DynamicOptimization

open Real

/-- AKMM, p. 830, corrected: on a balanced path `c' = (1 + γ)c`, the Euler equation
`u'(c) = β(1 + r)u'(c')` gives `u'((1 + γ)c)/u'(c) = 1/(β(1 + r))`. -/
theorem bgp_marginal_ratio {u' : ℝ → ℝ} {β r γ c : ℝ} (hβr : β * (1 + r) ≠ 0)
    (hu : u' c ≠ 0) (heuler : u' c = β * (1 + r) * u' ((1 + γ) * c)) :
    u' ((1 + γ) * c) / u' c = 1 / (β * (1 + r)) := by
  rw [div_eq_div_iff hu hβr, heuler]; ring

/-- Constancy on `(0, ∞)` from a zero derivative. -/
theorem crraBGP_const {φ : ℝ → ℝ} (hφ : ∀ x, 0 < x → HasDerivAt φ 0 x) {x : ℝ} (hx : 0 < x) :
    φ x = φ 1 :=
  isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi 0).isPreconnected
    (fun y hy => (hφ y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hφ y hy).deriv) hx (Set.mem_Ioi.2 one_pos)

/-- **Theorem .4** (AKMM, App. 4.A.2, pp. 829–830). Let `u` have derivative `u' > 0` and `u'` have
derivative `u''` on `(0, ∞)`. If for every `γ > −1` there is `#(γ)` with
`u'((1 + γ)c) = #(γ)u'(c)` for all `c > 0`, then with `σ = −u''(1)/u'(1)`:
`u'(c) = u'(1)c^{−σ}`, and `u(c) = u'(1) log c + u(1)` if `σ = 1`, otherwise
`u(c) = u'(1)c^{1−σ}/(1 − σ) + b` for a constant `b`. -/
theorem theorem_4A_4 {u u' u'' : ℝ → ℝ} (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu' : ∀ c, 0 < c → HasDerivAt u' (u'' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hbgp : ∀ γ, -1 < γ → ∃ M, ∀ c, 0 < c → u' ((1 + γ) * c) = M * u' c) :
    (∀ c, 0 < c → u' c = u' 1 * c ^ (-(-u'' 1 / u' 1))) ∧
      ((-u'' 1 / u' 1 = 1 → ∀ c, 0 < c → u c = u' 1 * Real.log c + u 1) ∧
        (-u'' 1 / u' 1 ≠ 1 → ∃ b, ∀ c, 0 < c →
          u c = u' 1 * c ^ (1 - -u'' 1 / u' 1) / (1 - -u'' 1 / u' 1) + b)) := by
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = -u'' 1 / u' 1 := ⟨_, rfl⟩
  rw [← hσdef]
  have h1 : 0 < u' 1 := hpos 1 one_pos
  -- the multiplicative equation `u'(xc) = (u'(x)/u'(1))u'(c)`
  have hmul : ∀ x, 0 < x → ∀ c, 0 < c → u' (x * c) = u' x / u' 1 * u' c := by
    intro x hx c hc
    obtain ⟨M, hM⟩ := hbgp (x - 1) (by linarith)
    have e : 1 + (x - 1) = x := by ring
    have hM1 := hM 1 one_pos
    rw [e, mul_one] at hM1
    have hMc := hM c hc
    rw [e] at hMc
    rw [hMc, hM1]
    field_simp
  -- differentiating in `c` at `c = 1`: `x u''(x) = (u'(x)/u'(1)) u''(1)`
  have hode : ∀ x, 0 < x → x * u'' x = -σ * u' x := by
    intro x hx
    have hl : HasDerivAt (fun c => u' (x * c)) (u'' (x * 1) * x) 1 := by
      have := (hu' (x * 1) (by linarith)).comp 1 ((hasDerivAt_id (1 : ℝ)).const_mul x)
      simpa [Function.comp_def] using this
    have hr : HasDerivAt (fun c => u' x / u' 1 * u' c) (u' x / u' 1 * u'' 1) 1 :=
      (hu' 1 one_pos).const_mul _
    have heq : (fun c => u' (x * c)) =ᶠ[nhds 1] fun c => u' x / u' 1 * u' c :=
      Filter.eventually_of_mem (Ioi_mem_nhds one_pos) fun c hc => hmul x hx c hc
    have := hl.unique (hr.congr_of_eventuallyEq heq)
    rw [mul_one, div_mul_eq_mul_div, eq_div_iff h1.ne'] at this
    rw [hσdef]
    field_simp
    linear_combination this
  -- `u'(x)x^σ` is constant
  have hconst : ∀ x, 0 < x → u' x * x ^ σ = u' 1 := by
    intro x hx
    have hd : ∀ y, 0 < y → HasDerivAt (fun y => u' y * y ^ σ) 0 y := by
      intro y hy
      have h2 := (hu' y hy).mul (hasDerivAt_rpow_const (p := σ) (Or.inl hy.ne'))
      convert h2 using 1
      have h3 : u'' y = -σ * u' y / y := by rw [← hode y hy]; field_simp
      rw [rpow_sub_one hy.ne', h3]
      field_simp
      ring
    have := crraBGP_const hd hx
    simpa using this
  have hform : ∀ c, 0 < c → u' c = u' 1 * c ^ (-σ) := by
    intro c hc
    rw [← hconst c hc, mul_assoc, ← rpow_add hc, add_neg_cancel, rpow_zero, mul_one]
  refine ⟨hform, fun hσ c hc => ?_, fun hσ => ?_⟩
  · -- `σ = 1`: `u − u'(1) log` has zero derivative
    have hd : ∀ y, 0 < y → HasDerivAt (fun y => u y - u' 1 * Real.log y) 0 y := by
      intro y hy
      have h2 := (hu y hy).sub ((Real.hasDerivAt_log hy.ne').const_mul (u' 1))
      convert h2 using 1
      rw [hform y hy, hσ, rpow_neg hy.le, rpow_one]
      ring
    have := crraBGP_const hd hc
    simp only [Real.log_one, mul_zero, sub_zero] at this
    linarith
  · -- `σ ≠ 1`: `u − u'(1)c^{1−σ}/(1 − σ)` has zero derivative
    have h1σ : (1 - σ) ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    refine ⟨u 1 - u' 1 / (1 - σ), fun c hc => ?_⟩
    have hd : ∀ y, 0 < y → HasDerivAt (fun y => u y - u' 1 * y ^ (1 - σ) / (1 - σ)) 0 y := by
      intro y hy
      have h2 := (hu y hy).sub (((hasDerivAt_rpow_const (p := 1 - σ)
        (Or.inl hy.ne')).const_mul (u' 1)).div_const (1 - σ))
      convert h2 using 1
      rw [hform y hy, show 1 - σ - 1 = -σ by ring]
      field_simp
      ring
    have := crraBGP_const hd hc
    simp only [one_rpow, mul_one] at this
    linarith

/-- **AKMM, Theorem .4: `σ > 0` needs concavity.** If `u'(c) = u'(1)c^{−σ}` with `u'(1) > 0`, then
`σ > 0` iff `u'` is strictly decreasing on `(0, ∞)`. -/
theorem theorem_4A_4_sigma_pos {u' : ℝ → ℝ} {σ : ℝ} (h1 : 0 < u' 1)
    (hform : ∀ c, 0 < c → u' c = u' 1 * c ^ (-σ)) :
    0 < σ ↔ StrictAntiOn u' (Set.Ioi 0) := by
  constructor
  · intro hσ x hx y hy hxy
    rw [hform x hx, hform y hy]
    exact mul_lt_mul_of_pos_left (rpow_lt_rpow_of_neg hx hxy (by linarith)) h1
  · intro h
    by_contra hle
    push Not at hle
    have := h (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 two_pos) one_lt_two
    rw [hform 1 one_pos, hform 2 two_pos, one_rpow, mul_one] at this
    have : 1 ≤ (2 : ℝ) ^ (-σ) := one_le_rpow (by norm_num) (by linarith)
    nlinarith

/-- **AKMM, Theorem .4 as printed is false: affine transformations.** `u(c) = 2 log c` satisfies
the balanced-growth hypothesis (`u'((1 + γ)c) = (1 + γ)^{−1}u'(c)`) but is neither `log c` nor
`c^{1−σ}/(1 − σ)` for any `σ`. -/
theorem theorem_4A_4_affine_counterexample :
    (∀ γ : ℝ, -1 < γ → ∀ c : ℝ, 0 < c → 2 / ((1 + γ) * c) = (1 + γ)⁻¹ * (2 / c)) ∧
      (∃ c : ℝ, 0 < c ∧ 2 * Real.log c ≠ Real.log c) ∧
      ∀ σ : ℝ, (fun c : ℝ => 2 * Real.log c) 1 ≠ (1 : ℝ) ^ (1 - σ) / (1 - σ) ∨ σ = 1 := by
  refine ⟨fun γ hγ c hc => ?_, ⟨2, two_pos, fun h => ?_⟩, fun σ => ?_⟩
  · have : (1 + γ) ≠ 0 := by linarith
    field_simp
  · have : Real.log 2 = 0 := by linarith
    exact absurd this (Real.log_pos one_lt_two).ne'
  · by_cases hσ : σ = 1
    · exact Or.inr hσ
    · left
      simp only [Real.log_one, mul_zero, one_rpow]
      exact (one_div_ne_zero (sub_ne_zero.2 (Ne.symm hσ))).symm

/-- **AKMM, Theorem .4: without concavity `σ` can be negative.** `u(c) = c²/2`, with `u'(c) = c`
and `u''(c) = 1`, satisfies every hypothesis of `theorem_4A_4` (`u'((1 + γ)c) = (1 + γ)u'(c)`),
and its `σ = −u''(1)/u'(1)` is `−1 < 0`. -/
theorem theorem_4A_4_convex_example :
    (∀ c : ℝ, 0 < c → HasDerivAt (fun c : ℝ => c ^ 2 / 2) c c) ∧
      (∀ c : ℝ, 0 < c → HasDerivAt (fun c : ℝ => c) 1 c) ∧ (∀ c : ℝ, 0 < c → 0 < c) ∧
      (∀ γ : ℝ, -1 < γ → ∃ M, ∀ c : ℝ, 0 < c → (1 + γ) * c = M * c) ∧
      -(1 : ℝ) / 1 < 0 := by
  refine ⟨fun c _ => ?_, fun c _ => hasDerivAt_id c, fun c hc => hc,
    fun γ _ => ⟨1 + γ, fun c _ => rfl⟩, by norm_num⟩
  have := (hasDerivAt_pow 2 c).div_const 2
  convert this using 1
  ring

end AKMM.DynamicOptimization

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The NGM in the phase diagram

AKMM, App. 4.A.4, pp. 831–835: the resource constraint (4.A.8)
`k_{t+1} − k_t = f(k_t) − δk_t − c_t` and the Euler equation (4.A.9)
`u'(c_t) = βu'(c_{t+1})(f'(k_{t+1}) + 1 − δ)`.

* (4.A.10)–(4.A.12): `k` rises, stays or falls as `c_t` is below, on or above
  `f(k_t) − δk_t` (`eq_4A_12`).
* (4.A.13): `c` rises iff `k_{t+1} < k̄` iff `c_t > f(k_t) − δk_t + (k_t − k̄)` (`eq_4A_13`).
* The golden rule `f'(k^G) = δ` maximizes `f(k) − δk` (`golden_rule`), and `k̄ < k^G`
  (`steady_below_golden`).
* The TVC along an Euler path:
  `βᵗu'(c_t)(f'(k_t) + 1 − δ)k_t = u'(c₀)k_t/∏_{s=1}^{t−1}(f'(k_s) + 1 − δ)`
  (`phase_tvc_identity`); the book's product starts at `s = 0`, which is off by the factor
  `f'(k₀) + 1 − δ` (`phase_tvc_printed_differs`).
* Paths below the saddle path, which eventually stay above `k̂ > k^G`, violate the TVC: the
  expression tends to `+∞` (`phase_below_saddle_violates_tvc`, with `phase_return_below_one`).
* A convergent path (the saddle path) satisfies the TVC (`phase_saddle_tvc`).
* A path whose capital tends to `0` while consumption stays above `c̲ > 0` eventually violates
  `k ≥ 0` (`phase_above_saddle_infeasible`).

The facts read off Figures .1–.3 (the shape of the loci, the existence of the saddle path, and
that paths above or below it enter the regions described) are deferred.
-/

namespace AKMM.DynamicOptimization

open Filter Topology StokeyLucasPrescott.DeterministicDynamics

/-- **AKMM, (4.A.10)–(4.A.12), p. 832.** Under (4.A.8), `k_{t+1} > k_t ⇔ c_t < f(k_t) − δk_t`,
`k_{t+1} < k_t ⇔ c_t > f(k_t) − δk_t`, and `k_{t+1} = k_t ⇔ c_t = f(k_t) − δk_t`. -/
theorem eq_4A_12 {f : ℝ → ℝ} {δ k k' c : ℝ} (h48 : k' - k = f k - δ * k - c) :
    (k < k' ↔ c < f k - δ * k) ∧ (k' < k ↔ f k - δ * k < c) ∧ (k' = k ↔ c = f k - δ * k) := by
  refine ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun h => by linarith,
    fun h => by linarith⟩, ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- **AKMM, (4.A.13), pp. 832–833.** Let `u' > 0` be strictly decreasing and `f'` strictly
decreasing on `(0, ∞)`, `1 = β(f'(k̄) + 1 − δ)` (4.A.11), `β > 0`, and let `(k, c) → (k', c')`
satisfy (4.A.8)–(4.A.9) with positive values. Then `c' > c ⇔ k' < k̄ ⇔
c > f(k) − δk + (k − k̄)`. -/
theorem eq_4A_13 {f f' u' : ℝ → ℝ} {β δ kbar k k' c c' : ℝ} (hβ : 0 < β)
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0))
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hkbar : 0 < kbar) (h411 : 1 = β * (f' kbar + 1 - δ))
    (hk' : 0 < k') (hc : 0 < c) (hc' : 0 < c') (h48 : k' - k = f k - δ * k - c)
    (h49 : u' c = β * u' c' * (f' k' + 1 - δ)) :
    (c < c' ↔ k' < kbar) ∧ (k' < kbar ↔ f k - δ * k + (k - kbar) < c) := by
  have hpos := hu'pos c' hc'
  refine ⟨?_, ⟨fun h => by linarith, fun h => by linarith⟩⟩
  have step : c < c' ↔ 1 < β * (f' k' + 1 - δ) := by
    constructor
    · intro h
      have := hu' (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hc') h
      rw [h49] at this
      nlinarith
    · intro h
      by_contra hle
      push Not at hle
      have : u' c ≤ u' c' := hu'.antitoneOn (Set.mem_Ioi.2 hc') (Set.mem_Ioi.2 hc) hle
      rw [h49] at this
      nlinarith
  rw [step]
  constructor
  · intro h
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with he | hlt
    · rw [← he] at h; linarith
    · have := hf' (Set.mem_Ioi.2 hkbar) (Set.mem_Ioi.2 hk') hlt
      nlinarith
  · intro h
    have := hf' (Set.mem_Ioi.2 hk') (Set.mem_Ioi.2 hkbar) h
    nlinarith

/-- **AKMM, p. 832: the golden rule.** If `f` is concave on `[0, ∞)` and `f'(k^G) = δ`, then
`k^G` maximizes steady-state consumption `f(k) − δk` over `k ≥ 0`. -/
theorem golden_rule {f : ℝ → ℝ} {δ kG : ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) (hkG : 0 ≤ kG)
    (hd : HasDerivAt f δ kG) {k : ℝ} (hk : 0 ≤ k) : f k - δ * k ≤ f kG - δ * kG := by
  have := tangent_le hf (Set.mem_Ici.2 hkG) (Set.mem_Ici.2 hk) hd
  linarith

/-- **AKMM, p. 834: `k̄ < k^G`.** With `f'` strictly decreasing, `f'(k^G) = δ` and
`f'(k̄) = δ + 1/β − 1 > δ` (`0 < β < 1`), the modified golden rule lies below the golden rule. -/
theorem steady_below_golden {f' : ℝ → ℝ} {β δ kbar kG : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hkbar : 0 < kbar) (hkG : 0 < kG)
    (hbar : f' kbar = δ + 1 / β - 1) (hG : f' kG = δ) : kbar < kG := by
  by_contra hle
  push Not at hle
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  rcases eq_or_lt_of_le hle with he | hlt
  · rw [← he] at hbar; linarith
  · have := hf' (Set.mem_Ioi.2 hkG) (Set.mem_Ioi.2 hkbar) hlt
    linarith

/-- **AKMM, p. 834: the TVC along an Euler path**, with `R_s = f'(k_s) + 1 − δ`: if
`u'(c_s) = βu'(c_{s+1})R_{s+1}` for all `s`, then
`β^{t+1}u'(c_{t+1})R_{t+1}k_{t+1} = u'(c₀)k_{t+1}/∏_{s=1}^{t} R_s`, for `R_s ≠ 0`. -/
theorem phase_tvc_identity {β : ℝ} {mu R k : ℕ → ℝ}
    (heuler : ∀ s, mu s = β * mu (s + 1) * R (s + 1)) (hR : ∀ s, R s ≠ 0) (t : ℕ) :
    β ^ (t + 1) * mu (t + 1) * R (t + 1) * k (t + 1) =
      mu 0 * k (t + 1) / ∏ s ∈ Finset.range t, R (s + 1) := by
  have hprod : ∀ t, β ^ t * mu t * ∏ s ∈ Finset.range t, R (s + 1) = mu 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.prod_range_succ, ← ih, heuler t, pow_succ]
      ring
  have hP : ∏ s ∈ Finset.range t, R (s + 1) ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => hR _
  rw [eq_div_iff hP, ← hprod (t + 1), Finset.prod_range_succ]
  ring

/-- **AKMM, p. 834, corrected.** The printed `u'(c₀)k_t/∏_{s=0}^{t−1}R_s` differs from the true
value by the factor `R₀`: at `t = 1` the true value is `u'(c₀)k₁` and the printed one
`u'(c₀)k₁/R₀`, which differ whenever `R₀ ≠ 1`, `u'(c₀) ≠ 0` and `k₁ ≠ 0`. -/
theorem phase_tvc_printed_differs {β : ℝ} {mu R k : ℕ → ℝ}
    (heuler : ∀ s, mu s = β * mu (s + 1) * R (s + 1)) (hR0 : R 0 ≠ 1) (hR0' : R 0 ≠ 0)
    (hmu : mu 0 ≠ 0) (hk : k 1 ≠ 0) :
    β ^ 1 * mu 1 * R 1 * k 1 = mu 0 * k 1 ∧
      β ^ 1 * mu 1 * R 1 * k 1 ≠ mu 0 * k 1 / ∏ s ∈ Finset.range 1, R s := by
  have h1 : β ^ 1 * mu 1 * R 1 * k 1 = mu 0 * k 1 := by rw [heuler 0]; ring
  refine ⟨h1, ?_⟩
  rw [h1, Finset.prod_range_one]
  intro h
  rw [eq_div_iff hR0'] at h
  have : mu 0 * k 1 * (R 0 - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h2 | h2
  · rcases mul_eq_zero.1 h2 with h3 | h3
    · exact hmu h3
    · exact hk h3
  · exact hR0 (by linarith)

/-- AKMM, p. 834: if `k_s ≥ k̂ > k^G` with `f'` strictly decreasing and `f'(k^G) = δ`, then
`R_s = f'(k_s) + 1 − δ ≤ f'(k̂) + 1 − δ < 1`. -/
theorem phase_return_below_one {f' : ℝ → ℝ} {δ kG khat k : ℝ}
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hkG : 0 < kG) (hG : f' kG = δ) (hlt : kG < khat)
    (hk : khat ≤ k) : f' k + 1 - δ ≤ f' khat + 1 - δ ∧ f' khat + 1 - δ < 1 := by
  have hk0 : 0 < khat := hkG.trans hlt
  refine ⟨?_, ?_⟩
  · have := hf'.antitoneOn (Set.mem_Ioi.2 hk0) (Set.mem_Ioi.2 (hk0.trans_le hk)) hk
    linarith
  · have := hf' (Set.mem_Ioi.2 hkG) (Set.mem_Ioi.2 hk0) hlt
    linarith

/-- **AKMM, p. 834: paths below the saddle path violate the TVC.** Along an Euler path with
`u'(c₀) > 0` and returns `R_s > 0`, if from some date `T` on `R_s ≤ ρ < 1` (`k_s` above some
`k̂ > k^G`, `phase_return_below_one`) and `k_s ≥ κ > 0`, then
`βᵗu'(c_t)(f'(k_t) + 1 − δ)k_t → +∞`. -/
theorem phase_below_saddle_violates_tvc {β ρ κ : ℝ} {mu R k : ℕ → ℝ} {T : ℕ}
    (heuler : ∀ s, mu s = β * mu (s + 1) * R (s + 1)) (hR : ∀ s, 0 < R s) (hmu : 0 < mu 0)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hRρ : ∀ s, T ≤ s → R s ≤ ρ) (hκ : 0 < κ)
    (hkκ : ∀ s, T ≤ s → κ ≤ k s) :
    Tendsto (fun t => β ^ (t + 1) * mu (t + 1) * R (t + 1) * k (t + 1)) atTop atTop := by
  set P : ℕ → ℝ := fun t => ∏ s ∈ Finset.range t, R (s + 1)
  have hP : ∀ t, 0 < P t := fun t => Finset.prod_pos fun s _ => hR _
  have hPbound : ∀ n, P (T + n) ≤ P T * ρ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : P (T + (n + 1)) = P (T + n) * R (T + n + 1) := Finset.prod_range_succ _ _
      rw [e, pow_succ, ← mul_assoc]
      exact mul_le_mul ih (hRρ _ (by omega)) (hR _).le (mul_pos (hP T) (pow_pos hρ0 n)).le
  have hgrow : Tendsto (fun n : ℕ => mu 0 * κ / (P T * ρ ^ n)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (ρ⁻¹) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv_iff₀.2 ⟨hρ0, hρ1⟩)
    have h2 := h1.const_mul_atTop (div_pos (mul_pos hmu hκ) (hP T))
    refine h2.congr fun n => ?_
    rw [inv_pow]
    field_simp
  have hshift : Tendsto (fun t => mu 0 * κ / (P T * ρ ^ (t - T))) atTop atTop :=
    hgrow.comp (tendsto_sub_atTop_nat T)
  refine tendsto_atTop_mono' _ ?_ hshift
  filter_upwards [eventually_ge_atTop T] with t ht
  rw [phase_tvc_identity heuler (fun s => (hR s).ne') t]
  obtain ⟨n, rfl⟩ : ∃ n, t = T + n := ⟨t - T, by omega⟩
  rw [show T + n - T = n by omega]
  have hb := hPbound n
  have hPpos := hP (T + n)
  have hk := hkκ (T + n + 1) (by omega)
  have hden : 0 < P T * ρ ^ n := mul_pos (hP T) (pow_pos hρ0 n)
  calc mu 0 * κ / (P T * ρ ^ n) ≤ mu 0 * κ / P (T + n) :=
        div_le_div_of_nonneg_left (mul_pos hmu hκ).le hPpos hb
    _ ≤ mu 0 * k (T + n + 1) / P (T + n) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk hmu.le) hPpos.le

/-- **AKMM, p. 834: the saddle path satisfies the TVC.** If `0 ≤ β < 1` and `k_t → k̄`,
`c_t → c̄`, with `u'` continuous at `c̄` and `f'` continuous at `k̄`, then
`βᵗu'(c_t)(f'(k_t) + 1 − δ)k_t → 0`. -/
theorem phase_saddle_tvc {u' f' : ℝ → ℝ} {β δ kbar cbar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {k c : ℕ → ℝ} (hk : Tendsto k atTop (𝓝 kbar)) (hc : Tendsto c atTop (𝓝 cbar))
    (hu' : ContinuousAt u' cbar) (hf' : ContinuousAt f' kbar) :
    Tendsto (fun t => β ^ t * (u' (c t) * (f' (k t) + 1 - δ) * k t)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t => u' (c t) * (f' (k t) + 1 - δ) * k t) atTop
      (𝓝 (u' cbar * (f' kbar + 1 - δ) * kbar)) :=
    (((hu'.tendsto.comp hc).mul (((hf'.tendsto.comp hk).add_const 1).sub_const δ)).mul hk)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul h1

/-- **AKMM, p. 834: paths above the saddle path become infeasible.** If `f(0) = 0` with `f`
continuous at `0`, `k_t → 0` and `c_t ≥ c̲ > 0`, then (4.A.8) eventually forces `k_{t+1} < 0`. -/
theorem phase_above_saddle_infeasible {f : ℝ → ℝ} {δ clow : ℝ} {k c : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : ContinuousAt f 0) (hclow : 0 < clow) (hc : ∀ t, clow ≤ c t)
    (hk : Tendsto k atTop (𝓝 0)) (h48 : ∀ t, k (t + 1) = f (k t) + (1 - δ) * k t - c t) :
    ∃ t, k (t + 1) < 0 := by
  have h1 : Tendsto (fun t => f (k t) + (1 - δ) * k t) atTop (𝓝 (f 0 + (1 - δ) * 0)) :=
    (hf.tendsto.comp hk).add (hk.const_mul _)
  rw [hf0, mul_zero, add_zero] at h1
  obtain ⟨t, ht⟩ := (h1.eventually (gt_mem_nhds hclow)).exists
  exact ⟨t, by rw [h48]; linarith [hc t]⟩

end AKMM.DynamicOptimization

set_option linter.style.longLine false
#print axioms AKMM.DynamicOptimization.objective
#print axioms AKMM.DynamicOptimization.FeasibleT
#print axioms AKMM.DynamicOptimization.seq_objective_congr
#print axioms AKMM.DynamicOptimization.seq_weierstrass
#print axioms AKMM.DynamicOptimization.seqCounterGamma
#print axioms AKMM.DynamicOptimization.seq_weierstrass_counterexample
#print axioms AKMM.DynamicOptimization.cs_gamma_iff
#print axioms AKMM.DynamicOptimization.eq_4_2
#print axioms AKMM.DynamicOptimization.ngm_gamma_iff
#print axioms AKMM.DynamicOptimization.ngm_resource_binds
#print axioms AKMM.DynamicOptimization.twoPeriodValue
#print axioms AKMM.DynamicOptimization.twoPeriod_lifetime_budget
#print axioms AKMM.DynamicOptimization.eq_4_4_to_4_6
#print axioms AKMM.DynamicOptimization.twoPeriod_euler
#print axioms AKMM.DynamicOptimization.twoPeriod_interior
#print axioms AKMM.DynamicOptimization.twoPeriod_closed_form
#print axioms AKMM.DynamicOptimization.twoPeriod_closed_form_optimal
#print axioms AKMM.DynamicOptimization.finite_fderiv_apply
#print axioms AKMM.DynamicOptimization.finite_telescope
#print axioms AKMM.DynamicOptimization.result_1
#print axioms AKMM.DynamicOptimization.result_1_F2_nonpos
#print axioms AKMM.DynamicOptimization.result_1_of_antitone
#print axioms AKMM.DynamicOptimization.ngm_return_concave
#print axioms AKMM.DynamicOptimization.ngm_return_strictConcave
#print axioms AKMM.DynamicOptimization.ngm_hasFDerivAt
#print axioms AKMM.DynamicOptimization.NGMFeasible
#print axioms AKMM.DynamicOptimization.ngmObjective
#print axioms AKMM.DynamicOptimization.ngm_terminal_zero
#print axioms AKMM.DynamicOptimization.eq_4_10
#print axioms AKMM.DynamicOptimization.ngm_finite_sufficient
#print axioms AKMM.DynamicOptimization.finite_unique_max
#print axioms AKMM.DynamicOptimization.ngm_finite_unique
#print axioms AKMM.DynamicOptimization.ngm_objective_update
#print axioms AKMM.DynamicOptimization.ngm_finite_interior
#print axioms AKMM.DynamicOptimization.example41Rate
#print axioms AKMM.DynamicOptimization.example41_rate_zero
#print axioms AKMM.DynamicOptimization.example41_rate_recursion
#print axioms AKMM.DynamicOptimization.example41_rate_geometric
#print axioms AKMM.DynamicOptimization.example41_kT
#print axioms AKMM.DynamicOptimization.example41_kTminus1
#print axioms AKMM.DynamicOptimization.example41_consumption_share
#print axioms AKMM.DynamicOptimization.example41_rate_nonneg
#print axioms AKMM.DynamicOptimization.example41_rate_lt_one
#print axioms AKMM.DynamicOptimization.example41_rate_pos
#print axioms AKMM.DynamicOptimization.example41Plan
#print axioms AKMM.DynamicOptimization.example41_plan_succ
#print axioms AKMM.DynamicOptimization.example41_plan_pos
#print axioms AKMM.DynamicOptimization.eq_4_11
#print axioms AKMM.DynamicOptimization.example_4_1
#print axioms AKMM.DynamicOptimization.crra
#print axioms AKMM.DynamicOptimization.crra_tendsto_log
#print axioms AKMM.DynamicOptimization.crra_tendsto_zero_of_one_le
#print axioms AKMM.DynamicOptimization.crra_tendsto_atBot_of_lt_one
#print axioms AKMM.DynamicOptimization.crra_leontief_limit
#print axioms AKMM.DynamicOptimization.example42_repeated
#print axioms AKMM.DynamicOptimization.example42_ratio
#print axioms AKMM.DynamicOptimization.example42_eis
#print axioms AKMM.DynamicOptimization.example42_log_shares
#print axioms AKMM.DynamicOptimization.example42_consumption
#print axioms AKMM.DynamicOptimization.example42_income_effect
#print axioms AKMM.DynamicOptimization.example42_substitution_effect
#print axioms AKMM.DynamicOptimization.infinite_constant_summable_iff
#print axioms AKMM.DynamicOptimization.infinite_growth_term
#print axioms AKMM.DynamicOptimization.infinite_growth_summable_iff
#print axioms AKMM.DynamicOptimization.infinite_growth_sigma_gt_one
#print axioms AKMM.DynamicOptimization.infinite_growth_sigma_lt_one
#print axioms AKMM.DynamicOptimization.infinite_growth_negative_fails
#print axioms AKMM.DynamicOptimization.ponziAssets
#print axioms AKMM.DynamicOptimization.ponzi_improvement
#print axioms AKMM.DynamicOptimization.ponzi_no_maximum
#print axioms AKMM.DynamicOptimization.eq_4_13_finite
#print axioms AKMM.DynamicOptimization.eq_4_13
#print axioms AKMM.DynamicOptimization.eq_4_14
#print axioms AKMM.DynamicOptimization.example_4_3_path
#print axioms AKMM.DynamicOptimization.example_4_3_c0
#print axioms AKMM.DynamicOptimization.example_4_3
#print axioms AKMM.DynamicOptimization.proposition_4_4
#print axioms AKMM.DynamicOptimization.proposition_4_4_F1_nonneg
#print axioms AKMM.DynamicOptimization.prop44CounterF
#print axioms AKMM.DynamicOptimization.proposition_4_4_counterexample
#print axioms AKMM.DynamicOptimization.proposition_4_4_ngm
#print axioms AKMM.DynamicOptimization.tvc_stationary
#print axioms AKMM.DynamicOptimization.ngm_steady_state_optimal
#print axioms AKMM.DynamicOptimization.tvc_balanced_growth
#print axioms AKMM.DynamicOptimization.eq_4_16_of_euler
#print axioms AKMM.DynamicOptimization.eq_4_16
#print axioms AKMM.DynamicOptimization.example_4_5_limit
#print axioms AKMM.DynamicOptimization.example_4_5_tvc
#print axioms AKMM.DynamicOptimization.example_4_6
#print axioms AKMM.DynamicOptimization.example_4_5_steady
#print axioms AKMM.DynamicOptimization.example_4_5_convergence
#print axioms AKMM.DynamicOptimization.example_4_5
#print axioms AKMM.DynamicOptimization.eq_4_18
#print axioms AKMM.DynamicOptimization.adjustedDiscount
#print axioms AKMM.DynamicOptimization.eq_4_19
#print axioms AKMM.DynamicOptimization.bgp_hasFDerivAt
#print axioms AKMM.DynamicOptimization.bgp_euler_detrended
#print axioms AKMM.DynamicOptimization.bgp_euler_original
#print axioms AKMM.DynamicOptimization.bgp_condition
#print axioms AKMM.DynamicOptimization.bgp_no_growth
#print axioms AKMM.DynamicOptimization.bgp_cobbDouglas
#print axioms AKMM.DynamicOptimization.eq_4_22
#print axioms AKMM.DynamicOptimization.eq_4_22_policy
#print axioms AKMM.DynamicOptimization.periodicGamma
#print axioms AKMM.DynamicOptimization.periodicF
#print axioms AKMM.DynamicOptimization.periodic_bellman
#print axioms AKMM.DynamicOptimization.periodic_printed_gamma
#print axioms AKMM.DynamicOptimization.delayedGamma
#print axioms AKMM.DynamicOptimization.delayedF
#print axioms AKMM.DynamicOptimization.delayed_bellman
#print axioms AKMM.DynamicOptimization.delayedPrinted
#print axioms AKMM.DynamicOptimization.delayed_no_discount_not_contraction
#print axioms AKMM.DynamicOptimization.property_1
#print axioms AKMM.DynamicOptimization.property_2
#print axioms AKMM.DynamicOptimization.property_3
#print axioms AKMM.DynamicOptimization.property_4
#print axioms AKMM.DynamicOptimization.prop5F
#print axioms AKMM.DynamicOptimization.property_5_counterexample
#print axioms AKMM.DynamicOptimization.property_5_corrected
#print axioms AKMM.DynamicOptimization.property_5_ngm
#print axioms AKMM.DynamicOptimization.vfe_log_max
#print axioms AKMM.DynamicOptimization.eq_4_23
#print axioms AKMM.DynamicOptimization.example_4_7_iterate
#print axioms AKMM.DynamicOptimization.example_4_7_V2
#print axioms AKMM.DynamicOptimization.example_4_7_coefficients
#print axioms AKMM.DynamicOptimization.example_4_7
#print axioms AKMM.DynamicOptimization.eq_4_25
#print axioms AKMM.DynamicOptimization.example_4_8
#print axioms AKMM.DynamicOptimization.ngm_max_capital
#print axioms AKMM.DynamicOptimization.eq_4_26
#print axioms AKMM.DynamicOptimization.eq_4_27
#print axioms AKMM.DynamicOptimization.eq_4_28
#print axioms AKMM.DynamicOptimization.ngm_policy_direction
#print axioms AKMM.DynamicOptimization.ngm_global_convergence
#print axioms AKMM.DynamicOptimization.ngm_global_convergence_full
#print axioms AKMM.DynamicOptimization.eq_4_29
#print axioms AKMM.DynamicOptimization.eq_4_29_quadratic
#print axioms AKMM.DynamicOptimization.slopeRoot
#print axioms AKMM.DynamicOptimization.slopeRootOther
#print axioms AKMM.DynamicOptimization.slopeRoot_disc_nonneg
#print axioms AKMM.DynamicOptimization.slopeRoot_isRoot
#print axioms AKMM.DynamicOptimization.slopeRoot_sqrt_pos
#print axioms AKMM.DynamicOptimization.slopeRoot_eq
#print axioms AKMM.DynamicOptimization.slopeRoot_mem
#print axioms AKMM.DynamicOptimization.slopeRoot_zero
#print axioms AKMM.DynamicOptimization.slopeRoot_strictAnti
#print axioms AKMM.DynamicOptimization.slopeRoot_tendsto_zero
#print axioms AKMM.DynamicOptimization.slopeRoot_tendsto_one
#print axioms AKMM.DynamicOptimization.theta_crra
#print axioms AKMM.DynamicOptimization.theta_crra_strictAnti
#print axioms AKMM.DynamicOptimization.crra_slope_limits
#print axioms AKMM.DynamicOptimization.theta_cobbDouglas
#print axioms AKMM.DynamicOptimization.thetaCD
#print axioms AKMM.DynamicOptimization.thetaCD_pos
#print axioms AKMM.DynamicOptimization.theta_cobbDouglas_strictAnti_alpha
#print axioms AKMM.DynamicOptimization.theta_cobbDouglas_strictMono_delta
#print axioms AKMM.DynamicOptimization.cobbDouglas_slope_mono
#print axioms AKMM.DynamicOptimization.eq_4A_2
#print axioms AKMM.DynamicOptimization.appendix_4A_too_restrictive
#print axioms AKMM.DynamicOptimization.appendix_4A_partial
#print axioms AKMM.DynamicOptimization.theorem_4A_3
#print axioms AKMM.DynamicOptimization.bgp_marginal_ratio
#print axioms AKMM.DynamicOptimization.crraBGP_const
#print axioms AKMM.DynamicOptimization.theorem_4A_4
#print axioms AKMM.DynamicOptimization.theorem_4A_4_sigma_pos
#print axioms AKMM.DynamicOptimization.theorem_4A_4_affine_counterexample
#print axioms AKMM.DynamicOptimization.theorem_4A_4_convex_example
#print axioms AKMM.DynamicOptimization.eq_4A_12
#print axioms AKMM.DynamicOptimization.eq_4A_13
#print axioms AKMM.DynamicOptimization.golden_rule
#print axioms AKMM.DynamicOptimization.steady_below_golden
#print axioms AKMM.DynamicOptimization.phase_tvc_identity
#print axioms AKMM.DynamicOptimization.phase_tvc_printed_differs
#print axioms AKMM.DynamicOptimization.phase_return_below_one
#print axioms AKMM.DynamicOptimization.phase_below_saddle_violates_tvc
#print axioms AKMM.DynamicOptimization.phase_saddle_tvc
#print axioms AKMM.DynamicOptimization.phase_above_saddle_infeasible
