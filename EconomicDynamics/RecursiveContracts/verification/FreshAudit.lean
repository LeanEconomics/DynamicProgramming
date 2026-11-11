import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The endowment chain and the autarky value (Miao §22.1, pp. 774–775)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1, pp. 774–775. The agent's
endowment follows a Markov chain on finitely many states `θ₁, …, θₙ` (an arbitrary finite type
`ι`) with transition probabilities `pl i j = π(θⱼ | θᵢ)`. The outside option is the autarky value
`U_d(y_t) = E_t Σ_{s ≥ t} β^{s-t} u(y_s)`.

We define the one-step conditional expectation `lc_condExp`, the autarky value `lc_autarky` as the
discounted series of iterated conditional expectations of a reward `r = u ∘ θ`, and prove:
the series converges, it satisfies the recursion `U_d = r + β π U_d`, it is the unique solution
of that recursion, and it splits at any fixed date `τ` as
`U_d(θᵢ) = E[Σ_{t<τ} β^t r(y_t) | y₀ = θᵢ] + β^τ E[U_d(y_τ) | y₀ = θᵢ]`
(the identity behind the definition of `d_i(τ)` in §22.1.3, p. 780, for deterministic dates).
-/

namespace Miao.RecursiveContracts

open Filter Topology

variable {ι : Type*} [Fintype ι]

/-- The conditional expectation `(π f)(θᵢ) = Σⱼ π(θⱼ | θᵢ) f(θⱼ)` (Miao, p. 774). -/
def lc_condExp (pl : ι → ι → ℝ) (f : ι → ℝ) (i : ι) : ℝ := ∑ j, pl i j * f j

/-- `pl` is a transition matrix: nonnegative entries and rows summing to one (Miao, p. 774). -/
def lc_IsStochastic (pl : ι → ι → ℝ) : Prop := (∀ i j, 0 ≤ pl i j) ∧ ∀ i, ∑ j, pl i j = 1

/-- The autarky value `U_d(θᵢ) = Σ_t β^t E[r(y_t) | y₀ = θᵢ]` (Miao, p. 775), for a reward
`r = u ∘ θ`. -/
noncomputable def lc_autarky (β : ℝ) (pl : ι → ι → ℝ) (r : ι → ℝ) (i : ι) : ℝ :=
  ∑' t : ℕ, β ^ t * (lc_condExp pl)^[t] r i

/-- The conditional expectation is bounded by any bound on the function. -/
theorem lc_condExp_abs_le {pl : ι → ι → ℝ} (hpl : lc_IsStochastic pl) {f : ι → ℝ} {M : ℝ}
    (hf : ∀ j, |f j| ≤ M) (i : ι) : |lc_condExp pl f i| ≤ M := by
  unfold lc_condExp
  calc |∑ j, pl i j * f j| ≤ ∑ j, |pl i j * f j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, pl i j * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hpl.1 i j)]
        exact mul_le_mul_of_nonneg_left (hf j) (hpl.1 i j)
    _ = M := by rw [← Finset.sum_mul, hpl.2 i, one_mul]

/-- Iterated conditional expectations keep the bound. -/
theorem lc_condExp_iter_abs_le {pl : ι → ι → ℝ} (hpl : lc_IsStochastic pl) {f : ι → ℝ} {M : ℝ}
    (hf : ∀ j, |f j| ≤ M) (t : ℕ) (i : ι) : |(lc_condExp pl)^[t] f i| ≤ M := by
  induction t generalizing i with
  | zero => exact hf i
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact lc_condExp_abs_le hpl ih i

omit [Fintype ι] in
/-- A finite family of reals has a common bound. -/
theorem lc_exists_bound [Finite ι] (f : ι → ℝ) : ∃ M, ∀ j, |f j| ≤ M := by
  cases nonempty_fintype ι
  exact ⟨∑ j, |f j|, fun j => Finset.single_le_sum (f := fun j => |f j|)
    (fun k _ => abs_nonneg (f k)) (Finset.mem_univ j)⟩

/-- The autarky series converges (Miao, p. 775). -/
theorem lc_autarky_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (r : ι → ℝ) (i : ι) :
    Summable fun t : ℕ => β ^ t * (lc_condExp pl)^[t] r i := by
  obtain ⟨M, hM⟩ := lc_exists_bound r
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
  exact mul_le_mul_of_nonneg_right (lc_condExp_iter_abs_le hpl hM t i) (pow_nonneg hβ0 t)

/-- Miao, p. 775: the autarky value satisfies the recursion
`U_d(θᵢ) = u(θᵢ) + β Σⱼ π(θⱼ | θᵢ) U_d(θⱼ)`. -/
theorem lc_autarky_recursion {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (r : ι → ℝ) (i : ι) :
    lc_autarky β pl r i = r i + β * ∑ j, pl i j * lc_autarky β pl r j := by
  unfold lc_autarky
  rw [(lc_autarky_summable hβ0 hβ1 hpl r i).tsum_eq_zero_add]
  congr 1
  · simp
  · have hs := fun j => lc_autarky_summable hβ0 hβ1 hpl r j
    have h1 : ∀ t : ℕ, β ^ (t + 1) * (lc_condExp pl)^[t + 1] r i =
        β * ∑ j, pl i j * (β ^ t * (lc_condExp pl)^[t] r j) := by
      intro t
      rw [Function.iterate_succ_apply', lc_condExp, Finset.mul_sum, Finset.mul_sum, pow_succ]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [h1]
    rw [tsum_mul_left, Summable.tsum_finsetSum fun j _ => (hs j).mul_left (pl i j)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact tsum_mul_left

/-- Miao, p. 775: the autarky value is the unique solution of the recursion
`f = r + β π f` (finite states, `0 ≤ β < 1`). -/
theorem lc_autarky_unique {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (r f : ι → ℝ)
    (hf : ∀ i, f i = r i + β * ∑ j, pl i j * f j) : f = lc_autarky β pl r := by
  have hg := lc_autarky_recursion hβ0 hβ1 hpl r
  generalize lc_autarky β pl r = g at hg ⊢
  rcases isEmpty_or_nonempty ι with hι | hι
  · funext i; exact (IsEmpty.false i).elim
  obtain ⟨i0, hi0⟩ := Finite.exists_max fun i => |f i - g i|
  have hd : ∀ i, |f i - g i| ≤ β * |f i0 - g i0| := by
    intro i
    have : f i - g i = β * lc_condExp pl (fun j => f j - g j) i := by
      rw [hf i, hg i, lc_condExp]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [this, abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (lc_condExp_abs_le hpl hi0 i) hβ0
  have h0 : |f i0 - g i0| = 0 := by
    have := hd i0
    have hn := abs_nonneg (f i0 - g i0)
    nlinarith
  funext i
  have := hi0 i
  rw [h0] at this
  linarith [abs_nonneg (f i - g i), abs_eq_zero.mp (le_antisymm this (abs_nonneg _))]

/-- Iterated conditional expectations are linear. -/
theorem lc_condExp_iter_linear (pl : ι → ι → ℝ) (a : ℝ) (f g : ι → ℝ) (t : ℕ) (i : ι) :
    (lc_condExp pl)^[t] (fun j => f j + a * g j) i =
      (lc_condExp pl)^[t] f i + a * (lc_condExp pl)^[t] g i := by
  induction t generalizing f g i with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply]
    have : lc_condExp pl (fun j => f j + a * g j) =
        fun j => lc_condExp pl f j + a * lc_condExp pl g j := by
      funext j
      simp only [lc_condExp, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this, ih]

/-- Miao, p. 780 (for a deterministic date `τ`): the autarky value splits as
`U_d(θᵢ) = Σ_{t<τ} β^t E[u(y_t) | y₀ = θᵢ] + β^τ E[U_d(y_τ) | y₀ = θᵢ]`. -/
theorem lc_autarky_split {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (r : ι → ℝ) (τ : ℕ) (i : ι) :
    lc_autarky β pl r i = ∑ t ∈ Finset.range τ, β ^ t * (lc_condExp pl)^[t] r i +
      β ^ τ * (lc_condExp pl)^[τ] (lc_autarky β pl r) i := by
  induction τ generalizing i with
  | zero => simp
  | succ τ ih =>
    rw [ih, Finset.sum_range_succ]
    have hrec : lc_autarky β pl r = fun j => r j + β * lc_condExp pl (lc_autarky β pl r) j := by
      funext j; exact lc_autarky_recursion hβ0 hβ1 hpl r j
    have : (lc_condExp pl)^[τ] (lc_autarky β pl r) i =
        (lc_condExp pl)^[τ] r i + β * (lc_condExp pl)^[τ + 1] (lc_autarky β pl r) i := by
      conv_lhs => rw [hrec]
      rw [lc_condExp_iter_linear, Function.iterate_succ_apply]
    rw [this, pow_succ]
    ring

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The sequence problem with one-sided limited commitment (Miao §22.1, pp. 774–776)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1, pp. 774–776. The contract is a
consumption plan on the event tree of endowment histories. A node is a pair `(y_t, past)`: the
current state and the list of earlier states (most recent first); `lc_ext h j` is the successor
node in which the next state is `θⱼ`. `lc_treeExp pl t F h` is the conditional expectation at `h`
of `F` evaluated `t` periods later, and `lc_treeValue` is the discounted value
`E_t Σ_{s ≥ t} β^{s-t} F`.

We prove: the value of the autarky plan at every node is `U_d(y_t)` (so autarky satisfies the
incentive constraints (22.1) with equality); with `v₀ ≥ U_d(y₀)` the participation constraint
(22.2) implies (22.1) at the initial node; and the recursive decomposition behind the Bellman
equation of §22.1.1: for any bounded feasible plan, the date-0 consumption and the continuation
values `wⱼ` satisfy (22.3) and (22.4), the principal's value satisfies the one-step recursion, and
the continuation plan at `θⱼ` is feasible for the promise `wⱼ`.

Departure: the incentive constraint (22.1) is imposed at every node of the tree (not only at
nodes reachable from `y₀`); constraints at other nodes do not affect values at `y₀`.
-/

namespace Miao.RecursiveContracts

open Filter Topology

variable {ι : Type*} [Fintype ι]

/-- The successor node: next period's state is `θⱼ`. -/
def lc_ext (h : ι × List ι) (j : ι) : ι × List ι := (j, h.1 :: h.2)

/-- `E_t[F(h_{t+s})]` on the event tree (Miao, p. 775). -/
def lc_treeExp (pl : ι → ι → ℝ) : ℕ → (ι × List ι → ℝ) → ι × List ι → ℝ
  | 0, F, h => F h
  | t + 1, F, h => ∑ j, pl h.1 j * lc_treeExp pl t F (lc_ext h j)

/-- The discounted value `E_t Σ_{s ≥ 0} β^s F(h_{t+s})` at node `h` (Miao, p. 775). -/
noncomputable def lc_treeValue (β : ℝ) (pl : ι → ι → ℝ) (F : ι × List ι → ℝ)
    (h : ι × List ι) : ℝ :=
  ∑' t : ℕ, β ^ t * lc_treeExp pl t F h

/-- Tree expectations keep bounds. -/
theorem lc_treeExp_abs_le {pl : ι → ι → ℝ} (hpl : lc_IsStochastic pl) {F : ι × List ι → ℝ}
    {M : ℝ} (hF : ∀ h, |F h| ≤ M) (t : ℕ) (h : ι × List ι) : |lc_treeExp pl t F h| ≤ M := by
  induction t generalizing h with
  | zero => exact hF h
  | succ t ih =>
    simp only [lc_treeExp]
    exact lc_condExp_abs_le hpl (f := fun j => lc_treeExp pl t F (lc_ext h j)) (fun j => ih _) h.1

/-- The discounted value of a bounded plan converges. -/
theorem lc_treeValue_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) {F : ι × List ι → ℝ} {M : ℝ} (hF : ∀ h, |F h| ≤ M)
    (h : ι × List ι) : Summable fun t : ℕ => β ^ t * lc_treeExp pl t F h := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
  exact mul_le_mul_of_nonneg_right (lc_treeExp_abs_le hpl hF t h) (pow_nonneg hβ0 t)

/-- Miao, p. 775: the one-step recursion
`V(h) = F(h) + β Σⱼ π(θⱼ | y_t) V(h, θⱼ)` for the value of a bounded plan. -/
theorem lc_treeValue_recursion {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) {F : ι × List ι → ℝ} {M : ℝ} (hF : ∀ h, |F h| ≤ M)
    (h : ι × List ι) :
    lc_treeValue β pl F h = F h + β * ∑ j, pl h.1 j * lc_treeValue β pl F (lc_ext h j) := by
  unfold lc_treeValue
  rw [(lc_treeValue_summable hβ0 hβ1 hpl hF h).tsum_eq_zero_add]
  congr 1
  · simp [lc_treeExp]
  · have hs := fun j => lc_treeValue_summable hβ0 hβ1 hpl hF (lc_ext h j)
    have h1 : ∀ t : ℕ, β ^ (t + 1) * lc_treeExp pl (t + 1) F h =
        β * ∑ j, pl h.1 j * (β ^ t * lc_treeExp pl t F (lc_ext h j)) := by
      intro t
      rw [lc_treeExp, Finset.mul_sum, Finset.mul_sum, pow_succ]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [h1]
    rw [tsum_mul_left, Summable.tsum_finsetSum fun j _ => (hs j).mul_left (pl h.1 j)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact tsum_mul_left

/-- Expectations of a function of the current state reduce to the chain's iterates. -/
theorem lc_treeExp_state (pl : ι → ι → ℝ) (r : ι → ℝ) (t : ℕ) (h : ι × List ι) :
    lc_treeExp pl t (fun k => r k.1) h = (lc_condExp pl)^[t] r h.1 := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    rw [lc_treeExp, Function.iterate_succ_apply', lc_condExp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ih]
    rfl

/-- Miao, (22.1), p. 775: the incentive constraint at every node,
`E_t Σ_j β^j u(c_{t+j}) ≥ U_d(y_t)`. -/
def lc_IC (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (θ : ι → ℝ) (c : ι × List ι → ℝ) : Prop :=
  ∀ h, lc_autarky β pl (fun i => u (θ i)) h.1 ≤ lc_treeValue β pl (fun k => u (c k)) h

/-- Miao, (22.2), p. 775: the participation constraint `E Σ_t β^t u(c_t) ≥ v₀` at node `h`. -/
def lc_PK (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (c : ι × List ι → ℝ) (h : ι × List ι)
    (v₀ : ℝ) : Prop :=
  v₀ ≤ lc_treeValue β pl (fun k => u (c k)) h

/-- A plan with bounded consumption and bounded utility. -/
def lc_BddPlan (u : ℝ → ℝ) (c : ι × List ι → ℝ) : Prop :=
  ∃ M, ∀ h, |c h| ≤ M ∧ |u (c h)| ≤ M

/-- The principal's value `E_t Σ_s β^s (y_{t+s} − c_{t+s})` (Miao, p. 775). -/
noncomputable def lc_principalValue (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ)
    (c : ι × List ι → ℝ) (h : ι × List ι) : ℝ :=
  lc_treeValue β pl (fun k => θ k.1 - c k) h

/-- Miao, (22.1), p. 775: the value of the autarky plan `c_t = y_t` at every node is the autarky
value `U_d(y_t)`; in particular autarky satisfies every incentive constraint (22.1), with
equality. -/
theorem eq_22_1 (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (θ : ι → ℝ) (h : ι × List ι) :
    lc_treeValue β pl (fun k => u (θ k.1)) h = lc_autarky β pl (fun i => u (θ i)) h.1 ∧
      lc_IC β pl u θ (fun k => θ k.1) := by
  have key : ∀ h : ι × List ι, lc_treeValue β pl (fun k => u (θ k.1)) h =
      lc_autarky β pl (fun i => u (θ i)) h.1 := by
    intro h
    unfold lc_treeValue lc_autarky
    congr 1
    funext t
    rw [← lc_treeExp_state pl (fun i => u (θ i)) t h]
  exact ⟨key h, fun h => (key h).ge⟩

/-- Miao, (22.2), p. 775: since `v₀ ≥ U_d(y₀)`, the participation constraint (22.2) implies the
incentive constraint (22.1) at the initial node. -/
theorem eq_22_2 (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (θ : ι → ℝ) (c : ι × List ι → ℝ)
    (h : ι × List ι) (v₀ : ℝ) (hv₀ : lc_autarky β pl (fun i => u (θ i)) h.1 ≤ v₀)
    (hPK : lc_PK β pl u c h v₀) :
    lc_autarky β pl (fun i => u (θ i)) h.1 ≤ lc_treeValue β pl (fun k => u (c k)) h :=
  hv₀.trans hPK

/-- Miao, (22.3), p. 776, derived from the sequence problem: for a plan satisfying (22.1), the
continuation values `wⱼ = E_{t+1} Σ β^s u(c)` after `θⱼ` satisfy `wⱼ ≥ U_d(θⱼ)`. -/
theorem eq_22_3 (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (θ : ι → ℝ) (c : ι × List ι → ℝ)
    (hIC : lc_IC β pl u θ c) (h : ι × List ι) (j : ι) :
    lc_autarky β pl (fun i => u (θ i)) j ≤ lc_treeValue β pl (fun k => u (c k)) (lc_ext h j) :=
  hIC (lc_ext h j)

/-- Miao, (22.4), p. 776, derived from the sequence problem: for a bounded plan satisfying
(22.2) at `h`, `u(c) + β Σⱼ π(θⱼ | y) wⱼ ≥ v₀` with `wⱼ` the continuation values. -/
theorem eq_22_4 {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (u : ℝ → ℝ) (c : ι × List ι → ℝ) (hc : lc_BddPlan u c)
    (h : ι × List ι) (v₀ : ℝ) (hPK : lc_PK β pl u c h v₀) :
    v₀ ≤ u (c h) + β * ∑ j, pl h.1 j * lc_treeValue β pl (fun k => u (c k)) (lc_ext h j) := by
  obtain ⟨M, hM⟩ := hc
  have := lc_treeValue_recursion hβ0 hβ1 hpl (F := fun k => u (c k)) (fun k => (hM k).2) h
  unfold lc_PK at hPK
  rw [this] at hPK
  exact hPK

/-- Miao, p. 776: the principal's value of a bounded plan satisfies the one-step recursion
`Π(h) = y − c + β Σⱼ π(θⱼ | y) Π(h, θⱼ)`, the objective of the Bellman equation. -/
theorem lc_principal_recursion {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (u : ℝ → ℝ) (θ : ι → ℝ) (c : ι × List ι → ℝ)
    (hc : lc_BddPlan u c) (h : ι × List ι) :
    lc_principalValue β pl θ c h =
      θ h.1 - c h + β * ∑ j, pl h.1 j * lc_principalValue β pl θ c (lc_ext h j) := by
  obtain ⟨M, hM⟩ := hc
  obtain ⟨K, hK⟩ := lc_exists_bound θ
  exact lc_treeValue_recursion hβ0 hβ1 hpl (F := fun k => θ k.1 - c k) (M := K + M)
    (fun k => (abs_sub _ _).trans (add_le_add (hK k.1) (hM k).1)) h

/-- Miao, p. 776: the continuation of a feasible plan after `θⱼ` is feasible for the promise
`wⱼ`: it satisfies (22.1) and the promise-keeping constraint (22.2) with `v₀ = wⱼ` (with
equality), so the problem can be written recursively with the promised value as the state. -/
theorem lc_continuation_feasible (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (θ : ι → ℝ)
    (c : ι × List ι → ℝ) (hIC : lc_IC β pl u θ c) (h : ι × List ι) (j : ι) :
    lc_IC β pl u θ c ∧
      lc_PK β pl u c (lc_ext h j) (lc_treeValue β pl (fun k => u (c k)) (lc_ext h j)) :=
  ⟨hIC, le_rfl⟩

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Bellman equation with the promised value as the state (Miao §22.1.1, pp. 776–778)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1.1, pp. 776–778. The principal's
value `P(θᵢ, v)` solves
`P(θᵢ, v) = max_{c, {wⱼ}} θᵢ − c + β Σⱼ π(θⱼ|θᵢ) P(θⱼ, wⱼ)` subject to the incentive
constraints (22.3) `wⱼ ≥ U_d(θⱼ)` and the promise-keeping constraint (22.4)
`u(c) + β Σⱼ π(θⱼ|θᵢ) wⱼ ≥ v`.

Proved here, for any solution `P` of the Bellman equation (`lc_Bellman`):
* the constraint set is convex and the Bellman operator maps concave `P` to concave `P`
  (`lc_feasible_convex`, `lc_bellman_concave`); `P` is decreasing in `v`;
* the promise-keeping constraint binds (`lc_promise_keeping_binds`);
* the first-order conditions (22.5)–(22.6) of the Lagrangian, the envelope condition (22.7),
  and (22.8)–(22.9). The envelope condition is derived by a perturbation argument (raise `v` and
  consumption together) instead of being assumed; the multipliers `λⱼ ≥ 0` with complementary
  slackness are constructed from one-sided perturbations of `wⱼ`;
* the two cases `λⱼ > 0` (the incentive constraint binds, `wⱼ = U_d(θⱼ)`, consumption rises and
  depends on `θⱼ` only: amnesia) and `λⱼ = 0` (consumption is unchanged);
* the optimal contract: next-period consumption is `max{h(θⱼ), c}` with `h(θⱼ)` the consumption
  at `(θⱼ, U_d(θⱼ))`, i.e. (22.11); consumption never falls and is eventually constant.

Correction. The book also states that for `λⱼ = 0`, (22.9) "implies that `wⱼ = v`", so that
`w = max{U_d(y), v}` and promised values never decrease. That is true when the endowments are
i.i.d. (`lc_iid_promised_value`), the case treated by Ljungqvist and Sargent, but false for a
general Markov chain: see `lc_promise_decrease_counterexample` in `LCInstances`.

Consumption is restricted to `c > 0`; the utility function enters through hypotheses
(strictly increasing on `(0, ∞)` with a continuous inverse `g`, derivative `du > 0`).
-/

namespace Miao.RecursiveContracts

open Filter Topology

variable {ι : Type*} [Fintype ι]

/-- Miao, (22.3)–(22.4), p. 776: `(c, w)` is feasible at `(θᵢ, v)`: `c > 0`, the incentive
constraints `wⱼ ≥ U_d(θⱼ)` and promise keeping `u(c) + β Σⱼ π(θⱼ|θᵢ) wⱼ ≥ v`. -/
def lc_feasible (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ) (i : ι) (v c : ℝ)
    (w : ι → ℝ) : Prop :=
  0 < c ∧ (∀ j, Ud j ≤ w j) ∧ v ≤ u c + β * ∑ j, pl i j * w j

/-- The Bellman objective `θᵢ − c + β Σⱼ π(θⱼ|θᵢ) P(θⱼ, wⱼ)` (Miao, p. 776). -/
def lc_obj (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (P : ι → ℝ → ℝ) (i : ι) (c : ℝ)
    (w : ι → ℝ) : ℝ :=
  θ i - c + β * ∑ j, pl i j * P j (w j)

/-- The set of attainable objective values at `(θᵢ, v)`. -/
def lc_valueSet (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) (i : ι) (v : ℝ) : Set ℝ :=
  {x | ∃ c w, lc_feasible β pl u Ud i v c w ∧ x = lc_obj β pl θ P i c w}

/-- Miao, p. 776: the Bellman equation holds at `(θᵢ, v)`: `P(θᵢ, v)` is the maximum. -/
def lc_BellmanAt (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) (i : ι) (v : ℝ) : Prop :=
  IsGreatest (lc_valueSet β pl θ u Ud P i v) (P i v)

/-- Miao, p. 776: `P` solves the Bellman equation at every state and promised value. -/
def lc_Bellman (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) : Prop :=
  ∀ i v, lc_BellmanAt β pl θ u Ud P i v

/-- `(c, w)` attains `P(θᵢ, v)`. -/
def lc_Optimal (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) (i : ι) (v c : ℝ) (w : ι → ℝ) : Prop :=
  lc_feasible β pl u Ud i v c w ∧ lc_obj β pl θ P i c w = P i v

/-- The upper bound part of the Bellman equation. -/
theorem lc_BellmanAt.lc_obj_le {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ} {Ud : ι → ℝ}
    {P : ι → ℝ → ℝ} {i : ι} {v : ℝ} (hB : lc_BellmanAt β pl θ u Ud P i v) {c : ℝ}
    {w : ι → ℝ} (hf : lc_feasible β pl u Ud i v c w) : lc_obj β pl θ P i c w ≤ P i v :=
  hB.2 ⟨c, w, hf, rfl⟩

/-- The Bellman maximum is attained. -/
theorem lc_BellmanAt.lc_exists_optimal {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ}
    {Ud : ι → ℝ} {P : ι → ℝ → ℝ} {i : ι} {v : ℝ} (hB : lc_BellmanAt β pl θ u Ud P i v) :
    ∃ c w, lc_Optimal β pl θ u Ud P i v c w := by
  obtain ⟨c, w, hf, he⟩ := hB.1
  exact ⟨c, w, hf, he.symm⟩

/-- Miao, p. 776: "the constraint set is convex": the set of `(v, c, w)` satisfying
(22.3)–(22.4) is convex when `u` is concave. -/
theorem lc_feasible_convex (β : ℝ) (pl : ι → ι → ℝ) {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ (Set.Ioi 0) u) (Ud : ι → ℝ) (i : ι) :
    Convex ℝ {p : ℝ × ℝ × (ι → ℝ) | lc_feasible β pl u Ud i p.1 p.2.1 p.2.2} := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨(convex_Ioi (0 : ℝ)) hp1 hq1 ha hb hab, fun j => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := add_le_add (mul_le_mul_of_nonneg_left (hp2 j) ha)
      (mul_le_mul_of_nonneg_left (hq2 j) hb)
    rw [← add_mul, hab, one_mul] at this
    exact this
  · have hc := hu.2 (Set.mem_Ioi.mpr hp1) (Set.mem_Ioi.mpr hq1) ha hb hab
    simp only [smul_eq_mul] at hc
    have hs : ∑ j, pl i j * (a * p.2.2 j + b * q.2.2 j) =
        a * ∑ j, pl i j * p.2.2 j + b * ∑ j, pl i j * q.2.2 j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hs]
    nlinarith [mul_le_mul_of_nonneg_left hp3 ha, mul_le_mul_of_nonneg_left hq3 hb]

/-- Miao, p. 776: "the value function `P` is concave in `v`": if the continuation values
`P(θⱼ, ·)` are concave and `u` is concave, the Bellman maximum `Q(v)` at `θᵢ` is concave in `v`
(the Bellman operator preserves concavity). -/
theorem lc_bellman_concave {β : ℝ} (hβ : 0 ≤ β) {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ (Set.Ioi 0) u) (Ud : ι → ℝ) (P : ι → ℝ → ℝ)
    (hP : ∀ j, ConcaveOn ℝ Set.univ (P j)) (i : ι) (hpl : ∀ j, 0 ≤ pl i j) (Q : ℝ → ℝ)
    (hQ : ∀ v, IsGreatest (lc_valueSet β pl θ u Ud P i v) (Q v)) :
    ConcaveOn ℝ Set.univ Q := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨c1, w1, hf1, he1⟩ := (hQ x).1
  obtain ⟨c2, w2, hf2, he2⟩ := (hQ y).1
  have hconv := lc_feasible_convex β pl hu Ud i (x := (x, c1, w1)) hf1 (y := (y, c2, w2)) hf2
    ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, Set.mem_ofPred_eq] at hconv
  have hle := (hQ (a • x + b • y)).2 ⟨_, _, hconv, rfl⟩
  refine le_trans ?_ hle
  rw [he1, he2]
  simp only [lc_obj, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  have hPj : ∀ j, a * P j (w1 j) + b * P j (w2 j) ≤ P j (a * w1 j + b * w2 j) := by
    intro j
    have := (hP j).2 (Set.mem_univ (w1 j)) (Set.mem_univ (w2 j)) ha hb hab
    simpa only [smul_eq_mul] using this
  have hs : a * ∑ j, pl i j * P j (w1 j) + b * ∑ j, pl i j * P j (w2 j) ≤
      ∑ j, pl i j * P j (a * w1 j + b * w2 j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have := mul_le_mul_of_nonneg_left (hPj j) (hpl j)
    linarith
  have hθ : θ i = a * θ i + b * θ i := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hs hβ]

/-- Miao, p. 776: `P(θᵢ, ·)` is decreasing in the promised value. -/
theorem lc_bellman_antitone {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ} {Ud : ι → ℝ}
    {P : ι → ℝ → ℝ} (hB : lc_Bellman β pl θ u Ud P) (i : ι) : Antitone (P i) := by
  intro v v' hvv'
  obtain ⟨c, w, hf, he⟩ := (hB i v').1
  rw [he]
  exact (hB i v).lc_obj_le ⟨hf.1, hf.2.1, hvv'.trans hf.2.2⟩

/-- Miao, p. 777: "the promise-keeping constraint always binds": at an optimum
`u(c) + β Σⱼ π(θⱼ|θᵢ) wⱼ = v` (lowering `c` would otherwise raise the principal's value). -/
theorem lc_promise_keeping_binds {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ}
    {Ud : ι → ℝ} {P : ι → ℝ → ℝ} {i : ι} {v c : ℝ} {w : ι → ℝ}
    (hB : lc_BellmanAt β pl θ u Ud P i v) (hopt : lc_Optimal β pl θ u Ud P i v c w)
    (hu : ContinuousAt u c) : u c + β * ∑ j, pl i j * w j = v := by
  obtain ⟨⟨hc, hw, hv⟩, he⟩ := hopt
  by_contra hne
  have hlt : v < u c + β * ∑ j, pl i j * w j := lt_of_le_of_ne hv (Ne.symm hne)
  set s := β * ∑ j, pl i j * w j
  obtain ⟨δ, hδ, hδu⟩ := Metric.continuousAt_iff.mp hu (u c + s - v) (by linarith)
  set y := c - min δ c / 2
  have hm : 0 < min δ c := lt_min hδ hc
  have hy : 0 < y := by have := min_le_right δ c; simp only [y]; linarith
  have hyd : dist y c < δ := by
    rw [Real.dist_eq, abs_lt]
    have := min_le_left δ c
    constructor <;> simp only [y] <;> linarith
  have huy := hδu hyd
  rw [Real.dist_eq, abs_lt] at huy
  have := hB.lc_obj_le (c := y) (w := w) ⟨hy, hw, by linarith [huy.1]⟩
  rw [← he] at this
  simp only [lc_obj, y] at this
  linarith

/-- The derivative of the inverse utility `g = u⁻¹` at `u(c)` is `1/u'(c)`. -/
theorem lc_inv_hasDerivAt {u g : ℝ → ℝ} (hg : Continuous g) (hug : ∀ a, u (g a) = a) {c du : ℝ}
    (hgu : g (u c) = c) (hu : HasDerivAt u du c) (hdu : du ≠ 0) :
    HasDerivAt g du⁻¹ (u c) := by
  refine HasDerivAt.of_local_left_inverse hg.continuousAt ?_ hdu (Eventually.of_forall hug)
  rw [hgu]
  exact hu

/-- Miao, (22.8), p. 777: the envelope condition `P_v(θᵢ, v) = −1/u'(c)`. Derived by raising the
promised value and current utility together: `v' ↦ P(θᵢ, v') + u⁻¹(u(c) + v' − v)` is minimised
at `v' = v`. -/
theorem eq_22_8 {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u g : ℝ → ℝ} {Ud : ι → ℝ}
    {P : ι → ℝ → ℝ} {i : ι} {v c : ℝ} {w : ι → ℝ}
    (hB : ∀ v', lc_BellmanAt β pl θ u Ud P i v') (hopt : lc_Optimal β pl θ u Ud P i v c w)
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a) (hgu : g (u c) = c)
    {du : ℝ} (hu : HasDerivAt u du c) (hdu : du ≠ 0) {p : ℝ} (hP : HasDerivAt (P i) p v) :
    p = -du⁻¹ := by
  obtain ⟨⟨hc, hw, hv⟩, he⟩ := hopt
  have hg' := lc_inv_hasDerivAt hg hug hgu hu hdu
  have hinner : HasDerivAt (fun v' => u c + (v' - v)) 1 v := by
    simpa using ((hasDerivAt_id v).sub_const v).const_add (u c)
  have hg2 : HasDerivAt g du⁻¹ (u c + (v - v)) := by rw [sub_self, add_zero]; exact hg'
  have hsum := hP.add (hg2.comp v hinner)
  have hmin : IsLocalMin (fun v' => P i v' + (g ∘ fun v' => u c + (v' - v)) v') v := by
    refine Eventually.of_forall fun v' => ?_
    have hfe : lc_feasible β pl u Ud i v' (g (u c + (v' - v))) w :=
      ⟨hgpos _, hw, by rw [hug]; linarith⟩
    have := (hB v').lc_obj_le hfe
    simp only [lc_obj] at this he
    simp only [Function.comp_apply, sub_self, add_zero, hgu]
    linarith
  have := hmin.hasDerivAt_eq_zero hsum
  linarith

/-- Miao, (22.7), p. 777: the envelope condition `P₂(θᵢ, v) = −μ`, where `μ = 1/u'(c) > 0` is the
multiplier of the promise-keeping constraint given by (22.5). -/
theorem eq_22_7 {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u g : ℝ → ℝ} {Ud : ι → ℝ}
    {P : ι → ℝ → ℝ} {i : ι} {v c : ℝ} {w : ι → ℝ}
    (hB : ∀ v', lc_BellmanAt β pl θ u Ud P i v') (hopt : lc_Optimal β pl θ u Ud P i v c w)
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a) (hgu : g (u c) = c)
    {du : ℝ} (hu : HasDerivAt u du c) (hdu : 0 < du) {p : ℝ} (hP : HasDerivAt (P i) p v) :
    let μ := du⁻¹
    0 < μ ∧ p = -μ :=
  ⟨inv_pos.mpr hdu, eq_22_8 hB hopt hg hgpos hug hgu hu hdu.ne' hP⟩

/-- The Lagrangian of the Bellman problem (Miao, p. 776):
`L = θᵢ − c + β Σⱼ πᵢⱼ P(θⱼ, wⱼ) + Σⱼ λⱼ (wⱼ − U_d(θⱼ)) + μ (u(c) + β Σⱼ πᵢⱼ wⱼ − v)`. -/
def lc_lagrangian (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) (i : ι) (v c : ℝ) (w lam : ι → ℝ) (μ : ℝ) : ℝ :=
  lc_obj β pl θ P i c w + ∑ j, lam j * (w j - Ud j) + μ * (u c + β * ∑ j, pl i j * w j - v)

/-- Miao, (22.5), p. 776: the first-order condition for `c`: `∂L/∂c = −1 + μ u'(c)`, which
vanishes iff `u'(c) = 1/μ`; then `μ > 0` because `u' > 0`. -/
theorem eq_22_5 (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) {u : ℝ → ℝ} (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) (i : ι) (v : ℝ) (w lam : ι → ℝ) (μ : ℝ) {c du : ℝ}
    (hu : HasDerivAt u du c) (hdu : 0 < du) :
    HasDerivAt (fun c' => lc_lagrangian β pl θ u Ud P i v c' w lam μ) (-1 + μ * du) c ∧
      (-1 + μ * du = 0 ↔ du = 1 / μ) ∧ (-1 + μ * du = 0 → 0 < μ) := by
  refine ⟨?_, ?_, fun h => ?_⟩
  · have h1 : HasDerivAt (fun c' => θ i - c') (-1) c := by
      simpa using (hasDerivAt_id c).const_sub (θ i)
    have h2 := ((hu.add_const (β * ∑ j, pl i j * w j)).sub_const v).const_mul μ
    have h3 := ((h1.add_const (β * ∑ j, pl i j * P j (w j))).add_const
      (∑ j, lam j * (w j - Ud j))).add h2
    convert h3 using 1
    funext c'
    simp only [lc_lagrangian, lc_obj, Pi.add_apply]
  · constructor
    · intro h
      have hμ : μ ≠ 0 := by rintro rfl; simp at h
      field_simp
      linarith
    · intro h
      have hμ : μ ≠ 0 := by rintro rfl; simp at h; linarith
      rw [h]; field_simp; ring
  · have : μ * du = 1 := by linarith
    by_contra hμ
    have : μ * du ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hμ) hdu.le
    linarith

/-- Replacing one coordinate of `w` changes a separable sum by the change in that term. -/
theorem lc_sum_update [DecidableEq ι] (F : ι → ℝ → ℝ) (w : ι → ℝ) (j : ι) (x : ℝ) :
    ∑ k, F k (Function.update w j x k) = ∑ k, F k (w k) + (F j x - F j (w j)) := by
  have : ∀ k, F k (Function.update w j x k) =
      F k (w k) + if k = j then F j x - F j (w j) else 0 := by
    intro k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- Miao, (22.6), p. 776: the first-order condition for `wⱼ`. The Lagrangian's partial
derivative in `wⱼ` is `β πᵢⱼ P₂(θⱼ, wⱼ) + λⱼ + μ β πᵢⱼ`; and at an optimum there is a multiplier
`λⱼ ≥ 0` with complementary slackness `λⱼ (wⱼ − U_d(θⱼ)) = 0` making it vanish, with
`μ = 1/u'(c)`. The multiplier is constructed by moving `wⱼ` and `c` together so that promise
keeping is unchanged (one-sided at a binding incentive constraint). -/
theorem eq_22_6 [DecidableEq ι] {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ}
    {u g : ℝ → ℝ} {Ud : ι → ℝ} {P : ι → ℝ → ℝ} {i : ι} {v c : ℝ} {w : ι → ℝ}
    (hB : lc_BellmanAt β pl θ u Ud P i v) (hopt : lc_Optimal β pl θ u Ud P i v c w)
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a) (hgu : g (u c) = c)
    {du : ℝ} (hu : HasDerivAt u du c) (hdu : 0 < du) (j : ι) (hpl : 0 ≤ pl i j) {q : ℝ}
    (hq : HasDerivAt (P j) q (w j)) (lam : ι → ℝ) (μ : ℝ) :
    HasDerivAt (fun x => lc_lagrangian β pl θ u Ud P i v c (Function.update w j x) lam μ)
        (β * pl i j * q + lam j + μ * β * pl i j) (w j) ∧
      ∃ lamj : ℝ, 0 ≤ lamj ∧ lamj * (w j - Ud j) = 0 ∧
        β * pl i j * q + lamj + du⁻¹ * β * pl i j = 0 := by
  constructor
  · have hL : (fun x => lc_lagrangian β pl θ u Ud P i v c (Function.update w j x) lam μ) =
        fun x => (lc_lagrangian β pl θ u Ud P i v c w lam μ - β * pl i j * P j (w j)
          - lam j * w j - μ * β * pl i j * w j) +
          (β * pl i j * P j x + lam j * x + μ * β * pl i j * x) := by
      funext x
      simp only [lc_lagrangian, lc_obj]
      rw [lc_sum_update (fun k y => pl i k * P k y), lc_sum_update (fun k y => lam k * (y - Ud k)),
        lc_sum_update (fun k y => pl i k * y)]
      ring
    rw [hL]
    have := ((hq.const_mul (β * pl i j)).add ((hasDerivAt_id (w j)).const_mul (lam j))).add
      ((hasDerivAt_id (w j)).const_mul (μ * β * pl i j))
    simp only [id, mul_one] at this
    exact this.const_add _
  obtain ⟨⟨hc, hw, hv⟩, he⟩ := hopt
  set D := β * pl i j * (du⁻¹ + q) with hD
  -- the perturbed objective
  set f : ℝ → ℝ := fun t => θ i - g (u c - β * pl i j * t) +
    β * (∑ k, pl i k * P k (w k) + (pl i j * P j (w j + t) - pl i j * P j (w j))) with hf
  have hfeas : ∀ t, Ud j - w j ≤ t → f t ≤ P i v := by
    intro t ht
    have hfe : lc_feasible β pl u Ud i v (g (u c - β * pl i j * t))
        (Function.update w j (w j + t)) := by
      refine ⟨hgpos _, fun k => ?_, ?_⟩
      · by_cases hk : k = j
        · subst hk; simp only [Function.update_self]; linarith
        · rw [Function.update_of_ne hk]; exact hw k
      · rw [hug, lc_sum_update (fun k y => pl i k * y)]
        nlinarith
    have := hB.lc_obj_le hfe
    simp only [lc_obj] at this
    rw [lc_sum_update (fun k y => pl i k * P k y)] at this
    exact this
  have hf0 : f 0 = P i v := by
    simp only [hf, mul_zero, sub_zero, add_zero, hgu, sub_self]
    simpa only [lc_obj] using he
  have hg' := lc_inv_hasDerivAt hg hug hgu hu hdu.ne'
  have hinner : HasDerivAt (fun t => u c - β * pl i j * t) (-(β * pl i j)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (β * pl i j)).const_sub (u c)
  have hg2 : HasDerivAt g du⁻¹ (u c - β * pl i j * 0) := by rw [mul_zero, sub_zero]; exact hg'
  have hPj : HasDerivAt (fun t => P j (w j + t)) q 0 := by
    have h1 : HasDerivAt (fun t => w j + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (w j)
    have h2 : HasDerivAt (P j) q (w j + 0) := by rw [add_zero]; exact hq
    convert h2.comp 0 h1 using 1
    · rfl
    · ring
  have hfd : HasDerivAt f D 0 := by
    have := ((hg2.comp 0 hinner).const_sub (θ i)).add
      ((((hPj.const_mul (pl i j)).sub_const (pl i j * P j (w j))).const_add
        (∑ k, pl i k * P k (w k))).const_mul β)
    convert this using 1
    · funext x
      simp only [hf, Pi.add_apply, Function.comp_apply]
    · rw [hD]
      ring
  have hDle : D ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hT := hfd.tendsto_slope_zero_right
    have hev := (hT.eventually (lt_mem_nhds hpos)).and self_mem_nhdsWithin
    obtain ⟨t, ht, ht0⟩ := hev.exists
    simp only [zero_add, smul_eq_mul] at ht ht0
    have := hfeas t (by linarith [hw j])
    have hpos' : 0 < f t - f 0 := by
      by_contra hn
      push Not at hn
      have : t⁻¹ * (f t - f 0) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0.le) hn
      linarith
    linarith
  refine ⟨-D, by linarith, ?_, by simp only [hD]; ring⟩
  rcases (hw j).lt_or_eq with hlt | heq
  · have hmax : IsLocalMax f 0 := by
      have : Set.Ioi (Ud j - w j) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by linarith)
      filter_upwards [this] with t ht
      rw [hf0]
      exact hfeas t (le_of_lt ht)
    have := hmax.hasDerivAt_eq_zero hfd
    rw [this]; ring
  · rw [heq]; ring

/-- Miao, (22.9), p. 777: combining (22.6) and (22.7),
`P_v(θⱼ, wⱼ) = P_v(θᵢ, v) − λⱼ / (β π(θⱼ|θᵢ))`. -/
theorem eq_22_9 {β πij q p lamj μ : ℝ} (hβ : 0 < β) (hπ : 0 < πij) (h7 : p = -μ)
    (h6 : β * πij * q + lamj + μ * β * πij = 0) : q = p - lamj / (β * πij) := by
  rw [h7]
  field_simp
  linarith

/-- Miao, p. 777, "States where `λᵢ > 0`": the incentive constraint binds, `wⱼ = U_d(θⱼ)`, and
next-period consumption is `h(θⱼ)`, the consumption at `(θⱼ, U_d(θⱼ))`, which depends on `θⱼ`
only (amnesia); it is strictly above current consumption. Here `cⱼ` is the consumption at
`(θⱼ, wⱼ)` given by the policy `σ`, and `P_v(θⱼ, wⱼ) ≥ −1/u'(cⱼ)`. -/
theorem lc_binding_case {β πij q lamj c : ℝ} {wj Udj : ℝ} {σ : ℝ → ℝ} {du : ℝ → ℝ}
    (hβ : 0 < β) (hπ : 0 < πij) (hc : 0 < c) (hcj : 0 < σ wj)
    (hdupos : ∀ x, 0 < x → 0 < du x) (hduanti : StrictAntiOn du (Set.Ioi 0))
    (hCS : lamj * (wj - Udj) = 0) (h6 : β * πij * q + lamj + (du c)⁻¹ * β * πij = 0)
    (henv : q = -(du (σ wj))⁻¹) (hlam : 0 < lamj) :
    wj = Udj ∧ σ wj = σ Udj ∧ c < σ wj := by
  have hw : wj = Udj := by
    rcases mul_eq_zero.mp hCS with h | h
    · linarith
    · linarith
  refine ⟨hw, by rw [hw], ?_⟩
  have h9 := eq_22_9 hβ hπ rfl h6
  rw [henv] at h9
  have hlt : (du c)⁻¹ < (du (σ wj))⁻¹ := by
    have : 0 < lamj / (β * πij) := div_pos hlam (mul_pos hβ hπ)
    linarith
  rw [inv_lt_inv₀ (hdupos c hc) (hdupos _ hcj)] at hlt
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with h | h
  · exact absurd (hduanti hcj hc h) (not_lt.mpr hlt.le)
  · rw [h] at hlt; exact lt_irrefl _ hlt

/-- Miao, p. 777, "States where `λᵢ = 0`": the incentive constraint does not bind and (22.9)
gives `P_v(θⱼ, wⱼ) = P_v(θᵢ, v)`, so by (22.8) next-period consumption equals current
consumption. -/
theorem lc_slack_case {β πij q c cj : ℝ} {du : ℝ → ℝ} (hc : 0 < c) (hcj : 0 < cj)
    (hduanti : StrictAntiOn du (Set.Ioi 0))
    (h6 : β * πij * q + 0 + (du c)⁻¹ * β * πij = 0) (hβπ : β * πij ≠ 0)
    (henv : q = -(du cj)⁻¹) : cj = c := by
  have : q = -(du c)⁻¹ := by
    have h : β * πij * (q + (du c)⁻¹) = 0 := by linarith
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hβπ
    · linarith
  rw [henv, neg_inj, inv_inj] at this
  exact hduanti.injOn hcj hc this

/-- Miao, p. 778, "The Optimal Contract", in the general Markov case. Let `σc, σw` be optimal
policies for a solution `P` of the Bellman equation, differentiable with `P_v(θⱼ, ·)` decreasing
(`P` concave). If `π(θⱼ|θᵢ) > 0`, next-period consumption after `θⱼ` is
`max{h(θⱼ), c}`, where `h(θⱼ) = σc(θⱼ, U_d(θⱼ))` is the consumption when the incentive
constraint binds; consumption never falls, and it rises only if the incentive constraint at
`θⱼ` binds (`wⱼ = U_d(θⱼ)`). -/
theorem lc_optimal_contract {β : ℝ} (hβ : 0 < β) {pl : ι → ι → ℝ} {θ : ι → ℝ}
    {u g : ℝ → ℝ} {Ud : ι → ℝ} {P : ι → ℝ → ℝ} (hB : lc_Bellman β pl θ u Ud P)
    (σc : ι → ℝ → ℝ) (σw : ι → ℝ → ι → ℝ)
    (hσ : ∀ k x, lc_Optimal β pl θ u Ud P k x (σc k x) (σw k x))
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a)
    (hgu : ∀ x, 0 < x → g (u x) = x) (du : ℝ → ℝ) (hdu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdupos : ∀ x, 0 < x → 0 < du x) (hduanti : StrictAntiOn du (Set.Ioi 0))
    (dP : ι → ℝ → ℝ) (hdP : ∀ k x, HasDerivAt (P k) (dP k x) x) (hconc : ∀ k, Antitone (dP k))
    (i : ι) (v : ℝ) (j : ι) (hπ : 0 < pl i j) :
    σc j (σw i v j) = max (σc j (Ud j)) (σc i v) ∧ σc i v ≤ σc j (σw i v j) ∧
      (σc i v < σc j (σw i v j) → σw i v j = Ud j) ∧
      (Ud j < σw i v j → σc j (σw i v j) = σc i v) := by
  classical
  have hc : 0 < σc i v := (hσ i v).1.1
  have hcj : 0 < σc j (σw i v j) := (hσ j _).1.1
  have hf1 : 0 < σc j (Ud j) := (hσ j _).1.1
  have henv : ∀ k x, dP k x = -(du (σc k x))⁻¹ := fun k x =>
    eq_22_8 (fun v' => hB k v') (hσ k x) hg hgpos hug (hgu _ (hσ k x).1.1)
      (hdu _ (hσ k x).1.1) (hdupos _ (hσ k x).1.1).ne' (hdP k x)
  obtain ⟨lamj, hl0, hCS, h6⟩ := (eq_22_6 (hB i v) (hσ i v) hg hgpos hug (hgu _ hc)
    (hdu _ hc) (hdupos _ hc) j hπ.le (hdP j (σw i v j)) (fun _ => 0) 0).2
  rw [henv j] at h6
  have hβπ : 0 < β * pl i j := mul_pos hβ hπ
  have hinv : (du (σc i v))⁻¹ ≤ (du (σc j (σw i v j)))⁻¹ := by
    have h9 := eq_22_9 hβ hπ rfl h6
    have := div_nonneg hl0 hβπ.le
    linarith
  rw [inv_le_inv₀ (hdupos _ hc) (hdupos _ hcj)] at hinv
  have hmono : σc i v ≤ σc j (σw i v j) := by
    by_contra h
    push Not at h
    exact absurd (hduanti hcj hc h) (not_lt.mpr hinv)
  have hslack : Ud j < σw i v j → σc j (σw i v j) = σc i v := by
    intro hlt
    have hl : lamj = 0 := by
      rcases mul_eq_zero.mp hCS with h | h
      · exact h
      · linarith
    rw [hl] at h6
    exact lc_slack_case hc hcj hduanti (q := -(du (σc j (σw i v j)))⁻¹) h6 hβπ.ne' rfl
  have hbind : σc i v < σc j (σw i v j) → σw i v j = Ud j := by
    intro hlt
    by_contra hne
    have := hslack (lt_of_le_of_ne ((hσ i v).1.2.1 j) (Ne.symm hne))
    linarith
  refine ⟨?_, hmono, hbind, hslack⟩
  rcases ((hσ i v).1.2.1 j).lt_or_eq with hlt | heq
  · have hcj' := hslack hlt
    have hd := hconc j hlt.le
    rw [henv, henv, neg_le_neg_iff, inv_le_inv₀ (hdupos _ hf1) (hdupos _ hcj)] at hd
    have : σc j (Ud j) ≤ σc j (σw i v j) := by
      by_contra h
      push Not at h
      exact absurd (hduanti hcj hf1 h) (not_lt.mpr hd)
    rw [hcj'] at this ⊢
    exact (max_eq_right this).symm
  · rw [← heq] at hmono ⊢
    exact (max_eq_left hmono).symm

/-- Miao, (22.11), p. 780: along any history of positive-probability transitions, optimal
consumption follows `c_t = max{c_{t-1}, h(y_t)}` with the minimum consumption function
`h(θⱼ) = σc(θⱼ, U_d(θⱼ))`, the consumption delivered when the incentive constraint binds. -/
theorem eq_22_11 {β : ℝ} (hβ : 0 < β) {pl : ι → ι → ℝ} {θ : ι → ℝ}
    {u g : ℝ → ℝ} {Ud : ι → ℝ} {P : ι → ℝ → ℝ} (hB : lc_Bellman β pl θ u Ud P)
    (σc : ι → ℝ → ℝ) (σw : ι → ℝ → ι → ℝ)
    (hσ : ∀ k x, lc_Optimal β pl θ u Ud P k x (σc k x) (σw k x))
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a)
    (hgu : ∀ x, 0 < x → g (u x) = x) (du : ℝ → ℝ) (hdu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdupos : ∀ x, 0 < x → 0 < du x) (hduanti : StrictAntiOn du (Set.Ioi 0))
    (dP : ι → ℝ → ℝ) (hdP : ∀ k x, HasDerivAt (P k) (dP k x) x) (hconc : ∀ k, Antitone (dP k))
    (y : ℕ → ι) (v : ℕ → ℝ) (hy : ∀ t, 0 < pl (y t) (y (t + 1)))
    (hv : ∀ t, v (t + 1) = σw (y t) (v t) (y (t + 1))) (t : ℕ) :
    σc (y (t + 1)) (v (t + 1)) = max (σc (y t) (v t)) (σc (y (t + 1)) (Ud (y (t + 1)))) := by
  rw [hv t, max_comm]
  exact (lc_optimal_contract hβ hB σc σw hσ hg hgpos hug hgu du hdu hdupos hduanti dP hdP hconc
    (y t) (v t) (y (t + 1)) (hy t)).1

omit [Fintype ι] in
/-- Miao, p. 778: "Consumption stays constant during periods when the incentive constraint does
not bind and increases during periods when it binds". With finitely many states a path
`c_{t+1} = max{c_t, h(y_{t+1})}` is nondecreasing and eventually constant. -/
theorem lc_consumption_eventually_constant [Finite ι] (h : ι → ℝ) (y : ℕ → ι) (c : ℕ → ℝ)
    (hc : ∀ t, c (t + 1) = max (c t) (h (y (t + 1)))) :
    Monotone c ∧ ∃ T, ∀ t, T ≤ t → c t = c T := by
  have hmono : Monotone c := monotone_nat_of_le_succ fun t => by rw [hc t]; exact le_max_left _ _
  refine ⟨hmono, ?_⟩
  have hmem : ∀ t, c t ∈ insert (c 0) (Set.range h) := by
    intro t
    induction t with
    | zero => exact Set.mem_insert _ _
    | succ t ih =>
      rw [hc t]
      rcases max_choice (c t) (h (y (t + 1))) with he | he
      · rw [he]; exact ih
      · rw [he]; exact Set.mem_insert_of_mem _ ⟨_, rfl⟩
  have hfin : (Set.range c).Finite :=
    ((Set.finite_range h).insert (c 0)).subset (Set.range_subset_iff.mpr hmem)
  obtain ⟨x, ⟨T, rfl⟩, hx⟩ := Set.exists_max_image (Set.range c) id hfin ⟨c 0, 0, rfl⟩
  exact ⟨T, fun t ht => le_antisymm (hx _ ⟨t, rfl⟩) (hmono ht)⟩

/-- Miao, p. 778 (i.i.d. case): when the transition probabilities do not depend on the current
state, `P(θᵢ, v) − θᵢ` does not depend on `i`. -/
theorem lc_iid_value_shift {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ} {Ud : ι → ℝ}
    {P : ι → ℝ → ℝ} (hB : lc_Bellman β pl θ u Ud P) (hiid : ∀ i i' k, pl i k = pl i' k)
    (i i' : ι) (v : ℝ) : P i v - θ i = P i' v - θ i' := by
  have key : ∀ i i', P i v ≤ P i' v + θ i - θ i' := by
    intro i i'
    obtain ⟨c, w, ⟨hc, hw, hv⟩, he⟩ := (hB i v).1
    have hf' : lc_feasible β pl u Ud i' v c w := by
      refine ⟨hc, hw, ?_⟩
      simp_rw [← hiid i i']
      exact hv
    have := (hB i' v).lc_obj_le hf'
    rw [he]
    simp only [lc_obj] at this ⊢
    simp_rw [hiid i i']
    linarith
  linarith [key i i', key i' i]

/-- Miao, p. 777–778, the claims "`λᵢ = 0` implies `wᵢ = v`" and `w = max{U_d(y), v}`, proved in
the i.i.d. case (Ljungqvist and Sargent's setting) for a strictly concave differentiable `P`:
the promised value after `θⱼ` is `max{U_d(θⱼ), v}`, so promised values never decrease. For a
general Markov chain this fails (`lc_promise_decrease_counterexample`). -/
theorem lc_iid_promised_value {β : ℝ} (hβ : 0 < β) {pl : ι → ι → ℝ} {θ : ι → ℝ}
    {u g : ℝ → ℝ} {Ud : ι → ℝ} {P : ι → ℝ → ℝ} (hB : lc_Bellman β pl θ u Ud P)
    (hiid : ∀ i i' k, pl i k = pl i' k)
    (σc : ι → ℝ → ℝ) (σw : ι → ℝ → ι → ℝ)
    (hσ : ∀ k x, lc_Optimal β pl θ u Ud P k x (σc k x) (σw k x))
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a)
    (hgu : ∀ x, 0 < x → g (u x) = x) (du : ℝ → ℝ) (hdu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdupos : ∀ x, 0 < x → 0 < du x)
    (dP : ι → ℝ → ℝ) (hdP : ∀ k x, HasDerivAt (P k) (dP k x) x)
    (hsconc : ∀ k, StrictAnti (dP k)) (i : ι) (v : ℝ) (j : ι) (hπ : 0 < pl i j) :
    σw i v j = max (Ud j) v ∧ v ≤ σw i v j := by
  classical
  have hc : 0 < σc i v := (hσ i v).1.1
  have hsame : ∀ x, dP j x = dP i x := by
    intro x
    have hfun : P j = fun x => P i x + (θ j - θ i) := by
      funext x
      linarith [lc_iid_value_shift hB hiid j i x]
    have := (hdP i x).add_const (θ j - θ i)
    rw [← hfun] at this
    exact (hdP j x).unique this
  have henv := eq_22_8 (fun v' => hB i v') (hσ i v) hg hgpos hug (hgu _ hc) (hdu _ hc)
    (hdupos _ hc).ne' (hdP i v)
  obtain ⟨lamj, hl0, hCS, h6⟩ := (eq_22_6 (hB i v) (hσ i v) hg hgpos hug (hgu _ hc)
    (hdu _ hc) (hdupos _ hc) j hπ.le (hdP j (σw i v j)) (fun _ => 0) 0).2
  have hβπ : 0 < β * pl i j := mul_pos hβ hπ
  have h9 := eq_22_9 hβ hπ henv h6
  rw [← hsame v] at h9
  have hle : dP j (σw i v j) ≤ dP j v := by
    have := div_nonneg hl0 hβπ.le
    linarith
  have hw := (hσ i v).1.2.1 j
  have hvw : v ≤ σw i v j := by
    by_contra h
    push Not at h
    exact absurd ((hsconc j) h) (not_lt.mpr hle)
  refine ⟨?_, hvw⟩
  rcases hw.lt_or_eq with hlt | heq
  · have hl : lamj = 0 := by
      rcases mul_eq_zero.mp hCS with h | h
      · exact h
      · linarith
    rw [hl, zero_div, sub_zero] at h9
    have := (hsconc j).injective h9
    rw [this, max_eq_right (this ▸ hlt).le]
  · rw [← heq] at hvw ⊢
    exact (max_eq_left hvw).symm

omit [Fintype ι] in
/-- Miao, p. 778, "Promised values never decrease" and full insurance in the i.i.d. case: if
`v_{t+1} = max{U_d(y_{t+1}), v_t}` then promised values are nondecreasing, and once the state
with the largest autarky value has been visited the promised value, hence consumption, stays
constant forever. -/
theorem lc_iid_full_insurance (Ud : ι → ℝ) (y : ℕ → ι) (v : ℕ → ℝ)
    (hv : ∀ t, v (t + 1) = max (Ud (y (t + 1))) (v t)) (T : ℕ)
    (hmax : ∀ k, Ud k ≤ Ud (y T)) (hT : Ud (y T) ≤ v T) :
    Monotone v ∧ ∀ t, T ≤ t → v t = v T := by
  refine ⟨monotone_nat_of_le_succ fun t => by rw [hv t]; exact le_max_right _ _, ?_⟩
  intro t ht
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← add_assoc, hv, ih (Nat.le_add_right T n)]
    exact max_eq_right ((hmax _).trans hT)

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Solutions of the Bellman equation with log utility, and the Markov counterexample

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1.1, pp. 776–778, with `u = log`
(which satisfies the Inada conditions; its inverse is `exp`).

* `lc_absorbing_bellman`: at an absorbing state with endowment `θⱼ` the Bellman equation of
  §22.1.1 is solved, for every promised value `v ∈ ℝ`, by the explicit function `lc_absorbP`:
  with `B = log θⱼ = (1 − β) U_d(θⱼ)`, `κ = β/(1 − β)` and `b = max{B, (1 − β)v}`,
  `P(v) = θⱼ/(1 − β) − exp(v − κb) − κ exp(b)`; for `v ≥ U_d(θⱼ)` this is
  `(θⱼ − exp((1 − β)v))/(1 − β)`, full insurance at the constant consumption `exp((1 − β)v)`.
* `lc_bellman_one_state`: the one-state economy, where `U_d` is the autarky value; this shows
  that the Bellman equation `lc_Bellman` has solutions.
* `lc_promise_decrease_counterexample`: a three-state Markov chain (state 0 moves to a high or a
  low absorbing state with probability 1/2 each, `β = 1/2`) in which the optimal contract at
  `(θ₀, v = 1)` gives the promised value `w₂ = 0 < v` after the low state, although the
  incentive constraint there is slack (`w₂ > U_d(θ₂) = −4`). This refutes the book's claims
  "`λᵢ = 0` implies `wᵢ = v`", `w = max{U_d(y), v}` and "promised values never decrease" for
  general Markov endowments (p. 777–778); they hold in the i.i.d. case (`lc_iid_promised_value`).
-/

namespace Miao.RecursiveContracts

open Real

/-- The value at an absorbing state with log utility (see the module docstring). -/
noncomputable def lc_absorbP (β θj B v : ℝ) : ℝ :=
  θj / (1 - β) - exp (v - β / (1 - β) * max B ((1 - β) * v)) -
    β / (1 - β) * exp (max B ((1 - β) * v))

/-- For `(1 − β)v ≥ B` the absorbing-state value is `(θⱼ − exp((1 − β)v))/(1 − β)`. -/
theorem lc_absorbP_of_le {β : ℝ} (hβ1 : β < 1) (θj B v : ℝ) (h : B ≤ (1 - β) * v) :
    lc_absorbP β θj B v = θj / (1 - β) - exp ((1 - β) * v) / (1 - β) := by
  have h1 : 0 < 1 - β := by linarith
  unfold lc_absorbP
  rw [max_eq_right h]
  have : v - β / (1 - β) * ((1 - β) * v) = (1 - β) * v := by field_simp
  rw [this]
  field_simp
  ring

/-- The supporting-line inequality `exp b ≥ exp a (1 + b − a)`. -/
theorem lc_exp_ge_tangent (a b : ℝ) : exp a * (1 + (b - a)) ≤ exp b := by
  have h := add_one_le_exp (b - a)
  have : exp b = exp a * exp (b - a) := by rw [← exp_add]; ring_nf
  rw [this]
  nlinarith [exp_pos a]

/-- Miao, p. 776, with `u = log` at an absorbing state: `lc_absorbP` solves the Bellman equation
at `θⱼ` for every promised value `v`. -/
theorem lc_absorbing_bellman {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (pl : ι → ι → ℝ) (θ : ι → ℝ) (Ud : ι → ℝ) (P : ι → ℝ → ℝ) (j : ι)
    (hpl : ∀ k, pl j k = if k = j then 1 else 0) (hUd : Ud j = log (θ j) / (1 - β))
    (hP : P j = lc_absorbP β (θ j) (log (θ j))) (v : ℝ) :
    lc_BellmanAt β pl θ log Ud P j v := by
  have h1 : 0 < 1 - β := by linarith
  have hsum : ∀ X : ι → ℝ, ∑ k, pl j k * X k = X j := by
    intro X
    simp_rw [hpl, ite_mul, one_mul, zero_mul]
    simp
  set B := log (θ j)
  set κ := β / (1 - β) with hκ
  set bs := max B ((1 - β) * v) with hbs
  set as := v - κ * bs with has
  have hκ0 : 0 ≤ κ := div_nonneg hβ0 h1.le
  have hκβ : ∀ x, β * (x / (1 - β)) = κ * x := by intro x; rw [hκ]; ring
  have hPw : ∀ w, Ud j ≤ w → P j w = θ j / (1 - β) - exp ((1 - β) * w) / (1 - β) := by
    intro w hw
    rw [hP]
    apply lc_absorbP_of_le hβ1
    rw [hUd, div_le_iff₀ h1] at hw
    linarith
  -- the key inequality
  have hkey : ∀ a b, B ≤ b → v ≤ a + κ * b → exp as + κ * exp bs ≤ exp a + κ * exp b := by
    intro a b hb hv
    have ha := lc_exp_ge_tangent as a
    have hb' : exp bs + exp as * (b - bs) ≤ exp b := by
      rcases le_total B ((1 - β) * v) with hle | hle
      · have hbs' : bs = (1 - β) * v := max_eq_right hle
        have : as = bs := by rw [has, hbs', hκ]; field_simp
        have := lc_exp_ge_tangent bs b
        rw [‹as = bs›]
        nlinarith
      · have hbs' : bs = B := max_eq_left hle
        have hasB : as ≤ B := by
          rw [has, hbs', hκ]
          have : v * (1 - β) ≤ B := by linarith
          have e : v - β / (1 - β) * B = (v * (1 - β) - β * B) / (1 - β) := by field_simp
          rw [e, div_le_iff₀ h1]
          nlinarith
        have := lc_exp_ge_tangent B b
        have hexp : exp as ≤ exp B := exp_le_exp.mpr hasB
        rw [hbs']
        nlinarith [mul_le_mul_of_nonneg_right hexp (by linarith : (0 : ℝ) ≤ b - B)]
    have hsumv : as + κ * bs = v := by rw [has]; ring
    nlinarith [mul_le_mul_of_nonneg_left hb' hκ0, exp_pos as]
  have hval : lc_absorbP β (θ j) B v = θ j / (1 - β) - exp as - κ * exp bs := rfl
  refine ⟨⟨exp as, fun k => if k = j then bs / (1 - β) else Ud k, ⟨exp_pos _, fun k => ?_, ?_⟩,
    ?_⟩, ?_⟩
  · by_cases hk : k = j
    · subst hk
      simp only [↓reduceIte]
      rw [hUd]
      exact div_le_div_of_nonneg_right (le_max_left _ _) h1.le
    · simp [hk]
  · rw [hsum]
    simp only [↓reduceIte, log_exp]
    rw [hκβ, has]
    linarith
  · simp only [lc_obj]
    rw [hsum]
    simp only [↓reduceIte]
    rw [hPw (bs / (1 - β)) (by rw [hUd]; exact div_le_div_of_nonneg_right (le_max_left _ _) h1.le),
      hP]
    rw [hval]
    have : (1 - β) * (bs / (1 - β)) = bs := by field_simp
    rw [this, hκ]
    field_simp
    ring
  · rintro x ⟨c, w, ⟨hc, hw, hv⟩, rfl⟩
    rw [hP, hval]
    simp only [lc_obj]
    rw [hsum] at hv ⊢
    rw [hPw _ (hw j)]
    have hb : B ≤ (1 - β) * w j := by
      have := hw j
      rw [hUd, div_le_iff₀ h1] at this
      linarith
    have hk := hkey (log c) ((1 - β) * w j) hb (by
      have : κ * ((1 - β) * w j) = β * w j := by rw [hκ]; field_simp
      rw [this]; exact hv)
    rw [exp_log hc] at hk
    have e : β * (θ j / (1 - β) - exp ((1 - β) * w j) / (1 - β)) =
        κ * θ j - κ * exp ((1 - β) * w j) := by rw [hκ]; field_simp
    have e2 : θ j / (1 - β) = θ j + κ * θ j := by rw [hκ]; field_simp; ring
    rw [e, e2]
    linarith

/-- Miao, pp. 775–776, the one-state economy with `u = log`: the autarky value is
`log θ₀/(1 − β)` and `lc_absorbP` solves the Bellman equation at every promised value. So
`lc_Bellman` has solutions (with `U_d` the true autarky value). -/
theorem lc_bellman_one_state {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (θ0 : ℝ) :
    let pl : Unit → Unit → ℝ := fun _ _ => 1
    let Ud : Unit → ℝ := fun _ => log θ0 / (1 - β)
    Ud = lc_autarky β pl (fun _ => log θ0) ∧
      lc_Bellman β pl (fun _ => θ0) log Ud (fun _ => lc_absorbP β θ0 (log θ0)) := by
  intro pl Ud
  have h1 : 0 < 1 - β := by linarith
  refine ⟨?_, fun i v => ?_⟩
  · apply lc_autarky_unique hβ0 hβ1 ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
    intro i
    simp only [Ud, Finset.univ_unique, Finset.sum_singleton, one_mul]
    field_simp
    ring
  · cases i
    exact lc_absorbing_bellman hβ0 hβ1 pl _ Ud _ () (fun k => by cases k; rfl) rfl rfl v

/-- Miao, pp. 777–778, counterexample to "`λᵢ = 0` implies `wᵢ = v`", to `w = max{U_d(y), v}`
and to "promised values never decrease" for Markov endowments. States `0, 1, 2`, `β = 1/2`,
`u = log`, endowments `1, e², e⁻²`; state 0 moves to 1 or 2 with probability 1/2 each and 1, 2 are
absorbing. Then `U_d = (0, 4, −4)` is the autarky value, `lc_absorbP` solves the Bellman equation
at states 1 and 2, and at `(θ₀, v = 1)` the contract `c = 1`, `w = (0, 4, 0)` is optimal: after
state 2 the incentive constraint is slack (`w₂ = 0 > −4`) but the promised value falls to
`w₂ = 0 < v = 1 = max{U_d(θ₂), v}`. -/
theorem lc_promise_decrease_counterexample :
    let β : ℝ := 1 / 2
    let pl : Fin 3 → Fin 3 → ℝ := ![![0, 1 / 2, 1 / 2], ![0, 1, 0], ![0, 0, 1]]
    let θ : Fin 3 → ℝ := ![1, exp 2, exp (-2)]
    let Ud : Fin 3 → ℝ := ![0, 4, -4]
    let P : Fin 3 → ℝ → ℝ :=
      ![fun _ => 0, lc_absorbP β (exp 2) 2, lc_absorbP β (exp (-2)) (-2)]
    let w : Fin 3 → ℝ := ![0, 4, 0]
    Ud = lc_autarky β pl (fun i => log (θ i)) ∧
      (∀ v, lc_BellmanAt β pl θ log Ud P 1 v) ∧ (∀ v, lc_BellmanAt β pl θ log Ud P 2 v) ∧
      lc_feasible β pl log Ud 0 1 1 w ∧
      IsGreatest (lc_valueSet β pl θ log Ud P 0 1) (lc_obj β pl θ P 0 1 w) ∧
      Ud 2 < w 2 ∧ w 2 < 1 ∧ w 2 ≠ max (Ud 2) 1 := by
  intro β pl θ Ud P w
  have hstoch : lc_IsStochastic pl := by
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [pl]
    · fin_cases i <;> simp [pl, Fin.sum_univ_three]
      norm_num
  have hβ0 : (0 : ℝ) ≤ β := by norm_num [β]
  have hβ1 : β < 1 := by norm_num [β]
  refine ⟨?_, fun v => ?_, fun v => ?_, ?_, ?_, ?_⟩
  · apply lc_autarky_unique hβ0 hβ1 hstoch
    intro i
    fin_cases i <;> simp [Ud, pl, θ, β, Fin.sum_univ_three] <;> norm_num
  · refine lc_absorbing_bellman hβ0 hβ1 pl θ Ud P 1 (fun k => ?_) ?_ ?_ v
    · fin_cases k <;> simp [pl]
    · simp [Ud, θ, β]; norm_num
    · simp [P, θ]
  · refine lc_absorbing_bellman hβ0 hβ1 pl θ Ud P 2 (fun k => ?_) ?_ ?_ v
    · fin_cases k <;> simp [pl]
    · simp [Ud, θ, β]; norm_num
    · simp [P, θ]
  · refine ⟨one_pos, fun k => ?_, ?_⟩
    · fin_cases k <;> simp [Ud, w]
    · simp [pl, w, β, Fin.sum_univ_three]; norm_num
  · have hP1 : ∀ x, 4 ≤ x → P 1 x = 2 * exp 2 - 2 * exp (x / 2) := by
      intro x hx
      simp only [P, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [lc_absorbP_of_le hβ1 _ _ _ (by norm_num [β]; linarith)]
      norm_num [β]
      ring_nf
    have hP2 : ∀ x, -4 ≤ x → P 2 x = 2 * exp (-2) - 2 * exp (x / 2) := by
      intro x hx
      simp only [P, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [lc_absorbP_of_le hβ1 _ _ _ (by norm_num [β]; linarith)]
      norm_num [β]
      ring_nf
    have hobj : ∀ c (w' : Fin 3 → ℝ), 4 ≤ w' 1 → -4 ≤ w' 2 →
        lc_obj β pl θ P 0 c w' = 1 - c + (exp 2 + exp (-2)) / 2 -
          (exp (w' 1 / 2) + exp (w' 2 / 2)) / 2 := by
      intro c w' h1 h2
      simp only [lc_obj, Fin.sum_univ_three]
      rw [hP1 _ h1, hP2 _ h2]
      simp [pl, θ, β]
      ring
    refine ⟨⟨1, w, ?_, rfl⟩, ?_⟩
    · refine ⟨one_pos, fun k => ?_, ?_⟩
      · fin_cases k <;> simp [Ud, w]
      · simp [pl, w, β, Fin.sum_univ_three]; norm_num
    · rintro x ⟨c, w', ⟨hc, hw, hv⟩, rfl⟩
      have h1 : 4 ≤ w' 1 := by simpa [Ud] using hw 1
      have h2 : -4 ≤ w' 2 := by simpa [Ud] using hw 2
      rw [hobj c w' h1 h2, hobj 1 w (by simp [w]) (by simp [w])]
      simp only [pl, β, Fin.sum_univ_three] at hv
      norm_num at hv
      have ha := lc_exp_ge_tangent 0 (log c)
      rw [exp_log hc, exp_zero] at ha
      have hb := lc_exp_ge_tangent 0 (w' 2 / 2)
      have hc2 := lc_exp_ge_tangent 2 (w' 1 / 2)
      have he2 : 1 ≤ exp 2 := one_le_exp (by norm_num)
      simp only [w, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      norm_num
      rw [exp_zero] at hb
      nlinarith [mul_le_mul_of_nonneg_right he2 (by linarith : (0 : ℝ) ≤ w' 1 / 2 - 2)]
  · simp [Ud, w]
    norm_num

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Discounted values of deterministic sequences

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1 and Exercise 22.1, pp. 775–798. In
the deterministic version of the limited-commitment model (Exercise 22.1, after Zhang 2012)
endowments and consumption are sequences, and the agent's continuation value at `t` is
`V_t(x) = Σ_{j ≥ 0} β^j x_{t+j}` (`lc_detValue`). This module collects the facts about these
discounted sums used in `LCLagrangian` and `LCZhang`: convergence for bounded sequences, bounds,
linearity, monotonicity, the split `V_t = Σ_{j<τ} β^j x_{t+j} + β^τ V_{t+τ}`, and the value of
a constant sequence.
-/

namespace Miao.RecursiveContracts

open Filter Topology

/-- The continuation value `V_t(x) = Σ_j β^j x_{t+j}` (Miao, p. 797). -/
noncomputable def lc_detValue (β : ℝ) (x : ℕ → ℝ) (t : ℕ) : ℝ := ∑' j : ℕ, β ^ j * x (t + j)

/-- Discounted bounded sequences are summable. -/
theorem lc_summable_geom {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) : Summable fun j : ℕ => β ^ j * x j := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
  exact mul_le_mul_of_nonneg_right (hx t) (pow_nonneg hβ0 t)

/-- The bound `|V_t(x)| ≤ M/(1 − β)`. -/
theorem lc_detValue_abs_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (t : ℕ) : |lc_detValue β x t| ≤ M / (1 - β) := by
  have hs := lc_summable_geom hβ0 hβ1 (x := fun j => x (t + j)) (fun j => hx (t + j))
  have hg := summable_geometric_of_lt_one hβ0 hβ1
  have hgeo : ∑' j : ℕ, M * β ^ j = M / (1 - β) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]
  rw [abs_le]
  constructor
  · have := Summable.tsum_le_tsum (f := fun j : ℕ => -(M * β ^ j))
      (g := fun j => β ^ j * x (t + j)) (fun j => by
        have := (abs_le.mp (hx (t + j))).1
        nlinarith [pow_nonneg hβ0 j]) (hg.mul_left M).neg hs
    rw [tsum_neg, hgeo] at this
    exact this
  · have := Summable.tsum_le_tsum (g := fun j : ℕ => M * β ^ j)
      (f := fun j => β ^ j * x (t + j)) (fun j => by
        have := (abs_le.mp (hx (t + j))).2
        nlinarith [pow_nonneg hβ0 j]) hs (hg.mul_left M)
    rw [hgeo] at this
    exact this

/-- The split `V_t = Σ_{j<τ} β^j x_{t+j} + β^τ V_{t+τ}`. -/
theorem lc_detValue_split {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (t τ : ℕ) :
    lc_detValue β x t = ∑ j ∈ Finset.range τ, β ^ j * x (t + j) +
      β ^ τ * lc_detValue β x (t + τ) := by
  have hs := lc_summable_geom hβ0 hβ1 (x := fun j => x (t + j)) (fun j => hx (t + j))
  unfold lc_detValue
  rw [← hs.sum_add_tsum_nat_add τ, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun i => ?_
  rw [pow_add, show t + (i + τ) = t + τ + i by ring]
  ring

/-- The recursion `V_t = x_t + β V_{t+1}`. -/
theorem lc_detValue_succ {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (t : ℕ) :
    lc_detValue β x t = x t + β * lc_detValue β x (t + 1) := by
  rw [lc_detValue_split hβ0 hβ1 hx t 1]
  simp

/-- `V_0(x) = Σ_{s<T} β^s x_s + β^T V_T(x)`. -/
theorem lc_detValue_split0 {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (T : ℕ) :
    lc_detValue β x 0 = ∑ s ∈ Finset.range T, β ^ s * x s + β ^ T * lc_detValue β x T := by
  rw [lc_detValue_split hβ0 hβ1 hx 0 T]
  simp

/-- Linearity: `V_t(a − b) = V_t(a) − V_t(b)`. -/
theorem lc_detValue_sub {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a b : ℕ → ℝ} {M : ℝ}
    (ha : ∀ t, |a t| ≤ M) (hb : ∀ t, |b t| ≤ M) (t : ℕ) :
    lc_detValue β (fun s => a s - b s) t = lc_detValue β a t - lc_detValue β b t := by
  unfold lc_detValue
  rw [← (lc_summable_geom hβ0 hβ1 (x := fun j => a (t + j)) (fun _ => ha _)).tsum_sub
    (lc_summable_geom hβ0 hβ1 (x := fun j => b (t + j)) (fun _ => hb _))]
  exact tsum_congr fun j => by ring

/-- Monotonicity: `a ≤ b` pointwise gives `V_t(a) ≤ V_t(b)`. -/
theorem lc_detValue_mono {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a b : ℕ → ℝ} {M : ℝ}
    (ha : ∀ t, |a t| ≤ M) (hb : ∀ t, |b t| ≤ M) (hab : ∀ t, a t ≤ b t) (t : ℕ) :
    lc_detValue β a t ≤ lc_detValue β b t :=
  Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hab _) (pow_nonneg hβ0 j))
    (lc_summable_geom hβ0 hβ1 (x := fun j => a (t + j)) (fun _ => ha _))
    (lc_summable_geom hβ0 hβ1 (x := fun j => b (t + j)) (fun _ => hb _))

/-- The value of a constant sequence: `V_t(k) = k/(1 − β)`. -/
theorem lc_detValue_const {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (k : ℝ) (t : ℕ) :
    lc_detValue β (fun _ => k) t = k / (1 - β) := by
  unfold lc_detValue
  rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1]
  ring

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Lagrangian method of Marcet and Marimon (Miao §22.1.2, pp. 778–780)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1.2, pp. 778–780, and the
first-best benchmark of p. 775. We work with deterministic endowments (the setting of
Exercise 22.1); the incentive constraint at `t` is `V_t(u(c)) ≥ U_t = V_t(u(y))`, with
multiplier `β^t α_t`, and the participation constraint is `V_0(u(c)) ≥ v₀` with multiplier `φ`.

Proved:
* (22.10): the cumulative multipliers `μ_t = μ_{t-1} + α_t`, `μ_{-1} = 0`, are the partial
  sums of `α` (`eq_22_10`);
* the rewriting of the Lagrangian: `Σ_t β^t α_t V_t(x) = Σ_s β^s μ_s x_s`, exactly for finite
  horizons with a remainder `μ_{T-1} β^T V_T(x)` (`lc_lagrangian_rewrite_finite`) and for the
  infinite horizon when the multipliers are nonnegative with bounded sums
  (`lc_lagrangian_rewrite`);
* the first-order condition `u'(c_t) = 1/(μ_t + φ)` and `−(μ_t + φ) = P_v(y_t, v_t)`
  (`lc_lagrangian_foc`, `lc_multiplier_value_derivative`);
* sufficiency: a feasible plan with nonnegative multipliers, complementary slackness and
  consumption maximising `−c + (μ_t + φ) u(c)` each period is optimal
  (`lc_lagrangian_sufficiency`): "the preceding three equations together with (22.10)
  characterize the solution";
* the first best (p. 775): without incentive constraints constant consumption with
  `u(c̄) = (1 − β) v₀` is optimal (`lc_first_best`).

Departure: the book states the Lagrangian with conditional expectations on the event tree; we
prove the rewriting and the sufficiency theorem for deterministic sequences, the case used in
Exercise 22.1.
-/

namespace Miao.RecursiveContracts

open Filter Topology

/-- Miao, (22.10), p. 779: `μ_t = α_0 + ⋯ + α_t`, the cumulative multiplier. -/
def lc_cumMult (α : ℕ → ℝ) (t : ℕ) : ℝ := ∑ s ∈ Finset.range (t + 1), α s

/-- Miao, (22.10), p. 779: `μ_t = μ_{t-1} + α_t` with `μ_{-1} = 0`. -/
theorem eq_22_10 (α : ℕ → ℝ) :
    lc_cumMult α 0 = 0 + α 0 ∧ ∀ t, lc_cumMult α (t + 1) = lc_cumMult α t + α (t + 1) := by
  refine ⟨by simp [lc_cumMult], fun t => ?_⟩
  unfold lc_cumMult
  rw [Finset.sum_range_succ]

/-- Swapping the order of summation in the triangle `t ≤ s < T`. -/
theorem lc_triangle_swap (α z : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, α t * ∑ s ∈ Finset.Ico t T, z s =
      ∑ s ∈ Finset.range T, z s * lc_cumMult α s := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h1 : ∀ t ∈ Finset.range (T + 1), α t * ∑ s ∈ Finset.Ico t (T + 1), z s =
        α t * ∑ s ∈ Finset.Ico t T, z s + α t * z T := by
      intro t ht
      rw [Finset.sum_Ico_succ_top (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)), mul_add]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib,
      Finset.sum_range_succ (fun t => α t * ∑ s ∈ Finset.Ico t T, z s),
      Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero, ih,
      Finset.sum_range_succ (fun s => z s * lc_cumMult α s), ← Finset.sum_mul]
    unfold lc_cumMult
    ring

/-- Miao, p. 779, the rewriting of the Lagrangian, finite-horizon form:
`Σ_{t<T} β^t α_t V_t(x) = Σ_{s<T} β^s μ_s x_s + μ_{T-1} β^T V_T(x)`. -/
theorem lc_lagrangian_rewrite_finite {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (α : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, β ^ t * α t * lc_detValue β x t =
      ∑ s ∈ Finset.range T, β ^ s * lc_cumMult α s * x s +
        (∑ t ∈ Finset.range T, α t) * (β ^ T * lc_detValue β x T) := by
  have hsplit : ∀ t ∈ Finset.range T, β ^ t * α t * lc_detValue β x t =
      α t * ∑ s ∈ Finset.Ico t T, β ^ s * x s + α t * (β ^ T * lc_detValue β x T) := by
    intro t ht
    have htT : t ≤ T := (Finset.mem_range.mp ht).le
    rw [lc_detValue_split hβ0 hβ1 hx t (T - t), Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel' htT]
    have hT : β ^ T = β ^ t * β ^ (T - t) := by rw [← pow_add, Nat.add_sub_cancel' htT]
    rw [hT, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_add]; ring
    · ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, lc_triangle_swap, ← Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Miao, p. 779, the rewriting of the Lagrangian:
`Σ_t β^t α_t E_t[Σ_{s ≥ t} β^{s-t} u(c_s)] = Σ_t β^t μ_t u(c_t)`, for nonnegative multipliers
with bounded cumulative sums and a bounded utility sequence `x`. -/
theorem lc_lagrangian_rewrite {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (α : ℕ → ℝ) (hα : ∀ t, 0 ≤ α t) {K : ℝ}
    (hK : ∀ t, lc_cumMult α t ≤ K) :
    ∑' t, β ^ t * α t * lc_detValue β x t = ∑' s, β ^ s * lc_cumMult α s * x s := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hx 0)
  have h1 : 0 < 1 - β := by linarith
  have hpart : ∀ T, ∑ t ∈ Finset.range T, α t ≤ K := by
    intro T
    cases T with
    | zero => simpa using (Finset.sum_nonneg fun t _ => hα t).trans (hK 0)
    | succ T => exact hK T
  have hK0 : 0 ≤ K := (Finset.sum_nonneg fun t _ => hα t).trans (hpart 0)
  have hμ : ∀ s, |lc_cumMult α s| ≤ K := fun s => by
    rw [abs_of_nonneg (show 0 ≤ lc_cumMult α s from Finset.sum_nonneg fun t _ => hα t)]
    exact hK s
  have hαs : Summable α := summable_of_sum_range_le hα hpart
  have hV := lc_detValue_abs_le hβ0 hβ1 hx
  have hL : Summable fun t => β ^ t * α t * lc_detValue β x t := by
    refine Summable.of_norm_bounded (hαs.mul_left (M / (1 - β))) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), abs_of_nonneg (hα t)]
    have := pow_le_one₀ hβ0 hβ1.le (n := t)
    calc β ^ t * α t * |lc_detValue β x t| ≤ 1 * α t * (M / (1 - β)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right this (hα t)) (hV t) (abs_nonneg _)
            (by rw [one_mul]; exact hα t)
      _ = M / (1 - β) * α t := by ring
  have hR : Summable fun s => β ^ s * lc_cumMult α s * x s := by
    have := lc_summable_geom hβ0 hβ1 (x := fun s => lc_cumMult α s * x s) (M := K * M)
      (fun s => by rw [abs_mul]; exact mul_le_mul (hμ s) (hx s) (abs_nonneg _) hK0)
    simpa only [mul_assoc] using this
  have hrem : Tendsto (fun T => (∑ t ∈ Finset.range T, α t) * (β ^ T * lc_detValue β x T))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun T => K * (M / (1 - β)) * β ^ T) (fun T => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ0 T),
        abs_of_nonneg (Finset.sum_nonneg fun t _ => hα t)]
      calc (∑ t ∈ Finset.range T, α t) * (β ^ T * |lc_detValue β x T|) ≤
            K * (β ^ T * (M / (1 - β))) := by
            gcongr
            · exact hpart T
            · exact hV T
        _ = K * (M / (1 - β)) * β ^ T := by ring
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul (K * (M / (1 - β)))
  have hlim := (hR.hasSum.tendsto_sum_nat).add hrem
  rw [add_zero] at hlim
  have hlim' := hL.hasSum.tendsto_sum_nat
  have heq : (fun T => ∑ t ∈ Finset.range T, β ^ t * α t * lc_detValue β x t) =
      fun T => ∑ s ∈ Finset.range T, β ^ s * lc_cumMult α s * x s +
        (∑ t ∈ Finset.range T, α t) * (β ^ T * lc_detValue β x T) := by
    funext T; exact lc_lagrangian_rewrite_finite hβ0 hβ1 hx α T
  rw [heq] at hlim'
  exact tendsto_nhds_unique hlim' hlim

/-- Miao, p. 779: the first-order condition for `c_t` in the rewritten Lagrangian: the
derivative of `(y_t − c) + (μ_t + φ) u(c)` is `−1 + (μ_t + φ) u'(c)`, which vanishes iff
`u'(c_t) = 1/(μ_t + φ)`. -/
theorem lc_lagrangian_foc {u : ℝ → ℝ} {c du : ℝ} (hu : HasDerivAt u du c) (y m : ℝ)
    (hm : m ≠ 0) :
    HasDerivAt (fun c' => y - c' + m * u c') (-1 + m * du) c ∧
      (-1 + m * du = 0 ↔ du = 1 / m) := by
  refine ⟨?_, ?_⟩
  · have := ((hasDerivAt_id c).const_sub y).add (hu.const_mul m)
    simp only [id] at this
    exact this
  · constructor
    · intro h; field_simp; linarith
    · intro h; rw [h]; field_simp; ring

/-- Miao, p. 779: "`−(μ_t + φ)` is equal to `P_v(y_t, v_t)`": combining the first-order condition
`u'(c_t) = 1/(μ_t + φ)` with the envelope condition (22.8) `P_v = −1/u'(c_t)`. -/
theorem lc_multiplier_value_derivative {du m pv : ℝ} (hm : m ≠ 0) (hfoc : du = 1 / m)
    (henv : pv = -1 / du) : pv = -m := by
  rw [henv, hfoc]
  field_simp

/-- The agent's autarky values `U_t = V_t(u(y))` (Exercise 22.1, p. 797). -/
noncomputable def lc_detU (β : ℝ) (u : ℝ → ℝ) (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  lc_detValue β (fun s => u (y s)) t

/-- The principal's value `Σ_t β^t (y_t − c_t)` (Miao, p. 775). -/
noncomputable def lc_detPrincipal (β : ℝ) (y c : ℕ → ℝ) : ℝ := ∑' t, β ^ t * (y t - c t)

/-- Feasible plans of the deterministic problem (Miao, (22.1)–(22.2), p. 775, and Exercise 22.1,
p. 797): positive bounded consumption with bounded utility, the incentive constraints
`V_t(u(c)) ≥ U_t` at every date and participation `V_0(u(c)) ≥ v₀`. -/
def lc_detFeasible (β : ℝ) (u : ℝ → ℝ) (y : ℕ → ℝ) (v₀ : ℝ) (c : ℕ → ℝ) : Prop :=
  (∀ t, 0 < c t) ∧ (∃ K, ∀ t, |c t| ≤ K ∧ |u (c t)| ≤ K) ∧
    (∀ t, lc_detU β u y t ≤ lc_detValue β (fun s => u (c s)) t) ∧
    v₀ ≤ lc_detValue β (fun s => u (c s)) 0

/-- Miao, p. 780, sufficiency of the Lagrangian conditions: let `c*` be feasible, `α_t ≥ 0`,
`φ ≥ 0` with complementary slackness, `μ_t` (22.10) bounded, and let `c*_t` maximise
`−c + (μ_t + φ) u(c)` over `c > 0` (the first-order condition for concave `u`). Then `c*`
maximises the principal's value among feasible plans. -/
theorem lc_lagrangian_sufficiency {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ}
    {y : ℕ → ℝ} (hy : ∃ K, ∀ t, |y t| ≤ K ∧ |u (y t)| ≤ K) {v₀ : ℝ} {cs : ℕ → ℝ}
    (hcs : lc_detFeasible β u y v₀ cs) (α : ℕ → ℝ) (hα : ∀ t, 0 ≤ α t) {φ : ℝ} (hφ : 0 ≤ φ)
    (hCS : ∀ t, α t * (lc_detValue β (fun s => u (cs s)) t - lc_detU β u y t) = 0)
    (hCSφ : φ * (lc_detValue β (fun s => u (cs s)) 0 - v₀) = 0) {Kμ : ℝ}
    (hKμ : ∀ t, lc_cumMult α t ≤ Kμ)
    (hmax : ∀ t, ∀ x, 0 < x → -x + (lc_cumMult α t + φ) * u x ≤
      -cs t + (lc_cumMult α t + φ) * u (cs t))
    {c : ℕ → ℝ} (hc : lc_detFeasible β u y v₀ c) :
    lc_detPrincipal β y c ≤ lc_detPrincipal β y cs := by
  obtain ⟨Ky, hKy⟩ := hy
  obtain ⟨hcs0, ⟨K1, hK1⟩, hcsIC, _⟩ := hcs
  obtain ⟨hc0, ⟨K2, hK2⟩, hcIC, hcPK⟩ := hc
  set K := K1 + K2 + Ky with hKdef
  have hK10 : 0 ≤ K1 := (abs_nonneg _).trans (hK1 0).1
  have hK20 : 0 ≤ K2 := (abs_nonneg _).trans (hK2 0).1
  have hKy0 : 0 ≤ Ky := (abs_nonneg _).trans (hKy 0).1
  have huc : ∀ t, |u (c t)| ≤ K := fun t => by linarith [(hK2 t).2]
  have hucs : ∀ t, |u (cs t)| ≤ K := fun t => by linarith [(hK1 t).2]
  set d : ℕ → ℝ := fun s => u (c s) - u (cs s) with hd
  set e : ℕ → ℝ := fun s => cs s - c s with he
  have hdK : ∀ s, |d s| ≤ 2 * K := fun s => (abs_sub _ _).trans (by linarith [huc s, hucs s])
  have heK : ∀ s, |e s| ≤ 2 * K := fun s =>
    (abs_sub _ _).trans (by linarith [(hK1 s).1, (hK2 s).1])
  have hVd : ∀ t, lc_detValue β d t =
      lc_detValue β (fun s => u (c s)) t - lc_detValue β (fun s => u (cs s)) t :=
    lc_detValue_sub hβ0 hβ1 huc hucs
  have hPdiff : lc_detPrincipal β y c - lc_detPrincipal β y cs = lc_detValue β e 0 := by
    unfold lc_detPrincipal lc_detValue
    have hyc : ∀ t, |y t - c t| ≤ Ky + K2 := fun t =>
      (abs_sub _ _).trans (add_le_add (hKy t).1 (hK2 t).1)
    have hycs : ∀ t, |y t - cs t| ≤ Ky + K1 := fun t =>
      (abs_sub _ _).trans (add_le_add (hKy t).1 (hK1 t).1)
    rw [← (lc_summable_geom hβ0 hβ1 hyc).tsum_sub (lc_summable_geom hβ0 hβ1 hycs)]
    refine tsum_congr fun t => ?_
    simp only [he, zero_add]
    ring
  have hμ0 : ∀ t, 0 ≤ lc_cumMult α t := fun t => Finset.sum_nonneg fun s _ => hα s
  have hKμ0 : 0 ≤ Kμ := (hμ0 0).trans (hKμ 0)
  have hpart : ∀ T, ∑ t ∈ Finset.range T, α t ≤ Kμ := by
    intro T
    cases T with
    | zero => simpa using hKμ0
    | succ T => exact hKμ T
  -- the bound for every horizon
  set R : ℕ → ℝ := fun T => β ^ T * lc_detValue β e T +
    ((∑ t ∈ Finset.range T, α t) + φ) * (β ^ T * lc_detValue β d T) with hR
  have hbound : ∀ T, lc_detValue β e 0 ≤ R T := by
    intro T
    have hIC : 0 ≤ ∑ t ∈ Finset.range T, β ^ t * α t * lc_detValue β d t := by
      refine Finset.sum_nonneg fun t _ => ?_
      have h1 := hCS t
      have h2 : α t * (lc_detValue β (fun s => u (c s)) t - lc_detU β u y t) ≥ 0 :=
        mul_nonneg (hα t) (by linarith [hcIC t])
      rw [hVd t]
      have : α t * (lc_detValue β (fun s => u (c s)) t -
          lc_detValue β (fun s => u (cs s)) t) ≥ 0 := by nlinarith
      have := mul_nonneg (pow_nonneg hβ0 t) this
      linarith
    have hPK : 0 ≤ φ * lc_detValue β d 0 := by
      rw [hVd 0]
      nlinarith
    rw [lc_lagrangian_rewrite_finite hβ0 hβ1 hdK α T] at hIC
    rw [lc_detValue_split0 hβ0 hβ1 hdK T] at hPK
    rw [lc_detValue_split0 hβ0 hβ1 heK T]
    have hpt : ∑ s ∈ Finset.range T, β ^ s * e s +
        (∑ s ∈ Finset.range T, β ^ s * lc_cumMult α s * d s +
          φ * ∑ s ∈ Finset.range T, β ^ s * d s) ≤ 0 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_nonpos fun s _ => ?_
      have := hmax s (c s) (hc0 s)
      have h : e s + (lc_cumMult α s + φ) * d s ≤ 0 := by simp only [he, hd]; linarith
      have := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ0 s) h
      linarith
    simp only [hR]
    nlinarith
  have hRlim : Tendsto R atTop (𝓝 0) := by
    have hVe := lc_detValue_abs_le hβ0 hβ1 heK
    have hVd' := lc_detValue_abs_le hβ0 hβ1 hdK
    refine squeeze_zero_norm (a := fun T => (2 * K / (1 - β) + (Kμ + φ) * (2 * K / (1 - β))) *
      β ^ T) (fun T => ?_) ?_
    · have hs0 : 0 ≤ ∑ t ∈ Finset.range T, α t := Finset.sum_nonneg fun t _ => hα t
      rw [Real.norm_eq_abs]
      simp only [hR]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ0 T),
        abs_of_nonneg (add_nonneg hs0 hφ)]
      have hb1 : β ^ T * |lc_detValue β e T| ≤ β ^ T * (2 * K / (1 - β)) :=
        mul_le_mul_of_nonneg_left (hVe T) (pow_nonneg hβ0 T)
      have hb2 : ((∑ t ∈ Finset.range T, α t) + φ) * (β ^ T * |lc_detValue β d T|) ≤
          (Kμ + φ) * (β ^ T * (2 * K / (1 - β))) := by
        gcongr
        · exact hpart T
        · exact hVd' T
      nlinarith
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul
        (2 * K / (1 - β) + (Kμ + φ) * (2 * K / (1 - β)))
  have := ge_of_tendsto' hRlim hbound
  linarith

/-- Miao, p. 775, the first best: without incentive constraints, constant consumption `c̄` with
`u(c̄) = (1 − β) v₀` minimises the cost `Σ β^t c_t` among bounded positive plans with
`V_0(u(c)) ≥ v₀`, for concave `u` with derivative `du(c̄) > 0` (supporting line). The
risk-neutral principal fully insures the agent. -/
theorem lc_first_best {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ} {cbar du v₀ : ℝ}
    (hdu : 0 < du) (hsupp : ∀ x, 0 < x → u x ≤ u cbar + du * (x - cbar))
    (hcbar : u cbar = (1 - β) * v₀) {c : ℕ → ℝ} (hc0 : ∀ t, 0 < c t) {K : ℝ}
    (hK : ∀ t, |c t| ≤ K ∧ |u (c t)| ≤ K) (hPK : v₀ ≤ lc_detValue β (fun s => u (c s)) 0) :
    ∑' t, β ^ t * cbar ≤ ∑' t, β ^ t * c t := by
  have h1 : 0 < 1 - β := by linarith
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0).1
  have hc' : ∀ t, |c t - cbar| ≤ K + |cbar| := fun t =>
    (abs_sub _ _).trans (add_le_add (hK t).1 le_rfl)
  have hu' : ∀ t, |u (c t) - u cbar| ≤ K + |u cbar| := fun t =>
    (abs_sub _ _).trans (add_le_add (hK t).2 le_rfl)
  have hineq : ∀ t, (u (c t) - u cbar) / du ≤ c t - cbar := by
    intro t
    rw [div_le_iff₀ hdu]
    linarith [hsupp (c t) (hc0 t)]
  have hsum := Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left (hineq t)
    (pow_nonneg hβ0 t)) ((lc_summable_geom hβ0 hβ1 hu').div_const du |>.congr fun t => by ring)
    (lc_summable_geom hβ0 hβ1 hc')
  have hb1 : ∀ t, |u (c t)| ≤ K + |u cbar| := fun t => by linarith [(hK t).2, abs_nonneg (u cbar)]
  have hb2 : ∀ _t : ℕ, |u cbar| ≤ K + |u cbar| := fun _ => by linarith
  have hV : ∑' t, β ^ t * ((u (c t) - u cbar) / du) =
      (lc_detValue β (fun s => u (c s)) 0 - v₀) / du := by
    have := lc_detValue_sub hβ0 hβ1 hb1 (b := fun _ => u cbar) hb2 0
    have hconst : lc_detValue β (fun _ => u cbar) 0 = v₀ := by
      rw [lc_detValue_const hβ0 hβ1, hcbar]; field_simp
    rw [hconst] at this
    rw [← this, lc_detValue, ← tsum_div_const]
    refine tsum_congr fun t => ?_
    rw [zero_add]
    ring
  have hdiff : ∑' t, β ^ t * c t - ∑' t, β ^ t * cbar = ∑' t, β ^ t * (c t - cbar) := by
    rw [← (lc_summable_geom hβ0 hβ1 (fun t => (hK t).1)).tsum_sub
      (lc_summable_geom hβ0 hβ1 (x := fun _ => cbar) (fun _ => le_rfl))]
    exact tsum_congr fun t => by ring
  have hnn : 0 ≤ (lc_detValue β (fun s => u (c s)) 0 - v₀) / du := div_nonneg (by linarith) hdu.le
  linarith

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Zhang's minimum consumption function, deterministic case (Miao §22.1.3, pp. 780–781)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1.3, pp. 780–781, and Exercise 22.1,
p. 797, for a deterministic bounded utility-of-endowment sequence `x_t = u(y_t)`. With
`B_τ = Σ_{j<τ} β^j`, `S_t(τ) = Σ_{j<τ} β^j x_{t+j}` and the average `A_t(τ) = S_t(τ)/B_τ`, the
minimum consumption level at `t` in utility units is `m_t = inf_{τ ≥ 1} A_t(τ)` (`lc_m`), so
that `h(y_t) = u⁻¹(m_t)`. `lc_run m k j = max_{k ≤ s ≤ k+j} m_s` is the running maximum.

Main result (`lc_zhang_identity`): for every `k`,
`Σ_j β^j max_{k ≤ s ≤ k+j} m_s = U_k = Σ_j β^j x_{k+j}`.
This is the identity behind Zhang's characterisation (22.11): the consumption path
`c_t = max{c_{t-1}, h(y_t)}`, `c_0 = h(y_0)`, delivers at least the autarky value at every date
and exactly the autarky value at every date at which consumption is reset to `h(y_t)`.

The proof decomposes time into blocks between successive strict increases of `m`: on a finite
block `[t, t+T)` the average of `x` equals `m_t` (`lc_block_eq`), and on an infinite final block
`(1 − β)U_t = m_t` (`lc_tail_eq`).
-/

namespace Miao.RecursiveContracts

open Filter Topology

/-- `B_τ = Σ_{j<τ} β^j`. -/
def lc_B (β : ℝ) (τ : ℕ) : ℝ := ∑ j ∈ Finset.range τ, β ^ j

/-- `S_t(τ) = Σ_{j<τ} β^j x_{t+j}`. -/
def lc_S (β : ℝ) (x : ℕ → ℝ) (t τ : ℕ) : ℝ := ∑ j ∈ Finset.range τ, β ^ j * x (t + j)

/-- The discounted average `A_t(τ) = S_t(τ)/B_τ` (Miao, Exercise 22.1(c), p. 798). -/
noncomputable def lc_A (β : ℝ) (x : ℕ → ℝ) (t τ : ℕ) : ℝ := lc_S β x t τ / lc_B β τ

/-- The minimum consumption level in utility units, `m_t = inf_{τ ≥ 1} A_t(τ)`
(Miao, p. 781 and Exercise 22.1(c), p. 798). -/
noncomputable def lc_m (β : ℝ) (x : ℕ → ℝ) (t : ℕ) : ℝ := ⨅ τ : ℕ, lc_A β x t (τ + 1)

/-- The running maximum `max_{k ≤ s ≤ k+j} m_s`. -/
def lc_run (m : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => m k
  | j + 1 => max (lc_run m k j) (m (k + j + 1))

theorem lc_B_add (β : ℝ) (τ σ : ℕ) : lc_B β (τ + σ) = lc_B β τ + β ^ τ * lc_B β σ := by
  unfold lc_B
  rw [Finset.sum_range_add, Finset.mul_sum]
  simp_rw [pow_add]

theorem lc_S_add (β : ℝ) (x : ℕ → ℝ) (t τ σ : ℕ) :
    lc_S β x t (τ + σ) = lc_S β x t τ + β ^ τ * lc_S β x (t + τ) σ := by
  unfold lc_S
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, add_assoc]
  ring

theorem lc_B_mul (β : ℝ) (τ : ℕ) : lc_B β τ * (1 - β) = 1 - β ^ τ := by
  unfold lc_B
  have := geom_sum_mul β τ
  linarith [show (∑ i ∈ Finset.range τ, β ^ i) * (1 - β) =
    -((∑ i ∈ Finset.range τ, β ^ i) * (β - 1)) by ring]

theorem lc_B_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (τ : ℕ) : 0 ≤ lc_B β τ :=
  Finset.sum_nonneg fun j _ => pow_nonneg hβ0 j

theorem lc_B_ge_one {β : ℝ} (hβ0 : 0 ≤ β) {τ : ℕ} (hτ : 1 ≤ τ) : 1 ≤ lc_B β τ := by
  have := Finset.single_le_sum (f := fun j => β ^ j) (fun j _ => pow_nonneg hβ0 j)
    (Finset.mem_range.mpr (by omega : 0 < τ))
  simpa [lc_B] using this

theorem lc_B_mul_le {β : ℝ} (hβ0 : 0 ≤ β) (τ : ℕ) : lc_B β τ * (1 - β) ≤ 1 := by
  rw [lc_B_mul]; linarith [pow_nonneg hβ0 τ]

theorem lc_S_abs_le {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t τ : ℕ) : |lc_S β x t τ| ≤ M * lc_B β τ := by
  unfold lc_S lc_B
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 j), mul_comm]
  exact mul_le_mul_of_nonneg_right (hx _) (pow_nonneg hβ0 j)

theorem lc_A_abs_le {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t : ℕ) {τ : ℕ} (hτ : 1 ≤ τ) : |lc_A β x t τ| ≤ M := by
  have hB := lc_B_ge_one hβ0 hτ
  unfold lc_A
  rw [abs_div, abs_of_pos (show 0 < lc_B β τ by linarith),
    div_le_iff₀ (show 0 < lc_B β τ by linarith)]
  exact lc_S_abs_le hβ0 hx t τ

theorem lc_A_bddBelow {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t : ℕ) : BddBelow (Set.range fun τ : ℕ => lc_A β x t (τ + 1)) :=
  ⟨-M, by rintro _ ⟨τ, rfl⟩; exact (abs_le.mp (lc_A_abs_le hβ0 hx t (by omega))).1⟩

theorem lc_m_le_A {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t : ℕ) {τ : ℕ} (hτ : 1 ≤ τ) : lc_m β x t ≤ lc_A β x t τ := by
  obtain ⟨σ, rfl⟩ : ∃ σ, τ = σ + 1 := ⟨τ - 1, by omega⟩
  exact ciInf_le (lc_A_bddBelow hβ0 hx t) σ

theorem lc_m_abs_le {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t : ℕ) : |lc_m β x t| ≤ M := by
  rw [abs_le]
  constructor
  · exact le_ciInf fun τ => (abs_le.mp (lc_A_abs_le hβ0 hx t (by omega))).1
  · exact (lc_m_le_A hβ0 hx t le_rfl).trans (abs_le.mp (lc_A_abs_le hβ0 hx t le_rfl)).2

/-- `m_t ≤ x_t` (take `τ = 1`). -/
theorem lc_m_le_x {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t : ℕ) : lc_m β x t ≤ x t := by
  have := lc_m_le_A hβ0 hx t le_rfl
  simpa [lc_A, lc_S, lc_B] using this

theorem lc_S_ge_m {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t τ : ℕ) : lc_m β x t * lc_B β τ ≤ lc_S β x t τ := by
  rcases Nat.eq_zero_or_pos τ with rfl | hτ
  · simp [lc_B, lc_S]
  · have h := lc_m_le_A hβ0 hx t hτ
    have hB := lc_B_ge_one hβ0 hτ
    unfold lc_A at h
    rwa [le_div_iff₀ (by linarith)] at h

/-- The averages converge to `(1 − β) U_t`. -/
theorem lc_A_tendsto {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (t : ℕ) :
    Tendsto (fun τ => lc_A β x t τ) atTop (𝓝 ((1 - β) * lc_detValue β x t)) := by
  have hS : Tendsto (fun τ => lc_S β x t τ) atTop (𝓝 (lc_detValue β x t)) :=
    (lc_summable_geom hβ0 hβ1 (x := fun j => x (t + j)) (fun j => hx _)).hasSum.tendsto_sum_nat
  have hB : Tendsto (fun τ => lc_B β τ) atTop (𝓝 (1 - β)⁻¹) :=
    (hasSum_geometric_of_lt_one hβ0 hβ1).tendsto_sum_nat
  have h1 : (1 - β)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have := hS.div hB h1
  rw [div_inv_eq_mul, mul_comm] at this
  exact this

/-- If `m_t ≤ m̄` and the averages from some horizon `T` on are at least `m̄ + δ`, then some
average before `T` is at most `m̄`. -/
theorem lc_exists_low {β : ℝ} {x : ℕ → ℝ} (T : ℕ) : ∀ t mb δ, lc_m β x t ≤ mb → 0 < δ →
      (∀ τ, 1 ≤ τ → T ≤ τ → mb + δ ≤ lc_A β x t τ) →
      ∃ τ0, 1 ≤ τ0 ∧ τ0 < T ∧ lc_A β x t τ0 ≤ mb := by
  have hall : ∀ t mb δ, lc_m β x t ≤ mb → 0 < δ →
      (∀ τ, 1 ≤ τ → mb + δ ≤ lc_A β x t τ) → False := by
    intro t mb δ hm hδ h
    have : mb + δ ≤ lc_m β x t := le_ciInf fun τ => h (τ + 1) (by omega)
    linarith
  induction T with
  | zero =>
    intro t mb δ hm hδ h
    exact (hall t mb δ hm hδ fun τ h1 => h τ h1 (Nat.zero_le τ)).elim
  | succ T ih =>
    intro t mb δ hm hδ h
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · exact (hall t mb δ hm hδ fun τ h1 => h τ h1 h1).elim
    by_cases hA : lc_A β x t T ≤ mb
    · exact ⟨T, hT, by omega, hA⟩
    push Not at hA
    obtain ⟨τ0, h1, h2, h3⟩ := ih t mb (min δ (lc_A β x t T - mb)) hm
      (lt_min hδ (by linarith)) (fun τ hτ1 hτT => by
        rcases hτT.lt_or_eq with h' | h'
        · exact (add_le_add_right (min_le_left _ _) _).trans (h τ hτ1 h')
        · rw [← h']; linarith [min_le_right δ (lc_A β x t T - mb)])
    exact ⟨τ0, h1, by omega, h3⟩

/-- On a block `[t, t+T)` on which `m ≤ m̄`, ending with `m_{t+T} > m̄`, the discounted sum of
`x` is at most `m̄ B_T`. -/
theorem lc_block_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (T : ℕ) : 1 ≤ T → ∀ t mb, lc_m β x t ≤ mb →
      (∀ s, 1 ≤ s → s < T → lc_m β x (t + s) ≤ mb) → mb < lc_m β x (t + T) →
      lc_S β x t T ≤ mb * lc_B β T := by
  induction T using Nat.strong_induction_on with
  | _ T ih =>
  intro hT t mb hm hs hTm
  by_contra hgt
  push Not at hgt
  set ε := lc_S β x t T - mb * lc_B β T with hε
  have hε0 : 0 < ε := by linarith
  have h1β : 0 < 1 - β := by linarith
  have hbig : ∀ τ, 1 ≤ τ → T ≤ τ → mb + ε * (1 - β) ≤ lc_A β x t τ := by
    intro τ hτ1 hτT
    obtain ⟨σ, rfl⟩ : ∃ σ, τ = T + σ := ⟨τ - T, by omega⟩
    have hBpos : 0 < lc_B β (T + σ) := by linarith [lc_B_ge_one hβ0 hτ1]
    unfold lc_A
    rw [le_div_iff₀ hBpos, lc_S_add, lc_B_add]
    have h2 := lc_S_ge_m hβ0 hx (t + T) σ
    have h3 : mb * lc_B β σ ≤ lc_m β x (t + T) * lc_B β σ :=
      mul_le_mul_of_nonneg_right hTm.le (lc_B_nonneg hβ0 σ)
    have h4 : β ^ T * (mb * lc_B β σ) ≤ β ^ T * lc_S β x (t + T) σ :=
      mul_le_mul_of_nonneg_left (h3.trans h2) (pow_nonneg hβ0 T)
    have h5 := lc_B_mul_le hβ0 (T + σ)
    rw [lc_B_add] at h5
    nlinarith
  obtain ⟨τ0, h1, h2, h3⟩ := lc_exists_low T t mb (ε * (1 - β)) hm
    (mul_pos hε0 h1β) hbig
  have hlow : lc_S β x t τ0 ≤ mb * lc_B β τ0 := by
    unfold lc_A at h3
    rwa [div_le_iff₀ (by linarith [lc_B_ge_one hβ0 h1])] at h3
  have hIH := ih (T - τ0) (by omega) (by omega) (t + τ0) mb (hs τ0 h1 h2)
    (fun s hs1 hs2 => by rw [add_assoc]; exact hs (τ0 + s) (by omega) (by omega))
    (by rw [show t + τ0 + (T - τ0) = t + T by omega]; exact hTm)
  have hsplitS := lc_S_add β x t τ0 (T - τ0)
  have hsplitB := lc_B_add β τ0 (T - τ0)
  rw [show τ0 + (T - τ0) = T by omega] at hsplitS hsplitB
  have := mul_le_mul_of_nonneg_left hIH (pow_nonneg hβ0 τ0)
  have e : mb * lc_B β T = mb * lc_B β τ0 + β ^ τ0 * (mb * lc_B β (T - τ0)) := by
    rw [hsplitB]; ring
  linarith

/-- On a finite block between strict increases of `m` the average of `x` equals `m_t`. -/
theorem lc_block_eq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (T : ℕ) (hT : 1 ≤ T) (t : ℕ)
    (hs : ∀ s, 1 ≤ s → s < T → lc_m β x (t + s) ≤ lc_m β x t)
    (hTm : lc_m β x t < lc_m β x (t + T)) :
    lc_S β x t T = lc_m β x t * lc_B β T :=
  le_antisymm (lc_block_le hβ0 hβ1 hx T hT t _ le_rfl hs hTm) (lc_S_ge_m hβ0 hx t T)

/-- If `m ≤ m̄` from `t` on, then `(1 − β) U_t − m̄ ≤ (M + |m̄|) β^k` for every `k`. -/
theorem lc_tail_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (mb : ℝ) (k : ℕ) : ∀ t, (∀ s, lc_m β x (t + s) ≤ mb) →
      (1 - β) * lc_detValue β x t - mb ≤ (M + |mb|) * β ^ k := by
  have h1β : 0 < 1 - β := by linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans (hx 0)
  induction k with
  | zero =>
    intro t _
    have hU := abs_le.mp (lc_detValue_abs_le hβ0 hβ1 hx t)
    have : (1 - β) * lc_detValue β x t ≤ M := by
      have := mul_le_mul_of_nonneg_left hU.2 h1β.le
      rwa [mul_div_cancel₀ _ h1β.ne'] at this
    simp only [pow_zero, mul_one]
    linarith [neg_abs_le mb]
  | succ k ih =>
    intro t hs
    set η := (1 - β) * lc_detValue β x t - mb
    have hC : 0 ≤ (M + |mb|) * β ^ (k + 1) :=
      mul_nonneg (add_nonneg hM (abs_nonneg _)) (pow_nonneg hβ0 _)
    by_cases hη : η ≤ 0
    · linarith
    push Not at hη
    have hev := (lc_A_tendsto hβ0 hβ1 hx t).eventually
      (Ioi_mem_nhds (show mb + η / 2 < (1 - β) * lc_detValue β x t by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    obtain ⟨τ0, h1, -, h3⟩ := lc_exists_low N t mb (η / 2)
      (by simpa using hs 0) (by linarith) (fun τ _ hτ => (hN τ hτ).le)
    have hlow : lc_S β x t τ0 ≤ mb * lc_B β τ0 := by
      unfold lc_A at h3
      rwa [div_le_iff₀ (by linarith [lc_B_ge_one hβ0 h1])] at h3
    have hIH := ih (t + τ0) (fun s => by rw [add_assoc]; exact hs (τ0 + s))
    have hsplit := lc_detValue_split hβ0 hβ1 hx t τ0
    have hB := lc_B_mul β τ0
    have hpow : β ^ τ0 ≤ β := pow_le_of_le_one hβ0 hβ1.le (by omega)
    have hCk : 0 ≤ (M + |mb|) * β ^ k :=
      mul_nonneg (add_nonneg hM (abs_nonneg _)) (pow_nonneg hβ0 _)
    have key : η ≤ β ^ τ0 * ((1 - β) * lc_detValue β x (t + τ0) - mb) := by
      simp only [η]
      rw [hsplit]
      change (1 - β) * (lc_S β x t τ0 + β ^ τ0 * lc_detValue β x (t + τ0)) - mb ≤ _
      have e2 : (1 - β) * (mb * lc_B β τ0) = mb * (1 - β ^ τ0) := by rw [← hB]; ring
      have := mul_le_mul_of_nonneg_left hlow h1β.le
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left hIH (pow_nonneg hβ0 τ0)
    have h3 := mul_le_mul_of_nonneg_right hpow hCk
    rw [pow_succ]
    nlinarith

/-- On an infinite final block (`m_{t+s} ≤ m_t` for all `s`), `(1 − β) U_t = m_t`. -/
theorem lc_tail_eq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (t : ℕ) (hs : ∀ s, lc_m β x (t + s) ≤ lc_m β x t) :
    (1 - β) * lc_detValue β x t = lc_m β x t := by
  apply le_antisymm
  · have hlim : Tendsto (fun k : ℕ => (M + |lc_m β x t|) * β ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul (M + |lc_m β x t|)
    have := ge_of_tendsto' hlim fun k => lc_tail_le hβ0 hβ1 hx (lc_m β x t) k t hs
    linarith
  · exact ge_of_tendsto (lc_A_tendsto hβ0 hβ1 hx t)
      (eventually_atTop.mpr ⟨1, fun τ hτ => lc_m_le_A hβ0 hx t hτ⟩)

theorem lc_run_succ (m : ℕ → ℝ) (k j : ℕ) :
    lc_run m k (j + 1) = max (lc_run m k j) (m (k + j + 1)) := rfl

theorem lc_run_ge (m : ℕ → ℝ) (k j : ℕ) : m (k + j) ≤ lc_run m k j ∧ m k ≤ lc_run m k j := by
  induction j with
  | zero => simp [lc_run]
  | succ j ih =>
    rw [lc_run_succ]
    exact ⟨le_max_of_le_right le_rfl, le_max_of_le_left ih.2⟩

theorem lc_run_mono (m : ℕ → ℝ) (k : ℕ) : Monotone (lc_run m k) :=
  monotone_nat_of_le_succ fun j => by rw [lc_run_succ]; exact le_max_left _ _

theorem lc_run_add (m : ℕ → ℝ) (k i j : ℕ) :
    lc_run m k (i + j) = max (lc_run m k i) (lc_run m (k + i) j) := by
  induction j with
  | zero =>
    simp only [add_zero, lc_run]
    exact (max_eq_left (by simpa using (lc_run_ge m k i).1)).symm
  | succ j ih =>
    rw [← add_assoc, lc_run_succ, ih, lc_run_succ, max_assoc]
    congr 3
    ring

theorem lc_run_eq_first (m : ℕ → ℝ) (k j : ℕ) (h : ∀ s, 1 ≤ s → s ≤ j → m (k + s) ≤ m k) :
    lc_run m k j = m k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [lc_run_succ, ih (fun s h1 h2 => h s h1 (by omega))]
    exact max_eq_left (h (j + 1) (by omega) le_rfl)

theorem lc_run_abs_le (m : ℕ → ℝ) {M : ℝ} (hm : ∀ t, |m t| ≤ M) (k j : ℕ) :
    |lc_run m k j| ≤ M := by
  induction j with
  | zero => exact hm k
  | succ j ih =>
    rw [lc_run_succ]
    rcases max_choice (lc_run m k j) (m (k + j + 1)) with h | h <;> rw [h]
    · exact ih
    · exact hm _

/-- **Zhang's identity** (Miao, §22.1.3, pp. 780–781, and Exercise 22.1(c), p. 798, deterministic
case): for every date `k`, `Σ_j β^j max_{k ≤ s ≤ k+j} m_s = Σ_j β^j x_{k+j} = U_k`. -/
theorem lc_zhang_identity {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (k : ℕ) :
    lc_detValue β (lc_run (lc_m β x) k) 0 = lc_detValue β x k := by
  classical
  set m := lc_m β x
  have hm : ∀ t, |m t| ≤ M := lc_m_abs_le hβ0 hx
  have hrun := lc_run_abs_le m hm
  have h1β : 0 < 1 - β := by linarith
  set C := 2 * (M / (1 - β))
  have hbound : ∀ n k, |lc_detValue β x k - lc_detValue β (lc_run m k) 0| ≤ C * β ^ n := by
    intro n
    induction n with
    | zero =>
      intro k
      simp only [pow_zero, mul_one, C]
      refine (abs_sub _ _).trans ?_
      linarith [lc_detValue_abs_le hβ0 hβ1 hx k, lc_detValue_abs_le hβ0 hβ1 (hrun k) 0]
    | succ n ih =>
      intro k
      have hC : 0 ≤ C * β ^ (n + 1) := by
        have : 0 ≤ M := (abs_nonneg _).trans (hx 0)
        exact mul_nonneg (by positivity) (pow_nonneg hβ0 _)
      by_cases hex : ∃ s, 1 ≤ s ∧ m k < m (k + s)
      · set T := Nat.find hex
        have hT : 1 ≤ T ∧ m k < m (k + T) := Nat.find_spec hex
        have hbefore : ∀ s, 1 ≤ s → s < T → m (k + s) ≤ m k := by
          intro s h1 h2
          have := Nat.find_min hex h2
          push Not at this
          exact this h1
        have hS := lc_block_eq hβ0 hβ1 hx T hT.1 k hbefore hT.2
        have hrunT : ∀ j, lc_run m k (T + j) = lc_run m (k + T) j := by
          intro j
          rw [lc_run_add]
          have : lc_run m k T = m (k + T) := by
            obtain ⟨T', hT'⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
            have h2 : m k < m (k + (T' + 1)) := hT' ▸ hT.2
            rw [hT', lc_run_succ, lc_run_eq_first m k T' (fun s h1 h2 => hbefore s h1 (by omega)),
              show k + T' + 1 = k + (T' + 1) by ring]
            exact max_eq_right h2.le
          rw [this]
          exact max_eq_right (by simpa using (lc_run_ge m (k + T) j).2)
        have hW : lc_detValue β (lc_run m k) 0 =
            m k * lc_B β T + β ^ T * lc_detValue β (lc_run m (k + T)) 0 := by
          rw [lc_detValue_split hβ0 hβ1 (hrun k) 0 T]
          congr 1
          · unfold lc_B
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [zero_add, lc_run_eq_first m k j (fun s h1 h2 =>
              hbefore s h1 (by have := Finset.mem_range.mp hj; omega))]
            ring
          · congr 1
            unfold lc_detValue
            refine tsum_congr fun j => ?_
            rw [zero_add, zero_add, hrunT]
        have hU := lc_detValue_split hβ0 hβ1 hx k T
        change lc_detValue β x k = lc_S β x k T + _ at hU
        rw [hS] at hU
        rw [hU, hW]
        have hpow : β ^ T ≤ β := pow_le_of_le_one hβ0 hβ1.le (by omega)
        have := ih (k + T)
        rw [show m k * lc_B β T + β ^ T * lc_detValue β x (k + T) -
            (m k * lc_B β T + β ^ T * lc_detValue β (lc_run m (k + T)) 0) =
            β ^ T * (lc_detValue β x (k + T) - lc_detValue β (lc_run m (k + T)) 0) by ring,
          abs_mul, abs_of_nonneg (pow_nonneg hβ0 T)]
        have hCn : 0 ≤ C * β ^ n := by
          have : 0 ≤ M := (abs_nonneg _).trans (hx 0)
          exact mul_nonneg (by positivity) (pow_nonneg hβ0 _)
        calc β ^ T * |lc_detValue β x (k + T) - lc_detValue β (lc_run m (k + T)) 0|
            ≤ β ^ T * (C * β ^ n) := mul_le_mul_of_nonneg_left this (pow_nonneg hβ0 T)
          _ ≤ β * (C * β ^ n) := mul_le_mul_of_nonneg_right hpow hCn
          _ = C * β ^ (n + 1) := by ring
      · push Not at hex
        have hconst : ∀ j, lc_run m k j = m k := fun j =>
          lc_run_eq_first m k j fun s h1 _ => hex s h1
        have hW : lc_detValue β (lc_run m k) 0 = m k / (1 - β) := by
          rw [← lc_detValue_const hβ0 hβ1 (m k) 0]
          unfold lc_detValue
          exact tsum_congr fun j => by rw [hconst]
        have hU : (1 - β) * lc_detValue β x k = m k := lc_tail_eq hβ0 hβ1 hx k (fun s => by
          rcases Nat.eq_zero_or_pos s with rfl | hs
          · simp
          · exact hex s hs)
        rw [hW, ← hU, mul_div_cancel_left₀ _ h1β.ne', sub_self, abs_zero]
        exact hC
  have hlim : Tendsto (fun n : ℕ => C * β ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul C
  have h0 := ge_of_tendsto' hlim fun n => hbound n k
  have := abs_nonneg (lc_detValue β x k - lc_detValue β (lc_run m k) 0)
  have he : |lc_detValue β x k - lc_detValue β (lc_run m k) 0| = 0 := le_antisymm h0 this
  rw [abs_eq_zero, sub_eq_zero] at he
  exact he.symm

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 22.1 and the alternative characterisation (Miao §22.1.3, pp. 780–781, 797–798)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1.3 and Exercise 22.1 (Zhang 2012),
deterministic endowments `y_t > 0` with bounded `y` and `u(y)`. Utility `u` is strictly
increasing on `(0, ∞)` with inverse `g : ℝ → (0, ∞)`, and concave with a positive, decreasing
derivative `du` (supporting-line form `u(z) ≤ u(c) + du(c)(z − c)`).

* `lc_optimal_of_marginal`: a feasible nondecreasing bounded plan whose incentive constraint
  binds at date 0 and at every date at which consumption changes is optimal (Lagrangian
  sufficiency with `μ_t = 1/u'(c_t)`).
* `ex_22_1a`: decreasing endowments: constant consumption with `u(c) = (1 − β) U_d(y₀)`.
* `ex_22_1b`: increasing endowments: autarky.
* `ex_22_1c`: in general `c_t = max{c_{t-1}, h(y_t)}`, `c₀ = h(y₀)`, with
  `h = u⁻¹(inf_{τ ≥ 1} Σ_{t<τ} β^t u(y_t) / Σ_{t<τ} β^t)` is optimal.
* `lc_d_tau`, `lc_h_isGLB`: the book's `d_i(τ)` and `h = inf_τ d(τ)` (p. 780–781).
* `lc_c0_strictMono`, `lc_c0_gt_h`: the initial consumption solving the binding participation
  constraint is unique, equals `h(y₀)` when `v₀ = U_d(y₀)`, and exceeds it when `v₀ > U_d(y₀)`.

Corrections. In Exercise 22.1(c) the minimum over `τ` need not exist: for `u(y) = (1, 0, 0, …)`
the averages strictly decrease (`lc_ex_22_1c_min_not_attained`), so `min` must be read as `inf`
(as in the main text, p. 781). And `h` depends on the date (the whole future endowment path),
not on `y_t = θᵢ` alone: `lc_h_depends_on_future` gives two dates with the same endowment and
different `h`.
-/

namespace Miao.RecursiveContracts

open Filter Topology

/-- The increments of a sequence, `α₀ = μ₀`, `α_{t+1} = μ_{t+1} − μ_t`. -/
def lc_incr (μ : ℕ → ℝ) : ℕ → ℝ
  | 0 => μ 0
  | t + 1 => μ (t + 1) - μ t

/-- (22.10) inverted: the cumulative sums of the increments are `μ`. -/
theorem lc_cumMult_incr (μ : ℕ → ℝ) (t : ℕ) : lc_cumMult (lc_incr μ) t = μ t := by
  induction t with
  | zero => simp [lc_cumMult, lc_incr]
  | succ t ih =>
    rw [(eq_22_10 _).2, ih]
    simp [lc_incr]

/-- The inverse of a strictly increasing utility is strictly increasing. -/
theorem lc_g_strictMono {u g : ℝ → ℝ} (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a)
    (humono : StrictMonoOn u (Set.Ioi 0)) : StrictMono g := by
  intro a b hab
  by_contra h
  push Not at h
  have := humono.monotoneOn (hgpos b) (hgpos a) h
  rw [hug, hug] at this
  linarith

/-- `V_t(x) = V_0(x_{t+·})`. -/
theorem lc_detValue_shift (β : ℝ) (x : ℕ → ℝ) (t : ℕ) :
    lc_detValue β x t = lc_detValue β (fun j => x (t + j)) 0 := by
  simp [lc_detValue]

/-- Miao, p. 780 (sufficiency in the form used by Zhang): a feasible, nondecreasing, bounded
plan whose incentive constraint binds at date 0 and at every date at which consumption changes
is optimal; the multipliers are `μ_t = 1/u'(c_t)`. -/
theorem lc_optimal_of_marginal {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ} {y : ℕ → ℝ}
    (hyb : ∃ K, ∀ t, |y t| ≤ K ∧ |u (y t)| ≤ K) (du : ℝ → ℝ)
    (hdupos : ∀ c, 0 < c → 0 < du c) (hduanti : AntitoneOn du (Set.Ioi 0))
    (hsupp : ∀ c, 0 < c → ∀ z, 0 < z → u z ≤ u c + du c * (z - c)) {cs : ℕ → ℝ}
    (hcs : lc_detFeasible β u y (lc_detU β u y 0) cs) (hmono : Monotone cs)
    (hbind0 : lc_detValue β (fun s => u (cs s)) 0 = lc_detU β u y 0)
    (hbind : ∀ t, cs (t + 1) ≠ cs t →
      lc_detValue β (fun s => u (cs s)) (t + 1) = lc_detU β u y (t + 1))
    {c : ℕ → ℝ} (hc : lc_detFeasible β u y (lc_detU β u y 0) c) :
    lc_detPrincipal β y c ≤ lc_detPrincipal β y cs := by
  have hpos := hcs.1
  obtain ⟨K, hK⟩ := hcs.2.1
  set μ : ℕ → ℝ := fun t => (du (cs t))⁻¹ with hμ
  have hμmono : ∀ t, μ t ≤ μ (t + 1) := by
    intro t
    have h := hduanti (hpos t) (hpos (t + 1)) (hmono (Nat.le_succ t))
    exact inv_anti₀ (hdupos _ (hpos _)) h
  have hα : ∀ t, 0 ≤ lc_incr μ t := by
    intro t
    cases t with
    | zero => exact (inv_pos.mpr (hdupos _ (hpos 0))).le
    | succ t => simp only [lc_incr]; linarith [hμmono t]
  have hKpos : 0 < K := lt_of_lt_of_le (hpos 0) ((le_abs_self _).trans (hK 0).1)
  refine lc_lagrangian_sufficiency hβ0 hβ1 hyb hcs (lc_incr μ) hα le_rfl (fun t => ?_)
    (by simp) (Kμ := (du K)⁻¹) (fun t => ?_) (fun t z hz => ?_) hc
  · cases t with
    | zero => rw [hbind0, sub_self, mul_zero]
    | succ t =>
      by_cases h : cs (t + 1) = cs t
      · simp only [lc_incr, hμ, h, sub_self, zero_mul]
      · rw [hbind t h, sub_self, mul_zero]
  · rw [lc_cumMult_incr]
    have hle : cs t ≤ K := (le_abs_self _).trans (hK t).1
    exact inv_anti₀ (hdupos K hKpos) (hduanti (hpos t) hKpos hle)
  · rw [lc_cumMult_incr, add_zero]
    have h := hsupp (cs t) (hpos t) z hz
    have hd := hdupos _ (hpos t)
    have : μ t * u z ≤ μ t * u (cs t) + (z - cs t) := by
      have := mul_le_mul_of_nonneg_left h (inv_pos.mpr hd).le
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul] at this
      exact this
    linarith

/-- **Exercise 22.1(a)** (Miao, p. 797). If endowments decrease (`y₀ ≥ y₁ ≥ ⋯`), the optimal
contract has constant consumption with `u(c_t) = (1 − β) U_d(y₀)`. -/
theorem ex_22_1a {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u g : ℝ → ℝ} {y : ℕ → ℝ}
    (hy0 : ∀ t, 0 < y t) (hyb : ∃ K, ∀ t, |y t| ≤ K ∧ |u (y t)| ≤ K) (hyd : Antitone y)
    (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a) (humono : StrictMonoOn u (Set.Ioi 0))
    (du : ℝ → ℝ) (hdupos : ∀ c, 0 < c → 0 < du c) (hduanti : AntitoneOn du (Set.Ioi 0))
    (hsupp : ∀ c, 0 < c → ∀ z, 0 < z → u z ≤ u c + du c * (z - c)) :
    let cbar := g ((1 - β) * lc_detU β u y 0)
    u cbar = (1 - β) * lc_detU β u y 0 ∧
      lc_detFeasible β u y (lc_detU β u y 0) (fun _ => cbar) ∧
      ∀ c, lc_detFeasible β u y (lc_detU β u y 0) c →
        lc_detPrincipal β y c ≤ lc_detPrincipal β y (fun _ => cbar) := by
  intro cbar
  have h1 : 0 < 1 - β := by linarith
  obtain ⟨K, hK⟩ := hyb
  have hx : ∀ t, |u (y t)| ≤ K := fun t => (hK t).2
  have hU : ∀ t, lc_detU β u y t ≤ lc_detU β u y 0 := by
    have hstep : ∀ t, lc_detU β u y (t + 1) ≤ lc_detU β u y t := by
      intro t
      unfold lc_detU lc_detValue
      refine Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 j))
        (lc_summable_geom hβ0 hβ1 (x := fun j => u (y (t + 1 + j))) (fun _ => hx _))
        (lc_summable_geom hβ0 hβ1 (x := fun j => u (y (t + j))) (fun _ => hx _))
      exact humono.monotoneOn (hy0 _) (hy0 _) (hyd (by omega))
    intro t
    exact (antitone_nat_of_succ_le hstep) (Nat.zero_le t)
  have hucbar : u cbar = (1 - β) * lc_detU β u y 0 := hug _
  have hV : ∀ t, lc_detValue β (fun _ => u cbar) t = lc_detU β u y 0 := by
    intro t
    rw [lc_detValue_const hβ0 hβ1, hucbar]
    field_simp
  have hfeas : lc_detFeasible β u y (lc_detU β u y 0) (fun _ => cbar) :=
    ⟨fun _ => hgpos _, ⟨max |cbar| |u cbar|, fun _ => ⟨le_max_left _ _, le_max_right _ _⟩⟩,
      fun t => by rw [hV]; exact hU t, by rw [hV]⟩
  refine ⟨hucbar, hfeas, fun c hc => ?_⟩
  exact lc_optimal_of_marginal hβ0 hβ1 ⟨K, hK⟩ du hdupos hduanti hsupp hfeas
    (fun _ _ _ => le_rfl) (hV 0) (fun t h => (h rfl).elim) hc

/-- **Exercise 22.1(b)** (Miao, p. 797). If endowments increase (`y₀ ≤ y₁ ≤ ⋯`), autarky is the
optimal contract. -/
theorem ex_22_1b {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ} {y : ℕ → ℝ}
    (hy0 : ∀ t, 0 < y t) (hyb : ∃ K, ∀ t, |y t| ≤ K ∧ |u (y t)| ≤ K) (hyi : Monotone y)
    (du : ℝ → ℝ) (hdupos : ∀ c, 0 < c → 0 < du c) (hduanti : AntitoneOn du (Set.Ioi 0))
    (hsupp : ∀ c, 0 < c → ∀ z, 0 < z → u z ≤ u c + du c * (z - c)) :
    lc_detFeasible β u y (lc_detU β u y 0) y ∧
      ∀ c, lc_detFeasible β u y (lc_detU β u y 0) c →
        lc_detPrincipal β y c ≤ lc_detPrincipal β y y := by
  have hfeas : lc_detFeasible β u y (lc_detU β u y 0) y :=
    ⟨hy0, hyb, fun _ => le_rfl, le_rfl⟩
  exact ⟨hfeas, fun c hc => lc_optimal_of_marginal hβ0 hβ1 hyb du hdupos hduanti hsupp hfeas
    hyi rfl (fun _ _ => rfl) hc⟩

/-- **Exercise 22.1(c)** (Miao, p. 798), and (22.11) (p. 780) in the deterministic case. With
`h_t = u⁻¹(m_t)`, `m_t = inf_{τ ≥ 1} Σ_{j<τ} β^j u(y_{t+j}) / Σ_{j<τ} β^j` (`lc_m`), the plan
`c₀ = h₀`, `c_t = max{c_{t-1}, h_t}` is feasible and optimal. -/
theorem ex_22_1c {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u g : ℝ → ℝ} {y : ℕ → ℝ}
    (hyb : ∃ K, ∀ t, |y t| ≤ K ∧ |u (y t)| ≤ K)
    (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a) (humono : StrictMonoOn u (Set.Ioi 0))
    (du : ℝ → ℝ) (hdupos : ∀ c, 0 < c → 0 < du c) (hduanti : AntitoneOn du (Set.Ioi 0))
    (hsupp : ∀ c, 0 < c → ∀ z, 0 < z → u z ≤ u c + du c * (z - c)) :
    let h : ℕ → ℝ := fun t => g (lc_m β (fun s => u (y s)) t)
    let c : ℕ → ℝ := fun t => g (lc_run (lc_m β (fun s => u (y s))) 0 t)
    c 0 = h 0 ∧ (∀ t, c (t + 1) = max (c t) (h (t + 1))) ∧
      lc_detFeasible β u y (lc_detU β u y 0) c ∧
      ∀ c', lc_detFeasible β u y (lc_detU β u y 0) c' →
        lc_detPrincipal β y c' ≤ lc_detPrincipal β y c := by
  intro h c
  obtain ⟨K, hK⟩ := hyb
  set x : ℕ → ℝ := fun s => u (y s) with hxdef
  have hx : ∀ t, |x t| ≤ K := fun t => (hK t).2
  set m := lc_m β x
  set a := lc_run m 0
  have hm := lc_m_abs_le hβ0 hx
  have ha := lc_run_abs_le m hm 0
  have hgmono := (lc_g_strictMono hgpos hug humono).monotone
  have hua : ∀ t, u (c t) = a t := fun t => hug _
  have hasucc : ∀ t, a (t + 1) = max (a t) (m (t + 1)) := by
    intro t; change lc_run m 0 (t + 1) = max (lc_run m 0 t) (m (t + 1)); rw [lc_run_succ, zero_add]
  have hsplit : ∀ t j, a (t + j) = max (a t) (lc_run m t j) := by
    intro t j
    change lc_run m 0 (t + j) = max (lc_run m 0 t) (lc_run m t j)
    rw [lc_run_add, zero_add]
  have hVc : ∀ t, lc_detValue β (fun s => u (c s)) t = lc_detValue β (fun j => a (t + j)) 0 := by
    intro t; rw [lc_detValue_shift]; simp only [hua]
  have hIC : ∀ t, lc_detU β u y t ≤ lc_detValue β (fun s => u (c s)) t := by
    intro t
    rw [hVc, lc_detU, ← lc_zhang_identity hβ0 hβ1 hx t]
    exact lc_detValue_mono hβ0 hβ1 (lc_run_abs_le m hm t) (fun j => ha _)
      (fun j => by change lc_run m t j ≤ a (t + j); rw [hsplit]; exact le_max_right _ _) 0
  have hbindt : ∀ t, a t = m t → lc_detValue β (fun s => u (c s)) t = lc_detU β u y t := by
    intro t hat
    rw [hVc, lc_detU, ← lc_zhang_identity hβ0 hβ1 hx t]
    unfold lc_detValue
    refine tsum_congr fun j => ?_
    simp only [zero_add]
    rw [hsplit, max_eq_right (by rw [hat]; simpa using (lc_run_ge m t j).2)]
  have hc0 : c 0 = h 0 := rfl
  have hcsucc : ∀ t, c (t + 1) = max (c t) (h (t + 1)) := by
    intro t
    simp only [c, h]
    rw [← hgmono.map_max]
    change g (a (t + 1)) = _
    rw [hasucc]
  have hfeas : lc_detFeasible β u y (lc_detU β u y 0) c := by
    refine ⟨fun t => hgpos _, ⟨max (g K) K, fun t => ⟨?_, ?_⟩⟩, hIC, hIC 0⟩
    · rw [abs_of_pos (hgpos _)]
      exact (hgmono (abs_le.mp (ha t)).2).trans (le_max_left _ _)
    · rw [hua]; exact (ha t).trans (le_max_right _ _)
  refine ⟨hc0, hcsucc, hfeas, fun c' hc' => ?_⟩
  refine lc_optimal_of_marginal hβ0 hβ1 ⟨K, hK⟩ du hdupos hduanti hsupp hfeas
    (hgmono.comp (lc_run_mono m 0)) (hbindt 0 rfl) (fun t hne => hbindt (t + 1) ?_) hc'
  rcases max_choice (a t) (m (t + 1)) with he | he
  · exfalso
    apply hne
    change g (a (t + 1)) = g (a t)
    rw [hasucc, he]
  · rw [hasucc, he]

/-- Miao, p. 780, the definition of `d_i(τ)` in the deterministic case: the constant consumption
`d = u⁻¹(A_t(τ))` on `[t, t+τ)` makes the incentive constraints at `t` and `t + τ` bind:
`Σ_{j<τ} β^j u(d) = U_d(y_t) − β^τ U_d(y_{t+τ})`. -/
theorem lc_d_tau {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u g : ℝ → ℝ} (hug : ∀ a, u (g a) = a)
    {y : ℕ → ℝ} {K : ℝ} (hx : ∀ t, |u (y t)| ≤ K) (t τ : ℕ) (hτ : 1 ≤ τ) :
    ∑ j ∈ Finset.range τ, β ^ j * u (g (lc_A β (fun s => u (y s)) t τ)) =
      lc_detU β u y t - β ^ τ * lc_detU β u y (t + τ) := by
  rw [hug, ← Finset.sum_mul]
  have hB := lc_B_ge_one hβ0 hτ
  have := lc_detValue_split hβ0 hβ1 hx t τ
  unfold lc_detU
  rw [this]
  change lc_B β τ * (lc_S β (fun s => u (y s)) t τ / lc_B β τ) = _
  field_simp
  simp [lc_S]

/-- Miao, p. 780, the definition of `d_i(τ)` in the Markov model of §22.1 for a deterministic
date `τ ≥ 1`: the constant consumption `d` with
`u(d) = Σ_{t<τ} β^t E[u(y_t) | y₀ = θᵢ] / Σ_{t<τ} β^t` satisfies
`E[Σ_{t<τ} β^t u(d) | y₀ = θᵢ] = U_d(θᵢ) − E[β^τ U_d(y_τ) | y₀ = θᵢ]`. -/
theorem lc_d_markov {ι : Type*} [Fintype ι] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {pl : ι → ι → ℝ} (hpl : lc_IsStochastic pl) {u g : ℝ → ℝ} (hug : ∀ a, u (g a) = a)
    (r : ι → ℝ) (i : ι) (τ : ℕ) (hτ : 1 ≤ τ) :
    ∑ t ∈ Finset.range τ, β ^ t * u (g ((∑ t ∈ Finset.range τ,
        β ^ t * (lc_condExp pl)^[t] r i) / lc_B β τ)) =
      lc_autarky β pl r i - β ^ τ * (lc_condExp pl)^[τ] (lc_autarky β pl r) i := by
  rw [hug, ← Finset.sum_mul, lc_autarky_split hβ0 hβ1 hpl r τ i]
  have hB := lc_B_ge_one hβ0 hτ
  change lc_B β τ * _ = _
  field_simp
  ring

/-- Miao, p. 781: `h = inf_{τ ≥ 1} d(τ)`: `u⁻¹(m_t)` is the greatest lower bound of the levels
`d_t(τ) = u⁻¹(A_t(τ))`, `τ ≥ 1`. -/
theorem lc_h_isGLB {β : ℝ} (hβ0 : 0 ≤ β) {u g : ℝ → ℝ} (hgpos : ∀ a, 0 < g a)
    (hug : ∀ a, u (g a) = a) (hgu : ∀ c, 0 < c → g (u c) = c)
    (humono : StrictMonoOn u (Set.Ioi 0)) {x : ℕ → ℝ} {K : ℝ} (hx : ∀ t, |x t| ≤ K) (t : ℕ) :
    IsGLB (Set.range fun τ : ℕ => g (lc_A β x t (τ + 1))) (g (lc_m β x t)) := by
  have hgmono := (lc_g_strictMono hgpos hug humono).monotone
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨τ, rfl⟩
    exact hgmono (lc_m_le_A hβ0 hx t (by omega))
  · rcases le_or_gt b 0 with hb0 | hb0
    · exact hb0.trans (hgpos _).le
    · have : u b ≤ lc_m β x t := le_ciInf fun τ => by
        have := humono.monotoneOn hb0 (hgpos _) (hb ⟨τ, rfl⟩)
        rwa [hug] at this
      rw [← hgu b hb0]
      exact hgmono this

/-- The consumption path from an initial utility level `z`:
`a₀ = z`, `a_{t+1} = max{a_t, m_{t+1}}` (Miao, p. 781). -/
def lc_zpath (m : ℕ → ℝ) (z : ℝ) : ℕ → ℝ
  | 0 => z
  | t + 1 => max (lc_zpath m z t) (m (t + 1))

theorem lc_zpath_abs_le (m : ℕ → ℝ) {M : ℝ} (hm : ∀ t, |m t| ≤ M) (z : ℝ) (t : ℕ) :
    |lc_zpath m z t| ≤ max |z| M := by
  induction t with
  | zero => exact le_max_left _ _
  | succ t ih =>
    simp only [lc_zpath]
    rcases max_choice (lc_zpath m z t) (m (t + 1)) with h | h <;> rw [h]
    · exact ih
    · exact (hm _).trans (le_max_right _ _)

/-- Miao, p. 781: "one can solve for a unique solution for `c₀`": the agent's value
`F(z) = Σ_t β^t a_t` of the path from initial utility `z` is strictly increasing in `z`, and
`F(m₀) = U_d(y₀)`. Hence the binding participation constraint `F(z) = v₀` has at most one
solution, `c₀ = u⁻¹(z)`. -/
theorem lc_c0_strictMono {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) :
    StrictMono (fun z => lc_detValue β (lc_zpath (lc_m β x) z) 0) ∧
      lc_detValue β (lc_zpath (lc_m β x) (lc_m β x 0)) 0 = lc_detValue β x 0 := by
  have hm := lc_m_abs_le hβ0 hx
  refine ⟨fun z z' hzz' => ?_, ?_⟩
  · have hmono : ∀ t, lc_zpath (lc_m β x) z t ≤ lc_zpath (lc_m β x) z' t := by
      intro t
      induction t with
      | zero => exact hzz'.le
      | succ t ih => exact max_le_max ih le_rfl
    set B := max (max |z| |z'|) M
    have hb : ∀ w, |w| ≤ max |z| |z'| → ∀ t, |lc_zpath (lc_m β x) w t| ≤ B := fun w hw t =>
      (lc_zpath_abs_le (lc_m β x) hm w t).trans (max_le_max hw le_rfl)
    have hbz := hb z (le_max_left _ _)
    have hbz' := hb z' (le_max_right _ _)
    have h1 := lc_detValue_mono hβ0 hβ1 hbz hbz' hmono 1
    simp only
    rw [lc_detValue_split0 hβ0 hβ1 hbz 1, lc_detValue_split0 hβ0 hβ1 hbz' 1]
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one]
    change z + _ < z' + _
    nlinarith [mul_le_mul_of_nonneg_left h1 hβ0]
  · rw [← lc_zhang_identity hβ0 hβ1 hx 0]
    congr 1
    funext t
    induction t with
    | zero => rfl
    | succ t ih => simp only [lc_zpath, lc_run_succ, ih, zero_add]

/-- Miao, p. 781: "`c₀(v₀, θᵢ) > h(θᵢ)` when `v₀ > U_d(θᵢ)`" (deterministic case): if the path
from initial utility `z` delivers more than `U_d(y₀)`, then `z > m₀`, so `c₀ = u⁻¹(z) > h(y₀)`. -/
theorem lc_c0_gt_h {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u g : ℝ → ℝ} (hgpos : ∀ a, 0 < g a)
    (hug : ∀ a, u (g a) = a) (humono : StrictMonoOn u (Set.Ioi 0)) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (z : ℝ)
    (hz : lc_detValue β x 0 < lc_detValue β (lc_zpath (lc_m β x) z) 0) :
    lc_m β x 0 < z ∧ g (lc_m β x 0) < g z := by
  obtain ⟨hmono, h0⟩ := lc_c0_strictMono hβ0 hβ1 hx
  have : lc_m β x 0 < z := by
    by_contra h
    push Not at h
    have := hmono.monotone h
    linarith
  exact ⟨this, lc_g_strictMono hgpos hug humono this⟩

/-- Correction to **Exercise 22.1(c)** (Miao, p. 798): the minimum over `τ ≥ 1` need not be
attained. For `u(y) = (1, 0, 0, …)` (e.g. `u = log`, `y = (e, 1, 1, …)`) and `0 < β < 1` the
averages `A₀(τ) = 1/B_τ` strictly decrease, so no `τ` minimises them; `min` must be `inf`. -/
theorem lc_ex_22_1c_min_not_attained {β : ℝ} (hβ0 : 0 < β) :
    let x : ℕ → ℝ := fun t => if t = 0 then 1 else 0
    (∀ τ, 1 ≤ τ → lc_A β x 0 (τ + 1) < lc_A β x 0 τ) ∧
      ¬ ∃ τ, 1 ≤ τ ∧ ∀ τ', 1 ≤ τ' → lc_A β x 0 τ ≤ lc_A β x 0 τ' := by
  intro x
  have hS : ∀ τ, 1 ≤ τ → lc_S β x 0 τ = 1 := by
    intro τ hτ
    unfold lc_S
    simp only [zero_add, x, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' (Finset.range τ) 0 (fun j => β ^ j)]
    simp [Finset.mem_range.mpr (by omega : 0 < τ)]
  have hdec : ∀ τ, 1 ≤ τ → lc_A β x 0 (τ + 1) < lc_A β x 0 τ := by
    intro τ hτ
    unfold lc_A
    rw [hS τ hτ, hS (τ + 1) (by omega)]
    have hB := lc_B_ge_one hβ0.le hτ
    have hB' : lc_B β (τ + 1) = lc_B β τ + β ^ τ := by
      unfold lc_B; rw [Finset.sum_range_succ]
    rw [hB']
    have := pow_pos hβ0 τ
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  refine ⟨hdec, ?_⟩
  rintro ⟨τ, hτ, hmin⟩
  have := hmin (τ + 1) (by omega)
  linarith [hdec τ hτ]

/-- Correction to the notation `h(θᵢ)` (Miao, pp. 780–781 and Exercise 22.1(c)): in the
deterministic model the minimum consumption level depends on the whole future endowment path,
not on the current endowment alone. For `u(y) = (1, 0, 1, 1, …)` and `0 < β < 1`,
`u(y₀) = u(y₂)` but `m₀ ≤ 1/(1 + β) < 1 = m₂`. -/
theorem lc_h_depends_on_future {β : ℝ} (hβ0 : 0 < β) :
    let x : ℕ → ℝ := fun t => if t = 1 then 0 else 1
    x 0 = x 2 ∧ lc_m β x 0 < lc_m β x 2 := by
  intro x
  have hx : ∀ t, |x t| ≤ 1 := fun t => by simp only [x]; split_ifs <;> simp
  refine ⟨rfl, ?_⟩
  have h2 : lc_m β x 2 = 1 := by
    have : ∀ τ, lc_A β x 2 (τ + 1) = 1 := by
      intro τ
      have hB := lc_B_ge_one hβ0.le (by omega : 1 ≤ τ + 1)
      unfold lc_A
      have : lc_S β x 2 (τ + 1) = lc_B β (τ + 1) := by
        unfold lc_S lc_B
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : 2 + j ≠ 1 := by omega
        simp only [x, hj, ↓reduceIte, mul_one]
      rw [this, div_self (by linarith)]
    unfold lc_m
    simp only [this, ciInf_const]
  have h0 : lc_m β x 0 ≤ 1 / (1 + β) := by
    have := lc_m_le_A hβ0.le hx 0 (by omega : 1 ≤ 2)
    have hA : lc_A β x 0 2 = 1 / (1 + β) := by
      simp [lc_A, lc_S, lc_B, Finset.sum_range_succ, x]
    rwa [hA] at this
  rw [h2]
  refine lt_of_le_of_lt h0 ?_
  rw [div_lt_one (by linarith)]
  linarith

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 22.2: the AR(1) endowment (Miao, p. 798)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, Exercise 22.2, p. 798. Income follows
`ln y_t = ρ ln y_{t-1} + σ ε_t` with `β = 0.98`, `ρ = 0.95`, `σ = 0.1`, and the outside option is
autarky.

(a) The Bellman equation is that of §22.1.1 with the AR(1) transition in place of `π`; for any
finite discretisation of the shock it is `lc_BellmanAt` (module `LCBellman`). Its mathematical
input that can be computed in closed form is the autarky value: with log utility and
`x = ln y`, `U_d(y) = ln y/(1 − βρ)`, which solves the autarky recursion
`U_d(x) = x + β E[U_d(ρx + σε)]` for any mean-zero integrable shock (`ex_22_2a`); in particular
`U_d(1) = 0`.

(b), (c): not formalised (computational: Matlab code, plots, and the numerical root of
`P(v, 1) = 0`).
-/

namespace Miao.RecursiveContracts

open MeasureTheory

/-- **Exercise 22.2(a)** (Miao, p. 798), the autarky value with log utility: for any probability
distribution `μ` of the shock with mean zero, `x/(1 − βρ)` (with `x = ln y`) solves the autarky
recursion `U_d(x) = x + β ∫ U_d(ρx + σε) dμ(ε)`, and `U_d(1) = 0`. -/
theorem ex_22_2a (β ρ σ : ℝ) (hβρ : β * ρ ≠ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun ε : ℝ => ε) μ) (hmean : ∫ ε, ε ∂μ = 0) (x : ℝ) :
    x / (1 - β * ρ) = x + β * ∫ ε, (ρ * x + σ * ε) / (1 - β * ρ) ∂μ ∧
      (Real.log 1) / (1 - β * ρ) = 0 := by
  have h1 : 1 - β * ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβρ)
  refine ⟨?_, by simp⟩
  have : ∫ ε, (ρ * x + σ * ε) / (1 - β * ρ) ∂μ = ρ * x / (1 - β * ρ) := by
    have e : (fun ε : ℝ => (ρ * x + σ * ε) / (1 - β * ρ)) =
        fun ε => ρ * x / (1 - β * ρ) + σ / (1 - β * ρ) * ε := by
      funext ε; field_simp
    rw [e, integral_add (integrable_const _) (hint.const_mul _), integral_const,
      integral_const_mul, hmean]
    simp
  rw [this]
  field_simp
  ring

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hidden action: the repeated moral-hazard model

Miao, §22.2 "Hidden Action", pp. 781–785. A risk-neutral principal owns a technology operated by
an agent whose effort `a ∈ A = [a_min, a_max]` is not observed; output `y` has density
`f (y | a)` on the output interval `[y_lo, y_hi]`, i.i.d. over time for a fixed action. In Lean a
density is a function `f : ℝ → ℝ → ℝ`, `f a y = f (y | a)`, and its effort derivative is `fa`.

* The sequence problem: the history density `π (y^t; a)` built recursively from `f`
  (`ha_histDensity`, with `ha_histDensity_succ`, `ha_histDensity_nonneg` and the i.i.d. product
  form for a constant effort plan `ha_histDensity_iid`), the principal's and the agent's lifetime
  values and the incentive and participation constraints (22.12)–(22.13) (`ha_seqIC`,
  `ha_seqPC`).
* The recursive problem of Spear and Srivastava (1987): the agent's value of a contract
  `(a(v), c(v, ·), w(v, ·))` under any effort, the principal's value, the recursive incentive
  constraint (22.14) (`ha_IC`), promise keeping (22.15) (`ha_PK`), the first-order approach
  (22.16) (`ha_FOA`) and the principal's Bellman equation (`ha_IsPrincipalValue`).
* The first-order approach is necessary: an interior effort satisfying (22.14) satisfies (22.16)
  (`eq_22_16`), with `∫ f_a = 0` (`ha_integral_fa_eq_zero`) and a concrete family of densities
  (linear in effort) for which the differentiation under the integral sign holds
  (`ha_linearDensity_hasDerivAt`).
* The Lagrangian first-order conditions (22.17)–(22.19) and their consequence (22.20)
  (`eq_22_17`, `eq_22_18`, `eq_22_19`, `eq_22_20`), from the pointwise Lagrangian
  `ha_pointLagr`, and the envelope condition `P′(v) = −λ(v)` (`ha_envelope`,
  `ha_envelope_condition`).

Departures: the book writes the agent's discount factor in (22.12)–(22.13) as `α` after assuming
the two discount factors are both `β`; the definitions take the discount factor as an argument.
The conditions (22.17) and (22.19) are derived from the maximisation of the Lagrangian's integrand
output by output (the way the book's first-order conditions in the functions `c(v, ·)` and
`w(v, ·)` arise); (22.18) from the maximisation of the Lagrangian in effort, given the
differentiation of the integrals under the integral sign.
-/

namespace Miao.RecursiveContracts

open MeasureTheory

/-! ## The sequence problem -/

/-- Miao, p. 782: the density of the output history `y^t = (y_0, …, y_t)` under the effort plan
`a`, `dπ(y^0; a) = f(y_0 | a_0) dy_0` and
`dπ(y^{t+1}; a) = f(y_{t+1} | a(y^t)) dπ(y^t; a) dy_{t+1}`.
The plan's date-`t` effort `a t` is a function of the history `y^{t−1}` of length `t`. -/
def ha_histDensity (f : ℝ → ℝ → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) :
    (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ
  | 0, y => f (a 0 Fin.elim0) (y 0)
  | t + 1, y => f (a (t + 1) (Fin.init y)) (y (Fin.last (t + 1))) *
      ha_histDensity f a t (Fin.init y)

/-- Miao, p. 782: the recursion `dπ(y^{t+1}; a) = f(y_{t+1} | a(y^t)) dπ(y^t; a)`. -/
theorem ha_histDensity_succ (f : ℝ → ℝ → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) (t : ℕ)
    (y : Fin (t + 2) → ℝ) :
    ha_histDensity f a (t + 1) y =
      f (a (t + 1) (Fin.init y)) (y (Fin.last (t + 1))) * ha_histDensity f a t (Fin.init y) :=
  rfl

/-- Miao, p. 782: the history densities are nonnegative when `f` is. -/
theorem ha_histDensity_nonneg {f : ℝ → ℝ → ℝ} (hf : ∀ a y, 0 ≤ f a y)
    (a : (t : ℕ) → (Fin t → ℝ) → ℝ) (t : ℕ) (y : Fin (t + 1) → ℝ) :
    0 ≤ ha_histDensity f a t y := by
  induction t with
  | zero => exact hf _ _
  | succ t ih => exact mul_nonneg (hf _ _) (ih _)

/-- Miao, p. 782: "for any fixed action, output is independently and identically distributed
over time": under a constant effort plan `a ≡ a₀` the history density is the product
`∏_{s ≤ t} f(y_s | a₀)`. -/
theorem ha_histDensity_iid (f : ℝ → ℝ → ℝ) {a : (t : ℕ) → (Fin t → ℝ) → ℝ} {a₀ : ℝ}
    (ha : ∀ t h, a t h = a₀) (t : ℕ) (y : Fin (t + 1) → ℝ) :
    ha_histDensity f a t y = ∏ i, f a₀ (y i) := by
  induction t with
  | zero => simp [ha_histDensity, ha]
  | succ t ih =>
    rw [ha_histDensity_succ, ih, ha, Fin.prod_univ_castSucc (n := t + 1), mul_comm]
    rfl

/-- Miao, p. 782: the principal's lifetime value `∑_t β^t ∫ v_P(y_t − c(y^t)) dπ(y^t; a)` of the
compensation plan `c` (a function of `y^t`) and effort plan `a`, with period utility `vP`. -/
noncomputable def ha_seqPrincipalValue (vP : ℝ → ℝ) (β : ℝ) (f : ℝ → ℝ → ℝ)
    (c : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) : ℝ :=
  ∑' t, β ^ t * ∫ y, vP (y (Fin.last t) - c t y) * ha_histDensity f a t y

/-- Miao, (22.12)–(22.13), pp. 782–783: the agent's lifetime value
`∑_t α^t ∫ u(c(y^t), a(y^{t−1})) dπ(y^t; a)` of the compensation plan `c` under the effort
plan `a`. -/
noncomputable def ha_seqAgentValue (u : ℝ → ℝ → ℝ) (α : ℝ) (f : ℝ → ℝ → ℝ)
    (c : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) : ℝ :=
  ∑' t, α ^ t * ∫ y, u (c t y) (a t (Fin.init y)) * ha_histDensity f a t y

/-- Miao, (22.12), p. 782: the incentive constraint of the sequence problem: no effort plan
`â` with values in `A = [a_min, a_max]` gives the agent more than the recommended plan `a`. -/
def ha_seqIC (u : ℝ → ℝ → ℝ) (α : ℝ) (f : ℝ → ℝ → ℝ) (amin amax : ℝ)
    (c : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) : Prop :=
  ∀ â : (t : ℕ) → (Fin t → ℝ) → ℝ, (∀ t h, â t h ∈ Set.Icc amin amax) →
    ha_seqAgentValue u α f c â ≤ ha_seqAgentValue u α f c a

/-- Miao, (22.13), p. 783: the participation constraint of the sequence problem. -/
def ha_seqPC (u : ℝ → ℝ → ℝ) (α : ℝ) (f : ℝ → ℝ → ℝ) (u₀ : ℝ)
    (c : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) : Prop :=
  u₀ ≤ ha_seqAgentValue u α f c a

/-! ## The recursive problem -/

/-- Miao, (22.14)–(22.15), p. 783: the agent's value `∫ [φ(c(y)) + β w(y)] f(y | ã) dy − ψ(ã)` of
the payment schedule `c` and promised-value schedule `w` when he exerts effort `ã`. -/
noncomputable def ha_agentValue (ylo yhi β : ℝ) (φ ψ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (c w : ℝ → ℝ)
    (ã : ℝ) : ℝ :=
  (∫ y in ylo..yhi, (φ (c y) + β * w y) * f ã y) - ψ ã

/-- Miao, p. 783: the principal's value `∫ [(y − c(y)) + β P(w(y))] f(y | a) dy` of the contract
`(a, c, w)` given the continuation value function `P`. -/
noncomputable def ha_principalValue (ylo yhi β : ℝ) (P : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (a : ℝ)
    (c w : ℝ → ℝ) : ℝ :=
  ∫ y in ylo..yhi, (y - c y + β * P (w y)) * f a y

/-- Miao, (22.14), p. 783: the recursive incentive constraint: the recommended effort `a` is
optimal for the agent among all efforts in `A = [a_min, a_max]`. -/
def ha_IC (ylo yhi β : ℝ) (φ ψ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (amin amax a : ℝ) (c w : ℝ → ℝ) :
    Prop :=
  ∀ ã ∈ Set.Icc amin amax,
    ha_agentValue ylo yhi β φ ψ f c w ã ≤ ha_agentValue ylo yhi β φ ψ f c w a

/-- Miao, (22.15), p. 783: promise keeping: the contract delivers at least the promised
value `v`. -/
def ha_PK (ylo yhi β : ℝ) (φ ψ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (v a : ℝ) (c w : ℝ → ℝ) : Prop :=
  v ≤ ha_agentValue ylo yhi β φ ψ f c w a

/-- Miao, (22.16), p. 784: the first-order condition replacing the incentive constraint,
`∫ [φ(c(y)) + β w(y)] f_a(y | a) dy − ψ′(a) = 0`. -/
def ha_FOA (ylo yhi β : ℝ) (φ dψ : ℝ → ℝ) (fa : ℝ → ℝ → ℝ) (a : ℝ) (c w : ℝ → ℝ) : Prop :=
  (∫ y in ylo..yhi, (φ (c y) + β * w y) * fa a y) - dψ a = 0

/-- Miao, p. 783: `P` solves the principal's Bellman equation: for each promised value `v`, `P v`
is the largest principal's value over contracts `(a, c, w)` with `a ∈ A` satisfying (22.14)
and (22.15). -/
def ha_IsPrincipalValue (ylo yhi β : ℝ) (φ ψ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (amin amax : ℝ)
    (P : ℝ → ℝ) : Prop :=
  ∀ v, IsGreatest {x | ∃ a ∈ Set.Icc amin amax, ∃ c w : ℝ → ℝ,
    ha_IC ylo yhi β φ ψ f amin amax a c w ∧ ha_PK ylo yhi β φ ψ f v a c w ∧
    x = ha_principalValue ylo yhi β P f a c w} (P v)

/-- Miao, p. 783: under the Bellman equation, the principal's value of any contract satisfying
(22.14) and (22.15) at `v` is at most `P(v)`, and some such contract attains `P(v)`. -/
theorem ha_principalValue_le {ylo yhi β : ℝ} {φ ψ : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {amin amax : ℝ}
    {P : ℝ → ℝ} (hP : ha_IsPrincipalValue ylo yhi β φ ψ f amin amax P) (v : ℝ) :
    (∀ a ∈ Set.Icc amin amax, ∀ c w : ℝ → ℝ, ha_IC ylo yhi β φ ψ f amin amax a c w →
      ha_PK ylo yhi β φ ψ f v a c w → ha_principalValue ylo yhi β P f a c w ≤ P v) ∧
    ∃ a ∈ Set.Icc amin amax, ∃ c w : ℝ → ℝ, ha_IC ylo yhi β φ ψ f amin amax a c w ∧
      ha_PK ylo yhi β φ ψ f v a c w ∧ ha_principalValue ylo yhi β P f a c w = P v := by
  refine ⟨fun a ha c w hic hpk => (hP v).2 ⟨a, ha, c, w, hic, hpk, rfl⟩, ?_⟩
  obtain ⟨a, ha, c, w, hic, hpk, heq⟩ := (hP v).1
  exact ⟨a, ha, c, w, hic, hpk, heq.symm⟩

/-! ## The first-order approach -/

/-- Miao, p. 785 (used in the proofs of Propositions 22.2.1 and 22.2.2): `∫ f_a(y | a) dy = 0`,
differentiating `∫ f(y | ã) dy = 1` in `ã` at `a`. -/
theorem ha_integral_fa_eq_zero {ylo yhi a : ℝ} {f fa : ℝ → ℝ → ℝ}
    (hf1 : ∀ ã, ∫ y in ylo..yhi, f ã y = 1)
    (hd : HasDerivAt (fun ã => ∫ y in ylo..yhi, f ã y) (∫ y in ylo..yhi, fa a y) a) :
    ∫ y in ylo..yhi, fa a y = 0 := by
  have hconst : (fun ã => ∫ y in ylo..yhi, f ã y) = fun _ => (1 : ℝ) := funext hf1
  rw [hconst] at hd
  exact hd.unique (hasDerivAt_const a 1)

/-- Miao, p. 783 ("we assume that `f(y | a)` is twice continuously differentiable in `a`"): a
concrete family of densities for which differentiation under the integral sign holds: for
`f(y | a) = f₀(y) + a f₁(y)` with `f₀, f₁` integrable, `f_a = f₁` and
`d/dã ∫ g(y) f(y | ã) dy = ∫ g(y) f₁(y) dy` for every `g` with `g f₀`, `g f₁` integrable. -/
theorem ha_linearDensity_hasDerivAt {ylo yhi : ℝ} {g f₀ f₁ : ℝ → ℝ}
    (h₀ : IntervalIntegrable (fun y => g y * f₀ y) volume ylo yhi)
    (h₁ : IntervalIntegrable (fun y => g y * f₁ y) volume ylo yhi) (a : ℝ) :
    HasDerivAt (fun ã => ∫ y in ylo..yhi, g y * (f₀ y + ã * f₁ y))
      (∫ y in ylo..yhi, g y * f₁ y) a := by
  have hrw : (fun ã => ∫ y in ylo..yhi, g y * (f₀ y + ã * f₁ y)) =
      fun ã => (∫ y in ylo..yhi, g y * f₀ y) + ã * ∫ y in ylo..yhi, g y * f₁ y := by
    funext ã
    have hsplit : (fun y => g y * (f₀ y + ã * f₁ y)) =
        fun y => g y * f₀ y + ã * (g y * f₁ y) := by
      funext y
      ring
    rw [hsplit, intervalIntegral.integral_add h₀ (h₁.const_mul ã),
      intervalIntegral.integral_const_mul]
  rw [hrw]
  simpa using ((hasDerivAt_id a).mul_const (∫ y in ylo..yhi, g y * f₁ y)).const_add
    (∫ y in ylo..yhi, g y * f₀ y)

/-- Miao, (22.16), p. 784: the first-order approach is necessary: if the recommended effort `a`
is interior to `A = [a_min, a_max]` and satisfies the recursive incentive constraint (22.14),
and the agent's value is differentiable in effort (differentiation under the integral sign,
`d/dã ∫ h f(· | ã) = ∫ h f_a(· | a)` at `a`), then (22.16) holds. -/
theorem eq_22_16 {ylo yhi β amin amax a : ℝ} {φ ψ dψ : ℝ → ℝ} {f fa : ℝ → ℝ → ℝ}
    {c w : ℝ → ℝ} (hic : ha_IC ylo yhi β φ ψ f amin amax a c w)
    (hlo : amin < a) (hhi : a < amax)
    (hI : HasDerivAt (fun ã => ∫ y in ylo..yhi, (φ (c y) + β * w y) * f ã y)
      (∫ y in ylo..yhi, (φ (c y) + β * w y) * fa a y) a)
    (hψ : HasDerivAt ψ (dψ a) a) :
    ha_FOA ylo yhi β φ dψ fa a c w := by
  have hmax : IsLocalMax (ha_agentValue ylo yhi β φ ψ f c w) a :=
    Filter.eventually_of_mem (Icc_mem_nhds hlo hhi) hic
  exact hmax.hasDerivAt_eq_zero (hI.sub hψ)

/-! ## The Lagrangian and its first-order conditions -/

/-- Miao, p. 784: the integrand of the Lagrangian `L` at output `y`, as a function of the
payment `x = c(v, y)` and promised value `z = w(v, y)`, with `fy = f(y | a)`, `fay = f_a(y | a)`:
`[(y − x) + β P(z)] fy + μ [φ(x) + β z] fay + λ [φ(x) + β z] fy`. Integrating it over `y` and
subtracting `μ ψ′(a) + λ (ψ(a) + v)` gives `L`. -/
noncomputable def ha_pointLagr (β : ℝ) (φ P : ℝ → ℝ) (μ lam y fy fay x z : ℝ) : ℝ :=
  (y - x + β * P z) * fy + μ * ((φ x + β * z) * fay) + lam * ((φ x + β * z) * fy)

/-- Miao, (22.17), p. 784: the first-order condition in the payment: if the payment `x = c(v, y)`
maximises the Lagrangian's integrand at `y` (locally), `f(y | a) > 0` and `φ′(x) > 0`, then
`1 / φ′(c(v, y)) = λ(v) + μ(v) f_a(y | a) / f(y | a)`. -/
theorem eq_22_17 {β : ℝ} {φ dφ P : ℝ → ℝ} {μ lam y fy fay x z : ℝ}
    (hmax : IsLocalMax (fun x' => ha_pointLagr β φ P μ lam y fy fay x' z) x)
    (hφ : HasDerivAt φ (dφ x) x) (hfy : 0 < fy) (hdφ : 0 < dφ x) :
    1 / dφ x = lam + μ * (fay / fy) := by
  have hd : HasDerivAt (fun x' => ha_pointLagr β φ P μ lam y fy fay x' z)
      (-fy + μ * (dφ x * fay) + lam * (dφ x * fy)) x := by
    have h1 : HasDerivAt (fun x' => (y - x' + β * P z) * fy) (-1 * fy) x :=
      (((hasDerivAt_id x).const_sub y).add_const (β * P z)).mul_const fy
    have h2 : HasDerivAt (fun x' => (φ x' + β * z) * fay) (dφ x * fay) x :=
      (hφ.add_const (β * z)).mul_const fay
    have h3 : HasDerivAt (fun x' => (φ x' + β * z) * fy) (dφ x * fy) x :=
      (hφ.add_const (β * z)).mul_const fy
    exact ((h1.add (h2.const_mul μ)).add (h3.const_mul lam)).congr_deriv (by ring)
  have h0 := hmax.hasDerivAt_eq_zero hd
  field_simp
  linear_combination (-1) * h0

/-- Miao, (22.19), p. 785: the first-order condition in the promised value: if `z = w(v, y)`
maximises the Lagrangian's integrand at `y` (locally), then
`β P′(w(v, y)) f(y | a) + μ β f_a(y | a) + λ β f(y | a) = 0`. -/
theorem eq_22_19 {β : ℝ} {φ P dP : ℝ → ℝ} {μ lam y fy fay x z : ℝ}
    (hmax : IsLocalMax (fun z' => ha_pointLagr β φ P μ lam y fy fay x z') z)
    (hP : HasDerivAt P (dP z) z) :
    β * dP z * fy + μ * β * fay + lam * β * fy = 0 := by
  have hd : HasDerivAt (fun z' => ha_pointLagr β φ P μ lam y fy fay x z')
      (β * dP z * fy + μ * (β * fay) + lam * (β * fy)) z := by
    have h1 : HasDerivAt (fun z' => (y - x + β * P z') * fy) (β * dP z * fy) z :=
      ((hP.const_mul β).const_add (y - x)).mul_const fy
    have h2 : HasDerivAt (fun z' => (φ x + β * z') * fay) (β * 1 * fay) z :=
      (((hasDerivAt_id z).const_mul β).const_add (φ x)).mul_const fay
    have h3 : HasDerivAt (fun z' => (φ x + β * z') * fy) (β * 1 * fy) z :=
      (((hasDerivAt_id z).const_mul β).const_add (φ x)).mul_const fy
    exact ((h1.add (h2.const_mul μ)).add (h3.const_mul lam)).congr_deriv (by ring)
  have h0 := hmax.hasDerivAt_eq_zero hd
  linear_combination h0

/-- Miao, (22.20), p. 785: "(22.17) and (22.19) imply" `P′(w(v, y)) = −1 / φ′(c(v, y))`, when the
payment and the promised value both maximise the Lagrangian's integrand at `y`, `β > 0`,
`f(y | a) > 0` and `φ′ > 0`. -/
theorem eq_22_20 {β : ℝ} {φ dφ P dP : ℝ → ℝ} {μ lam y fy fay x z : ℝ}
    (hc : IsLocalMax (fun x' => ha_pointLagr β φ P μ lam y fy fay x' z) x)
    (hw : IsLocalMax (fun z' => ha_pointLagr β φ P μ lam y fy fay x z') z)
    (hφ : HasDerivAt φ (dφ x) x) (hP : HasDerivAt P (dP z) z) (hβ : 0 < β) (hfy : 0 < fy)
    (hdφ : 0 < dφ x) :
    dP z = -1 / dφ x := by
  have h17 := eq_22_17 hc hφ hfy hdφ
  have h19 := eq_22_19 hw hP
  rw [neg_div, h17]
  have h19' : dP z * fy + μ * fay + lam * fy = 0 :=
    mul_left_cancel₀ hβ.ne' (by linear_combination h19)
  field_simp
  linear_combination h19'

/-- Miao, (22.18), pp. 784–785: the first-order condition in effort. If the recommended effort
`a` maximises (locally) the Lagrangian
`L(ã) = ∫ g f(· | ã) + μ (∫ h f_a(· | ã) − ψ′(ã)) + λ (∫ h f(· | ã) − ψ(ã) − v)`, with
`g(y) = y − c(v, y) + β P(w(v, y))` and `h(y) = φ(c(v, y)) + β w(v, y)`, the integrals are
differentiated under the integral sign, and (22.16) holds, then
`0 = ∫ g f_a(· | a) + μ (∫ h f_aa(· | a) − ψ″(a))`: the `λ` term is `λ` times (22.16). -/
theorem eq_22_18 {ylo yhi a μ lam v : ℝ} {g h ψ dψ ddψ : ℝ → ℝ} {f fa faa : ℝ → ℝ → ℝ}
    (hmax : IsLocalMax (fun ã => (∫ y in ylo..yhi, g y * f ã y) +
      μ * ((∫ y in ylo..yhi, h y * fa ã y) - dψ ã) +
      lam * ((∫ y in ylo..yhi, h y * f ã y) - ψ ã - v)) a)
    (hg : HasDerivAt (fun ã => ∫ y in ylo..yhi, g y * f ã y) (∫ y in ylo..yhi, g y * fa a y) a)
    (hh1 : HasDerivAt (fun ã => ∫ y in ylo..yhi, h y * fa ã y)
      (∫ y in ylo..yhi, h y * faa a y) a)
    (hh0 : HasDerivAt (fun ã => ∫ y in ylo..yhi, h y * f ã y)
      (∫ y in ylo..yhi, h y * fa a y) a)
    (hψ : HasDerivAt ψ (dψ a) a) (hdψ : HasDerivAt dψ (ddψ a) a)
    (hfoa : (∫ y in ylo..yhi, h y * fa a y) - dψ a = 0) :
    0 = (∫ y in ylo..yhi, g y * fa a y) + μ * ((∫ y in ylo..yhi, h y * faa a y) - ddψ a) := by
  have hd := (hg.add ((hh1.sub hdψ).const_mul μ)).add (((hh0.sub hψ).sub_const v).const_mul lam)
  have h0 := hmax.hasDerivAt_eq_zero hd
  rw [hfoa, mul_zero, add_zero] at h0
  exact h0.symm

/-! ## The envelope condition -/

/-- Miao, p. 785 ("By the envelope condition, `P′(v) = −λ(v)`"), in abstract form. Let contracts
`x ∈ X` have principal's value `F x`, first-order-approach residual `G x` (constraint `G x = 0`)
and agent's value `K x` (promise keeping `K x ≥ v`). Suppose that for each `v′` the value `P v′`
is attained by some feasible contract, that the contract `xs` attaining `P v` maximises the
Lagrangian `F + μ G + λ (K − v)` over all contracts with `λ ≥ 0`, and complementary slackness
`λ (K xs − v) = 0`. If `P` is differentiable at `v`, then `P′(v) = −λ`. -/
theorem ha_envelope {X : Type*} (F G K : X → ℝ) (P : ℝ → ℝ) (xs : X) {v p μ lam : ℝ}
    (hP : HasDerivAt P p v) (hlam : 0 ≤ lam)
    (hfeas : ∀ v', ∃ x, G x = 0 ∧ v' ≤ K x ∧ P v' ≤ F x)
    (hsaddle : ∀ x, F x + μ * G x + lam * (K x - v) ≤ F xs + μ * G xs + lam * (K xs - v))
    (hval : F xs = P v) (hG : G xs = 0) (hcs : lam * (K xs - v) = 0) :
    p = -lam := by
  have hle : ∀ v', P v' - (P v - lam * (v' - v)) ≤ P v - (P v - lam * (v - v)) := by
    intro v'
    obtain ⟨x, hGx, hKx, hPx⟩ := hfeas v'
    have h1 := hsaddle x
    rw [hGx, hG, hcs, hval] at h1
    nlinarith
  have hmax : IsLocalMax (fun v' => P v' - (P v - lam * (v' - v))) v :=
    Filter.Eventually.of_forall hle
  have hd : HasDerivAt (fun v' => P v' - (P v - lam * (v' - v))) (p - -(lam * 1)) v :=
    hP.sub ((((hasDerivAt_id v).sub_const v).const_mul lam).const_sub (P v))
  have h0 := hmax.hasDerivAt_eq_zero hd
  linarith

/-- Miao, p. 785: the envelope condition `P′(v) = −λ(v)` for the recursive moral-hazard problem
under the first-order approach: contracts are triples `(a, c, w)`, the principal's value is
`ha_principalValue`, the constraint is (22.16) and promise keeping is (22.15). The hypotheses
are those of `ha_envelope` for this problem. -/
theorem ha_envelope_condition {ylo yhi β v p μ lam : ℝ} {φ ψ dψ P : ℝ → ℝ} {f fa : ℝ → ℝ → ℝ}
    {a : ℝ} {c w : ℝ → ℝ} (hP : HasDerivAt P p v) (hlam : 0 ≤ lam)
    (hfeas : ∀ v', ∃ a' c' w', ha_FOA ylo yhi β φ dψ fa a' c' w' ∧
      ha_PK ylo yhi β φ ψ f v' a' c' w' ∧ P v' ≤ ha_principalValue ylo yhi β P f a' c' w')
    (hsaddle : ∀ a' c' w', ha_principalValue ylo yhi β P f a' c' w' +
      μ * ((∫ y in ylo..yhi, (φ (c' y) + β * w' y) * fa a' y) - dψ a') +
      lam * (ha_agentValue ylo yhi β φ ψ f c' w' a' - v) ≤
      ha_principalValue ylo yhi β P f a c w +
      μ * ((∫ y in ylo..yhi, (φ (c y) + β * w y) * fa a y) - dψ a) +
      lam * (ha_agentValue ylo yhi β φ ψ f c w a - v))
    (hval : ha_principalValue ylo yhi β P f a c w = P v) (hfoa : ha_FOA ylo yhi β φ dψ fa a c w)
    (hcs : lam * (ha_agentValue ylo yhi β φ ψ f c w a - v) = 0) :
    p = -lam := by
  refine ha_envelope (X := ℝ × (ℝ → ℝ) × (ℝ → ℝ))
    (fun x => ha_principalValue ylo yhi β P f x.1 x.2.1 x.2.2)
    (fun x => (∫ y in ylo..yhi, (φ (x.2.1 y) + β * x.2.2 y) * fa x.1 y) - dψ x.1)
    (fun x => ha_agentValue ylo yhi β φ ψ f x.2.1 x.2.2 x.1) P (a, c, w) hP hlam ?_
    (fun x => hsaddle x.1 x.2.1 x.2.2) hval hfoa hcs
  intro v'
  obtain ⟨a', c', w', h1, h2, h3⟩ := hfeas v'
  exact ⟨(a', c', w'), h1, h2, h3⟩

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hidden action: expectations over the output interval

Miao, §22.2, pp. 785–787. The integral facts the proofs of Propositions 22.2.1–22.2.3 use, for
expectations `E[g] = ∫_{y_lo}^{y_hi} g(y) p(y) dy` against a density `p` on the output interval:

* the mean value theorem for integrals (`ha_integral_mean_value`, used for (22.22));
* the expectation of the likelihood ratio, `E[f_a / f] = ∫ f_a` (`ha_expect_lr`), the
  covariance decomposition `E[g X] = Cov(g, X) + E[g] E[X]` (`ha_expect_mul_eq_cov_add`) and the
  MLRC covariance inequality: for `g` increasing and `f_a / f` increasing with `∫ f_a = 0`,
  `∫ g f_a = Cov(g, f_a / f) ≥ 0` (`ha_sign_change`, `ha_mlrc_integral_nonneg`,
  `ha_cov_lr_eq`, `ha_cov_lr_nonneg`), strictly when both are strictly increasing
  (`ha_mlrc_integral_pos`);
* the harmonic-mean form of Jensen's inequality, `(E[1/h])⁻¹ ≤ E[h]` for `h > 0`, strict when
  `h` is not constant (`ha_inv_expect_inv_le`, `ha_inv_expect_inv_lt`).

Functions are taken continuous on `ℝ`; only their values on `[y_lo, y_hi]` enter.
-/

namespace Miao.RecursiveContracts

open MeasureTheory

/-- Miao, p. 786: the expectation `E[g] = ∫ g(y) p(y) dy` over the output interval against the
density `p`. -/
noncomputable def ha_expect (ylo yhi : ℝ) (p g : ℝ → ℝ) : ℝ :=
  ∫ y in ylo..yhi, g y * p y

/-- Miao, p. 786: the covariance `Cov(g, h) = E[g h] − E[g] E[h]` under the density `p`. -/
noncomputable def ha_cov (ylo yhi : ℝ) (p g h : ℝ → ℝ) : ℝ :=
  ha_expect ylo yhi p (fun y => g y * h y) - ha_expect ylo yhi p g * ha_expect ylo yhi p h

/-- Miao, p. 786: `E[g h] = Cov(g, h) + E[g] E[h]`. -/
theorem ha_expect_mul_eq_cov_add (ylo yhi : ℝ) (p g h : ℝ → ℝ) :
    ha_expect ylo yhi p (fun y => g y * h y) =
      ha_cov ylo yhi p g h + ha_expect ylo yhi p g * ha_expect ylo yhi p h := by
  unfold ha_cov
  ring

/-- Miao, (22.22), p. 785: the mean value theorem for integrals: if `g` is continuous and `p` is
a continuous density on `[y_lo, y_hi]` (`p ≥ 0`, `∫ p = 1`), then `∫ g p = g(ŷ)` for some
`ŷ ∈ [y_lo, y_hi]`. -/
theorem ha_integral_mean_value {ylo yhi : ℝ} (hle : ylo ≤ yhi) {g p : ℝ → ℝ}
    (hg : Continuous g) (hp : Continuous p) (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ p y)
    (hp1 : ∫ y in ylo..yhi, p y = 1) :
    ∃ yh ∈ Set.Icc ylo yhi, ∫ y in ylo..yhi, g y * p y = g yh := by
  have hK : IsCompact (Set.Icc ylo yhi) := isCompact_Icc
  have hne : (Set.Icc ylo yhi).Nonempty := Set.nonempty_Icc.2 hle
  obtain ⟨y1, hy1, hmin⟩ := hK.exists_isMinOn hne hg.continuousOn
  obtain ⟨y2, hy2, hmax⟩ := hK.exists_isMaxOn hne hg.continuousOn
  have hlo : g y1 ≤ ∫ y in ylo..yhi, g y * p y := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hle
      ((show Continuous fun y => g y1 * p y by fun_prop).intervalIntegrable ylo yhi)
      ((show Continuous fun y => g y * p y by fun_prop).intervalIntegrable ylo yhi)
      (fun y hy => mul_le_mul_of_nonneg_right (hmin hy) (hp0 y hy))
    rwa [intervalIntegral.integral_const_mul, hp1, mul_one] at h
  have hhi : ∫ y in ylo..yhi, g y * p y ≤ g y2 := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hle
      ((show Continuous fun y => g y * p y by fun_prop).intervalIntegrable ylo yhi)
      ((show Continuous fun y => g y2 * p y by fun_prop).intervalIntegrable ylo yhi)
      (fun y hy => mul_le_mul_of_nonneg_right (hmax hy) (hp0 y hy))
    rwa [intervalIntegral.integral_const_mul, hp1, mul_one] at h
  obtain ⟨yh, hyh, heq⟩ := intermediate_value_uIcc hg.continuousOn
    (Set.mem_uIcc.2 (Or.inl ⟨hlo, hhi⟩))
  exact ⟨yh, Set.uIcc_subset_Icc hy1 hy2 hyh, heq.symm⟩

/-- Miao, p. 786 (the step behind "by MLRC … the covariance term is nonnegative"): an increasing
likelihood ratio `r` changes sign once on `[y_lo, y_hi]`. For any `r` there is
`y* ∈ [y_lo, y_hi]` such that below `y*` some later point has `r ≤ 0` (so `r ≤ 0` there when `r` is
increasing) and `r > 0` above `y*`. -/
theorem ha_sign_change {ylo yhi : ℝ} (hle : ylo ≤ yhi) (r : ℝ → ℝ) :
    ∃ ys ∈ Set.Icc ylo yhi,
      (∀ y ∈ Set.Icc ylo yhi, y < ys → ∃ s ∈ Set.Icc ylo yhi, y < s ∧ r s ≤ 0) ∧
      (∀ y ∈ Set.Icc ylo yhi, ys < y → 0 < r y) := by
  set S : Set ℝ := insert ylo {y | y ∈ Set.Icc ylo yhi ∧ r y ≤ 0} with hS
  have hSne : S.Nonempty := ⟨ylo, Set.mem_insert _ _⟩
  have hSbdd : ∀ s ∈ S, s ≤ yhi := by
    intro s hs
    rcases hs with hs | hs
    · rw [hs]
      exact hle
    · exact hs.1.2
  have hbdd : BddAbove S := ⟨yhi, hSbdd⟩
  refine ⟨sSup S, ⟨le_csSup hbdd (Set.mem_insert _ _), csSup_le hSne hSbdd⟩, ?_, ?_⟩
  · intro y hy hlt
    obtain ⟨s, hs, hys⟩ := exists_lt_of_lt_csSup hSne hlt
    rcases hs with hs | hs
    · rw [hs] at hys
      exact absurd hy.1 (not_le.2 hys)
    · exact ⟨s, hs.1, hys, hs.2⟩
  · intro y hy hlt
    by_contra hneg
    have hmem : y ∈ S := Set.mem_insert_of_mem _ ⟨hy, not_lt.1 hneg⟩
    exact absurd (le_csSup hbdd hmem) (not_le.2 hlt)

/-- Miao, p. 786: the MLRC inequality: if `g` is increasing, the likelihood ratio `r = f_a / f`
is increasing (`f_a = r f`, `f ≥ 0` on the output interval) and `∫ f_a = 0`, then
`∫ g f_a ≥ 0`. -/
theorem ha_mlrc_integral_nonneg {ylo yhi : ℝ} (hle : ylo ≤ yhi) {g r p q : ℝ → ℝ}
    (hg : MonotoneOn g (Set.Icc ylo yhi)) (hr : MonotoneOn r (Set.Icc ylo yhi))
    (hq : ∀ y ∈ Set.Icc ylo yhi, q y = r y * p y) (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ p y)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hgc : Continuous g) (hqc : Continuous q) :
    0 ≤ ∫ y in ylo..yhi, g y * q y := by
  obtain ⟨ys, hys, hbelow, habove⟩ := ha_sign_change hle r
  have hpt : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ (g y - g ys) * q y := by
    intro y hy
    rw [hq y hy]
    rcases lt_trichotomy y ys with hlt | heq | hgt
    · obtain ⟨s, hs, hys', hrs⟩ := hbelow y hy hlt
      have hry : r y ≤ 0 := (hr hy hs hys'.le).trans hrs
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hg hy hys hlt.le))
        (mul_nonpos_of_nonpos_of_nonneg hry (hp0 y hy))
    · rw [heq, sub_self, zero_mul]
    · exact mul_nonneg (sub_nonneg.2 (hg hys hy hgt.le))
        (mul_nonneg (habove y hy hgt).le (hp0 y hy))
  have hsplit : ∫ y in ylo..yhi, g y * q y =
      (∫ y in ylo..yhi, (g y - g ys) * q y) + g ys * ∫ y in ylo..yhi, q y := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      ((show Continuous fun y => (g y - g ys) * q y by fun_prop).intervalIntegrable ylo yhi)
      ((show Continuous fun y => g ys * q y by fun_prop).intervalIntegrable ylo yhi)]
    congr 1
    funext y
    ring
  rw [hsplit, hq0, mul_zero, add_zero]
  exact intervalIntegral.integral_nonneg hle hpt

/-- Miao, p. 787 ("contradicting MLRC"): under the strict MLRC, `∫ g f_a > 0` for every strictly
increasing continuous `g` (in particular `g(y) = y`), when `y_lo < y_hi`, `f > 0` on the output
interval and `∫ f_a = 0`. -/
theorem ha_mlrc_integral_pos {ylo yhi : ℝ} (hlt : ylo < yhi) {g r p q : ℝ → ℝ}
    (hg : StrictMonoOn g (Set.Icc ylo yhi)) (hr : StrictMonoOn r (Set.Icc ylo yhi))
    (hq : ∀ y ∈ Set.Icc ylo yhi, q y = r y * p y) (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 < p y)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hgc : Continuous g) (hqc : Continuous q) :
    0 < ∫ y in ylo..yhi, g y * q y := by
  obtain ⟨ys, hys, hbelow, habove⟩ := ha_sign_change hlt.le r
  have hpt : ∀ y ∈ Set.Icc ylo yhi, y ≠ ys → 0 < (g y - g ys) * q y := by
    intro y hy hne
    rw [hq y hy]
    rcases lt_or_gt_of_ne hne with hlt' | hgt
    · obtain ⟨s, hs, hys', hrs⟩ := hbelow y hy hlt'
      have hry : r y < 0 := (hr hy hs hys').trans_le hrs
      exact mul_pos_of_neg_of_neg (sub_neg.2 (hg hy hys hlt'))
        (mul_neg_of_neg_of_pos hry (hp0 y hy))
    · exact mul_pos (sub_pos.2 (hg hys hy hgt)) (mul_pos (habove y hy hgt) (hp0 y hy))
  have hpt0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ (g y - g ys) * q y := by
    intro y hy
    by_cases hne : y = ys
    · rw [hne, sub_self, zero_mul]
    · exact (hpt y hy hne).le
  have hsplit : ∫ y in ylo..yhi, g y * q y =
      (∫ y in ylo..yhi, (g y - g ys) * q y) + g ys * ∫ y in ylo..yhi, q y := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      ((show Continuous fun y => (g y - g ys) * q y by fun_prop).intervalIntegrable ylo yhi)
      ((show Continuous fun y => g ys * q y by fun_prop).intervalIntegrable ylo yhi)]
    congr 1
    funext y
    ring
  rw [hsplit, hq0, mul_zero, add_zero]
  have hex : ∃ c ∈ Set.Icc ylo yhi, 0 < (g c - g ys) * q c := by
    by_cases hne : ylo = ys
    · exact ⟨yhi, ⟨hlt.le, le_rfl⟩, hpt yhi ⟨hlt.le, le_rfl⟩ (by rw [← hne]; exact hlt.ne')⟩
    · exact ⟨ylo, ⟨le_rfl, hlt.le⟩, hpt ylo ⟨le_rfl, hlt.le⟩ hne⟩
  exact intervalIntegral.integral_pos hlt
    ((show Continuous fun y => (g y - g ys) * q y by fun_prop).continuousOn)
    (fun y hy => hpt0 y ⟨hy.1.le, hy.2⟩) hex

/-- Miao, p. 786: `E[f_a / f] = ∫ f_a(y | a) dy` when `f > 0` on the output interval. -/
theorem ha_expect_lr {ylo yhi : ℝ} (hle : ylo ≤ yhi) {p q : ℝ → ℝ}
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) :
    ha_expect ylo yhi p (fun y => q y / p y) = ∫ y in ylo..yhi, q y := by
  unfold ha_expect
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le hle] at hy
  have := (hp y hy).ne'
  field_simp

/-- Miao, p. 786: with `∫ f_a = 0`, `∫ g f_a = E[g · f_a / f] = Cov(g, f_a / f)`, the book's
rewriting of the first term of (22.18). -/
theorem ha_cov_lr_eq {ylo yhi : ℝ} (hle : ylo ≤ yhi) {g p q : ℝ → ℝ}
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hq0 : ∫ y in ylo..yhi, q y = 0) :
    ∫ y in ylo..yhi, g y * q y = ha_cov ylo yhi p g (fun y => q y / p y) := by
  unfold ha_cov
  rw [ha_expect_lr hle hp, hq0, mul_zero, sub_zero]
  unfold ha_expect
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le hle] at hy
  have := (hp y hy).ne'
  simp only
  field_simp

/-- Miao, p. 786: "By MLRC and the monotonicity of `[y − c(v, y) + β P(w(v, y))]`, the above
covariance term is nonnegative": `Cov(g, f_a / f) ≥ 0` for `g` increasing under MLRC, when
`∫ f_a = 0`. -/
theorem ha_cov_lr_nonneg {ylo yhi : ℝ} (hle : ylo ≤ yhi) {g p q : ℝ → ℝ}
    (hg : MonotoneOn g (Set.Icc ylo yhi))
    (hr : MonotoneOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hq0 : ∫ y in ylo..yhi, q y = 0)
    (hgc : Continuous g) (hqc : Continuous q) :
    0 ≤ ha_cov ylo yhi p g (fun y => q y / p y) := by
  rw [← ha_cov_lr_eq hle hp hq0]
  refine ha_mlrc_integral_nonneg hle hg hr (fun y hy => ?_) (fun y hy => (hp y hy).le) hq0 hgc hqc
  have := (hp y hy).ne'
  field_simp

/-- Miao, p. 787 ("It follows from Jensen's inequality"), harmonic-mean form: for a continuous
`h > 0` and a continuous density `p` on the output interval, `(∫ (1/h) p)⁻¹ ≤ ∫ h p`. -/
theorem ha_inv_expect_inv_le {ylo yhi : ℝ} (hle : ylo ≤ yhi) {h p : ℝ → ℝ}
    (hh : Continuous h) (hpos : ∀ y, 0 < h y) (hp : Continuous p)
    (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ p y) (hp1 : ∫ y in ylo..yhi, p y = 1) :
    (∫ y in ylo..yhi, 1 / h y * p y)⁻¹ ≤ ∫ y in ylo..yhi, h y * p y := by
  have hinvc : Continuous fun y => 1 / h y := continuous_const.div hh (fun y => (hpos y).ne')
  obtain ⟨yh, -, hG⟩ := ha_integral_mean_value hle hinvc hp hp0 hp1
  set G := ∫ y in ylo..yhi, 1 / h y * p y with hGdef
  have hGpos : 0 < G := by rw [hG]; exact one_div_pos.2 (hpos yh)
  set t := G⁻¹ with ht
  have hpt : ∀ y ∈ Set.Icc ylo yhi, 2 * t * p y - t ^ 2 * (1 / h y * p y) ≤ h y * p y := by
    intro y hy
    have hhy := hpos y
    have hid : h y * p y - (2 * t * p y - t ^ 2 * (1 / h y * p y)) =
        (h y - t) ^ 2 / h y * p y := by
      field_simp
      ring
    have : 0 ≤ (h y - t) ^ 2 / h y * p y :=
      mul_nonneg (div_nonneg (sq_nonneg _) hhy.le) (hp0 y hy)
    linarith
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hle
    ((show Continuous fun y => 2 * t * p y - t ^ 2 * (1 / h y * p y) by
      fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => h y * p y by fun_prop).intervalIntegrable ylo yhi) hpt
  rw [intervalIntegral.integral_sub
    ((show Continuous fun y => 2 * t * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => t ^ 2 * (1 / h y * p y) by fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hp1, ← hGdef]
    at hmono
  have htG : t * G = 1 := inv_mul_cancel₀ hGpos.ne'
  nlinarith

/-- Miao, p. 787: the strict harmonic-mean Jensen inequality: if moreover `p > 0` on the output
interval, `y_lo < y_hi` and `h` is not constant on it, then `(∫ (1/h) p)⁻¹ < ∫ h p`. -/
theorem ha_inv_expect_inv_lt {ylo yhi : ℝ} (hlt : ylo < yhi) {h p : ℝ → ℝ}
    (hh : Continuous h) (hpos : ∀ y, 0 < h y) (hp : Continuous p)
    (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hnc : ∃ y₁ ∈ Set.Icc ylo yhi, ∃ y₂ ∈ Set.Icc ylo yhi, h y₁ ≠ h y₂) :
    (∫ y in ylo..yhi, 1 / h y * p y)⁻¹ < ∫ y in ylo..yhi, h y * p y := by
  have hinvc : Continuous fun y => 1 / h y := continuous_const.div hh (fun y => (hpos y).ne')
  obtain ⟨yh, -, hG⟩ := ha_integral_mean_value hlt.le hinvc hp (fun y hy => (hp0 y hy).le) hp1
  set G := ∫ y in ylo..yhi, 1 / h y * p y with hGdef
  have hGpos : 0 < G := by rw [hG]; exact one_div_pos.2 (hpos yh)
  set t := G⁻¹ with ht
  have hid : ∀ y, h y * p y - (2 * t * p y - t ^ 2 * (1 / h y * p y)) =
      (h y - t) ^ 2 / h y * p y := by
    intro y
    have hhy := hpos y
    field_simp
    ring
  have hpt : ∀ y ∈ Set.Ioc ylo yhi, 2 * t * p y - t ^ 2 * (1 / h y * p y) ≤ h y * p y := by
    intro y hy
    have : 0 ≤ (h y - t) ^ 2 / h y * p y :=
      mul_nonneg (div_nonneg (sq_nonneg _) (hpos y).le) (hp0 y ⟨hy.1.le, hy.2⟩).le
    linarith [hid y]
  have hex : ∃ c ∈ Set.Icc ylo yhi, 2 * t * p c - t ^ 2 * (1 / h c * p c) < h c * p c := by
    obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := hnc
    have hc : ∃ c ∈ Set.Icc ylo yhi, h c ≠ t := by
      by_cases h1 : h y₁ = t
      · exact ⟨y₂, hy₂, fun h2 => hne (h1.trans h2.symm)⟩
      · exact ⟨y₁, hy₁, h1⟩
    obtain ⟨c, hc, hct⟩ := hc
    refine ⟨c, hc, ?_⟩
    have : 0 < (h c - t) ^ 2 / h c * p c :=
      mul_pos (div_pos (sq_pos_of_ne_zero (sub_ne_zero.2 hct)) (hpos c)) (hp0 c hc)
    linarith [hid c]
  have hstrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hlt
    ((show Continuous fun y => 2 * t * p y - t ^ 2 * (1 / h y * p y) by
      fun_prop).continuousOn)
    ((show Continuous fun y => h y * p y by fun_prop).continuousOn) hpt hex
  rw [intervalIntegral.integral_sub
    ((show Continuous fun y => 2 * t * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => t ^ 2 * (1 / h y * p y) by fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hp1, ← hGdef]
    at hstrict
  have htG : t * G = 1 := inv_mul_cancel₀ hGpos.ne'
  nlinarith

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hidden action: the dynamics of the optimal contract

Miao, §22.2, pp. 785–787: Propositions 22.2.1–22.2.3 and their consequences, for an optimal
contract `(a(v), c(v, ·), w(v, ·))` with multipliers `λ(v)`, `μ(v)` satisfying the first-order
conditions (22.17)–(22.20) of `RecursiveContracts.HAModel` on the output interval
`[y_lo, y_hi]`. At a fixed promised value `v` we write `p = f(· | a(v))`, `q = f_a(· | a(v))`,
`c = c(v, ·)`, `w = w(v, ·)`; `dφ = φ′` and `dP = P′`.

* (22.21), (22.22) and **Proposition 22.2.1** (`eq_22_21`, `eq_22_22`, `proposition_22_2_1`):
  some output `ŷ(v)` has `w(v, ŷ(v)) = v`, and there the agent gets the "first-best" income
  `1/φ′(c(v, ŷ(v))) = λ(v)` (`ha_first_best_income`).
* **Proposition 22.2.2** (`proposition_22_2_2`): `μ(v) > 0` (`ha_mu_pos`), the payment and the
  promised value are strictly increasing in output (`ha_c_strictMonoOn`, `ha_w_strictMonoOn`),
  the differentiated (22.20) and (22.17) (`ha_eq_22_20_deriv`, `ha_eq_22_17_deriv`), `c_y` and
  `w_y` have the same sign (`ha_cy_pos_iff_wy_pos`), and the reward dynamics after `ŷ(v)`
  (`ha_contract_dynamics`).
* **Proposition 22.2.3** (`proposition_22_2_3`, corrected): the inverse Euler equation, its
  inverted form (`ha_inverse_euler_inv`), the martingale property of `P′(v_t)`
  (`ha_marginal_value_martingale`), Jensen's inequality `φ′(c_t) ≤ E_t φ′(c_{t+1})`, strict
  when the next payment schedule is not flat (`ha_jensen`, `ha_jensen_strict`,
  `ha_jensen_strict_of_mu_pos`), and Rogerson's conclusion: the agent would not borrow at the
  gross interest rate `1/β` (`ha_no_borrow`) but would save (`ha_wants_to_save`,
  `ha_rogerson_save`).

Departures (see `docs/HA-corrections.md`): Proposition 22.2.3 integrates against
`f(y′ | a(w(v, y)))`, the effort recommended next period, not `f(y′ | a(v))` as printed
(`ha_proposition_22_2_3_printed_false`); Proposition 22.2.2's strict `c_y > 0`, `w_y > 0` need the
likelihood ratio's derivative to be positive at `y` (otherwise `c_y = 0` can occur:
`ha_cy_eq_zero_of_ry_zero`, `ha_flat_mlrc_density`), and the MLRC is used in its strict form;
"promised `w(v, y) > y`" on p. 787 reads `w(v, y) > v`.
-/

namespace Miao.RecursiveContracts

open MeasureTheory Filter Topology

/-- Miao, p. 785: with `φ′ > 0` strictly decreasing (`φ` strictly concave), `1/φ′` is strictly
increasing. -/
theorem ha_one_div_strictMono {dφ : ℝ → ℝ} (hdφ : StrictAnti dφ) (hpos : ∀ x, 0 < dφ x) :
    StrictMono fun x => 1 / dφ x :=
  fun _ y hxy => one_div_lt_one_div_of_lt (hpos y) (hdφ hxy)

/-! ## Proposition 22.2.1 -/

/-- Miao, (22.21), p. 785: integrating (22.17) against `f(y | a(v))` and using the envelope
condition `P′(v) = −λ(v)`, `∫ f = 1` and `∫ f_a = 0`:
`P′(v) = −∫ f(y | a(v)) / φ′(c(v, y)) dy`. -/
theorem eq_22_21 {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP p q c : ℝ → ℝ} {v lam μ : ℝ}
    (henv : dP v = -lam)
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hpc : Continuous p) (hqc : Continuous q) :
    dP v = -∫ y in ylo..yhi, 1 / dφ (c y) * p y := by
  have hcongr : ∫ y in ylo..yhi, 1 / dφ (c y) * p y = ∫ y in ylo..yhi, (lam * p y + μ * q y) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le hle] at hy
    have := (hp y hy).ne'
    rw [h17 y hy]
    field_simp
  rw [hcongr, intervalIntegral.integral_add
    ((show Continuous fun y => lam * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => μ * q y by fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hp1, hq0, henv]
  ring

/-- Miao, (22.22), p. 785: by the mean value theorem for integrals, `P′(v) = −1/φ′(c(v, ŷ(v)))`
for some output `ŷ(v)`, when `c(v, ·)` and `φ′ > 0` are continuous. -/
theorem eq_22_22 {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP p q c : ℝ → ℝ} {v lam μ : ℝ}
    (henv : dP v = -lam)
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hpc : Continuous p) (hqc : Continuous q)
    (hc : Continuous c) (hdφc : Continuous dφ) (hdφpos : ∀ x, 0 < dφ x) :
    ∃ yh ∈ Set.Icc ylo yhi, dP v = -1 / dφ (c yh) := by
  have hg : Continuous fun y => 1 / dφ (c y) :=
    continuous_const.div (hdφc.comp hc) (fun y => (hdφpos (c y)).ne')
  obtain ⟨yh, hyh, heq⟩ :=
    ha_integral_mean_value hle hg hpc (fun y hy => (hp y hy).le) hp1
  refine ⟨yh, hyh, ?_⟩
  rw [eq_22_21 hle henv h17 hp hp1 hq0 hpc hqc, heq, neg_div]

/-- **Proposition 22.2.1** (Miao, p. 785). For every promised value `v` there is an output level
`ŷ(v)` with `v = w(v, ŷ(v))`. Hypotheses: the envelope condition `P′(v) = −λ(v)`, (22.17) and
(22.20) on the output interval, `P` strictly concave (`P′` strictly decreasing), `φ′ > 0`
continuous, `c(v, ·)` continuous, and `f(· | a(v)) > 0` a continuous density with
`∫ f_a(· | a(v)) = 0`. -/
theorem proposition_22_2_1 {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP p q c w : ℝ → ℝ}
    {v lam μ : ℝ} (henv : dP v = -lam)
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y)) (hdP : StrictAnti dP)
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hpc : Continuous p) (hqc : Continuous q)
    (hc : Continuous c) (hdφc : Continuous dφ) (hdφpos : ∀ x, 0 < dφ x) :
    ∃ yh ∈ Set.Icc ylo yhi, v = w yh := by
  obtain ⟨yh, hyh, h22⟩ := eq_22_22 hle henv h17 hp hp1 hq0 hpc hqc hc hdφc hdφpos
  exact ⟨yh, hyh, hdP.injective (h22.trans (h20 yh hyh).symm)⟩

/-- Miao, p. 787: at the output `ŷ(v)` of Proposition 22.2.1 the agent is paid the "first-best"
income level associated with the multiplier `λ(v)`: `1/φ′(c(v, ŷ(v))) = λ(v)`, and the next
contract is the current one, `w(v, ŷ(v)) = v`. -/
theorem ha_first_best_income {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP p q c w : ℝ → ℝ}
    {v lam μ : ℝ} (henv : dP v = -lam)
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y)) (hdP : StrictAnti dP)
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hpc : Continuous p) (hqc : Continuous q)
    (hc : Continuous c) (hdφc : Continuous dφ) (hdφpos : ∀ x, 0 < dφ x) :
    ∃ yh ∈ Set.Icc ylo yhi, v = w yh ∧ 1 / dφ (c yh) = lam := by
  obtain ⟨yh, hyh, h22⟩ := eq_22_22 hle henv h17 hp hp1 hq0 hpc hqc hc hdφc hdφpos
  refine ⟨yh, hyh, hdP.injective (h22.trans (h20 yh hyh).symm), ?_⟩
  rw [henv, neg_div] at h22
  linarith

/-! ## Proposition 22.2.2 -/

/-- **Proposition 22.2.2** (Miao, pp. 786–787), the multiplier part: `μ(v) > 0`. The book's proof:
if `μ ≤ 0`, then by (22.17), the MLRC and the concavity of `φ`, `c(v, ·)` is decreasing; by
(22.20) and the strict concavity of `P` so is `w(v, ·)`, so `y − c(v, y) + β P(w(v, y))` is
increasing (`P` is decreasing); its covariance with `f_a / f` is then nonnegative, the
agent's second-order condition `soc < 0` makes the second term of (22.18) nonnegative, so both
vanish and `μ = 0`; then `c(v, ·)`, `w(v, ·)` are constant and (22.18) gives `∫ y f_a = 0`,
contradicting the (strict) MLRC. -/
theorem ha_mu_pos {ylo yhi β soc lam μ : ℝ} (hlt : ylo < yhi) (hβ : 0 ≤ β)
    {dφ P dP p q c w : ℝ → ℝ} (hdφ : StrictAnti dφ) (hdφpos : ∀ x, 0 < dφ x)
    (hdP : StrictAnti dP) (hP : Antitone P) (hPc : Continuous P) (hc : Continuous c)
    (hw : Continuous w) (hqc : Continuous q)
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hq0 : ∫ y in ylo..yhi, q y = 0)
    (hmlrc : StrictMonoOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y))
    (h18 : 0 = (∫ y in ylo..yhi, (y - c y + β * P (w y)) * q y) + μ * soc) (hsoc : soc < 0) :
    0 < μ := by
  by_contra hμ'
  have hμ : μ ≤ 0 := not_lt.1 hμ'
  have hΦ := ha_one_div_strictMono hdφ hdφpos
  have hqr : ∀ y ∈ Set.Icc ylo yhi, q y = q y / p y * p y := by
    intro y hy
    have := (hp y hy).ne'
    field_simp
  -- `c(v, ·)` and `w(v, ·)` are decreasing
  have hcanti : ∀ y1 ∈ Set.Icc ylo yhi, ∀ y2 ∈ Set.Icc ylo yhi, y1 ≤ y2 → c y2 ≤ c y1 := by
    intro y1 hy1 y2 hy2 h12
    have hr := hmlrc.monotoneOn hy1 hy2 h12
    have : 1 / dφ (c y2) ≤ 1 / dφ (c y1) := by
      rw [h17 y1 hy1, h17 y2 hy2]
      nlinarith
    exact hΦ.le_iff_le.1 this
  have hwanti : ∀ y1 ∈ Set.Icc ylo yhi, ∀ y2 ∈ Set.Icc ylo yhi, y1 ≤ y2 → w y2 ≤ w y1 := by
    intro y1 hy1 y2 hy2 h12
    have h1 : 1 / dφ (c y2) ≤ 1 / dφ (c y1) := hΦ.monotone (hcanti y1 hy1 y2 hy2 h12)
    have : dP (w y1) ≤ dP (w y2) := by
      rw [h20 y1 hy1, h20 y2 hy2, neg_div, neg_div]
      exact neg_le_neg h1
    exact hdP.le_iff_ge.1 this
  have hgmono : MonotoneOn (fun y => y - c y + β * P (w y)) (Set.Icc ylo yhi) := by
    intro y1 hy1 y2 hy2 h12
    have h1 := hcanti y1 hy1 y2 hy2 h12
    have h2 : P (w y1) ≤ P (w y2) := hP (hwanti y1 hy1 y2 hy2 h12)
    have h3 := mul_le_mul_of_nonneg_left h2 hβ
    simp only
    linarith
  have hnonneg := ha_mlrc_integral_nonneg hlt.le hgmono hmlrc.monotoneOn hqr
    (fun y hy => (hp y hy).le) hq0 (by fun_prop) hqc
  have hμsoc : 0 ≤ μ * soc := mul_nonneg_of_nonpos_of_nonpos hμ hsoc.le
  have hμ0 : μ = 0 := by
    have : μ * soc = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hsoc.ne
  -- with `μ = 0`, `c(v, ·)` and `w(v, ·)` are constant
  have hcconst : ∀ y ∈ Set.Icc ylo yhi, c y = c ylo := by
    intro y hy
    have hylo : ylo ∈ Set.Icc ylo yhi := ⟨le_rfl, hlt.le⟩
    apply hΦ.injective
    change 1 / dφ (c y) = 1 / dφ (c ylo)
    rw [h17 y hy, h17 ylo hylo, hμ0, zero_mul, zero_mul]
  have hwconst : ∀ y ∈ Set.Icc ylo yhi, w y = w ylo := by
    intro y hy
    have hylo : ylo ∈ Set.Icc ylo yhi := ⟨le_rfl, hlt.le⟩
    apply hdP.injective
    rw [h20 y hy, h20 ylo hylo, hcconst y hy]
  set K := c ylo - β * P (w ylo) with hK
  have hcongr : ∫ y in ylo..yhi, (y - c y + β * P (w y)) * q y =
      ∫ y in ylo..yhi, (y * q y - K * q y) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le hlt.le] at hy
    rw [hcconst y hy, hwconst y hy, hK]
    ring
  have hpos := ha_mlrc_integral_pos hlt (g := fun y => y) (strictMono_id.strictMonoOn _) hmlrc
    hqr hp hq0 continuous_id hqc
  rw [hcongr, intervalIntegral.integral_sub
    ((show Continuous fun y => y * q y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => K * q y by fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul, hq0, hμ0] at h18
  linarith

/-- Miao, p. 787 (consequence of Proposition 22.2.2 and (22.17)): with `μ(v) > 0` and the strict
MLRC, the payment `c(v, ·)` is strictly increasing in output. -/
theorem ha_c_strictMonoOn {ylo yhi lam μ : ℝ} {dφ p q c : ℝ → ℝ} (hdφ : StrictAnti dφ)
    (hdφpos : ∀ x, 0 < dφ x) (hμ : 0 < μ)
    (hmlrc : StrictMonoOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y)) :
    StrictMonoOn c (Set.Icc ylo yhi) := by
  intro y1 hy1 y2 hy2 h12
  have hr := hmlrc hy1 hy2 h12
  have : 1 / dφ (c y1) < 1 / dφ (c y2) := by
    rw [h17 y1 hy1, h17 y2 hy2]
    exact add_lt_add_right (mul_lt_mul_of_pos_left hr hμ) lam
  exact (ha_one_div_strictMono hdφ hdφpos).lt_iff_lt.1 this

/-- Miao, p. 787 (consequence of Proposition 22.2.2 and (22.20)): with `μ(v) > 0` and the strict
MLRC, the promised value `w(v, ·)` is strictly increasing in output. -/
theorem ha_w_strictMonoOn {ylo yhi lam μ : ℝ} {dφ dP p q c w : ℝ → ℝ} (hdφ : StrictAnti dφ)
    (hdφpos : ∀ x, 0 < dφ x) (hdP : StrictAnti dP) (hμ : 0 < μ)
    (hmlrc : StrictMonoOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y)) :
    StrictMonoOn w (Set.Icc ylo yhi) := by
  intro y1 hy1 y2 hy2 h12
  have hc := ha_c_strictMonoOn hdφ hdφpos hμ hmlrc h17 hy1 hy2 h12
  have h1 : 1 / dφ (c y1) < 1 / dφ (c y2) := ha_one_div_strictMono hdφ hdφpos hc
  have : dP (w y2) < dP (w y1) := by
    rw [h20 y1 hy1, h20 y2 hy2, neg_div, neg_div]
    exact neg_lt_neg h1
  exact hdP.lt_iff_gt.1 this

/-- Miao, p. 786 (first display of the proof of Proposition 22.2.2): differentiating (22.20) in
output, `P″(w(v, y)) w_y(v, y) = φ″(c(v, y)) / φ′(c(v, y))² · c_y(v, y)`. -/
theorem ha_eq_22_20_deriv {dφ dP c w : ℝ → ℝ} {y cy wy ddφ ddP : ℝ}
    (hc : HasDerivAt c cy y) (hw : HasDerivAt w wy y) (hdφd : HasDerivAt dφ ddφ (c y))
    (hdPd : HasDerivAt dP ddP (w y)) (hne : dφ (c y) ≠ 0)
    (h20 : ∀ᶠ y' in 𝓝 y, dP (w y') = -1 / dφ (c y')) :
    ddP * wy = ddφ / dφ (c y) ^ 2 * cy := by
  have h1 : HasDerivAt (fun y' => dP (w y')) (ddP * wy) y := hdPd.comp y hw
  have h2 : HasDerivAt (fun y' => -1 / dφ (c y'))
      ((0 * dφ (c y) - -1 * (ddφ * cy)) / dφ (c y) ^ 2) y :=
    (hasDerivAt_const y (-1 : ℝ)).div (hdφd.comp y hc) hne
  rw [h1.unique (h2.congr_of_eventuallyEq h20)]
  field_simp
  ring

/-- Miao, p. 786 ("By (22.17) and concavity of `φ`"): differentiating (22.17) in output,
`−φ″(c(v, y)) / φ′(c(v, y))² · c_y(v, y) = μ(v) r_y(y)` for the likelihood ratio
`r = f_a / f`. -/
theorem ha_eq_22_17_deriv {dφ c r : ℝ → ℝ} {y cy ry ddφ lam μ : ℝ}
    (hc : HasDerivAt c cy y) (hr : HasDerivAt r ry y) (hdφd : HasDerivAt dφ ddφ (c y))
    (hne : dφ (c y) ≠ 0) (h17 : ∀ᶠ y' in 𝓝 y, 1 / dφ (c y') = lam + μ * r y') :
    -ddφ / dφ (c y) ^ 2 * cy = μ * ry := by
  have h1 : HasDerivAt (fun y' => lam + μ * r y') (μ * ry) y := (hr.const_mul μ).const_add lam
  have h2 : HasDerivAt (fun y' => 1 / dφ (c y'))
      ((0 * dφ (c y) - 1 * (ddφ * cy)) / dφ (c y) ^ 2) y :=
    (hasDerivAt_const y (1 : ℝ)).div (hdφd.comp y hc) hne
  rw [(h1.congr_of_eventuallyEq h17).unique h2]
  field_simp
  ring

/-- Miao, p. 786: "Since `P` and `φ` are strictly concave, `c_y` and `w_y` have the same sign"
(`P″ < 0`, `φ″ < 0`). -/
theorem ha_cy_pos_iff_wy_pos {dφ dP c w : ℝ → ℝ} {y cy wy ddφ ddP : ℝ}
    (hc : HasDerivAt c cy y) (hw : HasDerivAt w wy y) (hdφd : HasDerivAt dφ ddφ (c y))
    (hdPd : HasDerivAt dP ddP (w y)) (hne : dφ (c y) ≠ 0)
    (h20 : ∀ᶠ y' in 𝓝 y, dP (w y') = -1 / dφ (c y')) (hddφ : ddφ < 0) (hddP : ddP < 0) :
    (0 < cy ↔ 0 < wy) := by
  have heq := ha_eq_22_20_deriv hc hw hdφd hdPd hne h20
  have hk : ddφ / dφ (c y) ^ 2 < 0 := div_neg_of_neg_of_pos hddφ (by positivity)
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **Proposition 22.2.2** (Miao, p. 786), corrected. Suppose `c(v, ·)`, `w(v, ·)` and the
likelihood ratio `r = f_a / f` are differentiable at an interior output `y`, `φ″ < 0`,
`P″ < 0` there and, in addition to the book's hypotheses, `r_y(y) > 0`. Then `μ(v) > 0`,
`c_y(v, y) > 0` and `w_y(v, y) > 0`. (With only the strict MLRC, `r_y(y) = 0` is possible and
then `c_y(v, y) = w_y(v, y) = 0`: `ha_cy_eq_zero_of_ry_zero`, `ha_flat_mlrc_density`.) -/
theorem proposition_22_2_2 {ylo yhi β soc lam μ : ℝ} (hlt : ylo < yhi) (hβ : 0 ≤ β)
    {dφ P dP p q c w : ℝ → ℝ} (hdφ : StrictAnti dφ) (hdφpos : ∀ x, 0 < dφ x)
    (hdP : StrictAnti dP) (hP : Antitone P) (hPc : Continuous P) (hc : Continuous c)
    (hw : Continuous w) (hqc : Continuous q)
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hq0 : ∫ y in ylo..yhi, q y = 0)
    (hmlrc : StrictMonoOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y))
    (h18 : 0 = (∫ y in ylo..yhi, (y - c y + β * P (w y)) * q y) + μ * soc) (hsoc : soc < 0)
    {y cy wy ry ddφ ddP : ℝ} (hy : y ∈ Set.Ioo ylo yhi) (hcd : HasDerivAt c cy y)
    (hwd : HasDerivAt w wy y) (hrd : HasDerivAt (fun y' => q y' / p y') ry y)
    (hdφd : HasDerivAt dφ ddφ (c y)) (hdPd : HasDerivAt dP ddP (w y)) (hddφ : ddφ < 0)
    (hddP : ddP < 0) (hry : 0 < ry) :
    0 < μ ∧ 0 < cy ∧ 0 < wy := by
  have hμ := ha_mu_pos hlt hβ hdφ hdφpos hdP hP hPc hc hw hqc hp hq0 hmlrc h17 h20 h18 hsoc
  have hnhds : Set.Icc ylo yhi ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
  have h17e : ∀ᶠ y' in 𝓝 y, 1 / dφ (c y') = lam + μ * (q y' / p y') :=
    Filter.eventually_of_mem hnhds h17
  have h20e : ∀ᶠ y' in 𝓝 y, dP (w y') = -1 / dφ (c y') := Filter.eventually_of_mem hnhds h20
  have hne : dφ (c y) ≠ 0 := (hdφpos (c y)).ne'
  have hform := ha_eq_22_17_deriv (r := fun y' => q y' / p y') hcd hrd hdφd hne h17e
  have hk : 0 < -ddφ / dφ (c y) ^ 2 := div_pos (neg_pos.2 hddφ) (by positivity)
  have hcy : 0 < cy := by
    by_contra hcy
    have : -ddφ / dφ (c y) ^ 2 * cy ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (not_lt.1 hcy)
    nlinarith [mul_pos hμ hry]
  exact ⟨hμ, hcy, (ha_cy_pos_iff_wy_pos hcd hwd hdφd hdPd hne h20e hddφ hddP).1 hcy⟩

/-- Miao, p. 786, the correction to Proposition 22.2.2: by the differentiated (22.17), at an
output where the likelihood ratio has `r_y = 0` the payment has `c_y = 0`, whatever `μ(v)`. -/
theorem ha_cy_eq_zero_of_ry_zero {dφ c r : ℝ → ℝ} {y cy ddφ lam μ : ℝ}
    (hc : HasDerivAt c cy y) (hr : HasDerivAt r 0 y) (hdφd : HasDerivAt dφ ddφ (c y))
    (hne : dφ (c y) ≠ 0) (hddφ : ddφ ≠ 0) (h17 : ∀ᶠ y' in 𝓝 y, 1 / dφ (c y') = lam + μ * r y') :
    cy = 0 := by
  have h := ha_eq_22_17_deriv hc hr hdφd hne h17
  rw [mul_zero] at h
  have hk : -ddφ / dφ (c y) ^ 2 ≠ 0 := div_ne_zero (neg_ne_zero.2 hddφ) (by positivity)
  exact (mul_eq_zero.1 h).resolve_left hk

/-- Miao, p. 786, counterexample to the strict `c_y > 0` of Proposition 22.2.2 under the strict
MLRC alone: the densities `f(y | a) = 1 + a (y − 1/2)³` on `[0, 1]`, `|a| ≤ 1`, are positive and
integrate to one, `f_a(y | a) = (y − 1/2)³` (they are linear in `a`,
`ha_linearDensity_hasDerivAt`), and the likelihood ratio `r = f_a / f` is strictly increasing
on `[0, 1]` with `r_y(1/2) = 0`; by `ha_cy_eq_zero_of_ry_zero`, `c_y(v, 1/2) = 0`. -/
theorem ha_flat_mlrc_density {a : ℝ} (ha : |a| ≤ 1) :
    (∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + a * (y - 1 / 2) ^ 3) ∧
    (∫ y in (0 : ℝ)..1, (1 + a * (y - 1 / 2) ^ 3)) = 1 ∧
    StrictMonoOn (fun y => (y - 1 / 2) ^ 3 / (1 + a * (y - 1 / 2) ^ 3)) (Set.Icc 0 1) ∧
    HasDerivAt (fun y => (y - 1 / 2) ^ 3 / (1 + a * (y - 1 / 2) ^ 3)) 0 (1 / 2) := by
  have hpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + a * (y - 1 / 2) ^ 3 := by
    intro y hy
    have hz : |y - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hb : |a * (y - 1 / 2) ^ 3| ≤ 1 / 8 := by
      rw [abs_mul, abs_pow]
      calc |a| * |y - 1 / 2| ^ 3 ≤ 1 * (1 / 2) ^ 3 :=
            mul_le_mul ha (pow_le_pow_left₀ (abs_nonneg _) hz 3) (by positivity) zero_le_one
        _ = 1 / 8 := by norm_num
    linarith [neg_abs_le (a * (y - 1 / 2) ^ 3)]
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rw [intervalIntegral.integral_add intervalIntegrable_const
      ((show Continuous fun y : ℝ => a * (y - 1 / 2) ^ 3 by fun_prop).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ 3) (1 / 2), integral_pow]
    norm_num
  · intro s hs t ht hst
    have h3 : (s - 1 / 2) ^ 3 < (t - 1 / 2) ^ 3 :=
      (Odd.strictMono_pow (by decide : Odd 3)) (by linarith)
    rw [div_lt_div_iff₀ (hpos s hs) (hpos t ht)]
    nlinarith
  · have hN : HasDerivAt (fun y : ℝ => (y - 1 / 2) ^ 3)
        ((3 : ℕ) * ((1 : ℝ) / 2 - 1 / 2) ^ (3 - 1) * 1) (1 / 2) :=
      ((hasDerivAt_id (1 / 2 : ℝ)).sub_const (1 / 2)).pow 3
    have hD : HasDerivAt (fun y : ℝ => 1 + a * (y - 1 / 2) ^ 3)
        (a * ((3 : ℕ) * ((1 : ℝ) / 2 - 1 / 2) ^ (3 - 1) * 1)) (1 / 2) :=
      (hN.const_mul a).const_add 1
    have hne : (1 : ℝ) + a * (1 / 2 - 1 / 2) ^ 3 ≠ 0 := by norm_num
    exact (hN.div hD hne).congr_deriv (by norm_num)

/-- Miao, p. 787: the dynamics after observing output `y`: with `μ(v) > 0` and the strict MLRC, if
`y > ŷ(v)` the agent is paid more than the "first-best" income `c(v, ŷ(v))` and promised more
than `v` (the book prints "`w(v, y) > y`"); if `y < ŷ(v)`, less and less. -/
theorem ha_contract_dynamics {ylo yhi lam μ v yh : ℝ} {dφ dP p q c w : ℝ → ℝ}
    (hdφ : StrictAnti dφ) (hdφpos : ∀ x, 0 < dφ x) (hdP : StrictAnti dP) (hμ : 0 < μ)
    (hmlrc : StrictMonoOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y)) (hyh : yh ∈ Set.Icc ylo yhi)
    (hv : v = w yh) :
    ∀ y ∈ Set.Icc ylo yhi, (yh < y → c yh < c y ∧ v < w y) ∧ (y < yh → c y < c yh ∧ w y < v) := by
  intro y hy
  have hc := ha_c_strictMonoOn hdφ hdφpos hμ hmlrc h17
  have hw := ha_w_strictMonoOn hdφ hdφpos hdP hμ hmlrc h17 h20
  rw [hv]
  exact ⟨fun h => ⟨hc hyh hy h, hw hyh hy h⟩, fun h => ⟨hc hy hyh h, hw hy hyh h⟩⟩

/-! ## Proposition 22.2.3: the inverse Euler equation -/

/-- **Proposition 22.2.3** (Inverse Euler equation, Miao, p. 787), corrected:
`1/φ′(c(v, y)) = ∫ 1/φ′(c(w(v, y), y′)) f(y′ | a(w(v, y))) dy′`. The proof: (22.21) at the
promised value `w(v, y)` combined with (22.20). The density integrated against is that of
next period's recommended effort `a(w(v, y))`; the book prints `f(y′ | a(v))`
(`ha_proposition_22_2_3_printed_false`). Hypotheses hold at every promised value: the envelope
condition, (22.17), (22.20), and `f(· | a(v)) > 0` continuous densities with
`∫ f_a(· | a(v)) = 0`. -/
theorem proposition_22_2_3 {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi) :
    1 / dφ (c v y) = ∫ y' in ylo..yhi, 1 / dφ (c (w v y) y') * f (a (w v y)) y' := by
  have h21 := eq_22_21 hle (henv (w v y)) (h17 (w v y)) (hf (w v y)) (hf1 (w v y)) (hfa0 (w v y))
    (hfc (w v y)) (hfac (w v y))
  rw [h20 v y hy, neg_div] at h21
  exact neg_inj.1 h21

/-- Miao, p. 787 ("By this proposition"): the inverse Euler equation inverted,
`φ′(c(v, y)) = (∫ 1/φ′(c(w(v, y), y′)) f(y′ | a(w(v, y))) dy′)⁻¹`. -/
theorem ha_inverse_euler_inv {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi) :
    dφ (c v y) = (∫ y' in ylo..yhi, 1 / dφ (c (w v y) y') * f (a (w v y)) y')⁻¹ := by
  rw [← proposition_22_2_3 hle henv h17 h20 hf hf1 hfa0 hfc hfac v y hy, one_div, inv_inv]

/-- Miao, pp. 785–787 (the step shared by Propositions 22.2.1 and 22.2.3): the marginal value
`P′(v_t)` of the promised value is a martingale,
`P′(v) = ∫ P′(w(v, y)) f(y | a(v)) dy`, from (22.20) and (22.21). -/
theorem ha_marginal_value_martingale {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP p q c w : ℝ → ℝ}
    {v lam μ : ℝ} (henv : dP v = -lam)
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y))
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hpc : Continuous p) (hqc : Continuous q) :
    dP v = ∫ y in ylo..yhi, dP (w y) * p y := by
  rw [eq_22_21 hle henv h17 hp hp1 hq0 hpc hqc, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le hle] at hy
  rw [h20 y hy, neg_div, neg_mul]

/-- Miao, p. 787 ("It follows from Jensen's inequality"): `φ′(c(v, y)) ≤ E φ′(c(w(v, y), y′))`,
the expectation under next period's density `f(· | a(w(v, y)))`, for `φ′ > 0` continuous and
continuous payment schedules. -/
theorem ha_jensen {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (hc : ∀ v, Continuous (c v)) (hdφc : Continuous dφ)
    (hdφpos : ∀ x, 0 < dφ x) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi) :
    dφ (c v y) ≤ ∫ y' in ylo..yhi, dφ (c (w v y) y') * f (a (w v y)) y' := by
  rw [ha_inverse_euler_inv hle henv h17 h20 hf hf1 hfa0 hfc hfac v y hy]
  exact ha_inv_expect_inv_le hle (hdφc.comp (hc (w v y))) (fun y' => hdφpos _) (hfc (w v y))
    (fun y' hy' => (hf (w v y) y' hy').le) (hf1 (w v y))

/-- Miao, p. 787: the strict inequality `φ′(c(v, y)) < E φ′(c(w(v, y), y′))` printed in the book
holds when next period's payment schedule `c(w(v, y), ·)` is not constant on the output
interval (and `φ′` is strictly decreasing). -/
theorem ha_jensen_strict {ylo yhi : ℝ} (hlt : ylo < yhi) {dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (hc : ∀ v, Continuous (c v)) (hdφc : Continuous dφ)
    (hdφpos : ∀ x, 0 < dφ x) (hdφ : StrictAnti dφ) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi)
    (hnc : ∃ y₁ ∈ Set.Icc ylo yhi, ∃ y₂ ∈ Set.Icc ylo yhi, c (w v y) y₁ ≠ c (w v y) y₂) :
    dφ (c v y) < ∫ y' in ylo..yhi, dφ (c (w v y) y') * f (a (w v y)) y' := by
  rw [ha_inverse_euler_inv hlt.le henv h17 h20 hf hf1 hfa0 hfc hfac v y hy]
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := hnc
  exact ha_inv_expect_inv_lt hlt (hdφc.comp (hc (w v y))) (fun y' => hdφpos _) (hfc (w v y))
    (hf (w v y)) (hf1 (w v y)) ⟨y₁, hy₁, y₂, hy₂, fun h => hne (hdφ.injective h)⟩

/-- Miao, p. 787: the strict Jensen inequality holds in the model: if next period's multiplier
`μ(w(v, y))` is positive (Proposition 22.2.2) and the MLRC holds strictly at `a(w(v, y))`, then
`c(w(v, y), ·)` is strictly increasing, hence not constant, so
`φ′(c(v, y)) < E φ′(c(w(v, y), y′))`. -/
theorem ha_jensen_strict_of_mu_pos {ylo yhi : ℝ} (hlt : ylo < yhi) {dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (hc : ∀ v, Continuous (c v)) (hdφc : Continuous dφ)
    (hdφpos : ∀ x, 0 < dφ x) (hdφ : StrictAnti dφ) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi)
    (hμ : 0 < μ (w v y))
    (hmlrc : StrictMonoOn (fun y' => fa (a (w v y)) y' / f (a (w v y)) y') (Set.Icc ylo yhi)) :
    dφ (c v y) < ∫ y' in ylo..yhi, dφ (c (w v y) y') * f (a (w v y)) y' := by
  have hmono := ha_c_strictMonoOn hdφ hdφpos hμ hmlrc (h17 (w v y))
  refine ha_jensen_strict hlt henv h17 h20 hf hf1 hfa0 hfc hfac hc hdφc hdφpos hdφ v y hy
    ⟨ylo, ⟨le_rfl, hlt.le⟩, yhi, ⟨hlt.le, le_rfl⟩, ?_⟩
  exact (hmono ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt).ne

/-! ## Rogerson's saving implication -/

/-- Miao, p. 787 (the concavity step behind the saving implication): for `φ` with strictly
decreasing derivative `φ′` and `x < z`, the strict tangent inequalities
`φ′(z) (z − x) < φ(z) − φ(x) < φ′(x) (z − x)`. -/
theorem ha_tangent_lt {φ dφ : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : StrictAnti dφ)
    {x z : ℝ} (hxz : x < z) :
    dφ z * (z - x) < φ z - φ x ∧ φ z - φ x < dφ x * (z - x) := by
  have hcont : ContinuousOn φ (Set.Icc x z) :=
    fun t _ => (hφ t).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope φ dφ hxz hcont (fun t _ => hφ t)
  have hpos : 0 < z - x := sub_pos.2 hxz
  have heq : φ z - φ x = dφ ξ * (z - x) := by
    rw [hslope]
    field_simp
  rw [heq]
  exact ⟨mul_lt_mul_of_pos_right (hdφ hξ.2) hpos, mul_lt_mul_of_pos_right (hdφ hξ.1) hpos⟩

/-- Miao, p. 787: "the agent would not wish to borrow money at the gross interest rate `1/β`".
If `φ′(c₀) ≤ E φ′(c′)` (Jensen's inequality above, with today's payment `c₀ = c(v, y)`, next
period's schedule `c′ = c(w(v, y), ·)` and density `p = f(· | a(w(v, y)))`), then borrowing
any `b > 0` today and repaying `b/β` tomorrow strictly lowers the agent's utility
`φ(c₀) + β E φ(c′)`, efforts held fixed. -/
theorem ha_no_borrow {ylo yhi β c₀ b : ℝ} (hle : ylo ≤ yhi) (hβ : 0 < β) (hb : 0 < b)
    {φ dφ c' p : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : StrictAnti dφ)
    (hdφc : Continuous dφ) (hc' : Continuous c') (hp : Continuous p)
    (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ p y)
    (heuler : dφ c₀ ≤ ∫ y in ylo..yhi, dφ (c' y) * p y) :
    φ (c₀ + b) + β * ∫ y in ylo..yhi, φ (c' y - b / β) * p y <
      φ c₀ + β * ∫ y in ylo..yhi, φ (c' y) * p y := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  have h1 := (ha_tangent_lt hφ hdφ (show c₀ < c₀ + b by linarith)).2
  rw [add_sub_cancel_left] at h1
  have hbβ : 0 < b / β := div_pos hb hβ
  have hpt : ∀ y ∈ Set.Icc ylo yhi,
      φ (c' y - b / β) * p y ≤ φ (c' y) * p y - b / β * (dφ (c' y) * p y) := by
    intro y hy
    have h2 := (ha_tangent_lt hφ hdφ (show c' y - b / β < c' y by linarith)).1
    rw [sub_sub_cancel] at h2
    nlinarith [hp0 y hy]
  have hint := intervalIntegral.integral_mono_on (μ := volume) hle
    ((show Continuous fun y => φ (c' y - b / β) * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => φ (c' y) * p y - b / β * (dφ (c' y) * p y) by
      fun_prop).intervalIntegrable ylo yhi) hpt
  rw [intervalIntegral.integral_sub
    ((show Continuous fun y => φ (c' y) * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => b / β * (dφ (c' y) * p y) by fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul] at hint
  have h3 := mul_le_mul_of_nonneg_left hint hβ.le
  have h4 : β * (b / β) = b := by field_simp
  rw [mul_sub, ← mul_assoc, h4] at h3
  have h5 := mul_le_mul_of_nonneg_left heuler hb.le
  linarith

/-- Miao, p. 787: "but the agent would wish to save money" (Rogerson 1985a). If
`φ′(c₀) < E φ′(c′)` (the strict Jensen inequality), then saving some `s > 0` today at the gross
interest rate `1/β` strictly raises the agent's utility `φ(c₀) + β E φ(c′)`, efforts held fixed. -/
theorem ha_wants_to_save {ylo yhi β c₀ : ℝ} (hle : ylo ≤ yhi) (hβ : 0 < β)
    {φ dφ c' p : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : StrictAnti dφ)
    (hdφc : Continuous dφ) (hc' : Continuous c') (hp : Continuous p)
    (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ p y)
    (heuler : dφ c₀ < ∫ y in ylo..yhi, dφ (c' y) * p y) :
    ∃ s > 0, φ c₀ + β * ∫ y in ylo..yhi, φ (c' y) * p y <
      φ (c₀ - s) + β * ∫ y in ylo..yhi, φ (c' y + s / β) * p y := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  set F : ℝ → ℝ := fun s => (∫ y in ylo..yhi, dφ (c' y + s / β) * p y) - dφ (c₀ - s) with hF
  have hJ : Continuous fun z : ℝ × ℝ => dφ (c' z.2 + z.1 / β) * p z.2 := by fun_prop
  have hFc : Continuous F :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun s y => dφ (c' y + s / β) * p y) hJ ylo yhi).sub (by fun_prop)
  have hF0 : 0 < F 0 := by
    simp only [hF, zero_div, add_zero, sub_zero]
    linarith
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < F s := hFc.continuousAt.eventually (eventually_gt_nhds hF0)
  obtain ⟨s, hFs, hs⟩ : ∃ s, 0 < F s ∧ 0 < s :=
    ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  refine ⟨s, hs, ?_⟩
  have h1 := (ha_tangent_lt hφ hdφ (show c₀ - s < c₀ by linarith)).2
  rw [sub_sub_cancel] at h1
  have hsβ : 0 < s / β := div_pos hs hβ
  have hpt : ∀ y ∈ Set.Icc ylo yhi,
      φ (c' y) * p y + s / β * (dφ (c' y + s / β) * p y) ≤ φ (c' y + s / β) * p y := by
    intro y hy
    have h2 := (ha_tangent_lt hφ hdφ (show c' y < c' y + s / β by linarith)).1
    rw [add_sub_cancel_left] at h2
    nlinarith [hp0 y hy]
  have hint := intervalIntegral.integral_mono_on (μ := volume) hle
    ((show Continuous fun y => φ (c' y) * p y + s / β * (dφ (c' y + s / β) * p y) by
      fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => φ (c' y + s / β) * p y by fun_prop).intervalIntegrable ylo yhi) hpt
  rw [intervalIntegral.integral_add
    ((show Continuous fun y => φ (c' y) * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => s / β * (dφ (c' y + s / β) * p y) by
      fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul] at hint
  have h3 := mul_le_mul_of_nonneg_left hint hβ.le
  have h4 : β * (s / β) = s := by field_simp
  rw [mul_add, ← mul_assoc, h4] at h3
  have hFs' : dφ (c₀ - s) < ∫ y in ylo..yhi, dφ (c' y + s / β) * p y := by
    simp only [hF] at hFs
    linarith
  have h5 := mul_lt_mul_of_pos_left hFs' hs
  linarith

/-- Miao, p. 787, Rogerson's result in the model: when next period's multiplier `μ(w(v, y))` is
positive and the MLRC holds strictly there, the agent, paid `c(v, y)` today and facing the
schedule `c(w(v, y), ·)` tomorrow, would gain from saving some `s > 0` at the gross interest
rate `1/β`. -/
theorem ha_rogerson_save {ylo yhi β : ℝ} (hlt : ylo < yhi) (hβ : 0 < β) {φ dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (hc : ∀ v, Continuous (c v))
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφc : Continuous dφ) (hdφpos : ∀ x, 0 < dφ x)
    (hdφ : StrictAnti dφ) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi) (hμ : 0 < μ (w v y))
    (hmlrc : StrictMonoOn (fun y' => fa (a (w v y)) y' / f (a (w v y)) y') (Set.Icc ylo yhi)) :
    ∃ s > 0, φ (c v y) + β * ∫ y' in ylo..yhi, φ (c (w v y) y') * f (a (w v y)) y' <
      φ (c v y - s) + β * ∫ y' in ylo..yhi, φ (c (w v y) y' + s / β) * f (a (w v y)) y' :=
  ha_wants_to_save hlt.le hβ hφ hdφ hdφc (hc (w v y)) (hfc (w v y))
    (fun y' hy' => (hf (w v y) y' hy').le)
    (ha_jensen_strict_of_mu_pos hlt henv h17 h20 hf hf1 hfa0 hfc hfac hc hdφc hdφpos hdφ v y hy
      hμ hmlrc)

/-- Miao, p. 787, counterexample to Proposition 22.2.3 as printed (integrating against
`f(y′ | a(v))`). Take outputs in `[0, 1]`, the densities `f(y | a) = 1 + a (2y − 1)` (positive
for `|a| < 1`, integrating to one, with increasing likelihood ratio), and next period's
schedule with `1/φ′(c(w(v, y), y′)) = y′` (e.g. `φ = log`, `c(w(v, y), y′) = y′`). Then
`∫ y′ f(y′ | a) dy′ = 1/2 + a/6`, so the corrected right side (with `a = a(w(v, y))`) and the
printed one (with `a = a(v)`) differ whenever the recommended effort changes,
`a(w(v, y)) ≠ a(v)`: both cannot equal `1/φ′(c(v, y))`. -/
theorem ha_proposition_22_2_3_printed_false {a₀ a₁ : ℝ} (hne : a₀ ≠ a₁) :
    (∫ y in (0 : ℝ)..1, y * (1 + a₁ * (2 * y - 1))) ≠
      ∫ y in (0 : ℝ)..1, y * (1 + a₀ * (2 * y - 1)) := by
  have key : ∀ a : ℝ, ∫ y in (0 : ℝ)..1, y * (1 + a * (2 * y - 1)) = 1 / 2 + a / 6 := by
    intro a
    have hrw : (fun y : ℝ => y * (1 + a * (2 * y - 1))) = fun y => (1 - a) * y + 2 * a * y ^ 2 := by
      funext y
      ring
    rw [hrw, intervalIntegral.integral_add
      ((show Continuous fun y : ℝ => (1 - a) * y by fun_prop).intervalIntegrable 0 1)
      ((show Continuous fun y : ℝ => 2 * a * y ^ 2 by fun_prop).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
      integral_pow]
    ring
  rw [key, key]
  intro h
  exact hne (by linarith)

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hidden information: the model and the incentive constraints

Miao, §22.3, pp. 788–791: the Thomas–Worrall (1990) model. The agent's income `yₜ` is iid on
`Θ = {θ₁ < ⋯ < θₙ}` with `Pr(yₜ = θᵢ) = πᵢ` and is privately observed; the agent cannot save,
the principal is risk neutral, both discount with `β ∈ (0, 1)`. A one-period contract at
promised value `v` is a list `(cᵢ, wᵢ)` of transfers and continuation values.

* `HIModel`: the primitives. The index set is `Fin (N + 1)` (so `n = N + 1 ≥ 1`), `θ` is strictly
  increasing, the probabilities `prob` (the book's `πᵢ`; `π` is reserved) are positive and sum
  to one. The utility `u` is defined on all of `ℝ` (the book's `a = −∞`, as for the CARA utility
  of Exercise 22.4), continuous, strictly increasing, strictly concave, bounded above and
  unbounded below (the part of Assumption 22.3.1 used for the Bellman equation; the derivative
  conditions are in `HIAssumption`).
* `hi_C` is `Cᵢⱼ` of (22.24), `hi_IC` the incentive constraints, `hi_agentValue` the left side of
  the promise-keeping constraint (22.25), `hi_vmax = sup u / (1 − β)`, `hi_Feasible`.
* `lemma_22_3_1` (Lemma 22.3.1): incentive constraints imply `cᵢ₋₁ ≥ cᵢ`, `wᵢ₋₁ ≤ wᵢ`; it is
  proved from the two local constraints alone (`hi_local_mono`), as the book's proof does.
* `lemma_22_3_2` (Lemma 22.3.2): the local downward and upward constraints imply all constraints.
* `hi_upward_of_binding`: a binding local downward constraint with `cᵢ ≤ cᵢ₋₁` implies the local
  upward constraint (used in the proofs of Propositions 22.3.1 and 22.3.2).
* `hi_C_shift`, `hi_agentValue_shift`: shifting every `wᵢ` by `k` keeps every `Cᵢⱼ` and raises
  the agent's value by `βk` (the intuition for the martingale property, p. 796).
* `hi_cara`, `hi_caraModel`, `hi_exampleModel`: the CARA utility `−exp(−γc)` gives a model; a
  concrete two-state instance shows the hypotheses are satisfiable.
-/

namespace Miao.RecursiveContracts

open Finset

/-- The primitives of the hidden-information model of Miao, §22.3, pp. 788–789. The income
states are `Fin (N + 1)`; `prob i` is the book's `πᵢ`. -/
structure HIModel where
  /-- `n − 1`, so that there are `N + 1 ≥ 1` income states. -/
  N : ℕ
  /-- Income levels `θ₁ < ⋯ < θₙ`. -/
  θ : Fin (N + 1) → ℝ
  /-- The probabilities `πᵢ`. -/
  prob : Fin (N + 1) → ℝ
  /-- The common discount factor. -/
  β : ℝ
  /-- The agent's period utility. -/
  u : ℝ → ℝ
  θ_strictMono : StrictMono θ
  prob_pos : ∀ i, 0 < prob i
  prob_sum : ∑ i, prob i = 1
  β_pos : 0 < β
  β_lt_one : β < 1
  u_cont : Continuous u
  u_strictMono : StrictMono u
  u_strictConcave : StrictConcaveOn ℝ Set.univ u
  u_bddAbove : BddAbove (Set.range u)
  u_not_bddBelow : ¬ BddBelow (Set.range u)

/-- Miao, (22.24), p. 789: `Cᵢⱼ = u(θᵢ + cᵢ) + βwᵢ − [u(θᵢ + cⱼ) + βwⱼ]`, the gain of type `i`
from telling the truth rather than reporting `θⱼ`. -/
def hi_C (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (i j : Fin (M.N + 1)) : ℝ :=
  M.u (M.θ i + c i) + M.β * w i - (M.u (M.θ i + c j) + M.β * w j)

/-- Miao, (22.24), p. 789: all incentive constraints `Cᵢⱼ ≥ 0`. -/
def hi_IC (M : HIModel) (c w : Fin (M.N + 1) → ℝ) : Prop :=
  ∀ i j, 0 ≤ hi_C M c w i j

/-- The local downward (`Cᵢ,ᵢ₋₁ ≥ 0`) and upward (`Cᵢ₋₁,ᵢ ≥ 0`) constraints of Lemma 22.3.2. -/
def hi_LocalIC (M : HIModel) (c w : Fin (M.N + 1) → ℝ) : Prop :=
  ∀ i : Fin M.N, 0 ≤ hi_C M c w i.succ i.castSucc ∧ 0 ≤ hi_C M c w i.castSucc i.succ

/-- Miao, (22.25), p. 789: the agent's expected value `Σ πᵢ [u(θᵢ + cᵢ) + βwᵢ]`. -/
def hi_agentValue (M : HIModel) (c w : Fin (M.N + 1) → ℝ) : ℝ :=
  ∑ i, M.prob i * (M.u (M.θ i + c i) + M.β * w i)

/-- The principal's value `Σ πᵢ [−cᵢ + β f(wᵢ)]` of a contract against a continuation `f`, the
objective of (22.23). -/
def hi_principalValue (M : HIModel) (f : ℝ → ℝ) (c w : Fin (M.N + 1) → ℝ) : ℝ :=
  ∑ i, M.prob i * (-c i + M.β * f (w i))

/-- `sup u`. -/
noncomputable def hi_ubar (M : HIModel) : ℝ := sSup (Set.range M.u)

/-- Miao, p. 789: `vmax = sup u(c) / (1 − β)`. -/
noncomputable def hi_vmax (M : HIModel) : ℝ := hi_ubar M / (1 - M.β)

/-- Miao, (22.23)–(22.25), p. 789: the contract `(c, w)` is feasible at `v`: incentive
compatible, promise keeping, and `wᵢ < vmax` (the book allows `wᵢ ∈ [−∞, vmax]`; real
continuation values below the supremum are used here). -/
def hi_Feasible (M : HIModel) (v : ℝ) (c w : Fin (M.N + 1) → ℝ) : Prop :=
  hi_IC M c w ∧ hi_agentValue M c w = v ∧ ∀ i, w i < hi_vmax M

/-- A strictly concave function has strictly decreasing increments: for `x < y` and `d > 0`,
`f(y + d) − f(y) < f(x + d) − f(x)`. -/
theorem hi_strict_decreasing_increments {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ Set.univ f)
    {x y d : ℝ} (hxy : x < y) (hd : 0 < d) : f (y + d) - f y < f (x + d) - f x := by
  have h1 := hf.secant_strict_mono (a := x) (x := x + d) (y := y + d) (Set.mem_univ _)
    (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith) (by linarith)
  have h2 := hf.secant_strict_mono (a := y + d) (x := x) (y := y) (Set.mem_univ _)
    (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith) hxy
  have e1 : (f (x + d) - f x) / (x + d - x) = (f (x + d) - f x) / d := by ring_nf
  have e2 : (f y - f (y + d)) / (y - (y + d)) = (f (y + d) - f y) / d := by
    rw [show y - (y + d) = -d by ring, div_neg, ← neg_div]; ring
  have e3 : (f x - f (y + d)) / (x - (y + d)) = (f (y + d) - f x) / (y + d - x) := by
    rw [show x - (y + d) = -(y + d - x) by ring, div_neg, ← neg_div]; ring
  rw [e1] at h1
  rw [e2, e3] at h2
  exact (div_lt_div_iff_of_pos_right hd).1 (h2.trans h1)

/-- A concave function has decreasing increments: for `x ≤ y` and `d ≥ 0`,
`f(y + d) − f(y) ≤ f(x + d) − f(x)`. -/
theorem hi_decreasing_increments {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ Set.univ f)
    {x y d : ℝ} (hxy : x ≤ y) (hd : 0 ≤ d) : f (y + d) - f y ≤ f (x + d) - f x := by
  rcases hxy.lt_or_eq with hxy | rfl
  · rcases hd.lt_or_eq with hd | rfl
    · exact (hi_strict_decreasing_increments hf hxy hd).le
    · simp
  · exact le_rfl

/-- Miao, p. 790 (proof of Lemma 22.3.1): `Cᵢ,ₖ + Cₖ,ᵢ = [u(θᵢ + cᵢ) − u(θₖ + cᵢ)] −
[u(θᵢ + cₖ) − u(θₖ + cₖ)]`. -/
theorem hi_C_add_C (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (i k : Fin (M.N + 1)) :
    hi_C M c w i k + hi_C M c w k i =
      (M.u (M.θ i + c i) - M.u (M.θ k + c i)) - (M.u (M.θ i + c k) - M.u (M.θ k + c k)) := by
  unfold hi_C; ring

/-- Miao, p. 790 (proof of Lemma 22.3.1): the pair of constraints `Cᵢₖ ≥ 0`, `Cₖᵢ ≥ 0` with
`θₖ < θᵢ` implies `cᵢ ≤ cₖ` and `wₖ ≤ wᵢ`. -/
theorem hi_pair_mono (M : HIModel) (c w : Fin (M.N + 1) → ℝ) {i k : Fin (M.N + 1)}
    (hki : k < i) (h1 : 0 ≤ hi_C M c w i k) (h2 : 0 ≤ hi_C M c w k i) :
    c i ≤ c k ∧ w k ≤ w i := by
  have hθ : M.θ k < M.θ i := M.θ_strictMono hki
  have hc : c i ≤ c k := by
    by_contra hlt
    push Not at hlt
    have key := hi_strict_decreasing_increments M.u_strictConcave
      (x := M.θ k + c k) (y := M.θ k + c i) (d := M.θ i - M.θ k) (by linarith) (by linarith)
    have hs := hi_C_add_C M c w i k
    rw [show M.θ k + c i + (M.θ i - M.θ k) = M.θ i + c i by ring,
      show M.θ k + c k + (M.θ i - M.θ k) = M.θ i + c k by ring] at key
    linarith
  refine ⟨hc, ?_⟩
  have hu : M.u (M.θ i + c i) ≤ M.u (M.θ i + c k) := M.u_strictMono.monotone (by linarith)
  unfold hi_C at h1
  nlinarith [M.β_pos]

/-- Miao, p. 790 (proof of Lemma 22.3.1, local form): the local constraints imply that `c` is
antitone and `w` is monotone. -/
theorem hi_local_mono (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (h : hi_LocalIC M c w) :
    Antitone c ∧ Monotone w := by
  refine ⟨Fin.antitone_iff_succ_le.2 fun i => ?_, Fin.monotone_iff_le_succ.2 fun i => ?_⟩
  · exact (hi_pair_mono M c w (Fin.castSucc_lt_succ) (h i).1 (h i).2).1
  · exact (hi_pair_mono M c w (Fin.castSucc_lt_succ) (h i).1 (h i).2).2

/-- **Lemma 22.3.1** (Miao, p. 790). Incentive constraints imply `cᵢ₋₁ ≥ cᵢ` and `wᵢ₋₁ ≤ wᵢ`
for all `i`: `c` is antitone and `w` is monotone in the income state. -/
theorem lemma_22_3_1 (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (h : hi_IC M c w) :
    Antitone c ∧ Monotone w :=
  hi_local_mono M c w fun _ => ⟨h _ _, h _ _⟩

/-- Miao, p. 791 (proof of Lemma 22.3.2, downward step): if `Cᵢₖ ≥ 0`, `cᵢ ≤ cₖ`, `θᵢ ≤ θⱼ`,
and `Cⱼᵢ ≥ 0`, then `Cⱼₖ ≥ 0`. -/
theorem hi_down_step (M : HIModel) (c w : Fin (M.N + 1) → ℝ) {i j k : Fin (M.N + 1)}
    (hij : i ≤ j) (hc : c i ≤ c k) (h1 : 0 ≤ hi_C M c w i k) (h2 : 0 ≤ hi_C M c w j i) :
    0 ≤ hi_C M c w j k := by
  have hθ : M.θ i ≤ M.θ j := M.θ_strictMono.monotone hij
  have key := hi_decreasing_increments M.u_strictConcave (x := M.θ i + c i)
    (y := M.θ i + c k) (d := M.θ j - M.θ i) (by linarith) (by linarith)
  rw [show M.θ i + c i + (M.θ j - M.θ i) = M.θ j + c i by ring,
    show M.θ i + c k + (M.θ j - M.θ i) = M.θ j + c k by ring] at key
  unfold hi_C at *
  linarith

/-- Miao, p. 791 (proof of Lemma 22.3.2, upward step): if `Cₖᵢ ≥ 0`, `cⱼ ≤ cᵢ`, `θₖ ≤ θᵢ`
and `Cᵢⱼ ≥ 0`, then `Cₖⱼ ≥ 0`. -/
theorem hi_up_step (M : HIModel) (c w : Fin (M.N + 1) → ℝ) {i j k : Fin (M.N + 1)}
    (hki : k ≤ i) (hc : c j ≤ c i) (h1 : 0 ≤ hi_C M c w k i) (h2 : 0 ≤ hi_C M c w i j) :
    0 ≤ hi_C M c w k j := by
  have hθ : M.θ k ≤ M.θ i := M.θ_strictMono.monotone hki
  have key := hi_decreasing_increments M.u_strictConcave (x := M.θ k + c j)
    (y := M.θ k + c i) (d := M.θ i - M.θ k) (by linarith) (by linarith)
  rw [show M.θ k + c j + (M.θ i - M.θ k) = M.θ i + c j by ring,
    show M.θ k + c i + (M.θ i - M.θ k) = M.θ i + c i by ring] at key
  unfold hi_C at *
  linarith

/-- **Lemma 22.3.2** (Miao, p. 791). If the local downward constraints `Cᵢ,ᵢ₋₁ ≥ 0` and the local
upward constraints `Cᵢ₋₁,ᵢ ≥ 0` hold for each `i`, then all the constraints `Cᵢⱼ ≥ 0` hold. -/
theorem lemma_22_3_2 (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (h : hi_LocalIC M c w) :
    hi_IC M c w := by
  obtain ⟨hc, -⟩ := hi_local_mono M c w h
  have hself : ∀ i, hi_C M c w i i = 0 := fun i => by unfold hi_C; ring
  -- downward: `C_{k+m, k} ≥ 0`, by induction on `m`
  have down : ∀ m : ℕ, ∀ k : Fin (M.N + 1), ∀ hm : k.val + m < M.N + 1,
      0 ≤ hi_C M c w ⟨k.val + m, hm⟩ k := by
    intro m
    induction m with
    | zero => intro k _; simp [hself]
    | succ m ih =>
      intro k hm
      have hm' : k.val + m < M.N := by omega
      have ih' := ih k (by omega)
      have hloc := (h ⟨k.val + m, hm'⟩).1
      have e1 : (⟨k.val + m, hm'⟩ : Fin M.N).succ = ⟨k.val + (m + 1), hm⟩ := by
        ext; simp; omega
      have e2 : (⟨k.val + m, hm'⟩ : Fin M.N).castSucc = ⟨k.val + m, by omega⟩ := rfl
      rw [e1, e2] at hloc
      exact hi_down_step M c w (Fin.mk_le_mk.2 (by omega))
        (hc (Fin.mk_le_mk.2 (by omega) : k ≤ ⟨k.val + m, by omega⟩)) ih' hloc
  -- upward: `C_{k, k+m} ≥ 0`, by induction on `m`
  have up : ∀ m : ℕ, ∀ k : Fin (M.N + 1), ∀ hm : k.val + m < M.N + 1,
      0 ≤ hi_C M c w k ⟨k.val + m, hm⟩ := by
    intro m
    induction m with
    | zero => intro k _; simp [hself]
    | succ m ih =>
      intro k hm
      have hm' : k.val + m < M.N := by omega
      have ih' := ih k (by omega)
      have hloc := (h ⟨k.val + m, hm'⟩).2
      have e1 : (⟨k.val + m, hm'⟩ : Fin M.N).succ = ⟨k.val + (m + 1), hm⟩ := by
        ext; simp; omega
      have e2 : (⟨k.val + m, hm'⟩ : Fin M.N).castSucc = ⟨k.val + m, by omega⟩ := rfl
      rw [e1, e2] at hloc
      exact hi_up_step M c w (Fin.mk_le_mk.2 (by omega))
        (hc (Fin.mk_le_mk.2 (by omega))) ih' hloc
  intro i j
  rcases le_total j i with hji | hij
  · have := down (i.val - j.val) j (by omega)
    have e : (⟨j.val + (i.val - j.val), by omega⟩ : Fin (M.N + 1)) = i := by
      ext; simp only; omega
    rwa [e] at this
  · have := up (j.val - i.val) i (by omega)
    have e : (⟨i.val + (j.val - i.val), by omega⟩ : Fin (M.N + 1)) = j := by
      ext; simp only; omega
    rwa [e] at this

/-- Miao, p. 793 and p. 794 (proofs of Propositions 22.3.1 and 22.3.2): a binding local
downward constraint `Cᵢ,ₖ = 0` (`θₖ < θᵢ`) together with `cᵢ ≤ cₖ` implies the upward
constraint `Cₖ,ᵢ ≥ 0`; it is slack (`Cₖ,ᵢ > 0`) when `cᵢ < cₖ`. -/
theorem hi_upward_of_binding (M : HIModel) (c w : Fin (M.N + 1) → ℝ) {i k : Fin (M.N + 1)}
    (hki : k < i) (hbind : hi_C M c w i k = 0) (hc : c i ≤ c k) :
    0 ≤ hi_C M c w k i ∧ (c i < c k → 0 < hi_C M c w k i) := by
  have hθ : M.θ k < M.θ i := M.θ_strictMono hki
  have hs := hi_C_add_C M c w i k
  refine ⟨?_, fun hlt => ?_⟩
  · have key := hi_decreasing_increments M.u_strictConcave (x := M.θ k + c i)
      (y := M.θ k + c k) (d := M.θ i - M.θ k) (by linarith) (by linarith)
    rw [show M.θ k + c i + (M.θ i - M.θ k) = M.θ i + c i by ring,
      show M.θ k + c k + (M.θ i - M.θ k) = M.θ i + c k by ring] at key
    linarith
  · have key := hi_strict_decreasing_increments M.u_strictConcave (x := M.θ k + c i)
      (y := M.θ k + c k) (d := M.θ i - M.θ k) (by linarith) (by linarith)
    rw [show M.θ k + c i + (M.θ i - M.θ k) = M.θ i + c i by ring,
      show M.θ k + c k + (M.θ i - M.θ k) = M.θ i + c k by ring] at key
    linarith

/-- Miao, p. 796: adding a constant `k` to every continuation value `wᵢ` leaves every
incentive constraint `Cᵢⱼ` unchanged. -/
theorem hi_C_shift (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (k : ℝ) (i j : Fin (M.N + 1)) :
    hi_C M c (fun l => w l + k) i j = hi_C M c w i j := by
  unfold hi_C; ring

/-- Miao, p. 796: adding `k` to every `wᵢ` raises the agent's value by `βk`. -/
theorem hi_agentValue_shift (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (k : ℝ) :
    hi_agentValue M c (fun l => w l + k) = hi_agentValue M c w + M.β * k := by
  unfold hi_agentValue
  have : ∑ i, M.prob i * (M.u (M.θ i + c i) + M.β * (w i + k)) =
      ∑ i, M.prob i * (M.u (M.θ i + c i) + M.β * w i) + (∑ i, M.prob i) * (M.β * k) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, M.prob_sum, one_mul]

/-- The CARA utility `u(c) = −exp(−γc)` of Exercise 22.4. -/
noncomputable def hi_cara (γ : ℝ) (x : ℝ) : ℝ := -Real.exp (-γ * x)

/-- The CARA utility is strictly increasing. -/
theorem hi_cara_strictMono {γ : ℝ} (hγ : 0 < γ) : StrictMono (hi_cara γ) := by
  intro x y hxy
  unfold hi_cara
  have : -γ * y < -γ * x := by nlinarith
  linarith [Real.exp_lt_exp.2 this]

/-- The CARA utility is strictly concave. -/
theorem hi_cara_strictConcave {γ : ℝ} (hγ : 0 < γ) :
    StrictConcaveOn ℝ Set.univ (hi_cara γ) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hne : -γ * x ≠ -γ * y := by
    intro h; exact hxy (by have := mul_left_cancel₀ (neg_ne_zero.2 hγ.ne') h; exact this)
  have key := (strictConvexOn_exp).2 (Set.mem_univ (-γ * x)) (Set.mem_univ (-γ * y)) hne ha hb hab
  simp only [smul_eq_mul, hi_cara] at key ⊢
  have e : -γ * (a * x + b * y) = a * (-γ * x) + b * (-γ * y) := by ring
  rw [e]
  linarith

/-- The CARA utility is bounded above by `0`, with supremum `0`. -/
theorem hi_cara_sSup {γ : ℝ} (hγ : 0 < γ) : sSup (Set.range (hi_cara γ)) = 0 := by
  refine le_antisymm (csSup_le (Set.range_nonempty _) ?_) ?_
  · rintro _ ⟨x, rfl⟩; unfold hi_cara; linarith [Real.exp_pos (-γ * x)]
  · refine le_of_forall_lt fun ε hε => ?_
    have hbdd : BddAbove (Set.range (hi_cara γ)) := ⟨0, by
      rintro _ ⟨x, rfl⟩; unfold hi_cara; linarith [Real.exp_pos (-γ * x)]⟩
    -- choose `x` with `exp(−γx) < −ε`
    have hε' : 0 < -ε := by linarith
    refine lt_csSup_of_lt hbdd ⟨-Real.log (-ε) / γ + 1, rfl⟩ ?_
    unfold hi_cara
    have e : -γ * (-Real.log (-ε) / γ + 1) = Real.log (-ε) - γ := by field_simp; ring
    rw [e, Real.exp_sub, Real.exp_log hε']
    have h1 : 1 < Real.exp γ := Real.one_lt_exp_iff.2 hγ
    have : -ε / Real.exp γ < -ε := div_lt_self hε' h1
    linarith

/-- The CARA utility is unbounded below. -/
theorem hi_cara_not_bddBelow {γ : ℝ} (hγ : 0 < γ) : ¬ BddBelow (Set.range (hi_cara γ)) := by
  rintro ⟨m, hm⟩
  have h := hm ⟨-Real.log (|m| + 1) / γ, rfl⟩
  unfold hi_cara at h
  have e : -γ * (-Real.log (|m| + 1) / γ) = Real.log (|m| + 1) := by field_simp
  rw [e, Real.exp_log (by positivity)] at h
  have := neg_abs_le m
  linarith

/-- The hidden-information model with CARA utility `−exp(−γc)` (Exercise 22.4), for any income
distribution and discount factor. -/
noncomputable def hi_caraModel (γ : ℝ) (hγ : 0 < γ) (N : ℕ) (θ prob : Fin (N + 1) → ℝ)
    (β : ℝ) (hθ : StrictMono θ) (hp : ∀ i, 0 < prob i) (hs : ∑ i, prob i = 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) : HIModel where
  N := N
  θ := θ
  prob := prob
  β := β
  u := hi_cara γ
  θ_strictMono := hθ
  prob_pos := hp
  prob_sum := hs
  β_pos := hβ0
  β_lt_one := hβ1
  u_cont := by unfold hi_cara; fun_prop
  u_strictMono := hi_cara_strictMono hγ
  u_strictConcave := hi_cara_strictConcave hγ
  u_bddAbove := ⟨0, by rintro _ ⟨x, rfl⟩; unfold hi_cara; linarith [Real.exp_pos (-γ * x)]⟩
  u_not_bddBelow := hi_cara_not_bddBelow hγ

/-- A concrete instance: two income states `θ = (0, 1)` with probabilities `(1/2, 1/2)`,
`β = 1/2`, CARA utility with `γ = 1`. -/
noncomputable def hi_exampleModel : HIModel :=
  hi_caraModel 1 one_pos 1 ![0, 1] ![1 / 2, 1 / 2] (1 / 2)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) (by norm_num) (by norm_num)

/-- The concrete instance has two income states. -/
theorem hi_exampleModel_N : hi_exampleModel.N = 1 := rfl

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Assumption 22.3.1 and the DARA step of Proposition 22.3.1

Miao, §22.3, pp. 788 and 791–793.

* `assumption_22_3_1 u u' u''` (Assumption 22.3.1): `u' > 0`, `u'' < 0`, `sup u < ∞`,
  `inf u = −∞`, `u' → ∞` at the lower end of the domain, and decreasing absolute risk aversion
  `−u''/u'`. The domain is `ℝ` (the book's `a = −∞`, see `HIBasics`).
* `hi_cara_assumption_22_3_1`: the CARA utility of Exercise 22.4 satisfies it (so the assumption
  is not vacuous); `hi_modelOfAssumption` builds an `HIModel` from any utility satisfying it.
* `hi_dara_ratio_mono`: under DARA the ratio `u'(x + d)/u'(x)` is increasing in `x` (`d ≥ 0`).
* `hi_dara_ce`: the key DARA inequality of p. 792. If `u(x*) = δu(x⁰) + (1 − δ)u(x¹)` then
  `u(x* + d) ≤ δu(x⁰ + d) + (1 − δ)u(x¹ + d)` for `d ≥ 0` (the risk premium decreases with
  income). It is proved from the ratio monotonicity with Cauchy's mean value theorem.
* The averaged contract of p. 792: `hi_exists_mix` (the transfer `c*ᵢ` exists),
  `hi_mix_c_le` (`c*ᵢ ≤ δc⁰ᵢ + (1 − δ)c¹ᵢ`), `hi_mix_agentValue` (it delivers
  `δv⁰ + (1 − δ)v¹`), `hi_mix_principal_ge` (the principal gets at least the average against a
  concave continuation), `hi_mix_C_eq` (the displayed identity for `C*ᵢ,ᵢ₋₁`), and
  `hi_mix_downward` (all downward constraints of the averaged contract hold).
-/

namespace Miao.RecursiveContracts

open Finset Filter

/-- **Assumption 22.3.1** (Miao, p. 788). `u' > 0`, `u'' < 0`, `sup u < ∞`, `inf u = −∞`,
`lim u' = ∞` at the lower end of the domain (here `−∞`), and `−u''/u'` is decreasing (DARA);
`u'` and `u''` are the first two derivatives of `u`. -/
def assumption_22_3_1 (u u' u'' : ℝ → ℝ) : Prop :=
  (∀ x, HasDerivAt u (u' x) x) ∧ (∀ x, HasDerivAt u' (u'' x) x) ∧ (∀ x, 0 < u' x) ∧
    (∀ x, u'' x < 0) ∧ BddAbove (Set.range u) ∧ ¬ BddBelow (Set.range u) ∧
    Tendsto u' atBot atTop ∧ Antitone (fun x => -u'' x / u' x)

/-- The CARA utility `−exp(−γc)`, `γ > 0`, satisfies Assumption 22.3.1, with
`u' = γ exp(−γc)`, `u'' = −γ² exp(−γc)` and constant absolute risk aversion `γ`. -/
theorem hi_cara_assumption_22_3_1 {γ : ℝ} (hγ : 0 < γ) :
    assumption_22_3_1 (hi_cara γ) (fun x => γ * Real.exp (-γ * x))
      (fun x => -(γ ^ 2) * Real.exp (-γ * x)) := by
  have hd : ∀ x, HasDerivAt (fun x => -γ * x) (-γ) x := fun x => by
    simpa using (hasDerivAt_id x).const_mul (-γ)
  refine ⟨fun x => ?_, fun x => ?_, fun x => by positivity, fun x => ?_, ⟨0, ?_⟩,
    hi_cara_not_bddBelow hγ, ?_, ?_⟩
  · have := ((hd x).exp).neg
    unfold hi_cara
    convert this using 1; ring
  · have := ((hd x).exp).const_mul γ
    convert this using 1; ring
  · have := Real.exp_pos (-γ * x); nlinarith [sq_pos_of_pos hγ]
  · rintro _ ⟨x, rfl⟩; unfold hi_cara; linarith [Real.exp_pos (-γ * x)]
  · have h1 : Tendsto (fun x : ℝ => -γ * x) atBot atTop := by
      have := tendsto_neg_atBot_atTop.const_mul_atTop hγ
      simpa [neg_mul, mul_neg] using this
    exact (Real.tendsto_exp_atTop.comp h1).const_mul_atTop hγ
  · intro x y _
    have e : ∀ z, -(-(γ ^ 2) * Real.exp (-γ * z)) / (γ * Real.exp (-γ * z)) = γ := fun z => by
      have := Real.exp_pos (-γ * z); field_simp
    simp only [e, le_refl]

/-- An `HIModel` built from a utility satisfying Assumption 22.3.1. -/
noncomputable def hi_modelOfAssumption {u u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 u u' u'')
    (N : ℕ) (θ prob : Fin (N + 1) → ℝ) (β : ℝ) (hθ : StrictMono θ) (hp : ∀ i, 0 < prob i)
    (hs : ∑ i, prob i = 1) (hβ0 : 0 < β) (hβ1 : β < 1) : HIModel where
  N := N
  θ := θ
  prob := prob
  β := β
  u := u
  θ_strictMono := hθ
  prob_pos := hp
  prob_sum := hs
  β_pos := hβ0
  β_lt_one := hβ1
  u_cont := continuous_iff_continuousAt.2 fun x => (hu.1 x).continuousAt
  u_strictMono := strictMono_of_deriv_pos fun x => by rw [(hu.1 x).deriv]; exact hu.2.2.1 x
  u_strictConcave := by
    have hder : deriv u = u' := funext fun x => (hu.1 x).deriv
    refine StrictAnti.strictConcaveOn_univ_of_deriv
      (continuous_iff_continuousAt.2 fun x => (hu.1 x).continuousAt) ?_
    rw [hder]
    exact strictAnti_of_deriv_neg fun x => by rw [(hu.2.1 x).deriv]; exact hu.2.2.2.1 x
  u_bddAbove := hu.2.2.2.2.1
  u_not_bddBelow := hu.2.2.2.2.2.1

/-- Miao, p. 792 (DARA): under Assumption 22.3.1 the ratio `u'(x + d)/u'(x)` is increasing in
`x` for every `d ≥ 0`. -/
theorem hi_dara_ratio_mono {u u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 u u' u'') {d : ℝ}
    (hd : 0 ≤ d) : Monotone fun x => u' (x + d) / u' x := by
  obtain ⟨-, h2, h3, -, -, -, -, h8⟩ := hu
  have hder : ∀ x, HasDerivAt (fun x => u' (x + d) / u' x)
      ((u'' (x + d) * u' x - u' (x + d) * u'' x) / u' x ^ 2) x := fun x => by
    have ha : HasDerivAt (fun x => u' (x + d)) (u'' (x + d)) x :=
      (h2 (x + d)).comp_add_const x d
    exact ha.div (h2 x) (h3 x).ne'
  refine monotone_of_deriv_nonneg (fun x => (hder x).differentiableAt) fun x => ?_
  rw [(hder x).deriv]
  have hA := h8 (show x ≤ x + d by linarith)
  simp only at hA
  have p1 := h3 x
  have p2 := h3 (x + d)
  rw [div_le_div_iff₀ p2 p1] at hA
  apply div_nonneg _ (sq_nonneg _)
  nlinarith

/-- Miao, p. 792 (DARA, "the risk premium is a decreasing function of income"): if
`u(x*) = δu(x⁰) + (1 − δ)u(x¹)` with `δ ∈ (0, 1)` and `d ≥ 0`, then
`u(x* + d) ≤ δu(x⁰ + d) + (1 − δ)u(x¹ + d)`. -/
theorem hi_dara_ce {u u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 u u' u'') {d δ x0 x1 xs : ℝ}
    (hd : 0 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hxs : u xs = δ * u x0 + (1 - δ) * u x1) :
    u (xs + d) ≤ δ * u (x0 + d) + (1 - δ) * u (x1 + d) := by
  have hmono : StrictMono u :=
    strictMono_of_deriv_pos fun x => by rw [(hu.1 x).deriv]; exact hu.2.2.1 x
  have hρ := hi_dara_ratio_mono hu hd
  have hpos := hu.2.2.1
  have hderu := hu.1
  have hderh : ∀ x, HasDerivAt (fun x => u (x + d)) (u' (x + d)) x := fun x => by
    exact (hderu (x + d)).comp_add_const x d
  have hcu : Continuous u := continuous_iff_continuousAt.2 fun x => (hderu x).continuousAt
  have hch : Continuous fun x => u (x + d) := hcu.comp (continuous_id.add continuous_const)
  -- the core case `a < s < b`, with `u s = t u a + (1 − t) u b`
  have core : ∀ a b s t : ℝ, a < b → 0 < t → t < 1 → u s = t * u a + (1 - t) * u b →
      u (s + d) ≤ t * u (a + d) + (1 - t) * u (b + d) := by
    intro a b s t hab ht0 ht1 hs
    have hua := hmono hab
    have has : a < s := hmono.lt_iff_lt.1 (by rw [hs]; nlinarith)
    have hsb : s < b := hmono.lt_iff_lt.1 (by rw [hs]; nlinarith)
    obtain ⟨ξ, hξ, e1⟩ := exists_ratio_hasDerivAt_eq_ratio_slope (fun x => u (x + d))
      (fun x => u' (x + d)) has hch.continuousOn (fun x _ => hderh x) u u' hcu.continuousOn
      (fun x _ => hderu x)
    obtain ⟨η, hη, e2⟩ := exists_ratio_hasDerivAt_eq_ratio_slope (fun x => u (x + d))
      (fun x => u' (x + d)) hsb hch.continuousOn (fun x _ => hderh x) u u' hcu.continuousOn
      (fun x _ => hderu x)
    have hξη : ξ ≤ η := by linarith [hξ.2, hη.1]
    have hr := hρ hξη
    simp only at hr
    have pξ := hpos ξ
    have pη := hpos η
    rw [div_le_div_iff₀ pξ pη] at hr
    -- slopes: `h(s) − h(a) = ρ(ξ)(u s − u a)`, `h(b) − h(s) = ρ(η)(u b − u s)`
    have k1 : u s - u a = (1 - t) * (u b - u a) := by rw [hs]; ring
    have k2 : u b - u s = t * (u b - u a) := by rw [hs]; ring
    rw [k1] at e1
    rw [k2] at e2
    have hD : 0 < u b - u a := by linarith
    -- goal: `t (h s − h a) ≤ (1 − t)(h b − h s)`
    have key : t * (u (s + d) - u (a + d)) * (u' ξ * u' η) ≤
        (1 - t) * (u (b + d) - u (s + d)) * (u' ξ * u' η) := by
      have q1 : (u (s + d) - u (a + d)) * u' ξ = (1 - t) * (u b - u a) * u' (ξ + d) := by
        linarith
      have q2 : (u (b + d) - u (s + d)) * u' η = t * (u b - u a) * u' (η + d) := by linarith
      calc t * (u (s + d) - u (a + d)) * (u' ξ * u' η)
          = t * (1 - t) * (u b - u a) * (u' (ξ + d) * u' η) := by
            rw [show t * (u (s + d) - u (a + d)) * (u' ξ * u' η) =
              t * ((u (s + d) - u (a + d)) * u' ξ) * u' η by ring, q1]; ring
        _ ≤ t * (1 - t) * (u b - u a) * (u' (η + d) * u' ξ) := by
            apply mul_le_mul_of_nonneg_left hr
            have : 0 < t * (1 - t) := by nlinarith
            positivity
        _ = (1 - t) * (u (b + d) - u (s + d)) * (u' ξ * u' η) := by
            rw [show (1 - t) * (u (b + d) - u (s + d)) * (u' ξ * u' η) =
              (1 - t) * ((u (b + d) - u (s + d)) * u' η) * u' ξ by ring, q2]; ring
    have hpp : 0 < u' ξ * u' η := mul_pos pξ pη
    have := le_of_mul_le_mul_right key hpp
    nlinarith
  rcases lt_trichotomy x0 x1 with h01 | h01 | h01
  · exact core x0 x1 xs δ h01 hδ0 hδ1 hxs
  · subst h01
    have : xs = x0 := hmono.injective (by rw [hxs]; ring)
    subst this; linarith
  · have := core x1 x0 xs (1 - δ) h01 (by linarith) (by linarith) (by rw [hxs]; ring)
    linarith

/-- Miao, p. 792: the transfer `c*ᵢ` of the averaged contract exists:
`u(θᵢ + c*ᵢ) = δu(θᵢ + c⁰ᵢ) + (1 − δ)u(θᵢ + c¹ᵢ)` has a solution for `δ ∈ [0, 1]`. -/
theorem hi_exists_mix (M : HIModel) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (c0 c1 : Fin (M.N + 1) → ℝ) : ∃ cs : Fin (M.N + 1) → ℝ, ∀ i,
      M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i) := by
  have : ∀ i, ∃ x, M.u (M.θ i + x) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i) := by
    intro i
    set y := δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i)
    set lo := min (M.θ i + c0 i) (M.θ i + c1 i)
    set hi := max (M.θ i + c0 i) (M.θ i + c1 i)
    have hlo : M.u lo ≤ y := by
      have a1 : M.u lo ≤ M.u (M.θ i + c0 i) := M.u_strictMono.monotone (min_le_left _ _)
      have a2 : M.u lo ≤ M.u (M.θ i + c1 i) := M.u_strictMono.monotone (min_le_right _ _)
      nlinarith
    have hhi : y ≤ M.u hi := by
      have a1 : M.u (M.θ i + c0 i) ≤ M.u hi := M.u_strictMono.monotone (le_max_left _ _)
      have a2 : M.u (M.θ i + c1 i) ≤ M.u hi := M.u_strictMono.monotone (le_max_right _ _)
      nlinarith
    obtain ⟨x, hx⟩ := intermediate_value_univ lo hi M.u_cont ⟨hlo, hhi⟩
    exact ⟨x - M.θ i, by simp only [add_sub_cancel]; exact hx⟩
  choose cs hcs using this
  exact ⟨cs, hcs⟩

/-- Miao, p. 792: "the concavity of `u` implies `c*ᵢ ≤ δc⁰ᵢ + (1 − δ)c¹ᵢ`". -/
theorem hi_mix_c_le (M : HIModel) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {c0 c1 cs : Fin (M.N + 1) → ℝ}
    (hcs : ∀ i, M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i))
    (i : Fin (M.N + 1)) : cs i ≤ δ * c0 i + (1 - δ) * c1 i := by
  have hc := M.u_strictConcave.concaveOn.2 (Set.mem_univ (M.θ i + c0 i))
    (Set.mem_univ (M.θ i + c1 i)) hδ0 (by linarith : 0 ≤ 1 - δ) (by ring)
  simp only [smul_eq_mul] at hc
  rw [← hcs i] at hc
  have e : δ * (M.θ i + c0 i) + (1 - δ) * (M.θ i + c1 i) = M.θ i + (δ * c0 i + (1 - δ) * c1 i) :=
    by ring
  rw [e] at hc
  have := M.u_strictMono.le_iff_le.1 hc
  linarith

/-- Miao, p. 792: the averaged contract `(c*, δw⁰ + (1 − δ)w¹)` gives the agent the promised
utility `δv⁰ + (1 − δ)v¹`. -/
theorem hi_mix_agentValue (M : HIModel) {δ : ℝ} {c0 c1 cs w0 w1 : Fin (M.N + 1) → ℝ}
    (hcs : ∀ i, M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i)) :
    hi_agentValue M cs (fun i => δ * w0 i + (1 - δ) * w1 i) =
      δ * hi_agentValue M c0 w0 + (1 - δ) * hi_agentValue M c1 w1 := by
  unfold hi_agentValue
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [hcs i]; ring

/-- Miao, p. 792: against a continuation `f` concave on `(−∞, vmax)`, the averaged contract
gives the principal at least `δ` times the value of the first contract plus `1 − δ` times the
value of the second. -/
theorem hi_mix_principal_ge (M : HIModel) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) {c0 c1 cs w0 w1 : Fin (M.N + 1) → ℝ}
    (hcs : ∀ i, M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i))
    (hw0 : ∀ i, w0 i < hi_vmax M) (hw1 : ∀ i, w1 i < hi_vmax M) :
    δ * hi_principalValue M f c0 w0 + (1 - δ) * hi_principalValue M f c1 w1 ≤
      hi_principalValue M f cs (fun i => δ * w0 i + (1 - δ) * w1 i) := by
  unfold hi_principalValue
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hc := hi_mix_c_le M hδ0 hδ1 hcs i
  have hfc := hf.2 (hw0 i) (hw1 i) hδ0 (by linarith : 0 ≤ 1 - δ) (by ring)
  simp only [smul_eq_mul] at hfc
  have hp := M.prob_pos i
  have hβ := M.β_pos
  have h3 : δ * (-c0 i + M.β * f (w0 i)) + (1 - δ) * (-c1 i + M.β * f (w1 i)) ≤
      -cs i + M.β * f (δ * w0 i + (1 - δ) * w1 i) := by
    nlinarith [mul_le_mul_of_nonneg_left hfc hβ.le]
  have h4 := mul_le_mul_of_nonneg_left h3 hp.le
  simp only
  linarith

/-- Miao, p. 792: for the averaged contract,
`C*ᵢₖ = δC⁰ᵢₖ + (1 − δ)C¹ᵢₖ + [δu(θᵢ + c⁰ₖ) + (1 − δ)u(θᵢ + c¹ₖ) − u(θᵢ + c*ₖ)]`. -/
theorem hi_mix_C_eq (M : HIModel) {δ : ℝ} {c0 c1 cs w0 w1 : Fin (M.N + 1) → ℝ}
    (hcs : ∀ i, M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i))
    (i k : Fin (M.N + 1)) :
    hi_C M cs (fun i => δ * w0 i + (1 - δ) * w1 i) i k =
      δ * hi_C M c0 w0 i k + (1 - δ) * hi_C M c1 w1 i k +
        (δ * M.u (M.θ i + c0 k) + (1 - δ) * M.u (M.θ i + c1 k) - M.u (M.θ i + cs k)) := by
  unfold hi_C
  rw [hcs i]; ring

/-- Miao, p. 792: under Assumption 22.3.1 (DARA), if both contracts satisfy the downward
constraint `Cᵢₖ ≥ 0` (`k ≤ i`), so does the averaged contract. -/
theorem hi_mix_downward (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {c0 c1 cs w0 w1 : Fin (M.N + 1) → ℝ}
    (hcs : ∀ i, M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i))
    {i k : Fin (M.N + 1)} (hki : k ≤ i) (h0 : 0 ≤ hi_C M c0 w0 i k)
    (h1 : 0 ≤ hi_C M c1 w1 i k) :
    0 ≤ hi_C M cs (fun i => δ * w0 i + (1 - δ) * w1 i) i k := by
  rw [hi_mix_C_eq M hcs]
  have hθ : M.θ k ≤ M.θ i := M.θ_strictMono.monotone hki
  have key := hi_dara_ce hu (d := M.θ i - M.θ k) (by linarith) hδ0 hδ1 (hcs k)
  rw [show M.θ k + cs k + (M.θ i - M.θ k) = M.θ i + cs k by ring,
    show M.θ k + c0 k + (M.θ i - M.θ k) = M.θ i + c0 k by ring,
    show M.θ k + c1 k + (M.θ i - M.θ k) = M.θ i + c1 k by ring] at key
  nlinarith

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The principal's Bellman equation and Proposition 22.3.1

Miao, §22.3, pp. 789–793: the dynamic program (22.23)–(22.25) in the promised value `v`, its
bounds (22.26), and the contraction part of Proposition 22.3.1.

* `hi_uinv` inverts `u` on `(−∞, sup u)` (`hi_u_uinv`); `hi_cstar v = u⁻¹((1 − β)v)` is the
  first-best consumption `c*(v)` and `hi_b v` the constant transfer `b(v)` with
  `Σ πᵢ u(θᵢ + b) / (1 − β) = v` (`hi_b_spec`).
* `hi_L v = −b(v)/(1 − β)` and `hi_U v = Σ πᵢ [θᵢ − c*(v)]/(1 − β)` are the bounds of (22.26);
  `hi_InF` is the book's space `F` of functions between them on `(−∞, vmax)`;
  `hi_U_sub_L_le`: the gap is at most `(θ̄ − θ₁)/(1 − β)`.
* `hi_T` is the Bellman operator of (22.23): the supremum of the principal's value over the
  contracts feasible at `v`.
* `hi_const_feasible`: the constant contract `cᵢ = b(v)`, `wᵢ = v` is feasible;
  `hi_principal_le_U`: no feasible contract beats the first-best (Jensen's inequality);
  `eq_22_26`: `T` maps `F` into `F`, i.e. `−b/(1 − β) ≤ T f ≤ Σ πᵢ[θᵢ − c*]/(1 − β)`.
* `hi_T_abs_le`: Blackwell's discounting, `|Tf − Tg| ≤ β ε` when `|f − g| ≤ ε`.
* `proposition_22_3_1`: `T` has a fixed point `P` in `F` (the limit of `Tᵏ L`), it is unique in
  `F`, and it is decreasing; `hi_concaveOn_of_tendsto` is the final limit step of the concavity
  argument.

Departures: the book's space is continuous functions; here `F` is all functions between the
bounds (continuity is not needed for the contraction argument). Concavity of `P` is
`proposition_22_3_1_concave` (module `HIConcavity`); strict concavity, differentiability and
uniqueness of the optimal contract are not proved (see `docs/HI-corrections.md`).
-/

namespace Miao.RecursiveContracts

open Finset Filter Topology

/-- Every utility level lies strictly below `sup u`. -/
theorem hi_u_lt_ubar (M : HIModel) (x : ℝ) : M.u x < hi_ubar M :=
  lt_of_lt_of_le (M.u_strictMono (lt_add_one x)) (le_csSup M.u_bddAbove ⟨x + 1, rfl⟩)

/-- `u` maps onto `(−∞, sup u)`. -/
theorem hi_u_surj (M : HIModel) {y : ℝ} (hy : y < hi_ubar M) : ∃ x, M.u x = y := by
  obtain ⟨_, ⟨x0, rfl⟩, h0⟩ := exists_lt_of_lt_csSup (Set.range_nonempty M.u) hy
  have : ∃ x1, M.u x1 < y := by
    by_contra h
    push Not at h
    exact M.u_not_bddBelow ⟨y, by rintro _ ⟨x, rfl⟩; exact h x⟩
  obtain ⟨x1, h1⟩ := this
  exact intermediate_value_univ x1 x0 M.u_cont ⟨h1.le, h0.le⟩

/-- The inverse of `u` on `(−∞, sup u)` (`0` elsewhere). -/
noncomputable def hi_uinv (M : HIModel) (y : ℝ) : ℝ :=
  if h : y < hi_ubar M then Classical.choose (hi_u_surj M h) else 0

/-- `u(u⁻¹(y)) = y` for `y < sup u`. -/
theorem hi_u_uinv (M : HIModel) {y : ℝ} (hy : y < hi_ubar M) : M.u (hi_uinv M y) = y := by
  simp only [hi_uinv, hy, ↓reduceDIte]
  exact Classical.choose_spec (hi_u_surj M hy)

/-- `v < vmax` iff `(1 − β)v < sup u`. -/
theorem hi_lt_vmax_iff (M : HIModel) (v : ℝ) : v < hi_vmax M ↔ (1 - M.β) * v < hi_ubar M := by
  have h : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_vmax
  rw [lt_div_iff₀ h, mul_comm]

/-- `Σ πᵢ a = a`. -/
theorem hi_sum_const (M : HIModel) (a : ℝ) : ∑ i, M.prob i * a = a := by
  rw [← Finset.sum_mul, M.prob_sum, one_mul]

/-- Miao, p. 789: the first-best consumption `c*(v)`, `u(c*(v)) = (1 − β)v`. -/
noncomputable def hi_cstar (M : HIModel) (v : ℝ) : ℝ := hi_uinv M ((1 - M.β) * v)

/-- `Σ πᵢ u(θᵢ + b)`. -/
noncomputable def hi_Bfun (M : HIModel) (b : ℝ) : ℝ := ∑ i, M.prob i * M.u (M.θ i + b)

/-- `b ↦ Σ πᵢ u(θᵢ + b)` is strictly increasing. -/
theorem hi_Bfun_strictMono (M : HIModel) : StrictMono (hi_Bfun M) := by
  intro x y hxy
  unfold hi_Bfun
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
  exact mul_lt_mul_of_pos_left (M.u_strictMono (by linarith)) (M.prob_pos i)

/-- `u(θ₁ + b) ≤ Σ πᵢ u(θᵢ + b) ≤ u(θₙ + b)`. -/
theorem hi_Bfun_bounds (M : HIModel) (b : ℝ) :
    M.u (M.θ 0 + b) ≤ hi_Bfun M b ∧ hi_Bfun M b ≤ M.u (M.θ (Fin.last M.N) + b) := by
  unfold hi_Bfun
  constructor
  · calc M.u (M.θ 0 + b) = ∑ i, M.prob i * M.u (M.θ 0 + b) := (hi_sum_const M _).symm
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (M.u_strictMono.monotone (by linarith [M.θ_strictMono.monotone (Fin.zero_le i)]))
          (M.prob_pos i).le
  · calc ∑ i, M.prob i * M.u (M.θ i + b)
        ≤ ∑ i, M.prob i * M.u (M.θ (Fin.last M.N) + b) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (M.u_strictMono.monotone (by linarith [M.θ_strictMono.monotone (Fin.le_last i)]))
            (M.prob_pos i).le
      _ = _ := hi_sum_const M _

/-- `b ↦ Σ πᵢ u(θᵢ + b)` maps onto `(−∞, sup u)`. -/
theorem hi_Bfun_surj (M : HIModel) {y : ℝ} (hy : y < hi_ubar M) : ∃ b, hi_Bfun M b = y := by
  obtain ⟨x0, hx0⟩ := hi_u_surj M (show (y + hi_ubar M) / 2 < hi_ubar M by linarith)
  have : ∃ x1, M.u x1 < y := by
    by_contra h
    push Not at h
    exact M.u_not_bddBelow ⟨y, by rintro _ ⟨x, rfl⟩; exact h x⟩
  obtain ⟨x1, h1⟩ := this
  have hc : Continuous (hi_Bfun M) := by
    unfold hi_Bfun
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul (M.u_cont.comp (continuous_const.add continuous_id))
  have a0 := (hi_Bfun_bounds M (x0 - M.θ 0)).1
  have a1 := (hi_Bfun_bounds M (x1 - M.θ (Fin.last M.N))).2
  rw [add_sub_cancel] at a0 a1
  exact intermediate_value_univ (x1 - M.θ (Fin.last M.N)) (x0 - M.θ 0) hc
    ⟨by linarith, by linarith⟩

/-- Miao, p. 789: the constant transfer `b(v)`, `Σ πᵢ u(θᵢ + b(v)) / (1 − β) = v`. -/
noncomputable def hi_b (M : HIModel) (v : ℝ) : ℝ :=
  if h : (1 - M.β) * v < hi_ubar M then Classical.choose (hi_Bfun_surj M h) else 0

/-- Miao, p. 789: `Σ πᵢ u(θᵢ + b(v)) = (1 − β)v` for `v < vmax`. -/
theorem hi_b_spec (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    hi_Bfun M (hi_b M v) = (1 - M.β) * v := by
  have h := (hi_lt_vmax_iff M v).1 hv
  simp only [hi_b, h, ↓reduceDIte]
  exact Classical.choose_spec (hi_Bfun_surj M h)

/-- `u(c*(v)) = (1 − β)v` for `v < vmax`. -/
theorem hi_cstar_spec (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    M.u (hi_cstar M v) = (1 - M.β) * v :=
  hi_u_uinv M ((hi_lt_vmax_iff M v).1 hv)

/-- `θ̄ = Σ πᵢ θᵢ`. -/
noncomputable def hi_θbar (M : HIModel) : ℝ := ∑ i, M.prob i * M.θ i

/-- Miao, (22.26), p. 789: the lower bound `−b(v)/(1 − β)`. -/
noncomputable def hi_L (M : HIModel) (v : ℝ) : ℝ := -hi_b M v / (1 - M.β)

/-- Miao, (22.26), p. 789: the first-best upper bound `Σ πᵢ [θᵢ − c*(v)]/(1 − β)`. -/
noncomputable def hi_U (M : HIModel) (v : ℝ) : ℝ := (hi_θbar M - hi_cstar M v) / (1 - M.β)

/-- The upper bound written as in (22.26): `Σ πᵢ [θᵢ − c*(v)]/(1 − β)`. -/
theorem hi_U_eq_sum (M : HIModel) (v : ℝ) :
    hi_U M v = ∑ i, M.prob i * (M.θ i - hi_cstar M v) / (1 - M.β) := by
  unfold hi_U hi_θbar
  rw [← Finset.sum_div]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, hi_sum_const]

/-- Miao, p. 791: the space `F` of functions lying between the bounds (22.26) on
`(−∞, vmax)`. -/
def hi_InF (M : HIModel) (f : ℝ → ℝ) : Prop :=
  ∀ v < hi_vmax M, hi_L M v ≤ f v ∧ f v ≤ hi_U M v

/-- The gap bound of p. 791: `θ₁ + b(v) ≤ c*(v)`. -/
theorem hi_b_le_cstar (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    M.θ 0 + hi_b M v ≤ hi_cstar M v := by
  have h1 := (hi_Bfun_bounds M (hi_b M v)).1
  rw [hi_b_spec M hv, ← hi_cstar_spec M hv] at h1
  exact M.u_strictMono.le_iff_le.1 h1

/-- Miao, p. 791: "the gap between these bounds is bounded": `U(v) − L(v) ≤ (θ̄ − θ₁)/(1 − β)`. -/
theorem hi_U_sub_L_le (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    hi_U M v - hi_L M v ≤ (hi_θbar M - M.θ 0) / (1 - M.β) := by
  have h := hi_b_le_cstar M hv
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_U hi_L
  rw [div_sub_div_same, div_le_div_iff_of_pos_right h1]
  linarith

/-- The agent's value of a contract with `wᵢ < vmax` lies below `vmax`. -/
theorem hi_agentValue_lt_vmax (M : HIModel) {c w : Fin (M.N + 1) → ℝ}
    (hw : ∀ i, w i < hi_vmax M) : hi_agentValue M c w < hi_vmax M := by
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have key : hi_agentValue M c w < ∑ i, M.prob i * (hi_ubar M + M.β * hi_vmax M) := by
    unfold hi_agentValue
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
    have := hi_u_lt_ubar M (M.θ i + c i)
    have := mul_lt_mul_of_pos_left (hw i) M.β_pos
    exact mul_lt_mul_of_pos_left (by linarith) (M.prob_pos i)
  rw [hi_sum_const] at key
  have e : hi_ubar M + M.β * hi_vmax M = hi_vmax M := by
    unfold hi_vmax; field_simp; ring
  linarith

/-- The set of principal's values of contracts feasible at `v`. -/
def hi_vals (M : HIModel) (f : ℝ → ℝ) (v : ℝ) : Set ℝ :=
  {x | ∃ c w, hi_Feasible M v c w ∧ hi_principalValue M f c w = x}

/-- Miao, (22.23), p. 789: the Bellman operator `(Tf)(v) = sup Σ πᵢ[−cᵢ + β f(wᵢ)]` over the
contracts satisfying (22.24)–(22.25). -/
noncomputable def hi_T (M : HIModel) (f : ℝ → ℝ) (v : ℝ) : ℝ := sSup (hi_vals M f v)

/-- Miao, p. 789: the constant contract `cᵢ = b(v)`, `wᵢ = v` is incentive compatible and
delivers the promised utility `v`. -/
theorem hi_const_feasible (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    hi_Feasible M v (fun _ => hi_b M v) (fun _ => v) := by
  refine ⟨fun i j => by unfold hi_C; simp, ?_, fun _ => hv⟩
  unfold hi_agentValue
  have := hi_b_spec M hv
  unfold hi_Bfun at this
  simp only [mul_add, Finset.sum_add_distrib, this, hi_sum_const]
  ring

/-- The principal's value of the constant contract is `−b(v) + β f(v)`. -/
theorem hi_const_value (M : HIModel) (f : ℝ → ℝ) (v : ℝ) :
    hi_principalValue M f (fun _ => hi_b M v) (fun _ => v) = -hi_b M v + M.β * f v := by
  unfold hi_principalValue; exact hi_sum_const M _

/-- Miao, p. 789: a feasible contract never gives the principal more than the first-best bound
`U(v)`, when the continuation is below `U` (Jensen's inequality for `u`). -/
theorem hi_principal_le_U (M : HIModel) {f : ℝ → ℝ} (hf : ∀ w < hi_vmax M, f w ≤ hi_U M w)
    {v : ℝ} {c w : Fin (M.N + 1) → ℝ} (h : hi_Feasible M v c w) :
    hi_principalValue M f c w ≤ hi_U M v := by
  obtain ⟨-, hpk, hw⟩ := h
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hv : v < hi_vmax M := hpk ▸ hi_agentValue_lt_vmax M hw
  set y : Fin (M.N + 1) → ℝ := fun i => hi_cstar M (w i) with hydef
  have hy : ∀ i, M.u (y i) = (1 - M.β) * w i := fun i => hi_cstar_spec M (hw i)
  set z : Fin (M.N + 1) → ℝ := fun i => (1 - M.β) * (M.θ i + c i) + M.β * y i with hzdef
  -- two-point concavity
  have hA : ∀ i, (1 - M.β) * M.u (M.θ i + c i) + M.β * M.u (y i) ≤ M.u (z i) := fun i => by
    have := M.u_strictConcave.concaveOn.2 (Set.mem_univ (M.θ i + c i)) (Set.mem_univ (y i))
      h1.le M.β_pos.le (by ring)
    simpa only [smul_eq_mul] using this
  -- Jensen
  have hB := M.u_strictConcave.concaveOn.le_map_sum (t := Finset.univ) (w := M.prob)
    (p := z) (fun i _ => (M.prob_pos i).le) M.prob_sum (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hB
  have hC : (1 - M.β) * v ≤ ∑ i, M.prob i * M.u (z i) := by
    rw [← hpk]
    unfold hi_agentValue
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (hA i) (M.prob_pos i).le
    rw [hy i] at this
    nlinarith
  have hD : hi_cstar M v ≤ ∑ i, M.prob i * z i := by
    rw [← M.u_strictMono.le_iff_le, hi_cstar_spec M hv]
    linarith
  -- the principal's value against `U`
  have hE : hi_principalValue M f c w ≤ ∑ i, M.prob i * (-c i + M.β * hi_U M (w i)) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (by nlinarith [hf (w i) (hw i), M.β_pos]) (M.prob_pos i).le
  have hF : (1 - M.β) * ∑ i, M.prob i * (-c i + M.β * hi_U M (w i)) =
      hi_θbar M - ∑ i, M.prob i * z i := by
    unfold hi_θbar
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have e : ∀ i, (1 - M.β) * (M.prob i * (-c i + M.β * hi_U M (w i))) =
        M.prob i * M.θ i - M.prob i * z i + M.β * (M.prob i * (hi_θbar M - M.θ i)) := by
      intro i
      simp only [hzdef, hydef, hi_U]
      field_simp
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    have : ∑ i, M.prob i * (hi_θbar M - M.θ i) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, hi_sum_const, hi_θbar]
      ring
    rw [this, mul_zero, add_zero]
  have hG : hi_U M v = (hi_θbar M - hi_cstar M v) / (1 - M.β) := rfl
  rw [hG, le_div_iff₀ h1]
  have := mul_le_mul_of_nonneg_left hE h1.le
  linarith

/-- The set of values is nonempty on `(−∞, vmax)`. -/
theorem hi_vals_nonempty (M : HIModel) (f : ℝ → ℝ) {v : ℝ} (hv : v < hi_vmax M) :
    (hi_vals M f v).Nonempty :=
  ⟨_, _, _, hi_const_feasible M hv, rfl⟩

/-- The set of values is bounded above by `U(v)` when `f ≤ U`. -/
theorem hi_vals_bddAbove (M : HIModel) {f : ℝ → ℝ} (hf : ∀ w < hi_vmax M, f w ≤ hi_U M w)
    (v : ℝ) : BddAbove (hi_vals M f v) :=
  ⟨hi_U M v, by rintro _ ⟨c, w, h, rfl⟩; exact hi_principal_le_U M hf h⟩

/-- The value of any feasible contract is at most `Tf(v)`. -/
theorem hi_le_T (M : HIModel) {f : ℝ → ℝ} (hf : ∀ w < hi_vmax M, f w ≤ hi_U M w) {v : ℝ}
    {c w : Fin (M.N + 1) → ℝ} (h : hi_Feasible M v c w) :
    hi_principalValue M f c w ≤ hi_T M f v :=
  le_csSup (hi_vals_bddAbove M hf v) ⟨c, w, h, rfl⟩

/-- **(22.26)** (Miao, p. 789). `T` maps the space `F` of functions between the bounds into
itself: `−b(v)/(1 − β) ≤ Tf(v) ≤ Σ πᵢ [θᵢ − c*(v)]/(1 − β)`. -/
theorem eq_22_26 (M : HIModel) {f : ℝ → ℝ} (hf : hi_InF M f) : hi_InF M (hi_T M f) := by
  intro v hv
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  constructor
  · have := hi_le_T M (fun w hw => (hf w hw).2) (hi_const_feasible M hv)
    rw [hi_const_value] at this
    have hL := (hf v hv).1
    unfold hi_L at hL ⊢
    have e : -hi_b M v / (1 - M.β) = -hi_b M v + M.β * (-hi_b M v / (1 - M.β)) := by
      field_simp; ring
    rw [e]
    nlinarith [M.β_pos]
  · exact csSup_le (hi_vals_nonempty M f hv) (by
      rintro _ ⟨c, w, h, rfl⟩; exact hi_principal_le_U M (fun w hw => (hf w hw).2) h)

/-- Blackwell's monotonicity and discounting (Miao, p. 792): if `f ≤ g + ε` on `(−∞, vmax)`,
then `Tf ≤ Tg + βε`. -/
theorem hi_T_le_add (M : HIModel) {f g : ℝ → ℝ} (hg : hi_InF M g) {ε : ℝ}
    (hfg : ∀ w < hi_vmax M, f w ≤ g w + ε) {v : ℝ} (hv : v < hi_vmax M) :
    hi_T M f v ≤ hi_T M g v + M.β * ε := by
  refine csSup_le (hi_vals_nonempty M f hv) ?_
  rintro _ ⟨c, w, h, rfl⟩
  have h2 := hi_le_T M (fun w hw => (hg w hw).2) h
  have h3 : hi_principalValue M f c w ≤ hi_principalValue M g c w + M.β * ε := by
    unfold hi_principalValue
    rw [← hi_sum_const M (M.β * ε), ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (hfg (w i) (h.2.2 i)) M.β_pos.le
    nlinarith [M.prob_pos i]
  linarith

/-- Miao, p. 792: `T` is a contraction of modulus `β` in the sup distance on `F`. -/
theorem hi_T_abs_le (M : HIModel) {f g : ℝ → ℝ} (hf : hi_InF M f) (hg : hi_InF M g) {ε : ℝ}
    (hfg : ∀ w < hi_vmax M, |f w - g w| ≤ ε) {v : ℝ} (hv : v < hi_vmax M) :
    |hi_T M f v - hi_T M g v| ≤ M.β * ε := by
  have a := hi_T_le_add M hg (f := f) (ε := ε)
    (fun w hw => by linarith [(abs_le.1 (hfg w hw)).2]) hv
  have b := hi_T_le_add M hf (f := g) (ε := ε)
    (fun w hw => by linarith [(abs_le.1 (hfg w hw)).1]) hv
  rw [abs_le]; constructor <;> linarith

/-- Two functions in `F` are within `(θ̄ − θ₁)/(1 − β)` of each other. -/
theorem hi_InF_abs_sub (M : HIModel) {f g : ℝ → ℝ} (hf : hi_InF M f) (hg : hi_InF M g)
    {v : ℝ} (hv : v < hi_vmax M) : |f v - g v| ≤ (hi_θbar M - M.θ 0) / (1 - M.β) := by
  have := hi_U_sub_L_le M hv
  rw [abs_le]; constructor <;> linarith [hf v hv, hg v hv]

/-- The iterates `Pₖ = Tᵏ L`. -/
noncomputable def hi_Pk (M : HIModel) (k : ℕ) : ℝ → ℝ := (hi_T M)^[k] (hi_L M)

/-- The lower bound lies in `F`. -/
theorem hi_L_InF (M : HIModel) : hi_InF M (hi_L M) := by
  intro v hv
  refine ⟨le_rfl, ?_⟩
  have := hi_U_sub_L_le M hv
  have h := hi_b_le_cstar M hv
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_U hi_L
  rw [div_le_div_iff_of_pos_right h1]
  -- `−b ≤ θ̄ − c*`: `c* ≤ θₙ + b ≤ ...`; use `u(c*) = B(b) ≤ u(θ̄ + b)` by Jensen
  have hJ := M.u_strictConcave.concaveOn.le_map_sum (t := Finset.univ) (w := M.prob)
    (p := fun i => M.θ i + hi_b M v) (fun i _ => (M.prob_pos i).le) M.prob_sum
    (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hJ
  have hB := hi_b_spec M hv
  unfold hi_Bfun at hB
  rw [hB, ← hi_cstar_spec M hv, M.u_strictMono.le_iff_le] at hJ
  have e : ∑ i, M.prob i * (M.θ i + hi_b M v) = hi_θbar M + hi_b M v := by
    simp only [mul_add, Finset.sum_add_distrib, hi_sum_const, hi_θbar]
  linarith

/-- Every iterate lies in `F`. -/
theorem hi_Pk_InF (M : HIModel) (k : ℕ) : hi_InF M (hi_Pk M k) := by
  induction k with
  | zero => exact hi_L_InF M
  | succ k ih =>
    unfold hi_Pk at *
    rw [Function.iterate_succ_apply']
    exact eq_22_26 M ih

/-- Miao, p. 792: `|Pₖ₊₁ − Pₖ| ≤ K βᵏ` on `(−∞, vmax)`, `K = (θ̄ − θ₁)/(1 − β)`. -/
theorem hi_Pk_succ_abs (M : HIModel) (k : ℕ) {v : ℝ} (hv : v < hi_vmax M) :
    |hi_Pk M (k + 1) v - hi_Pk M k v| ≤ (hi_θbar M - M.θ 0) / (1 - M.β) * M.β ^ k := by
  induction k generalizing v with
  | zero => simpa using hi_InF_abs_sub M (hi_Pk_InF M 1) (hi_Pk_InF M 0) hv
  | succ k ih =>
    have e1 : hi_Pk M (k + 1 + 1) = hi_T M (hi_Pk M (k + 1)) := by
      unfold hi_Pk; rw [Function.iterate_succ_apply']
    have e2 : hi_Pk M (k + 1) = hi_T M (hi_Pk M k) := by
      unfold hi_Pk; rw [Function.iterate_succ_apply']
    have := hi_T_abs_le M (hi_Pk_InF M (k + 1)) (hi_Pk_InF M k) (fun w hw => ih hw) hv
    rw [← e1, ← e2] at this
    have e3 : M.β * ((hi_θbar M - M.θ 0) / (1 - M.β) * M.β ^ k) =
        (hi_θbar M - M.θ 0) / (1 - M.β) * M.β ^ (k + 1) := by ring
    linarith

/-- Miao, p. 792: the iterates converge on `(−∞, vmax)`. -/
theorem hi_Pk_cauchy (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    CauchySeq fun k => hi_Pk M k v :=
  cauchySeq_of_le_geometric M.β _ M.β_lt_one fun k => by
    rw [Real.dist_eq, abs_sub_comm]; exact hi_Pk_succ_abs M k hv

/-- The value function `P = lim Tᵏ L`. -/
noncomputable def hi_P (M : HIModel) (v : ℝ) : ℝ := limUnder atTop fun k => hi_Pk M k v

/-- `Pₖ(v) → P(v)` on `(−∞, vmax)`. -/
theorem hi_Pk_tendsto (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    Tendsto (fun k => hi_Pk M k v) atTop (𝓝 (hi_P M v)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hi_Pk_cauchy M hv))

/-- `|P − Pₖ| ≤ K βᵏ / (1 − β)`. -/
theorem hi_P_abs_sub (M : HIModel) (k : ℕ) {v : ℝ} (hv : v < hi_vmax M) :
    |hi_Pk M k v - hi_P M v| ≤ (hi_θbar M - M.θ 0) / (1 - M.β) * M.β ^ k / (1 - M.β) := by
  rw [← Real.dist_eq]
  exact dist_le_of_le_geometric_of_tendsto M.β _ M.β_lt_one
    (fun k => by rw [Real.dist_eq, abs_sub_comm]; exact hi_Pk_succ_abs M k hv)
    (hi_Pk_tendsto M hv) k

/-- `P` lies in `F`. -/
theorem hi_P_InF (M : HIModel) : hi_InF M (hi_P M) := fun v hv =>
  ⟨ge_of_tendsto' (hi_Pk_tendsto M hv) fun k => (hi_Pk_InF M k v hv).1,
    le_of_tendsto' (hi_Pk_tendsto M hv) fun k => (hi_Pk_InF M k v hv).2⟩

/-- `P` is a fixed point of `T` on `(−∞, vmax)`: the Bellman equation (22.23). -/
theorem hi_P_fixed (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) : hi_T M (hi_P M) v = hi_P M v := by
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  set K := (hi_θbar M - M.θ 0) / (1 - M.β)
  have hlim : Tendsto (fun k => hi_Pk M (k + 1) v) atTop (𝓝 (hi_T M (hi_P M) v)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hb : ∀ k, dist (hi_Pk M (k + 1) v) (hi_T M (hi_P M) v) ≤
        M.β * (K * M.β ^ k / (1 - M.β)) := fun k => by
      have e : hi_Pk M (k + 1) = hi_T M (hi_Pk M k) := by
        unfold hi_Pk; rw [Function.iterate_succ_apply']
      rw [e, Real.dist_eq]
      exact hi_T_abs_le M (hi_Pk_InF M k) (hi_P_InF M) (fun w hw => hi_P_abs_sub M k hw) hv
    refine squeeze_zero (fun _ => dist_nonneg) hb ?_
    have : Tendsto (fun k => M.β * (K * M.β ^ k / (1 - M.β))) atTop
        (𝓝 (M.β * (K * 0 / (1 - M.β)))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one M.β_pos.le M.β_lt_one).const_mul K |>.div_const
        _).const_mul _
    simpa using this
  exact tendsto_nhds_unique hlim ((hi_Pk_tendsto M hv).comp (tendsto_add_atTop_nat 1))

/-- Uniqueness: two fixed points of `T` in `F` agree on `(−∞, vmax)`. -/
theorem hi_fixed_unique (M : HIModel) {P Q : ℝ → ℝ} (hP : hi_InF M P) (hQ : hi_InF M Q)
    (hPf : ∀ v < hi_vmax M, hi_T M P v = P v) (hQf : ∀ v < hi_vmax M, hi_T M Q v = Q v)
    {v : ℝ} (hv : v < hi_vmax M) : P v = Q v := by
  set K := (hi_θbar M - M.θ 0) / (1 - M.β)
  have key : ∀ k : ℕ, ∀ w < hi_vmax M, |P w - Q w| ≤ K * M.β ^ k := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hi_InF_abs_sub M hP hQ hw
    | succ k ih =>
      intro w hw
      have := hi_T_abs_le M hP hQ ih hw
      rw [hPf w hw, hQf w hw] at this
      calc _ ≤ _ := this
        _ = _ := by ring
  have hlim : Tendsto (fun k => K * M.β ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_pos.le M.β_lt_one).const_mul K
  have h0 : |P v - Q v| ≤ 0 := ge_of_tendsto' hlim fun k => key k v hv
  have := abs_nonpos_iff.1 h0
  linarith

/-- `b(v)` is increasing on `(−∞, vmax)`. -/
theorem hi_b_mono (M : HIModel) {v v' : ℝ} (hv' : v' < hi_vmax M) (hvv : v ≤ v') :
    hi_b M v ≤ hi_b M v' := by
  have hv : v < hi_vmax M := lt_of_le_of_lt hvv hv'
  rw [← (hi_Bfun_strictMono M).le_iff_le, hi_b_spec M hv, hi_b_spec M hv']
  exact mul_le_mul_of_nonneg_left hvv (by linarith [M.β_lt_one])

/-- The lower bound `L` is decreasing. -/
theorem hi_L_antitoneOn (M : HIModel) : AntitoneOn (hi_L M) (Set.Iio (hi_vmax M)) := by
  intro v _ v' hv' hvv
  have := hi_b_mono M hv' hvv
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_L
  exact div_le_div_of_nonneg_right (by linarith) h1.le

/-- Miao, p. 792: "`T` maps a decreasing function to a decreasing function". Given a contract
feasible at `v'`, lowering every `wᵢ` by `(v' − v)/β` gives a contract feasible at `v ≤ v'`
that is at least as good for the principal. -/
theorem hi_T_antitoneOn (M : HIModel) {f : ℝ → ℝ} (hf : hi_InF M f)
    (hfa : AntitoneOn f (Set.Iio (hi_vmax M))) : AntitoneOn (hi_T M f) (Set.Iio (hi_vmax M)) := by
  intro v hv v' hv' hvv
  refine csSup_le (hi_vals_nonempty M f hv') ?_
  rintro _ ⟨c, w, ⟨hic, hpk, hw⟩, rfl⟩
  set k := -((v' - v) / M.β)
  have hk : k ≤ 0 := by
    have : 0 ≤ (v' - v) / M.β := div_nonneg (by linarith) M.β_pos.le
    linarith
  have hfeas : hi_Feasible M v c (fun l => w l + k) := by
    refine ⟨fun i j => by rw [hi_C_shift]; exact hic i j, ?_, fun i => by linarith [hw i]⟩
    rw [hi_agentValue_shift, hpk]
    have : M.β * k = -(v' - v) := by
      simp only [k]; rw [mul_neg, mul_div_cancel₀ _ M.β_pos.ne']
    linarith
  refine le_trans ?_ (hi_le_T M (fun w hw => (hf w hw).2) hfeas)
  unfold hi_principalValue
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (M.prob_pos i).le
  have := hfa (show w i + k ∈ Set.Iio (hi_vmax M) by
    simp only [Set.mem_Iio]; linarith [hw i]) (hw i) (by linarith)
  nlinarith [M.β_pos]

/-- The iterates are decreasing. -/
theorem hi_Pk_antitoneOn (M : HIModel) (k : ℕ) :
    AntitoneOn (hi_Pk M k) (Set.Iio (hi_vmax M)) := by
  induction k with
  | zero => exact hi_L_antitoneOn M
  | succ k ih =>
    have e : hi_Pk M (k + 1) = hi_T M (hi_Pk M k) := by
      unfold hi_Pk; rw [Function.iterate_succ_apply']
    rw [e]
    exact hi_T_antitoneOn M (hi_Pk_InF M k) ih

/-- **Proposition 22.3.1** (Miao, p. 791), the contraction part. There is a function `P` in the
space `F` of functions lying between the bounds (22.26) that solves the Bellman equation
(22.23) on `(−∞, vmax)`; any other solution in `F` agrees with it on `(−∞, vmax)`; and `P` is
decreasing. (Concavity is `proposition_22_3_1_concave`; strict concavity, continuous
differentiability and the uniqueness of the policies are not proved; see
`docs/HI-corrections.md`.) -/
theorem proposition_22_3_1 (M : HIModel) :
    ∃ P : ℝ → ℝ, hi_InF M P ∧ (∀ v < hi_vmax M, hi_T M P v = P v) ∧
      (∀ Q : ℝ → ℝ, hi_InF M Q → (∀ v < hi_vmax M, hi_T M Q v = Q v) →
        ∀ v < hi_vmax M, Q v = P v) ∧ AntitoneOn P (Set.Iio (hi_vmax M)) := by
  refine ⟨hi_P M, hi_P_InF M, fun v hv => hi_P_fixed M hv, fun Q hQ hQf v hv =>
    hi_fixed_unique M hQ (hi_P_InF M) hQf (fun w hw => hi_P_fixed M hw) hv, ?_⟩
  intro v hv v' hv' hvv
  exact le_of_tendsto_of_tendsto' (hi_Pk_tendsto M hv') (hi_Pk_tendsto M hv)
    fun k => hi_Pk_antitoneOn M k hv hv' hvv

/-- Miao, p. 793: "`P(v) = lim Pₖ(v)` is concave": a pointwise limit of concave functions is
concave. -/
theorem hi_concaveOn_of_tendsto {s : Set ℝ} {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ}
    (hF : ∀ k, ConcaveOn ℝ s (F k)) (hG : ∀ x ∈ s, Tendsto (fun k => F k x) atTop (𝓝 (G x))) :
    ConcaveOn ℝ s G := by
  refine ⟨(hF 0).1, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : a • x + b • y ∈ s := (hF 0).1 hx hy ha hb hab
  simp only [smul_eq_mul] at hxy ⊢
  exact le_of_tendsto_of_tendsto' (((hG x hx).const_mul a).add ((hG y hy).const_mul b))
    (hG _ hxy) fun k => by simpa only [smul_eq_mul] using (hF k).2 hx hy ha hb hab

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal contracts: Propositions 22.3.2–22.3.3, (22.27)–(22.30), Lemma 22.3.3

Miao, §22.3.1–22.3.2, pp. 794–796.

* `assumption_22_3_2` (Assumption 22.3.2): the value function is strictly concave on
  `(−∞, vmax)`. `hi_Optimal M f v c w`: `(c, w)` attains the supremum in (22.23) against the
  continuation `f`.
* `hi_spread_reduction`: the "mean-preserving decrease in the spread" of the proofs of
  Propositions 22.3.1 and 22.3.2. Lowering the increment `w_k − w_{k−1}` of a monotone list of
  continuation values by `δ ≤ w_k − w_{k−1}` and adding the constant that keeps `Σ πᵢ wᵢ` raises
  `Σ πᵢ f(wᵢ)` strictly for a strictly concave `f`.
* `proposition_22_3_2`: in an optimal contract against a strictly concave continuation the local
  downward constraints bind; the local upward constraints then hold, and are slack whenever
  `cᵢ < cᵢ₋₁` (the book's "never bind"; see `docs/HI-corrections.md`).
* `proposition_22_3_3`: coinsurance, `u(θᵢ + cᵢ) + βwᵢ > u(θᵢ₋₁ + cᵢ₋₁) + βwᵢ₋₁` and
  `−cᵢ + βf(wᵢ) ≥ −cᵢ₋₁ + βf(wᵢ₋₁)`.
* `hi_FOC` collects the first-order conditions (22.27)–(22.29) (stated, as in the book, for given
  multipliers `λ`, `μᵢ`); `eq_22_30` derives the martingale property `Σ πᵢ P'(wᵢ) = P'(v)` from
  (22.28)–(22.29) by summing, and `hi_martingale_of_shift` proves (22.30) without multipliers by
  the argument on p. 796 (shift every `wᵢ` and use the envelope theorem).
* `lemma_22_3_3`: `w₁ < v < wₙ` (for `n ≥ 2`), from the first-order conditions, as in the book.
-/

namespace Miao.RecursiveContracts

open Finset Filter Topology

/-- **Assumption 22.3.2** (Miao, p. 794). The value function `P` is strictly concave on
`(−∞, vmax)`. -/
def assumption_22_3_2 (M : HIModel) (P : ℝ → ℝ) : Prop :=
  StrictConcaveOn ℝ (Set.Iio (hi_vmax M)) P

/-- `(c, w)` is an optimal contract at `v` against the continuation `f`: it is feasible and no
feasible contract gives the principal more. -/
def hi_Optimal (M : HIModel) (f : ℝ → ℝ) (v : ℝ) (c w : Fin (M.N + 1) → ℝ) : Prop :=
  hi_Feasible M v c w ∧
    ∀ c' w', hi_Feasible M v c' w' → hi_principalValue M f c' w' ≤ hi_principalValue M f c w

/-- A strictly concave function on a convex set has decreasing increments there. -/
theorem hi_incr_le_on {f : ℝ → ℝ} {s : Set ℝ} (hf : StrictConcaveOn ℝ s f) {x y d : ℝ}
    (hx : x ∈ s) (hyd : y + d ∈ s) (hxy : x ≤ y) (hd : 0 ≤ d) :
    f (y + d) - f y ≤ f (x + d) - f x := by
  rcases hxy.lt_or_eq with hxy | rfl
  · rcases hd.lt_or_eq with hd | rfl
    · have hoc := hf.1.ordConnected
      have hy : y ∈ s := hoc.out hx hyd ⟨hxy.le, by linarith⟩
      have hxd : x + d ∈ s := hoc.out hx hyd ⟨by linarith, by linarith⟩
      have h1 := hf.secant_strict_mono (a := x) (x := x + d) (y := y + d) hx hxd hyd
        (by linarith) (by linarith) (by linarith)
      have h2 := hf.secant_strict_mono (a := y + d) (x := x) (y := y) hyd hx hy
        (by linarith) (by linarith) hxy
      have e1 : (f (x + d) - f x) / (x + d - x) = (f (x + d) - f x) / d := by ring_nf
      have e2 : (f y - f (y + d)) / (y - (y + d)) = (f (y + d) - f y) / d := by
        rw [show y - (y + d) = -d by ring, div_neg, ← neg_div]; ring
      have e3 : (f x - f (y + d)) / (x - (y + d)) = (f (y + d) - f x) / (y + d - x) := by
        rw [show x - (y + d) = -(y + d - x) by ring, div_neg, ← neg_div]; ring
      rw [e1] at h1
      rw [e2, e3] at h2
      exact ((div_lt_div_iff_of_pos_right hd).1 (h2.trans h1)).le
    · simp
  · exact le_rfl

/-- For a strictly concave function, the slope on `[x₁, x₂]` exceeds the slope on `[x₃, x₄]`
when `x₁ < x₂ ≤ x₃ < x₄`. -/
theorem hi_slope_strict_anti {f : ℝ → ℝ} {s : Set ℝ} (hf : StrictConcaveOn ℝ s f)
    {x1 x2 x3 x4 : ℝ} (h1 : x1 ∈ s) (h4 : x4 ∈ s) (h12 : x1 < x2) (h23 : x2 ≤ x3)
    (h34 : x3 < x4) :
    (f x4 - f x3) / (x4 - x3) < (f x2 - f x1) / (x2 - x1) := by
  have hoc := hf.1.ordConnected
  rcases h23.lt_or_eq with h23 | rfl
  · have hx2 : x2 ∈ s := hoc.out h1 h4 ⟨h12.le, by linarith⟩
    have a := hf.slope_anti_adjacent h1 (hoc.out h1 h4 ⟨by linarith, by linarith⟩) h12 h23
    have b := hf.slope_anti_adjacent hx2 h4 h23 h34
    linarith
  · exact hf.slope_anti_adjacent h1 h4 h12 h34

/-- The probability mass `q = Σ_{j ≥ k} πⱼ` of the states at or above `k`. -/
noncomputable def hi_upperMass (M : HIModel) (k : Fin (M.N + 1)) : ℝ :=
  ∑ j, M.prob j * (if k ≤ j then 1 else 0)

/-- `0 < q < 1` when `k` is not the lowest state. -/
theorem hi_upperMass_bounds (M : HIModel) (i : Fin M.N) :
    0 < hi_upperMass M i.succ ∧ hi_upperMass M i.succ < 1 := by
  constructor
  · have := Finset.single_le_sum (f := fun j => M.prob j * (if i.succ ≤ j then (1 : ℝ) else 0))
      (fun j _ => by split_ifs <;> simp [(M.prob_pos j).le]) (Finset.mem_univ i.succ)
    simp only [le_refl, ↓reduceIte, mul_one] at this
    exact lt_of_lt_of_le (M.prob_pos _) this
  · have e : 1 - hi_upperMass M i.succ = ∑ j, M.prob j * (if i.succ ≤ j then 0 else 1) := by
      have h : ∑ j, M.prob j * (if i.succ ≤ j then (0 : ℝ) else 1) + hi_upperMass M i.succ = 1 := by
        unfold hi_upperMass
        rw [← Finset.sum_add_distrib]
        convert M.prob_sum using 1
        exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
      linarith
    have := Finset.single_le_sum (f := fun j => M.prob j * (if i.succ ≤ j then (0 : ℝ) else 1))
      (fun j _ => by split_ifs <;> simp [(M.prob_pos j).le]) (Finset.mem_univ i.castSucc)
    have hn : ¬ i.succ ≤ i.castSucc := not_le.2 Fin.castSucc_lt_succ
    simp only [hn, ↓reduceIte, mul_one] at this
    linarith [M.prob_pos i.castSucc]

/-- The spread-reduced continuation values: `w'ⱼ = wⱼ + δq − δ·1{k ≤ j}`. -/
noncomputable def hi_reduce (M : HIModel) (w : Fin (M.N + 1) → ℝ) (k : Fin (M.N + 1))
    (δ : ℝ) (j : Fin (M.N + 1)) : ℝ :=
  w j + δ * hi_upperMass M k - (if k ≤ j then δ else 0)

/-- The spread reduction keeps the mean `Σ πⱼ wⱼ`. -/
theorem hi_reduce_mean (M : HIModel) (w : Fin (M.N + 1) → ℝ) (k : Fin (M.N + 1)) (δ : ℝ) :
    ∑ j, M.prob j * hi_reduce M w k δ j = ∑ j, M.prob j * w j := by
  unfold hi_reduce
  have : ∀ j, M.prob j * (w j + δ * hi_upperMass M k - (if k ≤ j then δ else 0)) =
      M.prob j * w j + M.prob j * (δ * hi_upperMass M k) -
        δ * (M.prob j * (if k ≤ j then 1 else 0)) := fun j => by split_ifs <;> ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, hi_sum_const,
    ← Finset.mul_sum]
  unfold hi_upperMass
  ring

/-- Miao, pp. 793–794: the mean-preserving decrease in the spread. If `w` is monotone with
values in `(−∞, vmax)`, `k = i + 1` and `0 < δ ≤ w_k − w_{k−1}`, then the spread-reduced values
lie in `(−∞, vmax)` and `Σ πⱼ f(w'ⱼ) > Σ πⱼ f(wⱼ)` for `f` strictly concave on `(−∞, vmax)`. -/
theorem hi_spread_reduction (M : HIModel) {f : ℝ → ℝ}
    (hf : StrictConcaveOn ℝ (Set.Iio (hi_vmax M)) f) {w : Fin (M.N + 1) → ℝ}
    (hw : ∀ j, w j < hi_vmax M) (hmono : Monotone w) (i : Fin M.N) {δ : ℝ} (hδ : 0 < δ)
    (hδw : δ ≤ w i.succ - w i.castSucc) :
    (∀ j, hi_reduce M w i.succ δ j < hi_vmax M) ∧
      ∑ j, M.prob j * f (w j) < ∑ j, M.prob j * f (hi_reduce M w i.succ δ j) := by
  obtain ⟨hq0, hq1⟩ := hi_upperMass_bounds M i
  set q := hi_upperMass M i.succ
  set a := w i.castSucc
  set b := w i.succ
  set e := δ * (1 - q)
  have he : 0 < e := mul_pos hδ (by linarith)
  have hdq : 0 < δ * q := mul_pos hδ hq0
  have hab : a + δ * q ≤ b - e := by simp only [e]; nlinarith
  have hbV : b < hi_vmax M := hw _
  have hred : ∀ j, hi_reduce M w i.succ δ j =
      if i.succ ≤ j then w j - e else w j + δ * q := fun j => by
    unfold hi_reduce; split_ifs <;> simp only [e, q] <;> ring
  -- position of each state relative to the reduced increment
  have hlow : ∀ j, ¬ i.succ ≤ j → w j ≤ a := fun j hj => by
    apply hmono
    rw [not_le] at hj
    exact Fin.le_castSucc_iff.2 hj
  have hhigh : ∀ j, i.succ ≤ j → b ≤ w j := fun j hj => hmono hj
  refine ⟨fun j => ?_, ?_⟩
  · rw [hred j]
    split_ifs with hj
    · linarith [hw j]
    · linarith [hlow j hj]
  -- the gains below and the losses above
  set gainL := f (a + δ * q) - f a
  set lossU := f b - f (b - e)
  have hterm : ∀ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) ≤
      M.prob j * (f (hi_reduce M w i.succ δ j) - f (w j)) := fun j => by
    refine mul_le_mul_of_nonneg_left ?_ (M.prob_pos j).le
    rw [hred j]
    split_ifs with hj
    · have := hi_incr_le_on hf (x := b - e) (y := w j - e) (d := e)
        (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio]; linarith [hw j])
        (by linarith [hhigh j hj]) he.le
      simp only [sub_add_cancel] at this
      simp only [lossU]; linarith
    · have := hi_incr_le_on hf (x := w j) (y := a) (d := δ * q)
        (by simp only [Set.mem_Iio]; linarith [hw j]) (by simp only [Set.mem_Iio]; linarith)
        (hlow j hj) hdq.le
      simp only [gainL]; linarith
  have hsum : ∑ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) =
      gainL - (gainL + lossU) * q := by
    have : ∀ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) =
        M.prob j * gainL - (gainL + lossU) * (M.prob j * (if i.succ ≤ j then 1 else 0)) :=
        fun j => by
      split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, hi_sum_const, ← Finset.mul_sum]
    rfl
  -- strict concavity: the slope below beats the slope above
  have hslope := hi_slope_strict_anti hf (x1 := a) (x2 := a + δ * q) (x3 := b - e) (x4 := b)
    (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio]; linarith)
    (by linarith) hab (by linarith)
  rw [show b - (b - e) = e by ring, show a + δ * q - a = δ * q by ring,
    div_lt_div_iff₀ he hdq] at hslope
  have hpos : 0 < gainL - (gainL + lossU) * q := by
    have h3 : lossU * (δ * q) < gainL * (δ * (1 - q)) := hslope
    have : δ * (gainL - (gainL + lossU) * q) = gainL * (δ * (1 - q)) - lossU * (δ * q) := by ring
    have h4 : 0 < δ * (gainL - (gainL + lossU) * q) := by linarith
    exact pos_of_mul_pos_right h4 hδ.le
  have htot := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
  rw [hsum] at htot
  simp only [mul_sub, Finset.sum_sub_distrib] at htot
  linarith

/-- `Σ πⱼ (a xⱼ) = a Σ πⱼ xⱼ`. -/
theorem hi_sum_mul_left (M : HIModel) (a : ℝ) (x : Fin (M.N + 1) → ℝ) :
    ∑ j, M.prob j * (a * x j) = a * ∑ j, M.prob j * x j := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring

/-- **Proposition 22.3.2** (Miao, p. 794). In an optimal contract against a strictly concave
continuation (Assumption 22.3.2 for `f = P`), the local downward incentive constraints bind,
`Cᵢ,ᵢ₋₁ = 0`. Consequently the local upward constraints `Cᵢ₋₁,ᵢ ≥ 0` hold, and they are slack
(`Cᵢ₋₁,ᵢ > 0`) whenever `cᵢ < cᵢ₋₁`. -/
theorem proposition_22_3_2 (M : HIModel) {f : ℝ → ℝ} (hf : assumption_22_3_2 M f) {v : ℝ}
    {c w : Fin (M.N + 1) → ℝ} (hopt : hi_Optimal M f v c w) (i : Fin M.N) :
    hi_C M c w i.succ i.castSucc = 0 ∧ 0 ≤ hi_C M c w i.castSucc i.succ ∧
      (c i.succ < c i.castSucc → 0 < hi_C M c w i.castSucc i.succ) := by
  obtain ⟨⟨hic, hpk, hw⟩, hbest⟩ := hopt
  obtain ⟨hcm, hwm⟩ := lemma_22_3_1 M c w hic
  have hci : c i.succ ≤ c i.castSucc := hcm (Fin.castSucc_lt_succ).le
  have hbind : hi_C M c w i.succ i.castSucc = 0 := by
    by_contra hne
    have hCpos : 0 < hi_C M c w i.succ i.castSucc := lt_of_le_of_ne (hic _ _) (Ne.symm hne)
    set δ := hi_C M c w i.succ i.castSucc / M.β
    have hδ : 0 < δ := div_pos hCpos M.β_pos
    have hβδ : M.β * δ = hi_C M c w i.succ i.castSucc := by
      simp only [δ]; rw [mul_div_cancel₀ _ M.β_pos.ne']
    have hu : M.u (M.θ i.succ + c i.succ) ≤ M.u (M.θ i.succ + c i.castSucc) :=
      M.u_strictMono.monotone (by linarith)
    have hδw : δ ≤ w i.succ - w i.castSucc := by
      have : hi_C M c w i.succ i.castSucc ≤ M.β * (w i.succ - w i.castSucc) := by
        unfold hi_C; nlinarith
      nlinarith [M.β_pos]
    obtain ⟨hw', hgain⟩ := hi_spread_reduction M hf hw hwm i hδ hδw
    set w' := hi_reduce M w i.succ δ
    -- the new contract is incentive compatible
    have hC' : ∀ j l, hi_C M c w' j l = hi_C M c w j l +
        M.β * ((if i.succ ≤ l then δ else 0) - (if i.succ ≤ j then δ else 0)) := by
      intro j l; simp only [hi_C, w', hi_reduce]; ring
    have hloc : hi_LocalIC M c w' := by
      intro l
      by_cases hl : l = i
      · subst hl
        have hn : ¬ l.succ ≤ l.castSucc := not_le.2 Fin.castSucc_lt_succ
        have h0 : hi_C M c w' l.succ l.castSucc = 0 := by
          rw [hC']; simp only [hn, le_refl, ↓reduceIte]; linarith
        exact ⟨h0.ge, (hi_upward_of_binding M c w' Fin.castSucc_lt_succ h0 hci).1⟩
      · have hiff : (i.succ ≤ l.succ ↔ i.succ ≤ l.castSucc) := by
          rw [Fin.le_def, Fin.le_def]
          simp only [Fin.val_succ, Fin.val_castSucc]
          have : l.val ≠ i.val := fun h => hl (Fin.ext h)
          omega
        constructor
        · rw [hC']
          by_cases h : i.succ ≤ l.castSucc
          · simp only [h, hiff.2 h, ↓reduceIte, sub_self, mul_zero, add_zero]; exact hic _ _
          · have h' : ¬ i.succ ≤ l.succ := fun h'' => h (hiff.1 h'')
            simp only [h, h', ↓reduceIte, sub_self, mul_zero, add_zero]; exact hic _ _
        · rw [hC']
          by_cases h : i.succ ≤ l.castSucc
          · simp only [h, hiff.2 h, ↓reduceIte, sub_self, mul_zero, add_zero]; exact hic _ _
          · have h' : ¬ i.succ ≤ l.succ := fun h'' => h (hiff.1 h'')
            simp only [h, h', ↓reduceIte, sub_self, mul_zero, add_zero]; exact hic _ _
    have hfeas : hi_Feasible M v c w' := by
      refine ⟨lemma_22_3_2 M c w' hloc, ?_, hw'⟩
      rw [← hpk]
      unfold hi_agentValue
      have h1 := hi_reduce_mean M w i.succ δ
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [hi_sum_mul_left M M.β w', hi_sum_mul_left M M.β w, h1]
    have hle := hbest c w' hfeas
    unfold hi_principalValue at hle
    have : ∑ j, M.prob j * (-c j + M.β * f (w j)) < ∑ j, M.prob j * (-c j + M.β * f (w' j)) := by
      simp only [mul_add, Finset.sum_add_distrib, add_lt_add_iff_left]
      rw [hi_sum_mul_left M M.β (fun j => f (w j)), hi_sum_mul_left M M.β (fun j => f (w' j))]
      exact mul_lt_mul_of_pos_left hgain M.β_pos
    linarith
  exact ⟨hbind, (hi_upward_of_binding M c w Fin.castSucc_lt_succ hbind hci).1,
    (hi_upward_of_binding M c w Fin.castSucc_lt_succ hbind hci).2⟩

/-- Changing one term of a weighted sum. -/
theorem hi_sum_ite (M : HIModel) (g : Fin (M.N + 1) → ℝ) (k : Fin (M.N + 1)) (x : ℝ) :
    ∑ j, M.prob j * (if j = k then x else g j) =
      ∑ j, M.prob j * g j + M.prob k * (x - g k) := by
  have : ∀ j, M.prob j * (if j = k then x else g j) =
      M.prob j * g j + (if j = k then M.prob k * (x - g k) else 0) := by
    intro j; split_ifs with h
    · subst h; ring
    · ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- **Proposition 22.3.3** (Miao, p. 795). In an optimal contract against a strictly concave
continuation, `u(θᵢ + cᵢ) + βwᵢ > u(θᵢ₋₁ + cᵢ₋₁) + βwᵢ₋₁` and
`−cᵢ + βf(wᵢ) ≥ −cᵢ₋₁ + βf(wᵢ₋₁)`. -/
theorem proposition_22_3_3 (M : HIModel) {f : ℝ → ℝ} (hf : assumption_22_3_2 M f) {v : ℝ}
    {c w : Fin (M.N + 1) → ℝ} (hopt : hi_Optimal M f v c w) (i : Fin M.N) :
    M.u (M.θ i.castSucc + c i.castSucc) + M.β * w i.castSucc <
        M.u (M.θ i.succ + c i.succ) + M.β * w i.succ ∧
      -c i.castSucc + M.β * f (w i.castSucc) ≤ -c i.succ + M.β * f (w i.succ) := by
  have hbind := (proposition_22_3_2 M hf hopt i).1
  obtain ⟨⟨hic, hpk, hw⟩, hbest⟩ := hopt
  have hθ : M.θ i.castSucc < M.θ i.succ := M.θ_strictMono Fin.castSucc_lt_succ
  have heq : M.u (M.θ i.succ + c i.succ) + M.β * w i.succ =
      M.u (M.θ i.succ + c i.castSucc) + M.β * w i.castSucc := by
    unfold hi_C at hbind; linarith
  refine ⟨?_, ?_⟩
  · rw [heq]
    have := M.u_strictMono (show M.θ i.castSucc + c i.castSucc < M.θ i.succ + c i.castSucc by
      linarith)
    linarith
  · by_contra hlt
    push Not at hlt
    -- replace `(c_i, w_i)` by `(c_{i−1}, w_{i−1})`
    set k := i.succ
    set r : Fin (M.N + 1) → Fin (M.N + 1) := fun j => if j = k then i.castSucc else j
    set c' := fun j => c (r j)
    set w' := fun j => w (r j)
    have hown : ∀ j, M.u (M.θ j + c' j) + M.β * w' j = M.u (M.θ j + c j) + M.β * w j := by
      intro j
      simp only [c', w', r]
      split_ifs with h
      · subst h; exact heq.symm
      · rfl
    have hic' : hi_IC M c' w' := by
      intro j l
      have := hic j (r l)
      unfold hi_C at this ⊢
      rw [hown j]
      exact this
    have hpk' : hi_agentValue M c' w' = v := by
      rw [← hpk]; unfold hi_agentValue
      exact Finset.sum_congr rfl fun j _ => by rw [hown j]
    have hw'' : ∀ j, w' j < hi_vmax M := fun j => hw (r j)
    have hle := hbest c' w' ⟨hic', hpk', hw''⟩
    unfold hi_principalValue at hle
    have e : ∀ j, -c' j + M.β * f (w' j) = if j = k then -c i.castSucc + M.β * f (w i.castSucc)
        else -c j + M.β * f (w j) := fun j => by
      simp only [c', w', r]; split_ifs <;> rfl
    simp only [e] at hle
    rw [hi_sum_ite M (fun j => -c j + M.β * f (w j))] at hle
    have := mul_lt_mul_of_pos_left (sub_pos.2 hlt) (M.prob_pos k)
    linarith

/-- The book's `θᵢ₊₁` in (22.27), with the convention `θₙ₊₁ = θₙ` (it is multiplied by
`μₙ₊₁ = 0`). -/
def hi_θsucc (M : HIModel) (i : Fin (M.N + 1)) : ℝ := M.θ ⟨min (i.val + 1) M.N, by omega⟩

/-- Miao, (22.27)–(22.29), p. 795: the first-order conditions for an optimal contract `(c, w)` at
`v`, with multipliers `λ` for (22.25) and `μᵢ` for `Cᵢ,ᵢ₋₁ ≥ 0`, `μ₁ = μₙ₊₁ = 0`; `u'` and `P'`
are the derivatives of `u` and `P`. The multipliers are indexed from `0`: `μ 0` is the book's
`μ₁`, `μ (N + 1)` its `μₙ₊₁`. -/
def hi_FOC (M : HIModel) (u' dP : ℝ → ℝ) (v : ℝ) (c w : Fin (M.N + 1) → ℝ) (lam : ℝ)
    (μ : ℕ → ℝ) : Prop :=
  μ 0 = 0 ∧ μ (M.N + 1) = 0 ∧
    (∀ i : Fin (M.N + 1), M.prob i * (1 - lam * u' (M.θ i + c i)) =
      μ i.val * u' (M.θ i + c i) - μ (i.val + 1) * u' (hi_θsucc M i + c i)) ∧
    (∀ i : Fin (M.N + 1), M.prob i * (dP (w i) + lam) = μ (i.val + 1) - μ i.val) ∧
    dP v = -lam

/-- **(22.30)** (Miao, p. 795). Summing (22.28) over `i` and using (22.29):
`Σ πᵢ P'(wᵢ) = P'(v)`, so `P'(vₜ)` is a martingale. -/
theorem eq_22_30 (M : HIModel) {u' dP : ℝ → ℝ} {v lam : ℝ} {c w : Fin (M.N + 1) → ℝ}
    {μ : ℕ → ℝ} (h : hi_FOC M u' dP v c w lam μ) :
    ∑ i, M.prob i * dP (w i) = dP v := by
  obtain ⟨h0, hn, -, h28, h29⟩ := h
  have hsum : ∑ i : Fin (M.N + 1), M.prob i * (dP (w i) + lam) = 0 := by
    rw [Finset.sum_congr rfl fun i _ => h28 i]
    rw [Fin.sum_univ_eq_sum_range (fun i => μ (i + 1) - μ i), Finset.sum_range_sub, hn, h0]
    ring
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, M.prob_sum, one_mul] at hsum
  linarith

/-- Miao, (22.30) and p. 796, without multipliers: if `P` solves the Bellman equation in `F`,
`(c, w)` attains `P(v)`, and `P` is differentiable at `v` and at each `wᵢ`, then
`Σ πᵢ P'(wᵢ) = P'(v)`. Raising every `wᵢ` by `ε` keeps incentive compatibility and delivers
`v + βε`, so `ε ↦ P(v + βε) − Σ πᵢ [−cᵢ + βP(wᵢ + ε)]` has a local minimum at `0`. -/
theorem hi_martingale_of_shift (M : HIModel) {P dP : ℝ → ℝ} (hP : hi_InF M P)
    (hfix : ∀ v < hi_vmax M, hi_T M P v = P v) {v : ℝ} {c w : Fin (M.N + 1) → ℝ}
    (hfeas : hi_Feasible M v c w) (hval : hi_principalValue M P c w = P v)
    (hdv : HasDerivAt P (dP v) v) (hdw : ∀ i, HasDerivAt P (dP (w i)) (w i)) :
    ∑ i, M.prob i * dP (w i) = dP v := by
  obtain ⟨hic, hpk, hw⟩ := hfeas
  have hv : v < hi_vmax M := hpk ▸ hi_agentValue_lt_vmax M hw
  set g : ℝ → ℝ := fun ε => P (v + M.β * ε) - hi_principalValue M P c (fun l => w l + ε)
  -- the shifted contract is feasible for small `ε`
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), (∀ i, w i + ε < hi_vmax M) ∧ v + M.β * ε < hi_vmax M := by
    refine (Filter.eventually_all.2 fun i => ?_).and ?_
    · exact (isOpen_lt (continuous_const.add continuous_id) continuous_const).mem_nhds
        (by simpa using hw i)
    · exact (isOpen_lt (continuous_const.add (continuous_const.mul continuous_id))
        continuous_const).mem_nhds (by simpa using hv)
  have hmin : IsLocalMin g 0 := by
    filter_upwards [hev] with ε ⟨hwε, hvε⟩
    have hf : hi_Feasible M (v + M.β * ε) c (fun l => w l + ε) :=
      ⟨fun i j => by rw [hi_C_shift]; exact hic i j, by rw [hi_agentValue_shift, hpk], hwε⟩
    have := hi_le_T M (fun w hw => (hP w hw).2) hf
    rw [hfix _ hvε] at this
    simp only [g, mul_zero, add_zero, hval, sub_self]
    linarith
  have hd1 : HasDerivAt (fun ε => P (v + M.β * ε)) (dP v * M.β) 0 := by
    have hin : HasDerivAt (fun ε : ℝ => v + M.β * ε) M.β 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul M.β).const_add v
    have hP0 : HasDerivAt P (dP v) ((fun ε : ℝ => v + M.β * ε) 0) := by simpa using hdv
    exact hP0.comp (0 : ℝ) hin
  have hd2 : HasDerivAt (fun ε => hi_principalValue M P c (fun l => w l + ε))
      (∑ i, M.prob i * (M.β * dP (w i))) 0 := by
    unfold hi_principalValue
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h := (show HasDerivAt P (dP (w i)) (w i + 0) by simpa using hdw i).comp_const_add
      (w i) 0
    exact ((h.const_mul M.β).const_add (-c i)).const_mul (M.prob i)
  have hz := hmin.hasDerivAt_eq_zero (hd1.sub hd2)
  have e : ∑ i, M.prob i * (M.β * dP (w i)) = M.β * ∑ i, M.prob i * dP (w i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e] at hz
  have : M.β * (dP v - ∑ i, M.prob i * dP (w i)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h M.β_pos.ne'
  · linarith

/-- Miao, p. 796: with `P` strictly concave and differentiable on `(−∞, vmax)`, the derivative is
strictly decreasing there. -/
theorem hi_strictAntiOn_deriv (M : HIModel) {P : ℝ → ℝ} (hP : assumption_22_3_2 M P)
    (hd : ∀ x < hi_vmax M, DifferentiableAt ℝ P x) :
    StrictAntiOn (deriv P) (Set.Iio (hi_vmax M)) :=
  hP.strictAntiOn_deriv fun x hx => hd x hx

/-- **Lemma 22.3.3** (Miao, p. 796). With at least two income states, in a contract satisfying
the incentive constraints and the first-order conditions (22.27)–(22.29), with `P'` strictly
decreasing on `(−∞, vmax)` (Assumption 22.3.2) and `u'` strictly decreasing, `w₁ < v < wₙ`. -/
theorem lemma_22_3_3 (M : HIModel) (hN : 1 ≤ M.N) {u' dP : ℝ → ℝ}
    (hu' : StrictAnti u') (hdP : StrictAntiOn dP (Set.Iio (hi_vmax M))) {v lam : ℝ}
    {c w : Fin (M.N + 1) → ℝ} {μ : ℕ → ℝ} (hfeas : hi_Feasible M v c w)
    (hfoc : hi_FOC M u' dP v c w lam μ) :
    w 0 < v ∧ v < w (Fin.last M.N) := by
  obtain ⟨hic, hpk, hw⟩ := hfeas
  have hv : v < hi_vmax M := hpk ▸ hi_agentValue_lt_vmax M hw
  have hwm := (lemma_22_3_1 M c w hic).2
  have h30 := eq_22_30 M hfoc
  obtain ⟨h0, hn, h27, h28, h29⟩ := hfoc
  -- if all `wᵢ` equal `v`, the first-order conditions force full smoothing: contradiction
  have key : (∀ i, w i = v) → False := by
    intro hall
    -- all `μ` vanish
    have hμ : ∀ m, m ≤ M.N + 1 → μ m = 0 := by
      intro m
      induction m with
      | zero => intro _; exact h0
      | succ m ih =>
        intro hm
        have := h28 ⟨m, by omega⟩
        simp only [hall, h29, neg_add_cancel, mul_zero] at this
        rw [ih (by omega)] at this
        linarith
    -- marginal utilities are equalised
    have hmu : ∀ i : Fin (M.N + 1), lam * u' (M.θ i + c i) = 1 := by
      intro i
      have := h27 i
      rw [hμ i.val (by omega), hμ (i.val + 1) (by omega)] at this
      have hp := M.prob_pos i
      have : M.prob i * (1 - lam * u' (M.θ i + c i)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    set i0 : Fin (M.N + 1) := ⟨0, by omega⟩
    set i1 : Fin (M.N + 1) := ⟨1, by omega⟩
    have hx : M.θ i0 + c i0 = M.θ i1 + c i1 := by
      apply hu'.injective
      have a := hmu i0
      have b := hmu i1
      have hl : lam ≠ 0 := fun h => by rw [h, zero_mul] at a; exact zero_ne_one a
      exact mul_left_cancel₀ hl (a.trans b.symm)
    have hθ : M.θ i0 < M.θ i1 := M.θ_strictMono (Fin.mk_lt_mk.2 (by omega))
    -- but equal continuation values and incentive compatibility give `c₁ = c₀`
    have hC := hic i1 i0
    unfold hi_C at hC
    rw [hall i0, hall i1] at hC
    have : M.u (M.θ i1 + c i0) ≤ M.u (M.θ i1 + c i1) := by linarith
    have := M.u_strictMono.le_iff_le.1 this
    linarith
  have hsum0 : ∑ i, M.prob i * (dP (w i) - dP v) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, hi_sum_const, h30, sub_self]
  constructor
  · by_contra hge
    push Not at hge
    apply key
    intro i
    have hwi : v ≤ w i := hge.trans (hwm (Fin.zero_le i))
    have hle : ∀ j, M.prob j * (dP (w j) - dP v) ≤ 0 := fun j => by
      have : dP (w j) ≤ dP v :=
        hdP.antitoneOn hv (hw j) (hge.trans (hwm (Fin.zero_le j)))
      nlinarith [M.prob_pos j]
    have hz := (Finset.sum_eq_zero_iff_of_nonpos fun j _ => hle j).1 hsum0 i (Finset.mem_univ _)
    have : dP (w i) = dP v := by
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (M.prob_pos i).ne'
      · linarith
    exact hdP.injOn (hw i) hv this
  · by_contra hge
    push Not at hge
    apply key
    intro i
    have hle : ∀ j, 0 ≤ M.prob j * (dP (w j) - dP v) := fun j => by
      have : dP v ≤ dP (w j) :=
        hdP.antitoneOn (hw j) hv ((hwm (Fin.le_last j)).trans hge)
      nlinarith [M.prob_pos j]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hle j).1 hsum0 i (Finset.mem_univ _)
    have : dP (w i) = dP v := by
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (M.prob_pos i).ne'
      · linarith
    exact hdP.injOn (hw i) hv this

/-- Lemma 22.3.3 needs at least two income states: with one state (`N = 0`) the conclusion
`w₁ < v < wₙ` is impossible, since `w₁ = wₙ`. -/
theorem hi_lemma_22_3_3_one_state (w : Fin 1 → ℝ) (v : ℝ) : ¬ (w 0 < v ∧ v < w (Fin.last 0)) :=
  fun h => lt_asymm h.1 h.2

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Concavity of the value function (Proposition 22.3.1)

Miao, §22.3.1, pp. 792–793: under Assumption 22.3.1 (DARA) the Bellman operator maps concave
functions in `F` to concave functions, so the value function `P = lim Tᵏ L` is concave.

The proof follows the book. For contracts `(c⁰, w⁰)` at `v⁰` and `(c¹, w¹)` at `v¹`, the
averaged contract `(c*, w*)` delivers `δv⁰ + (1 − δ)v¹`, gives the principal at least the average
(`hi_mix_principal_ge`) and, by DARA, satisfies the local downward constraints
(`hi_mix_downward`); `w*` is monotone. Such a "relaxed" contract is then repaired into an
incentive-compatible one with the same promised value and a weakly higher value to the principal
(`hi_repair`), by alternating two moves:

* **reduce the spread of `w`** (`hi_adjust_increments`): lower every increment `wᵢ − wᵢ₋₁` to
  `max(Dᵢ, 0)`, where `βDᵢ = u(θᵢ + cᵢ₋₁) − u(θᵢ + cᵢ)` is the increment at which `Cᵢ,ᵢ₋₁` binds,
  keeping `Σ πᵢ wᵢ`. This is a sequence of mean-preserving spread reductions
  (`hi_spread_reduction_weak`) and weakly raises `Σ πᵢ f(wᵢ)` for concave `f`. If now `c` is
  decreasing, every local downward constraint binds and the contract is incentive compatible
  (`hi_upward_of_binding`, Lemma 22.3.2).
* **pool the transfers** (`hi_pool`): otherwise some pair has `cᵢ₋₁ < cᵢ` and `wᵢ₋₁ = wᵢ`. On the
  set of states sharing that continuation value, `c` is increasing; replacing it there by the
  single transfer `c̄` with the same expected utility lowers the expected transfer
  (`hi_pool_cost`, a Chebyshev-sum argument with the tangent line of `u`), keeps the local
  downward constraints and strictly lowers the number of steps of the contract (`hi_steps`).

The repair terminates by strong induction on `hi_steps`. This replaces the book's sketch on
p. 793 ("reduce `c*₂` until `C₂,₁` binds … adding a constant to each `c*ᵢ`"), which does not keep
promise keeping.

* `hi_T_concaveOn`: `T` maps concave functions in `F` to concave functions.
* `hi_L_concaveOn`: the lower bound `−b(v)/(1 − β)` is concave.
* `proposition_22_3_1_concave`: the value function `P` is concave on `(−∞, vmax)`.
-/

namespace Miao.RecursiveContracts

open Finset Filter Topology

/-- A concave function on a convex set has decreasing increments there. -/
theorem hi_incr_le_on_concave {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f) {x y d : ℝ}
    (hx : x ∈ s) (hyd : y + d ∈ s) (hxy : x ≤ y) (hd : 0 ≤ d) :
    f (y + d) - f y ≤ f (x + d) - f x := by
  rcases hxy.lt_or_eq with hxy | rfl
  · rcases hd.lt_or_eq with hd | rfl
    · have hoc := hf.1.ordConnected
      have hy : y ∈ s := hoc.out hx hyd ⟨hxy.le, by linarith⟩
      have hxd : x + d ∈ s := hoc.out hx hyd ⟨by linarith, by linarith⟩
      have h1 := hf.neg.secant_mono (a := x) (x := x + d) (y := y + d) hx hxd hyd
        (by linarith) (by linarith) (by linarith)
      have h2 := hf.neg.secant_mono (a := y + d) (x := x) (y := y) hyd hx hy
        (by linarith) (by linarith) hxy.le
      simp only [Pi.neg_apply] at h1 h2
      have e1 : (-f (x + d) - -f x) / (x + d - x) = -((f (x + d) - f x) / d) := by
        rw [show x + d - x = d by ring]; ring
      have e2 : (-f (y + d) - -f x) / (y + d - x) = -((f (y + d) - f x) / (y + d - x)) := by
        ring
      have e3 : (-f x - -f (y + d)) / (x - (y + d)) = -((f (y + d) - f x) / (y + d - x)) := by
        rw [show x - (y + d) = -(y + d - x) by ring, div_neg]; ring
      have e4 : (-f y - -f (y + d)) / (y - (y + d)) = -((f (y + d) - f y) / d) := by
        rw [show y - (y + d) = -d by ring, div_neg]; ring
      rw [e1, e2] at h1
      rw [e3, e4] at h2
      exact (div_le_div_iff_of_pos_right hd).1 (by linarith)
    · simp
  · exact le_rfl

/-- For a concave function, the slope on `[x₁, x₂]` is at least the slope on `[x₃, x₄]` when
`x₁ < x₂ ≤ x₃ < x₄`. -/
theorem hi_slope_anti_concave {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    {x1 x2 x3 x4 : ℝ} (h1 : x1 ∈ s) (h4 : x4 ∈ s) (h12 : x1 < x2) (h23 : x2 ≤ x3)
    (h34 : x3 < x4) :
    (f x4 - f x3) / (x4 - x3) ≤ (f x2 - f x1) / (x2 - x1) := by
  have hoc := hf.1.ordConnected
  rcases h23.lt_or_eq with h23 | rfl
  · have hx2 : x2 ∈ s := hoc.out h1 h4 ⟨h12.le, by linarith⟩
    have a := hf.slope_anti_adjacent h1 (hoc.out h1 h4 ⟨by linarith, by linarith⟩) h12 h23
    have b := hf.slope_anti_adjacent hx2 h4 h23 h34
    linarith
  · exact hf.slope_anti_adjacent h1 h4 h12 h34

/-- Miao, pp. 793–794, weak form of `hi_spread_reduction`: for `f` concave on `(−∞, vmax)` and
`0 ≤ δ ≤ w_k − w_{k−1}`, the mean-preserving spread reduction weakly raises `Σ πⱼ f(wⱼ)`. -/
theorem hi_spread_reduction_weak (M : HIModel) {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) {w : Fin (M.N + 1) → ℝ}
    (hw : ∀ j, w j < hi_vmax M) (hmono : Monotone w) (i : Fin M.N) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδw : δ ≤ w i.succ - w i.castSucc) :
    (∀ j, hi_reduce M w i.succ δ j < hi_vmax M) ∧
      ∑ j, M.prob j * f (w j) ≤ ∑ j, M.prob j * f (hi_reduce M w i.succ δ j) := by
  rcases hδ0.lt_or_eq with hδ | hδ
  swap
  · subst hδ
    have : ∀ j, hi_reduce M w i.succ 0 j = w j := fun j => by
      unfold hi_reduce; split_ifs <;> ring
    simp only [this]
    exact ⟨hw, le_rfl⟩
  obtain ⟨hq0, hq1⟩ := hi_upperMass_bounds M i
  set q := hi_upperMass M i.succ
  set a := w i.castSucc
  set b := w i.succ
  set e := δ * (1 - q)
  have he : 0 < e := mul_pos hδ (by linarith)
  have hdq : 0 < δ * q := mul_pos hδ hq0
  have hab : a + δ * q ≤ b - e := by simp only [e]; nlinarith
  have hbV : b < hi_vmax M := hw _
  have hred : ∀ j, hi_reduce M w i.succ δ j =
      if i.succ ≤ j then w j - e else w j + δ * q := fun j => by
    unfold hi_reduce; split_ifs <;> simp only [e, q] <;> ring
  have hlow : ∀ j, ¬ i.succ ≤ j → w j ≤ a := fun j hj => by
    apply hmono
    rw [not_le] at hj
    exact Fin.le_castSucc_iff.2 hj
  have hhigh : ∀ j, i.succ ≤ j → b ≤ w j := fun j hj => hmono hj
  refine ⟨fun j => ?_, ?_⟩
  · rw [hred j]
    split_ifs with hj
    · linarith [hw j]
    · linarith [hlow j hj]
  set gainL := f (a + δ * q) - f a
  set lossU := f b - f (b - e)
  have hterm : ∀ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) ≤
      M.prob j * (f (hi_reduce M w i.succ δ j) - f (w j)) := fun j => by
    refine mul_le_mul_of_nonneg_left ?_ (M.prob_pos j).le
    rw [hred j]
    split_ifs with hj
    · have := hi_incr_le_on_concave hf (x := b - e) (y := w j - e) (d := e)
        (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio]; linarith [hw j])
        (by linarith [hhigh j hj]) he.le
      simp only [sub_add_cancel] at this
      simp only [lossU]; linarith
    · have := hi_incr_le_on_concave hf (x := w j) (y := a) (d := δ * q)
        (by simp only [Set.mem_Iio]; linarith [hw j]) (by simp only [Set.mem_Iio]; linarith)
        (hlow j hj) hdq.le
      simp only [gainL]; linarith
  have hsum : ∑ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) =
      gainL - (gainL + lossU) * q := by
    have : ∀ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) =
        M.prob j * gainL - (gainL + lossU) * (M.prob j * (if i.succ ≤ j then 1 else 0)) :=
        fun j => by split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, hi_sum_const, ← Finset.mul_sum]
    rfl
  have hslope := hi_slope_anti_concave hf (x1 := a) (x2 := a + δ * q) (x3 := b - e) (x4 := b)
    (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio]; linarith)
    (by linarith) hab (by linarith)
  rw [show b - (b - e) = e by ring, show a + δ * q - a = δ * q by ring,
    div_le_div_iff₀ he hdq] at hslope
  have hpos : 0 ≤ gainL - (gainL + lossU) * q := by
    have h3 : lossU * (δ * q) ≤ gainL * (δ * (1 - q)) := hslope
    have : δ * (gainL - (gainL + lossU) * q) = gainL * (δ * (1 - q)) - lossU * (δ * q) := by
      ring
    have h4 : 0 ≤ δ * (gainL - (gainL + lossU) * q) := by linarith
    exact nonneg_of_mul_nonneg_right (by linarith) hδ
  have htot := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
  rw [hsum] at htot
  simp only [mul_sub, Finset.sum_sub_distrib] at htot
  linarith

/-- The spread reduction lowers the reduced increment by `δ` and keeps the others. -/
theorem hi_reduce_incr (M : HIModel) (w : Fin (M.N + 1) → ℝ) (i l : Fin M.N) (δ : ℝ) :
    hi_reduce M w i.succ δ l.succ - hi_reduce M w i.succ δ l.castSucc =
      (w l.succ - w l.castSucc) - (if l = i then δ else 0) := by
  unfold hi_reduce
  by_cases hl : l = i
  · subst hl
    have hn : ¬ l.succ ≤ l.castSucc := not_le.2 Fin.castSucc_lt_succ
    simp only [le_refl, hn, ↓reduceIte]; ring
  · have hiff : (i.succ ≤ l.succ ↔ i.succ ≤ l.castSucc) := by
      rw [Fin.le_def, Fin.le_def]
      simp only [Fin.val_succ, Fin.val_castSucc]
      have : l.val ≠ i.val := fun h => hl (Fin.ext h)
      omega
    by_cases h : i.succ ≤ l.castSucc
    · simp only [h, hiff.2 h, hl, ↓reduceIte]; ring
    · have h' : ¬ i.succ ≤ l.succ := fun h'' => h (hiff.1 h'')
      simp only [h, h', hl, ↓reduceIte]; ring

/-- Miao, pp. 792–793: lowering the increments of a monotone list of continuation values to any
targets `0 ≤ eₗ ≤ w_{l+1} − w_l`, keeping the mean, weakly raises `Σ πⱼ f(wⱼ)` for concave `f`
(a sequence of mean-preserving spread reductions). -/
theorem hi_adjust_increments (M : HIModel) {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) {w : Fin (M.N + 1) → ℝ}
    (hw : ∀ j, w j < hi_vmax M) (e : Fin M.N → ℝ) (he0 : ∀ l, 0 ≤ e l)
    (hle : ∀ l, e l ≤ w l.succ - w l.castSucc) :
    ∃ w' : Fin (M.N + 1) → ℝ, (∀ j, w' j < hi_vmax M) ∧
      (∀ l, w' l.succ - w' l.castSucc = e l) ∧
      ∑ j, M.prob j * w' j = ∑ j, M.prob j * w j ∧
      ∑ j, M.prob j * f (w j) ≤ ∑ j, M.prob j * f (w' j) := by
  have key : ∀ k : ℕ, ∃ w' : Fin (M.N + 1) → ℝ, (∀ j, w' j < hi_vmax M) ∧
      (∀ l : Fin M.N, w' l.succ - w' l.castSucc =
        if l.val < k then e l else w l.succ - w l.castSucc) ∧
      ∑ j, M.prob j * w' j = ∑ j, M.prob j * w j ∧
      ∑ j, M.prob j * f (w j) ≤ ∑ j, M.prob j * f (w' j) := by
    intro k
    induction k with
    | zero => exact ⟨w, hw, fun l => by simp, rfl, le_rfl⟩
    | succ k ih =>
      obtain ⟨w', hw', hinc, hmean, hineq⟩ := ih
      have hmono' : Monotone w' := Fin.monotone_iff_le_succ.2 fun l => by
        have h := hinc l
        split_ifs at h <;> linarith [he0 l, hle l]
      by_cases hk : k < M.N
      · set l0 : Fin M.N := ⟨k, hk⟩
        set δ := (w l0.succ - w l0.castSucc) - e l0
        have hδ : 0 ≤ δ := by simp only [δ]; linarith [hle l0]
        have hδw : δ ≤ w' l0.succ - w' l0.castSucc := by
          rw [hinc l0]
          simp only [l0, lt_irrefl, ↓reduceIte, δ]
          linarith [he0 l0]
        obtain ⟨hlt, hge⟩ := hi_spread_reduction_weak M hf hw' hmono' l0 hδ hδw
        refine ⟨hi_reduce M w' l0.succ δ, hlt, fun l => ?_, ?_, ?_⟩
        · rw [hi_reduce_incr, hinc l]
          by_cases hl : l = l0
          · subst hl
            simp only [l0, lt_irrefl, ↓reduceIte, lt_add_one, δ]
            ring
          · have hne : l.val ≠ k := fun h => hl (Fin.ext h)
            have e1 : (l.val < k + 1) ↔ (l.val < k) := by omega
            simp only [hl, ↓reduceIte, sub_zero, e1]
        · rw [hi_reduce_mean, hmean]
        · linarith
      · refine ⟨w', hw', fun l => ?_, hmean, hineq⟩
        have h1 : l.val < k := by have := l.isLt; omega
        have h2 : l.val < k + 1 := by omega
        rw [hinc l]
        simp only [h1, h2, ↓reduceIte]
  obtain ⟨w', h1, h2, h3, h4⟩ := key M.N
  exact ⟨w', h1, fun l => by rw [h2 l]; simp [l.isLt], h3, h4⟩

/-- Under Assumption 22.3.1, `u'` is strictly decreasing. -/
theorem hi_deriv_strictAnti {u u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 u u' u'') :
    StrictAnti u' :=
  strictAnti_of_deriv_neg fun x => by rw [(hu.2.1 x).deriv]; exact hu.2.2.2.1 x

/-- The tangent line bounds a concave utility: `u(y) ≤ u(x) + u'(x)(y − x)`. -/
theorem hi_tangent {u u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 u u' u'') (x y : ℝ) :
    u y ≤ u x + u' x * (y - x) := by
  have hanti := hi_deriv_strictAnti hu
  have hc : Continuous u := continuous_iff_continuousAt.2 fun z => (hu.1 z).continuousAt
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope u u' hxy hc.continuousOn
      fun z _ => hu.1 z
    have h1 : u' ξ ≤ u' x := (hanti hξ.1).le
    rw [eq_div_iff (by linarith)] at hd
    nlinarith
  · simp
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope u u' hxy hc.continuousOn
      fun z _ => hu.1 z
    have h1 : u' x ≤ u' ξ := (hanti hξ.2).le
    rw [eq_div_iff (by linarith)] at hd
    nlinarith

/-- Miao, p. 793 (the transfer repair): on a set `S` of states on which the transfer is
increasing, replacing it by the single transfer `c̄` with the same expected utility does not raise
the expected transfer, `(Σ_S πⱼ) c̄ ≤ Σ_S πⱼ cⱼ`. -/
theorem hi_pool_cost (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    (S : Finset (Fin (M.N + 1))) (hS : S.Nonempty) (c : Fin (M.N + 1) → ℝ)
    (hc : ∀ j ∈ S, ∀ k ∈ S, j ≤ k → c j ≤ c k) (cb : ℝ)
    (hcb : ∑ j ∈ S, M.prob j * M.u (M.θ j + cb) = ∑ j ∈ S, M.prob j * M.u (M.θ j + c j)) :
    (∑ j ∈ S, M.prob j) * cb ≤ ∑ j ∈ S, M.prob j * c j := by
  set P := ∑ j ∈ S, M.prob j
  have hP : 0 < P := Finset.sum_pos (fun j _ => M.prob_pos j) hS
  set m := (∑ j ∈ S, M.prob j * c j) / P
  set a : Fin (M.N + 1) → ℝ := fun j => u' (M.θ j + m)
  set b : Fin (M.N + 1) → ℝ := fun j => c j - m
  have hB : ∑ j ∈ S, M.prob j * b j = 0 := by
    simp only [b, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, m]
    field_simp
    ring
  have hanti := hi_deriv_strictAnti hu
  -- Chebyshev: `Σ_S π a b ≤ 0`
  have hterm : ∀ j ∈ S, ∀ k ∈ S, M.prob j * M.prob k * ((a j - a k) * (b j - b k)) ≤ 0 := by
    intro j hj k hk
    have hp : 0 ≤ M.prob j * M.prob k := mul_nonneg (M.prob_pos j).le (M.prob_pos k).le
    refine mul_nonpos_of_nonneg_of_nonpos hp ?_
    rcases le_total j k with hjk | hjk
    · have h1 : a k ≤ a j := hanti.antitone (by linarith [M.θ_strictMono.monotone hjk])
      have h2 : b j ≤ b k := by simp only [b]; linarith [hc j hj k hk hjk]
      nlinarith
    · have h1 : a j ≤ a k := hanti.antitone (by linarith [M.θ_strictMono.monotone hjk])
      have h2 : b k ≤ b j := by simp only [b]; linarith [hc k hk j hj hjk]
      nlinarith
  have hD : ∑ j ∈ S, ∑ k ∈ S, M.prob j * M.prob k * ((a j - a k) * (b j - b k)) =
      2 * P * ∑ j ∈ S, M.prob j * (a j * b j) -
        2 * (∑ j ∈ S, M.prob j * a j) * ∑ j ∈ S, M.prob j * b j := by
    have e : ∀ j k, M.prob j * M.prob k * ((a j - a k) * (b j - b k)) =
        M.prob j * (a j * b j) * M.prob k + M.prob j * (M.prob k * (a k * b k)) -
          M.prob j * a j * (M.prob k * b k) - M.prob j * b j * (M.prob k * a k) :=
      fun j k => by ring
    have h2 : ∑ j ∈ S, ∑ k ∈ S, M.prob j * M.prob k * ((a j - a k) * (b j - b k)) =
        (∑ j ∈ S, M.prob j * (a j * b j)) * (∑ k ∈ S, M.prob k) +
          (∑ j ∈ S, M.prob j) * (∑ k ∈ S, M.prob k * (a k * b k)) -
          (∑ j ∈ S, M.prob j * a j) * (∑ k ∈ S, M.prob k * b k) -
          (∑ j ∈ S, M.prob j * b j) * (∑ k ∈ S, M.prob k * a k) := by
      simp only [Finset.sum_mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => e j k
    rw [h2]
    ring
  have hX : ∑ j ∈ S, M.prob j * (a j * b j) ≤ 0 := by
    have := Finset.sum_nonpos fun j hj => Finset.sum_nonpos fun k hk => hterm j hj k hk
    rw [hD, hB, mul_zero, sub_zero] at this
    nlinarith
  -- tangent lines
  have htan : ∑ j ∈ S, M.prob j * M.u (M.θ j + c j) ≤ ∑ j ∈ S, M.prob j * M.u (M.θ j + m) := by
    have h1 : ∑ j ∈ S, M.prob j * M.u (M.θ j + c j) ≤
        ∑ j ∈ S, (M.prob j * M.u (M.θ j + m) + M.prob j * (a j * b j)) :=
      Finset.sum_le_sum fun j _ => by
        have := hi_tangent hu (M.θ j + m) (M.θ j + c j)
        have e : M.θ j + c j - (M.θ j + m) = b j := by simp only [b]; ring
        rw [e] at this
        have := mul_le_mul_of_nonneg_left this (M.prob_pos j).le
        simp only [a]; linarith
    rw [Finset.sum_add_distrib] at h1
    linarith
  have hcbm : cb ≤ m := by
    by_contra h
    push Not at h
    have : ∑ j ∈ S, M.prob j * M.u (M.θ j + m) < ∑ j ∈ S, M.prob j * M.u (M.θ j + cb) :=
      Finset.sum_lt_sum_of_nonempty hS fun j _ =>
        mul_lt_mul_of_pos_left (M.u_strictMono (by linarith)) (M.prob_pos j)
    linarith
  have : P * m = ∑ j ∈ S, M.prob j * c j := by simp only [m]; field_simp
  nlinarith

/-- The number of steps of a contract: the pairs of adjacent states with different terms. -/
noncomputable def hi_steps (M : HIModel) (c w : Fin (M.N + 1) → ℝ) : ℕ :=
  (Finset.univ.filter fun l : Fin M.N => c l.succ ≠ c l.castSucc ∨ w l.succ ≠ w l.castSucc).card

/-- Miao, p. 793 (the transfer repair). If the local downward constraints hold, `w` is monotone,
and some pair has `wᵢ₋₁ = wᵢ` and `cᵢ₋₁ < cᵢ`, then pooling the transfers of all states sharing
that continuation value (keeping their expected utility) keeps the local downward constraints and
the agent's value, does not lower the principal's value, and lowers the number of steps. -/
theorem hi_pool (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    (f : ℝ → ℝ) {c w : Fin (M.N + 1) → ℝ}
    (hloc : ∀ l : Fin M.N, 0 ≤ hi_C M c w l.succ l.castSucc) (hmono : Monotone w)
    (l0 : Fin M.N) (hweq : w l0.succ = w l0.castSucc) (hclt : c l0.castSucc < c l0.succ) :
    ∃ c' : Fin (M.N + 1) → ℝ, (∀ l : Fin M.N, 0 ≤ hi_C M c' w l.succ l.castSucc) ∧
      hi_agentValue M c' w = hi_agentValue M c w ∧
      hi_principalValue M f c w ≤ hi_principalValue M f c' w ∧
      hi_steps M c' w < hi_steps M c w := by
  classical
  set w0 := w l0.succ
  set S := Finset.univ.filter fun j => w j = w0
  have hmemS : ∀ j, j ∈ S ↔ w j = w0 := fun j => by simp [S]
  have hS : S.Nonempty := ⟨l0.succ, (hmemS _).2 rfl⟩
  have hpair : ∀ l : Fin M.N, w l.succ = w l.castSucc → c l.castSucc ≤ c l.succ := by
    intro l hl
    have h := hloc l
    unfold hi_C at h
    rw [hl] at h
    have : M.u (M.θ l.succ + c l.castSucc) ≤ M.u (M.θ l.succ + c l.succ) := by linarith
    have := M.u_strictMono.le_iff_le.1 this
    linarith
  have hinter : ∀ j k m, j ∈ S → k ∈ S → j ≤ m → m ≤ k → m ∈ S := by
    intro j k m hj hk hjm hmk
    rw [hmemS] at hj hk ⊢
    exact le_antisymm (by rw [← hk]; exact hmono hmk) (by rw [← hj]; exact hmono hjm)
  have hcS : ∀ j ∈ S, ∀ k ∈ S, j ≤ k → c j ≤ c k := by
    have key : ∀ d : ℕ, ∀ j k : Fin (M.N + 1), k.val = j.val + d → j ∈ S → k ∈ S →
        c j ≤ c k := by
      intro d
      induction d with
      | zero =>
        intro j k h _ _
        have : j = k := Fin.ext (by omega)
        rw [this]
      | succ d ih =>
        intro j k h hj hk
        have hm : j.val + d < M.N := by omega
        set m : Fin M.N := ⟨j.val + d, hm⟩
        have hmS : m.castSucc ∈ S := hinter j k _ hj hk (Fin.le_def.2 (by simp [m]))
          (Fin.le_def.2 (by simp [m]; omega))
        have hks : m.succ = k := Fin.ext (by simp [m]; omega)
        have h1 := ih j m.castSucc (by simp [m]) hj hmS
        have hw : w m.succ = w m.castSucc := by
          rw [hks, (hmemS _).1 hk, (hmemS _).1 hmS]
        have h2 := hpair m hw
        rw [hks] at h2
        linarith
    intro j hj k hk hjk
    exact key (k.val - j.val) j k (by have := Fin.le_def.1 hjk; omega) hj hk
  obtain ⟨jlo, hjlo, hlo⟩ := S.exists_min_image c hS
  obtain ⟨jhi, hjhi, hhi⟩ := S.exists_max_image c hS
  set g : ℝ → ℝ := fun x => ∑ j ∈ S, M.prob j * M.u (M.θ j + x)
  have hg : Continuous g := continuous_finsetSum _ fun j _ =>
    continuous_const.mul (M.u_cont.comp (continuous_const.add continuous_id))
  have hgT1 : g (c jlo) ≤ ∑ j ∈ S, M.prob j * M.u (M.θ j + c j) :=
    Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
      (M.u_strictMono.monotone (by linarith [hlo j hj])) (M.prob_pos j).le
  have hgT2 : ∑ j ∈ S, M.prob j * M.u (M.θ j + c j) ≤ g (c jhi) :=
    Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
      (M.u_strictMono.monotone (by linarith [hhi j hj])) (M.prob_pos j).le
  obtain ⟨cb, ⟨hcb1, hcb2⟩, hcb⟩ :=
    intermediate_value_Icc (hlo jhi hjhi) hg.continuousOn ⟨hgT1, hgT2⟩
  set c' : Fin (M.N + 1) → ℝ := fun j => if j ∈ S then cb else c j
  -- sums against `c'`
  have hsplit : ∀ F : Fin (M.N + 1) → ℝ → ℝ,
      ∑ j, F j (c' j) = ∑ j, F j (c j) + ∑ j ∈ S, (F j cb - F j (c j)) := by
    intro F
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [c', hmemS]
    split_ifs <;> ring
  refine ⟨c', fun l => ?_, ?_, ?_, ?_⟩
  · have h0 := hloc l
    unfold hi_C at h0 ⊢
    simp only [c']
    by_cases hsS : l.succ ∈ S <;> by_cases htS : l.castSucc ∈ S
    · simp only [hsS, htS, ↓reduceIte]
      rw [(hmemS _).1 hsS, (hmemS _).1 htS]
      linarith
    · simp only [hsS, htS, ↓reduceIte]
      have hmin : c l.succ ≤ cb := by
        have : l.succ ≤ jlo := by
          by_contra hlt
          push Not at hlt
          exact htS (hinter jlo l.succ l.castSucc hjlo hsS (Fin.le_castSucc_iff.2 hlt)
            Fin.castSucc_lt_succ.le)
        linarith [hcS _ hsS _ hjlo this]
      have := M.u_strictMono.monotone
        (show M.θ l.succ + c l.succ ≤ M.θ l.succ + cb by linarith)
      linarith
    · simp only [hsS, htS, ↓reduceIte]
      have hmax : cb ≤ c l.castSucc := by
        have : jhi ≤ l.castSucc := by
          by_contra hlt
          push Not at hlt
          have h1 : l.succ ≤ jhi := Fin.le_def.2 (by
            have := Fin.lt_def.1 hlt; simp only [Fin.val_castSucc] at this
            simp only [Fin.val_succ]; omega)
          exact hsS (hinter l.castSucc jhi l.succ htS hjhi Fin.castSucc_lt_succ.le h1)
        linarith [hcS _ hjhi _ htS this]
      have := M.u_strictMono.monotone
        (show M.θ l.succ + cb ≤ M.θ l.succ + c l.castSucc by linarith)
      linarith
    · simp only [hsS, htS, ↓reduceIte]
      exact h0
  · unfold hi_agentValue
    rw [hsplit fun j x => M.prob j * (M.u (M.θ j + x) + M.β * w j)]
    have : ∑ j ∈ S, (M.prob j * (M.u (M.θ j + cb) + M.β * w j) -
        M.prob j * (M.u (M.θ j + c j) + M.β * w j)) = 0 := by
      rw [← sub_eq_zero.2 hcb, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, add_zero]
  · unfold hi_principalValue
    rw [hsplit fun j x => M.prob j * (-x + M.β * f (w j))]
    have hcost := hi_pool_cost M hu S hS c (fun j hj k hk hjk => hcS j hj k hk hjk) cb hcb
    have : ∑ j ∈ S, (M.prob j * (-cb + M.β * f (w j)) - M.prob j * (-c j + M.β * f (w j))) =
        ∑ j ∈ S, M.prob j * c j - (∑ j ∈ S, M.prob j) * cb := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    linarith
  · unfold hi_steps
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨l0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl hclt.ne'
      · have hs0 : l0.succ ∈ S := (hmemS _).2 rfl
        have ht0 : l0.castSucc ∈ S := (hmemS _).2 hweq.symm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not]
        exact ⟨by simp only [c', hs0, ht0, ↓reduceIte], hweq⟩
    · intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      by_cases hw : w l.succ = w l.castSucc
      · left
        rcases hl with hl | hl
        · by_cases hsS : l.succ ∈ S
          · have htS : l.castSucc ∈ S := (hmemS _).2 (hw.symm.trans ((hmemS _).1 hsS))
            exact absurd (by simp only [c', hsS, htS, ↓reduceIte]) hl
          · have htS : l.castSucc ∉ S := fun h => hsS ((hmemS _).2 (hw.trans ((hmemS _).1 h)))
            simpa only [c', hsS, htS, ↓reduceIte] using hl
        · exact absurd hw hl
      · exact Or.inr hw

/-- Miao, pp. 792–793: a contract satisfying the local downward constraints with monotone
continuation values can be repaired into an incentive-compatible contract, with every local
downward constraint binding, the same promised value and a weakly higher value to the
principal, against any continuation `f` that is concave on `(−∞, vmax)`. -/
theorem hi_repair (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) (c w : Fin (M.N + 1) → ℝ)
    (hloc : ∀ l : Fin M.N, 0 ≤ hi_C M c w l.succ l.castSucc) (hmono : Monotone w)
    (hw : ∀ j, w j < hi_vmax M) :
    ∃ c' w' : Fin (M.N + 1) → ℝ, hi_IC M c' w' ∧ hi_agentValue M c' w' = hi_agentValue M c w ∧
      (∀ j, w' j < hi_vmax M) ∧ hi_principalValue M f c w ≤ hi_principalValue M f c' w' ∧
      ∀ l : Fin M.N, hi_C M c' w' l.succ l.castSucc = 0 := by
  suffices h : ∀ s, ∀ c w : Fin (M.N + 1) → ℝ, hi_steps M c w = s →
      (∀ l : Fin M.N, 0 ≤ hi_C M c w l.succ l.castSucc) → Monotone w →
      (∀ j, w j < hi_vmax M) →
      ∃ c' w' : Fin (M.N + 1) → ℝ, hi_IC M c' w' ∧
        hi_agentValue M c' w' = hi_agentValue M c w ∧ (∀ j, w' j < hi_vmax M) ∧
        hi_principalValue M f c w ≤ hi_principalValue M f c' w' ∧
        ∀ l : Fin M.N, hi_C M c' w' l.succ l.castSucc = 0 from
    h _ c w rfl hloc hmono hw
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro c w hs hloc hmono hw
  set D : Fin M.N → ℝ := fun l =>
    (M.u (M.θ l.succ + c l.castSucc) - M.u (M.θ l.succ + c l.succ)) / M.β
  set e : Fin M.N → ℝ := fun l => max (D l) 0
  have hβD : ∀ l, M.β * D l =
      M.u (M.θ l.succ + c l.castSucc) - M.u (M.θ l.succ + c l.succ) := fun l => by
    have hβ := M.β_pos.ne'
    simp only [D]; field_simp
  have hincr : ∀ l, D l ≤ w l.succ - w l.castSucc := fun l => by
    have h1 := hloc l
    unfold hi_C at h1
    have h2 := hβD l
    have : M.β * D l ≤ M.β * (w l.succ - w l.castSucc) := by linarith
    exact le_of_mul_le_mul_left this M.β_pos
  have hle : ∀ l, e l ≤ w l.succ - w l.castSucc := fun l =>
    max_le (hincr l) (by linarith [hmono (Fin.castSucc_lt_succ : l.castSucc < l.succ).le])
  obtain ⟨w', hw', hinc', hmean, hineq⟩ :=
    hi_adjust_increments M hf hw e (fun l => le_max_right _ _) hle
  have hC' : ∀ l : Fin M.N, hi_C M c w' l.succ l.castSucc = M.β * (e l - D l) := fun l => by
    unfold hi_C
    linear_combination M.β * hinc' l + hβD l
  have hloc' : ∀ l : Fin M.N, 0 ≤ hi_C M c w' l.succ l.castSucc := fun l => by
    rw [hC']
    exact mul_nonneg M.β_pos.le (by simp only [e]; linarith [le_max_left (D l) 0])
  have hmono' : Monotone w' :=
    Fin.monotone_iff_le_succ.2 fun l => by linarith [hinc' l, le_max_right (D l) 0]
  have hagent : hi_agentValue M c w' = hi_agentValue M c w := by
    unfold hi_agentValue
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [hi_sum_mul_left M M.β w', hi_sum_mul_left M M.β w, hmean]
  have hpv : hi_principalValue M f c w ≤ hi_principalValue M f c w' := by
    unfold hi_principalValue
    simp only [mul_add, Finset.sum_add_distrib, add_le_add_iff_left]
    rw [hi_sum_mul_left M M.β (fun j => f (w j)), hi_sum_mul_left M M.β (fun j => f (w' j))]
    exact mul_le_mul_of_nonneg_left hineq M.β_pos.le
  have hsteps : hi_steps M c w' ≤ hi_steps M c w := by
    unfold hi_steps
    apply Finset.card_le_card
    intro l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    by_contra hn
    push Not at hn
    have hD0 : D l = 0 := by simp only [D, hn.1, sub_self, zero_div]
    have : w' l.succ = w' l.castSucc := by
      have := hinc' l
      simp only [e, hD0, max_self] at this
      linarith
    rcases h with h | h
    · exact h hn.1
    · exact h this
  by_cases hall : ∀ l : Fin M.N, c l.succ ≤ c l.castSucc
  · have hbind : ∀ l : Fin M.N, hi_C M c w' l.succ l.castSucc = 0 := fun l => by
      rw [hC']
      have h0 : 0 ≤ D l := by
        have := M.u_strictMono.monotone
          (show M.θ l.succ + c l.succ ≤ M.θ l.succ + c l.castSucc by linarith [hall l])
        have h2 := hβD l
        have : 0 ≤ M.β * D l := by linarith
        exact nonneg_of_mul_nonneg_right (by linarith) M.β_pos
      simp only [e, max_eq_left h0, sub_self, mul_zero]
    have hIC : hi_IC M c w' := lemma_22_3_2 M c w' fun l =>
      ⟨(hbind l).ge, (hi_upward_of_binding M c w' Fin.castSucc_lt_succ (hbind l) (hall l)).1⟩
    exact ⟨c, w', hIC, hagent, hw', hpv, hbind⟩
  · push Not at hall
    obtain ⟨l0, hl0⟩ := hall
    have hD : D l0 < 0 := by
      have := M.u_strictMono
        (show M.θ l0.succ + c l0.castSucc < M.θ l0.succ + c l0.succ by linarith)
      have h2 := hβD l0
      have : M.β * D l0 < 0 := by linarith
      by_contra h
      push Not at h
      linarith [mul_nonneg M.β_pos.le h]
    have hweq : w' l0.succ = w' l0.castSucc := by
      have := hinc' l0
      simp only [e, max_eq_right hD.le] at this
      linarith
    obtain ⟨c'', hloc'', hag'', hpv'', hst''⟩ := hi_pool M hu f hloc' hmono' l0 hweq hl0
    obtain ⟨c3, w3, hIC3, hag3, hw3, hpv3, hb3⟩ :=
      ih (hi_steps M c'' w') (by omega) c'' w' rfl hloc'' hmono' hw'
    exact ⟨c3, w3, hIC3, by rw [hag3, hag'', hagent], hw3, by linarith, hb3⟩

/-- Miao, pp. 792–793: for contracts feasible at `v⁰` and `v¹` and `δ ∈ (0, 1)`, there is an
incentive-compatible contract at `δv⁰ + (1 − δ)v¹` giving the principal at least the average of
their values, against a continuation concave on `(−∞, vmax)`. -/
theorem hi_mix_repair (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {v0 v1 : ℝ} {c0 w0 c1 w1 : Fin (M.N + 1) → ℝ} (h0 : hi_Feasible M v0 c0 w0)
    (h1 : hi_Feasible M v1 c1 w1) :
    ∃ c w, hi_Feasible M (δ * v0 + (1 - δ) * v1) c w ∧
      δ * hi_principalValue M f c0 w0 + (1 - δ) * hi_principalValue M f c1 w1 ≤
        hi_principalValue M f c w := by
  obtain ⟨cs, hcs⟩ := hi_exists_mix M hδ0.le hδ1.le c0 c1
  set ws : Fin (M.N + 1) → ℝ := fun i => δ * w0 i + (1 - δ) * w1 i
  have hloc : ∀ l : Fin M.N, 0 ≤ hi_C M cs ws l.succ l.castSucc := fun l =>
    hi_mix_downward M hu hδ0 hδ1 hcs Fin.castSucc_lt_succ.le (h0.1 _ _) (h1.1 _ _)
  have hm0 := (lemma_22_3_1 M c0 w0 h0.1).2
  have hm1 := (lemma_22_3_1 M c1 w1 h1.1).2
  have hmono : Monotone ws := fun i j hij => by
    simp only [ws]
    nlinarith [hm0 hij, hm1 hij]
  have hws : ∀ j, ws j < hi_vmax M := fun j => by
    simp only [ws]
    nlinarith [h0.2.2 j, h1.2.2 j]
  obtain ⟨c, w, hIC, hag, hw, hpv, -⟩ := hi_repair M hu hf cs ws hloc hmono hws
  refine ⟨c, w, ⟨hIC, ?_, hw⟩, ?_⟩
  · rw [hag, hi_mix_agentValue M hcs, h0.2.1, h1.2.1]
  · exact (hi_mix_principal_ge M hδ0.le hδ1.le hf hcs h0.2.2 h1.2.2).trans hpv

/-- **Proposition 22.3.1** (Miao, pp. 792–793), the induction step: under Assumption 22.3.1 the
Bellman operator maps a function in `F` that is concave on `(−∞, vmax)` to a concave function. -/
theorem hi_T_concaveOn (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    {f : ℝ → ℝ} (hF : hi_InF M f) (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) :
    ConcaveOn ℝ (Set.Iio (hi_vmax M)) (hi_T M f) := by
  refine ⟨convex_Iio _, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hfU : ∀ w < hi_vmax M, f w ≤ hi_U M w := fun w hw => (hF w hw).2
  rcases ha.lt_or_eq with ha | ha
  swap
  · subst ha; simp only [zero_add] at hab; subst hab; simp
  rcases hb.lt_or_eq with hb | hb
  swap
  · subst hb; simp only [add_zero] at hab; subst hab; simp
  have hb' : b = 1 - a := by linarith
  have hxy : a * x + b * y < hi_vmax M := by
    have : a * x + b * y < a * hi_vmax M + b * hi_vmax M := by
      have := mul_lt_mul_of_pos_left (show x < hi_vmax M from hx) ha
      have := mul_lt_mul_of_pos_left (show y < hi_vmax M from hy) hb
      linarith
    rwa [← add_mul, hab, one_mul] at this
  have key : ∀ x0 ∈ hi_vals M f x, ∀ x1 ∈ hi_vals M f y,
      a * x0 + b * x1 ≤ hi_T M f (a * x + b * y) := by
    rintro _ ⟨c0, w0, h0, rfl⟩ _ ⟨c1, w1, h1, rfl⟩
    obtain ⟨c, w, hfeas, hle⟩ := hi_mix_repair M hu hf ha (by linarith) h0 h1
    rw [← hb'] at hfeas hle
    exact hle.trans (hi_le_T M hfU hfeas)
  have step : ∀ x0 ∈ hi_vals M f x, a * x0 + b * hi_T M f y ≤ hi_T M f (a * x + b * y) := by
    intro x0 hx0
    have : hi_T M f y ≤ (hi_T M f (a * x + b * y) - a * x0) / b := by
      refine csSup_le (hi_vals_nonempty M f hy) fun x1 hx1 => ?_
      rw [le_div_iff₀ hb]
      linarith [key x0 hx0 x1 hx1]
    rw [le_div_iff₀ hb] at this
    linarith
  have : hi_T M f x ≤ (hi_T M f (a * x + b * y) - b * hi_T M f y) / a := by
    refine csSup_le (hi_vals_nonempty M f hx) fun x0 hx0 => ?_
    rw [le_div_iff₀ ha]
    linarith [step x0 hx0]
  rw [le_div_iff₀ ha] at this
  linarith

/-- The lower bound `L(v) = −b(v)/(1 − β)` is concave: `b` inverts the concave increasing map
`b ↦ Σ πᵢ u(θᵢ + b)`. -/
theorem hi_L_concaveOn (M : HIModel) : ConcaveOn ℝ (Set.Iio (hi_vmax M)) (hi_L M) := by
  refine ⟨convex_Iio _, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hxy : a * x + b * y < hi_vmax M := by
    have := (convex_Iio (hi_vmax M)) hx hy ha hb hab
    simpa only [smul_eq_mul, Set.mem_Iio] using this
  have hB : a * hi_Bfun M (hi_b M x) + b * hi_Bfun M (hi_b M y) ≤
      hi_Bfun M (a * hi_b M x + b * hi_b M y) := by
    unfold hi_Bfun
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := M.u_strictConcave.concaveOn.2 (Set.mem_univ (M.θ i + hi_b M x))
      (Set.mem_univ (M.θ i + hi_b M y)) ha hb hab
    simp only [smul_eq_mul] at this
    have e : a * (M.θ i + hi_b M x) + b * (M.θ i + hi_b M y) =
        M.θ i + (a * hi_b M x + b * hi_b M y) := by
      rw [show a * (M.θ i + hi_b M x) + b * (M.θ i + hi_b M y) =
        (a + b) * M.θ i + (a * hi_b M x + b * hi_b M y) by ring, hab, one_mul]
    rw [e] at this
    nlinarith [M.prob_pos i]
  rw [hi_b_spec M hx, hi_b_spec M hy] at hB
  have hb_le : hi_b M (a * x + b * y) ≤ a * hi_b M x + b * hi_b M y := by
    rw [← (hi_Bfun_strictMono M).le_iff_le, hi_b_spec M hxy]
    linarith [show (1 - M.β) * (a * x + b * y) = a * ((1 - M.β) * x) + b * ((1 - M.β) * y) by
      ring]
  unfold hi_L
  have key : a * (-hi_b M x / (1 - M.β)) + b * (-hi_b M y / (1 - M.β)) =
      -(a * hi_b M x + b * hi_b M y) / (1 - M.β) := by ring
  rw [key]
  exact div_le_div_of_nonneg_right (by linarith) h1β.le

/-- The iterates `Pₖ = Tᵏ L` are concave under Assumption 22.3.1. -/
theorem hi_Pk_concaveOn (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    (k : ℕ) : ConcaveOn ℝ (Set.Iio (hi_vmax M)) (hi_Pk M k) := by
  induction k with
  | zero => exact hi_L_concaveOn M
  | succ k ih =>
    have e : hi_Pk M (k + 1) = hi_T M (hi_Pk M k) := by
      unfold hi_Pk; rw [Function.iterate_succ_apply']
    rw [e]
    exact hi_T_concaveOn M hu (hi_Pk_InF M k) ih

/-- **Proposition 22.3.1** (Miao, p. 791), concavity: under Assumption 22.3.1 the value function
`P = lim Tᵏ L` is concave on `(−∞, vmax)`. -/
theorem proposition_22_3_1_concave (M : HIModel) {u' u'' : ℝ → ℝ}
    (hu : assumption_22_3_1 M.u u' u'') : ConcaveOn ℝ (Set.Iio (hi_vmax M)) (hi_P M) :=
  hi_concaveOn_of_tendsto (fun k => hi_Pk_concaveOn M hu k) fun _ hx => hi_Pk_tendsto M hx

/-- Miao, p. 794, Proposition 22.3.2 from concavity alone: under Assumption 22.3.1 (without
Assumption 22.3.2), whenever an optimal contract exists at `v` there is an optimal contract at `v`
in which every local downward constraint binds and every local upward constraint holds. -/
theorem hi_proposition_22_3_2_concave (M : HIModel) {u' u'' : ℝ → ℝ}
    (hu : assumption_22_3_1 M.u u' u'') {v : ℝ} {c w : Fin (M.N + 1) → ℝ}
    (hopt : hi_Optimal M (hi_P M) v c w) :
    ∃ c' w', hi_Optimal M (hi_P M) v c' w' ∧
      ∀ l : Fin M.N, hi_C M c' w' l.succ l.castSucc = 0 ∧ 0 ≤ hi_C M c' w' l.castSucc l.succ := by
  obtain ⟨⟨hic, hpk, hw⟩, hbest⟩ := hopt
  obtain ⟨c', w', hIC, hag, hw', hpv, hbind⟩ := hi_repair M hu (proposition_22_3_1_concave M hu)
    c w (fun l => hic _ _) (lemma_22_3_1 M c w hic).2 hw
  refine ⟨c', w', ⟨⟨hIC, hag.trans hpk, hw'⟩, fun c'' w'' h => (hbest c'' w'' h).trans hpv⟩,
    fun l => ⟨hbind l, hIC _ _⟩⟩

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Long-run poverty: Proposition 22.3.4

Miao, §22.3.2, pp. 796–797: under the optimal contract the promised value `vₜ` converges to
`−∞` almost surely (immiseration).

The shocks are an iid sequence `ξₜ : Ω → Fin n` on a probability space with
`Pr(ξₜ = i) = πᵢ`; the promised value evolves by `vₜ₊₁ = w_{ξₜ}(vₜ)` (`hi_vseq`) for policy
functions `wᵢ(v)`. The function `G` plays the role of `P'`.

* `hi_poverty_det`: the deterministic core. If `G(xₜ)` converges, `G` is continuous, strictly
  decreasing and negative on `(−∞, vmax)` with `G → 0` at `−∞` and `G → −∞` at `vmax`, and
  infinitely often `xₜ₊₁ = wₙ(xₜ)` where `wₙ` is continuous with `wₙ(v) > v` (Lemma 22.3.3),
  then `xₜ → −∞`. A finite negative limit would give a fixed point `v* = wₙ(v*)`.
* `hi_poverty_martingale`: `−G(vₜ₊₁)` is a nonnegative martingale for the natural filtration of
  the shocks (the martingale property (22.30) of the policies and independence of the shocks).
* `proposition_22_3_4`: `vₜ → −∞` almost surely, by the martingale convergence theorem
  (`Submartingale.ae_tendsto_limitProcess`) and the second Borel–Cantelli lemma (the top shock
  occurs infinitely often).
* `hi_poverty_example`: the hypotheses hold for the CARA example (`G(v) = 1/v`,
  `w₁(v) = 2v`, `w₂(v) = 2v/3`) with iid fair-coin shocks, so the proposition is not vacuous.

Departure: the continuity of the top policy `wₙ(v)` is assumed (the book uses it implicitly).
-/

namespace Miao.RecursiveContracts

open Finset Filter Topology MeasureTheory ProbabilityTheory

/-- Miao, p. 797: the promised values `v₀, v₁ = w_{s₀}(v₀), …` along a shock path `s`. -/
def hi_vseq (M : HIModel) (W : Fin (M.N + 1) → ℝ → ℝ) (v0 : ℝ) (s : ℕ → Fin (M.N + 1)) :
    ℕ → ℝ
  | 0 => v0
  | t + 1 => W (s t) (hi_vseq M W v0 s t)

/-- `vₜ` depends only on the shocks before `t`. -/
theorem hi_vseq_congr (M : HIModel) (W : Fin (M.N + 1) → ℝ → ℝ) (v0 : ℝ)
    {s s' : ℕ → Fin (M.N + 1)} (t : ℕ) (h : ∀ j < t, s j = s' j) :
    hi_vseq M W v0 s t = hi_vseq M W v0 s' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [hi_vseq]
    rw [h t (lt_add_one t), ih fun j hj => h j (by omega)]

/-- The promised values stay in `(−∞, vmax)`. -/
theorem hi_vseq_lt (M : HIModel) {W : Fin (M.N + 1) → ℝ → ℝ} {v0 : ℝ} (hv0 : v0 < hi_vmax M)
    (hWV : ∀ i, ∀ v < hi_vmax M, W i v < hi_vmax M) (s : ℕ → Fin (M.N + 1)) (t : ℕ) :
    hi_vseq M W v0 s t < hi_vmax M := by
  induction t with
  | zero => exact hv0
  | succ t ih => exact hWV _ _ ih

/-- Miao, p. 797 (proof of Proposition 22.3.4, deterministic part). If `G(xₜ)` converges,
`G` is continuous, strictly decreasing and negative on `(−∞, vmax)`, `G → 0` at `−∞`,
`G → −∞` at `vmax`, `wₙ` is continuous with `wₙ(v) > v` (Lemma 22.3.3), and infinitely often
`xₜ₊₁ = wₙ(xₜ)`, then `xₜ → −∞`. -/
theorem hi_poverty_det (M : HIModel) {G Wn : ℝ → ℝ} (hGneg : ∀ v < hi_vmax M, G v < 0)
    (hGanti : StrictAntiOn G (Set.Iio (hi_vmax M)))
    (hGcont : ContinuousOn G (Set.Iio (hi_vmax M))) (hGbot : Tendsto G atBot (𝓝 0))
    (hGtop : Tendsto G (𝓝[<] hi_vmax M) atBot) (hWcont : ContinuousOn Wn (Set.Iio (hi_vmax M)))
    (hlemma : ∀ v < hi_vmax M, v < Wn v) {x : ℕ → ℝ} (hx : ∀ t, x t < hi_vmax M) {ℓ : ℝ}
    (hℓ : Tendsto (fun t => G (x t)) atTop (𝓝 ℓ))
    (hfreq : ∃ᶠ t in atTop, x (t + 1) = Wn (x t)) : Tendsto x atTop atBot := by
  have hℓ0 : ℓ ≤ 0 := le_of_tendsto' hℓ fun t => (hGneg _ (hx t)).le
  rcases hℓ0.lt_or_eq with hneg | hzero
  · exfalso
    obtain ⟨A, hA, hAV⟩ : ∃ A, ℓ < G A ∧ A < hi_vmax M :=
      ((hGbot.eventually (lt_mem_nhds hneg)).and (eventually_lt_atBot _)).exists
    obtain ⟨B, hB, hBV⟩ : ∃ B, G B < ℓ ∧ B < hi_vmax M :=
      ((hGtop.eventually (eventually_lt_atBot ℓ)).and self_mem_nhdsWithin).exists
    have hAB : A < B := by
      by_contra h
      push Not at h
      have := hGanti.antitoneOn hBV hAV h
      linarith
    have hcont : ContinuousOn G (Set.Icc A B) := hGcont.mono fun y hy => lt_of_le_of_lt hy.2 hBV
    obtain ⟨vs, hvsI, hvs⟩ := intermediate_value_Icc' hAB.le hcont ⟨hB.le, hA.le⟩
    have hvsV : vs < hi_vmax M := lt_of_le_of_lt hvsI.2 hBV
    -- `xₜ → v*`
    have hxlim : Tendsto x atTop (𝓝 vs) := by
      rw [tendsto_order]
      constructor
      · intro a ha
        have haV : a < hi_vmax M := lt_trans ha hvsV
        have h1 : ℓ < G a := by rw [← hvs]; exact hGanti haV hvsV ha
        filter_upwards [hℓ.eventually (gt_mem_nhds h1)] with t ht
        by_contra h
        push Not at h
        have := hGanti.antitoneOn (hx t) haV h
        linarith
      · intro b hb
        set b' := min b ((vs + hi_vmax M) / 2)
        have hb'V : b' < hi_vmax M := lt_of_le_of_lt (min_le_right _ _) (by linarith)
        have hvsb' : vs < b' := lt_min hb (by linarith)
        have h1 : G b' < ℓ := by rw [← hvs]; exact hGanti hvsV hb'V hvsb'
        filter_upwards [hℓ.eventually (lt_mem_nhds h1)] with t ht
        by_contra h
        push Not at h
        have := hGanti.antitoneOn hb'V (hx t) (le_trans (min_le_left _ _) h)
        linarith
    have hW1 : Tendsto (fun t => Wn (x t)) atTop (𝓝 (Wn vs)) :=
      ((hWcont.continuousAt (Iio_mem_nhds hvsV)).tendsto).comp hxlim
    have hx1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 vs) := hxlim.comp (tendsto_add_atTop_nat 1)
    have hd : Tendsto (fun t => x (t + 1) - Wn (x t)) atTop (𝓝 (vs - Wn vs)) := hx1.sub hW1
    have hne : vs - Wn vs ≠ 0 := by linarith [hlemma vs hvsV]
    obtain ⟨t, h1, h2⟩ := (hfreq.and_eventually (hd.eventually_ne hne)).exists
    exact h2 (by rw [h1]; ring)
  · rw [tendsto_atBot]
    intro K
    by_cases hK : K < hi_vmax M
    · have hGK : G K < ℓ := by rw [hzero]; exact hGneg K hK
      filter_upwards [hℓ.eventually (lt_mem_nhds hGK)] with t ht
      by_contra h
      push Not at h
      have := hGanti.antitoneOn hK (hx t) h.le
      linarith
    · push Not at hK
      exact Eventually.of_forall fun t => by linarith [hx t]

/-- The natural filtration of the shocks: `ℱₜ = σ(ξ₀, …, ξₜ)`. -/
def hi_filt (M : HIModel) {Ω : Type*} [m0 : MeasurableSpace Ω] (ξ : ℕ → Ω → Fin (M.N + 1))
    (hξ : ∀ t, Measurable (ξ t)) : Filtration ℕ m0 where
  seq t := ⨆ j ≤ t, MeasurableSpace.comap (ξ j) inferInstance
  mono' _ _ hst := biSup_mono fun _ hj => le_trans hj hst
  le' _ := iSup₂_le fun j _ => (hξ j).comap_le

/-- `ξⱼ` is `ℱₜ`-measurable for `j ≤ t`. -/
theorem hi_filt_meas (M : HIModel) {Ω : Type*} [MeasurableSpace Ω] {ξ : ℕ → Ω → Fin (M.N + 1)}
    (hξ : ∀ t, Measurable (ξ t)) {j t : ℕ} (hj : j ≤ t) :
    Measurable[hi_filt M ξ hξ t] (ξ j) :=
  Measurable.of_comap_le
    (le_iSup₂ (f := fun j (_ : j ≤ t) => MeasurableSpace.comap (ξ j) inferInstance) j hj)

/-- A function of finitely many measurable shocks is strongly measurable. -/
theorem hi_tuple_sm_aux (M : HIModel) {Ω : Type*} [mΩ : MeasurableSpace Ω] (t : ℕ)
    (g : (Fin (t + 1) → Fin (M.N + 1)) → ℝ) (f : Fin (t + 1) → Ω → Fin (M.N + 1))
    (hf : ∀ j, Measurable (f j)) : StronglyMeasurable fun ω => g fun j => f j ω :=
  ((measurable_of_countable g).comp (measurable_pi_iff.2 hf)).stronglyMeasurable

/-- A function of `(ξ₀, …, ξₜ)` is `ℱₜ`-strongly measurable. -/
theorem hi_tuple_sm (M : HIModel) {Ω : Type*} [MeasurableSpace Ω] {ξ : ℕ → Ω → Fin (M.N + 1)}
    (hξ : ∀ t, Measurable (ξ t)) (t : ℕ) (g : (Fin (t + 1) → Fin (M.N + 1)) → ℝ) :
    StronglyMeasurable[hi_filt M ξ hξ t] fun ω => g fun j => ξ j ω := by
  exact hi_tuple_sm_aux M (mΩ := hi_filt M ξ hξ t) t g (fun j ω => ξ j ω)
    fun j => hi_filt_meas M hξ (Nat.lt_succ_iff.1 j.isLt)

/-- A function of `(ξ₀, …, ξₜ)` is integrable (it takes finitely many values). -/
theorem hi_tuple_int (M : HIModel) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {ξ : ℕ → Ω → Fin (M.N + 1)} (hξ : ∀ t, Measurable (ξ t)) (t : ℕ)
    (g : (Fin (t + 1) → Fin (M.N + 1)) → ℝ) : Integrable (fun ω => g fun j => ξ j ω) μ :=
  by
    have h1 := hi_tuple_sm M hξ t g
    have h2 : StronglyMeasurable fun ω => g fun j => ξ j ω :=
      StronglyMeasurable.mono h1 ((hi_filt M ξ hξ).le t)
    exact Integrable.of_bound h2.aestronglyMeasurable (∑ a, |g a|) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun a => |g a|) (fun a _ => abs_nonneg _)
        (Finset.mem_univ _))

/-- `vₜ₊₁` as a function of `(ξ₀, …, ξₜ)`. -/
def hi_Fseq (M : HIModel) (W : Fin (M.N + 1) → ℝ → ℝ) (v0 : ℝ) (t : ℕ)
    (a : Fin (t + 1) → Fin (M.N + 1)) : ℝ :=
  hi_vseq M W v0 (fun s => if h : s < t + 1 then a ⟨s, h⟩ else 0) (t + 1)

/-- `vₜ₊₁ = Fₜ(ξ₀, …, ξₜ)`. -/
theorem hi_vseq_eq_Fseq (M : HIModel) (W : Fin (M.N + 1) → ℝ → ℝ) (v0 : ℝ) {Ω : Type*}
    (ξ : ℕ → Ω → Fin (M.N + 1)) (t : ℕ) (ω : Ω) :
    hi_vseq M W v0 (fun s => ξ s ω) (t + 1) = hi_Fseq M W v0 t fun j => ξ j ω := by
  unfold hi_Fseq
  exact hi_vseq_congr M W v0 (t + 1) fun j hj => by simp [hj]

/-- Miao, p. 797: `−G(vₜ₊₁)` is a martingale for the natural filtration of the shocks, when the
policies satisfy the martingale property `Σ πᵢ G(wᵢ(v)) = G(v)` of (22.30). -/
theorem hi_poverty_martingale (M : HIModel) {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Fin (M.N + 1))
    (hξ : ∀ t, Measurable (ξ t)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ t i, μ (ξ t ⁻¹' {i}) = ENNReal.ofReal (M.prob i)) (W : Fin (M.N + 1) → ℝ → ℝ)
    (G : ℝ → ℝ) {v0 : ℝ} (hv0 : v0 < hi_vmax M)
    (hWV : ∀ i, ∀ v < hi_vmax M, W i v < hi_vmax M)
    (hmart : ∀ v < hi_vmax M, ∑ i, M.prob i * G (W i v) = G v) :
    Martingale (fun t ω => -G (hi_vseq M W v0 (fun s => ξ s ω) (t + 1))) (hi_filt M ξ hξ) μ := by
  set ℱ := hi_filt M ξ hξ
  set Y : ℕ → Ω → ℝ := fun t ω => -G (hi_vseq M W v0 (fun s => ξ s ω) (t + 1))
  have hrep : ∀ t, Y t = fun ω => (fun a => -G (hi_Fseq M W v0 t a)) fun j => ξ j ω :=
    fun t => funext fun ω => by simp only [Y, hi_vseq_eq_Fseq]
  have hadp : StronglyAdapted ℱ Y := fun t => by
    rw [hrep t]; exact hi_tuple_sm M hξ t (fun a => -G (hi_Fseq M W v0 t a))
  have hint : ∀ t, Integrable (Y t) μ := fun t => by
    rw [hrep t]; exact hi_tuple_int M hξ t (fun a => -G (hi_Fseq M W v0 t a))
  refine martingale_nat hadp hint fun t => ?_
  -- the decomposition `Y_{t+1} = Σᵢ hᵢ eᵢ`
  set h : Fin (M.N + 1) → Ω → ℝ := fun i ω => -G (W i (hi_vseq M W v0 (fun s => ξ s ω) (t + 1)))
  set e : Fin (M.N + 1) → Ω → ℝ := fun i => (ξ (t + 1) ⁻¹' {i}).indicator 1
  have hdec : Y (t + 1) = ∑ i, h i * e i := by
    funext ω
    rw [Finset.sum_apply, Finset.sum_eq_single (ξ (t + 1) ω)]
    · simp [Y, h, e, hi_vseq]
    · intro b _ hb
      simp [e, Set.indicator, Ne.symm hb]
    · simp
  have hhrep : ∀ i, h i = fun ω => (fun a => -G (W i (hi_Fseq M W v0 t a))) fun j => ξ j ω :=
    fun i => funext fun ω => by simp only [h, hi_vseq_eq_Fseq]
  have hhsm : ∀ i, StronglyMeasurable[ℱ t] (h i) := fun i => by
    rw [hhrep i]; exact hi_tuple_sm M hξ t (fun a => -G (W i (hi_Fseq M W v0 t a)))
  have hhint : ∀ i, Integrable (h i) μ := fun i => by
    rw [hhrep i]; exact hi_tuple_int M hξ t (fun a => -G (W i (hi_Fseq M W v0 t a)))
  have hemeas : ∀ i, MeasurableSet (ξ (t + 1) ⁻¹' {i}) := fun i =>
    hξ (t + 1) (MeasurableSpace.measurableSet_top)
  have heint : ∀ i, Integrable (e i) μ := fun i =>
    (integrable_const (1 : ℝ)).indicator (hemeas i)
  have hebdd : ∀ i, ∀ ω, ‖e i ω‖ ≤ 1 := fun i ω => by
    simp only [e, Set.indicator]; split_ifs <;> simp
  have hheint : ∀ i, Integrable (h i * e i) μ := fun i =>
    (hhint i).mul_bdd ((heint i).aestronglyMeasurable) (ae_of_all _ (hebdd i))
  -- independence of `ξ_{t+1}` from `ℱₜ`
  have hindep : Indep (MeasurableSpace.comap (ξ (t + 1)) inferInstance) (ℱ t) μ := by
    have := indep_iSup_of_disjoint (m := fun j => MeasurableSpace.comap (ξ j) inferInstance)
      (fun j => (hξ j).comap_le) ((iIndepFun_iff_iIndep _ _ _).1 hind)
      (S := {t + 1}) (T := {k | k ≤ t}) (by simp)
    rwa [_root_.iSup_singleton] at this
  have hesm : ∀ i, StronglyMeasurable[MeasurableSpace.comap (ξ (t + 1)) inferInstance] (e i) :=
    fun i => by
      have hm : Measurable[MeasurableSpace.comap (ξ (t + 1)) inferInstance] (ξ (t + 1)) :=
        Measurable.of_comap_le le_rfl
      have : e i = (fun a : Fin (M.N + 1) => ({i} : Set (Fin (M.N + 1))).indicator 1 a) ∘
          ξ (t + 1) := by
        funext ω; simp [e, Set.indicator]
      rw [this]
      exact ((measurable_of_countable _).comp hm).stronglyMeasurable
  have hEe : ∀ i, μ[e i] = M.prob i := fun i => by
    simp only [e]
    rw [integral_indicator_one (hemeas i), measureReal_def, hlaw,
      ENNReal.toReal_ofReal (M.prob_pos i).le]
  have hce : ∀ i, μ[e i | ℱ t] =ᵐ[μ] fun _ => M.prob i := fun i => by
    have := condExp_indep_eq (hξ (t + 1)).comap_le (ℱ.le t) (hesm i) hindep
    rw [hEe i] at this
    exact this
  have hpull : ∀ i, μ[h i * e i | ℱ t] =ᵐ[μ] h i * μ[e i | ℱ t] := fun i =>
    condExp_mul_of_stronglyMeasurable_left (hhsm i) (hheint i) (heint i)
  have hsum := condExp_finsetSum (μ := μ) (m := ℱ t) (s := Finset.univ)
    (f := fun i => h i * e i) fun i _ => hheint i
  rw [hdec]
  filter_upwards [hsum, ae_all_iff.2 hpull, ae_all_iff.2 hce] with ω h1 h2 h3
  rw [h1, Finset.sum_apply]
  simp only [Pi.mul_apply] at h2
  simp only [h2, h3]
  have hv := hi_vseq_lt M hv0 hWV (fun s => ξ s ω) (t + 1)
  have := hmart _ hv
  simp only [Y, h]
  rw [← this, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Proposition 22.3.4** (Miao, p. 796). The promised value `vₜ` converges to `−∞` almost
surely. Here `G` is the derivative `P'` of the value function, `W i` the policy `wᵢ(v)` of the
optimal contract, satisfying the martingale property (22.30), Lemma 22.3.3 (`wₙ(v) > v`), and
the endpoint limits `P'(−∞) = 0`, `P'(vmax) = −∞` of p. 797; `P'` is continuous, strictly
decreasing and negative, and `wₙ` is continuous. -/
theorem proposition_22_3_4 (M : HIModel) {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Fin (M.N + 1))
    (hξ : ∀ t, Measurable (ξ t)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ t i, μ (ξ t ⁻¹' {i}) = ENNReal.ofReal (M.prob i)) (W : Fin (M.N + 1) → ℝ → ℝ)
    (G : ℝ → ℝ) {v0 : ℝ} (hv0 : v0 < hi_vmax M)
    (hWV : ∀ i, ∀ v < hi_vmax M, W i v < hi_vmax M)
    (hmart : ∀ v < hi_vmax M, ∑ i, M.prob i * G (W i v) = G v)
    (hGneg : ∀ v < hi_vmax M, G v < 0) (hGanti : StrictAntiOn G (Set.Iio (hi_vmax M)))
    (hGcont : ContinuousOn G (Set.Iio (hi_vmax M))) (hGbot : Tendsto G atBot (𝓝 0))
    (hGtop : Tendsto G (𝓝[<] hi_vmax M) atBot)
    (hWcont : ContinuousOn (W (Fin.last M.N)) (Set.Iio (hi_vmax M)))
    (hlemma : ∀ v < hi_vmax M, v < W (Fin.last M.N) v) :
    ∀ᵐ ω ∂μ, Tendsto (fun t => hi_vseq M W v0 (fun s => ξ s ω) t) atTop atBot := by
  set Y : ℕ → Ω → ℝ := fun t ω => -G (hi_vseq M W v0 (fun s => ξ s ω) (t + 1))
  have hM := hi_poverty_martingale M ξ hξ hind hlaw W G hv0 hWV hmart
  have hY0 : ∀ t ω, 0 ≤ Y t ω := fun t ω => by
    have := hGneg _ (hi_vseq_lt M hv0 hWV (fun s => ξ s ω) (t + 1)); simp only [Y]; linarith
  -- L¹ bound
  have hbdd : ∀ n, eLpNorm (Y n) 1 μ ≤ (∫ ω, Y 0 ω ∂μ).toNNReal := by
    intro n
    have h1 : ∫ ω, Y n ω ∂μ = ∫ ω, Y 0 ω ∂μ := by
      rw [← integral_condExp ((hi_filt M ξ hξ).le 0)]
      exact integral_congr_ae (hM.2 0 n (Nat.zero_le n))
    rw [eLpNorm_one_eq_lintegral_enorm (hM.integrable n).aestronglyMeasurable]
    have h2 : ∫⁻ ω, ‖Y n ω‖ₑ ∂μ = ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂μ :=
      lintegral_congr fun ω => Real.enorm_eq_ofReal (hY0 n ω)
    rw [h2, ← ofReal_integral_eq_lintegral_ofReal (hM.integrable n) (ae_of_all _ (hY0 n)), h1]
    rfl
  have hconv := hM.submartingale.ae_tendsto_limitProcess hbdd
  -- the top shock occurs infinitely often
  set s : ℕ → Set Ω := fun t => ξ t ⁻¹' {Fin.last M.N}
  have hsm : ∀ t, MeasurableSet (s t) := fun t => hξ t MeasurableSpace.measurableSet_top
  have hsind : iIndepSet s μ := by
    rw [iIndepSet_iff_meas_biInter hsm]
    intro S
    exact hind.meas_biInter fun i _ => ⟨{Fin.last M.N}, MeasurableSpace.measurableSet_top, rfl⟩
  have hsum : ∑' t, μ (s t) = ⊤ := by
    simp only [s, hlaw]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by
      simpa using M.prob_pos (Fin.last M.N))
  have hBC := measure_limsup_eq_one hsm hsind hsum
  have hae : ∀ᵐ ω ∂μ, ω ∈ limsup s atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hsm)).2 hBC
  filter_upwards [hconv, hae] with ω h1 h2
  rw [Filter.mem_limsup_iff_frequently_mem] at h2
  set x : ℕ → ℝ := fun t => hi_vseq M W v0 (fun s => ξ s ω) (t + 1)
  have hx : ∀ t, x t < hi_vmax M := fun t => hi_vseq_lt M hv0 hWV _ _
  have hGx : Tendsto (fun t => G (x t)) atTop
      (𝓝 (-(hi_filt M ξ hξ).limitProcess Y μ ω)) := by
    have := h1.neg
    simp only [neg_neg] at this
    exact this
  have hfreq : ∃ᶠ t in atTop, x (t + 1) = W (Fin.last M.N) (x t) := by
    rw [Filter.frequently_atTop] at h2 ⊢
    intro a
    obtain ⟨b, hb, hbs⟩ := h2 (a + 1)
    refine ⟨b - 1, by omega, ?_⟩
    have hb1 : b - 1 + 1 = b := by omega
    simp only [x, hi_vseq]
    rw [hb1]
    simp only [s, Set.mem_preimage, Set.mem_singleton_iff] at hbs
    rw [hbs]
  have := hi_poverty_det M hGneg hGanti hGcont hGbot hGtop hWcont hlemma hx hGx hfreq
  exact (tendsto_add_atTop_iff_nat 1).1 this

/-- In the concrete CARA instance, `vmax = sup u / (1 − β) = 0`. -/
theorem hi_exampleModel_vmax : hi_vmax hi_exampleModel = 0 := by
  change sSup (Set.range (hi_cara 1)) / (1 - 1 / 2) = 0
  rw [hi_cara_sSup one_pos, zero_div]

/-- The example policies `w₁(v) = 2v`, `w₂(v) = 2v/3`. -/
noncomputable def hi_exampleW (i : Fin (hi_exampleModel.N + 1)) (v : ℝ) : ℝ :=
  if i = 0 then 2 * v else 2 / 3 * v

/-- Non-vacuity of Proposition 22.3.4: in the concrete CARA instance (two equally likely income
states), with `G(v) = 1/v` and the policies `w₁(v) = 2v`, `w₂(v) = 2v/3` (which satisfy
`½·1/(2v) + ½·3/(2v) = 1/v`), and iid fair-coin shocks on some probability space, every
hypothesis of `proposition_22_3_4` holds, and the promised value starting from `v₀ = −1`
converges to `−∞` almost surely. -/
theorem hi_poverty_example : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (ξ : ℕ → Ω → Fin (hi_exampleModel.N + 1)), IsProbabilityMeasure P ∧
      (∀ t, Measurable (ξ t)) ∧ iIndepFun ξ P ∧
      (∀ t i, P (ξ t ⁻¹' {i}) = ENNReal.ofReal (hi_exampleModel.prob i)) ∧
      ∀ᵐ ω ∂P, Tendsto (fun t => hi_vseq hi_exampleModel hi_exampleW (-1) (fun s => ξ s ω) t)
        atTop atBot := by
  set M := hi_exampleModel
  have hprob : ∀ i, M.prob i = 1 / 2 := fun i => by
    fin_cases i <;> simp [M, hi_exampleModel, hi_caraModel]
  obtain ⟨Ω, mΩ, P, ξ, hξ, hlaw, hind, hP⟩ :=
    exists_iid ℕ (PMF.uniformOfFintype (Fin (M.N + 1))).toMeasure
  have hlaw' : ∀ t i, P (ξ t ⁻¹' {i}) = ENNReal.ofReal (M.prob i) := by
    intro t i
    rw [← Measure.map_apply (hξ t) (MeasurableSpace.measurableSet_top), (hlaw t).map_eq,
      PMF.toMeasure_apply_singleton _ _ (MeasurableSpace.measurableSet_top),
      PMF.uniformOfFintype_apply, hprob, Fintype.card_fin, show M.N + 1 = 2 from rfl,
      ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, one_div]
    norm_num
  have hv : hi_vmax M = 0 := hi_exampleModel_vmax
  have hlast : (Fin.last M.N) ≠ 0 := by decide
  refine ⟨Ω, mΩ, P, ξ, hP, hξ, hind, hlaw', ?_⟩
  refine proposition_22_3_4 M ξ hξ hind hlaw' hi_exampleW (fun v => 1 / v) (by rw [hv]; norm_num)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i v hv0
    rw [hv] at hv0 ⊢
    unfold hi_exampleW
    split_ifs <;> linarith
  · intro v hv0
    rw [hv] at hv0
    have h1 : (1 : Fin (M.N + 1)) ≠ 0 := by decide
    have huniv : (Finset.univ : Finset (Fin (M.N + 1))) = {0, 1} := by
      ext j; fin_cases j <;> decide
    rw [huniv, Finset.sum_pair h1.symm]
    simp only [hprob, hi_exampleW, ↓reduceIte, h1]
    field_simp
    ring
  · intro v hv0
    rw [hv] at hv0
    exact one_div_neg.2 hv0
  · rw [hv]
    intro a ha b hb hab
    exact one_div_lt_one_div_of_neg_of_lt hb hab
  · rw [hv]
    exact continuousOn_const.div continuousOn_id fun x hx => ne_of_lt hx
  · simpa only [one_div] using tendsto_inv_atBot_zero
  · rw [hv]
    simpa only [one_div] using tendsto_inv_nhdsLT_zero
  · unfold hi_exampleW
    simp only [hlast, ↓reduceIte]
    exact (continuous_const.mul continuous_id).continuousOn
  · intro v hv0
    rw [hv] at hv0
    unfold hi_exampleW
    simp only [hlast, ↓reduceIte]
    linarith

end Miao.RecursiveContracts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 22.3 and 22.4

Miao, §22.4, pp. 798–799.

**Exercise 22.4** (CARA utility `u(c) = −exp(−γc)`). Shifting every transfer by `k` multiplies
every utility by `e^{−γk}`, so `(c, w) ↦ (c + k, e^{−γk} w)` maps the contracts feasible at `v`
onto those feasible at `e^{−γk} v` (`hi_cara_scale_feasible`) and the Bellman operator commutes
with `f ↦ f(e^{−γk} ·) + k/(1 − β)` (`hi_T_scaleFn`). By uniqueness of the fixed point
(Proposition 22.3.1) `P(e^{−γk} v) = P(v) − k/(1 − β)` (`hi_cara_P_scale`), hence
`P(v) = [ln(−v) + K]/(γ(1 − β))` (`ex_22_4_value`). Optimal contracts rescale
(`hi_cara_optimal_scale`), so `cᵢ(v) = −(1/γ) ln(−aᵢ v)`, `wᵢ(v) = dᵢ v` with
`0 < aᵢ₋₁ ≤ aᵢ`, `dᵢ₋₁ ≥ dᵢ > 0`, `Σ πᵢ/dᵢ = 1`, `Σ πᵢ (e^{−γθᵢ} aᵢ + β dᵢ) = 1` and
`K = Σ πᵢ ln aᵢ + β/(1 − β) Σ πᵢ ln dᵢ` (`ex_22_4`).

The book prints the form with a constant `A = Σ πᵢ/aᵢ`: `cᵢ = −(1/γ) ln(−aᵢ(v + A))`,
`wᵢ = dᵢ v + (dᵢ − 1)A`, `P(v) = [ln(−v − A) + K]/(γ(1 − β))`. Promise keeping forces `A = 0`
(`hi_ex_22_4_A_eq_zero`), which contradicts `A = Σ πᵢ/aᵢ > 0`
(`ex_22_4_printed_inconsistent`).

**Exercise 22.3** (`β → 1`). Not formalised as a limit; `ex_22_3_upper` proves the half that
follows from (22.26), and `hi_normalized_bounds` shows that in per-period terms both bounds of
(22.26) are independent of `β`, so they cannot settle the limit.
-/

namespace Miao.RecursiveContracts

open Finset Filter Topology

/-- `u(x + k) = e^{−γk} u(x)` for CARA utility. -/
theorem hi_cara_shift (γ x k : ℝ) : hi_cara γ (x + k) = Real.exp (-γ * k) * hi_cara γ x := by
  unfold hi_cara
  rw [show -γ * (x + k) = -γ * k + -γ * x by ring, Real.exp_add]; ring

/-- With CARA utility, `vmax = 0`. -/
theorem hi_cara_vmax (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) :
    hi_vmax M = 0 := by
  unfold hi_vmax hi_ubar; rw [hu, hi_cara_sSup hγ, zero_div]

/-- Exercise 22.4: `(c, w) ↦ (c + k, e^{−γk} w)` maps contracts feasible at `v` to contracts
feasible at `e^{−γk} v`. -/
theorem hi_cara_scale_feasible (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ)
    (k : ℝ) {v : ℝ} {c w : Fin (M.N + 1) → ℝ} (h : hi_Feasible M v c w) :
    hi_Feasible M (Real.exp (-γ * k) * v) (fun i => c i + k)
      (fun i => Real.exp (-γ * k) * w i) := by
  obtain ⟨hic, hpk, hw⟩ := h
  have he := Real.exp_pos (-γ * k)
  have hv := hi_cara_vmax M hγ hu
  refine ⟨fun i j => ?_, ?_, fun i => ?_⟩
  · have hC : hi_C M (fun i => c i + k) (fun i => Real.exp (-γ * k) * w i) i j =
        Real.exp (-γ * k) * hi_C M c w i j := by
      unfold hi_C
      rw [hu, show M.θ i + (c i + k) = M.θ i + c i + k by ring,
        show M.θ i + (c j + k) = M.θ i + c j + k by ring, hi_cara_shift γ (M.θ i + c i) k,
        hi_cara_shift γ (M.θ i + c j) k]
      ring
    rw [hC]; exact mul_nonneg he.le (hic i j)
  · rw [← hpk]; unfold hi_agentValue
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu, show M.θ i + (c i + k) = M.θ i + c i + k by ring,
      hi_cara_shift γ (M.θ i + c i) k]
    ring
  · have := hw i; rw [hv] at this ⊢; nlinarith

/-- Exercise 22.4: `b(e^{−γk} v) = b(v) + k`. -/
theorem hi_cara_b_shift (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {v : ℝ} (hv : v < 0) : hi_b M (Real.exp (-γ * k) * v) = hi_b M v + k := by
  have hV := hi_cara_vmax M hγ hu
  have he := Real.exp_pos (-γ * k)
  have h1 : v < hi_vmax M := by rw [hV]; exact hv
  have h2 : Real.exp (-γ * k) * v < hi_vmax M := by rw [hV]; nlinarith
  apply (hi_Bfun_strictMono M).injective
  rw [hi_b_spec M h2]
  have := hi_b_spec M h1
  unfold hi_Bfun at this ⊢
  have e : ∑ i, M.prob i * M.u (M.θ i + (hi_b M v + k)) =
      Real.exp (-γ * k) * ∑ i, M.prob i * M.u (M.θ i + hi_b M v) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu, show M.θ i + (hi_b M v + k) = M.θ i + hi_b M v + k by ring,
      hi_cara_shift γ (M.θ i + hi_b M v) k]; ring
  rw [e, this]; ring

/-- Exercise 22.4: `c*(e^{−γk} v) = c*(v) + k`. -/
theorem hi_cara_cstar_shift (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {v : ℝ} (hv : v < 0) : hi_cstar M (Real.exp (-γ * k) * v) = hi_cstar M v + k := by
  have hV := hi_cara_vmax M hγ hu
  have he := Real.exp_pos (-γ * k)
  have h1 : v < hi_vmax M := by rw [hV]; exact hv
  have h2 : Real.exp (-γ * k) * v < hi_vmax M := by rw [hV]; nlinarith
  apply M.u_strictMono.injective
  rw [hi_cstar_spec M h2]
  have := hi_cstar_spec M h1
  rw [hu] at this ⊢
  rw [hi_cara_shift γ (hi_cstar M v) k, this]; ring

/-- The rescaled function `f(e^{−γk} v) + k/(1 − β)`. -/
noncomputable def hi_scaleFn (M : HIModel) (γ k : ℝ) (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  f (Real.exp (-γ * k) * v) + k / (1 - M.β)

/-- The bounds (22.26) are invariant under the rescaling. -/
theorem hi_scaleFn_InF (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {f : ℝ → ℝ} (hf : hi_InF M f) : hi_InF M (hi_scaleFn M γ k f) := by
  have hV := hi_cara_vmax M hγ hu
  have he := Real.exp_pos (-γ * k)
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  intro v hv
  rw [hV] at hv
  have h2 : Real.exp (-γ * k) * v < hi_vmax M := by rw [hV]; nlinarith
  obtain ⟨hL, hU⟩ := hf _ h2
  have eL : hi_L M (Real.exp (-γ * k) * v) + k / (1 - M.β) = hi_L M v := by
    unfold hi_L; rw [hi_cara_b_shift M hγ hu k hv]; field_simp; ring
  have eU : hi_U M (Real.exp (-γ * k) * v) + k / (1 - M.β) = hi_U M v := by
    unfold hi_U; rw [hi_cara_cstar_shift M hγ hu k hv]; field_simp; ring
  unfold hi_scaleFn
  constructor <;> linarith

/-- The principal's value of a rescaled contract against a rescaled continuation. -/
theorem hi_pv_scaleFn (M : HIModel) (γ k : ℝ) (f : ℝ → ℝ) (c w : Fin (M.N + 1) → ℝ) :
    hi_principalValue M (hi_scaleFn M γ k f) c w =
      hi_principalValue M f (fun i => c i + k) (fun i => Real.exp (-γ * k) * w i) +
        k / (1 - M.β) := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_principalValue hi_scaleFn
  have : ∀ i, M.prob i * (-c i + M.β * (f (Real.exp (-γ * k) * w i) + k / (1 - M.β))) =
      M.prob i * (-(c i + k) + M.β * f (Real.exp (-γ * k) * w i)) +
        M.prob i * (k / (1 - M.β)) := fun i => by field_simp; ring
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, hi_sum_const]

/-- Exercise 22.4: the Bellman operator commutes with the rescaling,
`T(f(e^{−γk} ·) + k/(1 − β)) = (Tf)(e^{−γk} ·) + k/(1 − β)`. -/
theorem hi_T_scaleFn (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {f : ℝ → ℝ} (hf : hi_InF M f) {v : ℝ} (hv : v < 0) :
    hi_T M (hi_scaleFn M γ k f) v = hi_scaleFn M γ k (hi_T M f) v := by
  have hV := hi_cara_vmax M hγ hu
  have he := Real.exp_pos (-γ * k)
  have hvV : v < hi_vmax M := by rw [hV]; exact hv
  have h2 : Real.exp (-γ * k) * v < hi_vmax M := by rw [hV]; nlinarith
  have hsF := hi_scaleFn_InF M hγ hu k hf
  change hi_T M (hi_scaleFn M γ k f) v = hi_T M f (Real.exp (-γ * k) * v) + k / (1 - M.β)
  apply le_antisymm
  · refine csSup_le (hi_vals_nonempty M _ hvV) ?_
    rintro _ ⟨c, w, h, rfl⟩
    rw [hi_pv_scaleFn]
    have := hi_le_T M (fun w hw => (hf w hw).2) (hi_cara_scale_feasible M hγ hu k h)
    linarith
  · have : hi_T M f (Real.exp (-γ * k) * v) ≤
        hi_T M (hi_scaleFn M γ k f) v - k / (1 - M.β) := by
      refine csSup_le (hi_vals_nonempty M _ h2) ?_
      rintro _ ⟨c, w, h, rfl⟩
      have hb := hi_cara_scale_feasible M hγ hu (-k) h
      have e1 : Real.exp (-γ * -k) * (Real.exp (-γ * k) * v) = v := by
        rw [← mul_assoc, ← Real.exp_add]; simp
      rw [e1] at hb
      have := hi_le_T M (fun w hw => (hsF w hw).2) hb
      rw [hi_pv_scaleFn] at this
      have e2 : (fun i => Real.exp (-γ * k) * (Real.exp (-γ * -k) * w i)) = w := by
        funext i; rw [← mul_assoc, ← Real.exp_add]; simp
      have e3 : (fun i => c i + -k + k) = c := by funext i; ring
      simp only [e2, e3] at this
      linarith
    linarith

/-- Exercise 22.4: `P(e^{−γk} v) + k/(1 − β) = P(v)` for `v < 0`, by uniqueness of the fixed
point (Proposition 22.3.1). -/
theorem hi_cara_P_scale (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {v : ℝ} (hv : v < 0) :
    hi_P M (Real.exp (-γ * k) * v) + k / (1 - M.β) = hi_P M v := by
  have hV := hi_cara_vmax M hγ hu
  have hQ := hi_scaleFn_InF M hγ hu k (hi_P_InF M)
  have hQf : ∀ x < hi_vmax M,
      hi_T M (hi_scaleFn M γ k (hi_P M)) x = hi_scaleFn M γ k (hi_P M) x := by
    intro x hx
    rw [hV] at hx
    rw [hi_T_scaleFn M hγ hu k (hi_P_InF M) hx]
    unfold hi_scaleFn
    rw [hi_P_fixed M (by rw [hV]; nlinarith [Real.exp_pos (-γ * k)])]
  have := hi_fixed_unique M hQ (hi_P_InF M) hQf (fun x hx => hi_P_fixed M hx)
    (show v < hi_vmax M by rw [hV]; exact hv)
  unfold hi_scaleFn at this
  exact this

/-- **Exercise 22.4** (Miao, p. 799), the value function: with CARA utility,
`P(v) = [ln(−v) + K]/(γ(1 − β))` on `(−∞, 0)`, with `K = γ(1 − β)P(−1)`. -/
theorem ex_22_4_value (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) {v : ℝ}
    (hv : v < 0) :
    hi_P M v = (Real.log (-v) + γ * (1 - M.β) * hi_P M (-1)) / (γ * (1 - M.β)) := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have := hi_cara_P_scale M hγ hu (-Real.log (-v) / γ) (show (-1 : ℝ) < 0 by norm_num)
  have e : Real.exp (-γ * (-Real.log (-v) / γ)) * -1 = v := by
    rw [show -γ * (-Real.log (-v) / γ) = Real.log (-v) by field_simp,
      Real.exp_log (by linarith)]; ring
  rw [e] at this
  field_simp
  field_simp at this
  linarith

/-- With CARA utility, `P'(v) = 1/(γ(1 − β)v)` on `(−∞, 0)`. -/
theorem hi_cara_P_hasDerivAt (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) {v : ℝ}
    (hv : v < 0) : HasDerivAt (hi_P M) (1 / (γ * (1 - M.β) * v)) v := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  set K := γ * (1 - M.β) * hi_P M (-1)
  have hd : HasDerivAt (fun x => (Real.log (-x) + K) / (γ * (1 - M.β)))
      (1 / (γ * (1 - M.β) * v)) v := by
    have h1 := ((hasDerivAt_neg v).log (by linarith : -v ≠ 0)).add_const K
    have h2 := h1.div_const (γ * (1 - M.β))
    convert h2 using 1
    field_simp
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hv] with x hx
  exact ex_22_4_value M hγ hu hx

/-- With CARA utility, rescaling a contract lowers the principal's value by `k/(1 − β)`. -/
theorem hi_cara_pv_scale (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ) (k : ℝ)
    {c w : Fin (M.N + 1) → ℝ} (hw : ∀ i, w i < 0) :
    hi_principalValue M (hi_P M) (fun i => c i + k) (fun i => Real.exp (-γ * k) * w i) =
      hi_principalValue M (hi_P M) c w - k / (1 - M.β) := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_principalValue
  have : ∀ i, M.prob i * (-(c i + k) + M.β * hi_P M (Real.exp (-γ * k) * w i)) =
      M.prob i * (-c i + M.β * hi_P M (w i)) - M.prob i * (k / (1 - M.β)) := fun i => by
    have h := hi_cara_P_scale M hγ hu k (hw i)
    rw [show hi_P M (Real.exp (-γ * k) * w i) = hi_P M (w i) - k / (1 - M.β) by linarith]
    field_simp; ring
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, hi_sum_const]

/-- Exercise 22.4: an optimal contract at `v` rescales to an optimal contract at
`e^{−γk} v`. -/
theorem hi_cara_optimal_scale (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ)
    (k : ℝ) {v : ℝ} {c w : Fin (M.N + 1) → ℝ} (h : hi_Optimal M (hi_P M) v c w) :
    hi_Optimal M (hi_P M) (Real.exp (-γ * k) * v) (fun i => c i + k)
      (fun i => Real.exp (-γ * k) * w i) := by
  have hV := hi_cara_vmax M hγ hu
  obtain ⟨hf, hbest⟩ := h
  have hw : ∀ i, w i < 0 := fun i => by have := hf.2.2 i; rwa [hV] at this
  refine ⟨hi_cara_scale_feasible M hγ hu k hf, fun c' w' h' => ?_⟩
  have hw' : ∀ i, w' i < 0 := fun i => by have := h'.2.2 i; rwa [hV] at this
  have hb := hi_cara_scale_feasible M hγ hu (-k) h'
  have e1 : Real.exp (-γ * -k) * (Real.exp (-γ * k) * v) = v := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [e1] at hb
  have h1 := hbest _ _ hb
  have hw'' : ∀ i, Real.exp (-γ * -k) * w' i < 0 := fun i => by
    nlinarith [Real.exp_pos (-γ * -k), hw' i]
  have h2 := hi_cara_pv_scale M hγ hu k (c := fun i => c' i + -k) hw''
  have e2 : (fun i => Real.exp (-γ * k) * (Real.exp (-γ * -k) * w' i)) = w' := by
    funext i; rw [← mul_assoc, ← Real.exp_add]; simp
  have e3 : (fun i => c' i + -k + k) = c' := by funext i; ring
  simp only [e2, e3] at h2
  rw [hi_cara_pv_scale M hγ hu k hw]
  linarith

/-- An optimal contract attains the value function. -/
theorem hi_optimal_value (M : HIModel) {v : ℝ} {c w : Fin (M.N + 1) → ℝ}
    (h : hi_Optimal M (hi_P M) v c w) : hi_principalValue M (hi_P M) c w = hi_P M v := by
  have hv : v < hi_vmax M := h.1.2.1 ▸ hi_agentValue_lt_vmax M h.1.2.2
  rw [← hi_P_fixed M hv]
  apply le_antisymm (hi_le_T M (fun w hw => (hi_P_InF M w hw).2) h.1)
  exact csSup_le (hi_vals_nonempty M _ hv) (by rintro _ ⟨c', w', h', rfl⟩; exact h.2 c' w' h')

/-- **Exercise 22.4** (Miao, p. 799), the optimal contract, corrected (`A = 0`). With CARA
utility, let `(c, w)` be an optimal contract at `v = −1`, and put `aᵢ = e^{−γcᵢ}`,
`dᵢ = −wᵢ`. Then for every `v < 0` the contract `cᵢ(v) = −(1/γ) ln(−aᵢ v)`, `wᵢ(v) = dᵢ v` is
optimal at `v`; `0 < aᵢ₋₁ ≤ aᵢ`, `dᵢ₋₁ ≥ dᵢ > 0`, `Σ πᵢ/dᵢ = 1`,
`Σ πᵢ (e^{−γθᵢ} aᵢ + β dᵢ) = 1`, and `P(v) = [ln(−v) + K]/(γ(1 − β))` with
`K = Σ πᵢ ln aᵢ + β/(1 − β) Σ πᵢ ln dᵢ`. -/
theorem ex_22_4 (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ)
    {c w : Fin (M.N + 1) → ℝ} (h : hi_Optimal M (hi_P M) (-1) c w) :
    let a := fun i => Real.exp (-γ * c i)
    let d := fun i => -w i
    let K := ∑ i, M.prob i * Real.log (a i) + M.β / (1 - M.β) * ∑ i, M.prob i * Real.log (d i)
    (∀ v < 0, hi_Optimal M (hi_P M) v (fun i => -(1 / γ) * Real.log (-(a i * v)))
      (fun i => d i * v)) ∧
    (∀ i, 0 < a i) ∧ Monotone a ∧ (∀ i, 0 < d i) ∧ Antitone d ∧
    ∑ i, M.prob i / d i = 1 ∧
    ∑ i, M.prob i * (Real.exp (-γ * M.θ i) * a i + M.β * d i) = 1 ∧
    ∀ v < 0, hi_P M v = (Real.log (-v) + K) / (γ * (1 - M.β)) := by
  intro a d K
  have hV := hi_cara_vmax M hγ hu
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  obtain ⟨⟨hic, hpk, hwv⟩, hbest⟩ := h
  have hw : ∀ i, w i < 0 := fun i => by have := hwv i; rwa [hV] at this
  obtain ⟨hcm, hwm⟩ := lemma_22_3_1 M c w hic
  have hval := hi_optimal_value M ⟨⟨hic, hpk, hwv⟩, hbest⟩
  -- the value at `−1` and `K`
  have hK : γ * (1 - M.β) * hi_P M (-1) = K := by
    have hPw : ∀ i, hi_P M (w i) =
        (Real.log (d i) + γ * (1 - M.β) * hi_P M (-1)) / (γ * (1 - M.β)) := fun i => by
      rw [ex_22_4_value M hγ hu (hw i)]
    have hc : ∀ i, -c i = Real.log (a i) / γ := fun i => by
      simp only [a, Real.log_exp]; field_simp
    unfold hi_principalValue at hval
    simp only [hc, hPw] at hval
    simp only [K]
    have e : ∑ i, M.prob i * (Real.log (a i) / γ + M.β *
        ((Real.log (d i) + γ * (1 - M.β) * hi_P M (-1)) / (γ * (1 - M.β)))) =
        (∑ i, M.prob i * Real.log (a i)) / γ +
          M.β / (γ * (1 - M.β)) * ∑ i, M.prob i * Real.log (d i) +
          M.β * hi_P M (-1) := by
      have : ∀ i, M.prob i * (Real.log (a i) / γ + M.β *
          ((Real.log (d i) + γ * (1 - M.β) * hi_P M (-1)) / (γ * (1 - M.β)))) =
          M.prob i * Real.log (a i) / γ + M.β / (γ * (1 - M.β)) * (M.prob i * Real.log (d i)) +
            M.prob i * (M.β * hi_P M (-1)) := fun i => by field_simp; ring
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib,
        Finset.sum_add_distrib, hi_sum_const, ← Finset.sum_div, ← Finset.mul_sum]
    rw [e] at hval
    field_simp at hval ⊢
    linarith
  refine ⟨fun v hv => ?_, fun i => Real.exp_pos _, fun i j hij => ?_, fun i => ?_,
    fun i j hij => ?_, ?_, ?_, fun v hv => ?_⟩
  · -- rescale with `k = −ln(−v)/γ`
    have hs := hi_cara_optimal_scale M hγ hu (-Real.log (-v) / γ) ⟨⟨hic, hpk, hwv⟩, hbest⟩
    have ek : Real.exp (-γ * (-Real.log (-v) / γ)) = -v := by
      rw [show -γ * (-Real.log (-v) / γ) = Real.log (-v) by field_simp,
        Real.exp_log (by linarith)]
    rw [ek] at hs
    have e1 : -v * -1 = v := by ring
    have e2 : (fun i => c i + -Real.log (-v) / γ) =
        fun i => -(1 / γ) * Real.log (-(a i * v)) := by
      funext i
      simp only [a]
      rw [show -(Real.exp (-γ * c i) * v) = Real.exp (-γ * c i) * -v by ring,
        Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp]
      field_simp; ring
    have e3 : (fun i => -v * w i) = fun i => d i * v := by funext i; simp only [d]; ring
    rw [e1, e2, e3] at hs
    exact hs
  · simp only [a]
    exact Real.exp_le_exp.2 (by nlinarith [hcm hij])
  · simp only [d]; linarith [hw i]
  · simp only [d]; linarith [hwm hij]
  · -- the martingale property (22.30)
    have hm := hi_martingale_of_shift M (dP := fun x => 1 / (γ * (1 - M.β) * x)) (hi_P_InF M)
      (fun x hx => hi_P_fixed M hx)
      ⟨hic, hpk, hwv⟩ hval (hi_cara_P_hasDerivAt M hγ hu (by norm_num : (-1 : ℝ) < 0))
      fun i => hi_cara_P_hasDerivAt M hγ hu (hw i)
    have hC : 0 < γ * (1 - M.β) := mul_pos hγ h1β
    have e : ∀ i, M.prob i * (1 / (γ * (1 - M.β) * w i)) =
        -(1 / (γ * (1 - M.β))) * (M.prob i / d i) := fun i => by
      simp only [d]; have := (hw i).ne; field_simp
    simp only [e] at hm
    rw [← Finset.mul_sum] at hm
    have : (1 : ℝ) / (γ * (1 - M.β) * -1) = -(1 / (γ * (1 - M.β))) * 1 := by
      rw [mul_neg_one, one_div_neg_eq_neg_one_div, mul_one]
    rw [this] at hm
    exact mul_left_cancel₀ (neg_ne_zero.2 (one_div_ne_zero hC.ne')) hm
  · -- promise keeping at `−1`
    have := hpk
    unfold hi_agentValue at this
    have e : ∀ i, M.prob i * (M.u (M.θ i + c i) + M.β * w i) =
        -(M.prob i * (Real.exp (-γ * M.θ i) * a i + M.β * d i)) := fun i => by
      rw [hu]; simp only [hi_cara, a, d]
      rw [show -γ * (M.θ i + c i) = -γ * M.θ i + -γ * c i by ring, Real.exp_add]; ring
    simp only [e, Finset.sum_neg_distrib] at this
    linarith
  · rw [ex_22_4_value M hγ hu hv, hK]

/-- Exercise 22.4, the printed form: if `cᵢ(v) = −(1/γ) ln(−aᵢ(v + A))` and
`wᵢ(v) = dᵢ v + (dᵢ − 1)A` keep the promise at two distinct values `v₁ ≠ v₂` (with
`vⱼ + A < 0`), then `A = 0`. -/
theorem hi_ex_22_4_A_eq_zero (M : HIModel) {γ : ℝ} (hγ : 0 < γ) (hu : M.u = hi_cara γ)
    {a d : Fin (M.N + 1) → ℝ} (ha : ∀ i, 0 < a i) {A v1 v2 : ℝ} (h12 : v1 ≠ v2)
    (hv1 : v1 + A < 0) (hv2 : v2 + A < 0)
    (hpk : ∀ v ∈ ({v1, v2} : Set ℝ),
      hi_agentValue M (fun i => -(1 / γ) * Real.log (-(a i * (v + A))))
      (fun i => d i * v + (d i - 1) * A) = v) : A = 0 := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  set S := ∑ i, M.prob i * (Real.exp (-γ * M.θ i) * a i)
  set D := ∑ i, M.prob i * d i
  have hform : ∀ v, v + A < 0 → hi_agentValue M (fun i => -(1 / γ) * Real.log (-(a i * (v + A))))
      (fun i => d i * v + (d i - 1) * A) = (v + A) * S + M.β * (D * v + (D - 1) * A) := by
    intro v hv
    unfold hi_agentValue
    have e : ∀ i, M.prob i * (M.u (M.θ i + -(1 / γ) * Real.log (-(a i * (v + A)))) +
        M.β * (d i * v + (d i - 1) * A)) = (v + A) * (M.prob i * (Real.exp (-γ * M.θ i) * a i)) +
        M.β * (v * (M.prob i * d i) + A * (M.prob i * d i) - A * M.prob i) := fun i => by
      rw [hu]; simp only [hi_cara]
      have hpos : 0 < -(a i * (v + A)) := by nlinarith [ha i]
      rw [show -γ * (M.θ i + -(1 / γ) * Real.log (-(a i * (v + A)))) =
        -γ * M.θ i + Real.log (-(a i * (v + A))) by field_simp; ring, Real.exp_add,
        Real.exp_log hpos]
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, M.prob_sum]
    ring
  have e1 := hpk v1 (by simp)
  have e2 := hpk v2 (by simp)
  rw [hform v1 hv1] at e1
  rw [hform v2 hv2] at e2
  -- subtracting: `(v₁ − v₂)(S + βD − 1) = 0`
  have hS : S + M.β * D = 1 := by
    have : (v1 - v2) * (S + M.β * D - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h12
    · linarith
  have : A * (1 - M.β) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · linarith

/-- **Exercise 22.4** (Miao, p. 799), the printed form is inconsistent: there are no positive
`aᵢ` and constants `dᵢ`, `A = Σ πᵢ/aᵢ` for which the printed contract
`cᵢ = −(1/γ) ln(−aᵢ(v + A))`, `wᵢ = dᵢ v + (dᵢ − 1)A` keeps the promise for all `v < −A`. -/
theorem ex_22_4_printed_inconsistent (M : HIModel) {γ : ℝ} (hγ : 0 < γ)
    (hu : M.u = hi_cara γ) :
    ¬ ∃ (a d : Fin (M.N + 1) → ℝ) (A : ℝ), (∀ i, 0 < a i) ∧ ∑ i, M.prob i / a i = A ∧
      ∀ v, v + A < 0 → hi_agentValue M (fun i => -(1 / γ) * Real.log (-(a i * (v + A))))
        (fun i => d i * v + (d i - 1) * A) = v := by
  rintro ⟨a, d, A, ha, hA, hpk⟩
  have h0 := hi_ex_22_4_A_eq_zero M hγ hu ha (v1 := -A - 1) (v2 := -A - 2) (by norm_num)
    (by linarith) (by linarith) (by
      intro v hv
      rcases hv with rfl | rfl
      · exact hpk _ (by linarith)
      · exact hpk _ (by linarith))
  have hpos : 0 < ∑ i, M.prob i / a i :=
    Finset.sum_pos (fun i _ => div_pos (M.prob_pos i) (ha i)) Finset.univ_nonempty
  linarith

/-- **Exercise 22.3** (Miao, p. 798), the half that holds for every `β`: in per-period terms the
value function never exceeds the first best, `(1 − β) P(ṽ/(1 − β)) ≤ θ̄ − u⁻¹(ṽ)` for
`ṽ < sup u`. -/
theorem ex_22_3_upper (M : HIModel) {vt : ℝ} (hvt : vt < hi_ubar M) :
    (1 - M.β) * hi_P M (vt / (1 - M.β)) ≤ hi_θbar M - hi_uinv M vt := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hv : vt / (1 - M.β) < hi_vmax M := by
    rw [hi_lt_vmax_iff, mul_div_cancel₀ _ h1β.ne']; exact hvt
  have := (hi_P_InF M _ hv).2
  unfold hi_U hi_cstar at this
  rw [mul_div_cancel₀ _ h1β.ne'] at this
  rw [le_div_iff₀ h1β] at this
  linarith

/-- Exercise 22.3: in per-period terms both bounds of (22.26) are independent of `β`:
`(1 − β) U(ṽ/(1 − β)) = θ̄ − u⁻¹(ṽ)` and `(1 − β) L(ṽ/(1 − β)) = −b̃(ṽ)` where
`Σ πᵢ u(θᵢ + b̃) = ṽ`. So the bounds alone cannot give the limit `β → 1`. -/
theorem hi_normalized_bounds (M : HIModel) {vt : ℝ} (hvt : vt < hi_ubar M) :
    (1 - M.β) * hi_U M (vt / (1 - M.β)) = hi_θbar M - hi_uinv M vt ∧
      (1 - M.β) * hi_L M (vt / (1 - M.β)) = -hi_b M (vt / (1 - M.β)) ∧
      hi_Bfun M (hi_b M (vt / (1 - M.β))) = vt := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hv : vt / (1 - M.β) < hi_vmax M := by
    rw [hi_lt_vmax_iff, mul_div_cancel₀ _ h1β.ne']; exact hvt
  refine ⟨?_, ?_, ?_⟩
  · unfold hi_U hi_cstar; rw [mul_div_cancel₀ _ h1β.ne']; field_simp
  · unfold hi_L; field_simp
  · rw [hi_b_spec M hv, mul_div_cancel₀ _ h1β.ne']

end Miao.RecursiveContracts

set_option linter.style.longLine false
#print axioms Miao.RecursiveContracts.lc_condExp
#print axioms Miao.RecursiveContracts.lc_IsStochastic
#print axioms Miao.RecursiveContracts.lc_autarky
#print axioms Miao.RecursiveContracts.lc_condExp_abs_le
#print axioms Miao.RecursiveContracts.lc_condExp_iter_abs_le
#print axioms Miao.RecursiveContracts.lc_exists_bound
#print axioms Miao.RecursiveContracts.lc_autarky_summable
#print axioms Miao.RecursiveContracts.lc_autarky_recursion
#print axioms Miao.RecursiveContracts.lc_autarky_unique
#print axioms Miao.RecursiveContracts.lc_condExp_iter_linear
#print axioms Miao.RecursiveContracts.lc_autarky_split
#print axioms Miao.RecursiveContracts.lc_ext
#print axioms Miao.RecursiveContracts.lc_treeExp
#print axioms Miao.RecursiveContracts.lc_treeValue
#print axioms Miao.RecursiveContracts.lc_treeExp_abs_le
#print axioms Miao.RecursiveContracts.lc_treeValue_summable
#print axioms Miao.RecursiveContracts.lc_treeValue_recursion
#print axioms Miao.RecursiveContracts.lc_treeExp_state
#print axioms Miao.RecursiveContracts.lc_IC
#print axioms Miao.RecursiveContracts.lc_PK
#print axioms Miao.RecursiveContracts.lc_BddPlan
#print axioms Miao.RecursiveContracts.lc_principalValue
#print axioms Miao.RecursiveContracts.eq_22_1
#print axioms Miao.RecursiveContracts.eq_22_2
#print axioms Miao.RecursiveContracts.eq_22_3
#print axioms Miao.RecursiveContracts.eq_22_4
#print axioms Miao.RecursiveContracts.lc_principal_recursion
#print axioms Miao.RecursiveContracts.lc_continuation_feasible
#print axioms Miao.RecursiveContracts.lc_feasible
#print axioms Miao.RecursiveContracts.lc_obj
#print axioms Miao.RecursiveContracts.lc_valueSet
#print axioms Miao.RecursiveContracts.lc_BellmanAt
#print axioms Miao.RecursiveContracts.lc_Bellman
#print axioms Miao.RecursiveContracts.lc_Optimal
#print axioms Miao.RecursiveContracts.lc_BellmanAt.lc_obj_le
#print axioms Miao.RecursiveContracts.lc_BellmanAt.lc_exists_optimal
#print axioms Miao.RecursiveContracts.lc_feasible_convex
#print axioms Miao.RecursiveContracts.lc_bellman_concave
#print axioms Miao.RecursiveContracts.lc_bellman_antitone
#print axioms Miao.RecursiveContracts.lc_promise_keeping_binds
#print axioms Miao.RecursiveContracts.lc_inv_hasDerivAt
#print axioms Miao.RecursiveContracts.eq_22_8
#print axioms Miao.RecursiveContracts.eq_22_7
#print axioms Miao.RecursiveContracts.lc_lagrangian
#print axioms Miao.RecursiveContracts.eq_22_5
#print axioms Miao.RecursiveContracts.lc_sum_update
#print axioms Miao.RecursiveContracts.eq_22_6
#print axioms Miao.RecursiveContracts.eq_22_9
#print axioms Miao.RecursiveContracts.lc_binding_case
#print axioms Miao.RecursiveContracts.lc_slack_case
#print axioms Miao.RecursiveContracts.lc_optimal_contract
#print axioms Miao.RecursiveContracts.eq_22_11
#print axioms Miao.RecursiveContracts.lc_consumption_eventually_constant
#print axioms Miao.RecursiveContracts.lc_iid_value_shift
#print axioms Miao.RecursiveContracts.lc_iid_promised_value
#print axioms Miao.RecursiveContracts.lc_iid_full_insurance
#print axioms Miao.RecursiveContracts.lc_absorbP
#print axioms Miao.RecursiveContracts.lc_absorbP_of_le
#print axioms Miao.RecursiveContracts.lc_exp_ge_tangent
#print axioms Miao.RecursiveContracts.lc_absorbing_bellman
#print axioms Miao.RecursiveContracts.lc_bellman_one_state
#print axioms Miao.RecursiveContracts.lc_promise_decrease_counterexample
#print axioms Miao.RecursiveContracts.lc_detValue
#print axioms Miao.RecursiveContracts.lc_summable_geom
#print axioms Miao.RecursiveContracts.lc_detValue_abs_le
#print axioms Miao.RecursiveContracts.lc_detValue_split
#print axioms Miao.RecursiveContracts.lc_detValue_succ
#print axioms Miao.RecursiveContracts.lc_detValue_split0
#print axioms Miao.RecursiveContracts.lc_detValue_sub
#print axioms Miao.RecursiveContracts.lc_detValue_mono
#print axioms Miao.RecursiveContracts.lc_detValue_const
#print axioms Miao.RecursiveContracts.lc_cumMult
#print axioms Miao.RecursiveContracts.eq_22_10
#print axioms Miao.RecursiveContracts.lc_triangle_swap
#print axioms Miao.RecursiveContracts.lc_lagrangian_rewrite_finite
#print axioms Miao.RecursiveContracts.lc_lagrangian_rewrite
#print axioms Miao.RecursiveContracts.lc_lagrangian_foc
#print axioms Miao.RecursiveContracts.lc_multiplier_value_derivative
#print axioms Miao.RecursiveContracts.lc_detU
#print axioms Miao.RecursiveContracts.lc_detPrincipal
#print axioms Miao.RecursiveContracts.lc_detFeasible
#print axioms Miao.RecursiveContracts.lc_lagrangian_sufficiency
#print axioms Miao.RecursiveContracts.lc_first_best
#print axioms Miao.RecursiveContracts.lc_B
#print axioms Miao.RecursiveContracts.lc_S
#print axioms Miao.RecursiveContracts.lc_A
#print axioms Miao.RecursiveContracts.lc_m
#print axioms Miao.RecursiveContracts.lc_run
#print axioms Miao.RecursiveContracts.lc_B_add
#print axioms Miao.RecursiveContracts.lc_S_add
#print axioms Miao.RecursiveContracts.lc_B_mul
#print axioms Miao.RecursiveContracts.lc_B_nonneg
#print axioms Miao.RecursiveContracts.lc_B_ge_one
#print axioms Miao.RecursiveContracts.lc_B_mul_le
#print axioms Miao.RecursiveContracts.lc_S_abs_le
#print axioms Miao.RecursiveContracts.lc_A_abs_le
#print axioms Miao.RecursiveContracts.lc_A_bddBelow
#print axioms Miao.RecursiveContracts.lc_m_le_A
#print axioms Miao.RecursiveContracts.lc_m_abs_le
#print axioms Miao.RecursiveContracts.lc_m_le_x
#print axioms Miao.RecursiveContracts.lc_S_ge_m
#print axioms Miao.RecursiveContracts.lc_A_tendsto
#print axioms Miao.RecursiveContracts.lc_exists_low
#print axioms Miao.RecursiveContracts.lc_block_le
#print axioms Miao.RecursiveContracts.lc_block_eq
#print axioms Miao.RecursiveContracts.lc_tail_le
#print axioms Miao.RecursiveContracts.lc_tail_eq
#print axioms Miao.RecursiveContracts.lc_run_succ
#print axioms Miao.RecursiveContracts.lc_run_ge
#print axioms Miao.RecursiveContracts.lc_run_mono
#print axioms Miao.RecursiveContracts.lc_run_add
#print axioms Miao.RecursiveContracts.lc_run_eq_first
#print axioms Miao.RecursiveContracts.lc_run_abs_le
#print axioms Miao.RecursiveContracts.lc_zhang_identity
#print axioms Miao.RecursiveContracts.lc_incr
#print axioms Miao.RecursiveContracts.lc_cumMult_incr
#print axioms Miao.RecursiveContracts.lc_g_strictMono
#print axioms Miao.RecursiveContracts.lc_detValue_shift
#print axioms Miao.RecursiveContracts.lc_optimal_of_marginal
#print axioms Miao.RecursiveContracts.ex_22_1a
#print axioms Miao.RecursiveContracts.ex_22_1b
#print axioms Miao.RecursiveContracts.ex_22_1c
#print axioms Miao.RecursiveContracts.lc_d_tau
#print axioms Miao.RecursiveContracts.lc_d_markov
#print axioms Miao.RecursiveContracts.lc_h_isGLB
#print axioms Miao.RecursiveContracts.lc_zpath
#print axioms Miao.RecursiveContracts.lc_zpath_abs_le
#print axioms Miao.RecursiveContracts.lc_c0_strictMono
#print axioms Miao.RecursiveContracts.lc_c0_gt_h
#print axioms Miao.RecursiveContracts.lc_ex_22_1c_min_not_attained
#print axioms Miao.RecursiveContracts.lc_h_depends_on_future
#print axioms Miao.RecursiveContracts.ex_22_2a
#print axioms Miao.RecursiveContracts.ha_histDensity
#print axioms Miao.RecursiveContracts.ha_histDensity_succ
#print axioms Miao.RecursiveContracts.ha_histDensity_nonneg
#print axioms Miao.RecursiveContracts.ha_histDensity_iid
#print axioms Miao.RecursiveContracts.ha_seqPrincipalValue
#print axioms Miao.RecursiveContracts.ha_seqAgentValue
#print axioms Miao.RecursiveContracts.ha_seqIC
#print axioms Miao.RecursiveContracts.ha_seqPC
#print axioms Miao.RecursiveContracts.ha_agentValue
#print axioms Miao.RecursiveContracts.ha_principalValue
#print axioms Miao.RecursiveContracts.ha_IC
#print axioms Miao.RecursiveContracts.ha_PK
#print axioms Miao.RecursiveContracts.ha_FOA
#print axioms Miao.RecursiveContracts.ha_IsPrincipalValue
#print axioms Miao.RecursiveContracts.ha_principalValue_le
#print axioms Miao.RecursiveContracts.ha_integral_fa_eq_zero
#print axioms Miao.RecursiveContracts.ha_linearDensity_hasDerivAt
#print axioms Miao.RecursiveContracts.eq_22_16
#print axioms Miao.RecursiveContracts.ha_pointLagr
#print axioms Miao.RecursiveContracts.eq_22_17
#print axioms Miao.RecursiveContracts.eq_22_19
#print axioms Miao.RecursiveContracts.eq_22_20
#print axioms Miao.RecursiveContracts.eq_22_18
#print axioms Miao.RecursiveContracts.ha_envelope
#print axioms Miao.RecursiveContracts.ha_envelope_condition
#print axioms Miao.RecursiveContracts.ha_expect
#print axioms Miao.RecursiveContracts.ha_cov
#print axioms Miao.RecursiveContracts.ha_expect_mul_eq_cov_add
#print axioms Miao.RecursiveContracts.ha_integral_mean_value
#print axioms Miao.RecursiveContracts.ha_sign_change
#print axioms Miao.RecursiveContracts.ha_mlrc_integral_nonneg
#print axioms Miao.RecursiveContracts.ha_mlrc_integral_pos
#print axioms Miao.RecursiveContracts.ha_expect_lr
#print axioms Miao.RecursiveContracts.ha_cov_lr_eq
#print axioms Miao.RecursiveContracts.ha_cov_lr_nonneg
#print axioms Miao.RecursiveContracts.ha_inv_expect_inv_le
#print axioms Miao.RecursiveContracts.ha_inv_expect_inv_lt
#print axioms Miao.RecursiveContracts.ha_one_div_strictMono
#print axioms Miao.RecursiveContracts.eq_22_21
#print axioms Miao.RecursiveContracts.eq_22_22
#print axioms Miao.RecursiveContracts.proposition_22_2_1
#print axioms Miao.RecursiveContracts.ha_first_best_income
#print axioms Miao.RecursiveContracts.ha_mu_pos
#print axioms Miao.RecursiveContracts.ha_c_strictMonoOn
#print axioms Miao.RecursiveContracts.ha_w_strictMonoOn
#print axioms Miao.RecursiveContracts.ha_eq_22_20_deriv
#print axioms Miao.RecursiveContracts.ha_eq_22_17_deriv
#print axioms Miao.RecursiveContracts.ha_cy_pos_iff_wy_pos
#print axioms Miao.RecursiveContracts.proposition_22_2_2
#print axioms Miao.RecursiveContracts.ha_cy_eq_zero_of_ry_zero
#print axioms Miao.RecursiveContracts.ha_flat_mlrc_density
#print axioms Miao.RecursiveContracts.ha_contract_dynamics
#print axioms Miao.RecursiveContracts.proposition_22_2_3
#print axioms Miao.RecursiveContracts.ha_inverse_euler_inv
#print axioms Miao.RecursiveContracts.ha_marginal_value_martingale
#print axioms Miao.RecursiveContracts.ha_jensen
#print axioms Miao.RecursiveContracts.ha_jensen_strict
#print axioms Miao.RecursiveContracts.ha_jensen_strict_of_mu_pos
#print axioms Miao.RecursiveContracts.ha_tangent_lt
#print axioms Miao.RecursiveContracts.ha_no_borrow
#print axioms Miao.RecursiveContracts.ha_wants_to_save
#print axioms Miao.RecursiveContracts.ha_rogerson_save
#print axioms Miao.RecursiveContracts.ha_proposition_22_2_3_printed_false
#print axioms Miao.RecursiveContracts.HIModel
#print axioms Miao.RecursiveContracts.HIModel.mk
#print axioms Miao.RecursiveContracts.HIModel.N
#print axioms Miao.RecursiveContracts.HIModel.θ
#print axioms Miao.RecursiveContracts.HIModel.prob
#print axioms Miao.RecursiveContracts.HIModel.β
#print axioms Miao.RecursiveContracts.HIModel.u
#print axioms Miao.RecursiveContracts.HIModel.θ_strictMono
#print axioms Miao.RecursiveContracts.HIModel.prob_pos
#print axioms Miao.RecursiveContracts.HIModel.prob_sum
#print axioms Miao.RecursiveContracts.HIModel.β_pos
#print axioms Miao.RecursiveContracts.HIModel.β_lt_one
#print axioms Miao.RecursiveContracts.HIModel.u_cont
#print axioms Miao.RecursiveContracts.HIModel.u_strictMono
#print axioms Miao.RecursiveContracts.HIModel.u_strictConcave
#print axioms Miao.RecursiveContracts.HIModel.u_bddAbove
#print axioms Miao.RecursiveContracts.HIModel.u_not_bddBelow
#print axioms Miao.RecursiveContracts.hi_C
#print axioms Miao.RecursiveContracts.hi_IC
#print axioms Miao.RecursiveContracts.hi_LocalIC
#print axioms Miao.RecursiveContracts.hi_agentValue
#print axioms Miao.RecursiveContracts.hi_principalValue
#print axioms Miao.RecursiveContracts.hi_ubar
#print axioms Miao.RecursiveContracts.hi_vmax
#print axioms Miao.RecursiveContracts.hi_Feasible
#print axioms Miao.RecursiveContracts.hi_strict_decreasing_increments
#print axioms Miao.RecursiveContracts.hi_decreasing_increments
#print axioms Miao.RecursiveContracts.hi_C_add_C
#print axioms Miao.RecursiveContracts.hi_pair_mono
#print axioms Miao.RecursiveContracts.hi_local_mono
#print axioms Miao.RecursiveContracts.lemma_22_3_1
#print axioms Miao.RecursiveContracts.hi_down_step
#print axioms Miao.RecursiveContracts.hi_up_step
#print axioms Miao.RecursiveContracts.lemma_22_3_2
#print axioms Miao.RecursiveContracts.hi_upward_of_binding
#print axioms Miao.RecursiveContracts.hi_C_shift
#print axioms Miao.RecursiveContracts.hi_agentValue_shift
#print axioms Miao.RecursiveContracts.hi_cara
#print axioms Miao.RecursiveContracts.hi_cara_strictMono
#print axioms Miao.RecursiveContracts.hi_cara_strictConcave
#print axioms Miao.RecursiveContracts.hi_cara_sSup
#print axioms Miao.RecursiveContracts.hi_cara_not_bddBelow
#print axioms Miao.RecursiveContracts.hi_caraModel
#print axioms Miao.RecursiveContracts.hi_exampleModel
#print axioms Miao.RecursiveContracts.hi_exampleModel_N
#print axioms Miao.RecursiveContracts.assumption_22_3_1
#print axioms Miao.RecursiveContracts.hi_cara_assumption_22_3_1
#print axioms Miao.RecursiveContracts.hi_modelOfAssumption
#print axioms Miao.RecursiveContracts.hi_dara_ratio_mono
#print axioms Miao.RecursiveContracts.hi_dara_ce
#print axioms Miao.RecursiveContracts.hi_exists_mix
#print axioms Miao.RecursiveContracts.hi_mix_c_le
#print axioms Miao.RecursiveContracts.hi_mix_agentValue
#print axioms Miao.RecursiveContracts.hi_mix_principal_ge
#print axioms Miao.RecursiveContracts.hi_mix_C_eq
#print axioms Miao.RecursiveContracts.hi_mix_downward
#print axioms Miao.RecursiveContracts.hi_u_lt_ubar
#print axioms Miao.RecursiveContracts.hi_u_surj
#print axioms Miao.RecursiveContracts.hi_uinv
#print axioms Miao.RecursiveContracts.hi_u_uinv
#print axioms Miao.RecursiveContracts.hi_lt_vmax_iff
#print axioms Miao.RecursiveContracts.hi_sum_const
#print axioms Miao.RecursiveContracts.hi_cstar
#print axioms Miao.RecursiveContracts.hi_Bfun
#print axioms Miao.RecursiveContracts.hi_Bfun_strictMono
#print axioms Miao.RecursiveContracts.hi_Bfun_bounds
#print axioms Miao.RecursiveContracts.hi_Bfun_surj
#print axioms Miao.RecursiveContracts.hi_b
#print axioms Miao.RecursiveContracts.hi_b_spec
#print axioms Miao.RecursiveContracts.hi_cstar_spec
#print axioms Miao.RecursiveContracts.hi_θbar
#print axioms Miao.RecursiveContracts.hi_L
#print axioms Miao.RecursiveContracts.hi_U
#print axioms Miao.RecursiveContracts.hi_U_eq_sum
#print axioms Miao.RecursiveContracts.hi_InF
#print axioms Miao.RecursiveContracts.hi_b_le_cstar
#print axioms Miao.RecursiveContracts.hi_U_sub_L_le
#print axioms Miao.RecursiveContracts.hi_agentValue_lt_vmax
#print axioms Miao.RecursiveContracts.hi_vals
#print axioms Miao.RecursiveContracts.hi_T
#print axioms Miao.RecursiveContracts.hi_const_feasible
#print axioms Miao.RecursiveContracts.hi_const_value
#print axioms Miao.RecursiveContracts.hi_principal_le_U
#print axioms Miao.RecursiveContracts.hi_vals_nonempty
#print axioms Miao.RecursiveContracts.hi_vals_bddAbove
#print axioms Miao.RecursiveContracts.hi_le_T
#print axioms Miao.RecursiveContracts.eq_22_26
#print axioms Miao.RecursiveContracts.hi_T_le_add
#print axioms Miao.RecursiveContracts.hi_T_abs_le
#print axioms Miao.RecursiveContracts.hi_InF_abs_sub
#print axioms Miao.RecursiveContracts.hi_Pk
#print axioms Miao.RecursiveContracts.hi_L_InF
#print axioms Miao.RecursiveContracts.hi_Pk_InF
#print axioms Miao.RecursiveContracts.hi_Pk_succ_abs
#print axioms Miao.RecursiveContracts.hi_Pk_cauchy
#print axioms Miao.RecursiveContracts.hi_P
#print axioms Miao.RecursiveContracts.hi_Pk_tendsto
#print axioms Miao.RecursiveContracts.hi_P_abs_sub
#print axioms Miao.RecursiveContracts.hi_P_InF
#print axioms Miao.RecursiveContracts.hi_P_fixed
#print axioms Miao.RecursiveContracts.hi_fixed_unique
#print axioms Miao.RecursiveContracts.hi_b_mono
#print axioms Miao.RecursiveContracts.hi_L_antitoneOn
#print axioms Miao.RecursiveContracts.hi_T_antitoneOn
#print axioms Miao.RecursiveContracts.hi_Pk_antitoneOn
#print axioms Miao.RecursiveContracts.proposition_22_3_1
#print axioms Miao.RecursiveContracts.hi_concaveOn_of_tendsto
#print axioms Miao.RecursiveContracts.assumption_22_3_2
#print axioms Miao.RecursiveContracts.hi_Optimal
#print axioms Miao.RecursiveContracts.hi_incr_le_on
#print axioms Miao.RecursiveContracts.hi_slope_strict_anti
#print axioms Miao.RecursiveContracts.hi_upperMass
#print axioms Miao.RecursiveContracts.hi_upperMass_bounds
#print axioms Miao.RecursiveContracts.hi_reduce
#print axioms Miao.RecursiveContracts.hi_reduce_mean
#print axioms Miao.RecursiveContracts.hi_spread_reduction
#print axioms Miao.RecursiveContracts.hi_sum_mul_left
#print axioms Miao.RecursiveContracts.proposition_22_3_2
#print axioms Miao.RecursiveContracts.hi_sum_ite
#print axioms Miao.RecursiveContracts.proposition_22_3_3
#print axioms Miao.RecursiveContracts.hi_θsucc
#print axioms Miao.RecursiveContracts.hi_FOC
#print axioms Miao.RecursiveContracts.eq_22_30
#print axioms Miao.RecursiveContracts.hi_martingale_of_shift
#print axioms Miao.RecursiveContracts.hi_strictAntiOn_deriv
#print axioms Miao.RecursiveContracts.lemma_22_3_3
#print axioms Miao.RecursiveContracts.hi_lemma_22_3_3_one_state
#print axioms Miao.RecursiveContracts.hi_incr_le_on_concave
#print axioms Miao.RecursiveContracts.hi_slope_anti_concave
#print axioms Miao.RecursiveContracts.hi_spread_reduction_weak
#print axioms Miao.RecursiveContracts.hi_reduce_incr
#print axioms Miao.RecursiveContracts.hi_adjust_increments
#print axioms Miao.RecursiveContracts.hi_deriv_strictAnti
#print axioms Miao.RecursiveContracts.hi_tangent
#print axioms Miao.RecursiveContracts.hi_pool_cost
#print axioms Miao.RecursiveContracts.hi_steps
#print axioms Miao.RecursiveContracts.hi_pool
#print axioms Miao.RecursiveContracts.hi_repair
#print axioms Miao.RecursiveContracts.hi_mix_repair
#print axioms Miao.RecursiveContracts.hi_T_concaveOn
#print axioms Miao.RecursiveContracts.hi_L_concaveOn
#print axioms Miao.RecursiveContracts.hi_Pk_concaveOn
#print axioms Miao.RecursiveContracts.proposition_22_3_1_concave
#print axioms Miao.RecursiveContracts.hi_proposition_22_3_2_concave
#print axioms Miao.RecursiveContracts.hi_vseq
#print axioms Miao.RecursiveContracts.hi_vseq_congr
#print axioms Miao.RecursiveContracts.hi_vseq_lt
#print axioms Miao.RecursiveContracts.hi_poverty_det
#print axioms Miao.RecursiveContracts.hi_filt
#print axioms Miao.RecursiveContracts.hi_filt_meas
#print axioms Miao.RecursiveContracts.hi_tuple_sm_aux
#print axioms Miao.RecursiveContracts.hi_tuple_sm
#print axioms Miao.RecursiveContracts.hi_tuple_int
#print axioms Miao.RecursiveContracts.hi_Fseq
#print axioms Miao.RecursiveContracts.hi_vseq_eq_Fseq
#print axioms Miao.RecursiveContracts.hi_poverty_martingale
#print axioms Miao.RecursiveContracts.proposition_22_3_4
#print axioms Miao.RecursiveContracts.hi_exampleModel_vmax
#print axioms Miao.RecursiveContracts.hi_exampleW
#print axioms Miao.RecursiveContracts.hi_poverty_example
#print axioms Miao.RecursiveContracts.hi_cara_shift
#print axioms Miao.RecursiveContracts.hi_cara_vmax
#print axioms Miao.RecursiveContracts.hi_cara_scale_feasible
#print axioms Miao.RecursiveContracts.hi_cara_b_shift
#print axioms Miao.RecursiveContracts.hi_cara_cstar_shift
#print axioms Miao.RecursiveContracts.hi_scaleFn
#print axioms Miao.RecursiveContracts.hi_scaleFn_InF
#print axioms Miao.RecursiveContracts.hi_pv_scaleFn
#print axioms Miao.RecursiveContracts.hi_T_scaleFn
#print axioms Miao.RecursiveContracts.hi_cara_P_scale
#print axioms Miao.RecursiveContracts.ex_22_4_value
#print axioms Miao.RecursiveContracts.hi_cara_P_hasDerivAt
#print axioms Miao.RecursiveContracts.hi_cara_pv_scale
#print axioms Miao.RecursiveContracts.hi_cara_optimal_scale
#print axioms Miao.RecursiveContracts.hi_optimal_value
#print axioms Miao.RecursiveContracts.ex_22_4
#print axioms Miao.RecursiveContracts.hi_ex_22_4_A_eq_zero
#print axioms Miao.RecursiveContracts.ex_22_4_printed_inconsistent
#print axioms Miao.RecursiveContracts.ex_22_3_upper
#print axioms Miao.RecursiveContracts.hi_normalized_bounds
