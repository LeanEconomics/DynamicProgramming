import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Order.Compact
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Independence.Integration
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Uncertainty, preferences and endowments

Miao, §13.1, pp. 415–416: the event tree, adapted processes, the spaces `L∞` and `L¹`,
discounted expected utility (13.1) and Assumption 13.1.1.

* Histories. The state `s₀` is given, so a node `sᵗ = (s₀, s₁, …, s_t)` is recorded by the
  list `[s_t, …, s₁] : List S` of the later shocks, newest first. The root `s⁰` is `[]`, the time
  of a node is its length, its immediate successors are `s :: h` and its immediate predecessor is
  the tail (`po_unique_predecessor`). The nodes at `T` following `sᵗ` are `ofFn f ++ h` with
  `f : Fin (T - t) → S`.
* `POProb S`: the probabilities `Pr(sᵗ)` of the histories: nonnegative, `Pr(s⁰) = 1`, and
  consistent, `Pr(sᵗ) = Σ_s Pr(sᵗ, s)`. They sum to one at every date (`po_sum_pr_time`), and the
  conditional probabilities `Pr(sᵀ | sᵗ)` sum to one over the nodes following `sᵗ`
  (`po_condPr_sum`). The i.i.d. tree `po_iid` is a concrete instance.
* An adapted process is a real function on nodes; `po_Linfty`, `po_L1` and `po_Lplus` (the
  nonnegative processes of `L∞`) are the spaces of the text.
* `POEconomy ι S`: the discount factor `β ∈ (0, 1)`, the tree probabilities and the felicity
  functions `uⁱ`, each strictly increasing on `[0, ∞)` (the monotonicity part of Assumption
  13.1.1, used throughout). `po_U E i x = Σ_{t, sᵗ} βᵗ uⁱ(x_t(sᵗ)) Pr(sᵗ)` is (13.1); it is a
  convergent sum on `L∞₊` (`eq_13_1`).
* `Assumption13_1_1`: strictly increasing, `C²` and the Inada conditions on `(0, ∞)`, strictly
  concave. Departure: the text does not say on which domain; since consumption lies in `L∞₊`,
  which contains `0`, monotonicity, concavity and continuity are asked on `[0, ∞)`, and
  differentiability and the Inada conditions on `(0, ∞)`. `√·` satisfies it
  (`assumption_13_1_1_sqrt`), and `po_exampleEconomy` is a concrete economy.
-/

namespace Miao.CompleteMarkets

open Filter Topology

/-- Miao, §13.1, p. 416: the probabilities `Pr(sᵗ)` of the nodes of the event tree, with
`Pr(s⁰) = 1` and `Pr(sᵗ) = Σ_{s_{t+1}} Pr(sᵗ⁺¹)`. A history is a list of shocks, newest first. -/
structure POProb (S : Type*) [Fintype S] where
  /-- The unconditional probability `Pr(sᵗ)` of a node. -/
  pr : List S → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ h, 0 ≤ pr h
  /-- `Pr(s₀) = 1`. -/
  root : pr [] = 1
  /-- The probability of a node is the sum over its immediate successors. -/
  consistent : ∀ h, ∑ s, pr (s :: h) = pr h

/-- Miao, §13.1, p. 416: each node `sᵗ ≠ s⁰` has a unique immediate predecessor `sᵗ⁻`. -/
theorem po_unique_predecessor {S : Type*} (h : List S) (hne : h ≠ []) :
    ∃! g : List S, ∃ s, h = s :: g := by
  obtain ⟨s, g, rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨g, ⟨s, rfl⟩, ?_⟩
  rintro g' ⟨s', hs'⟩
  exact (List.cons_eq_cons.mp hs').2.symm

/-- Miao, §13.1, p. 416: an immediate successor `sᵗ⁺ = (sᵗ, s)` of a node at date `t` is a node
at date `t + 1`, and its immediate predecessor is `sᵗ`. -/
theorem po_successor {S : Type*} (h : List S) (s : S) :
    (s :: h).length = h.length + 1 ∧ (s :: h).tail = h :=
  ⟨rfl, rfl⟩

/-- Miao, §13.1, p. 416: the probabilities of the `k`-step continuations `sᵗ⁺ᵏ | sᵗ` of a node
sum to `Pr(sᵗ)`. -/
theorem po_sum_continuations {S : Type*} [Fintype S] (P : POProb S) (h : List S) :
    ∀ k : ℕ, ∑ f : Fin k → S, P.pr (List.ofFn f ++ h) = P.pr h := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← (Fin.consEquiv fun _ => S).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      List.cons_append]
    simp only [P.consistent]
    exact ih

/-- Miao, §13.1, p. 416: the probabilities of the nodes at any date `t` sum to one. -/
theorem po_sum_pr_time {S : Type*} [Fintype S] (P : POProb S) (t : ℕ) :
    ∑ f : Fin t → S, P.pr (List.ofFn f) = 1 := by
  have := po_sum_continuations P [] t
  simpa [P.root] using this

/-- Miao, §13.1, p. 416: the conditional probability `Pr(sᵀ | sᵗ) = Pr(sᵀ) / Pr(sᵗ)` of a node
`sᵀ` following `sᵗ`. -/
noncomputable def po_condPr {S : Type*} [Fintype S] (P : POProb S) (g h : List S) : ℝ :=
  P.pr g / P.pr h

/-- Miao, §13.1, p. 416: given `sᵗ` with `Pr(sᵗ) > 0`, the conditional probabilities of the
nodes `sᵗ⁺ᵏ | sᵗ` sum to one. -/
theorem po_condPr_sum {S : Type*} [Fintype S] (P : POProb S) (h : List S) (hh : 0 < P.pr h)
    (k : ℕ) : ∑ f : Fin k → S, po_condPr P (List.ofFn f ++ h) h = 1 := by
  unfold po_condPr
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, po_sum_continuations P h k, mul_inv_cancel₀ hh.ne']

/-- Miao, §13.1, p. 416: since `Pr(s₀) = 1`, conditioning on the root does nothing, and
`Pr(sᵀ) = Pr(sᵀ | sᵗ) Pr(sᵗ)` when `Pr(sᵗ) > 0`. -/
theorem po_condPr_root {S : Type*} [Fintype S] (P : POProb S) (g h : List S)
    (hh : 0 < P.pr h) :
    po_condPr P g [] = P.pr g ∧ P.pr g = po_condPr P g h * P.pr h := by
  unfold po_condPr
  refine ⟨by rw [P.root, div_one], ?_⟩
  field_simp

/-- Miao, §13.1: the i.i.d. event tree, `Pr(sᵗ) = p(s₁) ⋯ p(s_t)` for a probability vector
`p`. -/
noncomputable def po_iid {S : Type*} [Fintype S] (p : S → ℝ) (hp : ∀ s, 0 ≤ p s)
    (hsum : ∑ s, p s = 1) : POProb S where
  pr h := (h.map p).prod
  nonneg h := List.prod_nonneg (by
    intro a ha
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha
    exact hp s)
  root := by simp
  consistent h := by
    simp only [List.map_cons, List.prod_cons]
    rw [← Finset.sum_mul, hsum, one_mul]

/-- Miao, §13.1, p. 416: the real valued bounded adapted processes `L∞`. -/
def po_Linfty (S : Type*) : Set (List S → ℝ) :=
  {x | BddAbove (Set.range fun h => |x h|)}

/-- Miao, §13.1, p. 416: the real valued summable adapted processes `L¹`. -/
def po_L1 (S : Type*) : Set (List S → ℝ) :=
  {x | Summable fun h => |x h|}

/-- Miao, §13.1, p. 416: the nonnegative processes `L∞₊` of `L∞`, the consumption set. -/
def po_Lplus (S : Type*) : Set (List S → ℝ) :=
  {x | (∀ h, 0 ≤ x h) ∧ BddAbove (Set.range x)}

/-- Miao, §13.1: `L∞₊ ⊆ L∞`. -/
theorem po_Lplus_subset_Linfty {S : Type*} : po_Lplus S ⊆ po_Linfty S := by
  rintro x ⟨hx0, B, hB⟩
  refine ⟨B, ?_⟩
  rintro _ ⟨h, rfl⟩
  simp only [abs_of_nonneg (hx0 h)]
  exact hB ⟨h, rfl⟩

/-- Miao, §13.1, p. 416: the economy. `I` agents (`ι`), a finite shock set `S`, the discount
factor `β ∈ (0, 1)` common to all agents, the probabilities of the event tree and the felicity
functions `uⁱ`, strictly increasing on the consumption set `[0, ∞)`. -/
structure POEconomy (ι S : Type*) [Fintype S] where
  /-- The common discount factor. -/
  β : ℝ
  /-- `β > 0`. -/
  β_pos : 0 < β
  /-- `β < 1`. -/
  β_lt_one : β < 1
  /-- The probabilities of the event tree. -/
  P : POProb S
  /-- The felicity function of agent `i`. -/
  u : ι → ℝ → ℝ
  /-- Each `uⁱ` is strictly increasing on `[0, ∞)`. -/
  u_mono : ∀ i, StrictMonoOn (u i) (Set.Ici 0)

/-- Miao, (13.1): the weight `βᵗ Pr(sᵗ)` of a node in the discounted expected utility. -/
noncomputable def po_w {ι S : Type*} [Fintype S] (E : POEconomy ι S) (h : List S) : ℝ :=
  E.β ^ h.length * E.P.pr h

/-- Miao, (13.1), p. 416: the discounted expected utility `Uⁱ(x) = Σ_t Σ_{sᵗ} βᵗ uⁱ(x_t(sᵗ))
Pr(sᵗ)`. -/
noncomputable def po_U {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι)
    (x : List S → ℝ) : ℝ :=
  ∑' h, po_w E h * E.u i (x h)

/-- Miao, (13.1): the weights are nonnegative and the root has weight one. -/
theorem po_w_nonneg {ι S : Type*} [Fintype S] (E : POEconomy ι S) (h : List S) :
    0 ≤ po_w E h :=
  mul_nonneg (pow_nonneg E.β_pos.le _) (E.P.nonneg h)

/-- Miao, (13.1): the root `s⁰` has weight `β⁰ Pr(s₀) = 1`. -/
theorem po_w_root {ι S : Type*} [Fintype S] (E : POEconomy ι S) : po_w E [] = 1 := by
  simp [po_w, E.P.root]

/-- Miao, (13.1): the weights at date `t` sum to `βᵗ`. -/
theorem po_sum_w_time {ι S : Type*} [Fintype S] (E : POEconomy ι S) (t : ℕ) :
    ∑ f : Fin t → S, po_w E (List.ofFn f) = E.β ^ t := by
  simp only [po_w, List.length_ofFn]
  rw [← Finset.mul_sum, po_sum_pr_time, mul_one]

/-- Miao, (13.1): the weights `βᵗ Pr(sᵗ)` are summable over the whole tree. -/
theorem po_summable_w {ι S : Type*} [Fintype S] (E : POEconomy ι S) : Summable (po_w E) := by
  rw [← (List.equivSigmaTuple (α := S)).symm.summable_iff]
  change Summable fun x : (Σ n, Fin n → S) => po_w E (List.equivSigmaTuple.symm x)
  rw [summable_sigma_of_nonneg (fun x => po_w_nonneg E _)]
  refine ⟨fun n => (Summable.of_finite), ?_⟩
  have : (fun n => ∑' y : Fin n → S, po_w E ((List.equivSigmaTuple (α := S)).symm ⟨n, y⟩))
      = fun n => E.β ^ n := by
    funext n
    rw [tsum_fintype]
    exact po_sum_w_time E n
  rw [this]
  exact summable_geometric_of_lt_one E.β_pos.le E.β_lt_one

/-- Miao, (13.1), p. 416: for a consumption plan `x ∈ L∞₊` the series defining `Uⁱ(x)`
converges absolutely, so the discounted expected utility is well defined. -/
theorem eq_13_1 {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι) {x : List S → ℝ}
    (hx : x ∈ po_Lplus S) : Summable fun h => po_w E h * E.u i (x h) := by
  obtain ⟨hx0, B, hB⟩ := hx
  have hB' : ∀ h, x h ≤ B := fun h => hB ⟨h, rfl⟩
  have hB0 : 0 ≤ B := (hx0 []).trans (hB' [])
  refine Summable.of_norm_bounded ((po_summable_w E).mul_right
    (|E.u i 0| + |E.u i B|)) fun h => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (po_w_nonneg E h)]
  refine mul_le_mul_of_nonneg_left ?_ (po_w_nonneg E h)
  have h1 : E.u i 0 ≤ E.u i (x h) :=
    (E.u_mono i).monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (hx0 h)) (hx0 h)
  have h2 : E.u i (x h) ≤ E.u i B :=
    (E.u_mono i).monotoneOn (Set.mem_Ici.mpr (hx0 h)) (Set.mem_Ici.mpr hB0) (hB' h)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (E.u i 0), abs_nonneg (E.u i B)]
  · linarith [le_abs_self (E.u i B), abs_nonneg (E.u i 0)]

/-- Miao, **Assumption 13.1.1**, p. 416: `u` is strictly increasing, twice continuously
differentiable, strictly concave and satisfies the Inada conditions `u'(0+) = ∞`,
`u'(∞) = 0`. Monotonicity, strict concavity and continuity are asked on the consumption set
`[0, ∞)`, differentiability and the Inada conditions on `(0, ∞)`. -/
def Assumption13_1_1 (u : ℝ → ℝ) : Prop :=
  StrictMonoOn u (Set.Ici 0) ∧ ContinuousOn u (Set.Ici 0) ∧ ContDiffOn ℝ 2 u (Set.Ioi 0) ∧
    StrictConcaveOn ℝ (Set.Ici 0) u ∧ Tendsto (deriv u) (𝓝[>] 0) atTop ∧
    Tendsto (deriv u) atTop (𝓝 0)

/-- Miao, **Assumption 13.1.1**, p. 416: the felicity function `u(c) = √c` satisfies the
assumption, so it is not vacuous. -/
theorem assumption_13_1_1_sqrt : Assumption13_1_1 (fun c => √c) := by
  have hd : ∀ x : ℝ, 0 < x → deriv (fun c => √c) x = 1 / (2 * √x) := fun x hx =>
    ((Real.deriv_sqrt_aux hx.ne').1.hasDerivAt).deriv
  refine ⟨fun a ha b _ hab => Real.sqrt_lt_sqrt (Set.mem_Ici.mp ha) hab,
    Real.continuous_sqrt.continuousOn, ?_, Real.strictConcaveOn_sqrt, ?_, ?_⟩
  · intro x hx
    exact ((Real.deriv_sqrt_aux (ne_of_gt hx)).2 2).contDiffWithinAt
  · have hcongr : (fun x : ℝ => 1 / (2 * √x)) =ᶠ[𝓝[>] 0] deriv (fun c => √c) :=
      eventually_nhdsWithin_of_forall fun x hx => (hd x hx).symm
    refine Tendsto.congr' hcongr ?_
    have hs : Tendsto (fun x : ℝ => 2 * √x) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun x : ℝ => 2 * √x) (𝓝 0) (𝓝 (2 * √0)) :=
          (Real.continuous_sqrt.const_mul 2).tendsto 0
        rw [Real.sqrt_zero, mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun x hx =>
          Set.mem_Ioi.mpr (by have := Real.sqrt_pos.mpr (Set.mem_Ioi.mp hx); positivity)
    simp only [one_div]
    exact tendsto_inv_nhdsGT_zero.comp hs
  · have hcongr : (fun x : ℝ => 1 / (2 * √x)) =ᶠ[atTop] deriv (fun c => √c) :=
      (eventually_gt_atTop 0).mono fun x hx => (hd x hx).symm
    refine Tendsto.congr' hcongr ?_
    have hs : Tendsto (fun x : ℝ => 2 * √x) atTop atTop :=
      Real.tendsto_sqrt_atTop.const_mul_atTop two_pos
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp hs

/-- The fair coin on `Bool`. -/
noncomputable def po_coin : POProb Bool :=
  po_iid (fun _ => 1 / 2) (fun _ => by norm_num) (by simp)

/-- Miao, §13.1: a concrete economy. Two agents, a fair coin each period, `β = 1/2`, and
`uⁱ(c) = √c` for both agents. -/
noncomputable def po_exampleEconomy : POEconomy (Fin 2) Bool where
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  P := po_coin
  u _ := fun c => √c
  u_mono _ := assumption_13_1_1_sqrt.1

/-- Miao, §13.1: the felicity functions of `po_exampleEconomy` satisfy Assumption 13.1.1. -/
theorem po_exampleEconomy_assumption (i : Fin 2) : Assumption13_1_1 (po_exampleEconomy.u i) :=
  assumption_13_1_1_sqrt

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Pareto optimum

Miao, §13.2, pp. 417–418.

* `po_Feasible y c` is (13.2), with each `cⁱ ∈ L∞₊`; `po_ParetoOptimal` and `po_SolvesPlanner`
  are the definitions of the text.
* **Proposition 13.2.1** (`proposition_13_2_1`): an allocation is Pareto optimal iff it solves
  the planner's problem for some nonzero `λ ∈ ℝᴵ₊`. The "only if" part follows the book: the set
  `𝒰 = {U(x) − U(c) − z}` is convex because each `Uⁱ` is concave (`po_U_concave`), it misses the
  open positive orthant, and Hahn–Banach separates them (`po_planner_of_pareto`). The "if" part
  also follows the book, including the transfer from an agent with zero weight
  (`po_transfer_improvement`), which needs continuity of `uⁱ`. Hypotheses: concavity (only if)
  and continuity (if) of each `uⁱ` on `[0, ∞)`, as in Assumption 13.1.1, and `I ≥ 1`.
* The first-order conditions `λⁱ uⁱ'(cⁱ_t) = λʲ uʲ'(cʲ_t)` (`po_planner_foc`), derived by
  transferring consumption between two agents at one node; (13.3) (`eq_13_3`) and (13.4)
  (`eq_13_4`). The text omits that these hold at nodes of positive probability and for interior
  allocations.
* Risk sharing: consumption depends on the aggregate endowment only (`po_risk_sharing`,
  `po_consumption_fn_aggregate`), so with a Markov aggregate state there is no history dependence
  (`po_no_history_dependence`). The book's argument that (13.4) has one solution in `c¹` is
  replaced by the equivalent monotonicity argument; strictly decreasing marginal utilities
  (`po_strictAntiOn_deriv`, from Assumption 13.1.1) are what is used.
-/

namespace Miao.CompleteMarkets

open Filter Topology

/-- Miao, (13.2), p. 417: the allocation `c = (c¹, …, cᴵ)` is feasible for the endowments `y`:
each `cⁱ ∈ L∞₊` and `Σᵢ cⁱ_t(sᵗ) = Σᵢ yⁱ_t(sᵗ)` at every node. -/
def po_Feasible {ι S : Type*} [Fintype ι] (y c : ι → List S → ℝ) : Prop :=
  (∀ i, c i ∈ po_Lplus S) ∧ ∀ h, ∑ i, c i h = ∑ i, y i h

/-- Miao, §13.2, p. 417: `c` is Pareto optimal if it is feasible and no feasible allocation makes
every agent at least as well off and one agent strictly better off. -/
def po_ParetoOptimal {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (y c : ι → List S → ℝ) : Prop :=
  po_Feasible y c ∧ ¬ ∃ d, po_Feasible y d ∧ (∀ i, po_U E i (c i) ≤ po_U E i (d i)) ∧
    ∃ i, po_U E i (c i) < po_U E i (d i)

/-- Miao, §13.2, p. 417: `c` solves the social planner's problem with Pareto weights `λ`:
it maximises `Σᵢ λⁱ Uⁱ(cⁱ)` subject to (13.2). -/
def po_SolvesPlanner {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (y : ι → List S → ℝ) (lam : ι → ℝ) (c : ι → List S → ℝ) : Prop :=
  po_Feasible y c ∧ ∀ d, po_Feasible y d → ∑ i, lam i * po_U E i (d i) ≤ ∑ i, lam i * po_U E i (c i)

/-- Changing a summable family at one index changes its sum by the change at that index. -/
theorem po_tsum_update {S : Type*} [DecidableEq S] (f : List S → ℝ) (hf : Summable f)
    (h : List S) (v : ℝ) : ∑' k, Function.update f h v k = ∑' k, f k + (v - f h) := by
  have : Function.update f h v = fun k => f k + if k = h then v - f h else 0 := by
    funext k
    by_cases hk : k = h
    · subst hk; simp
    · simp [hk]
  rw [this, hf.tsum_add (hasSum_ite_eq h _).summable, tsum_ite_eq]

/-- Changing a plan in `L∞₊` at one node to a nonnegative value stays in `L∞₊`. -/
theorem po_update_mem {S : Type*} [DecidableEq S] {x : List S → ℝ} (hx : x ∈ po_Lplus S)
    (h : List S) {v : ℝ} (hv : 0 ≤ v) : Function.update x h v ∈ po_Lplus S := by
  obtain ⟨hx0, B, hB⟩ := hx
  refine ⟨fun k => ?_, max B v, ?_⟩
  · by_cases hk : k = h
    · subst hk; simpa using hv
    · simpa [hk] using hx0 k
  · rintro _ ⟨k, rfl⟩
    by_cases hk : k = h
    · subst hk; simp
    · simp only [Function.update_apply, hk, ↓reduceIte]
      exact le_max_of_le_left (hB ⟨k, rfl⟩)

/-- Miao, (13.1): changing consumption at one node `h` from `x(h)` to `v` changes `Uⁱ` by
`βᵗ Pr(h) (uⁱ(v) − uⁱ(x(h)))`. -/
theorem po_U_update {ι S : Type*} [Fintype S] [DecidableEq S] (E : POEconomy ι S) (i : ι)
    {x : List S → ℝ} (hx : x ∈ po_Lplus S) (h : List S) (v : ℝ) :
    po_U E i (Function.update x h v) = po_U E i x + po_w E h * (E.u i v - E.u i (x h)) := by
  unfold po_U
  have : (fun k => po_w E k * E.u i (Function.update x h v k)) =
      Function.update (fun k => po_w E k * E.u i (x k)) h (po_w E h * E.u i v) := by
    funext k
    by_cases hk : k = h
    · subst hk; simp
    · simp [hk]
  rw [this, po_tsum_update _ (eq_13_1 E i hx)]
  ring

/-- The allocation obtained from `c` by moving `δₖ` units to agent `k` at node `h`. -/
def po_perturb {ι S : Type*} [DecidableEq S] (c : ι → List S → ℝ) (h : List S) (δ : ι → ℝ) :
    ι → List S → ℝ :=
  fun k => Function.update (c k) h (c k h + δ k)

/-- Miao, (13.2): a transfer `δ` at one node with `Σₖ δₖ = 0` that keeps consumption
nonnegative preserves feasibility. -/
theorem po_perturb_feasible {ι S : Type*} [Fintype ι] [DecidableEq S]
    {y c : ι → List S → ℝ} (hc : po_Feasible y c) (h : List S) (δ : ι → ℝ)
    (hδ : ∑ k, δ k = 0) (hpos : ∀ k, 0 ≤ c k h + δ k) : po_Feasible y (po_perturb c h δ) := by
  refine ⟨fun k => po_update_mem (hc.1 k) h (hpos k), fun h' => ?_⟩
  unfold po_perturb
  by_cases hh : h' = h
  · subst hh
    simp only [Function.update_self]
    rw [Finset.sum_add_distrib, hδ, add_zero, hc.2]
  · simp only [Function.update_apply, hh, ↓reduceIte]
    exact hc.2 h'

/-- `L∞₊` is convex. -/
theorem po_Lplus_comb {S : Type*} {x x' : List S → ℝ} (hx : x ∈ po_Lplus S)
    (hx' : x' ∈ po_Lplus S) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (fun h => a * x h + b * x' h) ∈ po_Lplus S := by
  obtain ⟨hx0, B, hB⟩ := hx
  obtain ⟨hx0', B', hB'⟩ := hx'
  refine ⟨fun h => by have := hx0 h; have := hx0' h; positivity, a * B + b * B', ?_⟩
  rintro _ ⟨h, rfl⟩
  exact add_le_add (mul_le_mul_of_nonneg_left (hB ⟨h, rfl⟩) ha)
    (mul_le_mul_of_nonneg_left (hB' ⟨h, rfl⟩) hb)

/-- Miao, §13.2, p. 417 ("`𝒰` is convex by the concavity of utility functions"): if `uⁱ` is
concave on `[0, ∞)` then `Uⁱ` is concave on `L∞₊`. -/
theorem po_U_concave {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (E.u i)) {x x' : List S → ℝ} (hx : x ∈ po_Lplus S)
    (hx' : x' ∈ po_Lplus S) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * po_U E i x + b * po_U E i x' ≤ po_U E i (fun h => a * x h + b * x' h) := by
  unfold po_U
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((eq_13_1 E i hx).mul_left a).tsum_add ((eq_13_1 E i hx').mul_left b)]
  refine ((((eq_13_1 E i hx).mul_left a).add ((eq_13_1 E i hx').mul_left b))).tsum_le_tsum
    (fun h => ?_) (eq_13_1 E i (po_Lplus_comb hx hx' ha hb))
  have := hconc.2 (Set.mem_Ici.mpr (hx.1 h)) (Set.mem_Ici.mpr (hx'.1 h)) ha hb hab
  simp only [smul_eq_mul] at this
  nlinarith [po_w_nonneg E h]

/-- Miao, (13.1): `Uⁱ` is monotone on `L∞₊`. -/
theorem po_U_mono {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι) {x x' : List S → ℝ}
    (hx : x ∈ po_Lplus S) (hx' : x' ∈ po_Lplus S) (hle : ∀ h, x h ≤ x' h) :
    po_U E i x ≤ po_U E i x' :=
  (eq_13_1 E i hx).tsum_le_tsum (fun h => mul_le_mul_of_nonneg_left
    ((E.u_mono i).monotoneOn (Set.mem_Ici.mpr (hx.1 h)) (Set.mem_Ici.mpr (hx'.1 h)) (hle h))
    (po_w_nonneg E h)) (eq_13_1 E i hx')

/-- Miao, proof of Proposition 13.2.1, p. 417 ("if" part, first case): if `c` solves the
planner's problem with weights `λ ≥ 0`, no feasible `d` makes everyone weakly better off and an
agent with `λⁱ > 0` strictly better off. -/
theorem po_planner_improvement {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hc : po_SolvesPlanner E y lam c) {d : ι → List S → ℝ}
    (hd : po_Feasible y d) (hle : ∀ i, po_U E i (c i) ≤ po_U E i (d i))
    (hlt : ∃ i, 0 < lam i ∧ po_U E i (c i) < po_U E i (d i)) : False := by
  obtain ⟨i, hi, hlti⟩ := hlt
  have : ∑ k, lam k * po_U E k (c k) < ∑ k, lam k * po_U E k (d k) :=
    Finset.sum_lt_sum (fun k _ => mul_le_mul_of_nonneg_left (hle k) (hlam k))
      ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left hlti hi⟩
  exact absurd (hc.2 d hd) (not_le.mpr this)

/-- Miao, §13.2: a solution of the planner's problem with strictly positive weights is Pareto
optimal. -/
theorem po_pareto_of_planner_pos {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ} (hlam : ∀ i, 0 < lam i)
    (hc : po_SolvesPlanner E y lam c) : po_ParetoOptimal E y c := by
  refine ⟨hc.1, ?_⟩
  rintro ⟨d, hd, hle, i, hi⟩
  exact po_planner_improvement E (fun k => (hlam k).le) hc hd hle ⟨i, hlam i, hi⟩

/-- Miao, proof of Proposition 13.2.1, p. 418 ("We then decrease `ĉⁱ` a little but raise some
other agent `j`'s consumption"): if `d` is feasible and `Uⁱ(dⁱ) > Uⁱ(cⁱ)` for a plan `cⁱ ∈ L∞₊`,
moving a little consumption from `i` to `j ≠ i` at one node keeps `i` above `Uⁱ(cⁱ)`, raises `j`
strictly, and leaves everyone else unchanged. Uses continuity of `uⁱ`. -/
theorem po_transfer_improvement {ι S : Type*} [Fintype ι] [Fintype S]
    (E : POEconomy ι S) {y d : ι → List S → ℝ} (hd : po_Feasible y d) {i j : ι} (hij : i ≠ j)
    (hcont : ContinuousOn (E.u i) (Set.Ici 0)) {ci : List S → ℝ} (hci : ci ∈ po_Lplus S)
    (hgap : po_U E i ci < po_U E i (d i)) :
    ∃ d', po_Feasible y d' ∧ po_U E i ci ≤ po_U E i (d' i) ∧
      po_U E j (d j) < po_U E j (d' j) ∧ ∀ k, k ≠ i → k ≠ j → po_U E k (d' k) = po_U E k (d k) := by
  classical
  -- a node of positive weight where `dⁱ > 0`
  have h0mem : (fun _ : List S => (0 : ℝ)) ∈ po_Lplus S :=
    ⟨fun _ => le_rfl, 0, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  obtain ⟨h, hw, hpos⟩ : ∃ h, 0 < po_w E h ∧ 0 < d i h := by
    by_contra hne
    push Not at hne
    have heq : po_U E i (d i) = po_U E i (fun _ => 0) := by
      unfold po_U
      congr 1
      funext h
      rcases (po_w_nonneg E h).lt_or_eq with hw | hw
      · rw [le_antisymm (hne h hw) ((hd.1 i).1 h)]
      · rw [← hw, zero_mul, zero_mul]
    have := po_U_mono E i h0mem hci (fun h => hci.1 h)
    linarith
  set a := d i h
  obtain ⟨δ, hδ, hδu⟩ := Metric.continuousWithinAt_iff.mp (hcont a (Set.mem_Ici.mpr hpos.le))
    ((po_U E i (d i) - po_U E i ci) / po_w E h) (div_pos (by linarith) hw)
  set ε := min (δ / 2) a with hε
  have hε0 : 0 < ε := lt_min (by linarith) hpos
  have hεa : ε ≤ a := min_le_right _ _
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set t : ι → ℝ := fun k => (if k = j then ε else 0) - (if k = i then ε else 0) with ht
  have hti : t i = -ε := by simp [ht, hij]
  have htj : t j = ε := by simp [ht, hij.symm]
  have hto : ∀ k, k ≠ i → k ≠ j → t k = 0 := fun k hki hkj => by simp [ht, hki, hkj]
  have hsum : ∑ k, t k = 0 := by
    simp only [ht, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      sub_self]
  have hnn : ∀ k, 0 ≤ d k h + t k := by
    intro k
    by_cases hki : k = i
    · subst hki; rw [hti]; linarith
    by_cases hkj : k = j
    · subst hkj; rw [htj]; linarith [(hd.1 k).1 h]
    · rw [hto k hki hkj, add_zero]; exact (hd.1 k).1 h
  refine ⟨po_perturb d h t, po_perturb_feasible hd h t hsum hnn, ?_, ?_, ?_⟩
  · simp only [po_perturb]
    rw [po_U_update E i (hd.1 i) h, hti]
    have hdist := hδu (Set.mem_Ici.mpr (by linarith : 0 ≤ a + -ε))
      (by rw [Real.dist_eq]; rw [show a + -ε - a = -ε by ring, abs_neg, abs_of_pos hε0];
          exact hεδ)
    rw [Real.dist_eq, abs_lt] at hdist
    have h1 : po_w E h * (E.u i a - E.u i (a + -ε)) < po_U E i (d i) - po_U E i ci := by
      have := (lt_div_iff₀' hw).mp (by linarith [hdist.1] :
        E.u i a - E.u i (a + -ε) < (po_U E i (d i) - po_U E i ci) / po_w E h)
      linarith
    nlinarith
  · simp only [po_perturb]
    rw [po_U_update E j (hd.1 j) h, htj]
    have : E.u j (d j h) < E.u j (d j h + ε) :=
      E.u_mono j (Set.mem_Ici.mpr ((hd.1 j).1 h)) (Set.mem_Ici.mpr (by linarith [(hd.1 j).1 h]))
        (by linarith)
    nlinarith
  · intro k hki hkj
    simp only [po_perturb]
    rw [hto k hki hkj, add_zero, Function.update_eq_self]

/-- Miao, proof of Proposition 13.2.1, p. 417 ("only if" part): a Pareto optimal allocation solves
the planner's problem for some nonzero `λ ≥ 0`. The set `𝒰 = {U(x) − U(c) − z}` is convex and
misses the open positive orthant; a separating functional gives `λ`. -/
theorem po_planner_of_pareto {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι]
    (E : POEconomy ι S) (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i))
    {y c : ι → List S → ℝ} (hpo : po_ParetoOptimal E y c) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧ po_SolvesPlanner E y lam c := by
  classical
  set A : Set (ι → ℝ) := {v | ∃ x, po_Feasible y x ∧ ∀ i, v i ≤ po_U E i (x i) - po_U E i (c i)}
    with hA
  set Pos : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ioi 0 with hPos
  have hPosOpen : IsOpen Pos := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
  have hPosConv : Convex ℝ Pos := convex_pi fun _ _ => convex_Ioi 0
  have hAconv : Convex ℝ A := by
    rintro v ⟨x, hx, hvx⟩ v' ⟨x', hx', hvx'⟩ a b ha hb hab
    refine ⟨fun i h => a * x i h + b * x' i h,
      ⟨fun i => po_Lplus_comb (hx.1 i) (hx'.1 i) ha hb, fun h => ?_⟩, fun i => ?_⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hx'.2]
      rw [← add_mul, hab, one_mul]
    · have hcv := po_U_concave E i (hconc i) (hx.1 i) (hx'.1 i) ha hb hab
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left (hvx i) ha
      have h2 := mul_le_mul_of_nonneg_left (hvx' i) hb
      have hab' : a * po_U E i (c i) + b * po_U E i (c i) = po_U E i (c i) := by
        rw [← add_mul, hab, one_mul]
      linarith
  have hdisj : Disjoint Pos A := by
    rw [Set.disjoint_left]
    rintro v hv ⟨x, hx, hvx⟩
    apply hpo.2
    have hgt : ∀ i, po_U E i (c i) < po_U E i (x i) := fun i => by
      have := hv i (Set.mem_univ _)
      have := hvx i
      simp only [Set.mem_Ioi] at *
      linarith
    exact ⟨x, hx, fun i => (hgt i).le, Classical.arbitrary ι, hgt _⟩
  obtain ⟨f, u, hfPos, hfA⟩ := geometric_hahn_banach_open hPosConv hPosOpen hAconv hdisj
  set lam : ι → ℝ := fun i => -f (Pi.single i 1) with hlamdef
  have hf : ∀ v : ι → ℝ, f v = -∑ i, v i * lam i := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    simp only [hlamdef, mul_neg, Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Pi.single i (v i) = v i • (Pi.single i 1 : ι → ℝ) by
      ext k; by_cases hk : k = i <;> simp [hk], map_smul, smul_eq_mul]
  have h0A : (0 : ι → ℝ) ∈ A := ⟨c, hpo.1, fun i => by simp⟩
  have hu0 : u ≤ 0 := by simpa using hfA 0 h0A
  have hone : (fun _ => (1 : ℝ)) ∈ Pos := fun _ _ => Set.mem_Ioi.mpr one_pos
  have hf1 : f (fun _ => 1) < u := hfPos _ hone
  have hu : 0 ≤ u := by
    by_contra hneg
    push Not at hneg
    have hf1neg : f (fun _ => 1) < 0 := lt_of_lt_of_le hf1 hu0
    set s := u / f (fun _ => 1) / 2
    have hs : 0 < s := by
      have : 0 < u / f (fun _ => 1) := div_pos_of_neg_of_neg hneg hf1neg
      positivity
    have hmem : (fun _ => s) ∈ Pos := fun _ _ => Set.mem_Ioi.mpr hs
    have h2 := hfPos _ hmem
    have : f (fun _ => s) = s * f (fun _ => 1) := by
      rw [show (fun _ : ι => s) = s • (fun _ : ι => (1 : ℝ)) by funext; simp, map_smul,
        smul_eq_mul]
    rw [this] at h2
    have : s * f (fun _ => 1) = u / 2 := by
      have hne : f (fun _ => 1) ≠ 0 := hf1neg.ne
      simp only [s]
      field_simp
    linarith
  refine ⟨lam, fun i => ?_, ?_, hpo.1, fun x hx => ?_⟩
  · have hmem : (-(Pi.single i 1 : ι → ℝ)) ∈ A := ⟨c, hpo.1, fun k => by
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]⟩
    have := hfA _ hmem
    rw [map_neg] at this
    simp only [hlamdef]
    linarith
  · intro hz
    have := hf (fun _ => 1)
    rw [hz] at this
    simp at this
    linarith
  · have hmem : (fun i => po_U E i (x i) - po_U E i (c i)) ∈ A := ⟨x, hx, fun _ => le_rfl⟩
    have h1 := hfA _ hmem
    rw [hf] at h1
    have h2 : ∑ i, (po_U E i (x i) - po_U E i (c i)) * lam i ≤ 0 := by linarith
    simp only [sub_mul, Finset.sum_sub_distrib] at h2
    simp only [mul_comm (lam _)]
    linarith

/-- **Proposition 13.2.1** (Miao, p. 417). An allocation is Pareto optimal iff it solves the
social planner's problem for some nonzero weight `λ ∈ ℝᴵ₊`. Hypotheses (from Assumption 13.1.1):
each `uⁱ` is concave and continuous on `[0, ∞)`; there is at least one agent. -/
theorem proposition_13_2_1 {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι]
    (E : POEconomy ι S) (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i))
    (hcont : ∀ i, ContinuousOn (E.u i) (Set.Ici 0)) (y c : ι → List S → ℝ) :
    po_ParetoOptimal E y c ↔
      ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧ po_SolvesPlanner E y lam c := by
  classical
  refine ⟨po_planner_of_pareto E hconc, ?_⟩
  rintro ⟨lam, hlam, hne, hc⟩
  refine ⟨hc.1, ?_⟩
  rintro ⟨d, hd, hle, i, hi⟩
  by_cases hli : 0 < lam i
  · exact po_planner_improvement E hlam hc hd hle ⟨i, hli, hi⟩
  have hli0 : lam i = 0 := le_antisymm (not_lt.mp hli) (hlam i)
  obtain ⟨j, hj⟩ : ∃ j, lam j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hjpos : 0 < lam j := lt_of_le_of_ne (hlam j) (Ne.symm hj)
  have hij : i ≠ j := fun h => hj (h ▸ hli0)
  obtain ⟨d', hd', hi', hj', hk'⟩ := po_transfer_improvement E hd hij (hcont i) (hc.1.1 i) hi
  refine po_planner_improvement E hlam hc hd' (fun k => ?_) ⟨j, hjpos, ?_⟩
  · by_cases hki : k = i
    · subst hki; exact hi'
    by_cases hkj : k = j
    · subst hkj; exact (hle k).trans hj'.le
    · rw [hk' k hki hkj]; exact hle k
  · exact (hle j).trans_lt hj'

/-- Miao, §13.2, p. 418 ("Using first-order conditions"): at a solution of the planner's
problem, for two agents `i ≠ j` with interior consumption at node `h`,
`βᵗ Pr(h) (λⁱ uⁱ'(cⁱ(h)) − λʲ uʲ'(cʲ(h))) = 0`. Derived by transferring `ε` units from `j` to
`i` at `h`: the planner's objective is maximal at `ε = 0`. -/
theorem po_planner_foc {ι S : Type*} [Fintype ι] [Fintype S]
    (E : POEconomy ι S) {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ}
    (hc : po_SolvesPlanner E y lam c) {i j : ι} (hij : i ≠ j) (h : List S)
    (hi : 0 < c i h) (hj : 0 < c j h) (hdi : DifferentiableAt ℝ (E.u i) (c i h))
    (hdj : DifferentiableAt ℝ (E.u j) (c j h)) :
    po_w E h * (lam i * deriv (E.u i) (c i h) - lam j * deriv (E.u j) (c j h)) = 0 := by
  classical
  rcases (po_w_nonneg E h).lt_or_eq with hw | hw
  swap
  · rw [← hw, zero_mul]
  set φ : ℝ → ℝ := fun e => lam i * E.u i (c i h + e) + lam j * E.u j (c j h - e) with hφ
  have hmax : IsLocalMax φ 0 := by
    have hnhds : Set.Ioo (-min (c i h) (c j h)) (min (c i h) (c j h)) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by simp [hi, hj]) (lt_min hi hj)
    filter_upwards [hnhds] with e he
    obtain ⟨he1, he2⟩ := he
    have hmi := min_le_left (c i h) (c j h)
    have hmj := min_le_right (c i h) (c j h)
    set t : ι → ℝ := fun k => (if k = i then e else 0) - (if k = j then e else 0) with ht
    have hti : t i = e := by simp [ht, hij]
    have htj : t j = -e := by simp [ht, hij.symm]
    have hto : ∀ k, k ≠ i ∧ k ≠ j → t k = 0 := fun k hk => by simp [ht, hk.1, hk.2]
    have hsum : ∑ k, t k = 0 := by
      simp only [ht, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        sub_self]
    have hnn : ∀ k, 0 ≤ c k h + t k := by
      intro k
      by_cases hki : k = i
      · subst hki; rw [hti]; linarith
      by_cases hkj : k = j
      · subst hkj; rw [htj]; linarith
      · rw [hto k ⟨hki, hkj⟩, add_zero]; exact (hc.1.1 k).1 h
    have hopt := hc.2 _ (po_perturb_feasible hc.1 h t hsum hnn)
    simp only [po_perturb] at hopt
    simp only [po_U_update E _ (hc.1.1 _) h, mul_add, Finset.sum_add_distrib] at hopt
    have hcol : ∑ k, lam k * (po_w E h * (E.u k (c k h + t k) - E.u k (c k h))) =
        po_w E h * (φ e - φ 0) := by
      rw [Fintype.sum_eq_add i j hij (fun k hk => by rw [hto k hk, add_zero, sub_self,
        mul_zero, mul_zero]), hti, htj]
      simp only [hφ, add_zero, sub_zero, ← sub_eq_add_neg]
      ring
    rw [hcol] at hopt
    have : po_w E h * (φ e - φ 0) ≤ 0 := by linarith
    have := nonpos_of_mul_nonpos_right this hw
    linarith
  have hderiv : HasDerivAt φ (lam i * deriv (E.u i) (c i h) - lam j * deriv (E.u j) (c j h)) 0 := by
    have h1 : HasDerivAt (fun e => E.u i (c i h + e)) (deriv (E.u i) (c i h)) 0 := by
      exact HasDerivAt.comp_const_add (c i h) 0 (by simpa using hdi.hasDerivAt)
    have h2 : HasDerivAt (fun e => E.u j (c j h - e)) (-deriv (E.u j) (c j h)) 0 := by
      exact HasDerivAt.comp_const_sub (c j h) 0 (by simpa using hdj.hasDerivAt)
    have := (h1.const_mul (lam i)).add (h2.const_mul (lam j))
    convert this using 1
    ring
  rw [hmax.hasDerivAt_eq_zero hderiv, mul_zero]

/-- Miao, §13.2, p. 418: the first-order condition `uⁱ'(cⁱ_t) / uʲ'(cʲ_t) = λʲ / λⁱ` at a node of
positive probability, in multiplied-out form `λⁱ uⁱ'(cⁱ_t) = λʲ uʲ'(cʲ_t)` (all agents,
interior consumption). -/
theorem po_planner_foc_ratio {ι S : Type*} [Fintype ι] [Fintype S]
    (E : POEconomy ι S) {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ}
    (hc : po_SolvesPlanner E y lam c) (h : List S) (hw : 0 < po_w E h)
    (hpos : ∀ k, 0 < c k h) (hdiff : ∀ k, DifferentiableAt ℝ (E.u k) (c k h)) (i j : ι) :
    lam i * deriv (E.u i) (c i h) = lam j * deriv (E.u j) (c j h) := by
  by_cases hij : i = j
  · rw [hij]
  have := po_planner_foc E hc hij h (hpos i) (hpos j) (hdiff i) (hdiff j)
  have := (mul_eq_zero.mp this).resolve_left hw.ne'
  linarith

/-- Miao, (13.3), p. 418: `cⁱ_t(sᵗ) = (uⁱ')⁻¹(λᵢ⁻¹ λ₁ u¹'(c¹_t(sᵗ)))`, with `(uⁱ')⁻¹` the inverse
of the marginal utility on `(0, ∞)` (which exists when `uⁱ'` is injective there, e.g. under
Assumption 13.1.1 by `po_strictAntiOn_deriv`). Also the equivalent
`uⁱ'(cⁱ_t) = λᵢ⁻¹ λ₁ u¹'(c¹_t)`. -/
theorem eq_13_3 {ι S : Type*} [Fintype ι] [Fintype S]
    (E : POEconomy ι S) {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ}
    (hc : po_SolvesPlanner E y lam c) (hlam : ∀ i, 0 < lam i) (h : List S) (hw : 0 < po_w E h)
    (hpos : ∀ k, 0 < c k h) (hdiff : ∀ k, DifferentiableAt ℝ (E.u k) (c k h))
    (hinj : ∀ k, Set.InjOn (deriv (E.u k)) (Set.Ioi 0)) (i i₁ : ι) :
    deriv (E.u i) (c i h) = (lam i)⁻¹ * lam i₁ * deriv (E.u i₁) (c i₁ h) ∧
      c i h = Function.invFunOn (deriv (E.u i)) (Set.Ioi 0)
        ((lam i)⁻¹ * lam i₁ * deriv (E.u i₁) (c i₁ h)) := by
  have hfoc := po_planner_foc_ratio E hc h hw hpos hdiff i i₁
  have h1 : deriv (E.u i) (c i h) = (lam i)⁻¹ * lam i₁ * deriv (E.u i₁) (c i₁ h) := by
    rw [mul_assoc, ← hfoc, ← mul_assoc, inv_mul_cancel₀ (hlam i).ne', one_mul]
  refine ⟨h1, ?_⟩
  have hex : ∃ a ∈ Set.Ioi (0 : ℝ), deriv (E.u i) a =
      (lam i)⁻¹ * lam i₁ * deriv (E.u i₁) (c i₁ h) := ⟨c i h, hpos i, h1⟩
  exact hinj i (hpos i) (Function.invFunOn_mem hex) (h1.trans (Function.invFunOn_eq hex).symm)

/-- Miao, (13.4), p. 418: substituting (13.3) into (13.2),
`Σᵢ (uⁱ')⁻¹(λᵢ⁻¹ λ₁ u¹'(c¹_t(sᵗ))) = Σᵢ yⁱ_t(sᵗ)`, one equation in `c¹_t(sᵗ)`. -/
theorem eq_13_4 {ι S : Type*} [Fintype ι] [Fintype S]
    (E : POEconomy ι S) {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ}
    (hc : po_SolvesPlanner E y lam c) (hlam : ∀ i, 0 < lam i) (h : List S) (hw : 0 < po_w E h)
    (hpos : ∀ k, 0 < c k h) (hdiff : ∀ k, DifferentiableAt ℝ (E.u k) (c k h))
    (hinj : ∀ k, Set.InjOn (deriv (E.u k)) (Set.Ioi 0)) (i₁ : ι) :
    ∑ i, Function.invFunOn (deriv (E.u i)) (Set.Ioi 0)
        ((lam i)⁻¹ * lam i₁ * deriv (E.u i₁) (c i₁ h)) = ∑ i, y i h := by
  rw [← hc.1.2 h]
  exact Finset.sum_congr rfl fun i _ =>
    (eq_13_3 E hc hlam h hw hpos hdiff hinj i i₁).2.symm

/-- Miao, Assumption 13.1.1: the felicity function is differentiable at every positive
consumption level. -/
theorem po_differentiableAt {u : ℝ → ℝ} (hu : Assumption13_1_1 u) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ u x :=
  ((hu.2.2.1.differentiableOn (by norm_num)) x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)

/-- Miao, Assumption 13.1.1: marginal utility is strictly decreasing on `(0, ∞)`, so `uⁱ'` is
invertible there, as (13.3) requires. -/
theorem po_strictAntiOn_deriv {u : ℝ → ℝ} (hu : Assumption13_1_1 u) :
    StrictAntiOn (deriv u) (Set.Ioi 0) :=
  (hu.2.2.2.1.subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    fun _ hx => po_differentiableAt hu hx

/-- Miao, §13.2, p. 418 ("It shows that `c¹_t(sᵗ)` is a function of the aggregate endowment
only. As a result … any agent's consumption is also a function of the aggregate endowment
only"): if the planner's first-order conditions hold with positive weights at all nodes of
positive probability and marginal utilities are strictly decreasing, two such nodes with the
same aggregate endowment give every agent the same consumption. -/
theorem po_risk_sharing {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y c : ι → List S → ℝ} {lam : ι → ℝ} (hc : po_Feasible y c) (hlam : ∀ i, 0 < lam i)
    (hanti : ∀ i, StrictAntiOn (deriv (E.u i)) (Set.Ioi 0)) (hpos : ∀ i h, 0 < c i h)
    (hfoc : ∀ h, 0 < po_w E h → ∀ i j, lam i * deriv (E.u i) (c i h) =
      lam j * deriv (E.u j) (c j h))
    {h h' : List S} (hw : 0 < po_w E h) (hw' : 0 < po_w E h')
    (hy : ∑ i, y i h = ∑ i, y i h') (i : ι) : c i h = c i h' := by
  have key : ∀ g g', 0 < po_w E g → 0 < po_w E g' → c i g < c i g' →
      ∑ k, c k g < ∑ k, c k g' := by
    intro g g' hg hg' hlt
    have hd : deriv (E.u i) (c i g') < deriv (E.u i) (c i g) :=
      hanti i (hpos i g) (hpos i g') hlt
    refine Finset.sum_lt_sum (fun k _ => ?_) ⟨i, Finset.mem_univ _, hlt⟩
    have hk : deriv (E.u k) (c k g') < deriv (E.u k) (c k g) := by
      have e1 := hfoc g hg k i
      have e2 := hfoc g' hg' k i
      have : lam k * deriv (E.u k) (c k g') < lam k * deriv (E.u k) (c k g) := by
        rw [e1, e2]; exact mul_lt_mul_of_pos_left hd (hlam i)
      exact lt_of_mul_lt_mul_left this (hlam k).le
    refine le_of_lt (lt_of_not_ge fun hge => ?_)
    rcases hge.lt_or_eq with hlt' | heq
    · exact absurd (hanti k (hpos k g') (hpos k g) hlt') (not_lt.mpr hk.le)
    · rw [heq] at hk; exact lt_irrefl _ hk
  rcases lt_trichotomy (c i h) (c i h') with hlt | heq | hgt
  · have := key h h' hw hw' hlt
    rw [hc.2, hc.2, hy] at this
    exact absurd this (lt_irrefl _)
  · exact heq
  · have := key h' h hw' hw hgt
    rw [hc.2, hc.2, hy] at this
    exact absurd this (lt_irrefl _)

/-- Miao, §13.2, p. 418: under the hypotheses of `po_risk_sharing`, each agent's consumption is a
function `gᵢ` of the aggregate endowment `ȳ_t(sᵗ)` at the nodes of positive probability. -/
theorem po_consumption_fn_aggregate {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y c : ι → List S → ℝ} {lam : ι → ℝ} (hc : po_Feasible y c) (hlam : ∀ i, 0 < lam i)
    (hanti : ∀ i, StrictAntiOn (deriv (E.u i)) (Set.Ioi 0)) (hpos : ∀ i h, 0 < c i h)
    (hfoc : ∀ h, 0 < po_w E h → ∀ i j, lam i * deriv (E.u i) (c i h) =
      lam j * deriv (E.u j) (c j h)) :
    ∃ g : ι → ℝ → ℝ, ∀ i h, 0 < po_w E h → c i h = g i (∑ k, y k h) := by
  classical
  refine ⟨fun i a => if hx : ∃ h, 0 < po_w E h ∧ ∑ k, y k h = a then c i hx.choose else 0,
    fun i h hw => ?_⟩
  have hx : ∃ h', 0 < po_w E h' ∧ ∑ k, y k h' = ∑ k, y k h := ⟨h, hw, rfl⟩
  simp only [hx, ↓reduceDIte]
  exact po_risk_sharing E hc hlam hanti hpos hfoc hw hx.choose_spec.1 hx.choose_spec.2.symm i

/-- Miao, §13.2, p. 418 ("If the aggregate endowment is determined by an aggregate Markov state
variable, then individual consumption is a function of the state only. There is no history
dependence"): if `ȳ_t(sᵗ) = Y(z(sᵗ))` for a state `z(sᵗ)`, then `cⁱ_t(sᵗ) = Gᵢ(z(sᵗ))`. -/
theorem po_no_history_dependence {ι S Z : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y c : ι → List S → ℝ} {lam : ι → ℝ} (hc : po_Feasible y c) (hlam : ∀ i, 0 < lam i)
    (hanti : ∀ i, StrictAntiOn (deriv (E.u i)) (Set.Ioi 0)) (hpos : ∀ i h, 0 < c i h)
    (hfoc : ∀ h, 0 < po_w E h → ∀ i j, lam i * deriv (E.u i) (c i h) =
      lam j * deriv (E.u j) (c j h))
    (z : List S → Z) (Y : Z → ℝ) (hY : ∀ h, ∑ k, y k h = Y (z h)) :
    ∃ G : ι → Z → ℝ, ∀ i h, 0 < po_w E h → c i h = G i (z h) := by
  obtain ⟨g, hg⟩ := po_consumption_fn_aggregate E hc hlam hanti hpos hfoc
  exact ⟨fun i s => g i (Y s), fun i h hw => by rw [hg i h hw, hY]⟩

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Time 0 trading

Miao, §13.3, pp. 418–424: Arrow–Debreu state prices, equilibrium, first-order conditions, risk
sharing, the Negishi method, the two welfare theorems and asset pricing.

* `po_cost q x = Σ_{t, sᵗ} q⁰_t(sᵗ) x_t(sᵗ)`; it is well defined for `q ∈ L¹`, `x ∈ L∞`
  (`eq_13_5`). `po_ADEquilibrium E y q c` is Definition 13.3.1.
* (13.6) (`eq_13_6`) is derived by moving consumption between a node and the root along the
  budget line; the multiplier is `μᵢ = uⁱ'(cⁱ₀(s₀))` under `q⁰₀(s₀) = 1`. (13.7)–(13.10)
  (`eq_13_7`–`eq_13_10`) follow. The equilibrium allocation solves the planner's problem with
  `λᵢ = μᵢ⁻¹` (`po_AD_solves_planner`), and the planner's shadow prices are `q⁰`
  (`po_AD_shadow_price`). The text omits that these need interior consumption,
  differentiability, and (for (13.8)–(13.10)) nodes of positive probability.
* Example 13.3.1 (`example_13_3_1`, `example_13_3_1_shares`, marginal utility `po_crra_hasDerivAt`).
  The printed `c^{1−γ}/(1−γ)` needs `γ ≠ 1`; the computation uses only `u'(c) = c^{−γ}`, which
  covers `γ = 1` (log utility) as well.
* The Negishi algorithm: scale invariance (`po_negishi_scale`), `q⁰₀(s₀) = 1` iff
  `μ₁ = u¹'(c¹₀(s₀))` (`po_negishi_q0`), the direction of step 3 (`po_negishi_step3`) and the
  fact that a stopping point is an equilibrium (`po_negishi_fixed_point`). Convergence of the
  iteration (step 4) is not claimed by the text and not formalised.
* **Theorem 13.3.1** (`theorem_13_3_1`): First Welfare Theorem, under strict monotonicity only.
* **Theorem 13.3.2** (`theorem_13_3_2`): Second Welfare Theorem. Correction: as printed (with the
  economy's endowments) it is false (`theorem_13_3_2_counterexample`); it holds with the
  endowments relocated to the allocation (equivalently, after lump-sum transfers). The proof here
  is not the book's Hahn–Banach/Yosida–Hewitt outline: under differentiability and uniformly
  interior consumption, the planner's first-order conditions give the prices directly, and they
  lie in `L¹`. Strict concavity is not needed.
* Asset pricing: `po_assetPrice` (pp. 423–424), well defined for `q ∈ L¹` and `d ∈ L∞`
  (`po_assetPrice_summable`), at the root (`po_assetPrice_root`) and with (13.7) substituted
  (`po_assetPrice_eq`).
-/

namespace Miao.CompleteMarkets

open Filter Topology

/-- Miao, (13.5), p. 419: the value `Σ_t Σ_{sᵗ} q⁰_t(sᵗ) x_t(sᵗ)` of a plan `x` at the
Arrow–Debreu state prices `q⁰`. -/
noncomputable def po_cost {S : Type*} (q x : List S → ℝ) : ℝ :=
  ∑' h, q h * x h

/-- Miao, (13.5), p. 419 ("For this budget constraint to be well-defined, we need `q⁰` to be in
`L¹`"): for `q ∈ L¹` and `x ∈ L∞` the series `Σ q⁰_t(sᵗ) x_t(sᵗ)` converges absolutely. -/
theorem eq_13_5 {S : Type*} {q x : List S → ℝ} (hq : q ∈ po_L1 S) (hx : x ∈ po_Linfty S) :
    Summable fun h => q h * x h := by
  obtain ⟨B, hB⟩ := hx
  refine Summable.of_norm_bounded ((show Summable fun h => |q h| from hq).mul_right B)
    fun h => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hB ⟨h, rfl⟩) (abs_nonneg _)

/-- **Definition 13.3.1** (Miao, p. 419). An Arrow–Debreu equilibrium: state prices `q⁰ ∈ L¹`
and a feasible allocation `c ∈ (L∞₊)ᴵ` such that each `cⁱ` maximises `Uⁱ` over the plans in
`L∞₊` satisfying the budget constraint (13.5) at the endowment `yⁱ`. -/
def po_ADEquilibrium {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (y : ι → List S → ℝ) (q : List S → ℝ) (c : ι → List S → ℝ) : Prop :=
  q ∈ po_L1 S ∧ po_Feasible y c ∧ ∀ i, po_cost q (c i) ≤ po_cost q (y i) ∧
    ∀ x ∈ po_Lplus S, po_cost q x ≤ po_cost q (y i) → po_U E i x ≤ po_U E i (c i)

/-- Miao, (13.5): changing a plan at one node changes its value by the price times the change. -/
theorem po_cost_update {S : Type*} [DecidableEq S] {q x : List S → ℝ} (hq : q ∈ po_L1 S)
    (hx : x ∈ po_Linfty S) (h : List S) (v : ℝ) :
    po_cost q (Function.update x h v) = po_cost q x + q h * (v - x h) := by
  unfold po_cost
  have : (fun k => q k * Function.update x h v k) =
      Function.update (fun k => q k * x k) h (q h * v) := by
    funext k
    by_cases hk : k = h
    · subst hk; simp
    · simp [hk]
  rw [this, po_tsum_update _ (eq_13_5 hq hx)]
  ring

/-- Miao, (13.5) and (13.2): the values of the agents' plans add up to the value of the sum. -/
theorem po_sum_cost {ι S : Type*} [Fintype ι] {q : List S → ℝ} (hq : q ∈ po_L1 S)
    {x : ι → List S → ℝ} (hx : ∀ i, x i ∈ po_Linfty S) :
    ∑ i, po_cost q (x i) = po_cost q (fun h => ∑ i, x i h) := by
  unfold po_cost
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum fun i _ => eq_13_5 hq (hx i)]

/-- The tangent-line inequality for a concave felicity function:
`u(x) ≤ u(c) + u'(c)(x − c)` for `c > 0`, `x ≥ 0`. -/
theorem po_tangent {u : ℝ → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) u) {c x : ℝ} (hc : 0 < c)
    (hx : 0 ≤ x) (hd : DifferentiableAt ℝ u c) : u x ≤ u c + deriv u c * (x - c) := by
  rcases lt_trichotomy x c with hlt | heq | hgt
  · have := hconc.deriv_le_slope (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hc.le) hlt hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith
  · subst heq; simp
  · have := hconc.slope_le_deriv (Set.mem_Ici.mpr hc.le) (Set.mem_Ici.mpr hx) hgt hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    nlinarith

/-- Miao, §13.3: a concave felicity function, strictly increasing on `[0, ∞)`, has positive
marginal utility at every positive consumption level where it is differentiable. -/
theorem po_deriv_pos {u : ℝ → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) u)
    (hmono : StrictMonoOn u (Set.Ici 0)) {x : ℝ} (hx : 0 < x) (hd : DifferentiableAt ℝ u x) :
    0 < deriv u x := by
  have h1 := po_tangent hconc hx (by linarith : (0 : ℝ) ≤ x + 1) hd
  have h2 : u x < u (x + 1) :=
    hmono (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr (by linarith)) (by linarith)
  nlinarith

/-- Miao, §13.3, the sufficiency of the first-order conditions: if `uⁱ` is concave, `cⁱ` is
interior, and `βᵗ Pr(sᵗ) uⁱ'(cⁱ_t(sᵗ)) = μ q⁰_t(sᵗ)` at every node (13.6), then for every
`x ∈ L∞₊`, `Uⁱ(x) − Uⁱ(cⁱ) ≤ μ (q⁰ · x − q⁰ · cⁱ)`. -/
theorem po_utility_gain_le {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (E.u i)) {c : List S → ℝ} (hc : c ∈ po_Lplus S)
    (hpos : ∀ h, 0 < c h) (hdiff : ∀ h, DifferentiableAt ℝ (E.u i) (c h)) {q : List S → ℝ}
    (hq : q ∈ po_L1 S) (μ : ℝ) (hfoc : ∀ h, po_w E h * deriv (E.u i) (c h) = μ * q h)
    {x : List S → ℝ} (hx : x ∈ po_Lplus S) :
    po_U E i x - po_U E i c ≤ μ * (po_cost q x - po_cost q c) := by
  unfold po_U po_cost
  have hsx := eq_13_5 hq (po_Lplus_subset_Linfty hx)
  have hsc := eq_13_5 hq (po_Lplus_subset_Linfty hc)
  rw [← (eq_13_1 E i hx).tsum_sub (eq_13_1 E i hc), ← hsx.tsum_sub hsc, ← tsum_mul_left]
  refine ((eq_13_1 E i hx).sub (eq_13_1 E i hc)).tsum_le_tsum (fun h => ?_)
    ((hsx.sub hsc).mul_left μ)
  have ht := po_tangent hconc (hpos h) (hx.1 h) (hdiff h)
  have hw := po_w_nonneg E h
  have : po_w E h * E.u i (x h) ≤ po_w E h * (E.u i (c h) + deriv (E.u i) (c h) * (x h - c h)) :=
    mul_le_mul_of_nonneg_left ht hw
  have e : po_w E h * (deriv (E.u i) (c h) * (x h - c h)) = μ * (q h * x h - q h * c h) := by
    rw [← mul_assoc, hfoc h]; ring
  nlinarith

/-- Miao, §13.3: an interior plan satisfying (13.6) with `μ ≥ 0` and an exactly binding budget
constraint maximises `Uⁱ` over the budget set (the first-order conditions are sufficient). -/
theorem po_optimal_of_foc {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (E.u i)) {c y : List S → ℝ} (hc : c ∈ po_Lplus S)
    (hpos : ∀ h, 0 < c h) (hdiff : ∀ h, DifferentiableAt ℝ (E.u i) (c h)) {q : List S → ℝ}
    (hq : q ∈ po_L1 S) {μ : ℝ} (hμ : 0 ≤ μ)
    (hfoc : ∀ h, po_w E h * deriv (E.u i) (c h) = μ * q h) (hbud : po_cost q c = po_cost q y)
    {x : List S → ℝ} (hx : x ∈ po_Lplus S) (hxb : po_cost q x ≤ po_cost q y) :
    po_U E i x ≤ po_U E i c := by
  have := po_utility_gain_le E i hconc hc hpos hdiff hq μ hfoc hx
  have : μ * (po_cost q x - po_cost q c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hμ (by linarith)
  linarith

/-- Miao, (13.6), p. 419. At an Arrow–Debreu equilibrium with `q⁰₀(s₀) = 1`, if agent `i`'s
consumption is interior and `uⁱ` is differentiable there, then
`βᵗ uⁱ'(cⁱ_t(sᵗ)) Pr(sᵗ) = μᵢ q⁰_t(sᵗ)` at every node, with `μᵢ = uⁱ'(cⁱ₀(s₀))` (the text's "by
normalization"). Derived by buying `ε` more units at `sᵗ` and `ε q⁰_t(sᵗ)` fewer at `s₀`, which
leaves the budget unchanged; utility is maximal at `ε = 0`. -/
theorem eq_13_6 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (i : ι) (hpos : ∀ h, 0 < c i h)
    (hdiff : ∀ h, DifferentiableAt ℝ (E.u i) (c i h)) (h : List S) :
    po_w E h * deriv (E.u i) (c i h) = deriv (E.u i) (c i []) * q h := by
  classical
  by_cases hh : h = []
  · subst hh; rw [po_w_root, hq0]; ring
  obtain ⟨hq, hfeas, hopt⟩ := hE
  set a := c i h
  set b := c i []
  set φ : ℝ → ℝ := fun e => po_w E h * E.u i (a + e) + E.u i (b - e * q h) with hφ
  have hci := hfeas.1 i
  have hmax : IsLocalMax φ 0 := by
    have hr : 0 < min a (b / (|q h| + 1)) := lt_min (hpos h) (by
      have := hpos []; positivity)
    filter_upwards [Ioo_mem_nhds (neg_neg_iff_pos.mpr hr) hr] with e he
    obtain ⟨he1, he2⟩ := he
    have hea : |e| < a := (abs_lt.mpr ⟨he1, he2⟩).trans_le (min_le_left _ _)
    have heb : |e| < b / (|q h| + 1) := (abs_lt.mpr ⟨he1, he2⟩).trans_le (min_le_right _ _)
    have hnn1 : 0 ≤ a + e := by linarith [neg_abs_le e]
    have hnn2 : 0 ≤ b - e * q h := by
      have h1 : |e * q h| ≤ |e| * (|q h| + 1) := by
        rw [abs_mul]; nlinarith [abs_nonneg e, abs_nonneg (q h)]
      have h2 : |e| * (|q h| + 1) < b := (lt_div_iff₀ (by positivity)).mp heb
      linarith [le_abs_self (e * q h)]
    set x1 := Function.update (c i) h (a + e)
    have hx1 : x1 ∈ po_Lplus S := po_update_mem hci h hnn1
    set x2 := Function.update x1 [] (b - e * q h)
    have hx2 : x2 ∈ po_Lplus S := po_update_mem hx1 [] hnn2
    have hx1r : x1 [] = b := by simp [x1, Ne.symm hh, b]
    have hcost : po_cost q x2 = po_cost q (c i) := by
      simp only [x2, x1]
      rw [po_cost_update hq (po_Lplus_subset_Linfty hx1), hx1r,
        po_cost_update hq (po_Lplus_subset_Linfty hci), hq0]
      ring
    have hU := (hopt i).2 x2 hx2 (hcost ▸ (hopt i).1)
    simp only [x2] at hU
    rw [po_U_update E i hx1, hx1r, po_U_update E i hci, po_w_root] at hU
    simp only [hφ, add_zero, zero_mul, sub_zero]
    linarith
  have hderiv : HasDerivAt φ (po_w E h * deriv (E.u i) a - q h * deriv (E.u i) b) 0 := by
    have h1 : HasDerivAt (fun e => E.u i (a + e)) (deriv (E.u i) a) 0 :=
      HasDerivAt.comp_const_add a 0 (by simpa using (hdiff h).hasDerivAt)
    have hl : HasDerivAt (fun e : ℝ => b - e * q h) (-q h) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (q h)).const_sub b
    have h2 : HasDerivAt (fun e => E.u i (b - e * q h)) (deriv (E.u i) b * -q h) 0 := by
      have hb : HasDerivAt (E.u i) (deriv (E.u i) b) (b - 0 * q h) := by
        simpa using (hdiff []).hasDerivAt
      exact hb.comp 0 hl
    have := (h1.const_mul (po_w E h)).add h2
    convert this using 1
    ring
  have := hmax.hasDerivAt_eq_zero hderiv
  linarith

/-- Miao, (13.7), p. 419: the Arrow–Debreu state price
`q⁰_t(sᵗ) = βᵗ uⁱ'(cⁱ_t(sᵗ)) Pr(sᵗ) / uⁱ'(cⁱ₀(s₀))`. -/
theorem eq_13_7 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (i : ι) (hpos : ∀ h, 0 < c i h)
    (hdiff : ∀ h, DifferentiableAt ℝ (E.u i) (c i h)) (hμ : deriv (E.u i) (c i []) ≠ 0)
    (h : List S) :
    q h = E.β ^ h.length * deriv (E.u i) (c i h) * E.P.pr h / deriv (E.u i) (c i []) := by
  have := eq_13_6 E hE hq0 i hpos hdiff h
  unfold po_w at this
  field_simp
  linarith

/-- Miao, (13.8), p. 419: at a node of positive probability,
`uⁱ'(cⁱ_t(sᵗ)) μⱼ = uʲ'(cʲ_t(sᵗ)) μᵢ`, i.e. `uⁱ'(cⁱ_t) / uʲ'(cʲ_t) = μᵢ / μⱼ`, with
`μᵢ = uⁱ'(cⁱ₀(s₀))`. -/
theorem eq_13_8 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) {h : List S} (hw : 0 < po_w E h)
    (i j : ι) :
    deriv (E.u i) (c i h) * deriv (E.u j) (c j []) =
        deriv (E.u j) (c j h) * deriv (E.u i) (c i []) ∧
      (deriv (E.u j) (c j h) ≠ 0 → deriv (E.u j) (c j []) ≠ 0 →
        deriv (E.u i) (c i h) / deriv (E.u j) (c j h) =
          deriv (E.u i) (c i []) / deriv (E.u j) (c j [])) := by
  have hi := eq_13_6 E hE hq0 i (hpos i) (hdiff i) h
  have hj := eq_13_6 E hE hq0 j (hpos j) (hdiff j) h
  have key : deriv (E.u i) (c i h) * deriv (E.u j) (c j []) =
      deriv (E.u j) (c j h) * deriv (E.u i) (c i []) := by
    have : po_w E h * (deriv (E.u i) (c i h) * deriv (E.u j) (c j [])) =
        po_w E h * (deriv (E.u j) (c j h) * deriv (E.u i) (c i [])) := by
      rw [← mul_assoc, hi, ← mul_assoc, hj]; ring
    exact mul_left_cancel₀ hw.ne' this
  refine ⟨key, fun h1 h2 => ?_⟩
  rw [div_eq_div_iff h1 h2]
  linarith

/-- Miao, (13.9), p. 419: `cⁱ_t(sᵗ) = (uⁱ')⁻¹(u¹'(c¹_t(sᵗ)) μᵢ / μ₁)` at nodes of positive
probability, `(uⁱ')⁻¹` the inverse of the marginal utility on `(0, ∞)`. -/
theorem eq_13_9 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h))
    (hinj : ∀ k, Set.InjOn (deriv (E.u k)) (Set.Ioi 0)) {h : List S} (hw : 0 < po_w E h)
    (i i₁ : ι) (hμ₁ : deriv (E.u i₁) (c i₁ []) ≠ 0) :
    c i h = Function.invFunOn (deriv (E.u i)) (Set.Ioi 0)
      (deriv (E.u i₁) (c i₁ h) * (deriv (E.u i) (c i []) / deriv (E.u i₁) (c i₁ []))) := by
  have key := (eq_13_8 E hE hq0 hpos hdiff hw i i₁).1
  have h1 : deriv (E.u i) (c i h) =
      deriv (E.u i₁) (c i₁ h) * (deriv (E.u i) (c i []) / deriv (E.u i₁) (c i₁ [])) := by
    field_simp
    linarith
  have hex : ∃ a ∈ Set.Ioi (0 : ℝ), deriv (E.u i) a =
      deriv (E.u i₁) (c i₁ h) * (deriv (E.u i) (c i []) / deriv (E.u i₁) (c i₁ [])) :=
    ⟨c i h, hpos i h, h1⟩
  exact hinj i (hpos i h) (Function.invFunOn_mem hex) (h1.trans (Function.invFunOn_eq hex).symm)

/-- Miao, (13.10), p. 419: by feasibility,
`Σᵢ (uⁱ')⁻¹(u¹'(c¹_t(sᵗ)) μᵢ / μ₁) = Σᵢ yⁱ_t(sᵗ)`, the analogue of (13.4) with `λᵢ = μᵢ⁻¹`. -/
theorem eq_13_10 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h))
    (hinj : ∀ k, Set.InjOn (deriv (E.u k)) (Set.Ioi 0)) {h : List S} (hw : 0 < po_w E h)
    (i₁ : ι) (hμ₁ : deriv (E.u i₁) (c i₁ []) ≠ 0) :
    ∑ i, Function.invFunOn (deriv (E.u i)) (Set.Ioi 0)
      (deriv (E.u i₁) (c i₁ h) * (deriv (E.u i) (c i []) / deriv (E.u i₁) (c i₁ []))) =
        ∑ i, y i h := by
  rw [← hE.2.1.2 h]
  exact Finset.sum_congr rfl fun i _ => (eq_13_9 E hE hq0 hpos hdiff hinj hw i i₁ hμ₁).symm

/-- Miao, p. 420 ("the shadow prices `ξ_t(sᵗ)` for the associated planning problem … equal the
Arrow–Debreu state prices"): with `λᵢ = μᵢ⁻¹`, `λᵢ βᵗ Pr(sᵗ) uⁱ'(cⁱ_t(sᵗ)) = q⁰_t(sᵗ)` for every
agent and node, so the planner's multiplier on (13.2) at `sᵗ` is `q⁰_t(sᵗ)`. -/
theorem po_AD_shadow_price {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) (hμ : ∀ i, deriv (E.u i) (c i []) ≠ 0)
    (i : ι) (h : List S) :
    (deriv (E.u i) (c i []))⁻¹ * (po_w E h * deriv (E.u i) (c i h)) = q h := by
  rw [eq_13_6 E hE hq0 i (hpos i) (hdiff i) h, ← mul_assoc, inv_mul_cancel₀ (hμ i), one_mul]

/-- Miao, §13.2–13.3: sufficiency for the planner's problem. If `c` is feasible and interior,
each `uⁱ` is concave, and `λᵢ βᵗ Pr(sᵗ) uⁱ'(cⁱ_t(sᵗ)) = ξ_t(sᵗ)` for all `i` and nodes, with
`λ > 0` and `ξ ∈ L¹`, then `c` solves the planner's problem with weights `λ`. -/
theorem po_planner_of_foc {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i)) {y c : ι → List S → ℝ}
    (hc : po_Feasible y c) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i)
    {ξ : List S → ℝ} (hξ : ξ ∈ po_L1 S)
    (hfoc : ∀ i h, lam i * (po_w E h * deriv (E.u i) (c i h)) = ξ h) :
    po_SolvesPlanner E y lam c := by
  refine ⟨hc, fun d hd => ?_⟩
  have hgain : ∀ i, lam i * po_U E i (d i) - lam i * po_U E i (c i) ≤
      po_cost ξ (d i) - po_cost ξ (c i) := by
    intro i
    have hf : ∀ h, po_w E h * deriv (E.u i) (c i h) = (lam i)⁻¹ * ξ h := by
      intro h
      rw [← hfoc i h, ← mul_assoc, inv_mul_cancel₀ (hlam i).ne', one_mul]
    have := po_utility_gain_le E i (hconc i) (hc.1 i) (hpos i) (hdiff i) hξ _ hf (hd.1 i)
    have := mul_le_mul_of_nonneg_left this (hlam i).le
    rw [← mul_assoc, mul_inv_cancel₀ (hlam i).ne', one_mul] at this
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hgain i
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    po_sum_cost hξ fun i => po_Lplus_subset_Linfty (hd.1 i),
    po_sum_cost hξ fun i => po_Lplus_subset_Linfty (hc.1 i)] at hsum
  have : (fun h => ∑ i, d i h) = fun h => ∑ i, c i h := funext fun h => by rw [hd.2, hc.2]
  rw [this, sub_self] at hsum
  linarith

/-- Miao, p. 419 ("an Arrow–Debreu equilibrium allocation is a particular Pareto optimal
allocation, one that sets the Pareto weights `λᵢ = μᵢ⁻¹`"): an interior equilibrium allocation
with concave felicity functions solves the planner's problem with `λᵢ = uⁱ'(cⁱ₀(s₀))⁻¹`. -/
theorem po_AD_solves_planner {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i)) {y : ι → List S → ℝ} {q : List S → ℝ}
    {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c) (hq0 : q [] = 1)
    (hpos : ∀ i h, 0 < c i h) (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) :
    po_SolvesPlanner E y (fun i => (deriv (E.u i) (c i []))⁻¹) c := by
  have hμ : ∀ i, 0 < deriv (E.u i) (c i []) := fun i =>
    po_deriv_pos (hconc i) (E.u_mono i) (hpos i []) (hdiff i [])
  exact po_planner_of_foc E hconc hE.2.1 hpos hdiff (fun i => inv_pos.mpr (hμ i)) hE.1
    fun i h => po_AD_shadow_price E hE hq0 hpos hdiff (fun k => (hμ k).ne') i h

/-- Miao, Example 13.3.1: with `u(c) = c^{1−γ}/(1−γ)` (`γ > 0`, `γ ≠ 1`), marginal utility is
`u'(c) = c^{−γ}`. -/
theorem po_crra_hasDerivAt {γ : ℝ} (hγ : γ ≠ 1) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun x : ℝ => x ^ (1 - γ) / (1 - γ)) (c ^ (-γ)) c := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).div_const (1 - γ)
  convert this using 1
  rw [show (1 : ℝ) - γ - 1 = -γ by ring]
  field_simp

/-- **Example 13.3.1** (Risk sharing, Miao, p. 420). With CRRA marginal utility `c^{−γ}`,
`γ > 0`, the first-order condition (13.8) `(cⁱ)^{−γ} μⱼ = (cʲ)^{−γ} μᵢ` gives
`cⁱ = cʲ (μᵢ/μⱼ)^{−1/γ}` (consumption is perfectly correlated), and with `Σᵢ cⁱ = ȳ`,
`cⁱ = μᵢ^{−1/γ} / Σⱼ μⱼ^{−1/γ} · ȳ` (a constant share of the aggregate endowment). -/
theorem example_13_3_1 {ι : Type*} [Fintype ι] {γ : ℝ} (hγ : 0 < γ) {μ c : ι → ℝ}
    (hμ : ∀ i, 0 < μ i) (hc : ∀ i, 0 < c i)
    (hfoc : ∀ i j, c i ^ (-γ) * μ j = c j ^ (-γ) * μ i) {Y : ℝ} (hY : ∑ i, c i = Y) :
    (∀ i j, c i = c j * (μ i / μ j) ^ (-1 / γ)) ∧
      ∀ i, c i = μ i ^ (-1 / γ) / (∑ j, μ j ^ (-1 / γ)) * Y := by
  have hpow : ∀ x : ℝ, 0 < x → (x ^ (-γ)) ^ (-1 / γ) = x := by
    intro x hx
    rw [← Real.rpow_mul hx.le, show -γ * (-1 / γ) = 1 by field_simp, Real.rpow_one]
  have h1 : ∀ i j, c i = c j * (μ i / μ j) ^ (-1 / γ) := by
    intro i j
    have e : c i ^ (-γ) = c j ^ (-γ) * (μ i / μ j) := by
      field_simp [(hμ j).ne']
      linarith [hfoc i j]
    have := congrArg (fun z => z ^ (-1 / γ)) e
    rw [hpow _ (hc i), Real.mul_rpow (Real.rpow_nonneg (hc j).le _)
      (div_pos (hμ i) (hμ j)).le, hpow _ (hc j)] at this
    exact this
  refine ⟨h1, fun i => ?_⟩
  have hm : ∀ j, 0 < μ j ^ (-1 / γ) := fun j => Real.rpow_pos_of_pos (hμ j) _
  have hK : ∀ j, c j = c i / μ i ^ (-1 / γ) * μ j ^ (-1 / γ) := by
    intro j
    rw [h1 j i, Real.div_rpow (hμ j).le (hμ i).le]
    field_simp [(hm i).ne']
  have hsum : Y = c i / μ i ^ (-1 / γ) * ∑ j, μ j ^ (-1 / γ) := by
    rw [← hY, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hK j
  have hpos : 0 < ∑ j, μ j ^ (-1 / γ) :=
    Finset.sum_pos (fun j _ => hm j) ⟨i, Finset.mem_univ _⟩
  have hmi := (hm i).ne'
  have hT := hpos.ne'
  set M := μ i ^ (-1 / γ)
  set T := ∑ j, μ j ^ (-1 / γ)
  rw [hsum]
  field_simp

/-- Miao, Example 13.3.1, p. 420, in the economy: at an Arrow–Debreu equilibrium with
`q⁰₀(s₀) = 1`, interior consumption and CRRA marginal utility `uⁱ'(c) = c^{−γ}` for all agents,
every agent consumes the constant share `μᵢ^{−1/γ} / Σⱼ μⱼ^{−1/γ}` of the aggregate endowment at
every node of positive probability, with `μᵢ = (cⁱ₀(s₀))^{−γ}`. -/
theorem example_13_3_1_shares {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {γ : ℝ} (hγ : 0 < γ) (hu : ∀ i x, 0 < x → deriv (E.u i) x = x ^ (-γ))
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) {h : List S} (hw : 0 < po_w E h)
    (i : ι) :
    c i h = (c i [] ^ (-γ)) ^ (-1 / γ) / (∑ j, (c j [] ^ (-γ)) ^ (-1 / γ)) * ∑ j, y j h := by
  have hfoc : ∀ i j, c i h ^ (-γ) * c j [] ^ (-γ) = c j h ^ (-γ) * c i [] ^ (-γ) := by
    intro i j
    have := (eq_13_8 E hE hq0 hpos hdiff hw i j).1
    rwa [hu i _ (hpos i h), hu j _ (hpos j []), hu j _ (hpos j h), hu i _ (hpos i [])] at this
  exact (example_13_3_1 hγ (fun j => Real.rpow_pos_of_pos (hpos j []) _) (fun j => hpos j h)
    hfoc (hE.2.1.2 h)).2 i

/-- Miao, p. 421 ("Multiplying all of the `μᵢ`'s by a positive scalar changes the scale of the
price system"): if `(μ, q⁰)` satisfy (13.6) then so do `(kμ, q⁰/k)`, and the right side of
(13.9) depends only on the ratios `μᵢ/μ₁`. -/
theorem po_negishi_scale {ι S : Type*} [Fintype S] (E : POEconomy ι S) {c : ι → List S → ℝ}
    {μ : ι → ℝ} {q : List S → ℝ}
    (hfoc : ∀ i h, po_w E h * deriv (E.u i) (c i h) = μ i * q h) {k : ℝ} (hk : k ≠ 0) :
    (∀ i h, po_w E h * deriv (E.u i) (c i h) = (k * μ i) * (q h / k)) ∧
      ∀ i i₁, k * μ i / (k * μ i₁) = μ i / μ i₁ := by
  refine ⟨fun i h => by rw [hfoc i h]; field_simp, fun i i₁ => ?_⟩
  rw [mul_div_mul_left _ _ hk]

/-- Miao, p. 421 ("According to the above algorithm, `q⁰₀(s₀) ≠ 1` in general"): by (13.6) at
the root, `q⁰₀(s₀) μ₁ = u¹'(c¹₀(s₀))`, so `q⁰₀(s₀) = 1` iff the fixed `μ₁` equals
`u¹'(c¹₀(s₀))`. -/
theorem po_negishi_q0 {ι S : Type*} [Fintype S] (E : POEconomy ι S) {c : ι → List S → ℝ}
    {μ : ι → ℝ} {q : List S → ℝ}
    (hfoc : ∀ i h, po_w E h * deriv (E.u i) (c i h) = μ i * q h) (i₁ : ι) (hμ : μ i₁ ≠ 0) :
    q [] = 1 ↔ μ i₁ = deriv (E.u i₁) (c i₁ []) := by
  have := hfoc i₁ []
  rw [po_w_root, one_mul] at this
  rw [this]
  constructor
  · intro h; rw [h, mul_one]
  · intro h
    exact mul_left_cancel₀ hμ (h.symm.trans (mul_one _).symm)

/-- Miao, p. 421, step 3 of the Negishi algorithm: given `u¹'(c¹_t(sᵗ)) = v > 0`, (13.9) sets
`uⁱ'(cⁱ_t(sᵗ)) = (μᵢ/μ₁) v`; with strictly decreasing marginal utility, raising `μᵢ` lowers
`cⁱ_t(sᵗ)` (and so the cost of agent `i`'s plan), which is why `μᵢ` is raised when cost exceeds
the value of the endowment. -/
theorem po_negishi_step3 {u : ℝ → ℝ} (hanti : StrictAntiOn (deriv u) (Set.Ioi 0)) {a b m m' v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (hm : m < m') (hua : deriv u a = m * v)
    (hub : deriv u b = m' * v) : b < a := by
  have hlt : deriv u a < deriv u b := by
    rw [hua, hub]; exact mul_lt_mul_of_pos_right hm hv
  by_contra hge
  push Not at hge
  rcases hge.lt_or_eq with hab | hab
  · exact absurd (hanti ha hb hab) (not_lt.mpr hlt.le)
  · rw [hab] at hlt; exact lt_irrefl _ hlt

/-- Miao, p. 421, the Negishi algorithm at convergence: if the candidate allocation is feasible
and interior, the prices `q⁰ ∈ L¹` satisfy (13.6) for every agent with `μᵢ > 0`, the felicity
functions are concave, and every budget constraint (13.5) holds with equality, then `(c, q⁰)` is
an Arrow–Debreu equilibrium. -/
theorem po_negishi_fixed_point {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i)) {y c : ι → List S → ℝ}
    (hc : po_Feasible y c) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) {q : List S → ℝ} (hq : q ∈ po_L1 S)
    {μ : ι → ℝ} (hμ : ∀ i, 0 < μ i)
    (hfoc : ∀ i h, po_w E h * deriv (E.u i) (c i h) = μ i * q h)
    (hbud : ∀ i, po_cost q (c i) = po_cost q (y i)) : po_ADEquilibrium E y q c :=
  ⟨hq, hc, fun i => ⟨(hbud i).le, fun _ hx hxb =>
    po_optimal_of_foc E i (hconc i) (hc.1 i) (hpos i) (hdiff i) hq (hμ i).le (hfoc i) (hbud i)
      hx hxb⟩⟩

/-- Miao, proof of Theorem 13.3.1: local nonsatiation. If `x ∈ L∞₊` costs strictly less than the
endowment, a slightly larger plan at the root is still affordable and strictly better. -/
theorem po_local_nonsatiation {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι)
    {q x : List S → ℝ} (hq : q ∈ po_L1 S) (hx : x ∈ po_Lplus S) {b : ℝ}
    (hlt : po_cost q x < b) :
    ∃ x' ∈ po_Lplus S, po_cost q x' ≤ b ∧ po_U E i x < po_U E i x' := by
  classical
  set ε := (b - po_cost q x) / (|q []| + 1)
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hnn : 0 ≤ x [] + ε := by linarith [hx.1 []]
  refine ⟨Function.update x [] (x [] + ε), po_update_mem hx [] hnn, ?_, ?_⟩
  · rw [po_cost_update hq (po_Lplus_subset_Linfty hx), add_sub_cancel_left]
    have h1 : q [] * ε ≤ |q []| * ε := mul_le_mul_of_nonneg_right (le_abs_self _) hε.le
    have h2 : (|q []| + 1) * ε = b - po_cost q x := by
      simp only [ε]; field_simp
    nlinarith
  · rw [po_U_update E i hx, po_w_root, one_mul]
    have := E.u_mono i (Set.mem_Ici.mpr (hx.1 [])) (Set.mem_Ici.mpr hnn) (by linarith)
    linarith

/-- **Theorem 13.3.1** (First Welfare Theorem, Miao, p. 421). If each `uⁱ` is strictly
increasing and `(c, q⁰)` is an Arrow–Debreu equilibrium, then `c` is Pareto optimal. (The
endowments are in `L∞₊`, so that their values are defined.) -/
theorem theorem_13_3_1 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} (hy : ∀ i, y i ∈ po_Lplus S) {q : List S → ℝ} {c : ι → List S → ℝ}
    (hE : po_ADEquilibrium E y q c) : po_ParetoOptimal E y c := by
  obtain ⟨hq, hc, hopt⟩ := hE
  refine ⟨hc, ?_⟩
  rintro ⟨d, hd, hle, i₀, hlt⟩
  have hge : ∀ i, po_cost q (y i) ≤ po_cost q (d i) := by
    intro i
    by_contra hcon
    push Not at hcon
    obtain ⟨x', hx', hx'b, hx'U⟩ := po_local_nonsatiation E i hq (hd.1 i) hcon
    have := (hopt i).2 x' hx' hx'b
    linarith [hle i]
  have hgt : po_cost q (y i₀) < po_cost q (d i₀) := by
    by_contra hcon
    push Not at hcon
    have := (hopt i₀).2 (d i₀) (hd.1 i₀) hcon
    linarith
  have hsum : ∑ i, po_cost q (y i) < ∑ i, po_cost q (d i) :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨i₀, Finset.mem_univ _, hgt⟩
  rw [po_sum_cost hq fun i => po_Lplus_subset_Linfty (hy i),
    po_sum_cost hq fun i => po_Lplus_subset_Linfty (hd.1 i)] at hsum
  have : (fun h => ∑ i, d i h) = fun h => ∑ i, y i h := funext hd.2
  rw [this] at hsum
  exact lt_irrefl _ hsum

/-- Miao, §13.2–13.3: a Pareto optimal interior allocation with concave, differentiable felicity
functions satisfies the planner's first-order conditions with strictly positive weights. -/
theorem po_pareto_foc {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i)) {y c : ι → List S → ℝ}
    (hpo : po_ParetoOptimal E y c) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) :
    ∃ lam : ι → ℝ, (∀ i, 0 < lam i) ∧ po_SolvesPlanner E y lam c ∧
      ∀ h, 0 < po_w E h → ∀ i j, lam i * deriv (E.u i) (c i h) = lam j * deriv (E.u j) (c j h) := by
  obtain ⟨lam, hlam, hne, hpl⟩ := po_planner_of_pareto E hconc hpo
  have hfoc : ∀ h, 0 < po_w E h → ∀ i j,
      lam i * deriv (E.u i) (c i h) = lam j * deriv (E.u j) (c j h) := fun h hw i j =>
    po_planner_foc_ratio E hpl h hw (fun k => hpos k h) (fun k => hdiff k h) i j
  obtain ⟨j, hj⟩ : ∃ j, lam j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hjpos : 0 < lam j := lt_of_le_of_ne (hlam j) (Ne.symm hj)
  refine ⟨lam, fun i => ?_, hpl, hfoc⟩
  have e := hfoc [] (by rw [po_w_root]; exact one_pos) i j
  have hdj := po_deriv_pos (hconc j) (E.u_mono j) (hpos j []) (hdiff j [])
  have hdi := po_deriv_pos (hconc i) (E.u_mono i) (hpos i []) (hdiff i [])
  rcases (hlam i).lt_or_eq with h | h
  · exact h
  · rw [← h, zero_mul] at e
    nlinarith

/-- **Theorem 13.3.2** (Second Welfare Theorem, Miao, p. 421), corrected. Let each `uⁱ` be
concave on `[0, ∞)` and differentiable on `(0, ∞)`, and let `c` be a Pareto optimal allocation
that is uniformly interior (`cⁱ_t(sᵗ) ≥ δ > 0`). Then there are state prices `q⁰ ∈ L¹` with
`q⁰₀(s₀) = 1` such that `(c, q⁰)` is an Arrow–Debreu equilibrium of the economy in which agent
`i`'s endowment is `cⁱ` (equivalently: after lump-sum transfers). As printed, with the original
endowments, the theorem is false (`theorem_13_3_2_counterexample`). -/
theorem theorem_13_3_2 {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i))
    (hdiff : ∀ i x, 0 < x → DifferentiableAt ℝ (E.u i) x) {y c : ι → List S → ℝ}
    (hpo : po_ParetoOptimal E y c) {δ : ℝ} (hδ : 0 < δ) (hint : ∀ i h, δ ≤ c i h) :
    ∃ q : List S → ℝ, q [] = 1 ∧ po_ADEquilibrium E c q c := by
  have hpos : ∀ i h, 0 < c i h := fun i h => hδ.trans_le (hint i h)
  have hd : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h) := fun i h => hdiff i _ (hpos i h)
  obtain ⟨lam, hlam, -, hfoc⟩ := po_pareto_foc E hconc hpo hpos hd
  set j : ι := Classical.arbitrary ι
  set m := deriv (E.u j) (c j [])
  have hm : 0 < m := po_deriv_pos (hconc j) (E.u_mono j) (hpos j []) (hd j [])
  set q : List S → ℝ := fun h => po_w E h * deriv (E.u j) (c j h) / m with hqdef
  have hq0 : q [] = 1 := by simp only [hqdef, po_w_root, one_mul]; exact div_self hm.ne'
  have hdpos : ∀ h, 0 < deriv (E.u j) (c j h) := fun h =>
    po_deriv_pos (hconc j) (E.u_mono j) (hpos j h) (hd j h)
  have hdle : ∀ h, deriv (E.u j) (c j h) ≤ deriv (E.u j) δ := fun h =>
    ((hconc j).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).antitoneOn_deriv
      (fun x hx => hdiff j x hx) (Set.mem_Ioi.mpr hδ) (Set.mem_Ioi.mpr (hpos j h)) (hint j h)
  have hqnn : ∀ h, 0 ≤ q h := fun h =>
    div_nonneg (mul_nonneg (po_w_nonneg E h) (hdpos h).le) hm.le
  have hq : q ∈ po_L1 S := by
    change Summable fun h => |q h|
    simp only [abs_of_nonneg (hqnn _)]
    refine Summable.of_nonneg_of_le hqnn (fun h => ?_)
      ((po_summable_w E).mul_right (deriv (E.u j) δ / m))
    simp only [hqdef]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hdle h) hm.le)
      (po_w_nonneg E h)
  have hfoc' : ∀ i h, po_w E h * deriv (E.u i) (c i h) = (lam j * m / lam i) * q h := by
    intro i h
    rcases (po_w_nonneg E h).lt_or_eq with hw | hw
    · have e := hfoc h hw i j
      simp only [hqdef]
      field_simp [(hlam i).ne', hm.ne']
      rw [← e]
      ring
    · simp only [hqdef, ← hw, zero_mul, zero_div, mul_zero]
  refine ⟨q, hq0, hq, ⟨hpo.1.1, fun _ => rfl⟩, fun i => ⟨le_rfl, fun x hx hxb => ?_⟩⟩
  exact po_optimal_of_foc E i (hconc i) (hpo.1.1 i) (hpos i) (hd i) hq
    (div_pos (mul_pos (hlam j) hm) (hlam i)).le (hfoc' i) rfl hx hxb

/-- Miao, Theorem 13.3.2 as printed is false. In `po_exampleEconomy` (two agents, `uⁱ = √·`),
let agent `0` own one unit at every node and agent `1` nothing. The allocation giving everything
to agent `1` is Pareto optimal, but it is not an Arrow–Debreu equilibrium allocation at any
prices: agent `0` could always afford her endowment, which she prefers to nothing. -/
theorem theorem_13_3_2_counterexample :
    let y : Fin 2 → List Bool → ℝ := fun i _ => if i = 0 then 1 else 0
    let c : Fin 2 → List Bool → ℝ := fun i _ => if i = 0 then 0 else 1
    po_ParetoOptimal po_exampleEconomy y c ∧ ¬ ∃ q, po_ADEquilibrium po_exampleEconomy y q c := by
  intro y c
  have h0 : (fun _ : List Bool => (0 : ℝ)) ∈ po_Lplus Bool :=
    ⟨fun _ => le_rfl, 0, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  have h1 : (fun _ : List Bool => (1 : ℝ)) ∈ po_Lplus Bool :=
    ⟨fun _ => zero_le_one, 1, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  have hcmem : ∀ i, c i ∈ po_Lplus Bool := fun i => by
    by_cases hi : i = 0
    · simp only [c, hi, ↓reduceIte]; exact h0
    · simp only [c, hi, ↓reduceIte]; exact h1
  have hfeas : po_Feasible y c := ⟨hcmem, fun h => by simp [c, y, Fin.sum_univ_two]⟩
  refine ⟨?_, ?_⟩
  · have hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (po_exampleEconomy.u i) := fun i =>
      (po_exampleEconomy_assumption i).2.2.2.1.concaveOn
    have hcont : ∀ i, ContinuousOn (po_exampleEconomy.u i) (Set.Ici 0) := fun i =>
      (po_exampleEconomy_assumption i).2.1
    refine (proposition_13_2_1 po_exampleEconomy hconc hcont y c).mpr
      ⟨fun i => if i = 0 then 0 else 1, fun i => by by_cases hi : i = 0 <;> simp [hi], ?_,
        hfeas, fun d hd => ?_⟩
    · intro h
      have := congrFun h 1
      simp at this
    · simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, zero_mul, zero_add, one_mul,
        show (1 : Fin 2) ≠ 0 by decide]
      refine po_U_mono _ 1 (hd.1 1) (hcmem 1) fun h => ?_
      have := hd.2 h
      simp only [Fin.sum_univ_two, y, c, Fin.isValue, ↓reduceIte,
        show (1 : Fin 2) ≠ 0 by decide] at this ⊢
      linarith [(hd.1 0).1 h]
  · rintro ⟨q, -, -, hopt⟩
    classical
    have hy0 : y 0 = fun _ => 1 := rfl
    have hc0 : c 0 = fun _ => 0 := rfl
    have hle := (hopt 0).2 (fun _ => 1) h1 (by rw [hy0])
    rw [hc0] at hle
    have hup := po_U_update po_exampleEconomy 0 h0 [] 1
    have hmono := po_U_mono po_exampleEconomy 0 (po_update_mem h0 [] zero_le_one) h1
      (fun h => by by_cases hh : h = [] <;> simp [hh])
    rw [po_w_root, one_mul] at hup
    have : po_exampleEconomy.u 0 0 < po_exampleEconomy.u 0 1 :=
      po_exampleEconomy.u_mono 0 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one)
        zero_lt_one
    linarith

/-- Miao, pp. 423–424: the date-`t` price at node `sᵗ` of an asset with payoffs `d`,
`p_t(sᵗ) = q⁰_t(sᵗ)⁻¹ Σ_{j ≥ 1} Σ_{s^{t+j} | sᵗ} q⁰_{t+j}(s^{t+j}) d_{t+j}(s^{t+j})`. -/
noncomputable def po_assetPrice {S : Type*} [Fintype S] (q d : List S → ℝ) (h : List S) : ℝ :=
  (q h)⁻¹ * ∑' j : ℕ, ∑ f : Fin (j + 1) → S, q (List.ofFn f ++ h) * d (List.ofFn f ++ h)

/-- Miao, p. 424 ("it is important that `q⁰ ∈ L¹` for the above prices to be well-defined"):
for `q⁰ ∈ L¹` and `d ∈ L∞` the series defining the asset price converges. -/
theorem po_assetPrice_summable {S : Type*} [Fintype S] {q d : List S → ℝ} (hq : q ∈ po_L1 S)
    (hd : d ∈ po_Linfty S) (h : List S) :
    Summable fun j : ℕ => ∑ f : Fin (j + 1) → S, q (List.ofFn f ++ h) * d (List.ofFn f ++ h) := by
  set ι' : (Σ j : ℕ, Fin (j + 1) → S) → List S := fun x => List.ofFn x.2 ++ h
  have hinj : Function.Injective ι' := by
    rintro ⟨j, f⟩ ⟨j', f'⟩ he
    simp only [ι', List.append_cancel_right_eq] at he
    have := List.ofFn_inj'.mp he
    simp only [Sigma.mk.injEq, add_left_inj] at this
    obtain ⟨rfl, hf⟩ := this
    rw [heq_eq_eq] at hf
    rw [hf]
  have hs := ((eq_13_5 hq hd).comp_injective hinj).sigma
  simp only [Function.comp_def, ι', tsum_fintype] at hs
  exact hs

/-- Miao, p. 423: at the root, with `q⁰₀(s₀) = 1`, the date-zero price is
`p₀ = Σ_{j ≥ 1} Σ_{sʲ} q⁰_j(sʲ) d_j(sʲ)`. -/
theorem po_assetPrice_root {S : Type*} [Fintype S] {q : List S → ℝ} (hq0 : q [] = 1)
    (d : List S → ℝ) :
    po_assetPrice q d [] =
      ∑' j : ℕ, ∑ f : Fin (j + 1) → S, q (List.ofFn f) * d (List.ofFn f) := by
  simp [po_assetPrice, hq0]

/-- Miao, p. 424 ("For the discounted expected utility (13.1), `q⁰_t` is given in (13.7)"):
substituting (13.7), `p_t(sᵗ) = Σ_{j ≥ 1} Σ_{s^{t+j}|sᵗ} βʲ Pr(s^{t+j} | sᵗ)
(u'(c_{t+j}(s^{t+j})) / u'(c_t(sᵗ))) d_{t+j}(s^{t+j})`. -/
theorem po_assetPrice_eq {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι)
    {q d c : List S → ℝ} (hq : ∀ g, q g = po_w E g * deriv (E.u i) (c g) / deriv (E.u i) (c []))
    (hμ : deriv (E.u i) (c []) ≠ 0) {h : List S} (hpr : 0 < E.P.pr h)
    (hdh : deriv (E.u i) (c h) ≠ 0) :
    po_assetPrice q d h = ∑' j : ℕ, ∑ f : Fin (j + 1) → S,
      E.β ^ (j + 1) * po_condPr E.P (List.ofFn f ++ h) h *
        (deriv (E.u i) (c (List.ofFn f ++ h)) / deriv (E.u i) (c h)) * d (List.ofFn f ++ h) := by
  unfold po_assetPrice
  rw [← tsum_mul_left]
  congr 1
  funext j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hq, hq]
  unfold po_w po_condPr
  rw [List.length_append, List.length_ofFn, pow_add]
  have hβ : E.β ^ h.length ≠ 0 := pow_ne_zero _ E.β_pos.ne'
  field_simp

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 13.1 and 13.2

Miao, §13.9, p. 452.

* **Exercise 13.1** (existence of a representative agent, `ex_13_1`). `po_Ulam E λ x` is
  (13.37), the supremum of `Σᵢ λⁱ Uⁱ(cⁱ)` over the allocations of `x`. Departure: the exercise
  starts from a Radner equilibrium with nonbinding debt constraints, zero asset supply and
  complete markets, whose allocation and prices are those of an Arrow–Debreu equilibrium (§13.5;
  not part of this module). The statement proved here starts from an interior Arrow–Debreu
  equilibrium with `q⁰₀(s₀) = 1` and concave, differentiable felicity functions: with
  `λᵢ = uⁱ'(cⁱ₀(s₀))⁻¹ > 0`, the equilibrium allocation solves (13.37) at `ȳ`, and `(ȳ, q⁰)` is a
  no-trade equilibrium for the representative agent with utility `U_λ` and endowment `ȳ`.
* **Exercise 13.2** (`ex_13_2`, `ex_13_2_converse`). With a constant aggregate endowment `Y`
  and Assumption 13.1.1, the interior Pareto optimal allocations are exactly the constant ones:
  `cⁱ_t(sᵗ) = κᵢ` at all nodes of positive probability, with `Σᵢ κᵢ = Y` and
  `λⁱ uⁱ'(κᵢ)` equal across agents.
* `po_example_ADEquilibrium`: an Arrow–Debreu equilibrium exists in `po_exampleEconomy`, so
  Definition 13.3.1 is not vacuous.
-/

namespace Miao.CompleteMarkets

/-- Miao, (13.37), p. 452: the values `Σᵢ λⁱ Uⁱ(cⁱ)` attained by allocations `c ∈ (L∞₊)ᴵ` of
`x`, `Σᵢ cⁱ = x`. -/
def po_repSet {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S) (lam : ι → ℝ)
    (x : List S → ℝ) : Set ℝ :=
  {v | ∃ d : ι → List S → ℝ, (∀ i, d i ∈ po_Lplus S) ∧ (∀ h, ∑ i, d i h = x h) ∧
    v = ∑ i, lam i * po_U E i (d i)}

/-- Miao, (13.37), p. 452: the representative agent's utility
`U_λ(x) = sup {Σᵢ λⁱ Uⁱ(cⁱ) : Σᵢ cⁱ = x}`. -/
noncomputable def po_Ulam {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (lam : ι → ℝ) (x : List S → ℝ) : ℝ :=
  sSup (po_repSet E lam x)

/-- **Exercise 13.1** (Existence of a representative agent, Miao, p. 452), for an interior
Arrow–Debreu equilibrium `(c, q⁰)` with `q⁰₀(s₀) = 1`: with `λᵢ = uⁱ'(cⁱ₀(s₀))⁻¹ > 0`, the
allocation `c` solves (13.37) at `ȳ = Σᵢ yⁱ`, `U_λ(ȳ) = Σᵢ λᵢ Uⁱ(cⁱ)`, and `ȳ` maximises `U_λ`
over the representative agent's budget set `{x ∈ L∞₊ : q⁰ · x ≤ q⁰ · ȳ}`, so `(ȳ, q⁰)` is a
no-trade equilibrium. -/
theorem ex_13_1 {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i)) {y : ι → List S → ℝ} {q : List S → ℝ}
    {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c) (hq0 : q [] = 1)
    (hpos : ∀ i h, 0 < c i h) (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) :
    (∀ i, 0 < (deriv (E.u i) (c i []))⁻¹) ∧
      IsGreatest (po_repSet E (fun i => (deriv (E.u i) (c i []))⁻¹) (fun h => ∑ i, y i h))
        (∑ i, (deriv (E.u i) (c i []))⁻¹ * po_U E i (c i)) ∧
      po_Ulam E (fun i => (deriv (E.u i) (c i []))⁻¹) (fun h => ∑ i, y i h) =
        ∑ i, (deriv (E.u i) (c i []))⁻¹ * po_U E i (c i) ∧
      ∀ x ∈ po_Lplus S, po_cost q x ≤ po_cost q (fun h => ∑ i, y i h) →
        po_Ulam E (fun i => (deriv (E.u i) (c i []))⁻¹) x ≤
          po_Ulam E (fun i => (deriv (E.u i) (c i []))⁻¹) (fun h => ∑ i, y i h) := by
  set μ : ι → ℝ := fun i => deriv (E.u i) (c i []) with hμdef
  have hμ : ∀ i, 0 < μ i := fun i =>
    po_deriv_pos (hconc i) (E.u_mono i) (hpos i []) (hdiff i [])
  set ybar : List S → ℝ := fun h => ∑ i, y i h
  have hq := hE.1
  have hc := hE.2.1
  -- the key bound: any allocation `d` of `x` gives at most `Σ λU(c) + q·x − q·ȳ`
  have key : ∀ x, ∀ d : ι → List S → ℝ, (∀ i, d i ∈ po_Lplus S) → (∀ h, ∑ i, d i h = x h) →
      ∑ i, (μ i)⁻¹ * po_U E i (d i) ≤
        ∑ i, (μ i)⁻¹ * po_U E i (c i) + (po_cost q x - po_cost q ybar) := by
    intro x d hd hdx
    have hgain : ∀ i, (μ i)⁻¹ * po_U E i (d i) - (μ i)⁻¹ * po_U E i (c i) ≤
        po_cost q (d i) - po_cost q (c i) := by
      intro i
      have := po_utility_gain_le E i (hconc i) (hc.1 i) (hpos i) (hdiff i) hq (μ i)
        (eq_13_6 E hE hq0 i (hpos i) (hdiff i)) (hd i)
      have := mul_le_mul_of_nonneg_left this (inv_pos.mpr (hμ i)).le
      rw [← mul_assoc, inv_mul_cancel₀ (hμ i).ne', one_mul] at this
      linarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hgain i
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      po_sum_cost hq fun i => po_Lplus_subset_Linfty (hd i),
      po_sum_cost hq fun i => po_Lplus_subset_Linfty (hc.1 i)] at hsum
    have e1 : (fun h => ∑ i, d i h) = x := funext hdx
    have e2 : (fun h => ∑ i, c i h) = ybar := funext hc.2
    rw [e1, e2] at hsum
    linarith
  have hgreat : IsGreatest (po_repSet E (fun i => (μ i)⁻¹) ybar)
      (∑ i, (μ i)⁻¹ * po_U E i (c i)) := by
    refine ⟨⟨c, hc.1, hc.2, rfl⟩, ?_⟩
    rintro v ⟨d, hd, hdx, rfl⟩
    have := key ybar d hd hdx
    linarith
  have hval := hgreat.csSup_eq
  refine ⟨fun i => inv_pos.mpr (hμ i), hgreat, hval, fun x hx hxb => ?_⟩
  unfold po_Ulam
  rw [hval]
  obtain i₀ : ι := Classical.arbitrary ι
  classical
  have hne : (po_repSet E (fun i => (μ i)⁻¹) x).Nonempty := by
    have h0 : (fun _ : List S => (0 : ℝ)) ∈ po_Lplus S :=
      ⟨fun _ => le_rfl, 0, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
    refine ⟨_, fun i => if i = i₀ then x else fun _ => 0, fun i => ?_, fun h => ?_, rfl⟩
    · by_cases hi : i = i₀
      · simp only [hi, ↓reduceIte]; exact hx
      · simp only [hi, ↓reduceIte]; exact h0
    · simp only [apply_ite (fun f : List S → ℝ => f h), Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]
  refine csSup_le hne ?_
  rintro v ⟨d, hd, hdx, rfl⟩
  have := key x d hd hdx
  linarith

/-- **Exercise 13.2** (Miao, p. 452). If the aggregate endowment is constant, `Σᵢ yⁱ_t(sᵗ) = Y`,
and each `uⁱ` satisfies Assumption 13.1.1, then an interior Pareto optimal allocation is
constant over time and states: `cⁱ_t(sᵗ) = cⁱ₀(s₀) =: κᵢ` at every node of positive
probability, where `Σᵢ κᵢ = Y` and, for some weights `λ > 0`, `λⁱ uⁱ'(κᵢ) = λʲ uʲ'(κⱼ)`. -/
theorem ex_13_2 {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι] (E : POEconomy ι S)
    (hA : ∀ i, Assumption13_1_1 (E.u i)) {y c : ι → List S → ℝ} {Y : ℝ}
    (hY : ∀ h, ∑ i, y i h = Y) (hpo : po_ParetoOptimal E y c) (hpos : ∀ i h, 0 < c i h) :
    (∀ i h, 0 < po_w E h → c i h = c i []) ∧ ∑ i, c i [] = Y ∧
      ∃ lam : ι → ℝ, (∀ i, 0 < lam i) ∧
        ∀ i j, lam i * deriv (E.u i) (c i []) = lam j * deriv (E.u j) (c j []) := by
  have hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i) := fun i => (hA i).2.2.2.1.concaveOn
  have hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h) := fun i h =>
    po_differentiableAt (hA i) (hpos i h)
  obtain ⟨lam, hlam, -, hfoc⟩ := po_pareto_foc E hconc hpo hpos hdiff
  have hw0 : 0 < po_w E [] := by rw [po_w_root]; exact one_pos
  refine ⟨fun i h hw => po_risk_sharing E hpo.1 hlam (fun k => po_strictAntiOn_deriv (hA k))
      hpos hfoc hw hw0 (by rw [hY, hY]) i, by rw [hpo.1.2, hY], lam, hlam, hfoc [] hw0⟩

/-- **Exercise 13.2** (Miao, p. 452), converse. With a constant aggregate endowment `Y` and each
`uⁱ` satisfying Assumption 13.1.1, every constant allocation `cⁱ_t(sᵗ) = κᵢ > 0` with
`Σᵢ κᵢ = Y` is Pareto optimal (it solves the planner's problem with `λᵢ = uⁱ'(κᵢ)⁻¹`). -/
theorem ex_13_2_converse {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (hA : ∀ i, Assumption13_1_1 (E.u i)) {y : ι → List S → ℝ} {Y : ℝ}
    (hY : ∀ h, ∑ i, y i h = Y) {κ : ι → ℝ} (hκ : ∀ i, 0 < κ i) (hsum : ∑ i, κ i = Y) :
    po_ParetoOptimal E y (fun i _ => κ i) := by
  have hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i) := fun i => (hA i).2.2.2.1.concaveOn
  have hd : ∀ i, 0 < deriv (E.u i) (κ i) := fun i =>
    po_deriv_pos (hconc i) (E.u_mono i) (hκ i) (po_differentiableAt (hA i) (hκ i))
  have hfeas : po_Feasible y (fun i _ => κ i) :=
    ⟨fun i => ⟨fun _ => (hκ i).le, κ i, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩,
      fun h => by rw [hsum, hY]⟩
  have hξ : po_w E ∈ po_L1 S := by
    change Summable fun h => |po_w E h|
    simp only [abs_of_nonneg (po_w_nonneg E _)]
    exact po_summable_w E
  refine po_pareto_of_planner_pos E (fun i => inv_pos.mpr (hd i))
    (po_planner_of_foc E hconc hfeas (fun i _ => hκ i)
      (fun i _ => po_differentiableAt (hA i) (hκ i)) (fun i => inv_pos.mpr (hd i)) hξ
      fun i h => ?_)
  field_simp [(hd i).ne']

/-- Miao, Definition 13.3.1 is not vacuous: in `po_exampleEconomy` with both agents endowed
with one unit at every node, autarky `cⁱ = yⁱ` is an Arrow–Debreu equilibrium at some prices
`q⁰ ∈ L¹` with `q⁰₀(s₀) = 1` (by `ex_13_2_converse` and `theorem_13_3_2`). -/
theorem po_example_ADEquilibrium :
    ∃ q : List Bool → ℝ, q [] = 1 ∧
      po_ADEquilibrium po_exampleEconomy (fun _ _ => 1) q (fun _ _ => 1) := by
  have hA := po_exampleEconomy_assumption
  have hpo : po_ParetoOptimal po_exampleEconomy (fun _ _ => (1 : ℝ)) (fun _ _ => 1) :=
    ex_13_2_converse po_exampleEconomy hA (Y := 2) (fun _ => by simp)
      (κ := fun _ => 1) (fun _ => one_pos) (by simp)
  exact theorem_13_3_2 po_exampleEconomy (fun i => (hA i).2.2.2.1.concaveOn)
    (fun i _ hx => po_differentiableAt (hA i) hx) hpo one_pos (fun _ _ => le_rfl)

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The event tree, date sums and discounted expected utility

Miao, §13.1, pp. 415–416, as used in §§13.4–13.5 (pp. 424–439).

A node (history) `sᵗ = (s₀, s₁, …, sₜ)` is a list of shocks over a finite set `S`, *newest
first*: the root `s⁰` is `[]`, the date of a node is its length, the immediate successors of
`h` are `s :: h` (`s ∈ S`) and the immediate predecessor of `s :: h` is `h`. The descendants of
`h` at distance `j` are the lists `l ++ h` with `l` of length `j`.

* `rd_paths S j`: the finite set of shock lists of length `j` (`rd_mem_paths`).
* `rd_dsum F h j = ∑_{sᵗ⁺ʲ | h} F(sᵗ⁺ʲ)`: the sum of `F` over the descendants of `h` at distance
  `j`; `rd_dsum F [] t` is the sum over all date-`t` nodes. It satisfies the root-side recursion
  `rd_dsum_succ`, the leaf-side recursion `rd_dsum_succ'` and `rd_dsum_add_len`.
* `RDTree S`: the probabilities `Pr(sᵗ)` (positive, `Pr(s⁰) = 1`, consistent:
  `∑ₛ Pr(s :: h) = Pr(h)`); `rd_uniformTree` is a concrete instance. `rd_condE` is the
  conditional expectation `E_t[X_{t+j}]`.
* `rd_Bdd`, `rd_LinfPos`, `rd_L1`: the spaces `L^∞`, `L^∞₊` and `L¹` of adapted processes.
  `L¹` is read with respect to the date sums (`∑ₜ ∑_{sᵗ} |x(sᵗ)| < ∞`, as on p. 416).
* `rd_EU`: the discounted expected utility (13.1); `rd_eq_13_1` shows it is strictly increasing on
  `L^∞₊` when `u` is strictly increasing (the property used by Theorem 13.4.1).
-/

namespace Miao.CompleteMarkets

open Filter Topology

/-- Appending a single shock at the old end of a list is injective. -/
theorem rd_snoc_injective (S : Type*) :
    Function.Injective (fun x : List S × S => x.1 ++ [x.2]) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ hab
  have h := List.append_inj' hab rfl
  simp only [List.cons.injEq, and_true] at h
  rw [h.1, h.2]

/-- The finite set of all shock lists of length `j`. -/
def rd_paths (S : Type*) [Fintype S] : ℕ → Finset (List S)
  | 0 => {[]}
  | j + 1 => (rd_paths S j ×ˢ Finset.univ).map ⟨fun x => x.1 ++ [x.2], rd_snoc_injective S⟩

/-- Membership in `rd_paths S j` is having length `j`. -/
theorem rd_mem_paths {S : Type*} [Fintype S] (j : ℕ) (l : List S) :
    l ∈ rd_paths S j ↔ l.length = j := by
  induction j generalizing l with
  | zero => simp [rd_paths]
  | succ j ih =>
    simp only [rd_paths, Finset.mem_map, Finset.mem_product, Finset.mem_univ, and_true,
      Function.Embedding.coeFn_mk, Prod.exists, ih]
    constructor
    · rintro ⟨a, b, ha, rfl⟩
      simp [ha]
    · intro hl
      have hne : l ≠ [] := by
        rintro rfl
        simp at hl
      refine ⟨l.dropLast, l.getLast hne, ?_, List.dropLast_append_getLast hne⟩
      simp [hl]

/-- The sum of `F` over the descendants of the node `h` at distance `j`. -/
def rd_dsum {S : Type*} [Fintype S] (F : List S → ℝ) (h : List S) (j : ℕ) : ℝ :=
  ∑ l ∈ rd_paths S j, F (l ++ h)

variable {S : Type*} [Fintype S]

/-- Distance `0`: the node itself. -/
theorem rd_dsum_zero (F : List S → ℝ) (h : List S) : rd_dsum F h 0 = F h := by
  simp [rd_dsum, rd_paths]

/-- Root-side recursion: descendants at distance `j + 1` of `h` are the descendants at distance
`j` of its successors `s :: h`. -/
theorem rd_dsum_succ (F : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum F h (j + 1) = ∑ s, rd_dsum F (s :: h) j := by
  simp only [rd_dsum, rd_paths, Finset.sum_map, Function.Embedding.coeFn_mk, Finset.sum_product,
    List.append_assoc, List.singleton_append]
  exact Finset.sum_comm

/-- Splitting the distance: `∑_{a+b}` is the sum over distance-`a` nodes of distance-`b` sums. -/
theorem rd_dsum_add_len (F : List S → ℝ) (h : List S) (a b : ℕ) :
    rd_dsum F h (a + b) = rd_dsum (fun g => rd_dsum F g b) h a := by
  induction a generalizing h with
  | zero => simp [rd_dsum_zero]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by ring, rd_dsum_succ, rd_dsum_succ]
    exact Finset.sum_congr rfl fun s _ => ih (s :: h)

/-- Leaf-side recursion: the distance-`(j + 1)` sum is the distance-`j` sum of the sums over
immediate successors. -/
theorem rd_dsum_succ' (F : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum F h (j + 1) = rd_dsum (fun g => ∑ s, F (s :: g)) h j := by
  rw [rd_dsum_add_len]
  congr 1
  funext g
  rw [rd_dsum_succ]
  simp [rd_dsum_zero]

theorem rd_dsum_add (F G : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum (fun g => F g + G g) h j = rd_dsum F h j + rd_dsum G h j :=
  Finset.sum_add_distrib

theorem rd_dsum_sub (F G : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum (fun g => F g - G g) h j = rd_dsum F h j - rd_dsum G h j :=
  Finset.sum_sub_distrib _ _

theorem rd_dsum_neg (F : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum (fun g => -F g) h j = -rd_dsum F h j :=
  Finset.sum_neg_distrib _

theorem rd_dsum_const_mul (a : ℝ) (F : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum (fun g => a * F g) h j = a * rd_dsum F h j :=
  (Finset.mul_sum _ _ _).symm

theorem rd_dsum_finsetSum {ι : Type*} (A : Finset ι) (F : ι → List S → ℝ) (h : List S)
    (j : ℕ) : rd_dsum (fun g => ∑ i ∈ A, F i g) h j = ∑ i ∈ A, rd_dsum (F i) h j :=
  Finset.sum_comm

theorem rd_dsum_mono {F G : List S → ℝ} (hFG : ∀ g, F g ≤ G g) (h : List S) (j : ℕ) :
    rd_dsum F h j ≤ rd_dsum G h j :=
  Finset.sum_le_sum fun _ _ => hFG _

theorem rd_dsum_nonneg {F : List S → ℝ} (hF : ∀ g, 0 ≤ F g) (h : List S) (j : ℕ) :
    0 ≤ rd_dsum F h j :=
  Finset.sum_nonneg fun _ _ => hF _

theorem rd_dsum_congr {F G : List S → ℝ} (hFG : ∀ g, F g = G g) (h : List S) (j : ℕ) :
    rd_dsum F h j = rd_dsum G h j := by
  rw [funext hFG]

theorem rd_abs_dsum_le (F : List S → ℝ) (h : List S) (j : ℕ) :
    |rd_dsum F h j| ≤ rd_dsum (fun g => |F g|) h j :=
  Finset.abs_sum_le_sum_abs _ _

/-- A single descendant is bounded by the sum (nonnegative summands). -/
theorem rd_le_dsum {F : List S → ℝ} (hF : ∀ g, 0 ≤ F g) {h l : List S} {j : ℕ}
    (hl : l.length = j) : F (l ++ h) ≤ rd_dsum F h j :=
  Finset.single_le_sum (f := fun l => F (l ++ h)) (fun _ _ => hF _)
    ((rd_mem_paths j l).2 hl)

/-- Strict monotonicity of the distance-`j` sum. -/
theorem rd_dsum_lt {F G : List S → ℝ} (hFG : ∀ g, F g ≤ G g) {h l : List S} {j : ℕ}
    (hl : l.length = j) (hlt : F (l ++ h) < G (l ++ h)) : rd_dsum F h j < rd_dsum G h j :=
  Finset.sum_lt_sum (fun _ _ => hFG _) ⟨l, (rd_mem_paths j l).2 hl, hlt⟩

/-- The date sum of the indicator of a node `n`. -/
theorem rd_dsum_ite [DecidableEq S] (n : List S) (a : ℝ) (j : ℕ) :
    rd_dsum (fun g => if g = n then a else 0) [] j = if n.length = j then a else 0 := by
  simp [rd_dsum, rd_mem_paths]

/-- The descendants of `h` at distance `j` are among the date-`(len h + j)` nodes. -/
theorem rd_dsum_le_root {F : List S → ℝ} (hF : ∀ g, 0 ≤ F g) (h : List S) (j : ℕ) :
    rd_dsum F h j ≤ rd_dsum F [] (h.length + j) := by
  rw [rd_dsum_add_len]
  have := rd_le_dsum (F := fun g => rd_dsum F g j) (fun g => rd_dsum_nonneg hF g j)
    (h := []) (l := h) rfl
  simpa using this

/-- A function supported on the subtree of `h` has date sums equal to its subtree sums. -/
theorem rd_dsum_subtree {G : List S → ℝ} {h : List S} (hG : ∀ g, ¬ h <:+ g → G g = 0)
    (j : ℕ) : rd_dsum G [] (h.length + j) = rd_dsum G h j := by
  rw [rd_dsum_add_len, rd_dsum]
  simp only [List.append_nil]
  rw [Finset.sum_eq_single_of_mem h ((rd_mem_paths _ h).2 rfl)]
  · intro l hl hlh
    rw [rd_mem_paths] at hl
    refine Finset.sum_eq_zero fun l' _ => hG _ ?_
    rintro ⟨t, ht⟩
    have hlen : t.length = l'.length := by
      have := congrArg List.length ht
      simp only [List.length_append] at this
      omega
    exact hlh (List.append_inj ht hlen).2.symm

/-- A function supported on the subtree of `h` has zero date sums before the date of `h`. -/
theorem rd_dsum_subtree_early {G : List S → ℝ} {h : List S} (hG : ∀ g, ¬ h <:+ g → G g = 0)
    {t : ℕ} (ht : t < h.length) : rd_dsum G [] t = 0 := by
  refine Finset.sum_eq_zero fun l hl => hG _ ?_
  rw [rd_mem_paths] at hl
  intro hs
  have := hs.length_le
  simp only [List.append_nil] at this
  omega

/-- The probabilities on the event tree: `Pr(sᵗ) > 0`, `Pr(s⁰) = 1`, and
`∑_{s} Pr(s :: h) = Pr(h)`. -/
structure RDTree (S : Type*) [Fintype S] where
  /-- The unconditional probability `Pr(sᵗ)`. -/
  Pr : List S → ℝ
  /-- Every node has positive probability. -/
  pos : ∀ h, 0 < Pr h
  /-- `Pr(s⁰) = 1`. -/
  root : Pr [] = 1
  /-- Consistency of the probabilities of successors. -/
  cons : ∀ h, ∑ s, Pr (s :: h) = Pr h

/-- The probabilities of the descendants at distance `j` sum to the probability of the node. -/
theorem rd_dsum_Pr (T : RDTree S) (h : List S) (j : ℕ) : rd_dsum T.Pr h j = T.Pr h := by
  induction j generalizing h with
  | zero => exact rd_dsum_zero _ _
  | succ j ih =>
    rw [rd_dsum_succ]
    simp only [ih, T.cons]

/-- The uniform tree: every shock has conditional probability `1 / |S|`. -/
noncomputable def rd_uniformTree (S : Type*) [Fintype S] [Nonempty S] : RDTree S where
  Pr h := ((Fintype.card S : ℝ)⁻¹) ^ h.length
  pos h := pow_pos (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)) _
  root := by simp
  cons h := by
    have hc : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [List.length_cons, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_succ]
    field_simp

/-- The conditional probability `Pr(s | h) = Pr(s :: h) / Pr(h)`. -/
noncomputable def rd_condPr (T : RDTree S) (h : List S) (s : S) : ℝ := T.Pr (s :: h) / T.Pr h

/-- Conditional probabilities sum to one. -/
theorem rd_condPr_sum (T : RDTree S) (h : List S) : ∑ s, rd_condPr T h s = 1 := by
  simp only [rd_condPr, div_eq_mul_inv, ← Finset.sum_mul, T.cons]
  exact mul_inv_cancel₀ (T.pos h).ne'

/-- The conditional expectation `E_t[X_{t+j}]` at the date-`t` node `h`. -/
noncomputable def rd_condE (T : RDTree S) (X : List S → ℝ) (h : List S) (j : ℕ) : ℝ :=
  (T.Pr h)⁻¹ * rd_dsum (fun g => T.Pr g * X g) h j

/-- The unconditional expectation `E[X_t]` is the conditional one at the root. -/
theorem rd_condE_root (T : RDTree S) (X : List S → ℝ) (t : ℕ) :
    rd_condE T X [] t = rd_dsum (fun g => T.Pr g * X g) [] t := by
  simp [rd_condE, T.root]

/-- One-step conditional expectation as a sum over successors. -/
theorem rd_condE_one (T : RDTree S) (X : List S → ℝ) (h : List S) :
    rd_condE T X h 1 = ∑ s, rd_condPr T h s * X (s :: h) := by
  rw [rd_condE, rd_dsum_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rd_dsum_zero, rd_condPr]
  ring

/-- Bounded adapted processes (`L^∞`). -/
def rd_Bdd (x : List S → ℝ) : Prop := ∃ M, ∀ h, |x h| ≤ M

/-- Nonnegative bounded processes (`L^∞₊`). -/
def rd_LinfPos (c : List S → ℝ) : Prop := rd_Bdd c ∧ ∀ h, 0 ≤ c h

/-- Summable processes (`L¹`): `∑ₜ ∑_{sᵗ} |x(sᵗ)| < ∞`. -/
def rd_L1 (q : List S → ℝ) : Prop := Summable (fun t => rd_dsum (fun g => |q g|) [] t)

/-- An `L¹` process times a bounded one is summable in absolute value over dates. -/
theorem rd_L1_mul_abs {q x : List S → ℝ} (hq : rd_L1 q) (hx : rd_Bdd x) :
    Summable (fun t => rd_dsum (fun g => |q g * x g|) [] t) := by
  obtain ⟨M, hM⟩ := hx
  refine Summable.of_nonneg_of_le (fun t => rd_dsum_nonneg (fun g => abs_nonneg _) _ _)
    (fun t => ?_) (hq.mul_left M)
  rw [← rd_dsum_const_mul]
  refine rd_dsum_mono (fun g => ?_) _ _
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM g) (abs_nonneg _)

/-- An `L¹` process times a bounded one has summable date sums. -/
theorem rd_L1_mul {q x : List S → ℝ} (hq : rd_L1 q) (hx : rd_Bdd x) :
    Summable (fun t => rd_dsum (fun g => q g * x g) [] t) :=
  Summable.of_norm_bounded (rd_L1_mul_abs hq hx) fun t => by
    rw [Real.norm_eq_abs]
    exact rd_abs_dsum_le _ _ _

/-- The date sums of an `L¹` process times a bounded one tend to zero. -/
theorem rd_L1_mul_tendsto {q x : List S → ℝ} (hq : rd_L1 q) (hx : rd_Bdd x) :
    Tendsto (fun t => rd_dsum (fun g => q g * x g) [] t) atTop (𝓝 0) :=
  (rd_L1_mul hq hx).tendsto_atTop_zero

omit [Fintype S] in
/-- The constant process `1` is bounded. -/
theorem rd_bdd_one : rd_Bdd (fun _ : List S => (1 : ℝ)) := ⟨1, fun _ => by simp⟩

/-- `L¹` processes have date sums tending to zero. -/
theorem rd_L1_tendsto {q : List S → ℝ} (hq : rd_L1 q) :
    Tendsto (fun t => rd_dsum q [] t) atTop (𝓝 0) := by
  simpa using rd_L1_mul_tendsto hq rd_bdd_one

omit [Fintype S] in
/-- Bounded processes are closed under sums, differences and scaling. -/
theorem rd_bdd_add {x z : List S → ℝ} (hx : rd_Bdd x) (hz : rd_Bdd z) :
    rd_Bdd (fun h => x h + z h) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hz
  exact ⟨M + N, fun h => (abs_add_le _ _).trans (add_le_add (hM h) (hN h))⟩

omit [Fintype S] in
theorem rd_bdd_neg {x : List S → ℝ} (hx : rd_Bdd x) : rd_Bdd (fun h => -x h) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨M, fun h => by simpa using hM h⟩

omit [Fintype S] in
theorem rd_bdd_sub {x z : List S → ℝ} (hx : rd_Bdd x) (hz : rd_Bdd z) :
    rd_Bdd (fun h => x h - z h) := by
  simpa [sub_eq_add_neg] using rd_bdd_add hx (rd_bdd_neg hz)

omit [Fintype S] in
theorem rd_bdd_const_mul (a : ℝ) {x : List S → ℝ} (hx : rd_Bdd x) :
    rd_Bdd (fun h => a * x h) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨|a| * M, fun h => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM h) (abs_nonneg a)⟩

/-- A utility functional is strictly increasing on `L^∞₊`. -/
def rd_StrictIncr (U : (List S → ℝ) → ℝ) : Prop :=
  ∀ c c', rd_LinfPos c → rd_LinfPos c' → (∀ h, c h ≤ c' h) → c ≠ c' → U c < U c'

/-- A utility functional is (weakly) increasing on `L^∞₊`. -/
def rd_Mono (U : (List S → ℝ) → ℝ) : Prop :=
  ∀ c c', rd_LinfPos c → rd_LinfPos c' → (∀ h, c h ≤ c' h) → U c ≤ U c'

omit [Fintype S] in
/-- Strictly increasing utility functionals are increasing. -/
theorem rd_mono_of_strictIncr {U : (List S → ℝ) → ℝ} (hU : rd_StrictIncr U) : rd_Mono U := by
  intro c c' hc hc' hle
  by_cases h : c = c'
  · rw [h]
  · exact (hU c c' hc hc' hle h).le

/-- **(13.1)** (Miao, p. 416). The discounted expected utility
`U(c) = ∑ₜ ∑_{sᵗ} βᵗ u(cₜ(sᵗ)) Pr(sᵗ)`. -/
noncomputable def rd_EU (T : RDTree S) (β : ℝ) (u : ℝ → ℝ) (c : List S → ℝ) : ℝ :=
  ∑' t, β ^ t * rd_dsum (fun g => T.Pr g * u (c g)) [] t

/-- The date-`t` expected utility is bounded by `K` when `|u ∘ c| ≤ K`. -/
theorem rd_abs_dsum_Pr_le (T : RDTree S) {X : List S → ℝ} {K : ℝ} (hX : ∀ g, |X g| ≤ K)
    (h : List S) (j : ℕ) : |rd_dsum (fun g => T.Pr g * X g) h j| ≤ K * T.Pr h := by
  refine (rd_abs_dsum_le _ _ _).trans ?_
  rw [← rd_dsum_Pr T h j, ← rd_dsum_const_mul]
  refine rd_dsum_mono (fun g => ?_) _ _
  rw [abs_mul, abs_of_pos (T.pos g), mul_comm]
  exact mul_le_mul_of_nonneg_right (hX g) (T.pos g).le

/-- The series (13.1) converges when `u ∘ c` is bounded and `0 ≤ β < 1`. -/
theorem rd_EU_summable (T : RDTree S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (u : ℝ → ℝ)
    {c : List S → ℝ} {K : ℝ} (hK : ∀ g, |u (c g)| ≤ K) :
    Summable (fun t => β ^ t * rd_dsum (fun g => T.Pr g * u (c g)) [] t) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K)
    fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  have := rd_abs_dsum_Pr_le T hK [] t
  rw [T.root, mul_one] at this
  exact mul_le_mul_of_nonneg_left this (pow_nonneg hβ0 t)

omit [Fintype S] in
/-- A utility increasing on `[0, ∞)` is bounded on a bounded nonnegative plan. -/
theorem rd_abs_u_le {u : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) {c : List S → ℝ}
    (hc : rd_LinfPos c) : ∃ K, ∀ g, |u (c g)| ≤ K := by
  obtain ⟨⟨M, hM⟩, h0⟩ := hc
  refine ⟨|u 0| + |u M|, fun g => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM g)
  have hcM : c g ≤ M := (le_abs_self _).trans (hM g)
  have h1 : u 0 ≤ u (c g) := hu (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (h0 g)) (h0 g)
  have h2 : u (c g) ≤ u M := hu (Set.mem_Ici.2 (h0 g)) (Set.mem_Ici.2 hM0) hcM
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (u 0), abs_nonneg (u M)]
  · linarith [le_abs_self (u M), abs_nonneg (u 0)]

/-- **(13.1)** (Miao, p. 416, with Assumption 13.1.1's monotonicity). If `u` is strictly
increasing on `[0, ∞)` and `0 < β < 1`, the discounted expected utility is strictly increasing
on `L^∞₊`: raising consumption weakly everywhere and strictly somewhere raises utility. -/
theorem rd_eq_13_1 (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u : ℝ → ℝ}
    (hu : StrictMonoOn u (Set.Ici 0)) : rd_StrictIncr (rd_EU T β u) := by
  intro c c' hc hc' hle hne
  obtain ⟨K, hK⟩ := rd_abs_u_le hu.monotoneOn hc
  obtain ⟨K', hK'⟩ := rd_abs_u_le hu.monotoneOn hc'
  obtain ⟨h0, hh0⟩ := Function.ne_iff.1 hne
  have hlt : c h0 < c' h0 := lt_of_le_of_ne (hle h0) hh0
  have hule : ∀ g, T.Pr g * u (c g) ≤ T.Pr g * u (c' g) := fun g =>
    mul_le_mul_of_nonneg_left (hu.monotoneOn (Set.mem_Ici.2 (hc.2 g))
      (Set.mem_Ici.2 (hc'.2 g)) (hle g)) (T.pos g).le
  refine Summable.tsum_lt_tsum (i := h0.length) (fun t => ?_) ?_
    (rd_EU_summable T hβ0.le hβ1 u hK) (rd_EU_summable T hβ0.le hβ1 u hK')
  · exact mul_le_mul_of_nonneg_left (rd_dsum_mono hule _ _) (pow_nonneg hβ0.le t)
  · refine mul_lt_mul_of_pos_left ?_ (pow_pos hβ0 _)
    refine rd_dsum_lt hule (l := h0) (by simp) ?_
    simp only [List.append_nil]
    exact mul_lt_mul_of_pos_left (hu (Set.mem_Ici.2 (hc.2 h0)) (Set.mem_Ici.2 (hc'.2 h0)) hlt)
      (T.pos h0)

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sequential trading: securities, budgets, portfolio constraints and arbitrage

Miao, §13.4, pp. 424–429.

`J` securities are traded at every node. `p h : J → ℝ` is the price vector at node `h` and
`f (s :: h) : J → ℝ` is the payoff, at the successor `s :: h`, of the securities bought at `h`.
A trading strategy is `θ : List S → J → ℝ`, and `θm1` is the initial portfolio `θ_{−1}`.

* `rd_Budget` is the budget constraint (13.11); `eq_13_11` gives the book's two lines
  (13.11a) and (13.11b). `rd_fz` and `rd_prev` are the payoff and the portfolio carried into a
  node (at the root, (13.11b) values `θ_{−1}` at `p₀`).
* Arrow securities: `rd_arrowPayoff` and the budget (13.12), `eq_13_12`.
* Ponzi schemes `rd_Ponzi`, arbitrage `rd_Arb`, one-period arbitrage `rd_OneArb`: a Ponzi scheme
  is an arbitrage (`rd_ponzi_arb`); no arbitrage implies no one-period arbitrage
  (`rd_noArb_noOneArb`, also on the recession sets, `rd_noArbOn_noOneArbOn`); the converse
  fails (`rd_oneArb_converse_fails`: a riskless bond rolled over forever).
* The debt (13.13), borrowing (13.14) and short-sales (13.15) constraints `rd_ThetaDC`,
  `rd_ThetaBC`, `rd_ThetaSC`, the recession set `rd_Rec`, and its three computations
  `rd_rec_DC`, `rd_rec_BC`, `rd_rec_SC` (pp. 429–430).
* **Theorem 13.4.1** (`theorem_13_4_1`, Exercise 13.3 `ex_13_3`): an agent with strictly
  increasing utility who has an optimum has no arbitrage on the recession set. The proof adds
  the arbitrage to the optimal strategy and consumes the (truncated) surplus, which keeps
  consumption bounded.
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J : Type*} [Fintype S] [Fintype J]

omit [Fintype S] in
/-- The payoff vector received at a node: `f_t(sᵗ)` for `t > 0`, and `p₀(s⁰)` at the root, as in
(13.11b). -/
def rd_fz (p f : List S → J → ℝ) : List S → J → ℝ
  | [] => p []
  | s :: h => f (s :: h)

omit [Fintype S] in
/-- The portfolio carried into a node: `θ_{t−1}(sᵗ⁻)`, and `θ_{−1}` at the root. -/
def rd_prev (θ : List S → J → ℝ) (θm1 : J → ℝ) : List S → J → ℝ
  | [] => θm1
  | _ :: h => θ h

/-- The net cash flow of a strategy at a node: `f_t · θ_{t−1} − p_t · θ_t`. -/
def rd_net (p f : List S → J → ℝ) (θm1 : J → ℝ) (θ : List S → J → ℝ) (h : List S) : ℝ :=
  rd_fz p f h ⬝ᵥ rd_prev θ θm1 h - p h ⬝ᵥ θ h

/-- The sequential budget constraints (13.11). -/
def rd_Budget (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ) (c : List S → ℝ)
    (θ : List S → J → ℝ) : Prop :=
  ∀ h, c h + p h ⬝ᵥ θ h ≤ rd_fz p f h ⬝ᵥ rd_prev θ θm1 h + y h

omit [Fintype S] in
/-- **(13.11)** (Miao, p. 425). The budget constraints are (13.11a) at every node `sᵗ`,
`t > 0`, and (13.11b) at the root. -/
theorem eq_13_11 (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ) (c : List S → ℝ)
    (θ : List S → J → ℝ) :
    rd_Budget p f y θm1 c θ ↔
      (∀ s h, c (s :: h) + p (s :: h) ⬝ᵥ θ (s :: h) ≤ f (s :: h) ⬝ᵥ θ h + y (s :: h)) ∧
        c [] + p [] ⬝ᵥ θ [] ≤ p [] ⬝ᵥ θm1 + y [] := by
  constructor
  · intro hB
    exact ⟨fun s h => hB (s :: h), hB []⟩
  · rintro ⟨h1, h0⟩ h
    cases h with
    | nil => exact h0
    | cons s h => exact h1 s h

omit [Fintype S] in
/-- The budget constraint says consumption is at most net cash flow plus endowment. -/
theorem rd_budget_iff_net (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ)
    (c : List S → ℝ) (θ : List S → J → ℝ) :
    rd_Budget p f y θm1 c θ ↔ ∀ h, c h ≤ rd_net p f θm1 θ h + y h := by
  refine forall_congr' fun h => ?_
  rw [rd_net]
  constructor <;> intro H <;> linarith

omit [Fintype S] [Fintype J] in
/-- The carried-in portfolio is additive. -/
theorem rd_prev_add (θ θ' : List S → J → ℝ) (a b : J → ℝ) (h : List S) :
    rd_prev (θ + θ') (a + b) h = rd_prev θ a h + rd_prev θ' b h := by
  cases h with
  | nil => rfl
  | cons s h => rfl

omit [Fintype S] [Fintype J] in
/-- The carried-in portfolio scales. -/
theorem rd_prev_smul (r : ℝ) (θ : List S → J → ℝ) (a : J → ℝ) (h : List S) :
    rd_prev (r • θ) (r • a) h = r • rd_prev θ a h := by
  cases h with
  | nil => rfl
  | cons s h => rfl

omit [Fintype S] in
/-- Net cash flows are additive in the strategy. -/
theorem rd_net_add (p f : List S → J → ℝ) (θ θ' : List S → J → ℝ) (a b : J → ℝ)
    (h : List S) : rd_net p f (a + b) (θ + θ') h = rd_net p f a θ h + rd_net p f b θ' h := by
  simp only [rd_net, rd_prev_add, dotProduct_add, Pi.add_apply]
  ring

omit [Fintype S] in
/-- **Arrow securities** (Miao, p. 425). The `S` Arrow securities bought at `h` pay one unit at
`(h, s)` for the security indexed by `s`, and zero elsewhere. -/
def rd_arrowPayoff [DecidableEq S] : List S → S → ℝ
  | [] => fun _ => 0
  | s :: _ => fun j => if j = s then 1 else 0

omit [Fintype S] in
/-- The holding of Arrow securities carried into a node: `a_{t−1}(sᵗ⁻, sₜ)`, and the initial
holding `a_{−1}(s⁰)` at the root. -/
def rd_arrowIn (a : List S → S → ℝ) (a0 : ℝ) : List S → ℝ
  | [] => a0
  | s :: h => a h s

/-- The budget constraint (13.12) with Arrow securities, prices `Q(s′ | sᵗ)` and holdings
`a_t(sᵗ, s′)`. -/
def rd_ArrowBudget (Q : List S → S → ℝ) (y : List S → ℝ) (a0 : ℝ) (c : List S → ℝ)
    (a : List S → S → ℝ) : Prop :=
  ∀ h, c h + ∑ s', Q h s' * a h s' ≤ rd_arrowIn a a0 h + y h

/-- **(13.12)** (Miao, p. 425). With the `S` Arrow securities as the traded securities
(`J = S`, payoffs `rd_arrowPayoff`, prices `Q`), the sequential budget (13.11) is (13.12), the
initial Arrow holding being the value `a_{−1}(s⁰) = Q(· | s⁰) · θ_{−1}`. -/
theorem eq_13_12 [DecidableEq S] (Q : List S → S → ℝ) (y : List S → ℝ) (θm1 : S → ℝ)
    (c : List S → ℝ) (a : List S → S → ℝ) :
    rd_Budget Q rd_arrowPayoff y θm1 c a ↔ rd_ArrowBudget Q y (Q [] ⬝ᵥ θm1) c a := by
  refine forall_congr' fun h => ?_
  cases h with
  | nil => rfl
  | cons s h =>
    simp [rd_fz, rd_prev, rd_arrowIn, rd_arrowPayoff, dotProduct]

/-- A **Ponzi scheme** (Miao, p. 426): `p₀ · Δ₀ < 0` and `p_t · Δ_t = f_t · Δ_{t−1}` for `t > 0`. -/
def rd_Ponzi (p f : List S → J → ℝ) (Δ : List S → J → ℝ) : Prop :=
  p [] ⬝ᵥ Δ [] < 0 ∧ ∀ s h, p (s :: h) ⬝ᵥ Δ (s :: h) = f (s :: h) ⬝ᵥ Δ h

/-- An **arbitrage opportunity** (Miao, p. 428): `p₀ · θ₀ ≤ 0`, `f_t · θ_{t−1} − p_t · θ_t ≥ 0`,
with at least one strict inequality (the net cash flow with `θ_{−1} = 0`). -/
def rd_Arb (p f : List S → J → ℝ) (θ : List S → J → ℝ) : Prop :=
  (∀ h, 0 ≤ rd_net p f 0 θ h) ∧ ∃ h, 0 < rd_net p f 0 θ h

/-- An arbitrage within a set of trading strategies. -/
def rd_ArbOn (p f : List S → J → ℝ) (Θ' : Set (List S → J → ℝ)) : Prop :=
  ∃ θ ∈ Θ', rd_Arb p f θ

/-- A **one-period arbitrage** portfolio at `h` (Miao, p. 428): `p_t · v ≤ 0`,
`f_{t+1}(s :: h) · v ≥ 0` for all `s`, with at least one strict inequality. -/
def rd_OneArb (p f : List S → J → ℝ) (h : List S) (v : J → ℝ) : Prop :=
  p h ⬝ᵥ v ≤ 0 ∧ (∀ s, 0 ≤ f (s :: h) ⬝ᵥ v) ∧ (p h ⬝ᵥ v < 0 ∨ ∃ s, 0 < f (s :: h) ⬝ᵥ v)

/-- A one-period arbitrage at `h` by a strategy in `Θ'`. -/
def rd_OneArbOn (p f : List S → J → ℝ) (Θ' : Set (List S → J → ℝ)) (h : List S) : Prop :=
  ∃ θ ∈ Θ', rd_OneArb p f h (θ h)

omit [Fintype S] in
/-- Miao, p. 428: "By definition, a Ponzi scheme is an arbitrage opportunity." -/
theorem rd_ponzi_arb (p f : List S → J → ℝ) (Δ : List S → J → ℝ) (hΔ : rd_Ponzi p f Δ) :
    rd_Arb p f Δ := by
  have hn : ∀ h, rd_net p f 0 Δ h = if h = [] then -(p [] ⬝ᵥ Δ []) else 0 := by
    intro h
    cases h with
    | nil => simp [rd_net, rd_fz, rd_prev]
    | cons s h =>
      simp only [rd_net, rd_fz, rd_prev, hΔ.2 s h, sub_self, reduceCtorEq, ↓reduceIte]
  refine ⟨fun h => ?_, [], ?_⟩
  · rw [hn]
    split_ifs
    · linarith [hΔ.1]
    · exact le_rfl
  · rw [hn]
    simp only [↓reduceIte]
    linarith [hΔ.1]

omit [Fintype S] [Fintype J] in
/-- The strategy that holds `v` at the node `h` only. -/
def rd_loc [DecidableEq S] (v : J → ℝ) (h : List S) : List S → J → ℝ :=
  fun g => if g = h then v else 0

omit [Fintype S] in
/-- A one-period arbitrage at `h`, held at `h` only, is an arbitrage opportunity. -/
theorem rd_arb_loc [DecidableEq S] (p f : List S → J → ℝ) (h : List S) (v : J → ℝ)
    (hv : rd_OneArb p f h v) : rd_Arb p f (rd_loc v h) := by
  obtain ⟨hp, hf, hs⟩ := hv
  have hprev : ∀ g, g ≠ h → rd_net p f 0 (rd_loc v h) g =
      rd_fz p f g ⬝ᵥ rd_prev (rd_loc v h) 0 g := by
    intro g hg
    simp [rd_net, rd_loc, hg]
  have hat : rd_net p f 0 (rd_loc v h) h = -(p h ⬝ᵥ v) := by
    cases h with
    | nil => simp [rd_net, rd_loc, rd_prev]
    | cons s g =>
      have : g ≠ s :: g := fun e => by simpa using congrArg List.length e
      simp [rd_net, rd_loc, rd_prev, this]
  have hchild : ∀ s, rd_net p f 0 (rd_loc v h) (s :: h) = f (s :: h) ⬝ᵥ v := by
    intro s
    have : s :: h ≠ h := fun e => by simpa using congrArg List.length e
    rw [hprev _ this]
    simp [rd_fz, rd_prev, rd_loc]
  refine ⟨fun g => ?_, ?_⟩
  · by_cases hg : g = h
    · rw [hg, hat]
      linarith
    · rw [hprev g hg]
      cases g with
      | nil => simp [rd_prev]
      | cons s g' =>
        by_cases hg' : g' = h
        · subst hg'
          simpa [rd_fz, rd_prev, rd_loc] using hf s
        · simp [rd_prev, rd_loc, hg']
  · rcases hs with hs | ⟨s, hs⟩
    · exact ⟨h, by rw [hat]; linarith⟩
    · exact ⟨s :: h, by rw [hchild]; exact hs⟩

omit [Fintype S] in
/-- Miao, p. 428: "If there is no arbitrage, then there is no one-period arbitrage at any
node." -/
theorem rd_noArb_noOneArb (p f : List S → J → ℝ)
    (hna : ¬ ∃ θ, rd_Arb p f θ) (h : List S) : ¬ rd_OneArbOn p f Set.univ h := by
  classical
  rintro ⟨θ, -, hθ⟩
  exact hna ⟨_, rd_arb_loc p f h _ hθ⟩

omit [Fintype S] in
/-- The same on any set of strategies that contains the localisation of its members (as the
recession sets of `Θ_DC`, `Θ_BC`, `Θ_SC` do): no arbitrage on `Θ'` implies no one-period
arbitrage on `Θ'`. -/
theorem rd_noArbOn_noOneArbOn [DecidableEq S] (p f : List S → J → ℝ)
    (Θ' : Set (List S → J → ℝ)) (hloc : ∀ θ ∈ Θ', ∀ h, rd_loc (θ h) h ∈ Θ')
    (hna : ¬ rd_ArbOn p f Θ') (h : List S) : ¬ rd_OneArbOn p f Θ' h := by
  rintro ⟨θ, hθ, harb⟩
  exact hna ⟨_, hloc θ hθ h, rd_arb_loc p f h _ harb⟩

/-- Miao, p. 428: "The converse may not be true." A riskless bond with price and payoff `1`
admits no one-period arbitrage at any node, but rolling over one unit of debt forever is an
arbitrage (a Ponzi scheme). -/
theorem rd_oneArb_converse_fails :
    (∀ h, ¬ rd_OneArbOn (S := Unit) (J := Unit) (fun _ _ => 1) (fun _ _ => 1) Set.univ h) ∧
      ∃ θ, rd_Arb (S := Unit) (J := Unit) (fun _ _ => 1) (fun _ _ => 1) θ := by
  refine ⟨fun h => ?_, fun _ _ => -1, rd_ponzi_arb _ _ _ ?_⟩
  · rintro ⟨θ, -, hp, hf, hs⟩
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, one_mul] at hp hf hs
    have h1 := hf ()
    rcases hs with hs | ⟨_, hs⟩ <;> linarith
  · simp [rd_Ponzi, dotProduct]

/-- The **debt constraints** (13.13): `f_{t+1}(sᵗ⁺¹) · θ_t(sᵗ) ≥ −D̄_{t+1}(sᵗ⁺¹)`. -/
def rd_ThetaDC (f : List S → J → ℝ) (Dbar : List S → ℝ) : Set (List S → J → ℝ) :=
  {θ | ∀ h s, -Dbar (s :: h) ≤ f (s :: h) ⬝ᵥ θ h}

/-- The **borrowing constraints** (13.14): `p_t(sᵗ) · θ_t(sᵗ) ≥ −B̄_t(sᵗ)`. -/
def rd_ThetaBC (p : List S → J → ℝ) (Bbar : List S → ℝ) : Set (List S → J → ℝ) :=
  {θ | ∀ h, -Bbar h ≤ p h ⬝ᵥ θ h}

omit [Fintype S] [Fintype J] in
/-- The **short-sales constraints** (13.15): `θ_t(sᵗ) ≥ −h̄_t(sᵗ)`. -/
def rd_ThetaSC (hbar : List S → J → ℝ) : Set (List S → J → ℝ) :=
  {θ | ∀ h j, -hbar h j ≤ θ h j}

omit [Fintype S] [Fintype J] in
/-- The **recession set** `R(Θᵃ) = {θ : Θᵃ + λθ ⊂ Θᵃ, ∀ λ > 0}` (Miao, p. 428). -/
def rd_Rec (Θa : Set (List S → J → ℝ)) : Set (List S → J → ℝ) :=
  {θ | ∀ lam : ℝ, 0 < lam → ∀ θ' ∈ Θa, θ' + lam • θ ∈ Θa}

/-- If `−D ≤ λx` for all `λ > 0` then `x ≥ 0`. -/
theorem rd_nonneg_of_forall_lam {D x : ℝ} (hD : ∀ lam : ℝ, 0 < lam → -D ≤ lam * x) :
    0 ≤ x := by
  by_contra hx
  push Not at hx
  have hpos : 0 < (|D| + 1) / (-x) := div_pos (by positivity) (by linarith)
  have := hD _ hpos
  have hx0 : x ≠ 0 := hx.ne
  have e : (|D| + 1) / (-x) * x = -(|D| + 1) := by
    field_simp
  rw [e] at this
  linarith [le_abs_self D]

omit [Fintype S] in
/-- Miao, p. 429: `R(Θ_DC(p, f)) = {θ : f_{t+1} · θ_t ≥ 0}` (debt limits `D̄ ≥ 0`). -/
theorem rd_rec_DC (f : List S → J → ℝ) {Dbar : List S → ℝ} (hD : ∀ h, 0 ≤ Dbar h) :
    rd_Rec (rd_ThetaDC f Dbar) = {θ | ∀ h s, 0 ≤ f (s :: h) ⬝ᵥ θ h} := by
  ext θ
  simp only [rd_Rec, rd_ThetaDC, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  constructor
  · intro H h s
    refine rd_nonneg_of_forall_lam (D := Dbar (s :: h)) fun lam hlam => ?_
    have := H lam hlam 0 (fun h' s' => by simpa using hD (s' :: h')) h s
    simpa using this
  · intro H lam hlam θ' hθ' h s
    have := mul_nonneg hlam.le (H h s)
    linarith [hθ' h s]

omit [Fintype S] in
/-- Miao, p. 429: `R(Θ_BC(p, f)) = {θ : p_t · θ_t ≥ 0}` (borrowing limits `B̄ ≥ 0`). -/
theorem rd_rec_BC (p : List S → J → ℝ) {Bbar : List S → ℝ} (hB : ∀ h, 0 ≤ Bbar h) :
    rd_Rec (rd_ThetaBC p Bbar) = {θ | ∀ h, 0 ≤ p h ⬝ᵥ θ h} := by
  ext θ
  simp only [rd_Rec, rd_ThetaBC, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  constructor
  · intro H h
    refine rd_nonneg_of_forall_lam (D := Bbar h) fun lam hlam => ?_
    have := H lam hlam 0 (fun h' => by simpa using hB h') h
    simpa using this
  · intro H lam hlam θ' hθ' h
    have := mul_nonneg hlam.le (H h)
    linarith [hθ' h]

omit [Fintype S] [Fintype J] in
/-- Miao, p. 430: `R(Θ_SC(p, f)) = {θ : θ_t ≥ 0}` (short-sales limits `h̄ ≥ 0`). -/
theorem rd_rec_SC {hbar : List S → J → ℝ} (hh : ∀ h j, 0 ≤ hbar h j) :
    rd_Rec (rd_ThetaSC hbar) = {θ | ∀ h j, 0 ≤ θ h j} := by
  ext θ
  simp only [rd_Rec, rd_ThetaSC, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro H h j
    refine rd_nonneg_of_forall_lam (D := hbar h j) fun lam hlam => ?_
    have := H lam hlam 0 (fun h' j' => by simpa using hh h' j') h j
    simpa using this
  · intro H lam hlam θ' hθ' h j
    have := mul_nonneg hlam.le (H h j)
    linarith [hθ' h j]

omit [Fintype S] in
/-- The recession set of the debt constraints contains the localisations of its members. -/
theorem rd_loc_mem_recDC [DecidableEq S] (f : List S → J → ℝ) {θ : List S → J → ℝ}
    (hθ : ∀ h s, 0 ≤ f (s :: h) ⬝ᵥ θ h) (h : List S) :
    ∀ g s, 0 ≤ f (s :: g) ⬝ᵥ rd_loc (θ h) h g := by
  intro g s
  by_cases hg : g = h
  · subst hg
    simpa [rd_loc] using hθ g s
  · simp [rd_loc, hg]

omit [Fintype S] in
/-- The recession set of the borrowing constraints contains the localisations of its
members. -/
theorem rd_loc_mem_recBC [DecidableEq S] (p : List S → J → ℝ) {θ : List S → J → ℝ}
    (hθ : ∀ h, 0 ≤ p h ⬝ᵥ θ h) (h : List S) : ∀ g, 0 ≤ p g ⬝ᵥ rd_loc (θ h) h g := by
  intro g
  by_cases hg : g = h
  · subst hg
    simpa [rd_loc] using hθ g
  · simp [rd_loc, hg]

/-- Agent `i`'s sequential problem: bounded nonnegative consumption, the budget (13.11), and a
strategy in the admissible set `Θa`. -/
def rd_SeqFeas (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ)
    (Θa : Set (List S → J → ℝ)) (c : List S → ℝ) (θ : List S → J → ℝ) : Prop :=
  rd_LinfPos c ∧ rd_Budget p f y θm1 c θ ∧ θ ∈ Θa

omit [Fintype S] [Fintype J] in
/-- `(c, θ)` solves the problem of maximising `U` over the plans satisfying `Feas`. -/
def rd_Solves {X : Type*} (U : (List S → ℝ) → ℝ) (Feas : (List S → ℝ) → X → Prop)
    (c : List S → ℝ) (θ : X) : Prop :=
  Feas c θ ∧ ∀ c' θ', Feas c' θ' → U c' ≤ U c

omit [Fintype S] in
/-- **Theorem 13.4.1** (Miao, p. 429). If `U` is strictly increasing and agent `i`'s problem of
maximising `U` subject to (13.11) and `θ ∈ Θᵃ(p, f)` has a solution, then there is no arbitrage
opportunity on the recession set `R(Θᵃ(p, f))`. -/
theorem theorem_13_4_1 (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ)
    (Θa : Set (List S → J → ℝ)) {U : (List S → ℝ) → ℝ} (hU : rd_StrictIncr U)
    {c : List S → ℝ} {θ : List S → J → ℝ} (hsol : rd_Solves U (rd_SeqFeas p f y θm1 Θa) c θ) :
    ¬ rd_ArbOn p f (rd_Rec Θa) := by
  rintro ⟨θ', hrec, hnn, h0, hpos⟩
  obtain ⟨⟨⟨M, hM⟩, hc0⟩, hB, hΘ⟩ := hsol.1
  set c'' : List S → ℝ := fun h => c h + min (rd_net p f 0 θ' h) 1 with hc''
  have hmin0 : ∀ h, 0 ≤ min (rd_net p f 0 θ' h) 1 := fun h => le_min (hnn h) zero_le_one
  have hfeas : rd_SeqFeas p f y θm1 Θa c'' (θ + θ') := by
    refine ⟨⟨⟨M + 1, fun h => ?_⟩, fun h => add_nonneg (hc0 h) (hmin0 h)⟩, ?_, ?_⟩
    · rw [hc'', abs_le]
      have h1 := min_le_right (rd_net p f 0 θ' h) 1
      have := abs_le.1 (hM h)
      constructor <;> linarith [hmin0 h]
    · rw [rd_budget_iff_net]
      intro h
      have hn := rd_net_add p f θ θ' θm1 0 h
      rw [add_zero] at hn
      rw [hn]
      have := (rd_budget_iff_net p f y θm1 c θ).1 hB h
      have := min_le_left (rd_net p f 0 θ' h) 1
      simp only [hc'']
      linarith
    · simpa using hrec 1 one_pos θ hΘ
  have hlt : U c < U c'' := by
    refine hU c c'' hsol.1.1 hfeas.1 (fun h => le_add_of_nonneg_right (hmin0 h)) ?_
    intro he
    have := congrFun he h0
    simp only [hc'', left_eq_add] at this
    have : 0 < min (rd_net p f 0 θ' h0) 1 := lt_min hpos one_pos
    linarith
  exact absurd (hsol.2 c'' (θ + θ') hfeas) (not_le.2 hlt)

omit [Fintype S] in
/-- **Exercise 13.3** (Miao, p. 452): prove Theorem 13.4.1. -/
theorem ex_13_3 (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ)
    (Θa : Set (List S → J → ℝ)) {U : (List S → ℝ) → ℝ} (hU : rd_StrictIncr U)
    {c : List S → ℝ} {θ : List S → J → ℝ} (hsol : rd_Solves U (rd_SeqFeas p f y θm1 Θa) c θ) :
    ¬ rd_ArbOn p f (rd_Rec Θa) :=
  theorem_13_4_1 p f y θm1 Θa hU hsol

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stiemke's lemma

Miao, proof of Theorem 13.4.2, p. 429, cites Stiemke's Lemma: a subspace `L ⊆ ℝᴷ` contains no
nonzero nonnegative vector iff there is a strictly positive `q ∈ ℝᴷ` orthogonal to `L`. It is
proved here from the compact–closed Hahn–Banach separation theorem, separating the simplex from
`L`.
-/

namespace Miao.CompleteMarkets

/-- The standard simplex `{v ≥ 0 : ∑ₖ vₖ = 1}` in `ℝᴷ`. -/
def rd_simplex (K : Type*) [Fintype K] : Set (K → ℝ) := {v | (∀ k, 0 ≤ v k) ∧ ∑ k, v k = 1}

variable {K : Type*} [Fintype K]

/-- The simplex is convex. -/
theorem rd_simplex_convex : Convex ℝ (rd_simplex K) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hf.1 x)) (mul_nonneg hb (hg.1 x))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hf.2, hg.2, mul_one,
      mul_one, hab]

/-- The simplex is compact. -/
theorem rd_simplex_compact : IsCompact (rd_simplex K) := by
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : K → ℝ)) (b := 1)) ?_ ?_
  · have : rd_simplex K = (⋂ k, {v : K → ℝ | 0 ≤ v k}) ∩ {v | ∑ k, v k = 1} := by
      ext v
      simp [rd_simplex]
    rw [this]
    exact (isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  · intro v hv
    refine ⟨fun k => hv.1 k, fun k => ?_⟩
    have := Finset.single_le_sum (f := v) (fun k _ => hv.1 k) (Finset.mem_univ k)
    rw [hv.2] at this
    exact this

/-- **Stiemke's Lemma** (Miao, p. 429). A subspace `L` of `ℝᴷ` contains no nonzero nonnegative
vector iff some strictly positive `q` is orthogonal to `L`. -/
theorem rd_stiemke (L : Submodule ℝ (K → ℝ)) :
    (∀ v ∈ L, (∀ k, 0 ≤ v k) → v = 0) ↔
      ∃ q : K → ℝ, (∀ k, 0 < q k) ∧ ∀ v ∈ L, ∑ k, q k * v k = 0 := by
  classical
  constructor
  · intro hL
    have hdisj : Disjoint (rd_simplex K) (L : Set (K → ℝ)) := by
      rw [Set.disjoint_left]
      intro v hv hvL
      have h0 := hL v hvL hv.1
      have := hv.2
      rw [h0] at this
      simp at this
    obtain ⟨φ, u, w, hu, huw, hw⟩ := geometric_hahn_banach_compact_closed rd_simplex_convex
      rd_simplex_compact L.convex (Submodule.closed_of_finiteDimensional L) hdisj
    have hw0 : w < 0 := by simpa using hw 0 L.zero_mem
    have hφL : ∀ b ∈ L, φ b = 0 := by
      intro b hb
      by_contra hne
      have := hw (((w - 1) / φ b) • b) (L.smul_mem _ hb)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      linarith
    refine ⟨fun k => -φ (fun j => if k = j then 1 else 0), fun k => ?_, fun v hv => ?_⟩
    · have hmem : (fun j => if k = j then (1 : ℝ) else 0) ∈ rd_simplex K := by
        refine ⟨fun j => by dsimp only; split_ifs <;> norm_num, ?_⟩
        simp
      have := hu _ hmem
      linarith
    · have hv' := hφL v hv
      rw [pi_eq_sum_univ v, map_sum] at hv'
      simp only [map_smul, smul_eq_mul] at hv'
      have : ∑ k, -φ (fun j => if k = j then (1 : ℝ) else 0) * v k =
          -∑ k, v k * φ (fun j => if k = j then 1 else 0) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this, hv', neg_zero]
  · rintro ⟨q, hq, hqL⟩ v hv hnn
    by_contra hne
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    have hpos : 0 < v k := lt_of_le_of_ne (hnn k) (Ne.symm hk)
    have : 0 < ∑ k, q k * v k :=
      Finset.sum_pos' (fun j _ => mul_nonneg (hq j).le (hnn j))
        ⟨k, Finset.mem_univ k, mul_pos (hq k) hpos⟩
    rw [hqL v hv] at this
    exact lt_irrefl 0 this

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# No one-period arbitrage and state prices

Miao, §13.4, pp. 429–430.

* `rd_StatePrice p f q`: `q` is a strictly positive state price process satisfying the
  no-arbitrage pricing equation (13.16), `p_t = (1/q⁰_t) ∑_{sᵗ⁺¹|sᵗ} q⁰_{t+1} f_{t+1}`.
* **Theorem 13.4.2** for debt constraints (`theorem_13_4_2`): no one-period arbitrage on
  `R(Θ_DC)` at every node iff a state price process exists. The proof applies Stiemke's Lemma
  at each node to the `J × (S + 1)` matrix `[−p, f(·, 1), …, f(·, S)]` and chains the ratios.
* For borrowing constraints the book's "iff" is false as printed: if every security pays zero at
  some node, `R(Θ_BC)` admits no one-period arbitrage but (13.16) fails
  (`theorem_13_4_2_BC_counterexample`). With positive prices, nonnegative payoffs and a nonzero
  payoff at every node it is true (`theorem_13_4_2_BC`).
* (13.17)–(13.18): the state price deflator `rd_deflator`, the stochastic discount factor
  `rd_SDF`, and the pricing formula (`eq_13_18`); the normalisation `q⁰(s⁰) = 1`
  (`eq_13_17_normalize`), and "π need not lie in L¹" (`rd_statePrice_not_L1`).
* Short sales (p. 430): with `R(Θ_SC) = {θ ≥ 0}`, (13.16) need not hold
  (`rd_SC_no_statePrice`), but it holds as an inequality (`rd_SC_inequality`, which with
  positive prices is in fact automatic).
* Multi-period securities (pp. 425–426): a claim paying at distance `n + 1` is priced as the
  one-period payoff given by its next-period price (`rd_multiperiod_price`,
  `rd_twoPeriodBond`).
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J : Type*} [Fintype S] [Fintype J]

/-- **(13.16)**: `q` is a strictly positive state price process for `(p, f)`:
`p_t(sᵗ) = (1/q⁰_t(sᵗ)) ∑_{sᵗ⁺¹|sᵗ} q⁰_{t+1}(sᵗ⁺¹) f_{t+1}(sᵗ⁺¹)`. -/
def rd_StatePrice (p f : List S → J → ℝ) (q : List S → ℝ) : Prop :=
  (∀ h, 0 < q h) ∧ ∀ h j, p h j = (q h)⁻¹ * ∑ s, q (s :: h) * f (s :: h) j

omit [Fintype J] in
/-- (13.16) multiplied out: `q⁰_t p_t = ∑ q⁰_{t+1} f_{t+1}`. -/
theorem rd_statePrice_mul {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    (h : List S) (j : J) : q h * p h j = ∑ s, q (s :: h) * f (s :: h) j := by
  rw [hq.2 h j, ← mul_assoc, mul_inv_cancel₀ (hq.1 h).ne', one_mul]

/-- (13.16) applied to a portfolio: `q⁰_t (p_t · v) = ∑ q⁰_{t+1} (f_{t+1} · v)`. -/
theorem rd_statePrice_dot {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    (h : List S) (v : J → ℝ) : q h * (p h ⬝ᵥ v) = ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ v) := by
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, rd_statePrice_mul hq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype S] in
/-- The process obtained by chaining one-period ratios `r(sᵗ, s)` from `q(s⁰) = 1`. -/
def rd_qOf (r : List S → S → ℝ) : List S → ℝ
  | [] => 1
  | s :: h => rd_qOf r h * r h s

omit [Fintype S] in
theorem rd_qOf_pos {r : List S → S → ℝ} (hr : ∀ h s, 0 < r h s) (h : List S) :
    0 < rd_qOf r h := by
  induction h with
  | nil => exact one_pos
  | cons s h ih => exact mul_pos ih (hr h s)

omit [Fintype J] in
/-- A state price process built from ratios satisfying the one-period pricing equation. -/
theorem rd_statePrice_qOf {p f : List S → J → ℝ} {r : List S → S → ℝ} (hr : ∀ h s, 0 < r h s)
    (hp : ∀ h j, p h j = ∑ s, r h s * f (s :: h) j) : rd_StatePrice p f (rd_qOf r) := by
  refine ⟨rd_qOf_pos hr, fun h j => ?_⟩
  rw [hp h j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [rd_qOf]
  field_simp [(rd_qOf_pos hr h).ne']

/-- Positive state prices rule out one-period arbitrage at every node, on any set of
strategies. -/
theorem rd_noOneArb_of_statePrice {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) (h : List S) (v : J → ℝ) : ¬ rd_OneArb p f h v := by
  rintro ⟨hp, hf, hs⟩
  have key := rd_statePrice_dot hq h v
  have hnn : 0 ≤ ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ v) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hq.1 _).le (hf s)
  rcases hs with hs | ⟨s, hs⟩
  · have : q h * (p h ⬝ᵥ v) < 0 := mul_neg_of_pos_of_neg (hq.1 h) hs
    linarith
  · have : 0 < ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ v) :=
      Finset.sum_pos' (fun s _ => mul_nonneg (hq.1 _).le (hf s))
        ⟨s, Finset.mem_univ s, mul_pos (hq.1 _) hs⟩
    have : q h * (p h ⬝ᵥ v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hq.1 h).le hp
    linarith

omit [Fintype S] [Fintype J] in
/-- The rows of the matrix `[−p, f(·, 1), …, f(·, S)]ᵀ` of the proof of Theorem 13.4.2, indexed
by `Option S` (`none` is the price row). -/
def rd_arbRow (p f : List S → J → ℝ) (h : List S) : Option S → J → ℝ
  | none => -p h
  | some s => f (s :: h)

/-- Stiemke's Lemma at one node: no one-period arbitrage portfolio at `h` iff there are positive
`q₀, q₁, …, q_S` with `q₀ p = ∑ₛ qₛ f(s :: h)`. -/
theorem rd_node_stiemke (p f : List S → J → ℝ) (h : List S) :
    (¬ ∃ v, rd_OneArb p f h v) ↔
      ∃ Q : Option S → ℝ, (∀ k, 0 < Q k) ∧ ∀ j, Q none * p h j = ∑ s, Q (some s) * f (s :: h) j
    := by
  classical
  set A : Matrix (Option S) J ℝ := Matrix.of (rd_arbRow p f h)
  have hAn : ∀ v, A.mulVec v none = -(p h ⬝ᵥ v) := fun v => by
    simp [A, rd_arbRow, Matrix.mulVec, dotProduct]
  have hAs : ∀ v s, A.mulVec v (some s) = f (s :: h) ⬝ᵥ v := fun v s => by
    simp [A, rd_arbRow, Matrix.mulVec, dotProduct]
  have hst := rd_stiemke (LinearMap.range A.mulVecLin)
  have lhs : (¬ ∃ v, rd_OneArb p f h v) ↔
      ∀ w ∈ LinearMap.range A.mulVecLin, (∀ k, 0 ≤ w k) → w = 0 := by
    constructor
    · rintro hno w ⟨v, rfl⟩ hnn
      simp only [Matrix.mulVecLin_apply] at hnn ⊢
      by_contra hne
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
      have hpos : 0 < A.mulVec v k := lt_of_le_of_ne (hnn k) (Ne.symm hk)
      have h0 := hnn none
      rw [hAn] at h0
      refine hno ⟨v, by linarith, fun s => ?_, ?_⟩
      · have := hnn (some s)
        rwa [hAs] at this
      · cases k with
        | none =>
          rw [hAn] at hpos
          left
          linarith
        | some s =>
          rw [hAs] at hpos
          exact Or.inr ⟨s, hpos⟩
    · rintro H ⟨v, hp, hf, hs⟩
      have hnn : ∀ k, 0 ≤ A.mulVec v k := by
        intro k
        cases k with
        | none => rw [hAn]; linarith
        | some s => rw [hAs]; exact hf s
      have h0 := H (A.mulVec v) ⟨v, rfl⟩ hnn
      rcases hs with hs | ⟨s, hs⟩
      · have := congrFun h0 none
        rw [hAn] at this
        simp only [Pi.zero_apply] at this
        linarith
      · have := congrFun h0 (some s)
        rw [hAs] at this
        simp only [Pi.zero_apply] at this
        linarith
  rw [lhs, hst]
  constructor
  · rintro ⟨Q, hQ, hQL⟩
    refine ⟨Q, hQ, fun j => ?_⟩
    have := hQL (A.mulVec (Pi.single j 1)) ⟨_, rfl⟩
    rw [Fintype.sum_option, hAn] at this
    simp only [hAs, dotProduct_single, mul_one] at this
    linarith
  · rintro ⟨Q, hQ, hQp⟩
    refine ⟨Q, hQ, ?_⟩
    rintro w ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Fintype.sum_option, hAn]
    simp only [hAs]
    have e : ∑ s, Q (some s) * (f (s :: h) ⬝ᵥ v) = (fun j => Q none * p h j) ⬝ᵥ v := by
      simp only [hQp, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring
    rw [e]
    simp only [dotProduct]
    rw [mul_neg, Finset.mul_sum, neg_add_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- **Theorem 13.4.2** (Miao, p. 429), debt constraints. With debt limits `D̄ ≥ 0`, the pair
`(p, f)` admits no one-period arbitrage on `R(Θ_DC(p, f))` at any node iff there is a strictly
positive state price process satisfying (13.16). -/
theorem theorem_13_4_2 (p f : List S → J → ℝ) {Dbar : List S → ℝ}
    (hD : ∀ h, 0 ≤ Dbar h) :
    (∀ h, ¬ rd_OneArbOn p f (rd_Rec (rd_ThetaDC f Dbar)) h) ↔ ∃ q, rd_StatePrice p f q := by
  classical
  rw [rd_rec_DC f hD]
  constructor
  · intro H
    have hnode : ∀ h, ∃ Q : Option S → ℝ, (∀ k, 0 < Q k) ∧
        ∀ j, Q none * p h j = ∑ s, Q (some s) * f (s :: h) j := by
      intro h
      refine (rd_node_stiemke p f h).1 ?_
      rintro ⟨v, hv⟩
      refine H h ⟨rd_loc v h, fun g s => ?_, by simpa [rd_loc] using hv⟩
      by_cases hg : g = h
      · subst hg
        simpa [rd_loc] using hv.2.1 s
      · simp [rd_loc, hg]
    choose Q hQ hQp using hnode
    refine ⟨rd_qOf fun h s => Q h (some s) / Q h none,
      rd_statePrice_qOf (fun h s => div_pos (hQ h _) (hQ h _)) fun h j => ?_⟩
    have hn := (hQ h none).ne'
    have e : ∑ s, Q h (some s) / Q h none * f (s :: h) j =
        (Q h none)⁻¹ * ∑ s, Q h (some s) * f (s :: h) j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e, ← hQp h j, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · rintro ⟨q, hq⟩ h ⟨θ, -, hθ⟩
    exact rd_noOneArb_of_statePrice hq h _ hθ

/-- Miao, p. 429 (correction): Theorem 13.4.2 for borrowing constraints is false as printed. With
one security paying nothing (price `1`), `R(Θ_BC)` admits no one-period arbitrage at any node,
but no state price process satisfies (13.16). -/
theorem theorem_13_4_2_BC_counterexample :
    (∀ h, ¬ rd_OneArbOn (S := Unit) (J := Unit) (fun _ _ => 1) (fun _ _ => 0)
        (rd_Rec (rd_ThetaBC (fun _ _ => 1) (fun _ => 0))) h) ∧
      ¬ ∃ q, rd_StatePrice (S := Unit) (J := Unit) (fun _ _ => 1) (fun _ _ => 0) q := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [rd_rec_BC _ (fun _ => le_rfl)]
    rintro ⟨θ, hθ, hp, -, hs⟩
    have := hθ h
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, one_mul,
      zero_mul] at this hp hs
    rcases hs with hs | ⟨_, hs⟩ <;> linarith
  · rintro ⟨q, -, hq⟩
    have := hq [] ()
    simp at this

/-- **Theorem 13.4.2** (Miao, p. 429), borrowing constraints, corrected. If prices are strictly
positive, payoffs are nonnegative and at every node some security has a nonzero payoff in some
successor state, then `(p, f)` admits no one-period arbitrage on `R(Θ_BC(p, f))` at any node iff
there is a strictly positive state price process satisfying (13.16). -/
theorem theorem_13_4_2_BC (p f : List S → J → ℝ) {Bbar : List S → ℝ}
    (hB : ∀ h, 0 ≤ Bbar h) (hp : ∀ h j, 0 < p h j) (hf : ∀ h s j, 0 ≤ f (s :: h) j)
    (hnz : ∀ h, ∃ s j, f (s :: h) j ≠ 0) :
    (∀ h, ¬ rd_OneArbOn p f (rd_Rec (rd_ThetaBC p Bbar)) h) ↔ ∃ q, rd_StatePrice p f q := by
  classical
  rw [rd_rec_BC p hB]
  constructor
  · intro H
    have hnode : ∀ h, ∃ r : S → ℝ, (∀ s, 0 < r s) ∧ ∀ j, p h j = ∑ s, r s * f (s :: h) j := by
      intro h
      set F : Matrix S J ℝ := Matrix.of fun s j => f (s :: h) j
      set P : Matrix Unit J ℝ := Matrix.of fun _ j => p h j
      set L : Submodule ℝ (S → ℝ) := (LinearMap.ker P.mulVecLin).map F.mulVecLin
      have hFv : ∀ v s, (F.mulVec v) s = f (s :: h) ⬝ᵥ v := fun v s => by
        simp [F, Matrix.mulVec, dotProduct]
      have hPv : ∀ v, P.mulVec v = 0 ↔ p h ⬝ᵥ v = 0 := fun v => by
        constructor
        · intro e
          have := congrFun e ()
          simpa [P, Matrix.mulVec, dotProduct] using this
        · intro e
          funext u
          simpa [P, Matrix.mulVec, dotProduct] using e
      have hno : ∀ w ∈ L, (∀ k, 0 ≤ w k) → w = 0 := by
        rintro w ⟨v, hv, rfl⟩ hnn
        rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply, hPv] at hv
        by_contra hne
        obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
        have hpos : 0 < (F.mulVec v) k := lt_of_le_of_ne (hnn k) (Ne.symm hk)
        refine H h ⟨rd_loc v h, fun g => ?_, ?_⟩
        · by_cases hg : g = h
          · subst hg
            simp [rd_loc, hv]
          · simp [rd_loc, hg]
        · refine ⟨by simp [rd_loc, hv], fun s => ?_, Or.inr ⟨k, ?_⟩⟩
          · have := hnn s
            simpa [rd_loc, hFv] using this
          · simpa [rd_loc, hFv] using hpos
      obtain ⟨r, hr, hrL⟩ := (rd_stiemke L).1 hno
      set g : J → ℝ := fun j => ∑ s, r s * f (s :: h) j
      have hgv : ∀ v, p h ⬝ᵥ v = 0 → g ⬝ᵥ v = 0 := by
        intro v hv
        have := hrL (F.mulVec v) ⟨v, by
          rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply, hPv]; exact hv, rfl⟩
        simp only [hFv, dotProduct, Finset.mul_sum] at this
        rw [Finset.sum_comm] at this
        simp only [g, dotProduct, Finset.sum_mul]
        rw [← this]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring
      obtain ⟨s0, j0, hj0⟩ := hnz h
      have hg0 : 0 < g j0 := Finset.sum_pos' (fun s _ => mul_nonneg (hr s).le (hf h s j0))
        ⟨s0, Finset.mem_univ _, mul_pos (hr s0) (lt_of_le_of_ne (hf h s0 j0) (Ne.symm hj0))⟩
      have hgj : ∀ j, g j * p h j0 = g j0 * p h j := by
        intro j
        by_cases hj : j = j0
        · rw [hj]
        have := hgv (p h j0 • Pi.single j 1 - p h j • Pi.single j0 1) (by
          simp only [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
          ring)
        simp only [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one,
          smul_eq_mul] at this
        linarith
      set lam := g j0 / p h j0
      have hlam : 0 < lam := div_pos hg0 (hp h j0)
      refine ⟨fun s => r s / lam, fun s => div_pos (hr s) hlam, fun j => ?_⟩
      have hj := hgj j
      have e : ∑ s, r s / lam * f (s :: h) j = g j / lam := by
        simp only [g, div_eq_mul_inv, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [e]
      have hp0 := (hp h j0).ne'
      have hg0' := hg0.ne'
      simp only [lam]
      field_simp
      linarith
    choose r hr hrp using hnode
    exact ⟨_, rd_statePrice_qOf hr hrp⟩
  · rintro ⟨q, hq⟩ h ⟨θ, hθ, hp1, hf1, hs⟩
    have h0 : p h ⬝ᵥ θ h = 0 := le_antisymm hp1 (hθ h)
    have key := rd_statePrice_dot hq h (θ h)
    rw [h0, mul_zero] at key
    rcases hs with hs | ⟨s, hs⟩
    · linarith
    · have : 0 < ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ θ h) :=
        Finset.sum_pos' (fun s _ => mul_nonneg (hq.1 _).le (hf1 s))
          ⟨s, Finset.mem_univ s, mul_pos (hq.1 _) hs⟩
      linarith

omit [Fintype J] in
/-- Miao, p. 430: only the ratios `q⁰_{t+1}/q⁰_t` are restricted, so positive multiples of a
state price process are state price processes. -/
theorem rd_statePrice_smul {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {a : ℝ} (ha : 0 < a) : rd_StatePrice p f (fun h => a * q h) := by
  refine ⟨fun h => mul_pos ha (hq.1 h), fun h j => ?_⟩
  rw [hq.2 h j]
  simp only [mul_assoc, ← Finset.mul_sum, mul_inv]
  field_simp

omit [Fintype J] in
/-- **(13.17)** normalisation (Miao, p. 430): every state price process can be normalised to
`q⁰(s⁰) = 1`. -/
theorem eq_13_17_normalize {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q) :
    rd_StatePrice p f (fun h => (q [])⁻¹ * q h) ∧ (fun h => (q [])⁻¹ * q h) [] = 1 :=
  ⟨rd_statePrice_smul hq (inv_pos.2 (hq.1 [])), inv_mul_cancel₀ (hq.1 []).ne'⟩

/-- **(13.17)** The state price deflator `π_t(sᵗ) = q⁰_t(sᵗ) / Pr(sᵗ)`. -/
noncomputable def rd_deflator (T : RDTree S) (q : List S → ℝ) (h : List S) : ℝ := q h / T.Pr h

/-- The stochastic discount factor `M_{t+1} = π_{t+1}/π_t` (set to `1` at the root). -/
noncomputable def rd_SDF (T : RDTree S) (q : List S → ℝ) : List S → ℝ
  | [] => 1
  | s :: h => rd_deflator T q (s :: h) / rd_deflator T q h

omit [Fintype J] in
/-- **(13.18)** (Miao, p. 430). Under (13.16), `p_t = (1/π_t) E_t[π_{t+1} f_{t+1}]
= E_t[M_{t+1} f_{t+1}]`. -/
theorem eq_13_18 (T : RDTree S) {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) (h : List S) (j : J) :
    p h j = (rd_deflator T q h)⁻¹ * rd_condE T (fun g => rd_deflator T q g * f g j) h 1 ∧
      p h j = rd_condE T (fun g => rd_SDF T q g * f g j) h 1 := by
  have hPr := fun g => (T.pos g).ne'
  have hqh := (hq.1 h).ne'
  rw [rd_condE_one, rd_condE_one, hq.2 h j]
  simp only [rd_condPr, rd_deflator, rd_SDF, Finset.mul_sum]
  constructor
  · refine Finset.sum_congr rfl fun s _ => ?_
    field_simp [hPr (s :: h), hPr h]
  · refine Finset.sum_congr rfl fun s _ => ?_
    field_simp [hPr (s :: h), hPr h]

/-- Miao, p. 430: "Theorem 13.4.2 does not imply that `π` or `q⁰` lies in `L¹`." With one
riskless bond of price and payoff `1` in a deterministic economy, the state price process is
constant (`q⁰ ≡ 1` after normalisation) and not summable. -/
theorem rd_statePrice_not_L1 :
    rd_StatePrice (S := Unit) (J := Unit) (fun _ _ => 1) (fun _ _ => 1) (fun _ => 1) ∧
      ¬ rd_L1 (S := Unit) (fun _ => 1) := by
  refine ⟨⟨fun _ => one_pos, fun _ _ => by simp⟩, fun hL => ?_⟩
  have := rd_L1_tendsto hL
  have e : (fun t => rd_dsum (S := Unit) (fun _ => (1 : ℝ)) [] t) = fun _ => 1 := by
    funext t
    have := rd_dsum_Pr (rd_uniformTree Unit) [] t
    simpa [rd_uniformTree] using this
  rw [e] at this
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)

/-- Miao, p. 430 (short sales): the no-arbitrage pricing equation (13.16) need not hold under
short-sales constraints. Two securities with the same payoff `1` and prices `1` and `2` admit no
one-period arbitrage on `R(Θ_SC) = {θ ≥ 0}`, but no state price process exists. -/
theorem rd_SC_no_statePrice :
    (∀ h, ¬ rd_OneArbOn (S := Unit) (J := Bool) (fun _ j => if j then 2 else 1) (fun _ _ => 1)
        (rd_Rec (rd_ThetaSC (fun _ _ => 0))) h) ∧
      ¬ ∃ q, rd_StatePrice (S := Unit) (J := Bool) (fun _ j => if j then 2 else 1)
        (fun _ _ => 1) q := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [rd_rec_SC (fun _ _ => le_rfl)]
    rintro ⟨θ, hθ, hp, hf, hs⟩
    have h1 := hθ h true
    have h2 := hθ h false
    simp only [dotProduct, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, one_mul] at hp hf hs
    rcases hs with hs | ⟨_, hs⟩ <;> linarith
  · rintro ⟨q, -, hq⟩
    have h1 := hq [] true
    have h2 := hq [] false
    simp only [↓reduceIte, Bool.false_eq_true] at h1 h2
    rw [← h2] at h1
    norm_num at h1

/-- Miao, p. 430 (short sales): with strictly positive prices, (13.16) holds as an inequality,
`q⁰_t p_t ≥ ∑ q⁰_{t+1} f_{t+1}`, for some strictly positive `q⁰`; and any such `q⁰` rules out
one-period arbitrage on `R(Θ_SC)` (short-sales limits `h̄ ≥ 0`). -/
theorem rd_SC_inequality (p f : List S → J → ℝ) {hbar : List S → J → ℝ}
    (hh : ∀ h j, 0 ≤ hbar h j) (hp : ∀ h j, 0 < p h j) :
    (∃ q : List S → ℝ, (∀ h, 0 < q h) ∧ ∀ h j, ∑ s, q (s :: h) * f (s :: h) j ≤ q h * p h j) ∧
      ∀ q : List S → ℝ, (∀ h, 0 < q h) →
        (∀ h j, ∑ s, q (s :: h) * f (s :: h) j ≤ q h * p h j) →
        ∀ h, ¬ rd_OneArbOn p f (rd_Rec (rd_ThetaSC hbar)) h := by
  rw [rd_rec_SC hh]
  refine ⟨?_, fun q hq hqp h => ?_⟩
  · set A : List S → ℝ := fun h => ∑ j, ∑ s, |f (s :: h) j| / p h j
    have hA : ∀ h, 0 ≤ A h := fun h => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun s _ => div_nonneg (abs_nonneg _) (hp h j).le
    set r : List S → S → ℝ := fun h _ => 1 / (1 + A h)
    have hr : ∀ h s, 0 < r h s := fun h _ => div_pos one_pos (by linarith [hA h])
    refine ⟨rd_qOf r, rd_qOf_pos hr, fun h j => ?_⟩
    simp only [rd_qOf, mul_assoc, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (rd_qOf_pos hr h).le
    have hpj := hp h j
    have hsum : ∑ s, |f (s :: h) j| / p h j ≤ A h :=
      Finset.single_le_sum (f := fun j => ∑ s, |f (s :: h) j| / p h j)
        (fun j _ => Finset.sum_nonneg fun s _ => div_nonneg (abs_nonneg _) (hp h j).le)
        (Finset.mem_univ j)
    have h1 : ∑ s, r h s * f (s :: h) j ≤ 1 / (1 + A h) * ∑ s, |f (s :: h) j| := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (le_abs_self _) (hr h s).le
    have e2 : ∑ s, |f (s :: h) j| = (∑ s, |f (s :: h) j| / p h j) * p h j := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by field_simp
    have h2 : ∑ s, |f (s :: h) j| ≤ A h * p h j := by
      rw [e2]
      exact mul_le_mul_of_nonneg_right hsum hpj.le
    have hA1 : 0 < 1 + A h := by linarith [hA h]
    calc ∑ s, r h s * f (s :: h) j ≤ 1 / (1 + A h) * ∑ s, |f (s :: h) j| := h1
      _ ≤ 1 / (1 + A h) * (A h * p h j) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ p h j := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hA1]
          nlinarith [hA h]
  · rintro ⟨θ, hθ, hp1, hf1, hs⟩
    have hge : 0 ≤ p h ⬝ᵥ θ h :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hp h j).le (hθ h j)
    have h0 : p h ⬝ᵥ θ h = 0 := le_antisymm hp1 hge
    have key : ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ θ h) ≤ q h * (p h ⬝ᵥ θ h) := by
      simp only [dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun j _ => ?_
      have := mul_le_mul_of_nonneg_right (hqp h j) (hθ h j)
      rw [Finset.sum_mul] at this
      calc ∑ s, q (s :: h) * (f (s :: h) j * θ h j)
          = ∑ s, q (s :: h) * f (s :: h) j * θ h j :=
            Finset.sum_congr rfl fun s _ => by ring
        _ ≤ q h * p h j * θ h j := this
        _ = q h * (p h j * θ h j) := by ring
    rw [h0, mul_zero] at key
    rcases hs with hs | ⟨s, hs⟩
    · linarith
    · have : 0 < ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ θ h) :=
        Finset.sum_pos' (fun s _ => mul_nonneg (hq _).le (hf1 s))
          ⟨s, Finset.mem_univ s, mul_pos (hq _) hs⟩
      linarith

/-- Miao, pp. 425–426 (multi-period securities). Pricing a claim `X` paid at distance `n + 1`
from `sᵗ` with state prices equals pricing the one-period payoff given, at each successor, by the
claim's price there. This is how the two-period bond and the call option are described by
one-period payoffs. -/
theorem rd_multiperiod_price {q : List S → ℝ} (hq : ∀ h, 0 < q h) (X : List S → ℝ)
    (h : List S) (n : ℕ) :
    (q h)⁻¹ * rd_dsum (fun g => q g * X g) h (n + 1) =
      (q h)⁻¹ * ∑ s, q (s :: h) * ((q (s :: h))⁻¹ * rd_dsum (fun g => q g * X g) (s :: h) n) := by
  rw [rd_dsum_succ]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, mul_inv_cancel₀ (hq _).ne', one_mul]

/-- Miao, pp. 425–426: the two-period riskless bond (one unit at every node two periods ahead)
has the price of the one-period payoff `q_{1,t+1}`, the one-period bond price at `t + 1`. -/
theorem rd_twoPeriodBond {q : List S → ℝ} (hq : ∀ h, 0 < q h) (h : List S) :
    (q h)⁻¹ * rd_dsum q h 2 =
      (q h)⁻¹ * ∑ s, q (s :: h) * ((q (s :: h))⁻¹ * ∑ s', q (s' :: s :: h)) := by
  have := rd_multiperiod_price hq (fun _ => 1) h 1
  simp only [mul_one] at this
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rd_dsum_succ]
  simp [rd_dsum_zero]

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Complete markets, Theorem 13.4.3 and Exercise 13.8

Miao, §13.4, pp. 430–432, and Exercise 13.8, p. 454.

* `rd_payoffMatrix f h` is the `J × S` payoff matrix `D_{t+1}(sᵗ)`. Rank `S` is equivalent to
  spanning every one-period payoff vector (`rd_rank_iff_span`) and to injectivity of
  `x ↦ D x` (`rd_rank_iff_injective`).
* `rd_CompletePrinted`: the book's definition of dynamically complete markets (every bounded
  `x` is the net cash flow of some strategy from date 1 on). Without any restriction on the
  strategy it is satisfied whenever prices are positive, by rolling one security over
  (`rd_completePrinted_of_pos`). So Exercise 13.8's "only if" is false as printed
  (`ex_13_8_counterexample`: one riskless bond, two states), and so is Theorem 13.4.3 with this
  definition (`theorem_13_4_3_counterexample`: two non-proportional state price processes).
* `rd_Complete`: completeness for finite-horizon payoffs replicated by strategies that are
  liquidated at the horizon. **Exercise 13.8** corrected (`ex_13_8`): markets are complete in
  this sense iff `D_{t+1}(sᵗ)` has rank `S` at every node; the "if" direction of the printed
  statement holds too (`ex_13_8_printed_if`).
* **Theorem 13.4.3** (`theorem_13_4_3`): with rank `S` at every node and no arbitrage on
  `R(Θ_DC)`, a state price process exists and is unique up to a positive factor; the one-period
  ratios are `x_{t+1} = (DᵀD)⁻¹ Dᵀ p_t` (`theorem_13_4_3_formula`).
* Arrow securities (p. 431): the payoff matrix is the identity, so markets are complete
  (`rd_arrow_rank`), and the Arrow prices are the ratios of state prices,
  `q⁰_{t+1}(sᵗ⁺¹) = Q_t(s_{t+1} | sᵗ) q⁰_t(sᵗ)` (`rd_arrow_statePrice`).
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J : Type*} [Fintype S] [Fintype J]

omit [Fintype S] [Fintype J] in
/-- The `J × S` payoff matrix `D_{t+1}(sᵗ)`: entry `(j, s)` is `f_{j,t+1}(sᵗ, s)`. -/
def rd_payoffMatrix (f : List S → J → ℝ) (h : List S) : Matrix J S ℝ :=
  Matrix.of fun j s => f (s :: h) j

omit [Fintype S] in
/-- `(D_{t+1}(sᵗ))ᵀ v` is the vector of payoffs `f_{t+1}(sᵗ, s) · v`. -/
theorem rd_payoffMatrix_transpose_mulVec (f : List S → J → ℝ) (h : List S) (v : J → ℝ)
    (s : S) : Matrix.mulVec (rd_payoffMatrix f h).transpose v s = f (s :: h) ⬝ᵥ v := by
  simp [rd_payoffMatrix, Matrix.mulVec, dotProduct, mul_comm]

omit [Fintype J] in
/-- `D_{t+1}(sᵗ) x` is the vector of the prices `∑ₛ xₛ f_{t+1}(sᵗ, s)`. -/
theorem rd_payoffMatrix_mulVec (f : List S → J → ℝ) (h : List S) (x : S → ℝ) (j : J) :
    Matrix.mulVec (rd_payoffMatrix f h) x j = ∑ s, x s * f (s :: h) j := by
  simp [rd_payoffMatrix, Matrix.mulVec, dotProduct, mul_comm]

/-- Rank `S` iff the securities span every one-period payoff vector at `sᵗ`. -/
theorem rd_rank_iff_span (f : List S → J → ℝ) (h : List S) :
    (rd_payoffMatrix f h).rank = Fintype.card S ↔
      ∀ z : S → ℝ, ∃ v : J → ℝ, ∀ s, f (s :: h) ⬝ᵥ v = z s := by
  rw [← Matrix.rank_transpose, Matrix.rank]
  set M := (rd_payoffMatrix f h).transpose
  have hsurj : (∀ z : S → ℝ, ∃ v : J → ℝ, ∀ s, f (s :: h) ⬝ᵥ v = z s) ↔
      LinearMap.range M.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    constructor
    · intro H z
      obtain ⟨v, hv⟩ := H z
      exact ⟨v, funext fun s => by
        rw [Matrix.mulVecLin_apply, rd_payoffMatrix_transpose_mulVec, hv]⟩
    · intro H z
      obtain ⟨v, hv⟩ := H z
      exact ⟨v, fun s => by
        rw [← rd_payoffMatrix_transpose_mulVec, ← Matrix.mulVecLin_apply, hv]⟩
  rw [hsurj]
  constructor
  · intro hr
    exact Submodule.eq_top_of_finrank_eq (by rw [hr, Module.finrank_pi])
  · intro ht
    rw [ht, finrank_top, Module.finrank_pi]

omit [Fintype J] in
/-- Rank `S` iff `x ↦ D_{t+1}(sᵗ) x` is injective (the form used in Theorem 13.4.3). -/
theorem rd_rank_iff_injective (f : List S → J → ℝ) (h : List S) :
    (rd_payoffMatrix f h).rank = Fintype.card S ↔
      Function.Injective (Matrix.mulVec (rd_payoffMatrix f h)) := by
  rw [Matrix.rank]
  set M := rd_payoffMatrix f h
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_pi] at hrn
  have hinj : Function.Injective M.mulVec ↔ LinearMap.ker M.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    rfl
  rw [hinj, ← Submodule.finrank_eq_zero]
  omega

/-- Book's definition of complete markets (Miao, pp. 430–431): for every bounded process `x`
there is a strategy with `f_t · θ_{t−1} − p_t · θ_t = x_t` at all nodes of date `t ≥ 1`. -/
def rd_CompletePrinted (p f : List S → J → ℝ) : Prop :=
  ∀ x : List S → ℝ, rd_Bdd x →
    ∃ θ : List S → J → ℝ, ∀ s h, f (s :: h) ⬝ᵥ θ h - p (s :: h) ⬝ᵥ θ (s :: h) = x (s :: h)

/-- Complete markets for finite-horizon payoffs: every bounded `x` vanishing after `T` is the net
cash flow, from date 1 on, of a strategy liquidated from date `T` on. -/
def rd_Complete (p f : List S → J → ℝ) : Prop :=
  ∀ x : List S → ℝ, rd_Bdd x → ∀ T : ℕ, (∀ g, T < g.length → x g = 0) →
    ∃ θ : List S → J → ℝ, (∀ g, T ≤ g.length → θ g = 0) ∧
      ∀ s h, f (s :: h) ⬝ᵥ θ h - p (s :: h) ⬝ᵥ θ (s :: h) = x (s :: h)

omit [Fintype S] in
/-- Rolling security `j₀` over: the strategy that finances any `x` from date 1 on. -/
noncomputable def rd_rollover [DecidableEq J] (p f : List S → J → ℝ) (x : List S → ℝ) (j0 : J) :
    List S → J → ℝ
  | [] => 0
  | s :: h => ((f (s :: h) ⬝ᵥ rd_rollover p f x j0 h - x (s :: h)) / p (s :: h) j0) •
      Pi.single j0 1

omit [Fintype S] in
/-- With strictly positive prices, the book's completeness condition always holds: the payoff
`x` is financed by rolling one security over. -/
theorem rd_completePrinted_of_pos [Nonempty J] (p f : List S → J → ℝ)
    (hp : ∀ h j, 0 < p h j) : rd_CompletePrinted p f := by
  classical
  intro x _
  obtain ⟨j0⟩ := (inferInstance : Nonempty J)
  refine ⟨rd_rollover p f x j0, fun s h => ?_⟩
  simp only [rd_rollover, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
  rw [div_mul_cancel₀ _ (hp _ j0).ne']
  ring

/-- **Exercise 13.8** (Miao, p. 454), the "if" direction of the printed statement: rank `S` at
every node (with positive prices) gives completeness in the book's sense. -/
theorem ex_13_8_printed_if [Nonempty J] (p f : List S → J → ℝ) (hp : ∀ h j, 0 < p h j)
    (_hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) : rd_CompletePrinted p f :=
  rd_completePrinted_of_pos p f hp

/-- **Exercise 13.8** (Miao, p. 454), counterexample to the printed "only if": with two states
and one riskless bond (price and payoff `1`), markets are complete in the book's sense but the
payoff matrix has rank `1 < 2`. -/
theorem ex_13_8_counterexample :
    rd_CompletePrinted (S := Bool) (J := Unit) (fun _ _ => 1) (fun _ _ => 1) ∧
      ∀ h, (rd_payoffMatrix (S := Bool) (J := Unit) (fun _ _ => 1) h).rank ≠ Fintype.card Bool
    := by
  refine ⟨rd_completePrinted_of_pos _ _ fun _ _ => one_pos, fun h => ?_⟩
  have := Matrix.rank_le_card_height (rd_payoffMatrix (S := Bool) (J := Unit) (fun _ _ => 1) h)
  simp only [Fintype.card_unit] at this
  simp only [Fintype.card_bool]
  omega

omit [Fintype S] in
/-- Backward construction of a replicating strategy, `n` periods before liquidation. -/
noncomputable def rd_backward (p : List S → J → ℝ) (sol : List S → (S → ℝ) → J → ℝ)
    (x : List S → ℝ) : ℕ → List S → J → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun g => sol g fun s => x (s :: g) + p (s :: g) ⬝ᵥ rd_backward p sol x n (s :: g)

/-- **Exercise 13.8** (Miao, p. 454), corrected: markets are complete for finite-horizon payoffs
(`rd_Complete`) iff the payoff matrix `D_{t+1}(sᵗ)` has rank `S` at every node `sᵗ`. -/
theorem ex_13_8 (p f : List S → J → ℝ) :
    rd_Complete p f ↔ ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S := by
  classical
  simp only [rd_rank_iff_span]
  constructor
  · intro H h z
    set x : List S → ℝ := fun g => match g with
      | [] => 0
      | s :: g' => if g' = h then z s else 0
    have hx : rd_Bdd x := by
      refine ⟨∑ s, |z s|, fun g => ?_⟩
      have h0 : 0 ≤ ∑ s, |z s| := Finset.sum_nonneg fun s _ => abs_nonneg _
      cases g with
      | nil => simpa [x] using h0
      | cons s g' =>
        simp only [x]
        split_ifs
        · exact Finset.single_le_sum (f := fun s => |z s|) (fun s _ => abs_nonneg _)
            (Finset.mem_univ s)
        · simpa using h0
    obtain ⟨θ, hθT, hθ⟩ := H x hx (h.length + 1) (fun g hg => by
      cases g with
      | nil => rfl
      | cons s g' =>
        have : g' ≠ h := by
          rintro rfl
          simp at hg
        simp [x, this])
    refine ⟨θ h, fun s => ?_⟩
    have := hθ s h
    rw [hθT (s :: h) (by simp)] at this
    simpa [x] using this
  · intro H x _ T hxT
    choose sol hsol using H
    refine ⟨fun g => rd_backward p sol x (T - g.length) g, fun g hg => ?_, fun s h => ?_⟩
    · simp only [Nat.sub_eq_zero_of_le hg, rd_backward]
    · simp only [List.length_cons]
      by_cases hT : h.length < T
      · have e : T - h.length = (T - (h.length + 1)) + 1 := by omega
        rw [e, rd_backward, hsol]
        ring
      · push Not at hT
        rw [Nat.sub_eq_zero_of_le hT, Nat.sub_eq_zero_of_le (by omega)]
        simp only [rd_backward, dotProduct_zero, sub_zero]
        exact (hxT (s :: h) (by simp; omega)).symm

omit [Fintype J] in
/-- The one-period ratio vector of a state price process, `x_{t+1}(sᵗ)_s = q⁰(sᵗ, s)/q⁰(sᵗ)`,
solves `D_{t+1}(sᵗ) x_{t+1}(sᵗ) = p_t(sᵗ)` (the proof of Theorem 13.4.3). -/
theorem rd_ratio_solves {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    (h : List S) :
    Matrix.mulVec (rd_payoffMatrix f h) (fun s => q (s :: h) / q h) = p h := by
  funext j
  rw [rd_payoffMatrix_mulVec, hq.2 h j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype J] in
/-- Uniqueness in Theorem 13.4.3: with rank `S` at every node, any two state price processes are
proportional, `q′ = (q′(s⁰)/q(s⁰)) q`. -/
theorem rd_statePrice_unique {p f : List S → J → ℝ}
    (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) {q q' : List S → ℝ}
    (hq : rd_StatePrice p f q) (hq' : rd_StatePrice p f q') (h : List S) :
    q' h = q' [] / q [] * q h := by
  have hr : ∀ g s, q' (s :: g) / q' g = q (s :: g) / q g := by
    intro g s
    have := (rd_rank_iff_injective f g).1 (hrank g)
      ((rd_ratio_solves hq' g).trans (rd_ratio_solves hq g).symm)
    exact congrFun this s
  have key : ∀ g, q' g / q g = q' [] / q [] := by
    intro g
    induction g with
    | nil => rfl
    | cons s g ih =>
      rw [← ih]
      have := hr g s
      have h1 := (hq.1 g).ne'
      have h2 := (hq.1 (s :: g)).ne'
      have h3 := (hq'.1 g).ne'
      field_simp at this ⊢
      linarith
  rw [← key h]
  field_simp [(hq.1 h).ne']

/-- **Theorem 13.4.3** (Miao, p. 431). If the payoff matrix has rank `S` at every node and there
is no arbitrage on `R(Θ_DC(p, f))` (debt limits `D̄ ≥ 0`), then a state price process exists and
it is unique up to a positive scaling factor. -/
theorem theorem_13_4_3 (p f : List S → J → ℝ) {Dbar : List S → ℝ}
    (hD : ∀ h, 0 ≤ Dbar h) (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S)
    (hna : ¬ rd_ArbOn p f (rd_Rec (rd_ThetaDC f Dbar))) :
    (∃ q, rd_StatePrice p f q) ∧
      ∀ q q', rd_StatePrice p f q → rd_StatePrice p f q' → ∀ h, q' h = q' [] / q [] * q h := by
  classical
  refine ⟨(theorem_13_4_2 p f hD).1 fun h => ?_, fun q q' hq hq' h =>
    rd_statePrice_unique hrank hq hq' h⟩
  refine rd_noArbOn_noOneArbOn p f _ ?_ hna h
  intro θ hθ g
  rw [rd_rec_DC f hD] at hθ ⊢
  exact rd_loc_mem_recDC f hθ g

/-- **Theorem 13.4.3**, the formula in the proof (Miao, p. 431): with rank `S`, `DᵀD` is
invertible and the ratio vector is `x_{t+1}(sᵗ) = (DᵀD)⁻¹ Dᵀ p_t(sᵗ)`. -/
theorem theorem_13_4_3_formula [DecidableEq S] {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) (h : List S)
    (hrank : (rd_payoffMatrix f h).rank = Fintype.card S) :
    IsUnit ((rd_payoffMatrix f h).transpose * rd_payoffMatrix f h) ∧
      (fun s => q (s :: h) / q h) =
        Matrix.mulVec ((rd_payoffMatrix f h).transpose * rd_payoffMatrix f h)⁻¹
          (Matrix.mulVec (rd_payoffMatrix f h).transpose (p h)) := by
  set D := rd_payoffMatrix f h
  have hinj := (rd_rank_iff_injective f h).1 hrank
  have hunit : IsUnit (D.transpose * D) := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro v w hvw
    apply hinj
    have hz : Matrix.mulVec (D.transpose * D) (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    have : Matrix.mulVec D (v - w) ⬝ᵥ Matrix.mulVec D (v - w) = 0 := by
      have e : (v - w) ⬝ᵥ Matrix.mulVec (D.transpose * D) (v - w) =
          Matrix.mulVec D (v - w) ⬝ᵥ Matrix.mulVec D (v - w) := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      rw [← e, hz, dotProduct_zero]
    rw [dotProduct_self_eq_zero, Matrix.mulVec_sub, sub_eq_zero] at this
    exact this
  refine ⟨hunit, ?_⟩
  have hx := rd_ratio_solves hq h
  rw [← hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    show rd_payoffMatrix f h = D from rfl,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit), Matrix.one_mulVec]

/-- **Theorem 13.4.3**, counterexample with the book's completeness condition: two states, one
riskless bond (price and payoff `1`). Markets are complete in the book's sense and there is no
arbitrage on `R(Θ_DC)` (limit `0`), yet the state price processes built from the ratios
`(1/2, 1/2)` and `(1/3, 2/3)` are not proportional. -/
theorem theorem_13_4_3_counterexample :
    rd_CompletePrinted (S := Bool) (J := Unit) (fun _ _ => 1) (fun _ _ => 1) ∧
      ¬ rd_ArbOn (S := Bool) (J := Unit) (fun _ _ => 1) (fun _ _ => 1)
        (rd_Rec (rd_ThetaDC (fun _ _ => 1) (fun _ => 0))) ∧
      rd_StatePrice (S := Bool) (J := Unit) (fun _ _ => 1) (fun _ _ => 1)
        (rd_qOf fun _ _ => 1 / 2) ∧
      rd_StatePrice (S := Bool) (J := Unit) (fun _ _ => 1) (fun _ _ => 1)
        (rd_qOf fun _ s => if s then 1 / 3 else 2 / 3) ∧
      ¬ ∃ a : ℝ, ∀ h, rd_qOf (S := Bool) (fun _ s => if s then 1 / 3 else 2 / 3) h =
        a * rd_qOf (S := Bool) (fun _ _ => 1 / 2) h := by
  refine ⟨rd_completePrinted_of_pos _ _ fun _ _ => one_pos, ?_,
    rd_statePrice_qOf (fun _ _ => by norm_num) fun _ _ => by norm_num,
    rd_statePrice_qOf (fun _ s => by split_ifs <;> norm_num) fun _ _ => by norm_num, ?_⟩
  · rw [rd_rec_DC _ (fun _ => le_rfl)]
    rintro ⟨θ, hθ, hnn, g, hg⟩
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, one_mul,
      Set.mem_ofPred_eq] at hθ
    have h0 : ∀ g, θ g () = 0 := by
      intro g
      induction g with
      | nil =>
        have := hnn []
        simp only [rd_net, rd_fz, rd_prev, dotProduct, Finset.univ_unique, Finset.sum_singleton,
          Pi.zero_apply, mul_zero, one_mul, zero_sub] at this
        linarith [hθ [] true]
      | cons s g ih =>
        have := hnn (s :: g)
        simp only [rd_net, rd_fz, rd_prev, dotProduct, Finset.univ_unique, Finset.sum_singleton,
          one_mul, ih, zero_sub] at this
        linarith [hθ (s :: g) true]
    cases g with
    | nil => simp [rd_net, rd_prev, dotProduct, h0] at hg
    | cons s g => simp [rd_net, rd_fz, rd_prev, dotProduct, h0] at hg
  · rintro ⟨a, ha⟩
    have h0 := ha []
    have h1 := ha [true]
    simp only [rd_qOf, ↓reduceIte] at h0 h1
    norm_num at h0 h1
    rw [← h0] at h1
    norm_num at h1

/-- Arrow securities complete the market: their payoff matrix is the identity, of rank `S`
(Miao, p. 431). -/
theorem rd_arrow_rank [DecidableEq S] (h : List S) :
    (rd_payoffMatrix (rd_arrowPayoff (S := S)) h).rank = Fintype.card S := by
  have : rd_payoffMatrix (rd_arrowPayoff (S := S)) h = 1 := by
    ext j s
    simp [rd_payoffMatrix, rd_arrowPayoff, Matrix.one_apply]
  rw [this, Matrix.rank_one]

/-- Miao, p. 432: with Arrow securities priced at `Q_t(s′ | sᵗ)`, the state price equation
(13.16) is the relation `q⁰_{t+1}(sᵗ, s′) = Q_t(s′ | sᵗ) q⁰_t(sᵗ)`. -/
theorem rd_arrow_statePrice [DecidableEq S] (Q : List S → S → ℝ) (q : List S → ℝ)
    (hq : ∀ h, 0 < q h) :
    rd_StatePrice Q rd_arrowPayoff q ↔ ∀ h s, q (s :: h) = Q h s * q h := by
  have e : ∀ h s, (q h)⁻¹ * ∑ s', q (s' :: h) * rd_arrowPayoff (s' :: h) s =
      (q h)⁻¹ * q (s :: h) := by
    intro h s
    simp [rd_arrowPayoff]
  constructor
  · rintro ⟨-, H⟩ h s
    rw [H h s, e]
    field_simp [(hq h).ne']
  · intro H
    refine ⟨hq, fun h s => ?_⟩
    rw [e, H]
    field_simp [(hq h).ne']

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Radner equilibrium, the transversality condition and natural debt limits

Miao, §13.4, pp. 427–435.

* Radner equilibrium with debt constraints (**Definition 13.4.1**, `rd_RadnerDC`) and with
  borrowing constraints (`rd_RadnerBC`); summing the budget equalities gives the goods-market
  condition of Definition 13.4.1 (`rd_goods_clearing`), which with zero supply is the
  feasibility condition (13.2) (`definition_13_4_1`).
* The present-value budget inequalities (13.19)–(13.20) (`eq_13_19`, `eq_13_19_E`, `eq_13_20`),
  the transversality condition (13.21) (`rd_TVC`), and the limits (13.22) (`eq_13_22`) and
  (13.23) (`eq_13_23`). (13.23) needs the transversality condition *conditional on* `sᵗ`; the
  date-0 condition (13.21) does not imply it (see `eq_13_23_counterexample` in `RDCounter`).
  A lower bound on the date-`T` value that vanishes in the limit is enough for (13.22)
  (`rd_AD_of_lowerTail`); bounded borrowing or debt limits supply one (`rd_AD_of_BC`,
  `rd_AD_of_DC`).
* The Arrow–Debreu equilibrium of §13.3 in this setting (`rd_ADEqm`, Definition 13.3.1, with the
  budget (13.5) `rd_ADBudget`), Pareto optimality (`rd_ParetoOptimal`) and the First Welfare
  Theorem in this setting (`rd_first_welfare`, Theorem 13.3.1 re-proved here as needed for §13.4).
* The competitive equilibrium with transversality condition (**Definition 13.4.2**,
  `rd_CETVC`). Its allocation is an Arrow–Debreu equilibrium allocation (`definition_13_4_2`),
  hence Pareto optimal (`rd_cetvc_pareto`). Conversely an Arrow–Debreu equilibrium with
  positive prices in `L¹` is a competitive equilibrium with transversality condition once the
  securities have rank `S` and are priced by its state prices (`rd_ad_cetvc`); this is the
  step of the claim on pp. 433–434 that follows the Second Welfare Theorem. The strategy is
  built by replication (`rd_repl`).
* The natural debt limit (13.24) (`eq_13_24`, `rd_naturalDebt_nonbinding`) and the natural
  borrowing limit (`rd_naturalBorrowing`).
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J ι : Type*} [Fintype S] [Fintype J] [Fintype ι]

omit [Fintype S] in
/-- A consumption-only problem: `c` maximises `U` over the plans satisfying `Feas`. -/
def rd_SolvesC (U : (List S → ℝ) → ℝ) (Feas : (List S → ℝ) → Prop) (c : List S → ℝ) : Prop :=
  Feas c ∧ ∀ c', Feas c' → U c' ≤ U c

/-- The budget constraint (13.11) holding with equality. -/
def rd_BudgetEq (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ) (c : List S → ℝ)
    (θ : List S → J → ℝ) : Prop :=
  ∀ h, c h + p h ⬝ᵥ θ h = rd_fz p f h ⬝ᵥ rd_prev θ θm1 h + y h

/-- **Definition 13.4.1** (Miao, p. 427). A Radner equilibrium with debt constraints: every
agent solves (13.1) subject to (13.11) and (13.13), and markets clear,
`∑ᵢ cⁱ_t = ȳ_t + θ̄_{−1} · (f_t − p_t)`, `∑ᵢ θⁱ_t = θ̄_{−1}` (at the root `f₀ = p₀` as in
(13.11b)). -/
def rd_RadnerDC (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (θm1 : ι → J → ℝ)
    (p f : List S → J → ℝ) (Dbar : ι → List S → ℝ) (c : ι → List S → ℝ)
    (θ : ι → List S → J → ℝ) : Prop :=
  (∀ i, rd_Solves (U i) (rd_SeqFeas p f (y i) (θm1 i) (rd_ThetaDC f (Dbar i))) (c i) (θ i)) ∧
    (∀ h, ∑ i, c i h = ∑ i, y i h + (rd_fz p f h - p h) ⬝ᵥ ∑ i, θm1 i) ∧
    ∀ h, ∑ i, θ i h = ∑ i, θm1 i

/-- A Radner equilibrium with borrowing constraints (13.14) (Miao, p. 428). -/
def rd_RadnerBC (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (θm1 : ι → J → ℝ)
    (p f : List S → J → ℝ) (Bbar : ι → List S → ℝ) (c : ι → List S → ℝ)
    (θ : ι → List S → J → ℝ) : Prop :=
  (∀ i, rd_Solves (U i) (rd_SeqFeas p f (y i) (θm1 i) (rd_ThetaBC p (Bbar i))) (c i) (θ i)) ∧
    (∀ h, ∑ i, c i h = ∑ i, y i h + (rd_fz p f h - p h) ⬝ᵥ ∑ i, θm1 i) ∧
    ∀ h, ∑ i, θ i h = ∑ i, θm1 i

omit [Fintype S] [Fintype J] in
/-- The carried-in portfolios sum to the carried-in aggregate portfolio. -/
theorem rd_prev_sum (θ : ι → List S → J → ℝ) (θm1 : ι → J → ℝ) (h : List S) :
    ∑ i, rd_prev (θ i) (θm1 i) h = rd_prev (∑ i, θ i) (∑ i, θm1 i) h := by
  cases h with
  | nil => rfl
  | cons s h => simp [rd_prev]

omit [Fintype S] in
/-- Miao, p. 427: summing the budget equalities with `∑ᵢ θⁱ_t = θ̄_{−1}` gives the goods-market
clearing condition of Definition 13.4.1. -/
theorem rd_goods_clearing (p f : List S → J → ℝ) (y : ι → List S → ℝ) (θm1 : ι → J → ℝ)
    (c : ι → List S → ℝ) (θ : ι → List S → J → ℝ)
    (hB : ∀ i, rd_BudgetEq p f (y i) (θm1 i) (c i) (θ i))
    (hθ : ∀ h, ∑ i, θ i h = ∑ i, θm1 i) (h : List S) :
    ∑ i, c i h = ∑ i, y i h + (rd_fz p f h - p h) ⬝ᵥ ∑ i, θm1 i := by
  have hsum := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hB i h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [← dotProduct_sum] at hsum
  rw [rd_prev_sum] at hsum
  have hprev : rd_prev (∑ i, θ i) (∑ i, θm1 i) h = ∑ i, θm1 i := by
    cases h with
    | nil => rfl
    | cons s g =>
      simp only [rd_prev]
      rw [← hθ g]
      simp
  rw [hprev, ← hθ h] at hsum
  rw [sub_dotProduct, ← hθ h]
  linarith

omit [Fintype S] [Fintype J] [Fintype ι] in
/-- **Definition 13.4.1**, remark (Miao, p. 428): when the security supply is zero, the
market-clearing condition is identical with the feasibility condition (13.2). -/
theorem definition_13_4_1 [Fintype J] [Fintype ι] (p f : List S → J → ℝ)
    (y : ι → List S → ℝ) (θm1 : ι → J → ℝ) (c : ι → List S → ℝ) (h0 : ∑ i, θm1 i = 0) :
    (∀ h, ∑ i, c i h = ∑ i, y i h + (rd_fz p f h - p h) ⬝ᵥ ∑ i, θm1 i) ↔
      ∀ h, ∑ i, c i h = ∑ i, y i h := by
  simp [h0]

/-- **(13.19)** (Miao, p. 432), in state prices `q⁰ = π Pr`. If `q` satisfies (13.16) and the
budget (13.11) holds, then at every node `sᵗ` and horizon `T`,
`∑_{j ≤ T} ∑ q c + ∑_{sᵗ⁺ᵀ} q (p · θ) ≤ q⁰_t (f_t · θ_{t−1}) + ∑_{j ≤ T} ∑ q y`. -/
theorem eq_13_19 {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (h : List S) (T : ℕ) :
    ∑ j ∈ Finset.range (T + 1), rd_dsum (fun g => q g * c g) h j +
        rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T ≤
      q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) +
        ∑ j ∈ Finset.range (T + 1), rd_dsum (fun g => q g * y g) h j := by
  have hpt : ∀ g, q g * c g + q g * (p g ⬝ᵥ θ g) ≤
      q g * (rd_fz p f g ⬝ᵥ rd_prev θ θm1 g) + q g * y g := by
    intro g
    rw [← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hB g) (hq.1 g).le
  induction T with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, rd_dsum_zero]
    exact hpt h
  | succ T ih =>
    rw [Finset.sum_range_succ (fun j => rd_dsum (fun g => q g * c g) h j) (T + 1),
      Finset.sum_range_succ (fun j => rd_dsum (fun g => q g * y g) h j) (T + 1)]
    have hV : rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T =
        rd_dsum (fun g => q g * (rd_fz p f g ⬝ᵥ rd_prev θ θm1 g)) h (T + 1) := by
      rw [rd_dsum_succ']
      exact rd_dsum_congr (fun g => rd_statePrice_dot hq g (θ g)) h T
    have hstep := rd_dsum_mono hpt h (T + 1)
    rw [rd_dsum_add, rd_dsum_add] at hstep
    linarith

/-- **(13.19)** in the book's form (Miao, p. 432), with conditional expectations and the
deflator `π = q⁰ / Pr`: `∑_{j≤T} E_t[π c] + E_t[π_{t+T} p_{t+T} · θ_{t+T}] ≤
π_t f_t · θ_{t−1} + ∑_{j≤T} E_t[π y]`. -/
theorem eq_13_19_E (T : RDTree S) {p f : List S → J → ℝ} {pd : List S → ℝ}
    (hq : rd_StatePrice p f (fun g => pd g * T.Pr g)) {y : List S → ℝ} {θm1 : J → ℝ}
    {c : List S → ℝ} {θ : List S → J → ℝ} (hB : rd_Budget p f y θm1 c θ) (h : List S)
    (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), rd_condE T (fun g => pd g * c g) h j +
        rd_condE T (fun g => pd g * (p g ⬝ᵥ θ g)) h n ≤
      pd h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) +
        ∑ j ∈ Finset.range (n + 1), rd_condE T (fun g => pd g * y g) h j := by
  have key := eq_13_19 hq hB h n
  have hP := T.pos h
  have e : ∀ X : List S → ℝ, ∀ j, rd_condE T (fun g => pd g * X g) h j =
      (T.Pr h)⁻¹ * rd_dsum (fun g => pd g * T.Pr g * X g) h j := by
    intro X j
    rw [rd_condE]
    congr 1
    exact rd_dsum_congr (fun g => by ring) h j
  simp only [e, ← Finset.mul_sum]
  have key' := mul_le_mul_of_nonneg_left key (inv_pos.2 hP).le
  rw [mul_add, mul_add] at key'
  have : (T.Pr h)⁻¹ * (pd h * T.Pr h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h)) =
      pd h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) := by
    field_simp
  linarith

/-- **(13.20)** (Miao, p. 432): (13.19) at the root,
`∑_{t≤T} E[π c] + E[π_T p_T · θ_T] ≤ π₀ p₀ · θ_{−1} + ∑_{t≤T} E[π y]`. -/
theorem eq_13_20 {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), rd_dsum (fun g => q g * c g) [] t +
        rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) [] T ≤
      q [] * (p [] ⬝ᵥ θm1) + ∑ t ∈ Finset.range (T + 1), rd_dsum (fun g => q g * y g) [] t :=
  eq_13_19 hq hB [] T

/-- The transversality condition (13.21), `lim_{T→∞} E[π_T p_T · θ_T] = 0`, in state prices.
(The book prints `T → 0`.) -/
def rd_TVC (q : List S → ℝ) (p : List S → J → ℝ) (θ : List S → J → ℝ) : Prop :=
  Tendsto (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) [] T) atTop (𝓝 0)

/-- The limit of (13.19) at a node under a vanishing lower bound on the date-`T` value: if
`∑ q (p · θ)` over `sᵗ⁺ᵀ | sᵗ` is at least `−e_T` with `e_T → 0`, then
`∑_j ∑ q c ≤ q_t f_t · θ_{t−1} + ∑_j ∑ q y`. -/
theorem rd_AD_of_lowerTail_at {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ}
    {θ : List S → J → ℝ} (hB : rd_Budget p f y θm1 c θ) (h : List S) {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hlow : ∀ T, -e T ≤ rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T)
    (hc : Summable fun j => rd_dsum (fun g => q g * c g) h j)
    (hy : Summable fun j => rd_dsum (fun g => q g * y g) h j) :
    ∑' j, rd_dsum (fun g => q g * c g) h j ≤
      q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) + ∑' j, rd_dsum (fun g => q g * y g) h j := by
  have hA := hc.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hY := hy.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hR : Tendsto (fun T => q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) +
      ∑ j ∈ Finset.range (T + 1), rd_dsum (fun g => q g * y g) h j + e T) atTop
      (𝓝 (q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) +
        ∑' j, rd_dsum (fun g => q g * y g) h j + 0)) :=
    (tendsto_const_nhds.add hY).add he
  rw [add_zero] at hR
  refine le_of_tendsto_of_tendsto' hA hR fun T => ?_
  have := eq_13_19 hq hB h T
  have := hlow T
  simp only [Function.comp_apply]
  linarith

/-- **(13.22)** under a vanishing lower bound on the date-`T` value. -/
theorem rd_AD_of_lowerTail {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ}
    {θ : List S → J → ℝ} (hB : rd_Budget p f y θm1 c θ) {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hlow : ∀ T, -e T ≤ rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) [] T)
    (hc : Summable fun t => rd_dsum (fun g => q g * c g) [] t)
    (hy : Summable fun t => rd_dsum (fun g => q g * y g) [] t) :
    ∑' t, rd_dsum (fun g => q g * c g) [] t ≤
      q [] * (p [] ⬝ᵥ θm1) + ∑' t, rd_dsum (fun g => q g * y g) [] t :=
  rd_AD_of_lowerTail_at hq hB [] he hlow hc hy

/-- **(13.22)** (Miao, p. 433): under the transversality condition (13.21), the limit of (13.20)
is the present-value budget `E ∑ πc ≤ π₀ p₀ · θ_{−1} + E ∑ πy`. -/
theorem eq_13_22 {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (hT : rd_TVC q p θ)
    (hc : Summable fun t => rd_dsum (fun g => q g * c g) [] t)
    (hy : Summable fun t => rd_dsum (fun g => q g * y g) [] t) :
    ∑' t, rd_dsum (fun g => q g * c g) [] t ≤
      q [] * (p [] ⬝ᵥ θm1) + ∑' t, rd_dsum (fun g => q g * y g) [] t := by
  refine rd_AD_of_lowerTail hq hB (e := fun T => |rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) [] T|)
    ?_ (fun T => neg_abs_le _) hc hy
  simpa using hT.abs

/-- **(13.23)** (Miao, p. 433): at a node `sᵗ`, under the transversality condition *conditional on
`sᵗ`*, `E_t ∑ π c ≤ π_t f_t · θ_{t−1} + E_t ∑ π y`. -/
theorem eq_13_23 {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (h : List S)
    (hT : Tendsto (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T) atTop (𝓝 0))
    (hc : Summable fun j => rd_dsum (fun g => q g * c g) h j)
    (hy : Summable fun j => rd_dsum (fun g => q g * y g) h j) :
    ∑' j, rd_dsum (fun g => q g * c g) h j ≤
      q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) + ∑' j, rd_dsum (fun g => q g * y g) h j := by
  refine rd_AD_of_lowerTail_at hq hB h
    (e := fun T => |rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T|) ?_ (fun T => neg_abs_le _) hc hy
  simpa using hT.abs

/-- A process whose date sums are absolutely summable has summable subtree sums at every node. -/
theorem rd_summable_subtree {F : List S → ℝ}
    (hF : Summable fun t => rd_dsum (fun g => |F g|) [] t) (h : List S) :
    Summable fun j => rd_dsum F h j := by
  refine Summable.of_norm_bounded ((summable_nat_add_iff h.length).2 hF) fun j => ?_
  rw [Real.norm_eq_abs, add_comm]
  exact (rd_abs_dsum_le _ _ _).trans (rd_dsum_le_root (fun g => abs_nonneg _) h j)

/-- **(13.22)** for a borrowing-constrained plan: if `p · θ ≥ −B` with `B` bounded and `q ∈ L¹`,
the budget (13.11) implies the present-value budget (13.22). -/
theorem rd_AD_of_BC {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    (hL : rd_L1 q) {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) {Bbar : List S → ℝ} (hBb : rd_Bdd Bbar)
    (hθ : θ ∈ rd_ThetaBC p Bbar) (hc : rd_Bdd c) (hy : rd_Bdd y) :
    ∑' t, rd_dsum (fun g => q g * c g) [] t ≤
      q [] * (p [] ⬝ᵥ θm1) + ∑' t, rd_dsum (fun g => q g * y g) [] t := by
  refine rd_AD_of_lowerTail hq hB (e := fun T => rd_dsum (fun g => q g * Bbar g) [] T)
    (rd_L1_mul_tendsto hL hBb) (fun T => ?_) (rd_L1_mul hL hc) (rd_L1_mul hL hy)
  rw [← rd_dsum_neg]
  refine rd_dsum_mono (fun g => ?_) _ _
  rw [← mul_neg]
  exact mul_le_mul_of_nonneg_left (hθ g) (hq.1 g).le

/-- **(13.22)** for a debt-constrained plan: if `f · θ ≥ −D` with `D` bounded and `q ∈ L¹`, the
budget (13.11) implies the present-value budget (13.22). -/
theorem rd_AD_of_DC {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    (hL : rd_L1 q) {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) {Dbar : List S → ℝ} (hDb : rd_Bdd Dbar)
    (hθ : θ ∈ rd_ThetaDC f Dbar) (hc : rd_Bdd c) (hy : rd_Bdd y) :
    ∑' t, rd_dsum (fun g => q g * c g) [] t ≤
      q [] * (p [] ⬝ᵥ θm1) + ∑' t, rd_dsum (fun g => q g * y g) [] t := by
  have hlim := (rd_L1_mul_tendsto hL hDb).comp (tendsto_add_atTop_nat 1)
  refine rd_AD_of_lowerTail hq hB (e := fun T => rd_dsum (fun g => q g * Dbar g) [] (T + 1))
    hlim (fun T => ?_) (rd_L1_mul hL hc) (rd_L1_mul hL hy)
  rw [← rd_dsum_neg, rd_dsum_succ']
  refine rd_dsum_mono (fun g => ?_) _ _
  rw [rd_statePrice_dot hq g]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [← mul_neg]
  exact mul_le_mul_of_nonneg_left (hθ g s) (hq.1 _).le

/-- The Arrow–Debreu budget (13.5): `∑ₜ ∑_{sᵗ} q⁰ c ≤ ∑ₜ ∑_{sᵗ} q⁰ y`. -/
def rd_ADBudget (q y c : List S → ℝ) : Prop :=
  ∑' t, rd_dsum (fun g => q g * c g) [] t ≤ ∑' t, rd_dsum (fun g => q g * y g) [] t

/-- Definition 13.3.1 in this setting: an Arrow–Debreu equilibrium `(q⁰, c)` with `q⁰ ∈ L¹`,
each `cⁱ` maximising `Uⁱ` over `L^∞₊` subject to (13.5), and (13.2). -/
def rd_ADEqm (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (q : List S → ℝ)
    (c : ι → List S → ℝ) : Prop :=
  rd_L1 q ∧ (∀ i, rd_SolvesC (U i) (fun c' => rd_LinfPos c' ∧ rd_ADBudget q (y i) c') (c i)) ∧
    ∀ h, ∑ i, c i h = ∑ i, y i h

/-- Feasible allocations (13.2) in `(L^∞₊)ᴵ`. -/
def rd_Feasible (y : ι → List S → ℝ) (c : ι → List S → ℝ) : Prop :=
  (∀ i, rd_LinfPos (c i)) ∧ ∀ h, ∑ i, c i h = ∑ i, y i h

/-- Pareto optimality (Miao, p. 417). -/
def rd_ParetoOptimal (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (c : ι → List S → ℝ) :
    Prop :=
  rd_Feasible y c ∧ ¬ ∃ c', rd_Feasible y c' ∧ (∀ i, U i (c i) ≤ U i (c' i)) ∧
    ∃ i, U i (c i) < U i (c' i)

/-- Raising consumption at the root by `ε` raises the date-sum value by `q(s⁰) ε`. -/
theorem rd_tsum_add_root {q c : List S → ℝ}
    (hc : Summable fun t => rd_dsum (fun g => q g * c g) [] t) (ε : ℝ) :
    ∑' t, rd_dsum (fun g => q g * (c g + if g = [] then ε else 0)) [] t =
      ∑' t, rd_dsum (fun g => q g * c g) [] t + q [] * ε := by
  classical
  have e : ∀ t, rd_dsum (fun g => q g * (c g + if g = [] then ε else 0)) [] t =
      rd_dsum (fun g => q g * c g) [] t + if t = 0 then q [] * ε else 0 := by
    intro t
    have : (fun g => q g * (c g + if g = [] then ε else 0)) =
        fun g => q g * c g + if g = [] then q [] * ε else 0 := by
      funext g
      split_ifs with hg
      · rw [hg]; ring
      · ring
    rw [this, rd_dsum_add, rd_dsum_ite]
    simp only [List.length_nil, eq_comm]
  simp only [e]
  rw [Summable.tsum_add hc ⟨_, hasSum_ite_eq 0 (q [] * ε)⟩, tsum_ite_eq]

/-- Theorem 13.3.1 (First Welfare Theorem) in this setting (Miao, p. 421), used on p. 433:
with strictly increasing utilities, positive state prices in `L¹` and bounded endowments, an
Arrow–Debreu equilibrium allocation is Pareto optimal. -/
theorem rd_first_welfare {U : ι → (List S → ℝ) → ℝ} {y : ι → List S → ℝ} {q : List S → ℝ}
    {c : ι → List S → ℝ} (hU : ∀ i, rd_StrictIncr (U i)) (hq : ∀ h, 0 < q h)
    (hy : ∀ i, rd_Bdd (y i)) (hAD : rd_ADEqm U y q c) : rd_ParetoOptimal U y c := by
  classical
  obtain ⟨hL, hopt, hclear⟩ := hAD
  refine ⟨⟨fun i => (hopt i).1.1, hclear⟩, ?_⟩
  rintro ⟨c', ⟨hc'f, hc'c⟩, hweak, i0, hstrict⟩
  have hs : ∀ i, Summable fun t => rd_dsum (fun g => q g * c' i g) [] t :=
    fun i => rd_L1_mul hL (hc'f i).1
  have hsy : ∀ i, Summable fun t => rd_dsum (fun g => q g * y i g) [] t :=
    fun i => rd_L1_mul hL (hy i)
  have hge : ∀ i, ∑' t, rd_dsum (fun g => q g * y i g) [] t ≤
      ∑' t, rd_dsum (fun g => q g * c' i g) [] t := by
    intro i
    by_contra hlt
    push Not at hlt
    set ε := (∑' t, rd_dsum (fun g => q g * y i g) [] t -
      ∑' t, rd_dsum (fun g => q g * c' i g) [] t) / q []
    have hε : 0 < ε := div_pos (by linarith) (hq [])
    set c'' : List S → ℝ := fun g => c' i g + if g = [] then ε else 0
    have hc'' : rd_LinfPos c'' := by
      obtain ⟨⟨M, hM⟩, h0⟩ := hc'f i
      refine ⟨⟨M + ε, fun g => ?_⟩, fun g => ?_⟩
      · simp only [c'']
        refine (abs_add_le _ _).trans (add_le_add (hM g) ?_)
        split_ifs <;> simp [abs_of_pos hε, hε.le]
      · simp only [c'']
        split_ifs <;> linarith [h0 g]
    have hbud : rd_ADBudget q (y i) c'' := by
      rw [rd_ADBudget, rd_tsum_add_root (hs i)]
      simp only [ε]
      rw [mul_div_cancel₀ _ (hq []).ne']
      linarith
    have hlt2 : U i (c' i) < U i c'' := by
      refine hU i _ _ (hc'f i) hc'' (fun g => ?_) ?_
      · simp only [c'']
        split_ifs <;> linarith
      · intro he
        have := congrFun he []
        simp only [c'', ↓reduceIte] at this
        linarith
    exact absurd ((hopt i).2 c'' ⟨hc'', hbud⟩) (not_le.2 ((hweak i).trans_lt hlt2))
  have hgt : ∑' t, rd_dsum (fun g => q g * y i0 g) [] t <
      ∑' t, rd_dsum (fun g => q g * c' i0 g) [] t := by
    by_contra hle
    push Not at hle
    exact absurd ((hopt i0).2 (c' i0) ⟨hc'f i0, hle⟩) (not_le.2 hstrict)
  have htot : ∑ i, ∑' t, rd_dsum (fun g => q g * y i g) [] t <
      ∑ i, ∑' t, rd_dsum (fun g => q g * c' i g) [] t :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨i0, Finset.mem_univ _, hgt⟩
  have hswap : ∀ x : ι → List S → ℝ, (∀ i, Summable fun t => rd_dsum (fun g => q g * x i g) [] t) →
      ∑ i, ∑' t, rd_dsum (fun g => q g * x i g) [] t =
        ∑' t, rd_dsum (fun g => q g * ∑ i, x i g) [] t := by
    intro x hx
    rw [← Summable.tsum_finsetSum fun i _ => hx i]
    refine tsum_congr fun t => ?_
    rw [← rd_dsum_finsetSum]
    exact rd_dsum_congr (fun g => by rw [Finset.mul_sum]) _ _
  rw [hswap _ hsy, hswap _ hs] at htot
  simp only [hc'c] at htot
  exact lt_irrefl _ htot

/-- **Definition 13.4.2** (Miao, p. 433). A competitive equilibrium with transversality
condition `((cⁱ, θⁱ), π, p) ∈ (L^∞₊)ᴵ × Θᴵ × L¹₊₊ × (L^∞₊)ᴶ` (here `π ∈ L¹` means
`q⁰ = π Pr ∈ L¹`): (i) each `(cⁱ, θⁱ)` maximises (13.1) subject to (13.11) and (13.21);
(ii) each `cⁱ` maximises (13.1) subject to (13.22); (iii) `(π, p)` satisfies (13.18)
(equivalently (13.16) for `q⁰ = π Pr`, `eq_13_18`); (iv) (13.2) and `∑ᵢ θⁱ_t = θ̄_{−1}`. -/
def rd_CETVC (T : RDTree S) (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ)
    (θm1 : ι → J → ℝ) (f : List S → J → ℝ) (c : ι → List S → ℝ) (θ : ι → List S → J → ℝ)
    (pd : List S → ℝ) (p : List S → J → ℝ) : Prop :=
  (∀ i, rd_LinfPos (c i)) ∧ rd_L1 (fun g => pd g * T.Pr g) ∧ (∀ h, 0 < pd h) ∧
    (∀ h j, 0 ≤ p h j) ∧ (∀ j, rd_Bdd fun h => p h j) ∧
    (∀ i, rd_Solves (U i) (fun c' θ' => rd_LinfPos c' ∧ rd_Budget p f (y i) (θm1 i) c' θ' ∧
      rd_TVC (fun g => pd g * T.Pr g) p θ') (c i) (θ i)) ∧
    (∀ i, rd_SolvesC (U i) (fun c' => rd_LinfPos c' ∧
      ∑' t, rd_dsum (fun g => pd g * T.Pr g * c' g) [] t ≤
        pd [] * T.Pr [] * (p [] ⬝ᵥ θm1 i) + ∑' t, rd_dsum (fun g => pd g * T.Pr g * y i g) [] t)
      (c i)) ∧
    rd_StatePrice p f (fun g => pd g * T.Pr g) ∧
    (∀ h, ∑ i, c i h = ∑ i, y i h) ∧ ∀ h, ∑ i, θ i h = ∑ i, θm1 i

/-- **Definition 13.4.2**, remark (Miao, p. 433): with zero initial holdings, the allocation of a
competitive equilibrium with transversality condition is an Arrow–Debreu equilibrium allocation
with state prices `q⁰ = π Pr` ((13.22) is (13.5) when `θ_{−1} = 0`). -/
theorem definition_13_4_2 (T : RDTree S) {U : ι → (List S → ℝ) → ℝ} {y : ι → List S → ℝ}
    {f : List S → J → ℝ} {c : ι → List S → ℝ} {θ : ι → List S → J → ℝ} {pd : List S → ℝ}
    {p : List S → J → ℝ} (hE : rd_CETVC T U y (fun _ => 0) f c θ pd p) :
    rd_ADEqm U y (fun g => pd g * T.Pr g) c := by
  obtain ⟨-, hL, -, -, -, -, hii, -, hclear, -⟩ := hE
  refine ⟨hL, fun i => ?_, hclear⟩
  simp only [dotProduct_zero, mul_zero, zero_add] at hii
  exact hii i

/-- Miao, p. 433: "and hence is Pareto optimal" (via `rd_first_welfare`). -/
theorem rd_cetvc_pareto (T : RDTree S) {U : ι → (List S → ℝ) → ℝ} {y : ι → List S → ℝ}
    {f : List S → J → ℝ} {c : ι → List S → ℝ} {θ : ι → List S → J → ℝ} {pd : List S → ℝ}
    {p : List S → J → ℝ} (hU : ∀ i, rd_StrictIncr (U i)) (hy : ∀ i, rd_Bdd (y i))
    (hE : rd_CETVC T U y (fun _ => 0) f c θ pd p) : rd_ParetoOptimal U y c :=
  rd_first_welfare hU (fun h => mul_pos (hE.2.2.1 h) (T.pos h)) hy (definition_13_4_2 T hE)

/-- The present value, at `sᵗ`, of `q x` over the strict descendants of `sᵗ`. -/
noncomputable def rd_W (q x : List S → ℝ) (h : List S) : ℝ :=
  ∑' j, rd_dsum (fun g => q g * x g) h (j + 1)

/-- The subtree sum splits into successors: `W(sᵗ) = ∑ₛ (q x (sᵗ, s) + W(sᵗ, s))`. -/
theorem rd_W_rec {q x : List S → ℝ}
    (hs : Summable fun t => rd_dsum (fun g => |q g * x g|) [] t) (h : List S) :
    rd_W q x h = ∑ s, (q (s :: h) * x (s :: h) + rd_W q x (s :: h)) := by
  rw [rd_W]
  simp only [rd_dsum_succ]
  rw [Summable.tsum_finsetSum fun s _ => rd_summable_subtree hs (s :: h)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [(rd_summable_subtree hs (s :: h)).tsum_eq_zero_add, rd_dsum_zero, rd_W]

/-- The date sums of `W` are tails of the summable date sums of `q x`. -/
theorem rd_W_dsum {q x : List S → ℝ}
    (hs : Summable fun t => rd_dsum (fun g => |q g * x g|) [] t) (T : ℕ) :
    rd_dsum (rd_W q x) [] T = ∑' j, rd_dsum (fun g => q g * x g) [] (j + (T + 1)) := by
  rw [rd_dsum]
  simp only [List.append_nil, rd_W]
  rw [← Summable.tsum_finsetSum fun l _ =>
    (summable_nat_add_iff 1).2 (rd_summable_subtree hs l)]
  refine tsum_congr fun j => ?_
  rw [show j + (T + 1) = T + (j + 1) by ring, rd_dsum_add_len, rd_dsum]
  simp only [List.append_nil]

/-- The date sums of `W` vanish in the limit. -/
theorem rd_W_tendsto {q x : List S → ℝ}
    (hs : Summable fun t => rd_dsum (fun g => |q g * x g|) [] t) :
    Tendsto (fun T => rd_dsum (rd_W q x) [] T) atTop (𝓝 0) := by
  simp only [rd_W_dsum hs]
  exact (tendsto_sum_nat_add fun t => rd_dsum (fun g => q g * x g) [] t).comp
    (tendsto_add_atTop_nat 1)

/-- The replicating portfolio at `sᵗ`: `D (DᵀD)⁻¹ z` with `z_s = x(sᵗ, s) + W(sᵗ, s)/q(sᵗ, s)`.
-/
noncomputable def rd_repl [DecidableEq S] (f : List S → J → ℝ) (q x : List S → ℝ)
    (h : List S) : J → ℝ :=
  Matrix.mulVec (rd_payoffMatrix f h *
      (Matrix.transpose (rd_payoffMatrix f h) * rd_payoffMatrix f h)⁻¹)
    fun s => x (s :: h) + rd_W q x (s :: h) / q (s :: h)

/-- With rank `S`, `D (DᵀD)⁻¹` is a right inverse of `Dᵀ`: the replicating portfolio pays
`z_s` in each successor state. -/
theorem rd_repl_payoff [DecidableEq S] (f : List S → J → ℝ) (q x : List S → ℝ) (h : List S)
    (hrank : (rd_payoffMatrix f h).rank = Fintype.card S) (s : S) :
    f (s :: h) ⬝ᵥ rd_repl f q x h = x (s :: h) + rd_W q x (s :: h) / q (s :: h) := by
  set D := rd_payoffMatrix f h
  have hdet : IsUnit (D.transpose * D).det := by
    have := (theorem_13_4_3_formula (p := fun g j => ∑ s', f (s' :: g) j)
      (q := fun _ => 1) ⟨fun _ => one_pos, fun g j => by simp⟩ h hrank).1
    exact (Matrix.isUnit_iff_isUnit_det _).1 this
  rw [← rd_payoffMatrix_transpose_mulVec, rd_repl, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    show rd_payoffMatrix f h = D from rfl, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- The replicating portfolio costs `W(sᵗ)/q(sᵗ)`: `q (p · θ) = W`. -/
theorem rd_repl_value [DecidableEq S] {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S)
    {x : List S → ℝ} (hs : Summable fun t => rd_dsum (fun g => |q g * x g|) [] t)
    (h : List S) : q h * (p h ⬝ᵥ rd_repl f q x h) = rd_W q x h := by
  rw [rd_statePrice_dot hq, rd_W_rec hs]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rd_repl_payoff f q x h (hrank h), mul_add, mul_div_cancel₀ _ (hq.1 _).ne']

/-- The replicating strategy finances `c` from `y` when `c` satisfies the Arrow–Debreu budget:
it satisfies (13.11) with `θ_{−1} = 0` (with equality at every node after the root) and the
transversality condition (13.21). -/
theorem rd_repl_budget [DecidableEq S] {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) (hL : rd_L1 q)
    (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) {c y : List S → ℝ}
    (hc : rd_Bdd c) (hy : rd_Bdd y) (hbud : rd_ADBudget q y c) :
    rd_Budget p f y 0 c (rd_repl f q fun g => c g - y g) ∧
      rd_TVC q p (rd_repl f q fun g => c g - y g) ∧
      ∀ s g, c (s :: g) + p (s :: g) ⬝ᵥ rd_repl f q (fun g => c g - y g) (s :: g) =
        f (s :: g) ⬝ᵥ rd_repl f q (fun g => c g - y g) g + y (s :: g) := by
  set x : List S → ℝ := fun g => c g - y g
  have hxs : Summable fun t => rd_dsum (fun g => |q g * x g|) [] t :=
    rd_L1_mul_abs hL (rd_bdd_sub hc hy)
  have hpv : ∀ h, p h ⬝ᵥ rd_repl f q x h = rd_W q x h / q h := fun h => by
    rw [← rd_repl_value hq hrank hxs h, mul_div_cancel_left₀ _ (hq.1 h).ne']
  have hcons : ∀ s g, c (s :: g) + p (s :: g) ⬝ᵥ rd_repl f q x (s :: g) =
      f (s :: g) ⬝ᵥ rd_repl f q x g + y (s :: g) := by
    intro s g
    rw [hpv, rd_repl_payoff f q x g (hrank g)]
    simp only [x]
    ring
  refine ⟨fun h => ?_, ?_, hcons⟩
  · cases h with
    | nil =>
      rw [hpv]
      simp only [rd_fz, rd_prev, dotProduct_zero, zero_add]
      rw [rd_ADBudget] at hbud
      have hsum : ∑' t, rd_dsum (fun g => q g * x g) [] t = q [] * x [] + rd_W q x [] := by
        rw [(rd_summable_subtree hxs []).tsum_eq_zero_add, rd_dsum_zero, rd_W]
      have hsub : ∑' t, rd_dsum (fun g => q g * x g) [] t =
          ∑' t, rd_dsum (fun g => q g * c g) [] t - ∑' t, rd_dsum (fun g => q g * y g) [] t := by
        rw [← Summable.tsum_sub (rd_L1_mul hL hc) (rd_L1_mul hL hy)]
        refine tsum_congr fun t => ?_
        rw [← rd_dsum_sub]
        exact rd_dsum_congr (fun g => by simp only [x]; ring) _ _
      have hq0 := hq.1 []
      have hW : rd_W q x [] / q [] ≤ -(x []) := by
        rw [div_le_iff₀ hq0]
        linarith
      simp only [x] at hW
      linarith
    | cons s g => exact (hcons s g).le
  · have e : (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ rd_repl f q x g)) [] T) =
        fun T => rd_dsum (rd_W q x) [] T :=
      funext fun T => rd_dsum_congr (fun g => rd_repl_value hq hrank hxs g) [] T
    rw [rd_TVC, e]
    exact rd_W_tendsto hxs

/-- With market clearing, the replicating strategies sum to zero. -/
theorem rd_repl_sum_zero [DecidableEq S] (f : List S → J → ℝ) {q : List S → ℝ} (hL : rd_L1 q)
    {c y : ι → List S → ℝ} (hcb : ∀ i, rd_Bdd (c i)) (hy : ∀ i, rd_Bdd (y i))
    (hclear : ∀ h, ∑ i, c i h = ∑ i, y i h) (h : List S) :
    ∑ i, rd_repl f q (fun g => c i g - y i g) h = 0 := by
  have hxs : ∀ i, Summable fun t => rd_dsum (fun g => |q g * (c i g - y i g)|) [] t :=
    fun i => rd_L1_mul_abs hL (rd_bdd_sub (hcb i) (hy i))
  have hW0 : ∀ g, ∑ i, rd_W q (fun g => c i g - y i g) g = 0 := by
    intro g
    simp only [rd_W]
    rw [← Summable.tsum_finsetSum fun i _ =>
      (summable_nat_add_iff 1).2 (rd_summable_subtree (hxs i) g)]
    have : ∀ j, ∑ i, rd_dsum (fun g => q g * (c i g - y i g)) g (j + 1) = 0 := by
      intro j
      rw [← rd_dsum_finsetSum]
      have : (fun g => ∑ i, q g * (c i g - y i g)) = fun _ => 0 := by
        funext g
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, hclear g, sub_self, mul_zero]
      rw [this]
      simp [rd_dsum]
    simp only [this, tsum_zero]
  simp only [rd_repl]
  rw [← Matrix.mulVec_sum]
  refine (congrArg _ ?_).trans (Matrix.mulVec_zero _)
  funext s
  simp only [Finset.sum_apply, Pi.zero_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hclear (s :: h), sub_self, zero_add, div_eq_mul_inv, ← Finset.sum_mul, hW0, zero_mul]

/-- Miao, pp. 433–434 (the step after the Second Welfare Theorem in the claim that Pareto optima
are supported): an Arrow–Debreu equilibrium `(q⁰, c)` with `q⁰ > 0` in `L¹`, bounded endowments,
zero initial holdings, securities of rank `S` at every node priced by `q⁰` through (13.16), and
`p ∈ (L^∞₊)ᴶ`, is a competitive equilibrium with transversality condition, with deflator
`π = q⁰/Pr` and replicating strategies `θⁱ` with `f_t · θⁱ_{t−1} − p_t · θⁱ_t = cⁱ_t − yⁱ_t`. -/
theorem rd_ad_cetvc [DecidableEq S] (T : RDTree S) {U : ι → (List S → ℝ) → ℝ}
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} {p f : List S → J → ℝ}
    (hAD : rd_ADEqm U y q c) (hy : ∀ i, rd_Bdd (y i)) (hq : rd_StatePrice p f q)
    (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) (hp0 : ∀ h j, 0 ≤ p h j)
    (hpb : ∀ j, rd_Bdd fun h => p h j) :
    rd_CETVC T U y (fun _ => 0) f c (fun i => rd_repl f q fun g => c i g - y i g)
      (fun g => q g / T.Pr g) p := by
  obtain ⟨hL, hopt, hclear⟩ := hAD
  have hqpd : ∀ g, q g / T.Pr g * T.Pr g = q g := fun g => div_mul_cancel₀ _ (T.pos g).ne'
  simp only [rd_CETVC, hqpd]
  have hcb : ∀ i, rd_Bdd (c i) := fun i => (hopt i).1.1.1
  -- every plan satisfying (13.11) and (13.21) satisfies the Arrow–Debreu budget
  have hseqAD : ∀ i c' θ', rd_LinfPos c' → rd_Budget p f (y i) 0 c' θ' → rd_TVC q p θ' →
      rd_ADBudget q (y i) c' := by
    intro i c' θ' hc' hB hT
    have := eq_13_22 hq hB hT (rd_L1_mul hL hc'.1) (rd_L1_mul hL (hy i))
    simpa [rd_ADBudget] using this
  have hfeas : ∀ i, rd_LinfPos (c i) ∧ rd_Budget p f (y i) 0 (c i)
      (rd_repl f q fun g => c i g - y i g) ∧ rd_TVC q p (rd_repl f q fun g => c i g - y i g) :=
    fun i => ⟨(hopt i).1.1, (rd_repl_budget hq hL hrank (hcb i) (hy i) (hopt i).1.2).1,
      (rd_repl_budget hq hL hrank (hcb i) (hy i) (hopt i).1.2).2.1⟩
  refine ⟨fun i => (hopt i).1.1, hL, fun h => div_pos (hq.1 h) (T.pos h), hp0, hpb,
    fun i => ⟨hfeas i, fun c' θ' ⟨hc', hB, hT⟩ => (hopt i).2 c' ⟨hc', hseqAD i c' θ' hc' hB hT⟩⟩,
    fun i => ⟨⟨(hopt i).1.1, by simpa [rd_ADBudget] using (hopt i).1.2⟩,
      fun c' ⟨hc', hb⟩ => (hopt i).2 c' ⟨hc', by simpa [rd_ADBudget] using hb⟩⟩,
    hq, hclear, fun h => ?_⟩
  simp only [Finset.sum_const_zero]
  exact rd_repl_sum_zero f hL hcb hy hclear h

/-- **(13.24)** (Miao, p. 434): under (13.23)'s hypotheses and `c ≥ 0`, agent `i`'s debt cannot
exceed the present value of current and future endowments,
`f_t · θ_{t−1} ≥ −(1/π_t) E_t ∑_j π_{t+j} y_{t+j}`. -/
theorem eq_13_24 {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (hc0 : ∀ g, 0 ≤ c g) (h : List S)
    (hT : Tendsto (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T) atTop (𝓝 0))
    (hc : Summable fun j => rd_dsum (fun g => q g * c g) h j)
    (hy : Summable fun j => rd_dsum (fun g => q g * y g) h j) :
    -((q h)⁻¹ * ∑' j, rd_dsum (fun g => q g * y g) h j) ≤
      rd_fz p f h ⬝ᵥ rd_prev θ θm1 h := by
  have key := eq_13_23 hq hB h hT hc hy
  have hnn : 0 ≤ ∑' j, rd_dsum (fun g => q g * c g) h j :=
    tsum_nonneg fun j => rd_dsum_nonneg (fun g => mul_nonneg (hq.1 g).le (hc0 g)) h j
  have hqh := hq.1 h
  have h1 : -∑' j, rd_dsum (fun g => q g * y g) h j ≤ q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) := by
    linarith
  calc -((q h)⁻¹ * ∑' j, rd_dsum (fun g => q g * y g) h j)
      = (q h)⁻¹ * -∑' j, rd_dsum (fun g => q g * y g) h j := by ring
    _ ≤ (q h)⁻¹ * (q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hqh.le)
    _ = rd_fz p f h ⬝ᵥ rd_prev θ θm1 h := by field_simp

/-- The natural debt limit `D̄_t = (1/π_t) E_t ∑_j π_{t+j} y_{t+j}` (Miao, p. 434), in state
prices. -/
noncomputable def rd_naturalDebtLimit (q y : List S → ℝ) (h : List S) : ℝ :=
  (q h)⁻¹ * ∑' j, rd_dsum (fun g => q g * y g) h j

/-- Miao, p. 435: under the natural debt limit, the debt constraint never binds when optimal
consumption is strictly positive (the inequality (13.24) is strict). -/
theorem rd_naturalDebt_nonbinding {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ}
    {θ : List S → J → ℝ} (hB : rd_Budget p f y θm1 c θ) (hc0 : ∀ g, 0 ≤ c g) (h : List S)
    (hcpos : 0 < c h)
    (hT : Tendsto (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T) atTop (𝓝 0))
    (hc : Summable fun j => rd_dsum (fun g => q g * c g) h j)
    (hy : Summable fun j => rd_dsum (fun g => q g * y g) h j) :
    -rd_naturalDebtLimit q y h < rd_fz p f h ⬝ᵥ rd_prev θ θm1 h := by
  have key := eq_13_23 hq hB h hT hc hy
  have hnn : q h * c h ≤ ∑' j, rd_dsum (fun g => q g * c g) h j := by
    have := hc.le_tsum 0 (fun j _ => rd_dsum_nonneg (fun g => mul_nonneg (hq.1 g).le (hc0 g)) h j)
    rwa [rd_dsum_zero] at this
  have hpos : 0 < q h * c h := mul_pos (hq.1 h) hcpos
  have hqh := hq.1 h
  have h1 : -∑' j, rd_dsum (fun g => q g * y g) h j < q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) := by
    linarith
  rw [rd_naturalDebtLimit]
  calc -((q h)⁻¹ * ∑' j, rd_dsum (fun g => q g * y g) h j)
      = (q h)⁻¹ * -∑' j, rd_dsum (fun g => q g * y g) h j := by ring
    _ < (q h)⁻¹ * (q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h)) :=
        mul_lt_mul_of_pos_left h1 (inv_pos.2 hqh)
    _ = rd_fz p f h ⬝ᵥ rd_prev θ θm1 h := by field_simp

/-- The natural borrowing limit (Miao, p. 435): by (13.18), `θ_{t−1} · p_{t−1} =
(1/π_{t−1}) E_{t−1}[π_t f_t · θ_{t−1}]`, and by (13.24) at each successor this is at least
`−(1/π_{t−1}) ∑ₛ E_t ∑_j π_{t+j} y_{t+j}`. -/
theorem rd_naturalBorrowing {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (hc0 : ∀ g, 0 ≤ c g) (g : List S)
    (hT : ∀ s, Tendsto (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) (s :: g) T) atTop (𝓝 0))
    (hc : ∀ s, Summable fun j => rd_dsum (fun g => q g * c g) (s :: g) j)
    (hy : ∀ s, Summable fun j => rd_dsum (fun g => q g * y g) (s :: g) j) :
    q g * (p g ⬝ᵥ θ g) = ∑ s, q (s :: g) * (f (s :: g) ⬝ᵥ θ g) ∧
      -(q g)⁻¹ * ∑ s, ∑' j, rd_dsum (fun g => q g * y g) (s :: g) j ≤ p g ⬝ᵥ θ g := by
  refine ⟨rd_statePrice_dot hq g (θ g), ?_⟩
  have hqg := hq.1 g
  have hb : ∀ s, -∑' j, rd_dsum (fun g => q g * y g) (s :: g) j ≤
      q (s :: g) * (f (s :: g) ⬝ᵥ θ g) := by
    intro s
    have := eq_13_24 hq hB hc0 (s :: g) (hT s) (hc s) (hy s)
    simp only [rd_fz, rd_prev] at this
    have hqs := hq.1 (s :: g)
    have := mul_le_mul_of_nonneg_left this hqs.le
    rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hqs.ne', one_mul] at this
    exact this
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hb s
  rw [Finset.sum_neg_distrib, ← rd_statePrice_dot hq g] at hsum
  calc -(q g)⁻¹ * ∑ s, ∑' j, rd_dsum (fun g => q g * y g) (s :: g) j
      = (q g)⁻¹ * -∑ s, ∑' j, rd_dsum (fun g => q g * y g) (s :: g) j := by ring
    _ ≤ (q g)⁻¹ * (q g * (p g ⬝ᵥ θ g)) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hqg.le)
    _ = p g ⬝ᵥ θ g := by field_simp

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# First-order conditions of the sequential problem

Miao, §13.4, p. 432 (the Arrow security prices from first-order conditions) and the first-order
conditions of Exercise 13.4, p. 452, for the discounted expected utility (13.1).

* `rd_EU_pert`: the change in (13.1) when consumption moves at a node and its successors only.
* `rd_euler_dir`: if `(c, θ)` is optimal and buying `ε d` more at `sᵗ` (for small `ε > 0`)
  keeps the strategy admissible, then the one-sided derivative is nonpositive:
  `−u′(cₜ) pₜ · d + β ∑ₛ Pr(s | sᵗ) u′(c_{t+1}) f_{t+1} · d ≤ 0`. Two-sided feasibility gives the
  Euler equation (`rd_euler_eq`).
* Arrow securities (p. 432): `rd_arrow_price`, `Q_t(s′|sᵗ) = β u′(c_{t+1}(sᵗ, s′)) Pr(s′|sᵗ)/
  u′(c_t(sᵗ))`, the same for every agent (`rd_arrow_price_common`).
* `rd_statePrice_of_euler`: the Euler equations make `q⁰_t = βᵗ Pr u′(c_t)/u′(c₀)` a state price
  process ((13.7) with (13.16)).
* **Exercise 13.4** (p. 452): first-order conditions for the three economies — borrowing
  constraints (`ex_13_4_BC_foc`), short-sales constraints (`ex_13_4_SC_foc`), debt constraints
  (`ex_13_4_DC_foc`, with rank `S`) — and their sufficiency together with the transversality
  conditions (13.39), (13.40), (13.38) (`ex_13_4_BC_suff`, `ex_13_4_SC_suff`, `ex_13_4_DC_suff`),
  and the equilibrium version (`ex_13_4_BC_eqm`). Necessity of the transversality conditions is
  not formalised.
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J : Type*} [Fintype S] [Fintype J]

omit [Fintype S] in
/-- The localised strategy `rd_loc d h` pays `−pₜ · d` at `sᵗ`. -/
theorem rd_net_loc_self [DecidableEq S] (p f : List S → J → ℝ) (d : J → ℝ) (h : List S) :
    rd_net p f 0 (rd_loc d h) h = -(p h ⬝ᵥ d) := by
  cases h with
  | nil => simp [rd_net, rd_loc, rd_prev]
  | cons s g =>
    have : g ≠ s :: g := fun e => by simpa using congrArg List.length e
    simp [rd_net, rd_loc, rd_prev, this]

omit [Fintype S] in
/-- The localised strategy pays `f_{t+1}(sᵗ, s) · d` at the successor `(sᵗ, s)`. -/
theorem rd_net_loc_child [DecidableEq S] (p f : List S → J → ℝ) (d : J → ℝ) (h : List S)
    (s : S) : rd_net p f 0 (rd_loc d h) (s :: h) = f (s :: h) ⬝ᵥ d := by
  have : s :: h ≠ h := fun e => by simpa using congrArg List.length e
  simp [rd_net, rd_loc, rd_prev, rd_fz, this]

omit [Fintype S] in
/-- The localised strategy pays nothing elsewhere. -/
theorem rd_net_loc_other [DecidableEq S] (p f : List S → J → ℝ) (d : J → ℝ) (h g : List S)
    (hg : g ≠ h) (hg' : ∀ s, g ≠ s :: h) : rd_net p f 0 (rd_loc d h) g = 0 := by
  cases g with
  | nil => simp [rd_net, rd_loc, rd_prev, hg]
  | cons s g' =>
    have : g' ≠ h := by
      rintro rfl
      exact hg' s rfl
    simp [rd_net, rd_loc, rd_prev, hg, this]

/-- The localised strategy's cash flows are bounded. -/
theorem rd_net_loc_bdd [DecidableEq S] (p f : List S → J → ℝ) (d : J → ℝ) (h : List S)
    (g : List S) : |rd_net p f 0 (rd_loc d h) g| ≤ |p h ⬝ᵥ d| + ∑ s, |f (s :: h) ⬝ᵥ d| := by
  have h0 : 0 ≤ ∑ s, |f (s :: h) ⬝ᵥ d| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hgh : g = h
  · rw [hgh, rd_net_loc_self, abs_neg]
    linarith
  · by_cases hc : ∃ s, g = s :: h
    · obtain ⟨s, rfl⟩ := hc
      rw [rd_net_loc_child]
      have := Finset.single_le_sum (f := fun s => |f (s :: h) ⬝ᵥ d|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
      linarith [abs_nonneg (p h ⬝ᵥ d)]
    · push Not at hc
      rw [rd_net_loc_other p f d h g hgh hc, abs_zero]
      positivity

omit [Fintype S] [Fintype J] in
/-- Adding `ε` times the localised strategy to the carried-in portfolio. -/
theorem rd_prev_add_loc [DecidableEq S] (θ : List S → J → ℝ) (θm1 : J → ℝ) (ε : ℝ)
    (d : J → ℝ) (h g : List S) :
    rd_prev (θ + ε • rd_loc d h) θm1 g = rd_prev θ θm1 g + ε • rd_prev (rd_loc d h) 0 g := by
  cases g with
  | nil => simp [rd_prev]
  | cons s g => rfl

/-- The change in the expected utility (13.1) when consumption changes only at `sᵗ` and its
successors. -/
theorem rd_EU_pert (T : RDTree S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) {c c' : List S → ℝ} (hc : rd_LinfPos c)
    (hc' : rd_LinfPos c') (h : List S) (hsupp : ∀ g, g ≠ h → (∀ s, g ≠ s :: h) → c' g = c g) :
    rd_EU T β u c' - rd_EU T β u c =
      β ^ h.length * (T.Pr h * (u (c' h) - u (c h))) +
        β ^ (h.length + 1) * ∑ s, T.Pr (s :: h) * (u (c' (s :: h)) - u (c (s :: h))) := by
  classical
  obtain ⟨K, hK⟩ := rd_abs_u_le hu hc
  obtain ⟨K', hK'⟩ := rd_abs_u_le hu hc'
  set G : List S → ℝ := fun g => T.Pr g * (u (c' g) - u (c g)) with hGdef
  have hne : ∀ s, h ≠ s :: h := fun s e => by simpa using congrArg List.length e
  have hG : ∀ g, G g = (if g = h then G h else 0) + ∑ s, if g = s :: h then G (s :: h) else 0 := by
    intro g
    by_cases hgh : g = h
    · subst hgh
      simp [hne]
    · by_cases hcs : ∃ s, g = s :: h
      · obtain ⟨s, rfl⟩ := hcs
        simp only [hgh, ↓reduceIte, zero_add, List.cons.injEq, and_true]
        rw [Finset.sum_ite_eq]
        simp
      · push Not at hcs
        simp [hgh, hcs, G, hsupp g hgh hcs]
  have hd : ∀ t, rd_dsum G [] t = (if h.length = t then G h else 0) +
      ∑ s, if h.length + 1 = t then G (s :: h) else 0 := by
    intro t
    rw [rd_dsum_congr hG, rd_dsum_add, rd_dsum_finsetSum, rd_dsum_ite]
    simp only [rd_dsum_ite, List.length_cons]
  rw [rd_EU, rd_EU, ← Summable.tsum_sub (rd_EU_summable T hβ0 hβ1 u hK')
    (rd_EU_summable T hβ0 hβ1 u hK)]
  have e1 : ∀ t, β ^ t * rd_dsum (fun g => T.Pr g * u (c' g)) [] t -
      β ^ t * rd_dsum (fun g => T.Pr g * u (c g)) [] t =
      (if t = h.length then β ^ h.length * G h else 0) +
        if t = h.length + 1 then β ^ (h.length + 1) * ∑ s, G (s :: h) else 0 := by
    intro t
    rw [← mul_sub, ← rd_dsum_sub]
    have : rd_dsum (fun g => T.Pr g * u (c' g) - T.Pr g * u (c g)) [] t = rd_dsum G [] t :=
      rd_dsum_congr (fun g => by simp only [G]; ring) _ _
    rw [this, hd]
    by_cases h1 : t = h.length
    · subst h1
      simp
    · by_cases h2 : t = h.length + 1
      · subst h2
        simp
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  simp only [e1]
  rw [Summable.tsum_add (hasSum_ite_eq _ _).summable (hasSum_ite_eq _ _).summable,
    tsum_ite_eq, tsum_ite_eq]

/-- Miao, p. 432 (first-order conditions), one-sided form. If `(c, θ)` maximises (13.1) subject
to (13.11) and `θ ∈ Θᵃ`, consumption is positive at `sᵗ` and its successors, and adding `ε d`
to the portfolio at `sᵗ` keeps the strategy admissible for small `ε > 0`, then
`−u′(cₜ) pₜ · d + β ∑ₛ Pr(s | sᵗ) u′(c_{t+1}) f_{t+1} · d ≤ 0`. -/
theorem rd_euler_dir [DecidableEq S] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Θa : Set (List S → J → ℝ)}
    {c : List S → ℝ} {θ : List S → J → ℝ}
    (hsol : rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 Θa) c θ)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h)) (d : J → ℝ)
    (hΘ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), θ + ε • rd_loc d h ∈ Θa) :
    -(u' (c h) * (p h ⬝ᵥ d)) +
        β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * (f (s :: h) ⬝ᵥ d)) ≤ 0 := by
  set N := rd_net p f 0 (rd_loc d h)
  set a := h.length
  set ψ : ℝ → ℝ := fun ε => β ^ a * (T.Pr h * (u (c h + ε * -(p h ⬝ᵥ d)) - u (c h))) +
    β ^ (a + 1) * ∑ s, T.Pr (s :: h) * (u (c (s :: h) + ε * (f (s :: h) ⬝ᵥ d)) - u (c (s :: h)))
  set D := β ^ a * (T.Pr h * (u' (c h) * -(p h ⬝ᵥ d))) +
    β ^ (a + 1) * ∑ s, T.Pr (s :: h) * (u' (c (s :: h)) * (f (s :: h) ⬝ᵥ d))
  have hlin : ∀ (x k : ℝ), 0 < x →
      HasDerivAt (fun ε : ℝ => u (x + ε * k)) (u' x * k) 0 := by
    intro x k hx
    have hl : HasDerivAt (fun ε : ℝ => x + ε * k) k 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_add x
    have hu0 : HasDerivAt u (u' x) (x + 0 * k) := by simpa using hd x hx
    exact hu0.comp (0 : ℝ) hl
  have hψ : HasDerivAt ψ D 0 := by
    have h1 := (((hlin (c h) (-(p h ⬝ᵥ d)) hch).sub_const (u (c h))).const_mul
      (T.Pr h)).const_mul (β ^ a)
    have h2 := (HasDerivAt.fun_sum (u := Finset.univ) fun s _ =>
      ((hlin (c (s :: h)) (f (s :: h) ⬝ᵥ d) (hcs s)).sub_const (u (c (s :: h)))).const_mul
        (T.Pr (s :: h))).const_mul (β ^ (a + 1))
    exact h1.add h2
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ψ ε ≤ 0 := by
    have hc1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c h + ε * -(p h ⬝ᵥ d) := by
      have : Tendsto (fun ε : ℝ => c h + ε * -(p h ⬝ᵥ d)) (𝓝 0) (𝓝 (c h)) := by
        simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (-(p h ⬝ᵥ d))).const_add (c h)
      exact this.eventually (lt_mem_nhds hch)
    have hc2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, 0 < c (s :: h) + ε * (f (s :: h) ⬝ᵥ d) := by
      refine Filter.eventually_all.2 fun s => ?_
      have : Tendsto (fun ε : ℝ => c (s :: h) + ε * (f (s :: h) ⬝ᵥ d)) (𝓝 0)
          (𝓝 (c (s :: h))) := by
        simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (f (s :: h) ⬝ᵥ d)).const_add
          (c (s :: h))
      exact this.eventually (lt_mem_nhds (hcs s))
    filter_upwards [hΘ, nhdsWithin_le_nhds hc1, nhdsWithin_le_nhds hc2] with ε hθε h1 h2
    set c' : List S → ℝ := fun g => c g + ε * N g with hc'def
    have hne : ∀ s, h ≠ s :: h := fun s e => by simpa using congrArg List.length e
    have hc'h : c' h = c h + ε * -(p h ⬝ᵥ d) := by simp only [c', N, rd_net_loc_self]
    have hc's : ∀ s, c' (s :: h) = c (s :: h) + ε * (f (s :: h) ⬝ᵥ d) := fun s => by
      simp only [c', N, rd_net_loc_child]
    have hc'o : ∀ g, g ≠ h → (∀ s, g ≠ s :: h) → c' g = c g := fun g hg hg' => by
      simp only [c', N, rd_net_loc_other p f d h g hg hg', mul_zero, add_zero]
    have hfeas : rd_SeqFeas p f y θm1 Θa c' (θ + ε • rd_loc d h) := by
      obtain ⟨⟨⟨M, hM⟩, h0⟩, hB, -⟩ := hsol.1
      have hBd := rd_net_loc_bdd p f d h
      refine ⟨⟨⟨M + |ε| * (|p h ⬝ᵥ d| + ∑ s, |f (s :: h) ⬝ᵥ d|), fun g => ?_⟩, fun g => ?_⟩,
        ?_, hθε⟩
      · simp only [c']
        refine (abs_add_le _ _).trans (add_le_add (hM g) ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hBd g) (abs_nonneg ε)
      · by_cases hgh : g = h
        · rw [hgh, hc'h]
          exact h1.le
        · by_cases hcs' : ∃ s, g = s :: h
          · obtain ⟨s, rfl⟩ := hcs'
            rw [hc's]
            exact (h2 s).le
          · push Not at hcs'
            rw [hc'o g hgh hcs']
            exact h0 g
      · rw [rd_budget_iff_net]
        intro g
        have hn := (rd_budget_iff_net p f y θm1 c θ).1 hB g
        simp only [rd_net, rd_prev_add_loc, dotProduct_add, dotProduct_smul, smul_eq_mul,
          Pi.add_apply, Pi.smul_apply] at hn ⊢
        simp only [c', N, rd_net]
        nlinarith [hn]
    have hle := hsol.2 _ _ hfeas
    have hpert := rd_EU_pert T hβ0.le hβ1 hu hsol.1.1 hfeas.1 h hc'o
    rw [hc'h] at hpert
    simp only [hc's] at hpert
    simp only [ψ]
    linarith
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hslope := hψ.tendsto_slope_zero_right
  have hDle : D ≤ 0 := by
    refine le_of_tendsto hslope ?_
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
    rw [zero_add, hψ0, sub_zero, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt htpos)) ht
  have hPr := T.pos h
  have hD : D = β ^ a * T.Pr h * (-(u' (c h) * (p h ⬝ᵥ d)) +
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * (f (s :: h) ⬝ᵥ d))) := by
    simp only [D, Finset.mul_sum, mul_add]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun s _ => ?_
      simp only [rd_condPr, pow_succ]
      field_simp
  rw [hD] at hDle
  have hpos : 0 < β ^ a * T.Pr h := mul_pos (pow_pos hβ0 a) hPr
  by_contra hcon
  push Not at hcon
  exact absurd hDle (not_le.2 (mul_pos hpos hcon))

/-- The marginal value of a portfolio direction: `−u′(cₜ) pₜ · d + β E_t[u′(c_{t+1}) f_{t+1} · d]`.
-/
noncomputable def rd_Phi (T : RDTree S) (β : ℝ) (u' : ℝ → ℝ) (p f : List S → J → ℝ)
    (c : List S → ℝ) (h : List S) (d : J → ℝ) : ℝ :=
  -(u' (c h) * (p h ⬝ᵥ d)) + β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * (f (s :: h) ⬝ᵥ d))

/-- `rd_Phi` is linear in the direction. -/
theorem rd_Phi_eq (T : RDTree S) (β : ℝ) (u' : ℝ → ℝ) (p f : List S → J → ℝ) (c : List S → ℝ)
    (h : List S) (d : J → ℝ) :
    rd_Phi T β u' p f c h d =
      ∑ j, (-(u' (c h) * p h j) +
        β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j)) * d j := by
  simp only [rd_Phi, dotProduct, Finset.mul_sum, Finset.sum_add_distrib, add_mul,
    Finset.sum_mul, ← Finset.sum_neg_distrib, neg_mul]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring

/-- `rd_Phi` of the negated direction. -/
theorem rd_Phi_neg (T : RDTree S) (β : ℝ) (u' : ℝ → ℝ) (p f : List S → J → ℝ) (c : List S → ℝ)
    (h : List S) (d : J → ℝ) : rd_Phi T β u' p f c h (-d) = -rd_Phi T β u' p f c h d := by
  simp only [rd_Phi_eq, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- **Euler equation** (Miao, p. 432). If adding `±ε d` at `sᵗ` keeps the strategy admissible for
small `ε`, the marginal value of `d` is zero:
`u′(cₜ) pₜ · d = β E_t[u′(c_{t+1}) f_{t+1} · d]`. -/
theorem rd_euler_eq [DecidableEq S] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Θa : Set (List S → J → ℝ)}
    {c : List S → ℝ} {θ : List S → J → ℝ}
    (hsol : rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 Θa) c θ)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h)) (d : J → ℝ)
    (hΘ : ∀ᶠ ε in 𝓝 (0 : ℝ), θ + ε • rd_loc d h ∈ Θa) : rd_Phi T β u' p f c h d = 0 := by
  have h1 := rd_euler_dir T hβ0 hβ1 hu hd hsol h hch hcs d (nhdsWithin_le_nhds hΘ)
  have hΘ' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), θ + ε • rd_loc (-d) h ∈ Θa := by
    have : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_id.neg : Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 (-0))).mono_left
        nhdsWithin_le_nhds
    filter_upwards [this.eventually hΘ] with ε hε
    have e : (-ε) • rd_loc d h = ε • rd_loc (-d) h := by
      funext g j
      simp [rd_loc]
      split_ifs <;> simp
    rwa [e] at hε
  have h2 := rd_euler_dir T hβ0 hβ1 hu hd hsol h hch hcs (-d) hΘ'
  have h1' : rd_Phi T β u' p f c h d ≤ 0 := h1
  have h2' : rd_Phi T β u' p f c h (-d) ≤ 0 := h2
  rw [rd_Phi_neg] at h2'
  linarith

omit [Fintype S] in
/-- Feasibility near `0` of the perturbed debt-constrained strategy when the debt constraints at
the successors of `sᵗ` are slack. -/
theorem rd_DC_slack [Finite S] [DecidableEq S] {f : List S → J → ℝ} {Dbar : List S → ℝ}
    {θ : List S → J → ℝ} (hθ : θ ∈ rd_ThetaDC f Dbar) (h : List S)
    (hslack : ∀ s, -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h) (d : J → ℝ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), θ + ε • rd_loc d h ∈ rd_ThetaDC f Dbar := by
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h + ε * (f (s :: h) ⬝ᵥ d)
      := by
    refine Filter.eventually_all.2 fun s => ?_
    have : Tendsto (fun ε : ℝ => f (s :: h) ⬝ᵥ θ h + ε * (f (s :: h) ⬝ᵥ d)) (𝓝 0)
        (𝓝 (f (s :: h) ⬝ᵥ θ h)) := by
      simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (f (s :: h) ⬝ᵥ d)).const_add _
    exact this.eventually (lt_mem_nhds (hslack s))
  filter_upwards [hev] with ε hε g s
  by_cases hg : g = h
  · subst hg
    simp only [Pi.add_apply, Pi.smul_apply, rd_loc, ↓reduceIte, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    exact (hε s).le
  · simpa [rd_loc, hg] using hθ g s

/-- **Arrow security prices** (Miao, p. 432). With Arrow securities, nonbinding debt constraints
at the successors of `sᵗ` and positive consumption, the first-order conditions give
`Q_t(s′ | sᵗ) = β u′(c_{t+1}(sᵗ, s′)) Pr(s′ | sᵗ) / u′(c_t(sᵗ))`. -/
theorem rd_arrow_price [DecidableEq S] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    {Q : List S → S → ℝ} {y : List S → ℝ} {a0 : S → ℝ} {Dbar : List S → ℝ}
    {c : List S → ℝ} {a : List S → S → ℝ}
    (hsol : rd_Solves (rd_EU T β u)
      (rd_SeqFeas Q rd_arrowPayoff y a0 (rd_ThetaDC rd_arrowPayoff Dbar)) c a)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h)) (hu'0 : 0 < u' (c h))
    (hslack : ∀ s, -Dbar (s :: h) < a h s) (s' : S) :
    Q h s' = β * u' (c (s' :: h)) * rd_condPr T h s' / u' (c h) := by
  have hsl : ∀ s, -Dbar (s :: h) < rd_arrowPayoff (s :: h) ⬝ᵥ a h := fun s => by
    simpa [rd_arrowPayoff, dotProduct] using hslack s
  have := rd_euler_eq T hβ0 hβ1 hu hd hsol h hch hcs (Pi.single s' 1)
    (rd_DC_slack hsol.1.2.2 h hsl _)
  simp only [rd_Phi, dotProduct_single, mul_one] at this
  have e : ∑ s, rd_condPr T h s * (u' (c (s :: h)) * rd_arrowPayoff (s :: h) s') =
      rd_condPr T h s' * u' (c (s' :: h)) := by
    simp [rd_arrowPayoff]
  rw [e] at this
  field_simp
  linarith

/-- Miao, p. 432: "Under complete markets the above equation does not depend on `i`": two agents
facing the same Arrow prices have equal intertemporal marginal rates of substitution. -/
theorem rd_arrow_price_common [DecidableEq S] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u₁ u₁' u₂ u₂' : ℝ → ℝ} (hu₁ : MonotoneOn u₁ (Set.Ici 0))
    (hd₁ : ∀ x, 0 < x → HasDerivAt u₁ (u₁' x) x) (hu₂ : MonotoneOn u₂ (Set.Ici 0))
    (hd₂ : ∀ x, 0 < x → HasDerivAt u₂ (u₂' x) x)
    {Q : List S → S → ℝ} {y₁ y₂ : List S → ℝ} {a₁ a₂ : S → ℝ} {D₁ D₂ : List S → ℝ}
    {c₁ c₂ : List S → ℝ} {θ₁ θ₂ : List S → S → ℝ}
    (hs₁ : rd_Solves (rd_EU T β u₁)
      (rd_SeqFeas Q rd_arrowPayoff y₁ a₁ (rd_ThetaDC rd_arrowPayoff D₁)) c₁ θ₁)
    (hs₂ : rd_Solves (rd_EU T β u₂)
      (rd_SeqFeas Q rd_arrowPayoff y₂ a₂ (rd_ThetaDC rd_arrowPayoff D₂)) c₂ θ₂)
    (h : List S) (h1 : 0 < c₁ h) (h1s : ∀ s, 0 < c₁ (s :: h)) (h1' : 0 < u₁' (c₁ h))
    (h2 : 0 < c₂ h) (h2s : ∀ s, 0 < c₂ (s :: h)) (h2' : 0 < u₂' (c₂ h))
    (hsl₁ : ∀ s, -D₁ (s :: h) < θ₁ h s) (hsl₂ : ∀ s, -D₂ (s :: h) < θ₂ h s) (s' : S) :
    β * u₁' (c₁ (s' :: h)) * rd_condPr T h s' / u₁' (c₁ h) =
      β * u₂' (c₂ (s' :: h)) * rd_condPr T h s' / u₂' (c₂ h) := by
  rw [← rd_arrow_price T hβ0 hβ1 hu₁ hd₁ hs₁ h h1 h1s h1' hsl₁ s',
    ← rd_arrow_price T hβ0 hβ1 hu₂ hd₂ hs₂ h h2 h2s h2' hsl₂ s']

/-- (13.7) with (13.16) (Miao, pp. 419, 429): if the Euler equation holds at every node for every
security, `q⁰_t(sᵗ) = βᵗ Pr(sᵗ) u′(c_t(sᵗ)) / u′(c₀(s⁰))` is a state price process. -/
theorem rd_statePrice_of_euler [DecidableEq J] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) {u' : ℝ → ℝ}
    {p f : List S → J → ℝ} {c : List S → ℝ} (hu'0 : ∀ h, 0 < u' (c h))
    (heul : ∀ h j, rd_Phi T β u' p f c h (Pi.single j 1) = 0) :
    rd_StatePrice p f fun h => β ^ h.length * T.Pr h * u' (c h) / u' (c []) := by
  refine ⟨fun h => div_pos (mul_pos (mul_pos (pow_pos hβ0 _) (T.pos h)) (hu'0 h)) (hu'0 []),
    fun h j => ?_⟩
  have := heul h j
  simp only [rd_Phi, dotProduct_single, mul_one, rd_condPr] at this
  have hP := (T.pos h).ne'
  have hu := (hu'0 h).ne'
  have hu0 := (hu'0 []).ne'
  have hb := (pow_pos hβ0 h.length).ne'
  have e : u' (c h) * p h j =
      β * ∑ s, T.Pr (s :: h) / T.Pr h * (u' (c (s :: h)) * f (s :: h) j) := by
    linarith
  have hsum : ∑ s, β ^ (s :: h).length * T.Pr (s :: h) * u' (c (s :: h)) / u' (c []) *
      f (s :: h) j = β ^ h.length * T.Pr h / u' (c []) *
        (β * ∑ s, T.Pr (s :: h) / T.Pr h * (u' (c (s :: h)) * f (s :: h) j)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [List.length_cons, pow_succ]
    field_simp
  rw [hsum, ← e]
  field_simp

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 13.4: first-order and transversality conditions

Miao, Exercise 13.4, p. 452, for the discounted expected utility (13.1) with a differentiable
utility `u` (derivative `u′`) satisfying the gradient inequality of concavity
`u(x′) ≤ u(x) + u′(x)(x′ − x)` (`x > 0`, `x′ ≥ 0`; `rd_gradIneq_of_concave` derives it from
`ConcaveOn` and differentiability, and `rd_sqrt_gradIneq` checks it for `√·`).

Necessity of the first-order conditions (Kuhn–Tucker form, at a node with positive
consumption there and at the successors):
* borrowing constraints (13.14): `u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + μₜ pₜ`, `μₜ ≥ 0`,
  `μₜ (pₜ · θₜ + B̄ₜ) = 0` (`ex_13_4_BC_foc`);
* short-sales constraints (13.15): `u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + νₜ`, `νₜ ≥ 0`,
  `νₜⱼ (θₜⱼ + h̄ₜⱼ) = 0` (`ex_13_4_SC_foc`);
* debt constraints (13.13), when the payoff matrix has rank `S` at the node:
  `u′(cₜ) pₜ = ∑ₛ (β Pr(s|sᵗ) u′(c_{t+1}) + ηₛ) f_{t+1}`, `ηₛ ≥ 0`,
  `ηₛ (f_{t+1} · θₜ + D̄_{t+1}) = 0` (`ex_13_4_DC_foc`). Without rank `S` this needs Farkas'
  lemma and is not formalised.

Sufficiency: the budget equalities, the first-order conditions and the transversality condition
(13.39) (`ex_13_4_BC_suff`), (13.40) (`ex_13_4_SC_suff`, read as
`lim E βᵀ u′(c_T) p_T · (θ_T + h̄_T) = 0`, the book's `p_T · θ_T + h̄_T` mixing a scalar and a
vector) or (13.38) (`ex_13_4_DC_suff`) imply optimality; with market clearing they characterise
an equilibrium (`ex_13_4_BC_eqm`). The proof telescopes the budget constraints weighted by
`ξ = βᵗ Pr u′(c)` (`rd_telescope`). Necessity of the transversality conditions is not
formalised.
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J : Type*} [Fintype S] [Fintype J]

/-- The gradient inequality of a concave differentiable utility on `[0, ∞)`. -/
def rd_GradIneq (u u' : ℝ → ℝ) : Prop := ∀ x, 0 < x → ∀ x', 0 ≤ x' → u x' ≤ u x + u' x * (x' - x)

/-- A concave utility on `[0, ∞)`, differentiable on `(0, ∞)`, satisfies the gradient
inequality. -/
theorem rd_gradIneq_of_concave {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ici 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) : rd_GradIneq u u' := by
  intro x hx x' hx'
  rcases lt_trichotomy x' x with hlt | heq | hgt
  · have := ConcaveOn.le_slope_of_hasDerivAt hc (Set.mem_Ici.2 hx') (Set.mem_Ici.2 hx.le) hlt
      (hd x hx)
    rw [slope_def_field] at this
    have hpos : 0 < x - x' := by linarith
    rw [le_div_iff₀ hpos] at this
    nlinarith
  · rw [heq]
    simp
  · have := ConcaveOn.slope_le_of_hasDerivAt hc (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 hx') hgt
      (hd x hx)
    rw [slope_def_field] at this
    have hpos : 0 < x' - x := by linarith
    rw [div_le_iff₀ hpos] at this
    nlinarith

/-- `√·` satisfies the gradient inequality with `u′(x) = 1/(2√x)`. -/
theorem rd_sqrt_gradIneq : rd_GradIneq Real.sqrt fun x => 1 / (2 * Real.sqrt x) := by
  intro x hx x' hx'
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 := Real.sq_sqrt hx.le
  have h2 := Real.sq_sqrt hx'
  rw [show 1 / (2 * Real.sqrt x) * (x' - x) = (x' - x) / (2 * Real.sqrt x) by ring,
    ← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt x' - Real.sqrt x), Real.sqrt_nonneg x']

/-- Over date-`T` nodes, a factor `β^{len}` is the constant `β^T`. -/
theorem rd_dsum_pow (β : ℝ) (F : List S → ℝ) (T : ℕ) :
    rd_dsum (fun g => β ^ g.length * F g) [] T = β ^ T * rd_dsum F [] T := by
  rw [rd_dsum, rd_dsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [rd_mem_paths] at hl
  simp [hl]

omit [Fintype S] in
/-- The net cash flows of two strategies differ by the net cash flow of their difference. -/
theorem rd_net_sub (p f : List S → J → ℝ) (θm1 : J → ℝ) (θ θ' : List S → J → ℝ)
    (g : List S) : rd_net p f θm1 θ' g - rd_net p f θm1 θ g = rd_net p f 0 (θ' - θ) g := by
  cases g with
  | nil => simp [rd_net, rd_prev, dotProduct_sub]
  | cons s g => simp [rd_net, rd_prev, rd_fz, dotProduct_sub]; ring

/-- Telescoping the cash flows of a strategy `Δ` (with `Δ_{−1} = 0`) weighted by `ξ`. -/
theorem rd_telescope (p f : List S → J → ℝ) (ξ : List S → ℝ) (Δ : List S → J → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), rd_dsum (fun g => ξ g * rd_net p f 0 Δ g) [] t =
      ∑ t ∈ Finset.range T, rd_dsum (fun g => ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ Δ g) -
        ξ g * (p g ⬝ᵥ Δ g)) [] t - rd_dsum (fun g => ξ g * (p g ⬝ᵥ Δ g)) [] T := by
  induction T with
  | zero => simp [rd_dsum_zero, rd_net, rd_prev]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have e : rd_dsum (fun g => ξ g * rd_net p f 0 Δ g) [] (T + 1) =
        rd_dsum (fun g => ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ Δ g)) [] T -
          rd_dsum (fun g => ξ g * (p g ⬝ᵥ Δ g)) [] (T + 1) := by
      have h1 : rd_dsum (fun g => ξ g * (rd_fz p f g ⬝ᵥ rd_prev Δ 0 g)) [] (T + 1) =
          rd_dsum (fun g => ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ Δ g)) [] T := rd_dsum_succ' _ _ _
      rw [← h1, ← rd_dsum_sub]
      exact rd_dsum_congr (fun g => by simp only [rd_net]; ring) _ _
    rw [e, rd_dsum_sub]
    ring

/-- The first-order condition with a multiplier vector `e`, multiplied by `ξ = βᵗ Pr u′(c)` and
applied to a portfolio `v`: `ξₜ (pₜ · v) = ∑ₛ ξ_{t+1} (f_{t+1} · v) + βᵗ Pr (e · v)`. -/
theorem rd_foc_xi (T : RDTree S) (β : ℝ) (u' : ℝ → ℝ) (p f : List S → J → ℝ)
    (c : List S → ℝ) (g : List S) (e : J → ℝ)
    (hfoc : ∀ j, u' (c g) * p g j =
      β * ∑ s, rd_condPr T g s * (u' (c (s :: g)) * f (s :: g) j) + e j) (v : J → ℝ) :
    β ^ g.length * T.Pr g * u' (c g) * (p g ⬝ᵥ v) =
      ∑ s, β ^ (s :: g).length * T.Pr (s :: g) * u' (c (s :: g)) * (f (s :: g) ⬝ᵥ v) +
        β ^ g.length * T.Pr g * (e ⬝ᵥ v) := by
  have hP := (T.pos g).ne'
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := hfoc j
  have e1 : β ^ g.length * T.Pr g * u' (c g) * (p g j * v j) =
      β ^ g.length * T.Pr g * (u' (c g) * p g j) * v j := by ring
  rw [e1, this]
  simp only [rd_condPr, Finset.mul_sum, mul_add, add_mul, Finset.sum_mul, List.length_cons,
    pow_succ]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    field_simp
  · ring

/-- The core of the sufficiency argument: if the weighted consumption gains are bounded by a
sequence with a nonpositive limit, the plan `c′` is no better than `c`. -/
theorem rd_suff_core (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : MonotoneOn u (Set.Ici 0)) (hgrad : rd_GradIneq u u') {c c' : List S → ℝ}
    (hc : rd_LinfPos c) (hc' : rd_LinfPos c') (hcpos : ∀ g, 0 < c g) {τ : ℕ → ℝ} {L : ℝ}
    (hτ : Tendsto τ atTop (𝓝 L)) (hL : L ≤ 0)
    (hbound : ∀ n, ∑ t ∈ Finset.range (n + 1),
      rd_dsum (fun g => β ^ g.length * T.Pr g * u' (c g) * (c' g - c g)) [] t ≤ τ n) :
    rd_EU T β u c' ≤ rd_EU T β u c := by
  obtain ⟨K, hK⟩ := rd_abs_u_le hu hc
  obtain ⟨K', hK'⟩ := rd_abs_u_le hu hc'
  have hs := (rd_EU_summable T hβ0.le hβ1 u hK').sub (rd_EU_summable T hβ0.le hβ1 u hK)
  have hA := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hle : rd_EU T β u c' - rd_EU T β u c ≤ L := by
    rw [rd_EU, rd_EU, ← Summable.tsum_sub (rd_EU_summable T hβ0.le hβ1 u hK')
      (rd_EU_summable T hβ0.le hβ1 u hK)]
    refine le_of_tendsto_of_tendsto' hA hτ fun n => ?_
    refine le_trans ?_ (hbound n)
    simp only [Function.comp_apply]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [← mul_sub, ← rd_dsum_sub, ← rd_dsum_pow]
    refine rd_dsum_mono (fun g => ?_) _ _
    have := hgrad (c g) (hcpos g) (c' g) (hc'.2 g)
    have hw : 0 ≤ β ^ g.length * T.Pr g := mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le
    have := mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.2 this) hw
    calc β ^ g.length * (T.Pr g * u (c' g) - T.Pr g * u (c g))
        = β ^ g.length * T.Pr g * (u (c' g) - u (c g)) := by ring
      _ ≤ β ^ g.length * T.Pr g * (u' (c g) * (c' g - c g)) := this
      _ = β ^ g.length * T.Pr g * u' (c g) * (c' g - c g) := by ring
  linarith

/-- The weighted consumption gain is bounded by the weighted net cash flow of `θ′ − θ`. -/
theorem rd_gain_le (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) {u' : ℝ → ℝ}
    (hu'0 : ∀ x, 0 < x → 0 ≤ u' x) {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ}
    {c c' : List S → ℝ} {θ θ' : List S → J → ℝ} (hcpos : ∀ g, 0 < c g)
    (hB : rd_BudgetEq p f y θm1 c θ) (hB' : rd_Budget p f y θm1 c' θ') (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1),
        rd_dsum (fun g => β ^ g.length * T.Pr g * u' (c g) * (c' g - c g)) [] t ≤
      ∑ t ∈ Finset.range (n + 1), rd_dsum (fun g => β ^ g.length * T.Pr g * u' (c g) *
        rd_net p f 0 (θ' - θ) g) [] t := by
  apply Finset.sum_le_sum
  intro t _
  apply rd_dsum_mono
  intro g
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le) (hu'0 _ (hcpos g)))
  rw [← rd_net_sub p f θm1 θ θ' g]
  have h1 := (rd_budget_iff_net p f y θm1 c' θ').1 hB' g
  have h2 := hB g
  simp only [rd_net] at h1 ⊢
  linarith

/-- **Exercise 13.4** (Miao, p. 452), borrowing constraints: sufficiency. Budget equalities, the
first-order conditions `u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + μₜ pₜ` with `μ ≥ 0` and
`μₜ (pₜ · θₜ + B̄ₜ) = 0`, and the transversality condition (13.39)
`lim E[βᵀ u′(c_T)(p_T · θ_T + B̄_T)] = 0` imply that `(c, θ)` is optimal. -/
theorem ex_13_4_BC_suff (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : MonotoneOn u (Set.Ici 0)) (hgrad : rd_GradIneq u u') (hu'0 : ∀ x, 0 < x → 0 ≤ u' x)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Bbar : List S → ℝ}
    {c : List S → ℝ} {θ : List S → J → ℝ} (hc : rd_LinfPos c) (hcpos : ∀ g, 0 < c g)
    (hB : rd_BudgetEq p f y θm1 c θ) (hθ : θ ∈ rd_ThetaBC p Bbar) {μ : List S → ℝ}
    (hμ0 : ∀ h, 0 ≤ μ h) (hcs : ∀ h, μ h * (p h ⬝ᵥ θ h + Bbar h) = 0)
    (hfoc : ∀ h j, u' (c h) * p h j =
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j) + μ h * p h j)
    (htvc : Tendsto (fun n => β ^ n * rd_dsum (fun g => T.Pr g * (u' (c g) *
      (p g ⬝ᵥ θ g + Bbar g))) [] n) atTop (𝓝 0)) :
    rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaBC p Bbar)) c θ := by
  refine ⟨⟨hc, fun h => (hB h).le, hθ⟩, fun c' θ' ⟨hc', hB', hθ'⟩ => ?_⟩
  set ξ : List S → ℝ := fun g => β ^ g.length * T.Pr g * u' (c g)
  have hξ : ∀ g, 0 ≤ ξ g := fun g =>
    mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le) (hu'0 _ (hcpos g))
  refine rd_suff_core T hβ0 hβ1 hu hgrad hc hc' hcpos htvc le_rfl fun n => ?_
  refine (rd_gain_le T hβ0 hu'0 hcpos hB hB' n).trans ?_
  rw [rd_telescope]
  have hX : ∀ g, ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g) ≤ 0 := by
    intro g
    have := rd_foc_xi T β u' p f c g (μ g • p g) (fun j => by
      rw [hfoc g j]; simp) ((θ' - θ) g)
    simp only [ξ]
    rw [this]
    have hm : 0 ≤ β ^ g.length * T.Pr g * (μ g • p g ⬝ᵥ (θ' - θ) g) := by
      refine mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le) ?_
      simp only [smul_dotProduct, smul_eq_mul, Pi.sub_apply, dotProduct_sub]
      have := hcs g
      have := mul_nonneg (hμ0 g) (by linarith [hθ' g] : 0 ≤ p g ⬝ᵥ θ' g + Bbar g)
      nlinarith
    linarith
  have hterm : -rd_dsum (fun g => ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] n ≤
      β ^ n * rd_dsum (fun g => T.Pr g * (u' (c g) * (p g ⬝ᵥ θ g + Bbar g))) [] n := by
    rw [← rd_dsum_pow, ← rd_dsum_neg]
    refine rd_dsum_mono (fun g => ?_) _ _
    simp only [ξ, Pi.sub_apply, dotProduct_sub]
    have := mul_nonneg (hξ g) (by linarith [hθ' g] : 0 ≤ p g ⬝ᵥ θ' g + Bbar g)
    simp only [ξ] at this
    nlinarith
  have hsum : ∑ t ∈ Finset.range n, rd_dsum (fun g => ∑ s, ξ (s :: g) *
      (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] t ≤ 0 :=
    Finset.sum_nonpos fun t _ => by
      have := rd_dsum_mono hX [] t
      simpa [rd_dsum] using this
  linarith

/-- **Exercise 13.4** (Miao, p. 452), short-sales constraints: sufficiency. Budget equalities,
`u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + νₜ` with `ν ≥ 0`, `νₜⱼ (θₜⱼ + h̄ₜⱼ) = 0`, nonnegative
prices, and the transversality condition (13.40) `lim E[βᵀ u′(c_T) p_T · (θ_T + h̄_T)] = 0`
imply that `(c, θ)` is optimal. -/
theorem ex_13_4_SC_suff (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : MonotoneOn u (Set.Ici 0)) (hgrad : rd_GradIneq u u') (hu'0 : ∀ x, 0 < x → 0 ≤ u' x)
    {p f : List S → J → ℝ} (hp0 : ∀ h j, 0 ≤ p h j) {y : List S → ℝ} {θm1 : J → ℝ}
    {hbar : List S → J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ} (hc : rd_LinfPos c)
    (hcpos : ∀ g, 0 < c g) (hB : rd_BudgetEq p f y θm1 c θ) (hθ : θ ∈ rd_ThetaSC hbar)
    {ν : List S → J → ℝ} (hν0 : ∀ h j, 0 ≤ ν h j) (hcs : ∀ h j, ν h j * (θ h j + hbar h j) = 0)
    (hfoc : ∀ h j, u' (c h) * p h j =
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j) + ν h j)
    (htvc : Tendsto (fun n => β ^ n * rd_dsum (fun g => T.Pr g * (u' (c g) *
      (p g ⬝ᵥ (θ g + hbar g)))) [] n) atTop (𝓝 0)) :
    rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaSC hbar)) c θ := by
  refine ⟨⟨hc, fun h => (hB h).le, hθ⟩, fun c' θ' ⟨hc', hB', hθ'⟩ => ?_⟩
  set ξ : List S → ℝ := fun g => β ^ g.length * T.Pr g * u' (c g)
  have hξ : ∀ g, 0 ≤ ξ g := fun g =>
    mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le) (hu'0 _ (hcpos g))
  refine rd_suff_core T hβ0 hβ1 hu hgrad hc hc' hcpos htvc le_rfl fun n => ?_
  refine (rd_gain_le T hβ0 hu'0 hcpos hB hB' n).trans ?_
  rw [rd_telescope]
  have hX : ∀ g, ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g) ≤ 0 := by
    intro g
    have := rd_foc_xi T β u' p f c g (ν g) (hfoc g) ((θ' - θ) g)
    simp only [ξ]
    rw [this]
    have hm : 0 ≤ ν g ⬝ᵥ (θ' - θ) g := by
      refine Finset.sum_nonneg fun j _ => ?_
      simp only [Pi.sub_apply]
      have := hcs g j
      have := mul_nonneg (hν0 g j) (by linarith [hθ' g j] : 0 ≤ θ' g j + hbar g j)
      nlinarith
    have := mul_nonneg (mul_nonneg (pow_nonneg hβ0.le g.length) (T.pos g).le) hm
    linarith
  have hterm : -rd_dsum (fun g => ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] n ≤
      β ^ n * rd_dsum (fun g => T.Pr g * (u' (c g) * (p g ⬝ᵥ (θ g + hbar g)))) [] n := by
    rw [← rd_dsum_pow, ← rd_dsum_neg]
    refine rd_dsum_mono (fun g => ?_) _ _
    have hpos : 0 ≤ p g ⬝ᵥ (θ' g + hbar g) := Finset.sum_nonneg fun j _ =>
      mul_nonneg (hp0 g j) (by simp only [Pi.add_apply]; linarith [hθ' g j])
    have e : p g ⬝ᵥ (θ' - θ) g = p g ⬝ᵥ (θ' g + hbar g) - p g ⬝ᵥ (θ g + hbar g) := by
      simp only [Pi.sub_apply, dotProduct_sub, dotProduct_add]
      ring
    rw [e]
    have := mul_nonneg (hξ g) hpos
    simp only [ξ] at this ⊢
    nlinarith
  have hsum : ∑ t ∈ Finset.range n, rd_dsum (fun g => ∑ s, ξ (s :: g) *
      (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] t ≤ 0 :=
    Finset.sum_nonpos fun t _ => by
      have := rd_dsum_mono hX [] t
      simpa [rd_dsum] using this
  linarith

/-- **Exercise 13.4** (Miao, p. 452), debt constraints: sufficiency. Budget equalities,
`u′(cₜ) pₜ = ∑ₛ (β Pr(s|sᵗ) u′(c_{t+1}) + η_{t+1}) f_{t+1}` with `η ≥ 0`,
`η_{t+1} (f_{t+1} · θₜ + D̄_{t+1}) = 0`, and the transversality condition (13.38)
`lim E[β^{T+1} u′(c_{T+1})(f_{T+1} · θ_T + D̄_{T+1})] = 0` imply that `(c, θ)` is optimal.
The multiplier `η (s :: h)` belongs to the debt constraint at the successor `(sᵗ, s)`. -/
theorem ex_13_4_DC_suff (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : MonotoneOn u (Set.Ici 0)) (hgrad : rd_GradIneq u u') (hu'0 : ∀ x, 0 < x → 0 ≤ u' x)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Dbar : List S → ℝ}
    {c : List S → ℝ} {θ : List S → J → ℝ} (hc : rd_LinfPos c) (hcpos : ∀ g, 0 < c g)
    (hB : rd_BudgetEq p f y θm1 c θ) (hθ : θ ∈ rd_ThetaDC f Dbar) {η : List S → ℝ}
    (hη0 : ∀ h, 0 ≤ η h) (hcs : ∀ h s, η (s :: h) * (f (s :: h) ⬝ᵥ θ h + Dbar (s :: h)) = 0)
    (hfoc : ∀ h j, u' (c h) * p h j =
      ∑ s, (β * rd_condPr T h s * u' (c (s :: h)) + η (s :: h)) * f (s :: h) j)
    (htvc : Tendsto (fun n => rd_dsum (fun g => ∑ s, β ^ (n + 1) * T.Pr (s :: g) *
      u' (c (s :: g)) * (f (s :: g) ⬝ᵥ θ g + Dbar (s :: g))) [] n) atTop (𝓝 0)) :
    rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaDC f Dbar)) c θ := by
  refine ⟨⟨hc, fun h => (hB h).le, hθ⟩, fun c' θ' ⟨hc', hB', hθ'⟩ => ?_⟩
  set ξ : List S → ℝ := fun g => β ^ g.length * T.Pr g * u' (c g)
  have hξ : ∀ g, 0 ≤ ξ g := fun g =>
    mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le) (hu'0 _ (hcpos g))
  have hfoc' : ∀ g j, u' (c g) * p g j = β * ∑ s, rd_condPr T g s *
      (u' (c (s :: g)) * f (s :: g) j) + ∑ s, η (s :: g) * f (s :: g) j := by
    intro g j
    rw [hfoc g j, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hdotη : ∀ g (v : J → ℝ), (fun j => ∑ s, η (s :: g) * f (s :: g) j) ⬝ᵥ v =
      ∑ s, η (s :: g) * (f (s :: g) ⬝ᵥ v) := by
    intro g v
    simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring
  have hηΔ : ∀ g, 0 ≤ ∑ s, η (s :: g) * (f (s :: g) ⬝ᵥ (θ' - θ) g) := by
    intro g
    refine Finset.sum_nonneg fun s _ => ?_
    simp only [Pi.sub_apply, dotProduct_sub]
    have := hcs g s
    have := mul_nonneg (hη0 (s :: g)) (by linarith [hθ' g s] :
      0 ≤ f (s :: g) ⬝ᵥ θ' g + Dbar (s :: g))
    nlinarith
  have hxi : ∀ g (v : J → ℝ), ξ g * (p g ⬝ᵥ v) = ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ v) +
      β ^ g.length * T.Pr g * ∑ s, η (s :: g) * (f (s :: g) ⬝ᵥ v) := by
    intro g v
    have := rd_foc_xi T β u' p f c g _ (hfoc' g) v
    rw [hdotη] at this
    exact this
  refine rd_suff_core T hβ0 hβ1 hu hgrad hc hc' hcpos htvc le_rfl fun n => ?_
  refine (rd_gain_le T hβ0 hu'0 hcpos hB hB' n).trans ?_
  rw [rd_telescope]
  have hX : ∀ g, ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g) ≤ 0 := by
    intro g
    rw [hxi]
    have := mul_nonneg (mul_nonneg (pow_nonneg hβ0.le g.length) (T.pos g).le) (hηΔ g)
    linarith
  have hterm : -rd_dsum (fun g => ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] n ≤
      rd_dsum (fun g => ∑ s, β ^ (n + 1) * T.Pr (s :: g) * u' (c (s :: g)) *
        (f (s :: g) ⬝ᵥ θ g + Dbar (s :: g))) [] n := by
    rw [← rd_dsum_neg]
    unfold rd_dsum
    refine Finset.sum_le_sum fun l hl => ?_
    rw [rd_mem_paths] at hl
    simp only [List.append_nil]
    rw [hxi]
    have h1 := mul_nonneg (mul_nonneg (pow_nonneg hβ0.le l.length) (T.pos l).le) (hηΔ l)
    have h2 : -∑ s, ξ (s :: l) * (f (s :: l) ⬝ᵥ (θ' - θ) l) ≤ ∑ s, β ^ (n + 1) *
        T.Pr (s :: l) * u' (c (s :: l)) * (f (s :: l) ⬝ᵥ θ l + Dbar (s :: l)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      have hpos := mul_nonneg (hξ (s :: l)) (by linarith [hθ' l s] :
        0 ≤ f (s :: l) ⬝ᵥ θ' l + Dbar (s :: l))
      simp only [ξ, List.length_cons, hl, Pi.sub_apply, dotProduct_sub] at hpos ⊢
      nlinarith
    linarith
  have hsum : ∑ t ∈ Finset.range n, rd_dsum (fun g => ∑ s, ξ (s :: g) *
      (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] t ≤ 0 :=
    Finset.sum_nonpos fun t _ => by
      have := rd_dsum_mono hX [] t
      simpa [rd_dsum] using this
  linarith

/-- **Exercise 13.4**, borrowing constraints: the conditions of `ex_13_4_BC_suff` for every
agent, with market clearing, characterise a Radner equilibrium with borrowing constraints. -/
theorem ex_13_4_BC_eqm {ι : Type*} [Fintype ι] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {u u' : ι → ℝ → ℝ} (hu : ∀ i, MonotoneOn (u i) (Set.Ici 0))
    (hgrad : ∀ i, rd_GradIneq (u i) (u' i)) (hu'0 : ∀ i x, 0 < x → 0 ≤ u' i x)
    {p f : List S → J → ℝ} {y : ι → List S → ℝ} {θm1 : ι → J → ℝ} {Bbar : ι → List S → ℝ}
    {c : ι → List S → ℝ} {θ : ι → List S → J → ℝ} {μ : ι → List S → ℝ}
    (hc : ∀ i, rd_LinfPos (c i)) (hcpos : ∀ i g, 0 < c i g)
    (hB : ∀ i, rd_BudgetEq p f (y i) (θm1 i) (c i) (θ i))
    (hθ : ∀ i, θ i ∈ rd_ThetaBC p (Bbar i)) (hμ0 : ∀ i h, 0 ≤ μ i h)
    (hcs : ∀ i h, μ i h * (p h ⬝ᵥ θ i h + Bbar i h) = 0)
    (hfoc : ∀ i h j, u' i (c i h) * p h j =
      β * ∑ s, rd_condPr T h s * (u' i (c i (s :: h)) * f (s :: h) j) + μ i h * p h j)
    (htvc : ∀ i, Tendsto (fun n => β ^ n * rd_dsum (fun g => T.Pr g * (u' i (c i g) *
      (p g ⬝ᵥ θ i g + Bbar i g))) [] n) atTop (𝓝 0))
    (hclear : ∀ h, ∑ i, θ i h = ∑ i, θm1 i) :
    rd_RadnerBC (fun i => rd_EU T β (u i)) y θm1 p f Bbar c θ :=
  ⟨fun i => ex_13_4_BC_suff T hβ0 hβ1 (hu i) (hgrad i) (hu'0 i) (hc i) (hcpos i) (hB i) (hθ i)
    (hμ0 i) (hcs i) (hfoc i) (htvc i), rd_goods_clearing p f y θm1 c θ hB hclear, hclear⟩

omit [Fintype S] in
/-- Feasibility of a perturbed borrowing-constrained strategy. -/
theorem rd_BC_feas [DecidableEq S] {p : List S → J → ℝ} {Bbar : List S → ℝ}
    {θ : List S → J → ℝ} (hθ : θ ∈ rd_ThetaBC p Bbar) (h : List S) (d : J → ℝ) (ε : ℝ)
    (hε : -Bbar h ≤ p h ⬝ᵥ θ h + ε * (p h ⬝ᵥ d)) : θ + ε • rd_loc d h ∈ rd_ThetaBC p Bbar := by
  intro g
  by_cases hg : g = h
  · subst hg
    simpa [rd_loc, dotProduct_add, dotProduct_smul] using hε
  · simpa [rd_loc, hg] using hθ g

/-- **Exercise 13.4** (Miao, p. 452), borrowing constraints: the first-order conditions are
necessary. At a node with positive consumption there and at the successors, and a nonzero price
vector, there is `μ ≥ 0` with `μ (pₜ · θₜ + B̄ₜ) = 0` and
`u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + μ pₜ`. -/
theorem ex_13_4_BC_foc (T : RDTree S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0))
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {p f : List S → J → ℝ} {y : List S → ℝ}
    {θm1 : J → ℝ} {Bbar : List S → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hsol : rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaBC p Bbar)) c θ)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h)) (hp : ∃ j0, p h j0 ≠ 0) :
    ∃ μ, 0 ≤ μ ∧ μ * (p h ⬝ᵥ θ h + Bbar h) = 0 ∧ ∀ j, u' (c h) * p h j =
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j) + μ * p h j := by
  classical
  have hθ := hsol.1.2.2
  set w : J → ℝ := fun j => -(u' (c h) * p h j) +
    β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j)
  have hΦ : ∀ d, rd_Phi T β u' p f c h d = w ⬝ᵥ d := fun d => rd_Phi_eq T β u' p f c h d
  -- one-sided feasibility for directions with `p · d ≥ 0`
  have hdir : ∀ d, 0 ≤ p h ⬝ᵥ d → w ⬝ᵥ d ≤ 0 := by
    intro d hd0
    rw [← hΦ]
    refine rd_euler_dir T hβ0 hβ1 hu hd hsol h hch hcs d ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact rd_BC_feas hθ h d ε (by nlinarith [hθ h, mul_nonneg (le_of_lt hε) hd0])
  have horth : ∀ d, p h ⬝ᵥ d = 0 → w ⬝ᵥ d = 0 := by
    intro d hd0
    have h1 := hdir d hd0.ge
    have h2 := hdir (-d) (by rw [dotProduct_neg, hd0, neg_zero])
    rw [dotProduct_neg] at h2
    linarith
  obtain ⟨j0, hj0⟩ := hp
  have hwj : ∀ j, w j * p h j0 = w j0 * p h j := by
    intro j
    have := horth (p h j0 • Pi.single j 1 - p h j • Pi.single j0 1) (by
      simp only [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
      ring)
    simp only [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at this
    linarith
  set lam := w j0 / p h j0
  have hw : ∀ j, w j = lam * p h j := fun j => by
    simp only [lam]
    field_simp
    linarith [hwj j]
  have hpp : 0 < p h ⬝ᵥ p h := by
    refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨j0, Finset.mem_univ _, ?_⟩
    exact mul_self_pos.2 hj0
  have hwp : w ⬝ᵥ p h = lam * (p h ⬝ᵥ p h) := by
    simp only [dotProduct, hw, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlam : lam ≤ 0 := by
    have := hdir (p h) hpp.le
    rw [hwp] at this
    by_contra hc
    push Not at hc
    exact absurd this (not_le.2 (mul_pos hc hpp))
  refine ⟨-lam, by linarith, ?_, fun j => ?_⟩
  · by_cases hbind : p h ⬝ᵥ θ h + Bbar h = 0
    · rw [hbind, mul_zero]
    · have hslack : -Bbar h < p h ⬝ᵥ θ h := by
        have := hθ h
        rcases lt_or_eq_of_le this with hlt | heq
        · exact hlt
        · exact absurd (by linarith) hbind
      have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), θ + ε • rd_loc (-p h) h ∈ rd_ThetaBC p Bbar := by
        have : Tendsto (fun ε : ℝ => p h ⬝ᵥ θ h + ε * (p h ⬝ᵥ -p h)) (𝓝 0)
            (𝓝 (p h ⬝ᵥ θ h)) := by
          simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (p h ⬝ᵥ -p h)).const_add _
        filter_upwards [this.eventually (lt_mem_nhds hslack)] with ε hε
        exact rd_BC_feas hθ h _ ε hε.le
      have := rd_euler_eq T hβ0 hβ1 hu hd hsol h hch hcs (-p h) hev
      rw [hΦ, dotProduct_neg, hwp] at this
      have : lam = 0 := by
        rcases mul_eq_zero.1 (neg_eq_zero.1 this) with h1 | h1
        · exact h1
        · exact absurd h1 hpp.ne'
      rw [this, neg_zero, zero_mul]
  · have := hw j
    simp only [w] at this
    linarith

/-- **Exercise 13.4** (Miao, p. 452), short-sales constraints: the first-order conditions are
necessary. At a node with positive consumption there and at the successors there is `ν ≥ 0`
with `νⱼ (θₜⱼ + h̄ₜⱼ) = 0` and `u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + ν`. -/
theorem ex_13_4_SC_foc (T : RDTree S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0))
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {p f : List S → J → ℝ} {y : List S → ℝ}
    {θm1 : J → ℝ} {hbar : List S → J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hsol : rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaSC hbar)) c θ)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h)) :
    ∃ ν : J → ℝ, (∀ j, 0 ≤ ν j) ∧ (∀ j, ν j * (θ h j + hbar h j) = 0) ∧ ∀ j, u' (c h) * p h j =
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j) + ν j := by
  classical
  have hθ := hsol.1.2.2
  have hfeas : ∀ j (ε : ℝ), -hbar h j ≤ θ h j + ε →
      θ + ε • rd_loc (Pi.single j 1) h ∈ rd_ThetaSC hbar := by
    intro j ε hε g k
    by_cases hg : g = h
    · subst hg
      by_cases hk : k = j
      · subst hk
        simpa [rd_loc] using hε
      · simpa [rd_loc, hk] using hθ g k
    · simpa [rd_loc, hg] using hθ g k
  set ν : J → ℝ := fun j => -rd_Phi T β u' p f c h (Pi.single j 1)
  have hν : ∀ j, 0 ≤ ν j := by
    intro j
    have := rd_euler_dir T hβ0 hβ1 hu hd hsol h hch hcs (Pi.single j 1) (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hfeas j ε (by linarith [hθ h j, (le_of_lt hε : (0 : ℝ) ≤ ε)]))
    simp only [ν]
    unfold rd_Phi
    linarith
  refine ⟨ν, hν, fun j => ?_, fun j => ?_⟩
  · by_cases hbind : θ h j + hbar h j = 0
    · rw [hbind, mul_zero]
    · have hslack : -hbar h j < θ h j := by
        rcases lt_or_eq_of_le (hθ h j) with hlt | heq
        · exact hlt
        · exact absurd (by linarith) hbind
      have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), θ + ε • rd_loc (Pi.single j 1) h ∈ rd_ThetaSC hbar := by
        have : Tendsto (fun ε : ℝ => θ h j + ε) (𝓝 0) (𝓝 (θ h j)) := by
          simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_add (θ h j)
        filter_upwards [this.eventually (lt_mem_nhds hslack)] with ε hε
        exact hfeas j ε hε.le
      have := rd_euler_eq T hβ0 hβ1 hu hd hsol h hch hcs _ hev
      simp only [ν, this, neg_zero, zero_mul]
  · simp only [ν, rd_Phi, dotProduct_single, mul_one]
    ring

/-- **Exercise 13.4** (Miao, p. 452), debt constraints: the first-order conditions are necessary
when the payoff matrix has rank `S` at the node. There are `ηₛ ≥ 0` with
`ηₛ (f_{t+1}(sᵗ, s) · θₜ + D̄_{t+1}(sᵗ, s)) = 0` and
`u′(cₜ) pₜ = ∑ₛ (β Pr(s|sᵗ) u′(c_{t+1}) + ηₛ) f_{t+1}(sᵗ, s)`. -/
theorem ex_13_4_DC_foc (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Dbar : List S → ℝ}
    {c : List S → ℝ} {θ : List S → J → ℝ}
    (hsol : rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaDC f Dbar)) c θ)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h))
    (hrank : (rd_payoffMatrix f h).rank = Fintype.card S) :
    ∃ η : S → ℝ, (∀ s, 0 ≤ η s) ∧ (∀ s, η s * (f (s :: h) ⬝ᵥ θ h + Dbar (s :: h)) = 0) ∧
      ∀ j, u' (c h) * p h j =
        ∑ s, (β * rd_condPr T h s * u' (c (s :: h)) + η s) * f (s :: h) j := by
  classical
  have hθ := hsol.1.2.2
  set w : J → ℝ := fun j => -(u' (c h) * p h j) +
    β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j)
  have hΦ : ∀ d, rd_Phi T β u' p f c h d = w ⬝ᵥ d := fun d => rd_Phi_eq T β u' p f c h d
  have hfeas : ∀ d (ε : ℝ), (∀ s, -Dbar (s :: h) ≤ f (s :: h) ⬝ᵥ θ h + ε * (f (s :: h) ⬝ᵥ d)) →
      θ + ε • rd_loc d h ∈ rd_ThetaDC f Dbar := by
    intro d ε hε g s
    by_cases hg : g = h
    · subst hg
      simpa [rd_loc, dotProduct_add, dotProduct_smul] using hε s
    · simpa [rd_loc, hg] using hθ g s
  -- the spanning portfolios `d s` with `f(sᵗ, s′) · d s = δ_{s s′}`
  have hspan := (rd_rank_iff_span f h).1 hrank
  choose dd hdd using fun s : S => hspan fun s' => if s' = s then 1 else 0
  -- slackness is an open condition
  have hslack_ev : ∀ d, ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h →
      -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h + ε * (f (s :: h) ⬝ᵥ d) := by
    intro d
    refine Filter.eventually_all.2 fun s => ?_
    by_cases hs : -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h
    · have : Tendsto (fun ε : ℝ => f (s :: h) ⬝ᵥ θ h + ε * (f (s :: h) ⬝ᵥ d)) (𝓝 0)
          (𝓝 (f (s :: h) ⬝ᵥ θ h)) := by
        simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (f (s :: h) ⬝ᵥ d)).const_add _
      filter_upwards [this.eventually (lt_mem_nhds hs)] with ε hε _
      exact hε
    · exact Filter.Eventually.of_forall fun ε h' => absurd h' hs
  -- directions in the kernel have zero marginal value
  have hker : ∀ d, (∀ s, f (s :: h) ⬝ᵥ d = 0) → w ⬝ᵥ d = 0 := by
    intro d hd0
    rw [← hΦ]
    refine rd_euler_eq T hβ0 hβ1 hu hd hsol h hch hcs d (Filter.Eventually.of_forall
      fun ε => hfeas d ε fun s => ?_)
    rw [hd0 s, mul_zero, add_zero]
    exact hθ h s
  set η : S → ℝ := fun s => -(w ⬝ᵥ dd s)
  have hη : ∀ s, 0 ≤ η s := by
    intro s
    have := rd_euler_dir T hβ0 hβ1 hu hd hsol h hch hcs (dd s) (by
      filter_upwards [nhdsWithin_le_nhds (hslack_ev (dd s)), self_mem_nhdsWithin] with ε hε hpos
      refine hfeas _ ε fun s' => ?_
      by_cases hs' : -Dbar (s' :: h) < f (s' :: h) ⬝ᵥ θ h
      · exact (hε s' hs').le
      · rw [hdd s s']
        have := hθ h s'
        split_ifs <;> nlinarith [(le_of_lt hpos : (0 : ℝ) ≤ ε)])
    have this : rd_Phi T β u' p f c h (dd s) ≤ 0 := this
    rw [hΦ] at this
    simp only [η]
    linarith
  have hηs : ∀ s, η s * (f (s :: h) ⬝ᵥ θ h + Dbar (s :: h)) = 0 := by
    intro s
    by_cases hbind : f (s :: h) ⬝ᵥ θ h + Dbar (s :: h) = 0
    · rw [hbind, mul_zero]
    · have hs : -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h := by
        rcases lt_or_eq_of_le (hθ h s) with hlt | heq
        · exact hlt
        · exact absurd (by linarith) hbind
      have := rd_euler_eq T hβ0 hβ1 hu hd hsol h hch hcs (dd s) (by
        filter_upwards [hslack_ev (dd s)] with ε hε
        refine hfeas _ ε fun s' => ?_
        by_cases hs' : -Dbar (s' :: h) < f (s' :: h) ⬝ᵥ θ h
        · exact (hε s' hs').le
        · have hne : s' ≠ s := fun e => hs' (e ▸ hs)
          simp only [hdd s s', hne, ↓reduceIte, mul_zero, add_zero]
          exact hθ h s')
      rw [hΦ] at this
      simp only [η, this, neg_zero, zero_mul]
  refine ⟨η, hη, hηs, fun j => ?_⟩
  -- `e_j − ∑ₛ f_j(sᵗ, s) dd s` lies in the kernel
  have hk := hker (Pi.single j 1 - ∑ s, f (s :: h) j • dd s) (fun s' => by
    simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, dotProduct_single, mul_one,
      smul_eq_mul, hdd, mul_ite, mul_zero]
    simp)
  simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, dotProduct_single, mul_one,
    smul_eq_mul] at hk
  have hwj : w j = -∑ s, f (s :: h) j * η s := by
    simp only [η, mul_neg, Finset.sum_neg_distrib, neg_neg]
    linarith
  simp only [w] at hwj
  have e : ∑ s, (β * rd_condPr T h s * u' (c (s :: h)) + η s) * f (s :: h) j =
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j) + ∑ s, f (s :: h) j * η s := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  linarith

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Assumption 13.5.1: uniform lower bound on impatience

Miao, §13.5, p. 437.

* `rd_impPlan c ȳ κ α sᵗ`: the plan that adds `κ ȳ_t(sᵗ)` at `sᵗ` and scales consumption by `α`
  at every strict successor `s^τ | sᵗ`.
* `rd_Assumption1351Printed`: Assumption 13.5.1 as printed (for every `κ > 0` some `α ∈ (0, 1)`,
  independent of the node, makes the modified plan strictly preferred for *every* consumption
  plan). The book's remark that discounted expected utility satisfies it is false as printed:
  with `u = √·` the gain `√(c + κ) − √c` vanishes for large `c` while the loss
  `(1 − √α) √c` grows (`assumption_13_5_1_printed_fails`).
* `rd_Assumption1351`: the assumption for consumption plans in the order interval `[0, ȳ]`
  (Magill–Quinzii's formulation, and all that the proof of Theorem 13.5.1 uses). Continuous,
  strictly increasing discounted expected utility satisfies it when `ȳ` is bounded and bounded
  away from zero (`assumption_13_5_1`), by compactness of `[0, sup ȳ]`.
* `rd_tsum_subtree`, `rd_EU_sub_subtree`: sums of processes supported on the subtree of a node.
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S : Type*} [Fintype S]

omit [Fintype S] in
/-- The plan of Assumption 13.5.1: `cₜ(sᵗ) + κ ȳₜ(sᵗ)` at `sᵗ`, `α c_τ(s^τ)` for `s^τ | sᵗ`,
`τ > t`, and unchanged elsewhere. -/
def rd_impPlan [DecidableEq S] (c ybar : List S → ℝ) (κ α : ℝ) (h : List S) : List S → ℝ :=
  fun g => if g = h then c h + κ * ybar h else if h <:+ g then α * c g else c g

/-- Assumption 13.5.1 as printed (Miao, p. 437), for every consumption plan in `L^∞₊`. -/
def rd_Assumption1351Printed [DecidableEq S] (U : (List S → ℝ) → ℝ) (ybar : List S → ℝ) :
    Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    ∀ h c, rd_LinfPos c → U c < U (rd_impPlan c ybar κ α h)

/-- **Assumption 13.5.1** (uniform lower bound on impatience; Miao, p. 437), for consumption
plans in the order interval `[0, ȳ]`. -/
def rd_Assumption1351 [DecidableEq S] (U : (List S → ℝ) → ℝ) (ybar : List S → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    ∀ h c, rd_LinfPos c → (∀ g, c g ≤ ybar g) → U c < U (rd_impPlan c ybar κ α h)

omit [Fintype S] in
/-- The book's form implies the corrected one. -/
theorem rd_assumption1351_of_printed [DecidableEq S] {U : (List S → ℝ) → ℝ}
    {ybar : List S → ℝ} (hU : rd_Assumption1351Printed U ybar) : rd_Assumption1351 U ybar := by
  intro κ hκ
  obtain ⟨α, h0, h1, H⟩ := hU κ hκ
  exact ⟨α, h0, h1, fun h c hc _ => H h c hc⟩

/-- A process supported on the subtree of `sᵗ` has total sum equal to its subtree sum. -/
theorem rd_tsum_subtree {G : List S → ℝ} {h : List S} (hG : ∀ g, ¬ h <:+ g → G g = 0)
    (hs : Summable fun t => rd_dsum G [] t) : ∑' t, rd_dsum G [] t = ∑' j, rd_dsum G h j := by
  rw [← hs.sum_add_tsum_nat_add h.length,
    Finset.sum_eq_zero fun t ht => rd_dsum_subtree_early hG (Finset.mem_range.1 ht), zero_add]
  exact tsum_congr fun j => by rw [add_comm]; exact rd_dsum_subtree hG j

/-- At distance `j` from `sᵗ`, a factor `β^{len}` is the constant `β^{t+j}`. -/
theorem rd_dsum_pow_at (β : ℝ) (F : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum (fun g => β ^ g.length * F g) h j = β ^ (h.length + j) * rd_dsum F h j := by
  rw [rd_dsum, rd_dsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [rd_mem_paths] at hl
  simp [hl, add_comm]

/-- The change in (13.1) from a change of consumption on the subtree of `sᵗ`. -/
theorem rd_EU_sub_subtree (T : RDTree S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ}
    (hu : MonotoneOn u (Set.Ici 0)) {c c' : List S → ℝ} (hc : rd_LinfPos c)
    (hc' : rd_LinfPos c') (h : List S) (hsupp : ∀ g, ¬ h <:+ g → c' g = c g) :
    rd_EU T β u c' - rd_EU T β u c =
      ∑' j, β ^ (h.length + j) * rd_dsum (fun g => T.Pr g * (u (c' g) - u (c g))) h j := by
  obtain ⟨K, hK⟩ := rd_abs_u_le hu hc
  obtain ⟨K', hK'⟩ := rd_abs_u_le hu hc'
  have hs := (rd_EU_summable T hβ0 hβ1 u hK').sub (rd_EU_summable T hβ0 hβ1 u hK)
  rw [rd_EU, rd_EU, ← Summable.tsum_sub (rd_EU_summable T hβ0 hβ1 u hK')
    (rd_EU_summable T hβ0 hβ1 u hK)]
  set G : List S → ℝ := fun g => β ^ g.length * (T.Pr g * (u (c' g) - u (c g)))
  have e : ∀ t, β ^ t * rd_dsum (fun g => T.Pr g * u (c' g)) [] t -
      β ^ t * rd_dsum (fun g => T.Pr g * u (c g)) [] t = rd_dsum G [] t := by
    intro t
    rw [← mul_sub, ← rd_dsum_sub, ← rd_dsum_pow]
    exact rd_dsum_congr (fun g => by ring) _ _
  simp only [e] at hs ⊢
  rw [rd_tsum_subtree (fun g hg => by simp [G, hsupp g hg]) hs]
  exact tsum_congr fun j => rd_dsum_pow_at β _ h j

/-- **Assumption 13.5.1**, the remark "This assumption is satisfied by the continuous discounted
expected utility" (Miao, p. 437), for plans in `[0, ȳ]`: if `u` is continuous and strictly
increasing on `[0, ∞)`, `0 < β < 1` and `m ≤ ȳ ≤ Y` with `m > 0`, then (13.1) satisfies the
uniform lower bound on impatience. -/
theorem assumption_13_5_1 [DecidableEq S] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u : ℝ → ℝ} (hu : StrictMonoOn u (Set.Ici 0)) (hcont : ContinuousOn u (Set.Ici 0))
    {ybar : List S → ℝ} {m Y : ℝ} (hm : 0 < m) (hym : ∀ g, m ≤ ybar g)
    (hyY : ∀ g, ybar g ≤ Y) : rd_Assumption1351 (rd_EU T β u) ybar := by
  intro κ hκ
  set K := Set.Icc (0 : ℝ) Y
  have hY : m ≤ Y := (hym []).trans (hyY [])
  have hKc : IsCompact K := isCompact_Icc
  have hKsub : K ⊆ Set.Ici 0 := fun x hx => hx.1
  -- the minimal gain on `[0, Y]`
  have hγc : ContinuousOn (fun x => u (x + κ * m) - u x) K := by
    refine ContinuousOn.sub ?_ (hcont.mono hKsub)
    refine hcont.comp (continuousOn_id.add continuousOn_const) fun x hx => ?_
    exact Set.mem_Ici.2 (by have := hx.1; positivity)
  obtain ⟨x0, hx0, hmin⟩ := hKc.exists_isMinOn ⟨0, le_rfl, by linarith⟩ hγc
  set g0 := u (x0 + κ * m) - u x0
  have hg0 : 0 < g0 := by
    have := hu (Set.mem_Ici.2 hx0.1) (Set.mem_Ici.2 (by have := hx0.1; positivity))
      (by linarith [mul_pos hκ hm] : x0 < x0 + κ * m)
    simp only [g0]
    linarith
  -- uniform continuity on `[0, Y]`
  set ε0 := g0 * (1 - β) / (2 * β)
  have hε0 : 0 < ε0 := div_pos (mul_pos hg0 (by linarith)) (by linarith)
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous (hcont.mono hKsub)) ε0 hε0
  set r := min (1 / 2 : ℝ) (δ / (2 * (Y + 1)))
  have hY1 : 0 < Y + 1 := by linarith
  have hr0 : 0 < r := lt_min (by norm_num) (div_pos hδ (by linarith))
  have hr1 : r ≤ 1 / 2 := min_le_left _ _
  have hrδ : r * Y < δ := by
    have h1 : r ≤ δ / (2 * (Y + 1)) := min_le_right _ _
    have h2 : δ / (2 * (Y + 1)) * Y < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    nlinarith [hm.le.trans hY]
  refine ⟨1 - r, by linarith, by linarith, fun h c hc hcy => ?_⟩
  set c' := rd_impPlan c ybar κ (1 - r) h
  have hc0 := hc.2
  have hcK : ∀ g, c g ∈ K := fun g => ⟨hc0 g, (hcy g).trans (hyY g)⟩
  have hc' : rd_LinfPos c' := by
    obtain ⟨⟨M, hM⟩, -⟩ := hc
    refine ⟨⟨M + κ * Y, fun g => ?_⟩, fun g => ?_⟩
    · simp only [c', rd_impPlan]
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM g)
      split_ifs with h1 h2
      · subst h1
        rw [abs_le]
        have := abs_le.1 (hM g)
        constructor <;> nlinarith [hym g, hyY g, hc0 g]
      · rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - r)]
        nlinarith [hM g, abs_nonneg (c g), mul_pos hκ hm]
      · nlinarith [hM g, mul_pos hκ hm]
    · simp only [c', rd_impPlan]
      split_ifs
      · nlinarith [hym h, hc0 h]
      · exact mul_nonneg (by linarith) (hc0 g)
      · exact hc0 g
  have hsupp : ∀ g, ¬ h <:+ g → c' g = c g := by
    intro g hg
    have hne : g ≠ h := by
      rintro rfl
      exact hg List.suffix_rfl
    simp [c', rd_impPlan, hne, hg]
  rw [← sub_pos, rd_EU_sub_subtree T hβ0.le hβ1 hu.monotoneOn hc hc' h hsupp]
  set F : ℕ → ℝ := fun j =>
    β ^ (h.length + j) * rd_dsum (fun g => T.Pr g * (u (c' g) - u (c g))) h j
  have hsF : Summable F := by
    obtain ⟨K1, hK1⟩ := rd_abs_u_le hu.monotoneOn hc
    obtain ⟨K2, hK2⟩ := rd_abs_u_le hu.monotoneOn hc'
    refine Summable.of_norm_bounded (((summable_geometric_of_lt_one hβ0.le hβ1).mul_left
      (β ^ h.length * ((K1 + K2) * T.Pr h)))) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le _), pow_add]
    have := rd_abs_dsum_Pr_le T (X := fun g => u (c' g) - u (c g)) (K := K1 + K2)
      (fun g => (abs_sub _ _).trans (by linarith [hK1 g, hK2 g])) h j
    calc β ^ h.length * β ^ j * |rd_dsum (fun g => T.Pr g * (u (c' g) - u (c g))) h j|
        ≤ β ^ h.length * β ^ j * ((K1 + K2) * T.Pr h) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = β ^ h.length * ((K1 + K2) * T.Pr h) * β ^ j := by ring
  rw [hsF.tsum_eq_zero_add]
  -- the gain at `sᵗ`
  have hF0 : β ^ h.length * T.Pr h * g0 ≤ F 0 := by
    simp only [F, add_zero, rd_dsum_zero]
    have hval : c' h = c h + κ * ybar h := by simp [c', rd_impPlan]
    rw [hval]
    have h1 : u (c h + κ * m) ≤ u (c h + κ * ybar h) :=
      hu.monotoneOn (Set.mem_Ici.2 (by have := hc0 h; positivity))
        (Set.mem_Ici.2 (by have := hc0 h; nlinarith [hym h])) (by nlinarith [hym h])
    have h2 := hmin (hcK h)
    simp only [Set.mem_ofPred_eq] at h2
    have : g0 ≤ u (c h + κ * ybar h) - u (c h) := by
      simp only [g0]
      linarith
    have := mul_le_mul_of_nonneg_left this (mul_nonneg (pow_nonneg hβ0.le h.length)
      (T.pos h).le)
    linarith
  -- the losses at the strict successors
  have hFs : ∀ j, -(β ^ h.length * T.Pr h * ε0 * β ^ (j + 1)) ≤ F (j + 1) := by
    intro j
    simp only [F]
    have hd : -(ε0 * T.Pr h) ≤ rd_dsum (fun g => T.Pr g * (u (c' g) - u (c g))) h (j + 1) := by
      rw [← rd_dsum_Pr T h (j + 1), ← rd_dsum_const_mul, ← rd_dsum_neg]
      unfold rd_dsum
      refine Finset.sum_le_sum fun l hl => ?_
      rw [rd_mem_paths] at hl
      have hne : l ++ h ≠ h := fun e => by
        have := congrArg List.length e
        simp only [List.length_append] at this
        omega
      have hval : c' (l ++ h) = (1 - r) * c (l ++ h) := by
        simp [c', rd_impPlan, hne, List.suffix_append]
      dsimp only
      rw [hval]
      have hmem : (1 - r) * c (l ++ h) ∈ K :=
        ⟨mul_nonneg (by linarith) (hc0 _), by nlinarith [(hcK (l ++ h)).2, hc0 (l ++ h)]⟩
      have hdist : dist ((1 - r) * c (l ++ h)) (c (l ++ h)) < δ := by
        rw [Real.dist_eq, show (1 - r) * c (l ++ h) - c (l ++ h) = -(r * c (l ++ h)) by ring,
          abs_neg, abs_of_nonneg (mul_nonneg hr0.le (hc0 _))]
        nlinarith [(hcK (l ++ h)).2]
      have := hδu _ hmem _ (hcK _) hdist
      rw [Real.dist_eq, abs_lt] at this
      have hP := (T.pos (l ++ h)).le
      nlinarith [this.1]
    have := mul_le_mul_of_nonneg_left hd (pow_nonneg hβ0.le (h.length + (j + 1)))
    calc -(β ^ h.length * T.Pr h * ε0 * β ^ (j + 1))
        = β ^ (h.length + (j + 1)) * -(ε0 * T.Pr h) := by ring
      _ ≤ _ := this
  have hgeo : ∑' j, -(β ^ h.length * T.Pr h * ε0 * β ^ (j + 1)) =
      -(β ^ h.length * T.Pr h * ε0 * (β / (1 - β))) := by
    rw [tsum_neg, tsum_mul_left]
    congr 2
    simp only [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1]
    ring
  have hsum := Summable.tsum_le_tsum hFs
    (by
      have := ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left
        (β ^ h.length * T.Pr h * ε0 * β)).neg
      refine this.congr fun j => ?_
      ring)
    ((summable_nat_add_iff 1).2 hsF)
  rw [hgeo] at hsum
  have hkey : β ^ h.length * T.Pr h * ε0 * (β / (1 - β)) = β ^ h.length * T.Pr h * (g0 / 2) := by
    have hb1 : 1 - β ≠ 0 := by linarith
    simp only [ε0]
    field_simp
  rw [hkey] at hsum
  have hpos : 0 < β ^ h.length * T.Pr h * (g0 / 2) :=
    mul_pos (mul_pos (pow_pos hβ0 _) (T.pos h)) (by linarith)
  nlinarith

/-- Miao, p. 437 (correction): Assumption 13.5.1 as printed fails for continuous discounted
expected utility. In a deterministic economy with `β = 1/2`, `u = √·` and `ȳ ≡ 1`, for `κ = 1`
and any `α ∈ (0, 1)` the constant plan `c ≡ (1 − √α)⁻²` is weakly preferred to the modified
plan at the root. -/
theorem assumption_13_5_1_printed_fails :
    ¬ rd_Assumption1351Printed (rd_EU (rd_uniformTree Unit) (1 / 2) Real.sqrt) fun _ => 1 := by
  intro H
  obtain ⟨α, hα0, hα1, hα⟩ := H 1 one_pos
  set a := Real.sqrt α
  have ha0 : 0 < a := Real.sqrt_pos.2 hα0
  have ha1 : a < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hα0.le hα1
  set M := (1 / (1 - a)) ^ 2
  have hM0 : 0 < M := by positivity
  have h1a : 0 < 1 - a := by linarith
  have hsM : Real.sqrt M = 1 / (1 - a) := Real.sqrt_sq (by positivity)
  set c : List Unit → ℝ := fun _ => M
  have hc : rd_LinfPos c := ⟨⟨M, fun _ => by simp [c, abs_of_pos hM0]⟩, fun _ => hM0.le⟩
  have hlt := hα [] c hc
  set c' := rd_impPlan c (fun _ => 1) 1 α []
  have hc' : rd_LinfPos c' := by
    refine ⟨⟨M + 1, fun g => ?_⟩, fun g => ?_⟩
    · simp only [c', rd_impPlan, c, List.nil_suffix, ↓reduceIte]
      split_ifs
      · rw [abs_of_pos (by linarith)]
        linarith
      · rw [abs_of_pos (mul_pos hα0 hM0)]
        nlinarith
    · simp only [c', rd_impPlan, c, List.nil_suffix, ↓reduceIte]
      split_ifs <;> positivity
  have hsupp : ∀ g, ¬ ([] : List Unit) <:+ g → c' g = c g := fun g hg =>
    absurd (List.nil_suffix) hg
  set T := rd_uniformTree Unit
  have hd := rd_EU_sub_subtree T (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (fun x _ y _ hxy => Real.sqrt_le_sqrt hxy) hc hc' [] hsupp
  set G : List Unit → ℝ := fun g => T.Pr g * (Real.sqrt (c' g) - Real.sqrt (c g))
  have hsαM : Real.sqrt (α * M) = a / (1 - a) := by
    rw [Real.sqrt_mul hα0.le, hsM]
    ring
  have hG0 : rd_dsum G [] 0 = Real.sqrt (M + 1) - Real.sqrt M := by
    simp [rd_dsum_zero, G, c', rd_impPlan, c, T.root]
  have hGs : ∀ j, rd_dsum G [] (j + 1) = -1 := by
    intro j
    have : rd_dsum G [] (j + 1) = rd_dsum (fun g => -1 * T.Pr g) [] (j + 1) := by
      unfold rd_dsum
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [rd_mem_paths] at hl
      have hne : l ++ [] ≠ [] := by
        intro e
        rw [List.append_nil] at e
        rw [e] at hl
        simp at hl
      simp only [G, c', rd_impPlan, c, hne, ↓reduceIte, List.nil_suffix, hsαM, hsM]
      field_simp
      ring
    rw [this, rd_dsum_const_mul, rd_dsum_Pr, T.root, mul_one]
  simp only [List.length_nil, zero_add] at hd
  have hsF : Summable fun j => (1 / 2 : ℝ) ^ j * rd_dsum G [] j := by
    refine (summable_nat_add_iff 1).1 ?_
    have : (fun j => (1 / 2 : ℝ) ^ (j + 1) * rd_dsum G [] (j + 1)) =
        fun j => -((1 / 2) * (1 / 2 : ℝ) ^ j) := by
      funext j
      rw [hGs]
      simp [pow_succ]
      ring
    rw [this]
    exact ((summable_geometric_two).mul_left (1 / 2)).neg
  rw [hsF.tsum_eq_zero_add] at hd
  have hrest : ∑' j, (1 / 2 : ℝ) ^ (j + 1) * rd_dsum G [] (j + 1) = -1 := by
    have : (fun j => (1 / 2 : ℝ) ^ (j + 1) * rd_dsum G [] (j + 1)) =
        fun j => -((1 / 2) * (1 / 2 : ℝ) ^ j) := by
      funext j
      rw [hGs]
      simp [pow_succ]
      ring
    rw [this, tsum_neg, tsum_mul_left, tsum_geometric_two]
    norm_num
  rw [hrest] at hd
  simp only [pow_zero, one_mul, hG0] at hd
  have hle : Real.sqrt (M + 1) ≤ Real.sqrt M + 1 := by
    rw [Real.sqrt_le_left]
    · nlinarith [Real.sq_sqrt hM0.le, Real.sqrt_nonneg M]
    · positivity
  have : rd_EU T (1 / 2) Real.sqrt c' ≤ rd_EU T (1 / 2) Real.sqrt c := by
    linarith
  exact absurd hlt (not_lt.2 this)

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equivalence of equilibria: Theorem 13.5.1

Miao, §13.5, pp. 435–439. All assets are in zero supply and `θⁱ_{−1} = 0`.

* `rd_RadnerBCnb`, `rd_RadnerDCnb`: Radner equilibria with nonbinding *bounded* borrowing or debt
  limits (bounded limits are what makes Example 13.5.1 a counterexample).
* **Theorem 13.5.1, "if"** (`theorem_13_5_1_if`, corrected). Under complete markets and
  Assumption 13.5.1, a competitive equilibrium with transversality condition `(c, θ, π, p)` yields
  a Radner equilibrium with nonbinding bounded borrowing constraints and one with nonbinding
  bounded debt constraints, with the same allocation and prices but with the *replicating*
  strategies `θ̃ⁱ` (`p_t · θ̃ⁱ_t = (1/q⁰_t) ∑_{s^τ ≻ sᵗ} q⁰ (cⁱ − yⁱ)`). The book's statement with
  the given `θ` is false: the date-0 transversality condition (13.21) allows a zero-cost position
  that is a bubble on one branch and a Ponzi scheme on another (`theorem_13_5_1_counterexample`
  in `RDCounter`). The bound on `p_t · θ̃ⁱ_t` is the book's scaling argument
  (`rd_impatience_bound`), applied to the Arrow–Debreu problem (ii).
* **Theorem 13.5.1, "only if"** (`theorem_13_5_1_onlyIf`), for the discounted expected utility
  (13.1) with differentiable concave `uⁱ` and consumption bounded away from zero (the book's
  sketch uses separation and Mackey continuity, citing Magill and Quinzii): the Euler equations
  give a common state price process `q⁰ = βᵗ Pr u′(c)/u′(c₀)` in `L¹`, the bounded limits give the
  transversality condition, and concavity gives optimality in the Arrow–Debreu budget set.
* `rd_budget_binds`: with strictly increasing utility the budget constraints bind at an optimum.
* `rd_pv_eq`: the equality version of (13.19).
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J ι : Type*} [Fintype S] [Fintype J] [Fintype ι]

/-- A Radner equilibrium with nonbinding bounded borrowing constraints (zero initial holdings). -/
def rd_RadnerBCnb (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (p f : List S → J → ℝ)
    (c : ι → List S → ℝ) (θ : ι → List S → J → ℝ) : Prop :=
  ∃ Bbar : ι → List S → ℝ, (∀ i, rd_Bdd (Bbar i)) ∧ (∀ i h, 0 ≤ Bbar i h) ∧
    rd_RadnerBC U y (fun _ => 0) p f Bbar c θ ∧ ∀ i h, -Bbar i h < p h ⬝ᵥ θ i h

/-- A Radner equilibrium with nonbinding bounded debt constraints (zero initial holdings). -/
def rd_RadnerDCnb (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (p f : List S → J → ℝ)
    (c : ι → List S → ℝ) (θ : ι → List S → J → ℝ) : Prop :=
  ∃ Dbar : ι → List S → ℝ, (∀ i, rd_Bdd (Dbar i)) ∧ (∀ i h, 0 ≤ Dbar i h) ∧
    rd_RadnerDC U y (fun _ => 0) p f Dbar c θ ∧ ∀ i h s, -Dbar i (s :: h) < f (s :: h) ⬝ᵥ θ i h

omit [Fintype J] [Fintype S] in
/-- The scaled-down plan of the proof of Theorem 13.5.1: `cₜ + (1 − α) Vₜ` at `sᵗ` and `α c` on
the strict successors. -/
theorem rd_scaled_plan_le [DecidableEq S] (c ybar : List S → ℝ) (α V : ℝ) (h : List S)
    (hV : ybar h ≤ (1 - α) * V) (g : List S) :
    rd_impPlan c ybar 1 α h g ≤
      (if g = h then c h + (1 - α) * V else if h <:+ g then α * c g else c g) := by
  simp only [rd_impPlan]
  split_ifs <;> linarith

/-- The book's bound from the uniform lower bound on impatience (Miao, pp. 437–438), in the
Arrow–Debreu problem: if `cⁱ` maximises an increasing `Uⁱ` over `L^∞₊` subject to (13.5) with
`q⁰ ∈ L¹`, `cⁱ ≥ 0` and `yⁱ ≥ 0` bounded, and `α` is given by Assumption 13.5.1 for `κ = 1`,
then the value `Vₜ = (1/q⁰ₜ) ∑_{s^τ ≻ sᵗ} q⁰ (cⁱ − yⁱ)` satisfies `(1 − α) Vₜ < ȳₜ`. -/
theorem rd_impatience_bound [DecidableEq S] {U : (List S → ℝ) → ℝ} (hU : rd_Mono U)
    {ybar : List S → ℝ} (hy0 : ∀ g, 0 ≤ ybar g) {q y c : List S → ℝ} (hq : ∀ h, 0 < q h)
    (hL : rd_L1 q) (hyb : rd_LinfPos y) (hc : rd_LinfPos c)
    (hopt : rd_SolvesC U (fun c' => rd_LinfPos c' ∧ rd_ADBudget q y c') c)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hA : ∀ h, U c < U (rd_impPlan c ybar 1 α h)) (hybb : rd_Bdd ybar) (h : List S) :
    (1 - α) * (rd_W q (fun g => c g - y g) h / q h) < ybar h := by
  by_contra hcon
  push Not at hcon
  set V := rd_W q (fun g => c g - y g) h / q h
  set ĉ : List S → ℝ := fun g => if g = h then c h + (1 - α) * V else if h <:+ g then α * c g
    else c g
  obtain ⟨⟨M, hM⟩, hc0⟩ := hc
  have hĉ : rd_LinfPos ĉ := by
    refine ⟨⟨M + |(1 - α) * V|, fun g => ?_⟩, fun g => ?_⟩
    · simp only [ĉ]
      split_ifs with h1 h2
      · subst h1
        exact (abs_add_le _ _).trans (add_le_add (hM _) le_rfl)
      · rw [abs_mul, abs_of_pos hα0]
        nlinarith [hM g, abs_nonneg (c g), abs_nonneg ((1 - α) * V)]
      · linarith [hM g, abs_nonneg ((1 - α) * V)]
    · simp only [ĉ]
      split_ifs with h1
      · subst h1
        linarith [hc0 g, hy0 g]
      · exact mul_nonneg hα0.le (hc0 g)
      · exact hc0 g
  have hplan : rd_LinfPos (rd_impPlan c ybar 1 α h) := by
    obtain ⟨Yb, hYb⟩ := hybb
    refine ⟨⟨M + Yb, fun g => ?_⟩, fun g => ?_⟩
    · simp only [rd_impPlan]
      split_ifs with h1
      · subst h1
        rw [one_mul]
        exact (abs_add_le _ _).trans (add_le_add (hM _) (hYb _))
      · rw [abs_mul, abs_of_pos hα0]
        nlinarith [hM g, abs_nonneg (c g), abs_nonneg (ybar g), hYb g]
      · linarith [hM g, (abs_nonneg _).trans (hYb g)]
    · simp only [rd_impPlan]
      split_ifs
      · linarith [hc0 h, hy0 h]
      · exact mul_nonneg hα0.le (hc0 g)
      · exact hc0 g
  have hle : U (rd_impPlan c ybar 1 α h) ≤ U ĉ :=
    hU _ _ hplan hĉ (rd_scaled_plan_le c ybar α V h hcon)
  -- `ĉ` is affordable
  have hcb : rd_Bdd c := ⟨M, hM⟩
  have hxs : Summable fun t => rd_dsum (fun g => |q g * (c g - y g)|) [] t :=
    rd_L1_mul_abs hL (rd_bdd_sub hcb hyb.1)
  have hbud : rd_ADBudget q y ĉ := by
    have hbc := (hopt.1).2
    rw [rd_ADBudget] at hbc ⊢
    set G : List S → ℝ := fun g => q g * (ĉ g - c g)
    have hGs : Summable fun t => rd_dsum (fun g => |G g|) [] t :=
      rd_L1_mul_abs hL (rd_bdd_sub hĉ.1 hcb)
    have hsplit : ∑' t, rd_dsum (fun g => q g * ĉ g) [] t =
        ∑' t, rd_dsum (fun g => q g * c g) [] t + ∑' t, rd_dsum G [] t := by
      rw [← Summable.tsum_add (rd_L1_mul hL hcb)
        (Summable.of_norm_bounded hGs fun t => by
          rw [Real.norm_eq_abs]; exact rd_abs_dsum_le _ _ _)]
      refine tsum_congr fun t => ?_
      rw [← rd_dsum_add]
      exact rd_dsum_congr (fun g => by simp only [G]; ring) _ _
    have hGsupp : ∀ g, ¬ h <:+ g → G g = 0 := by
      intro g hg
      have hne : g ≠ h := by
        rintro rfl
        exact hg List.suffix_rfl
      simp [G, ĉ, hne, hg]
    have hGsum : Summable fun t => rd_dsum G [] t :=
      Summable.of_norm_bounded hGs fun t => by
        rw [Real.norm_eq_abs]; exact rd_abs_dsum_le _ _ _
    rw [rd_tsum_subtree hGsupp hGsum, (rd_summable_subtree hGs h).tsum_eq_zero_add,
      rd_dsum_zero] at hsplit
    have hGh : G h = (1 - α) * rd_W q (fun g => c g - y g) h := by
      simp only [G, ĉ, ↓reduceIte, V]
      field_simp [(hq h).ne']
      ring
    have hGj : ∀ j, rd_dsum G h (j + 1) = -(1 - α) * rd_dsum (fun g => q g * c g) h (j + 1) := by
      intro j
      rw [← rd_dsum_const_mul]
      unfold rd_dsum
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [rd_mem_paths] at hl
      have hne : l ++ h ≠ h := fun e => by
        have := congrArg List.length e
        simp only [List.length_append] at this
        omega
      simp only [G, ĉ, hne, ↓reduceIte, List.suffix_append]
      ring
    have hcs := rd_summable_subtree (rd_L1_mul_abs hL hcb) h
    have hys := rd_summable_subtree (rd_L1_mul_abs hL hyb.1) h
    have hW : rd_W q (fun g => c g - y g) h = ∑' j, rd_dsum (fun g => q g * c g) h (j + 1) -
        ∑' j, rd_dsum (fun g => q g * y g) h (j + 1) := by
      rw [rd_W, ← Summable.tsum_sub ((summable_nat_add_iff 1).2 hcs)
        ((summable_nat_add_iff 1).2 hys)]
      refine tsum_congr fun j => ?_
      rw [← rd_dsum_sub]
      exact rd_dsum_congr (fun g => by ring) _ _
    have hrest : ∑' j, rd_dsum G h (j + 1) =
        -(1 - α) * ∑' j, rd_dsum (fun g => q g * c g) h (j + 1) := by
      simp only [hGj]
      exact tsum_mul_left
    have hy0' : 0 ≤ ∑' j, rd_dsum (fun g => q g * y g) h (j + 1) :=
      tsum_nonneg fun j => rd_dsum_nonneg (fun g => mul_nonneg (hq g).le (hyb.2 g)) _ _
    rw [hGh, hrest, hW] at hsplit
    nlinarith
  have hfin := hopt.2 ĉ ⟨hĉ, hbud⟩
  linarith [hA h]

/-- **Theorem 13.5.1, "if"** (Miao, pp. 435–438), corrected. Suppose markets are complete (rank
`S` at every node), utilities are increasing and satisfy Assumption 13.5.1 on `[0, ȳ]`,
endowments are bounded and nonnegative, assets are in zero supply and `θⁱ_{−1} = 0`. If
`(c, θ, π, p)` is a competitive equilibrium with transversality condition, then `(c, θ̃, p)` is a
Radner equilibrium with nonbinding bounded borrowing constraints, and also one with nonbinding
bounded debt constraints, where `θ̃ⁱ` is the replicating strategy of `cⁱ − yⁱ`. -/
theorem theorem_13_5_1_if [DecidableEq S] (T : RDTree S) {U : ι → (List S → ℝ) → ℝ}
    (hU : ∀ i, rd_Mono (U i)) {y : ι → List S → ℝ} (hy : ∀ i, rd_LinfPos (y i))
    (hA : ∀ i, rd_Assumption1351 (U i) fun g => ∑ k, y k g) {f : List S → J → ℝ}
    (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) {c : ι → List S → ℝ}
    {θ : ι → List S → J → ℝ} {pd : List S → ℝ} {p : List S → J → ℝ}
    (hE : rd_CETVC T U y (fun _ => 0) f c θ pd p) :
    rd_RadnerBCnb U y p f c (fun i => rd_repl f (fun g => pd g * T.Pr g) fun g => c i g - y i g) ∧
      rd_RadnerDCnb U y p f c
        (fun i => rd_repl f (fun g => pd g * T.Pr g) fun g => c i g - y i g) := by
  classical
  obtain ⟨hc, hL, hpd, -, -, -, hii, hsp, hclear, -⟩ := hE
  set q : List S → ℝ := fun g => pd g * T.Pr g
  have hq : ∀ h, 0 < q h := fun h => mul_pos (hpd h) (T.pos h)
  set θ' : ι → List S → J → ℝ := fun i => rd_repl f q fun g => c i g - y i g
  have hii' : ∀ i, rd_SolvesC (U i) (fun c' => rd_LinfPos c' ∧ rd_ADBudget q (y i) c') (c i) := by
    intro i
    simpa [rd_ADBudget] using hii i
  have hAD : ∀ i, rd_ADBudget q (y i) (c i) := fun i => (hii' i).1.2
  have hrb := fun i => rd_repl_budget hsp hL hrank (hc i).1 (hy i).1 (hAD i)
  set ybar : List S → ℝ := fun g => ∑ k, y k g
  have hy0 : ∀ g, 0 ≤ ybar g := fun g => Finset.sum_nonneg fun k _ => (hy k).2 g
  choose My hMy using fun i => (hy i).1
  set Y := ∑ k, |My k|
  have hyY : ∀ g, ybar g ≤ Y := fun g => Finset.sum_le_sum fun k _ =>
    (le_abs_self _).trans ((hMy k g).trans (le_abs_self _))
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hybb : rd_Bdd ybar := ⟨Y, fun g => by rw [abs_of_nonneg (hy0 g)]; exact hyY g⟩
  have hcy : ∀ i g, c i g ≤ ybar g := by
    intro i g
    rw [show ybar g = ∑ k, c k g from (hclear g).symm]
    exact Finset.single_le_sum (f := fun k => c k g) (fun k _ => (hc k).2 g) (Finset.mem_univ i)
  choose α hα0 hα1 hαA using fun i => hA i 1 one_pos
  have hval : ∀ i h, p h ⬝ᵥ θ' i h = rd_W q (fun g => c i g - y i g) h / q h := by
    intro i h
    rw [← rd_repl_value hsp hrank (rd_L1_mul_abs hL (rd_bdd_sub (hc i).1 (hy i).1)) h,
      mul_div_cancel_left₀ _ (hq h).ne']
  have hup : ∀ i h, p h ⬝ᵥ θ' i h < Y / (1 - α i) := by
    intro i h
    have := rd_impatience_bound (hU i) hy0 hq hL (hy i) (hc i) (hii' i) (hα0 i) (hα1 i)
      (fun h => hαA i h (c i) (hc i) (hcy i)) hybb h
    rw [← hval] at this
    have h1 : 0 < 1 - α i := by linarith [hα1 i]
    rw [lt_div_iff₀ h1]
    linarith [hyY h]
  set Bsum := ∑ k, Y / (1 - α k)
  have hUb0 : ∀ k, 0 ≤ Y / (1 - α k) := fun k => div_nonneg hY0 (by linarith [hα1 k])
  have hsum0 : ∀ h, ∑ k, p h ⬝ᵥ θ' k h = 0 := by
    intro h
    rw [← dotProduct_sum]
    have := rd_repl_sum_zero f hL (fun i => (hc i).1) (fun i => (hy i).1) hclear h
    simp only [θ', ← Finset.sum_apply] at this ⊢
    rw [show (∑ k, rd_repl f q fun g => c k g - y k g) h = 0 by simpa using this]
    simp
  have hlow : ∀ i h, -Bsum ≤ p h ⬝ᵥ θ' i h := by
    intro i h
    have := hsum0 h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at this
    have hle : ∑ k ∈ Finset.univ.erase i, p h ⬝ᵥ θ' k h ≤ Bsum :=
      (Finset.sum_le_sum fun k _ => (hup k h).le).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun k _ _ => hUb0 k)
    linarith
  have hBs0 : 0 ≤ Bsum := Finset.sum_nonneg fun k _ => hUb0 k
  have hθsum : ∀ h, ∑ i, θ' i h = ∑ _i : ι, (0 : J → ℝ) := by
    intro h
    rw [Finset.sum_const_zero]
    exact rd_repl_sum_zero f hL (fun i => (hc i).1) (fun i => (hy i).1) hclear h
  have hgoods : ∀ h, ∑ i, c i h = ∑ i, y i h + (rd_fz p f h - p h) ⬝ᵥ ∑ _i : ι, (0 : J → ℝ) := by
    intro h
    simp [hclear h]
  have hyB : ∀ i h, y i h ≤ Y := fun i h => (le_abs_self _).trans ((hMy i h).trans
    ((le_abs_self _).trans (Finset.single_le_sum (f := fun k => |My k|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ i))))
  refine ⟨⟨fun _ _ => Bsum + 1, fun _ => ⟨|Bsum + 1|, fun _ => le_rfl⟩, fun _ _ => by linarith,
    ⟨fun i => ⟨⟨hc i, (hrb i).1, fun h => by linarith [hlow i h]⟩, fun c' θ'' ⟨hc', hB', hθ''⟩ =>
      (hii' i).2 c' ⟨hc', by
        have := rd_AD_of_BC hsp hL hB' (Bbar := fun _ => Bsum + 1)
          ⟨|Bsum + 1|, fun _ => le_rfl⟩ hθ'' hc'.1 (hy i).1
        simpa [rd_ADBudget] using this⟩⟩, hgoods, hθsum⟩,
    fun i h => by linarith [hlow i h]⟩,
    ⟨fun _ _ => Bsum + Y + 1, fun _ => ⟨|Bsum + Y + 1|, fun _ => le_rfl⟩, fun _ _ => by linarith,
    ⟨fun i => ⟨⟨hc i, (hrb i).1, fun h s => ?_⟩, fun c' θ'' ⟨hc', hB', hθ''⟩ =>
      (hii' i).2 c' ⟨hc', by
        have := rd_AD_of_DC hsp hL hB' (Dbar := fun _ => Bsum + Y + 1)
          ⟨|Bsum + Y + 1|, fun _ => le_rfl⟩ hθ'' hc'.1 (hy i).1
        simpa [rd_ADBudget] using this⟩⟩, hgoods, hθsum⟩, fun i h s => ?_⟩⟩
  · have e := (hrb i).2.2 s h
    have := hlow i (s :: h)
    linarith [(hc i).2 (s :: h), hyB i (s :: h)]
  · have e := (hrb i).2.2 s h
    have := hlow i (s :: h)
    linarith [(hc i).2 (s :: h), hyB i (s :: h)]

omit [Fintype S] in
/-- With strictly increasing utility the budget constraints (13.11) bind at an optimum. -/
theorem rd_budget_binds {U : (List S → ℝ) → ℝ} (hU : rd_StrictIncr U)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Θa : Set (List S → J → ℝ)}
    {c : List S → ℝ} {θ : List S → J → ℝ} (hsol : rd_Solves U (rd_SeqFeas p f y θm1 Θa) c θ) :
    rd_BudgetEq p f y θm1 c θ := by
  classical
  intro h
  obtain ⟨⟨⟨M, hM⟩, hc0⟩, hB, hΘ⟩ := hsol.1
  by_contra hne
  have hlt : c h + p h ⬝ᵥ θ h < rd_fz p f h ⬝ᵥ rd_prev θ θm1 h + y h :=
    lt_of_le_of_ne (hB h) hne
  set e := rd_fz p f h ⬝ᵥ rd_prev θ θm1 h + y h - (c h + p h ⬝ᵥ θ h)
  have he : 0 < e := by simp only [e]; linarith
  set c' : List S → ℝ := fun g => c g + if g = h then e else 0
  have hc' : rd_SeqFeas p f y θm1 Θa c' θ := by
    refine ⟨⟨⟨M + e, fun g => ?_⟩, fun g => ?_⟩, fun g => ?_, hΘ⟩
    · simp only [c']
      refine (abs_add_le _ _).trans (add_le_add (hM g) ?_)
      split_ifs <;> simp [abs_of_pos he, he.le]
    · simp only [c']
      split_ifs <;> linarith [hc0 g]
    · simp only [c']
      split_ifs with hg
      · subst hg
        simp only [e]
        linarith
      · linarith [hB g]
  have := hU c c' hsol.1.1 hc'.1 (fun g => by simp only [c']; split_ifs <;> linarith) (by
    intro hcc
    have := congrFun hcc h
    simp only [c', ↓reduceIte] at this
    linarith)
  exact absurd (hsol.2 c' θ hc') (not_le.2 this)

/-- (13.19) with equality when the budget constraints bind. -/
theorem rd_pv_eq {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_BudgetEq p f y θm1 c θ) (h : List S) (T : ℕ) :
    ∑ j ∈ Finset.range (T + 1), rd_dsum (fun g => q g * c g) h j +
        rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T =
      q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) +
        ∑ j ∈ Finset.range (T + 1), rd_dsum (fun g => q g * y g) h j := by
  have hpt : ∀ g, q g * c g + q g * (p g ⬝ᵥ θ g) =
      q g * (rd_fz p f g ⬝ᵥ rd_prev θ θm1 g) + q g * y g := by
    intro g
    rw [← mul_add, ← mul_add, hB g]
  induction T with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, rd_dsum_zero]
    exact hpt h
  | succ T ih =>
    rw [Finset.sum_range_succ (fun j => rd_dsum (fun g => q g * c g) h j) (T + 1),
      Finset.sum_range_succ (fun j => rd_dsum (fun g => q g * y g) h j) (T + 1)]
    have hV : rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T =
        rd_dsum (fun g => q g * (rd_fz p f g ⬝ᵥ rd_prev θ θm1 g)) h (T + 1) := by
      rw [rd_dsum_succ']
      exact rd_dsum_congr (fun g => rd_statePrice_dot hq g (θ g)) h T
    have hstep := congrArg (fun F => F) (rd_dsum_congr hpt h (T + 1))
    rw [rd_dsum_add, rd_dsum_add] at hstep
    linarith

/-- The gradient inequality makes the marginal utility decreasing. -/
theorem rd_gradIneq_antitone {u u' : ℝ → ℝ} (hg : rd_GradIneq u u') {x z : ℝ} (hx : 0 < x)
    (hxz : x ≤ z) : u' z ≤ u' x := by
  have hz : 0 < z := lt_of_lt_of_le hx hxz
  have h1 := hg x hx z hz.le
  have h2 := hg z hz x hx.le
  rcases lt_or_eq_of_le hxz with hlt | heq
  · nlinarith
  · rw [heq]

/-- **Theorem 13.5.1, "only if"** (Miao, pp. 435, 438–439), for discounted expected utility
(13.1): with `uⁱ` strictly increasing, differentiable with positive derivative and concave
(gradient inequality), complete markets, `p ∈ (L^∞₊)ᴶ`, consumption bounded away from zero, zero
supply and `θⁱ_{−1} = 0`, a Radner equilibrium with nonbinding bounded borrowing constraints is a
competitive equilibrium with transversality condition, with the state price deflator
`π = q⁰/Pr`, `q⁰ = βᵗ Pr u′(c)/u′(c₀)` of any agent. -/
theorem theorem_13_5_1_onlyIf [Nonempty ι] (T : RDTree S)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u u' : ι → ℝ → ℝ}
    (hu : ∀ i, StrictMonoOn (u i) (Set.Ici 0)) (hd : ∀ i x, 0 < x → HasDerivAt (u i) (u' i x) x)
    (hu'pos : ∀ i x, 0 < x → 0 < u' i x) (hgrad : ∀ i, rd_GradIneq (u i) (u' i))
    {y : ι → List S → ℝ} (hy : ∀ i, rd_LinfPos (y i)) {p f : List S → J → ℝ}
    (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) (hp0 : ∀ h j, 0 ≤ p h j)
    (hpb : ∀ j, rd_Bdd fun h => p h j) {c : ι → List S → ℝ} {θ : ι → List S → J → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hcε : ∀ i h, ε ≤ c i h)
    (hR : rd_RadnerBCnb (fun i => rd_EU T β (u i)) y p f c θ) :
    ∃ pd, rd_CETVC T (fun i => rd_EU T β (u i)) y (fun _ => 0) f c θ pd p := by
  classical
  obtain ⟨Bbar, hBb, -, ⟨hsol, hgoods, hθsum⟩, hslack⟩ := hR
  have hcpos : ∀ i h, 0 < c i h := fun i h => lt_of_lt_of_le hε (hcε i h)
  -- Euler equations for every agent at every node
  have heul : ∀ i h j, rd_Phi T β (u' i) p f (c i) h (Pi.single j 1) = 0 := by
    intro i h j
    refine rd_euler_eq T hβ0 hβ1 (hu i).monotoneOn (hd i) (hsol i) h (hcpos i h)
      (fun s => hcpos i (s :: h)) _ ?_
    have : Tendsto (fun e : ℝ => p h ⬝ᵥ θ i h + e * (p h ⬝ᵥ Pi.single j 1)) (𝓝 0)
        (𝓝 (p h ⬝ᵥ θ i h)) := by
      simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (p h ⬝ᵥ Pi.single j 1)).const_add _
    filter_upwards [this.eventually (lt_mem_nhds (hslack i h))] with e he
    exact rd_BC_feas (hsol i).1.2.2 h _ e he.le
  set qi : ι → List S → ℝ := fun i h => β ^ h.length * T.Pr h * u' i (c i h) / u' i (c i [])
  have hqi : ∀ i, rd_StatePrice p f (qi i) := fun i =>
    rd_statePrice_of_euler T hβ0 (fun h => hu'pos i _ (hcpos i h)) (heul i)
  have hqi0 : ∀ i, qi i [] = 1 := fun i => by
    simp [qi, T.root, (hu'pos i _ (hcpos i [])).ne']
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  set q := qi i0
  have hq := hqi i0
  have hqeq : ∀ i, qi i = q := fun i => funext fun h => by
    rw [rd_statePrice_unique hrank hq (hqi i) h, hqi0, hqi0 i0, div_one, one_mul]
  -- `q⁰ ∈ L¹`
  set K := u' i0 ε / u' i0 (c i0 [])
  have hL : rd_L1 q := by
    refine Summable.of_nonneg_of_le (fun t => rd_dsum_nonneg (fun g => abs_nonneg _) _ _)
      (fun t => ?_) ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left K)
    have : ∀ g, |q g| ≤ β ^ g.length * (K * T.Pr g) := by
      intro g
      have hpos := (hq.1 g)
      rw [abs_of_pos hpos]
      simp only [qi, K]
      have hm := rd_gradIneq_antitone (hgrad i0) hε (hcε i0 g)
      have hu0 := hu'pos i0 _ (hcpos i0 [])
      rw [div_le_iff₀ hu0]
      have : β ^ g.length * T.Pr g * u' i0 (c i0 g) ≤ β ^ g.length * T.Pr g * u' i0 ε :=
        mul_le_mul_of_nonneg_left hm (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le)
      calc β ^ g.length * T.Pr g * u' i0 (c i0 g) ≤ β ^ g.length * T.Pr g * u' i0 ε := this
        _ = β ^ g.length * (u' i0 ε / u' i0 (c i0 []) * T.Pr g) * u' i0 (c i0 []) := by
          field_simp
    refine (rd_dsum_mono this [] t).trans ?_
    rw [rd_dsum_pow, rd_dsum_const_mul, rd_dsum_Pr, T.root]
    linarith
  -- bounded values `p · θⁱ`
  choose Bm hBm using hBb
  set Bsum := ∑ k, |Bm k|
  have hpθ : ∀ i, rd_Bdd fun h => p h ⬝ᵥ θ i h := by
    intro i
    refine ⟨Bsum, fun h => abs_le.2 ⟨?_, ?_⟩⟩
    · have h1 := hslack i h
      have h2 := (le_abs_self _).trans ((hBm i h).trans (le_abs_self (Bm i)))
      have h3 := Finset.single_le_sum (f := fun k => |Bm k|) (fun k _ => abs_nonneg _)
        (Finset.mem_univ i)
      linarith
    · have hs : ∑ k, p h ⬝ᵥ θ k h = 0 := by
        rw [← dotProduct_sum]
        have := hθsum h
        simp only [Finset.sum_const_zero] at this
        rw [show ∑ k, θ k h = 0 by simpa using this, dotProduct_zero]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hs
      have : ∀ k, -|Bm k| ≤ p h ⬝ᵥ θ k h := fun k => by
        have h1 := hslack k h
        have h2 := (le_abs_self _).trans ((hBm k h).trans (le_abs_self (Bm k)))
        linarith
      have hle : -∑ k ∈ Finset.univ.erase i, |Bm k| ≤ ∑ k ∈ Finset.univ.erase i,
          p h ⬝ᵥ θ k h := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum fun k _ => this k
      have hsub : ∑ k ∈ Finset.univ.erase i, |Bm k| ≤ Bsum :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun k _ _ => abs_nonneg _
      linarith
  have hTVC : ∀ i, rd_TVC q p (θ i) := fun i => rd_L1_mul_tendsto hL (hpθ i)
  have hBeq : ∀ i, rd_BudgetEq p f (y i) 0 (c i) (θ i) := fun i =>
    rd_budget_binds (rd_eq_13_1 T hβ0 hβ1 (hu i)) (hsol i)
  -- the Arrow–Debreu budget holds with equality
  have hADeq : ∀ i, ∑' t, rd_dsum (fun g => q g * c i g) [] t =
      ∑' t, rd_dsum (fun g => q g * y i g) [] t := by
    intro i
    have hcs := rd_L1_mul hL (hsol i).1.1.1
    have hys := rd_L1_mul hL (hy i).1
    have hA := hcs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have hY := (hys.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).sub (hTVC i)
    rw [sub_zero] at hY
    refine tendsto_nhds_unique hA (hY.congr fun T' => ?_)
    have := rd_pv_eq hq (hBeq i) [] T'
    simp only [rd_fz, rd_prev, dotProduct_zero, mul_zero, zero_add, Function.comp_apply] at this ⊢
    linarith
  -- optimality in the Arrow–Debreu budget set
  have hii : ∀ i, ∀ c', rd_LinfPos c' → rd_ADBudget q (y i) c' →
      rd_EU T β (u i) c' ≤ rd_EU T β (u i) (c i) := by
    intro i c' hc' hb
    have hu0 := hu'pos i _ (hcpos i [])
    have hcs := rd_L1_mul hL (hsol i).1.1.1
    have hc's := rd_L1_mul hL hc'.1
    refine rd_suff_core T hβ0 hβ1 (hu i).monotoneOn (hgrad i) (hsol i).1.1 hc' (hcpos i)
      (τ := fun n => u' i (c i []) * ∑ t ∈ Finset.range (n + 1),
        (rd_dsum (fun g => q g * c' g) [] t - rd_dsum (fun g => q g * c i g) [] t))
      (L := u' i (c i []) * (∑' t, rd_dsum (fun g => q g * c' g) [] t -
        ∑' t, rd_dsum (fun g => q g * c i g) [] t))
      ?_ ?_ fun n => le_of_eq ?_
    · refine Tendsto.const_mul _ ?_
      rw [← Summable.tsum_sub hc's hcs]
      exact (hc's.sub hcs).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    · rw [rd_ADBudget, ← hADeq i] at hb
      exact mul_nonpos_of_nonneg_of_nonpos hu0.le (by linarith)
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← rd_dsum_sub, ← rd_dsum_const_mul]
      refine rd_dsum_congr (fun g => ?_) _ _
      rw [← hqeq i]
      simp only [qi]
      field_simp
  refine ⟨fun g => q g / T.Pr g, ?_⟩
  have hqpd : ∀ g, q g / T.Pr g * T.Pr g = q g := fun g => div_mul_cancel₀ _ (T.pos g).ne'
  simp only [rd_CETVC, hqpd]
  refine ⟨fun i => (hsol i).1.1, hL, fun h => div_pos (hq.1 h) (T.pos h), hp0, hpb,
    fun i => ⟨⟨(hsol i).1.1, (hsol i).1.2.1, hTVC i⟩, fun c' θ' ⟨hc', hB, hT⟩ => hii i c' hc' ?_⟩,
    fun i => ⟨⟨(hsol i).1.1, ?_⟩, fun c' ⟨hc', hb⟩ => hii i c' hc' ?_⟩, hq, fun h => ?_, hθsum⟩
  · have := eq_13_22 hq hB hT (rd_L1_mul hL hc'.1) (rd_L1_mul hL (hy i).1)
    simpa [rd_ADBudget] using this
  · rw [hADeq i]
    simp
  · simpa [rd_ADBudget] using hb
  · simpa using hgoods h

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A bubble on one branch, a Ponzi scheme on the other

Counterexamples to (13.23) and to Theorem 13.5.1 ("if") as printed (Miao, pp. 433, 435).

The economy: two equally likely states each period (`rd_uniformTree Bool`), `β = 1/2`, two
agents with linear expected utility `U(c) = ∑ βᵗ E cₜ`, endowments `1`, complete Arrow
securities priced at `1/4` (so `q⁰(sᵗ) = 4⁻ᵗ`, `π(sᵗ) = 2⁻ᵗ`). Both agents consume their
endowment. The martingale `m = q⁰ V` (`rd_mg`) is `+1` along the branch that starts with `true`
and continues with `true`, `−1` along the branch that starts with `false` and continues with
`true`, and `0` elsewhere; the zero-cost strategy `ψ` (`rd_psi`) has value `V(sᵗ) = 4ᵗ m(sᵗ)`.
Agent `true` holds `ψ`, agent `false` holds `−ψ`.

* `theorem_13_5_1_counterexample`: this is a competitive equilibrium with transversality
  condition (the date-0 condition (13.21) holds because `E[π_T p_T · ψ_T] = m(s⁰) = 0`), markets
  are complete, utilities are strictly increasing and satisfy Assumption 13.5.1, but `(c, θ, p)`
  is not a Radner equilibrium with any bounded borrowing limits or bounded debt limits:
  `p · (−ψ)` and `f · (−ψ)` are unbounded below. (Theorem 13.5.1 holds with the replicating
  strategies, here `θ̃ = 0`: `theorem_13_5_1_if`.)
* `eq_13_23_counterexample`: the plan of agent `true` satisfies (13.11) and (13.21), but (13.23)
  fails at the node `(false)`.
-/

namespace Miao.CompleteMarkets

open Filter Topology

/-- The martingale `m`: `m(s⁰) = 0`, `m(s₁) = ±1` by the first shock, and afterwards `m` is
carried along shocks `true` and dropped to `0` at a shock `false`. -/
def rd_mg : List Bool → ℝ
  | [] => 0
  | [s] => if s then 1 else -1
  | s :: t :: h => if s then rd_mg (t :: h) else 0

/-- `m` is a martingale on the tree: `∑ₛ m(sᵗ, s) = m(sᵗ)`. -/
theorem rd_mg_sum (h : List Bool) : ∑ s, rd_mg (s :: h) = rd_mg h := by
  cases h with
  | nil => simp [rd_mg]
  | cons t h => simp [rd_mg]

/-- The martingale property over any number of periods. -/
theorem rd_dsum_mg (h : List Bool) (j : ℕ) : rd_dsum rd_mg h j = rd_mg h := by
  induction j generalizing h with
  | zero => exact rd_dsum_zero _ _
  | succ j ih =>
    rw [rd_dsum_succ]
    simp only [ih, rd_mg_sum]

/-- `m = 1` along the all-`true` branch. -/
theorem rd_mg_true (n : ℕ) : rd_mg (List.replicate (n + 1) true) = 1 := by
  induction n with
  | zero => simp [rd_mg]
  | succ n ih =>
    rw [List.replicate_succ] at ih ⊢
    rw [List.replicate_succ]
    simp only [rd_mg, ↓reduceIte]
    exact ih

/-- The zero-cost strategy: the Arrow holdings paying `V(sᵗ, s) = 4^{t+1} m(sᵗ, s)`. -/
noncomputable def rd_psi (h : List Bool) : Bool → ℝ := fun s => rd_mg (s :: h) * 4 ^ (h.length + 1)

/-- The probabilities of the uniform tree on `Bool`. -/
theorem rd_cx_Pr (h : List Bool) : (rd_uniformTree Bool).Pr h = (1 / 2) ^ h.length := by
  simp [rd_uniformTree]

/-- The deflator `π(sᵗ) = 2⁻ᵗ`. -/
noncomputable def rd_cxpd (h : List Bool) : ℝ := (1 / 2) ^ h.length

/-- The Arrow prices `1/4`. -/
noncomputable def rd_cxp (_h : List Bool) (_s : Bool) : ℝ := 1 / 4

/-- The state prices `q⁰ = π Pr = 4⁻ᵗ`. -/
theorem rd_cx_q (h : List Bool) :
    rd_cxpd h * (rd_uniformTree Bool).Pr h = (1 / 4) ^ h.length := by
  rw [rd_cx_Pr, rd_cxpd, ← mul_pow]
  norm_num

/-- The strategies: agent `true` holds `ψ`, agent `false` holds `−ψ`. -/
noncomputable def rd_cxθ (i : Bool) : List Bool → Bool → ℝ := if i then rd_psi else -rd_psi

/-- The cost of `ψ` at `sᵗ` is its value `4ᵗ m(sᵗ)`. -/
theorem rd_psi_cost (h : List Bool) : rd_cxp h ⬝ᵥ rd_psi h = rd_mg h * 4 ^ h.length := by
  rw [← rd_mg_sum h]
  simp only [rd_cxp, rd_psi, dotProduct, Fintype.sum_bool, pow_succ]
  ring

/-- The payoff of `ψ` bought at `sᵗ` in state `s`. -/
theorem rd_psi_payoff (h : List Bool) (s : Bool) :
    rd_arrowPayoff (s :: h) ⬝ᵥ rd_psi h = rd_mg (s :: h) * 4 ^ (s :: h).length := by
  cases s <;> simp [rd_arrowPayoff, rd_psi, dotProduct]

/-- The state prices of the economy. -/
theorem rd_cx_statePrice :
    rd_StatePrice rd_cxp rd_arrowPayoff fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g := by
  rw [rd_arrow_statePrice _ _ fun h => by rw [rd_cx_q]; positivity]
  intro h s
  simp only [rd_cx_q, List.length_cons, pow_succ, rd_cxp]
  ring

/-- `q⁰ ∈ L¹`. -/
theorem rd_cx_L1 : rd_L1 fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g := by
  have e : ∀ t, rd_dsum (fun g => |rd_cxpd g * (rd_uniformTree Bool).Pr g|) [] t =
      (1 / 2) ^ t := by
    intro t
    have : (fun g => |rd_cxpd g * (rd_uniformTree Bool).Pr g|) =
        fun g => (1 / 2 : ℝ) ^ g.length * (rd_uniformTree Bool).Pr g := by
      funext g
      rw [abs_of_pos (mul_pos (by unfold rd_cxpd; positivity) ((rd_uniformTree Bool).pos g))]
      rfl
    rw [this, rd_dsum_pow, rd_dsum_Pr, (rd_uniformTree Bool).root, mul_one]
  simp only [rd_L1, e]
  exact summable_geometric_two

/-- Linear expected utility is the state-price value of consumption. -/
theorem rd_cx_EU (c : List Bool → ℝ) :
    rd_EU (rd_uniformTree Bool) (1 / 2) id c =
      ∑' t, rd_dsum (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g * c g) [] t := by
  refine tsum_congr fun t => ?_
  rw [← rd_dsum_pow]
  exact rd_dsum_congr (fun g => by simp [rd_cxpd]; ring) _ _

/-- The agents' budgets bind and the date-0 transversality condition holds. -/
theorem rd_cx_budget (i : Bool) :
    rd_BudgetEq rd_cxp rd_arrowPayoff (fun _ => 1) 0 (fun _ => 1) (rd_cxθ i) ∧
      rd_TVC (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g) rd_cxp (rd_cxθ i) := by
  have hθ : ∀ g, rd_cxθ i g = (if i then (1 : ℝ) else -1) • rd_psi g := fun g => by
    cases i <;> simp [rd_cxθ]
  refine ⟨fun h => ?_, ?_⟩
  · cases h with
    | nil =>
      simp only [hθ, dotProduct_smul, rd_psi_cost, rd_fz, rd_prev, dotProduct_zero]
      simp [rd_mg]
    | cons s g =>
      simp only [hθ, dotProduct_smul, rd_psi_cost, rd_fz, rd_prev, rd_psi_payoff]
      ring
  · have e : (fun T => rd_dsum (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g *
        (rd_cxp g ⬝ᵥ rd_cxθ i g)) [] T) = fun _ => 0 := by
      funext T
      have : (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g * (rd_cxp g ⬝ᵥ rd_cxθ i g)) =
          fun g => (if i then (1 : ℝ) else -1) * rd_mg g := by
        funext g
        rw [hθ, dotProduct_smul, rd_psi_cost, rd_cx_q, smul_eq_mul]
        rw [show (1 / 4 : ℝ) ^ g.length * ((if i then 1 else -1) * (rd_mg g * 4 ^ g.length)) =
          (if i then 1 else -1) * rd_mg g * ((1 / 4) ^ g.length * 4 ^ g.length) by ring,
          ← mul_pow]
        norm_num
      rw [this, rd_dsum_const_mul, rd_dsum_mg]
      simp [rd_mg]
    rw [rd_TVC, e]
    exact tendsto_const_nhds

/-- The value of `ψ` is unbounded along the all-`true` branch. -/
theorem rd_psi_unbounded (M : ℝ) : ∃ n, M < rd_cxp (List.replicate (n + 1) true) ⬝ᵥ
    rd_psi (List.replicate (n + 1) true) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 4)
  refine ⟨n, ?_⟩
  rw [rd_psi_cost, rd_mg_true, one_mul, List.length_replicate]
  calc M < 4 ^ n := hn
    _ ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)

/-- **Theorem 13.5.1** (Miao, p. 435), counterexample to the "if" direction as printed. The
economy above is a competitive equilibrium with transversality condition, markets are complete,
utilities are strictly increasing and satisfy Assumption 13.5.1, but with the equilibrium
strategies it is not a Radner equilibrium with any bounded borrowing or debt limits. -/
theorem theorem_13_5_1_counterexample :
    rd_CETVC (rd_uniformTree Bool) (fun _ => rd_EU (rd_uniformTree Bool) (1 / 2) id)
        (fun _ _ => 1) (fun _ => 0) rd_arrowPayoff (fun _ _ => 1) rd_cxθ rd_cxpd rd_cxp ∧
      (∀ h, (rd_payoffMatrix (rd_arrowPayoff (S := Bool)) h).rank = Fintype.card Bool) ∧
      (∀ _i : Bool, rd_StrictIncr (rd_EU (rd_uniformTree Bool) (1 / 2) id)) ∧
      (∀ _i : Bool, rd_Assumption1351 (rd_EU (rd_uniformTree Bool) (1 / 2) id)
        fun _ => ∑ _k : Bool, (1 : ℝ)) ∧
      (¬ ∃ Bbar : Bool → List Bool → ℝ, (∀ i, rd_Bdd (Bbar i)) ∧
        rd_RadnerBC (fun _ => rd_EU (rd_uniformTree Bool) (1 / 2) id) (fun _ _ => 1)
          (fun _ => 0) rd_cxp rd_arrowPayoff Bbar (fun _ _ => 1) rd_cxθ) ∧
      ¬ ∃ Dbar : Bool → List Bool → ℝ, (∀ i, rd_Bdd (Dbar i)) ∧
        rd_RadnerDC (fun _ => rd_EU (rd_uniformTree Bool) (1 / 2) id) (fun _ _ => 1)
          (fun _ => 0) rd_cxp rd_arrowPayoff Dbar (fun _ _ => 1) rd_cxθ := by
  set q : List Bool → ℝ := fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g
  have hone : rd_LinfPos (fun _ : List Bool => (1 : ℝ)) := ⟨rd_bdd_one, fun _ => zero_le_one⟩
  have hU : ∀ c', rd_LinfPos c' → rd_ADBudget q (fun _ => 1) c' →
      rd_EU (rd_uniformTree Bool) (1 / 2) id c' ≤
        rd_EU (rd_uniformTree Bool) (1 / 2) id fun _ => 1 := by
    intro c' _ hb
    rw [rd_cx_EU, rd_cx_EU]
    exact hb
  have hseq : ∀ c' θ', rd_LinfPos c' → rd_Budget rd_cxp rd_arrowPayoff (fun _ => 1) 0 c' θ' →
      rd_TVC q rd_cxp θ' → rd_ADBudget q (fun _ => 1) c' := by
    intro c' θ' hc' hB hT
    have := eq_13_22 rd_cx_statePrice hB hT (rd_L1_mul rd_cx_L1 hc'.1)
      (rd_L1_mul rd_cx_L1 rd_bdd_one)
    simpa [rd_ADBudget] using this
  refine ⟨⟨fun _ => hone, rd_cx_L1, fun h => by unfold rd_cxpd; positivity,
    fun _ _ => by unfold rd_cxp; norm_num, fun _ => ⟨1 / 4, fun _ => by
      unfold rd_cxp; norm_num [abs_of_pos]⟩,
    fun i => ⟨⟨hone, fun h => ((rd_cx_budget i).1 h).le, (rd_cx_budget i).2⟩,
      fun c' θ' ⟨hc', hB, hT⟩ => hU c' hc' (hseq c' θ' hc' hB hT)⟩,
    fun i => ⟨⟨hone, by simp⟩, fun c' ⟨hc', hb⟩ => hU c' hc' (by simpa [rd_ADBudget] using hb)⟩,
    rd_cx_statePrice, fun h => rfl, fun h => ?_⟩,
    fun h => rd_arrow_rank h, fun _ => rd_eq_13_1 _ (by norm_num) (by norm_num) strictMonoOn_id,
    fun _ => assumption_13_5_1 _ (by norm_num) (by norm_num) strictMonoOn_id
      continuous_id.continuousOn (m := 2) (Y := 2) (by norm_num) (fun _ => by simp)
      (fun _ => by simp), ?_, ?_⟩
  · funext s
    simp [rd_cxθ]
  · rintro ⟨Bbar, hBb, hsol, -, -⟩
    obtain ⟨M, hM⟩ := hBb false
    obtain ⟨n, hn⟩ := rd_psi_unbounded M
    have := (hsol false).1.2.2 (List.replicate (n + 1) true)
    simp only [rd_cxθ, Bool.false_eq_true, ↓reduceIte, Pi.neg_apply, dotProduct_neg] at this
    linarith [(le_abs_self _).trans (hM (List.replicate (n + 1) true))]
  · rintro ⟨Dbar, hDb, hsol, -, -⟩
    obtain ⟨M, hM⟩ := hDb false
    obtain ⟨n, hn⟩ := rd_psi_unbounded M
    have := (hsol false).1.2.2 (List.replicate n true) true
    simp only [rd_cxθ, Bool.false_eq_true, ↓reduceIte, Pi.neg_apply, dotProduct_neg,
      rd_psi_payoff] at this
    rw [rd_psi_cost] at hn
    have hM' := (le_abs_self _).trans (hM (List.replicate (n + 1) true))
    rw [← List.replicate_succ] at this
    linarith

/-- (13.23) (Miao, p. 433), counterexample: agent `true`'s plan satisfies the budget (13.11) and
the transversality condition (13.21), but the conditional present-value budget (13.23) fails at
the node `(false)`, where the strategy is worth `−4` (`q⁰ = 1/4`). -/
theorem eq_13_23_counterexample :
    rd_Budget rd_cxp rd_arrowPayoff (fun _ => 1) 0 (fun _ => 1) rd_psi ∧
      rd_TVC (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g) rd_cxp rd_psi ∧
      ¬ (∑' j, rd_dsum (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g * 1) [false] j ≤
        rd_cxpd [false] * (rd_uniformTree Bool).Pr [false] *
          (rd_fz rd_cxp rd_arrowPayoff [false] ⬝ᵥ rd_prev rd_psi 0 [false]) +
        ∑' j, rd_dsum (fun g => rd_cxpd g * (rd_uniformTree Bool).Pr g * 1) [false] j) := by
  have hb := rd_cx_budget true
  simp only [rd_cxθ, ↓reduceIte] at hb
  refine ⟨fun h => (hb.1 h).le, hb.2, fun hle => ?_⟩
  have : rd_cxpd [false] * (rd_uniformTree Bool).Pr [false] *
      (rd_fz rd_cxp rd_arrowPayoff [false] ⬝ᵥ rd_prev rd_psi 0 [false]) = -1 := by
    rw [rd_cx_q]
    simp only [rd_fz, rd_prev]
    rw [rd_psi_payoff]
    simp [rd_mg]
  linarith

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The event tree of §§13.6–13.8

Miao, §13.1 (the event tree) as used in §13.6 (asset price bubbles, pp. 439–444), §13.7
(recursive formulation, p. 444) and Exercise 13.7 (p. 454).

A history `s^t = (s_1, …, s_t)` is a list `h : List S` of shocks over a finite shock set `S`,
the most recent shock first: the successors of `h` are the lists `s :: h`, the root `[]` is the
date-0 node and a date-`t` node is a list of length `t`. Probabilities `pr h = Pr(s^t)` are
strictly positive, `pr [] = 1` and `∑ₛ pr (s :: h) = pr h` (`BPTree`).

* `bp_nodeSum t g`: the sum of `g` over all date-`t` nodes (defined by recursion on `t`).
* `bp_condExp T j x h`: the conditional expectation `E_t[x_{t+j}]` at the date-`t` node `h`,
  `E_t[x_{t+j}] = ∑ₛ Pr(s | s^t) E_{t+1}[x_{t+j}]`.
* `bp_pv T δ t x = E[δ_t x_t]`: the date-0 value of a date-`t` payoff under the deflator `δ`.
* The tower property (`bp_condExp_add`), linearity and positivity of `bp_condExp`, and the law
  of iterated expectations `pr · E_t[x_{t+j}]` summed over date-`t` nodes `= E[x_{t+j}]`
  (`bp_nodeSum_condExp`).
* §13.7, p. 444: a Markov chain `P` with initial state `s₀` gives the probabilities
  `Pr(s^t) = Pr(s_t | s_{t−1}) ⋯ Pr(s_1 | s_0)` (`bp_markovPr`, `bp_markovTree`), and the
  conditional probability of `s_{t+1}` given `s^t` depends only on `s_t` (`eq_13_7_markov`).
-/

namespace Miao.CompleteMarkets

/-- The event tree (Miao, §13.1, p. 415): histories are lists over the finite shock set `S`
(most recent shock first), with strictly positive, consistent probabilities. -/
structure BPTree (S : Type*) [Fintype S] where
  /-- `pr h = Pr(s^t)`. -/
  pr : List S → ℝ
  pr_pos : ∀ h, 0 < pr h
  pr_nil : pr [] = 1
  pr_cons : ∀ h, ∑ s, pr (s :: h) = pr h

/-- The sum of `g` over the date-`t` nodes of the tree. -/
def bp_nodeSum {S : Type*} [Fintype S] : ℕ → (List S → ℝ) → ℝ
  | 0, g => g []
  | t + 1, g => bp_nodeSum t (fun h => ∑ s, g (s :: h))

/-- The conditional expectation `E_t[x_{t+j}]` at the node `h` (Miao, §13.1). -/
noncomputable def bp_condExp {S : Type*} [Fintype S] (T : BPTree S) : ℕ → (List S → ℝ) → List S → ℝ
  | 0, x, h => x h
  | j + 1, x, h => ∑ s, T.pr (s :: h) / T.pr h * bp_condExp T j x (s :: h)

/-- The date-0 value `E[δ_t x_t]` of the date-`t` payoff `x` under the deflator `δ`. -/
def bp_pv {S : Type*} [Fintype S] (T : BPTree S) (δ : List S → ℝ) (t : ℕ)
    (x : List S → ℝ) : ℝ :=
  bp_nodeSum t (fun h => T.pr h * δ h * x h)

theorem bp_nodeSum_zero {S : Type*} [Fintype S] (g : List S → ℝ) :
    bp_nodeSum 0 g = g [] := rfl

theorem bp_nodeSum_succ {S : Type*} [Fintype S] (t : ℕ) (g : List S → ℝ) :
    bp_nodeSum (t + 1) g = bp_nodeSum t (fun h => ∑ s, g (s :: h)) := rfl

/-- Only the values at date-`t` nodes matter. -/
theorem bp_nodeSum_congr {S : Type*} [Fintype S] (t : ℕ) (f g : List S → ℝ)
    (hfg : ∀ h : List S, h.length = t → f h = g h) : bp_nodeSum t f = bp_nodeSum t g := by
  induction t generalizing f g with
  | zero =>
    exact hfg [] rfl
  | succ t ih =>
    rw [bp_nodeSum_succ, bp_nodeSum_succ]
    refine ih _ _ (fun h hh => Finset.sum_congr rfl (fun s _ => hfg _ ?_))
    simp [hh]

theorem bp_nodeSum_add {S : Type*} [Fintype S] (t : ℕ) (f g : List S → ℝ) :
    bp_nodeSum t (fun h => f h + g h) = bp_nodeSum t f + bp_nodeSum t g := by
  induction t generalizing f g with
  | zero => rfl
  | succ t ih =>
    rw [bp_nodeSum_succ, bp_nodeSum_succ, bp_nodeSum_succ, ← ih]
    simp only [Finset.sum_add_distrib]

theorem bp_nodeSum_smul {S : Type*} [Fintype S] (t : ℕ) (a : ℝ) (f : List S → ℝ) :
    bp_nodeSum t (fun h => a * f h) = a * bp_nodeSum t f := by
  induction t generalizing f with
  | zero => rfl
  | succ t ih =>
    rw [bp_nodeSum_succ, bp_nodeSum_succ, ← ih]
    simp only [Finset.mul_sum]

theorem bp_nodeSum_neg {S : Type*} [Fintype S] (t : ℕ) (f : List S → ℝ) :
    bp_nodeSum t (fun h => -f h) = -bp_nodeSum t f := by
  have := bp_nodeSum_smul t (-1) f
  simpa using this

theorem bp_nodeSum_sub {S : Type*} [Fintype S] (t : ℕ) (f g : List S → ℝ) :
    bp_nodeSum t (fun h => f h - g h) = bp_nodeSum t f - bp_nodeSum t g := by
  have h1 := bp_nodeSum_add t f (fun h => -g h)
  rw [bp_nodeSum_neg] at h1
  simpa [sub_eq_add_neg] using h1

theorem bp_nodeSum_finsetSum {S : Type*} [Fintype S] {ι : Type*} (A : Finset ι) (t : ℕ)
    (f : ι → List S → ℝ) :
    bp_nodeSum t (fun h => ∑ i ∈ A, f i h) = ∑ i ∈ A, bp_nodeSum t (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simpa using bp_nodeSum_smul t 0 (fun _ => (0 : ℝ))
  | insert a A ha ih =>
    simp only [Finset.sum_insert ha]
    rw [bp_nodeSum_add, ih]

theorem bp_nodeSum_const {S : Type*} [Fintype S] (T : BPTree S) (t : ℕ) (a : ℝ) :
    bp_nodeSum t (fun h => T.pr h * a) = a := by
  induction t generalizing a with
  | zero => simp [bp_nodeSum_zero, T.pr_nil]
  | succ t ih =>
    rw [bp_nodeSum_succ]
    simp only [← Finset.sum_mul, T.pr_cons]
    exact ih a

theorem bp_nodeSum_mono {S : Type*} [Fintype S] (t : ℕ) (f g : List S → ℝ)
    (hfg : ∀ h, f h ≤ g h) : bp_nodeSum t f ≤ bp_nodeSum t g := by
  induction t generalizing f g with
  | zero => exact hfg []
  | succ t ih =>
    rw [bp_nodeSum_succ, bp_nodeSum_succ]
    exact ih _ _ (fun h => Finset.sum_le_sum (fun s _ => hfg _))

theorem bp_nodeSum_nonneg {S : Type*} [Fintype S] (t : ℕ) (f : List S → ℝ)
    (hf : ∀ h, 0 ≤ f h) : 0 ≤ bp_nodeSum t f := by
  have := bp_nodeSum_mono t (fun _ => (0 : ℝ)) f hf
  have h0 : bp_nodeSum t (fun _ : List S => (0 : ℝ)) = 0 := by
    simpa using bp_nodeSum_smul t 0 (fun _ : List S => (0 : ℝ))
  linarith

/-- A sum of nonnegative terms over the date-`t` nodes vanishes only if every term does. -/
theorem bp_nodeSum_eq_zero_iff {S : Type*} [Fintype S] (t : ℕ) (f : List S → ℝ)
    (hf : ∀ h, 0 ≤ f h) (h0 : bp_nodeSum t f = 0) : ∀ h : List S, h.length = t → f h = 0 := by
  induction t generalizing f with
  | zero =>
    intro h hh
    rw [List.length_eq_zero_iff] at hh
    subst hh
    exact h0
  | succ t ih =>
    intro h hh
    obtain ⟨s, h', rfl⟩ : ∃ s h', h = s :: h' := by
      cases h with
      | nil => simp at hh
      | cons s h' => exact ⟨s, h', rfl⟩
    have hh' : h'.length = t := by simpa using hh
    have key := ih (fun g => ∑ s, f (s :: g))
      (fun g => Finset.sum_nonneg (fun s _ => hf _)) h0 h' hh'
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hf _)).1 key s (Finset.mem_univ s)

/-- A single date-`t` node contributes its value. -/
theorem bp_nodeSum_single {S : Type*} [Fintype S] [DecidableEq S] (t : ℕ) (h₀ : List S)
    (hh₀ : h₀.length = t) (v : ℝ) :
    bp_nodeSum t (fun h => if h = h₀ then v else 0) = v := by
  induction t generalizing h₀ v with
  | zero =>
    rw [List.length_eq_zero_iff] at hh₀
    subst hh₀
    simp [bp_nodeSum_zero]
  | succ t ih =>
    obtain ⟨s₀, g₀, rfl⟩ : ∃ s g, h₀ = s :: g := by
      cases h₀ with
      | nil => simp at hh₀
      | cons s g => exact ⟨s, g, rfl⟩
    have hg : g₀.length = t := by simpa using hh₀
    rw [bp_nodeSum_succ]
    have : (fun h : List S => ∑ s, (if s :: h = s₀ :: g₀ then v else 0)) =
        fun h => if h = g₀ then v else 0 := by
      funext h
      by_cases hh : h = g₀
      · subst hh
        simp
      · simp [hh]
    rw [this]
    exact ih g₀ hg v

theorem bp_condExp_zero {S : Type*} [Fintype S] (T : BPTree S) (x : List S → ℝ)
    (h : List S) : bp_condExp T 0 x h = x h := rfl

theorem bp_condExp_succ {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (x : List S → ℝ)
    (h : List S) :
    bp_condExp T (j + 1) x h = ∑ s, T.pr (s :: h) / T.pr h * bp_condExp T j x (s :: h) := rfl

/-- The tower property: `E_t[E_{t+j}[x_{t+j+k}]] = E_t[x_{t+j+k}]`. -/
theorem bp_condExp_add {S : Type*} [Fintype S] (T : BPTree S) (j k : ℕ) (x : List S → ℝ)
    (h : List S) : bp_condExp T (j + k) x h = bp_condExp T j (bp_condExp T k x) h := by
  induction j generalizing h with
  | zero => simp [bp_condExp_zero]
  | succ j ih =>
    rw [show j + 1 + k = (j + k) + 1 by omega, bp_condExp_succ, bp_condExp_succ]
    exact Finset.sum_congr rfl (fun s _ => by rw [ih])

theorem bp_condExp_congr {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (x y : List S → ℝ)
    (hxy : ∀ g, x g = y g) (h : List S) : bp_condExp T j x h = bp_condExp T j y h := by
  rw [show x = y from funext hxy]

theorem bp_condExp_add_fun {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ)
    (x y : List S → ℝ) (h : List S) :
    bp_condExp T j (fun g => x g + y g) h = bp_condExp T j x h + bp_condExp T j y h := by
  induction j generalizing h with
  | zero => rfl
  | succ j ih =>
    simp only [bp_condExp_succ, ih, mul_add, Finset.sum_add_distrib]

theorem bp_condExp_smul {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (a : ℝ)
    (x : List S → ℝ) (h : List S) :
    bp_condExp T j (fun g => a * x g) h = a * bp_condExp T j x h := by
  induction j generalizing h with
  | zero => rfl
  | succ j ih =>
    simp only [bp_condExp_succ, ih, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)

theorem bp_condExp_sub_fun {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ)
    (x y : List S → ℝ) (h : List S) :
    bp_condExp T j (fun g => x g - y g) h = bp_condExp T j x h - bp_condExp T j y h := by
  have h1 := bp_condExp_add_fun T j x (fun g => (-1) * y g) h
  rw [bp_condExp_smul] at h1
  simpa [sub_eq_add_neg] using h1

theorem bp_condExp_const {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (a : ℝ)
    (h : List S) : bp_condExp T j (fun _ => a) h = a := by
  induction j generalizing h with
  | zero => rfl
  | succ j ih =>
    simp only [bp_condExp_succ, ih]
    rw [← Finset.sum_mul, ← Finset.sum_div, T.pr_cons, div_self (T.pr_pos h).ne', one_mul]

theorem bp_condExp_mono {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (x y : List S → ℝ)
    (hxy : ∀ g, x g ≤ y g) (h : List S) : bp_condExp T j x h ≤ bp_condExp T j y h := by
  induction j generalizing h with
  | zero => exact hxy h
  | succ j ih =>
    simp only [bp_condExp_succ]
    refine Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (ih _) ?_)
    exact div_nonneg (T.pr_pos _).le (T.pr_pos _).le

theorem bp_condExp_nonneg {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (x : List S → ℝ)
    (hx : ∀ g, 0 ≤ x g) (h : List S) : 0 ≤ bp_condExp T j x h := by
  have := bp_condExp_mono T j (fun _ => 0) x hx h
  rwa [bp_condExp_const] at this

theorem bp_condExp_finsetSum {S : Type*} [Fintype S] (T : BPTree S) {ι : Type*}
    (A : Finset ι) (j : ℕ) (x : ι → List S → ℝ) (h : List S) :
    bp_condExp T j (fun g => ∑ i ∈ A, x i g) h = ∑ i ∈ A, bp_condExp T j (x i) h := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bp_condExp_const T j 0 h
  | insert a A ha ih =>
    simp only [Finset.sum_insert ha]
    rw [bp_condExp_add_fun, ih]

/-- The law of iterated expectations on the tree: summing `Pr(s^t) E_t[x_{t+j}]` over the
date-`t` nodes gives `E[x_{t+j}]`. -/
theorem bp_nodeSum_condExp {S : Type*} [Fintype S] (T : BPTree S) (t j : ℕ)
    (x : List S → ℝ) :
    bp_nodeSum t (fun h => T.pr h * bp_condExp T j x h) =
      bp_nodeSum (t + j) (fun h => T.pr h * x h) := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    have hstep : (fun h => T.pr h * bp_condExp T (j + 1) x h) =
        fun h => ∑ s, T.pr (s :: h) * bp_condExp T j x (s :: h) := by
      funext h
      rw [bp_condExp_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      field_simp [(T.pr_pos h).ne']
    rw [hstep, ← bp_nodeSum_succ t (fun g => T.pr g * bp_condExp T j x g), ih (t + 1)]
    rw [show t + 1 + j = t + (j + 1) by omega]

/-- At the root, `E_0[x_j] = E[x_j]`. -/
theorem bp_condExp_root {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (x : List S → ℝ) :
    bp_condExp T j x [] = bp_nodeSum j (fun h => T.pr h * x h) := by
  have := bp_nodeSum_condExp T 0 j x
  rw [bp_nodeSum_zero, T.pr_nil, one_mul, zero_add] at this
  exact this

theorem bp_pv_add {S : Type*} [Fintype S] (T : BPTree S) (δ : List S → ℝ) (t : ℕ)
    (x y : List S → ℝ) :
    bp_pv T δ t (fun h => x h + y h) = bp_pv T δ t x + bp_pv T δ t y := by
  unfold bp_pv
  rw [← bp_nodeSum_add]
  congr 1
  funext h
  ring

theorem bp_pv_mono {S : Type*} [Fintype S] (T : BPTree S) (δ : List S → ℝ)
    (hδ : ∀ h, 0 ≤ δ h) (t : ℕ) (x y : List S → ℝ) (hxy : ∀ h, x h ≤ y h) :
    bp_pv T δ t x ≤ bp_pv T δ t y := by
  unfold bp_pv
  refine bp_nodeSum_mono t _ _ (fun h => ?_)
  exact mul_le_mul_of_nonneg_left (hxy h) (mul_nonneg (T.pr_pos h).le (hδ h))

theorem bp_pv_nonneg {S : Type*} [Fintype S] (T : BPTree S) (δ : List S → ℝ)
    (hδ : ∀ h, 0 ≤ δ h) (t : ℕ) (x : List S → ℝ) (hx : ∀ h, 0 ≤ x h) :
    0 ≤ bp_pv T δ t x :=
  bp_nodeSum_nonneg t _ (fun h => mul_nonneg (mul_nonneg (T.pr_pos h).le (hδ h)) (hx h))

theorem bp_pv_finsetSum {S : Type*} [Fintype S] (T : BPTree S) (δ : List S → ℝ)
    {ι : Type*} (A : Finset ι) (t : ℕ) (x : ι → List S → ℝ) :
    bp_pv T δ t (fun h => ∑ i ∈ A, x i h) = ∑ i ∈ A, bp_pv T δ t (x i) := by
  unfold bp_pv
  rw [← bp_nodeSum_finsetSum]
  congr 1
  funext h
  rw [Finset.mul_sum]

/-- The probabilities generated by a Markov chain `P` with initial state `s₀` (Miao, §13.7,
p. 444): `Pr(s_{t+1}, s^t) = Pr(s_{t+1} | s_t) Pr(s^t)`. -/
def bp_markovPr {S : Type*} (P : S → S → ℝ) (s₀ : S) : List S → ℝ
  | [] => 1
  | s :: h => P (h.headD s₀) s * bp_markovPr P s₀ h

/-- A strictly positive stochastic matrix generates an event tree. -/
def bp_markovTree {S : Type*} [Fintype S] (P : S → S → ℝ) (s₀ : S)
    (hP : ∀ a b, 0 < P a b) (hrow : ∀ a, ∑ b, P a b = 1) : BPTree S where
  pr := bp_markovPr P s₀
  pr_pos := by
    intro h
    induction h with
    | nil => simp [bp_markovPr]
    | cons s h ih => exact mul_pos (hP _ _) ih
  pr_nil := rfl
  pr_cons := by
    intro h
    simp only [bp_markovPr, ← Finset.sum_mul, hrow, one_mul]

/-- Miao, §13.7, p. 444: `Pr(s^t) = Pr(s_t | s_{t−1}) Pr(s_{t−1} | s_{t−2}) ⋯ Pr(s_1 | s_0)`,
written recursively, and the conditional probability `Pr(s_{t+1} | s^t)` of the next shock
equals the transition probability `Pr(s_{t+1} | s_t)`. -/
theorem eq_13_7_markov {S : Type*} [Fintype S] (P : S → S → ℝ) (s₀ : S)
    (hP : ∀ a b, 0 < P a b) (hrow : ∀ a, ∑ b, P a b = 1) (s : S) (h : List S) :
    (bp_markovTree P s₀ hP hrow).pr (s :: h) =
        P (h.headD s₀) s * (bp_markovTree P s₀ hP hrow).pr h ∧
      (bp_markovTree P s₀ hP hrow).pr (s :: h) / (bp_markovTree P s₀ hP hrow).pr h =
        P (h.headD s₀) s := by
  refine ⟨rfl, ?_⟩
  have hpos := (bp_markovTree P s₀ hP hrow).pr_pos h
  rw [show (bp_markovTree P s₀ hP hrow).pr (s :: h) =
    P (h.headD s₀) s * (bp_markovTree P s₀ hP hrow).pr h from rfl]
  field_simp

/-- The deterministic tree: one shock, probability one at every node. -/
def bp_detTree : BPTree Unit where
  pr := fun _ => 1
  pr_pos := fun _ => one_pos
  pr_nil := rfl
  pr_cons := fun _ => by simp

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fundamental values and bubbles

Miao, §13.6, pp. 439–440. A stock with ex-dividend price `p` and dividends `d` on the event tree
of `BPTree`, priced by a state price deflator `δ > 0` (the book's `π`):
`p_t = (1/π_t) E_t[π_{t+1}(p_{t+1} + d_{t+1})]` (`bp_Prices`).

* `eq_13_6_forward` (p. 439): repeated substitution,
  `p_t = (1/π_t) ∑_{j=1}^T E_t[π_{t+j} d_{t+j}] + (1/π_t) E_t[π_{t+T} p_{t+T}]`.
* `bp_fundamental` (p. 440): the fundamental value `v_t(d) = (1/π_t) ∑_{j≥1} E_t[π_{t+j} d_{t+j}]`;
  `bp_bubble`: `b_t = p_t − v_t(d)`. For `p, d ≥ 0` the series converges
  (`bp_summable_dividends`), since its partial sums are at most `p_t`.
* `eq_13_6_bubble_limit`: `b_t = lim_T (1/π_t) E_t[π_{t+T} p_{t+T}]`.
* `eq_13_6_bubble_bounds`: `0 ≤ b_t ≤ p_t`.
* `bp_no_bubble_finite_maturity` (p. 439): an asset with finite maturity has no bubble.
* `eq_13_25`: the discounted martingale property `b_t = (1/π_t) E_t[π_{t+1} b_{t+1}]`, with its
  iterate `eq_13_25_iterate` and the consequence that a bubble vanishing at the root vanishes at
  every node (`bp_bubble_eq_zero_of_root`). The fundamental value itself solves the pricing
  equation (`bp_fundamental_prices`).

**Correction.** The book states `0 < b_t ≤ p_t`. The strict inequality is false: an asset priced
at its fundamental value has `b_t = 0` (`eq_13_6_bubble_pos_counterexample`). What is true is
`0 ≤ b_t ≤ p_t` (`eq_13_6_bubble_bounds`).
-/

open Filter Topology

namespace Miao.CompleteMarkets

/-- The no-arbitrage pricing equation of the stock (Miao, p. 439):
`π_t p_t = E_t[π_{t+1}(p_{t+1} + d_{t+1})]` at every node. -/
def bp_Prices {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ) : Prop :=
  ∀ h, δ h * p h = bp_condExp T 1 (fun g => δ g * (p g + d g)) h

/-- The fundamental value `v_t(d) = (1/π_t) ∑_{j ≥ 1} E_t[π_{t+j} d_{t+j}]` (Miao, p. 440). -/
noncomputable def bp_fundamental {S : Type*} [Fintype S] (T : BPTree S) (δ d : List S → ℝ)
    (h : List S) : ℝ :=
  1 / δ h * ∑' j, bp_condExp T (j + 1) (fun g => δ g * d g) h

/-- The bubble `b_t = p_t − v_t(d)` (Miao, p. 440). -/
noncomputable def bp_bubble {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (h : List S) : ℝ :=
  p h - bp_fundamental T δ d h

/-- The forward-iterated pricing equation, multiplied through by `π_t`. -/
theorem bp_forward_mul {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hP : bp_Prices T δ p d) (n : ℕ) (h : List S) :
    δ h * p h = ∑ j ∈ Finset.range n, bp_condExp T (j + 1) (fun g => δ g * d g) h +
      bp_condExp T n (fun g => δ g * p g) h := by
  induction n generalizing h with
  | zero => simp [bp_condExp_zero]
  | succ n ih =>
    rw [ih, Finset.sum_range_succ]
    have h1 : bp_condExp T n (fun g => δ g * p g) h =
        bp_condExp T n (bp_condExp T 1 (fun g => δ g * (p g + d g))) h :=
      bp_condExp_congr T n _ _ (fun g => hP g) h
    rw [h1, ← bp_condExp_add]
    have h2 : bp_condExp T (n + 1) (fun g => δ g * (p g + d g)) h =
        bp_condExp T (n + 1) (fun g => δ g * d g) h +
          bp_condExp T (n + 1) (fun g => δ g * p g) h := by
      rw [← bp_condExp_add_fun]
      exact bp_condExp_congr T _ _ _ (fun g => by ring) h
    rw [h2]
    ring

/-- Miao, p. 439: solving the pricing equation forward by repeated substitution,
`p_t = (1/π_t) ∑_{j=1}^T E_t[π_{t+j} d_{t+j}] + (1/π_t) E_t[π_{t+T} p_{t+T}]`. -/
theorem eq_13_6_forward {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hP : bp_Prices T δ p d) (n : ℕ) (h : List S) :
    p h = 1 / δ h * ∑ j ∈ Finset.range n, bp_condExp T (j + 1) (fun g => δ g * d g) h +
      1 / δ h * bp_condExp T n (fun g => δ g * p g) h := by
  have := bp_forward_mul T δ p d hP n h
  have hne := (hδ h).ne'
  rw [← mul_add, ← this]
  field_simp

/-- For a nonnegative price and dividend, the series defining the fundamental value converges:
its partial sums are bounded by `π_t p_t`. -/
theorem bp_summable_dividends {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (h : List S) : Summable (fun j => bp_condExp T (j + 1) (fun g => δ g * d g) h) := by
  refine summable_of_sum_range_le (c := δ h * p h)
    (fun j => bp_condExp_nonneg T _ _ (fun g => mul_nonneg (hδ g).le (hd g)) h) (fun n => ?_)
  rw [bp_forward_mul T δ p d hP n h]
  have := bp_condExp_nonneg T n (fun g => δ g * p g) (fun g => mul_nonneg (hδ g).le (hp g)) h
  linarith

/-- `π_t v_t(d)` is the sum of the discounted expected dividends. -/
theorem bp_mul_fundamental {S : Type*} [Fintype S] (T : BPTree S) (δ d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (h : List S) :
    δ h * bp_fundamental T δ d h = ∑' j, bp_condExp T (j + 1) (fun g => δ g * d g) h := by
  unfold bp_fundamental
  have := (hδ h).ne'
  field_simp

/-- Miao, p. 440: the bubble is the limit of the discounted expected resale value,
`b_t = lim_{T→∞} (1/π_t) E_t[π_{t+T} p_{t+T}]`. -/
theorem eq_13_6_bubble_limit {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (h : List S) :
    Tendsto (fun n => 1 / δ h * bp_condExp T n (fun g => δ g * p g) h) atTop
      (𝓝 (bp_bubble T δ p d h)) := by
  have hs := (bp_summable_dividends T δ p d hδ hp hd hP h).hasSum.tendsto_sum_nat
  have hlim := (hs.const_mul (1 / δ h)).const_sub (p h)
  have heq : (fun n => 1 / δ h * bp_condExp T n (fun g => δ g * p g) h) =
      fun n => p h - 1 / δ h *
        ∑ j ∈ Finset.range n, bp_condExp T (j + 1) (fun g => δ g * d g) h := by
    funext n
    rw [eq_13_6_forward T δ p d hδ hP n h]
    ring
  rw [heq]
  exact hlim

/-- Miao, p. 440 (corrected): `0 ≤ b_t ≤ p_t`. The book's `0 < b_t` is false
(`eq_13_6_bubble_pos_counterexample`). -/
theorem eq_13_6_bubble_bounds {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (h : List S) : 0 ≤ bp_bubble T δ p d h ∧ bp_bubble T δ p d h ≤ p h := by
  constructor
  · refine ge_of_tendsto' (eq_13_6_bubble_limit T δ p d hδ hp hd hP h) (fun n => ?_)
    exact mul_nonneg (one_div_nonneg.2 (hδ h).le)
      (bp_condExp_nonneg T n _ (fun g => mul_nonneg (hδ g).le (hp g)) h)
  · unfold bp_bubble
    have : 0 ≤ bp_fundamental T δ d h := by
      unfold bp_fundamental
      exact mul_nonneg (one_div_nonneg.2 (hδ h).le) (tsum_nonneg (fun j =>
        bp_condExp_nonneg T _ _ (fun g => mul_nonneg (hδ g).le (hd g)) h))
    linarith

/-- Counterexample to `0 < b_t` (Miao, p. 440): on the deterministic tree with `π = 1` the asset
with zero dividends and zero price satisfies the pricing equation and has no bubble. -/
theorem eq_13_6_bubble_pos_counterexample :
    bp_Prices bp_detTree (fun _ => 1) (fun _ => 0) (fun _ => 0) ∧
      ¬ 0 < bp_bubble bp_detTree (fun _ => 1) (fun _ => 0) (fun _ => 0) [] := by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [add_zero, mul_zero]
    exact (bp_condExp_const bp_detTree 1 0 h).symm
  · have : bp_bubble bp_detTree (fun _ => (1 : ℝ)) (fun _ => 0) (fun _ => 0) [] = 0 := by
      unfold bp_bubble bp_fundamental
      simp only [mul_zero]
      simp [bp_condExp_const]
    rw [this]
    exact lt_irrefl 0

/-- The fundamental value solves the pricing equation:
`π_t v_t = E_t[π_{t+1}(v_{t+1} + d_{t+1})]`. -/
theorem bp_fundamental_prices {S : Type*} [Fintype S] (T : BPTree S) (δ d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h)
    (hsum : ∀ h, Summable (fun j => bp_condExp T (j + 1) (fun g => δ g * d g) h)) :
    bp_Prices T δ (bp_fundamental T δ d) d := by
  intro h
  set a : ℕ → List S → ℝ := fun j g => bp_condExp T (j + 1) (fun g => δ g * d g) g with ha
  rw [bp_mul_fundamental T δ d hδ h]
  have hrhs : bp_condExp T 1 (fun g => δ g * (bp_fundamental T δ d g + d g)) h =
      ∑ s, T.pr (s :: h) / T.pr h * (δ (s :: h) * d (s :: h)) +
        ∑ s, T.pr (s :: h) / T.pr h * ∑' j, a j (s :: h) := by
    rw [bp_condExp_succ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [bp_condExp_zero, mul_add, bp_mul_fundamental T δ d hδ (s :: h)]
    ring
  rw [hrhs]
  have hswap : ∑ s, T.pr (s :: h) / T.pr h * ∑' j, a j (s :: h) =
      ∑' j, a (j + 1) h := by
    have h1 : ∀ s, T.pr (s :: h) / T.pr h * ∑' j, a j (s :: h) =
        ∑' j, T.pr (s :: h) / T.pr h * a j (s :: h) :=
      fun s => ((hsum (s :: h)).tsum_mul_left _).symm
    simp only [h1]
    rw [← Summable.tsum_finsetSum (fun s _ => (hsum (s :: h)).mul_left _)]
    rfl
  rw [hswap, (hsum h).tsum_eq_zero_add]
  congr 1

/-- Miao, (13.25), p. 440: the bubble has the discounted martingale property
`b_t = (1/π_t) E_t[π_{t+1} b_{t+1}]`, stated multiplied through by `π_t`. -/
theorem eq_13_25 {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (h : List S) :
    δ h * bp_bubble T δ p d h = bp_condExp T 1 (fun g => δ g * bp_bubble T δ p d g) h := by
  have hF := bp_fundamental_prices T δ d hδ (bp_summable_dividends T δ p d hδ hp hd hP) h
  have hb : (fun g => δ g * bp_bubble T δ p d g) =
      fun g => δ g * (p g + d g) - δ g * (bp_fundamental T δ d g + d g) := by
    funext g
    unfold bp_bubble
    ring
  rw [hb, bp_condExp_sub_fun, ← hP h, ← hF]
  unfold bp_bubble
  ring

/-- Iterating (13.25): `π_t b_t = E_t[π_{t+k} b_{t+k}]` for every `k`. -/
theorem eq_13_25_iterate {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (k : ℕ) (h : List S) :
    δ h * bp_bubble T δ p d h = bp_condExp T k (fun g => δ g * bp_bubble T δ p d g) h := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    rw [show k + 1 = 1 + k by omega, bp_condExp_add, eq_13_25 T δ p d hδ hp hd hP h]
    exact bp_condExp_congr T 1 _ _ (fun g => ih g) h

/-- A bubble that vanishes at the root vanishes at every node (`b ≥ 0`, (13.25)). -/
theorem bp_bubble_eq_zero_of_root {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (h0 : bp_bubble T δ p d [] = 0) (h : List S) : bp_bubble T δ p d h = 0 := by
  have hit := eq_13_25_iterate T δ p d hδ hp hd hP h.length []
  rw [h0, mul_zero, bp_condExp_root] at hit
  have hnn : ∀ g, 0 ≤ T.pr g * (δ g * bp_bubble T δ p d g) := fun g =>
    mul_nonneg (T.pr_pos g).le
      (mul_nonneg (hδ g).le (eq_13_6_bubble_bounds T δ p d hδ hp hd hP g).1)
  have := bp_nodeSum_eq_zero_iff h.length _ hnn hit.symm h rfl
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (T.pr_pos h).ne'
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (hδ h).ne'
    · exact h2

/-- `E_t[x_{t+n}]` at `h` only depends on `x` at the nodes of length `|h| + n`. -/
theorem bp_condExp_congr_length {S : Type*} [Fintype S] (T : BPTree S) (n : ℕ)
    (x y : List S → ℝ) (h : List S)
    (hxy : ∀ g : List S, g.length = h.length + n → x g = y g) :
    bp_condExp T n x h = bp_condExp T n y h := by
  induction n generalizing h with
  | zero => exact hxy h (by simp)
  | succ n ih =>
    simp only [bp_condExp_succ]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [ih (s :: h) (fun g hg => hxy g (by simp at hg; omega))]

/-- Miao, p. 439: "by backward induction, there is no bubble on assets with finite maturity".
If the asset has no value from date `N` on (`p_t = 0` for `t ≥ N`), its bubble is zero at every
node. -/
theorem bp_no_bubble_finite_maturity {S : Type*} [Fintype S] (T : BPTree S)
    (δ p d : List S → ℝ) (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h)
    (hP : bp_Prices T δ p d) (N : ℕ) (hN : ∀ g : List S, N ≤ g.length → p g = 0)
    (h : List S) : bp_bubble T δ p d h = 0 := by
  have hlim := eq_13_6_bubble_limit T δ p d hδ hp hd hP h
  have hev : ∀ n, N ≤ n → 1 / δ h * bp_condExp T n (fun g => δ g * p g) h = 0 := by
    intro n hn
    rw [bp_condExp_congr_length T n _ (fun _ => 0) h (fun g hg => by
      rw [hN g (by omega), mul_zero]), bp_condExp_const, mul_zero]
  have h0 : Tendsto (fun n => 1 / δ h * bp_condExp T n (fun g => δ g * p g) h) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (hev n hn).symm)
  exact tendsto_nhds_unique hlim h0

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# No bubbles on assets in positive supply (Theorem 13.6.1)

Miao, §13.6, pp. 440–441, Theorem 13.6.1 (Santos and Woodford 1997) and its proof, equations
(13.20), (13.26) and (13.27), on the event tree of `BPTree` with finitely many agents `ι` and
stocks `J`.

* `BPRadnerEqm` (Definition 13.4.1, p. 427, with the debt constraints (13.13)): budget
  constraints (13.11) at every node, debt constraints, and market clearing
  `∑ᵢ θⁱ_t = θ̄_{−1}`, `∑ᵢ cⁱ_t = ȳ_t + θ̄_{−1}·d_t`. A concrete instance is
  `theorem_13_6_1_instance`.
* `bp_eq_13_20`: multiplying the date-`t` budget constraints by `π_t`, taking expectations and
  summing, `E ∑_{t≤T} π_t cⁱ_t + E π_T p_T·θⁱ_T ≤ π_0 p_0·θⁱ_{−1} + E ∑_{t≤T} π_t yⁱ_t`.
* `eq_13_26`: summing over agents and letting `T → ∞`,
  `∑ᵢ E ∑ π_t cⁱ_t + θ̄_{−1}·π_0 b_0 ≤ π_0 p_0·θ̄_{−1} + E ∑ π_t ȳ_t`, where
  `lim E π_T p_T = π_0 b_0` (`eq_13_6_bubble_limit`).
* `eq_13_27`: a bubble on an asset in positive supply makes this strict, so some agent has
  `E ∑ π_t cⁱ_t < π_0 p_0·θⁱ_{−1} + E ∑ π_t yⁱ_t` (`bp_exists_agent_slack`).
* `theorem_13_6_1`: if the present value of the aggregate endowment is finite, no asset in
  positive supply has a bubble, at any node.

**Departure.** The last step of the book's proof, "this contradicts agent `i`'s optimality",
uses that with complete markets the Radner consumption is optimal among consumption plans
satisfying the Arrow–Debreu budget (13.22) (Definition 13.4.2(ii), Theorem 13.5.1, §13.5) and
that preferences are strictly increasing. We state these two properties as hypotheses
(`hopt`, `hmono`) rather than deriving them from Radner optimality; §13.5 is formalised
separately. The book's hypothesis `E ∑_{t=0}^T π_t ȳ_t < ∞` is read as the convergence of
`∑_t E[π_t ȳ_t]`. Prices and dividends are nonnegative and supplies `θ̄_{−1}` nonnegative.
-/

open Filter Topology

namespace Miao.CompleteMarkets

variable {S ι J : Type*} [Fintype S] [Fintype ι] [Fintype J]
  (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ) (θ0 : ι → J → ℝ)
  (D : ι → List S → ℝ) in
/-- A Radner equilibrium with debt constraints (Miao, Definition 13.4.1, p. 427): the budget
constraints (13.11) (date 0: `cⁱ_0 + p_0·θⁱ_0 ≤ p_0·θⁱ_{−1} + yⁱ_0`), the debt constraints
(13.13) `f_{t+1}·θⁱ_t ≥ −D̄ⁱ_{t+1}` and market clearing. Optimality is imposed separately. -/
structure BPRadnerEqm where
  cons_nonneg : ∀ i h, 0 ≤ c i h
  budget_root : ∀ i, c i [] + ∑ j, p j [] * θ i j [] ≤ ∑ j, p j [] * θ0 i j + y i []
  budget_succ : ∀ i s h, c i (s :: h) + ∑ j, p j (s :: h) * θ i j (s :: h) ≤
      ∑ j, (p j (s :: h) + d j (s :: h)) * θ i j h + y i (s :: h)
  debt : ∀ i s h, -D i (s :: h) ≤ ∑ j, (p j (s :: h) + d j (s :: h)) * θ i j h
  clear_assets : ∀ j h, ∑ i, θ i j h = ∑ i, θ0 i j
  clear_goods_root : ∑ i, c i [] = ∑ i, y i []
  clear_goods_succ : ∀ s h,
      ∑ i, c i (s :: h) = ∑ i, y i (s :: h) + ∑ j, (∑ i, θ0 i j) * d j (s :: h)

variable {S ι J : Type*} [Fintype S] [Fintype ι] [Fintype J]

/-- `Pr(s^t) E_t[x_{t+1}] = ∑ₛ Pr(s^t, s) x(s^t, s)`. -/
theorem bp_pr_mul_condExp_one (T : BPTree S) (x : List S → ℝ) (h : List S) :
    T.pr h * bp_condExp T 1 x h = ∑ s, T.pr (s :: h) * x (s :: h) := by
  rw [bp_condExp_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [bp_condExp_zero]
  field_simp [(T.pr_pos h).ne']

theorem bp_nodeSum_succ_mono (t : ℕ) (f g : List S → ℝ)
    (hfg : ∀ s h, f (s :: h) ≤ g (s :: h)) : bp_nodeSum (t + 1) f ≤ bp_nodeSum (t + 1) g := by
  rw [bp_nodeSum_succ, bp_nodeSum_succ]
  exact bp_nodeSum_mono t _ _ (fun h => Finset.sum_le_sum (fun s _ => hfg s h))

/-- The deflated value of the date-`t+1` payoff of a date-`t` portfolio equals the deflated value
of its date-`t` cost (the pricing equation, summed over the date-`t` nodes). -/
theorem bp_pv_payoff (T : BPTree S) (δ : List S → ℝ) (p d : J → List S → ℝ)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (φ : J → List S → ℝ) (t : ℕ) :
    bp_nodeSum t (fun h => ∑ s, T.pr (s :: h) * δ (s :: h) *
        ∑ j, (p j (s :: h) + d j (s :: h)) * φ j h) =
      ∑ j, bp_pv T δ t (fun h => p j h * φ j h) := by
  unfold bp_pv
  rw [← bp_nodeSum_finsetSum]
  congr 1
  funext h
  have key : ∀ j, T.pr h * δ h * (p j h * φ j h) =
      (∑ s, T.pr (s :: h) * (δ (s :: h) * (p j (s :: h) + d j (s :: h)))) * φ j h := by
    intro j
    have hc := bp_pr_mul_condExp_one T (fun g => δ g * (p j g + d j g)) h
    rw [← hc, ← hP j h]
    ring
  simp only [key, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun s _ => ?_))
  ring

/-- Miao, (13.20), p. 432 (used in the proof of Theorem 13.6.1): for each agent,
`E ∑_{t≤T} π_t cⁱ_t + E π_T p_T·θⁱ_T ≤ π_0 p_0·θⁱ_{−1} + E ∑_{t≤T} π_t yⁱ_t`. -/
theorem bp_eq_13_20 (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ)
    (θ0 : ι → J → ℝ) (D : ι → List S → ℝ) (hE : BPRadnerEqm p d y c θ θ0 D)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (i : ι) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c i) +
        ∑ j, bp_pv T δ n (fun h => p j h * θ i j h) ≤
      δ [] * ∑ j, p j [] * θ0 i j + ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (y i) := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one]
    unfold bp_pv
    simp only [bp_nodeSum_zero, T.pr_nil, one_mul]
    have := mul_le_mul_of_nonneg_left (hE.budget_root i) (hδ []).le
    rw [mul_add, mul_add] at this
    simp only [Finset.mul_sum] at this ⊢
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun t => bp_pv T δ t (y i))]
    have hstep : bp_pv T δ (n + 1) (c i) + ∑ j, bp_pv T δ (n + 1) (fun h => p j h * θ i j h) ≤
        ∑ j, bp_pv T δ n (fun h => p j h * θ i j h) + bp_pv T δ (n + 1) (y i) := by
      rw [← bp_pv_payoff T δ p d hP (θ i) n]
      have h1 : bp_pv T δ (n + 1) (c i) + ∑ j, bp_pv T δ (n + 1) (fun h => p j h * θ i j h) =
          bp_nodeSum (n + 1) (fun g => T.pr g * δ g *
            (c i g + ∑ j, p j g * θ i j g)) := by
        unfold bp_pv
        rw [← bp_nodeSum_finsetSum, ← bp_nodeSum_add]
        congr 1
        funext g
        rw [mul_add, Finset.mul_sum]
      have h2 : bp_nodeSum n (fun h => ∑ s, T.pr (s :: h) * δ (s :: h) *
            ∑ j, (p j (s :: h) + d j (s :: h)) * θ i j h) + bp_pv T δ (n + 1) (y i) =
          bp_nodeSum (n + 1) (fun g => T.pr g * δ g *
            (∑ j, (p j g + d j g) * θ i j g.tail + y i g)) := by
        unfold bp_pv
        rw [bp_nodeSum_succ, bp_nodeSum_succ, ← bp_nodeSum_add]
        congr 1
        funext h
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        simp only [List.tail_cons]
        ring
      rw [h1, h2]
      refine bp_nodeSum_succ_mono n _ _ (fun s h => ?_)
      exact mul_le_mul_of_nonneg_left (hE.budget_succ i s h)
        (mul_nonneg (T.pr_pos _).le (hδ _).le)
    linarith

/-- `E[π_T p_T] = E_0[π_T p_T]`, the quantity whose limit is `π_0 b_0`. -/
theorem bp_pv_price_root (T : BPTree S) (δ q : List S → ℝ) (n : ℕ) :
    bp_pv T δ n q = bp_condExp T n (fun g => δ g * q g) [] := by
  rw [bp_condExp_root]
  unfold bp_pv
  congr 1
  funext h
  ring

/-- The present value of an endowment bounded by a summable aggregate converges. -/
theorem bp_summable_pv_of_le (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (x z : List S → ℝ) (hx : ∀ h, 0 ≤ x h) (hxz : ∀ h, x h ≤ z h)
    (hz : Summable (fun t => bp_pv T δ t z)) : Summable (fun t => bp_pv T δ t x) :=
  Summable.of_nonneg_of_le (fun t => bp_pv_nonneg T δ (fun h => (hδ h).le) t x hx)
    (fun t => bp_pv_mono T δ (fun h => (hδ h).le) t x z hxz) hz

/-- Miao, (13.26), p. 441: summing (13.20) over agents and letting `T → ∞`,
`∑ᵢ E ∑ π_t cⁱ_t + θ̄_{−1}·π_0 b_0 ≤ π_0 p_0·θ̄_{−1} + ∑ᵢ E ∑ π_t yⁱ_t`. Also returns the
convergence of each agent's present value of consumption. -/
theorem eq_13_26 (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ)
    (θ0 : ι → J → ℝ) (D : ι → List S → ℝ) (hE : BPRadnerEqm p d y c θ θ0 D)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (hp : ∀ j h, 0 ≤ p j h) (hd : ∀ j h, 0 ≤ d j h)
    (hy : ∀ i h, 0 ≤ y i h) (hsupp : ∀ j, 0 ≤ ∑ i, θ0 i j)
    (hY : Summable (fun t => bp_pv T δ t (fun h => ∑ i, y i h))) :
    (∀ i, Summable (fun t => bp_pv T δ t (c i))) ∧
    ∑ i, ∑' t, bp_pv T δ t (c i) +
        δ [] * ∑ j, (∑ i, θ0 i j) * bp_bubble T δ (p j) (d j) [] ≤
      δ [] * ∑ j, p j [] * (∑ i, θ0 i j) + ∑ i, ∑' t, bp_pv T δ t (y i) := by
  have hyi : ∀ i, Summable (fun t => bp_pv T δ t (y i)) := fun i =>
    bp_summable_pv_of_le T δ hδ (y i) _ (hy i)
      (fun h => Finset.single_le_sum (fun k _ => hy k h) (Finset.mem_univ i)) hY
  -- the aggregate of (13.20)
  have hagg : ∀ n, ∑ i, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c i) +
      ∑ j, (∑ i, θ0 i j) * bp_pv T δ n (p j) ≤
      δ [] * ∑ j, p j [] * (∑ i, θ0 i j) +
        ∑ i, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (y i) := by
    intro n
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      bp_eq_13_20 T δ hδ p d y c θ θ0 D hE hP i n)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    have hV : ∑ i, ∑ j, bp_pv T δ n (fun h => p j h * θ i j h) =
        ∑ j, (∑ i, θ0 i j) * bp_pv T δ n (p j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← bp_pv_finsetSum]
      have : (fun h => ∑ i, p j h * θ i j h) = fun h => p j h * (∑ i, θ0 i j) := by
        funext h
        rw [← Finset.mul_sum, hE.clear_assets j h]
      rw [this]
      unfold bp_pv
      rw [← bp_nodeSum_smul]
      congr 1
      funext h
      ring
    have hW : ∑ i, δ [] * ∑ j, p j [] * θ0 i j = δ [] * ∑ j, p j [] * (∑ i, θ0 i j) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    linarith
  have hVnn : ∀ n, 0 ≤ ∑ j, (∑ i, θ0 i j) * bp_pv T δ n (p j) := fun n =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (hsupp j)
      (bp_pv_nonneg T δ (fun h => (hδ h).le) n (p j) (hp j)))
  set R := δ [] * ∑ j, p j [] * (∑ i, θ0 i j) + ∑ i, ∑' t, bp_pv T δ t (y i) with hR
  have hYle : ∀ n, ∑ i, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (y i) ≤
      ∑ i, ∑' t, bp_pv T δ t (y i) := fun n =>
    Finset.sum_le_sum (fun i _ => (hyi i).sum_le_tsum _
      (fun t _ => bp_pv_nonneg T δ (fun h => (hδ h).le) t (y i) (hy i)))
  have hcnn : ∀ i t, 0 ≤ bp_pv T δ t (c i) := fun i t =>
    bp_pv_nonneg T δ (fun h => (hδ h).le) t (c i) (hE.cons_nonneg i)
  have hci : ∀ i, Summable (fun t => bp_pv T δ t (c i)) := by
    intro i
    refine summable_of_sum_range_le (c := R) (hcnn i) (fun n => ?_)
    have h1 : ∑ t ∈ Finset.range n, bp_pv T δ t (c i) ≤
        ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c i) := by
      rw [Finset.sum_range_succ]
      linarith [hcnn i n]
    have h2 : ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c i) ≤
        ∑ k, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c k) :=
      Finset.single_le_sum (f := fun k => ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c k))
        (fun k _ => Finset.sum_nonneg (fun t _ => hcnn k t)) (Finset.mem_univ i)
    linarith [hagg n, hVnn n, hYle n]
  refine ⟨hci, ?_⟩
  have hlimC : Tendsto (fun n => ∑ i, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c i)) atTop
      (𝓝 (∑ i, ∑' t, bp_pv T δ t (c i))) :=
    tendsto_finsetSum _ (fun i _ =>
      (tendsto_add_atTop_iff_nat 1).2 (hci i).hasSum.tendsto_sum_nat)
  have hlimY : Tendsto (fun n => ∑ i, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (y i)) atTop
      (𝓝 (∑ i, ∑' t, bp_pv T δ t (y i))) :=
    tendsto_finsetSum _ (fun i _ =>
      (tendsto_add_atTop_iff_nat 1).2 (hyi i).hasSum.tendsto_sum_nat)
  have hlimV : Tendsto (fun n => ∑ j, (∑ i, θ0 i j) * bp_pv T δ n (p j)) atTop
      (𝓝 (δ [] * ∑ j, (∑ i, θ0 i j) * bp_bubble T δ (p j) (d j) [])) := by
    rw [Finset.mul_sum]
    refine tendsto_finsetSum _ (fun j _ => ?_)
    have hb := eq_13_6_bubble_limit T δ (p j) (d j) hδ (hp j) (hd j) (hP j) []
    have hb' := hb.const_mul (δ [])
    have heq : (fun n => δ [] * (1 / δ [] * bp_condExp T n (fun g => δ g * p j g) [])) =
        fun n => bp_pv T δ n (p j) := by
      funext n
      rw [bp_pv_price_root]
      field_simp [(hδ []).ne']
    rw [heq] at hb'
    have := hb'.const_mul (∑ i, θ0 i j)
    convert this using 2
    ring
  exact le_of_tendsto_of_tendsto' (hlimC.add hlimV) (tendsto_const_nhds.add hlimY) hagg

/-- Miao, (13.27), p. 441: if some asset in positive supply has a bubble, (13.26) is strict:
`∑ᵢ E ∑ π_t cⁱ_t < π_0 p_0·θ̄_{−1} + ∑ᵢ E ∑ π_t yⁱ_t`. -/
theorem eq_13_27 (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ)
    (θ0 : ι → J → ℝ) (D : ι → List S → ℝ) (hE : BPRadnerEqm p d y c θ θ0 D)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (hp : ∀ j h, 0 ≤ p j h) (hd : ∀ j h, 0 ≤ d j h)
    (hy : ∀ i h, 0 ≤ y i h) (hsupp : ∀ j, 0 ≤ ∑ i, θ0 i j)
    (hY : Summable (fun t => bp_pv T δ t (fun h => ∑ i, y i h)))
    (j₀ : J) (hj₀ : 0 < ∑ i, θ0 i j₀) (hb : 0 < bp_bubble T δ (p j₀) (d j₀) []) :
    ∑ i, ∑' t, bp_pv T δ t (c i) <
      δ [] * ∑ j, p j [] * (∑ i, θ0 i j) + ∑ i, ∑' t, bp_pv T δ t (y i) := by
  have h26 := (eq_13_26 T δ hδ p d y c θ θ0 D hE hP hp hd hy hsupp hY).2
  have hpos : 0 < δ [] * ∑ j, (∑ i, θ0 i j) * bp_bubble T δ (p j) (d j) [] := by
    refine mul_pos (hδ []) ?_
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (∑ i, θ0 i j) * bp_bubble T δ (p j) (d j) [] :=
      fun j _ => mul_nonneg (hsupp j)
        (eq_13_6_bubble_bounds T δ (p j) (d j) hδ (hp j) (hd j) (hP j) []).1
    exact lt_of_lt_of_le (mul_pos hj₀ hb) (Finset.single_le_sum hnn (Finset.mem_univ j₀))
  linarith

/-- Miao, p. 441: "this means that for at least one agent `i`,
`E ∑ π_t cⁱ_t < π_0 p_0·θⁱ_{−1} + E ∑ π_t yⁱ_t`". -/
theorem bp_exists_agent_slack (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ)
    (θ0 : ι → J → ℝ) (D : ι → List S → ℝ) (hE : BPRadnerEqm p d y c θ θ0 D)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (hp : ∀ j h, 0 ≤ p j h) (hd : ∀ j h, 0 ≤ d j h)
    (hy : ∀ i h, 0 ≤ y i h) (hsupp : ∀ j, 0 ≤ ∑ i, θ0 i j)
    (hY : Summable (fun t => bp_pv T δ t (fun h => ∑ i, y i h)))
    (j₀ : J) (hj₀ : 0 < ∑ i, θ0 i j₀) (hb : 0 < bp_bubble T δ (p j₀) (d j₀) []) :
    ∃ i, ∑' t, bp_pv T δ t (c i) <
      δ [] * ∑ j, p j [] * θ0 i j + ∑' t, bp_pv T δ t (y i) := by
  have h27 := eq_13_27 T δ hδ p d y c θ θ0 D hE hP hp hd hy hsupp hY j₀ hj₀ hb
  have hW : δ [] * ∑ j, p j [] * (∑ i, θ0 i j) + ∑ i, ∑' t, bp_pv T δ t (y i) =
      ∑ i, (δ [] * ∑ j, p j [] * θ0 i j + ∑' t, bp_pv T δ t (y i)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [hW] at h27
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt h27
  exact ⟨i, hi⟩

/-- **Theorem 13.6.1** (Santos–Woodford, Miao, p. 440). Let `p` be a Radner equilibrium price
system under debt constraints, with complete markets and state price deflator `π`. If the
present value of the aggregate endowment is finite, there is no bubble on any asset in positive
supply. Optimality is used through the Arrow–Debreu budget (13.22): each agent's consumption is
best among plans `x ≥ 0` with `E ∑ π_t x_t ≤ π_0 p_0·θⁱ_{−1} + E ∑ π_t yⁱ_t` (`hopt`), and
preferences strictly increase with date-0 consumption (`hmono`). -/
theorem theorem_13_6_1 (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ)
    (θ0 : ι → J → ℝ) (D : ι → List S → ℝ) (hE : BPRadnerEqm p d y c θ θ0 D)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (hp : ∀ j h, 0 ≤ p j h) (hd : ∀ j h, 0 ≤ d j h)
    (hy : ∀ i h, 0 ≤ y i h) (hsupp : ∀ j, 0 ≤ ∑ i, θ0 i j)
    (hY : Summable (fun t => bp_pv T δ t (fun h => ∑ i, y i h)))
    (U : ι → (List S → ℝ) → ℝ)
    (hopt : ∀ i (x : List S → ℝ), (∀ h, 0 ≤ x h) → Summable (fun t => bp_pv T δ t x) →
      ∑' t, bp_pv T δ t x ≤ δ [] * ∑ j, p j [] * θ0 i j + ∑' t, bp_pv T δ t (y i) →
      U i x ≤ U i (c i))
    (hmono : ∀ i (x : List S → ℝ) (ε : ℝ), 0 < ε →
      U i x < U i (fun h => x h + if h = [] then ε else 0))
    (j : J) (hj : 0 < ∑ i, θ0 i j) (h : List S) : bp_bubble T δ (p j) (d j) h = 0 := by
  have hb0 := (eq_13_6_bubble_bounds T δ (p j) (d j) hδ (hp j) (hd j) (hP j) []).1
  refine bp_bubble_eq_zero_of_root T δ (p j) (d j) hδ (hp j) (hd j) (hP j) ?_ h
  by_contra hne
  have hb : 0 < bp_bubble T δ (p j) (d j) [] := lt_of_le_of_ne hb0 (Ne.symm hne)
  obtain ⟨i, hi⟩ := bp_exists_agent_slack T δ hδ p d y c θ θ0 D hE hP hp hd hy hsupp hY j hj hb
  have hci := (eq_13_26 T δ hδ p d y c θ θ0 D hE hP hp hd hy hsupp hY).1 i
  set W := δ [] * ∑ j, p j [] * θ0 i j + ∑' t, bp_pv T δ t (y i) with hW
  set C := ∑' t, bp_pv T δ t (c i) with hC
  set ε := (W - C) / δ [] with hε
  have hεpos : 0 < ε := div_pos (by linarith) (hδ [])
  set x : List S → ℝ := fun g => c i g + if g = [] then ε else 0 with hx
  have hpvx : ∀ t, bp_pv T δ t x = bp_pv T δ t (c i) + if t = 0 then W - C else 0 := by
    intro t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      unfold bp_pv
      simp only [bp_nodeSum_zero, T.pr_nil, one_mul, hx, ↓reduceIte, hε]
      field_simp [(hδ []).ne']
    · have hne : t ≠ 0 := ht.ne'
      simp only [hne, ↓reduceIte, add_zero]
      unfold bp_pv
      refine bp_nodeSum_congr t _ _ (fun g hg => ?_)
      have : g ≠ [] := by
        intro hg0
        rw [hg0] at hg
        exact hne hg.symm
      simp [hx, this]
  have hsx : HasSum (fun t => bp_pv T δ t x) (C + (W - C)) := by
    have h1 := (hci.hasSum).add (hasSum_ite_eq 0 (W - C))
    convert h1 using 1
    funext t
    rw [hpvx]
  have hxnn : ∀ g, 0 ≤ x g := by
    intro g
    have := hE.cons_nonneg i g
    by_cases hg : g = []
    · subst hg
      simp only [hx, ↓reduceIte]
      linarith
    · simp only [hx, hg, ↓reduceIte, add_zero]
      exact this
  have hle := hopt i x hxnn hsx.summable (by rw [hsx.tsum_eq]; linarith)
  have hlt := hmono i (c i) ε hεpos
  exact absurd hle (not_le.2 hlt)

/-- A concrete Radner equilibrium (`BPRadnerEqm`) in which every hypothesis of Theorem 13.6.1
holds, including `hopt` and `hmono`: one agent, one share of a stock in positive supply that pays
nothing and costs nothing, endowment `1` at the root and `0` afterwards, `π = 1` and the utility
`U(x) = x_0`. -/
theorem theorem_13_6_1_instance :
    BPRadnerEqm (S := Unit) (ι := Unit) (J := Unit) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ h => if h = [] then 1 else 0) (fun _ h => if h = [] then 1 else 0)
      (fun _ _ _ => 1) (fun _ _ => 1) (fun _ _ => 0) ∧
    (∀ _j : Unit, bp_Prices bp_detTree (fun _ => 1) (fun _ => 0) (fun _ => 0)) ∧
    Summable (fun t => bp_pv bp_detTree (fun _ => 1) t
      (fun h => ∑ _i : Unit, if h = [] then (1 : ℝ) else 0)) ∧
    (∀ (_i : Unit) (x : List Unit → ℝ), (∀ h, 0 ≤ x h) →
      Summable (fun t => bp_pv bp_detTree (fun _ => 1) t x) →
      ∑' t, bp_pv bp_detTree (fun _ => 1) t x ≤
        1 * ∑ _j : Unit, (0 : ℝ) * 1 + ∑' t, bp_pv bp_detTree (fun _ => 1) t
          (fun h => if h = [] then 1 else 0) →
      x [] ≤ (fun h : List Unit => if h = [] then (1 : ℝ) else 0) []) ∧
    (∀ (_i : Unit) (x : List Unit → ℝ) (ε : ℝ), 0 < ε →
      x [] < (fun h => x h + if h = [] then ε else 0) []) := by
  have hpvY : ∀ t, bp_pv bp_detTree (fun _ => 1) t (fun h => if h = [] then (1 : ℝ) else 0) =
      if t = 0 then 1 else 0 := by
    intro t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      simp [bp_pv, bp_nodeSum_zero, bp_detTree]
    · have hne : t ≠ 0 := ht.ne'
      simp only [hne, ↓reduceIte]
      unfold bp_pv
      rw [bp_nodeSum_congr t _ (fun _ => 0) (fun g hg => by
        have : g ≠ [] := by
          intro hg0
          rw [hg0] at hg
          exact hne hg.symm
        simp [this])]
      simpa using bp_nodeSum_smul t 0 (fun _ : List Unit => (0 : ℝ))
  have hsY : HasSum (fun t => bp_pv bp_detTree (fun _ => 1) t
      (fun h => if h = [] then (1 : ℝ) else 0)) 1 := by
    convert hasSum_ite_eq 0 (1 : ℝ) using 1
    funext t
    rw [hpvY]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i h
    split_ifs <;> norm_num
  · intro i
    simp
  · intro i s h
    simp
  · intro i s h
    simp
  · intro j h
    simp
  · simp
  · intro s h
    simp
  · intro j h
    simp only [add_zero, mul_zero]
    exact (bp_condExp_const bp_detTree 1 0 h).symm
  · simpa using hsY.summable
  · intro i x hx hsx hle
    rw [hsY.tsum_eq] at hle
    have h0 : bp_pv bp_detTree (fun _ => 1) 0 x ≤ ∑' t, bp_pv bp_detTree (fun _ => 1) t x :=
      hsx.le_tsum 0 (fun t _ => bp_pv_nonneg bp_detTree _ (fun _ => zero_le_one) t x hx)
    have hx0 : bp_pv bp_detTree (fun _ => 1) 0 x = x [] := by
      simp [bp_pv, bp_nodeSum_zero, bp_detTree]
    simp only [↓reduceIte]
    simp at hle
    linarith
  · intro i x ε hε
    simp only [↓reduceIte]
    linarith

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bubbles and debt limits (Kocherlakota 2008, Exercise 13.7)

Miao, §13.9, Exercise 13.7 (p. 454), on the event tree of `BPTree`. A representative agent with
`∑ₜ ∑_{sᵗ} Pr(sᵗ) βᵗ u(c(sᵗ))`, a constant endowment `y`, one share of a long-lived asset with
constant dividend `d` and price `p(sᵗ)`, and complete Arrow securities `b(s^{t+1})` with prices
`q(s^{t+1})` (initial holdings zero). The budget constraint at `sᵗ` is
`c + a p + ∑ q b' ≤ y + a_−(p + d) + b` and the debt constraint is
`a(sᵗ)(p(s^{t+1}) + d) + b(s^{t+1}) ≥ −D(s^{t+1})`.

* `ex_13_7_bubble`: if `b̃` satisfies `b̃_t = βE_t b̃_{t+1}` and the debt limit is
  `D̂ = y/(1 − β) − b̃`, then `q(s^{t+1}) = β Pr(s^{t+1} | sᵗ)` and `p = βd/(1 − β) + b̃` support
  the no-trade equilibrium `c = y + d`, `a = 1`, `b = 0`: the plan is feasible and beats every
  feasible plan with convergent utility. The asset prices solve the Euler equations
  (`ex_13_7_prices`).
* `ex_13_7`: the case `b̃ = 0`, debt limit `D = y/(1 − β)`, price `p^f = βd/(1 − β)`.

The proof is the tree version of the sufficiency argument: deflating by `βᵗ Pr(sᵗ)`, the budget
constraints telescope, and the debt constraint bounds the deflated terminal wealth below by
`−β^{T+1} y/(1 − β) + b̃_0` (the bubble is a discounted martingale), which offsets the bubble in
the initial wealth `p_0 + d`.

**Departure.** The exercise says "prove that the equilibrium price is given by" `q`, `p^f`. We
prove that these prices (and, with the perturbed limit, `p^f + b̃`) support the equilibrium and
solve the Euler equations; uniqueness of the equilibrium price is not formalised. The utility
`u` is any function with a supergradient `u'(c̄) ≥ 0` at `c̄ = y + d`.
-/

open Filter Topology

namespace Miao.CompleteMarkets

/-- The budget and debt constraints of Exercise 13.7 for the plan `(c, a, b)` at prices `(q, p)`
and debt limit `D`: positive consumption, the date-0 budget (one share, no Arrow securities),
the date-`t` budgets and the debt constraints. -/
def bp_k08Budget {S : Type*} [Fintype S] (q p : List S → ℝ) (y dv : ℝ) (D : List S → ℝ)
    (c a b : List S → ℝ) : Prop :=
  (∀ h, 0 < c h) ∧ c [] + a [] * p [] + ∑ s, q [s] * b [s] ≤ y + (p [] + dv) ∧
    (∀ s h, c (s :: h) + a (s :: h) * p (s :: h) + ∑ s', q (s' :: s :: h) * b (s' :: s :: h) ≤
      y + a h * (p (s :: h) + dv) + b (s :: h)) ∧
    ∀ s h, -D (s :: h) ≤ a h * (p (s :: h) + dv) + b (s :: h)

/-- Expected discounted utility `∑ₜ βᵗ ∑_{sᵗ} Pr(sᵗ) u(c(sᵗ))`. -/
noncomputable def bp_k08U {S : Type*} [Fintype S] (T : BPTree S) (β : ℝ) (u : ℝ → ℝ)
    (c : List S → ℝ) : ℝ :=
  ∑' t, β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h))

/-- A discounted martingale `b̃_t = β E_t b̃_{t+1}` satisfies `βᵏ E[b̃_k] = b̃_0`. -/
theorem bp_k08_martingale {S : Type*} [Fintype S] (T : BPTree S) (β : ℝ) (bt : List S → ℝ)
    (hb : ∀ h, bt h = β * bp_condExp T 1 bt h) (k : ℕ) :
    β ^ k * bp_nodeSum k (fun h => T.pr h * bt h) = bt [] := by
  have key : ∀ k h, β ^ k * bp_condExp T k bt h = bt h := by
    intro k
    induction k with
    | zero => intro h; simp [bp_condExp_zero]
    | succ k ih =>
      intro h
      rw [show k + 1 = 1 + k by omega, bp_condExp_add, pow_add, pow_one, mul_assoc,
        ← bp_condExp_smul, bp_condExp_congr T 1 _ bt ih, ← hb h]
  rw [← bp_condExp_root]
  exact key k []

/-- `∑_{t≤n} βᵗ x + β^{n+1} x/(1 − β) = x/(1 − β)`. -/
theorem bp_k08_geom (β x : ℝ) (hβ1 : β < 1) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), β ^ t * x + β ^ (n + 1) * x / (1 - β) = x / (1 - β) := by
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, pow_one]
    field_simp
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, pow_succ β (n + 1)]
    have e : β ^ (n + 1) * β * x / (1 - β) = β ^ (n + 1) * x / (1 - β) - β ^ (n + 1) * x := by
      field_simp
      ring
    rw [e]
    ring

/-- Exercise 13.7 (Miao, p. 454): the prices of the perturbed economy solve the Euler equations
of the no-trade allocation: `q(s^{t+1}) u'(c̄) = β Pr(s^{t+1} | sᵗ) u'(c̄)` and
`p_t = βE_t[p_{t+1} + d]`. -/
theorem ex_13_7_prices {S : Type*} [Fintype S] (T : BPTree S) (β dv : ℝ) (hβ1 : β < 1)
    (bt : List S → ℝ) (hb : ∀ h, bt h = β * bp_condExp T 1 bt h) (h : List S) :
    β * dv / (1 - β) + bt h = β * bp_condExp T 1 (fun g => β * dv / (1 - β) + bt g + dv) h := by
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  rw [bp_condExp_add_fun, bp_condExp_add_fun, bp_condExp_const, bp_condExp_const]
  rw [hb h]
  field_simp
  ring

/-- **Exercise 13.7**, perturbed debt limit (Kocherlakota 2008, Miao, p. 454). Let `0 < β < 1`,
`y > 0`, `d ≥ 0`, let `b̃` satisfy `b̃_t = βE_t b̃_{t+1}`, and let the debt limit be
`D̂(s^{t+1}) = y/(1 − β) − b̃(s^{t+1})`. With `q(s^{t+1}) = β Pr(s^{t+1} | sᵗ)` and
`p = βd/(1 − β) + b̃`, the no-trade plan `c = y + d`, `a = 1`, `b = 0` is feasible and is optimal
among feasible plans with convergent utility, for any `u` with a supergradient
`u'(y + d) ≥ 0` at `y + d`. -/
theorem ex_13_7_bubble {S : Type*} [Fintype S] (T : BPTree S) (β y dv : ℝ) (hβ : 0 < β)
    (hβ1 : β < 1) (hy : 0 < y) (hd : 0 ≤ dv) (bt : List S → ℝ)
    (hb : ∀ h, bt h = β * bp_condExp T 1 bt h) (u : ℝ → ℝ) (du : ℝ)
    (hsg : ∀ x, 0 < x → u x ≤ u (y + dv) + du * (x - (y + dv))) (hdu : 0 ≤ du) :
    let q : List S → ℝ := fun g => match g with
      | [] => 0
      | s :: h => β * T.pr (s :: h) / T.pr h
    let p : List S → ℝ := fun h => β * dv / (1 - β) + bt h
    let D : List S → ℝ := fun h => y / (1 - β) - bt h
    bp_k08Budget q p y dv D (fun _ => y + dv) (fun _ => 1) (fun _ => 0) ∧
      ∀ c a b, bp_k08Budget q p y dv D c a b →
        Summable (fun t => β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h))) →
        bp_k08U T β u c ≤ bp_k08U T β u (fun _ => y + dv) := by
  intro q p D
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hpf : 0 ≤ β * dv / (1 - β) := div_nonneg (mul_nonneg hβ.le hd) (by linarith)
  refine ⟨⟨fun _ => by linarith, ?_, fun s h => ?_, fun s h => ?_⟩, ?_⟩
  · simp only [mul_zero, Finset.sum_const_zero, add_zero]
    linarith
  · simp only [mul_zero, Finset.sum_const_zero, add_zero]
    linarith
  · simp only [p, D, add_zero, neg_sub]
    have : 0 ≤ y / (1 - β) := div_nonneg hy.le (by linarith)
    linarith
  intro c a b hB hs
  obtain ⟨hc, hb0, hbs, hdebt⟩ := hB
  -- deflated wealth `W(sᵗ)` carried into each node
  set W : List S → ℝ := fun g => match g with
    | [] => p [] + dv
    | s :: h => a h * (p (s :: h) + dv) + b (s :: h) with hW
  -- the pricing identity at every node
  have hprice : ∀ h, T.pr h * (a h * p h + ∑ s, q (s :: h) * b (s :: h)) =
      β * ∑ s, T.pr (s :: h) * W (s :: h) := by
    intro h
    have hph : p h = β * bp_condExp T 1 (fun g => p g + dv) h :=
      ex_13_7_prices T β dv hβ1 bt hb h
    have hc1 := bp_pr_mul_condExp_one T (fun g => p g + dv) h
    rw [hph, mul_add, ← mul_assoc, mul_comm (T.pr h) (a h), mul_assoc, mul_left_comm (T.pr h),
      hc1, Finset.mul_sum]
    simp only [q, W, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    field_simp [(T.pr_pos h).ne']
  -- per-node budget in deflated form
  have hnode : ∀ h, T.pr h * c h + β * ∑ s, T.pr (s :: h) * W (s :: h) ≤
      T.pr h * y + T.pr h * W h := by
    intro h
    rw [← hprice h]
    have hpr := (T.pr_pos h).le
    cases h with
    | nil =>
      have := mul_le_mul_of_nonneg_left hb0 hpr
      simp only [W]
      nlinarith
    | cons s h =>
      have := mul_le_mul_of_nonneg_left (hbs s h) hpr
      simp only [W]
      nlinarith
  -- telescoping
  have htel : ∀ n, ∑ t ∈ Finset.range (n + 1), β ^ t * bp_nodeSum t (fun h => T.pr h * c h) +
      β ^ (n + 1) * bp_nodeSum (n + 1) (fun h => T.pr h * W h) ≤
      ∑ t ∈ Finset.range (n + 1), β ^ t * y + W [] := by
    have hdate : ∀ t, β ^ t * bp_nodeSum t (fun h => T.pr h * c h) +
        β ^ (t + 1) * bp_nodeSum (t + 1) (fun h => T.pr h * W h) ≤
        β ^ t * y + β ^ t * bp_nodeSum t (fun h => T.pr h * W h) := by
      intro t
      have hm := bp_nodeSum_mono t _ _ hnode
      rw [bp_nodeSum_add, bp_nodeSum_add, bp_nodeSum_smul, bp_nodeSum_const] at hm
      rw [bp_nodeSum_succ, pow_succ]
      have := mul_le_mul_of_nonneg_left hm (pow_nonneg hβ.le t)
      nlinarith
    intro n
    induction n with
    | zero =>
      have := hdate 0
      simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, bp_nodeSum_zero,
        T.pr_nil] at this ⊢
      linarith
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun t => β ^ t * y)]
      have := hdate (n + 1)
      linarith
  -- the debt constraint bounds terminal wealth
  have hterm : ∀ n, -(β ^ (n + 1) * y / (1 - β)) + bt [] ≤
      β ^ (n + 1) * bp_nodeSum (n + 1) (fun h => T.pr h * W h) := by
    intro n
    have hm : bp_nodeSum (n + 1) (fun h => T.pr h * (-(y / (1 - β)) + bt h)) ≤
        bp_nodeSum (n + 1) (fun h => T.pr h * W h) := by
      refine bp_nodeSum_succ_mono n _ _ (fun s h => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (T.pr_pos _).le
      have := hdebt s h
      simp only [W]
      simp only [D] at this
      linarith
    have e : bp_nodeSum (n + 1) (fun h => T.pr h * (-(y / (1 - β)) + bt h)) =
        -(y / (1 - β)) + bp_nodeSum (n + 1) (fun h => T.pr h * bt h) := by
      have hf : (fun h => T.pr h * (-(y / (1 - β)) + bt h)) =
          fun h => T.pr h * (-(y / (1 - β))) + T.pr h * bt h := by
        funext h
        ring
      rw [hf, bp_nodeSum_add, bp_nodeSum_const]
    rw [e] at hm
    have hmart := bp_k08_martingale T β bt hb (n + 1)
    have := mul_le_mul_of_nonneg_left hm (pow_nonneg hβ.le (n + 1))
    rw [mul_add, hmart] at this
    have e2 : β ^ (n + 1) * -(y / (1 - β)) = -(β ^ (n + 1) * y / (1 - β)) := by ring
    linarith
  -- partial sums of deflated consumption
  have hcons : ∀ n, ∑ t ∈ Finset.range (n + 1),
      β ^ t * bp_nodeSum t (fun h => T.pr h * (c h - (y + dv))) ≤
      β ^ (n + 1) * (y + dv) / (1 - β) := by
    intro n
    have hg1 := bp_k08_geom β y hβ1 n
    have hg2 := bp_k08_geom β (y + dv) hβ1 n
    have hsplit : ∀ t, β ^ t * bp_nodeSum t (fun h => T.pr h * (c h - (y + dv))) =
        β ^ t * bp_nodeSum t (fun h => T.pr h * c h) - β ^ t * (y + dv) := by
      intro t
      have : (fun h => T.pr h * (c h - (y + dv))) =
          fun h => T.pr h * c h - T.pr h * (y + dv) := by
        funext h
        ring
      rw [this, bp_nodeSum_sub, bp_nodeSum_const]
      ring
    simp only [hsplit, Finset.sum_sub_distrib]
    have hW0 : W [] = β * dv / (1 - β) + bt [] + dv := rfl
    have := htel n
    have := hterm n
    have e : β * dv / (1 - β) + dv = dv / (1 - β) := by field_simp; ring
    have e2 : (y + dv) / (1 - β) = y / (1 - β) + dv / (1 - β) := by ring
    linarith
  -- utility comparison
  have hsc : Summable (fun t => β ^ t * bp_nodeSum t (fun h => T.pr h * u (y + dv))) := by
    simp only [bp_nodeSum_const]
    exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
  have hutil : ∀ n, ∑ t ∈ Finset.range (n + 1),
      (β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h)) -
        β ^ t * bp_nodeSum t (fun h => T.pr h * u (y + dv))) ≤
      du * (β ^ (n + 1) * (y + dv) / (1 - β)) := by
    intro n
    have hle : ∀ t, β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h)) -
        β ^ t * bp_nodeSum t (fun h => T.pr h * u (y + dv)) ≤
        du * (β ^ t * bp_nodeSum t (fun h => T.pr h * (c h - (y + dv)))) := by
      intro t
      have hm : bp_nodeSum t (fun h => T.pr h * u (c h)) ≤
          bp_nodeSum t (fun h => T.pr h * u (y + dv) + du * (T.pr h * (c h - (y + dv)))) := by
        refine bp_nodeSum_mono t _ _ (fun h => ?_)
        have := mul_le_mul_of_nonneg_left (hsg (c h) (hc h)) (T.pr_pos h).le
        nlinarith
      rw [bp_nodeSum_add, bp_nodeSum_smul] at hm
      have := mul_le_mul_of_nonneg_left hm (pow_nonneg hβ.le t)
      nlinarith
    calc _ ≤ ∑ t ∈ Finset.range (n + 1),
          du * (β ^ t * bp_nodeSum t (fun h => T.pr h * (c h - (y + dv)))) :=
          Finset.sum_le_sum (fun t _ => hle t)
      _ = du * ∑ t ∈ Finset.range (n + 1),
          β ^ t * bp_nodeSum t (fun h => T.pr h * (c h - (y + dv))) := by
          rw [Finset.mul_sum]
      _ ≤ du * (β ^ (n + 1) * (y + dv) / (1 - β)) :=
          mul_le_mul_of_nonneg_left (hcons n) hdu
  have hlim : Tendsto (fun n => ∑ t ∈ Finset.range (n + 1),
      (β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h)) -
        β ^ t * bp_nodeSum t (fun h => T.pr h * u (y + dv)))) atTop
      (𝓝 (bp_k08U T β u c - bp_k08U T β u (fun _ => y + dv))) := by
    unfold bp_k08U
    rw [← hs.tsum_sub hsc]
    exact (tendsto_add_atTop_iff_nat 1).2 (hs.sub hsc).hasSum.tendsto_sum_nat
  have hzero : Tendsto (fun n : ℕ => du * (β ^ (n + 1) * (y + dv) / (1 - β))) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).comp
      (tendsto_add_atTop_nat 1)).mul_const ((y + dv) / (1 - β))
    have := this.const_mul du
    simp only [zero_mul, mul_zero] at this
    convert this using 2 with n
    simp only [Function.comp_apply]
    ring
  have := le_of_tendsto_of_tendsto' hlim hzero hutil
  linarith

/-- **Exercise 13.7** (Kocherlakota 2008, Miao, p. 454). With the debt limit
`D = y/(1 − β)`, the Arrow prices `q(s^{t+1}) = β Pr(s^{t+1} | sᵗ)` and the fundamental price
`p^f = βd/(1 − β)` support the equilibrium `c = y + d`, `a = 1`, `b = 0`, and `p^f` solves
`p = βE_t[p + d]`. -/
theorem ex_13_7 {S : Type*} [Fintype S] (T : BPTree S) (β y dv : ℝ) (hβ : 0 < β)
    (hβ1 : β < 1) (hy : 0 < y) (hd : 0 ≤ dv) (u : ℝ → ℝ) (du : ℝ)
    (hsg : ∀ x, 0 < x → u x ≤ u (y + dv) + du * (x - (y + dv))) (hdu : 0 ≤ du) :
    let q : List S → ℝ := fun g => match g with
      | [] => 0
      | s :: h => β * T.pr (s :: h) / T.pr h
    let p : List S → ℝ := fun _ => β * dv / (1 - β)
    let D : List S → ℝ := fun _ => y / (1 - β)
    (∀ h, p h = β * bp_condExp T 1 (fun g => p g + dv) h) ∧
    bp_k08Budget q p y dv D (fun _ => y + dv) (fun _ => 1) (fun _ => 0) ∧
      ∀ c a b, bp_k08Budget q p y dv D c a b →
        Summable (fun t => β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h))) →
        bp_k08U T β u c ≤ bp_k08U T β u (fun _ => y + dv) := by
  intro q p D
  have hb0 : ∀ h : List S, (fun _ => (0 : ℝ)) h = β * bp_condExp T 1 (fun _ => 0) h := by
    intro h
    simp [bp_condExp_const]
  have key := ex_13_7_bubble T β y dv hβ hβ1 hy hd (fun _ => 0) hb0 u du hsg hdu
  simp only [add_zero, sub_zero] at key
  refine ⟨fun h => ?_, key⟩
  have := ex_13_7_prices T β dv hβ1 (fun _ => 0) hb0 h
  simpa using this

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Deterministic Radner economies with one stock

The setting of Examples 13.6.1 and 13.6.2 and Exercises 13.5–13.6 (Miao, §13.6, pp. 441–444,
and §13.9, p. 453): a deterministic economy with finitely many agents `ι` and one long-lived
asset (stock or money) with ex-dividend price `p_t` and dividend `d_t`.

* `bp_detBudget`: agent `i`'s sequential budget constraints (13.11),
  `c_0 + p_0θ_0 ≤ (p_0 + d_0)θ_{−1} + y_0` and `c_t + p_tθ_t ≤ (p_t + d_t)θ_{t−1} + y_t`, with
  positive consumption and a portfolio constraint `con t p_t θ_t` (a borrowing constraint
  (13.14), a short-sales constraint (13.15), …).
* `BPDetEqm` (Definition 13.4.1): budget feasibility, optimality among admissible feasible
  plans, and market clearing `∑ᵢ θⁱ_t = θ̄_{−1}`, `∑ᵢ cⁱ_t = ȳ_t + θ̄_{−1} d_t`.
* `bp_detU β u c = ∑ βᵗ u(c_t)`; a plan is admissible (`bp_detAdm`) when this series converges.
* `bp_det_sufficiency`: the Euler–Kuhn–Tucker sufficiency argument used to verify optimality in
  the examples: with a supergradient `u'`, multipliers `λ_t = βᵗ u'(c_t)`,
  `(θ'_t − θ_t)(λ_{t+1}(p_{t+1} + d_{t+1}) − λ_t p_t) ≤ 0` for every feasible `θ'` and a
  vanishing boundary term, `c` beats every admissible feasible `c'`.
* `bp_log_supergradient`, `bp_crra_supergradient`: `log` and `c^{1−γ}/(1−γ)` (`γ > 0`, `γ ≠ 1`)
  satisfy `u(x') ≤ u(x) + u'(x)(x' − x)`.
* `bp_tail f t = ∑_{s>t} f_s` and its elementary properties.
-/

open Filter Topology

namespace Miao.CompleteMarkets

/-- Agent `i`'s budget set in the deterministic one-asset economy (Miao, (13.11)): positive
consumption, the date-0 and date-`t` budget constraints, and the portfolio constraint. -/
def bp_detBudget (p d y : ℕ → ℝ) (θ0 : ℝ) (con : ℕ → ℝ → ℝ → Prop) (c θ : ℕ → ℝ) : Prop :=
  (∀ t, 0 < c t) ∧ c 0 + p 0 * θ 0 ≤ (p 0 + d 0) * θ0 + y 0 ∧
    (∀ t, c (t + 1) + p (t + 1) * θ (t + 1) ≤ (p (t + 1) + d (t + 1)) * θ t + y (t + 1)) ∧
    ∀ t, con t (p t) (θ t)

variable {ι : Type*} [Fintype ι] (U : ι → (ℕ → ℝ) → ℝ) (adm : ι → (ℕ → ℝ) → Prop)
  (y : ι → ℕ → ℝ) (d : ℕ → ℝ) (θ0 : ι → ℝ) (con : ι → ℕ → ℝ → ℝ → Prop) (c θ : ι → ℕ → ℝ)
  (p : ℕ → ℝ) in
/-- A Radner equilibrium of the deterministic one-asset economy (Miao, Definition 13.4.1,
p. 427): each agent's plan is feasible and best among admissible feasible plans, and the asset
and goods markets clear. -/
structure BPDetEqm : Prop where
  budget : ∀ i, bp_detBudget p d (y i) (θ0 i) (con i) (c i) (θ i)
  adm_self : ∀ i, adm i (c i)
  optimal : ∀ i c' θ', bp_detBudget p d (y i) (θ0 i) (con i) c' θ' → adm i c' →
    U i c' ≤ U i (c i)
  clear_assets : ∀ t, ∑ i, θ i t = ∑ i, θ0 i
  clear_goods : ∀ t, ∑ i, c i t = ∑ i, y i t + (∑ i, θ0 i) * d t

/-- Discounted utility `∑ βᵗ u(c_t)`. -/
noncomputable def bp_detU (β : ℝ) (u : ℝ → ℝ) (c : ℕ → ℝ) : ℝ := ∑' t, β ^ t * u (c t)

/-- A consumption plan is admissible when its discounted utility converges. -/
def bp_detAdm (β : ℝ) (u : ℝ → ℝ) (c : ℕ → ℝ) : Prop := Summable (fun t => β ^ t * u (c t))

/-- The tail sum `∑_{s > t} f_s`. -/
noncomputable def bp_tail (f : ℕ → ℝ) (t : ℕ) : ℝ := ∑' k, f (k + (t + 1))

theorem bp_tail_succ (f : ℕ → ℝ) (hf : Summable f) (t : ℕ) :
    bp_tail f t = f (t + 1) + bp_tail f (t + 1) := by
  unfold bp_tail
  have hs : Summable (fun k => f (k + (t + 1))) := (summable_nat_add_iff (t + 1)).2 hf
  rw [hs.tsum_eq_zero_add]
  simp only [zero_add]
  congr 1
  refine tsum_congr (fun k => ?_)
  congr 1
  omega

theorem bp_sum_add_tail (f : ℕ → ℝ) (hf : Summable f) (t : ℕ) :
    ∑ s ∈ Finset.range (t + 1), f s + bp_tail f t = ∑' s, f s :=
  hf.sum_add_tsum_nat_add (t + 1)

theorem bp_tail_tendsto (f : ℕ → ℝ) : Tendsto (bp_tail f) atTop (𝓝 0) :=
  (tendsto_add_atTop_iff_nat 1).2 (tendsto_sum_nat_add f)

theorem bp_tail_nonneg (f : ℕ → ℝ) (hf : ∀ t, 0 ≤ f t) (t : ℕ) : 0 ≤ bp_tail f t :=
  tsum_nonneg (fun _ => hf _)

/-- The partial-sum form of the sufficiency argument: summing
`λ_t(c'_t − c_t) ≤ λ_t((p_t + d_t)(θ'_{t−1} − θ_{t−1}) − p_t(θ'_t − θ_t))` by parts. -/
theorem bp_det_partial (lam p d y : ℕ → ℝ) (θ0 : ℝ) (c θ c' θ' : ℕ → ℝ)
    (hlam : ∀ t, 0 ≤ lam t)
    (hb0 : c 0 + p 0 * θ 0 = (p 0 + d 0) * θ0 + y 0)
    (hb : ∀ t, c (t + 1) + p (t + 1) * θ (t + 1) = (p (t + 1) + d (t + 1)) * θ t + y (t + 1))
    (hb0' : c' 0 + p 0 * θ' 0 ≤ (p 0 + d 0) * θ0 + y 0)
    (hb' : ∀ t, c' (t + 1) + p (t + 1) * θ' (t + 1) ≤
      (p (t + 1) + d (t + 1)) * θ' t + y (t + 1)) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), lam t * (c' t - c t) ≤
      ∑ t ∈ Finset.range n,
        (θ' t - θ t) * (lam (t + 1) * (p (t + 1) + d (t + 1)) - lam t * p t) -
      lam n * p n * (θ' n - θ n) := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, zero_sub]
    have h : c' 0 - c 0 ≤ -(p 0 * (θ' 0 - θ 0)) := by linarith
    have := mul_le_mul_of_nonneg_left h (hlam 0)
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun t => (θ' t - θ t) *
      (lam (t + 1) * (p (t + 1) + d (t + 1)) - lam t * p t))]
    have h : c' (n + 1) - c (n + 1) ≤
        (p (n + 1) + d (n + 1)) * (θ' n - θ n) - p (n + 1) * (θ' (n + 1) - θ (n + 1)) := by
      linarith [hb n, hb' n]
    have h1 := mul_le_mul_of_nonneg_left h (hlam (n + 1))
    linear_combination ih + h1

/-- The Euler–Kuhn–Tucker sufficiency argument (used in Examples 13.6.1–13.6.2 and Exercises
13.5–13.6). Let `u'` be a supergradient of `u` on `(0, ∞)`, `λ_t = βᵗu'(c_t) ≥ 0`, let `(c, θ)`
satisfy the budget constraints with equality and `(c', θ')` satisfy them. If
`(θ'_t − θ_t)(λ_{t+1}(p_{t+1} + d_{t+1}) − λ_t p_t) ≤ 0` for all `t` (the Euler equation with
complementary slackness) and the boundary term `−λ_T p_T(θ'_T − θ_T)` is bounded by a sequence
tending to zero, then `∑ βᵗu(c'_t) ≤ ∑ βᵗu(c_t)`. -/
theorem bp_det_sufficiency (β : ℝ) (hβ : 0 ≤ β) (u u' : ℝ → ℝ)
    (hsg : ∀ x x', 0 < x → 0 < x' → u x' ≤ u x + u' x * (x' - x))
    (p d y : ℕ → ℝ) (θ0 : ℝ) (c θ c' θ' : ℕ → ℝ)
    (hc : ∀ t, 0 < c t) (hc' : ∀ t, 0 < c' t) (hu' : ∀ t, 0 ≤ u' (c t))
    (hb0 : c 0 + p 0 * θ 0 = (p 0 + d 0) * θ0 + y 0)
    (hb : ∀ t, c (t + 1) + p (t + 1) * θ (t + 1) = (p (t + 1) + d (t + 1)) * θ t + y (t + 1))
    (hb0' : c' 0 + p 0 * θ' 0 ≤ (p 0 + d 0) * θ0 + y 0)
    (hb' : ∀ t, c' (t + 1) + p (t + 1) * θ' (t + 1) ≤
      (p (t + 1) + d (t + 1)) * θ' t + y (t + 1))
    (hKT : ∀ t, (θ' t - θ t) * (β ^ (t + 1) * u' (c (t + 1)) * (p (t + 1) + d (t + 1)) -
      β ^ t * u' (c t) * p t) ≤ 0)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hbd : ∀ T, -(β ^ T * u' (c T) * p T * (θ' T - θ T)) ≤ e T)
    (hs : Summable (fun t => β ^ t * u (c t))) (hs' : Summable (fun t => β ^ t * u (c' t))) :
    ∑' t, β ^ t * u (c' t) ≤ ∑' t, β ^ t * u (c t) := by
  set lam : ℕ → ℝ := fun t => β ^ t * u' (c t) with hlam
  have hlam0 : ∀ t, 0 ≤ lam t := fun t => mul_nonneg (pow_nonneg hβ t) (hu' t)
  have hpart := bp_det_partial lam p d y θ0 c θ c' θ' hlam0 hb0 hb hb0' hb'
  have hbound : ∀ n, ∑ t ∈ Finset.range (n + 1), (β ^ t * u (c' t) - β ^ t * u (c t)) ≤ e n := by
    intro n
    have h1 : ∑ t ∈ Finset.range (n + 1), (β ^ t * u (c' t) - β ^ t * u (c t)) ≤
        ∑ t ∈ Finset.range (n + 1), lam t * (c' t - c t) := by
      refine Finset.sum_le_sum (fun t _ => ?_)
      have := mul_le_mul_of_nonneg_left (hsg (c t) (c' t) (hc t) (hc' t)) (pow_nonneg hβ t)
      simp only [hlam]
      linarith
    have h2 : ∑ t ∈ Finset.range n,
        (θ' t - θ t) * (lam (t + 1) * (p (t + 1) + d (t + 1)) - lam t * p t) ≤ 0 :=
      Finset.sum_nonpos (fun t _ => hKT t)
    have h3 := hpart n
    have h4 := hbd n
    simp only [hlam] at h3 h2
    linarith
  have hlim : Tendsto (fun n => ∑ t ∈ Finset.range (n + 1),
      (β ^ t * u (c' t) - β ^ t * u (c t))) atTop
      (𝓝 (∑' t, β ^ t * u (c' t) - ∑' t, β ^ t * u (c t))) := by
    rw [← hs'.tsum_sub hs]
    exact (tendsto_add_atTop_iff_nat 1).2 (hs'.sub hs).hasSum.tendsto_sum_nat
  have := le_of_tendsto_of_tendsto' hlim he hbound
  linarith

/-- `log` has the supergradient `1/x`: `log x' ≤ log x + (x' − x)/x`. -/
theorem bp_log_supergradient (x x' : ℝ) (hx : 0 < x) (hx' : 0 < x') :
    Real.log x' ≤ Real.log x + 1 / x * (x' - x) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx' hx)
  rw [Real.log_div hx'.ne' hx.ne'] at h
  have : x' / x - 1 = 1 / x * (x' - x) := by field_simp
  linarith

/-- The one-dimensional core of the CRRA supergradient: `(r^a − 1)/a ≤ r − 1` for `r > 0`,
`a < 1`, `a ≠ 0`. -/
theorem bp_rpow_sub_one_div_le (r a : ℝ) (hr : 0 < r) (ha1 : a < 1) (ha0 : a ≠ 0) :
    (r ^ a - 1) / a ≤ r - 1 := by
  rcases lt_or_gt_of_ne ha0 with ha | ha
  · -- `a < 0`: weighted AM–GM with weights `1/(1−a)`, `−a/(1−a)` on `r^a`, `r`
    have h1a : 0 < 1 - a := by linarith
    have hw1 : 0 ≤ 1 / (1 - a) := by positivity
    have hw2 : 0 ≤ -a / (1 - a) := div_nonneg (by linarith) h1a.le
    have hsum : 1 / (1 - a) + -a / (1 - a) = 1 := by field_simp; ring
    have hgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2
      (Real.rpow_nonneg hr.le a) hr.le hsum
    have hlhs : (r ^ a) ^ (1 / (1 - a)) * r ^ (-a / (1 - a)) = 1 := by
      rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr]
      have : a * (1 / (1 - a)) + -a / (1 - a) = 0 := by field_simp; ring
      rw [this, Real.rpow_zero]
    rw [hlhs] at hgm
    have key : 1 - a ≤ r ^ a - a * r := by
      have := mul_le_mul_of_nonneg_left hgm h1a.le
      have e1 : (1 - a) * (1 / (1 - a) * r ^ a + -a / (1 - a) * r) = r ^ a - a * r := by
        field_simp
        ring
      rw [e1] at this
      linarith
    rw [div_le_iff_of_neg ha]
    nlinarith
  · -- `0 < a < 1`: weighted AM–GM with weights `a`, `1 − a` on `r`, `1`
    have hgm := Real.geom_mean_le_arith_mean2_weighted ha.le (by linarith : 0 ≤ 1 - a) hr.le
      zero_le_one (by ring)
    rw [Real.one_rpow, mul_one] at hgm
    rw [div_le_iff₀ ha]
    nlinarith

/-- The CRRA utility `u(c) = c^{1−γ}/(1−γ)` (`γ > 0`, `γ ≠ 1`) has the supergradient `c^{−γ}`:
`u(x') ≤ u(x) + x^{−γ}(x' − x)`. -/
theorem bp_crra_supergradient (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≠ 1) (x x' : ℝ) (hx : 0 < x)
    (hx' : 0 < x') :
    x' ^ (1 - γ) / (1 - γ) ≤ x ^ (1 - γ) / (1 - γ) + x ^ (-γ) * (x' - x) := by
  set r := x' / x with hr
  have hrpos : 0 < r := div_pos hx' hx
  have hx'eq : x' = x * r := by rw [hr]; field_simp
  have ha0 : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  have hcore := bp_rpow_sub_one_div_le r (1 - γ) hrpos (by linarith) ha0
  have hxa : 0 < x ^ (1 - γ) := Real.rpow_pos_of_pos hx _
  have hmul := mul_le_mul_of_nonneg_left hcore hxa.le
  have e1 : x' ^ (1 - γ) = x ^ (1 - γ) * r ^ (1 - γ) := by
    rw [hx'eq, Real.mul_rpow hx.le hrpos.le]
  have e2 : x ^ (-γ) * (x' - x) = x ^ (1 - γ) * (r - 1) := by
    rw [hx'eq, show 1 - γ = -γ + 1 by ring, Real.rpow_add hx, Real.rpow_one]
    ring
  rw [e1, e2]
  have e3 : x ^ (1 - γ) * r ^ (1 - γ) / (1 - γ) =
      x ^ (1 - γ) / (1 - γ) + x ^ (1 - γ) * ((r ^ (1 - γ) - 1) / (1 - γ)) := by
    field_simp
    ring
  rw [e3]
  linarith

/-- The CRRA utility is strictly increasing on `(0, ∞)`. -/
theorem bp_crra_mono (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≠ 1) (x x' : ℝ) (hx : 0 < x)
    (hxx' : x ≤ x') : x ^ (1 - γ) / (1 - γ) ≤ x' ^ (1 - γ) / (1 - γ) := by
  have hsg := bp_crra_supergradient γ hγ hγ1 x' x (by linarith) hx
  have : 0 ≤ x' ^ (-γ) * (x' - x) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (by linarith)
  have h2 : x' ^ (-γ) * (x - x') ≤ 0 := by nlinarith
  linarith

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bubbles on assets in zero supply (Kocherlakota 1992)

Miao, §13.6, Example 13.6.1 (pp. 441–442), and §13.9, Exercises 13.5 and 13.6 (p. 453), in the
deterministic one-asset economy of `BPDeterministic`. `δ` is the state price deflator (the
book's `π`), `bp_natLimit δ y t = (1/π_t) ∑_{s>t} π_s y_s` the natural borrowing limit and
`bp_borrowCon B` the borrowing constraint `p_t θ_t ≥ −B_t` (13.14).

* `example_13_6_1`: if `(c, θ, p)` is an equilibrium with borrowing constraints, all initial
  holdings are zero and `π_t p_t = π_{t+1}(p_{t+1} + d_{t+1})`, then for every `η ≥ 0`,
  `(c, θ̂, p̂)` with `p̂_t = p_t + η/π_t`, `θ̂_t = θ_t p_t/p̂_t` is an equilibrium with the same
  borrowing limits. The text's derivations: `π_t/π_{t+1} = (p̂_{t+1} + d_{t+1})/p̂_t`, identical
  budget constraints (`bp_budget_transfer`), identical borrowing constraints, and identical
  transversality terms `π_t p̂_t θ̂_t = π_t p_t θ_t` (`example_13_6_1_tvc`). The bubble is `η/π_t`
  (`example_13_6_1_bubble`).
* `ex_13_5`: CRRA utilities, an asset in zero supply: for every admissible `η ≥ 0` the book's
  allocation, prices and portfolios form an equilibrium with natural borrowing constraints;
  `ex_13_5_continuum`: the prices differ for different `η`.
* `ex_13_6`: the special case `θ_{−1} = 0`, `d = 0`, `η > 0`, with the book's formulas
  `q_t = η/π_t`, `θⁱ_t = ∑_{s≤t} π_s(yⁱ_s − cⁱ_s)/(π_t q_t)` (`ex_13_6_formulas`);
  `ex_13_6_autarky`: the equilibrium with `q = 0`; `ex_13_6_pareto`: the allocation `sⁱ Y_t` is
  Pareto optimal.

**Corrections.**
* Example 13.6.1 needs `p_t > 0`. With `p_t = 0` (no dividends) the original economy has no
  trade while `p̂` permits trade, and the budget sets differ; the book's
  `p_t = (1/π_t)∑_{s>t} π_s d_s` is positive when dividends are positive.
* Exercise 13.5, initial wealth: the bracket `θⁱ_{−1}(q_0 + d_0 + η)` counts `η` twice when `q_0`
  is the equilibrium price (which already contains `η/π_0 = η`). The date-0 wealth is
  `θⁱ_{−1}(q_0 + d_0) = θⁱ_{−1}(∑_{s≥0} π_s d_s + η)`, which is what `bp_k5_wealth` uses.
* Exercise 13.5, "a continuum of equilibria indexed by `η ≥ 0`": false for large `η` when some
  agent has `θⁱ_{−1} < 0` (which zero supply and `θ_{−1} ≠ 0` force): `sⁱ(η)` falls below zero
  and the consumption `sⁱ(η) ȳ_t` is infeasible (`ex_13_5_share_counterexample`). The statement
  holds for the `η` with `sⁱ(η) > 0` for all `i` (`ex_13_5`).
* Exercise 13.5 also needs `q_t > 0` (true when `η > 0` or dividends are positive) for
  `θⁱ_t = …/(π_t q_t)` to be defined, and the present values `∑ π_t ȳ_t`, `∑ π_t d_t` finite.
-/

open Filter Topology

namespace Miao.CompleteMarkets

/-- The natural borrowing limit `B_t = (1/π_t) ∑_{s>t} π_s y_s` (Miao, p. 434). -/
noncomputable def bp_natLimit (δ y : ℕ → ℝ) (t : ℕ) : ℝ :=
  1 / δ t * bp_tail (fun s => δ s * y s) t

/-- The borrowing constraint `p_t θ_t ≥ −B_t` (Miao, (13.14)). -/
def bp_borrowCon (B : ℕ → ℝ) : ℕ → ℝ → ℝ → Prop := fun t z x => -B t ≤ z * x

/-- The CRRA utility `c^{1−γ}/(1−γ)`. -/
noncomputable def bp_crra (γ x : ℝ) : ℝ := x ^ (1 - γ) / (1 - γ)

/-- Two price systems priced by the same deflator, and two portfolios of equal value
`p_t a_t = q_t b_t`, give the same payoffs `(p_{t+1} + d_{t+1}) a_t = (q_{t+1} + d_{t+1}) b_t`. -/
theorem bp_payoff_eq (δ p q d a b : ℕ → ℝ) (hδ : ∀ t, 0 < δ t)
    (hp : ∀ t, δ t * p t = δ (t + 1) * (p (t + 1) + d (t + 1)))
    (hq : ∀ t, δ t * q t = δ (t + 1) * (q (t + 1) + d (t + 1)))
    (hval : ∀ t, p t * a t = q t * b t) (t : ℕ) :
    (p (t + 1) + d (t + 1)) * a t = (q (t + 1) + d (t + 1)) * b t := by
  have h1 : δ (t + 1) * ((p (t + 1) + d (t + 1)) * a t) =
      δ (t + 1) * ((q (t + 1) + d (t + 1)) * b t) := by
    rw [← mul_assoc, ← hp t, ← mul_assoc, ← hq t, mul_assoc, hval t, mul_assoc]
  exact mul_left_cancel₀ (hδ (t + 1)).ne' h1

/-- Miao, p. 442: with zero initial holdings and portfolios of equal value, the budget
constraints and the borrowing constraints under `p` and under `q` coincide. -/
theorem bp_budget_transfer (δ p q d y B : ℕ → ℝ) (hδ : ∀ t, 0 < δ t)
    (hp : ∀ t, δ t * p t = δ (t + 1) * (p (t + 1) + d (t + 1)))
    (hq : ∀ t, δ t * q t = δ (t + 1) * (q (t + 1) + d (t + 1)))
    (c a b : ℕ → ℝ) (hval : ∀ t, p t * a t = q t * b t) :
    bp_detBudget p d y 0 (bp_borrowCon B) c a ↔ bp_detBudget q d y 0 (bp_borrowCon B) c b := by
  have hpay := bp_payoff_eq δ p q d a b hδ hp hq hval
  unfold bp_detBudget bp_borrowCon
  simp only [mul_zero, hval, hpay]

/-- The bubbly price `p̂_t = p_t + η/π_t` of Example 13.6.1. -/
noncomputable def bp_ex1361_price (δ p : ℕ → ℝ) (η : ℝ) (t : ℕ) : ℝ := p t + η / δ t

/-- The rescaled portfolio `θ̂_t = θ_t p_t / p̂_t` of Example 13.6.1. -/
noncomputable def bp_ex1361_hold (δ p : ℕ → ℝ) (η : ℝ) (θ : ℕ → ℝ) (t : ℕ) : ℝ :=
  θ t * p t / bp_ex1361_price δ p η t

theorem bp_ex1361_price_pos (δ p : ℕ → ℝ) (η : ℝ) (hδ : ∀ t, 0 < δ t) (hp : ∀ t, 0 < p t)
    (hη : 0 ≤ η) (t : ℕ) : 0 < bp_ex1361_price δ p η t := by
  unfold bp_ex1361_price
  have := div_nonneg hη (hδ t).le
  linarith [hp t]

/-- Miao, p. 442: `p̂` is priced by the same deflator,
`π_t/π_{t+1} = (p̂_{t+1} + d_{t+1})/p̂_t`, in the form `π_t p̂_t = π_{t+1}(p̂_{t+1} + d_{t+1})`. -/
theorem example_13_6_1_prices (δ p d : ℕ → ℝ) (η : ℝ) (hδ : ∀ t, 0 < δ t)
    (hpr : ∀ t, δ t * p t = δ (t + 1) * (p (t + 1) + d (t + 1))) (t : ℕ) :
    δ t * bp_ex1361_price δ p η t =
      δ (t + 1) * (bp_ex1361_price δ p η (t + 1) + d (t + 1)) := by
  unfold bp_ex1361_price
  have h1 := (hδ t).ne'
  have h2 := (hδ (t + 1)).ne'
  have e1 : δ t * (p t + η / δ t) = δ t * p t + η := by field_simp
  have e2 : δ (t + 1) * (p (t + 1) + η / δ (t + 1) + d (t + 1)) =
      δ (t + 1) * (p (t + 1) + d (t + 1)) + η := by field_simp; ring
  rw [e1, e2, hpr t]

/-- Value preservation `p̂_t θ̂_t = p_t θ_t`. -/
theorem bp_ex1361_value (δ p : ℕ → ℝ) (η : ℝ) (hδ : ∀ t, 0 < δ t) (hp : ∀ t, 0 < p t)
    (hη : 0 ≤ η) (θ : ℕ → ℝ) (t : ℕ) :
    p t * θ t = bp_ex1361_price δ p η t * bp_ex1361_hold δ p η θ t := by
  unfold bp_ex1361_hold
  have := (bp_ex1361_price_pos δ p η hδ hp hη t).ne'
  field_simp

/-- **Example 13.6.1** (Kocherlakota 1992, Miao, pp. 441–442). If `(c, θ, p)` is an equilibrium
with borrowing constraints `p_tθⁱ_t ≥ −Bⁱ_t`, zero initial holdings, a positive price priced by
the deflator `π`, then for every `η ≥ 0` the consumption `c`, the portfolios `θ̂ = θp/p̂` and the
prices `p̂ = p + η/π` form an equilibrium with the same borrowing limits. -/
theorem example_13_6_1 {ι : Type*} [Fintype ι] (U : ι → (ℕ → ℝ) → ℝ)
    (adm : ι → (ℕ → ℝ) → Prop) (y : ι → ℕ → ℝ) (d : ℕ → ℝ) (B : ι → ℕ → ℝ)
    (c θ : ι → ℕ → ℝ) (p δ : ℕ → ℝ) (η : ℝ)
    (hE : BPDetEqm U adm y d (fun _ => 0) (fun i => bp_borrowCon (B i)) c θ p)
    (hδ : ∀ t, 0 < δ t) (hp : ∀ t, 0 < p t)
    (hpr : ∀ t, δ t * p t = δ (t + 1) * (p (t + 1) + d (t + 1))) (hη : 0 ≤ η) :
    BPDetEqm U adm y d (fun _ => 0) (fun i => bp_borrowCon (B i)) c
      (fun i => bp_ex1361_hold δ p η (θ i)) (bp_ex1361_price δ p η) := by
  have hq := example_13_6_1_prices δ p d η hδ hpr
  have hqpos := bp_ex1361_price_pos δ p η hδ hp hη
  refine ⟨fun i => ?_, hE.adm_self, fun i c' θ' hb hadm => ?_, fun t => ?_, fun t => ?_⟩
  · exact (bp_budget_transfer δ p _ d (y i) (B i) hδ hpr hq (c i) (θ i) _
      (bp_ex1361_value δ p η hδ hp hη (θ i))).1 (hE.budget i)
  · -- pull the deviation back to the original prices
    set θo : ℕ → ℝ := fun t => θ' t * bp_ex1361_price δ p η t / p t with hθo
    have hval : ∀ t, p t * θo t = bp_ex1361_price δ p η t * θ' t := by
      intro t
      simp only [hθo]
      field_simp [(hp t).ne']
    exact hE.optimal i c' θo
      ((bp_budget_transfer δ p _ d (y i) (B i) hδ hpr hq c' θo θ' hval).2 hb) hadm
  · have h0 : ∑ i, θ i t = 0 := by rw [hE.clear_assets t]; simp
    simp only [Finset.sum_const_zero]
    unfold bp_ex1361_hold
    rw [← Finset.sum_div, ← Finset.sum_mul, h0]
    simp
  · exact hE.clear_goods t

/-- Miao, p. 442: the transversality terms agree, `π_t p̂_t θ̂_t = π_t p_t θ_t`, so
`lim π_t p̂_t θ̂_t = lim π_t p_t θ_t = 0` whenever the original condition holds. -/
theorem example_13_6_1_tvc (δ p θ : ℕ → ℝ) (η : ℝ) (hδ : ∀ t, 0 < δ t) (hp : ∀ t, 0 < p t)
    (hη : 0 ≤ η) (htvc : Tendsto (fun t => δ t * p t * θ t) atTop (𝓝 0)) :
    (∀ t, δ t * bp_ex1361_price δ p η t * bp_ex1361_hold δ p η θ t = δ t * p t * θ t) ∧
      Tendsto (fun t => δ t * bp_ex1361_price δ p η t * bp_ex1361_hold δ p η θ t) atTop
        (𝓝 0) := by
  have h : ∀ t, δ t * bp_ex1361_price δ p η t * bp_ex1361_hold δ p η θ t = δ t * p t * θ t :=
    fun t => by rw [mul_assoc, ← bp_ex1361_value δ p η hδ hp hη θ t, mul_assoc]
  refine ⟨h, ?_⟩
  simpa only [h] using htvc

/-- Miao, p. 442: when `p_t = (1/π_t) ∑_{s>t} π_s d_s` is the fundamental value, the bubble on
`p̂` is `b_t = η/π_t`. -/
theorem example_13_6_1_bubble (δ p d : ℕ → ℝ) (η : ℝ)
    (hfund : ∀ t, p t = 1 / δ t * bp_tail (fun s => δ s * d s) t) (t : ℕ) :
    bp_ex1361_price δ p η t - 1 / δ t * bp_tail (fun s => δ s * d s) t = η / δ t := by
  unfold bp_ex1361_price
  rw [hfund t]
  ring

/-! ### Exercises 13.5 and 13.6 -/

/-- Aggregate endowment `ȳ_t = ∑ᵢ yⁱ_t`. -/
def bp_k5_Y {ι : Type*} [Fintype ι] (y : ι → ℕ → ℝ) (t : ℕ) : ℝ := ∑ i, y i t

/-- The state price deflator `π_t = βᵗ (ȳ_t/ȳ_0)^{−γ}` of Exercise 13.5. -/
noncomputable def bp_k5_defl {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (bp_k5_Y y t / bp_k5_Y y 0) ^ (-γ)

/-- The stock price `q_t = (1/π_t) ∑_{s>t} π_s d_s + η/π_t` of Exercise 13.5. -/
noncomputable def bp_k5_price {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (η : ℝ) (t : ℕ) : ℝ :=
  (bp_tail (fun s => bp_k5_defl β γ y s * d s) t + η) / bp_k5_defl β γ y t

/-- Agent `i`'s wealth `∑ π_t yⁱ_t + θⁱ_{−1}(q_0 + d_0) = ∑ π_t yⁱ_t + θⁱ_{−1}(∑ π_t d_t + η)`. -/
noncomputable def bp_k5_wealth {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (θ0 : ι → ℝ) (η : ℝ) (i : ι) : ℝ :=
  ∑' t, bp_k5_defl β γ y t * y i t + θ0 i * (∑' t, bp_k5_defl β γ y t * d t + η)

/-- The consumption share `sⁱ(η)`. -/
noncomputable def bp_k5_share {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (θ0 : ι → ℝ) (η : ℝ) (i : ι) : ℝ :=
  bp_k5_wealth β γ y d θ0 η i / ∑' t, bp_k5_defl β γ y t * bp_k5_Y y t

/-- Consumption `cⁱ_t = sⁱ(η) ȳ_t`. -/
noncomputable def bp_k5_cons {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (θ0 : ι → ℝ) (η : ℝ) (i : ι) (t : ℕ) : ℝ :=
  bp_k5_share β γ y d θ0 η i * bp_k5_Y y t

/-- The numerator `π_t q_t θⁱ_t = ∑_{s≤t} π_s(yⁱ_s − cⁱ_s) + θⁱ_{−1}(∑ π_s d_s + η)`. -/
noncomputable def bp_k5_value {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (θ0 : ι → ℝ) (η : ℝ) (i : ι) (t : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (t + 1), bp_k5_defl β γ y s * (y i s - bp_k5_cons β γ y d θ0 η i s) +
    θ0 i * (∑' s, bp_k5_defl β γ y s * d s + η)

/-- The portfolio `θⁱ_t` of Exercise 13.5. -/
noncomputable def bp_k5_hold {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (θ0 : ι → ℝ) (η : ℝ) (i : ι) (t : ℕ) : ℝ :=
  bp_k5_value β γ y d θ0 η i t / (bp_k5_defl β γ y t * bp_k5_price β γ y d η t)

theorem bp_k5_Y_pos {ι : Type*} [Fintype ι] [Nonempty ι] (y : ι → ℕ → ℝ)
    (hy : ∀ i t, 0 < y i t) (t : ℕ) : 0 < bp_k5_Y y t :=
  Finset.sum_pos (fun i _ => hy i t) Finset.univ_nonempty

theorem bp_k5_defl_pos {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (t : ℕ) : 0 < bp_k5_defl β γ y t := by
  unfold bp_k5_defl
  have := bp_k5_Y_pos y hy t
  have := bp_k5_Y_pos y hy 0
  positivity

theorem bp_k5_defl_zero {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (y : ι → ℕ → ℝ)
    (hy : ∀ i t, 0 < y i t) : bp_k5_defl β γ y 0 = 1 := by
  unfold bp_k5_defl
  rw [div_self (bp_k5_Y_pos y hy 0).ne', Real.one_rpow, pow_zero, one_mul]

/-- The marginal utility identity `βᵗ (sȳ_t)^{−γ} = (sȳ_0)^{−γ} π_t`. -/
theorem bp_k5_marginal {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (y : ι → ℕ → ℝ)
    (hy : ∀ i t, 0 < y i t) (s : ℝ) (hs : 0 < s) (t : ℕ) :
    β ^ t * (s * bp_k5_Y y t) ^ (-γ) = (s * bp_k5_Y y 0) ^ (-γ) * bp_k5_defl β γ y t := by
  unfold bp_k5_defl
  have h0 := bp_k5_Y_pos y hy 0
  have ht := bp_k5_Y_pos y hy t
  rw [Real.mul_rpow hs.le ht.le, Real.mul_rpow hs.le h0.le, Real.div_rpow ht.le h0.le]
  have : 0 < bp_k5_Y y 0 ^ (-γ) := Real.rpow_pos_of_pos h0 _
  field_simp

/-- The pricing equation `π_t q_t = π_{t+1}(q_{t+1} + d_{t+1})`. -/
theorem bp_k5_prices {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ)
    (hD : Summable (fun t => bp_k5_defl β γ y t * d t)) (η : ℝ) (t : ℕ) :
    bp_k5_defl β γ y t * bp_k5_price β γ y d η t =
      bp_k5_defl β γ y (t + 1) * (bp_k5_price β γ y d η (t + 1) + d (t + 1)) := by
  unfold bp_k5_price
  have h1 := (bp_k5_defl_pos β γ hβ y hy t).ne'
  have h2 := (bp_k5_defl_pos β γ hβ y hy (t + 1)).ne'
  rw [bp_tail_succ _ hD t]
  field_simp
  ring

theorem bp_k5_summable_y {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) (i : ι) :
    Summable (fun t => bp_k5_defl β γ y t * y i t) := by
  refine Summable.of_nonneg_of_le (fun t => (mul_pos (bp_k5_defl_pos β γ hβ y hy t)
    (hy i t)).le) (fun t => ?_) hY
  refine mul_le_mul_of_nonneg_left ?_ (bp_k5_defl_pos β γ hβ y hy t).le
  exact Finset.single_le_sum (f := fun k => y k t) (fun k _ => (hy k t).le) (Finset.mem_univ i)

theorem bp_k5_pv_pos {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) :
    0 < ∑' t, bp_k5_defl β γ y t * bp_k5_Y y t :=
  hY.tsum_pos (fun t => (mul_pos (bp_k5_defl_pos β γ hβ y hy t) (bp_k5_Y_pos y hy t)).le) 0
    (mul_pos (bp_k5_defl_pos β γ hβ y hy 0) (bp_k5_Y_pos y hy 0))

/-- With zero supply, the shares sum to one. -/
theorem bp_k5_share_sum {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ) (θ0 : ι → ℝ) (hθ0 : ∑ i, θ0 i = 0)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) (η : ℝ) :
    ∑ i, bp_k5_share β γ y d θ0 η i = 1 := by
  unfold bp_k5_share bp_k5_wealth
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, hθ0, zero_mul, add_zero]
  rw [← Summable.tsum_finsetSum (fun i _ => bp_k5_summable_y β γ hβ y hy hY i)]
  have : (fun t => ∑ i, bp_k5_defl β γ y t * y i t) =
      fun t => bp_k5_defl β γ y t * bp_k5_Y y t := by
    funext t
    rw [bp_k5_Y, Finset.mul_sum]
  rw [this, div_self (bp_k5_pv_pos β γ hβ y hy hY).ne']

/-- The present value of agent `i`'s consumption is his wealth. -/
theorem bp_k5_pv_cons {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ) (θ0 : ι → ℝ)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) (η : ℝ) (i : ι) :
    HasSum (fun t => bp_k5_defl β γ y t * bp_k5_cons β γ y d θ0 η i t)
      (bp_k5_wealth β γ y d θ0 η i) := by
  have h := hY.hasSum.mul_left (bp_k5_share β γ y d θ0 η i)
  have hw : bp_k5_share β γ y d θ0 η i * ∑' t, bp_k5_defl β γ y t * bp_k5_Y y t =
      bp_k5_wealth β γ y d θ0 η i := by
    unfold bp_k5_share
    field_simp [(bp_k5_pv_pos β γ hβ y hy hY).ne']
  rw [hw] at h
  convert h using 1
  funext t
  unfold bp_k5_cons
  ring

/-- `π_t q_t θⁱ_t + ∑_{s>t} π_s yⁱ_s = ∑_{s>t} π_s cⁱ_s`: the value of the portfolio plus human
wealth is the value of future consumption. -/
theorem bp_k5_value_tail {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ) (θ0 : ι → ℝ)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) (η : ℝ) (i : ι) (t : ℕ) :
    bp_k5_value β γ y d θ0 η i t + bp_tail (fun s => bp_k5_defl β γ y s * y i s) t =
      bp_tail (fun s => bp_k5_defl β γ y s * bp_k5_cons β γ y d θ0 η i s) t := by
  have hc := bp_k5_pv_cons β γ hβ y hy d θ0 hY η i
  have h1 := bp_sum_add_tail _ hc.summable t
  have h2 := bp_sum_add_tail _ (bp_k5_summable_y β γ hβ y hy hY i) t
  rw [hc.tsum_eq] at h1
  unfold bp_k5_wealth at h1
  unfold bp_k5_value
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

/-- **Exercise 13.5** (Kocherlakota 1992, Miao, p. 453). CRRA utilities `c^{1−γ}/(1−γ)`, one
stock in zero supply. For every `η ≥ 0` such that all shares `sⁱ(η)` are positive and the prices
`q_t` are positive, the consumption `cⁱ_t = sⁱ(η)ȳ_t`, the deflator `π_t = βᵗ(ȳ_t/ȳ_0)^{−γ}`, the
price `q_t = (1/π_t)∑_{s>t} π_s d_s + η/π_t` and the portfolios `θⁱ_t` form an equilibrium with
natural borrowing constraints. -/
theorem ex_13_5 {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ1 : γ ≠ 1) (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ) (θ0 : ι → ℝ)
    (hθ0 : ∑ i, θ0 i = 0) (η : ℝ)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t))
    (hD : Summable (fun t => bp_k5_defl β γ y t * d t))
    (hs : ∀ i, 0 < bp_k5_share β γ y d θ0 η i) (hq : ∀ t, 0 < bp_k5_price β γ y d η t) :
    BPDetEqm (fun _ => bp_detU β (bp_crra γ)) (fun _ => bp_detAdm β (bp_crra γ)) y d θ0
      (fun i => bp_borrowCon (bp_natLimit (bp_k5_defl β γ y) (y i)))
      (bp_k5_cons β γ y d θ0 η) (bp_k5_hold β γ y d θ0 η) (bp_k5_price β γ y d η) := by
  set δ := bp_k5_defl β γ y with hδdef
  set q := bp_k5_price β γ y d η with hqdef
  set c := bp_k5_cons β γ y d θ0 η with hcdef
  set θ := bp_k5_hold β γ y d θ0 η with hθdef
  set V := bp_k5_value β γ y d θ0 η with hVdef
  have hδ : ∀ t, 0 < δ t := bp_k5_defl_pos β γ hβ y hy
  have hδ0 : δ 0 = 1 := bp_k5_defl_zero β γ y hy
  have hpr : ∀ t, δ t * q t = δ (t + 1) * (q (t + 1) + d (t + 1)) :=
    bp_k5_prices β γ hβ y hy d hD η
  have hcpos : ∀ i t, 0 < c i t := fun i t => mul_pos (hs i) (bp_k5_Y_pos y hy t)
  -- portfolio value
  have hqθ : ∀ i t, δ t * q t * θ i t = V i t := by
    intro i t
    have := (mul_pos (hδ t) (hq t)).ne'
    change δ t * q t * (V i t / (δ t * q t)) = V i t
    rw [mul_comm]
    exact div_mul_cancel₀ (V i t) this
  have hD0 : ∑' s, δ s * d s = d 0 + bp_tail (fun s => δ s * d s) 0 := by
    have := bp_sum_add_tail _ hD 0
    simp only [zero_add, Finset.sum_range_one] at this
    rw [hδ0, one_mul] at this
    linarith
  -- budget constraints hold with equality
  have hb0 : ∀ i, c i 0 + q 0 * θ i 0 = (q 0 + d 0) * θ0 i + y i 0 := by
    intro i
    have h := hqθ i 0
    rw [hδ0, one_mul] at h
    rw [h]
    simp only [hVdef, bp_k5_value, zero_add, Finset.sum_range_one]
    simp only [hqdef, bp_k5_price, ← hδdef, hδ0, div_one]
    rw [hD0]
    ring
  have hb : ∀ i t, c i (t + 1) + q (t + 1) * θ i (t + 1) =
      (q (t + 1) + d (t + 1)) * θ i t + y i (t + 1) := by
    intro i t
    have hne := (hδ (t + 1)).ne'
    have h1 : δ (t + 1) * (c i (t + 1) + q (t + 1) * θ i (t + 1)) =
        δ (t + 1) * ((q (t + 1) + d (t + 1)) * θ i t + y i (t + 1)) := by
      have e1 : δ (t + 1) * (q (t + 1) + d (t + 1)) * θ i t = V i t := by
        rw [← hpr t]
        exact hqθ i t
      have e2 : V i (t + 1) = V i t + δ (t + 1) * (y i (t + 1) - c i (t + 1)) := by
        simp only [hVdef, bp_k5_value, Finset.sum_range_succ]
        ring
      have e3 := hqθ i (t + 1)
      calc δ (t + 1) * (c i (t + 1) + q (t + 1) * θ i (t + 1))
          = δ (t + 1) * c i (t + 1) + δ (t + 1) * q (t + 1) * θ i (t + 1) := by ring
        _ = δ (t + 1) * c i (t + 1) + V i (t + 1) := by rw [e3]
        _ = V i t + δ (t + 1) * y i (t + 1) := by rw [e2]; ring
        _ = δ (t + 1) * ((q (t + 1) + d (t + 1)) * θ i t + y i (t + 1)) := by
          rw [← e1]; ring
    exact mul_left_cancel₀ hne h1
  -- the borrowing constraint, in deflated form
  have hcon_iff : ∀ i t (x : ℝ), bp_borrowCon (bp_natLimit δ (y i)) t (q t) x ↔
      -bp_tail (fun s => δ s * y i s) t ≤ δ t * q t * x := by
    intro i t x
    unfold bp_borrowCon bp_natLimit
    have hd := hδ t
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_left h hd.le
      have e : δ t * -(1 / δ t * bp_tail (fun s => δ s * y i s) t) =
          -bp_tail (fun s => δ s * y i s) t := by field_simp
      rw [e] at this
      linarith
    · intro h
      have e : -(1 / δ t * bp_tail (fun s => δ s * y i s) t) =
          (1 / δ t) * (-bp_tail (fun s => δ s * y i s) t) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left h (one_div_nonneg.2 hd.le)
      have e2 : 1 / δ t * (δ t * q t * x) = q t * x := by field_simp
      linarith
  have hVtail : ∀ i t, V i t + bp_tail (fun s => δ s * y i s) t =
      bp_tail (fun s => δ s * c i s) t :=
    bp_k5_value_tail β γ hβ y hy d θ0 hY η
  have hbudget : ∀ i, bp_detBudget q d (y i) (θ0 i)
      (bp_borrowCon (bp_natLimit δ (y i))) (c i) (θ i) := by
    intro i
    refine ⟨hcpos i, (hb0 i).le, fun t => (hb i t).le, fun t => ?_⟩
    rw [hcon_iff, hqθ, ← sub_nonneg]
    have := hVtail i t
    have := bp_tail_nonneg (fun s => δ s * c i s) (fun s => (mul_pos (hδ s) (hcpos i s)).le) t
    linarith
  -- utility of `c` converges
  have hadm : ∀ i, bp_detAdm β (bp_crra γ) (c i) := by
    intro i
    unfold bp_detAdm bp_crra
    have hsi := hs i
    have hY0 := bp_k5_Y_pos y hy 0
    have key : ∀ t, β ^ t * (c i t ^ (1 - γ) / (1 - γ)) =
        (bp_k5_share β γ y d θ0 η i ^ (1 - γ) * bp_k5_Y y 0 ^ (-γ) / (1 - γ)) *
          (δ t * bp_k5_Y y t) := by
      intro t
      have hYt := bp_k5_Y_pos y hy t
      simp only [hcdef, bp_k5_cons, hδdef, bp_k5_defl]
      rw [Real.mul_rpow hsi.le hYt.le, Real.div_rpow hYt.le hY0.le,
        show 1 - γ = -γ + 1 by ring, Real.rpow_add hYt, Real.rpow_one]
      have : 0 < bp_k5_Y y 0 ^ (-γ) := Real.rpow_pos_of_pos hY0 _
      have : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
      field_simp
    simp only [key]
    exact hY.mul_left _
  refine ⟨hbudget, hadm, fun i c' θ' hb' hadm' => ?_, fun t => ?_, fun t => ?_⟩
  · -- optimality via the sufficiency argument with `λ_t = κ π_t`
    obtain ⟨hc', hb0', hbs', hcon'⟩ := hb'
    set κ := (bp_k5_share β γ y d θ0 η i * bp_k5_Y y 0) ^ (-γ) with hκ
    have hκpos : 0 < κ := Real.rpow_pos_of_pos (mul_pos (hs i) (bp_k5_Y_pos y hy 0)) _
    have hlam : ∀ t, β ^ t * c i t ^ (-γ) = κ * δ t := fun t =>
      bp_k5_marginal β γ y hy _ (hs i) t
    refine bp_det_sufficiency β hβ.le (bp_crra γ) (fun x => x ^ (-γ))
      (fun x x' hx hx' => bp_crra_supergradient γ hγ hγ1 x x' hx hx') q d (y i) (θ0 i)
      (c i) (θ i) c' θ' (hcpos i) hc' (fun t => Real.rpow_nonneg (hcpos i t).le _) (hb0 i)
      (hb i) hb0' hbs' (fun t => ?_) (fun T => κ * bp_tail (fun s => δ s * c i s) T)
      (by simpa using (bp_tail_tendsto (fun s => δ s * c i s)).const_mul κ) (fun T => ?_)
      (hadm i) hadm'
    · simp only [hlam]
      rw [mul_assoc, ← hpr t]
      ring_nf
      exact le_rfl
    · simp only [hlam]
      have h1 := (hcon_iff i T (θ' T)).1 (hcon' T)
      have h2 := hqθ i T
      have h3 := hVtail i T
      have e : -(κ * δ T * q T * (θ' T - θ i T)) =
          κ * (δ T * q T * θ i T - δ T * q T * θ' T) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ hκpos.le
      linarith
  · -- asset market clearing
    have hcsum : ∀ s, ∑ i, c i s = bp_k5_Y y s := by
      intro s
      simp only [hcdef, bp_k5_cons]
      rw [← Finset.sum_mul, bp_k5_share_sum β γ hβ y hy d θ0 hθ0 hY η, one_mul]
    have hVsum : ∑ i, V i t = 0 := by
      simp only [hVdef, bp_k5_value, Finset.sum_add_distrib]
      rw [Finset.sum_comm, ← Finset.sum_mul, hθ0, zero_mul, add_zero]
      refine Finset.sum_eq_zero (fun s _ => ?_)
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← hcdef, hcsum s]
      simp [bp_k5_Y]
    simp only [hθdef, bp_k5_hold]
    rw [← Finset.sum_div, ← hVdef, hVsum, hθ0, zero_div]
  · simp only [hcdef, bp_k5_cons]
    rw [← Finset.sum_mul, bp_k5_share_sum β γ hβ y hy d θ0 hθ0 hY η, one_mul, hθ0, zero_mul,
      add_zero]
    rfl

/-- Exercise 13.5: the equilibria are distinct, `q_t(η) ≠ q_t(η')` for `η ≠ η'`. -/
theorem ex_13_5_continuum {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ) (η η' : ℝ) (hne : η ≠ η') (t : ℕ) :
    bp_k5_price β γ y d η t ≠ bp_k5_price β γ y d η' t := by
  unfold bp_k5_price
  intro h
  have hd := (bp_k5_defl_pos β γ hβ y hy t).ne'
  rw [div_left_inj' hd] at h
  exact hne (by linarith)

/-- Counterexample to Exercise 13.5 for all `η ≥ 0`: two agents with endowments `1`, `β = 1/2`,
`γ = 2`, no dividends and `θ_{−1} = (1, −1)`. At `η = 3` agent 2's share is negative, so his
consumption `s²(3) ȳ_t` is negative: no equilibrium. -/
theorem ex_13_5_share_counterexample :
    bp_k5_share (ι := Bool) (1 / 2) 2 (fun _ _ => 1) (fun _ => 0)
      (fun i => if i then 1 else -1) 3 false < 0 := by
  have hdefl : ∀ t, bp_k5_defl (ι := Bool) (1 / 2) 2 (fun _ _ => 1) t = (1 / 2) ^ t := by
    intro t
    simp [bp_k5_defl, bp_k5_Y]
  have hY : ∀ t, bp_k5_Y (ι := Bool) (fun _ _ => (1 : ℝ)) t = 2 := by
    intro t
    simp [bp_k5_Y]
  have hg : ∑' t : ℕ, ((1 : ℝ) / 2) ^ t = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  unfold bp_k5_share bp_k5_wealth
  simp only [hdefl, hY, mul_one, mul_zero, tsum_zero, zero_add]
  rw [tsum_mul_right, hg]
  norm_num

/-- **Exercise 13.6** (Kocherlakota 1992, Miao, p. 453). With `θⁱ_{−1} = 0` and `d = 0`, for
every `η > 0` the allocation `cⁱ_t = sⁱ Y_t`, the price `q_t = η/π_t` and the portfolios
`θⁱ_t = ∑_{s≤t} π_s(yⁱ_s − cⁱ_s)/(π_t q_t)` (`ex_13_6_formulas`) form an equilibrium. -/
theorem ex_13_6 {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ1 : γ ≠ 1) (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (η : ℝ) (hη : 0 < η)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) :
    BPDetEqm (fun _ => bp_detU β (bp_crra γ)) (fun _ => bp_detAdm β (bp_crra γ)) y
      (fun _ => 0) (fun _ => 0)
      (fun i => bp_borrowCon (bp_natLimit (bp_k5_defl β γ y) (y i)))
      (bp_k5_cons β γ y (fun _ => 0) (fun _ => 0) η)
      (bp_k5_hold β γ y (fun _ => 0) (fun _ => 0) η) (bp_k5_price β γ y (fun _ => 0) η) := by
  refine ex_13_5 β γ hβ hγ hγ1 y hy _ _ (by simp) η hY (by simp)
    (fun i => ?_) (fun t => ?_)
  · unfold bp_k5_share bp_k5_wealth
    simp only [zero_mul, add_zero]
    refine div_pos ?_ (bp_k5_pv_pos β γ hβ y hy hY)
    exact (bp_k5_summable_y β γ hβ y hy hY i).tsum_pos
      (fun t => (mul_pos (bp_k5_defl_pos β γ hβ y hy t) (hy i t)).le) 0
      (mul_pos (bp_k5_defl_pos β γ hβ y hy 0) (hy i 0))
  · unfold bp_k5_price bp_tail
    simp only [mul_zero, tsum_zero, zero_add]
    exact div_pos hη (bp_k5_defl_pos β γ hβ y hy t)

/-- Exercise 13.6: the objects of `ex_13_6` are the book's: `q_t = η/π_t`,
`sⁱ = ∑ π_t yⁱ_t / ∑ π_t Y_t` and `θⁱ_t = ∑_{s≤t} π_s(yⁱ_s − cⁱ_s)/(π_t q_t)`. -/
theorem ex_13_6_formulas {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (η : ℝ)
    (i : ι) (t : ℕ) :
    bp_k5_price β γ y (fun _ => 0) η t = η / bp_k5_defl β γ y t ∧
      bp_k5_share β γ y (fun _ => 0) (fun _ => 0) η i =
        (∑' t, bp_k5_defl β γ y t * y i t) / ∑' t, bp_k5_defl β γ y t * bp_k5_Y y t ∧
      bp_k5_hold β γ y (fun _ => 0) (fun _ => 0) η i t =
        (∑ s ∈ Finset.range (t + 1), bp_k5_defl β γ y s *
          (y i s - bp_k5_cons β γ y (fun _ => 0) (fun _ => 0) η i s)) /
          (bp_k5_defl β γ y t * bp_k5_price β γ y (fun _ => 0) η t) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold bp_k5_price bp_tail
    simp
  · unfold bp_k5_share bp_k5_wealth
    simp
  · unfold bp_k5_hold bp_k5_value
    simp

/-- Exercise 13.6: "there is an equilibrium in which `q_t = 0`": autarky `cⁱ = yⁱ`, `θⁱ = 0`
(assuming each endowment has finite utility). -/
theorem ex_13_6_autarky {ι : Type*} [Fintype ι] (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ1 : γ ≠ 1) (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (δ : ℕ → ℝ) (hδ : ∀ t, 0 < δ t)
    (hU : ∀ i, bp_detAdm β (bp_crra γ) (y i)) :
    BPDetEqm (fun _ => bp_detU β (bp_crra γ)) (fun _ => bp_detAdm β (bp_crra γ)) y
      (fun _ => 0) (fun _ => 0) (fun i => bp_borrowCon (bp_natLimit δ (y i))) y
      (fun _ _ => 0) (fun _ => 0) := by
  have hB : ∀ i t, 0 ≤ bp_natLimit δ (y i) t := fun i t =>
    mul_nonneg (one_div_nonneg.2 (hδ t).le)
      (bp_tail_nonneg _ (fun s => (mul_pos (hδ s) (hy i s)).le) t)
  refine ⟨fun i => ⟨hy i, by simp, fun t => by simp, fun t => ?_⟩, hU,
    fun i c' θ' hb hadm => ?_, fun t => by simp, fun t => by simp⟩
  · unfold bp_borrowCon
    simp only [mul_zero, neg_nonpos]
    exact hB i t
  · obtain ⟨hc', hb0, hbs, -⟩ := hb
    have hle : ∀ t, c' t ≤ y i t := by
      intro t
      cases t with
      | zero => simpa using hb0
      | succ t => simpa using hbs t
    unfold bp_detU
    refine Summable.tsum_le_tsum (fun t => ?_) hadm (hU i)
    exact mul_le_mul_of_nonneg_left (bp_crra_mono γ hγ hγ1 _ _ (hc' t) (hle t))
      (pow_nonneg hβ.le t)

/-- Pareto optimality in the deterministic economy: no feasible allocation with positive,
admissible consumption makes everyone weakly better off and someone strictly better off. -/
def bp_detParetoOptimal {ι : Type*} [Fintype ι] (U : ι → (ℕ → ℝ) → ℝ)
    (adm : ι → (ℕ → ℝ) → Prop) (Y : ℕ → ℝ) (c : ι → ℕ → ℝ) : Prop :=
  ¬ ∃ x : ι → ℕ → ℝ, (∀ i t, 0 < x i t) ∧ (∀ t, ∑ i, x i t ≤ Y t) ∧ (∀ i, adm i (x i)) ∧
    (∀ i, U i (c i) ≤ U i (x i)) ∧ ∃ i, U i (c i) < U i (x i)

/-- Exercise 13.6: "the consumption allocation is Pareto optimal". With CRRA utilities, any
allocation `cⁱ_t = sⁱ Y_t` with positive shares summing to one (in particular that of `ex_13_6`)
is Pareto optimal; the Negishi weights are `(sⁱ)^γ`. -/
theorem ex_13_6_pareto {ι : Type*} [Fintype ι] (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ1 : γ ≠ 1) (Y : ℕ → ℝ) (hYpos : ∀ t, 0 < Y t) (s : ι → ℝ) (hs : ∀ i, 0 < s i)
    (hs1 : ∑ i, s i = 1) (hadm : ∀ i, bp_detAdm β (bp_crra γ) (fun t => s i * Y t)) :
    bp_detParetoOptimal (fun _ => bp_detU β (bp_crra γ)) (fun _ => bp_detAdm β (bp_crra γ)) Y
      (fun i t => s i * Y t) := by
  rintro ⟨x, hx, hfeas, hxadm, hge, i₀, hgt⟩
  set w : ι → ℝ := fun i => s i ^ γ with hw
  have hwpos : ∀ i, 0 < w i := fun i => Real.rpow_pos_of_pos (hs i) _
  -- weighted per-period gain is nonpositive
  have hper : ∀ t, ∑ i, w i * (β ^ t * bp_crra γ (x i t) - β ^ t * bp_crra γ (s i * Y t)) ≤ 0 := by
    intro t
    have hYt := hYpos t
    have h1 : ∀ i, w i * (β ^ t * bp_crra γ (x i t) - β ^ t * bp_crra γ (s i * Y t)) ≤
        β ^ t * Y t ^ (-γ) * (x i t - s i * Y t) := by
      intro i
      have hsg := bp_crra_supergradient γ hγ hγ1 (s i * Y t) (x i t)
        (mul_pos (hs i) hYt) (hx i t)
      have hwm : w i * (s i * Y t) ^ (-γ) = Y t ^ (-γ) := by
        rw [hw, Real.mul_rpow (hs i).le hYt.le, ← mul_assoc, ← Real.rpow_add (hs i)]
        simp
      have e : w i * (β ^ t * bp_crra γ (x i t) - β ^ t * bp_crra γ (s i * Y t)) =
          w i * β ^ t * (bp_crra γ (x i t) - bp_crra γ (s i * Y t)) := by ring
      rw [e]
      have h2 : bp_crra γ (x i t) - bp_crra γ (s i * Y t) ≤
          (s i * Y t) ^ (-γ) * (x i t - s i * Y t) := by
        unfold bp_crra
        linarith
      have h3 := mul_le_mul_of_nonneg_left h2
        (mul_nonneg (hwpos i).le (pow_nonneg hβ.le t))
      calc w i * β ^ t * (bp_crra γ (x i t) - bp_crra γ (s i * Y t))
          ≤ w i * β ^ t * ((s i * Y t) ^ (-γ) * (x i t - s i * Y t)) := h3
        _ = β ^ t * (w i * (s i * Y t) ^ (-γ)) * (x i t - s i * Y t) := by ring
        _ = β ^ t * Y t ^ (-γ) * (x i t - s i * Y t) := by rw [hwm]
    have h4 : ∑ i, β ^ t * Y t ^ (-γ) * (x i t - s i * Y t) ≤ 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, hs1, one_mul]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (pow_nonneg hβ.le t) (Real.rpow_nonneg hYt.le _)) (by linarith [hfeas t])
    exact (Finset.sum_le_sum (fun i _ => h1 i)).trans h4
  have hsum : ∀ i, Summable (fun t => w i * (β ^ t * bp_crra γ (x i t) -
      β ^ t * bp_crra γ (s i * Y t))) := fun i => ((hxadm i).sub (hadm i)).mul_left _
  have htot : ∑ i, w i * (bp_detU β (bp_crra γ) (x i) -
      bp_detU β (bp_crra γ) (fun t => s i * Y t)) ≤ 0 := by
    have e : ∀ i, w i * (bp_detU β (bp_crra γ) (x i) -
        bp_detU β (bp_crra γ) (fun t => s i * Y t)) =
        ∑' t, w i * (β ^ t * bp_crra γ (x i t) - β ^ t * bp_crra γ (s i * Y t)) := by
      intro i
      unfold bp_detU
      rw [← (hxadm i).tsum_sub (hadm i), (((hxadm i).sub (hadm i))).tsum_mul_left]
    simp only [e]
    rw [← Summable.tsum_finsetSum (fun i _ => hsum i)]
    exact tsum_nonpos hper
  have hpos : 0 < ∑ i, w i * (bp_detU β (bp_crra γ) (x i) -
      bp_detU β (bp_crra γ) (fun t => s i * Y t)) := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ w i * (bp_detU β (bp_crra γ) (x i) -
        bp_detU β (bp_crra γ) (fun t => s i * Y t)) :=
      fun i _ => mul_nonneg (hwpos i).le (by linarith [hge i])
    exact lt_of_lt_of_le (mul_pos (hwpos i₀) (by linarith))
      (Finset.single_le_sum hnn (Finset.mem_univ i₀))
  linarith

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive competitive equilibrium with debt constraints

Miao, §13.7, pp. 444–446. Shocks follow a Markov chain `P` on the finite set `S` (the history
probabilities are `bp_markovPr`, with the factorisation `eq_13_7_markov` in `BPTree`).
Endowments `yⁱ(s)`, dividends `d(s) ∈ ℝ^J` and debt limits `D̄ⁱ(s)` are time-invariant
functions of the current shock, the state is `(w, s)` with `w ∈ ℝ^I` the wealth distribution,
the price function is `p(w, s)` and the wealth distribution evolves by `w' = G(w, s, s')`
(13.28).

* `bp_rceFeasible`: the constraints of agent `i`'s problem (13.29),
  `c + p(w, s)·θ ≤ wⁱ + yⁱ(s)` and `wⁱ' = (p(w', s') + d(s'))·θ ≥ −D̄ⁱ(s')` for all `s'`.
* `bp_rceObj`: the objective `uⁱ(c) + β ∑_{s'} Vⁱ(wⁱ', w', s') Pr(s'|s)` of (13.29).
* `BPRCE` (Definition 13.7.1): value, consumption and portfolio functions solving (13.29), market
  clearing and consistency of the law of motion. `definition_13_7_1_instance` is a concrete RCE
  (one agent, a Lucas tree, linear utility).
* `bp_rce_walras`: when budgets bind, market clearing at `(w, s)` forces aggregate wealth to
  equal the value of the trees, `∑ᵢ wⁱ = ∑_j (p_j(w, s) + d_j(s))`.
* `bp_rce_aggregate_wealth`: consistency and clearing give `∑ᵢ Gⁱ(w, s, s') = ∑_j (p_j(w', s') +
  d_j(s'))`, so one agent's wealth can be removed from the state (the remark on p. 446).

**Departures.**
* Definition 13.7.1(ii) imposes market clearing at every `(w, s)`. By `bp_rce_walras` this is
  only possible at states whose aggregate wealth equals the value of the trees; we impose
  clearing and consistency on a state space `Ωs` of wealth distributions that is invariant
  under `G` (in the instance, `Ωs = {∑ᵢ wⁱ = p + d}`).
* Typographical: the clearing conditions read `∑ᵢ hⁱ(wⁱ; w, s)`, `∑ᵢ gⁱ(wⁱ; w, s)` for `cⁱ`,
  `θⁱ`, the law of motion is written `G(w, s, s)` for `G(w, s, s')`, and the stock supplies are
  normalised to one share each.
-/

namespace Miao.CompleteMarkets

variable {ι J S : Type*} [Fintype ι] [Fintype J] [Fintype S]

/-- The constraint set of agent `i`'s dynamic programming problem (13.29) at the state
`(wⁱ; w, s)`: the budget constraint and the debt constraints for every next shock. -/
def bp_rceFeasible (p : (ι → ℝ) → S → J → ℝ) (d : S → J → ℝ) (G : (ι → ℝ) → S → S → ι → ℝ)
    (y : ι → S → ℝ) (Dbar : ι → S → ℝ) (i : ι) (wi : ℝ) (w : ι → ℝ) (s : S) (c : ℝ)
    (θ : J → ℝ) : Prop :=
  c + ∑ j, p w s j * θ j ≤ wi + y i s ∧
    ∀ s', -Dbar i s' ≤ ∑ j, (p (G w s s') s' j + d s' j) * θ j

/-- The objective of (13.29): `uⁱ(c) + β ∑_{s'} Vⁱ(wⁱ', G(w, s, s'), s') Pr(s' | s)` with
`wⁱ' = (p(w', s') + d(s'))·θ`. -/
def bp_rceObj (u : ι → ℝ → ℝ) (β : ℝ) (Pm : S → S → ℝ) (V : ι → ℝ → (ι → ℝ) → S → ℝ)
    (p : (ι → ℝ) → S → J → ℝ) (d : S → J → ℝ) (G : (ι → ℝ) → S → S → ι → ℝ) (i : ι) (w : ι → ℝ)
    (s : S) (c : ℝ) (θ : J → ℝ) : ℝ :=
  u i c + β * ∑ s', V i (∑ j, (p (G w s s') s' j + d s' j) * θ j) (G w s s') s' * Pm s s'

variable (u : ι → ℝ → ℝ) (β : ℝ) (Pm : S → S → ℝ) (y : ι → S → ℝ) (d : S → J → ℝ)
  (Dbar : ι → S → ℝ) (V : ι → ℝ → (ι → ℝ) → S → ℝ) (c : ι → ℝ → (ι → ℝ) → S → ℝ)
  (θ : ι → ℝ → (ι → ℝ) → S → J → ℝ) (p : (ι → ℝ) → S → J → ℝ)
  (G : (ι → ℝ) → S → S → ι → ℝ) (Ωs : Set ((ι → ℝ) × S)) in
/-- **Definition 13.7.1** (Miao, p. 445). A recursive competitive equilibrium with debt
constraints: value functions `Vⁱ(wⁱ; w, s)`, consumption functions `cⁱ(wⁱ; w, s)` and portfolio
functions `θⁱ(wⁱ; w, s)`, a price function `p(w, s)` and a law of motion `G(w, s, s')` such that
(i) given `G` and `p`, `(cⁱ, θⁱ)` solves (13.29) and `Vⁱ` is its value; (ii) markets clear,
`∑ᵢ cⁱ = ∑ᵢ yⁱ(s) + ∑_j d_j(s)` and `∑ᵢ θⁱ_j = 1`; (iii) `Gⁱ(w, s, s') = (p(G(w, s, s'), s') +
d(s'))·θⁱ(wⁱ; w, s)`. (ii) and (iii) are imposed on a state space `Ωs` invariant under `G`. -/
structure BPRCE : Prop where
  feasible : ∀ i wi w s, bp_rceFeasible p d G y Dbar i wi w s (c i wi w s) (θ i wi w s)
  value : ∀ i wi w s, V i wi w s = bp_rceObj u β Pm V p d G i w s (c i wi w s) (θ i wi w s)
  optimal : ∀ i wi w s c' θ', bp_rceFeasible p d G y Dbar i wi w s c' θ' →
    bp_rceObj u β Pm V p d G i w s c' θ' ≤ V i wi w s
  clear_goods : ∀ w s, (w, s) ∈ Ωs → ∑ i, c i (w i) w s = ∑ i, y i s + ∑ j, d s j
  clear_assets : ∀ w s, (w, s) ∈ Ωs → ∀ j, ∑ i, θ i (w i) w s j = 1
  invariant : ∀ w s s', (w, s) ∈ Ωs → (G w s s', s') ∈ Ωs
  consistent : ∀ w s s', (w, s) ∈ Ωs → ∀ i,
    G w s s' i = ∑ j, (p (G w s s') s' j + d s' j) * θ i (w i) w s j

omit [Fintype S] in
/-- Walras's law for Definition 13.7.1 (Miao, p. 445): if every agent's budget binds at
`(w, s)` and the goods and asset markets clear there, then aggregate wealth equals the value of
the trees, `∑ᵢ wⁱ = ∑_j (p_j(w, s) + d_j(s))`. Hence (ii) can hold only on such states. -/
theorem bp_rce_walras (y : ι → S → ℝ) (d : S → J → ℝ) (c : ι → ℝ → (ι → ℝ) → S → ℝ)
    (θ : ι → ℝ → (ι → ℝ) → S → J → ℝ) (p : (ι → ℝ) → S → J → ℝ) (w : ι → ℝ) (s : S)
    (hbind : ∀ i, c i (w i) w s + ∑ j, p w s j * θ i (w i) w s j = w i + y i s)
    (hgoods : ∑ i, c i (w i) w s = ∑ i, y i s + ∑ j, d s j)
    (hassets : ∀ j, ∑ i, θ i (w i) w s j = 1) :
    ∑ i, w i = ∑ j, (p w s j + d s j) := by
  have h := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hbind i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hgoods, Finset.sum_comm] at h
  simp only [← Finset.mul_sum, hassets, mul_one] at h
  rw [Finset.sum_add_distrib]
  linarith

/-- Miao, p. 446: on the state space, consistency (iii) and asset market clearing give
`∑ᵢ Gⁱ(w, s, s') = ∑_j (p_j(G(w, s, s'), s') + d_j(s'))`: aggregate wealth is the value of the
trees, so one agent's wealth is determined by the others' and can be removed from the state. -/
theorem bp_rce_aggregate_wealth {u : ι → ℝ → ℝ} {β : ℝ} {Pm : S → S → ℝ} {y : ι → S → ℝ}
    {d : S → J → ℝ} {Dbar : ι → S → ℝ} {V : ι → ℝ → (ι → ℝ) → S → ℝ}
    {c : ι → ℝ → (ι → ℝ) → S → ℝ} {θ : ι → ℝ → (ι → ℝ) → S → J → ℝ}
    {p : (ι → ℝ) → S → J → ℝ} {G : (ι → ℝ) → S → S → ι → ℝ} {Ωs : Set ((ι → ℝ) × S)}
    (hR : BPRCE u β Pm y d Dbar V c θ p G Ωs) (w : ι → ℝ) (s s' : S) (hw : (w, s) ∈ Ωs) :
    ∑ i, G w s s' i = ∑ j, (p (G w s s') s' j + d s' j) := by
  simp only [hR.consistent w s s' hw]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hR.clear_assets w s hw, mul_one]

/-- A concrete recursive competitive equilibrium (`BPRCE`): one agent with linear utility
`u(c) = c` and discount factor `0 < β < 1`, one shock, one tree paying `d ≥ 0`, endowment `y`,
debt limit `0`. The price is `p = βd/(1 − β)`, the value function `V(wⁱ) = wⁱ + y/(1 − β)`,
consumption `wⁱ + y − p`, the portfolio `θ = 1`, the law of motion `G = p + d` and the state
space `{w = p + d}`. -/
theorem definition_13_7_1_instance (β y dv : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hd : 0 ≤ dv) :
    BPRCE (ι := Unit) (J := Unit) (S := Unit) (fun _ x => x) β (fun _ _ => 1) (fun _ _ => y)
      (fun _ _ => dv) (fun _ _ => 0) (fun _ wi _ _ => wi + y / (1 - β))
      (fun _ wi _ _ => wi + y - β * dv / (1 - β)) (fun _ _ _ _ _ => 1)
      (fun _ _ _ => β * dv / (1 - β)) (fun _ _ _ _ => β * dv / (1 - β) + dv)
      {x | ∑ i, x.1 i = β * dv / (1 - β) + dv} := by
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hp : β * (β * dv / (1 - β) + dv) = β * dv / (1 - β) := by field_simp; ring
  have hpd : 0 ≤ β * dv / (1 - β) + dv :=
    add_nonneg (div_nonneg (mul_nonneg hβ.le hd) (by linarith)) hd
  refine ⟨fun i wi w s => ⟨?_, fun s' => ?_⟩, fun i wi w s => ?_, fun i wi w s c' θ' hf => ?_,
    fun w s hw => ?_, fun w s hw j => ?_, fun w s s' hw => ?_, fun w s s' hw i => ?_⟩
  · simp
  · simp only [Finset.univ_unique, Finset.sum_singleton, mul_one, neg_zero]
    exact hpd
  · simp only [bp_rceObj, Finset.univ_unique, Finset.sum_singleton, mul_one]
    field_simp
    ring
  · obtain ⟨hb, -⟩ := hf
    simp only [Finset.univ_unique, Finset.sum_singleton] at hb
    simp only [bp_rceObj, Finset.univ_unique, Finset.sum_singleton, mul_one]
    have e : β * ((β * dv / (1 - β) + dv) * θ' () + y / (1 - β)) =
        β * dv / (1 - β) * θ' () + β * y / (1 - β) := by
      rw [mul_add, ← mul_assoc, hp]
      ring
    rw [e]
    have e2 : wi + y / (1 - β) = wi + y + β * y / (1 - β) := by field_simp; ring
    rw [e2]
    linarith
  · simp only [Set.mem_ofPred_eq, Finset.univ_unique, Finset.sum_singleton] at hw ⊢
    rw [hw]
    ring
  · simp
  · simp
  · simp

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Asset pricing with a stochastic discount factor

Miao, §13.8, pp. 446–449 (the SDF, (13.30), (13.31), the Hansen–Jagannathan bound, CAPM,
factor pricing, the CCAPM SDF) and Exercise 13.9 (p. 454). Conditional moments at a node are
moments under a finite conditional distribution `w` on the successor states `Ω`
(`w ≥ 0`, `∑ w = 1`): `bp_E`, `bp_Cov`, `bp_Var`, `bp_sd`.

* `eq_13_30`: `p_j = E[M f_j]` gives `E[M R_j] = 1` for `R_j = f_j/p_j`.
* `bp_riskfree`: `R_f = 1/E[M]`; `bp_excess`: `E[(R_j − R_f) M] = 0`.
* `eq_13_31`: `E[R_j − R_f] = −Cov(M, R_j − R_f)/E[M]`.
* `bp_cov_ge_neg_sd`: `Cov(X, Y) ≥ −σ(X)σ(Y)`; `bp_hansen_jagannathan`:
  `σ(M)/E[M] ≥ E[R_j − R_f]/σ(R_j − R_f)`.
* CAPM, `M = a + bR_m`: `bp_capm_market` (`E[R_m − R_f] = −b Var(R_m)/E[M]`), `bp_capm_asset`
  (`E[R_j − R_f] = −b Cov(R_m, R_j)/E[M]`), `bp_capm` (`E[R_j − R_f] = β_j E[R_m − R_f]` with
  `β_j = Cov(R_j, R_m)/Var(R_m)`).
* Factor pricing, `M = a + ∑ b_k F_k` (13.32): `eq_13_32_cov` and `bp_factor_pricing`
  (`E[R_j − R_f] = ∑ β_{jk} λ_k`).
* CCAPM: `bp_ccapm_euler` derives the representative agent's Euler equation
  `p u'(C) = β E[u'(C') f]` from optimality (a local maximum along the one-asset perturbation),
  hence the SDF `M = βu'(C')/u'(C)` (`bp_ccapm_sdf`).
* Exercise 13.9 (`ex_13_9_wealth`, `ex_13_9_sdf`): with log utility the wealth portfolio (the
  claim to aggregate consumption) has price `βC_t/(1 − β)`, return `R_w = C_{t+1}/(βC_t)` and
  `M = 1/R_w`. CAPM: `ex_13_9_capm_two_states` (exact when the conditional distribution has two
  states); `ex_13_9_capm_counterexample` (fails with three states).

**Corrections.**
* p. 448, CAPM: the book defines `β_{jt} = Cov_t[R_{j,t+1}, M_{t+1}]/Var_t(M_{t+1})`. With
  `M = a + bR_m` this is `Cov(R_j, R_m)/(b Var(R_m))`, and the stated relation
  `E[R_j − R_f] = β_j E[R_m − R_f]` holds only for `b = 1`; the book's own gloss ("the regression
  coefficient of the asset return `j` on the market portfolio return") is the correct
  `β_j = Cov(R_j, R_m)/Var(R_m)` (`bp_capm`). Counterexample: `bp_capm_book_beta_counterexample`.
* Exercise 13.9, "derive the CAPM": with log utility `M = 1/R_w`, which is not affine in `R_w`
  in general, so the CAPM in `R_w` holds exactly only when `1/R_w` is affine in `R_w` on the
  support (e.g. two states, `ex_13_9_capm_two_states`) and fails otherwise
  (`ex_13_9_capm_counterexample`); in general it is an approximation.
-/

open Filter Topology

namespace Miao.CompleteMarkets

/-- Conditional expectation under the finite distribution `w`. -/
def bp_E {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) : ℝ := ∑ ω, w ω * X ω

/-- Conditional covariance. -/
def bp_Cov {Ω : Type*} [Fintype Ω] (w X Y : Ω → ℝ) : ℝ :=
  bp_E w (fun ω => X ω * Y ω) - bp_E w X * bp_E w Y

/-- Conditional variance. -/
def bp_Var {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) : ℝ := bp_Cov w X X

/-- Conditional volatility `σ(X)`. -/
noncomputable def bp_sd {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) : ℝ := Real.sqrt (bp_Var w X)

variable {Ω : Type*} [Fintype Ω]

theorem bp_E_add (w X Y : Ω → ℝ) : bp_E w (fun ω => X ω + Y ω) = bp_E w X + bp_E w Y := by
  simp only [bp_E, mul_add, Finset.sum_add_distrib]

theorem bp_E_sub (w X Y : Ω → ℝ) : bp_E w (fun ω => X ω - Y ω) = bp_E w X - bp_E w Y := by
  simp only [bp_E, mul_sub, Finset.sum_sub_distrib]

theorem bp_E_mul_left (w X : Ω → ℝ) (a : ℝ) : bp_E w (fun ω => a * X ω) = a * bp_E w X := by
  simp only [bp_E, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

theorem bp_E_const (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (a : ℝ) : bp_E w (fun _ => a) = a := by
  simp only [bp_E, ← Finset.sum_mul, hw, one_mul]

theorem bp_E_finsetSum {K : Type*} (A : Finset K) (w : Ω → ℝ) (X : K → Ω → ℝ) :
    bp_E w (fun ω => ∑ k ∈ A, X k ω) = ∑ k ∈ A, bp_E w (X k) := by
  simp only [bp_E, Finset.mul_sum]
  exact Finset.sum_comm

/-- The covariance in deviation form `Cov(X, Y) = E[(X − EX)(Y − EY)]`. -/
theorem bp_Cov_eq_dev (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (X Y : Ω → ℝ) :
    bp_Cov w X Y = bp_E w (fun ω => (X ω - bp_E w X) * (Y ω - bp_E w Y)) := by
  have h : (fun ω => (X ω - bp_E w X) * (Y ω - bp_E w Y)) =
      fun ω => X ω * Y ω - (bp_E w Y * X ω + (bp_E w X * Y ω - bp_E w X * bp_E w Y)) := by
    funext ω
    ring
  rw [h, bp_E_sub, bp_E_add, bp_E_sub, bp_E_mul_left, bp_E_mul_left, bp_E_const w hw]
  unfold bp_Cov
  ring

theorem bp_Cov_comm (w X Y : Ω → ℝ) : bp_Cov w X Y = bp_Cov w Y X := by
  unfold bp_Cov
  simp only [mul_comm (X _), mul_comm (bp_E w X)]

/-- `Cov(a + bX, Y) = b Cov(X, Y)`. -/
theorem bp_Cov_affine_left (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (a b : ℝ) (X Y : Ω → ℝ) :
    bp_Cov w (fun ω => a + b * X ω) Y = b * bp_Cov w X Y := by
  unfold bp_Cov
  have h1 : (fun ω => (a + b * X ω) * Y ω) = fun ω => a * Y ω + b * (X ω * Y ω) := by
    funext ω
    ring
  rw [h1, bp_E_add, bp_E_mul_left, bp_E_mul_left, bp_E_add, bp_E_const w hw, bp_E_mul_left]
  ring

/-- `Cov(X, Y − c) = Cov(X, Y)` for a constant `c`. -/
theorem bp_Cov_sub_const (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (X Y : Ω → ℝ) (c : ℝ) :
    bp_Cov w X (fun ω => Y ω - c) = bp_Cov w X Y := by
  unfold bp_Cov
  have h1 : (fun ω => X ω * (Y ω - c)) = fun ω => X ω * Y ω - c * X ω := by
    funext ω
    ring
  rw [h1, bp_E_sub, bp_E_sub, bp_E_mul_left, bp_E_const w hw]
  ring

/-- `Cov(∑ₖ bₖ Fₖ, Y) = ∑ₖ bₖ Cov(Fₖ, Y)`. -/
theorem bp_Cov_sum_left {K : Type*} [Fintype K] (w X : Ω → ℝ) (b : K → ℝ) (F : K → Ω → ℝ) :
    bp_Cov w (fun ω => ∑ k, b k * F k ω) X = ∑ k, b k * bp_Cov w (F k) X := by
  unfold bp_Cov
  have h1 : (fun ω => (∑ k, b k * F k ω) * X ω) = fun ω => ∑ k, b k * (F k ω * X ω) := by
    funext ω
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h1, bp_E_finsetSum, bp_E_finsetSum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [bp_E_mul_left, bp_E_mul_left]
  ring

theorem bp_Var_nonneg (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw : ∑ ω, w ω = 1) (X : Ω → ℝ) :
    0 ≤ bp_Var w X := by
  unfold bp_Var
  rw [bp_Cov_eq_dev w hw]
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hw0 ω) (mul_self_nonneg _))

/-- The Cauchy–Schwarz inequality `Cov(X, Y)² ≤ Var(X) Var(Y)`. -/
theorem bp_Cov_sq_le (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw : ∑ ω, w ω = 1) (X Y : Ω → ℝ) :
    bp_Cov w X Y ^ 2 ≤ bp_Var w X * bp_Var w Y := by
  unfold bp_Var
  rw [bp_Cov_eq_dev w hw, bp_Cov_eq_dev w hw, bp_Cov_eq_dev w hw]
  unfold bp_E
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => Real.sqrt (w ω) * (X ω - bp_E w X)) (fun ω => Real.sqrt (w ω) * (Y ω - bp_E w Y))
  have e1 : ∀ ω, Real.sqrt (w ω) * (X ω - bp_E w X) * (Real.sqrt (w ω) * (Y ω - bp_E w Y)) =
      w ω * ((X ω - bp_E w X) * (Y ω - bp_E w Y)) := by
    intro ω
    have := Real.mul_self_sqrt (hw0 ω)
    linear_combination ((X ω - bp_E w X) * (Y ω - bp_E w Y)) * this
  have e2 : ∀ (Z : Ω → ℝ) (c : ℝ) ω, (Real.sqrt (w ω) * (Z ω - c)) ^ 2 =
      w ω * ((Z ω - c) * (Z ω - c)) := by
    intro Z c ω
    rw [mul_pow, Real.sq_sqrt (hw0 ω)]
    ring
  simp only [e1, e2] at h
  exact h

/-- `Cov(X, Y) ≥ −σ(X)σ(Y)` (Miao, p. 447). -/
theorem bp_cov_ge_neg_sd (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw : ∑ ω, w ω = 1)
    (X Y : Ω → ℝ) : -(bp_sd w X * bp_sd w Y) ≤ bp_Cov w X Y := by
  have h := Real.abs_le_sqrt (bp_Cov_sq_le w hw0 hw X Y)
  rw [Real.sqrt_mul (bp_Var_nonneg w hw0 hw X)] at h
  unfold bp_sd
  linarith [neg_abs_le (bp_Cov w X Y)]

/-- Miao, (13.30), p. 446: if `p_j = E[M f_j]` and `R_j = f_j/p_j`, then `E[M R_j] = 1`. -/
theorem eq_13_30 (w M f : Ω → ℝ) (p : ℝ) (hp : p ≠ 0) (hpr : p = bp_E w (fun ω => M ω * f ω)) :
    bp_E w (fun ω => M ω * (f ω / p)) = 1 := by
  have : (fun ω => M ω * (f ω / p)) = fun ω => (1 / p) * (M ω * f ω) := by
    funext ω
    ring
  rw [this, bp_E_mul_left, ← hpr]
  field_simp

/-- Miao, p. 446: the riskfree rate `R_f = 1/E[M]`. -/
theorem bp_riskfree (w M : Ω → ℝ) (Rf : ℝ) (h : bp_E w (fun ω => M ω * Rf) = 1) :
    Rf = 1 / bp_E w M := by
  have : bp_E w (fun ω => M ω * Rf) = Rf * bp_E w M := by
    rw [← bp_E_mul_left]
    congr 1
    funext ω
    ring
  rw [this] at h
  have hM : bp_E w M ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  field_simp
  linarith

/-- Miao, p. 447: the conditional expected excess return weighted by the SDF vanishes,
`E[(R_j − R_f) M] = 0`. -/
theorem bp_excess (w M R : Ω → ℝ) (Rf : ℝ) (hR : bp_E w (fun ω => M ω * R ω) = 1)
    (hf : bp_E w (fun ω => M ω * Rf) = 1) : bp_E w (fun ω => (R ω - Rf) * M ω) = 0 := by
  have : (fun ω => (R ω - Rf) * M ω) = fun ω => M ω * R ω - M ω * Rf := by
    funext ω
    ring
  rw [this, bp_E_sub, hR, hf, sub_self]

/-- Miao, (13.31), p. 447: `E[R_j − R_f] = −Cov(M, R_j − R_f)/E[M]`. -/
theorem eq_13_31 (w M R : Ω → ℝ) (Rf : ℝ) (hR : bp_E w (fun ω => M ω * R ω) = 1)
    (hf : bp_E w (fun ω => M ω * Rf) = 1) (hM : bp_E w M ≠ 0) :
    bp_E w (fun ω => R ω - Rf) = -bp_Cov w M (fun ω => R ω - Rf) / bp_E w M := by
  have hx := bp_excess w M R Rf hR hf
  unfold bp_Cov
  have : (fun ω => M ω * (R ω - Rf)) = fun ω => (R ω - Rf) * M ω := by
    funext ω
    ring
  rw [this, hx]
  field_simp
  ring

/-- Miao, p. 447 (Hansen–Jagannathan): the Sharpe ratio of any asset is bounded by the market
price of risk, `σ(M)/E[M] ≥ E[R_j − R_f]/σ(R_j − R_f)`. -/
theorem bp_hansen_jagannathan (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw : ∑ ω, w ω = 1)
    (M R : Ω → ℝ) (Rf : ℝ) (hR : bp_E w (fun ω => M ω * R ω) = 1)
    (hf : bp_E w (fun ω => M ω * Rf) = 1) (hM : 0 < bp_E w M)
    (hsd : 0 < bp_sd w (fun ω => R ω - Rf)) :
    bp_E w (fun ω => R ω - Rf) / bp_sd w (fun ω => R ω - Rf) ≤ bp_sd w M / bp_E w M := by
  rw [eq_13_31 w M R Rf hR hf hM.ne']
  have hc := bp_cov_ge_neg_sd w hw0 hw M (fun ω => R ω - Rf)
  rw [div_div, div_le_div_iff₀ (mul_pos hM hsd) hM]
  have : 0 ≤ bp_sd w M := Real.sqrt_nonneg _
  nlinarith

/-- CAPM, Miao, p. 448: with `M = a + bR_m`, `E[R_m − R_f] = −b Var(R_m)/E[M]`. -/
theorem bp_capm_market (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (M Rm : Ω → ℝ) (a b Rf : ℝ)
    (hMdef : ∀ ω, M ω = a + b * Rm ω) (hRm : bp_E w (fun ω => M ω * Rm ω) = 1)
    (hf : bp_E w (fun ω => M ω * Rf) = 1) (hM : bp_E w M ≠ 0) :
    bp_E w (fun ω => Rm ω - Rf) = -b * bp_Var w Rm / bp_E w M := by
  rw [eq_13_31 w M Rm Rf hRm hf hM, bp_Cov_sub_const w hw, show M = fun ω => a + b * Rm ω from
    funext hMdef, bp_Cov_affine_left w hw]
  unfold bp_Var
  ring

/-- CAPM, Miao, p. 448: with `M = a + bR_m`, `E[R_j − R_f] = −b Cov(R_m, R_j)/E[M]`. -/
theorem bp_capm_asset (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (M Rm R : Ω → ℝ) (a b Rf : ℝ)
    (hMdef : ∀ ω, M ω = a + b * Rm ω) (hR : bp_E w (fun ω => M ω * R ω) = 1)
    (hf : bp_E w (fun ω => M ω * Rf) = 1) (hM : bp_E w M ≠ 0) :
    bp_E w (fun ω => R ω - Rf) = -b * bp_Cov w Rm R / bp_E w M := by
  rw [eq_13_31 w M R Rf hR hf hM, bp_Cov_sub_const w hw, show M = fun ω => a + b * Rm ω from
    funext hMdef, bp_Cov_affine_left w hw]
  ring

/-- **CAPM** (Sharpe–Lintner, Miao, p. 448, corrected beta): with `M = a + bR_m` and
`Var(R_m) ≠ 0`, `E[R_j − R_f] = β_j E[R_m − R_f]` where
`β_j = Cov(R_j, R_m)/Var(R_m)` is the regression coefficient of `R_j` on `R_m`. -/
theorem bp_capm (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (M Rm R : Ω → ℝ) (a b Rf : ℝ)
    (hMdef : ∀ ω, M ω = a + b * Rm ω) (hRm : bp_E w (fun ω => M ω * Rm ω) = 1)
    (hR : bp_E w (fun ω => M ω * R ω) = 1) (hf : bp_E w (fun ω => M ω * Rf) = 1)
    (hM : bp_E w M ≠ 0) (hV : bp_Var w Rm ≠ 0) :
    bp_E w (fun ω => R ω - Rf) =
      bp_Cov w R Rm / bp_Var w Rm * bp_E w (fun ω => Rm ω - Rf) := by
  rw [bp_capm_asset w hw M Rm R a b Rf hMdef hR hf hM,
    bp_capm_market w hw M Rm a b Rf hMdef hRm hf hM, bp_Cov_comm w R Rm]
  field_simp

/-- The weights `(1/2, 1/2)` on two states. -/
noncomputable def bp_half : Fin 2 → ℝ := fun _ => 1 / 2

/-- Counterexample to the book's CAPM beta `β_j = Cov(R_j, M)/Var(M)` (Miao, p. 448): two
equally likely states, `R_m = (1, 3)`, `M = 9/8 − R_m/4 = (7/8, 3/8)`, `R_f = 8/5`. The SDF
prices `R_m` and `R_f`, but for `j = m` the book's beta is `−4`, not `1`, and
`E[R_m − R_f] = 2/5 ≠ −4 · 2/5`. -/
theorem bp_capm_book_beta_counterexample :
    let Rm : Fin 2 → ℝ := ![1, 3]
    let M : Fin 2 → ℝ := fun ω => 9 / 8 + (-1 / 4) * Rm ω
    bp_E bp_half (fun ω => M ω * Rm ω) = 1 ∧ bp_E bp_half (fun ω => M ω * (8 / 5)) = 1 ∧
      bp_E bp_half (fun ω => Rm ω - 8 / 5) ≠
        bp_Cov bp_half Rm M / bp_Var bp_half M * bp_E bp_half (fun ω => Rm ω - 8 / 5) := by
  intro Rm M
  simp only [bp_E, bp_Cov, bp_Var, bp_half, Fin.sum_univ_two, Rm, M, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- Miao, p. 449, factor pricing: with `M = a + ∑ₖ bₖ Fₖ` (13.32),
`−Cov(M, R_j − R_f) = −∑ₖ bₖ Var(Fₖ) · Cov(Fₖ, R_j)/Var(Fₖ)`. -/
theorem eq_13_32_cov {K : Type*} [Fintype K] (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (M R : Ω → ℝ)
    (a Rf : ℝ) (b : K → ℝ) (F : K → Ω → ℝ) (hMdef : ∀ ω, M ω = a + ∑ k, b k * F k ω)
    (hVF : ∀ k, bp_Var w (F k) ≠ 0) :
    -bp_Cov w M (fun ω => R ω - Rf) = -∑ k, b k * bp_Cov w (F k) R ∧
      -∑ k, b k * bp_Cov w (F k) R =
        -∑ k, b k * bp_Var w (F k) * (bp_Cov w (F k) R / bp_Var w (F k)) := by
  refine ⟨?_, ?_⟩
  · rw [bp_Cov_sub_const w hw, show M = fun ω => a + 1 * ∑ k, b k * F k ω by
      funext ω
      rw [hMdef, one_mul], bp_Cov_affine_left w hw, one_mul, bp_Cov_sum_left]
  · congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    field_simp [hVF k]

/-- **Factor pricing model** (Miao, p. 449): with `M = a + ∑ₖ bₖ Fₖ`,
`E[R_j − R_f] = ∑ₖ β_{jk} λ_k`, `β_{jk} = Cov(Fₖ, R_j)/Var(Fₖ)`,
`λ_k = −bₖ Var(Fₖ)/E[M]`. -/
theorem bp_factor_pricing {K : Type*} [Fintype K] (w : Ω → ℝ) (hw : ∑ ω, w ω = 1)
    (M R : Ω → ℝ) (a Rf : ℝ) (b : K → ℝ) (F : K → Ω → ℝ)
    (hMdef : ∀ ω, M ω = a + ∑ k, b k * F k ω) (hVF : ∀ k, bp_Var w (F k) ≠ 0)
    (hR : bp_E w (fun ω => M ω * R ω) = 1) (hf : bp_E w (fun ω => M ω * Rf) = 1)
    (hM : bp_E w M ≠ 0) :
    bp_E w (fun ω => R ω - Rf) =
      ∑ k, bp_Cov w (F k) R / bp_Var w (F k) * (-b k * bp_Var w (F k) / bp_E w M) := by
  rw [eq_13_31 w M R Rf hR hf hM, (eq_13_32_cov w hw M R a Rf b F hMdef hVF).1, neg_div,
    Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  field_simp [hVF k]

/-- The CCAPM Euler equation from optimality (Miao, p. 449). The representative agent consumes
`C` today and `C'_ω` tomorrow; buying `ε` units of an asset with price `p` and payoff `f` gives
utility `u(C − pε) + β E[u(C' + fε)]`. If `ε = 0` is a local maximum and `u` is differentiable,
then `p u'(C) = β E[u'(C') f]`. -/
theorem bp_ccapm_euler (w : Ω → ℝ) (u u' : ℝ → ℝ) (hu : ∀ x, HasDerivAt u (u' x) x)
    (β C p : ℝ) (C' f : Ω → ℝ)
    (hmax : IsLocalMax (fun ε => u (C - p * ε) + β * bp_E w (fun ω => u (C' ω + f ω * ε))) 0) :
    p * u' C = β * bp_E w (fun ω => u' (C' ω) * f ω) := by
  have h1 : HasDerivAt (fun ε => u (C - p * ε)) (u' C * (-p)) 0 := by
    have hin : HasDerivAt (fun ε : ℝ => C - p * ε) (-p) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul p |>.const_sub C
    exact (hu C).comp_of_eq 0 hin (by ring)
  have h2 : ∀ ω, HasDerivAt (fun ε => w ω * u (C' ω + f ω * ε)) (w ω * (u' (C' ω) * f ω)) 0 := by
    intro ω
    have hin : HasDerivAt (fun ε : ℝ => C' ω + f ω * ε) (f ω) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (f ω)).const_add (C' ω)
    exact ((hu (C' ω)).comp_of_eq 0 hin (by ring)).const_mul (w ω)
  have h3 : HasDerivAt (fun ε => bp_E w (fun ω => u (C' ω + f ω * ε)))
      (bp_E w (fun ω => u' (C' ω) * f ω)) 0 := by
    unfold bp_E
    have := HasDerivAt.sum (u := Finset.univ) (fun ω _ => h2 ω)
    convert this using 1
    funext ε
    simp
  have h := hmax.hasDerivAt_eq_zero (h1.add (h3.const_mul β))
  linarith

/-- The CCAPM stochastic discount factor (Miao, p. 449): the Euler equation `p u'(C) =
β E[u'(C') f]` with `u'(C) ≠ 0` says `p = E[M f]` with `M = βu'(C')/u'(C)`. -/
theorem bp_ccapm_sdf (w : Ω → ℝ) (u' : ℝ → ℝ) (β C p : ℝ) (C' f : Ω → ℝ) (hC : u' C ≠ 0)
    (heul : p * u' C = β * bp_E w (fun ω => u' (C' ω) * f ω)) :
    p = bp_E w (fun ω => β * u' (C' ω) / u' C * f ω) := by
  have : (fun ω => β * u' (C' ω) / u' C * f ω) = fun ω => β / u' C * (u' (C' ω) * f ω) := by
    funext ω
    ring
  rw [this, bp_E_mul_left, ← mul_div_right_comm, ← heul]
  field_simp

/-- **Exercise 13.9** (Miao, p. 454), the wealth portfolio. With log utility and aggregate
consumption `C > 0` on the event tree, the claim to aggregate consumption with price
`p^w_t = βC_t/(1 − β)` satisfies the Euler equation
`u'(C_t) p^w_t = β E_t[u'(C_{t+1})(p^w_{t+1} + C_{t+1})]`, and its return is
`R_{w,t+1} = (p^w_{t+1} + C_{t+1})/p^w_t = C_{t+1}/(βC_t)`. -/
theorem ex_13_9_wealth {S : Type*} [Fintype S] (T : BPTree S) (β : ℝ) (hβ : 0 < β)
    (hβ1 : β < 1) (C : List S → ℝ) (hC : ∀ h, 0 < C h) (h : List S) :
    1 / C h * (β * C h / (1 - β)) =
        β * bp_condExp T 1 (fun g => 1 / C g * (β * C g / (1 - β) + C g)) h ∧
      ∀ s, (β * C (s :: h) / (1 - β) + C (s :: h)) / (β * C h / (1 - β)) =
        C (s :: h) / (β * C h) := by
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  refine ⟨?_, fun s => ?_⟩
  · have : (fun g => 1 / C g * (β * C g / (1 - β) + C g)) = fun _ => 1 / (1 - β) := by
      funext g
      have := (hC g).ne'
      field_simp
      ring
    rw [this, bp_condExp_const]
    have := (hC h).ne'
    field_simp
  · have := (hC h).ne'
    have := (hC (s :: h)).ne'
    have := hβ.ne'
    field_simp
    ring

/-- **Exercise 13.9** (Miao, p. 454): with log utility the SDF is the inverse of the return on
the wealth portfolio, `M_{t+1} = βu'(C_{t+1})/u'(C_t) = βC_t/C_{t+1} = 1/R_{w,t+1}`. -/
theorem ex_13_9_sdf (β Ct Ct1 : ℝ) (hβ : 0 < β) (hCt : 0 < Ct) (hCt1 : 0 < Ct1) :
    β * (1 / Ct1) / (1 / Ct) = 1 / (Ct1 / (β * Ct)) := by
  have := hCt.ne'
  have := hCt1.ne'
  have := hβ.ne'
  field_simp

/-- Exercise 13.9, CAPM in the two-state case: if the conditional distribution has two states
and `R_w` takes different values in them, `M = 1/R_w` is affine in `R_w`, so
`E[R_j − R_f] = β_j E[R_w − R_f]` with `β_j = Cov(R_j, R_w)/Var(R_w)`. -/
theorem ex_13_9_capm_two_states (w : Fin 2 → ℝ) (hw : ∑ ω, w ω = 1) (Rw R : Fin 2 → ℝ)
    (Rf : ℝ) (hRw : ∀ ω, 0 < Rw ω) (hne : Rw 0 ≠ Rw 1)
    (hRm : bp_E w (fun ω => 1 / Rw ω * Rw ω) = 1) (hR : bp_E w (fun ω => 1 / Rw ω * R ω) = 1)
    (hf : bp_E w (fun ω => 1 / Rw ω * Rf) = 1) (hM : bp_E w (fun ω => 1 / Rw ω) ≠ 0)
    (hV : bp_Var w Rw ≠ 0) :
    bp_E w (fun ω => R ω - Rf) = bp_Cov w R Rw / bp_Var w Rw * bp_E w (fun ω => Rw ω - Rf) := by
  set b := (1 / Rw 1 - 1 / Rw 0) / (Rw 1 - Rw 0) with hb
  set a := 1 / Rw 0 - b * Rw 0 with ha
  have hsub : Rw 1 - Rw 0 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hMdef : ∀ ω, 1 / Rw ω = a + b * Rw ω := by
    intro ω
    fin_cases ω
    · simp [ha]
    · change 1 / Rw 1 = a + b * Rw 1
      have := (hRw 0).ne'
      have := (hRw 1).ne'
      simp only [ha, hb]
      field_simp
      ring
  exact bp_capm w hw (fun ω => 1 / Rw ω) Rw R a b Rf hMdef hRm hR hf hM hV

/-- The weights `(1/3, 1/3, 1/3)` on three states. -/
noncomputable def bp_third : Fin 3 → ℝ := fun _ => 1 / 3

/-- Counterexample to an exact CAPM in Exercise 13.9: three equally likely states,
`R_w = (1, 2, 4)`, `M = 1/R_w`, `R_f = 12/7` and the Arrow security of state 0, `R_j = (3, 0, 0)`.
`M` prices `R_w`, `R_f` and `R_j`, but `E[R_j − R_f] = −5/7` while
`β_j E[R_w − R_f] = −26/49`. -/
theorem ex_13_9_capm_counterexample :
    let Rw : Fin 3 → ℝ := ![1, 2, 4]
    let R : Fin 3 → ℝ := ![3, 0, 0]
    bp_E bp_third (fun ω => 1 / Rw ω * Rw ω) = 1 ∧
      bp_E bp_third (fun ω => 1 / Rw ω * R ω) = 1 ∧
      bp_E bp_third (fun ω => 1 / Rw ω * (12 / 7)) = 1 ∧
      bp_E bp_third (fun ω => R ω - 12 / 7) ≠
        bp_Cov bp_third R Rw / bp_Var bp_third Rw * bp_E bp_third (fun ω => Rw ω - 12 / 7) := by
  intro Rw R
  simp only [bp_E, bp_Cov, bp_Var, bp_third, Fin.sum_univ_three, Rw, R, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The lognormal CCAPM: the riskfree rate and the equity premium

Miao, §13.8, pp. 449–451, equations (13.33)–(13.36). The SDF is `M = e^m` and a return is
`R_j = e^{r_j}`; joint lognormality enters through the Gaussian laws of `m`, `r_j` and `m + r_j`
on a probability space `(Ω, P)` (the conditional distribution at a node, which is the same at
every node under homoskedasticity).

* `bp_integral_exp_gaussian`: `E[e^X] = e^{μ + v/2}` for `X ~ N(μ, v)`.
* `eq_13_33`: `E[M R_f] = 1` gives `r_f = −E[m] − σ_m²/2`.
* `eq_13_34`: `E[M R_j] = 1` gives `E[r_j − r_f] + σ_j²/2 = −σ_{jm}` with
  `σ_{jm} = Cov(r_j, m)`; the covariance is recovered from `Var(m + r_j)`.
* CRRA utility and lognormal consumption growth `Δc = g + σ_c ε`, `ε ~ N(0, 1)`:
  `m = ln β − γΔc` (`bp_ccapm_log_sdf`), `eq_13_35` (`r_f = −ln β + γg − γ²σ_c²/2`) and the
  comparative statics stated after it (`eq_13_35_beta`, `eq_13_35_growth`, `eq_13_35_risk`);
  `eq_13_36` (corrected): `E[r_j − r_f] + σ_j²/2 = γσ_c Cov(r_j, ε) = γ Cov(r_j, Δc)`.

**Correction.** (13.36) as printed, `E[r_j − r_f] + σ_j²/2 = γσ_{jc}` with
`σ_{jc} = Cov(r_j − E r_j, ε)`, omits the factor `σ_c`: since `m − Em = −γσ_c ε`,
`−σ_{jm} = γσ_c Cov(r_j, ε)` (`eq_13_36`). The printed formula is right if `σ_{jc}` is the
covariance with consumption growth `Δc = g + σ_c ε`. Counterexample to the printed form:
`eq_13_36_counterexample` (`γ = 1`, `σ_c = 1/2`, `Cov(r_j, ε) = 1`: the premium is `1/2`, not `1`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Miao.CompleteMarkets

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem bp_integrable_id_gaussian (μ : ℝ) (v : ℝ≥0) :
    Integrable (id : ℝ → ℝ) (gaussianReal μ v) :=
  (memLp_id_gaussianReal 2).integrable one_le_two

/-- `E[e^X] = e^{μ + v/2}` for a Gaussian `X ~ N(μ, v)`. -/
theorem bp_integral_exp_gaussian {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal μ v) P) : ∫ ω, Real.exp (X ω) ∂P = Real.exp (μ + v / 2) := by
  have := mgf_gaussianReal hX 1
  simpa [mgf] using this

theorem bp_mean_gaussian {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal μ v) P) :
    ∫ ω, X ω ∂P = μ :=
  hX.integral_eq.trans integral_id_gaussianReal

theorem bp_var_gaussian {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal μ v) P) :
    Var[X; P] = v :=
  hX.variance_eq.trans variance_id_gaussianReal

theorem bp_memLp_gaussian {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal μ v) P) :
    MemLp X 2 P :=
  hX.memLp (memLp_id_gaussianReal 2)

/-- An Euler equation `E[e^X e^a] = 1` with `X ~ N(μ, v)` pins down `a = −μ − v/2`. -/
theorem bp_euler_gaussian {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal μ v) P)
    (a : ℝ) (h : ∫ ω, Real.exp (X ω) * Real.exp a ∂P = 1) : μ + v / 2 + a = 0 := by
  rw [integral_mul_const, bp_integral_exp_gaussian hX, ← Real.exp_add] at h
  exact Real.exp_eq_one_iff _ |>.1 h

/-- Miao, (13.33), p. 449: with `M = e^m`, `m` Gaussian, and `E[M e^{r_f}] = 1`,
`r_f = −E[m] − σ_m²/2`. -/
theorem eq_13_33 {m : Ω → ℝ} {μm : ℝ} {vm : ℝ≥0} (hm : HasLaw m (gaussianReal μm vm) P)
    (rf : ℝ) (heul : ∫ ω, Real.exp (m ω) * Real.exp rf ∂P = 1) :
    rf = -(∫ ω, m ω ∂P) - Var[m; P] / 2 := by
  have := bp_euler_gaussian hm rf heul
  rw [bp_mean_gaussian hm, bp_var_gaussian hm]
  linarith

/-- Miao, (13.34), p. 450: if `m`, `r_j` and `m + r_j` are Gaussian (joint normality), the Euler
equations `E[M R_f] = 1` and `E[M R_j] = 1` give `E[r_j − r_f] + σ_j²/2 = −σ_{jm}` with
`σ_{jm} = Cov(r_j, m)`. -/
theorem eq_13_34 [IsProbabilityMeasure P] {m r : Ω → ℝ} {μm μj : ℝ} {vm vj vmr : ℝ≥0}
    (hm : HasLaw m (gaussianReal μm vm) P) (hr : HasLaw r (gaussianReal μj vj) P)
    (hmr : HasLaw (fun ω => m ω + r ω) (gaussianReal (μm + μj) vmr) P) (rf : ℝ)
    (hf : ∫ ω, Real.exp (m ω) * Real.exp rf ∂P = 1)
    (hj : ∫ ω, Real.exp (m ω) * Real.exp (r ω) ∂P = 1) :
    (∫ ω, r ω ∂P) - rf + Var[r; P] / 2 = -cov[r, m; P] := by
  have h1 := bp_euler_gaussian hm rf hf
  have h2 : μm + μj + vmr / 2 = 0 := by
    have := bp_euler_gaussian hmr 0 (by simpa [← Real.exp_add] using hj)
    linarith
  have hvar := variance_add (bp_memLp_gaussian hm) (bp_memLp_gaussian hr)
  have hvmr : Var[m + r; P] = vmr := bp_var_gaussian hmr
  rw [hvmr, bp_var_gaussian hm, bp_var_gaussian hr] at hvar
  rw [bp_mean_gaussian hr, bp_var_gaussian hr, covariance_comm]
  linarith

/-- Miao, p. 450: with `u(c) = c^{1−γ}/(1−γ)` the SDF `M = β(C_{t+1}/C_t)^{−γ}` has
`m = ln M = ln β − γΔc`, `Δc = ln(C_{t+1}/C_t)`. -/
theorem bp_ccapm_log_sdf (β γ C C' : ℝ) (hβ : 0 < β) (hC : 0 < C) (hC' : 0 < C') :
    Real.log (β * (C' / C) ^ (-γ)) = Real.log β - γ * Real.log (C' / C) := by
  have hr : 0 < C' / C := div_pos hC' hC
  rw [Real.log_mul hβ.ne' (Real.rpow_pos_of_pos hr _).ne', Real.log_rpow hr]
  ring

/-- With `ε ~ N(0, 1)`, `m = ln β − γ(g + σ_c ε) ~ N(ln β − γg, γ²σ_c²)`. -/
theorem bp_ccapm_m_law {ε : Ω → ℝ} (hε : HasLaw ε (gaussianReal 0 1) P) (β γ g σc : ℝ) :
    HasLaw (fun ω => Real.log β - γ * (g + σc * ε ω))
      (gaussianReal (Real.log β - γ * g) (.mk ((γ * σc) ^ 2) (sq_nonneg _))) P := by
  have h := gaussianReal_const_add (gaussianReal_const_mul hε (-(γ * σc)))
    (Real.log β - γ * g)
  have hf : (fun ω => Real.log β - γ * (g + σc * ε ω)) =
      fun ω => Real.log β - γ * g + -(γ * σc) * ε ω := by
    funext ω
    ring
  rw [hf]
  convert h using 2
  · ring
  · ext
    simp

/-- Miao, (13.35), p. 450: with CRRA utility and `Δc = g + σ_c ε`, `ε ~ N(0, 1)`, the riskfree
rate is `r_f = −ln β + γg − γ²σ_c²/2`. -/
theorem eq_13_35 {ε : Ω → ℝ} (hε : HasLaw ε (gaussianReal 0 1) P) (β γ g σc rf : ℝ)
    (heul : ∫ ω, Real.exp (Real.log β - γ * (g + σc * ε ω)) * Real.exp rf ∂P = 1) :
    rf = -Real.log β + γ * g - γ ^ 2 * σc ^ 2 / 2 := by
  have := bp_euler_gaussian (bp_ccapm_m_law hε β γ g σc) rf heul
  simp only [NNReal.coe_mk] at this
  linarith

/-- The riskfree rate of (13.35) as a function of the parameters. -/
noncomputable def bp_rf (β γ g σc : ℝ) : ℝ := -Real.log β + γ * g - γ ^ 2 * σc ^ 2 / 2

/-- Miao, p. 450: the riskfree rate decreases with the subjective discount factor `β`. -/
theorem eq_13_35_beta (β₁ β₂ γ g σc : ℝ) (h₁ : 0 < β₁) (h : β₁ < β₂) :
    bp_rf β₂ γ g σc < bp_rf β₁ γ g σc := by
  unfold bp_rf
  have := Real.log_lt_log h₁ h
  linarith

/-- Miao, p. 450: the riskfree rate increases with expected consumption growth (`γ > 0`). -/
theorem eq_13_35_growth (β γ g₁ g₂ σc : ℝ) (hγ : 0 < γ) (h : g₁ < g₂) :
    bp_rf β γ g₁ σc < bp_rf β γ g₂ σc := by
  unfold bp_rf
  nlinarith

/-- Miao, p. 451: the riskfree rate decreases with the variance of consumption growth
(precautionary saving, `γ ≠ 0`). -/
theorem eq_13_35_risk (β γ g σ₁ σ₂ : ℝ) (hγ : γ ≠ 0) (h : σ₁ ^ 2 < σ₂ ^ 2) :
    bp_rf β γ g σ₂ < bp_rf β γ g σ₁ := by
  unfold bp_rf
  have : 0 < γ ^ 2 := pow_pos (abs_pos.2 hγ) 2 |>.trans_eq (sq_abs γ)
  nlinarith

/-- Miao, (13.36), p. 450 (corrected): with CRRA utility, `Δc = g + σ_c ε`, `ε ~ N(0, 1)` and
`r_j`, `m + r_j` Gaussian, the equity premium satisfies
`E[r_j − r_f] + σ_j²/2 = γσ_c Cov(r_j, ε)`. -/
theorem eq_13_36 [IsProbabilityMeasure P] {ε r : Ω → ℝ} (hε : HasLaw ε (gaussianReal 0 1) P)
    (β γ g σc : ℝ) {μj : ℝ} {vj vmr : ℝ≥0} (hr : HasLaw r (gaussianReal μj vj) P)
    (hmr : HasLaw (fun ω => Real.log β - γ * (g + σc * ε ω) + r ω)
      (gaussianReal (Real.log β - γ * g + μj) vmr) P) (rf : ℝ)
    (hf : ∫ ω, Real.exp (Real.log β - γ * (g + σc * ε ω)) * Real.exp rf ∂P = 1)
    (hj : ∫ ω, Real.exp (Real.log β - γ * (g + σc * ε ω)) * Real.exp (r ω) ∂P = 1) :
    (∫ ω, r ω ∂P) - rf + Var[r; P] / 2 = γ * σc * cov[r, ε; P] := by
  have hm := bp_ccapm_m_law hε β γ g σc
  rw [eq_13_34 hm hr hmr rf hf hj]
  have hf' : (fun ω => Real.log β - γ * (g + σc * ε ω)) =
      fun ω => Real.log β - γ * g + -(γ * σc) * ε ω := by
    funext ω
    ring
  have hint : Integrable (fun ω => -(γ * σc) * ε ω) P :=
    (hε.integrable (bp_integrable_id_gaussian 0 1)).const_mul _
  rw [hf', covariance_const_add_right hint, covariance_const_mul_right]
  ring

/-- Counterexample to (13.36) as printed (Miao, p. 450). On `Ω = ℝ` with the standard normal
law, `ε = id`, `β = 1/2`, `γ = 1`, `g = 0`, `σ_c = 1/2`, `r_f = ln 2 − 1/8` and
`r_j = ln 2 − 1/8 + ε`: both Euler equations hold, `Cov(r_j, ε) = 1`, and the premium
`E[r_j − r_f] + σ_j²/2` is `γσ_c Cov(r_j, ε) = 1/2`, not `γ Cov(r_j, ε) = 1`. -/
theorem eq_13_36_counterexample :
    let P := gaussianReal 0 1
    let r : ℝ → ℝ := fun x => Real.log 2 - 1 / 8 + x
    let rf : ℝ := Real.log 2 - 1 / 8
    (∫ x, Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x)) * Real.exp rf ∂P = 1) ∧
      (∫ x, Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x)) * Real.exp (r x) ∂P = 1) ∧
      cov[r, id; P] = 1 ∧
      (∫ x, r x ∂P) - rf + Var[r; P] / 2 ≠ 1 * cov[r, id; P] := by
  intro P r rf
  have hε : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) P := HasLaw.id
  have hm := bp_ccapm_m_law hε (1 / 2) 1 0 (1 / 2)
  have hr : HasLaw r (gaussianReal (Real.log 2 - 1 / 8) 1) P := by
    have h := gaussianReal_const_add hε (Real.log 2 - 1 / 8)
    simpa [r] using h
  have hmr : HasLaw (fun x => Real.log (1 / 2) - 1 * (0 + 1 / 2 * x) + r x)
      (gaussianReal (Real.log (1 / 2) - 1 * 0 + (Real.log 2 - 1 / 8))
        (.mk ((1 / 2) ^ 2) (sq_nonneg _))) P := by
    have h := gaussianReal_const_add (gaussianReal_const_mul hε (1 / 2))
      (Real.log (1 / 2) - 1 * 0 + (Real.log 2 - 1 / 8))
    have hfun : (fun x => Real.log (1 / 2) - 1 * (0 + 1 / 2 * x) + r x) =
        fun x => Real.log (1 / 2) - 1 * 0 + (Real.log 2 - 1 / 8) + 1 / 2 * x := by
      funext x
      simp only [r]
      ring
    rw [hfun]
    convert h using 2
    · ring
    · simp
  have hlog : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hf : ∫ x, Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x)) * Real.exp rf ∂P = 1 := by
    rw [integral_mul_const, bp_integral_exp_gaussian hm, ← Real.exp_add, Real.exp_eq_one_iff]
    simp only [NNReal.coe_mk, rf, hlog]
    ring
  have hj : ∫ x, Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x)) * Real.exp (r x) ∂P = 1 := by
    have e : (fun x => Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x)) * Real.exp (r x)) =
        fun x => Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x) + r x) := by
      funext x
      rw [← Real.exp_add]
    rw [e, bp_integral_exp_gaussian hmr, Real.exp_eq_one_iff]
    simp only [NNReal.coe_mk, hlog]
    ring
  have hcov : cov[r, id; P] = 1 := by
    have hint : Integrable (id : ℝ → ℝ) P := bp_integrable_id_gaussian 0 1
    have : r = fun x => (Real.log 2 - 1 / 8) + id x := rfl
    rw [this, covariance_const_add_left hint, covariance_self aemeasurable_id,
      variance_id_gaussianReal, NNReal.coe_one]
  have hmain := eq_13_36 hε (1 / 2) 1 0 (1 / 2) hr hmr rf hf hj
  refine ⟨hf, hj, hcov, ?_⟩
  have hcov' : cov[r, fun x => x; P] = 1 := hcov
  rw [hmain, hcov', hcov]
  norm_num

end Miao.CompleteMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The static CCAPM with exponential utility (Exercise 13.10)

Miao, §13.9, Exercise 13.10 (p. 454): "Consider a static CCAPM with exponential utility and
normally distributed returns. Derive the CAPM."

The representative agent has `u(c) = −e^{−αc}/α` (`α > 0`), so `u'(C) = e^{−αC}` and the first-
order condition for an asset with return `R_j` is `E[e^{−αC}(R_j − R_f)] = 0`. Consumption
`C ~ N(μ, v)` is aggregate wealth `W_0 R_m` (the market return), and joint normality of
`(C, R_j)` is expressed by the regression decomposition `R_j = a_j + κ_j C + e_j` with `e_j`
independent of `C` and square integrable.

* `bp_gaussian_stein`: `E[C e^{tC}] = (μ + vt) E[e^{tC}]` (from the derivative of the moment
  generating function `t ↦ e^{μt + vt²/2}`).
* `ex_13_10_pricing`: `E[R_j] − R_f = α Cov(C, R_j)`.
* `ex_13_10_capm`: with `R_m = C/W_0`, `E[R_j] − R_f = β_j (E[R_m] − R_f)`,
  `β_j = Cov(R_j, R_m)/Var(R_m)`.

The first-order condition is taken as given (it is the static analogue of the Euler equation
derived in `bp_ccapm_euler`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Miao.CompleteMarkets

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
theorem bp_integrableExpSet_gaussian [MeasurableSpace Ω] {P : Measure Ω} {C : Ω → ℝ} {μ : ℝ}
    {v : ℝ≥0} (hC : HasLaw C (gaussianReal μ v) P) : integrableExpSet C P = Set.univ := by
  ext s
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hC.integrable_comp (f := fun x => Real.exp (s * x)) (integrable_exp_mul_gaussianReal s)

/-- A Stein-type identity for a Gaussian `C ~ N(μ, v)`: `E[C e^{tC}] = (μ + vt) E[e^{tC}]`. -/
theorem bp_gaussian_stein {C : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hC : HasLaw C (gaussianReal μ v) P)
    (t : ℝ) :
    ∫ ω, C ω * Real.exp (t * C ω) ∂P = (μ + v * t) * ∫ ω, Real.exp (t * C ω) ∂P := by
  have hint : t ∈ interior (integrableExpSet C P) := by
    rw [bp_integrableExpSet_gaussian hC, interior_univ]
    trivial
  have h1 := hasDerivAt_mgf hint
  have hmgf : mgf C P = fun s => Real.exp (μ * s + v * s ^ 2 / 2) :=
    funext (mgf_gaussianReal hC)
  have h2 : HasDerivAt (fun s => Real.exp (μ * s + v * s ^ 2 / 2))
      (Real.exp (μ * t + v * t ^ 2 / 2) * (μ + v * t)) t := by
    have h3 : HasDerivAt (fun s => μ * s + v * s ^ 2 / 2) (μ + v * t) t := by
      have := ((hasDerivAt_id t).const_mul μ).add
        (((hasDerivAt_pow 2 t).const_mul (v : ℝ)).div_const 2)
      convert this using 1
      · funext s
        simp [mul_div_assoc]
      · simp only [mul_one, Nat.cast_ofNat]
        ring
    exact h3.exp
  rw [hmgf] at h1
  have heq := h1.unique h2
  have hm : ∫ ω, Real.exp (t * C ω) ∂P = Real.exp (μ * t + v * t ^ 2 / 2) :=
    mgf_gaussianReal hC t
  rw [hm, heq]
  ring

/-- **Exercise 13.10**, pricing (Miao, p. 454). With `u'(C) = e^{−αC}`, `C ~ N(μ, v)` and
`R_j = a + κC + e` (`e` independent of `C`, square integrable), the first-order condition
`E[e^{−αC}(R_j − R_f)] = 0` gives `E[R_j] − R_f = α Cov(C, R_j)`. -/
theorem ex_13_10_pricing [IsProbabilityMeasure P] {C e : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hC : HasLaw C (gaussianReal μ v) P) (he : MemLp e 2 P) (hind : IndepFun C e P)
    (α a κ Rf : ℝ)
    (hfoc : ∫ ω, Real.exp (-α * C ω) * (a + κ * C ω + e ω - Rf) ∂P = 0) :
    (∫ ω, (a + κ * C ω + e ω) ∂P) - Rf = α * cov[C, fun ω => a + κ * C ω + e ω; P] := by
  have hint : -α ∈ interior (integrableExpSet C P) := by
    rw [bp_integrableExpSet_gaussian hC, interior_univ]
    trivial
  have I1 : Integrable (fun ω => Real.exp (-α * C ω)) P := by
    have := bp_integrableExpSet_gaussian hC
    have hm : -α ∈ integrableExpSet C P := by rw [this]; trivial
    exact hm
  have I2 : Integrable (fun ω => C ω * Real.exp (-α * C ω)) P := by
    have := integrable_pow_mul_exp_of_mem_interior_integrableExpSet hint 1
    simpa using this
  have hmeas : Measurable (fun x : ℝ => Real.exp (-α * x)) := by fun_prop
  have hind' : IndepFun (fun ω => Real.exp (-α * C ω)) e P :=
    hind.comp hmeas measurable_id
  have Ie : Integrable e P := he.integrable one_le_two
  have I3 : Integrable (fun ω => Real.exp (-α * C ω) * e ω) P := hind'.integrable_mul I1 Ie
  have hE3 : ∫ ω, Real.exp (-α * C ω) * e ω ∂P =
      (∫ ω, Real.exp (-α * C ω) ∂P) * ∫ ω, e ω ∂P :=
    hind'.integral_fun_mul_eq_mul_integral I1.aestronglyMeasurable Ie.aestronglyMeasurable
  have hstein := bp_gaussian_stein hC (-α)
  set E1 := ∫ ω, Real.exp (-α * C ω) ∂P with hE1
  have hE1pos : 0 < E1 := by
    rw [hE1, show (∫ ω, Real.exp (-α * C ω) ∂P) = mgf C P (-α) from rfl,
      mgf_gaussianReal hC]
    exact Real.exp_pos _
  have hsplit : (fun ω => Real.exp (-α * C ω) * (a + κ * C ω + e ω - Rf)) =
      fun ω => ((a - Rf) * Real.exp (-α * C ω) + κ * (C ω * Real.exp (-α * C ω))) +
        Real.exp (-α * C ω) * e ω := by
    funext ω
    ring
  have I12 : Integrable (fun ω => (a - Rf) * Real.exp (-α * C ω) +
      κ * (C ω * Real.exp (-α * C ω))) P := (I1.const_mul _).add (I2.const_mul _)
  rw [hsplit, integral_add I12 I3, integral_add (I1.const_mul _) (I2.const_mul _),
    integral_const_mul, integral_const_mul, hE3, hstein] at hfoc
  have hkey : (a - Rf) + κ * (μ + v * -α) + ∫ ω, e ω ∂P = 0 := by
    have : E1 * ((a - Rf) + κ * (μ + v * -α) + ∫ ω, e ω ∂P) = 0 := by
      rw [← hfoc]
      ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hE1pos.ne'
    · exact h
  have IC : Integrable C P := hC.integrable (bp_integrable_id_gaussian μ v)
  have hmean : ∫ ω, (a + κ * C ω + e ω) ∂P = a + κ * μ + ∫ ω, e ω ∂P := by
    have Iak : Integrable (fun ω => a + κ * C ω) P := (integrable_const a).add (IC.const_mul κ)
    rw [integral_add Iak Ie, integral_add (integrable_const a) (IC.const_mul κ),
      integral_const_mul,
      bp_mean_gaussian hC]
    simp
  have hCm : MemLp C 2 P := bp_memLp_gaussian hC
  have hcov : cov[C, fun ω => a + κ * C ω + e ω; P] = κ * v := by
    have hf : (fun ω => a + κ * C ω + e ω) = fun ω => a + ((fun ω => κ * C ω) + e) ω := by
      funext ω
      simp only [Pi.add_apply]
      ring
    rw [hf, covariance_const_add_right ((IC.const_mul κ).add Ie),
      covariance_add_right hCm (hCm.const_mul κ) he, covariance_const_mul_right,
      covariance_self hC.aemeasurable, bp_var_gaussian hC,
      hind.covariance_eq_zero hCm he]
    ring
  rw [hmean, hcov]
  linarith

/-- **Exercise 13.10**, the CAPM (Miao, p. 454). If consumption is `C = W_0 R_m` (`W_0 > 0`),
`C ~ N(μ, v)` with `v > 0`, and both the market return and asset `j` satisfy the first-order
condition, then `E[R_j] − R_f = β_j(E[R_m] − R_f)` with `β_j = Cov(R_j, R_m)/Var(R_m)`. -/
theorem ex_13_10_capm [IsProbabilityMeasure P] {C e : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hC : HasLaw C (gaussianReal μ v) P) (hv : 0 < (v : ℝ)) (he : MemLp e 2 P)
    (hind : IndepFun C e P) (α a κ Rf W0 : ℝ) (hW0 : 0 < W0)
    (hfoc : ∫ ω, Real.exp (-α * C ω) * (a + κ * C ω + e ω - Rf) ∂P = 0)
    (hfocm : ∫ ω, Real.exp (-α * C ω) * (C ω / W0 - Rf) ∂P = 0) :
    (∫ ω, (a + κ * C ω + e ω) ∂P) - Rf =
      cov[fun ω => a + κ * C ω + e ω, fun ω => C ω / W0; P] /
          cov[fun ω => C ω / W0, fun ω => C ω / W0; P] *
        ((∫ ω, C ω / W0 ∂P) - Rf) := by
  have hj := ex_13_10_pricing hC he hind α a κ Rf hfoc
  have he0 : MemLp (fun _ : Ω => (0 : ℝ)) 2 P := memLp_const 0
  have hind0 : IndepFun C (fun _ : Ω => (0 : ℝ)) P := indepFun_const_right C 0
  have hfocm' : ∫ ω, Real.exp (-α * C ω) * (0 + 1 / W0 * C ω + (fun _ => (0 : ℝ)) ω - Rf) ∂P
      = 0 := by
    have hfun : (fun ω => Real.exp (-α * C ω) * (0 + 1 / W0 * C ω + (fun _ => (0 : ℝ)) ω - Rf)) =
        fun ω => Real.exp (-α * C ω) * (C ω / W0 - Rf) := by
      funext ω
      ring
    rw [hfun]
    exact hfocm
  have hm := ex_13_10_pricing hC he0 hind0 α 0 (1 / W0) Rf hfocm'
  have hfm : (fun ω => 0 + 1 / W0 * C ω + (fun _ => (0 : ℝ)) ω) = fun ω => 1 / W0 * C ω := by
    funext ω
    ring
  have hfm2 : (fun ω => C ω / W0) = fun ω => 1 / W0 * C ω := by
    funext ω
    ring
  rw [hfm] at hm
  rw [hfm2, hm, hj, covariance_const_mul_right, covariance_const_mul_left,
    covariance_const_mul_right, covariance_self hC.aemeasurable, bp_var_gaussian hC,
    covariance_comm (fun ω => a + κ * C ω + e ω)]
  have := hW0.ne'
  have := hv.ne'
  field_simp

end Miao.CompleteMarkets

set_option linter.style.longLine false
#print axioms Miao.CompleteMarkets.POProb
#print axioms Miao.CompleteMarkets.POProb.mk
#print axioms Miao.CompleteMarkets.POProb.pr
#print axioms Miao.CompleteMarkets.POProb.nonneg
#print axioms Miao.CompleteMarkets.POProb.root
#print axioms Miao.CompleteMarkets.POProb.consistent
#print axioms Miao.CompleteMarkets.po_unique_predecessor
#print axioms Miao.CompleteMarkets.po_successor
#print axioms Miao.CompleteMarkets.po_sum_continuations
#print axioms Miao.CompleteMarkets.po_sum_pr_time
#print axioms Miao.CompleteMarkets.po_condPr
#print axioms Miao.CompleteMarkets.po_condPr_sum
#print axioms Miao.CompleteMarkets.po_condPr_root
#print axioms Miao.CompleteMarkets.po_iid
#print axioms Miao.CompleteMarkets.po_Linfty
#print axioms Miao.CompleteMarkets.po_L1
#print axioms Miao.CompleteMarkets.po_Lplus
#print axioms Miao.CompleteMarkets.po_Lplus_subset_Linfty
#print axioms Miao.CompleteMarkets.POEconomy
#print axioms Miao.CompleteMarkets.POEconomy.mk
#print axioms Miao.CompleteMarkets.POEconomy.β
#print axioms Miao.CompleteMarkets.POEconomy.β_pos
#print axioms Miao.CompleteMarkets.POEconomy.β_lt_one
#print axioms Miao.CompleteMarkets.POEconomy.P
#print axioms Miao.CompleteMarkets.POEconomy.u
#print axioms Miao.CompleteMarkets.POEconomy.u_mono
#print axioms Miao.CompleteMarkets.po_w
#print axioms Miao.CompleteMarkets.po_U
#print axioms Miao.CompleteMarkets.po_w_nonneg
#print axioms Miao.CompleteMarkets.po_w_root
#print axioms Miao.CompleteMarkets.po_sum_w_time
#print axioms Miao.CompleteMarkets.po_summable_w
#print axioms Miao.CompleteMarkets.eq_13_1
#print axioms Miao.CompleteMarkets.Assumption13_1_1
#print axioms Miao.CompleteMarkets.assumption_13_1_1_sqrt
#print axioms Miao.CompleteMarkets.po_coin
#print axioms Miao.CompleteMarkets.po_exampleEconomy
#print axioms Miao.CompleteMarkets.po_exampleEconomy_assumption
#print axioms Miao.CompleteMarkets.po_Feasible
#print axioms Miao.CompleteMarkets.po_ParetoOptimal
#print axioms Miao.CompleteMarkets.po_SolvesPlanner
#print axioms Miao.CompleteMarkets.po_tsum_update
#print axioms Miao.CompleteMarkets.po_update_mem
#print axioms Miao.CompleteMarkets.po_U_update
#print axioms Miao.CompleteMarkets.po_perturb
#print axioms Miao.CompleteMarkets.po_perturb_feasible
#print axioms Miao.CompleteMarkets.po_Lplus_comb
#print axioms Miao.CompleteMarkets.po_U_concave
#print axioms Miao.CompleteMarkets.po_U_mono
#print axioms Miao.CompleteMarkets.po_planner_improvement
#print axioms Miao.CompleteMarkets.po_pareto_of_planner_pos
#print axioms Miao.CompleteMarkets.po_transfer_improvement
#print axioms Miao.CompleteMarkets.po_planner_of_pareto
#print axioms Miao.CompleteMarkets.proposition_13_2_1
#print axioms Miao.CompleteMarkets.po_planner_foc
#print axioms Miao.CompleteMarkets.po_planner_foc_ratio
#print axioms Miao.CompleteMarkets.eq_13_3
#print axioms Miao.CompleteMarkets.eq_13_4
#print axioms Miao.CompleteMarkets.po_differentiableAt
#print axioms Miao.CompleteMarkets.po_strictAntiOn_deriv
#print axioms Miao.CompleteMarkets.po_risk_sharing
#print axioms Miao.CompleteMarkets.po_consumption_fn_aggregate
#print axioms Miao.CompleteMarkets.po_no_history_dependence
#print axioms Miao.CompleteMarkets.po_cost
#print axioms Miao.CompleteMarkets.eq_13_5
#print axioms Miao.CompleteMarkets.po_ADEquilibrium
#print axioms Miao.CompleteMarkets.po_cost_update
#print axioms Miao.CompleteMarkets.po_sum_cost
#print axioms Miao.CompleteMarkets.po_tangent
#print axioms Miao.CompleteMarkets.po_deriv_pos
#print axioms Miao.CompleteMarkets.po_utility_gain_le
#print axioms Miao.CompleteMarkets.po_optimal_of_foc
#print axioms Miao.CompleteMarkets.eq_13_6
#print axioms Miao.CompleteMarkets.eq_13_7
#print axioms Miao.CompleteMarkets.eq_13_8
#print axioms Miao.CompleteMarkets.eq_13_9
#print axioms Miao.CompleteMarkets.eq_13_10
#print axioms Miao.CompleteMarkets.po_AD_shadow_price
#print axioms Miao.CompleteMarkets.po_planner_of_foc
#print axioms Miao.CompleteMarkets.po_AD_solves_planner
#print axioms Miao.CompleteMarkets.po_crra_hasDerivAt
#print axioms Miao.CompleteMarkets.example_13_3_1
#print axioms Miao.CompleteMarkets.example_13_3_1_shares
#print axioms Miao.CompleteMarkets.po_negishi_scale
#print axioms Miao.CompleteMarkets.po_negishi_q0
#print axioms Miao.CompleteMarkets.po_negishi_step3
#print axioms Miao.CompleteMarkets.po_negishi_fixed_point
#print axioms Miao.CompleteMarkets.po_local_nonsatiation
#print axioms Miao.CompleteMarkets.theorem_13_3_1
#print axioms Miao.CompleteMarkets.po_pareto_foc
#print axioms Miao.CompleteMarkets.theorem_13_3_2
#print axioms Miao.CompleteMarkets.theorem_13_3_2_counterexample
#print axioms Miao.CompleteMarkets.po_assetPrice
#print axioms Miao.CompleteMarkets.po_assetPrice_summable
#print axioms Miao.CompleteMarkets.po_assetPrice_root
#print axioms Miao.CompleteMarkets.po_assetPrice_eq
#print axioms Miao.CompleteMarkets.po_repSet
#print axioms Miao.CompleteMarkets.po_Ulam
#print axioms Miao.CompleteMarkets.ex_13_1
#print axioms Miao.CompleteMarkets.ex_13_2
#print axioms Miao.CompleteMarkets.ex_13_2_converse
#print axioms Miao.CompleteMarkets.po_example_ADEquilibrium
#print axioms Miao.CompleteMarkets.rd_snoc_injective
#print axioms Miao.CompleteMarkets.rd_paths
#print axioms Miao.CompleteMarkets.rd_mem_paths
#print axioms Miao.CompleteMarkets.rd_dsum
#print axioms Miao.CompleteMarkets.rd_dsum_zero
#print axioms Miao.CompleteMarkets.rd_dsum_succ
#print axioms Miao.CompleteMarkets.rd_dsum_add_len
#print axioms Miao.CompleteMarkets.rd_dsum_succ'
#print axioms Miao.CompleteMarkets.rd_dsum_add
#print axioms Miao.CompleteMarkets.rd_dsum_sub
#print axioms Miao.CompleteMarkets.rd_dsum_neg
#print axioms Miao.CompleteMarkets.rd_dsum_const_mul
#print axioms Miao.CompleteMarkets.rd_dsum_finsetSum
#print axioms Miao.CompleteMarkets.rd_dsum_mono
#print axioms Miao.CompleteMarkets.rd_dsum_nonneg
#print axioms Miao.CompleteMarkets.rd_dsum_congr
#print axioms Miao.CompleteMarkets.rd_abs_dsum_le
#print axioms Miao.CompleteMarkets.rd_le_dsum
#print axioms Miao.CompleteMarkets.rd_dsum_lt
#print axioms Miao.CompleteMarkets.rd_dsum_ite
#print axioms Miao.CompleteMarkets.rd_dsum_le_root
#print axioms Miao.CompleteMarkets.rd_dsum_subtree
#print axioms Miao.CompleteMarkets.rd_dsum_subtree_early
#print axioms Miao.CompleteMarkets.RDTree
#print axioms Miao.CompleteMarkets.RDTree.mk
#print axioms Miao.CompleteMarkets.RDTree.Pr
#print axioms Miao.CompleteMarkets.RDTree.pos
#print axioms Miao.CompleteMarkets.RDTree.root
#print axioms Miao.CompleteMarkets.RDTree.cons
#print axioms Miao.CompleteMarkets.rd_dsum_Pr
#print axioms Miao.CompleteMarkets.rd_uniformTree
#print axioms Miao.CompleteMarkets.rd_condPr
#print axioms Miao.CompleteMarkets.rd_condPr_sum
#print axioms Miao.CompleteMarkets.rd_condE
#print axioms Miao.CompleteMarkets.rd_condE_root
#print axioms Miao.CompleteMarkets.rd_condE_one
#print axioms Miao.CompleteMarkets.rd_Bdd
#print axioms Miao.CompleteMarkets.rd_LinfPos
#print axioms Miao.CompleteMarkets.rd_L1
#print axioms Miao.CompleteMarkets.rd_L1_mul_abs
#print axioms Miao.CompleteMarkets.rd_L1_mul
#print axioms Miao.CompleteMarkets.rd_L1_mul_tendsto
#print axioms Miao.CompleteMarkets.rd_bdd_one
#print axioms Miao.CompleteMarkets.rd_L1_tendsto
#print axioms Miao.CompleteMarkets.rd_bdd_add
#print axioms Miao.CompleteMarkets.rd_bdd_neg
#print axioms Miao.CompleteMarkets.rd_bdd_sub
#print axioms Miao.CompleteMarkets.rd_bdd_const_mul
#print axioms Miao.CompleteMarkets.rd_StrictIncr
#print axioms Miao.CompleteMarkets.rd_Mono
#print axioms Miao.CompleteMarkets.rd_mono_of_strictIncr
#print axioms Miao.CompleteMarkets.rd_EU
#print axioms Miao.CompleteMarkets.rd_abs_dsum_Pr_le
#print axioms Miao.CompleteMarkets.rd_EU_summable
#print axioms Miao.CompleteMarkets.rd_abs_u_le
#print axioms Miao.CompleteMarkets.rd_eq_13_1
#print axioms Miao.CompleteMarkets.rd_fz
#print axioms Miao.CompleteMarkets.rd_prev
#print axioms Miao.CompleteMarkets.rd_net
#print axioms Miao.CompleteMarkets.rd_Budget
#print axioms Miao.CompleteMarkets.eq_13_11
#print axioms Miao.CompleteMarkets.rd_budget_iff_net
#print axioms Miao.CompleteMarkets.rd_prev_add
#print axioms Miao.CompleteMarkets.rd_prev_smul
#print axioms Miao.CompleteMarkets.rd_net_add
#print axioms Miao.CompleteMarkets.rd_arrowPayoff
#print axioms Miao.CompleteMarkets.rd_arrowIn
#print axioms Miao.CompleteMarkets.rd_ArrowBudget
#print axioms Miao.CompleteMarkets.eq_13_12
#print axioms Miao.CompleteMarkets.rd_Ponzi
#print axioms Miao.CompleteMarkets.rd_Arb
#print axioms Miao.CompleteMarkets.rd_ArbOn
#print axioms Miao.CompleteMarkets.rd_OneArb
#print axioms Miao.CompleteMarkets.rd_OneArbOn
#print axioms Miao.CompleteMarkets.rd_ponzi_arb
#print axioms Miao.CompleteMarkets.rd_loc
#print axioms Miao.CompleteMarkets.rd_arb_loc
#print axioms Miao.CompleteMarkets.rd_noArb_noOneArb
#print axioms Miao.CompleteMarkets.rd_noArbOn_noOneArbOn
#print axioms Miao.CompleteMarkets.rd_oneArb_converse_fails
#print axioms Miao.CompleteMarkets.rd_ThetaDC
#print axioms Miao.CompleteMarkets.rd_ThetaBC
#print axioms Miao.CompleteMarkets.rd_ThetaSC
#print axioms Miao.CompleteMarkets.rd_Rec
#print axioms Miao.CompleteMarkets.rd_nonneg_of_forall_lam
#print axioms Miao.CompleteMarkets.rd_rec_DC
#print axioms Miao.CompleteMarkets.rd_rec_BC
#print axioms Miao.CompleteMarkets.rd_rec_SC
#print axioms Miao.CompleteMarkets.rd_loc_mem_recDC
#print axioms Miao.CompleteMarkets.rd_loc_mem_recBC
#print axioms Miao.CompleteMarkets.rd_SeqFeas
#print axioms Miao.CompleteMarkets.rd_Solves
#print axioms Miao.CompleteMarkets.theorem_13_4_1
#print axioms Miao.CompleteMarkets.ex_13_3
#print axioms Miao.CompleteMarkets.rd_simplex
#print axioms Miao.CompleteMarkets.rd_simplex_convex
#print axioms Miao.CompleteMarkets.rd_simplex_compact
#print axioms Miao.CompleteMarkets.rd_stiemke
#print axioms Miao.CompleteMarkets.rd_StatePrice
#print axioms Miao.CompleteMarkets.rd_statePrice_mul
#print axioms Miao.CompleteMarkets.rd_statePrice_dot
#print axioms Miao.CompleteMarkets.rd_qOf
#print axioms Miao.CompleteMarkets.rd_qOf_pos
#print axioms Miao.CompleteMarkets.rd_statePrice_qOf
#print axioms Miao.CompleteMarkets.rd_noOneArb_of_statePrice
#print axioms Miao.CompleteMarkets.rd_arbRow
#print axioms Miao.CompleteMarkets.rd_node_stiemke
#print axioms Miao.CompleteMarkets.theorem_13_4_2
#print axioms Miao.CompleteMarkets.theorem_13_4_2_BC_counterexample
#print axioms Miao.CompleteMarkets.theorem_13_4_2_BC
#print axioms Miao.CompleteMarkets.rd_statePrice_smul
#print axioms Miao.CompleteMarkets.eq_13_17_normalize
#print axioms Miao.CompleteMarkets.rd_deflator
#print axioms Miao.CompleteMarkets.rd_SDF
#print axioms Miao.CompleteMarkets.eq_13_18
#print axioms Miao.CompleteMarkets.rd_statePrice_not_L1
#print axioms Miao.CompleteMarkets.rd_SC_no_statePrice
#print axioms Miao.CompleteMarkets.rd_SC_inequality
#print axioms Miao.CompleteMarkets.rd_multiperiod_price
#print axioms Miao.CompleteMarkets.rd_twoPeriodBond
#print axioms Miao.CompleteMarkets.rd_payoffMatrix
#print axioms Miao.CompleteMarkets.rd_payoffMatrix_transpose_mulVec
#print axioms Miao.CompleteMarkets.rd_payoffMatrix_mulVec
#print axioms Miao.CompleteMarkets.rd_rank_iff_span
#print axioms Miao.CompleteMarkets.rd_rank_iff_injective
#print axioms Miao.CompleteMarkets.rd_CompletePrinted
#print axioms Miao.CompleteMarkets.rd_Complete
#print axioms Miao.CompleteMarkets.rd_rollover
#print axioms Miao.CompleteMarkets.rd_completePrinted_of_pos
#print axioms Miao.CompleteMarkets.ex_13_8_printed_if
#print axioms Miao.CompleteMarkets.ex_13_8_counterexample
#print axioms Miao.CompleteMarkets.rd_backward
#print axioms Miao.CompleteMarkets.ex_13_8
#print axioms Miao.CompleteMarkets.rd_ratio_solves
#print axioms Miao.CompleteMarkets.rd_statePrice_unique
#print axioms Miao.CompleteMarkets.theorem_13_4_3
#print axioms Miao.CompleteMarkets.theorem_13_4_3_formula
#print axioms Miao.CompleteMarkets.theorem_13_4_3_counterexample
#print axioms Miao.CompleteMarkets.rd_arrow_rank
#print axioms Miao.CompleteMarkets.rd_arrow_statePrice
#print axioms Miao.CompleteMarkets.rd_SolvesC
#print axioms Miao.CompleteMarkets.rd_BudgetEq
#print axioms Miao.CompleteMarkets.rd_RadnerDC
#print axioms Miao.CompleteMarkets.rd_RadnerBC
#print axioms Miao.CompleteMarkets.rd_prev_sum
#print axioms Miao.CompleteMarkets.rd_goods_clearing
#print axioms Miao.CompleteMarkets.definition_13_4_1
#print axioms Miao.CompleteMarkets.eq_13_19
#print axioms Miao.CompleteMarkets.eq_13_19_E
#print axioms Miao.CompleteMarkets.eq_13_20
#print axioms Miao.CompleteMarkets.rd_TVC
#print axioms Miao.CompleteMarkets.rd_AD_of_lowerTail_at
#print axioms Miao.CompleteMarkets.rd_AD_of_lowerTail
#print axioms Miao.CompleteMarkets.eq_13_22
#print axioms Miao.CompleteMarkets.eq_13_23
#print axioms Miao.CompleteMarkets.rd_summable_subtree
#print axioms Miao.CompleteMarkets.rd_AD_of_BC
#print axioms Miao.CompleteMarkets.rd_AD_of_DC
#print axioms Miao.CompleteMarkets.rd_ADBudget
#print axioms Miao.CompleteMarkets.rd_ADEqm
#print axioms Miao.CompleteMarkets.rd_Feasible
#print axioms Miao.CompleteMarkets.rd_ParetoOptimal
#print axioms Miao.CompleteMarkets.rd_tsum_add_root
#print axioms Miao.CompleteMarkets.rd_first_welfare
#print axioms Miao.CompleteMarkets.rd_CETVC
#print axioms Miao.CompleteMarkets.definition_13_4_2
#print axioms Miao.CompleteMarkets.rd_cetvc_pareto
#print axioms Miao.CompleteMarkets.rd_W
#print axioms Miao.CompleteMarkets.rd_W_rec
#print axioms Miao.CompleteMarkets.rd_W_dsum
#print axioms Miao.CompleteMarkets.rd_W_tendsto
#print axioms Miao.CompleteMarkets.rd_repl
#print axioms Miao.CompleteMarkets.rd_repl_payoff
#print axioms Miao.CompleteMarkets.rd_repl_value
#print axioms Miao.CompleteMarkets.rd_repl_budget
#print axioms Miao.CompleteMarkets.rd_repl_sum_zero
#print axioms Miao.CompleteMarkets.rd_ad_cetvc
#print axioms Miao.CompleteMarkets.eq_13_24
#print axioms Miao.CompleteMarkets.rd_naturalDebtLimit
#print axioms Miao.CompleteMarkets.rd_naturalDebt_nonbinding
#print axioms Miao.CompleteMarkets.rd_naturalBorrowing
#print axioms Miao.CompleteMarkets.rd_net_loc_self
#print axioms Miao.CompleteMarkets.rd_net_loc_child
#print axioms Miao.CompleteMarkets.rd_net_loc_other
#print axioms Miao.CompleteMarkets.rd_net_loc_bdd
#print axioms Miao.CompleteMarkets.rd_prev_add_loc
#print axioms Miao.CompleteMarkets.rd_EU_pert
#print axioms Miao.CompleteMarkets.rd_euler_dir
#print axioms Miao.CompleteMarkets.rd_Phi
#print axioms Miao.CompleteMarkets.rd_Phi_eq
#print axioms Miao.CompleteMarkets.rd_Phi_neg
#print axioms Miao.CompleteMarkets.rd_euler_eq
#print axioms Miao.CompleteMarkets.rd_DC_slack
#print axioms Miao.CompleteMarkets.rd_arrow_price
#print axioms Miao.CompleteMarkets.rd_arrow_price_common
#print axioms Miao.CompleteMarkets.rd_statePrice_of_euler
#print axioms Miao.CompleteMarkets.rd_GradIneq
#print axioms Miao.CompleteMarkets.rd_gradIneq_of_concave
#print axioms Miao.CompleteMarkets.rd_sqrt_gradIneq
#print axioms Miao.CompleteMarkets.rd_dsum_pow
#print axioms Miao.CompleteMarkets.rd_net_sub
#print axioms Miao.CompleteMarkets.rd_telescope
#print axioms Miao.CompleteMarkets.rd_foc_xi
#print axioms Miao.CompleteMarkets.rd_suff_core
#print axioms Miao.CompleteMarkets.rd_gain_le
#print axioms Miao.CompleteMarkets.ex_13_4_BC_suff
#print axioms Miao.CompleteMarkets.ex_13_4_SC_suff
#print axioms Miao.CompleteMarkets.ex_13_4_DC_suff
#print axioms Miao.CompleteMarkets.ex_13_4_BC_eqm
#print axioms Miao.CompleteMarkets.rd_BC_feas
#print axioms Miao.CompleteMarkets.ex_13_4_BC_foc
#print axioms Miao.CompleteMarkets.ex_13_4_SC_foc
#print axioms Miao.CompleteMarkets.ex_13_4_DC_foc
#print axioms Miao.CompleteMarkets.rd_impPlan
#print axioms Miao.CompleteMarkets.rd_Assumption1351Printed
#print axioms Miao.CompleteMarkets.rd_Assumption1351
#print axioms Miao.CompleteMarkets.rd_assumption1351_of_printed
#print axioms Miao.CompleteMarkets.rd_tsum_subtree
#print axioms Miao.CompleteMarkets.rd_dsum_pow_at
#print axioms Miao.CompleteMarkets.rd_EU_sub_subtree
#print axioms Miao.CompleteMarkets.assumption_13_5_1
#print axioms Miao.CompleteMarkets.assumption_13_5_1_printed_fails
#print axioms Miao.CompleteMarkets.rd_RadnerBCnb
#print axioms Miao.CompleteMarkets.rd_RadnerDCnb
#print axioms Miao.CompleteMarkets.rd_scaled_plan_le
#print axioms Miao.CompleteMarkets.rd_impatience_bound
#print axioms Miao.CompleteMarkets.theorem_13_5_1_if
#print axioms Miao.CompleteMarkets.rd_budget_binds
#print axioms Miao.CompleteMarkets.rd_pv_eq
#print axioms Miao.CompleteMarkets.rd_gradIneq_antitone
#print axioms Miao.CompleteMarkets.theorem_13_5_1_onlyIf
#print axioms Miao.CompleteMarkets.rd_mg
#print axioms Miao.CompleteMarkets.rd_mg_sum
#print axioms Miao.CompleteMarkets.rd_dsum_mg
#print axioms Miao.CompleteMarkets.rd_mg_true
#print axioms Miao.CompleteMarkets.rd_psi
#print axioms Miao.CompleteMarkets.rd_cx_Pr
#print axioms Miao.CompleteMarkets.rd_cxpd
#print axioms Miao.CompleteMarkets.rd_cxp
#print axioms Miao.CompleteMarkets.rd_cx_q
#print axioms Miao.CompleteMarkets.rd_cxθ
#print axioms Miao.CompleteMarkets.rd_psi_cost
#print axioms Miao.CompleteMarkets.rd_psi_payoff
#print axioms Miao.CompleteMarkets.rd_cx_statePrice
#print axioms Miao.CompleteMarkets.rd_cx_L1
#print axioms Miao.CompleteMarkets.rd_cx_EU
#print axioms Miao.CompleteMarkets.rd_cx_budget
#print axioms Miao.CompleteMarkets.rd_psi_unbounded
#print axioms Miao.CompleteMarkets.theorem_13_5_1_counterexample
#print axioms Miao.CompleteMarkets.eq_13_23_counterexample
#print axioms Miao.CompleteMarkets.rd_dsum_unit
#print axioms Miao.CompleteMarkets.rd_exR
#print axioms Miao.CompleteMarkets.rd_exζ
#print axioms Miao.CompleteMarkets.rd_exR_summable
#print axioms Miao.CompleteMarkets.rd_exR_succ
#print axioms Miao.CompleteMarkets.rd_exR_nonneg
#print axioms Miao.CompleteMarkets.rd_exR_tendsto
#print axioms Miao.CompleteMarkets.rd_exR_zero
#print axioms Miao.CompleteMarkets.rd_exqd
#print axioms Miao.CompleteMarkets.rd_exq
#print axioms Miao.CompleteMarkets.rd_exqd_pos
#print axioms Miao.CompleteMarkets.rd_exqd_succ_le
#print axioms Miao.CompleteMarkets.rd_exU
#print axioms Miao.CompleteMarkets.rd_exy
#print axioms Miao.CompleteMarkets.rd_exc
#print axioms Miao.CompleteMarkets.rd_exy_pos
#print axioms Miao.CompleteMarkets.rd_exq_L1
#print axioms Miao.CompleteMarkets.rd_ex_pv
#print axioms Miao.CompleteMarkets.rd_ex_pv_y1
#print axioms Miao.CompleteMarkets.rd_ex_pv_y2
#print axioms Miao.CompleteMarkets.example_13_5_1_AD
#print axioms Miao.CompleteMarkets.rd_exp
#print axioms Miao.CompleteMarkets.example_13_5_1_prices
#print axioms Miao.CompleteMarkets.rd_exθ
#print axioms Miao.CompleteMarkets.rd_ex_value
#print axioms Miao.CompleteMarkets.rd_ex_budget
#print axioms Miao.CompleteMarkets.example_13_5_1_TVC
#print axioms Miao.CompleteMarkets.example_13_5_1_CETVC
#print axioms Miao.CompleteMarkets.example_13_5_1_unlimited
#print axioms Miao.CompleteMarkets.example_13_5_1_not_Radner
#print axioms Miao.CompleteMarkets.example_13_5_1_patience
#print axioms Miao.CompleteMarkets.BPTree
#print axioms Miao.CompleteMarkets.BPTree.mk
#print axioms Miao.CompleteMarkets.BPTree.pr
#print axioms Miao.CompleteMarkets.BPTree.pr_pos
#print axioms Miao.CompleteMarkets.BPTree.pr_nil
#print axioms Miao.CompleteMarkets.BPTree.pr_cons
#print axioms Miao.CompleteMarkets.bp_nodeSum
#print axioms Miao.CompleteMarkets.bp_condExp
#print axioms Miao.CompleteMarkets.bp_pv
#print axioms Miao.CompleteMarkets.bp_nodeSum_zero
#print axioms Miao.CompleteMarkets.bp_nodeSum_succ
#print axioms Miao.CompleteMarkets.bp_nodeSum_congr
#print axioms Miao.CompleteMarkets.bp_nodeSum_add
#print axioms Miao.CompleteMarkets.bp_nodeSum_smul
#print axioms Miao.CompleteMarkets.bp_nodeSum_neg
#print axioms Miao.CompleteMarkets.bp_nodeSum_sub
#print axioms Miao.CompleteMarkets.bp_nodeSum_finsetSum
#print axioms Miao.CompleteMarkets.bp_nodeSum_const
#print axioms Miao.CompleteMarkets.bp_nodeSum_mono
#print axioms Miao.CompleteMarkets.bp_nodeSum_nonneg
#print axioms Miao.CompleteMarkets.bp_nodeSum_eq_zero_iff
#print axioms Miao.CompleteMarkets.bp_nodeSum_single
#print axioms Miao.CompleteMarkets.bp_condExp_zero
#print axioms Miao.CompleteMarkets.bp_condExp_succ
#print axioms Miao.CompleteMarkets.bp_condExp_add
#print axioms Miao.CompleteMarkets.bp_condExp_congr
#print axioms Miao.CompleteMarkets.bp_condExp_add_fun
#print axioms Miao.CompleteMarkets.bp_condExp_smul
#print axioms Miao.CompleteMarkets.bp_condExp_sub_fun
#print axioms Miao.CompleteMarkets.bp_condExp_const
#print axioms Miao.CompleteMarkets.bp_condExp_mono
#print axioms Miao.CompleteMarkets.bp_condExp_nonneg
#print axioms Miao.CompleteMarkets.bp_condExp_finsetSum
#print axioms Miao.CompleteMarkets.bp_nodeSum_condExp
#print axioms Miao.CompleteMarkets.bp_condExp_root
#print axioms Miao.CompleteMarkets.bp_pv_add
#print axioms Miao.CompleteMarkets.bp_pv_mono
#print axioms Miao.CompleteMarkets.bp_pv_nonneg
#print axioms Miao.CompleteMarkets.bp_pv_finsetSum
#print axioms Miao.CompleteMarkets.bp_markovPr
#print axioms Miao.CompleteMarkets.bp_markovTree
#print axioms Miao.CompleteMarkets.eq_13_7_markov
#print axioms Miao.CompleteMarkets.bp_detTree
#print axioms Miao.CompleteMarkets.bp_Prices
#print axioms Miao.CompleteMarkets.bp_fundamental
#print axioms Miao.CompleteMarkets.bp_bubble
#print axioms Miao.CompleteMarkets.bp_forward_mul
#print axioms Miao.CompleteMarkets.eq_13_6_forward
#print axioms Miao.CompleteMarkets.bp_summable_dividends
#print axioms Miao.CompleteMarkets.bp_mul_fundamental
#print axioms Miao.CompleteMarkets.eq_13_6_bubble_limit
#print axioms Miao.CompleteMarkets.eq_13_6_bubble_bounds
#print axioms Miao.CompleteMarkets.eq_13_6_bubble_pos_counterexample
#print axioms Miao.CompleteMarkets.bp_fundamental_prices
#print axioms Miao.CompleteMarkets.eq_13_25
#print axioms Miao.CompleteMarkets.eq_13_25_iterate
#print axioms Miao.CompleteMarkets.bp_bubble_eq_zero_of_root
#print axioms Miao.CompleteMarkets.bp_condExp_congr_length
#print axioms Miao.CompleteMarkets.bp_no_bubble_finite_maturity
#print axioms Miao.CompleteMarkets.BPRadnerEqm
#print axioms Miao.CompleteMarkets.BPRadnerEqm.mk
#print axioms Miao.CompleteMarkets.BPRadnerEqm.cons_nonneg
#print axioms Miao.CompleteMarkets.BPRadnerEqm.budget_root
#print axioms Miao.CompleteMarkets.BPRadnerEqm.budget_succ
#print axioms Miao.CompleteMarkets.BPRadnerEqm.debt
#print axioms Miao.CompleteMarkets.BPRadnerEqm.clear_assets
#print axioms Miao.CompleteMarkets.BPRadnerEqm.clear_goods_root
#print axioms Miao.CompleteMarkets.BPRadnerEqm.clear_goods_succ
#print axioms Miao.CompleteMarkets.bp_pr_mul_condExp_one
#print axioms Miao.CompleteMarkets.bp_nodeSum_succ_mono
#print axioms Miao.CompleteMarkets.bp_pv_payoff
#print axioms Miao.CompleteMarkets.bp_eq_13_20
#print axioms Miao.CompleteMarkets.bp_pv_price_root
#print axioms Miao.CompleteMarkets.bp_summable_pv_of_le
#print axioms Miao.CompleteMarkets.eq_13_26
#print axioms Miao.CompleteMarkets.eq_13_27
#print axioms Miao.CompleteMarkets.bp_exists_agent_slack
#print axioms Miao.CompleteMarkets.theorem_13_6_1
#print axioms Miao.CompleteMarkets.theorem_13_6_1_instance
#print axioms Miao.CompleteMarkets.bp_k08Budget
#print axioms Miao.CompleteMarkets.bp_k08U
#print axioms Miao.CompleteMarkets.bp_k08_martingale
#print axioms Miao.CompleteMarkets.bp_k08_geom
#print axioms Miao.CompleteMarkets.ex_13_7_prices
#print axioms Miao.CompleteMarkets.ex_13_7_bubble
#print axioms Miao.CompleteMarkets.ex_13_7
#print axioms Miao.CompleteMarkets.bp_detBudget
#print axioms Miao.CompleteMarkets.BPDetEqm
#print axioms Miao.CompleteMarkets.BPDetEqm.mk
#print axioms Miao.CompleteMarkets.BPDetEqm.budget
#print axioms Miao.CompleteMarkets.BPDetEqm.adm_self
#print axioms Miao.CompleteMarkets.BPDetEqm.optimal
#print axioms Miao.CompleteMarkets.BPDetEqm.clear_assets
#print axioms Miao.CompleteMarkets.BPDetEqm.clear_goods
#print axioms Miao.CompleteMarkets.bp_detU
#print axioms Miao.CompleteMarkets.bp_detAdm
#print axioms Miao.CompleteMarkets.bp_tail
#print axioms Miao.CompleteMarkets.bp_tail_succ
#print axioms Miao.CompleteMarkets.bp_sum_add_tail
#print axioms Miao.CompleteMarkets.bp_tail_tendsto
#print axioms Miao.CompleteMarkets.bp_tail_nonneg
#print axioms Miao.CompleteMarkets.bp_det_partial
#print axioms Miao.CompleteMarkets.bp_det_sufficiency
#print axioms Miao.CompleteMarkets.bp_log_supergradient
#print axioms Miao.CompleteMarkets.bp_rpow_sub_one_div_le
#print axioms Miao.CompleteMarkets.bp_crra_supergradient
#print axioms Miao.CompleteMarkets.bp_crra_mono
#print axioms Miao.CompleteMarkets.bp_natLimit
#print axioms Miao.CompleteMarkets.bp_borrowCon
#print axioms Miao.CompleteMarkets.bp_crra
#print axioms Miao.CompleteMarkets.bp_payoff_eq
#print axioms Miao.CompleteMarkets.bp_budget_transfer
#print axioms Miao.CompleteMarkets.bp_ex1361_price
#print axioms Miao.CompleteMarkets.bp_ex1361_hold
#print axioms Miao.CompleteMarkets.bp_ex1361_price_pos
#print axioms Miao.CompleteMarkets.example_13_6_1_prices
#print axioms Miao.CompleteMarkets.bp_ex1361_value
#print axioms Miao.CompleteMarkets.example_13_6_1
#print axioms Miao.CompleteMarkets.example_13_6_1_tvc
#print axioms Miao.CompleteMarkets.example_13_6_1_bubble
#print axioms Miao.CompleteMarkets.bp_k5_Y
#print axioms Miao.CompleteMarkets.bp_k5_defl
#print axioms Miao.CompleteMarkets.bp_k5_price
#print axioms Miao.CompleteMarkets.bp_k5_wealth
#print axioms Miao.CompleteMarkets.bp_k5_share
#print axioms Miao.CompleteMarkets.bp_k5_cons
#print axioms Miao.CompleteMarkets.bp_k5_value
#print axioms Miao.CompleteMarkets.bp_k5_hold
#print axioms Miao.CompleteMarkets.bp_k5_Y_pos
#print axioms Miao.CompleteMarkets.bp_k5_defl_pos
#print axioms Miao.CompleteMarkets.bp_k5_defl_zero
#print axioms Miao.CompleteMarkets.bp_k5_marginal
#print axioms Miao.CompleteMarkets.bp_k5_prices
#print axioms Miao.CompleteMarkets.bp_k5_summable_y
#print axioms Miao.CompleteMarkets.bp_k5_pv_pos
#print axioms Miao.CompleteMarkets.bp_k5_share_sum
#print axioms Miao.CompleteMarkets.bp_k5_pv_cons
#print axioms Miao.CompleteMarkets.bp_k5_value_tail
#print axioms Miao.CompleteMarkets.ex_13_5
#print axioms Miao.CompleteMarkets.ex_13_5_continuum
#print axioms Miao.CompleteMarkets.ex_13_5_share_counterexample
#print axioms Miao.CompleteMarkets.ex_13_6
#print axioms Miao.CompleteMarkets.ex_13_6_formulas
#print axioms Miao.CompleteMarkets.ex_13_6_autarky
#print axioms Miao.CompleteMarkets.bp_detParetoOptimal
#print axioms Miao.CompleteMarkets.ex_13_6_pareto
#print axioms Miao.CompleteMarkets.bp_alt
#print axioms Miao.CompleteMarkets.bp_werner_eta
#print axioms Miao.CompleteMarkets.bp_werner_y
#print axioms Miao.CompleteMarkets.bp_werner_c
#print axioms Miao.CompleteMarkets.bp_werner_θ
#print axioms Miao.CompleteMarkets.bp_werner_eta_facts
#print axioms Miao.CompleteMarkets.bp_werner_optimal
#print axioms Miao.CompleteMarkets.bp_werner_adm
#print axioms Miao.CompleteMarkets.bp_alt_succ
#print axioms Miao.CompleteMarkets.example_13_6_2
#print axioms Miao.CompleteMarkets.example_13_6_2_prices
#print axioms Miao.CompleteMarkets.example_13_6_2_binds
#print axioms Miao.CompleteMarkets.example_13_6_2_tvc
#print axioms Miao.CompleteMarkets.example_13_6_2_tvc_21_fails
#print axioms Miao.CompleteMarkets.example_13_6_2_autarky
#print axioms Miao.CompleteMarkets.bp_rceFeasible
#print axioms Miao.CompleteMarkets.bp_rceObj
#print axioms Miao.CompleteMarkets.BPRCE
#print axioms Miao.CompleteMarkets.BPRCE.mk
#print axioms Miao.CompleteMarkets.BPRCE.feasible
#print axioms Miao.CompleteMarkets.BPRCE.value
#print axioms Miao.CompleteMarkets.BPRCE.optimal
#print axioms Miao.CompleteMarkets.BPRCE.clear_goods
#print axioms Miao.CompleteMarkets.BPRCE.clear_assets
#print axioms Miao.CompleteMarkets.BPRCE.invariant
#print axioms Miao.CompleteMarkets.BPRCE.consistent
#print axioms Miao.CompleteMarkets.bp_rce_walras
#print axioms Miao.CompleteMarkets.bp_rce_aggregate_wealth
#print axioms Miao.CompleteMarkets.definition_13_7_1_instance
#print axioms Miao.CompleteMarkets.bp_E
#print axioms Miao.CompleteMarkets.bp_Cov
#print axioms Miao.CompleteMarkets.bp_Var
#print axioms Miao.CompleteMarkets.bp_sd
#print axioms Miao.CompleteMarkets.bp_E_add
#print axioms Miao.CompleteMarkets.bp_E_sub
#print axioms Miao.CompleteMarkets.bp_E_mul_left
#print axioms Miao.CompleteMarkets.bp_E_const
#print axioms Miao.CompleteMarkets.bp_E_finsetSum
#print axioms Miao.CompleteMarkets.bp_Cov_eq_dev
#print axioms Miao.CompleteMarkets.bp_Cov_comm
#print axioms Miao.CompleteMarkets.bp_Cov_affine_left
#print axioms Miao.CompleteMarkets.bp_Cov_sub_const
#print axioms Miao.CompleteMarkets.bp_Cov_sum_left
#print axioms Miao.CompleteMarkets.bp_Var_nonneg
#print axioms Miao.CompleteMarkets.bp_Cov_sq_le
#print axioms Miao.CompleteMarkets.bp_cov_ge_neg_sd
#print axioms Miao.CompleteMarkets.eq_13_30
#print axioms Miao.CompleteMarkets.bp_riskfree
#print axioms Miao.CompleteMarkets.bp_excess
#print axioms Miao.CompleteMarkets.eq_13_31
#print axioms Miao.CompleteMarkets.bp_hansen_jagannathan
#print axioms Miao.CompleteMarkets.bp_capm_market
#print axioms Miao.CompleteMarkets.bp_capm_asset
#print axioms Miao.CompleteMarkets.bp_capm
#print axioms Miao.CompleteMarkets.bp_half
#print axioms Miao.CompleteMarkets.bp_capm_book_beta_counterexample
#print axioms Miao.CompleteMarkets.eq_13_32_cov
#print axioms Miao.CompleteMarkets.bp_factor_pricing
#print axioms Miao.CompleteMarkets.bp_ccapm_euler
#print axioms Miao.CompleteMarkets.bp_ccapm_sdf
#print axioms Miao.CompleteMarkets.ex_13_9_wealth
#print axioms Miao.CompleteMarkets.ex_13_9_sdf
#print axioms Miao.CompleteMarkets.ex_13_9_capm_two_states
#print axioms Miao.CompleteMarkets.bp_third
#print axioms Miao.CompleteMarkets.ex_13_9_capm_counterexample
#print axioms Miao.CompleteMarkets.bp_integrable_id_gaussian
#print axioms Miao.CompleteMarkets.bp_integral_exp_gaussian
#print axioms Miao.CompleteMarkets.bp_mean_gaussian
#print axioms Miao.CompleteMarkets.bp_var_gaussian
#print axioms Miao.CompleteMarkets.bp_memLp_gaussian
#print axioms Miao.CompleteMarkets.bp_euler_gaussian
#print axioms Miao.CompleteMarkets.eq_13_33
#print axioms Miao.CompleteMarkets.eq_13_34
#print axioms Miao.CompleteMarkets.bp_ccapm_log_sdf
#print axioms Miao.CompleteMarkets.bp_ccapm_m_law
#print axioms Miao.CompleteMarkets.eq_13_35
#print axioms Miao.CompleteMarkets.bp_rf
#print axioms Miao.CompleteMarkets.eq_13_35_beta
#print axioms Miao.CompleteMarkets.eq_13_35_growth
#print axioms Miao.CompleteMarkets.eq_13_35_risk
#print axioms Miao.CompleteMarkets.eq_13_36
#print axioms Miao.CompleteMarkets.eq_13_36_counterexample
#print axioms Miao.CompleteMarkets.bp_integrableExpSet_gaussian
#print axioms Miao.CompleteMarkets.bp_gaussian_stein
#print axioms Miao.CompleteMarkets.ex_13_10_pricing
#print axioms Miao.CompleteMarkets.ex_13_10_capm
