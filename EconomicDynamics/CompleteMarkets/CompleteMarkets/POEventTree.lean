/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Order.Filter.AtTopBot.Basic

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
