import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.Integral
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Field
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Contractions for the supremum distance

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Appendix A (§A.2.2, §A.4.2, §A.5.2):
the facts about bounded functions and contractions that Chapter 1 uses.

Value functions live in a set `V` of real functions on a set `X`, such as the bounded measurable
functions `bX` (§A.4.2.4). The supremum distance is handled pointwise: `T` is a `β`-contraction
on `V` when `|v − w| ≤ c` everywhere implies `|Tv − Tw| ≤ βc` everywhere.

* **Banach's theorem on `bX`**: if every element of `V` is bounded and `V` is closed under
  uniform limits, then a `β`-contraction of `V` with `β < 1` has a unique fixed point, and its
  iterates converge to it uniformly from every starting point, at rate `β^n` (global stability,
  §A.2.2.2). The set `bX` of bounded measurable functions is closed under uniform limits.
* An order preserving globally stable map is order stable (Lemma A.5.19): `v ≤ Tv` implies
  `v ≤ v̄` and `Tv ≤ v` implies `v̄ ≤ v`.
* `|α ∨ x − α ∨ y| ≤ |x − y|` (p. 8) and Corollary A.5.13, `|sup f − sup g| ≤ sup |f − g|`.
-/

open Filter Topology Set Function

namespace SargentStachurski.PreludeExamples

variable {X : Type*}

/-- `f` is bounded. -/
def IsBdd (f : X → ℝ) : Prop := ∃ M, ∀ x, |f x| ≤ M

/-- `T` is a `β`-contraction of `V` for the supremum distance (§A.2.2.2). -/
def IsSupContraction (V : Set (X → ℝ)) (T : (X → ℝ) → X → ℝ) (β : ℝ) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, ∀ c : ℝ, (∀ x, |v x - w x| ≤ c) → ∀ x, |T v x - T w x| ≤ β * c

/-- `V` is closed under uniform limits of sequences. -/
def IsUniformlyClosed (V : Set (X → ℝ)) : Prop :=
  ∀ f : ℕ → X → ℝ, (∀ n, f n ∈ V) → ∀ g, TendstoUniformly f g atTop → g ∈ V

theorem isBdd_const (c : ℝ) : IsBdd (fun _ : X => c) := ⟨|c|, fun _ => le_rfl⟩

theorem IsBdd.sub {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) : IsBdd (f - g) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M + N, fun x => ?_⟩
  simp only [Pi.sub_apply]
  exact (abs_sub _ _).trans (add_le_add (hM x) (hN x))

theorem IsBdd.add {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) : IsBdd (f + g) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M + N, fun x => ?_⟩
  simp only [Pi.add_apply]
  exact (abs_add_le _ _).trans (add_le_add (hM x) (hN x))

theorem IsBdd.nonneg_bound {f : X → ℝ} (hf : IsBdd f) : ∃ M, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩

/-- Two bounded functions are within a finite supremum distance. -/
theorem IsBdd.exists_dist {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) :
    ∃ c, 0 ≤ c ∧ ∀ x, |f x - g x| ≤ c := by
  obtain ⟨c, hc0, hc⟩ := (hf.sub hg).nonneg_bound
  exact ⟨c, hc0, hc⟩

variable {V : Set (X → ℝ)} {T : (X → ℝ) → X → ℝ} {β : ℝ}

/-- Iterating the contraction inequality: `|v − w| ≤ c` gives `|Tⁿv − Tⁿw| ≤ βⁿc`. -/
theorem IsSupContraction.iterate (hT : MapsTo T V V) (hc : IsSupContraction V T β)
    {v w : X → ℝ} (hv : v ∈ V) (hw : w ∈ V) {c : ℝ} (hvw : ∀ x, |v x - w x| ≤ c) (n : ℕ) :
    ∀ x, |T^[n] v x - T^[n] w x| ≤ β ^ n * c := by
  induction n with
  | zero => simpa using hvw
  | succ n ih =>
    intro x
    rw [iterate_succ_apply', iterate_succ_apply', pow_succ, mul_comm (β ^ n) β, mul_assoc]
    exact hc _ (hT.iterate n hv) _ (hT.iterate n hw) _ ih x

/-- A contraction has at most one fixed point among bounded functions. -/
theorem IsSupContraction.eq_of_isFixedPt (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc : IsSupContraction V T β) {u w : X → ℝ} (hu : u ∈ V) (hw : w ∈ V) (hub : IsBdd u)
    (hwb : IsBdd w) (hTu : T u = u) (hTw : T w = w) : u = w := by
  obtain ⟨c, -, hcd⟩ := hub.exists_dist hwb
  have key : ∀ n : ℕ, ∀ x, |u x - w x| ≤ β ^ n * c := by
    intro n
    induction n with
    | zero => simpa using hcd
    | succ n ih =>
      intro x
      have := hc u hu w hw _ ih x
      rw [hTu, hTw] at this
      rwa [pow_succ, mul_comm (β ^ n) β, mul_assoc]
  funext x
  have hlim : Tendsto (fun n : ℕ => β ^ n * c) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const c
  have h0 : |u x - w x| ≤ 0 := ge_of_tendsto' hlim fun n => key n x
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-- **Banach's theorem on `bX`**, construction step: from any `v ∈ V` the iterates `Tⁿv`
converge uniformly, at rate `βⁿc/(1 − β)` where `|Tv − v| ≤ c`, to a fixed point of `T` in `V`. -/
theorem IsSupContraction.exists_limit (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hbdd : ∀ v ∈ V, IsBdd v) (hV : IsUniformlyClosed V) (hT : MapsTo T V V)
    (hc : IsSupContraction V T β) {v : X → ℝ} (hv : v ∈ V) :
    ∃ u ∈ V, T u = u ∧ TendstoUniformly (fun n => T^[n] v) u atTop ∧
      ∃ c, 0 ≤ c ∧ ∀ n x, |T^[n] v x - u x| ≤ c * β ^ n / (1 - β) := by
  obtain ⟨c, hc0, hcd⟩ := (hbdd _ (hT hv)).exists_dist (hbdd _ hv)
  -- consecutive iterates are `βⁿc` apart
  have hstep : ∀ n x, dist (T^[n] v x) (T^[n + 1] v x) ≤ c * β ^ n := fun n x => by
    have := hc.iterate hT (hT hv) hv hcd n x
    rw [Real.dist_eq, abs_sub_comm, iterate_succ_apply, mul_comm]
    exact this
  have hlim : ∀ x, ∃ a, Tendsto (fun n => T^[n] v x) atTop (𝓝 a) := fun x =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric β c hβ1 (hstep · x))
  choose u hu using hlim
  have hbound : ∀ n x, |T^[n] v x - u x| ≤ c * β ^ n / (1 - β) := fun n x => by
    rw [← Real.dist_eq]
    exact dist_le_of_le_geometric_of_tendsto β c hβ1 (hstep · x) (hu x) n
  have hrate : Tendsto (fun n : ℕ => c * β ^ n / (1 - β)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul c).div_const (1 - β)
  have hunif : TendstoUniformly (fun n => T^[n] v) u atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 hrate).2 ε hε] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    exact (hbound n x).trans_lt hn
  have huV : u ∈ V := hV _ (fun n => hT.iterate n hv) u hunif
  refine ⟨u, huV, ?_, hunif, c, hc0, hbound⟩
  -- `T u = u`: `T^{n+1} v → u` and `|T u − T^{n+1} v| ≤ β · rate`
  funext x
  have h1 : Tendsto (fun n => T^[n + 1] v x) atTop (𝓝 (u x)) :=
    (hu x).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => T^[n + 1] v x) atTop (𝓝 (T u x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (hrate.const_mul β |>.trans
      (by simp))
    rw [Real.dist_eq, iterate_succ_apply', abs_sub_comm]
    exact hc _ huV _ (hT.iterate n hv) _ (fun y => by
      rw [abs_sub_comm]; exact hbound n y) x
  exact tendsto_nhds_unique h2 h1

/-- **Banach's contraction mapping theorem on `bX`** (§A.2.2.2): a `β`-contraction (`β < 1`) of a
nonempty set `V` of bounded functions closed under uniform limits is globally stable. -/
theorem IsSupContraction.globallyStable (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hbdd : ∀ v ∈ V, IsBdd v) (hV : IsUniformlyClosed V) (hT : MapsTo T V V)
    (hc : IsSupContraction V T β) (hne : V.Nonempty) :
    ∃ u ∈ V, T u = u ∧ (∀ w ∈ V, T w = w → w = u) ∧
      ∀ v ∈ V, TendstoUniformly (fun n => T^[n] v) u atTop := by
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨u, huV, hTu, -, -⟩ := hc.exists_limit hβ0 hβ1 hbdd hV hT hv₀
  refine ⟨u, huV, hTu, fun w hw hTw =>
    hc.eq_of_isFixedPt hβ0 hβ1 hw huV (hbdd w hw) (hbdd u huV) hTw hTu, fun v hv => ?_⟩
  obtain ⟨u', hu'V, hTu', hlim, -⟩ := hc.exists_limit hβ0 hβ1 hbdd hV hT hv
  rwa [hc.eq_of_isFixedPt hβ0 hβ1 hu'V huV (hbdd _ hu'V) (hbdd _ huV) hTu' hTu] at hlim

/-- **Lemma A.5.19**, first half: if `T` is order preserving on `V` and its iterates from `v`
converge to `u`, then `v ≤ Tv` implies `v ≤ u`. -/
theorem le_of_le_map_of_tendsto (hT : MapsTo T V V)
    (hmono : ∀ v ∈ V, ∀ w ∈ V, v ≤ w → T v ≤ T w) {v u : X → ℝ} (hv : v ∈ V)
    (hlim : TendstoUniformly (fun n => T^[n] v) u atTop) (hle : v ≤ T v) : v ≤ u := by
  have hn : ∀ n, v ≤ T^[n] v := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [iterate_succ_apply']
      exact hle.trans (hmono _ hv _ (hT.iterate n hv) ih)
  exact fun x => ge_of_tendsto' (hlim.tendsto_at x) fun n => hn n x

/-- **Lemma A.5.19**, second half: `Tv ≤ v` implies `u ≤ v`. -/
theorem le_of_map_le_of_tendsto (hT : MapsTo T V V)
    (hmono : ∀ v ∈ V, ∀ w ∈ V, v ≤ w → T v ≤ T w) {v u : X → ℝ} (hv : v ∈ V)
    (hlim : TendstoUniformly (fun n => T^[n] v) u atTop) (hle : T v ≤ v) : u ≤ v := by
  have hn : ∀ n, T^[n] v ≤ v := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [iterate_succ_apply']
      exact (hmono _ (hT.iterate n hv) _ hv ih).trans hle
  exact fun x => le_of_tendsto' (hlim.tendsto_at x) fun n => hn n x

/-! ### Bounded measurable functions -/

/-- `bX`: the bounded measurable real functions on a measurable space (§A.4.2.4). -/
def bX (X : Type*) [MeasurableSpace X] : Set (X → ℝ) := {f | Measurable f ∧ IsBdd f}

/-- `bX` is closed under uniform limits. -/
theorem isUniformlyClosed_bX [MeasurableSpace X] : IsUniformlyClosed (bX X) := by
  intro f hf g hg
  refine ⟨measurable_of_tendsto_metrizable (fun n => (hf n).1)
    (tendsto_pi_nhds.2 fun x => hg.tendsto_at x), ?_⟩
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformly_iff.1 hg 1 one_pos).exists
  obtain ⟨M, hM⟩ := (hf N).2
  refine ⟨M + 1, fun x => ?_⟩
  have h := hN x
  rw [Real.dist_eq] at h
  calc |g x| = |f N x + (g x - f N x)| := by ring_nf
    _ ≤ |f N x| + |g x - f N x| := abs_add_le _ _
    _ ≤ M + 1 := add_le_add (hM x) h.le

theorem const_mem_bX [MeasurableSpace X] (c : ℝ) : (fun _ : X => c) ∈ bX X :=
  ⟨measurable_const, isBdd_const c⟩

/-! ### Two elementary inequalities -/

/-- `|α ∨ x − α ∨ y| ≤ |x − y|` (p. 8). -/
theorem abs_max_sub_max_le (α x y : ℝ) : |max α x - max α y| ≤ |x - y| := by
  rw [max_comm α x, max_comm α y]
  exact abs_max_sub_max_le_abs x y α

/-- **Corollary A.5.13** (p. 377), for bounded above families of reals:
`|sup f − sup g| ≤ c` whenever `|f − g| ≤ c` pointwise. -/
theorem abs_ciSup_sub_ciSup_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ} (hf : BddAbove (range f))
    (hg : BddAbove (range g)) {c : ℝ} (hfg : ∀ i, |f i - g i| ≤ c) :
    |(⨆ i, f i) - ⨆ i, g i| ≤ c := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    exact ciSup_le fun i => by
      have := (abs_sub_le_iff.1 (hfg i)).1
      have := le_ciSup hg i
      linarith
  · rw [sub_le_iff_le_add]
    exact ciSup_le fun i => by
      have := (abs_sub_le_iff.1 (hfg i)).2
      have := le_ciSup hf i
      linarith

end SargentStachurski.PreludeExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Contracting dynamic programs

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Chapter 1: the common structure of the
proofs of Theorems 1.1.1 and 1.2.1–1.2.2 (§1.1.1.4, pp. 9–10).

A *contracting dynamic program* is a family of policy operators `T_σ` on a set `V` of bounded
functions closed under uniform limits, each order preserving and a `β`-contraction for the
supremum distance (`β < 1`), such that every `v ∈ V` has a `v`-greedy policy. This is the
setting of the firm problem (§1.1), finite MDPs (§1.2) and the optimal savings problem (§1.3).

* `v_σ` is the unique fixed point of `T_σ` in `V`, the limit of `T_σⁿ v` from every `v ∈ V`.
* The Bellman operator `Tv = T_σ v` for a `v`-greedy `σ` is the pointwise supremum
  `sup_σ T_σ v`, is order preserving and is a `β`-contraction.
* **Theorem 1.1.1** (abstract form): the value function `v* = sup_σ v_σ` is the greatest
  element of `{v_σ}`, the unique solution of the Bellman equation in `V`, and a policy is
  optimal iff it is `v*`-greedy; an optimal policy exists, and `Tᵏv → v*` (VFI).
* **Theorem 1.2.2**: HPI reaches an optimal policy in finitely many steps when the policy set is
  finite, and, when the policy operators shift constants by `β` (`T_σ(v − c) = T_σ v − βc`),
  OPI converges from every starting point.
* **Lemma 1.2.3**: `Tv ≤ v` implies `v* ≤ v`.
-/

open Filter Topology Set Function

namespace SargentStachurski.PreludeExamples

/-- A contracting dynamic program: policy operators `T_σ` on a set `V` of bounded functions. -/
structure ContractingDP (X P : Type*) where
  /-- the candidate value functions -/
  V : Set (X → ℝ)
  /-- the policy operators -/
  T : P → (X → ℝ) → X → ℝ
  /-- the modulus of contraction -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  nonempty : V.Nonempty
  bdd : ∀ v ∈ V, IsBdd v
  closed : IsUniformlyClosed V
  mapsTo : ∀ σ, MapsTo (T σ) V V
  mono : ∀ σ, ∀ v ∈ V, ∀ w ∈ V, v ≤ w → T σ v ≤ T σ w
  contraction : ∀ σ, IsSupContraction V (T σ) β
  exists_greedy : ∀ v ∈ V, ∃ σ, ∀ τ, T τ v ≤ T σ v

namespace ContractingDP

variable {X P : Type*} (D : ContractingDP X P)

/-- Each policy operator is globally stable on `V` (§1.1.1.2). -/
theorem globallyStable (σ : P) :
    ∃ u ∈ D.V, D.T σ u = u ∧ (∀ w ∈ D.V, D.T σ w = w → w = u) ∧
      ∀ v ∈ D.V, TendstoUniformly (fun n => (D.T σ)^[n] v) u atTop :=
  (D.contraction σ).globallyStable D.β_nonneg D.β_lt_one D.bdd D.closed (D.mapsTo σ) D.nonempty

/-- The `σ`-value function: the unique fixed point of `T_σ` in `V`. -/
noncomputable def vσ (σ : P) : X → ℝ := (D.globallyStable σ).choose

theorem vσ_mem (σ : P) : D.vσ σ ∈ D.V := (D.globallyStable σ).choose_spec.1

theorem T_vσ (σ : P) : D.T σ (D.vσ σ) = D.vσ σ := (D.globallyStable σ).choose_spec.2.1

theorem eq_vσ {σ : P} {w : X → ℝ} (hw : w ∈ D.V) (h : D.T σ w = w) : w = D.vσ σ :=
  (D.globallyStable σ).choose_spec.2.2.1 w hw h

theorem tendsto_vσ (σ : P) {v : X → ℝ} (hv : v ∈ D.V) :
    TendstoUniformly (fun n => (D.T σ)^[n] v) (D.vσ σ) atTop :=
  (D.globallyStable σ).choose_spec.2.2.2 v hv

/-- Order stability of `T_σ`: `v ≤ T_σ v` implies `v ≤ v_σ`. -/
theorem le_vσ {σ : P} {v : X → ℝ} (hv : v ∈ D.V) (h : v ≤ D.T σ v) : v ≤ D.vσ σ :=
  le_of_le_map_of_tendsto (D.mapsTo σ) (D.mono σ) hv (D.tendsto_vσ σ hv) h

/-- Order stability of `T_σ`: `T_σ v ≤ v` implies `v_σ ≤ v`. -/
theorem vσ_le {σ : P} {v : X → ℝ} (hv : v ∈ D.V) (h : D.T σ v ≤ v) : D.vσ σ ≤ v :=
  le_of_map_le_of_tendsto (D.mapsTo σ) (D.mono σ) hv (D.tendsto_vσ σ hv) h

/-- `σ` is `v`-greedy: `T_τ v ≤ T_σ v` for every policy `τ`. -/
def IsGreedy (v : X → ℝ) (σ : P) : Prop := ∀ τ, D.T τ v ≤ D.T σ v

include D in
/-- The policy set is nonempty. -/
theorem nonempty_policy : Nonempty P :=
  ⟨(D.exists_greedy _ D.nonempty.some_mem).choose⟩

/-- A chosen `v`-greedy policy (an arbitrary policy off `V`). -/
noncomputable def greedy (v : X → ℝ) : P :=
  @Classical.epsilon P D.nonempty_policy fun σ => v ∈ D.V → D.IsGreedy v σ

theorem isGreedy_greedy {v : X → ℝ} (hv : v ∈ D.V) : D.IsGreedy v (D.greedy v) := by
  obtain ⟨σ, hσ⟩ := D.exists_greedy v hv
  exact @Classical.epsilon_spec P (fun σ => v ∈ D.V → D.IsGreedy v σ) ⟨σ, fun _ => hσ⟩ hv

/-- The Bellman operator `Tv = T_σ v` for the chosen `v`-greedy `σ`. -/
noncomputable def bellman (v : X → ℝ) : X → ℝ := D.T (D.greedy v) v

theorem bellman_mapsTo : MapsTo D.bellman D.V D.V := fun _ hv => D.mapsTo _ hv

theorem T_le_bellman (σ : P) {v : X → ℝ} (hv : v ∈ D.V) : D.T σ v ≤ D.bellman v :=
  D.isGreedy_greedy hv σ

/-- Greedy policies are those attaining the Bellman operator (Exercises 1.1.3 and 1.2.4). -/
theorem isGreedy_iff {v : X → ℝ} (hv : v ∈ D.V) (σ : P) :
    D.IsGreedy v σ ↔ D.T σ v = D.bellman v :=
  ⟨fun h => le_antisymm (D.T_le_bellman σ hv) (h _), fun h τ => h ▸ D.T_le_bellman τ hv⟩

/-- The Bellman operator is the pointwise supremum of the policy operators. -/
theorem bellman_eq_iSup {v : X → ℝ} (hv : v ∈ D.V) (x : X) :
    D.bellman v x = ⨆ σ, D.T σ v x := by
  have := D.nonempty_policy
  refine le_antisymm ?_ (ciSup_le fun σ => D.T_le_bellman σ hv x)
  exact le_ciSup (f := fun σ => D.T σ v x)
    ⟨D.bellman v x, by rintro _ ⟨σ, rfl⟩; exact D.T_le_bellman σ hv x⟩ (D.greedy v)

theorem bellman_mono {v w : X → ℝ} (hv : v ∈ D.V) (hw : w ∈ D.V) (h : v ≤ w) :
    D.bellman v ≤ D.bellman w :=
  (D.mono _ v hv w hw h).trans (D.T_le_bellman _ hw)

/-- The Bellman operator is a `β`-contraction (§1.1.1.3, Exercise 1.2.3). -/
theorem bellman_contraction : IsSupContraction D.V D.bellman D.β := by
  intro v hv w hw c hc x
  have h1 := D.contraction (D.greedy v) v hv w hw c hc x
  have h2 := D.contraction (D.greedy w) v hv w hw c hc x
  have a1 := D.T_le_bellman (D.greedy v) hw x
  have a2 := D.T_le_bellman (D.greedy w) hv x
  rw [abs_le] at h1 h2 ⊢
  simp only [bellman] at a1 a2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem bellman_globallyStable :
    ∃ u ∈ D.V, D.bellman u = u ∧ (∀ w ∈ D.V, D.bellman w = w → w = u) ∧
      ∀ v ∈ D.V, TendstoUniformly (fun n => D.bellman^[n] v) u atTop :=
  D.bellman_contraction.globallyStable D.β_nonneg D.β_lt_one D.bdd D.closed D.bellman_mapsTo
    D.nonempty

/-- The value function `v*`, the fixed point of the Bellman operator. -/
noncomputable def vstar : X → ℝ := D.bellman_globallyStable.choose

theorem vstar_mem : D.vstar ∈ D.V := D.bellman_globallyStable.choose_spec.1

theorem bellman_vstar : D.bellman D.vstar = D.vstar := D.bellman_globallyStable.choose_spec.2.1

theorem eq_vstar {w : X → ℝ} (hw : w ∈ D.V) (h : D.bellman w = w) : w = D.vstar :=
  D.bellman_globallyStable.choose_spec.2.2.1 w hw h

/-- **VFI** (§1.1.1.3): `Tᵏ v → v*` uniformly for every `v ∈ V`. -/
theorem tendsto_bellman_iterate {v : X → ℝ} (hv : v ∈ D.V) :
    TendstoUniformly (fun n => D.bellman^[n] v) D.vstar atTop :=
  D.bellman_globallyStable.choose_spec.2.2.2 v hv

/-- Every `σ`-value function lies below `v*` (the second inequality in the proof of
Theorem 1.1.1). -/
theorem vσ_le_vstar (σ : P) : D.vσ σ ≤ D.vstar :=
  D.vσ_le D.vstar_mem ((D.T_le_bellman σ D.vstar_mem).trans D.bellman_vstar.le)

/-- `σ` attains `v*` iff it is `v*`-greedy. -/
theorem vσ_eq_vstar_iff (σ : P) : D.vσ σ = D.vstar ↔ D.IsGreedy D.vstar σ := by
  rw [D.isGreedy_iff D.vstar_mem, D.bellman_vstar]
  constructor
  · intro h
    rw [← h, D.T_vσ]
  · intro h
    exact (D.eq_vσ D.vstar_mem h).symm

/-- A `σ` is optimal: `v_τ ≤ v_σ` for every `τ`. -/
def IsOptimal (σ : P) : Prop := ∀ τ, D.vσ τ ≤ D.vσ σ

theorem isOptimal_iff (σ : P) : D.IsOptimal σ ↔ D.vσ σ = D.vstar := by
  constructor
  · intro h
    refine le_antisymm (D.vσ_le_vstar σ) ?_
    have hg := (D.vσ_eq_vstar_iff (D.greedy D.vstar)).2 (D.isGreedy_greedy D.vstar_mem)
    exact hg ▸ h _
  · intro h τ
    exact h ▸ D.vσ_le_vstar τ

/-- **Theorem 1.1.1**, abstract form (pp. 6–10): `v*` is the greatest `σ`-value function and the
pointwise supremum of them, it is the unique solution of the Bellman equation in `V`, a policy
is optimal iff it is `v*`-greedy, an optimal policy exists, and VFI converges. -/
theorem optimality :
    IsGreatest (range D.vσ) D.vstar ∧ (∀ x, D.vstar x = ⨆ σ, D.vσ σ x) ∧
      (∀ v ∈ D.V, D.bellman v = v ↔ v = D.vstar) ∧
      (∀ σ, D.IsOptimal σ ↔ D.IsGreedy D.vstar σ) ∧ (∃ σ, D.IsOptimal σ) ∧
      ∀ v ∈ D.V, TendstoUniformly (fun n => D.bellman^[n] v) D.vstar atTop := by
  have hopt := (D.vσ_eq_vstar_iff (D.greedy D.vstar)).2 (D.isGreedy_greedy D.vstar_mem)
  have := D.nonempty_policy
  refine ⟨⟨⟨_, hopt⟩, ?_⟩, fun x => ?_, fun v hv => ⟨D.eq_vstar hv, fun h => h ▸ D.bellman_vstar⟩,
    fun σ => (D.isOptimal_iff σ).trans (D.vσ_eq_vstar_iff σ),
    ⟨_, (D.isOptimal_iff _).2 hopt⟩, fun v hv => D.tendsto_bellman_iterate hv⟩
  · rintro _ ⟨σ, rfl⟩
    exact D.vσ_le_vstar σ
  · refine le_antisymm ?_ (ciSup_le fun σ => D.vσ_le_vstar σ x)
    conv_lhs => rw [← hopt]
    exact le_ciSup ⟨D.vstar x, by rintro _ ⟨σ, rfl⟩; exact D.vσ_le_vstar σ x⟩ _

/-- **Lemma 1.2.3** (p. 25): `Tv ≤ v` implies `v* ≤ v`. -/
theorem vstar_le_of_bellman_le {v : X → ℝ} (hv : v ∈ D.V) (h : D.bellman v ≤ v) :
    D.vstar ≤ v :=
  le_of_map_le_of_tendsto D.bellman_mapsTo (fun _ ha _ hb hab => D.bellman_mono ha hb hab) hv
    (D.tendsto_bellman_iterate hv) h

/-- `v ≤ Tv` implies `v ≤ v*`. -/
theorem le_vstar_of_le_bellman {v : X → ℝ} (hv : v ∈ D.V) (h : v ≤ D.bellman v) :
    v ≤ D.vstar :=
  le_of_le_map_of_tendsto D.bellman_mapsTo (fun _ ha _ hb hab => D.bellman_mono ha hb hab) hv
    (D.tendsto_bellman_iterate hv) h

/-! ### Howard policy iteration -/

/-- HPI (Algorithm 1.2): `σ₀` given and `σ_{k+1}` a `v_{σ_k}`-greedy policy. -/
noncomputable def hpiPolicy (σ₀ : P) : ℕ → P
  | 0 => σ₀
  | k + 1 => D.greedy (D.vσ (hpiPolicy σ₀ k))

/-- HPI values increase. -/
theorem vσ_hpi_le_succ (σ₀ : P) (k : ℕ) :
    D.vσ (D.hpiPolicy σ₀ k) ≤ D.vσ (D.hpiPolicy σ₀ (k + 1)) := by
  set σ := D.hpiPolicy σ₀ k
  refine D.le_vσ (D.vσ_mem σ) ?_
  change D.vσ σ ≤ D.T (D.greedy (D.vσ σ)) (D.vσ σ)
  calc D.vσ σ = D.T σ (D.vσ σ) := (D.T_vσ σ).symm
    _ ≤ _ := D.isGreedy_greedy (D.vσ_mem σ) σ

/-- A repeated HPI value is `v*`. -/
theorem vσ_hpi_eq_vstar {σ₀ : P} {k : ℕ}
    (h : D.vσ (D.hpiPolicy σ₀ (k + 1)) = D.vσ (D.hpiPolicy σ₀ k)) :
    D.vσ (D.hpiPolicy σ₀ k) = D.vstar := by
  set v := D.vσ (D.hpiPolicy σ₀ k)
  refine D.eq_vstar (D.vσ_mem _) ?_
  change D.T (D.greedy v) v = v
  have hτ : D.vσ (D.greedy v) = v := h
  calc D.T (D.greedy v) v = D.T (D.greedy v) (D.vσ (D.greedy v)) := by rw [hτ]
    _ = D.vσ (D.greedy v) := D.T_vσ _
    _ = v := hτ

/-- **Theorem 1.2.2**, HPI part (p. 24): with finitely many policies, HPI reaches `v*` in finitely
many steps, after which every policy it produces is optimal. -/
theorem hpi_terminates [Finite P] (σ₀ : P) :
    ∃ k, ∀ j, k ≤ j → D.vσ (D.hpiPolicy σ₀ j) = D.vstar ∧ D.IsOptimal (D.hpiPolicy σ₀ j) := by
  have hk : ∃ k, D.vσ (D.hpiPolicy σ₀ (k + 1)) = D.vσ (D.hpiPolicy σ₀ k) := by
    by_contra hne
    push Not at hne
    have hsm : StrictMono fun k => D.vσ (D.hpiPolicy σ₀ k) :=
      strictMono_nat_of_lt_succ fun k => lt_of_le_of_ne (D.vσ_hpi_le_succ σ₀ k) (hne k).symm
    obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (D.hpiPolicy σ₀)
    exact hij (hsm.injective (by simp only [heq]))
  obtain ⟨k, hk⟩ := hk
  have h0 := D.vσ_hpi_eq_vstar hk
  have hall : ∀ j, k ≤ j → D.vσ (D.hpiPolicy σ₀ j) = D.vstar := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact h0
    | succ j _ ih =>
      change D.vσ (D.greedy (D.vσ (D.hpiPolicy σ₀ j))) = D.vstar
      rw [ih]
      exact (D.vσ_eq_vstar_iff _).2 (D.isGreedy_greedy D.vstar_mem)
  exact ⟨k, fun j hj => ⟨hall j hj, (D.isOptimal_iff _).2 (hall j hj)⟩⟩

/-! ### Optimistic policy iteration -/

/-- OPI (Algorithm 1.3): `v_{n+1} = T_σ^m v_n` for the chosen `v_n`-greedy `σ`. -/
noncomputable def opi (m : ℕ) (v₀ : X → ℝ) : ℕ → X → ℝ
  | 0 => v₀
  | n + 1 => (D.T (D.greedy (opi m v₀ n)))^[m] (opi m v₀ n)

/-- One OPI step from a point mapped up by `T` (Lemmas 2.2.1–2.2.4 of Chapter 2): if `u ≤ Tu`,
`σ` is `u`-greedy and `m ≥ 1`, then `w = T_σ^m u` satisfies `Tu ≤ w ≤ v*` and `w ≤ Tw`. -/
theorem opi_step {m : ℕ} (hm : 1 ≤ m) {u : X → ℝ} (hu : u ∈ D.V) (hup : u ≤ D.bellman u)
    {σ : P} (hσ : D.IsGreedy u σ) :
    (D.T σ)^[m] u ∈ D.V ∧ D.bellman u ≤ (D.T σ)^[m] u ∧ (D.T σ)^[m] u ≤ D.vstar ∧
      (D.T σ)^[m] u ≤ D.bellman ((D.T σ)^[m] u) := by
  have hTu : D.T σ u = D.bellman u := (D.isGreedy_iff hu σ).1 hσ
  have hle : u ≤ D.T σ u := hTu ▸ hup
  -- the iterates `T_σᵏ u` increase
  have hinc : ∀ k, (D.T σ)^[k] u ≤ (D.T σ)^[k + 1] u := by
    intro k
    induction k with
    | zero => simpa using hle
    | succ k ih =>
      have := D.mono σ _ ((D.mapsTo σ).iterate k hu) _ ((D.mapsTo σ).iterate (k + 1) hu) ih
      simpa only [iterate_succ_apply'] using this
  have hmono : Monotone fun k => (D.T σ)^[k] u := monotone_nat_of_le_succ hinc
  have hwV := (D.mapsTo σ).iterate m hu
  refine ⟨hwV, ?_, ?_, ?_⟩
  · rw [← hTu]
    simpa using hmono hm
  · -- `T_σ^m u ≤ T_σ^m v_σ = v_σ ≤ v*`
    have hvσ := D.le_vσ hu hle
    have : ∀ k, (D.T σ)^[k] u ≤ D.vσ σ := by
      intro k
      induction k with
      | zero => exact hvσ
      | succ k ih =>
        rw [iterate_succ_apply']
        calc D.T σ ((D.T σ)^[k] u) ≤ D.T σ (D.vσ σ) :=
              D.mono σ _ ((D.mapsTo σ).iterate k hu) _ (D.vσ_mem σ) ih
          _ = D.vσ σ := D.T_vσ σ
    exact (this m).trans (D.vσ_le_vstar σ)
  · calc (D.T σ)^[m] u ≤ (D.T σ)^[m + 1] u := hinc m
      _ = D.T σ ((D.T σ)^[m] u) := iterate_succ_apply' _ _ _
      _ ≤ D.bellman ((D.T σ)^[m] u) := D.T_le_bellman σ hwV

/-- **Theorem 1.2.2**, OPI part (p. 24): if each `T_σ` shifts constants by `β`, then for every
`m ≥ 1` and every `v₀ ∈ V` the OPI sequence converges uniformly to `v*`. The proof runs OPI from
`v₀ − c`, which is mapped up by `T`, and squeezes it between `Tⁿ(v₀ − c)` and `v*`. -/
theorem tendsto_opi {m : ℕ} (hm : 1 ≤ m)
    (hshift : ∀ σ, ∀ v ∈ D.V, ∀ c : ℝ, D.T σ (fun x => v x - c) = fun x => D.T σ v x - D.β * c)
    (hVshift : ∀ v ∈ D.V, ∀ c : ℝ, (fun x => v x - c) ∈ D.V) {v₀ : X → ℝ} (hv₀ : v₀ ∈ D.V) :
    TendstoUniformly (D.opi m v₀) D.vstar atTop := by
  set β := D.β
  -- shifting commutes with iterates of `T_σ` and with the greedy choice
  have hiter : ∀ σ k, ∀ v ∈ D.V, ∀ c : ℝ,
      (D.T σ)^[k] (fun x => v x - c) = fun x => (D.T σ)^[k] v x - β ^ k * c := by
    intro σ k
    induction k with
    | zero => intro v _ c; simp
    | succ k ih =>
      intro v hv c
      rw [iterate_succ_apply', iterate_succ_apply', ih v hv c,
        hshift σ _ ((D.mapsTo σ).iterate k hv)]
      funext x
      ring
  have hgreedy : ∀ v ∈ D.V, ∀ c : ℝ, D.IsGreedy (fun x => v x - c) (D.greedy v) := by
    intro v hv c τ x
    rw [hshift τ v hv, hshift _ v hv]
    simp only
    linarith [D.isGreedy_greedy hv τ x]
  have hbshift : ∀ v ∈ D.V, ∀ c : ℝ,
      D.bellman (fun x => v x - c) = fun x => D.bellman v x - β * c := by
    intro v hv c
    rw [← (D.isGreedy_iff (hVshift v hv c) _).1 (hgreedy v hv c), hshift _ v hv]
    rfl
  -- the starting shift
  obtain ⟨c₁, hc₁0, hc₁⟩ := (D.bdd _ (D.bellman_mapsTo hv₀)).exists_dist (D.bdd _ hv₀)
  set c := c₁ / (1 - β)
  have h1β : 0 < 1 - β := sub_pos.2 D.β_lt_one
  have hc0 : 0 ≤ c := div_nonneg hc₁0 h1β.le
  have hcc : c₁ = (1 - β) * c := by rw [mul_div_cancel₀ _ h1β.ne']
  set u : ℕ → X → ℝ := fun n x => D.opi m v₀ n x - β ^ (n * m) * c
  have hu0 : u 0 = fun x => v₀ x - c := by funext x; simp [u, opi]
  have hstep : ∀ n, D.opi m v₀ n ∈ D.V → u (n + 1) =
      (D.T (D.greedy (D.opi m v₀ n)))^[m] (u n) := by
    intro n hn
    have : u n = fun x => D.opi m v₀ n x - β ^ (n * m) * c := rfl
    rw [this, hiter _ m _ hn]
    funext x
    simp only [u, opi]
    rw [add_mul, one_mul, pow_add]
    ring
  have hu0V : u 0 ∈ D.V := hu0 ▸ hVshift v₀ hv₀ c
  -- invariants: `u n ∈ V`, `u n ≤ T(u n)`, `Tⁿ u₀ ≤ u n ≤ v*`, and `opi n ∈ V`
  have hinv : ∀ n, D.opi m v₀ n ∈ D.V ∧ u n ∈ D.V ∧ u n ≤ D.bellman (u n) ∧
      D.bellman^[n] (u 0) ≤ u n ∧ u n ≤ D.vstar := by
    intro n
    induction n with
    | zero =>
      have hup : u 0 ≤ D.bellman (u 0) := by
        rw [hu0, hbshift v₀ hv₀ c]
        intro x
        have := (abs_le.1 (hc₁ x)).1
        simp only
        nlinarith
      exact ⟨hv₀, hu0V, hup, le_rfl, D.le_vstar_of_le_bellman hu0V hup⟩
    | succ n ih =>
      obtain ⟨hon, hun, hup, hlow, -⟩ := ih
      have hσ : D.IsGreedy (u n) (D.greedy (D.opi m v₀ n)) := by
        have := hgreedy _ hon (β ^ (n * m) * c)
        exact this
      obtain ⟨hwV, hTw, hwle, hwup⟩ := D.opi_step hm hun hup hσ
      have hon' : D.opi m v₀ (n + 1) ∈ D.V := (D.mapsTo _).iterate m hon
      rw [← hstep n hon] at hwV hTw hwle hwup
      refine ⟨hon', hwV, hwup, ?_, hwle⟩
      rw [iterate_succ_apply']
      exact (D.bellman_mono (D.bellman_mapsTo.iterate n hu0V) hun hlow).trans hTw
  -- squeeze: `Tⁿ u₀ ≤ u n ≤ v*` and `Tⁿ u₀ → v*`, while `opi n − u n = β^{nm} c → 0`
  have hlim := D.tendsto_bellman_iterate hu0V
  have hpow : Tendsto (fun n : ℕ => β ^ n * c) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one D.β_nonneg D.β_lt_one).mul_const c
  rw [Metric.tendstoUniformly_iff] at hlim ⊢
  intro ε hε
  filter_upwards [hlim (ε / 2) (half_pos hε), (tendsto_order.1 hpow).2 (ε / 2) (half_pos hε)]
    with n hn hn' x
  obtain ⟨-, -, -, hlow, hup⟩ := hinv n
  have h1 := hn x
  have hpm : β ^ (n * m) ≤ β ^ n :=
    pow_le_pow_of_le_one D.β_nonneg D.β_lt_one.le (Nat.le_mul_of_pos_right n hm)
  have hpm' : β ^ (n * m) * c ≤ β ^ n * c := mul_le_mul_of_nonneg_right hpm hc0
  have hpm0 : 0 ≤ β ^ (n * m) * c := mul_nonneg (pow_nonneg D.β_nonneg _) hc0
  have hl := hlow x
  have hu := hup x
  simp only [u] at hl hu
  rw [Real.dist_eq] at h1 ⊢
  rw [abs_lt] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

end ContractingDP

end SargentStachurski.PreludeExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov operators on bounded measurable functions

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §A.5.4 (pp. 385–389), as used in
Chapter 1.

A stochastic kernel `P` on a measurable space `X` (a Markov kernel) acts on bounded measurable
functions by `(Pv)(x) = ∫ v(x') P(x, dx')`. The Markov operator maps `bX` into itself, is linear
and order preserving, fixes constants, and does not increase the supremum distance (`‖P‖ = 1`,
Lemma A.5.30).
-/

open MeasureTheory ProbabilityTheory Set Function

namespace SargentStachurski.PreludeExamples

variable {X : Type*} [MeasurableSpace X]

/-- The Markov operator `(Pv)(x) = ∫ v(x') P(x, dx')` (§A.5.4.2). -/
noncomputable def markovOp (P : Kernel X X) (v : X → ℝ) (x : X) : ℝ := ∫ y, v y ∂(P x)

variable (P : Kernel X X) [IsMarkovKernel P]

theorem integrable_of_mem_bX {v : X → ℝ} (hv : v ∈ bX X) (x : X) : Integrable v (P x) := by
  obtain ⟨M, hM⟩ := hv.2
  exact Integrable.of_bound hv.1.aestronglyMeasurable M (Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact hM y)

omit [IsMarkovKernel P] in
theorem measurable_markovOp {v : X → ℝ} (hv : Measurable v) : Measurable (markovOp P v) :=
  (hv.stronglyMeasurable.integral_kernel (κ := P)).measurable

theorem abs_markovOp_le {v : X → ℝ} {M : ℝ} (hM : ∀ x, |v x| ≤ M) (x : X) :
    |markovOp P v x| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := P x) (f := v) (C := M)
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)
  simpa [markovOp] using this

theorem markovOp_mem_bX {v : X → ℝ} (hv : v ∈ bX X) : markovOp P v ∈ bX X := by
  obtain ⟨M, hM⟩ := hv.2
  exact ⟨measurable_markovOp P hv.1, M, abs_markovOp_le P hM⟩

/-- `P` is order preserving on `bX`. -/
theorem markovOp_mono {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) (h : v ≤ w) :
    markovOp P v ≤ markovOp P w := fun x =>
  integral_mono (integrable_of_mem_bX P hv x) (integrable_of_mem_bX P hw x) h

/-- `P1 = 1`: the Markov operator fixes constants. -/
theorem markovOp_const (c : ℝ) : markovOp P (fun _ => c) = fun _ => c := by
  funext x
  simp [markovOp]

theorem markovOp_add {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) :
    markovOp P (v + w) = markovOp P v + markovOp P w := by
  funext x
  exact integral_add (integrable_of_mem_bX P hv x) (integrable_of_mem_bX P hw x)

theorem markovOp_sub {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) :
    markovOp P (v - w) = markovOp P v - markovOp P w := by
  funext x
  exact integral_sub (integrable_of_mem_bX P hv x) (integrable_of_mem_bX P hw x)

omit [IsMarkovKernel P] in
theorem markovOp_smul (a : ℝ) (v : X → ℝ) : markovOp P (a • v) = a • markovOp P v := by
  funext x
  simp only [markovOp, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul a _

/-- Shifting by a constant: `P(v − c) = Pv − c`. -/
theorem markovOp_sub_const {v : X → ℝ} (hv : v ∈ bX X) (c : ℝ) :
    markovOp P (fun x => v x - c) = fun x => markovOp P v x - c := by
  have := markovOp_sub P hv (const_mem_bX c)
  rw [markovOp_const] at this
  exact this

/-- `‖P‖ = 1` (Lemma A.5.30): `|v − w| ≤ c` gives `|Pv − Pw| ≤ c`. -/
theorem abs_markovOp_sub_le {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) {c : ℝ}
    (h : ∀ x, |v x - w x| ≤ c) (x : X) : |markovOp P v x - markovOp P w x| ≤ c := by
  have := abs_markovOp_le P (v := v - w) h x
  rwa [markovOp_sub P hv hw] at this

end SargentStachurski.PreludeExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Affine maps `v ↦ r + βLv` and the Neumann series

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Theorem A.4.10 and Corollary A.4.11
(pp. 367–368), in the form Chapter 1 uses them: (1.3), (1.17) and (1.44).

An operator `L` on `bX` is *Markov-like* when it maps `bX` into itself, is linear and order
preserving there, and satisfies `|v| ≤ M ⟹ |Lv| ≤ M` (so `‖L‖ ≤ 1`). Markov operators of
stochastic kernels are Markov-like. For `r ∈ bX` and `β ∈ [0, 1)` the map `v ↦ r + βLv` is a
`β`-contraction on `bX`, hence globally stable, and its fixed point is the Neumann series
`∑ₜ βᵗLᵗr = (I − βL)⁻¹r`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Function

namespace SargentStachurski.PreludeExamples

variable {X : Type*} [MeasurableSpace X]

/-- A linear, order preserving operator on `bX` of norm at most one. -/
structure IsMarkovLike (L : (X → ℝ) → X → ℝ) : Prop where
  mapsTo : MapsTo L (bX X) (bX X)
  add : ∀ v ∈ bX X, ∀ w ∈ bX X, L (v + w) = L v + L w
  smul : ∀ a : ℝ, ∀ v ∈ bX X, L (a • v) = a • L v
  mono : ∀ v ∈ bX X, ∀ w ∈ bX X, v ≤ w → L v ≤ L w
  abs_le : ∀ v ∈ bX X, ∀ M : ℝ, (∀ x, |v x| ≤ M) → ∀ x, |L v x| ≤ M

/-- The Markov operator of a stochastic kernel is Markov-like (§A.5.4). -/
theorem isMarkovLike_markovOp (P : Kernel X X) [IsMarkovKernel P] :
    IsMarkovLike (markovOp P) :=
  ⟨fun _ h => markovOp_mem_bX P h, fun _ hv _ hw => markovOp_add P hv hw,
    fun a v _ => markovOp_smul P a v, fun _ hv _ hw h => markovOp_mono P hv hw h,
    fun _ _ _ hM => abs_markovOp_le P hM⟩

namespace IsMarkovLike

variable {L : (X → ℝ) → X → ℝ} (hL : IsMarkovLike L)
include hL

theorem sub {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) : L (v - w) = L v - L w := by
  have hnw : (-1 : ℝ) • w ∈ bX X := by
    obtain ⟨M, hM⟩ := hw.2
    exact ⟨hw.1.const_smul _, M, fun x => by simpa using hM x⟩
  have := hL.add v hv _ hnw
  rw [hL.smul _ w hw] at this
  simpa [sub_eq_add_neg] using this

theorem abs_sub_le {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) {c : ℝ}
    (h : ∀ x, |v x - w x| ≤ c) (x : X) : |L v x - L w x| ≤ c := by
  have hvw : v - w ∈ bX X := ⟨hv.1.sub hw.1, hv.2.sub hw.2⟩
  have := hL.abs_le _ hvw c h x
  rwa [hL.sub hv hw] at this

theorem iterate_mem {r : X → ℝ} (hr : r ∈ bX X) (t : ℕ) : L^[t] r ∈ bX X :=
  hL.mapsTo.iterate t hr

theorem abs_iterate_le {r : X → ℝ} (hr : r ∈ bX X) {M : ℝ} (hM : ∀ x, |r x| ≤ M) (t : ℕ)
    (x : X) : |L^[t] r x| ≤ M := by
  induction t generalizing x with
  | zero => exact hM x
  | succ t ih =>
    rw [iterate_succ_apply']
    exact hL.abs_le _ (hL.iterate_mem hr t) M ih x

end IsMarkovLike

/-- The affine map `v ↦ r + βLv`. -/
def affineOp (r : X → ℝ) (β : ℝ) (L : (X → ℝ) → X → ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => r x + β * L v x

variable {L : (X → ℝ) → X → ℝ} {r : X → ℝ} {β : ℝ}

theorem affineOp_mapsTo (hL : IsMarkovLike L) (hr : r ∈ bX X) (hβ0 : 0 ≤ β) :
    MapsTo (affineOp r β L) (bX X) (bX X) := by
  intro v hv
  obtain ⟨hm, N, hN⟩ := hL.mapsTo hv
  obtain ⟨M, hM⟩ := hr.2
  refine ⟨hr.1.add (measurable_const.mul hm), M + β * N, fun x => ?_⟩
  refine (abs_add_le _ _).trans (add_le_add (hM x) ?_)
  rw [abs_mul, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (hN x) hβ0

theorem affineOp_mono (hL : IsMarkovLike L) (hβ0 : 0 ≤ β) {v w : X → ℝ} (hv : v ∈ bX X)
    (hw : w ∈ bX X) (h : v ≤ w) : affineOp r β L v ≤ affineOp r β L w := fun x =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (hL.mono v hv w hw h x) hβ0)

theorem affineOp_contraction (hL : IsMarkovLike L) (hβ0 : 0 ≤ β) :
    IsSupContraction (bX X) (affineOp r β L) β := by
  intro v hv w hw c h x
  simp only [affineOp, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (hL.abs_sub_le hv hw h x) hβ0

/-- Corollary A.4.11: `v ↦ r + βLv` is globally stable on `bX`. -/
theorem affineOp_globallyStable (hL : IsMarkovLike L) (hr : r ∈ bX X) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    ∃ u ∈ bX X, affineOp r β L u = u ∧ (∀ w ∈ bX X, affineOp r β L w = w → w = u) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => (affineOp r β L)^[n] v) u atTop :=
  (affineOp_contraction hL hβ0).globallyStable hβ0 hβ1 (fun _ h => h.2) isUniformlyClosed_bX
    (affineOp_mapsTo hL hr hβ0) ⟨_, const_mem_bX 0⟩

/-- The `n`-th iterate of `v ↦ r + βLv` from `0` is the partial Neumann sum `∑_{t<n} βᵗLᵗr`. -/
theorem affineOp_iterate_zero (hL : IsMarkovLike L) (hr : r ∈ bX X) (n : ℕ) :
    (affineOp r β L)^[n] (fun _ => 0) = fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x := by
  have hterm : ∀ t, β ^ t • L^[t] r ∈ bX X := fun t => by
    obtain ⟨M, hM⟩ := (hL.iterate_mem hr t).2
    refine ⟨(hL.iterate_mem hr t).1.const_smul _, |β ^ t| * M, fun x => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
  have hsplit : ∀ n, (fun x => ∑ t ∈ Finset.range (n + 1), β ^ t * L^[t] r x) =
      (fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x) + β ^ n • L^[n] r := by
    intro n; funext x; simp [Finset.sum_range_succ]
  have hmem : ∀ n, (fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x) ∈ bX X := by
    intro n
    induction n with
    | zero => simpa using const_mem_bX (X := X) 0
    | succ n ih =>
      rw [hsplit]
      exact ⟨ih.1.add (hterm n).1, ih.2.add (hterm n).2⟩
  -- `L` passes through the partial sums
  have hsumL : ∀ n, L (fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x) =
      fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t + 1] r x := by
    intro n
    induction n with
    | zero =>
      have := hL.smul 0 (fun _ => (0 : ℝ)) (const_mem_bX 0)
      simp only [zero_smul] at this
      simp only [Finset.range_zero, Finset.sum_empty]
      exact this
    | succ n ih =>
      rw [hsplit, hL.add _ (hmem n) _ (hterm n), hL.smul _ _ (hL.iterate_mem hr n), ih]
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_range_succ,
        iterate_succ_apply']
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    funext x
    change r x + β * L (fun y => ∑ t ∈ Finset.range n, β ^ t * L^[t] r y) x = _
    rw [hsumL, Finset.sum_range_succ', Finset.mul_sum, pow_zero, one_mul, iterate_zero_apply,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_succ]
    ring

/-- **The Neumann series** (Theorem A.4.10, as in (1.3), (1.17), (1.44)): the fixed point of
`v ↦ r + βLv` in `bX` is `∑ₜ βᵗLᵗr = (I − βL)⁻¹r`. -/
theorem affineOp_hasSum (hL : IsMarkovLike L) (hr : r ∈ bX X) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u : X → ℝ} (hu : u ∈ bX X) (hfix : affineOp r β L u = u) (x : X) :
    HasSum (fun t => β ^ t * L^[t] r x) (u x) := by
  obtain ⟨M, hM⟩ := hr.2
  have hsum : Summable fun t => β ^ t * L^[t] r x :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one hβ0 hβ1 |>.mul_left M) fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hL.abs_iterate_le hr hM t x) (pow_nonneg hβ0 t)
  obtain ⟨u', -, -, huniq, hlim⟩ := affineOp_globallyStable hL hr hβ0 hβ1
  have hu' := huniq u hu hfix
  have hlimx := (hlim _ (const_mem_bX 0)).tendsto_at x
  simp only [affineOp_iterate_zero hL hr] at hlimx
  rw [← hu'] at hlimx
  exact (tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlimx) ▸ hsum.hasSum

end SargentStachurski.PreludeExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A firm problem

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.1.1 (pp. 2–10).

Profits are `π(X_t)` for a Markov state `(X_t)` with stochastic kernel `P` on a measurable space
`X`, `π ∈ bX`, and `β ∈ [0, 1)`.

* **Valuation** (§1.1.1.1): `v = π + βPv` (1.2) has a unique solution in `bX`, given by the
  Neumann series `v = ∑ₜ βᵗPᵗπ = (I − βP)⁻¹π` (1.3) (Exercise 1.1.1, in its functional form).
* **Control** (§1.1.1.2): the manager may sell the firm for `s`. A policy is a measurable
  `σ : X → {0, 1}` (here `Bool`, `true` meaning sell), with policy operator
  `T_σ v = σs + (1 − σ)(π + βPv)` (1.5), a `β`-contraction on `bX` with fixed point `v_σ`.
* **Theorem 1.1.1** (p. 6): `v* = sup_σ v_σ` is the unique solution in `bX` of the Bellman
  equation `v = s ∨ (π + βPv)` (1.6), an optimal policy exists, and a policy is optimal iff it
  is `v*`-greedy (1.7); Exercises 1.1.2 and 1.1.3; the Bellman operator (1.9) is a
  `β`-contraction and `Tᵏv → v*` (§1.1.1.3); Remark 1.1.2 (sell at ties).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Function

namespace SargentStachurski.PreludeExamples

variable {X : Type*} [MeasurableSpace X]

/-- The firm problem of §1.1.1. -/
structure FirmProblem (X : Type*) [MeasurableSpace X] where
  /-- the stochastic kernel of the state -/
  P : Kernel X X
  isMarkov : IsMarkovKernel P
  /-- the profit function `π` -/
  profit : X → ℝ
  profit_mem : profit ∈ bX X
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the sale price -/
  s : ℝ

/-- Policies (§1.1.1.2): measurable maps `X → {0, 1}`, with `true` meaning sell. -/
def FirmPolicy (X : Type*) [MeasurableSpace X] : Type _ := {σ : X → Bool // Measurable σ}

namespace FirmProblem

variable (F : FirmProblem X)

/-! ### Valuation -/

theorem isMarkovLike_P : IsMarkovLike (markovOp F.P) := by
  have := F.isMarkov
  exact isMarkovLike_markovOp F.P

/-- The valuation operator `v ↦ π + βPv` of (1.2). -/
noncomputable def valOp : (X → ℝ) → X → ℝ := affineOp F.profit F.β (markovOp F.P)

theorem valOp_mapsTo : MapsTo F.valOp (bX X) (bX X) :=
  affineOp_mapsTo F.isMarkovLike_P F.profit_mem F.β_nonneg

theorem valOp_contraction : IsSupContraction (bX X) F.valOp F.β :=
  affineOp_contraction F.isMarkovLike_P F.β_nonneg

/-- (1.2): `v = π + βPv` has a unique solution in `bX`, the limit of iterates from any `v ∈ bX`. -/
theorem valuation_globallyStable :
    ∃ u ∈ bX X, F.valOp u = u ∧ (∀ w ∈ bX X, F.valOp w = w → w = u) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => F.valOp^[n] v) u atTop :=
  affineOp_globallyStable F.isMarkovLike_P F.profit_mem F.β_nonneg F.β_lt_one

/-- The value of the firm, the solution of (1.2). -/
noncomputable def value : X → ℝ := F.valuation_globallyStable.choose

theorem value_mem : F.value ∈ bX X := F.valuation_globallyStable.choose_spec.1

/-- (1.2) and **Exercise 1.1.1** (p. 4): `v = π + βPv`. -/
theorem value_eq (x : X) : F.value x = F.profit x + F.β * markovOp F.P F.value x :=
  (congrFun F.valuation_globallyStable.choose_spec.2.1 x).symm

/-- (1.3) (p. 4): the value of the firm is the Neumann series `v = ∑ₜ βᵗPᵗπ = (I − βP)⁻¹π`. -/
theorem value_hasSum (x : X) :
    HasSum (fun t => F.β ^ t * (markovOp F.P)^[t] F.profit x) (F.value x) :=
  affineOp_hasSum F.isMarkovLike_P F.profit_mem F.β_nonneg F.β_lt_one F.value_mem
    F.valuation_globallyStable.choose_spec.2.1 x

/-! ### Control -/

/-- The policy operator (1.5): `T_σ v = s` where `σ` sells and `π + βPv` where it continues. -/
noncomputable def Tσ (σ : X → Bool) (v : X → ℝ) : X → ℝ :=
  fun x => if σ x then F.s else F.profit x + F.β * markovOp F.P v x

/-- (1.5) in the book's form `T_σ v = σs + (1 − σ)(π + βPv)`, with `σ ∈ {0, 1}`. -/
theorem Tσ_eq (σ : X → Bool) (v : X → ℝ) (x : X) :
    F.Tσ σ v x = (if σ x then 1 else 0) * F.s +
      (1 - if σ x then 1 else 0) * (F.profit x + F.β * markovOp F.P v x) := by
  unfold Tσ
  cases σ x <;> simp

theorem Tσ_mapsTo {σ : X → Bool} (hσ : Measurable σ) : MapsTo (F.Tσ σ) (bX X) (bX X) := by
  intro v hv
  obtain ⟨hm, M, hM⟩ := F.valOp_mapsTo hv
  refine ⟨Measurable.ite (hσ (measurableSet_singleton true)) measurable_const hm,
    max |F.s| M, fun x => ?_⟩
  simp only [Tσ]
  split_ifs
  · exact le_max_left _ _
  · exact (hM x).trans (le_max_right _ _)

theorem Tσ_mono (σ : X → Bool) {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) (h : v ≤ w) :
    F.Tσ σ v ≤ F.Tσ σ w := by
  have := F.isMarkov
  intro x
  simp only [Tσ]
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (markovOp_mono F.P hv hw h x)
      F.β_nonneg)

/-- §1.1.1.2: each `T_σ` is a `β`-contraction on `bX`. -/
theorem Tσ_contraction (σ : X → Bool) : IsSupContraction (bX X) (F.Tσ σ) F.β := by
  intro v hv w hw c h x
  simp only [Tσ]
  split_ifs
  · simpa using mul_nonneg F.β_nonneg ((abs_nonneg _).trans (h x))
  · exact F.valOp_contraction v hv w hw c h x

/-- The policy that sells exactly when `s ≥ π + βPv` is measurable (§2.3.1). -/
theorem measurable_sellPolicy {v : X → ℝ} (hv : v ∈ bX X) :
    Measurable fun x => decide (F.profit x + F.β * markovOp F.P v x ≤ F.s) := by
  refine measurable_to_bool ?_
  have hm := (F.valOp_mapsTo hv).1
  have : (fun x => decide (F.profit x + F.β * markovOp F.P v x ≤ F.s)) ⁻¹' {true} =
      {x | F.valOp v x ≤ F.s} := by
    ext x; simp [valOp, affineOp]
  rw [this]
  exact measurableSet_le hm measurable_const

/-- `T_σ v ≤ s ∨ (π + βPv)`, with equality for the selling policy above. -/
theorem Tσ_le_max (σ : X → Bool) (v : X → ℝ) (x : X) :
    F.Tσ σ v x ≤ max F.s (F.profit x + F.β * markovOp F.P v x) := by
  simp only [Tσ]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem Tσ_sellPolicy (v : X → ℝ) (x : X) :
    F.Tσ (fun x => decide (F.profit x + F.β * markovOp F.P v x ≤ F.s)) v x =
      max F.s (F.profit x + F.β * markovOp F.P v x) := by
  simp only [Tσ]
  by_cases h : F.profit x + F.β * markovOp F.P v x ≤ F.s
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right (le_of_not_ge h)).symm

/-- The firm problem as a contracting dynamic program on `bX`. -/
noncomputable def toDP : ContractingDP X (FirmPolicy X) where
  V := bX X
  T σ := F.Tσ σ.1
  β := F.β
  β_nonneg := F.β_nonneg
  β_lt_one := F.β_lt_one
  nonempty := ⟨_, const_mem_bX 0⟩
  bdd := fun _ h => h.2
  closed := isUniformlyClosed_bX
  mapsTo σ := F.Tσ_mapsTo σ.2
  mono σ _ hv _ hw h := F.Tσ_mono σ.1 hv hw h
  contraction σ := F.Tσ_contraction σ.1
  exists_greedy v hv := ⟨⟨_, F.measurable_sellPolicy hv⟩, fun τ x => by
    change F.Tσ τ.1 v x ≤ F.Tσ _ v x
    rw [F.Tσ_sellPolicy]
    exact F.Tσ_le_max τ.1 v x⟩

/-- The firm's Bellman operator is `Tv = s ∨ (π + βPv)` (1.9). -/
theorem bellman_eq {v : X → ℝ} (hv : v ∈ bX X) (x : X) :
    F.toDP.bellman v x = max F.s (F.profit x + F.β * markovOp F.P v x) := by
  refine le_antisymm (F.Tσ_le_max _ v x) ?_
  rw [← F.Tσ_sellPolicy]
  exact F.toDP.T_le_bellman ⟨_, F.measurable_sellPolicy hv⟩ hv x

/-- `σ` is `v`-greedy in the sense of (1.8): at each `x`, `σ(x)` maximizes
`as + (1 − a)(π(x) + β(Pv)(x))` over `a ∈ {0, 1}`. -/
def IsGreedy (v : X → ℝ) (σ : X → Bool) : Prop :=
  ∀ x, ∀ a : Bool, (if a then F.s else F.profit x + F.β * markovOp F.P v x) ≤ F.Tσ σ v x

/-- (1.8) agrees with greedy policies of the dynamic program (§2.3.1). -/
theorem isGreedy_iff (v : X → ℝ) (σ : FirmPolicy X) :
    F.IsGreedy v σ.1 ↔ F.toDP.IsGreedy v σ := by
  constructor
  · intro h τ x
    change F.Tσ τ.1 v x ≤ F.Tσ σ.1 v x
    have := h x (τ.1 x)
    simp only [Tσ] at this ⊢
    exact this
  · intro h x a
    have := h ⟨fun _ => a, measurable_const⟩ x
    change F.Tσ (fun _ => a) v x ≤ F.Tσ σ.1 v x at this
    simpa only [Tσ] using this

/-- **Exercise 1.1.3** (p. 8): `σ` is `v`-greedy iff `Tv = T_σ v`. -/
theorem isGreedy_iff_bellman {v : X → ℝ} (hv : v ∈ bX X) (σ : FirmPolicy X) :
    F.IsGreedy v σ.1 ↔ F.Tσ σ.1 v = F.toDP.bellman v :=
  (F.isGreedy_iff v σ).trans (F.toDP.isGreedy_iff hv σ)

/-- **Exercise 1.1.2** (p. 6): if `|π| ≤ M` and `|s| ≤ M`, every `σ`-value function satisfies
`|v_σ| ≤ M/(1 − β)`; in particular `v* = sup_σ v_σ` is a well-defined real function. -/
theorem abs_vσ_le {M : ℝ} (hπ : ∀ x, |F.profit x| ≤ M) (hs : |F.s| ≤ M) (σ : FirmPolicy X)
    (x : X) : |F.toDP.vσ σ x| ≤ M / (1 - F.β) := by
  have := F.isMarkov
  have h1β : 0 < 1 - F.β := sub_pos.2 F.β_lt_one
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hs
  set K := M / (1 - F.β)
  have hK : M + F.β * K = K := by
    have : K * (1 - F.β) = M := div_mul_cancel₀ M h1β.ne'
    linear_combination -this
  have hKM : M ≤ K := by
    rw [le_div_iff₀ h1β]; nlinarith [F.β_nonneg]
  have hup : F.toDP.T σ (fun _ => K) ≤ fun _ => K := fun y => by
    change F.Tσ σ.1 _ y ≤ K
    simp only [Tσ, markovOp_const]
    split_ifs
    · exact (le_abs_self _).trans (hs.trans hKM)
    · linarith [(abs_le.1 (hπ y)).2]
  have hdown : (fun _ => -K) ≤ F.toDP.T σ (fun _ => -K) := fun y => by
    change -K ≤ F.Tσ σ.1 _ y
    simp only [Tσ, markovOp_const]
    split_ifs
    · linarith [(abs_le.1 hs).1]
    · linarith [(abs_le.1 (hπ y)).1]
  rw [abs_le]
  exact ⟨F.toDP.le_vσ (const_mem_bX _) hdown x, F.toDP.vσ_le (const_mem_bX _) hup x⟩

/-- **Theorem 1.1.1** (p. 6): the value function `v* = sup_σ v_σ` is the unique `v ∈ bX` solving
the Bellman equation `v = s ∨ (π + βPv)` (1.6); at least one optimal policy exists; a policy is
optimal iff it is `v*`-greedy (1.7); and VFI converges, `Tᵏv → v*` uniformly (§1.1.1.3). -/
theorem theorem_1_1_1 :
    F.toDP.vstar ∈ bX X ∧ (∀ x, F.toDP.vstar x = ⨆ σ, F.toDP.vσ σ x) ∧
      (∀ x, F.toDP.vstar x = max F.s (F.profit x + F.β * markovOp F.P F.toDP.vstar x)) ∧
      (∀ v ∈ bX X, (∀ x, v x = max F.s (F.profit x + F.β * markovOp F.P v x)) →
        v = F.toDP.vstar) ∧
      (∃ σ, F.toDP.IsOptimal σ) ∧ (∀ σ, F.toDP.IsOptimal σ ↔ F.IsGreedy F.toDP.vstar σ.1) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => F.toDP.bellman^[n] v) F.toDP.vstar atTop := by
  obtain ⟨-, hsup, hfix, hopt, hex, hvfi⟩ := F.toDP.optimality
  have hmem : F.toDP.vstar ∈ bX X := F.toDP.vstar_mem
  refine ⟨hmem, hsup, fun x => ?_, fun v hv h => (hfix v hv).1 (funext fun x => ?_), hex,
    fun σ => (hopt σ).trans (F.isGreedy_iff _ σ).symm, hvfi⟩
  · rw [← F.bellman_eq hmem x, F.toDP.bellman_vstar]
  · rw [F.bellman_eq hv x]; exact (h x).symm

/-- **Remark 1.1.2** (p. 7): the policy that sells whenever `s ≥ π + βPv*` is optimal. -/
theorem sellPolicy_optimal :
    F.toDP.IsOptimal ⟨_, F.measurable_sellPolicy F.toDP.vstar_mem⟩ := by
  refine (F.toDP.optimality.2.2.2.1 _).2 ((F.isGreedy_iff _ _).1 fun x a => ?_)
  rw [F.Tσ_sellPolicy]
  cases a
  · exact le_max_right _ _
  · exact le_max_left _ _

end FirmProblem

end SargentStachurski.PreludeExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Beyond risk neutrality

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.1.3 (pp. 12–18) and §1.2.3.2
(pp. 34–35).

* §1.1.3.4: the entropic certainty equivalent `e_γ(μ) = −(1/γ) ln ∫ exp(−γz) μ(dz)`. For
  `γ > 0` it lies below the mean (Jensen's inequality), and for a normal distribution it is
  exactly `m − γσ²/2` (p. 16: "the approximation becomes exact when `Z_σ` is normally
  distributed"). Value-at-risk `VaR_α(Z) = inf {c : ℙ{Z + c < 0} ≤ α}` falls when payoffs rise.
* §1.1.3.6: recursive risk adjustment `v_σ = σs + (1 − σ)(π + βKv_σ)` (1.14). The book asks
  whether `v_σ` is well defined. It is, whenever `K` is order preserving and shifts constants,
  `K(v + c) = Kv + c`: then `K` does not increase the supremum distance, each policy operator is
  a `β`-contraction on `bX`, and the conclusions of Theorem 1.1.1 hold. The entropic operator
  `(Kv)(x) = −(1/γ) ln ∫ exp(−γv(x')) P(x, dx')` qualifies for `γ > 0`.
* The mean-variance operator `Kv = Pv − (γ/2) Var_P(v)` (p. 18) is not order preserving: an
  explicit two-point example.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Function

open scoped NNReal ENNReal

namespace SargentStachurski.PreludeExamples

/-! ### Certainty equivalents for a single payoff -/

/-- The entropic certainty equivalent `e_γ(μ) = −(1/γ) ln ∫ exp(−γz) μ(dz)` (§1.1.3.4). -/
noncomputable def entropicCE (γ : ℝ) (μ : Measure ℝ) : ℝ :=
  -(1 / γ) * Real.log (∫ z, Real.exp (-γ * z) ∂μ)

/-- §1.1.3.4 (p. 16): for a normal payoff `N(m, σ²)`, `e_γ = m − γσ²/2` exactly. -/
theorem entropicCE_gaussianReal {γ : ℝ} (hγ : γ ≠ 0) (m : ℝ) (v : ℝ≥0) :
    entropicCE γ (gaussianReal m v) = m - γ * v / 2 := by
  have h : ∫ z, Real.exp (-γ * z) ∂(gaussianReal m v) =
      Real.exp (m * -γ + v * (-γ) ^ 2 / 2) := by
    have := congrFun (mgf_id_gaussianReal (μ := m) (v := v)) (-γ)
    rw [mgf] at this
    simpa using this
  rw [entropicCE, h, Real.log_exp]
  field_simp
  ring

/-- §1.1.3.4 (p. 15): for `γ > 0`, the decision maker values a risky payoff below its mean,
`e_γ(μ) ≤ ∫ z μ(dz)`. -/
theorem entropicCE_le_integral {γ : ℝ} (hγ : 0 < γ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : ℝ => z) μ) (he : Integrable (fun z => Real.exp (-γ * z)) μ) :
    entropicCE γ μ ≤ ∫ z, z ∂μ := by
  have hj := convexOn_exp.map_integral_le (μ := μ) (f := fun z => -γ * z)
    Real.continuous_exp.continuousOn isClosed_univ (Eventually.of_forall fun _ => mem_univ _)
    (hi.const_mul (-γ)) he
  rw [integral_const_mul] at hj
  have hpos : 0 < ∫ z, Real.exp (-γ * z) ∂μ := (Real.exp_pos _).trans_le hj
  have hlog : -γ * ∫ z, z ∂μ ≤ Real.log (∫ z, Real.exp (-γ * z) ∂μ) :=
    (Real.le_log_iff_exp_le hpos).2 hj
  rw [entropicCE]
  have : 1 / γ * (-γ * ∫ z, z ∂μ) = -∫ z, z ∂μ := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog (one_div_nonneg.2 hγ.le)]

/-- Value-at-risk `VaR_α(Z) = inf {c ∈ ℝ : ℙ{Z + c < 0} ≤ α}` (§1.1.3.4). -/
noncomputable def valueAtRisk {Ω : Type*} [MeasurableSpace Ω] (α : ℝ≥0∞) (μ : Measure Ω)
    (Z : Ω → ℝ) : ℝ :=
  sInf {c : ℝ | μ {ω | Z ω + c < 0} ≤ α}

/-- §1.1.3.4 (p. 16): a payoff with less downside needs a smaller cash injection: if `Z ≤ Z'`
then `VaR_α(Z') ≤ VaR_α(Z)` (whenever both infima are over nonempty sets bounded below). -/
theorem valueAtRisk_anti {Ω : Type*} [MeasurableSpace Ω] {α : ℝ≥0∞} {μ : Measure Ω}
    {Z Z' : Ω → ℝ} (h : ∀ ω, Z ω ≤ Z' ω)
    (hne : {c : ℝ | μ {ω | Z ω + c < 0} ≤ α}.Nonempty)
    (hbdd : BddBelow {c : ℝ | μ {ω | Z' ω + c < 0} ≤ α}) :
    valueAtRisk α μ Z' ≤ valueAtRisk α μ Z := by
  refine csInf_le_csInf hbdd hne fun c hc => ?_
  refine (measure_mono fun ω (hω : Z' ω + c < 0) => ?_).trans hc
  change Z ω + c < 0
  linarith [h ω]

/-! ### Recursive risk adjustment -/

variable {X : Type*} [MeasurableSpace X]

/-- An operator `K` on `bX` that is order preserving and shifts constants, `K(v + c) = Kv + c`,
like a certainty equivalent. -/
structure IsShiftMonotone (K : (X → ℝ) → X → ℝ) : Prop where
  mapsTo : MapsTo K (bX X) (bX X)
  mono : ∀ v ∈ bX X, ∀ w ∈ bX X, v ≤ w → K v ≤ K w
  shift : ∀ v ∈ bX X, ∀ c : ℝ, K (fun x => v x + c) = fun x => K v x + c

/-- An order preserving, constant-shifting operator does not increase the supremum distance. -/
theorem IsShiftMonotone.abs_sub_le {K : (X → ℝ) → X → ℝ} (hK : IsShiftMonotone K) {v w : X → ℝ}
    (hv : v ∈ bX X) (hw : w ∈ bX X) {c : ℝ} (h : ∀ x, |v x - w x| ≤ c) (x : X) :
    |K v x - K w x| ≤ c := by
  have hwc : ∀ d : ℝ, (fun x => w x + d) ∈ bX X := fun d =>
    ⟨hw.1.add measurable_const, hw.2.add (isBdd_const d)⟩
  have h1 : K v ≤ fun x => K w x + c := by
    rw [← hK.shift w hw c]
    exact hK.mono v hv _ (hwc c) fun y => by linarith [(abs_le.1 (h y)).2]
  have h2 : (fun x => K w x + -c) ≤ K v := by
    rw [← hK.shift w hw (-c)]
    exact hK.mono _ (hwc (-c)) v hv fun y => by linarith [(abs_le.1 (h y)).1]
  rw [abs_le]
  constructor
  · linarith [h2 x]
  · linarith [h1 x]

namespace FirmProblem

variable (F : FirmProblem X)

/-- The risk-adjusted policy operator (1.14): `T_σ v = σs + (1 − σ)(π + βKv)`. -/
noncomputable def TσK (K : (X → ℝ) → X → ℝ) (σ : X → Bool) (v : X → ℝ) : X → ℝ :=
  fun x => if σ x then F.s else F.profit x + F.β * K v x

/-- §1.1.3.6: with an order preserving, constant-shifting `K`, the risk-adjusted firm problem
(1.14) is a contracting dynamic program on `bX`; in particular every `v_σ` is well defined. -/
noncomputable def toDPK {K : (X → ℝ) → X → ℝ} (hK : IsShiftMonotone K) :
    ContractingDP X (FirmPolicy X) where
  V := bX X
  T σ := F.TσK K σ.1
  β := F.β
  β_nonneg := F.β_nonneg
  β_lt_one := F.β_lt_one
  nonempty := ⟨_, const_mem_bX 0⟩
  bdd := fun _ h => h.2
  closed := isUniformlyClosed_bX
  mapsTo σ v hv := by
    obtain ⟨hm, N, hN⟩ := hK.mapsTo hv
    obtain ⟨M, hM⟩ := F.profit_mem.2
    refine ⟨Measurable.ite (σ.2 (measurableSet_singleton true)) measurable_const
      (F.profit_mem.1.add (measurable_const.mul hm)), max |F.s| (M + F.β * N), fun x => ?_⟩
    simp only [TσK]
    split_ifs
    · exact le_max_left _ _
    · refine (abs_add_le _ _).trans (le_max_of_le_right (add_le_add (hM x) ?_))
      rw [abs_mul, abs_of_nonneg F.β_nonneg]
      exact mul_le_mul_of_nonneg_left (hN x) F.β_nonneg
  mono σ v hv w hw h x := by
    simp only [TσK]
    split_ifs
    · exact le_rfl
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hK.mono v hv w hw h x) F.β_nonneg)
  contraction σ v hv w hw c h x := by
    simp only [TσK]
    split_ifs
    · simpa using mul_nonneg F.β_nonneg ((abs_nonneg _).trans (h x))
    · rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg F.β_nonneg]
      exact mul_le_mul_of_nonneg_left (hK.abs_sub_le hv hw h x) F.β_nonneg
  exists_greedy v hv := by
    obtain ⟨hm, -⟩ := hK.mapsTo hv
    have hmeas : Measurable fun x => decide (F.profit x + F.β * K v x ≤ F.s) := by
      refine measurable_to_bool ?_
      have : (fun x => decide (F.profit x + F.β * K v x ≤ F.s)) ⁻¹' {true} =
          {x | F.profit x + F.β * K v x ≤ F.s} := by ext x; simp
      rw [this]
      exact measurableSet_le (F.profit_mem.1.add (measurable_const.mul hm)) measurable_const
    refine ⟨⟨_, hmeas⟩, fun τ x => ?_⟩
    change F.TσK K τ.1 v x ≤ F.TσK K _ v x
    simp only [TσK]
    by_cases hx : F.profit x + F.β * K v x ≤ F.s
    · simp only [hx, decide_true, ↓reduceIte]
      split_ifs
      · exact le_rfl
      · exact hx
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · exact (le_of_not_ge hx)
      · exact le_rfl

/-- §1.1.3.6: Theorem 1.1.1 for the risk-adjusted firm (1.14). Each `v_σ` is the unique solution
of (1.14) in `bX`; `v* = sup_σ v_σ` uniquely solves `v = s ∨ (π + βKv)` in `bX`; an optimal
policy exists and a policy is optimal iff it is `v*`-greedy; VFI converges. -/
theorem riskAdjusted_optimality {K : (X → ℝ) → X → ℝ} (hK : IsShiftMonotone K) :
    (∀ σ, (F.toDPK hK).vσ σ ∈ bX X ∧ ∀ w ∈ bX X, F.TσK K σ.1 w = w → w = (F.toDPK hK).vσ σ) ∧
      IsGreatest (range (F.toDPK hK).vσ) (F.toDPK hK).vstar ∧
      (∀ v ∈ bX X, (F.toDPK hK).bellman v = v ↔ v = (F.toDPK hK).vstar) ∧
      (∀ σ, (F.toDPK hK).IsOptimal σ ↔ (F.toDPK hK).IsGreedy (F.toDPK hK).vstar σ) ∧
      (∃ σ, (F.toDPK hK).IsOptimal σ) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => (F.toDPK hK).bellman^[n] v)
        (F.toDPK hK).vstar atTop := by
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := (F.toDPK hK).optimality
  exact ⟨fun σ => ⟨(F.toDPK hK).vσ_mem σ, fun w hw h => (F.toDPK hK).eq_vσ hw h⟩, h1, h3, h4,
    h5, h6⟩

end FirmProblem

/-! ### The entropic operator -/

/-- The entropic risk operator `(Kv)(x) = −(1/γ) ln ∫ exp(−γv(x')) P(x, dx')` (§1.1.3.6). -/
noncomputable def entropicOp (γ : ℝ) (P : ProbabilityTheory.Kernel X X) (v : X → ℝ) (x : X) : ℝ :=
  -(1 / γ) * Real.log (∫ y, Real.exp (-γ * v y) ∂(P x))

/-- §1.1.3.6: for `γ > 0` the entropic operator is order preserving on `bX` and shifts
constants, so the entropic version of (1.14) is well defined and Theorem 1.1.1 holds for it. -/
theorem isShiftMonotone_entropicOp {γ : ℝ} (hγ : 0 < γ) (P : ProbabilityTheory.Kernel X X)
    [IsMarkovKernel P] : IsShiftMonotone (entropicOp γ P) := by
  -- `exp(−γv) ∈ bX` and its integral is positive
  have hexp : ∀ v ∈ bX X, (fun y => Real.exp (-γ * v y)) ∈ bX X := by
    intro v hv
    obtain ⟨M, hM⟩ := hv.2
    refine ⟨(measurable_const.mul hv.1).exp, Real.exp (γ * M), fun y => ?_⟩
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by nlinarith [(abs_le.1 (hM y)).1])
  have hpos : ∀ v ∈ bX X, ∀ x, 0 < ∫ y, Real.exp (-γ * v y) ∂(P x) := by
    intro v hv x
    obtain ⟨M, hM⟩ := hv.2
    have hle : ∫ _y, Real.exp (-γ * M) ∂(P x) ≤ ∫ y, Real.exp (-γ * v y) ∂(P x) :=
      integral_mono (integrable_const _) (integrable_of_mem_bX P (hexp v hv) x) fun y =>
        Real.exp_le_exp.2 (by nlinarith [(abs_le.1 (hM y)).2])
    simp only [integral_const, probReal_univ, one_smul] at hle
    exact (Real.exp_pos _).trans_le hle
  refine ⟨fun v hv => ?_, fun v hv w hw h x => ?_, fun v hv c => ?_⟩
  · -- measurable and bounded
    obtain ⟨M, hM⟩ := hv.2
    have hmI : Measurable fun x => ∫ y, Real.exp (-γ * v y) ∂(P x) :=
      measurable_markovOp P (hexp v hv).1
    refine ⟨measurable_const.mul (Real.measurable_log.comp hmI), |M|, fun x => ?_⟩
    have hvM : ∀ y, |v y| ≤ |M| := fun y => (hM y).trans (le_abs_self M)
    have hlo : ∫ _y, Real.exp (-γ * |M|) ∂(P x) ≤ ∫ y, Real.exp (-γ * v y) ∂(P x) :=
      integral_mono (integrable_const _) (integrable_of_mem_bX P (hexp v hv) x) fun y =>
        Real.exp_le_exp.2 (by
          nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 (hvM y)).2 hγ.le])
    have hhi : ∫ y, Real.exp (-γ * v y) ∂(P x) ≤ ∫ _y, Real.exp (γ * |M|) ∂(P x) :=
      integral_mono (integrable_of_mem_bX P (hexp v hv) x) (integrable_const _) fun y =>
        Real.exp_le_exp.2 (by
          nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 (hvM y)).1 hγ.le])
    simp only [integral_const, probReal_univ, one_smul] at hlo hhi
    have l1 := Real.log_le_log (Real.exp_pos _) hlo
    have l2 := Real.log_le_log (hpos v hv x) hhi
    rw [Real.log_exp] at l1 l2
    simp only [entropicOp]
    rw [abs_le]
    have hγ' : 0 < 1 / γ := one_div_pos.2 hγ
    constructor
    · have := mul_le_mul_of_nonneg_left l2 hγ'.le
      have e : 1 / γ * (γ * |M|) = |M| := by field_simp
      nlinarith
    · have := mul_le_mul_of_nonneg_left l1 hγ'.le
      have e : 1 / γ * (-γ * |M|) = -|M| := by field_simp
      nlinarith
  · -- order preserving
    have hle : ∫ y, Real.exp (-γ * w y) ∂(P x) ≤ ∫ y, Real.exp (-γ * v y) ∂(P x) :=
      integral_mono (integrable_of_mem_bX P (hexp w hw) x) (integrable_of_mem_bX P (hexp v hv) x)
        fun y => Real.exp_le_exp.2 (by nlinarith [h y])
    have hl := Real.log_le_log (hpos w hw x) hle
    simp only [entropicOp]
    nlinarith [mul_le_mul_of_nonneg_left hl (one_div_pos.2 hγ).le]
  · -- shifting constants
    funext x
    have hsplit : (fun y => Real.exp (-γ * (v y + c))) =
        fun y => Real.exp (-γ * c) * Real.exp (-γ * v y) := by
      funext y; rw [← Real.exp_add]; ring_nf
    simp only [entropicOp]
    rw [hsplit, integral_const_mul, Real.log_mul (Real.exp_pos _).ne' (hpos v hv x).ne',
      Real.log_exp]
    field_simp
    ring

/-! ### Mean-variance is not order preserving -/

/-- The mean-variance criterion `E v − (γ/2) Var v` under a probability measure `μ` (p. 15). -/
noncomputable def meanVariance {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (μ : Measure Ω)
    (v : Ω → ℝ) : ℝ :=
  ∫ ω, v ω ∂μ - γ / 2 * ∫ ω, (v ω - ∫ ω', v ω' ∂μ) ^ 2 ∂μ

/-- §1.1.3.6 (p. 18): the mean-variance operator is not order preserving. For a fair coin `μ`
and `γ > 0`, the payoff `w = (8/γ)𝟙{heads}` dominates `v = 0` but has lower mean-variance
value. So (1.14) with the mean-variance `K` falls outside the order-based theory. -/
theorem meanVariance_not_monotone {γ : ℝ} (hγ : 0 < γ) :
    ∃ v w : Bool → ℝ, v ≤ w ∧
      meanVariance γ (PMF.uniformOfFintype Bool).toMeasure w <
        meanVariance γ (PMF.uniformOfFintype Bool).toMeasure v := by
  refine ⟨fun _ => 0, fun b => if b then 8 / γ else 0, fun b => ?_, ?_⟩
  · cases b
    · simp
    · simpa using (div_pos (by norm_num : (0 : ℝ) < 8) hγ).le
  · simp only [meanVariance, PMF.integral_eq_sum, PMF.uniformOfFintype_apply, Fintype.univ_bool,
      Fintype.card_bool, smul_eq_mul]
    norm_num
    field_simp
    nlinarith

end SargentStachurski.PreludeExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite Markov decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.2.1 (pp. 19–26).

A finite MDP has a finite state space `X`, a nonempty finite feasible set `Γ(x)` of actions, a
reward `r`, a discount factor `β ∈ [0, 1)` and transition probabilities `P(x, a, ·)` on the
feasible pairs. The action set need not be finite: only the sets `Γ(x)` are.

* **Exercise 1.2.1**: `T_σ v = r_σ + βP_σ v` (1.18) is a `β`-contraction on `ℝ^X` whose fixed
  point is `v_σ = (I − βP_σ)⁻¹r_σ = ∑ₜ (βP_σ)ᵗr_σ` (1.17); `I − βP_σ` is invertible.
* **Exercise 1.2.2**: with `r̄ ≥ |r|` on `G` and `M = r̄/(1 − β)`, each `T_σ` maps `[−M, M]` into
  itself and `|v_σ| ≤ M`, so `v* = sup_σ v_σ` is well defined.
* The Bellman operator (1.20); **Exercise 1.2.3** (it is a `β`-contraction); `v`-greedy policies
  (1.21) and **Exercise 1.2.4**.
* **Theorem 1.2.1**: `v*` is the unique solution of the Bellman equation (1.19), a policy is
  optimal iff it is `v*`-greedy, and an optimal policy exists.
* **Theorem 1.2.2**: VFI and OPI (for every `m ≥ 1`) converge to `v*` from every starting point,
  and HPI reaches an optimal policy in finitely many steps.
* **Lemma 1.2.3** and **Proposition 1.2.4**: `v*` is the unique solution of the linear program
  (1.23) for any everywhere positive weight `c`.
-/

open Filter Topology Set Function Matrix

namespace SargentStachurski.PreludeExamples

/-- A finite MDP `(Γ, r, β, P)` (§1.2.1.1). The kernel is required to be stochastic on the
feasible pairs only. -/
structure FiniteMDP (X A : Type*) [Fintype X] where
  /-- the feasible correspondence -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the reward -/
  r : X → A → ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the transition probabilities -/
  P : X → A → X → ℝ
  P_nonneg : ∀ x, ∀ a ∈ Γ x, ∀ x', 0 ≤ P x a x'
  P_sum : ∀ x, ∀ a ∈ Γ x, ∑ x', P x a x' = 1

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- The feasible policies `Σ = {σ ∈ A^X : σ(x) ∈ Γ(x)}` (1.15). -/
def Policy : Type _ := {σ : X → A // ∀ x, σ x ∈ M.Γ x}

/-- The value of action `a` at `x` given `v`: `r(x, a) + β ∑_{x'} v(x')P(x, a, x')`. -/
def Q (v : X → ℝ) (x : X) (a : A) : ℝ := M.r x a + M.β * ∑ x', v x' * M.P x a x'

/-- The policy operator (1.18): `(T_σ v)(x) = r(x, σ(x)) + β ∑_{x'} v(x')P(x, σ(x), x')`. -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := fun x => M.Q v x (σ x)

omit [Fintype X] in
/-- Every function on a finite set is bounded. -/
theorem isBdd_of_finite [Finite X] (v : X → ℝ) : IsBdd v := by
  have := Fintype.ofFinite X
  exact ⟨∑ x, |v x|, fun x =>
    Finset.single_le_sum (f := fun y => |v y|) (fun y _ => abs_nonneg _) (Finset.mem_univ x)⟩

/-- `|∑ v P − ∑ w P| ≤ c` when `|v − w| ≤ c`, for a feasible pair. -/
theorem abs_sum_sub_le {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} {c : ℝ}
    (h : ∀ y, |v y - w y| ≤ c) :
    |∑ x', v x' * M.P x a x' - ∑ x', w x' * M.P x a x'| ≤ c := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ x', (v x' * M.P x a x' - w x' * M.P x a x')|
      ≤ ∑ x', |v x' * M.P x a x' - w x' * M.P x a x'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x', c * M.P x a x' := Finset.sum_le_sum fun y _ => by
        rw [← sub_mul, abs_mul, abs_of_nonneg (M.P_nonneg x a ha y)]
        exact mul_le_mul_of_nonneg_right (h y) (M.P_nonneg x a ha y)
    _ = c := by rw [← Finset.mul_sum, M.P_sum x a ha, mul_one]

theorem Q_mono {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} (h : v ≤ w) : M.Q v x a ≤ M.Q w x a :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_right (h y) (M.P_nonneg x a ha y)) M.β_nonneg)

theorem abs_Q_sub_le {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} {c : ℝ}
    (h : ∀ y, |v y - w y| ≤ c) : |M.Q v x a - M.Q w x a| ≤ M.β * c := by
  simp only [Q, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_nonneg]
  exact mul_le_mul_of_nonneg_left (M.abs_sum_sub_le ha h) M.β_nonneg

/-- Shifting by a constant: `Q(v − c) = Qv − βc` on feasible pairs. -/
theorem Q_sub_const {x : X} {a : A} (ha : a ∈ M.Γ x) (v : X → ℝ) (c : ℝ) :
    M.Q (fun y => v y - c) x a = M.Q v x a - M.β * c := by
  simp only [Q, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, M.P_sum x a ha]
  ring

/-- A `v`-greedy action exists at every state. -/
theorem exists_greedy (v : X → ℝ) :
    ∃ σ : M.Policy, ∀ x, ∀ a ∈ M.Γ x, M.Q v x a ≤ M.Q v x (σ.1 x) := by
  choose f hf hmax using fun x => Finset.exists_max_image (M.Γ x) (M.Q v x) (M.Γ_nonempty x)
  exact ⟨⟨f, hf⟩, hmax⟩

/-- The finite MDP as a contracting dynamic program on `ℝ^X`. -/
def toDP : ContractingDP X M.Policy where
  V := univ
  T σ := M.Tσ σ.1
  β := M.β
  β_nonneg := M.β_nonneg
  β_lt_one := M.β_lt_one
  nonempty := ⟨0, trivial⟩
  bdd v _ := isBdd_of_finite v
  closed _ _ _ _ := trivial
  mapsTo _ _ _ := trivial
  mono σ _ _ _ _ h x := M.Q_mono (σ.2 x) h
  contraction σ _ _ _ _ _ h x := M.abs_Q_sub_le (σ.2 x) h
  exists_greedy v _ := by
    obtain ⟨σ, hσ⟩ := M.exists_greedy v
    exact ⟨σ, fun τ x => hσ x _ (τ.2 x)⟩

/-- `σ` is `v`-greedy in the sense of (1.21). -/
def IsGreedy (v : X → ℝ) (σ : M.Policy) : Prop := ∀ x, ∀ a ∈ M.Γ x, M.Q v x a ≤ M.Q v x (σ.1 x)

/-- **Exercise 1.2.4** (p. 22): `σ` is `v`-greedy iff `T_σ v ≥ T_τ v` for all `τ ∈ Σ`. -/
theorem isGreedy_iff (v : X → ℝ) (σ : M.Policy) :
    M.IsGreedy v σ ↔ M.toDP.IsGreedy v σ := by
  classical
  constructor
  · exact fun h τ x => h x _ (τ.2 x)
  · intro h x a ha
    let τ : M.Policy := ⟨Function.update σ.1 x a, fun y => by
      rcases eq_or_ne y x with rfl | hy
      · rw [Function.update_self]; exact ha
      · rw [Function.update_of_ne hy]; exact σ.2 y⟩
    have := h τ x
    change M.Q v x (Function.update σ.1 x a x) ≤ M.Q v x (σ.1 x) at this
    rwa [Function.update_self] at this

/-- The Bellman operator (1.20): `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑ v(x')P(x, a, x')}`. -/
theorem bellman_eq (v : X → ℝ) (x : X) :
    M.toDP.bellman v x = (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x) := by
  obtain ⟨σ, hσ⟩ := M.exists_greedy v
  refine le_antisymm (Finset.le_sup' (M.Q v x) ((M.toDP.greedy v).2 x)) ?_
  refine Finset.sup'_le _ _ fun a ha => (hσ x a ha).trans ?_
  exact M.toDP.T_le_bellman σ (mem_univ v) x

/-- **Exercise 1.2.3** (p. 22): the Bellman operator is a `β`-contraction on `(ℝ^X, d_∞)`. -/
theorem bellman_contraction : IsSupContraction univ M.toDP.bellman M.β :=
  M.toDP.bellman_contraction

/-! ### Lifetime values as matrix expressions -/

/-- `P_σ(x, x') = P(x, σ(x), x')` (1.16). -/
def Pσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.P x (σ x) x'

/-- `r_σ(x) = r(x, σ(x))` (1.16). -/
def rσ (σ : X → A) : X → ℝ := fun x => M.r x (σ x)

theorem Tσ_eq_mulVec (σ : X → A) (v : X → ℝ) : M.Tσ σ v = M.rσ σ + (M.β • M.Pσ σ) *ᵥ v := by
  funext x
  simp only [Tσ, Q, rσ, Pσ, Pi.add_apply, smul_mulVec, Pi.smul_apply, smul_eq_mul, mulVec,
    dotProduct, Matrix.of_apply]
  congr 2
  exact Finset.sum_congr rfl fun y _ => mul_comm _ _

/-- `|P_σ w| ≤ c` when `|w| ≤ c`. -/
theorem abs_Pσ_mulVec_le (σ : M.Policy) {w : X → ℝ} {c : ℝ} (h : ∀ y, |w y| ≤ c) (x : X) :
    |(M.Pσ σ.1 *ᵥ w) x| ≤ c := by
  have := M.abs_sum_sub_le (σ.2 x) (v := w) (w := 0) (c := c) (by simpa using h)
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] at this
  simpa [Pσ, mulVec, dotProduct, mul_comm] using this

/-- **Exercise 1.2.1** (p. 21), (1.17): `I − βP_σ` is invertible and `v_σ = (I − βP_σ)⁻¹r_σ`. -/
theorem vσ_eq_inv [DecidableEq X] (σ : M.Policy) :
    IsUnit (1 - M.β • M.Pσ σ.1) ∧ M.toDP.vσ σ = (1 - M.β • M.Pσ σ.1)⁻¹ *ᵥ M.rσ σ.1 := by
  set B := M.β • M.Pσ σ.1
  -- `z = Bz` forces `z = 0`
  have hzero : ∀ z : X → ℝ, z = B *ᵥ z → z = 0 := by
    intro z hz
    have hc : IsSupContraction (univ : Set (X → ℝ)) (fun v => B *ᵥ v) M.β := by
      intro v _ w _ c h x
      have e : (B *ᵥ v) x - (B *ᵥ w) x = M.β * (M.Pσ σ.1 *ᵥ (v - w)) x := by
        simp only [B, smul_mulVec, mulVec_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      change |(B *ᵥ v) x - (B *ᵥ w) x| ≤ M.β * c
      rw [e, abs_mul, abs_of_nonneg M.β_nonneg]
      exact mul_le_mul_of_nonneg_left
        (M.abs_Pσ_mulVec_le σ (fun y => by simpa using h y) x) M.β_nonneg
    exact hc.eq_of_isFixedPt M.β_nonneg M.β_lt_one (mem_univ z) (mem_univ 0)
      (isBdd_of_finite z) (isBdd_of_finite 0) hz.symm (by simp)
  have hunit : IsUnit (1 - B) := by
    rw [← mulVec_injective_iff_isUnit]
    intro u w huw
    have : u - w = B *ᵥ (u - w) := by
      have h2 : (1 - B) *ᵥ (u - w) = 0 := by rw [mulVec_sub, huw, sub_self]
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at h2
      exact h2
    exact sub_eq_zero.1 (hzero _ this)
  refine ⟨hunit, ?_⟩
  have hfix : M.toDP.vσ σ = M.rσ σ.1 + B *ᵥ M.toDP.vσ σ := by
    conv_lhs => rw [← M.toDP.T_vσ σ]
    exact M.Tσ_eq_mulVec σ.1 _
  have h1 : (1 - B) *ᵥ M.toDP.vσ σ = M.rσ σ.1 := by
    rw [sub_mulVec, one_mulVec]
    nth_rewrite 1 [hfix]
    abel
  rw [← h1, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hunit), one_mulVec]

/-- (1.17) (p. 21): `v_σ = ∑ₜ (βP_σ)ᵗr_σ`. -/
theorem vσ_hasSum [DecidableEq X] (σ : M.Policy) (x : X) :
    HasSum (fun t => ((M.β • M.Pσ σ.1) ^ t *ᵥ M.rσ σ.1) x) (M.toDP.vσ σ x) := by
  set B := M.β • M.Pσ σ.1
  obtain ⟨R, hR⟩ := isBdd_of_finite (M.rσ σ.1)
  have hbound : ∀ t y, |(B ^ t *ᵥ M.rσ σ.1) y| ≤ M.β ^ t * R := by
    intro t
    induction t with
    | zero => simpa using hR
    | succ t ih =>
      intro y
      rw [pow_succ', ← mulVec_mulVec, smul_mulVec, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg M.β_nonneg, pow_succ, mul_comm (M.β ^ t) M.β, mul_assoc]
      exact mul_le_mul_of_nonneg_left (M.abs_Pσ_mulVec_le σ ih y) M.β_nonneg
  have hsum : Summable fun t => (B ^ t *ᵥ M.rσ σ.1) x :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one M.β_nonneg M.β_lt_one).mul_right R)
      fun t => by rw [Real.norm_eq_abs]; exact hbound t x
  -- the partial sums are the iterates of `T_σ` from `0`
  have hiter : ∀ n, (M.toDP.T σ)^[n] 0 = ∑ t ∈ Finset.range n, B ^ t *ᵥ M.rσ σ.1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply', ih]
      change M.Tσ σ.1 _ = _
      rw [M.Tσ_eq_mulVec, mulVec_sum, Finset.sum_range_succ', pow_zero, one_mulVec, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun t _ => by rw [mulVec_mulVec, pow_succ']
  have hlim := (M.toDP.tendsto_vσ σ (mem_univ 0)).tendsto_at x
  simp only [hiter, Finset.sum_apply] at hlim
  exact (tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim) ▸ hsum.hasSum

/-- **Exercise 1.2.2** (p. 21): if `|r| ≤ r̄` on `G` and `M = r̄/(1 − β)`, then (i) every `T_σ`
maps `[−M, M]` into itself and (ii) `|v_σ| ≤ M`. -/
theorem abs_vσ_le {rbar : ℝ} (hr : ∀ x, ∀ a ∈ M.Γ x, |M.r x a| ≤ rbar) :
    (∀ σ : M.Policy, ∀ v : X → ℝ, (∀ x, |v x| ≤ rbar / (1 - M.β)) →
      ∀ x, |M.Tσ σ.1 v x| ≤ rbar / (1 - M.β)) ∧
      ∀ σ x, |M.toDP.vσ σ x| ≤ rbar / (1 - M.β) := by
  have h1β : 0 < 1 - M.β := sub_pos.2 M.β_lt_one
  have hK : rbar + M.β * (rbar / (1 - M.β)) = rbar / (1 - M.β) := by
    have : rbar / (1 - M.β) * (1 - M.β) = rbar := div_mul_cancel₀ _ h1β.ne'
    linear_combination -this
  have hself : ∀ σ : M.Policy, ∀ v : X → ℝ, (∀ x, |v x| ≤ rbar / (1 - M.β)) →
      ∀ x, |M.Tσ σ.1 v x| ≤ rbar / (1 - M.β) := by
    intro σ v hv x
    have hP := M.abs_Pσ_mulVec_le σ hv x
    simp only [Pσ, mulVec, dotProduct, Matrix.of_apply] at hP
    simp only [Tσ, Q]
    calc |M.r x (σ.1 x) + M.β * ∑ x', v x' * M.P x (σ.1 x) x'|
        ≤ |M.r x (σ.1 x)| + M.β * |∑ x', v x' * M.P x (σ.1 x) x'| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg M.β_nonneg]
      _ ≤ rbar + M.β * (rbar / (1 - M.β)) := by
          refine add_le_add (hr x _ (σ.2 x)) (mul_le_mul_of_nonneg_left ?_ M.β_nonneg)
          simpa only [mul_comm] using hP
      _ = rbar / (1 - M.β) := hK
  refine ⟨hself, fun σ x => ?_⟩
  -- the iterates from `0` stay in `[−M, M]`, and so does their limit `v_σ`
  have hrbar : 0 ≤ rbar / (1 - M.β) := by
    have hr0 : 0 ≤ rbar := (abs_nonneg _).trans (hr x _ (σ.2 x))
    positivity
  have hit : ∀ n y, |(M.toDP.T σ)^[n] 0 y| ≤ rbar / (1 - M.β) := by
    intro n
    induction n with
    | zero => intro y; simpa using hrbar
    | succ n ih => intro y; rw [iterate_succ_apply']; exact hself σ _ ih y
  exact le_of_tendsto' (((M.toDP.tendsto_vσ σ (mem_univ 0)).tendsto_at x).abs) fun n => hit n x

/-! ### Optimality and algorithms -/

/-- `Σ` is finite: each `Γ(x)` is. -/
theorem finite_policy : Finite M.Policy := by
  classical
  refine Finite.of_injective (fun σ : M.Policy => fun x => (⟨σ.1 x, σ.2 x⟩ : M.Γ x)) ?_
  intro σ τ h
  apply Subtype.ext
  funext x
  have := congrFun h x
  simpa using congrArg Subtype.val this

/-- **Theorem 1.2.1** (p. 22): the value function `v*` is the unique solution in `ℝ^X` of the
Bellman equation (1.19), a policy is optimal iff it is `v*`-greedy (1.21), and an optimal policy
exists. -/
theorem theorem_1_2_1 :
    (∀ x, M.toDP.vstar x = ⨆ σ, M.toDP.vσ σ x) ∧
      (∀ x, M.toDP.vstar x = (M.Γ x).sup' (M.Γ_nonempty x) (M.Q M.toDP.vstar x)) ∧
      (∀ v : X → ℝ, (∀ x, v x = (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x)) → v = M.toDP.vstar) ∧
      (∀ σ, M.toDP.IsOptimal σ ↔ M.IsGreedy M.toDP.vstar σ) ∧ ∃ σ, M.toDP.IsOptimal σ := by
  obtain ⟨-, hsup, hfix, hopt, hex, -⟩ := M.toDP.optimality
  refine ⟨hsup, fun x => ?_, fun v hv => (hfix v (mem_univ v)).1 (funext fun x => ?_),
    fun σ => (hopt σ).trans (M.isGreedy_iff _ σ).symm, hex⟩
  · rw [← M.bellman_eq, M.toDP.bellman_vstar]
  · rw [M.bellman_eq]; exact (hv x).symm

/-- **Theorem 1.2.2** (p. 24): VFI converges, OPI converges for every `m ≥ 1`, from every
starting point, and HPI reaches an optimal policy in finitely many steps. -/
theorem theorem_1_2_2 :
    (∀ v, TendstoUniformly (fun n => M.toDP.bellman^[n] v) M.toDP.vstar atTop) ∧
      (∀ m, 1 ≤ m → ∀ v, TendstoUniformly (M.toDP.opi m v) M.toDP.vstar atTop) ∧
      ∀ σ₀, ∃ k, ∀ j, k ≤ j → M.toDP.vσ (M.toDP.hpiPolicy σ₀ j) = M.toDP.vstar ∧
        M.toDP.IsOptimal (M.toDP.hpiPolicy σ₀ j) := by
  have := M.finite_policy
  refine ⟨fun v => M.toDP.tendsto_bellman_iterate (mem_univ v), fun m hm v => ?_,
    M.toDP.hpi_terminates⟩
  refine M.toDP.tendsto_opi hm (fun σ v _ c => ?_) (fun _ _ _ => trivial) (mem_univ v)
  funext x
  exact M.Q_sub_const (σ.2 x) v c

/-- **Lemma 1.2.3** (p. 25): if `Tv ≤ v` then `v* ≤ v`. -/
theorem vstar_le {v : X → ℝ} (h : ∀ x, (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x) ≤ v x) :
    M.toDP.vstar ≤ v :=
  M.toDP.vstar_le_of_bellman_le (mem_univ v) fun x => (M.bellman_eq v x).trans_le (h x)

/-- The constraint set of the linear program (1.23). -/
def IsLPFeasible (v : X → ℝ) : Prop := ∀ x, ∀ a ∈ M.Γ x, M.Q v x a ≤ v x

/-- **Proposition 1.2.4** (p. 25): for any everywhere positive `c`, the value function `v*` is
the unique solution of the linear program `min ⟨c, v⟩` subject to
`r(x, a) + β ∑ v(x')P(x, a, x') ≤ v(x)` for all `(x, a) ∈ G` (1.23). -/
theorem lp_solution {c : X → ℝ} (hc : ∀ x, 0 < c x) :
    IsLeast {s | ∃ v, M.IsLPFeasible v ∧ s = ∑ x, c x * v x} (∑ x, c x * M.toDP.vstar x) ∧
      ∀ v, M.IsLPFeasible v → ∑ x, c x * v x ≤ ∑ x, c x * M.toDP.vstar x → v = M.toDP.vstar := by
  have hfeas : M.IsLPFeasible M.toDP.vstar := fun x a ha => by
    rw [← congrFun M.toDP.bellman_vstar x, M.bellman_eq]
    exact Finset.le_sup' (M.Q M.toDP.vstar x) ha
  have hge : ∀ v, M.IsLPFeasible v → M.toDP.vstar ≤ v := fun v hv =>
    M.vstar_le fun x => Finset.sup'_le _ _ fun a ha => hv x a ha
  refine ⟨⟨⟨_, hfeas, rfl⟩, ?_⟩, fun v hv hle => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hge v hv x) (hc x).le
  · have hvs := hge v hv
    have hsum : ∑ x, c x * (v x - M.toDP.vstar x) = 0 := by
      have h0 : 0 ≤ ∑ x, c x * (v x - M.toDP.vstar x) :=
        Finset.sum_nonneg fun x _ => mul_nonneg (hc x).le (sub_nonneg.2 (hvs x))
      have : ∑ x, c x * (v x - M.toDP.vstar x) = ∑ x, c x * v x - ∑ x, c x * M.toDP.vstar x := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
      mul_nonneg (hc x).le (sub_nonneg.2 (hvs x))).1 hsum
    funext x
    have := hterm x (Finset.mem_univ x)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hc x).ne'
    · linarith

end FiniteMDP

end SargentStachurski.PreludeExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Cash management

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.2.1.5 (pp. 26–28).

Cash `x ∈ X = {0, …, w̄}`; a transfer `a ∈ Γ(x) = {a ∈ ℤ : −x ≤ a ≤ w̄ − x}`; iid shocks
`ξ ∈ Ξ = {−k, …, k}` with probabilities `φ`; next cash `F(x, a, ξ) = max{0, min{w̄, x + a + ξ}}`
(1.24); transition probabilities `P(x, a, x') = ∑_ξ 𝟙{F(x, a, ξ) = x'}φ(ξ)`; flow profit
`π(x, a, ξ) = ρ(w̄ − x) − (c + τ|a|)𝟙{a ≠ 0} − p𝟙{x + a + ξ < 0}` (1.25) and reward
`r(x, a) = ∑_ξ π(x, a, ξ)φ(ξ)` (1.26). This is a finite MDP, so Theorems 1.2.1 and 1.2.2 apply:
an optimal policy exists and HPI finds one in finitely many steps.
-/

namespace SargentStachurski.PreludeExamples

/-- The parameters of the cash management problem. -/
structure CashManagement where
  /-- total wealth `w̄` -/
  wbar : ℕ
  /-- the shock bound `k` -/
  k : ℕ
  /-- the shock probabilities on `Ξ = {−k, …, k}` -/
  φ : ℤ → ℝ
  φ_nonneg : ∀ ξ, 0 ≤ φ ξ
  φ_sum : ∑ ξ ∈ Finset.Icc (-(k : ℤ)) k, φ ξ = 1
  /-- the return on securities -/
  ρ : ℝ
  /-- the fixed transaction cost -/
  c : ℝ
  /-- the proportional transaction cost -/
  τ : ℝ
  /-- the penalty for insufficient cash -/
  p : ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace CashManagement

variable (C : CashManagement)

/-- The shock set `Ξ = {−k, …, k}`. -/
def Ξ : Finset ℤ := Finset.Icc (-(C.k : ℤ)) C.k

/-- The next-period state (1.24), `F(x, a, ξ) = max{0, min{w̄, x + a + ξ}}`. -/
def next (x : Fin (C.wbar + 1)) (a ξ : ℤ) : Fin (C.wbar + 1) :=
  ⟨(max 0 (min (C.wbar : ℤ) (x + a + ξ))).toNat, by omega⟩

/-- The flow profit (1.25). -/
def profit (x : Fin (C.wbar + 1)) (a ξ : ℤ) : ℝ :=
  C.ρ * ((C.wbar : ℝ) - x) - (if a ≠ 0 then C.c + C.τ * |(a : ℝ)| else 0) -
    (if (x : ℤ) + a + ξ < 0 then C.p else 0)

/-- The cash management problem as a finite MDP (§1.2.1.5). -/
def toMDP : FiniteMDP (Fin (C.wbar + 1)) ℤ where
  Γ x := Finset.Icc (-(x : ℤ)) (C.wbar - x)
  Γ_nonempty x := ⟨0, by simp only [Finset.mem_Icc]; omega⟩
  r x a := ∑ ξ ∈ C.Ξ, C.profit x a ξ * C.φ ξ
  β := C.β
  β_nonneg := C.β_nonneg
  β_lt_one := C.β_lt_one
  P x a x' := ∑ ξ ∈ C.Ξ, if C.next x a ξ = x' then C.φ ξ else 0
  P_nonneg _ _ _ _ := Finset.sum_nonneg fun ξ _ => by
    split_ifs
    · exact C.φ_nonneg ξ
    · exact le_rfl
  P_sum x a _ := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    exact C.φ_sum

/-- §1.2.1.5: Theorems 1.2.1 and 1.2.2 apply to cash management. The value function uniquely
solves the Bellman equation, an optimal policy exists, VFI and OPI converge, and HPI reaches an
optimal policy in finitely many steps (five iterations in Figure 1.9). -/
theorem optimality :
    (∀ v : Fin (C.wbar + 1) → ℝ, (∀ x, v x = (C.toMDP.Γ x).sup' (C.toMDP.Γ_nonempty x)
      (C.toMDP.Q v x)) → v = C.toMDP.toDP.vstar) ∧ (∃ σ, C.toMDP.toDP.IsOptimal σ) ∧
      ∀ σ₀, ∃ k, ∀ j, k ≤ j → C.toMDP.toDP.IsOptimal (C.toMDP.toDP.hpiPolicy σ₀ j) := by
  obtain ⟨-, -, huniq, -, hex⟩ := C.toMDP.theorem_1_2_1
  obtain ⟨-, -, hhpi⟩ := C.toMDP.theorem_1_2_2
  exact ⟨huniq, hex, fun σ₀ => by
    obtain ⟨k, hk⟩ := hhpi σ₀
    exact ⟨k, fun j hj => (hk j hj).2⟩⟩

end CashManagement

end SargentStachurski.PreludeExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Continuous-time MDPs and uniformization

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.2.2 (pp. 28–33).

A continuous-time MDP `(Γ, δ, r, Q)` on finite `X` has a discount rate `δ > 0` and an intensity
kernel `Q` on the feasible pairs (nonnegative off the diagonal, rows summing to zero). Its
`σ`-value function is `v_σ = (δI − Q_σ)⁻¹r_σ` (1.28).

* **Uniformization** (§1.2.2.2): for `m > 0` with `|Q(x, a, x)| ≤ m` on `G`, set
  `P = I + Q/m`, `β = m/(m + δ)` and `r̂ = r/(m + δ)` (1.29)–(1.30). **Exercise 1.2.5**: `P` is
  stochastic and `v_σ = (I − βP_σ)⁻¹r̂_σ`, so the discrete-time theory applies (§1.2.2.3).
* **Exercise 1.2.6**: `v` solves the uniformized Bellman equation (1.32) iff it solves the HJB
  equation `δv(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑ v(x')Q(x, a, x')}` (1.33), and the greedy
  policies of the two coincide.
* **Service rate control** (§1.2.2.4): the queue's kernel is an intensity kernel and
  `m = λ + μ̄` bounds its diagonal; the bound is attained when the capacity is at least two.
-/

open Filter Topology Set Function Matrix

namespace SargentStachurski.PreludeExamples

/-- A continuous-time MDP `(Γ, δ, r, Q)` (§1.2.2.1). -/
structure CTMDP (X A : Type*) [Fintype X] where
  /-- the feasible correspondence -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the discount rate -/
  δ : ℝ
  δ_pos : 0 < δ
  /-- the reward rate -/
  r : X → A → ℝ
  /-- the intensity kernel -/
  Q : X → A → X → ℝ
  Q_nonneg : ∀ x, ∀ a ∈ Γ x, ∀ x', x ≠ x' → 0 ≤ Q x a x'
  Q_sum : ∀ x, ∀ a ∈ Γ x, ∑ x', Q x a x' = 0

namespace CTMDP

variable {X A : Type*} [Fintype X] [DecidableEq X] (C : CTMDP X A)

/-- `Q_σ(x, x') = Q(x, σ(x), x')`. -/
def Qσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => C.Q x (σ x) x'

/-- `r_σ(x) = r(x, σ(x))`. -/
def rσ (σ : X → A) : X → ℝ := fun x => C.r x (σ x)

/-- The `σ`-value function (1.28): `v_σ = (δI − Q_σ)⁻¹r_σ`. -/
noncomputable def vσ (σ : X → A) : X → ℝ := (C.δ • (1 : Matrix X X ℝ) - C.Qσ σ)⁻¹ *ᵥ C.rσ σ

variable {m : ℝ}

/-- The uniformized discrete-time MDP (1.29)–(1.30), for any `m > 0` bounding `|Q(x, a, x)|`
on `G`: `P = I + Q/m`, `β = m/(m + δ)`, `r̂ = r/(m + δ)`. **Exercise 1.2.5 (i)**: `P` is a
stochastic kernel. -/
noncomputable def uniformize (hm : 0 < m) (hmQ : ∀ x, ∀ a ∈ C.Γ x, |C.Q x a x| ≤ m) :
    FiniteMDP X A where
  Γ := C.Γ
  Γ_nonempty := C.Γ_nonempty
  r x a := C.r x a / (m + C.δ)
  β := m / (m + C.δ)
  β_nonneg := div_nonneg hm.le (add_pos hm C.δ_pos).le
  β_lt_one := (div_lt_one (add_pos hm C.δ_pos)).2 (lt_add_of_pos_right m C.δ_pos)
  P x a x' := (if x = x' then 1 else 0) + C.Q x a x' / m
  P_nonneg x a ha x' := by
    split_ifs with h
    · subst h
      have := (abs_le.1 (hmQ x a ha)).1
      have : -1 ≤ C.Q x a x / m := by rw [le_div_iff₀ hm]; linarith
      linarith
    · simpa using div_nonneg (C.Q_nonneg x a ha x' h) hm.le
  P_sum x a ha := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.sum_div, C.Q_sum x a ha]
    simp

variable (hm : 0 < m) (hmQ : ∀ x, ∀ a ∈ C.Γ x, |C.Q x a x| ≤ m)

/-- `δI − Q_σ = (m + δ)(I − βP_σ)`. -/
theorem sub_Qσ_eq (σ : X → A) :
    C.δ • (1 : Matrix X X ℝ) - C.Qσ σ =
      (m + C.δ) • (1 - (C.uniformize hm hmQ).β • (C.uniformize hm hmQ).Pσ σ) := by
  have hmδ : m + C.δ ≠ 0 := (add_pos hm C.δ_pos).ne'
  ext x y
  simp only [uniformize, FiniteMDP.Pσ, Qσ, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  field_simp
  split_ifs <;> ring

/-- **Exercise 1.2.5 (ii)** (p. 31): `v_σ = (δI − Q_σ)⁻¹r_σ = (I − βP_σ)⁻¹r̂_σ`, the `σ`-value
function of the uniformized MDP; in particular `δI − Q_σ` is invertible. -/
theorem vσ_eq_uniformize (σ : (C.uniformize hm hmQ).Policy) :
    IsUnit (C.δ • (1 : Matrix X X ℝ) - C.Qσ σ.1) ∧
      C.vσ σ.1 = (C.uniformize hm hmQ).toDP.vσ σ := by
  obtain ⟨hU, hv⟩ := (C.uniformize hm hmQ).vσ_eq_inv σ
  have hmδ : m + C.δ ≠ 0 := (add_pos hm C.δ_pos).ne'
  have hdet := (isUnit_iff_isUnit_det _).1 hU
  have hunit2 : IsUnit (C.δ • (1 : Matrix X X ℝ) - C.Qσ σ.1) := by
    rw [C.sub_Qσ_eq hm hmQ, isUnit_iff_isUnit_det, Matrix.det_smul]
    exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ hmδ)).mul hdet
  refine ⟨hunit2, ?_⟩
  have hr : (C.uniformize hm hmQ).rσ σ.1 = (m + C.δ)⁻¹ • C.rσ σ.1 := by
    funext x
    simp [uniformize, rσ, FiniteMDP.rσ, div_eq_inv_mul]
  have hB : (1 - (C.uniformize hm hmQ).β • (C.uniformize hm hmQ).Pσ σ.1) *ᵥ
      (C.uniformize hm hmQ).toDP.vσ σ = (C.uniformize hm hmQ).rσ σ.1 := by
    rw [hv, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hA : (C.δ • (1 : Matrix X X ℝ) - C.Qσ σ.1) *ᵥ (C.uniformize hm hmQ).toDP.vσ σ =
      C.rσ σ.1 := by
    rw [C.sub_Qσ_eq hm hmQ, smul_mulVec, hB, hr, smul_smul, mul_inv_cancel₀ hmδ, one_smul]
  rw [vσ, ← hA, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hunit2),
    one_mulVec]

/-- The uniformized action value is an increasing affine function of `r + ∑ vQ`. -/
theorem Q_uniformize (v : X → ℝ) (x : X) (a : A) :
    (C.uniformize hm hmQ).Q v x a =
      (C.r x a + ∑ x', v x' * C.Q x a x') / (m + C.δ) + m / (m + C.δ) * v x := by
  have hmδ : m + C.δ ≠ 0 := (add_pos hm C.δ_pos).ne'
  simp only [FiniteMDP.Q, uniformize, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hsum : ∑ x', v x' * (C.Q x a x' / m) = (∑ x', v x' * C.Q x a x') / m := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hsum]
  field_simp
  ring

/-- A finite maximum commutes with an increasing affine map. -/
theorem sup'_div_add {ι : Type*} (s : Finset ι) (H : s.Nonempty) (f : ι → ℝ) {d : ℝ}
    (hd : 0 < d) (e : ℝ) : s.sup' H (fun i => f i / d + e) = s.sup' H f / d + e := by
  refine le_antisymm (Finset.sup'_le _ _ fun i hi => ?_) ?_
  · exact add_le_add (div_le_div_of_nonneg_right (Finset.le_sup' f hi) hd.le) le_rfl
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' H f
    rw [heq]
    exact Finset.le_sup' (fun i => f i / d + e) hi

/-- **Exercise 1.2.6** (p. 31): `v` solves the uniformized Bellman equation (1.32) iff it solves
the HJB equation `δv(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑ v(x')Q(x, a, x')}` (1.33). -/
theorem bellman_iff_hjb (v : X → ℝ) :
    (∀ x, v x = (C.Γ x).sup' (C.Γ_nonempty x) ((C.uniformize hm hmQ).Q v x)) ↔
      ∀ x, C.δ * v x = (C.Γ x).sup' (C.Γ_nonempty x)
        (fun a => C.r x a + ∑ x', v x' * C.Q x a x') := by
  have hmδ : 0 < m + C.δ := add_pos hm C.δ_pos
  refine forall_congr' fun x => ?_
  have hsup : (C.Γ x).sup' (C.Γ_nonempty x) ((C.uniformize hm hmQ).Q v x) =
      (C.Γ x).sup' (C.Γ_nonempty x) (fun a => C.r x a + ∑ x', v x' * C.Q x a x') / (m + C.δ) +
        m / (m + C.δ) * v x := by
    simp only [C.Q_uniformize hm hmQ]
    exact sup'_div_add _ _ _ hmδ _
  rw [hsup]
  set S := (C.Γ x).sup' (C.Γ_nonempty x) (fun a => C.r x a + ∑ x', v x' * C.Q x a x')
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- §1.2.2.3 (p. 31): `σ` is greedy for the uniformized MDP iff
`σ(x) ∈ argmax_{a ∈ Γ(x)} {r(x, a) + ∑ v(x')Q(x, a, x')}` for all `x`. -/
theorem isGreedy_uniformize_iff (v : X → ℝ) (σ : (C.uniformize hm hmQ).Policy) :
    (C.uniformize hm hmQ).IsGreedy v σ ↔
      ∀ x, ∀ a ∈ C.Γ x, C.r x a + ∑ x', v x' * C.Q x a x' ≤
        C.r x (σ.1 x) + ∑ x', v x' * C.Q x (σ.1 x) x' := by
  have hmδ : 0 < m + C.δ := add_pos hm C.δ_pos
  refine forall_congr' fun x => forall₂_congr fun a _ => ?_
  rw [C.Q_uniformize hm hmQ, C.Q_uniformize hm hmQ, add_le_add_iff_right,
    div_le_div_iff_of_pos_right hmδ]

end CTMDP

/-! ### Service rate control -/

/-- The off-diagonal rates of the queue in §1.2.2.4: arrivals at rate `λ` (`x → x + 1`) and
service at rate `μ(a)` (`x → x − 1`). -/
def queueRate {N : ℕ} {A : Type*} (lam : ℝ) (μ : A → ℝ) (x : Fin (N + 1)) (a : A)
    (y : Fin (N + 1)) : ℝ :=
  (if (y : ℕ) = x + 1 then lam else 0) + (if (y : ℕ) + 1 = x then μ a else 0)

/-- The queue's intensity kernel: the rates off the diagonal, minus their sum on it. -/
def queueQ {N : ℕ} {A : Type*} (lam : ℝ) (μ : A → ℝ) (x : Fin (N + 1)) (a : A)
    (y : Fin (N + 1)) : ℝ :=
  if y = x then -∑ z, queueRate lam μ x a z else queueRate lam μ x a y

theorem sum_fin_ite_val_eq {N : ℕ} (k : ℕ) (c : ℝ) :
    ∑ z : Fin (N + 1), (if (z : ℕ) = k then c else 0) = if k < N + 1 then c else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = k then c else 0), Finset.sum_ite_eq']
  simp

/-- The diagonal of the queue's kernel: `Q(x, a, x) = −(λ𝟙{x < N} + μ(a)𝟙{x > 0})`. -/
theorem queueQ_diag {N : ℕ} {A : Type*} (lam : ℝ) (μ : A → ℝ) (x : Fin (N + 1)) (a : A) :
    queueQ lam μ x a x =
      -((if (x : ℕ) < N then lam else 0) + (if 0 < (x : ℕ) then μ a else 0)) := by
  simp only [queueQ, ↓reduceIte, queueRate, Finset.sum_add_distrib, sum_fin_ite_val_eq]
  congr 1
  have hx := x.isLt
  congr 1
  · by_cases h : (x : ℕ) < N
    · have h' : (x : ℕ) + 1 < N + 1 := by omega
      simp only [h, h', ↓reduceIte]
    · have h' : ¬ (x : ℕ) + 1 < N + 1 := by omega
      simp only [h, h', ↓reduceIte]
  · rcases Nat.eq_zero_or_pos (x : ℕ) with h0 | hpos
    · have h' : ¬ 0 < (x : ℕ) := by omega
      simp only [h', ↓reduceIte]
      refine Finset.sum_eq_zero fun z _ => ?_
      have hz : ¬ ((z : ℕ) + 1 = x) := by omega
      simp only [hz, ↓reduceIte]
    · obtain ⟨j, hj⟩ : ∃ j, (x : ℕ) = j + 1 := ⟨(x : ℕ) - 1, by omega⟩
      have : ∀ z : Fin (N + 1), ((z : ℕ) + 1 = x) ↔ ((z : ℕ) = j) := fun z => by omega
      have hj' : j < N + 1 := by omega
      simp only [hpos, this, sum_fin_ite_val_eq, hj', ↓reduceIte]

/-- §1.2.2.4: the service rate control problem as a continuous-time MDP: `Q` is an intensity
kernel, all actions are feasible, and `r(x, a) = μ(a)R𝟙{x > 0} − hx − c(a)`. -/
def serviceRate (N : ℕ) {A : Type*} (Γ : Finset A) (hΓ : Γ.Nonempty) (lam : ℝ) (hlam : 0 ≤ lam)
    (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (R h δ : ℝ) (hδ : 0 < δ) (c : A → ℝ) :
    CTMDP (Fin (N + 1)) A where
  Γ _ := Γ
  Γ_nonempty _ := hΓ
  δ := δ
  δ_pos := hδ
  r x a := μ a * R * (if 0 < (x : ℕ) then 1 else 0) - h * x - c a
  Q := queueQ lam μ
  Q_nonneg x a _ y hxy := by
    simp only [queueQ, Ne.symm hxy, ↓reduceIte, queueRate]
    exact add_nonneg (by split_ifs <;> simp [hlam]) (by split_ifs <;> simp [hμ a])
  Q_sum x a _ := by
    have hxx : queueRate lam μ x a x = 0 := by simp [queueRate]
    have h1 := Finset.add_sum_erase Finset.univ (queueQ lam μ x a) (Finset.mem_univ x)
    have h2 := Finset.add_sum_erase Finset.univ (queueRate lam μ x a) (Finset.mem_univ x)
    have h3 : ∑ y ∈ Finset.univ.erase x, queueQ lam μ x a y =
        ∑ y ∈ Finset.univ.erase x, queueRate lam μ x a y :=
      Finset.sum_congr rfl fun y hy => by simp only [queueQ, Finset.ne_of_mem_erase hy, ↓reduceIte]
    have h4 : queueQ lam μ x a x = -∑ z, queueRate lam μ x a z := by simp [queueQ]
    rw [← h1, h3, h4, ← h2, hxx]
    ring

/-- §1.2.2.4 (p. 32): `m = λ + μ̄` bounds the diagonal, `|Q(x, a, x)| ≤ λ + μ̄` where
`μ̄ ≥ μ(a)` for all `a`. -/
theorem abs_queueQ_diag_le {N : ℕ} {A : Type*} {lam : ℝ} (hlam : 0 ≤ lam) {μ : A → ℝ}
    (hμ : ∀ a, 0 ≤ μ a) {μbar : ℝ} (hμbar : ∀ a, μ a ≤ μbar) (x : Fin (N + 1)) (a : A) :
    |queueQ lam μ x a x| ≤ lam + μbar := by
  rw [queueQ_diag, abs_neg, abs_of_nonneg (add_nonneg (by split_ifs <;> simp [hlam])
    (by split_ifs <;> simp [hμ a]))]
  refine add_le_add (by split_ifs <;> simp [hlam]) ?_
  split_ifs
  · exact hμbar a
  · exact (hμ a).trans (hμbar a)

/-- §1.2.2.4 (p. 32): when the capacity is `N ≥ 2`, an interior state `0 < x < N` exists and
`|Q(x, a, x)| = λ + μ(a)` there, so `m = λ + μ̄` is the maximum of `|Q(x, a, x)|`. -/
theorem abs_queueQ_diag_interior {N : ℕ} (hN : 2 ≤ N) {A : Type*} {lam : ℝ} (hlam : 0 ≤ lam)
    {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) (a : A) :
    |queueQ lam μ (⟨1, by omega⟩ : Fin (N + 1)) a ⟨1, by omega⟩| = lam + μ a := by
  rw [queueQ_diag]
  simp only [show (1 : ℕ) < N by omega, ↓reduceIte, zero_lt_one, abs_neg]
  exact abs_of_nonneg (add_nonneg hlam (hμ a))

/-- §1.2.2.4: with capacity `N = 1` there is no interior state, and the largest `|Q(x, a, x)|`
is `max(λ, μ̄)`, not `λ + μ̄`; `λ + μ̄` is still a valid uniformization rate. -/
theorem abs_queueQ_diag_capacity_one {A : Type*} {lam : ℝ} (hlam : 0 ≤ lam) {μ : A → ℝ}
    (hμ : ∀ a, 0 ≤ μ a) (x : Fin 2) (a : A) :
    |queueQ lam μ x a x| = if (x : ℕ) = 0 then lam else μ a := by
  rw [queueQ_diag]
  fin_cases x
  · simp [abs_of_nonneg hlam]
  · simp [abs_of_nonneg (hμ a)]

/-- §1.2.2.4: the service rate problem uniformized at `m = λ + μ̄` (`λ > 0`). -/
noncomputable def serviceRateMDP (N : ℕ) {A : Type*} (Γ : Finset A) (hΓ : Γ.Nonempty) {lam : ℝ}
    (hlam : 0 < lam) {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) {μbar : ℝ} (hμbar : ∀ a, μ a ≤ μbar)
    (R h δ : ℝ) (hδ : 0 < δ) (c : A → ℝ) : FiniteMDP (Fin (N + 1)) A :=
  (serviceRate N Γ hΓ lam hlam.le μ hμ R h δ hδ c).uniformize
    (m := lam + μbar) (add_pos_of_pos_of_nonneg hlam ((hμ hΓ.choose).trans (hμbar _)))
    fun x a _ => abs_queueQ_diag_le hlam.le hμ hμbar x a

/-- §1.2.2.4 (p. 32): for the service rate problem the value function solves the HJB equation
(1.33) and an optimal policy exists, which HPI finds in finitely many steps. -/
theorem serviceRate_optimality (N : ℕ) {A : Type*} (Γ : Finset A) (hΓ : Γ.Nonempty) {lam : ℝ}
    (hlam : 0 < lam) {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) {μbar : ℝ} (hμbar : ∀ a, μ a ≤ μbar)
    (R h δ : ℝ) (hδ : 0 < δ) (c : A → ℝ) :
    (∀ x, δ * (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).toDP.vstar x =
      Γ.sup' hΓ (fun a => (μ a * R * (if 0 < (x : ℕ) then 1 else 0) - h * x - c a) +
        ∑ x', (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).toDP.vstar x' *
          queueQ lam μ x a x')) ∧
      (∃ σ, (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).toDP.IsOptimal σ) ∧
      ∀ σ₀, ∃ k, ∀ j, k ≤ j → (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).toDP.IsOptimal
        ((serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).toDP.hpiPolicy σ₀ j) := by
  obtain ⟨-, hbell, -, -, hex⟩ := (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).theorem_1_2_1
  obtain ⟨-, -, hhpi⟩ := (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).theorem_1_2_2
  refine ⟨(CTMDP.bellman_iff_hjb _ _ _ _).1 hbell, hex, fun σ₀ => ?_⟩
  obtain ⟨k, hk⟩ := hhpi σ₀
  exact ⟨k, fun j hj => (hk j hj).2⟩

end SargentStachurski.PreludeExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal savings

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.3.1–§1.3.2 (pp. 36–43).

Wealth `w ∈ ℝ₊` evolves as `W_{t+1} = R(W_t − C_t) + Y_{t+1}` with iid income `Y ∼ φ`, and
utility `u` is continuous and bounded (Assumption 1.3.1; the density of `φ` is not needed
here). A feasible policy is a Borel `σ : ℝ₊ → ℝ₊` with `σ(w) ≤ w`.

* **Exercise 1.3.1** and **Lemma 1.3.1**: each policy operator
  `(T_σ v)(w) = u(σ(w)) + β ∫ v(R(w − σ(w)) + y) φ(dy)` (1.42) maps `bℝ₊` into itself and is
  globally stable, with fixed point `v_σ = (I − βP_σ)⁻¹r_σ = ∑ₜ (βP_σ)ᵗr_σ` (1.44); lifetime
  values are limits of finite-horizon values (1.47).
* (1.48): `|v_σ| ≤ M/(1 − β)` when `|u| ≤ M`, so `v* = sup_σ v_σ` is well defined.
* **Exercise 1.3.2**: the Bellman operator (1.51) is a `β`-contraction.
* §2.3.2: a policy is greedy in the dynamic-program sense iff it is `v`-greedy in the sense
  of (1.49) (a policy can be changed at a single wealth level).
* §1.3.2.2, (i)–(iii): given the existence of greedy policies (Lemma 1.3.2 (i), which rests on
  the density of `φ` and is proved in Chapter 6), an optimal policy exists, `v*` is the unique
  solution of the Bellman equation (1.50) in `bℝ₊`, and a policy is optimal iff it is
  `v*`-greedy.
-/

open MeasureTheory Filter Topology Set Function

open scoped NNReal

namespace SargentStachurski.PreludeExamples

/-- The optimal savings problem of §1.3 (with bounded continuous utility). -/
structure OptimalSavings where
  /-- the utility function -/
  u : ℝ≥0 → ℝ
  u_cont : Continuous u
  u_bdd : IsBdd u
  /-- the distribution of labor income -/
  φ : Measure ℝ≥0
  φ_prob : IsProbabilityMeasure φ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the gross return on assets -/
  R : ℝ≥0

/-- Feasible policies (§1.3.1.1): Borel `σ` with `0 ≤ σ(w) ≤ w`. -/
def SavingsPolicy : Type := {σ : ℝ≥0 → ℝ≥0 // Measurable σ ∧ ∀ w, σ w ≤ w}

namespace OptimalSavings

variable (S : OptimalSavings)

/-- The expected continuation value of saving `w − c`: `∫ v(R(w − c) + y) φ(dy)`. -/
noncomputable def cont (v : ℝ≥0 → ℝ) (w c : ℝ≥0) : ℝ := ∫ y, v (S.R * (w - c) + y) ∂S.φ

/-- The Markov operator `(P_σ v)(w) = ∫ v(R(w − σ(w)) + y) φ(dy)` (proof of Lemma 1.3.1). -/
noncomputable def Pσ (σ : ℝ≥0 → ℝ≥0) (v : ℝ≥0 → ℝ) (w : ℝ≥0) : ℝ := S.cont v w (σ w)

/-- `r_σ = u ∘ σ`. -/
def rσ (σ : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ := fun w => S.u (σ w)

/-- The policy operator (1.42): `(T_σ v)(w) = u(σ(w)) + β ∫ v(R(w − σ(w)) + y) φ(dy)`. -/
noncomputable def Tσ (σ : ℝ≥0 → ℝ≥0) : (ℝ≥0 → ℝ) → ℝ≥0 → ℝ := affineOp (S.rσ σ) S.β (S.Pσ σ)

theorem integrable_comp {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0) (a : ℝ≥0) :
    Integrable (fun y => v (a + y)) S.φ := by
  have := S.φ_prob
  obtain ⟨M, hM⟩ := hv.2
  exact Integrable.of_bound (hv.1.comp (measurable_const.add measurable_id)).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM _)

theorem abs_cont_le {v : ℝ≥0 → ℝ} {M : ℝ} (hM : ∀ w, |v w| ≤ M) (w c : ℝ≥0) :
    |S.cont v w c| ≤ M := by
  have := S.φ_prob
  have := norm_integral_le_of_norm_le_const (μ := S.φ) (f := fun y => v (S.R * (w - c) + y))
    (C := M) (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM _)
  simpa [cont] using this

/-- `P_σ` is a Markov operator on `bℝ₊`. -/
theorem isMarkovLike_Pσ {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) : IsMarkovLike (S.Pσ σ) := by
  have := S.φ_prob
  refine ⟨fun v hv => ?_, fun v hv w hw => ?_, fun a v _ => ?_, fun v hv w hw h => ?_,
    fun v hv M hM x => S.abs_cont_le hM _ _⟩
  · obtain ⟨M, hM⟩ := hv.2
    have hf : StronglyMeasurable fun p : ℝ≥0 × ℝ≥0 => v (S.R * (p.1 - σ p.1) + p.2) :=
      (hv.1.comp ((measurable_const.mul (measurable_fst.sub (hσ.comp measurable_fst))).add
        measurable_snd)).stronglyMeasurable
    exact ⟨hf.integral_prod_right'.measurable, M, fun w => S.abs_cont_le hM _ _⟩
  · funext x
    exact integral_add (S.integrable_comp hv _) (S.integrable_comp hw _)
  · funext x
    simp only [Pσ, cont, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul a _
  · intro x
    exact integral_mono (S.integrable_comp hv _) (S.integrable_comp hw _) fun y => h _

theorem rσ_mem {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) : S.rσ σ ∈ bX ℝ≥0 := by
  obtain ⟨M, hM⟩ := S.u_bdd
  exact ⟨S.u_cont.measurable.comp hσ, M, fun w => hM _⟩

/-- **Exercise 1.3.1** (p. 38): `T_σ` maps `bℝ₊` into itself. -/
theorem Tσ_mapsTo {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) : MapsTo (S.Tσ σ) (bX ℝ≥0) (bX ℝ≥0) :=
  affineOp_mapsTo (S.isMarkovLike_Pσ hσ) (S.rσ_mem hσ) S.β_nonneg

/-- **Lemma 1.3.1** (p. 38) and (1.47): each `T_σ` is globally stable on `bℝ₊`: it has a unique
fixed point `v_σ`, and `T_σᵏ v → v_σ` from every terminal value `v ∈ bℝ₊`. -/
theorem Tσ_globallyStable {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) :
    ∃ u ∈ bX ℝ≥0, S.Tσ σ u = u ∧ (∀ w ∈ bX ℝ≥0, S.Tσ σ w = w → w = u) ∧
      ∀ v ∈ bX ℝ≥0, TendstoUniformly (fun n => (S.Tσ σ)^[n] v) u atTop :=
  affineOp_globallyStable (S.isMarkovLike_Pσ hσ) (S.rσ_mem hσ) S.β_nonneg S.β_lt_one

/-- **Lemma 1.3.1**, (1.44): the fixed point of `T_σ` is `v_σ = ∑ₜ (βP_σ)ᵗr_σ`. -/
theorem vσ_hasSum {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0)
    (hfix : S.Tσ σ v = v) (w : ℝ≥0) :
    HasSum (fun t => S.β ^ t * (S.Pσ σ)^[t] (S.rσ σ) w) (v w) :=
  affineOp_hasSum (S.isMarkovLike_Pσ hσ) (S.rσ_mem hσ) S.β_nonneg S.β_lt_one hv hfix w

/-- (1.48) (p. 40): if `|u| ≤ M` then `|v_σ| ≤ M/(1 − β)`; so `v* = sup_σ v_σ` is well defined. -/
theorem abs_fixedPoint_le {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) {M : ℝ}
    (hM : ∀ w, |S.u w| ≤ M) {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0) (hfix : S.Tσ σ v = v)
    (w : ℝ≥0) : |v w| ≤ M / (1 - S.β) := by
  have hL := S.isMarkovLike_Pσ hσ
  have h1β : 0 < 1 - S.β := sub_pos.2 S.β_lt_one
  obtain ⟨u, -, -, huniq, hlim⟩ := S.Tσ_globallyStable hσ
  rw [huniq v hv hfix]
  -- the iterates from `0` stay within `M/(1 − β)`
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK : M + S.β * (M / (1 - S.β)) = M / (1 - S.β) := by
    field_simp
    ring
  have hit : ∀ n x, |(S.Tσ σ)^[n] (fun _ => 0) x| ≤ M / (1 - S.β) := by
    intro n
    induction n with
    | zero => intro x; simpa using div_nonneg hM0 h1β.le
    | succ n ih =>
      intro x
      rw [iterate_succ_apply']
      have hmem : (S.Tσ σ)^[n] (fun _ => 0) ∈ bX ℝ≥0 := (S.Tσ_mapsTo hσ).iterate n (const_mem_bX 0)
      calc |S.rσ σ x + S.β * S.Pσ σ ((S.Tσ σ)^[n] fun _ => 0) x|
          ≤ |S.rσ σ x| + S.β * |S.Pσ σ ((S.Tσ σ)^[n] fun _ => 0) x| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_nonneg S.β_nonneg]
        _ ≤ M + S.β * (M / (1 - S.β)) :=
            add_le_add (hM _) (mul_le_mul_of_nonneg_left (hL.abs_le _ hmem _ ih x) S.β_nonneg)
        _ = M / (1 - S.β) := hK
  exact le_of_tendsto' ((hlim _ (const_mem_bX 0)).tendsto_at w).abs fun n => hit n w

/-! ### The Bellman operator -/

/-- The objective in (1.49)–(1.51): `u(c) + β ∫ v(R(w − c) + y) φ(dy)`. -/
noncomputable def objective (v : ℝ≥0 → ℝ) (w c : ℝ≥0) : ℝ := S.u c + S.β * S.cont v w c

/-- The Bellman operator (1.51): `(Tv)(w) = max_{0 ≤ c ≤ w} {u(c) + β ∫ v(R(w − c) + y) φ(dy)}`. -/
noncomputable def bellmanOp (v : ℝ≥0 → ℝ) (w : ℝ≥0) : ℝ :=
  ⨆ c : {c : ℝ≥0 // c ≤ w}, S.objective v w c

theorem bddAbove_objective {v : ℝ≥0 → ℝ} (hv : IsBdd v) (w : ℝ≥0) :
    BddAbove (range fun c : {c : ℝ≥0 // c ≤ w} => S.objective v w c) := by
  obtain ⟨M, hM⟩ := S.u_bdd
  obtain ⟨N, hN⟩ := hv
  refine ⟨M + S.β * N, ?_⟩
  rintro _ ⟨c, rfl⟩
  refine add_le_add (le_of_abs_le (hM _)) (mul_le_mul_of_nonneg_left ?_ S.β_nonneg)
  exact le_of_abs_le (S.abs_cont_le hN _ _)

/-- **Exercise 1.3.2** (p. 42): the Bellman operator is a `β`-contraction on `bℝ₊`. -/
theorem bellmanOp_contraction : IsSupContraction (bX ℝ≥0) S.bellmanOp S.β := by
  intro v hv v' hv' c h w
  have : Nonempty {c : ℝ≥0 // c ≤ w} := ⟨⟨0, bot_le⟩⟩
  refine abs_ciSup_sub_ciSup_le (S.bddAbove_objective hv.2 w) (S.bddAbove_objective hv'.2 w)
    fun d => ?_
  have hvv' : v - v' ∈ bX ℝ≥0 := ⟨hv.1.sub hv'.1, hv.2.sub hv'.2⟩
  have hsub : S.cont v w d - S.cont v' w d = S.cont (v - v') w d := by
    have := S.φ_prob
    simp only [cont, Pi.sub_apply]
    exact (integral_sub (S.integrable_comp hv _) (S.integrable_comp hv' _)).symm
  simp only [objective, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.β_nonneg,
    hsub]
  exact mul_le_mul_of_nonneg_left (S.abs_cont_le h _ _) S.β_nonneg

/-! ### Greedy policies and optimality -/

/-- `σ` is `v`-greedy (1.49): `σ(w)` maximizes `u(c) + β ∫ v(R(w − c) + y) φ(dy)` over
`0 ≤ c ≤ w`, for every `w`. -/
def IsGreedy (v : ℝ≥0 → ℝ) (σ : SavingsPolicy) : Prop :=
  ∀ w, ∀ c ≤ w, S.objective v w c ≤ S.objective v w (σ.1 w)

/-- The optimal savings problem as a contracting dynamic program, given that greedy policies
exist (Lemma 1.3.2 (i)). -/
noncomputable def toDP (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ) :
    ContractingDP ℝ≥0 SavingsPolicy where
  V := bX ℝ≥0
  T σ := S.Tσ σ.1
  β := S.β
  β_nonneg := S.β_nonneg
  β_lt_one := S.β_lt_one
  nonempty := ⟨_, const_mem_bX 0⟩
  bdd _ h := h.2
  closed := isUniformlyClosed_bX
  mapsTo σ := S.Tσ_mapsTo σ.2.1
  mono σ _ hv _ hw h := affineOp_mono (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg hv hw h
  contraction σ := affineOp_contraction (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg
  exists_greedy v hv := by
    obtain ⟨σ, hσ⟩ := hgreedy v hv
    exact ⟨σ, fun τ w => hσ w _ (τ.2.2 w)⟩

variable {S} (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ)

/-- §2.3.2 (p. 81): `σ` is greedy for the dynamic program (`T_τ v ≤ T_σ v` for all feasible `τ`)
iff it is `v`-greedy in the sense of (1.49). -/
theorem isGreedy_iff (v : ℝ≥0 → ℝ) (σ : SavingsPolicy) :
    S.IsGreedy v σ ↔ (S.toDP hgreedy).IsGreedy v σ := by
  constructor
  · exact fun h τ w => h w _ (τ.2.2 w)
  · intro h w c hc
    classical
    let τ : SavingsPolicy := ⟨fun x => if x = w then c else σ.1 x,
      Measurable.ite (measurableSet_singleton w) measurable_const σ.2.1, fun x => by
        by_cases hx : x = w
        · simp only [hx, ↓reduceIte]; exact hc
        · simp only [hx, ↓reduceIte]; exact σ.2.2 x⟩
    have := h τ w
    change S.Tσ (fun x => if x = w then c else σ.1 x) v w ≤ S.Tσ σ.1 v w at this
    simpa [Tσ, affineOp, rσ, Pσ, objective] using this

/-- (1.51): the Bellman operator of the dynamic program is
`(Tv)(w) = max_{0 ≤ c ≤ w} {u(c) + β ∫ v(R(w − c) + y) φ(dy)}`. -/
theorem bellman_eq {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0) (w : ℝ≥0) :
    (S.toDP hgreedy).bellman v w = S.bellmanOp v w := by
  have hg := (isGreedy_iff hgreedy v _).2 ((S.toDP hgreedy).isGreedy_greedy hv)
  have : Nonempty {c : ℝ≥0 // c ≤ w} := ⟨⟨0, bot_le⟩⟩
  refine le_antisymm ?_ (ciSup_le fun c => hg w c c.2)
  exact le_ciSup (S.bddAbove_objective hv.2 w) ⟨((S.toDP hgreedy).greedy v).1 w,
    ((S.toDP hgreedy).greedy v).2.2 w⟩

/-- **§1.3.2.2** (p. 42), given greedy policies (Lemma 1.3.2 (i)): (i) an optimal policy
exists, (ii) `v*` is the unique solution of the Bellman equation (1.50) in `bℝ₊`, and (iii) a
policy is optimal iff it is `v*`-greedy. -/
theorem dp_results :
    (∃ σ, (S.toDP hgreedy).IsOptimal σ) ∧
      (S.toDP hgreedy).vstar ∈ bX ℝ≥0 ∧
      (∀ w, (S.toDP hgreedy).vstar w = S.bellmanOp (S.toDP hgreedy).vstar w) ∧
      (∀ v ∈ bX ℝ≥0, (∀ w, v w = S.bellmanOp v w) → v = (S.toDP hgreedy).vstar) ∧
      ∀ σ, (S.toDP hgreedy).IsOptimal σ ↔ S.IsGreedy (S.toDP hgreedy).vstar σ := by
  obtain ⟨-, -, hfix, hopt, hex, -⟩ := (S.toDP hgreedy).optimality
  have hmem := (S.toDP hgreedy).vstar_mem
  refine ⟨hex, hmem, fun w => ?_, fun v hv h => (hfix v hv).1 (funext fun w => ?_),
    fun σ => (hopt σ).trans (isGreedy_iff hgreedy _ σ).symm⟩
  · rw [← bellman_eq hgreedy hmem, (S.toDP hgreedy).bellman_vstar]
  · rw [bellman_eq hgreedy hv]; exact (h w).symm

end OptimalSavings

end SargentStachurski.PreludeExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal savings without labor income: the CRRA solution

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.3.2.3 (pp. 43–45).

With `Y ≡ 0`, CRRA utility `u(c) = c^{1−γ}/(1 − γ)` (`γ > 0`, `γ ≠ 1`) (1.52), `R > 0` and
`βR^{1−γ} < 1`:

* **Exercise 1.3.3**: lifetime values of all feasible policies are bounded above by a function
  `m(w)`: every partial sum `∑_{t<n} βᵗu(C_t)` is at most `u(w)/(1 − βR^{1−γ})` when `γ < 1`
  and at most `0` when `γ > 1`.
* (1.55): `η = 1 − (βR^{1−γ})^{1/γ}` lies in `(0, 1)` and `(1 − η)^γ = βR^{1−γ}`.
* (1.54): `v*(w) = η^{−γ}u(w)` solves the Bellman equation
  `v(w) = max_{0 < c < w} {u(c) + βv(R(w − c))}`, with the maximum attained at `c = ηw` (the
  linear policy (1.53)). The proof replaces the book's first-order condition by the tangent
  line inequality for the concave function `u`.
* The consumption growth factor is `C_{t+1}/C_t = R(1 − η) = (βR)^{1/γ}` (p. 45).
-/

open Finset

namespace SargentStachurski.PreludeExamples

/-- CRRA utility (1.52): `u(c) = c^{1−γ}/(1 − γ)`. -/
noncomputable def crra (γ c : ℝ) : ℝ := c ^ (1 - γ) / (1 - γ)

/-- Bernoulli's inequality in the form used here: for `p < 1`, `p ≠ 0` and `t > 0`,
`(tᵖ − 1)/p ≤ t − 1`. -/
theorem rpow_sub_one_div_le {p t : ℝ} (hp1 : p < 1) (hp0 : p ≠ 0) (ht : 0 < t) :
    (t ^ p - 1) / p ≤ t - 1 := by
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · -- `p < 0`: Bernoulli with exponent `1 − p ≥ 1` at `t⁻¹`
    have hb := one_add_mul_self_le_rpow_one_add (s := t⁻¹ - 1)
      (by have := inv_pos.2 ht; linarith) (p := 1 - p) (by linarith)
    rw [show 1 + (t⁻¹ - 1) = t⁻¹ by ring, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le,
      neg_sub] at hb
    have h2 : t ^ p = t * t ^ (p - 1) := by
      rw [← Real.rpow_one_add' ht.le (by linarith), show 1 + (p - 1) = p by ring]
    have h3 : 1 + p * (t - 1) ≤ t ^ p := by
      rw [h2]
      calc 1 + p * (t - 1) = t * (1 + (1 - p) * (t⁻¹ - 1)) := by field_simp; ring
        _ ≤ t * t ^ (p - 1) := mul_le_mul_of_nonneg_left hb ht.le
    rw [div_le_iff_of_neg hneg]
    linarith
  · -- `0 < p < 1`
    have hb := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hpos.le hp1.le
    rw [show 1 + (t - 1) = t by ring] at hb
    rw [div_le_iff₀ hpos]
    linarith

/-- The tangent line inequality for CRRA utility: `u(c) ≤ u(c₀) + c₀^{−γ}(c − c₀)` for
`c, c₀ > 0`, since `u` is concave with `u'(c₀) = c₀^{−γ}`. -/
theorem crra_le_tangent {γ c c₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≠ 1) (hc : 0 < c) (hc₀ : 0 < c₀) :
    crra γ c ≤ crra γ c₀ + c₀ ^ (-γ) * (c - c₀) := by
  have hp1 : 1 - γ < 1 := by linarith
  have hp0 : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  have key := rpow_sub_one_div_le hp1 hp0 (div_pos hc hc₀)
  rw [Real.div_rpow hc.le hc₀.le] at key
  have hc₀p : 0 < c₀ ^ (1 - γ) := Real.rpow_pos_of_pos hc₀ _
  have e2 : c₀ ^ (-γ) = c₀ ^ (1 - γ) / c₀ := by
    rw [show -γ = (1 - γ) - 1 by ring, Real.rpow_sub_one hc₀.ne']
  have h := mul_le_mul_of_nonneg_left key hc₀p.le
  have l : c₀ ^ (1 - γ) * ((c ^ (1 - γ) / c₀ ^ (1 - γ) - 1) / (1 - γ)) =
      c ^ (1 - γ) / (1 - γ) - c₀ ^ (1 - γ) / (1 - γ) := by
    field_simp
  have r : c₀ ^ (1 - γ) * (c / c₀ - 1) = c₀ ^ (1 - γ) / c₀ * (c - c₀) := by
    field_simp
  rw [l, r] at h
  rw [crra, crra, e2]
  linarith

variable {β R γ : ℝ}

/-- (1.55): `η = 1 − (βR^{1−γ})^{1/γ}`. -/
noncomputable def crraEta (β R γ : ℝ) : ℝ := 1 - (β * R ^ (1 - γ)) ^ (1 / γ)

/-- (1.55) (p. 44): if `0 < βR^{1−γ} < 1` then `0 < η < 1` and `(1 − η)^γ = βR^{1−γ}`. -/
theorem crraEta_spec (hγ : 0 < γ) (hk0 : 0 < β * R ^ (1 - γ)) (hk1 : β * R ^ (1 - γ) < 1) :
    0 < crraEta β R γ ∧ crraEta β R γ < 1 ∧ (1 - crraEta β R γ) ^ γ = β * R ^ (1 - γ) := by
  have hpos : 0 < (β * R ^ (1 - γ)) ^ (1 / γ) := Real.rpow_pos_of_pos hk0 _
  have hlt : (β * R ^ (1 - γ)) ^ (1 / γ) < 1 := Real.rpow_lt_one hk0.le hk1 (by positivity)
  refine ⟨by unfold crraEta; linarith, by unfold crraEta; linarith, ?_⟩
  rw [crraEta, sub_sub_cancel, one_div, Real.rpow_inv_rpow hk0.le hγ.ne']

/-- (p. 45): the consumption growth factor `R(1 − η)` equals `(βR)^{1/γ}`. -/
theorem crra_growth (hγ : 0 < γ) (hβ : 0 ≤ β) (hR : 0 < R) :
    R * (1 - crraEta β R γ) = (β * R) ^ (1 / γ) := by
  rw [crraEta, sub_sub_cancel, Real.mul_rpow hβ (Real.rpow_nonneg hR.le _),
    ← Real.rpow_mul hR.le, Real.mul_rpow hβ hR.le]
  have h1 : 1 + (1 - γ) * (1 / γ) = 1 / γ := by
    field_simp
    ring
  have : R * R ^ ((1 - γ) * (1 / γ)) = R ^ (1 / γ) := by
    rw [← Real.rpow_one_add' hR.le (by rw [h1]; positivity), h1]
  linear_combination β ^ (1 / γ) * this

/-- (1.54), the value: with `η` from (1.55) and `m = η^{−γ}`, the linear policy `c = ηw` attains
`u(ηw) + βm u(R(1 − η)w) = m u(w)`, so `v*(w) = η^{−γ}u(w)`. -/
theorem crra_value (hγ : 0 < γ) (hγ1 : γ ≠ 1) (hR : 0 < R) (hk0 : 0 < β * R ^ (1 - γ))
    (hk1 : β * R ^ (1 - γ) < 1) {w : ℝ} (hw : 0 < w) :
    crra γ (crraEta β R γ * w) +
        β * (crraEta β R γ ^ (-γ) * crra γ (R * (w - crraEta β R γ * w))) =
      crraEta β R γ ^ (-γ) * crra γ w := by
  obtain ⟨ha0, ha1, hb⟩ := crraEta_spec hγ hk0 hk1
  set a := crraEta β R γ
  have hb0 : 0 < 1 - a := by linarith
  have hp0 : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  have e1 : (a * w) ^ (1 - γ) = a * a ^ (-γ) * w ^ (1 - γ) := by
    rw [Real.mul_rpow ha0.le hw.le, show 1 - γ = 1 + -γ by ring,
      Real.rpow_add ha0, Real.rpow_one]
  have e2 : (R * (w - a * w)) ^ (1 - γ) = R ^ (1 - γ) * (1 - a) ^ (1 - γ) * w ^ (1 - γ) := by
    rw [show w - a * w = (1 - a) * w by ring, ← mul_assoc,
      Real.mul_rpow (mul_pos hR hb0).le hw.le, Real.mul_rpow hR.le hb0.le]
  have e3 : β * R ^ (1 - γ) * (1 - a) ^ (1 - γ) = 1 - a := by
    rw [← hb, ← Real.rpow_add hb0, show γ + (1 - γ) = 1 by ring, Real.rpow_one]
  simp only [crra, e1, e2]
  linear_combination (a ^ (-γ) * w ^ (1 - γ) / (1 - γ)) * e3

/-- (1.54), the maximum: for `0 < c < w`, `u(c) + βm u(R(w − c)) ≤ m u(w)` with `m = η^{−γ}`.
Together with `crra_value`, `v*(w) = η^{−γ}u(w)` solves the Bellman equation (1.54) and the
linear policy `σ(w) = ηw` (1.53) attains the maximum. -/
theorem crra_bellman_le (hγ : 0 < γ) (hγ1 : γ ≠ 1) (hR : 0 < R) (hk0 : 0 < β * R ^ (1 - γ))
    (hk1 : β * R ^ (1 - γ) < 1) {w c : ℝ} (hc : 0 < c) (hcw : c < w) :
    crra γ c + β * (crraEta β R γ ^ (-γ) * crra γ (R * (w - c))) ≤
      crraEta β R γ ^ (-γ) * crra γ w := by
  obtain ⟨ha0, ha1, hb⟩ := crraEta_spec hγ hk0 hk1
  have hw : 0 < w := hc.trans hcw
  set a := crraEta β R γ
  have hb0 : 0 < 1 - a := by linarith
  have hβ : 0 < β := by
    have : 0 < R ^ (1 - γ) := Real.rpow_pos_of_pos hR _
    exact pos_of_mul_pos_left hk0 this.le
  have hm : 0 < a ^ (-γ) := Real.rpow_pos_of_pos ha0 _
  -- tangent lines at `c₀ = ηw` and `d₀ = R(1 − η)w`
  have t1 := crra_le_tangent hγ hγ1 hc (mul_pos ha0 hw)
  have t2 := crra_le_tangent hγ hγ1 (mul_pos hR (sub_pos.2 hcw))
    (mul_pos hR (sub_pos.2 (show a * w < w by nlinarith)))
  -- the first-order condition `c₀^{−γ} = βmR d₀^{−γ}`
  have foc : (a * w) ^ (-γ) = β * a ^ (-γ) * R * (R * (w - a * w)) ^ (-γ) := by
    rw [show w - a * w = (1 - a) * w by ring, ← mul_assoc,
      Real.mul_rpow (mul_pos hR hb0).le hw.le, Real.mul_rpow hR.le hb0.le,
      Real.mul_rpow ha0.le hw.le]
    have hRR : R * R ^ (-γ) = R ^ (1 - γ) := by
      rw [show 1 - γ = 1 + -γ by ring, Real.rpow_add hR, Real.rpow_one]
    have hbb : (1 - a) ^ (-γ) = (β * R ^ (1 - γ))⁻¹ := by
      rw [Real.rpow_neg hb0.le, hb]
    rw [hbb]
    have hKK : β * R ^ (1 - γ) * (β * R ^ (1 - γ))⁻¹ = 1 := mul_inv_cancel₀ hk0.ne'
    linear_combination (-(β * a ^ (-γ) * (β * R ^ (1 - γ))⁻¹ * w ^ (-γ))) * hRR +
      (-(a ^ (-γ) * w ^ (-γ))) * hKK
  have hval := crra_value hγ hγ1 hR hk0 hk1 hw
  have hβm : 0 ≤ β * a ^ (-γ) := (mul_pos hβ hm).le
  have hsplit : R * (w - c) - R * (w - a * w) = -R * (c - a * w) := by ring
  rw [hsplit] at t2
  have t2' := mul_le_mul_of_nonneg_left t2 hβm
  calc crra γ c + β * (a ^ (-γ) * crra γ (R * (w - c)))
      = crra γ c + β * a ^ (-γ) * crra γ (R * (w - c)) := by ring
    _ ≤ (crra γ (a * w) + (a * w) ^ (-γ) * (c - a * w)) +
        β * a ^ (-γ) * (crra γ (R * (w - a * w)) +
          (R * (w - a * w)) ^ (-γ) * (-R * (c - a * w))) := add_le_add t1 t2'
    _ = a ^ (-γ) * crra γ w := by linear_combination hval + (c - a * w) * foc

/-! ### Exercise 1.3.3 -/

/-- Wealth along a deterministic path (`Y ≡ 0`): `W_{t+1} = R(W_t − σ(W_t))`. -/
def crraPath (R : ℝ) (σ : ℝ → ℝ) (w : ℝ) : ℕ → ℝ
  | 0 => w
  | t + 1 => R * (crraPath R σ w t - σ (crraPath R σ w t))

/-- **Exercise 1.3.3** (p. 43): if `βR^{1−γ} < 1`, every feasible policy (`0 ≤ σ(w) ≤ w`) has
lifetime value at most `m(w)`, where `m(w) = u(w)/(1 − βR^{1−γ})` for `γ < 1` and `m(w) = 0`
for `γ > 1`: every partial sum of `∑ βᵗu(σ(W_t))` is at most `m(w)`. -/
theorem crra_lifetime_bound (hγ1 : γ ≠ 1) (hβ : 0 ≤ β) (hR : 0 < R)
    (hk1 : β * R ^ (1 - γ) < 1) {σ : ℝ → ℝ} (hσ0 : ∀ w, 0 ≤ w → 0 ≤ σ w)
    (hσw : ∀ w, 0 ≤ w → σ w ≤ w) {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    ∑ t ∈ range n, β ^ t * crra γ (σ (crraPath R σ w t)) ≤
      if γ < 1 then crra γ w / (1 - β * R ^ (1 - γ)) else 0 := by
  -- the path stays in `[0, Rᵗw]`
  have hpath : ∀ t, 0 ≤ crraPath R σ w t ∧ crraPath R σ w t ≤ R ^ t * w := by
    intro t
    induction t with
    | zero => simp [crraPath, hw]
    | succ t ih =>
      obtain ⟨h0, h1⟩ := ih
      have := hσw _ h0
      have := hσ0 _ h0
      refine ⟨mul_nonneg hR.le (by linarith), ?_⟩
      simp only [crraPath, pow_succ]
      nlinarith
  split_ifs with hlt
  · -- `γ < 1`: `u ≥ 0` is increasing and `u(Rᵗw) = (R^{1−γ})ᵗu(w)`
    have hp : 0 < 1 - γ := by linarith
    have hk0 : 0 ≤ β * R ^ (1 - γ) := mul_nonneg hβ (Real.rpow_nonneg hR.le _)
    have hterm : ∀ t, β ^ t * crra γ (σ (crraPath R σ w t)) ≤
        (β * R ^ (1 - γ)) ^ t * crra γ w := by
      intro t
      obtain ⟨h0, h1⟩ := hpath t
      have hc0 := hσ0 _ h0
      have hc1 := (hσw _ h0).trans h1
      have hmono : σ (crraPath R σ w t) ^ (1 - γ) ≤ (R ^ t * w) ^ (1 - γ) :=
        Real.rpow_le_rpow hc0 hc1 hp.le
      have hsplit : (R ^ t * w) ^ (1 - γ) = (R ^ (1 - γ)) ^ t * w ^ (1 - γ) := by
        rw [Real.mul_rpow (pow_nonneg hR.le t) hw, ← Real.rpow_natCast_mul hR.le,
          mul_comm (t : ℝ), Real.rpow_mul_natCast hR.le]
      rw [mul_pow, mul_assoc, crra, crra]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ t)
      rw [← mul_div_assoc, ← hsplit]
      exact div_le_div_of_nonneg_right hmono hp.le
    calc ∑ t ∈ range n, β ^ t * crra γ (σ (crraPath R σ w t))
        ≤ ∑ t ∈ range n, (β * R ^ (1 - γ)) ^ t * crra γ w := sum_le_sum fun t _ => hterm t
      _ = crra γ w * ∑ t ∈ range n, (β * R ^ (1 - γ)) ^ t := by rw [mul_sum]; simp [mul_comm]
      _ ≤ crra γ w * (1 / (1 - β * R ^ (1 - γ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Real.rpow_nonneg hw _) hp.le)
          have hk1' : 0 < 1 - β * R ^ (1 - γ) := by linarith
          rw [geom_sum_eq (by linarith : β * R ^ (1 - γ) ≠ 1) n]
          have e : ((β * R ^ (1 - γ)) ^ n - 1) / (β * R ^ (1 - γ) - 1) =
              (1 - (β * R ^ (1 - γ)) ^ n) / (1 - β * R ^ (1 - γ)) := by
            rw [← neg_sub, ← neg_sub (1 : ℝ) (β * R ^ (1 - γ)), neg_div_neg_eq]
          rw [e]
          exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hk0 n]) hk1'.le
      _ = crra γ w / (1 - β * R ^ (1 - γ)) := by ring
  · -- `γ > 1`: `u ≤ 0`
    have hp : 1 - γ < 0 := by
      have : 1 < γ := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hγ1)
      linarith
    refine sum_nonpos fun t _ => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ t) ?_
    exact div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hσ0 _ (hpath t).1) _) hp.le

end SargentStachurski.PreludeExamples

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sequential analysis

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.4 (pp. 49–54).

Draws `Z₁, Z₂, …` are iid with density `f₀` or `f₁`; the state is the posterior probability
`π` that `f = f₁`.

* Bayes' rule (1.56): `κ(π, z) = πf₁(z)/((1 − π)f₀(z) + πf₁(z))` stays in `[0, 1]`, and the
  predictive density `ψ(π, z) = (1 − π)f₀(z) + πf₁(z)` (1.57) integrates to one.
* Beliefs are a martingale: `∫ κ(π, z)ψ(π, z) dz = π`.
* The Bellman operator of (1.58), `(Tg)(π) = min{πL₀, (1 − π)L₁, c + ∫ g(κ(π, z))ψ(π, z) dz}`,
  is order preserving and maps nonnegative functions to functions between `0` and
  `min{πL₀, (1 − π)L₁}`.

Theorem 1.4.1 (the optimal loss function uniquely solves (1.58), with optimal policies the
minimizers of `Q(π, a)`) has no discounting; the book proves it as Theorem 3.2.9, in Chapter 3.
-/

open MeasureTheory

namespace SargentStachurski.PreludeExamples

variable {f₀ f₁ : ℝ → ℝ}

/-- The predictive density (1.57): `ψ(π, z) = (1 − π)f₀(z) + πf₁(z)`. -/
def predDensity (f₀ f₁ : ℝ → ℝ) (π z : ℝ) : ℝ := (1 - π) * f₀ z + π * f₁ z

/-- Bayes' rule (1.56): `κ(π, z) = πf₁(z)/((1 − π)f₀(z) + πf₁(z))`. -/
noncomputable def bayesUpdate (f₀ f₁ : ℝ → ℝ) (π z : ℝ) : ℝ := π * f₁ z / predDensity f₀ f₁ π z

/-- (1.56): the posterior is a probability. -/
theorem bayesUpdate_mem_Icc (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) {π : ℝ}
    (hπ : π ∈ Set.Icc (0 : ℝ) 1) (z : ℝ) : bayesUpdate f₀ f₁ π z ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hπ
  have ha : 0 ≤ (1 - π) * f₀ z := mul_nonneg (by linarith) (hf₀ z)
  have hb : 0 ≤ π * f₁ z := mul_nonneg h0 (hf₁ z)
  refine ⟨div_nonneg hb (add_nonneg ha hb), ?_⟩
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · simp [bayesUpdate, predDensity, ← h]
  · exact (div_le_one h).2 (by linarith)

/-- `κ(π, z)ψ(π, z) = πf₁(z)`, also where `ψ(π, z) = 0`. -/
theorem bayesUpdate_mul_predDensity (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) {π : ℝ}
    (hπ : π ∈ Set.Icc (0 : ℝ) 1) (z : ℝ) :
    bayesUpdate f₀ f₁ π z * predDensity f₀ f₁ π z = π * f₁ z := by
  obtain ⟨h0, h1⟩ := hπ
  have ha : 0 ≤ (1 - π) * f₀ z := mul_nonneg (by linarith) (hf₀ z)
  have hb : 0 ≤ π * f₁ z := mul_nonneg h0 (hf₁ z)
  rcases eq_or_ne (predDensity f₀ f₁ π z) 0 with h | h
  · have : π * f₁ z = 0 := by simp only [predDensity] at h; linarith
    rw [h, this, mul_zero]
  · exact div_mul_cancel₀ _ h

/-- (1.57): the predictive density integrates to one. -/
theorem integral_predDensity (hi₀ : Integrable f₀) (hi₁ : Integrable f₁)
    (h₀ : ∫ z, f₀ z = 1) (h₁ : ∫ z, f₁ z = 1) (π : ℝ) : ∫ z, predDensity f₀ f₁ π z = 1 := by
  simp only [predDensity]
  rw [integral_add (hi₀.const_mul _) (hi₁.const_mul _), integral_const_mul, integral_const_mul,
    h₀, h₁]
  ring

/-- §1.4.1: beliefs are a martingale, `∫ κ(π, z)ψ(π, z) dz = π`. -/
theorem integral_bayesUpdate_mul_predDensity (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z)
    (h₁ : ∫ z, f₁ z = 1) {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    ∫ z, bayesUpdate f₀ f₁ π z * predDensity f₀ f₁ π z = π := by
  simp only [bayesUpdate_mul_predDensity hf₀ hf₁ hπ, integral_const_mul, h₁, mul_one]

/-- The Bellman operator of (1.58):
`(Tg)(π) = min{πL₀, (1 − π)L₁, c + ∫ g(κ(π, z))ψ(π, z) dz}`. -/
noncomputable def seqBellman (f₀ f₁ : ℝ → ℝ) (L₀ L₁ c : ℝ) (g : ℝ → ℝ) (π : ℝ) : ℝ :=
  min (π * L₀) (min ((1 - π) * L₁)
    (c + ∫ z, g (bayesUpdate f₀ f₁ π z) * predDensity f₀ f₁ π z))

/-- The Bellman operator (1.58) is order preserving on bounded measurable functions. -/
theorem seqBellman_mono (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) (hm₀ : Measurable f₀)
    (hm₁ : Measurable f₁) (hi₀ : Integrable f₀) (hi₁ : Integrable f₁) {L₀ L₁ c : ℝ}
    {g g' : ℝ → ℝ} (hg : Measurable g) (hg' : Measurable g') {M : ℝ} (hgM : ∀ x, |g x| ≤ M)
    (hgM' : ∀ x, |g' x| ≤ M) (hle : g ≤ g') {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    seqBellman f₀ f₁ L₀ L₁ c g π ≤ seqBellman f₀ f₁ L₀ L₁ c g' π := by
  have hψ : Integrable (predDensity f₀ f₁ π) := (hi₀.const_mul _).add (hi₁.const_mul _)
  have hψ0 : ∀ z, 0 ≤ predDensity f₀ f₁ π z := fun z =>
    add_nonneg (mul_nonneg (by linarith [hπ.2]) (hf₀ z)) (mul_nonneg hπ.1 (hf₁ z))
  have hκm : Measurable (bayesUpdate f₀ f₁ π) :=
    (measurable_const.mul hm₁).div ((measurable_const.mul hm₀).add (measurable_const.mul hm₁))
  have hint : ∀ {h : ℝ → ℝ}, Measurable h → (∀ x, |h x| ≤ M) →
      Integrable fun z => h (bayesUpdate f₀ f₁ π z) * predDensity f₀ f₁ π z := by
    intro h hh hhM
    refine hψ.bdd_mul (hh.comp hκm).aestronglyMeasurable (c := M) ?_
    exact Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hhM _
  refine min_le_min le_rfl (min_le_min le_rfl (add_le_add le_rfl ?_))
  exact integral_mono (hint hg hgM) (hint hg' hgM') fun z =>
    mul_le_mul_of_nonneg_right (hle _) (hψ0 z)

/-- The Bellman operator (1.58) maps nonnegative functions into `[0, min{πL₀, (1 − π)L₁}]`. -/
theorem seqBellman_mem (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) {L₀ L₁ c : ℝ}
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hc : 0 ≤ c) {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) {π : ℝ}
    (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ seqBellman f₀ f₁ L₀ L₁ c g π ∧
      seqBellman f₀ f₁ L₀ L₁ c g π ≤ min (π * L₀) ((1 - π) * L₁) := by
  obtain ⟨h0, h1⟩ := hπ
  have hψ0 : ∀ z, 0 ≤ predDensity f₀ f₁ π z := fun z =>
    add_nonneg (mul_nonneg (by linarith) (hf₀ z)) (mul_nonneg h0 (hf₁ z))
  have hI : 0 ≤ ∫ z, g (bayesUpdate f₀ f₁ π z) * predDensity f₀ f₁ π z :=
    integral_nonneg fun z => mul_nonneg (hg _) (hψ0 z)
  refine ⟨le_min (mul_nonneg h0 hL₀) (le_min (mul_nonneg (by linarith) hL₁) (by linarith)),
    le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))⟩

end SargentStachurski.PreludeExamples

set_option linter.style.longLine false
#print axioms SargentStachurski.PreludeExamples.IsBdd
#print axioms SargentStachurski.PreludeExamples.IsSupContraction
#print axioms SargentStachurski.PreludeExamples.IsUniformlyClosed
#print axioms SargentStachurski.PreludeExamples.isBdd_const
#print axioms SargentStachurski.PreludeExamples.IsBdd.sub
#print axioms SargentStachurski.PreludeExamples.IsBdd.add
#print axioms SargentStachurski.PreludeExamples.IsBdd.nonneg_bound
#print axioms SargentStachurski.PreludeExamples.IsBdd.exists_dist
#print axioms SargentStachurski.PreludeExamples.IsSupContraction.iterate
#print axioms SargentStachurski.PreludeExamples.IsSupContraction.eq_of_isFixedPt
#print axioms SargentStachurski.PreludeExamples.IsSupContraction.exists_limit
#print axioms SargentStachurski.PreludeExamples.IsSupContraction.globallyStable
#print axioms SargentStachurski.PreludeExamples.le_of_le_map_of_tendsto
#print axioms SargentStachurski.PreludeExamples.le_of_map_le_of_tendsto
#print axioms SargentStachurski.PreludeExamples.bX
#print axioms SargentStachurski.PreludeExamples.isUniformlyClosed_bX
#print axioms SargentStachurski.PreludeExamples.const_mem_bX
#print axioms SargentStachurski.PreludeExamples.abs_max_sub_max_le
#print axioms SargentStachurski.PreludeExamples.abs_ciSup_sub_ciSup_le
#print axioms SargentStachurski.PreludeExamples.ContractingDP
#print axioms SargentStachurski.PreludeExamples.ContractingDP.mk
#print axioms SargentStachurski.PreludeExamples.ContractingDP.V
#print axioms SargentStachurski.PreludeExamples.ContractingDP.T
#print axioms SargentStachurski.PreludeExamples.ContractingDP.β
#print axioms SargentStachurski.PreludeExamples.ContractingDP.β_nonneg
#print axioms SargentStachurski.PreludeExamples.ContractingDP.β_lt_one
#print axioms SargentStachurski.PreludeExamples.ContractingDP.nonempty
#print axioms SargentStachurski.PreludeExamples.ContractingDP.bdd
#print axioms SargentStachurski.PreludeExamples.ContractingDP.closed
#print axioms SargentStachurski.PreludeExamples.ContractingDP.mapsTo
#print axioms SargentStachurski.PreludeExamples.ContractingDP.mono
#print axioms SargentStachurski.PreludeExamples.ContractingDP.contraction
#print axioms SargentStachurski.PreludeExamples.ContractingDP.exists_greedy
#print axioms SargentStachurski.PreludeExamples.ContractingDP.globallyStable
#print axioms SargentStachurski.PreludeExamples.ContractingDP.vσ
#print axioms SargentStachurski.PreludeExamples.ContractingDP.vσ_mem
#print axioms SargentStachurski.PreludeExamples.ContractingDP.T_vσ
#print axioms SargentStachurski.PreludeExamples.ContractingDP.eq_vσ
#print axioms SargentStachurski.PreludeExamples.ContractingDP.tendsto_vσ
#print axioms SargentStachurski.PreludeExamples.ContractingDP.le_vσ
#print axioms SargentStachurski.PreludeExamples.ContractingDP.vσ_le
#print axioms SargentStachurski.PreludeExamples.ContractingDP.IsGreedy
#print axioms SargentStachurski.PreludeExamples.ContractingDP.nonempty_policy
#print axioms SargentStachurski.PreludeExamples.ContractingDP.greedy
#print axioms SargentStachurski.PreludeExamples.ContractingDP.isGreedy_greedy
#print axioms SargentStachurski.PreludeExamples.ContractingDP.bellman
#print axioms SargentStachurski.PreludeExamples.ContractingDP.bellman_mapsTo
#print axioms SargentStachurski.PreludeExamples.ContractingDP.T_le_bellman
#print axioms SargentStachurski.PreludeExamples.ContractingDP.isGreedy_iff
#print axioms SargentStachurski.PreludeExamples.ContractingDP.bellman_eq_iSup
#print axioms SargentStachurski.PreludeExamples.ContractingDP.bellman_mono
#print axioms SargentStachurski.PreludeExamples.ContractingDP.bellman_contraction
#print axioms SargentStachurski.PreludeExamples.ContractingDP.bellman_globallyStable
#print axioms SargentStachurski.PreludeExamples.ContractingDP.vstar
#print axioms SargentStachurski.PreludeExamples.ContractingDP.vstar_mem
#print axioms SargentStachurski.PreludeExamples.ContractingDP.bellman_vstar
#print axioms SargentStachurski.PreludeExamples.ContractingDP.eq_vstar
#print axioms SargentStachurski.PreludeExamples.ContractingDP.tendsto_bellman_iterate
#print axioms SargentStachurski.PreludeExamples.ContractingDP.vσ_le_vstar
#print axioms SargentStachurski.PreludeExamples.ContractingDP.vσ_eq_vstar_iff
#print axioms SargentStachurski.PreludeExamples.ContractingDP.IsOptimal
#print axioms SargentStachurski.PreludeExamples.ContractingDP.isOptimal_iff
#print axioms SargentStachurski.PreludeExamples.ContractingDP.optimality
#print axioms SargentStachurski.PreludeExamples.ContractingDP.vstar_le_of_bellman_le
#print axioms SargentStachurski.PreludeExamples.ContractingDP.le_vstar_of_le_bellman
#print axioms SargentStachurski.PreludeExamples.ContractingDP.hpiPolicy
#print axioms SargentStachurski.PreludeExamples.ContractingDP.vσ_hpi_le_succ
#print axioms SargentStachurski.PreludeExamples.ContractingDP.vσ_hpi_eq_vstar
#print axioms SargentStachurski.PreludeExamples.ContractingDP.hpi_terminates
#print axioms SargentStachurski.PreludeExamples.ContractingDP.opi
#print axioms SargentStachurski.PreludeExamples.ContractingDP.opi_step
#print axioms SargentStachurski.PreludeExamples.ContractingDP.tendsto_opi
#print axioms SargentStachurski.PreludeExamples.markovOp
#print axioms SargentStachurski.PreludeExamples.integrable_of_mem_bX
#print axioms SargentStachurski.PreludeExamples.measurable_markovOp
#print axioms SargentStachurski.PreludeExamples.abs_markovOp_le
#print axioms SargentStachurski.PreludeExamples.markovOp_mem_bX
#print axioms SargentStachurski.PreludeExamples.markovOp_mono
#print axioms SargentStachurski.PreludeExamples.markovOp_const
#print axioms SargentStachurski.PreludeExamples.markovOp_add
#print axioms SargentStachurski.PreludeExamples.markovOp_sub
#print axioms SargentStachurski.PreludeExamples.markovOp_smul
#print axioms SargentStachurski.PreludeExamples.markovOp_sub_const
#print axioms SargentStachurski.PreludeExamples.abs_markovOp_sub_le
#print axioms SargentStachurski.PreludeExamples.IsMarkovLike
#print axioms SargentStachurski.PreludeExamples.IsMarkovLike.mk
#print axioms SargentStachurski.PreludeExamples.IsMarkovLike.mapsTo
#print axioms SargentStachurski.PreludeExamples.IsMarkovLike.add
#print axioms SargentStachurski.PreludeExamples.IsMarkovLike.smul
#print axioms SargentStachurski.PreludeExamples.IsMarkovLike.mono
#print axioms SargentStachurski.PreludeExamples.IsMarkovLike.abs_le
#print axioms SargentStachurski.PreludeExamples.isMarkovLike_markovOp
#print axioms SargentStachurski.PreludeExamples.IsMarkovLike.sub
#print axioms SargentStachurski.PreludeExamples.IsMarkovLike.abs_sub_le
#print axioms SargentStachurski.PreludeExamples.IsMarkovLike.iterate_mem
#print axioms SargentStachurski.PreludeExamples.IsMarkovLike.abs_iterate_le
#print axioms SargentStachurski.PreludeExamples.affineOp
#print axioms SargentStachurski.PreludeExamples.affineOp_mapsTo
#print axioms SargentStachurski.PreludeExamples.affineOp_mono
#print axioms SargentStachurski.PreludeExamples.affineOp_contraction
#print axioms SargentStachurski.PreludeExamples.affineOp_globallyStable
#print axioms SargentStachurski.PreludeExamples.affineOp_iterate_zero
#print axioms SargentStachurski.PreludeExamples.affineOp_hasSum
#print axioms SargentStachurski.PreludeExamples.FirmProblem
#print axioms SargentStachurski.PreludeExamples.FirmProblem.mk
#print axioms SargentStachurski.PreludeExamples.FirmProblem.P
#print axioms SargentStachurski.PreludeExamples.FirmProblem.isMarkov
#print axioms SargentStachurski.PreludeExamples.FirmProblem.profit
#print axioms SargentStachurski.PreludeExamples.FirmProblem.profit_mem
#print axioms SargentStachurski.PreludeExamples.FirmProblem.β
#print axioms SargentStachurski.PreludeExamples.FirmProblem.β_nonneg
#print axioms SargentStachurski.PreludeExamples.FirmProblem.β_lt_one
#print axioms SargentStachurski.PreludeExamples.FirmProblem.s
#print axioms SargentStachurski.PreludeExamples.FirmPolicy
#print axioms SargentStachurski.PreludeExamples.FirmProblem.isMarkovLike_P
#print axioms SargentStachurski.PreludeExamples.FirmProblem.valOp
#print axioms SargentStachurski.PreludeExamples.FirmProblem.valOp_mapsTo
#print axioms SargentStachurski.PreludeExamples.FirmProblem.valOp_contraction
#print axioms SargentStachurski.PreludeExamples.FirmProblem.valuation_globallyStable
#print axioms SargentStachurski.PreludeExamples.FirmProblem.value
#print axioms SargentStachurski.PreludeExamples.FirmProblem.value_mem
#print axioms SargentStachurski.PreludeExamples.FirmProblem.value_eq
#print axioms SargentStachurski.PreludeExamples.FirmProblem.value_hasSum
#print axioms SargentStachurski.PreludeExamples.FirmProblem.Tσ
#print axioms SargentStachurski.PreludeExamples.FirmProblem.Tσ_eq
#print axioms SargentStachurski.PreludeExamples.FirmProblem.Tσ_mapsTo
#print axioms SargentStachurski.PreludeExamples.FirmProblem.Tσ_mono
#print axioms SargentStachurski.PreludeExamples.FirmProblem.Tσ_contraction
#print axioms SargentStachurski.PreludeExamples.FirmProblem.measurable_sellPolicy
#print axioms SargentStachurski.PreludeExamples.FirmProblem.Tσ_le_max
#print axioms SargentStachurski.PreludeExamples.FirmProblem.Tσ_sellPolicy
#print axioms SargentStachurski.PreludeExamples.FirmProblem.toDP
#print axioms SargentStachurski.PreludeExamples.FirmProblem.bellman_eq
#print axioms SargentStachurski.PreludeExamples.FirmProblem.IsGreedy
#print axioms SargentStachurski.PreludeExamples.FirmProblem.isGreedy_iff
#print axioms SargentStachurski.PreludeExamples.FirmProblem.isGreedy_iff_bellman
#print axioms SargentStachurski.PreludeExamples.FirmProblem.abs_vσ_le
#print axioms SargentStachurski.PreludeExamples.FirmProblem.theorem_1_1_1
#print axioms SargentStachurski.PreludeExamples.FirmProblem.sellPolicy_optimal
#print axioms SargentStachurski.PreludeExamples.entropicCE
#print axioms SargentStachurski.PreludeExamples.entropicCE_gaussianReal
#print axioms SargentStachurski.PreludeExamples.entropicCE_le_integral
#print axioms SargentStachurski.PreludeExamples.valueAtRisk
#print axioms SargentStachurski.PreludeExamples.valueAtRisk_anti
#print axioms SargentStachurski.PreludeExamples.IsShiftMonotone
#print axioms SargentStachurski.PreludeExamples.IsShiftMonotone.mk
#print axioms SargentStachurski.PreludeExamples.IsShiftMonotone.mapsTo
#print axioms SargentStachurski.PreludeExamples.IsShiftMonotone.mono
#print axioms SargentStachurski.PreludeExamples.IsShiftMonotone.shift
#print axioms SargentStachurski.PreludeExamples.IsShiftMonotone.abs_sub_le
#print axioms SargentStachurski.PreludeExamples.FirmProblem.TσK
#print axioms SargentStachurski.PreludeExamples.FirmProblem.toDPK
#print axioms SargentStachurski.PreludeExamples.FirmProblem.riskAdjusted_optimality
#print axioms SargentStachurski.PreludeExamples.entropicOp
#print axioms SargentStachurski.PreludeExamples.isShiftMonotone_entropicOp
#print axioms SargentStachurski.PreludeExamples.meanVariance
#print axioms SargentStachurski.PreludeExamples.meanVariance_not_monotone
#print axioms SargentStachurski.PreludeExamples.FiniteMDP
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.mk
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.Γ
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.Γ_nonempty
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.r
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.β
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.β_nonneg
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.β_lt_one
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.P
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.P_nonneg
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.P_sum
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.Policy
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.Q
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.Tσ
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.isBdd_of_finite
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.abs_sum_sub_le
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.Q_mono
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.abs_Q_sub_le
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.Q_sub_const
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.exists_greedy
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.toDP
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.IsGreedy
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.isGreedy_iff
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.bellman_eq
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.bellman_contraction
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.Pσ
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.rσ
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.Tσ_eq_mulVec
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.abs_Pσ_mulVec_le
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.vσ_eq_inv
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.vσ_hasSum
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.abs_vσ_le
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.finite_policy
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.theorem_1_2_1
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.theorem_1_2_2
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.vstar_le
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.IsLPFeasible
#print axioms SargentStachurski.PreludeExamples.FiniteMDP.lp_solution
#print axioms SargentStachurski.PreludeExamples.CashManagement
#print axioms SargentStachurski.PreludeExamples.CashManagement.mk
#print axioms SargentStachurski.PreludeExamples.CashManagement.wbar
#print axioms SargentStachurski.PreludeExamples.CashManagement.k
#print axioms SargentStachurski.PreludeExamples.CashManagement.φ
#print axioms SargentStachurski.PreludeExamples.CashManagement.φ_nonneg
#print axioms SargentStachurski.PreludeExamples.CashManagement.φ_sum
#print axioms SargentStachurski.PreludeExamples.CashManagement.ρ
#print axioms SargentStachurski.PreludeExamples.CashManagement.c
#print axioms SargentStachurski.PreludeExamples.CashManagement.τ
#print axioms SargentStachurski.PreludeExamples.CashManagement.p
#print axioms SargentStachurski.PreludeExamples.CashManagement.β
#print axioms SargentStachurski.PreludeExamples.CashManagement.β_nonneg
#print axioms SargentStachurski.PreludeExamples.CashManagement.β_lt_one
#print axioms SargentStachurski.PreludeExamples.CashManagement.Ξ
#print axioms SargentStachurski.PreludeExamples.CashManagement.next
#print axioms SargentStachurski.PreludeExamples.CashManagement.profit
#print axioms SargentStachurski.PreludeExamples.CashManagement.toMDP
#print axioms SargentStachurski.PreludeExamples.CashManagement.optimality
#print axioms SargentStachurski.PreludeExamples.CTMDP
#print axioms SargentStachurski.PreludeExamples.CTMDP.mk
#print axioms SargentStachurski.PreludeExamples.CTMDP.Γ
#print axioms SargentStachurski.PreludeExamples.CTMDP.Γ_nonempty
#print axioms SargentStachurski.PreludeExamples.CTMDP.δ
#print axioms SargentStachurski.PreludeExamples.CTMDP.δ_pos
#print axioms SargentStachurski.PreludeExamples.CTMDP.r
#print axioms SargentStachurski.PreludeExamples.CTMDP.Q
#print axioms SargentStachurski.PreludeExamples.CTMDP.Q_nonneg
#print axioms SargentStachurski.PreludeExamples.CTMDP.Q_sum
#print axioms SargentStachurski.PreludeExamples.CTMDP.Qσ
#print axioms SargentStachurski.PreludeExamples.CTMDP.rσ
#print axioms SargentStachurski.PreludeExamples.CTMDP.vσ
#print axioms SargentStachurski.PreludeExamples.CTMDP.uniformize
#print axioms SargentStachurski.PreludeExamples.CTMDP.sub_Qσ_eq
#print axioms SargentStachurski.PreludeExamples.CTMDP.vσ_eq_uniformize
#print axioms SargentStachurski.PreludeExamples.CTMDP.Q_uniformize
#print axioms SargentStachurski.PreludeExamples.CTMDP.sup'_div_add
#print axioms SargentStachurski.PreludeExamples.CTMDP.bellman_iff_hjb
#print axioms SargentStachurski.PreludeExamples.CTMDP.isGreedy_uniformize_iff
#print axioms SargentStachurski.PreludeExamples.queueRate
#print axioms SargentStachurski.PreludeExamples.queueQ
#print axioms SargentStachurski.PreludeExamples.sum_fin_ite_val_eq
#print axioms SargentStachurski.PreludeExamples.queueQ_diag
#print axioms SargentStachurski.PreludeExamples.serviceRate
#print axioms SargentStachurski.PreludeExamples.abs_queueQ_diag_le
#print axioms SargentStachurski.PreludeExamples.abs_queueQ_diag_interior
#print axioms SargentStachurski.PreludeExamples.abs_queueQ_diag_capacity_one
#print axioms SargentStachurski.PreludeExamples.serviceRateMDP
#print axioms SargentStachurski.PreludeExamples.serviceRate_optimality
#print axioms SargentStachurski.PreludeExamples.OptimalSavings
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.mk
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.u
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.u_cont
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.u_bdd
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.φ
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.φ_prob
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.β
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.β_nonneg
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.β_lt_one
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.R
#print axioms SargentStachurski.PreludeExamples.SavingsPolicy
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.cont
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.Pσ
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.rσ
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.Tσ
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.integrable_comp
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.abs_cont_le
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.isMarkovLike_Pσ
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.rσ_mem
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.Tσ_mapsTo
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.Tσ_globallyStable
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.vσ_hasSum
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.abs_fixedPoint_le
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.objective
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.bellmanOp
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.bddAbove_objective
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.bellmanOp_contraction
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.IsGreedy
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.toDP
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.isGreedy_iff
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.bellman_eq
#print axioms SargentStachurski.PreludeExamples.OptimalSavings.dp_results
#print axioms SargentStachurski.PreludeExamples.crra
#print axioms SargentStachurski.PreludeExamples.rpow_sub_one_div_le
#print axioms SargentStachurski.PreludeExamples.crra_le_tangent
#print axioms SargentStachurski.PreludeExamples.crraEta
#print axioms SargentStachurski.PreludeExamples.crraEta_spec
#print axioms SargentStachurski.PreludeExamples.crra_growth
#print axioms SargentStachurski.PreludeExamples.crra_value
#print axioms SargentStachurski.PreludeExamples.crra_bellman_le
#print axioms SargentStachurski.PreludeExamples.crraPath
#print axioms SargentStachurski.PreludeExamples.crra_lifetime_bound
#print axioms SargentStachurski.PreludeExamples.predDensity
#print axioms SargentStachurski.PreludeExamples.bayesUpdate
#print axioms SargentStachurski.PreludeExamples.bayesUpdate_mem_Icc
#print axioms SargentStachurski.PreludeExamples.bayesUpdate_mul_predDensity
#print axioms SargentStachurski.PreludeExamples.integral_predDensity
#print axioms SargentStachurski.PreludeExamples.integral_bayesUpdate_mul_predDensity
#print axioms SargentStachurski.PreludeExamples.seqBellman
#print axioms SargentStachurski.PreludeExamples.seqBellman_mono
#print axioms SargentStachurski.PreludeExamples.seqBellman_mem
