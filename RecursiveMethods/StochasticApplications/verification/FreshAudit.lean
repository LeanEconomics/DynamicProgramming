import Mathlib
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Correspondences

SLP §3.3, pp. 56–61, carried over from the Chapter 3 project (`RecursiveMethods/
MathematicalPreliminaries`): lower and upper hemi-continuity on metric spaces (`IsLHC`, `IsUHC`),
the graph, Exercise 3.11a (`continuousAt_of_isUHC_singleton`) and Exercise 3.15
(`isCompact_graph`).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.StochasticApplications

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `Γ` is **lower hemi-continuous** at `x` (SLP p. 56). -/
def IsLHC (Γ : X → Set Y) (x : X) : Prop :=
  (Γ x).Nonempty ∧ ∀ y ∈ Γ x, ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) →
    ∃ N, ∃ ys : ℕ → Y, (∀ n ≥ N, ys n ∈ Γ (xs n)) ∧ Tendsto ys atTop (𝓝 y)

/-- `Γ` is **upper hemi-continuous** at `x` (SLP p. 56; the book applies it to compact-valued
correspondences). -/
def IsUHC (Γ : X → Set Y) (x : X) : Prop :=
  (Γ x).Nonempty ∧ ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) → ∀ ys : ℕ → Y, (∀ n, ys n ∈ Γ (xs n)) →
    ∃ y ∈ Γ x, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (ys ∘ φ) atTop (𝓝 y)

/-- The graph `A = {(x, y) : y ∈ Γ(x)}`. -/
def graph (Γ : X → Set Y) : Set (X × Y) := {p | p.2 ∈ Γ p.1}

/-- **Ex 3.11a.** A single-valued u.h.c. correspondence is continuous. -/
theorem continuousAt_of_isUHC_singleton {f : X → Y} {x : X} (h : IsUHC (fun x => {f x}) x) :
    ContinuousAt f x := by
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro xs hxs
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨y, hy, φ, -, hφ⟩ := h.2 (xs ∘ ns) (hxs.comp hns) (fun n => f (xs (ns n))) fun n => rfl
  rw [mem_singleton_iff] at hy
  exact ⟨φ, by rw [← hy]; exact hφ⟩

/-- **Ex 3.15.** A compact-valued u.h.c. correspondence on a compact space has a compact graph. -/
theorem isCompact_graph [CompactSpace X] {Γ : X → Set Y} (h : ∀ x, IsUHC Γ x) :
    IsCompact (graph Γ) := by
  refine IsSeqCompact.isCompact fun ps hps => ?_
  obtain ⟨x, -, ν, hν, hlim⟩ := isCompact_univ.tendsto_subseq (x := fun n => (ps n).1)
    fun _ => mem_univ _
  obtain ⟨y, hy, μ, hμ, hlim'⟩ := (h x).2 _ hlim (fun n => (ps (ν n)).2) fun n => hps (ν n)
  refine ⟨(x, y), hy, ν ∘ μ, hν.comp hμ, ?_⟩
  exact (Prod.tendsto_iff _ _).2 ⟨hlim.comp hμ.tendsto_atTop, hlim'⟩

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Contraction Mapping Theorem

SLP §3.2, pp. 49–53, carried over from the Chapter 3 project (`RecursiveMethods/
MathematicalPreliminaries`) so that this project is self-contained. Chapter 4 uses Theorem 3.2
and Corollary 1.

* `IsContraction` (p. 50): `ρ(Tx, Ty) ≤ βρ(x, y)` with `β ∈ (0, 1)`.
* `IsContraction.uniformContinuous` (Ex 3.8).
* `dist_iterate_succ_le`, `dist_iterate_le` ((1)–(2), p. 51), `cauchySeq_iterate`.
* `theorem_3_2` (**Contraction Mapping Theorem**): in a complete metric space a contraction has
  exactly one fixed point `v`, and `ρ(Tⁿv₀, v) ≤ βⁿρ(v₀, v)`; the proof follows the book.
* `dist_fixedPoint_le` (Ex 3.9): `ρ(Tⁿv₀, v) ≤ ρ(Tⁿv₀, Tⁿ⁺¹v₀)/(1 − β)`.
* `corollary_1`: the fixed point lies in every nonempty closed set `T` maps into itself, and in
  every `S''` with `T(S') ⊆ S'' ⊆ S'`.
* `corollary_2` (**N-stage Contraction Theorem**).
-/

open Filter Topology

namespace StokeyLucasPrescott.StochasticApplications

variable {S : Type*} [MetricSpace S]

/-- `T` is a contraction with modulus `β ∈ (0, 1)` (SLP p. 50). -/
def IsContraction (T : S → S) (β : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧ ∀ x y, dist (T x) (T y) ≤ β * dist x y

variable {T : S → S} {β : ℝ}

/-- **Ex 3.8.** A contraction is uniformly continuous. -/
theorem IsContraction.uniformContinuous (hT : IsContraction T β) : UniformContinuous T :=
  Metric.uniformContinuous_iff.2 fun ε hε => ⟨ε, hε, fun {x y} h =>
    lt_of_le_of_lt (hT.2.2 x y) (by
      calc β * dist x y ≤ 1 * dist x y := mul_le_mul_of_nonneg_right hT.2.1.le dist_nonneg
        _ < ε := by rw [one_mul]; exact h)⟩

/-- (1), p. 51: `ρ(v_{n+1}, v_n) ≤ βⁿ ρ(v₁, v₀)`. -/
theorem dist_iterate_succ_le (hT : IsContraction T β) (v₀ : S) (n : ℕ) :
    dist (T^[n + 1] v₀) (T^[n] v₀) ≤ β ^ n * dist (T v₀) v₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    calc dist (T^[n + 1 + 1] v₀) (T^[n + 1] v₀) = dist (T (T^[n + 1] v₀)) (T (T^[n] v₀)) := by
          rw [Function.iterate_succ_apply' T (n + 1), Function.iterate_succ_apply' T n]
      _ ≤ β * dist (T^[n + 1] v₀) (T^[n] v₀) := hT.2.2 _ _
      _ ≤ β * (β ^ n * dist (T v₀) v₀) := mul_le_mul_of_nonneg_left ih hT.1.le
      _ = β * β ^ n * dist (T v₀) v₀ := by ring

/-- (2), p. 51: `ρ(v_m, v_n) ≤ βⁿ/(1 − β) ρ(v₁, v₀)` for `m ≥ n`. -/
theorem dist_iterate_le (hT : IsContraction T β) (v₀ : S) {m n : ℕ} (hmn : n ≤ m) :
    dist (T^[m] v₀) (T^[n] v₀) ≤ β ^ n / (1 - β) * dist (T v₀) v₀ := by
  have h1β : 0 < 1 - β := sub_pos.2 hT.2.1
  -- the telescoped bound `∑_{k=n}^{m−1} βᵏ ρ(v₁, v₀) = βⁿ(1 − β^{m−n})/(1 − β) ρ(v₁, v₀)`
  have key : ∀ j, dist (T^[n + j] v₀) (T^[n] v₀) ≤
      β ^ n * (1 - β ^ j) / (1 - β) * dist (T v₀) v₀ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h := dist_iterate_succ_le hT v₀ (n + j)
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
theorem cauchySeq_iterate (hT : IsContraction T β) (v₀ : S) : CauchySeq fun n => T^[n] v₀ := by
  have h1β : 0 < 1 - β := sub_pos.2 hT.2.1
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hlim : Tendsto (fun n => β ^ n / (1 - β) * dist (T v₀) v₀) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hT.1.le hT.2.1).div_const (1 - β)).mul_const
      (dist (T v₀) v₀)
    simpa using this
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  exact ⟨N, fun n hn => (dist_iterate_le hT v₀ hn).trans_lt (hN N le_rfl)⟩

/-- **Theorem 3.2 (Contraction Mapping Theorem).** If `(S, ρ)` is complete and `T` is a contraction
with modulus `β`, then (a) `T` has exactly one fixed point `v`, and (b) `ρ(Tⁿv₀, v) ≤ βⁿρ(v₀, v)`
for every `v₀`. The space must be nonempty. -/
theorem theorem_3_2 [CompleteSpace S] [Nonempty S] (hT : IsContraction T β) :
    ∃ v, T v = v ∧ (∀ w, T w = w → w = v) ∧
      ∀ v₀ (n : ℕ), dist (T^[n] v₀) v ≤ β ^ n * dist v₀ v := by
  -- existence: the limit of the successive approximations from any `v₀`
  obtain ⟨v₀⟩ : Nonempty S := inferInstance
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete (cauchySeq_iterate hT v₀)
  have hfix : T v = v := by
    have h1 : Tendsto (fun n => T (T^[n] v₀)) atTop (𝓝 (T v)) :=
      (hT.uniformContinuous.continuous.tendsto v).comp hv
    have h2 : Tendsto (fun n => T (T^[n] v₀)) atTop (𝓝 v) := by
      have := hv.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, Function.iterate_succ_apply'] using this
    exact tendsto_nhds_unique h1 h2
  -- uniqueness
  have huniq : ∀ w, T w = w → w = v := fun w hw => by
    by_contra hne
    have hpos : 0 < dist w v := dist_pos.2 hne
    have := hT.2.2 w v
    rw [hw, hfix] at this
    nlinarith [hT.2.1]
  -- the rate
  refine ⟨v, hfix, huniq, fun v₁ n => ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    calc dist (T (T^[n] v₁)) v = dist (T (T^[n] v₁)) (T v) := by rw [hfix]
      _ ≤ β * dist (T^[n] v₁) v := hT.2.2 _ _
      _ ≤ β * (β ^ n * dist v₁ v) := mul_le_mul_of_nonneg_left ih hT.1.le
      _ = β * β ^ n * dist v₁ v := by ring

/-- **Ex 3.9.** If `v` is the fixed point, `ρ(Tⁿv₀, v) ≤ ρ(Tⁿv₀, Tⁿ⁺¹v₀)/(1 − β)`. -/
theorem dist_fixedPoint_le (hT : IsContraction T β) {v : S} (hv : T v = v) (v₀ : S) (n : ℕ) :
    dist (T^[n] v₀) v ≤ dist (T^[n] v₀) (T^[n + 1] v₀) / (1 - β) := by
  have h1β : 0 < 1 - β := sub_pos.2 hT.2.1
  rw [le_div_iff₀ h1β]
  have h1 := dist_triangle (T^[n] v₀) (T^[n + 1] v₀) v
  have h2 : dist (T^[n + 1] v₀) v ≤ β * dist (T^[n] v₀) v := by
    rw [Function.iterate_succ_apply']
    conv_lhs => rw [← hv]
    exact hT.2.2 _ _
  nlinarith

/-- **Corollary 1.** The fixed point lies in every nonempty closed set `S'` with `T(S') ⊆ S'`,
and in every `S''` with `T(S') ⊆ S'' ⊆ S'`. (The book does not ask `S'` to be nonempty; for
`S' = ∅` the claim fails.) -/
theorem corollary_1 (hT : IsContraction T β) {v : S} (hv : T v = v) {S' S'' : Set S}
    (hne : S'.Nonempty) (hclosed : IsClosed S') (hmaps : Set.MapsTo T S' S')
    (hS'' : Set.MapsTo T S' S'') : v ∈ S' ∧ v ∈ S'' := by
  obtain ⟨v₀, hv₀⟩ := hne
  have hmem : ∀ n, T^[n] v₀ ∈ S' := fun n => hmaps.iterate n hv₀
  -- the iterates converge to the fixed point
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

/-- **Corollary 2 (N-stage Contraction Theorem).** If `S` is complete and `T^N` is a contraction
with modulus `β`, then `T` has exactly one fixed point `v`, and `ρ(T^{kN}v₀, v) ≤ βᵏρ(v₀, v)`. -/
theorem corollary_2 [CompleteSpace S] [Nonempty S] {N : ℕ} (hT : IsContraction T^[N] β) :
    ∃ v, T v = v ∧ (∀ w, T w = w → w = v) ∧
      ∀ v₀ (k : ℕ), dist (T^[k * N] v₀) v ≤ β ^ k * dist v₀ v := by
  obtain ⟨v, hv, huniq, hrate⟩ := theorem_3_2 hT
  -- the fixed point of `T^N` is a fixed point of `T`
  have hTv : T v = v := by
    have h := hT.2.2 (T v) v
    have hc : T^[N] (T v) = T v := by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hv]
    rw [hc, hv] at h
    by_contra hne
    have hpos : 0 < dist (T v) v := dist_pos.2 hne
    nlinarith [hT.2.1]
  refine ⟨v, hTv, fun w hw => huniq w (Function.iterate_fixed hw N), fun v₀ k => ?_⟩
  rw [mul_comm k N, Function.iterate_mul]
  exact hrate v₀ k

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Theorem of the Maximum

SLP §3.3, pp. 56–65, carried over from the Chapter 3 project (`RecursiveMethods/
MathematicalPreliminaries`).

For `f : X × Y → ℝ` and a correspondence `Γ`, `h(x) = max_{y ∈ Γ(x)} f(x, y)` (`maxValue`) and
`G(x) = {y ∈ Γ(x) : f(x, y) = h(x)}` (`argmax`).

* `theorem_3_6` (**Theorem of the Maximum**).
* `UniqueArgmax`, `argmaxFn`, `continuous_argmaxFn`, `lemma_3_7`, `theorem_3_8`: Lemma 3.7 and
  Theorem 3.8 for objectives with a unique maximizer. Chapter 3 proves them with `Γ`
  convex-valued in a normed space and `f(x, ·)` strictly concave; the proofs use only uniqueness
  of the maximizer, and Chapter 4 needs them on a convex subset of a normed space.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.StochasticApplications

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `h(x) = max_{y ∈ Γ(x)} f(x, y)`. -/
noncomputable def maxValue (f : X × Y → ℝ) (Γ : X → Set Y) (x : X) : ℝ :=
  sSup ((fun y => f (x, y)) '' Γ x)

/-- `G(x) = {y ∈ Γ(x) : f(x, y) = h(x)}`. -/
def argmax (f : X × Y → ℝ) (Γ : X → Set Y) (x : X) : Set Y :=
  {y | y ∈ Γ x ∧ f (x, y) = maxValue f Γ x}

variable {f : X × Y → ℝ} {Γ : X → Set Y}

theorem continuousOn_section (hf : ContinuousOn f (graph Γ)) (x : X) :
    ContinuousOn (fun y => f (x, y)) (Γ x) :=
  hf.comp (Continuous.prodMk_right x).continuousOn fun _ hy => hy

/-- On a compact nonempty `Γ(x)` the maximum is attained. -/
theorem exists_argmax (hf : ContinuousOn f (graph Γ)) {x : X} (hc : IsCompact (Γ x))
    (hne : (Γ x).Nonempty) :
    ∃ y ∈ Γ x, f (x, y) = maxValue f Γ x ∧ ∀ z ∈ Γ x, f (x, z) ≤ f (x, y) := by
  obtain ⟨y, hy, hmax⟩ := hc.exists_isMaxOn hne (continuousOn_section hf x)
  have hgr : IsGreatest ((fun y => f (x, y)) '' Γ x) (f (x, y)) :=
    ⟨⟨y, hy, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hmax hz⟩
  exact ⟨y, hy, hgr.csSup_eq.symm, fun z hz => hmax hz⟩

theorem le_maxValue (hf : ContinuousOn f (graph Γ)) {x : X} (hc : IsCompact (Γ x)) {z : Y}
    (hz : z ∈ Γ x) : f (x, z) ≤ maxValue f Γ x :=
  le_csSup ((hc.image_of_continuousOn (continuousOn_section hf x)).bddAbove) ⟨z, hz, rfl⟩

/-- Along a sequence in the graph converging to a graph point, `f` converges. -/
theorem tendsto_f_graph (hf : ContinuousOn f (graph Γ)) {xs : ℕ → X} {ys : ℕ → Y} {x : X} {y : Y}
    (hy : y ∈ Γ x) (hxs : Tendsto xs atTop (𝓝 x)) (hys : Tendsto ys atTop (𝓝 y)) {N : ℕ}
    (hmem : ∀ n ≥ N, ys n ∈ Γ (xs n)) :
    Tendsto (fun n => f (xs n, ys n)) atTop (𝓝 (f (x, y))) := by
  have hp : Tendsto (fun n => (xs n, ys n)) atTop (𝓝[graph Γ] (x, y)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Prod.tendsto_iff _ _).2 ⟨hxs, hys⟩,
      eventually_atTop.2 ⟨N, fun n hn => hmem n hn⟩⟩
  exact (hf (x, y) hy).tendsto.comp hp

/-- **Theorem 3.6 (Theorem of the Maximum).** If `f` is continuous on the graph and `Γ` is
compact-valued and continuous (l.h.c. and u.h.c.), then `h` is continuous and `G` is nonempty,
compact-valued and u.h.c. -/
theorem theorem_3_6 (hf : ContinuousOn f (graph Γ)) (hc : ∀ x, IsCompact (Γ x))
    (hl : ∀ x, IsLHC Γ x) (hu : ∀ x, IsUHC Γ x) :
    Continuous (maxValue f Γ) ∧
      ∀ x, (argmax f Γ x).Nonempty ∧ IsCompact (argmax f Γ x) ∧ IsUHC (argmax f Γ) x := by
  -- G is nonempty and compact
  have hGne : ∀ x, (argmax f Γ x).Nonempty := fun x => by
    obtain ⟨y, hy, hval, -⟩ := exists_argmax hf (hc x) (hu x).1
    exact ⟨y, hy, hval⟩
  have hGc : ∀ x, IsCompact (argmax f Γ x) := fun x => by
    have hcl : IsClosed (Γ x ∩ (fun y => f (x, y)) ⁻¹' {maxValue f Γ x}) :=
      (continuousOn_section hf x).preimage_isClosed_of_isClosed (hc x).isClosed isClosed_singleton
    exact (hc x).of_isClosed_subset hcl (fun y hy => hy.1)
  -- G is u.h.c.
  have hGu : ∀ x, IsUHC (argmax f Γ) x := fun x => by
    refine ⟨hGne x, fun xs hxs ys hys => ?_⟩
    obtain ⟨y, hy, ν, hν, hlim⟩ := (hu x).2 xs hxs ys fun n => (hys n).1
    refine ⟨y, ⟨hy, ?_⟩, ν, hν, hlim⟩
    refine le_antisymm (le_maxValue hf (hc x) hy) ?_
    obtain ⟨z, hz, hzval, -⟩ := exists_argmax hf (hc x) (hu x).1
    rw [← hzval]
    -- compare with a sequence converging to the maximizer `z`
    have hxν : Tendsto (xs ∘ ν) atTop (𝓝 x) := hxs.comp hν.tendsto_atTop
    obtain ⟨N, zs, hzs, hzlim⟩ := (hl x).2 z hz (xs ∘ ν) hxν
    have h1 := tendsto_f_graph hf hy hxν hlim (N := 0) fun n _ => (hys (ν n)).1
    have h2 := tendsto_f_graph hf hz hxν hzlim hzs
    refine le_of_tendsto_of_tendsto h2 h1 (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have hyn := hys (ν n)
    simp only [Function.comp_apply]
    rw [hyn.2]
    exact le_maxValue hf (hc _) (hzs n hn)
  refine ⟨continuous_iff_continuousAt.2 fun x => ?_, fun x => ⟨hGne x, hGc x, hGu x⟩⟩
  -- h is continuous: every subsequence has a further subsequence along which `h → h(x)`
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro xs hxs
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  choose ys hys using fun n => hGne (xs (ns n))
  obtain ⟨y, hy, φ, hφ, hlim⟩ := (hGu x).2 (xs ∘ ns) (hxs.comp hns) ys hys
  refine ⟨φ, ?_⟩
  have h1 := tendsto_f_graph hf hy.1 ((hxs.comp hns).comp hφ.tendsto_atTop) hlim (N := 0)
    fun n _ => (hys (φ n)).1
  rw [hy.2] at h1
  refine h1.congr fun n => ?_
  simp only [Function.comp_apply]
  exact (hys (φ n)).2

/-! ### Unique maximizers: Lemma 3.7 and Theorem 3.8 -/

/-- The hypotheses of Lemma 3.7 with uniqueness of the maximizer in place of strict concavity. -/
structure UniqueArgmax (Γ : X → Set Y) (f : X × Y → ℝ) : Prop where
  nonempty : ∀ x, (Γ x).Nonempty
  compact : ∀ x, IsCompact (Γ x)
  lhc : ∀ x, IsLHC Γ x
  uhc : ∀ x, IsUHC Γ x
  cont : ContinuousOn f (graph Γ)
  unique : ∀ x, ∀ y₁ ∈ argmax f Γ x, ∀ y₂ ∈ argmax f Γ x, y₁ = y₂

variable [Nonempty Y]

/-- The maximizer `g(x) = argmax_{y ∈ Γ(x)} f(x, y)`. -/
noncomputable def argmaxFn (Γ : X → Set Y) (f : X × Y → ℝ) (x : X) : Y :=
  Classical.epsilon fun y => y ∈ argmax f Γ x

namespace UniqueArgmax

variable (h : UniqueArgmax Γ f)
include h

theorem argmaxFn_mem (x : X) : argmaxFn Γ f x ∈ argmax f Γ x := by
  obtain ⟨y, hy, hval, -⟩ := exists_argmax h.cont (h.compact x) (h.nonempty x)
  exact Classical.epsilon_spec (p := fun y => y ∈ argmax f Γ x) ⟨y, hy, hval⟩

theorem argmax_eq (x : X) : argmax f Γ x = {argmaxFn Γ f x} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨h.argmaxFn_mem x, fun _ hy => h.unique x _ hy _
    (h.argmaxFn_mem x)⟩

/-- `f(x, y) < f(x, g(x))` for `y ≠ g(x)` in `Γ(x)`. -/
theorem lt_of_ne {x : X} {y : Y} (hy : y ∈ Γ x) (hne : y ≠ argmaxFn Γ f x) :
    f (x, y) < f (x, argmaxFn Γ f x) := by
  have hle : f (x, y) ≤ f (x, argmaxFn Γ f x) := by
    rw [(h.argmaxFn_mem x).2]
    exact le_maxValue h.cont (h.compact x) hy
  refine lt_of_le_of_ne hle fun heq => hne ?_
  have : y ∈ argmax f Γ x := ⟨hy, by rw [heq]; exact (h.argmaxFn_mem x).2⟩
  rw [h.argmax_eq x] at this
  exact this

/-- The maximizer is continuous (Theorem 3.6 with Ex 3.11a). -/
theorem continuous_argmaxFn : Continuous (argmaxFn Γ f) := by
  have h36 := theorem_3_6 h.cont h.compact h.lhc h.uhc
  refine continuous_iff_continuousAt.2 fun x => continuousAt_of_isUHC_singleton ?_
  have := (h36.2 x).2.2
  have heq : argmax f Γ = fun x => {argmaxFn Γ f x} := funext h.argmax_eq
  rwa [heq] at this

/-- **Lemma 3.7.** For each `ε > 0` and `x` there is `δ > 0` such that `y ∈ Γ(x)` and
`|f(x, g(x)) − f(x, y)| < δ` imply `ρ(g(x), y) < ε`. -/
theorem lemma_3_7 {ε : ℝ} (hε : 0 < ε) (x : X) :
    ∃ δ > 0, ∀ y ∈ Γ x, |f (x, argmaxFn Γ f x) - f (x, y)| < δ → dist (argmaxFn Γ f x) y < ε := by
  set g := argmaxFn Γ f x
  set K := Γ x ∩ {y | ε ≤ dist g y}
  have hK : IsCompact K := (h.compact x).inter_right
    (isClosed_le continuous_const (continuous_const.dist continuous_id))
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun y hy _ => ?_⟩
    by_contra hge
    have : y ∈ K := ⟨hy, not_lt.1 hge⟩
    rw [hK0] at this
    exact this
  have hcont : ContinuousOn (fun y => f (x, g) - f (x, y)) K :=
    continuousOn_const.sub ((continuousOn_section h.cont x).mono inter_subset_left)
  obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hKne hcont
  have hpos : 0 < f (x, g) - f (x, y₀) := by
    have hne : y₀ ≠ g := fun he => by
      have := hy₀.2
      simp only [Set.mem_ofPred_eq] at this
      rw [he, dist_self] at this
      linarith
    linarith [h.lt_of_ne hy₀.1 hne]
  refine ⟨f (x, g) - f (x, y₀), hpos, fun y hy hyδ => ?_⟩
  by_contra hge
  have hyK : y ∈ K := ⟨hy, not_lt.1 hge⟩
  have := isMinOn_iff.1 hmin y hyK
  have habs := le_abs_self (f (x, g) - f (x, y))
  linarith

/-- **Lemma 3.7 (compact `X`).** If `X` is compact, `δ` can be chosen independently of `x`. -/
theorem lemma_3_7_uniform [CompactSpace X] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, ∀ y ∈ Γ x,
      |f (x, argmaxFn Γ f x) - f (x, y)| < δ → dist (argmaxFn Γ f x) y < ε := by
  set g := argmaxFn Γ f
  have hg := h.continuous_argmaxFn
  set Aε := graph Γ ∩ {p : X × Y | ε ≤ dist (g p.1) p.2}
  have hA : IsCompact Aε := (isCompact_graph h.uhc).inter_right
    (isClosed_le continuous_const ((hg.comp continuous_fst).dist continuous_snd))
  rcases Aε.eq_empty_or_nonempty with hA0 | hAne
  · refine ⟨1, one_pos, fun x y hy _ => ?_⟩
    by_contra hge
    have : (x, y) ∈ Aε := ⟨hy, not_lt.1 hge⟩
    rw [hA0] at this
    exact this
  have hcont : ContinuousOn (fun p : X × Y => f (p.1, g p.1) - f p) Aε := by
    refine ContinuousOn.sub ?_ (h.cont.mono inter_subset_left)
    exact h.cont.comp (continuous_fst.prodMk (hg.comp continuous_fst)).continuousOn
      fun p _ => (h.argmaxFn_mem p.1).1
  obtain ⟨p₀, hp₀, hmin⟩ := hA.exists_isMinOn hAne hcont
  have hpos : 0 < f (p₀.1, g p₀.1) - f p₀ := by
    have hne : p₀.2 ≠ g p₀.1 := fun he => by
      have := hp₀.2
      simp only [Set.mem_ofPred_eq] at this
      rw [he, dist_self] at this
      linarith
    have := h.lt_of_ne hp₀.1 hne
    linarith
  refine ⟨_, hpos, fun x y hy hyδ => ?_⟩
  by_contra hge
  have hyA : (x, y) ∈ Aε := ⟨hy, not_lt.1 hge⟩
  have := isMinOn_iff.1 hmin (x, y) hyA
  have habs := le_abs_self (f (x, g x) - f (x, y))
  linarith

end UniqueArgmax

/-- The shortfall bound behind Theorem 3.8: if `|f − fₙ| < δ/2` on the graph, then
`|f(x, g(x)) − f(x, gₙ(x))| < δ`. -/
theorem shortfall_lt {f fn : X × Y → ℝ} (hf : UniqueArgmax Γ f) (hfn : UniqueArgmax Γ fn)
    {δ : ℝ} (hclose : ∀ p ∈ graph Γ, |f p - fn p| < δ / 2) (x : X) :
    |f (x, argmaxFn Γ f x) - f (x, argmaxFn Γ fn x)| < δ := by
  set g := argmaxFn Γ f x
  set gn := argmaxFn Γ fn x
  have hg := hf.argmaxFn_mem x
  have hgn := hfn.argmaxFn_mem x
  have h1 : f (x, gn) ≤ f (x, g) := by rw [hg.2]; exact le_maxValue hf.cont (hf.compact x) hgn.1
  have h2 : fn (x, g) ≤ fn (x, gn) := by
    rw [hgn.2]; exact le_maxValue hfn.cont (hfn.compact x) hg.1
  have e1 := abs_lt.1 (hclose (x, g) hg.1)
  have e2 := abs_lt.1 (hclose (x, gn) hgn.1)
  rw [abs_of_nonneg (sub_nonneg.2 h1)]
  linarith [e1.1, e1.2, e2.1, e2.2]

/-- **Theorem 3.8.** If `fₙ → f` uniformly on the graph, each with a unique maximizer, then the
maximizers converge pointwise: `gₙ(x) → g(x)`. -/
theorem theorem_3_8 {fs : ℕ → X × Y → ℝ} (hf : UniqueArgmax Γ f)
    (hfs : ∀ n, UniqueArgmax Γ (fs n)) (hunif : TendstoUniformlyOn fs f atTop (graph Γ))
    (x : X) : Tendsto (fun n => argmaxFn Γ (fs n) x) atTop (𝓝 (argmaxFn Γ f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hlem⟩ := hf.lemma_3_7 hε x
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hunif) (δ / 2)
    (half_pos hδ))
  refine ⟨M, fun n hn => ?_⟩
  rw [dist_comm]
  refine hlem _ (hfs n |>.argmaxFn_mem x).1 (shortfall_lt hf (hfs n) (fun p hp => ?_) x)
  have := hM n hn p hp
  rwa [Real.dist_eq] at this

/-- **Theorem 3.8 (compact `X`).** If `X` is compact the convergence is uniform. -/
theorem theorem_3_8_uniform [CompactSpace X] {fs : ℕ → X × Y → ℝ}
    (hf : UniqueArgmax Γ f) (hfs : ∀ n, UniqueArgmax Γ (fs n))
    (hunif : TendstoUniformlyOn fs f atTop (graph Γ)) :
    TendstoUniformly (fun n => argmaxFn Γ (fs n)) (argmaxFn Γ f) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hlem⟩ := hf.lemma_3_7_uniform hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hunif) (δ / 2)
    (half_pos hδ))
  refine eventually_atTop.2 ⟨M, fun n hn x => ?_⟩
  refine hlem x _ (hfs n |>.argmaxFn_mem x).1 (shortfall_lt hf (hfs n) (fun p hp => ?_) x)
  have := hM n hn p hp
  rwa [Real.dist_eq] at this

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Differentiability of a concave function from below: Benveniste and Scheinkman

SLP §4.2, pp. 83–86.

* `theorem_4_10` (**Benveniste–Scheinkman**): if `V` is concave on a convex `X`, `x₀ ∈ int X`, and
  a function `W` differentiable at `x₀` satisfies `W(x₀) = V(x₀)` and `W ≤ V` near `x₀`, then `V`
  is differentiable at `x₀` with `DV(x₀) = DW(x₀)`. The proof needs no subgradients: near `x₀`,
  `W(x₀ + h) − W(x₀) ≤ V(x₀ + h) − V(x₀) ≤ V(x₀) − V(x₀ − h) ≤ W(x₀) − W(x₀ − h)`, the middle
  step by concavity at the midpoint `x₀`. Concavity of `W` (assumed in the book) is not needed.
* `ex_4_5`: from the first-order condition `U′(f(x) − g(x)) = βv′(g(x))` with `U`, `f`, `v`
  strictly increasing, strictly concave and differentiable, `0 < g(x′) − g(x) < f(x′) − f(x)`
  for `x′ > x`.
-/

open Filter Topology Asymptotics Set

namespace StokeyLucasPrescott.StochasticApplications

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 4.10 (Benveniste and Scheinkman).** Let `V` be concave on a convex set `X`,
`x₀ ∈ int X`, and `W` differentiable at `x₀` with `W(x₀) = V(x₀)` and `W ≤ V` on a neighborhood
of `x₀`. Then `V` is differentiable at `x₀` and `DV(x₀) = DW(x₀)`. -/
theorem theorem_4_10 {X : Set E} {V W : E → ℝ} {x₀ : E} {W' : E →L[ℝ] ℝ}
    (hV : ConcaveOn ℝ X V) (hx₀ : X ∈ 𝓝 x₀) (hW : HasFDerivAt W W' x₀) (heq : W x₀ = V x₀)
    (hle : ∀ᶠ x in 𝓝 x₀, W x ≤ V x) : HasFDerivAt V W' x₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hW ⊢
  set r : E → ℝ := fun h => W (x₀ + h) - W x₀ - W' h
  -- the remainder of `W` at `−h`
  have hr' : (fun h : E => r (-h)) =o[𝓝 0] fun h => h := by
    have := hW.comp_tendsto (show Tendsto (fun h : E => -h) (𝓝 0) (𝓝 0) by
      simpa using (continuous_neg (G := E)).tendsto 0)
    refine (this.trans_isBigO ?_)
    exact IsBigO.of_bound 1 (Eventually.of_forall fun h => by simp)
  -- `x₀ ± h ∈ X` and `W ≤ V` there, for `h` near `0`
  have hplus : ∀ᶠ h in 𝓝 (0 : E), x₀ + h ∈ X ∧ W (x₀ + h) ≤ V (x₀ + h) := by
    have hc : Tendsto (fun h : E => x₀ + h) (𝓝 0) (𝓝 x₀) := by
      simpa using (continuous_const_add x₀).tendsto (0 : E)
    exact (hc.eventually (Filter.eventually_mem_set.2 hx₀)).and (hc.eventually hle)
  have hminus : ∀ᶠ h in 𝓝 (0 : E), x₀ - h ∈ X ∧ W (x₀ - h) ≤ V (x₀ - h) := by
    have hc : Tendsto (fun h : E => x₀ - h) (𝓝 0) (𝓝 x₀) := by
      simpa using ((continuous_const.sub continuous_id).tendsto (0 : E) (f := fun h : E => x₀ - h))
    exact (hc.eventually (Filter.eventually_mem_set.2 hx₀)).and (hc.eventually hle)
  have hbound : ∀ᶠ h in 𝓝 (0 : E),
      ‖V (x₀ + h) - V x₀ - W' h‖ ≤ 1 * ‖‖r h‖ + ‖r (-h)‖‖ := by
    filter_upwards [hplus, hminus] with h hp hm
    have hx₀X : x₀ ∈ X := mem_of_mem_nhds hx₀
    -- concavity at the midpoint `x₀ = ½(x₀ + h) + ½(x₀ − h)`
    have hmid := hV.2 hp.1 hm.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have e : (1 / 2 : ℝ) • (x₀ + h) + (1 / 2 : ℝ) • (x₀ - h) = x₀ := by module
    rw [e, smul_eq_mul, smul_eq_mul] at hmid
    have er : r (-h) = W (x₀ - h) - W x₀ + W' h := by
      simp only [r, map_neg, ← sub_eq_add_neg]; ring
    rw [er, one_mul]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (add_nonneg (abs_nonneg (r h))
      (abs_nonneg (W (x₀ - h) - W x₀ + W' h))), abs_le]
    have h1 := hp.2
    have h2 := hm.2
    constructor
    · cases abs_cases (W (x₀ + h) - W x₀ - W' h) <;> cases abs_cases (W (x₀ - h) - W x₀ + W' h) <;>
        simp only [r] at * <;> linarith
    · cases abs_cases (W (x₀ + h) - W x₀ - W' h) <;> cases abs_cases (W (x₀ - h) - W x₀ + W' h) <;>
        simp only [r] at * <;> linarith
  have hsum : (fun h : E => ‖r h‖ + ‖r (-h)‖) =o[𝓝 0] fun h => h :=
    hW.norm_left.add hr'.norm_left
  exact (IsBigO.of_bound 1 hbound).trans_isLittleO hsum

/-- **Exercise 4.5.** Let `U`, `f`, `v` be strictly increasing, strictly concave and
differentiable on `ℝ₊`, `0 < g(x) < f(x)`, and `U′(f(x) − g(x)) = βv′(g(x))` with `β > 0`. Then
`0 < g(x′) − g(x) < f(x′) − f(x)` for `0 ≤ x < x′`. -/
theorem ex_4_5 {U f v g : ℝ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hUd : ∀ c ∈ Ici (0 : ℝ), DifferentiableAt ℝ U c)
    (hv : StrictConcaveOn ℝ (Ici 0) v) (hvd : ∀ c ∈ Ici (0 : ℝ), DifferentiableAt ℝ v c)
    (hf : StrictMonoOn f (Ici 0)) (hg : ∀ x ∈ Ici (0 : ℝ), 0 < g x ∧ g x < f x)
    (hfoc : ∀ x ∈ Ici (0 : ℝ), deriv U (f x - g x) = β * deriv v (g x))
    {x x' : ℝ} (hx : 0 ≤ x) (hxx' : x < x') :
    0 < g x' - g x ∧ g x' - g x < f x' - f x := by
  have hx' : 0 ≤ x' := hx.trans hxx'.le
  have hU' := hU.strictAntiOn_deriv hUd
  have hv' := hv.strictAntiOn_deriv hvd
  have hfx := hf hx hx' hxx'
  obtain ⟨g0, g1⟩ := hg x hx
  obtain ⟨g0', g1'⟩ := hg x' hx'
  have hc : (0 : ℝ) ≤ f x - g x := by linarith
  have hc' : (0 : ℝ) ≤ f x' - g x' := by linarith
  constructor
  · -- if `g(x′) ≤ g(x)` then consumption rises, contradicting the first-order condition
    by_contra hle
    push Not at hle
    have h1 : deriv v (g x) ≤ deriv v (g x') := hv'.antitoneOn g0'.le g0.le (by linarith)
    have h2 : f x - g x < f x' - g x' := by linarith
    have h3 := hU' hc hc' h2
    rw [hfoc x hx, hfoc x' hx'] at h3
    nlinarith
  · -- if `g` rises by at least `f`, consumption falls, again a contradiction
    by_contra hle
    push Not at hle
    have h2 : f x' - g x' ≤ f x - g x := by linarith
    have h3 : deriv U (f x - g x) ≤ deriv U (f x' - g x') := hU'.antitoneOn hc' hc h2
    rw [hfoc x hx, hfoc x' hx'] at h3
    have hgg : g x < g x' := by linarith
    have h4 := hv' g0.le g0'.le hgg
    nlinarith

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Measurable Selection Theorem

SLP §7.3, pp. 183–184: measurable selections and Theorem 7.6, which the book cites from
Hildenbrand (1974). It is proved here by **lexicographic minimization**.

A nonempty compact-valued correspondence `Φ : X → ℝᵐ` is *measurable* (`IsMeasCorr`) when
`{x : Φ(x) ∩ F ≠ ∅}` is measurable for every closed `F`. A compact-valued u.h.c. correspondence
on a metric space is measurable, since these sets are closed (`isMeasCorr_of_uhc`). For a
measurable `Φ`, the least `i`-th coordinate `x ↦ min {yᵢ : y ∈ Φ(x)}` is measurable
(`measurable_minCoord`), and the points of `Φ(x)` attaining it again form a measurable
correspondence (`IsMeasCorr.refine`): the key identity expresses the lower inverse through
rational thresholds. Minimizing the coordinates one after the other leaves a single point
whose coordinates are measurable functions (`theorem_7_6`).
-/

namespace StokeyLucasPrescott.StochasticApplications

open Set MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

/-- A **measurable selection** from `Γ` (SLP p. 183): a measurable `h` with `h(x) ∈ Γ(x)`. -/
def IsMeasurableSelection {Y : Type*} [MeasurableSpace Y] (Γ : X → Set Y) (h : X → Y) : Prop :=
  Measurable h ∧ ∀ x, h x ∈ Γ x

/-- A nonempty compact-valued correspondence whose lower inverses of closed sets are
measurable. -/
def IsMeasCorr (Φ : X → Set (Fin m → ℝ)) : Prop :=
  (∀ x, (Φ x).Nonempty ∧ IsCompact (Φ x)) ∧
    ∀ F : Set (Fin m → ℝ), IsClosed F → MeasurableSet {x | (Φ x ∩ F).Nonempty}

/-- The least `i`-th coordinate on `Φ(x)`. -/
noncomputable def minCoord (Φ : X → Set (Fin m → ℝ)) (i : Fin m) (x : X) : ℝ :=
  sInf ((fun y => y i) '' Φ x)

theorem minCoord_mem {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) (x : X) :
    ∃ y ∈ Φ x, y i = minCoord Φ i x := by
  have hK := ((hΦ.1 x).2.image (continuous_apply i))
  exact hK.sInf_mem ((hΦ.1 x).1.image _)

theorem minCoord_le {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) {x : X}
    {y : Fin m → ℝ} (hy : y ∈ Φ x) : minCoord Φ i x ≤ y i :=
  csInf_le ((hΦ.1 x).2.image (continuous_apply i)).bddBelow (mem_image_of_mem _ hy)

/-- The least coordinate is measurable: `{x : min yᵢ ≤ a} = {x : Φ(x) ∩ {yᵢ ≤ a} ≠ ∅}`. -/
theorem measurable_minCoord {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) :
    Measurable (minCoord Φ i) := by
  refine measurable_of_Iic fun a => ?_
  change MeasurableSet {x | minCoord Φ i x ≤ a}
  have heq : {x | minCoord Φ i x ≤ a} = {x | (Φ x ∩ {y | y i ≤ a}).Nonempty} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor
    · intro hx
      obtain ⟨y, hy, hyi⟩ := minCoord_mem hΦ i x
      exact ⟨y, hy, by rw [mem_ofPred_eq, hyi]; exact hx⟩
    · rintro ⟨y, hy, hya⟩
      exact (minCoord_le hΦ i hy).trans hya
  rw [heq]
  exact hΦ.2 _ (isClosed_le (continuous_apply i) continuous_const)

/-- The points of `Φ(x)` minimizing the `i`-th coordinate. -/
def refineCorr (Φ : X → Set (Fin m → ℝ)) (i : Fin m) (x : X) : Set (Fin m → ℝ) :=
  Φ x ∩ {y | y i = minCoord Φ i x}

/-- **The minimizers again form a measurable correspondence.** -/
theorem IsMeasCorr.refine {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) :
    IsMeasCorr (refineCorr Φ i) := by
  refine ⟨fun x => ⟨?_, ?_⟩, fun F hF => ?_⟩
  · obtain ⟨y, hy, hyi⟩ := minCoord_mem hΦ i x
    exact ⟨y, hy, hyi⟩
  · exact (hΦ.1 x).2.inter_right (isClosed_eq (continuous_apply i) continuous_const)
  · have heq : {x | (refineCorr Φ i x ∩ F).Nonempty} =
        ⋂ q : ℚ, ({x | (q : ℝ) ≤ minCoord Φ i x} ∪
          ⋃ n : ℕ, {x | (Φ x ∩ (F ∩ {y | y i ≤ q - 1 / ((n : ℝ) + 1)})).Nonempty}) := by
      ext x
      simp only [refineCorr, mem_ofPred_eq, mem_iInter, mem_union, mem_iUnion]
      constructor
      · rintro ⟨y, ⟨hy, hyi⟩, hyF⟩ q
        by_cases hq : (q : ℝ) ≤ minCoord Φ i x
        · exact Or.inl hq
        · push Not at hq
          right
          rw [mem_ofPred_eq] at hyi
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hq)
          exact ⟨n, y, hy, hyF, by rw [mem_ofPred_eq, hyi]; linarith⟩
      · intro hx
        by_contra hne
        set K := Φ x ∩ F
        have hKc : IsCompact K := (hΦ.1 x).2.inter_right hF
        have hall : ∀ y ∈ K, minCoord Φ i x < y i := fun y hy => by
          refine lt_of_le_of_ne (minCoord_le hΦ i hy.1) fun h => hne ⟨y, ⟨hy.1, h.symm⟩, hy.2⟩
        by_cases hKe : K.Nonempty
        · obtain ⟨y₀, hy₀, hmin⟩ := hKc.exists_isMinOn hKe (continuous_apply i).continuousOn
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (hall y₀ hy₀)
          rcases hx q with h | ⟨n, y, hy, hyF, hyq⟩
          · exact absurd h (not_le.2 hq1)
          · have : y₀ i ≤ y i := hmin ⟨hy, hyF⟩
            have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            rw [mem_ofPred_eq] at hyq
            linarith
        · obtain ⟨q, hq⟩ := exists_rat_gt (minCoord Φ i x)
          rcases hx q with h | ⟨n, y, hy, hyF, -⟩
          · exact absurd h (not_le.2 hq)
          · exact hKe ⟨y, hy, hyF⟩
    rw [heq]
    refine MeasurableSet.iInter fun q => ?_
    refine (measurableSet_le measurable_const (measurable_minCoord hΦ i)).union ?_
    exact MeasurableSet.iUnion fun n => hΦ.2 _
      (hF.inter (isClosed_le (continuous_apply i) continuous_const))

/-- The correspondences obtained by minimizing coordinates `0, 1, …, k − 1` in turn. -/
noncomputable def lexCorr (Γ : X → Set (Fin m → ℝ)) : ℕ → X → Set (Fin m → ℝ)
  | 0 => Γ
  | k + 1 => if h : k < m then refineCorr (lexCorr Γ k) ⟨k, h⟩ else lexCorr Γ k

theorem lexCorr_spec {Γ : X → Set (Fin m → ℝ)} (hΓ : IsMeasCorr Γ) (k : ℕ) :
    IsMeasCorr (lexCorr Γ k) ∧ (∀ x, lexCorr Γ k x ⊆ Γ x) ∧
      ∀ i : Fin m, (i : ℕ) < k → ∀ x, ∀ y ∈ lexCorr Γ k x, y i = minCoord (lexCorr Γ i) i x := by
  induction k with
  | zero => exact ⟨hΓ, fun _ => subset_rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    by_cases hk : k < m
    · have hdef : lexCorr Γ (k + 1) = refineCorr (lexCorr Γ k) ⟨k, hk⟩ := by
        simp only [lexCorr, hk, ↓reduceDIte]
      rw [hdef]
      refine ⟨h1.refine _, fun x => inter_subset_left.trans (h2 x), fun i hi x y hy => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
      · exact h3 i hlt x y hy.1
      · have : i = ⟨k, hk⟩ := Fin.ext heq
        subst this
        exact hy.2
    · have hdef : lexCorr Γ (k + 1) = lexCorr Γ k := by simp only [lexCorr, hk, ↓reduceDIte]
      rw [hdef]
      refine ⟨h1, h2, fun i hi => h3 i ?_⟩
      have := i.2
      omega

/-- **A compact-valued u.h.c. correspondence is measurable**: for closed `F`, the set
`{x : Γ(x) ∩ F ≠ ∅}` is closed. -/
theorem isMeasCorr_of_uhc {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {Γ : X → Set (Fin m → ℝ)} (hΓ : ∀ x, IsUHC Γ x) (hK : ∀ x, IsCompact (Γ x)) :
    IsMeasCorr Γ := by
  refine ⟨fun x => ⟨(hΓ x).1, hK x⟩, fun F hF => ?_⟩
  refine IsClosed.measurableSet (IsSeqClosed.isClosed fun xs x hxs hlim => ?_)
  choose ys hys using hxs
  obtain ⟨y, hy, φ, -, hφ⟩ := (hΓ x).2 xs hlim ys fun n => (hys n).1
  exact ⟨y, hy, hF.mem_of_tendsto hφ (Eventually.of_forall fun n => (hys (φ n)).2)⟩

/-- **Theorem 7.6 (Measurable Selection Theorem).** A nonempty compact-valued u.h.c.
correspondence `Γ` from a metric space `X` (with its Borel sets; the book's `X` is a Borel set
in `ℝˡ`) into `ℝᵐ` has a measurable selection. -/
theorem theorem_7_6 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {Γ : X → Set (Fin m → ℝ)} (hΓ : ∀ x, IsUHC Γ x) (hK : ∀ x, IsCompact (Γ x)) :
    ∃ h : X → Fin m → ℝ, IsMeasurableSelection Γ h := by
  have hM := isMeasCorr_of_uhc hΓ hK
  obtain ⟨h1, h2, h3⟩ := lexCorr_spec hM m
  refine ⟨fun x (i : Fin m) => minCoord (lexCorr Γ i) i x, ?_, fun x => ?_⟩
  · exact measurable_pi_iff.2 fun i => measurable_minCoord (lexCorr_spec hM i).1 i
  · obtain ⟨y, hy⟩ := (h1.1 x).1
    have : y = fun (i : Fin m) => minCoord (lexCorr Γ i) i x := funext fun i => h3 i i.2 x y hy
    change (fun (i : Fin m) => minCoord (lexCorr Γ i) i x) ∈ Γ x
    rw [← this]
    exact h2 x hy

/-- **Theorem 7.6 with a target set `T`** (SLP's `T ⊆ ℝᵐ`): if `Γ(x) ⊆ T` for all `x`, the
selection is a measurable map into `T` with its subspace σ-algebra. -/
theorem theorem_7_6_subtype {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {T : Set (Fin m → ℝ)} {Γ : X → Set (Fin m → ℝ)} (hΓ : ∀ x, IsUHC Γ x)
    (hK : ∀ x, IsCompact (Γ x)) (hT : ∀ x, Γ x ⊆ T) :
    ∃ h : X → T, Measurable h ∧ ∀ x, (h x : Fin m → ℝ) ∈ Γ x := by
  obtain ⟨h, hm, hmem⟩ := theorem_7_6 hΓ hK
  exact ⟨fun x => ⟨h x, hT x (hmem x)⟩, hm.subtype_mk, hmem⟩

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition functions

SLP §8.1, pp. 212–220. A transition function (`IsTransitionFunction`) is exactly a Markov kernel
(`isTransitionFunction_iff`). The Markov operator `T` on nonnegative and on bounded measurable
functions (`markovOp`, `markovOpR`) and its adjoint `T*` on probability measures (`adjointOp`):
Theorem 8.1 and its corollary (`theorem_8_1`, `theorem_8_1_cor`), Exercise 8.1 (`ex_8_1`),
Theorem 8.2 (`theorem_8_2`), Exercise 8.2 (`ex_8_2`), Theorem 8.3 and its corollary
(`theorem_8_3`, `theorem_8_3_cor`), the pairing `⟨f, λ⟩` and Exercise 8.3 (`ex_8_3`), the
`n`-step transition functions and Exercise 8.4 (`kpow`, `ex_8_4a`, `ex_8_4b`), the sequence
`λₙ = T*ⁿλ₀` (`adjointOp_iterate`), and the Feller and monotonicity properties (`IsFeller`,
`IsMonotoneTF`). Theorems 8.1 and 8.3 follow the book's proofs: indicators, then simple
functions, then increasing limits.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

/-- A **transition function** (SLP p. 212): each `Q(z, ·)` is a probability measure and each
`Q(·, A)` is measurable. -/
def IsTransitionFunction (Q : Z → Set Z → ℝ≥0∞) : Prop :=
  (∀ z, ∃ μ : Measure Z, IsProbabilityMeasure μ ∧ ∀ A, MeasurableSet A → μ A = Q z A) ∧
    ∀ A, MeasurableSet A → Measurable fun z => Q z A

/-- Transition functions are Mathlib's Markov kernels. -/
theorem isTransitionFunction_iff (Q : Z → Set Z → ℝ≥0∞) :
    IsTransitionFunction Q ↔
      ∃ κ : Kernel Z Z, IsMarkovKernel κ ∧ ∀ z A, MeasurableSet A → κ z A = Q z A := by
  constructor
  · rintro ⟨h1, h2⟩
    choose μ hμ hμQ using h1
    have hm : Measurable μ := Measure.measurable_of_measurable_coe _ fun A hA => by
      have : (fun z => μ z A) = fun z => Q z A := funext fun z => hμQ z A hA
      rw [this]
      exact h2 A hA
    exact ⟨⟨μ, hm⟩, ⟨fun z => hμ z⟩, fun z A hA => hμQ z A hA⟩
  · rintro ⟨κ, hκ, hQ⟩
    refine ⟨fun z => ⟨κ z, inferInstance, fun A hA => hQ z A hA⟩, fun A hA => ?_⟩
    have : (fun z => Q z A) = fun z => κ z A := funext fun z => (hQ z A hA).symm
    rw [this]
    exact κ.measurable_coe hA

variable (κ : Kernel Z Z)

/-- The **Markov operator** on nonnegative functions (SLP (1), p. 213):
`(Tf)(z) = ∫ f(z′) Q(z, dz′)`. -/
noncomputable def markovOp (f : Z → ℝ≥0∞) (z : Z) : ℝ≥0∞ := ∫⁻ z', f z' ∂κ z

/-- The Markov operator on real functions. -/
noncomputable def markovOpR (f : Z → ℝ) (z : Z) : ℝ := ∫ z', f z' ∂κ z

/-- The **adjoint** `T*` (SLP (2), p. 213): `(T*λ)(A) = ∫ Q(z, A) λ(dz)`. -/
noncomputable def adjointOp (lam : Measure Z) : Measure Z := lam.bind κ

theorem markovOp_indicator {A : Set Z} (hA : MeasurableSet A) (c : ℝ≥0∞) (z : Z) :
    markovOp κ (A.indicator fun _ => c) z = c * κ z A := by
  rw [markovOp, lintegral_indicator_const hA]

/-- **Theorem 8.1.** `T` maps nonnegative measurable functions into nonnegative measurable
functions. The book's proof: `Tχ_A = Q(·, A)` is measurable; `T` is additive on simple
functions; and `T` commutes with increasing limits (Monotone Convergence Theorem). -/
theorem theorem_8_1 {f : Z → ℝ≥0∞} (hf : Measurable f) : Measurable (markovOp κ f) := by
  refine Measurable.ennreal_induction (motive := fun f => Measurable (markovOp κ f))
    ?_ ?_ ?_ hf
  · intro c s hs
    have : markovOp κ (s.indicator fun _ => c) = fun z => c * κ z s :=
      funext (markovOp_indicator κ hs c)
    rw [this]
    exact measurable_const.mul (κ.measurable_coe hs)
  · intro f g hfg hf hg ihf ihg
    have : markovOp κ (f + g) = fun z => markovOp κ f z + markovOp κ g z := funext fun z =>
      lintegral_add_left hf _
    rw [this]
    exact ihf.add ihg
  · intro f hf hmono ih
    have : markovOp κ (fun x => ⨆ n, f n x) = fun z => ⨆ n, markovOp κ (f n) z :=
      funext fun z => lintegral_iSup hf hmono
    rw [this]
    exact Measurable.iSup ih

variable [IsMarkovKernel κ]

theorem integrable_of_bounded {μ : Measure Z} [IsFiniteMeasure μ] {f : Z → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ z, |f z| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hM z)

/-- **Corollary to Theorem 8.1.** `T` maps bounded measurable functions into bounded measurable
functions: `Tf = Tf⁺ − Tf⁻`, and `|Tf| ≤ sup |f|`. -/
theorem theorem_8_1_cor {f : Z → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    Measurable (markovOpR κ f) ∧ ∀ z, |markovOpR κ f z| ≤ M := by
  constructor
  · have heq : markovOpR κ f = fun z =>
        (markovOp κ (fun z' => ENNReal.ofReal (f z')) z).toReal -
          (markovOp κ (fun z' => ENNReal.ofReal (-f z')) z).toReal := funext fun z =>
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hf hM)
    rw [heq]
    exact (theorem_8_1 κ hf.ennreal_ofReal).ennreal_toReal.sub
      (theorem_8_1 κ hf.neg.ennreal_ofReal).ennreal_toReal
  · intro z
    have := norm_integral_le_of_norm_le_const (μ := κ z) (C := M) (f := f)
      (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hM z')
    simpa [markovOpR, Real.norm_eq_abs, measureReal_def] using this

/-- **Exercise 8.1.** `T(αf + βg) = αTf + βTg` on bounded measurable functions. -/
theorem ex_8_1 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (α β : ℝ) :
    markovOpR κ (fun z => α * f z + β * g z) =
      fun z => α * markovOpR κ f z + β * markovOpR κ g z := by
  funext z
  simp only [markovOpR]
  rw [integral_add ((integrable_of_bounded hf hfM).const_mul α)
    ((integrable_of_bounded hg hgM).const_mul β), integral_const_mul, integral_const_mul]

omit [IsMarkovKernel κ] in
/-- `(T*λ)(A) = ∫ Q(z, A) λ(dz)` (SLP (2)). -/
theorem adjointOp_apply (lam : Measure Z) {A : Set Z} (hA : MeasurableSet A) :
    adjointOp κ lam A = ∫⁻ z, κ z A ∂lam :=
  Measure.bind_apply hA κ.aemeasurable

/-- **Theorem 8.2.** `T*` maps probability measures to probability measures: `T*λ(∅) = 0`,
`T*λ(Z) = 1`, and countable additivity follows from that of each `Q(z, ·)` by the Monotone
Convergence Theorem. -/
theorem theorem_8_2 (lam : Measure Z) [IsProbabilityMeasure lam] :
    IsProbabilityMeasure (adjointOp κ lam) ∧
      ∀ A : ℕ → Set Z, (∀ n, MeasurableSet (A n)) → Pairwise (Function.onFun Disjoint A) →
        ∫⁻ z, κ z (⋃ n, A n) ∂lam = ∑' n, ∫⁻ z, κ z (A n) ∂lam := by
  refine ⟨⟨?_⟩, fun A hA hd => ?_⟩
  · rw [adjointOp_apply κ lam MeasurableSet.univ]
    simp
  · simp_rw [measure_iUnion hd hA]
    exact lintegral_tsum fun n => (κ.measurable_coe (hA n)).aemeasurable

omit [IsMarkovKernel κ] in
/-- **Exercise 8.2.** `T*` is affine: `T*[αλ + (1 − α)μ] = αT*λ + (1 − α)T*μ`. -/
theorem ex_8_2 (lam μ : Measure Z) (α : ℝ≥0∞) :
    adjointOp κ (α • lam + (1 - α) • μ) = α • adjointOp κ lam + (1 - α) • adjointOp κ μ := by
  ext A hA
  simp only [adjointOp_apply κ _ hA, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  rfl

omit [IsMarkovKernel κ] in
/-- **Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for nonnegative measurable `f`. The book's proof:
indicators, simple functions, then the Monotone Convergence Theorem on both sides. -/
theorem theorem_8_3 (lam : Measure Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam := by
  refine Measurable.ennreal_induction (motive := fun f =>
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam) ?_ ?_ ?_ hf
  · intro c s hs
    simp_rw [markovOp_indicator κ hs]
    rw [lintegral_indicator hs, setLIntegral_const, adjointOp_apply κ lam hs,
      lintegral_const_mul _ (κ.measurable_coe hs), mul_comm]
  · intro f g hfg hf hg ihf ihg
    have : ∀ z, markovOp κ (f + g) z = markovOp κ f z + markovOp κ g z := fun z =>
      lintegral_add_left hf _
    simp_rw [this]
    rw [lintegral_add_left (theorem_8_1 κ hf), ihf, ihg, Pi.add_def,
      lintegral_add_left hf]
  · intro f hf hmono ih
    have : ∀ z, markovOp κ (fun x => ⨆ n, f n x) z = ⨆ n, markovOp κ (f n) z := fun z =>
      lintegral_iSup hf hmono
    simp_rw [this]
    rw [lintegral_iSup (fun n => theorem_8_1 κ (hf n))
      (fun m n hmn z => lintegral_mono (hmono hmn)), lintegral_iSup hf hmono]
    simp_rw [ih]

/-- **Corollary to Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for bounded measurable `f`. -/
theorem theorem_8_3_cor (lam : Measure Z) [IsProbabilityMeasure lam] {f : Z → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    ∫ z, markovOpR κ f z ∂lam = ∫ z', f z' ∂adjointOp κ lam := by
  have : IsProbabilityMeasure (adjointOp κ lam) := (theorem_8_2 κ lam).1
  have hTf := theorem_8_1_cor κ hf hM
  have hpos : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOpR κ g z = (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal -
        (markovOp κ (fun z' => ENNReal.ofReal (-g z')) z).toReal := fun g hg hgM z =>
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hg hgM)
  have hfin : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOp κ (fun z' => ENNReal.ofReal (g z')) z ≠ ∞ := fun g hg hgM z =>
    ((integrable_of_bounded hg hgM (μ := κ z)).lintegral_lt_top).ne
  have hbd : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) →
      Integrable (fun z => (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal) lam :=
    fun g hg hgM => integrable_of_bounded (theorem_8_1 κ hg.ennreal_ofReal).ennreal_toReal
      (M := |M|) fun z => by
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        refine ENNReal.toReal_le_of_le_ofReal (abs_nonneg M) ?_
        calc markovOp κ (fun z' => ENNReal.ofReal (g z')) z
            ≤ ∫⁻ _, ENNReal.ofReal |M| ∂κ z :=
              lintegral_mono fun z' => ENNReal.ofReal_le_ofReal
                ((le_abs_self _).trans ((hgM z').trans (le_abs_self M)))
          _ = ENNReal.ofReal |M| := by simp
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hf hM),
    integral_congr_ae (Eventually.of_forall (hpos f hf hM))]
  rw [integral_sub, integral_toReal (theorem_8_1 κ hf.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin f hf hM z).lt_top),
    integral_toReal (f := fun z => markovOp κ (fun z' => ENNReal.ofReal (-f z')) z)
      (theorem_8_1 κ hf.neg.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin (fun z => -f z) hf.neg (fun z => by
      rw [abs_neg]; exact hM z) z).lt_top),
    theorem_8_3 κ lam hf.ennreal_ofReal,
    theorem_8_3 κ lam (f := fun z => ENNReal.ofReal (-f z)) hf.neg.ennreal_ofReal]
  · exact hbd f hf hM
  · exact hbd (fun z => -f z) hf.neg fun z => by rw [abs_neg]; exact hM z

/-- The pairing `⟨f, λ⟩ = ∫ f dλ` (SLP p. 218). -/
noncomputable def pairing (f : Z → ℝ) (lam : Measure Z) : ℝ := ∫ z, f z ∂lam

omit [IsMarkovKernel κ] in
/-- **Exercise 8.3.** The pairing is linear in `f` and affine in `λ`. -/
theorem ex_8_3 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (a b : ℝ) (lam μ : Measure Z)
    [IsProbabilityMeasure lam] [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    pairing (fun z => a * f z + b * g z) lam = a * pairing f lam + b * pairing g lam ∧
      pairing f (ENNReal.ofReal α • lam + ENNReal.ofReal (1 - α) • μ) =
        α * pairing f lam + (1 - α) * pairing f μ := by
  constructor
  · simp only [pairing]
    rw [integral_add ((integrable_of_bounded hf hfM).const_mul a)
      ((integrable_of_bounded hg hgM).const_mul b), integral_const_mul, integral_const_mul]
  · simp only [pairing]
    rw [integral_add_measure ((integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hα0,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- The `n`-step transition function (SLP p. 219): `Q⁰ = id`,
`Qⁿ⁺¹(z, A) = ∫ Qⁿ(z′, A) Q(z, dz′)`. -/
noncomputable def kpow (κ : Kernel Z Z) : ℕ → Kernel Z Z
  | 0 => Kernel.id
  | n + 1 => kpow κ n ∘ₖ κ

omit [IsMarkovKernel κ] in
theorem kpow_one : kpow κ 1 = κ := by simp [kpow]

/-- **Exercise 8.4a.** The functions `Qⁿ` are transition functions. -/
theorem ex_8_4a (n : ℕ) : IsMarkovKernel (kpow κ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih => exact inferInstanceAs (IsMarkovKernel (kpow κ n ∘ₖ κ))

omit [IsMarkovKernel κ] in
theorem kpow_add (n m : ℕ) : kpow κ (n + m) = kpow κ m ∘ₖ kpow κ n := by
  induction n with
  | zero => simp [kpow]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega, kpow, ih, kpow, Kernel.comp_assoc]

omit [IsMarkovKernel κ] in
theorem markovOp_comp (η : Kernel Z Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    markovOp (η ∘ₖ κ) f = markovOp κ (markovOp η f) := by
  funext z
  exact Kernel.lintegral_comp η κ z hf

omit [IsMarkovKernel κ] in
theorem adjointOp_comp (η : Kernel Z Z) (lam : Measure Z) :
    adjointOp (η ∘ₖ κ) lam = adjointOp η (adjointOp κ lam) := by
  simp only [adjointOp]
  rw [Measure.bind_bind κ.aemeasurable η.aemeasurable]
  rfl

omit [IsMarkovKernel κ] in
/-- **Exercise 8.4b.** `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` and `T*⁽ⁿ⁺ᵐ⁾λ = T*ⁿ(T*ᵐλ)`. -/
theorem ex_8_4b (n m : ℕ) {f : Z → ℝ≥0∞} (hf : Measurable f) (lam : Measure Z) :
    markovOp (kpow κ (n + m)) f = markovOp (kpow κ n) (markovOp (kpow κ m) f) ∧
      adjointOp (kpow κ (n + m)) lam = adjointOp (kpow κ n) (adjointOp (kpow κ m) lam) := by
  constructor
  · rw [kpow_add, markovOp_comp _ _ hf]
  · rw [add_comm, kpow_add, adjointOp_comp]

omit [IsMarkovKernel κ] in
/-- `λₙ = T*λₙ₋₁ = T*ⁿlam₀` (SLP p. 219). -/
theorem adjointOp_iterate (n : ℕ) (lam₀ : Measure Z) :
    (adjointOp κ)^[n] lam₀ = adjointOp (kpow κ n) lam₀ := by
  induction n generalizing lam₀ with
  | zero =>
    change lam₀ = lam₀.bind Kernel.id
    have : (⇑(Kernel.id : Kernel Z Z)) = fun z => Measure.dirac z := funext Kernel.id_apply
    rw [this, Measure.bind_dirac]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, kpow, adjointOp_comp]

/-- `Q` has the **Feller property** (SLP p. 220): `T` maps bounded continuous functions to
continuous functions. -/
def IsFeller [TopologicalSpace Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) → Continuous (markovOpR κ f)

/-- `Q` is **monotone** (SLP p. 220): `T` maps bounded nondecreasing measurable functions to
nondecreasing functions. -/
def IsMonotoneTF [Preorder Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Measurable f → (∃ M, ∀ z, |f z| ≤ M) → Monotone f → Monotone (markovOpR κ f)

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stochastic kernels and iterated integrals

SLP §8.3, pp. 225–234. A stochastic kernel on `{X, 𝒴}` (`IsStochasticKernel`) is a Markov
kernel from `X` to `Y` (`isStochasticKernel_iff`). Theorem 8.4 and its corollary
(`theorem_8_4`, `theorem_8_4_cor`); the direct product `P₁ × P₂` of Theorem 8.5 (`directProd`,
`theorem_8_5`, `theorem_8_5_unique`); the iterated integral formula (4) of Theorem 8.6 and its
corollary (`theorem_8_6`, `theorem_8_6_cor`) and Theorem 8.7 for integrable functions
(`theorem_8_7`); and Exercise 8.9 (`ex_8_9a`, `ex_8_9b`).

The book proves Theorems 8.4–8.6 with the Monotone Class Lemma, starting from measurable
rectangles; the same argument, in π-λ form, is Mathlib's for its kernel composition.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {W X Y : Type*} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]

/-- A **stochastic kernel** on `{X, 𝒴}` (SLP p. 226): each `P(x, ·)` is a probability measure on
`Y` and each `P(·, B)` is measurable. -/
def IsStochasticKernel (P : X → Set Y → ℝ≥0∞) : Prop :=
  (∀ x, ∃ μ : Measure Y, IsProbabilityMeasure μ ∧ ∀ B, MeasurableSet B → μ B = P x B) ∧
    ∀ B, MeasurableSet B → Measurable fun x => P x B

/-- Stochastic kernels are Mathlib's Markov kernels. -/
theorem isStochasticKernel_iff (P : X → Set Y → ℝ≥0∞) :
    IsStochasticKernel P ↔
      ∃ κ : Kernel X Y, IsMarkovKernel κ ∧ ∀ x B, MeasurableSet B → κ x B = P x B := by
  constructor
  · rintro ⟨h1, h2⟩
    choose μ hμ hμP using h1
    have hm : Measurable μ := Measure.measurable_of_measurable_coe _ fun B hB => by
      have : (fun x => μ x B) = fun x => P x B := funext fun x => hμP x B hB
      rw [this]
      exact h2 B hB
    exact ⟨⟨μ, hm⟩, ⟨fun x => hμ x⟩, fun x B hB => hμP x B hB⟩
  · rintro ⟨κ, hκ, hP⟩
    refine ⟨fun x => ⟨κ x, inferInstance, fun B hB => hP x B hB⟩, fun B hB => ?_⟩
    have : (fun x => P x B) = fun x => κ x B := funext fun x => (hP x B hB).symm
    rw [this]
    exact κ.measurable_coe hB

/-- **Theorem 8.4.** For `F ≥ 0` measurable on `X × Y`, `(TF)(x) = ∫ F(x, y) P(x, dy)` is
measurable. -/
theorem theorem_8_4 (P : Kernel X Y) [IsSFiniteKernel P] {F : X × Y → ℝ≥0∞}
    (hF : Measurable F) : Measurable fun x => ∫⁻ y, F (x, y) ∂P x :=
  hF.lintegral_kernel_prod_right'

/-- **Corollary to Theorem 8.4.** For bounded measurable `F`, `TF` is bounded and measurable. -/
theorem theorem_8_4_cor (P : Kernel X Y) [IsMarkovKernel P] {F : X × Y → ℝ}
    (hF : Measurable F) {M : ℝ} (hM : ∀ p, |F p| ≤ M) :
    Measurable (fun x => ∫ y, F (x, y) ∂P x) ∧ ∀ x, |∫ y, F (x, y) ∂P x| ≤ M := by
  refine ⟨(hF.stronglyMeasurable.integral_kernel_prod_right' (κ := P)).measurable, fun x => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := P x) (C := M) (f := fun y => F (x, y))
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM (x, y))
  simpa [Real.norm_eq_abs, measureReal_def] using this

/-- The **direct product** `P₃ = P₁ × P₂` (SLP p. 229): `P₃(w, ·)` is the law of `(x, y)` when
`x ~ P₁(w, ·)` and then `y ~ P₂(x, ·)`. -/
noncomputable def directProd (P₁ : Kernel W X) (P₂ : Kernel X Y) : Kernel W (X × Y) :=
  P₁ ⊗ₖ Kernel.prodMkLeft W P₂

theorem isMarkovKernel_directProd (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁]
    [IsMarkovKernel P₂] : IsMarkovKernel (directProd P₁ P₂) := by
  unfold directProd
  infer_instance

/-- **Theorem 8.5.** `P₃(w, A × B) = ∫_A P₂(x, B) P₁(w, dx)`, and `P₃` is a stochastic kernel on
`{W, 𝒳 × 𝒴}`. -/
theorem theorem_8_5 (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (w : W) {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    directProd P₁ P₂ w (A ×ˢ B) = ∫⁻ x in A, P₂ x B ∂P₁ w ∧
      IsMarkovKernel (directProd P₁ P₂) := by
  refine ⟨?_, isMarkovKernel_directProd P₁ P₂⟩
  rw [directProd, Kernel.compProd_apply_prod hA hB]
  rfl

/-- **Theorem 8.5, uniqueness.** A probability measure on `X × Y` with the values (3) on
measurable rectangles is `P₃(w, ·)`. -/
theorem theorem_8_5_unique (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁]
    [IsMarkovKernel P₂] (w : W) {ν : Measure (X × Y)} [IsProbabilityMeasure ν]
    (hν : ∀ A B, MeasurableSet A → MeasurableSet B → ν (A ×ˢ B) = ∫⁻ x in A, P₂ x B ∂P₁ w) :
    ν = directProd P₁ P₂ w := by
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    rw [hν A B hA hB, (theorem_8_5 P₁ P₂ w hA hB).1]
  · have := isMarkovKernel_directProd P₁ P₂
    simp

/-- **Theorem 8.6.** For `F ≥ 0` measurable on `X × Y`,
`∫ F dP₃(w, ·) = ∫_X [∫_Y F(x, y) P₂(x, dy)] P₁(w, dx)`. -/
theorem theorem_8_6 (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (w : W) {F : X × Y → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂directProd P₁ P₂ w = ∫⁻ x, ∫⁻ y, F (x, y) ∂P₂ x ∂P₁ w :=
  Kernel.lintegral_compProd _ _ w hF

/-- **Theorem 8.7.** (4) holds for every `F` integrable for `P₃(ŵ, ·)`. -/
theorem theorem_8_7 (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (w : W) {F : X × Y → ℝ} (hF : Integrable F (directProd P₁ P₂ w)) :
    ∫ p, F p ∂directProd P₁ P₂ w = ∫ x, ∫ y, F (x, y) ∂P₂ x ∂P₁ w :=
  integral_compProd hF

/-- **Corollary to Theorem 8.6.** (4) holds for bounded measurable `F`. -/
theorem theorem_8_6_cor (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁]
    [IsMarkovKernel P₂] (w : W) {F : X × Y → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ p, |F p| ≤ M) :
    ∫ p, F p ∂directProd P₁ P₂ w = ∫ x, ∫ y, F (x, y) ∂P₂ x ∂P₁ w := by
  have := isMarkovKernel_directProd P₁ P₂
  exact theorem_8_7 P₁ P₂ w (integrable_of_bounded hF hM)

/-- **Exercise 8.9a (Product Measure Theorem).** For probability spaces `(X, μ)` and `(Y, ν)`
there is a unique probability measure `λ` on `X × Y` with `λ(A × B) = μ(A)ν(B)`. -/
theorem ex_8_9a (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (IsProbabilityMeasure (μ.prod ν) ∧
      ∀ A B, MeasurableSet A → MeasurableSet B → μ.prod ν (A ×ˢ B) = μ A * ν B) ∧
      ∀ lam : Measure (X × Y), (∀ A B, MeasurableSet A → MeasurableSet B →
        lam (A ×ˢ B) = μ A * ν B) → lam = μ.prod ν :=
  ⟨⟨inferInstance, fun A B _ _ => Measure.prod_prod A B⟩,
    fun _ h => (Measure.prod_eq h).symm⟩

/-- **Exercise 8.9b (Tonelli and Fubini).** The two iterated integrals of a nonnegative
measurable, or a `λ`-integrable, function equal its integral. -/
theorem ex_8_9b (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (∀ F : X × Y → ℝ≥0∞, Measurable F →
      ∫⁻ p, F p ∂μ.prod ν = ∫⁻ x, ∫⁻ y, F (x, y) ∂ν ∂μ ∧
        ∫⁻ p, F p ∂μ.prod ν = ∫⁻ y, ∫⁻ x, F (x, y) ∂μ ∂ν) ∧
      ∀ F : X × Y → ℝ, Integrable F (μ.prod ν) →
        ∫ p, F p ∂μ.prod ν = ∫ x, ∫ y, F (x, y) ∂ν ∂μ ∧
          ∫ p, F p ∂μ.prod ν = ∫ y, ∫ x, F (x, y) ∂μ ∂ν :=
  ⟨fun F hF => ⟨lintegral_prod F hF.aemeasurable, lintegral_prod_symm F hF.aemeasurable⟩,
    fun F hF => ⟨integral_prod F hF, integral_prod_symm F hF⟩⟩

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Measures on spaces of finite histories

SLP §8.2–8.3, pp. 220–234. For a transition function `Q` and an initial state `z₀`, the
probability measure `μᵗ(z₀, ·)` on histories `zᵗ = (z₁, …, z_t) ∈ Zᵗ` (`hist Q t`), built as the
book does: first `z₁ ~ Q(z₀, ·)`, then the history from `z₁` (`hist_succ_lintegral`).

* Theorem 8.8: `∫ F dμᵗ(z₀, ·)` is the iterated integral
  `∫ Q(z₀, dz₁) ∫ Q(z₁, dz₂) ⋯ ∫ Q(z_{t−1}, dz_t) F(z₁, …, z_t)` (`iterLInt`, `theorem_8_8`, and
  `iterInt`, `theorem_8_8_integrable` for integrable `F`).
* Exercise 8.5: on rectangles `μᵗ` is given by that formula, it is countably additive and
  `μᵗ(z₀, Zᵗ) = 1` (`ex_8_5`).
* Exercise 8.8: `μᵗ(·, ·)` is a stochastic kernel (`ex_8_8a`); `Q × μᵗ⁻¹ = μᵗ = μᵗ⁻¹ × Q`, i.e. the
  history splits at its first or at its last date (`hist_succ_eq_cons`, `ex_8_8b`); and the
  integral splits accordingly, (1a) and (1b) (`ex_8_8c_last`, `ex_8_8c_first`).

`lastState z₀ zᵗ` is the most recent state: `z₀` if `t = 0`, otherwise `z_t`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

theorem measurable_cons (t : ℕ) :
    Measurable fun p : Z × (Fin t → Z) => (Fin.cons p.1 p.2 : Fin (t + 1) → Z) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_snoc (t : ℕ) :
    Measurable fun p : (Fin t → Z) × Z => (Fin.snoc p.1 p.2 : Fin (t + 1) → Z) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

/-- The most recent state of a history started at `z₀`: `z₀` for the empty history, otherwise
the last entry. -/
def lastState (z₀ : Z) : {t : ℕ} → (Fin t → Z) → Z
  | 0, _ => z₀
  | t + 1, h => h (Fin.last t)

theorem measurable_lastState (z₀ : Z) (t : ℕ) : Measurable (lastState z₀ (t := t)) := by
  cases t with
  | zero => exact measurable_const
  | succ t => exact measurable_pi_apply _

omit [MeasurableSpace Z] in
theorem lastState_cons (z₀ z₁ : Z) {t : ℕ} (h : Fin t → Z) :
    lastState z₀ (Fin.cons z₁ h : Fin (t + 1) → Z) = lastState z₁ h := by
  cases t with
  | zero => rfl
  | succ t =>
    simp only [lastState]
    rw [← Fin.succ_last, Fin.cons_succ]

omit [MeasurableSpace Z] in
theorem lastState_snoc (z₀ z : Z) {t : ℕ} (h : Fin t → Z) :
    lastState z₀ (Fin.snoc h z : Fin (t + 1) → Z) = z := by
  simp [lastState]

variable (Q : Kernel Z Z) [IsMarkovKernel Q]

/-- `μᵗ(z₀, ·)`: the distribution of the history `(z₁, …, z_t)` (SLP p. 221). -/
noncomputable def hist (Q : Kernel Z Z) : (t : ℕ) → Kernel Z (Fin t → Z)
  | 0 => Kernel.const Z (Measure.dirac Fin.elim0)
  | t + 1 => ((Kernel.id ×ₖ hist Q t).map fun p => (Fin.cons p.1 p.2 : Fin (t + 1) → Z)) ∘ₖ Q

/-- **Exercise 8.8a.** `μᵗ` is a stochastic kernel on `{Z, 𝒵ᵗ}`. -/
theorem ex_8_8a (t : ℕ) : IsMarkovKernel (hist Q t) := by
  induction t with
  | zero => exact inferInstanceAs (IsMarkovKernel (Kernel.const Z _))
  | succ t ih =>
    have : IsMarkovKernel ((Kernel.id ×ₖ hist Q t).map fun p =>
        (Fin.cons p.1 p.2 : Fin (t + 1) → Z)) :=
      Kernel.IsMarkovKernel.map _ (measurable_cons t)
    exact inferInstanceAs (IsMarkovKernel (_ ∘ₖ Q))

omit [IsMarkovKernel Q] in
theorem hist_zero_lintegral (z₀ : Z) (f : (Fin 0 → Z) → ℝ≥0∞) :
    ∫⁻ h, f h ∂hist Q 0 z₀ = f Fin.elim0 := by
  simp [hist, lintegral_dirac]

/-- **The first-date decomposition** (SLP p. 221, and the identity `μᵗ = Q × μᵗ⁻¹` of
Exercise 8.8b): `∫ f dμᵗ⁺¹(z₀, ·) = ∫ [∫ f(z₁, zᵗ) μᵗ(z₁, dzᵗ)] Q(z₀, dz₁)`. -/
theorem hist_succ_lintegral (t : ℕ) (z₀ : Z) {f : (Fin (t + 1) → Z) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ h, f h ∂hist Q (t + 1) z₀ = ∫⁻ z₁, ∫⁻ h, f (Fin.cons z₁ h) ∂hist Q t z₁ ∂Q z₀ := by
  have := ex_8_8a Q t
  rw [hist, Kernel.lintegral_comp _ _ _ hf]
  refine lintegral_congr fun z₁ => ?_
  rw [Kernel.lintegral_map _ (measurable_cons t) _ hf, Kernel.lintegral_prod _ _ _
    (g := fun p : Z × (Fin t → Z) => f (Fin.cons p.1 p.2)) (hf.comp (measurable_cons t)),
    Kernel.id_apply, lintegral_dirac']
  exact (hf.comp (measurable_cons t)).lintegral_prod_right'

/-- The iterated integral `∫ Q(z₀, dz₁) ∫ Q(z₁, dz₂) ⋯ ∫ Q(z_{t−1}, dz_t) F(z₁, …, z_t)`. -/
noncomputable def iterLInt : (t : ℕ) → ((Fin t → Z) → ℝ≥0∞) → Z → ℝ≥0∞
  | 0, F, _ => F Fin.elim0
  | t + 1, F, z₀ => ∫⁻ z₁, iterLInt t (fun h => F (Fin.cons z₁ h)) z₁ ∂Q z₀

/-- **Theorem 8.8** (nonnegative functions). -/
theorem theorem_8_8 (t : ℕ) (z₀ : Z) {F : (Fin t → Z) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F h ∂hist Q t z₀ = iterLInt Q t F z₀ := by
  induction t generalizing z₀ with
  | zero => exact hist_zero_lintegral Q z₀ F
  | succ t ih =>
    rw [hist_succ_lintegral Q t z₀ hF, iterLInt]
    refine lintegral_congr fun z₁ => ?_
    exact ih z₁ (hF.comp ((measurable_cons t).comp (measurable_const.prodMk measurable_id)))

/-- **Exercise 8.5.** On a measurable rectangle `A₁ × ⋯ × A_t`, `μᵗ(z₀, ·)` is the iterated
integral of its indicator; `μᵗ(z₀, ·)` is countably additive on rectangles; and
`μᵗ(z₀, Zᵗ) = 1`. -/
theorem ex_8_5 (t : ℕ) (z₀ : Z) {A : Fin t → Set Z} (hA : ∀ i, MeasurableSet (A i)) :
    hist Q t z₀ (Set.pi univ A) = iterLInt Q t ((Set.pi univ A).indicator 1) z₀ ∧
      (∀ C : ℕ → Set (Fin t → Z), (∀ n, MeasurableSet (C n)) →
        Pairwise (Function.onFun Disjoint C) →
          hist Q t z₀ (⋃ n, C n) = ∑' n, hist Q t z₀ (C n)) ∧
      hist Q t z₀ univ = 1 := by
  have := ex_8_8a Q t
  have hpi : MeasurableSet (Set.pi univ A) := MeasurableSet.univ_pi hA
  refine ⟨?_, fun C hC hd => measure_iUnion hd hC, measure_univ⟩
  rw [← theorem_8_8 Q t z₀ (measurable_one.indicator hpi), lintegral_indicator_one hpi]

/-- The kernel `zᵗ ↦ Q(z_t, ·)` of the next state given a history started at `z₀`. -/
noncomputable def nextKernel (z₀ : Z) (t : ℕ) : Kernel (Fin t → Z) Z :=
  Q.comap (lastState z₀) (measurable_lastState z₀ t)

theorem isMarkovKernel_nextKernel (z₀ : Z) (t : ℕ) : IsMarkovKernel (nextKernel Q z₀ t) := by
  unfold nextKernel
  infer_instance

omit [IsMarkovKernel Q] in
theorem nextKernel_apply (z₀ : Z) (t : ℕ) (h : Fin t → Z) :
    nextKernel Q z₀ t h = Q (lastState z₀ h) := rfl

/-- **The last-date decomposition** (the identity `μᵗ = μᵗ⁻¹ × Q` of Exercise 8.8b):
`∫ f dμᵗ⁺¹(z₀, ·) = ∫ [∫ f(zᵗ, z′) Q(z_t, dz′)] μᵗ(z₀, dzᵗ)`. -/
theorem hist_succ_lintegral_last (t : ℕ) (z₀ : Z) {f : (Fin (t + 1) → Z) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ h, f h ∂hist Q (t + 1) z₀ =
      ∫⁻ h, ∫⁻ z', f (Fin.snoc h z') ∂Q (lastState z₀ h) ∂hist Q t z₀ := by
  induction t generalizing z₀ with
  | zero =>
    rw [hist_succ_lintegral Q 0 z₀ hf, hist_zero_lintegral]
    refine lintegral_congr fun z₁ => ?_
    rw [hist_zero_lintegral]
    congr 1
    funext i
    fin_cases i
    rfl
  | succ t ih =>
    have hfc : ∀ z₁ : Z, Measurable fun h : Fin (t + 1) → Z => f (Fin.cons z₁ h) := fun z₁ =>
      hf.comp ((measurable_cons (t + 1)).comp (measurable_const.prodMk measurable_id))
    have := isMarkovKernel_nextKernel Q z₀ (t + 1)
    have hg : Measurable fun h : Fin (t + 1) → Z =>
        ∫⁻ z', f (Fin.snoc h z') ∂Q (lastState z₀ h) := by
      have := (hf.comp (measurable_snoc (t + 1))).lintegral_kernel_prod_right'
        (κ := nextKernel Q z₀ (t + 1))
      exact this
    rw [hist_succ_lintegral Q (t + 1) z₀ hf, hist_succ_lintegral Q t z₀ hg]
    refine lintegral_congr fun z₁ => ?_
    rw [ih z₁ (hfc z₁)]
    refine lintegral_congr fun h' => ?_
    rw [lastState_cons]
    refine lintegral_congr fun z' => ?_
    rw [Fin.cons_snoc_eq_snoc_cons]

/-- **Exercise 8.8b** as an identity of measures: `μᵗ⁺¹(z₀, ·)` is the image under
`(zᵗ, z′) ↦ (zᵗ, z′)` of `μᵗ(z₀, ·) ⊗ Q(z_t, ·)`. -/
theorem ex_8_8b (t : ℕ) (z₀ : Z) :
    hist Q (t + 1) z₀ =
      ((hist Q t z₀) ⊗ₘ nextKernel Q z₀ t).map fun p => (Fin.snoc p.1 p.2 : Fin (t + 1) → Z) := by
  have := ex_8_8a Q t
  have := isMarkovKernel_nextKernel Q z₀ t
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [hist_succ_lintegral_last Q t z₀ hf, lintegral_map hf (measurable_snoc t),
    Measure.lintegral_compProd (f := fun p : (Fin t → Z) × Z => f (Fin.snoc p.1 p.2))
      (hf.comp (measurable_snoc t))]
  rfl

/-- The first-date decomposition as an identity of measures: `μᵗ⁺¹(z₀, ·)` is the image under
`(z₁, zᵗ) ↦ (z₁, zᵗ)` of `Q(z₀, ·) ⊗ μᵗ(z₁, ·)`. -/
theorem hist_succ_eq_cons (t : ℕ) (z₀ : Z) :
    hist Q (t + 1) z₀ =
      ((Q z₀) ⊗ₘ hist Q t).map fun p => (Fin.cons p.1 p.2 : Fin (t + 1) → Z) := by
  have := ex_8_8a Q t
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [hist_succ_lintegral Q t z₀ hf, lintegral_map hf (measurable_cons t),
    Measure.lintegral_compProd (f := fun p : Z × (Fin t → Z) => f (Fin.cons p.1 p.2))
      (hf.comp (measurable_cons t))]

/-- **Exercise 8.8c, (1a).** For `μᵗ⁺¹(z₀, ·)`-integrable `F`,
`∫ F dμᵗ⁺¹ = ∫ [∫ F(zᵗ, z′) Q(z_t, dz′)] μᵗ(z₀, dzᵗ)`. -/
theorem ex_8_8c_last (t : ℕ) (z₀ : Z) {F : (Fin (t + 1) → Z) → ℝ}
    (hF : Integrable F (hist Q (t + 1) z₀)) :
    ∫ h, F h ∂hist Q (t + 1) z₀ =
      ∫ h, ∫ z', F (Fin.snoc h z') ∂Q (lastState z₀ h) ∂hist Q t z₀ := by
  have := ex_8_8a Q t
  have := isMarkovKernel_nextKernel Q z₀ t
  rw [ex_8_8b Q t z₀] at hF ⊢
  have hF' := (integrable_map_measure hF.1 (measurable_snoc t).aemeasurable).1 hF
  rw [integral_map (measurable_snoc t).aemeasurable hF.1,
    Measure.integral_compProd (f := fun p : (Fin t → Z) × Z => F (Fin.snoc p.1 p.2)) hF']
  rfl

/-- **Exercise 8.8c, (1b).** For `μᵗ⁺¹(z₀, ·)`-integrable `F`,
`∫ F dμᵗ⁺¹ = ∫ [∫ F(z₁, zᵗ) μᵗ(z₁, dzᵗ)] Q(z₀, dz₁)`. -/
theorem ex_8_8c_first (t : ℕ) (z₀ : Z) {F : (Fin (t + 1) → Z) → ℝ}
    (hF : Integrable F (hist Q (t + 1) z₀)) :
    ∫ h, F h ∂hist Q (t + 1) z₀ = ∫ z₁, ∫ h, F (Fin.cons z₁ h) ∂hist Q t z₁ ∂Q z₀ := by
  have := ex_8_8a Q t
  rw [hist_succ_eq_cons Q t z₀] at hF ⊢
  have hF' := (integrable_map_measure hF.1 (measurable_cons t).aemeasurable).1 hF
  rw [integral_map (measurable_cons t).aemeasurable hF.1,
    Measure.integral_compProd (f := fun p : Z × (Fin t → Z) => F (Fin.cons p.1 p.2)) hF']

/-- The iterated integral of a real function. -/
noncomputable def iterInt : (t : ℕ) → ((Fin t → Z) → ℝ) → Z → ℝ
  | 0, F, _ => F Fin.elim0
  | t + 1, F, z₀ => ∫ z₁, iterInt t (fun h => F (Fin.cons z₁ h)) z₁ ∂Q z₀

/-- **Theorem 8.8** (integrable functions). -/
theorem theorem_8_8_integrable (t : ℕ) (z₀ : Z) {F : (Fin t → Z) → ℝ}
    (hF : Integrable F (hist Q t z₀)) : ∫ h, F h ∂hist Q t z₀ = iterInt Q t F z₀ := by
  induction t generalizing z₀ with
  | zero => simp [hist, iterInt]
  | succ t ih =>
    have := ex_8_8a Q t
    rw [ex_8_8c_first Q t z₀ hF, iterInt]
    rw [hist_succ_eq_cons Q t z₀] at hF
    have hF' := (integrable_map_measure hF.1 (measurable_cons t).aemeasurable).1 hF
    have hae := (Measure.integrable_compProd_iff hF'.1).1 hF'
    refine integral_congr_ae (hae.1.mono fun z₁ hz₁ => ?_)
    exact ih z₁ hz₁

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Plans for stochastic dynamic programs

SLP §9.1, pp. 241–258. The problem is set up in the book's second, more general formulation
(p. 255): the decision-maker chooses an action `y ∈ Γ(x, z)` in a space `Y`, and the endogenous
state moves by `x′ = φ(x, y, z′)` (`Model`). The book's first formulation is the special case
`Y = X`, `φ(x, y, z′) = y` (`Model.first`), so each result is proved once.

* Plans `π_t : Zᵗ → Y` (`Plan`), the states `x_t^π` they induce (SLP (16): `xState`, `state`),
  feasibility (1a)–(1b) (`IsFeasible`), the period returns (`ret`), the partial sums `uₙ` and
  their limit `u` (`uN`, `planValue`), and the supremum function `v*` (SLP (2): `vStar`).
* The continuation `C(π, z₁)` of a plan after the first shock (SLP (8): `cont`, `start₁`), and the
  identities relating its states and returns to those of `π` (`state_cons`, `ret_cons`).
* Plans generated by a sequence of selections (`genPlan`), Lemma 9.1 and Exercise 9.3
  (`lemma_9_1`), and Markov (stationary) plans.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- The givens of a stochastic dynamic program (SLP pp. 241 and 255): a transition function `Q`
on the shocks, a feasibility correspondence `Γ : X × Z ⇉ Y`, a law of motion `φ`, a return
function `F(x, y, z)` and a discount factor `β`. -/
structure Model (X Y Z : Type*) [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] where
  Q : Kernel Z Z
  Γ : X × Z → Set Y
  φ : X × Y × Z → X
  F : X × Y × Z → ℝ
  β : ℝ

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The book's first formulation (SLP p. 241): the choice is next period's state,
`φ(x, y, z′) = y`. -/
abbrev Model.first (Q : Kernel Z Z) (Γ : X × Z → Set X) (F : X × X × Z → ℝ) (β : ℝ) :
    Model X X Z :=
  ⟨Q, Γ, fun p => p.2.1, F, β⟩

/-- A **plan** (SLP pp. 242, 255): for each date `t`, a function `π_t : Zᵗ → Y` of the history of
shocks. (`π₀` is a function on the one-point space `Z⁰`.) -/
abbrev Plan (Y Z : Type*) := (t : ℕ) → (Fin t → Z) → Y

variable (M : Model X Y Z)

/-- The endogenous state `x_t^π(zᵗ)` along a plan (SLP (16)). -/
def xState (s₀ : X × Z) (π : Plan Y Z) : (t : ℕ) → (Fin t → Z) → X
  | 0, _ => s₀.1
  | t + 1, h => M.φ (xState s₀ π t (Fin.init h), π t (Fin.init h), h (Fin.last t))

/-- The state `s_t = (x_t, z_t)` along a plan. -/
def state (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) (h : Fin t → Z) : X × Z :=
  (xState M s₀ π t h, lastState s₀.2 h)

theorem state_zero (s₀ : X × Z) (π : Plan Y Z) (h : Fin 0 → Z) : state M s₀ π 0 h = s₀ := rfl

/-- A plan is **feasible** from `s₀` (SLP (1a)–(1b), (1a′)–(1b′)): each `π_t` is measurable and
`π_t(zᵗ) ∈ Γ(x_t, z_t)`. -/
def IsFeasible (s₀ : X × Z) (π : Plan Y Z) : Prop :=
  (∀ t, Measurable (π t)) ∧ ∀ t h, π t h ∈ M.Γ (state M s₀ π t h)

/-- The return at date `t`: `F(x_t, π_t(zᵗ), z_t)`. -/
def ret (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) (h : Fin t → Z) : ℝ :=
  M.F ((state M s₀ π t h).1, π t h, (state M s₀ π t h).2)

/-- `uₙ(π, s₀)`: expected discounted returns in periods `0, …, n` (SLP p. 244). -/
noncomputable def uN (s₀ : X × Z) (π : Plan Y Z) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (n + 1), M.β ^ t * ∫ h, ret M s₀ π t h ∂hist M.Q t s₀.2

/-- `u(π, s₀) = lim uₙ(π, s₀)`, possibly `±∞` (SLP p. 245). -/
noncomputable def planValue (s₀ : X × Z) (π : Plan Y Z) : EReal :=
  limUnder atTop fun n => (uN M s₀ π n : EReal)

/-- The **supremum function** `v*(s) = sup_{π ∈ Π(s)} u(π, s)` (SLP (2)). -/
noncomputable def vStar (s₀ : X × Z) : EReal :=
  ⨆ (π : Plan Y Z) (_ : IsFeasible M s₀ π), planValue M s₀ π

theorem planValue_eq {s₀ : X × Z} {π : Plan Y Z} {L : EReal}
    (h : Tendsto (fun n => (uN M s₀ π n : EReal)) atTop (𝓝 L)) : planValue M s₀ π = L :=
  h.limUnder_eq

theorem measurable_init (t : ℕ) : Measurable (Fin.init : (Fin (t + 1) → Z) → Fin t → Z) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurable_xState (hφ : Measurable M.φ) (s₀ : X × Z) {π : Plan Y Z}
    (hπ : ∀ t, Measurable (π t)) (t : ℕ) : Measurable (xState M s₀ π t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact hφ.comp ((ih.comp (measurable_init t)).prodMk (((hπ t).comp (measurable_init t)).prodMk
      (measurable_pi_apply _)))

theorem measurable_state (hφ : Measurable M.φ) (s₀ : X × Z) {π : Plan Y Z}
    (hπ : ∀ t, Measurable (π t)) (t : ℕ) : Measurable (state M s₀ π t) :=
  (measurable_xState M hφ s₀ hπ t).prodMk (measurable_lastState s₀.2 t)

theorem measurable_ret (hφ : Measurable M.φ) (hF : Measurable M.F) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (t : ℕ) : Measurable (ret M s₀ π t) :=
  hF.comp ((measurable_state M hφ s₀ hπ t).fst.prodMk ((hπ t).prodMk
    (measurable_state M hφ s₀ hπ t).snd))

/-- The state after a history extended at its last date: `s_{t+1} = (φ(x_t, π_t, z′), z′)`. -/
theorem state_snoc (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) (h : Fin t → Z) (z' : Z) :
    state M s₀ π (t + 1) (Fin.snoc h z') = (M.φ (xState M s₀ π t h, π t h, z'), z') := by
  simp [state, xState, Fin.init_snoc, lastState]

/-- The **continuation** `C(π, z₁)` of a plan following `z₁` (SLP (8)). -/
def cont (π : Plan Y Z) (z₁ : Z) : Plan Y Z := fun t h => π (t + 1) (Fin.cons z₁ h)

/-- The state after the first shock `z₁`: `(φ(x₀, π₀, z₁), z₁)`. -/
def start₁ (s₀ : X × Z) (π : Plan Y Z) (z₁ : Z) : X × Z := (M.φ (s₀.1, π 0 Fin.elim0, z₁), z₁)

omit [MeasurableSpace Z] in
theorem init_cons {t : ℕ} (z₁ : Z) (h : Fin (t + 1) → Z) :
    Fin.init (Fin.cons z₁ h : Fin (t + 2) → Z) = Fin.cons z₁ (Fin.init h) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [Fin.init]

theorem xState_cons (s₀ : X × Z) (π : Plan Y Z) (z₁ : Z) (t : ℕ) (h : Fin t → Z) :
    xState M s₀ π (t + 1) (Fin.cons z₁ h) = xState M (start₁ M s₀ π z₁) (cont π z₁) t h := by
  induction t with
  | zero =>
    have : Fin.init (Fin.cons z₁ h : Fin 1 → Z) = Fin.elim0 := funext fun i => i.elim0
    simp only [xState, start₁, this]
    rfl
  | succ t ih =>
    rw [xState, init_cons, ih, xState]
    simp only [cont]
    congr 2

/-- **The states of the continuation** are those of the plan:
`s_{t+1}^π(z₁, zᵗ) = s_t^{C(π, z₁)}(zᵗ)`. -/
theorem state_cons (s₀ : X × Z) (π : Plan Y Z) (z₁ : Z) (t : ℕ) (h : Fin t → Z) :
    state M s₀ π (t + 1) (Fin.cons z₁ h) = state M (start₁ M s₀ π z₁) (cont π z₁) t h := by
  rw [state, state, xState_cons, lastState_cons]
  rfl

theorem ret_cons (s₀ : X × Z) (π : Plan Y Z) (z₁ : Z) (t : ℕ) (h : Fin t → Z) :
    ret M s₀ π (t + 1) (Fin.cons z₁ h) = ret M (start₁ M s₀ π z₁) (cont π z₁) t h := by
  simp only [ret, state_cons]
  rfl

/-- The continuation of a feasible plan is feasible from `(φ(x₀, π₀, z₁), z₁)` (SLP p. 248). -/
theorem IsFeasible.cont {s₀ : X × Z} {π : Plan Y Z} (hπ : IsFeasible M s₀ π) (z₁ : Z) :
    IsFeasible M (start₁ M s₀ π z₁) (StochasticApplications.cont π z₁) := by
  refine ⟨fun t => (hπ.1 (t + 1)).comp ((measurable_cons t).comp
    (measurable_const.prodMk measurable_id)), fun t h => ?_⟩
  rw [← state_cons]
  exact hπ.2 (t + 1) (Fin.cons z₁ h)

/-- The states of the plan generated by selections `gₜ` (SLP p. 245, 258). -/
def genX (s₀ : X × Z) (g : ℕ → X × Z → Y) : (t : ℕ) → (Fin t → Z) → X
  | 0, _ => s₀.1
  | t + 1, h => M.φ (genX s₀ g t (Fin.init h),
      g t (genX s₀ g t (Fin.init h), lastState s₀.2 (Fin.init h)), h (Fin.last t))

/-- The plan **generated** from `s₀` by the selections `g₀, g₁, …`:
`π_t(zᵗ) = g_t(x_t, z_t)`. -/
def genPlan (s₀ : X × Z) (g : ℕ → X × Z → Y) : Plan Y Z :=
  fun t h => g t (genX M s₀ g t h, lastState s₀.2 h)

theorem xState_genPlan (s₀ : X × Z) (g : ℕ → X × Z → Y) (t : ℕ) :
    xState M s₀ (genPlan M s₀ g) t = genX M s₀ g t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext h
    simp only [xState, genX, ih]
    rfl

theorem state_genPlan (s₀ : X × Z) (g : ℕ → X × Z → Y) (t : ℕ) (h : Fin t → Z) :
    state M s₀ (genPlan M s₀ g) t h = (genX M s₀ g t h, lastState s₀.2 h) := by
  rw [state, xState_genPlan]

theorem genPlan_apply (s₀ : X × Z) (g : ℕ → X × Z → Y) (t : ℕ) (h : Fin t → Z) :
    genPlan M s₀ g t h = g t (state M s₀ (genPlan M s₀ g) t h) := by
  rw [state_genPlan]
  rfl

/-- A plan generated by measurable selections from `Γ` is feasible (SLP pp. 243, 258). -/
theorem genPlan_feasible (hφ : Measurable M.φ) (s₀ : X × Z) {g : ℕ → X × Z → Y}
    (hg : ∀ t, Measurable (g t)) (hgΓ : ∀ t s, g t s ∈ M.Γ s) :
    IsFeasible M s₀ (genPlan M s₀ g) := by
  have hX : ∀ t, Measurable (genX M s₀ g t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ t ih =>
      exact hφ.comp ((ih.comp (measurable_init t)).prodMk (((hg t).comp
        ((ih.comp (measurable_init t)).prodMk ((measurable_lastState s₀.2 t).comp
          (measurable_init t)))).prodMk (measurable_pi_apply _)))
  refine ⟨fun t => (hg t).comp ((hX t).prodMk (measurable_lastState s₀.2 t)), fun t h => ?_⟩
  rw [genPlan_apply]
  exact hgΓ t _

/-- **Lemma 9.1** (and **Exercise 9.3**). If `Γ` has a measurable selection and `φ` is
measurable, every `s₀` has a feasible plan — for instance the Markov plan `π_t = h(x_t, z_t)`
that uses the same selection at every date. -/
theorem lemma_9_1 (hφ : Measurable M.φ) {h : X × Z → Y} (hh : Measurable h)
    (hhΓ : ∀ s, h s ∈ M.Γ s) (s₀ : X × Z) : ∃ π, IsFeasible M s₀ π :=
  ⟨genPlan M s₀ fun _ => h, genPlan_feasible M hφ s₀ (fun _ => hh) fun _ => hhΓ⟩

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 9.2: a solution of the functional equation is the supremum function

SLP §9.1, pp. 246–248 and Exercise 9.4. The functional equation (5′)
`v(x, z) = sup_{y ∈ Γ(x, z)} {F(x, y, z) + β ∫ v[φ(x, y, z′), z′] Q(z, dz′)}` (`SolvesFE`, with
right side `rhs` and expected continuation value `expV`) and its policy correspondence (6′)
(`policy`).

**Theorem 9.2** (`theorem_9_2`, and `ex_9_4` for the second formulation): if a measurable `v`
solves the functional equation, satisfies the limit condition (7) along every feasible plan, and
`G` has a measurable selection, then `v = v*` and every plan generated by `G` is optimal. The
book's proof: by (5), for every feasible plan
`v(s₀) ≥ uₙ(π, s₀) + βⁿ⁺¹ ∫ v(s_{n+1}) dμⁿ⁺¹` (`v_ge_uN`), with equality for plans generated by
`G` (`v_eq_uN`); the step from `n` to `n + 1` integrates (5) over `μⁿ⁺¹` and recombines the two
integrals with Exercise 8.8 (`integral_v_step`).

The integrability that the book's argument uses implicitly — of the returns and of
`v(s_t)` along each feasible plan — is a hypothesis.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (M : Model X Y Z)

/-- The expected continuation value `∫ v[φ(x, y, z′), z′] Q(z, dz′)`. -/
noncomputable def expV (v : X × Z → ℝ) (s : X × Z) (y : Y) : ℝ :=
  ∫ z', v (M.φ (s.1, y, z'), z') ∂M.Q s.2

/-- The right side of the functional equation, `F(x, y, z) + β ∫ v[φ(x, y, z′), z′] Q(z, dz′)`. -/
noncomputable def rhs (v : X × Z → ℝ) (s : X × Z) (y : Y) : ℝ :=
  M.F (s.1, y, s.2) + M.β * expV M v s y

/-- `v` solves the **functional equation** (SLP (5), (5′)). -/
def SolvesFE (v : X × Z → ℝ) : Prop := ∀ s, IsLUB (rhs M v s '' M.Γ s) (v s)

/-- The **policy correspondence** `G` (SLP (6), (6′)). -/
def policy (v : X × Z → ℝ) (s : X × Z) : Set Y := {y | y ∈ M.Γ s ∧ v s = rhs M v s y}

/-- Integrability of a function on next period's histories gives integrability of its
conditional expectation given today's history. -/
theorem integrable_next (Q : Kernel Z Z) [IsMarkovKernel Q] (t : ℕ) (z₀ : Z)
    {F : (Fin (t + 1) → Z) → ℝ} (hF : Integrable F (hist Q (t + 1) z₀)) :
    Integrable (fun h => ∫ z', F (Fin.snoc h z') ∂Q (lastState z₀ h)) (hist Q t z₀) := by
  have := ex_8_8a Q t
  have := isMarkovKernel_nextKernel Q z₀ t
  rw [ex_8_8b Q t z₀] at hF
  have hF' := (integrable_map_measure hF.1 (measurable_snoc t).aemeasurable).1 hF
  exact MeasureTheory.Integrable.integral_compProd (κ := Kernel.const Unit (hist Q t z₀))
    (η := Kernel.prodMkLeft Unit (nextKernel Q z₀ t)) (a := ()) hF'

/-- Integrability of a function on histories gives integrability of its integral over later
dates given the first shock. -/
theorem integrable_first (Q : Kernel Z Z) [IsMarkovKernel Q] (t : ℕ) (z₀ : Z)
    {F : (Fin (t + 1) → Z) → ℝ} (hF : Integrable F (hist Q (t + 1) z₀)) :
    Integrable (fun z₁ => ∫ h, F (Fin.cons z₁ h) ∂hist Q t z₁) (Q z₀) := by
  have := ex_8_8a Q t
  rw [hist_succ_eq_cons Q t z₀] at hF
  have hF' := (integrable_map_measure hF.1 (measurable_cons t).aemeasurable).1 hF
  exact MeasureTheory.Integrable.integral_compProd (κ := Kernel.const Unit (Q z₀))
    (η := Kernel.prodMkLeft Unit (hist Q t)) (a := ()) hF'

theorem integral_hist_zero (Q : Kernel Z Z) (z₀ : Z) (f : (Fin 0 → Z) → ℝ) :
    ∫ h, f h ∂hist Q 0 z₀ = f Fin.elim0 := by
  have hc : ∀ h : Fin 0 → Z, f h = f Fin.elim0 := fun h => by congr 1; funext i; exact i.elim0
  simp_rw [hc]
  simp [hist]

variable [IsMarkovKernel M.Q]

/-- `∫ v(s_{t+1}) dμᵗ⁺¹ = ∫ [∫ v(φ(x_t, π_t, z′), z′) Q(z_t, dz′)] dμᵗ` (Exercise 8.8). -/
theorem integral_v_succ {v : X × Z → ℝ} (s₀ : X × Z) (π : Plan Y Z) (t : ℕ)
    (hIv : Integrable (fun h => v (state M s₀ π (t + 1) h)) (hist M.Q (t + 1) s₀.2)) :
    ∫ h, v (state M s₀ π (t + 1) h) ∂hist M.Q (t + 1) s₀.2 =
      ∫ h, expV M v (state M s₀ π t h) (π t h) ∂hist M.Q t s₀.2 := by
  rw [ex_8_8c_last M.Q t s₀.2 hIv]
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  simp only [state_snoc, expV]
  rfl

theorem integrable_expV {v : X × Z → ℝ} (s₀ : X × Z) (π : Plan Y Z) (t : ℕ)
    (hIv : Integrable (fun h => v (state M s₀ π (t + 1) h)) (hist M.Q (t + 1) s₀.2)) :
    Integrable (fun h => expV M v (state M s₀ π t h) (π t h)) (hist M.Q t s₀.2) := by
  have := integrable_next M.Q t s₀.2 hIv
  refine this.congr (Eventually.of_forall fun h => ?_)
  simp only [state_snoc, expV]
  rfl

/-- **The step of Theorem 9.2.** Integrating (5) over `μᵗ`:
`∫ F(s_t, π_t) dμᵗ + β ∫ v(s_{t+1}) dμᵗ⁺¹ ≤ ∫ v(s_t) dμᵗ`, with equality if `π_t ∈ G(s_t)`. -/
theorem integral_v_step {v : X × Z → ℝ}
    (hle : ∀ s, ∀ y ∈ M.Γ s, rhs M v s y ≤ v s) {s₀ : X × Z} {π : Plan Y Z}
    (hπ : IsFeasible M s₀ π) (t : ℕ) (hIr : Integrable (ret M s₀ π t) (hist M.Q t s₀.2))
    (hIv : Integrable (fun h => v (state M s₀ π t h)) (hist M.Q t s₀.2))
    (hIv' : Integrable (fun h => v (state M s₀ π (t + 1) h)) (hist M.Q (t + 1) s₀.2)) :
    ∫ h, ret M s₀ π t h ∂hist M.Q t s₀.2 +
        M.β * ∫ h, v (state M s₀ π (t + 1) h) ∂hist M.Q (t + 1) s₀.2 ≤
      ∫ h, v (state M s₀ π t h) ∂hist M.Q t s₀.2 ∧
    ((∀ h, π t h ∈ policy M v (state M s₀ π t h)) →
      ∫ h, ret M s₀ π t h ∂hist M.Q t s₀.2 +
        M.β * ∫ h, v (state M s₀ π (t + 1) h) ∂hist M.Q (t + 1) s₀.2 =
      ∫ h, v (state M s₀ π t h) ∂hist M.Q t s₀.2) := by
  have hE := integrable_expV M s₀ π t hIv'
  rw [integral_v_succ M s₀ π t hIv', ← integral_const_mul, ← integral_add hIr (hE.const_mul _)]
  constructor
  · refine integral_mono (hIr.add (hE.const_mul _)) hIv fun h => ?_
    exact hle _ _ (hπ.2 t h)
  · intro hG
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    exact (hG h).2.symm

/-- **The inequality of Theorem 9.2:** `v(s₀) ≥ uₙ(π, s₀) + βⁿ⁺¹ ∫ v(s_{n+1}) dμⁿ⁺¹`. -/
theorem v_ge_uN {v : X × Z → ℝ} (hβ : 0 ≤ M.β) (hle : ∀ s, ∀ y ∈ M.Γ s, rhs M v s y ≤ v s)
    {s₀ : X × Z} {π : Plan Y Z} (hπ : IsFeasible M s₀ π)
    (hIr : ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2))
    (hIv : ∀ t, Integrable (fun h => v (state M s₀ π t h)) (hist M.Q t s₀.2)) (n : ℕ) :
    uN M s₀ π n + M.β ^ (n + 1) * ∫ h, v (state M s₀ π (n + 1) h) ∂hist M.Q (n + 1) s₀.2 ≤
      v s₀ := by
  induction n with
  | zero =>
    have := (integral_v_step M hle hπ 0 (hIr 0) (hIv 0) (hIv 1)).1
    simp only [integral_hist_zero] at this
    simpa [uN, integral_hist_zero, state_zero] using this
  | succ n ih =>
    have hstep := (integral_v_step M hle hπ (n + 1) (hIr _) (hIv _) (hIv _)).1
    have hpow : 0 ≤ M.β ^ (n + 1) := pow_nonneg hβ _
    calc uN M s₀ π (n + 1) + M.β ^ (n + 1 + 1) *
          ∫ h, v (state M s₀ π (n + 1 + 1) h) ∂hist M.Q (n + 1 + 1) s₀.2
        = uN M s₀ π n + M.β ^ (n + 1) * (∫ h, ret M s₀ π (n + 1) h ∂hist M.Q (n + 1) s₀.2 +
            M.β * ∫ h, v (state M s₀ π (n + 1 + 1) h) ∂hist M.Q (n + 1 + 1) s₀.2) := by
          rw [uN, Finset.sum_range_succ, ← uN]
          ring
      _ ≤ uN M s₀ π n + M.β ^ (n + 1) *
            ∫ h, v (state M s₀ π (n + 1) h) ∂hist M.Q (n + 1) s₀.2 := by
          gcongr
      _ ≤ v s₀ := ih

/-- **The equality of Theorem 9.2** for plans that follow `G`. -/
theorem v_eq_uN {v : X × Z → ℝ} (hle : ∀ s, ∀ y ∈ M.Γ s, rhs M v s y ≤ v s)
    {s₀ : X × Z} {π : Plan Y Z} (hπ : IsFeasible M s₀ π)
    (hG : ∀ t h, π t h ∈ policy M v (state M s₀ π t h))
    (hIr : ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2))
    (hIv : ∀ t, Integrable (fun h => v (state M s₀ π t h)) (hist M.Q t s₀.2)) (n : ℕ) :
    uN M s₀ π n + M.β ^ (n + 1) * ∫ h, v (state M s₀ π (n + 1) h) ∂hist M.Q (n + 1) s₀.2 =
      v s₀ := by
  induction n with
  | zero =>
    have := (integral_v_step M hle hπ 0 (hIr 0) (hIv 0) (hIv 1)).2 (hG 0)
    simp only [integral_hist_zero] at this
    simpa [uN, integral_hist_zero, state_zero] using this
  | succ n ih =>
    have hstep := (integral_v_step M hle hπ (n + 1) (hIr _) (hIv _) (hIv _)).2 (hG _)
    rw [← ih, uN, Finset.sum_range_succ, ← uN, ← hstep]
    ring

omit [IsMarkovKernel M.Q] in
theorem SolvesFE.le {v : X × Z → ℝ} (hFE : SolvesFE M v) : ∀ s, ∀ y ∈ M.Γ s, rhs M v s y ≤ v s :=
  fun s y hy => (hFE s).1 ⟨y, hy, rfl⟩

/-- **The upper bound of Theorem 9.2 for one plan**: if the returns and `v(s_t)` are integrable
along `π`, `uₙ(π, s₀)` converges, and `βᵗ ∫ v(s_t) dμᵗ → 0` along `π`, then `u(π, s₀) ≤ v(s₀)`. -/
theorem planValue_le_of_limit (hβ : 0 ≤ M.β) {v : X × Z → ℝ} (hFE : SolvesFE M v) {s₀ : X × Z}
    {π : Plan Y Z} (hπ : IsFeasible M s₀ π)
    (hint : ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2) ∧
      Integrable (fun h => v (state M s₀ π t h)) (hist M.Q t s₀.2))
    (hconv : ∃ L, Tendsto (fun n => (uN M s₀ π n : EReal)) atTop (𝓝 L))
    (h7 : Tendsto (fun t => M.β ^ t * ∫ h, v (state M s₀ π t h) ∂hist M.Q t s₀.2) atTop (𝓝 0)) :
    planValue M s₀ π ≤ v s₀ := by
  have hle := hFE.le M
  have hrest := h7.comp (tendsto_add_atTop_nat 1)
  obtain ⟨L, hL⟩ := hconv
  rw [planValue_eq M hL]
  have hbound : ∀ n, (uN M s₀ π n : EReal) ≤ ((v s₀ - M.β ^ (n + 1) *
      ∫ h, v (state M s₀ π (n + 1) h) ∂hist M.Q (n + 1) s₀.2 : ℝ) : EReal) := fun n => by
    refine EReal.coe_le_coe_iff.2 ?_
    linarith [v_ge_uN M hβ hle hπ (fun t => (hint t).1) (fun t => (hint t).2) n]
  have hlim : Tendsto (fun n => ((v s₀ - M.β ^ (n + 1) *
      ∫ h, v (state M s₀ π (n + 1) h) ∂hist M.Q (n + 1) s₀.2 : ℝ) : EReal)) atTop
      (𝓝 (v s₀ : EReal)) := by
    refine (continuous_coe_real_ereal.tendsto _).comp ?_
    simpa using tendsto_const_nhds.sub hrest
  exact le_of_tendsto_of_tendsto' hL hlim hbound

/-- **The equality of Theorem 9.2 for one plan**: a plan generated by measurable selections from
`G`, along which the integrability and limit conditions hold, attains `v(s₀)`. -/
theorem planValue_genPlan_of_limit (hφ : Measurable M.φ) {v : X × Z → ℝ} (hFE : SolvesFE M v)
    (s₀ : X × Z) {g : ℕ → X × Z → Y} (hg : ∀ t, Measurable (g t))
    (hgG : ∀ t s, g t s ∈ policy M v s)
    (hint : ∀ t, Integrable (ret M s₀ (genPlan M s₀ g) t) (hist M.Q t s₀.2) ∧
      Integrable (fun h => v (state M s₀ (genPlan M s₀ g) t h)) (hist M.Q t s₀.2))
    (h7 : Tendsto (fun t => M.β ^ t *
      ∫ h, v (state M s₀ (genPlan M s₀ g) t h) ∂hist M.Q t s₀.2) atTop (𝓝 0)) :
    IsFeasible M s₀ (genPlan M s₀ g) ∧ planValue M s₀ (genPlan M s₀ g) = v s₀ := by
  have hle := hFE.le M
  have hfeas := genPlan_feasible M hφ s₀ hg fun t s => (hgG t s).1
  have hGπ : ∀ t h, genPlan M s₀ g t h ∈ policy M v (state M s₀ (genPlan M s₀ g) t h) :=
    fun t h => by rw [genPlan_apply]; exact hgG t _
  refine ⟨hfeas, planValue_eq M ?_⟩
  have heq : ∀ n, (uN M s₀ (genPlan M s₀ g) n : EReal) = ((v s₀ - M.β ^ (n + 1) *
      ∫ h, v (state M s₀ (genPlan M s₀ g) (n + 1) h) ∂hist M.Q (n + 1) s₀.2 : ℝ) : EReal) :=
    fun n => by
      rw [← v_eq_uN M hle hfeas hGπ (fun t => (hint t).1) (fun t => (hint t).2) n]
      congr 1
      ring
  simp_rw [heq]
  refine (continuous_coe_real_ereal.tendsto _).comp ?_
  simpa using tendsto_const_nhds.sub (h7.comp (tendsto_add_atTop_nat 1))

/-- **Exercise 9.4 (Theorem 9.2 for the second formulation).** Let `v` be measurable and solve
the functional equation (5′); suppose that along every plan feasible from `s₀` the returns and
`v(s_t)` are integrable, `uₙ` converges (Assumption 9.2′), and the limit condition (7′)
`βᵗ ∫ v(s_t) dμᵗ → 0` holds; and let `g₀, g₁, …` be measurable selections from `G`. Then
`u(π, s₀) ≤ v(s₀)` for every feasible `π`, the plan generated by the `gₜ` attains `v(s₀)`, and
`v(s₀) = v*(s₀)`. -/
theorem ex_9_4 (hφ : Measurable M.φ) (hβ : 0 ≤ M.β) {v : X × Z → ℝ} (hFE : SolvesFE M v)
    (s₀ : X × Z)
    (hint : ∀ π, IsFeasible M s₀ π → ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2) ∧
      Integrable (fun h => v (state M s₀ π t h)) (hist M.Q t s₀.2))
    (hconv : ∀ π, IsFeasible M s₀ π → ∃ L, Tendsto (fun n => (uN M s₀ π n : EReal)) atTop (𝓝 L))
    (h7 : ∀ π, IsFeasible M s₀ π →
      Tendsto (fun t => M.β ^ t * ∫ h, v (state M s₀ π t h) ∂hist M.Q t s₀.2) atTop (𝓝 0))
    {g : ℕ → X × Z → Y} (hg : ∀ t, Measurable (g t)) (hgG : ∀ t s, g t s ∈ policy M v s) :
    (∀ π, IsFeasible M s₀ π → planValue M s₀ π ≤ v s₀) ∧
      planValue M s₀ (genPlan M s₀ g) = v s₀ ∧ vStar M s₀ = v s₀ := by
  have hupper : ∀ π, IsFeasible M s₀ π → planValue M s₀ π ≤ v s₀ := fun π hπ =>
    planValue_le_of_limit M hβ hFE hπ (hint π hπ) (hconv π hπ) (h7 π hπ)
  have hfeas := genPlan_feasible M hφ s₀ hg fun t s => (hgG t s).1
  have hattain := (planValue_genPlan_of_limit M hφ hFE s₀ hg hgG (hint _ hfeas) (h7 _ hfeas)).2
  refine ⟨hupper, hattain, le_antisymm (iSup₂_le hupper) ?_⟩
  rw [← hattain]
  exact le_iSup₂ (f := fun π (_ : IsFeasible M s₀ π) => planValue M s₀ π) _ hfeas

/-- **Theorem 9.2** (the book's first formulation, `x_{t+1} = π_t`). -/
theorem theorem_9_2 (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : X × Z → Set X)
    (F : X × X × Z → ℝ) {β : ℝ} (hβ : 0 ≤ β) {v : X × Z → ℝ}
    (hFE : SolvesFE (Model.first Q Γ F β) v) (s₀ : X × Z)
    (hint : ∀ π, IsFeasible (Model.first Q Γ F β) s₀ π → ∀ t,
      Integrable (ret (Model.first Q Γ F β) s₀ π t) (hist Q t s₀.2) ∧
      Integrable (fun h => v (state (Model.first Q Γ F β) s₀ π t h)) (hist Q t s₀.2))
    (hconv : ∀ π, IsFeasible (Model.first Q Γ F β) s₀ π →
      ∃ L, Tendsto (fun n => (uN (Model.first Q Γ F β) s₀ π n : EReal)) atTop (𝓝 L))
    (h7 : ∀ π, IsFeasible (Model.first Q Γ F β) s₀ π →
      Tendsto (fun t => β ^ t * ∫ h, v (state (Model.first Q Γ F β) s₀ π t h) ∂hist Q t s₀.2)
        atTop (𝓝 0))
    {g : ℕ → X × Z → X} (hg : ∀ t, Measurable (g t))
    (hgG : ∀ t s, g t s ∈ policy (Model.first Q Γ F β) v s) :
    (∀ π, IsFeasible (Model.first Q Γ F β) s₀ π → planValue (Model.first Q Γ F β) s₀ π ≤ v s₀) ∧
      planValue (Model.first Q Γ F β) s₀ (genPlan (Model.first Q Γ F β) s₀ g) = v s₀ ∧
      vStar (Model.first Q Γ F β) s₀ = v s₀ :=
  have : IsMarkovKernel (Model.first Q Γ F β).Q := ‹_›
  ex_9_4 (Model.first Q Γ F β) measurable_snd.fst hβ hFE s₀ hint hconv h7 hg hgG

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lemma 9.3: the value of a plan and of its continuations

SLP §9.1, pp. 248–250, Exercises 9.1 and 9.5a.

* The finite recursion `uₙ₊₁(π, s₀) = F(x₀, π₀, z₀) + β ∫ uₙ[C(π, z₁), s₁] Q(z₀, dz₁)`
  (`uN_succ`), from splitting `μᵗ⁺¹` at its first date (Exercise 8.8).
* **Exercise 9.1**: `z₁ ↦ uₙ[C(π, z₁), s₁(z₁)]` is measurable, and so is
  `z₁ ↦ u[C(π, z₁), s₁(z₁)]` when the limits exist (`ex_9_1`).
* **Lemma 9.3** (and **Exercise 9.5a**) `u(π, s₀) = F(x₀, π₀, z₀) + β ∫ u[C(π, z₁), s₁] Q(z₀, dz₁)`:
  under Assumption 9.3 — returns bounded by `L_t` with `Σ βᵗ L_t < ∞` — by dominated convergence
  (`lemma_9_3`); and for nonnegative returns, with values in `[0, +∞]`, by monotone convergence
  (`lemma_9_3_nonneg`), which gives the case `F ≤ 0` by symmetry.
* The real series `uR` with its bounds (`tendsto_uN`, `abs_uR_le`) and the continuation bounds
  `L_{t+1}` (`bounds_cont`), used by Theorem 9.4.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (M : Model X Y Z) [IsMarkovKernel M.Q]

/-- The expected return of the continuation at date `t`, as a function of the first shock. -/
theorem integral_ret_succ (s₀ : X × Z) (π : Plan Y Z) (t : ℕ)
    (hI : Integrable (ret M s₀ π (t + 1)) (hist M.Q (t + 1) s₀.2)) :
    ∫ h, ret M s₀ π (t + 1) h ∂hist M.Q (t + 1) s₀.2 =
      ∫ z₁, ∫ h, ret M (start₁ M s₀ π z₁) (cont π z₁) t h ∂hist M.Q t z₁ ∂M.Q s₀.2 := by
  rw [ex_8_8c_first M.Q t s₀.2 hI]
  simp_rw [ret_cons]

theorem integrable_ret_cont (s₀ : X × Z) (π : Plan Y Z) (t : ℕ)
    (hI : Integrable (ret M s₀ π (t + 1)) (hist M.Q (t + 1) s₀.2)) :
    Integrable (fun z₁ => ∫ h, ret M (start₁ M s₀ π z₁) (cont π z₁) t h ∂hist M.Q t z₁)
      (M.Q s₀.2) := by
  have := integrable_first M.Q t s₀.2 hI
  simp_rw [ret_cons] at this
  exact this

/-- **The finite recursion** behind Lemma 9.3:
`uₙ₊₁(π, s₀) = F(x₀, π₀, z₀) + β ∫ uₙ[C(π, z₁), s₁] Q(z₀, dz₁)`. -/
theorem uN_succ (s₀ : X × Z) (π : Plan Y Z)
    (hI : ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2)) (n : ℕ) :
    uN M s₀ π (n + 1) = ret M s₀ π 0 Fin.elim0 +
      M.β * ∫ z₁, uN M (start₁ M s₀ π z₁) (cont π z₁) n ∂M.Q s₀.2 := by
  have hs : ∀ z₁, (start₁ M s₀ π z₁).2 = z₁ := fun _ => rfl
  simp only [uN, hs]
  rw [integral_finsetSum _ fun t _ => (integrable_ret_cont M s₀ π t (hI (t + 1))).const_mul _,
    Finset.sum_range_succ', Finset.mul_sum, integral_hist_zero]
  simp only [pow_zero, one_mul, add_comm (ret M s₀ π 0 Fin.elim0)]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, integral_ret_succ M s₀ π t (hI (t + 1)), pow_succ]
  ring

omit [IsMarkovKernel M.Q] in
/-- Joint measurability of the continuation returns in `(z₁, zᵗ)`. -/
theorem measurable_ret_cont (hφ : Measurable M.φ) (hF : Measurable M.F) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (t : ℕ) :
    Measurable fun p : Z × (Fin t → Z) => ret M (start₁ M s₀ π p.1) (cont π p.1) t p.2 := by
  have := (measurable_ret M hφ hF s₀ hπ (t + 1)).comp (measurable_cons t)
  simp_rw [Function.comp_def, ret_cons] at this
  exact this

/-- **Exercise 9.1.** `z₁ ↦ uₙ[C(π, z₁), (φ(x₀, π₀, z₁), z₁)]` is measurable, and so is its
limit `z₁ ↦ u[C(π, z₁), (φ(x₀, π₀, z₁), z₁)]` when the limits exist. -/
theorem ex_9_1 (hφ : Measurable M.φ) (hF : Measurable M.F) (s₀ : X × Z) {π : Plan Y Z}
    (hπ : ∀ t, Measurable (π t)) :
    (∀ n, Measurable fun z₁ => uN M (start₁ M s₀ π z₁) (cont π z₁) n) ∧
      ((∀ z₁, ∃ L, Tendsto (fun n => (uN M (start₁ M s₀ π z₁) (cont π z₁) n : EReal)) atTop
        (𝓝 L)) → Measurable fun z₁ => planValue M (start₁ M s₀ π z₁) (cont π z₁)) := by
  have hn : ∀ n, Measurable fun z₁ => uN M (start₁ M s₀ π z₁) (cont π z₁) n := by
    intro n
    refine Finset.measurable_sum _ fun t _ => measurable_const.mul ?_
    have := ex_8_8a M.Q t
    exact ((measurable_ret_cont M hφ hF s₀ hπ t).stronglyMeasurable.integral_kernel_prod_right'
      (κ := hist M.Q t)).measurable
  refine ⟨hn, fun hconv => ?_⟩
  have heq : (fun z₁ => planValue M (start₁ M s₀ π z₁) (cont π z₁)) =
      fun z₁ => liminf (fun n => (uN M (start₁ M s₀ π z₁) (cont π z₁) n : EReal)) atTop := by
    funext z₁
    obtain ⟨L, hL⟩ := hconv z₁
    rw [planValue_eq M hL, hL.liminf_eq]
  rw [heq]
  exact Measurable.liminf fun n => measurable_coe_real_ereal.comp (hn n)

/-- The value of a plan as the real series `Σ βᵗ ∫ F(x_t, π_t, z_t) dμᵗ` (under Assumption 9.3
the series converges absolutely). -/
noncomputable def uR (s₀ : X × Z) (π : Plan Y Z) : ℝ :=
  ∑' t, M.β ^ t * ∫ h, ret M s₀ π t h ∂hist M.Q t s₀.2

omit [IsMarkovKernel M.Q] in
/-- Bounds `L_t` on the returns are nonnegative. -/
theorem bound_nonneg (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (t : ℕ) : 0 ≤ K t :=
  (abs_nonneg _).trans (hK t fun _ => s.2)

/-- Bounded returns are integrable. -/
theorem integrable_ret_of_bound (hφ : Measurable M.φ) (hF : Measurable M.F) (s : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (t : ℕ) : Integrable (ret M s π t) (hist M.Q t s.2) := by
  have := ex_8_8a M.Q t
  refine (integrable_const (K t)).mono' (measurable_ret M hφ hF s hπ t).aestronglyMeasurable
    (Eventually.of_forall fun h => ?_)
  rw [Real.norm_eq_abs]
  exact hK t h

/-- Under Assumption 9.3, `|βᵗ ∫ F dμᵗ| ≤ βᵗ L_t`. -/
theorem abs_term_le (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (t : ℕ) :
    |M.β ^ t * ∫ h, ret M s π t h ∂hist M.Q t s.2| ≤ M.β ^ t * K t := by
  have := ex_8_8a M.Q t
  rw [abs_mul, abs_of_nonneg (pow_nonneg hβ t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ t)
  have := norm_integral_le_of_norm_le_const (μ := hist M.Q t s.2) (C := K t)
    (f := ret M s π t) (Eventually.of_forall fun h => by rw [Real.norm_eq_abs]; exact hK t h)
  simpa [Real.norm_eq_abs, measureReal_def] using this

theorem summable_terms (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (hK' : Summable fun t => M.β ^ t * K t) :
    Summable fun t => M.β ^ t * ∫ h, ret M s π t h ∂hist M.Q t s.2 :=
  Summable.of_norm_bounded hK' fun t => by
    rw [Real.norm_eq_abs]; exact abs_term_le M hβ s π hK t

/-- Under Assumption 9.3, `uₙ(π, s) → Σ βᵗ ∫ F dμᵗ`. -/
theorem tendsto_uN (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (hK' : Summable fun t => M.β ^ t * K t) :
    Tendsto (fun n => uN M s π n) atTop (𝓝 (uR M s π)) :=
  (summable_terms M hβ s π hK hK').hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem planValue_eq_uR (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (hK' : Summable fun t => M.β ^ t * K t) :
    planValue M s π = (uR M s π : EReal) :=
  planValue_eq M ((continuous_coe_real_ereal.tendsto _).comp (tendsto_uN M hβ s π hK hK'))

theorem abs_uN_le (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (hK' : Summable fun t => M.β ^ t * K t) (n : ℕ) :
    |uN M s π n| ≤ ∑' t, M.β ^ t * K t := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun t _ => abs_term_le M hβ s π hK t).trans ?_
  exact hK'.sum_le_tsum _ fun t _ => mul_nonneg (pow_nonneg hβ t) (bound_nonneg M s π hK t)

theorem abs_uR_le (hβ : 0 ≤ M.β) (s : X × Z) (π : Plan Y Z) {K : ℕ → ℝ}
    (hK : ∀ t h, |ret M s π t h| ≤ K t) (hK' : Summable fun t => M.β ^ t * K t) :
    |uR M s π| ≤ ∑' t, M.β ^ t * K t :=
  le_of_tendsto' ((continuous_abs.tendsto _).comp (tendsto_uN M hβ s π hK hK'))
    (abs_uN_le M hβ s π hK hK')

omit [IsMarkovKernel M.Q] in
/-- The continuations of a plan satisfying Assumption 9.3 with bounds `L_t` satisfy it with the
shifted bounds `L_{t+1}`. -/
theorem bounds_cont (hβ : 0 ≤ M.β) (s₀ : X × Z) (π : Plan Y Z) {L : ℕ → ℝ}
    (hL : ∀ t h, |ret M s₀ π t h| ≤ L t) (hsum : Summable fun t => M.β ^ t * L t) :
    (∀ z₁ t h, |ret M (start₁ M s₀ π z₁) (cont π z₁) t h| ≤ L (t + 1)) ∧
      Summable fun t => M.β ^ t * L (t + 1) := by
  refine ⟨fun z₁ t h => by rw [← ret_cons]; exact hL (t + 1) _, ?_⟩
  by_cases hβ0 : M.β = 0
  · refine summable_of_ne_finset_zero (s := {0}) fun t ht => ?_
    have : t ≠ 0 := by simpa using ht
    simp [hβ0, this]
  · have := (summable_nat_add_iff 1).2 hsum
    refine (this.mul_left (M.β)⁻¹).congr fun t => ?_
    rw [pow_succ]
    field_simp

/-- `z₁ ↦ Σ βᵗ ∫ F dμᵗ` along the continuations is measurable (Exercise 9.1). -/
theorem measurable_uR_cont (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) {L : ℕ → ℝ}
    (hL : ∀ t h, |ret M s₀ π t h| ≤ L t) (hsum : Summable fun t => M.β ^ t * L t) :
    Measurable fun z₁ => uR M (start₁ M s₀ π z₁) (cont π z₁) := by
  obtain ⟨hLc, hsumc⟩ := bounds_cont M hβ s₀ π hL hsum
  exact measurable_of_tendsto_metrizable (ex_9_1 M hφ hF s₀ hπ).1
    (tendsto_pi_nhds.2 fun z₁ => tendsto_uN M hβ _ _ (hLc z₁) hsumc)

/-- **Lemma 9.3** (and **Exercise 9.5a**) under Assumption 9.3: if the returns of `π` are bounded,
`|F(x_t, π_t, z_t)| ≤ L_t`, with `Σ βᵗ L_t < ∞`, then `u(π, s₀)` is the real number
`Σ βᵗ ∫ F dμᵗ`, and `u(π, s₀) = F(x₀, π₀, z₀) + β ∫ u[C(π, z₁), s₁] Q(z₀, dz₁)`. The book's
proof: pass to the limit in the finite recursion under the integral, by dominated convergence. -/
theorem lemma_9_3 (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) {L : ℕ → ℝ}
    (hL : ∀ t h, |ret M s₀ π t h| ≤ L t) (hsum : Summable fun t => M.β ^ t * L t) :
    planValue M s₀ π = (uR M s₀ π : EReal) ∧
      uR M s₀ π = ret M s₀ π 0 Fin.elim0 +
        M.β * ∫ z₁, uR M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 := by
  refine ⟨planValue_eq_uR M hβ s₀ π hL hsum, ?_⟩
  obtain ⟨hLc, hsumc⟩ := bounds_cont M hβ s₀ π hL hsum
  have hmeas := (ex_9_1 M hφ hF s₀ hπ).1
  have hDCT : Tendsto (fun n => ∫ z₁, uN M (start₁ M s₀ π z₁) (cont π z₁) n ∂M.Q s₀.2) atTop
      (𝓝 (∫ z₁, uR M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∑' t, M.β ^ t * L (t + 1))
      (fun n => (hmeas n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun z₁ => by
        rw [Real.norm_eq_abs]; exact abs_uN_le M hβ _ _ (hLc z₁) hsumc n)
      (Eventually.of_forall fun z₁ => tendsto_uN M hβ _ _ (hLc z₁) hsumc)
  have hrec : Tendsto (fun n => uN M s₀ π (n + 1)) atTop (𝓝 (ret M s₀ π 0 Fin.elim0 +
      M.β * ∫ z₁, uR M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2)) := by
    simp_rw [uN_succ M s₀ π (integrable_ret_of_bound M hφ hF s₀ hπ hL)]
    exact tendsto_const_nhds.add (hDCT.const_mul _)
  exact tendsto_nhds_unique ((tendsto_uN M hβ s₀ π hL hsum).comp (tendsto_add_atTop_nat 1)) hrec

/-- The total expected discounted return of a plan with nonnegative returns, in `[0, +∞]`. -/
noncomputable def planValuePos (s₀ : X × Z) (π : Plan Y Z) : ℝ≥0∞ :=
  ∑' t, ENNReal.ofReal (M.β ^ t) * ∫⁻ h, ENNReal.ofReal (ret M s₀ π t h) ∂hist M.Q t s₀.2

/-- **Lemma 9.3 for `F ≥ 0`** (the book's monotone convergence case): with values in `[0, +∞]`,
`u(π, s₀) = F(x₀, π₀, z₀) + β ∫ u[C(π, z₁), s₁] Q(z₀, dz₁)`. No integrability is needed. -/
theorem lemma_9_3_nonneg (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) :
    planValuePos M s₀ π = ENNReal.ofReal (ret M s₀ π 0 Fin.elim0) +
      ENNReal.ofReal M.β * ∫⁻ z₁, planValuePos M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 := by
  have hinner : ∀ t, Measurable fun z₁ =>
      ∫⁻ h, ENNReal.ofReal (ret M (start₁ M s₀ π z₁) (cont π z₁) t h) ∂hist M.Q t z₁ := by
    intro t
    have := ex_8_8a M.Q t
    exact (measurable_ret_cont M hφ hF s₀ hπ t).ennreal_ofReal.lintegral_kernel_prod_right'
      (κ := hist M.Q t)
  have hsplit : ∀ t, ∫⁻ h, ENNReal.ofReal (ret M s₀ π (t + 1) h) ∂hist M.Q (t + 1) s₀.2 =
      ∫⁻ z₁, ∫⁻ h, ENNReal.ofReal (ret M (start₁ M s₀ π z₁) (cont π z₁) t h) ∂hist M.Q t z₁
        ∂M.Q s₀.2 := fun t => by
    rw [hist_succ_lintegral M.Q t s₀.2 (measurable_ret M hφ hF s₀ hπ (t + 1)).ennreal_ofReal]
    simp_rw [ret_cons]
  rw [planValuePos, tsum_eq_zero_add' ENNReal.summable, hist_zero_lintegral]
  simp only [pow_zero, ENNReal.ofReal_one, one_mul, hsplit]
  congr 1
  have hs : ∀ z₁, (start₁ M s₀ π z₁).2 = z₁ := fun _ => rfl
  simp only [planValuePos, hs]
  rw [lintegral_tsum fun t => ((hinner t).const_mul _).aemeasurable, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun t => ?_
  rw [lintegral_const_mul _ (hinner t), ← mul_assoc, ← ENNReal.ofReal_mul hβ, pow_succ,
    mul_comm (M.β ^ t)]

/-! ### Absolutely summable plans -/

/-- The model with returns `|F|`. -/
abbrev Model.absF (M : Model X Y Z) : Model X Y Z := { M with F := fun p => |M.F p| }

omit [IsMarkovKernel M.Q] in
theorem xState_absF (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) :
    xState M.absF s₀ π t = xState M s₀ π t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext h
    simp only [xState, ih]

omit [IsMarkovKernel M.Q] in
theorem ret_absF (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) :
    ret M.absF s₀ π t = fun h => |ret M s₀ π t h| := by
  funext h
  simp only [ret, state, xState_absF]

/-- `Σ βᵗ ∫ |F(x_t, π_t, z_t)| dμᵗ ∈ [0, +∞]`. Plans for which it is finite generalize
Assumption 9.3. -/
noncomputable def planAbs (s₀ : X × Z) (π : Plan Y Z) : ℝ≥0∞ := planValuePos M.absF s₀ π

omit [IsMarkovKernel M.Q] in
theorem planAbs_eq (s₀ : X × Z) (π : Plan Y Z) : planAbs M s₀ π =
    ∑' t, ENNReal.ofReal (M.β ^ t) * ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2 := by
  simp only [planAbs, planValuePos, ret_absF]

omit [IsMarkovKernel M.Q] in
theorem measurable_cont_plan {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (z₁ : Z) :
    ∀ t, Measurable (cont π z₁ t) := fun t =>
  (hπ (t + 1)).comp ((measurable_cons t).comp (measurable_const.prodMk measurable_id))

/-- The recursion for `Σ βᵗ ∫ |F| dμᵗ` (Lemma 9.3 for `|F|`). -/
theorem planAbs_rec (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) :
    planAbs M s₀ π = ENNReal.ofReal |ret M s₀ π 0 Fin.elim0| +
      ENNReal.ofReal M.β * ∫⁻ z₁, planAbs M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 :=
  lemma_9_3_nonneg M.absF hφ (continuous_abs.measurable.comp hF) hβ s₀ hπ

theorem measurable_planAbs_cont (hφ : Measurable M.φ) (hF : Measurable M.F) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) :
    Measurable fun z₁ => planAbs M (start₁ M s₀ π z₁) (cont π z₁) := by
  refine Measurable.tsum fun t => measurable_const.mul ?_
  have := ex_8_8a M.Q t
  exact (measurable_ret_cont M.absF hφ (continuous_abs.measurable.comp hF) s₀ hπ t
    ).ennreal_ofReal.lintegral_kernel_prod_right' (κ := hist M.Q t)

omit [IsMarkovKernel M.Q] in
theorem term_le_planAbs (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) :
    ENNReal.ofReal (M.β ^ t) * ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2 ≤
      planAbs M s₀ π := by
  rw [planAbs_eq]
  exact ENNReal.le_tsum (f := fun t => ENNReal.ofReal (M.β ^ t) *
    ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2) t

/-- With `Σ βᵗ ∫ |F| dμᵗ < ∞` and `β > 0`, every return is integrable. -/
theorem integrable_ret_of_planAbs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤)
    (t : ℕ) : Integrable (ret M s₀ π t) (hist M.Q t s₀.2) := by
  have := ex_8_8a M.Q t
  have hm := measurable_ret M hφ hF s₀ hπ t
  have hlt := (term_le_planAbs M s₀ π t).trans_lt hfin.lt_top
  have hne : ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2 ≠ ⊤ := by
    rcases ENNReal.mul_lt_top_iff.1 hlt with h | h | h
    · exact h.2.ne
    · exact absurd h (ENNReal.ofReal_pos.2 (pow_pos hβ t)).ne'
    · rw [h]; exact ENNReal.zero_ne_top
  have hI : Integrable (fun h => |ret M s₀ π t h|) (hist M.Q t s₀.2) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.abs.aestronglyMeasurable
      (Eventually.of_forall fun h => abs_nonneg _)).1 hne
  refine (integrable_norm_iff hm.aestronglyMeasurable).1 ?_
  simpa only [Real.norm_eq_abs] using hI

theorem abs_term_le_planAbs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (t : ℕ) :
    |M.β ^ t * ∫ h, ret M s₀ π t h ∂hist M.Q t s₀.2| ≤
      (ENNReal.ofReal (M.β ^ t) *
        ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2).toReal := by
  have := ex_8_8a M.Q t
  have hm := measurable_ret M hφ hF s₀ hπ t
  rw [abs_mul, abs_of_nonneg (pow_nonneg hβ t), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hβ t), ← integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun h => abs_nonneg _) hm.abs.aestronglyMeasurable]
  exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (pow_nonneg hβ t)

/-- With `Σ βᵗ ∫ |F| dμᵗ < ∞`, the series `Σ βᵗ ∫ F dμᵗ` converges absolutely. -/
theorem summable_of_planAbs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤) :
    Summable fun t => M.β ^ t * ∫ h, ret M s₀ π t h ∂hist M.Q t s₀.2 := by
  rw [planAbs_eq] at hfin
  exact Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun t => by
    rw [Real.norm_eq_abs]; exact abs_term_le_planAbs M hφ hF hβ s₀ hπ t

theorem tendsto_uN_abs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤) :
    Tendsto (fun n => uN M s₀ π n) atTop (𝓝 (uR M s₀ π)) :=
  (summable_of_planAbs M hφ hF hβ s₀ hπ hfin).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)

theorem planValue_eq_uR_abs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤) :
    planValue M s₀ π = (uR M s₀ π : EReal) :=
  planValue_eq M ((continuous_coe_real_ereal.tendsto _).comp
    (tendsto_uN_abs M hφ hF hβ s₀ hπ hfin))

theorem abs_uN_le_planAbs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤)
    (n : ℕ) : |uN M s₀ π n| ≤ (planAbs M s₀ π).toReal := by
  have hfin' := hfin
  rw [planAbs_eq] at hfin' ⊢
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun t _ => abs_term_le_planAbs M hφ hF hβ s₀ hπ t).trans ?_
  rw [← ENNReal.toReal_sum fun t _ => ne_top_of_le_ne_top hfin' (ENNReal.le_tsum t)]
  exact ENNReal.toReal_mono hfin' (ENNReal.sum_le_tsum _)

/-- With `β > 0`, the continuations of an absolutely summable plan are absolutely summable for
`Q(z₀, ·)`-almost every `z₁`. -/
theorem ae_planAbs_cont (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (s₀ : X × Z) {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤) :
    ∫⁻ z₁, planAbs M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 ≠ ⊤ ∧
      ∀ᵐ z₁ ∂M.Q s₀.2, planAbs M (start₁ M s₀ π z₁) (cont π z₁) ≠ ⊤ := by
  have hrec := planAbs_rec M hφ hF hβ.le s₀ hπ
  have hle : ENNReal.ofReal M.β * ∫⁻ z₁, planAbs M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 ≤
      planAbs M s₀ π := by rw [hrec]; exact le_add_self
  have hlt := hle.trans_lt hfin.lt_top
  have hne : ∫⁻ z₁, planAbs M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 ≠ ⊤ := by
    rcases ENNReal.mul_lt_top_iff.1 hlt with h | h | h
    · exact h.2.ne
    · exact absurd h (ENNReal.ofReal_pos.2 hβ).ne'
    · rw [h]; exact ENNReal.zero_ne_top
  exact ⟨hne, (ae_lt_top (measurable_planAbs_cont M hφ hF s₀ hπ) hne).mono fun _ h => h.ne⟩

/-- **Lemma 9.3 for absolutely summable plans.** If `Σ βᵗ ∫ |F| dμᵗ < ∞` and `β > 0`, then
`z₁ ↦ u[C(π, z₁), s₁]` is integrable and
`u(π, s₀) = F(x₀, π₀, z₀) + β ∫ u[C(π, z₁), s₁] Q(z₀, dz₁)`, by dominated convergence with the
dominating function `Σ βᵗ ∫ |F| dμᵗ` of the continuations. -/
theorem lemma_9_3_abs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t)) (hfin : planAbs M s₀ π ≠ ⊤) :
    Integrable (fun z₁ => uR M (start₁ M s₀ π z₁) (cont π z₁)) (M.Q s₀.2) ∧
      uR M s₀ π = ret M s₀ π 0 Fin.elim0 +
        M.β * ∫ z₁, uR M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 := by
  obtain ⟨hne, hae⟩ := ae_planAbs_cont M hφ hF hβ s₀ hπ hfin
  have hmeas := (ex_9_1 M hφ hF s₀ hπ).1
  have hGm := measurable_planAbs_cont M hφ hF s₀ hπ
  have hG : Integrable (fun z₁ => (planAbs M (start₁ M s₀ π z₁) (cont π z₁)).toReal)
      (M.Q s₀.2) := integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hne
  have hbound : ∀ n, ∀ᵐ z₁ ∂M.Q s₀.2, ‖uN M (start₁ M s₀ π z₁) (cont π z₁) n‖ ≤
      (planAbs M (start₁ M s₀ π z₁) (cont π z₁)).toReal := fun n => by
    filter_upwards [hae] with z₁ hz₁
    rw [Real.norm_eq_abs]
    exact abs_uN_le_planAbs M hφ hF hβ.le _ (measurable_cont_plan hπ z₁) hz₁ n
  have hlim : ∀ᵐ z₁ ∂M.Q s₀.2, Tendsto (fun n => uN M (start₁ M s₀ π z₁) (cont π z₁) n) atTop
      (𝓝 (uR M (start₁ M s₀ π z₁) (cont π z₁))) := by
    filter_upwards [hae] with z₁ hz₁
    exact tendsto_uN_abs M hφ hF hβ.le _ (measurable_cont_plan hπ z₁) hz₁
  have hIu : Integrable (fun z₁ => uR M (start₁ M s₀ π z₁) (cont π z₁)) (M.Q s₀.2) := by
    refine hG.mono' (aestronglyMeasurable_of_tendsto_ae _
      (fun n => (hmeas n).aestronglyMeasurable) hlim) ?_
    filter_upwards [hlim, hae] with z₁ hz₁ hfz
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp hz₁) fun n => by
      rw [Function.comp_apply, Real.norm_eq_abs]
      exact abs_uN_le_planAbs M hφ hF hβ.le _ (measurable_cont_plan hπ z₁) hfz n
  refine ⟨hIu, ?_⟩
  have hDCT := tendsto_integral_of_dominated_convergence _
    (fun n => (hmeas n).aestronglyMeasurable) hG hbound hlim
  have hrec : Tendsto (fun n => uN M s₀ π (n + 1)) atTop (𝓝 (ret M s₀ π 0 Fin.elim0 +
      M.β * ∫ z₁, uR M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2)) := by
    simp_rw [uN_succ M s₀ π (integrable_ret_of_planAbs M hφ hF hβ s₀ hπ hfin)]
    exact tendsto_const_nhds.add (hDCT.const_mul _)
  exact tendsto_nhds_unique ((tendsto_uN_abs M hφ hF hβ.le s₀ hπ hfin).comp
    (tendsto_add_atTop_nat 1)) hrec

/-- Assumption 9.3 implies absolute summability. -/
theorem planAbs_ne_top_of_bound (hβ : 0 ≤ M.β) (s₀ : X × Z) (π : Plan Y Z) {L : ℕ → ℝ}
    (hL : ∀ t h, |ret M s₀ π t h| ≤ L t) (hsum : Summable fun t => M.β ^ t * L t) :
    planAbs M s₀ π ≠ ⊤ := by
  have hL0 := bound_nonneg M s₀ π hL
  rw [planAbs_eq]
  refine ne_top_of_le_ne_top (ENNReal.ofReal_tsum_of_nonneg
    (fun t => mul_nonneg (pow_nonneg hβ t) (hL0 t)) hsum ▸ ENNReal.ofReal_ne_top) ?_
  refine ENNReal.tsum_le_tsum fun t => ?_
  have := ex_8_8a M.Q t
  rw [ENNReal.ofReal_mul (pow_nonneg hβ t)]
  gcongr
  calc ∫⁻ h, ENNReal.ofReal |ret M s₀ π t h| ∂hist M.Q t s₀.2
      ≤ ∫⁻ _h, ENNReal.ofReal (L t) ∂hist M.Q t s₀.2 :=
        lintegral_mono fun h => ENNReal.ofReal_le_ofReal (hL t h)
    _ = ENNReal.ofReal (L t) := by simp

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 9.4: optimal plans follow the policy correspondence almost surely

SLP §9.1, pp. 250–253, and Exercise 9.5b.

**Theorem 9.4** (`theorem_9_4`). Let `v*` be real-valued, measurable and solve the functional
equation, let the graph of `Γ` be measurable, and let `π*` be a feasible plan from `s₀` that
attains `v*(s₀)` and satisfies Assumption 9.3 — or, more generally, has
`Σ βᵗ ∫ |F(x_t, π_t, z_t)| dμᵗ < ∞` (`theorem_9_4_abs`). If `β > 0`, then `π*₀ ∈ G(s₀)` and
`π*_t(zᵗ) ∈ G(x_t, z_t)` for `μᵗ(z₀, ·)`-almost every `zᵗ`. The book's proof
(`theorem_9_4_step`): by Lemma 9.3, `v*(s₀) = F(s₀, π*₀) + β ∫ u[C(π*, z₁), s₁] Q(z₀, dz₁)`;
each continuation is worth at most `v*(s₁)`, and `F(s₀, π*₀) + β ∫ v*(s₁) dQ ≤ v*(s₀)` by (5);
so both inequalities are equalities, which gives `π*₀ ∈ G(s₀)` and (15): the continuation of `π*`
is optimal from `s₁` for `Q(z₀, ·)`-almost every `z₁`. Induction on `t` along continuations, with
the first-date split of `μᵗ⁺¹` (Exercise 8.8), gives the rest.

**Correction.** The book states the conclusion as: there is a plan `π^G` *generated by `G`* —
`π^G_t = g_t(x_t, z_t)` for measurable selections `g_t` — with `π^G = π*` almost everywhere.
That is false when `G` is not single-valued: an optimal plan may use the history in a way that no
plan generated by selections can copy (`theorem_9_4_counterexample`: i.i.d. fair coins, `F ≡ 0`,
`Γ ≡ {true, false}`, and `π*₂(z₁, z₂) = z₁`). The book's proof breaks where it defines `π^g` by a
single selection `g` and claims `π^g_t = π*_t` a.e.; what the argument does establish is that
`π*_t ∈ G(x_t, z_t)` almost everywhere, which is what `theorem_9_4` states. The hypothesis
`β > 0` is needed too: with `β = 0` only the first action matters.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (M : Model X Y Z) [IsMarkovKernel M.Q]

/-- The expected continuation value `∫ v[φ(x, y, z′), z′] Q(z, dz′)` is jointly measurable in
the state and the action. -/
theorem measurable_expV (hφ : Measurable M.φ) {v : X × Z → ℝ} (hv : Measurable v) :
    Measurable fun p : (X × Z) × Y => expV M v p.1 p.2 := by
  have hf : Measurable fun q : ((X × Z) × Y) × Z => v (M.φ (q.1.1.1, q.1.2, q.2), q.2) :=
    hv.comp ((hφ.comp (measurable_fst.fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd))).prodMk measurable_snd)
  exact (hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := M.Q.comap (fun p : (X × Z) × Y => p.1.2) measurable_fst.snd)).measurable

/-- If the graph of `Γ` is measurable and `v` is measurable, the graph of the policy
correspondence `G` is measurable. -/
theorem measurableSet_policy (hφ : Measurable M.φ) (hF : Measurable M.F)
    (hΓ : MeasurableSet {p : (X × Z) × Y | p.2 ∈ M.Γ p.1}) {v : X × Z → ℝ} (hv : Measurable v) :
    MeasurableSet {p : (X × Z) × Y | p.2 ∈ policy M v p.1} := by
  refine hΓ.inter (measurableSet_eq_fun (hv.comp measurable_fst) ?_)
  exact (hF.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))).add
    (measurable_const.mul (measurable_expV M hφ hv))

/-- **The first step of Theorem 9.4** (SLP (11a) and (15)): an optimal plan with
`Σ βᵗ ∫ |F| dμᵗ < ∞` has its first action in `G(s₀)`, and for `Q(z₀, ·)`-almost every `z₁` its
continuation is optimal from `s₁` and again absolutely summable. -/
theorem theorem_9_4_step (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    {v : X × Z → ℝ} (hFE : SolvesFE M v)
    (hIv : ∀ s, ∀ y ∈ M.Γ s, Integrable (fun z' => v (M.φ (s.1, y, z'), z')) (M.Q s.2))
    (hopt : ∀ s π, IsFeasible M s π → planValue M s π ≤ v s) {s : X × Z} {π : Plan Y Z}
    (hπ : IsFeasible M s π) (hfin : planAbs M s π ≠ ⊤) (hπopt : planValue M s π = v s) :
    π 0 Fin.elim0 ∈ policy M v s ∧
      ∀ᵐ z₁ ∂M.Q s.2, planValue M (start₁ M s π z₁) (cont π z₁) = v (start₁ M s π z₁) ∧
        planAbs M (start₁ M s π z₁) (cont π z₁) ≠ ⊤ := by
  obtain ⟨hIu, h2⟩ := lemma_9_3_abs M hφ hF hβ s hπ.1 hfin
  have hae := (ae_planAbs_cont M hφ hF hβ s hπ.1 hfin).2
  have hu : uR M s π = v s := by
    rw [planValue_eq_uR_abs M hφ hF hβ.le s hπ.1 hfin] at hπopt
    exact_mod_cast hπopt
  have hy₀ : π 0 Fin.elim0 ∈ M.Γ s := hπ.2 0 Fin.elim0
  have hcv : ∀ᵐ z₁ ∂M.Q s.2, planValue M (start₁ M s π z₁) (cont π z₁) =
      uR M (start₁ M s π z₁) (cont π z₁) := by
    filter_upwards [hae] with z₁ hz₁
    exact planValue_eq_uR_abs M hφ hF hβ.le _ (hπ.cont M z₁).1 hz₁
  have hle : ∀ᵐ z₁ ∂M.Q s.2, uR M (start₁ M s π z₁) (cont π z₁) ≤ v (start₁ M s π z₁) := by
    filter_upwards [hcv] with z₁ hz₁
    have := hopt _ _ (hπ.cont M z₁)
    rw [hz₁] at this
    exact_mod_cast this
  have hIv₀ : Integrable (fun z₁ => v (start₁ M s π z₁)) (M.Q s.2) := hIv s _ hy₀
  have hmono : ∫ z₁, uR M (start₁ M s π z₁) (cont π z₁) ∂M.Q s.2 ≤
      ∫ z₁, v (start₁ M s π z₁) ∂M.Q s.2 := integral_mono_ae hIu hIv₀ hle
  have hrhs : rhs M v s (π 0 Fin.elim0) =
      ret M s π 0 Fin.elim0 + M.β * ∫ z₁, v (start₁ M s π z₁) ∂M.Q s.2 := rfl
  have hFEle := hFE.le M s _ hy₀
  have heq : ∫ z₁, uR M (start₁ M s π z₁) (cont π z₁) ∂M.Q s.2 =
      ∫ z₁, v (start₁ M s π z₁) ∂M.Q s.2 := by
    refine le_antisymm hmono (le_of_mul_le_mul_left ?_ hβ)
    linarith
  refine ⟨⟨hy₀, ?_⟩, ?_⟩
  · rw [hrhs, ← heq, ← h2, hu]
  · filter_upwards [(integral_eq_iff_of_ae_le hIu hIv₀ hle).1 heq, hcv, hae]
      with z₁ hz₁ hc hf
    exact ⟨by rw [hc, hz₁], hf⟩

/-- The almost-sure part of Theorem 9.4, by induction on the date along continuations. -/
theorem theorem_9_4_ae (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (hΓ : MeasurableSet {p : (X × Z) × Y | p.2 ∈ M.Γ p.1}) {v : X × Z → ℝ} (hv : Measurable v)
    (hFE : SolvesFE M v)
    (hIv : ∀ s, ∀ y ∈ M.Γ s, Integrable (fun z' => v (M.φ (s.1, y, z'), z')) (M.Q s.2))
    (hopt : ∀ s π, IsFeasible M s π → planValue M s π ≤ v s) (t : ℕ) :
    ∀ (s : X × Z) (π : Plan Y Z), IsFeasible M s π → planAbs M s π ≠ ⊤ →
      planValue M s π = v s → ∀ᵐ h ∂hist M.Q t s.2, π t h ∈ policy M v (state M s π t h) := by
  induction t with
  | zero =>
    intro s π hπ hfin hπopt
    refine Eventually.of_forall fun h => ?_
    have : h = Fin.elim0 := funext fun i => i.elim0
    subst this
    exact (theorem_9_4_step M hφ hF hβ hFE hIv hopt hπ hfin hπopt).1
  | succ t ih =>
    intro s π hπ hfin hπopt
    have hae := (theorem_9_4_step M hφ hF hβ hFE hIv hopt hπ hfin hπopt).2
    have hG := measurableSet_policy M hφ hF hΓ hv
    rw [ae_iff]
    set B : Set (Fin (t + 1) → Z) :=
      {h | ¬π (t + 1) h ∈ policy M v (state M s π (t + 1) h)} with hBdef
    have hB : MeasurableSet B :=
      (hG.preimage ((measurable_state M hφ s hπ.1 (t + 1)).prodMk (hπ.1 (t + 1)))).compl
    rw [← lintegral_indicator_one hB, hist_succ_lintegral M.Q t s.2 (measurable_one.indicator hB)]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae] with z₁ hz₁
    have hπc := hπ.cont M z₁
    have hnull := ih _ _ hπc hz₁.2 hz₁.1
    rw [ae_iff] at hnull
    set B' : Set (Fin t → Z) := {h | ¬cont π z₁ t h ∈
      policy M v (state M (start₁ M s π z₁) (cont π z₁) t h)} with hB'def
    have hB' : MeasurableSet B' :=
      (hG.preimage ((measurable_state M hφ _ hπc.1 t).prodMk (hπc.1 t))).compl
    have hcons : ∀ h : Fin t → Z, (Fin.cons z₁ h : Fin (t + 1) → Z) ∈ B ↔ h ∈ B' := by
      intro h
      change (¬π (t + 1) (Fin.cons z₁ h) ∈
        policy M v (state M s π (t + 1) (Fin.cons z₁ h))) ↔ _
      rw [state_cons]
      rfl
    have hfun : ∀ h : Fin t → Z,
        B.indicator (1 : (Fin (t + 1) → Z) → ℝ≥0∞) (Fin.cons z₁ h) = B'.indicator 1 h := fun h => by
      by_cases hh : h ∈ B'
      · rw [indicator_of_mem ((hcons h).2 hh), indicator_of_mem hh]
        rfl
      · rw [indicator_of_notMem (fun h' => hh ((hcons h).1 h')), indicator_of_notMem hh]
    rw [lintegral_congr hfun, lintegral_indicator_one hB']
    exact hnull

/-- **Theorem 9.4** (corrected; see the module docstring), for plans with
`Σ βᵗ ∫ |F(x_t, π_t, z_t)| dμᵗ < ∞` (which Assumption 9.3 implies). Let `v*` be real-valued,
measurable and solve the functional equation (5′), with the integral in (5′) defined; let the
graph of `Γ` be measurable and `β > 0`. Then an optimal `π*` has `π*₀ ∈ G(s₀)` and
`π*_t ∈ G(x_t, z_t)` `μᵗ(z₀, ·)`-almost everywhere. -/
theorem theorem_9_4_abs (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (hΓ : MeasurableSet {p : (X × Z) × Y | p.2 ∈ M.Γ p.1}) {v : X × Z → ℝ} (hv : Measurable v)
    (hvstar : ∀ s, vStar M s = v s) (hFE : SolvesFE M v)
    (hIv : ∀ s, ∀ y ∈ M.Γ s, Integrable (fun z' => v (M.φ (s.1, y, z'), z')) (M.Q s.2))
    {s₀ : X × Z} {π : Plan Y Z} (hπ : IsFeasible M s₀ π) (hπopt : planValue M s₀ π = vStar M s₀)
    (hfin : planAbs M s₀ π ≠ ⊤) :
    π 0 Fin.elim0 ∈ policy M v s₀ ∧
      ∀ t, ∀ᵐ h ∂hist M.Q t s₀.2, π t h ∈ policy M v (state M s₀ π t h) := by
  have hopt : ∀ s π, IsFeasible M s π → planValue M s π ≤ v s := fun s π hπ => by
    rw [← hvstar]
    exact le_iSup₂ (f := fun π (_ : IsFeasible M s π) => planValue M s π) π hπ
  rw [hvstar] at hπopt
  exact ⟨(theorem_9_4_step M hφ hF hβ hFE hIv hopt hπ hfin hπopt).1,
    fun t => theorem_9_4_ae M hφ hF hβ hΓ hv hFE hIv hopt t s₀ π hπ hfin hπopt⟩

/-- **Theorem 9.4** (corrected) under Assumption 9.3: returns bounded by `L_t` with
`Σ βᵗ L_t < ∞`. -/
theorem theorem_9_4 (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (hΓ : MeasurableSet {p : (X × Z) × Y | p.2 ∈ M.Γ p.1}) {v : X × Z → ℝ} (hv : Measurable v)
    (hvstar : ∀ s, vStar M s = v s) (hFE : SolvesFE M v)
    (hIv : ∀ s, ∀ y ∈ M.Γ s, Integrable (fun z' => v (M.φ (s.1, y, z'), z')) (M.Q s.2))
    {s₀ : X × Z} {π : Plan Y Z} (hπ : IsFeasible M s₀ π) (hπopt : planValue M s₀ π = vStar M s₀)
    {L : ℕ → ℝ} (hL : ∀ t h, |ret M s₀ π t h| ≤ L t) (hsum : Summable fun t => M.β ^ t * L t) :
    π 0 Fin.elim0 ∈ policy M v s₀ ∧
      ∀ t, ∀ᵐ h ∂hist M.Q t s₀.2, π t h ∈ policy M v (state M s₀ π t h) :=
  theorem_9_4_abs M hφ hF hβ hΓ hv hvstar hFE hIv hπ hπopt
    (planAbs_ne_top_of_bound M hβ.le s₀ π hL hsum)

/-! ### The counterexample to "generated by `G`" -/

/-- If `Q(z, {z′}) > 0` for all `z, z′`, every history has positive probability. -/
theorem hist_singleton_ne_zero (Q : Kernel Z Z) [IsMarkovKernel Q] [MeasurableSingletonClass Z]
    (hQ : ∀ z z', Q z {z'} ≠ 0) (t : ℕ) : ∀ (z : Z) (h₀ : Fin t → Z), hist Q t z {h₀} ≠ 0 := by
  induction t with
  | zero =>
    intro z h₀
    have : h₀ = Fin.elim0 := funext fun i => i.elim0
    subst this
    simp [hist]
  | succ t ih =>
    intro z h₀
    have hm : MeasurableSet ({h₀} : Set (Fin (t + 1) → Z)) := measurableSet_singleton h₀
    rw [← lintegral_indicator_one hm, hist_succ_lintegral Q t z (measurable_one.indicator hm)]
    refine ne_of_gt (lt_of_lt_of_le ?_ (setLIntegral_le_lintegral {h₀ 0} _))
    rw [lintegral_singleton]
    refine ENNReal.mul_pos ?_ (hQ _ _)
    refine ne_of_gt ((pos_iff_ne_zero.2 (ih (h₀ 0) (Fin.tail h₀))).trans_le ?_)
    rw [← lintegral_indicator_one (measurableSet_singleton _)]
    refine lintegral_mono fun h => ?_
    by_cases hh : h = Fin.tail h₀
    · subst hh
      simp [Fin.cons_self_tail]
    · simp [hh]

/-- A fair coin on `Bool`. -/
noncomputable def coin : Measure Bool := (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

theorem isProbabilityMeasure_coin : IsProbabilityMeasure coin :=
  ⟨by simp [coin, ← two_mul, ENNReal.mul_inv_cancel]⟩

theorem coin_singleton_ne_zero (b : Bool) : coin {b} ≠ 0 := by
  cases b <;> simp [coin]

/-- The counterexample model: first formulation, `X = Z = Bool`, i.i.d. fair coins, `Γ ≡ Bool`,
`F ≡ 0`, `β = 1/2`. -/
noncomputable def coinModel : Model Bool Bool Bool :=
  Model.first (Kernel.const Bool coin) (fun _ => univ) (fun _ => 0) (1 / 2)

/-- The optimal plan `π*₀ = π*₁ = false`, `π*₂(z₁, z₂) = z₁`, `π*_t = false` for `t ≥ 3`. -/
def coinPlan : Plan Bool Bool
  | 2, h => h 0
  | _, _ => false

/-- **The counterexample to Theorem 9.4 as stated.** All hypotheses of the theorem hold: `v ≡ 0`
is `v*`, it solves the functional equation, `G ≡ Bool` has measurable selections, and `π*` is
feasible and optimal. But no plan generated by selections from `G` — indeed no plan of the form
`π_t = g_t(x_t, z_t)` for any functions `g_t` — agrees with `π*` almost everywhere. -/
theorem theorem_9_4_counterexample :
    (∀ s, vStar coinModel s = 0) ∧ SolvesFE coinModel (fun _ => 0) ∧
      (∀ s, policy coinModel (fun _ => 0) s = univ) ∧
      IsFeasible coinModel (false, false) coinPlan ∧
      planValue coinModel (false, false) coinPlan = vStar coinModel (false, false) ∧
      ¬∃ g : ℕ → Bool × Bool → Bool, ∀ t, ∀ᵐ h ∂hist coinModel.Q t false,
        genPlan coinModel (false, false) g t h = coinPlan t h := by
  have := isProbabilityMeasure_coin
  have hQ : IsMarkovKernel coinModel.Q := inferInstanceAs (IsMarkovKernel (Kernel.const Bool coin))
  have hval : ∀ s π, planValue coinModel s π = 0 := fun s π => by
    refine planValue_eq coinModel ?_
    have : ∀ n, uN coinModel s π n = 0 := fun n => by simp [uN, ret, coinModel, Model.first]
    simp_rw [this]
    exact tendsto_const_nhds
  have hfeas : ∀ s, IsFeasible coinModel s coinPlan := fun s =>
    ⟨fun t => measurable_of_countable _, fun t h => mem_univ _⟩
  have hstar : ∀ s, vStar coinModel s = 0 := fun s =>
    le_antisymm (iSup₂_le fun π _ => (hval s π).le)
      ((hval s coinPlan).symm.le.trans
        (le_iSup₂ (f := fun π (_ : IsFeasible coinModel s π) => planValue coinModel s π) _
          (hfeas s)))
  have hrhs : ∀ s y, rhs coinModel (fun _ => 0) s y = 0 := fun s y => by
    simp [rhs, expV, coinModel, Model.first]
  have hpol : ∀ s, policy coinModel (fun _ => 0) s = univ := fun s => by
    ext y
    exact ⟨fun _ => mem_univ _, fun _ => ⟨mem_univ y, (hrhs s y).symm⟩⟩
  refine ⟨hstar, fun s => ?_, hpol, hfeas _, by rw [hval, hstar], ?_⟩
  · simp only [hrhs]
    have : (fun _ : Bool => (0 : ℝ)) '' coinModel.Γ s = {0} :=
      (univ_nonempty : (univ : Set Bool).Nonempty).image_const 0
    rw [this]
    exact isLUB_singleton
  · rintro ⟨g, hg⟩
    have hQ1 : ∀ z z', coinModel.Q z {z'} ≠ 0 := fun _ z' => coin_singleton_ne_zero z'
    have hpt : ∀ t (h₀ : Fin t → Bool) (p : (Fin t → Bool) → Prop),
        (∀ᵐ h ∂hist coinModel.Q t false, p h) → p h₀ := fun t h₀ p hp => by
      by_contra hn
      refine hist_singleton_ne_zero coinModel.Q hQ1 t false h₀ (measure_mono_null ?_ (ae_iff.1 hp))
      intro h hh
      rw [mem_singleton_iff.1 hh]
      exact hn
    have h1 : ∀ b, g 1 (g 0 (false, false), b) = false := fun b =>
      hpt 1 ![b] _ (hg 1)
    have h2 : ∀ a b, g 2 (g 1 (g 0 (false, false), a), b) = a := fun a b =>
      hpt 2 ![a, b] _ (hg 2)
    have ht := h2 true false
    have hf := h2 false false
    rw [h1] at ht hf
    rw [ht] at hf
    exact Bool.noConfusion hf

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lemma 9.5: integration preserves continuity, monotonicity and concavity

SLP §9.2, pp. 260–262 and 268–269. The operator `(Mf)(w, z) = ∫ f(w, z′) Q(z, dz′)` (`mop`) on
functions of an endogenous variable `w` and the shock `z`. **Assumption 9.5** asks that `M` map
bounded continuous functions to continuous ones (`PreservesBC`). **Lemma 9.5** proves this in the
book's two cases:

* (a) `Z` countable with all subsets measurable (`lemma_9_5_discrete`: any `Z` with the discrete
  topology whose open sets are measurable; countability is not needed), by dominated convergence;
* (b) `Z` compact and `Q` Feller (`lemma_9_5_compact`): `|Mf(w′, z′) − Mf(w, z)|` is at most
  `sup_{z″} |f(w′, z″) − f(w, z″)| + |Mf(w, z′) − Mf(w, z)|`; the first term vanishes because
  `w ↦ f(w, ·)` is continuous into `C(Z)` with the sup norm (the book's uniform continuity on
  `D × Z`), the second by the Feller property.

The bound `|Mf| ≤ sup |f|` is `abs_mop_le`; preservation of (strict) monotonicity and concavity is
stated for any combination `θ f(w₀, z′) + (1 − θ) f(w₁, z′) ≤ f(w, z′)` (`lemma_9_5_comb`,
`lemma_9_5_comb_strict`, `lemma_9_5_mono`, `lemma_9_5_strictMono`), the strict versions by
Exercises 7.18 and 7.24 (`integral_lt_integral_of_lt`).

**Lemma 9.5′** (`lemma_9_5'`): with `φ` continuous on `D × Z`, where `D` is the projection of the
graph of `Γ` on `X × Y` (Assumption 9.17), `h(x, y, z) = ∫ f[φ(x, y, z′), z′] Q(z, dz′)` is
continuous on `D × Z`: apply Lemma 9.5 to `ψ(u, z′) = f[φ(u, z′), z′]` on `D × Z`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {W Z : Type*} [MeasurableSpace Z]

/-- The Markov operator on functions of `(w, z)`: `(Mf)(w, z) = ∫ f(w, z′) Q(z, dz′)`. -/
noncomputable def mop (Q : Kernel Z Z) (f : W × Z → ℝ) (p : W × Z) : ℝ := ∫ z', f (p.1, z') ∂Q p.2

/-- **Assumption 9.5** (in the form the proofs use): `M` maps the bounded continuous functions on
`W × Z` into continuous functions. -/
def PreservesBC (W : Type*) [TopologicalSpace W] [TopologicalSpace Z] (Q : Kernel Z Z) : Prop :=
  ∀ f : W × Z → ℝ, Continuous f → (∃ B, ∀ p, |f p| ≤ B) → Continuous (mop Q f)

/-- A bounded measurable function is integrable for a finite measure. -/
theorem integrable_of_abs_le {μ : Measure Z} [IsFiniteMeasure μ] {h : Z → ℝ} (hm : Measurable h)
    {B : ℝ} (hB : ∀ z, |h z| ≤ B) : Integrable h μ :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)

/-- **Exercises 7.18 and 7.24.** For a probability measure, `f < g` everywhere implies
`∫ f < ∫ g`. -/
theorem integral_lt_integral_of_lt {μ : Measure Z} [IsProbabilityMeasure μ] {f g : Z → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hlt : ∀ z, f z < g z) :
    ∫ z, f z ∂μ < ∫ z, g z ∂μ := by
  have hpos : 0 < ∫ z, (g z - f z) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun z => (sub_pos.2 (hlt z)).le) (hg.sub hf)]
    have : Function.support (fun z => g z - f z) = univ :=
      eq_univ_of_forall fun z => (sub_pos.2 (hlt z)).ne'
    rw [this, measure_univ]
    exact one_pos
  rw [integral_sub hg hf] at hpos
  linarith

variable [TopologicalSpace W] [TopologicalSpace Z] [OpensMeasurableSpace Z]

omit [TopologicalSpace W] [TopologicalSpace Z] [OpensMeasurableSpace Z] in
theorem abs_mop_le (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ} {B : ℝ}
    (hB : ∀ p, |f p| ≤ B) (p : W × Z) : |mop Q f p| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := B) (f := fun z' => f (p.1, z'))
    (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hB _)
  rw [mop]
  simpa [Real.norm_eq_abs, measureReal_def] using this

theorem integrable_section (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) (w : W) (z : Z) : Integrable (fun z' => f (w, z')) (Q z) :=
  integrable_of_abs_le (hf.comp (Continuous.prodMk_right w)).measurable fun _ => hB _

/-- **Lemma 9.5 (a).** If `Z` is discrete (with its subsets measurable), `M` maps bounded
continuous functions to continuous functions. -/
theorem lemma_9_5_discrete [FirstCountableTopology W] [DiscreteTopology Z] (Q : Kernel Z Z)
    [IsMarkovKernel Q] : PreservesBC W Q := by
  rintro f hf ⟨B, hB⟩
  refine continuous_prod_of_discrete_right.2 fun z => ?_
  exact continuous_of_dominated (bound := fun _ => B)
    (fun w => (integrable_section Q hf hB w z).aestronglyMeasurable)
    (fun w => Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hB _)
    (integrable_const B) (Eventually.of_forall fun z' => hf.comp (Continuous.prodMk_left z'))

/-- **Lemma 9.5 (b).** If `Z` is compact and `Q` has the Feller property, `M` maps bounded
continuous functions to continuous functions. -/
theorem lemma_9_5_compact [CompactSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (hQ : IsFeller Q) : PreservesBC W Q := by
  rintro f hf ⟨B, hB⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨w, z⟩
  set g : C(W, C(Z, ℝ)) := (ContinuousMap.mk f hf).curry with hgdef
  set k : Z → ℝ := markovOpR Q fun z' => f (w, z') with hkdef
  have hk : Continuous k :=
    hQ _ (hf.comp (Continuous.prodMk_right w)) ⟨B, fun z' => hB _⟩
  have hdist : Tendsto (fun p : W × Z => dist (g p.1) (g w)) (𝓝 (w, z)) (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 ((g.continuous.tendsto w).comp continuous_fst.continuousAt)
  have hA : Tendsto (fun p : W × Z => mop Q f p - k p.2) (𝓝 (w, z)) (𝓝 0) := by
    refine squeeze_zero_norm (fun p => ?_) hdist
    rw [mop, hkdef, markovOpR, ← integral_sub (integrable_section Q hf hB p.1 p.2)
      (integrable_section Q hf hB w p.2)]
    have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := dist (g p.1) (g w))
      (f := fun z' => f (p.1, z') - f (w, z')) (Eventually.of_forall fun z' => by
        rw [← dist_eq_norm]
        exact ContinuousMap.dist_apply_le_dist (f := g p.1) (g := g w) z')
    simpa [measureReal_def] using this
  have hB' : Tendsto (fun p : W × Z => k p.2) (𝓝 (w, z)) (𝓝 (k z)) :=
    (hk.tendsto z).comp continuous_snd.continuousAt
  have hsum := hA.add hB'
  rw [zero_add] at hsum
  have heq : (fun p : W × Z => mop Q f p - k p.2 + k p.2) = mop Q f :=
    funext fun p => sub_add_cancel _ _
  rw [heq] at hsum
  exact hsum

/-- **Lemma 9.5 (combinations).** If `θ f(w₀, z′) + (1 − θ) f(w₁, z′) ≤ f(w, z′)` for all `z′`,
then `θ (Mf)(w₀, z) + (1 − θ) (Mf)(w₁, z) ≤ (Mf)(w, z)`: concavity is preserved. -/
theorem lemma_9_5_comb (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) {w₀ w₁ w : W} {θ : ℝ}
    (hle : ∀ z', θ * f (w₀, z') + (1 - θ) * f (w₁, z') ≤ f (w, z')) (z : Z) :
    θ * mop Q f (w₀, z) + (1 - θ) * mop Q f (w₁, z) ≤ mop Q f (w, z) := by
  have h0 := integrable_section Q hf hB w₀ z
  have h1 := integrable_section Q hf hB w₁ z
  simp only [mop]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h0.const_mul θ)
    (h1.const_mul (1 - θ))]
  exact integral_mono ((h0.const_mul θ).add (h1.const_mul (1 - θ)))
    (integrable_section Q hf hB w z) hle

/-- **Lemma 9.5 (strict combinations).** Strict concavity is preserved. -/
theorem lemma_9_5_comb_strict (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ p, |f p| ≤ B) {w₀ w₁ w : W} {θ : ℝ}
    (hlt : ∀ z', θ * f (w₀, z') + (1 - θ) * f (w₁, z') < f (w, z')) (z : Z) :
    θ * mop Q f (w₀, z) + (1 - θ) * mop Q f (w₁, z) < mop Q f (w, z) := by
  have h0 := integrable_section Q hf hB w₀ z
  have h1 := integrable_section Q hf hB w₁ z
  simp only [mop]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h0.const_mul θ)
    (h1.const_mul (1 - θ))]
  exact integral_lt_integral_of_lt ((h0.const_mul θ).add (h1.const_mul (1 - θ)))
    (integrable_section Q hf hB w z) hlt

/-- **Lemma 9.5 (monotonicity).** If `f(·, z′)` is nondecreasing for every `z′`, so is
`(Mf)(·, z)`. -/
theorem lemma_9_5_mono [Preorder W] (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ p, |f p| ≤ B) (hmono : ∀ z', Monotone fun w => f (w, z'))
    (z : Z) : Monotone fun w => mop Q f (w, z) := fun _ _ hww' =>
  integral_mono (integrable_section Q hf hB _ z) (integrable_section Q hf hB _ z)
    fun z' => hmono z' hww'

/-- **Lemma 9.5 (strict monotonicity).** -/
theorem lemma_9_5_strictMono [Preorder W] (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ p, |f p| ≤ B)
    (hmono : ∀ z', StrictMono fun w => f (w, z')) (z : Z) :
    StrictMono fun w => mop Q f (w, z) := fun _ _ hww' =>
  integral_lt_integral_of_lt (integrable_section Q hf hB _ z) (integrable_section Q hf hB _ z)
    fun z' => hmono z' hww'

omit [OpensMeasurableSpace Z] in
/-- **Lemma 9.5′.** Let `D ⊆ X × Y` (the projection of the graph of `Γ`), let `φ` be continuous on
`D × Z` (Assumption 9.17), and let `Q` satisfy Assumption 9.5 on `D × Z`. For bounded continuous
`f` on `X × Z`, `h(x, y, z) = ∫ f[φ(x, y, z′), z′] Q(z, dz′)` is continuous on `D × Z`. -/
theorem lemma_9_5' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (D : Set (X × Y))
    {φ : X × Y × Z → X} (hφ : ContinuousOn (fun q : (X × Y) × Z => φ (q.1.1, q.1.2, q.2))
      (D ×ˢ univ)) (Q : Kernel Z Z) (hQ : PreservesBC D Q) {f : X × Z → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) :
    ContinuousOn (fun q : (X × Y) × Z => ∫ z', f (φ (q.1.1, q.1.2, z'), z') ∂Q q.2)
      (D ×ˢ univ) := by
  set ψ : D × Z → ℝ := fun q => f (φ (q.1.1.1, q.1.1.2, q.2), q.2) with hψdef
  have hφ' : Continuous fun q : D × Z => φ (q.1.1.1, q.1.1.2, q.2) := by
    refine hφ.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      fun q => ⟨q.1.2, mem_univ _⟩
  have hψ : Continuous ψ := hf.comp (hφ'.prodMk continuous_snd)
  have hM := hQ ψ hψ ⟨B, fun _ => hB _⟩
  rw [continuousOn_iff_continuous_domRestrict]
  have hmap : Continuous fun q : (D ×ˢ (univ : Set Z)) => ((⟨q.1.1, q.2.1⟩ : D), q.1.2) :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  exact (hM.comp hmap : _)

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bounded returns: Theorem 9.6 and Exercise 9.7b

SLP §9.2, pp. 259–264 and 268–270. The operator
`(Tf)(x, z) = sup_{y ∈ Γ(x, z)} {F(x, y, z) + β ∫ f[φ(x, y, z′), z′] Q(z, dz′)}` (`bellman`) on
the bounded continuous functions `C(S)`, `S = X × Z`, for the second formulation; the first
formulation is `φ(x, y, z′) = y` (`Model.first`), so one proof covers Theorem 9.6 and
Exercise 9.7b.

`BoundedDP` collects the hypotheses: Assumption 9.6 (`Γ` nonempty, compact-valued and
continuous), Assumption 9.7 (`F` bounded and continuous on the graph `A`, `0 < β < 1`),
Assumption 9.17 (`φ` continuous on `D × Z`), and the conclusion of Lemma 9.5′ — that
`(x, y, z) ↦ ∫ f[φ(x, y, z′), z′] Q(z, dz′)` is continuous on `D × Z` for bounded continuous `f`
(`ContExp`). It follows from Assumption 9.5 by Lemma 9.5′ (`contExp_of_preservesBC`), and in the
first formulation from Assumption 9.5 on `X × Z` by Lemma 9.5 (`contExp_first`). The metric
spaces `X`, `Y`, `Z` stand for the book's Borel sets in Euclidean spaces (Assumptions 9.4 and
9.16; convexity is used from Theorem 9.8 on).

* `bellman_mono`, `bellman_add_const`, `blackwell`: `T` is monotone and discounts, so it is a
  contraction of modulus `β` (Theorem 3.3).
* `ex_9_7b`: `T` has a unique fixed point `v ∈ C(S)`, `‖Tⁿv₀ − v‖ ≤ βⁿ‖v₀ − v‖`, and the policy
  correspondence `G` is nonempty, compact-valued and u.h.c.; `theorem_9_6` is the first
  formulation.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- `D = {(x, y) : y ∈ Γ(x, z) for some z}`, the domain of the law of motion. -/
def domD (M : Model X Y Z) : Set (X × Y) := {w | ∃ z, w.2 ∈ M.Γ (w.1, z)}

/-- The graph `A = {(x, y, z) : y ∈ Γ(x, z)}`. -/
def graphA (M : Model X Y Z) : Set (X × Y × Z) := {p | p.2.1 ∈ M.Γ (p.1, p.2.2)}

/-- The conclusion of Lemma 9.5′: `(x, y, z) ↦ ∫ f[φ(x, y, z′), z′] Q(z, dz′)` is continuous on
`D × Z` for every bounded continuous `f`. -/
def ContExp (M : Model X Y Z) : Prop :=
  ∀ f : X × Z → ℝ, Continuous f → (∃ B, ∀ p, |f p| ≤ B) →
    ContinuousOn (fun q : (X × Y) × Z => ∫ z', f (M.φ (q.1.1, q.1.2, z'), z') ∂M.Q q.2)
      (domD M ×ˢ univ)

/-- The hypotheses of §9.2: Assumptions 9.6, 9.7 and 9.17, and Lemma 9.5′. -/
structure BoundedDP (M : Model X Y Z) : Prop where
  nonempty : ∀ s, (M.Γ s).Nonempty
  compact : ∀ s, IsCompact (M.Γ s)
  lhc : ∀ s, IsLHC M.Γ s
  uhc : ∀ s, IsUHC M.Γ s
  contF : ContinuousOn M.F (graphA M)
  bddF : ∃ B, ∀ p ∈ graphA M, |M.F p| ≤ B
  β_pos : 0 < M.β
  β_lt : M.β < 1
  contφ : ContinuousOn (fun q : (X × Y) × Z => M.φ (q.1.1, q.1.2, q.2)) (domD M ×ˢ univ)
  contExp : ContExp M

omit [MetricSpace X] [MetricSpace Y] [MetricSpace Z] in
theorem mem_domD (M : Model X Y Z) {s : X × Z} {y : Y} (hy : y ∈ M.Γ s) : (s.1, y) ∈ domD M :=
  ⟨s.2, hy⟩

/-- **Lemma 9.5′ gives `ContExp`** under Assumptions 9.5 (on `D × Z`) and 9.17. -/
theorem contExp_of_preservesBC (M : Model X Y Z)
    (hφ : ContinuousOn (fun q : (X × Y) × Z => M.φ (q.1.1, q.1.2, q.2)) (domD M ×ˢ univ))
    (hQ : PreservesBC (domD M) M.Q) : ContExp M := fun _ hf ⟨_, hB⟩ =>
  lemma_9_5' (domD M) hφ M.Q hQ hf hB

/-- In the first formulation, `ContExp` follows from Assumption 9.5 on `X × Z` (Lemma 9.5). -/
theorem contExp_first (Q : Kernel Z Z) (Γ : X × Z → Set X) (F : X × X × Z → ℝ) (β : ℝ)
    (hQ : PreservesBC X Q) : ContExp (Model.first Q Γ F β) := fun f hf hB =>
  ((hQ f hf hB).comp (continuous_fst.snd.prodMk continuous_snd)).continuousOn

variable (M : Model X Y Z) [IsMarkovKernel M.Q] [OpensMeasurableSpace Z]

/-- The objective `(s, y) ↦ F(x, y, z) + β ∫ f[φ(x, y, z′), z′] Q(z, dz′)` on the graph. -/
noncomputable def objG (f : X × Z → ℝ) (p : (X × Z) × Y) : ℝ := rhs M f p.1 p.2

omit [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] in
theorem continuousOn_objG (h : BoundedDP M) (f : X × Z →ᵇ ℝ) :
    ContinuousOn (objG M f) (graph M.Γ) := by
  have hF : ContinuousOn (fun p : (X × Z) × Y => M.F (p.1.1, p.2, p.1.2)) (graph M.Γ) :=
    h.contF.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd)).continuousOn
      fun p hp => hp
  have hE : ContinuousOn (fun p : (X × Z) × Y => expV M f p.1 p.2) (graph M.Γ) :=
    (h.contExp f f.continuous ⟨‖f‖, fun p => f.norm_coe_le_norm p⟩).comp
      ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd).continuousOn
      fun p hp => ⟨mem_domD M hp, mem_univ _⟩
  exact hF.add (continuousOn_const.mul hE)

omit [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] in
/-- The integrand `z′ ↦ f[φ(x, y, z′), z′]` is continuous for `y ∈ Γ(x, z)`. -/
theorem continuous_integrand (h : BoundedDP M) (f : X × Z →ᵇ ℝ) {s : X × Z} {y : Y}
    (hy : y ∈ M.Γ s) : Continuous fun z' => f (M.φ (s.1, y, z'), z') := by
  have hφ : Continuous fun z' : Z => M.φ (s.1, y, z') :=
    h.contφ.comp_continuous (continuous_const.prodMk continuous_id)
      fun _ => ⟨mem_domD M hy, mem_univ _⟩
  exact f.continuous.comp (hφ.prodMk continuous_id)

theorem integrable_integrand (h : BoundedDP M) (f : X × Z →ᵇ ℝ) {s : X × Z} {y : Y}
    (hy : y ∈ M.Γ s) (z : Z) : Integrable (fun z' => f (M.φ (s.1, y, z'), z')) (M.Q z) :=
  integrable_of_abs_le (continuous_integrand M h f hy).measurable fun _ =>
    by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _

omit [MetricSpace Y] [OpensMeasurableSpace Z] in
theorem abs_expV_le (f : X × Z →ᵇ ℝ) (s : X × Z) (y : Y) : |expV M f s y| ≤ ‖f‖ := by
  have := norm_integral_le_of_norm_le_const (μ := M.Q s.2) (C := ‖f‖)
    (f := fun z' => f (M.φ (s.1, y, z'), z'))
    (Eventually.of_forall fun z' => f.norm_coe_le_norm _)
  rw [expV]
  simpa [Real.norm_eq_abs, measureReal_def] using this

omit [OpensMeasurableSpace Z] in
theorem bound_maxValueG (h : BoundedDP M) (f : X × Z →ᵇ ℝ) (s : X × Z) :
    ‖maxValue (objG M f) M.Γ s‖ ≤ h.bddF.choose + M.β * ‖f‖ := by
  obtain ⟨y, hy, hval, -⟩ := exists_argmax (continuousOn_objG M h f) (h.compact s) (h.nonempty s)
  rw [← hval, Real.norm_eq_abs, objG, rhs]
  refine (abs_add_le _ _).trans (add_le_add (h.bddF.choose_spec (s.1, y, s.2) hy) ?_)
  rw [abs_mul, abs_of_pos h.β_pos]
  exact mul_le_mul_of_nonneg_left (abs_expV_le M f s y) h.β_pos.le

/-- The operator `T` on `C(S)` (Exercise 9.7b; Theorem 9.6 when `φ(x, y, z′) = y`): `Tf` is
bounded and continuous by the Theorem of the Maximum. -/
noncomputable def bellman (h : BoundedDP M) (f : X × Z →ᵇ ℝ) : X × Z →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun s => maxValue (objG M f) M.Γ s)
    (theorem_3_6 (continuousOn_objG M h f) h.compact h.lhc h.uhc).1
    (h.bddF.choose + M.β * ‖f‖) (bound_maxValueG M h f)

omit [OpensMeasurableSpace Z] in
theorem bellman_apply (h : BoundedDP M) (f : X × Z →ᵇ ℝ) (s : X × Z) :
    bellman M h f s = maxValue (objG M f) M.Γ s := rfl

omit [OpensMeasurableSpace Z] in
/-- `Tf(s) = F(x, y, z) + β ∫ f[φ(x, y, z′), z′] Q(z, dz′)` at a maximizer `y`. -/
theorem exists_bellman_argmax (h : BoundedDP M) (f : X × Z →ᵇ ℝ) (s : X × Z) :
    ∃ y ∈ M.Γ s, bellman M h f s = rhs M f s y ∧ ∀ y' ∈ M.Γ s, rhs M f s y' ≤ bellman M h f s := by
  obtain ⟨y, hy, hval, hmax⟩ := exists_argmax (continuousOn_objG M h f) (h.compact s)
    (h.nonempty s)
  exact ⟨y, hy, hval.symm, fun y' hy' => (hmax y' hy').trans_eq hval⟩

/-- `T` is monotone (Theorem 3.3a). -/
theorem bellman_mono (h : BoundedDP M) {f g : X × Z →ᵇ ℝ} (hfg : f ≤ g) :
    bellman M h f ≤ bellman M h g := fun s => by
  obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M h f s
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M h g s
  change bellman M h f s ≤ bellman M h g s
  rw [hval]
  refine le_trans ?_ (hmax y hy)
  have hE : expV M f s y ≤ expV M g s y :=
    integral_mono (integrable_integrand M h f hy _) (integrable_integrand M h g hy _)
      fun z' => hfg _
  simp only [rhs]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hE h.β_pos.le)

theorem expV_add_const (h : BoundedDP M) (f : X × Z →ᵇ ℝ) (a : ℝ) {s : X × Z} {y : Y}
    (hy : y ∈ M.Γ s) : expV M ⇑(f + const (X × Z) a) s y = expV M f s y + a := by
  have heq : ∀ z', (f + const (X × Z) a) (M.φ (s.1, y, z'), z') =
      f (M.φ (s.1, y, z'), z') + a := fun _ => rfl
  simp only [expV, heq]
  rw [integral_add (integrable_integrand M h f hy _) (integrable_const a)]
  simp

/-- `T(f + a) = Tf + βa` (discounting, Theorem 3.3b, with equality). -/
theorem bellman_add_const (h : BoundedDP M) (f : X × Z →ᵇ ℝ) (a : ℝ) :
    bellman M h (f + const (X × Z) a) = bellman M h f + const (X × Z) (M.β * a) := by
  ext s
  obtain ⟨y, hy, hval, hmax⟩ := exists_bellman_argmax M h f s
  obtain ⟨y', hy', hval', hmax'⟩ := exists_bellman_argmax M h (f + const (X × Z) a) s
  simp only [BoundedContinuousFunction.add_apply, const_apply]
  have e1 := expV_add_const M h f a hy
  have e2 := expV_add_const M h f a hy'
  have i1 := hmax y' hy'
  have i2 := hmax' y hy
  simp only [rhs] at hval hval' i1 i2
  rw [e1] at i2
  rw [e2] at hval'
  refine le_antisymm ?_ ?_
  · rw [hval']; nlinarith
  · rw [hval]; nlinarith

/-- **Blackwell's sufficient conditions** (Theorem 3.3) on the bounded continuous functions on
any topological space. -/
theorem blackwell {S : Type*} [TopologicalSpace S] {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)} {β : ℝ}
    (hβ : 0 ≤ β) (hmono : ∀ f g, f ≤ g → T f ≤ T g)
    (hdisc : ∀ f a, 0 ≤ a → T (f + const S a) ≤ T f + const S (β * a)) (f g : S →ᵇ ℝ) :
    dist (T f) (T g) ≤ β * dist f g := by
  have hle : ∀ f g : S →ᵇ ℝ, f ≤ g + const S (dist f g) := fun f g x => by
    change f x ≤ (g + const S (dist f g)) x
    rw [BoundedContinuousFunction.add_apply, const_apply]
    have := dist_coe_le_dist (f := f) (g := g) x
    rw [Real.dist_eq] at this
    linarith [le_abs_self (f x - g x)]
  have h1 : ∀ f g : S →ᵇ ℝ, ∀ x, T f x ≤ T g x + β * dist f g := fun f g x => by
    have : T f x ≤ (T g + const S (β * dist f g)) x :=
      (hmono _ _ (hle f g)).trans (hdisc g _ dist_nonneg) x
    rwa [BoundedContinuousFunction.add_apply, const_apply] at this
  refine (dist_le (mul_nonneg hβ dist_nonneg)).2 fun x => ?_
  rw [Real.dist_eq, abs_le]
  have a := h1 f g x
  have b := h1 g f x
  rw [dist_comm] at b
  constructor <;> linarith

/-- `T` is a contraction of modulus `β`. -/
theorem bellman_contraction (h : BoundedDP M) : IsContraction (bellman M h) M.β :=
  ⟨h.β_pos, h.β_lt, blackwell h.β_pos.le (fun _ _ => bellman_mono M h)
    (fun f a _ => (bellman_add_const M h f a).le)⟩

omit [OpensMeasurableSpace Z] in
/-- At a fixed point, the policy correspondence `G` is the argmax correspondence of `T`. -/
theorem policy_eq_argmax (h : BoundedDP M) {v : X × Z →ᵇ ℝ} (hv : bellman M h v = v) :
    policy M v = argmax (objG M v) M.Γ := by
  funext s
  ext y
  change y ∈ M.Γ s ∧ v s = rhs M v s y ↔ y ∈ M.Γ s ∧ objG M v (s, y) = maxValue (objG M v) M.Γ s
  rw [← bellman_apply M h, hv, objG, eq_comm]

/-- **Exercise 9.7b** (Theorem 9.6 for the second formulation). `T : C(S) → C(S)` has a unique
fixed point `v`, `‖Tⁿv₀ − v‖ ≤ βⁿ‖v₀ − v‖`, and the policy correspondence `G` is nonempty,
compact-valued and u.h.c. -/
theorem ex_9_7b (h : BoundedDP M) :
    ∃ v : X × Z →ᵇ ℝ, bellman M h v = v ∧ (∀ w, bellman M h w = w → w = v) ∧
      (∀ v₀ (n : ℕ), dist ((bellman M h)^[n] v₀) v ≤ M.β ^ n * dist v₀ v) ∧
      ∀ s, (policy M v s).Nonempty ∧ IsCompact (policy M v s) ∧ IsUHC (policy M v) s := by
  obtain ⟨v, hv, huniq, hrate⟩ := theorem_3_2 (bellman_contraction M h)
  refine ⟨v, hv, huniq, hrate, ?_⟩
  rw [policy_eq_argmax M h hv]
  exact (theorem_3_6 (continuousOn_objG M h v) h.compact h.lhc h.uhc).2

/-- **Theorem 9.6** (first formulation). Under Assumptions 9.4–9.7 — with Assumption 9.5 in the
form `M : C(X × Z) → C(X × Z)` (Lemma 9.5) — `T` has a unique fixed point `v ∈ C(S)`,
`‖Tⁿv₀ − v‖ ≤ βⁿ‖v₀ − v‖`, and `G` is nonempty, compact-valued and u.h.c. -/
theorem theorem_9_6 (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : X × Z → Set X) (F : X × X × Z → ℝ)
    (β : ℝ) (hΓne : ∀ s, (Γ s).Nonempty) (hΓc : ∀ s, IsCompact (Γ s)) (hΓl : ∀ s, IsLHC Γ s)
    (hΓu : ∀ s, IsUHC Γ s) (hF : ContinuousOn F (graphA (Model.first Q Γ F β)))
    (hFb : ∃ B, ∀ p ∈ graphA (Model.first Q Γ F β), |F p| ≤ B) (hβ : 0 < β) (hβ1 : β < 1)
    (hQ : PreservesBC X Q) :
    ∃ h : BoundedDP (Model.first Q Γ F β), ∃ v : X × Z →ᵇ ℝ,
      bellman (Model.first Q Γ F β) h v = v ∧
      (∀ w, bellman (Model.first Q Γ F β) h w = w → w = v) ∧
      (∀ v₀ (n : ℕ), dist ((bellman (Model.first Q Γ F β) h)^[n] v₀) v ≤ β ^ n * dist v₀ v) ∧
      ∀ s, (policy (Model.first Q Γ F β) v s).Nonempty ∧
        IsCompact (policy (Model.first Q Γ F β) v s) ∧
        IsUHC (policy (Model.first Q Γ F β) v) s := by
  have h : BoundedDP (Model.first Q Γ F β) :=
    ⟨hΓne, hΓc, hΓl, hΓu, hF, hFb, hβ, hβ1, continuous_fst.snd.continuousOn,
      contExp_first Q Γ F β hQ⟩
  exact ⟨h, ex_9_7b (Model.first Q Γ F β) h⟩

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bounded returns: the principle of optimality applies (Exercises 9.6 and 9.7a)

SLP §9.2, pp. 263–264 and 269.

* **Exercises 9.6 and 9.7a** (`ex_9_7a`): under the hypotheses of §9.2, Assumptions 9.1′–9.3′
  hold: `Γ` is nonempty with a closed (so measurable) graph; it has a measurable selection when
  the actions lie in a subset of `ℝᵐ` (`exists_measurableSelection`, Theorem 7.6); the returns,
  modified off the graph `A` to be measurable, agree with `F` on `A`; and the returns of every
  feasible plan are bounded by `B = sup_A |F|`, so Assumption 9.3′ holds with `L_t = B`.
* `bounded_vStar` (the conclusion the book draws, p. 264): the fixed point `v` of `T` is the
  supremum function `v*`, and every plan generated by measurable selections from `G` is optimal
  (Theorem 9.2 via Exercise 9.4).
* `bounded_theorem_9_4`: every optimal plan follows `G` almost surely (Theorem 9.4, corrected).

The law of motion is a total function `φ : X × Y × Z → X`; the book's `φ : D × Z → X` is
measurable on `D × Z` (Exercise 7.10), and we assume the total function measurable.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- A u.h.c. correspondence between metric spaces has a closed graph. -/
theorem isClosed_graph_of_uhc {S T : Type*} [MetricSpace S] [MetricSpace T] {Γ : S → Set T}
    (hu : ∀ s, IsUHC Γ s) : IsClosed (graph Γ) := by
  refine IsSeqClosed.isClosed fun ps p hps hlim => ?_
  have h1 : Tendsto (fun n => (ps n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hlim
  have h2 : Tendsto (fun n => (ps n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hlim
  obtain ⟨y, hy, φ, hφ, hφlim⟩ := (hu p.1).2 _ h1 _ hps
  have : y = p.2 := tendsto_nhds_unique hφlim (h2.comp hφ.tendsto_atTop)
  change p.2 ∈ Γ p.1
  rw [← this]
  exact hy

/-- The image of a u.h.c. correspondence into a subtype is u.h.c. -/
theorem isUHC_image_val {S E : Type*} [MetricSpace S] [MetricSpace E] {T : Set E}
    {G : S → Set T} {s : S} (h : IsUHC G s) : IsUHC (fun s => Subtype.val '' G s) s := by
  refine ⟨h.1.image _, fun xs hxs ys hys => ?_⟩
  choose zs hzs hzv using hys
  obtain ⟨y, hy, φ, hφ, hlim⟩ := h.2 xs hxs zs hzs
  refine ⟨y, ⟨y, hy, rfl⟩, φ, hφ, ?_⟩
  refine ((continuous_subtype_val.tendsto y).comp hlim).congr fun n => ?_
  simp [Function.comp, hzv]

/-- **Theorem 7.6 for correspondences into `T ⊆ ℝᵐ`.** A nonempty compact-valued u.h.c.
correspondence has a measurable selection. -/
theorem exists_measurableSelection {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    {m : ℕ} {T : Set (Fin m → ℝ)} {G : S → Set T} (hu : ∀ s, IsUHC G s)
    (hc : ∀ s, IsCompact (G s)) : ∃ g : S → T, Measurable g ∧ ∀ s, g s ∈ G s := by
  obtain ⟨g, hg, hmem⟩ := theorem_7_6_subtype (T := T) (Γ := fun s => Subtype.val '' G s)
    (fun s => isUHC_image_val (hu s)) (fun s => (hc s).image continuous_subtype_val)
    (fun s => by rintro _ ⟨y, -, rfl⟩; exact y.2)
  refine ⟨g, hg, fun s => ?_⟩
  obtain ⟨y, hy, hyv⟩ := hmem s
  have : y = g s := Subtype.ext hyv
  rw [← this]
  exact hy

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem isClosed_graphA (M : Model X Y Z) (hu : ∀ s, IsUHC M.Γ s) : IsClosed (graphA M) :=
  (isClosed_graph_of_uhc hu).preimage
    ((continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst)

omit [MetricSpace X] [MetricSpace Y] [MetricSpace Z] in
/-- Along a feasible plan, the returns are values of `F` on the graph `A`. -/
theorem ret_mem_graphA (M : Model X Y Z) {s₀ : X × Z} {π : Plan Y Z} (hπ : IsFeasible M s₀ π)
    (t : ℕ) (h : Fin t → Z) :
    ((state M s₀ π t h).1, π t h, (state M s₀ π t h).2) ∈ graphA M :=
  hπ.2 t h

open Classical in
/-- **Exercises 9.6 and 9.7a.** Under the hypotheses of §9.2, Assumptions 9.1′–9.3′ hold: `Γ` is
nonempty with a closed, hence measurable, graph; the returns modified off `A` are measurable and
agree with `F` on `A`; and along every feasible plan the returns are bounded by a constant `B`,
with `Σ βᵗ B < ∞` (Assumption 9.3′ with `L_t = B`). -/
theorem ex_9_7a (M : Model X Y Z) (h : BoundedDP M) [OpensMeasurableSpace ((X × Z) × Y)]
    [OpensMeasurableSpace (X × Y × Z)] :
    (∀ s, (M.Γ s).Nonempty) ∧ IsClosed (graph M.Γ) ∧ MeasurableSet (graph M.Γ) ∧
      Measurable ((graphA M).piecewise M.F 0) ∧
      (∀ p ∈ graphA M, (graphA M).piecewise M.F 0 p = M.F p) ∧
      ∃ B, ∀ s₀ π, IsFeasible M s₀ π →
        (∀ t h, |ret M s₀ π t h| ≤ B) ∧ Summable fun t => M.β ^ t * B := by
  have hcl := isClosed_graph_of_uhc h.uhc
  refine ⟨h.nonempty, hcl, hcl.measurableSet, ?_, fun p hp => piecewise_eq_of_mem _ _ _ hp,
    h.bddF.choose, fun s₀ π hπ => ⟨fun t h' => h.bddF.choose_spec _ (ret_mem_graphA M hπ t h'),
      (summable_geometric_of_lt_one h.β_pos.le h.β_lt).mul_right _⟩⟩
  exact h.contF.measurable_piecewise continuousOn_const
    (isClosed_graphA M h.uhc).measurableSet

variable (M : Model X Y Z) [IsMarkovKernel M.Q] [OpensMeasurableSpace Z]

omit [OpensMeasurableSpace Z] in
/-- The fixed point of `T` solves the functional equation (5′). -/
theorem solvesFE_of_fixed (h : BoundedDP M) {v : X × Z →ᵇ ℝ} (hv : bellman M h v = v) :
    SolvesFE M v := fun s => by
  obtain ⟨y, hy, hval, hmax⟩ := exists_bellman_argmax M h v s
  rw [hv] at hval hmax
  refine IsGreatest.isLUB ⟨⟨y, hy, hval.symm⟩, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  exact hmax y' hy'

omit [OpensMeasurableSpace Z] in
/-- **The fixed point is the supremum function** (p. 264, from Exercise 9.6 and Theorem 9.2).
Every feasible plan is worth at most `v(s₀)`, the plan generated by measurable selections from
`G` attains `v(s₀)`, and `v*(s₀) = v(s₀)`. -/
theorem bounded_vStar (h : BoundedDP M) [OpensMeasurableSpace (X × Z)] (hφm : Measurable M.φ)
    (hFm : Measurable M.F) {v : X × Z →ᵇ ℝ} (hv : bellman M h v = v) {g : ℕ → X × Z → Y}
    (hg : ∀ t, Measurable (g t)) (hgG : ∀ t s, g t s ∈ policy M v s) (s₀ : X × Z) :
    (∀ π, IsFeasible M s₀ π → planValue M s₀ π ≤ v s₀) ∧
      planValue M s₀ (genPlan M s₀ g) = v s₀ ∧ vStar M s₀ = v s₀ := by
  set B := h.bddF.choose
  have hB : ∀ π, IsFeasible M s₀ π → ∀ t h', |ret M s₀ π t h'| ≤ B := fun π hπ t h' =>
    h.bddF.choose_spec _ (ret_mem_graphA M hπ t h')
  have hsum : Summable fun t => M.β ^ t * B :=
    (summable_geometric_of_lt_one h.β_pos.le h.β_lt).mul_right _
  have hvm : Measurable fun s : X × Z => v s := v.continuous.measurable
  have hvB : ∀ s, |v s| ≤ ‖v‖ := fun s => by rw [← Real.norm_eq_abs]; exact v.norm_coe_le_norm s
  refine ex_9_4 M hφm h.β_pos.le (solvesFE_of_fixed M h hv) s₀ (fun π hπ t => ⟨?_, ?_⟩)
    (fun π hπ => ⟨_, (continuous_coe_real_ereal.tendsto _).comp
      (tendsto_uN M h.β_pos.le s₀ π (hB π hπ) hsum)⟩) (fun π hπ => ?_) hg hgG
  · exact integrable_ret_of_bound M hφm hFm s₀ hπ.1 (hB π hπ) t
  · have := ex_8_8a M.Q t
    exact integrable_of_abs_le (hvm.comp (measurable_state M hφm s₀ hπ.1 t)) fun _ => hvB _
  · refine squeeze_zero_norm (a := fun t => M.β ^ t * ‖v‖) (fun t => ?_) ?_
    · have := ex_8_8a M.Q t
      rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos h.β_pos]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h.β_pos.le t)
      have := norm_integral_le_of_norm_le_const (μ := hist M.Q t s₀.2) (C := ‖v‖)
        (f := fun h' => v (state M s₀ π t h'))
        (Eventually.of_forall fun h' => v.norm_coe_le_norm _)
      simpa [measureReal_def] using this
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.β_pos.le h.β_lt).mul_const ‖v‖

/-- **Theorem 9.4 under the hypotheses of §9.2** (corrected form): if `v = v*` (e.g. by
`bounded_vStar`), every optimal plan's actions lie in `G` almost surely. -/
theorem bounded_theorem_9_4 (h : BoundedDP M) [OpensMeasurableSpace (X × Z)]
    [OpensMeasurableSpace ((X × Z) × Y)] (hφm : Measurable M.φ) (hFm : Measurable M.F)
    {v : X × Z →ᵇ ℝ} (hv : bellman M h v = v) (hvstar : ∀ s, vStar M s = v s) {s₀ : X × Z}
    {π : Plan Y Z} (hπ : IsFeasible M s₀ π) (hπopt : planValue M s₀ π = vStar M s₀) :
    π 0 Fin.elim0 ∈ policy M v s₀ ∧
      ∀ t, ∀ᵐ h' ∂hist M.Q t s₀.2, π t h' ∈ policy M v (state M s₀ π t h') :=
  theorem_9_4 M hφm hFm h.β_pos (isClosed_graph_of_uhc h.uhc).measurableSet
    v.continuous.measurable hvstar (solvesFE_of_fixed M h hv)
    (fun _ _ hy => integrable_integrand M h v hy _) hπ hπopt
    (fun t h' => h.bddF.choose_spec _ (ret_mem_graphA M hπ t h'))
    ((summable_geometric_of_lt_one h.β_pos.le h.β_lt).mul_right _)

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bounded returns: monotonicity (Theorems 9.7 and 9.11, Exercises 9.7c and 9.7g)

SLP §9.2, pp. 264–270. Each proof is the book's: by Corollary 1 to the Contraction Mapping
Theorem, it suffices that `T` maps the closed set of functions nondecreasing in the relevant
argument into the strictly increasing ones. The order on `X` (or `Z`) is any partial order —
the book's `ℝˡ` with the coordinatewise order is a special case.

* **Exercise 9.7c** (`ex_9_7c`): with Assumption 9.8 (`F(·, y, z)` strictly increasing),
  Assumption 9.9 (`Γ(·, z)` increasing) and `φ(·, y, z′)` nondecreasing, `v(·, z)` is strictly
  increasing. **Theorem 9.7** (`theorem_9_7`) is the first formulation.
* **Exercise 9.7g** (`ex_9_7g`): with Assumptions 9.13–9.15 (`F(x, y, ·)` strictly increasing,
  `Γ(x, ·)` increasing, `Q` monotone), `v(x, ·)` is strictly increasing. **Correction:** in the
  second formulation the integrand `f[φ(x, y, z′), z′]` must be nondecreasing in `z′`, which needs
  `φ(x, y, ·)` nondecreasing (the solutions manual adds this) *and* `f` nondecreasing in `x`; we
  add the hypotheses of part (c), so that `T` maps the functions nondecreasing in both `x` and
  `z` into those strictly increasing in both. **Theorem 9.11** (`theorem_9_11`) is the first
  formulation, where `φ(x, y, z′) = y` and only monotonicity in `z` is needed.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (M : Model X Y Z) [IsMarkovKernel M.Q] [OpensMeasurableSpace Z]

/-- A set of bounded continuous functions cut out by pointwise inequalities is closed. -/
theorem isClosed_pointwise_le {S ι : Type*} [TopologicalSpace S] (a b : ι → S) :
    IsClosed {f : S →ᵇ ℝ | ∀ i, f (a i) ≤ f (b i)} := by
  have : {f : S →ᵇ ℝ | ∀ i, f (a i) ≤ f (b i)} = ⋂ i, {f : S →ᵇ ℝ | f (a i) ≤ f (b i)} := by
    ext f; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (continuous_eval_const _) (continuous_eval_const _)

/-- `T` maps functions nondecreasing in `x` to functions strictly increasing in `x`. -/
theorem bellman_strictMono_x [PartialOrder X] (h : BoundedDP M)
    (h98 : ∀ x x' y z, x < x' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → M.Γ (x, z) ⊆ M.Γ (x', z))
    (hφx : ∀ y z', Monotone fun x => M.φ (x, y, z')) {f : X × Z →ᵇ ℝ}
    (hf : ∀ z, Monotone fun x => f (x, z)) (z : Z) :
    StrictMono fun x => bellman M h f (x, z) := by
  intro x x' hxx'
  obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M h f (x, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M h f (x', z)
  have hy' : y ∈ M.Γ (x', z) := h99 x x' z hxx'.le hy
  have hE : expV M f (x, z) y ≤ expV M f (x', z) y :=
    integral_mono (integrable_integrand M h f hy _) (integrable_integrand M h f hy' _)
      fun z' => hf z' (hφx y z' hxx'.le)
  change bellman M h f (x, z) < bellman M h f (x', z)
  rw [hval]
  refine lt_of_lt_of_le ?_ (hmax y hy')
  simp only [rhs]
  exact add_lt_add_of_lt_of_le (h98 x x' y z hxx' hy)
    (mul_le_mul_of_nonneg_left hE h.β_pos.le)

/-- **Exercise 9.7c.** Under §9.2's hypotheses, Assumptions 9.8 and 9.9, and `φ(·, y, z′)`
nondecreasing, the fixed point `v(·, z)` is strictly increasing for each `z`. -/
theorem ex_9_7c [PartialOrder X] (h : BoundedDP M)
    (h98 : ∀ x x' y z, x < x' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → M.Γ (x, z) ⊆ M.Γ (x', z))
    (hφx : ∀ y z', Monotone fun x => M.φ (x, y, z')) {v : X × Z →ᵇ ℝ}
    (hv : bellman M h v = v) (z : Z) : StrictMono fun x => v (x, z) := by
  set C' : Set (X × Z →ᵇ ℝ) := {f | ∀ z, Monotone fun x => f (x, z)}
  have hclosed : IsClosed C' := by
    have := isClosed_pointwise_le (S := X × Z) (ι := {q : X × X × Z // q.1 ≤ q.2.1})
      (fun q => (q.1.1, q.1.2.2)) (fun q => (q.1.2.1, q.1.2.2))
    convert this using 1
    ext f
    exact ⟨fun hf q => hf q.1.2.2 q.2, fun hf z x x' hxx' => hf ⟨(x, x', z), hxx'⟩⟩
  have hmaps := fun (f : X × Z →ᵇ ℝ) (hf : f ∈ C') =>
    bellman_strictMono_x M h h98 h99 hφx hf
  have hv' := (corollary_1 (S' := C') (S'' := {f | ∀ z, StrictMono fun x => f (x, z)})
    (bellman_contraction M h) hv ⟨0, fun _ _ _ _ => le_rfl⟩ hclosed
    (fun f hf z => (hmaps f hf z).monotone) hmaps).2
  exact hv' z

/-- **Theorem 9.7** (first formulation). Under Assumptions 9.4–9.9, `v(·, z)` is strictly
increasing for each `z`. -/
theorem theorem_9_7 [PartialOrder X] (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : X × Z → Set X)
    (F : X × X × Z → ℝ) (β : ℝ) (h : BoundedDP (Model.first Q Γ F β))
    (h98 : ∀ x x' y z, x < x' → y ∈ Γ (x, z) → F (x, y, z) < F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → Γ (x, z) ⊆ Γ (x', z)) {v : X × Z →ᵇ ℝ}
    (hv : bellman (Model.first Q Γ F β) h v = v) (z : Z) : StrictMono fun x => v (x, z) :=
  ex_9_7c (Model.first Q Γ F β) h h98 h99 (fun _ _ => monotone_const) hv z

omit [IsMarkovKernel M.Q] in
/-- With `Q` monotone, the expected continuation value is nondecreasing in `z` when the integrand
is nondecreasing in `z′`. -/
theorem expV_mono_z [Preorder Z] (h : BoundedDP M) (hQ : IsMonotoneTF M.Q) (f : X × Z →ᵇ ℝ)
    {x : X} {y : Y} {z₁ z₂ : Z} (hy : y ∈ M.Γ (x, z₁)) (hz : z₁ ≤ z₂)
    (hk : Monotone fun z' => f (M.φ (x, y, z'), z')) :
    expV M f (x, z₁) y ≤ expV M f (x, z₂) y :=
  hQ _ (continuous_integrand M h f hy).measurable ⟨‖f‖, fun _ => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _⟩ hk hz

/-- `T` maps functions whose integrands are nondecreasing in `z′` to functions strictly
increasing in `z`. -/
theorem bellman_strictMono_z [Preorder Z] (h : BoundedDP M)
    (h913 : ∀ x y z z', z < z' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x, y, z'))
    (h914 : ∀ x z z', z ≤ z' → M.Γ (x, z) ⊆ M.Γ (x, z')) (hQ : IsMonotoneTF M.Q)
    {f : X × Z →ᵇ ℝ} (hk : ∀ x y, Monotone fun z' => f (M.φ (x, y, z'), z')) (x : X) :
    StrictMono fun z => bellman M h f (x, z) := by
  intro z z' hzz'
  obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M h f (x, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M h f (x, z')
  have hy' : y ∈ M.Γ (x, z') := h914 x z z' hzz'.le hy
  change bellman M h f (x, z) < bellman M h f (x, z')
  rw [hval]
  refine lt_of_lt_of_le ?_ (hmax y hy')
  simp only [rhs]
  exact add_lt_add_of_lt_of_le (h913 x y z z' hzz' hy)
    (mul_le_mul_of_nonneg_left (expV_mono_z M h hQ f hy hzz'.le (hk x y)) h.β_pos.le)

/-- **Theorem 9.11** (first formulation). Under Assumptions 9.4–9.7 and 9.13–9.15, `v(x, ·)` is
strictly increasing for each `x`. -/
theorem theorem_9_11 [PartialOrder Z] (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : X × Z → Set X)
    (F : X × X × Z → ℝ) (β : ℝ) (h : BoundedDP (Model.first Q Γ F β))
    (h913 : ∀ x y z z', z < z' → y ∈ Γ (x, z) → F (x, y, z) < F (x, y, z'))
    (h914 : ∀ x z z', z ≤ z' → Γ (x, z) ⊆ Γ (x, z')) (hQ : IsMonotoneTF Q) {v : X × Z →ᵇ ℝ}
    (hv : bellman (Model.first Q Γ F β) h v = v) (x : X) : StrictMono fun z => v (x, z) := by
  set M := Model.first Q Γ F β
  set C' : Set (X × Z →ᵇ ℝ) := {f | ∀ x, Monotone fun z => f (x, z)}
  have hclosed : IsClosed C' := by
    have := isClosed_pointwise_le (S := X × Z) (ι := {q : X × Z × Z // q.2.1 ≤ q.2.2})
      (fun q => (q.1.1, q.1.2.1)) (fun q => (q.1.1, q.1.2.2))
    convert this using 1
    ext f
    exact ⟨fun hf q => hf q.1.1 q.2, fun hf x z z' hzz' => hf ⟨(x, z, z'), hzz'⟩⟩
  have hmaps := fun (f : X × Z →ᵇ ℝ) (hf : f ∈ C') =>
    bellman_strictMono_z M h h913 h914 hQ (f := f) (fun _ y => hf y)
  have hv' := (corollary_1 (S' := C') (S'' := {f | ∀ x, StrictMono fun z => f (x, z)})
    (bellman_contraction M h) hv ⟨0, fun _ _ _ _ => le_rfl⟩ hclosed
    (fun f hf x => (hmaps f hf x).monotone) hmaps).2
  exact hv' x

/-- **Exercise 9.7g** (corrected). Under §9.2's hypotheses, Assumptions 9.13–9.15, the
hypotheses of part (c), and `φ(x, y, ·)` nondecreasing, `v(x, ·)` is strictly increasing for each
`x` (and `v(·, z)` for each `z`). -/
theorem ex_9_7g [PartialOrder X] [PartialOrder Z] (h : BoundedDP M)
    (h98 : ∀ x x' y z, x < x' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → M.Γ (x, z) ⊆ M.Γ (x', z))
    (hφx : ∀ y z', Monotone fun x => M.φ (x, y, z'))
    (h913 : ∀ x y z z', z < z' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x, y, z'))
    (h914 : ∀ x z z', z ≤ z' → M.Γ (x, z) ⊆ M.Γ (x, z')) (hQ : IsMonotoneTF M.Q)
    (hφz : ∀ x y, Monotone fun z' => M.φ (x, y, z')) {v : X × Z →ᵇ ℝ}
    (hv : bellman M h v = v) :
    (∀ x, StrictMono fun z => v (x, z)) ∧ ∀ z, StrictMono fun x => v (x, z) := by
  set C' : Set (X × Z →ᵇ ℝ) := {f | Monotone (f : X × Z → ℝ)}
  have hclosed : IsClosed C' := by
    have := isClosed_pointwise_le (S := X × Z) (ι := {q : (X × Z) × (X × Z) // q.1 ≤ q.2})
      (fun q => q.1.1) (fun q => q.1.2)
    convert this using 1
    ext f
    exact ⟨fun hf q => hf q.2, fun hf p p' hpp' => hf ⟨(p, p'), hpp'⟩⟩
  have hjoint : ∀ f : X × Z →ᵇ ℝ, (∀ x, StrictMono fun z => f (x, z)) →
      (∀ z, StrictMono fun x => f (x, z)) → Monotone (f : X × Z → ℝ) := by
    intro f hz hx p p' hpp'
    exact ((hx p.2).monotone hpp'.1).trans ((hz p'.1).monotone hpp'.2)
  have hmaps : ∀ f ∈ C', bellman M h f ∈
      {g : X × Z →ᵇ ℝ | (∀ x, StrictMono fun z => g (x, z)) ∧
        ∀ z, StrictMono fun x => g (x, z)} := fun f hf =>
    ⟨bellman_strictMono_z M h h913 h914 hQ
        (fun x y z₁ z₂ hz => hf (Prod.mk_le_mk.2 ⟨hφz x y hz, hz⟩)),
      bellman_strictMono_x M h h98 h99 hφx
        fun z x x' hxx' => hf (Prod.mk_le_mk.2 ⟨hxx', le_rfl⟩)⟩
  exact (corollary_1 (S' := C') (bellman_contraction M h) hv ⟨0, fun _ _ _ => le_rfl⟩ hclosed
    (fun f hf => hjoint _ (hmaps f hf).1 (hmaps f hf).2) hmaps).2

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Interior points of convex-valued l.h.c. correspondences

Carried over from the Chapter 3 project (`RecursiveMethods/MathematicalPreliminaries`, the proof
of Exercise 3.12d): if `φ` is l.h.c. at `x` with convex values in `ℝᵐ`, every point interior to
`φ(x)` lies in `φ(xₙ)` for all large `n` (`eventually_mem_of_mem_interior`). Theorem 9.10 uses
it (as Theorem 4.11 does in Chapter 4), where the book asserts that `g(x₀, z₀) ∈ int Γ(x₀, z₀)`
and continuity of `Γ` give `g(x₀, z₀) ∈ Γ(x, z₀)` near `x₀`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.StochasticApplications

variable {X : Type*} [MetricSpace X] {m : ℕ}

/-- A linear functional on `ℝ^m` in coordinates. -/
theorem dual_apply_eq_sum (f : StrongDual ℝ (Fin m → ℝ)) (v : Fin m → ℝ) :
    f v = ∑ j, v j * f (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [map_sum, map_smul]

/-- `z ± 2δeⱼ`. -/
noncomputable def vertex (z : Fin m → ℝ) (δ : ℝ) (j : Fin m) (s : Bool) : Fin m → ℝ :=
  z + (if s then 2 * δ else -(2 * δ)) • Pi.single j 1

/-- No hyperplane separates `z` from points within `δ/(m + 1)` of every vertex `z ± 2δeⱼ`
(and from one further point `w₀`). -/
theorem no_separation {z : Fin m → ℝ} {δ : ℝ} (hδ : 0 < δ) (f : StrongDual ℝ (Fin m → ℝ))
    {u : ℝ} (hz : f z < u) {w₀ : Fin m → ℝ} (hw₀ : u < f w₀) (w : Fin m → Bool → Fin m → ℝ)
    (hw : ∀ j s, u < f (w j s)) (hclose : ∀ j s, ‖w j s - vertex z δ j s‖ ≤ δ / (m + 1)) :
    False := by
  set c : Fin m → ℝ := fun j => f (Pi.single j 1)
  set A := ∑ j, |c j|
  set ε := δ / ((m : ℝ) + 1)
  have hε : 0 < ε := by positivity
  -- the error terms move `f` by at most `εA`
  have herr : ∀ e : Fin m → ℝ, ‖e‖ ≤ ε → |f e| ≤ ε * A := fun e he => by
    rw [dual_apply_eq_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm e j).trans he) (abs_nonneg _)
  have hcoord : ∀ j, 2 * δ * |c j| ≤ ε * A := fun j => by
    have hs : ∀ s, 0 < f (w j s) - f z := fun s => by linarith [hw j s]
    have hdec : ∀ s, f (w j s) - f z =
        (if s then 2 * δ else -(2 * δ)) * c j + f (w j s - vertex z δ j s) := fun s => by
      simp only [vertex, map_sub, map_add, map_smul, smul_eq_mul, c]
      ring
    have h1 := hdec true
    have h2 := hdec false
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
    have e1 := (abs_le.1 (herr _ (hclose j true))).2
    have e2 := (abs_le.1 (herr _ (hclose j false))).2
    have s1 := hs true
    have s2 := hs false
    rcases abs_cases (c j) with ⟨hc, _⟩ | ⟨hc, _⟩ <;> rw [hc] <;> nlinarith
  have hsum : 2 * δ * A ≤ m * (ε * A) := by
    calc 2 * δ * A = ∑ j, 2 * δ * |c j| := Finset.mul_sum _ _ _
      _ ≤ ∑ _j : Fin m, ε * A := Finset.sum_le_sum fun j _ => hcoord j
      _ = m * (ε * A) := by simp
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hmε : (m : ℝ) * ε < 2 * δ := by
    have : (m : ℝ) * ε = δ * (m / (m + 1)) := by simp only [ε]; ring
    rw [this]
    have : (m : ℝ) / (m + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    nlinarith
  have hA : A = 0 := le_antisymm (by nlinarith) hA0
  have hc0 : ∀ j, c j = 0 := fun j => abs_eq_zero.1 (le_antisymm
    ((Finset.single_le_sum (fun k _ => abs_nonneg (c k)) (Finset.mem_univ j)).trans hA.le)
    (abs_nonneg _))
  have hf0 : ∀ v, f v = 0 := fun v => by
    rw [dual_apply_eq_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [show f (Pi.single j 1) = c j from rfl, hc0 j,
      mul_zero]
  linarith [hf0 z, hf0 w₀]

/-- If `φ` is l.h.c. at `x` with convex values in `ℝ^m`, every point interior to `φ(x)` lies in
`φ(xₙ)` for all large `n`, whenever `xₙ → x`. -/
theorem eventually_mem_of_mem_interior {φ : X → Set (Fin m → ℝ)} (hconv : ∀ x', Convex ℝ (φ x'))
    {x : X} (hφ : IsLHC φ x) {z : Fin m → ℝ} (hz : z ∈ interior (φ x)) {xs : ℕ → X}
    (hxs : Tendsto xs atTop (𝓝 x)) : ∀ᶠ n in atTop, z ∈ φ (xs n) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  set δ := r / 4
  have hδ : 0 < δ := by positivity
  have hv : ∀ j s, vertex z δ j s ∈ φ x := fun j s => interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, vertex, add_sub_cancel_left]
    refine (norm_smul_le _ _).trans_lt ?_
    have h1 : ‖(Pi.single j 1 : Fin m → ℝ)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2
      fun k => by
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
    have h2 : ‖(if s then 2 * δ else -(2 * δ))‖ = 2 * δ := by
      cases s <;> simp [abs_of_pos hδ]
    rw [h2]
    have h3 : 2 * δ < r := by simp only [δ]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * δ)]))
  obtain ⟨N₀, y₀, hy₀, -⟩ := hφ.2 z (interior_subset hz) xs hxs
  have happ := fun j s => hφ.2 _ (hv j s) xs hxs
  choose N ys hys hlim using happ
  have hclose : ∀ᶠ n in atTop, ∀ j s, ‖ys j s n - vertex z δ j s‖ ≤ δ / (m + 1) :=
    eventually_all.2 fun j => eventually_all.2 fun s => by
      filter_upwards [(hlim j s).eventually (Metric.closedBall_mem_nhds _
        (show (0 : ℝ) < δ / (m + 1) by positivity))] with n hn
      rwa [dist_eq_norm] at hn
  have hN : ∀ᶠ n in atTop, ∀ j s, N j s ≤ n :=
    eventually_all.2 fun j => eventually_all.2 fun s => eventually_ge_atTop _
  filter_upwards [hclose, hN, eventually_ge_atTop N₀] with n h1 h2 h3
  by_contra hzn
  set S : Set (Fin m → ℝ) := insert (y₀ n) (range fun p : Fin m × Bool => ys p.1 p.2 n)
  have hS : S ⊆ φ (xs n) := by
    rintro w (rfl | ⟨p, rfl⟩)
    · exact hy₀ n h3
    · exact hys p.1 p.2 n (h2 p.1 p.2)
  have hcl : IsClosed (convexHull ℝ S) :=
    (Set.Finite.isCompact_convexHull (𝕜 := ℝ) ((Set.finite_range _).insert _)).isClosed
  obtain ⟨f, u, hfz, hfu⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ S) hcl
    fun h => hzn (convexHull_min hS (hconv _) h)
  exact no_separation hδ f hfz (hfu _ (subset_convexHull ℝ S (mem_insert _ _)))
    (fun j s => ys j s n)
    (fun j s => hfu _ (subset_convexHull ℝ S (mem_insert_of_mem _ ⟨(j, s), rfl⟩))) h1

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bounded returns: concavity, policy functions, differentiability

SLP §9.2, pp. 264–267 and 269–270: Theorems 9.8–9.10 and Exercises 9.7d–f. The endogenous
state space is a convex set `X ⊆ ℝˡ` and the action space a convex set `Y ⊆ ℝᵐ` (Assumptions 9.4
and 9.16); `θx + (1 − θ)x′` is `cmb`.

* Assumption 9.10 (`Assumption910`: `F(·, ·, z)` concave on `A_z`, strictly when `x ≠ x′`) and
  Assumption 9.11 (`Assumption911`: `A_z` convex).
* **Exercise 9.7d** (`ex_9_7d`): if `φ(·, ·, z′)` is affine (`IsAffineφ`), `v(·, z)` is strictly
  concave. **Correction:** the solutions manual asserts this for `φ(·, ·, z′)` concave; then
  `f[φ(x, y, z′), z′]` is concave only if `f` is also nondecreasing in `x`, so the hypotheses of
  part (c) are needed as well (`ex_9_7d_concave`, which runs the contraction on the closed set of
  functions concave and nondecreasing in `x`). **Second correction:** that `G` is single-valued
  does not follow from Assumption 9.10, which is strict only in `x`: if neither `F` nor `φ`
  depends on `y`, every feasible `y` is optimal. We add that `φ(x, ·, z′)` is one-to-one
  (`ex_9_7d_policy`); in the first formulation `φ(x, y, z′) = y` is.
* **Theorem 9.8** (`theorem_9_8`): the first formulation; `v(·, z)` strictly concave and `G` a
  continuous single-valued function.
* **Exercise 9.7e** and **Theorem 9.9** (`ex_9_7e`, `theorem_9_9`): from a concave `v₀`, the
  policy functions of `vₙ = Tⁿv₀` converge to `g` pointwise, uniformly if `S` is compact.
* **Exercise 9.7f** and **Theorem 9.10** (`ex_9_7f`, `theorem_9_10`): if `φ` does not depend on
  `x`, `x₀ ∈ int X`, `g(x₀, z₀) ∈ int Γ(x₀, z₀)` and `F(·, g(x₀, z₀), z₀)` is differentiable at
  `x₀` (Assumption 9.12), then `v(·, z₀)` is differentiable at `x₀` with
  `vᵢ(x₀, z₀) = Fᵢ[x₀, g(x₀, z₀), z₀]` (Benveniste–Scheinkman, Theorem 4.10).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- `θx + (1 − θ)x′` in the convex set `S`. -/
def cmb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} (hS : Convex ℝ S)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x x' : S) : S :=
  ⟨θ • x.1 + (1 - θ) • x'.1, hS x.2 x'.2 h0 (by linarith) (by ring)⟩

theorem cmb_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    (hS : Convex ℝ S) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : S) : cmb hS h0 h1 x x = x := by
  ext1; simp only [cmb]; rw [← add_smul]; simp

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {SX : Set E} {SY : Set E'}

/-- `f` is concave on `S`. -/
def IsConcaveS (hS : Convex ℝ SX) (f : SX → ℝ) : Prop :=
  ∀ x x' (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1), θ * f x + (1 - θ) * f x' ≤ f (cmb hS h0 h1 x x')

/-- `f` is strictly concave on `S`. -/
def IsStrictConcaveS (hS : Convex ℝ SX) (f : SX → ℝ) : Prop :=
  ∀ x x', x ≠ x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * f x + (1 - θ) * f x' < f (cmb hS h0.le h1.le x x')

/-- A strictly concave function is concave. -/
theorem IsStrictConcaveS.isConcaveS {hS : Convex ℝ SX} {f : SX → ℝ}
    (hf : IsStrictConcaveS hS f) : IsConcaveS hS f := by
  intro x x' θ h0 h1
  rcases eq_or_ne x x' with rfl | hne
  · rw [cmb_self]; linarith
  rcases h0.eq_or_lt with rfl | h0'
  · simp only [zero_mul, sub_zero, one_mul, zero_add]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  rcases h1.eq_or_lt with rfl | h1'
  · simp only [one_mul, sub_self, zero_mul, add_zero]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  exact (hf x x' hne θ h0' h1').le

variable [MeasurableSpace E] [MeasurableSpace E']
variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]

/-- **Assumption 9.10.** For each `z`, `F(·, ·, z)` is concave on `A_z`, strictly if `x ≠ x′`. -/
def Assumption910 (hX : Convex ℝ SX) (hY : Convex ℝ SY) (M : Model SX SY Z) : Prop :=
  ∀ z x y x' y', y ∈ M.Γ (x, z) → y' ∈ M.Γ (x', z) → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * M.F (x, y, z) + (1 - θ) * M.F (x', y', z) ≤
      M.F (cmb hX h0.le h1.le x x', cmb hY h0.le h1.le y y', z) ∧
    (x ≠ x' → θ * M.F (x, y, z) + (1 - θ) * M.F (x', y', z) <
      M.F (cmb hX h0.le h1.le x x', cmb hY h0.le h1.le y y', z))

/-- **Assumption 9.11.** For each `z`, `A_z` is convex. -/
def Assumption911 (hX : Convex ℝ SX) (hY : Convex ℝ SY) (M : Model SX SY Z) : Prop :=
  ∀ z x y x' y', y ∈ M.Γ (x, z) → y' ∈ M.Γ (x', z) → ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
    cmb hY h0 h1 y y' ∈ M.Γ (cmb hX h0 h1 x x', z)

/-- `φ(·, ·, z′)` is affine. -/
def IsAffineφ (hX : Convex ℝ SX) (hY : Convex ℝ SY) (M : Model SX SY Z) : Prop :=
  ∀ x y x' y' z' (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
    M.φ (cmb hX h0 h1 x x', cmb hY h0 h1 y y', z') =
      cmb hX h0 h1 (M.φ (x, y, z')) (M.φ (x', y', z'))

variable {hX : Convex ℝ SX} {hY : Convex ℝ SY}

omit [MeasurableSpace E] [MeasurableSpace E'] [MeasurableSpace Z] in
/-- The functions concave in `x` form a closed subset of `C(S)`. -/
theorem isClosed_concaveX (hX : Convex ℝ SX) :
    IsClosed {f : SX × Z →ᵇ ℝ | ∀ z, IsConcaveS hX fun x => f (x, z)} := by
  have : {f : SX × Z →ᵇ ℝ | ∀ z, IsConcaveS hX fun x => f (x, z)} =
      ⋂ z, ⋂ x, ⋂ x', ⋂ θ : ℝ, ⋂ h0 : 0 ≤ θ, ⋂ h1 : θ ≤ 1,
        {f : SX × Z →ᵇ ℝ | θ * f (x, z) + (1 - θ) * f (x', z) ≤ f (cmb hX h0 h1 x x', z)} := by
    ext f; simp [IsConcaveS]
  rw [this]
  refine isClosed_iInter fun z => isClosed_iInter fun x => isClosed_iInter fun x' =>
    isClosed_iInter fun θ => isClosed_iInter fun h0 => isClosed_iInter fun h1 =>
      isClosed_le ?_ (continuous_eval_const _)
  exact (continuous_const.mul (continuous_eval_const _)).add
    (continuous_const.mul (continuous_eval_const _))

variable (M : Model SX SY Z) [IsMarkovKernel M.Q] [OpensMeasurableSpace Z]

/-- **Concavity passes through the integral** (Lemma 9.5): with `φ` affine and `f(·, z′)`
concave, `θ E₀ + (1 − θ) E₁ ≤ E_θ` for the expected continuation values. -/
theorem expV_comb (h : BoundedDP M) (haff : IsAffineφ hX hY M) {f : SX × Z →ᵇ ℝ}
    (hf : ∀ z, IsConcaveS hX fun x => f (x, z)) {x x' : SX} {y y' : SY} {z : Z}
    (hy : y ∈ M.Γ (x, z)) (hy' : y' ∈ M.Γ (x', z)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hyθ : cmb hY h0 h1 y y' ∈ M.Γ (cmb hX h0 h1 x x', z)) :
    θ * expV M f (x, z) y + (1 - θ) * expV M f (x', z) y' ≤
      expV M f (cmb hX h0 h1 x x', z) (cmb hY h0 h1 y y') := by
  have i0 := integrable_integrand M h f hy z
  have i1 := integrable_integrand M h f hy' z
  have iθ := integrable_integrand M h f hyθ z
  simp only [expV]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i0.const_mul θ)
    (i1.const_mul _)]
  refine integral_mono ((i0.const_mul θ).add (i1.const_mul _)) iθ fun z' => ?_
  change θ * f (M.φ (x, y, z'), z') + (1 - θ) * f (M.φ (x', y', z'), z') ≤
    f (M.φ (cmb hX h0 h1 x x', cmb hY h0 h1 y y', z'), z')
  rw [haff]
  exact hf z' _ _ θ h0 h1

/-- The strict version: with `f(·, z′)` strictly concave and `φ(x, y, z′) ≠ φ(x′, y′, z′)`. -/
theorem expV_comb_strict (h : BoundedDP M) (haff : IsAffineφ hX hY M) {f : SX × Z →ᵇ ℝ}
    (hf : ∀ z, IsStrictConcaveS hX fun x => f (x, z)) {x x' : SX} {y y' : SY} {z : Z}
    (hy : y ∈ M.Γ (x, z)) (hy' : y' ∈ M.Γ (x', z)) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (hyθ : cmb hY h0.le h1.le y y' ∈ M.Γ (cmb hX h0.le h1.le x x', z))
    (hne : ∀ z', M.φ (x, y, z') ≠ M.φ (x', y', z')) :
    θ * expV M f (x, z) y + (1 - θ) * expV M f (x', z) y' <
      expV M f (cmb hX h0.le h1.le x x', z) (cmb hY h0.le h1.le y y') := by
  have i0 := integrable_integrand M h f hy z
  have i1 := integrable_integrand M h f hy' z
  have iθ := integrable_integrand M h f hyθ z
  simp only [expV]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i0.const_mul θ)
    (i1.const_mul _)]
  refine integral_lt_integral_of_lt ((i0.const_mul θ).add (i1.const_mul _)) iθ fun z' => ?_
  change θ * f (M.φ (x, y, z'), z') + (1 - θ) * f (M.φ (x', y', z'), z') <
    f (M.φ (cmb hX h0.le h1.le x x', cmb hY h0.le h1.le y y', z'), z')
  rw [haff]
  exact hf z' _ _ (hne z') θ h0 h1

omit [OpensMeasurableSpace Z] in
/-- `T` maps `f` to a function strictly concave in `x`, given the concavity inequality for the
expected continuation values of `f` (Lemma 9.5; `expV_comb` when `φ` is affine). -/
theorem bellman_maps_concave (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M) {f : SX × Z →ᵇ ℝ}
    (hE : ∀ x x' y y' z, y ∈ M.Γ (x, z) → y' ∈ M.Γ (x', z) → ∀ (θ : ℝ) (h0 : 0 ≤ θ)
      (h1 : θ ≤ 1), θ * expV M f (x, z) y + (1 - θ) * expV M f (x', z) y' ≤
        expV M f (cmb hX h0 h1 x x', z) (cmb hY h0 h1 y y')) (z : Z) :
    IsStrictConcaveS hX fun x => bellman M h f (x, z) := by
  intro x₀ x₁ hne θ h0 h1
  obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax M h f (x₀, z)
  obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax M h f (x₁, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M h f (cmb hX h0.le h1.le x₀ x₁, z)
  have hyθ := h911 z x₀ y₀ x₁ y₁ hy₀ hy₁ θ h0.le h1.le
  have hF := (h910 z x₀ y₀ x₁ y₁ hy₀ hy₁ θ h0 h1).2 hne
  have hE' := mul_le_mul_of_nonneg_left (hE x₀ x₁ y₀ y₁ z hy₀ hy₁ θ h0.le h1.le) h.β_pos.le
  have hm := hmax _ hyθ
  simp only [rhs] at hv₀ hv₁ hm
  dsimp only at hv₀ hv₁ hm ⊢
  rw [hv₀, hv₁]
  nlinarith

/-- **Exercise 9.7d** (`φ(·, ·, z′)` affine). The fixed point `v(·, z)` is strictly concave. -/
theorem ex_9_7d (h : BoundedDP M) (h910 : Assumption910 hX hY M) (h911 : Assumption911 hX hY M)
    (haff : IsAffineφ hX hY M) {v : SX × Z →ᵇ ℝ} (hv : bellman M h v = v) (z : Z) :
    IsStrictConcaveS hX fun x => v (x, z) := by
  have hmaps := fun (f : SX × Z →ᵇ ℝ) (hf : ∀ z, IsConcaveS hX fun x => f (x, z)) =>
    bellman_maps_concave M h h910 h911 (f := f) fun x x' y y' z hy hy' θ h0 h1 =>
      expV_comb M h haff hf hy hy' h0 h1 (h911 z x y x' y' hy hy' θ h0 h1)
  exact (corollary_1 (S' := {f : SX × Z →ᵇ ℝ | ∀ z, IsConcaveS hX fun x => f (x, z)})
    (S'' := {f | ∀ z, IsStrictConcaveS hX fun x => f (x, z)}) (bellman_contraction M h) hv
    ⟨0, fun _ _ _ _ _ _ => by simp⟩ (isClosed_concaveX hX)
    (fun f hf z => (hmaps f hf z).isConcaveS) hmaps).2 z

/-- With `w(·, z′)` strictly concave and `φ(x, ·, z′)` one-to-one, the objective
`F(x, y, z) + β ∫ w[φ(x, y, z′), z′] Q(z, dz′)` has at most one maximizer on `Γ(x, z)`. -/
theorem argmax_unique_of_strictConcave (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M) (haff : IsAffineφ hX hY M)
    (hinj : ∀ x y y' z', y ≠ y' → M.φ (x, y, z') ≠ M.φ (x, y', z')) {w : SX × Z →ᵇ ℝ}
    (hw : ∀ z, IsStrictConcaveS hX fun x => w (x, z)) :
    ∀ s, ∀ y₁ ∈ argmax (objG M w) M.Γ s, ∀ y₂ ∈ argmax (objG M w) M.Γ s, y₁ = y₂ := by
  rintro ⟨x, z⟩ y₁ hy₁ y₂ hy₂
  by_contra hne
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  have hh1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hmem := h911 z x y₁ x y₂ hy₁.1 hy₂.1 (1 / 2) hh.le hh1.le
  have hF := (h910 z x y₁ x y₂ hy₁.1 hy₂.1 (1 / 2) hh hh1).1
  have hE := expV_comb_strict M h haff hw hy₁.1 hy₂.1 hh hh1 hmem
    fun z' => hinj x y₁ y₂ z' hne
  rw [cmb_self] at hmem hF hE
  have hle := le_maxValue (continuousOn_objG M h w) (h.compact (x, z)) hmem
  have e1 := hy₁.2
  have e2 := hy₂.2
  simp only [objG, rhs] at hle e1 e2
  nlinarith [h.β_pos]

/-- **Exercise 9.7d** (`G` single-valued and continuous), when `φ(x, ·, z′)` is one-to-one. -/
theorem ex_9_7d_policy [Nonempty SY] (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M) (haff : IsAffineφ hX hY M)
    (hinj : ∀ x y y' z', y ≠ y' → M.φ (x, y, z') ≠ M.φ (x, y', z')) {v : SX × Z →ᵇ ℝ}
    (hv : bellman M h v = v) :
    UniqueArgmax M.Γ (objG M v) ∧ (∀ s, policy M v s = {argmaxFn M.Γ (objG M v) s}) ∧
      Continuous (argmaxFn M.Γ (objG M v)) := by
  have huniq := argmax_unique_of_strictConcave M h h910 h911 haff hinj
    (ex_9_7d M h h910 h911 haff hv)
  have hU : UniqueArgmax M.Γ (objG M v) :=
    ⟨h.nonempty, h.compact, h.lhc, h.uhc, continuousOn_objG M h v, huniq⟩
  refine ⟨hU, fun s => ?_, hU.continuous_argmaxFn⟩
  rw [policy_eq_argmax M h hv]
  exact hU.argmax_eq s

/-- **Theorem 9.8** (first formulation). Under Assumptions 9.4–9.7 and 9.10–9.11, `v(·, z)` is
strictly concave for each `z`, and `G` is a continuous single-valued function. -/
theorem theorem_9_8 [Nonempty SX] (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : SX × Z → Set SX)
    (F : SX × SX × Z → ℝ) (β : ℝ) (h : BoundedDP (Model.first Q Γ F β))
    (h910 : Assumption910 hX hX (Model.first Q Γ F β))
    (h911 : Assumption911 hX hX (Model.first Q Γ F β)) {v : SX × Z →ᵇ ℝ}
    (hv : bellman (Model.first Q Γ F β) h v = v) :
    (∀ z, IsStrictConcaveS hX fun x => v (x, z)) ∧
      (∀ s, policy (Model.first Q Γ F β) v s =
        {argmaxFn Γ (objG (Model.first Q Γ F β) v) s}) ∧
      Continuous (argmaxFn Γ (objG (Model.first Q Γ F β) v)) := by
  have haff : IsAffineφ hX hX (Model.first Q Γ F β) := fun _ _ _ _ _ _ _ _ => rfl
  obtain ⟨-, h2, h3⟩ := ex_9_7d_policy (Model.first Q Γ F β) h h910 h911 haff
    (fun _ _ _ _ hne => hne) hv
  exact ⟨ex_9_7d (Model.first Q Γ F β) h h910 h911 haff hv, h2, h3⟩

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bounded returns: concave laws of motion, policy convergence, differentiability

SLP §9.2, pp. 265–267 and 269–270.

* `ex_9_7d_concave`: Exercise 9.7d with `φ(·, ·, z′)` concave (in the order of `X`), under the
  hypotheses of part (c) as well — `T` maps the closed set of functions concave and
  nondecreasing in `x` into the strictly concave, strictly increasing ones.
* `ex_9_7e`, `theorem_9_9`: from `v₀` concave in `x`, the policy functions `gₙ` of `vₙ = Tⁿv₀`
  converge to `g` pointwise, and uniformly if `S` is compact (Theorem 3.8).
* `ex_9_7f`, `theorem_9_10`: differentiability of `v(·, z₀)` at interior points
  (Benveniste–Scheinkman, Theorem 4.10).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [MeasurableSpace E'] {SX : Set E} {SY : Set E'}
  {hX : Convex ℝ SX} {hY : Convex ℝ SY}
variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
variable (M : Model SX SY Z) [IsMarkovKernel M.Q] [OpensMeasurableSpace Z]

/-- **Exercise 9.7d** (corrected, `φ(·, ·, z′)` concave). With the hypotheses of part (c) —
Assumptions 9.8 and 9.9 and `φ(·, y, z′)` nondecreasing — and
`θφ(x, y, z′) + (1 − θ)φ(x′, y′, z′) ≤ φ(θ(x, y) + (1 − θ)(x′, y′), z′)`, the fixed point `v(·, z)`
is strictly concave and strictly increasing. -/
theorem ex_9_7d_concave [PartialOrder E] (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M)
    (h98 : ∀ x x' y z, x < x' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → M.Γ (x, z) ⊆ M.Γ (x', z))
    (hφx : ∀ y z', Monotone fun x => M.φ (x, y, z'))
    (hφc : ∀ x y x' y' z' (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      cmb hX h0 h1 (M.φ (x, y, z')) (M.φ (x', y', z')) ≤
        M.φ (cmb hX h0 h1 x x', cmb hY h0 h1 y y', z'))
    {v : SX × Z →ᵇ ℝ} (hv : bellman M h v = v) (z : Z) :
    IsStrictConcaveS hX (fun x => v (x, z)) ∧ StrictMono fun x => v (x, z) := by
  set C' : Set (SX × Z →ᵇ ℝ) :=
    {f | ∀ z, IsConcaveS hX (fun x => f (x, z)) ∧ Monotone fun x => f (x, z)}
  have hclosed : IsClosed C' := by
    have h1 := isClosed_concaveX (Z := Z) hX
    have h2 := isClosed_pointwise_le (S := SX × Z) (ι := {q : SX × SX × Z // q.1 ≤ q.2.1})
      (fun q => (q.1.1, q.1.2.2)) (fun q => (q.1.2.1, q.1.2.2))
    convert h1.inter h2 using 1
    ext f
    exact ⟨fun hf => ⟨fun z => (hf z).1, fun q => (hf q.1.2.2).2 q.2⟩,
      fun hf z => ⟨hf.1 z, fun x x' hxx' => hf.2 ⟨(x, x', z), hxx'⟩⟩⟩
  have hmaps : ∀ f ∈ C', bellman M h f ∈ {g : SX × Z →ᵇ ℝ | ∀ z,
      IsStrictConcaveS hX (fun x => g (x, z)) ∧ StrictMono fun x => g (x, z)} := by
    intro f hf z
    refine ⟨bellman_maps_concave M h h910 h911 (fun x x' y y' z hy hy' θ h0 h1 => ?_) z,
      bellman_strictMono_x M h h98 h99 hφx (fun z => (hf z).2) z⟩
    have hyθ := h911 z x y x' y' hy hy' θ h0 h1
    have i0 := integrable_integrand M h f hy z
    have i1 := integrable_integrand M h f hy' z
    have iθ := integrable_integrand M h f hyθ z
    simp only [expV]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i0.const_mul θ)
      (i1.const_mul _)]
    refine integral_mono ((i0.const_mul θ).add (i1.const_mul _)) iθ fun z' => ?_
    change θ * f (M.φ (x, y, z'), z') + (1 - θ) * f (M.φ (x', y', z'), z') ≤
      f (M.φ (cmb hX h0 h1 x x', cmb hY h0 h1 y y', z'), z')
    exact ((hf z').1 _ _ θ h0 h1).trans ((hf z').2 (hφc x y x' y' z' θ h0 h1))
  have := (corollary_1 (S' := C') (bellman_contraction M h) hv
    ⟨0, fun _ => ⟨fun _ _ _ _ _ => by simp, fun _ _ _ => le_rfl⟩⟩ hclosed
    (fun f hf z => ⟨((hmaps f hf) z).1.isConcaveS, ((hmaps f hf) z).2.monotone⟩) hmaps).2 z
  exact this

omit [NormedSpace ℝ E] [NormedSpace ℝ E'] in
/-- `|∫ v[φ(x, y, z′), z′] Q(z, dz′) − ∫ w[φ(x, y, z′), z′] Q(z, dz′)| ≤ ‖v − w‖`. -/
theorem abs_expV_sub_le (h : BoundedDP M) (v w : SX × Z →ᵇ ℝ) {s : SX × Z} {y : SY}
    (hy : y ∈ M.Γ s) : |expV M v s y - expV M w s y| ≤ dist v w := by
  rw [expV, expV, ← integral_sub (integrable_integrand M h v hy _)
    (integrable_integrand M h w hy _)]
  have := norm_integral_le_of_norm_le_const (μ := M.Q s.2) (C := dist v w)
    (f := fun z' => v (M.φ (s.1, y, z'), z') - w (M.φ (s.1, y, z'), z'))
    (Eventually.of_forall fun z' => by rw [← dist_eq_norm]; exact dist_coe_le_dist _)
  simpa [Real.norm_eq_abs, measureReal_def] using this

/-- **Exercise 9.7e** (policy convergence). Let `φ` be affine with `φ(x, ·, z′)` one-to-one, let
`v₀` be bounded, continuous and concave in `x`, and let `gₙ` be the policy function of
`vₙ = Tⁿv₀`. Then `gₙ → g` pointwise, and uniformly if `S` is compact. -/
theorem ex_9_7e [Nonempty SY] (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M) (haff : IsAffineφ hX hY M)
    (hinj : ∀ x y y' z', y ≠ y' → M.φ (x, y, z') ≠ M.φ (x, y', z')) {v : SX × Z →ᵇ ℝ}
    (hv : bellman M h v = v) {v₀ : SX × Z →ᵇ ℝ} (hv₀ : ∀ z, IsConcaveS hX fun x => v₀ (x, z)) :
    (∀ s, Tendsto (fun n => argmaxFn M.Γ (objG M ((bellman M h)^[n] v₀)) s) atTop
      (𝓝 (argmaxFn M.Γ (objG M v) s))) ∧
    (CompactSpace (SX × Z) → TendstoUniformly
      (fun n => argmaxFn M.Γ (objG M ((bellman M h)^[n] v₀))) (argmaxFn M.Γ (objG M v)) atTop) := by
  set T := bellman M h
  have hmaps := fun (f : SX × Z →ᵇ ℝ) (hf : ∀ z, IsConcaveS hX fun x => f (x, z)) =>
    bellman_maps_concave M h h910 h911 (f := f) fun x x' y y' z hy hy' θ h0 h1 =>
      expV_comb M h haff hf hy hy' h0 h1 (h911 z x y x' y' hy hy' θ h0 h1)
  have hconc : ∀ n, ∀ z, IsConcaveS hX fun x => (T^[n] v₀) (x, z) := by
    intro n
    induction n with
    | zero => exact hv₀
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact fun z => (hmaps _ ih z).isConcaveS
  have hU : ∀ n, UniqueArgmax M.Γ (objG M (T^[n + 1] v₀)) := fun n => by
    have hsc : ∀ z, IsStrictConcaveS hX fun x => (T^[n + 1] v₀) (x, z) := by
      rw [Function.iterate_succ_apply']
      exact hmaps _ (hconc n)
    exact ⟨h.nonempty, h.compact, h.lhc, h.uhc, continuousOn_objG M h _,
      argmax_unique_of_strictConcave M h h910 h911 haff hinj hsc⟩
  have hUv := (ex_9_7d_policy M h h910 h911 haff hinj hv).1
  have hunif : TendstoUniformlyOn (fun n => objG M (T^[n + 1] v₀)) (objG M v) atTop
      (graph M.Γ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => M.β * (M.β ^ (n + 1) * dist v₀ v)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h.β_pos.le h.β_lt).comp
        (tendsto_add_atTop_nat 1)).mul_const (dist v₀ v) |>.const_mul M.β
      simpa using this
    obtain ⟨w, -, hwu, hwr⟩ := theorem_3_2 (bellman_contraction M h)
    rw [← hwu v hv] at hwr
    filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn p hp
    have hd : dist (T^[n + 1] v₀) v ≤ M.β ^ (n + 1) * dist v₀ v := hwr v₀ (n + 1)
    simp only [objG, rhs, Real.dist_eq]
    calc |M.F (p.1.1, p.2, p.1.2) + M.β * expV M v p.1 p.2 -
          (M.F (p.1.1, p.2, p.1.2) + M.β * expV M (T^[n + 1] v₀) p.1 p.2)|
        = M.β * |expV M v p.1 p.2 - expV M (T^[n + 1] v₀) p.1 p.2| := by
          rw [show M.F (p.1.1, p.2, p.1.2) + M.β * expV M v p.1 p.2 -
            (M.F (p.1.1, p.2, p.1.2) + M.β * expV M (T^[n + 1] v₀) p.1 p.2) =
            M.β * (expV M v p.1 p.2 - expV M (T^[n + 1] v₀) p.1 p.2) by ring, abs_mul,
            abs_of_pos h.β_pos]
      _ ≤ M.β * (M.β ^ (n + 1) * dist v₀ v) := by
          refine mul_le_mul_of_nonneg_left ?_ h.β_pos.le
          exact (abs_expV_sub_le M h _ _ hp).trans (by rw [dist_comm]; exact hd)
      _ < ε := hn
  refine ⟨fun s => ?_, fun _ => ?_⟩
  · exact (tendsto_add_atTop_iff_nat 1).1 (theorem_3_8 hUv hU hunif s)
  · have := theorem_3_8_uniform hUv hU hunif
    rw [Metric.tendstoUniformly_iff] at this ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (this ε hε)
    refine eventually_atTop.2 ⟨N + 1, fun n hn x => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact hN k (by omega) x

/-- **Theorem 9.9** (first formulation): from `v₀` concave in `x`, `gₙ → g` pointwise, uniformly
if `X` and `Z` are compact. -/
theorem theorem_9_9 [Nonempty SX] (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : SX × Z → Set SX)
    (F : SX × SX × Z → ℝ) (β : ℝ) (h : BoundedDP (Model.first Q Γ F β))
    (h910 : Assumption910 hX hX (Model.first Q Γ F β))
    (h911 : Assumption911 hX hX (Model.first Q Γ F β)) {v : SX × Z →ᵇ ℝ}
    (hv : bellman (Model.first Q Γ F β) h v = v) {v₀ : SX × Z →ᵇ ℝ}
    (hv₀ : ∀ z, IsConcaveS hX fun x => v₀ (x, z)) :
    (∀ s, Tendsto (fun n => argmaxFn Γ (objG (Model.first Q Γ F β)
      ((bellman (Model.first Q Γ F β) h)^[n] v₀)) s) atTop
      (𝓝 (argmaxFn Γ (objG (Model.first Q Γ F β) v) s))) ∧
    (CompactSpace (SX × Z) → TendstoUniformly
      (fun n => argmaxFn Γ (objG (Model.first Q Γ F β)
        ((bellman (Model.first Q Γ F β) h)^[n] v₀)))
      (argmaxFn Γ (objG (Model.first Q Γ F β) v)) atTop) :=
  ex_9_7e (Model.first Q Γ F β) h h910 h911 (fun _ _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ hne => hne) hv hv₀

omit [MetricSpace Z] [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] in
/-- Under Assumption 9.11 the values of `Γ` are convex sets. -/
theorem convex_image_Γ (h911 : Assumption911 hX hY M) (s : SX × Z) :
    Convex ℝ (Subtype.val '' M.Γ s) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have := h911 s.2 s.1 y s.1 y' hy hy' a ha (by linarith)
  rw [cmb_self] at this
  exact ⟨_, this, rfl⟩

omit [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] in
/-- If `g₀` is interior to `Γ(x₀, z₀) ⊆ ℝᵐ`, then `g₀ ∈ Γ(x, z₀)` for all `x` near `x₀`. -/
theorem eventually_mem_Γ {m : ℕ} {T : Set (Fin m → ℝ)} {hT : Convex ℝ T} (N : Model SX T Z)
    (hl : ∀ s, IsLHC N.Γ s) (h911 : Assumption911 hX hT N) {x₀ : SX} {z₀ : Z} {g₀ : T}
    (hg : g₀.1 ∈ interior (Subtype.val '' N.Γ (x₀, z₀))) :
    ∀ᶠ x in 𝓝 x₀, g₀ ∈ N.Γ (x, z₀) := by
  have hlhc : IsLHC (fun x => Subtype.val '' N.Γ (x, z₀)) x₀ := by
    refine ⟨(hl (x₀, z₀)).1.image _, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ xs hxs
    obtain ⟨N', ys, hys, hlim⟩ := (hl (x₀, z₀)).2 y hy (fun n => (xs n, z₀))
      (hxs.prodMk_nhds tendsto_const_nhds)
    exact ⟨N', fun n => (ys n).1, fun n hn => ⟨ys n, hys n hn, rfl⟩,
      (continuous_subtype_val.tendsto y).comp hlim⟩
  have hseq : ∀ xs : ℕ → SX, Tendsto xs atTop (𝓝 x₀) → ∀ᶠ n in atTop, g₀ ∈ N.Γ (xs n, z₀) :=
    fun xs hxs => (eventually_mem_of_mem_interior (fun x => convex_image_Γ N h911 (x, z₀))
      hlhc hg hxs).mono fun n ⟨y, hy, hyg⟩ => Subtype.ext hyg ▸ hy
  exact eventually_iff_seq_eventually.2 hseq

omit [MeasurableSpace E] in
/-- A function on `X ⊆ E` extended by zero. -/
noncomputable def liftS (f : SX → ℝ) (x : E) : ℝ := by
  classical exact if hx : x ∈ SX then f ⟨x, hx⟩ else 0

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] in
theorem liftS_of_mem (f : SX → ℝ) {x : E} (hx : x ∈ SX) : liftS f x = f ⟨x, hx⟩ := by
  simp only [liftS, hx, ↓reduceDIte]

omit [MeasurableSpace E] in
/-- A concave function on `X` is concave on `X ⊆ E` after extension. -/
theorem concaveOn_liftS {f : SX → ℝ} (hf : IsConcaveS hX f) : ConcaveOn ℝ SX (liftS f) := by
  refine ⟨hX, fun x hx y hy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hmem : a • x + b • y ∈ SX := hX hx hy ha hb hab
  rw [liftS_of_mem f hx, liftS_of_mem f hy, liftS_of_mem f hmem, smul_eq_mul, smul_eq_mul]
  have := hf ⟨x, hx⟩ ⟨y, hy⟩ a ha ha1
  subst hb'
  exact this

/-- **Exercise 9.7f** with the neighbourhood condition as a hypothesis. Let `φ(x, y, z′)` not
depend on `x`, let `x₀ ∈ int X`, let `g₀ = g(x₀, z₀)` lie in `Γ(x, z₀)` for all `x` near `x₀`,
and let `x ↦ F(x, g₀, z₀)` have derivative `DF` at `x₀`. Then `v(·, z₀)` is differentiable at
`x₀` with derivative `DF`. -/
theorem ex_9_7f' [Nonempty SY] (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M) (haff : IsAffineφ hX hY M)
    (hinj : ∀ x y y' z', y ≠ y' → M.φ (x, y, z') ≠ M.φ (x, y', z')) {v : SX × Z →ᵇ ℝ}
    (hv : bellman M h v = v) (hφx : ∀ x x' y z', M.φ (x, y, z') = M.φ (x', y, z'))
    {x₀ : SX} {z₀ : Z} (hint : SX ∈ 𝓝 x₀.1)
    (hev : ∀ᶠ x in 𝓝 x₀, argmaxFn M.Γ (objG M v) (x₀, z₀) ∈ M.Γ (x, z₀)) {DF : E →L[ℝ] ℝ}
    (hF : HasFDerivAt (liftS fun x => M.F (x, argmaxFn M.Γ (objG M v) (x₀, z₀), z₀)) DF x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) DF x₀.1 := by
  set g₀ := argmaxFn M.Γ (objG M v) (x₀, z₀)
  obtain ⟨hU, -, -⟩ := ex_9_7d_policy M h h910 h911 haff hinj hv
  have hvc := ex_9_7d M h h910 h911 haff hv z₀
  set c := M.β * expV M v (x₀, z₀) g₀
  set W : E → ℝ := fun x => liftS (fun x => M.F (x, g₀, z₀)) x + c
  have hW : HasFDerivAt W DF x₀.1 := hF.add_const c
  have hg₀ := hU.argmaxFn_mem (x₀, z₀)
  have hvx : ∀ s, v s = maxValue (objG M v) M.Γ s := fun s => by
    rw [← bellman_apply M h, hv]
  have hexp : ∀ x : SX, expV M v (x, z₀) g₀ = expV M v (x₀, z₀) g₀ := fun x => by
    simp only [expV]
    congr 1
    funext z'
    rw [hφx x x₀]
  have heq : W x₀.1 = liftS (fun x => v (x, z₀)) x₀.1 := by
    simp only [W, liftS_of_mem _ x₀.2, Subtype.coe_eta]
    rw [hvx (x₀, z₀), ← hg₀.2]
    rfl
  have hle : ∀ᶠ x in 𝓝 x₀.1, W x ≤ liftS (fun x => v (x, z₀)) x := by
    have h1 := hev
    rw [nhds_subtype, eventually_comap] at h1
    filter_upwards [h1, hint] with x hx hxS
    simp only [W, liftS_of_mem _ hxS]
    rw [hvx (⟨x, hxS⟩, z₀)]
    have := le_maxValue (continuousOn_objG M h v) (h.compact _) (hx ⟨x, hxS⟩ rfl)
    simp only [objG, rhs] at this
    rw [hexp] at this
    exact this
  exact theorem_4_10 (concaveOn_liftS hvc.isConcaveS) hint hW heq hle

/-- **Exercise 9.7f.** As `ex_9_7f'`, for actions in `ℝᵐ` with `g(x₀, z₀) ∈ int Γ(x₀, z₀)`:
then `vᵢ(x₀, z₀) = Fᵢ[x₀, g(x₀, z₀), z₀]`. -/
theorem ex_9_7f {m : ℕ} {T : Set (Fin m → ℝ)} {hT : Convex ℝ T} [Nonempty T]
    (N : Model SX T Z) [IsMarkovKernel N.Q] (h : BoundedDP N) (h910 : Assumption910 hX hT N)
    (h911 : Assumption911 hX hT N) (haff : IsAffineφ hX hT N)
    (hinj : ∀ x y y' z', y ≠ y' → N.φ (x, y, z') ≠ N.φ (x, y', z')) {v : SX × Z →ᵇ ℝ}
    (hv : bellman N h v = v) (hφx : ∀ x x' y z', N.φ (x, y, z') = N.φ (x', y, z'))
    {x₀ : SX} {z₀ : Z} (hint : SX ∈ 𝓝 x₀.1)
    (hg : (argmaxFn N.Γ (objG N v) (x₀, z₀)).1 ∈ interior (Subtype.val '' N.Γ (x₀, z₀)))
    {DF : E →L[ℝ] ℝ}
    (hF : HasFDerivAt (liftS fun x => N.F (x, argmaxFn N.Γ (objG N v) (x₀, z₀), z₀)) DF x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) DF x₀.1 :=
  ex_9_7f' N h h910 h911 haff hinj hv hφx hint (eventually_mem_Γ N h.lhc h911 hg) hF

/-- **Theorem 9.10** (first formulation, `X ⊆ ℝˡ`). Under Assumptions 9.4–9.7 and 9.10–9.12, if
`x₀ ∈ int X` and `g(x₀, z₀) ∈ int Γ(x₀, z₀)`, then `v(·, z₀)` is differentiable at `x₀` with
`vᵢ(x₀, z₀) = Fᵢ[x₀, g(x₀, z₀), z₀]`. -/
theorem theorem_9_10 {l : ℕ} {S : Set (Fin l → ℝ)} {hS : Convex ℝ S} [Nonempty S]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : S × Z → Set S)
    (F : S × S × Z → ℝ) (β : ℝ) (h : BoundedDP (Model.first Q Γ F β))
    (h910 : Assumption910 hS hS (Model.first Q Γ F β))
    (h911 : Assumption911 hS hS (Model.first Q Γ F β)) {v : S × Z →ᵇ ℝ}
    (hv : bellman (Model.first Q Γ F β) h v = v) {x₀ : S} {z₀ : Z} (hint : S ∈ 𝓝 x₀.1)
    (hg : (argmaxFn Γ (objG (Model.first Q Γ F β) v) (x₀, z₀)).1 ∈
      interior (Subtype.val '' Γ (x₀, z₀)))
    {DF : (Fin l → ℝ) →L[ℝ] ℝ}
    (hF : HasFDerivAt (liftS fun x =>
      F (x, argmaxFn Γ (objG (Model.first Q Γ F β) v) (x₀, z₀), z₀)) DF x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) DF x₀.1 :=
  ex_9_7f (Model.first Q Γ F β) h h910 h911 (fun _ _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ hne => hne) hv (fun _ _ _ _ => rfl) hint hg hF

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Marginals of the history measures

Two facts used to evaluate expectations along plans in §9.4: dropping the last date maps `μᵗ⁺¹`
to `μᵗ` (`map_init_hist`), so a function of the history up to `t` has the same integral under
both; and with i.i.d. shocks, `Q(z, ·) = μ`, the last shock is distributed as `μ`
(`map_last_hist_const`).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q]

/-- Dropping the last date: `μᵗ⁺¹(z₀, ·)` maps to `μᵗ(z₀, ·)`. -/
theorem map_init_hist (t : ℕ) (z₀ : Z) :
    (hist Q (t + 1) z₀).map Fin.init = hist Q t z₀ := by
  have := ex_8_8a Q t
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_init t),
    hist_succ_lintegral_last Q t z₀ (f := fun h => f (Fin.init h)) (hf.comp (measurable_init t))]
  simp only [Fin.init_snoc, lintegral_const, measure_univ, mul_one]

theorem lintegral_init (t : ℕ) (z₀ : Z) {f : (Fin t → Z) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ h, f (Fin.init h) ∂hist Q (t + 1) z₀ = ∫⁻ h, f h ∂hist Q t z₀ := by
  rw [← lintegral_map hf (measurable_init t), map_init_hist]

theorem integral_init (t : ℕ) (z₀ : Z) {F : (Fin t → Z) → ℝ}
    (hF : AEStronglyMeasurable F (hist Q t z₀)) :
    ∫ h, F (Fin.init h) ∂hist Q (t + 1) z₀ = ∫ h, F h ∂hist Q t z₀ := by
  rw [← map_init_hist Q t z₀] at hF ⊢
  rw [integral_map (measurable_init t).aemeasurable hF]

theorem integrable_init (t : ℕ) (z₀ : Z) {F : (Fin t → Z) → ℝ}
    (hF : Integrable F (hist Q t z₀)) :
    Integrable (fun h => F (Fin.init h)) (hist Q (t + 1) z₀) := by
  rw [← map_init_hist Q t z₀] at hF
  exact hF.comp_measurable (measurable_init t)

/-- With i.i.d. shocks the last shock is distributed as `μ`. -/
theorem map_last_hist_const (μ : Measure Z) [IsProbabilityMeasure μ] (t : ℕ) (z₀ : Z) :
    (hist (Kernel.const Z μ) (t + 1) z₀).map (lastState z₀) = μ := by
  have := ex_8_8a (Kernel.const Z μ) t
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_lastState z₀ (t + 1)),
    hist_succ_lintegral_last _ t z₀ (f := fun h => f (lastState z₀ h))
      (hf.comp (measurable_lastState z₀ (t + 1)))]
  simp only [lastState_snoc, Kernel.const_apply, lintegral_const, measure_univ, mul_one]

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Policy functions and transition functions

SLP §9.6, pp. 283–287.

* **Theorem 9.13** (`theorem_9_13`): for a measurable policy `g : S → X`,
  `P[(x, z), A × B] = Q(z, B)` if `g(x, z) ∈ A` and `0` otherwise defines a unique transition
  function on `S = X × Z` (`policyKernel`, `δ_{g(s)} ⊗ Q(z, ·)`).
* **Exercise 9.15** (`ex_9_15a`, `ex_9_15b`): `∫ f dP[(x, z), ·] = ∫ f(g(x, z), z′) Q(z, dz′)` for
  nonnegative measurable and for `P`-integrable `f`.
* **Theorem 9.14** (`theorem_9_14`): if `Q` satisfies Assumption 9.5 (`M` preserves bounded
  continuous functions, Lemma 9.5) and `g` is continuous, `P` has the Feller property.
* **Exercise 9.17** (`ex_9_17a`, `ex_9_17b`): in the second formulation,
  `P[(x, z), A × B] = Q[z, B ∩ H(x, z, A)]` with `H(x, z, A) = {z′ : φ[x, g(x, z), z′] ∈ A}`
  defines a transition function (`policyKernel'`); it is Feller if `g` is continuous and a
  selection from `Γ` and `φ` is continuous on `D × Z` (Lemma 9.5′).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- The transition function of the state `(x, z)` under the policy `g`: `δ_{g(x, z)} ⊗ Q(z, ·)`. -/
noncomputable def policyKernel (Q : Kernel Z Z) {g : X × Z → X} (hg : Measurable g) :
    Kernel (X × Z) (X × Z) :=
  Kernel.deterministic g hg ×ₖ Q.comap Prod.snd measurable_snd

theorem policyKernel_apply (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X}
    (hg : Measurable g) (s : X × Z) :
    policyKernel Q hg s = (Q s.2).map (Prod.mk (g s)) := by
  rw [policyKernel, Kernel.prod_apply, Kernel.deterministic_apply, Kernel.comap_apply,
    Measure.dirac_prod]

open Classical in
/-- **Theorem 9.13.** For measurable `g : S → X`, `P[(x, z), A × B] = Q(z, B)` if `g(x, z) ∈ A`
and `0` otherwise defines a transition function on `(S, 𝒮)`, and it is the only one with these
values on measurable rectangles. -/
theorem theorem_9_13 (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g) :
    IsMarkovKernel (policyKernel Q hg) ∧
      (∀ x z A B, MeasurableSet A → MeasurableSet B →
        policyKernel Q hg (x, z) (A ×ˢ B) = if g (x, z) ∈ A then Q z B else 0) ∧
      ∀ P : Kernel (X × Z) (X × Z), IsMarkovKernel P →
        (∀ x z A B, MeasurableSet A → MeasurableSet B →
          P (x, z) (A ×ˢ B) = if g (x, z) ∈ A then Q z B else 0) → P = policyKernel Q hg := by
  have hval : ∀ x z A B, MeasurableSet A → MeasurableSet B →
      policyKernel Q hg (x, z) (A ×ˢ B) = if g (x, z) ∈ A then Q z B else 0 := by
    intro x z A B hA hB
    rw [policyKernel, Kernel.prod_apply_prod, Kernel.deterministic_apply' _ _ hA,
      Kernel.comap_apply]
    by_cases h : g (x, z) ∈ A <;> simp [h]
  have hM : IsMarkovKernel (policyKernel Q hg) :=
    inferInstanceAs (IsMarkovKernel (Kernel.deterministic g hg ×ₖ _))
  refine ⟨hM, hval, fun P hP hval' => ?_⟩
  ext ⟨x, z⟩ : 1
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ (by simp)
  rintro _ ⟨A, hA, B, hB, rfl⟩
  rw [hval' x z A B hA hB, hval x z A B hA hB]

/-- **Exercise 9.15a.** For nonnegative measurable `f`,
`∫ f(x′, z′) P[(x, z), dx′ × dz′] = ∫ f[g(x, z), z′] Q(z, dz′)`. -/
theorem ex_9_15a (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g)
    {f : X × Z → ℝ≥0∞} (hf : Measurable f) (s : X × Z) :
    ∫⁻ p, f p ∂policyKernel Q hg s = ∫⁻ z', f (g s, z') ∂Q s.2 := by
  rw [policyKernel_apply, lintegral_map hf measurable_prodMk_left]

/-- **Exercise 9.15b.** The same equality for `P[(x, z), ·]`-integrable `f`. -/
theorem ex_9_15b (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g)
    {f : X × Z → ℝ} (s : X × Z) (hf : Integrable f (policyKernel Q hg s)) :
    ∫ p, f p ∂policyKernel Q hg s = ∫ z', f (g s, z') ∂Q s.2 := by
  rw [policyKernel_apply] at hf ⊢
  rw [integral_map measurable_prodMk_left.aemeasurable hf.aestronglyMeasurable]

/-- **Theorem 9.14.** If `M` maps bounded continuous functions on `X × Z` to continuous functions
(Assumption 9.5 via Lemma 9.5) and `g` is continuous, `P` has the Feller property:
`(M_P f)(x, z) = (M_Q f)[g(x, z), z]`. -/
theorem theorem_9_14 [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X]
    [OpensMeasurableSpace Z] [SecondCountableTopologyEither X Z] (Q : Kernel Z Z)
    [IsMarkovKernel Q] (hQ : PreservesBC X Q) {g : X × Z → X} (hgc : Continuous g) :
    IsFeller (policyKernel Q hgc.measurable) := by
  intro f hf hb
  have := (theorem_9_13 Q hgc.measurable).1
  have heq : markovOpR (policyKernel Q hgc.measurable) f = fun s => mop Q f (g s, s.2) := by
    funext s
    obtain ⟨B, hB⟩ := hb
    rw [markovOpR, ex_9_15b Q hgc.measurable s (integrable_of_abs_le hf.measurable hB)]
    rfl
  rw [heq]
  exact (hQ f hf hb).comp (hgc.prodMk continuous_snd)

variable {Y : Type*} [MeasurableSpace Y]

/-- The transition function of `(x, z)` in the second formulation: `z′ ~ Q(z, ·)` and
`x′ = φ[x, g(x, z), z′]`. -/
noncomputable def policyKernel' (Q : Kernel Z Z) (φ : X × Y × Z → X) (g : X × Z → Y) :
    Kernel (X × Z) (X × Z) :=
  (Kernel.deterministic id measurable_id ×ₖ Q.comap Prod.snd measurable_snd).map
    fun p => (φ (p.1.1, g p.1, p.2), p.2)

theorem measurable_policy' {φ : X × Y × Z → X} (hφ : Measurable φ) {g : X × Z → Y}
    (hg : Measurable g) : Measurable fun p : (X × Z) × Z => (φ (p.1.1, g p.1, p.2), p.2) :=
  (hφ.comp (measurable_fst.fst.prodMk ((hg.comp measurable_fst).prodMk measurable_snd))).prodMk
    measurable_snd

theorem policyKernel'_apply (Q : Kernel Z Z) [IsMarkovKernel Q] {φ : X × Y × Z → X}
    (hφ : Measurable φ) {g : X × Z → Y} (hg : Measurable g) (s : X × Z) :
    policyKernel' Q φ g s = (Q s.2).map fun z' => (φ (s.1, g s, z'), z') := by
  rw [policyKernel', Kernel.map_apply _ (measurable_policy' hφ hg), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.comap_apply, Measure.dirac_prod,
    Measure.map_map (measurable_policy' hφ hg) measurable_prodMk_left]
  rfl

/-- **Exercise 9.17a.** `P[(x, z), A × B] = Q[z, B ∩ H(x, z, A)]`, with
`H(x, z, A) = {z′ : φ[x, g(x, z), z′] ∈ A}`, defines a transition function on `(S, 𝒮)`. -/
theorem ex_9_17a (Q : Kernel Z Z) [IsMarkovKernel Q] {φ : X × Y × Z → X} (hφ : Measurable φ)
    {g : X × Z → Y} (hg : Measurable g) :
    IsMarkovKernel (policyKernel' Q φ g) ∧
      ∀ x z A B, MeasurableSet A → MeasurableSet B →
        policyKernel' Q φ g (x, z) (A ×ˢ B) = Q z (B ∩ {z' | φ (x, g (x, z), z') ∈ A}) := by
  refine ⟨by unfold policyKernel'; exact Kernel.IsMarkovKernel.map _ (measurable_policy' hφ hg),
    fun x z A B hA hB => ?_⟩
  have hm : Measurable fun z' => (φ ((x, z).1, g (x, z), z'), z') :=
    (hφ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).prodMk
      measurable_id
  rw [policyKernel'_apply Q hφ hg, Measure.map_apply hm (hA.prod hB)]
  congr 1
  ext z'
  simp [and_comm]

/-- **Exercise 9.17b.** Under Assumptions 9.4, 9.5 (on `D × Z`), 9.16 and 9.17, if `g` is
continuous and a selection from `Γ`, then `P` has the Feller property:
`(M_P f)(x, z) = ∫ f[φ(x, g(x, z), z′), z′] Q(z, dz′)` is continuous by Lemma 9.5′. -/
theorem ex_9_17b {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [BorelSpace Y]
    [OpensMeasurableSpace (X × Z)] (M : Model X Y Z) [IsMarkovKernel M.Q] (hφm : Measurable M.φ)
    (hφc : ContinuousOn (fun q : (X × Y) × Z => M.φ (q.1.1, q.1.2, q.2)) (domD M ×ˢ univ))
    (hQ : PreservesBC (domD M) M.Q) {g : X × Z → Y} (hgc : Continuous g)
    (hgΓ : ∀ s, g s ∈ M.Γ s) : IsFeller (policyKernel' M.Q M.φ g) := by
  intro f hf hb
  have hcont := contExp_of_preservesBC M hφc hQ f hf hb
  have heq : markovOpR (policyKernel' M.Q M.φ g) f =
      fun s => ∫ z', f (M.φ (s.1, g s, z'), z') ∂M.Q s.2 := by
    funext s
    have hm : Measurable fun z' => (M.φ (s.1, g s, z'), z') :=
      (hφm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).prodMk
        measurable_id
    rw [markovOpR, policyKernel'_apply M.Q hφm hgc.measurable,
      integral_map hm.aemeasurable hf.measurable.aestronglyMeasurable]
  rw [heq]
  exact hcont.comp_continuous ((continuous_fst.prodMk hgc).prodMk continuous_snd)
    fun s => ⟨mem_domD M (hgΓ s), mem_univ _⟩

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The one-sector model of optimal growth under uncertainty

SLP §10.1, pp. 288–290: `sup E Σ βᵗ U[z_t f(x_t) − x_{t+1}]` subject to
`0 ≤ x_{t+1} ≤ z_t f(x_t)`, on the capital stocks `X = [0, x̄]` and the shocks `Z = [1, z̄]`
(Assumption (Z1)), where `x̄ = z̄ f(x̄)`. The shocks follow any Markov transition `Q` with the
Feller property: this covers the i.i.d. shocks of (Z2) (`Q(z, ·) = λ`) and the Markov shocks of
(Z3), so parts (a)–(c) are proved once for both, as Exercise 10.1f asks.

* `GrowthHyp`: (U1)–(U3), (T1)–(T3), (Z1) and `z̄ f(x̄) ≤ x̄`; concavity, (U4) and (T4), is
  assumed where it is used.
* `growthΓ`, `growthF`, `growthModel`: `Γ(x, z) = {y ∈ X : y ≤ z f(x)}` and
  `F(x, y, z) = U[z f(x) − y]` in the first formulation of Chapter 9.
* `growth_boundedDP`: the hypotheses of §9.2 hold.
* `exists_measurableSelection_Icc`: a compact-valued u.h.c. correspondence into an interval has a
  measurable selection (its largest element).
* **Exercise 10.1a** (`ex_10_1a`): the feasible plans, and the value of a plan as the convergent
  sum `Σ βᵗ ∫ U[z_t f(x_t) − x_{t+1}] dμᵗ`.
* **Exercise 10.1b** (`ex_10_1b`): there is a unique bounded continuous solution `v` of (2), its
  policy correspondence `G` is nonempty, compact-valued and u.h.c., `v = v*`, some plan generated
  by `G` is optimal, and every optimal plan follows `G` almost surely (Theorem 9.4, corrected).
* **Exercise 10.1c** (`ex_10_1c`): `v(·, z)` is strictly increasing and strictly concave and `G`
  is a continuous function `g`. (T4) only asks for `f` concave, and then Assumption 9.10 (strict
  concavity of `F` in `x`) fails, so Theorem 9.8 does not apply. The conclusion holds anyway
  (`growth_strictConcave`): along a chord on which `v(·, z)` were affine, consumption would be
  constant, so the chord would be carried to affine chords of `v(·, z′)` with `β` times the rise;
  the supremum of the rises would satisfy `S ≤ βS`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- (U1)–(U3), (T1)–(T3) and (Z1) of SLP §§5.1 and 10.1. The book takes `x̄ = z̄ f(x̄)` (p. 289);
only `z̄ f(x̄) ≤ x̄` is used, which says that `X = [0, x̄]` is never left. -/
structure GrowthHyp (U f : ℝ → ℝ) (β xbar zbar : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  U_cont : ContinuousOn U (Ici 0)
  U_mono : StrictMonoOn U (Ici 0)
  f_cont : ContinuousOn f (Ici 0)
  f_zero : f 0 = 0
  f_mono : StrictMonoOn f (Ici 0)
  zbar_gt : 1 < zbar
  xbar_pos : 0 < xbar
  xbar_maintain : zbar * f xbar ≤ xbar

variable {U f : ℝ → ℝ} {β xbar zbar : ℝ}

/-- `Γ(x, z) = {y ∈ [0, x̄] : y ≤ z f(x)}`. -/
def growthΓ (f : ℝ → ℝ) (xbar zbar : ℝ) (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) :
    Set (Icc (0 : ℝ) xbar) :=
  {y | y.1 ≤ s.2.1 * f s.1.1}

/-- `F(x, y, z) = U[z f(x) − y]`, with consumption clamped at `0` off the graph of `Γ`. -/
def growthF (U f : ℝ → ℝ) (xbar zbar : ℝ)
    (p : Icc (0 : ℝ) xbar × Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) : ℝ :=
  U (max (p.2.2.1 * f p.1.1 - p.2.1.1) 0)

/-- The growth model in the first formulation of Chapter 9. -/
abbrev growthModel (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) (U f : ℝ → ℝ)
    (β xbar : ℝ) : Model (Icc (0 : ℝ) xbar) (Icc (0 : ℝ) xbar) (Icc (1 : ℝ) zbar) :=
  Model.first Q (growthΓ f xbar zbar) (growthF U f xbar zbar) β

theorem GrowthHyp.f_nonneg (h : GrowthHyp U f β xbar zbar) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have := h.f_mono.monotoneOn (mem_Ici.2 le_rfl : (0 : ℝ) ∈ Ici 0) hx hx
  rwa [h.f_zero] at this

theorem GrowthHyp.zf_nonneg (h : GrowthHyp U f β xbar zbar)
    (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) : 0 ≤ s.2.1 * f s.1.1 :=
  mul_nonneg (by linarith [s.2.2.1]) (h.f_nonneg s.1.2.1)

/-- Output never exceeds `x̄`: `z f(x) ≤ z̄ f(x̄) = x̄`. -/
theorem GrowthHyp.zf_le (h : GrowthHyp U f β xbar zbar)
    (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) : s.2.1 * f s.1.1 ≤ xbar := by
  have h1 : f s.1.1 ≤ f xbar := h.f_mono.monotoneOn s.1.2.1 h.xbar_pos.le s.1.2.2
  calc s.2.1 * f s.1.1 ≤ zbar * f xbar :=
        mul_le_mul s.2.2.2 h1 (h.f_nonneg s.1.2.1) (by linarith [h.zbar_gt])
    _ ≤ xbar := h.xbar_maintain

theorem GrowthHyp.continuous_zf (h : GrowthHyp U f β xbar zbar) :
    Continuous fun s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar => s.2.1 * f s.1.1 :=
  (continuous_subtype_val.comp continuous_snd).mul
    (h.f_cont.comp_continuous (continuous_subtype_val.comp continuous_fst) fun s => s.1.2.1)

theorem GrowthHyp.continuous_F (h : GrowthHyp U f β xbar zbar) :
    Continuous (growthF U f xbar zbar) :=
  h.U_cont.comp_continuous ((((continuous_subtype_val.comp continuous_snd.snd).mul
    (h.f_cont.comp_continuous (continuous_subtype_val.comp continuous_fst) fun p => p.1.2.1)).sub
    (continuous_subtype_val.comp continuous_snd.fst)).max continuous_const)
    fun _ => mem_Ici.2 (le_max_right _ _)

theorem GrowthHyp.bddF (h : GrowthHyp U f β xbar zbar) :
    ∃ B, ∀ p, |growthF U f xbar zbar p| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn h.continuous_F.continuousOn
  exact ⟨B, fun p => by simpa [Real.norm_eq_abs] using hB p (mem_univ _)⟩

/-- On the graph, `F(x, y, z) = U[z f(x) − y]`. -/
theorem growthF_of_mem {x y : Icc (0 : ℝ) xbar} {z : Icc (1 : ℝ) zbar}
    (hy : y ∈ growthΓ f xbar zbar (x, z)) :
    growthF U f xbar zbar (x, y, z) = U (z.1 * f x.1 - y.1) := by
  have : 0 ≤ z.1 * f x.1 - y.1 := sub_nonneg.2 hy
  simp only [growthF, max_eq_left this]

/-- The correspondence `s ↦ {y ∈ [0, x̄] : y ≤ c(s)}`, for continuous `c ≥ 0`, is l.h.c. -/
theorem isLHC_Icc_le {S : Type*} [MetricSpace S] {c : S → ℝ} (hc : Continuous c)
    (h0 : ∀ s, 0 ≤ c s) (hx : 0 ≤ xbar) (s : S) :
    IsLHC (fun s => {y : Icc (0 : ℝ) xbar | y.1 ≤ c s}) s := by
  refine ⟨⟨⟨0, le_rfl, hx⟩, h0 s⟩, fun y hy xs hxs => ?_⟩
  refine ⟨0, fun n => ⟨min y.1 (c (xs n)), le_min y.2.1 (h0 _), (min_le_left _ _).trans y.2.2⟩,
    fun n _ => show min y.1 (c (xs n)) ≤ c (xs n) from min_le_right _ _, ?_⟩
  have hlim := (tendsto_const_nhds (x := y.1)).min ((hc.tendsto s).comp hxs)
  rw [min_eq_left hy] at hlim
  exact tendsto_subtype_rng.2 hlim

/-- The correspondence `s ↦ {y ∈ [0, x̄] : y ≤ c(s)}`, for continuous `c ≥ 0`, is u.h.c. -/
theorem isUHC_Icc_le {S : Type*} [MetricSpace S] {c : S → ℝ} (hc : Continuous c)
    (h0 : ∀ s, 0 ≤ c s) (hx : 0 ≤ xbar) (s : S) :
    IsUHC (fun s => {y : Icc (0 : ℝ) xbar | y.1 ≤ c s}) s := by
  refine ⟨⟨⟨0, le_rfl, hx⟩, h0 s⟩, fun xs hxs ys hys => ?_⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
  refine ⟨y, ?_, φ, hφ, hlim⟩
  exact le_of_tendsto_of_tendsto ((continuous_subtype_val.tendsto y).comp hlim)
    ((hc.tendsto s).comp (hxs.comp hφ.tendsto_atTop)) (Eventually.of_forall fun n => hys (φ n))

/-- The hypotheses of §9.2 hold for the growth model (Exercise 10.1b; Exercise 10.1f for Markov
shocks): `Γ` is nonempty, compact-valued and continuous, `F` is bounded and continuous, and
Lemma 9.5 applies because `Z` is compact and `Q` is Feller. -/
theorem growth_boundedDP (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q) :
    BoundedDP (growthModel Q U f β xbar) :=
  ⟨fun s => ⟨⟨0, le_rfl, h.xbar_pos.le⟩, h.zf_nonneg s⟩,
    fun _ => IsClosed.isCompact (isClosed_le continuous_subtype_val continuous_const),
    isLHC_Icc_le h.continuous_zf h.zf_nonneg h.xbar_pos.le,
    isUHC_Icc_le h.continuous_zf h.zf_nonneg h.xbar_pos.le, h.continuous_F.continuousOn,
    ⟨h.bddF.choose, fun p _ => h.bddF.choose_spec p⟩, h.β_pos, h.β_lt,
    continuous_fst.snd.continuousOn, contExp_first Q _ _ β (lemma_9_5_compact Q hQ)⟩

/-- **Measurable selection into an interval.** A nonempty, compact-valued, u.h.c. correspondence
`G : S ⇉ [a, b]` has a measurable selection: `g(s) = max G(s)`, since
`{s : max G(s) ≥ x} = {s : G(s) ∩ [x, ∞) ≠ ∅}` is closed. -/
theorem exists_measurableSelection_Icc {S : Type*} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] {a b : ℝ} {G : S → Set (Icc a b)} (hu : ∀ s, IsUHC G s)
    (hc : ∀ s, IsCompact (G s)) : ∃ g : S → Icc a b, Measurable g ∧ ∀ s, g s ∈ G s := by
  set m : S → ℝ := fun s => sSup (Subtype.val '' G s)
  have hmem : ∀ s, m s ∈ Subtype.val '' G s := fun s =>
    ((hc s).image continuous_subtype_val).sSup_mem ((hu s).1.image _)
  have hle : ∀ s, ∀ y ∈ G s, y.1 ≤ m s := fun s y hy =>
    le_csSup ((hc s).image continuous_subtype_val).bddAbove ⟨y, hy, rfl⟩
  have hmeas : Measurable m := by
    refine measurable_of_Ici fun x => (IsSeqClosed.isClosed fun ss s hss hlim => ?_).measurableSet
    choose ys hys hysv using fun n => hmem (ss n)
    obtain ⟨y, hy, φ, hφ, hylim⟩ := (hu s).2 ss hlim ys hys
    have hx : x ≤ y.1 := ge_of_tendsto ((continuous_subtype_val.tendsto y).comp hylim)
      (Eventually.of_forall fun n => by
        change x ≤ (ys (φ n)).1
        rw [hysv]
        exact hss (φ n))
    exact hx.trans (hle s y hy)
  have hgm : ∀ s, m s ∈ Icc a b := fun s => by
    obtain ⟨y, -, hy⟩ := hmem s
    rw [← hy]
    exact y.2
  refine ⟨fun s => ⟨m s, hgm s⟩, hmeas.subtype_mk, fun s => ?_⟩
  obtain ⟨y, hy, hyv⟩ := hmem s
  have : (⟨m s, hgm s⟩ : Icc a b) = y := Subtype.ext hyv.symm
  change (⟨m s, hgm s⟩ : Icc a b) ∈ G s
  rw [this]
  exact hy

/-- **Exercise 10.1a.** A plan is feasible if and only if each `π_t` is measurable and
`0 ≤ x_{t+1} ≤ z_t f(x_t)`. The expectation in (1) is the convergent sum
`Σ βᵗ ∫ U[z_t f(x_t) − x_{t+1}] μᵗ(z₀, dzᵗ)`. -/
theorem ex_10_1a (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q]
    (s₀ : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) (π : Plan (Icc (0 : ℝ) xbar) (Icc (1 : ℝ) zbar)) :
    (IsFeasible (growthModel Q U f β xbar) s₀ π ↔ (∀ t, Measurable (π t)) ∧
      ∀ t hz, 0 ≤ (π t hz).1 ∧ (π t hz).1 ≤ (state (growthModel Q U f β xbar) s₀ π t hz).2.1 *
        f (state (growthModel Q U f β xbar) s₀ π t hz).1.1) ∧
    (IsFeasible (growthModel Q U f β xbar) s₀ π →
      Summable (fun t => β ^ t * ∫ hz, U ((state (growthModel Q U f β xbar) s₀ π t hz).2.1 *
        f (state (growthModel Q U f β xbar) s₀ π t hz).1.1 - (π t hz).1) ∂hist Q t s₀.2) ∧
      planValue (growthModel Q U f β xbar) s₀ π =
        ((∑' t, β ^ t * ∫ hz, U ((state (growthModel Q U f β xbar) s₀ π t hz).2.1 *
          f (state (growthModel Q U f β xbar) s₀ π t hz).1.1 - (π t hz).1) ∂hist Q t s₀.2 :
            ℝ) : EReal)) := by
  set M := growthModel Q U f β xbar
  refine ⟨⟨fun hπ => ⟨hπ.1, fun t hz => ⟨(π t hz).2.1, hπ.2 t hz⟩⟩,
    fun hπ => ⟨hπ.1, fun t hz => (hπ.2 t hz).2⟩⟩, fun hπ => ?_⟩
  obtain ⟨B, hB⟩ := h.bddF
  have hK : ∀ t hz, |ret M s₀ π t hz| ≤ B := fun t hz => hB _
  have hsum : Summable fun t => M.β ^ t * B :=
    (summable_geometric_of_lt_one h.β_pos.le h.β_lt).mul_right _
  have heq : (fun t => M.β ^ t * ∫ hz, ret M s₀ π t hz ∂hist M.Q t s₀.2) =
      fun t => β ^ t * ∫ hz, U ((state M s₀ π t hz).2.1 * f (state M s₀ π t hz).1.1 -
        (π t hz).1) ∂hist Q t s₀.2 := by
    funext t
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun hz => ?_)
    exact growthF_of_mem (hπ.2 t hz)
  refine ⟨heq ▸ summable_terms M h.β_pos.le s₀ π hK hsum, ?_⟩
  rw [planValue_eq_uR M h.β_pos.le s₀ π hK hsum, uR, heq]

/-- **Exercise 10.1b.** There is a unique bounded continuous `v` satisfying (2), and the policy
correspondence `G` is nonempty, compact-valued and u.h.c. The pair `(v, G)` solves the sequence
problem: `v = v*`, a plan generated by a measurable selection `g` from `G` is optimal from every
`s₀`, and every optimal plan takes its actions in `G` almost surely. -/
theorem ex_10_1b (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q) :
    ∃ v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ,
      bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v ∧
      (∀ w, bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w = w → w = v) ∧
      (∀ s, (policy (growthModel Q U f β xbar) v s).Nonempty ∧
        IsCompact (policy (growthModel Q U f β xbar) v s) ∧
        IsUHC (policy (growthModel Q U f β xbar) v) s) ∧
      (∀ s, vStar (growthModel Q U f β xbar) s = v s) ∧
      (∃ g : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar → Icc (0 : ℝ) xbar, Measurable g ∧
        (∀ s, g s ∈ policy (growthModel Q U f β xbar) v s) ∧
        ∀ s₀, IsFeasible (growthModel Q U f β xbar) s₀
            (genPlan (growthModel Q U f β xbar) s₀ fun _ => g) ∧
          planValue (growthModel Q U f β xbar) s₀
            (genPlan (growthModel Q U f β xbar) s₀ fun _ => g) =
            vStar (growthModel Q U f β xbar) s₀) ∧
      ∀ s₀ π, IsFeasible (growthModel Q U f β xbar) s₀ π →
        planValue (growthModel Q U f β xbar) s₀ π = vStar (growthModel Q U f β xbar) s₀ →
        π 0 Fin.elim0 ∈ policy (growthModel Q U f β xbar) v s₀ ∧
          ∀ t, ∀ᵐ hz ∂hist Q t s₀.2,
            π t hz ∈ policy (growthModel Q U f β xbar) v
              (state (growthModel Q U f β xbar) s₀ π t hz) := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  obtain ⟨v, hv, huniq, -, hG⟩ := ex_9_7b M hb
  obtain ⟨g, hgm, hgG⟩ := exists_measurableSelection_Icc (fun s => (hG s).2.2)
    fun s => (hG s).2.1
  have hφm : Measurable M.φ := measurable_snd.fst
  have hFm : Measurable M.F := h.continuous_F.measurable
  have hopt := fun s₀ => bounded_vStar M hb hφm hFm hv (g := fun _ => g) (fun _ => hgm)
    (fun _ => hgG) s₀
  refine ⟨v, hv, huniq, hG, fun s => (hopt s).2.2, ⟨g, hgm, hgG, fun s₀ =>
    ⟨genPlan_feasible M hφm s₀ (fun _ => hgm) (fun _ s => (hgG s).1), ?_⟩⟩,
    fun s₀ π hπ hopt' => bounded_theorem_9_4 M hb hφm hFm hv (fun s => (hopt s).2.2) hπ hopt'⟩
  rw [(hopt s₀).2.1, (hopt s₀).2.2]

/-! ### Exercise 10.1c: monotonicity, concavity and the policy function -/

/-- **Exercise 10.1c** (monotonicity, Theorem 9.7): `v(·, z)` is strictly increasing. -/
theorem growth_strictMono (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v)
    (z : Icc (1 : ℝ) zbar) : StrictMono fun x => v (x, z) := by
  refine theorem_9_7 Q _ _ β (growth_boundedDP h Q hQ) (fun x x' y z hxx' hy => ?_)
    (fun x x' z hxx' y hy => ?_) hv z
  · have hy' : y.1 ≤ z.1 * f x.1 := hy
    have hfx : f x.1 < f x'.1 := h.f_mono x.2.1 x'.2.1 hxx'
    have hz : 0 < z.1 := by linarith [z.2.1]
    have hlt : z.1 * f x.1 < z.1 * f x'.1 := mul_lt_mul_of_pos_left hfx hz
    rw [growthF_of_mem hy, growthF_of_mem (show y.1 ≤ z.1 * f x'.1 by linarith)]
    exact h.U_mono (show z.1 * f x.1 - y.1 ∈ Ici 0 from sub_nonneg.2 hy')
      (show z.1 * f x'.1 - y.1 ∈ Ici 0 by simp only [mem_Ici]; linarith) (by linarith)
  · have hy' : y.1 ≤ z.1 * f x.1 := hy
    have hfx : f x.1 ≤ f x'.1 := h.f_mono.monotoneOn x.2.1 x'.2.1 hxx'
    exact hy'.trans (mul_le_mul_of_nonneg_left hfx (by linarith [z.2.1]))

/-- With `f` concave, `θ z f(x₀) + (1 − θ) z f(x₁) ≤ z f(θx₀ + (1 − θ)x₁)`. -/
theorem growth_zf_cmb (hf : ConcaveOn ℝ (Ici 0) f) (x₀ x₁ : Icc (0 : ℝ) xbar)
    (z : Icc (1 : ℝ) zbar) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * (z.1 * f x₀.1) + (1 - θ) * (z.1 * f x₁.1) ≤
      z.1 * f (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁).1 := by
  have hc := hf.2 x₀.2.1 x₁.2.1 h0 (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hc
  simp only [cmb, smul_eq_mul]
  have hz : 0 ≤ z.1 := by linarith [z.2.1]
  nlinarith [mul_le_mul_of_nonneg_left hc hz]

theorem cmb_val {x₀ x₁ : Icc (0 : ℝ) xbar} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁).1 = θ * x₀.1 + (1 - θ) * x₁.1 := by
  simp [cmb]

/-- Assumption 9.11: the graph of `Γ(·, z)` is convex. -/
theorem growth_mem_cmb (hf : ConcaveOn ℝ (Ici 0) f) {x₀ x₁ y₀ y₁ : Icc (0 : ℝ) xbar}
    {z : Icc (1 : ℝ) zbar} (hy₀ : y₀ ∈ growthΓ f xbar zbar (x₀, z))
    (hy₁ : y₁ ∈ growthΓ f xbar zbar (x₁, z)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁ ∈
      growthΓ f xbar zbar (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁, z) := by
  have hc := growth_zf_cmb hf x₀ x₁ z h0 h1
  have e0 : y₀.1 ≤ z.1 * f x₀.1 := hy₀
  have e1 : y₁.1 ≤ z.1 * f x₁.1 := hy₁
  change (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁).1 ≤ _
  rw [cmb_val]
  nlinarith

/-- The return is concave on the graph: with `cᵢ = z f(xᵢ) − yᵢ`,
`θU(c₀) + (1 − θ)U(c₁) ≤ U(θc₀ + (1 − θ)c₁) ≤ F(x_θ, y_θ, z)`. -/
theorem growth_F_cmb (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {x₀ x₁ y₀ y₁ : Icc (0 : ℝ) xbar} {z : Icc (1 : ℝ) zbar}
    (hy₀ : y₀ ∈ growthΓ f xbar zbar (x₀, z)) (hy₁ : y₁ ∈ growthΓ f xbar zbar (x₁, z)) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * U (z.1 * f x₀.1 - y₀.1) + (1 - θ) * U (z.1 * f x₁.1 - y₁.1) ≤
        U (θ * (z.1 * f x₀.1 - y₀.1) + (1 - θ) * (z.1 * f x₁.1 - y₁.1)) ∧
      U (θ * (z.1 * f x₀.1 - y₀.1) + (1 - θ) * (z.1 * f x₁.1 - y₁.1)) ≤
        growthF U f xbar zbar (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁,
          cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁, z) := by
  have e0 : 0 ≤ z.1 * f x₀.1 - y₀.1 := sub_nonneg.2 hy₀
  have e1 : 0 ≤ z.1 * f x₁.1 - y₁.1 := sub_nonneg.2 hy₁
  have hc := growth_zf_cmb hf x₀ x₁ z h0 h1
  have hθ : 0 ≤ θ * (z.1 * f x₀.1 - y₀.1) + (1 - θ) * (z.1 * f x₁.1 - y₁.1) := by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  refine ⟨?_, ?_⟩
  · have := hU.2 e0 e1 h0 (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
    simpa only [smul_eq_mul] using this
  · rw [growthF_of_mem (growth_mem_cmb hf hy₀ hy₁ h0 h1)]
    simp only [cmb_val] at hc ⊢
    refine h.U_mono.monotoneOn hθ ?_ ?_
    · simp only [mem_Ici]; nlinarith
    · nlinarith

/-- `T` maps functions concave in `x` to functions concave in `x`. -/
theorem growth_bellman_concave (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {w : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hw : ∀ z, IsConcaveS (convex_Icc 0 xbar) fun x => w (x, z)) (z : Icc (1 : ℝ) zbar) :
    IsConcaveS (convex_Icc 0 xbar) fun x =>
      bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w (x, z) := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  intro x₀ x₁ θ h0 h1
  obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax M hb w (x₀, z)
  obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax M hb w (x₁, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb w (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁, z)
  have hyθ := growth_mem_cmb hf hy₀ hy₁ h0 h1
  have hF := growth_F_cmb h hU hf hy₀ hy₁ h0 h1
  have hE := expV_comb M hb (fun _ _ _ _ _ _ _ _ => rfl) hw hy₀ hy₁ h0 h1 hyθ
  have hm := hmax _ hyθ
  have hβE := mul_le_mul_of_nonneg_left hE h.β_pos.le
  simp only [rhs] at hv₀ hv₁ hm
  dsimp only
  rw [hv₀, hv₁]
  change θ * (growthF U f xbar zbar (x₀, y₀, z) + _) +
    (1 - θ) * (growthF U f xbar zbar (x₁, y₁, z) + _) ≤ _
  rw [growthF_of_mem hy₀, growthF_of_mem hy₁]
  change _ ≤ bellman M hb w (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁, z)
  change _ ≤ M.β * _ at hβE
  linarith [hF.1, hF.2]

/-- **Exercise 10.1c** (concavity): with `U` and `f` concave, `v(·, z)` is concave. -/
theorem growth_concave (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v) :
    ∀ z, IsConcaveS (convex_Icc 0 xbar) fun x => v (x, z) :=
  (corollary_1 (S' := {w | ∀ z, IsConcaveS (convex_Icc 0 xbar) fun x => w (x, z)})
    (S'' := {w | ∀ z, IsConcaveS (convex_Icc 0 xbar) fun x => w (x, z)})
    (bellman_contraction _ (growth_boundedDP h Q hQ)) hv ⟨0, fun _ _ _ _ _ _ => by simp⟩
    (isClosed_concaveX _) (fun _ hw => growth_bellman_concave h hU hf Q hQ hw)
    fun _ hw => growth_bellman_concave h hU hf Q hQ hw).1

/-- `z′ ↦ v(y, z′)` is integrable. -/
theorem integrable_section_v {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] {S : Type*} [TopologicalSpace S] (μ : Measure Z)
    [IsFiniteMeasure μ] (v : S × Z →ᵇ ℝ) (y : S) : Integrable (fun z' => v (y, z')) μ :=
  integrable_of_abs_le (v.continuous.comp (Continuous.prodMk_right y)).measurable fun _ => by
    rw [← Real.norm_eq_abs]; exact v.norm_coe_le_norm _

/-- **The step of the chord argument.** If `v(·, z)` is affine on a chord `[a, b]`, then
consumption is the same at `a` and `b`, the optimal `y_a < y_b`, `v(·, z′)` is affine on
`[y_a, y_b]` for `Q(z, ·)`-almost every `z′`, and
`v(b, z) − v(a, z) = β ∫ [v(y_b, z′) − v(y_a, z′)] Q(z, dz′)`. -/
theorem growth_flat_step (h : GrowthHyp U f β xbar zbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v)
    (hvc : ∀ z, IsConcaveS (convex_Icc 0 xbar) fun x => v (x, z)) {a b : Icc (0 : ℝ) xbar}
    {z : Icc (1 : ℝ) zbar} (hab : a < b) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (heq : v (cmb (convex_Icc 0 xbar) h0.le h1.le a b, z) = θ * v (a, z) + (1 - θ) * v (b, z)) :
    ∃ ya yb : Icc (0 : ℝ) xbar, ya < yb ∧
      (∀ᵐ z' ∂Q z, v (cmb (convex_Icc 0 xbar) h0.le h1.le ya yb, z') =
        θ * v (ya, z') + (1 - θ) * v (yb, z')) ∧
      v (b, z) - v (a, z) = β * ∫ z', (v (yb, z') - v (ya, z')) ∂Q z := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  obtain ⟨ya, hya, hva, -⟩ := exists_bellman_argmax M hb v (a, z)
  obtain ⟨yb, hyb, hvb, -⟩ := exists_bellman_argmax M hb v (b, z)
  obtain ⟨-, -, -, hmax⟩ :=
    exists_bellman_argmax M hb v (cmb (convex_Icc 0 xbar) h0.le h1.le a b, z)
  rw [hv] at hva hvb hmax
  have hyθ := growth_mem_cmb hf hya hyb h0.le h1.le
  have hm := hmax _ hyθ
  have hF := growth_F_cmb h hU.concaveOn hf hya hyb h0.le h1.le
  have hint := integrable_section_v (Q z) v
  have hpt : ∀ z', θ * v (ya, z') + (1 - θ) * v (yb, z') ≤
      v (cmb (convex_Icc 0 xbar) h0.le h1.le ya yb, z') := fun z' =>
    hvc z' ya yb θ h0.le h1.le
  -- the expected values
  set Ea := ∫ z', v (ya, z') ∂Q z
  set Eb := ∫ z', v (yb, z') ∂Q z
  set Eθ := ∫ z', v (cmb (convex_Icc 0 xbar) h0.le h1.le ya yb, z') ∂Q z
  have hI : Integrable (fun z' => θ * v (ya, z') + (1 - θ) * v (yb, z')) (Q z) :=
    ((hint ya).const_mul θ).add ((hint yb).const_mul (1 - θ))
  have hgapE : ∫ z', (v (cmb (convex_Icc 0 xbar) h0.le h1.le ya yb, z') -
      (θ * v (ya, z') + (1 - θ) * v (yb, z'))) ∂Q z = Eθ - (θ * Ea + (1 - θ) * Eb) := by
    rw [integral_sub (hint _) hI,
      integral_add ((hint ya).const_mul θ) ((hint yb).const_mul (1 - θ)), integral_const_mul,
      integral_const_mul]
  have hE0 : 0 ≤ Eθ - (θ * Ea + (1 - θ) * Eb) := by
    rw [← hgapE]
    exact integral_nonneg fun z' => sub_nonneg.2 (hpt z')
  -- the returns
  set ca := z.1 * f a.1 - ya.1
  set cb := z.1 * f b.1 - yb.1
  have hca : 0 ≤ ca := sub_nonneg.2 hya
  have hcb : 0 ≤ cb := sub_nonneg.2 hyb
  have hFa : growthF U f xbar zbar (a, ya, z) = U ca := growthF_of_mem hya
  have hFb : growthF U f xbar zbar (b, yb, z) = U cb := growthF_of_mem hyb
  simp only [rhs, expV] at hva hvb hm
  change v (a, z) = growthF U f xbar zbar (a, ya, z) + β * Ea at hva
  change v (b, z) = growthF U f xbar zbar (b, yb, z) + β * Eb at hvb
  change growthF U f xbar zbar (cmb (convex_Icc 0 xbar) h0.le h1.le a b,
    cmb (convex_Icc 0 xbar) h0.le h1.le ya yb, z) + β * Eθ ≤ _ at hm
  rw [hFa] at hva
  rw [hFb] at hvb
  have hβ := h.β_pos
  -- both gaps vanish
  have hgapF : θ * U ca + (1 - θ) * U cb = U (θ * ca + (1 - θ) * cb) := by
    have := hF.2
    nlinarith [hF.1, mul_nonneg hβ.le hE0]
  have hceq : ca = cb := by
    by_contra hne
    have := hU.2 (show ca ∈ Ici 0 from hca) (show cb ∈ Ici 0 from hcb) hne h0
      (by linarith : (0 : ℝ) < 1 - θ) (by ring)
    simp only [smul_eq_mul] at this
    linarith
  have hEeq : Eθ - (θ * Ea + (1 - θ) * Eb) = 0 := by
    have := hF.2
    nlinarith [hF.1]
  refine ⟨ya, yb, ?_, ?_, ?_⟩
  · have hfab : f a.1 < f b.1 := h.f_mono a.2.1 b.2.1 hab
    have hz : 0 < z.1 := by linarith [z.2.1]
    have := mul_lt_mul_of_pos_left hfab hz
    change ya.1 < yb.1
    have : z.1 * f a.1 - ya.1 = z.1 * f b.1 - yb.1 := hceq
    linarith
  · have hzero := (integral_eq_zero_iff_of_nonneg (fun z' => sub_nonneg.2 (hpt z'))
      ((hint _).sub hI)).1 (by rw [hgapE, hEeq])
    filter_upwards [hzero] with z' hz'
    simp only [Pi.zero_apply] at hz'
    linarith
  · rw [integral_sub (hint yb) (hint ya), hva, hvb, hceq]
    ring

/-- **Exercise 10.1c** (strict concavity, for `f` only concave as in (T4)): `v(·, z)` is strictly
concave. If `v(·, z)` were affine on some chord, let `S` be the supremum of the rises
`v(b, z) − v(a, z) > 0` over such chords; `growth_flat_step` bounds each rise by `βS`. -/
theorem growth_strictConcave (h : GrowthHyp U f β xbar zbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v)
    (z : Icc (1 : ℝ) zbar) : IsStrictConcaveS (convex_Icc 0 xbar) fun x => v (x, z) := by
  have hvc := growth_concave h hU.concaveOn hf Q hQ hv
  have hmono := growth_strictMono h Q hQ hv
  set D : Set ℝ := {d | ∃ a b : Icc (0 : ℝ) xbar, ∃ z : Icc (1 : ℝ) zbar, ∃ θ : ℝ,
    ∃ h0 : 0 < θ, ∃ h1 : θ < 1, a < b ∧
      v (cmb (convex_Icc 0 xbar) h0.le h1.le a b, z) = θ * v (a, z) + (1 - θ) * v (b, z) ∧
      d = v (b, z) - v (a, z)}
  have hD : D = ∅ := by
    by_contra hne
    obtain ⟨d₀, hd₀⟩ := nonempty_iff_ne_empty.2 hne
    have hbdd : BddAbove D := ⟨2 * ‖v‖, by
      rintro _ ⟨a, b, z, θ, h0, h1, -, -, rfl⟩
      have := v.dist_le_two_norm (b, z) (a, z)
      rw [Real.dist_eq] at this
      exact (le_abs_self _).trans this⟩
    have hle : ∀ d ∈ D, d ≤ β * sSup D := by
      rintro _ ⟨a, b, z, θ, h0, h1, hab, heq, rfl⟩
      obtain ⟨ya, yb, hlt, hae, hdiff⟩ := growth_flat_step h hU hf Q hQ hv hvc hab h0 h1 heq
      rw [hdiff]
      refine mul_le_mul_of_nonneg_left ?_ h.β_pos.le
      have hint := integrable_section_v (Q z) v
      have := integral_mono_ae ((hint yb).sub (hint ya)) (integrable_const (sSup D))
        (hae.mono fun z' hz' => le_csSup hbdd ⟨ya, yb, z', θ, h0, h1, hlt, hz', rfl⟩)
      simpa using this
    have hS : sSup D ≤ β * sSup D := csSup_le ⟨d₀, hd₀⟩ hle
    have hpos : 0 < d₀ := by
      obtain ⟨a, b, z, θ, h0, h1, hab, -, rfl⟩ := hd₀
      exact sub_pos.2 (hmono z hab)
    have := lt_of_lt_of_le hpos (le_csSup hbdd hd₀)
    nlinarith [h.β_lt]
  intro x x' hne θ h0 h1
  refine lt_of_le_of_ne (hvc z x x' θ h0.le h1.le) fun heq => ?_
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hmem : v (x', z) - v (x, z) ∈ D := ⟨x, x', z, θ, h0, h1, hlt, heq.symm, rfl⟩
    rw [hD] at hmem
    exact hmem
  · have h0' : 0 < 1 - θ := by linarith
    have h1' : 1 - θ < 1 := by linarith
    have hc : cmb (convex_Icc 0 xbar) h0'.le h1'.le x' x =
        cmb (convex_Icc 0 xbar) h0.le h1.le x x' := by
      ext1
      rw [cmb_val, cmb_val]
      ring
    dsimp only at heq
    have hmem : v (x, z) - v (x', z) ∈ D := ⟨x', x, z, 1 - θ, h0', h1', hlt, by
      rw [hc, ← heq]; ring, rfl⟩
    rw [hD] at hmem
    exact hmem

/-- `y ↦ ∫ v(y, z′) μ(dz′)` is strictly concave when each `v(·, z′)` is. -/
theorem strictConcave_integral {μ : Measure (Icc (1 : ℝ) zbar)} [IsProbabilityMeasure μ]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : ∀ z, IsStrictConcaveS (convex_Icc 0 xbar) fun x => v (x, z)) :
    IsStrictConcaveS (convex_Icc 0 xbar) fun y => ∫ z', v (y, z') ∂μ := by
  intro x x' hne θ h0 h1
  have hint := integrable_section_v μ v
  dsimp only
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint x).const_mul θ) ((hint x').const_mul _)]
  exact integral_lt_integral_of_lt (((hint x).const_mul θ).add ((hint x').const_mul _))
    (hint _) fun z' => hv z' x x' hne θ h0 h1

/-- With `U` concave and `W` strictly concave, `y ↦ U(c − y) + βW(y)` has at most one maximizer
on `{y ∈ [0, x̄] : y ≤ c}`. -/
theorem growth_argmax_unique (hU : ConcaveOn ℝ (Ici 0) U) (hβ : 0 < β)
    {W : Icc (0 : ℝ) xbar → ℝ} (hW : IsStrictConcaveS (convex_Icc 0 xbar) W) {c : ℝ}
    {y₁ y₂ : Icc (0 : ℝ) xbar} (h₁ : y₁.1 ≤ c) (h₂ : y₂.1 ≤ c)
    (hm₁ : ∀ y : Icc (0 : ℝ) xbar, y.1 ≤ c →
      U (max (c - y.1) 0) + β * W y ≤ U (max (c - y₁.1) 0) + β * W y₁)
    (hm₂ : ∀ y : Icc (0 : ℝ) xbar, y.1 ≤ c →
      U (max (c - y.1) 0) + β * W y ≤ U (max (c - y₂.1) 0) + β * W y₂) : y₁ = y₂ := by
  by_contra hne
  have hh0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hh1 : (1 / 2 : ℝ) < 1 := by norm_num
  set m := cmb (convex_Icc 0 xbar) hh0.le hh1.le y₁ y₂
  have hmv : m.1 = 1 / 2 * y₁.1 + (1 - 1 / 2) * y₂.1 := cmb_val _ _
  have hmc : m.1 ≤ c := by rw [hmv]; linarith
  have hWm := hW y₁ y₂ hne (1 / 2) hh0 hh1
  have hUm := hU.2 (show c - y₁.1 ∈ Ici 0 from sub_nonneg.2 h₁)
    (show c - y₂.1 ∈ Ici 0 from sub_nonneg.2 h₂) hh0.le hh0.le (by norm_num)
  simp only [smul_eq_mul] at hUm
  have e : 1 / 2 * (c - y₁.1) + 1 / 2 * (c - y₂.1) = c - m.1 := by rw [hmv]; ring
  rw [e] at hUm
  have h1' := hm₁ m hmc
  have h12 := hm₁ y₂ h₂
  have h21 := hm₂ y₁ h₁
  rw [max_eq_left (sub_nonneg.2 hmc), max_eq_left (sub_nonneg.2 h₁)] at h1'
  rw [max_eq_left (sub_nonneg.2 h₁), max_eq_left (sub_nonneg.2 h₂)] at h12 h21
  nlinarith [mul_lt_mul_of_pos_left hWm hβ]

/-- The objective of (2): `U[z f(x) − y] + β ∫ v(y, z′) Q(z, dz′)`. -/
theorem growth_objG (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    (v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar → ℝ) (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar)
    (y : Icc (0 : ℝ) xbar) :
    objG (growthModel Q U f β xbar) v (s, y) =
      U (max (s.2.1 * f s.1.1 - y.1) 0) + β * ∫ z', v (y, z') ∂Q s.2 := rfl

/-- **Exercise 10.1c.** With `U` strictly concave (U4) and `f` concave (T4), `v(·, z)` is strictly
increasing and strictly concave, and the policy correspondence is a continuous single-valued
function `g`. -/
theorem ex_10_1c [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar zbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v) :
    (∀ z, StrictMono fun x => v (x, z)) ∧
      (∀ z, IsStrictConcaveS (convex_Icc 0 xbar) fun x => v (x, z)) ∧
      UniqueArgmax (growthΓ f xbar zbar) (objG (growthModel Q U f β xbar) v) ∧
      (∀ s, policy (growthModel Q U f β xbar) v s =
        {argmaxFn (growthΓ f xbar zbar) (objG (growthModel Q U f β xbar) v) s}) ∧
      Continuous (argmaxFn (growthΓ f xbar zbar) (objG (growthModel Q U f β xbar) v)) := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  have hsc := growth_strictConcave h hU hf Q hQ hv
  have hUA : UniqueArgmax (growthΓ f xbar zbar) (objG M v) := by
    refine ⟨hb.nonempty, hb.compact, hb.lhc, hb.uhc, continuousOn_objG M hb v,
      fun s y₁ hy₁ y₂ hy₂ => ?_⟩
    have hle := fun y (hy : y ∈ growthΓ f xbar zbar s) =>
      le_maxValue (continuousOn_objG M hb v) (hb.compact s) hy
    refine growth_argmax_unique hU.concaveOn h.β_pos
      (W := fun y => ∫ z', v (y, z') ∂Q s.2) (strictConcave_integral hsc) hy₁.1 hy₂.1
      (fun y hy => ?_) (fun y hy => ?_)
    · have := hle y hy
      rw [← hy₁.2, growth_objG, growth_objG] at this
      exact this
    · have := hle y hy
      rw [← hy₂.2, growth_objG, growth_objG] at this
      exact this
  refine ⟨growth_strictMono h Q hQ hv, hsc, hUA, fun s => ?_, hUA.continuous_argmaxFn⟩
  rw [policy_eq_argmax M hb hv]
  exact hUA.argmax_eq s

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The one-sector growth model: the policy function, differentiability, Markov shocks

SLP §10.1, Exercise 10.1d–f, pp. 289–290.

* **Exercise 10.1d** (`ex_10_1d`). With i.i.d. shocks (`Q(z, ·) = λ`, which is Feller:
  `isFeller_const`), `g(x, z) = h[z f(x)]`, where `h` is the continuous policy function of the
  problem in output `s = z f(x)`: `max_{0 ≤ y ≤ s} U(s − y) + β ∫ v(y, z′) λ(dz′)` (`outΓ`,
  `outH`). Both `h` and consumption `s − h(s)` are nondecreasing (by exchange arguments, using
  the strict concavity of `U` and of `v(·, z′)`), so `g` and `c = z f(x) − g` are nondecreasing in
  both arguments. **Correction:** they need not be strictly increasing. With
  `U(c) = 1 − e^{−c}`, `f(x) = 2x/(1 + x)`, `z̄ = 2`, `x̄ = 3`, `β = 1/10` — which satisfy
  (U1)–(U4), (T1)–(T4) and (Z1) — `v(x, z) − v(0, z) ≤ 4x`, so saving is never worth its cost
  at low output: `G(x, z) = {0}` for `x ≤ 1/10`, for any Feller `Q` (`ex_10_1d_counterexample`,
  `ex_10_1d_not_strictMono`). The manual's proof uses the first-order condition, which fails
  at the corner `g = 0`.
* **Exercise 10.1e** (`ex_10_1e`): if `c = z f(x) − g(x, z) > 0`, `U` is differentiable at `c`
  and `f` at an interior `x`, then `v_x = U′(c) z f′(x)`; for interior `z`, `v_z = U′(c) f(x)`.
  Only `c > 0` is needed, not `g > 0`. Both follow from Benveniste–Scheinkman (Theorem 4.10):
  in `x` because `v(·, z)` is concave, in `z` because, with i.i.d. shocks, `v(x, ·)` is concave
  (`growth_concave_z`).
* **Exercise 10.1f** (`ex_10_1f`): with a Feller `Q`, parts (a)–(c) hold (they are proved for
  any Feller `Q`), and `v_x = U′(c) z f′(x)` still holds (`growth_hasDerivAt_x`). If `Q` is
  monotone, `v(x, ·)` is nondecreasing, and strictly increasing for `x > 0`. That `g` is then
  increasing in `z` is not established: the manual compares `∫ v′(g, z′) Q(z, dz′)` across
  different measures `Q(z, ·)`, `Q(ẑ, ·)`, which concavity of `v(·, z′)` does not order.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {U f : ℝ → ℝ} {β xbar zbar : ℝ}

/-- I.i.d. shocks (Assumption (Z2)): `Q(z, ·) = λ` has the Feller property. -/
theorem isFeller_const {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] (lam : Measure Z) :
    IsFeller (Kernel.const Z lam) := fun f _ _ => by
  have : markovOpR (Kernel.const Z lam) f = fun _ => ∫ z', f z' ∂lam := by
    funext z
    simp [markovOpR, Kernel.const_apply]
  rw [this]
  exact continuous_const

/-- `y ↦ ∫ v(y, z′) μ(dz′)` is continuous. -/
theorem continuous_integral_section {S Z : Type*} [TopologicalSpace S] [FirstCountableTopology S]
    [TopologicalSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (v : S × Z →ᵇ ℝ) : Continuous fun y => ∫ z', v (y, z') ∂μ :=
  continuous_of_dominated (bound := fun _ => ‖v‖)
    (fun y => (v.continuous.comp (Continuous.prodMk_right y)).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun _ => v.norm_coe_le_norm _) (integrable_const _)
    (Eventually.of_forall fun z' => v.continuous.comp (Continuous.prodMk_left z'))

/-- **The exchange inequality.** For `φ` strictly concave, `p < q < t` and `p + t = q + r`,
`φ(p) + φ(t) < φ(q) + φ(r)`. -/
theorem strictConcave_exchange {S : Set ℝ} {φ : ℝ → ℝ} (hφ : StrictConcaveOn ℝ S φ)
    {p q r t : ℝ} (hp : p ∈ S) (ht : t ∈ S) (hpq : p < q) (hqt : q < t) (hsum : p + t = q + r) :
    φ p + φ t < φ q + φ r := by
  have hpt : 0 < t - p := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = (t - q) / (t - p) := ⟨_, rfl⟩
  have hat : a * (t - p) = t - q := by rw [ha]; exact div_mul_cancel₀ _ hpt.ne'
  have ha0 : 0 < a := by rw [ha]; exact div_pos (by linarith) hpt
  have ha1 : 0 < 1 - a := by
    have : a * (t - p) < 1 * (t - p) := by rw [hat]; linarith
    linarith [lt_of_mul_lt_mul_right this hpt.le]
  have hq : a • p + (1 - a) • t = q := by
    simp only [smul_eq_mul]; linear_combination (-1 : ℝ) * hat
  have hr : (1 - a) • p + a • t = r := by
    simp only [smul_eq_mul]; linear_combination hat + hsum
  have h1 := hφ.2 hp ht (hpq.trans hqt).ne ha0 ha1 (by ring)
  have h2 := hφ.2 hp ht (hpq.trans hqt).ne ha1 ha0 (by ring)
  rw [hq] at h1
  rw [hr] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-- A strictly concave function on `S` is strictly concave on `S ⊆ E` after extension. -/
theorem strictConcaveOn_liftS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    {hS : Convex ℝ S} {W : S → ℝ} (hW : IsStrictConcaveS hS W) :
    StrictConcaveOn ℝ S (liftS W) := by
  refine ⟨hS, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hmem : a • x + (1 - a) • y ∈ S := hS hx hy ha.le hb.le hab
  rw [liftS_of_mem W hx, liftS_of_mem W hy, liftS_of_mem W hmem, smul_eq_mul, smul_eq_mul]
  exact hW ⟨x, hx⟩ ⟨y, hy⟩ (fun h => hxy (congrArg Subtype.val h)) a ha (by linarith)

/-! ### Exercise 10.1d: the policy function under i.i.d. shocks -/

/-- `Γ′(s) = {y ∈ X : y ≤ s}`: the constraint of the problem in output `s`. -/
def outΓ (xbar : ℝ) (s : Icc (0 : ℝ) xbar) : Set (Icc (0 : ℝ) xbar) := {y | y.1 ≤ s.1}

/-- The objective `U(s − y) + β ∫ v(y, z′) λ(dz′)` of the problem in output. -/
noncomputable def outH (U : ℝ → ℝ) (β : ℝ) (lam : Measure (Icc (1 : ℝ) zbar))
    (v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar → ℝ) (p : Icc (0 : ℝ) xbar × Icc (0 : ℝ) xbar) :
    ℝ :=
  U (max (p.1.1 - p.2.1) 0) + β * ∫ z', v (p.2, z') ∂lam

/-- Output `s(x, z) = z f(x)`, a point of `X`. -/
def outS (h : GrowthHyp U f β xbar zbar) (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) :
    Icc (0 : ℝ) xbar :=
  ⟨s.2.1 * f s.1.1, h.zf_nonneg s, h.zf_le s⟩

/-- The problem in output has a unique maximizer `h(s)`, continuous in `s` (Theorem 3.6). -/
theorem outH_uniqueArgmax (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : ∀ z, IsStrictConcaveS (convex_Icc 0 xbar) fun x => v (x, z)) :
    UniqueArgmax (outΓ xbar) (outH U β lam v) := by
  have hc : Continuous (outH U β lam v) :=
    (h.U_cont.comp_continuous (((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd)).max continuous_const)
      fun _ => mem_Ici.2 (le_max_right _ _)).add
      (continuous_const.mul ((continuous_integral_section lam v).comp continuous_snd))
  have hcpt : ∀ s, IsCompact (outΓ xbar s) := fun _ =>
    IsClosed.isCompact (isClosed_le continuous_subtype_val continuous_const)
  refine ⟨fun s => ⟨⟨0, le_rfl, h.xbar_pos.le⟩, s.2.1⟩, hcpt,
    isLHC_Icc_le continuous_subtype_val (fun s => s.2.1) h.xbar_pos.le,
    isUHC_Icc_le continuous_subtype_val (fun s => s.2.1) h.xbar_pos.le, hc.continuousOn,
    fun s y₁ hy₁ y₂ hy₂ => ?_⟩
  have hle := fun y (hy : y ∈ outΓ xbar s) => le_maxValue hc.continuousOn (hcpt s) hy
  refine growth_argmax_unique hU h.β_pos (W := fun y => ∫ z', v (y, z') ∂lam)
    (strictConcave_integral hv) hy₁.1 hy₂.1 (fun y hy => ?_) (fun y hy => ?_)
  · have := hle y hy
    rw [← hy₁.2] at this
    exact this
  · have := hle y hy
    rw [← hy₂.2] at this
    exact this

/-- Under i.i.d. shocks the maximization in (2) is the problem in output at `s = z f(x)`. -/
theorem growth_argmax_eq_out (h : GrowthHyp U f β xbar zbar) (lam : Measure (Icc (1 : ℝ) zbar))
    (v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar → ℝ) (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) :
    argmax (objG (growthModel (Kernel.const _ lam) U f β xbar) v) (growthΓ f xbar zbar) s =
      argmax (outH U β lam v) (outΓ xbar) (outS h s) := by
  have hobj : ∀ y, objG (growthModel (Kernel.const _ lam) U f β xbar) v (s, y) =
      outH U β lam v (outS h s, y) := fun y => by
    rw [growth_objG, Kernel.const_apply]
    rfl
  simp only [argmax, maxValue, hobj]
  rfl

/-- **Exercise 10.1d.** Under i.i.d. shocks, with (U4) strict and (T4), the policy function is
`g(x, z) = h[z f(x)]` with `h` continuous, and `h` and consumption `s − h(s)` are
nondecreasing; hence `g` and `c(x, z) = z f(x) − g(x, z)` are nondecreasing in `x` and in `z`.
(They need not be strictly increasing: `ex_10_1d_not_strictMono`.) -/
theorem ex_10_1d [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar zbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel (Kernel.const _ lam) U f β xbar)
      (growth_boundedDP h _ (isFeller_const lam)) v = v) :
    (∀ s, argmaxFn (growthΓ f xbar zbar) (objG (growthModel (Kernel.const _ lam) U f β xbar) v) s =
      argmaxFn (outΓ xbar) (outH U β lam v) (outS h s)) ∧
    Continuous (argmaxFn (outΓ xbar) (outH U β lam v)) ∧
    Monotone (argmaxFn (outΓ xbar) (outH U β lam v)) ∧
    Monotone (fun s => s.1 - (argmaxFn (outΓ xbar) (outH U β lam v) s).1) ∧
    (∀ z, Monotone fun x => argmaxFn (growthΓ f xbar zbar)
      (objG (growthModel (Kernel.const _ lam) U f β xbar) v) (x, z)) ∧
    (∀ x, Monotone fun z => argmaxFn (growthΓ f xbar zbar)
      (objG (growthModel (Kernel.const _ lam) U f β xbar) v) (x, z)) ∧
    (∀ z, Monotone fun x => z.1 * f x.1 - (argmaxFn (growthΓ f xbar zbar)
      (objG (growthModel (Kernel.const _ lam) U f β xbar) v) (x, z)).1) ∧
    (∀ x, Monotone fun z => z.1 * f x.1 - (argmaxFn (growthΓ f xbar zbar)
      (objG (growthModel (Kernel.const _ lam) U f β xbar) v) (x, z)).1) := by
  set M := growthModel (Kernel.const _ lam) U f β xbar
  obtain ⟨-, hsc, hUA, -, -⟩ := ex_10_1c h hU hf _ (isFeller_const lam) hv
  have hO := outH_uniqueArgmax h hU.concaveOn lam hsc
  set hs := argmaxFn (outΓ xbar) (outH U β lam v)
  -- `g = h ∘ s`
  have hgs : ∀ s, argmaxFn (growthΓ f xbar zbar) (objG M v) s = hs (outS h s) := fun s => by
    have h1 := hUA.argmax_eq s
    rw [growth_argmax_eq_out h lam v s, hO.argmax_eq] at h1
    exact (Set.singleton_eq_singleton_iff.1 h1).symm
  have hmem : ∀ s, (hs s).1 ≤ s.1 := fun s => (hO.argmaxFn_mem s).1
  have hopt : ∀ s y, y ∈ outΓ xbar s → outH U β lam v (s, y) ≤ outH U β lam v (s, hs s) :=
    fun s y hy => by
      rw [(hO.argmaxFn_mem s).2]
      exact le_maxValue hO.cont (hO.compact s) hy
  have hval : ∀ s y, y.1 ≤ s.1 →
      outH U β lam v (s, y) = U (s.1 - y.1) + β * ∫ z', v (y, z') ∂lam := fun s y hy => by
    simp only [outH, max_eq_left (sub_nonneg.2 hy)]
  have hlt_of : ∀ s s' : Icc (0 : ℝ) xbar, s ≤ s' → s ≠ s' → s.1 < s'.1 := fun s s' hle hne =>
    lt_of_le_of_ne hle fun heq => hne (Subtype.ext heq)
  -- `h` is nondecreasing
  have hmono : Monotone hs := by
    intro s s' hss'
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hlt' : (hs s').1 < (hs s).1 := hlt
    have hss : s.1 < s'.1 := hlt_of s s' hss' fun heq => by subst heq; exact lt_irrefl _ hlt
    have h1 := hopt s (hs s') (show (hs s').1 ≤ s.1 by linarith [hmem s])
    have h2 := hopt s' (hs s) (show (hs s).1 ≤ s'.1 by linarith [hmem s])
    rw [hval s _ (by linarith [hmem s]), hval s _ (hmem s)] at h1
    rw [hval s' _ (by linarith [hmem s]), hval s' _ (hmem s')] at h2
    have := strictConcave_exchange hU (p := s.1 - (hs s).1) (q := s.1 - (hs s').1)
      (r := s'.1 - (hs s).1) (t := s'.1 - (hs s').1) (sub_nonneg.2 (hmem s))
      (sub_nonneg.2 (hmem s')) (by linarith) (by linarith) (by ring)
    linarith
  -- consumption `s − h(s)` is nondecreasing
  have hW := strictConcaveOn_liftS (strictConcave_integral (μ := lam) hsc)
  have hWv : ∀ y : Icc (0 : ℝ) xbar, liftS (fun y => ∫ z', v (y, z') ∂lam) y.1 =
      ∫ z', v (y, z') ∂lam := fun y => liftS_of_mem _ y.2
  have hcons : Monotone fun s => s.1 - (hs s).1 := by
    intro s s' hss'
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hss : s.1 < s'.1 := hlt_of s s' hss' fun heq => by subst heq; exact lt_irrefl _ hlt
    have hy := (hs s).2
    have hy' := (hs s').2
    have hms := hmem s
    have hms' := hmem s'
    -- `y₁ = s − c′` at `s`, `y₂ = s′ − c` at `s′`
    have hy0 := (hs s).2.1
    have hy0' := (hs s').2.1
    set y₁ : Icc (0 : ℝ) xbar := ⟨s.1 - (s'.1 - (hs s').1), by
      constructor <;> linarith [s.2.2]⟩
    set y₂ : Icc (0 : ℝ) xbar := ⟨s'.1 - (s.1 - (hs s).1), by
      constructor <;> linarith [s'.2.2]⟩
    have h1 := hopt s y₁ (show y₁.1 ≤ s.1 by simp only [y₁]; linarith)
    have h2 := hopt s' y₂ (show y₂.1 ≤ s'.1 by simp only [y₂]; linarith)
    rw [hval s _ (show y₁.1 ≤ s.1 by simp only [y₁]; linarith), hval s _ hms] at h1
    rw [hval s' _ (show y₂.1 ≤ s'.1 by simp only [y₂]; linarith), hval s' _ hms'] at h2
    have e1 : s.1 - y₁.1 = s'.1 - (hs s').1 := by simp only [y₁]; ring
    have e2 : s'.1 - y₂.1 = s.1 - (hs s).1 := by simp only [y₂]; ring
    rw [e1] at h1
    rw [e2] at h2
    have hex := strictConcave_exchange hW (p := (hs s).1) (q := y₁.1) (r := y₂.1)
      (t := (hs s').1) (hs s).2 (hs s').2 (by simp only [y₁]; linarith)
      (by simp only [y₁]; linarith) (by simp only [y₁, y₂]; ring)
    rw [hWv, hWv, hWv, hWv] at hex
    nlinarith [h.β_pos]
  -- composition with `s(x, z) = z f(x)`
  have hsx : ∀ z, Monotone fun x => outS h (x, z) := fun z x x' hxx' => by
    change z.1 * f x.1 ≤ z.1 * f x'.1
    exact mul_le_mul_of_nonneg_left (h.f_mono.monotoneOn x.2.1 x'.2.1 hxx')
      (by linarith [z.2.1])
  have hsz : ∀ x, Monotone fun z => outS h (x, z) := fun x z z' hzz' => by
    change z.1 * f x.1 ≤ z'.1 * f x.1
    exact mul_le_mul_of_nonneg_right hzz' (h.f_nonneg x.2.1)
  refine ⟨hgs, hO.continuous_argmaxFn, hmono, hcons, fun z x x' hxx' => ?_,
    fun x z z' hzz' => ?_, fun z x x' hxx' => ?_, fun x z z' hzz' => ?_⟩
  · simp only [hgs]; exact hmono (hsx z hxx')
  · simp only [hgs]; exact hmono (hsz x hzz')
  · simp only [hgs]; exact hcons (hsx z hxx')
  · simp only [hgs]; exact hcons (hsz x hzz')

/-! ### The corner counterexample -/

/-- `U(c) = 1 − e^{−c}`. -/
noncomputable def cexU (c : ℝ) : ℝ := 1 - Real.exp (-c)

/-- `f(x) = 2x/(1 + x)`. -/
noncomputable def cexf (x : ℝ) : ℝ := 2 * x / (1 + x)

/-- The example satisfies (U1)–(U3), (T1)–(T3) and (Z1), with `x̄ = 3 = 2 f(3)`. -/
theorem cex_hyp : GrowthHyp cexU cexf (1 / 10) 3 2 where
  β_pos := by norm_num
  β_lt := by norm_num
  U_cont := (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousOn
  U_mono := fun c _ c' _ hcc' => by
    simp only [cexU]
    have := Real.exp_lt_exp.2 (neg_lt_neg hcc')
    linarith
  f_cont := ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => by
    have : (0 : ℝ) ≤ x := hx
    exact (by linarith : (0 : ℝ) < 1 + x).ne'
  f_zero := by simp [cexf]
  f_mono := fun x hx x' hx' hxx' => by
    have hx0 : (0 : ℝ) ≤ x := hx
    have hx0' : (0 : ℝ) ≤ x' := hx'
    simp only [cexf]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  zbar_gt := by norm_num
  xbar_pos := by norm_num
  xbar_maintain := by norm_num [cexf]

/-- (U4): `U(c) = 1 − e^{−c}` is strictly concave. -/
theorem cexU_strictConcave : StrictConcaveOn ℝ (Ici 0) cexU := by
  refine ⟨convex_Ici 0, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have := strictConvexOn_exp.2 (mem_univ (-x)) (mem_univ (-y))
    (fun h => hxy (neg_inj.1 h)) ha hb hab
  simp only [smul_eq_mul, cexU] at this ⊢
  have e : a * -x + b * -y = -(a * x + b * y) := by ring
  rw [e] at this
  linarith

/-- (T4): `f(x) = 2x/(1 + x)` is concave on `[0, ∞)`. -/
theorem cexf_concave : ConcaveOn ℝ (Ici 0) cexf := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := hy
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [smul_eq_mul, cexf]
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : (0 : ℝ) < 1 + y := by linarith
  have h3 : (0 : ℝ) < 1 + (a * x + (1 - a) * y) := by nlinarith
  rw [mul_div_assoc', mul_div_assoc', div_add_div _ _ h1.ne' h2.ne', div_le_div_iff₀
    (mul_pos h1 h2) h3]
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]

/-- In the example, `v(x, z) − v(0, z) ≤ 4x`: the set of such functions is closed and mapped into
itself by `T`, since `U(c) − U(0) ≤ c`, `βK = 2/5 ≤ 1` and `z f(x) ≤ 4x`. -/
theorem cex_lipschitz (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2)) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : bellman (growthModel Q cexU cexf (1 / 10) 3) (growth_boundedDP cex_hyp Q hQ) v = v)
    (x : Icc (0 : ℝ) 3) (z : Icc (1 : ℝ) 2) :
    v (x, z) - v (⟨0, le_rfl, by norm_num⟩, z) ≤ 4 * x.1 := by
  set M := growthModel Q cexU cexf (1 / 10) 3
  have hb := growth_boundedDP cex_hyp Q hQ
  obtain ⟨x0, hx0⟩ : ∃ x0 : Icc (0 : ℝ) 3, x0 = ⟨0, le_rfl, by norm_num⟩ := ⟨_, rfl⟩
  rw [← hx0]
  set C : Set (Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ) :=
    {w | ∀ x z, w (x, z) - w (x0, z) ≤ 4 * x.1}
  have hclosed : IsClosed C := by
    have : C = ⋂ x, ⋂ z, {w : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ |
        w (x, z) - w (x0, z) ≤ 4 * x.1} := by
      ext w; simp only [C, mem_ofPred_eq, mem_iInter]
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun z =>
      isClosed_le ((continuous_eval_const _).sub (continuous_eval_const _)) continuous_const
  have hmaps : MapsTo (bellman M hb) C C := by
    intro w hw x z
    obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M hb w (x, z)
    obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb w (x0, z)
    have h0 : x0 ∈ M.Γ (x0, z) := by
      change x0.1 ≤ z.1 * cexf x0.1
      simp [hx0, cexf]
    have hm := hmax x0 h0
    have hint := integrable_section_v (Q z) w
    have hE : ∫ z', w (y, z') ∂Q z - ∫ z', w (x0, z') ∂Q z ≤ 4 * y.1 := by
      rw [← integral_sub (hint y) (hint x0)]
      have := integral_mono (μ := Q z) ((hint y).sub (hint x0)) (integrable_const (4 * y.1))
        fun z' => hw y z'
      simpa using this
    simp only [rhs, expV] at hval hm
    change bellman M hb w (x, z) =
      growthF cexU cexf 3 2 (x, y, z) + 1 / 10 * ∫ z', w (y, z') ∂Q z at hval
    change growthF cexU cexf 3 2 (x0, x0, z) + 1 / 10 * ∫ z', w (x0, z') ∂Q z ≤
      bellman M hb w (x0, z) at hm
    rw [growthF_of_mem hy] at hval
    have hF0 : growthF cexU cexf 3 2 (x0, x0, z) = 0 := by simp [growthF, hx0, cexU, cexf]
    rw [hF0] at hm
    have hyz : y.1 ≤ z.1 * cexf x.1 := hy
    have hUc : cexU (z.1 * cexf x.1 - y.1) ≤ z.1 * cexf x.1 - y.1 := by
      simp only [cexU]
      linarith [Real.add_one_le_exp (-(z.1 * cexf x.1 - y.1))]
    have hfx : cexf x.1 ≤ 2 * x.1 := by
      simp only [cexf]
      exact div_le_self (by linarith [x.2.1]) (by linarith [x.2.1])
    have hzf : z.1 * cexf x.1 ≤ 4 * x.1 := by
      have := mul_le_mul z.2.2 hfx (by simp only [cexf]; have := x.2.1; positivity)
        (by norm_num)
      linarith
    change bellman M hb w (x, z) - bellman M hb w (x0, z) ≤ 4 * x.1
    linarith [y.2.1]
  have hzero : (0 : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ) ∈ C := fun x _ => by
    simp only [coe_zero, Pi.zero_apply, sub_self]
    linarith [x.2.1]
  exact (corollary_1 (bellman_contraction M hb) hv ⟨0, hzero⟩ hclosed hmaps hmaps).1 x z

/-- **Exercise 10.1d, corrected.** In the example, for any Feller `Q` (i.i.d. shocks included),
the only optimal choice at `x ≤ 1/10` is `y = 0`: the marginal utility `e^{−s} ≥ 3/5` of
consumption exceeds the bound `βK = 2/5` on the marginal value of capital. -/
theorem ex_10_1d_counterexample (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2)) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : bellman (growthModel Q cexU cexf (1 / 10) 3) (growth_boundedDP cex_hyp Q hQ) v = v)
    {x : Icc (0 : ℝ) 3} (hx : x.1 ≤ 1 / 10) (z : Icc (1 : ℝ) 2) {y : Icc (0 : ℝ) 3}
    (hy : y ∈ policy (growthModel Q cexU cexf (1 / 10) 3) v (x, z)) : y.1 = 0 := by
  set M := growthModel Q cexU cexf (1 / 10) 3
  have hb := growth_boundedDP cex_hyp Q hQ
  obtain ⟨x0, hx0⟩ : ∃ x0 : Icc (0 : ℝ) 3, x0 = ⟨0, le_rfl, by norm_num⟩ := ⟨_, rfl⟩
  have hL := fun z' => cex_lipschitz Q hQ hv y z'
  rw [← hx0] at hL
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb v (x, z)
  have h0 : x0 ∈ M.Γ (x, z) := by
    change x0.1 ≤ z.1 * cexf x.1
    rw [hx0]
    exact mul_nonneg (by linarith [z.2.1]) (by simp only [cexf]; have := x.2.1; positivity)
  have hm := hmax x0 h0
  rw [hv] at hm
  have hyv := hy.2
  have hint := integrable_section_v (Q z) v
  have hE : ∫ z', v (y, z') ∂Q z - ∫ z', v (x0, z') ∂Q z ≤ 4 * y.1 := by
    rw [← integral_sub (hint y) (hint x0)]
    have := integral_mono (μ := Q z) ((hint y).sub (hint x0)) (integrable_const (4 * y.1)) hL
    simpa using this
  simp only [rhs, expV] at hm hyv
  change growthF cexU cexf 3 2 (x, x0, z) + 1 / 10 * ∫ z', v (x0, z') ∂Q z ≤ v (x, z) at hm
  change v (x, z) = growthF cexU cexf 3 2 (x, y, z) + 1 / 10 * ∫ z', v (y, z') ∂Q z at hyv
  have hx00 : x0.1 = 0 := by rw [hx0]
  rw [growthF_of_mem h0, hx00, sub_zero] at hm
  rw [growthF_of_mem hy.1] at hyv
  -- output `s = z f(x) ≤ 2/5`
  set s := z.1 * cexf x.1
  have hfx : cexf x.1 ≤ 2 * x.1 := by
    simp only [cexf]
    exact div_le_self (by linarith [x.2.1]) (by linarith [x.2.1])
  have hs : s ≤ 2 / 5 := by
    have := mul_le_mul z.2.2 hfx (by simp only [cexf]; have := x.2.1; positivity) (by norm_num)
    linarith
  simp only [cexU] at hm hyv
  have hes : 3 / 5 ≤ Real.exp (-s) := by linarith [Real.add_one_le_exp (-s)]
  have hey : 1 + y.1 ≤ Real.exp y.1 := by linarith [Real.add_one_le_exp y.1]
  have hsplit : Real.exp (-(s - y.1)) = Real.exp y.1 * Real.exp (-s) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit] at hyv
  have hpos := Real.exp_pos (-s)
  have k1 := mul_nonneg hpos.le (sub_nonneg.2 hey)
  have k2 := mul_nonneg y.2.1 (sub_nonneg.2 hes)
  have : y.1 ≤ 0 := by linarith
  linarith [y.2.1]

/-- **Exercise 10.1d, corrected.** In the example no selection `g` from `G` is strictly increasing
in `x`: `g(0, z) = g(1/10, z) = 0`. -/
theorem ex_10_1d_not_strictMono (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2)) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : bellman (growthModel Q cexU cexf (1 / 10) 3) (growth_boundedDP cex_hyp Q hQ) v = v)
    {g : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 → Icc (0 : ℝ) 3}
    (hg : ∀ s, g s ∈ policy (growthModel Q cexU cexf (1 / 10) 3) v s) (z : Icc (1 : ℝ) 2) :
    ¬ StrictMono fun x => g (x, z) := by
  intro hmono
  have hlt : (⟨0, le_rfl, by norm_num⟩ : Icc (0 : ℝ) 3) < ⟨1 / 10, by norm_num, by norm_num⟩ :=
    show (0 : ℝ) < 1 / 10 by norm_num
  have := hmono hlt
  have h1 := ex_10_1d_counterexample Q hQ hv (x := ⟨0, le_rfl, by norm_num⟩)
    (show (0 : ℝ) ≤ 1 / 10 by norm_num) z (hg _)
  have h2 := ex_10_1d_counterexample Q hQ hv (x := ⟨1 / 10, by norm_num, by norm_num⟩)
    (show (1 / 10 : ℝ) ≤ 1 / 10 by norm_num) z (hg _)
  have : (g (⟨0, le_rfl, by norm_num⟩, z)).1 < (g (⟨1 / 10, by norm_num, by norm_num⟩, z)).1 :=
    this
  linarith

/-! ### Exercise 10.1e–f: differentiability and Markov shocks -/

/-- Benveniste–Scheinkman (Theorem 4.10) on the line. -/
theorem hasDerivAt_of_concaveOn_of_le {S : Set ℝ} {V L : ℝ → ℝ} {x₀ d : ℝ}
    (hV : ConcaveOn ℝ S V) (hS : S ∈ 𝓝 x₀) (hL : HasDerivAt L d x₀) (heq : L x₀ = V x₀)
    (hle : ∀ᶠ x in 𝓝 x₀, L x ≤ V x) : HasDerivAt V d x₀ := by
  have := (theorem_4_10 hV hS hL.hasFDerivAt heq hle).hasDerivAt
  simpa using this

/-- The return to any feasible `y` is at most the value: `U[z f(x) − y] + βE v(y, ·) ≤ v(x, z)`. -/
theorem growth_rhs_le (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v)
    {x y : Icc (0 : ℝ) xbar} {z : Icc (1 : ℝ) zbar} (hy : y ∈ growthΓ f xbar zbar (x, z)) :
    U (z.1 * f x.1 - y.1) + β * ∫ z', v (y, z') ∂Q z ≤ v (x, z) := by
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax _ (growth_boundedDP h Q hQ) v (x, z)
  have := hmax y hy
  rw [hv] at this
  simp only [rhs, expV] at this
  change growthF U f xbar zbar (x, y, z) + β * _ ≤ _ at this
  rwa [growthF_of_mem hy] at this

/-- At an optimal `y`, `v(x, z) = U[z f(x) − y] + βE v(y, ·)`. -/
theorem growth_eq_of_policy {Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)}
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ} {x y : Icc (0 : ℝ) xbar}
    {z : Icc (1 : ℝ) zbar} (hy : y ∈ policy (growthModel Q U f β xbar) v (x, z)) :
    v (x, z) = U (z.1 * f x.1 - y.1) + β * ∫ z', v (y, z') ∂Q z := by
  have := hy.2
  simp only [rhs, expV] at this
  change v (x, z) = growthF U f xbar zbar (x, y, z) + β * _ at this
  rwa [growthF_of_mem hy.1] at this

/-- **Exercise 10.1e–f** (`v_x`). With `U` and `f` concave and any Feller `Q`: if `y₀` is optimal
at `(x₀, z₀)` with `x₀ < x̄` and consumption `c = z₀ f(x₀) − y₀ > 0`, `U` is differentiable at
`c` and `f` at `x₀`, then `v_x(x₀, z₀) = U′(c) z₀ f′(x₀)`. -/
theorem growth_hasDerivAt_x (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v)
    {x₀ y₀ : Icc (0 : ℝ) xbar} {z₀ : Icc (1 : ℝ) zbar} (hx₀ : x₀.1 < xbar)
    (hy₀ : y₀ ∈ policy (growthModel Q U f β xbar) v (x₀, z₀)) (hc : y₀.1 < z₀.1 * f x₀.1)
    {U' f' : ℝ} (hU' : HasDerivAt U U' (z₀.1 * f x₀.1 - y₀.1)) (hf' : HasDerivAt f f' x₀.1) :
    HasDerivAt (liftS fun x => v (x, z₀)) (U' * (z₀.1 * f')) x₀.1 := by
  have hvc := growth_concave h hU hf Q hQ hv z₀
  have hx0 : 0 < x₀.1 := by
    rcases x₀.2.1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq, h.f_zero, mul_zero] at hc
      linarith [y₀.2.1]
  have hS : Icc (0 : ℝ) xbar ∈ 𝓝 x₀.1 := Icc_mem_nhds hx0 hx₀
  have hL : HasDerivAt (fun x => U (z₀.1 * f x - y₀.1) + β * ∫ z', v (y₀, z') ∂Q z₀)
      (U' * (z₀.1 * f')) x₀.1 :=
    (hU'.comp x₀.1 ((hf'.const_mul z₀.1).sub_const y₀.1)).add_const _
  refine hasDerivAt_of_concaveOn_of_le (concaveOn_liftS hvc) hS hL ?_ ?_
  · rw [liftS_of_mem _ x₀.2]
    exact (growth_eq_of_policy hy₀).symm
  · have hev : ∀ᶠ x in 𝓝 x₀.1, y₀.1 < z₀.1 * f x :=
      (hf'.continuousAt.const_mul z₀.1).eventually (lt_mem_nhds hc)
    filter_upwards [hev, hS] with x hx hxS
    rw [liftS_of_mem _ hxS]
    exact growth_rhs_le h Q hQ hv (x := ⟨x, hxS⟩) hx.le

/-- Under i.i.d. shocks `v(x, ·)` is concave: the expectation does not depend on `z`, and the
constraint `y ≤ z f(x)` and the return `U[z f(x) − y]` are concave in `(z, y)`. -/
theorem growth_concave_z (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel (Kernel.const _ lam) U f β xbar)
      (growth_boundedDP h _ (isFeller_const lam)) v = v) (x : Icc (0 : ℝ) xbar) :
    IsConcaveS (convex_Icc 1 zbar) fun z => v (x, z) := by
  set M := growthModel (Kernel.const _ lam) U f β xbar
  have hb := growth_boundedDP h _ (isFeller_const lam)
  have hvc := growth_concave h hU hf _ (isFeller_const lam) hv
  intro z₀ z₁ θ h0 h1
  obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax M hb v (x, z₀)
  obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax M hb v (x, z₁)
  rw [hv] at hv₀ hv₁
  have e₀ := growth_eq_of_policy (show y₀ ∈ policy M v (x, z₀) from ⟨hy₀, hv₀⟩)
  have e₁ := growth_eq_of_policy (show y₁ ∈ policy M v (x, z₁) from ⟨hy₁, hv₁⟩)
  rw [Kernel.const_apply] at e₀ e₁
  have hzθ : (cmb (convex_Icc 1 zbar) h0 h1 z₀ z₁).1 = θ * z₀.1 + (1 - θ) * z₁.1 := by
    simp [cmb]
  have hyθv := cmb_val (x₀ := y₀) (x₁ := y₁) h0 h1
  have c₀ : 0 ≤ z₀.1 * f x.1 - y₀.1 := sub_nonneg.2 hy₀
  have c₁ : 0 ≤ z₁.1 * f x.1 - y₁.1 := sub_nonneg.2 hy₁
  have hyθ : cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁ ∈
      growthΓ f xbar zbar (x, cmb (convex_Icc 1 zbar) h0 h1 z₀ z₁) := by
    change (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁).1 ≤ _
    rw [hyθv, hzθ]
    have : 0 ≤ 1 - θ := by linarith
    nlinarith [mul_nonneg h0 c₀, mul_nonneg this c₁]
  have hle := growth_rhs_le h _ (isFeller_const lam) hv hyθ
  rw [Kernel.const_apply] at hle
  have hUc := hU.2 c₀ c₁ h0 (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hUc
  have harg : θ * (z₀.1 * f x.1 - y₀.1) + (1 - θ) * (z₁.1 * f x.1 - y₁.1) =
      (cmb (convex_Icc 1 zbar) h0 h1 z₀ z₁).1 * f x.1 -
        (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁).1 := by
    rw [hyθv, hzθ]; ring
  rw [harg] at hUc
  have hint := integrable_section_v lam v
  have hE : θ * ∫ z', v (y₀, z') ∂lam + (1 - θ) * ∫ z', v (y₁, z') ∂lam ≤
      ∫ z', v (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁, z') ∂lam := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hint y₀).const_mul θ) ((hint y₁).const_mul _)]
    exact integral_mono (((hint y₀).const_mul θ).add ((hint y₁).const_mul _)) (hint _)
      fun z' => hvc z' y₀ y₁ θ h0 h1
  have hβE := mul_le_mul_of_nonneg_left hE h.β_pos.le
  dsimp only
  rw [e₀, e₁]
  nlinarith

/-- **Exercise 10.1e** (`v_z`, i.i.d. shocks): `v_z(x₀, z₀) = U′(c) f(x₀)` at an interior `z₀`
when `c = z₀ f(x₀) − y₀ > 0` for an optimal `y₀`. -/
theorem growth_hasDerivAt_z (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel (Kernel.const _ lam) U f β xbar)
      (growth_boundedDP h _ (isFeller_const lam)) v = v)
    {x₀ y₀ : Icc (0 : ℝ) xbar} {z₀ : Icc (1 : ℝ) zbar} (hz₁ : 1 < z₀.1) (hz₂ : z₀.1 < zbar)
    (hy₀ : y₀ ∈ policy (growthModel (Kernel.const _ lam) U f β xbar) v (x₀, z₀))
    (hc : y₀.1 < z₀.1 * f x₀.1) {U' : ℝ} (hU' : HasDerivAt U U' (z₀.1 * f x₀.1 - y₀.1)) :
    HasDerivAt (liftS fun z => v (x₀, z)) (U' * f x₀.1) z₀.1 := by
  have hvc := growth_concave_z h hU hf lam hv x₀
  have hS : Icc (1 : ℝ) zbar ∈ 𝓝 z₀.1 := Icc_mem_nhds hz₁ hz₂
  have hL : HasDerivAt (fun z => U (z * f x₀.1 - y₀.1) + β * ∫ z', v (y₀, z') ∂lam)
      (U' * f x₀.1) z₀.1 := by
    have := (hU'.comp z₀.1 (((hasDerivAt_id' z₀.1).mul_const (f x₀.1)).sub_const y₀.1)).add_const
      (β * ∫ z', v (y₀, z') ∂lam)
    simpa using this
  refine hasDerivAt_of_concaveOn_of_le (concaveOn_liftS hvc) hS hL ?_ ?_
  · rw [liftS_of_mem _ z₀.2]
    have := growth_eq_of_policy hy₀
    rw [Kernel.const_apply] at this
    exact this.symm
  · have hev : ∀ᶠ z in 𝓝 z₀.1, y₀.1 < z * f x₀.1 :=
      (continuous_id'.mul continuous_const).continuousAt.eventually (lt_mem_nhds hc)
    filter_upwards [hev, hS] with z hz hzS
    rw [liftS_of_mem _ hzS]
    have := growth_rhs_le h _ (isFeller_const lam) hv (x := x₀) (z := ⟨z, hzS⟩) hz.le
    rw [Kernel.const_apply] at this
    exact this

/-- **Exercise 10.1e.** Under i.i.d. shocks, with `U` and `f` concave: if `y₀` is optimal at an
interior `(x₀, z₀)` with consumption `c = z₀ f(x₀) − y₀ > 0`, `U` differentiable at `c` and `f`
at `x₀`, then `v_x(x₀, z₀) = U′(c) z₀ f′(x₀)` and `v_z(x₀, z₀) = U′(c) f(x₀)`. -/
theorem ex_10_1e (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel (Kernel.const _ lam) U f β xbar)
      (growth_boundedDP h _ (isFeller_const lam)) v = v)
    {x₀ y₀ : Icc (0 : ℝ) xbar} {z₀ : Icc (1 : ℝ) zbar} (hx₀ : x₀.1 < xbar) (hz₁ : 1 < z₀.1)
    (hz₂ : z₀.1 < zbar)
    (hy₀ : y₀ ∈ policy (growthModel (Kernel.const _ lam) U f β xbar) v (x₀, z₀))
    (hc : y₀.1 < z₀.1 * f x₀.1) {U' f' : ℝ} (hU' : HasDerivAt U U' (z₀.1 * f x₀.1 - y₀.1))
    (hf' : HasDerivAt f f' x₀.1) :
    HasDerivAt (liftS fun x => v (x, z₀)) (U' * (z₀.1 * f')) x₀.1 ∧
      HasDerivAt (liftS fun z => v (x₀, z)) (U' * f x₀.1) z₀.1 :=
  ⟨growth_hasDerivAt_x h hU hf _ (isFeller_const lam) hv hx₀ hy₀ hc hU' hf',
    growth_hasDerivAt_z h hU hf lam hv hz₁ hz₂ hy₀ hc hU'⟩

/-- With `Q` monotone, `T` maps functions nondecreasing in `z` to functions nondecreasing in `z`,
strictly increasing in `z` at `x > 0`. -/
theorem growth_bellman_mono_z (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hQm : IsMonotoneTF Q) {w : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hw : ∀ x, Monotone fun z => w (x, z)) (x : Icc (0 : ℝ) xbar) {z z' : Icc (1 : ℝ) zbar}
    (hzz' : z < z') :
    bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w (x, z) ≤
        bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w (x, z') ∧
      (0 < x.1 → bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w (x, z) <
        bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w (x, z')) := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M hb w (x, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb w (x, z')
  have hyz : y.1 ≤ z.1 * f x.1 := hy
  have hzz : z.1 < z'.1 := hzz'
  have hzle : z.1 * f x.1 ≤ z'.1 * f x.1 := mul_le_mul_of_nonneg_right hzz.le (h.f_nonneg x.2.1)
  have hy' : y ∈ M.Γ (x, z') := show y.1 ≤ z'.1 * f x.1 from hyz.trans hzle
  have hm := hmax y hy'
  have hE := expV_mono_z M hb hQm w hy hzz'.le (hw y)
  have hEβ := mul_le_mul_of_nonneg_left hE h.β_pos.le
  simp only [rhs] at hval hm
  change bellman M hb w (x, z) = growthF U f xbar zbar (x, y, z) + M.β * _ at hval
  change growthF U f xbar zbar (x, y, z') + M.β * _ ≤ _ at hm
  rw [growthF_of_mem hy] at hval
  rw [growthF_of_mem hy'] at hm
  have hUle : U (z.1 * f x.1 - y.1) ≤ U (z'.1 * f x.1 - y.1) :=
    h.U_mono.monotoneOn (mem_Ici.2 (sub_nonneg.2 hyz)) (mem_Ici.2 (sub_nonneg.2 (hyz.trans hzle)))
      (by linarith)
  refine ⟨by rw [hval]; linarith, fun hx => ?_⟩
  have hfx : 0 < f x.1 := by
    have := h.f_mono (mem_Ici.2 le_rfl : (0 : ℝ) ∈ Ici 0) x.2.1 hx
    rwa [h.f_zero] at this
  have hzlt : z.1 * f x.1 < z'.1 * f x.1 := mul_lt_mul_of_pos_right hzz hfx
  have hUlt := h.U_mono (mem_Ici.2 (sub_nonneg.2 hyz)) (mem_Ici.2 (sub_nonneg.2 (hyz.trans hzle)))
    (by linarith : z.1 * f x.1 - y.1 < z'.1 * f x.1 - y.1)
  rw [hval]
  linarith

/-- **Exercise 10.1f.** With Markov shocks (Z3), parts (a)–(c) hold (`ex_10_1a`–`ex_10_1c` are
proved for any Feller `Q`), and so does the formula for `v_x` (`growth_hasDerivAt_x`). If `Q` is
monotone, `v(x, ·)` is nondecreasing, and strictly increasing when `x > 0` (at `x = 0` output
is `0` for every `z`). -/
theorem ex_10_1f (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hQm : IsMonotoneTF Q) {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v) :
    (∀ x, Monotone fun z => v (x, z)) ∧
      ∀ x : Icc (0 : ℝ) xbar, 0 < x.1 → StrictMono fun z => v (x, z) := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  set C' : Set (Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ) :=
    {w | ∀ x, Monotone fun z => w (x, z)}
  have hclosed : IsClosed C' := by
    have := isClosed_pointwise_le (S := Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar)
      (ι := {q : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar × Icc (1 : ℝ) zbar // q.2.1 ≤ q.2.2})
      (fun q => (q.1.1, q.1.2.1)) (fun q => (q.1.1, q.1.2.2))
    convert this using 1
    ext w
    exact ⟨fun hw q => hw q.1.1 q.2, fun hw x z z' hzz' => hw ⟨(x, z, z'), hzz'⟩⟩
  have hmono : ∀ w ∈ C', ∀ x, Monotone fun z => bellman M hb w (x, z) :=
    fun w hw x z z' hzz' => by
      rcases hzz'.lt_or_eq with hlt | heq
      · exact (growth_bellman_mono_z h Q hQ hQm hw x hlt).1
      · rw [heq]
  have hv' := (corollary_1 (S' := C')
    (S'' := {w | ∀ x : Icc (0 : ℝ) xbar, 0 < x.1 → StrictMono fun z => w (x, z)})
    (bellman_contraction M hb) hv ⟨0, fun _ _ _ _ => le_rfl⟩ hclosed hmono
    fun w hw x hx z z' hzz' => (growth_bellman_mono_z h Q hQ hQm hw x hzz').2 hx)
  exact ⟨hv'.1, hv'.2⟩

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal growth with two capital goods

SLP §10.2, p. 290: one output `z f(x₁, x₂)`, consumed or invested in either capital good, which
depreciates fully: `0 ≤ y₁, y₂` and `y₁ + y₂ ≤ z f(x₁, x₂)`. The capital stocks lie in
`X = {x ≥ 0 : x₁ + x₂ ≤ x̄}` and the shocks in `Z = [1, z̄]`, with any Feller transition `Q`.

* **Exercise 10.2a** (`ex_10_2a`): if `z̄ f(x) < x₁ + x₂` whenever `x₁ + x₂ > x̄` (the analogue of
  (T2)), the set of sustainable stocks `{x ≥ 0 : x₁ + x₂ ≤ z̄ f(x)}` is compact and lies in `X`.
  The analysis on `X` uses `z̄ f(x) ≤ x̄` on `X` (`TwoHyp`).
* **Exercise 10.2b** (`two_boundedDP`, `ex_10_2b`, `ex_10_2b_diff`). The hypotheses of §9.2
  hold, so (2) has a unique bounded continuous solution `v`; it is strictly increasing. If `f` is
  strictly concave, `v(·, z)` is strictly concave, the policy is a continuous function `g`, the
  plans it generates are optimal (`v = v*`), and `v` is differentiable where consumption is
  positive, with `Dv(x, z) = U′(c) z Df(x)`. **Correction:** (T4) asks only that `f` be concave,
  and then both claims fail. With `f(x) = 2(x₁ + x₂)/(1 + x₁ + x₂)` (`ex_10_2b_counterexample`),
  `v(x, z)` depends on `x` only through `x₁ + x₂`, so `v(·, z)` is affine along
  `x₁ + x₂ = 1`; and at `x = (3, 0)`, `z = 2`, saving is optimal, and any optimal saving `k > 0`
  can be held as `(k, 0)` or `(0, k)`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- The nonnegative quadrant `ℝ²₊`. -/
def quadrant : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2}

/-- The capital stocks `X = {x ∈ ℝ²₊ : x₁ + x₂ ≤ x̄}`. -/
def twoX (xbar : ℝ) : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ xbar}

theorem convex_quadrant : Convex ℝ quadrant := by
  intro x hx y hy a b ha hb _
  exact ⟨by simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; nlinarith [hx.1, hy.1],
    by simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; nlinarith [hx.2, hy.2]⟩

theorem convex_twoX (xbar : ℝ) : Convex ℝ (twoX xbar) := by
  intro x hx y hy a b ha hb hab
  simp only [twoX, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨by positivity, by positivity, ?_⟩
  nlinarith

theorem isCompact_twoX (xbar : ℝ) : IsCompact (twoX xbar) := by
  have hb : Bornology.IsBounded (twoX xbar) :=
    (Metric.isBounded_Icc ((0, 0) : ℝ × ℝ) (xbar, xbar)).subset fun x hx =>
      ⟨⟨hx.1, hx.2.1⟩, ⟨by linarith [hx.2.2, hx.2.1], by linarith [hx.2.2, hx.1]⟩⟩
  have hc : IsClosed (twoX xbar) := by
    have h1 : IsClosed {b : ℝ × ℝ | 0 ≤ b.1} := isClosed_le continuous_const continuous_fst
    have h2 : IsClosed {b : ℝ × ℝ | 0 ≤ b.2} := isClosed_le continuous_const continuous_snd
    have h3 : IsClosed {b : ℝ × ℝ | b.1 + b.2 ≤ xbar} :=
      isClosed_le (by fun_prop) continuous_const
    exact h1.inter (h2.inter h3)
  exact Metric.isCompact_of_isClosed_isBounded hc hb

theorem twoX_subset_quadrant {xbar : ℝ} {x : ℝ × ℝ} (hx : x ∈ twoX xbar) : x ∈ quadrant :=
  ⟨hx.1, hx.2.1⟩

/-- (U1)–(U3), (T1) and (T3) for `f : ℝ²₊ → ℝ`, (Z1), and the answer to Exercise 10.2a in the form
used: `z̄ f(x) ≤ x̄` on `X`. -/
structure TwoHyp (U : ℝ → ℝ) (f : ℝ × ℝ → ℝ) (β xbar zbar : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  U_cont : ContinuousOn U (Ici 0)
  U_mono : StrictMonoOn U (Ici 0)
  f_cont : ContinuousOn f quadrant
  f_zero : f 0 = 0
  f_mono : ∀ x x' : ℝ × ℝ, x ∈ quadrant → x ≤ x' → x ≠ x' → f x < f x'
  zbar_gt : 1 < zbar
  xbar_pos : 0 < xbar
  f_bound : ∀ x ∈ twoX xbar, zbar * f x ≤ xbar

variable {U : ℝ → ℝ} {f : ℝ × ℝ → ℝ} {β xbar zbar : ℝ}

theorem TwoHyp.f_le (h : TwoHyp U f β xbar zbar) {x x' : ℝ × ℝ} (hx : x ∈ quadrant)
    (hxx' : x ≤ x') : f x ≤ f x' := by
  rcases eq_or_ne x x' with rfl | hne
  · exact le_rfl
  · exact (h.f_mono x x' hx hxx' hne).le

theorem TwoHyp.f_nonneg (h : TwoHyp U f β xbar zbar) {x : ℝ × ℝ} (hx : x ∈ quadrant) :
    0 ≤ f x := by
  have := h.f_le (show (0 : ℝ × ℝ) ∈ quadrant from ⟨le_rfl, le_rfl⟩)
    (show (0 : ℝ × ℝ) ≤ x from ⟨hx.1, hx.2⟩)
  rwa [h.f_zero] at this

theorem TwoHyp.continuous_f (h : TwoHyp U f β xbar zbar) :
    Continuous fun x : twoX xbar => f x.1 :=
  h.f_cont.comp_continuous continuous_subtype_val fun x => twoX_subset_quadrant x.2

theorem TwoHyp.zf_nonneg (h : TwoHyp U f β xbar zbar) (s : twoX xbar × Icc (1 : ℝ) zbar) :
    0 ≤ s.2.1 * f s.1.1 :=
  mul_nonneg (by linarith [s.2.2.1]) (h.f_nonneg (twoX_subset_quadrant s.1.2))

theorem TwoHyp.zf_le (h : TwoHyp U f β xbar zbar) (s : twoX xbar × Icc (1 : ℝ) zbar) :
    s.2.1 * f s.1.1 ≤ xbar :=
  (mul_le_mul_of_nonneg_right s.2.2.2 (h.f_nonneg (twoX_subset_quadrant s.1.2))).trans
    (h.f_bound _ s.1.2)

/-- `Γ(x, z) = {y ∈ X : y₁ + y₂ ≤ z f(x)}`. -/
def twoΓ (f : ℝ × ℝ → ℝ) (xbar zbar : ℝ) (s : twoX xbar × Icc (1 : ℝ) zbar) : Set (twoX xbar) :=
  {y | y.1.1 + y.1.2 ≤ s.2.1 * f s.1.1}

/-- `F(x, y, z) = U[z f(x) − y₁ − y₂]`, with consumption clamped at `0` off the graph. -/
def twoF (U : ℝ → ℝ) (f : ℝ × ℝ → ℝ) (xbar zbar : ℝ)
    (p : twoX xbar × twoX xbar × Icc (1 : ℝ) zbar) : ℝ :=
  U (max (p.2.2.1 * f p.1.1 - (p.2.1.1.1 + p.2.1.1.2)) 0)

/-- The two-capital model in the first formulation of Chapter 9. -/
abbrev twoModel (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) (U : ℝ → ℝ)
    (f : ℝ × ℝ → ℝ) (β xbar : ℝ) : Model (twoX xbar) (twoX xbar) (Icc (1 : ℝ) zbar) :=
  Model.first Q (twoΓ f xbar zbar) (twoF U f xbar zbar) β

theorem twoF_of_mem {x y : twoX xbar} {z : Icc (1 : ℝ) zbar} (hy : y ∈ twoΓ f xbar zbar (x, z)) :
    twoF U f xbar zbar (x, y, z) = U (z.1 * f x.1 - (y.1.1 + y.1.2)) := by
  have : 0 ≤ z.1 * f x.1 - (y.1.1 + y.1.2) := sub_nonneg.2 hy
  simp only [twoF, max_eq_left this]

theorem TwoHyp.continuous_F (h : TwoHyp U f β xbar zbar) : Continuous (twoF U f xbar zbar) :=
  h.U_cont.comp_continuous ((((continuous_subtype_val.comp continuous_snd.snd).mul
    (h.continuous_f.comp continuous_fst)).sub
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd.fst)).add
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd.fst)))).max
    continuous_const) fun _ => mem_Ici.2 (le_max_right _ _)

/-- The correspondence `s ↦ {y ∈ X : y₁ + y₂ ≤ c(s)}`, for continuous `c ≥ 0`, is l.h.c.: scale
`y` down by `min{1, c(sₙ)/(y₁ + y₂)}`. -/
theorem isLHC_twoX_le {S : Type*} [MetricSpace S] {c : S → ℝ} (hc : Continuous c)
    (h0 : ∀ s, 0 ≤ c s) (hx : 0 ≤ xbar) (s : S) :
    IsLHC (fun s => {y : twoX xbar | y.1.1 + y.1.2 ≤ c s}) s := by
  refine ⟨⟨⟨0, le_rfl, le_rfl, by simpa using hx⟩, by simpa using h0 s⟩, fun y hy xs hxs => ?_⟩
  have hy' : y.1.1 + y.1.2 ≤ c s := hy
  rcases (add_nonneg y.2.1 y.2.2.1).lt_or_eq with hσ | hσ
  · set σ := y.1.1 + y.1.2
    set t : ℕ → ℝ := fun n => min 1 (c (xs n) / σ)
    have ht0 : ∀ n, 0 ≤ t n := fun n => le_min zero_le_one (div_nonneg (h0 _) hσ.le)
    have ht1 : ∀ n, t n ≤ 1 := fun n => min_le_left _ _
    have hmem : ∀ n, t n • y.1 ∈ twoX xbar := fun n => by
      simp only [twoX, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      refine ⟨mul_nonneg (ht0 n) y.2.1, mul_nonneg (ht0 n) y.2.2.1, ?_⟩
      have := y.2.2.2
      nlinarith [ht0 n, ht1 n]
    refine ⟨0, fun n => ⟨t n • y.1, hmem n⟩, fun n _ => ?_, ?_⟩
    · change (t n • y.1).1 + (t n • y.1).2 ≤ c (xs n)
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have h1 : t n ≤ c (xs n) / σ := min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 hσ.le
      rw [div_mul_cancel₀ _ hσ.ne'] at h2
      linarith
    · have htl : Tendsto t atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).min (((hc.tendsto s).comp hxs).div_const σ)
        rwa [min_eq_left ((one_le_div hσ).2 hy')] at this
      refine tendsto_subtype_rng.2 ?_
      simpa using htl.smul_const y.1
  · refine ⟨0, fun _ => y, fun n _ => ?_, tendsto_const_nhds⟩
    change y.1.1 + y.1.2 ≤ c (xs n)
    rw [← hσ]
    exact h0 _

/-- The correspondence `s ↦ {y ∈ X : y₁ + y₂ ≤ c(s)}`, for continuous `c ≥ 0`, is u.h.c. -/
theorem isUHC_twoX_le {S : Type*} [MetricSpace S] {c : S → ℝ} (hc : Continuous c)
    (h0 : ∀ s, 0 ≤ c s) (hx : 0 ≤ xbar) (s : S) :
    IsUHC (fun s => {y : twoX xbar | y.1.1 + y.1.2 ≤ c s}) s := by
  have : CompactSpace (twoX xbar) := isCompact_iff_compactSpace.1 (isCompact_twoX xbar)
  refine ⟨⟨⟨0, le_rfl, le_rfl, by simpa using hx⟩, by simpa using h0 s⟩, fun xs hxs ys hys => ?_⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
  refine ⟨y, ?_, φ, hφ, hlim⟩
  have hc' : Continuous fun y : twoX xbar => y.1.1 + y.1.2 :=
    (continuous_fst.comp continuous_subtype_val).add (continuous_snd.comp continuous_subtype_val)
  exact le_of_tendsto_of_tendsto ((hc'.tendsto y).comp hlim)
    ((hc.tendsto s).comp (hxs.comp hφ.tendsto_atTop)) (Eventually.of_forall fun n => hys (φ n))

/-- The hypotheses of §9.2 hold for the two-capital model (Exercise 10.2b). -/
theorem two_boundedDP (h : TwoHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q) :
    BoundedDP (twoModel Q U f β xbar) := by
  have : CompactSpace (twoX xbar) := isCompact_iff_compactSpace.1 (isCompact_twoX xbar)
  have hzf : Continuous fun s : twoX xbar × Icc (1 : ℝ) zbar => s.2.1 * f s.1.1 :=
    (continuous_subtype_val.comp continuous_snd).mul (h.continuous_f.comp continuous_fst)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn h.continuous_F.continuousOn
  exact ⟨fun s => ⟨⟨0, le_rfl, le_rfl, by simpa using h.xbar_pos.le⟩, by
      change (0 : ℝ) + 0 ≤ _; simpa using h.zf_nonneg s⟩,
    fun _ => IsClosed.isCompact (isClosed_le ((continuous_fst.comp continuous_subtype_val).add
      (continuous_snd.comp continuous_subtype_val)) continuous_const),
    isLHC_twoX_le hzf h.zf_nonneg h.xbar_pos.le, isUHC_twoX_le hzf h.zf_nonneg h.xbar_pos.le,
    h.continuous_F.continuousOn,
    ⟨B, fun p _ => by simpa [Real.norm_eq_abs] using hB p (mem_univ _)⟩, h.β_pos, h.β_lt,
    continuous_fst.snd.continuousOn, contExp_first Q _ _ β (lemma_9_5_compact Q hQ)⟩

/-- **Exercise 10.2a.** If `z̄ f(x) < x₁ + x₂` whenever `x ≥ 0` and `x₁ + x₂ > x̄`, the set of
sustainable capital stocks `{x ≥ 0 : x₁ + x₂ ≤ z̄ f(x)}` is compact and contained in `X`. -/
theorem ex_10_2a (hf : ContinuousOn f quadrant)
    (hT2 : ∀ x ∈ quadrant, xbar < x.1 + x.2 → zbar * f x < x.1 + x.2) :
    {x | x ∈ quadrant ∧ x.1 + x.2 ≤ zbar * f x} ⊆ twoX xbar ∧
      IsCompact {x | x ∈ quadrant ∧ x.1 + x.2 ≤ zbar * f x} := by
  have hsub : {x | x ∈ quadrant ∧ x.1 + x.2 ≤ zbar * f x} ⊆ twoX xbar := fun x hx => by
    refine ⟨hx.1.1, hx.1.2, ?_⟩
    by_contra hlt
    have := hT2 x hx.1 (not_le.1 hlt)
    linarith [hx.2]
  refine ⟨hsub, (isCompact_twoX xbar).of_isClosed_subset ?_ hsub⟩
  have hq : IsClosed quadrant :=
    (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)
  have := (hf.const_smul zbar).sub (continuous_fst.add continuous_snd).continuousOn
    |>.preimage_isClosed_of_isClosed hq (isClosed_Ici (a := (0 : ℝ)))
  convert this using 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ici, Pi.sub_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, sub_nonneg]

/-! ### Exercise 10.2b -/

/-- **Exercise 10.2b** (monotonicity, Theorem 9.7): `v(·, z)` is strictly increasing. -/
theorem two_strictMono (h : TwoHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) v = v) (z : Icc (1 : ℝ) zbar) :
    StrictMono fun x => v (x, z) := by
  refine theorem_9_7 Q _ _ β (two_boundedDP h Q hQ) (fun x x' y z hxx' hy => ?_)
    (fun x x' z hxx' y hy => ?_) hv z
  · have hy' : y.1.1 + y.1.2 ≤ z.1 * f x.1 := hy
    have hfx : f x.1 < f x'.1 := h.f_mono x.1 x'.1 (twoX_subset_quadrant x.2) hxx'.le
      fun he => hxx'.ne (Subtype.ext he)
    have hz : 0 < z.1 := by linarith [z.2.1]
    have hlt : z.1 * f x.1 < z.1 * f x'.1 := mul_lt_mul_of_pos_left hfx hz
    rw [twoF_of_mem hy, twoF_of_mem (show y.1.1 + y.1.2 ≤ z.1 * f x'.1 by linarith)]
    exact h.U_mono (mem_Ici.2 (sub_nonneg.2 hy')) (mem_Ici.2 (by linarith)) (by linarith)
  · have hy' : y.1.1 + y.1.2 ≤ z.1 * f x.1 := hy
    have hfx : f x.1 ≤ f x'.1 := h.f_le (twoX_subset_quadrant x.2) hxx'
    exact hy'.trans (mul_le_mul_of_nonneg_left hfx (by linarith [z.2.1]))

theorem two_cmb_val {x₀ x₁ : twoX xbar} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (cmb (convex_twoX xbar) h0 h1 x₀ x₁).1.1 = θ * x₀.1.1 + (1 - θ) * x₁.1.1 ∧
      (cmb (convex_twoX xbar) h0 h1 x₀ x₁).1.2 = θ * x₀.1.2 + (1 - θ) * x₁.1.2 := by
  simp [cmb]

/-- Assumptions 9.10 and 9.11 hold when `U` is concave and `f` is strictly concave. -/
theorem two_assumptions (h : TwoHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : StrictConcaveOn ℝ quadrant f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) :
    Assumption910 (convex_twoX xbar) (convex_twoX xbar) (twoModel Q U f β xbar) ∧
      Assumption911 (convex_twoX xbar) (convex_twoX xbar) (twoModel Q U f β xbar) := by
  -- output at the mixture is at least the mixture of outputs
  have hout : ∀ (x x' : twoX xbar) (z : Icc (1 : ℝ) zbar) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      θ * (z.1 * f x.1) + (1 - θ) * (z.1 * f x'.1) ≤
        z.1 * f (cmb (convex_twoX xbar) h0 h1 x x').1 := by
    intro x x' z θ h0 h1
    have hc := hf.concaveOn.2 (twoX_subset_quadrant x.2) (twoX_subset_quadrant x'.2) h0
      (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
    simp only [smul_eq_mul] at hc
    have hz : 0 ≤ z.1 := by linarith [z.2.1]
    change _ ≤ z.1 * f (θ • x.1 + (1 - θ) • x'.1)
    nlinarith [mul_le_mul_of_nonneg_left hc hz]
  have hmem : Assumption911 (convex_twoX xbar) (convex_twoX xbar) (twoModel Q U f β xbar) := by
    intro z x y x' y' hy hy' θ h0 h1
    have e := hout x x' z θ h0 h1
    have e0 : y.1.1 + y.1.2 ≤ z.1 * f x.1 := hy
    have e1 : y'.1.1 + y'.1.2 ≤ z.1 * f x'.1 := hy'
    change (cmb (convex_twoX xbar) h0 h1 y y').1.1 + (cmb (convex_twoX xbar) h0 h1 y y').1.2 ≤ _
    rw [(two_cmb_val h0 h1).1, (two_cmb_val h0 h1).2]
    nlinarith
  refine ⟨fun z x y x' y' hy hy' θ h0 h1 => ?_, hmem⟩
  have hyθ := hmem z x y x' y' hy hy' θ h0.le h1.le
  have e0 : 0 ≤ z.1 * f x.1 - (y.1.1 + y.1.2) := sub_nonneg.2 hy
  have e1 : 0 ≤ z.1 * f x'.1 - (y'.1.1 + y'.1.2) := sub_nonneg.2 hy'
  have hsum : (cmb (convex_twoX xbar) h0.le h1.le y y').1.1 +
      (cmb (convex_twoX xbar) h0.le h1.le y y').1.2 =
      θ * (y.1.1 + y.1.2) + (1 - θ) * (y'.1.1 + y'.1.2) := by
    rw [(two_cmb_val h0.le h1.le).1, (two_cmb_val h0.le h1.le).2]; ring
  have hUc := hU.2 e0 e1 h0.le (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hUc
  change θ * twoF U f xbar zbar (x, y, z) + (1 - θ) * twoF U f xbar zbar (x', y', z) ≤
      twoF U f xbar zbar (cmb (convex_twoX xbar) h0.le h1.le x x',
        cmb (convex_twoX xbar) h0.le h1.le y y', z) ∧
    (x ≠ x' → θ * twoF U f xbar zbar (x, y, z) + (1 - θ) * twoF U f xbar zbar (x', y', z) <
      twoF U f xbar zbar (cmb (convex_twoX xbar) h0.le h1.le x x',
        cmb (convex_twoX xbar) h0.le h1.le y y', z))
  rw [twoF_of_mem hy, twoF_of_mem hy', twoF_of_mem hyθ, hsum]
  have hθ0 : 0 ≤ θ * (z.1 * f x.1 - (y.1.1 + y.1.2)) +
      (1 - θ) * (z.1 * f x'.1 - (y'.1.1 + y'.1.2)) := by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  have e := hout x x' z θ h0.le h1.le
  refine ⟨hUc.trans (h.U_mono.monotoneOn hθ0 ?_ ?_), fun hne => hUc.trans_lt (h.U_mono hθ0 ?_ ?_)⟩
  · simp only [mem_Ici]; nlinarith
  · nlinarith
  · simp only [mem_Ici]; nlinarith
  · have hfs := hf.2 (twoX_subset_quadrant x.2) (twoX_subset_quadrant x'.2)
      (fun he => hne (Subtype.ext he)) h0 (by linarith : (0 : ℝ) < 1 - θ) (by ring)
    simp only [smul_eq_mul] at hfs
    have hz : 0 < z.1 := by linarith [z.2.1]
    have := mul_lt_mul_of_pos_left hfs hz
    change _ < z.1 * f (θ • x.1 + (1 - θ) • x'.1) - _
    nlinarith

/-- **Exercise 10.2b.** With `U` concave and `f` strictly concave, there is a unique bounded
continuous solution `v` of the functional equation; `v(·, z)` is strictly increasing and strictly
concave; the policy correspondence is a continuous function `g`; and `v = v*`, attained by the
plans that `g` generates. -/
theorem ex_10_2b [Nonempty (twoX xbar)] (h : TwoHyp U f β xbar zbar)
    (hU : ConcaveOn ℝ (Ici 0) U) (hf : StrictConcaveOn ℝ quadrant f)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q) :
    ∃ v : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ,
      bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) v = v ∧
      (∀ w, bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) w = w → w = v) ∧
      (∀ z, StrictMono fun x => v (x, z)) ∧
      (∀ z, IsStrictConcaveS (convex_twoX xbar) fun x => v (x, z)) ∧
      (∀ s, policy (twoModel Q U f β xbar) v s =
        {argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v) s}) ∧
      Continuous (argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v)) ∧
      ∀ s₀, vStar (twoModel Q U f β xbar) s₀ = v s₀ ∧
        planValue (twoModel Q U f β xbar) s₀ (genPlan (twoModel Q U f β xbar) s₀ fun _ =>
          argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v)) = v s₀ := by
  set M := twoModel Q U f β xbar
  have hb := two_boundedDP h Q hQ
  obtain ⟨v, hv, huniq, -, -⟩ := ex_9_7b M hb
  obtain ⟨h910, h911⟩ := two_assumptions h hU hf Q
  obtain ⟨hsc, hpol, hcont⟩ := theorem_9_8 Q _ _ β hb h910 h911 hv
  have hgG : ∀ s, argmaxFn (twoΓ f xbar zbar) (objG M v) s ∈ policy M v s := fun s => by
    rw [hpol s]; exact rfl
  have hopt := fun s₀ => bounded_vStar M hb measurable_snd.fst h.continuous_F.measurable hv
    (g := fun _ => argmaxFn (twoΓ f xbar zbar) (objG M v)) (fun _ => hcont.measurable)
    (fun _ => hgG) s₀
  exact ⟨v, hv, huniq, two_strictMono h Q hQ hv, hsc, hpol, hcont,
    fun s₀ => ⟨(hopt s₀).2.2, (hopt s₀).2.1⟩⟩

/-- **Exercise 10.2b** (differentiability, Theorem 9.10). With `f` strictly concave, at an interior
`x₀` where consumption `c = z₀ f(x₀) − g₁ − g₂` is positive, `U` is differentiable at `c` and `f`
at `x₀`: `Dv(x₀, z₀) = U′(c) z₀ Df(x₀)`. -/
theorem ex_10_2b_diff [Nonempty (twoX xbar)] (h : TwoHyp U f β xbar zbar)
    (hU : ConcaveOn ℝ (Ici 0) U) (hf : StrictConcaveOn ℝ quadrant f)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) v = v) {x₀ : twoX xbar}
    {z₀ : Icc (1 : ℝ) zbar} (hint : twoX xbar ∈ 𝓝 x₀.1)
    (hc : (argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v) (x₀, z₀)).1.1 +
      (argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v) (x₀, z₀)).1.2 <
        z₀.1 * f x₀.1)
    {U' : ℝ} (hU' : HasDerivAt U U' (z₀.1 * f x₀.1 -
      ((argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v) (x₀, z₀)).1.1 +
        (argmaxFn (twoΓ f xbar zbar) (objG (twoModel Q U f β xbar) v) (x₀, z₀)).1.2)))
    {Df : ℝ × ℝ →L[ℝ] ℝ} (hf' : HasFDerivAt f Df x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) ((U' * z₀.1) • Df) x₀.1 := by
  set M := twoModel Q U f β xbar
  have hb := two_boundedDP h Q hQ
  obtain ⟨h910, h911⟩ := two_assumptions h hU hf Q
  set g₀ := argmaxFn (twoΓ f xbar zbar) (objG M v) (x₀, z₀)
  set k₀ := g₀.1.1 + g₀.1.2
  have hev : ∀ᶠ x in 𝓝 x₀, g₀ ∈ M.Γ (x, z₀) := by
    have := ((continuous_const.mul h.continuous_f).tendsto x₀).eventually (lt_mem_nhds hc)
    exact this.mono fun x hx => hx.le
  have hL : HasFDerivAt (fun x => U (z₀.1 * f x - k₀)) ((U' * z₀.1) • Df) x₀.1 := by
    have := hU'.comp_hasFDerivAt x₀.1 ((hf'.const_mul z₀.1).sub_const k₀)
    rwa [smul_smul] at this
  refine ex_9_7f' M hb h910 h911 (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ hne => hne) hv
    (fun _ _ _ _ => rfl) hint hev (hL.congr_of_eventuallyEq ?_)
  have hev' : ∀ᶠ x in 𝓝 x₀.1, k₀ < z₀.1 * f x :=
    ((hf'.continuousAt.const_mul z₀.1).eventually (lt_mem_nhds hc))
  filter_upwards [hev', hint] with x hx hxS
  rw [liftS_of_mem _ hxS]
  exact twoF_of_mem (x := ⟨x, hxS⟩) (z := z₀) (y := g₀) hx.le

/-! ### Weakly concave `f`: a counterexample -/

/-- `T` sees the capital stock only through output: if `f(x) = f(x′)` then
`(Tw)(x, z) = (Tw)(x′, z)`. -/
theorem two_bellman_eq_of_f_eq (h : TwoHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (w : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ) {x x' : twoX xbar} (hxx' : f x.1 = f x'.1)
    (z : Icc (1 : ℝ) zbar) :
    bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) w (x, z) =
      bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) w (x', z) := by
  simp only [bellman_apply, maxValue, objG, rhs, expV, twoΓ, twoF, hxx']

/-- `f(x) = 2(x₁ + x₂)/(1 + x₁ + x₂)`: concave and strictly increasing, but not strictly
concave. -/
noncomputable def cexf2 (x : ℝ × ℝ) : ℝ := cexf (x.1 + x.2)

theorem cexf2_hyp : TwoHyp cexU cexf2 (1 / 10) 3 2 where
  β_pos := by norm_num
  β_lt := by norm_num
  U_cont := cex_hyp.U_cont
  U_mono := cex_hyp.U_mono
  f_cont := cex_hyp.f_cont.comp (continuous_fst.add continuous_snd).continuousOn
    fun x hx => mem_Ici.2 (add_nonneg hx.1 hx.2)
  f_zero := by simp [cexf2, cexf]
  f_mono := fun x x' hx hxx' hne => by
    have hlt : x.1 + x.2 < x'.1 + x'.2 := by
      rcases hxx'.1.lt_or_eq with h1 | h1
      · linarith [hxx'.2]
      · rcases hxx'.2.lt_or_eq with h2 | h2
        · linarith
        · exact absurd (Prod.ext h1 h2) hne
    exact cex_hyp.f_mono (mem_Ici.2 (add_nonneg hx.1 hx.2))
      (mem_Ici.2 (by linarith [hx.1, hx.2])) hlt
  zbar_gt := by norm_num
  xbar_pos := by norm_num
  f_bound := fun x hx => by
    have := cex_hyp.f_mono.monotoneOn (mem_Ici.2 (add_nonneg hx.1 hx.2.1))
      (mem_Ici.2 (by norm_num : (0 : ℝ) ≤ 3)) hx.2.2
    have h3 : (2 : ℝ) * cexf 3 ≤ 3 := by norm_num [cexf]
    change 2 * cexf (x.1 + x.2) ≤ 3
    linarith

theorem cexf2_concave : ConcaveOn ℝ quadrant cexf2 := by
  refine ⟨convex_quadrant, fun x hx y hy a b ha hb hab => ?_⟩
  have := cexf_concave.2 (mem_Ici.2 (add_nonneg hx.1 hx.2)) (mem_Ici.2 (add_nonneg hy.1 hy.2))
    ha hb hab
  simp only [smul_eq_mul] at this ⊢
  simp only [cexf2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  convert this using 2
  ring

/-- `e^{−3} − e^{−2.9} + (1 − e^{−2/11})/10 > 0`. -/
theorem cex2_numeric : 0 < Real.exp (-3) - Real.exp (-(29 / 10)) +
    1 / 10 * (1 - Real.exp (-(2 / 11))) := by
  have e1 : Real.exp (-(29 / 10)) = Real.exp (-3) * Real.exp (1 / 10) := by
    rw [← Real.exp_add]; norm_num
  have h1 : Real.exp (1 / 10) ≤ 10 / 9 := by
    have := Real.add_one_le_exp (-(1 / 10))
    have hp := Real.exp_pos (1 / 10)
    have : Real.exp (1 / 10) * Real.exp (-(1 / 10)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have h3 : Real.exp (-3) ≤ 2 / 17 := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)
    have : Real.exp 3 * Real.exp (-3) = 1 := by rw [← Real.exp_add]; simp
    have := Real.exp_pos (-3)
    nlinarith
  have h4 : Real.exp (-(2 / 11)) ≤ 11 / 13 := by
    have := Real.add_one_le_exp (2 / 11)
    have : Real.exp (2 / 11) * Real.exp (-(2 / 11)) = 1 := by rw [← Real.exp_add]; simp
    have := Real.exp_pos (-(2 / 11))
    nlinarith
  rw [e1]
  have hp := Real.exp_pos (-3)
  nlinarith

/-- **Exercise 10.2b, corrected.** With `f(x) = 2(x₁ + x₂)/(1 + x₁ + x₂)` (concave, as (T4)
allows), `U(c) = 1 − e^{−c}`, `β = 1/10`, `x̄ = 3`, `z̄ = 2` and any Feller `Q`:
`v(·, z)` is not strictly concave, and at `x = (3, 0)`, `z = 2` the policy correspondence
contains two distinct points. -/
theorem ex_10_2b_counterexample (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2)) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : twoX 3 × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : bellman (twoModel Q cexU cexf2 (1 / 10) 3) (two_boundedDP cexf2_hyp Q hQ) v = v) :
    (∀ z, ¬ IsStrictConcaveS (convex_twoX 3) fun x => v (x, z)) ∧
      ∃ y y' : twoX 3, y ≠ y' ∧
        y ∈ policy (twoModel Q cexU cexf2 (1 / 10) 3) v (⟨(3, 0), by norm_num [twoX]⟩, ⟨2, by
          norm_num⟩) ∧
        y' ∈ policy (twoModel Q cexU cexf2 (1 / 10) 3) v (⟨(3, 0), by norm_num [twoX]⟩, ⟨2, by
          norm_num⟩) := by
  set M := twoModel Q cexU cexf2 (1 / 10) 3
  have hb := two_boundedDP cexf2_hyp Q hQ
  have hveq : ∀ (x x' : twoX 3) z, x.1.1 + x.1.2 = x'.1.1 + x'.1.2 → v (x, z) = v (x', z) :=
    fun x x' z hs => by
      rw [← hv]
      exact two_bellman_eq_of_f_eq cexf2_hyp Q hQ v (by simp only [cexf2, hs]) z
  refine ⟨fun z hsc => ?_, ?_⟩
  · -- `v` is constant along `x₁ + x₂ = 1`
    set a : twoX 3 := ⟨(1, 0), by norm_num [twoX]⟩
    set b : twoX 3 := ⟨(0, 1), by norm_num [twoX]⟩
    have hab : a ≠ b := fun he => by
      have := congrArg (fun p : twoX 3 => p.1.1) he
      norm_num [a, b] at this
    have h0 : (0 : ℝ) < 1 / 2 := by norm_num
    have h1 : (1 / 2 : ℝ) < 1 := by norm_num
    have := hsc a b hab (1 / 2) h0 h1
    have e1 := hveq a b z (by norm_num [a, b])
    have e2 := hveq (cmb (convex_twoX 3) h0.le h1.le a b) a z (by
      rw [(two_cmb_val h0.le h1.le).1, (two_cmb_val h0.le h1.le).2]; norm_num [a, b])
    dsimp only at this
    rw [e2, e1] at this
    linarith
  · set x₀ : twoX 3 := ⟨(3, 0), by norm_num [twoX]⟩
    set z₂ : Icc (1 : ℝ) 2 := ⟨2, by norm_num⟩
    set o : twoX 3 := ⟨(0, 0), by norm_num [twoX]⟩
    set y₁ : twoX 3 := ⟨(1 / 10, 0), by norm_num [twoX]⟩
    have hzf : z₂.1 * cexf2 x₀.1 = 3 := by norm_num [z₂, x₀, cexf2, cexf]
    -- `v(o, z′)` is the return to saving nothing from nothing
    have hvo : ∀ z', v (o, z') = 1 / 10 * ∫ z'', v (o, z'') ∂Q z' := fun z' => by
      obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M hb v (o, z')
      rw [hv] at hval
      have hy' : y.1.1 + y.1.2 ≤ z'.1 * cexf2 o.1 := hy
      have hyo : y = o := by
        have h0 : cexf2 o.1 = 0 := by norm_num [o, cexf2, cexf]
        rw [h0, mul_zero] at hy'
        ext <;> simp [o] <;> linarith [y.2.1, y.2.2.1]
      rw [hyo] at hy hval
      simp only [rhs, expV] at hval
      change v (o, z') = twoF cexU cexf2 3 2 (o, o, z') + 1 / 10 * ∫ z'', v (o, z'') ∂Q z'
        at hval
      rw [twoF_of_mem hy] at hval
      have h0 : cexU (z'.1 * cexf2 o.1 - (o.1.1 + o.1.2)) = 0 := by
        norm_num [o, cexf2, cexf, cexU]
      rw [h0, zero_add] at hval
      exact hval
    have hgain : ∀ z', cexU (2 / 11) ≤ v (y₁, z') - v (o, z') := fun z' => by
      obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb v (y₁, z')
      have ho : o ∈ M.Γ (y₁, z') := by
        change (0 : ℝ) + 0 ≤ z'.1 * cexf2 (1 / 10, 0)
        norm_num [cexf2, cexf]
        linarith [z'.2.1]
      have := hmax o ho
      rw [hv] at this
      simp only [rhs, expV] at this
      change twoF cexU cexf2 3 2 (y₁, o, z') + 1 / 10 * ∫ z'', v (o, z'') ∂Q z' ≤ _ at this
      rw [twoF_of_mem ho, ← hvo] at this
      have hf : cexf2 y₁.1 = 2 / 11 := by norm_num [y₁, cexf2, cexf]
      rw [hf] at this
      have hU : cexU (2 / 11) ≤ cexU (z'.1 * (2 / 11) - (o.1.1 + o.1.2)) := by
        have : (o.1.1 + o.1.2) = 0 := by norm_num [o]
        rw [this, sub_zero]
        exact cex_hyp.U_mono.monotoneOn (mem_Ici.2 (by norm_num))
          (mem_Ici.2 (by linarith [z'.2.1])) (by linarith [z'.2.1])
      linarith
    -- saving `1/10` beats saving nothing at `(x₀, 2)`
    obtain ⟨y, hy, hval, hmax⟩ := exists_bellman_argmax M hb v (x₀, z₂)
    rw [hv] at hval hmax
    have hy₁ : y₁ ∈ M.Γ (x₀, z₂) := by
      change (1 / 10 : ℝ) + 0 ≤ _
      rw [hzf]; norm_num
    have ho : o ∈ M.Γ (x₀, z₂) := by
      change (0 : ℝ) + 0 ≤ _
      rw [hzf]; norm_num
    have hint := integrable_section_v (Q z₂) v
    have hcmp : rhs M v (x₀, z₂) o < rhs M v (x₀, z₂) y₁ := by
      simp only [rhs, expV]
      change twoF cexU cexf2 3 2 (x₀, o, z₂) + 1 / 10 * ∫ z', v (o, z') ∂Q z₂ <
        twoF cexU cexf2 3 2 (x₀, y₁, z₂) + 1 / 10 * ∫ z', v (y₁, z') ∂Q z₂
      rw [twoF_of_mem ho, twoF_of_mem hy₁, hzf]
      have hE : cexU (2 / 11) ≤ ∫ z', v (y₁, z') ∂Q z₂ - ∫ z', v (o, z') ∂Q z₂ := by
        rw [← integral_sub (hint y₁) (hint o)]
        have := integral_mono (μ := Q z₂) (integrable_const (cexU (2 / 11)))
          ((hint y₁).sub (hint o)) hgain
        simpa using this
      have := cex2_numeric
      simp only [cexU] at hE ⊢
      norm_num [o, y₁] at hE ⊢
      nlinarith
    -- an optimal `y` saves `k > 0`, which can be held as `(k, 0)` or `(0, k)`
    have hk : 0 < y.1.1 + y.1.2 := by
      rcases (add_nonneg y.2.1 y.2.2.1).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hyo : y = o := by
          ext <;> simp [o] <;> linarith [y.2.1, y.2.2.1]
        have := hmax y₁ hy₁
        rw [hval, hyo] at this
        linarith
    set k := y.1.1 + y.1.2
    have hk3 : k ≤ 3 := y.2.2.2
    set p : twoX 3 := ⟨(k, 0), ⟨hk.le, le_rfl, by simp only; linarith⟩⟩
    set q : twoX 3 := ⟨(0, k), ⟨le_rfl, hk.le, by simp only; linarith⟩⟩
    have hrhs : ∀ y' : twoX 3, y'.1.1 + y'.1.2 = k → rhs M v (x₀, z₂) y' = rhs M v (x₀, z₂) y :=
      fun y' hy' => by
        simp only [rhs, expV]
        change twoF cexU cexf2 3 2 (x₀, y', z₂) + 1 / 10 * ∫ z', v (y', z') ∂Q z₂ =
          twoF cexU cexf2 3 2 (x₀, y, z₂) + 1 / 10 * ∫ z', v (y, z') ∂Q z₂
        simp only [twoF, hy']
        congr 2
        exact integral_congr_ae (Eventually.of_forall fun z' => hveq y' y z' hy')
    have hyk : k ≤ z₂.1 * cexf2 x₀.1 := hy
    have hp : p ∈ policy M v (x₀, z₂) :=
      ⟨show k + 0 ≤ _ by linarith, by rw [hrhs p (by simp [p]), ← hval]⟩
    have hq : q ∈ policy M v (x₀, z₂) :=
      ⟨show 0 + k ≤ _ by linarith, by rw [hrhs q (by simp [q]), ← hval]⟩
    refine ⟨p, q, fun he => ?_, hp, hq⟩
    have := congrArg (fun r : twoX 3 => r.1.1) he
    simp only [p, q] at this
    linarith

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Two capital goods: reduction to one endogenous state

SLP §10.2, Exercise 10.2d, p. 290. Output is `z f(x₁, x₂)` whatever the split, and next period's
output from total saving `k` is at most `z′ φ(k)`, `φ(k) = max_{y ≥ 0, y₁ + y₂ = k} f(y)`, with
equality at the best split (which does not depend on `z′`, since the shock is multiplicative).
So the model is the one-sector model of §10.1 with production function `φ`.

* `twoφ`, `continuous_twoφ`, `twoφ_attain`, `le_twoφ`: `φ`, computed over the shares
  `t ∈ [0, 1]`, is continuous and attained.
* `twoφ_hyp`, `twoφ_concave`: `φ` satisfies (T1)–(T3) and `z̄ φ(x̄) ≤ x̄`, and is concave if `f`
  is, so the analysis of Exercise 10.1 applies to it.
* **Exercise 10.2d** (`ex_10_2d`): if `v₂` solves the two-capital functional equation and `v₁`
  the one-sector equation with production `φ`, then `v₂(x, z) = v₁(k, z)` whenever
  `f(x) = φ(k)`, and every `x` has such a `k`. The proof shows that
  `w(x, z) = max_{0 ≤ k ≤ z f(x)} {U[z f(x) − k] + β ∫ v₁(k, z′) Q(z, dz′)}` is a fixed point of
  the two-capital operator.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {U : ℝ → ℝ} {f : ℝ × ℝ → ℝ} {β xbar zbar : ℝ}

/-- `φ(k) = max_{t ∈ [0, 1]} f(tk, (1 − t)k)` (the arguments clamped at `0`, so that `φ` is defined
and continuous on all of `ℝ`). -/
noncomputable def twoφ (f : ℝ × ℝ → ℝ) (k : ℝ) : ℝ :=
  sSup ((fun t : ℝ => f (max (t * k) 0, max ((1 - t) * k) 0)) '' Icc 0 1)

theorem continuous_twoφ_aux (h : TwoHyp U f β xbar zbar) :
    Continuous fun p : ℝ × ℝ => f (max (p.2 * p.1) 0, max ((1 - p.2) * p.1) 0) :=
  h.f_cont.comp_continuous (by fun_prop) fun _ => ⟨le_max_right _ _, le_max_right _ _⟩

theorem continuous_twoφ (h : TwoHyp U f β xbar zbar) : Continuous (twoφ f) :=
  isCompact_Icc.continuous_sSup (f := fun k t => f (max (t * k) 0, max ((1 - t) * k) 0))
    (continuous_twoφ_aux h)

theorem continuous_twoφ_section (h : TwoHyp U f β xbar zbar) (k : ℝ) :
    Continuous fun t : ℝ => f (max (t * k) 0, max ((1 - t) * k) 0) :=
  (continuous_twoφ_aux h).comp
    (continuous_const.prodMk continuous_id : Continuous fun t : ℝ => (k, t))

theorem twoφ_bdd (h : TwoHyp U f β xbar zbar) (k : ℝ) :
    BddAbove ((fun t : ℝ => f (max (t * k) 0, max ((1 - t) * k) 0)) '' Icc 0 1) :=
  (isCompact_Icc.image (continuous_twoφ_section h k)).bddAbove

/-- `φ(k)` is attained at some share `t ∈ [0, 1]`. -/
theorem twoφ_attain (h : TwoHyp U f β xbar zbar) {k : ℝ} (hk : 0 ≤ k) :
    ∃ t ∈ Icc (0 : ℝ) 1, twoφ f k = f (t * k, (1 - t) * k) := by
  obtain ⟨t, ht, he⟩ := (isCompact_Icc.image (continuous_twoφ_section h k)).sSup_mem
    ((nonempty_Icc.2 zero_le_one).image _)
  refine ⟨t, ht, ?_⟩
  rw [twoφ, ← he]
  simp only [max_eq_left (mul_nonneg ht.1 hk), max_eq_left (mul_nonneg (sub_nonneg.2 ht.2) hk)]

/-- `f(y) ≤ φ(y₁ + y₂)` on `ℝ²₊`. -/
theorem le_twoφ (h : TwoHyp U f β xbar zbar) {y : ℝ × ℝ} (hy : y ∈ quadrant) :
    f y ≤ twoφ f (y.1 + y.2) := by
  obtain ⟨y1, y2⟩ := y
  obtain ⟨h1, h2⟩ := hy
  simp only at h1 h2 ⊢
  rcases (add_nonneg h1 h2).lt_or_eq with hk | hk
  · refine le_csSup (twoφ_bdd h _) ⟨y1 / (y1 + y2), ⟨div_nonneg h1 hk.le,
      (div_le_one hk).2 (by linarith)⟩, ?_⟩
    have e1 : y1 / (y1 + y2) * (y1 + y2) = y1 := div_mul_cancel₀ _ hk.ne'
    have e2 : (1 - y1 / (y1 + y2)) * (y1 + y2) = y2 := by
      rw [sub_mul, e1, one_mul]; ring
    simp only [e1, e2, max_eq_left h1, max_eq_left h2]
  · have hy1 : y1 = 0 := by linarith
    have hy2 : y2 = 0 := by linarith
    subst hy1 hy2
    refine le_csSup (twoφ_bdd h _) ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    simp

theorem twoφ_zero (h : TwoHyp U f β xbar zbar) : twoφ f 0 = 0 := by
  obtain ⟨t, -, ht⟩ := twoφ_attain h le_rfl
  rw [ht, mul_zero, mul_zero]
  exact h.f_zero

/-- `φ` satisfies (T1)–(T3) and `z̄ φ(x̄) ≤ x̄`: the hypotheses of §10.1. -/
theorem twoφ_hyp (h : TwoHyp U f β xbar zbar) : GrowthHyp U (twoφ f) β xbar zbar where
  β_pos := h.β_pos
  β_lt := h.β_lt
  U_cont := h.U_cont
  U_mono := h.U_mono
  f_cont := (continuous_twoφ h).continuousOn
  f_zero := twoφ_zero h
  f_mono := fun k hk k' hk' hkk' => by
    have hk0 : (0 : ℝ) ≤ k := hk
    obtain ⟨t, ht, he⟩ := twoφ_attain h hk0
    rw [he]
    have hq : (t * k, (1 - t) * k) ∈ quadrant :=
      ⟨mul_nonneg ht.1 hk0, mul_nonneg (sub_nonneg.2 ht.2) hk0⟩
    have hle : (t * k, (1 - t) * k) ≤ (t * k', (1 - t) * k') :=
      ⟨mul_le_mul_of_nonneg_left hkk'.le ht.1,
        mul_le_mul_of_nonneg_left hkk'.le (sub_nonneg.2 ht.2)⟩
    have hne : (t * k, (1 - t) * k) ≠ (t * k', (1 - t) * k') := fun he' => by
      have h1 := congrArg Prod.fst he'
      have h2 := congrArg Prod.snd he'
      simp only at h1 h2
      linarith
    refine (h.f_mono _ _ hq hle hne).trans_le ?_
    have := le_twoφ h (y := (t * k', (1 - t) * k')) ⟨mul_nonneg ht.1 (by linarith),
      mul_nonneg (sub_nonneg.2 ht.2) (by linarith)⟩
    simpa [← add_mul] using this
  zbar_gt := h.zbar_gt
  xbar_pos := h.xbar_pos
  xbar_maintain := by
    obtain ⟨t, ht, he⟩ := twoφ_attain h h.xbar_pos.le
    rw [he]
    refine h.f_bound _ ⟨mul_nonneg ht.1 h.xbar_pos.le,
      mul_nonneg (sub_nonneg.2 ht.2) h.xbar_pos.le, ?_⟩
    simp only
    linarith

/-- (T4) passes to `φ`: if `f` is concave on `ℝ²₊`, `φ` is concave on `[0, ∞)`. -/
theorem twoφ_concave (h : TwoHyp U f β xbar zbar) (hf : ConcaveOn ℝ quadrant f) :
    ConcaveOn ℝ (Ici 0) (twoφ f) := by
  refine ⟨convex_Ici 0, fun k hk k' hk' a b ha hb hab => ?_⟩
  have hk0 : (0 : ℝ) ≤ k := hk
  have hk0' : (0 : ℝ) ≤ k' := hk'
  obtain ⟨t, ht, he⟩ := twoφ_attain h hk0
  obtain ⟨t', ht', he'⟩ := twoφ_attain h hk0'
  have hq : (t * k, (1 - t) * k) ∈ quadrant :=
    ⟨mul_nonneg ht.1 hk0, mul_nonneg (sub_nonneg.2 ht.2) hk0⟩
  have hq' : (t' * k', (1 - t') * k') ∈ quadrant :=
    ⟨mul_nonneg ht'.1 hk0', mul_nonneg (sub_nonneg.2 ht'.2) hk0'⟩
  have hc := hf.2 hq hq' ha hb hab
  have hmix := convex_quadrant hq hq' ha hb hab
  have hle := le_twoφ h hmix
  rw [he, he', smul_eq_mul, smul_eq_mul]
  refine hc.trans (hle.trans_eq ?_)
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Total capital `y₁ + y₂` as a point of `[0, x̄]`. -/
def twoσ (y : twoX xbar) : Icc (0 : ℝ) xbar := ⟨y.1.1 + y.1.2, add_nonneg y.2.1 y.2.2.1, y.2.2.2⟩

/-- **Exercise 10.2d.** The two-capital model is the one-sector model with production
`φ(k) = max_{y₁ + y₂ = k} f(y)`: `φ` satisfies the hypotheses of §10.1 (and (T4) if `f` does),
and if `v₂` and `v₁` are the fixed points of the two operators, `v₂(x, z) = v₁(k, z)` whenever
`f(x) = φ(k)`; every `x` has such a `k ≤ x₁ + x₂`. -/
theorem ex_10_2d (h : TwoHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v₂ : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv₂ : bellman (twoModel Q U f β xbar) (two_boundedDP h Q hQ) v₂ = v₂)
    {v₁ : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv₁ : bellman (growthModel Q U (twoφ f) β xbar) (growth_boundedDP (twoφ_hyp h) Q hQ) v₁ =
      v₁) :
    (∀ x : twoX xbar, ∃ k : Icc (0 : ℝ) xbar, k.1 ≤ x.1.1 + x.1.2 ∧ twoφ f k.1 = f x.1) ∧
      ∀ (x : twoX xbar) (k : Icc (0 : ℝ) xbar) (z : Icc (1 : ℝ) zbar),
        f x.1 = twoφ f k.1 → v₂ (x, z) = v₁ (k, z) := by
  set M₂ := twoModel Q U f β xbar
  have hb₂ := two_boundedDP h Q hQ
  set M₁ := growthModel Q U (twoφ f) β xbar
  have hb₁ := growth_boundedDP (twoφ_hyp h) Q hQ
  have : CompactSpace (twoX xbar) := isCompact_iff_compactSpace.1 (isCompact_twoX xbar)
  -- the auxiliary problem: choose total saving `k ≤ z f(x)`
  set Γw : twoX xbar × Icc (1 : ℝ) zbar → Set (Icc (0 : ℝ) xbar) :=
    fun s => {k | k.1 ≤ s.2.1 * f s.1.1}
  set Hw : (twoX xbar × Icc (1 : ℝ) zbar) × Icc (0 : ℝ) xbar → ℝ :=
    fun p => U (max (p.1.2.1 * f p.1.1.1 - p.2.1) 0) + β * ∫ z', v₁ (p.2, z') ∂Q p.1.2
  have hzf : Continuous fun s : twoX xbar × Icc (1 : ℝ) zbar => s.2.1 * f s.1.1 :=
    (continuous_subtype_val.comp continuous_snd).mul (h.continuous_f.comp continuous_fst)
  have hΓl := isLHC_Icc_le hzf h.zf_nonneg h.xbar_pos.le
  have hΓu := isUHC_Icc_le hzf h.zf_nonneg h.xbar_pos.le
  have hΓc : ∀ s, IsCompact (Γw s) := fun _ =>
    IsClosed.isCompact (isClosed_le continuous_subtype_val continuous_const)
  have hmop := lemma_9_5_compact (W := Icc (0 : ℝ) xbar) Q hQ v₁ v₁.continuous
    ⟨‖v₁‖, fun p => by rw [← Real.norm_eq_abs]; exact v₁.norm_coe_le_norm p⟩
  have hHc : Continuous Hw :=
    (h.U_cont.comp_continuous ((((continuous_subtype_val.comp continuous_fst.snd).mul
      (h.continuous_f.comp continuous_fst.fst)).sub
      (continuous_subtype_val.comp continuous_snd)).max continuous_const)
      fun _ => mem_Ici.2 (le_max_right _ _)).add
      (continuous_const.mul (hmop.comp (continuous_snd.prodMk continuous_fst.snd)))
  have h36 := theorem_3_6 hHc.continuousOn hΓc hΓl hΓu
  set w : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ :=
    mkOfCompact ⟨fun s => maxValue Hw Γw s, h36.1⟩
  have hwv : ∀ s, w s = maxValue Hw Γw s := fun _ => rfl
  have hΓne : ∀ s, (Γw s).Nonempty := fun s => (hΓl s).1
  -- `w(y, z′) ≤ v₁(y₁ + y₂, z′)`
  have hw_le : ∀ (y : twoX xbar) (z' : Icc (1 : ℝ) zbar), w (y, z') ≤ v₁ (twoσ y, z') := by
    intro y z'
    obtain ⟨k, hk, hval, -⟩ := exists_argmax hHc.continuousOn (hΓc (y, z')) (hΓne (y, z'))
    rw [hwv, ← hval]
    have hk' : k.1 ≤ z'.1 * f y.1 := hk
    have hfφ : f y.1 ≤ twoφ f (twoσ y).1 := le_twoφ h (twoX_subset_quadrant y.2)
    have hz : 0 ≤ z'.1 := by linarith [z'.2.1]
    have hkφ : k ∈ growthΓ (twoφ f) xbar zbar (twoσ y, z') :=
      show k.1 ≤ z'.1 * twoφ f (twoσ y).1 from hk'.trans (mul_le_mul_of_nonneg_left hfφ hz)
    obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M₁ hb₁ v₁ (twoσ y, z')
    have := hmax k hkφ
    rw [hv₁] at this
    refine le_trans ?_ this
    change U (max (z'.1 * f y.1 - k.1) 0) + β * _ ≤
      U (max (z'.1 * twoφ f (twoσ y).1 - k.1) 0) + β * _
    gcongr ?_ + _
    refine h.U_mono.monotoneOn (mem_Ici.2 (le_max_right _ _)) (mem_Ici.2 (le_max_right _ _)) ?_
    exact max_le_max (by nlinarith) le_rfl
  -- `w(x, z) = v₁(k, z)` when `f(x) = φ(k)`
  have hw_eq : ∀ (x : twoX xbar) (k : Icc (0 : ℝ) xbar) (z : Icc (1 : ℝ) zbar),
      f x.1 = twoφ f k.1 → w (x, z) = v₁ (k, z) := by
    intro x k z hfk
    rw [hwv, ← hv₁, bellman_apply]
    simp only [maxValue, Hw, Γw, objG, rhs, expV, growthΓ, growthF, hfk]
  -- `w` is a fixed point of the two-capital operator
  have hfix : bellman M₂ hb₂ w = w := by
    ext ⟨x, z⟩
    obtain ⟨y, hy, hval, hmax⟩ := exists_bellman_argmax M₂ hb₂ w (x, z)
    have hint := integrable_section_v (Q z) w
    have hint₁ := integrable_section_v (Q z) v₁
    apply le_antisymm
    · rw [hval]
      have hyσ : twoσ y ∈ Γw (x, z) := hy
      have hle := le_maxValue hHc.continuousOn (hΓc (x, z)) hyσ
      rw [← hwv] at hle
      refine le_trans ?_ hle
      simp only [rhs, expV]
      change twoF U f xbar zbar (x, y, z) + β * ∫ z', w (y, z') ∂Q z ≤
        U (max (z.1 * f x.1 - (twoσ y).1) 0) + β * ∫ z', v₁ (twoσ y, z') ∂Q z
      have e : ((twoσ y : Icc (0 : ℝ) xbar) : ℝ) = y.1.1 + y.1.2 := rfl
      rw [twoF_of_mem hy, e, max_eq_left (sub_nonneg.2 hy)]
      have hI := integral_mono (hint y) (hint₁ _) fun z' => hw_le y z'
      have := mul_le_mul_of_nonneg_left hI h.β_pos.le
      linarith
    · obtain ⟨k, hk, hkval, -⟩ := exists_argmax hHc.continuousOn (hΓc (x, z)) (hΓne (x, z))
      obtain ⟨t, ht, he⟩ := twoφ_attain h k.2.1
      set a : twoX xbar := ⟨(t * k.1, (1 - t) * k.1), mul_nonneg ht.1 k.2.1,
        mul_nonneg (sub_nonneg.2 ht.2) k.2.1, by simp only; linarith [k.2.2]⟩
      have hsum : a.1.1 + a.1.2 = k.1 := by simp only [a]; ring
      have ha : a ∈ M₂.Γ (x, z) := show a.1.1 + a.1.2 ≤ z.1 * f x.1 by rw [hsum]; exact hk
      have := hmax a ha
      rw [hwv, ← hkval]
      refine le_trans (le_of_eq ?_) this
      simp only [rhs, expV]
      change U (max (z.1 * f x.1 - k.1) 0) + β * ∫ z', v₁ (k, z') ∂Q z =
        twoF U f xbar zbar (x, a, z) + β * ∫ z', w (a, z') ∂Q z
      rw [twoF_of_mem ha, hsum, max_eq_left (sub_nonneg.2 hk)]
      congr 2
      exact integral_congr_ae (Eventually.of_forall fun z' => (hw_eq a k z' he.symm).symm)
  obtain ⟨v, -, huniq, -, -⟩ := ex_9_7b M₂ hb₂
  have hwv₂ : w = v₂ := (huniq w hfix).trans (huniq v₂ hv₂).symm
  refine ⟨fun x => ?_, fun x k z hfk => by rw [← hwv₂]; exact hw_eq x k z hfk⟩
  -- the intermediate value theorem
  have hs := add_nonneg x.2.1 x.2.2.1
  have hivt := intermediate_value_Icc hs (continuous_twoφ h).continuousOn
  rw [twoφ_zero h] at hivt
  obtain ⟨k, hk, hke⟩ := hivt ⟨h.f_nonneg (twoX_subset_quadrant x.2),
    le_twoφ h (twoX_subset_quadrant x.2)⟩
  exact ⟨⟨k, hk.1, hk.2.trans x.2.2.2⟩, hk.2, hke⟩

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal growth with many goods

SLP §10.3, pp. 290–292. There are `l` capital goods, `X ⊆ ℝˡ` convex, and `M` consumption goods
with utility `U : ℝᴹ₊ → ℝ`. The technology `Φ : X × Z ⇉ ℝᴹ₊ × X` gives the feasible pairs
`(c, y)` of consumption and end-of-period capital; it satisfies (a) nonempty, compact-valued and
continuous, (b) monotone in `x`, and (c) jointly convex in `(x, c, y)` (`TechHyp`). The reduced
problem has `Γ(x, z) = {y : (c, y) ∈ Φ(x, z) for some c}` and
`F(x, y, z) = max {U(c) : (c, y) ∈ Φ(x, z)}`.

* **Exercise 10.3a** (`many_boundedDP`, `ex_10_3a`). `Γ` satisfies Assumption 9.6, `F` is bounded
  (Assumption 9.7), Assumptions 9.9 and 9.11 hold, and `F` is nondecreasing in `x` and concave on
  `A_z`. So `v` exists and is unique, `v(·, z)` is nondecreasing and concave, and `G` is nonempty,
  compact-valued and u.h.c. That `F` is continuous on `A` is assumed: it is a maximum over the
  fibre `{c : (c, y) ∈ Φ(x, z)}`, and the Theorem of the Maximum needs that fibre to vary
  continuously in `(x, y, z)`, which the continuity of `Φ` does not give.
* **Correction.** Only the weak forms of Assumptions 9.8 and 9.10 follow from (a)–(c), and the
  conclusions drawn on p. 292 from Theorems 9.6–9.8 — `v(·, z)` strictly increasing and strictly
  concave, `g` single-valued — are false. If `Φ(x, z) = [0, 1] × X` for all `(x, z)`, which
  satisfies (a)–(c), `v(·, z)` is constant and every `y ∈ X` is optimal
  (`ex_10_3a_counterexample`).
* **Exercise 10.3b** (`ex_10_3b`). Let `π*` be generated by a measurable selection from `G` and
  `γ*_t` a measurable selection of a maximizing consumption (one exists: `exists_gammaStar`).
  Then `(γ*, π*)` maximizes `u(c) = Σ βᵗ ∫ U(c_t) dμᵗ` over all measurable plans with
  `(c_t, x_{t+1}) ∈ Φ(x_t, z_t)`, with value `v(x₀, z₀)`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- The nonnegative orthant `ℝᴹ₊`. -/
def Cplus (m : ℕ) : Set (Fin m → ℝ) := {c | ∀ i, 0 ≤ c i}

theorem convex_Cplus (m : ℕ) : Convex ℝ (Cplus m) := fun x hx y hy a b ha hb _ i => by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := hx i
  have := hy i
  positivity

variable {l m : ℕ} {SX : Set (Fin l → ℝ)} {hX : Convex ℝ SX} {Z : Type*} [MetricSpace Z]
  [MeasurableSpace Z]

/-- Assumptions (a)–(c) of SLP §10.3 on the technology `Φ`. -/
structure TechHyp (hX : Convex ℝ SX) (Φ : SX × Z → Set (Cplus m × SX)) : Prop where
  nonempty : ∀ s, (Φ s).Nonempty
  compact : ∀ s, IsCompact (Φ s)
  lhc : ∀ s, IsLHC Φ s
  uhc : ∀ s, IsUHC Φ s
  mono : ∀ x x' z, x ≤ x' → Φ (x, z) ⊆ Φ (x', z)
  joint : ∀ z x x' (p p' : Cplus m × SX) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1), p ∈ Φ (x, z) →
    p' ∈ Φ (x', z) →
      (cmb (convex_Cplus m) h0 h1 p.1 p'.1, cmb hX h0 h1 p.2 p'.2) ∈ Φ (cmb hX h0 h1 x x', z)

/-- `Γ(x, z) = {y : (c, y) ∈ Φ(x, z) for some c}`. -/
def manyΓ (Φ : SX × Z → Set (Cplus m × SX)) (s : SX × Z) : Set SX := Prod.snd '' Φ s

/-- `F(x, y, z) = max {U(c) : (c, y) ∈ Φ(x, z)}` (and `0` off the graph). -/
noncomputable def manyF (U : Cplus m → ℝ) (Φ : SX × Z → Set (Cplus m × SX))
    (p : SX × SX × Z) : ℝ :=
  sSup (U '' {c | (c, p.2.1) ∈ Φ (p.1, p.2.2)})

/-- The reduced model in the first formulation of Chapter 9. -/
noncomputable abbrev manyModel (Q : Kernel Z Z) (U : Cplus m → ℝ)
    (Φ : SX × Z → Set (Cplus m × SX)) (β : ℝ) : Model SX SX Z :=
  Model.first Q (manyΓ Φ) (manyF U Φ) β

variable {Φ : SX × Z → Set (Cplus m × SX)} {U : Cplus m → ℝ}

omit [MeasurableSpace Z] in
/-- The fibre `{c : (c, y) ∈ Φ(s)}` is compact. -/
theorem isCompact_fiber (hT : TechHyp hX Φ) (s : SX × Z) (y : SX) :
    IsCompact {c | (c, y) ∈ Φ s} := by
  have hK := ((hT.compact s).inter_right (isClosed_univ.prod (isClosed_singleton (x := y)))).image
    continuous_fst
  convert hK using 1
  ext c
  simp

omit [MeasurableSpace Z] in
/-- For `y ∈ Γ(x, z)`, the maximum in `F` is attained. -/
theorem manyF_spec (hT : TechHyp hX Φ) (hU : Continuous U) {x y : SX} {z : Z}
    (hy : y ∈ manyΓ Φ (x, z)) :
    ∃ c, (c, y) ∈ Φ (x, z) ∧ manyF U Φ (x, y, z) = U c ∧
      ∀ c', (c', y) ∈ Φ (x, z) → U c' ≤ U c := by
  obtain ⟨⟨c₀, y₀⟩, hp, rfl⟩ := hy
  obtain ⟨c, hc, hmax⟩ := (isCompact_fiber hT (x, z) y₀).exists_isMaxOn ⟨c₀, hp⟩
    hU.continuousOn
  refine ⟨c, hc, ?_, fun c' hc' => hmax hc'⟩
  exact (IsGreatest.csSup_eq ⟨⟨c, hc, rfl⟩, by rintro _ ⟨c', hc', rfl⟩; exact hmax hc'⟩)

omit [MeasurableSpace Z] in
theorem le_manyF (hT : TechHyp hX Φ) (hU : Continuous U) {x y : SX} {z : Z} {c : Cplus m}
    (hc : (c, y) ∈ Φ (x, z)) : U c ≤ manyF U Φ (x, y, z) := by
  obtain ⟨c', -, he, hmax⟩ := manyF_spec hT hU (y := y) ⟨(c, y), hc, rfl⟩
  rw [he]
  exact hmax c hc

/-- Assumptions 9.6 and 9.7 and Lemma 9.5 for the reduced model, given that `F` is continuous on
`A` (the Theorem of the Maximum does not give this; see the module docstring). -/
theorem many_boundedDP (hT : TechHyp hX Φ) (hU : Continuous U) (hUb : ∃ B, ∀ c, |U c| ≤ B)
    (Q : Kernel Z Z) [IsMarkovKernel Q] (hQ : PreservesBC SX Q) {β : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hFc : ContinuousOn (manyF U Φ) (graphA (manyModel Q U Φ β))) :
    BoundedDP (manyModel Q U Φ β) := by
  obtain ⟨B, hB⟩ := hUb
  refine ⟨fun s => (hT.nonempty s).image _, fun s => (hT.compact s).image continuous_snd,
    fun s => ⟨(hT.nonempty s).image _, ?_⟩, fun s => ⟨(hT.nonempty s).image _, ?_⟩, hFc,
    ⟨B, fun ⟨x, y, z⟩ hp => ?_⟩, hβ, hβ1, continuous_fst.snd.continuousOn,
    contExp_first Q _ _ β hQ⟩
  · rintro _ ⟨⟨c, y⟩, hp, rfl⟩ xs hxs
    obtain ⟨N, ps, hps, hlim⟩ := (hT.lhc s).2 (c, y) hp xs hxs
    exact ⟨N, fun n => (ps n).2, fun n hn => ⟨ps n, hps n hn, rfl⟩,
      (continuous_snd.tendsto _).comp hlim⟩
  · intro xs hxs ys hys
    choose ps hps hpy using hys
    obtain ⟨p, hp, φ, hφ, hlim⟩ := (hT.uhc s).2 xs hxs ps hps
    refine ⟨p.2, ⟨p, hp, rfl⟩, φ, hφ, ?_⟩
    have := (continuous_snd.tendsto p).comp hlim
    refine this.congr fun n => ?_
    simp [hpy]
  · obtain ⟨c, -, he, -⟩ := manyF_spec hT hU (x := x) (z := z) hp
    change |manyF U Φ (x, y, z)| ≤ B
    rw [he]
    exact hB c

/-- `F` is `0` off the graph, so it is measurable. -/
theorem measurable_manyF [OpensMeasurableSpace (SX × SX × Z)] (hT : TechHyp hX Φ) (Q : Kernel Z Z)
    {β : ℝ} (hFc : ContinuousOn (manyF U Φ) (graphA (manyModel Q U Φ β))) :
    Measurable (manyF U Φ) := by
  classical
  have hcl : IsClosed (graphA (manyModel Q U Φ β)) := by
    refine isClosed_graphA _ fun s => ⟨⟨(hT.nonempty s).some.2, (hT.nonempty s).some,
      (hT.nonempty s).some_mem, rfl⟩, fun xs hxs ys hys => ?_⟩
    choose ps hps hpy using hys
    obtain ⟨p, hp, φ, hφ, hlim⟩ := (hT.uhc s).2 xs hxs ps hps
    refine ⟨p.2, ⟨p, hp, rfl⟩, φ, hφ, ?_⟩
    exact ((continuous_snd.tendsto p).comp hlim).congr fun n => by simp [hpy]
  have heq : manyF U Φ = (graphA (manyModel Q U Φ β)).piecewise (manyF U Φ) fun _ => 0 := by
    funext p
    by_cases hp : p ∈ graphA (manyModel Q U Φ β)
    · simp [hp]
    · simp only [Set.piecewise_eq_of_notMem _ _ _ hp]
      have : {c | (c, p.2.1) ∈ Φ (p.1, p.2.2)} = ∅ := by
        ext c
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun hc => hp ⟨(c, p.2.1), hc, rfl⟩
      simp [manyF, this]
  rw [heq]
  exact hFc.measurable_piecewise continuousOn_const hcl.measurableSet

/-! ### Exercise 10.3a -/

omit [MeasurableSpace Z] in
/-- `F` is nondecreasing in `x` (the weak form of Assumption 9.8), by (b). -/
theorem manyF_mono (hT : TechHyp hX Φ) (hU : Continuous U) {x x' y : SX} {z : Z}
    (hxx' : x ≤ x') (hy : y ∈ manyΓ Φ (x, z)) : manyF U Φ (x, y, z) ≤ manyF U Φ (x', y, z) := by
  obtain ⟨c, hc, he, -⟩ := manyF_spec hT hU hy
  rw [he]
  exact le_manyF hT hU (hT.mono x x' z hxx' hc)

omit [MeasurableSpace Z] in
/-- Assumption 9.11 and the weak form of Assumption 9.10: `F(·, ·, z)` is concave on `A_z`. -/
theorem manyF_concave (hT : TechHyp hX Φ) (hU : Continuous U)
    (hUc : IsConcaveS (convex_Cplus m) U) {x x' y y' : SX} {z : Z} (hy : y ∈ manyΓ Φ (x, z))
    (hy' : y' ∈ manyΓ Φ (x', z)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    cmb hX h0 h1 y y' ∈ manyΓ Φ (cmb hX h0 h1 x x', z) ∧
      θ * manyF U Φ (x, y, z) + (1 - θ) * manyF U Φ (x', y', z) ≤
        manyF U Φ (cmb hX h0 h1 x x', cmb hX h0 h1 y y', z) := by
  obtain ⟨c, hc, he, -⟩ := manyF_spec hT hU hy
  obtain ⟨c', hc', he', -⟩ := manyF_spec hT hU hy'
  have hj := hT.joint z x x' (c, y) (c', y') θ h0 h1 hc hc'
  refine ⟨⟨_, hj, rfl⟩, ?_⟩
  rw [he, he']
  exact (hUc c c' θ h0 h1).trans (le_manyF hT hU hj)

/-- `T` maps functions nondecreasing in `x` to functions nondecreasing in `x`. -/
theorem many_bellman_mono [OpensMeasurableSpace Z]
    (hT : TechHyp hX Φ) (hU : Continuous U) {Q : Kernel Z Z} [IsMarkovKernel Q] {β : ℝ}
    (h : BoundedDP (manyModel Q U Φ β)) {w : SX × Z →ᵇ ℝ} (z : Z) :
    Monotone fun x => bellman (manyModel Q U Φ β) h w (x, z) := by
  intro x x' hxx'
  obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax (manyModel Q U Φ β) h w (x, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax (manyModel Q U Φ β) h w (x', z)
  have hy' : y ∈ manyΓ Φ (x', z) := by
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨p, hT.mono x x' z hxx' hp, rfl⟩
  have := hmax y hy'
  dsimp only
  rw [hval]
  refine le_trans ?_ this
  simp only [rhs, expV]
  have := manyF_mono hT hU hxx' hy
  linarith

/-- **Exercise 10.3a** (with `F` continuous on `A`). There is a unique `v ∈ C(S)` solving the
functional equation; `G` is nonempty, compact-valued and u.h.c.; and `v(·, z)` is nondecreasing
and concave. -/
theorem ex_10_3a [OpensMeasurableSpace Z] (hT : TechHyp hX Φ)
    (hU : Continuous U) (hUb : ∃ B, ∀ c, |U c| ≤ B) (hUc : IsConcaveS (convex_Cplus m) U)
    (Q : Kernel Z Z) [IsMarkovKernel Q] (hQ : PreservesBC SX Q) {β : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hFc : ContinuousOn (manyF U Φ) (graphA (manyModel Q U Φ β))) :
    ∃ v : SX × Z →ᵇ ℝ,
      bellman (manyModel Q U Φ β) (many_boundedDP hT hU hUb Q hQ hβ hβ1 hFc) v = v ∧
      (∀ w, bellman (manyModel Q U Φ β) (many_boundedDP hT hU hUb Q hQ hβ hβ1 hFc) w = w →
        w = v) ∧
      (∀ s, (policy (manyModel Q U Φ β) v s).Nonempty ∧
        IsCompact (policy (manyModel Q U Φ β) v s) ∧ IsUHC (policy (manyModel Q U Φ β) v) s) ∧
      (∀ z, Monotone fun x => v (x, z)) ∧ ∀ z, IsConcaveS hX fun x => v (x, z) := by
  set M := manyModel Q U Φ β
  have h := many_boundedDP hT hU hUb Q hQ hβ hβ1 hFc
  obtain ⟨v, hv, huniq, -, hG⟩ := ex_9_7b M h
  refine ⟨v, hv, huniq, hG, fun z => ?_, fun z => ?_⟩
  · rw [← hv]; exact many_bellman_mono hT hU h z
  · -- concavity: the contraction maps the closed set of concave functions into itself
    have hmaps : ∀ w : SX × Z →ᵇ ℝ, (∀ z, IsConcaveS hX fun x => w (x, z)) →
        ∀ z, IsConcaveS hX fun x => bellman M h w (x, z) := by
      intro w hw z x₀ x₁ θ h0 h1
      obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax M h w (x₀, z)
      obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax M h w (x₁, z)
      obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M h w (cmb hX h0 h1 x₀ x₁, z)
      obtain ⟨hyθ, hF⟩ := manyF_concave hT hU hUc hy₀ hy₁ h0 h1
      have hE := expV_comb M h (hX := hX) (hY := hX) (fun _ _ _ _ _ _ _ _ => rfl) hw hy₀ hy₁ h0
        h1 hyθ
      have hm := hmax _ hyθ
      have hβE := mul_le_mul_of_nonneg_left hE hβ.le
      simp only [rhs] at hv₀ hv₁ hm
      dsimp only
      rw [hv₀, hv₁]
      change _ ≤ M.β * _ at hβE
      change θ * (manyF U Φ (x₀, y₀, z) + M.β * _) + (1 - θ) * (manyF U Φ (x₁, y₁, z) + M.β * _)
        ≤ _
      linarith
    exact (corollary_1 (S' := {w : SX × Z →ᵇ ℝ | ∀ z, IsConcaveS hX fun x => w (x, z)})
      (S'' := {w : SX × Z →ᵇ ℝ | ∀ z, IsConcaveS hX fun x => w (x, z)})
      (bellman_contraction M h) hv ⟨0, fun _ _ _ _ _ _ => by simp⟩ (isClosed_concaveX hX)
      hmaps hmaps).1 z

/-! ### Exercise 10.3a: the strict conclusions fail -/

/-- `T` sees `x` only through `Γ(x, z)` and `F(x, ·, z)`: if `Φ(x, z) = Φ(x′, z)`, then
`(Tw)(x, z) = (Tw)(x′, z)`. -/
theorem many_bellman_eq {Q : Kernel Z Z} [IsMarkovKernel Q] {β : ℝ}
    (h : BoundedDP (manyModel Q U Φ β)) (w : SX × Z →ᵇ ℝ) {x x' : SX} {z : Z}
    (hΦ : Φ (x, z) = Φ (x', z)) :
    bellman (manyModel Q U Φ β) h w (x, z) = bellman (manyModel Q U Φ β) h w (x', z) := by
  simp only [bellman_apply, maxValue, objG, rhs, expV, manyΓ, manyF, hΦ]

/-- **Exercise 10.3a, corrected.** With a technology that does not depend on `(x, z)`, which
satisfies (a)–(c), `v(·, z)` is constant: it is not strictly increasing or strictly concave
(when `X` has two points), and if moreover `F` does not depend on `y`, every `y ∈ Γ(x, z)` is
optimal. So Assumptions 9.8 and 9.10 (strict) do not follow from (a)–(c), and neither do the
conclusions of Theorems 9.7 and 9.8. -/
theorem ex_10_3a_counterexample {K : Set (Cplus m × SX)}
    (hΦ : ∀ s, Φ s = K) {Q : Kernel Z Z} [IsMarkovKernel Q] {β : ℝ}
    (h : BoundedDP (manyModel Q U Φ β)) {v : SX × Z →ᵇ ℝ}
    (hv : bellman (manyModel Q U Φ β) h v = v) :
    (∀ x x' z, v (x, z) = v (x', z)) ∧
      ((∀ y y' : SX, {c | (c, y) ∈ K} = {c | (c, y') ∈ K}) →
        ∀ s, policy (manyModel Q U Φ β) v s = manyΓ Φ s) := by
  have hconst : ∀ x x' z, v (x, z) = v (x', z) := fun x x' z => by
    rw [← hv]
    exact many_bellman_eq h v (by rw [hΦ, hΦ])
  refine ⟨hconst, fun hK s => ?_⟩
  ext y
  refine ⟨fun hy => hy.1, fun hy => ⟨hy, ?_⟩⟩
  obtain ⟨y₀, hy₀, hval, -⟩ := exists_bellman_argmax _ h v s
  rw [hv] at hval
  rw [hval]
  simp only [rhs, expV]
  congr 1
  · simp only [manyF, hΦ, hK y₀ y]
  · congr 1
    exact integral_congr_ae (Eventually.of_forall fun z' => hconst _ _ _)

omit [MeasurableSpace Z] in
/-- The counterexample's technology `Φ(x, z) = [0, 1] × X` (one good, one capital good) satisfies
(a)–(c). -/
theorem techHyp_const {SX : Set (Fin 1 → ℝ)} (hX : Convex ℝ SX) (hcpt : IsCompact SX)
    [Nonempty SX] :
    TechHyp (Z := Z) hX fun _ => {p : Cplus 1 × SX | p.1.1 0 ≤ 1} := by
  have hne : ({p : Cplus 1 × SX | p.1.1 0 ≤ 1}).Nonempty :=
    ⟨(⟨0, fun _ => le_rfl⟩, Classical.arbitrary SX), by simp⟩
  have : CompactSpace SX := isCompact_iff_compactSpace.1 hcpt
  have hK : IsCompact {p : Cplus 1 × SX | p.1.1 0 ≤ 1} := by
    have hc : IsCompact {c : Cplus 1 | c.1 0 ≤ 1} := by
      have hb : IsCompact (Set.pi univ fun _ : Fin 1 => Icc (0 : ℝ) 1) :=
        isCompact_univ_pi fun _ => isCompact_Icc
      rw [Topology.IsInducing.subtypeVal.isCompact_iff]
      convert hb using 1
      ext c
      simp only [mem_image, mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, mem_Icc]
      constructor
      · rintro ⟨c', hc', rfl⟩ i
        fin_cases i
        exact ⟨c'.2 0, hc'⟩
      · intro hc
        exact ⟨⟨c, fun i => (hc i).1⟩, (hc 0).2, rfl⟩
    have hK2 := hc.prod (isCompact_univ : IsCompact (univ : Set SX))
    convert hK2 using 1
    ext p
    simp
  refine ⟨fun _ => hne, fun _ => hK, fun _ => ⟨hne, fun y hy _ _ => ⟨0, fun _ => y, fun _ _ => hy,
    tendsto_const_nhds⟩⟩, fun _ => ⟨hne, fun xs _ ys hys => ?_⟩, fun _ _ _ _ => subset_rfl,
    fun z x x' p p' θ h0 h1 hp hp' => ?_⟩
  · obtain ⟨y, hy, φ, hφ, hlim⟩ := hK.tendsto_subseq hys
    exact ⟨y, hy, φ, hφ, hlim⟩
  · change (cmb (convex_Cplus 1) h0 h1 p.1 p'.1).1 0 ≤ 1
    simp only [cmb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e1 : p.1.1 0 ≤ 1 := hp
    have e2 : p'.1.1 0 ≤ 1 := hp'
    nlinarith

/-! ### Exercise 10.3b -/

/-- A consumption plan `γ` with a capital plan `π` is **feasible** if both are measurable and
`(γ_t, π_t) ∈ Φ(x_t, z_t)`. -/
def ManyFeasible (Q : Kernel Z Z) (U : Cplus m → ℝ) (Φ : SX × Z → Set (Cplus m × SX)) (β : ℝ)
    (s₀ : SX × Z) (γ : (t : ℕ) → (Fin t → Z) → Cplus m) (π : Plan SX Z) : Prop :=
  (∀ t, Measurable (γ t)) ∧ (∀ t, Measurable (π t)) ∧
    ∀ t h, (γ t h, π t h) ∈ Φ (state (manyModel Q U Φ β) s₀ π t h)

/-- The utility of a consumption plan, `u(c) = Σ βᵗ ∫ U(c_t) dμᵗ` ((1), p. 291). -/
noncomputable def manyUtility (Q : Kernel Z Z) (U : Cplus m → ℝ) (β : ℝ) (z₀ : Z)
    (γ : (t : ℕ) → (Fin t → Z) → Cplus m) : ℝ :=
  ∑' t, β ^ t * ∫ h, U (γ t h) ∂hist Q t z₀

/-- A measurable choice `γ̂(x, y, z)` of a utility-maximizing consumption in the fibre exists
(Theorem 7.6), when `F` is continuous on `A`. -/
theorem exists_gammaStar [BorelSpace Z] (hT : TechHyp hX Φ)
    (hU : Continuous U) {Q : Kernel Z Z} {β : ℝ}
    (hFc : ContinuousOn (manyF U Φ) (graphA (manyModel Q U Φ β))) :
    ∃ γh : graphA (manyModel Q U Φ β) → Cplus m, Measurable γh ∧
      ∀ p, (γh p, p.1.2.1) ∈ Φ (p.1.1, p.1.2.2) ∧ U (γh p) = manyF U Φ p.1 := by
  set A := graphA (manyModel Q U Φ β)
  set G : A → Set (Cplus m) := fun p => {c | (c, p.1.2.1) ∈ Φ (p.1.1, p.1.2.2) ∧
    U c = manyF U Φ p.1}
  have hGne : ∀ p : A, (G p).Nonempty := fun p => by
    obtain ⟨c, hc, he, -⟩ := manyF_spec hT hU (x := p.1.1) (z := p.1.2.2) p.2
    exact ⟨c, hc, he.symm⟩
  have hGc : ∀ p : A, IsCompact (G p) := fun p =>
    (isCompact_fiber hT _ _).of_isClosed_subset
      ((isCompact_fiber hT _ _).isClosed.inter (isClosed_eq hU continuous_const))
      fun _ hc => hc.1
  have hGu : ∀ p, IsUHC G p := fun p => by
    refine ⟨hGne p, fun ps hps cs hcs => ?_⟩
    have h1 : Tendsto (fun n => ((ps n).1.1, (ps n).1.2.2)) atTop (𝓝 (p.1.1, p.1.2.2)) :=
      ((continuous_fst.prodMk continuous_snd.snd).comp continuous_subtype_val).tendsto p |>.comp
        hps
    obtain ⟨q, hq, φ, hφ, hlim⟩ := (hT.uhc (p.1.1, p.1.2.2)).2 _ h1
      (fun n => (cs n, (ps n).1.2.1)) fun n => (hcs n).1
    have hy : q.2 = p.1.2.1 := tendsto_nhds_unique ((continuous_snd.tendsto q).comp hlim)
      (((continuous_snd.fst.comp continuous_subtype_val).tendsto p).comp
        (hps.comp hφ.tendsto_atTop))
    have hcl : Tendsto (cs ∘ φ) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hlim
    refine ⟨q.1, ⟨by rw [← hy]; exact hq, ?_⟩, φ, hφ, hcl⟩
    have hFl : Tendsto (fun n => manyF U Φ (ps (φ n)).1) atTop (𝓝 (manyF U Φ p.1)) :=
      (hFc.comp_continuous continuous_subtype_val fun p => p.2).continuousAt.tendsto.comp
        (hps.comp hφ.tendsto_atTop)
    exact tendsto_nhds_unique ((hU.tendsto q.1).comp hcl)
      (hFl.congr fun n => ((hcs (φ n)).2).symm)
  obtain ⟨g, hg, hmem⟩ := theorem_7_6_subtype (T := Cplus m)
    (Γ := fun p => Subtype.val '' G p) (fun p => isUHC_image_val (hGu p))
    (fun p => (hGc p).image continuous_subtype_val) (fun p => by rintro _ ⟨c, -, rfl⟩; exact c.2)
  refine ⟨g, hg, fun p => ?_⟩
  obtain ⟨c, hc, hcv⟩ := hmem p
  have : c = g p := Subtype.ext hcv
  rw [← this]
  exact hc

/-- **Exercise 10.3b.** Let `g` be a measurable selection from `G` (Theorem 7.6) and `π*` the plan
it generates from `s₀`. No feasible consumption–capital plan has utility above `v(s₀)`, and there
is a consumption plan `γ*`, with `U(γ*_t) = F(x_t, π*_t, z_t)`, such that `(γ*, π*)` is feasible
and attains `v(s₀)`. -/
theorem ex_10_3b [OpensMeasurableSpace Z] [BorelSpace Z] (hT : TechHyp hX Φ) (hU : Continuous U)
    (hUb : ∃ B, ∀ c, |U c| ≤ B) (Q : Kernel Z Z) [IsMarkovKernel Q] (hQ : PreservesBC SX Q)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hFc : ContinuousOn (manyF U Φ) (graphA (manyModel Q U Φ β))) {v : SX × Z →ᵇ ℝ}
    (hv : bellman (manyModel Q U Φ β) (many_boundedDP hT hU hUb Q hQ hβ hβ1 hFc) v = v)
    {g : SX × Z → SX} (hg : Measurable g) (hgG : ∀ s, g s ∈ policy (manyModel Q U Φ β) v s)
    (s₀ : SX × Z) :
    (∀ γ π, ManyFeasible Q U Φ β s₀ γ π → manyUtility Q U β s₀.2 γ ≤ v s₀) ∧
      ∃ γ, ManyFeasible Q U Φ β s₀ γ (genPlan (manyModel Q U Φ β) s₀ fun _ => g) ∧
        manyUtility Q U β s₀.2 γ = v s₀ := by
  set M := manyModel Q U Φ β
  have h := many_boundedDP hT hU hUb Q hQ hβ hβ1 hFc
  obtain ⟨B, hB⟩ := hUb
  have hφm : Measurable M.φ := measurable_snd.fst
  have hFm : Measurable M.F := measurable_manyF hT Q hFc
  have hopt := bounded_vStar M h hφm hFm hv (g := fun _ => g) (fun _ => hg) (fun _ => hgG) s₀
  have hsum : Summable fun t => M.β ^ t * B :=
    (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
  have hFB : ∀ π, IsFeasible M s₀ π → ∀ t h', |ret M s₀ π t h'| ≤ B := fun π hπ t h' => by
    obtain ⟨c, -, he, -⟩ := manyF_spec hT hU (x := (state M s₀ π t h').1)
      (z := (state M s₀ π t h').2) (hπ.2 t h')
    change |manyF U Φ _| ≤ B
    rw [he]; exact hB c
  -- the value of a feasible capital plan, as a real number
  have hval : ∀ π, IsFeasible M s₀ π → planValue M s₀ π = (uR M s₀ π : EReal) := fun π hπ =>
    planValue_eq_uR M hβ.le s₀ π (K := fun _ => B) (hFB π hπ) hsum
  have hUγ : ∀ (γ : (t : ℕ) → (Fin t → Z) → Cplus m), (∀ t, Measurable (γ t)) →
      Summable fun t => β ^ t * ∫ h', U (γ t h') ∂hist Q t s₀.2 := fun γ hγ => by
    refine Summable.of_norm_bounded hsum fun t => ?_
    have := ex_8_8a Q t
    rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hβ]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ.le t)
    have := norm_integral_le_of_norm_le_const (μ := hist Q t s₀.2) (C := B)
      (f := fun h' => U (γ t h')) (Eventually.of_forall fun h' => by
        rw [Real.norm_eq_abs]; exact hB _)
    simpa [measureReal_def] using this
  have hret : ∀ π, IsFeasible M s₀ π →
      Summable fun t => M.β ^ t * ∫ h', ret M s₀ π t h' ∂hist M.Q t s₀.2 := fun π hπ =>
    summable_terms M hβ.le s₀ π (K := fun _ => B) (hFB π hπ) hsum
  have hint : ∀ (f : (t : ℕ) → (Fin t → Z) → ℝ), (∀ t, Measurable (f t)) →
      (∀ t h', |f t h'| ≤ B) → ∀ t, Integrable (f t) (hist Q t s₀.2) := fun f hf hfB t => by
    have := ex_8_8a Q t
    exact integrable_of_abs_le (hf t) (hfB t)
  refine ⟨fun γ π hγπ => ?_, ?_⟩
  · -- `U(γ_t) ≤ F(x_t, π_t, z_t)`, so `u(γ) ≤ u(π) ≤ v(s₀)`
    have hπ : IsFeasible M s₀ π := ⟨hγπ.2.1, fun t h' => ⟨_, hγπ.2.2 t h', rfl⟩⟩
    have hle : manyUtility Q U β s₀.2 γ ≤ uR M s₀ π := by
      refine Summable.tsum_le_tsum (fun t => ?_) (hUγ γ hγπ.1) (hret π hπ)
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ.le t)
      refine integral_mono (hint _ (fun t => hU.measurable.comp (hγπ.1 t)) (fun _ _ => hB _) t)
        (hint _ (fun t => measurable_ret M hφm hFm s₀ hπ.1 t) (hFB π hπ) t)
        fun h' => le_manyF hT hU (hγπ.2.2 t h')
    have := hopt.1 π hπ
    rw [hval π hπ] at this
    exact hle.trans (EReal.coe_le_coe_iff.1 this)
  · -- `γ*_t = γ̂(x_t, π*_t, z_t)`
    set π := genPlan M s₀ fun _ => g
    have hπ : IsFeasible M s₀ π := genPlan_feasible M hφm s₀ (fun _ => hg) fun _ s => (hgG s).1
    obtain ⟨γh, hγm, hγ⟩ := exists_gammaStar hT hU hFc (Q := Q) (β := β)
    set γ : (t : ℕ) → (Fin t → Z) → Cplus m := fun t h' =>
      γh ⟨((state M s₀ π t h').1, π t h', (state M s₀ π t h').2), hπ.2 t h'⟩
    have hγmeas : ∀ t, Measurable (γ t) := fun t =>
      hγm.comp (((measurable_state M hφm s₀ hπ.1 t).fst.prodMk ((hπ.1 t).prodMk
        (measurable_state M hφm s₀ hπ.1 t).snd)).subtype_mk)
    refine ⟨γ, ⟨hγmeas, hπ.1, fun t h' =>
      (hγ ⟨((state M s₀ π t h').1, π t h', (state M s₀ π t h').2), hπ.2 t h'⟩).1⟩, ?_⟩
    have heq : manyUtility Q U β s₀.2 γ = uR M s₀ π := by
      simp only [manyUtility, uR]
      congr 1
      funext t
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun h' => (hγ _).2)
    rw [heq]
    have := hopt.2.1
    rw [hval π hπ] at this
    exact EReal.coe_eq_coe_iff.1 this

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Asset prices: the pricing equation

SLP §10.6, Exercise 10.6e, pp. 303–304. On a compact state space `Z` with a Feller transition `Q`,
the Markov operator `M` maps `C(Z)` into itself (`fellerOp`), linearly and monotonically. For
`h ∈ C(Z)` and `0 < β < 1` the equation `φ = h + βMφ` (6) has a unique solution in `C(Z)`; it
is `φ = Σₙ βⁿ Mⁿ h`, and it is positive when `h` is (`ex_10_6e_general`).

For the exchange economy (`ex_10_6e`), `Z ⊆ ℝᵏ₊₊`, `U′` is continuous and positive, and
`hᵢ(z) = β ∫ U′(z′·1) z′ᵢ Q(z, dz′)`. Each `φᵢ` is positive, and `p*ᵢ = φᵢ/U′(z·1)` solves the
equilibrium condition `U′(z·1) p*ᵢ(z) = β ∫ U′(z′·1)[z′ᵢ + p*ᵢ(z′)] Q(z, dz′)` (5).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
  (Q : Kernel Z Z) [IsMarkovKernel Q]

omit [OpensMeasurableSpace Z] in
theorem abs_markovOpR_le (f : Z →ᵇ ℝ) (z : Z) : |markovOpR Q f z| ≤ ‖f‖ := by
  have := norm_integral_le_of_norm_le_const (μ := Q z) (C := ‖f‖) (f := fun z' => f z')
    (Eventually.of_forall fun z' => f.norm_coe_le_norm z')
  simpa [markovOpR, measureReal_def, Real.norm_eq_abs] using this

theorem integrable_bcf (f : Z →ᵇ ℝ) (z : Z) : Integrable (fun z' => f z') (Q z) :=
  integrable_of_abs_le f.continuous.measurable fun z' => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z'

/-- The Markov operator on `C(Z)`, for `Q` Feller: `(Mf)(z) = ∫ f(z′) Q(z, dz′)`. -/
noncomputable def fellerOp (hQ : IsFeller Q) (f : Z →ᵇ ℝ) : Z →ᵇ ℝ :=
  ofNormedAddCommGroup (markovOpR Q f) (hQ f f.continuous ⟨‖f‖, fun z => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z⟩) ‖f‖ fun z => by
    rw [Real.norm_eq_abs]; exact abs_markovOpR_le Q f z

variable {Q} (hQ : IsFeller Q)

omit [OpensMeasurableSpace Z] in
theorem fellerOp_apply (f : Z →ᵇ ℝ) (z : Z) : fellerOp Q hQ f z = ∫ z', f z' ∂Q z := rfl

theorem fellerOp_add (f g : Z →ᵇ ℝ) :
    fellerOp Q hQ (f + g) = fellerOp Q hQ f + fellerOp Q hQ g := by
  ext z
  simp only [fellerOp_apply, coe_add, Pi.add_apply]
  exact integral_add (integrable_bcf Q f z) (integrable_bcf Q g z)

omit [OpensMeasurableSpace Z] in
theorem fellerOp_smul (c : ℝ) (f : Z →ᵇ ℝ) : fellerOp Q hQ (c • f) = c • fellerOp Q hQ f := by
  ext z
  simp only [fellerOp_apply, coe_smul, smul_eq_mul]
  exact integral_const_mul c _

omit [OpensMeasurableSpace Z] in
theorem fellerOp_const (a : ℝ) : fellerOp Q hQ (const Z a) = const Z a := by
  ext z
  simp [fellerOp_apply]

theorem fellerOp_mono {f g : Z →ᵇ ℝ} (hfg : f ≤ g) : fellerOp Q hQ f ≤ fellerOp Q hQ g :=
  fun z => integral_mono (integrable_bcf Q f z) (integrable_bcf Q g z) fun z' => hfg z'

omit [OpensMeasurableSpace Z] in
theorem norm_fellerOp_le (f : Z →ᵇ ℝ) : ‖fellerOp Q hQ f‖ ≤ ‖f‖ :=
  (norm_le (norm_nonneg f)).2 fun z => by
    rw [Real.norm_eq_abs]; exact abs_markovOpR_le Q f z

omit [OpensMeasurableSpace Z] in
theorem norm_fellerOp_iterate_le (n : ℕ) (f : Z →ᵇ ℝ) : ‖(fellerOp Q hQ)^[n] f‖ ≤ ‖f‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (norm_fellerOp_le hQ _).trans ih

/-- The operator of (6): `Tφ = h + βMφ`. -/
noncomputable def priceT (β : ℝ) (h φ : Z →ᵇ ℝ) : Z →ᵇ ℝ := h + β • fellerOp Q hQ φ

theorem priceT_contraction {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (h : Z →ᵇ ℝ) :
    IsContraction (priceT hQ β h) β := by
  refine ⟨hβ0, hβ1, blackwell hβ0.le (fun f g hfg z => ?_) (fun f a _ z => ?_)⟩
  · change h z + β * fellerOp Q hQ f z ≤ h z + β * fellerOp Q hQ g z
    have h1 : fellerOp Q hQ f z ≤ fellerOp Q hQ g z := fellerOp_mono hQ hfg z
    nlinarith [mul_le_mul_of_nonneg_left h1 hβ0.le]
  · change h z + β * fellerOp Q hQ (f + const Z a) z ≤ h z + β * fellerOp Q hQ f z + β * a
    rw [fellerOp_add, fellerOp_const]
    change h z + β * (fellerOp Q hQ f z + a) ≤ _
    linarith

/-- The partial sums `Σ_{m<n} βᵐMᵐh` are the iterates `Tⁿ0`. -/
theorem priceT_iterate_zero (β : ℝ) (h : Z →ᵇ ℝ) (n : ℕ) :
    (priceT hQ β h)^[n] 0 = ∑ m ∈ Finset.range n, β ^ m • (fellerOp Q hQ)^[m] h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, priceT, Finset.sum_range_succ']
    have hlin : ∀ s : Finset ℕ, fellerOp Q hQ (∑ m ∈ s, β ^ m • (fellerOp Q hQ)^[m] h) =
        ∑ m ∈ s, β ^ m • (fellerOp Q hQ)^[m + 1] h := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have := fellerOp_smul hQ 0 0
        simpa using this
      | insert a s ha ih' =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, fellerOp_add, fellerOp_smul, ih',
          Function.iterate_succ_apply']
    rw [hlin, Finset.smul_sum]
    simp only [smul_smul, pow_zero, one_smul, Function.iterate_zero, id, ← pow_succ']
    abel

/-- **Exercise 10.6e** (general form). For `h ∈ C(Z)` and `0 < β < 1`, `φ = h + βMφ` has a unique
solution `φ ∈ C(Z)`; `φ = Σₙ βⁿMⁿh`; and `φ > 0` if `h > 0`. -/
theorem ex_10_6e_general {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (h : Z →ᵇ ℝ) :
    ∃ φ : Z →ᵇ ℝ, φ = h + β • fellerOp Q hQ φ ∧
      (∀ ψ : Z →ᵇ ℝ, ψ = h + β • fellerOp Q hQ ψ → ψ = φ) ∧
      HasSum (fun n => β ^ n • (fellerOp Q hQ)^[n] h) φ ∧
      ((∀ z, 0 < h z) → ∀ z, 0 < φ z) := by
  have hT := priceT_contraction hQ hβ0 hβ1 h
  obtain ⟨φ, hφ, huniq, hrate⟩ := theorem_3_2 hT
  refine ⟨φ, hφ.symm, fun ψ hψ => huniq ψ hψ.symm, ?_, fun hpos z => ?_⟩
  · -- the series converges absolutely, and its partial sums are `Tⁿ0 → φ`
    have hsum : Summable fun n => β ^ n • (fellerOp Q hQ)^[n] h := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right ‖h‖)
        fun n => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hβ0 n)]
      exact mul_le_mul_of_nonneg_left (norm_fellerOp_iterate_le hQ n h) (pow_nonneg hβ0.le n)
    have hlim : Tendsto (fun n => (priceT hQ β h)^[n] 0) atTop (𝓝 φ) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun _ => dist_nonneg) (fun n => hrate 0 n) ?_
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (dist 0 φ)
    simp only [priceT_iterate_zero] at hlim
    have := hsum.hasSum.tendsto_sum_nat
    rw [tendsto_nhds_unique hlim this]
    exact hsum.hasSum
  · -- `φ ≥ 0` (the closed set of nonnegative functions is invariant), so `φ ≥ h > 0`
    have hclosed : IsClosed {f : Z →ᵇ ℝ | ∀ z, 0 ≤ f z} := by
      have : {f : Z →ᵇ ℝ | ∀ z, 0 ≤ f z} = ⋂ z, {f | 0 ≤ f z} := by ext; simp
      rw [this]
      exact isClosed_iInter fun z => isClosed_le continuous_const (continuous_eval_const z)
    have hmaps : MapsTo (priceT hQ β h) {f | ∀ z, 0 ≤ f z} {f | ∀ z, 0 ≤ f z} := by
      intro f hf z
      have := fellerOp_mono hQ (show 0 ≤ f from hf) z
      have h0 : fellerOp Q hQ 0 = 0 := by simpa using fellerOp_smul hQ 0 0
      rw [h0] at this
      simp only [priceT, coe_add, coe_smul, Pi.add_apply, smul_eq_mul]
      have := hpos z
      change 0 ≤ fellerOp Q hQ f z at *
      positivity
    have hφ0 := (corollary_1 (S' := {f : Z →ᵇ ℝ | ∀ z, 0 ≤ f z})
      (S'' := {f : Z →ᵇ ℝ | ∀ z, 0 ≤ f z}) hT hφ ⟨0, fun _ => le_rfl⟩ hclosed hmaps hmaps).1
    have hM := fellerOp_mono hQ (show 0 ≤ φ from hφ0) z
    have h0 : fellerOp Q hQ 0 = 0 := by simpa using fellerOp_smul hQ 0 0
    rw [h0] at hM
    rw [← hφ]
    simp only [priceT, coe_add, coe_smul, Pi.add_apply, smul_eq_mul]
    have := hpos z
    change 0 ≤ fellerOp Q hQ φ z at hM
    positivity

/-- **Exercise 10.6e.** Let `Z` be compact with a Feller transition `Q`, let `dᵢ(z) > 0` be the
dividends (continuous), `U′ > 0` continuous, and `hᵢ(z) = β ∫ U′(z′·1) z′ᵢ Q(z, dz′)`. Then for
each asset `i` the equation `φᵢ = hᵢ + βMφᵢ` (6) has a unique solution in `C(Z)`, it is
positive, it equals `Σₙ βⁿMⁿhᵢ`, and `p*ᵢ(z) = φᵢ(z)/U′(z·1)` solves (5):
`U′(z·1) p*ᵢ(z) = β ∫ U′(z′·1)[z′ᵢ + p*ᵢ(z′)] Q(z, dz′)`. -/
theorem ex_10_6e [CompactSpace Z] {k : ℕ} {d : Fin k → Z → ℝ} (hd : ∀ i, Continuous (d i))
    (hdpos : ∀ i z, 0 < d i z) {Up : ℝ → ℝ} (hUc : Continuous Up) (hUpos : ∀ c, 0 < Up c)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (i : Fin k) :
    ∃ h φ : Z →ᵇ ℝ, (∀ z, h z = β * ∫ z', Up (∑ j, d j z') * d i z' ∂Q z) ∧
      φ = h + β • fellerOp Q hQ φ ∧
      (∀ ψ : Z →ᵇ ℝ, ψ = h + β • fellerOp Q hQ ψ → ψ = φ) ∧
      HasSum (fun n => β ^ n • (fellerOp Q hQ)^[n] h) φ ∧ (∀ z, 0 < φ z) ∧
      ∀ z, Up (∑ j, d j z) * (φ z / Up (∑ j, d j z)) =
        β * ∫ z', Up (∑ j, d j z') * (d i z' + φ z' / Up (∑ j, d j z')) ∂Q z := by
  have hgc : Continuous fun z => Up (∑ j, d j z) * d i z :=
    (hUc.comp (continuous_finsetSum _ fun j _ => hd j)).mul (hd i)
  set g : Z →ᵇ ℝ := mkOfCompact ⟨_, hgc⟩
  set h : Z →ᵇ ℝ := β • fellerOp Q hQ g
  have hh : ∀ z, h z = β * ∫ z', Up (∑ j, d j z') * d i z' ∂Q z := fun _ => rfl
  have hpos : ∀ z, 0 < h z := fun z => by
    rw [hh]
    refine mul_pos hβ0 ?_
    have := integral_lt_integral_of_lt (μ := Q z) (integrable_const (0 : ℝ))
      (integrable_bcf Q g z) fun z' => mul_pos (hUpos _) (hdpos i z')
    rw [integral_const, smul_zero] at this
    exact this
  obtain ⟨φ, hφ, huniq, hsum, hφpos⟩ := ex_10_6e_general hQ hβ0 hβ1 h
  refine ⟨h, φ, hh, hφ, huniq, hsum, hφpos hpos, fun z => ?_⟩
  rw [mul_div_cancel₀ _ (hUpos _).ne']
  have e : ∀ z', Up (∑ j, d j z') * (d i z' + φ z' / Up (∑ j, d j z')) = g z' + φ z' :=
    fun z' => by
      change _ = Up (∑ j, d j z') * d i z' + φ z'
      field_simp [(hUpos (∑ j, d j z')).ne']
  simp_rw [e]
  rw [integral_add (integrable_bcf Q g z) (integrable_bcf Q φ z), mul_add]
  conv_lhs => rw [hφ]
  rfl

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Asset prices: the consumer's problem

SLP §10.6, Exercise 10.6a–d, pp. 300–303. A consumer holds `x ∈ X = [0, x̄]ᵏ` shares (`x̄ > 1`);
in state `z` asset `i` pays the dividend `dᵢ(z) > 0` and sells at `pᵢ(z) > 0` (`p` continuous);
consumption is `c = d(z)·x + p(z)·(x − y)` for end-of-period holdings `y`. In the first
formulation of Chapter 9, `Γ(x, z) = {y ∈ X : p(z)·y ≤ [d(z) + p(z)]·x}` and `F(x, y, z) = U(c)`.

* **Exercise 10.6a–b** (`asset_boundedDP`, `ex_10_6ab`): the hypotheses of §9.2 hold, so the
  functional equation has a unique bounded continuous solution `vᵖ`, which is the supremum
  function `v*`. `vᵖ(·, z)` is strictly increasing and concave; `Gᵖ` is nonempty,
  compact-valued, u.h.c. and convex-valued; and any two optimal portfolios cost the same
  (`p(z)·y = p(z)·y′`, by strict concavity of `U`). `vᵖ` is only weakly concave because `c` is
  linear in `(x, y)`; portfolios of equal cost and equal continuation value tie.
* **Exercise 10.6c** (`ex_10_6c_deriv`, `ex_10_6c_euler`): at an interior `x` with an optimal
  `y` leaving positive consumption, `vᵖᵢ(x, z) = U′(c)[dᵢ(z) + pᵢ(z)]` (1). If moreover `y` is
  interior and each `vᵖ(·, z′)` has partial derivative `vᵖᵢ(y, z′)`, then
  `U′(c) pᵢ(z) = β ∫ vᵖᵢ(y, z′) Q(z, dz′)` (2). The integral is differentiated under the integral
  sign, using that a concave bounded function is Lipschitz inside its domain.
* **Exercise 10.6d** (`ex_10_6d`): if holding one share of each asset is optimal in every state
  (equilibrium), then (3) `vᵢ(1, z) = U′(z·1)[zᵢ + pᵢ(z)]` and (4)–(5)
  `U′(z·1)pᵢ(z) = β ∫ U′(z′·1)[z′ᵢ + pᵢ(z′)] Q(z, dz′)`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction Metric

/-- The portfolios `X = [0, x̄]ᵏ`. -/
def assetX (k : ℕ) (xbar : ℝ) : Set (Fin k → ℝ) := Set.pi univ fun _ => Icc 0 xbar

/-- The inner product `a·b`. -/
def dotR {k : ℕ} (a b : Fin k → ℝ) : ℝ := ∑ i, a i * b i

/-- `x ↦ a·x` as a continuous linear functional. -/
noncomputable def dotCLM {k : ℕ} (a : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • ContinuousLinearMap.proj i

variable {k : ℕ} {xbar : ℝ}

theorem dotCLM_apply (a x : Fin k → ℝ) : dotCLM a x = dotR a x := by
  simp [dotCLM, dotR]

theorem continuous_dotR : Continuous fun q : (Fin k → ℝ) × (Fin k → ℝ) => dotR q.1 q.2 :=
  continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)

theorem dotR_cmb (a x x' : Fin k → ℝ) (θ : ℝ) :
    dotR a (θ • x + (1 - θ) • x') = θ * dotR a x + (1 - θ) * dotR a x' := by
  simp only [dotR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dotR_nonneg {a x : Fin k → ℝ} (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ dotR a x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hx i)

theorem dotR_le {a x x' : Fin k → ℝ} (ha : ∀ i, 0 ≤ a i) (h : x ≤ x') : dotR a x ≤ dotR a x' :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (ha i)

theorem dotR_lt {a x x' : Fin k → ℝ} (ha : ∀ i, 0 < a i) (h : x < x') : dotR a x < dotR a x' := by
  obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.1 h
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  exact Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (ha j).le)
    ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left (lt_of_le_of_ne (hle i) hi) (ha i)⟩

theorem mem_assetX {x : Fin k → ℝ} : x ∈ assetX k xbar ↔ ∀ i, 0 ≤ x i ∧ x i ≤ xbar := by
  simp only [assetX, Set.mem_univ_pi, mem_Icc]

theorem convex_assetX : Convex ℝ (assetX k xbar) := convex_pi fun _ _ => convex_Icc 0 xbar

theorem isCompact_assetX : IsCompact (assetX k xbar) := isCompact_univ_pi fun _ => isCompact_Icc

/-- The budget correspondence `s ↦ {y ∈ X : q(s)·y ≤ b(s)}`, for continuous `q > 0` and
`b ≥ 0`, is l.h.c.: scale `y` by `min{1, b(sₙ)/q(sₙ)·y}`. -/
theorem isLHC_budget {S : Type*} [MetricSpace S] {q : S → Fin k → ℝ} {b : S → ℝ}
    (hq : Continuous q) (hqpos : ∀ s i, 0 < q s i) (hb : Continuous b) (hb0 : ∀ s, 0 ≤ b s)
    (hx : 0 ≤ xbar) (s : S) :
    IsLHC (fun s => {y : assetX k xbar | dotR (q s) y.1 ≤ b s}) s := by
  have h0 : (0 : Fin k → ℝ) ∈ assetX k xbar := mem_assetX.2 fun _ => ⟨le_rfl, hx⟩
  have hd0 : ∀ s, dotR (q s) (0 : Fin k → ℝ) = 0 := fun _ => by simp [dotR]
  refine ⟨⟨⟨0, h0⟩, by simp only [mem_ofPred_eq, hd0]; exact hb0 s⟩, fun y hy xs hxs => ?_⟩
  have hy' : dotR (q s) y.1 ≤ b s := hy
  have hynn : ∀ i, 0 ≤ y.1 i := fun i => (mem_assetX.1 y.2 i).1
  set σ : ℕ → ℝ := fun n => dotR (q (xs n)) y.1
  have hσ0 : ∀ n, 0 ≤ σ n := fun n => dotR_nonneg (fun i => (hqpos _ i).le) hynn
  rcases (dotR_nonneg (fun i => (hqpos s i).le) hynn).lt_or_eq with hpos | hzero
  · set t : ℕ → ℝ := fun n => min 1 (b (xs n) / σ n)
    have ht0 : ∀ n, 0 ≤ t n := fun n => le_min zero_le_one (div_nonneg (hb0 _) (hσ0 n))
    have ht1 : ∀ n, t n ≤ 1 := fun n => min_le_left _ _
    have hmem : ∀ n, t n • y.1 ∈ assetX k xbar := fun n => mem_assetX.2 fun i => by
      have := mem_assetX.1 y.2 i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact ⟨mul_nonneg (ht0 n) this.1, by nlinarith [ht0 n, ht1 n]⟩
    refine ⟨0, fun n => ⟨t n • y.1, hmem n⟩, fun n _ => ?_, ?_⟩
    · change dotR (q (xs n)) (t n • y.1) ≤ b (xs n)
      have e : dotR (q (xs n)) (t n • y.1) = t n * σ n := by
        simp only [dotR, Pi.smul_apply, smul_eq_mul, σ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      rcases (hσ0 n).lt_or_eq with hσ | hσ
      · have := mul_le_mul_of_nonneg_right (min_le_right 1 (b (xs n) / σ n)) hσ.le
        rwa [div_mul_cancel₀ _ hσ.ne'] at this
      · rw [← hσ, mul_zero]; exact hb0 _
    · have hσl : Tendsto σ atTop (𝓝 (dotR (q s) y.1)) :=
        (continuous_dotR.comp (hq.prodMk continuous_const)).tendsto s |>.comp hxs
      have htl : Tendsto t atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).min
          (((hb.tendsto s).comp hxs).div hσl hpos.ne')
        rwa [min_eq_left ((one_le_div hpos).2 hy')] at this
      refine tendsto_subtype_rng.2 ?_
      simpa using htl.smul_const y.1
  · -- `q(s)·y = 0` forces `y = 0`
    have hy0 : y.1 = 0 := by
      funext i
      have hs := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hqpos s j).le (hynn j))
        |>.1 hzero.symm i (Finset.mem_univ _)
      exact (mul_eq_zero.1 hs).resolve_left (hqpos s i).ne'
    refine ⟨0, fun _ => y, fun n _ => ?_, tendsto_const_nhds⟩
    change dotR (q (xs n)) y.1 ≤ b (xs n)
    rw [hy0, hd0]
    exact hb0 _

/-- The budget correspondence is u.h.c. -/
theorem isUHC_budget {S : Type*} [MetricSpace S] {q : S → Fin k → ℝ} {b : S → ℝ}
    (hq : Continuous q) (hb : Continuous b) (hb0 : ∀ s, 0 ≤ b s) (hx : 0 ≤ xbar) (s : S) :
    IsUHC (fun s => {y : assetX k xbar | dotR (q s) y.1 ≤ b s}) s := by
  have : CompactSpace (assetX k xbar) := isCompact_iff_compactSpace.1 isCompact_assetX
  have h0 : (0 : Fin k → ℝ) ∈ assetX k xbar := mem_assetX.2 fun _ => ⟨le_rfl, hx⟩
  refine ⟨⟨⟨0, h0⟩, by simp [dotR, hb0 s]⟩, fun xs hxs ys hys => ?_⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
  refine ⟨y, ?_, φ, hφ, hlim⟩
  have hc : Continuous fun p : S × assetX k xbar => dotR (q p.1) p.2.1 :=
    continuous_dotR.comp ((hq.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  exact le_of_tendsto_of_tendsto ((hc.tendsto (s, y)).comp
    ((hxs.comp hφ.tendsto_atTop).prodMk_nhds hlim))
    ((hb.tendsto s).comp (hxs.comp hφ.tendsto_atTop)) (Eventually.of_forall fun n => hys (φ n))

variable {Z : Type*} [MetricSpace Z]

/-- The hypotheses of SLP §10.6: `U` continuous, strictly increasing and strictly concave on
`[0, ∞)`; `0 < β < 1`; `x̄ > 1`; dividends and prices continuous and positive. -/
structure AssetHyp (U : ℝ → ℝ) (d p : Z → Fin k → ℝ) (β xbar : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  xbar_gt : 1 < xbar
  U_cont : ContinuousOn U (Ici 0)
  U_mono : StrictMonoOn U (Ici 0)
  U_conc : StrictConcaveOn ℝ (Ici 0) U
  d_cont : Continuous d
  d_pos : ∀ z i, 0 < d z i
  p_cont : Continuous p
  p_pos : ∀ z i, 0 < p z i

variable [MeasurableSpace Z] {U : ℝ → ℝ} {d p : Z → Fin k → ℝ} {β : ℝ}

/-- `Γ(x, z) = {y ∈ X : p(z)·y ≤ [d(z) + p(z)]·x}`. -/
def assetΓ (d p : Z → Fin k → ℝ) (xbar : ℝ) (s : assetX k xbar × Z) : Set (assetX k xbar) :=
  {y | dotR (p s.2) y.1 ≤ dotR (d s.2 + p s.2) s.1.1}

/-- Consumption `c = [d(z) + p(z)]·x − p(z)·y`. -/
def assetC (d p : Z → Fin k → ℝ) (x y : Fin k → ℝ) (z : Z) : ℝ :=
  dotR (d z + p z) x - dotR (p z) y

/-- `F(x, y, z) = U(c)`, with consumption clamped at `0` off the graph. -/
def assetF (U : ℝ → ℝ) (d p : Z → Fin k → ℝ) (xbar : ℝ)
    (q : assetX k xbar × assetX k xbar × Z) : ℝ :=
  U (max (assetC d p q.1.1 q.2.1.1 q.2.2) 0)

/-- The consumer's problem in the first formulation of Chapter 9. -/
abbrev assetModel (Q : Kernel Z Z) (U : ℝ → ℝ) (d p : Z → Fin k → ℝ) (β xbar : ℝ) :
    Model (assetX k xbar) (assetX k xbar) Z :=
  Model.first Q (assetΓ d p xbar) (assetF U d p xbar) β

omit [MetricSpace Z] [MeasurableSpace Z] in
theorem assetF_of_mem {x y : assetX k xbar} {z : Z} (hy : y ∈ assetΓ d p xbar (x, z)) :
    assetF U d p xbar (x, y, z) = U (assetC d p x.1 y.1 z) := by
  have : 0 ≤ assetC d p x.1 y.1 z := sub_nonneg.2 hy
  simp only [assetF, max_eq_left this]

omit [MeasurableSpace Z] in
theorem AssetHyp.continuous_F (h : AssetHyp U d p β xbar) :
    Continuous (assetF U d p xbar) := by
  have hc : Continuous fun q : assetX k xbar × assetX k xbar × Z =>
      assetC d p q.1.1 q.2.1.1 q.2.2 :=
    (continuous_dotR.comp (((h.d_cont.add h.p_cont).comp continuous_snd.snd).prodMk
      (continuous_subtype_val.comp continuous_fst))).sub
    (continuous_dotR.comp ((h.p_cont.comp continuous_snd.snd).prodMk
      (continuous_subtype_val.comp continuous_snd.fst)))
  exact h.U_cont.comp_continuous (hc.max continuous_const) fun _ => mem_Ici.2 (le_max_right _ _)

/-- The hypotheses of §9.2 hold for the consumer's problem, for any Feller `Q` on a compact `Z`
(Exercise 10.6b). -/
theorem asset_boundedDP [CompactSpace Z] [OpensMeasurableSpace Z] (h : AssetHyp U d p β xbar)
    (Q : Kernel Z Z)
    [IsMarkovKernel Q] (hQ : IsFeller Q) : BoundedDP (assetModel Q U d p β xbar) := by
  have : CompactSpace (assetX k xbar) := isCompact_iff_compactSpace.1 isCompact_assetX
  have hb : Continuous fun s : assetX k xbar × Z => dotR (d s.2 + p s.2) s.1.1 :=
    continuous_dotR.comp (((h.d_cont.add h.p_cont).comp continuous_snd).prodMk
      (continuous_subtype_val.comp continuous_fst))
  have hb0 : ∀ s : assetX k xbar × Z, 0 ≤ dotR (d s.2 + p s.2) s.1.1 := fun s =>
    dotR_nonneg (fun i => (add_pos (h.d_pos _ i) (h.p_pos _ i)).le)
      fun i => (mem_assetX.1 s.1.2 i).1
  have hx : 0 ≤ xbar := by linarith [h.xbar_gt]
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn h.continuous_F.continuousOn
  have hcl : ∀ s : assetX k xbar × Z, IsClosed (assetΓ d p xbar s) := fun s =>
    isClosed_le (continuous_dotR.comp (continuous_const.prodMk continuous_subtype_val))
      continuous_const
  have hq : Continuous fun s : assetX k xbar × Z => p s.2 := h.p_cont.comp continuous_snd
  have hl := isLHC_budget hq (fun s => h.p_pos s.2) hb hb0 hx
  exact ⟨fun s => (hl s).1, fun s => (hcl s).isCompact, hl, isUHC_budget hq hb hb0 hx,
    h.continuous_F.continuousOn,
    ⟨B, fun q _ => by simpa [Real.norm_eq_abs] using hB q (mem_univ _)⟩, h.β_pos, h.β_lt,
    continuous_fst.snd.continuousOn, contExp_first Q _ _ β (lemma_9_5_compact Q hQ)⟩

omit [MeasurableSpace Z] in
/-- The graph of `Γ(·, z)` is convex and `F(·, ·, z)` is concave on it. -/
theorem asset_cmb (h : AssetHyp U d p β xbar) {x x' y y' : assetX k xbar} {z : Z}
    (hy : y ∈ assetΓ d p xbar (x, z)) (hy' : y' ∈ assetΓ d p xbar (x', z)) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    cmb convex_assetX h0 h1 y y' ∈ assetΓ d p xbar (cmb convex_assetX h0 h1 x x', z) ∧
      assetC d p (cmb convex_assetX h0 h1 x x').1 (cmb convex_assetX h0 h1 y y').1 z =
        θ * assetC d p x.1 y.1 z + (1 - θ) * assetC d p x'.1 y'.1 z ∧
      θ * assetF U d p xbar (x, y, z) + (1 - θ) * assetF U d p xbar (x', y', z) ≤
        assetF U d p xbar (cmb convex_assetX h0 h1 x x', cmb convex_assetX h0 h1 y y', z) := by
  have hc : assetC d p (cmb convex_assetX h0 h1 x x').1 (cmb convex_assetX h0 h1 y y').1 z =
      θ * assetC d p x.1 y.1 z + (1 - θ) * assetC d p x'.1 y'.1 z := by
    simp only [assetC, cmb, dotR_cmb]; ring
  have e0 : 0 ≤ assetC d p x.1 y.1 z := sub_nonneg.2 hy
  have e1 : 0 ≤ assetC d p x'.1 y'.1 z := sub_nonneg.2 hy'
  have hθ1 : 0 ≤ 1 - θ := by linarith
  have hmem : cmb convex_assetX h0 h1 y y' ∈
      assetΓ d p xbar (cmb convex_assetX h0 h1 x x', z) := by
    have hpos : 0 ≤ assetC d p (cmb convex_assetX h0 h1 x x').1
        (cmb convex_assetX h0 h1 y y').1 z := by
      rw [hc]; positivity
    exact sub_nonneg.1 hpos
  refine ⟨hmem, hc, ?_⟩
  rw [assetF_of_mem hy, assetF_of_mem hy', assetF_of_mem hmem, hc]
  have := h.U_conc.concaveOn.2 e0 e1 h0 hθ1 (by ring)
  simpa only [smul_eq_mul] using this

variable [CompactSpace Z] [OpensMeasurableSpace Z]

/-- The rhs of the functional equation at a feasible `y` is at most `v`, with equality on `G`. -/
theorem asset_rhs_le (h : AssetHyp U d p β xbar) {Q : Kernel Z Z} [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : assetX k xbar × Z →ᵇ ℝ}
    (hv : bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v)
    {s : assetX k xbar × Z} {y : assetX k xbar} (hy : y ∈ assetΓ d p xbar s) :
    rhs (assetModel Q U d p β xbar) v s y ≤ v s := by
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax _ (asset_boundedDP h Q hQ) v s
  have := hmax y hy
  rwa [hv] at this

/-- `v(·, z)` is concave: `T` maps functions concave in `x` into themselves. -/
theorem asset_concave (h : AssetHyp U d p β xbar) {Q : Kernel Z Z} [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : assetX k xbar × Z →ᵇ ℝ}
    (hv : bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v) :
    ∀ z, IsConcaveS convex_assetX fun x => v (x, z) := by
  set M := assetModel Q U d p β xbar
  have hb := asset_boundedDP h Q hQ
  have hmaps : ∀ w : assetX k xbar × Z →ᵇ ℝ, (∀ z, IsConcaveS convex_assetX fun x => w (x, z)) →
      ∀ z, IsConcaveS convex_assetX fun x => bellman M hb w (x, z) := by
    intro w hw z x₀ x₁ θ h0 h1
    obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax M hb w (x₀, z)
    obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax M hb w (x₁, z)
    obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb w (cmb convex_assetX h0 h1 x₀ x₁, z)
    obtain ⟨hyθ, -, hF⟩ := asset_cmb h hy₀ hy₁ h0 h1
    have hE := expV_comb M hb (hX := convex_assetX) (hY := convex_assetX)
      (fun _ _ _ _ _ _ _ _ => rfl) hw hy₀ hy₁ h0 h1 hyθ
    have hm := hmax _ hyθ
    have hβE := mul_le_mul_of_nonneg_left hE h.β_pos.le
    simp only [rhs] at hv₀ hv₁ hm
    dsimp only
    rw [hv₀, hv₁]
    change _ ≤ M.β * _ at hβE
    change θ * (assetF U d p xbar (x₀, y₀, z) + M.β * _) +
      (1 - θ) * (assetF U d p xbar (x₁, y₁, z) + M.β * _) ≤ _
    linarith
  exact (corollary_1 (S' := {w : assetX k xbar × Z →ᵇ ℝ | ∀ z,
      IsConcaveS convex_assetX fun x => w (x, z)})
    (S'' := {w : assetX k xbar × Z →ᵇ ℝ | ∀ z, IsConcaveS convex_assetX fun x => w (x, z)})
    (bellman_contraction M hb) hv ⟨0, fun _ _ _ _ _ _ => by simp⟩ (isClosed_concaveX _)
    hmaps hmaps).1

/-- **Exercise 10.6a–b.** There is a unique bounded continuous `vᵖ` solving the functional
equation; it is the supremum function `v*`; `vᵖ(·, z)` is strictly increasing and concave;
`Gᵖ` is nonempty, compact-valued, u.h.c. and convex-valued; and all optimal portfolios have the
same cost `p(z)·y`. -/
theorem ex_10_6ab [BorelSpace Z] [SecondCountableTopology Z] (h : AssetHyp U d p β xbar)
    (Q : Kernel Z Z) [IsMarkovKernel Q] (hQ : IsFeller Q) :
    ∃ v : assetX k xbar × Z →ᵇ ℝ,
      bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v ∧
      (∀ w, bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) w = w → w = v) ∧
      (∀ s, vStar (assetModel Q U d p β xbar) s = v s) ∧
      (∀ z, StrictMono fun x => v (x, z)) ∧
      (∀ z, IsConcaveS convex_assetX fun x => v (x, z)) ∧
      (∀ s, (policy (assetModel Q U d p β xbar) v s).Nonempty ∧
        IsCompact (policy (assetModel Q U d p β xbar) v s) ∧
        IsUHC (policy (assetModel Q U d p β xbar) v) s) ∧
      (∀ s, Convex ℝ (Subtype.val '' policy (assetModel Q U d p β xbar) v s)) ∧
      ∀ s y y', y ∈ policy (assetModel Q U d p β xbar) v s →
        y' ∈ policy (assetModel Q U d p β xbar) v s → dotR (p s.2) y.1 = dotR (p s.2) y'.1 := by
  set M := assetModel Q U d p β xbar
  have hb := asset_boundedDP h Q hQ
  obtain ⟨v, hv, huniq, -, hG⟩ := ex_9_7b M hb
  have hvc := asset_concave h hQ hv
  -- `v = v*`, through a measurable selection from `G`
  obtain ⟨g, hgm, hgG⟩ := exists_measurableSelection (fun s => (hG s).2.2) fun s => (hG s).2.1
  have hopt := fun s₀ => bounded_vStar M hb measurable_snd.fst h.continuous_F.measurable hv
    (g := fun _ => g) (fun _ => hgm) (fun _ => hgG) s₀
  -- the objective at a mixture of two optimal portfolios
  have hmix : ∀ (s : assetX k xbar × Z) (y y' : assetX k xbar), y ∈ policy M v s →
      y' ∈ policy M v s → ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
        cmb convex_assetX h0 h1 y y' ∈ assetΓ d p xbar s ∧
        θ * U (assetC d p s.1.1 y.1 s.2) + (1 - θ) * U (assetC d p s.1.1 y'.1 s.2) +
          β * (θ * expV M v s y + (1 - θ) * expV M v s y') ≤
          rhs M v s (cmb convex_assetX h0 h1 y y') := by
    rintro ⟨x, z⟩ y y' hy hy' θ h0 h1
    obtain ⟨hyθ, -, hF⟩ := asset_cmb h hy.1 hy'.1 h0 h1
    rw [cmb_self] at hyθ hF
    have hE := expV_comb M hb (hX := convex_assetX) (hY := convex_assetX)
      (fun _ _ _ _ _ _ _ _ => rfl) hvc hy.1 hy'.1 h0 h1 (by rw [cmb_self]; exact hyθ)
    rw [cmb_self] at hE
    refine ⟨hyθ, ?_⟩
    rw [assetF_of_mem hy.1, assetF_of_mem hy'.1] at hF
    simp only [rhs]
    change _ ≤ assetF U d p xbar (x, cmb convex_assetX h0 h1 y y', z) + β * _
    nlinarith [mul_le_mul_of_nonneg_left hE h.β_pos.le]
  have hval : ∀ (s : assetX k xbar × Z) y, y ∈ policy M v s →
      v s = U (assetC d p s.1.1 y.1 s.2) + β * expV M v s y := by
    rintro ⟨x, z⟩ y hy
    have := hy.2
    simp only [rhs] at this
    rw [this]
    change assetF U d p xbar (x, y, z) + β * _ = _
    rw [assetF_of_mem hy.1]
  refine ⟨v, hv, huniq, fun s => (hopt s).2.2, fun z => ?_, hvc, hG, fun s => ?_,
    fun s y y' hy hy' => ?_⟩
  · -- strict monotonicity (Theorem 9.7)
    refine theorem_9_7 Q _ _ β hb (fun x x' y z hxx' hy => ?_) (fun x x' z hxx' y hy => ?_) hv z
    · have hlt : dotR (d z + p z) x.1 < dotR (d z + p z) x'.1 :=
        dotR_lt (fun i => add_pos (h.d_pos z i) (h.p_pos z i)) hxx'
      have hy' : y ∈ assetΓ d p xbar (x', z) := (show _ ≤ _ from hy).trans hlt.le
      rw [assetF_of_mem hy, assetF_of_mem hy']
      exact h.U_mono (mem_Ici.2 (sub_nonneg.2 hy)) (mem_Ici.2 (sub_nonneg.2 hy'))
        (by unfold assetC; linarith)
    · exact (show _ ≤ _ from hy).trans
        (dotR_le (fun i => (add_pos (h.d_pos z i) (h.p_pos z i)).le) hxx')
  · -- `G` is convex-valued
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ a b ha hb' hab
    obtain rfl : b = 1 - a := by linarith
    obtain ⟨hmem, hle⟩ := hmix s y y' hy hy' a ha (by linarith)
    refine ⟨cmb convex_assetX ha (by linarith) y y', ⟨hmem, le_antisymm ?_ ?_⟩, rfl⟩
    · have e1 := congrArg (fun t => a * t) (hval s y hy)
      have e2 := congrArg (fun t => (1 - a) * t) (hval s y' hy')
      linarith
    · exact asset_rhs_le h hQ hv hmem
  · -- equal cost, by strict concavity of `U`
    by_contra hne
    have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have h1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
    obtain ⟨hmem, hle⟩ := hmix s y y' hy hy' (1 / 2) h0 h1
    have hc : assetC d p s.1.1 y.1 s.2 ≠ assetC d p s.1.1 y'.1 s.2 := fun he => by
      apply hne; unfold assetC at he; linarith
    have hU := h.U_conc.2 (mem_Ici.2 (sub_nonneg.2 hy.1)) (mem_Ici.2 (sub_nonneg.2 hy'.1)) hc
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hcm : assetC d p s.1.1 (cmb convex_assetX h0 h1 y y').1 s.2 =
        1 / 2 * assetC d p s.1.1 y.1 s.2 + 1 / 2 * assetC d p s.1.1 y'.1 s.2 := by
      have := (asset_cmb h (z := s.2) (x := s.1) (x' := s.1) hy.1 hy'.1 h0 h1).2.1
      rw [cmb_self] at this
      rw [this]; ring
    have hrhs : rhs M v s (cmb convex_assetX h0 h1 y y') =
        U (assetC d p s.1.1 (cmb convex_assetX h0 h1 y y').1 s.2) +
          β * expV M v s (cmb convex_assetX h0 h1 y y') := by
      obtain ⟨x, z⟩ := s
      simp only [rhs]
      change assetF U d p xbar (x, _, z) + β * _ = _
      rw [assetF_of_mem hmem]
    have hE : (1 / 2) * expV M v s y + (1 - 1 / 2) * expV M v s y' ≤
        expV M v s (cmb convex_assetX h0 h1 y y') := by
      have := expV_comb M hb (hX := convex_assetX) (hY := convex_assetX)
        (fun _ _ _ _ _ _ _ _ => rfl) hvc (x := s.1) (x' := s.1) (z := s.2) hy.1 hy'.1 h0 h1
        (by rw [cmb_self]; exact hmem)
      rwa [cmb_self] at this
    have hlt := asset_rhs_le h hQ hv hmem
    rw [hrhs, hcm] at hlt
    simp only [smul_eq_mul] at hU
    have e1 := hval s y hy
    have e2 := hval s y' hy'
    have hβE := mul_le_mul_of_nonneg_left hE h.β_pos.le
    change 1 / 2 * U (assetC d p s.1.1 y.1 s.2) + 1 / 2 * U (assetC d p s.1.1 y'.1 s.2) <
      U (1 / 2 * assetC d p s.1.1 y.1 s.2 + 1 / 2 * assetC d p s.1.1 y'.1 s.2) at hU
    linarith

theorem assetX_mem_nhds {x : Fin k → ℝ} (hx : ∀ i, 0 < x i ∧ x i < xbar) :
    assetX k xbar ∈ 𝓝 x :=
  set_pi_mem_nhds finite_univ fun i _ => Icc_mem_nhds (hx i).1 (hx i).2

omit [CompactSpace Z] [OpensMeasurableSpace Z] in
/-- The value of a feasible choice: `rhs = U(c) + β ∫ v(y, z′) Q(z, dz′)`. -/
theorem asset_rhs_eq {Q : Kernel Z Z} (v : assetX k xbar × Z →ᵇ ℝ) {x y : assetX k xbar} {z : Z}
    (hy : y ∈ assetΓ d p xbar (x, z)) :
    rhs (assetModel Q U d p β xbar) v (x, z) y =
      U (assetC d p x.1 y.1 z) + β * ∫ z', v (y, z') ∂Q z := by
  simp only [rhs, expV]
  rw [assetF_of_mem hy]

/-- **Exercise 10.6c** (1). At an interior `x₀` with an optimal `y₀` leaving positive consumption
`c`, `vᵖ(·, z₀)` is differentiable with `vᵖᵢ(x₀, z₀) = U′(c)[dᵢ(z₀) + pᵢ(z₀)]`
(Benveniste–Scheinkman). -/
theorem ex_10_6c_deriv (h : AssetHyp U d p β xbar) {Q : Kernel Z Z} [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : assetX k xbar × Z →ᵇ ℝ}
    (hv : bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v)
    {x₀ y₀ : assetX k xbar} {z₀ : Z} (hint : ∀ i, 0 < x₀.1 i ∧ x₀.1 i < xbar)
    (hy₀ : y₀ ∈ policy (assetModel Q U d p β xbar) v (x₀, z₀))
    (hc : 0 < assetC d p x₀.1 y₀.1 z₀) {U' : ℝ}
    (hU' : HasDerivAt U U' (assetC d p x₀.1 y₀.1 z₀)) :
    HasFDerivAt (liftS fun x => v (x, z₀)) (U' • dotCLM (d z₀ + p z₀)) x₀.1 := by
  set a := d z₀ + p z₀
  set E := ∫ z', v (y₀, z') ∂Q z₀
  have hcx : ∀ x, assetC d p x y₀.1 z₀ = dotCLM a x - dotR (p z₀) y₀.1 := fun x => by
    rw [dotCLM_apply]; rfl
  have hL : HasFDerivAt (fun x => U (dotCLM a x - dotR (p z₀) y₀.1) + β * E)
      (U' • dotCLM a) x₀.1 := by
    rw [hcx] at hU'
    exact (hU'.comp_hasFDerivAt x₀.1 ((dotCLM a).hasFDerivAt.sub_const _)).add_const _
  refine theorem_4_10 (concaveOn_liftS (asset_concave h hQ hv z₀)) (assetX_mem_nhds hint) hL ?_ ?_
  · rw [liftS_of_mem _ x₀.2, ← hcx, hy₀.2, asset_rhs_eq v hy₀.1]
  · have hev : ∀ᶠ x in 𝓝 x₀.1, 0 < dotCLM a x - dotR (p z₀) y₀.1 := by
      rw [hcx] at hc
      exact ((dotCLM a).continuous.sub continuous_const).continuousAt.eventually (lt_mem_nhds hc)
    filter_upwards [hev, assetX_mem_nhds hint] with x hx hxS
    rw [liftS_of_mem _ hxS]
    have hy : y₀ ∈ assetΓ d p xbar (⟨x, hxS⟩, z₀) := by
      have := hx.le; rw [← hcx] at this; exact sub_nonneg.1 this
    have := asset_rhs_le h hQ hv hy
    rw [asset_rhs_eq v hy] at this
    rw [← hcx]
    exact this

/-- `p·(y + t eᵢ) = p·y + t pᵢ`. -/
theorem dotR_add_single (a y : Fin k → ℝ) (i : Fin k) (t : ℝ) :
    dotR a (y + t • Pi.single i 1) = dotR a y + t * a i := by
  simp only [dotR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
    (fun hi => absurd (Finset.mem_univ i) hi)]
  simp; ring

/-- **Exercise 10.6c** (2), the Euler equation. If moreover `y₀` is interior and each `vᵖ(·, z′)`
has partial derivative `vᵢ(z′)` at `y₀` (measurable in `z′`), then
`U′(c) pᵢ(z₀) = β ∫ vᵢ(z′) Q(z₀, dz′)`. -/
theorem ex_10_6c_euler (h : AssetHyp U d p β xbar) {Q : Kernel Z Z} [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : assetX k xbar × Z →ᵇ ℝ}
    (hv : bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v)
    {x₀ y₀ : assetX k xbar} {z₀ : Z} (hy₀ : y₀ ∈ policy (assetModel Q U d p β xbar) v (x₀, z₀))
    (hyint : ∀ i, 0 < y₀.1 i ∧ y₀.1 i < xbar) (hc : 0 < assetC d p x₀.1 y₀.1 z₀) {U' : ℝ}
    (hU' : HasDerivAt U U' (assetC d p x₀.1 y₀.1 z₀)) (i : Fin k) {vi : Z → ℝ}
    (hvim : AEStronglyMeasurable vi (Q z₀))
    (hvi : ∀ z', HasDerivAt (fun t : ℝ => liftS (fun y => v (y, z')) (y₀.1 + t • Pi.single i 1))
      (vi z') 0) :
    U' * p z₀ i = β * ∫ z', vi z' ∂Q z₀ := by
  set e : Fin k → ℝ := Pi.single i 1
  set r := min (y₀.1 i) (xbar - y₀.1 i)
  have hr : 0 < r := lt_min (hyint i).1 (by linarith [(hyint i).2])
  -- `y₀ + t eᵢ` stays in `X` for `|t| < r`
  have hmemX : ∀ t ∈ ball (0 : ℝ) r, y₀.1 + t • e ∈ assetX k xbar := by
    intro t ht
    rw [mem_ball, Real.dist_eq, sub_zero] at ht
    refine mem_assetX.2 fun j => ?_
    by_cases hj : j = i
    · subst hj
      have h1 := min_le_left (y₀.1 j) (xbar - y₀.1 j)
      have h2 := min_le_right (y₀.1 j) (xbar - y₀.1 j)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, Pi.single_eq_same, mul_one]
      constructor <;> linarith [neg_abs_le t, le_abs_self t]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, Pi.single_eq_of_ne hj, mul_zero,
        add_zero]
      exact mem_assetX.1 y₀.2 j
  set f : Z → ℝ → ℝ := fun z' t => liftS (fun y => v (y, z')) (y₀.1 + t • e)
  -- each `f(z′, ·)` is concave and bounded by `‖v‖` on `(−r, r)`, hence Lipschitz on `(−r/2, r/2)`
  have hconc : ∀ z', ConcaveOn ℝ (ball (0 : ℝ) r) (f z') := fun z' => by
    have hV := concaveOn_liftS (asset_concave h hQ hv z')
    refine ⟨convex_ball 0 r, fun a ha b hb θ η hθ hη hθη => ?_⟩
    have e1 : y₀.1 + (θ • a + η • b) • e = θ • (y₀.1 + a • e) + η • (y₀.1 + b • e) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(y₀.1 j)) * hθη
    have := hV.2 (hmemX a ha) (hmemX b hb) hθ hη hθη
    simp only [f]
    rw [e1]
    exact this
  have hbd : ∀ z' t, t ∈ ball (0 : ℝ) r → |f z' t| ≤ ‖v‖ := fun z' t ht => by
    simp only [f]
    rw [liftS_of_mem _ (hmemX t ht), ← Real.norm_eq_abs]
    exact v.norm_coe_le_norm _
  have hr2 : (0 : ℝ) < r / 2 := by positivity
  have hlip : ∀ z', LipschitzOnWith (Real.nnabs (2 * ‖v‖ / (r / 2))) (f z') (ball 0 (r - r / 2)) :=
    fun z' => by
      rw [Real.nnabs_of_nonneg (by positivity)]
      exact (hconc z').lipschitzOnWith_of_abs_le hr2 fun a ha => hbd z' a ha
  have hball : ball (0 : ℝ) (r - r / 2) ∈ 𝓝 0 := ball_mem_nhds 0 (by linarith)
  -- differentiate under the integral sign
  have hmeas : ∀ t ∈ ball (0 : ℝ) r, AEStronglyMeasurable (fun z' => f z' t) (Q z₀) := by
    intro t ht
    have : (fun z' => f z' t) = fun z' => v (⟨y₀.1 + t • e, hmemX t ht⟩, z') := by
      funext z'; simp only [f]; rw [liftS_of_mem _ (hmemX t ht)]
    rw [this]
    exact (v.continuous.comp (Continuous.prodMk_right _)).aestronglyMeasurable
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_lip (μ := Q z₀)
    (F := fun t z' => f z' t)
    (bound := fun _ => 2 * ‖v‖ / (r / 2)) hball
    (eventually_of_mem (ball_mem_nhds 0 hr) hmeas)
    (integrable_of_abs_le (by
      have := hmeas 0 (mem_ball_self hr)
      have e0 : (fun z' => f z' 0) = fun z' => v (y₀, z') := by
        funext z'; simp only [f, zero_smul, add_zero]; rw [liftS_of_mem _ y₀.2]
      rw [e0]
      exact (v.continuous.comp (Continuous.prodMk_right _)).measurable)
      fun z' => hbd z' 0 (mem_ball_self hr))
    hvim (Eventually.of_forall hlip) (integrable_const _) (Eventually.of_forall hvi)
  -- the objective along `y₀ + t eᵢ`
  set c₀ := assetC d p x₀.1 y₀.1 z₀
  set Φ : ℝ → ℝ := fun t => U (c₀ - t * p z₀ i) + β * ∫ z', f z' t ∂Q z₀
  have hΦ : HasDerivAt Φ (U' * (-p z₀ i) + β * ∫ z', vi z' ∂Q z₀) 0 := by
    have hin : HasDerivAt (fun t : ℝ => c₀ - t * p z₀ i) (-p z₀ i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (p z₀ i)).const_sub c₀
    have := hU'
    rw [show c₀ = c₀ - 0 * p z₀ i by ring] at this
    exact (this.comp 0 hin).add (hderiv.const_mul β)
  have hmax : IsLocalMax Φ 0 := by
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ c₀ - t * p z₀ i :=
      ((continuous_const.sub (continuous_id.mul continuous_const)).continuousAt.eventually
        (lt_mem_nhds (show 0 < c₀ - 0 * p z₀ i by simpa using hc))).mono fun _ ht => ht.le
    filter_upwards [hev, ball_mem_nhds (0 : ℝ) hr] with t ht htr
    set yt : assetX k xbar := ⟨y₀.1 + t • e, hmemX t htr⟩
    have hct : assetC d p x₀.1 yt.1 z₀ = c₀ - t * p z₀ i := by
      change dotR (d z₀ + p z₀) x₀.1 - dotR (p z₀) (y₀.1 + t • e) =
        assetC d p x₀.1 y₀.1 z₀ - t * p z₀ i
      rw [dotR_add_single]; unfold assetC; ring
    have hyt : yt ∈ assetΓ d p xbar (x₀, z₀) := sub_nonneg.1 (hct ▸ ht)
    have hle := asset_rhs_le h hQ hv hyt
    rw [asset_rhs_eq v hyt, hct] at hle
    have h0 : Φ 0 = v (x₀, z₀) := by
      simp only [Φ, zero_mul, sub_zero, f, zero_smul, add_zero]
      rw [hy₀.2, asset_rhs_eq v hy₀.1]
      congr 2
      exact integral_congr_ae (Eventually.of_forall fun z' => by
        simp only; rw [liftS_of_mem _ y₀.2])
    rw [h0]
    simp only [Φ, f]
    convert hle using 3
    exact integral_congr_ae (Eventually.of_forall fun z' => by
      simp only; rw [liftS_of_mem _ (hmemX t htr)])
  have := hmax.hasDerivAt_eq_zero hΦ
  linarith

/-- The portfolio of one share of each asset. -/
def oneX (h1 : 1 ≤ xbar) : assetX k xbar := ⟨fun _ => 1, mem_assetX.2 fun _ => ⟨zero_le_one, h1⟩⟩

omit [MetricSpace Z] [MeasurableSpace Z] [CompactSpace Z] [OpensMeasurableSpace Z] in
theorem assetC_one (h1 : 1 ≤ xbar) (z : Z) :
    assetC d p (oneX (k := k) h1).1 (oneX h1).1 z = ∑ j, d z j := by
  simp [assetC, dotR, oneX, Finset.sum_add_distrib]

theorem dotR_single (a : Fin k → ℝ) (i : Fin k) : dotR a (Pi.single i 1) = a i := by
  have := dotR_add_single a 0 i 1
  simpa [dotR] using this

/-- **Exercise 10.6d.** If holding one share of each asset is optimal in every state (the
equilibrium condition), then (3) `vᵢ(1, z) = U′(z·1)[zᵢ + pᵢ(z)]` and (4)–(5)
`U′(z·1) pᵢ(z) = β ∫ U′(z′·1)[z′ᵢ + pᵢ(z′)] Q(z, dz′)`. -/
theorem ex_10_6d (h : AssetHyp U d p β xbar) (hk : 0 < k) {Q : Kernel Z Z} [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : assetX k xbar × Z →ᵇ ℝ}
    (hv : bellman (assetModel Q U d p β xbar) (asset_boundedDP h Q hQ) v = v) {Up : ℝ → ℝ}
    (hUp : Continuous Up) (hUd : ∀ c, 0 < c → HasDerivAt U (Up c) c)
    (heq : ∀ z, oneX h.xbar_gt.le ∈ policy (assetModel Q U d p β xbar) v (oneX h.xbar_gt.le, z)) :
    (∀ z, HasFDerivAt (liftS fun x => v (x, z)) (Up (∑ j, d z j) • dotCLM (d z + p z))
      (fun _ => 1)) ∧
    ∀ z i, Up (∑ j, d z j) * p z i =
      β * ∫ z', Up (∑ j, d z' j) * (d z' i + p z' i) ∂Q z := by
  set one := oneX (k := k) h.xbar_gt.le
  have hint : ∀ i, 0 < one.1 i ∧ one.1 i < xbar := fun _ => ⟨one_pos, h.xbar_gt⟩
  have hc' : ∀ z, assetC d p one.1 one.1 z = ∑ j, d z j := fun z => assetC_one _ z
  have hsum : ∀ z, 0 < ∑ j, d z j := fun z => by
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact Finset.sum_pos (fun j _ => h.d_pos z j) Finset.univ_nonempty
  have hc : ∀ z, 0 < assetC d p one.1 one.1 z := fun z => by rw [hc' z]; exact hsum z
  have hU'' : ∀ z, HasDerivAt U (Up (∑ j, d z j)) (assetC d p one.1 one.1 z) := fun z => by
    rw [hc' z]; exact hUd _ (hsum z)
  have h3 : ∀ z, HasFDerivAt (liftS fun x => v (x, z)) (Up (∑ j, d z j) • dotCLM (d z + p z))
      (fun _ => 1) := fun z => ex_10_6c_deriv h hQ hv hint (heq z) (hc z) (hU'' z)
  refine ⟨h3, fun z i => ?_⟩
  set e : Fin k → ℝ := Pi.single i 1
  have hvi : ∀ z', HasDerivAt (fun t : ℝ => liftS (fun y => v (y, z')) (one.1 + t • e))
      (Up (∑ j, d z' j) * (d z' i + p z' i)) 0 := fun z' => by
    have hline : HasDerivAt (fun t : ℝ => one.1 + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add one.1
    have h3' := h3 z'
    rw [show (fun _ : Fin k => (1 : ℝ)) = one.1 + (0 : ℝ) • e by simp [one, oneX]] at h3'
    refine (h3'.comp_hasDerivAt (0 : ℝ) hline).congr_deriv ?_
    simp only [_root_.smul_apply, smul_eq_mul, dotCLM_apply, e, dotR_single, Pi.add_apply]
  have hvim : AEStronglyMeasurable (fun z' => Up (∑ j, d z' j) * (d z' i + p z' i)) (Q z) :=
    ((hUp.comp (continuous_finsetSum _ fun j _ => (continuous_apply j).comp h.d_cont)).mul
      (((continuous_apply i).comp h.d_cont).add
        ((continuous_apply i).comp h.p_cont))).aestronglyMeasurable
  exact ex_10_6c_euler h hQ hv (heq z) hint (hc z) (hU'' z) i hvim hvi

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A model of search unemployment

SLP §10.7, pp. 304–307, Exercise 10.7a–c. A worker with wage offer `w ∈ W = [0, w̄]` either works
(`y = 1`), earning `U(w)` and keeping the job next period with probability `1 − θ`, or searches
(`y = 0`), earning nothing and drawing a new offer from `μ`. The exogenous shocks are
`(d, z) ∈ {0, 1} × W`, i.i.d. with law `(θ δ₀ + (1 − θ) δ₁) ⊗ μ`: `d = 0` means the job is lost.
The book takes `μ` with a density `f`; any probability measure on `W` will do here.

* **Exercise 10.7a** (`searchφ`, `ex_10_7a`): the law of motion is
  `w_{t+1} = w_t` if `y_t = 1` and `d_{t+1} = 1`, `0` if `y_t = 1` and `d_{t+1} = 0`, and
  `z_{t+1}` if `y_t = 0`.
* `search_boundedDP`: the hypotheses of §9.2 hold, so Chapter 9 applies.
* **Exercise 10.7b–c** (`ex_10_7c`): the fixed point `v(w, d, z)` does not depend on `(d, z)`.
  Its section `v(w)` is the unique continuous solution of
  `v(w) = max {U(w) + β[(1 − θ)v(w) + θv(0)], β ∫ v dμ}` (1), it is nondecreasing, and it is the
  supremum function of the sequence problem, which therefore depends only on `w₀`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- The two-point set `{0, 1}` (as a subset of `ℕ`, which carries a metric). -/
abbrev Two : Type := Set.Iic (1 : ℕ)

/-- `0 ∈ {0, 1}`. -/
def two0 : Two := ⟨0, Set.mem_Iic.2 zero_le_one⟩

/-- `1 ∈ {0, 1}`. -/
def two1 : Two := ⟨1, Set.mem_Iic.2 le_rfl⟩

theorem two_cases (y : Two) : y = two0 ∨ y = two1 := by
  obtain ⟨n, hn⟩ := y
  have : n ≤ 1 := hn
  interval_cases n
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr (Subtype.ext rfl)

theorem two0_ne_two1 : two0 ≠ two1 := by
  intro h
  have := congrArg Subtype.val h
  simp [two0, two1] at this

/-- The law of the job-loss shock: `d = 0` (job lost) with probability `θ`. -/
noncomputable def lossMeasure (θ : ℝ) : Measure Two :=
  ENNReal.ofReal θ • Measure.dirac two0 + ENNReal.ofReal (1 - θ) • Measure.dirac two1

theorem isProbabilityMeasure_lossMeasure {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    IsProbabilityMeasure (lossMeasure θ) :=
  ⟨by simp [lossMeasure, ← ENNReal.ofReal_add h0 (by linarith : (0 : ℝ) ≤ 1 - θ)]⟩

theorem integral_lossMeasure {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (g : Two → ℝ) :
    ∫ d, g d ∂lossMeasure θ = θ * g two0 + (1 - θ) * g two1 := by
  have : IsFiniteMeasure (ENNReal.ofReal θ • Measure.dirac two0) := ⟨by simp⟩
  have : IsFiniteMeasure (ENNReal.ofReal (1 - θ) • Measure.dirac two1) := ⟨by simp⟩
  rw [lossMeasure, integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- Integration against `(θ δ₀ + (1 − θ) δ₁) ⊗ μ`. -/
theorem integral_loss_prod {W : Type*} [MeasurableSpace W] {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (μ : Measure W) [IsProbabilityMeasure μ] {g : Two × W → ℝ}
    (hg : Integrable g ((lossMeasure θ).prod μ)) :
    ∫ p, g p ∂(lossMeasure θ).prod μ =
      θ * ∫ z, g (two0, z) ∂μ + (1 - θ) * ∫ z, g (two1, z) ∂μ := by
  have : IsProbabilityMeasure (lossMeasure θ) := isProbabilityMeasure_lossMeasure h0 h1
  rw [integral_prod g hg, integral_lossMeasure h0 h1]

/-- The hypotheses of SLP §10.7 used here: `0 < β < 1`, `0 ≤ θ ≤ 1`, and `U` continuous and
strictly increasing on `W = [0, w̄]` with `U(0) = 0`. (Concavity and differentiability of `U`
are not needed.) -/
structure SearchHyp (U : ℝ → ℝ) (θ β wbar : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  θ_nonneg : 0 ≤ θ
  θ_le : θ ≤ 1
  wbar_pos : 0 < wbar
  U_cont : ContinuousOn U (Icc 0 wbar)
  U_mono : StrictMonoOn U (Icc 0 wbar)
  U_zero : U 0 = 0

variable {U : ℝ → ℝ} {θ β wbar : ℝ}

/-- The zero wage. -/
def w0 (hw : 0 ≤ wbar) : Icc (0 : ℝ) wbar := ⟨0, le_rfl, hw⟩

/-- **Exercise 10.7a.** The law of motion `w_{t+1} = φ(w_t, y_t, d_{t+1}, z_{t+1})`. -/
def searchφ (hw : 0 ≤ wbar)
    (p : Icc (0 : ℝ) wbar × Two × (Two × Icc (0 : ℝ) wbar)) : Icc (0 : ℝ) wbar :=
  if p.2.1 = two1 then (if p.2.2.1 = two1 then p.1 else w0 hw) else p.2.2.2

/-- The return: `U(w)` when working, `0` when searching. -/
def searchF (U : ℝ → ℝ) (p : Icc (0 : ℝ) wbar × Two × (Two × Icc (0 : ℝ) wbar)) : ℝ :=
  if p.2.1 = two1 then U p.1.1 else 0

/-- The search model in the second formulation of Chapter 9: `x = w`, `y ∈ {0, 1}`, shocks
`(d, z)` i.i.d. -/
noncomputable abbrev searchModel (hw : 0 ≤ wbar) (U : ℝ → ℝ) (θ β : ℝ)
    (μ : Measure (Icc (0 : ℝ) wbar)) :
    Model (Icc (0 : ℝ) wbar) Two (Two × Icc (0 : ℝ) wbar) :=
  ⟨Kernel.const _ ((lossMeasure θ).prod μ), fun _ => univ, searchφ hw, searchF U, β⟩

/-- **Exercise 10.7a.** -/
theorem ex_10_7a (hw : 0 ≤ wbar) (w z : Icc (0 : ℝ) wbar) :
    searchφ hw (w, two1, (two1, z)) = w ∧ searchφ hw (w, two1, (two0, z)) = w0 hw ∧
      ∀ d, searchφ hw (w, two0, (d, z)) = z := by
  refine ⟨by simp [searchφ], by simp [searchφ, two0_ne_two1], fun d => by
    simp [searchφ, two0_ne_two1]⟩

theorem continuous_searchF (h : SearchHyp U θ β wbar) :
    Continuous (searchF U : Icc (0 : ℝ) wbar × Two × (Two × Icc (0 : ℝ) wbar) → ℝ) := by
  have hU : Continuous fun w : Icc (0 : ℝ) wbar => U w.1 :=
    h.U_cont.comp_continuous continuous_subtype_val fun w => w.2
  have hG : Continuous fun q : Two × (Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar)) =>
      if q.1 = two1 then U q.2.1.1 else 0 := by
    refine continuous_prod_of_discrete_left.2 fun y => ?_
    dsimp only
    split_ifs
    · exact hU.comp continuous_fst
    · exact continuous_const
  exact hG.comp (continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))

theorem continuous_searchφ (hw : 0 ≤ wbar) :
    Continuous fun q : (Icc (0 : ℝ) wbar × Two) × (Two × Icc (0 : ℝ) wbar) =>
      searchφ hw (q.1.1, q.1.2, q.2) := by
  have hH : Continuous fun q : (Two × Two) × (Icc (0 : ℝ) wbar × Icc (0 : ℝ) wbar) =>
      if q.1.1 = two1 then (if q.1.2 = two1 then q.2.1 else w0 hw) else q.2.2 := by
    refine continuous_prod_of_discrete_left.2 fun yd => ?_
    dsimp only
    split_ifs
    · exact continuous_fst
    · exact continuous_const
    · exact continuous_snd
  exact hH.comp ((continuous_fst.snd.prodMk continuous_snd.fst).prodMk
    (continuous_fst.fst.prodMk continuous_snd.snd))

theorem continuous_searchφ' (hw : 0 ≤ wbar) : Continuous (searchφ hw) :=
  (continuous_searchφ hw).comp ((continuous_fst.prodMk continuous_snd.fst).prodMk
    continuous_snd.snd)

/-- The hypotheses of §9.2 hold for the search model. -/
theorem search_boundedDP (h : SearchHyp U θ β wbar) (μ : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure (lossMeasure θ)] :
    BoundedDP (searchModel h.wbar_pos.le U θ β μ) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_searchF h (wbar := wbar)).continuousOn
  have hφ := continuous_searchφ h.wbar_pos.le
  refine ⟨fun _ => univ_nonempty, fun _ => isCompact_univ,
    fun _ => ⟨univ_nonempty, fun y _ _ _ => ⟨0, fun _ => y, fun _ _ => mem_univ _,
      tendsto_const_nhds⟩⟩, fun _ => ⟨univ_nonempty, fun xs _ ys _ => ?_⟩,
    (continuous_searchF h).continuousOn, ⟨B, fun p _ => by
      simpa [Real.norm_eq_abs] using hB p (mem_univ _)⟩, h.β_pos, h.β_lt, hφ.continuousOn,
    contExp_of_preservesBC _ hφ.continuousOn
      (lemma_9_5_compact _ (isFeller_const _))⟩
  obtain ⟨y, -, φ, hφ', hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
  exact ⟨y, mem_univ _, φ, hφ', hlim⟩

variable (h : SearchHyp U θ β wbar) (μ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure μ]
  [IsProbabilityMeasure (lossMeasure θ)]

/-- `T` does not see the current shock: `(Tf)(w, s) = (Tf)(w, s′)`. -/
theorem search_bellman_indep (f : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ)
    (w : Icc (0 : ℝ) wbar) (s s' : Two × Icc (0 : ℝ) wbar) :
    bellman (searchModel h.wbar_pos.le U θ β μ) (search_boundedDP h μ) f (w, s) =
      bellman (searchModel h.wbar_pos.le U θ β μ) (search_boundedDP h μ) f (w, s') := by
  simp only [bellman_apply, maxValue, objG, rhs, expV, searchF, Kernel.const_apply]

/-- The expected continuation values: working gives `θ f(0) + (1 − θ) f(w)`, searching
`∫ f dμ`, when `f` does not depend on the shock. -/
theorem search_expV {f : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ}
    (hf : ∀ w s s', f (w, s) = f (w, s')) (s₀ : Two × Icc (0 : ℝ) wbar)
    (w : Icc (0 : ℝ) wbar) (s : Two × Icc (0 : ℝ) wbar) :
    expV (searchModel h.wbar_pos.le U θ β μ) f (w, s) two1 =
        θ * f (w0 h.wbar_pos.le, s₀) + (1 - θ) * f (w, s₀) ∧
      expV (searchModel h.wbar_pos.le U θ β μ) f (w, s) two0 = ∫ z, f (z, s₀) ∂μ := by
  have hint : ∀ y, Integrable (fun p => f (searchφ h.wbar_pos.le (w, y, p), p))
      ((lossMeasure θ).prod μ) := fun y => by
    have hc : Continuous fun p : Two × Icc (0 : ℝ) wbar => f (searchφ h.wbar_pos.le (w, y, p), p) :=
      f.continuous.comp (((continuous_searchφ' h.wbar_pos.le).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))).prodMk continuous_id)
    exact integrable_of_abs_le hc.measurable fun p => by
      rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
  simp only [expV, Kernel.const_apply]
  constructor
  · rw [integral_loss_prod h.θ_nonneg h.θ_le μ (hint two1)]
    have e1 : ∀ z, searchφ h.wbar_pos.le (w, two1, (two1, z)) = w := fun z => by
      simp [searchφ]
    have e0 : ∀ z, searchφ h.wbar_pos.le (w, two1, (two0, z)) = w0 h.wbar_pos.le := fun z => by
      simp [searchφ, two0_ne_two1]
    simp only [e0, e1]
    rw [show (fun z => f (w0 h.wbar_pos.le, (two0, z))) = fun _ => f (w0 h.wbar_pos.le, s₀) from
      funext fun z => hf _ _ _, show (fun z => f (w, (two1, z))) = fun _ => f (w, s₀) from
      funext fun z => hf _ _ _]
    simp
  · rw [integral_loss_prod h.θ_nonneg h.θ_le μ (hint two0)]
    have e : ∀ d z, searchφ h.wbar_pos.le (w, two0, (d, z)) = z := fun d z => by
      simp [searchφ, two0_ne_two1]
    simp only [e]
    rw [show (fun z => f (z, (two0, z))) = fun z => f (z, s₀) from funext fun z => hf _ _ _,
      show (fun z => f (z, (two1, z))) = fun z => f (z, s₀) from funext fun z => hf _ _ _]
    ring

/-- The value at a state is the larger of working and searching. -/
theorem search_bellman_eq_max {f : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ}
    (hf : ∀ w s s', f (w, s) = f (w, s')) (s₀ : Two × Icc (0 : ℝ) wbar)
    (w : Icc (0 : ℝ) wbar) (s : Two × Icc (0 : ℝ) wbar) :
    bellman (searchModel h.wbar_pos.le U θ β μ) (search_boundedDP h μ) f (w, s) =
      max (U w.1 + β * (θ * f (w0 h.wbar_pos.le, s₀) + (1 - θ) * f (w, s₀)))
        (β * ∫ z, f (z, s₀) ∂μ) := by
  set M := searchModel h.wbar_pos.le U θ β μ
  have hb := search_boundedDP h μ
  obtain ⟨e1, e0⟩ := search_expV h μ hf s₀ w s
  have r1 : rhs M f (w, s) two1 =
      U w.1 + β * (θ * f (w0 h.wbar_pos.le, s₀) + (1 - θ) * f (w, s₀)) := by
    simp only [rhs]; rw [e1]; simp [M, searchF]
  have r0 : rhs M f (w, s) two0 = β * ∫ z, f (z, s₀) ∂μ := by
    simp only [rhs]; rw [e0]; simp [M, searchF, two0_ne_two1]
  obtain ⟨y, -, hval, hmax⟩ := exists_bellman_argmax M hb f (w, s)
  rw [← r1, ← r0]
  refine le_antisymm ?_ (max_le (hmax two1 (mem_univ _)) (hmax two0 (mem_univ _)))
  rw [hval]
  rcases two_cases y with rfl | rfl
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- **Exercise 10.7b–c.** Let `v` be the fixed point of `T` (Theorem 9.6), and `v(w)` its section
at any shock `s₀`. Then `v(w, s)` does not depend on `s`; `v(w)` satisfies (1) and is the only
continuous solution of (1); `v(w)` is nondecreasing; and `v(w) = v*(w, s)` for every `s`, so the
supremum function depends only on `w₀`. -/
theorem ex_10_7c {v : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ}
    (hv : bellman (searchModel h.wbar_pos.le U θ β μ) (search_boundedDP h μ) v = v)
    (s₀ : Two × Icc (0 : ℝ) wbar) :
    (∀ w s, v (w, s) = v (w, s₀)) ∧
      (∀ w, v (w, s₀) = max (U w.1 + β * ((1 - θ) * v (w, s₀) + θ * v (w0 h.wbar_pos.le, s₀)))
        (β * ∫ z, v (z, s₀) ∂μ)) ∧
      (∀ u : C(Icc (0 : ℝ) wbar, ℝ), (∀ w, u w = max (U w.1 + β * ((1 - θ) * u w +
        θ * u (w0 h.wbar_pos.le))) (β * ∫ z, u z ∂μ)) → ∀ w, u w = v (w, s₀)) ∧
      Monotone (fun w => v (w, s₀)) ∧
      ∀ w s, vStar (searchModel h.wbar_pos.le U θ β μ) (w, s) = v (w, s₀) := by
  set M := searchModel h.wbar_pos.le U θ β μ
  have hb := search_boundedDP h μ
  obtain ⟨v', -, huniq, -, -⟩ := ex_9_7b M hb
  have hind : ∀ w s s', v (w, s) = v (w, s') := fun w s s' => by
    rw [← hv]; exact search_bellman_indep h μ v w s s'
  have hfe : ∀ w, v (w, s₀) = max (U w.1 + β * ((1 - θ) * v (w, s₀) +
      θ * v (w0 h.wbar_pos.le, s₀))) (β * ∫ z, v (z, s₀) ∂μ) := fun w => by
    conv_lhs => rw [← hv]
    rw [search_bellman_eq_max h μ hind s₀ w s₀]
    ring_nf
  refine ⟨fun w s => hind w s s₀, hfe, fun u hu w => ?_, ?_, fun w s => ?_⟩
  · -- uniqueness: lift `u` to a fixed point of `T`
    have : CompactSpace (Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar)) := inferInstance
    set ũ : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ :=
      mkOfCompact (u.comp ⟨Prod.fst, continuous_fst⟩)
    have hũ : ∀ w s s', ũ (w, s) = ũ (w, s') := fun _ _ _ => rfl
    have hfix : bellman M hb ũ = ũ := by
      ext ⟨w, s⟩
      rw [search_bellman_eq_max h μ hũ s₀ w s]
      change _ = u w
      rw [hu w]
      change max (U w.1 + β * (θ * u (w0 h.wbar_pos.le) + (1 - θ) * u w)) (β * ∫ z, u z ∂μ) = _
      ring_nf
    have := (huniq ũ hfix).trans (huniq v hv).symm
    change ũ (w, s₀) = v (w, s₀)
    rw [this]
  · -- monotonicity: `T` maps functions nondecreasing in `w` into themselves
    set C' : Set (Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ) :=
      {f | ∀ s, Monotone fun w => f (w, s)}
    have hclosed : IsClosed C' := by
      have := isClosed_pointwise_le (S := Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar))
        (ι := {q : Icc (0 : ℝ) wbar × Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) //
          q.1 ≤ q.2.1}) (fun q => (q.1.1, q.1.2.2)) (fun q => (q.1.2.1, q.1.2.2))
      convert this using 1
      ext f
      exact ⟨fun hf q => hf q.1.2.2 q.2, fun hf s w w' hww' => hf ⟨(w, w', s), hww'⟩⟩
    have hmaps : MapsTo (bellman M hb) C' C' := by
      intro f hf s w w' hww'
      obtain ⟨y, -, hval, -⟩ := exists_bellman_argmax M hb f (w, s)
      obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb f (w', s)
      dsimp only
      rw [hval]
      refine le_trans ?_ (hmax y (mem_univ _))
      simp only [rhs, expV]
      have hint : ∀ x, Integrable (fun p => f (searchφ h.wbar_pos.le (x, y, p), p))
          ((lossMeasure θ).prod μ) := fun x => by
        have hc : Continuous fun p : Two × Icc (0 : ℝ) wbar =>
            f (searchφ h.wbar_pos.le (x, y, p), p) :=
          f.continuous.comp (((continuous_searchφ' h.wbar_pos.le).comp
            (continuous_const.prodMk (continuous_const.prodMk continuous_id))).prodMk
              continuous_id)
        exact integrable_of_abs_le hc.measurable fun p => by
          rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
      have hE := integral_mono (hint w) (hint w') fun p => by
        refine hf p ?_
        change searchφ h.wbar_pos.le (w, y, p) ≤ searchφ h.wbar_pos.le (w', y, p)
        simp only [searchφ]
        split_ifs
        · exact hww'
        · exact le_rfl
        · exact le_rfl
      have hF : searchF U (w, y, s) ≤ searchF U (w', y, s) := by
        simp only [searchF]
        split_ifs
        · exact h.U_mono.monotoneOn w.2 w'.2 hww'
        · exact le_rfl
      change searchF U (w, y, s) + β * ∫ p, f (searchφ h.wbar_pos.le (w, y, p), p)
          ∂((lossMeasure θ).prod μ) ≤
        searchF U (w', y, s) + β * ∫ p, f (searchφ h.wbar_pos.le (w', y, p), p)
          ∂((lossMeasure θ).prod μ)
      have := mul_le_mul_of_nonneg_left hE h.β_pos.le
      linarith
    exact (corollary_1 (S' := C') (S'' := C') (bellman_contraction M hb) hv
      ⟨0, fun _ _ _ _ => le_rfl⟩ hclosed hmaps hmaps).1 s₀
  · -- `v = v*`, with the measurable policy "work iff working is at least as good"
    have hcont : Continuous fun p : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) =>
        (objG M v (p, two1), objG M v (p, two0)) := by
      have hc := continuousOn_univ.1 ((continuousOn_objG M hb v).mono fun _ _ => mem_univ _)
      exact (hc.comp (continuous_id.prodMk continuous_const)).prodMk
        (hc.comp (continuous_id.prodMk continuous_const))
    set g : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) → Two := fun p =>
      if objG M v (p, two0) ≤ objG M v (p, two1) then two1 else two0
    have hgm : Measurable g := by
      classical
      refine Measurable.ite ?_ measurable_const measurable_const
      exact (isClosed_le (continuous_snd.comp hcont) (continuous_fst.comp hcont)).measurableSet
    have hgG : ∀ p, g p ∈ policy M v p := fun p => by
      rw [policy_eq_argmax M hb hv]
      refine ⟨mem_univ _, le_antisymm ?_ ?_⟩
      · exact le_maxValue (continuousOn_objG M hb v) (hb.compact p) (mem_univ _)
      · obtain ⟨y, -, hval, hmax⟩ := exists_argmax (continuousOn_objG M hb v) (hb.compact p)
          (hb.nonempty p)
        rw [← hval]
        simp only [g]
        split_ifs with hle
        · rcases two_cases y with rfl | rfl
          · exact hle
          · exact le_rfl
        · rcases two_cases y with rfl | rfl
          · exact le_rfl
          · exact (not_le.1 hle).le
    have hopt := bounded_vStar M hb (continuous_searchφ' h.wbar_pos.le).measurable
      (continuous_searchF h).measurable hv (g := fun _ => g) (fun _ => hgm) (fun _ => hgG) (w, s)
    rw [hopt.2.2, hind w s s₀]

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Search unemployment: the reservation wage

SLP §10.7, Exercise 10.7d–h, pp. 306–307. Let `v` be a continuous nondecreasing solution of (1)
(`SearchSol`; the fixed point of Exercise 10.7c is one: `searchSol_of_fixed`), and
`A = β ∫ v dμ`. Suppose `μ` puts positive mass on positive wages (with a density this always
holds). Write `F(w) = μ([0, w))`; with a density this is the book's `F(w) = ∫₀ʷ f`.

* `SearchSol.nonneg`, `SearchSol.v_zero`, `SearchSol.A_pos`: `v ≥ 0`, `v(0) = A` and `A > 0`.
* **Exercise 10.7d** (`ex_10_7d`): there is a unique `w*` with
  `v(w*) = U(w*) + β[(1 − θ)v(w*) + θA] = A`, and then `U(w*) = (1 − β)A` (3).
* **Exercise 10.7e** (`ex_10_7e`): `v(w) = A` for `w < w*` and
  `v(w) = [U(w) + βθA]/[1 − β(1 − θ)]` for `w ≥ w*` (4).
* **Exercise 10.7f** (`ex_10_7f`): `(1 − β)A = β/[1 + βθ − βF(w*)] ∫_{w ≥ w*} U dμ` (5).
* **Exercise 10.7g** (`ex_10_7g`): `[1 + βθ − βF(w*)]U(w*) = β ∫_{w ≥ w*} U dμ` (6), and `w*` is the
  only solution of (6): its left side minus its right side, `resΨ`, is strictly increasing in
  `w` (`resΨ_strictMono`).
* **Exercise 10.7h** (`ex_10_7h_θ`, `ex_10_7h_β`): the reservation wage is strictly decreasing in
  the job-loss probability `θ` and, for `θ < 1`, strictly increasing in the discount factor `β`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {U : ℝ → ℝ} {θ β wbar : ℝ} (h : SearchHyp U θ β wbar) (μ : Measure (Icc (0 : ℝ) wbar))

/-- `v` is a continuous nondecreasing solution of the functional equation (1). -/
structure SearchSol (v : Icc (0 : ℝ) wbar → ℝ) : Prop where
  cont : Continuous v
  mono : Monotone v
  fe : ∀ w, v w = max (U w.1 + β * ((1 - θ) * v w + θ * v (w0 h.wbar_pos.le)))
    (β * ∫ z, v z ∂μ)

variable {h} {μ}

/-- The fixed point of Exercise 10.7c gives a solution. -/
theorem searchSol_of_fixed (h : SearchHyp U θ β wbar) (μ : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure (lossMeasure θ)]
    {v : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ}
    (hv : bellman (searchModel h.wbar_pos.le U θ β μ) (search_boundedDP h μ) v = v)
    (s₀ : Two × Icc (0 : ℝ) wbar) : SearchSol h μ fun w => v (w, s₀) := by
  obtain ⟨-, hfe, -, hmono, -⟩ := ex_10_7c h μ hv s₀
  exact ⟨v.continuous.comp (continuous_id.prodMk continuous_const), hmono, hfe⟩

theorem SearchHyp.U_nonneg (h : SearchHyp U θ β wbar) (w : Icc (0 : ℝ) wbar) : 0 ≤ U w.1 := by
  have := h.U_mono.monotoneOn (left_mem_Icc.2 h.wbar_pos.le) w.2 w.2.1
  rwa [h.U_zero] at this

theorem SearchHyp.integrable_U (h : SearchHyp U θ β wbar) (μ : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure μ] : Integrable (fun w : Icc (0 : ℝ) wbar => U w.1) μ :=
  (h.U_cont.comp_continuous continuous_subtype_val fun w => w.2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

namespace SearchSol

variable {h : SearchHyp U θ β wbar} {v : Icc (0 : ℝ) wbar → ℝ} (hs : SearchSol h μ v)
include hs

theorem integrable [IsProbabilityMeasure μ] : Integrable v μ :=
  hs.cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace v)

/-- `v ≥ 0`: at the bottom, `v(0) ≥ β ∫ v dμ ≥ β v(0)`. -/
theorem nonneg [IsProbabilityMeasure μ] (w : Icc (0 : ℝ) wbar) : 0 ≤ v w := by
  have hmin : ∀ z, v (w0 h.wbar_pos.le) ≤ v z := fun z => hs.mono z.2.1
  have hA : v (w0 h.wbar_pos.le) ≤ ∫ z, v z ∂μ := by
    have := integral_mono (integrable_const (v (w0 h.wbar_pos.le))) hs.integrable hmin
    simpa using this
  have h0 : β * ∫ z, v z ∂μ ≤ v (w0 h.wbar_pos.le) := by
    rw [hs.fe (w0 h.wbar_pos.le)]; exact le_max_right _ _
  have : 0 ≤ v (w0 h.wbar_pos.le) := by
    nlinarith [h.β_pos, h.β_lt, mul_le_mul_of_nonneg_left hA h.β_pos.le]
  exact this.trans (hmin w)

/-- `v(0) = A`. -/
theorem v_zero [IsProbabilityMeasure μ] : v (w0 h.wbar_pos.le) = β * ∫ z, v z ∂μ := by
  have hA : 0 ≤ β * ∫ z, v z ∂μ :=
    mul_nonneg h.β_pos.le (integral_nonneg fun z => hs.nonneg z)
  have he := hs.fe (w0 h.wbar_pos.le)
  have hU0 : U (w0 h.wbar_pos.le).1 = 0 := h.U_zero
  rw [hU0] at he
  rcases le_total (β * ((1 - θ) * v (w0 h.wbar_pos.le) + θ * v (w0 h.wbar_pos.le)))
    (β * ∫ z, v z ∂μ) with hle | hle
  · rw [he, zero_add, max_eq_right hle]
  · rw [zero_add, max_eq_left hle] at he
    have : v (w0 h.wbar_pos.le) = 0 := by nlinarith [h.β_lt]
    linarith

/-- The value of working at `w`: `U(w) + β[(1 − θ)v(w) + θA]`. -/
theorem fe' [IsProbabilityMeasure μ] (w : Icc (0 : ℝ) wbar) :
    v w = max (U w.1 + β * ((1 - θ) * v w + θ * (β * ∫ z, v z ∂μ))) (β * ∫ z, v z ∂μ) := by
  have := hs.fe w
  rw [hs.v_zero] at this
  exact this

/-- `A > 0` when `μ` puts mass on positive wages. -/
theorem A_pos [IsProbabilityMeasure μ] (hμ : 0 < μ {w | 0 < w.1}) : 0 < β * ∫ z, v z ∂μ := by
  refine mul_pos h.β_pos ?_
  have hpos : ∀ w : Icc (0 : ℝ) wbar, 0 < w.1 → 0 < v w := fun w hw => by
    have hUw : 0 < U w.1 := by
      have := h.U_mono (left_mem_Icc.2 h.wbar_pos.le) w.2 hw
      rwa [h.U_zero] at this
    have := le_max_left _ _ |>.trans_eq (hs.fe w).symm
    have h1 := hs.nonneg w
    have h2 := hs.nonneg (w0 h.wbar_pos.le)
    have : 0 ≤ β * ((1 - θ) * v w + θ * v (w0 h.wbar_pos.le)) :=
      mul_nonneg h.β_pos.le (add_nonneg (mul_nonneg (by linarith [h.θ_le]) h1)
        (mul_nonneg h.θ_nonneg h2))
    linarith
  rw [integral_pos_iff_support_of_nonneg (fun z => hs.nonneg z) hs.integrable]
  refine hμ.trans_le (measure_mono fun w hw => ?_)
  exact (hpos w hw).ne'

/-- The value of working is strictly increasing in `w`. -/
theorem work_strictMono [IsProbabilityMeasure μ] :
    StrictMono fun w : Icc (0 : ℝ) wbar =>
      U w.1 + β * ((1 - θ) * v w + θ * (β * ∫ z, v z ∂μ)) := by
  intro w w' hww'
  have hU := h.U_mono w.2 w'.2 hww'
  have hv := hs.mono hww'.le
  have : 0 ≤ β * (1 - θ) := mul_nonneg h.β_pos.le (by linarith [h.θ_le])
  nlinarith

end SearchSol

/-- **Exercise 10.7d.** There is a unique `w*` with `v(w*) = U(w*) + β[(1 − θ)v(w*) + θA] = A`;
it satisfies `U(w*) = (1 − β)A` (3), and `w* > 0`. -/
theorem ex_10_7d [IsProbabilityMeasure μ] {h : SearchHyp U θ β wbar} {v : Icc (0 : ℝ) wbar → ℝ}
    (hs : SearchSol h μ v) (hμ : 0 < μ {w | 0 < w.1}) :
    (∃! ws : Icc (0 : ℝ) wbar, v ws = U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) ∧
      v ws = β * ∫ z, v z ∂μ) ∧
    ∀ ws : Icc (0 : ℝ) wbar, U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) =
        β * ∫ z, v z ∂μ →
      U ws.1 = (1 - β) * (β * ∫ z, v z ∂μ) ∧ 0 < ws.1 := by
  set A := β * ∫ z, v z ∂μ
  set Vw : Icc (0 : ℝ) wbar → ℝ := fun w => U w.1 + β * ((1 - θ) * v w + θ * A)
  have hA := hs.A_pos hμ
  have hmono : StrictMono Vw := hs.work_strictMono
  have hfe : ∀ w, v w = max (Vw w) A := hs.fe'
  -- `Vw(0) < A ≤ Vw(w̄)`
  have hlow : Vw (w0 h.wbar_pos.le) < A := by
    have hv0 := hs.v_zero
    have hU0 : U (w0 h.wbar_pos.le).1 = 0 := h.U_zero
    change U (w0 h.wbar_pos.le).1 + β * ((1 - θ) * v (w0 h.wbar_pos.le) + θ * A) < A
    rw [hU0, hv0]
    nlinarith [h.β_lt]
  set wt : Icc (0 : ℝ) wbar := ⟨wbar, h.wbar_pos.le, le_rfl⟩
  have hhigh : A ≤ Vw wt := by
    by_contra hlt
    have hconst : ∀ w, v w = A := fun w => by
      rw [hfe w, max_eq_right ((hmono.monotone (show w ≤ wt from w.2.2)).trans (not_le.1 hlt).le)]
    have hint : ∫ z, v z ∂μ = A := by
      simp_rw [hconst]
      simp
    have : A = β * A := by
      change β * ∫ z, v z ∂μ = β * A
      rw [hint]
    nlinarith [h.β_lt]
  -- the intermediate value theorem along `[0, w̄]`
  have hcont : Continuous Vw :=
    (h.U_cont.comp_continuous continuous_subtype_val fun w => w.2).add
      (continuous_const.mul ((continuous_const.mul hs.cont).add continuous_const))
  have hivt := intermediate_value_Icc h.wbar_pos.le
    (hcont.comp (continuous_projIcc (h := h.wbar_pos.le))).continuousOn
  simp only [Function.comp_apply, projIcc_left, projIcc_right] at hivt
  obtain ⟨x, -, hx⟩ := hivt ⟨(hlow.trans_eq (by rfl)).le, hhigh⟩
  set ws := projIcc 0 wbar h.wbar_pos.le x
  have hx' : Vw ws = A := hx
  have hvws : v ws = A := by rw [hfe, hx', max_self]
  have hprop : ∀ w : Icc (0 : ℝ) wbar, Vw w = A →
      U w.1 = (1 - β) * A ∧ 0 < w.1 := fun w hw => by
    have hvw : v w = A := by rw [hfe, hw, max_self]
    have hU : U w.1 = (1 - β) * A := by
      change U w.1 + β * ((1 - θ) * v w + θ * A) = A at hw
      rw [hvw] at hw
      linarith
    refine ⟨hU, lt_of_le_of_ne w.2.1 fun h0 => ?_⟩
    have : U w.1 = 0 := by rw [← h0]; exact h.U_zero
    nlinarith [h.β_lt]
  refine ⟨⟨ws, ⟨hvws.trans hx'.symm, hvws⟩, fun w hw => ?_⟩, hprop⟩
  have hVw : Vw w = A := hw.1.symm.trans hw.2
  exact hmono.injective (hVw.trans hx'.symm)

/-- **Exercise 10.7e.** With `Vw(w*) = A`, `v(w) = A` below `w*` and
`v(w) = [U(w) + βθA]/[1 − β(1 − θ)]` from `w*` on (4). -/
theorem ex_10_7e [IsProbabilityMeasure μ] {h : SearchHyp U θ β wbar} {v : Icc (0 : ℝ) wbar → ℝ}
    (hs : SearchSol h μ v) {ws : Icc (0 : ℝ) wbar}
    (hws : U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) = β * ∫ z, v z ∂μ)
    (w : Icc (0 : ℝ) wbar) :
    (w < ws → v w = β * ∫ z, v z ∂μ) ∧
      (ws ≤ w → v w = (U w.1 + β * θ * (β * ∫ z, v z ∂μ)) / (1 - β * (1 - θ))) := by
  set A := β * ∫ z, v z ∂μ
  have hmono := hs.work_strictMono
  have hfe := hs.fe' w
  refine ⟨fun hlt => ?_, fun hle => ?_⟩
  · rw [hfe, max_eq_right ((hmono hlt).le.trans_eq hws)]
  · have hge := (hmono.monotone hle)
    rw [hws] at hge
    rw [max_eq_left hge] at hfe
    have hD : 0 < 1 - β * (1 - θ) := by nlinarith [h.β_lt, h.θ_nonneg, h.β_pos]
    rw [eq_div_iff hD.ne']
    linarith

/-- `F(w) = μ([0, w))`. -/
noncomputable def cdfF (μ : Measure (Icc (0 : ℝ) wbar)) (w : Icc (0 : ℝ) wbar) : ℝ :=
  (μ (Iio w)).toReal

theorem cdfF_nonneg (w : Icc (0 : ℝ) wbar) : 0 ≤ cdfF μ w := ENNReal.toReal_nonneg

theorem cdfF_le_one [IsProbabilityMeasure μ] (w : Icc (0 : ℝ) wbar) : cdfF μ w ≤ 1 := by
  unfold cdfF
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

/-- **Exercise 10.7f** (5): `(1 − β)A = β/[1 + βθ − βF(w*)] ∫_{w ≥ w*} U dμ`. -/
theorem ex_10_7f [IsProbabilityMeasure μ] {h : SearchHyp U θ β wbar} {v : Icc (0 : ℝ) wbar → ℝ}
    (hs : SearchSol h μ v) {ws : Icc (0 : ℝ) wbar}
    (hws : U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) = β * ∫ z, v z ∂μ) :
    (1 - β) * (β * ∫ z, v z ∂μ) =
      β / (1 + β * θ - β * cdfF μ ws) * ∫ w in Ici ws, U w.1 ∂μ := by
  set A := β * ∫ z, v z ∂μ
  set Fs := cdfF μ ws
  have hD : 0 < 1 - β * (1 - θ) := by nlinarith [h.β_lt, h.θ_nonneg, h.β_pos]
  have hF1 := cdfF_le_one (μ := μ) ws
  have hF0 := cdfF_nonneg (μ := μ) ws
  have hE : 0 < 1 + β * θ - β * Fs := by nlinarith [h.β_lt, h.θ_nonneg, h.β_pos]
  -- split `∫ v` at `w*`
  have hsplit : ∫ z, v z ∂μ = ∫ z in Iio ws, v z ∂μ + ∫ z in Ici ws, v z ∂μ := by
    rw [← integral_add_compl (measurableSet_Iio (a := ws)) hs.integrable, compl_Iio]
  have hlow : ∫ z in Iio ws, v z ∂μ = Fs * A := by
    rw [setIntegral_congr_fun measurableSet_Iio fun w hw => (ex_10_7e hs hws w).1 hw,
      setIntegral_const, smul_eq_mul]
    rfl
  have hμc : (μ (Ici ws)).toReal = 1 - Fs := by
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, ENNReal.toReal_sub_of_le
      prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
    rfl
  have hhigh : ∫ z in Ici ws, v z ∂μ =
      (∫ z in Ici ws, U z.1 ∂μ + β * θ * A * (1 - Fs)) / (1 - β * (1 - θ)) := by
    rw [setIntegral_congr_fun measurableSet_Ici fun w hw => (ex_10_7e hs hws w).2 hw,
      integral_div, integral_add (h.integrable_U μ).integrableOn (integrable_const _),
      setIntegral_const, smul_eq_mul, measureReal_def, hμc]
    ring
  have hAeq : A = β * (Fs * A + (∫ z in Ici ws, U z.1 ∂μ + β * θ * A * (1 - Fs)) /
      (1 - β * (1 - θ))) := by
    change β * ∫ z, v z ∂μ = _
    rw [hsplit, hlow, hhigh]
  rw [div_mul_eq_mul_div, eq_div_iff hE.ne']
  field_simp at hAeq
  linear_combination hAeq

/-- `Ψ(w) = [1 + βθ − βF(w)]U(w) − β ∫_{w′ ≥ w} U dμ`: equation (6) says `Ψ(w*) = 0`. -/
noncomputable def resΨ (μ : Measure (Icc (0 : ℝ) wbar)) (U : ℝ → ℝ) (β θ : ℝ)
    (w : Icc (0 : ℝ) wbar) : ℝ :=
  (1 + β * θ - β * cdfF μ w) * U w.1 - β * ∫ w' in Ici w, U w'.1 ∂μ

/-- **Exercise 10.7g** (existence): `w*` satisfies (6). -/
theorem ex_10_7g [IsProbabilityMeasure μ] {h : SearchHyp U θ β wbar} {v : Icc (0 : ℝ) wbar → ℝ}
    (hs : SearchSol h μ v) {ws : Icc (0 : ℝ) wbar}
    (hws : U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) = β * ∫ z, v z ∂μ) :
    resΨ μ U β θ ws = 0 := by
  have h5 := ex_10_7f hs hws
  have hvws : v ws = β * ∫ z, v z ∂μ := by rw [hs.fe', hws, max_self]
  have h3 : U ws.1 = (1 - β) * (β * ∫ z, v z ∂μ) := by
    rw [hvws] at hws; linarith
  have hF1 := cdfF_le_one (μ := μ) ws
  have hE : 0 < 1 + β * θ - β * cdfF μ ws := by nlinarith [h.β_lt, h.θ_nonneg, h.β_pos]
  unfold resΨ
  rw [h3, h5, div_mul_eq_mul_div, mul_div_cancel₀ _ hE.ne']
  ring

/-- **Exercise 10.7g** (uniqueness): `Ψ` is strictly increasing, so (6) has at most one root. -/
theorem resΨ_strictMono [IsProbabilityMeasure μ] (h : SearchHyp U θ β wbar) :
    StrictMono (resΨ μ U β θ) := by
  have hUi : Integrable (fun w : Icc (0 : ℝ) wbar => U w.1) μ :=
    (h.U_cont.comp_continuous continuous_subtype_val fun w => w.2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  intro w₁ w₂ h12
  set m := (μ (Ico w₁ w₂)).toReal
  have hF : cdfF μ w₂ = cdfF μ w₁ + m := by
    unfold cdfF
    have hd : Disjoint (Iio w₁) (Ico w₁ w₂) := Set.disjoint_left.2 fun x hx hx' =>
      not_le.2 (show x < w₁ from hx) hx'.1
    rw [← Iio_union_Ico_eq_Iio h12.le, measure_union hd measurableSet_Ico,
      ENNReal.toReal_add (measure_ne_top _ _)
      (measure_ne_top _ _)]
  have hI : ∫ w in Ici w₁, U w.1 ∂μ = ∫ w in Ico w₁ w₂, U w.1 ∂μ + ∫ w in Ici w₂, U w.1 ∂μ := by
    have hd : Disjoint (Ico w₁ w₂) (Ici w₂) := Set.disjoint_left.2 fun x hx hx' =>
      not_le.2 hx.2 (show w₂ ≤ x from hx')
    rw [← Ico_union_Ici_eq_Ici h12.le, setIntegral_union hd measurableSet_Ici
      hUi.integrableOn hUi.integrableOn]
  have hIco : U w₁.1 * m ≤ ∫ w in Ico w₁ w₂, U w.1 ∂μ := by
    have := setIntegral_mono_on (s := Ico w₁ w₂) (integrableOn_const (measure_ne_top _ _))
      hUi.integrableOn measurableSet_Ico (fun w hw => h.U_mono.monotoneOn w₁.2 w.2 hw.1)
      (μ := μ) (f := fun _ => U w₁.1)
    rw [setIntegral_const, smul_eq_mul, measureReal_def] at this
    linarith
  have hU12 : U w₁.1 < U w₂.1 := h.U_mono w₁.2 w₂.2 h12
  have hF1 := cdfF_le_one (μ := μ) w₂
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hE : 0 < 1 + β * θ - β * cdfF μ w₂ := by nlinarith [h.β_lt, h.θ_nonneg, h.β_pos]
  unfold resΨ
  rw [hI, hF]
  rw [hF] at hE
  nlinarith [mul_le_mul_of_nonneg_left hIco h.β_pos.le, mul_pos hE (sub_pos.2 hU12)]

/-- **Exercise 10.7g.** `w*` is the unique solution of (6). -/
theorem ex_10_7g_unique [IsProbabilityMeasure μ] {h : SearchHyp U θ β wbar}
    {v : Icc (0 : ℝ) wbar → ℝ} (hs : SearchSol h μ v) {ws : Icc (0 : ℝ) wbar}
    (hws : U ws.1 + β * ((1 - θ) * v ws + θ * (β * ∫ z, v z ∂μ)) = β * ∫ z, v z ∂μ)
    (w : Icc (0 : ℝ) wbar) (hw : resΨ μ U β θ w = 0) : w = ws :=
  (resΨ_strictMono h).injective (hw.trans (ex_10_7g hs hws).symm)

/-- **Exercise 10.7h** (`θ`). The reservation wage falls when the job-loss probability rises: if
`w₁ > 0` solves (6) at `θ₁` and `w₂` solves it at `θ₂ > θ₁`, then `w₂ < w₁`. -/
theorem ex_10_7h_θ [IsProbabilityMeasure μ] {θ₁ θ₂ : ℝ} (h₂ : SearchHyp U θ₂ β wbar)
    {w₁ w₂ : Icc (0 : ℝ) wbar} (hw₁ : resΨ μ U β θ₁ w₁ = 0) (hw₂ : resΨ μ U β θ₂ w₂ = 0)
    (hθ : θ₁ < θ₂) (hpos : 0 < w₁.1) : w₂ < w₁ := by
  have hU : 0 < U w₁.1 := by
    have := h₂.U_mono (left_mem_Icc.2 h₂.wbar_pos.le) w₁.2 hpos
    rwa [h₂.U_zero] at this
  have hgt : resΨ μ U β θ₂ w₂ < resΨ μ U β θ₂ w₁ := by
    have : resΨ μ U β θ₂ w₁ = resΨ μ U β θ₁ w₁ + β * (θ₂ - θ₁) * U w₁.1 := by
      unfold resΨ; ring
    rw [this, hw₁, hw₂]
    have := mul_pos (mul_pos h₂.β_pos (sub_pos.2 hθ)) hU
    linarith
  exact (resΨ_strictMono h₂).lt_iff_lt.1 hgt

/-- **Exercise 10.7h** (`β`). For `θ < 1` the reservation wage rises with patience: if `w₁ > 0`
solves (6) at `β₁` and `w₂` solves it at `β₂ > β₁`, then `w₁ < w₂`. -/
theorem ex_10_7h_β [IsProbabilityMeasure μ] {β₁ β₂ : ℝ} (h₂ : SearchHyp U θ β₂ wbar)
    (hθ1 : θ < 1) {w₁ w₂ : Icc (0 : ℝ) wbar} (hw₁ : resΨ μ U β₁ θ w₁ = 0)
    (hw₂ : resΨ μ U β₂ θ w₂ = 0) (hβ : β₁ < β₂) (hpos : 0 < w₁.1) : w₁ < w₂ := by
  have hUi : Integrable (fun w : Icc (0 : ℝ) wbar => U w.1) μ :=
    (h₂.U_cont.comp_continuous continuous_subtype_val fun w => w.2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hU : 0 < U w₁.1 := by
    have := h₂.U_mono (left_mem_Icc.2 h₂.wbar_pos.le) w₁.2 hpos
    rwa [h₂.U_zero] at this
  -- `∫_{w ≥ w₁} U ≥ U(w₁)(1 − F(w₁))`
  have hμc : (μ (Ici w₁)).toReal = 1 - cdfF μ w₁ := by
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, ENNReal.toReal_sub_of_le
      prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
    rfl
  have hI : U w₁.1 * (1 - cdfF μ w₁) ≤ ∫ w in Ici w₁, U w.1 ∂μ := by
    have := setIntegral_mono_on (integrableOn_const (measure_ne_top _ _))
      hUi.integrableOn measurableSet_Ici (fun w hw => h₂.U_mono.monotoneOn w₁.2 w.2 hw)
      (μ := μ) (f := fun _ => U w₁.1)
    rw [setIntegral_const, smul_eq_mul, measureReal_def, hμc] at this
    linarith
  have hlt : resΨ μ U β₂ θ w₁ < resΨ μ U β₁ θ w₁ := by
    have e : resΨ μ U β₂ θ w₁ - resΨ μ U β₁ θ w₁ = (β₂ - β₁) *
        ((θ - cdfF μ w₁) * U w₁.1 - ∫ w in Ici w₁, U w.1 ∂μ) := by
      unfold resΨ; ring
    have : (θ - cdfF μ w₁) * U w₁.1 - ∫ w in Ici w₁, U w.1 ∂μ < 0 := by
      nlinarith
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 hβ) this]
  rw [hw₁, ← hw₂] at hlt
  exact (resΨ_strictMono h₂).lt_iff_lt.1 hlt

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The dynamics of the search model

SLP §10.8, pp. 308–310. Under the reservation-wage policy, wage offers follow the transition
function `P` on `W = [0, w̄]` (1a)–(1b): from an unacceptable offer `w < w*` the next offer is
drawn from `μ`; from an acceptable one `w ≥ w*` the wage is kept with probability `1 − θ` and
drops to `0` with probability `θ` (`searchP`). Let `λₜ = T*ᵗλ₀` (`searchLaw`) and
`Aᶜ = [0, w*)`, with `0 < w*` and `0 < θ < 1`.

* `searchP_adjoint`: `λₜ₊₁(B) = μ(B) λₜ(Aᶜ) + θ 1_B(0) λₜ(A) + (1 − θ) λₜ(A ∩ B)`.
* `tendsto_affine_rec`: if `|a| < 1` and `bₜ → b`, solutions of `xₜ₊₁ = a xₜ + bₜ` converge to
  `b/(1 − a)`; in particular the difference equation (2) is stable.
* **Exercise 10.8a** (`ex_10_8a`): `λₜ₊₁(Aᶜ) = θ + λₜ(Aᶜ)[μ(Aᶜ) − θ]` (2), and
  `λₜ(Aᶜ) → θ/(θ + μ(A))` (3).
* **Exercise 10.8b** (`ex_10_8b_zero`, `ex_10_8b`): for `C ⊆ Aᶜ`, the recursion and limit (4)
  if `0 ∈ C`, and (5) if `0 ∉ C`.
* **Exercise 10.8c** (`ex_10_8c`): for `C ⊆ A`, `λₜ(C) → [θ/(θ + μ(A))] μ(C)/θ` (6).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- **Stability.** If `|a| < 1` and `bₜ → b`, every solution of `xₜ₊₁ = a xₜ + bₜ` converges to
`b/(1 − a)`. -/
theorem tendsto_affine_rec {a : ℝ} (ha : |a| < 1) {b : ℕ → ℝ} {L : ℝ}
    (hb : Tendsto b atTop (𝓝 L)) {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = a * x t + b t) :
    Tendsto x atTop (𝓝 (L / (1 - a))) := by
  have ha1 : 0 < 1 - a := by linarith [le_abs_self a]
  set c := L / (1 - a)
  have hc : c = a * c + L := by
    simp only [c]; field_simp; ring
  set r := |a|
  have hr0 : 0 ≤ r := abs_nonneg a
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hr1 : 0 < 1 - r := by linarith
  have hε' : 0 < ε * (1 - r) / 2 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hb _ hε'
  have hstep : ∀ k, |x (N + k) - c| ≤ r ^ k * |x N - c| + ε / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have hb' := hN (N + k) (by omega)
      rw [Real.dist_eq] at hb'
      have e : x (N + (k + 1)) - c = a * (x (N + k) - c) + (b (N + k) - L) := by
        rw [show N + (k + 1) = N + k + 1 by ring, hx]
        linear_combination (-1 : ℝ) * hc
      rw [e]
      calc |a * (x (N + k) - c) + (b (N + k) - L)|
          ≤ r * |x (N + k) - c| + |b (N + k) - L| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ r * (r ^ k * |x N - c| + ε / 2) + ε * (1 - r) / 2 :=
            add_le_add (mul_le_mul_of_nonneg_left ih hr0) hb'.le
        _ = r ^ (k + 1) * |x N - c| + ε / 2 := by ring
  obtain ⟨K, hK⟩ := (tendsto_order.1 ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 ha).mul_const
    |x N - c|)).2 (ε / 2) (by rw [zero_mul]; linarith)
  |>.exists_forall_of_atTop
  refine ⟨N + K, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = N + k := ⟨t - N, by omega⟩
  rw [Real.dist_eq]
  have := hK k (by omega)
  linarith [hstep k]

variable {wbar θ : ℝ} (hw : 0 ≤ wbar)

/-- The wage after a job-loss shock: `0` if `d = 0`, the current wage if `d = 1`. -/
def stayMap (p : Icc (0 : ℝ) wbar × Two) : Icc (0 : ℝ) wbar :=
  if p.2 = two0 then w0 hw else p.1

theorem measurable_stayMap : Measurable (stayMap hw) := by
  classical
  exact Measurable.ite (measurable_snd (measurableSet_singleton two0)) measurable_const
    measurable_fst

/-- The transition function (1a)–(1b) of wage offers under the reservation-wage policy. -/
noncomputable def searchP (θ : ℝ) (μ : Measure (Icc (0 : ℝ) wbar)) (ws : Icc (0 : ℝ) wbar) :
    Kernel (Icc (0 : ℝ) wbar) (Icc (0 : ℝ) wbar) :=
  Kernel.piecewise (measurableSet_Iio (a := ws)) (Kernel.const _ μ)
    ((Kernel.deterministic id measurable_id ×ₖ Kernel.const _ (lossMeasure θ)).map (stayMap hw))

variable (μ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure μ] (ws : Icc (0 : ℝ) wbar)

omit [IsProbabilityMeasure μ] in
/-- (1b): from an acceptable offer, `P(w, B) = θ 1_B(0) + (1 − θ) 1_B(w)`. -/
theorem searchP_apply_ge (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {w : Icc (0 : ℝ) wbar} (hw' : ws ≤ w)
    {B : Set (Icc (0 : ℝ) wbar)} (hB : MeasurableSet B) :
    searchP hw θ μ ws w B = ENNReal.ofReal θ * B.indicator 1 (w0 hw) +
      ENNReal.ofReal (1 - θ) * B.indicator 1 w := by
  have : IsProbabilityMeasure (lossMeasure θ) := isProbabilityMeasure_lossMeasure hθ0 hθ1
  have hnot : w ∉ Iio ws := not_lt.2 hw'
  simp only [searchP, Kernel.piecewise_apply, hnot, ↓reduceIte]
  rw [Kernel.map_apply' _ (measurable_stayMap hw) _ hB, Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left ((measurable_stayMap hw) hB)]
  simp only [lossMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply, Measure.dirac_apply]
  by_cases h1 : w0 hw ∈ B <;> by_cases h2 : w ∈ B <;>
    simp [stayMap, h1, h2, Set.indicator, two0_ne_two1.symm]

omit [IsProbabilityMeasure μ] in
/-- `λₜ₊₁(B) = μ(B) λₜ(Aᶜ) + θ 1_B(0) λₜ(A) + (1 − θ) λₜ(A ∩ B)`. -/
theorem searchP_adjoint (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (lam : Measure (Icc (0 : ℝ) wbar))
    {B : Set (Icc (0 : ℝ) wbar)} (hB : MeasurableSet B) :
    adjointOp (searchP hw θ μ ws) lam B = μ B * lam (Iio ws) +
      ENNReal.ofReal θ * B.indicator 1 (w0 hw) * lam (Ici ws) +
        ENNReal.ofReal (1 - θ) * lam (B ∩ Ici ws) := by
  rw [adjointOp_apply _ _ hB, ← lintegral_add_compl _ (measurableSet_Iio (a := ws)), compl_Iio]
  rw [setLIntegral_congr_fun (g := fun _ => μ B) measurableSet_Iio fun w hw' => by
      simp only [searchP, Kernel.piecewise_apply, hw', ↓reduceIte, Kernel.const_apply],
    setLIntegral_congr_fun measurableSet_Ici fun w hw' => searchP_apply_ge hw μ ws hθ0 hθ1 hw' hB,
    setLIntegral_const, lintegral_add_left measurable_const, setLIntegral_const,
    lintegral_const_mul _ (measurable_one.indicator hB), lintegral_indicator_one hB,
    Measure.restrict_apply hB]
  ring

/-- The marginal laws `λₜ = T*ᵗλ₀` of the wage offer. -/
noncomputable def searchLaw (θ : ℝ) (lam₀ : Measure (Icc (0 : ℝ) wbar)) (t : ℕ) :
    Measure (Icc (0 : ℝ) wbar) :=
  (adjointOp (searchP hw θ μ ws))^[t] lam₀

omit [IsProbabilityMeasure μ] in
theorem searchLaw_succ (θ : ℝ) (lam₀ : Measure (Icc (0 : ℝ) wbar)) (t : ℕ) :
    searchLaw hw μ ws θ lam₀ (t + 1) = adjointOp (searchP hw θ μ ws) (searchLaw hw μ ws θ lam₀ t) :=
  Function.iterate_succ_apply' _ _ _

/-- Each `λₜ` is a probability measure. -/
theorem searchLaw_prob (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (lam₀ : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure lam₀] (t : ℕ) : IsProbabilityMeasure (searchLaw hw μ ws θ lam₀ t) := by
  induction t with
  | zero => exact ‹_›
  | succ t ih =>
    refine ⟨?_⟩
    rw [searchLaw_succ, searchP_adjoint hw μ ws hθ0 hθ1 _ MeasurableSet.univ]
    simp only [measure_univ, one_mul, Set.indicator_univ, Pi.one_apply, mul_one, univ_inter]
    have h1 : ENNReal.ofReal θ + ENNReal.ofReal (1 - θ) = 1 := by
      rw [← ENNReal.ofReal_add hθ0 (by linarith)]; simp
    have hd : Disjoint (Iio ws) (Ici ws) := Set.disjoint_left.2 fun x hx hx' =>
      not_le.2 (show x < ws from hx) (show ws ≤ x from hx')
    calc searchLaw hw μ ws θ lam₀ t (Iio ws) + ENNReal.ofReal θ *
          searchLaw hw μ ws θ lam₀ t (Ici ws) +
          ENNReal.ofReal (1 - θ) * searchLaw hw μ ws θ lam₀ t (Ici ws)
        = searchLaw hw μ ws θ lam₀ t (Iio ws) + (ENNReal.ofReal θ + ENNReal.ofReal (1 - θ)) *
          searchLaw hw μ ws θ lam₀ t (Ici ws) := by ring
      _ = 1 := by rw [h1, one_mul, ← measure_union hd measurableSet_Ici, Iio_union_Ici,
          measure_univ]

/-- In real numbers: with `x = λ(Aᶜ)`,
`λ′(B) = μ(B) x + θ 1_B(0) (1 − x) + (1 − θ) λ(B ∩ A)`. -/
theorem searchP_adjoint_real (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (lam : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure lam] {B : Set (Icc (0 : ℝ) wbar)} (hB : MeasurableSet B) :
    (adjointOp (searchP hw θ μ ws) lam B).toReal = (μ B).toReal * (lam (Iio ws)).toReal +
      θ * (B.indicator 1 (w0 hw) : ℝ) * (1 - (lam (Iio ws)).toReal) +
        (1 - θ) * (lam (B ∩ Ici ws)).toReal := by
  have hIci : (lam (Ici ws)).toReal = 1 - (lam (Iio ws)).toReal := by
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, ENNReal.toReal_sub_of_le
      prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have hind : ((B.indicator 1 (w0 hw) : ℝ≥0∞)).toReal = (B.indicator 1 (w0 hw) : ℝ) := by
    by_cases h : w0 hw ∈ B <;> simp [h]
  have hi : B.indicator 1 (w0 hw) ≠ ∞ := by by_cases h : w0 hw ∈ B <;> simp [h]
  have h1 : μ B * lam (Iio ws) ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have h2 : ENNReal.ofReal θ * B.indicator 1 (w0 hw) * lam (Ici ws) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hi) (measure_ne_top _ _)
  have h3 : ENNReal.ofReal (1 - θ) * lam (B ∩ Ici ws) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [searchP_adjoint hw μ ws hθ0 hθ1 lam hB, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨h1, h2⟩)
    h3, ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ0,
    ENNReal.toReal_ofReal (by linarith), hind, hIci]

/-- **Exercise 10.8a.** `λₜ₊₁(Aᶜ) = θ + λₜ(Aᶜ)[μ(Aᶜ) − θ]` (2); since `|μ(Aᶜ) − θ| < 1` the
equation is stable, and `λₜ(Aᶜ) → θ/(θ + μ(A))` (3). -/
theorem ex_10_8a (hθ0 : 0 < θ) (hθ1 : θ < 1) (hws : 0 < ws.1) (lam₀ : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure lam₀] :
    (∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) (Iio ws)).toReal =
      θ + (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * ((μ (Iio ws)).toReal - θ)) ∧
    |(μ (Iio ws)).toReal - θ| < 1 ∧
    Tendsto (fun t => (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal) atTop
      (𝓝 (θ / (θ + (μ (Ici ws)).toReal))) := by
  have h0 : w0 hw ∈ Iio ws := show w0 hw < ws from hws
  have hrec : ∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) (Iio ws)).toReal =
      θ + (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * ((μ (Iio ws)).toReal - θ) := fun t => by
    have := searchLaw_prob hw μ ws hθ0.le hθ1.le lam₀ t
    rw [searchLaw_succ, searchP_adjoint_real hw μ ws hθ0.le hθ1.le _ measurableSet_Iio,
      Set.indicator_of_mem h0, Iio_inter_Ici, Ico_self, measure_empty]
    simp only [Pi.one_apply, ENNReal.toReal_zero]
    ring
  have hμc : (μ (Ici ws)).toReal = 1 - (μ (Iio ws)).toReal := by
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, ENNReal.toReal_sub_of_le
      prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have hμ0 : 0 ≤ (μ (Iio ws)).toReal := ENNReal.toReal_nonneg
  have hμ1 : (μ (Iio ws)).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have ha : |(μ (Iio ws)).toReal - θ| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
  refine ⟨hrec, ha, ?_⟩
  have := tendsto_affine_rec ha (tendsto_const_nhds (x := θ))
    (x := fun t => (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal) fun t => by
      rw [hrec]; ring
  convert this using 2
  rw [hμc]; ring

/-- The limit `L = θ/(θ + μ(A))` of `λₜ(Aᶜ)`, and its recursion. -/
theorem searchLaw_Iio_tendsto (hθ0 : 0 < θ) (hθ1 : θ < 1) (hws : 0 < ws.1)
    (lam₀ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure lam₀] :
    Tendsto (fun t => (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal) atTop
      (𝓝 (θ / (θ + (μ (Ici ws)).toReal))) :=
  (ex_10_8a hw μ ws hθ0 hθ1 hws lam₀).2.2

/-- **Exercise 10.8b** (`0 ∈ C`). For measurable `C ⊆ Aᶜ` with `0 ∈ C`,
`λₜ₊₁(C) = θ + λₜ(Aᶜ)[μ(C) − θ]`, and
`λₜ(C) → [θ/(θ + μ(A))] μ(C) + [μ(A)/(θ + μ(A))] θ` (4). -/
theorem ex_10_8b_zero (hθ0 : 0 < θ) (hθ1 : θ < 1) (hws : 0 < ws.1)
    (lam₀ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure lam₀] {C : Set (Icc (0 : ℝ) wbar)}
    (hC : MeasurableSet C) (hCA : C ⊆ Iio ws) (h0 : w0 hw ∈ C) :
    (∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      θ + (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * ((μ C).toReal - θ)) ∧
    Tendsto (fun t => (searchLaw hw μ ws θ lam₀ t C).toReal) atTop
      (𝓝 (θ / (θ + (μ (Ici ws)).toReal) * (μ C).toReal +
        (μ (Ici ws)).toReal / (θ + (μ (Ici ws)).toReal) * θ)) := by
  have hdisj : C ∩ Ici ws = ∅ := Set.eq_empty_of_forall_notMem fun w hw' =>
    not_le.2 (show w < ws from hCA hw'.1) (show ws ≤ w from hw'.2)
  have hrec : ∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      θ + (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * ((μ C).toReal - θ) := fun t => by
    have := searchLaw_prob hw μ ws hθ0.le hθ1.le lam₀ t
    rw [searchLaw_succ, searchP_adjoint_real hw μ ws hθ0.le hθ1.le _ hC, Set.indicator_of_mem h0,
      hdisj, measure_empty]
    simp only [Pi.one_apply, ENNReal.toReal_zero]
    ring
  refine ⟨hrec, ?_⟩
  have hL := searchLaw_Iio_tendsto hw μ ws hθ0 hθ1 hws lam₀
  have hpos : 0 < θ + (μ (Ici ws)).toReal := by
    have := ENNReal.toReal_nonneg (a := μ (Ici ws)); linarith
  have := (tendsto_const_nhds (x := θ)).add (hL.mul_const ((μ C).toReal - θ))
  rw [← tendsto_add_atTop_iff_nat 1]
  convert this using 1
  · funext t; exact hrec t
  · congr 1; field_simp; ring

/-- **Exercise 10.8b** (`0 ∉ C`). For measurable `C ⊆ Aᶜ` with `0 ∉ C`,
`λₜ₊₁(C) = λₜ(Aᶜ) μ(C)`, and `λₜ(C) → [θ/(θ + μ(A))] μ(C)` (5). -/
theorem ex_10_8b (hθ0 : 0 < θ) (hθ1 : θ < 1) (hws : 0 < ws.1)
    (lam₀ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure lam₀] {C : Set (Icc (0 : ℝ) wbar)}
    (hC : MeasurableSet C) (hCA : C ⊆ Iio ws) (h0 : w0 hw ∉ C) :
    (∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * (μ C).toReal) ∧
    Tendsto (fun t => (searchLaw hw μ ws θ lam₀ t C).toReal) atTop
      (𝓝 (θ / (θ + (μ (Ici ws)).toReal) * (μ C).toReal)) := by
  have hdisj : C ∩ Ici ws = ∅ := Set.eq_empty_of_forall_notMem fun w hw' =>
    not_le.2 (show w < ws from hCA hw'.1) (show ws ≤ w from hw'.2)
  have hrec : ∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * (μ C).toReal := fun t => by
    have := searchLaw_prob hw μ ws hθ0.le hθ1.le lam₀ t
    rw [searchLaw_succ, searchP_adjoint_real hw μ ws hθ0.le hθ1.le _ hC, Set.indicator_of_notMem h0,
      hdisj, measure_empty]
    simp only [ENNReal.toReal_zero]
    ring
  refine ⟨hrec, ?_⟩
  have hL := searchLaw_Iio_tendsto hw μ ws hθ0 hθ1 hws lam₀
  rw [← tendsto_add_atTop_iff_nat 1]
  convert hL.mul_const (μ C).toReal using 1
  funext t; exact hrec t

/-- **Exercise 10.8c.** For measurable `C ⊆ A`, `λₜ₊₁(C) = λₜ(Aᶜ) μ(C) + λₜ(C)(1 − θ)`, and
`λₜ(C) → [θ/(θ + μ(A))] μ(C)/θ` (6). -/
theorem ex_10_8c (hθ0 : 0 < θ) (hθ1 : θ < 1) (hws : 0 < ws.1)
    (lam₀ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure lam₀] {C : Set (Icc (0 : ℝ) wbar)}
    (hC : MeasurableSet C) (hCA : C ⊆ Ici ws) :
    (∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * (μ C).toReal +
        (searchLaw hw μ ws θ lam₀ t C).toReal * (1 - θ)) ∧
    Tendsto (fun t => (searchLaw hw μ ws θ lam₀ t C).toReal) atTop
      (𝓝 (θ / (θ + (μ (Ici ws)).toReal) * ((μ C).toReal / θ))) := by
  have h0 : w0 hw ∉ C := fun h => not_le.2 (show w0 hw < ws from hws) (hCA h)
  have hrec : ∀ t, (searchLaw hw μ ws θ lam₀ (t + 1) C).toReal =
      (searchLaw hw μ ws θ lam₀ t (Iio ws)).toReal * (μ C).toReal +
        (searchLaw hw μ ws θ lam₀ t C).toReal * (1 - θ) := fun t => by
    have := searchLaw_prob hw μ ws hθ0.le hθ1.le lam₀ t
    rw [searchLaw_succ, searchP_adjoint_real hw μ ws hθ0.le hθ1.le _ hC, Set.indicator_of_notMem h0,
      inter_eq_left.2 hCA]
    ring
  refine ⟨hrec, ?_⟩
  have hL := (searchLaw_Iio_tendsto hw μ ws hθ0 hθ1 hws lam₀).mul_const (μ C).toReal
  have ha : |1 - θ| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
  have := tendsto_affine_rec ha hL (x := fun t => (searchLaw hw μ ws θ lam₀ t C).toReal)
    fun t => by rw [hrec]; ring
  convert this using 2
  rw [show (1 : ℝ) - (1 - θ) = θ by ring]
  field_simp

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A model of job matching

SLP §10.10, pp. 311–314, Exercise 10.10d–h. A worker who has had `k` successes in `n` periods
on a task expects to succeed with probability `π(n, k)`. Staying earns `π(n, k)` and moves the
state to `(n + 1, k + 1)` or `(n + 1, k)`; a new task does the same from `(0, 0)`:
`v(n, k) = max {π(n, k) + β[π(n, k)v(n + 1, k + 1) + (1 − π(n, k))v(n + 1, k)], v-stay(0, 0)}` (1),
on the triangular array `D = {(n, k) : k ≤ n}` (`triD`).

* **Exercise 10.10f** (`ex_10_10f`): for any `π` with values in `[0, 1]`, (1) has a unique bounded
  solution, and it lies in `S = {f : D → [0, 1/(1 − β)]}` (Blackwell's conditions).
* **Exercise 10.10g** (`ex_10_10g`): if `π` has the properties of part (d) (`PiProps`),
  `v(n, k)` is nonincreasing in `n`, nondecreasing in `k`, and nondecreasing along
  `(n, k) ↦ (n + 1, k + 1)`. If `π` is uniformly near `p` on the windows
  `{(n + j, kₙ + i) : i ≤ j ≤ J}` for large `n`, then `v(n, kₙ) → max{p/(1 − β), v(0, 0)}`
  (`ex_10_10g_limit`); the beta-prior `π` satisfies this when `kₙ/n → p`
  (`betaπ_window`, `ex_10_10g_beta` in `BetaPosterior`).
* **Exercise 10.10h** (`ex_10_10h`): staying when indifferent, the optimal policy is
  `g(n, k) = 1` iff `k ≥ jₙ`, with `j₁ = 1` and `jₙ₊₁ ≥ jₙ`.
* Exercise 10.10a–e, for the beta prior, are in `BetaPosterior`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open Set Filter Topology BoundedContinuousFunction

/-- The triangular array `D = {(n, k) : k ≤ n}`. -/
def triD : Set (ℕ × ℕ) := {p | p.2 ≤ p.1}

/-- A success: `(n, k) ↦ (n + 1, k + 1)`. -/
def triS (p : triD) : triD := ⟨(p.1.1 + 1, p.1.2 + 1), Nat.succ_le_succ p.2⟩

/-- A failure: `(n, k) ↦ (n + 1, k)`. -/
def triF (p : triD) : triD := ⟨(p.1.1 + 1, p.1.2), Nat.le_succ_of_le p.2⟩

/-- One more success at the same date: `(n, k) ↦ (n, k + 1)`, for `k < n`. -/
def triK (p : triD) (h : p.1.2 + 1 ≤ p.1.1) : triD := ⟨(p.1.1, p.1.2 + 1), h⟩

/-- The state of a new task. -/
def tri00 : triD := ⟨(0, 0), show (0 : ℕ) ≤ 0 from le_rfl⟩

/-- The point `(n, k)` of `D`. -/
def triMk (n k : ℕ) (h : k ≤ n) : triD := ⟨(n, k), h⟩

variable (π : ℕ → ℕ → ℝ) (β : ℝ)

/-- The value of staying on the task: `π + β[π f(n + 1, k + 1) + (1 − π) f(n + 1, k)]`. -/
def stayV (f : triD → ℝ) (p : triD) : ℝ :=
  π p.1.1 p.1.2 + β * (π p.1.1 p.1.2 * f (triS p) + (1 - π p.1.1 p.1.2) * f (triF p))

/-- The return of staying, `q + β[q a + (1 − q) b]`, is nondecreasing in the continuation values,
and in the success probability `q` when `a ≥ b`; strictly so in `q`. -/
theorem stay_le {β : ℝ} (hβ : 0 ≤ β) {q q' a b a' b' : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hqq' : q ≤ q') (hba : b' ≤ a') (ha : a ≤ a') (hb : b ≤ b') :
    q + β * (q * a + (1 - q) * b) ≤ q' + β * (q' * a' + (1 - q') * b') := by
  have h1 : q * a + (1 - q) * b ≤ q * a' + (1 - q) * b' := by
    nlinarith [mul_le_mul_of_nonneg_left ha hq, mul_le_mul_of_nonneg_left hb (sub_nonneg.2 hq1)]
  have h2 : 0 ≤ (q' - q) * (1 + β * (a' - b')) :=
    mul_nonneg (by linarith) (by nlinarith [mul_nonneg hβ (sub_nonneg.2 hba)])
  nlinarith [mul_le_mul_of_nonneg_left h1 hβ]

theorem stay_lt {β : ℝ} (hβ : 0 ≤ β) {q q' a b a' b' : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hqq' : q < q') (hba : b' ≤ a') (ha : a ≤ a') (hb : b ≤ b') :
    q + β * (q * a + (1 - q) * b) < q' + β * (q' * a' + (1 - q') * b') := by
  have h1 : q * a + (1 - q) * b ≤ q * a' + (1 - q) * b' := by
    nlinarith [mul_le_mul_of_nonneg_left ha hq, mul_le_mul_of_nonneg_left hb (sub_nonneg.2 hq1)]
  have h2 : 0 < (q' - q) * (1 + β * (a' - b')) :=
    mul_pos (by linarith) (by nlinarith [mul_nonneg hβ (sub_nonneg.2 hba)])
  nlinarith [mul_le_mul_of_nonneg_left h1 hβ]

variable {π β}

theorem abs_stayV_le (hπ : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ : 0 ≤ β) (f : triD →ᵇ ℝ)
    (p : triD) : |stayV π β f p| ≤ 1 + β * ‖f‖ := by
  obtain ⟨h0, h1⟩ := hπ p.1.1 p.1.2 p.2
  have hS := (abs_le.1 ((Real.norm_eq_abs _).symm.le.trans (f.norm_coe_le_norm (triS p))))
  have hF := (abs_le.1 ((Real.norm_eq_abs _).symm.le.trans (f.norm_coe_le_norm (triF p))))
  rw [abs_le]
  unfold stayV
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hS.1 h0, mul_le_mul_of_nonneg_left hS.2 h0,
    mul_le_mul_of_nonneg_left hF.1 (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hF.2
      (sub_nonneg.2 h1), norm_nonneg f]

/-- The operator `T` of the functional equation (1). -/
noncomputable def jobT (hπ : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ : 0 ≤ β) (f : triD →ᵇ ℝ) :
    triD →ᵇ ℝ :=
  ofNormedAddCommGroupDiscrete (fun p => max (stayV π β f p) (stayV π β f tri00)) (1 + β * ‖f‖)
    fun p => by
      rw [Real.norm_eq_abs]
      exact abs_max_le_max_abs_abs.trans (max_le (abs_stayV_le hπ hβ f p)
        (abs_stayV_le hπ hβ f tri00))

theorem jobT_apply (hπ : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ : 0 ≤ β) (f : triD →ᵇ ℝ)
    (p : triD) :
    jobT hπ hβ f p = max (stayV π β f p) (stayV π β f tri00) := rfl

theorem jobT_contraction (hπ : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsContraction (jobT hπ hβ0.le) β := by
  have hmono : ∀ (f g : triD →ᵇ ℝ) (p : triD), f ≤ g → stayV π β f p ≤ stayV π β g p :=
    fun f g p hfg => by
      obtain ⟨h0, h1⟩ := hπ p.1.1 p.1.2 p.2
      have hS : f (triS p) ≤ g (triS p) := hfg (triS p)
      have hF : f (triF p) ≤ g (triF p) := hfg (triF p)
      have hmix : π p.1.1 p.1.2 * f (triS p) + (1 - π p.1.1 p.1.2) * f (triF p) ≤
          π p.1.1 p.1.2 * g (triS p) + (1 - π p.1.1 p.1.2) * g (triF p) := by
        nlinarith [mul_le_mul_of_nonneg_left hS h0, mul_le_mul_of_nonneg_left hF
          (sub_nonneg.2 h1)]
      unfold stayV
      nlinarith [mul_le_mul_of_nonneg_left hmix hβ0.le]
  refine ⟨hβ0, hβ1, blackwell hβ0.le (fun f g hfg p => ?_) (fun f a _ p => ?_)⟩
  · change jobT hπ hβ0.le f p ≤ jobT hπ hβ0.le g p
    rw [jobT_apply, jobT_apply]
    exact max_le_max (hmono f g p hfg) (hmono f g tri00 hfg)
  · have hs : ∀ q, stayV π β ((f + const triD a : triD →ᵇ ℝ) : triD → ℝ) q =
        stayV π β f q + β * a := fun q => by
      simp only [stayV, coe_add, Pi.add_apply, const_apply]; ring
    change jobT hπ hβ0.le (f + const triD a) p ≤ jobT hπ hβ0.le f p + β * a
    rw [jobT_apply, jobT_apply, hs, hs, max_add_add_right]

/-- **Exercise 10.10f.** For any `π` with values in `[0, 1]` and `0 < β < 1`, (1) has a unique
bounded solution `v`, and `0 ≤ v ≤ 1/(1 − β)`: `v` is the unique solution in `S`. -/
theorem ex_10_10f (hπ : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ v : triD →ᵇ ℝ, jobT hπ hβ0.le v = v ∧ (∀ w, jobT hπ hβ0.le w = w → w = v) ∧
      ∀ p, 0 ≤ v p ∧ v p ≤ 1 / (1 - β) := by
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (jobT_contraction hπ hβ0 hβ1)
  refine ⟨v, hv, huniq, ?_⟩
  set S' : Set (triD →ᵇ ℝ) := {f | ∀ p, 0 ≤ f p ∧ f p ≤ 1 / (1 - β)}
  have hclosed : IsClosed S' := by
    have : S' = ⋂ p, ({f : triD →ᵇ ℝ | 0 ≤ f p} ∩ {f | f p ≤ 1 / (1 - β)}) := by
      ext f; simp [S']
    rw [this]
    exact isClosed_iInter fun p => (isClosed_le continuous_const (continuous_eval_const p)).inter
      (isClosed_le (continuous_eval_const p) continuous_const)
  have hb1 : 0 < 1 - β := by linarith
  have hmaps : MapsTo (jobT hπ hβ0.le) S' S' := by
    intro f hf p
    have hs : ∀ q, 0 ≤ stayV π β f q ∧ stayV π β f q ≤ 1 / (1 - β) := fun q => by
      obtain ⟨h0, h1⟩ := hπ q.1.1 q.1.2 q.2
      obtain ⟨hS0, hS1⟩ := hf (triS q)
      obtain ⟨hF0, hF1⟩ := hf (triF q)
      unfold stayV
      constructor
      · have : 0 ≤ 1 - π q.1.1 q.1.2 := by linarith
        positivity
      · have e : 1 / (1 - β) = 1 + β * (1 / (1 - β)) := by field_simp; ring
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_left hS1 h0, mul_le_mul_of_nonneg_left hF1
          (sub_nonneg.2 h1)]
    rw [jobT_apply]
    exact ⟨(hs p).1.trans (le_max_left _ _), max_le (hs p).2 (hs tri00).2⟩
  exact (corollary_1 (jobT_contraction hπ hβ0 hβ1) hv
    ⟨0, fun _ => ⟨le_rfl, show (0 : ℝ) ≤ 1 / (1 - β) from div_nonneg zero_le_one hb1.le⟩⟩
    hclosed hmaps hmaps).1

/-! ### Exercise 10.10g: monotonicity -/

/-- The properties of `π(n, k)` in Exercise 10.10d. -/
structure PiProps (π : ℕ → ℕ → ℝ) : Prop where
  bounds : ∀ n k, k ≤ n → 0 < π n k ∧ π n k < 1
  succ_k : ∀ n k, k + 1 ≤ n → π n k < π n (k + 1)
  succ_n : ∀ n k, k ≤ n → π (n + 1) k < π n k
  succ_nk : ∀ n k, k ≤ n → π n k < π (n + 1) (k + 1)

/-- The closed set of functions nonincreasing in `n`, nondecreasing in `k`, and nondecreasing
along successes. -/
def jobMono : Set (triD →ᵇ ℝ) :=
  {f | (∀ p, f (triF p) ≤ f p) ∧ (∀ p h, f p ≤ f (triK p h)) ∧ ∀ p, f p ≤ f (triS p)}

theorem isClosed_jobMono : IsClosed jobMono := by
  have h1 : IsClosed {f : triD →ᵇ ℝ | ∀ p, f (triF p) ≤ f p} := by
    have : {f : triD →ᵇ ℝ | ∀ p, f (triF p) ≤ f p} = ⋂ p, {f | f (triF p) ≤ f p} := by
      ext; simp
    rw [this]
    exact isClosed_iInter fun p => isClosed_le (continuous_eval_const _) (continuous_eval_const _)
  have h2 : IsClosed {f : triD →ᵇ ℝ | ∀ p h, f p ≤ f (triK p h)} := by
    have : {f : triD →ᵇ ℝ | ∀ p h, f p ≤ f (triK p h)} =
        ⋂ p, ⋂ h, {f | f p ≤ f (triK p h)} := by
      ext; simp
    rw [this]
    exact isClosed_iInter fun p => isClosed_iInter fun h =>
      isClosed_le (continuous_eval_const _) (continuous_eval_const _)
  have h3 : IsClosed {f : triD →ᵇ ℝ | ∀ p, f p ≤ f (triS p)} := by
    have : {f : triD →ᵇ ℝ | ∀ p, f p ≤ f (triS p)} = ⋂ p, {f | f p ≤ f (triS p)} := by
      ext; simp
    rw [this]
    exact isClosed_iInter fun p => isClosed_le (continuous_eval_const _) (continuous_eval_const _)
  exact h1.inter (h2.inter h3)

/-- The stay value inherits the three monotonicity properties. -/
theorem stayV_mono (hπ : PiProps π) (hβ : 0 ≤ β) {f : triD →ᵇ ℝ} (hf : f ∈ jobMono) :
    (∀ p, stayV π β f (triF p) ≤ stayV π β f p) ∧
      (∀ p h, stayV π β f p ≤ stayV π β f (triK p h)) ∧
      (∀ p, stayV π β f p ≤ stayV π β f (triS p)) := by
  obtain ⟨hn, hk, hd⟩ := hf
  refine ⟨fun p => ?_, fun p h => ?_, fun p => ?_⟩
  · -- `(n + 1, k)` against `(n, k)`
    obtain ⟨h0, h1⟩ := hπ.bounds _ _ (triF p).2
    exact stay_le hβ h0.le h1.le (hπ.succ_n _ _ p.2).le (hk (triF p) (Nat.succ_le_succ p.2))
      (hn (triS p)) (hn (triF p))
  · -- `(n, k)` against `(n, k + 1)`
    obtain ⟨h0, h1⟩ := hπ.bounds _ _ p.2
    exact stay_le hβ h0.le h1.le (hπ.succ_k _ _ h).le (hk (triS p) (Nat.succ_le_succ h))
      (hk (triS p) (Nat.succ_le_succ h)) (hk (triF p) (Nat.succ_le_succ p.2))
  · -- `(n, k)` against `(n + 1, k + 1)`
    obtain ⟨h0, h1⟩ := hπ.bounds _ _ p.2
    exact stay_le hβ h0.le h1.le (hπ.succ_nk _ _ p.2).le
      (hk (triF (triS p)) (Nat.succ_le_succ (Nat.succ_le_succ p.2))) (hd (triS p)) (hd (triF p))

/-- **Exercise 10.10g** (monotonicity). With `π` as in part (d), `v(n, k)` is nonincreasing in
`n`, nondecreasing in `k`, and nondecreasing along `(n, k) ↦ (n + 1, k + 1)`. -/
theorem ex_10_10g (hπ : PiProps π) (hπ01 : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) {v : triD →ᵇ ℝ} (hv : jobT hπ01 hβ0.le v = v) : v ∈ jobMono := by
  have hmaps : MapsTo (jobT hπ01 hβ0.le) jobMono jobMono := by
    intro f hf
    obtain ⟨hn, hk, hd⟩ := stayV_mono hπ hβ0.le hf
    refine ⟨fun p => ?_, fun p h => ?_, fun p => ?_⟩ <;> simp only [jobT_apply]
    · exact max_le_max (hn p) le_rfl
    · exact max_le_max (hk p h) le_rfl
    · exact max_le_max (hd p) le_rfl
  exact (corollary_1 (S' := jobMono) (S'' := jobMono) (jobT_contraction hπ01 hβ0 hβ1) hv
    ⟨0, fun _ => le_rfl, fun _ _ => le_rfl, fun _ => le_rfl⟩ isClosed_jobMono hmaps hmaps).1

/-! ### Exercise 10.10h: the threshold policy -/

/-- **Exercise 10.10h.** Staying when indifferent, the worker stays on a task at `(n, k)` iff
`k ≥ jₙ`, where `j₁ = 1` and `jₙ` is nondecreasing. -/
theorem ex_10_10h (hπ : PiProps π) (hπ01 : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) {v : triD →ᵇ ℝ} (hv : jobT hπ01 hβ0.le v = v) :
    ∃ j : ℕ → ℕ, (∀ p : triD, v tri00 ≤ stayV π β v p ↔ j p.1.1 ≤ p.1.2) ∧ j 1 = 1 ∧
      Monotone j := by
  obtain ⟨hn, hk, hd⟩ := ex_10_10g hπ hπ01 hβ0 hβ1 hv
  obtain ⟨sn, sk, -⟩ := stayV_mono hπ hβ0.le (ex_10_10g hπ hπ01 hβ0 hβ1 hv)
  have hv00 : v tri00 = stayV π β v tri00 := by
    conv_lhs => rw [← hv, jobT_apply, max_self]
  -- stay at `(n, k)` iff `stay(n, k) ≥ v(0, 0)`; the set of such `k` is an up-set
  set P : ℕ → ℕ → Prop := fun n k => k = n + 1 ∨ ∃ h : k ≤ n, v tri00 ≤ stayV π β v (triMk n k h)
  have hex : ∀ n, ∃ k, P n k := fun n => ⟨n + 1, Or.inl rfl⟩
  classical
  set j : ℕ → ℕ := fun n => Nat.find (hex n)
  have hj_le : ∀ n, j n ≤ n + 1 := fun n => Nat.find_min' (hex n) (Or.inl rfl)
  -- `stay(n, ·)` is monotone in `k`
  have hsk : ∀ n k d (h : k + d ≤ n),
      stayV π β v (triMk n k (by omega)) ≤ stayV π β v (triMk n (k + d) h) := by
    intro n k d
    induction d with
    | zero => intro h; exact le_rfl
    | succ d ih =>
      intro h
      exact (ih (by omega)).trans (sk (triMk n (k + d) (by omega)) h)
  have hchar : ∀ p : triD, v tri00 ≤ stayV π β v p ↔ j p.1.1 ≤ p.1.2 := by
    rintro ⟨⟨n, k⟩, hkn⟩
    change v tri00 ≤ stayV π β v (triMk n k hkn) ↔ j n ≤ k
    constructor
    · intro h
      exact Nat.find_min' (hex n) (Or.inr ⟨hkn, h⟩)
    · intro h
      rcases Nat.find_spec (hex n) with h' | ⟨hjn, h'⟩
      · exfalso
        change j n = n + 1 at h'
        change j n ≤ k at h
        have : k ≤ n := hkn
        omega
      · obtain ⟨d, hd⟩ : ∃ d, k = j n + d := ⟨k - j n, by omega⟩
        subst hd
        exact h'.trans (hsk n (j n) d hkn)
  refine ⟨j, hchar, ?_, monotone_nat_of_le_succ fun n => ?_⟩
  · -- `j₁ = 1`: leave after one failure, stay after one success
    have hπ00 := hπ.bounds 0 0 le_rfl
    have hπ10 := hπ.bounds 1 0 (by norm_num)
    have hπ11 := hπ.bounds 1 1 le_rfl
    have h10 : stayV π β v (triMk 1 0 (by norm_num)) < v tri00 := by
      rw [hv00]
      exact stay_lt hβ0.le hπ10.1.le hπ10.2.le (hπ.succ_n 0 0 le_rfl) (hk (triF tri00) le_rfl)
        (hn (triS tri00)) (hn (triF tri00))
    have h11 : v tri00 ≤ stayV π β v (triMk 1 1 le_rfl) := by
      rw [hv00]
      exact (stay_lt hβ0.le hπ00.1.le hπ00.2.le (hπ.succ_nk 0 0 le_rfl)
        (hk (triF (triS tri00)) (show 1 + 1 ≤ 2 from le_rfl)) (hd (triS tri00))
        (hd (triF tri00))).le
    have hj1 : j 1 ≤ 1 := (hchar (triMk 1 1 le_rfl)).1 h11
    have hj0 : ¬ j 1 ≤ 0 := fun h => not_le.2 h10 ((hchar (triMk 1 0 (by norm_num))).2 h)
    omega
  · -- `jₙ ≤ jₙ₊₁`: staying at `(n + 1, k)` implies staying at `(n, k)`
    by_cases hk' : j (n + 1) ≤ n
    · have hstay := (hchar (triMk (n + 1) (j (n + 1)) (by omega))).2 le_rfl
      have := sn (triMk n (j (n + 1)) hk')
      exact (hchar (triMk n (j (n + 1)) hk')).1 (hstay.trans this)
    · exact (hj_le n).trans (by omega)

/-! ### Exercise 10.10g: the limit -/

/-- The bound sequence `G₀ = 1/(1 − β)`, `Gₘ₊₁ = max{v(0, 0), q + βGₘ}`. -/
noncomputable def jobG (β c q : ℝ) : ℕ → ℝ
  | 0 => 1 / (1 - β)
  | m + 1 => max c (q + β * jobG β c q m)

/-- If `π ≤ q` at all states within `m` steps of `b`, then `v(b) ≤ Gₘ`. -/
theorem job_v_le (hπ01 : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β) {v : triD →ᵇ ℝ}
    (hv : jobT hπ01 hβ0.le v = v) (hvb : ∀ p, v p ≤ 1 / (1 - β)) {q : ℝ} (m : ℕ) :
    ∀ b : triD, (∀ j i, i ≤ j → j < m → π (b.1.1 + j) (b.1.2 + i) ≤ q) →
      v b ≤ jobG β (v tri00) q m := by
  induction m with
  | zero => exact fun b _ => hvb b
  | succ m ih =>
    intro b hb
    have hS := ih (triS b) fun j i hij hjm => by
      have := hb (j + 1) (i + 1) (by omega) (by omega)
      simpa [triS, Nat.add_assoc, Nat.add_comm 1] using this
    have hF := ih (triF b) fun j i hij hjm => by
      have := hb (j + 1) i (by omega) (by omega)
      simpa [triF, Nat.add_assoc, Nat.add_comm 1] using this
    have hq := hb 0 0 le_rfl (Nat.succ_pos m)
    simp only [Nat.add_zero] at hq
    obtain ⟨h0, h1⟩ := hπ01 b.1.1 b.1.2 b.2
    conv_lhs => rw [← hv]
    rw [jobT_apply]
    refine max_le ?_ ?_
    · refine (le_max_right _ _).trans' ?_
      have hmix : π b.1.1 b.1.2 * v (triS b) + (1 - π b.1.1 b.1.2) * v (triF b) ≤
          jobG β (v tri00) q m := by
        nlinarith [mul_le_mul_of_nonneg_left hS h0, mul_le_mul_of_nonneg_left hF
          (sub_nonneg.2 h1)]
      have := mul_le_mul_of_nonneg_left hmix hβ0.le
      unfold stayV
      linarith
    · conv_lhs => rw [show stayV π β v tri00 = v tri00 by
        conv_rhs => rw [← hv, jobT_apply, max_self]]
      exact le_max_left _ _

/-- If `π ≥ q` at all states within `m` steps of `b`, then
`v(b) ≥ q + βq + ⋯ + βᵐ⁻¹q`. -/
theorem job_v_ge (hπ01 : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β) {v : triD →ᵇ ℝ}
    (hv : jobT hπ01 hβ0.le v = v) (hv0 : ∀ p, 0 ≤ v p) {q : ℝ} (m : ℕ) :
    ∀ b : triD, (∀ j i, i ≤ j → j < m → q ≤ π (b.1.1 + j) (b.1.2 + i)) →
      ∑ t ∈ Finset.range m, β ^ t * q ≤ v b := by
  induction m with
  | zero => exact fun b _ => by simpa using hv0 b
  | succ m ih =>
    intro b hb
    have hS := ih (triS b) fun j i hij hjm => by
      have := hb (j + 1) (i + 1) (by omega) (by omega)
      simpa [triS, Nat.add_assoc, Nat.add_comm 1] using this
    have hF := ih (triF b) fun j i hij hjm => by
      have := hb (j + 1) i (by omega) (by omega)
      simpa [triF, Nat.add_assoc, Nat.add_comm 1] using this
    have hq := hb 0 0 le_rfl (Nat.succ_pos m)
    simp only [Nat.add_zero] at hq
    obtain ⟨h0, h1⟩ := hπ01 b.1.1 b.1.2 b.2
    conv_rhs => rw [← hv]
    rw [jobT_apply]
    refine le_trans ?_ (le_max_left _ _)
    rw [Finset.sum_range_succ', pow_zero, one_mul]
    have hsum : ∑ t ∈ Finset.range m, β ^ (t + 1) * q = β * ∑ t ∈ Finset.range m, β ^ t * q := by
      rw [Finset.mul_sum]; congr 1; ext t; ring
    rw [hsum]
    have hmix : ∑ t ∈ Finset.range m, β ^ t * q ≤
        π b.1.1 b.1.2 * v (triS b) + (1 - π b.1.1 b.1.2) * v (triF b) := by
      nlinarith [mul_le_mul_of_nonneg_left hS h0, mul_le_mul_of_nonneg_left hF (sub_nonneg.2 h1)]
    have := mul_le_mul_of_nonneg_left hmix hβ0.le
    unfold stayV
    linarith

/-- `Gₘ` converges geometrically to `max{c, q/(1 − β)}`. -/
theorem jobG_dist (hβ0 : 0 < β) (hβ1 : β < 1) (c q : ℝ) (m : ℕ) :
    |jobG β c q m - max c (q / (1 - β))| ≤ β ^ m * |1 / (1 - β) - max c (q / (1 - β))| := by
  have hb1 : 0 < 1 - β := by linarith
  have hfix : max c (q + β * max c (q / (1 - β))) = max c (q / (1 - β)) := by
    rcases le_total c (q / (1 - β)) with h | h
    · rw [max_eq_right h, show q + β * (q / (1 - β)) = q / (1 - β) by field_simp; ring,
        max_eq_right h]
    · rw [max_eq_left h]
      apply max_eq_left
      have : q ≤ c * (1 - β) := by rwa [div_le_iff₀ hb1] at h
      nlinarith
  induction m with
  | zero => rw [pow_zero, one_mul]; exact le_rfl
  | succ m ih =>
    have e : jobG β c q (m + 1) = max c (q + β * jobG β c q m) := rfl
    calc |jobG β c q (m + 1) - max c (q / (1 - β))|
        = |max c (q + β * jobG β c q m) - max c (q + β * max c (q / (1 - β)))| := by
          rw [e, hfix]
      _ ≤ |(q + β * jobG β c q m) - (q + β * max c (q / (1 - β)))| := by
          rw [max_comm c, max_comm c]; exact abs_max_sub_max_le_abs _ _ _
      _ = β * |jobG β c q m - max c (q / (1 - β))| := by
          rw [show q + β * jobG β c q m - (q + β * max c (q / (1 - β))) =
            β * (jobG β c q m - max c (q / (1 - β))) by ring, abs_mul, abs_of_pos hβ0]
      _ ≤ β * (β ^ m * |1 / (1 - β) - max c (q / (1 - β))|) :=
          mul_le_mul_of_nonneg_left ih hβ0.le
      _ = _ := by ring

/-- **Exercise 10.10g** (limit). If `π` is uniformly within any `ε` of `p` on the windows
`{(n + j, kₙ + i) : i ≤ j ≤ J}` for all large `n`, then `v(n, kₙ) → max{p/(1 − β), v(0, 0)}`. -/
theorem ex_10_10g_limit (hπ01 : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {v : triD →ᵇ ℝ} (hv : jobT hπ01 hβ0.le v = v) {k : ℕ → ℕ} (hk : ∀ n, k n ≤ n) {p : ℝ}
    (hp : 0 ≤ p ∧ p ≤ 1)
    (hwin : ∀ (J : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, ∀ j i, i ≤ j → j ≤ J →
      |π (n + j) (k n + i) - p| ≤ ε) :
    Tendsto (fun n => v (triMk n (k n) (hk n))) atTop
      (𝓝 (max (p / (1 - β)) (v tri00))) := by
  obtain ⟨-, -, hvb⟩ := ex_10_10f hπ01 hβ0 hβ1
  obtain ⟨v', hv', huniq, hb⟩ := ex_10_10f hπ01 hβ0 hβ1
  have hvv' : v = v' := huniq v hv
  subst hvv'
  have hb1 : 0 < 1 - β := by linarith
  set c := v tri00
  have hc : 0 ≤ c ∧ c ≤ 1 / (1 - β) := hb tri00
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose `m` with `βᵐ · 4/(1 − β) < ε/2`, then `δ ≤ 1` with `δ/(1 − β) ≤ ε/4`
  obtain ⟨m, hm⟩ := (tendsto_order.1 ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
    (4 / (1 - β)))).2 (ε / 2) (by rw [zero_mul]; linarith) |>.exists
  set δ := min (ε * (1 - β) / 4) 1
  have hδ : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ / (1 - β) ≤ ε / 4 := by
    rw [div_le_iff₀ hb1]; have := min_le_left (ε * (1 - β) / 4) 1; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hwin m δ hδ)
  refine ⟨N, fun n hn => ?_⟩
  have hw := hN n hn
  set b := triMk n (k n) (hk n)
  have hup : v b ≤ jobG β c (p + δ) m := job_v_le hπ01 hβ0 hv (fun q => (hb q).2) m b
    fun j i hij hjm => by
      have := (abs_le.1 (hw j i hij hjm.le)).2
      change π (n + j) (k n + i) ≤ p + δ
      linarith
  have hlow : ∑ t ∈ Finset.range m, β ^ t * (p - δ) ≤ v b :=
    job_v_ge hπ01 hβ0 hv (fun q => (hb q).1) m b fun j i hij hjm => by
      have := (abs_le.1 (hw j i hij hjm.le)).1
      change p - δ ≤ π (n + j) (k n + i)
      linarith
  have hlow' : c ≤ v b := by
    rw [← hv, jobT_apply]
    refine le_trans (le_of_eq ?_) (le_max_right _ _)
    change v tri00 = stayV π β v tri00
    conv_lhs => rw [← hv, jobT_apply, max_self]
  have hgeo : ∑ t ∈ Finset.range m, β ^ t * (p - δ) = (p - δ) * (1 - β ^ m) / (1 - β) := by
    have hb' : β - 1 ≠ 0 := by linarith
    rw [← Finset.sum_mul, geom_sum_eq hβ1.ne, div_mul_eq_mul_div,
      div_eq_div_iff hb' hb1.ne']
    ring
  have hG := (abs_le.1 (jobG_dist hβ0 hβ1 c (p + δ) m)).2
  have hβm : 0 ≤ β ^ m := pow_nonneg hβ0.le m
  have hm' : β ^ m * (4 / (1 - β)) < ε / 2 := hm
  have hinv : 0 < 1 / (1 - β) := by positivity
  -- the limit of the bound sequence is within `ε/4` of `max{p/(1 − β), c}`
  have hstar : max c ((p + δ) / (1 - β)) ≤ max (p / (1 - β)) c + ε / 4 := by
    refine max_le (by linarith [le_max_right (p / (1 - β)) c]) ?_
    rw [add_div]
    linarith [le_max_left (p / (1 - β)) c]
  have hG0 : |1 / (1 - β) - max c ((p + δ) / (1 - β))| ≤ 4 / (1 - β) := by
    have h2 : (p + δ) / (1 - β) ≤ 2 / (1 - β) :=
      div_le_div_of_nonneg_right (by linarith) hb1.le
    have h3 : 1 / (1 - β) ≤ 2 / (1 - β) := div_le_div_of_nonneg_right (by norm_num) hb1.le
    have h4 : 2 / (1 - β) ≤ 4 / (1 - β) := div_le_div_of_nonneg_right (by norm_num) hb1.le
    rw [abs_le]
    constructor
    · linarith [max_le (hc.2.trans h3) h2]
    · linarith [le_max_left c ((p + δ) / (1 - β)), hc.1]
  have hupper : v b < max (p / (1 - β)) c + ε := by
    have := mul_le_mul_of_nonneg_left hG0 hβm
    linarith
  -- staying forever gives at least `(p − δ)(1 − βᵐ)/(1 − β)`
  have hL : p / (1 - β) - 3 * ε / 4 ≤ (p - δ) * (1 - β ^ m) / (1 - β) := by
    have e : (p - δ) * (1 - β ^ m) / (1 - β) =
        p / (1 - β) - δ / (1 - β) - β ^ m * (p / (1 - β)) + β ^ m * (δ / (1 - β)) := by
      field_simp
      ring
    have hp' : β ^ m * (p / (1 - β)) ≤ β ^ m * (4 / (1 - β)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hb1.le) hβm
    have : 0 ≤ β ^ m * (δ / (1 - β)) := mul_nonneg hβm (by positivity)
    linarith
  have hlower : max (p / (1 - β)) c - ε < v b := by
    rw [hgeo] at hlow
    rcases le_total (p / (1 - β)) c with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Job matching: the beta posterior

SLP §10.10, Exercise 10.10a–e, pp. 311–313. After `k` successes in `n` trials the density of
the success probability `θ` is `f(θ, n, k) ∝ C(n, k) θᵏ(1 − θ)ⁿ⁻ᵏ μ(θ)` (`postDensity`), and
`π(n, k) = ∫ θ f(θ, n, k) dθ` (`postMean`).

* `integral_beta_kernel`: `∫₀¹ x^{a−1}(1 − x)^{b−1} dx = Γ(a)Γ(b)/Γ(a + b)`.
* **Exercise 10.10a–b** (`ex_10_10a`, `ex_10_10b`): with the uniform prior the posterior is
  beta `(k + 1, n + 1 − k)`; with a beta `(α, β)` prior it is beta `(α + k, β + n − k)`.
* **Exercise 10.10c** (`ex_10_10c`): `π(n, k) = (α + k)/(α + β + n)` (`betaπ`).
* **Exercise 10.10d** (`ex_10_10d`): the four inequalities, as `PiProps`.
* **Exercise 10.10e** (`ex_10_10e`): `kₙ/n → p` implies `π(n, kₙ) → p`; uniformly on the
  windows `{(n + j, kₙ + i) : i ≤ j ≤ J}` (`betaπ_window`), so the limit of Exercise 10.10g holds
  for the beta prior (`ex_10_10g_beta`). Whether (d)–(e) hold for an arbitrary prior density
  positive on `(0, 1)` is not addressed.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

/-- The beta integral: `∫₀¹ x^{a−1}(1 − x)^{b−1} dx = Γ(a)Γ(b)/Γ(a + b)`. -/
theorem integral_beta_kernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Ioo (0 : ℝ) 1, x ^ (a - 1) * (1 - x) ^ (b - 1) = beta a b := by
  rw [beta_eq_betaIntegralReal a b ha hb, Complex.betaIntegral,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Ioc_eq_integral_Ioo,
    ← RCLike.re_to_complex, ← integral_re]
  · refine setIntegral_congr_fun measurableSet_Ioc fun x ⟨hx1, hx2⟩ => ?_
    norm_cast
    rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
      Complex.re_mul_ofReal, Complex.ofReal_re]
    all_goals linarith
  · convert! Complex.betaIntegral_convergent (u := a) (v := b) (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]

/-- The posterior density of `θ` after `k` successes in `n` trials, for a prior density `μ` on
`(0, 1)` (Bayes's rule, p. 312). -/
noncomputable def postDensity (μ : ℝ → ℝ) (n k : ℕ) (θ : ℝ) : ℝ :=
  (n.choose k : ℝ) * θ ^ k * (1 - θ) ^ (n - k) * μ θ /
    ∫ u in Ioo (0 : ℝ) 1, (n.choose k : ℝ) * u ^ k * (1 - u) ^ (n - k) * μ u

/-- The expected return `π(n, k) = ∫ θ f(θ, n, k) dθ` on the next trial. -/
noncomputable def postMean (μ : ℝ → ℝ) (n k : ℕ) : ℝ :=
  ∫ θ in Ioo (0 : ℝ) 1, θ * postDensity μ n k θ

/-- With a beta prior, the likelihood times the prior is a beta kernel. -/
theorem lik_mul_betaPDF {α β : ℝ} {n k : ℕ} (hkn : k ≤ n) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (n.choose k : ℝ) * u ^ k * (1 - u) ^ (n - k) * betaPDFReal α β u =
      (n.choose k : ℝ) / beta α β * (u ^ (α + k - 1) * (1 - u) ^ (β + n - k - 1)) := by
  have h0 : 0 < u := hu.1
  have h1 : 0 < 1 - u := by linarith [hu.2]
  rw [betaPDFReal, ite_eq_left_of_eq_true _ _ (eq_true (show 0 < u ∧ u < 1 from hu))]
  have e1 : u ^ (α + k - 1) = u ^ (k : ℝ) * u ^ (α - 1) := by
    rw [← Real.rpow_add h0]; ring_nf
  have e2 : (1 - u) ^ (β + n - k - 1) = (1 - u) ^ ((n - k : ℕ) : ℝ) * (1 - u) ^ (β - 1) := by
    rw [← Real.rpow_add h1, Nat.cast_sub hkn]; ring_nf
  rw [e1, e2, Real.rpow_natCast, Real.rpow_natCast]
  ring

/-- The normalizing constant of the posterior under a beta prior. -/
theorem integral_lik_mul_betaPDF {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n k : ℕ} (hkn : k ≤ n) :
    ∫ u in Ioo (0 : ℝ) 1, (n.choose k : ℝ) * u ^ k * (1 - u) ^ (n - k) * betaPDFReal α β u =
      (n.choose k : ℝ) / beta α β * beta (α + k) (β + n - k) := by
  rw [setIntegral_congr_fun measurableSet_Ioo fun u hu => lik_mul_betaPDF hkn hu,
    integral_const_mul, integral_beta_kernel (by positivity)]
  have : (k : ℝ) ≤ n := by exact_mod_cast hkn
  linarith

/-- `B(a, b) = Γ(a)Γ(b)/Γ(a + b)`, positive. -/
theorem beta_pos' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < beta a b := beta_pos ha hb

/-- **Exercise 10.10b.** With the beta prior `μ(θ) = Γ(α + β)/[Γ(α)Γ(β)] θ^{α−1}(1 − θ)^{β−1}`,
the posterior after `k` successes in `n` trials is the beta density with parameters
`(α + k, β + n − k)`. -/
theorem ex_10_10b {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n k : ℕ} (hkn : k ≤ n) {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    postDensity (betaPDFReal α β) n k θ = Real.Gamma (α + β + n) /
      (Real.Gamma (α + k) * Real.Gamma (β + n - k)) * θ ^ (α + k - 1) *
        (1 - θ) ^ (β + n - k - 1) := by
  have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hb1 : 0 < β + n - k := by linarith
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hB := beta_pos hα hβ
  have hB' := beta_pos (show 0 < α + k by positivity) hb1
  rw [postDensity, lik_mul_betaPDF hkn hθ, integral_lik_mul_betaPDF hα hβ hkn]
  have e : α + k + (β + n - k) = α + β + n := by ring
  rw [show beta (α + k) (β + n - k) = Real.Gamma (α + k) * Real.Gamma (β + n - k) /
    Real.Gamma (α + β + n) by rw [beta, e]]
  have hG1 := Real.Gamma_pos_of_pos (show 0 < α + k by positivity)
  have hG2 := Real.Gamma_pos_of_pos hb1
  have hG3 := Real.Gamma_pos_of_pos (show 0 < α + β + n by positivity)
  field_simp

/-- **Exercise 10.10a.** With the uniform prior `μ = 1` on `(0, 1)`, the posterior is the beta
density with parameters `(k + 1, n + 1 − k)`. -/
theorem ex_10_10a {n k : ℕ} (hkn : k ≤ n) {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    postDensity (fun _ => 1) n k θ = Real.Gamma (n + 2) /
      (Real.Gamma (k + 1) * Real.Gamma (n + 1 - k)) * θ ^ k * (1 - θ) ^ (n - k) := by
  -- the uniform density is the beta(1, 1) density on `(0, 1)`
  have hB : beta 1 1 = 1 := by norm_num [beta, Real.Gamma_two]
  have hU : ∀ u ∈ Ioo (0 : ℝ) 1, betaPDFReal 1 1 u = 1 := fun u hu => by
    rw [betaPDFReal, ite_eq_left_of_eq_true _ _ (eq_true (show 0 < u ∧ u < 1 from hu)), hB]; simp
  have hpost : postDensity (fun _ => 1) n k θ = postDensity (betaPDFReal 1 1) n k θ := by
    unfold postDensity
    rw [hU θ hθ, setIntegral_congr_fun (g := fun u => (n.choose k : ℝ) * u ^ k * (1 - u) ^ (n - k) *
      betaPDFReal 1 1 u) measurableSet_Ioo fun u hu => by simp only [hU u hu]]
  rw [hpost, ex_10_10b one_pos one_pos hkn hθ]
  have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have e1 : (1 : ℝ) + 1 + n = n + 2 := by ring
  have e2 : (1 : ℝ) + k = k + 1 := by ring
  have e3 : (1 : ℝ) + n - k = n + 1 - k := by ring
  have e4 : θ ^ ((1 : ℝ) + k - 1) = θ ^ k := by
    rw [show (1 : ℝ) + k - 1 = (k : ℝ) by ring, Real.rpow_natCast]
  have e5 : (1 - θ) ^ ((1 : ℝ) + n - k - 1) = (1 - θ) ^ (n - k) := by
    rw [show (1 : ℝ) + n - k - 1 = ((n - k : ℕ) : ℝ) by rw [Nat.cast_sub hkn]; ring,
      Real.rpow_natCast]
  rw [e4, e5, e1, e2, e3]

/-- **Exercise 10.10c.** With the beta prior, `π(n, k) = (α + k)/(α + β + n)`. -/
theorem ex_10_10c {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n k : ℕ} (hkn : k ≤ n) :
    postMean (betaPDFReal α β) n k = (α + k) / (α + β + n) := by
  have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hb1 : 0 < β + n - k := by linarith
  have hak : 0 < α + k := by positivity
  rw [postMean, setIntegral_congr_fun measurableSet_Ioo fun θ hθ => by
      rw [ex_10_10b hα hβ hkn hθ]]
  have hint : ∀ θ ∈ Ioo (0 : ℝ) 1, θ * (Real.Gamma (α + β + n) /
      (Real.Gamma (α + k) * Real.Gamma (β + n - k)) * θ ^ (α + k - 1) *
        (1 - θ) ^ (β + n - k - 1)) = Real.Gamma (α + β + n) /
      (Real.Gamma (α + k) * Real.Gamma (β + n - k)) *
        (θ ^ (α + k + 1 - 1) * (1 - θ) ^ (β + n - k - 1)) := fun θ hθ => by
    have : θ ^ (α + k + 1 - 1) = θ * θ ^ (α + k - 1) := by
      rw [show α + k + 1 - 1 = 1 + (α + k - 1) by ring, Real.rpow_add hθ.1, Real.rpow_one]
    rw [this]; ring
  rw [setIntegral_congr_fun measurableSet_Ioo hint, integral_const_mul,
    integral_beta_kernel (by positivity) hb1, beta]
  have e : α + k + 1 + (β + n - k) = α + β + n + 1 := by ring
  rw [e, Real.Gamma_add_one hak.ne', Real.Gamma_add_one (by positivity : α + β + n ≠ 0)]
  have hG1 := Real.Gamma_pos_of_pos hak
  have hG2 := Real.Gamma_pos_of_pos hb1
  have hG3 := Real.Gamma_pos_of_pos (show 0 < α + β + n by positivity)
  field_simp

/-- The success probability `π(n, k) = (α + k)/(α + β + n)` of Exercise 10.10c. -/
noncomputable def betaπ (α β : ℝ) (n k : ℕ) : ℝ := (α + k) / (α + β + n)

/-- **Exercise 10.10d.** `0 < π(n, k) < 1`, `π(n, k + 1) > π(n, k)`, `π(n + 1, k) < π(n, k)` and
`π(n + 1, k + 1) > π(n, k)`. -/
theorem ex_10_10d {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : PiProps (betaπ α β) := by
  refine ⟨fun n k hkn => ?_, fun n k hkn => ?_, fun n k hkn => ?_, fun n k hkn => ?_⟩ <;>
    unfold betaπ <;> push_cast
  · have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
    exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩
  · have hk : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    exact div_lt_div_of_pos_right (by linarith) (by positivity)
  · have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
    exact div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  · have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem betaπ_mem {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∀ n k, k ≤ n → 0 ≤ betaπ α β n k ∧ betaπ α β n k ≤ 1 := fun n k hkn =>
  ⟨((ex_10_10d hα hβ).bounds n k hkn).1.le, ((ex_10_10d hα hβ).bounds n k hkn).2.le⟩

/-- `π(n + j, kₙ + i) → p` when `kₙ/n → p`. -/
theorem betaπ_tendsto {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {k : ℕ → ℕ} {p : ℝ}
    (hp : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 p)) (j i : ℕ) :
    Tendsto (fun n => betaπ α β (n + j) (k n + i)) atTop (𝓝 p) := by
  have hnum := (tendsto_const_div_atTop_nhds_zero_nat (α + i)).add hp
  have hden := (tendsto_const_div_atTop_nhds_zero_nat (α + β + j)).add_const (1 : ℝ)
  rw [zero_add] at hnum hden
  have := hnum.div hden one_ne_zero
  rw [div_one] at this
  refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change ((α + i) / n + k n / n) / ((α + β + j) / n + 1) = betaπ α β (n + j) (k n + i)
  unfold betaπ
  push_cast
  field_simp
  ring

/-- **Exercise 10.10e.** If `kₙ ≤ n` and `kₙ/n → p`, then `π(n, kₙ) → p`. -/
theorem ex_10_10e {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {k : ℕ → ℕ} {p : ℝ}
    (hp : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 p)) :
    Tendsto (fun n => betaπ α β n (k n)) atTop (𝓝 p) := by
  simpa using betaπ_tendsto hα hβ hp 0 0

/-- The beta `π` is uniformly near `p` on the windows `{(n + j, kₙ + i) : i ≤ j ≤ J}`. -/
theorem betaπ_window {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {k : ℕ → ℕ} {p : ℝ}
    (hp : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 p)) (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ j i, i ≤ j → j ≤ J → |betaπ α β (n + j) (k n + i) - p| ≤ ε := by
  have h : ∀ j ∈ Finset.range (J + 1), ∀ i ∈ Finset.range (J + 1),
      ∀ᶠ n in atTop, |betaπ α β (n + j) (k n + i) - p| ≤ ε := fun j _ i _ =>
    (Metric.tendsto_nhds.1 (betaπ_tendsto hα hβ hp j i) ε hε).mono fun n hn =>
      (Real.dist_eq _ _ ▸ hn).le
  have h' : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (J + 1), ∀ i ∈ Finset.range (J + 1),
      |betaπ α β (n + j) (k n + i) - p| ≤ ε :=
    (eventually_all_finset _).2 fun j hj => (eventually_all_finset _).2 (h j hj)
  filter_upwards [h'] with n hn j i hij hjJ
  exact hn j (Finset.mem_range.2 (by omega)) i (Finset.mem_range.2 (by omega))

/-- **Exercise 10.10g** (limit) for the beta prior: if `kₙ ≤ n` and `kₙ/n → p`, then
`v(n, kₙ) → max{p/(1 − β), v(0, 0)}`. -/
theorem ex_10_10g_beta {α β₀ β : ℝ} (hα : 0 < α) (hβ₀ : 0 < β₀) (hβ0 : 0 < β) (hβ1 : β < 1)
    {v : triD →ᵇ ℝ} (hv : jobT (betaπ_mem hα hβ₀) hβ0.le v = v) {k : ℕ → ℕ}
    (hk : ∀ n, k n ≤ n) {p : ℝ} (hp : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 p)) :
    Tendsto (fun n => v (triMk n (k n) (hk n))) atTop (𝓝 (max (p / (1 - β)) (v tri00))) := by
  have hb : ∀ n, 0 ≤ (k n : ℝ) / n ∧ (k n : ℝ) / n ≤ 1 := fun n => by
    refine ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast hk n) (by positivity)⟩
  exact ex_10_10g_limit (betaπ_mem hα hβ₀) hβ0 hβ1 hv hk
    ⟨ge_of_tendsto' hp fun n => (hb n).1, le_of_tendsto' hp fun n => (hb n).2⟩
    (betaπ_window hα hβ₀ hp)

end StokeyLucasPrescott.StochasticApplications

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.StochasticApplications.IsLHC
#print axioms StokeyLucasPrescott.StochasticApplications.IsUHC
#print axioms StokeyLucasPrescott.StochasticApplications.graph
#print axioms StokeyLucasPrescott.StochasticApplications.continuousAt_of_isUHC_singleton
#print axioms StokeyLucasPrescott.StochasticApplications.isCompact_graph
#print axioms StokeyLucasPrescott.StochasticApplications.IsContraction
#print axioms StokeyLucasPrescott.StochasticApplications.IsContraction.uniformContinuous
#print axioms StokeyLucasPrescott.StochasticApplications.dist_iterate_succ_le
#print axioms StokeyLucasPrescott.StochasticApplications.dist_iterate_le
#print axioms StokeyLucasPrescott.StochasticApplications.cauchySeq_iterate
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_3_2
#print axioms StokeyLucasPrescott.StochasticApplications.dist_fixedPoint_le
#print axioms StokeyLucasPrescott.StochasticApplications.corollary_1
#print axioms StokeyLucasPrescott.StochasticApplications.corollary_2
#print axioms StokeyLucasPrescott.StochasticApplications.maxValue
#print axioms StokeyLucasPrescott.StochasticApplications.argmax
#print axioms StokeyLucasPrescott.StochasticApplications.continuousOn_section
#print axioms StokeyLucasPrescott.StochasticApplications.exists_argmax
#print axioms StokeyLucasPrescott.StochasticApplications.le_maxValue
#print axioms StokeyLucasPrescott.StochasticApplications.tendsto_f_graph
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_3_6
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.mk
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.nonempty
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.compact
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.lhc
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.uhc
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.cont
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.unique
#print axioms StokeyLucasPrescott.StochasticApplications.argmaxFn
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.argmaxFn_mem
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.argmax_eq
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.lt_of_ne
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.continuous_argmaxFn
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.lemma_3_7
#print axioms StokeyLucasPrescott.StochasticApplications.UniqueArgmax.lemma_3_7_uniform
#print axioms StokeyLucasPrescott.StochasticApplications.shortfall_lt
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_3_8
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_3_8_uniform
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_4_10
#print axioms StokeyLucasPrescott.StochasticApplications.ex_4_5
#print axioms StokeyLucasPrescott.StochasticApplications.IsMeasurableSelection
#print axioms StokeyLucasPrescott.StochasticApplications.IsMeasCorr
#print axioms StokeyLucasPrescott.StochasticApplications.minCoord
#print axioms StokeyLucasPrescott.StochasticApplications.minCoord_mem
#print axioms StokeyLucasPrescott.StochasticApplications.minCoord_le
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_minCoord
#print axioms StokeyLucasPrescott.StochasticApplications.refineCorr
#print axioms StokeyLucasPrescott.StochasticApplications.IsMeasCorr.refine
#print axioms StokeyLucasPrescott.StochasticApplications.lexCorr
#print axioms StokeyLucasPrescott.StochasticApplications.lexCorr_spec
#print axioms StokeyLucasPrescott.StochasticApplications.isMeasCorr_of_uhc
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_7_6
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_7_6_subtype
#print axioms StokeyLucasPrescott.StochasticApplications.IsTransitionFunction
#print axioms StokeyLucasPrescott.StochasticApplications.isTransitionFunction_iff
#print axioms StokeyLucasPrescott.StochasticApplications.markovOp
#print axioms StokeyLucasPrescott.StochasticApplications.markovOpR
#print axioms StokeyLucasPrescott.StochasticApplications.adjointOp
#print axioms StokeyLucasPrescott.StochasticApplications.markovOp_indicator
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_1
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_of_bounded
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_1_cor
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_1
#print axioms StokeyLucasPrescott.StochasticApplications.adjointOp_apply
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_2
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_2
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_3
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_3_cor
#print axioms StokeyLucasPrescott.StochasticApplications.pairing
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_3
#print axioms StokeyLucasPrescott.StochasticApplications.kpow
#print axioms StokeyLucasPrescott.StochasticApplications.kpow_one
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_4a
#print axioms StokeyLucasPrescott.StochasticApplications.kpow_add
#print axioms StokeyLucasPrescott.StochasticApplications.markovOp_comp
#print axioms StokeyLucasPrescott.StochasticApplications.adjointOp_comp
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_4b
#print axioms StokeyLucasPrescott.StochasticApplications.adjointOp_iterate
#print axioms StokeyLucasPrescott.StochasticApplications.IsFeller
#print axioms StokeyLucasPrescott.StochasticApplications.IsMonotoneTF
#print axioms StokeyLucasPrescott.StochasticApplications.IsStochasticKernel
#print axioms StokeyLucasPrescott.StochasticApplications.isStochasticKernel_iff
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_4
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_4_cor
#print axioms StokeyLucasPrescott.StochasticApplications.directProd
#print axioms StokeyLucasPrescott.StochasticApplications.isMarkovKernel_directProd
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_5
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_5_unique
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_6
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_7
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_6_cor
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_9a
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_9b
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_cons
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_snoc
#print axioms StokeyLucasPrescott.StochasticApplications.lastState
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_lastState
#print axioms StokeyLucasPrescott.StochasticApplications.lastState_cons
#print axioms StokeyLucasPrescott.StochasticApplications.lastState_snoc
#print axioms StokeyLucasPrescott.StochasticApplications.hist
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_8a
#print axioms StokeyLucasPrescott.StochasticApplications.hist_zero_lintegral
#print axioms StokeyLucasPrescott.StochasticApplications.hist_succ_lintegral
#print axioms StokeyLucasPrescott.StochasticApplications.iterLInt
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_8
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_5
#print axioms StokeyLucasPrescott.StochasticApplications.nextKernel
#print axioms StokeyLucasPrescott.StochasticApplications.isMarkovKernel_nextKernel
#print axioms StokeyLucasPrescott.StochasticApplications.nextKernel_apply
#print axioms StokeyLucasPrescott.StochasticApplications.hist_succ_lintegral_last
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_8b
#print axioms StokeyLucasPrescott.StochasticApplications.hist_succ_eq_cons
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_8c_last
#print axioms StokeyLucasPrescott.StochasticApplications.ex_8_8c_first
#print axioms StokeyLucasPrescott.StochasticApplications.iterInt
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_8_8_integrable
#print axioms StokeyLucasPrescott.StochasticApplications.Model
#print axioms StokeyLucasPrescott.StochasticApplications.Model.mk
#print axioms StokeyLucasPrescott.StochasticApplications.Model.Q
#print axioms StokeyLucasPrescott.StochasticApplications.Model.Γ
#print axioms StokeyLucasPrescott.StochasticApplications.Model.φ
#print axioms StokeyLucasPrescott.StochasticApplications.Model.F
#print axioms StokeyLucasPrescott.StochasticApplications.Model.β
#print axioms StokeyLucasPrescott.StochasticApplications.Model.first
#print axioms StokeyLucasPrescott.StochasticApplications.Plan
#print axioms StokeyLucasPrescott.StochasticApplications.xState
#print axioms StokeyLucasPrescott.StochasticApplications.state
#print axioms StokeyLucasPrescott.StochasticApplications.state_zero
#print axioms StokeyLucasPrescott.StochasticApplications.IsFeasible
#print axioms StokeyLucasPrescott.StochasticApplications.ret
#print axioms StokeyLucasPrescott.StochasticApplications.uN
#print axioms StokeyLucasPrescott.StochasticApplications.planValue
#print axioms StokeyLucasPrescott.StochasticApplications.vStar
#print axioms StokeyLucasPrescott.StochasticApplications.planValue_eq
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_init
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_xState
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_state
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_ret
#print axioms StokeyLucasPrescott.StochasticApplications.state_snoc
#print axioms StokeyLucasPrescott.StochasticApplications.cont
#print axioms StokeyLucasPrescott.StochasticApplications.start₁
#print axioms StokeyLucasPrescott.StochasticApplications.init_cons
#print axioms StokeyLucasPrescott.StochasticApplications.xState_cons
#print axioms StokeyLucasPrescott.StochasticApplications.state_cons
#print axioms StokeyLucasPrescott.StochasticApplications.ret_cons
#print axioms StokeyLucasPrescott.StochasticApplications.IsFeasible.cont
#print axioms StokeyLucasPrescott.StochasticApplications.genX
#print axioms StokeyLucasPrescott.StochasticApplications.genPlan
#print axioms StokeyLucasPrescott.StochasticApplications.xState_genPlan
#print axioms StokeyLucasPrescott.StochasticApplications.state_genPlan
#print axioms StokeyLucasPrescott.StochasticApplications.genPlan_apply
#print axioms StokeyLucasPrescott.StochasticApplications.genPlan_feasible
#print axioms StokeyLucasPrescott.StochasticApplications.lemma_9_1
#print axioms StokeyLucasPrescott.StochasticApplications.expV
#print axioms StokeyLucasPrescott.StochasticApplications.rhs
#print axioms StokeyLucasPrescott.StochasticApplications.SolvesFE
#print axioms StokeyLucasPrescott.StochasticApplications.policy
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_next
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_first
#print axioms StokeyLucasPrescott.StochasticApplications.integral_hist_zero
#print axioms StokeyLucasPrescott.StochasticApplications.integral_v_succ
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_expV
#print axioms StokeyLucasPrescott.StochasticApplications.integral_v_step
#print axioms StokeyLucasPrescott.StochasticApplications.v_ge_uN
#print axioms StokeyLucasPrescott.StochasticApplications.v_eq_uN
#print axioms StokeyLucasPrescott.StochasticApplications.SolvesFE.le
#print axioms StokeyLucasPrescott.StochasticApplications.planValue_le_of_limit
#print axioms StokeyLucasPrescott.StochasticApplications.planValue_genPlan_of_limit
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_4
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_2
#print axioms StokeyLucasPrescott.StochasticApplications.integral_ret_succ
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_ret_cont
#print axioms StokeyLucasPrescott.StochasticApplications.uN_succ
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_ret_cont
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_1
#print axioms StokeyLucasPrescott.StochasticApplications.uR
#print axioms StokeyLucasPrescott.StochasticApplications.bound_nonneg
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_ret_of_bound
#print axioms StokeyLucasPrescott.StochasticApplications.abs_term_le
#print axioms StokeyLucasPrescott.StochasticApplications.summable_terms
#print axioms StokeyLucasPrescott.StochasticApplications.tendsto_uN
#print axioms StokeyLucasPrescott.StochasticApplications.planValue_eq_uR
#print axioms StokeyLucasPrescott.StochasticApplications.abs_uN_le
#print axioms StokeyLucasPrescott.StochasticApplications.abs_uR_le
#print axioms StokeyLucasPrescott.StochasticApplications.bounds_cont
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_uR_cont
#print axioms StokeyLucasPrescott.StochasticApplications.lemma_9_3
#print axioms StokeyLucasPrescott.StochasticApplications.planValuePos
#print axioms StokeyLucasPrescott.StochasticApplications.lemma_9_3_nonneg
#print axioms StokeyLucasPrescott.StochasticApplications.Model.absF
#print axioms StokeyLucasPrescott.StochasticApplications.xState_absF
#print axioms StokeyLucasPrescott.StochasticApplications.ret_absF
#print axioms StokeyLucasPrescott.StochasticApplications.planAbs
#print axioms StokeyLucasPrescott.StochasticApplications.planAbs_eq
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_cont_plan
#print axioms StokeyLucasPrescott.StochasticApplications.planAbs_rec
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_planAbs_cont
#print axioms StokeyLucasPrescott.StochasticApplications.term_le_planAbs
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_ret_of_planAbs
#print axioms StokeyLucasPrescott.StochasticApplications.abs_term_le_planAbs
#print axioms StokeyLucasPrescott.StochasticApplications.summable_of_planAbs
#print axioms StokeyLucasPrescott.StochasticApplications.tendsto_uN_abs
#print axioms StokeyLucasPrescott.StochasticApplications.planValue_eq_uR_abs
#print axioms StokeyLucasPrescott.StochasticApplications.abs_uN_le_planAbs
#print axioms StokeyLucasPrescott.StochasticApplications.ae_planAbs_cont
#print axioms StokeyLucasPrescott.StochasticApplications.lemma_9_3_abs
#print axioms StokeyLucasPrescott.StochasticApplications.planAbs_ne_top_of_bound
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_expV
#print axioms StokeyLucasPrescott.StochasticApplications.measurableSet_policy
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_4_step
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_4_ae
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_4_abs
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_4
#print axioms StokeyLucasPrescott.StochasticApplications.hist_singleton_ne_zero
#print axioms StokeyLucasPrescott.StochasticApplications.coin
#print axioms StokeyLucasPrescott.StochasticApplications.isProbabilityMeasure_coin
#print axioms StokeyLucasPrescott.StochasticApplications.coin_singleton_ne_zero
#print axioms StokeyLucasPrescott.StochasticApplications.coinModel
#print axioms StokeyLucasPrescott.StochasticApplications.coinPlan
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_4_counterexample
#print axioms StokeyLucasPrescott.StochasticApplications.mop
#print axioms StokeyLucasPrescott.StochasticApplications.PreservesBC
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_of_abs_le
#print axioms StokeyLucasPrescott.StochasticApplications.integral_lt_integral_of_lt
#print axioms StokeyLucasPrescott.StochasticApplications.abs_mop_le
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_section
#print axioms StokeyLucasPrescott.StochasticApplications.lemma_9_5_discrete
#print axioms StokeyLucasPrescott.StochasticApplications.lemma_9_5_compact
#print axioms StokeyLucasPrescott.StochasticApplications.lemma_9_5_comb
#print axioms StokeyLucasPrescott.StochasticApplications.lemma_9_5_comb_strict
#print axioms StokeyLucasPrescott.StochasticApplications.lemma_9_5_mono
#print axioms StokeyLucasPrescott.StochasticApplications.lemma_9_5_strictMono
#print axioms StokeyLucasPrescott.StochasticApplications.lemma_9_5'
#print axioms StokeyLucasPrescott.StochasticApplications.domD
#print axioms StokeyLucasPrescott.StochasticApplications.graphA
#print axioms StokeyLucasPrescott.StochasticApplications.ContExp
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP.mk
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP.nonempty
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP.compact
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP.lhc
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP.uhc
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP.contF
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP.bddF
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP.β_pos
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP.β_lt
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP.contφ
#print axioms StokeyLucasPrescott.StochasticApplications.BoundedDP.contExp
#print axioms StokeyLucasPrescott.StochasticApplications.mem_domD
#print axioms StokeyLucasPrescott.StochasticApplications.contExp_of_preservesBC
#print axioms StokeyLucasPrescott.StochasticApplications.contExp_first
#print axioms StokeyLucasPrescott.StochasticApplications.objG
#print axioms StokeyLucasPrescott.StochasticApplications.continuousOn_objG
#print axioms StokeyLucasPrescott.StochasticApplications.continuous_integrand
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_integrand
#print axioms StokeyLucasPrescott.StochasticApplications.abs_expV_le
#print axioms StokeyLucasPrescott.StochasticApplications.bound_maxValueG
#print axioms StokeyLucasPrescott.StochasticApplications.bellman
#print axioms StokeyLucasPrescott.StochasticApplications.bellman_apply
#print axioms StokeyLucasPrescott.StochasticApplications.exists_bellman_argmax
#print axioms StokeyLucasPrescott.StochasticApplications.bellman_mono
#print axioms StokeyLucasPrescott.StochasticApplications.expV_add_const
#print axioms StokeyLucasPrescott.StochasticApplications.bellman_add_const
#print axioms StokeyLucasPrescott.StochasticApplications.blackwell
#print axioms StokeyLucasPrescott.StochasticApplications.bellman_contraction
#print axioms StokeyLucasPrescott.StochasticApplications.policy_eq_argmax
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_7b
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_6
#print axioms StokeyLucasPrescott.StochasticApplications.isClosed_graph_of_uhc
#print axioms StokeyLucasPrescott.StochasticApplications.isUHC_image_val
#print axioms StokeyLucasPrescott.StochasticApplications.exists_measurableSelection
#print axioms StokeyLucasPrescott.StochasticApplications.isClosed_graphA
#print axioms StokeyLucasPrescott.StochasticApplications.ret_mem_graphA
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_7a
#print axioms StokeyLucasPrescott.StochasticApplications.solvesFE_of_fixed
#print axioms StokeyLucasPrescott.StochasticApplications.bounded_vStar
#print axioms StokeyLucasPrescott.StochasticApplications.bounded_theorem_9_4
#print axioms StokeyLucasPrescott.StochasticApplications.isClosed_pointwise_le
#print axioms StokeyLucasPrescott.StochasticApplications.bellman_strictMono_x
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_7c
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_7
#print axioms StokeyLucasPrescott.StochasticApplications.expV_mono_z
#print axioms StokeyLucasPrescott.StochasticApplications.bellman_strictMono_z
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_11
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_7g
#print axioms StokeyLucasPrescott.StochasticApplications.dual_apply_eq_sum
#print axioms StokeyLucasPrescott.StochasticApplications.vertex
#print axioms StokeyLucasPrescott.StochasticApplications.no_separation
#print axioms StokeyLucasPrescott.StochasticApplications.eventually_mem_of_mem_interior
#print axioms StokeyLucasPrescott.StochasticApplications.cmb
#print axioms StokeyLucasPrescott.StochasticApplications.cmb_self
#print axioms StokeyLucasPrescott.StochasticApplications.IsConcaveS
#print axioms StokeyLucasPrescott.StochasticApplications.IsStrictConcaveS
#print axioms StokeyLucasPrescott.StochasticApplications.IsStrictConcaveS.isConcaveS
#print axioms StokeyLucasPrescott.StochasticApplications.Assumption910
#print axioms StokeyLucasPrescott.StochasticApplications.Assumption911
#print axioms StokeyLucasPrescott.StochasticApplications.IsAffineφ
#print axioms StokeyLucasPrescott.StochasticApplications.isClosed_concaveX
#print axioms StokeyLucasPrescott.StochasticApplications.expV_comb
#print axioms StokeyLucasPrescott.StochasticApplications.expV_comb_strict
#print axioms StokeyLucasPrescott.StochasticApplications.bellman_maps_concave
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_7d
#print axioms StokeyLucasPrescott.StochasticApplications.argmax_unique_of_strictConcave
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_7d_policy
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_8
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_7d_concave
#print axioms StokeyLucasPrescott.StochasticApplications.abs_expV_sub_le
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_7e
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_9
#print axioms StokeyLucasPrescott.StochasticApplications.convex_image_Γ
#print axioms StokeyLucasPrescott.StochasticApplications.eventually_mem_Γ
#print axioms StokeyLucasPrescott.StochasticApplications.liftS
#print axioms StokeyLucasPrescott.StochasticApplications.liftS_of_mem
#print axioms StokeyLucasPrescott.StochasticApplications.concaveOn_liftS
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_7f'
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_7f
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_10
#print axioms StokeyLucasPrescott.StochasticApplications.map_init_hist
#print axioms StokeyLucasPrescott.StochasticApplications.lintegral_init
#print axioms StokeyLucasPrescott.StochasticApplications.integral_init
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_init
#print axioms StokeyLucasPrescott.StochasticApplications.map_last_hist_const
#print axioms StokeyLucasPrescott.StochasticApplications.policyKernel
#print axioms StokeyLucasPrescott.StochasticApplications.policyKernel_apply
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_13
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_15a
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_15b
#print axioms StokeyLucasPrescott.StochasticApplications.theorem_9_14
#print axioms StokeyLucasPrescott.StochasticApplications.policyKernel'
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_policy'
#print axioms StokeyLucasPrescott.StochasticApplications.policyKernel'_apply
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_17a
#print axioms StokeyLucasPrescott.StochasticApplications.ex_9_17b
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.mk
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.β_pos
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.β_lt
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.U_cont
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.U_mono
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.f_cont
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.f_zero
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.f_mono
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.zbar_gt
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.xbar_pos
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.xbar_maintain
#print axioms StokeyLucasPrescott.StochasticApplications.growthΓ
#print axioms StokeyLucasPrescott.StochasticApplications.growthF
#print axioms StokeyLucasPrescott.StochasticApplications.growthModel
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.f_nonneg
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.zf_nonneg
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.zf_le
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.continuous_zf
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.continuous_F
#print axioms StokeyLucasPrescott.StochasticApplications.GrowthHyp.bddF
#print axioms StokeyLucasPrescott.StochasticApplications.growthF_of_mem
#print axioms StokeyLucasPrescott.StochasticApplications.isLHC_Icc_le
#print axioms StokeyLucasPrescott.StochasticApplications.isUHC_Icc_le
#print axioms StokeyLucasPrescott.StochasticApplications.growth_boundedDP
#print axioms StokeyLucasPrescott.StochasticApplications.exists_measurableSelection_Icc
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_1a
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_1b
#print axioms StokeyLucasPrescott.StochasticApplications.growth_strictMono
#print axioms StokeyLucasPrescott.StochasticApplications.growth_zf_cmb
#print axioms StokeyLucasPrescott.StochasticApplications.cmb_val
#print axioms StokeyLucasPrescott.StochasticApplications.growth_mem_cmb
#print axioms StokeyLucasPrescott.StochasticApplications.growth_F_cmb
#print axioms StokeyLucasPrescott.StochasticApplications.growth_bellman_concave
#print axioms StokeyLucasPrescott.StochasticApplications.growth_concave
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_section_v
#print axioms StokeyLucasPrescott.StochasticApplications.growth_flat_step
#print axioms StokeyLucasPrescott.StochasticApplications.growth_strictConcave
#print axioms StokeyLucasPrescott.StochasticApplications.strictConcave_integral
#print axioms StokeyLucasPrescott.StochasticApplications.growth_argmax_unique
#print axioms StokeyLucasPrescott.StochasticApplications.growth_objG
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_1c
#print axioms StokeyLucasPrescott.StochasticApplications.isFeller_const
#print axioms StokeyLucasPrescott.StochasticApplications.continuous_integral_section
#print axioms StokeyLucasPrescott.StochasticApplications.strictConcave_exchange
#print axioms StokeyLucasPrescott.StochasticApplications.strictConcaveOn_liftS
#print axioms StokeyLucasPrescott.StochasticApplications.outΓ
#print axioms StokeyLucasPrescott.StochasticApplications.outH
#print axioms StokeyLucasPrescott.StochasticApplications.outS
#print axioms StokeyLucasPrescott.StochasticApplications.outH_uniqueArgmax
#print axioms StokeyLucasPrescott.StochasticApplications.growth_argmax_eq_out
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_1d
#print axioms StokeyLucasPrescott.StochasticApplications.cexU
#print axioms StokeyLucasPrescott.StochasticApplications.cexf
#print axioms StokeyLucasPrescott.StochasticApplications.cex_hyp
#print axioms StokeyLucasPrescott.StochasticApplications.cexU_strictConcave
#print axioms StokeyLucasPrescott.StochasticApplications.cexf_concave
#print axioms StokeyLucasPrescott.StochasticApplications.cex_lipschitz
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_1d_counterexample
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_1d_not_strictMono
#print axioms StokeyLucasPrescott.StochasticApplications.hasDerivAt_of_concaveOn_of_le
#print axioms StokeyLucasPrescott.StochasticApplications.growth_rhs_le
#print axioms StokeyLucasPrescott.StochasticApplications.growth_eq_of_policy
#print axioms StokeyLucasPrescott.StochasticApplications.growth_hasDerivAt_x
#print axioms StokeyLucasPrescott.StochasticApplications.growth_concave_z
#print axioms StokeyLucasPrescott.StochasticApplications.growth_hasDerivAt_z
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_1e
#print axioms StokeyLucasPrescott.StochasticApplications.growth_bellman_mono_z
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_1f
#print axioms StokeyLucasPrescott.StochasticApplications.quadrant
#print axioms StokeyLucasPrescott.StochasticApplications.twoX
#print axioms StokeyLucasPrescott.StochasticApplications.convex_quadrant
#print axioms StokeyLucasPrescott.StochasticApplications.convex_twoX
#print axioms StokeyLucasPrescott.StochasticApplications.isCompact_twoX
#print axioms StokeyLucasPrescott.StochasticApplications.twoX_subset_quadrant
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.mk
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.β_pos
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.β_lt
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.U_cont
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.U_mono
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.f_cont
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.f_zero
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.f_mono
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.zbar_gt
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.xbar_pos
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.f_bound
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.f_le
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.f_nonneg
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.continuous_f
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.zf_nonneg
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.zf_le
#print axioms StokeyLucasPrescott.StochasticApplications.twoΓ
#print axioms StokeyLucasPrescott.StochasticApplications.twoF
#print axioms StokeyLucasPrescott.StochasticApplications.twoModel
#print axioms StokeyLucasPrescott.StochasticApplications.twoF_of_mem
#print axioms StokeyLucasPrescott.StochasticApplications.TwoHyp.continuous_F
#print axioms StokeyLucasPrescott.StochasticApplications.isLHC_twoX_le
#print axioms StokeyLucasPrescott.StochasticApplications.isUHC_twoX_le
#print axioms StokeyLucasPrescott.StochasticApplications.two_boundedDP
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_2a
#print axioms StokeyLucasPrescott.StochasticApplications.two_strictMono
#print axioms StokeyLucasPrescott.StochasticApplications.two_cmb_val
#print axioms StokeyLucasPrescott.StochasticApplications.two_assumptions
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_2b
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_2b_diff
#print axioms StokeyLucasPrescott.StochasticApplications.two_bellman_eq_of_f_eq
#print axioms StokeyLucasPrescott.StochasticApplications.cexf2
#print axioms StokeyLucasPrescott.StochasticApplications.cexf2_hyp
#print axioms StokeyLucasPrescott.StochasticApplications.cexf2_concave
#print axioms StokeyLucasPrescott.StochasticApplications.cex2_numeric
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_2b_counterexample
#print axioms StokeyLucasPrescott.StochasticApplications.twoφ
#print axioms StokeyLucasPrescott.StochasticApplications.continuous_twoφ_aux
#print axioms StokeyLucasPrescott.StochasticApplications.continuous_twoφ
#print axioms StokeyLucasPrescott.StochasticApplications.continuous_twoφ_section
#print axioms StokeyLucasPrescott.StochasticApplications.twoφ_bdd
#print axioms StokeyLucasPrescott.StochasticApplications.twoφ_attain
#print axioms StokeyLucasPrescott.StochasticApplications.le_twoφ
#print axioms StokeyLucasPrescott.StochasticApplications.twoφ_zero
#print axioms StokeyLucasPrescott.StochasticApplications.twoφ_hyp
#print axioms StokeyLucasPrescott.StochasticApplications.twoφ_concave
#print axioms StokeyLucasPrescott.StochasticApplications.twoσ
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_2d
#print axioms StokeyLucasPrescott.StochasticApplications.Cplus
#print axioms StokeyLucasPrescott.StochasticApplications.convex_Cplus
#print axioms StokeyLucasPrescott.StochasticApplications.TechHyp
#print axioms StokeyLucasPrescott.StochasticApplications.TechHyp.mk
#print axioms StokeyLucasPrescott.StochasticApplications.TechHyp.nonempty
#print axioms StokeyLucasPrescott.StochasticApplications.TechHyp.compact
#print axioms StokeyLucasPrescott.StochasticApplications.TechHyp.lhc
#print axioms StokeyLucasPrescott.StochasticApplications.TechHyp.uhc
#print axioms StokeyLucasPrescott.StochasticApplications.TechHyp.mono
#print axioms StokeyLucasPrescott.StochasticApplications.TechHyp.joint
#print axioms StokeyLucasPrescott.StochasticApplications.manyΓ
#print axioms StokeyLucasPrescott.StochasticApplications.manyF
#print axioms StokeyLucasPrescott.StochasticApplications.manyModel
#print axioms StokeyLucasPrescott.StochasticApplications.isCompact_fiber
#print axioms StokeyLucasPrescott.StochasticApplications.manyF_spec
#print axioms StokeyLucasPrescott.StochasticApplications.le_manyF
#print axioms StokeyLucasPrescott.StochasticApplications.many_boundedDP
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_manyF
#print axioms StokeyLucasPrescott.StochasticApplications.manyF_mono
#print axioms StokeyLucasPrescott.StochasticApplications.manyF_concave
#print axioms StokeyLucasPrescott.StochasticApplications.many_bellman_mono
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_3a
#print axioms StokeyLucasPrescott.StochasticApplications.many_bellman_eq
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_3a_counterexample
#print axioms StokeyLucasPrescott.StochasticApplications.techHyp_const
#print axioms StokeyLucasPrescott.StochasticApplications.ManyFeasible
#print axioms StokeyLucasPrescott.StochasticApplications.manyUtility
#print axioms StokeyLucasPrescott.StochasticApplications.exists_gammaStar
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_3b
#print axioms StokeyLucasPrescott.StochasticApplications.abs_markovOpR_le
#print axioms StokeyLucasPrescott.StochasticApplications.integrable_bcf
#print axioms StokeyLucasPrescott.StochasticApplications.fellerOp
#print axioms StokeyLucasPrescott.StochasticApplications.fellerOp_apply
#print axioms StokeyLucasPrescott.StochasticApplications.fellerOp_add
#print axioms StokeyLucasPrescott.StochasticApplications.fellerOp_smul
#print axioms StokeyLucasPrescott.StochasticApplications.fellerOp_const
#print axioms StokeyLucasPrescott.StochasticApplications.fellerOp_mono
#print axioms StokeyLucasPrescott.StochasticApplications.norm_fellerOp_le
#print axioms StokeyLucasPrescott.StochasticApplications.norm_fellerOp_iterate_le
#print axioms StokeyLucasPrescott.StochasticApplications.priceT
#print axioms StokeyLucasPrescott.StochasticApplications.priceT_contraction
#print axioms StokeyLucasPrescott.StochasticApplications.priceT_iterate_zero
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_6e_general
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_6e
#print axioms StokeyLucasPrescott.StochasticApplications.assetX
#print axioms StokeyLucasPrescott.StochasticApplications.dotR
#print axioms StokeyLucasPrescott.StochasticApplications.dotCLM
#print axioms StokeyLucasPrescott.StochasticApplications.dotCLM_apply
#print axioms StokeyLucasPrescott.StochasticApplications.continuous_dotR
#print axioms StokeyLucasPrescott.StochasticApplications.dotR_cmb
#print axioms StokeyLucasPrescott.StochasticApplications.dotR_nonneg
#print axioms StokeyLucasPrescott.StochasticApplications.dotR_le
#print axioms StokeyLucasPrescott.StochasticApplications.dotR_lt
#print axioms StokeyLucasPrescott.StochasticApplications.mem_assetX
#print axioms StokeyLucasPrescott.StochasticApplications.convex_assetX
#print axioms StokeyLucasPrescott.StochasticApplications.isCompact_assetX
#print axioms StokeyLucasPrescott.StochasticApplications.isLHC_budget
#print axioms StokeyLucasPrescott.StochasticApplications.isUHC_budget
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.mk
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.β_pos
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.β_lt
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.xbar_gt
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.U_cont
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.U_mono
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.U_conc
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.d_cont
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.d_pos
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.p_cont
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.p_pos
#print axioms StokeyLucasPrescott.StochasticApplications.assetΓ
#print axioms StokeyLucasPrescott.StochasticApplications.assetC
#print axioms StokeyLucasPrescott.StochasticApplications.assetF
#print axioms StokeyLucasPrescott.StochasticApplications.assetModel
#print axioms StokeyLucasPrescott.StochasticApplications.assetF_of_mem
#print axioms StokeyLucasPrescott.StochasticApplications.AssetHyp.continuous_F
#print axioms StokeyLucasPrescott.StochasticApplications.asset_boundedDP
#print axioms StokeyLucasPrescott.StochasticApplications.asset_cmb
#print axioms StokeyLucasPrescott.StochasticApplications.asset_rhs_le
#print axioms StokeyLucasPrescott.StochasticApplications.asset_concave
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_6ab
#print axioms StokeyLucasPrescott.StochasticApplications.assetX_mem_nhds
#print axioms StokeyLucasPrescott.StochasticApplications.asset_rhs_eq
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_6c_deriv
#print axioms StokeyLucasPrescott.StochasticApplications.dotR_add_single
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_6c_euler
#print axioms StokeyLucasPrescott.StochasticApplications.oneX
#print axioms StokeyLucasPrescott.StochasticApplications.assetC_one
#print axioms StokeyLucasPrescott.StochasticApplications.dotR_single
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_6d
#print axioms StokeyLucasPrescott.StochasticApplications.Two
#print axioms StokeyLucasPrescott.StochasticApplications.two0
#print axioms StokeyLucasPrescott.StochasticApplications.two1
#print axioms StokeyLucasPrescott.StochasticApplications.two_cases
#print axioms StokeyLucasPrescott.StochasticApplications.two0_ne_two1
#print axioms StokeyLucasPrescott.StochasticApplications.lossMeasure
#print axioms StokeyLucasPrescott.StochasticApplications.isProbabilityMeasure_lossMeasure
#print axioms StokeyLucasPrescott.StochasticApplications.integral_lossMeasure
#print axioms StokeyLucasPrescott.StochasticApplications.integral_loss_prod
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp.mk
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp.β_pos
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp.β_lt
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp.θ_nonneg
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp.θ_le
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp.wbar_pos
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp.U_cont
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp.U_mono
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp.U_zero
#print axioms StokeyLucasPrescott.StochasticApplications.w0
#print axioms StokeyLucasPrescott.StochasticApplications.searchφ
#print axioms StokeyLucasPrescott.StochasticApplications.searchF
#print axioms StokeyLucasPrescott.StochasticApplications.searchModel
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_7a
#print axioms StokeyLucasPrescott.StochasticApplications.continuous_searchF
#print axioms StokeyLucasPrescott.StochasticApplications.continuous_searchφ
#print axioms StokeyLucasPrescott.StochasticApplications.continuous_searchφ'
#print axioms StokeyLucasPrescott.StochasticApplications.search_boundedDP
#print axioms StokeyLucasPrescott.StochasticApplications.search_bellman_indep
#print axioms StokeyLucasPrescott.StochasticApplications.search_expV
#print axioms StokeyLucasPrescott.StochasticApplications.search_bellman_eq_max
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_7c
#print axioms StokeyLucasPrescott.StochasticApplications.SearchSol
#print axioms StokeyLucasPrescott.StochasticApplications.SearchSol.mk
#print axioms StokeyLucasPrescott.StochasticApplications.SearchSol.cont
#print axioms StokeyLucasPrescott.StochasticApplications.SearchSol.mono
#print axioms StokeyLucasPrescott.StochasticApplications.SearchSol.fe
#print axioms StokeyLucasPrescott.StochasticApplications.searchSol_of_fixed
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp.U_nonneg
#print axioms StokeyLucasPrescott.StochasticApplications.SearchHyp.integrable_U
#print axioms StokeyLucasPrescott.StochasticApplications.SearchSol.integrable
#print axioms StokeyLucasPrescott.StochasticApplications.SearchSol.nonneg
#print axioms StokeyLucasPrescott.StochasticApplications.SearchSol.v_zero
#print axioms StokeyLucasPrescott.StochasticApplications.SearchSol.fe'
#print axioms StokeyLucasPrescott.StochasticApplications.SearchSol.A_pos
#print axioms StokeyLucasPrescott.StochasticApplications.SearchSol.work_strictMono
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_7d
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_7e
#print axioms StokeyLucasPrescott.StochasticApplications.cdfF
#print axioms StokeyLucasPrescott.StochasticApplications.cdfF_nonneg
#print axioms StokeyLucasPrescott.StochasticApplications.cdfF_le_one
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_7f
#print axioms StokeyLucasPrescott.StochasticApplications.resΨ
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_7g
#print axioms StokeyLucasPrescott.StochasticApplications.resΨ_strictMono
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_7g_unique
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_7h_θ
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_7h_β
#print axioms StokeyLucasPrescott.StochasticApplications.tendsto_affine_rec
#print axioms StokeyLucasPrescott.StochasticApplications.stayMap
#print axioms StokeyLucasPrescott.StochasticApplications.measurable_stayMap
#print axioms StokeyLucasPrescott.StochasticApplications.searchP
#print axioms StokeyLucasPrescott.StochasticApplications.searchP_apply_ge
#print axioms StokeyLucasPrescott.StochasticApplications.searchP_adjoint
#print axioms StokeyLucasPrescott.StochasticApplications.searchLaw
#print axioms StokeyLucasPrescott.StochasticApplications.searchLaw_succ
#print axioms StokeyLucasPrescott.StochasticApplications.searchLaw_prob
#print axioms StokeyLucasPrescott.StochasticApplications.searchP_adjoint_real
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_8a
#print axioms StokeyLucasPrescott.StochasticApplications.searchLaw_Iio_tendsto
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_8b_zero
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_8b
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_8c
#print axioms StokeyLucasPrescott.StochasticApplications.triD
#print axioms StokeyLucasPrescott.StochasticApplications.triS
#print axioms StokeyLucasPrescott.StochasticApplications.triF
#print axioms StokeyLucasPrescott.StochasticApplications.triK
#print axioms StokeyLucasPrescott.StochasticApplications.tri00
#print axioms StokeyLucasPrescott.StochasticApplications.triMk
#print axioms StokeyLucasPrescott.StochasticApplications.stayV
#print axioms StokeyLucasPrescott.StochasticApplications.stay_le
#print axioms StokeyLucasPrescott.StochasticApplications.stay_lt
#print axioms StokeyLucasPrescott.StochasticApplications.abs_stayV_le
#print axioms StokeyLucasPrescott.StochasticApplications.jobT
#print axioms StokeyLucasPrescott.StochasticApplications.jobT_apply
#print axioms StokeyLucasPrescott.StochasticApplications.jobT_contraction
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_10f
#print axioms StokeyLucasPrescott.StochasticApplications.PiProps
#print axioms StokeyLucasPrescott.StochasticApplications.PiProps.mk
#print axioms StokeyLucasPrescott.StochasticApplications.PiProps.bounds
#print axioms StokeyLucasPrescott.StochasticApplications.PiProps.succ_k
#print axioms StokeyLucasPrescott.StochasticApplications.PiProps.succ_n
#print axioms StokeyLucasPrescott.StochasticApplications.PiProps.succ_nk
#print axioms StokeyLucasPrescott.StochasticApplications.jobMono
#print axioms StokeyLucasPrescott.StochasticApplications.isClosed_jobMono
#print axioms StokeyLucasPrescott.StochasticApplications.stayV_mono
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_10g
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_10h
#print axioms StokeyLucasPrescott.StochasticApplications.jobG
#print axioms StokeyLucasPrescott.StochasticApplications.job_v_le
#print axioms StokeyLucasPrescott.StochasticApplications.job_v_ge
#print axioms StokeyLucasPrescott.StochasticApplications.jobG_dist
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_10g_limit
#print axioms StokeyLucasPrescott.StochasticApplications.integral_beta_kernel
#print axioms StokeyLucasPrescott.StochasticApplications.postDensity
#print axioms StokeyLucasPrescott.StochasticApplications.postMean
#print axioms StokeyLucasPrescott.StochasticApplications.lik_mul_betaPDF
#print axioms StokeyLucasPrescott.StochasticApplications.integral_lik_mul_betaPDF
#print axioms StokeyLucasPrescott.StochasticApplications.beta_pos'
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_10b
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_10a
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_10c
#print axioms StokeyLucasPrescott.StochasticApplications.betaπ
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_10d
#print axioms StokeyLucasPrescott.StochasticApplications.betaπ_mem
#print axioms StokeyLucasPrescott.StochasticApplications.betaπ_tendsto
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_10e
#print axioms StokeyLucasPrescott.StochasticApplications.betaπ_window
#print axioms StokeyLucasPrescott.StochasticApplications.ex_10_10g_beta
