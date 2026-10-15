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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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
    IsFeasible M (start₁ M s₀ π z₁) (StochasticDP.cont π z₁) := by
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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 9.4: optimal plans follow the policy correspondence almost surely

SLP §9.1, pp. 250–253, and Exercise 9.5b.

**Theorem 9.4** (`theorem_9_4`). Let `v* ` be real-valued, measurable and solve the functional
equation, let the graph of `Γ` be measurable, and let `π*` be a feasible plan from `s₀` that
attains `v*(s₀)` and satisfies Assumption 9.3. If `β > 0`, then `π*₀ ∈ G(s₀)` and
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

namespace StokeyLucasPrescott.StochasticDP

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

/-- **The first step of Theorem 9.4** (SLP (11a) and (15)): an optimal plan's first action is in
`G(s₀)`, and its continuation is optimal from `s₁` for `Q(z₀, ·)`-almost every `z₁`. -/
theorem theorem_9_4_step (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    {v : X × Z → ℝ} (hFE : SolvesFE M v)
    (hIv : ∀ s, ∀ y ∈ M.Γ s, Integrable (fun z' => v (M.φ (s.1, y, z'), z')) (M.Q s.2))
    (hopt : ∀ s π, IsFeasible M s π → planValue M s π ≤ v s) {s : X × Z} {π : Plan Y Z}
    (hπ : IsFeasible M s π) {L : ℕ → ℝ} (hL : ∀ t h, |ret M s π t h| ≤ L t)
    (hsum : Summable fun t => M.β ^ t * L t) (hπopt : planValue M s π = v s) :
    π 0 Fin.elim0 ∈ policy M v s ∧
      ∀ᵐ z₁ ∂M.Q s.2, planValue M (start₁ M s π z₁) (cont π z₁) = v (start₁ M s π z₁) := by
  obtain ⟨h1, h2⟩ := lemma_9_3 M hφ hF hβ.le s hπ.1 hL hsum
  obtain ⟨hLc, hsumc⟩ := bounds_cont M hβ.le s π hL hsum
  have hu : uR M s π = v s := by
    rw [h1] at hπopt
    exact_mod_cast hπopt
  have hy₀ : π 0 Fin.elim0 ∈ M.Γ s := hπ.2 0 Fin.elim0
  have hcv : ∀ z₁, planValue M (start₁ M s π z₁) (cont π z₁) =
      uR M (start₁ M s π z₁) (cont π z₁) := fun z₁ => planValue_eq_uR M hβ.le _ _ (hLc z₁) hsumc
  have hle : ∀ z₁, uR M (start₁ M s π z₁) (cont π z₁) ≤ v (start₁ M s π z₁) := fun z₁ => by
    have := hopt _ _ (hπ.cont M z₁)
    rw [hcv] at this
    exact_mod_cast this
  have hIu : Integrable (fun z₁ => uR M (start₁ M s π z₁) (cont π z₁)) (M.Q s.2) :=
    (integrable_const (∑' t, M.β ^ t * L (t + 1))).mono'
      (measurable_uR_cont M hφ hF hβ.le s hπ.1 hL hsum).aestronglyMeasurable
      (Eventually.of_forall fun z₁ => by
        rw [Real.norm_eq_abs]; exact abs_uR_le M hβ.le _ _ (hLc z₁) hsumc)
  have hIv₀ : Integrable (fun z₁ => v (start₁ M s π z₁)) (M.Q s.2) := hIv s _ hy₀
  have hmono : ∫ z₁, uR M (start₁ M s π z₁) (cont π z₁) ∂M.Q s.2 ≤
      ∫ z₁, v (start₁ M s π z₁) ∂M.Q s.2 := integral_mono hIu hIv₀ hle
  have hrhs : rhs M v s (π 0 Fin.elim0) =
      ret M s π 0 Fin.elim0 + M.β * ∫ z₁, v (start₁ M s π z₁) ∂M.Q s.2 := rfl
  have hFEle := hFE.le M s _ hy₀
  have heq : ∫ z₁, uR M (start₁ M s π z₁) (cont π z₁) ∂M.Q s.2 =
      ∫ z₁, v (start₁ M s π z₁) ∂M.Q s.2 := by
    refine le_antisymm hmono (le_of_mul_le_mul_left ?_ hβ)
    linarith
  refine ⟨⟨hy₀, ?_⟩, ?_⟩
  · rw [hrhs, ← heq, ← h2, hu]
  · filter_upwards [(integral_eq_iff_of_ae_le hIu hIv₀ (Eventually.of_forall hle)).1 heq]
      with z₁ hz₁
    rw [hcv, hz₁]

/-- The almost-sure part of Theorem 9.4, by induction on the date along continuations. -/
theorem theorem_9_4_ae (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (hΓ : MeasurableSet {p : (X × Z) × Y | p.2 ∈ M.Γ p.1}) {v : X × Z → ℝ} (hv : Measurable v)
    (hFE : SolvesFE M v)
    (hIv : ∀ s, ∀ y ∈ M.Γ s, Integrable (fun z' => v (M.φ (s.1, y, z'), z')) (M.Q s.2))
    (hopt : ∀ s π, IsFeasible M s π → planValue M s π ≤ v s) (t : ℕ) :
    ∀ (s : X × Z) (π : Plan Y Z), IsFeasible M s π → ∀ L : ℕ → ℝ,
      (∀ t h, |ret M s π t h| ≤ L t) → Summable (fun t => M.β ^ t * L t) →
      planValue M s π = v s → ∀ᵐ h ∂hist M.Q t s.2, π t h ∈ policy M v (state M s π t h) := by
  induction t with
  | zero =>
    intro s π hπ L hL hsum hπopt
    refine Eventually.of_forall fun h => ?_
    have : h = Fin.elim0 := funext fun i => i.elim0
    subst this
    exact (theorem_9_4_step M hφ hF hβ hFE hIv hopt hπ hL hsum hπopt).1
  | succ t ih =>
    intro s π hπ L hL hsum hπopt
    have hae := (theorem_9_4_step M hφ hF hβ hFE hIv hopt hπ hL hsum hπopt).2
    obtain ⟨hLc, hsumc⟩ := bounds_cont M hβ.le s π hL hsum
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
    have hnull := ih _ _ hπc _ (hLc z₁) hsumc hz₁
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

/-- **Theorem 9.4** (corrected; see the module docstring). Let `v*` be real-valued, measurable
and solve the functional equation (5′), with the integral in (5′) defined; let the graph of `Γ`
be measurable and `β > 0`; and let `π*` be feasible from `s₀`, attain `v*(s₀)`, and satisfy
Assumption 9.3. Then `π*₀ ∈ G(s₀)` and `π*_t ∈ G(x_t, z_t)` `μᵗ(z₀, ·)`-almost everywhere. -/
theorem theorem_9_4 (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (hΓ : MeasurableSet {p : (X × Z) × Y | p.2 ∈ M.Γ p.1}) {v : X × Z → ℝ} (hv : Measurable v)
    (hvstar : ∀ s, vStar M s = v s) (hFE : SolvesFE M v)
    (hIv : ∀ s, ∀ y ∈ M.Γ s, Integrable (fun z' => v (M.φ (s.1, y, z'), z')) (M.Q s.2))
    {s₀ : X × Z} {π : Plan Y Z} (hπ : IsFeasible M s₀ π) (hπopt : planValue M s₀ π = vStar M s₀)
    {L : ℕ → ℝ} (hL : ∀ t h, |ret M s₀ π t h| ≤ L t) (hsum : Summable fun t => M.β ^ t * L t) :
    π 0 Fin.elim0 ∈ policy M v s₀ ∧
      ∀ t, ∀ᵐ h ∂hist M.Q t s₀.2, π t h ∈ policy M v (state M s₀ π t h) := by
  have hopt : ∀ s π, IsFeasible M s π → planValue M s π ≤ v s := fun s π hπ => by
    rw [← hvstar]
    exact le_iSup₂ (f := fun π (_ : IsFeasible M s π) => planValue M s π) π hπ
  rw [hvstar] at hπopt
  exact ⟨(theorem_9_4_step M hφ hF hβ hFE hIv hopt hπ hL hsum hπopt).1,
    fun t => theorem_9_4_ae M hφ hF hβ hΓ hv hFE hIv hopt t s₀ π hπ L hL hsum hπopt⟩

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

end StokeyLucasPrescott.StochasticDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 9.2: returns bounded on one side

SLP §9.1, p. 253. Let `F` be bounded above or below (not necessarily by zero) and `0 ≤ β < 1`.

* **Exercise 9.2a** (`ex_9_2a`): `u(π, s₀) = lim uₙ(π, s₀)` exists in `[−∞, +∞]`: `uₙ` is a
  monotone sequence plus the convergent `C Σ_{t ≤ n} βᵗ`. (That `v*` is then defined on the
  nonempty `Π(s₀)` is Lemma 9.1.)
* **Exercise 9.2b**: Theorem 9.2 holds with Exercise 9.2a in place of Assumption 9.2
  (`ex_9_2b_theorem_9_2`); Lemma 9.3 holds in the form of the book's solution — `u` is the
  difference `u⁺ − u⁻` of the values of the positive and negative parts of the returns, one of
  which is finite, and each satisfies the recursion (9) by monotone convergence
  (`ex_9_2b_lemma_9_3`); and Theorem 9.4 holds for bounded `F` (`ex_9_2b_theorem_9_4`), since
  then Assumption 9.3 holds with `L_t = sup |F|`.
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (M : Model X Y Z)

/-- A monotone real sequence plus a convergent one converges in `[−∞, +∞]`. -/
theorem exists_tendsto_ereal_of_monotone {a c : ℕ → ℝ} (ha : Monotone a) {c₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) :
    ∃ L : EReal, Tendsto (fun n => ((a n + c n : ℝ) : EReal)) atTop (𝓝 L) := by
  by_cases hb : BddAbove (range a)
  · exact ⟨((⨆ n, a n) + c₀ : ℝ),
      (continuous_coe_real_ereal.tendsto _).comp ((tendsto_atTop_ciSup ha hb).add hc)⟩
  · refine ⟨⊤, EReal.tendsto_nhds_top_iff_real.2 fun x => ?_⟩
    have h2 := (tendsto_atTop_atTop_of_monotone' ha hb).atTop_add hc
    filter_upwards [h2.eventually_gt_atTop x] with n hn
    exact EReal.coe_lt_coe_iff.2 hn

/-- An antitone real sequence plus a convergent one converges in `[−∞, +∞]`. -/
theorem exists_tendsto_ereal_of_antitone {a c : ℕ → ℝ} (ha : Antitone a) {c₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) :
    ∃ L : EReal, Tendsto (fun n => ((a n + c n : ℝ) : EReal)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_ereal_of_monotone (a := fun n => -a n) (c := fun n => -c n)
    (fun m n hmn => neg_le_neg (ha hmn)) hc.neg
  refine ⟨-L, ((continuous_neg.tendsto L).comp hL).congr fun n => ?_⟩
  simp only [Function.comp_apply, ← EReal.coe_neg]
  congr 1
  ring

variable [IsMarkovKernel M.Q]

/-- **Exercise 9.2a.** If `F` is bounded above or below and `0 ≤ β < 1`, `uₙ(π, s₀)` converges in
`[−∞, +∞]` along every plan with integrable returns. -/
theorem ex_9_2a (hβ : 0 ≤ M.β) (hβ1 : M.β < 1) {C : ℝ} (hC : (∀ p, M.F p ≤ C) ∨ ∀ p, C ≤ M.F p)
    (s₀ : X × Z) (π : Plan Y Z) (hI : ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2)) :
    ∃ L, Tendsto (fun n => (uN M s₀ π n : EReal)) atTop (𝓝 L) := by
  set c : ℕ → ℝ := fun n => C * ∑ t ∈ Finset.range (n + 1), M.β ^ t with hcdef
  have hc : Tendsto c atTop (𝓝 (C * (1 - M.β)⁻¹)) :=
    ((hasSum_geometric_of_lt_one hβ hβ1).tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)).const_mul C
  have hstep : ∀ n, (uN M s₀ π (n + 1) - c (n + 1)) - (uN M s₀ π n - c n) =
      M.β ^ (n + 1) * (∫ h, ret M s₀ π (n + 1) h ∂hist M.Q (n + 1) s₀.2 - C) := fun n => by
    simp only [uN, hcdef, Finset.sum_range_succ (n := n + 1)]
    ring
  have hconst : ∀ t, ∫ _h, C ∂hist M.Q t s₀.2 = C := fun t => by
    have := ex_8_8a M.Q t
    simp
  have hpow : ∀ n, 0 ≤ M.β ^ (n + 1) := fun n => pow_nonneg hβ _
  have hfin : ∀ L, Tendsto (fun n => ((uN M s₀ π n - c n + c n : ℝ) : EReal)) atTop (𝓝 L) →
      Tendsto (fun n => (uN M s₀ π n : EReal)) atTop (𝓝 L) := fun L hL =>
    hL.congr fun n => by rw [sub_add_cancel]
  rcases hC with hC | hC
  · obtain ⟨L, hL⟩ := exists_tendsto_ereal_of_antitone
      (a := fun n => uN M s₀ π n - c n) (antitone_nat_of_succ_le fun n => by
        have := ex_8_8a M.Q (n + 1)
        have hle : ∫ h, ret M s₀ π (n + 1) h ∂hist M.Q (n + 1) s₀.2 ≤ C :=
          (integral_mono (hI _) (integrable_const C) fun h => hC _).trans (hconst _).le
        nlinarith [hstep n, hpow n]) hc
    exact ⟨L, hfin L hL⟩
  · obtain ⟨L, hL⟩ := exists_tendsto_ereal_of_monotone
      (a := fun n => uN M s₀ π n - c n) (monotone_nat_of_le_succ fun n => by
        have := ex_8_8a M.Q (n + 1)
        have hle : C ≤ ∫ h, ret M s₀ π (n + 1) h ∂hist M.Q (n + 1) s₀.2 :=
          (hconst _).symm.le.trans (integral_mono (integrable_const C) (hI _) fun h => hC _)
        nlinarith [hstep n, hpow n]) hc
    exact ⟨L, hfin L hL⟩

/-- **Exercise 9.2b: Theorem 9.2** for `F` bounded above or below and `β < 1`, with Exercise 9.2a
in place of the convergence part of Assumption 9.2. -/
theorem ex_9_2b_theorem_9_2 (hφ : Measurable M.φ) (hβ : 0 ≤ M.β) (hβ1 : M.β < 1) {C : ℝ}
    (hC : (∀ p, M.F p ≤ C) ∨ ∀ p, C ≤ M.F p) {v : X × Z → ℝ} (hFE : SolvesFE M v)
    (s₀ : X × Z)
    (hint : ∀ π, IsFeasible M s₀ π → ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2) ∧
      Integrable (fun h => v (state M s₀ π t h)) (hist M.Q t s₀.2))
    (h7 : ∀ π, IsFeasible M s₀ π →
      Tendsto (fun t => M.β ^ t * ∫ h, v (state M s₀ π t h) ∂hist M.Q t s₀.2) atTop (𝓝 0))
    {g : ℕ → X × Z → Y} (hg : ∀ t, Measurable (g t)) (hgG : ∀ t s, g t s ∈ policy M v s) :
    (∀ π, IsFeasible M s₀ π → planValue M s₀ π ≤ v s₀) ∧
      planValue M s₀ (genPlan M s₀ g) = v s₀ ∧ vStar M s₀ = v s₀ :=
  ex_9_4 M hφ hβ hFE s₀ hint
    (fun π hπ => ex_9_2a M hβ hβ1 hC s₀ π fun t => (hint π hπ t).1) h7 hg hgG

/-- The model with returns `−F`. -/
abbrev Model.negF (M : Model X Y Z) : Model X Y Z := { M with F := fun p => -M.F p }

omit [IsMarkovKernel M.Q] in
theorem xState_negF (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) :
    xState M.negF s₀ π t = xState M s₀ π t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext h
    simp only [xState, ih]

omit [IsMarkovKernel M.Q] in
theorem ret_negF (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) :
    ret M.negF s₀ π t = fun h => -ret M s₀ π t h := by
  funext h
  simp only [ret, state, xState_negF]

/-- With `F ≤ C` and `0 ≤ β < 1`, the value of the positive part of the returns is finite. -/
theorem planValuePos_ne_top (hβ : 0 ≤ M.β) (hβ1 : M.β < 1) {C : ℝ} (hC : ∀ p, M.F p ≤ C)
    (s₀ : X × Z) (π : Plan Y Z) : planValuePos M s₀ π ≠ ⊤ := by
  have hle : planValuePos M s₀ π ≤ ∑' t, ENNReal.ofReal M.β ^ t * ENNReal.ofReal C := by
    refine ENNReal.tsum_le_tsum fun t => ?_
    have := ex_8_8a M.Q t
    rw [← ENNReal.ofReal_pow hβ]
    gcongr
    calc ∫⁻ h, ENNReal.ofReal (ret M s₀ π t h) ∂hist M.Q t s₀.2
        ≤ ∫⁻ _h, ENNReal.ofReal C ∂hist M.Q t s₀.2 :=
          lintegral_mono fun h => ENNReal.ofReal_le_ofReal (hC _)
      _ = ENNReal.ofReal C := by simp
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric] at hle
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top) hle
  exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hβ1)).ne'

/-- **Exercise 9.2b: Lemma 9.3** for `F` bounded above or below and `0 ≤ β < 1` (the book's
solution). `u(π, s₀) = u⁺ − u⁻`, where `u^±` are the values in `[0, +∞]` of the positive and
negative parts of the returns; one of them is finite; and each satisfies the recursion (9). -/
theorem ex_9_2b_lemma_9_3 (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (hβ1 : M.β < 1) {C : ℝ} (hC : (∀ p, M.F p ≤ C) ∨ ∀ p, C ≤ M.F p) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t))
    (hI : ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2)) :
    planValue M s₀ π = (planValuePos M s₀ π : EReal) - planValuePos M.negF s₀ π ∧
      (planValuePos M s₀ π ≠ ⊤ ∨ planValuePos M.negF s₀ π ≠ ⊤) ∧
      planValuePos M s₀ π = ENNReal.ofReal (ret M s₀ π 0 Fin.elim0) +
        ENNReal.ofReal M.β * ∫⁻ z₁, planValuePos M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 ∧
      planValuePos M.negF s₀ π = ENNReal.ofReal (-ret M s₀ π 0 Fin.elim0) +
        ENNReal.ofReal M.β *
          ∫⁻ z₁, planValuePos M.negF (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 := by
  have hfin : planValuePos M s₀ π ≠ ⊤ ∨ planValuePos M.negF s₀ π ≠ ⊤ := by
    rcases hC with hC | hC
    · exact Or.inl (planValuePos_ne_top M hβ hβ1 hC s₀ π)
    · exact Or.inr (planValuePos_ne_top M.negF hβ hβ1 (C := -C)
        (fun p => neg_le_neg (hC p)) s₀ π)
  refine ⟨?_, hfin, lemma_9_3_nonneg M hφ hF hβ s₀ hπ,
    lemma_9_3_nonneg M.negF hφ hF.neg hβ s₀ hπ⟩
  set A : ℕ → ℝ≥0∞ := fun n => ∑ t ∈ Finset.range (n + 1),
    ENNReal.ofReal (M.β ^ t) * ∫⁻ h, ENNReal.ofReal (ret M s₀ π t h) ∂hist M.Q t s₀.2 with hAdef
  set B : ℕ → ℝ≥0∞ := fun n => ∑ t ∈ Finset.range (n + 1),
    ENNReal.ofReal (M.β ^ t) * ∫⁻ h, ENNReal.ofReal (ret M.negF s₀ π t h) ∂hist M.Q t s₀.2
    with hBdef
  have hA : Tendsto (fun n => (A n : EReal)) atTop (𝓝 (planValuePos M s₀ π : EReal)) :=
    (continuous_coe_ennreal_ereal.tendsto _).comp
      ((ENNReal.tendsto_nat_tsum _).comp (tendsto_add_atTop_nat 1))
  have hB : Tendsto (fun n => (B n : EReal)) atTop (𝓝 (planValuePos M.negF s₀ π : EReal)) :=
    (continuous_coe_ennreal_ereal.tendsto _).comp
      ((ENNReal.tendsto_nat_tsum _).comp (tendsto_add_atTop_nat 1))
  have hAt : ∀ t, ENNReal.ofReal (M.β ^ t) *
      ∫⁻ h, ENNReal.ofReal (ret M s₀ π t h) ∂hist M.Q t s₀.2 ≠ ⊤ := fun t =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI t).lintegral_lt_top.ne
  have hBt : ∀ t, ENNReal.ofReal (M.β ^ t) *
      ∫⁻ h, ENNReal.ofReal (ret M.negF s₀ π t h) ∂hist M.Q t s₀.2 ≠ ⊤ := fun t => by
    rw [ret_negF]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI t).neg.lintegral_lt_top.ne
  have heq : ∀ n, (uN M s₀ π n : EReal) = (A n : EReal) + -(B n : EReal) := fun n => by
    rw [← EReal.coe_ennreal_toReal (ENNReal.sum_ne_top.2 fun t _ => hAt t),
      ← EReal.coe_ennreal_toReal (ENNReal.sum_ne_top.2 fun t _ => hBt t), ← EReal.coe_neg,
      ← EReal.coe_add, EReal.coe_eq_coe_iff, ENNReal.toReal_sum fun t _ => hAt t,
      ENNReal.toReal_sum fun t _ => hBt t, uN, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ret_negF, integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hI t), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hβ t)]
    ring
  refine planValue_eq M ?_
  simp_rw [heq, sub_eq_add_neg]
  refine ((EReal.continuousAt_add ?_ ?_).tendsto).comp
    (hA.prodMk_nhds ((continuous_neg.tendsto _).comp hB))
  · rcases hfin with h | h
    · exact Or.inl fun h' => h (EReal.coe_ennreal_eq_top_iff.1 h')
    · exact Or.inr fun h' => h (EReal.coe_ennreal_eq_top_iff.1 (EReal.neg_eq_bot_iff.1 h'))
  · exact Or.inl (EReal.coe_ennreal_ne_bot _)

/-- **Exercise 9.2b: Theorem 9.4** for bounded `F` and `0 < β < 1`: Assumption 9.3 holds with
`L_t = sup |F|`. -/
theorem ex_9_2b_theorem_9_4 (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (hβ1 : M.β < 1) {C : ℝ} (hC : ∀ p, |M.F p| ≤ C)
    (hΓ : MeasurableSet {p : (X × Z) × Y | p.2 ∈ M.Γ p.1}) {v : X × Z → ℝ} (hv : Measurable v)
    (hvstar : ∀ s, vStar M s = v s) (hFE : SolvesFE M v)
    (hIv : ∀ s, ∀ y ∈ M.Γ s, Integrable (fun z' => v (M.φ (s.1, y, z'), z')) (M.Q s.2))
    {s₀ : X × Z} {π : Plan Y Z} (hπ : IsFeasible M s₀ π)
    (hπopt : planValue M s₀ π = vStar M s₀) :
    π 0 Fin.elim0 ∈ policy M v s₀ ∧
      ∀ t, ∀ᵐ h ∂hist M.Q t s₀.2, π t h ∈ policy M v (state M s₀ π t h) :=
  theorem_9_4 M hφ hF hβ hΓ hv hvstar hFE hIv hπ hπopt (L := fun _ => C) (fun _ _ => hC _)
    ((summable_geometric_of_lt_one hβ.le hβ1).mul_right C)

end StokeyLucasPrescott.StochasticDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Blackwell's example: `v*` need not be measurable

SLP §9.1, pp. 253–254 (from Blackwell 1965). Let the shock never change, `Q(z, ·) = δ_z`, let
`Γ ≡ X`, and let `F(x, y, z) = 1` if `(y, z) ∈ E` and `0` otherwise, for a measurable
`E ⊆ X × Z`, with `0 ≤ β < 1`. Then `v*(x, z) = 1/(1 − β)` if `z ∈ Proj_Z E` and `0` otherwise,
the optimum being attained by a constant plan `π_t ≡ ŷ` with `(ŷ, z) ∈ E` (`blackwell_example`).
So `v*` is measurable only if `Proj_Z E` is. For `X = Z = [0, 1]` there are Borel sets `E` whose
projection is not Borel (Souslin; Behnke et al. 1974); that construction is not in Mathlib, so the
example is stated for any `E` whose projection is not measurable.
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- Blackwell's model (first formulation): constant shocks, `Γ ≡ X`, `F = 1_E(y, z)`. -/
noncomputable def blackwellModel (E : Set (X × Z)) (β : ℝ) : Model X X Z :=
  Model.first Kernel.id (fun _ => univ) (fun p => E.indicator 1 (p.2.1, p.2.2)) β

/-- With constant shocks, `μᵗ(z, ·)` is the point mass at the constant history. -/
theorem hist_id (t : ℕ) (z : Z) :
    hist (Kernel.id : Kernel Z Z) t z = Measure.dirac fun _ => z := by
  induction t with
  | zero =>
    have : (fun _ : Fin 0 => z) = Fin.elim0 := funext fun i => i.elim0
    rw [this]
    rfl
  | succ t ih =>
    have := ex_8_8a (Kernel.id : Kernel Z Z) t
    rw [hist, Kernel.comp_id, Kernel.map_apply _ (measurable_cons t), Kernel.prod_apply,
      Kernel.id_apply, ih, Measure.dirac_prod_dirac, Measure.map_dirac' (measurable_cons t)]
    congr 1
    funext i
    exact Fin.cases rfl (fun j => rfl) i

omit [MeasurableSpace Z] in
theorem lastState_const (z : Z) (t : ℕ) : lastState z (fun _ : Fin t => z) = z := by
  cases t <;> rfl

/-- The value of `n + 1` periods of a feasible plan in Blackwell's model. -/
theorem uN_blackwell {E : Set (X × Z)} (hE : MeasurableSet E) (β : ℝ) (s : X × Z)
    {π : Plan X Z} (hπ : ∀ t, Measurable (π t)) (n : ℕ) :
    uN (blackwellModel E β) s π n = ∑ t ∈ Finset.range (n + 1),
      β ^ t * E.indicator 1 (π t fun _ => s.2, s.2) := by
  have hF : Measurable (blackwellModel E β).F :=
    (measurable_one.indicator hE).comp (measurable_snd.fst.prodMk measurable_snd.snd)
  refine Finset.sum_congr rfl fun t _ => ?_
  have hm := measurable_ret (blackwellModel E β) measurable_snd.fst hF s hπ t
  change β ^ t * ∫ h, ret (blackwellModel E β) s π t h ∂hist Kernel.id t s.2 = _
  rw [hist_id, integral_dirac' _ _ hm.stronglyMeasurable]
  change β ^ t * E.indicator 1 (π t _, lastState s.2 _) = _
  rw [lastState_const]

open Classical in
/-- **Blackwell's example.** `v*(x, z) = 1/(1 − β)` on `z ∈ Proj_Z E`, attained by a constant
plan, and `v* = 0` off it; so if `Proj_Z E` is not measurable, neither is `v*`. -/
theorem blackwell_example [Nonempty X] {E : Set (X × Z)} (hE : MeasurableSet E) {β : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) :
    (∀ s : X × Z, vStar (blackwellModel E β) s =
      if s.2 ∈ Prod.snd '' E then (((1 - β)⁻¹ : ℝ) : EReal) else 0) ∧
    (∀ s : X × Z, s.2 ∈ Prod.snd '' E → ∃ y : X,
      planValue (blackwellModel E β) s (fun _ _ => y) = vStar (blackwellModel E β) s) ∧
    (¬MeasurableSet (Prod.snd '' E) → ¬Measurable (vStar (blackwellModel E β))) := by
  set M := blackwellModel E β with hMdef
  have hgeom : HasSum (fun t => β ^ t) (1 - β)⁻¹ := hasSum_geometric_of_lt_one hβ hβ1
  have hind : ∀ p : X × Z, E.indicator (1 : X × Z → ℝ) p ∈ Icc (0 : ℝ) 1 := fun p => by
    by_cases hp : p ∈ E <;> simp [hp]
  -- every feasible plan: `uₙ` is monotone, bounded by `1/(1 − β)`, and zero off the projection
  have hplan : ∀ s : X × Z, ∀ π : Plan X Z, IsFeasible M s π →
      planValue M s π = ⨆ n, (uN M s π n : EReal) ∧
      planValue M s π ≤ (((1 - β)⁻¹ : ℝ) : EReal) ∧
      (s.2 ∉ Prod.snd '' E → planValue M s π = 0) := by
    intro s π hπ
    have hu := uN_blackwell hE β s hπ.1
    have hmono : Monotone fun n => (uN M s π n : EReal) := by
      refine monotone_nat_of_le_succ fun n => EReal.coe_le_coe_iff.2 ?_
      rw [hu, hu, Finset.sum_range_succ (n := n + 1)]
      exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hβ _) (hind _).1)
    have hlim := tendsto_atTop_iSup hmono
    refine ⟨planValue_eq M hlim, ?_, fun hz => ?_⟩
    · rw [planValue_eq M hlim]
      refine iSup_le fun n => EReal.coe_le_coe_iff.2 ?_
      rw [hu, ← hgeom.tsum_eq]
      refine (Finset.sum_le_sum fun t _ => ?_).trans
        (hgeom.summable.sum_le_tsum _ fun t _ => pow_nonneg hβ t)
      exact mul_le_of_le_one_right (pow_nonneg hβ t) (hind _).2
    · have h0 : ∀ n, (uN M s π n : EReal) = 0 := fun n => by
        rw [hu, Finset.sum_eq_zero fun t _ => ?_, EReal.coe_zero]
        rw [indicator_of_notMem (a := (π t fun _ => s.2, s.2)) fun hmem => hz ⟨_, hmem, rfl⟩,
          mul_zero]
      rw [planValue_eq M hlim]
      simp [h0]
  have hconst : ∀ s : X × Z, ∀ y : X, IsFeasible M s fun _ _ => y := fun s y =>
    ⟨fun _ => measurable_const, fun _ _ => mem_univ _⟩
  have hattain : ∀ s : X × Z, ∀ y : X, (y, s.2) ∈ E →
      planValue M s (fun _ _ => y) = (((1 - β)⁻¹ : ℝ) : EReal) := fun s y hy => by
    have hu : ∀ n, uN M s (fun _ _ => y) n = ∑ t ∈ Finset.range (n + 1),
        β ^ t * E.indicator 1 (y, s.2) := uN_blackwell hE β s fun _ => measurable_const
    have ht : Tendsto (fun n => uN M s (fun _ _ => y) n) atTop (𝓝 (1 - β)⁻¹) := by
      simp only [hu, indicator_of_mem hy, Pi.one_apply, mul_one]
      exact hgeom.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact planValue_eq M ((continuous_coe_real_ereal.tendsto _).comp ht)
  have hle : ∀ s : X × Z, vStar M s ≤ (((1 - β)⁻¹ : ℝ) : EReal) := fun s =>
    iSup₂_le fun π hπ => (hplan s π hπ).2.1
  have hval : ∀ s : X × Z, vStar M s =
      if s.2 ∈ Prod.snd '' E then (((1 - β)⁻¹ : ℝ) : EReal) else 0 := by
    intro s
    split_ifs with hz
    · obtain ⟨⟨y, z⟩, hy, rfl⟩ := hz
      refine le_antisymm (hle s) ?_
      rw [← hattain s y hy]
      exact le_iSup₂ (f := fun π (_ : IsFeasible M s π) => planValue M s π) _ (hconst s y)
    · obtain ⟨y⟩ := ‹Nonempty X›
      refine le_antisymm (iSup₂_le fun π hπ => ((hplan s π hπ).2.2 hz).le) ?_
      rw [← (hplan s _ (hconst s y)).2.2 hz]
      exact le_iSup₂ (f := fun π (_ : IsFeasible M s π) => planValue M s π) _ (hconst s y)
  refine ⟨hval, fun s hz => ?_, fun hP hmeas => hP ?_⟩
  · obtain ⟨⟨y, z⟩, hy, hzs⟩ := hz
    refine ⟨y, ?_⟩
    rw [hval]
    simp only [show s.2 ∈ Prod.snd '' E from ⟨_, hy, hzs⟩, ↓reduceIte]
    exact hattain s y (hzs ▸ hy)
  · obtain ⟨x₀⟩ := ‹Nonempty X›
    have hne : (((1 - β)⁻¹ : ℝ) : EReal) ≠ 0 := by
      rw [Ne, EReal.coe_eq_zero]
      exact inv_ne_zero (sub_pos.2 hβ1).ne'
    have hset : Prod.snd '' E =
        (fun z => (x₀, z)) ⁻¹' (vStar M ⁻¹' {(((1 - β)⁻¹ : ℝ) : EReal)}) := by
      ext z
      simp only [mem_preimage, mem_singleton_iff, hval]
      split_ifs with hz
      · exact iff_of_true hz rfl
      · exact iff_of_false hz fun h => hne h.symm
    rw [hset]
    exact (hmeas (measurableSet_singleton _)).preimage measurable_prodMk_left

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- `θx + (1 − θ)x′` in the convex set `S`. -/
def cmb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} (hS : Convex ℝ S)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x x' : S) : S :=
  ⟨θ • x.1 + (1 - θ) • x'.1, hS x.2 x'.2 h0 (by linarith) (by ring)⟩

theorem cmb_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    (hS : Convex ℝ S) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : S) : cmb hS h0 h1 x x = x := by
  ext1; simp only [cmb]; rw [← add_smul]; simp

variable {l m : ℕ} {SX : Set (Fin l → ℝ)} {SY : Set (Fin m → ℝ)}

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

omit [MeasurableSpace Z] in
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

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {l m : ℕ} {SX : Set (Fin l → ℝ)} {SY : Set (Fin m → ℝ)}
  {hX : Convex ℝ SX} {hY : Convex ℝ SY}
variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
variable (M : Model SX SY Z) [IsMarkovKernel M.Q] [OpensMeasurableSpace Z]

/-- **Exercise 9.7d** (corrected, `φ(·, ·, z′)` concave). With the hypotheses of part (c) —
Assumptions 9.8 and 9.9 and `φ(·, y, z′)` nondecreasing — and
`θφ(x, y, z′) + (1 − θ)φ(x′, y′, z′) ≤ φ(θ(x, y) + (1 − θ)(x′, y′), z′)`, the fixed point `v(·, z)`
is strictly concave and strictly increasing. -/
theorem ex_9_7d_concave (h : BoundedDP M) (h910 : Assumption910 hX hY M)
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
/-- Under Assumption 9.11 the values of `Γ` are convex subsets of `ℝᵐ`. -/
theorem convex_image_Γ (h911 : Assumption911 hX hY M) (s : SX × Z) :
    Convex ℝ (Subtype.val '' M.Γ s) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have := h911 s.2 s.1 y s.1 y' hy hy' a ha (by linarith)
  rw [cmb_self] at this
  exact ⟨_, this, rfl⟩

omit [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] in
/-- If `g₀` is interior to `Γ(x₀, z₀)`, then `g₀ ∈ Γ(x, z₀)` for all `x` near `x₀`. -/
theorem eventually_mem_Γ (hl : ∀ s, IsLHC M.Γ s) (h911 : Assumption911 hX hY M) {x₀ : SX} {z₀ : Z}
    {g₀ : SY} (hg : g₀.1 ∈ interior (Subtype.val '' M.Γ (x₀, z₀))) :
    ∀ᶠ x in 𝓝 x₀, g₀ ∈ M.Γ (x, z₀) := by
  have hlhc : IsLHC (fun x => Subtype.val '' M.Γ (x, z₀)) x₀ := by
    refine ⟨(hl (x₀, z₀)).1.image _, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ xs hxs
    obtain ⟨N, ys, hys, hlim⟩ := (hl (x₀, z₀)).2 y hy (fun n => (xs n, z₀))
      (hxs.prodMk_nhds tendsto_const_nhds)
    exact ⟨N, fun n => (ys n).1, fun n hn => ⟨ys n, hys n hn, rfl⟩,
      (continuous_subtype_val.tendsto y).comp hlim⟩
  have hseq : ∀ xs : ℕ → SX, Tendsto xs atTop (𝓝 x₀) → ∀ᶠ n in atTop, g₀ ∈ M.Γ (xs n, z₀) :=
    fun xs hxs => (eventually_mem_of_mem_interior (fun x => convex_image_Γ M h911 (x, z₀))
      hlhc hg hxs).mono fun n ⟨y, hy, hyg⟩ => Subtype.ext hyg ▸ hy
  exact eventually_iff_seq_eventually.2 hseq

/-- A function on `X ⊆ ℝˡ` extended by zero. -/
noncomputable def liftS (f : SX → ℝ) (x : Fin l → ℝ) : ℝ := by
  classical exact if hx : x ∈ SX then f ⟨x, hx⟩ else 0

theorem liftS_of_mem (f : SX → ℝ) {x : Fin l → ℝ} (hx : x ∈ SX) : liftS f x = f ⟨x, hx⟩ := by
  simp only [liftS, hx, ↓reduceDIte]

/-- A concave function on `X` is concave on `X ⊆ ℝˡ` after extension. -/
theorem concaveOn_liftS {f : SX → ℝ} (hf : IsConcaveS hX f) : ConcaveOn ℝ SX (liftS f) := by
  refine ⟨hX, fun x hx y hy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hmem : a • x + b • y ∈ SX := hX hx hy ha hb hab
  rw [liftS_of_mem f hx, liftS_of_mem f hy, liftS_of_mem f hmem, smul_eq_mul, smul_eq_mul]
  have := hf ⟨x, hx⟩ ⟨y, hy⟩ a ha ha1
  subst hb'
  exact this

/-- **Exercise 9.7f.** Let `φ(x, y, z′)` not depend on `x`, let `x₀ ∈ int X` and
`g(x₀, z₀) ∈ int Γ(x₀, z₀)`, and let `x ↦ F(x, g(x₀, z₀), z₀)` have derivative `DF` at `x₀`
(Assumption 9.12). Then `v(·, z₀)` is differentiable at `x₀` with derivative `DF`, that is,
`vᵢ(x₀, z₀) = Fᵢ[x₀, g(x₀, z₀), z₀]`. -/
theorem ex_9_7f [Nonempty SY] (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M) (haff : IsAffineφ hX hY M)
    (hinj : ∀ x y y' z', y ≠ y' → M.φ (x, y, z') ≠ M.φ (x, y', z')) {v : SX × Z →ᵇ ℝ}
    (hv : bellman M h v = v) (hφx : ∀ x x' y z', M.φ (x, y, z') = M.φ (x', y, z'))
    {x₀ : SX} {z₀ : Z} (hint : SX ∈ 𝓝 x₀.1)
    (hg : (argmaxFn M.Γ (objG M v) (x₀, z₀)).1 ∈ interior (Subtype.val '' M.Γ (x₀, z₀)))
    {DF : (Fin l → ℝ) →L[ℝ] ℝ}
    (hF : HasFDerivAt (liftS fun x => M.F (x, argmaxFn M.Γ (objG M v) (x₀, z₀), z₀)) DF x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) DF x₀.1 := by
  set g₀ := argmaxFn M.Γ (objG M v) (x₀, z₀)
  obtain ⟨hU, -, -⟩ := ex_9_7d_policy M h h910 h911 haff hinj hv
  have hvc := ex_9_7d M h h910 h911 haff hv z₀
  set c := M.β * expV M v (x₀, z₀) g₀
  set W : (Fin l → ℝ) → ℝ := fun x => liftS (fun x => M.F (x, g₀, z₀)) x + c
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
    have h1 := eventually_mem_Γ M h.lhc h911 hg
    rw [nhds_subtype, eventually_comap] at h1
    filter_upwards [h1, hint] with x hx hxS
    simp only [W, liftS_of_mem _ hxS]
    rw [hvx (⟨x, hxS⟩, z₀)]
    have := le_maxValue (continuousOn_objG M h v) (h.compact _) (hx ⟨x, hxS⟩ rfl)
    simp only [objG, rhs] at this
    rw [hexp] at this
    exact this
  exact theorem_4_10 (concaveOn_liftS hvc.isConcaveS) hint hW heq hle

/-- **Theorem 9.10** (first formulation). Under Assumptions 9.4–9.7 and 9.10–9.12, if
`x₀ ∈ int X` and `g(x₀, z₀) ∈ int Γ(x₀, z₀)`, then `v(·, z₀)` is differentiable at `x₀` with
`vᵢ(x₀, z₀) = Fᵢ[x₀, g(x₀, z₀), z₀]`. -/
theorem theorem_9_10 [Nonempty SX] (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : SX × Z → Set SX)
    (F : SX × SX × Z → ℝ) (β : ℝ) (h : BoundedDP (Model.first Q Γ F β))
    (h910 : Assumption910 hX hX (Model.first Q Γ F β))
    (h911 : Assumption911 hX hX (Model.first Q Γ F β)) {v : SX × Z →ᵇ ℝ}
    (hv : bellman (Model.first Q Γ F β) h v = v) {x₀ : SX} {z₀ : Z} (hint : SX ∈ 𝓝 x₀.1)
    (hg : (argmaxFn Γ (objG (Model.first Q Γ F β) v) (x₀, z₀)).1 ∈
      interior (Subtype.val '' Γ (x₀, z₀)))
    {DF : (Fin l → ℝ) →L[ℝ] ℝ}
    (hF : HasFDerivAt (liftS fun x =>
      F (x, argmaxFn Γ (objG (Model.first Q Γ F β) v) (x₀, z₀), z₀)) DF x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) DF x₀.1 :=
  ex_9_7f (Model.first Q Γ F β) h h910 h911 (fun _ _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ hne => hne) hv (fun _ _ _ _ => rfl) hint hg hF

end StokeyLucasPrescott.StochasticDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The space `H(S)` of functions homogeneous of degree one in `x`

SLP §9.3, pp. 271–272 (and Exercise 4.7, which the book cites). The endogenous state space is a
cone `X` in a real normed space (`x ∈ X`, `λ ≥ 0` imply `λx ∈ X`). Functions on `S = X × Z` that
are continuous, homogeneous of degree one in `x`, and satisfy `|f(x, z)| ≤ M‖x‖` form `H(S)`
(`InHS`), normed by (2), `‖f‖ = sup_z sup_{‖x‖ = 1} |f(x, z)|` (`hnormS`).

* `abs_le_hnormS`: `|f(x, z)| ≤ ‖f‖‖x‖` on `H(S)`.
* `hnormS_norm`, `hnormS_complete`: `‖·‖` is a norm on `H(S)`, and `H(S)` is complete
  (Exercise 4.7a, with the shock).
* `contraction_HS`: monotone operators on `H(S)` that discount by `γ` in the sense
  `T(f + a‖x‖) ≤ Tf + γa‖x‖` satisfy `‖Tf − Tg‖ ≤ γ‖f − g‖` (Theorem 4.12).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.StochasticDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E}
variable {Z : Type*} [MetricSpace Z]

/-- `X` is a cone. -/
def IsCone (X : Set E) : Prop := ∀ x ∈ X, ∀ a : ℝ, 0 ≤ a → a • x ∈ X

/-- `ax` in the cone `X`, for `a ≥ 0`. -/
def csmul (hX : IsCone X) {a : ℝ} (ha : 0 ≤ a) (x : X) : X := ⟨a • x.1, hX x.1 x.2 a ha⟩

/-- `f : X × Z → ℝ` is in `H(S)`: continuous, homogeneous of degree one in `x`, and
`|f(x, z)| ≤ M‖x‖`. -/
def InHS (hX : IsCone X) (f : X × Z → ℝ) : Prop :=
  Continuous f ∧ (∀ x z (a : ℝ) (ha : 0 ≤ a), f (csmul hX ha x, z) = a * f (x, z)) ∧
    ∃ M, ∀ p : X × Z, |f p| ≤ M * ‖p.1.1‖

/-- The norm (2), p. 272: `‖f‖ = sup_z sup_{‖x‖ = 1} |f(x, z)|`. -/
noncomputable def hnormS (X : Set E) (f : X × Z → ℝ) : ℝ :=
  ⨆ p : {p : X × Z // ‖p.1.1‖ = 1}, |f p.1|

variable {hX : IsCone X}

omit [NormedSpace ℝ E] [MetricSpace Z] in
theorem hnormS_nonneg (f : X × Z → ℝ) : 0 ≤ hnormS X f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

omit [NormedSpace ℝ E] [MetricSpace Z] in
theorem bddAbove_sphereS {f : X × Z → ℝ} {M : ℝ} (hM : ∀ p : X × Z, |f p| ≤ M * ‖p.1.1‖) :
    BddAbove (range fun p : {p : X × Z // ‖p.1.1‖ = 1} => |f p.1|) :=
  ⟨M, by rintro _ ⟨p, rfl⟩; simpa [p.2] using hM p.1⟩

omit [MetricSpace Z] in
/-- On `H(S)`, `|f(x, z)| ≤ ‖f‖‖x‖`. -/
theorem abs_le_hnormS {f : X × Z → ℝ} (hhom : ∀ x z (a : ℝ) (ha : 0 ≤ a),
    f (csmul hX ha x, z) = a * f (x, z)) {M : ℝ} (hM : ∀ p : X × Z, |f p| ≤ M * ‖p.1.1‖)
    (p : X × Z) : |f p| ≤ hnormS X f * ‖p.1.1‖ := by
  obtain ⟨x, z⟩ := p
  rcases eq_or_ne x.1 0 with h0 | h0
  · have : x = csmul hX le_rfl x := Subtype.ext (by simp [csmul, h0])
    rw [this, hhom, zero_mul, abs_zero]
    exact mul_nonneg (hnormS_nonneg f) (norm_nonneg _)
  · have hn : 0 < ‖x.1‖ := norm_pos_iff.2 h0
    set u : X := csmul hX (inv_nonneg.2 hn.le) x
    have hu : ‖u.1‖ = 1 := by
      simp only [u, csmul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    have hxu : x = csmul hX hn.le u := Subtype.ext (by
      simp only [u, csmul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul])
    change |f (x, z)| ≤ hnormS X f * ‖x.1‖
    conv_lhs => rw [hxu, hhom, abs_mul, abs_of_pos hn, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (le_ciSup (bddAbove_sphereS hM) (⟨(u, z), hu⟩ : {p : X × Z // ‖p.1.1‖ = 1})) hn.le

theorem abs_le_hnormS' {f : X × Z → ℝ} (hf : InHS hX f) (p : X × Z) :
    |f p| ≤ hnormS X f * ‖p.1.1‖ :=
  abs_le_hnormS hf.2.1 hf.2.2.choose_spec p

omit [NormedSpace ℝ E] [MetricSpace Z] in
theorem hnormS_le {f : X × Z → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ p : X × Z, ‖p.1.1‖ = 1 → |f p| ≤ C) : hnormS X f ≤ C :=
  Real.iSup_le (fun p => h p.1 p.2) hC

theorem inHS_sub {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) : InHS hX (f - g) := by
  obtain ⟨M, hM⟩ := hf.2.2
  obtain ⟨N, hN⟩ := hg.2.2
  refine ⟨hf.1.sub hg.1, fun x z a ha => by simp [hf.2.1, hg.2.1, mul_sub], M + N,
    fun p => ?_⟩
  simp only [Pi.sub_apply]
  calc |f p - g p| ≤ |f p| + |g p| := abs_sub _ _
    _ ≤ M * ‖p.1.1‖ + N * ‖p.1.1‖ := add_le_add (hM p) (hN p)
    _ = (M + N) * ‖p.1.1‖ := by ring

theorem inHS_add {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) : InHS hX (f + g) := by
  obtain ⟨M, hM⟩ := hf.2.2
  obtain ⟨N, hN⟩ := hg.2.2
  refine ⟨hf.1.add hg.1, fun x z a ha => by simp [hf.2.1, hg.2.1, mul_add], M + N,
    fun p => ?_⟩
  simp only [Pi.add_apply]
  calc |f p + g p| ≤ |f p| + |g p| := abs_add_le _ _
    _ ≤ M * ‖p.1.1‖ + N * ‖p.1.1‖ := add_le_add (hM p) (hN p)
    _ = (M + N) * ‖p.1.1‖ := by ring

theorem inHS_smul {f : X × Z → ℝ} (hf : InHS hX f) (r : ℝ) : InHS hX (r • f) := by
  obtain ⟨M, hM⟩ := hf.2.2
  refine ⟨hf.1.const_smul r, fun x z a ha => by simp [hf.2.1]; ring, |r| * M, fun p => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hM p) (abs_nonneg r)

theorem inHS_zero : InHS hX (0 : X × Z → ℝ) :=
  ⟨continuous_const, fun _ _ _ _ => by simp, 0, fun _ => by simp⟩

/-- `x ↦ ‖x‖` is in `H(S)`. -/
theorem inHS_norm : InHS hX fun p : X × Z => ‖p.1.1‖ :=
  ⟨(continuous_subtype_val.comp continuous_fst).norm,
    fun x z a ha => by simp [csmul, norm_smul, abs_of_nonneg ha], 1, fun p => by simp⟩

/-- **Exercise 4.7a for `H(S)` (norm).** `‖·‖` of (2) is a norm on `H(S)`. -/
theorem hnormS_norm {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) (r : ℝ) :
    0 ≤ hnormS X f ∧ (hnormS X f = 0 ↔ f = 0) ∧ hnormS X (r • f) = |r| * hnormS X f ∧
      hnormS X (f + g) ≤ hnormS X f + hnormS X g := by
  refine ⟨hnormS_nonneg f, ⟨fun h0 => funext fun p => ?_, fun h => ?_⟩, ?_, ?_⟩
  · have := abs_le_hnormS' hf p
    rw [h0, zero_mul] at this
    exact abs_nonpos_iff.1 this
  · subst h; simp [hnormS]
  · simp only [hnormS, Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [Real.mul_iSup_of_nonneg (abs_nonneg r)]
  · refine hnormS_le (add_nonneg (hnormS_nonneg f) (hnormS_nonneg g)) fun p hp => ?_
    have h1 := abs_le_hnormS' hf p
    have h2 := abs_le_hnormS' hg p
    rw [hp, mul_one] at h1 h2
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem hnormS_symm {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) :
    hnormS X (g - f) = hnormS X (f - g) := by
  have := (hnormS_norm (inHS_sub hf hg) (inHS_sub hf hg) (-1)).2.2.1
  rw [abs_neg, abs_one, one_mul] at this
  rw [← this]; congr 1; funext p; simp

/-- The triangle inequality for `‖f − h‖` on `H(S)`. -/
theorem hnormS_sub_le {f g h : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) (hh : InHS hX h) :
    hnormS X (f - h) ≤ hnormS X (f - g) + hnormS X (g - h) := by
  have := (hnormS_norm (inHS_sub hf hg) (inHS_sub hg hh) 1).2.2.2
  rwa [sub_add_sub_cancel] at this

/-- **Exercise 4.7a for `H(S)` (completeness).** A sequence in `H(S)` that is Cauchy for `‖·‖`
converges in `‖·‖` to an element of `H(S)`. -/
theorem hnormS_complete {f : ℕ → X × Z → ℝ} (hf : ∀ n, InHS hX (f n))
    (hc : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, hnormS X (f m - f n) < ε) :
    ∃ g, InHS hX g ∧ Tendsto (fun n => hnormS X (f n - g)) atTop (𝓝 0) := by
  -- pointwise Cauchy, hence a pointwise limit
  have hpt : ∀ p : X × Z, CauchySeq fun n => f n p := fun p =>
    Metric.cauchySeq_iff.2 fun ε hε => by
      obtain ⟨N, hN⟩ := hc (ε / (‖p.1.1‖ + 1)) (by positivity)
      refine ⟨N, fun m hm n hn => ?_⟩
      have h := abs_le_hnormS' (inHS_sub (hf m) (hf n)) p
      rw [Real.dist_eq]
      simp only [Pi.sub_apply] at h
      calc |f m p - f n p| ≤ hnormS X (f m - f n) * ‖p.1.1‖ := h
        _ ≤ ε / (‖p.1.1‖ + 1) * ‖p.1.1‖ :=
            mul_le_mul_of_nonneg_right (hN m hm n hn).le (norm_nonneg _)
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg p.1.1]
  choose g hg using fun p => cauchySeq_tendsto_of_complete (hpt p)
  -- `|fₙ(p) − g(p)| ≤ ε‖x‖` from some `N` on
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ p : X × Z, |f n p - g p| ≤ ε * ‖p.1.1‖ := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun n hn p => ?_⟩
    have hlim : Tendsto (fun m => |f n p - f m p|) atTop (𝓝 |f n p - g p|) :=
      ((tendsto_const_nhds.sub (hg p)).abs)
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
    have h := abs_le_hnormS' (inHS_sub (hf n) (hf m)) p
    simp only [Pi.sub_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hN n hn m hm).le (norm_nonneg _))
  -- `g` is continuous: locally uniform limit
  have hgc : Continuous g := by
    refine TendstoLocallyUniformly.continuous (F := f) (p := atTop) ?_
      (Frequently.of_forall fun n => (hf n).1)
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε p
    refine ⟨Metric.ball p 1, Metric.ball_mem_nhds p one_pos, ?_⟩
    obtain ⟨N, hN⟩ := hunif (ε / (‖p.1.1‖ + 2)) (by positivity)
    refine eventually_atTop.2 ⟨N, fun n hn q hq => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    have hq' : ‖q.1.1‖ ≤ ‖p.1.1‖ + 1 := by
      have hd : dist q p < 1 := Metric.mem_ball.1 hq
      have hd1 : dist q.1 p.1 < 1 :=
        (show dist q.1 p.1 ≤ dist q p by rw [Prod.dist_eq]; exact le_max_left _ _).trans_lt hd
      rw [Subtype.dist_eq, dist_eq_norm] at hd1
      have := norm_sub_norm_le q.1.1 p.1.1
      linarith
    calc |f n q - g q| ≤ ε / (‖p.1.1‖ + 2) * ‖q.1.1‖ := hN n hn q
      _ ≤ ε / (‖p.1.1‖ + 2) * (‖p.1.1‖ + 1) := mul_le_mul_of_nonneg_left hq' (by positivity)
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg p.1.1]
  -- `g` is homogeneous and bounded
  have hghom : ∀ x z (a : ℝ) (ha : 0 ≤ a), g (csmul hX ha x, z) = a * g (x, z) :=
    fun x z a ha => tendsto_nhds_unique (hg _) (by
      simp only [(hf _).2.1]
      exact (hg (x, z)).const_mul a)
  obtain ⟨N, hN⟩ := hunif 1 one_pos
  obtain ⟨M, hM⟩ := (hf N).2.2
  have hgb : ∀ p : X × Z, |g p| ≤ (M + 1) * ‖p.1.1‖ := fun p => by
    have := hN N le_rfl p
    calc |g p| ≤ |f N p| + |f N p - g p| := by
          have := abs_sub (f N p) (f N p - g p)
          rwa [sub_sub_cancel] at this
      _ ≤ M * ‖p.1.1‖ + 1 * ‖p.1.1‖ := add_le_add (hM p) this
      _ = (M + 1) * ‖p.1.1‖ := by ring
  refine ⟨g, ⟨hgc, hghom, M + 1, hgb⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N', hN'⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N', fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnormS_nonneg _)]
  refine (hnormS_le (half_pos hε).le fun p hp => ?_).trans_lt (half_lt_self hε)
  have := hN' n hn p
  rwa [hp, mul_one] at this

/-- **Theorem 4.12 on `H(S)`.** Let `T` be monotone on `H(S)` and discount in the sense
`T(f + a‖x‖) ≤ Tf + γa‖x‖` for `a ≥ 0`. Then `‖Tf − Tg‖ ≤ γ‖f − g‖` on `H(S)`. -/
theorem contraction_HS {T : (X × Z → ℝ) → (X × Z → ℝ)} {γ : ℝ} (hγ : 0 ≤ γ)
    (hmono : ∀ f g, InHS hX f → InHS hX g → f ≤ g → T f ≤ T g)
    (hdisc : ∀ f, InHS hX f → ∀ a : ℝ, 0 ≤ a →
      T (fun p => f p + a * ‖p.1.1‖) ≤ fun p => T f p + γ * a * ‖p.1.1‖)
    {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) :
    hnormS X (T f - T g) ≤ γ * hnormS X (f - g) := by
  have hle : ∀ f g, InHS hX f → InHS hX g →
      T f ≤ fun p => T g p + γ * hnormS X (f - g) * ‖p.1.1‖ := fun f g hf hg => by
    have h1 : f ≤ fun p => g p + hnormS X (f - g) * ‖p.1.1‖ := fun p => by
      have := abs_le_hnormS' (inHS_sub hf hg) p
      simp only [Pi.sub_apply] at this
      linarith [le_abs_self (f p - g p)]
    have e : (fun p : X × Z => hnormS X (f - g) * ‖p.1.1‖) =
        hnormS X (f - g) • fun p : X × Z => ‖p.1.1‖ := by
      funext p; simp
    have hgH : InHS hX fun p => g p + hnormS X (f - g) * ‖p.1.1‖ := by
      change InHS hX (g + fun p : X × Z => hnormS X (f - g) * ‖p.1.1‖)
      rw [e]
      exact inHS_add hg (inHS_smul inHS_norm _)
    exact (hmono _ _ hf hgH h1).trans (hdisc g hg _ (hnormS_nonneg _))
  refine hnormS_le (mul_nonneg hγ (hnormS_nonneg _)) fun p hp => ?_
  have a := hle f g hf hg p
  have b := hle g f hg hf p
  dsimp only at a b
  rw [hnormS_symm hf hg, hp, mul_one] at b
  rw [hp, mul_one] at a
  simp only [Pi.sub_apply]
  rw [abs_le]
  constructor <;> linarith

end StokeyLucasPrescott.StochasticDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Constant returns to scale (§9.3)

SLP §9.3, pp. 270–273, for the first formulation `x_{t+1} = y_t` on a cone `X`.

* `Assume919` (Assumption 9.19, with Assumption 9.18: `X` a convex cone) and `Assume920`
  (Assumption 9.20).
* **Exercise 9.8** (`ex_9_8_growth`, `ex_9_8`): along feasible plans `‖x_t‖ ≤ αᵗ‖x₀‖`, so
  `|F(x_t, π_t, z_t)| ≤ αᵗB(1 + α)‖x₀‖` and Assumption 9.3 holds with
  `L_t = αᵗB(1 + α)‖x₀‖` (`αβ < 1`).
* **Exercise 9.9** (`ex_9_9`): `M` maps `H(S)` into itself under Assumption 9.5 — continuity by
  applying Assumption 9.5 to the bounded truncation `f(x, z) R / max(R, ‖x‖)`, which agrees with
  `f` on `‖x‖ < R` — and preserves concavity in `x` (`ex_9_9_concave`). **Correction:** it does
  not preserve quasi-concavity (`ex_9_9_quasiconcave_false`: with a fair coin, the quasi-concave
  `max(u, 2u)` and `max(−u, −2u)`, `u = x₁ − x₂`, average to `|x₁ − x₂|/2`). The solutions
  manual's argument picks the worse of two points for one shock and uses it for all shocks.
* **Exercise 9.10a** (`ex_9_10a`): `T` has a unique fixed point `v ∈ H(S)`, with
  `‖Tⁿv₀ − v‖ ≤ (αβ)ⁿ‖v₀ − v‖`; `G` is nonempty, compact-valued and u.h.c., and `y ∈ G(x, z)`
  implies `λy ∈ G(λx, z)`. By Exercise 9.8 and Theorem 9.2, `v = v*` and plans generated by `G`
  are optimal (`crs_vStar`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace StokeyLucasPrescott.StochasticDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {X : Set E}
variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
variable {hX : IsCone X}

omit [MeasurableSpace E] [OpensMeasurableSpace Z] in
/-- **Exercise 9.9.** Under Assumption 9.5, `M` maps `H(S)` into itself. -/
theorem ex_9_9 (Q : Kernel Z Z) [IsMarkovKernel Q] (hQ : PreservesBC X Q) {f : X × Z → ℝ}
    (hf : InHS hX f) : InHS hX (mop Q f) := by
  obtain ⟨M₀, hM₀⟩ := hf.2.2
  set M := max M₀ 0
  have hM : ∀ p : X × Z, |f p| ≤ M * ‖p.1.1‖ := fun p =>
    (hM₀ p).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  refine ⟨?_, fun y z a ha => ?_, M, fun p => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro p
    set R := ‖p.1.1‖ + 1
    have hR : 0 < R := by positivity
    have hmax : ∀ q : X × Z, 0 < max R ‖q.1.1‖ := fun q => lt_max_of_lt_left hR
    set g : X × Z → ℝ := fun q => f q * (R / max R ‖q.1.1‖)
    have hgc : Continuous g := hf.1.mul (continuous_const.div
      (continuous_const.max (continuous_subtype_val.comp continuous_fst).norm)
      fun q => (hmax q).ne')
    have hgb : ∀ q, |g q| ≤ M * R := fun q => by
      simp only [g, abs_mul, abs_div, abs_of_pos hR, abs_of_pos (hmax q)]
      have h1 := hM q
      have h2 : ‖q.1.1‖ * (R / max R ‖q.1.1‖) ≤ R := by
        rw [mul_div_assoc', div_le_iff₀ (hmax q)]
        rw [mul_comm R]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hR.le
      calc |f q| * (R / max R ‖q.1.1‖) ≤ M * ‖q.1.1‖ * (R / max R ‖q.1.1‖) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ M * R := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    have hcont := hQ g hgc ⟨_, hgb⟩
    have heq : ∀ᶠ q in 𝓝 p, mop Q g q = mop Q f q := by
      have hopen : {q : X × Z | ‖q.1.1‖ < R} ∈ 𝓝 p :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst).norm continuous_const).mem_nhds
          (by change ‖p.1.1‖ < R; simp only [R]; linarith)
      filter_upwards [hopen] with q hq
      simp only [mop, g]
      congr 1
      funext z'
      rw [max_eq_left (le_of_lt hq), div_self hR.ne', mul_one]
    exact hcont.continuousAt.congr heq
  · simp only [mop]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun z' => hf.2.1 y z' a ha)
  · have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := M * ‖p.1.1‖)
      (f := fun z' => f (p.1, z')) (Eventually.of_forall fun z' => by
        rw [Real.norm_eq_abs]; exact hM _)
    rw [mop]
    simpa [Real.norm_eq_abs, measureReal_def] using this


/-- **Assumption 9.19** (with Assumption 9.18: `X` is a convex cone). -/
structure Assume919 (hX : IsCone X) (Γ : X × Z → Set X) (β α : ℝ) : Prop where
  convex : Convex ℝ X
  nonempty : ∀ s, (Γ s).Nonempty
  compact : ∀ s, IsCompact (Γ s)
  lhc : ∀ s, IsLHC Γ s
  uhc : ∀ s, IsUHC Γ s
  cone : ∀ x z, ∀ y ∈ Γ (x, z), ∀ (a : ℝ) (ha : 0 ≤ a), csmul hX ha y ∈ Γ (csmul hX ha x, z)
  α_pos : 0 < α
  αβ_lt : α * β < 1
  growth : ∀ x z, ∀ y ∈ Γ (x, z), ‖y.1‖ ≤ α * ‖x.1‖

/-- **Assumption 9.20.** -/
structure Assume920 (hX : IsCone X) (Γ : X × Z → Set X) (F : X × X × Z → ℝ) (β B : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  cont : ContinuousOn F {p | p.2.1 ∈ Γ (p.1, p.2.2)}
  hom : ∀ x z, ∀ y ∈ Γ (x, z), ∀ (a : ℝ) (ha : 0 ≤ a),
    F (csmul hX ha x, csmul hX ha y, z) = a * F (x, y, z)
  B_pos : 0 < B
  bdd : ∀ x z, ∀ y ∈ Γ (x, z), |F (x, y, z)| ≤ B * (‖x.1‖ + ‖y.1‖)

variable {Γ : X × Z → Set X} {F : X × X × Z → ℝ} {β α B : ℝ}

omit [OpensMeasurableSpace Z] in
/-- **Exercise 9.8 (growth).** Along a feasible plan, `‖x_t‖ ≤ αᵗ‖x₀‖`. -/
theorem ex_9_8_growth (Q : Kernel Z Z) (h919 : Assume919 hX Γ β α) {s₀ : X × Z}
    {π : Plan X Z} (hπ : IsFeasible (Model.first Q Γ F β) s₀ π) (t : ℕ) (h : Fin t → Z) :
    ‖(xState (Model.first Q Γ F β) s₀ π t h).1‖ ≤ α ^ t * ‖s₀.1.1‖ := by
  induction t with
  | zero => simp [xState]
  | succ t ih =>
    have hmem := hπ.2 t (Fin.init h)
    calc ‖(xState (Model.first Q Γ F β) s₀ π (t + 1) h).1‖ = ‖(π t (Fin.init h)).1‖ := rfl
      _ ≤ α * ‖(xState (Model.first Q Γ F β) s₀ π t (Fin.init h)).1‖ :=
          h919.growth _ _ _ hmem
      _ ≤ α * (α ^ t * ‖s₀.1.1‖) := mul_le_mul_of_nonneg_left (ih _) h919.α_pos.le
      _ = α ^ (t + 1) * ‖s₀.1.1‖ := by ring

omit [OpensMeasurableSpace Z] in
/-- **Exercise 9.8.** Under Assumptions 9.18–9.20, the returns of a feasible plan satisfy
`|F(x_t, π_t, z_t)| ≤ αᵗB(1 + α)‖x₀‖`, and `Σ βᵗ αᵗB(1 + α)‖x₀‖ < ∞`: Assumption 9.3 holds. -/
theorem ex_9_8 (Q : Kernel Z Z) (h919 : Assume919 hX Γ β α)
    (h920 : Assume920 hX Γ F β B) {s₀ : X × Z} {π : Plan X Z}
    (hπ : IsFeasible (Model.first Q Γ F β) s₀ π) :
    (∀ t h, |ret (Model.first Q Γ F β) s₀ π t h| ≤ B * (1 + α) * ‖s₀.1.1‖ * α ^ t) ∧
      Summable fun t => β ^ t * (B * (1 + α) * ‖s₀.1.1‖ * α ^ t) := by
  refine ⟨fun t h => ?_, ?_⟩
  · have hmem := hπ.2 t h
    have hg := ex_9_8_growth Q h919 hπ t h
    have hy := h919.growth _ _ _ hmem
    have hb := h920.bdd _ _ _ hmem
    have hB := h920.B_pos
    have hα := h919.α_pos
    change |F ((state (Model.first Q Γ F β) s₀ π t h).1, π t h,
      (state (Model.first Q Γ F β) s₀ π t h).2)| ≤ _
    calc _ ≤ B * (‖(state (Model.first Q Γ F β) s₀ π t h).1.1‖ + ‖(π t h).1‖) := hb
      _ ≤ B * ((1 + α) * (α ^ t * ‖s₀.1.1‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hB.le
          have : ‖(state (Model.first Q Γ F β) s₀ π t h).1.1‖ ≤ α ^ t * ‖s₀.1.1‖ := hg
          nlinarith
      _ = B * (1 + α) * ‖s₀.1.1‖ * α ^ t := by ring
  · have hαβ : 0 ≤ α * β := mul_nonneg h919.α_pos.le h920.β_pos.le
    refine ((summable_geometric_of_lt_one hαβ h919.αβ_lt).mul_left
      (B * (1 + α) * ‖s₀.1.1‖)).congr fun t => ?_
    rw [mul_pow]
    ring

variable (Q : Kernel Z Z) [IsMarkovKernel Q]

/-- The operator `(Tf)(x, z) = max_{y ∈ Γ(x, z)} {F(x, y, z) + β ∫ f(y, z′) Q(z, dz′)}`. -/
noncomputable def crsT (Γ : X × Z → Set X) (F : X × X × Z → ℝ) (β : ℝ) (f : X × Z → ℝ)
    (s : X × Z) : ℝ :=
  maxValue (objG (Model.first Q Γ F β) f) Γ s

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace Z] [IsMarkovKernel Q]
  [OpensMeasurableSpace Z] in
theorem objG_first (f : X × Z → ℝ) (p : (X × Z) × X) :
    objG (Model.first Q Γ F β) f p = F (p.1.1, p.2, p.1.2) + β * mop Q f (p.2, p.1.2) := rfl

omit [OpensMeasurableSpace Z] in
theorem continuousOn_objG_crs (h920 : Assume920 hX Γ F β B) (hQ : PreservesBC X Q)
    {f : X × Z → ℝ} (hf : InHS hX f) :
    ContinuousOn (objG (Model.first Q Γ F β) f) (graph Γ) := by
  have hF : ContinuousOn (fun p : (X × Z) × X => F (p.1.1, p.2, p.1.2)) (graph Γ) :=
    h920.cont.comp (continuous_fst.fst.prodMk
      (continuous_snd.prodMk continuous_fst.snd)).continuousOn fun p hp => hp
  have hE : Continuous fun p : (X × Z) × X => mop Q f (p.2, p.1.2) :=
    (ex_9_9 Q hQ hf).1.comp (continuous_snd.prodMk continuous_fst.snd)
  have := hF.add ((continuousOn_const : ContinuousOn (fun _ : (X × Z) × X => β) _).mul
    hE.continuousOn)
  exact this.congr fun p _ => objG_first Q f p

omit [OpensMeasurableSpace Z] in
theorem exists_crsT_argmax (h919 : Assume919 hX Γ β α) (h920 : Assume920 hX Γ F β B)
    (hQ : PreservesBC X Q) {f : X × Z → ℝ} (hf : InHS hX f) (s : X × Z) :
    ∃ y ∈ Γ s, crsT Q Γ F β f s = F (s.1, y, s.2) + β * mop Q f (y, s.2) ∧
      ∀ y' ∈ Γ s, F (s.1, y', s.2) + β * mop Q f (y', s.2) ≤ crsT Q Γ F β f s := by
  obtain ⟨y, hy, hval, hmax⟩ := exists_argmax (continuousOn_objG_crs Q h920 hQ hf)
    (h919.compact s) (h919.nonempty s)
  exact ⟨y, hy, hval.symm, fun y' hy' => (hmax y' hy').trans_eq hval⟩

omit [MeasurableSpace E] [OpensMeasurableSpace Z] in
theorem abs_mop_le_hnormS {f : X × Z → ℝ} (hf : InHS hX f) (y : X) (z : Z) :
    |mop Q f (y, z)| ≤ hnormS X f * ‖y.1‖ := by
  have := norm_integral_le_of_norm_le_const (μ := Q z) (C := hnormS X f * ‖y.1‖)
    (f := fun z' => f (y, z')) (Eventually.of_forall fun z' => by
      rw [Real.norm_eq_abs]; exact abs_le_hnormS' hf _)
  rw [mop]
  simpa [Real.norm_eq_abs, measureReal_def] using this

omit [MeasurableSpace E] in
theorem integrable_section_HS {f : X × Z → ℝ} (hf : InHS hX f) (y : X) (z : Z) :
    Integrable (fun z' => f (y, z')) (Q z) :=
  integrable_of_abs_le (hf.1.comp (Continuous.prodMk_right y)).measurable
    (B := hnormS X f * ‖y.1‖) fun _ => abs_le_hnormS' hf _

omit [OpensMeasurableSpace Z] in
/-- **Exercise 9.10a (`T : H(S) → H(S)`).** -/
theorem crsT_mapsTo (h919 : Assume919 hX Γ β α) (h920 : Assume920 hX Γ F β B)
    (hQ : PreservesBC X Q) {f : X × Z → ℝ} (hf : InHS hX f) : InHS hX (crsT Q Γ F β f) := by
  have hMf := ex_9_9 Q hQ hf
  refine ⟨(theorem_3_6 (continuousOn_objG_crs Q h920 hQ hf) h919.compact h919.lhc
    h919.uhc).1, fun x z a ha => ?_, B * (1 + α) + β * α * hnormS X f, fun p => ?_⟩
  · obtain ⟨y, hy, hval, hmax⟩ := exists_crsT_argmax Q h919 h920 hQ hf (x, z)
    obtain ⟨y', hy', hval', hmax'⟩ := exists_crsT_argmax Q h919 h920 hQ hf (csmul hX ha x, z)
    dsimp only at hval hmax hval' hmax'
    rcases ha.eq_or_lt with rfl | hpos
    · have hy0 : y'.1 = 0 := by
        have := h919.growth _ _ _ hy'
        simp only [csmul, zero_smul, norm_zero, mul_zero] at this
        exact norm_le_zero_iff.1 this
      have hyeq : y' = csmul hX le_rfl y := Subtype.ext (by simp [csmul, hy0])
      rw [hval', hyeq, h920.hom x z y hy, hMf.2.1]
      ring
    · refine le_antisymm ?_ ?_
      · have hinv : 0 ≤ a⁻¹ := inv_nonneg.2 hpos.le
        have hz' : csmul hX hinv y' ∈ Γ (x, z) := by
          have := h919.cone _ z y' hy' a⁻¹ hinv
          have e : csmul hX hinv (csmul hX hpos.le x) = x := Subtype.ext (by
            simp [csmul, smul_smul, inv_mul_cancel₀ hpos.ne'])
          rwa [e] at this
        have hle := hmax _ hz'
        have e1 : csmul hX hpos.le (csmul hX hinv y') = y' := Subtype.ext (by
          simp [csmul, smul_smul, mul_inv_cancel₀ hpos.ne'])
        have hF := h920.hom x z _ hz' a hpos.le
        have hfz := hMf.2.1 (csmul hX hinv y') z a hpos.le
        rw [e1] at hF hfz
        rw [hval', hF, hfz]
        nlinarith [h920.β_pos]
      · have hF := h920.hom x z y hy a hpos.le
        have hfy := hMf.2.1 y z a hpos.le
        have := hmax' _ (h919.cone x z y hy a hpos.le)
        rw [hF, hfy] at this
        rw [hval]
        nlinarith [h920.β_pos]
  · obtain ⟨y, hy, hval, -⟩ := exists_crsT_argmax Q h919 h920 hQ hf p
    have hy' := h919.growth _ _ _ hy
    have hfy := abs_mop_le_hnormS Q hf y p.2
    have hB := h920.bdd _ _ _ hy
    rw [hval]
    have hβ := h920.β_pos
    have hn := hnormS_nonneg (X := X) f
    calc |F (p.1, y, p.2) + β * mop Q f (y, p.2)| ≤ |F (p.1, y, p.2)| + β * |mop Q f (y, p.2)| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_pos hβ]
      _ ≤ B * (‖p.1.1‖ + α * ‖p.1.1‖) + β * (hnormS X f * (α * ‖p.1.1‖)) := by
          gcongr
          · exact hB.trans (mul_le_mul_of_nonneg_left (by linarith) h920.B_pos.le)
          · exact hfy.trans (mul_le_mul_of_nonneg_left hy' hn)
      _ = (B * (1 + α) + β * α * hnormS X f) * ‖p.1.1‖ := by ring

/-- `T` is monotone on `H(S)`. -/
theorem crsT_mono (h919 : Assume919 hX Γ β α) (h920 : Assume920 hX Γ F β B)
    (hQ : PreservesBC X Q) {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) (hfg : f ≤ g) :
    crsT Q Γ F β f ≤ crsT Q Γ F β g := fun s => by
  obtain ⟨y, hy, hval, -⟩ := exists_crsT_argmax Q h919 h920 hQ hf s
  obtain ⟨-, -, -, hmax⟩ := exists_crsT_argmax Q h919 h920 hQ hg s
  rw [hval]
  refine le_trans ?_ (hmax y hy)
  have : mop Q f (y, s.2) ≤ mop Q g (y, s.2) :=
    integral_mono (integrable_section_HS Q hf y s.2) (integrable_section_HS Q hg y s.2)
      fun z' => hfg _
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left this h920.β_pos.le)

/-- `T(f + a‖x‖) ≤ Tf + αβa‖x‖`. -/
theorem crsT_disc (h919 : Assume919 hX Γ β α) (h920 : Assume920 hX Γ F β B)
    (hQ : PreservesBC X Q) {f : X × Z → ℝ} (hf : InHS hX f) {a : ℝ} (ha : 0 ≤ a) :
    crsT Q Γ F β (fun p => f p + a * ‖p.1.1‖) ≤ fun p => crsT Q Γ F β f p + α * β * a * ‖p.1.1‖ :=
  fun s => by
    have hc : InHS hX fun p : X × Z => f p + a * ‖p.1.1‖ := by
      have := inHS_add hf (inHS_smul (inHS_norm (hX := hX) (Z := Z)) a)
      convert this using 1
    obtain ⟨y, hy, hval, -⟩ := exists_crsT_argmax Q h919 h920 hQ hc s
    obtain ⟨-, -, -, hmax⟩ := exists_crsT_argmax Q h919 h920 hQ hf s
    rw [hval]
    have hm : mop Q (fun p : X × Z => f p + a * ‖p.1.1‖) (y, s.2) =
        mop Q f (y, s.2) + a * ‖y.1‖ := by
      simp only [mop]
      rw [integral_add (integrable_section_HS Q hf y s.2) (integrable_const _)]
      simp
    rw [hm]
    have h1 := hmax y hy
    have h2 := mul_le_mul_of_nonneg_left (h919.growth _ _ _ hy) (mul_nonneg h920.β_pos.le ha)
    dsimp only
    nlinarith

/-- `T` is a contraction of modulus `αβ` on `H(S)` (Theorem 4.12). -/
theorem crsT_contraction (h919 : Assume919 hX Γ β α) (h920 : Assume920 hX Γ F β B)
    (hQ : PreservesBC X Q) {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) :
    hnormS X (crsT Q Γ F β f - crsT Q Γ F β g) ≤ α * β * hnormS X (f - g) :=
  contraction_HS (mul_nonneg h919.α_pos.le h920.β_pos.le)
    (fun _ _ hf hg hfg => crsT_mono Q h919 h920 hQ hf hg hfg)
    (fun _ hf _ ha => crsT_disc Q h919 h920 hQ hf ha) hf hg

/-- **Exercise 9.10a.** Under Assumptions 9.5 and 9.18–9.20, `T` has a unique fixed point
`v ∈ H(S)`, `‖Tⁿv₀ − v‖ ≤ (αβ)ⁿ‖v₀ − v‖` for `v₀ ∈ H(S)`, and the policy correspondence `G` is
nonempty, compact-valued, u.h.c., and `y ∈ G(x, z)` implies `λy ∈ G(λx, z)`. -/
theorem ex_9_10a (h919 : Assume919 hX Γ β α) (h920 : Assume920 hX Γ F β B)
    (hQ : PreservesBC X Q) :
    ∃ v, InHS hX v ∧ crsT Q Γ F β v = v ∧ (∀ w, InHS hX w → crsT Q Γ F β w = w → w = v) ∧
      (∀ v₀, InHS hX v₀ → ∀ n : ℕ,
        hnormS X ((crsT Q Γ F β)^[n] v₀ - v) ≤ (α * β) ^ n * hnormS X (v₀ - v)) ∧
      (∀ s, (argmax (objG (Model.first Q Γ F β) v) Γ s).Nonempty ∧
        IsCompact (argmax (objG (Model.first Q Γ F β) v) Γ s) ∧
        IsUHC (argmax (objG (Model.first Q Γ F β) v) Γ) s) ∧
      ∀ x z y (a : ℝ) (ha : 0 ≤ a), y ∈ argmax (objG (Model.first Q Γ F β) v) Γ (x, z) →
        csmul hX ha y ∈ argmax (objG (Model.first Q Γ F β) v) Γ (csmul hX ha x, z) := by
  set T := crsT Q Γ F β
  set γ := α * β
  have hγ0 : 0 ≤ γ := mul_nonneg h919.α_pos.le h920.β_pos.le
  have hγ1 : γ < 1 := h919.αβ_lt
  have hTH : ∀ f, InHS hX f → InHS hX (T f) := fun f hf => crsT_mapsTo Q h919 h920 hQ hf
  have h0 : InHS hX (0 : X × Z → ℝ) := inHS_zero
  set fs : ℕ → X × Z → ℝ := fun n => T^[n] 0
  have hfs : ∀ n, InHS hX (fs n) := fun n => by
    induction n with
    | zero => exact h0
    | succ n ih => simp only [fs, Function.iterate_succ_apply']; exact hTH _ ih
  have hstep : ∀ n, hnormS X (fs (n + 1) - fs n) ≤ γ ^ n * hnormS X (fs 1 - fs 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : fs (n + 1 + 1) = T (fs (n + 1)) := Function.iterate_succ_apply' _ _ _
      have e2 : fs (n + 1) = T (fs n) := Function.iterate_succ_apply' _ _ _
      rw [e1, e2]
      calc hnormS X (T (T (fs n)) - T (fs n)) ≤ γ * hnormS X (T (fs n) - fs n) :=
            crsT_contraction Q h919 h920 hQ (e2 ▸ hfs (n + 1)) (hfs n)
        _ ≤ γ * (γ ^ n * hnormS X (fs 1 - fs 0)) := by
            rw [← e2]; exact mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (n + 1) * hnormS X (fs 1 - fs 0) := by ring
  have hgap : ∀ n k, hnormS X (fs (n + k) - fs n) ≤
      γ ^ n / (1 - γ) * hnormS X (fs 1 - fs 0) := by
    intro n k
    have hd := hnormS_nonneg (X := X) (fs 1 - fs 0)
    have hsum : ∀ k, hnormS X (fs (n + k) - fs n) ≤
        ∑ i ∈ Finset.range k, γ ^ (n + i) * hnormS X (fs 1 - fs 0) := by
      intro k
      induction k with
      | zero => simp [hnormS]
      | succ k ih =>
        rw [Finset.sum_range_succ]
        calc hnormS X (fs (n + (k + 1)) - fs n)
            ≤ hnormS X (fs (n + k + 1) - fs (n + k)) + hnormS X (fs (n + k) - fs n) :=
              hnormS_sub_le (hfs _) (hfs _) (hfs _)
          _ ≤ γ ^ (n + k) * hnormS X (fs 1 - fs 0) +
              ∑ i ∈ Finset.range k, γ ^ (n + i) * hnormS X (fs 1 - fs 0) :=
              add_le_add (hstep _) ih
          _ = _ := by ring
    refine (hsum k).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ hd
    simp only [pow_add, ← Finset.mul_sum]
    rw [div_eq_mul_inv, ← tsum_geometric_of_lt_one hγ0 hγ1]
    exact mul_le_mul_of_nonneg_left ((summable_geometric_of_lt_one hγ0 hγ1).sum_le_tsum _
      fun i _ => pow_nonneg hγ0 i) (pow_nonneg hγ0 n)
  have hgeo : Tendsto (fun n => γ ^ n / (1 - γ) * hnormS X (fs 1 - fs 0)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).div_const (1 - γ)).mul_const
      (hnormS X (fs 1 - fs 0))
  have hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, hnormS X (fs m - fs n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hgeo).2 (ε / 2) (half_pos hε))
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmN : hnormS X (fs m - fs N) < ε / 2 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact (hgap N k).trans_lt (hN N le_rfl)
    have hnN : hnormS X (fs N - fs n) < ε / 2 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [hnormS_symm (hfs (N + k)) (hfs N)]
      exact (hgap N k).trans_lt (hN N le_rfl)
    calc hnormS X (fs m - fs n) ≤ hnormS X (fs m - fs N) + hnormS X (fs N - fs n) :=
          hnormS_sub_le (hfs _) (hfs _) (hfs _)
      _ < ε := by linarith
  obtain ⟨v, hvH, hlim⟩ := hnormS_complete hfs hcauchy
  have hTv : T v = v := by
    have hb : ∀ n, hnormS X (T v - v) ≤ γ * hnormS X (fs n - v) + hnormS X (fs (n + 1) - v) := by
      intro n
      have e : fs (n + 1) = T (fs n) := Function.iterate_succ_apply' _ _ _
      calc hnormS X (T v - v) ≤ hnormS X (T v - fs (n + 1)) + hnormS X (fs (n + 1) - v) :=
            hnormS_sub_le (hTH v hvH) (hfs _) hvH
        _ ≤ γ * hnormS X (fs n - v) + hnormS X (fs (n + 1) - v) := by
            refine add_le_add ?_ le_rfl
            rw [e, hnormS_symm (hTH _ (hfs n)) (hTH v hvH)]
            exact crsT_contraction Q h919 h920 hQ (hfs n) hvH
    have hlim2 : Tendsto (fun n => γ * hnormS X (fs n - v) + hnormS X (fs (n + 1) - v)) atTop
        (𝓝 0) := by
      simpa using (hlim.const_mul γ).add (hlim.comp (tendsto_add_atTop_nat 1))
    have hz : hnormS X (T v - v) = 0 :=
      le_antisymm (ge_of_tendsto' hlim2 hb) (hnormS_nonneg _)
    exact sub_eq_zero.1 ((hnormS_norm (inHS_sub (hTH v hvH) hvH) h0 1).2.1.1 hz)
  have huniq : ∀ w, InHS hX w → T w = w → w = v := fun w hw hTw => by
    have h1 := crsT_contraction Q h919 h920 hQ hw hvH
    change hnormS X (T w - T v) ≤ _ at h1
    rw [hTw, hTv] at h1
    have hz : hnormS X (w - v) = 0 := by
      nlinarith [hnormS_nonneg (X := X) (w - v)]
    exact sub_eq_zero.1 ((hnormS_norm (inHS_sub hw hvH) h0 1).2.1.1 hz)
  refine ⟨v, hvH, hTv, huniq, fun v₀ hv₀ n => ?_, fun s => ?_, fun x z y a ha hy => ?_⟩
  · induction n with
    | zero => simp
    | succ n ih =>
      have hn : InHS hX (T^[n] v₀) := by
        clear ih
        induction n with
        | zero => exact hv₀
        | succ n ihn => rw [Function.iterate_succ_apply']; exact hTH _ ihn
      rw [Function.iterate_succ_apply']
      conv_lhs => rw [← hTv]
      calc hnormS X (T (T^[n] v₀) - T v) ≤ γ * hnormS X (T^[n] v₀ - v) :=
            crsT_contraction Q h919 h920 hQ hn hvH
        _ ≤ γ * (γ ^ n * hnormS X (v₀ - v)) := mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (n + 1) * hnormS X (v₀ - v) := by ring
  · exact (theorem_3_6 (continuousOn_objG_crs Q h920 hQ hvH) h919.compact h919.lhc
      h919.uhc).2 s
  · refine ⟨h919.cone x z y hy.1 a ha, ?_⟩
    have hvx : v (x, z) = maxValue (objG (Model.first Q Γ F β) v) Γ (x, z) :=
      (congrFun hTv (x, z)).symm
    have hvax : v (csmul hX ha x, z) =
        maxValue (objG (Model.first Q Γ F β) v) Γ (csmul hX ha x, z) := (congrFun hTv _).symm
    rw [← hvax, hvH.2.1, hvx, ← hy.2, objG_first, objG_first]
    dsimp only
    rw [h920.hom x z y hy.1 a ha, (ex_9_9 Q hQ hvH).2.1]
    ring

omit [OpensMeasurableSpace Z] in
/-- **The fixed point is `v*`** (Exercise 9.8 with Theorem 9.2). Every feasible plan is worth at
most `v(s₀)`, plans generated by measurable selections from `G` attain it, and `v*(s₀) = v(s₀)`. -/
theorem crs_vStar (h919 : Assume919 hX Γ β α) (h920 : Assume920 hX Γ F β B)
    (hQ : PreservesBC X Q) [OpensMeasurableSpace (X × Z)] (hFm : Measurable F) {v : X × Z → ℝ}
    (hvH : InHS hX v) (hv : crsT Q Γ F β v = v) {g : ℕ → X × Z → X}
    (hg : ∀ t, Measurable (g t)) (hgG : ∀ t s, g t s ∈ policy (Model.first Q Γ F β) v s)
    (s₀ : X × Z) :
    (∀ π, IsFeasible (Model.first Q Γ F β) s₀ π → planValue (Model.first Q Γ F β) s₀ π ≤ v s₀) ∧
      planValue (Model.first Q Γ F β) s₀ (genPlan (Model.first Q Γ F β) s₀ g) = v s₀ ∧
      vStar (Model.first Q Γ F β) s₀ = v s₀ := by
  set M := Model.first Q Γ F β
  have hφ : Measurable M.φ := measurable_snd.fst
  have hFE : SolvesFE M v := fun s => by
    obtain ⟨y, hy, hval, hmax⟩ := exists_crsT_argmax Q h919 h920 hQ hvH s
    rw [congrFun hv s] at hval hmax
    refine IsGreatest.isLUB ⟨⟨y, hy, hval.symm⟩, ?_⟩
    rintro _ ⟨y', hy', rfl⟩
    exact hmax y' hy'
  have hvbd : ∀ π, IsFeasible M s₀ π → ∀ t h, |v (state M s₀ π t h)| ≤
      hnormS X v * (α ^ t * ‖s₀.1.1‖) := fun π hπ t h =>
    (abs_le_hnormS' hvH _).trans (mul_le_mul_of_nonneg_left (ex_9_8_growth Q h919 hπ t h)
      (hnormS_nonneg v))
  refine ex_9_4 M hφ h920.β_pos.le hFE s₀ (fun π hπ t => ⟨?_, ?_⟩) (fun π hπ => ⟨_,
    (continuous_coe_real_ereal.tendsto _).comp (tendsto_uN M h920.β_pos.le s₀ π
      (ex_9_8 Q h919 h920 hπ).1 (ex_9_8 Q h919 h920 hπ).2)⟩) (fun π hπ => ?_) hg hgG
  · exact integrable_ret_of_bound M hφ hFm s₀ hπ.1 (ex_9_8 Q h919 h920 hπ).1 t
  · have := ex_8_8a M.Q t
    exact integrable_of_abs_le (hvH.1.measurable.comp (measurable_state M hφ s₀ hπ.1 t))
      (hvbd π hπ t)
  · have hαβ : 0 ≤ α * β := mul_nonneg h919.α_pos.le h920.β_pos.le
    refine squeeze_zero_norm (a := fun t => hnormS X v * ‖s₀.1.1‖ * (α * β) ^ t)
      (fun t => ?_) ?_
    · have := ex_8_8a M.Q t
      rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos h920.β_pos]
      have hI := norm_integral_le_of_norm_le_const (μ := hist M.Q t s₀.2)
        (C := hnormS X v * (α ^ t * ‖s₀.1.1‖)) (f := fun h' => v (state M s₀ π t h'))
        (Eventually.of_forall fun h' => by rw [Real.norm_eq_abs]; exact hvbd π hπ t h')
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at hI
      calc β ^ t * ‖∫ h', v (state M s₀ π t h') ∂hist M.Q t s₀.2‖
          ≤ β ^ t * (hnormS X v * (α ^ t * ‖s₀.1.1‖)) :=
            mul_le_mul_of_nonneg_left hI (pow_nonneg h920.β_pos.le t)
        _ = hnormS X v * ‖s₀.1.1‖ * (α * β) ^ t := by rw [mul_pow]; ring
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hαβ h919.αβ_lt).const_mul
        (hnormS X v * ‖s₀.1.1‖)

end StokeyLucasPrescott.StochasticDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Constant returns to scale: concavity, monotonicity, differentiability

SLP §9.3, pp. 272–273, Exercises 9.9 and 9.10b–c, with `X ⊆ ℝˡ` a convex cone.

* `ex_9_9_concave`: `M` preserves concavity in `x` on `H(S)`.
* `ex_9_9_quasiconcave_false`: `M` does **not** preserve quasi-concavity. With `Z = ℝ`,
  `Q(z, ·) = ½δ₀ + ½δ₁`, and `f(x, z) = max(s(z)u, 2s(z)u)`, `u = x₁ − x₂`, `s(0) = 1`,
  `s(1) = −1` and `s` continuous, every section `f(·, z)` is quasi-concave and `f ∈ H(S)`, but
  `(Mf)(x, z) = |x₁ − x₂|/2`.
* **Exercise 9.10b** (`ex_9_10b`): if `F(·, ·, z)` is concave on `A_z`, strictly for
  non-proportional `x, x′`, and `A_z` is convex, then `v(·, z)` is concave, and strictly so along
  non-proportional pairs (as in Exercise 4.8c). Homogeneous functions are linear along rays, so
  this is the strongest form of strict concavity available.
* **Exercise 9.10c**: `v(·, z)` is strictly increasing under Assumptions 9.8–9.9
  (`ex_9_10c_mono`); and at `x₀ ∈ int X` with `g(x₀, z₀) ∈ int Γ(x₀, z₀)`, `v(·, z₀)` is
  differentiable with `vᵢ(x₀, z₀) = Fᵢ[x₀, g(x₀, z₀), z₀]` (`ex_9_10c_diff`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StokeyLucasPrescott.StochasticDP

variable {l : ℕ} {XS : Set (Fin l → ℝ)} {hX : IsCone XS}
variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]

/-- **Exercise 9.9 (concavity).** If `f ∈ H(S)` is concave in `x` for each shock, so is `Mf`. -/
theorem ex_9_9_concave (hC : Convex ℝ XS) (Q : Kernel Z Z) [IsMarkovKernel Q]
    {f : XS × Z → ℝ} (hf : InHS hX f) (hconc : ∀ z', IsConcaveS hC fun x => f (x, z'))
    (z : Z) : IsConcaveS hC fun x => mop Q f (x, z) := by
  intro x x' θ h0 h1
  have i0 := integrable_section_HS Q hf x z
  have i1 := integrable_section_HS Q hf x' z
  have iθ := integrable_section_HS Q hf (cmb hC h0 h1 x x') z
  simp only [mop]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i0.const_mul θ)
    (i1.const_mul _)]
  exact integral_mono ((i0.const_mul θ).add (i1.const_mul _)) iθ
    fun z' => hconc z' x x' θ h0 h1

/-! ### The counterexample to quasi-concavity -/

/-- `f` is quasi-concave on the convex set `S`. -/
def IsQuasiConcaveS {S : Set (Fin l → ℝ)} (hS : Convex ℝ S) (f : S → ℝ) : Prop :=
  ∀ x x' (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1), min (f x) (f x') ≤ f (cmb hS h0 h1 x x')

/-- `φ(u) = max(u, 2u)`: increasing and homogeneous of degree one. -/
noncomputable def qcPhi (u : ℝ) : ℝ := max u (2 * u)

/-- A continuous sign switch with `s(0) = 1`, `s(1) = −1`. -/
noncomputable def qcSign (z : ℝ) : ℝ := max (-1) (min 1 (1 - 2 * z))

/-- The counterexample `f(x, z) = φ(s(z)(x₁ − x₂))` on the cone `ℝ²`. -/
noncomputable def qcF (p : ↥(univ : Set (Fin 2 → ℝ)) × ℝ) : ℝ :=
  qcPhi (qcSign p.2 * (p.1.1 0 - p.1.1 1))

/-- The two-point shock distribution `½δ₀ + ½δ₁`. -/
noncomputable def twoPoint : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 1)

theorem isProbabilityMeasure_twoPoint : IsProbabilityMeasure twoPoint :=
  ⟨by simp [twoPoint, ← two_mul, ENNReal.mul_inv_cancel]⟩

theorem isCone_univ : IsCone (univ : Set (Fin 2 → ℝ)) := fun _ _ _ _ => mem_univ _

theorem integral_twoPoint {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ} (hB : ∀ z, |g z| ≤ B) :
    ∫ z, g z ∂twoPoint = (g 0 + g 1) / 2 := by
  have hi : ∀ a : ℝ, Integrable g (Measure.dirac a) := fun a =>
    integrable_of_abs_le hg.measurable hB
  rw [twoPoint, integral_smul_measure, integral_add_measure (hi 0) (hi 1),
    integral_dirac' _ _ hg.stronglyMeasurable, integral_dirac' _ _ hg.stronglyMeasurable]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

theorem qcPhi_mono : Monotone qcPhi := fun a b h => max_le_max h (by linarith)

theorem abs_qcPhi_le (u : ℝ) : |qcPhi u| ≤ 2 * |u| := by
  simp only [qcPhi]
  rcases le_total 0 u with hu | hu
  · rw [max_eq_right (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg hu]
  · rw [max_eq_left (by linarith), abs_of_nonpos hu]
    linarith [abs_nonneg u]

theorem abs_qcSign_le (z : ℝ) : |qcSign z| ≤ 1 := by
  simp only [qcSign, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- **Correction to Exercise 9.9.** `M` does not preserve quasi-concavity: `qcF ∈ H(S)` and each
`qcF(·, z)` is quasi-concave, but `(M qcF)(·, z) = |x₁ − x₂|/2` is not. -/
theorem ex_9_9_quasiconcave_false :
    InHS isCone_univ qcF ∧ (∀ z, IsQuasiConcaveS convex_univ fun x => qcF (x, z)) ∧
      ¬∀ z, IsQuasiConcaveS convex_univ fun x => mop (Kernel.const ℝ twoPoint) qcF (x, z) := by
  have hs : Continuous qcSign :=
    continuous_const.max (continuous_const.min (continuous_const.sub
      (continuous_const.mul continuous_id)))
  have hlin : Continuous fun p : ↥(univ : Set (Fin 2 → ℝ)) × ℝ =>
      qcSign p.2 * (p.1.1 0 - p.1.1 1) :=
    (hs.comp continuous_snd).mul
      (((continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst)).sub
        ((continuous_apply 1).comp (continuous_subtype_val.comp continuous_fst)))
  have hphi : Continuous qcPhi := continuous_id.max (continuous_const.mul continuous_id)
  have hcont : Continuous qcF := hphi.comp hlin
  have hhom : ∀ x z (a : ℝ) (ha : 0 ≤ a), qcF (csmul isCone_univ ha x, z) = a * qcF (x, z) := by
    intro x z a ha
    simp only [qcF, qcPhi, csmul, Pi.smul_apply, smul_eq_mul]
    rw [mul_max_of_nonneg _ _ ha]
    congr 1 <;> ring
  have hbd : ∀ p, |qcF p| ≤ 4 * ‖p.1.1‖ := by
    intro p
    have h0 := norm_le_pi_norm p.1.1 0
    have h1 := norm_le_pi_norm p.1.1 1
    rw [Real.norm_eq_abs] at h0 h1
    have hs1 := abs_qcSign_le p.2
    calc |qcF p| ≤ 2 * |qcSign p.2 * (p.1.1 0 - p.1.1 1)| := abs_qcPhi_le _
      _ = 2 * (|qcSign p.2| * |p.1.1 0 - p.1.1 1|) := by rw [abs_mul]
      _ ≤ 2 * (1 * (|p.1.1 0| + |p.1.1 1|)) := by
          gcongr
          exact abs_sub _ _
      _ ≤ 4 * ‖p.1.1‖ := by linarith
  refine ⟨⟨hcont, hhom, 4, hbd⟩, fun z x x' θ h0 h1 => ?_, fun h => ?_⟩
  · have hl : qcSign z * ((cmb convex_univ h0 h1 x x').1 0 - (cmb convex_univ h0 h1 x x').1 1) =
        θ * (qcSign z * (x.1 0 - x.1 1)) + (1 - θ) * (qcSign z * (x'.1 0 - x'.1 1)) := by
      simp only [cmb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    change min (qcPhi _) (qcPhi _) ≤ qcPhi _
    rw [hl, ← qcPhi_mono.map_min]
    refine qcPhi_mono ?_
    rcases le_total (qcSign z * (x.1 0 - x.1 1)) (qcSign z * (x'.1 0 - x'.1 1)) with hab | hab
    · rw [min_eq_left hab]; nlinarith
    · rw [min_eq_right hab]; nlinarith
  · have := isProbabilityMeasure_twoPoint
    have hmop : ∀ x : (univ : Set (Fin 2 → ℝ)),
        mop (Kernel.const ℝ twoPoint) qcF (x, 0) = (qcF (x, 0) + qcF (x, 1)) / 2 := fun x => by
      rw [mop, Kernel.const_apply]
      exact integral_twoPoint (hcont.comp (Continuous.prodMk_right x)) (B := 4 * ‖x.1‖)
        fun z => hbd (x, z)
    have hq := h 0 ⟨fun i => if i = 0 then 1 else 0, mem_univ _⟩
      ⟨fun i => if i = 0 then 0 else 1, mem_univ _⟩ (1 / 2) (by norm_num) (by norm_num)
    simp only [hmop] at hq
    have s0 : qcSign 0 = 1 := by norm_num [qcSign]
    have s1 : qcSign 1 = -1 := by norm_num [qcSign]
    simp [qcF, qcPhi, s0, s1, cmb] at hq
    norm_num at hq

/-! ### Exercise 9.10b–c -/

/-- `x` and `x′` are not proportional. -/
def NonProp (x x' : XS) : Prop :=
  (∀ a : ℝ, 0 ≤ a → x.1 ≠ a • x'.1) ∧ ∀ a : ℝ, 0 ≤ a → x'.1 ≠ a • x.1

/-- `F(·, ·, z)` is concave on `A_z`, strictly for non-proportional `x, x′` (Exercise 4.8c). -/
def ConcaveCRS (hC : Convex ℝ XS) (Γ : XS × Z → Set XS) (F : XS × XS × Z → ℝ) : Prop :=
  ∀ z x y x' y', y ∈ Γ (x, z) → y' ∈ Γ (x', z) → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * F (x, y, z) + (1 - θ) * F (x', y', z) ≤
      F (cmb hC h0.le h1.le x x', cmb hC h0.le h1.le y y', z) ∧
    (NonProp x x' → θ * F (x, y, z) + (1 - θ) * F (x', y', z) <
      F (cmb hC h0.le h1.le x x', cmb hC h0.le h1.le y y', z))

variable {Γ : XS × Z → Set XS} {F : XS × XS × Z → ℝ} {β α B : ℝ}
variable (Q : Kernel Z Z) [IsMarkovKernel Q]

theorem cmb_one (hC : Convex ℝ XS) (x x' : XS) :
    cmb hC zero_le_one le_rfl x x' = x := Subtype.ext (by simp [cmb])

theorem cmb_zero (hC : Convex ℝ XS) (x x' : XS) :
    cmb hC le_rfl zero_le_one x x' = x' := Subtype.ext (by simp [cmb])

/-- `T` maps functions concave in `x` to functions concave in `x`, strictly along
non-proportional pairs. -/
theorem crsT_concave (hC : Convex ℝ XS) (h919 : Assume919 hX Γ β α)
    (h920 : Assume920 hX Γ F β B) (hQ : PreservesBC XS Q) (hF : ConcaveCRS hC Γ F)
    (h911 : Assumption911 hC hC (Model.first Q Γ F β)) {f : XS × Z → ℝ} (hf : InHS hX f)
    (hconc : ∀ z, IsConcaveS hC fun x => f (x, z)) (z : Z) (x x' : XS) (θ : ℝ) (h0 : 0 < θ)
    (h1 : θ < 1) :
    θ * crsT Q Γ F β f (x, z) + (1 - θ) * crsT Q Γ F β f (x', z) ≤
      crsT Q Γ F β f (cmb hC h0.le h1.le x x', z) ∧
    (NonProp x x' → θ * crsT Q Γ F β f (x, z) + (1 - θ) * crsT Q Γ F β f (x', z) <
      crsT Q Γ F β f (cmb hC h0.le h1.le x x', z)) := by
  obtain ⟨y, hy, hv, -⟩ := exists_crsT_argmax Q h919 h920 hQ hf (x, z)
  obtain ⟨y', hy', hv', -⟩ := exists_crsT_argmax Q h919 h920 hQ hf (x', z)
  obtain ⟨-, -, -, hmax⟩ := exists_crsT_argmax Q h919 h920 hQ hf (cmb hC h0.le h1.le x x', z)
  have hyθ := h911 z x y x' y' hy hy' θ h0.le h1.le
  have hE := mul_le_mul_of_nonneg_left
    (ex_9_9_concave hC Q hf hconc z y y' θ h0.le h1.le) h920.β_pos.le
  have hm := hmax _ hyθ
  have hFc := hF z x y x' y' hy hy' θ h0 h1
  dsimp only at hv hv' hm
  rw [hv, hv']
  exact ⟨by nlinarith [hFc.1], fun hnp => by nlinarith [hFc.2 hnp]⟩

/-- **Exercise 9.10b.** If `F(·, ·, z)` is concave on `A_z`, strictly for non-proportional
`x, x′`, and `A_z` is convex, then the fixed point `v(·, z)` is concave, and strictly so along
non-proportional pairs. -/
theorem ex_9_10b (hC : Convex ℝ XS) (h919 : Assume919 hX Γ β α)
    (h920 : Assume920 hX Γ F β B) (hQ : PreservesBC XS Q) (hF : ConcaveCRS hC Γ F)
    (h911 : Assumption911 hC hC (Model.first Q Γ F β)) {v : XS × Z → ℝ} (hvH : InHS hX v)
    (hv : crsT Q Γ F β v = v) :
    (∀ z, IsConcaveS hC fun x => v (x, z)) ∧
      ∀ z x x', NonProp x x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
        θ * v (x, z) + (1 - θ) * v (x', z) < v (cmb hC h0.le h1.le x x', z) := by
  obtain ⟨w, hwH, hw, huniq, hrate, -⟩ := ex_9_10a Q h919 h920 hQ
  obtain rfl := huniq v hvH hv
  set T := crsT Q Γ F β
  have hfull : ∀ f : XS × Z → ℝ, InHS hX f → (∀ z, IsConcaveS hC fun x => f (x, z)) →
      ∀ z, IsConcaveS hC fun x => T f (x, z) := by
    intro f hf hconc z x x' θ h0 h1
    rcases h0.eq_or_lt with rfl | h0'
    · rw [cmb_zero]; simp
    rcases h1.eq_or_lt with rfl | h1'
    · rw [cmb_one]; simp
    exact (crsT_concave Q hC h919 h920 hQ hF h911 hf hconc z x x' θ h0' h1').1
  have hTH : ∀ f, InHS hX f → InHS hX (T f) := fun f hf => crsT_mapsTo Q h919 h920 hQ hf
  have hiter : ∀ n, InHS hX (T^[n] 0) ∧ ∀ z, IsConcaveS hC fun x => T^[n] 0 (x, z) := by
    intro n
    induction n with
    | zero => exact ⟨inHS_zero, fun z x x' θ _ _ => by simp⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨hTH _ ih.1, hfull _ ih.1 ih.2⟩
  -- pointwise convergence of the iterates
  have hpt : ∀ p : XS × Z, Tendsto (fun n => T^[n] 0 p) atTop (𝓝 (v p)) := by
    intro p
    have hαβ : 0 ≤ α * β := mul_nonneg h919.α_pos.le h920.β_pos.le
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg)
      (fun n => ?_) (((tendsto_pow_atTop_nhds_zero_of_lt_one hαβ h919.αβ_lt).mul_const
        (hnormS XS (0 - v) * ‖p.1.1‖)).trans_eq (by simp)))
    rw [Real.dist_eq]
    have := abs_le_hnormS' (inHS_sub (hiter n).1 hvH) p
    simp only [Pi.sub_apply] at this
    refine this.trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hrate 0 inHS_zero n) (norm_nonneg _)
  have hconc : ∀ z, IsConcaveS hC fun x => v (x, z) := fun z x x' θ h0 h1 =>
    le_of_tendsto_of_tendsto' (((hpt (x, z)).const_mul θ).add ((hpt (x', z)).const_mul _))
      (hpt _) fun n => (hiter n).2 z x x' θ h0 h1
  refine ⟨hconc, fun z x x' hnp θ h0 h1 => ?_⟩
  have := (crsT_concave Q hC h919 h920 hQ hF h911 hvH hconc z x x' θ h0 h1).2 hnp
  change θ * T v (x, z) + (1 - θ) * T v (x', z) < T v (cmb hC h0.le h1.le x x', z) at this
  rwa [hw] at this

omit [OpensMeasurableSpace Z] in
/-- **Exercise 9.10c (monotonicity).** Under Assumptions 9.8 and 9.9, `v(·, z)` is strictly
increasing. -/
theorem ex_9_10c_mono (h919 : Assume919 hX Γ β α) (h920 : Assume920 hX Γ F β B)
    (hQ : PreservesBC XS Q)
    (h98 : ∀ x x' y z, x < x' → y ∈ Γ (x, z) → F (x, y, z) < F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → Γ (x, z) ⊆ Γ (x', z)) {v : XS × Z → ℝ} (hvH : InHS hX v)
    (hv : crsT Q Γ F β v = v) (z : Z) : StrictMono fun x => v (x, z) := by
  intro x x' hxx'
  obtain ⟨y, hy, hval, -⟩ := exists_crsT_argmax Q h919 h920 hQ hvH (x, z)
  obtain ⟨-, -, -, hmax⟩ := exists_crsT_argmax Q h919 h920 hQ hvH (x', z)
  rw [congrFun hv] at hval hmax
  have := hmax y (h99 x x' z hxx'.le hy)
  dsimp only at hval this ⊢
  rw [hval]
  linarith [h98 x x' y z hxx' hy]

/-- **Exercise 9.10c (differentiability).** Under the hypotheses of Exercise 9.10b, if
`x₀ ∈ int X`, `y₀ ∈ G(x₀, z₀)` lies in the interior of `Γ(x₀, z₀)`, and `F(·, y₀, z₀)` has
derivative `DF` at `x₀`, then `v(·, z₀)` is differentiable at `x₀` with derivative `DF`. -/
theorem ex_9_10c_diff (hC : Convex ℝ XS) (h919 : Assume919 hX Γ β α)
    (h920 : Assume920 hX Γ F β B) (hQ : PreservesBC XS Q) (hF : ConcaveCRS hC Γ F)
    (h911 : Assumption911 hC hC (Model.first Q Γ F β)) {v : XS × Z → ℝ} (hvH : InHS hX v)
    (hv : crsT Q Γ F β v = v) {x₀ : XS} {z₀ : Z} (hint : XS ∈ 𝓝 x₀.1) {y₀ : XS}
    (hy₀ : y₀ ∈ argmax (objG (Model.first Q Γ F β) v) Γ (x₀, z₀))
    (hg : y₀.1 ∈ interior (Subtype.val '' Γ (x₀, z₀))) {DF : (Fin l → ℝ) →L[ℝ] ℝ}
    (hFd : HasFDerivAt (liftS fun x => F (x, y₀, z₀)) DF x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) DF x₀.1 := by
  have hvc := (ex_9_10b Q hC h919 h920 hQ hF h911 hvH hv).1 z₀
  set c := β * mop Q v (y₀, z₀)
  set W : (Fin l → ℝ) → ℝ := fun x => liftS (fun x => F (x, y₀, z₀)) x + c
  have hW : HasFDerivAt W DF x₀.1 := hFd.add_const c
  have hvx : ∀ s, v s = maxValue (objG (Model.first Q Γ F β) v) Γ s := fun s =>
    (congrFun hv s).symm
  have heq : W x₀.1 = liftS (fun x => v (x, z₀)) x₀.1 := by
    simp only [W, liftS_of_mem _ x₀.2, Subtype.coe_eta]
    rw [hvx (x₀, z₀), ← hy₀.2, objG_first]
  have hle : ∀ᶠ x in 𝓝 x₀.1, W x ≤ liftS (fun x => v (x, z₀)) x := by
    have h1 := eventually_mem_Γ (Model.first Q Γ F β) h919.lhc h911 hg
    rw [nhds_subtype, eventually_comap] at h1
    filter_upwards [h1, hint] with x hx hxS
    simp only [W, liftS_of_mem _ hxS]
    rw [hvx (⟨x, hxS⟩, z₀)]
    have := le_maxValue (continuousOn_objG_crs Q h920 hQ hvH) (h919.compact _)
      (hx ⟨x, hxS⟩ rfl)
    rwa [objG_first] at this
  exact theorem_4_10 (concaveOn_liftS hvc) hint hW heq hle

end StokeyLucasPrescott.StochasticDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 9.12: unbounded returns

SLP §9.4, pp. 273–274. Let `v` solve the functional equation, and let `Π̂(s₀)` be the feasible
plans along which the limit condition (2), `βᵗ ∫ v(s_t) dμᵗ → 0`, holds (`IsHatFeasible`), with
`v̂(s₀) = sup_{π ∈ Π̂(s₀)} u(π, s₀)` (`vHat`). **Theorem 9.12** (`theorem_9_12`): if the plan `π*`
generated by `G` from `s₀` lies in `Π̂(s₀)` (a), and every feasible plan is weakly dominated by
one in `Π̂(s₀)` (b), then `v*(s₀) = v̂(s₀) = v(s₀) = u(π*, s₀)`. The proof is Theorem 9.2's
argument applied plan by plan (`planValue_le_of_limit`, `planValue_genPlan_of_limit`); the
book's sequence `π̂ᵏ` is replaced by taking suprema directly.
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (M : Model X Y Z) [IsMarkovKernel M.Q]

/-- `π ∈ Π̂(s₀)`: `π` is feasible and `βᵗ ∫ v(s_t) dμᵗ → 0` along `π` (condition (2)). -/
def IsHatFeasible (v : X × Z → ℝ) (s₀ : X × Z) (π : Plan Y Z) : Prop :=
  IsFeasible M s₀ π ∧
    Tendsto (fun t => M.β ^ t * ∫ h, v (state M s₀ π t h) ∂hist M.Q t s₀.2) atTop (𝓝 0)

/-- `v̂(s₀) = sup_{π ∈ Π̂(s₀)} u(π, s₀)`. -/
noncomputable def vHat (v : X × Z → ℝ) (s₀ : X × Z) : EReal :=
  ⨆ (π : Plan Y Z) (_ : IsHatFeasible M v s₀ π), planValue M s₀ π

/-- **Theorem 9.12.** Let `v` be measurable and solve the functional equation, with the returns
and `v(s_t)` integrable and `uₙ` convergent along feasible plans (Assumption 9.2), and let `π*`
be generated by measurable selections from `G`. If (a) `π* ∈ Π̂(s₀)` and (b) every feasible plan
is weakly dominated by a plan in `Π̂(s₀)`, then `v*(s₀) = v̂(s₀) = v(s₀) = u(π*, s₀)`. -/
theorem theorem_9_12 (hφ : Measurable M.φ) (hβ : 0 ≤ M.β) {v : X × Z → ℝ}
    (hFE : SolvesFE M v) (s₀ : X × Z)
    (hint : ∀ π, IsFeasible M s₀ π → ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2) ∧
      Integrable (fun h => v (state M s₀ π t h)) (hist M.Q t s₀.2))
    (hconv : ∀ π, IsFeasible M s₀ π → ∃ L, Tendsto (fun n => (uN M s₀ π n : EReal)) atTop (𝓝 L))
    {g : ℕ → X × Z → Y} (hg : ∀ t, Measurable (g t)) (hgG : ∀ t s, g t s ∈ policy M v s)
    (ha : Tendsto (fun t => M.β ^ t *
      ∫ h, v (state M s₀ (genPlan M s₀ g) t h) ∂hist M.Q t s₀.2) atTop (𝓝 0))
    (hb : ∀ π, IsFeasible M s₀ π →
      ∃ π', IsHatFeasible M v s₀ π' ∧ planValue M s₀ π ≤ planValue M s₀ π') :
    vStar M s₀ = v s₀ ∧ vHat M v s₀ = v s₀ ∧ planValue M s₀ (genPlan M s₀ g) = v s₀ := by
  have hfeas := genPlan_feasible M hφ s₀ hg fun t s => (hgG t s).1
  have hattain := (planValue_genPlan_of_limit M hφ hFE s₀ hg hgG (hint _ hfeas) ha).2
  have hhat : vHat M v s₀ = v s₀ := by
    refine le_antisymm (iSup₂_le fun π hπ =>
      planValue_le_of_limit M hβ hFE hπ.1 (hint π hπ.1) (hconv π hπ.1) hπ.2) ?_
    rw [← hattain]
    exact le_iSup₂ (f := fun π (_ : IsHatFeasible M v s₀ π) => planValue M s₀ π) _ ⟨hfeas, ha⟩
  refine ⟨le_antisymm ?_ ?_, hhat, hattain⟩
  · refine iSup₂_le fun π hπ => ?_
    obtain ⟨π', hπ', hle⟩ := hb π hπ
    rw [← hhat]
    exact hle.trans (le_iSup₂ (f := fun π (_ : IsHatFeasible M v s₀ π) => planValue M s₀ π)
      π' hπ')
  · rw [← hhat]
    exact iSup₂_le fun π hπ =>
      le_iSup₂ (f := fun π (_ : IsFeasible M s₀ π) => planValue M s₀ π) π hπ.1

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The linear-quadratic example with autoregressive shocks

SLP §9.4, pp. 277–280: shocks `z_{t+1} = ρz_t + u_{t+1}` with `0 < ρ < 1` and `u_t` i.i.d. with
finite variance (`arKernel`).

* **Exercise 9.12** (`ex_9_12`): `∫ |z_t| dμᵗ < A` and `∫ z_t² dμᵗ < B` for all `t`. The proof
  bounds the second moments recursively: `(ρz + u)² ≤ ρz² + u²/(1 − ρ)` (convexity of the square),
  so `E z_{t+1}² ≤ ρ E z_t² + E u²/(1 − ρ)`.
* **Exercise 9.13** (`ex_9_13`, corrected): the functional equation is solved by a quadratic
  `v₀ + v₁z + v₂x + v₃zx − v₄x² + v₅z²` with `v₄, v₅ > 0` and a linear policy with slope
  `0 < g₁ < 1`. The book's form (9) has no `z²` term, and no function of that form is a solution
  (`ex_9_13_book_form`).
* **Exercise 9.14** (`ex_9_14`): along the plan generated by a linear policy with `0 < g₁ < 1`,
  `βᵗ ∫ v(x_t, z_t) dμᵗ → 0` (condition (a) of Theorem 9.12).
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- The transition function of `z′ = ρz + u`, `u ~ λ`. -/
noncomputable def arKernel (ρ : ℝ) (lam : Measure ℝ) : Kernel ℝ ℝ :=
  ((Kernel.deterministic id measurable_id) ×ₖ Kernel.const ℝ lam).map fun p => ρ * p.1 + p.2

theorem measurable_ar (ρ : ℝ) : Measurable fun p : ℝ × ℝ => ρ * p.1 + p.2 :=
  (measurable_const.mul measurable_fst).add measurable_snd

variable {ρ : ℝ} {lam : Measure ℝ}

theorem arKernel_apply [IsProbabilityMeasure lam] (z : ℝ) :
    arKernel ρ lam z = lam.map fun u => ρ * z + u := by
  rw [arKernel, Kernel.map_apply _ (measurable_ar ρ), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_ar ρ) measurable_prodMk_left]
  rfl

theorem isMarkovKernel_arKernel [IsProbabilityMeasure lam] : IsMarkovKernel (arKernel ρ lam) := by
  unfold arKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_ar ρ)

/-- `(ρz + u)² ≤ ρz² + u²/(1 − ρ)` for `0 < ρ < 1`. -/
theorem sq_ar_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (z u : ℝ) :
    (ρ * z + u) ^ 2 ≤ ρ * z ^ 2 + (1 - ρ)⁻¹ * u ^ 2 := by
  have h1 : 0 < 1 - ρ := sub_pos.2 hρ1
  have key : ρ * z ^ 2 + (1 - ρ)⁻¹ * u ^ 2 - (ρ * z + u) ^ 2 =
      ρ * (1 - ρ) * (z - (1 - ρ)⁻¹ * u) ^ 2 := by
    field_simp
    ring
  nlinarith [mul_nonneg (mul_nonneg hρ0.le h1.le) (sq_nonneg (z - (1 - ρ)⁻¹ * u))]

/-- The second moments `E z_t²` are bounded uniformly in `t` (the core of Exercise 9.12). -/
theorem ar_lintegral_sq_le [IsProbabilityMeasure lam] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlam2 : Integrable (fun u => u ^ 2) lam) (z₀ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, ∫⁻ h, ENNReal.ofReal (lastState z₀ h ^ 2) ∂hist (arKernel ρ lam) t z₀ ≤
      ENNReal.ofReal K := by
  have hQ : IsMarkovKernel (arKernel ρ lam) := isMarkovKernel_arKernel
  set Q := arKernel ρ lam
  have h1 : 0 < 1 - ρ := sub_pos.2 hρ1
  set m := ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂lam
  have hm : m ≠ ⊤ := hlam2.lintegral_lt_top.ne
  set c : ℝ := (1 - ρ)⁻¹ * m.toReal
  have hc : 0 ≤ c := mul_nonneg (inv_nonneg.2 h1.le) ENNReal.toReal_nonneg
  have hstep : ∀ z : ℝ, ∫⁻ z', ENNReal.ofReal (z' ^ 2) ∂Q z ≤ ENNReal.ofReal (ρ * z ^ 2 + c) := by
    intro z
    rw [arKernel_apply, lintegral_map (by fun_prop) (by fun_prop)]
    calc ∫⁻ u, ENNReal.ofReal ((ρ * z + u) ^ 2) ∂lam
        ≤ ∫⁻ u, ENNReal.ofReal (ρ * z ^ 2) + ENNReal.ofReal (1 - ρ)⁻¹ * ENNReal.ofReal (u ^ 2)
          ∂lam := lintegral_mono fun u => by
            rw [← ENNReal.ofReal_mul (inv_nonneg.2 h1.le), ← ENNReal.ofReal_add
              (mul_nonneg hρ0.le (sq_nonneg z)) (mul_nonneg (inv_nonneg.2 h1.le) (sq_nonneg u))]
            exact ENNReal.ofReal_le_ofReal (sq_ar_le hρ0 hρ1 z u)
      _ = ENNReal.ofReal (ρ * z ^ 2) + ENNReal.ofReal (1 - ρ)⁻¹ * m := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ (by fun_prop)]
      _ = ENNReal.ofReal (ρ * z ^ 2 + c) := by
          rw [ENNReal.ofReal_add (mul_nonneg hρ0.le (sq_nonneg z)) hc, ENNReal.ofReal_mul
            (inv_nonneg.2 h1.le), ENNReal.ofReal_toReal hm]
  set K : ℝ := max (z₀ ^ 2) (c / (1 - ρ))
  have hK : ρ * K + c ≤ K := by
    have : c ≤ (1 - ρ) * K := by
      rw [← div_le_iff₀' h1]
      exact le_max_right _ _
    linarith
  have hlin : ∀ t, ∫⁻ h, ENNReal.ofReal (lastState z₀ h ^ 2) ∂hist Q t z₀ ≤ ENNReal.ofReal K := by
    intro t
    induction t with
    | zero =>
      rw [hist_zero_lintegral]
      exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    | succ t ih =>
      have := ex_8_8a Q t
      rw [hist_succ_lintegral_last Q t z₀ (by
        exact ENNReal.measurable_ofReal.comp ((measurable_lastState z₀ (t + 1)).pow_const 2))]
      simp_rw [lastState_snoc]
      calc ∫⁻ h, ∫⁻ z', ENNReal.ofReal (z' ^ 2) ∂Q (lastState z₀ h) ∂hist Q t z₀
          ≤ ∫⁻ h, ENNReal.ofReal (ρ * lastState z₀ h ^ 2 + c) ∂hist Q t z₀ :=
            lintegral_mono fun h => hstep _
        _ = ENNReal.ofReal ρ * ∫⁻ h, ENNReal.ofReal (lastState z₀ h ^ 2) ∂hist Q t z₀ +
            ENNReal.ofReal c := by
            simp_rw [ENNReal.ofReal_add (mul_nonneg hρ0.le (sq_nonneg _)) hc,
              ENNReal.ofReal_mul hρ0.le]
            rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ (by
              exact ENNReal.measurable_ofReal.comp ((measurable_lastState z₀ t).pow_const 2)),
              lintegral_const, measure_univ, mul_one]
        _ ≤ ENNReal.ofReal ρ * ENNReal.ofReal K + ENNReal.ofReal c := by gcongr
        _ = ENNReal.ofReal (ρ * K + c) := by
            rw [← ENNReal.ofReal_mul hρ0.le, ← ENNReal.ofReal_add
              (mul_nonneg hρ0.le ((sq_nonneg z₀).trans (le_max_left _ _))) hc]
        _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hK
  exact ⟨K, (sq_nonneg z₀).trans (le_max_left _ _), hlin⟩

/-- **Exercise 9.12.** If `0 < ρ < 1` and `u` has a finite second moment, then for any `z₀` there
are constants `A, B` with `∫ |z_t| μᵗ(z₀, dzᵗ) < A` and `∫ z_t² μᵗ(z₀, dzᵗ) < B` for all `t`. -/
theorem ex_9_12 [IsProbabilityMeasure lam] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlam2 : Integrable (fun u => u ^ 2) lam) (z₀ : ℝ) :
    ∃ A B : ℝ, ∀ t, Integrable (fun h => lastState z₀ h) (hist (arKernel ρ lam) t z₀) ∧
      Integrable (fun h => lastState z₀ h ^ 2) (hist (arKernel ρ lam) t z₀) ∧
      ∫ h, |lastState z₀ h| ∂hist (arKernel ρ lam) t z₀ < A ∧
      ∫ h, lastState z₀ h ^ 2 ∂hist (arKernel ρ lam) t z₀ < B := by
  have hQ : IsMarkovKernel (arKernel ρ lam) := isMarkovKernel_arKernel
  set Q := arKernel ρ lam
  obtain ⟨K, hK0, hlin⟩ := ar_lintegral_sq_le hρ0 hρ1 hlam2 z₀
  refine ⟨K + 2, K + 1, fun t => ?_⟩
  have := ex_8_8a Q t
  have hmeas : Measurable fun h : Fin t → ℝ => lastState z₀ h := measurable_lastState z₀ t
  have hI2 : Integrable (fun h => lastState z₀ h ^ 2) (hist Q t z₀) :=
    (lintegral_ofReal_ne_top_iff_integrable (hmeas.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun h => sq_nonneg _)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (hlin t))
  have hI1 : Integrable (fun h => lastState z₀ h) (hist Q t z₀) :=
    ((integrable_const 1).add hI2).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun h => by
        rw [Real.norm_eq_abs, Pi.add_apply]
        nlinarith [sq_nonneg (|lastState z₀ h| - 1), sq_abs (lastState z₀ h)])
  have hint2 : ∫ h, lastState z₀ h ^ 2 ∂hist Q t z₀ ≤ K := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun h => sq_nonneg _)
      (hmeas.pow_const 2).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hK0 (hlin t)
  refine ⟨hI1, hI2, ?_, by linarith⟩
  calc ∫ h, |lastState z₀ h| ∂hist Q t z₀ ≤ ∫ h, (1 + lastState z₀ h ^ 2) ∂hist Q t z₀ :=
        integral_mono hI1.abs ((integrable_const 1).add hI2) fun h => by
          nlinarith [sq_nonneg (|lastState z₀ h| - 1), sq_abs (lastState z₀ h)]
    _ = 1 + ∫ h, lastState z₀ h ^ 2 ∂hist Q t z₀ := by
        rw [integral_add (integrable_const 1) hI2]; simp
    _ < K + 2 := by linarith

/-! ### Exercise 9.13 -/

/-- The quadratic example (first formulation): `X = Z = ℝ`, `Γ ≡ ℝ`,
`F(x, y, z) = zx − ½bx² − ½c(y − x)²`, and `z′ = ρz + u`. -/
noncomputable def quadModel (ρ : ℝ) (lam : Measure ℝ) (b c β : ℝ) : Model ℝ ℝ ℝ :=
  Model.first (arKernel ρ lam) (fun _ => univ)
    (fun p => p.2.2 * p.1 - b / 2 * p.1 ^ 2 - c / 2 * (p.2.1 - p.1) ^ 2) β

/-- `v(x, z) = v₀ + v₁z + v₂x + v₃zx − v₄x² + v₅z²`. -/
def quadV (v₀ v₁ v₂ v₃ v₄ v₅ : ℝ) (s : ℝ × ℝ) : ℝ :=
  v₀ + v₁ * s.2 + v₂ * s.1 + v₃ * s.2 * s.1 - v₄ * s.1 ^ 2 + v₅ * s.2 ^ 2

/-- `∫ (w₀ + w₁z′ + w₂z′²) Q(z, dz′) = w₀ + w₁(ρz + ū) + w₂(ρ²z² + 2ρzū + E u²)`. -/
theorem integral_quad_ar [IsProbabilityMeasure lam] (hlam1 : Integrable (fun u => u) lam)
    (hlam2 : Integrable (fun u => u ^ 2) lam) (z w₀ w₁ w₂ : ℝ) :
    ∫ z', (w₀ + w₁ * z' + w₂ * z' ^ 2) ∂arKernel ρ lam z =
      w₀ + w₁ * (ρ * z + ∫ u, u ∂lam) +
        w₂ * (ρ ^ 2 * z ^ 2 + 2 * ρ * z * ∫ u, u ∂lam + ∫ u, u ^ 2 ∂lam) := by
  rw [arKernel_apply, integral_map (by fun_prop) (by fun_prop)]
  have e : ∀ u : ℝ, w₀ + w₁ * (ρ * z + u) + w₂ * (ρ * z + u) ^ 2 =
      (w₀ + w₁ * ρ * z + w₂ * ρ ^ 2 * z ^ 2) + (w₁ + 2 * w₂ * ρ * z) * u + w₂ * u ^ 2 :=
    fun u => by ring
  simp_rw [e]
  have i0 : Integrable (fun _ : ℝ => w₀ + w₁ * ρ * z + w₂ * ρ ^ 2 * z ^ 2) lam :=
    integrable_const _
  have i1 : Integrable (fun u : ℝ => (w₁ + 2 * w₂ * ρ * z) * u) lam := hlam1.const_mul _
  have i2 : Integrable (fun u : ℝ => w₂ * u ^ 2) lam := hlam2.const_mul _
  have i01 : Integrable (fun u : ℝ => w₀ + w₁ * ρ * z + w₂ * ρ ^ 2 * z ^ 2 +
      (w₁ + 2 * w₂ * ρ * z) * u) lam := i0.add i1
  rw [integral_add i01 i2, integral_add i0 i1, integral_const, integral_const_mul,
    integral_const_mul]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  ring

/-- The coefficient identity behind Exercise 9.13: with `D = c + 2βv₄`, `K₀ = β(v₂ + v₃ū)`,
`K₁ = βv₃ρ` and the six coefficient equations, the right side of the functional equation is
`v(x, z) − (D/2)(y − (cx + K₀ + K₁z)/D)²`. -/
theorem quad_rhs_eq {b c β ρ ub m₂ v₀ v₁ v₂ v₃ v₄ v₅ D K₀ K₁ : ℝ} (hD : D ≠ 0)
    (hDd : D = c + 2 * β * v₄) (hK₀d : K₀ = β * (v₂ + v₃ * ub)) (hK₁d : K₁ = β * v₃ * ρ)
    (hR4 : -D * (b + c) + 2 * D * v₄ + c ^ 2 = 0) (hR3 : 2 * D * (1 - v₃) + 2 * c * K₁ = 0)
    (hR2 : -2 * D * v₂ + 2 * c * K₀ = 0)
    (hR5 : 2 * D * (β * v₅ * ρ ^ 2 - v₅) + K₁ ^ 2 = 0)
    (hR1 : 2 * D * (β * v₁ * ρ + 2 * β * v₅ * ρ * ub - v₁) + 2 * K₀ * K₁ = 0)
    (hR0 : 2 * D * (β * v₀ + β * v₁ * ub + β * v₅ * m₂ - v₀) + K₀ ^ 2 = 0) (x z y : ℝ) :
    z * x - b / 2 * x ^ 2 - c / 2 * (y - x) ^ 2 +
        β * ((v₀ + v₂ * y - v₄ * y ^ 2) + (v₁ + v₃ * y) * (ρ * z + ub) +
          v₅ * (ρ ^ 2 * z ^ 2 + 2 * ρ * z * ub + m₂)) =
      quadV v₀ v₁ v₂ v₃ v₄ v₅ (x, z) - D / 2 * (y - (c * x + K₀ + K₁ * z) / D) ^ 2 := by
  have key : 2 * D * ((z * x - b / 2 * x ^ 2 - c / 2 * (y - x) ^ 2 +
      β * ((v₀ + v₂ * y - v₄ * y ^ 2) + (v₁ + v₃ * y) * (ρ * z + ub) +
        v₅ * (ρ ^ 2 * z ^ 2 + 2 * ρ * z * ub + m₂))) -
      (quadV v₀ v₁ v₂ v₃ v₄ v₅ (x, z) - D / 2 * (y - (c * x + K₀ + K₁ * z) / D) ^ 2)) = 0 := by
    simp only [quadV]
    subst hK₀d hK₁d
    field_simp
    subst hDd
    linear_combination x ^ 2 * hR4 + x * z * hR3 + x * hR2 + z ^ 2 * hR5 + z * hR1 + hR0
  have := (mul_eq_zero.1 key).resolve_left (mul_ne_zero two_ne_zero hD)
  linarith

/-- The coefficients of Exercise 9.13: `v₄` is the positive root of
`2βv² + ((1 − β)c − βb)v − bc/2 = 0`, and the rest solve the coefficient equations in turn. -/
theorem quad_coeffs {b c β ρ : ℝ} (ub m₂ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hb : 0 < b)
    (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ v₀ v₁ v₂ v₃ v₄ v₅ D K₀ K₁ : ℝ, 0 < v₄ ∧ 0 < v₅ ∧ 0 < D ∧ c < D ∧
      D = c + 2 * β * v₄ ∧ K₀ = β * (v₂ + v₃ * ub) ∧ K₁ = β * v₃ * ρ ∧
      -D * (b + c) + 2 * D * v₄ + c ^ 2 = 0 ∧ 2 * D * (1 - v₃) + 2 * c * K₁ = 0 ∧
      -2 * D * v₂ + 2 * c * K₀ = 0 ∧ 2 * D * (β * v₅ * ρ ^ 2 - v₅) + K₁ ^ 2 = 0 ∧
      2 * D * (β * v₁ * ρ + 2 * β * v₅ * ρ * ub - v₁) + 2 * K₀ * K₁ = 0 ∧
      2 * D * (β * v₀ + β * v₁ * ub + β * v₅ * m₂ - v₀) + K₀ ^ 2 = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, k = (1 - β) * c - β * b := ⟨_, rfl⟩
  obtain ⟨sq, hsqd⟩ : ∃ sq, sq = Real.sqrt (k ^ 2 + 4 * β * b * c) := ⟨_, rfl⟩
  have hsq : sq ^ 2 = k ^ 2 + 4 * β * b * c := by rw [hsqd]; exact Real.sq_sqrt (by positivity)
  have hksq : k < sq := by
    calc k ≤ |k| := le_abs_self k
      _ = Real.sqrt (k ^ 2) := (Real.sqrt_sq_eq_abs k).symm
      _ < sq := by
          rw [hsqd]
          exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith [mul_pos (mul_pos hβ0 hb) hc])
  obtain ⟨v₄, hv₄d⟩ : ∃ v₄, v₄ = (sq - k) / (4 * β) := ⟨_, rfl⟩
  have hv₄ : 0 < v₄ := by rw [hv₄d]; exact div_pos (by linarith) (by positivity)
  have hE4 : 2 * β * v₄ ^ 2 + k * v₄ - b * c / 2 = 0 := by
    rw [hv₄d]
    field_simp
    linear_combination 4 * hsq
  obtain ⟨D, hDd⟩ : ∃ D, D = c + 2 * β * v₄ := ⟨_, rfl⟩
  have hD : 0 < D := by rw [hDd]; positivity
  have hcD : c < D := by rw [hDd]; nlinarith [mul_pos hβ0 hv₄]
  have hρβ : β * ρ < 1 := by nlinarith
  have hDρ : 0 < D - c * β * ρ := by nlinarith
  have hDβ : 0 < D - c * β := by nlinarith
  obtain ⟨v₃, hv₃d⟩ : ∃ v₃, v₃ = D / (D - c * β * ρ) := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂d⟩ : ∃ v₂, v₂ = c * β * v₃ * ub / (D - c * β) := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀d⟩ : ∃ K₀, K₀ = β * (v₂ + v₃ * ub) := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁d⟩ : ∃ K₁, K₁ = β * v₃ * ρ := ⟨_, rfl⟩
  have h1βρ : 0 < 1 - β * ρ ^ 2 := by nlinarith
  have h1βρ' : 0 < 1 - β * ρ := by nlinarith
  have h1β : 0 < 1 - β := by linarith
  obtain ⟨v₅, hv₅d⟩ : ∃ v₅, v₅ = K₁ ^ 2 / (2 * D * (1 - β * ρ ^ 2)) := ⟨_, rfl⟩
  obtain ⟨v₁, hv₁d⟩ : ∃ v₁,
      v₁ = (4 * D * β * v₅ * ρ * ub + 2 * K₀ * K₁) / (2 * D * (1 - β * ρ)) := ⟨_, rfl⟩
  obtain ⟨v₀, hv₀d⟩ : ∃ v₀,
      v₀ = (2 * D * β * v₁ * ub + 2 * D * β * v₅ * m₂ + K₀ ^ 2) / (2 * D * (1 - β)) :=
    ⟨_, rfl⟩
  have hK₁ : 0 < K₁ := by
    rw [hK₁d, hv₃d]; exact mul_pos (mul_pos hβ0 (div_pos hD hDρ)) hρ0
  refine ⟨v₀, v₁, v₂, v₃, v₄, v₅, D, K₀, K₁, hv₄, ?_, hD, hcD, hDd, hK₀d, hK₁d, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hv₅d]; exact div_pos (pow_pos hK₁ 2) (by positivity)
  · rw [hDd]; rw [hk] at hE4; linear_combination 2 * hE4
  · rw [hK₁d, hv₃d]; field_simp; ring
  · rw [hK₀d, hv₂d]; field_simp; ring
  · rw [hv₅d]; field_simp; ring
  · rw [hv₁d]; field_simp; ring
  · rw [hv₀d]; field_simp; ring

/-- **Exercise 9.13** (corrected). For `b, c > 0`, `0 < β < 1` and `0 < ρ < 1`, with `u` of finite
variance, the functional equation has a solution
`v(x, z) = v₀ + v₁z + v₂x + v₃zx − v₄x² + v₅z²` with `v₄ > 0`, and the policy correspondence is
the single-valued `g(x, z) = g₀ + g₁x + g₂z` with `0 < g₁ < 1`. The book's form (9) omits the
`z²` term; here `v₅ > 0`, and no function of the form (9) solves the functional equation
(`ex_9_13_book_form`). -/
theorem ex_9_13 [IsProbabilityMeasure lam] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlam1 : Integrable (fun u => u) lam) (hlam2 : Integrable (fun u => u ^ 2) lam) {b c β : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ v₀ v₁ v₂ v₃ v₄ v₅ : ℝ, 0 < v₄ ∧ 0 < v₅ ∧
      SolvesFE (quadModel ρ lam b c β) (quadV v₀ v₁ v₂ v₃ v₄ v₅) ∧
      ∃ g₀ g₁ g₂ : ℝ, 0 < g₁ ∧ g₁ < 1 ∧
        ∀ s, policy (quadModel ρ lam b c β) (quadV v₀ v₁ v₂ v₃ v₄ v₅) s =
          {g₀ + g₁ * s.1 + g₂ * s.2} := by
  have hQ : IsMarkovKernel (arKernel ρ lam) := isMarkovKernel_arKernel
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, D, K₀, K₁, hv₄, hv₅, hD, hcD, hDd, hK₀d, hK₁d, hR4, hR3, hR2,
    hR5, hR1, hR0⟩ := quad_coeffs (∫ u, u ∂lam) (∫ u, u ^ 2 ∂lam) hρ0 hρ1 hb hc hβ0 hβ1
  have hrhs : ∀ (s : ℝ × ℝ) (y : ℝ), rhs (quadModel ρ lam b c β) (quadV v₀ v₁ v₂ v₃ v₄ v₅) s y =
      quadV v₀ v₁ v₂ v₃ v₄ v₅ s - D / 2 * (y - (c * s.1 + K₀ + K₁ * s.2) / D) ^ 2 := by
    rintro ⟨x, z⟩ y
    have hE : expV (quadModel ρ lam b c β) (quadV v₀ v₁ v₂ v₃ v₄ v₅) (x, z) y =
        (v₀ + v₂ * y - v₄ * y ^ 2) + (v₁ + v₃ * y) * (ρ * z + ∫ u, u ∂lam) +
          v₅ * (ρ ^ 2 * z ^ 2 + 2 * ρ * z * ∫ u, u ∂lam + ∫ u, u ^ 2 ∂lam) := by
      have e : ∀ z' : ℝ, quadV v₀ v₁ v₂ v₃ v₄ v₅ (y, z') =
          (v₀ + v₂ * y - v₄ * y ^ 2) + (v₁ + v₃ * y) * z' + v₅ * z' ^ 2 := fun z' => by
        simp only [quadV]; ring
      change ∫ z', quadV v₀ v₁ v₂ v₃ v₄ v₅ (y, z') ∂arKernel ρ lam z = _
      simp_rw [e]
      exact integral_quad_ar hlam1 hlam2 z _ _ _
    simp only [rhs, hE]
    exact quad_rhs_eq hD.ne' hDd hK₀d hK₁d hR4 hR3 hR2 hR5 hR1 hR0 x z y
  refine ⟨v₀, v₁, v₂, v₃, v₄, v₅, hv₄, hv₅, fun s => ?_, K₀ / D, c / D, K₁ / D,
    div_pos hc hD, (div_lt_one hD).2 hcD, fun s => ?_⟩
  · refine IsGreatest.isLUB ⟨⟨(c * s.1 + K₀ + K₁ * s.2) / D, mem_univ _, ?_⟩, ?_⟩
    · rw [hrhs]; simp
    · rintro _ ⟨y, -, rfl⟩
      rw [hrhs]
      nlinarith [sq_nonneg (y - (c * s.1 + K₀ + K₁ * s.2) / D)]
  · ext y
    rw [mem_singleton_iff]
    change (y ∈ (quadModel ρ lam b c β).Γ s ∧ _ = _) ↔ _
    rw [hrhs]
    constructor
    · rintro ⟨-, h⟩
      have h2 : D / 2 * (y - (c * s.1 + K₀ + K₁ * s.2) / D) ^ 2 = 0 := by linarith
      have h3 := (mul_eq_zero.1 h2).resolve_left (by positivity)
      have h4 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
      have : y = (c * s.1 + K₀ + K₁ * s.2) / D := by linarith
      rw [this]; field_simp; ring
    · intro h
      refine ⟨mem_univ _, ?_⟩
      rw [h]
      have : K₀ / D + c / D * s.1 + K₁ / D * s.2 - (c * s.1 + K₀ + K₁ * s.2) / D = 0 := by
        field_simp; ring
      rw [this]; ring

/-- **Correction to Exercise 9.13.** No function of the book's form (9),
`v(x, z) = v₀ + v₁z + v₂x + v₃zx − v₄x²` (no `z²` term), solves the functional equation when
`ρ > 0`. The maximized right side is `C(x, z) + L(x, z)²/(2D)` with `D = c + 2βv₄ > 0` and
`L = cx + β(v₂ + v₃(ρz + ū))`; its `z²` coefficient `(βv₃ρ)²/(2D)` must vanish, so `v₃ = 0`, but
then its `zx` coefficient is `1 ≠ v₃`. -/
theorem ex_9_13_book_form [IsProbabilityMeasure lam] (hρ0 : 0 < ρ)
    (hlam1 : Integrable (fun u => u) lam) (hlam2 : Integrable (fun u => u ^ 2) lam) {b c β : ℝ}
    (hc : 0 < c) (hβ0 : 0 < β) (v₀ v₁ v₂ v₃ v₄ : ℝ) :
    ¬SolvesFE (quadModel ρ lam b c β) (quadV v₀ v₁ v₂ v₃ v₄ 0) := by
  intro hFE
  have hQ : IsMarkovKernel (arKernel ρ lam) := isMarkovKernel_arKernel
  obtain ⟨ub, hub⟩ : ∃ ub, ub = ∫ u, u ∂lam := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ D, D = c + 2 * β * v₄ := ⟨_, rfl⟩
  -- the right side as a quadratic in `y`
  have hrhs : ∀ (x z y : ℝ), rhs (quadModel ρ lam b c β) (quadV v₀ v₁ v₂ v₃ v₄ 0) (x, z) y =
      -(D / 2) * y ^ 2 + (c * x + β * (v₂ + v₃ * (ρ * z + ub))) * y +
        (z * x - (b + c) / 2 * x ^ 2 + β * (v₀ + v₁ * (ρ * z + ub))) := by
    intro x z y
    have hE : expV (quadModel ρ lam b c β) (quadV v₀ v₁ v₂ v₃ v₄ 0) (x, z) y =
        (v₀ + v₂ * y - v₄ * y ^ 2) + (v₁ + v₃ * y) * (ρ * z + ub) +
          0 * (ρ ^ 2 * z ^ 2 + 2 * ρ * z * ub + ∫ u, u ^ 2 ∂lam) := by
      have e : ∀ z' : ℝ, quadV v₀ v₁ v₂ v₃ v₄ 0 (y, z') =
          (v₀ + v₂ * y - v₄ * y ^ 2) + (v₁ + v₃ * y) * z' + 0 * z' ^ 2 := fun z' => by
        simp only [quadV]; ring
      change ∫ z', quadV v₀ v₁ v₂ v₃ v₄ 0 (y, z') ∂arKernel ρ lam z = _
      simp_rw [e]
      rw [hub]
      exact integral_quad_ar hlam1 hlam2 z _ _ _
    simp only [rhs, hE]
    change z * x - b / 2 * x ^ 2 - c / 2 * (y - x) ^ 2 + β * _ = _
    rw [hDd]
    ring
  -- `D > 0`: otherwise the right side is unbounded at a state where `L = 1`
  have hD : 0 < D := by
    by_contra hD
    push Not at hD
    obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ = (1 - β * (v₂ + v₃ * ub)) / c := ⟨_, rfl⟩
    have hL : c * x₁ + β * (v₂ + v₃ * (ρ * 0 + ub)) = 1 := by
      rw [hx₁]; field_simp; ring
    obtain ⟨C₁, hC₁⟩ : ∃ C₁, C₁ = 0 * x₁ - (b + c) / 2 * x₁ ^ 2 + β * (v₀ + v₁ * (ρ * 0 + ub)) :=
      ⟨_, rfl⟩
    obtain ⟨y, hyd⟩ : ∃ y, y = max 0 (quadV v₀ v₁ v₂ v₃ v₄ 0 (x₁, 0) - C₁ + 1) := ⟨_, rfl⟩
    have hy := (hFE (x₁, 0)).1 ⟨y, mem_univ _, rfl⟩
    rw [hrhs, hL, ← hC₁] at hy
    have h1 : 0 ≤ -(D / 2) * y ^ 2 := by nlinarith [sq_nonneg y]
    have h2 : quadV v₀ v₁ v₂ v₃ v₄ 0 (x₁, 0) - C₁ + 1 ≤ y := by rw [hyd]; exact le_max_right _ _
    linarith
  -- the value is the maximum `C + L²/(2D)`
  have hval : ∀ x z : ℝ, quadV v₀ v₁ v₂ v₃ v₄ 0 (x, z) =
      (z * x - (b + c) / 2 * x ^ 2 + β * (v₀ + v₁ * (ρ * z + ub))) +
        (c * x + β * (v₂ + v₃ * (ρ * z + ub))) ^ 2 / (2 * D) := by
    intro x z
    obtain ⟨L, hLd⟩ : ∃ L, L = c * x + β * (v₂ + v₃ * (ρ * z + ub)) := ⟨_, rfl⟩
    obtain ⟨C, hCd⟩ : ∃ C, C = z * x - (b + c) / 2 * x ^ 2 + β * (v₀ + v₁ * (ρ * z + ub)) :=
      ⟨_, rfl⟩
    rw [← hLd, ← hCd]
    have hmax : IsGreatest (rhs (quadModel ρ lam b c β) (quadV v₀ v₁ v₂ v₃ v₄ 0) (x, z) ''
        (quadModel ρ lam b c β).Γ (x, z)) (C + L ^ 2 / (2 * D)) := by
      refine ⟨⟨L / D, mem_univ _, ?_⟩, ?_⟩
      · rw [hrhs, ← hLd, ← hCd]; field_simp; ring
      · rintro _ ⟨y, -, rfl⟩
        rw [hrhs, ← hLd, ← hCd]
        have : C + L ^ 2 / (2 * D) - (-(D / 2) * y ^ 2 + L * y + C) =
            D / 2 * (y - L / D) ^ 2 := by field_simp; ring
        nlinarith [sq_nonneg (y - L / D), hD]
    exact (hFE (x, z)).unique hmax.isLUB
  -- compare the `z²` and `zx` coefficients
  have e00 := hval 0 0
  have e01 := hval 0 1
  have e0m := hval 0 (-1)
  have e10 := hval 1 0
  have e11 := hval 1 1
  simp only [quadV] at e00 e01 e0m e10 e11
  field_simp at e00 e01 e0m e10 e11
  have hK : (β * v₃ * ρ) ^ 2 = 0 := by nlinarith
  have hv₃ : v₃ = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hK
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hβ0.ne'
      · exact h'
    · exact absurd h hρ0.ne'
  subst hv₃
  nlinarith

/-! ### Exercise 9.14 -/

/-- `|v(x, z)| ≤ C(1 + x² + z²)` for the quadratic `v`. -/
theorem abs_quadV_le (v₀ v₁ v₂ v₃ v₄ v₅ : ℝ) (s : ℝ × ℝ) :
    |quadV v₀ v₁ v₂ v₃ v₄ v₅ s| ≤
      (|v₀| + |v₁| + |v₂| + |v₃| + |v₄| + |v₅|) * (1 + s.1 ^ 2 + s.2 ^ 2) := by
  obtain ⟨x, z⟩ := s
  simp only [quadV]
  set B := 1 + x ^ 2 + z ^ 2
  have hB : ∀ (a m : ℝ), |m| ≤ B → |a * m| ≤ |a| * B := fun a m hm => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hm (abs_nonneg a)
  have h1 := abs_le.1 (hB v₀ 1 (by rw [abs_one]; nlinarith [sq_nonneg x, sq_nonneg z]))
  have h2 := abs_le.1 (hB v₁ z (by nlinarith [sq_nonneg (|z| - 1), sq_abs z, sq_nonneg x]))
  have h3 := abs_le.1 (hB v₂ x (by nlinarith [sq_nonneg (|x| - 1), sq_abs x, sq_nonneg z]))
  have h4 := abs_le.1 (hB v₃ (z * x) (by
    rw [abs_mul]; nlinarith [sq_nonneg (|z| - |x|), sq_abs z, sq_abs x]))
  have h5 := abs_le.1 (hB v₄ (x ^ 2) (by
    rw [abs_of_nonneg (sq_nonneg x)]; nlinarith [sq_nonneg z]))
  have h6 := abs_le.1 (hB v₅ (z ^ 2) (by
    rw [abs_of_nonneg (sq_nonneg z)]; nlinarith [sq_nonneg x]))
  rw [abs_le]
  constructor
  · nlinarith [h1.1, h2.1, h3.1, h4.1, h5.2, h6.1, mul_one v₀, mul_assoc v₃ z x]
  · nlinarith [h1.2, h2.2, h3.2, h4.2, h5.1, h6.2, mul_one v₀, mul_assoc v₃ z x]

/-- The linear policy `g(x, z) = g₀ + g₁x + g₂z`. -/
def linPolicy (g₀ g₁ g₂ : ℝ) : ℕ → ℝ × ℝ → ℝ := fun _ s => g₀ + g₁ * s.1 + g₂ * s.2

/-- **Exercise 9.14.** For the quadratic `v` and the plan generated by a linear policy with
`0 < g₁ < 1` (as in Exercise 9.13), condition (11) holds:
`βᵗ ∫ v(x_t, z_t) dμᵗ → 0`, i.e. the plan satisfies condition (a) of Theorem 9.12. The proof
bounds `E x_t²` recursively, `E x_{t+1}² ≤ g₁ E x_t² + (2g₀² + 2g₂² E z_t²)/(1 − g₁)`, using the
bound on `E z_t²` of Exercise 9.12. -/
theorem ex_9_14 [IsProbabilityMeasure lam] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlam2 : Integrable (fun u => u ^ 2) lam) {b c β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (v₀ v₁ v₂ v₃ v₄ v₅ g₀ g₁ g₂ : ℝ) (hg0 : 0 < g₁) (hg1 : g₁ < 1) (s₀ : ℝ × ℝ) :
    (∀ t, Integrable (fun h => quadV v₀ v₁ v₂ v₃ v₄ v₅ (state (quadModel ρ lam b c β) s₀
      (genPlan (quadModel ρ lam b c β) s₀ (linPolicy g₀ g₁ g₂)) t h))
      (hist (arKernel ρ lam) t s₀.2)) ∧
    Tendsto (fun t => β ^ t * ∫ h, quadV v₀ v₁ v₂ v₃ v₄ v₅ (state (quadModel ρ lam b c β) s₀
      (genPlan (quadModel ρ lam b c β) s₀ (linPolicy g₀ g₁ g₂)) t h)
      ∂hist (arKernel ρ lam) t s₀.2) atTop (𝓝 0) := by
  have hQ : IsMarkovKernel (arKernel ρ lam) := isMarkovKernel_arKernel
  set M := quadModel ρ lam b c β
  set Q := arKernel ρ lam
  set π := genPlan M s₀ (linPolicy g₀ g₁ g₂)
  have hφ : Measurable M.φ := measurable_snd.fst
  have hgm : ∀ t, Measurable (linPolicy g₀ g₁ g₂ t) := fun t => by
    unfold linPolicy; fun_prop
  have hπ : IsFeasible M s₀ π := genPlan_feasible M hφ s₀ hgm fun _ _ => mem_univ _
  have hst : ∀ t, Measurable (state M s₀ π t) := measurable_state M hφ s₀ hπ.1
  have hxs : ∀ t (h : Fin (t + 1) → ℝ), (state M s₀ π (t + 1) h).1 =
      g₀ + g₁ * (state M s₀ π t (Fin.init h)).1 + g₂ * (state M s₀ π t (Fin.init h)).2 := by
    intro t h
    simp only [π, state_genPlan]
    rfl
  obtain ⟨K, hK0, hZ⟩ := ar_lintegral_sq_le hρ0 hρ1 hlam2 s₀.2
  have h1g : 0 < 1 - g₁ := sub_pos.2 hg1
  set c₁ := 2 * (1 - g₁)⁻¹ * g₀ ^ 2
  set c₂ := 2 * (1 - g₁)⁻¹ * g₂ ^ 2
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  have hpt : ∀ x z : ℝ, (g₀ + g₁ * x + g₂ * z) ^ 2 ≤ g₁ * x ^ 2 + (c₁ + c₂ * z ^ 2) := by
    intro x z
    have h := sq_ar_le hg0 hg1 x (g₀ + g₂ * z)
    have h2 : (g₀ + g₂ * z) ^ 2 ≤ 2 * g₀ ^ 2 + 2 * g₂ ^ 2 * z ^ 2 := by
      nlinarith [sq_nonneg (g₀ - g₂ * z)]
    have h3 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 h1g.le)
    have e : g₀ + g₁ * x + g₂ * z = g₁ * x + (g₀ + g₂ * z) := by ring
    rw [e]
    simp only [c₁, c₂]
    nlinarith
  set Kx := max (s₀.1 ^ 2) ((c₁ + c₂ * K) / (1 - g₁))
  have hKx : g₁ * Kx + (c₁ + c₂ * K) ≤ Kx := by
    have : c₁ + c₂ * K ≤ (1 - g₁) * Kx := by
      rw [← div_le_iff₀' h1g]; exact le_max_right _ _
    linarith
  have hKx0 : 0 ≤ Kx := (sq_nonneg _).trans (le_max_left _ _)
  have hX : ∀ t, ∫⁻ h, ENNReal.ofReal ((state M s₀ π t h).1 ^ 2) ∂hist Q t s₀.2 ≤
      ENNReal.ofReal Kx := by
    intro t
    induction t with
    | zero =>
      rw [hist_zero_lintegral]
      exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    | succ t ih =>
      have := ex_8_8a Q t
      have hfm : Measurable fun h : Fin t → ℝ => ENNReal.ofReal ((g₀ + g₁ * (state M s₀ π t h).1 +
          g₂ * (state M s₀ π t h).2) ^ 2) :=
        ENNReal.measurable_ofReal.comp (((measurable_const.add
          (measurable_const.mul (hst t).fst)).add (measurable_const.mul (hst t).snd)).pow_const 2)
      calc ∫⁻ h, ENNReal.ofReal ((state M s₀ π (t + 1) h).1 ^ 2) ∂hist Q (t + 1) s₀.2
          = ∫⁻ h, ENNReal.ofReal ((g₀ + g₁ * (state M s₀ π t (Fin.init h)).1 +
              g₂ * (state M s₀ π t (Fin.init h)).2) ^ 2) ∂hist Q (t + 1) s₀.2 := by
            simp_rw [hxs]
        _ = ∫⁻ h, ENNReal.ofReal ((g₀ + g₁ * (state M s₀ π t h).1 +
              g₂ * (state M s₀ π t h).2) ^ 2) ∂hist Q t s₀.2 := lintegral_init Q t s₀.2 hfm
        _ ≤ ∫⁻ h, (ENNReal.ofReal g₁ * ENNReal.ofReal ((state M s₀ π t h).1 ^ 2) +
              (ENNReal.ofReal c₁ + ENNReal.ofReal c₂ *
                ENNReal.ofReal ((state M s₀ π t h).2 ^ 2))) ∂hist Q t s₀.2 :=
            lintegral_mono fun h => by
              rw [← ENNReal.ofReal_mul hg0.le, ← ENNReal.ofReal_mul hc₂, ← ENNReal.ofReal_add hc₁
                (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
              exact ENNReal.ofReal_le_ofReal (hpt _ _)
        _ = ENNReal.ofReal g₁ * ∫⁻ h, ENNReal.ofReal ((state M s₀ π t h).1 ^ 2) ∂hist Q t s₀.2 +
              (ENNReal.ofReal c₁ + ENNReal.ofReal c₂ *
                ∫⁻ h, ENNReal.ofReal (lastState s₀.2 h ^ 2) ∂hist Q t s₀.2) := by
            have hm1 : Measurable fun h => ENNReal.ofReal ((state M s₀ π t h).1 ^ 2) :=
              ENNReal.measurable_ofReal.comp ((hst t).fst.pow_const 2)
            have hm2 : Measurable fun h => ENNReal.ofReal ((state M s₀ π t h).2 ^ 2) :=
              ENNReal.measurable_ofReal.comp ((hst t).snd.pow_const 2)
            rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1,
              lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
              lintegral_const_mul _ hm2]
            rfl
        _ ≤ ENNReal.ofReal g₁ * ENNReal.ofReal Kx +
              (ENNReal.ofReal c₁ + ENNReal.ofReal c₂ * ENNReal.ofReal K) := by
            gcongr
            exact hZ t
        _ = ENNReal.ofReal (g₁ * Kx + (c₁ + c₂ * K)) := by
            rw [← ENNReal.ofReal_mul hg0.le, ← ENNReal.ofReal_mul hc₂, ← ENNReal.ofReal_add hc₁
              (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal Kx := ENNReal.ofReal_le_ofReal hKx
  set Cv := |v₀| + |v₁| + |v₂| + |v₃| + |v₄| + |v₅|
  have hCv : 0 ≤ Cv := by positivity
  -- integrability and the bound on `|∫ v(s_t)|`
  have hbound : ∀ t, Integrable (fun h => quadV v₀ v₁ v₂ v₃ v₄ v₅ (state M s₀ π t h))
      (hist Q t s₀.2) ∧
      |∫ h, quadV v₀ v₁ v₂ v₃ v₄ v₅ (state M s₀ π t h) ∂hist Q t s₀.2| ≤ Cv * (1 + Kx + K) := by
    intro t
    have := ex_8_8a Q t
    have hm1 : Measurable fun h => (state M s₀ π t h).1 ^ 2 := (hst t).fst.pow_const 2
    have hm2 : Measurable fun h : Fin t → ℝ => lastState s₀.2 h ^ 2 :=
      (measurable_lastState s₀.2 t).pow_const 2
    have hI1 : Integrable (fun h => (state M s₀ π t h).1 ^ 2) (hist Q t s₀.2) :=
      (lintegral_ofReal_ne_top_iff_integrable hm1.aestronglyMeasurable
        (Eventually.of_forall fun h => sq_nonneg _)).1
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hX t))
    have hI2 : Integrable (fun h : Fin t → ℝ => lastState s₀.2 h ^ 2) (hist Q t s₀.2) :=
      (lintegral_ofReal_ne_top_iff_integrable hm2.aestronglyMeasurable
        (Eventually.of_forall fun h => sq_nonneg _)).1
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hZ t))
    have hdom : Integrable (fun h => Cv * (1 + (state M s₀ π t h).1 ^ 2 +
        lastState s₀.2 h ^ 2)) (hist Q t s₀.2) :=
      (((integrable_const 1).add hI1).add hI2).const_mul Cv
    have hvm : Measurable fun h => quadV v₀ v₁ v₂ v₃ v₄ v₅ (state M s₀ π t h) := by
      have hq : Measurable (quadV v₀ v₁ v₂ v₃ v₄ v₅) := by unfold quadV; fun_prop
      exact hq.comp (hst t)
    have hpt' : ∀ h, ‖quadV v₀ v₁ v₂ v₃ v₄ v₅ (state M s₀ π t h)‖ ≤
        Cv * (1 + (state M s₀ π t h).1 ^ 2 + lastState s₀.2 h ^ 2) := fun h => by
      rw [Real.norm_eq_abs]; exact abs_quadV_le _ _ _ _ _ _ _
    have hI : Integrable (fun h => quadV v₀ v₁ v₂ v₃ v₄ v₅ (state M s₀ π t h)) (hist Q t s₀.2) :=
      hdom.mono' hvm.aestronglyMeasurable (Eventually.of_forall hpt')
    refine ⟨hI, ?_⟩
    have hx2 : ∫ h, (state M s₀ π t h).1 ^ 2 ∂hist Q t s₀.2 ≤ Kx := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun h => sq_nonneg _)
        hm1.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hKx0 (hX t)
    have hz2 : ∫ h, lastState s₀.2 h ^ 2 ∂hist Q t s₀.2 ≤ K := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun h => sq_nonneg _)
        hm2.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hK0 (hZ t)
    calc |∫ h, quadV v₀ v₁ v₂ v₃ v₄ v₅ (state M s₀ π t h) ∂hist Q t s₀.2|
        ≤ ∫ h, Cv * (1 + (state M s₀ π t h).1 ^ 2 + lastState s₀.2 h ^ 2) ∂hist Q t s₀.2 := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le hdom (Eventually.of_forall hpt')
      _ = Cv * (1 + ∫ h, (state M s₀ π t h).1 ^ 2 ∂hist Q t s₀.2 +
            ∫ h, lastState s₀.2 h ^ 2 ∂hist Q t s₀.2) := by
          have hI01 : Integrable (fun h => 1 + (state M s₀ π t h).1 ^ 2) (hist Q t s₀.2) :=
            (integrable_const 1).add hI1
          rw [integral_const_mul, integral_add hI01 hI2, integral_add (integrable_const 1) hI1]
          simp
      _ ≤ Cv * (1 + Kx + K) := by gcongr
  refine ⟨fun t => (hbound t).1, ?_⟩
  refine squeeze_zero_norm (a := fun t => Cv * (1 + Kx + K) * β ^ t) (fun t => ?_) ?_
  · rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hβ0, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbound t).2 (pow_nonneg hβ0 t)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul (Cv * (1 + Kx + K))

end StokeyLucasPrescott.StochasticDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stochastic growth model with logarithmic utility (Exercise 9.11)

SLP §9.4, pp. 274–277. `X = Z = ℝ₊₊`, `Γ(x, z) = (0, zx^α)`, `F(x, y, z) = ln(zx^α − y)`,
with i.i.d. shocks of distribution `μ` and `E ln z = m` finite. The solution of the functional
equation is `v(x, z) = A₀ + α/(1 − αβ) ln x + 1/(1 − αβ) ln z` (5), with policy
`g(x, z) = αβzx^α`.

**Exercise 9.11** (`ex_9_11`): the plans `π*(·; s₀)` generated by `g` satisfy condition (a) of
Theorem 9.12: `βᵗ ∫ v(x_t, z_t) dμᵗ → 0`. Along `π*`, `ln x_{t+1} = ln(αβ) + ln z_t + α ln x_t`,
so `E ln x_t` is bounded (`0 < α < 1`) and `E ln z_t` is `ln z₀` or `m`; hence `E v(x_t, z_t)` is
bounded and `βᵗ E v(x_t, z_t) → 0`.
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- The positive reals. -/
abbrev PosR := {x : ℝ // 0 < x}

/-- The growth model with logarithmic utility and i.i.d. shocks. -/
noncomputable def logModel (μ : Measure PosR) (α β : ℝ) : Model PosR PosR PosR :=
  Model.first (Kernel.const PosR μ) (fun s => {y | y.1 < s.2.1 * s.1.1 ^ α})
    (fun p => Real.log (p.2.2.1 * p.1.1 ^ α - p.2.1.1)) β

/-- The policy `g(x, z) = αβzx^α`. -/
noncomputable def logPolicy (α β : ℝ) (hαβ : 0 < α * β) : ℕ → PosR × PosR → PosR :=
  fun _ s => ⟨α * β * s.2.1 * s.1.1 ^ α, mul_pos (mul_pos hαβ s.2.2) (Real.rpow_pos_of_pos s.1.2 α)⟩

/-- `v(x, z) = A₀ + α/(1 − αβ) ln x + 1/(1 − αβ) ln z`. -/
noncomputable def logV (A₀ α β : ℝ) (s : PosR × PosR) : ℝ :=
  A₀ + α / (1 - α * β) * Real.log s.1.1 + 1 / (1 - α * β) * Real.log s.2.1

/-- **Exercise 9.11.** Along the plan generated by `g(x, z) = αβzx^α` from any `s₀`, the value
`v` of (5) is integrable at every date and `βᵗ ∫ v(x_t, z_t) dμᵗ → 0`: condition (a) of
Theorem 9.12 holds. -/
theorem ex_9_11 (μ : Measure PosR) [IsProbabilityMeasure μ]
    (hlog : Integrable (fun z : PosR => Real.log z.1) μ) {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (A₀ : ℝ) (s₀ : PosR × PosR) :
    (∀ t, Integrable (fun h => logV A₀ α β (state (logModel μ α β) s₀
      (genPlan (logModel μ α β) s₀ (logPolicy α β (mul_pos hα0 hβ0))) t h))
      (hist (Kernel.const PosR μ) t s₀.2)) ∧
    Tendsto (fun t => β ^ t * ∫ h, logV A₀ α β (state (logModel μ α β) s₀
      (genPlan (logModel μ α β) s₀ (logPolicy α β (mul_pos hα0 hβ0))) t h)
      ∂hist (Kernel.const PosR μ) t s₀.2) atTop (𝓝 0) := by
  have hαβ : 0 < α * β := mul_pos hα0 hβ0
  have hαβ1 : α * β < 1 := by nlinarith
  set M := logModel μ α β
  set Q := Kernel.const PosR μ
  set π := genPlan M s₀ (logPolicy α β hαβ)
  have hφ : Measurable M.φ := measurable_snd.fst
  have hgm : ∀ t, Measurable (logPolicy α β hαβ t) := fun t => by
    refine Measurable.subtype_mk ?_
    exact ((measurable_const.mul (measurable_subtype_coe.comp measurable_snd)).mul
      ((measurable_subtype_coe.comp measurable_fst).pow_const α))
  have hgΓ : ∀ t s, logPolicy α β hαβ t s ∈ M.Γ s := fun t s => by
    change α * β * s.2.1 * s.1.1 ^ α < s.2.1 * s.1.1 ^ α
    have hp : 0 < s.2.1 * s.1.1 ^ α := mul_pos s.2.2 (Real.rpow_pos_of_pos s.1.2 α)
    nlinarith
  have hπ : IsFeasible M s₀ π := genPlan_feasible M hφ s₀ hgm hgΓ
  have hst : ∀ t, Measurable (state M s₀ π t) := measurable_state M hφ s₀ hπ.1
  -- the logarithms of the state
  set lx : (t : ℕ) → (Fin t → PosR) → ℝ := fun t h => Real.log (state M s₀ π t h).1.1
  set lz : (t : ℕ) → (Fin t → PosR) → ℝ := fun t h => Real.log (state M s₀ π t h).2.1
  have hlxm : ∀ t, Measurable (lx t) := fun t =>
    Real.measurable_log.comp (measurable_subtype_coe.comp (hst t).fst)
  have hlzm : ∀ t, Measurable (lz t) := fun t =>
    Real.measurable_log.comp (measurable_subtype_coe.comp (hst t).snd)
  have hrec : ∀ t (h : Fin (t + 1) → PosR),
      lx (t + 1) h = Real.log (α * β) + lz t (Fin.init h) + α * lx t (Fin.init h) := by
    intro t h
    have e : (state M s₀ π (t + 1) h).1.1 = α * β * (state M s₀ π t (Fin.init h)).2.1 *
        (state M s₀ π t (Fin.init h)).1.1 ^ α := by
      simp only [π, state_genPlan]
      rfl
    simp only [lx, lz, e]
    have hz := (state M s₀ π t (Fin.init h)).2.2
    have hx := (state M s₀ π t (Fin.init h)).1.2
    rw [Real.log_mul (mul_pos hαβ hz).ne' (Real.rpow_pos_of_pos hx α).ne',
      Real.log_mul hαβ.ne' hz.ne', Real.log_rpow hx]
  -- the shocks: `ln z_t` is integrable with mean `ln z₀` or `m`
  set m := ∫ z, Real.log z.1 ∂μ
  set Cz := max |Real.log s₀.2.1| |m|
  have hlz : ∀ t, Integrable (lz t) (hist Q t s₀.2) ∧ |∫ h, lz t h ∂hist Q t s₀.2| ≤ Cz := by
    intro t
    have := ex_8_8a Q t
    cases t with
    | zero =>
      have hc : lz 0 = fun _ => Real.log s₀.2.1 := rfl
      rw [hc, integral_const]
      refine ⟨integrable_const _, ?_⟩
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      exact le_max_left _ _
    | succ t =>
      have hmap := map_last_hist_const μ t s₀.2
      have hc : lz (t + 1) = fun h => Real.log (lastState s₀.2 h).1 := rfl
      rw [hc]
      have hlog' : Integrable (fun z : PosR => Real.log z.1)
          ((hist Q (t + 1) s₀.2).map (lastState s₀.2)) := by rw [hmap]; exact hlog
      refine ⟨hlog'.comp_measurable (measurable_lastState s₀.2 (t + 1)), ?_⟩
      have hint := integral_map (measurable_lastState s₀.2 (t + 1)).aemeasurable
        hlog'.aestronglyMeasurable
      rw [hmap] at hint
      change |∫ h, Real.log (lastState s₀.2 h).1 ∂hist Q (t + 1) s₀.2| ≤ Cz
      rw [← hint]
      exact le_max_right _ _
  -- `E ln x_t` is bounded
  set Ka := max |Real.log s₀.1.1| ((|Real.log (α * β)| + Cz) / (1 - α))
  have h1α : 0 < 1 - α := sub_pos.2 hα1
  have hlx : ∀ t, Integrable (lx t) (hist Q t s₀.2) ∧ |∫ h, lx t h ∂hist Q t s₀.2| ≤ Ka := by
    intro t
    induction t with
    | zero =>
      have := ex_8_8a Q 0
      have hc : lx 0 = fun _ => Real.log s₀.1.1 := rfl
      rw [hc, integral_const]
      refine ⟨integrable_const _, ?_⟩
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      exact le_max_left _ _
    | succ t ih =>
      have := ex_8_8a Q t
      have hI : Integrable (fun h => Real.log (α * β) + lz t h + α * lx t h) (hist Q t s₀.2) :=
        ((integrable_const _).add (hlz t).1).add ((ih.1).const_mul α)
      have heq : lx (t + 1) = fun h => (fun h' => Real.log (α * β) + lz t h' + α * lx t h')
          (Fin.init h) := funext (hrec t)
      rw [heq]
      refine ⟨integrable_init Q t s₀.2 hI, ?_⟩
      have i1 : Integrable (fun h => Real.log (α * β) + lz t h) (hist Q t s₀.2) :=
        (integrable_const _).add (hlz t).1
      have i2 : Integrable (fun h => α * lx t h) (hist Q t s₀.2) := (ih.1).const_mul α
      rw [integral_init Q t s₀.2 hI.aestronglyMeasurable, integral_add i1 i2,
        integral_add (integrable_const _) (hlz t).1, integral_const, integral_const_mul]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      have h1 := (hlz t).2
      have h2 := ih.2
      have hKa : |Real.log (α * β)| + Cz ≤ (1 - α) * Ka := by
        rw [← div_le_iff₀' h1α]; exact le_max_right _ _
      calc |Real.log (α * β) + ∫ h, lz t h ∂hist Q t s₀.2 + α * ∫ h, lx t h ∂hist Q t s₀.2|
          ≤ |Real.log (α * β)| + |∫ h, lz t h ∂hist Q t s₀.2| +
              α * |∫ h, lx t h ∂hist Q t s₀.2| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_pos hα0]
            exact add_le_add (abs_add_le _ _) le_rfl
        _ ≤ |Real.log (α * β)| + Cz + α * Ka := by gcongr
        _ ≤ Ka := by linarith
  -- integrability of `v` and the bound on its mean
  set a := α / (1 - α * β)
  set b := 1 / (1 - α * β)
  have hval : ∀ t, logV A₀ α β ∘ state M s₀ π t = fun h => A₀ + a * lx t h + b * lz t h :=
    fun t => rfl
  have hbound : ∀ t, Integrable (fun h => logV A₀ α β (state M s₀ π t h)) (hist Q t s₀.2) ∧
      |∫ h, logV A₀ α β (state M s₀ π t h) ∂hist Q t s₀.2| ≤ |A₀| + |a| * Ka + |b| * Cz := by
    intro t
    have := ex_8_8a Q t
    have hI : Integrable (fun h => A₀ + a * lx t h + b * lz t h) (hist Q t s₀.2) :=
      ((integrable_const _).add ((hlx t).1.const_mul a)).add ((hlz t).1.const_mul b)
    refine ⟨hI, ?_⟩
    change |∫ h, A₀ + a * lx t h + b * lz t h ∂hist Q t s₀.2| ≤ _
    have i1 : Integrable (fun h => A₀ + a * lx t h) (hist Q t s₀.2) :=
      (integrable_const _).add ((hlx t).1.const_mul a)
    have i2 : Integrable (fun h => b * lz t h) (hist Q t s₀.2) := (hlz t).1.const_mul b
    have i3 : Integrable (fun h => a * lx t h) (hist Q t s₀.2) := (hlx t).1.const_mul a
    rw [integral_add i1 i2, integral_add (integrable_const _) i3, integral_const,
      integral_const_mul, integral_const_mul]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    calc |A₀ + a * ∫ h, lx t h ∂hist Q t s₀.2 + b * ∫ h, lz t h ∂hist Q t s₀.2|
        ≤ |A₀| + |a| * |∫ h, lx t h ∂hist Q t s₀.2| + |b| * |∫ h, lz t h ∂hist Q t s₀.2| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
          · rw [abs_mul]
          · rw [abs_mul]
      _ ≤ |A₀| + |a| * Ka + |b| * Cz := by
          gcongr
          · exact (hlx t).2
          · exact (hlz t).2
  refine ⟨fun t => (hbound t).1, ?_⟩
  refine squeeze_zero_norm (a := fun t => (|A₀| + |a| * Ka + |b| * Cz) * β ^ t) (fun t => ?_) ?_
  · rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hβ0, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbound t).2 (pow_nonneg hβ0.le t)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul
      (|A₀| + |a| * Ka + |b| * Cz)

end StokeyLucasPrescott.StochasticDP

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

namespace StokeyLucasPrescott.StochasticDP

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

end StokeyLucasPrescott.StochasticDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 9.16: the endogenous state need not be a Markov process

SLP §9.6, p. 286. `X = [0, 1]`, `Z = {0, 1}` with `Q(0, 0) = Q(1, 1) = 0.9`, and
`g(x, z) = θx + (1 − θ)z`. The book asks to show that `x_t` is not a first-order Markov process:
`Pr(x_{t+1} ∈ A | x_t, x_{t−1}) ≠ Pr(x_{t+1} ∈ A | x_t)`.

The Markov property of `x` is stated as a factorization of the joint law (as in Chapter 8): the
law of `(x_t, x_{t+1}, x_{t+2})` is the law of `(x_t, x_{t+1})` followed by a transition function
`R(x_{t+1}, ·)` (`IsMarkovAt`). The shocks are `z₀` (given) and the history `(z₁, …, z_t)`;
`x_t = xP t` uses `z₀, …, z_{t−1}`.

**Correction.** The claim depends on `θ`:

* for `θ < 1/2` it is false (`ex_9_16_markov`): `x_{t+1} = θx_t + (1 − θ)z_t` lies in `[0, θ]`
  when `z_t = 0` and in `[1 − θ, 1]` when `z_t = 1`, so `z_t = 1{x_{t+1} ≥ 1 − θ}` and `x` is a
  Markov process, with `R(y, ·)` the law of `θy + (1 − θ)z′`, `z′ ~ Q(1{y ≥ 1 − θ}, ·)`;
* for `θ = (√5 − 1)/2` it is true (`ex_9_16`): from `x₀ = 0`, `z₀ = 0`, the shock histories
  `(1, 1, 0)` and `(0, 0, 1)` both give `x₄ = 1 − θ` (as `θ² + θ = 1`) but differ in `x₃` and in
  `z₃`, so `Pr(x₅ = θ(1 − θ) | x₃, x₄)` is `0.9` on one and `0.1` on the other, and no `R` exists.
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- `Q(z, ·)`: stay with probability `0.9`, switch with probability `0.1`. -/
noncomputable def flipMeasure (b : Bool) : Measure Bool :=
  (9 / 10 : ℝ≥0∞) • Measure.dirac b + (1 / 10 : ℝ≥0∞) • Measure.dirac (!b)

/-- The transition function of the two-state shock. -/
noncomputable def flipKernel : Kernel Bool Bool := Kernel.ofFunOfCountable flipMeasure

theorem flipKernel_apply (b : Bool) : flipKernel b = flipMeasure b := rfl

theorem isMarkovKernel_flipKernel : IsMarkovKernel flipKernel :=
  ⟨fun b => ⟨by
    rw [flipKernel_apply, flipMeasure]
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.add_div]
    norm_num [ENNReal.div_self]⟩⟩

theorem flipKernel_singleton (b c : Bool) :
    flipKernel b {c} = if c = b then 9 / 10 else 1 / 10 := by
  rw [flipKernel_apply, flipMeasure]
  cases b <;> cases c <;> simp

/-- The value of a shock, `0` or `1`. -/
def bv (z : Bool) : ℝ := if z then 1 else 0

theorem measurable_bv : Measurable bv := measurable_of_countable _

/-- `x_t` along the shock history: `x₀` given, `x_{t+1} = θx_t + (1 − θ)z_t`. -/
noncomputable def xP (θ x₀ : ℝ) (z₀ : Bool) : (t : ℕ) → (Fin t → Bool) → ℝ
  | 0, _ => x₀
  | t + 1, h => θ * xP θ x₀ z₀ t (Fin.init h) + (1 - θ) * bv (lastState z₀ (Fin.init h))

theorem measurable_xP (θ x₀ : ℝ) (z₀ : Bool) (t : ℕ) : Measurable (xP θ x₀ z₀ t) :=
  measurable_of_countable _

/-- `x_{t+1}` as a function of the history `(z₁, …, z_t)`. -/
noncomputable def xNext (θ x₀ : ℝ) (z₀ : Bool) (t : ℕ) (h : Fin t → Bool) : ℝ :=
  θ * xP θ x₀ z₀ t h + (1 - θ) * bv (lastState z₀ h)

/-- `(x_t, x_{t+1})` as a function of `(z₁, …, z_t)`. -/
noncomputable def xPair (θ x₀ : ℝ) (z₀ : Bool) (t : ℕ) (h : Fin t → Bool) : ℝ × ℝ :=
  (xP θ x₀ z₀ t h, xNext θ x₀ z₀ t h)

/-- `((x_t, x_{t+1}), x_{t+2})` as a function of `(z₁, …, z_{t+1})`. -/
noncomputable def xTriple (θ x₀ : ℝ) (z₀ : Bool) (t : ℕ) (h : Fin (t + 1) → Bool) :
    (ℝ × ℝ) × ℝ :=
  (xPair θ x₀ z₀ t (Fin.init h),
    θ * xNext θ x₀ z₀ t (Fin.init h) + (1 - θ) * bv (lastState z₀ h))

/-- **The Markov property of `x` at date `t`**: the joint law of `(x_t, x_{t+1}, x_{t+2})` is the
law of `(x_t, x_{t+1})` followed by a transition function `R(x_{t+1}, ·)`. -/
def IsMarkovAt (θ x₀ : ℝ) (z₀ : Bool) (t : ℕ) : Prop :=
  ∃ R : Kernel ℝ ℝ, IsMarkovKernel R ∧
    (hist flipKernel (t + 1) z₀).map (xTriple θ x₀ z₀ t) =
      ((hist flipKernel t z₀).map (xPair θ x₀ z₀ t)) ⊗ₘ R.comap Prod.snd measurable_snd

/-! ### `θ < 1/2`: `x` is a Markov process -/

/-- Decoding the last shock: `1{y ≥ 1 − θ}`. -/
noncomputable def decodeZ (θ y : ℝ) : Bool := if 1 - θ ≤ y then true else false

theorem measurable_decodeZ (θ : ℝ) : Measurable (decodeZ θ) :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

/-- `R(y, ·)`: the law of `θy + (1 − θ)z′` with `z′ ~ Q(1{y ≥ 1 − θ}, ·)`. -/
noncomputable def xKernel (θ : ℝ) : Kernel ℝ ℝ :=
  (Kernel.deterministic id measurable_id ×ₖ
    flipKernel.comap (decodeZ θ) (measurable_decodeZ θ)).map fun p => θ * p.1 + (1 - θ) * bv p.2

theorem measurable_xKernel_fun (θ : ℝ) :
    Measurable fun p : ℝ × Bool => θ * p.1 + (1 - θ) * bv p.2 :=
  (measurable_const.mul measurable_fst).add
    (measurable_const.mul (measurable_bv.comp measurable_snd))

theorem xKernel_apply (θ y : ℝ) :
    xKernel θ y = (flipKernel (decodeZ θ y)).map fun z' => θ * y + (1 - θ) * bv z' := by
  have := isMarkovKernel_flipKernel
  rw [xKernel, Kernel.map_apply _ (measurable_xKernel_fun θ), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.comap_apply, Measure.dirac_prod,
    Measure.map_map (measurable_xKernel_fun θ) measurable_prodMk_left]
  rfl

theorem isMarkovKernel_xKernel (θ : ℝ) : IsMarkovKernel (xKernel θ) := by
  have := isMarkovKernel_flipKernel
  unfold xKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_xKernel_fun θ)

theorem xP_mem_Icc {θ x₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx₀ : x₀ ∈ Icc (0 : ℝ) 1)
    (z₀ : Bool) (t : ℕ) (h : Fin t → Bool) : xP θ x₀ z₀ t h ∈ Icc (0 : ℝ) 1 := by
  induction t with
  | zero => exact hx₀
  | succ t ih =>
    have hb : bv (lastState z₀ (Fin.init h)) ∈ Icc (0 : ℝ) 1 := by
      unfold bv; split_ifs <;> norm_num
    obtain ⟨h1, h2⟩ := ih (Fin.init h)
    constructor <;> simp only [xP] <;> nlinarith [hb.1, hb.2]

/-- For `θ < 1/2` the last shock is recovered from `x_{t+1}`. -/
theorem decodeZ_xNext {θ x₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hx₀ : x₀ ∈ Icc (0 : ℝ) 1)
    (z₀ : Bool) (t : ℕ) (h : Fin t → Bool) :
    decodeZ θ (xNext θ x₀ z₀ t h) = lastState z₀ h := by
  obtain ⟨h1, h2⟩ := xP_mem_Icc hθ0 (by linarith) hx₀ z₀ t h
  unfold decodeZ xNext
  cases hz : lastState z₀ h
  · simp only [bv, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
    simp only [ite_eq_right_iff, Bool.true_eq_false, imp_false, not_le]
    nlinarith
  · simp only [bv, ↓reduceIte, mul_one]
    simp only [ite_eq_left_iff, not_le, Bool.false_eq_true, imp_false, not_lt]
    nlinarith

/-- **Exercise 9.16, correction (`θ < 1/2`).** For `0 ≤ θ < 1/2` and `x₀ ∈ [0, 1]`, `x` is a
Markov process: at every date the law of `(x_t, x_{t+1}, x_{t+2})` factors through
`R(x_{t+1}, ·)`. -/
theorem ex_9_16_markov {θ x₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hx₀ : x₀ ∈ Icc (0 : ℝ) 1)
    (z₀ : Bool) (t : ℕ) : IsMarkovAt θ x₀ z₀ t := by
  have hQ := isMarkovKernel_flipKernel
  have hR := isMarkovKernel_xKernel θ
  refine ⟨xKernel θ, hR, ?_⟩
  have := ex_8_8a flipKernel t
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_of_countable _),
    hist_succ_lintegral_last flipKernel t z₀ (f := fun h => f (xTriple θ x₀ z₀ t h))
      (hf.comp (measurable_of_countable _)),
    Measure.lintegral_compProd hf,
    lintegral_map (hf.lintegral_kernel_prod_right' (κ := (xKernel θ).comap Prod.snd
      measurable_snd)) (measurable_of_countable _)]
  refine lintegral_congr fun h => ?_
  have hm : Measurable fun z' : Bool => θ * xNext θ x₀ z₀ t h + (1 - θ) * bv z' :=
    measurable_of_countable _
  simp only [xTriple, Fin.init_snoc, lastState_snoc, Kernel.comap_apply, xKernel_apply]
  have hp2 : (xPair θ x₀ z₀ t h).2 = xNext θ x₀ z₀ t h := rfl
  rw [hp2, lintegral_map (f := fun y => f (xPair θ x₀ z₀ t h, y)) (hf.comp measurable_prodMk_left)
    hm, decodeZ_xNext hθ0 hθ hx₀ z₀ t h]

/-! ### `θ = (√5 − 1)/2`: `x` is not a Markov process -/

/-- The golden-section `θ`, with `θ² + θ = 1`. -/
noncomputable def θg : ℝ := (Real.sqrt 5 - 1) / 2

theorem θg_sq : θg ^ 2 = 1 - θg := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold θg
  nlinarith

theorem θg_bounds : 3 / 5 < θg ∧ θg < 13 / 20 := by
  have h1 : (11 / 5 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 5 < 23 / 10 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold θg
  constructor <;> linarith

theorem xP3_eq (h : Fin 3 → Bool) :
    xP θg 0 false 3 h = θg * (1 - θg) * bv (h 0) + (1 - θg) * bv (h 1) := by
  simp only [xP, lastState, Fin.init]
  have e0 : ((Fin.last 0).castSucc.castSucc : Fin 3) = 0 := rfl
  have e1 : ((Fin.last 1).castSucc : Fin 3) = 1 := rfl
  rw [e0, e1]
  simp only [bv, Bool.false_eq_true, ↓reduceIte]
  ring

theorem xNext3_eq (h : Fin 3 → Bool) :
    xNext θg 0 false 3 h = θg * xP θg 0 false 3 h + (1 - θg) * bv (h 2) := rfl

theorem bv_false : bv false = 0 := rfl

theorem bv_true : bv true = 1 := rfl

/-- On `(x₃, x₄) = (θ, 1 − θ)`, the history is `(1, 1, 0)`: in particular `z₃ = 0`. -/
theorem decode_A {h : Fin 3 → Bool} (hA : xPair θg 0 false 3 h = (θg, 1 - θg)) :
    h 2 = false := by
  obtain ⟨hb1, hb2⟩ := θg_bounds
  have hsq := θg_sq
  have e1 : xP θg 0 false 3 h = θg := congrArg Prod.fst hA
  have e2 : xNext θg 0 false 3 h = 1 - θg := congrArg Prod.snd hA
  rw [xNext3_eq, e1] at e2
  rw [xP3_eq] at e1
  cases h0 : h 0 <;> cases h1 : h 1 <;> cases h2 : h 2 <;>
    simp only [h0, h1, h2, bv_false, bv_true] at e1 e2 <;> first | rfl | nlinarith

/-- On `(x₃, x₄) = (0, 1 − θ)`, the history is `(0, 0, 1)`: in particular `z₃ = 1`. -/
theorem decode_B {h : Fin 3 → Bool} (hB : xPair θg 0 false 3 h = (0, 1 - θg)) :
    h 2 = true := by
  obtain ⟨hb1, hb2⟩ := θg_bounds
  have e1 : xP θg 0 false 3 h = 0 := congrArg Prod.fst hB
  have e2 : xNext θg 0 false 3 h = 1 - θg := congrArg Prod.snd hB
  rw [xNext3_eq, e1] at e2
  rw [xP3_eq] at e1
  cases h0 : h 0 <;> cases h1 : h 1 <;> cases h2 : h 2 <;>
    simp only [h0, h1, h2, bv_false, bv_true] at e1 e2 <;> first | rfl | nlinarith

theorem mem_A : xPair θg 0 false 3 ![true, true, false] = (θg, 1 - θg) := by
  have hsq := θg_sq
  have e1 : xP θg 0 false 3 ![true, true, false] = θg := by
    rw [xP3_eq]
    change θg * (1 - θg) * bv true + (1 - θg) * bv true = θg
    rw [bv_true]
    nlinarith
  refine Prod.ext e1 ?_
  change xNext θg 0 false 3 ![true, true, false] = 1 - θg
  rw [xNext3_eq, e1]
  change θg * θg + (1 - θg) * bv false = 1 - θg
  rw [bv_false]
  nlinarith

theorem mem_B : xPair θg 0 false 3 ![false, false, true] = (0, 1 - θg) := by
  have e1 : xP θg 0 false 3 ![false, false, true] = 0 := by
    rw [xP3_eq]
    change θg * (1 - θg) * bv false + (1 - θg) * bv false = 0
    rw [bv_false]
    ring
  refine Prod.ext e1 ?_
  change xNext θg 0 false 3 ![false, false, true] = 1 - θg
  rw [xNext3_eq, e1]
  change θg * 0 + (1 - θg) * bv true = 1 - θg
  rw [bv_true]
  ring

/-- The law of `(x₃, x₄, x₅)` on `{(x₃, x₄) = p} × {x₅ ∈ S}`. -/
theorem triple_rect (p : ℝ × ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    (hist flipKernel 4 false).map (xTriple θg 0 false 3) ({p} ×ˢ S) =
      ∫⁻ h, (xPair θg 0 false 3 ⁻¹' {p}).indicator (fun h => flipKernel (lastState false h)
        {z' | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈ S}) h ∂hist flipKernel 3 false := by
  have hQ := isMarkovKernel_flipKernel
  have hm : MeasurableSet ({p} ×ˢ S) := (measurableSet_singleton p).prod hS
  rw [Measure.map_apply (measurable_of_countable _) hm, ← lintegral_indicator_one
    ((measurable_of_countable _) hm), hist_succ_lintegral_last flipKernel 3 false
    (measurable_of_countable _)]
  refine lintegral_congr fun h => ?_
  by_cases hp : h ∈ xPair θg 0 false 3 ⁻¹' {p}
  · rw [indicator_of_mem hp, ← lintegral_indicator_one (Set.toFinite _).measurableSet]
    refine lintegral_congr fun z' => ?_
    rw [mem_preimage, mem_singleton_iff] at hp
    have hiff : Fin.snoc h z' ∈ xTriple θg 0 false 3 ⁻¹' ({p} ×ˢ S) ↔
        z' ∈ {z' : Bool | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈ S} := by
      simp only [mem_preimage, mem_prod, mem_singleton_iff, xTriple, Fin.init_snoc,
        lastState_snoc, hp, true_and]
      rfl
    by_cases hz : z' ∈ {z' : Bool | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈ S}
    · rw [indicator_of_mem (hiff.2 hz), indicator_of_mem hz]
      rfl
    · rw [indicator_of_notMem (fun h' => hz (hiff.1 h')), indicator_of_notMem hz]
  · rw [indicator_of_notMem hp]
    refine (lintegral_congr fun z' => ?_).trans lintegral_zero
    rw [indicator_of_notMem]
    simp only [mem_preimage, mem_prod, mem_singleton_iff, xTriple, Fin.init_snoc, not_and]
    rw [mem_preimage, mem_singleton_iff] at hp
    exact fun h' => absurd h' hp

/-- **Exercise 9.16** (for `θ = (√5 − 1)/2`). From `x₀ = 0`, `z₀ = 0`, the process `x` is not
Markov at date 3: no transition function `R` makes the law of `(x₃, x₄, x₅)` the law of
`(x₃, x₄)` followed by `R(x₄, ·)`. -/
theorem ex_9_16 : ¬IsMarkovAt θg 0 false 3 := by
  rintro ⟨R, hR, heq⟩
  have hQ := isMarkovKernel_flipKernel
  have h3 := ex_8_8a flipKernel 3
  obtain ⟨hb1, hb2⟩ := θg_bounds
  set v := θg * (1 - θg)
  -- both sides on `{p} × {v}`
  have hside : ∀ (p : ℝ × ℝ) (c : ℝ≥0∞), (∀ h : Fin 3 → Bool, xPair θg 0 false 3 h = p →
      flipKernel (lastState false h) {z' | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈
        ({v} : Set ℝ)} = c) →
      c * hist flipKernel 3 false (xPair θg 0 false 3 ⁻¹' {p}) =
        R p.2 {v} * hist flipKernel 3 false (xPair θg 0 false 3 ⁻¹' {p}) := by
    intro p c hc
    have e := congrArg (fun μ : Measure ((ℝ × ℝ) × ℝ) => μ ({p} ×ˢ {v})) heq
    rw [triple_rect p (measurableSet_singleton v), Measure.compProd_apply_prod
      (measurableSet_singleton p) (measurableSet_singleton v), lintegral_singleton,
      Measure.map_apply (measurable_of_countable _) (measurableSet_singleton p),
      Kernel.comap_apply] at e
    rw [← e, ← lintegral_indicator_const ((measurable_of_countable _)
      (measurableSet_singleton p))]
    refine lintegral_congr fun h => ?_
    by_cases hp : h ∈ xPair θg 0 false 3 ⁻¹' {p}
    · rw [indicator_of_mem hp, indicator_of_mem hp, hc h hp]
    · rw [indicator_of_notMem hp, indicator_of_notMem hp]
  -- the conditional probabilities on the two histories
  have hA := hside (θg, 1 - θg) (9 / 10) fun h hh => by
    have h2 := decode_A hh
    have hx : xNext θg 0 false 3 h = 1 - θg := congrArg Prod.snd hh
    have hset : {z' : Bool | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈ ({v} : Set ℝ)} =
        {false} := by
      ext z'
      cases z'
      · simp [hx, v, bv]
      · simp [hx, v, bv]
        nlinarith
    rw [hset, show lastState false h = h 2 from rfl, h2, flipKernel_singleton]
    simp
  have hB := hside (0, 1 - θg) (1 / 10) fun h hh => by
    have h2 := decode_B hh
    have hx : xNext θg 0 false 3 h = 1 - θg := congrArg Prod.snd hh
    have hset : {z' : Bool | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈ ({v} : Set ℝ)} =
        {false} := by
      ext z'
      cases z'
      · simp [hx, v, bv]
      · simp [hx, v, bv]
        nlinarith
    rw [hset, show lastState false h = h 2 from rfl, h2, flipKernel_singleton]
    simp
  -- the histories `(1, 1, 0)` and `(0, 0, 1)` have positive probability
  have hpos : ∀ z z' : Bool, flipKernel z {z'} ≠ 0 := fun z z' => by
    rw [flipKernel_singleton]; split_ifs <;> norm_num
  have hHA : hist flipKernel 3 false (xPair θg 0 false 3 ⁻¹' {(θg, 1 - θg)}) ≠ 0 := fun h0 =>
    hist_singleton_ne_zero flipKernel hpos 3 false ![true, true, false]
      (measure_mono_null (singleton_subset_iff.2 mem_A) h0)
  have hHB : hist flipKernel 3 false (xPair θg 0 false 3 ⁻¹' {(0, 1 - θg)}) ≠ 0 := fun h0 =>
    hist_singleton_ne_zero flipKernel hpos 3 false ![false, false, true]
      (measure_mono_null (singleton_subset_iff.2 mem_B) h0)
  have r1 := (ENNReal.mul_left_inj hHA (measure_ne_top _ _)).1 hA
  have r2 := (ENNReal.mul_left_inj hHB (measure_ne_top _ _)).1 hB
  have := r1.trans r2.symm
  have := congrArg ENNReal.toReal this
  norm_num at this

end StokeyLucasPrescott.StochasticDP

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.StochasticDP.IsLHC
#print axioms StokeyLucasPrescott.StochasticDP.IsUHC
#print axioms StokeyLucasPrescott.StochasticDP.graph
#print axioms StokeyLucasPrescott.StochasticDP.continuousAt_of_isUHC_singleton
#print axioms StokeyLucasPrescott.StochasticDP.isCompact_graph
#print axioms StokeyLucasPrescott.StochasticDP.IsContraction
#print axioms StokeyLucasPrescott.StochasticDP.IsContraction.uniformContinuous
#print axioms StokeyLucasPrescott.StochasticDP.dist_iterate_succ_le
#print axioms StokeyLucasPrescott.StochasticDP.dist_iterate_le
#print axioms StokeyLucasPrescott.StochasticDP.cauchySeq_iterate
#print axioms StokeyLucasPrescott.StochasticDP.theorem_3_2
#print axioms StokeyLucasPrescott.StochasticDP.dist_fixedPoint_le
#print axioms StokeyLucasPrescott.StochasticDP.corollary_1
#print axioms StokeyLucasPrescott.StochasticDP.corollary_2
#print axioms StokeyLucasPrescott.StochasticDP.maxValue
#print axioms StokeyLucasPrescott.StochasticDP.argmax
#print axioms StokeyLucasPrescott.StochasticDP.continuousOn_section
#print axioms StokeyLucasPrescott.StochasticDP.exists_argmax
#print axioms StokeyLucasPrescott.StochasticDP.le_maxValue
#print axioms StokeyLucasPrescott.StochasticDP.tendsto_f_graph
#print axioms StokeyLucasPrescott.StochasticDP.theorem_3_6
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.mk
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.nonempty
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.compact
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.lhc
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.uhc
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.cont
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.unique
#print axioms StokeyLucasPrescott.StochasticDP.argmaxFn
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.argmaxFn_mem
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.argmax_eq
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.lt_of_ne
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.continuous_argmaxFn
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.lemma_3_7
#print axioms StokeyLucasPrescott.StochasticDP.UniqueArgmax.lemma_3_7_uniform
#print axioms StokeyLucasPrescott.StochasticDP.shortfall_lt
#print axioms StokeyLucasPrescott.StochasticDP.theorem_3_8
#print axioms StokeyLucasPrescott.StochasticDP.theorem_3_8_uniform
#print axioms StokeyLucasPrescott.StochasticDP.theorem_4_10
#print axioms StokeyLucasPrescott.StochasticDP.ex_4_5
#print axioms StokeyLucasPrescott.StochasticDP.IsMeasurableSelection
#print axioms StokeyLucasPrescott.StochasticDP.IsMeasCorr
#print axioms StokeyLucasPrescott.StochasticDP.minCoord
#print axioms StokeyLucasPrescott.StochasticDP.minCoord_mem
#print axioms StokeyLucasPrescott.StochasticDP.minCoord_le
#print axioms StokeyLucasPrescott.StochasticDP.measurable_minCoord
#print axioms StokeyLucasPrescott.StochasticDP.refineCorr
#print axioms StokeyLucasPrescott.StochasticDP.IsMeasCorr.refine
#print axioms StokeyLucasPrescott.StochasticDP.lexCorr
#print axioms StokeyLucasPrescott.StochasticDP.lexCorr_spec
#print axioms StokeyLucasPrescott.StochasticDP.isMeasCorr_of_uhc
#print axioms StokeyLucasPrescott.StochasticDP.theorem_7_6
#print axioms StokeyLucasPrescott.StochasticDP.theorem_7_6_subtype
#print axioms StokeyLucasPrescott.StochasticDP.IsTransitionFunction
#print axioms StokeyLucasPrescott.StochasticDP.isTransitionFunction_iff
#print axioms StokeyLucasPrescott.StochasticDP.markovOp
#print axioms StokeyLucasPrescott.StochasticDP.markovOpR
#print axioms StokeyLucasPrescott.StochasticDP.adjointOp
#print axioms StokeyLucasPrescott.StochasticDP.markovOp_indicator
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_1
#print axioms StokeyLucasPrescott.StochasticDP.integrable_of_bounded
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_1_cor
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_1
#print axioms StokeyLucasPrescott.StochasticDP.adjointOp_apply
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_2
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_2
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_3
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_3_cor
#print axioms StokeyLucasPrescott.StochasticDP.pairing
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_3
#print axioms StokeyLucasPrescott.StochasticDP.kpow
#print axioms StokeyLucasPrescott.StochasticDP.kpow_one
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_4a
#print axioms StokeyLucasPrescott.StochasticDP.kpow_add
#print axioms StokeyLucasPrescott.StochasticDP.markovOp_comp
#print axioms StokeyLucasPrescott.StochasticDP.adjointOp_comp
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_4b
#print axioms StokeyLucasPrescott.StochasticDP.adjointOp_iterate
#print axioms StokeyLucasPrescott.StochasticDP.IsFeller
#print axioms StokeyLucasPrescott.StochasticDP.IsMonotoneTF
#print axioms StokeyLucasPrescott.StochasticDP.IsStochasticKernel
#print axioms StokeyLucasPrescott.StochasticDP.isStochasticKernel_iff
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_4
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_4_cor
#print axioms StokeyLucasPrescott.StochasticDP.directProd
#print axioms StokeyLucasPrescott.StochasticDP.isMarkovKernel_directProd
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_5
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_5_unique
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_6
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_7
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_6_cor
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_9a
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_9b
#print axioms StokeyLucasPrescott.StochasticDP.measurable_cons
#print axioms StokeyLucasPrescott.StochasticDP.measurable_snoc
#print axioms StokeyLucasPrescott.StochasticDP.lastState
#print axioms StokeyLucasPrescott.StochasticDP.measurable_lastState
#print axioms StokeyLucasPrescott.StochasticDP.lastState_cons
#print axioms StokeyLucasPrescott.StochasticDP.lastState_snoc
#print axioms StokeyLucasPrescott.StochasticDP.hist
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_8a
#print axioms StokeyLucasPrescott.StochasticDP.hist_zero_lintegral
#print axioms StokeyLucasPrescott.StochasticDP.hist_succ_lintegral
#print axioms StokeyLucasPrescott.StochasticDP.iterLInt
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_8
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_5
#print axioms StokeyLucasPrescott.StochasticDP.nextKernel
#print axioms StokeyLucasPrescott.StochasticDP.isMarkovKernel_nextKernel
#print axioms StokeyLucasPrescott.StochasticDP.nextKernel_apply
#print axioms StokeyLucasPrescott.StochasticDP.hist_succ_lintegral_last
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_8b
#print axioms StokeyLucasPrescott.StochasticDP.hist_succ_eq_cons
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_8c_last
#print axioms StokeyLucasPrescott.StochasticDP.ex_8_8c_first
#print axioms StokeyLucasPrescott.StochasticDP.iterInt
#print axioms StokeyLucasPrescott.StochasticDP.theorem_8_8_integrable
#print axioms StokeyLucasPrescott.StochasticDP.Model
#print axioms StokeyLucasPrescott.StochasticDP.Model.mk
#print axioms StokeyLucasPrescott.StochasticDP.Model.Q
#print axioms StokeyLucasPrescott.StochasticDP.Model.Γ
#print axioms StokeyLucasPrescott.StochasticDP.Model.φ
#print axioms StokeyLucasPrescott.StochasticDP.Model.F
#print axioms StokeyLucasPrescott.StochasticDP.Model.β
#print axioms StokeyLucasPrescott.StochasticDP.Model.first
#print axioms StokeyLucasPrescott.StochasticDP.Plan
#print axioms StokeyLucasPrescott.StochasticDP.xState
#print axioms StokeyLucasPrescott.StochasticDP.state
#print axioms StokeyLucasPrescott.StochasticDP.state_zero
#print axioms StokeyLucasPrescott.StochasticDP.IsFeasible
#print axioms StokeyLucasPrescott.StochasticDP.ret
#print axioms StokeyLucasPrescott.StochasticDP.uN
#print axioms StokeyLucasPrescott.StochasticDP.planValue
#print axioms StokeyLucasPrescott.StochasticDP.vStar
#print axioms StokeyLucasPrescott.StochasticDP.planValue_eq
#print axioms StokeyLucasPrescott.StochasticDP.measurable_init
#print axioms StokeyLucasPrescott.StochasticDP.measurable_xState
#print axioms StokeyLucasPrescott.StochasticDP.measurable_state
#print axioms StokeyLucasPrescott.StochasticDP.measurable_ret
#print axioms StokeyLucasPrescott.StochasticDP.state_snoc
#print axioms StokeyLucasPrescott.StochasticDP.cont
#print axioms StokeyLucasPrescott.StochasticDP.start₁
#print axioms StokeyLucasPrescott.StochasticDP.init_cons
#print axioms StokeyLucasPrescott.StochasticDP.xState_cons
#print axioms StokeyLucasPrescott.StochasticDP.state_cons
#print axioms StokeyLucasPrescott.StochasticDP.ret_cons
#print axioms StokeyLucasPrescott.StochasticDP.IsFeasible.cont
#print axioms StokeyLucasPrescott.StochasticDP.genX
#print axioms StokeyLucasPrescott.StochasticDP.genPlan
#print axioms StokeyLucasPrescott.StochasticDP.xState_genPlan
#print axioms StokeyLucasPrescott.StochasticDP.state_genPlan
#print axioms StokeyLucasPrescott.StochasticDP.genPlan_apply
#print axioms StokeyLucasPrescott.StochasticDP.genPlan_feasible
#print axioms StokeyLucasPrescott.StochasticDP.lemma_9_1
#print axioms StokeyLucasPrescott.StochasticDP.expV
#print axioms StokeyLucasPrescott.StochasticDP.rhs
#print axioms StokeyLucasPrescott.StochasticDP.SolvesFE
#print axioms StokeyLucasPrescott.StochasticDP.policy
#print axioms StokeyLucasPrescott.StochasticDP.integrable_next
#print axioms StokeyLucasPrescott.StochasticDP.integrable_first
#print axioms StokeyLucasPrescott.StochasticDP.integral_hist_zero
#print axioms StokeyLucasPrescott.StochasticDP.integral_v_succ
#print axioms StokeyLucasPrescott.StochasticDP.integrable_expV
#print axioms StokeyLucasPrescott.StochasticDP.integral_v_step
#print axioms StokeyLucasPrescott.StochasticDP.v_ge_uN
#print axioms StokeyLucasPrescott.StochasticDP.v_eq_uN
#print axioms StokeyLucasPrescott.StochasticDP.SolvesFE.le
#print axioms StokeyLucasPrescott.StochasticDP.planValue_le_of_limit
#print axioms StokeyLucasPrescott.StochasticDP.planValue_genPlan_of_limit
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_4
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_2
#print axioms StokeyLucasPrescott.StochasticDP.integral_ret_succ
#print axioms StokeyLucasPrescott.StochasticDP.integrable_ret_cont
#print axioms StokeyLucasPrescott.StochasticDP.uN_succ
#print axioms StokeyLucasPrescott.StochasticDP.measurable_ret_cont
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_1
#print axioms StokeyLucasPrescott.StochasticDP.uR
#print axioms StokeyLucasPrescott.StochasticDP.bound_nonneg
#print axioms StokeyLucasPrescott.StochasticDP.integrable_ret_of_bound
#print axioms StokeyLucasPrescott.StochasticDP.abs_term_le
#print axioms StokeyLucasPrescott.StochasticDP.summable_terms
#print axioms StokeyLucasPrescott.StochasticDP.tendsto_uN
#print axioms StokeyLucasPrescott.StochasticDP.planValue_eq_uR
#print axioms StokeyLucasPrescott.StochasticDP.abs_uN_le
#print axioms StokeyLucasPrescott.StochasticDP.abs_uR_le
#print axioms StokeyLucasPrescott.StochasticDP.bounds_cont
#print axioms StokeyLucasPrescott.StochasticDP.measurable_uR_cont
#print axioms StokeyLucasPrescott.StochasticDP.lemma_9_3
#print axioms StokeyLucasPrescott.StochasticDP.planValuePos
#print axioms StokeyLucasPrescott.StochasticDP.lemma_9_3_nonneg
#print axioms StokeyLucasPrescott.StochasticDP.measurable_expV
#print axioms StokeyLucasPrescott.StochasticDP.measurableSet_policy
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_4_step
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_4_ae
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_4
#print axioms StokeyLucasPrescott.StochasticDP.hist_singleton_ne_zero
#print axioms StokeyLucasPrescott.StochasticDP.coin
#print axioms StokeyLucasPrescott.StochasticDP.isProbabilityMeasure_coin
#print axioms StokeyLucasPrescott.StochasticDP.coin_singleton_ne_zero
#print axioms StokeyLucasPrescott.StochasticDP.coinModel
#print axioms StokeyLucasPrescott.StochasticDP.coinPlan
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_4_counterexample
#print axioms StokeyLucasPrescott.StochasticDP.exists_tendsto_ereal_of_monotone
#print axioms StokeyLucasPrescott.StochasticDP.exists_tendsto_ereal_of_antitone
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_2a
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_2b_theorem_9_2
#print axioms StokeyLucasPrescott.StochasticDP.Model.negF
#print axioms StokeyLucasPrescott.StochasticDP.xState_negF
#print axioms StokeyLucasPrescott.StochasticDP.ret_negF
#print axioms StokeyLucasPrescott.StochasticDP.planValuePos_ne_top
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_2b_lemma_9_3
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_2b_theorem_9_4
#print axioms StokeyLucasPrescott.StochasticDP.blackwellModel
#print axioms StokeyLucasPrescott.StochasticDP.hist_id
#print axioms StokeyLucasPrescott.StochasticDP.lastState_const
#print axioms StokeyLucasPrescott.StochasticDP.uN_blackwell
#print axioms StokeyLucasPrescott.StochasticDP.blackwell_example
#print axioms StokeyLucasPrescott.StochasticDP.mop
#print axioms StokeyLucasPrescott.StochasticDP.PreservesBC
#print axioms StokeyLucasPrescott.StochasticDP.integrable_of_abs_le
#print axioms StokeyLucasPrescott.StochasticDP.integral_lt_integral_of_lt
#print axioms StokeyLucasPrescott.StochasticDP.abs_mop_le
#print axioms StokeyLucasPrescott.StochasticDP.integrable_section
#print axioms StokeyLucasPrescott.StochasticDP.lemma_9_5_discrete
#print axioms StokeyLucasPrescott.StochasticDP.lemma_9_5_compact
#print axioms StokeyLucasPrescott.StochasticDP.lemma_9_5_comb
#print axioms StokeyLucasPrescott.StochasticDP.lemma_9_5_comb_strict
#print axioms StokeyLucasPrescott.StochasticDP.lemma_9_5_mono
#print axioms StokeyLucasPrescott.StochasticDP.lemma_9_5_strictMono
#print axioms StokeyLucasPrescott.StochasticDP.lemma_9_5'
#print axioms StokeyLucasPrescott.StochasticDP.domD
#print axioms StokeyLucasPrescott.StochasticDP.graphA
#print axioms StokeyLucasPrescott.StochasticDP.ContExp
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP.mk
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP.nonempty
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP.compact
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP.lhc
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP.uhc
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP.contF
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP.bddF
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP.β_pos
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP.β_lt
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP.contφ
#print axioms StokeyLucasPrescott.StochasticDP.BoundedDP.contExp
#print axioms StokeyLucasPrescott.StochasticDP.mem_domD
#print axioms StokeyLucasPrescott.StochasticDP.contExp_of_preservesBC
#print axioms StokeyLucasPrescott.StochasticDP.contExp_first
#print axioms StokeyLucasPrescott.StochasticDP.objG
#print axioms StokeyLucasPrescott.StochasticDP.continuousOn_objG
#print axioms StokeyLucasPrescott.StochasticDP.continuous_integrand
#print axioms StokeyLucasPrescott.StochasticDP.integrable_integrand
#print axioms StokeyLucasPrescott.StochasticDP.abs_expV_le
#print axioms StokeyLucasPrescott.StochasticDP.bound_maxValueG
#print axioms StokeyLucasPrescott.StochasticDP.bellman
#print axioms StokeyLucasPrescott.StochasticDP.bellman_apply
#print axioms StokeyLucasPrescott.StochasticDP.exists_bellman_argmax
#print axioms StokeyLucasPrescott.StochasticDP.bellman_mono
#print axioms StokeyLucasPrescott.StochasticDP.expV_add_const
#print axioms StokeyLucasPrescott.StochasticDP.bellman_add_const
#print axioms StokeyLucasPrescott.StochasticDP.blackwell
#print axioms StokeyLucasPrescott.StochasticDP.bellman_contraction
#print axioms StokeyLucasPrescott.StochasticDP.policy_eq_argmax
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_7b
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_6
#print axioms StokeyLucasPrescott.StochasticDP.isClosed_graph_of_uhc
#print axioms StokeyLucasPrescott.StochasticDP.isUHC_image_val
#print axioms StokeyLucasPrescott.StochasticDP.exists_measurableSelection
#print axioms StokeyLucasPrescott.StochasticDP.isClosed_graphA
#print axioms StokeyLucasPrescott.StochasticDP.ret_mem_graphA
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_7a
#print axioms StokeyLucasPrescott.StochasticDP.solvesFE_of_fixed
#print axioms StokeyLucasPrescott.StochasticDP.bounded_vStar
#print axioms StokeyLucasPrescott.StochasticDP.bounded_theorem_9_4
#print axioms StokeyLucasPrescott.StochasticDP.isClosed_pointwise_le
#print axioms StokeyLucasPrescott.StochasticDP.bellman_strictMono_x
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_7c
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_7
#print axioms StokeyLucasPrescott.StochasticDP.expV_mono_z
#print axioms StokeyLucasPrescott.StochasticDP.bellman_strictMono_z
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_11
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_7g
#print axioms StokeyLucasPrescott.StochasticDP.dual_apply_eq_sum
#print axioms StokeyLucasPrescott.StochasticDP.vertex
#print axioms StokeyLucasPrescott.StochasticDP.no_separation
#print axioms StokeyLucasPrescott.StochasticDP.eventually_mem_of_mem_interior
#print axioms StokeyLucasPrescott.StochasticDP.cmb
#print axioms StokeyLucasPrescott.StochasticDP.cmb_self
#print axioms StokeyLucasPrescott.StochasticDP.IsConcaveS
#print axioms StokeyLucasPrescott.StochasticDP.IsStrictConcaveS
#print axioms StokeyLucasPrescott.StochasticDP.IsStrictConcaveS.isConcaveS
#print axioms StokeyLucasPrescott.StochasticDP.Assumption910
#print axioms StokeyLucasPrescott.StochasticDP.Assumption911
#print axioms StokeyLucasPrescott.StochasticDP.IsAffineφ
#print axioms StokeyLucasPrescott.StochasticDP.isClosed_concaveX
#print axioms StokeyLucasPrescott.StochasticDP.expV_comb
#print axioms StokeyLucasPrescott.StochasticDP.expV_comb_strict
#print axioms StokeyLucasPrescott.StochasticDP.bellman_maps_concave
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_7d
#print axioms StokeyLucasPrescott.StochasticDP.argmax_unique_of_strictConcave
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_7d_policy
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_8
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_7d_concave
#print axioms StokeyLucasPrescott.StochasticDP.abs_expV_sub_le
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_7e
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_9
#print axioms StokeyLucasPrescott.StochasticDP.convex_image_Γ
#print axioms StokeyLucasPrescott.StochasticDP.eventually_mem_Γ
#print axioms StokeyLucasPrescott.StochasticDP.liftS
#print axioms StokeyLucasPrescott.StochasticDP.liftS_of_mem
#print axioms StokeyLucasPrescott.StochasticDP.concaveOn_liftS
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_7f
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_10
#print axioms StokeyLucasPrescott.StochasticDP.IsCone
#print axioms StokeyLucasPrescott.StochasticDP.csmul
#print axioms StokeyLucasPrescott.StochasticDP.InHS
#print axioms StokeyLucasPrescott.StochasticDP.hnormS
#print axioms StokeyLucasPrescott.StochasticDP.hnormS_nonneg
#print axioms StokeyLucasPrescott.StochasticDP.bddAbove_sphereS
#print axioms StokeyLucasPrescott.StochasticDP.abs_le_hnormS
#print axioms StokeyLucasPrescott.StochasticDP.abs_le_hnormS'
#print axioms StokeyLucasPrescott.StochasticDP.hnormS_le
#print axioms StokeyLucasPrescott.StochasticDP.inHS_sub
#print axioms StokeyLucasPrescott.StochasticDP.inHS_add
#print axioms StokeyLucasPrescott.StochasticDP.inHS_smul
#print axioms StokeyLucasPrescott.StochasticDP.inHS_zero
#print axioms StokeyLucasPrescott.StochasticDP.inHS_norm
#print axioms StokeyLucasPrescott.StochasticDP.hnormS_norm
#print axioms StokeyLucasPrescott.StochasticDP.hnormS_symm
#print axioms StokeyLucasPrescott.StochasticDP.hnormS_sub_le
#print axioms StokeyLucasPrescott.StochasticDP.hnormS_complete
#print axioms StokeyLucasPrescott.StochasticDP.contraction_HS
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_9
#print axioms StokeyLucasPrescott.StochasticDP.Assume919
#print axioms StokeyLucasPrescott.StochasticDP.Assume919.mk
#print axioms StokeyLucasPrescott.StochasticDP.Assume919.convex
#print axioms StokeyLucasPrescott.StochasticDP.Assume919.nonempty
#print axioms StokeyLucasPrescott.StochasticDP.Assume919.compact
#print axioms StokeyLucasPrescott.StochasticDP.Assume919.lhc
#print axioms StokeyLucasPrescott.StochasticDP.Assume919.uhc
#print axioms StokeyLucasPrescott.StochasticDP.Assume919.cone
#print axioms StokeyLucasPrescott.StochasticDP.Assume919.α_pos
#print axioms StokeyLucasPrescott.StochasticDP.Assume919.αβ_lt
#print axioms StokeyLucasPrescott.StochasticDP.Assume919.growth
#print axioms StokeyLucasPrescott.StochasticDP.Assume920
#print axioms StokeyLucasPrescott.StochasticDP.Assume920.mk
#print axioms StokeyLucasPrescott.StochasticDP.Assume920.β_pos
#print axioms StokeyLucasPrescott.StochasticDP.Assume920.β_lt
#print axioms StokeyLucasPrescott.StochasticDP.Assume920.cont
#print axioms StokeyLucasPrescott.StochasticDP.Assume920.hom
#print axioms StokeyLucasPrescott.StochasticDP.Assume920.B_pos
#print axioms StokeyLucasPrescott.StochasticDP.Assume920.bdd
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_8_growth
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_8
#print axioms StokeyLucasPrescott.StochasticDP.crsT
#print axioms StokeyLucasPrescott.StochasticDP.objG_first
#print axioms StokeyLucasPrescott.StochasticDP.continuousOn_objG_crs
#print axioms StokeyLucasPrescott.StochasticDP.exists_crsT_argmax
#print axioms StokeyLucasPrescott.StochasticDP.abs_mop_le_hnormS
#print axioms StokeyLucasPrescott.StochasticDP.integrable_section_HS
#print axioms StokeyLucasPrescott.StochasticDP.crsT_mapsTo
#print axioms StokeyLucasPrescott.StochasticDP.crsT_mono
#print axioms StokeyLucasPrescott.StochasticDP.crsT_disc
#print axioms StokeyLucasPrescott.StochasticDP.crsT_contraction
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_10a
#print axioms StokeyLucasPrescott.StochasticDP.crs_vStar
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_9_concave
#print axioms StokeyLucasPrescott.StochasticDP.IsQuasiConcaveS
#print axioms StokeyLucasPrescott.StochasticDP.qcPhi
#print axioms StokeyLucasPrescott.StochasticDP.qcSign
#print axioms StokeyLucasPrescott.StochasticDP.qcF
#print axioms StokeyLucasPrescott.StochasticDP.twoPoint
#print axioms StokeyLucasPrescott.StochasticDP.isProbabilityMeasure_twoPoint
#print axioms StokeyLucasPrescott.StochasticDP.isCone_univ
#print axioms StokeyLucasPrescott.StochasticDP.integral_twoPoint
#print axioms StokeyLucasPrescott.StochasticDP.qcPhi_mono
#print axioms StokeyLucasPrescott.StochasticDP.abs_qcPhi_le
#print axioms StokeyLucasPrescott.StochasticDP.abs_qcSign_le
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_9_quasiconcave_false
#print axioms StokeyLucasPrescott.StochasticDP.NonProp
#print axioms StokeyLucasPrescott.StochasticDP.ConcaveCRS
#print axioms StokeyLucasPrescott.StochasticDP.cmb_one
#print axioms StokeyLucasPrescott.StochasticDP.cmb_zero
#print axioms StokeyLucasPrescott.StochasticDP.crsT_concave
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_10b
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_10c_mono
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_10c_diff
#print axioms StokeyLucasPrescott.StochasticDP.IsHatFeasible
#print axioms StokeyLucasPrescott.StochasticDP.vHat
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_12
#print axioms StokeyLucasPrescott.StochasticDP.map_init_hist
#print axioms StokeyLucasPrescott.StochasticDP.lintegral_init
#print axioms StokeyLucasPrescott.StochasticDP.integral_init
#print axioms StokeyLucasPrescott.StochasticDP.integrable_init
#print axioms StokeyLucasPrescott.StochasticDP.map_last_hist_const
#print axioms StokeyLucasPrescott.StochasticDP.arKernel
#print axioms StokeyLucasPrescott.StochasticDP.measurable_ar
#print axioms StokeyLucasPrescott.StochasticDP.arKernel_apply
#print axioms StokeyLucasPrescott.StochasticDP.isMarkovKernel_arKernel
#print axioms StokeyLucasPrescott.StochasticDP.sq_ar_le
#print axioms StokeyLucasPrescott.StochasticDP.ar_lintegral_sq_le
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_12
#print axioms StokeyLucasPrescott.StochasticDP.quadModel
#print axioms StokeyLucasPrescott.StochasticDP.quadV
#print axioms StokeyLucasPrescott.StochasticDP.integral_quad_ar
#print axioms StokeyLucasPrescott.StochasticDP.quad_rhs_eq
#print axioms StokeyLucasPrescott.StochasticDP.quad_coeffs
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_13
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_13_book_form
#print axioms StokeyLucasPrescott.StochasticDP.abs_quadV_le
#print axioms StokeyLucasPrescott.StochasticDP.linPolicy
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_14
#print axioms StokeyLucasPrescott.StochasticDP.PosR
#print axioms StokeyLucasPrescott.StochasticDP.logModel
#print axioms StokeyLucasPrescott.StochasticDP.logPolicy
#print axioms StokeyLucasPrescott.StochasticDP.logV
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_11
#print axioms StokeyLucasPrescott.StochasticDP.policyKernel
#print axioms StokeyLucasPrescott.StochasticDP.policyKernel_apply
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_13
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_15a
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_15b
#print axioms StokeyLucasPrescott.StochasticDP.theorem_9_14
#print axioms StokeyLucasPrescott.StochasticDP.policyKernel'
#print axioms StokeyLucasPrescott.StochasticDP.measurable_policy'
#print axioms StokeyLucasPrescott.StochasticDP.policyKernel'_apply
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_17a
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_17b
#print axioms StokeyLucasPrescott.StochasticDP.flipMeasure
#print axioms StokeyLucasPrescott.StochasticDP.flipKernel
#print axioms StokeyLucasPrescott.StochasticDP.flipKernel_apply
#print axioms StokeyLucasPrescott.StochasticDP.isMarkovKernel_flipKernel
#print axioms StokeyLucasPrescott.StochasticDP.flipKernel_singleton
#print axioms StokeyLucasPrescott.StochasticDP.bv
#print axioms StokeyLucasPrescott.StochasticDP.measurable_bv
#print axioms StokeyLucasPrescott.StochasticDP.xP
#print axioms StokeyLucasPrescott.StochasticDP.measurable_xP
#print axioms StokeyLucasPrescott.StochasticDP.xNext
#print axioms StokeyLucasPrescott.StochasticDP.xPair
#print axioms StokeyLucasPrescott.StochasticDP.xTriple
#print axioms StokeyLucasPrescott.StochasticDP.IsMarkovAt
#print axioms StokeyLucasPrescott.StochasticDP.decodeZ
#print axioms StokeyLucasPrescott.StochasticDP.measurable_decodeZ
#print axioms StokeyLucasPrescott.StochasticDP.xKernel
#print axioms StokeyLucasPrescott.StochasticDP.measurable_xKernel_fun
#print axioms StokeyLucasPrescott.StochasticDP.xKernel_apply
#print axioms StokeyLucasPrescott.StochasticDP.isMarkovKernel_xKernel
#print axioms StokeyLucasPrescott.StochasticDP.xP_mem_Icc
#print axioms StokeyLucasPrescott.StochasticDP.decodeZ_xNext
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_16_markov
#print axioms StokeyLucasPrescott.StochasticDP.θg
#print axioms StokeyLucasPrescott.StochasticDP.θg_sq
#print axioms StokeyLucasPrescott.StochasticDP.θg_bounds
#print axioms StokeyLucasPrescott.StochasticDP.xP3_eq
#print axioms StokeyLucasPrescott.StochasticDP.xNext3_eq
#print axioms StokeyLucasPrescott.StochasticDP.bv_false
#print axioms StokeyLucasPrescott.StochasticDP.bv_true
#print axioms StokeyLucasPrescott.StochasticDP.decode_A
#print axioms StokeyLucasPrescott.StochasticDP.decode_B
#print axioms StokeyLucasPrescott.StochasticDP.mem_A
#print axioms StokeyLucasPrescott.StochasticDP.mem_B
#print axioms StokeyLucasPrescott.StochasticDP.triple_rect
#print axioms StokeyLucasPrescott.StochasticDP.ex_9_16
