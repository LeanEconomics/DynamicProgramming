/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Correspondences

SLP §3.3, pp. 56–61.

A correspondence `Γ : X → Y` assigns a set `Γ(x) ⊆ Y` to each `x`. The book defines continuity of
correspondences through sequences; `X` and `Y` here are metric spaces (the book's `X ⊆ ℝˡ`,
`Y ⊆ ℝᵐ`).

* `IsLHC`, `IsUHC` (p. 56), `IsCompactValued`, `image` (`Γ(X̂)`), `graph`.
* Ex 3.11 (upper hemi-continuity): `continuousAt_of_isUHC_singleton` (a), `isUHC_proj` (b),
  `isUHC_union` (c), `isUHC_inter` (d), `isUHC_comp` (e), `isUHC_pi` (f), `isCompact_image` (g).
* Ex 3.12 (lower hemi-continuity): `continuousAt_of_isLHC_singleton` (a), `isLHC_proj` (b),
  `isLHC_union` (c), `not_isLHC_inter` (d, the example), `isLHC_comp` (e), `isLHC_pi` (f).
  The positive half of (d) is `isLHC_inter_of_interior` in `ConvexCorrespondences`.
* `isCompact_graph` (Ex 3.15).
* `theorem_3_4`: a closed graph with bounded images of bounded sets gives a compact-valued u.h.c.
  correspondence; `closedGraph_not_uhc`: boundedness is needed.
* `theorem_3_5`: a convex graph with locally bounded selections gives a correspondence l.h.c. at
  interior points.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

/-- `Γ` is **lower hemi-continuous** at `x` (SLP p. 56). -/
def IsLHC (Γ : X → Set Y) (x : X) : Prop :=
  (Γ x).Nonempty ∧ ∀ y ∈ Γ x, ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) →
    ∃ N, ∃ ys : ℕ → Y, (∀ n ≥ N, ys n ∈ Γ (xs n)) ∧ Tendsto ys atTop (𝓝 y)

/-- `Γ` is **upper hemi-continuous** at `x` (SLP p. 56; the book applies it to compact-valued
correspondences). -/
def IsUHC (Γ : X → Set Y) (x : X) : Prop :=
  (Γ x).Nonempty ∧ ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) → ∀ ys : ℕ → Y, (∀ n, ys n ∈ Γ (xs n)) →
    ∃ y ∈ Γ x, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (ys ∘ φ) atTop (𝓝 y)

/-- `Γ` is compact-valued. -/
def IsCompactValued (Γ : X → Set Y) : Prop := ∀ x, IsCompact (Γ x)

/-- `Γ(X̂) = {y : y ∈ Γ(x) for some x ∈ X̂}`. -/
def image (Γ : X → Set Y) (S : Set X) : Set Y := ⋃ x ∈ S, Γ x

/-- The graph `A = {(x, y) : y ∈ Γ(x)}`. -/
def graph (Γ : X → Set Y) : Set (X × Y) := {p | p.2 ∈ Γ p.1}

/-! ### Exercise 3.11 -/

/-- **Ex 3.11a.** A single-valued u.h.c. correspondence is continuous. -/
theorem continuousAt_of_isUHC_singleton {f : X → Y} {x : X} (h : IsUHC (fun x => {f x}) x) :
    ContinuousAt f x := by
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro xs hxs
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨y, hy, φ, -, hφ⟩ := h.2 (xs ∘ ns) (hxs.comp hns) (fun n => f (xs (ns n))) fun n => rfl
  rw [mem_singleton_iff] at hy
  exact ⟨φ, by rw [← hy]; exact hφ⟩

/-- A continuous function is u.h.c. as a correspondence. -/
theorem isUHC_singleton_of_continuousAt {f : X → Y} {x : X} (h : ContinuousAt f x) :
    IsUHC (fun x => {f x}) x :=
  ⟨singleton_nonempty _, fun xs hxs ys hys => ⟨f x, rfl, id, strictMono_id, by
    have : ys = f ∘ xs := funext hys
    rw [this]
    exact h.tendsto.comp hxs⟩⟩

/-- **Ex 3.11b.** The projection `φ(x) = {y : (y, z) ∈ Γ(x) for some z}` of a compact-valued
u.h.c. correspondence is compact-valued and u.h.c. -/
theorem isUHC_proj {Γ : X → Set (Y × Z)} {x : X} (hc : IsCompact (Γ x)) (h : IsUHC Γ x) :
    IsCompact (Prod.fst '' Γ x) ∧ IsUHC (fun x => Prod.fst '' Γ x) x := by
  refine ⟨hc.image continuous_fst, h.1.image _, fun xs hxs ys hys => ?_⟩
  choose zs hzs using hys
  obtain ⟨p, hp, φ, hφ, hlim⟩ := h.2 xs hxs zs fun n => (hzs n).1
  refine ⟨p.1, ⟨p, hp, rfl⟩, φ, hφ, ?_⟩
  have := (continuous_fst.tendsto p).comp hlim
  refine this.congr fun n => ?_
  simp only [Function.comp_apply]
  exact (hzs (φ n)).2

/-- **Ex 3.11c.** The union of two compact-valued u.h.c. correspondences is compact-valued and
u.h.c. -/
theorem isUHC_union {φ ψ : X → Set Y} {x : X} (hφc : IsCompact (φ x)) (hψc : IsCompact (ψ x))
    (hφ : IsUHC φ x) (hψ : IsUHC ψ x) :
    IsCompact (φ x ∪ ψ x) ∧ IsUHC (fun x => φ x ∪ ψ x) x := by
  refine ⟨hφc.union hψc, hφ.1.mono subset_union_left, fun xs hxs ys hys => ?_⟩
  by_cases hfreq : ∃ᶠ n in atTop, ys n ∈ φ (xs n)
  · obtain ⟨ν, hν, hνφ⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨y, hy, μ, hμ, hlim⟩ := hφ.2 (xs ∘ ν) (hxs.comp hν.tendsto_atTop) (ys ∘ ν) hνφ
    exact ⟨y, Or.inl hy, ν ∘ μ, hν.comp hμ, hlim⟩
  · have hψfreq : ∃ᶠ n in atTop, ys n ∈ ψ (xs n) := by
      rw [not_frequently] at hfreq
      exact (hfreq.mono fun n hn => (hys n).resolve_left hn).frequently
    obtain ⟨ν, hν, hνψ⟩ := extraction_of_frequently_atTop hψfreq
    obtain ⟨y, hy, μ, hμ, hlim⟩ := hψ.2 (xs ∘ ν) (hxs.comp hν.tendsto_atTop) (ys ∘ ν) hνψ
    exact ⟨y, Or.inr hy, ν ∘ μ, hν.comp hμ, hlim⟩

/-- **Ex 3.11d.** A nonempty intersection of two compact-valued u.h.c. correspondences is
compact-valued and u.h.c. -/
theorem isUHC_inter {φ ψ : X → Set Y} {x : X} (hφc : IsCompact (φ x)) (hψc : IsCompact (ψ x))
    (hφ : IsUHC φ x) (hψ : IsUHC ψ x) (hne : (φ x ∩ ψ x).Nonempty) :
    IsCompact (φ x ∩ ψ x) ∧ IsUHC (fun x => φ x ∩ ψ x) x := by
  refine ⟨hφc.inter_right hψc.isClosed, hne, fun xs hxs ys hys => ?_⟩
  obtain ⟨y, hy, ν, hν, hlim⟩ := hφ.2 xs hxs ys fun n => (hys n).1
  obtain ⟨y', hy', μ, hμ, hlim'⟩ :=
    hψ.2 (xs ∘ ν) (hxs.comp hν.tendsto_atTop) (ys ∘ ν) fun n => (hys (ν n)).2
  have : y' = y := tendsto_nhds_unique hlim' (hlim.comp hμ.tendsto_atTop)
  rw [this] at hlim' hy'
  exact ⟨y, ⟨hy, hy'⟩, ν ∘ μ, hν.comp hμ, hlim'⟩

/-- **Ex 3.11g.** If `Γ` is u.h.c. at every point of a compact set `K`, then `Γ(K)` is compact. -/
theorem isCompact_image {Γ : X → Set Y} {K : Set X} (hK : IsCompact K)
    (h : ∀ x ∈ K, IsUHC Γ x) : IsCompact (image Γ K) := by
  refine IsSeqCompact.isCompact fun ys hys => ?_
  have hys' : ∀ n, ∃ x ∈ K, ys n ∈ Γ x := fun n => by
    simpa [image] using hys n
  choose xs hxK hxΓ using hys'
  obtain ⟨x, hx, ν, hν, hlim⟩ := hK.tendsto_subseq hxK
  obtain ⟨y, hy, μ, hμ, hlim'⟩ := (h x hx).2 (xs ∘ ν) hlim (ys ∘ ν) fun n => hxΓ (ν n)
  exact ⟨y, by simp only [image, mem_iUnion]; exact ⟨x, hx, hy⟩, ν ∘ μ, hν.comp hμ, hlim'⟩

/-- **Ex 3.11e.** The composition `Γ(x) = ψ(φ(x))` of compact-valued u.h.c. correspondences is
compact-valued and u.h.c. -/
theorem isUHC_comp {φ : X → Set Y} {ψ : Y → Set Z} {x : X} (hφc : IsCompact (φ x))
    (hφ : IsUHC φ x) (hψ : ∀ y, IsUHC ψ y) :
    IsCompact (image ψ (φ x)) ∧ IsUHC (fun x => image ψ (φ x)) x := by
  refine ⟨isCompact_image hφc fun y _ => hψ y, ?_, fun xs hxs zs hzs => ?_⟩
  · obtain ⟨y, hy⟩ := hφ.1
    obtain ⟨z, hz⟩ := (hψ y).1
    exact ⟨z, by simp only [image, mem_iUnion]; exact ⟨y, hy, hz⟩⟩
  have hzs' : ∀ n, ∃ y ∈ φ (xs n), zs n ∈ ψ y := fun n => by
    simpa [image] using hzs n
  choose ys hyφ hzψ using hzs'
  obtain ⟨y, hy, ν, hν, hlim⟩ := hφ.2 xs hxs ys hyφ
  obtain ⟨z, hz, μ, hμ, hlim'⟩ := (hψ y).2 (ys ∘ ν) hlim (zs ∘ ν) fun n => hzψ (ν n)
  exact ⟨z, by simp only [image, mem_iUnion]; exact ⟨y, hy, hz⟩, ν ∘ μ, hν.comp hμ, hlim'⟩

/-- **Ex 3.11f.** A finite product of compact-valued u.h.c. correspondences is compact-valued and
u.h.c. -/
theorem isUHC_pi {ι : Type*} [Fintype ι] {W : ι → Type*} [∀ i, MetricSpace (W i)]
    {Γ : ∀ i, X → Set (W i)} {x : X} (hc : ∀ i, IsCompact (Γ i x)) (h : ∀ i, IsUHC (Γ i) x) :
    IsCompact (Set.univ.pi fun i => Γ i x) ∧ IsUHC (fun x => Set.univ.pi fun i => Γ i x) x := by
  classical
  refine ⟨isCompact_univ_pi hc, univ_pi_nonempty_iff.2 fun i => (h i).1, fun xs hxs ys hys => ?_⟩
  -- extract a common convergent subsequence, one coordinate at a time
  have key : ∀ s : Finset ι, ∃ ν : ℕ → ℕ, StrictMono ν ∧ ∃ y : ∀ i, W i,
      ∀ i ∈ s, y i ∈ Γ i x ∧ Tendsto (fun n => ys (ν n) i) atTop (𝓝 (y i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, fun i => (h i).1.some, fun i hi => absurd hi
        (Finset.notMem_empty i)⟩
    | insert j s hj ih =>
      obtain ⟨ν, hν, y, hy⟩ := ih
      obtain ⟨yj, hyj, μ, hμ, hlim⟩ := (h j).2 (xs ∘ ν) (hxs.comp hν.tendsto_atTop)
        (fun n => ys (ν n) j) fun n => hys (ν n) j (mem_univ j)
      refine ⟨ν ∘ μ, hν.comp hμ, Function.update y j yj, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simp only [Function.update_self]
        exact ⟨hyj, hlim⟩
      · have hij : i ≠ j := fun h => hj (h ▸ hi)
        simp only [Function.update_of_ne hij]
        exact ⟨(hy i hi).1, (hy i hi).2.comp hμ.tendsto_atTop⟩
  obtain ⟨ν, hν, y, hy⟩ := key Finset.univ
  exact ⟨y, fun i _ => (hy i (Finset.mem_univ i)).1, ν, hν,
    tendsto_pi_nhds.2 fun i => (hy i (Finset.mem_univ i)).2⟩

/-! ### Exercise 3.12 -/

/-- **Ex 3.12a.** A single-valued l.h.c. correspondence is continuous. -/
theorem continuousAt_of_isLHC_singleton {f : X → Y} {x : X} (h : IsLHC (fun x => {f x}) x) :
    ContinuousAt f x := by
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro xs hxs
  obtain ⟨N, ys, hys, hlim⟩ := h.2 (f x) rfl xs hxs
  refine hlim.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  exact hys n hn

/-- **Ex 3.12b.** The projection of an l.h.c. correspondence is l.h.c. -/
theorem isLHC_proj {Γ : X → Set (Y × Z)} {x : X} (h : IsLHC Γ x) :
    IsLHC (fun x => Prod.fst '' Γ x) x := by
  refine ⟨h.1.image _, fun y hy xs hxs => ?_⟩
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨N, ps, hps, hlim⟩ := h.2 p hp xs hxs
  exact ⟨N, fun n => (ps n).1, fun n hn => ⟨ps n, hps n hn, rfl⟩,
    (continuous_fst.tendsto p).comp hlim⟩

/-- **Ex 3.12c.** The union of two l.h.c. correspondences is l.h.c. -/
theorem isLHC_union {φ ψ : X → Set Y} {x : X} (hφ : IsLHC φ x) (hψ : IsLHC ψ x) :
    IsLHC (fun x => φ x ∪ ψ x) x := by
  refine ⟨hφ.1.mono subset_union_left, fun y hy xs hxs => ?_⟩
  rcases hy with hy | hy
  · obtain ⟨N, ys, hys, hlim⟩ := hφ.2 y hy xs hxs
    exact ⟨N, ys, fun n hn => Or.inl (hys n hn), hlim⟩
  · obtain ⟨N, ys, hys, hlim⟩ := hψ.2 y hy xs hxs
    exact ⟨N, ys, fun n hn => Or.inr (hys n hn), hlim⟩

/-- **Ex 3.12e.** The composition of l.h.c. correspondences is l.h.c. -/
theorem isLHC_comp {φ : X → Set Y} {ψ : Y → Set Z} {x : X} (hφ : IsLHC φ x)
    (hψ : ∀ y, IsLHC ψ y) : IsLHC (fun x => image ψ (φ x)) x := by
  refine ⟨?_, fun z hz xs hxs => ?_⟩
  · obtain ⟨y, hy⟩ := hφ.1
    obtain ⟨z, hz⟩ := (hψ y).1
    exact ⟨z, by simp only [image, mem_iUnion]; exact ⟨y, hy, hz⟩⟩
  obtain ⟨y, hy, hz⟩ : ∃ y ∈ φ x, z ∈ ψ y := by simpa [image] using hz
  obtain ⟨N, ys, hys, hlim⟩ := hφ.2 y hy xs hxs
  obtain ⟨M, zs, hzs, hlim'⟩ := (hψ y).2 z hz ys hlim
  exact ⟨max N M, zs, fun n hn => by
    simp only [image, mem_iUnion]
    exact ⟨ys n, hys n (le_of_max_le_left hn), hzs n (le_of_max_le_right hn)⟩, hlim'⟩

/-- **Ex 3.12f.** A finite product of l.h.c. correspondences is l.h.c. -/
theorem isLHC_pi {ι : Type*} [Fintype ι] {W : ι → Type*} [∀ i, MetricSpace (W i)]
    {Γ : ∀ i, X → Set (W i)} {x : X} (h : ∀ i, IsLHC (Γ i) x) :
    IsLHC (fun x => Set.univ.pi fun i => Γ i x) x := by
  refine ⟨univ_pi_nonempty_iff.2 fun i => (h i).1, fun y hy xs hxs => ?_⟩
  have hi : ∀ i, ∃ N, ∃ ys : ℕ → W i, (∀ n ≥ N, ys n ∈ Γ i (xs n)) ∧
      Tendsto ys atTop (𝓝 (y i)) := fun i => (h i).2 (y i) (hy i (mem_univ i)) xs hxs
  choose N ys hys hlim using hi
  refine ⟨Finset.univ.sup N, fun n i => ys i n, fun n hn i _ => hys i n ?_,
    tendsto_pi_nhds.2 hlim⟩
  exact (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn

/-- **Ex 3.12d (the example).** The intersection of l.h.c. correspondences need not be l.h.c.:
`φ(x) = {0, 1}` and `ψ(x) = {0, 1 + |x|}` are l.h.c. with intersection `{0, 1}` at `x = 0` and
`{0}` elsewhere. -/
theorem not_isLHC_inter :
    (∀ x : ℝ, IsLHC (fun _ : ℝ => ({0, 1} : Set ℝ)) x) ∧
      (∀ x : ℝ, IsLHC (fun x : ℝ => ({0, 1 + |x|} : Set ℝ)) x) ∧
      (∀ x : ℝ, (({0, 1} : Set ℝ) ∩ {0, 1 + |x|}).Nonempty) ∧
      ¬ IsLHC (fun x : ℝ => ({0, 1} : Set ℝ) ∩ {0, 1 + |x|}) 0 := by
  refine ⟨fun x => ⟨⟨0, by simp⟩, fun y hy xs _ => ⟨0, fun _ => y, fun _ _ => hy,
      tendsto_const_nhds⟩⟩, fun x => ⟨⟨0, by simp⟩, fun y hy xs hxs => ?_⟩,
    fun x => ⟨0, by simp⟩, ?_⟩
  · rcases hy with rfl | rfl
    · exact ⟨0, fun _ => 0, fun _ _ => Or.inl rfl, tendsto_const_nhds⟩
    · exact ⟨0, fun n => 1 + |xs n|, fun _ _ => Or.inr rfl,
        tendsto_const_nhds.add hxs.abs⟩
  · rintro ⟨-, h⟩
    have hxs : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨N, ys, hys, hlim⟩ := h 1 (by simp) _ hxs
    -- along the sequence the intersection is `{0}`
    have hzero : ∀ n ≥ N, ys n = 0 := fun n hn => by
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨h1, h2⟩ := hys n hn
      rcases h2 with h2 | h2
      · exact h2
      · rcases h1 with h1 | h1
        · exact h1
        · rw [mem_singleton_iff] at h1 h2
          rw [h1, abs_of_pos hpos] at h2
          linarith
    have : Tendsto ys atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => (hzero n hn).symm⟩)
    have := tendsto_nhds_unique hlim this
    norm_num at this

/-! ### Exercise 3.15 and Theorems 3.4–3.5 -/

/-- **Ex 3.15.** A compact-valued u.h.c. correspondence on a compact space has a compact graph. -/
theorem isCompact_graph [CompactSpace X] {Γ : X → Set Y} (h : ∀ x, IsUHC Γ x) :
    IsCompact (graph Γ) := by
  refine IsSeqCompact.isCompact fun ps hps => ?_
  obtain ⟨x, -, ν, hν, hlim⟩ := isCompact_univ.tendsto_subseq (x := fun n => (ps n).1)
    fun _ => mem_univ _
  obtain ⟨y, hy, μ, hμ, hlim'⟩ := (h x).2 _ hlim (fun n => (ps (ν n)).2) fun n => hps (ν n)
  refine ⟨(x, y), hy, ν ∘ μ, hν.comp hμ, ?_⟩
  exact (Prod.tendsto_iff _ _).2 ⟨hlim.comp hμ.tendsto_atTop, hlim'⟩

/-- **Theorem 3.4.** If `Γ` is nonempty-valued with a closed graph, and `Γ(X̂)` is bounded for every
bounded `X̂`, then `Γ` is compact-valued and u.h.c. (`Y` proper, as `ℝᵐ` is). -/
theorem theorem_3_4 [ProperSpace Y] {Γ : X → Set Y} (hne : ∀ x, (Γ x).Nonempty)
    (hcl : IsClosed (graph Γ))
    (hbdd : ∀ S : Set X, Bornology.IsBounded S → Bornology.IsBounded (image Γ S)) (x : X) :
    IsCompact (Γ x) ∧ IsUHC Γ x := by
  have hclx : IsClosed (Γ x) := by
    have := hcl.preimage (Continuous.prodMk_right x)
    exact this
  have hbx : Bornology.IsBounded (Γ x) :=
    (hbdd {x} Bornology.isBounded_singleton).subset fun y hy => by
      simp only [image, mem_iUnion]; exact ⟨x, rfl, hy⟩
  refine ⟨Metric.isCompact_of_isClosed_isBounded hclx hbx, hne x, fun xs hxs ys hys => ?_⟩
  have hb : Bornology.IsBounded (image Γ (range xs)) :=
    hbdd _ (Metric.isBounded_range_of_tendsto xs hxs)
  obtain ⟨y, -, ν, hν, hlim⟩ := tendsto_subseq_of_bounded hb fun n => by
    simp only [image, mem_iUnion]; exact ⟨xs n, ⟨n, rfl⟩, hys n⟩
  refine ⟨y, ?_, ν, hν, hlim⟩
  have hgr : Tendsto (fun n => (xs (ν n), ys (ν n))) atTop (𝓝 (x, y)) :=
    (Prod.tendsto_iff _ _).2 ⟨hxs.comp hν.tendsto_atTop, hlim⟩
  exact hcl.mem_of_tendsto hgr (Eventually.of_forall fun n => hys (ν n))

/-- **Boundedness is needed in Theorem 3.4** (SLP p. 61): `Γ(0) = {0}`, `Γ(x) = {0, 1/x}` for
`x > 0` has a closed graph but is not u.h.c. at `0`. -/
theorem closedGraph_not_uhc :
    IsClosed (graph fun x : ℝ => {y : ℝ | y = 0 ∨ (0 ≤ x ∧ x * y = 1)}) ∧
      ¬ IsUHC (fun x : ℝ => {y : ℝ | y = 0 ∨ (0 ≤ x ∧ x * y = 1)}) 0 := by
  refine ⟨?_, fun h => ?_⟩
  · have : graph (fun x : ℝ => {y : ℝ | y = 0 ∨ (0 ≤ x ∧ x * y = 1)}) =
        {p : ℝ × ℝ | p.2 = 0} ∪ ({p : ℝ × ℝ | 0 ≤ p.1} ∩ {p : ℝ × ℝ | p.1 * p.2 = 1}) := by
      ext p; simp [graph]
    rw [this]
    exact (isClosed_eq continuous_snd continuous_const).union
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const))
  · have hxs : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨y, -, ν, hν, hlim⟩ := h.2 _ hxs (fun n => (n : ℝ) + 1) fun n => by
      right
      refine ⟨by positivity, ?_⟩
      field_simp
    -- the subsequence `ν n + 1` is unbounded
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) 1 one_pos
    obtain ⟨n, hn⟩ := exists_nat_gt (y + 1)
    have h1 := hN (max N n) (le_max_left _ _)
    rw [Function.comp_apply, Real.dist_eq] at h1
    have h2 : (n : ℝ) ≤ ν (max N n) := by
      exact_mod_cast (le_max_right N n).trans (hν.id_le _)
    have := (abs_lt.1 h1).2
    linarith

/-- **Theorem 3.5.** Let `Γ` be nonempty-valued on `X ⊆ E` with a convex graph over `X`, and suppose
every bounded `X̂ ⊆ X` has a bounded `Ŷ` meeting every `Γ(x)`, `x ∈ X̂`. Then `Γ` is l.h.c. at
every interior point of `X`. -/
theorem theorem_3_5 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {S : Set E} {Γ : E → Set F} (hne : ∀ x ∈ S, (Γ x).Nonempty)
    (hconv : Convex ℝ {p : E × F | p.1 ∈ S ∧ p.2 ∈ Γ p.1})
    (hloc : ∀ T ⊆ S, Bornology.IsBounded T → ∃ B : Set F, Bornology.IsBounded B ∧
      ∀ x ∈ T, (Γ x ∩ B).Nonempty)
    {x₀ : E} (hx₀ : x₀ ∈ interior S) : IsLHC Γ x₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (mem_interior_iff_mem_nhds.1 hx₀)
  refine ⟨hne x₀ (interior_subset hx₀), fun y₀ hy₀ xs hxs => ?_⟩
  -- a bounded selection on the ball
  obtain ⟨B, hB, hsel⟩ := hloc _ hball Metric.isBounded_closedBall
  choose sel hsel using fun x : Metric.closedBall x₀ ε => hsel x x.2
  obtain ⟨C, hC⟩ := (hB.subset_closedBall y₀)
  -- the boundary points `d_n` and weights `α_n`
  set v : ℕ → E := fun n => xs n - x₀
  set α : ℕ → ℝ := fun n => ‖v n‖ / ε
  set d : ℕ → E := fun n => x₀ + (ε / ‖v n‖) • v n
  have hd : ∀ n, d n ∈ Metric.closedBall x₀ ε := fun n => by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [d, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rcases eq_or_ne ‖v n‖ 0 with h | h
    · rw [h, mul_zero]; exact hε.le
    · rw [abs_of_nonneg (div_nonneg hε.le (norm_nonneg _)), div_mul_cancel₀ _ h]
  set ys : ℕ → F := fun n => α n • sel ⟨d n, hd n⟩ + (1 - α n) • y₀
  -- eventually `‖v n‖ ≤ ε`
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hxs ε hε
  have hα0 : ∀ n, 0 ≤ α n := fun n => div_nonneg (norm_nonneg _) hε.le
  have hα1 : ∀ n ≥ N, α n ≤ 1 := fun n hn => by
    rw [div_le_one hε]
    have := hN n hn
    rw [dist_eq_norm] at this
    exact this.le
  have hxs_eq : ∀ n, α n • d n + (1 - α n) • x₀ = xs n := fun n => by
    simp only [α, d, smul_add, smul_smul]
    rcases eq_or_ne ‖v n‖ 0 with h | h
    · have hv : v n = 0 := norm_eq_zero.1 h
      simp only [v] at hv
      rw [sub_eq_zero.1 hv, h]
      simp
    · rw [show ‖v n‖ / ε * (ε / ‖v n‖) = 1 by field_simp, one_smul]
      simp only [v]
      module
  refine ⟨N, ys, fun n hn => ?_, ?_⟩
  · -- membership through convexity of the graph
    have hp : ((d n, sel ⟨d n, hd n⟩) : E × F) ∈ {p : E × F | p.1 ∈ S ∧ p.2 ∈ Γ p.1} :=
      ⟨hball (hd n), (hsel ⟨d n, hd n⟩).1⟩
    have hq : ((x₀, y₀) : E × F) ∈ {p : E × F | p.1 ∈ S ∧ p.2 ∈ Γ p.1} :=
      ⟨interior_subset hx₀, hy₀⟩
    have hmem := hconv hp hq (hα0 n) (sub_nonneg.2 (hα1 n hn)) (by ring)
    simp only [Prod.smul_mk, Prod.mk_add_mk, hxs_eq] at hmem
    exact hmem.2
  · -- `‖y_n − y₀‖ = α_n ‖sel(d_n) − y₀‖ ≤ α_n C → 0`
    have hαlim : Tendsto α atTop (𝓝 0) := by
      have := ((tendsto_iff_norm_sub_tendsto_zero.1 hxs).div_const ε)
      simpa [α, v] using this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using hαlim.mul_const C)
    have h1 : ys n - y₀ = α n • (sel ⟨d n, hd n⟩ - y₀) := by
      simp only [ys]
      module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα0 n), ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (hC (hsel ⟨d n, hd n⟩).2) (hα0 n)

end StokeyLucasPrescott.MathematicalPreliminaries
