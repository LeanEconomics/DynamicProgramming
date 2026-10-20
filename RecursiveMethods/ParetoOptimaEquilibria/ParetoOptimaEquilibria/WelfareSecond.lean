/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.Welfare

/-!
# The Second Welfare Theorem

SLP §15.2, pp. 454–458.

* Separation of disjoint convex sets, in the two cases of Assumption 15.5, proved here directly
  (the book's Theorem 15.2 is not used):
  * `exists_dual_nonneg_of_zero_notMem`: in a finite-dimensional space a nonempty convex set
    missing `0` lies in a half-space `{φ ≥ 0}`, `φ ≠ 0` (interior nonempty: Mathlib's
    `geometric_hahn_banach_of_nonempty_interior_point`; interior empty: the affine span is a
    proper affine subspace and a nonzero functional vanishing on its direction is constant on the
    set).
  * `exists_separating_of_finiteDimensional`, `exists_separating_of_interior`,
    `exists_separating_of_assumption15_5`: a nonzero `φ` with `φ(b) ≤ φ(a)` for `a ∈ A`, `b ∈ B`.
* `SupportsAllocation`: conditions (3) and (4) of Theorem 15.4 (a "quasi-equilibrium" price).
* **Theorem 15.4** (`theorem_15_4`, Second Welfare Theorem, p. 455): under Assumptions 15.1–15.5,
  a Pareto optimum with one nonsatiated consumer is supported by a nonzero continuous linear
  functional. `preferredSum` is the set `A = Åₕ + Σ_{i≠h} Aᵢ`; `convex_preferredSum`,
  `preferredSum_disjoint` and `le_of_weaklyPreferred` are steps 1–3 of the proof.
* **Remark** (`remark_cheaper_point`, p. 456): a supporting price with a cheaper point for every
  consumer is a competitive equilibrium price.
* `exists_better_of_localNonsatiation` and `welfare_theorems_corrected`: the corrected form of the
  p. 458 claim that "the CE and PO allocations coincide" (see `WelfareExamples` for the
  counterexamples to the book's version).

**Corrections** (to the proof of Theorem 15.4; see also `Welfare`).
* Step 1: the convexity of `Aᵢ`, `Åᵢ` uses Assumptions 15.1–15.3, not 15.2 alone
  (`convex_weaklyPreferred`, `assumption15_2_convex_counterexample`).
* Step 3: the extension from `Åₕ + Σ_{i≠h} Aᵢ` to `Σᵢ Aᵢ` uses `Aₕ ⊆ cl Åₕ` (15.1, 15.2 and
  `x̂ₕ`) and continuity of `φ`, not continuity of `uₕ` (`le_of_weaklyPreferred`,
  `continuity_closure_counterexample`).
* Step 4: the book does not state that the separating constant is `c = φ(Σᵢ xᵢ⁰) = φ(Σⱼ yⱼ⁰)`,
  which is what turns the separation into (3) and (4). Here the separation is stated without a
  constant and (3), (4) are derived by comparing with `Σᵢ xᵢ⁰ = Σⱼ yⱼ⁰`, which lies in both
  `Σᵢ Aᵢ` and `Y`.
* Theorem 15.2 needs `A ≠ ∅` (and `B ≠ ∅` in finite dimensions); in Theorem 15.4 both sets are
  nonempty (`preferredSum_nonempty`).
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Set Pointwise

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] {ι κ : Type*} [Fintype ι]
  [Fintype κ]

/-! ### Separation -/

/-- In a finite-dimensional normed space, a nonempty convex set `C` with `0 ∉ C` lies in a closed
half-space `{φ ≥ 0}` of a nonzero continuous linear functional `φ`. -/
theorem exists_dual_nonneg_of_zero_notMem [FiniteDimensional ℝ S] {C : Set S}
    (hC : Convex ℝ C) (hne : C.Nonempty) (h0 : (0 : S) ∉ C) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∀ c ∈ C, 0 ≤ φ c := by
  by_cases hint : (interior C).Nonempty
  · obtain ⟨f, hf0, hf⟩ := geometric_hahn_banach_of_nonempty_interior_point hC
      (fun h => h0 (interior_subset h)) hint
    refine ⟨-f, neg_ne_zero.2 hf0, fun c hc => ?_⟩
    have := hf c hc
    simp only [map_zero] at this
    simp only [neg_apply]
    linarith
  · have hspan : affineSpan ℝ C ≠ ⊤ := fun h =>
      hint (hC.interior_nonempty_iff_affineSpan_eq_top.2 h)
    have hdir : (affineSpan ℝ C).direction ≠ ⊤ := fun h =>
      hspan ((AffineSubspace.direction_eq_top_iff_of_nonempty
        ((affineSpan_nonempty (k := ℝ)).2 hne)).1 h)
    obtain ⟨g, hg0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hdir)
    obtain ⟨c0, hc0⟩ := hne
    have hconst : ∀ c ∈ C, g c = g c0 := fun c hc => by
      have hmem : c -ᵥ c0 ∈ (affineSpan ℝ C).direction :=
        AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hc) (mem_affineSpan ℝ hc0)
      have := hle hmem
      rw [LinearMap.mem_ker, vsub_eq_sub, map_sub] at this
      linarith
    set f : StrongDual ℝ S := LinearMap.toContinuousLinearMap g with hf
    have hfg : ∀ v, f v = g v := fun v => rfl
    have hf0 : f ≠ 0 := fun h => hg0 (LinearMap.ext fun v => by
      rw [← hfg, h]
      rfl)
    rcases le_total 0 (g c0) with hs | hs
    · exact ⟨f, hf0, fun c hc => by rw [hfg, hconst c hc]; exact hs⟩
    · refine ⟨-f, neg_ne_zero.2 hf0, fun c hc => ?_⟩
      rw [neg_apply, hfg, hconst c hc]
      linarith

/-- **Separation in finite dimensions**: disjoint nonempty convex sets `A`, `B` of a
finite-dimensional normed space are separated by a nonzero continuous linear functional,
`φ(b) ≤ φ(a)` for `a ∈ A`, `b ∈ B`. -/
theorem exists_separating_of_finiteDimensional [FiniteDimensional ℝ S] {A B : Set S}
    (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hdisj : Disjoint A B) : ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ B, φ b ≤ φ a := by
  obtain ⟨φ, hφ0, hφ⟩ := exists_dual_nonneg_of_zero_notMem (hA.sub hB) (hAne.sub hBne)
    hdisj.zero_notMem_sub_set
  refine ⟨φ, hφ0, fun a ha b hb => ?_⟩
  have := hφ (a - b) (sub_mem_sub ha hb)
  rw [map_sub] at this
  linarith

/-- **Separation with an interior point** (Mathlib's geometric Hahn–Banach): if `B` is convex with
nonempty interior, `A` is convex and nonempty, and `A ∩ B = ∅`, then a nonzero continuous linear
functional has `φ(b) ≤ φ(a)` for `a ∈ A`, `b ∈ B`. -/
theorem exists_separating_of_interior {A B : Set S} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hAne : A.Nonempty) (hBint : (interior B).Nonempty) (hdisj : Disjoint A B) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ B, φ b ≤ φ a := by
  obtain ⟨f, c, hf0, hfB, hfA⟩ := geometric_hahn_banach_of_nonempty_interior hB hA
    (hdisj.symm.mono_left interior_subset) hBint hAne
  exact ⟨f, hf0, fun a ha b hb => (hfB b hb).trans (hfA a ha)⟩

/-- Separation under the dichotomy of Assumption 15.5: `B` has an interior point or `S` is finite
dimensional. -/
theorem exists_separating_of_assumption15_5 {A B : Set S} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hdisj : Disjoint A B)
    (h5 : (interior B).Nonempty ∨ FiniteDimensional ℝ S) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ B, φ b ≤ φ a := by
  rcases h5 with h | h
  · exact exists_separating_of_interior hA hB hAne h hdisj
  · have := h
    exact exists_separating_of_finiteDimensional hA hB hAne hBne hdisj

/-! ### Theorem 15.4 -/

/-- Conditions (3) and (4) of Theorem 15.4: `φ` supports the allocation, i.e. each `xᵢ⁰` minimises
cost over the weakly preferred set `Aᵢ` and each `yⱼ⁰` maximises profit over `Yⱼ`. -/
def SupportsAllocation (X : ι → Set S) (u : ι → S → ℝ) (Y : κ → Set S) (x : ι → S) (y : κ → S)
    (φ : StrongDual ℝ S) : Prop :=
  (∀ i, ∀ z ∈ X i, u i (x i) ≤ u i z → φ (x i) ≤ φ z) ∧ ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y j)

/-- The set `A = Åₕ + Σ_{i≠h} Aᵢ` of the proof of Theorem 15.4: sums `Σᵢ zᵢ` with every `zᵢ` in
the weakly preferred set `Aᵢ` and `zₕ` in the strictly preferred set `Åₕ`. -/
def preferredSum (X : ι → Set S) (u : ι → S → ℝ) (x : ι → S) (h : ι) : Set S :=
  {w | ∃ z : ι → S, (∀ i, z i ∈ X i ∧ u i (x i) ≤ u i (z i)) ∧ u h (x h) < u h (z h) ∧
    w = ∑ i, z i}

/-- Step 1–2 of the proof of Theorem 15.4: `A` is convex (Assumptions 15.1–15.3). -/
theorem convex_preferredSum {X : ι → Set S} {u : ι → S → ℝ} (h1 : Assumption15_1 X)
    (h2 : Assumption15_2 X u) (h3 : Assumption15_3 X u) (x : ι → S) (h : ι) :
    Convex ℝ (preferredSum X u x h) := by
  rintro _ ⟨z, hz, hzh, rfl⟩ _ ⟨z', hz', hzh', rfl⟩ a b ha hb hab
  refine ⟨fun i => a • z i + b • z' i, fun i => ?_, ?_, ?_⟩
  · exact convex_weaklyPreferred (h1 i) (h2 i) (h3 i) _ (hz i) (hz' i) ha hb hab
  · exact (convex_strictlyPreferred (h1 h) (h2 h) (h3 h) _ ⟨(hz h).1, hzh⟩
      ⟨(hz' h).1, hzh'⟩ ha hb hab).2
  · rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]

omit [NormedSpace ℝ S] in
/-- `A` is nonempty when consumer `h` has a strictly better point `x̂ₕ`. -/
theorem preferredSum_nonempty {X : ι → Set S} {u : ι → S → ℝ} {x : ι → S}
    (hx : ∀ i, x i ∈ X i) {h : ι} {xhat : S} (hxhat : xhat ∈ X h)
    (hsat : u h (x h) < u h xhat) : (preferredSum X u x h).Nonempty := by
  classical
  refine ⟨_, Function.update x h xhat, fun i => ?_, by simpa using hsat, rfl⟩
  rcases eq_or_ne i h with rfl | hi
  · simp only [Function.update_self]
    exact ⟨hxhat, hsat.le⟩
  · simp only [Function.update_of_ne hi]
    exact ⟨hx i, le_rfl⟩

omit [NormedSpace ℝ S] in
/-- Step 2 of the proof of Theorem 15.4: at a Pareto optimum, `A ∩ Y = ∅`. -/
theorem preferredSum_disjoint {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S}
    {y : κ → S} (hPO : ParetoOptimal X u Y x y) (h : ι) :
    Disjoint (preferredSum X u x h) (aggTech Y) := by
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, hzh, rfl⟩ ⟨y', hy', hsum⟩
  exact hPO.2 ⟨z, y', ⟨fun i => (hz i).1, hy', sub_eq_zero.2 hsum⟩, fun i => (hz i).2, h, hzh⟩

/-- Step 3 of the proof of Theorem 15.4, corrected: if `φ(b) ≤ φ(a)` for `a ∈ A`, `b ∈ Y`, then
also `φ(b) ≤ φ(Σᵢ zᵢ)` for every `(zᵢ)` with `zᵢ ∈ Aᵢ` for all `i`. The reason is `Aₕ ⊆ cl Åₕ`
(`weaklyPreferred_subset_closure`) and continuity of `φ`. -/
theorem le_of_weaklyPreferred {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) {h : ι} {xhat : S} (hxhat : xhat ∈ X h)
    (hsat : u h (x h) < u h xhat) {φ : StrongDual ℝ S}
    (hsep : ∀ a ∈ preferredSum X u x h, ∀ b ∈ aggTech Y, φ b ≤ φ a) (z : ι → S)
    (hz : ∀ i, z i ∈ X i ∧ u i (x i) ≤ u i (z i)) {b : S} (hb : b ∈ aggTech Y) :
    φ b ≤ φ (∑ i, z i) := by
  classical
  set R := ∑ i ∈ Finset.univ \ {h}, z i with hR
  have hstrict : {v | v ∈ X h ∧ u h (x h) < u h v} ⊆ {v | φ b ≤ φ (v + R)} := by
    rintro v ⟨hv, hvlt⟩
    have hmem : ∑ i, Function.update z h v i ∈ preferredSum X u x h := by
      refine ⟨Function.update z h v, fun i => ?_, by simpa using hvlt, rfl⟩
      rcases eq_or_ne i h with rfl | hi
      · simp only [Function.update_self]
        exact ⟨hv, hvlt.le⟩
      · simp only [Function.update_of_ne hi]
        exact hz i
    have := hsep _ hmem b hb
    rwa [Finset.sum_update_of_mem (Finset.mem_univ h)] at this
  have hclosed : IsClosed {v | φ b ≤ φ (v + R)} :=
    isClosed_le continuous_const (φ.continuous.comp (continuous_id.add continuous_const))
  have hzh : z h ∈ {v | φ b ≤ φ (v + R)} :=
    closure_minimal hstrict hclosed
      (weaklyPreferred_subset_closure (h1 h) (h2 h) hxhat hsat (hz h))
  rwa [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ h)]

/-- **Theorem 15.4** (Second Welfare Theorem, p. 455). Under Assumptions 15.1–15.5, if
`[(xᵢ⁰), (yⱼ⁰)]` is Pareto optimal and some consumer `h` has `x̂ₕ ∈ Xₕ` with
`uₕ(x̂ₕ) > uₕ(xₕ⁰)`, then a nonzero continuous linear functional `φ` satisfies (3) and (4). -/
theorem theorem_15_4 {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S} {y : κ → S}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (h3 : Assumption15_3 X u)
    (h4 : Assumption15_4 Y) (h5 : Assumption15_5 S Y) (hPO : ParetoOptimal X u Y x y)
    {h : ι} {xhat : S} (hxhat : xhat ∈ X h) (hsat : u h (x h) < u h xhat) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ SupportsAllocation X u Y x y φ := by
  classical
  obtain ⟨hxX, hyY, hxy⟩ := hPO.1
  obtain ⟨φ, hφ0, hsep⟩ := exists_separating_of_assumption15_5
    (convex_preferredSum h1 h2 h3 x h) h4 (preferredSum_nonempty hxX hxhat hsat)
    ⟨_, y, hyY, rfl⟩ (preferredSum_disjoint hPO h) h5
  have hext := le_of_weaklyPreferred h1 h2 hxhat hsat hsep
  have hxy' : ∑ i, x i = ∑ j, y j := sub_eq_zero.mp hxy
  refine ⟨φ, hφ0, fun i z hz hle => ?_, fun j w hw => ?_⟩
  · -- (3): compare `Σⱼ yⱼ⁰ = Σᵢ xᵢ⁰ ∈ Y` with `z + Σ_{i' ≠ i} xᵢ'⁰ ∈ Σᵢ Aᵢ`
    have key := hext (Function.update x i z) (fun i' => by
      rcases eq_or_ne i' i with rfl | hi
      · simp only [Function.update_self]
        exact ⟨hz, hle⟩
      · simp only [Function.update_of_ne hi]
        exact ⟨hxX i', le_rfl⟩) (b := ∑ j, y j) ⟨y, hyY, rfl⟩
    rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← hxy',
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i), map_add,
      map_add] at key
    linarith
  · -- (4): compare `w + Σ_{j' ≠ j} yⱼ'⁰ ∈ Y` with `Σᵢ xᵢ⁰ ∈ Σᵢ Aᵢ`
    have key := hext x (fun i' => ⟨hxX i', le_rfl⟩)
      (b := ∑ j', Function.update y j w j') ⟨Function.update y j w, fun j' => by
        rcases eq_or_ne j' j with rfl | hj
        · simp only [Function.update_self]
          exact hw
        · simp only [Function.update_of_ne hj]
          exact hyY j', rfl⟩
    rw [Finset.sum_update_of_mem (Finset.mem_univ j), hxy',
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j), map_add,
      map_add] at key
    linarith

/-! ### The Remark on p. 456 -/

/-- **Remark** (cheaper point ⇒ competitive equilibrium, p. 456). Under Assumptions 15.1 and 15.3,
if `[(xᵢ⁰), (yⱼ⁰)]` is feasible, `φ` satisfies (3) and (4), and every consumer has a cheaper point
`xᵢ′ ∈ Xᵢ`, `φ(xᵢ′) < φ(xᵢ⁰)`, then `[(xᵢ⁰), (yⱼ⁰), φ]` is a competitive equilibrium. -/
theorem remark_cheaper_point {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S}
    {y : κ → S} {φ : StrongDual ℝ S} (h1 : Assumption15_1 X) (h3 : Assumption15_3 X u)
    (hF : Feasible X Y x y) (hφ : SupportsAllocation X u Y x y φ)
    (hcheap : ∀ i, ∃ z ∈ X i, φ z < φ (x i)) : CompetitiveEq X u Y x y φ := by
  refine ⟨hF, fun i z hz hzle => ?_, hφ.2⟩
  obtain ⟨x', hx', hlt⟩ := hcheap i
  set p : ℝ → S := fun θ => θ • x' + (1 - θ) • z with hp
  have hpc : Continuous p := by fun_prop
  have hp0 : p 0 = z := by simp [hp]
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), p θ ∈ X i ∧ u i (p θ) < u i (x i) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
    have hpX : p θ ∈ X i := h1 i hx' hz hθ.1.le (by linarith [hθ.2]) (by ring)
    refine ⟨hpX, ?_⟩
    by_contra hge
    push Not at hge
    have hcost := hφ.1 i (p θ) hpX hge
    simp only [hp, map_add, map_smul, smul_eq_mul] at hcost
    nlinarith [hθ.1, hθ.2]
  have hlim : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝[X i] z) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hev.mono fun θ hθ => hθ.1⟩
    rw [← hp0]
    exact (hpc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ((h3 i z hz).tendsto.comp hlim) (hev.mono fun θ hθ => hθ.2.le)

/-! ### The corrected form of the p. 458 claim -/

omit [NormedSpace ℝ S] [Fintype ι] in
/-- Under local nonsatiation every consumer has a strictly better point than any `xᵢ ∈ Xᵢ`; this
supplies the hypothesis `x̂ₕ` of Theorem 15.4. -/
theorem exists_better_of_localNonsatiation {X : ι → Set S} {u : ι → S → ℝ}
    (hLNS : LocalNonsatiation X u) {x : ι → S} (hx : ∀ i, x i ∈ X i) (i : ι) :
    ∃ xhat ∈ X i, u i (x i) < u i xhat := by
  obtain ⟨zs, hzsX, -, hzsu⟩ := hLNS i (x i) (hx i)
  exact ⟨zs 0, hzsX 0, hzsu 0⟩

/-- **The welfare theorems, correctly combined** (the NOTE to p. 458). With local nonsatiation and
Assumptions 15.1–15.5, and at least one consumer:
(a) every competitive equilibrium allocation is Pareto optimal (Theorem 15.3);
(b) every Pareto optimum is supported by a nonzero continuous linear functional satisfying (3),
(4) (Theorem 15.4);
(c) a Pareto optimum is a competitive equilibrium allocation if some nonzero supporting
functional leaves every consumer a cheaper point (Remark).
The book's "the two sets coincide exactly" is false (`WelfareExamples`). -/
theorem welfare_theorems_corrected [Nonempty ι] {X : ι → Set S} {u : ι → S → ℝ}
    {Y : κ → Set S} (hLNS : LocalNonsatiation X u) (h1 : Assumption15_1 X)
    (h2 : Assumption15_2 X u) (h3 : Assumption15_3 X u) (h4 : Assumption15_4 Y)
    (h5 : Assumption15_5 S Y) (x : ι → S) (y : κ → S) :
    ((∃ φ, CompetitiveEq X u Y x y φ) → ParetoOptimal X u Y x y) ∧
    (ParetoOptimal X u Y x y → ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ SupportsAllocation X u Y x y φ) ∧
    (ParetoOptimal X u Y x y → ∀ φ : StrongDual ℝ S, SupportsAllocation X u Y x y φ →
      (∀ i, ∃ z ∈ X i, φ z < φ (x i)) → CompetitiveEq X u Y x y φ) := by
  refine ⟨fun ⟨φ, hφ⟩ => theorem_15_3 hLNS hφ, fun hPO => ?_,
    fun hPO φ hφ hcheap => remark_cheaper_point h1 h3 hPO.1 hφ hcheap⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨xhat, hxhat, hsat⟩ := exists_better_of_localNonsatiation hLNS hPO.1.1 i
  exact theorem_15_4 h1 h2 h3 h4 h5 hPO hxhat hsat

end StokeyLucasPrescott.ParetoOptimaEquilibria
