/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.NSSTChain
import VUniformErgodicity.Communication

/-!
# Minimal sets and irreducibility (MT §7.2)

Meyn and Tweedie, §7.2, pp. 154–157.

Deterministic part (CM(F) with `F(·, u)` continuous for `u ∈ O`):

* `IsMinimal F O M` (MT p. 155): `M` is non-empty, closed, invariant and contains no smaller
  non-empty closed invariant set. **Correction:** read literally ("does not contain any closed
  invariant set as a proper subset") the definition admits only `∅`, since `∅` is closed and
  invariant (`minimal_literal_eq_empty`); "non-empty" is needed, as Proposition 7.2.3 implicitly
  assumes.
* **Proposition 7.2.3** (p. 155): `proposition_7_2_3`, for non-empty `M`: `M` is minimal iff
  `closure A₊(x) = M` for all `x ∈ M` iff `Ω₊(x) = M` for all `x ∈ M`.
* `IsIndecomposable`, `IsMIrreducible`, `IsGloballyAttracting` (MT pp. 156–157).
  `translation_indecomposable_no_minimal` (MT p. 156): for `x + u` on `ℝ` with `O = (0, 1)` the
  control system is indecomposable but has no minimal set.
* **Correction** (MT p. 156): "if CM(F) is M-irreducible then `M⁰ = ∅`" is false:
  `halving_noReach_nonempty` (`x ↦ x/2`, `M = {0}`). The argument needs `M⁰` closed, which
  Proposition 7.2.1 (iii) gives only for open `M`. What is true is
  `IsMIrreducible.minimal_subset`: `M` lies in every non-empty closed invariant set, so every
  `A₊(x)` comes arbitrarily close to `M`.
* **Correction** (MT p. 156): indecomposability is not "clearly necessary" for a unique minimal
  set: `indecomposable_not_necessary` (`x ↦ 2x`, unique minimal set `{0}`, yet `{0}` and
  `[1, ∞)` are disjoint closed invariant sets).
* **Proposition 7.2.5** (p. 157): `proposition_7_2_5_i` (M-irreducible iff a globally attracting
  state exists) and `proposition_7_2_5_ii` (then the unique minimal set is
  `closure A₊(x*) = Ω₊(x*)`).

Stochastic part (NSS(F) under (NSS3), `F` continuous):

* **Proposition 7.2.2** (p. 155): `proposition_7_2_2_ii`, for open `U` and every `k`,
  `A₊ᵏ(x) ∩ U ≠ ∅` iff `Pᵏ(x, U) > 0`; `proposition_7_2_2_iii`, `A₊(x) ∩ U ≠ ∅` iff
  `K_{a_{1/2}}(x, U) > 0`; `proposition_7_2_2_i`, a closed set is absorbing iff it is invariant.
  The book assumes forward accessibility; it is not needed.
* In `NSSIrreducibility`: `isTChain_restrictKernel`, the restriction of a T-chain to an absorbing
  set is a T-chain;
* **Theorem 7.2.4** (p. 156, in `NSSIrreducibility`): `theorem_7_2_4_i`, a minimal set is absorbing;
  `theorem_7_2_4_ii`, under (NSS3) and the rank condition (CM3) for a `C¹` map, NSS(F)
  restricted to `M` is an open set irreducible, `ψ`-irreducible T-chain.
* **Theorem 7.2.6** (p. 157, in `NSSIrreducibility`): `theorem_7_2_6`, under the same hypotheses
  NSS(F) is `ψ`-irreducible iff CM(F) is M-irreducible. (Only "if" uses the T-chain property.) The
  book's "`x*` is globally attracting" for a point of `supp ψ` uses only `x* ∈ closure A₊(y)` for
  every `y`; `isMIrreducible_of_forall_mem_closure` shows this suffices.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Minimal sets of the control model -/

variable {X W : Type*}

/-- The empty set is invariant. -/
theorem isCMInvariant_empty (F : X × W → X) (O : Set W) : IsCMInvariant F O ∅ := by
  intro y hy
  simp [reachSet] at hy

/-- `A₊({x}) = A₊(x)`. -/
theorem reachSet_singleton (F : X × W → X) (O : Set W) (x : X) :
    reachSet F O {x} = reach F O x := by
  simp [reachSet]

/-- `A₊ᵏ({x}) = A₊ᵏ(x)`. -/
theorem reachKSet_singleton (F : X × W → X) (O : Set W) (k : ℕ) (x : X) :
    reachKSet F O k {x} = reachK F O k x := by
  simp [reachKSet]

variable [TopologicalSpace X]

/-- A set is **minimal** for CM(F) (MT p. 155): it is non-empty, closed and invariant, and every
non-empty closed invariant subset is the whole set. -/
def IsMinimal (F : X × W → X) (O : Set W) (M : Set X) : Prop :=
  M.Nonempty ∧ IsClosed M ∧ IsCMInvariant F O M ∧
    ∀ C ⊆ M, C.Nonempty → IsClosed C → IsCMInvariant F O C → C = M

/-- **Correction** (MT p. 155): read literally, "closed, invariant, and does not contain any
closed invariant set as a proper subset" forces `M = ∅`, because `∅` is closed and invariant. -/
theorem minimal_literal_eq_empty {F : X × W → X} {O : Set W} {M : Set X}
    (h : IsClosed M ∧ IsCMInvariant F O M ∧ ∀ C ⊂ M, ¬ (IsClosed C ∧ IsCMInvariant F O C)) :
    M = ∅ := by
  by_contra hne
  exact h.2.2 ∅ (Set.empty_ssubset.2 (nonempty_iff_ne_empty.2 hne))
    ⟨isClosed_empty, isCMInvariant_empty F O⟩

/-- A closed invariant set containing `x` contains the closure of `A₊(x)`. -/
theorem IsCMInvariant.closure_reach_subset {F : X × W → X} {O : Set W} {E : Set X}
    (hE : IsCMInvariant F O E) (hEc : IsClosed E) {x : X} (hx : x ∈ E) :
    _root_.closure (reach F O x) ⊆ E :=
  closure_minimal (hE.reach_subset hx) hEc

omit [TopologicalSpace X] in
/-- Intersections of two invariant sets are invariant. -/
theorem IsCMInvariant.inter {F : X × W → X} {O : Set W} {C D : Set X} (hC : IsCMInvariant F O C)
    (hD : IsCMInvariant F O D) : IsCMInvariant F O (C ∩ D) := by
  rw [isCMInvariant_iff_step] at hC hD ⊢
  exact fun x hx w hw => ⟨hC x hx.1 w hw, hD x hx.2 w hw⟩

/-- `closure A₊(x)` is closed and invariant. -/
theorem isCMInvariant_closure_reach {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) (x : X) :
    IsCMInvariant F O (closure (reach F O x)) := by
  have := (proposition_7_2_1_i hF {x}).2
  rwa [reachSet_singleton] at this

/-- `Ω₊(x) ⊆ closure A₊(x)`. -/
theorem omegaSet_subset_closure_reach (F : X × W → X) (O : Set W) (x : X) :
    omegaSet F O {x} ⊆ closure (reach F O x) := by
  intro y hy
  have h1 := mem_iInter₂.1 hy 1 le_rfl
  refine closure_mono (fun z hz => ?_) h1
  obtain ⟨k, -, hz⟩ := mem_iUnion₂.1 hz
  rw [reachKSet_singleton] at hz
  exact reachK_subset_reach F O k x hz

/-- `closure (⋃_{k ≥ N} A₊ᵏ(x))` is a non-empty closed invariant set. -/
theorem tail_closure_props {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) (hO : O.Nonempty) (x : X) (N : ℕ) :
    (closure (⋃ k ≥ N, reachKSet F O k {x})).Nonempty ∧
      IsClosed (closure (⋃ k ≥ N, reachKSet F O k {x})) ∧
      IsCMInvariant F O (closure (⋃ k ≥ N, reachKSet F O k {x})) := by
  refine ⟨?_, isClosed_closure, ?_⟩
  · obtain ⟨y, hy⟩ := reachK_nonempty (F := F) hO N x
    refine ⟨y, subset_closure (mem_iUnion₂.2 ⟨N, le_rfl, ?_⟩)⟩
    rwa [reachKSet_singleton]
  · rw [← reachSet_reachKSet]
    exact (isCMInvariant_reachSet F O _).closure hF

/-- The tail sets of a point of a closed invariant `E` lie in `E`. -/
theorem tail_closure_subset {F : X × W → X} {O : Set W} {E : Set X} (hE : IsCMInvariant F O E)
    (hEc : IsClosed E) {x : X} (hx : x ∈ E) (N : ℕ) :
    closure (⋃ k ≥ N, reachKSet F O k {x}) ⊆ E := by
  refine closure_minimal (fun y hy => ?_) hEc
  obtain ⟨k, -, hy⟩ := mem_iUnion₂.1 hy
  rw [reachKSet_singleton] at hy
  exact hE.reachK_subset hx k hy

/-- **Proposition 7.2.3** (MT p. 155): for a non-empty `M`, the following are equivalent:
(i) `M` is minimal; (ii) `closure A₊(x) = M` for every `x ∈ M`; (iii) `Ω₊(x) = M` for every
`x ∈ M`. -/
theorem proposition_7_2_3 {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) (hO : O.Nonempty) {M : Set X}
    (hM : M.Nonempty) :
    (IsMinimal F O M ↔ ∀ x ∈ M, closure (reach F O x) = M) ∧
      (IsMinimal F O M ↔ ∀ x ∈ M, omegaSet F O {x} = M) := by
  have h12 : IsMinimal F O M ↔ ∀ x ∈ M, closure (reach F O x) = M := by
    constructor
    · intro hmin x hx
      exact hmin.2.2.2 _ (hmin.2.2.1.closure_reach_subset hmin.2.1 hx)
        ⟨x, subset_closure (self_mem_reach F O x)⟩ isClosed_closure
        (isCMInvariant_closure_reach hF x)
    · intro h
      obtain ⟨x₀, hx₀⟩ := hM
      refine ⟨⟨x₀, hx₀⟩, (h x₀ hx₀) ▸ isClosed_closure,
        (h x₀ hx₀) ▸ isCMInvariant_closure_reach hF x₀, fun C hCM hCne hCc hCi => ?_⟩
      obtain ⟨y, hy⟩ := hCne
      exact hCM.antisymm ((h y (hCM hy)).symm.subset.trans (hCi.closure_reach_subset hCc hy))
  refine ⟨h12, ?_⟩
  constructor
  · intro hmin x hx
    refine (omegaSet_subset_closure_reach F O x).trans ((h12.1 hmin x hx).subset) |>.antisymm ?_
    intro y hy
    refine mem_iInter₂.2 fun N _ => ?_
    obtain ⟨hne, hc, hi⟩ := tail_closure_props hF hO x N
    rw [hmin.2.2.2 _ (tail_closure_subset hmin.2.2.1 hmin.2.1 hx N) hne hc hi]
    exact hy
  · intro h
    obtain ⟨x₀, hx₀⟩ := hM
    have hMc : IsClosed M := (h x₀ hx₀) ▸ isClosed_omegaSet F O {x₀}
    have hMi : IsCMInvariant F O M := (h x₀ hx₀) ▸ proposition_7_2_1_ii hF {x₀}
    refine h12.2 fun x hx => (hMi.closure_reach_subset hMc hx).antisymm ?_
    rw [← h x hx]
    exact omegaSet_subset_closure_reach F O x

/-! ### Indecomposability and M-irreducibility -/

/-- CM(F) is **indecomposable** (MT p. 156): there are no two disjoint non-empty closed invariant
sets. -/
def IsIndecomposable (F : X × W → X) (O : Set W) : Prop :=
  ∀ C D : Set X, C.Nonempty → D.Nonempty → IsClosed C → IsClosed D → IsCMInvariant F O C →
    IsCMInvariant F O D → ¬ Disjoint C D

/-- CM(F) is **M-irreducible** (MT p. 156): it is indecomposable and has a minimal set. -/
def IsMIrreducible (F : X × W → X) (O : Set W) : Prop :=
  IsIndecomposable F O ∧ ∃ M, IsMinimal F O M

/-- `x` is **globally attracting** (MT p. 157): `x ∈ Ω₊(y)` for every `y`. -/
def IsGloballyAttracting (F : X × W → X) (O : Set W) (x : X) : Prop :=
  ∀ y, x ∈ omegaSet F O {y}

/-- If `x* ∈ closure A₊(y)` for every `y`, then `closure A₊(x*)` is minimal. -/
theorem isMinimal_closure_reach_of_forall_mem_closure {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) {x : X}
    (h : ∀ y, x ∈ closure (reach F O y)) : IsMinimal F O (closure (reach F O x)) := by
  have hc : ∀ y, closure (reach F O x) ⊆ closure (reach F O y) := fun y =>
    (isCMInvariant_closure_reach hF y).closure_reach_subset isClosed_closure (h y)
  refine ⟨⟨x, subset_closure (self_mem_reach F O x)⟩, isClosed_closure,
    isCMInvariant_closure_reach hF x, fun C hCM hCne hCc hCi => ?_⟩
  obtain ⟨y, hy⟩ := hCne
  exact hCM.antisymm ((hc y).trans (hCi.closure_reach_subset hCc hy))

/-- If `x* ∈ closure A₊(y)` for every `y`, CM(F) is M-irreducible. -/
theorem isMIrreducible_of_forall_mem_closure {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) {x : X}
    (h : ∀ y, x ∈ closure (reach F O y)) : IsMIrreducible F O := by
  refine ⟨fun C D hC hD hCc hDc hCi hDi hdisj => ?_,
    ⟨_, isMinimal_closure_reach_of_forall_mem_closure hF h⟩⟩
  obtain ⟨c, hc⟩ := hC
  obtain ⟨d, hd⟩ := hD
  exact Set.disjoint_left.1 hdisj (hCi.closure_reach_subset hCc hc (h c))
    (hDi.closure_reach_subset hDc hd (h d))

/-- **What is true of `M⁰`** (MT p. 156): if CM(F) is M-irreducible with minimal set `M`, then
`M` lies in every non-empty closed invariant set. -/
theorem IsMIrreducible.minimal_subset {F : X × W → X} {O : Set W} (h : IsIndecomposable F O)
    {M : Set X} (hM : IsMinimal F O M) {C : Set X} (hC : C.Nonempty) (hCc : IsClosed C)
    (hCi : IsCMInvariant F O C) : M ⊆ C := by
  have hne : (C ∩ M).Nonempty := Set.not_disjoint_iff_nonempty_inter.1
    (h C M hC hM.1 hCc hM.2.1 hCi hM.2.2.1)
  have := hM.2.2.2 (C ∩ M) inter_subset_right hne (hCc.inter hM.2.1) (hCi.inter hM.2.2.1)
  rw [← this]
  exact inter_subset_left

/-- **Proposition 7.2.5 (i)** (MT p. 157): CM(F) is M-irreducible iff it has a globally
attracting state. Every point of the minimal set is globally attracting. -/
theorem proposition_7_2_5_i {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) (hO : O.Nonempty) :
    IsMIrreducible F O ↔ ∃ x, IsGloballyAttracting F O x := by
  constructor
  · rintro ⟨hind, M, hM⟩
    obtain ⟨x, hx⟩ := hM.1
    refine ⟨x, fun y => mem_iInter₂.2 fun N _ => ?_⟩
    obtain ⟨hne, hc, hi⟩ := tail_closure_props hF hO y N
    exact IsMIrreducible.minimal_subset hind hM hne hc hi hx
  · rintro ⟨x, hx⟩
    exact isMIrreducible_of_forall_mem_closure hF fun y =>
      omegaSet_subset_closure_reach F O y (hx y)

/-- **Proposition 7.2.5 (ii)** (MT p. 157): if `x*` is globally attracting, the unique minimal set
is `closure A₊(x*) = Ω₊(x*)`. -/
theorem proposition_7_2_5_ii {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) (hO : O.Nonempty) {x : X}
    (hx : IsGloballyAttracting F O x) :
    IsMinimal F O (closure (reach F O x)) ∧ omegaSet F O {x} = closure (reach F O x) ∧
      ∀ M, IsMinimal F O M → M = closure (reach F O x) := by
  have hcl : ∀ y, x ∈ closure (reach F O y) := fun y => omegaSet_subset_closure_reach F O y (hx y)
  have hmin := isMinimal_closure_reach_of_forall_mem_closure hF hcl
  refine ⟨hmin, ?_, fun M hM => ?_⟩
  · exact ((proposition_7_2_3 hF hO hmin.1).2.1 hmin) x (subset_closure (self_mem_reach F O x))
  · obtain ⟨y, hy⟩ := hM.1
    have hsub : closure (reach F O x) ⊆ M :=
      hM.2.2.1.closure_reach_subset hM.2.1 (hM.2.2.1.closure_reach_subset hM.2.1 hy (hcl y))
    exact (hM.2.2.2 _ hsub hmin.1 hmin.2.1 hmin.2.2.1).symm

/-! ### Examples on the line -/

/-- `x ↦ x + u` driven `n` times by the constant control `c` gives `x + n c`. -/
theorem controlMap_translate_const (n : ℕ) (x c : ℝ) :
    controlMap (fun p : ℝ × ℝ => p.1 + p.2) n x (fun _ => c) = x + n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [controlMap_succ]
    change controlMap (fun p : ℝ × ℝ => p.1 + p.2) n x (fun _ => c) + c = _
    rw [ih]
    push_cast
    ring

/-- **Indecomposable without a minimal set** (MT p. 156): for `xₖ₊₁ = xₖ + uₖ₊₁` on `ℝ` with
`O = (0, 1)`, CM(F) is indecomposable but has no minimal set. -/
theorem translation_indecomposable_no_minimal :
    IsIndecomposable (fun p : ℝ × ℝ => p.1 + p.2) (Ioo 0 1) ∧
      ∀ M, ¬ IsMinimal (fun p : ℝ × ℝ => p.1 + p.2) (Ioo 0 1) M := by
  have hup : ∀ C : Set ℝ, IsCMInvariant (fun p : ℝ × ℝ => p.1 + p.2) (Ioo 0 1) C →
      ∀ x ∈ C, ∀ t > 0, x + t ∈ C := by
    intro C hC x hx t ht
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have hn0 : (0 : ℝ) < n := lt_trans ht hn
    have hmem : x + t ∈ reachK (fun p : ℝ × ℝ => p.1 + p.2) (Ioo 0 1) n x := by
      refine ⟨fun _ => t / n, fun _ => ⟨div_pos ht hn0, (div_lt_one hn0).2 hn⟩, ?_⟩
      rw [controlMap_translate_const]
      field_simp
    exact hC.reachK_subset hx n hmem
  refine ⟨fun C D hC hD _ _ hCi hDi hdisj => ?_, fun M hM => ?_⟩
  · obtain ⟨c, hc⟩ := hC
    obtain ⟨d, hd⟩ := hD
    have h1 := hup C hCi c hc (max c d + 1 - c) (by linarith [le_max_left c d])
    have h2 := hup D hDi d hd (max c d + 1 - d) (by linarith [le_max_right c d])
    rw [add_sub_cancel] at h1 h2
    exact Set.disjoint_left.1 hdisj h1 h2
  · obtain ⟨x, hx⟩ := hM.1
    have hx1 : x + 1 ∈ M := hup M hM.2.2.1 x hx 1 one_pos
    have hCi : IsCMInvariant (fun p : ℝ × ℝ => p.1 + p.2) (Ioo 0 1) (M ∩ Ici (x + 1)) := by
      rw [isCMInvariant_iff_step]
      intro z hz w hw
      exact ⟨isCMInvariant_iff_step.1 hM.2.2.1 z hz.1 w hw,
        le_trans (mem_Ici.1 hz.2) (by simp only; linarith [hw.1])⟩
    have := hM.2.2.2 (M ∩ Ici (x + 1)) inter_subset_left ⟨x + 1, hx1, mem_Ici.2 le_rfl⟩
      (hM.2.1.inter isClosed_Ici) hCi
    have hxC : x ∈ M ∩ Ici (x + 1) := by rw [this]; exact hx
    linarith [mem_Ici.1 hxC.2]

/-- `x ↦ x/2` driven `n` times gives `x/2ⁿ`, whatever the controls. -/
theorem controlMap_halve (n : ℕ) (x : ℝ) (u : Fin n → ℝ) :
    controlMap (fun p : ℝ × ℝ => p.1 / 2) n x u = x / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [controlMap_succ]
    change controlMap (fun p : ℝ × ℝ => p.1 / 2) n x (Fin.init u) / 2 = _
    rw [ih, pow_succ, div_div]

/-- **Correction** (MT p. 156): an M-irreducible control model can have `M⁰ ≠ ∅`. For
`xₖ₊₁ = xₖ/2` on `ℝ` (any non-empty control set) the minimal set is `M = {0}`, the model is
M-irreducible, yet `1 ∈ M⁰`: no trajectory from `1` reaches `0`. -/
theorem halving_noReach_nonempty {O : Set ℝ} (hO : O.Nonempty) :
    IsMIrreducible (fun p : ℝ × ℝ => p.1 / 2) O ∧ IsMinimal (fun p : ℝ × ℝ => p.1 / 2) O {0} ∧
      (1 : ℝ) ∈ noReach (fun p : ℝ × ℝ => p.1 / 2) O {0} := by
  have hcont : ∀ w ∈ O, Continuous fun x : ℝ => (fun p : ℝ × ℝ => p.1 / 2) (x, w) :=
    fun _ _ => continuous_id.div_const 2
  have hzero : ∀ y : ℝ, (0 : ℝ) ∈ closure (reach (fun p : ℝ × ℝ => p.1 / 2) O y) := by
    intro y
    obtain ⟨w, hw⟩ := hO
    have hmem : ∀ n : ℕ, y / 2 ^ n ∈ reach (fun p : ℝ × ℝ => p.1 / 2) O y := fun n =>
      mem_reach_iff.2 ⟨n, fun _ => w, fun _ => hw, controlMap_halve n y _⟩
    have ht : Tendsto (fun n : ℕ => y / 2 ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul y
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      rw [one_div, inv_pow, div_eq_mul_inv]
    exact mem_closure_of_tendsto ht (Eventually.of_forall hmem)
  have hmin : IsMinimal (fun p : ℝ × ℝ => p.1 / 2) O {0} := by
    refine ⟨singleton_nonempty 0, isClosed_singleton, ?_, fun C hC hCne _ _ => ?_⟩
    · rw [isCMInvariant_iff_step]
      intro x hx w _
      rw [mem_singleton_iff] at hx ⊢
      simp [hx]
    · exact Subset.antisymm hC (singleton_subset_iff.2 (by
        obtain ⟨c, hc⟩ := hCne
        rwa [mem_singleton_iff.1 (hC hc)] at hc))
  refine ⟨isMIrreducible_of_forall_mem_closure hcont hzero, hmin, ?_⟩
  refine Set.disjoint_left.2 fun z hz h0 => ?_
  obtain ⟨n, u, -, rfl⟩ := mem_reach_iff.1 hz
  rw [mem_singleton_iff, controlMap_halve] at h0
  exact (div_ne_zero one_ne_zero (pow_ne_zero n two_ne_zero)) h0

/-- `x ↦ 2x` driven `n` times gives `2ⁿx`, whatever the controls. -/
theorem controlMap_double (n : ℕ) (x : ℝ) (u : Fin n → ℝ) :
    controlMap (fun p : ℝ × ℝ => 2 * p.1) n x u = 2 ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [controlMap_succ]
    change 2 * controlMap (fun p : ℝ × ℝ => 2 * p.1) n x (Fin.init u) = _
    rw [ih, pow_succ]
    ring

/-- **Correction** (MT p. 156): indecomposability is not necessary for a unique minimal set. For
`xₖ₊₁ = 2xₖ` on `ℝ` (any non-empty control set) `{0}` is the only minimal set, yet `{0}` and
`[1, ∞)` are disjoint non-empty closed invariant sets. -/
theorem indecomposable_not_necessary {O : Set ℝ} (hO : O.Nonempty) :
    (∀ M, IsMinimal (fun p : ℝ × ℝ => 2 * p.1) O M ↔ M = {0}) ∧
      ¬ IsIndecomposable (fun p : ℝ × ℝ => 2 * p.1) O := by
  have hcont : ∀ w ∈ O, Continuous fun x : ℝ => (fun p : ℝ × ℝ => 2 * p.1) (x, w) :=
    fun _ _ => continuous_const.mul continuous_id
  have hinv0 : IsCMInvariant (fun p : ℝ × ℝ => 2 * p.1) O {0} := by
    rw [isCMInvariant_iff_step]
    intro x hx w _
    rw [mem_singleton_iff] at hx ⊢
    simp [hx]
  have hmin0 : IsMinimal (fun p : ℝ × ℝ => 2 * p.1) O {0} := by
    refine ⟨singleton_nonempty 0, isClosed_singleton, hinv0, fun C hC hne _ _ => ?_⟩
    obtain ⟨c, hc⟩ := hne
    exact Subset.antisymm hC (singleton_subset_iff.2 (by rwa [mem_singleton_iff.1 (hC hc)] at hc))
  refine ⟨fun M => ⟨fun hM => ?_, fun h => h ▸ hmin0⟩, fun h => ?_⟩
  · -- every point of a minimal set is `0`
    have hpts : ∀ y ∈ M, y = 0 := by
      intro y hy
      by_contra hy0
      obtain ⟨w, hw⟩ := hO
      have h2y : 2 * y ∈ M := isCMInvariant_iff_step.1 hM.2.2.1 y hy w hw
      have hcl := ((proposition_7_2_3 hcont ⟨w, hw⟩ hM.1).1.1 hM) (2 * y) h2y
      have hymem : y ∈ closure (reach (fun p : ℝ × ℝ => 2 * p.1) O (2 * y)) := by
        rw [hcl]; exact hy
      have hsub : reach (fun p : ℝ × ℝ => 2 * p.1) O (2 * y) ⊆ {z | 2 * |y| ≤ |z|} := by
        intro z hz
        obtain ⟨n, u, -, rfl⟩ := mem_reach_iff.1 hz
        rw [controlMap_double, mem_ofPred_eq, abs_mul, abs_mul, abs_pow, abs_two]
        have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        have h0 : 0 ≤ |y| := abs_nonneg y
        nlinarith
      have hcl' : IsClosed {z : ℝ | 2 * |y| ≤ |z|} :=
        isClosed_le continuous_const continuous_abs
      have := closure_minimal hsub hcl' hymem
      have hy' : 0 < |y| := abs_pos.2 hy0
      simp only [mem_ofPred_eq] at this
      linarith
    obtain ⟨y, hy⟩ := hM.1
    have hy0 := hpts y hy
    subst hy0
    exact Subset.antisymm (fun z hz => mem_singleton_iff.2 (hpts z hz))
      (singleton_subset_iff.2 hy)
  · refine h {0} (Ici 1) (singleton_nonempty 0) ⟨1, mem_Ici.2 le_rfl⟩ isClosed_singleton
      isClosed_Ici hinv0 ?_ ?_
    · rw [isCMInvariant_iff_step]
      intro x hx _ _
      simp only [mem_Ici] at hx ⊢
      linarith
    · rw [Set.disjoint_singleton_left]
      simp

/-! ### Proposition 7.2.2: reachable sets and the kernel -/

variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasureSpace W]
  [BorelSpace W] [(volume : Measure W).IsAddHaarMeasure]

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure] in
/-- The control maps are continuous in the controls when `F` is continuous. -/
theorem continuous_controlMap_right {F : X × W → X} (hF : Continuous F) (k : ℕ) (x : X) :
    Continuous (controlMap F k x) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    have : controlMap F (k + 1) x = fun u => F (controlMap F k x (Fin.init u), u (Fin.last k)) :=
      rfl
    rw [this]
    exact hF.comp ((ih.comp (continuous_pi fun i => continuous_apply _)).prodMk
      (continuous_apply _))

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
/-- Under (NSS3), every open set meeting `O_w` has positive `Γ`-measure. -/
theorem measure_pos_of_isOpen_inter {Γ : Measure W} {γ : W → ℝ≥0∞} (hΓ : IsLSCDensity Γ γ)
    {B : Set W} (hB : IsOpen B) (hne : (B ∩ controlSet γ).Nonempty) : 0 < Γ B := by
  have hO := isOpen_controlSet hΓ.1
  rw [hΓ.2, withDensity_apply _ hB.measurableSet, setLIntegral_pos_iff hΓ.1.measurable]
  have : Function.support γ ∩ B = B ∩ controlSet γ := by
    ext w
    simp only [mem_inter_iff, Function.mem_support, controlSet, mem_ofPred_eq, ne_eq,
      pos_iff_ne_zero]
    tauto
  rw [this]
  exact (hB.inter hO).measure_pos _ hne

/-- Under (NSS3), every open subset of `Wᵏ` meeting `O_wᵏ` has positive `Γ^{⊗k}`-measure. -/
theorem pi_measure_pos_of_isOpen {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {k : ℕ} {V : Set (Fin k → W)} (hV : IsOpen V) {u : Fin k → W}
    (huV : u ∈ V) (hu : ∀ i, u i ∈ controlSet γ) :
    0 < (Measure.pi fun _ : Fin k => Γ) V := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hV u huV
  refine lt_of_lt_of_le ?_ (measure_mono hball)
  rw [ball_pi u hr, Measure.pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun i _ => (measure_pos_of_isOpen_inter hΓ Metric.isOpen_ball
    ⟨u i, Metric.mem_ball_self hr, hu i⟩).ne'

omit [(volume : Measure W).IsAddHaarMeasure] in
/-- Under (NSS3), `Γ^{⊗k}` gives full measure to `O_wᵏ`. -/
theorem pi_measure_compl_controlSet {Γ : Measure W} [IsProbabilityMeasure Γ]
    {γ : W → ℝ≥0∞} (hΓ : IsLSCDensity Γ γ) (k : ℕ) :
    (Measure.pi fun _ : Fin k => Γ) {u | ∀ i, u i ∈ controlSet γ}ᶜ = 0 := by
  have : {u : Fin k → W | ∀ i, u i ∈ controlSet γ}ᶜ =
      ⋃ i, Function.eval i ⁻¹' (controlSet γ)ᶜ := by
    ext u; simp
  rw [this]
  exact measure_iUnion_null fun i =>
    Measure.pi_eval_preimage_null _ (measure_compl_controlSet hΓ)

variable [MeasurableSpace X] [BorelSpace X]

/-- **Proposition 7.2.2 (ii)** (MT p. 155): under (NSS3), for `F` continuous and `U` open,
`A₊ᵏ(x) ∩ U ≠ ∅` iff `Pᵏ(x, U) > 0` (for every `k`; the book states `k ≥ 1`). -/
theorem proposition_7_2_2_ii {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Continuous F) {U : Set X} (hU : IsOpen U)
    (k : ℕ) (x : X) :
    (reachK F (controlSet γ) k x ∩ U).Nonempty ↔ 0 < (nssKernel Γ F ^ k) x U := by
  rw [nssKernel, recursionKernel_pow_apply' Γ hF.measurable k x hU.measurableSet]
  constructor
  · rintro ⟨y, ⟨u, hu, rfl⟩, hyU⟩
    exact pi_measure_pos_of_isOpen hΓ (hU.preimage (continuous_controlMap_right hF k x)) hyU hu
  · intro hpos
    by_contra hc
    have hsub : {u | controlMap F k x u ∈ U} ⊆ {u : Fin k → W | ∀ i, u i ∈ controlSet γ}ᶜ :=
      fun u hu hO => hc ⟨_, ⟨u, hO, rfl⟩, hu⟩
    exact hpos.ne' (measure_mono_null hsub (pi_measure_compl_controlSet hΓ k))

/-- **Proposition 7.2.2 (iii)** (MT p. 155): under (NSS3), for `F` continuous and `U` open,
`A₊(x) ∩ U ≠ ∅` iff `K_{a_{1/2}}(x, U) > 0`. -/
theorem proposition_7_2_2_iii {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Continuous F) {U : Set X} (hU : IsOpen U)
    (x : X) :
    (reach F (controlSet γ) x ∩ U).Nonempty ↔ 0 < resolventHalf (nssKernel Γ F) x U := by
  rw [resolventHalf_pos_iff _ x hU.measurableSet]
  simp_rw [← proposition_7_2_2_ii hΓ hF hU, reach, iUnion_inter, nonempty_iUnion]

/-- **Proposition 7.2.2 (i)** (MT p. 155): under (NSS3), for `F` continuous, a closed set is
absorbing for NSS(F) iff it is invariant for CM(F). -/
theorem proposition_7_2_2_i {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Continuous F) {A : Set X} (hA : IsClosed A) :
    IsAbsorbing (nssKernel Γ F) A ↔ IsCMInvariant F (controlSet γ) A := by
  have hM := isMarkovKernel_recursionKernel Γ hF.measurable
  have key := fun x => proposition_7_2_2_ii hΓ hF hA.isOpen_compl 1 x
  simp_rw [pow_one] at key
  constructor
  · intro h
    rw [isCMInvariant_iff_step]
    intro x hx w hw
    by_contra hc
    have h1 : F (x, w) ∈ reachK F (controlSet γ) 1 x := by
      simpa using step_mem_reachK (self_mem_reachK_zero F (controlSet γ) x) hw
    have hpos := (key x).1 ⟨F (x, w), h1, hc⟩
    have h1 := h x hx
    rw [← prob_compl_eq_zero_iff hA.measurableSet] at h1
    exact hpos.ne' h1
  · intro h x hx
    rw [← prob_compl_eq_zero_iff hA.measurableSet]
    by_contra hc
    obtain ⟨y, hy, hyA⟩ := (key x).2 (pos_iff_ne_zero.2 hc)
    exact hyA (h.reachK_subset hx 1 hy)

end MeynTweedie.VUniformErgodicity
