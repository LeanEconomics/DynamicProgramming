/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.OCLemma641
import InfiniteHorizonDP.SLPMaximum
import InfiniteHorizonDP.SLPSelection

/-!
# Theorem 6.4.1: existence

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCExistence`), namespace renamed.

Miao, §6.4, pp. 174–175. Under Assumptions 6.4.1–6.4.6, the solution `V_t` of the Bellman
equation (6.29) is continuous and the policy correspondence `G_t` is nonempty, compact-valued
and upper hemicontinuous, by backward induction with Lemma 6.4.1 and the Theorem of the Maximum
(SLP Theorem 3.6, `theorem_3_6`); each `G_t` then has a measurable selection (SLP Theorem 7.6,
`theorem_7_6`).

* `theorem_6_4_1`: the induction for any class `P` of functions for which Lemma 6.4.1 holds
  (`ExpCont P`) and which contains every `V_t`.
* `theorem_6_4_1_compact`: case (ii) of Assumption 6.4.3 (`Z` compact, `Q` Feller).
* `theorem_6_4_1_countable`: case (i) (`Z` discrete). **Correction:** here Lemma 6.4.1 needs
  bounded functions (`lemma_6_4_1_countable_counterexample`), so we add that the rewards are
  bounded on `X × Z × A`; then every `V_t` is bounded (`V_bounded`).
* `theorem_6_4_1_selection`: for actions in `ℝ^m`, each `G_t` has a measurable selection.
* `objS`, `Gs_eq_argmax`: the objective on `(X × Z) × A` and `G_t` as its argmax correspondence.

Assumptions 6.4.1–6.4.2 (convexity) and 5.1.2 (`β ∈ (0, 1)`) are not used. The state space
`X × Z` is the subtype `↥(X ×ˢ univ)` of `E × Z`; `E`, `F`, `Z` are metric spaces (the book's
Borel sets in Euclidean spaces).
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

namespace OCModel

variable {E F Z : Type*} [MeasurableSpace Z] (M : OCModel E F Z)

/-- The objective of (6.29) on the graph of `Γ`, as a function on `(X × Z) × A`. -/
noncomputable def objS (t : ℕ) (f : E → Z → ℝ) (p : ↥(M.X ×ˢ (Set.univ : Set Z)) × F) : ℝ :=
  M.obj t f p.1.1.1 p.1.1.2 p.2

theorem maxValue_objS (t : ℕ) (f : E → Z → ℝ) (s : ↥(M.X ×ˢ (Set.univ : Set Z))) :
    maxValue (M.objS t f) M.Γs s = M.bellman t f s.1.1 s.1.2 := rfl

theorem V_eq_maxValue {t : ℕ} (ht : t < M.T) (s : ↥(M.X ×ˢ (Set.univ : Set Z))) :
    M.V t s.1.1 s.1.2 = maxValue (M.objS t (M.V (t + 1))) M.Γs s := by
  rw [maxValue_objS, M.V_succ ht]

/-- `G_t` is the argmax correspondence of the objective (6.29). -/
theorem Gs_eq_argmax {t : ℕ} (ht : t < M.T) :
    M.Gs t = argmax (M.objS t (M.V (t + 1))) M.Γs := by
  funext s
  ext a
  change a ∈ M.Γ s.1.1 s.1.2 ∧ M.obj t (M.V (t + 1)) s.1.1 s.1.2 a = M.V t s.1.1 s.1.2 ↔
    a ∈ M.Γs s ∧ M.objS t (M.V (t + 1)) (s, a) = maxValue (M.objS t (M.V (t + 1))) M.Γs s
  rw [← M.V_eq_maxValue ht]
  rfl

/-- The bound `|∫ f| ≤ C` for a probability measure and `|f| ≤ C`. -/
theorem oc_abs_integral_le {μ : Measure Z} [IsProbabilityMeasure μ] {f : Z → ℝ} {C : ℝ}
    (hf : ∀ z, |f z| ≤ C) : |∫ z, f z ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := C) (f := f)
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hf z)
  simpa [Real.norm_eq_abs, measureReal_def] using this

variable [MetricSpace E] [MetricSpace F] [MetricSpace Z]

/-- The objective of (6.29) is continuous on the graph of `Γ` when `u_t` is continuous and the
continuation value `h` of Lemma 6.4.1 is. -/
theorem continuousOn_objS (h644 : M.Assumption644) {t : ℕ}
    (hu : ContinuousOn (fun p : E × Z × F => M.u t p.1 p.2.1 p.2.2) (M.X ×ˢ Set.univ ×ˢ M.A))
    {f : E → Z → ℝ}
    (hc : ContinuousOn (fun p : E × F × Z => M.cont f p.1 p.2.1 p.2.2) (M.X ×ˢ M.A ×ˢ Set.univ)) :
    ContinuousOn (M.objS t f) (graph M.Γs) := by
  have hA : ∀ p ∈ graph M.Γs, p.2 ∈ M.A := fun p hp => h644.1 _ p.1.2.1 _ hp
  have h1 : ContinuousOn (fun p : ↥(M.X ×ˢ (Set.univ : Set Z)) × F =>
      M.u t p.1.1.1 p.1.1.2 p.2) (graph M.Γs) :=
    hu.comp ((continuous_subtype_val.comp continuous_fst).fst.prodMk
      ((continuous_subtype_val.comp continuous_fst).snd.prodMk continuous_snd)).continuousOn
      fun p hp => ⟨p.1.2.1, Set.mem_univ _, hA p hp⟩
  have h2 : ContinuousOn (fun p : ↥(M.X ×ˢ (Set.univ : Set Z)) × F =>
      M.cont f p.1.1.1 p.2 p.1.1.2) (graph M.Γs) :=
    hc.comp ((continuous_subtype_val.comp continuous_fst).fst.prodMk
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst).snd)).continuousOn
      fun p hp => ⟨p.1.2.1, hA p hp, Set.mem_univ _⟩
  exact h1.add (continuousOn_const.mul h2)

/-- **Theorem 6.4.1 (Existence)** (Miao, p. 174), for any class `P` of functions for which the
conclusion of Lemma 6.4.1 holds and which contains every `V_t`. Under Assumptions 6.4.4 and
6.4.6, each `V_t` is continuous on `X × Z` (`t ≤ T`) and each `G_t` (`t < T`) is nonempty,
compact-valued and upper hemicontinuous. -/
theorem theorem_6_4_1 (P : (E → Z → ℝ) → Prop) (hE : M.ExpCont P)
    (hP : ∀ t ≤ M.T, P (M.V t)) (h644 : M.Assumption644) (h646 : M.Assumption646) :
    (∀ t ≤ M.T, ContinuousOn (fun p : E × Z => M.V t p.1 p.2) (M.X ×ˢ Set.univ)) ∧
      ∀ t < M.T, ∀ s, (M.Gs t s).Nonempty ∧ IsCompact (M.Gs t s) ∧ IsUHC (M.Gs t) s := by
  have hcpt : ∀ s, IsCompact (M.Γs s) := fun s => (h644.2 s).1
  have hl : ∀ s, IsLHC M.Γs s := fun s => (h644.2 s).2.1
  have hu : ∀ s, IsUHC M.Γs s := fun s => (h644.2 s).2.2
  -- the step: continuity of `V_{t+1}` gives the Theorem of the Maximum at `t`
  have hstep : ∀ t < M.T,
      ContinuousOn (fun p : E × Z => M.V (t + 1) p.1 p.2) (M.X ×ˢ Set.univ) →
      ContinuousOn (M.objS t (M.V (t + 1))) (graph M.Γs) := fun t ht hV =>
    M.continuousOn_objS h644 (h646.1 t ht) (hE _ (hP (t + 1) ht) hV).1
  have hcont : ∀ k ≤ M.T,
      ContinuousOn (fun p : E × Z => M.V (M.T - k) p.1 p.2) (M.X ×ˢ Set.univ) := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.sub_zero, M.V_T_eq]; exact h646.2
    | succ k ih =>
      intro hk
      have ht : M.T - (k + 1) < M.T := by omega
      have he : M.T - (k + 1) + 1 = M.T - k := by omega
      have hV := ih (by omega)
      rw [← he] at hV
      have h36 := theorem_3_6 (hstep _ ht hV) hcpt hl hu
      rw [continuousOn_iff_continuous_domRestrict]
      refine h36.1.congr fun s => ?_
      exact (M.V_eq_maxValue ht s).symm
  have hcont' : ∀ t ≤ M.T,
      ContinuousOn (fun p : E × Z => M.V t p.1 p.2) (M.X ×ˢ Set.univ) := fun t ht => by
    have := hcont (M.T - t) (Nat.sub_le _ _)
    rwa [Nat.sub_sub_self ht] at this
  refine ⟨hcont', fun t ht s => ?_⟩
  rw [M.Gs_eq_argmax ht]
  exact (theorem_3_6 (hstep t ht (hcont' (t + 1) ht)) hcpt hl hu).2 s

/-- **Theorem 6.4.1 (Existence)** (Miao, p. 174), case (ii) of Assumption 6.4.3: if `Z` is
compact and `Q` is Feller, then under Assumptions 6.4.4–6.4.6 every `V_t` is continuous and
every `G_t` is nonempty, compact-valued and u.h.c. -/
theorem theorem_6_4_1_compact [IsMarkovKernel M.Q] (h643 : M.Assumption643ii)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h646 : M.Assumption646) :
    (∀ t ≤ M.T, ContinuousOn (fun p : E × Z => M.V t p.1 p.2) (M.X ×ˢ Set.univ)) ∧
      ∀ t < M.T, ∀ s, (M.Gs t s).Nonempty ∧ IsCompact (M.Gs t s) ∧ IsUHC (M.Gs t) s := by
  have : CompactSpace Z := h643.1
  have : BorelSpace Z := h643.2.1
  exact M.theorem_6_4_1 _ (M.expCont_compact h643.2.2 h645) (fun _ _ => trivial) h644 h646

/-- With bounded rewards, every `V_t` is bounded on `X × Z` (Assumptions 6.4.4–6.4.5). -/
theorem V_bounded [IsMarkovKernel M.Q] (h644 : M.Assumption644)
    (h645X : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) {B : ℝ}
    (hu : ∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B)
    (huT : ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B) :
    ∀ t ≤ M.T, ∃ C, ∀ x ∈ M.X, ∀ z, |M.V t x z| ≤ C := by
  have key : ∀ k ≤ M.T, ∃ C, ∀ x ∈ M.X, ∀ z, |M.V (M.T - k) x z| ≤ C := by
    intro k
    induction k with
    | zero => intro _; exact ⟨B, fun x hx z => by rw [Nat.sub_zero, M.V_T_eq]; exact huT x hx z⟩
    | succ k ih =>
      intro hk
      obtain ⟨C, hC⟩ := ih (by omega)
      have ht : M.T - (k + 1) < M.T := by omega
      have he : M.T - (k + 1) + 1 = M.T - k := by omega
      refine ⟨B + |M.β| * C, fun x hx z => ?_⟩
      rw [M.V_succ_apply ht]
      have hobj : ∀ a ∈ M.Γ x z, |M.obj (M.T - (k + 1)) (M.V (M.T - (k + 1) + 1)) x z a| ≤
          B + |M.β| * C := fun a ha => by
        have haA := h644.1 x hx z ha
        have hcont : |M.cont (M.V (M.T - (k + 1) + 1)) x a z| ≤ C := by
          rw [he]
          exact oc_abs_integral_le fun z' => hC _ (h645X x hx a haA z z') z'
        refine (abs_add_le _ _).trans (add_le_add (hu _ ht x hx z a haA) ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hcont (abs_nonneg _)
      have hne : (M.Γ x z).Nonempty := (h644.2 ⟨(x, z), hx, Set.mem_univ _⟩).2.1.1
      have hS : (M.obj (M.T - (k + 1)) (M.V (M.T - (k + 1) + 1)) x z '' M.Γ x z).Nonempty :=
        hne.image _
      have hbdd : BddAbove (M.obj (M.T - (k + 1)) (M.V (M.T - (k + 1) + 1)) x z '' M.Γ x z) :=
        ⟨B + |M.β| * C, by rintro _ ⟨a, ha, rfl⟩; exact (abs_le.1 (hobj a ha)).2⟩
      obtain ⟨a, ha⟩ := hne
      rw [abs_le]
      constructor
      · exact (abs_le.1 (hobj a ha)).1.trans (le_csSup hbdd ⟨a, ha, rfl⟩)
      · exact csSup_le hS (by rintro _ ⟨b, hb, rfl⟩; exact (abs_le.1 (hobj b hb)).2)
  intro t ht
  have := key (M.T - t) (Nat.sub_le _ _)
  rwa [Nat.sub_sub_self ht] at this

/-- **Theorem 6.4.1 (Existence)** (Miao, p. 174), case (i) of Assumption 6.4.3, corrected: if `Z`
is discrete with all subsets measurable and the rewards are **bounded** on `X × Z × A`, then
under Assumptions 6.4.4–6.4.6 every `V_t` is continuous and every `G_t` is nonempty,
compact-valued and u.h.c. (Without the bound Lemma 6.4.1 fails:
`lemma_6_4_1_countable_counterexample`.) -/
theorem theorem_6_4_1_countable [IsMarkovKernel M.Q] (h643 : Assumption643i Z)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h646 : M.Assumption646) {B : ℝ}
    (hu : ∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B)
    (huT : ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B) :
    (∀ t ≤ M.T, ContinuousOn (fun p : E × Z => M.V t p.1 p.2) (M.X ×ˢ Set.univ)) ∧
      ∀ t < M.T, ∀ s, (M.Gs t s).Nonempty ∧ IsCompact (M.Gs t s) ∧ IsUHC (M.Gs t) s := by
  have : DiscreteTopology Z := h643.2.1
  have : DiscreteMeasurableSpace Z := h643.2.2
  exact M.theorem_6_4_1 _ (M.expCont_countable h645) (M.V_bounded h644 h645.1 hu huT) h644 h646

/-- **Measurable selections** (Miao, p. 175): with actions in `ℝ^m`, under the hypotheses of
`theorem_6_4_1` each `G_t` has a measurable selection (SLP Theorem 7.6), so Theorem 6.3.2
applies. -/
theorem theorem_6_4_1_selection {m : ℕ} [MeasurableSpace E] [BorelSpace (E × Z)]
    (M : OCModel E (Fin m → ℝ) Z) (P : (E → Z → ℝ) → Prop) (hE : M.ExpCont P)
    (hP : ∀ t ≤ M.T, P (M.V t)) (h644 : M.Assumption644) (h646 : M.Assumption646) :
    ∀ t < M.T, ∃ g : ↥(M.X ×ˢ (Set.univ : Set Z)) → Fin m → ℝ,
      Measurable g ∧ ∀ s, g s ∈ M.Gs t s := by
  intro t ht
  have h := (M.theorem_6_4_1 P hE hP h644 h646).2 t ht
  exact theorem_7_6 (fun s => (h s).2.2) fun s => (h s).2.1

/-! ### The standing hypotheses -/

/-- The **standing hypotheses** of §6.4 for a class `P` of functions: Lemma 6.4.1 holds on `P`
(`ExpCont P`), every `V_t` lies in `P`, and Assumptions 6.4.4–6.4.6 hold. They hold in case (ii)
of Assumption 6.4.3 with `P = True` (`Standing.of_compact`) and in case (i) with bounded rewards
and `P` = bounded (`Standing.of_countable`). -/
structure Standing (P : (E → Z → ℝ) → Prop) : Prop where
  expCont : M.ExpCont P
  memP : ∀ t ≤ M.T, P (M.V t)
  a644 : M.Assumption644
  a645 : M.Assumption645
  a646 : M.Assumption646

/-- Case (ii) of Assumption 6.4.3 gives the standing hypotheses with `P = True`. -/
theorem Standing.of_compact [IsMarkovKernel M.Q] (h643 : M.Assumption643ii)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h646 : M.Assumption646) :
    M.Standing fun _ => True := by
  have : CompactSpace Z := h643.1
  have : BorelSpace Z := h643.2.1
  exact ⟨M.expCont_compact h643.2.2 h645, fun _ _ => trivial, h644, h645, h646⟩

/-- Case (i) of Assumption 6.4.3 with bounded rewards gives the standing hypotheses with `P` the
bounded functions. -/
theorem Standing.of_countable [IsMarkovKernel M.Q] (h643 : Assumption643i Z)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h646 : M.Assumption646) {B : ℝ}
    (hu : ∀ t < M.T, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u t x z a| ≤ B)
    (huT : ∀ x ∈ M.X, ∀ z, |M.uT x z| ≤ B) :
    M.Standing fun f => ∃ B, ∀ x ∈ M.X, ∀ z, |f x z| ≤ B := by
  have : DiscreteTopology Z := h643.2.1
  have : DiscreteMeasurableSpace Z := h643.2.2
  exact ⟨M.expCont_countable h645, M.V_bounded h644 h645.1 hu huT, h644, h645, h646⟩

variable {M} {P : (E → Z → ℝ) → Prop}

/-- Under the standing hypotheses every `V_t` is continuous (Theorem 6.4.1). -/
theorem Standing.contV (h : M.Standing P) {t : ℕ} (ht : t ≤ M.T) :
    ContinuousOn (fun p : E × Z => M.V t p.1 p.2) (M.X ×ˢ Set.univ) :=
  (M.theorem_6_4_1 P h.expCont h.memP h.a644 h.a646).1 t ht

/-- The integrands `z′ ↦ V_{t+1}(φ(x, a, z, z′), z′)` are integrable. -/
theorem Standing.integrable (h : M.Standing P) {t : ℕ} (ht : t < M.T) {x : E} (hx : x ∈ M.X)
    {a : F} (ha : a ∈ M.A) (z : Z) :
    Integrable (fun z' => M.V (t + 1) (M.φ x a z z') z') (M.Q z) :=
  (h.expCont _ (h.memP (t + 1) ht) (h.contV ht)).2 x hx a ha z

/-- The objective of (6.29) is continuous on the graph of `Γ`. -/
theorem Standing.continuousOn_objS (h : M.Standing P) {t : ℕ} (ht : t < M.T) :
    ContinuousOn (M.objS t (M.V (t + 1))) (graph M.Γs) :=
  M.continuousOn_objS h.a644 (h.a646.1 t ht) (h.expCont _ (h.memP (t + 1) ht) (h.contV ht)).1

/-- Every feasible action does at most as well as `V_t`: `obj_t(x, z, a) ≤ V_t(x, z)`. -/
theorem Standing.obj_le_V (h : M.Standing P) {t : ℕ} (ht : t < M.T) {x : E} (hx : x ∈ M.X)
    {z : Z} {a : F} (ha : a ∈ M.Γ x z) : M.obj t (M.V (t + 1)) x z a ≤ M.V t x z := by
  have := le_maxValue (h.continuousOn_objS ht) (h.a644.2 ⟨(x, z), hx, Set.mem_univ _⟩).1
    (x := ⟨(x, z), hx, Set.mem_univ _⟩) ha
  rwa [← M.V_eq_maxValue ht] at this

/-- `G_t(x, z)` is nonempty (Theorem 6.4.1). -/
theorem Standing.G_nonempty (h : M.Standing P) {t : ℕ} (ht : t < M.T) {x : E} (hx : x ∈ M.X)
    (z : Z) : (M.G t x z).Nonempty :=
  ((M.theorem_6_4_1 P h.expCont h.memP h.a644 h.a646).2 t ht ⟨(x, z), hx, Set.mem_univ _⟩).1

/-- The selection `g_t(x, z)` lies in `G_t(x, z)`. -/
theorem Standing.g_mem [Nonempty F] (h : M.Standing P) {t : ℕ} (ht : t < M.T) {x : E}
    (hx : x ∈ M.X) (z : Z) : M.g t x z ∈ M.G t x z :=
  M.g_mem (h.G_nonempty ht hx z)

end OCModel

end Miao.InfiniteHorizonDP
