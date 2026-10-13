import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Iterate
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Continuous functions on `[a, b]` and the `L¹` distance

SLP §3.1 works with `C[a, b]`, the continuous functions on a closed interval, under the sup norm
and under `∫ₐᵇ |x(t)| dt`. A function `x ∈ C[a, b]` is a continuous map on the subtype
`Icc a b`; integrals use its continuous extension `ext x` to `ℝ`.

* `integral_pos_of_pos`: a continuous function, nonnegative on `[a, b]` and positive at one point
  of it, has positive integral (`a < b`).
* `l1`, `l1_nonneg`, `l1_eq_zero_iff`, `l1_add_le`, `l1_smul`: the `L¹` size of a continuous
  function is a norm; definiteness uses continuity and `a < b`.
-/

open Set MeasureTheory intervalIntegral

namespace StokeyLucasPrescott.MathematicalPreliminaries

/-- A continuous function on `ℝ`, nonnegative on `[a, b]` and positive at some `t₀ ∈ [a, b]`,
has positive integral over `[a, b]` when `a < b`. -/
theorem integral_pos_of_pos {g : ℝ → ℝ} (hg : Continuous g) {a b t₀ : ℝ} (hab : a < b)
    (hnn : ∀ t ∈ Icc a b, 0 ≤ g t) (ht₀ : t₀ ∈ Icc a b) (hpos : 0 < g t₀) :
    0 < ∫ t in a..b, g t := by
  have hint : IntervalIntegrable g volume a b := hg.intervalIntegrable a b
  have hnn' : 0 ≤ᵐ[volume.restrict (Set.uIoc a b)] g := by
    rw [uIoc_of_le hab.le]
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht =>
      hnn t (Ioc_subset_Icc_self ht))
  rw [integral_pos_iff_support_of_nonneg_ae' hnn' hint]
  refine ⟨hab, ?_⟩
  -- the support is open and contains `t₀`, so it meets `(a, b]` in an interval
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_lt continuous_const hg) t₀ hpos
  set δ := ε / 2
  set c := max a (t₀ - δ)
  set d := min b (t₀ + δ)
  have hδ : 0 < δ := half_pos hε
  have hδε : δ < ε := half_lt_self hε
  have hcd : c < d := max_lt (lt_min hab (by linarith [ht₀.1]))
    (lt_min (by linarith [ht₀.2]) (by linarith))
  have hsub : Ioo c d ⊆ Function.support g ∩ Ioc a b := fun s hs => by
    have h1 : c < s := hs.1
    have h2 : s < d := hs.2
    have ha1 : a < s := lt_of_le_of_lt (le_max_left _ _) h1
    have ha2 : t₀ - δ < s := lt_of_le_of_lt (le_max_right _ _) h1
    have hb1 : s < b := lt_of_lt_of_le h2 (min_le_left _ _)
    have hb2 : s < t₀ + δ := lt_of_lt_of_le h2 (min_le_right _ _)
    refine ⟨?_, ha1, hb1.le⟩
    have : s ∈ Metric.ball t₀ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact (hball this).ne'
  calc (0 : ENNReal) < volume (Ioo c d) := by rw [Real.volume_Ioo]; simpa using hcd
    _ ≤ volume (Function.support g ∩ Ioc a b) := measure_mono hsub

variable {a b : ℝ}

/-- The continuous extension of `x ∈ C[a, b]` to `ℝ`. -/
noncomputable def ext (hab : a ≤ b) (x : C(Icc a b, ℝ)) : ℝ → ℝ := ContinuousMap.IccExtend hab x

theorem continuous_ext (hab : a ≤ b) (x : C(Icc a b, ℝ)) : Continuous (ext hab x) :=
  (ContinuousMap.IccExtend hab x).continuous

theorem ext_of_mem (hab : a ≤ b) (x : C(Icc a b, ℝ)) {t : ℝ} (ht : t ∈ Icc a b) :
    ext hab x t = x ⟨t, ht⟩ := by
  simp [ext, IccExtend_of_mem hab x ht]

theorem ext_add (hab : a ≤ b) (x y : C(Icc a b, ℝ)) (t : ℝ) :
    ext hab (x + y) t = ext hab x t + ext hab y t := by
  simp [ext, IccExtend_apply]

theorem ext_smul (hab : a ≤ b) (r : ℝ) (x : C(Icc a b, ℝ)) (t : ℝ) :
    ext hab (r • x) t = r * ext hab x t := by
  simp [ext, IccExtend_apply]

theorem ext_sub (hab : a ≤ b) (x y : C(Icc a b, ℝ)) (t : ℝ) :
    ext hab (x - y) t = ext hab x t - ext hab y t := by
  simp [ext, IccExtend_apply]

/-- The `L¹` size `∫ₐᵇ |x(t)| dt` of `x ∈ C[a, b]`. -/
noncomputable def l1 (hab : a ≤ b) (x : C(Icc a b, ℝ)) : ℝ := ∫ t in a..b, |ext hab x t|

theorem l1_nonneg (hab : a ≤ b) (x : C(Icc a b, ℝ)) : 0 ≤ l1 hab x :=
  integral_nonneg hab fun _ _ => abs_nonneg _

theorem l1_zero (hab : a ≤ b) : l1 hab 0 = 0 := by
  simp [l1, ext, IccExtend_apply]

/-- **Definiteness needs continuity**: `∫ₐᵇ |x| = 0` forces `x = 0` when `a < b`. -/
theorem l1_eq_zero_iff (hab : a < b) (x : C(Icc a b, ℝ)) : l1 hab.le x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, l1_zero]⟩
  ext ⟨t, ht⟩
  by_contra hne
  have hpos : 0 < |ext hab.le x t| := by
    rw [ext_of_mem hab.le x ht]
    exact abs_pos.2 hne
  have := integral_pos_of_pos (continuous_ext hab.le x).abs hab (fun _ _ => abs_nonneg _) ht hpos
  unfold l1 at h
  linarith

theorem l1_add_le (hab : a ≤ b) (x y : C(Icc a b, ℝ)) :
    l1 hab (x + y) ≤ l1 hab x + l1 hab y := by
  unfold l1
  have hx := ((continuous_ext hab x).abs).intervalIntegrable (μ := volume) a b
  have hy := ((continuous_ext hab y).abs).intervalIntegrable (μ := volume) a b
  rw [← integral_add hx hy]
  refine integral_mono_on hab (((continuous_ext hab (x + y)).abs).intervalIntegrable a b)
    (hx.add hy) fun t _ => ?_
  rw [ext_add]
  exact abs_add_le _ _

theorem l1_smul (hab : a ≤ b) (r : ℝ) (x : C(Icc a b, ℝ)) :
    l1 hab (r • x) = |r| * l1 hab x := by
  unfold l1
  simp_rw [ext_smul, abs_mul]
  exact integral_const_mul _ _

theorem l1_neg (hab : a ≤ b) (x : C(Icc a b, ℝ)) : l1 hab (-x) = l1 hab x := by
  have := l1_smul hab (-1) x
  simpa using this

/-- The `L¹` size is at most `(b − a)` times the sup norm. -/
theorem l1_le_norm (hab : a ≤ b) (x : C(Icc a b, ℝ)) : l1 hab x ≤ (b - a) * ‖x‖ := by
  unfold l1
  have := integral_mono_on hab (((continuous_ext hab x).abs).intervalIntegrable (μ := volume) a b)
    (intervalIntegrable_const (c := ‖x‖)) fun t ht => by
      rw [ext_of_mem hab x ht]
      exact x.norm_coe_le_norm ⟨t, ht⟩
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  exact this

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Metric spaces

SLP §3.1, pp. 44–47: the book's definitions of a metric, convergence, Cauchy sequences and
completeness, stated for an arbitrary distance function `ρ : S → S → ℝ`, with Exercises 3.3 and
3.5.

* `IsMetric`: the four axioms of a metric (p. 44).
* `Converges`, `IsCauchy`, `IsCompleteFor` (pp. 46–47).
* `limit_unique`, `IsCauchy.of_converges`, `IsCauchy.bounded`, `converges_iff_subseq` (Ex 3.5).
* `isMetric_int`, `isMetric_discrete`, `isMetric_sup_strictMono`, `isMetric_l1_strictMono`,
  `isMetric_rat`, `isMetric_comp` (Ex 3.3a–f); the last uses `concave_subadditive`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.MathematicalPreliminaries

/-- A metric in the sense of SLP p. 44. -/
structure IsMetric {S : Type*} (ρ : S → S → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ ρ x y
  eq_zero : ∀ x y, ρ x y = 0 ↔ x = y
  symm : ∀ x y, ρ x y = ρ y x
  triangle : ∀ x y z, ρ x z ≤ ρ x y + ρ y z

variable {S : Type*}

/-- `x_n → l` in the metric `ρ` (SLP (1), p. 46). -/
def Converges (ρ : S → S → ℝ) (x : ℕ → S) (l : S) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ρ (x n) l < ε

/-- `x` satisfies the Cauchy criterion (SLP (2), p. 46). -/
def IsCauchy (ρ : S → S → ℝ) (x : ℕ → S) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ρ (x n) (x m) < ε

/-- `(S, ρ)` is complete: every Cauchy sequence converges (SLP p. 47). -/
def IsCompleteFor (ρ : S → S → ℝ) : Prop := ∀ x : ℕ → S, IsCauchy ρ x → ∃ l, Converges ρ x l

variable {ρ : S → S → ℝ}

theorem IsMetric.self (hρ : IsMetric ρ) (x : S) : ρ x x = 0 := (hρ.eq_zero x x).2 rfl

/-- **Ex 3.5a.** Limits are unique. -/
theorem limit_unique (hρ : IsMetric ρ) {x : ℕ → S} {l l' : S} (h : Converges ρ x l)
    (h' : Converges ρ x l') : l = l' := by
  by_contra hne
  have hpos : 0 < ρ l l' :=
    lt_of_le_of_ne (hρ.nonneg l l') fun h0 => hne ((hρ.eq_zero l l').1 h0.symm)
  obtain ⟨N, hN⟩ := h (ρ l l' / 2) (half_pos hpos)
  obtain ⟨N', hN'⟩ := h' (ρ l l' / 2) (half_pos hpos)
  have h1 := hN (max N N') (le_max_left _ _)
  have h2 := hN' (max N N') (le_max_right _ _)
  have := hρ.triangle l (x (max N N')) l'
  rw [hρ.symm l (x (max N N'))] at this
  linarith

/-- **Ex 3.5b.** A convergent sequence is Cauchy. -/
theorem IsCauchy.of_converges (hρ : IsMetric ρ) {x : ℕ → S} {l : S} (h : Converges ρ x l) :
    IsCauchy ρ x := fun ε hε => by
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn m hm => ?_⟩
  have := hρ.triangle (x n) l (x m)
  rw [hρ.symm l (x m)] at this
  linarith [hN n hn, hN m hm]

/-- **Ex 3.5c.** A Cauchy sequence is bounded. -/
theorem IsCauchy.bounded (hρ : IsMetric ρ) {x : ℕ → S} (h : IsCauchy ρ x) :
    ∃ M, ∀ n, ρ (x n) (x 0) ≤ M := by
  obtain ⟨N, hN⟩ := h 1 one_pos
  refine ⟨(Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun n => ρ (x n) (x 0)) + 1,
    fun n => ?_⟩
  rcases le_or_gt n N with hn | hn
  · have := Finset.le_sup' (fun n => ρ (x n) (x 0)) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
    linarith
  · have h1 := hN n hn.le N le_rfl
    have h2 := Finset.le_sup' (fun n => ρ (x n) (x 0)) (Finset.mem_range.2 (Nat.lt_succ_self N))
    have := hρ.triangle (x n) (x N) (x 0)
    linarith

/-- **Ex 3.5d.** `x_n → l` if and only if every subsequence converges to `l`. -/
theorem converges_iff_subseq {x : ℕ → S} {l : S} :
    Converges ρ x l ↔ ∀ φ : ℕ → ℕ, StrictMono φ → Converges ρ (x ∘ φ) l := by
  refine ⟨fun h φ hφ ε hε => ?_, fun h => h id strictMono_id⟩
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => hN (φ n) (hn.trans (hφ.id_le n))⟩

/-! ### Exercise 3.3 -/

/-- **Ex 3.3a.** The integers with `ρ(x, y) = |x − y|`. -/
theorem isMetric_int : IsMetric fun x y : ℤ => |(x : ℝ) - y| where
  nonneg _ _ := abs_nonneg _
  eq_zero x y := by simp [sub_eq_zero]
  symm _ _ := abs_sub_comm _ _
  triangle _ _ _ := abs_sub_le _ _ _

/-- **Ex 3.3b.** The discrete metric (on the integers, or any set). -/
theorem isMetric_discrete (T : Type*) [DecidableEq T] :
    IsMetric fun x y : T => if x = y then (0 : ℝ) else 1 where
  nonneg x y := by split_ifs <;> norm_num
  eq_zero x y := by split_ifs with h <;> simp [h]
  symm x y := by
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  triangle x y z := by
    by_cases hxz : x = z
    · simp only [hxz, ↓reduceIte]
      split_ifs <;> norm_num
    · simp only [hxz, ↓reduceIte]
      by_cases hxy : x = y
      · subst hxy; simp [hxz]
      · simp only [hxy, ↓reduceIte]
        split_ifs <;> norm_num

/-- **Ex 3.3e.** The rationals with `ρ(x, y) = |x − y|`. -/
theorem isMetric_rat : IsMetric fun x y : ℚ => |(x : ℝ) - y| where
  nonneg _ _ := abs_nonneg _
  eq_zero x y := by simp [sub_eq_zero]
  symm _ _ := abs_sub_comm _ _
  triangle _ _ _ := abs_sub_le _ _ _

variable {a b : ℝ}

/-- The continuous, strictly increasing functions on `[a, b]`. -/
abbrev StrictIncr (a b : ℝ) : Type := {x : C(Icc a b, ℝ) // StrictMono x}

/-- **Ex 3.3c.** Continuous strictly increasing functions with `ρ(x, y) = max |x(t) − y(t)|`. -/
theorem isMetric_sup_strictMono :
    IsMetric fun x y : StrictIncr a b => ‖x.1 - y.1‖ where
  nonneg _ _ := norm_nonneg _
  eq_zero x y := by rw [norm_sub_eq_zero_iff, Subtype.ext_iff]
  symm _ _ := norm_sub_rev _ _
  triangle x y z := by
    have := norm_add_le (x.1 - y.1) (y.1 - z.1)
    rwa [sub_add_sub_cancel] at this

/-- **Ex 3.3d.** Continuous strictly increasing functions with `ρ(x, y) = ∫ₐᵇ |x(t) − y(t)| dt`
(`a < b`; definiteness uses continuity). -/
theorem isMetric_l1_strictMono (hab : a < b) :
    IsMetric fun x y : StrictIncr a b => l1 hab.le (x.1 - y.1) where
  nonneg _ _ := l1_nonneg _ _
  eq_zero x y := by rw [l1_eq_zero_iff hab, sub_eq_zero, Subtype.ext_iff]
  symm x y := by rw [← l1_neg, neg_sub]
  triangle x y z := by
    have := l1_add_le hab.le (x.1 - y.1) (y.1 - z.1)
    rwa [sub_add_sub_cancel] at this

/-- A concave function with `f(0) = 0` is subadditive on `[0, ∞)`. -/
theorem concave_subadditive {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Ici 0) f) (h0 : f 0 = 0) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) : f (s + t) ≤ f s + f t := by
  rcases (add_nonneg hs ht).eq_or_lt with h | h
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simp [hs0, ht0, h0]
  -- `s` and `t` are convex combinations of `0` and `s + t`
  have key : ∀ u, 0 ≤ u → u ≤ s + t → u / (s + t) * f (s + t) ≤ f u := fun u hu hus => by
    have h1 : 0 ≤ u / (s + t) := div_nonneg hu h.le
    have h2 : 0 ≤ 1 - u / (s + t) := by rw [sub_nonneg, div_le_one h]; exact hus
    have := hf.2 (mem_Ici.2 (le_refl (0 : ℝ))) (mem_Ici.2 h.le) h2 h1 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, h0] at this
    rwa [show u / (s + t) * (s + t) = u by field_simp] at this
  have e1 := key s hs (by linarith)
  have e2 := key t ht (by linarith)
  have : s / (s + t) + t / (s + t) = 1 := by field_simp
  calc f (s + t) = s / (s + t) * f (s + t) + t / (s + t) * f (s + t) := by
        rw [← add_mul, this, one_mul]
    _ ≤ f s + f t := add_le_add e1 e2

/-- **Ex 3.3f.** On `ℝ`, `ρ(x, y) = f(|x − y|)` is a metric for `f` strictly increasing and concave
on `[0, ∞)` with `f(0) = 0` (continuity is not needed). -/
theorem isMetric_comp {f : ℝ → ℝ} (hmono : StrictMonoOn f (Ici 0)) (hconc : ConcaveOn ℝ (Ici 0) f)
    (h0 : f 0 = 0) : IsMetric fun x y : ℝ => f |x - y| where
  nonneg x y := by
    rw [← h0]
    exact hmono.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 (abs_nonneg _)) (abs_nonneg _)
  eq_zero x y := by
    constructor
    · intro h
      by_contra hne
      have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hne)
      have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hpos.le) hpos
      linarith
    · rintro rfl
      simp [h0]
  symm x y := by rw [abs_sub_comm]
  triangle x y z := by
    have hmo := hmono.monotoneOn (mem_Ici.2 (abs_nonneg (x - z)))
      (mem_Ici.2 (add_nonneg (abs_nonneg (x - y)) (abs_nonneg (y - z)))) (abs_sub_le x y z)
    exact hmo.trans (concave_subadditive hconc h0 (abs_nonneg _) (abs_nonneg _))

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Vector spaces and normed vector spaces

SLP §3.1, pp. 43–46, Exercises 3.2 and 3.4.

A set of functions or vectors "with the usual operations" is a vector space exactly when it is a
subspace of the ambient space: it contains `0` and is closed under addition and scalar
multiplication (`IsSubspace`).

* Ex 3.2a–d: `isSubspace_univ`, `isSubspace_line`, `isSubspace_continuousOn`; Ex 3.2e–g:
  `not_isSubspace_circle`, `not_isSubspace_int`, `not_isSubspace_nonneg`.
* `IsNorm` (p. 45) and `IsNorm.isMetric` (p. 46).
* Ex 3.4a–f: `isNorm_euclid`, `isNorm_max`, `isNorm_sum`, `isNorm_ellInf`, `isNorm_sup`,
  `isNorm_l1`.
-/

open Set Finset

namespace StokeyLucasPrescott.MathematicalPreliminaries

/-- A subset of a vector space is a vector space under the inherited operations. -/
def IsSubspace {E : Type*} [AddCommGroup E] [Module ℝ E] (V : Set E) : Prop :=
  (0 : E) ∈ V ∧ (∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) ∧ ∀ (r : ℝ), ∀ x ∈ V, r • x ∈ V

/-- **Ex 3.2a, 3.2c.** `ℝ^l` and the space of all real sequences. -/
theorem isSubspace_univ {E : Type*} [AddCommGroup E] [Module ℝ E] : IsSubspace (Set.univ : Set E) :=
  ⟨trivial, fun _ _ _ _ => trivial, fun _ _ _ => trivial⟩

/-- **Ex 3.2b.** The line `{αz : α ∈ ℝ}` through `z ∈ ℝ²`. -/
theorem isSubspace_line (z : ℝ × ℝ) : IsSubspace {x : ℝ × ℝ | ∃ α : ℝ, x = α • z} :=
  ⟨⟨0, by simp⟩, fun _ ⟨α, hx⟩ _ ⟨β, hy⟩ => ⟨α + β, by rw [hx, hy, add_smul]⟩,
    fun r _ ⟨α, hx⟩ => ⟨r * α, by rw [hx, smul_smul]⟩⟩

/-- **Ex 3.2d.** The continuous functions on `[a, b]`. -/
theorem isSubspace_continuousOn (a b : ℝ) :
    IsSubspace {f : ℝ → ℝ | ContinuousOn f (Icc a b)} :=
  ⟨continuousOn_const, fun _ hf _ hg => hf.add hg, fun _ _ hf => continuousOn_const.mul hf⟩

/-- **Ex 3.2e.** The unit circle in `ℝ²` is not a vector space: it does not contain `0`. -/
theorem not_isSubspace_circle : ¬ IsSubspace {x : ℝ × ℝ | x.1 ^ 2 + x.2 ^ 2 = 1} := by
  rintro ⟨h0, -, -⟩
  simp at h0

/-- **Ex 3.2f.** The integers are not a real vector space: `½ · 1 ∉ ℤ`. -/
theorem not_isSubspace_int : ¬ IsSubspace (Set.range (Int.cast : ℤ → ℝ)) := by
  rintro ⟨-, -, hs⟩
  obtain ⟨n, hn⟩ := hs (1 / 2) 1 ⟨1, by simp⟩
  have h1 : (2 : ℝ) * n = 1 := by rw [hn]; norm_num
  have h2 : (2 * n : ℤ) = 1 := by exact_mod_cast h1
  omega

/-- **Ex 3.2g.** The nonnegative functions on `[a, b]` (`a ≤ b`) are not a vector space:
`(−1) · 1` is negative. -/
theorem not_isSubspace_nonneg {a b : ℝ} (hab : a ≤ b) :
    ¬ IsSubspace {f : ℝ → ℝ | ∀ t ∈ Icc a b, 0 ≤ f t} := by
  rintro ⟨-, -, hs⟩
  have := hs (-1) (fun _ => 1) (fun _ _ => zero_le_one) a ⟨le_rfl, hab⟩
  simp at this
  linarith

/-- A norm in the sense of SLP p. 45. -/
structure IsNorm {E : Type*} [AddCommGroup E] [Module ℝ E] (N : E → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ N x
  eq_zero : ∀ x, N x = 0 ↔ x = 0
  smul : ∀ (r : ℝ) x, N (r • x) = |r| * N x
  triangle : ∀ x y, N (x + y) ≤ N x + N y

/-- **A norm gives a metric** `ρ(x, y) = ‖x − y‖` (SLP p. 46). -/
theorem IsNorm.isMetric {E : Type*} [AddCommGroup E] [Module ℝ E] {N : E → ℝ} (hN : IsNorm N) :
    IsMetric fun x y => N (x - y) where
  nonneg _ _ := hN.nonneg _
  eq_zero x y := by rw [hN.eq_zero, sub_eq_zero]
  symm x y := by
    rw [show y - x = (-1 : ℝ) • (x - y) by simp [neg_sub], hN.smul]
    simp
  triangle x y z := by
    have := hN.triangle (x - y) (y - z)
    rwa [sub_add_sub_cancel] at this

/-- A normed space's own norm is a norm in the book's sense. -/
theorem isNorm_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsNorm fun x : E => ‖x‖ where
  nonneg _ := norm_nonneg _
  eq_zero _ := norm_eq_zero
  smul r x := by rw [norm_smul, Real.norm_eq_abs]
  triangle _ _ := norm_add_le _ _

/-- **Ex 3.4a.** The Euclidean norm `‖x‖ = (∑ xᵢ²)^{1/2}` on `ℝ^l`. -/
theorem isNorm_euclid (l : ℕ) : IsNorm fun x : Fin l → ℝ => Real.sqrt (∑ i, x i ^ 2) := by
  have h : ∀ x : Fin l → ℝ,
      Real.sqrt (∑ i, x i ^ 2) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin l))‖ := fun x => by
      rw [EuclideanSpace.norm_eq]
      simp [Real.norm_eq_abs, sq_abs]
  simp_rw [h]
  exact ⟨fun _ => norm_nonneg _, fun x => by
      rw [norm_eq_zero]
      exact ⟨fun h0 => WithLp.toLp_injective 2 (by rw [h0, WithLp.toLp_zero]), fun h0 => by
        rw [h0, WithLp.toLp_zero]⟩,
    fun r x => by rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs],
    fun x y => by rw [WithLp.toLp_add]; exact norm_add_le _ _⟩

/-- **Ex 3.4b.** The max norm `‖x‖ = maxᵢ |xᵢ|` on `ℝ^l`: Mathlib's norm on `Fin l → ℝ` is this
maximum (`abs_le_max_norm`, `max_norm_le`). -/
theorem isNorm_max (l : ℕ) : IsNorm fun x : Fin l → ℝ => ‖x‖ := isNorm_norm

theorem abs_le_max_norm {l : ℕ} (x : Fin l → ℝ) (i : Fin l) : |x i| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]
  exact norm_le_pi_norm x i

theorem max_norm_le {l : ℕ} (x : Fin l → ℝ) {M : ℝ} (hM : 0 ≤ M) (h : ∀ i, |x i| ≤ M) :
    ‖x‖ ≤ M :=
  (pi_norm_le_iff_of_nonneg hM).2 fun i => by rw [Real.norm_eq_abs]; exact h i

/-- **Ex 3.4c.** The sum norm `‖x‖ = ∑ᵢ |xᵢ|` on `ℝ^l`. -/
theorem isNorm_sum (l : ℕ) : IsNorm fun x : Fin l → ℝ => ∑ i, |x i| where
  nonneg _ := sum_nonneg fun _ _ => abs_nonneg _
  eq_zero x := by
    constructor
    · intro h
      funext i
      have := (sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _).1 h i (mem_univ i)
      simpa using this
    · rintro rfl
      simp
  smul r x := by simp [abs_mul, mul_sum]
  triangle x y := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun i _ => abs_add_le _ _

/-- The bounded real sequences, `ℓ∞`. -/
def ellInf : Submodule ℝ (ℕ → ℝ) where
  carrier := {x | BddAbove (Set.range fun k => |x k|)}
  add_mem' {x y} hx hy := by
    obtain ⟨M, hM⟩ := hx
    obtain ⟨M', hM'⟩ := hy
    refine ⟨M + M', ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (abs_add_le _ _).trans (add_le_add (hM ⟨k, rfl⟩) (hM' ⟨k, rfl⟩))
  zero_mem' := ⟨0, by rintro _ ⟨k, rfl⟩; simp⟩
  smul_mem' r x hx := by
    obtain ⟨M, hM⟩ := hx
    refine ⟨|r| * M, ?_⟩
    rintro _ ⟨k, rfl⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM ⟨k, rfl⟩) (abs_nonneg r)

/-- The sup norm `supₖ |xₖ|` on `ℓ∞`. -/
noncomputable def supNorm (x : ellInf) : ℝ := ⨆ k, |(x : ℕ → ℝ) k|

theorem abs_le_supNorm (x : ellInf) (k : ℕ) : |(x : ℕ → ℝ) k| ≤ supNorm x :=
  le_ciSup x.2 k

theorem supNorm_le (x : ellInf) {M : ℝ} (h : ∀ k, |(x : ℕ → ℝ) k| ≤ M) : supNorm x ≤ M :=
  ciSup_le h

/-- **Ex 3.4d.** `ℓ∞` with `‖x‖ = supₖ |xₖ|`. -/
theorem isNorm_ellInf : IsNorm supNorm where
  nonneg x := (abs_nonneg _).trans (abs_le_supNorm x 0)
  eq_zero x := by
    constructor
    · intro h
      ext k
      have := abs_le_supNorm x k
      rw [h] at this
      simpa using abs_nonpos_iff.1 this
    · rintro rfl
      exact le_antisymm (supNorm_le _ fun k => by simp) ((abs_nonneg _).trans (abs_le_supNorm _ 0))
  smul r x := by
    unfold supNorm
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact (Real.mul_iSup_of_nonneg (abs_nonneg r) _).symm
  triangle x y := supNorm_le _ fun k => by
    simp only [Submodule.coe_add, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (abs_le_supNorm x k) (abs_le_supNorm y k))

/-- **Ex 3.4e.** `C[a, b]` with `‖x‖ = max |x(t)|`; Mathlib's norm is this maximum
(`ContinuousMap.norm_coe_le_norm`, `ContinuousMap.norm_le`). -/
theorem isNorm_sup (a b : ℝ) : IsNorm fun x : C(Icc a b, ℝ) => ‖x‖ := isNorm_norm

/-- **Ex 3.4f.** `C[a, b]` with `‖x‖ = ∫ₐᵇ |x(t)| dt`, for `a < b`. -/
theorem isNorm_l1 {a b : ℝ} (hab : a < b) : IsNorm (l1 hab.le) where
  nonneg := l1_nonneg _
  eq_zero := l1_eq_zero_iff hab
  smul := l1_smul _
  triangle := l1_add_le _

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Completeness

SLP §3.1, pp. 46–49: Theorem 3.1 and Exercise 3.6.

* `theorem_3_1`: the bounded continuous functions `C(X)` on a topological space, with the sup
  norm, are complete; the proof follows the book's three steps (pointwise limit, uniform
  convergence, the limit bounded and continuous).
* `isCompleteFor_of_completeSpace`: Mathlib's completeness of a metric space is the book's.
* Ex 3.6a, complete: `isComplete_int`, `isComplete_discrete` (3.3a–b), `isComplete_euclid`,
  `isComplete_max`, `isComplete_sum` (3.4a–c), `isComplete_ellInf` (3.4d), `isComplete_sup`
  (3.4e), `isComplete_sup_monotone` (3.3c with "nondecreasing").
* Ex 3.6a, not complete: `not_isComplete_sup_strictMono` (3.3c), `not_isComplete_l1_strictMono`
  (3.3d), `not_isComplete_rat` (3.3e), `not_isComplete_l1` (3.4f).
* `IsClosedFor`, `isComplete_subset` (Ex 3.6b): a closed subset of a complete space is complete.
-/

open Set Filter Topology Finset BoundedContinuousFunction

namespace StokeyLucasPrescott.MathematicalPreliminaries

/-! ### Theorem 3.1 -/

/-- **Theorem 3.1.** The space of bounded continuous real functions on a topological space, with the
sup norm, is complete: every Cauchy sequence converges. -/
theorem theorem_3_1 {X : Type*} [TopologicalSpace X] (f : ℕ → X →ᵇ ℝ) (hf : CauchySeq f) :
    ∃ g : X →ᵇ ℝ, Tendsto f atTop (𝓝 g) := by
  rw [Metric.cauchySeq_iff] at hf
  -- Step 1: the candidate, the pointwise limit
  have hpt : ∀ x, CauchySeq fun n => f n x := fun x => Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hf ε hε
    exact ⟨N, fun m hm n hn => (dist_coe_le_dist x).trans_lt (hN m hm n hn)⟩
  choose g0 hg0 using fun x => cauchySeq_tendsto_of_complete (hpt x)
  -- Step 2: uniform convergence
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, dist (f n x) (g0 x) ≤ ε := fun ε hε => by
    obtain ⟨N, hN⟩ := hf ε hε
    refine ⟨N, fun n hn x => ?_⟩
    have hlim : Tendsto (fun m => dist (f n x) (f m x)) atTop (𝓝 (dist (f n x) (g0 x))) :=
      tendsto_const_nhds.dist (hg0 x)
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
    exact ((dist_coe_le_dist x).trans (hN n hn m hm).le)
  -- Step 3: the limit is continuous and bounded
  have hcont : Continuous g0 := by
    refine TendstoUniformly.continuous (F := fun n x => f n x) ?_
      (Frequently.of_forall (f := atTop) fun n => (f n).continuous)
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun n hn x => ?_⟩
    rw [dist_comm]
    exact (hN n hn x).trans_lt (half_lt_self hε)
  obtain ⟨N₁, hN₁⟩ := hunif 1 one_pos
  have hbdd : ∀ x, ‖g0 x‖ ≤ ‖f N₁‖ + 1 := fun x => by
    have h1 := hN₁ N₁ le_rfl x
    have h2 := (f N₁).norm_coe_le_norm x
    rw [Real.dist_eq] at h1
    rw [Real.norm_eq_abs] at h2 ⊢
    have := abs_sub_abs_le_abs_sub (g0 x) (f N₁ x)
    rw [abs_sub_comm] at h1
    linarith
  refine ⟨ofNormedAddCommGroup g0 hcont _ hbdd, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  exact (dist_le (half_pos hε).le).2 fun x => hN n hn x

/-- Mathlib's completeness of a metric space is completeness in the book's sense. -/
theorem isCompleteFor_of_completeSpace {E : Type*} [MetricSpace E] [CompleteSpace E] :
    IsCompleteFor (dist : E → E → ℝ) := fun x hx => by
  have hc : CauchySeq x := Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hx ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn⟩
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨l, fun ε hε => (Metric.tendsto_atTop.1 hl ε hε)⟩

/-! ### Exercise 3.6a: complete spaces -/

/-- An integer- or discrete-valued Cauchy sequence is eventually constant. -/
theorem isComplete_of_eventually_const {S : Type*} {ρ : S → S → ℝ} (hρ : IsMetric ρ)
    (hsep : ∀ x y, ρ x y < 1 / 2 → x = y) : IsCompleteFor ρ := fun x hx => by
  obtain ⟨N, hN⟩ := hx (1 / 2) (by norm_num)
  refine ⟨x N, fun ε hε => ⟨N, fun n hn => ?_⟩⟩
  rw [hsep _ _ (hN n hn N le_rfl), hρ.self]
  exact hε

/-- **Ex 3.6a (Ex 3.3a).** The integers are complete. -/
theorem isComplete_int : IsCompleteFor fun x y : ℤ => |(x : ℝ) - y| :=
  isComplete_of_eventually_const isMetric_int fun x y h => by
    by_contra hne
    have : (1 : ℝ) ≤ |(x : ℝ) - y| := by
      have h1 : (1 : ℤ) ≤ |x - y| := Int.one_le_abs (sub_ne_zero.2 hne)
      exact_mod_cast h1
    linarith

/-- **Ex 3.6a (Ex 3.3b).** A discrete metric space is complete. -/
theorem isComplete_discrete (T : Type*) [DecidableEq T] :
    IsCompleteFor fun x y : T => if x = y then (0 : ℝ) else 1 :=
  isComplete_of_eventually_const (isMetric_discrete T) fun x y h => by
    by_contra hne
    simp [hne] at h
    linarith

/-- A norm on `ℝ^l` bounded above and below by multiples of the max norm is complete. -/
theorem isComplete_of_equiv_max {l : ℕ} {N : (Fin l → ℝ) → ℝ} {c C : ℝ} (hc : 0 < c)
    (hlow : ∀ x, c * ‖x‖ ≤ N x) (hup : ∀ x, N x ≤ C * ‖x‖) :
    IsCompleteFor fun x y => N (x - y) := fun x hx => by
  have hcs : CauchySeq x := Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨M, hM⟩ := hx (c * ε) (mul_pos hc hε)
    refine ⟨M, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have := (hlow (x m - x n)).trans_lt (hM m hm n hn)
    exact lt_of_mul_lt_mul_left this hc.le
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨L, fun ε hε => ?_⟩
  have hC : 0 < |C| + 1 := by positivity
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hL (ε / (|C| + 1)) (div_pos hε hC)
  refine ⟨M, fun n hn => ?_⟩
  have h1 := hM n hn
  rw [dist_eq_norm] at h1
  calc N (x n - L) ≤ C * ‖x n - L‖ := hup _
    _ ≤ (|C| + 1) * ‖x n - L‖ := mul_le_mul_of_nonneg_right (by linarith [le_abs_self C])
          (norm_nonneg _)
    _ < (|C| + 1) * (ε / (|C| + 1)) := mul_lt_mul_of_pos_left h1 hC
    _ = ε := by field_simp

theorem sum_abs_le_card_mul_max {l : ℕ} (x : Fin l → ℝ) : ∑ i, |x i| ≤ l * ‖x‖ := by
  calc ∑ i, |x i| ≤ ∑ _i : Fin l, ‖x‖ := sum_le_sum fun i _ => abs_le_max_norm x i
    _ = l * ‖x‖ := by simp

theorem max_le_sum_abs {l : ℕ} (x : Fin l → ℝ) : ‖x‖ ≤ ∑ i, |x i| :=
  max_norm_le x (sum_nonneg fun _ _ => abs_nonneg _) fun i =>
    single_le_sum (f := fun i => |x i|) (fun _ _ => abs_nonneg _) (mem_univ i)

/-- **Ex 3.6a (Ex 3.4c).** `ℝ^l` with the sum norm is complete. -/
theorem isComplete_sum (l : ℕ) : IsCompleteFor fun x y : Fin l → ℝ => ∑ i, |(x - y) i| :=
  isComplete_of_equiv_max one_pos (fun x => by rw [one_mul]; exact max_le_sum_abs x)
    sum_abs_le_card_mul_max

/-- **Ex 3.6a (Ex 3.4b).** `ℝ^l` with the max norm is complete. -/
theorem isComplete_max (l : ℕ) : IsCompleteFor fun x y : Fin l → ℝ => ‖x - y‖ :=
  isComplete_of_equiv_max one_pos (fun x => by rw [one_mul]) (fun x => by rw [one_mul])

/-- **Ex 3.6a (Ex 3.4a).** `ℝ^l` with the Euclidean norm is complete. -/
theorem isComplete_euclid (l : ℕ) :
    IsCompleteFor fun x y : Fin l → ℝ => Real.sqrt (∑ i, (x - y) i ^ 2) := by
  refine isComplete_of_equiv_max (N := fun x : Fin l → ℝ => Real.sqrt (∑ i, x i ^ 2)) (C := l)
    one_pos (fun x => ?_) (fun x => ?_)
  · rw [one_mul]
    refine max_norm_le x (Real.sqrt_nonneg _) fun i => ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (single_le_sum (f := fun i => x i ^ 2) (fun _ _ => sq_nonneg _)
      (mem_univ i))
  · refine le_trans ?_ (sum_abs_le_card_mul_max x)
    rw [Real.sqrt_le_left (sum_nonneg fun _ _ => abs_nonneg _)]
    calc ∑ i, x i ^ 2 = ∑ i, |x i| ^ 2 := by simp
      _ ≤ (∑ i, |x i|) ^ 2 := sum_sq_le_sq_sum_of_nonneg fun _ _ => abs_nonneg _

/-- **Ex 3.6a (Ex 3.4d).** `ℓ∞` is complete. -/
theorem isComplete_ellInf : IsCompleteFor fun x y : ellInf => supNorm (x - y) := fun x hx => by
  -- pointwise limits
  have hpt : ∀ k, CauchySeq fun n => (x n : ℕ → ℝ) k := fun k =>
    Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hx ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    exact (abs_le_supNorm (x m - x n) k).trans_lt (hN m hm n hn)
  choose L hL using fun k => cauchySeq_tendsto_of_complete (hpt k)
  -- uniform convergence
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k, |(x n : ℕ → ℝ) k - L k| ≤ ε := fun ε hε => by
    obtain ⟨N, hN⟩ := hx ε hε
    refine ⟨N, fun n hn k => le_of_tendsto ((tendsto_const_nhds.sub (hL k)).abs)
      (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)⟩
    exact (abs_le_supNorm (x n - x m) k).trans (hN n hn m hm).le
  -- the limit is bounded
  obtain ⟨N₁, hN₁⟩ := hunif 1 one_pos
  have hLb : L ∈ ellInf := ⟨supNorm (x N₁) + 1, by
    rintro _ ⟨k, rfl⟩
    have h1 := hN₁ N₁ le_rfl k
    have h2 := abs_le_supNorm (x N₁) k
    have := abs_sub_abs_le_abs_sub (L k) ((x N₁ : ℕ → ℝ) k)
    rw [abs_sub_comm] at h1
    simp only
    linarith⟩
  refine ⟨⟨L, hLb⟩, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  exact ⟨N, fun n hn => (supNorm_le _ fun k => hN n hn k).trans_lt (half_lt_self hε)⟩

/-- **Ex 3.6a (Ex 3.4e).** `C[a, b]` with the sup norm is complete. -/
theorem isComplete_sup (a b : ℝ) : IsCompleteFor fun x y : C(Icc a b, ℝ) => ‖x - y‖ := by
  have h : (fun x y : C(Icc a b, ℝ) => ‖x - y‖) = dist := by
    funext x y
    rw [dist_eq_norm]
  rw [h]
  exact isCompleteFor_of_completeSpace

/-! ### Exercise 3.6b -/

/-- A subset is closed when it contains the limits of its convergent sequences. -/
def IsClosedFor {S : Type*} (ρ : S → S → ℝ) (V : Set S) : Prop :=
  ∀ (x : ℕ → S) (l : S), (∀ n, x n ∈ V) → Converges ρ x l → l ∈ V

/-- **Ex 3.6b.** A closed subset of a complete metric space is complete. -/
theorem isComplete_subset {S : Type*} {ρ : S → S → ℝ} (hc : IsCompleteFor ρ) {V : Set S}
    (hV : IsClosedFor ρ V) : IsCompleteFor fun x y : V => ρ x y := fun x hx => by
  obtain ⟨l, hl⟩ := hc (fun n => x n) hx
  exact ⟨⟨l, hV _ l (fun n => (x n).2) hl⟩, hl⟩

/-- **Ex 3.6a (Ex 3.3c with "nondecreasing").** The continuous nondecreasing functions on `[a, b]`
with the sup metric are complete. -/
theorem isComplete_sup_monotone (a b : ℝ) :
    IsCompleteFor fun x y : {x : C(Icc a b, ℝ) // Monotone x} => ‖x.1 - y.1‖ := by
  refine isComplete_subset (isComplete_sup a b) fun x l hx hl s t hst => ?_
  have hpt : ∀ u, Tendsto (fun n => x n u) atTop (𝓝 (l u)) := fun u => by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hl ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have := (x n - l).norm_coe_le_norm u
    simp only [ContinuousMap.sub_apply] at this
    exact this.trans_lt (hN n hn)
  exact le_of_tendsto_of_tendsto (hpt s) (hpt t) (Eventually.of_forall fun n => hx n hst)

/-! ### Exercise 3.6a: spaces that are not complete -/

variable {a b : ℝ}

/-- The ramps `x_n(t) = (t − a)/(n + 1)`: strictly increasing, shrinking to `0`. -/
noncomputable def ramp (a b : ℝ) (n : ℕ) : C(Icc a b, ℝ) :=
  ⟨fun t => ((t : ℝ) - a) / (n + 1), by fun_prop⟩

theorem ramp_strictMono (n : ℕ) : StrictMono (ramp a b n) := fun s t hst => by
  simp only [ramp, ContinuousMap.coe_mk]
  have : (s : ℝ) < t := hst
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

theorem norm_ramp_le (hab : a ≤ b) (n : ℕ) : ‖ramp a b n‖ ≤ (b - a) / (n + 1) := by
  have : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  refine (ContinuousMap.norm_le_of_nonempty _).2 fun t => ?_
  simp only [ramp, ContinuousMap.coe_mk, Real.norm_eq_abs]
  rw [abs_of_nonneg (div_nonneg (by linarith [t.2.1]) (by positivity))]
  exact div_le_div_of_nonneg_right (by linarith [t.2.2]) (by positivity)

theorem norm_ramp_tendsto (hab : a ≤ b) : Tendsto (fun n => ‖ramp a b n‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => norm_nonneg _) (norm_ramp_le hab) ?_
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a)
  rw [mul_zero] at h
  exact h.congr fun n => by rw [mul_one_div]

/-- A sequence whose sizes tend to `0` is Cauchy for any norm-like `N`. -/
theorem isCauchy_of_tendsto_zero {E : Type*} [AddCommGroup E] [Module ℝ E] {N : E → ℝ}
    (hN : IsNorm N) {x : ℕ → E} (hx : Tendsto (fun n => N (x n)) atTop (𝓝 0)) :
    IsCauchy (fun u v => N (u - v)) x := fun ε hε => by
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hx (ε / 2) (half_pos hε)
  refine ⟨M, fun n hn m hm => ?_⟩
  have h1 := hM n hn
  have h2 := hM m hm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hN.nonneg _)] at h1 h2
  have := hN.triangle (x n) (-x m)
  rw [← sub_eq_add_neg, show N (-x m) = N (x m) by
    rw [show -x m = (-1 : ℝ) • x m by simp, hN.smul]; simp] at this
  linarith

/-- **Ex 3.6a (Ex 3.3c).** The continuous strictly increasing functions with the sup metric are not
complete (`a < b`). -/
theorem not_isComplete_sup_strictMono (hab : a < b) :
    ¬ IsCompleteFor fun x y : StrictIncr a b => ‖x.1 - y.1‖ := by
  intro hc
  set x : ℕ → StrictIncr a b := fun n => ⟨ramp a b n, ramp_strictMono n⟩
  obtain ⟨l, hl⟩ := hc x (isCauchy_of_tendsto_zero (isNorm_sup a b) (norm_ramp_tendsto hab.le))
  -- the limit is `0`, which is not strictly increasing
  have hl0 : l.1 = 0 := by
    rw [← norm_eq_zero]
    refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
    obtain ⟨N₁, hN₁⟩ := hl (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (norm_ramp_tendsto hab.le) (ε / 2) (half_pos hε)
    have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
    have h2 := hN₂ (max N₁ N₂) (le_max_right _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h2
    have := norm_sub_le (x (max N₁ N₂)).1 ((x (max N₁ N₂)).1 - l.1)
    rw [sub_sub_cancel] at this
    linarith
  have := l.2 (show (⟨a, le_rfl, hab.le⟩ : Icc a b) < ⟨b, hab.le, le_rfl⟩ from hab)
  rw [hl0] at this
  simp at this

/-- **Ex 3.6a (Ex 3.3d).** The continuous strictly increasing functions with the `L¹` metric are not
complete (`a < b`). -/
theorem not_isComplete_l1_strictMono (hab : a < b) :
    ¬ IsCompleteFor fun x y : StrictIncr a b => l1 hab.le (x.1 - y.1) := by
  intro hc
  set x : ℕ → StrictIncr a b := fun n => ⟨ramp a b n, ramp_strictMono n⟩
  have hl1 : Tendsto (fun n => l1 hab.le (ramp a b n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => l1_nonneg _ _) (fun n => l1_le_norm hab.le _) ?_
    simpa using (norm_ramp_tendsto hab.le).const_mul (b - a)
  obtain ⟨l, hl⟩ := hc x (isCauchy_of_tendsto_zero (isNorm_l1 hab) hl1)
  have hl0 : l.1 = 0 := by
    rw [← l1_eq_zero_iff hab]
    refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (l1_nonneg _ _)
    obtain ⟨N₁, hN₁⟩ := hl (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hl1 (ε / 2) (half_pos hε)
    have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
    have h2 := hN₂ (max N₁ N₂) (le_max_right _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (l1_nonneg _ _)] at h2
    have := l1_add_le hab.le (-(x (max N₁ N₂)).1) ((x (max N₁ N₂)).1 - l.1)
    rw [show -(x (max N₁ N₂)).1 + ((x (max N₁ N₂)).1 - l.1) = -l.1 by abel, l1_neg] at this
    have h4 : l1 hab.le (-(x (max N₁ N₂)).1) = l1 hab.le (ramp a b (max N₁ N₂)) := l1_neg _ _
    simp only at h1
    linarith
  have := l.2 (show (⟨a, le_rfl, hab.le⟩ : Icc a b) < ⟨b, hab.le, le_rfl⟩ from hab)
  rw [hl0] at this
  simp at this

/-- **Ex 3.6a (Ex 3.3e).** The rationals are not complete: rational approximations of `√2` form a
Cauchy sequence with no rational limit. -/
theorem not_isComplete_rat : ¬ IsCompleteFor fun x y : ℚ => |(x : ℝ) - y| := by
  intro hc
  have hq : ∀ n : ℕ, ∃ q : ℚ, |(q : ℝ) - Real.sqrt 2| < 1 / (n + 1) := fun n => by
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show Real.sqrt 2 < Real.sqrt 2 + 1 / (n + 1) by
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith)
    refine ⟨q, ?_⟩
    rw [abs_of_pos (by linarith)]
    linarith
  choose q hq using hq
  have hlim : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (Real.sqrt 2)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact (hq n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hcauchy : IsCauchy (fun x y : ℚ => |(x : ℝ) - y|) q := fun ε hε => by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
    exact ⟨N, fun n hn m hm => by simpa [Real.dist_eq] using hN n hn m hm⟩
  obtain ⟨r, hr⟩ := hc q hcauchy
  have hlim' : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (r : ℝ)) :=
    Metric.tendsto_atTop.2 fun ε hε => by
      obtain ⟨N, hN⟩ := hr ε hε
      exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact hN n hn⟩
  have := tendsto_nhds_unique hlim hlim'
  exact irrational_sqrt_two ⟨r, this.symm⟩

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# `C[a, b]` with the `L¹` norm is not complete

SLP Exercise 3.6a (for Exercise 3.4f), p. 47.

The ramps `s_n(t) = min{1, max{0, (n + 1)(t − m)}}`, `m = (a + b)/2`, increase with `n`, so their
`L¹` distances are differences of the increasing, bounded integrals `∫ s_n`: the sequence is
Cauchy (`isCauchy_stepRamp`). A continuous `L¹` limit `g` would vanish on `[a, m)`
(`limit_eq_zero_left`) and equal `1` on `(m, b]` (`limit_eq_one_right`), which continuity at `m`
forbids (`not_isComplete_l1`).
-/

open Set Filter Topology MeasureTheory intervalIntegral

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {a b : ℝ}

/-- A lower bound for an `L¹` integral from a subinterval where `|h| ≥ η`. -/
theorem integral_abs_ge {h : ℝ → ℝ} (hh : Continuous h) {c d η : ℝ} (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hη : ∀ t ∈ Icc c d, η ≤ |h t|) : (d - c) * η ≤ ∫ t in a..b, |h t| := by
  have hab : a ≤ b := hac.trans (hcd.trans hdb)
  have h1 : ∫ t in c..d, |h t| ≤ ∫ t in a..b, |h t| :=
    integral_mono_interval hac hcd hdb
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun _ _ => abs_nonneg _))
      (hh.abs.intervalIntegrable a b)
  have h2 : ∫ t in c..d, η ≤ ∫ t in c..d, |h t| :=
    integral_mono_on hcd intervalIntegrable_const (hh.abs.intervalIntegrable c d) hη
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  linarith

/-- The ramp `s_n(t) = min{1, max{0, (n + 1)(t − m)}}`. -/
noncomputable def stepRamp (a b : ℝ) (n : ℕ) : C(Icc a b, ℝ) :=
  ⟨fun t => min 1 (max 0 ((n + 1) * ((t : ℝ) - (a + b) / 2))), by fun_prop⟩

theorem stepRamp_apply (n : ℕ) (t : Icc a b) :
    stepRamp a b n t = min 1 (max 0 ((n + 1) * ((t : ℝ) - (a + b) / 2))) := rfl

theorem stepRamp_nonneg (n : ℕ) (t : Icc a b) : 0 ≤ stepRamp a b n t := by
  rw [stepRamp_apply]
  exact le_min zero_le_one (le_max_left _ _)

theorem stepRamp_le_one (n : ℕ) (t : Icc a b) : stepRamp a b n t ≤ 1 := by
  rw [stepRamp_apply]
  exact min_le_left _ _

theorem stepRamp_mono {n k : ℕ} (hnk : n ≤ k) (t : Icc a b) :
    stepRamp a b n t ≤ stepRamp a b k t := by
  rw [stepRamp_apply, stepRamp_apply]
  refine min_le_min le_rfl ?_
  have hk : (n : ℝ) ≤ k := by exact_mod_cast hnk
  rcases le_total ((t : ℝ) - (a + b) / 2) 0 with h | h
  · rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by positivity) h)]
    exact le_max_left _ _
  · exact max_le_max le_rfl (by nlinarith)

theorem stepRamp_left (n : ℕ) (t : Icc a b) (ht : (t : ℝ) ≤ (a + b) / 2) :
    stepRamp a b n t = 0 := by
  rw [stepRamp_apply, max_eq_left (by nlinarith : (n + 1 : ℝ) * ((t : ℝ) - (a + b) / 2) ≤ 0)]
  exact min_eq_right zero_le_one

theorem stepRamp_right (n : ℕ) (t : Icc a b) (ht : (a + b) / 2 + 1 / (n + 1) ≤ t) :
    stepRamp a b n t = 1 := by
  rw [stepRamp_apply]
  have hn : (0 : ℝ) < n + 1 := by positivity
  have : 1 ≤ (n + 1 : ℝ) * ((t : ℝ) - (a + b) / 2) := by
    rw [← div_le_iff₀' hn]
    linarith
  rw [max_eq_right (by linarith), min_eq_left this]

/-- The integrals `∫ₐᵇ s_n`. -/
noncomputable def rampIntegral (hab : a ≤ b) (n : ℕ) : ℝ := ∫ t in a..b, ext hab (stepRamp a b n) t

theorem ext_stepRamp_mono (hab : a ≤ b) {n k : ℕ} (hnk : n ≤ k) (t : ℝ) :
    ext hab (stepRamp a b n) t ≤ ext hab (stepRamp a b k) t := by
  simp only [ext, ContinuousMap.coe_IccExtend, IccExtend_apply]
  exact stepRamp_mono hnk _

/-- For `n ≤ k`, the `L¹` distance is `∫ s_k − ∫ s_n`. -/
theorem l1_stepRamp_sub (hab : a ≤ b) {n k : ℕ} (hnk : n ≤ k) :
    l1 hab (stepRamp a b k - stepRamp a b n) = rampIntegral hab k - rampIntegral hab n := by
  unfold l1 rampIntegral
  rw [← integral_sub ((continuous_ext hab _).intervalIntegrable a b)
    ((continuous_ext hab _).intervalIntegrable a b)]
  refine integral_congr fun t _ => ?_
  rw [ext_sub, abs_of_nonneg (sub_nonneg.2 (ext_stepRamp_mono hab hnk t))]

theorem rampIntegral_mono (hab : a ≤ b) : Monotone (rampIntegral (a := a) (b := b) hab) :=
  fun n k hnk => by
    have := l1_nonneg hab (stepRamp a b k - stepRamp a b n)
    rw [l1_stepRamp_sub hab hnk] at this
    linarith

theorem rampIntegral_le (hab : a ≤ b) (n : ℕ) : rampIntegral hab n ≤ b - a := by
  unfold rampIntegral
  have := integral_mono_on hab ((continuous_ext hab (stepRamp a b n)).intervalIntegrable a b)
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun t ht => by
      rw [ext_of_mem hab _ ht]
      exact stepRamp_le_one n _
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
  exact this

/-- **The ramps form an `L¹`-Cauchy sequence.** -/
theorem isCauchy_stepRamp (hab : a ≤ b) :
    IsCauchy (fun x y : C(Icc a b, ℝ) => l1 hab (x - y)) (stepRamp a b) := fun ε hε => by
  have hbdd : BddAbove (range (rampIntegral (a := a) (b := b) hab)) :=
    ⟨b - a, by rintro _ ⟨n, rfl⟩; exact rampIntegral_le hab n⟩
  have hlim := tendsto_atTop_ciSup (rampIntegral_mono hab) hbdd
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
  refine ⟨N, fun n hn k hk => ?_⟩
  have hd := hN n hn k hk
  rw [Real.dist_eq] at hd
  change l1 hab (stepRamp a b n - stepRamp a b k) < ε
  rcases le_total k n with h | h
  · rw [l1_stepRamp_sub hab h]
    exact (le_abs_self _).trans_lt hd
  · rw [show stepRamp a b n - stepRamp a b k = -(stepRamp a b k - stepRamp a b n) by abel,
      l1_neg, l1_stepRamp_sub hab h]
    rw [abs_sub_comm] at hd
    exact (le_abs_self _).trans_lt hd

/-- Near a point where a continuous function differs from `c`, it stays away from `c`. -/
theorem away_of_ne {h : ℝ → ℝ} (hh : Continuous h) {t₀ c : ℝ} (hne : h t₀ ≠ c) :
    ∃ δ > 0, ∀ t, |t - t₀| < δ → |h t₀ - c| / 2 ≤ |h t - c| := by
  have hpos : 0 < |h t₀ - c| / 2 := half_pos (abs_pos.2 (sub_ne_zero.2 hne))
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hh t₀ _ hpos
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have h1 := hball t (by rw [Real.dist_eq]; exact ht)
  rw [Real.dist_eq] at h1
  have := abs_sub_abs_le_abs_sub (h t₀ - c) (h t - c)
  rw [show h t₀ - c - (h t - c) = -(h t - h t₀) by ring, abs_neg] at this
  linarith

/-- The `L¹` limit of the ramps vanishes on `[a, m)`. -/
theorem limit_eq_zero_left (hab : a < b) {g : C(Icc a b, ℝ)}
    (hg : Converges (fun x y : C(Icc a b, ℝ) => l1 hab.le (x - y)) (stepRamp a b) g)
    {t₀ : ℝ} (ht₀a : a ≤ t₀) (ht₀m : t₀ < (a + b) / 2) : ext hab.le g t₀ = 0 := by
  by_contra hne
  obtain ⟨δ, hδ, hnear⟩ := away_of_ne (continuous_ext hab.le g) hne
  set η := |ext hab.le g t₀ - 0| / 2
  have hη : 0 < η := half_pos (abs_pos.2 (by simpa using hne))
  set d := min (t₀ + δ / 2) ((t₀ + (a + b) / 2) / 2)
  have hd : t₀ < d := lt_min (by linarith) (by linarith)
  have hdm : d ≤ (a + b) / 2 := (min_le_right _ _).trans (by linarith)
  have hd1 : d ≤ t₀ + δ / 2 := min_le_left _ _
  obtain ⟨N, hN⟩ := hg ((d - t₀) * η) (mul_pos (sub_pos.2 hd) hη)
  have hlow := integral_abs_ge (h := ext hab.le (stepRamp a b N - g))
    (continuous_ext hab.le _) ht₀a hd.le (hdm.trans (by linarith : (a + b) / 2 ≤ b)) fun t ht => by
      have ht' : t ∈ Icc a b :=
        ⟨ht₀a.trans ht.1, ht.2.trans (hdm.trans (by linarith : (a + b) / 2 ≤ b))⟩
      rw [ext_sub, ext_of_mem hab.le (stepRamp a b N) ht', stepRamp_left N _ (ht.2.trans hdm),
        zero_sub, abs_neg]
      have := hnear t (by
        rw [abs_lt]
        constructor <;> linarith [ht.1, ht.2])
      simpa [η] using this
  have := hN N le_rfl
  have key : (d - t₀) * η ≤ ∫ t in a..b, |ext hab.le (stepRamp a b N - g) t| := by
    convert hlow using 2
    simp [η]
  simp only [l1] at this
  linarith

/-- The `L¹` limit of the ramps equals `1` on `(m, b]`. -/
theorem limit_eq_one_right (hab : a < b) {g : C(Icc a b, ℝ)}
    (hg : Converges (fun x y : C(Icc a b, ℝ) => l1 hab.le (x - y)) (stepRamp a b) g)
    {t₀ : ℝ} (ht₀m : (a + b) / 2 < t₀) (ht₀b : t₀ ≤ b) : ext hab.le g t₀ = 1 := by
  by_contra hne
  obtain ⟨δ, hδ, hnear⟩ := away_of_ne (continuous_ext hab.le g) hne
  set η := |ext hab.le g t₀ - 1| / 2
  have hη : 0 < η := half_pos (abs_pos.2 (sub_ne_zero.2 hne))
  set c := max (t₀ - δ / 2) (((a + b) / 2 + t₀) / 2)
  have hc : c < t₀ := max_lt (by linarith) (by linarith)
  have hcm : (a + b) / 2 < c := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hc1 : t₀ - δ / 2 ≤ c := le_max_left _ _
  -- far enough along, the ramp is `1` on `[c, t₀]`
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1 / (c - (a + b) / 2))
  have hramp : (a + b) / 2 + 1 / (N₁ + 1) ≤ c := by
    have hpos : 0 < c - (a + b) / 2 := sub_pos.2 hcm
    have : 1 / ((N₁ : ℝ) + 1) ≤ c - (a + b) / 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hN₁
      nlinarith
    linarith
  obtain ⟨N₂, hN₂⟩ := hg ((t₀ - c) * η) (mul_pos (sub_pos.2 hc) hη)
  set N := max N₁ N₂
  have hN1 : (a + b) / 2 + 1 / (N + 1) ≤ c := by
    refine le_trans ?_ hramp
    have : (N₁ : ℝ) ≤ N := by exact_mod_cast le_max_left N₁ N₂
    have : 1 / ((N : ℝ) + 1) ≤ 1 / (N₁ + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hca : a ≤ c := by linarith
  have hlow := integral_abs_ge (h := ext hab.le (stepRamp a b N - g))
    (continuous_ext hab.le _) hca hc.le ht₀b fun t ht => by
      have ht' : t ∈ Icc a b := ⟨hca.trans ht.1, ht.2.trans ht₀b⟩
      rw [ext_sub, ext_of_mem hab.le (stepRamp a b N) ht', stepRamp_right N _ (hN1.trans ht.1)]
      have := hnear t (by
        rw [abs_lt]
        constructor <;> linarith [ht.1, ht.2])
      rw [abs_sub_comm]
      simpa [η] using this
  have := hN₂ N (le_max_right _ _)
  have key : (t₀ - c) * η ≤ ∫ t in a..b, |ext hab.le (stepRamp a b N - g) t| := hlow
  simp only [l1] at this
  linarith

/-- **Ex 3.6a (Ex 3.4f).** `C[a, b]` with `‖x‖ = ∫ₐᵇ |x(t)| dt` is not complete (`a < b`). -/
theorem not_isComplete_l1 (hab : a < b) :
    ¬ IsCompleteFor fun x y : C(Icc a b, ℝ) => l1 hab.le (x - y) := by
  intro hc
  obtain ⟨g, hg⟩ := hc _ (isCauchy_stepRamp hab.le)
  set m := (a + b) / 2 with hm
  have hcont := (continuous_ext hab.le g).tendsto m
  -- from the left the limit is `0`, from the right `1`
  have hleft : Tendsto (fun k : ℕ => m - (m - a) / (k + 2)) atTop (𝓝 m) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).const_mul
      (m - a)
    have h2 := tendsto_const_nhds (x := m) |>.sub this
    simp only [mul_zero, sub_zero] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hright : Tendsto (fun k : ℕ => m + (b - m) / (k + 2)) atTop (𝓝 m) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).const_mul
      (b - m)
    have h2 := tendsto_const_nhds (x := m) |>.add this
    simp only [mul_zero, add_zero] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have h0 : ext hab.le g m = 0 := by
    refine tendsto_nhds_unique (hcont.comp hleft) (tendsto_const_nhds.congr fun k => ?_)
    have hk : (0 : ℝ) < (m - a) / (k + 2) := div_pos (by linarith) (by positivity)
    have hk2 : (m - a) / (k + 2) ≤ m - a := div_le_self (by linarith) (by linarith)
    simp only [Function.comp_apply]
    exact (limit_eq_zero_left hab hg (by linarith) (by linarith)).symm
  have h1 : ext hab.le g m = 1 := by
    refine tendsto_nhds_unique (hcont.comp hright) (tendsto_const_nhds.congr fun k => ?_)
    have hk : (0 : ℝ) < (b - m) / (k + 2) := div_pos (by linarith) (by positivity)
    have hk2 : (b - m) / (k + 2) ≤ b - m := div_le_self (by linarith) (by linarith)
    simp only [Function.comp_apply]
    exact (limit_eq_one_right hab hg (by linarith) (by linarith)).symm
  rw [h0] at h1
  exact zero_ne_one h1

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Contraction Mapping Theorem

SLP §3.2, pp. 49–53.

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

namespace StokeyLucasPrescott.MathematicalPreliminaries

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

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Blackwell's sufficient conditions

SLP §3.2, pp. 54–55.

`B(X)` is the space of bounded functions `f : X → ℝ` with the sup distance
`‖f − g‖ = supₓ |f(x) − g(x)|` (`supDist`).

* `theorem_3_3` (**Blackwell's sufficient conditions**): an operator on `B(X)` that is monotone and
  discounts constants, `T(f + a) ≤ Tf + βa`, satisfies `‖Tf − Tg‖ ≤ β‖f − g‖`.
* `bellmanOp`, `bellmanOp_bdd`, `bellmanOp_mono`, `bellmanOp_add_const`, `bellmanOp_contraction`
  (p. 55): the operator `(Tv)(x) = sup_{y ∈ Γ(x)} [F(x, y) + βv(y)]` of the growth model, with
  nonempty feasible sets and bounded returns, is monotone and discounts, so it is a contraction.
-/

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {X : Type*}

/-- `f` is bounded. -/
def IsBdd (f : X → ℝ) : Prop := ∃ M, ∀ x, |f x| ≤ M

/-- The sup distance `‖f − g‖ = supₓ |f(x) − g(x)|` on `B(X)`. -/
noncomputable def supDist (f g : X → ℝ) : ℝ := ⨆ x, |f x - g x|

theorem bddAbove_absDiff {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) :
    BddAbove (Set.range fun x => |f x - g x|) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨M', hM'⟩ := hg
  refine ⟨M + M', ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (abs_sub _ _).trans (add_le_add (hM x) (hM' x))

theorem abs_le_supDist {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) (x : X) :
    |f x - g x| ≤ supDist f g :=
  le_ciSup (bddAbove_absDiff hf hg) x

theorem supDist_le [Nonempty X] {f g : X → ℝ} {c : ℝ} (h : ∀ x, |f x - g x| ≤ c) :
    supDist f g ≤ c :=
  ciSup_le h

theorem supDist_nonneg [Nonempty X] {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) :
    0 ≤ supDist f g :=
  (abs_nonneg _).trans (abs_le_supDist hf hg (Classical.arbitrary X))

/-- **Theorem 3.3 (Blackwell's sufficient conditions for a contraction).** If `T` on `B(X)`
satisfies (a) monotonicity, `f ≤ g ⇒ Tf ≤ Tg`, and (b) discounting,
`T(f + a) ≤ Tf + βa` for `a ≥ 0`, then `‖Tf − Tg‖ ≤ β‖f − g‖`. -/
theorem theorem_3_3 [Nonempty X] {T : (X → ℝ) → (X → ℝ)} {β : ℝ}
    (hmono : ∀ f g, IsBdd f → IsBdd g → f ≤ g → T f ≤ T g)
    (hdisc : ∀ f, IsBdd f → ∀ a, 0 ≤ a → T (fun x => f x + a) ≤ fun x => T f x + β * a)
    {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) :
    supDist (T f) (T g) ≤ β * supDist f g := by
  set c := supDist f g
  have hc : 0 ≤ c := supDist_nonneg hf hg
  have hshift : ∀ {u : X → ℝ}, IsBdd u → IsBdd fun x => u x + c := fun {u} ⟨M, hM⟩ =>
    ⟨M + |c|, fun x => (abs_add_le _ _).trans (add_le_add (hM x) le_rfl)⟩
  -- `f ≤ g + c` and `g ≤ f + c`
  have h1 : f ≤ fun x => g x + c := fun x => by
    have := abs_le_supDist hf hg x
    linarith [le_abs_self (f x - g x)]
  have h2 : g ≤ fun x => f x + c := fun x => by
    have := abs_le_supDist hf hg x
    linarith [neg_abs_le (f x - g x)]
  have e1 := (hmono _ _ hf (hshift hg) h1).trans (hdisc g hg c hc)
  have e2 := (hmono _ _ hg (hshift hf) h2).trans (hdisc f hf c hc)
  exact supDist_le fun x => abs_le.2 ⟨by linarith [e2 x], by linarith [e1 x]⟩

/-! ### The growth model's operator -/

/-- The operator `(Tv)(x) = sup_{y ∈ Γ(x)} [F(x, y) + βv(y)]`. -/
noncomputable def bellmanOp (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (v : X → ℝ) (x : X) : ℝ :=
  ⨆ y : Γ x, F x y + β * v y

variable {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ}

theorem bddAbove_bellman {M : ℝ} (hF : ∀ x y, |F x y| ≤ M) {v : X → ℝ} (hv : IsBdd v) (x : X) :
    BddAbove (Set.range fun y : Γ x => F x y + β * v y) := by
  obtain ⟨K, hK⟩ := hv
  refine ⟨M + |β| * K, ?_⟩
  rintro _ ⟨y, rfl⟩
  have h1 := (le_abs_self _).trans (hF x y)
  have h2 : β * v y ≤ |β| * K := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK y) (abs_nonneg β))
  linarith

theorem le_bellmanOp {M : ℝ} (hF : ∀ x y, |F x y| ≤ M) {v : X → ℝ} (hv : IsBdd v) {x y : X}
    (hy : y ∈ Γ x) : F x y + β * v y ≤ bellmanOp Γ F β v x :=
  le_ciSup (f := fun y : Γ x => F x y + β * v y) (bddAbove_bellman hF hv x) ⟨y, hy⟩

/-- `T` maps bounded functions to bounded functions. -/
theorem bellmanOp_bdd (hΓ : ∀ x, (Γ x).Nonempty) {M : ℝ} (hF : ∀ x y, |F x y| ≤ M) {v : X → ℝ}
    (hv : IsBdd v) : IsBdd (bellmanOp Γ F β v) := by
  obtain ⟨K, hK⟩ := hv
  refine ⟨M + |β| * K, fun x => ?_⟩
  have := (hΓ x).to_subtype
  have hterm : ∀ y : Γ x, |F x y + β * v y| ≤ M + |β| * K := fun y => by
    refine (abs_add_le _ _).trans (add_le_add (hF x y) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hK y) (abs_nonneg β)
  unfold bellmanOp
  rw [abs_le]
  constructor
  · obtain ⟨y⟩ := (inferInstance : Nonempty (Γ x))
    have := le_ciSup (f := fun y : Γ x => F x y + β * v y) (bddAbove_bellman hF ⟨K, hK⟩ x) y
    linarith [(abs_le.1 (hterm y)).1]
  · exact ciSup_le fun y => (abs_le.1 (hterm y)).2

/-- **Monotonicity** (p. 55). -/
theorem bellmanOp_mono {M : ℝ} (hF : ∀ x y, |F x y| ≤ M) (hβ : 0 ≤ β)
    {v w : X → ℝ} (hw : IsBdd w) (hvw : v ≤ w) : bellmanOp Γ F β v ≤ bellmanOp Γ F β w :=
  fun x => ciSup_mono (bddAbove_bellman hF hw x) fun y =>
    add_le_add le_rfl (mul_le_mul_of_nonneg_left (hvw y) hβ)

/-- `sup (fᵢ + c) = sup fᵢ + c`. -/
theorem ciSup_add_const {ι : Type*} [Nonempty ι] {f : ι → ℝ} (hf : BddAbove (Set.range f))
    (c : ℝ) : ⨆ i, (f i + c) = (⨆ i, f i) + c := by
  have hfc : BddAbove (Set.range fun i => f i + c) := by
    obtain ⟨M, hM⟩ := hf
    exact ⟨M + c, by rintro _ ⟨i, rfl⟩; linarith [hM ⟨i, rfl⟩]⟩
  refine le_antisymm (ciSup_le fun i => by linarith [le_ciSup hf i]) ?_
  have : (⨆ i, f i) ≤ (⨆ i, (f i + c)) - c :=
    ciSup_le fun i => by linarith [le_ciSup hfc i]
  linarith

/-- **Discounting** (p. 55), with equality: `T(v + a) = Tv + βa`. -/
theorem bellmanOp_add_const (hΓ : ∀ x, (Γ x).Nonempty) {M : ℝ} (hF : ∀ x y, |F x y| ≤ M)
    {v : X → ℝ} (hv : IsBdd v) (a : ℝ) :
    bellmanOp Γ F β (fun x => v x + a) = fun x => bellmanOp Γ F β v x + β * a := by
  funext x
  have := (hΓ x).to_subtype
  unfold bellmanOp
  rw [← ciSup_add_const (bddAbove_bellman hF hv x)]
  congr 1
  funext y
  ring

/-- **The growth model's operator is a contraction** on `B(X)` by Blackwell's theorem. -/
theorem bellmanOp_contraction [Nonempty X] (hΓ : ∀ x, (Γ x).Nonempty) {M : ℝ}
    (hF : ∀ x y, |F x y| ≤ M) (hβ : 0 ≤ β) {v w : X → ℝ} (hv : IsBdd v) (hw : IsBdd w) :
    supDist (bellmanOp Γ F β v) (bellmanOp Γ F β w) ≤ β * supDist v w :=
  theorem_3_3 (fun _ _ _ hg hfg => bellmanOp_mono hF hβ hg hfg)
    (fun _ hf a _ => (bellmanOp_add_const hΓ hF hf a).le) hv hw

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The method of successive approximations

SLP Chapter 3 introduction, pp. 39–43.

* `policyValue`, `exercise_3_1` (Ex 3.1): the lifetime utility `w₀` of a feasible policy `g₀`
  satisfies `w₀(k) = U[f(k) − g₀(k)] + βw₀[g₀(k)]`.
* `policyValue_le_bellmanOp` ((4), p. 41): starting from `v₀ = w₀`, the first approximation is an
  improvement, `v₁ ≥ v₀`.
* `iterate_mono` (pp. 41–42): if `T` is monotone and `v₁ ≥ v₀`, the successive approximations
  increase, `v_{n+1} ≥ v_n`.
* `fixedPoint_eq_limit` (p. 40, "(Why?)"): if the successive approximations converge to the same
  limit from every initial guess, that limit is the only solution of the functional equation.
-/

open Filter Topology

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {X : Type*}

/-- The lifetime utility `w₀(k) = ∑ βᵗ R(k_t)` of the policy `g₀` from `k`, with `k_{t+1} = g₀(k_t)`
and per-period utility `R(k) = U[f(k) − g₀(k)]`. -/
noncomputable def policyValue (R : X → ℝ) (g : X → X) (β : ℝ) (k : X) : ℝ :=
  ∑' t, β ^ t * R (g^[t] k)

/-- **Ex 3.1.** `w₀(k) = R(k) + βw₀(g₀(k))`, whenever the series defining `w₀(k)` converges. -/
theorem exercise_3_1 {R : X → ℝ} {g : X → X} {β : ℝ} {k : X}
    (hs : Summable fun t => β ^ t * R (g^[t] k)) :
    policyValue R g β k = R k + β * policyValue R g β (g k) := by
  have e : ∀ t, β ^ (t + 1) * R (g^[t + 1] k) = β * (β ^ t * R (g^[t] (g k))) := fun t => by
    rw [Function.iterate_succ_apply, pow_succ]
    ring
  unfold policyValue
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, Function.iterate_zero_apply, e, tsum_mul_left]

/-- **(4), p. 41.** If `g₀(k)` is feasible, `R(k) = F(k, g₀(k))` and `w₀` satisfies Ex 3.1, the
first successive approximation from `w₀` improves on it: `w₀ ≤ Tw₀`. -/
theorem policyValue_le_bellmanOp {Γ : X → Set X} {F : X → X → ℝ} {M : ℝ}
    (hF : ∀ x y, |F x y| ≤ M) {g : X → X} (hg : ∀ k, g k ∈ Γ k) {β : ℝ}
    (hs : ∀ k, Summable fun t => β ^ t * F (g^[t] k) (g (g^[t] k)))
    (hbdd : IsBdd (policyValue (fun k => F k (g k)) g β)) (k : X) :
    policyValue (fun k => F k (g k)) g β k ≤
      bellmanOp Γ F β (policyValue (fun k => F k (g k)) g β) k := by
  have h := exercise_3_1 (R := fun k => F k (g k)) (g := g) (β := β) (k := k) (hs k)
  rw [h]
  exact le_bellmanOp hF hbdd (hg k)

/-- **pp. 41–42.** If `T` is monotone and `v₀ ≤ Tv₀`, the successive approximations `vₙ = Tⁿv₀`
increase. -/
theorem iterate_mono {α : Type*} [Preorder α] {T : α → α} (hT : Monotone T) {v₀ : α}
    (h : v₀ ≤ T v₀) : Monotone fun n => T^[n] v₀ :=
  hT.monotone_iterate_of_le_map h

/-- **p. 40, "(Why?)".** If `Tⁿv₀ → L` for every initial guess `v₀`, every fixed point of `T` is
`L`: the functional equation has exactly one solution. -/
theorem fixedPoint_eq_limit {α : Type*} [TopologicalSpace α] [T2Space α] {T : α → α} {L : α}
    (h : ∀ v₀, Tendsto (fun n => T^[n] v₀) atTop (𝓝 L)) {v : α} (hv : T v = v) : v = L := by
  have hconst : Tendsto (fun n => T^[n] v) atTop (𝓝 v) := by
    simp only [Function.iterate_fixed hv]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hconst (h v)

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Intersections of convex-valued l.h.c. correspondences

SLP Exercise 3.12d, p. 59, second half: if `φ, ψ : X → ℝ^m` are l.h.c. at `x` and
convex-valued, and `int φ(x) ∩ int ψ(x) ≠ ∅`, then `φ ∩ ψ` is l.h.c. at `x`. (The first half,
an example where `φ ∩ ψ` fails to be l.h.c., is `not_isLHC_inter`.)

* `eventually_mem_of_mem_interior`: a point interior to `φ(x)` lies in `φ(xₙ)` for all large
  `n`. Points of `φ(xₙ)` near the `2m` vertices `z ± 2δeⱼ` would otherwise be separated from `z`
  by a hyperplane, which cannot be.
* `isLHC_inter_of_interior` (Ex 3.12d).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.MathematicalPreliminaries

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

/-- **Ex 3.12d.** If `φ, ψ : X → ℝ^m` are convex-valued and l.h.c. at `x`, and
`int φ(x) ∩ int ψ(x) ≠ ∅`, then `Γ = φ ∩ ψ` is l.h.c. at `x`. -/
theorem isLHC_inter_of_interior {φ ψ : X → Set (Fin m → ℝ)} (hφc : ∀ x', Convex ℝ (φ x'))
    (hψc : ∀ x', Convex ℝ (ψ x')) {x : X} (hφ : IsLHC φ x) (hψ : IsLHC ψ x)
    (hint : (interior (φ x) ∩ interior (ψ x)).Nonempty) :
    IsLHC (fun x => φ x ∩ ψ x) x := by
  obtain ⟨ŷ, hŷφ, hŷψ⟩ := hint
  refine ⟨⟨ŷ, interior_subset hŷφ, interior_subset hŷψ⟩, fun y hy xs hxs => ?_⟩
  -- points `yₖ → y` interior to both `φ(x)` and `ψ(x)`
  set yk : ℕ → Fin m → ℝ := fun k => y + (1 / ((k : ℝ) + 1)) • (ŷ - y)
  have hk : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ∈ Ioc (0 : ℝ) 1 := fun k =>
    ⟨by positivity, (div_le_one (by positivity)).2 (by linarith [k.cast_nonneg (α := ℝ)])⟩
  have hev : ∀ k, ∀ᶠ n in atTop, yk k ∈ φ (xs n) ∩ ψ (xs n) := fun k =>
    (eventually_mem_of_mem_interior hφc hφ
      ((hφc x).add_smul_sub_mem_interior hy.1 hŷφ (hk k)) hxs).and
    (eventually_mem_of_mem_interior hψc hψ
      ((hψc x).add_smul_sub_mem_interior hy.2 hŷψ (hk k)) hxs)
  choose N hN using fun k => eventually_atTop.1 (hev k)
  -- a diagonal sequence: at time `n` use the largest `k ≤ n` with `N k ≤ n`
  set kn : ℕ → ℕ := fun n => Nat.findGreatest (fun k => N k ≤ n) n
  have hyk : Tendsto yk atTop (𝓝 y) := by
    have := (tendsto_const_nhds (x := y)).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (ŷ - y))
    rwa [zero_smul, add_zero] at this
  have hkn : Tendsto kn atTop atTop := tendsto_atTop.2 fun K => eventually_atTop.2
    ⟨max K (N K), fun n hn => Nat.le_findGreatest (le_of_max_le_left hn) (le_of_max_le_right hn)⟩
  exact ⟨N 0, fun n => yk (kn n),
    fun n hn => hN _ n (Nat.findGreatest_spec (P := fun k => N k ≤ n) (Nat.zero_le n) hn),
    hyk.comp hkn⟩

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Theorem of the Maximum

SLP §3.3, pp. 56–65.

For `f : X × Y → ℝ` and a correspondence `Γ`, `h(x) = max_{y ∈ Γ(x)} f(x, y)` (`maxValue`) and
`G(x) = {y ∈ Γ(x) : f(x, y) = h(x)}` (`argmax`).

* `theorem_3_6` (**Theorem of the Maximum**): if `f` is continuous (on the graph) and `Γ` is
  compact-valued and continuous, then `h` is continuous and `G` is nonempty, compact-valued and
  u.h.c.
* `ArgmaxSetup`, `argmaxFn`: with `Γ` also convex-valued and `f(x, ·)` strictly concave, the
  maximizer `g(x)` is unique; `continuous_argmaxFn`: `g` is continuous.
* `lemma_3_7`: `y` close to the maximum in value is close to `g(x)` (uniformly when `X` is compact,
  `lemma_3_7_uniform`).
* `theorem_3_8`: if `f_n → f` uniformly on the graph, the maximizers `g_n → g` pointwise, and
  uniformly when `X` is compact (`theorem_3_8_uniform`).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.MathematicalPreliminaries

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

/-! ### Strictly concave objectives: Lemma 3.7 and Theorem 3.8 -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The hypotheses of Lemma 3.7: `Γ` nonempty-, compact- and convex-valued and continuous; `f`
continuous on the graph and strictly concave in its second argument. -/
structure ArgmaxSetup (Γ : X → Set V) (f : X × V → ℝ) : Prop where
  nonempty : ∀ x, (Γ x).Nonempty
  compact : ∀ x, IsCompact (Γ x)
  convex : ∀ x, Convex ℝ (Γ x)
  lhc : ∀ x, IsLHC Γ x
  uhc : ∀ x, IsUHC Γ x
  cont : ContinuousOn f (graph Γ)
  strict : ∀ x, StrictConcaveOn ℝ (Γ x) fun y => f (x, y)

namespace ArgmaxSetup

variable {Γ : X → Set V} {f : X × V → ℝ} (h : ArgmaxSetup Γ f)
include h

/-- With a strictly concave objective the maximizer is unique. -/
theorem argmax_unique {x : X} {y₁ y₂ : V} (h₁ : y₁ ∈ argmax f Γ x) (h₂ : y₂ ∈ argmax f Γ x) :
    y₁ = y₂ := by
  by_contra hne
  have hmid := (h.strict x).2 h₁.1 h₂.1 hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hmem : (1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂ ∈ Γ x :=
    h.convex x h₁.1 h₂.1 (by norm_num) (by norm_num) (by norm_num)
  have := le_maxValue h.cont (h.compact x) hmem
  simp only [smul_eq_mul, h₁.2, h₂.2] at hmid
  linarith

end ArgmaxSetup

/-- The maximizer `g(x) = argmax_{y ∈ Γ(x)} f(x, y)`. -/
noncomputable def argmaxFn (Γ : X → Set V) (f : X × V → ℝ) (x : X) : V :=
  Classical.epsilon fun y => y ∈ argmax f Γ x

namespace ArgmaxSetup

variable {Γ : X → Set V} {f : X × V → ℝ} (h : ArgmaxSetup Γ f)
include h

theorem argmaxFn_mem (x : X) : argmaxFn Γ f x ∈ argmax f Γ x := by
  obtain ⟨y, hy, hval, -⟩ := exists_argmax h.cont (h.compact x) (h.nonempty x)
  exact Classical.epsilon_spec (p := fun y => y ∈ argmax f Γ x) ⟨y, hy, hval⟩

theorem argmax_eq (x : X) : argmax f Γ x = {argmaxFn Γ f x} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨h.argmaxFn_mem x, fun _ hy => h.argmax_unique hy
    (h.argmaxFn_mem x)⟩

/-- `f(x, y) < f(x, g(x))` for `y ≠ g(x)` in `Γ(x)`. -/
theorem lt_of_ne {x : X} {y : V} (hy : y ∈ Γ x) (hne : y ≠ argmaxFn Γ f x) :
    f (x, y) < f (x, argmaxFn Γ f x) := by
  have hle : f (x, y) ≤ f (x, argmaxFn Γ f x) := by
    rw [(h.argmaxFn_mem x).2]
    exact le_maxValue h.cont (h.compact x) hy
  refine lt_of_le_of_ne hle fun heq => hne ?_
  have : y ∈ argmax f Γ x := ⟨hy, by rw [heq]; exact (h.argmaxFn_mem x).2⟩
  rw [h.argmax_eq x] at this
  exact this

/-- **The maximizer is continuous** (Theorem 3.6 with Ex 3.11a). -/
theorem continuous_argmaxFn : Continuous (argmaxFn Γ f) := by
  have h36 := theorem_3_6 h.cont h.compact h.lhc h.uhc
  refine continuous_iff_continuousAt.2 fun x => continuousAt_of_isUHC_singleton ?_
  have := (h36.2 x).2.2
  have heq : argmax f Γ = fun x => {argmaxFn Γ f x} := funext h.argmax_eq
  rwa [heq] at this

/-- **Lemma 3.7.** For each `ε > 0` and `x` there is `δ > 0` such that `y ∈ Γ(x)` and
`|f(x, g(x)) − f(x, y)| < δ` imply `‖g(x) − y‖ < ε`. -/
theorem lemma_3_7 {ε : ℝ} (hε : 0 < ε) (x : X) :
    ∃ δ > 0, ∀ y ∈ Γ x, |f (x, argmaxFn Γ f x) - f (x, y)| < δ → ‖argmaxFn Γ f x - y‖ < ε := by
  set g := argmaxFn Γ f x
  set K := Γ x ∩ {y | ε ≤ ‖g - y‖}
  have hK : IsCompact K := (h.compact x).inter_right
    (isClosed_le continuous_const (continuous_const.sub continuous_id).norm)
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun y hy _ => ?_⟩
    by_contra hge
    have : y ∈ K := ⟨hy, not_lt.1 hge⟩
    rw [hK0] at this
    exact this
  -- the smallest shortfall from the maximum on `K` is positive
  have hcont : ContinuousOn (fun y => f (x, g) - f (x, y)) K :=
    continuousOn_const.sub ((continuousOn_section h.cont x).mono inter_subset_left)
  obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hKne hcont
  have hpos : 0 < f (x, g) - f (x, y₀) := by
    have hne : y₀ ≠ g := fun he => by
      have := hy₀.2
      simp only [Set.mem_ofPred_eq] at this
      rw [he, sub_self, norm_zero] at this
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
      |f (x, argmaxFn Γ f x) - f (x, y)| < δ → ‖argmaxFn Γ f x - y‖ < ε := by
  set g := argmaxFn Γ f
  have hg := h.continuous_argmaxFn
  set Aε := graph Γ ∩ {p : X × V | ε ≤ ‖g p.1 - p.2‖}
  have hA : IsCompact Aε := (isCompact_graph h.uhc).inter_right
    (isClosed_le continuous_const ((hg.comp continuous_fst).sub continuous_snd).norm)
  rcases Aε.eq_empty_or_nonempty with hA0 | hAne
  · refine ⟨1, one_pos, fun x y hy _ => ?_⟩
    by_contra hge
    have : (x, y) ∈ Aε := ⟨hy, not_lt.1 hge⟩
    rw [hA0] at this
    exact this
  -- `(x, y) ↦ f(x, g(x)) − f(x, y)` is continuous on the graph
  have hcont : ContinuousOn (fun p : X × V => f (p.1, g p.1) - f p) Aε := by
    refine ContinuousOn.sub ?_ (h.cont.mono inter_subset_left)
    exact h.cont.comp (continuous_fst.prodMk (hg.comp continuous_fst)).continuousOn
      fun p _ => (h.argmaxFn_mem p.1).1
  obtain ⟨p₀, hp₀, hmin⟩ := hA.exists_isMinOn hAne hcont
  have hpos : 0 < f (p₀.1, g p₀.1) - f p₀ := by
    have hne : p₀.2 ≠ g p₀.1 := fun he => by
      have := hp₀.2
      simp only [Set.mem_ofPred_eq] at this
      rw [he, sub_self, norm_zero] at this
      linarith
    have := h.lt_of_ne hp₀.1 hne
    linarith
  refine ⟨_, hpos, fun x y hy hyδ => ?_⟩
  by_contra hge
  have hyA : (x, y) ∈ Aε := ⟨hy, not_lt.1 hge⟩
  have := isMinOn_iff.1 hmin (x, y) hyA
  have habs := le_abs_self (f (x, g x) - f (x, y))
  linarith

end ArgmaxSetup

/-- The shortfall bound behind Theorem 3.8: if `|f − fₙ| < δ/2` on the graph, then
`|f(x, g(x)) − f(x, gₙ(x))| < δ`. -/
theorem shortfall_lt {Γ : X → Set V} {f fn : X × V → ℝ} (hf : ArgmaxSetup Γ f)
    (hfn : ArgmaxSetup Γ fn) {δ : ℝ} (hclose : ∀ p ∈ graph Γ, |f p - fn p| < δ / 2) (x : X) :
    |f (x, argmaxFn Γ f x) - f (x, argmaxFn Γ fn x)| < δ := by
  set g := argmaxFn Γ f x
  set gn := argmaxFn Γ fn x
  have hg := hf.argmaxFn_mem x
  have hgn := hfn.argmaxFn_mem x
  have h1 : f (x, gn) ≤ f (x, g) := by rw [hg.2]; exact le_maxValue hf.cont (hf.compact x) hgn.1
  have h2 : fn (x, g) ≤ fn (x, gn) := by rw [hgn.2]; exact le_maxValue hfn.cont (hfn.compact x) hg.1
  have e1 := abs_lt.1 (hclose (x, g) hg.1)
  have e2 := abs_lt.1 (hclose (x, gn) hgn.1)
  rw [abs_of_nonneg (sub_nonneg.2 h1)]
  linarith [e1.1, e1.2, e2.1, e2.2]

/-- **Theorem 3.8.** If `fₙ → f` uniformly on the graph, each with the properties of Lemma 3.7,
then the maximizers converge pointwise: `gₙ(x) → g(x)`. -/
theorem theorem_3_8 {Γ : X → Set V} {f : X × V → ℝ} {fs : ℕ → X × V → ℝ}
    (hf : ArgmaxSetup Γ f) (hfs : ∀ n, ArgmaxSetup Γ (fs n))
    (hunif : TendstoUniformlyOn fs f atTop (graph Γ)) (x : X) :
    Tendsto (fun n => argmaxFn Γ (fs n) x) atTop (𝓝 (argmaxFn Γ f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hlem⟩ := hf.lemma_3_7 hε x
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hunif) (δ / 2)
    (half_pos hδ))
  refine ⟨M, fun n hn => ?_⟩
  rw [dist_comm, dist_eq_norm]
  refine hlem _ (hfs n |>.argmaxFn_mem x).1 (shortfall_lt hf (hfs n) (fun p hp => ?_) x)
  have := hM n hn p hp
  rwa [Real.dist_eq] at this

/-- **Theorem 3.8 (compact `X`).** If `X` is compact the convergence is uniform. -/
theorem theorem_3_8_uniform [CompactSpace X] {Γ : X → Set V} {f : X × V → ℝ}
    {fs : ℕ → X × V → ℝ} (hf : ArgmaxSetup Γ f) (hfs : ∀ n, ArgmaxSetup Γ (fs n))
    (hunif : TendstoUniformlyOn fs f atTop (graph Γ)) :
    TendstoUniformly (fun n => argmaxFn Γ (fs n)) (argmaxFn Γ f) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hlem⟩ := hf.lemma_3_7_uniform hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hunif) (δ / 2)
    (half_pos hδ))
  refine eventually_atTop.2 ⟨M, fun n hn x => ?_⟩
  rw [dist_eq_norm]
  refine hlem x _ (hfs n |>.argmaxFn_mem x).1 (shortfall_lt hf (hfs n) (fun p hp => ?_) x)
  have := hM n hn p hp
  rwa [Real.dist_eq] at this

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# What the Theorem of the Maximum does and does not say

SLP Exercise 3.16, pp. 62–63: in each example `G` is u.h.c. (Theorem 3.6) but not l.h.c.
everywhere.

* `isLHC_const`, `isUHC_const`: a constant compact correspondence is continuous.
* `ex_3_16a`: `Γ(x) = [−1, 1]`, `f(x, y) = xy²`; `G` is u.h.c. but not l.h.c. at `0`.
* `ex_3_16b`: `Γ(x) = [0, 4]`, `f(x, y) = max{2 − (y − 1)², x + 1 − (y − 2)²}`; `G` is u.h.c. and
  is l.h.c. exactly at `x ≠ 1`.
* `ex_3_16c`: `X = ℝ₊`, `Γ(x) = [−x, x]`, `f(x, y) = cos y`; `G` is u.h.c. and fails to be l.h.c.
  exactly at `x = 2πk`, `k = 1, 2, …`.
-/

open Set Filter Topology Real

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem isLHC_const {K : Set Y} (hK : K.Nonempty) (x : X) : IsLHC (fun _ : X => K) x :=
  ⟨hK, fun y hy _ _ => ⟨0, fun _ => y, fun _ _ => hy, tendsto_const_nhds⟩⟩

theorem isUHC_const {K : Set Y} (hK : K.Nonempty) (hc : IsCompact K) (x : X) :
    IsUHC (fun _ : X => K) x :=
  ⟨hK, fun _ _ _ hys => hc.tendsto_subseq hys⟩

/-- Along a sequence where `G` is eventually `{c}`, an l.h.c. selection must converge to `c`. -/
theorem not_isLHC_of_eventually {G : X → Set ℝ} {x : X} {y c : ℝ} (hy : y ∈ G x) (hyc : y ≠ c)
    {xs : ℕ → X} (hxs : Tendsto xs atTop (𝓝 x)) (hG : ∀ᶠ n in atTop, G (xs n) ⊆ {c}) :
    ¬ IsLHC G x := by
  rintro ⟨-, h⟩
  obtain ⟨N, ys, hys, hlim⟩ := h y hy xs hxs
  have hc : Tendsto ys atTop (𝓝 c) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hG, eventually_ge_atTop N] with n hn hnN
    exact (hn (hys n hnN)).symm
  exact hyc (tendsto_nhds_unique hlim hc)

/-! ### Exercise 3.16a -/

/-- **Ex 3.16a.** For `Γ(x) = [−1, 1]` and `f(x, y) = xy²`, the maximizers `G` are u.h.c. but not
l.h.c. at `x = 0`. -/
theorem ex_3_16a :
    (∀ x : ℝ, IsUHC (argmax (fun p : ℝ × ℝ => p.1 * p.2 ^ 2) fun _ => Set.Icc (-1) 1) x) ∧
      ¬ IsLHC (argmax (fun p : ℝ × ℝ => p.1 * p.2 ^ 2) fun _ => Set.Icc (-1) 1) 0 := by
  set f : ℝ × ℝ → ℝ := fun p => p.1 * p.2 ^ 2
  set Γ : ℝ → Set ℝ := fun _ => Set.Icc (-1) 1
  have hne : (Icc (-1 : ℝ) 1).Nonempty := ⟨0, by norm_num, by norm_num⟩
  have hf : ContinuousOn f (graph Γ) := (continuous_fst.mul (continuous_snd.pow 2)).continuousOn
  have h36 := theorem_3_6 hf (fun _ => isCompact_Icc) (isLHC_const hne)
    (isUHC_const hne isCompact_Icc)
  refine ⟨fun x => (h36.2 x).2.2, ?_⟩
  -- at `x = 0` every point maximizes; for `x < 0` only `0` does
  have h1 : (1 : ℝ) ∈ argmax f Γ 0 := by
    refine ⟨⟨by norm_num, le_rfl⟩, ?_⟩
    obtain ⟨y, hy, hval, -⟩ := exists_argmax hf (x := 0) (isCompact_Icc (a := -1) (b := 1)) hne
    simp only [f, zero_mul] at hval ⊢
    exact hval
  refine not_isLHC_of_eventually h1 one_ne_zero (xs := fun n : ℕ => -(1 / ((n : ℝ) + 1)))
    (by have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg; rwa [neg_zero] at this)
    (Eventually.of_forall fun n y hy => ?_)
  have hneg : -(1 / ((n : ℝ) + 1)) < 0 := neg_neg_of_pos (by positivity)
  have h0 := le_maxValue (f := f) (Γ := Γ) hf (isCompact_Icc (a := -1) (b := 1))
    (x := -(1 / ((n : ℝ) + 1))) (show (0 : ℝ) ∈ Set.Icc (-1) 1 from ⟨by norm_num, by norm_num⟩)
  rw [← hy.2] at h0
  simp only [f] at h0
  have hy2 : y ^ 2 = 0 := by nlinarith [sq_nonneg y]
  rw [mem_singleton_iff]
  exact (pow_eq_zero_iff two_ne_zero).1 hy2

/-! ### Exercise 3.16b -/

/-- The objective of Ex 3.16b. -/
noncomputable def f316b (p : ℝ × ℝ) : ℝ := max (2 - (p.2 - 1) ^ 2) (p.1 + 1 - (p.2 - 2) ^ 2)

theorem continuous_f316b : Continuous f316b := by unfold f316b; fun_prop

/-- For `x < 1` the maximizers are `{1}`; for `x > 1`, `{2}`; at `x = 1`, `{1, 2}`. -/
theorem argmax_316b (x : ℝ) :
    argmax f316b (fun _ => Set.Icc 0 4) x =
      if x < 1 then {1} else if 1 < x then {2} else {1, 2} := by
  have hne : (Icc (0 : ℝ) 4).Nonempty := ⟨0, le_rfl, by norm_num⟩
  have hf : ContinuousOn f316b (graph fun _ : ℝ => Icc (0 : ℝ) 4) := continuous_f316b.continuousOn
  -- the maximum value is `max 2 (x + 1)`
  have hmax : maxValue f316b (fun _ => Set.Icc 0 4) x = max 2 (x + 1) := by
    refine le_antisymm (csSup_le (hne.image _) ?_) ?_
    · rintro _ ⟨y, -, rfl⟩
      exact max_le_max (by nlinarith [sq_nonneg (y - 1)]) (by nlinarith [sq_nonneg (y - 2)])
    · have e1 := le_maxValue (f := f316b) (Γ := fun _ => Icc (0 : ℝ) 4) hf isCompact_Icc (x := x)
        (show (1 : ℝ) ∈ Set.Icc 0 4 from ⟨by norm_num, by norm_num⟩)
      have e2 := le_maxValue (f := f316b) (Γ := fun _ => Icc (0 : ℝ) 4) hf isCompact_Icc (x := x)
        (show (2 : ℝ) ∈ Set.Icc 0 4 from ⟨by norm_num, by norm_num⟩)
      simp only [f316b] at e1 e2
      refine max_le ?_ ?_
      · exact le_trans (by norm_num) (le_trans (le_max_left _ _) e1)
      · exact le_trans (by norm_num) (le_trans (le_max_right _ _) e2)
  ext y
  simp only [argmax, Set.mem_ofPred_eq, hmax, f316b]
  constructor
  · rintro ⟨hy, heq⟩
    split_ifs with h1 h2
    · rw [mem_singleton_iff]
      rcases le_total (2 - (y - 1) ^ 2) (x + 1 - (y - 2) ^ 2) with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)] at heq
        nlinarith [sq_nonneg (y - 2)]
      · rw [max_eq_left h, max_eq_left (by linarith)] at heq
        nlinarith [sq_nonneg (y - 1)]
    · rw [mem_singleton_iff]
      rcases le_total (2 - (y - 1) ^ 2) (x + 1 - (y - 2) ^ 2) with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)] at heq
        nlinarith [sq_nonneg (y - 2)]
      · rw [max_eq_left h, max_eq_right (by linarith)] at heq
        nlinarith [sq_nonneg (y - 1)]
    · have hx : x = 1 := by linarith [not_lt.1 h1, not_lt.1 h2]
      subst hx
      rcases le_total (2 - (y - 1) ^ 2) (1 + 1 - (y - 2) ^ 2) with h | h
      · rw [max_eq_right h] at heq
        norm_num at heq
        right; rw [mem_singleton_iff]; nlinarith [sq_nonneg (y - 2)]
      · rw [max_eq_left h] at heq
        norm_num at heq
        left; nlinarith [sq_nonneg (y - 1)]
  · intro hy
    split_ifs at hy with h1 h2
    · rw [mem_singleton_iff] at hy
      subst hy
      refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      norm_num
    · rw [mem_singleton_iff] at hy
      subst hy
      refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      norm_num
    · have hx : x = 1 := by linarith [not_lt.1 h1, not_lt.1 h2]
      subst hx
      rcases hy with rfl | hy
      · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
      · rw [mem_singleton_iff] at hy
        subst hy
        exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩

/-- **Ex 3.16b.** `G` is u.h.c. everywhere and l.h.c. exactly at `x ≠ 1`. -/
theorem ex_3_16b :
    (∀ x : ℝ, IsUHC (argmax f316b fun _ => Set.Icc 0 4) x) ∧
      ∀ x : ℝ, IsLHC (argmax f316b fun _ => Set.Icc 0 4) x ↔ x ≠ 1 := by
  have hne : (Icc (0 : ℝ) 4).Nonempty := ⟨0, le_rfl, by norm_num⟩
  have h36 := theorem_3_6 continuous_f316b.continuousOn (fun _ => isCompact_Icc)
    (isLHC_const (X := ℝ) hne) (isUHC_const hne isCompact_Icc)
  refine ⟨fun x => (h36.2 x).2.2, fun x => ⟨fun h hx => ?_, fun hx => ?_⟩⟩
  · -- not l.h.c. at `1`: approach from below, where `G = {1}`, the maximizer `2` is lost
    subst hx
    refine not_isLHC_of_eventually (c := 1) (y := 2) ?_ (by norm_num)
      (xs := fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) ?_ (Eventually.of_forall fun n => ?_) h
    · rw [argmax_316b]; simp
    · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
    · have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have : 1 - 1 / ((n : ℝ) + 1) < 1 := by linarith
      rw [argmax_316b]
      simp only [this, ↓reduceIte, subset_refl]
  · -- l.h.c. at `x ≠ 1`: `G` is locally constant there
    refine ⟨?_, fun y hy xs hxs => ?_⟩
    · rcases lt_or_gt_of_ne hx with h | h
      · exact ⟨1, by rw [argmax_316b]; simp [h]⟩
      · exact ⟨2, by rw [argmax_316b]; simp [not_lt.2 h.le, h]⟩
    rcases lt_or_gt_of_ne hx with h | h
    · rw [argmax_316b] at hy
      simp only [h, ↓reduceIte, mem_singleton_iff] at hy
      subst hy
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hxs.eventually (gt_mem_nhds h))
      exact ⟨N, fun _ => 1, fun n hn => by rw [argmax_316b]; simp [hN n hn],
        tendsto_const_nhds⟩
    · rw [argmax_316b] at hy
      simp only [not_lt.2 h.le, h, ↓reduceIte, mem_singleton_iff] at hy
      subst hy
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hxs.eventually (lt_mem_nhds h))
      exact ⟨N, fun _ => 2, fun n hn => by
        rw [argmax_316b]; simp [not_lt.2 (hN n hn).le, hN n hn],
        tendsto_const_nhds⟩

/-! ### Exercise 3.16c -/

/-- The nonnegative reals, `ℝ₊`. -/
abbrev NNR : Type := {x : ℝ // 0 ≤ x}

/-- `Γ(x) = [−x, x]` on `ℝ₊`. -/
def gamma316c (x : NNR) : Set ℝ := Icc (-(x : ℝ)) x

theorem tendsto_val {xs : ℕ → NNR} {x : NNR} (h : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun n => ((xs n : NNR) : ℝ)) atTop (𝓝 (x : ℝ)) :=
  (continuous_subtype_val.tendsto x).comp h

/-- `Γ(x) = [−x, x]` is continuous on `ℝ₊`. -/
theorem gamma316c_continuous (x : NNR) : IsLHC gamma316c x ∧ IsUHC gamma316c x := by
  have hne : (gamma316c x).Nonempty := ⟨0, by simp [gamma316c, x.2]⟩
  refine ⟨⟨hne, fun y hy xs hxs => ?_⟩, ⟨hne, fun xs hxs ys hys => ?_⟩⟩
  · -- clamp `y` into `[−x_n, x_n]`
    refine ⟨0, fun n => max (-((xs n : NNR) : ℝ)) (min (xs n : ℝ) y), fun n _ => ⟨le_max_left _ _,
      max_le (by linarith [(xs n).2]) (min_le_left _ _)⟩, ?_⟩
    have h := ((tendsto_val hxs).neg).max ((tendsto_val hxs).min (tendsto_const_nhds (x := y)))
    rwa [min_eq_right hy.2, max_eq_right hy.1] at h
  · -- bounded, so a subsequence converges; the limit stays in `[−x, x]`
    obtain ⟨B, hB⟩ := (tendsto_val hxs).bddAbove_range
    have hmem : ∀ n, ys n ∈ Icc (-B) B := fun n =>
      ⟨by linarith [(hys n).1, hB ⟨n, rfl⟩], by linarith [(hys n).2, hB ⟨n, rfl⟩]⟩
    obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
    have hx := (tendsto_val hxs).comp hφ.tendsto_atTop
    refine ⟨y, ⟨?_, ?_⟩, φ, hφ, hlim⟩
    · exact le_of_tendsto_of_tendsto hx.neg hlim (Eventually.of_forall fun n => (hys (φ n)).1)
    · exact le_of_tendsto_of_tendsto hlim hx (Eventually.of_forall fun n => (hys (φ n)).2)

/-- The maximizers of `cos y` on `[−x, x]`: the multiples `2πj` in `[−x, x]`. -/
theorem argmax_316c (x : NNR) :
    argmax (fun p : NNR × ℝ => cos p.2) gamma316c x = {y | y ∈ gamma316c x ∧ cos y = 1} := by
  have hf : ContinuousOn (fun p : NNR × ℝ => cos p.2) (graph gamma316c) :=
    (continuous_cos.comp continuous_snd).continuousOn
  have hmax : maxValue (fun p : NNR × ℝ => cos p.2) gamma316c x = 1 := by
    refine le_antisymm (csSup_le ⟨1, 0, by simp [gamma316c, x.2]⟩ ?_) ?_
    · rintro _ ⟨y, -, rfl⟩
      exact cos_le_one y
    · have := le_maxValue hf isCompact_Icc (x := x) (show (0 : ℝ) ∈ gamma316c x by
        simp [gamma316c, x.2])
      simpa using this
  ext y
  simp only [argmax, Set.mem_ofPred_eq, hmax]

/-- A sequence staying at distance `≥ c > 0` from `y` does not converge to `y`. -/
theorem not_tendsto_of_far {ys : ℕ → ℝ} {y c : ℝ} (hc : 0 < c) {N : ℕ}
    (h : ∀ n ≥ N, c ≤ |ys n - y|) : ¬ Tendsto ys atTop (𝓝 y) := fun hlim => by
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hlim c hc
  have := hM (max M N) (le_max_left _ _)
  rw [Real.dist_eq] at this
  linarith [h (max M N) (le_max_right _ _)]

/-- **Ex 3.16c.** For `Γ(x) = [−x, x]` on `ℝ₊` and `f(x, y) = cos y`, `G` is u.h.c. everywhere and
fails to be l.h.c. exactly at `x = 2πk`, `k = 1, 2, …`. -/
theorem ex_3_16c :
    (∀ x : NNR, IsUHC (argmax (fun p : NNR × ℝ => cos p.2) gamma316c) x) ∧
      ∀ x : NNR, IsLHC (argmax (fun p : NNR × ℝ => cos p.2) gamma316c) x ↔
        ¬ ∃ k : ℕ, 1 ≤ k ∧ (x : ℝ) = 2 * π * k := by
  have h36 := theorem_3_6 (continuous_cos.comp continuous_snd).continuousOn
    (fun _ => isCompact_Icc) (fun x => (gamma316c_continuous x).1)
    (fun x => (gamma316c_continuous x).2)
  refine ⟨fun x => (h36.2 x).2.2, fun x => ⟨fun h ⟨k, hk, hx⟩ => ?_, fun hx => ?_⟩⟩
  · -- at `x = 2πk`, approach from below: the maximizer `2πk` is lost
    rw [show argmax (fun p : NNR × ℝ => cos p.2) gamma316c = fun x => {y | y ∈ gamma316c x ∧
      cos y = 1} from funext argmax_316c] at h
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hy : 2 * π * k ∈ {y | y ∈ gamma316c x ∧ cos y = 1} := by
      refine ⟨⟨by rw [hx]; nlinarith [pi_pos], by rw [hx]⟩, ?_⟩
      rw [cos_eq_one_iff]
      exact ⟨k, by push_cast; ring⟩
    set xs : ℕ → NNR := fun n => ⟨2 * π * k - π / (n + 2), by
      have : π / ((n : ℝ) + 2) ≤ π := div_le_self pi_pos.le (by linarith)
      nlinarith [pi_pos]⟩
    have hxs : Tendsto xs atTop (𝓝 x) := by
      rw [tendsto_subtype_rng, hx]
      have h1 : Tendsto (fun n : ℕ => π / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
        have := this.const_mul π
        rw [mul_zero] at this
        refine this.congr fun n => ?_
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
        ring
      have := (tendsto_const_nhds (x := 2 * π * (k : ℝ))).sub h1
      rwa [sub_zero] at this
    obtain ⟨N, ys, hys, hlim⟩ := h.2 _ hy xs hxs
    refine not_tendsto_of_far (c := 2 * π) (by linarith [pi_pos]) (N := N) (fun n hn => ?_) hlim
    obtain ⟨⟨-, hle⟩, hcos⟩ := hys n hn
    obtain ⟨j, hj⟩ := (cos_eq_one_iff _).1 hcos
    have hlt : (j : ℝ) < k := by
      have : π / ((n : ℝ) + 2) > 0 := by positivity
      have h2 : (j : ℝ) * (2 * π) < 2 * π * k := by
        rw [hj]; exact lt_of_le_of_lt hle (by simp only [xs]; linarith)
      nlinarith [pi_pos]
    have hjk : (j : ℝ) ≤ k - 1 := by
      have : j < (k : ℤ) := by exact_mod_cast hlt
      have : j ≤ (k : ℤ) - 1 := by omega
      exact_mod_cast this
    rw [← hj, abs_sub_comm, abs_of_nonneg (by nlinarith [pi_pos])]
    nlinarith [pi_pos]
  · -- elsewhere: a maximizer strictly inside `[−x, x]` survives nearby, and on the boundary
    -- the only maximizer is `0`, at `x = 0`
    rw [show argmax (fun p : NNR × ℝ => cos p.2) gamma316c = fun x => {y | y ∈ gamma316c x ∧
      cos y = 1} from funext argmax_316c]
    refine ⟨⟨0, by simp [gamma316c, x.2]⟩, fun y hy xs hxs => ?_⟩
    obtain ⟨⟨hy1, hy2⟩, hcos⟩ := hy
    rcases lt_or_eq_of_le (abs_le.2 ⟨hy1, hy2⟩) with hlt | heq
    · obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_val hxs).eventually (lt_mem_nhds hlt))
      exact ⟨N, fun _ => y, fun n hn => ⟨⟨by linarith [neg_abs_le y, hN n hn],
        by linarith [le_abs_self y, hN n hn]⟩, hcos⟩, tendsto_const_nhds⟩
    · obtain ⟨j, hj⟩ := (cos_eq_one_iff _).1 hcos
      have hj0 : j = 0 := by
        by_contra hj0
        refine hx ⟨j.natAbs, Int.natAbs_pos.2 hj0, ?_⟩
        rw [← heq, ← hj, abs_mul, abs_of_pos (by linarith [pi_pos] : (0 : ℝ) < 2 * π),
          Nat.cast_natAbs, Int.cast_abs]
        ring
      have hy0 : y = 0 := by rw [← hj, hj0]; simp
      subst hy0
      exact ⟨0, fun _ => 0, fun n _ => ⟨by simp [gamma316c, (xs n).2], cos_zero⟩,
        tendsto_const_nhds⟩

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Correspondences defined by constraints

SLP Exercises 3.13–3.14, pp. 59–60: constraints stated through continuous functions give
continuous correspondences.

* `isLHC_Icc`, `isUHC_Icc`: `Γ(x) = [a(x), b(x)]` is continuous when `a ≤ b` are continuous.
* `ex_3_13a`, `ex_3_13b`: `Γ(x) = [0, x]` on `ℝ₊` and `Γ(x) = [0, f(x)]` are continuous.
* `budget`, `ex_3_13c`: the production possibility correspondence is compact-valued and
  continuous: it is the projection (Exercises 3.11b, 3.12b) of the allocation correspondence
  `allocGraph`, which is u.h.c. by Theorem 3.4 (`isUHC_allocGraph`) and l.h.c. by rescaling
  allocations (`isLHC_allocGraph`).
* `superlevel`, `isLHC_superlevel`, `isUHC_superlevel`: `Γ(x) = {y ∈ C : H(x, y) ≥ 0}`.
* `ex_3_14a` (monotone `H`), `ex_3_14b` (concave `H` with a Slater point).
* `ex_3_14c`: `Γ(x) = {y : 1 − max{|x|, |y|} ≥ 0}` is l.h.c. exactly at `|x| < 1`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {X : Type*} [MetricSpace X]

/-- `Γ(x) = [a(x), b(x)]` is l.h.c. when `a ≤ b` are continuous. -/
theorem isLHC_Icc {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b) (hab : ∀ x, a x ≤ b x)
    (x : X) : IsLHC (fun x => Icc (a x) (b x)) x := by
  refine ⟨nonempty_Icc.2 (hab x), fun y hy xs hxs => ?_⟩
  refine ⟨0, fun n => max (a (xs n)) (min (b (xs n)) y), fun n _ =>
    ⟨le_max_left _ _, max_le (hab _) (min_le_left _ _)⟩, ?_⟩
  have h := ((ha.tendsto x).comp hxs).max (((hb.tendsto x).comp hxs).min
    (tendsto_const_nhds (x := y)))
  rwa [min_eq_right hy.2, max_eq_right hy.1] at h

/-- `Γ(x) = [a(x), b(x)]` is compact-valued and u.h.c. when `a ≤ b` are continuous. -/
theorem isUHC_Icc {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b) (hab : ∀ x, a x ≤ b x)
    (x : X) : IsUHC (fun x => Icc (a x) (b x)) x := by
  refine ⟨nonempty_Icc.2 (hab x), fun xs hxs ys hys => ?_⟩
  have hta := (ha.tendsto x).comp hxs
  have htb := (hb.tendsto x).comp hxs
  obtain ⟨A, hA⟩ := hta.bddBelow_range
  obtain ⟨B, hB⟩ := htb.bddAbove_range
  have hmem : ∀ n, ys n ∈ Icc A B := fun n =>
    ⟨(hA ⟨n, rfl⟩).trans (hys n).1, (hys n).2.trans (hB ⟨n, rfl⟩)⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  refine ⟨y, ⟨?_, ?_⟩, φ, hφ, hlim⟩
  · exact le_of_tendsto_of_tendsto (hta.comp hφ.tendsto_atTop) hlim
      (Eventually.of_forall fun n => (hys (φ n)).1)
  · exact le_of_tendsto_of_tendsto hlim (htb.comp hφ.tendsto_atTop)
      (Eventually.of_forall fun n => (hys (φ n)).2)

/-- **Ex 3.13a.** `Γ(x) = [0, x]` on `ℝ₊` is continuous. -/
theorem ex_3_13a (x : NNR) :
    IsLHC (fun x : NNR => Icc 0 (x : ℝ)) x ∧ IsUHC (fun x : NNR => Icc 0 (x : ℝ)) x :=
  ⟨isLHC_Icc continuous_const continuous_subtype_val (fun x => x.2) x,
    isUHC_Icc continuous_const continuous_subtype_val (fun x => x.2) x⟩

/-- **Ex 3.13b.** For continuous `f ≥ 0`, `Γ(x) = [0, f(x)]` is continuous. -/
theorem ex_3_13b {f : X → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (x : X) :
    IsLHC (fun x => Icc 0 (f x)) x ∧ IsUHC (fun x => Icc 0 (f x)) x :=
  ⟨isLHC_Icc continuous_const hf hf0 x, isUHC_Icc continuous_const hf hf0 x⟩

/-- **Ex 3.14c.** For `H(x, y) = 1 − max{|x|, |y|}`, `Γ(x) = {y : H(x, y) ≥ 0}` is `[−1, 1]` for
`|x| ≤ 1` and empty otherwise; it is l.h.c. exactly where `|x| < 1`. (Where `|x| = 1` no
`ŷ ∈ Γ(x)` has `H(x, ŷ) > 0`, the hypothesis of Ex 3.14b.) -/
theorem ex_3_14c (x : ℝ) :
    IsLHC (fun x : ℝ => {y : ℝ | 0 ≤ 1 - max |x| |y|}) x ↔ |x| < 1 := by
  have hΓ : ∀ x : ℝ, {y : ℝ | 0 ≤ 1 - max |x| |y|} = if |x| ≤ 1 then Set.Icc (-1) 1 else ∅ := by
    intro x
    ext y
    simp only [Set.mem_ofPred_eq, sub_nonneg, max_le_iff]
    split_ifs with h
    · simp [abs_le, h]
    · simp [h]
  rw [show (fun x : ℝ => {y : ℝ | 0 ≤ 1 - max |x| |y|}) =
    fun x => if |x| ≤ 1 then Set.Icc (-1) 1 else ∅ from funext hΓ]
  constructor
  · intro h
    by_contra hx
    push Not at hx
    -- approach `x` from outside `[−1, 1]`, where `Γ` is empty
    have hx0 : 0 < |x| := by linarith
    have hxs : Tendsto (fun n : ℕ => x * (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 x) := by
      have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1).const_mul x
      rwa [add_zero, mul_one] at this
    obtain ⟨y, hy⟩ := h.1
    obtain ⟨N, ys, hys, -⟩ := h.2 y hy _ hxs
    have hN := hys N le_rfl
    have hpos : 0 < 1 / ((N : ℝ) + 1) := by positivity
    have habs : |x * (1 + 1 / ((N : ℝ) + 1))| = |x| * (1 + 1 / ((N : ℝ) + 1)) := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 + 1 / ((N : ℝ) + 1) by linarith)]
    have hlt : ¬ |x * (1 + 1 / ((N : ℝ) + 1))| ≤ 1 := by
      rw [habs]
      nlinarith
    simp only [hlt, ↓reduceIte] at hN
    exact hN
  · intro hx
    refine ⟨by simp only [hx.le, ↓reduceIte]; exact ⟨0, by norm_num, by norm_num⟩,
      fun y hy xs hxs => ?_⟩
    simp only [hx.le, ↓reduceIte] at hy
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((continuous_abs.tendsto x |>.comp hxs).eventually
      (gt_mem_nhds hx))
    refine ⟨N, fun _ => y, fun n hn => ?_, tendsto_const_nhds⟩
    have : |xs n| ≤ 1 := (hN n hn).le
    simp only [this, ↓reduceIte]
    exact hy

/-! ### Exercise 3.13c: the production possibility correspondence -/

/-- The nonnegative orthant `ℝ^l₊`. -/
abbrev Orthant (l : ℕ) := {x : Fin l → ℝ // 0 ≤ x}

variable {l m : ℕ}

/-- **Ex 3.13c.** Outputs `y ∈ ℝ^l₊` producible from the input vector `x ∈ ℝ^l₊` with shock
`z ∈ ℝ^m`: the inputs are split as `x¹ + ⋯ + xˡ ≤ x`, `xⁱ ∈ ℝ^l₊`, and `0 ≤ yᵢ ≤ fᵢ(xⁱ, z)`. -/
def budget (f : Fin l → (Fin l → ℝ) × (Fin m → ℝ) → ℝ) (p : Orthant l × (Fin m → ℝ)) :
    Set (Fin l → ℝ) :=
  {y | 0 ≤ y ∧ ∃ a : Fin l → Fin l → ℝ, 0 ≤ a ∧ ∑ i, a i ≤ p.1.1 ∧ ∀ i, y i ≤ f i (a i, p.2)}

/-- The outputs together with the allocation that produces them. -/
def allocGraph (f : Fin l → (Fin l → ℝ) × (Fin m → ℝ) → ℝ) (p : Orthant l × (Fin m → ℝ)) :
    Set ((Fin l → ℝ) × (Fin l → Fin l → ℝ)) :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ ∑ i, q.2 i ≤ p.1.1 ∧ ∀ i, q.1 i ≤ f i (q.2 i, p.2)}

theorem budget_eq (f : Fin l → (Fin l → ℝ) × (Fin m → ℝ) → ℝ) (p : Orthant l × (Fin m → ℝ)) :
    budget f p = Prod.fst '' allocGraph f p := by
  ext y
  constructor
  · rintro ⟨hy, a, ha, hs, hf⟩
    exact ⟨(y, a), ⟨hy, ha, hs, hf⟩, rfl⟩
  · rintro ⟨q, ⟨hy, ha, hs, hf⟩, rfl⟩
    exact ⟨hy, q.2, ha, hs, hf⟩

theorem allocGraph_nonempty {f : Fin l → (Fin l → ℝ) × (Fin m → ℝ) → ℝ}
    (hf0 : ∀ i a z, 0 ≤ a → 0 ≤ f i (a, z)) (p : Orthant l × (Fin m → ℝ)) :
    (allocGraph f p).Nonempty :=
  ⟨(0, 0), le_rfl, le_rfl, by simpa using p.1.2, fun i => hf0 i 0 p.2 le_rfl⟩

/-- The allocation correspondence has a closed graph and bounded images of bounded sets, so it
is compact-valued and u.h.c. by Theorem 3.4. -/
theorem isUHC_allocGraph {f : Fin l → (Fin l → ℝ) × (Fin m → ℝ) → ℝ} (hf : ∀ i, Continuous (f i))
    (hf0 : ∀ i a z, 0 ≤ a → 0 ≤ f i (a, z)) (p : Orthant l × (Fin m → ℝ)) :
    IsCompact (allocGraph f p) ∧ IsUHC (allocGraph f) p := by
  refine theorem_3_4 (allocGraph_nonempty hf0) ?_ ?_ p
  · have : graph (allocGraph f) =
        {r | 0 ≤ r.2.1} ∩ {r | 0 ≤ r.2.2} ∩ {r | ∑ i, r.2.2 i ≤ r.1.1.1} ∩
          ⋂ i, {r | r.2.1 i ≤ f i (r.2.2 i, r.1.2)} := by
      ext r
      simp only [graph, allocGraph, Set.mem_ofPred_eq, mem_inter_iff, mem_iInter]
      tauto
    rw [this]
    refine ((isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le continuous_const (by fun_prop))).inter
      (isClosed_le (by fun_prop) (by fun_prop)) |>.inter (isClosed_iInter fun i => ?_)
    exact isClosed_le (by fun_prop) ((hf i).comp (by fun_prop))
  · intro S hS
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1
      (Bornology.isBounded_image_subtype_val.2
        (Bornology.isBounded_image_fst_and_snd.2 hS).1)
    obtain ⟨R', hR'⟩ := isBounded_iff_forall_norm_le.1
      (Bornology.isBounded_image_fst_and_snd.2 hS).2
    set K := Metric.closedBall (0 : Fin l → ℝ) R ×ˢ Metric.closedBall (0 : Fin m → ℝ) R'
    have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
    have hC : ∀ i, ∃ C, ∀ q ∈ K, ‖f i q‖ ≤ C := fun i =>
      hK.exists_bound_of_continuousOn (hf i).continuousOn
    choose C hC using hC
    refine isBounded_iff_forall_norm_le.2 ⟨max (∑ i, |C i|) R, fun q hq => ?_⟩
    simp only [image, mem_iUnion] at hq
    obtain ⟨r, hr, hy0, ha0, hs, hfy⟩ := hq
    have hxR : ‖r.1.1‖ ≤ R := hR _ ⟨r.1, ⟨r, hr, rfl⟩, rfl⟩
    have hzR : ‖r.2‖ ≤ R' := hR' _ ⟨r, hr, rfl⟩
    -- each allocated input vector lies in the ball of radius `R`
    have hai : ∀ i, ‖q.2 i‖ ≤ R := fun i => by
      refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hxR)).2 fun j => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (ha0 i j)]
      calc q.2 i j ≤ ∑ k, q.2 k j :=
            Finset.single_le_sum (fun k _ => ha0 k j) (Finset.mem_univ i)
        _ = (∑ k, q.2 k) j := (Finset.sum_apply j _ _).symm
        _ ≤ r.1.1 j := hs j
        _ ≤ |r.1.1 j| := le_abs_self _
        _ ≤ R := (norm_le_pi_norm r.1.1 j).trans hxR
    rw [Prod.norm_def]
    refine max_le_max ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (C i))).2
        fun i => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hy0 i)]
      have hfi := hC i (q.2 i, r.2) ⟨by simpa using hai i, by simpa using hzR⟩
      calc q.1 i ≤ f i (q.2 i, r.2) := hfy i
        _ ≤ C i := (le_abs_self _).trans hfi
        _ ≤ |C i| := le_abs_self _
        _ ≤ ∑ i, |C i| := Finset.single_le_sum (fun i _ => abs_nonneg (C i))
            (Finset.mem_univ i)
    · exact (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hxR)).2 hai

/-- The allocation correspondence is l.h.c.: as the inputs `xₙ → x`, scale each allocation
coordinatewise by `xₙⱼ / xⱼ` and cap each output at what the scaled allocation produces. -/
theorem isLHC_allocGraph {f : Fin l → (Fin l → ℝ) × (Fin m → ℝ) → ℝ} (hf : ∀ i, Continuous (f i))
    (hf0 : ∀ i a z, 0 ≤ a → 0 ≤ f i (a, z)) (p : Orthant l × (Fin m → ℝ)) :
    IsLHC (allocGraph f) p := by
  refine ⟨allocGraph_nonempty hf0 p, fun q hq ps hps => ?_⟩
  obtain ⟨hy0, ha0, hs, hfy⟩ := hq
  have hsj : ∀ j, ∑ k, q.2 k j ≤ p.1.1 j := fun j => by
    rw [← Finset.sum_apply j]; exact hs j
  set as : ℕ → Fin l → Fin l → ℝ := fun n i j => q.2 i j * ((ps n).1.1 j / p.1.1 j)
  have has0 : ∀ n, 0 ≤ as n := fun n i j =>
    mul_nonneg (ha0 i j) (div_nonneg ((ps n).1.2 j) (p.1.2 j))
  have hxj : ∀ j, Tendsto (fun n => (ps n).1.1 j) atTop (𝓝 (p.1.1 j)) := fun j =>
    (((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).tendsto p).comp hps
  have hzs : Tendsto (fun n => (ps n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hps
  have has : ∀ i, Tendsto (fun n => as n i) atTop (𝓝 (q.2 i)) := fun i =>
    tendsto_pi_nhds.2 fun j => by
      by_cases hx : p.1.1 j = 0
      · have h0 : q.2 i j = 0 := le_antisymm
          ((Finset.single_le_sum (fun k _ => ha0 k j) (Finset.mem_univ i)).trans
            ((hsj j).trans hx.le)) (ha0 i j)
        simp only [as, h0, zero_mul]
        exact tendsto_const_nhds
      · have := ((hxj j).div_const (p.1.1 j)).const_mul (q.2 i j)
        rwa [div_self hx, mul_one] at this
  refine ⟨0, fun n => (fun i => min (q.1 i) (f i (as n i, (ps n).2)), as n),
    fun n _ => ⟨fun i => le_min (hy0 i) (hf0 i _ _ (has0 n i)), has0 n, fun j => ?_,
      fun i => min_le_right _ _⟩, ?_⟩
  · rw [Finset.sum_apply]
    simp only [as]
    rw [← Finset.sum_mul]
    by_cases hx : p.1.1 j = 0
    · rw [hx, div_zero, mul_zero]; exact (ps n).1.2 j
    · calc (∑ k, q.2 k j) * ((ps n).1.1 j / p.1.1 j) ≤ p.1.1 j * ((ps n).1.1 j / p.1.1 j) :=
            mul_le_mul_of_nonneg_right (hsj j) (div_nonneg ((ps n).1.2 j) (p.1.2 j))
        _ = (ps n).1.1 j := mul_div_cancel₀ _ hx
  · refine Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun i => ?_) (tendsto_pi_nhds.2 has)
    have := (tendsto_const_nhds (x := q.1 i)).min
      (((hf i).tendsto (q.2 i, p.2)).comp ((has i).prodMk_nhds hzs))
    rwa [min_eq_left (hfy i)] at this

/-- **Ex 3.13c.** The production possibility correspondence is compact-valued and continuous:
it is the projection of the allocation correspondence (Exercises 3.11b and 3.12b). -/
theorem ex_3_13c {f : Fin l → (Fin l → ℝ) × (Fin m → ℝ) → ℝ} (hf : ∀ i, Continuous (f i))
    (hf0 : ∀ i a z, 0 ≤ a → 0 ≤ f i (a, z)) (p : Orthant l × (Fin m → ℝ)) :
    IsCompact (budget f p) ∧ IsLHC (budget f) p ∧ IsUHC (budget f) p := by
  have he : budget f = fun p => Prod.fst '' allocGraph f p := funext (budget_eq f)
  obtain ⟨hc, hu⟩ := isUHC_allocGraph hf hf0 p
  rw [he]
  exact ⟨(isUHC_proj hc hu).1, isLHC_proj (isLHC_allocGraph hf hf0 p), (isUHC_proj hc hu).2⟩

/-! ### Exercise 3.14: correspondences defined by an inequality -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `Γ(x) = {y ∈ C : H(x, y) ≥ 0}`. -/
def superlevel (C : Set V) (H : X → V → ℝ) (x : X) : Set V := {y | y ∈ C ∧ 0 ≤ H x y}

/-- If every `y ∈ Γ(x)` is joined within `C` to some `ŷ` by a segment on which `H(x, ·) > 0`
except at `y`, then `Γ` is l.h.c. at `x`: move along the segment by the least amount that keeps
`H(xₙ, ·) ≥ 0` (the argument of SLP's Ex 3.14b). -/
theorem isLHC_superlevel {C : Set V} (hC : Convex ℝ C) {H : X → V → ℝ}
    (hH : Continuous fun r : X × V => H r.1 r.2) {x : X} (hne : (superlevel C H x).Nonempty)
    (hpath : ∀ y ∈ superlevel C H x, ∃ ŷ ∈ C, ∀ t ∈ Ioc (0 : ℝ) 1, 0 < H x (y + t • (ŷ - y))) :
    IsLHC (superlevel C H) x := by
  refine ⟨hne, fun y hy xs hxs => ?_⟩
  obtain ⟨ŷ, hŷ, hpos⟩ := hpath y hy
  have hev : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ᶠ n in atTop, 0 < H (xs n) (y + t • (ŷ - y)) :=
    fun t ht => ((hH.tendsto (x, y + t • (ŷ - y))).comp
      (hxs.prodMk_nhds tendsto_const_nhds)).eventually (lt_mem_nhds (hpos t ht))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev 1 ⟨one_pos, le_rfl⟩)
  set S : ℕ → Set ℝ := fun n => Icc 0 1 ∩ {t | 0 ≤ H (xs n) (y + t • (ŷ - y))}
  set lam : ℕ → ℝ := fun n => sInf (S n)
  have hbdd : ∀ n, BddBelow (S n) := fun n => ⟨0, fun t ht => ht.1.1⟩
  have hmem : ∀ n ≥ N, lam n ∈ S n := fun n hn => by
    refine IsClosed.csInf_mem (isClosed_Icc.inter (isClosed_le continuous_const ?_))
      ⟨1, ⟨zero_le_one, le_rfl⟩, (hN n hn).le⟩ (hbdd n)
    exact hH.comp (Continuous.prodMk continuous_const (by fun_prop))
  have hlam0 : ∀ n, 0 ≤ lam n := fun n => Real.sInf_nonneg fun t ht => ht.1.1
  have hlam : Tendsto lam atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hlam0 n),
      fun a ha => ?_⟩
    have ht : min (a / 2) 1 ∈ Ioc (0 : ℝ) 1 := ⟨lt_min (half_pos ha) one_pos, min_le_right _ _⟩
    filter_upwards [hev _ ht] with n hn
    exact (csInf_le (hbdd n) ⟨⟨ht.1.le, ht.2⟩, hn.le⟩).trans_lt
      ((min_le_left _ _).trans_lt (half_lt_self ha))
  refine ⟨N, fun n => y + lam n • (ŷ - y), fun n hn =>
    ⟨hC.add_smul_sub_mem hy.1 hŷ (hmem n hn).1, (hmem n hn).2⟩, ?_⟩
  have := (tendsto_const_nhds (x := y)).add (hlam.smul (tendsto_const_nhds (x := ŷ - y)))
  rwa [zero_smul, add_zero] at this

omit [NormedSpace ℝ V] in
/-- If `C` is closed and the values `yₙ ∈ Γ(xₙ)` along any `xₙ → x` are eventually bounded,
then `Γ` is u.h.c. at `x`. -/
theorem isUHC_superlevel [ProperSpace V] {C : Set V} (hC : IsClosed C) {H : X → V → ℝ}
    (hH : Continuous fun r : X × V => H r.1 r.2) {x : X} (hne : (superlevel C H x).Nonempty)
    (hbdd : ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) → ∀ ys : ℕ → V,
      (∀ n, ys n ∈ superlevel C H (xs n)) → ∃ R, ∀ᶠ n in atTop, ‖ys n‖ ≤ R) :
    IsUHC (superlevel C H) x := by
  refine ⟨hne, fun xs hxs ys hys => ?_⟩
  obtain ⟨R, hR⟩ := hbdd xs hxs ys hys
  obtain ⟨φ, hφ, hφR⟩ := extraction_of_eventually_atTop hR
  obtain ⟨y, -, ψ, hψ, hlim⟩ := (isCompact_closedBall (0 : V) R).tendsto_subseq
    (x := ys ∘ φ) fun n => mem_closedBall_zero_iff.2 (hφR n)
  have hxs' : Tendsto (xs ∘ φ ∘ ψ) atTop (𝓝 x) :=
    hxs.comp (hφ.comp hψ).tendsto_atTop
  refine ⟨y, ⟨hC.mem_of_tendsto hlim (Eventually.of_forall fun n => (hys _).1), ?_⟩,
    φ ∘ ψ, hφ.comp hψ, hlim⟩
  exact ge_of_tendsto' ((hH.tendsto (x, y)).comp (hxs'.prodMk_nhds hlim))
    fun n => (hys (φ (ψ n))).2

/-- **Ex 3.14b.** If `H` is continuous and concave in `y`, `Γ(x)` is bounded and some `ŷ` has
`H(x, ŷ) > 0`, then `Γ(x) = {y : H(x, y) ≥ 0}` is compact and `Γ` is continuous at `x`. -/
theorem ex_3_14b [ProperSpace V] {H : X → V → ℝ} (hH : Continuous fun r : X × V => H r.1 r.2)
    (hconc : ∀ x, ConcaveOn ℝ univ (H x)) {x : X}
    (hbd : Bornology.IsBounded (superlevel univ H x)) (hslater : ∃ ŷ, 0 < H x ŷ) :
    IsLHC (superlevel univ H) x ∧ IsUHC (superlevel univ H) x := by
  obtain ⟨ŷ, hŷ⟩ := hslater
  have hne : (superlevel univ H x).Nonempty := ⟨ŷ, mem_univ _, hŷ.le⟩
  -- along a segment, `H` is at least the chord
  have hchord : ∀ x' y y' (t : ℝ), 0 ≤ t → t ≤ 1 →
      (1 - t) * H x' y + t * H x' y' ≤ H x' (y + t • (y' - y)) := fun x' y y' t h0 h1 => by
    have h := (hconc x').2 (mem_univ y) (mem_univ y') (sub_nonneg.2 h1) h0 (by ring)
    rw [show y + t • (y' - y) = (1 - t) • y + t • y' by
      rw [smul_sub, sub_smul, one_smul]; abel]
    simpa only [smul_eq_mul] using h
  refine ⟨isLHC_superlevel convex_univ hH hne fun y hy => ⟨ŷ, mem_univ _, fun t ht => ?_⟩,
    isUHC_superlevel isClosed_univ hH hne fun xs hxs ys hys => ?_⟩
  · have := hchord x y ŷ t ht.1.le ht.2
    nlinarith [hy.2, sub_nonneg.2 ht.2, ht.1]
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hbd
  have hŷM : ‖ŷ‖ ≤ M := hM ŷ ⟨mem_univ _, hŷ.le⟩
  set R := 2 * M + 1
  have hR : 0 < R := by have := norm_nonneg ŷ; linarith
  refine ⟨R + M, ?_⟩
  have hfar : ∀ᶠ n in atTop, ‖ys n - ŷ‖ ≤ R := by
    by_contra hcon
    rw [not_eventually] at hcon
    have hevŷ : ∀ᶠ n in atTop, 0 < H (xs n) ŷ := ((hH.tendsto (x, ŷ)).comp
      (hxs.prodMk_nhds tendsto_const_nhds)).eventually (lt_mem_nhds hŷ)
    obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop (hcon.and_eventually hevŷ)
    -- the point at distance `R` from `ŷ` towards `yₙ` stays in `Γ(xₙ)` by concavity
    set d : ℕ → ℝ := fun k => ‖ys (φ k) - ŷ‖
    have hd : ∀ k, R < d k := fun k => not_le.1 (hφP k).1
    set w : ℕ → V := fun k => ŷ + (R / d k) • (ys (φ k) - ŷ)
    have hdpos : ∀ k, 0 < d k := fun k => hR.trans (hd k)
    have hw : ∀ k, ‖w k - ŷ‖ = R := fun k => by
      simp only [w, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      rw [abs_of_pos (div_pos hR (hdpos k)), div_mul_cancel₀ _ (hdpos k).ne']
    have hHw : ∀ k, 0 ≤ H (xs (φ k)) (w k) := fun k => by
      have hs0 : 0 ≤ R / d k := (div_pos hR (hdpos k)).le
      have hs1 : R / d k ≤ 1 := (div_le_one (hdpos k)).2 (hd k).le
      have := hchord (xs (φ k)) ŷ (ys (φ k)) (R / d k) hs0 hs1
      have h1 := (hφP k).2
      have h2 := (hys (φ k)).2
      nlinarith [sub_nonneg.2 hs1]
    obtain ⟨wl, hwl, ψ, hψ, hlim⟩ := (isCompact_closedBall ŷ R).tendsto_subseq (x := w)
      fun k => mem_closedBall_iff_norm.2 (hw k).le
    have hHwl : 0 ≤ H x wl := ge_of_tendsto' ((hH.tendsto (x, wl)).comp
      ((hxs.comp (hφ.comp hψ).tendsto_atTop).prodMk_nhds hlim)) fun k => hHw (ψ k)
    have hnorm : ‖wl - ŷ‖ = R := by
      have := ((continuous_norm.comp (continuous_sub_right ŷ)).tendsto wl).comp hlim
      exact tendsto_nhds_unique this (by simp only [Function.comp_def, hw]; exact
        tendsto_const_nhds)
    have hwlM := hM wl ⟨mem_univ _, hHwl⟩
    have := norm_sub_le wl ŷ
    linarith
  filter_upwards [hfar] with n hn
  calc ‖ys n‖ = ‖(ys n - ŷ) + ŷ‖ := by rw [sub_add_cancel]
    _ ≤ ‖ys n - ŷ‖ + ‖ŷ‖ := norm_add_le _ _
    _ ≤ R + M := add_le_add hn hŷM

/-- **Ex 3.14a.** Let `H : ℝ^l₊ × ℝ^m₊ → ℝ` be continuous, strictly increasing in `x`, strictly
decreasing in `y`, with `H(0, 0) = 0`, and let `Γ(x) = {y ≥ 0 : H(x, y) ≥ 0}` be compact-valued
(bounded suffices). Then `Γ` is continuous. At `x ≠ 0` the role of the Slater point `ŷ` of
Ex 3.14b is played by `0`; at `x = 0`, `Γ(0) = {0}` and `0 ∈ Γ(xₙ)` for all `n`. -/
theorem ex_3_14a {H : Orthant l → (Fin m → ℝ) → ℝ}
    (hH : Continuous fun r : Orthant l × (Fin m → ℝ) => H r.1 r.2)
    (hinc : ∀ y, 0 ≤ y → StrictMono fun x => H x y)
    (hdec : ∀ x, StrictAntiOn (H x) {y | 0 ≤ y}) (h00 : H ⟨0, le_rfl⟩ 0 = 0)
    (hcpt : ∀ x, Bornology.IsBounded (superlevel {y | 0 ≤ y} H x)) (x : Orthant l) :
    IsLHC (superlevel {y | 0 ≤ y} H) x ∧ IsUHC (superlevel {y | 0 ≤ y} H) x := by
  set x0 : Orthant l := ⟨0, le_rfl⟩
  have hx0 : ∀ x' : Orthant l, x0 ≤ x' := fun x' => x'.2
  have hzero : ∀ x', (0 : Fin m → ℝ) ∈ superlevel {y | 0 ≤ y} H x' := fun x' =>
    ⟨show (0 : Fin m → ℝ) ≤ 0 from le_rfl, h00 ▸ (hinc 0 le_rfl).monotone (hx0 x')⟩
  refine ⟨?_, isUHC_superlevel (isClosed_Ici (a := (0 : Fin m → ℝ))) hH ⟨0, hzero x⟩
    fun xs hxs ys hys => ?_⟩
  · by_cases hx : x = x0
    · -- `Γ(0) = {0}`
      refine ⟨⟨0, hzero x⟩, fun y hy xs _ => ?_⟩
      have hy0 : y = 0 := by
        by_contra hy0
        have := hdec x (le_refl (0 : Fin m → ℝ)) hy.1
          (lt_of_le_of_ne hy.1 (Ne.symm hy0))
        rw [hx, h00] at this
        rw [hx] at hy
        linarith [hy.2]
      exact ⟨0, fun _ => 0, fun n _ => hzero (xs n), hy0 ▸ tendsto_const_nhds⟩
    · have hxpos : x0 < x := lt_of_le_of_ne (hx0 x) (Ne.symm hx)
      refine isLHC_superlevel (convex_Ici (0 : Fin m → ℝ)) hH ⟨0, hzero x⟩
        fun y hy => ⟨0, show (0 : Fin m → ℝ) ≤ 0 from le_rfl, fun t ht => ?_⟩
      rw [zero_sub, smul_neg, ← sub_eq_add_neg]
      by_cases hy0 : y = 0
      · rw [hy0, smul_zero, sub_zero]
        have := hinc 0 le_rfl hxpos
        simp only [x0, h00] at this
        exact this
      · obtain ⟨i, hi⟩ := Function.ne_iff.1 hy0
        have hyi : 0 < y i := lt_of_le_of_ne (hy.1 i) (Ne.symm hi)
        have hmem : y - t • y ∈ {y : Fin m → ℝ | 0 ≤ y} := fun j => by
          have := hy.1 j
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
          nlinarith [ht.2]
        have hlt : y - t • y < y := Pi.lt_def.2 ⟨fun j => by
          have := hy.1 j
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
          nlinarith [ht.1], i, by
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          nlinarith [ht.1]⟩
        have := hdec x hmem hy.1 hlt
        linarith [hy.2]
  · -- eventually `xₙ ≤ x + 1`, so `yₙ ∈ Γ(x + 1)` by monotonicity
    set xbar : Orthant l := ⟨x.1 + 1, add_nonneg x.2 zero_le_one⟩
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hcpt xbar)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hxs 1 one_pos
    refine ⟨M, eventually_atTop.2 ⟨N, fun n hn => hM _ ⟨(hys n).1, ?_⟩⟩⟩
    have hle : xs n ≤ xbar := fun j => by
      have h1 := (dist_le_pi_dist (xs n).1 x.1 j).trans_lt
        ((Subtype.dist_eq (xs n) x).symm ▸ hN n hn)
      rw [Real.dist_eq] at h1
      have := (abs_lt.1 h1).2
      simp only [xbar, Pi.add_apply, Pi.one_apply]
      linarith
    exact (hys n).2.trans ((hinc _ (hys n).1).monotone hle)

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A differential equation by the contraction mapping theorem

SLP Exercise 3.10, pp. 53–54: `dx/ds = f(x(s))`, `x(0) = c`, with `f` Lipschitz with constant
`B`. On `C[0, τ]` (sup norm) the operator `(Tv)(s) = c + ∫₀ˢ f(v(z)) dz`

* maps `C[0, τ]` into itself (`continuous_picardFn`, `picard`; Ex 3.10a);
* is a contraction with modulus `τB` when `τB < 1` (`ex_3_10b`);
* has a unique fixed point, which is differentiable and is the unique solution of the
  differential equation on `[0, τ]` (`ex_3_10c`).
-/

open Set MeasureTheory intervalIntegral

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {τ : ℝ} {f : ℝ → ℝ} {c : ℝ}

/-- `s ↦ c + ∫₀ˢ f(v(z)) dz`, with `v` extended continuously to `ℝ`. -/
noncomputable def picardFn (hτ : 0 ≤ τ) (f : ℝ → ℝ) (c : ℝ) (v : C(Icc 0 τ, ℝ)) (s : ℝ) : ℝ :=
  c + ∫ z in (0 : ℝ)..s, f (ext hτ v z)

/-- **Ex 3.10a.** `Tv` is continuous. -/
theorem continuous_picardFn (hτ : 0 ≤ τ) (hf : Continuous f) (v : C(Icc 0 τ, ℝ)) :
    Continuous (picardFn hτ f c v) :=
  continuous_const.add (intervalIntegral.continuous_primitive
    (fun a b => (hf.comp (continuous_ext hτ v)).intervalIntegrable a b) 0)

/-- **Ex 3.10a.** The operator `T : C[0, τ] → C[0, τ]`. -/
noncomputable def picard (hτ : 0 ≤ τ) (hf : Continuous f) (c : ℝ) (v : C(Icc 0 τ, ℝ)) :
    C(Icc 0 τ, ℝ) :=
  ⟨fun s => picardFn hτ f c v s, (continuous_picardFn hτ hf v).comp continuous_subtype_val⟩

theorem picard_apply (hτ : 0 ≤ τ) (hf : Continuous f) (v : C(Icc 0 τ, ℝ)) (s : Icc 0 τ) :
    picard hτ hf c v s = c + ∫ z in (0 : ℝ)..s, f (ext hτ v z) := rfl

/-- **Ex 3.10b.** If `|f(a) − f(b)| ≤ B|a − b|` and `0 < τ`, `τB < 1`, then `T` is a contraction
on `C[0, τ]` with modulus `τB`. -/
theorem ex_3_10b {B : ℝ} (hB : 0 < B) (hf : Continuous f)
    (hlip : ∀ a b, |f a - f b| ≤ B * |a - b|) (hτ : 0 < τ) (hτB : τ * B < 1) :
    IsContraction (picard hτ.le hf c) (τ * B) := by
  refine ⟨mul_pos hτ hB, hτB, fun v w => ?_⟩
  refine (ContinuousMap.dist_le (mul_nonneg (mul_pos hτ hB).le dist_nonneg)).2 fun s => ?_
  have hpt : ∀ z, ‖f (ext hτ.le v z) - f (ext hτ.le w z)‖ ≤ B * dist v w := fun z => by
    rw [Real.norm_eq_abs]
    refine (hlip _ _).trans (mul_le_mul_of_nonneg_left ?_ hB.le)
    change |v (projIcc 0 τ hτ.le z) - w (projIcc 0 τ hτ.le z)| ≤ dist v w
    rw [← Real.dist_eq]
    exact ContinuousMap.dist_apply_le_dist _
  have hint : ∀ u : C(Icc 0 τ, ℝ), IntervalIntegrable (fun z => f (ext hτ.le u z)) volume 0 s :=
    fun u => (hf.comp (continuous_ext hτ.le u)).intervalIntegrable _ _
  rw [Real.dist_eq, picard_apply, picard_apply, add_sub_add_left_eq_sub,
    ← intervalIntegral.integral_sub (hint v) (hint w)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (s : ℝ))
    fun z _ => hpt z
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg s.2.1] at h
  calc _ ≤ B * dist v w * s := h
    _ ≤ B * dist v w * τ := mul_le_mul_of_nonneg_left s.2.2
        (mul_nonneg hB.le dist_nonneg)
    _ = τ * B * dist v w := by ring

/-- **Ex 3.10c.** The unique fixed point `v` of `T` on `C[0, τ]` satisfies `v(0) = c` and is
differentiable on `[0, τ]` (one-sided at the ends) with `v′ = f ∘ v`; any `x`, continuous on
`[0, τ]` with `x(0) = c` and `x′(s) = f(x(s))` on `(0, τ)`, coincides with `v` on `[0, τ]`. -/
theorem ex_3_10c {B : ℝ} (hB : 0 < B) (hf : Continuous f)
    (hlip : ∀ a b, |f a - f b| ≤ B * |a - b|) (hτ : 0 < τ) (hτB : τ * B < 1) :
    ∃ v : C(Icc 0 τ, ℝ), picard hτ.le hf c v = v ∧ ext hτ.le v 0 = c ∧
      (∀ s ∈ Icc 0 τ, HasDerivWithinAt (ext hτ.le v) (f (ext hτ.le v s)) (Icc 0 τ) s) ∧
      ∀ x : ℝ → ℝ, ContinuousOn x (Icc 0 τ) → x 0 = c →
        (∀ s ∈ Ioo 0 τ, HasDerivAt x (f (x s)) s) → ∀ s ∈ Icc 0 τ, x s = ext hτ.le v s := by
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (ex_3_10b (c := c) hB hf hlip hτ hτB)
  -- on `[0, τ]` the fixed point is its own Picard integral
  have hfix : EqOn (ext hτ.le v) (picardFn hτ.le f c v) (Icc 0 τ) := fun s hs => by
    rw [ext_of_mem hτ.le v hs]
    conv_lhs => rw [← hv]
    rfl
  have h0 : (0 : ℝ) ∈ Icc 0 τ := ⟨le_rfl, hτ.le⟩
  refine ⟨v, hv, ?_, fun s hs => ?_, fun x hxc hx0 hxd s hs => ?_⟩
  · rw [hfix h0, picardFn, intervalIntegral.integral_same, add_zero]
  · have hd : HasDerivAt (picardFn hτ.le f c v) (f (ext hτ.le v s)) s :=
      ((hf.comp (continuous_ext hτ.le v)).integral_hasStrictDerivAt 0 s).hasDerivAt.const_add c
    exact hd.hasDerivWithinAt.congr hfix (hfix hs)
  · -- `x` restricted to `[0, τ]` is a fixed point of `T`
    set xv : C(Icc 0 τ, ℝ) :=
      ⟨fun u => x u, hxc.comp_continuous continuous_subtype_val fun u => u.2⟩
    have hxv : picard hτ.le hf c xv = xv := by
      ext u
      rw [picard_apply]
      have hsub : Icc 0 (u : ℝ) ⊆ Icc 0 τ := Icc_subset_Icc le_rfl u.2.2
      have hcongr : ∫ z in (0 : ℝ)..u, f (ext hτ.le xv z) = ∫ z in (0 : ℝ)..u, f (x z) := by
        refine intervalIntegral.integral_congr fun z hz => ?_
        rw [uIcc_of_le u.2.1] at hz
        simp only [ext_of_mem hτ.le xv (hsub hz)]
        rfl
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le u.2.1 (hxc.mono hsub)
        (fun z hz => hxd z ⟨hz.1, hz.2.trans_le u.2.2⟩)
        ((hf.comp_continuousOn (hxc.mono hsub)).intervalIntegrable_of_Icc u.2.1)
      rw [hcongr, hftc, hx0]
      change c + (x u - c) = x u
      ring
    have := huniq xv hxv
    rw [ext_of_mem hτ.le v hs, ← this]
    rfl

end StokeyLucasPrescott.MathematicalPreliminaries

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Spaces of continuously differentiable functions

SLP Exercise 3.7, p. 49. A function in `C^k[a, b]` is recorded with its derivatives: a tuple
`F : Fin (k + 1) → C[a, b]` with `F (i + 1) = (F i)′` on `[a, b]` (one-sided at the ends).

* `ckSub`: `C^k[a, b]` as a vector space; `ckNorm α F = ∑ᵢ αᵢ max |F i|`.
* `isCk_iff_integral`: the derivative relations are equivalent to
  `F i (s) = F i (a) + ∫ₐˢ F (i + 1)`.
* `isClosed_ckSub`, `isComplete_ckNorm`: with every `αᵢ > 0` the norm is complete (Ex 3.7c,
  "if"); `ex_3_7a` is the case `k = 1`, `α = (1, 1)`.
* `ex_3_7b`: under `max |f|` alone, `C¹[a, b]` is not complete; the sequence
  `√((t − c)² + 1/(n + 1))` is Cauchy but its limit `|t − c|` is not differentiable, and it is not
  Cauchy in the norm of (a).
* `ex_3_7c_counterexample`: the book's "only if" is false: on `C²[a, b]`,
  `max |f| + max |f″|` (`α = (1, 0, 1)`) is a complete norm, by the interpolation inequality
  `interpolation`. `not_isNorm_of_alpha0`: with `α₀ = 0` the formula is not a norm.
-/

open Set Filter Topology MeasureTheory intervalIntegral

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {a b : ℝ}

theorem ext_zero (hab : a ≤ b) (t : ℝ) : ext hab (0 : C(Icc a b, ℝ)) t = 0 := by
  simpa using ext_smul hab 0 0 t

/-- `|x(t)| ≤ max |x|` for the extension of `x ∈ C[a, b]`. -/
theorem abs_ext_le (hab : a ≤ b) (x : C(Icc a b, ℝ)) (t : ℝ) : |ext hab x t| ≤ ‖x‖ := by
  change |x (projIcc a b hab t)| ≤ ‖x‖
  rw [← Real.norm_eq_abs]
  exact x.norm_coe_le_norm _

/-- `F (i + 1)` is the derivative of `F i` on `[a, b]`, for `i < k`. -/
def IsCk (hab : a ≤ b) (k : ℕ) (F : Fin (k + 1) → C(Icc a b, ℝ)) : Prop :=
  ∀ i : Fin k, ∀ s ∈ Icc a b,
    HasDerivWithinAt (ext hab (F i.castSucc)) (ext hab (F i.succ) s) (Icc a b) s

/-- `C^k[a, b]` (with the derivatives recorded) is a vector space. -/
def ckSub (hab : a ≤ b) (k : ℕ) : Submodule ℝ (Fin (k + 1) → C(Icc a b, ℝ)) where
  carrier := {F | IsCk hab k F}
  zero_mem' i s _ := by
    have : ext hab (0 : C(Icc a b, ℝ)) = fun _ => 0 := funext (ext_zero hab)
    simp only [Pi.zero_apply]
    rw [this]
    exact hasDerivWithinAt_const s _ 0
  add_mem' {F G} hF hG i s hs := by
    have h := (hF i s hs).add (hG i s hs)
    simp only [Pi.add_apply]
    rw [ext_add]
    exact h.congr (fun t _ => ext_add hab _ _ t) (ext_add hab _ _ s)
  smul_mem' r F hF i s hs := by
    have h := (hF i s hs).const_mul r
    simp only [Pi.smul_apply]
    rw [ext_smul]
    exact h.congr (fun t _ => ext_smul hab _ _ t) (ext_smul hab _ _ s)

/-- `‖F‖ = ∑ᵢ αᵢ max_{t ∈ [a,b]} |F i (t)|`. -/
noncomputable def ckNorm {k : ℕ} (α : Fin (k + 1) → ℝ) (F : Fin (k + 1) → C(Icc a b, ℝ)) : ℝ :=
  ∑ i, α i * ‖F i‖

/-- The derivative relations hold iff each `F i` is the integral of `F (i + 1)`. -/
theorem isCk_iff_integral (hab : a ≤ b) {k : ℕ} (F : Fin (k + 1) → C(Icc a b, ℝ)) :
    IsCk hab k F ↔ ∀ i : Fin k, ∀ s ∈ Icc a b,
      ext hab (F i.castSucc) s = ext hab (F i.castSucc) a + ∫ t in a..s, ext hab (F i.succ) t := by
  constructor
  · intro hF i s hs
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl hs.2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
      (continuous_ext hab _).continuousOn (fun z hz => ?_)
      ((continuous_ext hab _).intervalIntegrable _ _)]
    · ring
    · exact (hF i z (hsub (Ioo_subset_Icc_self hz))).hasDerivAt
        (Icc_mem_nhds hz.1 (hz.2.trans_le hs.2))
  · intro hF i s hs
    have hd : HasDerivAt (fun u => ext hab (F i.castSucc) a + ∫ t in a..u, ext hab (F i.succ) t)
        (ext hab (F i.succ) s) s :=
      ((continuous_ext hab _).integral_hasStrictDerivAt a s).hasDerivAt.const_add _
    exact hd.hasDerivWithinAt.congr (fun u hu => hF i u hu) (hF i s hs)

/-- `C^k[a, b]` is closed in `C[a, b]^{k+1}` under the sup norm on each coordinate. -/
theorem isClosed_ckSub (hab : a ≤ b) (k : ℕ) :
    IsClosed (ckSub hab k : Set (Fin (k + 1) → C(Icc a b, ℝ))) := by
  have hev : ∀ (j : Fin (k + 1)) (s : ℝ),
      Continuous fun F : Fin (k + 1) → C(Icc a b, ℝ) => ext hab (F j) s := fun j s =>
    continuous_eval.comp ((continuous_apply j).prodMk continuous_const)
  have hint : ∀ (j : Fin (k + 1)) (s : ℝ),
      Continuous fun F : Fin (k + 1) → C(Icc a b, ℝ) => ∫ t in a..s, ext hab (F j) t :=
    fun j s => intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (F : Fin (k + 1) → C(Icc a b, ℝ)) t => ext hab (F j) t) (μ := volume)
      (continuous_eval.comp (((continuous_apply j).comp continuous_fst).prodMk
        ((continuous_projIcc (h := hab)).comp continuous_snd))) a s
  have : (ckSub hab k : Set (Fin (k + 1) → C(Icc a b, ℝ))) = ⋂ i : Fin k, ⋂ s ∈ Icc a b,
      {F | ext hab (F i.castSucc) s = ext hab (F i.castSucc) a +
        ∫ t in a..s, ext hab (F i.succ) t} := by
    ext F
    simp only [SetLike.mem_coe, mem_iInter]
    exact isCk_iff_integral hab F
  rw [this]
  exact isClosed_iInter fun i => isClosed_biInter fun s _ =>
    isClosed_eq (hev _ s) ((hev _ a).add (hint _ s))

/-- **Ex 3.7c ("if").** With every `αᵢ > 0`, `ckNorm α` is a norm on `C^k[a, b]`. -/
theorem isNorm_ckNorm (hab : a ≤ b) {k : ℕ} {α : Fin (k + 1) → ℝ} (hα : ∀ i, 0 < α i) :
    IsNorm fun F : ckSub hab k => ckNorm α F.1 where
  nonneg F := Finset.sum_nonneg fun i _ => mul_nonneg (hα i).le (norm_nonneg _)
  eq_zero F := by
    constructor
    · intro h
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_nonneg (hα i).le (norm_nonneg (F.1 i))).1 h
      ext1
      funext i
      exact norm_eq_zero.1 ((mul_eq_zero.1 (h0 i (Finset.mem_univ i))).resolve_left (hα i).ne')
    · rintro rfl
      simp [ckNorm]
  smul r F := by
    simp only [ckNorm, Submodule.coe_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  triangle F G := by
    simp only [ckNorm, Submodule.coe_add, Pi.add_apply, ← Finset.sum_add_distrib, ← mul_add]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (norm_add_le _ _) (hα i).le

/-- Each coordinate is bounded by the weighted norm. -/
theorem norm_le_ckNorm {k : ℕ} {α : Fin (k + 1) → ℝ} (hα : ∀ i, 0 < α i)
    (F : Fin (k + 1) → C(Icc a b, ℝ)) :
    ‖F‖ ≤ ckNorm α F / Finset.univ.inf' Finset.univ_nonempty α := by
  have hm : 0 < Finset.univ.inf' Finset.univ_nonempty α :=
    (Finset.lt_inf'_iff _).2 fun i _ => hα i
  have hN : 0 ≤ ckNorm α F := Finset.sum_nonneg fun i _ => mul_nonneg (hα i).le (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg (div_nonneg hN hm.le)).2 fun i => ?_
  rw [le_div_iff₀ hm]
  calc ‖F i‖ * Finset.univ.inf' Finset.univ_nonempty α ≤ ‖F i‖ * α i :=
        mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ i)) (norm_nonneg _)
    _ = α i * ‖F i‖ := mul_comm _ _
    _ ≤ ckNorm α F := Finset.single_le_sum (f := fun j => α j * ‖F j‖)
        (fun j _ => mul_nonneg (hα j).le (norm_nonneg _)) (Finset.mem_univ i)

/-- The weighted norm is bounded by `∑ αᵢ` times the sup over coordinates. -/
theorem ckNorm_le {k : ℕ} {α : Fin (k + 1) → ℝ} (hα : ∀ i, 0 ≤ α i)
    (F : Fin (k + 1) → C(Icc a b, ℝ)) : ckNorm α F ≤ (∑ i, α i) * ‖F‖ := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm F i) (hα i)

/-- **Ex 3.7c ("if").** With every `αᵢ > 0`, `C^k[a, b]` is complete under `ckNorm α`. -/
theorem isComplete_ckNorm (hab : a ≤ b) {k : ℕ} {α : Fin (k + 1) → ℝ} (hα : ∀ i, 0 < α i) :
    IsCompleteFor fun F G : ckSub hab k => ckNorm α (F.1 - G.1) := by
  intro x hx
  have hm : 0 < Finset.univ.inf' Finset.univ_nonempty α :=
    (Finset.lt_inf'_iff _).2 fun i _ => hα i
  have hcs : CauchySeq fun n => (x n).1 := Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hx (Finset.univ.inf' Finset.univ_nonempty α * ε) (mul_pos hm hε)
    refine ⟨N, fun p hp q hq => ?_⟩
    rw [dist_eq_norm]
    refine (norm_le_ckNorm hα _).trans_lt ?_
    rw [div_lt_iff₀ hm, mul_comm ε]
    exact hN p hp q hq
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have hLmem : L ∈ ckSub hab k :=
    (isClosed_ckSub hab k).mem_of_tendsto hL (Eventually.of_forall fun n => (x n).2)
  have hA : 0 < ∑ i, α i := Finset.sum_pos (fun i _ => hα i) Finset.univ_nonempty
  refine ⟨⟨L, hLmem⟩, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hL (ε / ∑ i, α i) (div_pos hε hA)
  refine ⟨N, fun n hn => ?_⟩
  calc ckNorm α ((x n).1 - L) ≤ (∑ i, α i) * ‖(x n).1 - L‖ := ckNorm_le (fun i => (hα i).le) _
    _ < (∑ i, α i) * (ε / ∑ i, α i) := by
        rw [← dist_eq_norm]; exact mul_lt_mul_of_pos_left (hN n hn) hA
    _ = ε := mul_div_cancel₀ _ hA.ne'

/-- **Ex 3.7a.** `C¹[a, b]` with `‖f‖ = max |f| + max |f′|` is a Banach space. -/
theorem ex_3_7a (hab : a ≤ b) :
    IsNorm (fun F : ckSub hab 1 => ‖F.1 0‖ + ‖F.1 1‖) ∧
      IsCompleteFor fun F G : ckSub hab 1 => ‖F.1 0 - G.1 0‖ + ‖F.1 1 - G.1 1‖ := by
  have hα : ∀ i, 0 < (fun _ : Fin 2 => (1 : ℝ)) i := fun _ => one_pos
  have h : ∀ F : Fin 2 → C(Icc a b, ℝ), ckNorm (fun _ => 1) F = ‖F 0‖ + ‖F 1‖ := fun F => by
    simp [ckNorm, Fin.sum_univ_two]
  constructor
  · have := isNorm_ckNorm hab hα
    simp only [h] at this
    exact this
  · have := isComplete_ckNorm hab hα
    simp only [h, Pi.sub_apply] at this
    exact this

/-! ### Exercise 3.7b: the sup norm on `C¹` -/

/-- A continuous `g : ℝ → ℝ` restricted to `[a, b]`. -/
def restrictC {g : ℝ → ℝ} (hg : Continuous g) : C(Icc a b, ℝ) :=
  ⟨fun u => g u, hg.comp continuous_subtype_val⟩

theorem ext_restrictC (hab : a ≤ b) {g : ℝ → ℝ} (hg : Continuous g) {t : ℝ} (ht : t ∈ Icc a b) :
    ext hab (restrictC hg) t = g t := by
  rw [ext_of_mem hab _ ht]; rfl

/-- A function differentiable on `ℝ` with continuous derivative gives an element of `C¹[a, b]`. -/
def mk1 (hab : a ≤ b) {g g' : ℝ → ℝ} (hg : Continuous g) (hg' : Continuous g')
    (hd : ∀ s, HasDerivAt g (g' s) s) : ckSub hab 1 :=
  ⟨![restrictC hg, restrictC hg'], fun i s hs => by
    rw [Subsingleton.elim i 0]
    change HasDerivWithinAt (ext hab (restrictC hg)) (ext hab (restrictC hg') s) (Icc a b) s
    rw [ext_restrictC hab hg' hs]
    exact (hd s).hasDerivWithinAt.congr (fun t ht => ext_restrictC hab hg ht)
      (ext_restrictC hab hg hs)⟩

/-- **Ex 3.7b.** On `C¹[a, b]` (`a < b`), `max |f|` is a norm. -/
theorem isNorm_sup_C1 (hab : a < b) : IsNorm fun F : ckSub hab.le 1 => ‖F.1 0‖ where
  nonneg _ := norm_nonneg _
  eq_zero F := by
    constructor
    · intro h
      have h0 : F.1 0 = 0 := norm_eq_zero.1 h
      -- the derivative of the zero function is zero
      have h1 : F.1 1 = 0 := by
        ext u
        have hd := F.2 0 u u.2
        change HasDerivWithinAt (ext hab.le (F.1 0)) (ext hab.le (F.1 1) u) (Icc a b) u at hd
        rw [h0, show ext hab.le (0 : C(Icc a b, ℝ)) = fun _ => 0 from funext (ext_zero hab.le)]
          at hd
        have := (uniqueDiffOn_Icc hab u u.2).eq_deriv _ hd (hasDerivWithinAt_const _ _ 0)
        rw [ext_of_mem hab.le _ u.2] at this
        simpa using this
      ext1
      funext i
      fin_cases i
      · exact h0
      · exact h1
    · rintro rfl; simp
  smul r F := by simp [norm_smul]
  triangle F G := by simpa using norm_add_le (F.1 0) (G.1 0)

/-- `√((t − c)² + 1/(n + 1))`. -/
noncomputable def sqrtSeq (c : ℝ) (n : ℕ) (t : ℝ) : ℝ := √((t - c) ^ 2 + 1 / ((n : ℝ) + 1))

/-- Its derivative `(t − c)/√((t − c)² + 1/(n + 1))`. -/
noncomputable def sqrtSeq' (c : ℝ) (n : ℕ) (t : ℝ) : ℝ := (t - c) / sqrtSeq c n t

theorem sqrtSeq_pos (c : ℝ) (n : ℕ) (t : ℝ) : 0 < sqrtSeq c n t :=
  Real.sqrt_pos.2 (by positivity)

theorem continuous_sqrtSeq (c : ℝ) (n : ℕ) : Continuous (sqrtSeq c n) := by
  unfold sqrtSeq; fun_prop

theorem continuous_sqrtSeq' (c : ℝ) (n : ℕ) : Continuous (sqrtSeq' c n) :=
  (continuous_id.sub continuous_const).div (continuous_sqrtSeq c n)
    fun t => (sqrtSeq_pos c n t).ne'

theorem hasDerivAt_sqrtSeq (c : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (sqrtSeq c n) (sqrtSeq' c n t) t := by
  have hne : (t - c) ^ 2 + 1 / ((n : ℝ) + 1) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x => x - c) 1 t := (hasDerivAt_id t).sub_const c
  have h2 : HasDerivAt (fun x => (x - c) ^ 2) (2 * (t - c)) t := by
    simpa [Function.comp_def] using (hasDerivAt_pow 2 (t - c)).comp t h1
  refine ((h2.add_const (1 / ((n : ℝ) + 1))).sqrt hne).congr_deriv ?_
  unfold sqrtSeq' sqrtSeq
  rw [mul_div_mul_left _ _ two_ne_zero]

/-- `|√(x² + ε) − |x|| ≤ √ε`. -/
theorem abs_sqrt_sub_abs_le (x ε : ℝ) (hε : 0 ≤ ε) : abs (√(x ^ 2 + ε) - |x|) ≤ √ε := by
  have h1 : |x| ≤ √(x ^ 2 + ε) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have h2 : √(x ^ 2 + ε) ≤ |x| + √ε := by
    rw [← Real.sqrt_sq (add_nonneg (abs_nonneg x) (Real.sqrt_nonneg ε))]
    refine Real.sqrt_le_sqrt ?_
    have := Real.sq_sqrt hε
    nlinarith [sq_abs x, abs_nonneg x, Real.sqrt_nonneg ε]
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Ex 3.7b.** Under `max |f|`, `C¹[a, b]` is not complete: with `c = (a + b)/2`, the functions
`√((t − c)² + 1/(n + 1))` form a Cauchy sequence with no limit in `C¹[a, b]` (its uniform limit
`|t − c|` has a kink at `c`). The sequence is not Cauchy in the norm of part (a). -/
theorem ex_3_7b (hab : a < b) :
    ¬ IsCompleteFor (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖) ∧
      ∃ x : ℕ → ckSub hab.le 1, IsCauchy (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖) x ∧
        (¬ ∃ G, Converges (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖) x G) ∧
        ¬ IsCauchy (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖ + ‖F.1 1 - G.1 1‖) x := by
  set c := (a + b) / 2
  have hc : c ∈ Ioo a b := ⟨by simp only [c]; linarith, by simp only [c]; linarith⟩
  set x : ℕ → ckSub hab.le 1 := fun n =>
    mk1 hab.le (continuous_sqrtSeq c n) (continuous_sqrtSeq' c n) (hasDerivAt_sqrtSeq c n)
  have hx0 : ∀ n, (x n).1 0 = restrictC (continuous_sqrtSeq c n) := fun n => rfl
  have hk : Continuous fun t : ℝ => |t - c| := by fun_prop
  -- uniform convergence to `|t − c|`
  have hconv : Tendsto (fun n => (x n).1 0) atTop (𝓝 (restrictC hk)) := by
    have hsq : Tendsto (fun n : ℕ => √(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [Real.sqrt_zero] at this
    refine squeeze_zero_norm (fun n => ?_) hsq |> tendsto_iff_norm_sub_tendsto_zero.2
    rw [norm_norm]
    refine (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).2 fun u => ?_
    rw [hx0, ContinuousMap.sub_apply, Real.norm_eq_abs]
    exact abs_sqrt_sub_abs_le _ _ (by positivity)
  have hcauchy : IsCauchy (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖) x := fun ε hε => by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hconv.cauchySeq ε hε
    exact ⟨N, fun n hn m hm => by
      change ‖(x n).1 0 - (x m).1 0‖ < ε
      rw [← dist_eq_norm]; exact hN n hn m hm⟩
  have hnolim : ¬ ∃ G, Converges (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖) x G := by
    rintro ⟨G, hG⟩
    have hG' : Tendsto (fun n => (x n).1 0) atTop (𝓝 (G.1 0)) := Metric.tendsto_atTop.2
      fun ε hε => by
        obtain ⟨N, hN⟩ := hG ε hε
        exact ⟨N, fun n hn => by rw [dist_eq_norm]; exact hN n hn⟩
    have heq : G.1 0 = restrictC hk := tendsto_nhds_unique hG' hconv
    -- `G 0 = |t − c|` on `[a, b]` would be differentiable at the interior point `c`
    have hd := G.2 0 c (Ioo_subset_Icc_self hc)
    change HasDerivWithinAt (ext hab.le (G.1 0)) _ (Icc a b) c at hd
    have hd' := (hd.hasDerivAt (Icc_mem_nhds hc.1 hc.2)).congr_of_eventuallyEq
      (f₁ := fun t => |t - c|) (by
        filter_upwards [Icc_mem_nhds hc.1 hc.2] with t ht
        rw [heq, ext_restrictC hab.le hk ht])
    have habs : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
      have hcomp := (show DifferentiableAt ℝ (fun t => |t - c|) (0 + c) by
        rw [zero_add]; exact hd'.differentiableAt).comp (0 : ℝ)
        ((differentiableAt_id).add_const c)
      have : ((fun t => |t - c|) ∘ fun t => id t + c) = abs := funext fun t => by simp
      rwa [this] at hcomp
    exact not_differentiableAt_abs_zero habs
  refine ⟨fun hcomp => hnolim (hcomp x hcauchy), x, hcauchy, hnolim, fun hC1 => ?_⟩
  -- a Cauchy sequence for the norm of (a) converges in it, hence in `max |f|`
  obtain ⟨G, hG⟩ := (ex_3_7a hab.le).2 x hC1
  exact hnolim ⟨G, fun ε hε => by
    obtain ⟨N, hN⟩ := hG ε hε
    exact ⟨N, fun n hn => lt_of_le_of_lt (le_add_of_nonneg_right (norm_nonneg _)) (hN n hn)⟩⟩

/-! ### Exercise 3.7c: weighted norms on `C^k` -/

/-- **Ex 3.7c**, the weight `α₀`: if `α₀ = 0` the formula is not a norm, since the constant `1`
(with zero derivatives) gets size `0`. -/
theorem not_isNorm_of_alpha0 (hab : a ≤ b) {k : ℕ} {α : Fin (k + 1) → ℝ} (h0 : α 0 = 0) :
    ¬ IsNorm fun F : ckSub hab k => ckNorm α F.1 := by
  intro hN
  have hone : ext hab (1 : C(Icc a b, ℝ)) = fun _ => 1 := funext fun _ => rfl
  have hzero : ext hab (0 : C(Icc a b, ℝ)) = fun _ => 0 := funext (ext_zero hab)
  set F : Fin (k + 1) → C(Icc a b, ℝ) := fun i => if i = 0 then 1 else 0
  have hF : F ∈ ckSub hab k := fun i s _ => by
    have hs : F i.succ = 0 := by simp [F]
    rw [hs, hzero]
    by_cases hi : i.castSucc = 0
    · have : F i.castSucc = 1 := by simp [F, hi]
      rw [this, hone]
      exact hasDerivWithinAt_const _ _ _
    · have : F i.castSucc = 0 := by simp [F, hi]
      rw [this, hzero]
      exact hasDerivWithinAt_const _ _ _
  have hsize : ckNorm α F = 0 := Finset.sum_eq_zero fun i _ => by
    by_cases hi : i = 0
    · rw [hi, h0, zero_mul]
    · simp [F, hi]
  have := (hN.eq_zero ⟨F, hF⟩).1 hsize
  have h1 : F 0 = 0 := congrFun (congrArg Subtype.val this) 0
  have h2 : (1 : C(Icc a b, ℝ)) ⟨a, le_rfl, hab⟩ = 0 := by
    have : F 0 = 1 := by simp [F]
    rw [← this, h1]; rfl
  exact one_ne_zero h2

/-- **Interpolation.** On `C²[a, b]`, `max |f′| ≤ (4/(b − a)) max |f| + ((b − a)/2) max |f″|`:
compare `f(v) − f(t)` with `(v − t) f′(t)` over a step of length `(b − a)/2`. -/
theorem interpolation (hab : a < b) (F : ckSub hab.le 2) :
    ‖F.1 1‖ ≤ 4 / (b - a) * ‖F.1 0‖ + (b - a) / 2 * ‖F.1 2‖ := by
  set g : Fin 3 → ℝ → ℝ := fun i => ext hab.le (F.1 i)
  have hcont : ∀ i, Continuous (g i) := fun i => continuous_ext hab.le _
  have hid := (isCk_iff_integral hab.le F.1).1 F.2
  -- differences of `g i` are integrals of `g (i + 1)`
  have hdiff : ∀ (i : Fin 2) (t u : ℝ), t ∈ Icc a b → u ∈ Icc a b →
      g i.castSucc u - g i.castSucc t = ∫ z in t..u, g i.succ z := fun i t u ht hu => by
    have h1 := hid i u hu
    have h2 := hid i t ht
    change g i.castSucc u = g i.castSucc a + ∫ z in a..u, g i.succ z at h1
    change g i.castSucc t = g i.castSucc a + ∫ z in a..t, g i.succ z at h2
    rw [h1, h2, add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      ((hcont _).intervalIntegrable _ _) ((hcont _).intervalIntegrable _ _)]
  have hbd : ∀ i z, |g i z| ≤ ‖F.1 i‖ := fun i z => abs_ext_le hab.le _ z
  set h := (b - a) / 2
  have hh : 0 < h := by simp only [h]; linarith
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun u => ?_
  set t : ℝ := u.1
  have ht : t ∈ Icc a b := u.2
  rw [Real.norm_eq_abs, ← ext_of_mem hab.le _ ht]
  change |g 1 t| ≤ _
  -- a point `v ∈ [a, b]` at distance `h` from `t`
  obtain ⟨v, hv, hvt⟩ : ∃ v ∈ Icc a b, |v - t| = h := by
    by_cases hc : t ≤ (a + b) / 2
    · exact ⟨t + h, ⟨by linarith [ht.1], by simp only [h]; linarith⟩, by
        rw [add_sub_cancel_left, abs_of_pos hh]⟩
    · exact ⟨t - h, ⟨by simp only [h]; linarith, by linarith [ht.2]⟩, by
        rw [sub_sub_cancel_left, abs_neg, abs_of_pos hh]⟩
  have hsub : uIcc t v ⊆ Icc a b := uIcc_subset_Icc ht hv
  -- `g 1` moves by at most `h ‖F 2‖` between `t` and `v`
  have hclose : ∀ z ∈ uIoc t v, ‖g 1 z - g 1 t‖ ≤ ‖F.1 2‖ * h := fun z hz => by
    have hz' := uIoc_subset_uIcc hz
    have := hdiff 1 t z ht (hsub hz')
    change g 1 z - g 1 t = ∫ w in t..z, g 2 w at this
    rw [this]
    calc ‖∫ w in t..z, g 2 w‖ ≤ ‖F.1 2‖ * |z - t| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun w _ =>
            (Real.norm_eq_abs _).trans_le (hbd 2 w)
      _ ≤ ‖F.1 2‖ * h := by
          rw [← hvt]
          exact mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hz') (norm_nonneg _)
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hclose
  have hd0 : g 0 v - g 0 t = ∫ z in t..v, g 1 z := hdiff 0 t v ht hv
  rw [intervalIntegral.integral_sub ((hcont 1).intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul,
    ← hd0, Real.norm_eq_abs, hvt] at hI
  change |g 0 v - g 0 t - (v - t) * g 1 t| ≤ ‖F.1 2‖ * h * h at hI
  have hg0 : |g 0 v - g 0 t| ≤ 2 * ‖F.1 0‖ := by
    have := abs_sub (g 0 v) (g 0 t)
    linarith [hbd 0 v, hbd 0 t]
  have hstep : h * |g 1 t| ≤ 2 * ‖F.1 0‖ + ‖F.1 2‖ * h * h := by
    have : |(v - t) * g 1 t| ≤ |g 0 v - g 0 t| + |g 0 v - g 0 t - (v - t) * g 1 t| := by
      have := abs_sub (g 0 v - g 0 t) (g 0 v - g 0 t - (v - t) * g 1 t)
      rwa [sub_sub_cancel] at this
    rw [abs_mul, hvt] at this
    linarith
  have hba : b - a = 2 * h := by simp only [h]; ring
  rw [hba]
  rw [← mul_le_mul_iff_of_pos_left hh]
  calc h * |g 1 t| ≤ 2 * ‖F.1 0‖ + ‖F.1 2‖ * h * h := hstep
    _ = h * (4 / (2 * h) * ‖F.1 0‖ + h * ‖F.1 2‖) := by field_simp; ring

/-- **Ex 3.7c: the "only if" is false.** On `C²[a, b]` the weights `α = (1, 0, 1)` give a
norm, `max |f| + max |f″|`, and it is complete although `α₁ = 0`. -/
theorem ex_3_7c_counterexample (hab : a < b) :
    IsNorm (fun F : ckSub hab.le 2 => ckNorm ![1, 0, 1] F.1) ∧
      IsCompleteFor fun F G : ckSub hab.le 2 => ckNorm ![1, 0, 1] (F.1 - G.1) := by
  have hform : ∀ F : Fin 3 → C(Icc a b, ℝ), ckNorm ![1, 0, 1] F = ‖F 0‖ + ‖F 2‖ := fun F => by
    simp [ckNorm, Fin.sum_univ_three]
  have hall : ∀ F : Fin 3 → C(Icc a b, ℝ),
      ckNorm (fun _ => 1) F = ‖F 0‖ + ‖F 1‖ + ‖F 2‖ := fun F => by
    simp [ckNorm, Fin.sum_univ_three]
  set K := max (4 / (b - a)) ((b - a) / 2)
  have hK : 0 ≤ K := le_max_of_le_right (by linarith)
  -- `max |f′|` is controlled by `max |f| + max |f″|`
  have hctrl : ∀ F : ckSub hab.le 2, ‖F.1 1‖ ≤ K * (‖F.1 0‖ + ‖F.1 2‖) := fun F => by
    refine (interpolation hab F).trans ?_
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  refine ⟨⟨fun F => by rw [hform]; positivity, fun F => ?_, fun r F => ?_, fun F G => ?_⟩, ?_⟩
  · rw [hform]
    constructor
    · intro h
      have h0 : ‖F.1 0‖ = 0 := by linarith [norm_nonneg (F.1 0), norm_nonneg (F.1 2)]
      have h2 : ‖F.1 2‖ = 0 := by linarith [norm_nonneg (F.1 0), norm_nonneg (F.1 2)]
      have h1 : ‖F.1 1‖ = 0 := le_antisymm (by simpa [h0, h2] using hctrl F) (norm_nonneg _)
      ext1
      funext i
      fin_cases i
      · exact norm_eq_zero.1 h0
      · exact norm_eq_zero.1 h1
      · exact norm_eq_zero.1 h2
    · rintro rfl; simp
  · rw [hform, hform]
    simp only [Submodule.coe_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    ring
  · rw [hform, hform, hform]
    simp only [Submodule.coe_add, Pi.add_apply]
    linarith [norm_add_le (F.1 0) (G.1 0), norm_add_le (F.1 2) (G.1 2)]
  · intro x hx
    -- Cauchy for `(1, 0, 1)` ⇒ Cauchy for `(1, 1, 1)`, which is complete
    have hcmp : ∀ F G : ckSub hab.le 2,
        ckNorm (fun _ => 1) (F.1 - G.1) ≤ (1 + K) * ckNorm ![1, 0, 1] (F.1 - G.1) := fun F G => by
      rw [hall, hform]
      have := hctrl (F - G)
      simp only [Submodule.coe_sub] at this
      nlinarith [norm_nonneg ((F.1 - G.1) 0), norm_nonneg ((F.1 - G.1) 2)]
    have hx' : IsCauchy (fun F G : ckSub hab.le 2 => ckNorm (fun _ => 1) (F.1 - G.1)) x :=
      fun ε hε => by
        obtain ⟨N, hN⟩ := hx (ε / (1 + K)) (div_pos hε (by linarith))
        refine ⟨N, fun n hn m hm => (hcmp _ _).trans_lt ?_⟩
        have := hN n hn m hm
        rwa [lt_div_iff₀ (by linarith), mul_comm] at this
    obtain ⟨L, hL⟩ := isComplete_ckNorm hab.le (fun _ => one_pos) x hx'
    refine ⟨L, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hL ε hε
    refine ⟨N, fun n hn => lt_of_le_of_lt ?_ (hN n hn)⟩
    change ckNorm ![1, 0, 1] ((x n).1 - L.1) ≤ ckNorm (fun _ => 1) ((x n).1 - L.1)
    rw [hall, hform]
    linarith [norm_nonneg (((x n).1 - L.1) 1)]

end StokeyLucasPrescott.MathematicalPreliminaries

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.integral_pos_of_pos
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ext
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.continuous_ext
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ext_of_mem
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ext_add
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ext_smul
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ext_sub
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.l1
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.l1_nonneg
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.l1_zero
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.l1_eq_zero_iff
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.l1_add_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.l1_smul
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.l1_neg
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.l1_le_norm
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsMetric
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsMetric.mk
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsMetric.nonneg
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsMetric.eq_zero
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsMetric.symm
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsMetric.triangle
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.Converges
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsCauchy
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsCompleteFor
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsMetric.self
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.limit_unique
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsCauchy.of_converges
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsCauchy.bounded
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.converges_iff_subseq
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isMetric_int
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isMetric_discrete
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isMetric_rat
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.StrictIncr
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isMetric_sup_strictMono
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isMetric_l1_strictMono
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.concave_subadditive
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isMetric_comp
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsSubspace
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isSubspace_univ
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isSubspace_line
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isSubspace_continuousOn
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.not_isSubspace_circle
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.not_isSubspace_int
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.not_isSubspace_nonneg
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsNorm
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsNorm.mk
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsNorm.nonneg
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsNorm.eq_zero
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsNorm.smul
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsNorm.triangle
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsNorm.isMetric
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isNorm_norm
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isNorm_euclid
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isNorm_max
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.abs_le_max_norm
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.max_norm_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isNorm_sum
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ellInf
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.supNorm
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.abs_le_supNorm
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.supNorm_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isNorm_ellInf
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isNorm_sup
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isNorm_l1
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.theorem_3_1
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isCompleteFor_of_completeSpace
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_of_eventually_const
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_int
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_discrete
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_of_equiv_max
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.sum_abs_le_card_mul_max
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.max_le_sum_abs
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_sum
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_max
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_euclid
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_ellInf
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_sup
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsClosedFor
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_subset
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_sup_monotone
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ramp
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ramp_strictMono
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.norm_ramp_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.norm_ramp_tendsto
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isCauchy_of_tendsto_zero
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.not_isComplete_sup_strictMono
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.not_isComplete_l1_strictMono
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.not_isComplete_rat
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.integral_abs_ge
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.stepRamp
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.stepRamp_apply
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.stepRamp_nonneg
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.stepRamp_le_one
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.stepRamp_mono
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.stepRamp_left
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.stepRamp_right
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.rampIntegral
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ext_stepRamp_mono
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.l1_stepRamp_sub
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.rampIntegral_mono
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.rampIntegral_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isCauchy_stepRamp
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.away_of_ne
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.limit_eq_zero_left
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.limit_eq_one_right
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.not_isComplete_l1
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsContraction
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsContraction.uniformContinuous
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.dist_iterate_succ_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.dist_iterate_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.cauchySeq_iterate
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.theorem_3_2
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.dist_fixedPoint_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.corollary_1
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.corollary_2
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsBdd
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.supDist
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.bddAbove_absDiff
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.abs_le_supDist
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.supDist_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.supDist_nonneg
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.theorem_3_3
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.bellmanOp
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.bddAbove_bellman
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.le_bellmanOp
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.bellmanOp_bdd
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.bellmanOp_mono
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ciSup_add_const
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.bellmanOp_add_const
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.bellmanOp_contraction
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.policyValue
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.exercise_3_1
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.policyValue_le_bellmanOp
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.iterate_mono
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.fixedPoint_eq_limit
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsLHC
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsUHC
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsCompactValued
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.image
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.graph
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.continuousAt_of_isUHC_singleton
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isUHC_singleton_of_continuousAt
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isUHC_proj
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isUHC_union
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isUHC_inter
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isCompact_image
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isUHC_comp
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isUHC_pi
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.continuousAt_of_isLHC_singleton
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isLHC_proj
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isLHC_union
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isLHC_comp
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isLHC_pi
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.not_isLHC_inter
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isCompact_graph
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.theorem_3_4
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.closedGraph_not_uhc
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.theorem_3_5
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.dual_apply_eq_sum
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.vertex
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.no_separation
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.eventually_mem_of_mem_interior
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isLHC_inter_of_interior
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.maxValue
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.argmax
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.continuousOn_section
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.exists_argmax
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.le_maxValue
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.tendsto_f_graph
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.theorem_3_6
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.mk
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.nonempty
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.compact
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.convex
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.lhc
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.uhc
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.cont
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.strict
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.argmax_unique
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.argmaxFn
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.argmaxFn_mem
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.argmax_eq
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.lt_of_ne
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.continuous_argmaxFn
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.lemma_3_7
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ArgmaxSetup.lemma_3_7_uniform
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.shortfall_lt
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.theorem_3_8
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.theorem_3_8_uniform
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isLHC_const
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isUHC_const
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.not_isLHC_of_eventually
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_16a
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.f316b
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.continuous_f316b
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.argmax_316b
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_16b
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.NNR
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.gamma316c
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.tendsto_val
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.gamma316c_continuous
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.argmax_316c
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.not_tendsto_of_far
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_16c
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isLHC_Icc
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isUHC_Icc
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_13a
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_13b
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_14c
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.Orthant
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.budget
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.allocGraph
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.budget_eq
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.allocGraph_nonempty
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isUHC_allocGraph
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isLHC_allocGraph
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_13c
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.superlevel
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isLHC_superlevel
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isUHC_superlevel
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_14b
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_14a
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.picardFn
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.continuous_picardFn
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.picard
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.picard_apply
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_10b
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_10c
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ext_zero
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.abs_ext_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.IsCk
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ckSub
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ckNorm
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isCk_iff_integral
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isClosed_ckSub
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isNorm_ckNorm
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.norm_le_ckNorm
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ckNorm_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isComplete_ckNorm
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_7a
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.restrictC
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ext_restrictC
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.mk1
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.isNorm_sup_C1
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.sqrtSeq
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.sqrtSeq'
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.sqrtSeq_pos
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.continuous_sqrtSeq
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.continuous_sqrtSeq'
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.hasDerivAt_sqrtSeq
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.abs_sqrt_sub_abs_le
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_7b
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.not_isNorm_of_alpha0
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.interpolation
#print axioms StokeyLucasPrescott.MathematicalPreliminaries.ex_3_7c_counterexample
