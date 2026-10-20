/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MathematicalPreliminaries.IntervalFunctions

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
