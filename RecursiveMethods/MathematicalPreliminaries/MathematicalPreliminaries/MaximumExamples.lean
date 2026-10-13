/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MathematicalPreliminaries.Maximum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

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
