/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MathematicalPreliminaries.MaximumExamples

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
