/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MathematicalPreliminaries.Correspondences
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology

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
