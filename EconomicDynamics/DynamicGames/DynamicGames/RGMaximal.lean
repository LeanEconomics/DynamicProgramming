/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.RGPayoffSet
import Mathlib.Analysis.Convex.Topology
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.FixedPoints

/-!
# `V` is the maximal fixed point of `B` in the feasible payoff set

Miao, §21.1.1, p. 740 (the feasible payoff set) and Theorem 21.1.2, p. 745.

* `rg_feasible u = co {u(a) : a ∈ A}`, the feasible payoff set; `rg_box M = [−M, M]ⁿ`.
* `rg_U_mem_closure_feasible`: every payoff `U(σ)` lies in the closure of the feasible set (an
  infinite convex combination of stage payoffs); for finite `A` the feasible set is closed and
  `U(σ) ∈ rg_feasible u` (`rg_V_subset_feasible`).
* `rg_BOn F`: `B` as a monotone map on the complete lattice `{W : W ⊆ F}` of subsets of a convex
  `F` containing all stage payoffs.
* `theorem_21_1_2` (finite `A`, `F` the feasible set): `V` is the greatest fixed point
  (`OrderHom.gfp`, Knaster–Tarski) of `B` on the subsets of `F`, it equals the union of the
  self-generating subsets of `F`, and contains every fixed point in `F`.
* `theorem_21_1_2_closure`: the same for any action sets, with `F` the closure of the feasible
  set (departure: with infinite `A` the book's convex hull need not be closed, and `V` is only
  shown to lie in its closure).
-/

namespace Miao.DynamicGames

open Filter Topology

variable {ι : Type*} {A : ι → Type*}

/-- The feasible payoff set `W = co {u(a) ∈ ℝⁿ : a ∈ A}` (Miao, p. 740). -/
def rg_feasible (u : rg_Prof A → ι → ℝ) : Set (ι → ℝ) := convexHull ℝ (Set.range u)

/-- Every stage payoff `u(a)` is feasible. -/
theorem rg_u_mem_feasible (u : rg_Prof A → ι → ℝ) (a : rg_Prof A) : u a ∈ rg_feasible u :=
  subset_convexHull ℝ (Set.range u) (Set.mem_range_self a)

/-- The box `[−M, M]ⁿ`. -/
def rg_box (ι : Type*) (M : ℝ) : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Icc (-M) M

/-- The box `[−M, M]ⁿ` is convex. -/
theorem rg_box_convex (M : ℝ) : Convex ℝ (rg_box ι M) :=
  convex_pi fun _ _ => convex_Icc _ _

/-- The box `[−M, M]ⁿ` is closed. -/
theorem rg_box_isClosed (M : ℝ) : IsClosed (rg_box ι M) :=
  isClosed_set_pi fun _ _ => isClosed_Icc

/-- Membership in the box. -/
theorem rg_mem_box {M : ℝ} {x : ι → ℝ} : x ∈ rg_box ι M ↔ ∀ j, |x j| ≤ M := by
  simp only [rg_box, Set.mem_univ_pi, Set.mem_Icc, abs_le]

/-- The closed feasible set lies in `[−M, M]ⁿ` when `|u| ≤ M`. -/
theorem rg_closure_feasible_subset_box {M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) : closure (rg_feasible u) ⊆ rg_box ι M := by
  refine closure_minimal (convexHull_min ?_ (rg_box_convex M)) (rg_box_isClosed M)
  rintro x ⟨a, rfl⟩
  exact rg_mem_box.2 (hM a)

/-- Each continuation payoff `U(σ|h)` is within `2Mδⁿ` of a point of the feasible set. -/
theorem rg_U_near_feasible {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) (n : ℕ) :
    ∀ h, ∃ c ∈ rg_feasible u, ∀ j, |rg_U δ u (rg_cont σ h) j - c j| ≤ 2 * M * δ ^ n := by
  induction n with
  | zero =>
    intro h
    refine ⟨u (σ h), rg_u_mem_feasible u (σ h), fun j => ?_⟩
    have h1 := rg_abs_U_le hM hδ0 hδ1 (rg_cont σ h) j
    have h2 := hM (σ h) j
    calc |rg_U δ u (rg_cont σ h) j - u (σ h) j|
        ≤ |rg_U δ u (rg_cont σ h) j| + |u (σ h) j| := abs_sub _ _
      _ ≤ 2 * M * δ ^ 0 := by rw [pow_zero]; linarith
  | succ n ih =>
    intro h
    obtain ⟨c, hc, hcj⟩ := ih (σ h :: h)
    refine ⟨(1 - δ) • u (σ h) + δ • c, ?_, fun j => ?_⟩
    · exact convex_convexHull ℝ _ (rg_u_mem_feasible u (σ h)) hc (by linarith) hδ0
        (by ring)
    · rw [rg_U_cont_rec hM hδ0 hδ1 σ h j]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : (1 - δ) * u (σ h) j + δ * rg_U δ u (rg_cont σ (σ h :: h)) j -
          ((1 - δ) * u (σ h) j + δ * c j) = δ * (rg_U δ u (rg_cont σ (σ h :: h)) j - c j) := by
        ring
      rw [this, abs_mul, abs_of_nonneg hδ0, pow_succ]
      have := hcj j
      nlinarith

/-- Every payoff `U(σ) = (1 − δ) Σ δᵗ u(aₜ)` lies in the closure of the feasible set. -/
theorem rg_U_mem_closure_feasible {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) : rg_U δ u σ ∈ closure (rg_feasible u) := by
  have hc := fun n => rg_U_near_feasible hM hδ0 hδ1 σ n []
  choose c hcF hcj using hc
  simp only [rg_cont_nil] at hcj
  refine mem_closure_of_tendsto (b := atTop) (f := c) (tendsto_pi_nhds.2 fun j => ?_)
    (Eventually.of_forall hcF)
  have hlim : Tendsto (fun n : ℕ => 2 * M * δ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).const_mul (2 * M)
  have hl : Tendsto (fun n => rg_U δ u σ j - 2 * M * δ ^ n) atTop (𝓝 (rg_U δ u σ j)) := by
    simpa using tendsto_const_nhds.sub hlim
  have hr : Tendsto (fun n => rg_U δ u σ j + 2 * M * δ ^ n) atTop (𝓝 (rg_U δ u σ j)) := by
    simpa using tendsto_const_nhds.add hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl hr (fun n => ?_) (fun n => ?_)
  · have := (abs_le.1 (hcj n j)).2
    simp only
    linarith
  · have := (abs_le.1 (hcj n j)).1
    simp only
    linarith

/-- `V` lies in the closure of the feasible set. -/
theorem rg_V_subset_closure_feasible {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    rg_V δ u ⊆ closure (rg_feasible u) := by
  rintro v ⟨σ, -, rfl⟩
  exact rg_U_mem_closure_feasible hM hδ0 hδ1 σ

/-- For finite `A` the feasible set is compact, hence closed. -/
theorem rg_closure_feasible_of_finite [Finite (rg_Prof A)] (u : rg_Prof A → ι → ℝ) :
    closure (rg_feasible u) = rg_feasible u :=
  ((Set.finite_range u).isCompact_convexHull ℝ).isClosed.closure_eq

/-- For finite `A`, `V` lies in the feasible set `co {u(a)}`. -/
theorem rg_V_subset_feasible [Finite (rg_Prof A)] {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : rg_V δ u ⊆ rg_feasible u := by
  rw [← rg_closure_feasible_of_finite u]
  exact rg_V_subset_closure_feasible hM hδ0 hδ1

/-- `B` maps subsets of a convex set `F` containing every `u(a)` into `F`. -/
theorem rg_B_subset_of_convex {δ : ℝ} {u : rg_Prof A → ι → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {F : Set (ι → ℝ)} (hFc : Convex ℝ F) (hFu : ∀ a, u a ∈ F) {W : Set (ι → ℝ)}
    (hW : W ⊆ F) : rg_B δ u W ⊆ F := by
  rintro v ⟨a, w, ⟨hw, -⟩, rfl⟩
  have := hFc (hFu a) (hW (hw a)) (by linarith : (0 : ℝ) ≤ 1 - δ) hδ0 (by ring)
  convert this using 1

/-- `B` as a monotone operator on the complete lattice of subsets of `F`. -/
def rg_BOn (δ : ℝ) (u : rg_Prof A → ι → ℝ) (F : Set (ι → ℝ))
    (hF : ∀ W, W ⊆ F → rg_B δ u W ⊆ F) : Set.Iic F →o Set.Iic F where
  toFun W := ⟨rg_B δ u W.1, hF W.1 W.2⟩
  monotone' _ _ h := lemma_21_1_3 δ u h

/-- The fixed-point characterisation behind Theorem 21.1.2, for any convex `F ⊆ [−M, M]ⁿ` that
contains every `u(a)` and `V`. -/
theorem rg_maximal_fixed_point {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {F : Set (ι → ℝ)} (hFc : Convex ℝ F) (hFu : ∀ a, u a ∈ F)
    (hFb : F ⊆ rg_box ι M) (hVF : rg_V δ u ⊆ F) :
    (OrderHom.gfp (rg_BOn δ u F fun _ hW => rg_B_subset_of_convex hδ0 hδ1 hFc hFu hW)).1 =
        rg_V δ u ∧
      rg_V δ u = ⋃₀ {W | W ⊆ F ∧ W ⊆ rg_B δ u W} ∧
      ∀ W, W ⊆ F → W = rg_B δ u W → W ⊆ rg_V δ u := by
  have hbdF : ∀ W, W ⊆ F → rg_Bdd W := fun W hW => ⟨M, fun x hx => rg_mem_box.1 (hFb (hW hx))⟩
  have hself : ∀ W, W ⊆ F → W ⊆ rg_B δ u W → W ⊆ rg_V δ u := fun W hW hWB =>
    hWB.trans (lemma_21_1_2 hM hδ0 hδ1 (hbdF W hW) hWB)
  refine ⟨?_, ?_, fun W hW hWB => hself W hW hWB.le⟩
  · set f := rg_BOn δ u F fun _ hW => rg_B_subset_of_convex hδ0 hδ1 hFc hFu hW
    apply Set.Subset.antisymm
    · have hfix : f (OrderHom.gfp f) = OrderHom.gfp f := OrderHom.map_gfp f
      have hG : (OrderHom.gfp f).1 = rg_B δ u (OrderHom.gfp f).1 :=
        (congrArg Subtype.val hfix).symm
      exact hself _ (OrderHom.gfp f).2 hG.le
    · have : (⟨rg_V δ u, hVF⟩ : Set.Iic F) ≤ f ⟨rg_V δ u, hVF⟩ := lemma_21_1_1 hM hδ0 hδ1
      exact OrderHom.le_gfp f this
  · apply Set.Subset.antisymm
    · exact Set.subset_sUnion_of_mem ⟨hVF, lemma_21_1_1 hM hδ0 hδ1⟩
    · rintro x ⟨W, ⟨hW, hWB⟩, hx⟩
      exact hself W hW hWB hx

/-- **Theorem 21.1.2** (Miao, p. 745), for finite `A`: `V` is the maximal fixed point of `B` on
the lattice of subsets of the feasible payoff set `co {u(a)}`: it is the greatest fixed point
given by Tarski's theorem, the union of all self-generating subsets, and it contains every fixed
point of `B` in the feasible set. -/
theorem theorem_21_1_2 [Finite (rg_Prof A)] {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (OrderHom.gfp (rg_BOn δ u (rg_feasible u) fun _ hW => rg_B_subset_of_convex hδ0 hδ1
        (convex_convexHull ℝ _) (rg_u_mem_feasible u) hW)).1 = rg_V δ u ∧
      rg_V δ u = ⋃₀ {W | W ⊆ rg_feasible u ∧ W ⊆ rg_B δ u W} ∧
      ∀ W, W ⊆ rg_feasible u → W = rg_B δ u W → W ⊆ rg_V δ u :=
  rg_maximal_fixed_point hM hδ0 hδ1 (convex_convexHull ℝ _)
    (rg_u_mem_feasible u)
    ((subset_closure).trans (rg_closure_feasible_subset_box hM))
    (rg_V_subset_feasible hM hδ0 hδ1)

/-- **Theorem 21.1.2** (Miao, p. 745), any action sets: the same with the closure of the
feasible set in place of the feasible set. -/
theorem theorem_21_1_2_closure {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (OrderHom.gfp (rg_BOn δ u (closure (rg_feasible u)) fun _ hW => rg_B_subset_of_convex hδ0
        hδ1 (convex_convexHull ℝ _).closure
        (fun a => subset_closure (rg_u_mem_feasible u a)) hW)).1 = rg_V δ u ∧
      rg_V δ u = ⋃₀ {W | W ⊆ closure (rg_feasible u) ∧ W ⊆ rg_B δ u W} ∧
      ∀ W, W ⊆ closure (rg_feasible u) → W = rg_B δ u W → W ⊆ rg_V δ u :=
  rg_maximal_fixed_point hM hδ0 hδ1 (convex_convexHull ℝ _).closure
    (fun a => subset_closure (rg_u_mem_feasible u a))
    (rg_closure_feasible_subset_box hM) (rg_V_subset_closure_feasible hM hδ0 hδ1)

end Miao.DynamicGames
