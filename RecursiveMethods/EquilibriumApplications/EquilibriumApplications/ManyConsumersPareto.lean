/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManyConsumers

/-!
# Utility possibility sets and Pareto optima with many consumers

SLP §16.7, pp. 497–498. Consumers are indexed by a finite type `ι` (`I = |ι|`); `mcSimplex ι` is the
unit simplex `Δᴵ` (Mathlib's `stdSimplex` is deprecated).

* `mcFeasible Φ κ c`: `[(cᵢ), Σᵢ cᵢ]` is feasible from `κ` (p. 497); `mc_feasible_iff` relates it
  to `Feasible` of §15.2 with one firm.
* `mcUtilSet Φ u κ` is `U(κ)`, equation (1); `mcSupport Φ u κ θ` is its support function `v(κ, θ)`;
  `mc_eq2` is equation (2). `mcUtilSet_nonempty`, `mc_utility_bounds`, `mcUtilSet_subset_Icc`,
  `mcUtilSet_bddAbove`: `U(κ)` is nonempty and bounded.
* **Exercise 16.7b** (p. 497): `ex_16_7b_onlyIf` — every Pareto optimum maximises `Σᵢ θᵢuᵢ(cᵢ)`
  over the allocations feasible from `κ` for some `θ ∈ Δᴵ` (separate the convex set `U(κ) − ℝᴵ₊`,
  `convex_mcUtilHull`, from the open orthant above the optimum); `ex_16_7b_if` — a maximiser for
  some `θ ≫ 0` is Pareto optimal.
* **Exercise 16.7c** (p. 498): `ex_16_7c_onlyIf`; `mc_exists_simplex_separating` (strict
  separation by a weight in `Δᴵ` from a closed convex set `D` with `D − ℝᴵ₊ ⊆ D`);
  `mc_isClosed_lowerHull`; `mc_mem_of_forall_support` (a compact, comprehensive set with convex
  lower hull is recovered from its support function on `Δᴵ`); `mcUtilSet_comprehensive` (`U(κ)` is
  comprehensive in `ℝᴵ₊`: intermediate value theorem on `λ ↦ uᵢ(λcᵢ)` and free disposal);
  `ex_16_7c` (the corrected statement, for closed `U(κ)`).
* **Equation (3)** (p. 498): `mc_eq3_set` — `U(κ)` is the set of `(Wᵢ(γᵢ, z′ᵢ))ᵢ` with `γᵢ ≥ 0`,
  `(Σᵢ γᵢ, κ′) ∈ Φ(κ)`, `z′ ∈ U(κ′)` — and `mc_eq3`.

**Corrections.**
* Exercise 16.7b must read "for some `θ ∈ Δᴵ`", and its "if" direction holds only for `θ ≫ 0`
  (`ex_16_7b_if`); for `θ` on the boundary of `Δᴵ` it fails (`ex_16_7b_counterexample`). The
  "only if" direction needs at least one consumer. "Attains the supremum" is formalised as
  maximising over the feasible allocations (no attainment of `sup U(κ)` is claimed).
* Exercise 16.7c needs `U(κ)` closed (`ex_16_7c_counterexample`, where `U(1)` is not closed);
  convexity of `U(κ) − ℝᴵ₊` and comprehensiveness hold under (W1)–(W5), (T1)–(T7). Under the capital
  bound (T8), `U(κ)` is closed (`mcUtilSet_isClosed` in `ManyConsumersCapital`).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

variable {l p : ℕ} {Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))} {ι : Type*} [Fintype ι]

/-! ### Sequence operations -/

omit [Fintype ι] in
/-- Coordinates of a finite sum of bounded sequences. -/
theorem mc_sum_apply {E : Type*} [NormedAddCommGroup E] (s : Finset ι) (c : ι → BddSeq E)
    (t : ℕ) : (∑ i ∈ s, c i) t = ∑ i ∈ s, c i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rw [lp.coeFn_zero]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mc_add_apply, ih]

/-- The sequence `(a, x₀, x₁, …)`. -/
noncomputable def mcSeqCons {E : Type*} [NormedAddCommGroup E] (a : E) (x : BddSeq E) :
    BddSeq E :=
  BddSeq.mk (fun t => Nat.casesOn t a fun s => x s) (‖a‖ + ‖x‖) fun t => by
    cases t with
    | zero => exact le_add_of_nonneg_right (norm_nonneg _)
    | succ s => exact (norm_seq_coord_le x s).trans (le_add_of_nonneg_left (norm_nonneg _))

/-- The head of `mcSeqCons a x` is `a`. -/
@[simp] theorem mcSeqCons_zero {E : Type*} [NormedAddCommGroup E] (a : E) (x : BddSeq E) :
    mcSeqCons a x 0 = a := rfl

/-- The tail of `mcSeqCons a x` is `x`. -/
@[simp] theorem mcSeqCons_succ {E : Type*} [NormedAddCommGroup E] (a : E) (x : BddSeq E)
    (t : ℕ) : mcSeqCons a x (t + 1) = x t := rfl

/-- `₁(a, x) = x`. -/
@[simp] theorem seqShift_mcSeqCons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E)
    (x : BddSeq E) : seqShift (mcSeqCons a x) = x := by
  ext t
  rw [seqShift_apply, mcSeqCons_succ]

/-! ### Feasible allocations, `U(k̂)` and its support function (p. 497) -/

omit [Fintype ι] in
/-- The unit simplex `Δᴵ = {θ ∈ ℝᴵ₊ : Σᵢ θᵢ = 1}` (p. 497). -/
def mcSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {θ | (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1}

/-- A weight in `Δᴵ` is at most one. -/
theorem mcSimplex_le_one {θ : ι → ℝ} (hθ : θ ∈ mcSimplex ι) (i : ι) : θ i ≤ 1 := by
  rw [← hθ.2]
  exact Finset.single_le_sum (fun j _ => hθ.1 j) (Finset.mem_univ i)

/-- An allocation `[(cᵢ), y]` is **feasible from `κ`** (p. 497): `cᵢ ∈ C` and `y = Σᵢ cᵢ ∈ Y(κ)`.
(The production plan is determined by the consumption plans, so it is not recorded.) -/
def mcFeasible (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))) (κ : Fin p → ℝ)
    (c : ι → BddSeq (Fin l → ℝ)) : Prop :=
  (∀ i, c i ∈ mcCons l) ∧ ∑ i, c i ∈ mcProdSet Φ κ

/-- The **utility possibility set** (1), p. 497:
`U(κ) = {z : zᵢ = uᵢ(cᵢ) ∀i, for some allocation feasible from κ}`. -/
def mcUtilSet (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ)))
    (u : ι → BddSeq (Fin l → ℝ) → ℝ) (κ : Fin p → ℝ) : Set (ι → ℝ) :=
  {z | ∃ c, mcFeasible Φ κ c ∧ z = fun i => u i (c i)}

/-- The **support function** of `U(κ)`, p. 497: `v(κ, θ) = sup_{z ∈ U(κ)} Σᵢ θᵢ zᵢ`. -/
noncomputable def mcSupport (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ)))
    (u : ι → BddSeq (Fin l → ℝ) → ℝ) (κ : Fin p → ℝ) (θ : ι → ℝ) : ℝ :=
  sSup ((fun z => ∑ i, θ i * z i) '' mcUtilSet Φ u κ)

/-- **Equation (2)**, p. 497: `v(κ, θ) = sup Σᵢ θᵢ uᵢ(cᵢ)` over `cᵢ ≥ 0` with `Σᵢ cᵢ ∈ Y(κ)`. -/
theorem mc_eq2 (u : ι → BddSeq (Fin l → ℝ) → ℝ) (κ : Fin p → ℝ) (θ : ι → ℝ) :
    mcSupport Φ u κ θ = sSup {r | ∃ c, mcFeasible Φ κ c ∧ r = ∑ i, θ i * u i (c i)} := by
  unfold mcSupport
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩

/-- The zero allocation is feasible from `κ ≥ 0`. -/
theorem mcFeasible_zero (hΦ : ManyConsumersTech Φ) {κ : Fin p → ℝ} (hκ : 0 ≤ κ) :
    mcFeasible (ι := ι) Φ κ 0 := by
  refine ⟨fun _ t => ?_, ?_⟩
  · change (0 : Fin l → ℝ) ≤ (0 : BddSeq (Fin l → ℝ)) t
    rw [lp.coeFn_zero]; rfl
  · simpa using zero_mem_mcProdSet hΦ hκ

/-- `U(κ)` is nonempty for `κ ≥ 0`. -/
theorem mcUtilSet_nonempty (hΦ : ManyConsumersTech Φ) (u : ι → BddSeq (Fin l → ℝ) → ℝ)
    {κ : Fin p → ℝ} (hκ : 0 ≤ κ) : (mcUtilSet Φ u κ).Nonempty :=
  ⟨_, 0, mcFeasible_zero hΦ hκ, rfl⟩

omit [Fintype ι] in
/-- Utilities are bounded: for a family of fixed points there are bounds `Bᵢ ≥ 0` with
`0 ≤ uᵢ ≤ Bᵢ` on `C`. -/
theorem mc_utility_bounds {W : ι → (Fin l → ℝ) → ℝ → ℝ} {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) :
    ∃ B : ι → ℝ, (∀ i, 0 ≤ B i) ∧ ∀ i, ∀ x ∈ mcCons l, 0 ≤ u i x ∧ u i x ≤ B i := by
  choose B hB using fun i => (hu i).bounded
  refine ⟨fun i => |B i|, fun i => abs_nonneg _, fun i x hx => ⟨(hu i).nonneg x hx, ?_⟩⟩
  exact (le_abs_self _).trans ((hB i x hx).trans (le_abs_self _))

/-- `U(κ) ⊆ ∏ᵢ [0, Bᵢ]`. -/
theorem mcUtilSet_subset_Icc {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    {B : ι → ℝ} (hB : ∀ i, ∀ x ∈ mcCons l, 0 ≤ u i x ∧ u i x ≤ B i) (κ : Fin p → ℝ) :
    mcUtilSet Φ u κ ⊆ Icc 0 B := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨fun i => (hB i _ (hc.1 i)).1, fun i => (hB i _ (hc.1 i)).2⟩

/-- For `θ ∈ Δᴵ`, `θ · z ≤ Σᵢ Bᵢ` on `U(κ)`, so the supremum `v(κ, θ)` is finite. -/
theorem mcUtilSet_bddAbove {u : ι → BddSeq (Fin l → ℝ) → ℝ} {B : ι → ℝ}
    (hB : ∀ i, ∀ x ∈ mcCons l, 0 ≤ u i x ∧ u i x ≤ B i) (κ : Fin p → ℝ) {θ : ι → ℝ}
    (hθ : θ ∈ mcSimplex ι) :
    BddAbove ((fun z => ∑ i, θ i * z i) '' mcUtilSet Φ u κ) := by
  refine ⟨∑ i, B i, ?_⟩
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  refine Finset.sum_le_sum fun i _ => ?_
  have h := hB i _ (hc.1 i)
  have h1 := mcSimplex_le_one hθ i
  nlinarith [hθ.1 i]

/-- **Feasibility in the sense of §15.2**: with one firm, `[(cᵢ), y]` is feasible iff it is
feasible from `κ` and `y = Σᵢ cᵢ`. -/
theorem mc_feasible_iff (κ : Fin p → ℝ) (c : ι → BddSeq (Fin l → ℝ))
    (y : Unit → BddSeq (Fin l → ℝ)) :
    Feasible (fun _ : ι => mcCons l) (fun _ : Unit => mcProdSet Φ κ) c y ↔
      mcFeasible Φ κ c ∧ y () = ∑ i, c i := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hy : y () = ∑ i, c i := by
      simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton] at h3
      exact (sub_eq_zero.1 h3).symm
    exact ⟨⟨h1, hy ▸ h2 ()⟩, hy⟩
  · rintro ⟨⟨h1, h2⟩, hy⟩
    refine ⟨h1, fun _ => hy ▸ h2, ?_⟩
    simp [hy]

/-! ### Exercise 16.7b -/

/-- The weakly dominated hull `{z : z ≤ w for some w ∈ U(κ)}` of the utility possibility set. -/
def mcUtilHull (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ)))
    (u : ι → BddSeq (Fin l → ℝ) → ℝ) (κ : Fin p → ℝ) : Set (ι → ℝ) :=
  {z | ∃ w ∈ mcUtilSet Φ u κ, z ≤ w}

/-- The hull `U(κ) − ℝᴵ₊` is convex: concave utilities (W5) and a convex technology (T5). -/
theorem convex_mcUtilHull {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    (κ : Fin p → ℝ) : Convex ℝ (mcUtilHull Φ u κ) := by
  rintro z ⟨_, ⟨c, hc, rfl⟩, hz⟩ z' ⟨_, ⟨c', hc', rfl⟩, hz'⟩ a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  refine ⟨_, ⟨fun i => a • c i + (1 - a) • c' i, ⟨fun i => convex_seqSet (convex_Ici 0) (hc.1 i)
    (hc'.1 i) ha hb hab, ?_⟩, rfl⟩, fun i => ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
    exact ex_16_7a_convex hΦ κ hc.2 hc'.2 ha hb hab
  · have h1 := mc_utility_concave (hW i) (hu i) _ (hc.1 i) _ (hc'.1 i) a ha ha1
    have h2 := hz i
    have h3 := hz' i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2 h3 ⊢
    nlinarith

/-- A linear functional on `ℝᴵ` is `z ↦ Σᵢ zᵢ θᵢ` with `θᵢ = φ(eᵢ)`. -/
theorem mc_dual_apply [DecidableEq ι] (φ : StrongDual ℝ (ι → ℝ)) (z : ι → ℝ) :
    φ z = ∑ i, z i * φ (fun j => if i = j then 1 else 0) := by
  have := LinearMap.pi_apply_eq_sum_univ (φ : (ι → ℝ) →ₗ[ℝ] ℝ) z
  simpa [smul_eq_mul] using this

/-- **Exercise 16.7b**, "if", for strictly positive weights: an allocation feasible from `κ` that
maximises `Σᵢ θᵢuᵢ(cᵢ)` for some `θ ≫ 0` is Pareto optimal. -/
theorem ex_16_7b_if {u : ι → BddSeq (Fin l → ℝ) → ℝ} {κ : Fin p → ℝ}
    {c : ι → BddSeq (Fin l → ℝ)} (hc : mcFeasible Φ κ c) {θ : ι → ℝ} (hθ : ∀ i, 0 < θ i)
    (hmax : ∀ c', mcFeasible Φ κ c' → ∑ i, θ i * u i (c' i) ≤ ∑ i, θ i * u i (c i)) :
    ParetoOptimal (fun _ : ι => mcCons l) u (fun _ : Unit => mcProdSet Φ κ) c
      (fun _ => ∑ i, c i) := by
  refine ⟨(mc_feasible_iff κ c _).2 ⟨hc, rfl⟩, ?_⟩
  rintro ⟨c', y', hF, hge, i0, hi0⟩
  have hc' := ((mc_feasible_iff κ c' y').1 hF).1
  have hlt : ∑ i, θ i * u i (c i) < ∑ i, θ i * u i (c' i) :=
    Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hge i) (hθ i).le)
      ⟨i0, Finset.mem_univ _, mul_lt_mul_of_pos_left hi0 (hθ i0)⟩
  exact absurd (hmax c' hc') (not_le.2 hlt)

/-- **Exercise 16.7b**, "only if" (corrected: "for some `θ ∈ Δᴵ`"). Under (W1)–(W5) and
(T1)–(T7), every Pareto optimal allocation feasible from `κ` maximises `Σᵢ θᵢuᵢ(cᵢ)` over the
allocations feasible from `κ`, for some `θ ∈ Δᴵ`: separate the convex hull `U(κ) − ℝᴵ₊` from the
open orthant `{z ≫ u(c)}`. -/
theorem ex_16_7b_onlyIf [Nonempty ι] {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    {κ : Fin p → ℝ} {c : ι → BddSeq (Fin l → ℝ)} {y : Unit → BddSeq (Fin l → ℝ)}
    (hPO : ParetoOptimal (fun _ : ι => mcCons l) u (fun _ : Unit => mcProdSet Φ κ) c y) :
    ∃ θ ∈ mcSimplex ι,
      ∀ c', mcFeasible Φ κ c' → ∑ i, θ i * u i (c' i) ≤ ∑ i, θ i * u i (c i) := by
  classical
  have hc := ((mc_feasible_iff κ c y).1 hPO.1).1
  set z0 : ι → ℝ := fun i => u i (c i) with hz0
  set A : Set (ι → ℝ) := Set.pi univ fun i => Ioi (z0 i) with hA
  have hAc : Convex ℝ A := convex_pi fun i _ => convex_Ioi _
  have hz1 : z0 + 1 ∈ A := mem_univ_pi.2 fun i => by simp
  have hz0B : z0 ∈ mcUtilHull Φ u κ := ⟨z0, ⟨c, hc, rfl⟩, le_rfl⟩
  have hdisj : Disjoint A (mcUtilHull Φ u κ) := by
    rw [Set.disjoint_left]
    rintro z hzA ⟨_, ⟨c', hc', rfl⟩, hzw⟩
    obtain ⟨i0⟩ := ‹Nonempty ι›
    have hlt : ∀ i, u i (c i) < u i (c' i) := fun i =>
      (mem_univ_pi.1 hzA i).trans_le (hzw i)
    exact hPO.2 ⟨c', fun _ => ∑ i, c' i, (mc_feasible_iff κ c' _).2 ⟨hc', rfl⟩,
      fun i => (hlt i).le, i0, hlt i0⟩
  obtain ⟨φ, hφ0, hsep⟩ := exists_separating_of_finiteDimensional hAc
    (convex_mcUtilHull hW hu hΦ κ) ⟨_, hz1⟩ ⟨_, hz0B⟩ hdisj
  set θ : ι → ℝ := fun i => φ (fun j => if i = j then 1 else 0) with hθdef
  have hrep : ∀ z, φ z = ∑ i, z i * θ i := mc_dual_apply φ
  have hφ1 : ∀ w ∈ mcUtilHull Φ u κ, φ w ≤ φ z0 + ∑ i, θ i := fun w hw => by
    have := hsep _ hz1 w hw
    rwa [map_add, hrep 1, Finset.sum_congr rfl fun i _ => by rw [Pi.one_apply, one_mul]] at this
  have hθ0 : ∀ i, 0 ≤ θ i := by
    intro i
    by_contra hneg
    push Not at hneg
    set t := (|∑ j, θ j| + 1) / (-θ i) with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) (by linarith)
    have hw : z0 - t • (fun j => if i = j then 1 else 0) ∈ mcUtilHull Φ u κ :=
      ⟨z0, ⟨c, hc, rfl⟩, fun j => by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        split_ifs <;> nlinarith⟩
    have := hφ1 _ hw
    rw [map_sub, map_smul, smul_eq_mul] at this
    have hne : θ i ≠ 0 := hneg.ne
    have hti : t * θ i = -(|∑ j, θ j| + 1) := by
      rw [ht]; field_simp
    linarith [le_abs_self (∑ j, θ j)]
  set S := ∑ i, θ i with hS
  have hSpos : 0 < S := by
    rcases (Finset.sum_nonneg fun i _ => hθ0 i : 0 ≤ S).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : ∀ i, θ i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hθ0 j).1 h.symm i (Finset.mem_univ i)
      exact hφ0 (ContinuousLinearMap.ext fun z => by simp [hrep z, hz])
  refine ⟨fun i => θ i / S, ⟨fun i => div_nonneg (hθ0 i) hSpos.le, ?_⟩, fun c' hc' => ?_⟩
  · rw [← Finset.sum_div, div_self hSpos.ne']
  · have hw : (fun i => u i (c' i)) ∈ mcUtilHull Φ u κ := ⟨_, ⟨c', hc', rfl⟩, le_rfl⟩
    have hle : φ (fun i => u i (c' i)) ≤ φ z0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have hmem : z0 + (δ / S) • (1 : ι → ℝ) ∈ A := mem_univ_pi.2 fun i => by
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, mem_Ioi]
        have : 0 < δ / S := div_pos hδ hSpos
        linarith
      have := hsep _ hmem _ hw
      rw [map_add, map_smul, smul_eq_mul, hrep 1,
        Finset.sum_congr rfl fun i _ => by rw [Pi.one_apply, one_mul], ← hS,
        div_mul_cancel₀ _ hSpos.ne'] at this
      exact this
    rw [hrep, hrep] at hle
    have e : ∀ x : ι → ℝ, ∑ i, θ i / S * x i = (∑ i, x i * θ i) / S := fun x => by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, e]
    exact div_le_div_of_nonneg_right hle hSpos.le

/-! ### Exercise 16.7c -/

omit [Fintype ι] in
/-- Coordinates of a scalar multiple of a bounded sequence. -/
theorem mc_smul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (x : BddSeq E) (t : ℕ) : (a • x) t = a • x t := by
  rw [lp.coeFn_smul]; rfl

/-- **Exercise 16.7c**, "only if": `z ∈ U(κ)` implies `θ · z ≤ v(κ, θ)` for all `θ ∈ Δᴵ`. -/
theorem ex_16_7c_onlyIf {u : ι → BddSeq (Fin l → ℝ) → ℝ} {B : ι → ℝ}
    (hB : ∀ i, ∀ x ∈ mcCons l, 0 ≤ u i x ∧ u i x ≤ B i) {κ : Fin p → ℝ} {z : ι → ℝ}
    (hz : z ∈ mcUtilSet Φ u κ) : ∀ θ ∈ mcSimplex ι, ∑ i, θ i * z i ≤ mcSupport Φ u κ θ :=
  fun _ hθ => le_csSup (mcUtilSet_bddAbove hB κ hθ) ⟨z, hz, rfl⟩

/-- **Separation by a weight in the simplex.** A point `z` outside a nonempty closed convex set
`D ⊆ ℝᴵ` with `D − ℝᴵ₊ ⊆ D` is strictly separated from `D` by some `θ ∈ Δᴵ`. -/
theorem mc_exists_simplex_separating {D : Set (ι → ℝ)} (hDc : Convex ℝ D)
    (hDcl : IsClosed D) (hDne : D.Nonempty) (hDdown : ∀ w ∈ D, ∀ w', w' ≤ w → w' ∈ D)
    {z : ι → ℝ} (hz : z ∉ D) :
    ∃ θ ∈ mcSimplex ι, ∃ r, (∀ w ∈ D, ∑ i, θ i * w i < r) ∧ r < ∑ i, θ i * z i := by
  classical
  obtain ⟨f, r, hfD, hfz⟩ := geometric_hahn_banach_closed_point hDc hDcl hz
  set θ : ι → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hθdef
  have hrep : ∀ z, f z = ∑ i, z i * θ i := mc_dual_apply f
  obtain ⟨w0, hw0⟩ := hDne
  have hθ0 : ∀ i, 0 ≤ θ i := by
    intro i
    by_contra hneg
    push Not at hneg
    set t := (|r - f w0| + 1) / (-θ i) with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) (by linarith)
    have hw : w0 - t • (fun j => if i = j then 1 else 0) ∈ D := hDdown w0 hw0 _ fun j => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> nlinarith
    have := hfD _ hw
    rw [map_sub, map_smul, smul_eq_mul] at this
    have hne : θ i ≠ 0 := hneg.ne
    have hti : t * θ i = -(|r - f w0| + 1) := by
      rw [ht]; field_simp
    linarith [le_abs_self (r - f w0)]
  set S := ∑ i, θ i with hS
  have hSpos : 0 < S := by
    rcases (Finset.sum_nonneg fun i _ => hθ0 i : 0 ≤ S).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz0 : ∀ i, θ i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hθ0 j).1 h.symm i (Finset.mem_univ i)
      have h1 := hfD w0 hw0
      rw [hrep] at h1 hfz
      simp only [hz0, mul_zero, Finset.sum_const_zero] at h1 hfz
      linarith
  have e : ∀ x : ι → ℝ, ∑ i, θ i / S * x i = f x / S := fun x => by
    rw [hrep, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨fun i => θ i / S, ⟨fun i => div_nonneg (hθ0 i) hSpos.le, ?_⟩, r / S,
    fun w hw => ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hSpos.ne']
  · rw [e]; exact div_lt_div_of_pos_right (hfD w hw) hSpos
  · rw [e]; exact div_lt_div_of_pos_right hfz hSpos

omit [Fintype ι] in
/-- The lower hull `K − ℝᴵ₊ = {w : w ≤ k for some k ∈ K}` of a compact set is closed. -/
theorem mc_isClosed_lowerHull {K : Set (ι → ℝ)} [Finite ι] (hK : IsCompact K) :
    IsClosed {w | ∃ k ∈ K, w ≤ k} := by
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨x, hx, hxw⟩ := mem_closure_iff_seq_limit.1 hw
  choose k hk hxk using hx
  obtain ⟨k0, hk0, φ, hφ, hlim⟩ := hK.tendsto_subseq hk
  exact ⟨k0, hk0, le_of_tendsto_of_tendsto' (hxw.comp hφ.tendsto_atTop) hlim
    fun n => hxk (φ n)⟩

/-- **The corrected Exercise 16.7c, abstract form.** Let `K ⊆ ℝᴵ` be compact, nonempty,
comprehensive in `ℝᴵ₊` (`k ∈ K`, `0 ≤ z ≤ k` ⇒ `z ∈ K`) with convex lower hull `K − ℝᴵ₊`. Then
every `z ≥ 0` with `θ · z ≤ sup_{k ∈ K} θ · k` for all `θ ∈ Δᴵ` lies in `K`. -/
theorem mc_mem_of_forall_support {K : Set (ι → ℝ)} (hK : IsCompact K)
    (hKne : K.Nonempty) (hconv : Convex ℝ {w | ∃ k ∈ K, w ≤ k})
    (hcomp : ∀ k ∈ K, ∀ z, 0 ≤ z → z ≤ k → z ∈ K) {z : ι → ℝ} (hz0 : 0 ≤ z)
    (hz : ∀ θ ∈ mcSimplex ι, ∑ i, θ i * z i ≤ sSup ((fun k => ∑ i, θ i * k i) '' K)) :
    z ∈ K := by
  by_contra hzK
  have hzD : z ∉ {w | ∃ k ∈ K, w ≤ k} := fun ⟨k, hk, hzk⟩ => hzK (hcomp k hk z hz0 hzk)
  obtain ⟨k0, hk0⟩ := hKne
  obtain ⟨θ, hθ, r, hD, hr⟩ := mc_exists_simplex_separating hconv (mc_isClosed_lowerHull hK)
    ⟨k0, k0, hk0, le_rfl⟩ (fun w ⟨k, hk, hwk⟩ w' hw' => ⟨k, hk, hw'.trans hwk⟩) hzD
  have hsup : sSup ((fun k => ∑ i, θ i * k i) '' K) ≤ r :=
    csSup_le ⟨_, k0, hk0, rfl⟩ fun _ ⟨k, hk, hke⟩ => hke ▸ (hD k ⟨k, hk, le_rfl⟩).le
  linarith [hz θ hθ]

/-- `U(κ)` is **comprehensive** in `ℝᴵ₊` (the NOTE to Exercise 16.7c): if `z ∈ U(κ)` and
`0 ≤ z′ ≤ z` then `z′ ∈ U(κ)`. Each `λ ↦ uᵢ(λcᵢ)` is continuous on `[0, 1]` from `uᵢ(0) = 0` to
`uᵢ(cᵢ)` (intermediate value theorem), and `Σᵢ λᵢcᵢ ≤ Σᵢ cᵢ` is feasible by free disposal. -/
theorem mcUtilSet_comprehensive {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i))
    {u : ι → BddSeq (Fin l → ℝ) → ℝ} (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i))
    (hΦ : ManyConsumersTech Φ) (κ : Fin p → ℝ) :
    ∀ k ∈ mcUtilSet Φ u κ, ∀ z : ι → ℝ, 0 ≤ z → z ≤ k → z ∈ mcUtilSet Φ u κ := by
  rintro _ ⟨c, hc, rfl⟩ z hz0 hzk
  have hmaps : ∀ i, MapsTo (fun a : ℝ => a • c i) (Icc 0 1) (mcCons l) := fun i a ha t => by
    change (0 : Fin l → ℝ) ≤ (a • c i) t
    rw [mc_smul_apply]
    exact smul_nonneg ha.1 (hc.1 i t)
  have hcont : ∀ i, ContinuousOn (fun a : ℝ => u i (a • c i)) (Icc 0 1) := fun i =>
    (hu i).continuousOn.comp (continuous_id.smul continuous_const).continuousOn (hmaps i)
  have hivt : ∀ i, ∃ a ∈ Icc (0 : ℝ) 1, u i (a • c i) = z i := fun i => by
    have h := intermediate_value_Icc zero_le_one (hcont i)
    simp only [zero_smul, one_smul, mc_utility_zero (hW i) (hu i)] at h
    exact h ⟨hz0 i, hzk i⟩
  choose a ha hza using hivt
  refine ⟨fun i => a i • c i, ⟨fun i => hmaps i (ha i), ?_⟩, funext fun i => (hza i).symm⟩
  refine mcProdSet_disposal hΦ hc.2 (fun t => ?_) fun t => ?_
  · rw [mc_sum_apply]
    exact Finset.sum_nonneg fun i _ => by rw [mc_smul_apply]; exact smul_nonneg (ha i).1 (hc.1 i t)
  · rw [mc_sum_apply, mc_sum_apply]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mc_smul_apply]
    have h0 : (0 : Fin l → ℝ) ≤ c i t := hc.1 i t
    exact smul_le_of_le_one_left h0 (ha i).2

/-- **Exercise 16.7c**, corrected: if `U(κ)` is closed (which (T1)–(T7) do not guarantee:
`ex_16_7c_counterexample`), then for `κ ≥ 0`, `z ∈ U(κ)` iff `z ≥ 0` and `v(κ, θ) ≥ θ · z` for
every `θ ∈ Δᴵ`. -/
theorem ex_16_7c {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    {κ : Fin p → ℝ} (hκ : 0 ≤ κ) (hcl : IsClosed (mcUtilSet Φ u κ)) (z : ι → ℝ) :
    z ∈ mcUtilSet Φ u κ ↔ 0 ≤ z ∧ ∀ θ ∈ mcSimplex ι, ∑ i, θ i * z i ≤ mcSupport Φ u κ θ := by
  classical
  obtain ⟨B, -, hB⟩ := mc_utility_bounds hu
  constructor
  · intro hz
    exact ⟨(mcUtilSet_subset_Icc hB κ hz).1, ex_16_7c_onlyIf hB hz⟩
  · rintro ⟨hz0, hz⟩
    exact mc_mem_of_forall_support
      (Metric.isCompact_of_isClosed_isBounded hcl ((Metric.isBounded_Icc 0 B).subset
        (mcUtilSet_subset_Icc hB κ)))
      (mcUtilSet_nonempty hΦ u hκ) (convex_mcUtilHull hW hu hΦ κ)
      (mcUtilSet_comprehensive (fun i => (hW i).agg) hu hΦ κ) hz0 hz

/-! ### Equation (3): the recursive structure of `U` (p. 498) -/

/-- **Equation (3)**, set form: `U(κ)` is the set of vectors `(Wᵢ(γᵢ, z′ᵢ))ᵢ` with `γᵢ ≥ 0`,
`(Σᵢ γᵢ, κ′) ∈ Φ(κ)` and `z′ ∈ U(κ′)` (split each `cᵢ` into `cᵢ₀` and `₁cᵢ`). -/
theorem mc_eq3_set {W : ι → (Fin l → ℝ) → ℝ → ℝ} {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) {κ : Fin p → ℝ} (hκ : 0 ≤ κ) :
    mcUtilSet Φ u κ = {z | ∃ γ : ι → Fin l → ℝ, ∃ z' : ι → ℝ, ∃ κ' : Fin p → ℝ,
      (∀ i, 0 ≤ γ i) ∧ (∑ i, γ i, κ') ∈ Φ κ ∧ z' ∈ mcUtilSet Φ u κ' ∧
        z = fun i => W i (γ i) (z' i)} := by
  ext z
  constructor
  · rintro ⟨c, ⟨hcC, hc0, k, hk0, hkk, hk⟩, rfl⟩
    refine ⟨fun i => c i 0, fun i => u i (seqShift (c i)), k 1, fun i => hcC i 0, ?_, ?_, ?_⟩
    · have := hk 0
      rwa [mc_sum_apply, hkk] at this
    · refine ⟨fun i => seqShift (c i), ⟨fun i => seqShift_mem_seqSet (hcC i), ?_⟩, rfl⟩
      rw [← map_sum]
      refine ⟨fun t => hc0 (t + 1), seqShift k, fun t => hk0 (t + 1), rfl, fun t => ?_⟩
      rw [seqShift_apply, seqShift_apply, seqShift_apply]
      exact hk (t + 1)
    · exact funext fun i => (hu i).fixed _ (hcC i)
  · rintro ⟨γ, _, κ', hγ, hΦκ, ⟨c', ⟨hc'C, hc'0, k', hk'0, hk'k, hk'⟩, rfl⟩, rfl⟩
    have hcC : ∀ i, mcSeqCons (γ i) (c' i) ∈ mcCons l := fun i t => by
      cases t with
      | zero => exact hγ i
      | succ s => exact hc'C i s
    refine ⟨fun i => mcSeqCons (γ i) (c' i), ⟨hcC, fun t => ?_, mcSeqCons κ k', fun t => ?_, rfl,
      fun t => ?_⟩, funext fun i => ?_⟩
    · rw [mc_sum_apply]
      exact Finset.sum_nonneg fun i _ => hcC i t
    · cases t with
      | zero => exact hκ
      | succ s => exact hk'0 s
    · rw [mc_sum_apply]
      cases t with
      | zero =>
        simp only [mcSeqCons_zero, mcSeqCons_succ, hk'k]
        exact hΦκ
      | succ s =>
        simp only [mcSeqCons_succ]
        have := hk' s
        rwa [mc_sum_apply] at this
    · change W i (γ i) (u i (c' i)) = u i (mcSeqCons (γ i) (c' i))
      rw [(hu i).fixed _ (hcC i), mcSeqCons_zero, seqShift_mcSeqCons]

/-- **Equation (3)**, p. 498: `v(κ, θ) = sup Σᵢ θᵢ Wᵢ(γᵢ, z′ᵢ)` subject to `z′ ∈ U(κ′)` and
`(Σᵢ γᵢ, κ′) ∈ Φ(κ)`. -/
theorem mc_eq3 {W : ι → (Fin l → ℝ) → ℝ → ℝ} {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) {κ : Fin p → ℝ} (hκ : 0 ≤ κ)
    (θ : ι → ℝ) :
    mcSupport Φ u κ θ = sSup {r | ∃ γ : ι → Fin l → ℝ, ∃ z' : ι → ℝ, ∃ κ' : Fin p → ℝ,
      (∀ i, 0 ≤ γ i) ∧ (∑ i, γ i, κ') ∈ Φ κ ∧ z' ∈ mcUtilSet Φ u κ' ∧
        r = ∑ i, θ i * W i (γ i) (z' i)} := by
  unfold mcSupport
  rw [mc_eq3_set hu hκ]
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨γ, z', κ', h1, h2, h3, rfl⟩, rfl⟩
    exact ⟨γ, z', κ', h1, h2, h3, rfl⟩
  · rintro ⟨γ, z', κ', h1, h2, h3, rfl⟩
    exact ⟨_, ⟨γ, z', κ', h1, h2, h3, rfl⟩, rfl⟩

end StokeyLucasPrescott.EquilibriumApplications
