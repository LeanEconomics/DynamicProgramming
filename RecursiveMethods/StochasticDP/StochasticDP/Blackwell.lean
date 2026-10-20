/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDP.Exercise92

/-!
# Blackwell's example: `v*` need not be measurable

SLP §9.1, pp. 253–254 (from Blackwell 1965). Let the shock never change, `Q(z, ·) = δ_z`, let
`Γ ≡ X`, and let `F(x, y, z) = 1` if `(y, z) ∈ E` and `0` otherwise, for a measurable
`E ⊆ X × Z`, with `0 ≤ β < 1`. Then `v*(x, z) = 1/(1 − β)` if `z ∈ Proj_Z E` and `0` otherwise,
the optimum being attained by a constant plan `π_t ≡ ŷ` with `(ŷ, z) ∈ E` (`blackwell_example`).
So `v*` is measurable only if `Proj_Z E` is. For `X = Z = [0, 1]` there are Borel sets `E` whose
projection is not Borel (Souslin; Behnke et al. 1974); that construction is not in Mathlib, so the
example is stated for any `E` whose projection is not measurable.
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- Blackwell's model (first formulation): constant shocks, `Γ ≡ X`, `F = 1_E(y, z)`. -/
noncomputable def blackwellModel (E : Set (X × Z)) (β : ℝ) : Model X X Z :=
  Model.first Kernel.id (fun _ => univ) (fun p => E.indicator 1 (p.2.1, p.2.2)) β

/-- With constant shocks, `μᵗ(z, ·)` is the point mass at the constant history. -/
theorem hist_id (t : ℕ) (z : Z) :
    hist (Kernel.id : Kernel Z Z) t z = Measure.dirac fun _ => z := by
  induction t with
  | zero =>
    have : (fun _ : Fin 0 => z) = Fin.elim0 := funext fun i => i.elim0
    rw [this]
    rfl
  | succ t ih =>
    have := ex_8_8a (Kernel.id : Kernel Z Z) t
    rw [hist, Kernel.comp_id, Kernel.map_apply _ (measurable_cons t), Kernel.prod_apply,
      Kernel.id_apply, ih, Measure.dirac_prod_dirac, Measure.map_dirac' (measurable_cons t)]
    congr 1
    funext i
    exact Fin.cases rfl (fun j => rfl) i

omit [MeasurableSpace Z] in
theorem lastState_const (z : Z) (t : ℕ) : lastState z (fun _ : Fin t => z) = z := by
  cases t <;> rfl

/-- The value of `n + 1` periods of a feasible plan in Blackwell's model. -/
theorem uN_blackwell {E : Set (X × Z)} (hE : MeasurableSet E) (β : ℝ) (s : X × Z)
    {π : Plan X Z} (hπ : ∀ t, Measurable (π t)) (n : ℕ) :
    uN (blackwellModel E β) s π n = ∑ t ∈ Finset.range (n + 1),
      β ^ t * E.indicator 1 (π t fun _ => s.2, s.2) := by
  have hF : Measurable (blackwellModel E β).F :=
    (measurable_one.indicator hE).comp (measurable_snd.fst.prodMk measurable_snd.snd)
  refine Finset.sum_congr rfl fun t _ => ?_
  have hm := measurable_ret (blackwellModel E β) measurable_snd.fst hF s hπ t
  change β ^ t * ∫ h, ret (blackwellModel E β) s π t h ∂hist Kernel.id t s.2 = _
  rw [hist_id, integral_dirac' _ _ hm.stronglyMeasurable]
  change β ^ t * E.indicator 1 (π t _, lastState s.2 _) = _
  rw [lastState_const]

open Classical in
/-- **Blackwell's example.** `v*(x, z) = 1/(1 − β)` on `z ∈ Proj_Z E`, attained by a constant
plan, and `v* = 0` off it; so if `Proj_Z E` is not measurable, neither is `v*`. -/
theorem blackwell_example [Nonempty X] {E : Set (X × Z)} (hE : MeasurableSet E) {β : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) :
    (∀ s : X × Z, vStar (blackwellModel E β) s =
      if s.2 ∈ Prod.snd '' E then (((1 - β)⁻¹ : ℝ) : EReal) else 0) ∧
    (∀ s : X × Z, s.2 ∈ Prod.snd '' E → ∃ y : X,
      planValue (blackwellModel E β) s (fun _ _ => y) = vStar (blackwellModel E β) s) ∧
    (¬MeasurableSet (Prod.snd '' E) → ¬Measurable (vStar (blackwellModel E β))) := by
  set M := blackwellModel E β with hMdef
  have hgeom : HasSum (fun t => β ^ t) (1 - β)⁻¹ := hasSum_geometric_of_lt_one hβ hβ1
  have hind : ∀ p : X × Z, E.indicator (1 : X × Z → ℝ) p ∈ Icc (0 : ℝ) 1 := fun p => by
    by_cases hp : p ∈ E <;> simp [hp]
  -- every feasible plan: `uₙ` is monotone, bounded by `1/(1 − β)`, and zero off the projection
  have hplan : ∀ s : X × Z, ∀ π : Plan X Z, IsFeasible M s π →
      planValue M s π = ⨆ n, (uN M s π n : EReal) ∧
      planValue M s π ≤ (((1 - β)⁻¹ : ℝ) : EReal) ∧
      (s.2 ∉ Prod.snd '' E → planValue M s π = 0) := by
    intro s π hπ
    have hu := uN_blackwell hE β s hπ.1
    have hmono : Monotone fun n => (uN M s π n : EReal) := by
      refine monotone_nat_of_le_succ fun n => EReal.coe_le_coe_iff.2 ?_
      rw [hu, hu, Finset.sum_range_succ (n := n + 1)]
      exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hβ _) (hind _).1)
    have hlim := tendsto_atTop_iSup hmono
    refine ⟨planValue_eq M hlim, ?_, fun hz => ?_⟩
    · rw [planValue_eq M hlim]
      refine iSup_le fun n => EReal.coe_le_coe_iff.2 ?_
      rw [hu, ← hgeom.tsum_eq]
      refine (Finset.sum_le_sum fun t _ => ?_).trans
        (hgeom.summable.sum_le_tsum _ fun t _ => pow_nonneg hβ t)
      exact mul_le_of_le_one_right (pow_nonneg hβ t) (hind _).2
    · have h0 : ∀ n, (uN M s π n : EReal) = 0 := fun n => by
        rw [hu, Finset.sum_eq_zero fun t _ => ?_, EReal.coe_zero]
        rw [indicator_of_notMem (a := (π t fun _ => s.2, s.2)) fun hmem => hz ⟨_, hmem, rfl⟩,
          mul_zero]
      rw [planValue_eq M hlim]
      simp [h0]
  have hconst : ∀ s : X × Z, ∀ y : X, IsFeasible M s fun _ _ => y := fun s y =>
    ⟨fun _ => measurable_const, fun _ _ => mem_univ _⟩
  have hattain : ∀ s : X × Z, ∀ y : X, (y, s.2) ∈ E →
      planValue M s (fun _ _ => y) = (((1 - β)⁻¹ : ℝ) : EReal) := fun s y hy => by
    have hu : ∀ n, uN M s (fun _ _ => y) n = ∑ t ∈ Finset.range (n + 1),
        β ^ t * E.indicator 1 (y, s.2) := uN_blackwell hE β s fun _ => measurable_const
    have ht : Tendsto (fun n => uN M s (fun _ _ => y) n) atTop (𝓝 (1 - β)⁻¹) := by
      simp only [hu, indicator_of_mem hy, Pi.one_apply, mul_one]
      exact hgeom.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact planValue_eq M ((continuous_coe_real_ereal.tendsto _).comp ht)
  have hle : ∀ s : X × Z, vStar M s ≤ (((1 - β)⁻¹ : ℝ) : EReal) := fun s =>
    iSup₂_le fun π hπ => (hplan s π hπ).2.1
  have hval : ∀ s : X × Z, vStar M s =
      if s.2 ∈ Prod.snd '' E then (((1 - β)⁻¹ : ℝ) : EReal) else 0 := by
    intro s
    split_ifs with hz
    · obtain ⟨⟨y, z⟩, hy, rfl⟩ := hz
      refine le_antisymm (hle s) ?_
      rw [← hattain s y hy]
      exact le_iSup₂ (f := fun π (_ : IsFeasible M s π) => planValue M s π) _ (hconst s y)
    · obtain ⟨y⟩ := ‹Nonempty X›
      refine le_antisymm (iSup₂_le fun π hπ => ((hplan s π hπ).2.2 hz).le) ?_
      rw [← (hplan s _ (hconst s y)).2.2 hz]
      exact le_iSup₂ (f := fun π (_ : IsFeasible M s π) => planValue M s π) _ (hconst s y)
  refine ⟨hval, fun s hz => ?_, fun hP hmeas => hP ?_⟩
  · obtain ⟨⟨y, z⟩, hy, hzs⟩ := hz
    refine ⟨y, ?_⟩
    rw [hval]
    simp only [show s.2 ∈ Prod.snd '' E from ⟨_, hy, hzs⟩, ↓reduceIte]
    exact hattain s y (hzs ▸ hy)
  · obtain ⟨x₀⟩ := ‹Nonempty X›
    have hne : (((1 - β)⁻¹ : ℝ) : EReal) ≠ 0 := by
      rw [Ne, EReal.coe_eq_zero]
      exact inv_ne_zero (sub_pos.2 hβ1).ne'
    have hset : Prod.snd '' E =
        (fun z => (x₀, z)) ⁻¹' (vStar M ⁻¹' {(((1 - β)⁻¹ : ℝ) : EReal)}) := by
      ext z
      simp only [mem_preimage, mem_singleton_iff, hval]
      split_ifs with hz
      · exact iff_of_true hz rfl
      · exact iff_of_false hz fun h => hne h.symm
    rw [hset]
    exact (hmeas (measurableSet_singleton _)).preimage measurable_prodMk_left

end StokeyLucasPrescott.StochasticDP
