/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearDecisionProcesses.ExogenousDiscount
import LinearDecisionProcesses.LDPOptimality

/-!
# An LDP with exogenous discounting

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.1.4.2 (pp. 195–197).

The state is `x = (y, z) ∈ Y × Z` with `Z` finite and discrete, and the kernel has the form
`(Kh)(y, z, a) = β(z) ∫ ∑_{z'} h(y', z')Q(z, z')R(y, z, a, dy')`: the endogenous state moves by
`R`, the exogenous state by `Q`, and only `z` drives discounting.

* `continuousOn_of_slices`: with `Z` discrete, continuity on `G` reduces to continuity on each
  slice `G_z`, which is the form of Assumption 6.1.2.
* **Proposition 6.1.6**: under Assumptions 6.1.1–6.1.2 and `ρ(K_Q) < 1`, the fundamental optimality
  properties hold, `v* ∈ bcX` and VFI converges geometrically on `bcX`.

The book's discount operator
`(Dh)(y, z) = β(z) sup_{a ∈ Γ(y, z)} ∫ ∑_{z'} h(y', z')Q R(y, z, a, dy')` need not be Borel
measurable in `y` for measurable `h` (a supremum over an uncountable family), so it
need not map `bX` into itself. The proof uses instead
`(Dh)(y, z) = β(z) ∑_{z'} sup_{y'} h(y', z') Q(z, z')`, which also dominates every `K_σ`, depends on
`z` only, and satisfies `Dⁿh = K_Qⁿ m_h` with `m_h(z') = sup_{y'} h(y', z')`, so the book's
eventual contraction argument goes through.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.LinearDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono hasSolidNorm_pi

/-- With `Z` discrete, a function continuous on every slice `G_z` is continuous on `G`. -/
theorem continuousOn_of_slices {Y Z A : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    [DiscreteTopology Z] [TopologicalSpace A] {G : Set ((Y × Z) × A)} {f : (Y × Z) × A → ℝ}
    (h : ∀ z, ContinuousOn (fun q : Y × A => f ((q.1, z), q.2)) {q | ((q.1, z), q.2) ∈ G}) :
    ContinuousOn f G := by
  intro p hp
  let z₀ := p.1.2
  let U : Set ((Y × Z) × A) := {p' | p'.1.2 = z₀}
  have hU : U ∈ 𝓝 p :=
    ((isOpen_discrete {z₀}).preimage (continuous_snd.comp continuous_fst)).mem_nhds rfl
  let π : (Y × Z) × A → Y × A := fun p' => (p'.1.1, p'.2)
  have hπ : Continuous π := (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hmaps : MapsTo π (G ∩ U) {q | ((q.1, z₀), q.2) ∈ G} := fun p' ⟨hp', hz⟩ => by
    change ((p'.1.1, z₀), p'.2) ∈ G
    rw [← show p'.1.2 = z₀ from hz]
    exact hp'
  have hc := (h z₀ (π p) (by change ((p.1.1, p.1.2), p.2) ∈ G; exact hp)).comp
    hπ.continuousWithinAt hmaps
  have heq : EqOn f ((fun q : Y × A => f ((q.1, z₀), q.2)) ∘ π) (G ∩ U) := fun p' ⟨_, hz⟩ => by
    change f p' = f ((p'.1.1, z₀), p'.2)
    rw [← show p'.1.2 = z₀ from hz]
  exact (continuousWithinAt_inter hU).1 (hc.congr heq (heq ⟨hp, rfl⟩))

namespace LDP

attribute [local instance] LDP.P_markov

variable {Y Z A : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace A]

/-- `m_h(z') = sup_{y'} h(y', z')`. -/
noncomputable def supY (h : BM (Y × Z)) (z : Z) : ℝ := ⨆ y, h.toFun (y, z)

theorem bddAbove_slice (h : BM (Y × Z)) (z : Z) : BddAbove (range fun y => h.toFun (y, z)) :=
  ⟨‖h‖, by rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (BM.abs_le_norm h _)⟩

theorem le_supY (h : BM (Y × Z)) (y : Y) (z : Z) : h.toFun (y, z) ≤ supY h z :=
  le_ciSup (bddAbove_slice h z) y

theorem abs_supY_le (h : BM (Y × Z)) (z : Z) : |supY h z| ≤ ‖h‖ := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · rw [supY, Real.iSup_of_isEmpty, abs_zero]
    exact norm_nonneg _
  · refine abs_le.2 ⟨?_, ciSup_le fun y => (le_abs_self _).trans (BM.abs_le_norm h _)⟩
    obtain ⟨y⟩ := hY
    exact (neg_le.2 ((neg_le_abs _).trans (BM.abs_le_norm h (y, z)))).trans (le_supY h y z)

theorem abs_supY_sub_le (u v : BM (Y × Z)) (z : Z) : |supY u z - supY v z| ≤ ‖u - v‖ := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · simp [supY]
  · exact abs_ciSup_sub_ciSup_le (bddAbove_slice u z) (bddAbove_slice v z) fun y =>
      (BM.abs_sub_le_dist u v (y, z)).trans (dist_eq_norm u v).le

/-- The measurable discount operator `(Dh)(y, z) = β(z) ∑_{z'} sup_{y'} h(y', z') Q(z, z')`. -/
noncomputable def Dexo [Fintype Z] [MeasurableSingletonClass Z] (βz : Z → ℝ) (Q : Z → Z → ℝ)
    (h : BM (Y × Z)) : BM (Y × Z) :=
  ⟨fun x => Exo.K βz Q (supY h) x.2, (measurable_of_countable _).comp measurable_snd,
    ⟨‖Exo.K βz Q (supY h)‖, fun x => by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (Exo.K βz Q (supY h)) x.2⟩⟩

theorem supY_lift [Nonempty Y] (g : Z → ℝ) (hm : Measurable fun x : Y × Z => g x.2)
    (hb : ∃ C, ∀ x : Y × Z, |g x.2| ≤ C) :
    supY (⟨fun x => g x.2, hm, hb⟩ : BM (Y × Z)) = g := funext fun z => by
  change (⨆ _ : Y, g z) = g z
  exact ciSup_const

theorem Dexo_iterate [Fintype Z] [MeasurableSingletonClass Z] [Nonempty Y] (βz : Z → ℝ)
    (Q : Z → Z → ℝ) (h : BM (Y × Z)) (n : ℕ)
    (x : Y × Z) : ((Dexo βz Q)^[n + 1] h).toFun x = (Exo.K βz Q ^ (n + 1)) (supY h) x.2 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply']
    change Exo.K βz Q (supY ((Dexo βz Q)^[n + 1] h)) x.2 = _
    have : supY ((Dexo βz Q)^[n + 1] h) = (Exo.K βz Q ^ (n + 1)) (supY h) :=
      funext fun z => by
        rw [supY]
        simp_rw [ih]
        exact ciSup_const
    rw [this, pow_succ' (Exo.K βz Q) (n + 1)]
    rfl

/-- `D` is a discount operator when `ρ(K_Q) < 1` (proof of Proposition 6.1.6). -/
theorem Dexo_isDiscountOperator [Fintype Z] [MeasurableSingletonClass Z] {βz : Z → ℝ}
    (hβ : ∀ z, 0 ≤ βz z) {Q : Z → Z → ℝ}
    (hQ : ∀ z z', 0 ≤ Q z z') (hρ : BanachLattice.specRad (Exo.K βz Q) < 1) :
    BanachLattice.IsDiscountOperator (Dexo (Y := Y) βz Q) := by
  have hpos := Exo.K_isPositive hβ hQ
  have hsupmono : ∀ u v : BM (Y × Z), u ≤ v → supY u ≤ supY v := fun u v huv z => by
    rcases isEmpty_or_nonempty Y with hY | hY
    · simp [supY]
    · exact ciSup_le fun y => (huv (y, z)).trans (le_supY v y z)
  obtain ⟨n, hn, lam, hlam0, hlam1, hK⟩ := (BanachLattice.lemma_6_1_5 (Exo.K βz Q)).1 hρ
  refine ⟨BM.ext fun x => ?_, fun h hh x => ?_, fun u _ v _ huv x => ?_, n, hn, lam, hlam0,
    hlam1, fun u _ v _ => ?_⟩
  · change Exo.K βz Q (supY 0) x.2 = 0
    have : supY (0 : BM (Y × Z)) = 0 := funext fun z => by
      rcases isEmpty_or_nonempty Y with hY | hY
      · exact Real.iSup_of_isEmpty _
      · exact ciSup_const
    rw [this, map_zero]
    rfl
  · exact hpos _ (fun z => Real.iSup_nonneg fun y => hh (y, z)) x.2
  · exact hpos.mono (hsupmono u v huv) x.2
  · rcases isEmpty_or_nonempty Y with hY | hY
    · have : IsEmpty (Y × Z) := inferInstance
      rw [show (Dexo βz Q)^[n] u - (Dexo βz Q)^[n] v = 0 from BM.ext fun x => isEmptyElim x,
        norm_zero]
      exact mul_nonneg hlam0 (norm_nonneg _)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine BM.norm_le (mul_nonneg hlam0 (norm_nonneg _)) fun x => ?_
      rw [BM.sub_apply, Dexo_iterate, Dexo_iterate, ← Pi.sub_apply, ← map_sub]
      have h1 : ‖supY u - supY v‖ ≤ ‖u - v‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun z => by
          rw [Real.norm_eq_abs]; exact abs_supY_sub_le u v z
      calc |(Exo.K βz Q ^ (m + 1)) (supY u - supY v) x.2|
          ≤ ‖(Exo.K βz Q ^ (m + 1)) (supY u - supY v)‖ := by
            rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ x.2
        _ ≤ lam * ‖supY u - supY v‖ := hK _
        _ ≤ lam * ‖u - v‖ := mul_le_mul_of_nonneg_left h1 hlam0

variable (M : LDP (Y × Z) A)

/-- `K_σ ≤ D` (proof of Proposition 6.1.6). -/
theorem K_le_Dexo [Fintype Z] [MeasurableSingletonClass Z] {βz : Z → ℝ} (hβ : ∀ z, 0 ≤ βz z)
    {Q : Z → Z → ℝ} (hQ : ∀ z z', 0 ≤ Q z z')
    (hβM : ∀ p : (Y × Z) × A, M.β.toFun p = βz p.1.2) (R : Kernel ((Y × Z) × A) Y)
    [IsMarkovKernel R]
    (hP : ∀ (h : BM (Y × Z)) (p : (Y × Z) × A),
      ∫ x', h.toFun x' ∂(M.P p) = ∫ y', ∑ z', h.toFun (y', z') * Q p.1.2 z' ∂(R p))
    (σ : M.Policy) (h : BM (Y × Z)) : M.K σ h ≤ Dexo βz Q h := fun x => by
  rw [K_apply, hβM, hP]
  change βz x.2 * _ ≤ βz x.2 * ∑ z', supY h z' * Q x.2 z'
  refine mul_le_mul_of_nonneg_left ?_ (hβ _)
  have hint : Integrable (fun y' => ∑ z', h.toFun (y', z') * Q x.2 z') (R (x, σ.1 x)) :=
    integrable_finsetSum _ fun z' _ => (Integrable.of_bound
      (h.measurable'.comp measurable_prodMk_right).aestronglyMeasurable ‖h‖
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact BM.abs_le_norm h _)).mul_const _
  calc ∫ y', ∑ z', h.toFun (y', z') * Q x.2 z' ∂(R (x, σ.1 x))
      ≤ ∫ _, ∑ z', supY h z' * Q x.2 z' ∂(R (x, σ.1 x)) :=
        integral_mono hint (integrable_const _) fun y' => Finset.sum_le_sum fun z' _ =>
          mul_le_mul_of_nonneg_right (le_supY h y' z') (hQ _ _)
    _ = ∑ z', supY h z' * Q x.2 z' := by simp

/-- **Proposition 6.1.6** (p. 196): for an LDP on `X = Y × Z` with `Z` finite and
`(Kh)(y, z, a) = β(z) ∫ ∑_{z'} h(y', z')Q(z, z')R(y, z, a, dy')`, under Assumption 6.1.1 (`Γ` with
the maximum theorem, `r` continuous on `G`), Assumption 6.1.2 (`(y, a) ↦ ∫ g(y')R(y, z, a, dy')`
continuous on `G_z` for `g ∈ bcY`) and `ρ(K_Q) < 1`, (i) the fundamental optimality properties
hold, (ii) `v* ∈ bcX` and (iii) VFI converges geometrically on `bcX`. -/
theorem proposition_6_1_6 [TopologicalSpace Y] [TopologicalSpace Z] [DiscreteTopology Z]
    [TopologicalSpace A] [Fintype Z] [MeasurableSingletonClass Z] (hB : HasMaxSelections M.Γ)
    (hr : ContinuousOn M.r.toFun M.G) {βz : Z → ℝ} (hβ : ∀ z, 0 ≤ βz z) {Q : Z → Z → ℝ}
    (hQ : ∀ z z', 0 ≤ Q z z') (hβM : ∀ p : (Y × Z) × A, M.β.toFun p = βz p.1.2)
    (R : Kernel ((Y × Z) × A) Y) [IsMarkovKernel R]
    (hP : ∀ (h : BM (Y × Z)) (p : (Y × Z) × A),
      ∫ x', h.toFun x' ∂(M.P p) = ∫ y', ∑ z', h.toFun (y', z') * Q p.1.2 z' ∂(R p))
    (hR : ∀ z, ∀ g : BM Y, Continuous g.toFun →
      ContinuousOn (fun q : Y × A => ∫ y', g.toFun y' ∂(R ((q.1, z), q.2)))
        {q | q.2 ∈ M.Γ (q.1, z)})
    (hρ : BanachLattice.specRad (Exo.K βz Q) < 1) :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧ ∃ vstar ∈ bc (Y × Z),
      M.adp.VFIGeometric (bc (Y × Z)) vstar := by
  -- `K` is weak Feller
  have hK : M.IsWeakFeller := by
    intro h hc
    refine continuousOn_of_slices fun z => ?_
    have hslice : ∀ z' : Z, ∃ g : BM Y, Continuous g.toFun ∧ ∀ y, g.toFun y = h.toFun (y, z') :=
      fun z' => ⟨⟨fun y => h.toFun (y, z'), h.measurable'.comp measurable_prodMk_right,
        ⟨‖h‖, fun _ => BM.abs_le_norm h _⟩⟩, hc.comp (continuous_id.prodMk continuous_const),
        fun _ => rfl⟩
    choose g hgc hg using hslice
    have hform : ∀ q : Y × A, M.β.toFun ((q.1, z), q.2) * ∫ x', h.toFun x' ∂(M.P ((q.1, z), q.2))
        = βz z * ∑ z', Q z z' * ∫ y', (g z').toFun y' ∂(R ((q.1, z), q.2)) := fun q => by
      have hint : ∀ z' ∈ Finset.univ, Integrable (fun y' => h.toFun (y', z') * Q z z')
          (R ((q.1, z), q.2)) := fun z' _ => (Integrable.of_bound
        (h.measurable'.comp measurable_prodMk_right).aestronglyMeasurable ‖h‖
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact BM.abs_le_norm h _)).mul_const _
      have e1 : ∫ y', ∑ z', h.toFun (y', z') * Q z z' ∂(R ((q.1, z), q.2)) =
          ∑ z', ∫ y', h.toFun (y', z') * Q z z' ∂(R ((q.1, z), q.2)) :=
        integral_finsetSum Finset.univ hint
      rw [hβM, hP]
      change βz z * ∫ y', ∑ z', h.toFun (y', z') * Q z z' ∂(R ((q.1, z), q.2)) = _
      rw [e1]
      congr 1
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [integral_mul_const, mul_comm]
      simp_rw [hg]
    simp_rw [hform]
    exact continuousOn_const.mul (continuousOn_finsetSum _ fun z' _ =>
      continuousOn_const.mul (hR z (g z') (hgc z')))
  obtain ⟨hw, hFO, vstar, hv, hgeo, -⟩ := M.proposition_6_1_3 hB hr hK
    (Dexo_isDiscountOperator hβ hQ hρ) fun σ h _ => M.K_le_Dexo hβ hQ hβM R hP σ h
  exact ⟨hw, hFO, vstar, hv, hgeo⟩

end LDP

end SargentStachurski.LinearDecisionProcesses
