/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManySectorTech
import EquilibriumApplications.GrowthCertaintyOptimum

/-!
# A many-sector model of stochastic growth: equilibrium prices (Exercise 16.2(b))

SLP §16.2, p. 482. Let `γ*` be the optimal consumption plan of §10.3 (Ex 10.3b: it maximises `u`
on `C ∩ Y`; a hypothesis here). Exercise 16.2(b): there is a continuous linear `ν` with
`(γ*, γ*, ν)` a competitive equilibrium and `ν(c) = Σ_t ∫ p_t(z^t) c_t(z^t) dμ^t(z^t)`,
`p_t ∈ L¹(μ^t)`.

* `ms_linfty_bounds`: the two limit bounds produced in the proof of Theorem 15.9
  (`theorem_15_9`, Chapter 15 part of this project), kept because Theorem 15.9 as stated does not
  record `ν(x⁰) = φ(x⁰)`, which is needed for the cheaper point.
* `ms_paretoOptimal`: `(γ*, γ*)` is Pareto optimal (one consumer, one firm).
* **Exercise 16.2(b)** (`ex_16_2b`): under the corrected hypotheses of `ex_16_2a`, `(γ*, γ*, ν)` is
  a competitive equilibrium for some `ν` of the form (9), with `ν(γ*) = φ(γ*) > 0` for the `φ` of
  Theorem 15.4.

**Corrections.**
* Theorem 15.9 alone does not give a competitive equilibrium: `ν` could vanish (it supports the
  allocation trivially). The cheaper point `0` needs `ν(γ*) > 0`; this follows from
  `ν(γ*) = φ(γ*)` (both limit bounds at `γ*`) and `φ(γ*) ≥ φ(y*) ≥ ε φ(𝟙) > 0` for an interior
  point `y* ≥ ε𝟙` of `Y` (as in the corrected Ex 16.1b). The solutions manual has no solution.
* As in Ex 16.2(a), free disposal of consumption and uniformly positive production are assumed;
  one consumption good.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set

variable {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] {μ : ∀ t, Measure (Ω t)}
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The limit bounds of the proof of Theorem 15.9** (steps 2–3, p. 471–472): under 15.6–15.9′,
for `φ` supporting a feasible allocation there is `ν = Σ_t ∫ p_t (·)_t dμ^t` with
`φ(xᵢ⁰) ≤ ν(z)` for every strictly preferred `z ∈ Xᵢ` and `ν(w) ≤ φ(yⱼ⁰)` for `w ∈ Yⱼ`. -/
theorem ms_linfty_bounds [∀ t, IsFiniteMeasure (μ t)] {X : ι → Set (LinftyTimeState μ)}
    {u : ι → LinftyTimeState μ → ℝ} {Y : κ → Set (LinftyTimeState μ)}
    {x : ι → LinftyTimeState μ} {y : κ → LinftyTimeState μ}
    (h6 : Assumption15_6_timeState X Y) (h7 : Assumption15_7_timeState X u)
    (h8 : Assumption15_8' μ X Y) (h9 : Assumption15_9' μ X u)
    (hF : Feasible X Y x y) {φ : StrongDual ℝ (LinftyTimeState μ)}
    (hφ : SupportsAllocation X u Y x y φ) :
    ∃ ν : StrongDual ℝ (LinftyTimeState μ),
      (∀ i, ∀ z ∈ X i, u i (x i) < u i z → φ (x i) ≤ ν z) ∧
      (∀ j, ∀ w ∈ Y j, ν w ≤ φ (y j)) ∧
      ∃ p : ∀ t, Ω t → ℝ, (∀ t, Integrable (p t) (μ t)) ∧
        ∀ z, HasSum (fun t => ∫ w, p t w * z t w ∂(μ t)) (ν z) := by
  obtain ⟨A, hA, νt, hνlim, hνp, ν, -, hνsum⟩ := exists_linftyTimeState_decomposition φ
  choose p hp hpν using hνp
  refine ⟨ν, ?_, ?_, p, hp, fun z => by simpa only [hpν] using hνsum z⟩
  · intro i z hz hlt
    have hev : ∀ᶠ T in atTop, φ (x i) ≤ ∑ t ∈ Finset.range (T + 1), νt t (z t) := by
      filter_upwards [h6.1 i z hz, h7 i z hz (x i) (hF.1 i) hlt] with T hT1 hT2
      have h := linftyTS_consumer_bound h8 h9 (hF.1 i) (hφ.1 i) hA hνlim (T + 1) _ hT1 hT2
      rw [linftyTimeTrunc_drop, map_zero, add_zero] at h
      rwa [Finset.sum_congr rfl (g := fun t => νt t (z t)) fun t ht => by
        simp only [linftyTimeTrunc_apply, Nat.lt_succ_iff.1 (Finset.mem_range.1 ht),
          ↓reduceIte]] at h
    exact ge_of_tendsto ((hνsum z).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)) hev
  · intro j w hw
    have hev : ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1), νt t (w t) ≤ φ (y j) := by
      filter_upwards [h6.2 j w hw] with T hT
      have h := linftyTS_firm_bound h8 (hφ.2 j) hA hνlim (T + 1) _ hT
      rw [linftyTimeTrunc_drop, map_zero, add_zero] at h
      rwa [Finset.sum_congr rfl (g := fun t => νt t (w t)) fun t ht => by
        simp only [linftyTimeTrunc_apply, Nat.lt_succ_iff.1 (Finset.mem_range.1 ht),
          ↓reduceIte]] at h
    exact le_of_tendsto ((hνsum w).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)) hev

variable {Z : Type*} [TopologicalSpace Z] {l : ℕ} {Xc : Set (Fin l → ℝ)}
  {Φ : (Fin l → ℝ) → Z → Set (ℝ × (Fin l → ℝ))} {proj : ∀ t, Ω (t + 1) → Ω t}
  {ζ : ∀ t, Ω t → Z} {xhat : Fin l → ℝ} {U : ℝ → ℝ} {β : ℝ} [∀ t, IsProbabilityMeasure (μ t)]

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- `0 ∈ C`. -/
theorem ms_zero_mem_C : (0 : LinftyTimeState μ) ∈ msC μ := fun t => by
  filter_upwards [Lp.coeFn_zero ℝ ⊤ (μ t)] with ω h
  change 0 ≤ (0 : Lp ℝ ⊤ (μ t)) ω
  rw [h]; rfl

/-- `(γ*, γ*)` is Pareto optimal in the one-consumer, one-firm economy. -/
theorem ms_paretoOptimal (H : ManySectorHyp U β) (hT : MsTech Xc Φ) {γ : LinftyTimeState μ}
    (hγC : γ ∈ msC μ) (hγY : γ ∈ msY μ proj ζ Φ xhat)
    (hopt : ∀ c ∈ msC μ, c ∈ msY μ proj ζ Φ xhat → msU μ β U c ≤ msU μ β U γ) :
    ParetoOptimal (fun _ : Unit => msC μ) (fun _ => msU μ β U)
      (fun _ : Unit => msY μ proj ζ Φ xhat) (fun _ => γ) (fun _ => γ) :=
  (gc_symmetric_paretoOptimal_iff ms_convex_C (ms_convex_Y hT) (ms_U_concave H) γ γ).2
    ⟨rfl, hγC, hγY, hopt⟩

/-- **Exercise 16.2(b)** (corrected hypotheses as in `ex_16_2a`): if `γ*` maximises `u` on `C ∩ Y`
(Ex 10.3b), there is a continuous linear `ν` such that `(γ*, γ*, ν)` is a competitive equilibrium
and `ν(c) = Σ_t ∫ p_t c_t dμ^t` with every `p_t ∈ L¹(μ^t)`; moreover `ν(γ*) > 0`. -/
theorem ex_16_2b (H : ManySectorHyp U β) (hT : MsTech Xc Φ) (hfd : MsFreeDisposal Φ)
    (hpos : MsPositiveProduction μ proj ζ Φ xhat) {γ : LinftyTimeState μ} (hγC : γ ∈ msC μ)
    (hγY : γ ∈ msY μ proj ζ Φ xhat)
    (hopt : ∀ c ∈ msC μ, c ∈ msY μ proj ζ Φ xhat → msU μ β U c ≤ msU μ β U γ) :
    ∃ ν : StrongDual ℝ (LinftyTimeState μ),
      CompetitiveEq (fun _ : Unit => msC μ) (fun _ => msU μ β U)
        (fun _ : Unit => msY μ proj ζ Φ xhat) (fun _ => γ) (fun _ => γ) ν ∧ 0 < ν γ ∧
      ∃ p : ∀ t, Ω t → ℝ, (∀ t, Integrable (p t) (μ t)) ∧
        ∀ c, HasSum (fun t => ∫ ω, p t ω * c t ω ∂(μ t)) (ν c) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ex_16_2a H hT hfd hpos
  have hPO := ms_paretoOptimal H hT hγC hγY hopt
  have hsatX := ms_add_one_mem hγC
  have hsat := ms_U_lt_add_one H hγC
  obtain ⟨φ, hne, hφ⟩ := theorem_15_4 h1 h2 h3 h4 h5 hPO (h := ()) hsatX hsat
  -- `φ(γ*) > 0`
  have hφpos : ∀ z ∈ msC μ, 0 ≤ φ z := fun z hz =>
    ms_supporting_nonneg H hγC (fun w hw hle => hφ.1 () w hw hle) hz
  obtain ⟨ystar, hystar⟩ := ms_interior_Y hfd hpos (proj := proj) (ζ := ζ) (xhat := xhat)
  obtain ⟨ε, hε, hεy⟩ := ms_interior_ge (ms_Y_sub_C hT) hystar
  have hyφ := hφpos _ hεy
  rw [map_add, map_smul, smul_eq_mul] at hyφ
  have hφ1 := ms_one_pos hφpos hne
  have hφγ : 0 < φ γ := by
    have := hφ.2 () ystar (interior_subset hystar)
    nlinarith
  -- the limit bounds of Theorem 15.9 and `ν(γ*) = φ(γ*)`
  obtain ⟨ν, hνX, hνY, p, hp, hpν⟩ := ms_linfty_bounds h6 h7 h8 h9 hPO.1 hφ
  have hνsup := supportsAllocation_of_limit_bounds h1 h2 hPO.1 (fun _ => ⟨_, hsatX, hsat⟩) hνX hνY
  have hle1 : ν γ ≤ φ γ := hνY () γ hγY
  have hle2 : φ γ ≤ ν γ := by
    have hc : Continuous fun θ : ℝ => ν γ + θ * ν (msOne μ) := by fun_prop
    have ht : Tendsto (fun θ : ℝ => ν γ + θ * ν (msOne μ)) (𝓝[>] 0) (𝓝 (ν γ)) := by
      have := hc.tendsto 0
      simp only [zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
    have hmem : θ • (γ + msOne μ) + (1 - θ) • γ ∈ msC μ :=
      ms_convex_C hsatX hγC hθ.1.le (by linarith [hθ.2]) (by ring)
    have hlt := h2 () _ hsatX γ hγC hsat θ hθ.1 hθ.2
    have := hνX () _ hmem hlt
    have e : θ • (γ + msOne μ) + (1 - θ) • γ = γ + θ • msOne μ := by
      rw [smul_add, add_comm (θ • γ), add_assoc, ← add_smul, add_sub_cancel, one_smul,
        add_comm]
    rw [e, map_add, map_smul, smul_eq_mul] at this
    exact this
  have hνγ : ν γ = φ γ := le_antisymm hle1 hle2
  refine ⟨ν, remark_cheaper_point h1 h3 hPO.1 hνsup fun _ => ⟨0, ms_zero_mem_C, by
    rw [map_zero, hνγ]; exact hφγ⟩, hνγ ▸ hφγ, p, hp, hpν⟩

end StokeyLucasPrescott.EquilibriumApplications
