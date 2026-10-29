/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.LadderInvariant

/-!
# The invariant measure of the GI/G/1 queue (MT §10.5.3)

Meyn and Tweedie, pp. 251–252. `gig1Ladder H G` is the ladder chain (3.40), (3.42)–(3.43) of the
embedded GI/G/1 queue (`LadderChains`), with service law `H` and interarrival law `G`; its
kernels are `Λ = gig1Lambda H G` and `Λ* = gig1LambdaStar H G`, and `S = ladS Λ Λ*` is the minimal
solution of (10.40)/(10.53).

* `gig1_entrance`: every entrance to the bottom rung `[0]` has the law `H`:
  `P(z, 0 × A) = P(z, [0]) H(A)` (3.43). Hence `U_{[0]}(z, 0 × A) = L(z, [0]) H(A)`: the process on
  `[0]` is an i.i.d. sequence with law `H` (p. 251).
* `gig1Tilde H G`: the measure `π̃(k × A) = ∫ H(dy) Sᵏ(y, A)` of (10.52)
  (`gig1Tilde_apply_prod`).
* **Theorem 10.5.4** (p. 252): `theorem_10_5_4_invariant`, if `π̃` is finite it is invariant, so
  `π̃/π̃(X)` is an invariant probability; `theorem_10_5_4_eq`, for a recurrent chain with
  `ψ([0]) > 0` every invariant probability is `π([0]) π̃`; `theorem_10_5_4`: the chain has an
  invariant probability iff `π̃` is finite, and it is then `π̃/π̃(X)`.

**Hypotheses.** Theorem 10.5.4 is stated in the book for a positive Harris chain with
`ψ([0]) > 0` (the standing assumption of §10.5.3); the direction "`π̃` finite ⇒ invariant
probability" needs no irreducibility, the converse uses recurrence and `ψ([0]) > 0`.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G]

/-- The GI/G/1 ladder chain is the ladder chain of `Λ = gig1Lambda`, `Λ* = gig1LambdaStar`. -/
theorem gig1Ladder_eq :
    gig1Ladder H G = ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G) := rfl

/-- (3.43): every entrance to `[0]` has the law `H`: `P(z, 0 × A) = P(z, [0]) H(A)`. -/
theorem gig1_entrance (z : ℕ × ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G) z ({0} ×ˢ A) =
      ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G) z (rung 0) * H A := by
  obtain ⟨i, x⟩ := z
  rw [rung, eq_3_40_zero _ _ i x hA, eq_3_40_zero _ _ i x MeasurableSet.univ]
  change ((∑' j, gig1Lambda H G (j + i + 1) x univ) • H) A =
    ((∑' j, gig1Lambda H G (j + i + 1) x univ) • H) univ * H A
  simp

/-- The measure `π̃(k × A) = ∫ H(dy) Sᵏ(y, A)` of (10.52). -/
noncomputable def gig1Tilde : Measure (ℕ × ℝ) :=
  Measure.sum fun k =>
    ((ladS (gig1Lambda H G) (gig1LambdaStar H G) ^ k : Kernel ℝ ℝ) ∘ₘ H).map (Prod.mk k)

/-- `π̃(j × A) = ∫ H(dy) Sʲ(y, A)`. -/
theorem gig1Tilde_apply_prod (j : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    gig1Tilde H G ({j} ×ˢ A) =
      ∫⁻ y, (ladS (gig1Lambda H G) (gig1LambdaStar H G) ^ j) y A ∂H := by
  have hE : MeasurableSet ({j} ×ˢ A : Set (ℕ × ℝ)) := (measurableSet_singleton j).prod hA
  rw [gig1Tilde, Measure.sum_apply _ hE, tsum_eq_single j]
  · rw [Measure.map_apply measurable_prodMk_left hE, measure_kernel_apply _ _ (by
      convert hA using 1; ext y; simp)]
    congr 1
    ext y; simp
  · intro k hk
    rw [Measure.map_apply measurable_prodMk_left hE]
    convert measure_empty
      (μ := (ladS (gig1Lambda H G) (gig1LambdaStar H G) ^ k : Kernel ℝ ℝ) ∘ₘ H)
    ext y; simp [hk]

/-- `μ(X) = Σₖ μ(k × ℝ)` on `ℤ₊ × ℝ`. -/
theorem measure_univ_nat_prod (μ : Measure (ℕ × ℝ)) : μ univ = ∑' k, μ ({k} ×ˢ univ) := by
  have := lintegral_nat_prod μ (f := fun _ => 1) measurable_const
  simp only [lintegral_const, one_mul] at this
  rw [this]
  exact tsum_congr fun k => map_snd_restrict_rung_apply μ k MeasurableSet.univ

/-- The bottom-rung law `ν = δ₀ ⊗ H`. -/
noncomputable def gig1Bottom : Measure (ℕ × ℝ) := H.map (Prod.mk 0)

omit [IsProbabilityMeasure H] in
/-- `ν` lives on `[0]`. -/
theorem gig1Bottom_restrict : (gig1Bottom H).restrict (rung 0) = gig1Bottom H := by
  ext S hS
  rw [Measure.restrict_apply hS, gig1Bottom, Measure.map_apply measurable_prodMk_left hS,
    Measure.map_apply measurable_prodMk_left (hS.inter (measurableSet_rung 0))]
  congr 1
  ext y; simp [rung]

variable [IsMarkovKernel (ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G))]

omit [IsMarkovKernel (ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G))] in
/-- `ν°(k × A) = ∫ H(dy) U_{[0]}(0, y; k × A)` for `ν° = ∫_{[0]} ν(dz) U_{[0]}(z, ·)`. -/
theorem gig1_minimal_apply {E : Set (ℕ × ℝ)} (hE : MeasurableSet E) :
    minimalMeasure (ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G))
        (measurableSet_rung 0) (gig1Bottom H) E =
      ∫⁻ y, tabooPotKernel (ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G))
        (measurableSet_rung 0) (0, y) E ∂H := by
  rw [minimalMeasure, gig1Bottom_restrict, measure_kernel_apply _ _ hE, gig1Bottom,
    lintegral_map (Kernel.measurable_coe _ hE) measurable_prodMk_left]

/-- **Theorem 10.5.4**, sufficiency (MT p. 252): if `π̃(X) < ∞` then `π̃` is invariant. -/
theorem theorem_10_5_4_invariant (hfin : gig1Tilde H G univ ≠ ∞) :
    IsInvariant (gig1Ladder H G) (gig1Tilde H G) := by
  have hU0 : ∀ y {A : Set ℝ}, MeasurableSet A →
      tabooPotKernel (ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G))
        (measurableSet_rung 0) (0, y) ({0} ×ˢ A) =
      hitProb (ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G)) (rung 0) (0, y) * H A :=
    fun y A hA =>
    tabooPotKernel_rung_zero_of_entrance _ _ H (fun z A hA => gig1_entrance H G z hA) _ hA
  set P := ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G)
  set ν := gig1Bottom H
  set M := minimalMeasure P (measurableSet_rung 0) ν
  have hU0P : ∀ y {A : Set ℝ}, MeasurableSet A → tabooPotKernel P (measurableSet_rung 0) (0, y)
      ({0} ×ˢ A) = hitProb P (rung 0) (0, y) * H A := hU0
  -- `M` agrees with `π̃` above `[0]` and is below it on `[0]`
  have hM : ∀ k {A : Set ℝ}, MeasurableSet A → 1 ≤ k → M ({k} ×ˢ A) = gig1Tilde H G ({k} ×ˢ A) :=
    fun k A hA hk => by
      rw [gig1_minimal_apply H G ((measurableSet_singleton k).prod hA),
        gig1Tilde_apply_prod H G k hA, ← ladderS_eq_pow _ _ hk]
      exact lintegral_congr fun y => (ladderS_apply _ _ k y hA).symm
  have hM0 : ∀ {A : Set ℝ}, MeasurableSet A →
      M ({0} ×ˢ A) = (∫⁻ y, hitProb P (rung 0) (0, y) ∂H) * H A := fun {A} hA => by
    rw [gig1_minimal_apply H G ((measurableSet_singleton 0).prod hA)]
    simp_rw [hU0 _ hA]
    exact lintegral_mul_const _ ((measurable_hitProb P (measurableSet_rung 0)).comp
      measurable_prodMk_left)
  have hT0 : ∀ {A : Set ℝ}, MeasurableSet A → gig1Tilde H G ({0} ×ˢ A) = H A := fun {A} hA => by
    rw [gig1Tilde_apply_prod H G 0 hA, pow_zero]
    change ∫⁻ y, Kernel.id y A ∂H = _
    simp_rw [Kernel.id_apply, Measure.dirac_apply' _ hA]
    exact lintegral_indicator_one hA
  -- `M` is finite, hence the return to `[0]` is sure from `H`-almost every point
  have hMfin : M univ ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin ?_
    rw [measure_univ_nat_prod M, measure_univ_nat_prod (gig1Tilde H G)]
    refine ENNReal.tsum_le_tsum fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hM0 MeasurableSet.univ, hT0 MeasurableSet.univ, measure_univ, mul_one, ← measure_univ
        (μ := H), ← lintegral_one]
      exact lintegral_mono fun y => hitProb_le_one P _ _
    · rw [hM k MeasurableSet.univ hk]
  have hmean : ∀ᵐ y ∂H, meanReturnTime P (rung 0) (0, y) ≠ ∞ := by
    have hm : Measurable fun y => meanReturnTime P (rung 0) (0, y) := by
      simp_rw [meanReturnTime_eq_tabooPotKernel P (measurableSet_rung 0)]
      exact (Kernel.measurable_coe _ MeasurableSet.univ).comp measurable_prodMk_left
    have h1 : M univ = ∫⁻ y, meanReturnTime P (rung 0) (0, y) ∂H := by
      rw [gig1_minimal_apply H G MeasurableSet.univ]
      simp_rw [meanReturnTime_eq_tabooPotKernel P (measurableSet_rung 0)]
      rfl
    rw [h1] at hMfin
    filter_upwards [ae_lt_top hm hMfin] with y hy using hy.ne
  have hL : ∀ᵐ y ∂H, hitProb P (rung 0) (0, y) = 1 := hmean.mono fun y hy =>
    hitProb_eq_one_of_meanReturnTime_ne_top (measurableSet_rung 0) hy
  have hLint : ∫⁻ y, hitProb P (rung 0) (0, y) ∂H = 1 := by
    rw [lintegral_congr_ae (hL.mono fun y hy => hy), lintegral_one, measure_univ]
  -- `M = π̃`
  have hMT : M = gig1Tilde H G := by
    refine ext_nat_prod fun k A hA => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hM0 hA, hLint, one_mul, hT0 hA]
    · exact hM k hA hk
  -- `M` is invariant (Proposition 10.4.8)
  have hinv : IsInvariant P M := by
    refine proposition_10_4_8 P (measurableSet_rung 0) fun B hB hsub => ?_
    have hBeq : B = {0} ×ˢ (Prod.mk 0 ⁻¹' B) := by
      ext p
      simp only [mem_prod, mem_singleton_iff, mem_preimage]
      constructor
      · intro h
        have h0 : p.1 = 0 := (hsub h).1
        refine ⟨h0, ?_⟩
        have : p = (0, p.2) := Prod.ext h0 rfl
        rwa [← this]
      · rintro ⟨h0, h⟩
        have : p = (0, p.2) := Prod.ext h0 rfl
        rwa [this]
    have hB' : MeasurableSet (Prod.mk 0 ⁻¹' B : Set ℝ) := measurable_prodMk_left hB
    rw [setLIntegral_rung_zero ν (Kernel.measurable_coe _ hB), gig1Bottom_restrict]
    change ∫⁻ y, _ ∂(H.map (Prod.mk 0)).map Prod.snd = (H.map (Prod.mk 0)) B
    rw [Measure.map_map measurable_snd measurable_prodMk_left, Measure.map_apply
      measurable_prodMk_left hB]
    have hid : (Prod.snd ∘ Prod.mk (0 : ℕ) : ℝ → ℝ) = id := rfl
    rw [hid, Measure.map_id, hBeq]
    simp_rw [hU0P _ hB']
    rw [lintegral_mul_const (f := fun y => hitProb P (rung 0) (0, y)) _
      ((measurable_hitProb P (measurableSet_rung 0)).comp measurable_prodMk_left), hLint, one_mul]
    congr 1
    ext y; simp
  rw [← hMT]
  exact hinv

/-- **Theorem 10.5.4**, the form of `π` (MT p. 252): for a recurrent GI/G/1 ladder chain with
`ψ([0]) > 0`, every invariant probability is `π = π([0]) π̃`. -/
theorem theorem_10_5_4_eq {ψ : Measure (ℕ × ℝ)}
    (hrec : IsRecurrentChain (ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G)) ψ)
    (hψ0 : 0 < ψ (rung 0)) {π : Measure (ℕ × ℝ)} [IsProbabilityMeasure π]
    (hπ : IsInvariant (gig1Ladder H G) π) : π = π (rung 0) • gig1Tilde H G := by
  set P := ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G)
  have hπm : IsInvariantMeasure P π := ⟨inferInstance, hπ⟩
  have hπ0 : π ≠ 0 := IsProbabilityMeasure.ne_zero π
  -- `π₀ = π([0]) H`
  have hmin := theorem_10_4_9 hrec hπm (measurableSet_rung 0) hψ0 (measure_ne_top π _)
  have hL := ae_hitProb_eq_one hrec hπm hπ0 (measurableSet_rung 0) hψ0
  have hπ0H : (π.restrict (rung 0)).map Prod.snd = π (rung 0) • H := by
    ext A hA
    rw [map_snd_restrict_rung_apply _ 0 hA, Measure.smul_apply, smul_eq_mul]
    conv_lhs => rw [← hmin]
    rw [minimalMeasure_apply _ _ _ ((measurableSet_singleton 0).prod hA)]
    simp_rw [tabooPotKernel_rung_zero_of_entrance _ _ H (fun z A hA => gig1_entrance H G z hA)
      _ hA]
    rw [lintegral_mul_const _ (measurable_hitProb P (measurableSet_rung 0)),
      setLIntegral_congr_fun_ae (measurableSet_rung 0) (hL.mono fun x hx _ => hx),
      setLIntegral_const, one_mul]
  refine ext_nat_prod fun k A hA => ?_
  rw [theorem_10_5_3 _ _ hrec hπm hψ0 (measure_ne_top π _) k hA, hπ0H, Measure.smul_apply,
    lintegral_smul_measure, gig1Tilde_apply_prod H G k hA]

/-- **Theorem 10.5.4** (MT p. 252): a recurrent GI/G/1 ladder chain with `ψ([0]) > 0` has an
invariant probability iff `π̃(k × A) = ∫ H(dy) Sᵏ(y, A)` is a finite measure, and the invariant
probability is then `π̃/π̃(X)`. -/
theorem theorem_10_5_4 {ψ : Measure (ℕ × ℝ)}
    (hrec : IsRecurrentChain (ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G)) ψ)
    (hψ0 : 0 < ψ (rung 0)) :
    ((∃ π : Measure (ℕ × ℝ), IsProbabilityMeasure π ∧ IsInvariant (gig1Ladder H G) π) ↔
      gig1Tilde H G univ ≠ ∞) ∧
    ∀ π : Measure (ℕ × ℝ), IsProbabilityMeasure π → IsInvariant (gig1Ladder H G) π →
      π = (gig1Tilde H G univ)⁻¹ • gig1Tilde H G := by
  set P := ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G)
  have key : ∀ π : Measure (ℕ × ℝ), IsProbabilityMeasure π → IsInvariant (gig1Ladder H G) π →
      gig1Tilde H G univ ≠ ∞ ∧ π = (gig1Tilde H G univ)⁻¹ • gig1Tilde H G := by
    intro π hπp hπ
    have he := theorem_10_5_4_eq H G hrec hψ0 hπ
    have hpos : π (rung 0) ≠ 0 := (hπ.isSubinvariant.pos_of_pos hrec.1.2.1
      (IsProbabilityMeasure.ne_zero π) (measurableSet_rung 0) hψ0).ne'
    have hu := congrArg (fun m : Measure (ℕ × ℝ) => m univ) he
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ] at hu
    have hfin : gig1Tilde H G univ ≠ ∞ := by
      intro h; rw [h, ENNReal.mul_top hpos] at hu; exact ENNReal.one_ne_top hu
    refine ⟨hfin, ?_⟩
    have hc : π (rung 0) = (gig1Tilde H G univ)⁻¹ :=
      ENNReal.eq_inv_of_mul_eq_one_left hu.symm
    rw [← hc]
    exact he
  refine ⟨⟨fun ⟨π, hπp, hπ⟩ => (key π hπp hπ).1, fun hfin => ?_⟩,
    fun π hπp hπ => (key π hπp hπ).2⟩
  have hinv := theorem_10_5_4_invariant H G hfin
  have hpos : gig1Tilde H G univ ≠ 0 := by
    intro h
    have h1 : gig1Tilde H G ({0} ×ˢ univ) = 1 := by
      rw [gig1Tilde_apply_prod H G 0 MeasurableSet.univ, pow_zero]
      change ∫⁻ y, Kernel.id y univ ∂H = 1
      simp
    have := measure_mono (μ := gig1Tilde H G) (subset_univ ({0} ×ˢ (univ : Set ℝ)))
    rw [h1, h] at this
    exact absurd this (by simp)
  refine ⟨(gig1Tilde H G univ)⁻¹ • gig1Tilde H G, ⟨?_⟩, hinv.smul _⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]

end MeynTweedie.Epilogue
