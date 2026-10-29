/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.PetiteSets

/-!
# Petite sets for the split chain (MT Proposition 5.5.6 (ii))

Meyn and Tweedie, Proposition 5.5.6 (ii), p. 120: if `Φ` is strongly aperiodic and split on the
small set `A`, then `C₀ ∪ C₁` is petite for the split chain whenever `C` is petite for `Φ`.

* `split_comp_sampledKernel`: (5.10) for sampled chains, `μ* Ǩ_a = (μ K_a)*`.
* `split_dirac_of_notMem`, `sampledKernel_split_false_of_notMem`: off `C` the split of `δₓ` is
  `δ_{x₀}`, so `Ǩ_a(x₀, ·) = K_a(x, ·)*`.
* `proposition_5_5_6_ii_average`: for `x ∈ C`, the split initial law `δₓ*` satisfies
  `δₓ* Ǩ_a ≥ ν_a*`: `C` is petite "on average over the coin".
* `proposition_5_5_6_ii`, the corrected statement: on a countably generated space and for a
  `ψ`-irreducible chain, `(C \ A)₀ ∪ X₁` is petite for the split chain for every minorization
  on `A` and every petite `C`.
* `proposition_5_5_6_ii_counterexample`: the claim as stated is false. For the ladder chain
  `ladderKernel` on `ℕ` (even states `2i` jump to `0` or to `2i + 1` with probability `½` each,
  odd states descend `2k + 3 ↦ 2k + 1 ↦ ⋯ ↦ 1 ↦ 0`), the set `A` of even states is `½δ₀`-small,
  the chain is strongly aperiodic, and `A₀` (hence `A₀ ∪ A₁`) is not petite for the split chain:
  the residual law from `(2i, 0)` is `δ_{2i+1}`, and the split chain then needs `i + 1` steps to
  return to the region where the paths from different `i` meet.

**Corrections.** Proposition 5.5.6 (ii) is false as stated (`proposition_5_5_6_ii_counterexample`).
The book's step "`A₀` is small since `P̌(x₀, X₁) ≥ δ` for `x₀ ∈ A₀`" fails: `P̌(x₀, X₁) =
δ R(x, A)` with `R` the residual kernel (5.6), which can vanish. The averaged and the corrected
statements above hold.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

namespace Minorization

variable {P : Kernel X X}

/-- (5.10) for sampled chains: `μ* Ǩ_a = (μ K_a)*`. -/
theorem split_comp_sampledKernel (M : Minorization P) (a : ℕ → ℝ≥0∞) (μ : Measure X) :
    sampledKernel M.splitKernel a ∘ₘ M.split μ = M.split (sampledKernel P a ∘ₘ μ) := by
  ext s hs
  have hg : Measurable fun y => M.splitK y s := Kernel.measurable_coe _ hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [sampledKernel_apply _ a _ hs]
  rw [lintegral_tsum fun n => ((Kernel.measurable_coe _ hs).const_mul _).aemeasurable]
  simp_rw [lintegral_const_mul _ (Kernel.measurable_coe _ hs)]
  have h1 : ∀ n, ∫⁻ z, (M.splitKernel ^ n) z s ∂M.split μ =
      M.split ((P ^ n : Kernel X X) ∘ₘ μ) s := fun n => by
    rw [← split_comp_splitKernel_pow, Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [h1]
  rw [split, Measure.bind_apply hs M.splitK.aemeasurable,
    Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]
  change _ = ∫⁻ x, ∫⁻ y, M.splitK y s ∂(Measure.sum fun n => a n • (P ^ n) x) ∂μ
  simp_rw [lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_tsum fun n => (hg.lintegral_kernel.const_mul _).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [lintegral_const_mul _ hg.lintegral_kernel, split,
    Measure.bind_apply hs M.splitK.aemeasurable,
    Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]

/-- Off `C`, the split of `δₓ` is `δ_{x₀}`. -/
theorem split_dirac_of_notMem (M : Minorization P) {x : X} (hx : x ∉ M.C) :
    M.split (Measure.dirac x) = Measure.dirac (x, false) := by
  rw [split, Measure.dirac_bind M.splitK.measurable, splitK_apply, splitMeas,
    M.splitProb_of_notMem hx]
  simp

/-- Off `C`, `Ǩ_a(x₀, ·) = K_a(x, ·)*`. -/
theorem sampledKernel_split_false_of_notMem (M : Minorization P) (a : ℕ → ℝ≥0∞) {x : X}
    (hx : x ∉ M.C) :
    sampledKernel M.splitKernel a (x, false) = M.split (sampledKernel P a x) := by
  have h := M.split_comp_sampledKernel a (Measure.dirac x)
  rwa [M.split_dirac_of_notMem hx, Measure.dirac_bind (Kernel.measurable _),
    Measure.dirac_bind (Kernel.measurable _)] at h

/-- `μ*` is nonzero when `μ` is. -/
theorem split_ne_zero (M : Minorization P) {μ : Measure X} (hμ : μ ≠ 0) : M.split μ ≠ 0 := by
  intro h
  apply hμ
  rw [← Measure.measure_univ_eq_zero, ← M.split_univ, h]
  rfl

/-- Proposition 5.5.6 (ii), averaged form: if `C` is `ν_a`-petite for `Φ`, then for every
`x ∈ C` the split initial law satisfies `δₓ* Ǩ_a ≥ ν_a*`. -/
theorem proposition_5_5_6_ii_average (M : Minorization P) {a : ℕ → ℝ≥0∞} {ν : Measure X}
    {C : Set X} (hC : IsPetiteSet P a ν C) {x : X} (hx : x ∈ C) :
    M.split ν ≤ sampledKernel M.splitKernel a ∘ₘ M.split (Measure.dirac x) := by
  rw [M.split_comp_sampledKernel, Measure.dirac_bind (Kernel.measurable _)]
  exact comp_le_comp _ (hC.2.2.2 x hx)

/-- **Proposition 5.5.6 (ii)**, corrected (MT p. 120). On a countably generated space, let `Φ` be
`ψ`-irreducible, `M` a minorization on a set `A` and `C` a petite set. Then `(C \ A)₀ ∪ X₁` is
petite for the split chain. -/
theorem proposition_5_5_6_ii [MeasurableSpace.CountablyGenerated X] (M : Minorization P)
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {C : Set X}
    (hC : IsPetite P C) :
    haveI := M.isMarkovKernel_splitKernel
    IsPetite M.splitKernel ((C \ M.C) ×ˢ {false} ∪ univ ×ˢ {true}) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isProbabilityMeasure_ν
  obtain ⟨a, ν, hpet⟩ := hC
  have hψ' := M.isMaximalIrreducibility_split hψ
  -- the top level outside `A`
  have h0 : IsPetite M.splitKernel ((C \ M.C) ×ˢ {false}) := by
    refine ⟨a, M.split ν, (hpet.1.diff M.measurableSet_C).prod (measurableSet_singleton _),
      hpet.2.1, M.split_ne_zero hpet.2.2.1, fun z hz => ?_⟩
    obtain ⟨x, b⟩ := z
    obtain ⟨⟨hxC, hxA⟩, hb⟩ := hz
    have hb' : b = false := hb
    subst hb'
    rw [M.sampledKernel_split_false_of_notMem a hxA]
    exact comp_le_comp _ (hpet.2.2.2 x hxC)
  -- the bottom level is an atom
  have h1 : IsPetite M.splitKernel (univ ×ˢ ({true} : Set Bool)) := by
    obtain ⟨hm, -, hν⟩ := M.isAtom_bottom
    exact ⟨_, _, proposition_5_5_3 (isSmallSet_of_atom M.splitKernel
      (MeasurableSet.univ.prod (measurableSet_singleton true)) (fun z hz => by
        obtain ⟨x, b⟩ := z
        obtain ⟨-, hb⟩ := hz
        have hb' : b = true := hb
        subst hb'
        rw [splitKernel_apply_true]) (M.split_ne_zero
          (IsProbabilityMeasure.ne_zero M.ν)))⟩
  exact proposition_5_5_5_ii M.splitKernel hψ' h0 h1

end Minorization

/-! ### The counterexample -/

/-- The transition law of the ladder chain on `ℕ`: from an even state `n = 2i`, jump to `0` or to
`2i + 1` with probability `½` each; from an odd state `n`, move to `n − 2` (and from `1` to
`0`). -/
noncomputable def ladderMeas (n : ℕ) : Measure ℕ :=
  if Even n then (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • Measure.dirac (n + 1)
  else Measure.dirac (n - 2)

/-- The ladder chain. -/
noncomputable def ladderKernel : Kernel ℕ ℕ := ⟨ladderMeas, measurable_of_countable _⟩

/-- The ladder chain is a transition kernel. -/
theorem isMarkovKernel_ladderKernel : IsMarkovKernel ladderKernel := by
  refine ⟨fun n => ⟨?_⟩⟩
  change ladderMeas n univ = 1
  unfold ladderMeas
  split_ifs
  · simp [ENNReal.inv_two_add_inv_two]
  · simp

/-- The minorization `P(x, ·) ≥ ½ δ₀` on the even states. -/
noncomputable def ladderMinorization : Minorization ladderKernel where
  C := {n | Even n}
  δ := 2⁻¹
  ν := Measure.dirac 0
  measurableSet_C := measurableSet_of_countable _
  δ_pos := by simp
  δ_lt_one := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  isProbabilityMeasure_ν := inferInstance
  le x hx := by
    change _ ≤ ladderMeas x
    have hx' : Even x := hx
    simp only [ladderMeas, hx', ite_true]
    exact Measure.le_add_right le_rfl

/-- The ladder chain is strongly aperiodic: the even states are `½δ₀`-small. -/
theorem ladder_isStronglyAperiodic : IsStronglyAperiodic ladderKernel :=
  ⟨(2⁻¹ : ℝ≥0∞) • Measure.dirac 0, {n | Even n}, ⟨measurableSet_of_countable _, one_pos,
    smul_measure_ne_zero (by simp) (by simp), fun x hx => by
      rw [pow_one]; exact ladderMinorization.le x hx⟩, by simp⟩

/-- The residual law of the ladder chain at an even state `x` is `δ_{x+1}`. -/
theorem ladder_resid_even {x : ℕ} (hx : Even x) :
    ladderMinorization.resid x = Measure.dirac (x + 1) := by
  ext s hs
  rw [Minorization.resid_apply, Minorization.residMeas_apply_of_mem _ hx hs]
  change (1 - 2⁻¹)⁻¹ * (ladderMeas x s - 2⁻¹ * Measure.dirac 0 s) = _
  simp only [ladderMeas, hx, ite_true]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, ENNReal.add_sub_cancel_left (ENNReal.mul_ne_top (by simp)
      (measure_ne_top _ _)), ENNReal.one_sub_inv_two, inv_inv, ← mul_assoc,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- The split of `δ_y` at an odd state `y` is `δ_{(y, 0)}`. -/
theorem ladder_split_dirac_odd {y : ℕ} (hy : ¬ Even y) :
    ladderMinorization.split (Measure.dirac y) = Measure.dirac (y, false) :=
  ladderMinorization.split_dirac_of_notMem hy

/-- From `(2i, 0)` the split chain moves to `(2i + 1, 0)`. -/
theorem ladder_splitKernel_even (i : ℕ) :
    ladderMinorization.splitKernel (2 * i, false) = Measure.dirac (2 * i + 1, false) := by
  rw [Minorization.splitKernel_apply, Minorization.baseK_apply_false,
    ladder_resid_even (even_two_mul i), ladder_split_dirac_odd (by simp)]

/-- From `(2k + 3, 0)` the split chain moves to `(2k + 1, 0)`. -/
theorem ladder_splitKernel_odd (k : ℕ) :
    ladderMinorization.splitKernel (2 * k + 3, false) = Measure.dirac (2 * k + 1, false) := by
  have hodd : ¬ Even (2 * k + 3) := by
    rw [Nat.not_even_iff_odd]; exact ⟨k + 1, by ring⟩
  rw [ladderMinorization.splitKernel_apply_false_of_notMem hodd]
  change ladderMinorization.split (ladderMeas (2 * k + 3)) = _
  simp only [ladderMeas, hodd, ite_false]
  rw [show 2 * k + 3 - 2 = 2 * k + 1 by omega,
    ladder_split_dirac_odd (by rw [Nat.not_even_iff_odd]; exact ⟨k, rfl⟩)]

/-- From `(2i, 0)`, after `n + 1 ≤ i + 1` steps the split chain is at `(2(i − n) + 1, 0)`. -/
theorem ladder_splitKernel_pow (i n : ℕ) (hn : n ≤ i) :
    (ladderMinorization.splitKernel ^ (n + 1)) (2 * i, false) =
      Measure.dirac (2 * (i - n) + 1, false) := by
  induction n with
  | zero => rw [zero_add, pow_one, ladder_splitKernel_even, Nat.sub_zero]
  | succ n ih =>
    rw [pow_succ']
    change (ladderMinorization.splitKernel ∘ₖ (ladderMinorization.splitKernel ^ (n + 1)))
      (2 * i, false) = _
    rw [Kernel.comp_apply, ih (by omega), Measure.dirac_bind (Kernel.measurable _),
      show 2 * (i - n) + 1 = 2 * (i - (n + 1)) + 3 by omega, ladder_splitKernel_odd]

/-- **Correction to Proposition 5.5.6 (ii)** (MT p. 120). For the strongly aperiodic ladder chain
split on the `½δ₀`-small set `A` of even states, `A` is petite for `Φ` but `A₀ ∪ A₁` is not
petite for the split chain. -/
theorem proposition_5_5_6_ii_counterexample :
    haveI := isMarkovKernel_ladderKernel
    IsPetite ladderKernel {n | Even n} ∧
      ¬ IsPetite ladderMinorization.splitKernel ({n | Even n} ×ˢ univ) := by
  have := isMarkovKernel_ladderKernel
  refine ⟨⟨_, _, proposition_5_5_3 (m := 1) (ν := (2⁻¹ : ℝ≥0∞) • Measure.dirac 0)
    ⟨measurableSet_of_countable _, one_pos, smul_measure_ne_zero (by simp) (by simp),
      fun x hx => by rw [pow_one]; exact ladderMinorization.le x hx⟩⟩, ?_⟩
  set Q := ladderMinorization.splitKernel with hQ
  have hM : IsMarkovKernel Q := ladderMinorization.isMarkovKernel_splitKernel
  rintro ⟨a, ν', -, ha, hν, hle⟩
  -- a point charged by the minorizing measure
  have hpos : 0 < ν' univ := pos_iff_ne_zero.2 fun h => hν (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨w, -, hw⟩ := exists_singleton_pos_of_pos ν' hpos
  have hK := isMarkovKernel_sampledKernel Q ha
  have hct : ν' {w} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((hle (0, false) ⟨Even.zero, mem_univ _⟩ {w}).trans prob_le_one)
  have hc2 : 0 < ν' {w} / 2 := ENNReal.div_pos hw.ne' (by simp)
  obtain ⟨T, hT⟩ := exists_tail_le ha hc2
  -- the state `(2i, 0)`, `i = T + w₁`, has not reached `w` before time `T`
  set i := T + w.1 with hi
  have h1 := hle (2 * i, false) ⟨even_two_mul i, mem_univ _⟩ {w}
  rw [sampledKernel_apply _ a _ (measurableSet_singleton w)] at h1
  have hsplit : ∑' n, a n * (Q ^ n) (2 * i, false) {w} =
      ∑ n ∈ Finset.range T, a n * (Q ^ n) (2 * i, false) {w} +
        ∑' k, a (k + T) * (Q ^ (k + T)) (2 * i, false) {w} :=
    (Summable.sum_add_tsum_nat_add' (f := fun n => a n * (Q ^ n) (2 * i, false) {w}) (k := T)
      ENNReal.summable).symm
  have hhead : ∑ n ∈ Finset.range T, a n * (Q ^ n) (2 * i, false) {w} = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_range] at hn
    rcases n with _ | m
    · rw [pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton w),
        indicator_of_notMem, mul_zero]
      intro h
      have := congrArg Prod.fst (mem_singleton_iff.1 h)
      simp only at this
      omega
    · rw [hQ, ladder_splitKernel_pow i m (by omega),
        Measure.dirac_apply' _ (measurableSet_singleton w), indicator_of_notMem, mul_zero]
      intro h
      have := congrArg Prod.fst (mem_singleton_iff.1 h)
      simp only at this
      omega
  have htail : ∑' k, a (k + T) * (Q ^ (k + T)) (2 * i, false) {w} ≤ ν' {w} / 2 := by
    refine le_trans (ENNReal.tsum_le_tsum fun k => ?_) hT
    have := isMarkovKernel_pow Q (k + T)
    exact mul_le_of_le_one_right' prob_le_one
  rw [hsplit, hhead, zero_add] at h1
  exact absurd (h1.trans htail) (not_le.2 (ENNReal.half_lt_self hw.ne' hct))

end MeynTweedie.VUniformErgodicity
