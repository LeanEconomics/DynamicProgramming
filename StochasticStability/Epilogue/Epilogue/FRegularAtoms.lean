/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.FRegularityDrift
import Epilogue.SumsNoAtom

/-!
# `f`-properties of chains with atoms (MT §14.1)

Meyn and Tweedie, §14.1, pp. 338–342. `α` is an atom with a point `a ∈ α`, `T_j = _αP^{j+1}(a, ·)`
(`tabooKernel P hα j a`) and `t_f(j + 1) = T_j(f)`; `a_λ` is the entry law of `λ` and
`u(n) = Pⁿ(a, α)` the renewal sequence of the atom.

**The regenerative decomposition in `f`-norm** (13.47), (13.48), (14.6), for measurable
`f : X → [0, ∞]` with no boundedness.
* `add_eq_add_of_measureReal_sub_eq`: a real decomposition `μ(B) − ν(B) = σ₁(B) − σ₂(B)` is an
  identity of measures `μ + σ₂ = ν + σ₁`.
* `fNorm_comp_pow_succ_le` ((14.6)): if `π = π(α) μ°_α`,
  `‖λPⁿ⁺¹ − π‖_f ≤ λ_αPⁿ⁺¹(f) + Σ_{k ≤ n} |a_λ ∗ u(k) − π(α)| T_{n−k}(f) + π(α) Σ_{j > n} T_j(f)`.
* `fNorm_comp_pow_succ_le_atom` ((14.14)–(14.15)):
  `‖λPⁿ⁺¹ − Pⁿ⁺¹(a, ·)‖_f ≤ λ_αPⁿ⁺¹(f) + Σ_{k ≤ n} |a_λ ∗ u(k) − u(k)| T_{n−k}(f)`.
* `tsum_lintegral_tabooSeq` ((14.9)): `Σₙ λ_αPⁿ⁺¹(f) = E_λ[Σ_{k=1}^{τ_α} f(Φ_k)]`;
  `lintegral_eq_atom` ((14.7)): `π(f) = π(α) E_a[Σ_{k=1}^{τ_α} f(Φ_k)]`.

**Convergence and summability from an atom.**
* `tendsto_fNorm_of_ergodic_atom`: if `u(n) → π(α)`, `π(f) < ∞`, the initial law `λ` reaches
  `α` almost surely and `E_λ[Σ_{k=1}^{τ_α} f(Φ_k)] < ∞`, then `‖λPⁿ − π‖_f → 0`: the three terms of
  (14.6) tend to `0`.
* `tsum_fNorm_comp_le_atom`: `Σₙ ‖λPⁿ⁺¹ − Pⁿ⁺¹(a, ·)‖_f ≤ E_λ[Σ_{k=1}^{τ_α} f] +
  E_λ[τ_α] Var(u) E_a[Σ_{k=1}^{τ_α} f]` (the proof of Theorem 14.1.3 (iii)).

**Results.**
* **Proposition 14.1.2** (p. 340): for a positive chain with an accessible atom and `π(f) < ∞`,
  (i) `proposition_14_1_2_i`: `C` is `f`-regular iff `G_α(·, f)` is bounded on `C`
  (`isFRegularState_iff_atom`: `x` is `f`-regular iff `G_α(x, f) < ∞`);
  (ii) `proposition_14_1_2_ii`: the sets `S_f(n) = {G_α(·, f) ≤ n}` are `f`-regular, increasing,
  and their union is full and absorbing.
* **Theorem 14.1.3** (p. 341), for a positive Harris aperiodic chain with an accessible atom:
  (i) `theorem_14_1_3_i`, if `π(f) < ∞` the `f`-regular states form a full absorbing set from
  which `‖Pᵏ(x, ·) − π‖_f → 0`; (ii) `theorem_14_1_3_ii`, an `f`-regular chain is `f`-ergodic;
  (iii) `theorem_14_1_3_iii`, the bound (14.13).
* **Theorem 14.1.4** (`theorem_14_1_4`, p. 342): on a countable space, for an irreducible positive
  Harris aperiodic chain with `π(f) < ∞`, `‖Pᵏ(x, ·) − π‖_f → 0` and
  `Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f < ∞` for all `x`, `y`.
* `IsFErgodic` (p. 337): `f ≥ 1`, positive Harris with invariant probability `π`, `π(f) < ∞`, and
  `‖Pᵏ(x, ·) − π‖_f → 0` for every `x`.

**Hypotheses.** `f` is measurable, finite valued (the book's `f : X → [1, ∞)`; for
Proposition 14.1.2 it suffices that `f` is finite at one point of `α`), and `f ≥ 1` where the book
uses it. The state space is countably generated (Theorem 14.2.3 is used for the
`f`-regularity of the sublevel sets of `G_α`). In Theorem 14.1.4 the maximal irreducibility
measure is assumed to charge every state.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Measure identities from set identities -/

/-- A decomposition `μ(B) − ν(B) = σ₁(B) − σ₂(B)` of finite measures, for every measurable `B`,
is the identity of measures `μ + σ₂ = ν + σ₁`. -/
theorem add_eq_add_of_measureReal_sub_eq {μ ν σ₁ σ₂ : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    (h : ∀ B, MeasurableSet B → μ.real B - ν.real B = σ₁.real B - σ₂.real B) :
    μ + σ₂ = ν + σ₁ := by
  ext B hB
  rw [Measure.add_apply, Measure.add_apply, ← ENNReal.toReal_eq_toReal_iff'
    (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
    (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have := h B hB
  simp only [measureReal_def] at this
  linarith

/-- `ofReal x + ofReal (−x) = ofReal |x|`. -/
theorem ofReal_add_ofReal_neg (x : ℝ) :
    ENNReal.ofReal x + ENNReal.ofReal (-x) = ENNReal.ofReal |x| := by
  rcases le_total x 0 with hx | hx
  · rw [ENNReal.ofReal_of_nonpos hx, zero_add, abs_of_nonpos hx]
  · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 hx), add_zero, abs_of_nonneg hx]

/-! ### The regenerative decomposition in `f`-norm -/

/-- **The regenerative decomposition (14.6) in `f`-norm.** If `π = π(α) μ°_α`, then for every
measurable `f ≥ 0`, `‖λPⁿ⁺¹ − π‖_f ≤ λ_αPⁿ⁺¹(f) + Σ_{k ≤ n} |a_λ ∗ u(k) − π(α)| T_{n−k}(f) +
π(α) Σ_{i} T_{i+n+1}(f)`. -/
theorem fNorm_comp_pow_succ_le {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα.1 a) (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ)
    (f : X → ℝ≥0∞) :
    fNorm f ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) π ≤ ∫⁻ y, f y ∂tabooSeq P hα.1 μ n +
      ∑ k ∈ range (n + 1), ENNReal.ofReal
        |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - (π α).toReal| *
          ∫⁻ y, f y ∂tabooKernel P hα.1 (n - k) a +
      π α * ∑' i, ∫⁻ y, f y ∂tabooKernel P hα.1 (i + n + 1) a := by
  have := isMarkovKernel_pow P (n + 1)
  have hm := meanReturnTime_ne_top_of_rep P hα.1 a hπ
  set c := (π α).toReal with hc
  set au := realConv (entryLaw P hα.1 μ) (atomRenewal P α a) with hau
  set T : ℕ → Measure X := fun k => tabooKernel P hα.1 k a with hT
  have hTfin : ∀ k B, T k B ≠ ∞ := fun k B =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (tabooKernel_apply_le_one P hα.1 k a B)
  have hSfin : ∀ B, ∑' i, T (i + n + 1) B ≠ ∞ := fun B => by
    refine ne_top_of_le_ne_top (b := meanReturnTime P α a) hm ?_
    rw [meanReturnTime_eq_tabooPotKernel P hα.1, tabooPotKernel, Kernel.sum_apply,
      Measure.sum_apply _ MeasurableSet.univ]
    calc ∑' i, T (i + n + 1) B ≤ ∑' i, T (i + n + 1) univ :=
          ENNReal.tsum_le_tsum fun i => measure_mono (subset_univ B)
      _ ≤ ∑' k, T k univ := ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun i => i + n + 1) (fun i j hij => by simpa using hij) (fun k => T k univ)
  have hE : ∀ B, tabooSeq P hα.1 μ n B ≠ ∞ := fun B =>
    ne_top_of_le_ne_top (measure_ne_top μ univ) (tabooSeq_apply_le P hα.1 μ n B)
  set σ₁ : Measure X := tabooSeq P hα.1 μ n +
    ∑ k ∈ range (n + 1), ENNReal.ofReal (au k - c) • T (n - k) with hσ₁
  set σ₂ : Measure X := ∑ k ∈ range (n + 1), ENNReal.ofReal (c - au k) • T (n - k) +
    π α • Measure.sum (fun i => T (i + n + 1)) with hσ₂
  have hσ₁B : ∀ B, σ₁ B = tabooSeq P hα.1 μ n B +
      ∑ k ∈ range (n + 1), ENNReal.ofReal (au k - c) * T (n - k) B := fun B => by
    rw [hσ₁, Measure.add_apply, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
  have hσ₂B : ∀ B, MeasurableSet B → σ₂ B =
      ∑ k ∈ range (n + 1), ENNReal.ofReal (c - au k) * T (n - k) B +
        π α * ∑' i, T (i + n + 1) B := fun B hB => by
    rw [hσ₂, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.sum_apply _ hB]
    simp only [Measure.smul_apply, smul_eq_mul]
  have hσ₁fin : ∀ B, σ₁ B ≠ ∞ := fun B => by
    rw [hσ₁B]
    exact ENNReal.add_ne_top.2 ⟨hE B, ENNReal.sum_ne_top.2 fun k _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)⟩
  have hσ₂fin : ∀ B, MeasurableSet B → σ₂ B ≠ ∞ := fun B hB => by
    rw [hσ₂B B hB]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun k _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _),
      ENNReal.mul_ne_top (measure_ne_top π α) (hSfin B)⟩
  have : IsFiniteMeasure σ₁ := ⟨lt_top_iff_ne_top.2 (hσ₁fin univ)⟩
  have : IsFiniteMeasure σ₂ := ⟨lt_top_iff_ne_top.2 (hσ₂fin univ MeasurableSet.univ)⟩
  have hσ₁R : ∀ B, σ₁.real B = (tabooSeq P hα.1 μ n B).toReal +
      ∑ k ∈ range (n + 1), (ENNReal.ofReal (au k - c)).toReal * (T (n - k) B).toReal :=
    fun B => by
      rw [measureReal_def, hσ₁B, ENNReal.toReal_add (hE B) (ENNReal.sum_ne_top.2 fun k _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)), ENNReal.toReal_sum fun k _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)]
      simp_rw [ENNReal.toReal_mul]
  have hσ₂R : ∀ B, MeasurableSet B → σ₂.real B =
      ∑ k ∈ range (n + 1), (ENNReal.ofReal (c - au k)).toReal * (T (n - k) B).toReal +
        c * ∑' i, (T (i + n + 1) B).toReal := fun B hB => by
    rw [measureReal_def, hσ₂B B hB, ENNReal.toReal_add (ENNReal.sum_ne_top.2 fun k _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _))
        (ENNReal.mul_ne_top (measure_ne_top π α) (hSfin B)), ENNReal.toReal_sum fun k _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _), ENNReal.toReal_mul,
      ENNReal.tsum_toReal_eq fun i => hTfin _ _]
    simp_rw [ENNReal.toReal_mul]
    rfl
  have hind : ∀ B, MeasurableSet B → ∀ y, B.indicator (1 : X → ℝ≥0∞) y ≤ 1 := fun B _ y => by
    by_cases hy : y ∈ B <;> simp [hy]
  have heq : (P ^ (n + 1) : Kernel X X) ∘ₘ μ + σ₂ = π + σ₁ := by
    refine add_eq_add_of_measureReal_sub_eq fun B hB => ?_
    have hid := regenerative_identity_48 hα ha hπ μ ENNReal.one_ne_top (hind B hB) n
    simp only [lintegral_indicator_one hB] at hid
    rw [measureReal_def, measureReal_def, hid, hσ₁R, hσ₂R B hB,
      realConv_lastExitSeq_succ]
    simp only [lintegral_indicator_one hB]
    have htail : ∀ i, lastExitSeq P hα.1 a (B.indicator 1) (i + n + 2) =
        (T (i + n + 1) B).toReal :=
      fun i => by rw [show i + n + 2 = (i + n + 1) + 1 by ring, lastExitSeq_indicator_succ _ _ _ hB]
    simp_rw [htail]
    have hk : ∀ k ∈ range (n + 1), (au k - c) * (T (n - k) B).toReal =
        (ENNReal.ofReal (au k - c)).toReal * (T (n - k) B).toReal -
          (ENNReal.ofReal (c - au k)).toReal * (T (n - k) B).toReal := fun k _ => by
      rw [← sub_mul, show c - au k = -(au k - c) by ring, toReal_ofReal_sub_ofReal_neg]
    rw [Finset.sum_congr rfl hk, Finset.sum_sub_distrib]
    ring
  refine (fNorm_le_of_add_eq heq).trans (le_of_eq ?_)
  rw [hσ₁, hσ₂, lintegral_add_measure, lintegral_finsetSum_measure, lintegral_add_measure,
    lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  have hk : ∀ k ∈ range (n + 1), ENNReal.ofReal (au k - c) * ∫⁻ y, f y ∂T (n - k) +
      ENNReal.ofReal (c - au k) * ∫⁻ y, f y ∂T (n - k) =
      ENNReal.ofReal |au k - c| * ∫⁻ y, f y ∂T (n - k) := fun k _ => by
    rw [← add_mul, show c - au k = -(au k - c) by ring, ofReal_add_ofReal_neg]
  rw [← Finset.sum_congr rfl hk, Finset.sum_add_distrib]
  simp only [hT]
  ring

/-- **The regenerative decomposition (13.47) in `f`-norm**, (14.14)–(14.15):
`‖λPⁿ⁺¹ − Pⁿ⁺¹(a, ·)‖_f ≤ λ_αPⁿ⁺¹(f) + Σ_{k ≤ n} |a_λ ∗ u(k) − u(k)| T_{n−k}(f)`. -/
theorem fNorm_comp_pow_succ_le_atom {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ)
    (f : X → ℝ≥0∞) :
    fNorm f ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) ((P ^ (n + 1) : Kernel X X) a) ≤
      ∫⁻ y, f y ∂tabooSeq P hα.1 μ n +
        ∑ k ∈ range (n + 1), ENNReal.ofReal
          |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - atomRenewal P α a k| *
            ∫⁻ y, f y ∂tabooKernel P hα.1 (n - k) a := by
  have := isMarkovKernel_pow P (n + 1)
  set g := fun k => realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - atomRenewal P α a k
  set T : ℕ → Measure X := fun k => tabooKernel P hα.1 k a
  have hTfin : ∀ k B, T k B ≠ ∞ := fun k B =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (tabooKernel_apply_le_one P hα.1 k a B)
  have hE : ∀ B, tabooSeq P hα.1 μ n B ≠ ∞ := fun B =>
    ne_top_of_le_ne_top (measure_ne_top μ univ) (tabooSeq_apply_le P hα.1 μ n B)
  set σ₁ : Measure X := tabooSeq P hα.1 μ n +
    ∑ k ∈ range (n + 1), ENNReal.ofReal (g k) • T (n - k) with hσ₁
  set σ₂ : Measure X := ∑ k ∈ range (n + 1), ENNReal.ofReal (-g k) • T (n - k) with hσ₂
  have hσ₁B : ∀ B, σ₁ B = tabooSeq P hα.1 μ n B +
      ∑ k ∈ range (n + 1), ENNReal.ofReal (g k) * T (n - k) B := fun B => by
    simp only [σ₁, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  have hσ₂B : ∀ B, σ₂ B = ∑ k ∈ range (n + 1), ENNReal.ofReal (-g k) * T (n - k) B := fun B => by
    simp only [σ₂, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  have hsum1 : ∀ B, ∑ k ∈ range (n + 1), ENNReal.ofReal (g k) * T (n - k) B ≠ ∞ := fun B =>
    ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)
  have hsum2 : ∀ B, ∑ k ∈ range (n + 1), ENNReal.ofReal (-g k) * T (n - k) B ≠ ∞ := fun B =>
    ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)
  have : IsFiniteMeasure σ₁ := ⟨by
    rw [hσ₁B]; exact lt_top_iff_ne_top.2 (ENNReal.add_ne_top.2 ⟨hE _, hsum1 _⟩)⟩
  have : IsFiniteMeasure σ₂ := ⟨by rw [hσ₂B]; exact lt_top_iff_ne_top.2 (hsum2 _)⟩
  have hσ₁R : ∀ B, σ₁.real B = (tabooSeq P hα.1 μ n B).toReal +
      ∑ k ∈ range (n + 1), (ENNReal.ofReal (g k)).toReal * (T (n - k) B).toReal := fun B => by
    rw [measureReal_def, hσ₁B, ENNReal.toReal_add (hE B) (hsum1 B), ENNReal.toReal_sum fun k _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)]
    simp_rw [ENNReal.toReal_mul]
  have hσ₂R : ∀ B, σ₂.real B =
      ∑ k ∈ range (n + 1), (ENNReal.ofReal (-g k)).toReal * (T (n - k) B).toReal := fun B => by
    rw [measureReal_def, hσ₂B, ENNReal.toReal_sum fun k _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)]
    simp_rw [ENNReal.toReal_mul]
  have hind : ∀ B, MeasurableSet B → ∀ y, B.indicator (1 : X → ℝ≥0∞) y ≤ 1 := fun B _ y => by
    by_cases hy : y ∈ B <;> simp [hy]
  have heq : (P ^ (n + 1) : Kernel X X) ∘ₘ μ + σ₂ = (P ^ (n + 1) : Kernel X X) a + σ₁ := by
    refine add_eq_add_of_measureReal_sub_eq fun B hB => ?_
    have h1 := lintegral_comp_pow_succ_atom_toReal hα ha μ ENNReal.one_ne_top (hind B hB) n
    have h2 := lintegral_pow_succ_atom_toReal hα ha ENNReal.one_ne_top (hind B hB) n
    simp only [lintegral_indicator_one hB] at h1 h2
    rw [measureReal_def, measureReal_def, h1, h2, hσ₁R, hσ₂R, add_sub_assoc,
      ← Pi.sub_apply (realConv _ _), ← realConv_sub_left, realConv_lastExitSeq_succ]
    simp only [lintegral_indicator_one hB]
    have hk : ∀ k ∈ range (n + 1), (realConv (entryLaw P hα.1 μ) (atomRenewal P α a) -
        atomRenewal P α a) k * (T (n - k) B).toReal =
        (ENNReal.ofReal (g k)).toReal * (T (n - k) B).toReal -
          (ENNReal.ofReal (-g k)).toReal * (T (n - k) B).toReal := fun k _ => by
      rw [← sub_mul, toReal_ofReal_sub_ofReal_neg]
      rfl
    rw [Finset.sum_congr rfl hk, Finset.sum_sub_distrib]
    ring
  refine (fNorm_le_of_add_eq heq).trans (le_of_eq ?_)
  rw [hσ₁, hσ₂, lintegral_add_measure, lintegral_finsetSum_measure, lintegral_finsetSum_measure,
    add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← add_mul,
    ofReal_add_ofReal_neg]

/-! ### Sums of the taboo terms -/

/-- `Σ_j T_j(f) = U_α(a, f)`: the taboo kernels sum to the taboo potential. -/
theorem tsum_lintegral_tabooKernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    ∑' j, ∫⁻ y, f y ∂tabooKernel P hA j x = tabooPotFn P A f x := by
  rw [← lintegral_tabooPotKernel P hA hf x, tabooPotKernel, Kernel.sum_apply,
    lintegral_sum_measure]

/-- **(14.9)**: `Σₙ λ_αPⁿ⁺¹(f) = ∫ λ(dx) U_α(x, f) = E_λ[Σ_{k=1}^{τ_α} f(Φ_k)]`. -/
theorem tsum_lintegral_tabooSeq (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {f : X → ℝ≥0∞} (hf : Measurable f) (μ : Measure X) :
    ∑' n, ∫⁻ y, f y ∂tabooSeq P hA μ n = ∫⁻ x, tabooPotFn P A f x ∂μ := by
  simp_rw [tabooSeq, ← lintegral_comp_kernel _ μ hf]
  rw [← lintegral_tsum fun n => (hf.lintegral_kernel).aemeasurable]
  exact lintegral_congr fun x => tsum_lintegral_tabooKernel P hA hf x

/-- **(14.7)**: if `π = π(α) μ°_α` then `π(f) = π(α) U_α(a, f)`. -/
theorem lintegral_eq_atom (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) {π : Measure X} (hπ : π = π α • atomMeasure P hα a)
    {f : X → ℝ≥0∞} (hf : Measurable f) : ∫⁻ y, f y ∂π = π α * tabooPotFn P α f a := by
  conv_lhs => rw [hπ]
  rw [lintegral_smul_measure, smul_eq_mul, atomMeasure, lintegral_tabooPotKernel P hα hf]

/-- On an atom, `U_α(y, f)` does not depend on `y ∈ α`. -/
theorem IsAtom.tabooPotFn_eq {P : Kernel X X} [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {f : X → ℝ≥0∞} (hf : Measurable f) {x y : X} (hx : x ∈ α) (hy : y ∈ α) :
    tabooPotFn P α f x = tabooPotFn P α f y := by
  rw [← lintegral_tabooPotKernel P hα.1 hf, ← lintegral_tabooPotKernel P hα.1 hf,
    hα.tabooPotKernel_eq hx hy]

/-- If `π = π(α) μ°_α` and `π(f) < ∞`, then `U_α(a, f) < ∞`. -/
theorem tabooPotFn_ne_top_of_rep (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα a) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hπf : ∫⁻ y, f y ∂π ≠ ∞) : tabooPotFn P α f a ≠ ∞ := by
  intro htop
  have h := lintegral_eq_atom P hα a hπ hf
  rw [htop, ENNReal.mul_top (measure_atom_ne_zero_of_rep P hα a hπ)] at h
  exact hπf h

/-! ### Convergence from an atom -/

/-- **Convergence in `f`-norm from an ergodic atom** (the proof of Theorem 14.1.3 (i)). If
`π = π(α) μ°_α`, `u(n) → π(α)`, `π(f) < ∞`, and the initial law `λ` reaches `α` almost surely
with `E_λ[Σ_{k=1}^{τ_α} f(Φ_k)] < ∞`, then `‖λPⁿ − π‖_f → 0`. -/
theorem tendsto_fNorm_of_ergodic_atom {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα.1 a)
    (herg : Tendsto (atomRenewal P α a) atTop (𝓝 (π α).toReal)) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hπf : ∫⁻ y, f y ∂π ≠ ∞) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∫⁻ x, hitProb P α x ∂μ = 1) (hμf : ∫⁻ x, tabooPotFn P α f x ∂μ ≠ ∞) :
    Tendsto (fun n => fNorm f ((P ^ n : Kernel X X) ∘ₘ μ) π) atTop (𝓝 0) := by
  set c := (π α).toReal
  set t : ℕ → ℝ≥0∞ := fun j => ∫⁻ y, f y ∂tabooKernel P hα.1 j a with ht
  have hUa := tabooPotFn_ne_top_of_rep P hα.1 a hπ hf hπf
  have hts : ∑' j, t j ≠ ∞ := by rw [ht, tsum_lintegral_tabooKernel P hα.1 hf a]; exact hUa
  have htfin : ∀ j, t j ≠ ∞ := fun j => ne_top_of_le_ne_top hts (ENNReal.le_tsum j)
  -- (A): `λ_αPⁿ⁺¹(f) → 0`
  have hA : Tendsto (fun n => ∫⁻ y, f y ∂tabooSeq P hα.1 μ n) atTop (𝓝 0) := by
    refine ENNReal.tendsto_atTop_zero_of_tsum_ne_top ?_
    rw [tsum_lintegral_tabooSeq P hα.1 hf μ]; exact hμf
  -- (B): `|a_λ ∗ u − π(α)| ∗ t_f → 0`
  have hE := hasSum_entryLaw P hα.1 μ
  rw [hμ, ENNReal.toReal_one] at hE
  have hau : Tendsto (realConv (entryLaw P hα.1 μ) (atomRenewal P α a)) atTop (𝓝 c) := by
    have := lemma_D_7_1 (entryLaw_nonneg P hα.1 μ) hE.summable herg
    rwa [hE.tsum_eq, mul_one] at this
  set w := fun k => |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - c| with hw
  have hw0 : Tendsto w atTop (𝓝 0) := by
    have := (hau.sub_const c).abs
    simpa using this
  set tR : ℕ → ℝ := fun j => (t j).toReal with htR
  have htRs : Summable tR := ENNReal.summable_toReal hts
  have hBR : Tendsto (realConv tR w) atTop (𝓝 0) := by
    have := lemma_D_7_1 (fun j => ENNReal.toReal_nonneg) htRs hw0
    simpa using this
  have hB : Tendsto (fun n => ∑ k ∈ range (n + 1), ENNReal.ofReal (w k) * t (n - k)) atTop
      (𝓝 0) := by
    have heq : ∀ n, ∑ k ∈ range (n + 1), ENNReal.ofReal (w k) * t (n - k) =
        ENNReal.ofReal (realConv tR w n) := fun n => by
      rw [realConv_comm, realConv_eq_sum_range, ENNReal.ofReal_sum_of_nonneg fun k _ =>
        mul_nonneg (abs_nonneg _) ENNReal.toReal_nonneg]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_toReal (htfin _)]
    simp_rw [heq]
    have := ENNReal.tendsto_ofReal hBR
    rwa [ENNReal.ofReal_zero] at this
  -- (C): the tail `π(α) Σ_{i} t_f(i + n + 1) → 0`
  have hC : Tendsto (fun n => π α * ∑' i, t (i + n + 1)) atTop (𝓝 0) := by
    have h1 := (ENNReal.tendsto_sum_nat_add t hts).comp (tendsto_add_atTop_nat 1)
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr (measure_ne_top π α))
    rw [mul_zero] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, add_assoc]
  have hbound := (hA.add hB).add hC
  simp only [add_zero] at hbound
  rw [← tendsto_add_atTop_iff_nat 1]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound (fun _ => zero_le)
    fun n => fNorm_comp_pow_succ_le hα ha hπ μ n f

/-! ### Two facts about sums in `[0, ∞]` -/

/-- `Σₙ ∫ gₙ ≤ ∫ Σₙ gₙ`, without measurability (superadditivity of the lower integral). -/
theorem tsum_lintegral_le_lintegral_tsum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : ℕ → Ω → ℝ≥0∞) : ∑' n, ∫⁻ ω, g n ω ∂μ ≤ ∫⁻ ω, ∑' n, g n ω ∂μ := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  have h : ∀ N, ∑ n ∈ range N, ∫⁻ ω, g n ω ∂μ ≤ ∫⁻ ω, ∑ n ∈ range N, g n ω ∂μ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      simp_rw [Finset.sum_range_succ]
      exact (add_le_add ih le_rfl).trans (le_lintegral_add (fun ω => ∑ n ∈ range N, g n ω)
        (g N))
  exact (h N).trans (lintegral_mono fun ω => ENNReal.sum_le_tsum _)

/-- The Cauchy product in `[0, ∞]`: `Σₙ Σ_{k ≤ n} a(k) b(n − k) = (Σ a)(Σ b)`. -/
theorem tsum_sum_range_mul (a b : ℕ → ℝ≥0∞) :
    ∑' n, ∑ k ∈ range (n + 1), a k * b (n - k) = (∑' k, a k) * ∑' j, b j := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j)]
  rw [tsum_sum_antidiagonal (fun q => a q.1 * b q.2), ← ENNReal.tsum_mul_right]
  exact tsum_congr fun i => (ENNReal.tsum_mul_left (a := a i) (f := b))

/-! ### Summability from an atom -/

/-- `U_A(x, 1) = E_x[τ_A]`, and `E_x[τ_A] ≤ U_A(x, f)` for `f ≥ 1`. -/
theorem meanReturnTime_le_tabooPotFn (P : Kernel X X) [IsMarkovKernel P] (A : Set X)
    {f : X → ℝ≥0∞} (hf1 : ∀ x, 1 ≤ f x) (x : X) : meanReturnTime P A x ≤ tabooPotFn P A f x := by
  rw [meanReturnTime_eq_sumBefore]
  exact lintegral_mono fun ω => sumBefore_mono _ (fun k ω => hf1 (ω (k + 1))) ω

/-- **The summability bound behind Theorem 14.1.3 (iii)**: if `α` is an atom with `L(a, α) = 1`,
`E_a[τ_α] < ∞` and an aperiodic return-time law, and `λ` is a probability with
`E_λ[τ_α] < ∞`, then `Σₙ ‖λPⁿ⁺¹ − Pⁿ⁺¹(a, ·)‖_f ≤ E_λ[Σ_{k=1}^{τ_α} f] +
E_λ[τ_α] Var(u) U_α(a, f)` (14.14)–(14.15). -/
theorem tsum_fNorm_comp_le_atom {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (hLa : hitProb P α a = 1)
    (hEa : meanReturnTime P α a ≠ ∞)
    (hap : IsAperiodicLaw (entryLaw P hα.1 (Measure.dirac a))) (μ : Measure X)
    [IsProbabilityMeasure μ] (hE : ∫⁻ x, meanReturnTime P α x ∂μ ≠ ∞) {f : X → ℝ≥0∞}
    (hf : Measurable f) :
    ∑' n, fNorm f ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) ((P ^ (n + 1) : Kernel X X) a) ≤
      ∫⁻ x, tabooPotFn P α f x ∂μ + ENNReal.ofReal ((∫⁻ x, meanReturnTime P α x ∂μ).toReal *
        renewalVar (entryLaw P hα.1 (Measure.dirac a))) * tabooPotFn P α f a := by
  set p := entryLaw P hα.1 (Measure.dirac a)
  set Eμ := (∫⁻ x, meanReturnTime P α x ∂μ).toReal
  have hp := isIncrementLaw_entryLaw P hα.1 hLa
  have hmp : Summable fun n : ℕ => (n : ℝ) * p n := by
    have h1 : HasSum (renewalTail p) (meanReturnTime P α a).toReal := by
      rw [show renewalTail p = fun n => (tabooKernel P hα.1 n a univ).toReal from
        funext (renewalTail_entryLaw P hα.1 a)]
      exact hasSum_tabooKernel_univ P hα.1 a hEa
    exact (summable_renewalTail_iff hp).1 h1.summable
  have hu : atomRenewal P α a = realRenewalSeq p := atomRenewal_eq_realRenewalSeq hα ha
  have hv := summable_seqDiff_realRenewalSeq hp hap hmp
  obtain ⟨hma, hmean⟩ := entryLaw_mean P hα.1 μ hE
  have hdelay : IsDelayLaw (entryLaw P hα.1 μ) := (isIncrementLaw_entryLaw_of P hα.1 μ
    (lintegral_hitProb_eq_one_of_lintegral_meanReturnTime P hα.1 μ hE)).isDelayLaw
  obtain ⟨hgs, hgle⟩ := abs_sub_realConv_summable hdelay hma hv
  set w := fun k => |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - atomRenewal P α a k|
    with hwdef
  have hw : w = fun k => |realRenewalSeq p k - realConv (entryLaw P hα.1 μ) (realRenewalSeq p) k|
    := by funext k; simp only [w, hu]; rw [abs_sub_comm]
  have hws : Summable w := by rw [hw]; exact hgs
  have hwle : ∑' k, w k ≤ Eμ * renewalVar p := by
    rw [hw]
    refine hgle.trans_eq ?_
    rw [hmean]
    rfl
  set t : ℕ → ℝ≥0∞ := fun j => ∫⁻ y, f y ∂tabooKernel P hα.1 j a with ht
  have hbd := fun n => fNorm_comp_pow_succ_le_atom hα ha μ n f
  calc ∑' n, fNorm f ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) ((P ^ (n + 1) : Kernel X X) a)
      ≤ ∑' n, (∫⁻ y, f y ∂tabooSeq P hα.1 μ n +
          ∑ k ∈ range (n + 1), ENNReal.ofReal (w k) * t (n - k)) := ENNReal.tsum_le_tsum hbd
    _ = ∫⁻ x, tabooPotFn P α f x ∂μ + (∑' k, ENNReal.ofReal (w k)) * ∑' j, t j := by
        rw [ENNReal.tsum_add, tsum_lintegral_tabooSeq P hα.1 hf μ, tsum_sum_range_mul]
    _ ≤ ∫⁻ x, tabooPotFn P α f x ∂μ + ENNReal.ofReal (Eμ * renewalVar p) *
          tabooPotFn P α f a := by
        refine add_le_add le_rfl (mul_le_mul' ?_ (le_of_eq ?_))
        · rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => abs_nonneg _) hws]
          exact ENNReal.ofReal_le_ofReal hwle
        · rw [ht, tsum_lintegral_tabooKernel P hα.1 hf a]

/-- On an atom, `Pⁿ⁺¹(a, f) ≤ π(f) / π(α)` for an invariant probability `π`: `π(f) = πPⁿ⁺¹(f) ≥
π(α) Pⁿ⁺¹(a, f)`. In particular `Pⁿ⁺¹(a, f) < ∞` when `π(f) < ∞` and `π(α) > 0`. -/
theorem IsAtom.mul_lintegral_pow_le {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {π : Measure X} (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    π α * ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a ≤ ∫⁻ y, f y ∂π := by
  calc π α * ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a
      = ∫⁻ x in α, ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) x ∂π := by
        rw [setLIntegral_congr_fun hα.1 fun x hx => by rw [hα.pow_succ_eq hx ha n],
          setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x, ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) x ∂π := setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, f y ∂π := by rw [lintegral_comp_kernel _ π hf, hπ.pow (n + 1)]

/-! ### Proposition 14.1.2 -/

omit [MeasurableSpace X] in
/-- `σ_α + 1 ≤ t + (σ_α + 1) ∘ θᵗ`. -/
theorem firstHit_add_one_le_add_shift (A : Set X) (ω : ℕ → X) (t : ℕ) :
    firstHit A ω + 1 ≤ (t : WithTop ℕ) + (firstHit A (shift t ω) + 1) := by
  rw [← add_assoc]
  exact add_le_add_left (firstHit_le_add_shift A ω t) 1

/-- If `G_A(·, f) ≤ n` on a measurable set `B`, then `G_A(x, f) ≤ E_x[Σ_{k<τ_B} f(Φ_k)] + n` for
every `x` (strong Markov property at `τ_B`, the bound in the proof of Proposition 14.1.2). -/
theorem gKernelFn_le_fSumReturn_add {P : Kernel X X} [IsMarkovKernel P] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) {f : X → ℝ≥0∞} (hf : Measurable f)
    {M : ℝ≥0∞} (hM : ∀ y ∈ B, gKernelFn P A f y ≤ M) (x : X) :
    gKernelFn P A f x ≤ fSumReturn P B f x + M := by
  have := isMarkovKernel_pathKernel P
  refine (lintegral_sumBefore_le_stopping P x (proposition_3_4_4 hB).1
    (measurableSet_lt_firstHit_add_one hA) (firstHit_add_one_le_add_shift A) hf).trans
    (add_le_add le_rfl ?_)
  calc ∫⁻ ω in {ω | firstReturn B ω ≠ ⊤}, ∫⁻ ω', sumBefore (fun ω => firstHit A ω + 1)
        (fun k ω => f (ω k)) ω' ∂pathKernel P (stoppedState (firstReturn B) ω) ∂pathKernel P x
      ≤ ∫⁻ _ in {ω | firstReturn B ω ≠ ⊤}, M ∂pathKernel P x := by
        refine setLIntegral_mono measurable_const fun ω hω => hM _ ?_
        obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
        rw [stoppedState_of_eq ht.symm]
        exact mem_of_firstReturn_eq ht.symm
    _ ≤ M := by
        rw [setLIntegral_const]
        exact mul_le_of_le_one_right' prob_le_one

/-- `U_α(x, f) ≤ G_α(x, f) + U_α(a, f)` on an atom. -/
theorem IsAtom.tabooPotFn_le_gKernelFn {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    tabooPotFn P α f x ≤ gKernelFn P α f x + tabooPotFn P α f a := by
  by_cases hx : x ∈ α
  · rw [hα.tabooPotFn_eq hf hx ha]; exact le_add_self
  · rw [gKernelFn_eq P hα.1 hf x, indicator_of_mem (show x ∈ αᶜ from hx)]
    exact le_add_self.trans le_self_add

/-- The atom data used throughout: `π = π(α) μ°_α`, `U_α(a, f) < ∞`, the drift (V3) for
`G_α(·, f)` with `b = U_α(a, f)`, the petiteness of `α`, and `G_α(a, f) < ∞`. -/
theorem atom_driftV3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hπf : ∫⁻ y, f y ∂π ≠ ∞) :
    π = π α • atomMeasure P h.1.1 a ∧ tabooPotFn P α f a ≠ ∞ ∧
      DriftV3 P (gKernelFn P α f) f (tabooPotFn P α f a) α ∧ IsPetite P α := by
  have hrec := proposition_10_1_1 hpos
  have hrep := eq_smul_atomMeasure_of_accessible h hrec ha hπ
  exact ⟨hrep, tabooPotFn_ne_top_of_rep P h.1.1 a hrep hf hπf, driftV3_gKernelFn h.1.1 hf
    fun x hx => (h.1.tabooPotFn_eq hf hx ha).le, h.1.isPetite ⟨a, ha⟩⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 14.1.2 (ii)** (MT p. 340): for a positive chain with an accessible atom `α` and
`π(f) < ∞` (`f` finite at a point of `α`), the sets `S_f(n) = {G_α(·, f) ≤ n}` are `f`-regular and
increasing, and their union `S_f = {G_α(·, f) < ∞}` is full and absorbing. -/
theorem proposition_14_1_2_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∃ a ∈ α, f a ≠ ∞) (hπf : ∫⁻ y, f y ∂π ≠ ∞) :
    (∀ n : ℕ, IsFRegularSet P ψ f {x | gKernelFn P α f x ≤ n}) ∧
      Monotone (fun n : ℕ => {x | gKernelFn P α f x ≤ n}) ∧
      ⋃ n : ℕ, {x | gKernelFn P α f x ≤ n} = {x | gKernelFn P α f x ≠ ∞} ∧
      IsFull ψ {x | gKernelFn P α f x ≠ ∞} ∧ IsAbsorbing P {x | gKernelFn P α f x ≠ ∞} := by
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero h.2.2.ne'
  obtain ⟨-, hc, hdrift, hpet⟩ := atom_driftV3 hpos h ha hπ hf hπf
  have hVm := measurable_gKernelFn h.1.1 hf (P := P)
  obtain ⟨a', ha', hfa'⟩ := hfin
  have ha0 : gKernelFn P α f a' ≠ ∞ := by rw [gKernelFn_of_mem h.1.1 hf ha']; exact hfa'
  obtain ⟨habs, hfull⟩ := lemma_14_2_1 h.2.1.2.1 hVm hc hdrift ha0
  refine ⟨fun n => theorem_14_2_6_sublevel hpos.1 hVm hf hc hpet hdrift
    (ENNReal.natCast_ne_top n), fun m n hmn x hx => ?_, ?_, hfull, habs⟩
  · exact le_trans (show gKernelFn P α f x ≤ m from hx) (by exact_mod_cast hmn)
  · ext x
    simp only [mem_iUnion, mem_ofPred_eq]
    refine ⟨fun ⟨n, hn⟩ => ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) hn, fun hx => ?_⟩
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    exact ⟨n, hn.le⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- Under the hypotheses of Proposition 14.1.2 some sublevel set `{G_α(·, f) ≤ n}` lies in
`B⁺(X)`. -/
theorem exists_sublevel_pos_atom {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∃ a ∈ α, f a ≠ ∞) (hπf : ∫⁻ y, f y ∂π ≠ ∞) :
    ∃ n : ℕ, 0 < ψ {x | gKernelFn P α f x ≤ n} := by
  obtain ⟨-, -, hU, hfull, -⟩ := proposition_14_1_2_ii hpos h hπ hf hfin hπf
  by_contra hcon
  push Not at hcon
  apply hpos.1.1
  rw [← Measure.measure_univ_eq_zero]
  refine le_antisymm ?_ zero_le
  calc ψ univ ≤ ψ ((⋃ n : ℕ, {x | gKernelFn P α f x ≤ n}) ∪ {x | gKernelFn P α f x ≠ ∞}ᶜ) :=
        measure_mono (by rw [hU, union_compl_self])
    _ ≤ ψ (⋃ n : ℕ, {x | gKernelFn P α f x ≤ n}) + ψ {x | gKernelFn P α f x ≠ ∞}ᶜ :=
        measure_union_le _ _
    _ = 0 := by
        rw [hfull, add_zero]
        exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hcon n)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 14.1.2 (i)** for states: under the hypotheses of Proposition 14.1.2, `x` is
`f`-regular iff `G_α(x, f) < ∞`. -/
theorem isFRegularState_iff_atom {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∃ a ∈ α, f a ≠ ∞) (hπf : ∫⁻ y, f y ∂π ≠ ∞) (x : X) :
    IsFRegularState P ψ f x ↔ gKernelFn P α f x ≠ ∞ := by
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero h.2.2.ne'
  obtain ⟨-, hc, hdrift, hpet⟩ := atom_driftV3 hpos h ha hπ hf hπf
  have hVm := measurable_gKernelFn h.1.1 hf (P := P)
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_sublevel_pos_atom hpos h hπ hf hfin hπf
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hx _ (measurableSet_le hVm
      measurable_const) hn, ENNReal.natCast_ne_top n⟩) ?_
    exact gKernelFn_le_fSumReturn_add h.1.1 (measurableSet_le hVm measurable_const) hf
      (fun y hy => hy) x
  · exact fun hx => isFRegularState_of_driftV3 hpos.1 hVm hf hc hpet hdrift hx

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 14.1.2 (i)** (MT p. 340): under the hypotheses of Proposition 14.1.2, a
measurable set `C` is `f`-regular iff `sup_{x ∈ C} G_α(x, f) < ∞`. -/
theorem proposition_14_1_2_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∃ a ∈ α, f a ≠ ∞) (hπf : ∫⁻ y, f y ∂π ≠ ∞) {C : Set X} (hC : MeasurableSet C) :
    IsFRegularSet P ψ f C ↔ ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, gKernelFn P α f x ≤ M := by
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero h.2.2.ne'
  obtain ⟨-, hc, hdrift, hpet⟩ := atom_driftV3 hpos h ha hπ hf hπf
  have hVm := measurable_gKernelFn h.1.1 hf (P := P)
  constructor
  · intro hCr
    obtain ⟨n, hn⟩ := exists_sublevel_pos_atom hpos h hπ hf hfin hπf
    obtain ⟨M, hM, hbound⟩ := hCr.2 _ (measurableSet_le hVm measurable_const) hn
    refine ⟨M + n, ENNReal.add_ne_top.2 ⟨hM, ENNReal.natCast_ne_top n⟩, fun x hx => ?_⟩
    exact (gKernelFn_le_fSumReturn_add h.1.1 (measurableSet_le hVm measurable_const) hf
      (fun y hy => hy) x).trans (add_le_add (hbound x hx) le_rfl)
  · rintro ⟨M, hM, hbound⟩
    exact theorem_14_2_3_i_fRegular hpos.1 hVm hf hc hpet hdrift hC hM hbound

/-! ### `f`-ergodicity and Theorem 14.1.3 -/

/-- The chain is **`f`-ergodic** (MT p. 337): `f ≥ 1`, the chain is positive Harris with
invariant probability `π`, `π(f) < ∞`, and `‖Pᵏ(x, ·) − π‖_f → 0` for every initial state. -/
def IsFErgodic (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (f : X → ℝ≥0∞)
    (π : Measure X) : Prop :=
  (∀ x, 1 ≤ f x) ∧ IsPositiveHarris P ψ ∧ IsProbabilityMeasure π ∧ IsInvariant P π ∧
    ∫⁻ y, f y ∂π ≠ ∞ ∧ ∀ x, Tendsto (fun k => fNorm f ((P ^ k : Kernel X X) x) π) atTop (𝓝 0)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.1.3 (i)** (MT p. 341): for a positive Harris aperiodic chain with an accessible
atom and `π(f) < ∞` (`f` finite), the set `S_f` of `f`-regular states is absorbing and full, and
`‖Pᵏ(x, ·) − π‖_f → 0` for every `x ∈ S_f`. -/
theorem theorem_14_1_3_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {α : Set X}
    (h : IsAccessibleAtom P ψ α) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hfin : ∀ x, f x ≠ ∞) (hπf : ∫⁻ y, f y ∂π ≠ ∞) :
    IsAbsorbing P {x | IsFRegularState P ψ f x} ∧ IsFull ψ {x | IsFRegularState P ψ f x} ∧
      ∀ x, IsFRegularState P ψ f x →
        Tendsto (fun k => fNorm f ((P ^ k : Kernel X X) x) π) atTop (𝓝 0) := by
  have hpos := hph.2
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero h.2.2.ne'
  obtain ⟨hrep, hc, -, -⟩ := atom_driftV3 hpos h ha hπ hf hπf
  have hset : {x | IsFRegularState P ψ f x} = {x | gKernelFn P α f x ≠ ∞} := by
    ext x; exact isFRegularState_iff_atom hpos h hπ hf ⟨a, ha, hfin a⟩ hπf x
  obtain ⟨-, -, -, hfull, habs⟩ := proposition_14_1_2_ii hpos h hπ hf ⟨a, ha, hfin a⟩ hπf
  refine ⟨hset ▸ habs, hset ▸ hfull, fun x hx => ?_⟩
  have herg := proposition_13_2_4_i hpos hap h hπ a ha
  have hL : ∫⁻ y, hitProb P α y ∂Measure.dirac x = 1 := by
    rw [lintegral_dirac' _ (measurable_hitProb P h.1.1),
      IsHarris.hitProb_eq_one hph.1 h.1.1 h.2.2 x]
  have hU : ∫⁻ y, tabooPotFn P α f y ∂Measure.dirac x ≠ ∞ := by
    rw [lintegral_dirac' _ (measurable_tabooPotFn P h.1.1 hf)]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨(isFRegularState_iff_atom hpos h hπ hf
      ⟨a, ha, hfin a⟩ hπf x).1 hx, hc⟩) (h.1.tabooPotFn_le_gKernelFn ha hf x)
  have hlim := tendsto_fNorm_of_ergodic_atom h.1 ha hrep herg hf hπf (Measure.dirac x) hL hU
  simp_rw [dirac_kernel] at hlim
  exact hlim

variable [MeasurableSpace.CountablyGenerated X] in
/-- An `f`-regular chain (with `f ≥ 1`, recurrent, with invariant probability `π`) has
`π(f) < ∞` (Proposition 14.1.1 on an `f`-regular set in `B⁺(X)`). -/
theorem IsFRegularChain.lintegral_ne_top {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hrec : IsRecurrentChain P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hreg : IsFRegularChain P ψ f) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) : ∫⁻ y, f y ∂π ≠ ∞ := by
  obtain ⟨C, hC, hψC, -⟩ := hreg.exists_pos hrec.1
  obtain ⟨M, hM, hbound⟩ := hC.2 C hC.1 hψC
  exact (proposition_14_1_1 hrec ⟨inferInstance, hπ⟩ (IsProbabilityMeasure.ne_zero π) hf hf1 hC.1
    (nonempty_of_measure_ne_zero hψC.ne') (measure_ne_top π C) hM hbound).2.2.1

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.1.3 (ii)** (MT p. 341): a positive Harris aperiodic chain with an accessible
atom which is `f`-regular (`f ≥ 1` finite) is `f`-ergodic. -/
theorem theorem_14_1_3_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {α : Set X}
    (h : IsAccessibleAtom P ψ α) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hfin : ∀ x, f x ≠ ∞)
    (hreg : IsFRegularChain P ψ f) : IsFErgodic P ψ f π := by
  have hπf := hreg.lintegral_ne_top (proposition_10_1_1 hph.2) hf hf1 hπ
  obtain ⟨-, -, hconv⟩ := theorem_14_1_3_i hph hap h hπ hf hfin hπf
  obtain ⟨Cs, hCs, hcov⟩ := hreg
  refine ⟨hf1, hph, inferInstance, hπ, hπf, fun x => hconv x ?_⟩
  obtain ⟨m, hm⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ n, Cs n)
  exact (hCs m).isFRegularState hm

variable [MeasurableSpace.CountablyGenerated X] in
/-- An `f`-regular probability `λ` has `λ(G_α(·, f)) < ∞`, under the hypotheses of
Proposition 14.1.2. -/
theorem lintegral_gKernelFn_ne_top_of_isFRegularMeasure {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hpos : IsPositive P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hfin : ∃ a ∈ α, f a ≠ ∞) (hπf : ∫⁻ y, f y ∂π ≠ ∞) {μ : Measure X}
    [IsProbabilityMeasure μ] (hμ : IsFRegularMeasure P ψ f μ) :
    ∫⁻ x, gKernelFn P α f x ∂μ ≠ ∞ := by
  have hVm := measurable_gKernelFn h.1.1 hf (P := P)
  obtain ⟨n, hn⟩ := exists_sublevel_pos_atom hpos h hπ hf hfin hπf
  have hB := measurableSet_le hVm (measurable_const (a := (n : ℝ≥0∞)))
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hμ _ hB hn, ENNReal.natCast_ne_top n⟩) ?_
  calc ∫⁻ x, gKernelFn P α f x ∂μ ≤ ∫⁻ x, (fSumReturn P {x | gKernelFn P α f x ≤ n} f x + n) ∂μ :=
        lintegral_mono fun x => gKernelFn_le_fSumReturn_add h.1.1 hB hf (fun y hy => hy) x
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- **Theorem 14.1.3 (iii)** (MT p. 341), (14.13): for a positive Harris aperiodic chain with an
accessible atom and `π(f) < ∞` (`1 ≤ f < ∞`), there is `M_f < ∞` such that for all probabilities
`λ`, `μ`, `Σ_{n ≥ 1} ∫ λ(dx) ∫ μ(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f ≤ M_f (λ(G_α(·, f)) + μ(G_α(·, f)))`.
For `f`-regular `λ`, `μ` the right side is finite
(`lintegral_gKernelFn_ne_top_of_isFRegularMeasure`). -/
theorem theorem_14_1_3_iii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {α : Set X}
    (h : IsAccessibleAtom P ψ α) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ y, f y ∂π ≠ ∞) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ (l m : Measure X) [IsProbabilityMeasure l] [IsProbabilityMeasure m],
      ∑' n, ∫⁻ x, ∫⁻ y, fNorm f ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y)
        ∂m ∂l ≤ M * (∫⁻ x, gKernelFn P α f x ∂l + ∫⁻ y, gKernelFn P α f y ∂m) := by
  have hpos := hph.2
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero h.2.2.ne'
  obtain ⟨hrep, hc, -, -⟩ := atom_driftV3 hpos h ha hπ hf hπf
  have hEa := meanReturnTime_ne_top_of_rep P h.1.1 a hrep
  have hLa := hitProb_eq_one_of_meanReturnTime_ne_top h.1.1 hEa
  have hap' := isAperiodicLaw_entryLaw h hap ha
  set c := tabooPotFn P α f a with hcdef
  set K := ENNReal.ofReal (renewalVar (entryLaw P h.1.1 (Measure.dirac a))) * c with hK
  have hKne : K ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc
  have hπα : π α ≠ 0 := measure_atom_ne_zero_of_rep P h.1.1 a hrep
  -- `Pⁿ⁺¹(a, f) < ∞`
  have hPa : ∀ n, ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a ≠ ∞ := fun n => by
    have h1 := h.1.mul_lintegral_pow_le ha hπ hf n
    intro htop
    rw [htop, ENNReal.mul_top hπα] at h1
    exact hπf (top_le_iff.1 h1)
  -- the pointwise bound `H(x) ≤ (1 + K) U_α(x, f)`
  set H : X → ℝ≥0∞ := fun x => ∑' n, fNorm f ((P ^ (n + 1) : Kernel X X) x)
    ((P ^ (n + 1) : Kernel X X) a) with hH
  have hHle : ∀ x, H x ≤ (1 + K) * (gKernelFn P α f x + c) := fun x => by
    have hU := h.1.tabooPotFn_le_gKernelFn ha hf x
    have hEx : meanReturnTime P α x ≤ tabooPotFn P α f x := meanReturnTime_le_tabooPotFn P α hf1 x
    by_cases hx : tabooPotFn P α f x = ∞
    · have : gKernelFn P α f x + c = ∞ := top_le_iff.1 (hx ▸ hU)
      rw [this, ENNReal.mul_top (by simp)]; exact le_top
    have hE : ∫⁻ y, meanReturnTime P α y ∂Measure.dirac x ≠ ∞ := by
      rw [lintegral_dirac' _ (measurable_meanReturnTime P h.1.1)]
      exact ne_top_of_le_ne_top hx hEx
    have hb := tsum_fNorm_comp_le_atom h.1 ha hLa hEa hap' (Measure.dirac x) hE hf
    simp_rw [dirac_kernel, lintegral_dirac' _ (measurable_tabooPotFn P h.1.1 hf),
      lintegral_dirac' _ (measurable_meanReturnTime P h.1.1)] at hb
    calc H x ≤ tabooPotFn P α f x + ENNReal.ofReal ((meanReturnTime P α x).toReal *
          renewalVar (entryLaw P h.1.1 (Measure.dirac a))) * c := hb
      _ ≤ tabooPotFn P α f x + tabooPotFn P α f x * K := by
          refine add_le_add le_rfl ?_
          rw [hK, ← mul_assoc]
          refine mul_le_mul' ?_ le_rfl
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal (ne_top_of_le_ne_top hx hEx)]
          exact mul_le_mul' hEx le_rfl
      _ = (1 + K) * tabooPotFn P α f x := by ring
      _ ≤ (1 + K) * (gKernelFn P α f x + c) := mul_le_mul' le_rfl hU
  -- `G_α ≥ f ≥ 1`
  have hG1 : ∀ x, 1 ≤ gKernelFn P α f x := fun x => by
    rw [gKernelFn_eq P h.1.1 hf x]; exact (hf1 x).trans le_self_add
  refine ⟨(1 + K) * (1 + c), ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hKne⟩)
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hc⟩), fun l m _ _ => ?_⟩
  have hpt : ∀ x y, ∑' n, fNorm f ((P ^ (n + 1) : Kernel X X) x)
      ((P ^ (n + 1) : Kernel X X) y) ≤ H x + H y := fun x y => by
    rw [hH, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rw [fNorm_comm f ((P ^ (n + 1) : Kernel X X) y)]
    exact fNorm_triangle _ _ _ (hPa n)
  have hGc : ∀ ρ : Measure X, IsProbabilityMeasure ρ →
      ∫⁻ x, H x ∂ρ ≤ (1 + K) * (1 + c) * ∫⁻ x, gKernelFn P α f x ∂ρ := fun ρ _ => by
    have hG1' : 1 ≤ ∫⁻ x, gKernelFn P α f x ∂ρ := by
      calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂ρ := by rw [lintegral_one, measure_univ]
        _ ≤ _ := lintegral_mono hG1
    calc ∫⁻ x, H x ∂ρ ≤ ∫⁻ x, (1 + K) * (gKernelFn P α f x + c) ∂ρ := lintegral_mono hHle
      _ = (1 + K) * (∫⁻ x, gKernelFn P α f x ∂ρ + c) := by
          rw [lintegral_const_mul' _ _ (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hKne⟩),
            lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ (1 + K) * (∫⁻ x, gKernelFn P α f x ∂ρ + c * ∫⁻ x, gKernelFn P α f x ∂ρ) :=
          mul_le_mul' le_rfl (add_le_add le_rfl (le_mul_of_one_le_right' hG1'))
      _ = (1 + K) * (1 + c) * ∫⁻ x, gKernelFn P α f x ∂ρ := by ring
  calc ∑' n, ∫⁻ x, ∫⁻ y, fNorm f ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y)
        ∂m ∂l
      ≤ ∫⁻ x, ∫⁻ y, ∑' n, fNorm f ((P ^ (n + 1) : Kernel X X) x)
          ((P ^ (n + 1) : Kernel X X) y) ∂m ∂l := by
        refine (tsum_lintegral_le_lintegral_tsum l _).trans (lintegral_mono fun x => ?_)
        exact tsum_lintegral_le_lintegral_tsum m _
    _ ≤ ∫⁻ x, H x ∂l + ∫⁻ y, H y ∂m := lintegral_lintegral_le_of_le_add hpt l m
    _ ≤ (1 + K) * (1 + c) * ∫⁻ x, gKernelFn P α f x ∂l +
          (1 + K) * (1 + c) * ∫⁻ y, gKernelFn P α f y ∂m :=
        add_le_add (hGc l inferInstance) (hGc m inferInstance)
    _ = _ := by ring

/-! ### Theorem 14.1.4: countable spaces -/

/-- **Theorem 14.1.4** (MT p. 342): on a countable space, for a positive Harris aperiodic chain
whose maximal irreducibility measure charges every state and `π(f) < ∞` (`1 ≤ f < ∞`),
`‖Pᵏ(x, ·) − π‖_f → 0` and `Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f < ∞` for all `x`, `y`. -/
theorem theorem_14_1_4 [Countable X] [MeasurableSingletonClass X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ)
    (hψx : ∀ x, 0 < ψ {x}) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf1 : ∀ x, 1 ≤ f x) (hfin : ∀ x, f x ≠ ∞) (hπf : ∫⁻ y, f y ∂π ≠ ∞) :
    (∀ x, Tendsto (fun k => fNorm f ((P ^ k : Kernel X X) x) π) atTop (𝓝 0)) ∧
      ∀ x y, ∑' n, fNorm f ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y) ≠ ∞ := by
  have hf : Measurable f := measurable_of_countable f
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    exact hph.2.1.1 (Measure.eq_zero_of_isEmpty ψ)
  have h : IsAccessibleAtom P ψ {x₀} := ⟨isAtom_singleton P x₀, hph.2.1, hψx x₀⟩
  obtain ⟨-, hfull, hconv⟩ := theorem_14_1_3_i hph hap h hπ hf hfin hπf
  -- every state is `f`-regular: the exceptional set is `ψ`-null, hence empty
  have hall : ∀ x, IsFRegularState P ψ f x := fun x => by
    by_contra hx
    have : ψ {x} ≤ ψ {x | IsFRegularState P ψ f x}ᶜ :=
      measure_mono fun y hy => by rw [mem_singleton_iff.1 hy]; exact hx
    rw [hfull] at this
    exact (hψx x).ne' (le_antisymm this zero_le)
  refine ⟨fun x => hconv x (hall x), fun x y => ?_⟩
  obtain ⟨M, hM, hbound⟩ := theorem_14_1_3_iii hph hap h hπ hf hf1 hπf
  have hb := hbound (Measure.dirac x) (Measure.dirac y)
  have hG : ∀ z, gKernelFn P {x₀} f z ≠ ∞ := fun z =>
    (isFRegularState_iff_atom hph.2 h hπ hf ⟨x₀, mem_singleton x₀, hfin x₀⟩ hπf z).1 (hall z)
  have hGm := measurable_gKernelFn (P := P) (measurableSet_singleton x₀) hf
  simp only [lintegral_dirac' _ hGm] at hb
  have hb' : ∑' n, fNorm f ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hM (ENNReal.add_ne_top.2 ⟨hG x, hG y⟩)) ?_
    refine le_trans (le_of_eq ?_) hb
    refine tsum_congr fun n => ?_
    rw [lintegral_dirac', lintegral_dirac']
    · exact measurable_of_countable _
    · exact measurable_of_countable _
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_ne_top.2 ⟨?_, hb'⟩
  rw [pow_zero_apply, pow_zero_apply]
  refine ne_top_of_le_ne_top ?_ (fNorm_le_add f _ _)
  rw [lintegral_dirac' _ hf, lintegral_dirac' _ hf]
  exact ENNReal.add_ne_top.2 ⟨hfin x, hfin y⟩

end MeynTweedie.Epilogue
