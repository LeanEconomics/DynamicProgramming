/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeometricErgodicity.GeometricAtoms

/-!
# Geometric regularity of `Φ` and its skeletons (MT §15.3.2)

Meyn and Tweedie, §15.3.2, pp. 382–383. For `m ≥ 1` the `m`-skeleton has kernel `Pᵐ`, and
`f^{(m)} = Σ_{i<m} Pⁱf` (14.22) is `fSkel P m f`. The state space is countably generated and `ψ`
is a maximal irreducibility measure; for an aperiodic chain every skeleton is `ψ`-irreducible
with the same `ψ` (Proposition 5.4.5).

**Tools.**
* `DriftV4.iterate`: (V4) iterates to `PᵐV ≤ ρᵐ V + b Σ_{i<m} Pⁱ(·, C)`;
  `fSkel_le_of_driftV4`: `f^{(m)} ≤ m (1 + b m) V` for `f ≤ V`, `V ≥ 1`.
* `IsPetite.of_skeleton`: a set petite for a skeleton is petite for the chain.
* `geomSum_le_skeleton`: **the skeleton dominates the chain**,
  `E_x[Σ_{k<τ_B} f(Φ_k) rᵏ] ≤ rᵐ E^{(m)}_x[Σ_{j<τ_B^{(m)}} f^{(m)}(Φ_{mj}) r^{mj}]`.
* `exists_one_lt_pow_le`: for `R > 1` there is `r > 1` with `rᵐ ≤ R`.

**Results.**
* **Theorem 15.3.4** (p. 382): (i) `theorem_15_3_4_i`, (V4) for `P` and a petite `C` gives (V4) for
  `Pᵐ` and a set small for `Pᵐ` ((15.39)); (ii) `theorem_15_3_4_ii`, an `f`-geometrically regular
  `C ∈ B⁺(X)` is `f`-geometrically regular for every skeleton.
* **Theorem 15.3.5** (`theorem_15_3_5`, p. 383): an `f`-geometrically regular aperiodic chain has
  `f`-geometrically regular skeletons.
* **Theorem 15.3.6** (`theorem_15_3_6`, p. 383): `C ∈ B⁺(X)` is `f`-geometrically regular iff it
  is `f^{(m)}`-geometrically regular for one, and then every, `m`-skeleton.
* **Theorem 15.3.7** (`theorem_15_3_7`, p. 383): the chain is `f`-geometrically regular iff each
  `m`-skeleton is `f^{(m)}`-geometrically regular; one skeleton suffices.

**Hypotheses.** Theorem 15.3.4 (ii) assumes `C ∈ B⁺(X)`: its proof goes through Theorem 15.2.1,
which needs it (an `f`-geometrically regular set is petite and `f`-Kendall only for `C ∈ B⁺(X)`).
-/

namespace MeynTweedie.GeometricErgodicity

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### Iterating (V4) -/

/-- **(V4) iterated**: `PᵐV ≤ ρᵐ V + b Σ_{i<m} Pⁱ(·, C)` for `ρ ≤ 1`. -/
theorem DriftV4.iterate {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0∞} (hV : Measurable V)
    {ρ b : ℝ≥0∞} (hρ : ρ ≤ 1) {C : Set X} (hC : MeasurableSet C) (h : DriftV4 P V ρ b C)
    (m : ℕ) (x : X) :
    ∫⁻ y, V y ∂(P ^ m : Kernel X X) x ≤ ρ ^ m * V x + b * ∑ i ∈ range m, (P ^ i : Kernel X X) x C
    := by
  induction m with
  | zero => rw [pow_zero_apply, lintegral_dirac' _ hV]; simp
  | succ m ih =>
    have := isMarkovKernel_pow P m
    have hPV : ∫⁻ y, V y ∂(P ^ (m + 1) : Kernel X X) x =
        ∫⁻ y, ∫⁻ z, V z ∂P y ∂(P ^ m : Kernel X X) x := by
      rw [pow_succ']
      exact Kernel.lintegral_comp P (P ^ m) x hV
    rw [hPV]
    calc ∫⁻ y, ∫⁻ z, V z ∂P y ∂(P ^ m : Kernel X X) x
        ≤ ∫⁻ y, (ρ * V y + C.indicator (fun _ => b) y) ∂(P ^ m : Kernel X X) x :=
          lintegral_mono fun y => h y
      _ = ρ * ∫⁻ y, V y ∂(P ^ m : Kernel X X) x + b * (P ^ m : Kernel X X) x C := by
          rw [lintegral_add_left (hV.const_mul ρ), lintegral_const_mul _ hV,
            lintegral_indicator_const hC]
      _ ≤ ρ * (ρ ^ m * V x + b * ∑ i ∈ range m, (P ^ i : Kernel X X) x C) +
            b * (P ^ m : Kernel X X) x C := add_le_add (mul_le_mul' le_rfl ih) le_rfl
      _ ≤ ρ ^ (m + 1) * V x + b * ∑ i ∈ range (m + 1), (P ^ i : Kernel X X) x C := by
          rw [Finset.sum_range_succ]
          have h1 : ρ * (ρ ^ m * V x) = ρ ^ (m + 1) * V x := by rw [pow_succ']; ring
          have h2 : ρ * (b * ∑ i ∈ range m, (P ^ i : Kernel X X) x C) ≤
              b * ∑ i ∈ range m, (P ^ i : Kernel X X) x C := mul_le_of_le_one_left' hρ
          calc ρ * (ρ ^ m * V x + b * ∑ i ∈ range m, (P ^ i : Kernel X X) x C) +
                b * (P ^ m : Kernel X X) x C
              = ρ * (ρ ^ m * V x) + ρ * (b * ∑ i ∈ range m, (P ^ i : Kernel X X) x C) +
                  b * (P ^ m : Kernel X X) x C := by ring
            _ ≤ ρ ^ (m + 1) * V x + b * ∑ i ∈ range m, (P ^ i : Kernel X X) x C +
                  b * (P ^ m : Kernel X X) x C := by
                rw [h1]; exact add_le_add (add_le_add le_rfl h2) le_rfl
            _ = ρ ^ (m + 1) * V x + b * (∑ i ∈ range m, (P ^ i : Kernel X X) x C +
                  (P ^ m : Kernel X X) x C) := by ring

/-- `PⁱV ≤ V + b i` under (V4) with `ρ ≤ 1`. -/
theorem DriftV4.pow_le {P : Kernel X X} [IsMarkovKernel P] {V : X → ℝ≥0∞} (hV : Measurable V)
    {ρ b : ℝ≥0∞} (hρ : ρ ≤ 1) {C : Set X} (hC : MeasurableSet C) (h : DriftV4 P V ρ b C)
    (i : ℕ) (x : X) : ∫⁻ y, V y ∂(P ^ i : Kernel X X) x ≤ V x + b * i := by
  refine (h.iterate hV hρ hC i x).trans
    (add_le_add (mul_le_of_le_one_left' (pow_le_one₀ zero_le hρ)) (mul_le_mul' le_rfl ?_))
  calc ∑ j ∈ range i, (P ^ j : Kernel X X) x C ≤ ∑ _j ∈ range i, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun j _ => by
          have := isMarkovKernel_pow P j
          exact prob_le_one
    _ = i := by simp

/-- `f^{(m)} ≤ m (1 + b m) V` under (V4) (`ρ ≤ 1`), for `f ≤ V` and `V ≥ 1`. -/
theorem fSkel_le_of_driftV4 {P : Kernel X X} [IsMarkovKernel P] {V f : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hfV : ∀ x, f x ≤ V x) {ρ b : ℝ≥0∞} (hρ : ρ ≤ 1)
    {C : Set X} (hC : MeasurableSet C) (h : DriftV4 P V ρ b C) (m : ℕ) (x : X) :
    fSkel P m f x ≤ m * (1 + b * m) * V x := by
  unfold fSkel
  calc ∑ i ∈ range m, ∫⁻ y, f y ∂(P ^ i : Kernel X X) x
      ≤ ∑ _i ∈ range m, (1 + b * m) * V x := Finset.sum_le_sum fun i hi => by
        refine (lintegral_mono fun y => hfV y).trans ((h.pow_le hV hρ hC i x).trans ?_)
        have hi : (i : ℝ≥0∞) ≤ m := by exact_mod_cast (Finset.mem_range.1 hi).le
        calc V x + b * i ≤ V x + b * m * V x :=
              add_le_add le_rfl ((mul_le_mul' le_rfl hi).trans (le_mul_of_one_le_right' (hV1 x)))
          _ = (1 + b * m) * V x := by ring
    _ = m * (1 + b * m) * V x := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ### Theorem 15.3.4 (i) -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.3.4 (i)** (MT p. 382), (15.39): for an aperiodic `ψ`-irreducible chain, if (V4)
holds for `V ≥ 1`, a petite `C`, `ρ < 1` and `b < ∞`, then for every `m ≥ 1` (V4) holds for the
`m`-skeleton, `PᵐV ≤ ρ' V + b' 1_{C'}` with `ρ' < 1`, `b' < ∞` and `C'` small for `Pᵐ`. -/
theorem theorem_15_3_4_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞)
    {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {m : ℕ} (hm : 1 ≤ m) :
    ∃ ρ' b' : ℝ≥0∞, ρ' < 1 ∧ b' ≠ ∞ ∧ ∃ C', IsSmall (P ^ m : Kernel X X) C' ∧
      DriftV4 (P ^ m : Kernel X X) V ρ' b' C' := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hρm : ρ ^ m < 1 := pow_lt_one₀ zero_le hρ (by omega)
  obtain ⟨ρ', hρρ', hρ'1⟩ := exists_between hρm
  have hb1 : b + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hb, ENNReal.one_ne_top⟩
  have hb10 : b + 1 ≠ 0 := by positivity
  set ε := (ρ' - ρ ^ m) / (b + 1) with hε
  have hε0 : 0 < ε := ENNReal.div_pos (tsub_pos_iff_lt.2 hρρ').ne' hb1
  obtain ⟨Cε, hsmall, hsum⟩ := lemma_14_2_8 P hψ hap hC hm hε0
  have hbε : b * ε ≤ ρ' - ρ ^ m := by
    calc b * ε ≤ (b + 1) * ε := mul_le_mul' le_self_add le_rfl
      _ = ρ' - ρ ^ m := by rw [hε, ENNReal.mul_div_cancel hb10 hb1]
  refine ⟨ρ', b * m, hρ'1, ENNReal.mul_ne_top hb (ENNReal.natCast_ne_top m), Cε, hsmall,
    fun x => ?_⟩
  calc ∫⁻ y, V y ∂(P ^ m : Kernel X X) x
      ≤ ρ ^ m * V x + b * ∑ i ∈ range m, (P ^ i : Kernel X X) x C :=
        h.iterate hV hρ.le hCm m x
    _ ≤ ρ ^ m * V x + b * (m * Cε.indicator 1 x + ε) := add_le_add le_rfl (mul_le_mul' le_rfl
        (hsum x))
    _ = ρ ^ m * V x + b * ε + b * m * Cε.indicator 1 x := by ring
    _ ≤ ρ ^ m * V x + (ρ' - ρ ^ m) * V x + Cε.indicator (fun _ => b * m) x := by
        refine add_le_add (add_le_add le_rfl (hbε.trans (le_mul_of_one_le_right' (hV1 x))))
          (le_of_eq ?_)
        by_cases hx : x ∈ Cε
        · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, mul_one]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
    _ = ρ' * V x + Cε.indicator (fun _ => b * m) x := by
        rw [← add_mul, add_tsub_cancel_of_le hρρ'.le]

/-! ### Petite sets of skeletons -/

/-- **A set petite for a skeleton is petite for the chain**: `K_a^{Pᵐ} = K_{a'}^{P}` with
`a'(k) = Σₙ a(n) 1{k = mn}`. -/
theorem IsPetite.of_skeleton {P : Kernel X X} {m : ℕ} {C : Set X}
    (h : IsPetite (P ^ m : Kernel X X) C) : IsPetite P C := by
  obtain ⟨a, ν, hC, ha, hν, hle⟩ := h
  set a' : ℕ → ℝ≥0∞ := fun k => ∑' n, if k = m * n then a n else 0 with ha'
  have hsamp : ∀ x, sampledKernel P a' x = sampledKernel (P ^ m : Kernel X X) a x := fun x => by
    ext A hA
    rw [sampledKernel_apply P a' x hA, sampledKernel_apply _ a x hA]
    simp_rw [ha', ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun n => ?_
    rw [tsum_eq_single (m * n) fun k hk => by simp [hk]]
    simp [pow_mul]
  refine ⟨a', ν, hC, ?_, hν, fun x hx => (hle x hx).trans (hsamp x).symm.le⟩
  change ∑' k, a' k = 1
  simp_rw [ha']
  rw [ENNReal.tsum_comm, ← ha]
  exact tsum_congr fun n => by simp

/-! ### The skeleton dominates the chain -/

/-- **The skeleton dominates the chain** (MT p. 383, the proof of Theorem 15.3.6): for `m ≥ 1` and
`r ≥ 1`, `E_x[Σ_{k<τ_B} f(Φ_k) rᵏ] ≤ rᵐ E^{(m)}_x[Σ_{j<τ_B^{(m)}} f^{(m)}(Φ_{mj}) (rᵐ)ʲ]`. -/
theorem geomSum_le_skeleton {P : Kernel X X} [IsMarkovKernel P] {m : ℕ} (hm : 1 ≤ m)
    {B : Set X} (hB : MeasurableSet B) {r : ℝ≥0∞} (hr : 1 ≤ r) {f : X → ℝ≥0∞}
    (hf : Measurable f) (x : X) :
    haveI := isMarkovKernel_pow P m
    geomSum P B r f x ≤ r ^ m * geomSum (P ^ m : Kernel X X) B (r ^ m) (fSkel P m f) x := by
  have := isMarkovKernel_pow P m
  have := isMarkovKernel_pathKernel P
  set s : (ℕ → X) → (ℕ → X) := fun ω n => ω (m * n) with hsdef
  have hs : Measurable s := measurable_pi_iff.2 fun n => measurable_pi_apply (m * n)
  have hGm : ∀ j : ℕ, MeasurableSet {ω : ℕ → X | (j : WithTop ℕ) < firstReturn B (s ω)} :=
    fun j => (natFilt (X := X)).le _ _ (measurableSet_natFilt_lt_firstReturn_skeleton hB m j)
  have hR : geomSum (P ^ m : Kernel X X) B (r ^ m) (fSkel P m f) x =
      ∑' j : ℕ, ∑ i ∈ range m, (r ^ m) ^ j * ∫⁻ ω in {ω | (j : WithTop ℕ) < firstReturn B (s ω)},
        f (ω (m * j + i)) ∂pathKernel P x := by
    have hcomp : ∀ a : ℕ → X, sumBefore (firstReturn B)
        (fun k ω => (r ^ m) ^ k * fSkel P m f (ω k)) (s a) =
        sumBefore (fun ω => firstReturn B (s ω)) (fun k ω => (r ^ m) ^ k * fSkel P m f (s ω k)) a
        := fun a => by
      simp only [sumBefore, Set.indicator_apply, mem_ofPred_eq]
    rw [geomSum, ← pathKernel_map_skeleton P m x,
      lintegral_map (measurable_sumBefore_geom hB _ (measurable_fSkel P m hf)) hs,
      lintegral_congr hcomp, lintegral_sumBefore _ (fun j => hGm j)
        (F := fun k ω => (r ^ m) ^ k * fSkel P m f (s ω k)) fun j => measurable_const.mul
          ((measurable_fSkel P m hf).comp ((measurable_pi_apply j).comp hs))]
    refine tsum_congr fun j => ?_
    rw [lintegral_const_mul (f := fun ω => fSkel P m f (s ω j)) _
      ((measurable_fSkel P m hf).comp ((measurable_pi_apply j).comp hs)), ← Finset.mul_sum]
    congr 1
    simp only [fSkel, hsdef]
    rw [lintegral_finsetSum (f := fun i (ω : ℕ → X) => ∫⁻ y, f y ∂(P ^ i : Kernel X X) (ω (m * j)))
      _ fun i _ => hf.lintegral_kernel.comp (measurable_pi_apply (m * j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmk := markov_lintegral P (Measure.dirac x)
      (measurableSet_natFilt_lt_firstReturn_skeleton hB m j) (H := fun ω : ℕ → X => f (ω i))
      (hf.comp (measurable_pi_apply i))
    rw [pathMeasure_dirac] at hmk
    rw [show (∫⁻ ω in {ω : ℕ → X | (j : WithTop ℕ) < firstReturn B fun n => ω (m * n)},
      f (ω (m * j + i)) ∂pathKernel P x) = ∫⁻ ω in {ω : ℕ → X | (j : WithTop ℕ) <
        firstReturn B fun n => ω (m * n)}, f (shift (m * j) ω i) ∂pathKernel P x from rfl, hmk]
    refine setLIntegral_congr_fun (hGm j) fun ω _ => ?_
    rw [lintegral_coord_eq_pow P (ω (m * j)) i hf]
  rw [hR, geomSum, lintegral_sumBefore _ (measurableSet_lt_firstReturn hB)
    (F := fun k (ω : ℕ → X) => r ^ k * f (ω k)) fun k =>
      measurable_const.mul (hf.comp (measurable_pi_apply k))]
  calc ∑' k : ℕ, ∫⁻ ω in {ω | (k : WithTop ℕ) < firstReturn B ω}, r ^ k * f (ω k) ∂pathKernel P x
      = ∑' j : ℕ, ∑ i ∈ range m, ∫⁻ ω in {ω | ((m * j + i : ℕ) : WithTop ℕ) < firstReturn B ω},
          r ^ (m * j + i) * f (ω (m * j + i)) ∂pathKernel P x :=
        tsum_eq_tsum_sum_block (fun k : ℕ => ∫⁻ ω in {ω | (k : WithTop ℕ) < firstReturn B ω},
          r ^ k * f (ω k) ∂pathKernel P x) hm
    _ ≤ ∑' j : ℕ, r ^ m * ∑ i ∈ range m, (r ^ m) ^ j *
          ∫⁻ ω in {ω | (j : WithTop ℕ) < firstReturn B (s ω)}, f (ω (m * j + i))
            ∂pathKernel P x := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have hSG : {ω : ℕ → X | ((m * j + i : ℕ) : WithTop ℕ) < firstReturn B ω} ⊆
            {ω | (j : WithTop ℕ) < firstReturn B (s ω)} := fun ω hω => by
          simp only [mem_ofPred_eq] at hω ⊢
          by_contra hc
          push Not at hc
          obtain ⟨t, ht⟩ : ∃ t : ℕ, firstReturn B (s ω) = t := by
            cases h : firstReturn B (s ω) with
            | top => rw [h] at hc; exact absurd hc (by simp)
            | coe t => exact ⟨t, rfl⟩
          have htj : t ≤ j := by rw [ht] at hc; exact_mod_cast hc
          have ht1 : 1 ≤ t := by
            have := one_le_firstReturn B (s ω); rw [ht] at this; exact WithTop.coe_le_coe.1 this
          have hmem : ω (m * t) ∈ B := (mem_of_firstReturn_eq ht : s ω t ∈ B)
          have hle := firstReturn_le_of_mem (A := B) (ω := ω) (j := m * t) (by nlinarith) hmem
          have : ((m * j + i : ℕ) : WithTop ℕ) < WithTop.some (m * t) := lt_of_lt_of_le hω hle
          have : m * j + i < m * t := WithTop.coe_lt_coe.1 this
          nlinarith
        have hpow : r ^ (m * j + i) ≤ r ^ m * (r ^ m) ^ j := by
          rw [← pow_mul, ← pow_add]
          exact pow_le_pow_right₀ hr (by omega)
        have hfm : Measurable fun ω : ℕ → X => f (ω (m * j + i)) :=
          hf.comp (measurable_pi_apply (m * j + i))
        calc ∫⁻ ω in {ω | ((m * j + i : ℕ) : WithTop ℕ) < firstReturn B ω},
              r ^ (m * j + i) * f (ω (m * j + i)) ∂pathKernel P x
            ≤ ∫⁻ ω in {ω | ((m * j + i : ℕ) : WithTop ℕ) < firstReturn B ω},
                (r ^ m * (r ^ m) ^ j) * f (ω (m * j + i)) ∂pathKernel P x :=
              setLIntegral_mono' (measurableSet_lt_firstReturn hB _) fun ω _ =>
                mul_le_mul' hpow le_rfl
          _ ≤ ∫⁻ ω in {ω | (j : WithTop ℕ) < firstReturn B (s ω)},
                (r ^ m * (r ^ m) ^ j) * f (ω (m * j + i)) ∂pathKernel P x :=
              lintegral_mono_set hSG
          _ = r ^ m * ((r ^ m) ^ j * ∫⁻ ω in {ω | (j : WithTop ℕ) < firstReturn B (s ω)},
                f (ω (m * j + i)) ∂pathKernel P x) := by
              rw [lintegral_const_mul _ hfm, mul_assoc]
    _ = r ^ m * ∑' j : ℕ, ∑ i ∈ range m, (r ^ m) ^ j *
          ∫⁻ ω in {ω | (j : WithTop ℕ) < firstReturn B (s ω)}, f (ω (m * j + i))
            ∂pathKernel P x := ENNReal.tsum_mul_left

/-- For `R > 1` and `m` there is `r > 1`, `r < ∞`, with `rᵐ ≤ R`. -/
theorem exists_one_lt_pow_le {R : ℝ≥0∞} (hR : 1 < R) (m : ℕ) :
    ∃ r, 1 < r ∧ r ≠ ∞ ∧ r ^ m ≤ R := by
  obtain ⟨n, hn⟩ := ((tendsto_seqOneLt_pow m).eventually (gt_mem_nhds hR)).exists
  exact ⟨seqOneLt n, one_lt_seqOneLt n, seqOneLt_ne_top n, hn.le⟩

/-- An `f`-geometrically regular set is `g`-geometrically regular for `g ≤ c f`, `c < ∞`. -/
theorem IsFGeomRegularSet.of_le_const_mul {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f g : X → ℝ≥0∞} (hf : Measurable f) {c : ℝ≥0∞} (hc : c ≠ ∞) (hgf : ∀ x, g x ≤ c * f x)
    {A : Set X} (h : IsFGeomRegularSet P ψ f A) : IsFGeomRegularSet P ψ g A :=
  ⟨h.1, fun B hB hψB => by
    obtain ⟨r, hr, hr', M, hM, hb⟩ := h.2 B hB hψB
    refine ⟨r, hr, hr', c * M, ENNReal.mul_ne_top hc hM, fun x hx => ?_⟩
    calc geomSum P B r g x ≤ geomSum P B r (fun y => c * f y) x := geomSum_mono_f P B r hgf x
      _ = c * geomSum P B r f x := geomSum_const_mul P hB r c hf x
      _ ≤ c * M := mul_le_mul' le_rfl (hb x hx)⟩

/-- `f`-geometric regularity on `S` passes to `g ≤ c f`, `c < ∞`. -/
theorem IsFGeomRegularOn.of_le_const_mul {P : Kernel X X} [IsMarkovKernel P] {f g : X → ℝ≥0∞}
    (hf : Measurable f) {c : ℝ≥0∞} (hc : c ≠ ∞) (hgf : ∀ x, g x ≤ c * f x) {S : Set X}
    (h : IsFGeomRegularOn P f S) : IsFGeomRegularOn P g S := by
  obtain ⟨C, hC, κ, hκ, hκ', hfin, M, hM, hb⟩ := h
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hle : ∀ x, geomSum P C κ g x ≤ c * geomSum P C κ f x := fun x =>
    (geomSum_mono_f P C κ hgf x).trans (le_of_eq (geomSum_const_mul P hCm κ c hf x))
  exact ⟨C, hC, κ, hκ, hκ', fun x hx => ne_top_of_le_ne_top (ENNReal.mul_ne_top hc (hfin x hx))
    (hle x), c * M, ENNReal.mul_ne_top hc hM, fun x hx => (hle x).trans
      (mul_le_mul' le_rfl (hb x hx))⟩

/-! ### Theorems 15.3.4 (ii) and 15.3.5 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The skeleton drift from an `f`-geometrically regular set** (the proof of
Theorem 15.3.4 (ii)): for `C ∈ B⁺(X)` `f`-geometrically regular (`f ≥ 1`), with
`V = G_C^{(κ)}(·, f)`, the set `C` is `V`-geometrically regular for every `m`-skeleton, and
`V` solves (V4) for `P` with `V ≤ M` on `C`. -/
theorem skeleton_geomRegular_of_set {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X} (hC : IsFGeomRegularSet P ψ f C)
    (hψC : 0 < ψ C) :
    ∃ V : X → ℝ≥0∞, Measurable V ∧ (∀ x, f x ≤ V x) ∧ (∀ x, 1 ≤ V x) ∧
      ∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧ DriftV4 P V ρ b C ∧
      ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m
        IsFGeomRegularSet (P ^ m : Kernel X X) ψ V C := by
  obtain ⟨hpet, -, κ, hK⟩ := (theorem_15_2_1 hψ hf hf1).2 ⟨hC, hψC⟩
  obtain ⟨M, hM, hdrift, hfV, hVC⟩ := theorem_15_2_4 hf hf1 hK
  obtain ⟨hCm, hκ, -, -⟩ := hK
  have hVm := measurable_geomG P hCm κ hf
  have hV1 : ∀ x, 1 ≤ geomG P C κ f x := fun x => (hf1 x).trans (hfV x)
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hκ).ne'
  have hρ : κ⁻¹ < 1 := ENNReal.inv_lt_one.2 hκ
  have hb : κ⁻¹ * M ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hκ0) hM
  refine ⟨geomG P C κ f, hVm, hfV, hV1, κ⁻¹, κ⁻¹ * M, hρ, hb, hdrift, fun m hm => ?_⟩
  have := isMarkovKernel_pow P m
  obtain ⟨ρ', b', hρ', hb', C', hsmall, hdrift'⟩ :=
    theorem_15_3_4_i hψ hap hVm hV1 hρ hb hpet hdrift hm
  obtain ⟨hψm, -⟩ := (proposition_5_4_5_iii P hψ hap).1 m hm
  obtain ⟨k, ν, hsm⟩ := hsmall
  exact theorem_15_2_6 hψm hVm hV1 hρ' hb' ⟨_, _, proposition_5_5_3 hsm⟩ hdrift' hCm hM hVC

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.3.4 (ii)** (MT p. 382): for an aperiodic `ψ`-irreducible chain and `f ≥ 1`, an
`f`-geometrically regular `C ∈ B⁺(X)` is `f`-geometrically regular for every `m`-skeleton. -/
theorem theorem_15_3_4_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X} (hC : IsFGeomRegularSet P ψ f C)
    (hψC : 0 < ψ C) {m : ℕ} (hm : 1 ≤ m) :
    haveI := isMarkovKernel_pow P m
    IsFGeomRegularSet (P ^ m : Kernel X X) ψ f C := by
  have := isMarkovKernel_pow P m
  obtain ⟨V, -, hfV, -, -, -, -, -, -, hreg⟩ := skeleton_geomRegular_of_set hψ hap hf hf1 hC hψC
  exact (hreg m hm).mono hfV

/-- A nonzero measure has a point. -/
theorem exists_point_of_ne_zero {ψ : Measure X} (hψ : ψ ≠ 0) : Nonempty X := by
  obtain ⟨x, -⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.2 hψ)
  exact ⟨x⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The skeleton drift from an `f`-geometrically regular chain**: there is an everywhere finite
`V ≥ f` solving (V4) for `P` such that every `m`-skeleton is `V`-geometrically regular. -/
theorem skeleton_geomRegular_of_chain {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (h : IsFGeomRegularChain P f) :
    ∃ V : X → ℝ≥0∞, Measurable V ∧ (∀ x, f x ≤ V x) ∧ (∀ x, 1 ≤ V x) ∧ (∀ x, V x ≠ ∞) ∧
      ∃ C ρ b, IsPetite P C ∧ ρ < 1 ∧ b ≠ ∞ ∧ DriftV4 P V ρ b C ∧
      ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m
        IsFGeomRegularChain (P ^ m : Kernel X X) V := by
  obtain ⟨C, hC, V, hVm, hfV, hfin, ρ, b, hρ, hb, hdrift⟩ := theorem_15_3_3_converse hf hf1 h
  have hV1 : ∀ x, 1 ≤ V x := fun x => (hf1 x).trans (hfV x)
  obtain ⟨x₀⟩ := exists_point_of_ne_zero hψ.1
  refine ⟨V, hVm, hfV, hV1, hfin, C, ρ, b, hC, hρ, hb, hdrift, fun m hm => ?_⟩
  have := isMarkovKernel_pow P m
  obtain ⟨ρ', b', hρ', hb', C', hsmall, hdrift'⟩ :=
    theorem_15_3_4_i hψ hap hVm hV1 hρ hb hC hdrift hm
  obtain ⟨hψm, -⟩ := (proposition_5_4_5_iii P hψ hap).1 m hm
  obtain ⟨k, ν, hsm⟩ := hsmall
  obtain ⟨hreg, -⟩ := theorem_15_3_3 hψm hVm hV1 hρ' hb' ⟨_, _, proposition_5_5_3 hsm⟩ hdrift'
    (hfin x₀)
  have hU : {x | V x ≠ ∞} = univ := eq_univ_of_forall hfin
  rwa [hU] at hreg

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.3.5** (MT p. 383): if the chain is `f`-geometrically regular (`f ≥ 1`) and
aperiodic, every `m`-skeleton is `f`-geometrically regular. -/
theorem theorem_15_3_5 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (h : IsFGeomRegularChain P f) {m : ℕ}
    (hm : 1 ≤ m) :
    haveI := isMarkovKernel_pow P m
    IsFGeomRegularChain (P ^ m : Kernel X X) f := by
  have := isMarkovKernel_pow P m
  obtain ⟨V, -, hfV, -, -, -, -, -, -, -, -, -, hreg⟩ :=
    skeleton_geomRegular_of_chain hψ hap hf hf1 h
  exact (hreg m hm).mono hfV

/-! ### Theorems 15.3.6 and 15.3.7 -/

/-- **The skeleton gives the chain**: if `C` is `f^{(m)}`-geometrically regular for the
`m`-skeleton, it is `f`-geometrically regular for the chain (the first half of the proof of
Theorem 15.3.6). -/
theorem IsFGeomRegularSet.of_skeleton {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {f : X → ℝ≥0∞} (hf : Measurable f) {m : ℕ} (hm : 1 ≤ m) {C : Set X}
    (hC : haveI := isMarkovKernel_pow P m;
      IsFGeomRegularSet (P ^ m : Kernel X X) ψ (fSkel P m f) C) :
    IsFGeomRegularSet P ψ f C := by
  have := isMarkovKernel_pow P m
  refine ⟨hC.1, fun B hB hψB => ?_⟩
  obtain ⟨R, hR, -, M, hM, hb⟩ := hC.2 B hB hψB
  obtain ⟨r, hr, hrt, hrR⟩ := exists_one_lt_pow_le hR m
  refine ⟨r, hr, hrt, r ^ m * M, ENNReal.mul_ne_top (ENNReal.pow_ne_top hrt) hM, fun x hx => ?_⟩
  calc geomSum P B r f x ≤ r ^ m * geomSum (P ^ m : Kernel X X) B (r ^ m) (fSkel P m f) x :=
        geomSum_le_skeleton hm hB hr.le hf x
    _ ≤ r ^ m * M := mul_le_mul' le_rfl ((geomSum_mono_r _ B hrR _ x).trans (hb x hx))

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.3.6** (MT p. 383): for an aperiodic `ψ`-irreducible chain and `f ≥ 1`, a set
`C ∈ B⁺(X)` is `f`-geometrically regular iff it is `f^{(m)}`-geometrically regular for one
`m`-skeleton, iff it is for every `m`-skeleton. -/
theorem theorem_15_3_6 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X} (hψC : 0 < ψ C) :
    (IsFGeomRegularSet P ψ f C ↔ ∃ m, 1 ≤ m ∧ haveI := isMarkovKernel_pow P m;
        IsFGeomRegularSet (P ^ m : Kernel X X) ψ (fSkel P m f) C) ∧
      (IsFGeomRegularSet P ψ f C ↔ ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m;
        IsFGeomRegularSet (P ^ m : Kernel X X) ψ (fSkel P m f) C) := by
  have hevery : IsFGeomRegularSet P ψ f C → ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m;
      IsFGeomRegularSet (P ^ m : Kernel X X) ψ (fSkel P m f) C := fun hC m hm => by
    have := isMarkovKernel_pow P m
    obtain ⟨V, hVm, hfV, hV1, ρ, b, hρ, hb, hdrift, hreg⟩ :=
      skeleton_geomRegular_of_set hψ hap hf hf1 hC hψC
    exact (hreg m hm).of_le_const_mul hVm (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hb
        (ENNReal.natCast_ne_top m)⟩)) (fSkel_le_of_driftV4 hVm hV1 hfV hρ.le hC.1 hdrift m)
  exact ⟨⟨fun hC => ⟨1, le_rfl, hevery hC 1 le_rfl⟩, fun ⟨m, hm, h⟩ => h.of_skeleton hf hm⟩,
    ⟨hevery, fun h => (h 1 le_rfl).of_skeleton hf le_rfl⟩⟩

/-- **The skeleton gives the chain**, chain form (the second half of Theorem 15.3.7): if the
`m`-skeleton is `f^{(m)}`-geometrically regular, so is the chain `f`-geometrically regular. -/
theorem isFGeomRegularChain_of_skeleton {P : Kernel X X} [IsMarkovKernel P] {f : X → ℝ≥0∞}
    (hf : Measurable f) {m : ℕ} (hm : 1 ≤ m)
    (h : haveI := isMarkovKernel_pow P m;
      IsFGeomRegularChain (P ^ m : Kernel X X) (fSkel P m f)) :
    IsFGeomRegularChain P f := by
  have := isMarkovKernel_pow P m
  obtain ⟨C, hC, R, hR, -, hfin, M, hM, hb⟩ := h
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨r, hr, hrt, hrR⟩ := exists_one_lt_pow_le hR m
  have hle : ∀ x, geomSum P C r f x ≤ r ^ m *
      geomSum (P ^ m : Kernel X X) C R (fSkel P m f) x := fun x =>
    (geomSum_le_skeleton hm hCm hr.le hf x).trans (mul_le_mul' le_rfl
      (geomSum_mono_r _ C hrR _ x))
  exact ⟨C, hC.of_skeleton, r, hr, hrt, fun x hx => ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top hrt) (hfin x hx)) (hle x),
    r ^ m * M, ENNReal.mul_ne_top (ENNReal.pow_ne_top hrt) hM, fun x hx =>
      (hle x).trans (mul_le_mul' le_rfl (hb x hx))⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.3.7** (MT p. 383): for an aperiodic `ψ`-irreducible chain and `f ≥ 1`, the chain
is `f`-geometrically regular iff each `m`-skeleton is `f^{(m)}`-geometrically regular; one skeleton
suffices (`isFGeomRegularChain_of_skeleton`). -/
theorem theorem_15_3_7 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) :
    IsFGeomRegularChain P f ↔ ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m;
      IsFGeomRegularChain (P ^ m : Kernel X X) (fSkel P m f) := by
  refine ⟨fun h m hm => ?_, fun h => isFGeomRegularChain_of_skeleton hf le_rfl (h 1 le_rfl)⟩
  have := isMarkovKernel_pow P m
  obtain ⟨V, hVm, hfV, hV1, -, C, ρ, b, hC, hρ, hb, hdrift, hreg⟩ :=
    skeleton_geomRegular_of_chain hψ hap hf hf1 h
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  exact (hreg m hm).of_le_const_mul hVm (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m)
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hb
      (ENNReal.natCast_ne_top m)⟩)) (fSkel_le_of_driftV4 hVm hV1 hfV hρ.le hCm hdrift m)

end MeynTweedie.GeometricErgodicity
