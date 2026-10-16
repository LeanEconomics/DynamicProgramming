/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.ErgodicMeasures

/-!
# Existence of invariant measures under Doeblin's condition

Under Condition D for `(φ, N, ε)`, every probability measure `λ` yields an invariant probability
measure `π` with `π(A) = 1` whenever all the Cesàro averages of `λ` give `A` mass one
(`exists_invariant`). The construction is elementary.

* **A reference measure.** `ψ = Σⱼ 2^{-(j+1)} φPʲ` (`doeblinRef`) is finite, with `φ ≤ 2ψ` and
  `ψP ≤ 2ψ`, so `ψPᵐ ≤ 2ᵐψ`.
* **Uniform integrability** (`adjoint_real_le_ref`). For `μ` of mass at most one,
  `μP^{Nj}(A) ≤ b_j ψ(A) + (1 − ε)ʲ μ(S)`. Split `μPᴺ` by a Hahn set `H` for `μPᴺ − (2/ε)ψ`:
  off `H` it is below `(2/ε)ψ`, and `ψ(H) ≤ ε/2`, so Doeblin gives `μPᴺ(H) ≤ (1 − ε)μ(S)`.
  Hence the Cesàro averages are uniformly absolutely continuous with respect to `ψ`
  (`cesaro_small`).
* **The limit.** Along a non-principal ultrafilter on `ℕ`, the averages converge on every set
  (they lie in `[0, 1]`). The limit is finitely additive, and by uniform absolute continuity
  countably additive. Integrals of `[0, 1]`-valued functions converge too, by a uniform
  discretisation (`abs_integral_sub_levels_le`). The averages are nearly invariant, so the
  limit is invariant.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ]

omit [IsMarkovKernel κ] in
theorem adjointOp_kpow_zero (μ : Measure S) : adjointOp (kpow κ 0) μ = μ := by
  change μ.bind (kpow κ 0) = μ
  have : (⇑(kpow κ 0)) = fun z => Measure.dirac z := funext fun z => by
    simp [kpow, Kernel.id_apply]
  rw [this, Measure.bind_dirac]

/-! ### The reference measure -/

variable (κ) in
/-- `ψ = Σⱼ 2^{-(j+1)} φPʲ`. -/
noncomputable def doeblinRef (φ : Measure S) : Measure S :=
  Measure.sum fun j : ℕ => ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • adjointOp (kpow κ j) φ

omit [IsMarkovKernel κ] in
theorem doeblinRef_apply (φ : Measure S) {A : Set S} (hA : MeasurableSet A) :
    doeblinRef κ φ A = ∑' j : ℕ, ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ * adjointOp (kpow κ j) φ A := by
  simp [doeblinRef, Measure.sum_apply _ hA]

theorem tsum_inv_two_pow_succ : ∑' j : ℕ, ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ = 1 := by
  have : ∀ j : ℕ, ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ = 2⁻¹ * 2⁻¹ ^ j := fun j => by
    rw [← ENNReal.inv_pow, pow_succ, ENNReal.mul_inv (by simp) (by simp), mul_comm]
  simp_rw [this]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.inv_mul_cancel (by simp) (by simp)]

theorem isFinite_doeblinRef (φ : Measure S) [IsFiniteMeasure φ] :
    IsFiniteMeasure (doeblinRef κ φ) := ⟨by
  rw [doeblinRef_apply φ MeasurableSet.univ]
  simp only [adjointOp_kpow_univ]
  rw [ENNReal.tsum_mul_right, tsum_inv_two_pow_succ, one_mul]
  exact measure_lt_top φ univ⟩

omit [IsMarkovKernel κ] in
theorem le_two_doeblinRef (φ : Measure S) : φ ≤ (2 : ℝ≥0∞) • doeblinRef κ φ := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [Measure.smul_apply, doeblinRef_apply φ hA, smul_eq_mul]
  calc φ A = 2 * (((2 : ℝ≥0∞) ^ (0 + 1))⁻¹ * adjointOp (kpow κ 0) φ A) := by
        rw [adjointOp_kpow_zero, zero_add, pow_one, ← mul_assoc,
          ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
    _ ≤ _ := by gcongr; exact ENNReal.le_tsum (f := fun j : ℕ =>
        ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ * adjointOp (kpow κ j) φ A) 0

omit [IsMarkovKernel κ] in
theorem adjoint_doeblinRef_le (φ : Measure S) :
    adjointOp κ (doeblinRef κ φ) ≤ (2 : ℝ≥0∞) • doeblinRef κ φ := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [adjointOp_apply κ _ hA, Measure.smul_apply, smul_eq_mul, doeblinRef_apply φ hA,
    doeblinRef, lintegral_sum_measure]
  simp only [lintegral_smul_measure]
  have hstep : ∀ j : ℕ, ∫⁻ s, κ s A ∂adjointOp (kpow κ j) φ = adjointOp (kpow κ (j + 1)) φ A :=
    fun j => by
      rw [← adjointOp_apply κ _ hA]
      have := adjoint_add (κ := κ) 1 j φ
      rw [kpow_one, add_comm] at this
      rw [this]
  simp_rw [hstep]
  rw [← ENNReal.tsum_mul_left]
  calc ∑' j : ℕ, ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ * adjointOp (kpow κ (j + 1)) φ A
      = ∑' j : ℕ, 2 * (((2 : ℝ≥0∞) ^ (j + 1 + 1))⁻¹ * adjointOp (kpow κ (j + 1)) φ A) := by
        congr 1; funext j
        rw [← mul_assoc, pow_succ _ (j + 1), ENNReal.mul_inv (by simp) (by simp), mul_comm 2,
          mul_assoc _ 2⁻¹, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (f := Nat.succ) Nat.succ_injective
        (fun j => 2 * (((2 : ℝ≥0∞) ^ (j + 1))⁻¹ * adjointOp (kpow κ j) φ A))

omit [IsMarkovKernel κ] in
theorem adjoint_kpow_doeblinRef_le (φ : Measure S) (m : ℕ) :
    adjointOp (kpow κ m) (doeblinRef κ φ) ≤ ((2 : ℝ≥0∞) ^ m) • doeblinRef κ φ := by
  induction m with
  | zero => rw [adjointOp_kpow_zero, pow_zero, one_smul]
  | succ m ih =>
    rw [adjoint_add, kpow_one]
    calc adjointOp (kpow κ m) (adjointOp κ (doeblinRef κ φ)) ≤
          adjointOp (kpow κ m) ((2 : ℝ≥0∞) • doeblinRef κ φ) :=
          adjointOp_mono _ (adjoint_doeblinRef_le φ)
      _ = (2 : ℝ≥0∞) • adjointOp (kpow κ m) (doeblinRef κ φ) := adjointOp_smul _ _ _
      _ ≤ (2 : ℝ≥0∞) • ((2 : ℝ≥0∞) ^ m • doeblinRef κ φ) := Measure.le_iff'.2 fun A => by
          simp only [Measure.smul_apply, smul_eq_mul]
          gcongr; exact Measure.le_iff'.1 ih A
      _ = ((2 : ℝ≥0∞) ^ (m + 1)) • doeblinRef κ φ := by rw [smul_smul, pow_succ, mul_comm]

/-! ### Uniform integrability -/

omit [IsMarkovKernel κ] in
/-- Condition D forces `ε ≤ 1`. -/
theorem doeblin_eps_le_one [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) : ε ≤ 1 := by
  obtain ⟨s⟩ := ‹Nonempty S›
  have := hD.2.2.2 ∅ MeasurableSet.empty (by simp only [measureReal_empty]; exact hD.2.2.1.le) s
  simp only [measureReal_empty] at this
  linarith

/-- The constants `b_j = Σ_{i<j} (2/ε) 2^{Ni}`. -/
noncomputable def refBound (N : ℕ) (ε : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, 2 / ε * 2 ^ (N * i)

theorem refBound_nonneg {N : ℕ} {ε : ℝ} (hε : 0 < ε) (j : ℕ) : 0 ≤ refBound N ε j :=
  Finset.sum_nonneg fun i _ => by positivity

/-- **Uniform integrability.** Under Condition D, for `μ` of mass at most one,
`μP^{Nj}(A) ≤ b_j ψ(A) + (1 − ε)ʲ μ(S)`. -/
theorem adjoint_real_le_ref [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) (j : ℕ) :
    ∀ (μ : Measure S) [IsFiniteMeasure μ], μ.real univ ≤ 1 → ∀ A, MeasurableSet A →
      (adjointOp (kpow κ (N * j)) μ).real A ≤
        refBound N ε j * (doeblinRef κ φ).real A + (1 - ε) ^ j * μ.real univ := by
  have hφ := hD.1
  have hε := hD.2.2.1
  have hε1 := doeblin_eps_le_one hD
  have hψ := isFinite_doeblinRef (κ := κ) φ
  induction j with
  | zero =>
    intro μ _ _ A _
    simp only [mul_zero, adjointOp_kpow_zero, refBound, Finset.range_zero, Finset.sum_empty,
      zero_mul, pow_zero, one_mul, zero_add]
    exact measureReal_mono (subset_univ A)
  | succ j ih =>
    intro μ _ hμ A hA
    set ψ := doeblinRef κ φ
    set c : ℝ≥0∞ := ENNReal.ofReal (2 / ε)
    set ν := adjointOp (kpow κ N) μ
    have hν : IsFiniteMeasure ν := isFinite_adjoint N μ
    have hνu : ν.real univ = μ.real univ := by
      rw [measureReal_def, adjointOp_kpow_univ]; rfl
    have hcψfin : IsFiniteMeasure (c • ψ) := ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ψ univ)⟩
    obtain ⟨H, hH, hH1, hH2⟩ := hahn_decomposition ν (c • ψ)
    -- `ψ(H) ≤ ε/2`, hence `φ(H) ≤ ε` and `ν(H) ≤ (1 − ε) μ(S)`
    have hcψ : (2 / ε) * ψ.real H ≤ 1 := by
      have h1 := hH1 H hH subset_rfl
      have h2 : (c • ψ).real H ≤ ν.real H := ENNReal.toReal_mono (measure_ne_top _ _) h1
      rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (by positivity)] at h2
      linarith [measureReal_mono (μ := ν) (subset_univ H)]
    have hφH : φ.real H ≤ ε := by
      have h1 : φ.real H ≤ ((2 : ℝ≥0∞) • ψ).real H :=
        ENNReal.toReal_mono (by
          rw [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_ne_top (by simp) (measure_ne_top ψ H)) (le_two_doeblinRef φ H)
      rw [measureReal_ennreal_smul_apply] at h1
      have : (2 : ℝ≥0∞).toReal = 2 := by simp
      rw [this] at h1
      have h2 : ψ.real H ≤ ε / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hε] at hcψ; linarith
      linarith
    have hνH : ν.real H ≤ (1 - ε) * μ.real univ := by
      have := isMarkov_kpow (κ := κ) N
      rw [bind_real_eq _ _ hH]
      calc ∫ s, (kpow κ N s).real H ∂μ ≤ ∫ _s, (1 - ε) ∂μ :=
            integral_mono (integrable_of_abs_le μ (Kernel.measurable_coe _ hH).ennreal_toReal
              (C := 1) fun s => by
                rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
              (integrable_const _) fun s => hD.2.2.2 H hH hφH s
        _ = (1 - ε) * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
    -- the two pieces
    set R := ν.restrict H
    set K := ν.restrict Hᶜ
    have hsplit : ν = R + K := (Measure.restrict_add_restrict_compl hH).symm
    have hK : K ≤ c • ψ := Measure.le_iff.2 fun t ht => by
      rw [Measure.restrict_apply ht]
      exact (hH2 _ (ht.inter hH.compl) inter_subset_right).trans
        (measure_mono inter_subset_left)
    have hRu : R.real univ = ν.real H := by
      rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter]
    have hKbound : (adjointOp (kpow κ (N * j)) K).real A ≤
        2 / ε * 2 ^ (N * j) * ψ.real A := by
      have h1 : adjointOp (kpow κ (N * j)) K ≤ (c * 2 ^ (N * j)) • ψ := by
        calc adjointOp (kpow κ (N * j)) K ≤ adjointOp (kpow κ (N * j)) (c • ψ) :=
              adjointOp_mono _ hK
          _ = c • adjointOp (kpow κ (N * j)) ψ := adjointOp_smul _ _ _
          _ ≤ c • ((2 : ℝ≥0∞) ^ (N * j) • ψ) := Measure.le_iff'.2 fun B => by
              simp only [Measure.smul_apply, smul_eq_mul]
              gcongr; exact Measure.le_iff'.1 (adjoint_kpow_doeblinRef_le φ (N * j)) B
          _ = (c * 2 ^ (N * j)) • ψ := smul_smul _ _ _
      have h2 := ENNReal.toReal_mono (by
          rw [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))
            (measure_ne_top ψ A))
        (Measure.le_iff'.1 h1 A)
      have hfin : IsFiniteMeasure (adjointOp (kpow κ (N * j)) K) := isFinite_adjoint _ K
      rw [← measureReal_def, ← measureReal_def, measureReal_ennreal_smul_apply,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
      simpa using h2
    have hRbound := ih R (by rw [hRu]; linarith [measureReal_mono (μ := ν) (subset_univ H)]) A hA
    rw [show N * (j + 1) = N * j + N by ring, adjoint_add]
    change (adjointOp (kpow κ (N * j)) ν).real A ≤ _
    have : IsFiniteMeasure (adjointOp (kpow κ (N * j)) R) := isFinite_adjoint _ R
    have : IsFiniteMeasure (adjointOp (kpow κ (N * j)) K) := isFinite_adjoint _ K
    rw [hsplit, adjointOp_add, measureReal_add_apply (h₁ := measure_ne_top _ _)
      (h₂ := measure_ne_top _ _)]
    have hpow : 0 ≤ (1 - ε) ^ j := pow_nonneg (by linarith) j
    have : (1 - ε) ^ j * R.real univ ≤ (1 - ε) ^ (j + 1) * μ.real univ := by
      rw [hRu, pow_succ, mul_assoc]; exact mul_le_mul_of_nonneg_left hνH hpow
    simp only [refBound, Finset.sum_range_succ] at hRbound ⊢
    nlinarith [measureReal_nonneg (μ := ψ) (s := A)]

/-- The Cesàro averages are uniformly absolutely continuous with respect to `ψ`. -/
theorem cesaro_small [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (μ : Measure S) [IsProbabilityMeasure μ] {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ n₀, ∀ n ≥ n₀, ∀ A, MeasurableSet A → (doeblinRef κ φ).real A ≤ δ →
      (cesaroM κ n μ).real A ≤ η := by
  have hε := hD.2.2.1
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < η / 3)
    (by linarith : 1 - ε < 1)
  set b := refBound N ε j
  have hb := refBound_nonneg (N := N) hε j
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (3 * (N * j) / η)
  refine ⟨η / 3 / (b + 1), by positivity, n₀, fun n hn A hA hψA => ?_⟩
  have hterm : ∀ k, (adjointOp (kpow κ (k + 1)) μ).real A ≤
      2 * η / 3 + if k + 1 < N * j then 1 else 0 := fun k => by
    split_ifs with hk
    · have := isProb_adjoint (κ := κ) (k + 1) μ
      have : (adjointOp (kpow κ (k + 1)) μ).real A ≤ 1 := measureReal_le_one
      linarith
    · obtain ⟨m, hm⟩ : ∃ m, k + 1 = N * j + m := ⟨k + 1 - N * j, by omega⟩
      have := isProb_adjoint (κ := κ) m μ
      rw [hm, adjoint_add]
      have h1 := adjoint_real_le_ref hD j (adjointOp (kpow κ m) μ) (by simp) A hA
      simp only [probReal_univ, mul_one] at h1
      have h2 : b * (doeblinRef κ φ).real A ≤ η / 3 := by
        calc b * (doeblinRef κ φ).real A ≤ (b + 1) * (η / 3 / (b + 1)) :=
              mul_le_mul (by linarith) hψA measureReal_nonneg (by positivity)
          _ = η / 3 := by
              have hb1 : b + 1 ≠ 0 := by positivity
              field_simp
      linarith
  rw [cesaroM_real]
  have hsum : ∑ k ∈ Finset.range (n + 1), (adjointOp (kpow κ (k + 1)) μ).real A ≤
      (n + 1) * (2 * η / 3) + N * j := by
    calc ∑ k ∈ Finset.range (n + 1), (adjointOp (kpow κ (k + 1)) μ).real A ≤
          ∑ k ∈ Finset.range (n + 1), (2 * η / 3 + if k + 1 < N * j then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = (n + 1) * (2 * η / 3) + ∑ k ∈ Finset.range (n + 1),
            (if k + 1 < N * j then (1 : ℝ) else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
      _ ≤ (n + 1) * (2 * η / 3) + N * j := by
          gcongr
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_one]
          have : ((Finset.range (n + 1)).filter fun k => k + 1 < N * j) ⊆
              Finset.range (N * j) := fun k hk => by
            simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; omega
          have := Finset.card_le_card this
          rw [Finset.card_range] at this
          exact_mod_cast this
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hNj : (N : ℝ) * j ≤ η / 3 * (n + 1) := by
    have := (div_lt_iff₀ hη).1 hn₀
    nlinarith
  calc ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), (adjointOp (kpow κ (k + 1)) μ).real A ≤
        ((n : ℝ) + 1)⁻¹ * ((n + 1) * (2 * η / 3) + N * j) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((n : ℝ) + 1)⁻¹ * ((n + 1) * (2 * η / 3) + η / 3 * (n + 1)) := by gcongr
    _ = η := by field_simp; ring

/-! ### Discretising integrals -/

omit [MeasurableSpace S] in
/-- `|g(s) − (1/k) #{i < k : (i+1)/k < g(s)}| ≤ 1/k` for `0 ≤ g(s) ≤ 1`. -/
theorem abs_sub_levels_le {g : S → ℝ} {k : ℕ} (hk : 0 < k) (s : S) (h0 : 0 ≤ g s)
    (h1 : g s ≤ 1) :
    |g s - (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
      {x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ) s| ≤ (k : ℝ)⁻¹ := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set x := (k : ℝ) * g s
  have hx0 : 0 ≤ x := by positivity
  have hxk : x ≤ k := by
    calc x ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 hk'.le
      _ = k := mul_one _
  set m := ⌈x⌉₊
  have hmk : m ≤ k := Nat.ceil_le.2 hxk
  have hcount : ∑ i ∈ Finset.range k, {x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ) s =
      ((m - 1 : ℕ) : ℝ) := by
    have hfilt : (Finset.range k).filter (fun i : ℕ => ((i : ℝ) + 1) / k < g s) =
        Finset.range (m - 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      rw [div_lt_iff₀ hk', mul_comm]
      have : ((i : ℝ) + 1 < x) ↔ i + 1 < m := by
        rw [Nat.lt_ceil]; push_cast; rfl
      rw [this]
      omega
    rw [← Finset.card_range (m - 1), ← hfilt, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ((i : ℝ) + 1) / k < g s
    · simp only [indicator_of_mem (show s ∈ {x | ((i : ℝ) + 1) / k < g x} from hi), hi,
        ↓reduceIte, Pi.one_apply]
    · simp only [indicator_of_notMem (show s ∉ {x | ((i : ℝ) + 1) / k < g x} from hi), hi,
        ↓reduceIte]
  rw [hcount]
  have hxm : x ≤ m := Nat.le_ceil x
  have hmx : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have key : |x - ((m - 1 : ℕ) : ℝ)| ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm] at hxm ⊢
      simp only [Nat.zero_sub, sub_zero, CharP.cast_eq_zero] at hxm ⊢
      rw [abs_of_nonneg hx0]; linarith
    · rw [Nat.cast_sub hm, Nat.cast_one, abs_le]
      constructor <;> linarith
  have : g s - (k : ℝ)⁻¹ * ((m - 1 : ℕ) : ℝ) = (k : ℝ)⁻¹ * (x - ((m - 1 : ℕ) : ℝ)) := by
    simp only [x]; field_simp
  rw [this, abs_mul, abs_of_pos (inv_pos.2 hk')]
  exact (mul_le_mul_of_nonneg_left key (inv_pos.2 hk').le).trans (le_of_eq (mul_one _))

/-- `|∫ g dμ − (1/k) Σ_{i<k} μ{(i+1)/k < g}| ≤ 1/k` for `0 ≤ g ≤ 1` and a probability `μ`. -/
theorem abs_integral_sub_levels_le (μ : Measure S) [IsProbabilityMeasure μ] {g : S → ℝ}
    (hg : Measurable g) (h01 : ∀ s, 0 ≤ g s ∧ g s ≤ 1) {k : ℕ} (hk : 0 < k) :
    |∫ s, g s ∂μ - (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, μ.real {x | ((i : ℝ) + 1) / k < g x}| ≤
      (k : ℝ)⁻¹ := by
  have hmeas : ∀ i : ℕ, MeasurableSet {x | ((i : ℝ) + 1) / k < g x} := fun i =>
    measurableSet_lt measurable_const hg
  have hint : ∀ i : ℕ, Integrable ({x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ)) μ :=
    fun i => (integrable_const 1).indicator (hmeas i)
  have hD : ∫ s, (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
      {x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ) s ∂μ =
        (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, μ.real {x | ((i : ℝ) + 1) / k < g x} := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]
    simp only [integral_indicator_one (hmeas _)]
  have hgi : Integrable g μ := integrable_of_abs_le μ hg (C := 1) fun s => by
    rw [abs_of_nonneg (h01 s).1]; exact (h01 s).2
  have hDi : Integrable (fun s => (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
      {x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ) s) μ :=
    (integrable_finsetSum _ fun i _ => hint i).const_mul _
  rw [← hD, ← integral_sub hgi hDi]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ s, |g s - (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
        {x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ) s| ∂μ ≤ ∫ _s, (k : ℝ)⁻¹ ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _)
          (integrable_const _) (Eventually.of_forall fun s =>
            abs_sub_levels_le hk s (h01 s).1 (h01 s).2)
    _ = (k : ℝ)⁻¹ := by simp

/-! ### The ultrafilter limit -/

theorem hyperfilter_le_atTop : (hyperfilter ℕ : Filter ℕ) ≤ atTop :=
  hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le

variable (κ) in
/-- The limit of the Cesàro averages on `A` along a non-principal ultrafilter. -/
noncomputable def cesaroLim (μ : Measure S) (A : Set S) : ℝ :=
  limUnder (hyperfilter ℕ : Filter ℕ) fun n => (cesaroM κ n μ).real A

/-- Bounded sequences converge along an ultrafilter. -/
theorem tendsto_ultra_of_mem {u : ℕ → ℝ} (hu : ∀ n, u n ∈ Icc (0 : ℝ) 1) :
    Tendsto u (hyperfilter ℕ) (𝓝 (limUnder (hyperfilter ℕ : Filter ℕ) u)) := by
  refine tendsto_nhds_limUnder ?_
  obtain ⟨x, -, hx⟩ := isCompact_iff_ultrafilter_le_nhds.1 isCompact_Icc
    ((hyperfilter ℕ).map u) (by
      rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
      exact Filter.univ_mem' fun n => hu n)
  exact ⟨x, by rwa [Ultrafilter.coe_map] at hx⟩

theorem tendsto_cesaroLim (μ : Measure S) [IsProbabilityMeasure μ] (A : Set S) :
    Tendsto (fun n => (cesaroM κ n μ).real A) (hyperfilter ℕ) (𝓝 (cesaroLim κ μ A)) :=
  tendsto_ultra_of_mem fun n => by
    have := isProb_cesaroM (κ := κ) n μ
    exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- Sequences tending to a limit at infinity tend to it along the ultrafilter. -/
theorem tendsto_ultra {u : ℕ → ℝ} {a : ℝ} (h : Tendsto u atTop (𝓝 a)) :
    Tendsto u (hyperfilter ℕ) (𝓝 a) := h.mono_left hyperfilter_le_atTop

theorem cesaroLim_union (μ : Measure S) [IsProbabilityMeasure μ] {A B : Set S}
    (hd : Disjoint A B) (hB : MeasurableSet B) :
    cesaroLim κ μ (A ∪ B) = cesaroLim κ μ A + cesaroLim κ μ B := by
  refine tendsto_nhds_unique (tendsto_cesaroLim μ (A ∪ B)) ?_
  have := (tendsto_cesaroLim (κ := κ) μ A).add (tendsto_cesaroLim (κ := κ) μ B)
  refine this.congr fun n => ?_
  have := isProb_cesaroM (κ := κ) n μ
  exact (measureReal_union hd hB).symm

theorem cesaroLim_nonneg (μ : Measure S) [IsProbabilityMeasure μ] (A : Set S) :
    0 ≤ cesaroLim κ μ A :=
  ge_of_tendsto (tendsto_cesaroLim μ A) (Eventually.of_forall fun _ => measureReal_nonneg)

theorem cesaroLim_univ (μ : Measure S) [IsProbabilityMeasure μ] : cesaroLim κ μ univ = 1 := by
  refine tendsto_nhds_unique (tendsto_cesaroLim μ univ) ?_
  refine tendsto_const_nhds.congr fun n => ?_
  have := isProb_cesaroM (κ := κ) n μ
  exact probReal_univ.symm

theorem cesaroLim_empty (μ : Measure S) [IsProbabilityMeasure μ] : cesaroLim κ μ ∅ = 0 := by
  refine tendsto_nhds_unique (tendsto_cesaroLim μ ∅) ?_
  exact tendsto_const_nhds.congr fun _ => by simp

/-- The limit is countably additive, by uniform absolute continuity. -/
theorem hasSum_cesaroLim [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (μ : Measure S) [IsProbabilityMeasure μ] {f : ℕ → Set S} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Function.onFun Disjoint f)) :
    HasSum (fun i => cesaroLim κ μ (f i)) (cesaroLim κ μ (⋃ i, f i)) := by
  have hφ := hD.1
  have hψ := isFinite_doeblinRef (κ := κ) φ
  set P : ℕ → Set S := fun n => ⋃ i ∈ Finset.range n, f i
  have hPm : ∀ n, MeasurableSet (P n) := fun n =>
    Finset.measurableSet_biUnion _ fun i _ => hf i
  have hPsum : ∀ n, cesaroLim κ μ (P n) = ∑ i ∈ Finset.range n, cesaroLim κ μ (f i) := by
    intro n
    refine tendsto_nhds_unique (tendsto_cesaroLim μ (P n)) ?_
    refine (tendsto_finsetSum _ fun i _ => tendsto_cesaroLim (κ := κ) μ (f i)).congr fun m => ?_
    have := isProb_cesaroM (κ := κ) m μ
    exact (measureReal_biUnion_finset (fun i _ j _ hij => hd hij) fun i _ => hf i).symm
  set T : ℕ → Set S := fun n => (⋃ i, f i) \ P n
  have hTsplit : ∀ n, cesaroLim κ μ (⋃ i, f i) = cesaroLim κ μ (P n) + cesaroLim κ μ (T n) := by
    intro n
    rw [← cesaroLim_union μ disjoint_sdiff_right ((MeasurableSet.iUnion hf).diff (hPm n))]
    congr 1
    exact (union_sdiff_cancel (iUnion₂_subset fun i _ => subset_iUnion f i)).symm
  -- `ψ(Tₙ) → 0`
  have hPmono : Monotone P := fun m n hmn => biUnion_subset_biUnion_left fun i hi => by
    simp only [Finset.coe_range, mem_Iio] at hi ⊢; omega
  have hPU : (⋃ n, P n) = ⋃ i, f i := by
    ext x; simp only [P, mem_iUnion, Finset.mem_range]
    exact ⟨fun ⟨n, i, _, hx⟩ => ⟨i, hx⟩, fun ⟨i, hx⟩ => ⟨i + 1, i, by omega, hx⟩⟩
  have hψT : Tendsto (fun n => (doeblinRef κ φ).real (T n)) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := doeblinRef κ φ) hPmono
    rw [hPU] at h1
    have h2 := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
    have h3 := h2.const_sub ((doeblinRef κ φ).real (⋃ i, f i))
    rw [show ((doeblinRef κ φ) (⋃ i, f i)).toReal = (doeblinRef κ φ).real (⋃ i, f i) from rfl,
      sub_self] at h3
    refine h3.congr fun n => ?_
    simp only [Function.comp_apply, T]
    rw [measureReal_sdiff (iUnion₂_subset fun i _ => subset_iUnion f i) (hPm n)]
    rfl
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => cesaroLim_nonneg μ _)]
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, n₀, hsmall⟩ := cesaro_small hD μ (half_pos hη)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((hψT.eventually (gt_mem_nhds hδ)))
  refine ⟨N₁, fun n hn => ?_⟩
  have hTle : cesaroLim κ μ (T n) ≤ η / 2 := by
    refine le_of_tendsto (tendsto_cesaroLim μ (T n)) ?_
    refine (Filter.eventually_ge_atTop n₀).filter_mono hyperfilter_le_atTop |>.mono fun m hm => ?_
    exact hsmall m hm (T n) ((MeasurableSet.iUnion hf).diff (hPm n)) (hN₁ n hn).le
  rw [Real.dist_eq, ← hPsum, hTsplit n]
  rw [abs_sub_comm, add_sub_cancel_left, abs_of_nonneg (cesaroLim_nonneg μ _)]
  linarith

omit [IsMarkovKernel κ] in
/-- `T*` commutes with the Cesàro averages. -/
theorem adjoint_cesaroM (n : ℕ) (μ : Measure S) :
    adjointOp κ (cesaroM κ n μ) = cesaroM κ n (adjointOp (kpow κ 1) μ) := by
  simp only [cesaroM, adjointOp_smul, adjointOp_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := adjoint_add (κ := κ) 1 (k + 1) μ
  have h2 := adjoint_add (κ := κ) (k + 1) 1 μ
  rw [kpow_one] at h1
  rw [← h1, ← h2, add_comm]

/-- Integrals of `[0, 1]`-valued functions converge along the ultrafilter. -/
theorem tendsto_integral_ultra (μ : Measure S) [IsProbabilityMeasure μ] {π : Measure S}
    [IsProbabilityMeasure π] (hπ : ∀ A, MeasurableSet A → π.real A = cesaroLim κ μ A)
    {g : S → ℝ} (hg : Measurable g) (h01 : ∀ s, 0 ≤ g s ∧ g s ≤ 1) :
    Tendsto (fun n => ∫ s, g s ∂cesaroM κ n μ) (hyperfilter ℕ) (𝓝 (∫ s, g s ∂π)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨k, hk⟩ := exists_nat_gt (3 / η)
  have hk0 : 0 < k := by
    have : (0 : ℝ) < k := lt_trans (by positivity) hk
    exact_mod_cast this
  have hkη : 3 * (k : ℝ)⁻¹ < η := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    rw [div_lt_iff₀ hη] at hk
    rw [← div_eq_mul_inv, div_lt_iff₀ hk']; linarith
  set G : ℕ → Set S := fun i => {x | ((i : ℝ) + 1) / k < g x}
  have hG : ∀ i, MeasurableSet (G i) := fun i => measurableSet_lt measurable_const hg
  have happrox : Tendsto (fun n => (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (cesaroM κ n μ).real (G i))
      (hyperfilter ℕ) (𝓝 ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, π.real (G i))) := by
    simp only [fun i => hπ (G i) (hG i)]
    exact (tendsto_finsetSum _ fun i _ => tendsto_cesaroLim μ (G i)).const_mul _
  filter_upwards [happrox.eventually (Metric.ball_mem_nhds _ (inv_pos.2
    (show (0 : ℝ) < k by exact_mod_cast hk0)))] with n hn
  have := isProb_cesaroM (κ := κ) n μ
  have e1 := abs_integral_sub_levels_le (cesaroM κ n μ) hg h01 hk0
  have e2 := abs_integral_sub_levels_le π hg h01 hk0
  rw [Real.dist_eq] at hn
  rw [Real.dist_eq]
  calc |∫ s, g s ∂cesaroM κ n μ - ∫ s, g s ∂π| ≤ (k : ℝ)⁻¹ + (k : ℝ)⁻¹ + (k : ℝ)⁻¹ := by
        rw [abs_le] at e1 e2 ⊢
        rw [abs_lt] at hn
        constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hn.1, hn.2]
    _ < η := by linarith

/-- **Existence of invariant measures under Condition D.** Every probability measure `λ` yields
an invariant probability measure `π`, the limit of its Cesàro averages along a non-principal
ultrafilter on each measurable set. -/
theorem exists_invariant [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (μ : Measure S) [IsProbabilityMeasure μ] :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ adjointOp κ π = π ∧
      ∀ A, MeasurableSet A → π.real A = cesaroLim κ μ A := by
  set π : Measure S := Measure.ofMeasurable (fun A _ => ENNReal.ofReal (cesaroLim κ μ A))
    (by simp [cesaroLim_empty]) fun f hf hd => by
      have h := hasSum_cesaroLim hD μ hf hd
      rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => cesaroLim_nonneg μ _) h.summable]
  have hπA : ∀ A, MeasurableSet A → π A = ENNReal.ofReal (cesaroLim κ μ A) := fun A hA =>
    Measure.ofMeasurable_apply A hA
  have hprob : IsProbabilityMeasure π :=
    ⟨by rw [hπA univ MeasurableSet.univ, cesaroLim_univ, ENNReal.ofReal_one]⟩
  have hπr : ∀ A, MeasurableSet A → π.real A = cesaroLim κ μ A := fun A hA => by
    rw [measureReal_def, hπA A hA, ENNReal.toReal_ofReal (cesaroLim_nonneg μ A)]
  refine ⟨π, hprob, ?_, hπr⟩
  have hPfin : IsFiniteMeasure (adjointOp κ π) := by
    have := isFinite_adjoint (κ := κ) 1 π; rwa [kpow_one] at this
  refine Measure.ext fun A hA => ?_
  have hreal : (adjointOp κ π).real A = π.real A := by
    set g : S → ℝ := fun s => (κ s).real A
    have hg : Measurable g := (κ.measurable_coe hA).ennreal_toReal
    have h01 : ∀ s, 0 ≤ g s ∧ g s ≤ 1 := fun s => ⟨measureReal_nonneg, measureReal_le_one⟩
    rw [bind_real_eq κ π hA, hπr A hA]
    refine tendsto_nhds_unique (tendsto_integral_ultra μ hπr hg h01) ?_
    -- `∫ g dλₙ = (T*λₙ)(A)`, within `1/(n+1)` of `λₙ(A)`
    have hsh : Tendsto (fun n => (cesaroM κ n (adjointOp (kpow κ 1) μ)).real A -
        (cesaroM κ n μ).real A) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat)
      rw [Real.norm_eq_abs]
      refine (abs_cesaro_shift_le n 1 μ A).trans (le_of_eq ?_)
      simp [div_eq_mul_inv]
    have := (tendsto_ultra hsh).add (tendsto_cesaroLim (κ := κ) μ A)
    rw [zero_add] at this
    refine this.congr fun n => ?_
    have := isFinite_cesaroM (κ := κ) n μ
    rw [sub_add_cancel, ← adjoint_cesaroM, bind_real_eq κ _ hA]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hreal

end StokeyLucasPrescott.StrongConvergence
