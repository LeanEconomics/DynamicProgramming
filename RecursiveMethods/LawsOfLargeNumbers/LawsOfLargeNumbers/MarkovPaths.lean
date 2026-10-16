/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LawsOfLargeNumbers.MartingaleLaw
import LawsOfLargeNumbers.MarkovOperator

/-!
# Sample paths of a Markov process: Lemma 14.8

SLP §14.2, pp. 415–416 and 425–430. Paths are `ω : ℕ → S` with `ω 0 = s₀`; the book's
`ω = (s₁, s₂, …)` and `σₙ(ω) = sₙ` are the coordinates `n ≥ 1`. The law `μ(s₀, ·)` of the path
(§8.2) is `pathM Q s₀`, built by the Ionescu-Tulcea theorem (Mathlib's `Kernel.traj`).

* `markov_property`: `E[h(σ_{t+1}) | σ₀, …, σ_t] = (Th)(σ_t)` a.s. for bounded measurable `h`.
  The book uses it without citation in the proof of Lemma 14.8.
* `law_coord` (p. 415): the law of `σₙ` is `λₙ = T*ⁿδ_{s₀}`. Hence display (2) of p. 415,
  `E f(σₙ) = ∫ f dλₙ` (`intro_2`).
* **Lemma 14.8** (`lemma_14_8`, p. 427): for bounded measurable `f` and `m ≥ 1`,
  `(1/N) Σ_{n=m+1}^N [f(σₙ) − (Tᵐf)(σ_{n−m})] → 0` a.s. The proof is the book's. It telescopes over
  `j < m` into the differences `(Tʲf)(σ_{k+1}) − (T^{j+1}f)(σ_k)`. These are martingale differences
  for the filtration of the path (`Filtration.piLE`), so Theorem 14.6 applies (`mg_avg_tendsto`).

**Corrections.**
* Lemma 14.8 is stated for an *arbitrary* probability measure `μ` on `S^∞`. That is false
  (`lemma_14_8_counterexample`): on `S = {0, 1}` with `P(s, ·)` uniform, `μ = δ_{(0, 0, …)}` and
  `f = 1_{1}`, the averages tend to `−1/2`. The lemma holds for `μ = μ(s₀, ·)`, the only case used.
* The book writes the conditional-expectation identities in the proof "for all `ω`"; they hold
  a.s. `𝓕̂⁰` is undefined in §8.2 (the trivial σ-algebra is meant). Here the filtration includes
  the coordinate `σ₀ = s₀`, which is a.s. constant.
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {S : Type*} [MeasurableSpace S]

/-! ### The path measure and the Markov property -/

/-- The kernels `(s₀, …, sₙ) ↦ P(sₙ, ·)` that drive the path. -/
noncomputable def trajKernel (Q : Kernel S S) (n : ℕ) : Kernel (Π _ : Finset.Iic n, S) S :=
  Q.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

theorem isMarkovKernel_trajKernel (Q : Kernel S S) [IsMarkovKernel Q] (n : ℕ) :
    IsMarkovKernel (trajKernel Q n) := by
  unfold trajKernel
  infer_instance

/-- The law `μ(s₀, ·)` of the path `(s₀, s₁, s₂, …)` of the Markov process with transition `P`
started at `s₀` (SLP §8.2). -/
noncomputable def pathM (Q : Kernel S S) [IsMarkovKernel Q] (s₀ : S) : Measure (ℕ → S) :=
  @Kernel.traj (fun _ => S) _ (trajKernel Q) (isMarkovKernel_trajKernel Q) 0 (fun _ => s₀)

theorem isProbabilityMeasure_pathM (Q : Kernel S S) [IsMarkovKernel Q] (s₀ : S) :
    IsProbabilityMeasure (pathM Q s₀) := by
  have := isMarkovKernel_trajKernel Q
  unfold pathM
  infer_instance

/-- The `k`-th coordinate is measurable for the σ-algebra of the coordinates `0, …, k`. -/
theorem measurable_coord_piLE (k : ℕ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => S) k] fun ω : ℕ → S => ω k :=
  fun s hs => ⟨(fun x : Π _ : Set.Iic k, S => x ⟨k, Set.mem_Iic.2 le_rfl⟩) ⁻¹' s,
    measurable_pi_apply _ hs, rfl⟩

/-- **The Markov property.** For bounded measurable `h`,
`E[h(σ_{t+1}) | σ₀, …, σ_t] = (Th)(σ_t)`, `μ(s₀, ·)`-a.s. -/
theorem markov_property (Q : Kernel S S) [IsMarkovKernel Q] (s₀ : S) {h : S → ℝ}
    (hh : Measurable h) {B : ℝ} (hB : ∀ s, |h s| ≤ B) (t : ℕ) :
    (pathM Q s₀)[fun ω => h (ω (t + 1)) | Filtration.piLE (X := fun _ : ℕ => S) t]
      =ᵐ[pathM Q s₀] fun ω => markovOpR Q h (ω t) := by
  have := isMarkovKernel_trajKernel Q
  have := isProbabilityMeasure_pathM Q s₀
  have hint : Integrable (fun ω : ℕ → S => h (ω (t + 1))) (pathM Q s₀) :=
    integrable_of_bounded (hh.comp (measurable_pi_apply _)) fun ω => hB _
  have hce := Kernel.condExp_traj (X := fun _ => S) (κ := trajKernel Q) (Nat.zero_le t)
    (x₀ := fun _ => s₀) hint
  refine hce.trans (Eventually.of_forall fun ω => ?_)
  change ∫ y, h (y (t + 1)) ∂(Kernel.traj (trajKernel Q) t) (Preorder.frestrictLe t ω) =
    markovOpR Q h (ω t)
  rw [← integral_map (φ := fun y : ℕ → S => y (t + 1)) (f := h)
    (measurable_pi_apply (t + 1)).aemeasurable hh.aestronglyMeasurable,
    ← Kernel.map_apply _ (measurable_pi_apply _), Kernel.map_traj_succ_self]
  rfl

theorem pathM_map_zero (Q : Kernel S S) [IsMarkovKernel Q] (s₀ : S) :
    (pathM Q s₀).map (fun ω => ω 0) = Measure.dirac s₀ := by
  have := isMarkovKernel_trajKernel Q
  have hg : Measurable fun x : Π _ : Finset.Iic 0, S => x ⟨0, Finset.mem_Iic.2 le_rfl⟩ :=
    measurable_pi_apply _
  have hfr := Preorder.measurable_frestrictLe (X := fun _ : ℕ => S) 0
  have h1 := Kernel.traj_map_frestrictLe (X := fun _ => S) (κ := trajKernel Q) 0 0
  rw [Kernel.partialTraj_self] at h1
  have h3 := congrArg (fun η => (η (fun _ : Finset.Iic 0 => s₀)).map
    (fun x : Π _ : Finset.Iic 0, S => x ⟨0, Finset.mem_Iic.2 le_rfl⟩)) h1
  simp only [Kernel.map_apply _ hfr, Kernel.id_apply, Measure.map_dirac' hg,
    Measure.map_map hg hfr] at h3
  exact h3

theorem measure_eq_of_real {μ ν : Measure S} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ A, MeasurableSet A → μ.real A = ν.real A) : μ = ν :=
  Measure.ext fun A hA =>
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (h A hA)

/-- The law of `σₙ` under `μ(s₀, ·)` is `λₙ = T*ⁿδ_{s₀}` (p. 415). -/
theorem law_coord (Q : Kernel S S) [IsMarkovKernel Q] (s₀ : S) (n : ℕ) :
    (pathM Q s₀).map (fun ω => ω n) = (adjointOp Q)^[n] (Measure.dirac s₀) := by
  have hP := isProbabilityMeasure_pathM Q s₀
  induction n with
  | zero => exact pathM_map_zero Q s₀
  | succ n ih =>
    have hprob : IsProbabilityMeasure ((adjointOp Q)^[n] (Measure.dirac s₀)) := by
      rw [← ih]; infer_instance
    have : IsProbabilityMeasure (adjointOp Q ((adjointOp Q)^[n] (Measure.dirac s₀))) :=
      (theorem_8_2 Q _).1
    rw [Function.iterate_succ_apply']
    refine measure_eq_of_real fun A hA => ?_
    set h : S → ℝ := A.indicator 1
    have hh : Measurable h := measurable_one.indicator hA
    have hB : ∀ s, |h s| ≤ 1 := fun s => by
      by_cases hs : s ∈ A <;> simp [h, hs]
    have hmn : Measurable fun ω : ℕ → S => ω n := measurable_pi_apply n
    have hmn1 : Measurable fun ω : ℕ → S => ω (n + 1) := measurable_pi_apply (n + 1)
    have hle := (Filtration.piLE (X := fun _ : ℕ => S)).le n
    calc ((pathM Q s₀).map fun ω => ω (n + 1)).real A
        = ∫ ω, h (ω (n + 1)) ∂pathM Q s₀ := by
          rw [← integral_indicator_one hA,
            integral_map hmn1.aemeasurable (hh.aestronglyMeasurable)]
      _ = ∫ ω, ((pathM Q s₀)[fun ω => h (ω (n + 1)) |
            Filtration.piLE (X := fun _ : ℕ => S) n]) ω ∂pathM Q s₀ :=
          (integral_condExp hle).symm
      _ = ∫ ω, markovOpR Q h (ω n) ∂pathM Q s₀ :=
          integral_congr_ae (markov_property Q s₀ hh hB n)
      _ = ∫ s, markovOpR Q h s ∂(adjointOp Q)^[n] (Measure.dirac s₀) := by
          rw [← ih, integral_map hmn.aemeasurable
            (theorem_8_1_cor Q hh hB).1.aestronglyMeasurable]
      _ = ∫ s, h s ∂adjointOp Q ((adjointOp Q)^[n] (Measure.dirac s₀)) :=
          theorem_8_3_cor Q _ hh hB
      _ = _ := integral_indicator_one hA

/-- Display (2) of p. 415: `E f(σₙ) = ∫ f dλₙ`, `λₙ = T*ⁿδ_{s₀}`. -/
theorem intro_2 (Q : Kernel S S) [IsMarkovKernel Q] (s₀ : S) {f : S → ℝ} (hf : Measurable f)
    (n : ℕ) :
    ∫ ω, f (ω n) ∂pathM Q s₀ = ∫ s, f s ∂(adjointOp Q)^[n] (Measure.dirac s₀) := by
  rw [← law_coord Q s₀ n, integral_map (measurable_pi_apply n).aemeasurable
    hf.aestronglyMeasurable]

/-! ### Cesàro averages of real sequences -/

/-- If `(1/N) uₙ → L` and `|v_N − u_N| ≤ C`, then `(1/N) v_N → L`. -/
theorem tendsto_avg_of_bounded_diff {u v : ℕ → ℝ} {L C : ℝ}
    (hu : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * u N) atTop (𝓝 L)) (hC : ∀ N, |v N - u N| ≤ C) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * v N) atTop (𝓝 L) := by
  have herr : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (v N - u N)) atTop (𝓝 0) := by
    have hb : ∀ N : ℕ, ‖(N : ℝ)⁻¹ * (v N - u N)‖ ≤ C * (N : ℝ)⁻¹ := fun N => by
      rw [Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC N) (inv_nonneg.2 (Nat.cast_nonneg N))
    have hlim : Tendsto (fun N : ℕ => C * (N : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul C
    exact squeeze_zero_norm hb hlim
  have := hu.add herr
  rw [add_zero] at this
  exact this.congr fun N => by ring

/-- If `(1/n) Σ_{k<n} aₖ → 0` then `(1/N) Σ_{n<N} a_{n+c} → 0`. -/
theorem tendsto_avg_shift {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k) atTop (𝓝 0)) (c : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, a (n + c)) atTop (𝓝 0) := by
  set P : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, a k
  have hsplit : ∀ N, ∑ n ∈ Finset.range N, a (n + c) = P (N + c) - P c := fun N => by
    simp only [P]
    rw [add_comm N c, Finset.sum_range_add, add_sub_cancel_left]
    exact Finset.sum_congr rfl fun n _ => by rw [add_comm]
  simp_rw [hsplit]
  have h1 : Tendsto (fun N : ℕ => ((N + c : ℕ) : ℝ)⁻¹ * P (N + c)) atTop (𝓝 0) :=
    ha.comp (tendsto_add_atTop_nat c)
  have h2 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * P (N + c)) atTop (𝓝 0) := by
    have hb : ∀ᶠ N : ℕ in atTop,
        ‖(N : ℝ)⁻¹ * P (N + c)‖ ≤ (1 + c) * ‖((N + c : ℕ) : ℝ)⁻¹ * P (N + c)‖ := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hpos : (0 : ℝ) < N := by linarith
      rw [norm_mul, norm_mul, norm_inv, norm_inv, Real.norm_natCast, Real.norm_natCast,
        ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Nat.cast_add, inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, mul_one,
        div_le_div_iff₀ hpos (by positivity)]
      nlinarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
    have hlim : Tendsto (fun N : ℕ => (1 + c) * ‖((N + c : ℕ) : ℝ)⁻¹ * P (N + c)‖) atTop
        (𝓝 0) := by
      simpa using (h1.norm).const_mul (1 + (c : ℝ))
    exact squeeze_zero_norm' hb hlim
  have h3 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * P c) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const (P c)
  simpa [mul_sub] using h2.sub h3

/-! ### Lemma 14.8 -/

/-- `Tʲf` is bounded measurable, with the bound of `f`. -/
theorem iterate_markovOpR_bdd (Q : Kernel S S) [IsMarkovKernel Q] {f : S → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ s, |f s| ≤ B) (j : ℕ) :
    Measurable ((markovOpR Q)^[j] f) ∧ ∀ s, |(markovOpR Q)^[j] f s| ≤ B := by
  induction j with
  | zero => exact ⟨hf, hB⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact theorem_8_1_cor Q ih.1 ih.2

/-- For each `j`, the averages of the martingale differences `(Tʲf)(σ_{k+1}) − (T^{j+1}f)(σ_k)`
tend to `0` a.s. (Theorem 14.6 with the Markov property). -/
theorem mg_avg_tendsto (Q : Kernel S S) [IsMarkovKernel Q] (s₀ : S) {f : S → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ s, |f s| ≤ B) (j : ℕ) :
    ∀ᵐ ω ∂pathM Q s₀, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
      ((markovOpR Q)^[j] f (ω (k + 1)) - (markovOpR Q)^[j + 1] f (ω k))) atTop (𝓝 0) := by
  have := isProbabilityMeasure_pathM Q s₀
  set g := (markovOpR Q)^[j] f
  obtain ⟨hgm, hgB⟩ := iterate_markovOpR_bdd Q hf hB j
  have hg1 : (markovOpR Q)^[j + 1] f = markovOpR Q g := Function.iterate_succ_apply' _ _ _
  set 𝒜 := Filtration.piLE (X := fun _ : ℕ => S)
  set F : ℕ → (ℕ → S) → ℝ := fun k ω => g (ω k)
  have hFm : ∀ k, StronglyMeasurable[𝒜 k] (F k) := fun k =>
    (hgm.comp (measurable_coord_piLE k)).stronglyMeasurable
  have hF2 : ∀ k, MemLp (F k) 2 (pathM Q s₀) := fun k =>
    MemLp.of_bound (hgm.comp (measurable_pi_apply k)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgB _)
  have hmp : ∀ k, (pathM Q s₀)[F (k + 1) | 𝒜 k] =ᵐ[pathM Q s₀] fun ω => markovOpR Q g (ω k) :=
    fun k => markov_property Q s₀ hgm hgB k
  have hTB := (theorem_8_1_cor Q hgm hgB).2
  have hM : ∀ k, ∫ ω, (F (k + 1) ω - (pathM Q s₀)[F (k + 1) | 𝒜 k] ω) ^ 2 ∂pathM Q s₀ ≤
      (2 * B) ^ 2 := fun k => by
    have hint : Integrable (fun ω => (F (k + 1) ω - (pathM Q s₀)[F (k + 1) | 𝒜 k] ω) ^ 2)
        (pathM Q s₀) := ((hF2 (k + 1)).sub ((hF2 (k + 1)).condExp one_le_two)).integrable_sq
    refine (integral_mono_ae hint (integrable_const ((2 * B) ^ 2)) ?_).trans (by simp)
    filter_upwards [hmp k] with ω hω
    rw [hω]
    have h1 := hgB (ω (k + 1))
    have h2 := hTB (ω k)
    have : |F (k + 1) ω - markovOpR Q g (ω k)| ≤ 2 * B := by
      simp only [F]
      linarith [abs_sub (g (ω (k + 1))) (markovOpR Q g (ω k))]
    exact sq_le_sq' (by linarith [neg_abs_le (F (k + 1) ω - markovOpR Q g (ω k))])
      (le_of_abs_le this)
  have h146 := theorem_14_6 𝒜 (fun _ _ hij => 𝒜.mono hij) 𝒜.le hFm hF2 hM
  filter_upwards [h146, ae_all_iff.2 hmp] with ω hω hall
  rw [hg1]
  refine hω.congr fun n => ?_
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hall k]

/-- Lemma 14.8 in shifted form: `(1/N) Σ_{n<N} [f(σ_{n+m}) − (Tᵐf)(σₙ)] → 0` a.s., for all `m`
simultaneously. -/
theorem lemma_14_8_shift (Q : Kernel S S) [IsMarkovKernel Q] (s₀ : S) {f : S → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ s, |f s| ≤ B) :
    ∀ᵐ ω ∂pathM Q s₀, ∀ m, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      (f (ω (n + m)) - (markovOpR Q)^[m] f (ω n))) atTop (𝓝 0) := by
  filter_upwards [ae_all_iff.2 (mg_avg_tendsto Q s₀ hf hB)] with ω hω m
  set d : ℕ → ℕ → ℝ := fun j k =>
    (markovOpR Q)^[j] f (ω (k + 1)) - (markovOpR Q)^[j + 1] f (ω k)
  have htel : ∀ n, f (ω (n + m)) - (markovOpR Q)^[m] f (ω n) =
      ∑ j ∈ Finset.range m, d j (n + (m - 1 - j)) := fun n => by
    have := Finset.sum_range_sub' (fun j => (markovOpR Q)^[j] f (ω (n + m - j))) m
    simp only [Function.iterate_zero, id, Nat.sub_zero, Nat.add_sub_cancel] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    simp only [d]
    rw [show n + (m - 1 - j) + 1 = n + m - j by omega, show n + m - (j + 1) = n + (m - 1 - j) by
      omega]
  simp_rw [htel]
  have : ∀ N : ℕ, (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range m, d j (n + (m - 1 - j)) =
      ∑ j ∈ Finset.range m, (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, d j (n + (m - 1 - j)) :=
    fun N => by rw [Finset.sum_comm, Finset.mul_sum]
  simp_rw [this]
  have := tendsto_finsetSum (Finset.range m) fun j _ => tendsto_avg_shift (hω j) (m - 1 - j)
  rw [Finset.sum_const_zero] at this
  exact this

/-- **Lemma 14.8** (corrected: `μ = μ(s₀, ·)`). For bounded measurable `f` and `m ≥ 1`,
`(1/N) Σ_{n=m+1}^N [f(σₙ) − (Tᵐf)(σ_{n−m})] → 0`, `μ(s₀, ·)`-a.s. -/
theorem lemma_14_8 (Q : Kernel S S) [IsMarkovKernel Q] (s₀ : S) {f : S → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ s, |f s| ≤ B) {m : ℕ} (hm : 1 ≤ m) :
    ∀ᵐ ω ∂pathM Q s₀, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc m N,
      (f (ω n) - (markovOpR Q)^[m] f (ω (n - m)))) atTop (𝓝 0) := by
  filter_upwards [lemma_14_8_shift Q s₀ hf hB] with ω hω
  set a : ℕ → ℝ := fun n => f (ω (n + m)) - (markovOpR Q)^[m] f (ω n)
  have haB : ∀ n, |a n| ≤ 2 * B := fun n => by
    have h1 := hB (ω (n + m))
    have h2 := (iterate_markovOpR_bdd Q hf hB m).2 (ω n)
    simp only [a]
    linarith [abs_sub (f (ω (n + m))) ((markovOpR Q)^[m] f (ω n))]
  -- reindex `n = n' + m`
  have hre : ∀ N, ∑ n ∈ Finset.Ioc m N, (f (ω n) - (markovOpR Q)^[m] f (ω (n - m))) =
      ∑ k ∈ Finset.range (N - m), a (k + 1) := fun N => by
    have hset : Finset.Ioc m N = (Finset.range (N - m)).map (addRightEmbedding (m + 1)) := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, addRightEmbedding_apply]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨n - (m + 1), by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩
        omega
    rw [hset, Finset.sum_map]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [addRightEmbedding_apply, a]
    rw [show k + (m + 1) - m = k + 1 by omega, show k + (m + 1) = k + 1 + m by omega]
  simp_rw [hre]
  refine tendsto_avg_of_bounded_diff (C := 2 * B + m * (2 * B) + 1 * (2 * B)) (hω m)
    fun N => ?_
  -- `Σ_{k < N-m} a(k+1)` differs from `Σ_{n < N} aₙ` by at most `m + 1` terms
  have hsplit : ∑ n ∈ Finset.range N, a n =
      ∑ k ∈ Finset.range (N - m), a (k + 1) +
        (a 0 + ∑ n ∈ Finset.Ico (N - m + 1) (max N (N - m + 1)), a n) -
        ∑ n ∈ Finset.Ico N (max N (N - m + 1)), a n := by
    have h1 : ∑ n ∈ Finset.range (N - m + 1), a n =
        ∑ k ∈ Finset.range (N - m), a (k + 1) + a 0 := Finset.sum_range_succ' a _
    have h2 := Finset.sum_range_add_sum_Ico a (show N - m + 1 ≤ max N (N - m + 1) from
      le_max_right _ _)
    have h3 := Finset.sum_range_add_sum_Ico a (show N ≤ max N (N - m + 1) from le_max_left _ _)
    linarith
  rw [hsplit]
  have hIco : ∀ p q : ℕ, |∑ n ∈ Finset.Ico p q, a n| ≤ (q - p : ℕ) * (2 * B) := fun p q => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul (Finset.Ico p q) (fun n => |a n|) (2 * B)
      fun n _ => haB n
    rwa [Nat.card_Ico, nsmul_eq_mul] at this
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB s₀)
  have e1 := hIco (N - m + 1) (max N (N - m + 1))
  have e2 := hIco N (max N (N - m + 1))
  have hc1 : ((max N (N - m + 1) - (N - m + 1) : ℕ) : ℝ) ≤ m := by
    have : max N (N - m + 1) - (N - m + 1) ≤ m := by omega
    exact_mod_cast this
  have hc2 : ((max N (N - m + 1) - N : ℕ) : ℝ) ≤ 1 := by
    have : max N (N - m + 1) - N ≤ 1 := by omega
    exact_mod_cast this
  have e3 := haB 0
  set A1 := ∑ n ∈ Finset.Ico (N - m + 1) (max N (N - m + 1)), a n
  set A2 := ∑ n ∈ Finset.Ico N (max N (N - m + 1)), a n
  have f1 : |A1| ≤ m * (2 * B) := e1.trans (mul_le_mul_of_nonneg_right hc1 (by linarith))
  have f2 : |A2| ≤ 1 * (2 * B) := e2.trans (mul_le_mul_of_nonneg_right hc2 (by linarith))
  have h1 := abs_add_le (-(a 0) - A1) A2
  have h2 := abs_sub (-(a 0)) A1
  rw [abs_neg] at h2
  have : ∑ k ∈ Finset.range (N - m), a (k + 1) -
      (∑ k ∈ Finset.range (N - m), a (k + 1) + (a 0 + A1) - A2) = -(a 0) - A1 + A2 := by ring
  rw [this]
  linarith

/-! ### The counterexample to Lemma 14.8 as printed -/

/-- The uniform distribution on `{0, 1}` (`false`, `true`). -/
noncomputable def unifBool : Measure Bool :=
  (1 / 2 : ENNReal) • (Measure.dirac false + Measure.dirac true)

theorem isProbabilityMeasure_unifBool : IsProbabilityMeasure unifBool := ⟨by
  simp only [unifBool, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, one_div, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

/-- The indicator of `{1}` on `{0, 1}`. -/
def indTrue (b : Bool) : ℝ := if b then 1 else 0

theorem integral_indTrue_unifBool : ∫ b, indTrue b ∂unifBool = 1 / 2 := by
  have := isProbabilityMeasure_unifBool
  rw [unifBool, integral_smul_measure, integral_add_measure (integrable_of_bounded
    (measurable_of_countable _) (M := 1) fun b => by cases b <;> simp [indTrue])
    (integrable_of_bounded (measurable_of_countable _) (M := 1) fun b => by
      cases b <;> simp [indTrue])]
  simp [indTrue]

/-- **Correction to Lemma 14.8.** As printed, `μ` is any probability measure on `S^∞`. With
`S = {0, 1}`, `P(s, ·)` uniform, `μ = δ_{(0, 0, …)}`, `f = 1_{1}` and `m = 1`, the averages
`(1/N) Σ_{n=2}^N [f(σₙ) − (Tf)(σ_{n−1})]` tend to `−1/2`, not `0`. -/
theorem lemma_14_8_counterexample :
    ¬ ∀ᵐ ω ∂(Measure.dirac (fun _ : ℕ => false)),
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc 1 N,
        (indTrue (ω n) - (markovOpR (Kernel.const Bool unifBool))^[1] indTrue (ω (n - 1))))
        atTop (𝓝 0) := by
  rw [ae_dirac_eq, eventually_pure]
  intro h
  have hT : ∀ b, (markovOpR (Kernel.const Bool unifBool))^[1] indTrue b = 1 / 2 := fun b => by
    simp only [Function.iterate_one, markovOpR, Kernel.const_apply]
    exact integral_indTrue_unifBool
  have hval : ∀ N : ℕ, (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc 1 N,
      (indTrue false - (markovOpR (Kernel.const Bool unifBool))^[1] indTrue false) =
      -(1 / 2) * (((N : ℝ) - 1) / N) + 0 * N := fun N => by
    simp only [hT, indTrue, Bool.false_eq_true, ↓reduceIte, Finset.sum_const, Nat.card_Ioc,
      nsmul_eq_mul, zero_mul, add_zero]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [Nat.cast_sub hN]
      field_simp
      ring
  simp only [hval] at h
  have hlim : Tendsto (fun N : ℕ => -(1 / 2) * (((N : ℝ) - 1) / N) + 0 * N) atTop
      (𝓝 (-(1 / 2) * 1)) := by
    have h1 : Tendsto (fun N : ℕ => ((N : ℝ) - 1) / N) atTop (𝓝 1) := by
      have : Tendsto (fun N : ℕ => 1 - (N : ℝ)⁻¹) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub tendsto_inv_atTop_nhds_zero_nat
      rw [sub_zero] at this
      refine this.congr' (eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
      have : (N : ℝ) ≠ 0 := by positivity
      field_simp
    simpa using h1.const_mul (-(1 / 2 : ℝ))
  have := tendsto_nhds_unique h hlim
  norm_num at this

end StokeyLucasPrescott.LawsOfLargeNumbers
