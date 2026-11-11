/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.StationaryProcesses

/-!
# Equivalent formulations of ergodicity (Miao Theorem 4.2.2, Exercise 5)

Copied from `EconomicDynamics/ErgodicTheory` (module `StationaryErgodicity`), namespace renamed.

Miao, Theorem 4.2.2, p. 123 (after Karlin and Taylor 1975), and Exercise 5, p. 129. For a
stationary process `X` (on any measurable state space) the following are equivalent
(`theorem_4_2_2`, a `List.TFAE`):

* (a) `X` is ergodic (Definition 4.2.3, with the book's shift-invariant sets `θA ⊆ A`);
* (b) `Pr{(X₀, X₁, …) ∈ A} ∈ {0, 1}` for every transformation-invariant `A` (`θ⁻¹A = A`);
* (c) `(1/n) Σ_{j=1}^n 1{(X_j, X_{j+1}, …) ∈ A} → Pr{(X₀, X₁, …) ∈ A}` a.s., for every
  `A ∈ B(E^∞)`;
* (d) the same for the windows `(X_j, …, X_{j+k})` and `A ∈ B(E^{k+1})`;
* (e) `(1/n) Σ_{j=1}^n φ(X_j, …, X_{j+k}) → E φ(X₀, …, X_k)` a.s. for every integrable Borel `φ`;
* (f) `(1/n) Σ_{k=1}^n φ(X_k, X_{k+1}, …) → E φ(X₀, X₁, …)` a.s. for every Borel `φ` with
  `E|φ(X₀, X₁, …)| < ∞`.

The proof: (a) ⇔ (b) is `isErgodicProcess_iff_isErgodic` (the book's (a) and (b) coincide by
Definition 4.2.3; here (b) uses transformation-invariant sets, which makes the equivalence the
correction of p. 123); (b) ⇒ (f) is Birkhoff's theorem; (f) ⇒ (e) ⇒ (d) and (f) ⇒ (c) are
special cases; (c) ⇒ (b) because `1_A(θʲx) = 1_A(x)` for invariant `A`; (d) ⇒ (b) because
(d) gives `P̃r(B ∩ C) = P̃r(B) P̃r(C)` for invariant `B` and every finite-dimensional box `C`,
hence for `C = B`.

`tendsto_avg_succ` moves the averages from `j = 0, …, n − 1` (Birkhoff) to the book's
`j = 1, …, n`. **Exercise 5** asks for the proofs of Theorems 4.2.2 and 4.3.2: `ex_4_5_a` is
Theorem 4.2.2 (Theorem 4.3.2 is `ex_4_5_b` in `ErgodicTheory.StationaryMarkov`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Averages over `j = 1, …, n` have the same limit as averages over `j = 0, …, n − 1`. -/
theorem tendsto_avg_succ {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a (k + 1)) atTop (𝓝 L) := by
  have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), a k) atTop
      (𝓝 L) := h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have h3 : Tendsto (fun n : ℕ => a 0 * (1 / (n : ℝ))) atTop (𝓝 (a 0 * 0)) :=
    tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at h3
  have h4 := (h2.mul h1).sub h3
  rw [one_mul, sub_zero] at h4
  refine h4.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsum : ∑ k ∈ Finset.range n, a (k + 1) = ∑ k ∈ Finset.range (n + 1), a k - a 0 := by
    rw [Finset.sum_range_succ']
    ring
  dsimp only
  rw [hsum]
  push_cast
  field_simp

omit [MeasurableSpace E] in
/-- For `θ⁻¹A = A`, `1_A(θʲx) = 1_A(x)`. -/
theorem indicator_shift_of_invariant {A : Set (ℕ → E)} (hA : shift 1 ⁻¹' A = A) (j : ℕ)
    (x : ℕ → E) : A.indicator (1 : (ℕ → E) → ℝ) (shift j x) = A.indicator 1 x := by
  have h : shift j ⁻¹' A = A := by
    have := iterate_mem_iff hA j
    ext y
    rw [Set.mem_preimage, ← iterate_shift_one, this]
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show shift j x ∈ A from
      (show x ∈ shift j ⁻¹' A by rw [h]; exact hx))]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show shift j x ∉ A from
      fun h' => hx (by rw [← h]; exact h'))]

/-- For a shift-preserving `μ` and `θ⁻¹B = B`, `μ(B ∩ θ⁻ʲC) = μ(B ∩ C)`. -/
theorem measure_inter_preimage_shift {μ : Measure (ℕ → E)} (hμ : MeasurePreserving (shift 1) μ μ)
    {B C : Set (ℕ → E)} (hB : shift 1 ⁻¹' B = B) (hBm : MeasurableSet B) (hCm : MeasurableSet C)
    (j : ℕ) : μ (B ∩ shift j ⁻¹' C) = μ (B ∩ C) := by
  have h : shift j ⁻¹' B = B := by
    have := iterate_mem_iff hB j
    ext y
    rw [Set.mem_preimage, ← iterate_shift_one, this]
  have hmp : MeasurePreserving (shift (X := E) j) μ μ := by
    have := hμ.iterate j
    rwa [show (shift 1)^[j] = shift (X := E) j from funext (iterate_shift_one j)] at this
  rw [show B ∩ shift j ⁻¹' C = shift j ⁻¹' (B ∩ C) by rw [Set.preimage_inter, h],
    hmp.measure_preimage (hBm.inter hCm).nullMeasurableSet]

/-- The key step of (d) ⇒ (b): if the averages of `1_C(θʲx)` converge a.s. to `μ(C)` for every
box `C`, then every invariant `B` has `μ(B) ∈ {0, 1}`. -/
theorem measure_eq_zero_or_one_of_boxes {μ : Measure (ℕ → E)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ)
    (hbox : ∀ n (A : ℕ → Set E), (∀ i, MeasurableSet (A i)) → ∀ᵐ x ∂μ,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
        (boxSet n A).indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)) atTop
        (𝓝 (μ.real (boxSet n A))))
    {B : Set (ℕ → E)} (hBm : MeasurableSet B) (hB : shift 1 ⁻¹' B = B) :
    μ B = 0 ∨ μ B = 1 := by
  -- `μ(B ∩ C) = μ(B) μ(C)` for boxes
  have hprod : ∀ n (A : ℕ → Set E), (∀ i, MeasurableSet (A i)) →
      μ.real (B ∩ boxSet n A) = μ.real B * μ.real (boxSet n A) := by
    intro n A hA
    set C := boxSet n A with hC
    have hCm : MeasurableSet C := measurableSet_boxSet n hA
    set F : ℕ → (ℕ → E) → ℝ := fun N x => B.indicator 1 x * ((N : ℝ)⁻¹ *
      ∑ j ∈ Finset.range N, C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)) with hF
    have hFm : ∀ N, Measurable (F N) := fun N =>
      (measurable_one.indicator hBm).mul (measurable_const.mul (Finset.measurable_sum _
        fun j _ => (measurable_one.indicator hCm).comp (measurable_shift (j + 1))))
    have hFb : ∀ N x, |F N x| ≤ 1 := by
      intro N x
      have hi : ∀ (S : Set (ℕ → E)) y, 0 ≤ S.indicator (1 : (ℕ → E) → ℝ) y ∧
          S.indicator (1 : (ℕ → E) → ℝ) y ≤ 1 := fun S y => by
        by_cases hy : y ∈ S <;> simp [hy]
      have hsum : (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
          C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x) ≤ 1 := by
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · simp
        rw [inv_mul_le_iff₀ (by exact_mod_cast hN), mul_one]
        calc ∑ j ∈ Finset.range N, C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)
            ≤ ∑ _j ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum fun j _ => (hi C _).2
          _ = N := by simp
      have hsum0 : 0 ≤ (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
          C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x) :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => (hi C _).1)
      rw [hF, abs_of_nonneg (mul_nonneg (hi B x).1 hsum0)]
      calc B.indicator 1 x * _ ≤ 1 * 1 := mul_le_mul (hi B x).2 hsum hsum0 zero_le_one
        _ = 1 := one_mul 1
    -- `∫ F N = μ(B ∩ C)` for `N ≥ 1`
    have hint : ∀ N, 1 ≤ N → ∫ x, F N x ∂μ = μ.real (B ∩ C) := by
      intro N hN
      have hterm : ∀ j : ℕ, ∫ x, B.indicator (1 : (ℕ → E) → ℝ) x *
          C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x) ∂μ = μ.real (B ∩ C) := by
        intro j
        have : (fun x => B.indicator (1 : (ℕ → E) → ℝ) x *
            C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)) =
            (B ∩ shift (j + 1) ⁻¹' C).indicator 1 := by
          ext x
          by_cases hx : x ∈ B <;> by_cases hy : shift (j + 1) x ∈ C <;>
            simp [hx, hy, Set.indicator_of_mem, Set.indicator_of_notMem]
        rw [this, integral_indicator_one (hBm.inter ((measurable_shift (j + 1)) hCm)),
          measureReal_def, measure_inter_preimage_shift hμ hB hBm hCm, ← measureReal_def]
      have hInt : ∀ j : ℕ, Integrable (fun x => B.indicator (1 : (ℕ → E) → ℝ) x *
          C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)) μ := by
        intro j
        refine Integrable.of_bound ((measurable_one.indicator hBm).mul
          ((measurable_one.indicator hCm).comp (measurable_shift (j + 1)))).aestronglyMeasurable
          1 (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs]
        by_cases hx : x ∈ B <;> by_cases hy : shift (j + 1) x ∈ C <;> simp [hx, hy]
      have hFN : F N = fun x => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
          B.indicator (1 : (ℕ → E) → ℝ) x * C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x) := by
        ext x
        simp only [hF]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hFN, integral_const_mul, integral_finsetSum _ fun j _ => hInt j]
      simp_rw [hterm]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      field_simp
    -- dominated convergence
    have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
      (F := F) (f := fun x => B.indicator 1 x * μ.real C)
      (fun N => (hFm N).aestronglyMeasurable) (integrable_const _)
      (fun N => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFb N x)
      (by
        filter_upwards [hbox n A hA] with x hx
        exact tendsto_const_nhds.mul hx)
    have hlim' : ∫ x, B.indicator (1 : (ℕ → E) → ℝ) x * μ.real C ∂μ = μ.real B * μ.real C := by
      rw [integral_mul_const, integral_indicator_one hBm]
    rw [hlim'] at hlim
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' (eventually_atTop.2
      ⟨1, fun N hN => (hint N hN).symm⟩)) hlim
  -- hence `μ|_B = μ(B) μ`
  have hfinB : IsFiniteMeasure (μ B • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]; exact measure_lt_top μ B⟩
  have hmeas : μ.restrict B = μ B • μ := by
    refine ext_of_boxSet fun n A hA => ?_
    have hCm := measurableSet_boxSet n hA
    rw [Measure.restrict_apply hCm, Measure.smul_apply, smul_eq_mul, Set.inter_comm]
    have h := hprod n A hA
    rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul] at h
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1 h
  have hBB : μ B = μ B * μ B := by
    have := congrArg (fun m : Measure (ℕ → E) => m B) hmeas
    simp only [Measure.restrict_apply hBm, Set.inter_self, Measure.smul_apply,
      smul_eq_mul] at this
    exact this
  have hfin : μ B ≠ ⊤ := measure_ne_top _ _
  by_cases h0 : μ B = 0
  · exact Or.inl h0
  · right
    have := (ENNReal.mul_eq_left h0 hfin).1 hBB.symm
    exact this

/-- **Theorem 4.2.2** (Miao, p. 123). For a stationary process the conditions (a)–(f) are
equivalent (see the module docstring for (a)–(f); the averages run over `j = 1, …, n`). -/
theorem theorem_4_2_2 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) :
    List.TFAE [
      IsErgodicProcess P X,
      ∀ A : Set (ℕ → E), MeasurableSet A → shift 1 ⁻¹' A = A →
        P (pathOf X ⁻¹' A) = 0 ∨ P (pathOf X ⁻¹' A) = 1,
      ∀ A : Set (ℕ → E), MeasurableSet A → ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
          A.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) (pathOf X ω))) atTop
          (𝓝 (P.real (pathOf X ⁻¹' A))),
      ∀ (k : ℕ) (A : Set (Fin (k + 1) → E)), MeasurableSet A → ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
          A.indicator (1 : (Fin (k + 1) → E) → ℝ) (window X (j + 1) k ω)) atTop
          (𝓝 (P.real (window X 0 k ⁻¹' A))),
      ∀ (k : ℕ) (φ : (Fin (k + 1) → E) → ℝ), Measurable φ →
        Integrable (fun ω => φ (window X 0 k ω)) P → ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, φ (window X (j + 1) k ω))
          atTop (𝓝 (∫ ω, φ (window X 0 k ω) ∂P)),
      ∀ φ : (ℕ → E) → ℝ, Measurable φ → Integrable (fun ω => φ (pathOf X ω)) P → ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, φ (shift (j + 1) (pathOf X ω)))
          atTop (𝓝 (∫ ω, φ (pathOf X ω) ∂P))] := by
  have hΦ := measurable_pathOf hX
  have := isProbabilityMeasure_pathLaw P (X := X)
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  have hind : ∀ (S : Set (ℕ → E)), MeasurableSet S → Measurable (S.indicator
      (1 : (ℕ → E) → ℝ)) := fun S hS => measurable_one.indicator hS
  have hindb : ∀ (S : Set (ℕ → E)) (ψ : Ω → ℕ → E), Measurable ψ → MeasurableSet S →
      Integrable (fun ω => S.indicator (1 : (ℕ → E) → ℝ) (ψ ω)) P := by
    intro S ψ hψ hS
    refine Integrable.of_bound ((hind S hS).comp hψ).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    by_cases h : ψ ω ∈ S <;> simp [h]
  tfae_have 1 ↔ 2 := by
    rw [isErgodicProcess_iff_isErgodic hX hst]
    constructor
    · intro h A hA hθA
      have := h A ⟨hA, hθA⟩
      rwa [pathLaw, Measure.map_apply hΦ hA] at this
    · intro h A hA
      have := h A hA.1 hA.2
      rwa [pathLaw, Measure.map_apply hΦ hA.1]
  tfae_have 2 → 6 := by
    intro h φ hφ hφi
    have herg : IsErgodic (pathLaw P X) (shift 1) := fun A hA => by
      have := h A hA.1 hA.2
      rwa [pathLaw, Measure.map_apply hΦ hA.1]
    have hφi' : Integrable φ (pathLaw P X) :=
      (integrable_map_measure hφ.aestronglyMeasurable hΦ.aemeasurable).2 hφi
    have hB := theorem_4_1_1_ergodic hmp herg hφ hφi'
    have hE : ∫ y, φ y ∂pathLaw P X = ∫ ω, φ (pathOf X ω) ∂P :=
      integral_map hΦ.aemeasurable hφ.aestronglyMeasurable
    rw [hE] at hB
    filter_upwards [ae_of_ae_map hΦ.aemeasurable hB] with ω hω
    have := tendsto_avg_succ hω
    refine this.congr fun n => ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iterate_shift_one]
  tfae_have 6 → 3 := by
    intro h A hA
    have := h (A.indicator 1) (hind A hA) (hindb A (pathOf X) hΦ hA)
    have hE : ∫ ω, A.indicator (1 : (ℕ → E) → ℝ) (pathOf X ω) ∂P = P.real (pathOf X ⁻¹' A) := by
      rw [← integral_indicator_one (hΦ hA)]
      congr 1
    rwa [hE] at this
  tfae_have 6 → 5 := by
    intro h k φ hφ hφi
    have hφi' : Integrable (fun ω => (φ ∘ pathWindow k) (pathOf X ω)) P := by
      have : (fun ω => (φ ∘ pathWindow k) (pathOf X ω)) = fun ω => φ (window X 0 k ω) := by
        rw [window_zero]; rfl
      rw [this]; exact hφi
    have := h (φ ∘ pathWindow k) (hφ.comp (measurable_pathWindow k)) hφi'
    have hE : ∫ ω, (φ ∘ pathWindow k) (pathOf X ω) ∂P = ∫ ω, φ (window X 0 k ω) ∂P := by
      rw [window_zero]; rfl
    rw [hE] at this
    exact this
  tfae_have 5 → 4 := by
    intro h k A hA
    have hφ : Measurable (A.indicator (1 : (Fin (k + 1) → E) → ℝ)) :=
      measurable_one.indicator hA
    have hφi : Integrable (fun ω => A.indicator (1 : (Fin (k + 1) → E) → ℝ)
        (window X 0 k ω)) P := by
      refine Integrable.of_bound (hφ.comp (measurable_window hX 0 k)).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      by_cases hω : window X 0 k ω ∈ A <;> simp [hω]
    have := h k _ hφ hφi
    have hE : ∫ ω, A.indicator (1 : (Fin (k + 1) → E) → ℝ) (window X 0 k ω) ∂P =
        P.real (window X 0 k ⁻¹' A) := by
      rw [← integral_indicator_one ((measurable_window hX 0 k) hA)]
      congr 1
    rwa [hE] at this
  tfae_have 3 → 2 := by
    intro h A hA hθA
    have hc := h A hA
    have hconst : ∀ᵐ ω ∂P, A.indicator (1 : (ℕ → E) → ℝ) (pathOf X ω) =
        P.real (pathOf X ⁻¹' A) := by
      filter_upwards [hc] with ω hω
      refine tendsto_nhds_unique (tendsto_const_nhds.congr' (eventually_atTop.2
        ⟨1, fun n hn => ?_⟩)) hω
      simp_rw [indicator_shift_of_invariant hθA]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega)), one_mul]
    obtain ⟨ω, hω⟩ := hconst.exists
    have hfin : P (pathOf X ⁻¹' A) ≠ ⊤ := measure_ne_top _ _
    by_cases hmem : pathOf X ω ∈ A
    · rw [Set.indicator_of_mem hmem, Pi.one_apply, measureReal_def] at hω
      right
      exact ((ENNReal.toReal_eq_one_iff _).1 hω.symm)
    · rw [Set.indicator_of_notMem hmem, measureReal_def] at hω
      left
      exact ((ENNReal.toReal_eq_zero_iff _).1 hω.symm).resolve_right hfin
  tfae_have 4 → 2 := by
    intro h A hA hθA
    have hbox : ∀ n (B : ℕ → Set E), (∀ i, MeasurableSet (B i)) → ∀ᵐ x ∂pathLaw P X,
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
          (boxSet n B).indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)) atTop
          (𝓝 ((pathLaw P X).real (boxSet n B))) := by
      intro n B hB
      set R := Set.univ.pi fun i : Fin (n + 1) => B i with hR
      have hRm : MeasurableSet R := MeasurableSet.univ_pi fun i => hB i
      have hd := h n R hRm
      have hmeasC : MeasurableSet {x : ℕ → E | Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
          ∑ j ∈ Finset.range N, (boxSet n B).indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x))
          atTop (𝓝 ((pathLaw P X).real (boxSet n B)))} :=
        measurableSet_tendsto _ fun N => measurable_const.mul (Finset.measurable_sum _
          fun j _ => (hind _ (measurableSet_boxSet n hB)).comp (measurable_shift (j + 1)))
      change ∀ᵐ x ∂(P.map (pathOf X)), _
      rw [ae_map_iff hΦ.aemeasurable hmeasC]
      have hlim : P.real (window X 0 n ⁻¹' R) = (pathLaw P X).real (boxSet n B) := by
        rw [pathLaw, map_measureReal_apply hΦ (measurableSet_boxSet n hB), boxSet_eq_preimage,
          window_zero]
        rfl
      filter_upwards [hd] with ω hω
      rw [← hlim]
      refine hω.congr fun N => ?_
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [boxSet_eq_preimage]
      rfl
    have := measure_eq_zero_or_one_of_boxes hmp hbox hA hθA
    rwa [pathLaw, Measure.map_apply hΦ hA] at this
  tfae_finish

/-- **Exercise 5** (Miao, p. 129), first part: the proof of Theorem 4.2.2 (`theorem_4_2_2`). -/
theorem ex_4_5_a {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) :
    IsErgodicProcess P X ↔ ∀ φ : (ℕ → E) → ℝ, Measurable φ →
      Integrable (fun ω => φ (pathOf X ω)) P → ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, φ (shift (j + 1) (pathOf X ω)))
          atTop (𝓝 (∫ ω, φ (pathOf X ω) ∂P)) :=
  (theorem_4_2_2 hX hst).out 1 6

end Miao.StructuralEstimation
