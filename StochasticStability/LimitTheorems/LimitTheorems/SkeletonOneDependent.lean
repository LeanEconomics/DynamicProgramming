/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.AtomCLT
import LimitTheorems.DependentLIL
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Chebyshev

/-!
# Stationary one-dependent sequences: the strong law, the CLT and random indices (MT §17.3)

Meyn and Tweedie, proofs of Theorems 17.3.2 and 17.3.6, pp. 436 and 441–442. The cycle sums of
a split `m`-skeleton are stationary and one-dependent (Theorem 17.3.1); this module proves the
limit theorems for such sequences that the book uses. `IsOneDependent` and `IsStationarySeq`
are the definitions of `DependentLIL` (the past `(Z₀, …, Zₙ)` is independent of the future
`(Z_{n+2}, Z_{n+3}, …)`; every shift has the law of the sequence).

**Tools.**
* `indepFun_of_boxes`, `indepFun_of_boxes_nat`, `measure_eq_of_boxes`, `measure_eq_of_boxSets`:
  independence and equality of laws are checked on boxes.
* `IsOneDependent.iIndepFun_even`, `IsOneDependent.iIndepFun_odd`: the even and the odd terms are
  independent (MT p. 436).
* `bigBlock Z L i = Σ_{j ≤ L} Z_{i(L+2)+j}`, `IsOneDependent.iIndepFun_bigBlock`,
  `IsStationarySeq.identDistrib_bigBlock`: the big blocks of (17.36) are i.i.d.;
  `sum_range_eq_bigBlock` is the decomposition (17.36); `IsOneDependent.integral_sq_sum_sparse`
  and `IsOneDependent.integral_sq_sub_bigBlock_le`: the small blocks are negligible in `L²`.
* `norm_charFun_map_sub_le`: `|φ_X(t) − φ_Y(t)| ≤ |t| E|X − Y|`; `tendsto_of_approx`: the
  approximation argument at the end of MT p. 442.

**Results.**
* **The strong law** (`IsOneDependent.ae_tendsto_average`, MT p. 436): `(1/n) Σ_{j<n} Zⱼ → E[Z₀]`
  almost surely, for integrable `Z₀`.
* `oneDepVariance Z Q = E[Z₀²] + 2 E[Z₀ Z₁]` (the `σ̄²` of MT p. 442) and
  `IsOneDependent.oneDepVariance_nonneg`.
* **The CLT** (`IsOneDependent.tendstoInDistribution`, MT p. 442): for centred `Z₀ ∈ L²`,
  `n^{−1/2} Σ_{j<n} Zⱼ ⇒ N(0, σ̄²)`; `IsOneDependent.tendsto_charFun_bigBlock` is the CLT for the
  big blocks, `N(0, σ_{L+1}²/(L + 2))` with `σ_{L+1}² = (L + 1) E[Z₀²] + 2L E[Z₀ Z₁]` (MT's
  `σ_m² = (m − 1) E[s₁²] + 2 (m − 2) E[s₁ s₂]` with `m = L + 2`).
* **The random-index step** (`IsOneDependent.tendstoInMeasure_randomIndex`, MT (17.35)): if
  `Kₙ/n → c > 0` a.s., `(Σ_{j<Kₙ} Zⱼ − Σ_{j<2⌊cn/2⌋} Zⱼ)/√n → 0` in probability, by Kolmogorov's
  inequality (Theorem D.6.3, `tendstoInMeasure_anscombe`) for the even and the odd terms.

**Corrections.** None. The book's `σ_m²/m → σ̄²` and `σ_s²/m → 0` "from which it can be shown"
is made precise by `tendsto_of_approx`: the big-block sums are within `L²`-distance
`O(m^{−1/2})` of the partial sums uniformly in `n`.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Boxes -/

/-- Two finite random vectors are independent as soon as box events are: boxes form a
generating π-system of the product σ-algebra. -/
theorem indepFun_of_boxes {Q : Measure Ω} [IsProbabilityMeasure Q] {ι κ : Type*} [Finite ι]
    [Finite κ] {U : Ω → ι → ℝ} {W : Ω → κ → ℝ} (hU : Measurable U) (hW : Measurable W)
    (h : ∀ (A : ι → Set ℝ) (B : κ → Set ℝ), (∀ i, MeasurableSet (A i)) →
      (∀ i, MeasurableSet (B i)) →
      Q (U ⁻¹' univ.pi A ∩ W ⁻¹' univ.pi B) = Q (U ⁻¹' univ.pi A) * Q (W ⁻¹' univ.pi B)) :
    IndepFun U W Q := by
  rw [IndepFun_iff_Indep]
  have hU' : MeasurableSpace.comap U MeasurableSpace.pi = MeasurableSpace.generateFrom
      {s | ∃ t ∈ pi univ '' pi univ fun _ => {s : Set ℝ | MeasurableSet s}, U ⁻¹' t = s} := by
    rw [← generateFrom_pi, MeasurableSpace.comap_generateFrom]; rfl
  have hW' : MeasurableSpace.comap W MeasurableSpace.pi = MeasurableSpace.generateFrom
      {s | ∃ t ∈ pi univ '' pi univ fun _ => {s : Set ℝ | MeasurableSet s}, W ⁻¹' t = s} := by
    rw [← generateFrom_pi, MeasurableSpace.comap_generateFrom]; rfl
  refine IndepSets.indep hU.comap_le hW.comap_le (isPiSystem_pi.comap U) (isPiSystem_pi.comap W)
    hU' hW' ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩ ⟨_, ⟨B, hB, rfl⟩, rfl⟩
  exact h A B (fun i => hA i (mem_univ i)) (fun i => hB i (mem_univ i))

/-- Two finite measures on `ι → ℝ` (`ι` finite) that agree on boxes are equal. -/
theorem measure_eq_of_boxes {ι : Type*} [Finite ι] {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (h : ∀ B : ι → Set ℝ, (∀ i, MeasurableSet (B i)) → μ (univ.pi B) = ν (univ.pi B)) :
    μ = ν := by
  refine ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ ?_
  · rintro _ ⟨B, hB, rfl⟩
    exact h B fun i => hB i (mem_univ i)
  · have := h (fun _ => univ) fun _ => MeasurableSet.univ
    rwa [pi_univ] at this

/-- A finite random vector and a random sequence are independent as soon as box events are:
boxes `{Φ₀ ∈ B₀, …, Φₙ ∈ Bₙ}` generate the product σ-algebra on `ℕ → ℝ` (`generateFrom_boxSets`). -/
theorem indepFun_of_boxes_nat {Q : Measure Ω} [IsProbabilityMeasure Q] {ι : Type*} [Finite ι]
    {U : Ω → ι → ℝ} {W : Ω → ℕ → ℝ} (hU : Measurable U) (hW : Measurable W)
    (h : ∀ (A : ι → Set ℝ) (n : ℕ) (B : ℕ → Set ℝ), (∀ i, MeasurableSet (A i)) →
      (∀ i, MeasurableSet (B i)) →
      Q (U ⁻¹' univ.pi A ∩ W ⁻¹' boxSet n B) = Q (U ⁻¹' univ.pi A) * Q (W ⁻¹' boxSet n B)) :
    IndepFun U W Q := by
  rw [IndepFun_iff_Indep]
  have hU' : MeasurableSpace.comap U MeasurableSpace.pi = MeasurableSpace.generateFrom
      {s | ∃ t ∈ pi univ '' pi univ fun _ => {s : Set ℝ | MeasurableSet s}, U ⁻¹' t = s} := by
    rw [← generateFrom_pi, MeasurableSpace.comap_generateFrom]; rfl
  have hW' : MeasurableSpace.comap W MeasurableSpace.pi = MeasurableSpace.generateFrom
      {s | ∃ t ∈ {S : Set (ℕ → ℝ) | ∃ n, ∃ B : ℕ → Set ℝ, (∀ i, MeasurableSet (B i)) ∧
        S = boxSet n B}, W ⁻¹' t = s} := by
    rw [generateFrom_boxSets, MeasurableSpace.comap_generateFrom]; rfl
  refine IndepSets.indep hU.comap_le hW.comap_le (isPiSystem_pi.comap U)
    (isPiSystem_boxSets.comap W) hU' hW' ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩ ⟨_, ⟨n, B, hB, rfl⟩, rfl⟩
  exact h A n B (fun i => hA i (mem_univ i)) hB

/-- Two finite measures on `ℕ → ℝ` that agree on boxes are equal. -/
theorem measure_eq_of_boxSets {μ ν : Measure (ℕ → ℝ)} [IsFiniteMeasure μ]
    (h : ∀ (n : ℕ) (B : ℕ → Set ℝ), (∀ i, MeasurableSet (B i)) →
      μ (boxSet n B) = ν (boxSet n B)) : μ = ν := by
  refine ext_of_generate_finite _ generateFrom_boxSets isPiSystem_boxSets ?_ ?_
  · rintro _ ⟨n, B, hB, rfl⟩
    exact h n B hB
  · have hu : (univ : Set (ℕ → ℝ)) = boxSet 0 (fun _ => univ) := by ext; simp [boxSet]
    rw [hu]
    exact h 0 _ fun _ => MeasurableSet.univ

/-! ### One-dependent sequences: even and odd terms -/

/-- The even terms `Z₀, Z₂, Z₄, …` of a one-dependent sequence are independent. -/
theorem IsOneDependent.iIndepFun_even {Z : ℕ → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (h : IsOneDependent Z Q) : iIndepFun (fun i => Z (2 * i)) Q := by
  refine iIndepFun_of_indepFun_succ fun i => ?_
  have h1 := h (2 * i)
  have hφ : Measurable fun (v : Fin (2 * i + 1) → ℝ) (j : Fin (i + 1)) =>
      v ⟨2 * j, by have := j.2; omega⟩ := measurable_pi_iff.2 fun j => measurable_pi_apply _
  have h2 := h1.comp hφ (measurable_pi_apply 0)
  have h3 : ((fun w : ℕ → ℝ => w 0) ∘ fun ω (j : ℕ) => Z (2 * i + 2 + j) ω) =
      Z (2 * (i + 1)) := by
    funext ω; simp only [Function.comp_apply, add_zero]; congr 1
  rw [h3] at h2
  exact h2

/-- The odd terms `Z₁, Z₃, Z₅, …` of a one-dependent sequence are independent. -/
theorem IsOneDependent.iIndepFun_odd {Z : ℕ → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (h : IsOneDependent Z Q) : iIndepFun (fun i => Z (2 * i + 1)) Q := by
  refine iIndepFun_of_indepFun_succ fun i => ?_
  have h1 := h (2 * i + 1)
  have hφ : Measurable fun (v : Fin (2 * i + 1 + 1) → ℝ) (j : Fin (i + 1)) =>
      v ⟨2 * j + 1, by have := j.2; omega⟩ := measurable_pi_iff.2 fun j => measurable_pi_apply _
  have h2 := h1.comp hφ (measurable_pi_apply 0)
  have h3 : ((fun w : ℕ → ℝ => w 0) ∘ fun ω (j : ℕ) => Z (2 * i + 1 + 2 + j) ω) =
      Z (2 * (i + 1) + 1) := by
    funext ω; simp only [Function.comp_apply, add_zero]; congr 1
  rw [h3] at h2
  exact h2

/-! ### The strong law -/

/-- A sequence converges if its even and odd subsequences converge to the same limit. -/
theorem tendsto_of_tendsto_two_mul {u : ℕ → ℝ} {L : ℝ}
    (he : Tendsto (fun n => u (2 * n)) atTop (𝓝 L))
    (ho : Tendsto (fun n => u (2 * n + 1)) atTop (𝓝 L)) : Tendsto u atTop (𝓝 L) := by
  rw [tendsto_def] at he ho ⊢
  intro s hs
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (he s hs)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (ho s hs)
  refine eventually_atTop.2 ⟨2 * (N1 + N2) + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact hN1 k (by omega)
  · exact hN2 k (by omega)

/-- `Σ_{j<2n} zⱼ = Σ_{i<n} z_{2i} + Σ_{i<n} z_{2i+1}`. -/
theorem sum_range_two_mul (z : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), z j =
      ∑ i ∈ Finset.range n, z (2 * i) + ∑ i ∈ Finset.range n, z (2 * i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- If the averages of the even terms and of the odd terms both converge to `L`, so do the
averages of the whole sequence. -/
theorem tendsto_average_of_even_odd {z : ℕ → ℝ} {L : ℝ}
    (he : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z (2 * i)) atTop (𝓝 L))
    (ho : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z (2 * i + 1)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, z j) atTop (𝓝 L) := by
  -- along the even times
  have h2 : Tendsto (fun n : ℕ => ((2 * n : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (2 * n), z j) atTop
      (𝓝 L) := by
    have : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z (2 * i)) +
        (1 / 2 : ℝ) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z (2 * i + 1))) atTop
        (𝓝 ((1 / 2) * L + (1 / 2) * L)) := (he.const_mul _).add (ho.const_mul _)
    rw [show (1 / 2 : ℝ) * L + 1 / 2 * L = L by ring] at this
    refine this.congr fun n => ?_
    rw [sum_range_two_mul]
    push_cast
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
  -- the extra even term is negligible
  have hterm : Tendsto (fun n : ℕ => z (2 * n) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    refine tendsto_term_div_of_tendsto_average (a := fun i => z (2 * i)) (L := L) ?_
    refine he.congr fun n => ?_
    rw [div_eq_inv_mul]
  have hterm2 : Tendsto (fun n : ℕ => z (2 * n) / ((2 * n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_norm_zero.comp hterm)
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_div]
    rw [abs_of_pos (by positivity : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ)),
      abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by push_cast; linarith)
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => by omega⟩
  have hfac : Tendsto (fun n : ℕ => ((2 * n : ℕ) : ℝ) / ((2 * n : ℕ) + 1)) atTop (𝓝 1) :=
    (tendsto_natCast_div_add_atTop (1 : ℝ)).comp h2n
  refine tendsto_of_tendsto_two_mul h2 ?_
  have := (hfac.mul h2).add hterm2
  rw [one_mul, add_zero] at this
  refine this.congr fun n => ?_
  rw [Finset.sum_range_succ]
  push_cast
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp


/-- **The strong law for stationary one-dependent sequences** (MT p. 436, from the strong law for
the i.i.d. even and odd subsequences): `(1/n) Σ_{j<n} Zⱼ → E[Z₀]` almost surely. -/
theorem IsOneDependent.ae_tendsto_average {Z : ℕ → Ω → ℝ} {Q : Measure Ω}
    [IsProbabilityMeasure Q] (hOD : IsOneDependent Z Q)
    (hST : IsStationarySeq Z Q) (hint : Integrable (Z 0) Q) :
    ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, Z j ω) atTop
      (𝓝 (∫ ω, Z 0 ω ∂Q)) := by
  have hid : ∀ i, IdentDistrib (Z i) (Z 0) Q Q := hST.identDistrib_coord
  have he := strong_law_ae (fun i => Z (2 * i)) (by simpa using hint)
    (fun i j hij => hOD.iIndepFun_even.indepFun hij)
    (fun i => (hid (2 * i)).trans (hid (2 * 0)).symm)
  have ho := strong_law_ae (fun i => Z (2 * i + 1)) ((hid 1).integrable_iff.2 hint)
    (fun i j hij => hOD.iIndepFun_odd.indepFun hij)
    (fun i => (hid (2 * i + 1)).trans (hid (2 * 0 + 1)).symm)
  filter_upwards [he, ho] with ω h1 h2
  refine tendsto_average_of_even_odd ?_ ?_
  · simpa [smul_eq_mul] using h1
  · have : ∫ ω, Z (2 * 0 + 1) ω ∂Q = ∫ ω, Z 0 ω ∂Q := (hid 1).integral_eq
    simpa [smul_eq_mul, this] using h2

/-! ### Covariances -/

/-- In a stationary sequence, `E[Z_k Z_{k+1}] = E[Z₀ Z₁]`. -/
theorem IsStationarySeq.integral_mul_succ {Z : ℕ → Ω → ℝ} {Q : Measure Ω}
    (hST : IsStationarySeq Z Q) (k : ℕ) :
    ∫ ω, Z k ω * Z (k + 1) ω ∂Q = ∫ ω, Z 0 ω * Z 1 ω ∂Q := by
  have h := (hST.identDistrib_comp (u := fun v => v 0 * v 1)
    ((measurable_pi_apply 0).mul (measurable_pi_apply 1)) k).integral_eq
  simpa only [add_zero] using h

/-- In a stationary sequence, `E[Z_k²] = E[Z₀²]`. -/
theorem IsStationarySeq.integral_sq {Z : ℕ → Ω → ℝ} {Q : Measure Ω}
    (hST : IsStationarySeq Z Q) (k : ℕ) :
    ∫ ω, Z k ω ^ 2 ∂Q = ∫ ω, Z 0 ω ^ 2 ∂Q :=
  ((hST.identDistrib_coord k).comp (measurable_id.pow_const 2)).integral_eq

/-! ### Big blocks and small blocks (MT (17.36)) -/

/-- The big blocks `ηᵢ = Σ_{j ≤ L} Z_{i(L+2)+j}`: blocks of `L + 1` consecutive terms, separated
by one term. -/
def bigBlock (Z : ℕ → Ω → ℝ) (L i : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range (L + 1), Z (i * (L + 2) + j) ω

/-- The big blocks are measurable. -/
theorem measurable_bigBlock {Z : ℕ → Ω → ℝ} (hZ : ∀ j, Measurable (Z j)) (L i : ℕ) :
    Measurable (bigBlock Z L i) :=
  Finset.measurable_sum _ fun _ _ => hZ _

/-- The big blocks of a one-dependent sequence are independent (MT p. 442). -/
theorem IsOneDependent.iIndepFun_bigBlock {Z : ℕ → Ω → ℝ} {Q : Measure Ω}
    [IsProbabilityMeasure Q] (hOD : IsOneDependent Z Q) (L : ℕ) :
    iIndepFun (bigBlock Z L) Q := by
  have h := iIndepFun_windowSum hOD (o := 0) (L := L + 1) (p := L + 2) (by omega) (by omega)
  have e : (fun i ω => ∑ j ∈ Finset.range (L + 1), Z (i * (L + 2) + 0 + j) ω) = bigBlock Z L :=
    funext fun i => funext fun ω => by simp only [add_zero, bigBlock]
  rwa [e] at h

/-- The big blocks of a stationary sequence are identically distributed. -/
theorem IsStationarySeq.identDistrib_bigBlock {Z : ℕ → Ω → ℝ} {Q : Measure Ω}
    (hST : IsStationarySeq Z Q) (L i : ℕ) :
    IdentDistrib (bigBlock Z L i) (bigBlock Z L 0) Q Q := by
  have h := hST.identDistrib_comp (u := fun v => ∑ j ∈ Finset.range (L + 1), v j)
    (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) (i * (L + 2))
  have e1 : (fun ω => ∑ j ∈ Finset.range (L + 1), Z (i * (L + 2) + j) ω) = bigBlock Z L i := rfl
  have e2 : (fun ω => ∑ j ∈ Finset.range (L + 1), Z j ω) = bigBlock Z L 0 :=
    funext fun ω => by simp only [bigBlock, zero_mul, zero_add]
  rw [e1, e2] at h
  exact h

omit [MeasurableSpace Ω] in
/-- The decomposition (17.36): `Σ_{j < M(L+2)} Zⱼ = Σ_{i<M} (ηᵢ + Z_{i(L+2)+L+1})`. -/
theorem sum_range_eq_bigBlock (Z : ℕ → Ω → ℝ) (L M : ℕ) (ω : Ω) :
    ∑ j ∈ Finset.range (M * (L + 2)), Z j ω =
      ∑ i ∈ Finset.range M, (bigBlock Z L i ω + Z (i * (L + 2) + (L + 1)) ω) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ← ih, show (M + 1) * (L + 2) = M * (L + 2) + (L + 1 + 1) by ring,
      Finset.sum_range_add, Finset.sum_range_succ, bigBlock]

/-- The second moment of a sum of terms with indices at least two apart is the sum of the second
moments. -/
theorem IsOneDependent.integral_sq_sum_sparse {Z : ℕ → Ω → ℝ} {Q : Measure Ω}
    [IsProbabilityMeasure Q] (hOD : IsOneDependent Z Q)
    (hST : IsStationarySeq Z Q) (h2 : MemLp (Z 0) 2 Q) (h0 : ∫ ω, Z 0 ω ∂Q = 0) {a : ℕ → ℕ}
    (ha : ∀ i, a i + 2 ≤ a (i + 1)) (M : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range M, Z (a i) ω) ^ 2 ∂Q = M * ∫ ω, Z 0 ω ^ 2 ∂Q := by
  have hid : ∀ i, IdentDistrib (Z i) (Z 0) Q Q := hST.identDistrib_coord
  have hL2 : ∀ i, MemLp (Z i) 2 Q := fun i => (hid i).memLp_iff.2 h2
  have hmean : ∀ i, ∫ ω, Z i ω ∂Q = 0 := fun i => (hid i).integral_eq.trans h0
  have hmono : ∀ i j, i < j → a i + 2 ≤ a j := by
    intro i j hij
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · have := ih h; have := ha j; omega
      · subst h; exact ha i
  induction M with
  | zero => simp
  | succ M ih =>
    have hS2 : MemLp (fun ω => ∑ i ∈ Finset.range M, Z (a i) ω) 2 Q :=
      memLp_finsetSum _ fun i _ => hL2 _
    have hcross : ∫ ω, (∑ i ∈ Finset.range M, Z (a i) ω) * Z (a M) ω ∂Q = 0 := by
      simp only [Finset.sum_mul]
      rw [integral_finsetSum (f := fun i ω => Z (a i) ω * Z (a M) ω) _
        fun i _ => (hL2 _).integrable_mul (hL2 _)]
      exact Finset.sum_eq_zero fun i hi =>
        hOD.integral_mul_eq_zero hL2 hmean (hmono i M (Finset.mem_range.1 hi))
    have hexp : (fun ω => (∑ i ∈ Finset.range (M + 1), Z (a i) ω) ^ 2) = fun ω =>
        (∑ i ∈ Finset.range M, Z (a i) ω) ^ 2 + 2 * ((∑ i ∈ Finset.range M, Z (a i) ω) *
          Z (a M) ω) + Z (a M) ω ^ 2 := by
      ext ω; rw [Finset.sum_range_succ]; ring
    have hi1 : Integrable (fun ω => (∑ i ∈ Finset.range M, Z (a i) ω) ^ 2) Q := hS2.integrable_sq
    have hi2 : Integrable (fun ω => 2 * ((∑ i ∈ Finset.range M, Z (a i) ω) * Z (a M) ω)) Q :=
      (hS2.integrable_mul (hL2 _)).const_mul 2
    have hi3 : Integrable (fun ω => Z (a M) ω ^ 2) Q := (hL2 _).integrable_sq
    have e1 := integral_add (hi1.add hi2) hi3
    have e2 := integral_add hi1 hi2
    simp only [Pi.add_apply] at e1 e2
    rw [hexp, e1, e2, ih, integral_const_mul, hcross, hST.integral_sq (a M)]
    push_cast; ring

/-! ### Characteristic functions -/

/-- `‖e^{ita} − e^{itb}‖ ≤ |t| |a − b|`. -/
theorem norm_cexp_mul_I_sub_le (t a b : ℝ) :
    ‖Complex.exp (t * a * Complex.I) - Complex.exp (t * b * Complex.I)‖ ≤ |t| * |a - b| := by
  have h1 : Complex.exp (t * a * Complex.I) - Complex.exp (t * b * Complex.I) =
      Complex.exp (t * b * Complex.I) *
        (Complex.exp (Complex.I * ((t * (a - b) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [h1, norm_mul, show (t : ℂ) * b * Complex.I = ((t * b : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul]

/-- Characteristic functions of close random variables are close:
`|φ_X(t) − φ_Y(t)| ≤ |t| E|X − Y|`. -/
theorem norm_charFun_map_sub_le {Q : Measure Ω} [IsProbabilityMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : Integrable (fun ω => X ω - Y ω) Q) (t : ℝ) :
    ‖charFun (Q.map X) t - charFun (Q.map Y) t‖ ≤ |t| * ∫ ω, |X ω - Y ω| ∂Q := by
  have hc : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I) := by fun_prop
  have hb : ∀ (V : Ω → ℝ), Measurable V →
      Integrable (fun ω => Complex.exp (t * V ω * Complex.I)) Q := fun V hV =>
    Integrable.mono' (integrable_const (1 : ℝ)) (hc.measurable.comp hV).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [show (t : ℂ) * V ω * Complex.I = ((t * V ω : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply_real, charFun_apply_real,
    integral_map hX.aemeasurable hc.aestronglyMeasurable,
    integral_map hY.aemeasurable hc.aestronglyMeasurable, ← integral_sub (hb X hX) (hb Y hY),
    ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) (hXY.abs.const_mul _)
    (Eventually.of_forall fun ω => norm_cexp_mul_I_sub_le t (X ω) (Y ω)))

/-- `E|R| ≤ √(E[R²])`. -/
theorem integral_abs_le_sqrt {Q : Measure Ω} [IsProbabilityMeasure Q] {R : Ω → ℝ}
    (hR : MemLp R 2 Q) : ∫ ω, |R ω| ∂Q ≤ √(∫ ω, R ω ^ 2 ∂Q) := by
  have habs : MemLp (fun ω => |R ω|) 2 Q := hR.abs
  have h := variance_eq_sub habs
  have h0 := variance_nonneg (fun ω => |R ω|) Q
  rw [h] at h0
  have hsq : (fun ω => |R ω|) ^ 2 = fun ω => R ω ^ 2 := funext fun ω => by
    simp only [Pi.pow_apply, sq_abs]
  rw [hsq] at h0
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- **An approximation lemma** (the end of the argument on MT p. 442): if `aₙ` is within
`e_L + f_L(n)` of `b_L(n)` for every `L`, `b_L(n) → c_L` as `n → ∞`, `c_L → ℓ`, `e_L → 0` and
`f_L(n) → 0` as `n → ∞`, then `aₙ → ℓ`. -/
theorem tendsto_of_approx {a : ℕ → ℂ} {b : ℕ → ℕ → ℂ} {c : ℕ → ℂ} {ℓ : ℂ} {e : ℕ → ℝ}
    {f : ℕ → ℕ → ℝ} (hb : ∀ L, Tendsto (b L) atTop (𝓝 (c L))) (hc : Tendsto c atTop (𝓝 ℓ))
    (he : Tendsto e atTop (𝓝 0)) (hf : ∀ L, Tendsto (f L) atTop (𝓝 0))
    (hab : ∀ L n, ‖a n - b L n‖ ≤ e L + f L n) : Tendsto a atTop (𝓝 ℓ) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 := (Metric.tendsto_atTop.1 hc) (ε / 4) (by positivity)
  have h2 := (Metric.tendsto_atTop.1 he) (ε / 4) (by positivity)
  obtain ⟨L1, hL1⟩ := h1
  obtain ⟨L2, hL2⟩ := h2
  set L := max L1 L2
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.1 (hb L)) (ε / 4) (by positivity)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.1 (hf L)) (ε / 4) (by positivity)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have i1 := hL1 L (le_max_left _ _)
  have i2 := hL2 L (le_max_right _ _)
  have i3 := hN1 n (le_of_max_le_left hn)
  have i4 := hN2 n (le_of_max_le_right hn)
  rw [Real.dist_eq, sub_zero] at i2 i4
  rw [dist_eq_norm] at i1 i3 ⊢
  have := hab L n
  calc ‖a n - ℓ‖ = ‖(a n - b L n) + (b L n - c L) + (c L - ℓ)‖ := by ring_nf
    _ ≤ ‖a n - b L n‖ + ‖b L n - c L‖ + ‖c L - ℓ‖ := norm_add₃_le
    _ < ε := by
      have : e L + f L n < ε / 2 := by
        have := le_abs_self (e L); have := le_abs_self (f L n); linarith
      linarith


/-! ### The CLT for stationary one-dependent sequences -/

/-- `(n / k : ℕ) / n → 1 / k`. -/
theorem tendsto_nat_div_div (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => ((n / k : ℕ) : ℝ) / n) atTop (𝓝 (1 / k)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (show (0 : ℝ) ≤ 1 / k by positivity)).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  congr 2
  rw [one_div_mul_eq_div, Nat.floor_div_eq_div]

/-- `n / k → ∞`. -/
theorem tendsto_nat_div_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => n / k) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b * k, fun _ hn => (Nat.le_div_iff_mul_le hk).2 hn⟩

/-- **The CLT for the big blocks**: with blocks of length `L + 1` separated by one term,
`n^{−1/2} Σ_{i < n/(L+2)} ηᵢ ⇒ N(0, σ_{L+1}²/(L+2))`, where
`σ_{L+1}² = E[η₀²] = (L + 1) E[Z₀²] + 2L E[Z₀Z₁]` (MT p. 442), stated for characteristic
functions. -/
theorem IsOneDependent.tendsto_charFun_bigBlock {Z : ℕ → Ω → ℝ} {Q : Measure Ω}
    [IsProbabilityMeasure Q] (hZ : ∀ j, Measurable (Z j)) (hOD : IsOneDependent Z Q)
    (hST : IsStationarySeq Z Q) (h2 : MemLp (Z 0) 2 Q) (h0 : ∫ ω, Z 0 ω ∂Q = 0) (L : ℕ)
    (t : ℝ) :
    Tendsto (fun n : ℕ => charFun (Q.map fun ω => (√(n : ℝ))⁻¹ *
      ∑ i ∈ Finset.range (n / (L + 2)), bigBlock Z L i ω) t) atTop
      (𝓝 (Complex.exp (-((((L + 1 : ℕ) : ℝ) * ∫ ω, Z 0 ω ^ 2 ∂Q +
        2 * (L : ℝ) * ∫ ω, Z 0 ω * Z 1 ω ∂Q) / (L + 2) : ℝ) * t ^ 2 / 2))) := by
  have hid : ∀ i, IdentDistrib (Z i) (Z 0) Q Q := hST.identDistrib_coord
  have hL2 : ∀ i, MemLp (Z i) 2 Q := fun i => (hid i).memLp_iff.2 h2
  set η := bigBlock Z L with hη
  have hηm : ∀ i, Measurable (η i) := fun i => measurable_bigBlock hZ _ i
  have hind := hOD.iIndepFun_bigBlock L
  have hident := hST.identDistrib_bigBlock L
  have hη0eq : η 0 = fun ω => ∑ j ∈ Finset.range (L + 1), Z j ω := by
    funext ω; simp [hη, bigBlock]
  have hη2 : MemLp (η 0) 2 Q := by
    rw [hη0eq]; exact memLp_finsetSum _ fun j _ => hL2 j
  have hη0 : ∫ ω, η 0 ω ∂Q = 0 := by
    rw [hη0eq, integral_finsetSum _ fun j _ => (hL2 j).integrable one_le_two]
    exact Finset.sum_eq_zero fun j _ => (hid j).integral_eq.trans h0
  set v := Var[η 0; Q] with hv
  have hvval : v = ((L + 1 : ℕ) : ℝ) * ∫ ω, Z 0 ω ^ 2 ∂Q +
      2 * (L : ℝ) * ∫ ω, Z 0 ω * Z 1 ω ∂Q := by
    rw [hv, variance_of_integral_eq_zero (hηm 0).aemeasurable hη0, hη0eq,
      hOD.integral_sq_sum hST h2 h0 (L := L + 1) (by omega)]
    push_cast; ring
  have hv0 : 0 ≤ v := variance_nonneg _ _
  -- the i.i.d. CLT for the blocks
  have hZ₀ : HasLaw (id : ℝ → ℝ) (gaussianReal 0 v.toNNReal) (gaussianReal 0 v.toNNReal) :=
    HasLaw.id
  have hCLT := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ₀ hη2 hind hident
  simp only [hη0, mul_zero, sub_zero] at hCLT
  set N : ℕ → ℕ := fun n => n / (L + 2) with hN
  have hNt : Tendsto N atTop atTop := tendsto_nat_div_atTop _ (by omega)
  have hcn : Tendsto (fun n : ℕ => √(N n : ℝ) / √(n : ℝ)) atTop (𝓝 (1 / √((L + 2 : ℕ) : ℝ))) := by
    have h1 := tendsto_nat_div_div (L + 2) (by omega)
    have h2' := (Real.continuous_sqrt.tendsto _).comp h1
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one] at h2'
    refine h2'.congr fun n => ?_
    rw [Function.comp_apply, Real.sqrt_div' _ (Nat.cast_nonneg n)]
  have hX := tendstoInDistribution_const_mul_seq (tendstoInDistribution_comp_index hCLT hNt) hcn
  have hXeq : (fun n ω => √(N n : ℝ) / √(n : ℝ) *
      ((√(N n : ℝ))⁻¹ * ∑ k ∈ Finset.range (N n), η k ω)) = fun (n : ℕ) ω =>
        (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range (n / (L + 2)), η i ω := by
    ext n ω
    rcases Nat.eq_zero_or_pos (N n) with h0' | hpos
    · rw [show n / (L + 2) = N n from rfl, h0']; simp
    · have hn : n ≠ 0 := by
        rintro rfl; simp [hN] at hpos
      have h1 : √(N n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hpos)).ne'
      have h2'' : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)).ne'
      rw [show n / (L + 2) = N n from rfl]
      field_simp
  rw [hXeq] at hX
  have hlim := hX.tendsto_charFun t
  convert hlim using 2
  symm
  simp only [id]
  rw [charFun_map_mul, charFun_gaussianReal, Real.coe_toNNReal _ hv0, hvval]
  congr 1
  have hs : (√((L + 2 : ℕ) : ℝ)) ^ 2 = ((L + 2 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hs0 : √((L + 2 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  push_cast at hs hs0 ⊢
  field_simp
  rw [show ((√((L : ℝ) + 2) : ℝ) : ℂ) ^ 2 = (L : ℂ) + 2 by
    rw [← Complex.ofReal_pow, hs]; push_cast; ring]
  ring


/-- **The small blocks are negligible** (MT p. 442): the second moment of
`Σ_{j<n} Zⱼ − Σ_{i < n/(L+2)} ηᵢ` (the separating terms and the incomplete last block) is at most
`2 (n/(L+2)) E[Z₀²] + 2 (L+1)² E[Z₀²]`. -/
theorem IsOneDependent.integral_sq_sub_bigBlock_le {Z : ℕ → Ω → ℝ} {Q : Measure Ω}
    [IsProbabilityMeasure Q] (hOD : IsOneDependent Z Q)
    (hST : IsStationarySeq Z Q) (h2 : MemLp (Z 0) 2 Q) (h0 : ∫ ω, Z 0 ω ∂Q = 0) (L n : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range n, Z j ω -
        ∑ i ∈ Finset.range (n / (L + 2)), bigBlock Z L i ω) ^ 2 ∂Q ≤
      2 * ((n / (L + 2) : ℕ) : ℝ) * ∫ ω, Z 0 ω ^ 2 ∂Q +
        2 * (((L + 1 : ℕ) : ℝ) ^ 2 * ∫ ω, Z 0 ω ^ 2 ∂Q) := by
  have hid : ∀ i, IdentDistrib (Z i) (Z 0) Q Q := hST.identDistrib_coord
  have hL2 : ∀ i, MemLp (Z i) 2 Q := fun i => (hid i).memLp_iff.2 h2
  have hc0 : 0 ≤ ∫ ω, Z 0 ω ^ 2 ∂Q := integral_nonneg fun ω => sq_nonneg _
  set M := n / (L + 2) with hM
  set r := n % (L + 2) with hr
  have hrL : r ≤ L + 1 := by
    have := Nat.mod_lt n (show 0 < L + 2 by omega); omega
  have hn : n = M * (L + 2) + r := by
    rw [hM, hr, mul_comm]; exact (Nat.div_add_mod n (L + 2)).symm
  set A : Ω → ℝ := fun ω => ∑ i ∈ Finset.range M, Z (i * (L + 2) + (L + 1)) ω with hA
  set B : Ω → ℝ := fun ω => ∑ l ∈ Finset.range r, Z (M * (L + 2) + l) ω with hB
  have hdec : ∀ ω, ∑ j ∈ Finset.range n, Z j ω -
      ∑ i ∈ Finset.range M, bigBlock Z L i ω = A ω + B ω := by
    intro ω
    have h1 := sum_range_eq_bigBlock Z L M ω
    rw [show L + 1 + 1 = L + 2 by ring] at h1
    rw [hn, Finset.sum_range_add, h1, Finset.sum_add_distrib]
    simp only [hA, hB]
    ring
  have hAm : MemLp A 2 Q := memLp_finsetSum _ fun i _ => hL2 _
  have hBm : MemLp B 2 Q := memLp_finsetSum _ fun i _ => hL2 _
  have hA2 : ∫ ω, A ω ^ 2 ∂Q = M * ∫ ω, Z 0 ω ^ 2 ∂Q :=
    hOD.integral_sq_sum_sparse hST h2 h0 (a := fun i => i * (L + 2) + (L + 1))
      (fun i => by simp only [add_mul, one_mul]; omega) M
  have hB2 : ∫ ω, B ω ^ 2 ∂Q ≤ ((L + 1 : ℕ) : ℝ) ^ 2 * ∫ ω, Z 0 ω ^ 2 ∂Q := by
    have hpt : ∀ ω, B ω ^ 2 ≤ r * ∑ l ∈ Finset.range r, Z (M * (L + 2) + l) ω ^ 2 := by
      intro ω
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range r)
        (f := fun l => Z (M * (L + 2) + l) ω)
      simpa [hB] using this
    have hint : Integrable (fun ω => (r : ℝ) * ∑ l ∈ Finset.range r,
        Z (M * (L + 2) + l) ω ^ 2) Q :=
      (integrable_finsetSum _ fun l _ => (hL2 _).integrable_sq).const_mul _
    calc ∫ ω, B ω ^ 2 ∂Q ≤ ∫ ω, (r : ℝ) * ∑ l ∈ Finset.range r,
          Z (M * (L + 2) + l) ω ^ 2 ∂Q := integral_mono hBm.integrable_sq hint hpt
      _ = (r : ℝ) * (r * ∫ ω, Z 0 ω ^ 2 ∂Q) := by
          rw [integral_const_mul, integral_finsetSum _ fun l _ => (hL2 _).integrable_sq]
          simp_rw [hST.integral_sq]
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((L + 1 : ℕ) : ℝ) ^ 2 * ∫ ω, Z 0 ω ^ 2 ∂Q := by
          rw [← mul_assoc, ← sq]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _)
            (by exact_mod_cast hrL) 2) hc0
  have hpt : ∀ ω, (∑ j ∈ Finset.range n, Z j ω -
      ∑ i ∈ Finset.range M, bigBlock Z L i ω) ^ 2 ≤ 2 * A ω ^ 2 + 2 * B ω ^ 2 := by
    intro ω
    rw [hdec]
    nlinarith [sq_nonneg (A ω - B ω)]
  calc ∫ ω, (∑ j ∈ Finset.range n, Z j ω -
        ∑ i ∈ Finset.range M, bigBlock Z L i ω) ^ 2 ∂Q
      ≤ ∫ ω, (2 * A ω ^ 2 + 2 * B ω ^ 2) ∂Q := by
        refine integral_mono ?_ ((hAm.integrable_sq.const_mul 2).add
          (hBm.integrable_sq.const_mul 2)) hpt
        have : (fun ω => (∑ j ∈ Finset.range n, Z j ω -
            ∑ i ∈ Finset.range M, bigBlock Z L i ω) ^ 2) = fun ω => (A ω + B ω) ^ 2 :=
          funext fun ω => by rw [hdec]
        rw [this]; exact (hAm.add hBm).integrable_sq
    _ = 2 * ∫ ω, A ω ^ 2 ∂Q + 2 * ∫ ω, B ω ^ 2 ∂Q := by
        rw [integral_add (hAm.integrable_sq.const_mul 2) (hBm.integrable_sq.const_mul 2),
          integral_const_mul, integral_const_mul]
    _ ≤ _ := by rw [hA2]; linarith


/-- The asymptotic variance `σ̄² = E[Z₀²] + 2 E[Z₀ Z₁]` of a stationary one-dependent sequence
(MT p. 442). -/
noncomputable def oneDepVariance (Z : ℕ → Ω → ℝ) (Q : Measure Ω) : ℝ :=
  ∫ ω, Z 0 ω ^ 2 ∂Q + 2 * ∫ ω, Z 0 ω * Z 1 ω ∂Q

/-- `σ̄² ≥ 0`: it is the limit of `E[(Σ_{j<n} Zⱼ)²]/n`. -/
theorem IsOneDependent.oneDepVariance_nonneg {Z : ℕ → Ω → ℝ} {Q : Measure Ω}
    [IsProbabilityMeasure Q] (hOD : IsOneDependent Z Q)
    (hST : IsStationarySeq Z Q) (h2 : MemLp (Z 0) 2 Q) (h0 : ∫ ω, Z 0 ω ∂Q = 0) :
    0 ≤ oneDepVariance Z Q := by
  by_contra hneg
  push Not at hneg
  set σ := oneDepVariance Z Q with hσ
  set c1 := ∫ ω, Z 0 ω * Z 1 ω ∂Q with hc1
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * c1 / σ)
  have h1 := hOD.integral_sq_sum hST h2 h0 (L := n + 1) (by omega)
  have hpos : 0 ≤ ∫ ω, (∑ j ∈ Finset.range (n + 1), Z j ω) ^ 2 ∂Q :=
    integral_nonneg fun ω => sq_nonneg _
  rw [h1] at hpos
  have h3 : ((n + 1 : ℕ) : ℝ) * σ < 2 * c1 := by
    have : 2 * c1 / σ < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    rwa [div_lt_iff_of_neg hneg] at this
  have h4 : ((n + 1 : ℕ) : ℝ) * ∫ ω, Z 0 ω ^ 2 ∂Q + 2 * (((n + 1 : ℕ) : ℝ) - 1) * c1 =
      ((n + 1 : ℕ) : ℝ) * σ - 2 * c1 := by
    rw [hσ, oneDepVariance]; push_cast; ring
  linarith

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem sqrt_add_le_add_sqrt' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b :=
  calc √(a + b) ≤ √((√a + √b) ^ 2) := Real.sqrt_le_sqrt (by
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b])
    _ = √a + √b := Real.sqrt_sq (by positivity)

/-- **The CLT for stationary one-dependent sequences** (MT p. 442): for a centred stationary
one-dependent sequence in `L²`, `n^{−1/2} Σ_{j<n} Zⱼ ⇒ N(0, σ̄²)` with
`σ̄² = E[Z₀²] + 2 E[Z₀ Z₁]`. The proof is the book's big-block/small-block argument (17.36): the
big blocks are i.i.d. (Mathlib's CLT), the small blocks are negligible in `L²` uniformly in `n`
as the block length grows, and the characteristic functions are compared. -/
theorem IsOneDependent.tendstoInDistribution {Z : ℕ → Ω → ℝ} {Q : Measure Ω}
    [IsProbabilityMeasure Q] (hZ : ∀ j, Measurable (Z j)) (hOD : IsOneDependent Z Q)
    (hST : IsStationarySeq Z Q) (h2 : MemLp (Z 0) 2 Q) (h0 : ∫ ω, Z 0 ω ∂Q = 0)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z' : Ω' → ℝ}
    (hZ' : HasLaw Z' (gaussianReal 0 (oneDepVariance Z Q).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ j ∈ Finset.range n, Z j ω) atTop Z'
      (fun _ => Q) P' := by
  have hid : ∀ i, IdentDistrib (Z i) (Z 0) Q Q := hST.identDistrib_coord
  have hL2 : ∀ i, MemLp (Z i) 2 Q := fun i => (hid i).memLp_iff.2 h2
  set c0 := ∫ ω, Z 0 ω ^ 2 ∂Q with hc0def
  set c1 := ∫ ω, Z 0 ω * Z 1 ω ∂Q with hc1def
  set σ := oneDepVariance Z Q with hσdef
  have hσ0 : 0 ≤ σ := hOD.oneDepVariance_nonneg hST h2 h0
  have hc0 : 0 ≤ c0 := integral_nonneg fun ω => sq_nonneg _
  have hXm : ∀ n : ℕ, Measurable fun ω => (√(n : ℝ))⁻¹ * ∑ j ∈ Finset.range n, Z j ω :=
    fun n => measurable_const.mul (Finset.measurable_sum _ fun j _ => hZ j)
  have hYm : ∀ L n : ℕ, Measurable fun ω => (√(n : ℝ))⁻¹ *
      ∑ i ∈ Finset.range (n / (L + 2)), bigBlock Z L i ω :=
    fun L n => measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      measurable_bigBlock hZ _ i)
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hXm n).aemeasurable)
    hZ'.aemeasurable fun t => ?_
  rw [hZ'.map_eq, charFun_gaussianReal, Real.coe_toNNReal _ hσ0]
  have htarget : Complex.exp (t * (0 : ℝ) * Complex.I - (σ : ℂ) * t ^ 2 / 2) =
      Complex.exp (-((σ : ℝ) : ℂ) * t ^ 2 / 2) := by congr 1; push_cast; ring
  rw [htarget]
  refine tendsto_of_approx (b := fun L n => charFun (Q.map fun ω => (√(n : ℝ))⁻¹ *
      ∑ i ∈ Finset.range (n / (L + 2)), bigBlock Z L i ω) t)
    (c := fun L => Complex.exp (-((((L + 1 : ℕ) : ℝ) * c0 + 2 * (L : ℝ) * c1) / (L + 2) : ℝ) *
      t ^ 2 / 2))
    (e := fun L => |t| * √(2 * c0 / (L + 2)))
    (f := fun L n => |t| * √(2 * (((L + 1 : ℕ) : ℝ) ^ 2 * c0) / n))
    (fun L => hOD.tendsto_charFun_bigBlock hZ hST h2 h0 L t) ?_ ?_ ?_ ?_
  · -- the block variances converge to `σ̄²`
    have hr : Tendsto (fun L : ℕ => (((L + 1 : ℕ) : ℝ) * c0 + 2 * (L : ℝ) * c1) / (L + 2))
        atTop (𝓝 σ) := by
      have h1 : Tendsto (fun L : ℕ => ((L + 1 : ℕ) : ℝ) / (((L + 1 : ℕ) : ℝ) + 1)) atTop
          (𝓝 1) := (tendsto_natCast_div_add_atTop (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
      have h2' : Tendsto (fun L : ℕ => 2 * c1 / ((L : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have := (h1.const_mul σ).sub h2'
      rw [mul_one, sub_zero] at this
      refine this.congr fun L => ?_
      have hL : ((L : ℝ) + 2) ≠ 0 := by positivity
      rw [hσdef, oneDepVariance]
      push_cast
      field_simp
      ring
    have hcont : Continuous fun x : ℝ => Complex.exp (-(x : ℂ) * t ^ 2 / 2) := by fun_prop
    exact (hcont.tendsto σ).comp hr
  · -- `e_L → 0`
    have : Tendsto (fun L : ℕ => 2 * c0 / ((L : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h := ((Real.continuous_sqrt.tendsto 0).comp this).const_mul |t|
    rw [Real.sqrt_zero, mul_zero] at h
    exact h
  · -- `f_L(n) → 0`
    intro L
    have : Tendsto (fun n : ℕ => 2 * (((L + 1 : ℕ) : ℝ) ^ 2 * c0) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h := ((Real.continuous_sqrt.tendsto 0).comp this).const_mul |t|
    rw [Real.sqrt_zero, mul_zero] at h
    exact h
  · -- the comparison of characteristic functions
    intro L n
    set S : Ω → ℝ := fun ω => ∑ j ∈ Finset.range n, Z j ω -
      ∑ i ∈ Finset.range (n / (L + 2)), bigBlock Z L i ω with hS
    have hSm : MemLp S 2 Q := (memLp_finsetSum _ fun j _ => hL2 j).sub
      (memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun l _ => hL2 _)
    have hdiff : (fun ω => (√(n : ℝ))⁻¹ * ∑ j ∈ Finset.range n, Z j ω -
        (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range (n / (L + 2)), bigBlock Z L i ω) =
        fun ω => (√(n : ℝ))⁻¹ * S ω := funext fun ω => by rw [hS, mul_sub]
    have hRm : MemLp (fun ω => (√(n : ℝ))⁻¹ * S ω) 2 Q := hSm.const_mul _
    have hint : Integrable (fun ω => (√(n : ℝ))⁻¹ * ∑ j ∈ Finset.range n, Z j ω -
        (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range (n / (L + 2)), bigBlock Z L i ω) Q := by
      rw [hdiff]; exact hRm.integrable one_le_two
    have h1 := norm_charFun_map_sub_le (hXm n) (hYm L n) hint t
    have hdiff' : ∀ ω, (√(n : ℝ))⁻¹ * ∑ j ∈ Finset.range n, Z j ω -
        (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range (n / (L + 2)), bigBlock Z L i ω =
        (√(n : ℝ))⁻¹ * S ω := fun ω => congrFun hdiff ω
    simp_rw [hdiff'] at h1
    refine h1.trans ?_
    have h3 := integral_abs_le_sqrt hRm
    have hsq : ∫ ω, ((√(n : ℝ))⁻¹ * S ω) ^ 2 ∂Q = (n : ℝ)⁻¹ * ∫ ω, S ω ^ 2 ∂Q := by
      simp_rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      exact integral_const_mul _ _
    have hS2 := hOD.integral_sq_sub_bigBlock_le hST h2 h0 L n
    have hM : ((n / (L + 2) : ℕ) : ℝ) * (n : ℝ)⁻¹ ≤ 1 / ((L : ℝ) + 2) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [Nat.zero_div, CharP.cast_eq_zero, inv_zero, mul_zero, one_div, inv_nonneg]
        positivity
      · have : ((n / (L + 2) : ℕ) : ℝ) ≤ (n : ℝ) / ((L + 2 : ℕ) : ℝ) := Nat.cast_div_le
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [← div_eq_mul_inv, div_le_iff₀ hn']
        push_cast at this
        calc ((n / (L + 2) : ℕ) : ℝ) ≤ (n : ℝ) / ((L : ℝ) + 2) := this
          _ = 1 / ((L : ℝ) + 2) * n := by ring
    have hbound : (n : ℝ)⁻¹ * ∫ ω, S ω ^ 2 ∂Q ≤
        2 * c0 / ((L : ℝ) + 2) + 2 * (((L + 1 : ℕ) : ℝ) ^ 2 * c0) / n := by
      have hninv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg n)
      calc (n : ℝ)⁻¹ * ∫ ω, S ω ^ 2 ∂Q ≤ (n : ℝ)⁻¹ * (2 * ((n / (L + 2) : ℕ) : ℝ) * c0 +
            2 * (((L + 1 : ℕ) : ℝ) ^ 2 * c0)) := mul_le_mul_of_nonneg_left hS2 hninv
        _ = 2 * c0 * (((n / (L + 2) : ℕ) : ℝ) * (n : ℝ)⁻¹) +
            2 * (((L + 1 : ℕ) : ℝ) ^ 2 * c0) / n := by ring
        _ ≤ 2 * c0 * (1 / ((L : ℝ) + 2)) + 2 * (((L + 1 : ℕ) : ℝ) ^ 2 * c0) / n := by
            gcongr
        _ = _ := by ring
    have hab0 : 0 ≤ 2 * c0 / ((L : ℝ) + 2) := by positivity
    have hab1 : 0 ≤ 2 * (((L + 1 : ℕ) : ℝ) ^ 2 * c0) / n := by positivity
    calc |t| * ∫ ω, |(√(n : ℝ))⁻¹ * S ω| ∂Q ≤ |t| * √(∫ ω, ((√(n : ℝ))⁻¹ * S ω) ^ 2 ∂Q) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg t)
      _ ≤ |t| * √(2 * c0 / ((L : ℝ) + 2) + 2 * (((L + 1 : ℕ) : ℝ) ^ 2 * c0) / n) := by
          rw [hsq]; gcongr
      _ ≤ |t| * (√(2 * c0 / ((L : ℝ) + 2)) + √(2 * (((L + 1 : ℕ) : ℝ) ^ 2 * c0) / n)) :=
          mul_le_mul_of_nonneg_left (sqrt_add_le_add_sqrt' hab0 hab1) (abs_nonneg t)
      _ = _ := by ring


/-! ### The random-index step -/

/-- `Σ_{j<K} zⱼ = Σ_{i<⌈K/2⌉} z_{2i} + Σ_{i<⌊K/2⌋} z_{2i+1}`. -/
theorem sum_range_eq_even_odd (z : ℕ → ℝ) (K : ℕ) :
    ∑ j ∈ Finset.range K, z j =
      ∑ i ∈ Finset.range ((K + 1) / 2), z (2 * i) + ∑ i ∈ Finset.range (K / 2), z (2 * i + 1) := by
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' K
  · rw [sum_range_two_mul, show (2 * a + 1) / 2 = a by omega, show 2 * a / 2 = a by omega]
  · rw [Finset.sum_range_succ, sum_range_two_mul, show (2 * a + 1 + 1) / 2 = a + 1 by omega,
      show (2 * a + 1) / 2 = a by omega, Finset.sum_range_succ]
    ring

/-- The sum of two sequences tending to `0` in probability tends to `0` in probability. -/
theorem tendstoInMeasure_add_zero {Q : Measure Ω} {f g : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure Q f atTop fun _ => 0) (hg : TendstoInMeasure Q g atTop fun _ => 0) :
    TendstoInMeasure Q (fun n ω => f n ω + g n ω) atTop fun _ => 0 := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have h := (hf (ε / 2) (by positivity)).add (hg (ε / 2) (by positivity))
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun n => ?_
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [sub_zero, mem_ofPred_eq, mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  have := norm_add_le (f n ω) (g n ω)
  linarith [hcon.1, hcon.2]

/-- If `kₙ/n → c`, then `⌊(kₙ + a)/2⌋/n → c/2` for `a ≤ 1`. -/
theorem tendsto_half_index {k : ℕ → ℕ} {c : ℝ} (h : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 c))
    {a : ℕ} (ha : a ≤ 1) :
    Tendsto (fun n => (((k n + a) / 2 : ℕ) : ℝ) / n) atTop (𝓝 (c / 2)) := by
  have h1 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlo := (h.div_const 2).sub h1
  have hhi := (h.div_const 2).add h1
  rw [sub_zero] at hlo
  rw [add_zero] at hhi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n => ?_) fun n => ?_
  · have e1 := Nat.div_add_mod (k n + a) 2
    have e2 := Nat.mod_lt (k n + a) (show 0 < 2 by omega)
    have h2 : ((k n : ℝ) - 1) / 2 ≤ (((k n + a) / 2 : ℕ) : ℝ) := by
      have : k n ≤ 2 * ((k n + a) / 2) + 1 := by omega
      have := (Nat.cast_le (α := ℝ)).2 this
      push_cast at this; linarith
    calc (k n : ℝ) / n / 2 - 1 / 2 / n = (((k n : ℝ) - 1) / 2) / n := by ring
      _ ≤ _ := div_le_div_of_nonneg_right h2 (Nat.cast_nonneg n)
  · have e1 := Nat.div_add_mod (k n + a) 2
    have h2 : (((k n + a) / 2 : ℕ) : ℝ) ≤ ((k n : ℝ) + 1) / 2 := by
      have : 2 * ((k n + a) / 2) ≤ k n + 1 := by omega
      have := (Nat.cast_le (α := ℝ)).2 this
      push_cast at this; linarith
    calc (((k n + a) / 2 : ℕ) : ℝ) / n ≤ (((k n : ℝ) + 1) / 2) / n :=
          div_le_div_of_nonneg_right h2 (Nat.cast_nonneg n)
      _ = (k n : ℝ) / n / 2 + 1 / 2 / n := by ring


/-- **The random-index step for one-dependent sequences** (MT (17.35), from Kolmogorov's
inequality for the i.i.d. even and odd subsequences): if `Kₙ/n → c > 0` almost surely, then
`(Σ_{j<Kₙ} Zⱼ − Σ_{j<2⌊cn/2⌋} Zⱼ)/√n → 0` in probability. -/
theorem IsOneDependent.tendstoInMeasure_randomIndex {Z : ℕ → Ω → ℝ} {Q : Measure Ω}
    [IsProbabilityMeasure Q] (hZ : ∀ j, Measurable (Z j)) (hOD : IsOneDependent Z Q)
    (hST : IsStationarySeq Z Q) (h2 : MemLp (Z 0) 2 Q) (h0 : ∫ ω, Z 0 ω ∂Q = 0)
    {K : ℕ → Ω → ℕ} (hKm : ∀ n, Measurable (K n)) {c : ℝ} (hc : 0 < c)
    (hK : ∀ᵐ ω ∂Q, Tendsto (fun n => (K n ω : ℝ) / n) atTop (𝓝 c)) :
    TendstoInMeasure Q (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * (∑ j ∈ Finset.range (K n ω), Z j ω -
      ∑ j ∈ Finset.range (2 * ⌊c / 2 * n⌋₊), Z j ω)) atTop (fun _ => 0) := by
  have hid : ∀ i, IdentDistrib (Z i) (Z 0) Q Q := hST.identDistrib_coord
  have hc2 : 0 < c / 2 := by positivity
  have hKe : ∀ᵐ ω ∂Q, Tendsto (fun n => (((K n ω + 1) / 2 : ℕ) : ℝ) / n) atTop
      (𝓝 (c / 2)) := by
    filter_upwards [hK] with ω hω using tendsto_half_index hω le_rfl
  have hKo : ∀ᵐ ω ∂Q, Tendsto (fun n => (((K n ω + 0) / 2 : ℕ) : ℝ) / n) atTop
      (𝓝 (c / 2)) := by
    filter_upwards [hK] with ω hω using tendsto_half_index hω (Nat.zero_le 1)
  have hE := tendstoInMeasure_anscombe hOD.iIndepFun_even (fun i => hZ (2 * i))
    (fun i => (hid (2 * i)).trans (hid (2 * 0)).symm) (by simpa using h2) (by simpa using h0)
    (fun n => ((hKm n).add_const 1).div_const 2) hc2 hKe
  have hO := tendstoInMeasure_anscombe hOD.iIndepFun_odd (fun i => hZ (2 * i + 1))
    (fun i => (hid (2 * i + 1)).trans (hid (2 * 0 + 1)).symm) ((hid 1).memLp_iff.2 h2)
    ((hid 1).integral_eq.trans h0) (fun n => ((hKm n).add_const 0).div_const 2) hc2 hKo
  refine (tendstoInMeasure_add_zero hE hO).congr_left fun n => Eventually.of_forall fun ω => ?_
  simp only [add_zero]
  rw [sum_range_eq_even_odd (fun j => Z j ω) (K n ω), sum_range_two_mul]
  ring

end MeynTweedie.LimitTheorems
