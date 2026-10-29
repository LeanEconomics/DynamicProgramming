/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.MG1Invariant
import Positivity.LadderChains

/-!
# Invariant measures of ladder chains (MT §10.5.3)

Meyn and Tweedie, §10.5.3, pp. 249–251. `P = ladderChainKernel Λ Λ*` is the ladder chain (3.40)
on `ℤ₊ × ℝ` (`LadderChains`). The bottom rung is `[0] = {0} × ℝ`; `rung k = {k} × ℝ` and
`aboveRung k = {(i, x) : i > k}`.

**Kernels.** `ladL k = I_{(k, ∞)} P` ("move by `P`, kill at levels `≤ k`"); `Q = ladL 0` kills at
`[0]`, and its powers are the taboo probabilities `_{[0]}Pⁿ⁺¹` off `[0]`
(`tabooKernel_eq_ladQ_pow`).
`ladderS k` is the kernel `S^{(k)}(y, A) = U_{[0]}(0, y; k × A)` of (10.42), and `ladS = S^{(1)}`.

**Tools.**
* `ext_nat_prod`, `lintegral_nat_prod`: measures on `ℤ₊ × ℝ` are determined by the rectangles
  `{j} × A`, and integrals split over the rungs.
* `restrict_pow_comp_decomp`: the last-exit decomposition through a set `Dᶜ`:
  `(ρQⁿ)|_D = ρ|_D (I_D Q)ⁿ + Σ_{j < n} (ρQʲ)|_{Dᶜ} (I_D Q)^{n−j}`.
* `ladL_pow_translate` (10.44): above rung `k` the chain killed below `k + 1` is the chain killed
  at `[0]`, shifted by `k`.
* `ladL_pow_apply_of_lt`: from below rung `k`, the chain cannot jump above rung `k` (skip-free
  to the right).

**Results.**
* `ladderS_succ` (10.45): `S^{(k+1)} = S^{(k)} S` for `k ≥ 1`, the last-exit decomposition over
  the last visit to `[k]`, which happens at rung `k`; `ladderS_eq_pow` (10.39): `S^{(k)} = Sᵏ`.
* `ladS_eq` (10.40), (10.46): `S = Σₖ Sᵏ Λₖ`.
* `ladS_minimal` (10.47)–(10.51): `S` is the minimal solution of (10.40).
* **Theorem 10.5.3** (`theorem_10_5_3`, p. 249): for a recurrent ladder chain with `ψ([0]) > 0` and
  an invariant measure `π` with `π([0]) < ∞`, `π(k × A) = ∫ π₀(dy) Sᵏ(y, A)` (10.38), where `π₀` is
  `π` on the bottom rung.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped ENNReal

/-! ### Measures on `ℤ₊ × ℝ` -/

/-- The rung `{k} × ℝ`. -/
def rung (k : ℕ) : Set (ℕ × ℝ) := {k} ×ˢ univ

/-- The levels above `k`: `{(i, x) : i > k}`. -/
def aboveRung (k : ℕ) : Set (ℕ × ℝ) := {p | k < p.1}

/-- Rungs are measurable. -/
theorem measurableSet_rung (k : ℕ) : MeasurableSet (rung k) :=
  (measurableSet_singleton k).prod MeasurableSet.univ

/-- The levels above `k` form a measurable set. -/
theorem measurableSet_aboveRung (k : ℕ) : MeasurableSet (aboveRung k) :=
  measurable_fst (measurableSet_Ioi (a := k))

/-- The bottom rung is the complement of the levels above `0`. -/
theorem rung_zero_compl : (rung 0)ᶜ = aboveRung 0 := by
  ext p; simp [rung, aboveRung, Nat.pos_iff_ne_zero]

/-- A measure on `ℤ₊ × ℝ` is determined by its values on the rectangles `{j} × A`. -/
theorem ext_nat_prod {μ ν : Measure (ℕ × ℝ)}
    (h : ∀ j (A : Set ℝ), MeasurableSet A → μ ({j} ×ˢ A) = ν ({j} ×ˢ A)) : μ = ν := by
  ext S hS
  have hU : S = ⋃ j : ℕ, {j} ×ˢ (Prod.mk j ⁻¹' S) := by
    ext p; simp
  have hm : ∀ j, MeasurableSet ({j} ×ˢ (Prod.mk j ⁻¹' S) : Set (ℕ × ℝ)) := fun j =>
    (measurableSet_singleton j).prod (measurable_prodMk_left hS)
  have hd : Pairwise (Disjoint on fun j : ℕ => ({j} ×ˢ (Prod.mk j ⁻¹' S) : Set (ℕ × ℝ))) :=
    fun i j hij => Set.disjoint_left.2 fun p hp hq => hij (hp.1.symm.trans hq.1)
  rw [hU, measure_iUnion hd hm, measure_iUnion hd hm]
  exact tsum_congr fun j => h j _ (measurable_prodMk_left hS)

/-- Integrals over `ℤ₊ × ℝ` split over the rungs:
`∫ f dμ = Σₖ ∫ f(k, w) μ(k × dw)`. -/
theorem lintegral_nat_prod (μ : Measure (ℕ × ℝ)) {f : ℕ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂μ = ∑' k, ∫⁻ w, f (k, w) ∂(μ.restrict (rung k)).map Prod.snd := by
  have hU : (⋃ k, rung k) = univ := eq_univ_of_forall fun p => mem_iUnion.2 ⟨p.1, by simp [rung]⟩
  have hd : Pairwise (Disjoint on rung) :=
    fun i j hij => Set.disjoint_left.2 fun p hp hq => hij (hp.1.symm.trans hq.1)
  rw [← setLIntegral_univ, ← hU, lintegral_iUnion measurableSet_rung hd]
  refine tsum_congr fun k => ?_
  have hg : Measurable fun w : ℝ => f (k, w) := hf.comp measurable_prodMk_left
  rw [lintegral_map hg measurable_snd]
  refine setLIntegral_congr_fun (measurableSet_rung k) fun p hp => ?_
  have : p = (k, p.2) := Prod.ext hp.1 rfl
  rw [← this]

/-- `(μ restricted to rung k ∘ snd⁻¹)(A) = μ(k × A)`. -/
theorem map_snd_restrict_rung_apply (μ : Measure (ℕ × ℝ)) (k : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) : ((μ.restrict (rung k)).map Prod.snd) A = μ ({k} ×ˢ A) := by
  rw [Measure.map_apply measurable_snd hA, Measure.restrict_apply (measurable_snd hA)]
  congr 1
  ext p; simp [rung, and_comm]

/-! ### Composition lemmas -/

variable {Y : Type*} [MeasurableSpace Y]

/-- `K ∘ₘ Σ_{j ∈ s} mⱼ = Σ_{j ∈ s} K ∘ₘ mⱼ`. -/
theorem comp_finset_sum_measure (K : Kernel Y Y) (m : ℕ → Measure Y) (s : Finset ℕ) :
    K ∘ₘ (∑ j ∈ s, m j) = ∑ j ∈ s, K ∘ₘ m j := by
  induction s using Finset.induction_on with
  | empty => simp [Measure.bind_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.comp_add, ih]

/-- `L ∘ₘ (Lᵃ ∘ₘ m) = Lᵃ⁺¹ ∘ₘ m`. -/
theorem comp_pow_comp (L : Kernel Y Y) (a : ℕ) (m : Measure Y) :
    L ∘ₘ ((L ^ a : Kernel Y Y) ∘ₘ m) = (L ^ (a + 1) : Kernel Y Y) ∘ₘ m := by
  rw [Measure.comp_assoc, pow_add_eq L a 1, pow_one]

/-- The last-exit decomposition through `Dᶜ`:
`(ρQⁿ)|_D = ρ|_D (I_D Q)ⁿ + Σ_{j < n} (ρQʲ)|_{Dᶜ} (I_D Q)^{n−j}`. -/
theorem restrict_pow_comp_decomp (Q : Kernel Y Y) {D : Set Y} (hD : MeasurableSet D)
    (ρ : Measure Y) (n : ℕ) :
    ((Q ^ n : Kernel Y Y) ∘ₘ ρ).restrict D =
      ((indKernel hD ∘ₖ Q) ^ n : Kernel Y Y) ∘ₘ ρ.restrict D +
        ∑ j ∈ Finset.range n, ((indKernel hD ∘ₖ Q) ^ (n - j) : Kernel Y Y) ∘ₘ
          ((Q ^ j : Kernel Y Y) ∘ₘ ρ).restrict Dᶜ := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Finset.range_zero, Finset.sum_empty, add_zero]
    change (Kernel.id ∘ₘ ρ).restrict D = Kernel.id ∘ₘ ρ.restrict D
    rw [Measure.id_comp, Measure.id_comp]
  | succ n ih =>
    have e1 : ((Q ^ (n + 1) : Kernel Y Y) ∘ₘ ρ).restrict D =
        (indKernel hD ∘ₖ Q) ∘ₘ ((Q ^ n : Kernel Y Y) ∘ₘ ρ) := by
      rw [pow_add_eq Q n 1, pow_one, ← Measure.comp_assoc, ← Measure.comp_assoc,
        indKernel_comp_eq_restrict]
    rw [e1]
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := (Q ^ n : Kernel Y Y) ∘ₘ ρ) hD]
    rw [Measure.comp_add, ih, Measure.comp_add, comp_finset_sum_measure, comp_pow_comp,
      Finset.sum_range_succ]
    simp_rw [comp_pow_comp]
    rw [show n + 1 - n = 1 by omega, pow_one, add_assoc]
    congr 2
    exact Finset.sum_congr rfl fun j hj => by
      rw [show n + 1 - j = n - j + 1 by simp only [Finset.mem_range] at hj; omega]

/-- `I_D (I_{D'} P) = I_D P` for `D ⊆ D'`. -/
theorem indKernel_comp_indKernel_comp (P : Kernel Y Y) {D D' : Set Y} (hD : MeasurableSet D)
    (hD' : MeasurableSet D') (hsub : D ⊆ D') :
    indKernel hD ∘ₖ (indKernel hD' ∘ₖ P) = indKernel hD ∘ₖ P := by
  ext x S hS
  rw [comp_indKernel_apply _ hD x hS, comp_indKernel_apply _ hD' x (hS.inter hD),
    comp_indKernel_apply _ hD x hS, inter_assoc, inter_eq_left.2 hsub]

/-! ### The ladder chain killed at `[0]` and above rung `k` -/

variable (Λ Λs : ℕ → Kernel ℝ ℝ)

/-- The ladder chain killed outside the levels above `k`: `I_{(k, ∞)} P`. -/
noncomputable def ladL (k : ℕ) : Kernel (ℕ × ℝ) (ℕ × ℝ) :=
  indKernel (measurableSet_aboveRung k) ∘ₖ ladderChainKernel Λ Λs

/-- The shift `(i, x) ↦ (i + k, x)`. -/
def rungShift (k : ℕ) (p : ℕ × ℝ) : ℕ × ℝ := (p.1 + k, p.2)

/-- The shift is measurable. -/
theorem measurable_rungShift (k : ℕ) : Measurable (rungShift k) :=
  (measurable_fst.add_const k).prodMk measurable_snd

/-- Iterated translation invariance (10.44): `P(i + k, x; (j + k) × A) = P(i, x; j × A)` for
`j ≥ 1`. -/
theorem ladder_translate_iter {i j : ℕ} (hj : 1 ≤ j) (k : ℕ) (x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ladderChainKernel Λ Λs (i + k, x) ({j + k} ×ˢ A) =
      ladderChainKernel Λ Λs (i, x) ({j} ×ˢ A) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show i + (k + 1) = i + k + 1 by omega, show j + (k + 1) = j + k + 1 by omega,
      ladderChainKernel_translate Λ Λs (by omega) x hA, ih]

/-- The ladder chain does not jump above rung `i + 1`: `P(i, x; (i + 1, ∞)) = 0`. -/
theorem ladder_apply_aboveRung_succ (i : ℕ) (x : ℝ) :
    ladderChainKernel Λ Λs (i, x) (aboveRung (i + 1)) = 0 := by
  have hU : aboveRung (i + 1) = ⋃ j : ℕ, {j + (i + 2)} ×ˢ (univ : Set ℝ) := by
    ext p
    simp only [aboveRung, mem_ofPred_eq, mem_iUnion, mem_prod, mem_singleton_iff, mem_univ,
      and_true]
    exact ⟨fun h => ⟨p.1 - (i + 2), by omega⟩, fun ⟨j, hj⟩ => by omega⟩
  rw [hU]
  exact measure_iUnion_null fun j => eq_3_40_up Λ Λs (by omega) x MeasurableSet.univ

/-- One step of the translation: `L_k(i + k, w) = Q(i, w) ∘ shift_k⁻¹`. -/
theorem ladL_translate (k i : ℕ) (w : ℝ) :
    ladL Λ Λs k (i + k, w) = (ladL Λ Λs 0 (i, w)).map (rungShift k) := by
  refine ext_nat_prod fun j A hA => ?_
  rw [Measure.map_apply (measurable_rungShift k) ((measurableSet_singleton j).prod hA)]
  simp only [ladL]
  rw [comp_indKernel_apply _ _ _ ((measurableSet_singleton j).prod hA),
    comp_indKernel_apply _ _ _ ((measurable_rungShift k) ((measurableSet_singleton j).prod hA))]
  by_cases hjk : k < j
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + k := ⟨j - k, by omega⟩
    have h1 : ({j' + k} ×ˢ A) ∩ aboveRung k = {j' + k} ×ˢ A := by
      ext p; simp only [mem_inter_iff, mem_prod, mem_singleton_iff, aboveRung, mem_ofPred_eq]
      constructor
      · exact fun h => h.1
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, by omega⟩
    have h2 : rungShift k ⁻¹' ({j' + k} ×ˢ A) ∩ aboveRung 0 = {j'} ×ˢ A := by
      ext p; simp only [mem_inter_iff, mem_preimage, rungShift, mem_prod, mem_singleton_iff,
        aboveRung, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, by omega⟩
    rw [h1, h2, ladder_translate_iter Λ Λs (by omega) k w hA]
  · have h1 : ({j} ×ˢ A) ∩ aboveRung k = ∅ := by
      ext p; simp only [mem_inter_iff, mem_prod, mem_singleton_iff, aboveRung, mem_ofPred_eq,
        mem_empty_iff_false, iff_false]
      omega
    have h2 : rungShift k ⁻¹' ({j} ×ˢ A) ∩ aboveRung 0 = ∅ := by
      ext p; simp only [mem_inter_iff, mem_preimage, rungShift, mem_prod, mem_singleton_iff,
        aboveRung, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      omega
    rw [h1, h2, measure_empty, measure_empty]

/-- (10.44): `L_kᵐ(i + k, w) = Qᵐ(i, w) ∘ shift_k⁻¹` for every `m`. -/
theorem ladL_pow_translate (k : ℕ) (m : ℕ) (i : ℕ) (w : ℝ) :
    (ladL Λ Λs k ^ m) (i + k, w) = ((ladL Λ Λs 0 ^ m) (i, w)).map (rungShift k) := by
  induction m generalizing i w with
  | zero =>
    rw [pow_zero_apply, pow_zero_apply, Measure.map_dirac' (measurable_rungShift k)]
    rfl
  | succ m ih =>
    ext S hS
    rw [Measure.map_apply (measurable_rungShift k) hS, pow_succ_apply _ m _ hS,
      pow_succ_apply _ m _ ((measurable_rungShift k) hS), ladL_translate,
      lintegral_map (Kernel.measurable_coe _ hS) (measurable_rungShift k)]
    refine lintegral_congr fun z => ?_
    obtain ⟨i', w'⟩ := z
    change (ladL Λ Λs k ^ m) (i' + k, w') S = _
    rw [ih, Measure.map_apply (measurable_rungShift k) hS]

/-- From below rung `k`, the chain killed outside `(k, ∞)` dies at once:
`L_k(z, ·) = 0` for `z₁ < k`. -/
theorem ladL_apply_of_lt {k : ℕ} {z : ℕ × ℝ} (hz : z.1 < k) : ladL Λ Λs k z = 0 := by
  ext S hS
  rw [ladL, comp_indKernel_apply _ _ _ hS, Measure.coe_zero, Pi.zero_apply]
  refine measure_mono_null (fun p hp => ?_)
    (ladder_apply_aboveRung_succ Λ Λs z.1 z.2)
  simp only [aboveRung, mem_inter_iff, mem_ofPred_eq] at hp ⊢
  omega

/-- From below rung `k`, `L_kᵃ⁺¹(z, ·) = 0`. -/
theorem ladL_pow_succ_apply_of_lt {k : ℕ} (a : ℕ) {z : ℕ × ℝ} (hz : z.1 < k) :
    (ladL Λ Λs k ^ (a + 1)) z = 0 := by
  rw [pow_succ]
  change ((ladL Λ Λs k ^ a) ∘ₖ ladL Λ Λs k) z = 0
  rw [Kernel.comp_apply, ladL_apply_of_lt Λ Λs hz, Measure.bind_zero_left]

/-! ### The kernels `S^{(k)}` -/

/-- Equal sets give equal kernels `I_A`. -/
theorem indKernel_congr {A B : Set (ℕ × ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : A = B) : indKernel hA = indKernel hB := by
  subst h; rfl

/-- The taboo kernel of `[0]` is `P (I_{[0]ᶜ} P)ⁿ = P Qⁿ` with `Q = L₀`. -/
theorem tabooKernel_rung_zero (n : ℕ) :
    tabooKernel (ladderChainKernel Λ Λs) (measurableSet_rung 0) n =
      ladderChainKernel Λ Λs ∘ₖ (ladL Λ Λs 0 ^ n) := by
  rw [tabooKernel, ladL, indKernel_congr _ (measurableSet_aboveRung 0) rung_zero_compl]

/-- Off `[0]`, the taboo probabilities are the powers of `Q`:
`_{[0]}Pⁿ⁺¹(x, E) = Qⁿ⁺¹(x, E)` for `E ⊆ (0, ∞) × ℝ`. -/
theorem tabooKernel_eq_ladQ_pow (n : ℕ) (x : ℕ × ℝ) {E : Set (ℕ × ℝ)} (hE : MeasurableSet E)
    (hsub : E ⊆ aboveRung 0) :
    tabooKernel (ladderChainKernel Λ Λs) (measurableSet_rung 0) n x E =
      (ladL Λ Λs 0 ^ (n + 1)) x E := by
  rw [tabooKernel_rung_zero, pow_add_eq _ n 1, pow_one, ladL, Kernel.comp_assoc,
    comp_indKernel_apply _ _ _ hE, inter_eq_left.2 hsub]

/-- The kernel `S^{(k)}(y, A) = U_{[0]}(0, y; k × A)` (10.42). -/
noncomputable def ladderS (k : ℕ) : Kernel ℝ ℝ :=
  (((tabooPotKernel (ladderChainKernel Λ Λs) (measurableSet_rung 0)).comap
    (fun y => ((0 : ℕ), y)) measurable_prodMk_left).restrict (measurableSet_rung k)).map
      Prod.snd

/-- `S^{(k)}(y, ·)` is `U_{[0]}(0, y; ·)` on rung `k`, seen on `ℝ`. -/
theorem ladderS_apply_measure (k : ℕ) (y : ℝ) :
    ladderS Λ Λs k y =
      ((tabooPotKernel (ladderChainKernel Λ Λs) (measurableSet_rung 0) (0, y)).restrict
        (rung k)).map Prod.snd := by
  rw [ladderS, Kernel.map_apply _ measurable_snd, Kernel.restrict_apply, Kernel.comap_apply]

/-- `S^{(k)}(y, A) = U_{[0]}(0, y; k × A)`. -/
theorem ladderS_apply (k : ℕ) (y : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    ladderS Λ Λs k y A =
      tabooPotKernel (ladderChainKernel Λ Λs) (measurableSet_rung 0) (0, y) ({k} ×ˢ A) := by
  rw [ladderS_apply_measure, map_snd_restrict_rung_apply _ k hA]

/-- For `k ≥ 1`: `S^{(k)}(y, A) = Σₙ Qⁿ⁺¹(0, y; k × A)`. -/
theorem ladderS_apply_eq_tsum {k : ℕ} (hk : 1 ≤ k) (y : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    ladderS Λ Λs k y A = ∑' n, (ladL Λ Λs 0 ^ (n + 1)) (0, y) ({k} ×ˢ A) := by
  rw [ladderS_apply _ _ k y hA, tabooPotKernel, Kernel.sum_apply' _ _
    ((measurableSet_singleton k).prod hA)]
  refine tsum_congr fun n => tabooKernel_eq_ladQ_pow _ _ n _
    ((measurableSet_singleton k).prod hA) fun p hp => ?_
  simp only [mem_prod, mem_singleton_iff, aboveRung, mem_ofPred_eq] at hp ⊢
  omega

/-- The kernel `S = S^{(1)}` of (10.40). -/
noncomputable abbrev ladS : Kernel ℝ ℝ := ladderS Λ Λs 1

/-- The restriction of `Qⁿ⁺¹` and of `_{[0]}Pⁿ⁺¹` to rung `k ≥ 1` agree. -/
theorem tabooKernel_restrict_rung {k : ℕ} (hk : 1 ≤ k) (n : ℕ) (x : ℕ × ℝ) :
    (tabooKernel (ladderChainKernel Λ Λs) (measurableSet_rung 0) n x).restrict (rung k) =
      ((ladL Λ Λs 0 ^ (n + 1)) x).restrict (rung k) := by
  ext S hS
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
  exact tabooKernel_eq_ladQ_pow _ _ n x (hS.inter (measurableSet_rung k)) fun p hp => by
    simp only [rung, mem_inter_iff, mem_prod, mem_singleton_iff, aboveRung,
      mem_ofPred_eq] at hp ⊢
    omega

/-- The integrand of the decomposition: `L_kᵃ⁺¹(z, (k + 1) × A)` vanishes below rung `k` and is
`Qᵃ⁺¹(0, w; 1 × A)` at `z = (k, w)`. -/
theorem ladL_pow_apply_rung {k : ℕ} (a : ℕ) {A : Set ℝ} (hA : MeasurableSet A) {z : ℕ × ℝ}
    (hz : z ∈ (aboveRung k)ᶜ) :
    (ladL Λ Λs k ^ (a + 1)) z ({k + 1} ×ˢ A) =
      (rung k).indicator (fun z => (ladL Λ Λs 0 ^ (a + 1)) (0, z.2) ({1} ×ˢ A)) z := by
  simp only [aboveRung, mem_compl_iff, mem_ofPred_eq, not_lt] at hz
  by_cases hzk : z.1 = k
  · obtain ⟨i, w⟩ := z
    simp only at hzk
    subst hzk
    rw [indicator_of_mem (show (i, w) ∈ rung i by simp [rung])]
    have := ladL_pow_translate Λ Λs i (a + 1) 0 w
    rw [zero_add] at this
    rw [this, Measure.map_apply (measurable_rungShift i) ((measurableSet_singleton _).prod hA)]
    congr 1
    ext p
    simp only [mem_preimage, rungShift, mem_prod, mem_singleton_iff]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
  · rw [ladL_pow_succ_apply_of_lt Λ Λs a (by omega), indicator_of_notMem
      (show z ∉ rung k by simp [rung, hzk])]
    rfl

/-- One term of the decomposition: for `k ≥ 1`,
`Qⁿ⁺¹(0, y; (k + 1) × A) = Σ_{j ≤ n} ∫_{rung k} Qʲ(0, y; dz) Q^{n+1−j}(0, z₂; 1 × A)`. -/
theorem ladQ_pow_succ_decomp {k : ℕ} (hk : 1 ≤ k) (n : ℕ) (y : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    (ladL Λ Λs 0 ^ (n + 1)) (0, y) ({k + 1} ×ˢ A) =
      ∑ j ∈ Finset.range (n + 1), ∫⁻ z in rung k,
        (ladL Λ Λs 0 ^ (n + 1 - j)) (0, z.2) ({1} ×ˢ A) ∂(ladL Λ Λs 0 ^ j) (0, y) := by
  have hE : MeasurableSet ({k + 1} ×ˢ A) := (measurableSet_singleton _).prod hA
  have hED : {k + 1} ×ˢ A ⊆ aboveRung k := fun p hp => by
    simp only [mem_prod, mem_singleton_iff] at hp
    simp only [aboveRung, mem_ofPred_eq]; omega
  have hL : indKernel (measurableSet_aboveRung k) ∘ₖ ladL Λ Λs 0 = ladL Λ Λs k :=
    indKernel_comp_indKernel_comp _ _ _ fun p hp => by
      simp only [aboveRung, mem_ofPred_eq] at hp ⊢; omega
  have hdec := restrict_pow_comp_decomp (ladL Λ Λs 0) (measurableSet_aboveRung k)
    (Measure.dirac ((0 : ℕ), y)) (n + 1)
  rw [hL, dirac_kernel] at hdec
  have hρ : (Measure.dirac ((0 : ℕ), y)).restrict (aboveRung k) = 0 := by
    ext S hS
    rw [Measure.restrict_apply hS, Measure.dirac_apply' _ (hS.inter (measurableSet_aboveRung k))]
    simp only [Measure.coe_zero, Pi.zero_apply]
    exact indicator_of_notMem (fun h => by
      simp only [mem_inter_iff, aboveRung, mem_ofPred_eq] at h; omega) _
  rw [hρ, Measure.bind_zero_left, zero_add] at hdec
  have h1 := congrArg (fun m : Measure (ℕ × ℝ) => m ({k + 1} ×ˢ A)) hdec
  rw [Measure.restrict_apply hE, inter_eq_left.2 hED, Measure.finsetSum_apply] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rw [measure_kernel_apply _ _ hE, dirac_kernel]
  obtain ⟨a, ha⟩ : ∃ a, n + 1 - j = a + 1 := ⟨n - j, by omega⟩
  rw [ha, setLIntegral_congr_fun (measurableSet_aboveRung k).compl fun z hz =>
    ladL_pow_apply_rung Λ Λs a hA hz, lintegral_indicator (measurableSet_rung k),
    Measure.restrict_restrict (measurableSet_rung k), inter_eq_left.2 fun p hp => by
      simp only [rung, mem_prod, mem_singleton_iff] at hp
      simp only [mem_compl_iff, aboveRung, mem_ofPred_eq, not_lt]; omega]

/-- **(10.45), (10.39)**: for `k ≥ 1`, `S^{(k+1)} = S^{(k)} S` (first `S^{(k)}`, then `S`). -/
theorem ladderS_succ {k : ℕ} (hk : 1 ≤ k) :
    ladderS Λ Λs (k + 1) = ladS Λ Λs ∘ₖ ladderS Λ Λs k := by
  ext y A hA
  have hg : ∀ a, Measurable fun z : ℕ × ℝ => (ladL Λ Λs 0 ^ a) (0, z.2) ({1} ×ˢ A) := fun a =>
    (Kernel.measurable_coe _ ((measurableSet_singleton 1).prod hA)).comp
      (measurable_prodMk_left.comp measurable_snd)
  rw [ladderS_apply_eq_tsum _ _ (by omega) y hA]
  simp_rw [ladQ_pow_succ_decomp Λ Λs hk _ y hA]
  -- reindex the double sum
  have e1 : ∑' n, ∑ j ∈ Finset.range (n + 1), ∫⁻ z in rung k,
      (ladL Λ Λs 0 ^ (n + 1 - j)) (0, z.2) ({1} ×ˢ A) ∂(ladL Λ Λs 0 ^ j) (0, y) =
      ∑' N, ∑ j ∈ Finset.range N, ∫⁻ z in rung k,
        (ladL Λ Λs 0 ^ (N - j)) (0, z.2) ({1} ×ˢ A) ∂(ladL Λ Λs 0 ^ j) (0, y) := by
    rw [tsum_eq_zero_add' ENNReal.summable (f := fun N => ∑ j ∈ Finset.range N, _)]
    simp
  rw [e1, tsum_sum_range_lt (fun j N => ∫⁻ z in rung k,
    (ladL Λ Λs 0 ^ (N - j)) (0, z.2) ({1} ×ˢ A) ∂(ladL Λ Λs 0 ^ j) (0, y))]
  simp only [show ∀ m j : ℕ, m + (j + 1) - j = m + 1 from fun m j => by omega]
  simp_rw [← lintegral_tsum fun m => (hg (m + 1)).aemeasurable]
  -- the inner sum is `S(z₂, A)`
  have hS : ∀ z : ℕ × ℝ, ∑' m, (ladL Λ Λs 0 ^ (m + 1)) (0, z.2) ({1} ×ˢ A) =
      ladS Λ Λs z.2 A := fun z => (ladderS_apply_eq_tsum _ _ le_rfl z.2 hA).symm
  simp_rw [hS]
  -- drop `j = 0` and recognise `U_{[0]}` on rung `k`
  rw [tsum_eq_zero_add' ENNReal.summable]
  have h0 : ∫⁻ z in rung k, ladS Λ Λs z.2 A ∂(ladL Λ Λs 0 ^ 0) (0, y) = 0 := by
    rw [pow_zero_apply, Measure.restrict_eq_zero.2, lintegral_zero_measure]
    rw [Measure.dirac_apply' _ (measurableSet_rung k)]
    exact indicator_of_notMem (by simp [rung, show (0 : ℕ) ≠ k by omega]) _
  rw [h0, zero_add, Kernel.comp_apply' _ _ _ hA, ladderS_apply_measure,
    lintegral_map ((Kernel.measurable_coe _ hA)) measurable_snd, tabooPotKernel,
    Kernel.sum_apply, Measure.restrict_sum _ (measurableSet_rung k), lintegral_sum_measure]
  refine tsum_congr fun j => ?_
  rw [tabooKernel_restrict_rung Λ Λs hk j]

/-- (10.39): `S^{(k)} = Sᵏ` for `k ≥ 1`. -/
theorem ladderS_eq_pow {k : ℕ} (hk : 1 ≤ k) : ladderS Λ Λs k = ladS Λ Λs ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rw [pow_one]
    · rw [ladderS_succ Λ Λs h, ih h, pow_succ']
      rfl

/-! ### The operator equation (10.40) -/

/-- `Q(z, 1 × B) = Λ_{z₁}(z₂, B)`: from rung `i` the chain reaches rung `1` through `Λᵢ`. -/
theorem ladQ_apply_rung_one (z : ℕ × ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    ladL Λ Λs 0 z ({1} ×ˢ B) = Λ z.1 z.2 B := by
  obtain ⟨i, w⟩ := z
  rw [ladL, comp_indKernel_apply _ _ _ ((measurableSet_singleton 1).prod hB),
    inter_eq_left.2 fun p hp => by
      simp only [mem_prod, mem_singleton_iff] at hp
      simp only [aboveRung, mem_ofPred_eq]; omega,
    eq_3_40_mid Λ Λs le_rfl (by omega) w hB]
  simp

/-- `Qⁿ⁺¹` puts no mass on `[0]`. -/
theorem ladQ_pow_succ_restrict_rung_zero (n : ℕ) (x : ℕ × ℝ) :
    ((ladL Λ Λs 0 ^ (n + 1)) x).restrict (rung 0) = 0 := by
  rw [Measure.restrict_eq_zero, pow_add_eq _ n 1, pow_one,
    Kernel.comp_apply' _ _ _ (measurableSet_rung 0)]
  have h0 : ∀ z, ladL Λ Λs 0 z (rung 0) = 0 := fun z => by
    rw [ladL, comp_indKernel_apply _ _ _ (measurableSet_rung 0)]
    convert measure_empty (μ := ladderChainKernel Λ Λs z)
    ext p; simp [rung, aboveRung]
  simp [h0]

/-- The finite partial sums `S_N^{(k)}(y, ·) = Σ_{n < N} Qⁿ⁺¹(0, y; k × ·)` of (10.47). -/
noncomputable def ladSN (N k : ℕ) (y : ℝ) : Measure ℝ :=
  ∑ n ∈ Finset.range N, (((ladL Λ Λs 0 ^ (n + 1)) (0, y)).restrict (rung k)).map Prod.snd

/-- `S_N^{(k)}(y, A) = Σ_{n < N} Qⁿ⁺¹(0, y; k × A)`. -/
theorem ladSN_apply (N k : ℕ) (y : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    ladSN Λ Λs N k y A = ∑ n ∈ Finset.range N, (ladL Λ Λs 0 ^ (n + 1)) (0, y) ({k} ×ˢ A) := by
  rw [ladSN, Measure.finsetSum_apply]
  exact Finset.sum_congr rfl fun n _ => map_snd_restrict_rung_apply _ k hA

/-- The partial sums increase to `S^{(k)}` (`k ≥ 1`). -/
theorem ladderS_apply_eq_iSup {k : ℕ} (hk : 1 ≤ k) (y : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    ladderS Λ Λs k y A = ⨆ N, ladSN Λ Λs N k y A := by
  rw [ladderS_apply_eq_tsum _ _ hk y hA, ENNReal.tsum_eq_iSup_nat]
  simp_rw [ladSN_apply _ _ _ k y hA]

/-- (10.46), integrated: `Qⁿ⁺²(0, y; 1 × B) = Σ_{k ≥ 1} ∫ Qⁿ⁺¹(0, y; k × dw) Λₖ(w, B)`. -/
theorem ladQ_pow_succ_succ_rung_one (n : ℕ) (y : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    (ladL Λ Λs 0 ^ (n + 1 + 1)) (0, y) ({1} ×ˢ B) =
      ∑' k, ∫⁻ w, Λ (k + 1) w B ∂(((ladL Λ Λs 0 ^ (n + 1)) (0, y)).restrict
        (rung (k + 1))).map Prod.snd := by
  have hF : Measurable fun z : ℕ × ℝ => Λ z.1 z.2 B :=
    measurable_from_prod_countable_right (f := fun z : ℕ × ℝ => Λ z.1 z.2 B)
      fun i => Kernel.measurable_coe (Λ i) hB
  rw [pow_succ_apply' _ _ _ ((measurableSet_singleton 1).prod hB)]
  simp_rw [ladQ_apply_rung_one Λ Λs _ hB]
  rw [lintegral_nat_prod _ hF, tsum_eq_zero_add' ENNReal.summable,
    ladQ_pow_succ_restrict_rung_zero, Measure.map_zero, lintegral_zero_measure, zero_add]

/-- (10.40), (10.46): `S = Σₖ Sᵏ Λₖ`, i.e. `S(y, B) = Σₖ ∫ Sᵏ(y, dz) Λₖ(z, B)`. -/
theorem ladS_eq : ladS Λ Λs = Kernel.sum fun k => Λ k ∘ₖ (ladS Λ Λs ^ k) := by
  ext y B hB
  rw [Kernel.sum_apply' _ _ hB, tsum_eq_zero_add' ENNReal.summable, pow_zero]
  change _ = (Λ 0 ∘ₖ Kernel.id) y B + _
  rw [Kernel.comp_id, ladderS_apply_eq_tsum _ _ le_rfl y hB, tsum_eq_zero_add' ENNReal.summable,
    zero_add, pow_one, ladQ_apply_rung_one Λ Λs _ hB]
  congr 1
  simp_rw [ladQ_pow_succ_succ_rung_one Λ Λs _ y hB]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  rw [← ladderS_eq_pow Λ Λs (by omega), Kernel.comp_apply' _ _ _ hB, ladderS_apply_measure,
    tabooPotKernel, Kernel.sum_apply, Measure.restrict_sum _ (measurableSet_rung _)]
  rw [Measure.map_sum measurable_snd.aemeasurable, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [tabooKernel_restrict_rung Λ Λs (by omega) n]

/-! ### Minimality (10.47)–(10.51) -/

/-- (10.49): `S_{N+1}(y, B) = Λ₀(y, B) + Σ_{k ≥ 1} ∫ S_N^{(k)}(y, dw) Λₖ(w, B)`. -/
theorem ladSN_succ_one (N : ℕ) (y : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    ladSN Λ Λs (N + 1) 1 y B =
      Λ 0 y B + ∑' k, ∫⁻ w, Λ (k + 1) w B ∂ladSN Λ Λs N (k + 1) y := by
  rw [ladSN_apply _ _ _ 1 y hB, Finset.sum_range_succ', zero_add, pow_one,
    ladQ_apply_rung_one Λ Λs _ hB, add_comm]
  congr 1
  simp_rw [ladQ_pow_succ_succ_rung_one Λ Λs _ y hB]
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine tsum_congr fun k => ?_
  rw [ladSN, lintegral_finsetSum_measure]

/-- The finite version of the reindexing:
`Σ_{n < N} Σ_{j < n} f(j, n) ≤ Σ_{j < N} Σ_{m < N} f(j, m + j + 1)`. -/
theorem sum_sum_range_lt_le_finite (f : ℕ → ℕ → ℝ≥0∞) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range n, f j n ≤
      ∑ j ∈ Finset.range N, ∑ m ∈ Finset.range N, f j (m + (j + 1)) := by
  have h1 : ∀ n ∈ Finset.range N, ∑ j ∈ Finset.range n, f j n =
      ∑ j ∈ Finset.range N, (Iio n).indicator (fun j => f j n) j := fun n hn => by
    simp only [Finset.mem_range] at hn
    rw [← Finset.sum_subset (Finset.range_subset_range.2 hn.le) (fun i _ hi =>
      indicator_of_notMem (show i ∉ Iio n from fun h => hi (Finset.mem_range.2 h)) _)]
    exact Finset.sum_congr rfl fun i hi =>
      (indicator_of_mem (show i ∈ Iio n from Finset.mem_range.1 hi) (fun i => f i n)).symm
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  calc ∑ n ∈ Finset.range N, (Iio n).indicator (fun j => f j n) j
      ≤ ∑ n ∈ Finset.range (j + 1 + N), (Iio n).indicator (fun j => f j n) j :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
    _ = ∑ n ∈ Finset.range (j + 1), (Iio n).indicator (fun j => f j n) j +
        ∑ m ∈ Finset.range N, (Iio (j + 1 + m)).indicator (fun j => f j (j + 1 + m)) j :=
        Finset.sum_range_add _ _ _
    _ = ∑ m ∈ Finset.range N, f j (m + (j + 1)) := by
        rw [Finset.sum_eq_zero (fun n hn => indicator_of_notMem (show j ∉ Iio n by
          simp only [Finset.mem_range] at hn; simp only [mem_Iio]; omega) _), zero_add]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [indicator_of_mem (show j ∈ Iio (j + 1 + m) by simp only [mem_Iio]; omega)]
        congr 1; omega

/-- `w ↦ S_N^{(k)}(w, A)` is measurable. -/
theorem measurable_ladSN (N k : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    Measurable fun w => ladSN Λ Λs N k w A := by
  simp_rw [ladSN_apply _ _ _ k _ hA]
  exact Finset.measurable_sum _ fun n _ =>
    (Kernel.measurable_coe _ ((measurableSet_singleton k).prod hA)).comp measurable_prodMk_left

/-- (10.48): `S_N^{(k+1)}(y, A) ≤ ∫ S_N^{(k)}(y, dw) S_N(w, A)` for `k ≥ 1`. -/
theorem ladSN_succ_le {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (y : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ladSN Λ Λs N (k + 1) y A ≤ ∫⁻ w, ladSN Λ Λs N 1 w A ∂ladSN Λ Λs N k y := by
  have hg : ∀ a, Measurable fun z : ℕ × ℝ => (ladL Λ Λs 0 ^ a) (0, z.2) ({1} ×ˢ A) := fun a =>
    (Kernel.measurable_coe _ ((measurableSet_singleton 1).prod hA)).comp
      (measurable_prodMk_left.comp measurable_snd)
  rw [ladSN_apply _ _ _ _ y hA]
  simp_rw [ladQ_pow_succ_decomp Λ Λs hk _ y hA]
  -- drop `j = 0`
  have h0 : ∀ n, ∫⁻ z in rung k, (ladL Λ Λs 0 ^ (n + 1 - 0)) (0, z.2) ({1} ×ˢ A)
      ∂(ladL Λ Λs 0 ^ 0) (0, y) = 0 := fun n => by
    rw [pow_zero_apply, Measure.restrict_eq_zero.2, lintegral_zero_measure]
    rw [Measure.dirac_apply' _ (measurableSet_rung k)]
    exact indicator_of_notMem (by simp [rung, show (0 : ℕ) ≠ k by omega]) _
  simp_rw [Finset.sum_range_succ' _ _, h0, add_zero]
  simp only [show ∀ n j : ℕ, n + 1 - (j + 1) = n - j from fun n j => by omega]
  refine (sum_sum_range_lt_le_finite (fun j n => ∫⁻ z in rung k, (ladL Λ Λs 0 ^ (n - j))
    (0, z.2) ({1} ×ˢ A) ∂(ladL Λ Λs 0 ^ (j + 1)) (0, y)) N).trans (le_of_eq ?_)
  simp only [show ∀ m j : ℕ, m + (j + 1) - j = m + 1 from fun m j => by omega]
  rw [ladSN, lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← lintegral_finsetSum _ fun m _ => hg (m + 1),
    lintegral_map (measurable_ladSN Λ Λs N 1 hA) measurable_snd]
  refine lintegral_congr fun z => ?_
  rw [ladSN_apply _ _ _ 1 _ hA]

/-- **(10.51), minimality** (MT p. 251): `S` is the minimal solution of the operator equation
(10.40): every kernel `S*` with `S* ≥ Σₖ S*ᵏ Λₖ` satisfies `S ≤ S*`. -/
theorem ladS_minimal (Sstar : Kernel ℝ ℝ)
    (hS : ∀ y B, MeasurableSet B →
      (Kernel.sum fun k => Λ k ∘ₖ (Sstar ^ k)) y B ≤ Sstar y B) :
    ∀ y B, MeasurableSet B → ladS Λ Λs y B ≤ Sstar y B := by
  -- step 1: `S_N ≤ S*` for every `N`
  have hstep : ∀ N, (∀ y B, MeasurableSet B → ladSN Λ Λs N 1 y B ≤ Sstar y B) →
      ∀ k, 1 ≤ k → ∀ y A, MeasurableSet A → ladSN Λ Λs N k y A ≤ (Sstar ^ k) y A := by
    intro N hN k hk
    induction k, hk using Nat.le_induction with
    | base => intro y A hA; rw [pow_one]; exact hN y A hA
    | succ k hk ih =>
      intro y A hA
      have hle : ladSN Λ Λs N k y ≤ (Sstar ^ k) y := Measure.le_intro fun A hA _ => ih y A hA
      calc ladSN Λ Λs N (k + 1) y A ≤ ∫⁻ w, ladSN Λ Λs N 1 w A ∂ladSN Λ Λs N k y :=
            ladSN_succ_le Λ Λs hk N y hA
        _ ≤ ∫⁻ w, Sstar w A ∂(Sstar ^ k) y :=
            lintegral_mono' hle fun w => hN w A hA
        _ = (Sstar ^ (k + 1)) y A := by
            rw [pow_succ']
            exact (Kernel.comp_apply' _ _ _ hA).symm
  have hN : ∀ N y B, MeasurableSet B → ladSN Λ Λs N 1 y B ≤ Sstar y B := by
    intro N
    induction N with
    | zero => intro y B _; simp [ladSN]
    | succ N ih =>
      intro y B hB
      have hk := hstep N ih
      rw [ladSN_succ_one Λ Λs N y hB]
      refine le_trans ?_ (hS y B hB)
      rw [Kernel.sum_apply' _ _ hB]
      conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable, pow_zero]
      change _ ≤ (Λ 0 ∘ₖ Kernel.id) y B + _
      rw [Kernel.comp_id]
      refine add_le_add_right (ENNReal.tsum_le_tsum fun k => ?_) _
      rw [Kernel.comp_apply' _ _ _ hB]
      exact lintegral_mono' (Measure.le_intro fun A hA _ => hk (k + 1) (by omega) y A hA) le_rfl
  intro y B hB
  rw [ladderS_apply_eq_iSup _ _ le_rfl y hB]
  exact iSup_le fun N => hN N y B hB

/-! ### Theorem 10.5.3 -/

/-- For a measure `π`, `∫_{[0]} π(dz) f(z) = ∫ π₀(dy) f(0, y)`, with `π₀ = π` on the bottom rung. -/
theorem setLIntegral_rung_zero (π : Measure (ℕ × ℝ)) {f : ℕ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in rung 0, f z ∂π = ∫⁻ y, f (0, y) ∂(π.restrict (rung 0)).map Prod.snd := by
  have hg : Measurable fun w : ℝ => f (0, w) := hf.comp measurable_prodMk_left
  rw [lintegral_map hg measurable_snd]
  refine setLIntegral_congr_fun (measurableSet_rung 0) fun p hp => ?_
  have : p = (0, p.2) := Prod.ext hp.1 rfl
  rw [← this]

/-- **Theorem 10.5.3** (MT p. 249), (10.38): for a recurrent ladder chain with `ψ([0]) > 0` and
an invariant measure `π` with `π([0]) < ∞`, `π(k × A) = ∫ π₀(dy) Sᵏ(y, A)`, where `π₀` is `π` on
the bottom rung and `S` is the minimal solution (`ladS_minimal`) of (10.40) (`ladS_eq`). -/
theorem theorem_10_5_3 [IsMarkovKernel (ladderChainKernel Λ Λs)] {ψ : Measure (ℕ × ℝ)}
    (hrec : IsRecurrentChain (ladderChainKernel Λ Λs) ψ) {π : Measure (ℕ × ℝ)}
    (hπ : IsInvariantMeasure (ladderChainKernel Λ Λs) π) (hψ0 : 0 < ψ (rung 0))
    (hπ0 : π (rung 0) ≠ ∞) (k : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    π ({k} ×ˢ A) = ∫⁻ y, (ladS Λ Λs ^ k) y A ∂(π.restrict (rung 0)).map Prod.snd := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero]
    change _ = ∫⁻ y, Kernel.id y A ∂_
    simp_rw [Kernel.id_apply, Measure.dirac_apply' _ hA]
    rw [lintegral_indicator_one hA, map_snd_restrict_rung_apply _ 0 hA]
  · rw [← ladderS_eq_pow Λ Λs hk]
    simp_rw [ladderS_apply Λ Λs k _ hA]
    have hmin := theorem_10_4_9 hrec hπ (measurableSet_rung 0) hψ0 hπ0
    have hE : MeasurableSet ({k} ×ˢ A) := (measurableSet_singleton k).prod hA
    conv_lhs => rw [← hmin]
    rw [minimalMeasure_apply _ _ _ hE, setLIntegral_rung_zero π (Kernel.measurable_coe _ hE)]

/-! ### Ladder chains whose bottom rung is entered with a fixed law -/

/-- If every entrance to `[0]` has the law `H` (`P(z, 0 × A) = P(z, [0]) H(A)`), then
`U_{[0]}(z, 0 × A) = L(z, [0]) H(A)`. -/
theorem tabooPotKernel_rung_zero_of_entrance [IsMarkovKernel (ladderChainKernel Λ Λs)]
    (H : Measure ℝ)
    (hH : ∀ z A, MeasurableSet A →
      ladderChainKernel Λ Λs z ({0} ×ˢ A) = ladderChainKernel Λ Λs z (rung 0) * H A)
    (z : ℕ × ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    tabooPotKernel (ladderChainKernel Λ Λs) (measurableSet_rung 0) z ({0} ×ˢ A) =
      hitProb (ladderChainKernel Λ Λs) (rung 0) z * H A := by
  have hE : MeasurableSet ({0} ×ˢ A : Set (ℕ × ℝ)) := (measurableSet_singleton 0).prod hA
  rw [← tabooPotKernel_self _ (measurableSet_rung 0), tabooPotKernel, Kernel.sum_apply' _ _ hE,
    Kernel.sum_apply' _ _ (measurableSet_rung 0), ← ENNReal.tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [tabooKernel, Kernel.comp_apply' _ _ _ hE, Kernel.comp_apply' _ _ _ (measurableSet_rung 0),
    ← lintegral_mul_const _ (Kernel.measurable_coe _ (measurableSet_rung 0))]
  exact lintegral_congr fun z' => hH z' A hA

end MeynTweedie.Positivity


