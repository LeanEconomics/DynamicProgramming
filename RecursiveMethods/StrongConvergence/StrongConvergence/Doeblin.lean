/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.TransitionFunctions

/-!
# Doeblin's condition and Condition M

SLP §11.4, pp. 344–349. `P` is a transition function, a Markov kernel `κ`, with `n`-step
transitions `Pⁿ = kpow κ n`.

* `DoeblinFor κ φ N ε` (**Condition D**, p. 345): `φ` is a finite measure, and `φ(A) ≤ ε` implies
  `Pᴺ(s, A) ≤ 1 − ε` for all `s`. `doeblinFor_mono` shows it persists for `N′ ≥ N` (the book's
  "Why?").
* `ConditionMFor κ N ε` (**Condition M**, p. 348): for each `A`, either `Pᴺ(s, A) ≥ ε` for all
  `s`, or `Pᴺ(s, Aᶜ) ≥ ε` for all `s`.
* **Exercise 11.4** (`ex_11_4a`–`ex_11_4j`): sufficient conditions for Condition D, and three
  kernels violating it.
* **Exercise 11.5** (`ex_11_5a`, `ex_11_5b`, `ex_11_5c`): Condition M holds in Exercise 11.4c and
  11.4e, and implies Condition D. The identity on two points satisfies D but not M.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- **Condition D** (Doeblin, p. 345) for `(φ, N, ε)`. -/
def DoeblinFor (κ : Kernel S S) (φ : Measure S) (N : ℕ) (ε : ℝ) : Prop :=
  IsFiniteMeasure φ ∧ 1 ≤ N ∧ 0 < ε ∧
    ∀ A, MeasurableSet A → φ.real A ≤ ε → ∀ s, (kpow κ N s).real A ≤ 1 - ε

/-- `P` satisfies **Condition D** for some `(φ, N, ε)`. -/
def ConditionD (κ : Kernel S S) : Prop := ∃ φ N ε, DoeblinFor κ φ N ε

/-- **Condition M** (p. 348) for `(N, ε)`. -/
def ConditionMFor (κ : Kernel S S) (N : ℕ) (ε : ℝ) : Prop :=
  1 ≤ N ∧ 0 < ε ∧ ∀ A, MeasurableSet A →
    (∀ s, ε ≤ (kpow κ N s).real A) ∨ ∀ s, ε ≤ (kpow κ N s).real Aᶜ

/-- `P` satisfies **Condition M** for some `(N, ε)`. -/
def ConditionM (κ : Kernel S S) : Prop := ∃ N ε, ConditionMFor κ N ε

variable {κ : Kernel S S} [IsMarkovKernel κ]

omit [IsMarkovKernel κ] in
/-- Chapman–Kolmogorov: `Pⁿ⁺ᵐ(s, A) = ∫ Pᵐ(s′, A) Pⁿ(s, ds′)`. -/
theorem kpow_add_apply (n m : ℕ) (s : S) {A : Set S} (hA : MeasurableSet A) :
    kpow κ (n + m) s A = ∫⁻ s', kpow κ m s' A ∂kpow κ n s := by
  rw [kpow_add, Kernel.comp_apply' _ _ _ hA]

theorem isMarkov_kpow (n : ℕ) : IsMarkovKernel (kpow κ n) := ex_8_4a κ n

/-- An average of numbers at most `c ≤ 1` is at most `c`. -/
theorem kpow_real_le_of_forall {n m : ℕ} {A : Set S} (hA : MeasurableSet A) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ s', (kpow κ m s').real A ≤ c) (s : S) : (kpow κ (n + m) s).real A ≤ c := by
  have := isMarkov_kpow (κ := κ) n
  have := isMarkov_kpow (κ := κ) m
  have hle : kpow κ (n + m) s A ≤ ENNReal.ofReal c := by
    rw [kpow_add_apply n m s hA]
    calc ∫⁻ s', kpow κ m s' A ∂kpow κ n s ≤ ∫⁻ _, ENNReal.ofReal c ∂kpow κ n s :=
          lintegral_mono fun s' => by
            rw [← ENNReal.ofReal_toReal (measure_ne_top _ A)]
            exact ENNReal.ofReal_le_ofReal (h s')
      _ = ENNReal.ofReal c := by simp
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hc hle

/-- Condition D for `(φ, N, ε)` holds for `(φ, N′, ε)`, `N′ ≥ N` (p. 345, "Why?"). -/
theorem doeblinFor_mono [Nonempty S] {φ : Measure S} {N N' : ℕ} {ε : ℝ}
    (h : DoeblinFor κ φ N ε) (hNN' : N ≤ N') : DoeblinFor κ φ N' ε := by
  obtain ⟨hφ, hN, hε, hD⟩ := h
  have hε1 : ε ≤ 1 := by
    obtain ⟨s⟩ := ‹Nonempty S›
    have := hD ∅ MeasurableSet.empty (by simp [hε.le]) s
    simp at this; linarith
  refine ⟨hφ, hN.trans hNN', hε, fun A hA hφA s => ?_⟩
  have := kpow_real_le_of_forall (n := N' - N) (m := N) hA (by linarith)
    (fun s' => hD A hA hφA s') s
  rwa [Nat.sub_add_cancel hNN'] at this

theorem real_le_one_sub_of_compl {μ : Measure S} [IsProbabilityMeasure μ] {A : Set S}
    (hA : MeasurableSet A) {c : ℝ} (h : c ≤ μ.real Aᶜ) : μ.real A ≤ 1 - c := by
  have := probReal_compl_eq_one_sub (μ := μ) hA
  linarith

/-- A finite measure gives mass at most `ε` to some point of any injective sequence. -/
theorem exists_small_atom [MeasurableSingletonClass S] (φ : Measure S) [IsFiniteMeasure φ]
    {x : ℕ → S} (hx : Function.Injective x) {ε : ℝ} (hε : 0 < ε) :
    ∃ k, φ.real {x k} ≤ ε := by
  by_contra hc
  push Not at hc
  obtain ⟨K, hK⟩ := exists_nat_gt (φ.real univ / ε)
  have hsum : φ.real (⋃ k ∈ Finset.range K, {x k}) = ∑ k ∈ Finset.range K, φ.real {x k} :=
    measureReal_biUnion_finset (fun i _ j _ hij => Set.disjoint_singleton.2 (hx.ne hij))
      (fun k _ => measurableSet_singleton _) (fun k _ => measure_ne_top _ _)
  have hlt : (K : ℝ) * ε < ∑ k ∈ Finset.range K, φ.real {x k} := by
    rcases Nat.eq_zero_or_pos K with rfl | hK0
    · rw [Nat.cast_zero] at hK
      exact absurd hK (not_lt.2 (div_nonneg measureReal_nonneg hε.le))
    · calc (K : ℝ) * ε = ∑ _k ∈ Finset.range K, ε := by simp
        _ < _ := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by omega))
          fun k _ => hc k
  have hle := measureReal_mono (μ := φ) (subset_univ (⋃ k ∈ Finset.range K, {x k}))
  rw [div_lt_iff₀ hε] at hK
  linarith

omit [IsMarkovKernel κ] in
/-- **Exercise 11.4a.** On a finite set with all subsets measurable, every `P` satisfies
Condition D (with `φ` the counting measure). -/
theorem ex_11_4a [Finite S] [MeasurableSingletonClass S] : ConditionD κ := by
  have : IsFiniteMeasure (Measure.count : Measure S) := ⟨by
    rw [Measure.count_apply_finite _ Set.finite_univ]; exact ENNReal.natCast_lt_top _⟩
  refine ⟨Measure.count, 1, 1 / 2, this, le_rfl, by norm_num, fun A hA hφA s => ?_⟩
  have hA0 : A = ∅ := by
    by_contra hne
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hne
    have h1 : (1 : ℝ) ≤ (Measure.count : Measure S).real A := by
      have := measureReal_mono (μ := (Measure.count : Measure S)) (Set.singleton_subset_iff.2 ha)
      rw [measureReal_def, Measure.count_singleton] at this
      simpa using this
    linarith
  subst hA0
  simp only [measureReal_empty]
  norm_num

/-- **Exercise 11.4b.** On `ℕ`, if the tails `Σ_{j ≥ J} pᵢⱼ` tend to zero uniformly in `i`,
Condition D holds (with `φ` the counting measure on `{0, …, J − 1}`). -/
theorem ex_11_4b {κ : Kernel ℕ ℕ} [IsMarkovKernel κ]
    (htail : ∀ δ > 0, ∃ J, ∀ i, (κ i).real (Ici J) ≤ δ) : ConditionD κ := by
  obtain ⟨J, hJ⟩ := htail (1 / 2) (by norm_num)
  set φ : Measure ℕ := Measure.count.restrict (Iio J)
  have hφ : IsFiniteMeasure φ := ⟨by
    rw [Measure.restrict_apply_univ, Measure.count_apply_finite _ (Set.finite_Iio J)]
    exact ENNReal.natCast_lt_top _⟩
  refine ⟨φ, 1, 1 / 2, hφ, le_rfl, by norm_num, fun A hA hφA i => ?_⟩
  have hsub : A ⊆ Ici J := by
    intro a ha
    by_contra hlt
    have hmem : a ∈ A ∩ Iio J := ⟨ha, Set.mem_Iio.2 (not_le.1 fun h => hlt h)⟩
    have h1 : (1 : ℝ≥0∞) ≤ φ A := by
      rw [Measure.restrict_apply hA, ← Measure.count_singleton a]
      exact measure_mono (Set.singleton_subset_iff.2 hmem)
    have h1 : (1 : ℝ) ≤ φ.real A :=
      ENNReal.toReal_one ▸ ENNReal.toReal_mono (measure_ne_top φ A) h1
    linarith
  rw [kpow_one]
  calc (κ i).real A ≤ (κ i).real (Ici J) := measureReal_mono hsub
    _ ≤ 1 / 2 := hJ i
    _ = 1 - 1 / 2 := by norm_num

/-- **Exercise 11.4c.** If `Pᴺ(s, {s₀}) > ε` for all `s`, Condition D holds (with `φ = δ_{s₀}`). -/
theorem ex_11_4c [MeasurableSingletonClass S] {s₀ : S} {N : ℕ} {ε : ℝ} (hN : 1 ≤ N)
    (hε : 0 < ε) (h : ∀ s, ε < (kpow κ N s).real {s₀}) : ConditionD κ := by
  have := isMarkov_kpow (κ := κ) N
  refine ⟨Measure.dirac s₀, N, min ε (1 / 2), inferInstance, hN, lt_min hε (by norm_num),
    fun A hA hφA s => ?_⟩
  have hs₀ : s₀ ∉ A := fun hmem => by
    rw [measureReal_def, Measure.dirac_apply_of_mem hmem, ENNReal.toReal_one] at hφA
    have := min_le_right ε (1 / 2 : ℝ)
    linarith
  refine real_le_one_sub_of_compl hA ?_
  calc min ε (1 / 2) ≤ ε := min_le_left _ _
    _ ≤ (kpow κ N s).real {s₀} := (h s).le
    _ ≤ (kpow κ N s).real Aᶜ := measureReal_mono (Set.singleton_subset_iff.2 hs₀)

/-- **Exercise 11.4d.** If `Pᴺ(s, A) ≤ φ(A)` for a finite measure `φ`, Condition D holds. -/
theorem ex_11_4d {φ : Measure S} [IsFiniteMeasure φ] {N : ℕ} (hN : 1 ≤ N)
    (h : ∀ s A, MeasurableSet A → kpow κ N s A ≤ φ A) : ConditionD κ := by
  have := isMarkov_kpow (κ := κ) N
  refine ⟨φ, N, 1 / 2, inferInstance, hN, by norm_num, fun A hA hφA s => ?_⟩
  have : (kpow κ N s).real A ≤ φ.real A :=
    ENNReal.toReal_mono (measure_ne_top φ A) (h s A hA)
  linarith

omit [IsMarkovKernel κ] in
/-- The lower bound `P(s, A) ≥ δ μ(A)` from a density bounded below by `δ`. -/
theorem density_lower {μ : Measure S} {p : S → S → ℝ} {δ : ℝ} (hp : ∀ s x, δ ≤ p s x)
    (hκ : ∀ s A, MeasurableSet A → κ s A = ∫⁻ x in A, ENNReal.ofReal (p s x) ∂μ) (s : S)
    {A : Set S} (hA : MeasurableSet A) : ENNReal.ofReal δ * μ A ≤ κ s A := by
  rw [hκ s A hA, ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp s x)

/-- **Exercise 11.4e.** If `P(s, A) = ∫_A p(s, s′) μ(ds′)` for a finite measure `μ` and a density
bounded below by `δ > 0`, Condition D holds. -/
theorem ex_11_4e {μ : Measure S} [IsFiniteMeasure μ] {p : S → S → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ s x, δ ≤ p s x)
    (hκ : ∀ s A, MeasurableSet A → κ s A = ∫⁻ x in A, ENNReal.ofReal (p s x) ∂μ) :
    ConditionD κ := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · exact ⟨μ, 1, 1 / 2, inferInstance, le_rfl, by norm_num, fun A _ _ s => isEmptyElim s⟩
  set m := μ.real univ
  have hm : 0 < m := by
    refine lt_of_le_of_ne measureReal_nonneg fun h0 => ?_
    have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.1
      ((ENNReal.toReal_eq_zero_iff _).1 h0.symm |>.resolve_right (measure_ne_top μ univ))
    have := hκ s₀ univ MeasurableSet.univ
    rw [measure_univ, hμ0, Measure.restrict_zero, lintegral_zero_measure] at this
    exact one_ne_zero this
  set ε := δ * m / (1 + δ)
  have hε : 0 < ε := by positivity
  refine ⟨μ, 1, ε, inferInstance, le_rfl, hε, fun A hA hμA s => ?_⟩
  rw [kpow_one]
  refine real_le_one_sub_of_compl hA ?_
  have hlow := density_lower hp hκ s hA.compl
  have hreal : δ * μ.real Aᶜ ≤ (κ s).real Aᶜ := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) hlow
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le] at this
  have hcompl : μ.real Aᶜ = m - μ.real A := measureReal_compl hA
  have hεeq : δ * (m - ε) = ε := by simp only [ε]; field_simp; ring
  calc ε = δ * (m - ε) := hεeq.symm
    _ ≤ δ * μ.real Aᶜ := mul_le_mul_of_nonneg_left (by linarith) hδ.le
    _ ≤ (κ s).real Aᶜ := hreal

/-- **Exercise 11.4f.** If `P(s, A) = ∫_A p(s, s′) μ(ds′)` with `p ≤ K`, Condition D holds (by
Exercise 11.4d with `φ = Kμ`). -/
theorem ex_11_4f {μ : Measure S} [IsFiniteMeasure μ] {p : S → S → ℝ} {K : ℝ}
    (hp : ∀ s x, p s x ≤ K)
    (hκ : ∀ s A, MeasurableSet A → κ s A = ∫⁻ x in A, ENNReal.ofReal (p s x) ∂μ) :
    ConditionD κ := by
  refine ex_11_4d (φ := K.toNNReal • μ) le_rfl fun s A hA => ?_
  rw [kpow_one, hκ s A hA, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp s x)

omit [IsMarkovKernel κ] in
/-- For the mixture `P = αP₁ + (1 − α)P₂`, `Pⁿ ≥ αⁿP₁ⁿ`. -/
theorem kpow_mixture_ge {κ₁ κ₂ : Kernel S S} [IsMarkovKernel κ₁] {α : ℝ}
    (hκ : ∀ s, κ s = ENNReal.ofReal α • κ₁ s + ENNReal.ofReal (1 - α) • κ₂ s) (hα : 0 ≤ α) :
    ∀ n s {A : Set S}, MeasurableSet A →
      ENNReal.ofReal (α ^ n) * kpow κ₁ n s A ≤ kpow κ n s A := by
  intro n
  induction n with
  | zero => intro s A hA; simp [kpow]
  | succ n ih =>
    intro s A hA
    rw [show n + 1 = 1 + n by ring, kpow_add_apply 1 n s hA, kpow_add_apply 1 n s hA, kpow_one,
      kpow_one]
    calc ENNReal.ofReal (α ^ (1 + n)) * ∫⁻ s', kpow κ₁ n s' A ∂κ₁ s
        = ∫⁻ s', ENNReal.ofReal (α ^ n) * kpow κ₁ n s' A ∂(ENNReal.ofReal α • κ₁ s) := by
          rw [lintegral_smul_measure, lintegral_const_mul _ (Kernel.measurable_coe _ hA),
            pow_add, pow_one, ENNReal.ofReal_mul hα, smul_eq_mul, mul_assoc]
      _ ≤ ∫⁻ s', ENNReal.ofReal (α ^ n) * kpow κ₁ n s' A ∂κ s :=
          lintegral_mono' (by rw [hκ s]; exact Measure.le_add_right le_rfl) le_rfl
      _ ≤ ∫⁻ s', kpow κ n s' A ∂κ s := lintegral_mono fun s' => ih s' hA

/-- **Exercise 11.4g.** If `P = αP₁ + (1 − α)P₂` with `α ∈ (0, 1)` and `P₁` satisfies Condition D
for `(φ, N, ε)`, then `P` satisfies it for `(φ, N, αᴺε)`. -/
theorem ex_11_4g {κ₁ κ₂ : Kernel S S} [IsMarkovKernel κ₁] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hκ : ∀ s, κ s = ENNReal.ofReal α • κ₁ s + ENNReal.ofReal (1 - α) • κ₂ s)
    {φ : Measure S} {N : ℕ} {ε : ℝ} (h₁ : DoeblinFor κ₁ φ N ε) :
    DoeblinFor κ φ N (α ^ N * ε) := by
  obtain ⟨hφ, hN, hε, hD⟩ := h₁
  have := isMarkov_kpow (κ := κ) N
  have := isMarkov_kpow (κ := κ₁) N
  have hαN : α ^ N ≤ 1 := pow_le_one₀ hα0.le hα1.le
  refine ⟨hφ, hN, by positivity, fun A hA hφA s => real_le_one_sub_of_compl hA ?_⟩
  have h1 : ε ≤ (kpow κ₁ N s).real Aᶜ := by
    have := hD A hA (hφA.trans (by nlinarith)) s
    have := probReal_compl_eq_one_sub (μ := kpow κ₁ N s) hA
    linarith
  have h2 := kpow_mixture_ge hκ hα0.le N s hA.compl
  have h3 := ENNReal.toReal_mono (measure_ne_top _ _) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h3
  change α ^ N * (kpow κ₁ N s).real Aᶜ ≤ (kpow κ N s).real Aᶜ at h3
  nlinarith [pow_pos hα0 N]

/-- The `n`-step transitions of a deterministic kernel: `Pⁿ(s, ·) = δ_{fⁿ(s)}`. -/
theorem kpow_deterministic {f : S → S} (hf : Measurable f) (n : ℕ) (s : S) :
    kpow (Kernel.deterministic f hf) n s = Measure.dirac (f^[n] s) := by
  induction n generalizing s with
  | zero => simp [kpow, Kernel.id_apply]
  | succ n ih =>
    rw [kpow, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply, ih,
      Function.iterate_succ_apply]

/-- A deterministic injective map on a space with infinitely many points violates Condition D:
a finite `φ` gives small mass to some point `fᴺ(yₖ)`, which `Pᴺ` reaches with probability one
from `yₖ`. -/
theorem not_conditionD_deterministic [MeasurableSingletonClass S] {f : S → S}
    (hf : Measurable f) (hinj : Function.Injective f) {y : ℕ → S}
    (hy : Function.Injective y) : ¬ ConditionD (Kernel.deterministic f hf) := by
  rintro ⟨φ, N, ε, hφ, -, hε, hD⟩
  obtain ⟨k, hk⟩ := exists_small_atom φ ((hinj.iterate N).comp hy) hε
  have := hD _ (measurableSet_singleton _) hk (y k)
  simp only [Function.comp_apply] at this
  rw [kpow_deterministic, measureReal_def, Measure.dirac_apply_of_mem (mem_singleton _),
    ENNReal.toReal_one] at this
  linarith

/-- **Exercise 11.4h.** The identity on a countably infinite set violates Condition D. -/
theorem ex_11_4h : ¬ ConditionD (Kernel.deterministic (id : ℕ → ℕ) measurable_id) :=
  not_conditionD_deterministic measurable_id Function.injective_id Function.injective_id

/-- **Exercise 11.4i.** The shift `sᵢ ↦ sᵢ₊₁` violates Condition D. -/
theorem ex_11_4i : ¬ ConditionD (Kernel.deterministic Nat.succ measurable_from_top) :=
  not_conditionD_deterministic measurable_from_top Nat.succ_injective Function.injective_id

/-- The halving map `s ↦ s/2` on `[0, 1]`. -/
noncomputable def halve (s : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨s.1 / 2, by have := s.2; constructor <;> linarith [this.1, this.2]⟩

theorem measurable_halve : Measurable halve :=
  (Continuous.subtype_mk (continuous_subtype_val.div_const 2) _).measurable

/-- **Exercise 11.4j.** The deterministic halving `P(s, A) = 1` iff `s/2 ∈ A` on `[0, 1]`
violates Condition D. -/
theorem ex_11_4j : ¬ ConditionD (Kernel.deterministic halve measurable_halve) := by
  refine not_conditionD_deterministic measurable_halve (fun a b h => ?_)
    (y := fun k => ⟨1 / (k + 1 : ℝ), by positivity, by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]⟩) ?_
  · have := congrArg Subtype.val h
    simp only [halve] at this
    exact Subtype.ext (by linarith)
  · intro j k h
    have := congrArg Subtype.val h
    simp only at this
    have : (j : ℝ) + 1 = k + 1 := by
      rwa [one_div, one_div, inv_inj] at this
    exact_mod_cast (by linarith : (j : ℝ) = k)

/-- **Exercise 11.5a** (for Exercise 11.4c). If `Pᴺ(s, {s₀}) > ε` for all `s`, Condition M
holds: `s₀` lies in `A` or in `Aᶜ`. -/
theorem ex_11_5a_c [MeasurableSingletonClass S] {s₀ : S} {N : ℕ} {ε : ℝ} (hN : 1 ≤ N)
    (hε : 0 < ε) (h : ∀ s, ε < (kpow κ N s).real {s₀}) : ConditionM κ := by
  have := isMarkov_kpow (κ := κ) N
  refine ⟨N, ε, hN, hε, fun A hA => ?_⟩
  by_cases hs₀ : s₀ ∈ A
  · exact Or.inl fun s => (h s).le.trans (measureReal_mono (Set.singleton_subset_iff.2 hs₀))
  · exact Or.inr fun s => (h s).le.trans (measureReal_mono (Set.singleton_subset_iff.2 hs₀))

/-- **Exercise 11.5a** (for Exercise 11.4e). A density bounded below by `δ > 0` gives Condition M
with `ε = δμ(S)/2`: one of `A`, `Aᶜ` has `μ`-measure at least `μ(S)/2`. -/
theorem ex_11_5a_e {μ : Measure S} [IsFiniteMeasure μ] {p : S → S → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ s x, δ ≤ p s x)
    (hκ : ∀ s A, MeasurableSet A → κ s A = ∫⁻ x in A, ENNReal.ofReal (p s x) ∂μ) :
    ConditionM κ := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · exact ⟨1, 1, le_rfl, one_pos, fun A _ => Or.inl fun s => isEmptyElim s⟩
  set m := μ.real univ
  have hm : 0 < m := by
    refine lt_of_le_of_ne measureReal_nonneg fun h0 => ?_
    have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.1
      ((ENNReal.toReal_eq_zero_iff _).1 h0.symm |>.resolve_right (measure_ne_top μ univ))
    have := hκ s₀ univ MeasurableSet.univ
    rw [measure_univ, hμ0, Measure.restrict_zero, lintegral_zero_measure] at this
    exact one_ne_zero this
  have hlow : ∀ s {A : Set S}, MeasurableSet A → δ * μ.real A ≤ (κ s).real A := fun s A hA => by
    have := ENNReal.toReal_mono (measure_ne_top _ _) (density_lower hp hκ s hA)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le] at this
  refine ⟨1, δ * m / 2, le_rfl, by positivity, fun A hA => ?_⟩
  simp only [kpow_one]
  have hsum : μ.real A + μ.real Aᶜ = m := measureReal_add_measureReal_compl hA
  rcases le_total (m / 2) (μ.real A) with hA2 | hA2
  · exact Or.inl fun s => le_trans (by nlinarith) (hlow s hA)
  · exact Or.inr fun s => le_trans (by nlinarith) (hlow s hA.compl)

/-- **Exercise 11.5b.** Condition M implies Condition D (with `φ = Pᴺ(s₀, ·)` and `ε/2`). -/
theorem ex_11_5b (h : ConditionM κ) : ConditionD κ := by
  obtain ⟨N, ε, hN, hε, hM⟩ := h
  have := isMarkov_kpow (κ := κ) N
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · exact ⟨0, 1, 1, inferInstance, le_rfl, one_pos, fun A _ _ s => isEmptyElim s⟩
  refine ⟨kpow κ N s₀, N, ε / 2, inferInstance, hN, by positivity, fun A hA hφA s => ?_⟩
  rcases hM A hA with h1 | h2
  · have := h1 s₀; linarith
  · have := real_le_one_sub_of_compl hA (h2 s); linarith

/-- **Exercise 11.5c.** The identity on two points satisfies Condition D (Exercise 11.4a) but not
Condition M: from `true` the set `{false}` is never reached, and from `false` its complement
`{true}` is never reached. -/
theorem ex_11_5c :
    ConditionD (Kernel.deterministic (id : Bool → Bool) measurable_id) ∧
      ¬ ConditionM (Kernel.deterministic (id : Bool → Bool) measurable_id) := by
  refine ⟨ex_11_4a, ?_⟩
  rintro ⟨N, ε, -, hε, hM⟩
  rcases hM {false} (measurableSet_singleton _) with h | h
  · have := h true
    rw [kpow_deterministic, measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
      at this
    simp at this; linarith
  · have := h false
    rw [kpow_deterministic, measureReal_def,
      Measure.dirac_apply' _ (measurableSet_singleton _).compl] at this
    simp at this; linarith

end StokeyLucasPrescott.StrongConvergence
