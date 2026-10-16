/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Weak convergence: basic tools

SLP §12.1, pp. 353–358. `(S, ρ)` is a metric space with its Borel sets.

* **Exercise 12.1** (`ex_12_1`): for a Borel `S ⊆ ℝˡ`, the Borel sets of `S` are the Borel sets of
  `ℝˡ` contained in `S`; relatively open sets are traces of open sets; relative interiors are
  relatively open; and an open set is its own interior.
* **Exercise 12.2** (`ex_12_2`): the distance `ρ(s, A)` is `1`-Lipschitz, hence uniformly
  continuous, and `Ā = {s : ρ(s, A) = 0}` for nonempty `A`.
* `ConvWeak` (p. 354): `λₙ ⇒ λ` if `∫ f dλₙ → ∫ f dλ` for every bounded continuous `f`.
* **Lemma 12.1** (`lemma_12_1`): for a closed `F` the continuous functions
  `fₙ(s) = max(0, 1 − n ρ(s, F))` decrease, equal `1` on `F`, lie in `[0, 1]`, and
  `∫ fₙ dλ → λ(F)` for every probability measure `λ`. The book proves the limit with the sets
  `Fₙ = {ρ(·, F) ≤ 1/n}`; here dominated convergence is used.
* **Lemma 12.2** (`lemma_12_2`): for measurable `a ≤ f < b`, the sets `Fᵢ = {f ≥ a + ic/k}` give
  `a + (c/k) Σ μ(Fᵢ) ≤ ∫ f dμ ≤ a + (c/k) Σ μ(Fᵢ) + ε` for every probability `μ`. The `Fᵢ` are
  closed if `f` is continuous. The book sums by parts; here the pointwise inequality
  `m/k ≤ g < (m + 1)/k`, with `m = #{i ≤ k : i/k ≤ g}`, is integrated.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory Filter Topology Set BoundedContinuousFunction

/-- **Exercise 12.1.** For a Borel set `S ⊆ ℝˡ`: (a) the Borel sets of `S` are the Borel subsets
of `ℝˡ` contained in `S`; (b) the relatively open sets are the traces `A′ ∩ S` of open sets;
(c) relative interiors are relatively open; (d) a relatively open set is its own interior. -/
theorem ex_12_1 {l : ℕ} {S : Set (Fin l → ℝ)} (hS : MeasurableSet S) :
    (∀ A : Set S, MeasurableSet A ↔ MeasurableSet (Subtype.val '' A)) ∧
      (∀ A : Set S, IsOpen A ↔ ∃ A' : Set (Fin l → ℝ), IsOpen A' ∧ Subtype.val ⁻¹' A' = A) ∧
      (∀ A : Set S, IsOpen (interior A)) ∧ ∀ A : Set S, IsOpen A → interior A = A := by
  refine ⟨fun A => ⟨fun hA => hS.subtype_image hA, fun hA => ?_⟩, fun A => isOpen_induced_iff,
    fun A => isOpen_interior, fun A hA => hA.interior_eq⟩
  have := (measurable_subtype_coe (p := fun x => x ∈ S)) hA
  rwa [Subtype.val_injective.preimage_image] at this

variable {S : Type*} [MetricSpace S]

/-- **Exercise 12.2.** (a) `|ρ(x, A) − ρ(y, A)| ≤ ρ(x, y)`; (b) `ρ(·, A)` is uniformly
continuous; (c) for nonempty `A`, `Ā = {s : ρ(s, A) = 0}`. -/
theorem ex_12_2 (A : Set S) :
    (∀ x y, |Metric.infDist x A - Metric.infDist y A| ≤ dist x y) ∧
      UniformContinuous (fun s => Metric.infDist s A) ∧
      (A.Nonempty → closure A = {s | Metric.infDist s A = 0}) := by
  refine ⟨fun x y => ?_, (Metric.lipschitz_infDist_pt A).uniformContinuous, fun hA => ?_⟩
  · have := (Metric.lipschitz_infDist_pt A).dist_le_mul x y
    rwa [NNReal.coe_one, one_mul, Real.dist_eq] at this
  · ext s; exact Metric.mem_closure_iff_infDist_zero hA

/-- The functions of Lemma 12.1: `fₙ(s) = max(0, 1 − (n + 1) ρ(s, F))`. -/
noncomputable def bump (F : Set S) (n : ℕ) (s : S) : ℝ :=
  max 0 (1 - (n + 1) * Metric.infDist s F)

theorem continuous_bump (F : Set S) (n : ℕ) : Continuous (bump F n) :=
  continuous_const.max (continuous_const.sub (continuous_const.mul
    (Metric.continuous_infDist_pt F)))

theorem bump_mem (F : Set S) (n : ℕ) (s : S) : 0 ≤ bump F n s ∧ bump F n s ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (by
    have := Metric.infDist_nonneg (x := s) (s := F)
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])⟩

theorem bump_eq_one {F : Set S} {s : S} (hs : s ∈ F) (n : ℕ) : bump F n s = 1 := by
  simp [bump, Metric.infDist_zero_of_mem hs]

theorem bump_antitone (F : Set S) (s : S) : Antitone fun n => bump F n s := fun m n hmn => by
  refine max_le_max le_rfl (sub_le_sub_left (mul_le_mul_of_nonneg_right ?_
    Metric.infDist_nonneg) 1)
  exact_mod_cast Nat.succ_le_succ hmn

/-- `fₙ → 1_F` pointwise for closed nonempty `F`. -/
theorem tendsto_bump {F : Set S} (hF : IsClosed F) (hne : F.Nonempty) (s : S) :
    Tendsto (fun n => bump F n s) atTop (𝓝 (F.indicator 1 s)) := by
  by_cases hs : s ∈ F
  · simp [bump_eq_one hs, indicator_of_mem hs]
  · rw [indicator_of_notMem hs]
    have hpos : 0 < Metric.infDist s F :=
      (hF.notMem_iff_infDist_pos hne).1 hs
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / Metric.infDist s F)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have : 1 ≤ (n + 1) * Metric.infDist s F := by
      rw [div_lt_iff₀ hpos] at hN
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    simp only [bump]
    exact (max_eq_left (by linarith)).symm

variable [MeasurableSpace S] [BorelSpace S]

/-- `λₙ` **converges weakly** to `λ` (p. 354): `∫ f dλₙ → ∫ f dλ` for every bounded continuous
`f`. -/
def ConvWeak (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ∀ f : S →ᵇ ℝ, Tendsto (fun n => ∫ s, f s ∂ls n) atTop (𝓝 (∫ s, f s ∂l))

/-- **Lemma 12.1.** For a closed set `F` there are continuous `fₙ`, decreasing in `n`, with
`fₙ = 1` on `F`, `0 ≤ fₙ ≤ 1`, and `∫ fₙ dλ → λ(F)` for every probability measure `λ`. -/
theorem lemma_12_1 {F : Set S} (hF : IsClosed F) :
    ∃ f : ℕ → S → ℝ, (∀ n, Continuous (f n)) ∧ (∀ s, Antitone fun n => f n s) ∧
      (∀ n, ∀ s ∈ F, f n s = 1) ∧ (∀ n s, 0 ≤ f n s ∧ f n s ≤ 1) ∧
      ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        Tendsto (fun n => ∫ s, f n s ∂μ) atTop (𝓝 (μ.real F)) := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => 0, fun _ => continuous_const, fun _ _ _ _ => le_rfl, fun _ s hs => hs.elim,
      fun _ _ => ⟨le_rfl, zero_le_one⟩, fun μ _ => by simp⟩
  refine ⟨bump F, continuous_bump F, bump_antitone F, fun n s hs => bump_eq_one hs n,
    bump_mem F, fun μ _ => ?_⟩
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (F := bump F)
    (f := F.indicator 1) (fun _ => 1)
    (fun n => (continuous_bump F n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (bump_mem F n s).1]; exact (bump_mem F n s).2)
    (Eventually.of_forall fun s => tendsto_bump hF hne s)
  rwa [integral_indicator_one hF.measurableSet] at hlim

/-- For `0 ≤ g < 1` and `m = #{1 ≤ i ≤ k : i/k ≤ g}`: `m/k ≤ g < (m + 1)/k`. -/
theorem count_bounds {k : ℕ} (hk : 1 ≤ k) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) :
    (((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g).card : ℝ) / k ≤ g ∧
      g < (((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g).card + 1 : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hkg : 0 ≤ k * g := mul_nonneg hk'.le hg0
  have hfloor : ⌊(k : ℝ) * g⌋₊ ≤ k := by
    have : (k : ℝ) * g < k := by nlinarith
    exact_mod_cast (Nat.floor_le hkg).trans this.le
  have hset : ((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g) =
      Finset.Icc 1 ⌊(k : ℝ) * g⌋₊ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [div_le_iff₀ hk', mul_comm g, ← Nat.le_floor_iff hkg]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hfloor⟩, h3⟩
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  constructor
  · rw [div_le_iff₀ hk']; have := Nat.floor_le hkg; linarith [mul_comm (k : ℝ) g]
  · rw [lt_div_iff₀ hk', mul_comm]; exact Nat.lt_floor_add_one _

omit [BorelSpace S] in
/-- **Lemma 12.2.** For measurable `f` with `a ≤ f < b`, `c = b − a`, and `ε > 0`, there are `k ≥ 1`
and sets `Fᵢ = {f ≥ a + ic/k}`, `1 ≤ i ≤ k`, independent of `μ`, with
`a + (c/k) Σ μ(Fᵢ) ≤ ∫ f dμ ≤ a + (c/k) Σ μ(Fᵢ) + ε` for every probability `μ`. If `f` is
continuous the `Fᵢ` are closed. -/
theorem lemma_12_2 {f : S → ℝ} (hf : Measurable f) {a b : ℝ} (hab : ∀ s, a ≤ f s ∧ f s < b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ F : ℕ → Set S, (∀ i, MeasurableSet (F i)) ∧
      (Continuous f → ∀ i, IsClosed (F i)) ∧
      ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        a + (b - a) / k * ∑ i ∈ Finset.Icc 1 k, μ.real (F i) ≤ ∫ s, f s ∂μ ∧
          ∫ s, f s ∂μ ≤ a + (b - a) / k * ∑ i ∈ Finset.Icc 1 k, μ.real (F i) + ε := by
  set k := ⌈(b - a) / ε⌉₊ + 1
  have hk : 1 ≤ k := Nat.le_add_left 1 _
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set F : ℕ → Set S := fun i => {s | a + (b - a) * i / k ≤ f s}
  refine ⟨k, hk, F, fun i => measurableSet_le measurable_const hf,
    fun hc i => isClosed_le continuous_const hc, fun μ _ => ?_⟩
  obtain ⟨s₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hba : 0 < b - a := by have := hab s₀; linarith
  have hck : (b - a) / k ≤ ε := by
    rw [div_le_iff₀ hk']
    have := Nat.le_ceil ((b - a) / ε)
    rw [div_le_iff₀ hε] at this
    have : (⌈(b - a) / ε⌉₊ : ℝ) ≤ k := by simp [k]
    nlinarith
  -- the pointwise inequality, with `g = (f − a)/(b − a)`
  set cnt : S → ℝ := fun s => ∑ i ∈ Finset.Icc 1 k, (F i).indicator 1 s
  have hcnt : ∀ s, cnt s = (((Finset.Icc 1 k).filter fun i : ℕ =>
      (i : ℝ) / k ≤ (f s - a) / (b - a)).card : ℝ) := fun s => by
    simp only [cnt, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : a + (b - a) * i / k ≤ f s ↔ (i : ℝ) / k ≤ (f s - a) / (b - a) := by
      have e : (b - a) * (i : ℝ) / k = (i : ℝ) / k * (b - a) := by ring
      rw [le_div_iff₀ hba, ← e]; constructor <;> intro h <;> linarith
    by_cases h : a + (b - a) * i / k ≤ f s
    · have hm : s ∈ F i := h
      simp [Set.indicator_of_mem hm, this.1 h]
    · have hm : s ∉ F i := h
      have h2 : ¬ ((i : ℝ) / k ≤ (f s - a) / (b - a)) := fun h' => h (this.2 h')
      simp [Set.indicator_of_notMem hm, h2]
  have hpt : ∀ s, (b - a) / k * cnt s ≤ f s - a ∧ f s - a ≤ (b - a) / k * cnt s + (b - a) / k := by
    intro s
    obtain ⟨h1, h2⟩ := hab s
    obtain ⟨c1, c2⟩ := count_bounds hk (g := (f s - a) / (b - a)) (div_nonneg (by linarith) hba.le)
      ((div_lt_one hba).2 (by linarith))
    rw [hcnt]
    constructor
    · calc (b - a) / k * _ = (b - a) * (_ / k) := by ring
        _ ≤ (b - a) * ((f s - a) / (b - a)) := mul_le_mul_of_nonneg_left c1 hba.le
        _ = f s - a := by field_simp
    · calc f s - a = (b - a) * ((f s - a) / (b - a)) := by field_simp
        _ ≤ (b - a) * ((_ + 1) / k) := mul_le_mul_of_nonneg_left c2.le hba.le
        _ = _ := by ring
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable (|a| + |b|)
    (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_le]; obtain ⟨h1, h2⟩ := hab s
      constructor <;> linarith [abs_nonneg a, abs_nonneg b, neg_abs_le a, le_abs_self b])
  have hci : Integrable cnt μ := integrable_finsetSum _ fun i _ =>
    (integrable_const 1).indicator (measurableSet_le measurable_const hf)
  have hint_cnt : ∫ s, cnt s ∂μ = ∑ i ∈ Finset.Icc 1 k, μ.real (F i) := by
    rw [integral_finsetSum _ fun i _ => (integrable_const 1).indicator
      (measurableSet_le measurable_const hf)]
    exact Finset.sum_congr rfl fun i _ => integral_indicator_one
      (measurableSet_le measurable_const hf)
  have hfa : Integrable (fun s => f s - a) μ := hfi.sub (integrable_const a)
  have hca : Integrable (fun s => (b - a) / k * cnt s + (b - a) / k) μ :=
    (hci.const_mul _).add (integrable_const _)
  have hlo := integral_mono (hci.const_mul ((b - a) / k)) hfa fun s => (hpt s).1
  have hhi := integral_mono hfa hca fun s => (hpt s).2
  rw [integral_const_mul, hint_cnt, integral_sub hfi (integrable_const a)] at hlo
  rw [integral_add (hci.const_mul _) (integrable_const _), integral_const_mul, hint_cnt,
    integral_sub hfi (integrable_const a)] at hhi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlo hhi
  constructor <;> linarith

end StokeyLucasPrescott.ConvergenceApplications
