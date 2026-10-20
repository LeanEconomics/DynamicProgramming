import Mathlib
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Almost everywhere convergence and convergence in probability

SLP Chapter 14, introduction and §14.1, pp. 415–420.

* Convergence almost everywhere (`ConvAE`) and in probability (`ConvInProb`).
* **Lemma 14.1** (`lemma_14_1`): `fₙ → f` a.e. iff `μ(|fₙ − f| ≤ ε for all n ≥ m) → 1` for every
  `ε > 0`.
* `μ(Aₙ i.o.) = lim_m μ(⋃_{n≥m} Aₙ)` (`measure_limsupSet`, (2) on p. 418).
* **Lemma 14.2** (`lemma_14_2`): `fₙ → f` a.e. iff `μ(|fₙ − f| > ε i.o.) = 0` for every `ε > 0`.
* **Lemma 14.3** (`lemma_14_3`, the first Borel–Cantelli lemma applied).
* A.e. convergence implies convergence in probability (`ConvAE.convInProb`).
* **Exercise 14.1**: the sliding indicators converge nowhere, but converge to `0` in
  probability, and their diagonal subsequence converges everywhere (`ex_14_1a`, `ex_14_1b`,
  `ex_14_1c`).
* **Exercise 14.2**: summable `μ(|fₙ − f| > εₙ)` with `εₙ → 0` gives a.e. convergence;
  convergence in probability gives an a.e. convergent subsequence (`ex_14_2a`, `ex_14_2b`).
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `fₙ → f` almost everywhere (p. 415). -/
def ConvAE (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))

/-- `fₙ → f` in probability (p. 415). -/
def ConvInProb (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n => μ {ω | ε < |f n ω - g ω|}) atTop (𝓝 0)

/-- `lim sup Aₙ = ⋂ₘ ⋃_{n≥m} Aₙ`, the event "`Aₙ` infinitely often" (p. 418). -/
def limsupSet (A : ℕ → Set Ω) : Set Ω := ⋂ m, ⋃ n ≥ m, A n

omit [MeasurableSpace Ω] in
theorem mem_limsupSet {A : ℕ → Set Ω} {ω : Ω} : ω ∈ limsupSet A ↔ ∃ᶠ n in atTop, ω ∈ A n := by
  simp only [limsupSet, mem_iInter, mem_iUnion, exists_prop, frequently_atTop]

/-- (2), p. 418: `μ(Aₙ i.o.) = lim_m μ(⋃_{n≥m} Aₙ)`. -/
theorem measure_limsupSet (μ : Measure Ω) [IsFiniteMeasure μ] {A : ℕ → Set Ω}
    (hA : ∀ n, MeasurableSet (A n)) :
    Tendsto (fun m => μ (⋃ n ≥ m, A n)) atTop (𝓝 (μ (limsupSet A))) :=
  tendsto_measure_iInter_atTop
    (fun _ => (MeasurableSet.biUnion (to_countable _) fun n _ => hA n).nullMeasurableSet)
    (fun m₁ m₂ h => biUnion_subset_biUnion_left fun n (hn : m₂ ≤ n) => (h.trans hn : m₁ ≤ n))
    ⟨0, measure_ne_top _ _⟩

theorem measurableSet_dev {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (hf : ∀ n, Measurable (f n))
    (hg : Measurable g) (ε : ℝ) (n : ℕ) : MeasurableSet {ω | ε < |f n ω - g ω|} :=
  measurableSet_lt measurable_const ((hf n).sub hg).abs

/-- **Lemma 14.1.** `fₙ → f` a.e. iff `μ(|fₙ − f| ≤ ε for all n ≥ m) → 1` for every `ε > 0`. -/
theorem lemma_14_1 (μ : Measure Ω) [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) :
    ConvAE μ f g ↔
      ∀ ε > 0, Tendsto (fun m => μ {ω | ∀ n ≥ m, |f n ω - g ω| ≤ ε}) atTop (𝓝 1) := by
  set A : ℝ → ℕ → Set Ω := fun ε m => {ω | ∀ n ≥ m, |f n ω - g ω| ≤ ε}
  have hAm : ∀ ε m, MeasurableSet (A ε m) := fun ε m => by
    have : A ε m = ⋂ n, ⋂ (_ : n ≥ m), {ω | |f n ω - g ω| ≤ ε} := by
      ext ω; simp [A]
    rw [this]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      measurableSet_le ((hf n).sub hg).abs measurable_const
  have hmono : ∀ ε, Monotone (A ε) := fun ε m₁ m₂ h ω hω n hn => hω n (h.trans hn)
  have hlim : ∀ ε, Tendsto (fun m => μ (A ε m)) atTop (𝓝 (μ (⋃ m, A ε m))) := fun ε =>
    tendsto_measure_iUnion_atTop (hmono ε)
  constructor
  · intro h ε hε
    have h1 : μ (⋃ m, A ε m) = 1 := by
      rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion (hAm ε))]
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h)
      simp only [mem_ofPred_eq]
      intro ht
      obtain ⟨m, hm⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 ht) ε hε)
      exact hω (mem_iUnion.2 ⟨m, fun n hn => by
        have := hm n hn; rw [Real.dist_eq] at this; exact this.le⟩)
    rw [← h1]; exact hlim ε
  · intro h
    have hfull : ∀ k : ℕ, μ (⋃ m, A (1 / ((k : ℝ) + 1)) m) = 1 := fun k =>
      tendsto_nhds_unique (hlim _) (h _ (by positivity))
    have hae : ∀ᵐ ω ∂μ, ∀ k : ℕ, ω ∈ ⋃ m, A (1 / ((k : ℝ) + 1)) m := by
      rw [ae_all_iff]
      intro k
      rw [ae_iff, ← compl_def]
      exact (prob_compl_eq_zero_iff (MeasurableSet.iUnion (hAm _))).2 (hfull k)
    filter_upwards [hae] with ω hω
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    obtain ⟨m, hm⟩ := mem_iUnion.1 (hω k)
    exact ⟨m, fun n hn => by rw [Real.dist_eq]; exact lt_of_le_of_lt (hm n hn) hk⟩

/-- **Lemma 14.2.** `fₙ → f` a.e. iff `μ(|fₙ − f| > ε i.o.) = 0` for every `ε > 0`. -/
theorem lemma_14_2 (μ : Measure Ω) {f : ℕ → Ω → ℝ} {g : Ω → ℝ} :
    ConvAE μ f g ↔ ∀ ε > 0, μ (limsupSet fun n => {ω | ε < |f n ω - g ω|}) = 0 := by
  constructor
  · intro h ε hε
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h)
    simp only [mem_ofPred_eq]
    intro ht
    rw [mem_limsupSet] at hω
    obtain ⟨m, hm⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 ht) ε hε)
    obtain ⟨n, hn, hn'⟩ := frequently_atTop.1 hω m
    have := hm n hn
    rw [Real.dist_eq] at this
    exact absurd hn' (not_lt.2 this.le)
  · intro h
    have hae : ∀ᵐ ω ∂μ, ∀ k : ℕ,
        ω ∉ limsupSet fun n => {ω | 1 / ((k : ℝ) + 1) < |f n ω - g ω|} := by
      rw [ae_all_iff]
      intro k
      rw [ae_iff]
      simpa using h (1 / ((k : ℝ) + 1)) (by positivity)
    filter_upwards [hae] with ω hω
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    have := hω k
    rw [mem_limsupSet, not_frequently] at this
    obtain ⟨m, hm⟩ := eventually_atTop.1 this
    exact ⟨m, fun n hn => by
      rw [Real.dist_eq]
      have := hm n hn
      simp only [mem_ofPred_eq, not_lt] at this
      exact lt_of_le_of_lt this hk⟩

/-- The first Borel–Cantelli lemma, `Σ μ(Aₙ) < ∞ ⇒ μ(Aₙ i.o.) = 0` (proof of Lemma 14.3). -/
theorem measure_limsupSet_eq_zero (μ : Measure Ω) {A : ℕ → Set Ω} (hA : ∑' n, μ (A n) ≠ ∞) :
    μ (limsupSet A) = 0 := by
  have := measure_limsup_atTop_eq_zero (μ := μ) hA
  rwa [limsup_eq_iInf_iSup_of_nat] at this

/-- **Lemma 14.3.** If `Σₙ μ(|fₙ − f| > ε) < ∞` for every `ε > 0`, then `fₙ → f` a.e. -/
theorem lemma_14_3 (μ : Measure Ω) {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (h : ∀ ε > 0, ∑' n, μ {ω | ε < |f n ω - g ω|} ≠ ∞) : ConvAE μ f g :=
  (lemma_14_2 μ).2 fun ε hε => measure_limsupSet_eq_zero μ (h ε hε)

/-- A.e. convergence implies convergence in probability (p. 420). -/
theorem ConvAE.convInProb {μ : Measure Ω} [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) (h : ConvAE μ f g) : ConvInProb μ f g := by
  intro ε hε
  have h0 := (lemma_14_2 μ).1 h ε hε
  have hlim := measure_limsupSet μ (measurableSet_dev hf hg ε)
  rw [h0] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun m => zero_le) fun m => measure_mono (subset_biUnion_of_mem (u := fun n =>
      {ω | ε < |f n ω - g ω|}) (le_refl m))

/-- **Exercise 14.2a.** If `εₙ → 0` and `Σₙ μ(|fₙ − f| > εₙ) < ∞`, then `fₙ → f` a.e. -/
theorem ex_14_2a (μ : Measure Ω) {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (h : ∑' n, μ {ω | ε n < |f n ω - g ω|} ≠ ∞) :
    ConvAE μ f g := by
  have h0 := measure_limsupSet_eq_zero μ h
  rw [ConvAE, ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h0
  simp only [mem_ofPred_eq] at hω
  rw [mem_limsupSet]
  intro hev
  apply hω
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hε
  filter_upwards [hev] with n hn
  simp only [not_lt] at hn
  rw [norm_norm, Real.norm_eq_abs]
  exact hn

/-- **Exercise 14.2b.** Convergence in probability gives an a.e. convergent subsequence. -/
theorem ex_14_2b (μ : Measure Ω) {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (h : ConvInProb μ f g) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvAE μ (fun k => f (φ k)) g := by
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop,
      μ {ω | 1 / ((k : ℝ) + 1) < |f n ω - g ω|} ≤ ((2 : ℝ≥0∞)⁻¹) ^ k := fun k =>
    (h _ (by positivity)).eventually (ge_mem_nhds
      (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) k))
  obtain ⟨φ, hφ, hφk⟩ := extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ex_14_2a μ (ε := fun k => 1 / ((k : ℝ) + 1))
    tendsto_one_div_add_atTop_nhds_zero_nat ?_⟩
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hφk)
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.ofNat_ne_top

end StokeyLucasPrescott.LawsOfLargeNumbers

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 14.1: convergence in probability without a.e. convergence

SLP p. 420. On `[0, 1)` with Lebesgue measure, list the indicators `f_{ni}` of `[(i−1)/n, i/n)`,
`1 ≤ i ≤ n`, row by row. Rows are indexed here from `0`: the `k`-th function lies in row
`r = row k` (the row whose block `[tri r, tri (r+1))` contains `k`, with `tri r = 0 + 1 + ⋯ + r`) at
position `i = k − tri r ∈ {0, …, r}`, and is the indicator of `[i/(r+1), (i+1)/(r+1))`.

* (a) the sequence converges at no point of `[0, 1)` (`ex_14_1a`);
* (b) it converges to `0` in probability (`ex_14_1b`);
* (c) the diagonal subsequence (the last function of each row, the indicator of
  `[r/(r+1), 1)`) converges to `0` at every point of `[0, 1)`, hence a.e. (`ex_14_1c`).
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The triangular numbers `tri r = 0 + 1 + ⋯ + r`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | r + 1 => tri r + (r + 1)

theorem tri_succ (r : ℕ) : tri (r + 1) = tri r + (r + 1) := rfl

theorem le_tri (r : ℕ) : r ≤ tri r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [tri_succ]; omega

theorem tri_mono : Monotone tri :=
  monotone_nat_of_le_succ fun r => by rw [tri_succ]; omega

theorem exists_row (k : ℕ) : ∃ r, k < tri (r + 1) := ⟨k, by
  have := le_tri (k + 1); omega⟩

/-- The row containing index `k`. -/
def row (k : ℕ) : ℕ := Nat.find (exists_row k)

theorem row_spec (k : ℕ) : tri (row k) ≤ k ∧ k < tri (row k + 1) := by
  refine ⟨?_, Nat.find_spec (exists_row k)⟩
  rcases h : row k with _ | r
  · exact Nat.zero_le _
  · have := Nat.find_min (exists_row k) (show r < row k by omega)
    omega

theorem row_eq {k r : ℕ} (h1 : tri r ≤ k) (h2 : k < tri (r + 1)) : row k = r := by
  obtain ⟨h3, h4⟩ := row_spec k
  rcases lt_trichotomy (row k) r with h | h | h
  · have := tri_mono (show row k + 1 ≤ r by omega); omega
  · exact h
  · have := tri_mono (show r + 1 ≤ row k by omega); omega

/-- The position of index `k` in its row. -/
def pos (k : ℕ) : ℕ := k - tri (row k)

theorem pos_le (k : ℕ) : pos k ≤ row k := by
  have := row_spec k; rw [tri_succ] at this; unfold pos; omega

theorem row_tri_add {r i : ℕ} (hi : i ≤ r) : row (tri r + i) = r ∧ pos (tri r + i) = i := by
  have hr : row (tri r + i) = r := row_eq (by omega) (by rw [tri_succ]; omega)
  exact ⟨hr, by unfold pos; rw [hr]; omega⟩

theorem le_row {k r : ℕ} (hk : tri r ≤ k) : r ≤ row k := by
  by_contra h
  have := tri_mono (show row k + 1 ≤ r by omega)
  have := (row_spec k).2
  omega

/-- The interval `[i/(r+1), (i+1)/(r+1))` of index `k`. -/
def slideSet (k : ℕ) : Set ℝ :=
  Ico ((pos k : ℝ) / (row k + 1)) (((pos k : ℝ) + 1) / (row k + 1))

/-- The `k`-th function of the sequence of Exercise 14.1. -/
noncomputable def sliding (k : ℕ) (ω : ℝ) : ℝ := (slideSet k).indicator 1 ω

/-- Lebesgue measure on `[0, 1)`. -/
noncomputable def unitLeb : Measure ℝ := volume.restrict (Ico 0 1)

theorem sliding_eq_one {k : ℕ} {ω : ℝ} (h : ω ∈ slideSet k) : sliding k ω = 1 := by
  simp [sliding, h]

theorem sliding_eq_zero {k : ℕ} {ω : ℝ} (h : ω ∉ slideSet k) : sliding k ω = 0 := by
  simp [sliding, h]

/-- In every row `r ≥ 1` some function is `1` at `ω` and some is `0`. -/
theorem row_one_zero {ω : ℝ} (hω : ω ∈ Ico (0 : ℝ) 1) {r : ℕ} (hr : 1 ≤ r) :
    (∃ k, tri r ≤ k ∧ sliding k ω = 1) ∧ ∃ k, tri r ≤ k ∧ sliding k ω = 0 := by
  have hr1 : (0 : ℝ) < r + 1 := by positivity
  set i := ⌊ω * (r + 1)⌋₊
  have hx0 : 0 ≤ ω * (r + 1) := mul_nonneg hω.1 hr1.le
  have hxlt : ω * (r + 1) < r + 1 := by nlinarith [hω.2]
  have hil : (i : ℝ) ≤ ω * (r + 1) := Nat.floor_le hx0
  have hiu : ω * (r + 1) < i + 1 := Nat.lt_floor_add_one _
  have hir : i ≤ r := by
    have : (i : ℝ) < r + 1 := lt_of_le_of_lt hil hxlt
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have hmem : ∀ j, j ≤ r → (ω ∈ slideSet (tri r + j) ↔ j = i) := fun j hj => by
    obtain ⟨h1, h2⟩ := row_tri_add hj
    simp only [slideSet, h1, h2, mem_Ico, div_le_iff₀ hr1, lt_div_iff₀ hr1]
    constructor
    · rintro ⟨ha, hb⟩
      have e1 : j ≤ i := Nat.le_floor (by linarith)
      have e2 : i < j + 1 := by
        have : (i : ℝ) < j + 1 := lt_of_le_of_lt hil (by linarith)
        exact_mod_cast this
      omega
    · rintro rfl; constructor <;> linarith
  refine ⟨⟨tri r + i, by omega, sliding_eq_one ((hmem i hir).2 rfl)⟩, ?_⟩
  set j := if i = 0 then 1 else 0
  have hj : j ≤ r := by simp only [j]; split_ifs <;> omega
  have hji : j ≠ i := by simp only [j]; split_ifs <;> omega
  exact ⟨tri r + j, by omega, sliding_eq_zero fun h => hji ((hmem j hj).1 h)⟩

/-- **Exercise 14.1a.** The sequence converges at no point of `[0, 1)`. -/
theorem ex_14_1a {ω : ℝ} (hω : ω ∈ Ico (0 : ℝ) 1) :
    ¬ ∃ L, Tendsto (fun k => sliding k ω) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hL) (1 / 2) (by norm_num))
  obtain ⟨⟨k₁, hk₁, h1⟩, ⟨k₀, hk₀, h0⟩⟩ := row_one_zero hω (le_max_right K 1)
  have e1 := hK k₁ ((le_max_left K 1).trans ((le_tri _).trans hk₁))
  have e0 := hK k₀ ((le_max_left K 1).trans ((le_tri _).trans hk₀))
  rw [h1, Real.dist_eq] at e1
  rw [h0, Real.dist_eq] at e0
  rw [abs_lt] at e1 e0
  linarith [e1.1, e0.2]

/-- **Exercise 14.1b.** The sequence converges to `0` in probability. -/
theorem ex_14_1b : ConvInProb unitLeb sliding fun _ => 0 := by
  intro ε hε
  have hrow : Tendsto row atTop atTop := tendsto_atTop.2 fun r =>
    eventually_atTop.2 ⟨tri r, fun k hk => le_row hk⟩
  have hlen : Tendsto (fun k => ENNReal.ofReal (1 / ((row k : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.comp hrow)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlen
    (fun k => zero_le) fun k => ?_
  have hsub : {ω | ε < |sliding k ω - 0|} ⊆ slideSet k := fun ω hω => by
    by_contra h
    simp only [mem_ofPred_eq, sliding_eq_zero h, sub_zero, abs_zero] at hω
    linarith
  calc unitLeb {ω | ε < |sliding k ω - 0|} ≤ volume (slideSet k) :=
        (Measure.restrict_le_self _).trans (measure_mono hsub)
    _ = ENNReal.ofReal (1 / ((row k : ℝ) + 1)) := by
        rw [slideSet, Real.volume_Ico]
        congr 1
        field_simp
        ring

/-- **Exercise 14.1c.** The diagonal subsequence (the indicator of `[r/(r+1), 1)`, last in row
`r`) converges to `0` at every point of `[0, 1)`, hence a.e. -/
theorem ex_14_1c :
    StrictMono (fun r => tri r + r) ∧
      (∀ ω ∈ Ico (0 : ℝ) 1, Tendsto (fun r => sliding (tri r + r) ω) atTop (𝓝 0)) ∧
      ConvAE unitLeb (fun r => sliding (tri r + r)) fun _ => 0 := by
  have hpt : ∀ ω ∈ Ico (0 : ℝ) 1, Tendsto (fun r => sliding (tri r + r) ω) atTop (𝓝 0) := by
    intro ω hω
    obtain ⟨R, hR⟩ := exists_nat_gt (1 / (1 - ω))
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨R, fun r hr => ?_⟩)
    obtain ⟨h1, h2⟩ := row_tri_add (le_refl r)
    have hr1 : (0 : ℝ) < r + 1 := by positivity
    have h1ω : 0 < 1 - ω := by linarith [hω.2]
    refine (sliding_eq_zero fun h => ?_).symm
    simp only [slideSet, h1, h2, mem_Ico, div_le_iff₀ hr1] at h
    have hR' : (R : ℝ) ≤ r := by exact_mod_cast hr
    rw [div_lt_iff₀ h1ω] at hR
    nlinarith [h.1]
  refine ⟨fun a b hab => ?_, hpt, ?_⟩
  · have := tri_mono hab.le; change tri a + a < tri b + b; omega
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with ω hω
    exact hpt ω hω

end StokeyLucasPrescott.LawsOfLargeNumbers

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Laws of large numbers for uncorrelated random variables

SLP §14.1, pp. 421–423.

* **Chebyshev's inequality** (`chebyshev`, (3) on p. 421).
* Uncorrelated sequences (`Uncorrelated`, p. 421), and (4): the centred variables are orthogonal
  (`integral_centered_mul`). Hence the variance of a sum is the sum of the variances
  (`integral_sq_sum`, (6)).
* **Theorem 14.4** (`theorem_14_4`, the weak law): the average of `fₖ − E fₖ` tends to `0` in
  probability.
* **Theorem 14.5** (`theorem_14_5`, the strong law): it tends to `0` almost everywhere.

**Book pp. 422–423 are missing from the scan used** (the end of the proof of Theorem 14.4, the
statement and proof of Theorem 14.5, and display (6)). Theorem 14.5 is formalised in the form in
which the book later uses it, under the hypotheses of Theorem 14.4. Its proof here is the
"method of subsequences" that the book's index names, along the squares `m²`:
* Chebyshev and Borel–Cantelli give `S_{m²}/m² → 0`;
* the gaps are controlled by `Q_m = Σ_{m² ≤ n < (m+1)²} (S_n − S_{m²})²`, whose mean is at most
  `6m²M`, so that `Q_m/m⁴ → 0`.

Sums run over `k = 0, …, n − 1` (the book's `k = 1, …, n`).
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Chebyshev's inequality** ((3), p. 421): `μ(|h| ≥ ε) ≤ E(h²)/ε²`. -/
theorem chebyshev [IsFiniteMeasure μ] {h : Ω → ℝ} (hh : MemLp h 2 μ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ |h ω|} ≤ (∫ ω, h ω ^ 2 ∂μ) / ε ^ 2 := by
  have h2 : Integrable (fun ω => h ω ^ 2) μ := hh.integrable_sq
  have := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg (h ω)) h2
    (ε ^ 2)
  have hset : {ω | ε ^ 2 ≤ h ω ^ 2} = {ω | ε ≤ |h ω|} := by
    ext ω
    simp only [mem_ofPred_eq, sq_le_sq, abs_of_pos hε]
  rw [hset] at this
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- A sequence is **uncorrelated** (p. 421): square integrable, with `E(fⱼfₖ) = E(fⱼ)E(fₖ)` for
`j ≠ k`. -/
def Uncorrelated (μ : Measure Ω) (f : ℕ → Ω → ℝ) : Prop :=
  (∀ k, MemLp (f k) 2 μ) ∧
    ∀ j k, j ≠ k → ∫ ω, f j ω * f k ω ∂μ = (∫ ω, f j ω ∂μ) * ∫ ω, f k ω ∂μ

/-- The centred variables `fₖ − E fₖ`. -/
noncomputable def centered (μ : Measure Ω) (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  f k ω - ∫ ω', f k ω' ∂μ

theorem memLp_centered [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ) (k : ℕ) :
    MemLp (centered μ f k) 2 μ :=
  (hf k).sub (memLp_const _)

theorem integral_centered [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ)
    (k : ℕ) : ∫ ω, centered μ f k ω ∂μ = 0 := by
  simp only [centered]
  rw [integral_sub ((hf k).integrable one_le_two) (integrable_const _), integral_const,
    probReal_univ, one_smul, sub_self]

/-- (4), p. 421: the centred variables are orthogonal. -/
theorem integral_centered_mul [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f)
    {j k : ℕ} (hjk : j ≠ k) : ∫ ω, centered μ f j ω * centered μ f k ω ∂μ = 0 := by
  set a := ∫ ω, f j ω ∂μ
  set b := ∫ ω, f k ω ∂μ
  have hj := (hf.1 j).integrable one_le_two
  have hk := (hf.1 k).integrable one_le_two
  have hjk' : Integrable (fun ω => f j ω * f k ω) μ := (hf.1 j).integrable_mul (hf.1 k)
  have hexp : (fun ω => centered μ f j ω * centered μ f k ω) =
      fun ω => f j ω * f k ω - b * f j ω - a * f k ω + a * b := by
    funext ω; simp only [centered, a, b]; ring
  have h1 : Integrable (fun ω => f j ω * f k ω - b * f j ω) μ := hjk'.sub (hj.const_mul b)
  have h2 : Integrable (fun ω => f j ω * f k ω - b * f j ω - a * f k ω) μ :=
    h1.sub (hk.const_mul a)
  rw [hexp, integral_add h2 (integrable_const _), integral_sub h1 (hk.const_mul a),
    integral_sub hjk' (hj.const_mul b), integral_const_mul, integral_const_mul, integral_const,
    probReal_univ, one_smul, hf.2 j k hjk]
  ring

/-- (6): for orthogonal square-integrable variables, the second moment of a sum is the sum of the
second moments. -/
theorem integral_sq_sum {g : ℕ → Ω → ℝ} (hg : ∀ k, MemLp (g k) 2 μ)
    (horth : ∀ j k, j ≠ k → ∫ ω, g j ω * g k ω ∂μ = 0) (s : Finset ℕ) :
    ∫ ω, (∑ k ∈ s, g k ω) ^ 2 ∂μ = ∑ k ∈ s, ∫ ω, g k ω ^ 2 ∂μ := by
  have hexp : ∀ ω, (∑ k ∈ s, g k ω) ^ 2 = ∑ j ∈ s, ∑ k ∈ s, g j ω * g k ω := fun ω => by
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  have hint : ∀ j k, Integrable (fun ω => g j ω * g k ω) μ := fun j k =>
    (hg j).integrable_mul (hg k)
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun k _ => hint j k,
    Finset.sum_eq_single j (fun k _ hkj => horth j k (Ne.symm hkj)) (fun h => absurd hj h)]
  simp only [sq]

/-- The variance bound used for Theorems 14.4–14.5: `E[(Σ_{k∈s} (fₖ − E fₖ))²] ≤ |s| M`. -/
theorem integral_sq_sum_le [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f)
    {M : ℝ} (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) (s : Finset ℕ) :
    ∫ ω, (∑ k ∈ s, centered μ f k ω) ^ 2 ∂μ ≤ s.card * M := by
  rw [integral_sq_sum (memLp_centered hf.1) (fun j k hjk => integral_centered_mul hf hjk)]
  calc ∑ k ∈ s, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ ∑ _k ∈ s, M := Finset.sum_le_sum fun k _ => hM k
    _ = s.card * M := by rw [Finset.sum_const, nsmul_eq_mul]

theorem memLp_sum_centered [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ)
    (s : Finset ℕ) : MemLp (fun ω => ∑ k ∈ s, centered μ f k ω) 2 μ := by
  have := memLp_finsetSum' s fun k _ => memLp_centered (μ := μ) hf k
  convert this using 1
  funext ω; simp

/-- The averages `(1/n) Σ_{k<n} (fₖ − E fₖ)`. -/
noncomputable def avgDev (μ : Measure Ω) (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, centered μ f k ω

/-- **Theorem 14.4** (the weak law). For an uncorrelated sequence with bounded variances,
`(1/n) Σ_{k<n} (fₖ − E fₖ) → 0` in probability. -/
theorem theorem_14_4 [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f) {M : ℝ}
    (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) :
    ConvInProb μ (avgDev μ f) fun _ => 0 := by
  intro ε hε
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (hM 0)
  have hbound : ∀ n : ℕ, 1 ≤ n →
      μ {ω | ε < |avgDev μ f n ω - 0|} ≤ ENNReal.ofReal (M / ε ^ 2 * (1 / n)) := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hmem : MemLp (avgDev μ f n) 2 μ := (memLp_sum_centered hf.1 _).const_mul _
    have hsq : ∫ ω, avgDev μ f n ω ^ 2 ∂μ ≤ M / n := by
      simp only [avgDev, mul_pow]
      rw [integral_const_mul]
      have := integral_sq_sum_le hf hM (Finset.range n)
      rw [Finset.card_range] at this
      calc ((n : ℝ)⁻¹) ^ 2 * ∫ ω, (∑ k ∈ Finset.range n, centered μ f k ω) ^ 2 ∂μ ≤
            ((n : ℝ)⁻¹) ^ 2 * (n * M) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = M / n := by field_simp
    have hc := chebyshev hmem hε
    rw [← ofReal_measureReal (μ := μ)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc μ.real {ω | ε < |avgDev μ f n ω - 0|} ≤ μ.real {ω | ε ≤ |avgDev μ f n ω|} :=
          measureReal_mono fun ω (hω : ε < |avgDev μ f n ω - 0|) => by
            simp only [sub_zero] at hω; exact hω.le
      _ ≤ (∫ ω, avgDev μ f n ω ^ 2 ∂μ) / ε ^ 2 := hc
      _ ≤ M / n / ε ^ 2 := by gcongr
      _ = M / ε ^ 2 * (1 / n) := by ring
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (M / ε ^ 2 * (1 / n))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero, ← mul_zero (M / ε ^ 2)]
    exact ENNReal.tendsto_ofReal (tendsto_one_div_atTop_nhds_zero_nat.const_mul _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => zero_le) (eventually_atTop.2 ⟨1, hbound⟩)

/-! ### Theorem 14.5 -/

/-- The partial sums `S_n = Σ_{k<n} (fₖ − E fₖ)`. -/
noncomputable def partialDev (μ : Measure Ω) (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, centered μ f k ω

theorem partialDev_sub {f : ℕ → Ω → ℝ} {a n : ℕ} (h : a ≤ n) (ω : Ω) :
    partialDev μ f n ω - partialDev μ f a ω = ∑ k ∈ Finset.Ico a n, centered μ f k ω :=
  (Finset.sum_Ico_eq_sub _ h).symm

theorem memLp_partialDev_sub [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ)
    {a n : ℕ} (h : a ≤ n) :
    MemLp (fun ω => partialDev μ f n ω - partialDev μ f a ω) 2 μ := by
  simp_rw [partialDev_sub h]
  exact memLp_sum_centered hf _

theorem integral_sq_partialDev_sub_le [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ}
    (hf : Uncorrelated μ f) {M : ℝ} (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) {a n : ℕ}
    (h : a ≤ n) :
    ∫ ω, (partialDev μ f n ω - partialDev μ f a ω) ^ 2 ∂μ ≤ ((n : ℝ) - a) * M := by
  simp_rw [partialDev_sub h]
  have := integral_sq_sum_le hf hM (Finset.Ico a n)
  rwa [Nat.card_Ico, Nat.cast_sub h] at this

theorem tsum_ofReal_div_sq_ne_top (c : ℝ) (hc : 0 ≤ c) :
    ∑' m : ℕ, ENNReal.ofReal (c * (1 / (m : ℝ) ^ 2)) ≠ ∞ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity)
    ((Real.summable_one_div_nat_pow.2 one_lt_two).mul_left c)]
  exact ENNReal.ofReal_ne_top

/-- Step 1: `S_{m²}/m² → 0` a.e. -/
theorem squares_convAE [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f) {M : ℝ}
    (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) :
    ConvAE μ (fun m ω => partialDev μ f (m ^ 2) ω / (m : ℝ) ^ 2) fun _ => 0 := by
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (hM 0)
  refine lemma_14_3 μ fun ε hε => ne_top_of_le_ne_top
    (tsum_ofReal_div_sq_ne_top (M / ε ^ 2) (by positivity)) (ENNReal.tsum_le_tsum fun m => ?_)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : {ω | ε < |partialDev μ f (0 ^ 2) ω / ((0 : ℕ) : ℝ) ^ 2 - 0|} = ∅ := by
      ext ω; simp only [mem_ofPred_eq, Nat.cast_zero, zero_pow two_ne_zero, div_zero, sub_zero,
        abs_zero, mem_empty_iff_false, iff_false, not_lt]; exact hε.le
    rw [this, measure_empty]; exact zero_le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmem : MemLp (partialDev μ f (m ^ 2)) 2 μ := memLp_sum_centered hf.1 _
  have hc := chebyshev hmem (show 0 < ε * (m : ℝ) ^ 2 by positivity)
  have hsq : ∫ ω, partialDev μ f (m ^ 2) ω ^ 2 ∂μ ≤ (m : ℝ) ^ 2 * M := by
    have := integral_sq_sum_le hf hM (Finset.range (m ^ 2))
    rw [Finset.card_range] at this
    push_cast at this
    exact this
  rw [← ofReal_measureReal (μ := μ)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc μ.real {ω | ε < |partialDev μ f (m ^ 2) ω / (m : ℝ) ^ 2 - 0|} ≤
        μ.real {ω | ε * (m : ℝ) ^ 2 ≤ |partialDev μ f (m ^ 2) ω|} :=
        measureReal_mono fun ω (hω : ε < |partialDev μ f (m ^ 2) ω / (m : ℝ) ^ 2 - 0|) => by
          rw [sub_zero, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) ^ 2),
            lt_div_iff₀ (by positivity)] at hω
          exact hω.le
    _ ≤ (∫ ω, partialDev μ f (m ^ 2) ω ^ 2 ∂μ) / (ε * (m : ℝ) ^ 2) ^ 2 := hc
    _ ≤ (m : ℝ) ^ 2 * M / (ε * (m : ℝ) ^ 2) ^ 2 := by gcongr
    _ = M / ε ^ 2 * (1 / (m : ℝ) ^ 2) := by field_simp

/-- The gap statistic `Q_m = Σ_{m² ≤ n < (m+1)²} (S_n − S_{m²})²`. -/
noncomputable def gapSq (μ : Measure Ω) (f : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ n ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), (partialDev μ f n ω - partialDev μ f (m ^ 2) ω) ^ 2

theorem gapSq_nonneg {f : ℕ → Ω → ℝ} (m : ℕ) (ω : Ω) : 0 ≤ gapSq μ f m ω :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem integrable_gapSq [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ)
    (m : ℕ) : Integrable (gapSq μ f m) μ := by
  unfold gapSq
  refine integrable_finsetSum _ fun n hn => ?_
  exact (memLp_partialDev_sub hf (Finset.mem_Ico.1 hn).1).integrable_sq

theorem integral_gapSq_le [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f)
    {M : ℝ} (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) (m : ℕ) :
    ∫ ω, gapSq μ f m ω ∂μ ≤ 6 * M * (m : ℝ) ^ 2 := by
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (hM 0)
  unfold gapSq
  rw [integral_finsetSum _ fun n hn =>
    (memLp_partialDev_sub hf.1 (Finset.mem_Ico.1 hn).1).integrable_sq]
  calc ∑ n ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2),
        ∫ ω, (partialDev μ f n ω - partialDev μ f (m ^ 2) ω) ^ 2 ∂μ ≤
        ∑ _n ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), 2 * (m : ℝ) * M := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hn
        refine (integral_sq_partialDev_sub_le hf hM h1).trans ?_
        have : (n : ℝ) - (m ^ 2 : ℕ) ≤ 2 * m := by
          have : n ≤ m ^ 2 + 2 * m := by nlinarith
          have : (n : ℝ) ≤ (m ^ 2 + 2 * m : ℕ) := by exact_mod_cast this
          push_cast at this ⊢; linarith
        exact mul_le_mul_of_nonneg_right this hM0
    _ = (2 * (m : ℝ) + 1) * (2 * m * M) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        congr 1
        rw [Nat.cast_sub (Nat.pow_le_pow_left (Nat.le_succ m) 2)]
        push_cast; ring
    _ ≤ 6 * M * (m : ℝ) ^ 2 := by
        have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos m with rfl | hm
          · simp
          · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
            nlinarith
        nlinarith

/-- Step 2: `Q_m/m⁴ → 0` a.e. -/
theorem gaps_convAE [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f) {M : ℝ}
    (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) :
    ConvAE μ (fun m ω => gapSq μ f m ω / (m : ℝ) ^ 4) fun _ => 0 := by
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (hM 0)
  refine lemma_14_3 μ fun ε hε => ne_top_of_le_ne_top
    (tsum_ofReal_div_sq_ne_top (6 * M / ε) (by positivity)) (ENNReal.tsum_le_tsum fun m => ?_)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : {ω | ε < |gapSq μ f 0 ω / ((0 : ℕ) : ℝ) ^ 4 - 0|} = ∅ := by
      ext ω; simp only [mem_ofPred_eq, Nat.cast_zero, zero_pow (by norm_num : 4 ≠ 0), div_zero,
        sub_zero, abs_zero, mem_empty_iff_false, iff_false, not_lt]; exact hε.le
    rw [this, measure_empty]; exact zero_le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall (gapSq_nonneg (μ := μ)
    (f := f) m)) (integrable_gapSq hf.1 m) (ε * (m : ℝ) ^ 4)
  have hint := integral_gapSq_le hf hM m
  rw [← ofReal_measureReal (μ := μ)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : 0 < ε * (m : ℝ) ^ 4 := by positivity
  calc μ.real {ω | ε < |gapSq μ f m ω / (m : ℝ) ^ 4 - 0|} ≤
        μ.real {ω | ε * (m : ℝ) ^ 4 ≤ gapSq μ f m ω} :=
        measureReal_mono fun ω (hω : ε < |gapSq μ f m ω / (m : ℝ) ^ 4 - 0|) => by
          rw [sub_zero, abs_of_nonneg (div_nonneg (gapSq_nonneg m ω) (by positivity)),
            lt_div_iff₀ (by positivity)] at hω
          exact hω.le
    _ ≤ (∫ ω, gapSq μ f m ω ∂μ) / (ε * (m : ℝ) ^ 4) := by
        rw [le_div_iff₀ hpos]; linarith
    _ ≤ 6 * M * (m : ℝ) ^ 2 / (ε * (m : ℝ) ^ 4) := by gcongr
    _ = 6 * M / ε * (1 / (m : ℝ) ^ 2) := by field_simp

theorem tendsto_sqrt_atTop : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b * b, fun _ hn => Nat.le_sqrt.2 hn⟩

/-- **Theorem 14.5** (the strong law, reconstructed; see the module docstring). For an uncorrelated
sequence with bounded variances, `(1/n) Σ_{k<n} (fₖ − E fₖ) → 0` almost everywhere. -/
theorem theorem_14_5 [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f) {M : ℝ}
    (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) : ConvAE μ (avgDev μ f) fun _ => 0 := by
  filter_upwards [squares_convAE hf hM, gaps_convAE hf hM] with ω hA hB
  set c : ℕ → ℝ := fun m => |partialDev μ f (m ^ 2) ω / (m : ℝ) ^ 2| +
    Real.sqrt (gapSq μ f m ω / (m : ℝ) ^ 4)
  have hc : Tendsto c atTop (𝓝 0) := by
    have h1 := hA.abs
    have h2 := (Real.continuous_sqrt.tendsto 0).comp hB
    simp only [abs_zero, Real.sqrt_zero, Function.comp_def] at h1 h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  refine squeeze_zero_norm' ?_ (hc.comp tendsto_sqrt_atTop)
  filter_upwards [eventually_ge_atTop 1] with n hn
  set m := Nat.sqrt n
  have hm1 : 1 ≤ m := Nat.le_sqrt.2 (by simpa using hn)
  have hmn : m ^ 2 ≤ n := Nat.sqrt_le' n
  have hnm : n < (m + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
  have hn' : ((m : ℝ)) ^ 2 ≤ n := by exact_mod_cast hmn
  -- `|S_n − S_{m²}| ≤ √Q_m`
  have hgap : |partialDev μ f n ω - partialDev μ f (m ^ 2) ω| ≤ Real.sqrt (gapSq μ f m ω) :=
    Real.abs_le_sqrt (Finset.single_le_sum (f := fun n =>
      (partialDev μ f n ω - partialDev μ f (m ^ 2) ω) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_Ico.2 ⟨hmn, hnm⟩))
  have hsqrt : Real.sqrt (gapSq μ f m ω / (m : ℝ) ^ 4) =
      Real.sqrt (gapSq μ f m ω) / (m : ℝ) ^ 2 := by
    rw [Real.sqrt_div' _ (by positivity), show (m : ℝ) ^ 4 = ((m : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [Function.comp_apply, Real.norm_eq_abs, avgDev, abs_mul, abs_inv, Nat.abs_cast]
  change (n : ℝ)⁻¹ * |partialDev μ f n ω| ≤ c m
  simp only [c, hsqrt, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)]
  have htri : |partialDev μ f n ω| ≤ |partialDev μ f (m ^ 2) ω| + Real.sqrt (gapSq μ f m ω) := by
    have := abs_sub_abs_le_abs_sub (partialDev μ f n ω) (partialDev μ f (m ^ 2) ω)
    linarith
  calc (n : ℝ)⁻¹ * |partialDev μ f n ω| ≤ ((m : ℝ) ^ 2)⁻¹ * |partialDev μ f n ω| :=
        mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) hn') (abs_nonneg _)
    _ ≤ ((m : ℝ) ^ 2)⁻¹ * (|partialDev μ f (m ^ 2) ω| + Real.sqrt (gapSq μ f m ω)) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ = _ := by field_simp

end StokeyLucasPrescott.LawsOfLargeNumbers

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A strong law for martingale differences: Theorem 14.6

SLP §14.1, p. 424. Let `𝒜₀ ⊆ 𝒜₁ ⊆ ⋯ ⊆ 𝓕` be σ-algebras with `fₖ` `𝒜ₖ`-measurable, and
`φₖ = E(fₖ | 𝒜ₖ₋₁)`. If `E[(fₖ − φₖ)²] ≤ M` for `k ≥ 1`, then `(1/n) Σ_{k=1}^n (fₖ − φₖ) → 0` a.e.

The proof is the book's. The differences `gₖ = fₖ − φₖ` have conditional mean zero,
`E(gₖ | 𝒜ₖ₋₁) = 0` (`condExp_diff_ae_eq_zero`). For `j < k` the factor `gⱼ` is
`𝒜ₖ₋₁`-measurable, so it can be taken out of `E(gⱼ gₖ | 𝒜ₖ₋₁)`. Hence `E(gⱼ gₖ) = 0` and the
`gₖ` are uncorrelated (`uncorrelated_diff`). Theorem 14.5 then applies.

**Correction.** `E(fₖ | 𝒜ₖ₋₁)` needs `fₖ` integrable, which the book does not assume. Also
`E[(fₖ − φₖ)²] < M` must be read with `fₖ − φₖ ∈ L²`; for a Bochner integral, the bound would
otherwise hold vacuously for a non-integrable square. We assume `fₖ ∈ L²` (then
`φₖ ∈ L²`). Condition (c) involves `𝒜ₖ₋₁`, so it is required for `k ≥ 1` only.

Indices are shifted to avoid `k − 1`: the `k`-th difference is
`f (k + 1) − E(f (k + 1) | 𝒜 k)`, `k = 0, …, n − 1`.
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The martingale differences `gₖ = f_{k+1} − E(f_{k+1} | 𝒜ₖ)`. -/
noncomputable def mgDiff (μ : Measure Ω) (𝒜 : ℕ → MeasurableSpace Ω) (f : ℕ → Ω → ℝ) (k : ℕ) :
    Ω → ℝ :=
  f (k + 1) - μ[f (k + 1) | 𝒜 k]

theorem memLp_mgDiff [IsFiniteMeasure μ] {𝒜 : ℕ → MeasurableSpace Ω} {f : ℕ → Ω → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (k : ℕ) : MemLp (mgDiff μ 𝒜 f k) 2 μ :=
  (hf (k + 1)).sub ((hf (k + 1)).condExp one_le_two)

/-- `E(gₖ | 𝒜ₖ) = 0` a.e. -/
theorem condExp_diff_ae_eq_zero [IsFiniteMeasure μ] {𝒜 : ℕ → MeasurableSpace Ω}
    (h𝒜le : ∀ k, 𝒜 k ≤ mΩ) {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ) (k : ℕ) :
    μ[mgDiff μ 𝒜 f k | 𝒜 k] =ᵐ[μ] 0 := by
  have hi : Integrable (f (k + 1)) μ := (hf (k + 1)).integrable one_le_two
  filter_upwards [condExp_sub hi integrable_condExp (𝒜 k)] with ω hω
  rw [mgDiff, hω, Pi.sub_apply,
    condExp_of_stronglyMeasurable (h𝒜le k) stronglyMeasurable_condExp integrable_condExp]
  simp

/-- `gⱼ` is `𝒜ₖ`-measurable for `j < k`. -/
theorem stronglyMeasurable_mgDiff {𝒜 : ℕ → MeasurableSpace Ω} (h𝒜 : Monotone 𝒜)
    {f : ℕ → Ω → ℝ} (hfm : ∀ k, StronglyMeasurable[𝒜 k] (f k)) {j k : ℕ} (hjk : j < k) :
    StronglyMeasurable[𝒜 k] (mgDiff μ 𝒜 f j) :=
  ((hfm (j + 1)).mono (h𝒜 hjk)).sub (stronglyMeasurable_condExp.mono (h𝒜 hjk.le))

/-- `E(gⱼ gₖ) = 0` for `j < k`. -/
theorem integral_mgDiff_mul [IsProbabilityMeasure μ] {𝒜 : ℕ → MeasurableSpace Ω}
    (h𝒜 : Monotone 𝒜) (h𝒜le : ∀ k, 𝒜 k ≤ mΩ) {f : ℕ → Ω → ℝ}
    (hfm : ∀ k, StronglyMeasurable[𝒜 k] (f k)) (hf : ∀ k, MemLp (f k) 2 μ) {j k : ℕ}
    (hjk : j < k) : ∫ ω, mgDiff μ 𝒜 f j ω * mgDiff μ 𝒜 f k ω ∂μ = 0 := by
  have hprod : Integrable (mgDiff μ 𝒜 f j * mgDiff μ 𝒜 f k) μ :=
    (memLp_mgDiff hf j).integrable_mul (memLp_mgDiff hf k)
  have hk : Integrable (mgDiff μ 𝒜 f k) μ := (memLp_mgDiff hf k).integrable one_le_two
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := 𝒜 k)
    (stronglyMeasurable_mgDiff h𝒜 hfm hjk) hprod hk
  have h0 := condExp_diff_ae_eq_zero h𝒜le hf k
  have : ∫ ω, (μ[mgDiff μ 𝒜 f j * mgDiff μ 𝒜 f k | 𝒜 k]) ω ∂μ = 0 := by
    rw [integral_eq_zero_of_ae]
    filter_upwards [hpull, h0] with ω h1 h2
    rw [h1, Pi.mul_apply, h2, Pi.zero_apply, mul_zero]
  rw [integral_condExp (h𝒜le k)] at this
  exact this

/-- `E(gₖ) = 0`. -/
theorem integral_mgDiff [IsProbabilityMeasure μ] {𝒜 : ℕ → MeasurableSpace Ω}
    (h𝒜le : ∀ k, 𝒜 k ≤ mΩ) {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ) (k : ℕ) :
    ∫ ω, mgDiff μ 𝒜 f k ω ∂μ = 0 := by
  rw [← integral_condExp (h𝒜le k), integral_eq_zero_of_ae (condExp_diff_ae_eq_zero h𝒜le hf k)]

/-- The martingale differences are uncorrelated. -/
theorem uncorrelated_diff [IsProbabilityMeasure μ] {𝒜 : ℕ → MeasurableSpace Ω}
    (h𝒜 : Monotone 𝒜) (h𝒜le : ∀ k, 𝒜 k ≤ mΩ) {f : ℕ → Ω → ℝ}
    (hfm : ∀ k, StronglyMeasurable[𝒜 k] (f k)) (hf : ∀ k, MemLp (f k) 2 μ) :
    Uncorrelated μ (mgDiff μ 𝒜 f) := by
  refine ⟨memLp_mgDiff hf, fun j k hjk => ?_⟩
  rw [integral_mgDiff h𝒜le hf j, zero_mul]
  rcases lt_or_gt_of_ne hjk with h | h
  · exact integral_mgDiff_mul h𝒜 h𝒜le hfm hf h
  · simp_rw [mul_comm (mgDiff μ 𝒜 f j _)]
    exact integral_mgDiff_mul h𝒜 h𝒜le hfm hf h

/-- **Theorem 14.6.** Let `𝒜ₖ` be increasing sub-σ-algebras, `fₖ` `𝒜ₖ`-measurable and in `L²`,
and `E[(f_{k+1} − E(f_{k+1} | 𝒜ₖ))²] ≤ M` for all `k`. Then
`(1/n) Σ_{k=0}^{n−1} [f_{k+1} − E(f_{k+1} | 𝒜ₖ)] → 0` a.e. (the book's `Σ_{k=1}^n`). -/
theorem theorem_14_6 [IsProbabilityMeasure μ] (𝒜 : ℕ → MeasurableSpace Ω) (h𝒜 : Monotone 𝒜)
    (h𝒜le : ∀ k, 𝒜 k ≤ mΩ) {f : ℕ → Ω → ℝ} (hfm : ∀ k, StronglyMeasurable[𝒜 k] (f k))
    (hf : ∀ k, MemLp (f k) 2 μ) {M : ℝ}
    (hM : ∀ k, ∫ ω, (f (k + 1) ω - μ[f (k + 1) | 𝒜 k] ω) ^ 2 ∂μ ≤ M) :
    ConvAE μ (fun n ω => (n : ℝ)⁻¹ *
      ∑ k ∈ Finset.range n, (f (k + 1) ω - μ[f (k + 1) | 𝒜 k] ω)) fun _ => 0 := by
  have hc : ∀ k ω, centered μ (mgDiff μ 𝒜 f) k ω = f (k + 1) ω - μ[f (k + 1) | 𝒜 k] ω :=
    fun k ω => by rw [centered, integral_mgDiff h𝒜le hf k, sub_zero]; rfl
  have := theorem_14_5 (uncorrelated_diff h𝒜 h𝒜le hfm hf) (M := M) fun k => by
    simp_rw [hc]; exact hM k
  filter_upwards [this] with ω h
  simpa only [avgDev, hc] using h

end StokeyLucasPrescott.LawsOfLargeNumbers

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Minimum norm duality and the Norms Ergodic Lemma

SLP §14.2, pp. 430–435. `X` is a real normed space and `X*` (`StrongDual ℝ X`) its dual.

* **Theorem 14.10** (`theorem_14_10`, minimum norm duality, p. 432): for a subspace `M`,
  `inf_{y ∈ M} ‖x − y‖ = max {⟨x, μ⟩ : ‖μ‖ ≤ 1, μ = 0 on M}`, and the maximum is attained. The
  book cites Luenberger. Here the maximiser is a norm-one functional on the quotient `X/M`, from
  Hahn–Banach, composed with the quotient map; `‖x + M‖ = inf_{y ∈ M} ‖x − y‖`.
* **Lemma 14.11** (`lemma_14_11`, p. 432): a weak limit of a sequence in a subspace lies in its
  norm closure (`mem_closure_of_weak`); in the book the subspace is the image `TX`.
* **Exercise 14.3** (`ex_14_3a`, `ex_14_3b`, pp. 432–433): `Tᵏ` and
  `Hₙ = (1/n) Σ_{k=1}^n T^{k−1}` (`cesaroOp`) are linear, with norms `≤ 1` when `‖T‖ ≤ 1`.
* **Lemma 14.12** (`lemma_14_12`, p. 433): `‖Hₙx‖ → 0` for `x` in the closure of `(T − I)X`.
* **Lemma 14.13** (`lemma_14_13`, the Norms Ergodic Lemma, p. 434): if `Tx̄ = x̄` and `Hₙx → x̄`
  weakly then `Hₙx → x̄` in norm.

**Corrections.**
* The book's space `L` of linear operators (p. 431) includes unbounded operators, for which
  `‖T‖_L = ∞`. Operators here are continuous (`X →L[ℝ] X`); every operator used later has
  `‖T‖ ≤ 1`.
* Lemmas 14.12 and 14.13 assume `‖T‖ = 1`; only `‖T‖ ≤ 1` is used.
* In the proof of Lemma 14.13 the weak limit of `(Hₙ − I)x` is `x̄ − x`; the book writes
  `x − x̄` (harmless: the closed subspace is symmetric).
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open Filter Topology Metric

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Theorem 14.10 -/

/-- The quotient norm is the distance to the subspace. -/
theorem norm_quotient_mk (M : Submodule ℝ X) (x : X) :
    ‖(Submodule.Quotient.mk x : X ⧸ M)‖ = infDist x (M : Set X) :=
  QuotientAddGroup.norm_mk (S := M.toAddSubgroup) x

/-- **Theorem 14.10** (minimum norm duality). For a subspace `M` and `x ∈ X`, every `μ ∈ X*` with
`‖μ‖ ≤ 1` vanishing on `M` has `⟨x, μ⟩ ≤ inf_{y ∈ M} ‖x − y‖`, and some such `μ*` attains it. -/
theorem theorem_14_10 (M : Submodule ℝ X) (x : X) :
    IsGreatest {r | ∃ μ : StrongDual ℝ X, ‖μ‖ ≤ 1 ∧ (∀ y ∈ M, μ y = 0) ∧ r = μ x}
      (infDist x (M : Set X)) := by
  constructor
  · obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' ℝ (Submodule.Quotient.mk x : X ⧸ M)
    have hb : ∀ y : X, ‖(g.toLinearMap.comp M.mkQ) y‖ ≤ 1 * ‖y‖ := fun y => by
      change ‖g (Submodule.Quotient.mk y)‖ ≤ 1 * ‖y‖
      calc ‖g (Submodule.Quotient.mk y)‖ ≤ ‖g‖ * ‖(Submodule.Quotient.mk y : X ⧸ M)‖ :=
            g.le_opNorm _
        _ ≤ 1 * ‖y‖ := mul_le_mul hg1 (Submodule.Quotient.norm_mk_le M y) (norm_nonneg _)
            zero_le_one
    refine ⟨(g.toLinearMap.comp M.mkQ).mkContinuous 1 hb,
      LinearMap.mkContinuous_norm_le _ zero_le_one hb, fun y hy => ?_, ?_⟩
    · change g (Submodule.Quotient.mk y) = 0
      rw [(Submodule.Quotient.mk_eq_zero M).2 hy, map_zero]
    · change _ = g (Submodule.Quotient.mk x)
      rw [hgx, norm_quotient_mk]
      rfl
  · rintro r ⟨μ, hμ1, hμM, rfl⟩
    rw [infDist_eq_iInf]
    have : Nonempty (M : Set X) := ⟨⟨0, M.zero_mem⟩⟩
    refine le_ciInf fun y => ?_
    have h0 : μ x = μ (x - y) := by rw [map_sub, hμM y y.2, sub_zero]
    rw [h0, dist_eq_norm]
    exact (le_abs_self _).trans ((μ.le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hμ1))

/-! ### Lemma 14.11 -/

/-- A weak limit of a sequence in a subspace `M` lies in the norm closure of `M`. -/
theorem mem_closure_of_weak (M : Submodule ℝ X) {x : X} {xs : ℕ → X} (hxs : ∀ n, xs n ∈ M)
    (hw : ∀ μ : StrongDual ℝ X, Tendsto (fun n => μ (xs n)) atTop (𝓝 (μ x))) :
    x ∈ closure (M : Set X) := by
  obtain ⟨⟨μ, -, hμM, hμx⟩, -⟩ := theorem_14_10 M x
  have hlim := hw μ
  simp only [hμM _ (hxs _)] at hlim
  rw [mem_closure_iff_infDist_zero ⟨0, M.zero_mem⟩, hμx]
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **Lemma 14.11.** If `T` is linear, `xₙ ∈ TX` and `⟨xₙ, μ⟩ → ⟨x, μ⟩` for all `μ ∈ X*`, then
`x` lies in the closure of `TX`. -/
theorem lemma_14_11 (T : X →ₗ[ℝ] X) {x : X} {xs : ℕ → X} (hxs : ∀ n, xs n ∈ LinearMap.range T)
    (hw : ∀ μ : StrongDual ℝ X, Tendsto (fun n => μ (xs n)) atTop (𝓝 (μ x))) :
    x ∈ closure (LinearMap.range T : Set X) :=
  mem_closure_of_weak _ hxs hw

/-! ### Exercise 14.3 -/

/-- **Exercise 14.3a.** `T⁰ = I`, `Tᵏx = T(T^{k−1}x)`, each `Tᵏ` is linear, and `‖Tᵏ‖ ≤ 1` when
`‖T‖ ≤ 1`. -/
theorem ex_14_3a (T : X →L[ℝ] X) :
    T ^ 0 = ContinuousLinearMap.id ℝ X ∧ (∀ k x, (T ^ (k + 1)) x = T ((T ^ k) x)) ∧
      (∀ k (a b : ℝ) (x y : X), (T ^ k) (a • x + b • y) = a • (T ^ k) x + b • (T ^ k) y) ∧
      (‖T‖ ≤ 1 → ∀ k, ‖T ^ k‖ ≤ 1) := by
  refine ⟨pow_zero T, fun k x => by rw [pow_succ']; rfl,
    fun k a b x y => by rw [map_add, map_smul, map_smul], fun hT k => ?_⟩
  induction k with
  | zero =>
    rw [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ']
    calc ‖T * T ^ k‖ ≤ ‖T‖ * ‖T ^ k‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hT ih (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- The Cesàro operator `Hₙ = (1/n) Σ_{k=1}^n T^{k−1}` ((8), p. 433). -/
noncomputable def cesaroOp (T : X →L[ℝ] X) (n : ℕ) : X →L[ℝ] X :=
  (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, T ^ k

theorem cesaroOp_apply (T : X →L[ℝ] X) (n : ℕ) (x : X) :
    cesaroOp T n x = (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, (T ^ k) x := by
  simp [cesaroOp]

/-- **Exercise 14.3b.** Each `Hₙ` is linear, and `‖Hₙ‖ ≤ 1` when `‖T‖ ≤ 1`. -/
theorem ex_14_3b (T : X →L[ℝ] X) :
    (∀ n (a b : ℝ) (x y : X),
      cesaroOp T n (a • x + b • y) = a • cesaroOp T n x + b • cesaroOp T n y) ∧
      (‖T‖ ≤ 1 → ∀ n, ‖cesaroOp T n‖ ≤ 1) := by
  refine ⟨fun n a b x y => by rw [map_add, map_smul, map_smul], fun hT n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cesaroOp]
  · have hsum : ‖∑ k ∈ Finset.range n, T ^ k‖ ≤ n := by
      refine (norm_sum_le _ _).trans ?_
      have := Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => (ex_14_3a T).2.2.2 hT k
      simpa using this
    rw [cesaroOp, norm_smul, norm_inv, Real.norm_natCast]
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [inv_mul_le_iff₀ hn', mul_one]
    exact hsum

/-! ### Lemmas 14.12 and 14.13 -/

/-- `Hₙ(T − I)y = (Tⁿy − y)/n`. -/
theorem cesaroOp_sub_one (T : X →L[ℝ] X) (n : ℕ) (y : X) :
    cesaroOp T n ((T - 1) y) = (n : ℝ)⁻¹ • ((T ^ n) y - y) := by
  rw [cesaroOp_apply]
  congr 1
  have : ∀ k, (T ^ k) ((T - 1) y) = (T ^ (k + 1)) y - (T ^ k) y := fun k => by
    rw [pow_succ]
    change (T ^ k) (T y - y) = (T ^ k) (T y) - (T ^ k) y
    rw [map_sub]
  simp_rw [this]
  rw [Finset.sum_range_sub (fun k => (T ^ k) y), pow_zero]
  rfl

/-- **Lemma 14.12.** If `‖T‖ ≤ 1`, then `‖Hₙx‖ → 0` for every `x` in the closure of `(T − I)X`. -/
theorem lemma_14_12 (T : X →L[ℝ] X) (hT : ‖T‖ ≤ 1) {x : X}
    (hx : x ∈ closure (LinearMap.range ((T - 1 : X →L[ℝ] X) : X →ₗ[ℝ] X) : Set X)) :
    Tendsto (fun n => ‖cesaroOp T n x‖) atTop (𝓝 0) := by
  -- Step 1: on `(T − I)X`
  have hstep : ∀ y : X, Tendsto (fun n => ‖cesaroOp T n ((T - 1) y)‖) atTop (𝓝 0) := fun y => by
    have hb : ∀ n : ℕ, ‖cesaroOp T n ((T - 1) y)‖ ≤ 2 * ‖y‖ * (n : ℝ)⁻¹ := fun n => by
      rw [cesaroOp_sub_one, norm_smul, norm_inv, Real.norm_natCast]
      have h1 : ‖(T ^ n) y - y‖ ≤ 2 * ‖y‖ := by
        refine (norm_sub_le _ _).trans ?_
        have := ((T ^ n).le_opNorm y).trans
          (mul_le_of_le_one_left (norm_nonneg _) ((ex_14_3a T).2.2.2 hT n))
        linarith
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 (Nat.cast_nonneg n))
    have hlim : Tendsto (fun n : ℕ => 2 * ‖y‖ * (n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul (2 * ‖y‖)
    exact squeeze_zero (fun n => norm_nonneg _) hb hlim
  -- Step 2: approximation
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨x', hx'⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (half_pos hε)
  obtain ⟨⟨y, rfl⟩, hd⟩ := hx'
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hstep y) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1 ⊢
  have h2 : ‖cesaroOp T n (x - (T - 1) y)‖ ≤ ‖x - (T - 1) y‖ :=
    ((cesaroOp T n).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) ((ex_14_3b T).2 hT n))
  have h3 : ‖x - (T - 1) y‖ < ε / 2 := by rwa [← dist_eq_norm]
  have h4 : cesaroOp T n x = cesaroOp T n ((T - 1) y) + cesaroOp T n (x - (T - 1) y) := by
    rw [← map_add, add_sub_cancel]
  rw [h4]
  linarith [norm_add_le (cesaroOp T n ((T - 1) y)) (cesaroOp T n (x - (T - 1) y))]

/-- `Hₙx − x ∈ (T − I)X`. -/
theorem cesaroOp_sub_mem_range (T : X →L[ℝ] X) (n : ℕ) (hn : 1 ≤ n) (x : X) :
    cesaroOp T n x - x ∈ LinearMap.range ((T - 1 : X →L[ℝ] X) : X →ₗ[ℝ] X) := by
  set R := LinearMap.range ((T - 1 : X →L[ℝ] X) : X →ₗ[ℝ] X)
  have hk : ∀ k, (T ^ k) x - x ∈ R := fun k => by
    induction k with
    | zero => simp [R]
    | succ k ih =>
      have : (T ^ (k + 1)) x - x = (T - 1) ((T ^ k) x) + ((T ^ k) x - x) := by
        rw [pow_succ']
        change T ((T ^ k) x) - x = (T ((T ^ k) x) - (T ^ k) x) + ((T ^ k) x - x)
        abel
      rw [this]
      exact R.add_mem ⟨_, rfl⟩ ih
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have : cesaroOp T n x - x = (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, ((T ^ k) x - x) := by
    rw [cesaroOp_apply, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn', one_smul]
  rw [this]
  exact R.smul_mem _ (R.sum_mem fun k _ => hk k)

/-- `Hₙx̄ = x̄` for a fixed point `x̄` of `T` and `n ≥ 1`. -/
theorem cesaroOp_fixed (T : X →L[ℝ] X) {xbar : X} (hfix : T xbar = xbar) {n : ℕ} (hn : 1 ≤ n) :
    cesaroOp T n xbar = xbar := by
  have hk : ∀ k, (T ^ k) xbar = xbar := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ']
      change T ((T ^ k) xbar) = xbar
      rw [ih, hfix]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [cesaroOp_apply]
  simp_rw [hk]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hn', one_smul]

/-- **Lemma 14.13** (Norms Ergodic Lemma). Let `‖T‖ ≤ 1` and `Tx̄ = x̄`. If `⟨Hₙx, μ⟩ → ⟨x̄, μ⟩`
for every `μ ∈ X*`, then `‖Hₙx − x̄‖ → 0`. -/
theorem lemma_14_13 (T : X →L[ℝ] X) (hT : ‖T‖ ≤ 1) {xbar x : X} (hfix : T xbar = xbar)
    (hw : ∀ μ : StrongDual ℝ X, Tendsto (fun n => μ (cesaroOp T n x)) atTop (𝓝 (μ xbar))) :
    Tendsto (fun n => ‖cesaroOp T n x - xbar‖) atTop (𝓝 0) := by
  set R := LinearMap.range ((T - 1 : X →L[ℝ] X) : X →ₗ[ℝ] X)
  -- `yₙ = H_{n+1}x − x ∈ (T − I)X` converges weakly to `x̄ − x`
  have hmem : xbar - x ∈ closure (R : Set X) := by
    refine mem_closure_of_weak R (xs := fun n => cesaroOp T (n + 1) x - x)
      (fun n => cesaroOp_sub_mem_range T (n + 1) (by omega) x) fun μ => ?_
    simp only [map_sub]
    exact ((hw μ).comp (tendsto_add_atTop_nat 1)).sub tendsto_const_nhds
  have hc : (R.topologicalClosure : Set X) = closure (R : Set X) :=
    Submodule.topologicalClosure_coe R
  have hmem' : x - xbar ∈ closure (R : Set X) := by
    rw [← hc] at hmem ⊢
    have := R.topologicalClosure.neg_mem hmem
    rwa [neg_sub] at this
  have hlim := lemma_14_12 T hT hmem'
  refine hlim.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  rw [map_sub, cesaroOp_fixed T hfix hn]

end StokeyLucasPrescott.LawsOfLargeNumbers

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition functions

SLP §8.1, pp. 212–220. A transition function (`IsTransitionFunction`) is exactly a Markov kernel
(`isTransitionFunction_iff`). The Markov operator `T` on nonnegative and on bounded measurable
functions (`markovOp`, `markovOpR`) and its adjoint `T*` on probability measures (`adjointOp`):
Theorem 8.1 and its corollary (`theorem_8_1`, `theorem_8_1_cor`), Exercise 8.1 (`ex_8_1`),
Theorem 8.2 (`theorem_8_2`), Exercise 8.2 (`ex_8_2`), Theorem 8.3 and its corollary
(`theorem_8_3`, `theorem_8_3_cor`), the pairing `⟨f, λ⟩` and Exercise 8.3 (`ex_8_3`), the
`n`-step transition functions and Exercise 8.4 (`kpow`, `ex_8_4a`, `ex_8_4b`), the sequence
`λₙ = T*ⁿλ₀` (`adjointOp_iterate`), and the Feller and monotonicity properties (`IsFeller`,
`IsMonotoneTF`). Theorems 8.1 and 8.3 follow the book's proofs: indicators, then simple
functions, then increasing limits.
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

/-- A **transition function** (SLP p. 212): each `Q(z, ·)` is a probability measure and each
`Q(·, A)` is measurable. -/
def IsTransitionFunction (Q : Z → Set Z → ℝ≥0∞) : Prop :=
  (∀ z, ∃ μ : Measure Z, IsProbabilityMeasure μ ∧ ∀ A, MeasurableSet A → μ A = Q z A) ∧
    ∀ A, MeasurableSet A → Measurable fun z => Q z A

/-- Transition functions are Mathlib's Markov kernels. -/
theorem isTransitionFunction_iff (Q : Z → Set Z → ℝ≥0∞) :
    IsTransitionFunction Q ↔
      ∃ κ : Kernel Z Z, IsMarkovKernel κ ∧ ∀ z A, MeasurableSet A → κ z A = Q z A := by
  constructor
  · rintro ⟨h1, h2⟩
    choose μ hμ hμQ using h1
    have hm : Measurable μ := Measure.measurable_of_measurable_coe _ fun A hA => by
      have : (fun z => μ z A) = fun z => Q z A := funext fun z => hμQ z A hA
      rw [this]
      exact h2 A hA
    exact ⟨⟨μ, hm⟩, ⟨fun z => hμ z⟩, fun z A hA => hμQ z A hA⟩
  · rintro ⟨κ, hκ, hQ⟩
    refine ⟨fun z => ⟨κ z, inferInstance, fun A hA => hQ z A hA⟩, fun A hA => ?_⟩
    have : (fun z => Q z A) = fun z => κ z A := funext fun z => (hQ z A hA).symm
    rw [this]
    exact κ.measurable_coe hA

variable (κ : Kernel Z Z)

/-- The **Markov operator** on nonnegative functions (SLP (1), p. 213):
`(Tf)(z) = ∫ f(z′) Q(z, dz′)`. -/
noncomputable def markovOp (f : Z → ℝ≥0∞) (z : Z) : ℝ≥0∞ := ∫⁻ z', f z' ∂κ z

/-- The Markov operator on real functions. -/
noncomputable def markovOpR (f : Z → ℝ) (z : Z) : ℝ := ∫ z', f z' ∂κ z

/-- The **adjoint** `T*` (SLP (2), p. 213): `(T*λ)(A) = ∫ Q(z, A) λ(dz)`. -/
noncomputable def adjointOp (lam : Measure Z) : Measure Z := lam.bind κ

theorem markovOp_indicator {A : Set Z} (hA : MeasurableSet A) (c : ℝ≥0∞) (z : Z) :
    markovOp κ (A.indicator fun _ => c) z = c * κ z A := by
  rw [markovOp, lintegral_indicator_const hA]

/-- **Theorem 8.1.** `T` maps nonnegative measurable functions into nonnegative measurable
functions. The book's proof: `Tχ_A = Q(·, A)` is measurable; `T` is additive on simple
functions; and `T` commutes with increasing limits (Monotone Convergence Theorem). -/
theorem theorem_8_1 {f : Z → ℝ≥0∞} (hf : Measurable f) : Measurable (markovOp κ f) := by
  refine Measurable.ennreal_induction (motive := fun f => Measurable (markovOp κ f))
    ?_ ?_ ?_ hf
  · intro c s hs
    have : markovOp κ (s.indicator fun _ => c) = fun z => c * κ z s :=
      funext (markovOp_indicator κ hs c)
    rw [this]
    exact measurable_const.mul (κ.measurable_coe hs)
  · intro f g hfg hf hg ihf ihg
    have : markovOp κ (f + g) = fun z => markovOp κ f z + markovOp κ g z := funext fun z =>
      lintegral_add_left hf _
    rw [this]
    exact ihf.add ihg
  · intro f hf hmono ih
    have : markovOp κ (fun x => ⨆ n, f n x) = fun z => ⨆ n, markovOp κ (f n) z :=
      funext fun z => lintegral_iSup hf hmono
    rw [this]
    exact Measurable.iSup ih

variable [IsMarkovKernel κ]

theorem integrable_of_bounded {μ : Measure Z} [IsFiniteMeasure μ] {f : Z → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ z, |f z| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hM z)

/-- **Corollary to Theorem 8.1.** `T` maps bounded measurable functions into bounded measurable
functions: `Tf = Tf⁺ − Tf⁻`, and `|Tf| ≤ sup |f|`. -/
theorem theorem_8_1_cor {f : Z → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    Measurable (markovOpR κ f) ∧ ∀ z, |markovOpR κ f z| ≤ M := by
  constructor
  · have heq : markovOpR κ f = fun z =>
        (markovOp κ (fun z' => ENNReal.ofReal (f z')) z).toReal -
          (markovOp κ (fun z' => ENNReal.ofReal (-f z')) z).toReal := funext fun z =>
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hf hM)
    rw [heq]
    exact (theorem_8_1 κ hf.ennreal_ofReal).ennreal_toReal.sub
      (theorem_8_1 κ hf.neg.ennreal_ofReal).ennreal_toReal
  · intro z
    have := norm_integral_le_of_norm_le_const (μ := κ z) (C := M) (f := f)
      (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hM z')
    simpa [markovOpR, Real.norm_eq_abs, measureReal_def] using this

/-- **Exercise 8.1.** `T(αf + βg) = αTf + βTg` on bounded measurable functions. -/
theorem ex_8_1 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (α β : ℝ) :
    markovOpR κ (fun z => α * f z + β * g z) =
      fun z => α * markovOpR κ f z + β * markovOpR κ g z := by
  funext z
  simp only [markovOpR]
  rw [integral_add ((integrable_of_bounded hf hfM).const_mul α)
    ((integrable_of_bounded hg hgM).const_mul β), integral_const_mul, integral_const_mul]

omit [IsMarkovKernel κ] in
/-- `(T*λ)(A) = ∫ Q(z, A) λ(dz)` (SLP (2)). -/
theorem adjointOp_apply (lam : Measure Z) {A : Set Z} (hA : MeasurableSet A) :
    adjointOp κ lam A = ∫⁻ z, κ z A ∂lam :=
  Measure.bind_apply hA κ.aemeasurable

/-- **Theorem 8.2.** `T*` maps probability measures to probability measures: `T*λ(∅) = 0`,
`T*λ(Z) = 1`, and countable additivity follows from that of each `Q(z, ·)` by the Monotone
Convergence Theorem. -/
theorem theorem_8_2 (lam : Measure Z) [IsProbabilityMeasure lam] :
    IsProbabilityMeasure (adjointOp κ lam) ∧
      ∀ A : ℕ → Set Z, (∀ n, MeasurableSet (A n)) → Pairwise (Function.onFun Disjoint A) →
        ∫⁻ z, κ z (⋃ n, A n) ∂lam = ∑' n, ∫⁻ z, κ z (A n) ∂lam := by
  refine ⟨⟨?_⟩, fun A hA hd => ?_⟩
  · rw [adjointOp_apply κ lam MeasurableSet.univ]
    simp
  · simp_rw [measure_iUnion hd hA]
    exact lintegral_tsum fun n => (κ.measurable_coe (hA n)).aemeasurable

omit [IsMarkovKernel κ] in
/-- **Exercise 8.2.** `T*` is affine: `T*[αλ + (1 − α)μ] = αT*λ + (1 − α)T*μ`. -/
theorem ex_8_2 (lam μ : Measure Z) (α : ℝ≥0∞) :
    adjointOp κ (α • lam + (1 - α) • μ) = α • adjointOp κ lam + (1 - α) • adjointOp κ μ := by
  ext A hA
  simp only [adjointOp_apply κ _ hA, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  rfl

omit [IsMarkovKernel κ] in
/-- **Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for nonnegative measurable `f`. The book's proof:
indicators, simple functions, then the Monotone Convergence Theorem on both sides. -/
theorem theorem_8_3 (lam : Measure Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam := by
  refine Measurable.ennreal_induction (motive := fun f =>
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam) ?_ ?_ ?_ hf
  · intro c s hs
    simp_rw [markovOp_indicator κ hs]
    rw [lintegral_indicator hs, setLIntegral_const, adjointOp_apply κ lam hs,
      lintegral_const_mul _ (κ.measurable_coe hs), mul_comm]
  · intro f g hfg hf hg ihf ihg
    have : ∀ z, markovOp κ (f + g) z = markovOp κ f z + markovOp κ g z := fun z =>
      lintegral_add_left hf _
    simp_rw [this]
    rw [lintegral_add_left (theorem_8_1 κ hf), ihf, ihg, Pi.add_def,
      lintegral_add_left hf]
  · intro f hf hmono ih
    have : ∀ z, markovOp κ (fun x => ⨆ n, f n x) z = ⨆ n, markovOp κ (f n) z := fun z =>
      lintegral_iSup hf hmono
    simp_rw [this]
    rw [lintegral_iSup (fun n => theorem_8_1 κ (hf n))
      (fun m n hmn z => lintegral_mono (hmono hmn)), lintegral_iSup hf hmono]
    simp_rw [ih]

/-- **Corollary to Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for bounded measurable `f`. -/
theorem theorem_8_3_cor (lam : Measure Z) [IsProbabilityMeasure lam] {f : Z → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    ∫ z, markovOpR κ f z ∂lam = ∫ z', f z' ∂adjointOp κ lam := by
  have : IsProbabilityMeasure (adjointOp κ lam) := (theorem_8_2 κ lam).1
  have hTf := theorem_8_1_cor κ hf hM
  have hpos : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOpR κ g z = (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal -
        (markovOp κ (fun z' => ENNReal.ofReal (-g z')) z).toReal := fun g hg hgM z =>
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hg hgM)
  have hfin : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOp κ (fun z' => ENNReal.ofReal (g z')) z ≠ ∞ := fun g hg hgM z =>
    ((integrable_of_bounded hg hgM (μ := κ z)).lintegral_lt_top).ne
  have hbd : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) →
      Integrable (fun z => (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal) lam :=
    fun g hg hgM => integrable_of_bounded (theorem_8_1 κ hg.ennreal_ofReal).ennreal_toReal
      (M := |M|) fun z => by
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        refine ENNReal.toReal_le_of_le_ofReal (abs_nonneg M) ?_
        calc markovOp κ (fun z' => ENNReal.ofReal (g z')) z
            ≤ ∫⁻ _, ENNReal.ofReal |M| ∂κ z :=
              lintegral_mono fun z' => ENNReal.ofReal_le_ofReal
                ((le_abs_self _).trans ((hgM z').trans (le_abs_self M)))
          _ = ENNReal.ofReal |M| := by simp
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hf hM),
    integral_congr_ae (Eventually.of_forall (hpos f hf hM))]
  rw [integral_sub, integral_toReal (theorem_8_1 κ hf.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin f hf hM z).lt_top),
    integral_toReal (f := fun z => markovOp κ (fun z' => ENNReal.ofReal (-f z')) z)
      (theorem_8_1 κ hf.neg.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin (fun z => -f z) hf.neg (fun z => by
      rw [abs_neg]; exact hM z) z).lt_top),
    theorem_8_3 κ lam hf.ennreal_ofReal,
    theorem_8_3 κ lam (f := fun z => ENNReal.ofReal (-f z)) hf.neg.ennreal_ofReal]
  · exact hbd f hf hM
  · exact hbd (fun z => -f z) hf.neg fun z => by rw [abs_neg]; exact hM z

/-- The pairing `⟨f, λ⟩ = ∫ f dλ` (SLP p. 218). -/
noncomputable def pairing (f : Z → ℝ) (lam : Measure Z) : ℝ := ∫ z, f z ∂lam

omit [IsMarkovKernel κ] in
/-- **Exercise 8.3.** The pairing is linear in `f` and affine in `λ`. -/
theorem ex_8_3 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (a b : ℝ) (lam μ : Measure Z)
    [IsProbabilityMeasure lam] [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    pairing (fun z => a * f z + b * g z) lam = a * pairing f lam + b * pairing g lam ∧
      pairing f (ENNReal.ofReal α • lam + ENNReal.ofReal (1 - α) • μ) =
        α * pairing f lam + (1 - α) * pairing f μ := by
  constructor
  · simp only [pairing]
    rw [integral_add ((integrable_of_bounded hf hfM).const_mul a)
      ((integrable_of_bounded hg hgM).const_mul b), integral_const_mul, integral_const_mul]
  · simp only [pairing]
    rw [integral_add_measure ((integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hα0,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- The `n`-step transition function (SLP p. 219): `Q⁰ = id`,
`Qⁿ⁺¹(z, A) = ∫ Qⁿ(z′, A) Q(z, dz′)`. -/
noncomputable def kpow (κ : Kernel Z Z) : ℕ → Kernel Z Z
  | 0 => Kernel.id
  | n + 1 => kpow κ n ∘ₖ κ

omit [IsMarkovKernel κ] in
theorem kpow_one : kpow κ 1 = κ := by simp [kpow]

/-- **Exercise 8.4a.** The functions `Qⁿ` are transition functions. -/
theorem ex_8_4a (n : ℕ) : IsMarkovKernel (kpow κ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih => exact inferInstanceAs (IsMarkovKernel (kpow κ n ∘ₖ κ))

omit [IsMarkovKernel κ] in
theorem kpow_add (n m : ℕ) : kpow κ (n + m) = kpow κ m ∘ₖ kpow κ n := by
  induction n with
  | zero => simp [kpow]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega, kpow, ih, kpow, Kernel.comp_assoc]

omit [IsMarkovKernel κ] in
theorem markovOp_comp (η : Kernel Z Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    markovOp (η ∘ₖ κ) f = markovOp κ (markovOp η f) := by
  funext z
  exact Kernel.lintegral_comp η κ z hf

omit [IsMarkovKernel κ] in
theorem adjointOp_comp (η : Kernel Z Z) (lam : Measure Z) :
    adjointOp (η ∘ₖ κ) lam = adjointOp η (adjointOp κ lam) := by
  simp only [adjointOp]
  rw [Measure.bind_bind κ.aemeasurable η.aemeasurable]
  rfl

omit [IsMarkovKernel κ] in
/-- **Exercise 8.4b.** `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` and `T*⁽ⁿ⁺ᵐ⁾λ = T*ⁿ(T*ᵐλ)`. -/
theorem ex_8_4b (n m : ℕ) {f : Z → ℝ≥0∞} (hf : Measurable f) (lam : Measure Z) :
    markovOp (kpow κ (n + m)) f = markovOp (kpow κ n) (markovOp (kpow κ m) f) ∧
      adjointOp (kpow κ (n + m)) lam = adjointOp (kpow κ n) (adjointOp (kpow κ m) lam) := by
  constructor
  · rw [kpow_add, markovOp_comp _ _ hf]
  · rw [add_comm, kpow_add, adjointOp_comp]

omit [IsMarkovKernel κ] in
/-- `λₙ = T*λₙ₋₁ = T*ⁿlam₀` (SLP p. 219). -/
theorem adjointOp_iterate (n : ℕ) (lam₀ : Measure Z) :
    (adjointOp κ)^[n] lam₀ = adjointOp (kpow κ n) lam₀ := by
  induction n generalizing lam₀ with
  | zero =>
    change lam₀ = lam₀.bind Kernel.id
    have : (⇑(Kernel.id : Kernel Z Z)) = fun z => Measure.dirac z := funext Kernel.id_apply
    rw [this, Measure.bind_dirac]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, kpow, adjointOp_comp]

/-- `Q` has the **Feller property** (SLP p. 220): `T` maps bounded continuous functions to
continuous functions. -/
def IsFeller [TopologicalSpace Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) → Continuous (markovOpR κ f)

/-- `Q` is **monotone** (SLP p. 220): `T` maps bounded nondecreasing measurable functions to
nondecreasing functions. -/
def IsMonotoneTF [Preorder Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Measurable f → (∃ M, ∀ z, |f z| ≤ M) → Monotone f → Monotone (markovOpR κ f)

end StokeyLucasPrescott.LawsOfLargeNumbers

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Markov operator on `C(S)`: Exercise 14.4 and Lemma 14.9

SLP §14.2, pp. 425–437. `S` is a metric space with its Borel sets and `C(S) = S →ᵇ ℝ`.

* **Exercise 14.4** (`ex_14_4`, p. 435): under the Feller property (Assumption 14.2) the Markov
  operator `T` is a continuous linear operator on `C(S)` (`markovCLM`), with `‖T‖ = 1` (for
  nonempty `S`), and every constant function is a fixed point.
* `integral_markovCLM_pow`: `∫ Tᵏf dλ = ∫ f d(T*ᵏλ)` (Theorem 8.3, iterated).
* **Assumption 14.3** (`Assumption14_3`, p. 425): the Cesàro averages `(1/N) Σ_{n=1}^N T*ⁿλ₀`
  converge weakly to `λ*` for every `λ₀`. The limit is unique (`assumption14_3_unique`).
* **Lemma 14.9** (`lemma_14_9_of_repr`, p. 427): the averages `(1/M) Σ_{m=1}^M Tᵐf` converge
  uniformly on `S` to the constant `∫ f dλ*`. The proof is the book's, through the Norms Ergodic
  Lemma (`lemma_14_13`). It uses Assumptions 14.2 and 14.3 and that every element of `C(S)*` is
  represented by a signed measure. That is Theorem 14.14 for compact `S`, where Assumption 14.1
  enters; the hypothesis is discharged in `lemma_14_9`.

**Correction (index shift, pp. 436–437).** Assumption 14.3 and Lemma 14.9 use the powers
`1, …, N`, while `Hₙ` uses `0, …, n − 1`. The gaps are closed by
`(1/M) Σ_{m=1}^M Tᵐf = T(H_M f)` and `‖T(H_M f − f̄)‖ ≤ ‖H_M f − f̄‖`, and by an `O(1/n)` bound in
(10).
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-! ### Exercise 14.4 -/

theorem abs_markovOpR_le (κ : Kernel S S) [IsMarkovKernel κ] (f : S →ᵇ ℝ) (s : S) :
    |markovOpR κ f s| ≤ ‖f‖ :=
  (theorem_8_1_cor κ f.continuous.measurable fun z => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z).2 s

/-- `Tf` as a bounded continuous function, for a Feller `P`. -/
noncomputable def markovBCF (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ)
    (f : S →ᵇ ℝ) : S →ᵇ ℝ :=
  ofNormedAddCommGroup (markovOpR κ f)
    (hF f f.continuous ⟨‖f‖, fun z => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z⟩)
    ‖f‖ fun s => by rw [Real.norm_eq_abs]; exact abs_markovOpR_le κ f s

theorem markovBCF_apply (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ)
    (s : S) : markovBCF κ hF f s = ∫ s', f s' ∂κ s := rfl

/-- The Markov operator `T` as a linear map on `C(S)`. -/
noncomputable def markovLin (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) :
    (S →ᵇ ℝ) →ₗ[ℝ] (S →ᵇ ℝ) where
  toFun := markovBCF κ hF
  map_add' f g := by
    ext s
    simp only [markovBCF_apply, coe_add, Pi.add_apply]
    exact integral_add (f.integrable _) (g.integrable _)
  map_smul' c f := by
    ext s
    simp only [markovBCF_apply, coe_smul, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

/-- The Markov operator `T` as a continuous linear operator on `C(S)`, `‖T‖ ≤ 1`. -/
noncomputable def markovCLM (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) :
    (S →ᵇ ℝ) →L[ℝ] (S →ᵇ ℝ) :=
  (markovLin κ hF).mkContinuous 1 fun f => by
    rw [one_mul]
    exact norm_ofNormedAddCommGroup_le _ (norm_nonneg f) fun s => by
      rw [Real.norm_eq_abs]; exact abs_markovOpR_le κ f s

theorem markovCLM_apply (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ)
    (s : S) : markovCLM κ hF f s = ∫ s', f s' ∂κ s := rfl

theorem markovCLM_const (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) (c : ℝ) :
    markovCLM κ hF (const S c) = const S c := by
  ext s
  rw [markovCLM_apply]
  simp

theorem norm_markovCLM_le (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) :
    ‖markovCLM κ hF‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **Exercise 14.4.** Under the Feller property, `T : C(S) → C(S)` is a (continuous) linear
operator, `‖T‖ = 1` for nonempty `S`, and every constant function is a fixed point. -/
theorem ex_14_4 [Nonempty S] (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) :
    (∀ (a b : ℝ) (f g : S →ᵇ ℝ),
      markovCLM κ hF (a • f + b • g) = a • markovCLM κ hF f + b • markovCLM κ hF g) ∧
      ‖markovCLM κ hF‖ = 1 ∧ ∀ c : ℝ, markovCLM κ hF (const S c) = const S c := by
  refine ⟨fun a b f g => by rw [map_add, map_smul, map_smul], le_antisymm
    (norm_markovCLM_le κ hF) ?_, markovCLM_const κ hF⟩
  have h := (markovCLM κ hF).le_opNorm (const S 1)
  rw [markovCLM_const, norm_const_eq, norm_one, mul_one] at h
  exact h

/-! ### Iterates and the adjoint -/

theorem integral_markovCLM (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ)
    (lam : Measure S) [IsProbabilityMeasure lam] (f : S →ᵇ ℝ) :
    ∫ s, markovCLM κ hF f s ∂lam = ∫ s, f s ∂adjointOp κ lam :=
  theorem_8_3_cor κ lam f.continuous.measurable fun z => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z

/-- `∫ Tᵏf dλ = ∫ f d(T*ᵏλ)`. -/
theorem integral_markovCLM_pow (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) (k : ℕ)
    (lam : Measure S) [IsProbabilityMeasure lam] (f : S →ᵇ ℝ) :
    ∫ s, (markovCLM κ hF ^ k) f s ∂lam = ∫ s, f s ∂(adjointOp κ)^[k] lam := by
  induction k generalizing lam with
  | zero => rfl
  | succ k ih =>
    have : IsProbabilityMeasure (adjointOp κ lam) := (theorem_8_2 κ lam).1
    rw [pow_succ', Function.iterate_succ_apply, ← ih (adjointOp κ lam)]
    exact integral_markovCLM κ hF lam _

/-! ### Assumption 14.3 -/

/-- **Assumption 14.3.** For every initial `λ₀`, the Cesàro averages `(1/N) Σ_{n=1}^N T*ⁿλ₀`
converge weakly to the probability measure `λ*`. -/
def Assumption14_3 (κ : Kernel S S) (lstar : Measure S) : Prop :=
  IsProbabilityMeasure lstar ∧ ∀ lam₀ : Measure S, IsProbabilityMeasure lam₀ → ∀ f : S →ᵇ ℝ,
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ∫ s, f s ∂(adjointOp κ)^[n + 1] lam₀)
      atTop (𝓝 (∫ s, f s ∂lstar))

/-- The limit in Assumption 14.3 is unique. -/
theorem assumption14_3_unique [Nonempty S] {κ : Kernel S S} {l₁ l₂ : Measure S}
    (h₁ : Assumption14_3 κ l₁) (h₂ : Assumption14_3 κ l₂) : l₁ = l₂ := by
  have := h₁.1
  have := h₂.1
  have hd : IsProbabilityMeasure (Measure.dirac (Classical.arbitrary S)) := inferInstance
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f =>
    tendsto_nhds_unique (h₁.2 _ hd f) (h₂.2 _ hd f)

/-! ### Lemma 14.9 -/

/-- `∫ Hₙf dλ → ∫ f dλ*` for probability measures `λ` ((10), p. 436), with the index shift. -/
theorem integral_cesaroOp_tendsto (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ)
    {lstar : Measure S} (hA : Assumption14_3 κ lstar) (lam : Measure S) [IsProbabilityMeasure lam]
    (f : S →ᵇ ℝ) :
    Tendsto (fun n => ∫ s, cesaroOp (markovCLM κ hF) n f s ∂lam) atTop
      (𝓝 (∫ s, f s ∂lstar)) := by
  set a : ℕ → ℝ := fun k => ∫ s, f s ∂(adjointOp κ)^[k] lam
  have hprob : ∀ k, IsProbabilityMeasure ((adjointOp κ)^[k] lam) := fun k => by
    induction k with
    | zero => exact inferInstanceAs (IsProbabilityMeasure lam)
    | succ k ih => rw [Function.iterate_succ_apply']; exact (theorem_8_2 κ _).1
  have ha : ∀ k, |a k| ≤ ‖f‖ := fun k => by
    rw [← Real.norm_eq_abs]
    exact (norm_integral_le_of_norm_le_const (Eventually.of_forall f.norm_coe_le_norm)).trans
      (by simp)
  have hH : ∀ n, ∫ s, cesaroOp (markovCLM κ hF) n f s ∂lam =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k := fun n => by
    rw [cesaroOp_apply]
    simp only [coe_smul, coe_sum, Finset.sum_apply, smul_eq_mul]
    rw [integral_const_mul, integral_finsetSum _ fun k _ => (BoundedContinuousFunction.integrable
      lam _)]
    exact congrArg _ (Finset.sum_congr rfl fun k _ => integral_markovCLM_pow κ hF k lam f)
  simp_rw [hH]
  -- compare with the shifted averages of Assumption 14.3
  have hshift : ∀ n : ℕ, (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a (k + 1) + (n : ℝ)⁻¹ * (a 0 - a n) := fun n => by
    have : ∑ k ∈ Finset.range n, a k = ∑ k ∈ Finset.range n, a (k + 1) + a 0 - a n := by
      have h1 := Finset.sum_range_succ a n
      have h2 := Finset.sum_range_succ' a n
      linarith
    rw [this]
    ring
  simp_rw [hshift]
  have herr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (a 0 - a n)) atTop (𝓝 0) := by
    have hb : ∀ n : ℕ, |(n : ℝ)⁻¹ * (a 0 - a n)| ≤ 2 * ‖f‖ * (n : ℝ)⁻¹ := fun n => by
      rw [abs_mul, abs_inv, Nat.abs_cast, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (Nat.cast_nonneg n))
      linarith [abs_sub (a 0) (a n), ha 0, ha n]
    have hlim : Tendsto (fun n : ℕ => 2 * ‖f‖ * (n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul (2 * ‖f‖)
    exact squeeze_zero_norm (fun n => (Real.norm_eq_abs _).trans_le (hb n)) hlim
  have := (hA.2 lam inferInstance f).add herr
  rw [add_zero] at this
  exact this

/-- `∫ Hₙf dμ → μ(S) ∫ f dλ*` for finite measures `μ`. -/
theorem integral_cesaroOp_tendsto_finite (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ)
    {lstar : Measure S} (hA : Assumption14_3 κ lstar) (μ : Measure S) [IsFiniteMeasure μ]
    (f : S →ᵇ ℝ) :
    Tendsto (fun n => ∫ s, cesaroOp (markovCLM κ hF) n f s ∂μ) atTop
      (𝓝 (∫ s, const S (∫ s, f s ∂lstar) s ∂μ)) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · set c := μ Set.univ
    have hc0 : c ≠ 0 := (Measure.measure_univ_ne_zero).2 hμ.out
    have hct : c ≠ ⊤ := measure_ne_top μ _
    set lam := c⁻¹ • μ
    have : IsProbabilityMeasure lam := ⟨by
      simp [lam, c]⟩
    have hμlam : μ = c • lam := by
      simp only [lam, smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul]
    rw [hμlam]
    simp only [integral_smul_measure, const_apply, integral_const, smul_eq_mul,
      measureReal_ennreal_smul_apply, probReal_univ, mul_one]
    exact (integral_cesaroOp_tendsto κ hF hA lam f).const_mul _

/-- **Lemma 14.9** (from the representation of `C(S)*`). Under Assumptions 14.2 and 14.3, if every
continuous linear functional on `C(S)` is `f ↦ ∫ f dμ₁ − ∫ f dμ₂` for finite measures `μ₁`, `μ₂`,
then `(1/M) Σ_{m=1}^M Tᵐf → ∫ f dλ*` uniformly on `S`. -/
theorem lemma_14_9_of_repr (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ)
    {lstar : Measure S} (hA : Assumption14_3 κ lstar)
    (hR : ∀ Λ : StrongDual ℝ (S →ᵇ ℝ), ∃ μ₁ μ₂ : Measure S, IsFiniteMeasure μ₁ ∧
      IsFiniteMeasure μ₂ ∧ ∀ f : S →ᵇ ℝ, Λ f = ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂) (f : S →ᵇ ℝ) :
    Tendsto (fun M : ℕ => ‖(M : ℝ)⁻¹ • ∑ m ∈ Finset.range M, (markovCLM κ hF ^ (m + 1)) f -
      const S (∫ s, f s ∂lstar)‖) atTop (𝓝 0) := by
  set T := markovCLM κ hF
  set fbar := const S (∫ s, f s ∂lstar)
  have hfix : T fbar = fbar := markovCLM_const κ hF _
  have hw : ∀ Λ : StrongDual ℝ (S →ᵇ ℝ),
      Tendsto (fun n => Λ (cesaroOp T n f)) atTop (𝓝 (Λ fbar)) := fun Λ => by
    obtain ⟨μ₁, μ₂, h₁, h₂, hΛ⟩ := hR Λ
    simp_rw [hΛ]
    exact (integral_cesaroOp_tendsto_finite κ hF hA μ₁ f).sub
      (integral_cesaroOp_tendsto_finite κ hF hA μ₂ f)
  have hlim := lemma_14_13 T (norm_markovCLM_le κ hF) hfix hw
  refine squeeze_zero (fun M => norm_nonneg _) (fun M => ?_) hlim
  have heq : (M : ℝ)⁻¹ • ∑ m ∈ Finset.range M, (T ^ (m + 1)) f - fbar =
      T (cesaroOp T M f - fbar) := by
    rw [map_sub, hfix, cesaroOp_apply, map_smul, map_sum]
    congr 2
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [pow_succ']
    rfl
  rw [heq]
  exact (T.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (norm_markovCLM_le κ hF))

end StokeyLucasPrescott.LawsOfLargeNumbers

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 14.14: the Riesz representation theorem for signed measures

SLP §14.2, p. 435. The book: `S ⊆ ℝˡ` compact with its Borel sets, `C(S)` the bounded continuous
functions `S → ℝ`; if `T : C(S) → ℝ` is a continuous linear functional, there is a unique signed
measure `ν` with `T f = ∫ f dν` for all `f ∈ C(S)`. The book reuses the letter `T` (elsewhere the
Markov operator) for the functional; here it is `Λ`. The book gives no proof, referring to
Royden (1968, Theorem 8, pp. 310–311).

Here `S` is any compact metric space with its Borel σ-algebra (more general than the book),
`C(S)` is `S →ᵇ ℝ` with the sup norm, and `Λ : StrongDual ℝ (S →ᵇ ℝ)`. Signed measures are
Mathlib's `SignedMeasure S`, and the integral of `f` against `ν` is `sIntegral ν f`
`= ∫ f dν⁺ − ∫ f dν⁻` (Jordan decomposition of `ν`).

* `theorem_14_14_exists`: `Λ f = ∫ f dμ₁ − ∫ f dμ₂` for two finite Borel measures `μ₁, μ₂`.
* `theorem_14_14_unique`: a signed measure is determined by its integrals of `f ∈ C(S)`;
  `theorem_14_14_unique_measures` is the same for the pairs `(μ₁, μ₂)` (unique as `μ₁ − μ₂`).
* `theorem_14_14`: `∃! ν : SignedMeasure S, ∀ f, Λ f = sIntegral ν f`.
* `theorem_14_14_prob`: for nonempty `S`, `Λ f = α₁ ∫ f dλ₁ − α₂ ∫ f dλ₂` with `λ₁, λ₂`
  probability measures and `α₁, α₂ ≥ 0` (the form the book uses).

Proof route (Royden's).
1. *Jordan decomposition of the functional* (`functional_jordanDecomposition`). For `f ≥ 0` put
   `Λ⁺ f = sup {Λ g : 0 ≤ g ≤ f}` (`rieszPosSup`; bounded by `‖Λ‖ ‖f‖`). It is additive
   (`rieszPosSup_add`, splitting `0 ≤ g ≤ a + b` as `g ⊓ a + (g − g ⊓ a)`) and positively
   homogeneous (`rieszPosSup_smul`). Extend by `Λ⁺ f = Λ⁺ (f ⊔ 0) − Λ⁺ ((−f) ⊔ 0)`
   (`rieszPosPart`); independence of the decomposition (`rieszPosPart_sub`) makes it linear
   (`rieszPosPartLM`). Then `Λ⁺ ≥ 0` and `Λ⁻ := Λ⁺ − Λ ≥ 0`.
2. *Positive functionals are measures* (`exists_measure_of_positive`): Mathlib's
   Riesz–Markov–Kakutani theorem `RealRMK.integral_rieszMeasure` on `C_c(S, ℝ)`, which on a
   compact space is all of `C(S)`; the measure is finite.
3. *Uniqueness*: finite Borel measures on a metric space are determined by integrals of bounded
   continuous functions (`ext_of_forall_integral_eq_of_IsFiniteMeasure`). If `ν, ν'` integrate
   every `f` equally, then `ν⁺ + ν'⁻ = ν'⁺ + ν⁻`, hence `ν = ν'`.

Only the representation half is used later in the book (for Lemma 14.9); the isometry between
`C(S)*` and the signed measures with the total-variation norm is not formalised.
-/

open MeasureTheory BoundedContinuousFunction Set
open scoped BoundedContinuousFunction CompactlySupported

namespace StokeyLucasPrescott.LawsOfLargeNumbers

/-- The positive part of `Λ` evaluated at `f ≥ 0`:
`Λ⁺ f = sup {Λ g : g ∈ C(S), 0 ≤ g ≤ f}` (Royden's construction). For `f` not nonnegative the
set is empty and the value is junk; only `f ≥ 0` is used. -/
noncomputable def rieszPosSup {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    (f : S →ᵇ ℝ) : ℝ :=
  sSup (Λ '' {g | 0 ≤ g ∧ g ≤ f})

/-- The set `{Λ g : 0 ≤ g ≤ f}` is bounded above by `‖Λ‖ ‖f‖`; this is where continuity of `Λ` is
used. -/
theorem rieszPosSup_bddAbove {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    (f : S →ᵇ ℝ) : BddAbove (Λ '' {g | 0 ≤ g ∧ g ≤ f}) := by
  refine ⟨‖Λ‖ * ‖f‖, ?_⟩
  rintro _ ⟨g, ⟨hg0, hgf⟩, rfl⟩
  have hg : ‖g‖ ≤ ‖f‖ := by
    refine (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun x => ?_
    have h0 : 0 ≤ g x := hg0 x
    have h1 : g x ≤ f x := hgf x
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1.trans ((le_abs_self (f x)).trans
      (by simpa [Real.norm_eq_abs] using norm_coe_le_norm f x))
  calc Λ g ≤ ‖Λ g‖ := Real.le_norm_self _
    _ ≤ ‖Λ‖ * ‖g‖ := Λ.le_opNorm g
    _ ≤ ‖Λ‖ * ‖f‖ := mul_le_mul_of_nonneg_left hg (norm_nonneg Λ)

/-- Every `Λ g` with `0 ≤ g ≤ f` is at most `Λ⁺ f`. -/
theorem le_rieszPosSup {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {f g : S →ᵇ ℝ} (hg0 : 0 ≤ g) (hgf : g ≤ f) : Λ g ≤ rieszPosSup Λ f :=
  le_csSup (rieszPosSup_bddAbove Λ f) ⟨g, ⟨hg0, hgf⟩, rfl⟩

/-- `Λ⁺ f ≤ c` as soon as `Λ g ≤ c` for every `0 ≤ g ≤ f` (for `f ≥ 0`, so that `g = 0` is a
witness of non-emptiness). -/
theorem rieszPosSup_le {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {f : S →ᵇ ℝ} (hf : 0 ≤ f) {c : ℝ} (h : ∀ g : S →ᵇ ℝ, 0 ≤ g → g ≤ f → Λ g ≤ c) :
    rieszPosSup Λ f ≤ c := by
  refine csSup_le ⟨Λ 0, 0, ⟨le_rfl, hf⟩, rfl⟩ ?_
  rintro _ ⟨g, ⟨hg0, hgf⟩, rfl⟩
  exact h g hg0 hgf

/-- `Λ⁺ 0 = 0`. -/
theorem rieszPosSup_zero {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    rieszPosSup Λ 0 = 0 := by
  refine le_antisymm (rieszPosSup_le Λ le_rfl fun g hg0 hg => ?_) ?_
  · rw [le_antisymm hg hg0, map_zero]
  · simpa using le_rieszPosSup Λ (le_refl (0 : S →ᵇ ℝ)) le_rfl

/-- `Λ⁺` is additive on nonnegative functions. For `≤`, a function `0 ≤ g ≤ a + b` splits as
`g = g ⊓ a + (g − g ⊓ a)` with `0 ≤ g ⊓ a ≤ a` and `0 ≤ g − g ⊓ a ≤ b`. -/
theorem rieszPosSup_add {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {a b : S →ᵇ ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    rieszPosSup Λ (a + b) = rieszPosSup Λ a + rieszPosSup Λ b := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  refine le_antisymm (rieszPosSup_le Λ hab fun g hg0 hg => ?_) ?_
  · have h1 : 0 ≤ g ⊓ a := le_inf hg0 ha
    have h2 : g ⊓ a ≤ a := inf_le_right
    have h3 : 0 ≤ g - g ⊓ a := sub_nonneg.2 inf_le_left
    have h4 : g - g ⊓ a ≤ b := by
      intro x
      have hx : g x ≤ a x + b x := hg x
      change (g - g ⊓ a) x ≤ b x
      simp only [coe_sub, coe_inf, Pi.sub_apply, Pi.inf_apply]
      rcases le_total (g x) (a x) with h | h
      · have hbx : 0 ≤ b x := hb x
        rw [inf_eq_left.2 h]; linarith
      · rw [inf_eq_right.2 h]; linarith
    have e : g = g ⊓ a + (g - g ⊓ a) := by abel
    rw [e, map_add]
    exact add_le_add (le_rieszPosSup Λ h1 h2) (le_rieszPosSup Λ h3 h4)
  · rw [← le_sub_iff_add_le]
    refine rieszPosSup_le Λ ha fun g hg0 hga => ?_
    rw [le_sub_comm]
    refine rieszPosSup_le Λ hb fun h hh0 hhb => ?_
    rw [le_sub_iff_add_le, ← map_add]
    exact le_rieszPosSup Λ (add_nonneg hh0 hg0) (by rw [add_comm a b]; exact add_le_add hhb hga)

/-- A nonnegative multiple of a nonnegative bounded continuous function is nonnegative. -/
theorem bcf_smul_nonneg {S : Type*} [TopologicalSpace S] {c : ℝ} (hc : 0 ≤ c)
    {a : S →ᵇ ℝ} (ha : 0 ≤ a) : 0 ≤ c • a := fun x => by
  have hax : 0 ≤ a x := ha x
  change 0 ≤ (c • a) x
  simp only [coe_smul, smul_eq_mul]
  exact mul_nonneg hc hax

/-- Multiplication by a nonnegative scalar is monotone on bounded continuous functions. -/
theorem bcf_smul_le {S : Type*} [TopologicalSpace S] {c : ℝ} (hc : 0 ≤ c)
    {a b : S →ᵇ ℝ} (hab : a ≤ b) : c • a ≤ c • b := fun x => by
  have hx : a x ≤ b x := hab x
  change (c • a) x ≤ (c • b) x
  simp only [coe_smul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hx hc

/-- `Λ⁺` is positively homogeneous on nonnegative functions: `Λ⁺ (c f) = c Λ⁺ f` for `c ≥ 0`. -/
theorem rieszPosSup_smul {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {c : ℝ} (hc : 0 ≤ c) {a : S →ᵇ ℝ} (ha : 0 ≤ a) :
    rieszPosSup Λ (c • a) = c * rieszPosSup Λ a := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [zero_smul, rieszPosSup_zero, zero_mul]
  have hca : 0 ≤ c • a := bcf_smul_nonneg hc.le ha
  refine le_antisymm (rieszPosSup_le Λ hca fun g hg0 hg => ?_) ?_
  · have h1 : 0 ≤ c⁻¹ • g := bcf_smul_nonneg (inv_nonneg.2 hc.le) hg0
    have h2 : c⁻¹ • g ≤ a := by
      intro x
      have hx : g x ≤ c * a x := hg x
      change (c⁻¹ • g) x ≤ a x
      simp only [coe_smul, smul_eq_mul]
      rw [inv_mul_le_iff₀ hc]
      exact hx
    have e : g = c • (c⁻¹ • g) := by rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    rw [e, map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (le_rieszPosSup Λ h1 h2) hc.le
  · rw [← le_div_iff₀' hc]
    refine rieszPosSup_le Λ ha fun g hg0 hga => ?_
    rw [le_div_iff₀' hc, ← smul_eq_mul, ← map_smul]
    exact le_rieszPosSup Λ (bcf_smul_nonneg hc.le hg0) (bcf_smul_le hc.le hga)

/-- Every bounded continuous function is the difference of its positive and negative parts:
`f = f ⊔ 0 − (−f) ⊔ 0`. -/
theorem bcf_eq_posPart_sub_negPart {S : Type*} [TopologicalSpace S] (f : S →ᵇ ℝ) :
    f = f ⊔ 0 - (-f) ⊔ 0 := by
  ext x
  simp only [coe_sub, coe_sup, coe_neg, coe_zero, Pi.sub_apply, Pi.sup_apply, Pi.neg_apply,
    Pi.zero_apply]
  rw [max_def, max_def]
  split_ifs <;> linarith

/-- The extension of `Λ⁺` to all of `C(S)`: `Λ⁺ f = Λ⁺ (f ⊔ 0) − Λ⁺ ((−f) ⊔ 0)`. -/
noncomputable def rieszPosPart {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    (f : S →ᵇ ℝ) : ℝ :=
  rieszPosSup Λ (f ⊔ 0) - rieszPosSup Λ ((-f) ⊔ 0)

/-- Independence of the decomposition: if `a, b ≥ 0` then `Λ⁺ (a − b) = Λ⁺ a − Λ⁺ b`. -/
theorem rieszPosPart_sub {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {a b : S →ᵇ ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    rieszPosPart Λ (a - b) = rieszPosSup Λ a - rieszPosSup Λ b := by
  have hp : (0 : S →ᵇ ℝ) ≤ (a - b) ⊔ 0 := le_sup_right
  have hn : (0 : S →ᵇ ℝ) ≤ (-(a - b)) ⊔ 0 := le_sup_right
  have e : (a - b) ⊔ 0 + b = a + (-(a - b)) ⊔ 0 := by
    ext x
    simp only [coe_add, coe_sub, coe_sup, coe_neg, coe_zero, Pi.add_apply, Pi.sub_apply,
      Pi.sup_apply, Pi.neg_apply, Pi.zero_apply]
    rw [max_def, max_def]
    split_ifs <;> linarith
  have h := congrArg (rieszPosSup Λ) e
  rw [rieszPosSup_add Λ hp hb, rieszPosSup_add Λ ha hn] at h
  unfold rieszPosPart
  linarith

/-- The extended `Λ⁺` is additive. -/
theorem rieszPosPart_add {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    (f g : S →ᵇ ℝ) : rieszPosPart Λ (f + g) = rieszPosPart Λ f + rieszPosPart Λ g := by
  have hf1 : (0 : S →ᵇ ℝ) ≤ f ⊔ 0 := le_sup_right
  have hf2 : (0 : S →ᵇ ℝ) ≤ (-f) ⊔ 0 := le_sup_right
  have hg1 : (0 : S →ᵇ ℝ) ≤ g ⊔ 0 := le_sup_right
  have hg2 : (0 : S →ᵇ ℝ) ≤ (-g) ⊔ 0 := le_sup_right
  have e : f + g = (f ⊔ 0 + g ⊔ 0) - ((-f) ⊔ 0 + (-g) ⊔ 0) := by
    nth_rewrite 1 [bcf_eq_posPart_sub_negPart f]
    nth_rewrite 1 [bcf_eq_posPart_sub_negPart g]
    abel
  rw [e, rieszPosPart_sub Λ (add_nonneg hf1 hg1) (add_nonneg hf2 hg2), rieszPosSup_add Λ hf1 hg1,
    rieszPosSup_add Λ hf2 hg2]
  unfold rieszPosPart
  ring

/-- The extended `Λ⁺` is homogeneous: `Λ⁺ (c f) = c Λ⁺ f` for every real `c`. -/
theorem rieszPosPart_smul {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    (c : ℝ) (f : S →ᵇ ℝ) : rieszPosPart Λ (c • f) = c * rieszPosPart Λ f := by
  have hf1 : (0 : S →ᵇ ℝ) ≤ f ⊔ 0 := le_sup_right
  have hf2 : (0 : S →ᵇ ℝ) ≤ (-f) ⊔ 0 := le_sup_right
  have hx : ∀ x, f x = (f ⊔ 0) x - ((-f) ⊔ 0) x := fun x =>
    congrArg (fun g : S →ᵇ ℝ => g x) (bcf_eq_posPart_sub_negPart f)
  rcases le_or_gt 0 c with hc | hc
  · have e : c • f = c • (f ⊔ 0) - c • ((-f) ⊔ 0) := by
      ext x
      change c * f x = c * (f ⊔ 0) x - c * ((-f) ⊔ 0) x
      rw [hx x]
      ring
    rw [e, rieszPosPart_sub Λ (bcf_smul_nonneg hc hf1) (bcf_smul_nonneg hc hf2),
      rieszPosSup_smul Λ hc hf1, rieszPosSup_smul Λ hc hf2]
    unfold rieszPosPart
    ring
  · have hc' : 0 ≤ -c := by linarith
    have e : c • f = (-c) • ((-f) ⊔ 0) - (-c) • (f ⊔ 0) := by
      ext x
      change c * f x = (-c) * ((-f) ⊔ 0) x - (-c) * (f ⊔ 0) x
      rw [hx x]
      ring
    rw [e, rieszPosPart_sub Λ (bcf_smul_nonneg hc' hf2) (bcf_smul_nonneg hc' hf1),
      rieszPosSup_smul Λ hc' hf1, rieszPosSup_smul Λ hc' hf2]
    unfold rieszPosPart
    ring

/-- On nonnegative functions the extension agrees with the supremum. -/
theorem rieszPosPart_of_nonneg {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {f : S →ᵇ ℝ} (hf : 0 ≤ f) : rieszPosPart Λ f = rieszPosSup Λ f := by
  unfold rieszPosPart
  rw [sup_eq_left.2 hf, sup_eq_right.2 (neg_nonpos.2 hf), rieszPosSup_zero, sub_zero]

/-- The positive part `Λ⁺` of `Λ`, as a linear functional on `C(S)`. -/
noncomputable def rieszPosPartLM {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    (S →ᵇ ℝ) →ₗ[ℝ] ℝ where
  toFun := rieszPosPart Λ
  map_add' := rieszPosPart_add Λ
  map_smul' c f := by rw [rieszPosPart_smul, RingHom.id_apply, smul_eq_mul]

/-- `Λ⁺` is a positive functional. -/
theorem rieszPosPartLM_nonneg {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {f : S →ᵇ ℝ} (hf : 0 ≤ f) : 0 ≤ rieszPosPartLM Λ f := by
  change 0 ≤ rieszPosPart Λ f
  rw [rieszPosPart_of_nonneg Λ hf]
  simpa using le_rieszPosSup Λ (le_refl (0 : S →ᵇ ℝ)) hf

/-- `Λ ≤ Λ⁺` on nonnegative functions, so that `Λ⁻ = Λ⁺ − Λ` is positive. -/
theorem le_rieszPosPartLM {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ))
    {f : S →ᵇ ℝ} (hf : 0 ≤ f) : Λ f ≤ rieszPosPartLM Λ f := by
  change Λ f ≤ rieszPosPart Λ f
  rw [rieszPosPart_of_nonneg Λ hf]
  exact le_rieszPosSup Λ hf le_rfl

/-- **Jordan decomposition of a continuous linear functional on `C(S)`**: `Λ = Λ⁺ − Λ⁻` with
`Λ⁺` and `Λ⁻` positive linear functionals. -/
theorem functional_jordanDecomposition {S : Type*} [TopologicalSpace S]
    (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    ∃ P₁ P₂ : (S →ᵇ ℝ) →ₗ[ℝ] ℝ, (∀ f, 0 ≤ f → 0 ≤ P₁ f) ∧ (∀ f, 0 ≤ f → 0 ≤ P₂ f) ∧
      ∀ f, Λ f = P₁ f - P₂ f := by
  refine ⟨rieszPosPartLM Λ, rieszPosPartLM Λ - (Λ : (S →ᵇ ℝ) →ₗ[ℝ] ℝ),
    fun f hf => rieszPosPartLM_nonneg Λ hf, fun f hf => ?_, fun f => ?_⟩
  · rw [LinearMap.sub_apply, ContinuousLinearMap.coe_coe, sub_nonneg]
    exact le_rieszPosPartLM Λ hf
  · rw [LinearMap.sub_apply, ContinuousLinearMap.coe_coe]
    ring

/-- A positive linear functional on `C(S)`, `S` a compact metric space, is integration against a
finite Borel measure. This transfers Mathlib's Riesz–Markov–Kakutani theorem
(`RealRMK.integral_rieszMeasure`, stated on `C_c(S, ℝ)`) to bounded continuous functions; the
measure is finite because `S` is compact. -/
theorem exists_measure_of_positive {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] (P : (S →ᵇ ℝ) →ₗ[ℝ] ℝ) (hP : ∀ f, 0 ≤ f → 0 ≤ P f) :
    ∃ μ : Measure S, IsFiniteMeasure μ ∧ ∀ f : S →ᵇ ℝ, P f = ∫ s, f s ∂μ := by
  let L : C_c(S, ℝ) →ₗ[ℝ] (S →ᵇ ℝ) :=
    { toFun := fun f => mkOfCompact (f : C(S, ℝ))
      map_add' := fun f g => by ext x; rfl
      map_smul' := fun c f => by ext x; rfl }
  let Q : C_c(S, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ (P.comp L) fun f hf => hP _ fun s => hf s
  refine ⟨RealRMK.rieszMeasure Q, inferInstance, fun f => ?_⟩
  let f' : C_c(S, ℝ) := ⟨f.toContinuousMap, HasCompactSupport.of_compactSpace _⟩
  have h1 := RealRMK.integral_rieszMeasure Q f'
  have h2 : Q f' = P f := by
    change P (L f') = P f
    congr 1
  rw [← h2, ← h1]
  rfl

/-- The integral of `f` against a signed measure `ν`: `∫ f dν⁺ − ∫ f dν⁻`, where `ν = ν⁺ − ν⁻`
is the Jordan decomposition of `ν`. -/
noncomputable def sIntegral {S : Type*} [MeasurableSpace S] (ν : SignedMeasure S)
    (f : S → ℝ) : ℝ :=
  ∫ s, f s ∂ν.toJordanDecomposition.posPart - ∫ s, f s ∂ν.toJordanDecomposition.negPart

/-- If two differences of finite measures integrate every bounded continuous function equally,
`∫ f dμ₁ − ∫ f dμ₂ = ∫ f dμ₃ − ∫ f dμ₄`, then `μ₁ + μ₄ = μ₃ + μ₂`: finite Borel measures on a
metric space are determined by the integrals of bounded continuous functions. -/
theorem add_eq_add_of_integral_sub_eq {S : Type*} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] {μ₁ μ₂ μ₃ μ₄ : Measure S} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (h : ∀ f : S →ᵇ ℝ, ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂ = ∫ s, f s ∂μ₃ - ∫ s, f s ∂μ₄) :
    μ₁ + μ₄ = μ₃ + μ₂ := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_add_measure (f.integrable μ₁) (f.integrable μ₄),
    integral_add_measure (f.integrable μ₃) (f.integrable μ₂)]
  linarith [h f]

/-- If `μ₁ − μ₂ = μ₃ − μ₄` as signed measures, then `∫ f dμ₁ − ∫ f dμ₂ = ∫ f dμ₃ − ∫ f dμ₄` for
every bounded continuous `f`. -/
theorem integral_sub_eq_of_toSignedMeasure_eq {S : Type*} [TopologicalSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S] {μ₁ μ₂ μ₃ μ₄ : Measure S} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (h : μ₁.toSignedMeasure - μ₂.toSignedMeasure = μ₃.toSignedMeasure - μ₄.toSignedMeasure)
    (f : S →ᵇ ℝ) : ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂ = ∫ s, f s ∂μ₃ - ∫ s, f s ∂μ₄ := by
  have h' : μ₁ + μ₄ = μ₃ + μ₂ := by
    rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff, Measure.toSignedMeasure_add,
      Measure.toSignedMeasure_add, ← sub_eq_sub_iff_add_eq_add]
    exact h
  have h2 := congrArg (fun μ : Measure S => ∫ s, f s ∂μ) h'
  rw [integral_add_measure (f.integrable μ₁) (f.integrable μ₄),
    integral_add_measure (f.integrable μ₃) (f.integrable μ₂)] at h2
  linarith

/-- The integral against the signed measure `μ₁ − μ₂` is `∫ f dμ₁ − ∫ f dμ₂`, whatever the
Jordan decomposition of `μ₁ − μ₂` is. -/
theorem sIntegral_toSignedMeasure_sub {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (f : S →ᵇ ℝ) :
    sIntegral (μ₁.toSignedMeasure - μ₂.toSignedMeasure) f = ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂ :=
  integral_sub_eq_of_toSignedMeasure_eq
    (SignedMeasure.toSignedMeasure_toJordanDecomposition _) f

/-- **Theorem 14.14, existence** (p. 435): every continuous linear functional `Λ` on `C(S)` is
`Λ f = ∫ f dμ₁ − ∫ f dμ₂` for two finite Borel measures `μ₁, μ₂`. -/
theorem theorem_14_14_exists {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    ∃ μ₁ μ₂ : Measure S, IsFiniteMeasure μ₁ ∧ IsFiniteMeasure μ₂ ∧
      ∀ f : S →ᵇ ℝ, Λ f = ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂ := by
  obtain ⟨P₁, P₂, hP₁, hP₂, hΛ⟩ := functional_jordanDecomposition Λ
  obtain ⟨μ₁, hμ₁, h₁⟩ := exists_measure_of_positive P₁ hP₁
  obtain ⟨μ₂, hμ₂, h₂⟩ := exists_measure_of_positive P₂ hP₂
  exact ⟨μ₁, μ₂, hμ₁, hμ₂, fun f => by rw [hΛ f, h₁ f, h₂ f]⟩

/-- **Theorem 14.14, uniqueness** (p. 435): a signed measure is determined by its integrals of
bounded continuous functions. (Compactness is not needed here.) -/
theorem theorem_14_14_unique {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    {ν ν' : SignedMeasure S} (h : ∀ f : S →ᵇ ℝ, sIntegral ν f = sIntegral ν' f) : ν = ν' := by
  have hm := add_eq_add_of_integral_sub_eq h
  calc ν = ν.toJordanDecomposition.toSignedMeasure :=
        (SignedMeasure.toSignedMeasure_toJordanDecomposition ν).symm
    _ = ν'.toJordanDecomposition.toSignedMeasure := by
        unfold JordanDecomposition.toSignedMeasure
        rw [sub_eq_sub_iff_add_eq_add, ← Measure.toSignedMeasure_add,
          ← Measure.toSignedMeasure_add]
        exact Measure.toSignedMeasure_congr hm
    _ = ν' := SignedMeasure.toSignedMeasure_toJordanDecomposition ν'

/-- **Theorem 14.14, uniqueness for the pair of measures**: two representations
`Λ f = ∫ f dμ₁ − ∫ f dμ₂ = ∫ f dμ₃ − ∫ f dμ₄` give the same signed measure `μ₁ − μ₂ = μ₃ − μ₄`. -/
theorem theorem_14_14_unique_measures {S : Type*} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) {μ₁ μ₂ μ₃ μ₄ : Measure S} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (h₁₂ : ∀ f : S →ᵇ ℝ, Λ f = ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂)
    (h₃₄ : ∀ f : S →ᵇ ℝ, Λ f = ∫ s, f s ∂μ₃ - ∫ s, f s ∂μ₄) :
    μ₁.toSignedMeasure - μ₂.toSignedMeasure = μ₃.toSignedMeasure - μ₄.toSignedMeasure := by
  have hm := add_eq_add_of_integral_sub_eq fun f => (h₁₂ f).symm.trans (h₃₄ f)
  rw [sub_eq_sub_iff_add_eq_add, ← Measure.toSignedMeasure_add, ← Measure.toSignedMeasure_add]
  exact Measure.toSignedMeasure_congr hm

/-- **Theorem 14.14** (Riesz representation theorem, p. 435): for every continuous linear
functional `Λ` on `C(S)`, `S` a compact metric space, there is a unique signed measure `ν` with
`Λ f = ∫ f dν` for all `f ∈ C(S)`. -/
theorem theorem_14_14 {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    ∃! ν : SignedMeasure S, ∀ f : S →ᵇ ℝ, Λ f = sIntegral ν f := by
  obtain ⟨μ₁, μ₂, hμ₁, hμ₂, hΛ⟩ := theorem_14_14_exists Λ
  refine ⟨μ₁.toSignedMeasure - μ₂.toSignedMeasure,
    fun f => by rw [sIntegral_toSignedMeasure_sub, hΛ f], fun ν hν => ?_⟩
  refine theorem_14_14_unique fun f => ?_
  rw [← hν f, sIntegral_toSignedMeasure_sub, hΛ f]

/-- A finite measure on a nonempty space is `α` times a probability measure, `α ≥ 0`. -/
theorem exists_smul_probabilityMeasure {S : Type*} [MeasurableSpace S] [Nonempty S]
    (μ : Measure S) [IsFiniteMeasure μ] :
    ∃ α : ℝ, ∃ p : Measure S, 0 ≤ α ∧ IsProbabilityMeasure p ∧
      ∀ f : S → ℝ, ∫ s, f s ∂μ = α * ∫ s, f s ∂p := by
  by_cases hμ : μ = 0
  · exact ⟨0, Measure.dirac (Classical.arbitrary S), le_rfl, inferInstance,
      fun f => by simp [hμ]⟩
  · have : NeZero μ := ⟨hμ⟩
    refine ⟨μ.real univ, (μ univ)⁻¹ • μ, measureReal_nonneg, inferInstance, fun f => ?_⟩
    rw [integral_smul_measure, smul_eq_mul, ← mul_assoc, measureReal_def,
      ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel (NeZero.ne _) (measure_ne_top _ _),
      ENNReal.toReal_one, one_mul]

/-- **Theorem 14.14, the form used in the book** (for Lemma 14.9): every continuous linear
functional on `C(S)` is `Λ f = α₁ ∫ f dλ₁ − α₂ ∫ f dλ₂` with `λ₁, λ₂` probability measures and
`α₁, α₂ ≥ 0`. (`S` must be nonempty for probability measures to exist.) -/
theorem theorem_14_14_prob {S : Type*} [MetricSpace S] [CompactSpace S] [Nonempty S]
    [MeasurableSpace S] [BorelSpace S] (Λ : StrongDual ℝ (S →ᵇ ℝ)) :
    ∃ α₁ α₂ : ℝ, ∃ p₁ p₂ : Measure S, 0 ≤ α₁ ∧ 0 ≤ α₂ ∧ IsProbabilityMeasure p₁ ∧
      IsProbabilityMeasure p₂ ∧
      ∀ f : S →ᵇ ℝ, Λ f = α₁ * ∫ s, f s ∂p₁ - α₂ * ∫ s, f s ∂p₂ := by
  obtain ⟨μ₁, μ₂, hμ₁, hμ₂, hΛ⟩ := theorem_14_14_exists Λ
  obtain ⟨α₁, p₁, hα₁, hp₁, h₁⟩ := exists_smul_probabilityMeasure μ₁
  obtain ⟨α₂, p₂, hα₂, hp₂, h₂⟩ := exists_smul_probabilityMeasure μ₂
  exact ⟨α₁, α₂, p₁, p₂, hα₁, hα₂, hp₁, hp₂, fun f => by rw [hΛ f, h₁, h₂]⟩

end StokeyLucasPrescott.LawsOfLargeNumbers

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The strong law for Markov processes: Lemma 14.9 and Theorem 14.7

SLP §14.2, pp. 425–437. Assumption 14.1 is a compact metric `S` (the book: a compact subset of
`ℝˡ`), Assumption 14.2 the Feller property, Assumption 14.3 `Assumption14_3`.

* **Lemma 14.9** (`lemma_14_9`, p. 427): `(1/M) Σ_{m=1}^M Tᵐf → ∫ f dλ*` uniformly on `S`.
  It combines `lemma_14_9_of_repr` with the Riesz representation theorem (Theorem 14.14,
  `theorem_14_14_exists`).
* **Theorem 14.7** (`theorem_14_7`, Breiman's strong law, p. 425): for every `s₀` and every
  continuous `f`, `(1/N) Σ_{n=1}^N f(σₙ) → ∫ f dλ*`, `μ(s₀, ·)`-a.s. The proof is the book's: the
  splitting (1)–(2) of pp. 426–427, Lemma 14.8 for the first term and Lemma 14.9 for the second.

**Corrections.**
* Display (4) of p. 427 claims a threshold `N_m(ε)` uniform in `ω ∈ A_mᶜ`. Almost-everywhere
  convergence gives only a threshold depending on `ω`. The proof here lets every threshold depend
  on `ω`, which is all the conclusion needs.
* The introduction (p. 416) says that (3) holds when `S` is compact and `P` is Feller. That
  omits Assumption 14.3 (`feller_compact_not_enough`). On `S = {0, 1}` the identity kernel is
  Feller, but `(1/N) Σ f(sₙ) = f(s₀)`, so no single `λ*` serves for both starting points.
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

/-- **Lemma 14.9.** Under Assumptions 14.1–14.3, for every `f ∈ C(S)`,
`(1/M) Σ_{m=1}^M Tᵐf → ∫ f dλ*` uniformly on `S`. -/
theorem lemma_14_9 {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S]
    [BorelSpace S] (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) {lstar : Measure S}
    (hA : Assumption14_3 κ lstar) (f : S →ᵇ ℝ) :
    Tendsto (fun M : ℕ => ‖(M : ℝ)⁻¹ • ∑ m ∈ Finset.range M, (markovCLM κ hF ^ (m + 1)) f -
      const S (∫ s, f s ∂lstar)‖) atTop (𝓝 0) :=
  lemma_14_9_of_repr κ hF hA theorem_14_14_exists f

/-- The powers of `T` on `C(S)` are the iterates of the Markov operator. -/
theorem markovCLM_pow_apply {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ) (m : ℕ) (s : S) :
    (markovCLM κ hF ^ m) f s = (markovOpR κ)^[m] f s := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Function.iterate_succ_apply']
    change ∫ s', (markovCLM κ hF ^ m) f s' ∂κ s = _
    simp_rw [ih]
    rfl

/-- `|Σ_{n<N} aₙ − Σ_{n<N} a_{n+k}| ≤ 2kB` when `|aₙ| ≤ B`. -/
theorem abs_sum_sub_shift_le {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) (N k : ℕ) :
    |∑ n ∈ Finset.range N, a n - ∑ n ∈ Finset.range N, a (n + k)| ≤ 2 * k * B := by
  have h1 := Finset.sum_range_add a N k
  have h2 := Finset.sum_range_add a k N
  have hs : ∀ p : ℕ → ℕ, |∑ n ∈ Finset.range k, a (p n)| ≤ k * B := fun p => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul (Finset.range k) (fun n => |a (p n)|) B fun n _ => hB _
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have e1 := hs (fun n => N + n)
  have e2 := hs id
  have hshift : ∑ n ∈ Finset.range N, a (n + k) = ∑ n ∈ Finset.range N, a (k + n) :=
    Finset.sum_congr rfl fun n _ => by rw [add_comm]
  rw [hshift, add_comm N k] at *
  have : ∑ n ∈ Finset.range N, a n - ∑ n ∈ Finset.range N, a (k + n) =
      ∑ n ∈ Finset.range k, a n - ∑ n ∈ Finset.range k, a (N + n) := by linarith
  rw [this]
  simp only [id] at e2
  calc _ ≤ |∑ n ∈ Finset.range k, a n| + |∑ n ∈ Finset.range k, a (N + n)| := abs_sub _ _
    _ ≤ k * B + k * B := add_le_add e2 e1
    _ = 2 * k * B := by ring

/-- **Theorem 14.7** (the strong law of large numbers for Markov processes; Breiman 1960). Under
Assumptions 14.1–14.3, for every `s₀ ∈ S` and every continuous `f`,
`(1/N) Σ_{n=1}^N f(σₙ) → ∫ f dλ*`, `μ(s₀, ·)`-a.s. -/
theorem theorem_14_7 {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S]
    [BorelSpace S] (Q : Kernel S S) [IsMarkovKernel Q] (hF : IsFeller Q) {lstar : Measure S}
    (hA : Assumption14_3 Q lstar) (s₀ : S) (f : S →ᵇ ℝ) :
    ∀ᵐ ω ∂pathM Q s₀, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc 0 N, f (ω n)) atTop
      (𝓝 (∫ s, f s ∂lstar)) := by
  set c := ∫ s, f s ∂lstar
  set g : ℕ → S → ℝ := fun m => (markovOpR Q)^[m] f
  have hB : ∀ s, |f s| ≤ ‖f‖ := fun s => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm s
  have h9 := lemma_14_9 Q hF hA f
  filter_upwards [lemma_14_8_shift Q s₀ f.continuous.measurable hB] with ω hω
  -- the shifted form `(1/N) Σ_{n<N} f(σₙ) → c`
  have hcore : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (ω n)) atTop (𝓝 c) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Lemma 14.9: choose `M ≥ 1`
    obtain ⟨M, hMε, hM1⟩ := ((h9.eventually (gt_mem_nhds (half_pos hε))).and
      (eventually_ge_atTop 1)).exists
    set δ := ‖(M : ℝ)⁻¹ • ∑ m ∈ Finset.range M, (markovCLM Q hF ^ (m + 1)) f - const S c‖
    have hH : ∀ s, |(M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, g (m + 1) s - c| ≤ δ := fun s => by
      have := (((M : ℝ)⁻¹ • ∑ m ∈ Finset.range M, (markovCLM Q hF ^ (m + 1)) f -
        const S c)).norm_coe_le_norm s
      rw [Real.norm_eq_abs] at this
      convert this using 2
      simp only [coe_sub, coe_smul, coe_sum, Pi.sub_apply, Finset.sum_apply,
        const_apply, smul_eq_mul, markovCLM_pow_apply, g]
    -- Lemma 14.8 for `m = 1, …, M`, and the boundary terms
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM1
    have hev : ∀ᶠ N : ℕ in atTop, (∀ m ∈ Finset.range M, |(N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, (f (ω (n + (m + 1))) - g (m + 1) (ω n))| < ε / 4) ∧
        (N : ℝ)⁻¹ * (2 * M * ‖f‖) < ε / 4 ∧ 1 ≤ N := by
      refine ((Filter.eventually_all_finset _).2 fun m _ => ?_).and (Eventually.and ?_ ?_)
      · have := (hω (m + 1)).eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < ε / 4))
        filter_upwards [this] with N hN
        rwa [Real.dist_eq, sub_zero] at hN
      · have : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 * M * ‖f‖)) atTop (𝓝 0) := by
          simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const (2 * (M : ℝ) * ‖f‖)
        exact this.eventually (gt_mem_nhds (by positivity))
      · exact eventually_ge_atTop 1
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨hA8, hbd, hN1⟩ := hN₀ N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    set avg := (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (ω n)
    set G : ℕ → ℝ := fun m => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, g (m + 1) (ω n)
    -- each `|avg − Gₘ| < ε/2`
    have hfirst : ∀ m ∈ Finset.range M, |avg - G m| < ε / 2 := fun m hm => by
      have hbnd := abs_sum_sub_shift_le (a := fun n => f (ω n)) (fun n => hB _) N (m + 1)
      have hdecomp : avg - G m = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          (f (ω (n + (m + 1))) - g (m + 1) (ω n)) + (N : ℝ)⁻¹ * (∑ n ∈ Finset.range N, f (ω n) -
            ∑ n ∈ Finset.range N, f (ω (n + (m + 1)))) := by
        simp only [avg, G, Finset.sum_sub_distrib]
        ring
      have hm1 : ((m + 1 : ℕ) : ℝ) ≤ M := by
        have := Finset.mem_range.1 hm
        exact_mod_cast this
      have hb2 : |(N : ℝ)⁻¹ * (∑ n ∈ Finset.range N, f (ω n) -
          ∑ n ∈ Finset.range N, f (ω (n + (m + 1))))| < ε / 4 := by
        rw [abs_mul, abs_inv, Nat.abs_cast]
        refine lt_of_le_of_lt ?_ hbd
        refine mul_le_mul_of_nonneg_left (hbnd.trans ?_) (inv_nonneg.2 hNpos.le)
        have := norm_nonneg f
        nlinarith
      rw [hdecomp]
      exact (abs_add_le _ _).trans_lt (by linarith [hA8 m hm])
    -- the average over `m` of `Gₘ` is the time average of `(1/M) Σ_m T^{m+1}f`
    have hswap : (M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, G m - c = (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, ((M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, g (m + 1) (ω n) - c) := by
      simp only [G, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum]
      rw [Finset.sum_comm]
      field_simp
    have hsecond : |(M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, G m - c| < ε / 2 := by
      rw [hswap, abs_mul, abs_inv, Nat.abs_cast]
      refine lt_of_le_of_lt ?_ hMε
      have := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_card_nsmul (Finset.range N)
        (fun n => |(M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, g (m + 1) (ω n) - c|) δ
        fun n _ => hH (ω n))
      rw [Finset.card_range, nsmul_eq_mul] at this
      calc (N : ℝ)⁻¹ * |∑ n ∈ Finset.range N,
            ((M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, g (m + 1) (ω n) - c)|
          ≤ (N : ℝ)⁻¹ * (N * δ) := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hNpos.le)
        _ = δ := by field_simp
    have hsplit : avg - c = (M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, (avg - G m) +
        ((M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, G m - c) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      ring
    have hfirst' : |(M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, (avg - G m)| ≤ ε / 2 := by
      rw [abs_mul, abs_inv, Nat.abs_cast]
      have := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_card_nsmul (Finset.range M)
        (fun m => |avg - G m|) (ε / 2) fun m hm => (hfirst m hm).le)
      rw [Finset.card_range, nsmul_eq_mul] at this
      calc (M : ℝ)⁻¹ * |∑ m ∈ Finset.range M, (avg - G m)| ≤ (M : ℝ)⁻¹ * (M * (ε / 2)) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 hM'.le)
        _ = ε / 2 := by field_simp
    rw [Real.dist_eq, hsplit]
    exact (abs_add_le _ _).trans_lt (by linarith)
  -- back to the book's `Σ_{n=1}^N`
  refine tendsto_avg_of_bounded_diff (C := 2 * ‖f‖) hcore fun N => ?_
  have hIoc : ∑ n ∈ Finset.Ioc 0 N, f (ω n) =
      ∑ n ∈ Finset.range N, f (ω n) + f (ω N) - f (ω 0) := by
    have h1 := Finset.sum_range_succ (fun n => f (ω n)) N
    have h2 : ∑ n ∈ Finset.range (N + 1), f (ω n) = f (ω 0) + ∑ n ∈ Finset.Ioc 0 N, f (ω n) := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N), Nat.succ_eq_add_one,
        Finset.Ico_add_one_add_one_eq_Ioc]
    linarith
  rw [hIoc]
  have := hB (ω N)
  have := hB (ω 0)
  rw [show ∑ n ∈ Finset.range N, f (ω n) + f (ω N) - f (ω 0) - ∑ n ∈ Finset.range N, f (ω n) =
    f (ω N) - f (ω 0) by ring]
  linarith [abs_sub (f (ω N)) (f (ω 0))]

/-! ### Compactness and the Feller property are not enough (p. 416) -/

theorem adjointOp_id {S : Type*} [MeasurableSpace S] (μ : Measure S) :
    adjointOp (Kernel.id : Kernel S S) μ = μ := by
  change μ.bind Kernel.id = μ
  have : (⇑(Kernel.id : Kernel S S)) = fun s => Measure.dirac s := funext Kernel.id_apply
  rw [this, Measure.bind_dirac]

/-- **Correction (p. 416).** On the compact space `S = {0, 1}` the identity kernel is Feller, yet
no `λ*` satisfies the strong law (3) of p. 416 for every starting point: Assumption 14.3 is
needed. -/
theorem feller_compact_not_enough :
    IsFeller (Kernel.id : Kernel Bool Bool) ∧
      ¬ ∃ lstar : Measure Bool, ∀ (s₀ : Bool) (f : Bool →ᵇ ℝ), ∀ᵐ ω ∂pathM Kernel.id s₀,
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc 0 N, f (ω n)) atTop
          (𝓝 (∫ s, f s ∂lstar)) := by
  refine ⟨fun f _ _ => continuous_of_discreteTopology, ?_⟩
  rintro ⟨lstar, h⟩
  set fT : Bool →ᵇ ℝ := ofNormedAddCommGroupDiscrete indTrue 1 fun b => by
    cases b <;> simp [indTrue]
  have hval : ∀ s₀ : Bool, ∫ s, fT s ∂lstar = indTrue s₀ := fun s₀ => by
    have := isProbabilityMeasure_pathM (Kernel.id : Kernel Bool Bool) s₀
    have hid : ∀ n, (adjointOp (Kernel.id : Kernel Bool Bool))^[n] (Measure.dirac s₀) =
        Measure.dirac s₀ := fun n => by
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, adjointOp_id]
    have hcoord : ∀ n, ∀ᵐ ω ∂pathM (Kernel.id : Kernel Bool Bool) s₀, ω n = s₀ := fun n => by
      have hlaw := law_coord (Kernel.id : Kernel Bool Bool) s₀ n
      rw [hid n] at hlaw
      have : ∀ᵐ x ∂((pathM (Kernel.id : Kernel Bool Bool) s₀).map fun ω => ω n), x = s₀ := by
        rw [hlaw, ae_dirac_eq]
        exact eventually_pure.2 rfl
      exact ae_of_ae_map (measurable_pi_apply n).aemeasurable this
    obtain ⟨ω, hω1, hω2⟩ := ((ae_all_iff.2 hcoord).and (h s₀ fT)).exists
    have hseq : ∀ᶠ N : ℕ in atTop,
        (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc 0 N, fT (ω n) = indTrue s₀ := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (N : ℝ) ≠ 0 := by positivity
      simp only [hω1, Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      change (N : ℝ)⁻¹ * (N * indTrue s₀) = indTrue s₀
      field_simp
    exact tendsto_nhds_unique hω2 (tendsto_const_nhds.congr' (hseq.mono fun N hN => hN.symm))
  have h1 := hval true
  have h0 := hval false
  rw [h1] at h0
  simp [indTrue] at h0

end StokeyLucasPrescott.LawsOfLargeNumbers

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ConvAE
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ConvInProb
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.limsupSet
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.mem_limsupSet
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.measure_limsupSet
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.measurableSet_dev
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.lemma_14_1
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.lemma_14_2
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.measure_limsupSet_eq_zero
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.lemma_14_3
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ConvAE.convInProb
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_14_2a
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_14_2b
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.tri
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.tri_succ
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.le_tri
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.tri_mono
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.exists_row
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.row
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.row_spec
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.row_eq
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.pos
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.pos_le
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.row_tri_add
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.le_row
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.slideSet
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.sliding
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.unitLeb
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.sliding_eq_one
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.sliding_eq_zero
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.row_one_zero
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_14_1a
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_14_1b
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_14_1c
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.chebyshev
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.Uncorrelated
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.centered
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.memLp_centered
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_centered
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_centered_mul
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_sq_sum
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_sq_sum_le
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.memLp_sum_centered
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.avgDev
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_14_4
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.partialDev
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.partialDev_sub
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.memLp_partialDev_sub
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_sq_partialDev_sub_le
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.tsum_ofReal_div_sq_ne_top
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.squares_convAE
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.gapSq
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.gapSq_nonneg
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integrable_gapSq
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_gapSq_le
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.gaps_convAE
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.tendsto_sqrt_atTop
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_14_5
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.mgDiff
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.memLp_mgDiff
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.condExp_diff_ae_eq_zero
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.stronglyMeasurable_mgDiff
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_mgDiff_mul
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_mgDiff
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.uncorrelated_diff
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_14_6
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.norm_quotient_mk
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_14_10
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.mem_closure_of_weak
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.lemma_14_11
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_14_3a
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.cesaroOp
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.cesaroOp_apply
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_14_3b
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.cesaroOp_sub_one
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.lemma_14_12
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.cesaroOp_sub_mem_range
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.cesaroOp_fixed
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.lemma_14_13
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.IsTransitionFunction
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.isTransitionFunction_iff
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markovOp
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markovOpR
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.adjointOp
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markovOp_indicator
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_8_1
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integrable_of_bounded
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_8_1_cor
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_8_1
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.adjointOp_apply
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_8_2
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_8_2
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_8_3
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_8_3_cor
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.pairing
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_8_3
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.kpow
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.kpow_one
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_8_4a
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.kpow_add
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markovOp_comp
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.adjointOp_comp
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_8_4b
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.adjointOp_iterate
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.IsFeller
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.IsMonotoneTF
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.abs_markovOpR_le
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markovBCF
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markovBCF_apply
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markovLin
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markovCLM
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markovCLM_apply
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markovCLM_const
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.norm_markovCLM_le
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.ex_14_4
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_markovCLM
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_markovCLM_pow
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.Assumption14_3
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.assumption14_3_unique
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_cesaroOp_tendsto
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_cesaroOp_tendsto_finite
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.lemma_14_9_of_repr
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosSup
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosSup_bddAbove
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.le_rieszPosSup
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosSup_le
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosSup_zero
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosSup_add
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.bcf_smul_nonneg
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.bcf_smul_le
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosSup_smul
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.bcf_eq_posPart_sub_negPart
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosPart
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosPart_sub
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosPart_add
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosPart_smul
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosPart_of_nonneg
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosPartLM
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.rieszPosPartLM_nonneg
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.le_rieszPosPartLM
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.functional_jordanDecomposition
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.exists_measure_of_positive
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.sIntegral
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.add_eq_add_of_integral_sub_eq
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_sub_eq_of_toSignedMeasure_eq
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.sIntegral_toSignedMeasure_sub
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_14_14_exists
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_14_14_unique
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_14_14_unique_measures
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_14_14
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.exists_smul_probabilityMeasure
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_14_14_prob
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.trajKernel
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.isMarkovKernel_trajKernel
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.pathM
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.isProbabilityMeasure_pathM
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.measurable_coord_piLE
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markov_property
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.pathM_map_zero
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.measure_eq_of_real
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.law_coord
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.intro_2
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.tendsto_avg_of_bounded_diff
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.tendsto_avg_shift
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.iterate_markovOpR_bdd
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.mg_avg_tendsto
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.lemma_14_8_shift
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.lemma_14_8
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.unifBool
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.isProbabilityMeasure_unifBool
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.indTrue
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.integral_indTrue_unifBool
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.lemma_14_8_counterexample
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.lemma_14_9
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.markovCLM_pow_apply
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.abs_sum_sub_shift_le
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.theorem_14_7
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.adjointOp_id
#print axioms StokeyLucasPrescott.LawsOfLargeNumbers.feller_compact_not_enough
