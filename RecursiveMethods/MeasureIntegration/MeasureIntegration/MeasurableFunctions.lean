/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MeasureIntegration.Intervals

/-!
# Measurable functions

SLP §7.3, pp. 177–184. The book calls `f : S → ℝ` measurable when every set `{f ≤ a}` is
measurable; this is Mathlib's `Measurable` for the Borel σ-algebra (`measurable_iff_book`,
`measurable_iff_book_ereal`), and Exercise 7.14 is the book's route from one to the other
(`ex_7_14`). Exercise 7.9 (`ex_7_9a`, `ex_7_9b`, `ex_7_9b_converse_fails`, `ex_7_9c`), Exercise
7.10 (`ex_7_10a`, `ex_7_10b`), indicator functions (`measurable_indicator_iff`), simple functions
in standard representation (`ex_7_11`), Theorem 7.4 with the book's proof (`theorem_7_4`),
Theorem 7.5 with the book's dyadic construction (`theorem_7_5`, and `theorem_7_5_ext` for
`[0, +∞]`-valued functions), Exercise 7.12 (`ex_7_12a`, `ex_7_12b`), Exercise 7.13a
(`ex_7_13a`), compositions (`measurable_comp_book`) and Exercise 7.15 (`ex_7_15`).
-/

namespace StokeyLucasPrescott.MeasureIntegration

open Set MeasureTheory MeasurableSpace Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- The book's definition of a measurable real function (SLP p. 177, (1)). -/
theorem measurable_iff_book {f : S → ℝ} : Measurable f ↔ ∀ a, MeasurableSet {s | f s ≤ a} :=
  ⟨fun hf _ => measurableSet_le hf measurable_const, fun h => measurable_of_Iic h⟩

/-- The same criterion for extended real-valued functions (SLP p. 177). -/
theorem measurable_iff_book_ereal {f : S → EReal} :
    Measurable f ↔ ∀ a, MeasurableSet {s | f s ≤ a} :=
  ⟨fun hf _ => measurableSet_le hf measurable_const, fun h => measurable_of_Iic h⟩

/-- **Exercise 7.14.** If every `{f ≤ a}` is measurable then so is the inverse image of every
Borel set. The book's hint: the sets whose inverse image is measurable form a σ-algebra, and it
contains the generators `(−∞, a]` of the Borel sets. -/
theorem ex_7_14 {f : S → ℝ} (hf : ∀ a, MeasurableSet {s | f s ≤ a}) {A : Set ℝ}
    (hA : MeasurableSet[borel ℝ] A) : MeasurableSet (f ⁻¹' A) := by
  have hle : borel ℝ ≤ MeasurableSpace.map f ‹MeasurableSpace S› := by
    rw [borel_eq_generateFrom_Iic ℝ]
    exact generateFrom_le fun _ ⟨a, ha⟩ => ha ▸ hf a
  exact hle A hA

/-- **Exercise 7.9a.** Four equivalent definitions of measurability, using `≤`, `≥`, `<`
or `>`. -/
theorem ex_7_9a {f : S → ℝ} :
    ((∀ a, MeasurableSet {s | f s ≤ a}) ↔ ∀ a, MeasurableSet {s | a ≤ f s}) ∧
      ((∀ a, MeasurableSet {s | f s ≤ a}) ↔ ∀ a, MeasurableSet {s | f s < a}) ∧
      ((∀ a, MeasurableSet {s | f s ≤ a}) ↔ ∀ a, MeasurableSet {s | a < f s}) := by
  rw [← measurable_iff_book]
  refine ⟨⟨fun hf a => measurableSet_le measurable_const hf, fun h => measurable_of_Ici h⟩,
    ⟨fun hf a => measurableSet_lt hf measurable_const, fun h => measurable_of_Iio h⟩,
    ⟨fun hf a => measurableSet_lt measurable_const hf, fun h => measurable_of_Ioi h⟩⟩

/-- **Exercise 7.9b.** Each of these implies that `{f = a}` is measurable for every `a`. -/
theorem ex_7_9b {f : S → ℝ} (hf : ∀ a, MeasurableSet {s | f s ≤ a}) (a : ℝ) :
    MeasurableSet {s | f s = a} :=
  measurableSet_eq_fun (measurable_iff_book.2 hf) measurable_const

/-- **Exercise 7.9b, the converse fails.** On `ℝ` with the σ-algebra of countable and
co-countable sets, every level set of the identity is measurable but `{x ≤ 0}` is not. -/
theorem ex_7_9b_converse_fails :
    (∀ a : ℝ, MeasurableSet[countableCocountable] {x : ℝ | x = a}) ∧
      ¬ MeasurableSet[countableCocountable] {x : ℝ | x ≤ 0} := by
  refine ⟨fun a => Or.inl (countable_singleton a), fun h => ?_⟩
  have hvol1 : volume (Iic (0 : ℝ)) ≠ 0 := by simp
  have hvol2 : volume (Iic (0 : ℝ))ᶜ ≠ 0 := by simp
  rcases h with h | h
  · exact hvol1 (h.measure_zero volume)
  · exact hvol2 (h.measure_zero volume)

/-- **Exercise 7.9c.** For a measurable `f : S → [−∞, +∞]`, the sets `{f = +∞}` and `{f = −∞}`
are measurable. -/
theorem ex_7_9c {f : S → EReal} (hf : Measurable f) :
    MeasurableSet {s | f s = ⊤} ∧ MeasurableSet {s | f s = ⊥} :=
  ⟨measurableSet_eq_fun hf measurable_const, measurableSet_eq_fun hf measurable_const⟩

/-- **Exercise 7.10a.** Monotone (nondecreasing or nonincreasing) and continuous functions
`ℝ → ℝ` are Borel measurable. -/
theorem ex_7_10a {f : ℝ → ℝ} (hf : Monotone f ∨ Antitone f ∨ Continuous f) : Measurable f := by
  rcases hf with hf | hf | hf
  exacts [hf.measurable, hf.measurable, hf.measurable]

/-- **Exercise 7.10b.** With the σ-algebra of all subsets, every function is measurable. -/
theorem ex_7_10b {T : Type*} (f : T → ℝ) : Measurable[⊤] f := measurable_from_top

/-- An indicator function is measurable iff its set is (SLP p. 178). -/
theorem measurable_indicator_iff {A : Set S} :
    Measurable (A.indicator (fun _ => (1 : ℝ))) ↔ MeasurableSet A :=
  measurable_indicator_const_iff 1

/-- **Exercise 7.11.** If `φ = Σᵢ aᵢ χ_{Aᵢ}` is in standard representation (the `Aᵢ` partition
`S` and the `aᵢ` are distinct), then `φ` is measurable iff every `Aᵢ` is. -/
theorem ex_7_11 {ι : Type*} [Fintype ι] {A : ι → Set S} {a : ι → ℝ}
    (hd : Pairwise (Function.onFun Disjoint A)) (hcov : ∀ s, ∃ i, s ∈ A i)
    (ha : Function.Injective a) :
    Measurable (fun s => ∑ i, a i * (A i).indicator (fun _ => (1 : ℝ)) s) ↔
      ∀ i, MeasurableSet (A i) := by
  have hval : ∀ i, ∀ s ∈ A i, ∑ j, a j * (A j).indicator (fun _ => (1 : ℝ)) s = a i := by
    intro i s hs
    rw [Finset.sum_eq_single i]
    · simp [indicator_of_mem hs]
    · intro j _ hji
      rw [indicator_of_notMem (fun h' => (hd hji).ne_of_mem h' hs rfl), mul_zero]
    · simp
  constructor
  · intro hφ i
    have : A i = (fun s => ∑ j, a j * (A j).indicator (fun _ => (1 : ℝ)) s) ⁻¹' {a i} := by
      ext s
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · exact hval i s
      · intro hs
        obtain ⟨j, hj⟩ := hcov s
        rw [hval j s hj] at hs
        rwa [ha hs] at hj
    rw [this]
    exact hφ (measurableSet_singleton _)
  · intro hA
    exact Finset.measurable_sum _ fun i _ =>
      measurable_const.mul (measurable_const.indicator (hA i))

/-- **Theorem 7.4.** A pointwise limit of measurable functions is measurable. The book's proof:
`{f ≤ a} = ⋂_k ⋃_N ⋂_{n ≥ N} {fₙ ≤ a + 1/k}`. -/
theorem theorem_7_4 {f : ℕ → S → ℝ} {g : S → ℝ} (hf : ∀ n, Measurable (f n))
    (hlim : ∀ s, Tendsto (fun n => f n s) atTop (𝓝 (g s))) : Measurable g := by
  refine measurable_iff_book.2 fun a => ?_
  have heq : {s | g s ≤ a} =
      ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n ∈ Ici N, {s | f n s ≤ a + 1 / ((k : ℝ) + 1)} := by
    ext s
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_Ici]
    constructor
    · intro hs k
      have hk : g s < a + 1 / ((k : ℝ) + 1) := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      obtain ⟨N, hN⟩ := eventually_atTop.1 ((hlim s).eventually (gt_mem_nhds hk))
      exact ⟨N, fun n hn => (hN n hn).le⟩
    · intro hs
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := hs k
      have : g s ≤ a + 1 / ((k : ℝ) + 1) :=
        le_of_tendsto' ((hlim s).comp (tendsto_add_atTop_nat N)) fun n =>
          hN (n + N) (Nat.le_add_left N n)
      linarith
  rw [heq]
  exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun N =>
    MeasurableSet.biInter (to_countable _) fun n _ => measurableSet_le (hf n) measurable_const

/-! ### Theorem 7.5: approximation by simple functions -/

/-- The book's dyadic approximation (SLP p. 181): `⌊x 2ⁿ⌋ / 2ⁿ` below `n`, and `n` above. -/
noncomputable def dyadic (n : ℕ) (x : ℝ) : ℝ := if x < n then ⌊x * 2 ^ n⌋ / 2 ^ n else n

theorem dyadic_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ dyadic n x := by
  unfold dyadic
  split_ifs
  · exact div_nonneg (Int.cast_nonneg (Int.floor_nonneg.2 (by positivity))) (by positivity)
  · exact n.cast_nonneg

theorem dyadic_le (n : ℕ) {x : ℝ} : dyadic n x ≤ x := by
  unfold dyadic
  split_ifs with h
  · rw [div_le_iff₀ (by positivity)]
    exact Int.floor_le _
  · exact not_lt.1 h

theorem dyadic_close {n : ℕ} {x : ℝ} (hx : x < n) : x - 1 / 2 ^ n ≤ dyadic n x := by
  unfold dyadic
  simp only [hx, ↓reduceIte]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have := Int.lt_floor_add_one (x * 2 ^ n)
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ h2]
  linarith

theorem dyadic_mono_x (n : ℕ) {x y : ℝ} (hxy : x ≤ y) : dyadic n x ≤ dyadic n y := by
  unfold dyadic
  split_ifs with hx hy hy
  · exact div_le_div_of_nonneg_right (Int.cast_le.2 (Int.floor_mono (by gcongr))) (by positivity)
  · exact (div_le_iff₀ (by positivity)).2 (Int.floor_le _) |>.trans hx.le
  · exact absurd (hxy.trans_lt hy) hx
  · exact le_rfl

theorem le_dyadic_succ {n : ℕ} {x : ℝ} (hx : (n : ℝ) ≤ x) : (n : ℝ) ≤ dyadic (n + 1) x := by
  unfold dyadic
  split_ifs with h
  · rw [le_div_iff₀ (by positivity)]
    have : ((n * 2 ^ (n + 1) : ℕ) : ℤ) ≤ ⌊x * 2 ^ (n + 1)⌋ := by
      rw [Int.le_floor]
      push_cast
      gcongr
    exact_mod_cast this
  · push_cast
    linarith

theorem dyadic_mono_n (n : ℕ) {x : ℝ} : dyadic n x ≤ dyadic (n + 1) x := by
  by_cases hx : x < n
  · have hx' : x < (n + 1 : ℕ) := by push_cast; linarith
    unfold dyadic
    simp only [hx, hx', ↓reduceIte]
    have h2 : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    have : (2 * ⌊x * 2 ^ n⌋ : ℤ) ≤ ⌊x * 2 ^ (n + 1)⌋ := by
      rw [Int.le_floor]
      push_cast
      rw [h2]
      nlinarith [Int.floor_le (x * 2 ^ n), (by positivity : (0 : ℝ) < 2 ^ n)]
    rw [h2, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : ((2 * ⌊x * 2 ^ n⌋ : ℤ) : ℝ) ≤ (⌊x * 2 ^ (n + 1)⌋ : ℝ) := Int.cast_le.2 this
    rw [h2] at h3
    push_cast at h3
    nlinarith [(by positivity : (0 : ℝ) < 2 ^ n)]
  · have : dyadic n x = n := by unfold dyadic; simp only [hx, ↓reduceIte]
    rw [this]
    exact le_dyadic_succ (not_lt.1 hx)

/-- The values of `dyadic n` on `[0, ∞)` lie in a finite set. -/
theorem dyadic_mem (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    dyadic n x ∈ (Finset.range (n * 2 ^ n + 1)).image (fun k : ℕ => (k : ℝ) / 2 ^ n) := by
  rw [Finset.mem_image]
  unfold dyadic
  split_ifs with h
  · refine ⟨(⌊x * 2 ^ n⌋).toNat, ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      have h1 : ⌊x * 2 ^ n⌋ ≤ ((n * 2 ^ n : ℕ) : ℤ) := by
        rw [Int.floor_le_iff]
        push_cast
        nlinarith [(by positivity : (0 : ℝ) < 2 ^ n)]
      omega
    · rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.floor_nonneg.2 (by positivity))]
  · refine ⟨n * 2 ^ n, by simp, ?_⟩
    push_cast
    field_simp

theorem measurable_dyadic (n : ℕ) : Measurable (dyadic n) := by
  unfold dyadic
  refine Measurable.ite measurableSet_Iio ?_ measurable_const
  exact ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    (Int.measurable_floor.comp (measurable_id.mul_const _))).div_const _

theorem tendsto_dyadic {x : ℝ} : Tendsto (fun n => dyadic n x) atTop (𝓝 x) := by
  have hlow : Tendsto (fun n : ℕ => x - 1 / 2 ^ n) atTop (𝓝 x) := by
    have : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [one_div, inv_pow] using tendsto_const_nhds.sub this
  obtain ⟨N, hN⟩ := exists_nat_gt x
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun n => dyadic_le n)
  filter_upwards [eventually_ge_atTop N] with n hn
  exact dyadic_close (hN.trans_le (by exact_mod_cast hn))

/-- **Theorem 7.5 (approximation by simple functions).** A measurable `f : S → ℝ` is the
pointwise limit of measurable simple functions `φₙ`; if `f ≥ 0` they can be chosen with
`0 ≤ φₙ ≤ φₙ₊₁ ≤ f` (SLP (5)); and if `f` is bounded the convergence is uniform. The book's
construction: dyadic approximations of `f⁺` and `f⁻`. -/
theorem theorem_7_5 {f : S → ℝ} (hf : Measurable f) :
    ∃ φ : ℕ → S → ℝ, (∀ n, Measurable (φ n) ∧ (range (φ n)).Finite) ∧
      (∀ s, Tendsto (fun n => φ n s) atTop (𝓝 (f s))) ∧
      ((∀ s, 0 ≤ f s) → ∀ n s, 0 ≤ φ n s ∧ φ n s ≤ φ (n + 1) s ∧ φ (n + 1) s ≤ f s) ∧
      ((∃ M, ∀ s, |f s| ≤ M) → TendstoUniformly φ f atTop) := by
  set fp : S → ℝ := fun s => max (f s) 0
  set fm : S → ℝ := fun s => max (-f s) 0
  have hfpm : ∀ s, f s = fp s - fm s := fun s => by
    simp only [fp, fm]
    rcases le_total (f s) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  refine ⟨fun n s => dyadic n (fp s) - dyadic n (fm s), fun n => ⟨?_, ?_⟩, fun s => ?_,
    fun hpos n s => ?_, fun ⟨M, hM⟩ => ?_⟩
  · exact ((measurable_dyadic n).comp (hf.max measurable_const)).sub
      ((measurable_dyadic n).comp (hf.neg.max measurable_const))
  · let F := (Finset.range (n * 2 ^ n + 1)).image (fun k : ℕ => (k : ℝ) / 2 ^ n)
    refine ((F.finite_toSet.image2 (· - ·) F.finite_toSet)).subset ?_
    rintro _ ⟨s, rfl⟩
    exact mem_image2_of_mem (dyadic_mem n (le_max_right _ _)) (dyadic_mem n (le_max_right _ _))
  · rw [hfpm s]
    exact tendsto_dyadic.sub tendsto_dyadic
  · have hm : fm s = 0 := max_eq_right (by linarith [hpos s])
    have h0 : ∀ k, dyadic k 0 = 0 := fun k => by
      unfold dyadic
      split_ifs <;> simp_all
    simp only [hm, h0, sub_zero]
    have hfp : fp s = f s := max_eq_left (hpos s)
    rw [hfp]
    exact ⟨dyadic_nonneg n (hpos s), dyadic_mono_n n, dyadic_le (n + 1)⟩
  · have hbound : ∀ s, fp s < (⌈M⌉₊ + 1 : ℕ) ∧ fm s < (⌈M⌉₊ + 1 : ℕ) := fun s => by
      have h1 := Nat.le_ceil M
      have h2 := abs_le.1 (hM s)
      constructor <;> push_cast <;> simp only [fp, fm, max_lt_iff] <;> constructor <;> linarith
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    filter_upwards [eventually_ge_atTop (⌈M⌉₊ + 1 + K)] with n hn s
    have hn1 : ((⌈M⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈M⌉₊ + 1 ≤ n)
    have hp := dyadic_close ((hbound s).1.trans_le hn1)
    have hm := dyadic_close ((hbound s).2.trans_le hn1)
    have hp' := dyadic_le n (x := fp s)
    have hm' := dyadic_le n (x := fm s)
    have hsmall : 1 / (2 : ℝ) ^ n ≤ (1 / 2) ^ K := by
      rw [one_div_pow]
      gcongr
      · norm_num
      · omega
    rw [Real.dist_eq, hfpm s, abs_lt]
    constructor <;> nlinarith [(by positivity : (0 : ℝ) < 1 / 2 ^ n)]

/-- **Theorem 7.5 for `[0, +∞]`-valued functions** (SLP p. 181): a measurable
`f : S → [0, +∞]` is the increasing limit of measurable, finite-valued simple functions
`0 ≤ φₙ ≤ φₙ₊₁ ≤ f`. Here `φₙ = n` on `{f ≥ n}`. -/
theorem theorem_7_5_ext {f : S → ℝ≥0∞} (hf : Measurable f) :
    ∃ φ : ℕ → S → ℝ, (∀ n, Measurable (φ n) ∧ (range (φ n)).Finite) ∧
      (∀ n s, 0 ≤ φ n s ∧ φ n s ≤ φ (n + 1) s ∧ ENNReal.ofReal (φ n s) ≤ f s) ∧
      ∀ s, Tendsto (fun n => ENNReal.ofReal (φ n s)) atTop (𝓝 (f s)) := by
  refine ⟨fun n s => dyadic n (min (f s) n).toReal, fun n => ⟨?_, ?_⟩, fun n s => ⟨?_, ?_, ?_⟩,
    fun s => ?_⟩
  · exact (measurable_dyadic n).comp ((hf.min measurable_const).ennreal_toReal)
  · let F := (Finset.range (n * 2 ^ n + 1)).image (fun k : ℕ => (k : ℝ) / 2 ^ n)
    refine F.finite_toSet.subset ?_
    rintro _ ⟨s, rfl⟩
    exact dyadic_mem n ENNReal.toReal_nonneg
  · exact dyadic_nonneg n ENNReal.toReal_nonneg
  · refine (dyadic_mono_n n).trans (dyadic_mono_x _ ?_)
    refine ENNReal.toReal_mono (by simp) (min_le_min_left _ ?_)
    exact_mod_cast n.le_succ
  · have h1 : dyadic n (min (f s) n).toReal ≤ (min (f s) n).toReal := dyadic_le n
    calc ENNReal.ofReal (dyadic n (min (f s) n).toReal)
        ≤ ENNReal.ofReal (min (f s) n).toReal := ENNReal.ofReal_le_ofReal h1
      _ = min (f s) n := ENNReal.ofReal_toReal (by simp)
      _ ≤ f s := min_le_left _ _
  · by_cases htop : f s = ∞
    · have : ∀ n : ℕ, ENNReal.ofReal (dyadic n (min (f s) n).toReal) = n := fun n => by
        rw [htop]
        simp only [min_eq_right le_top, ENNReal.toReal_natCast]
        unfold dyadic
        simp only [lt_irrefl, ↓reduceIte, ENNReal.ofReal_natCast]
      rw [htop]
      exact ENNReal.tendsto_nat_nhds_top.congr fun n => (this n).symm
    · have hev : ∀ᶠ n : ℕ in atTop, dyadic n (min (f s) n).toReal = dyadic n (f s).toReal := by
        obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt htop
        filter_upwards [eventually_ge_atTop N] with n hn
        rw [min_eq_left (hN.le.trans (by exact_mod_cast hn))]
      have := (ENNReal.tendsto_ofReal (tendsto_dyadic (x := (f s).toReal)))
      rw [ENNReal.ofReal_toReal htop] at this
      exact this.congr' (hev.mono fun n hn => by dsimp only; rw [hn])

/-- **Exercise 7.12a.** Sums, products, absolute values and scalar multiples of measurable
functions are measurable. -/
theorem ex_7_12a {f g : S → ℝ} (hf : Measurable f) (hg : Measurable g) (c : ℝ) :
    Measurable (f + g) ∧ Measurable (f * g) ∧ Measurable (fun s => |f s|) ∧
      Measurable (c • f) :=
  ⟨hf.add hg, hf.mul hg, hf.abs, hf.const_smul c⟩

/-- **Exercise 7.12b.** For measurable `fₙ`, the functions `inf fₙ`, `sup fₙ`, `lim inf fₙ` and
`lim sup fₙ` are measurable; they take values in `[−∞, +∞]`. -/
theorem ex_7_12b {f : ℕ → S → ℝ} (hf : ∀ n, Measurable (f n)) :
    Measurable (fun s => ⨅ n, (f n s : EReal)) ∧ Measurable (fun s => ⨆ n, (f n s : EReal)) ∧
      Measurable (fun s => liminf (fun n => (f n s : EReal)) atTop) ∧
      Measurable (fun s => limsup (fun n => (f n s : EReal)) atTop) := by
  have hf' : ∀ n, Measurable fun s => (f n s : EReal) := fun n =>
    measurable_coe_real_ereal.comp (hf n)
  exact ⟨Measurable.iInf hf', Measurable.iSup hf', Measurable.liminf hf', Measurable.limsup hf'⟩

/-- **Exercise 7.13a.** Continuous functions on `ℝˡ` are Borel measurable. -/
theorem ex_7_13a {l : ℕ} {f : (Fin l → ℝ) → ℝ} (hf : Continuous f) : Measurable f :=
  hf.measurable

/-- Compositions of measurable functions are measurable (SLP p. 183). -/
theorem measurable_comp_book {T U : Type*} [MeasurableSpace T] [MeasurableSpace U] {f : S → T}
    {g : T → U} (hf : Measurable f) (hg : Measurable g) : Measurable (fun s => g (f s)) :=
  hg.comp hf

/-- **Exercise 7.15.** `f : ℝˡ → ℝᵐ` is measurable iff each component `fᵢ` is. -/
theorem ex_7_15 {l m : ℕ} {f : (Fin l → ℝ) → Fin m → ℝ} :
    Measurable f ↔ ∀ i, Measurable fun x => f x i :=
  measurable_pi_iff

end StokeyLucasPrescott.MeasureIntegration
