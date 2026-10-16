/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import WeakConvergence.Determining

/-!
# Distribution functions on `ℝˡ`

SLP §12.2, pp. 364–369. Points of `ℝˡ` are functions `Fin l → ℝ`, ordered coordinatewise. The
distribution function of `λ` is `F(x) = λ((−∞, x])` (`distFun`). The half-open box `(a, b]` is
`∏ᵢ (aᵢ, bᵢ]` (`box`), and for `t ⊆ {1, …, l}` its vertex `a + θₜd` takes `bᵢ` for `i ∈ t` and
`aᵢ` otherwise (`vertex`).

* **Exercise 12.3** (`ex_12_3`): a nondecreasing `F` continuous from above and from below at `x`
  is continuous at `x`.
* **Theorem 12.7a** (`theorem_12_7a`): (D1) `F` is nondecreasing, tends to `0` as any coordinate
  tends to `−∞`, and to `1` as all coordinates tend to `+∞`; (D2) `F` is continuous from above;
  (D3) `Σₜ (−1)^{l − |t|} F(a + θₜd) = λ((a, b]) ≥ 0`. (D3) comes from the identity
  `1_{(a,b]} = ∏ᵢ (1[xᵢ ≤ bᵢ] − 1[xᵢ ≤ aᵢ])`, expanded as a sum over `t`.
* **Theorem 12.7b**, uniqueness (`distFun_injective`): the sets `(−∞, x]` form a π-system
  generating the Borel sets of `ℝˡ`, so `F` determines `λ`. Existence is in
  `MultivariateStieltjes`.
* **Theorem 12.7c** (`theorem_12_7c`): `F` is continuous from below at `x` iff `λ(∂(−∞, x]) = 0`.
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory Filter Topology Set

variable {l : ℕ}

/-- The distribution function `F(x) = λ((−∞, x])`. -/
noncomputable def distFun (μ : Measure (Fin l → ℝ)) (x : Fin l → ℝ) : ℝ := μ.real (Iic x)

/-- The half-open box `(a, b] = ∏ᵢ (aᵢ, bᵢ]`. -/
def box (a b : Fin l → ℝ) : Set (Fin l → ℝ) := Set.pi univ fun i => Ioc (a i) (b i)

/-- The vertex of `(a, b]` taking `bᵢ` for `i ∈ t` and `aᵢ` otherwise. -/
def vertex (a b : Fin l → ℝ) (t : Finset (Fin l)) : Fin l → ℝ := fun i => if i ∈ t then b i else a i

/-- The alternating vertex sum `Σₜ (−1)^{l − |t|} F(a + θₜd)` of (D3). -/
def vertexSum (F : (Fin l → ℝ) → ℝ) (a b : Fin l → ℝ) : ℝ :=
  ∑ t : Finset (Fin l), (-1 : ℝ) ^ (l - t.card) * F (vertex a b t)

/-- The vector `ε1 = (ε, …, ε)`. -/
def diag (ε : ℝ) : Fin l → ℝ := fun _ => ε

/-- `F` is **continuous from above** at `x`: `F(x + ε1) → F(x)` as `ε ↓ 0`. -/
def ContFromAbove (F : (Fin l → ℝ) → ℝ) (x : Fin l → ℝ) : Prop :=
  Tendsto (fun ε => F (x + diag ε)) (𝓝[>] 0) (𝓝 (F x))

/-- `F` is **continuous from below** at `x`: `F(x − ε1) → F(x)` as `ε ↓ 0`. -/
def ContFromBelow (F : (Fin l → ℝ) → ℝ) (x : Fin l → ℝ) : Prop :=
  Tendsto (fun ε => F (x - diag ε)) (𝓝[>] 0) (𝓝 (F x))

theorem Iic_eq_pi (x : Fin l → ℝ) : Iic x = Set.pi univ fun i => Iic (x i) := by
  ext y; simp [Pi.le_def]

/-- The product expansion: `1_{(a,b]}(y) = Σₜ (−1)^{l − |t|} 1[y ≤ a + θₜd]` for `a ≤ b`. -/
theorem box_indicator_eq {a b : Fin l → ℝ} (hab : a ≤ b) (y : Fin l → ℝ) :
    (box a b).indicator (1 : (Fin l → ℝ) → ℝ) y =
      ∑ t : Finset (Fin l), (-1 : ℝ) ^ (l - t.card) * (Iic (vertex a b t)).indicator 1 y := by
  classical
  -- `1_{(a,b]}(y) = ∏ᵢ (1[yᵢ ≤ bᵢ] − 1[yᵢ ≤ aᵢ])`
  have hprod : (box a b).indicator (1 : (Fin l → ℝ) → ℝ) y =
      ∏ i, ((Iic (b i)).indicator (1 : ℝ → ℝ) (y i) + -(Iic (a i)).indicator 1 (y i)) := by
    by_cases hy : y ∈ box a b
    · rw [indicator_of_mem hy, Pi.one_apply]
      symm
      refine Finset.prod_eq_one fun i _ => ?_
      have hi := hy i (mem_univ i)
      rw [indicator_of_mem (show y i ∈ Iic (b i) from hi.2),
        indicator_of_notMem (show y i ∉ Iic (a i) from fun h => (not_le.2 hi.1) h)]
      simp
    · rw [indicator_of_notMem hy]
      simp only [box, Set.mem_pi, mem_univ, true_implies, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      by_cases h1 : y i ≤ a i
      · rw [indicator_of_mem (show y i ∈ Iic (b i) from h1.trans (hab i)),
          indicator_of_mem (show y i ∈ Iic (a i) from h1)]; simp
      · have h2 : ¬ y i ≤ b i := fun h => hi ⟨not_le.1 h1, h⟩
        rw [indicator_of_notMem (show y i ∉ Iic (b i) from h2),
          indicator_of_notMem (show y i ∉ Iic (a i) from h1)]; simp
  rw [hprod, Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_neg, Finset.card_univ_sdiff, Fintype.card_fin]
  -- the product of indicators is the indicator of `(−∞, vertex]`
  have hv : (∏ i ∈ t, (Iic (b i)).indicator (1 : ℝ → ℝ) (y i)) *
      ∏ i ∈ Finset.univ \ t, (Iic (a i)).indicator (1 : ℝ → ℝ) (y i) =
        (Iic (vertex a b t)).indicator 1 y := by
    by_cases hy : y ≤ vertex a b t
    · rw [indicator_of_mem (show y ∈ Iic (vertex a b t) from hy), Pi.one_apply]
      rw [Finset.prod_eq_one fun i hi => ?_, Finset.prod_eq_one fun i hi => ?_, one_mul]
      · have := hy i; simp only [vertex, Finset.mem_sdiff] at this hi
        simp only [hi.2, ↓reduceIte] at this
        rw [indicator_of_mem (show y i ∈ Iic (a i) from this)]; rfl
      · have := hy i; simp only [vertex] at this
        simp only [hi, ↓reduceIte] at this
        rw [indicator_of_mem (show y i ∈ Iic (b i) from this)]; rfl
    · rw [indicator_of_notMem (show y ∉ Iic (vertex a b t) from hy)]
      rw [Pi.le_def] at hy
      push Not at hy
      obtain ⟨i, hi⟩ := hy
      by_cases hit : i ∈ t
      · simp only [vertex, hit, ↓reduceIte] at hi
        rw [Finset.prod_eq_zero hit (indicator_of_notMem (show y i ∉ Iic (b i) from
          not_le.2 hi) _), zero_mul]
      · simp only [vertex, hit, ↓reduceIte] at hi
        rw [Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨Finset.mem_univ i, hit⟩)
          (indicator_of_notMem (show y i ∉ Iic (a i) from not_le.2 hi) _), mul_zero]
  rw [← hv]
  ring

theorem measurableSet_box (a b : Fin l → ℝ) : MeasurableSet (box a b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- (D3): `Σₜ (−1)^{l − |t|} F(a + θₜd) = λ((a, b])`. -/
theorem vertexSum_eq (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] {a b : Fin l → ℝ}
    (hab : a ≤ b) : vertexSum (distFun μ) a b = μ.real (box a b) := by
  rw [← integral_indicator_one (measurableSet_box a b)]
  simp_rw [box_indicator_eq hab]
  rw [integral_finsetSum _ fun t _ =>
    ((integrable_const 1).indicator measurableSet_Iic).const_mul _]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, integral_indicator_one measurableSet_Iic]
  rfl

theorem distFun_mono (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] : Monotone (distFun μ) :=
  fun _ _ hxy => measureReal_mono (Iic_subset_Iic.2 hxy)

/-- Continuity from above of `F`, as a squeeze along `ε ↓ 0`, given decreasing sets whose
measures converge. -/
theorem contFromAbove_distFun (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (x : Fin l → ℝ) : ContFromAbove (distFun μ) x := by
  set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (x + diag (1 / (n + 1)))
  have hanti : Antitone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
    simp only [Pi.add_apply, diag]
    gcongr
  have hinter : (⋂ n, A n) = Iic x := by
    ext y
    simp only [A, mem_iInter, mem_Iic, Pi.le_def, Pi.add_apply, diag]
    constructor
    · intro h i
      refine le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      linarith [h n i]
    · intro h n i
      linarith [h i, show (0 : ℝ) < 1 / (n + 1) by positivity]
  have hlim : Tendsto (fun n => μ.real (A n)) atTop (𝓝 (μ.real (Iic x))) := by
    have := tendsto_measure_iInter_atTop (μ := μ) (fun n => measurableSet_Iic.nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rw [hinter] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  rw [ContFromAbove, tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact lt_of_lt_of_le hc (distFun_mono μ fun i => by
      simp only [Pi.add_apply, diag]; linarith [show (0 : ℝ) < ε from hε])
  · obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hc)).exists
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (n + 1) by positivity)] with ε hε
    exact lt_of_le_of_lt (distFun_mono μ fun i => by
      simp only [Pi.add_apply, diag]; linarith [hε.2]) hn

/-- **Theorem 12.7a.** The distribution function of a probability measure on `ℝˡ` satisfies
(D1): it is nondecreasing, tends to `0` as any coordinate tends to `−∞` and to `1` as all
coordinates tend to `+∞`; (D2): it is continuous from above; and (D3): the alternating vertex
sum over any box is `λ((a, b]) ≥ 0`. -/
theorem theorem_12_7a (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] :
    (Monotone (distFun μ) ∧
      (∀ i, ∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, x i ≤ M → distFun μ x < ε) ∧
      (∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, (∀ i, M ≤ x i) → 1 - ε < distFun μ x)) ∧
      (∀ x, ContFromAbove (distFun μ) x) ∧
      ∀ a b, a ≤ b → vertexSum (distFun μ) a b = μ.real (box a b) ∧
        0 ≤ vertexSum (distFun μ) a b := by
  refine ⟨⟨distFun_mono μ, fun i ε hε => ?_, fun ε hε => ?_⟩, contFromAbove_distFun μ,
    fun a b hab => ⟨vertexSum_eq μ hab, vertexSum_eq μ hab ▸ measureReal_nonneg⟩⟩
  · -- the `i`-th marginal of `(−∞, −n]` tends to `0`
    set A : ℕ → Set (Fin l → ℝ) := fun n => {y | y i ≤ -n}
    have hanti : Antitone A := fun m n hmn y hy => by
      simp only [A, mem_ofPred_eq] at hy ⊢
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have hempty : (⋂ n, A n) = ∅ := by
      ext y
      simp only [A, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
        not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-y i)
      exact ⟨n, by linarith⟩
    have hlim := tendsto_measure_iInter_atTop (μ := μ)
      (fun n => (measurableSet_le (measurable_pi_apply i) measurable_const).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rw [hempty, measure_empty] at hlim
    have hlim' : Tendsto (fun n => μ.real (A n)) atTop (𝓝 0) := by
      simpa [Function.comp_def, Measure.real] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    obtain ⟨n, hn⟩ := (hlim'.eventually (gt_mem_nhds hε)).exists
    refine ⟨-n, fun x hx => lt_of_le_of_lt (measureReal_mono fun y hy => ?_) hn⟩
    exact (hy i).trans hx
  · -- the sets `(−∞, n1]` increase to `ℝˡ`
    set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (diag n)
    have hmono : Monotone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
      simp only [diag]; exact_mod_cast hmn
    have hunion : (⋃ n, A n) = univ := by
      refine eq_univ_of_forall fun y => mem_iUnion.2 ⟨⌈∑ j, |y j|⌉₊, fun i => ?_⟩
      simp only [diag]
      calc y i ≤ |y i| := le_abs_self _
        _ ≤ ∑ j, |y j| := Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)
        _ ≤ ⌈∑ j, |y j|⌉₊ := Nat.le_ceil _
    have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion, measure_univ] at hlim
    have hlim' : Tendsto (fun n => μ.real (A n)) atTop (𝓝 1) := by
      simpa [Function.comp_def, Measure.real] using
        (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim
    obtain ⟨n, hn⟩ := (hlim'.eventually (lt_mem_nhds (show 1 - ε < 1 by linarith))).exists
    exact ⟨n, fun x hx => lt_of_lt_of_le hn (distFun_mono μ fun i => hx i)⟩

/-- The sets `(−∞, x]` generate the Borel sets of `ℝˡ`. -/
theorem generateFrom_Iic_pi :
    MeasurableSpace.generateFrom (range fun x : Fin l → ℝ => Iic x) =
      (MeasurableSpace.pi : MeasurableSpace (Fin l → ℝ)) := by
  rw [← generateFrom_eq_pi (C := fun _ => range (Iic : ℝ → Set ℝ))
    (fun _ => (borel_eq_generateFrom_Iic ℝ).symm.trans BorelSpace.measurable_eq.symm)
    fun _ => ⟨fun n => Iic (n : ℝ), fun n => mem_range_self _,
      eq_univ_of_forall fun x => mem_iUnion.2 ⟨⌈x⌉₊, Nat.le_ceil x⟩⟩]
  congr 1
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun i => Iic (x i), fun i _ => ⟨x i, rfl⟩, (Iic_eq_pi x).symm⟩
  · rintro ⟨T, hT, rfl⟩
    choose x hx using fun i => hT i (mem_univ i)
    exact ⟨x, by change Iic x = _; rw [Iic_eq_pi]; congr 1; funext i; exact hx i⟩

/-- **Theorem 12.7b** (uniqueness). A probability measure on `ℝˡ` is determined by its
distribution function. -/
theorem distFun_injective {μ ν : Measure (Fin l → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : distFun μ = distFun ν) : μ = ν := by
  refine ext_of_generate_finite _ generateFrom_Iic_pi.symm ?_ ?_ (by simp)
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    exact ⟨x ⊓ y, Iic_inter_Iic.symm⟩
  · rintro _ ⟨x, rfl⟩
    have := congrFun h x
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- The open lower orthant `{y : y < x}` (all coordinates strictly smaller). -/
def lowerOpen (x : Fin l → ℝ) : Set (Fin l → ℝ) := Set.pi univ fun i => Iio (x i)

theorem frontier_Iic_eq (x : Fin l → ℝ) : frontier (Iic x) = Iic x \ lowerOpen x := by
  rw [frontier, isClosed_Iic.closure_eq, Iic_eq_pi, interior_pi_set finite_univ]
  simp_rw [interior_Iic]
  rfl

theorem lowerOpen_subset (x : Fin l → ℝ) : lowerOpen x ⊆ Iic x := fun _ hy i => (hy i trivial).le

/-- `F(x − ε1) → λ({y < x})` as `ε ↓ 0`. -/
theorem tendsto_distFun_below (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (x : Fin l → ℝ) :
    Tendsto (fun ε => distFun μ (x - diag ε)) (𝓝[>] 0) (𝓝 (μ.real (lowerOpen x))) := by
  set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (x - diag (1 / (n + 1)))
  have hmono : Monotone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
    simp only [Pi.sub_apply, diag]
    gcongr
  have hunion : (⋃ n, A n) = lowerOpen x := by
    ext y
    simp only [A, mem_iUnion, mem_Iic, Pi.le_def, Pi.sub_apply, diag, lowerOpen, Set.mem_pi,
      mem_univ, true_implies, mem_Iio]
    constructor
    · rintro ⟨n, hn⟩ i; linarith [hn i, show (0 : ℝ) < 1 / (n + 1) by positivity]
    · intro h
      choose N hN using fun i => exists_nat_one_div_lt (sub_pos.2 (h i))
      refine ⟨Finset.univ.sup N, fun i => ?_⟩
      have hle : (N i : ℝ) ≤ Finset.univ.sup N := by
        exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ i)
      have : 1 / ((Finset.univ.sup N : ℕ) + 1 : ℝ) ≤ 1 / (N i + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith [hN i]
  have hlim : Tendsto (fun n => μ.real (A n)) atTop (𝓝 (μ.real (lowerOpen x))) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hc)).exists
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (n + 1) by positivity)] with ε hε
    exact lt_of_lt_of_le hn (distFun_mono μ fun i => by
      simp only [Pi.sub_apply, diag]; linarith [hε.2])
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine lt_of_le_of_lt (measureReal_mono (s₂ := lowerOpen x) fun y hy i _ => ?_) hc
    have := hy i
    simp only [Pi.sub_apply, diag] at this
    exact lt_of_le_of_lt this (by linarith [show (0 : ℝ) < ε from hε])

/-- **Theorem 12.7c.** `F` is continuous from below at `x` iff the boundary of `(−∞, x]` is
`λ`-null. -/
theorem theorem_12_7c (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] (x : Fin l → ℝ) :
    ContFromBelow (distFun μ) x ↔ μ (frontier (Iic x)) = 0 := by
  have hdiff : μ.real (frontier (Iic x)) = distFun μ x - μ.real (lowerOpen x) := by
    rw [frontier_Iic_eq, measureReal_sdiff (lowerOpen_subset x)
      (MeasurableSet.univ_pi fun _ => measurableSet_Iio)]
    rfl
  have h0 : μ (frontier (Iic x)) = 0 ↔ μ.real (frontier (Iic x)) = 0 := by
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff]; simp [measure_ne_top]
  rw [h0, hdiff, sub_eq_zero]
  constructor
  · intro h
    exact tendsto_nhds_unique h (tendsto_distFun_below μ x)
  · intro h
    rw [ContFromBelow, h]
    exact tendsto_distFun_below μ x

/-- **Exercise 12.3.** A nondecreasing `F` that is continuous from above and from below at `x` is
continuous at `x`. -/
theorem ex_12_3 {F : (Fin l → ℝ) → ℝ} (hF : Monotone F) {x : Fin l → ℝ}
    (ha : ContFromAbove F x) (hb : ContFromBelow F x) : ContinuousAt F x := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨ε₁, hε₁, h1⟩ := (Metric.tendsto_nhdsWithin_nhds.1 ha) δ hδ
  obtain ⟨ε₂, hε₂, h2⟩ := (Metric.tendsto_nhdsWithin_nhds.1 hb) δ hδ
  set ε := min ε₁ ε₂ / 2
  have hε : 0 < ε := by positivity
  have hu := h1 (x := ε) (show ε ∈ Ioi 0 from hε) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; simp only [ε]
    linarith [min_le_left ε₁ ε₂, half_lt_self (lt_min hε₁ hε₂)])
  have hl := h2 (x := ε) (show ε ∈ Ioi 0 from hε) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; simp only [ε]
    linarith [min_le_right ε₁ ε₂, half_lt_self (lt_min hε₁ hε₂)])
  rw [Real.dist_eq] at hu hl
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  rw [Metric.mem_ball, dist_pi_lt_iff hε] at hy
  have hlo : x - diag ε ≤ y := fun i => by
    have := hy i; rw [Real.dist_eq, abs_lt] at this; simp only [Pi.sub_apply, diag]; linarith
  have hhi : y ≤ x + diag ε := fun i => by
    have := hy i; rw [Real.dist_eq, abs_lt] at this; simp only [Pi.add_apply, diag]; linarith
  have := hF hlo
  have := hF hhi
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at hu hl
  constructor <;> linarith

end StokeyLucasPrescott.WeakConvergence
