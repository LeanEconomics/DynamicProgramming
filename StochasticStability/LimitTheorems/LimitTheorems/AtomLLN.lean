/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.RegenerationCycles

/-!
# The ratio limit theorem for chains with an atom (MT §17.2.1)

Meyn and Tweedie, (17.10) and Theorem 17.2.1, pp. 428–429. `α` is an atom with `a ∈ α`,
`μ°_α = atomMeasure P hα a` is the invariant measure of the atom (10.10), and the atom is
recurrent, `L(a, α) = 1`.

* `cycleSumE`: the cycle functional with values in `[0, ∞]`.
* **(17.10)** (`lintegral_cycleSumE`, `integral_cycleSum`): the mean of a cycle sum is the
  `μ°_α`-integral, `E_ρ[Σ_{i ≤ σ_α} f(eᵢ)] = E_a[Σ_{k=1}^{τ_α} f(Φₖ)] = ∫ f dμ°_α`; and
  `integrable_cycleSum`: cycle sums of `μ°_α`-integrable functions are `ρ`-integrable.
* `tendsto_renewal_average`: along the visit times,
  `(1/(j + 1)) Σ_{i ≤ σ_α(j)} f(Φᵢ) → ∫ f dμ°_α`, `P_μ`-a.s.
* `tendsto_of_renewal_sandwich`: a deterministic sandwich between consecutive visit times.
* **Theorem 17.2.1** (`theorem_17_2_1`, p. 428): for `f, g ∈ L¹(μ°_α)` with `∫ g dμ°_α ≠ 0`,
  `Sₙ(f)/Sₙ(g) → ∫ f dμ°_α / ∫ g dμ°_α`, `P_μ`-a.s., for every initial law `μ` from which `α`
  is reached almost surely; `theorem_17_2_1_harris`: the book's form for a Harris chain with an
  atom in `B⁺(X)` and an invariant measure `π`, from every initial state.

The book's proof is followed: the sums are compared at consecutive visit times with sums of the
i.i.d. cycle variables (17.12), and the strong law is applied to these.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The mean of a cycle sum (17.10) -/

/-- The cycle functional `Σ_{i ≤ σ_α(e)} f(eᵢ)` with values in `[0, ∞]`. -/
noncomputable def cycleSumE (α : Set X) (f : X → ℝ≥0∞) (e : ℕ → X) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (hitNat α e + 1), f (e i)

/-- `cycleSumE` is measurable. -/
theorem measurable_cycleSumE {α : Set X} (hα : MeasurableSet α) {f : X → ℝ≥0∞}
    (hf : Measurable f) : Measurable (cycleSumE α f) := by
  have hF : Measurable fun p : (ℕ → X) × ℕ => ∑ i ∈ Finset.range (p.2 + 1), f (p.1 i) :=
    measurable_from_prod_countable_left fun n => by
      dsimp only
      exact Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i)
  exact hF.comp (measurable_id.prodMk (measurable_hitNat hα))

omit [MeasurableSpace X] in
/-- `ofReal ∘ cycleSum = cycleSumE ∘ ofReal` for `f ≥ 0`. -/
theorem ofReal_cycleSum {α : Set X} {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) (e : ℕ → X) :
    ENNReal.ofReal (cycleSum α f e) = cycleSumE α (fun x => ENNReal.ofReal (f x)) e := by
  rw [cycleSum, cycleSumE, ENNReal.ofReal_sum_of_nonneg fun i _ => hf _]

/-- The atom measure as a sum of laws: `∫ f dμ°_α = E_a[Σ_{n ≥ 0} 1{n + 1 ≤ τ_α} f(Φₙ₊₁)]`. -/
theorem lintegral_atomMeasure (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂atomMeasure P hα a = ∫⁻ ω, ∑' n : ℕ,
      {ω : ℕ → X | WithTop.some (n + 1) ≤ firstReturn α ω}.indicator
        (fun ω => f (ω (n + 1))) ω ∂pathKernel P a := by
  have := isMarkovKernel_pathKernel P
  have hS : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | WithTop.some (n + 1) ≤ firstReturn α ω} :=
    fun n => measurableSet_le_firstReturn hα (n + 1)
  set m : Measure X := Measure.sum fun n : ℕ =>
    ((pathKernel P a).restrict {ω | WithTop.some (n + 1) ≤ firstReturn α ω}).map
      (fun ω => ω (n + 1)) with hm
  have hmeq : atomMeasure P hα a = m := by
    ext B hB
    rw [atomMeasure, tabooPotKernel_eq_lintegral P hα a hB, hm, Measure.sum_apply _ hB,
      lintegral_tsum]
    swap
    · exact fun n => (measurable_one.indicator
        ((measurable_pi_apply (n + 1) hB).inter (hS n))).aemeasurable
    refine tsum_congr fun n => ?_
    rw [Measure.map_apply (measurable_pi_apply (n + 1)) hB, Measure.restrict_apply
      (measurable_pi_apply (n + 1) hB)]
    exact lintegral_indicator_one (s := {ω : ℕ → X | ω (n + 1) ∈ B} ∩
      {ω | WithTop.some (n + 1) ≤ firstReturn α ω})
      ((measurable_pi_apply (n + 1) hB).inter (hS n))
  rw [hmeq, hm, lintegral_sum_measure, lintegral_tsum]
  swap
  · exact fun n => ((hf.comp (measurable_pi_apply (n + 1))).indicator (hS n)).aemeasurable
  refine tsum_congr fun n => ?_
  rw [lintegral_map hf (measurable_pi_apply (n + 1)), lintegral_indicator (hS n)]

/-- If `L(a, α) = 1`, then `α` is reached almost surely from `ν = P(a, ·)`. -/
theorem ae_firstHit_ne_top_of_hitProb (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) {a : X} (hrec : hitProb P α a = 1) :
    ∀ᵐ ω ∂pathMeasure P (P a), firstHit α ω ≠ ⊤ := by
  have := isMarkovKernel_pathKernel P
  have hE : MeasurableSet {ω : ℕ → X | firstHit α ω ≠ ⊤} :=
    measurableSet_ne_top (isStoppingTime_firstHit hα)
  rw [← pathKernel_map_shift_one, ae_map_iff (measurable_shift 1).aemeasurable hE]
  have h1 : ∀ᵐ ω ∂pathKernel P a, firstReturn α ω ≠ ⊤ :=
    (mem_ae_iff_prob_eq_one (measurableSet_ne_top (proposition_3_4_4 hα).1)).2 hrec
  filter_upwards [h1] with ω hω
  rw [firstReturn_eq_firstHit_shift] at hω
  intro h
  rw [h] at hω
  exact hω rfl

/-- **(17.10)** in `[0, ∞]`: `E_ρ[Σ_{i ≤ σ_α} f(eᵢ)] = ∫ f dμ°_α`, for a recurrent atom. -/
theorem lintegral_cycleSumE (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (hrec : hitProb P α a = 1) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ e, cycleSumE α f e ∂cycleLaw P α a = ∫⁻ x, f x ∂atomMeasure P hα.1 a := by
  have := isMarkovKernel_pathKernel P
  rw [lintegral_atomMeasure P hα.1 a hf, cycleLaw,
    lintegral_map (measurable_cycleSumE hα.1 hf) (measurable_excursion hα.1),
    ← pathKernel_map_shift_one,
    lintegral_map (f := fun ω => cycleSumE α f (excursion α ω))
      ((measurable_cycleSumE hα.1 hf).comp (measurable_excursion hα.1)) (measurable_shift 1)]
  have h1 : ∀ᵐ ω ∂pathKernel P a, firstReturn α ω ≠ ⊤ :=
    (mem_ae_iff_prob_eq_one (measurableSet_ne_top (proposition_3_4_4 hα.1).1)).2 hrec
  refine lintegral_congr_ae ?_
  filter_upwards [h1] with ω hω
  have hτ := firstReturn_eq_firstHit_shift α ω
  have hne : firstHit α (shift 1 ω) ≠ ⊤ := by
    intro h; rw [h] at hτ; exact hω (by rw [hτ]; rfl)
  have hσ := firstHit_eq_hitNat hne
  rw [cycleSumE, hitNat_excursion]
  set s := hitNat α (shift 1 ω) with hs
  rw [tsum_eq_sum (s := Finset.range (s + 1))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    have hle : WithTop.some (n + 1) ≤ firstReturn α ω := by
      rw [hτ, hσ]
      rw [← WithTop.coe_one, ← WithTop.coe_add]
      exact WithTop.coe_le_coe.2 (by omega)
    rw [indicator_of_mem (show ω ∈ {ω : ℕ → X | WithTop.some (n + 1) ≤ firstReturn α ω}
      from hle), excursion_apply_of_le_hitNat hn']
    simp [shift, add_comm]
  · intro n hn
    have hn' : s < n := by simpa using hn
    have hnot : ¬ WithTop.some (n + 1) ≤ firstReturn α ω := by
      rw [hτ, hσ]
      intro h
      have : n + 1 ≤ s + 1 := by
        rw [← WithTop.coe_one, ← WithTop.coe_add] at h
        exact WithTop.coe_le_coe.1 h
      omega
    rw [indicator_of_notMem (show ω ∉ {ω : ℕ → X | WithTop.some (n + 1) ≤ firstReturn α ω}
      from hnot)]

omit [MeasurableSpace X] in
/-- `|cycleSum f| ≤ cycleSum |f|`. -/
theorem abs_cycleSum_le (α : Set X) (f : X → ℝ) (e : ℕ → X) :
    |cycleSum α f e| ≤ cycleSum α (fun x => |f x|) e :=
  Finset.abs_sum_le_sum_abs _ _

/-- Cycle sums of a `μ°_α`-integrable function are `ρ`-integrable. -/
theorem integrable_cycleSum (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (hrec : hitProb P α a = 1) {f : X → ℝ} (hfm : Measurable f)
    (hfi : Integrable f (atomMeasure P hα.1 a)) : Integrable (cycleSum α f) (cycleLaw P α a) := by
  refine ⟨(measurable_cycleSum hα.1 hfm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ e, ENNReal.ofReal ‖cycleSum α f e‖ ∂cycleLaw P α a
      ≤ ∫⁻ e, ENNReal.ofReal (cycleSum α (fun x => |f x|) e) ∂cycleLaw P α a :=
        lintegral_mono fun e => ENNReal.ofReal_le_ofReal (by
          rw [Real.norm_eq_abs]; exact abs_cycleSum_le α f e)
    _ = ∫⁻ e, cycleSumE α (fun x => ENNReal.ofReal |f x|) e ∂cycleLaw P α a := by
        simp_rw [ofReal_cycleSum (fun x => abs_nonneg (f x))]
    _ = ∫⁻ x, ENNReal.ofReal |f x| ∂atomMeasure P hα.1 a :=
        lintegral_cycleSumE P hα hrec (measurable_abs_of_measurable hfm).ennreal_ofReal
    _ < ∞ := by
        have := hfi.2
        rw [hasFiniteIntegral_iff_norm] at this
        simpa [Real.norm_eq_abs] using this

omit [MeasurableSpace X] in
/-- `cycleSum (f − g) = cycleSum f − cycleSum g`. -/
theorem cycleSum_sub (α : Set X) (f g : X → ℝ) (e : ℕ → X) :
    cycleSum α (fun x => f x - g x) e = cycleSum α f e - cycleSum α g e := by
  simp [cycleSum, Finset.sum_sub_distrib]

/-- For `f ≥ 0`, `E_ρ[cycleSum f] = ∫ f dμ°_α` (real form). -/
theorem integral_cycleSum_of_nonneg (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (hrec : hitProb P α a = 1) {f : X → ℝ} (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∫ e, cycleSum α f e ∂cycleLaw P α a = ∫ x, f x ∂atomMeasure P hα.1 a := by
  have h0 : ∀ e, 0 ≤ cycleSum α f e := fun e => Finset.sum_nonneg fun i _ => hf0 _
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0)
      (measurable_cycleSum hα.1 hfm).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfm.aestronglyMeasurable]
  simp_rw [ofReal_cycleSum hf0]
  rw [lintegral_cycleSumE P hα hrec hfm.ennreal_ofReal]

/-- **(17.10)**: `E_ρ[Σ_{i ≤ σ_α} f(eᵢ)] = ∫ f dμ°_α` for `f ∈ L¹(μ°_α)`. -/
theorem integral_cycleSum (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (hrec : hitProb P α a = 1) {f : X → ℝ} (hfm : Measurable f)
    (hfi : Integrable f (atomMeasure P hα.1 a)) :
    ∫ e, cycleSum α f e ∂cycleLaw P α a = ∫ x, f x ∂atomMeasure P hα.1 a := by
  have hp : Measurable fun x => max (f x) 0 := hfm.max measurable_const
  have hn : Measurable fun x => max (-f x) 0 := hfm.neg.max measurable_const
  have hpi : Integrable (fun x => max (f x) 0) (atomMeasure P hα.1 a) := hfi.pos_part
  have hni : Integrable (fun x => max (-f x) 0) (atomMeasure P hα.1 a) := hfi.neg_part
  have hdec : f = fun x => max (f x) 0 - max (-f x) 0 := by
    ext x; rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hcs : cycleSum α f = fun e => cycleSum α (fun x => max (f x) 0) e -
      cycleSum α (fun x => max (-f x) 0) e := by
    ext e; rw [← cycleSum_sub]; congr 1
  rw [hcs, integral_sub (integrable_cycleSum P hα hrec hp hpi)
    (integrable_cycleSum P hα hrec hn hni),
    integral_cycleSum_of_nonneg P hα hrec hp fun x => le_max_right _ _,
    integral_cycleSum_of_nonneg P hα hrec hn fun x => le_max_right _ _,
    ← integral_sub hpi hni]
  conv_rhs => rw [hdec]

/-! ### The strong law along the visit times -/

/-- Along the visit times, `(1/(j + 1)) Σ_{i ≤ σ_α(j)} f(Φᵢ) → ∫ f dμ°_α`, `P_μ`-a.s. -/
theorem tendsto_renewal_average (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (hrec : hitProb P α a = 1) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤) {f : X → ℝ}
    (hfm : Measurable f) (hfi : Integrable f (atomMeasure P hα.1 a)) :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun j : ℕ =>
      (∑ i ∈ Finset.range (renewalTime α j ω + 1), f (ω i)) / ((j : ℝ) + 1)) atTop
      (𝓝 (∫ x, f x ∂atomMeasure P hα.1 a)) := by
  have hν := ae_firstHit_ne_top_of_hitProb P hα.1 hrec
  have hsl := tendsto_cycle_average P hα ha hν μ hμ (measurable_cycleSum hα.1 hfm)
    (integrable_cycleSum P hα hrec hfm hfi)
  rw [integral_cycleSum P hα hrec hfm hfi] at hsl
  filter_upwards [hsl] with ω hω
  set m := ∫ x, f x ∂atomMeasure P hα.1 a
  set c := fun i => cycleSum α f (cycle α i ω) with hc
  -- `(c₀ + Σ_{i<j} cᵢ₊₁)/(j + 1) → m`
  have h1 : Tendsto (fun j : ℕ => (∑ i ∈ Finset.range j, c (i + 1)) / ((j : ℝ) + 1)) atTop
      (𝓝 m) := by
    have h2 : Tendsto (fun j : ℕ => (j : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 1) := by
      have : Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
      rw [sub_zero] at this
      refine this.congr fun j => ?_
      have : (j : ℝ) + 1 ≠ 0 := by positivity
      field_simp; ring
    have := hω.mul h2
    rw [mul_one] at this
    refine this.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    have : (j : ℝ) + 1 ≠ 0 := by positivity
    simp only [hc]
    field_simp
  have h3 : Tendsto (fun j : ℕ => c 0 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h4 := h3.add h1
  rw [zero_add] at h4
  refine h4.congr fun j => ?_
  rw [sum_range_renewalTime, Finset.sum_range_succ', add_div, add_comm]

/-! ### A sandwich between visit times -/

omit [MeasurableSpace X] in
/-- If `T` is strictly increasing and `u n` lies between `lo j` and `hi j` whenever
`T j ≤ n < T (j + 1)` (for all large `j`), and `lo j, hi j → L`, then `u n → L`. -/
theorem tendsto_of_renewal_sandwich {T : ℕ → ℕ} (hT : StrictMono T) {u lo hi : ℕ → ℝ} {L : ℝ}
    (hsand : ∀ᶠ j in atTop, ∀ n, T j ≤ n → n < T (j + 1) → lo j ≤ u n ∧ u n ≤ hi j)
    (hlo : Tendsto lo atTop (𝓝 L)) (hhi : Tendsto hi atTop (𝓝 L)) :
    Tendsto u atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at hlo hhi ⊢
  intro ε hε
  obtain ⟨J₁, hJ₁⟩ := hlo ε hε
  obtain ⟨J₂, hJ₂⟩ := hhi ε hε
  obtain ⟨J₃, hJ₃⟩ := eventually_atTop.1 hsand
  set J := max J₁ (max J₂ J₃)
  refine ⟨T J, fun n hn => ?_⟩
  have hTid : ∀ j, j ≤ T j := hT.id_le
  -- the index of the last visit at or before `n`
  classical
  set j := Nat.findGreatest (fun j => T j ≤ n) n with hj
  have hJn : J ≤ n := (hTid J).trans hn
  have hJj : J ≤ j := Nat.le_findGreatest hJn hn
  have hTj : T j ≤ n := Nat.findGreatest_spec (P := fun j => T j ≤ n) hJn hn
  have hTj1 : n < T (j + 1) := by
    by_contra h
    push Not at h
    have hle : j + 1 ≤ n := (hTid (j + 1)).trans h
    exact Nat.findGreatest_is_greatest (P := fun j => T j ≤ n) (Nat.lt_succ_self j) hle h
  obtain ⟨h1, h2⟩ := hJ₃ j (le_of_max_le_right (le_of_max_le_right hJj)) n hTj hTj1
  have hl := hJ₁ j (le_of_max_le_left hJj)
  have hh := hJ₂ j (le_of_max_le_left (le_of_max_le_right hJj))
  rw [Real.dist_eq, abs_lt] at hl hh ⊢
  constructor <;> linarith

/-! ### The ratio limit theorem -/

omit [MeasurableSpace X] in
/-- Partial sums of a nonnegative function are monotone in the upper limit. -/
theorem sum_range_mono_of_nonneg {g : X → ℝ} (hg0 : ∀ x, 0 ≤ g x) (ω : ℕ → X) {m n : ℕ}
    (hmn : m ≤ n) :
    ∑ i ∈ Finset.range (m + 1), g (ω i) ≤ ∑ i ∈ Finset.range (n + 1), g (ω i) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    fun i _ _ => hg0 _

omit [MeasurableSpace X] in
/-- The ratio form along visit times, deterministic part: if along the visit times
`Aₜⱼ/(j + 1) → a` and `Bₜⱼ/(j + 1) → b > 0` for nonnegative summands, then `Aₙ/Bₙ → a/b`. -/
theorem tendsto_ratio_of_renewal {T : ℕ → ℕ} (hT : StrictMono T) {f g : X → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) {ω : ℕ → X} {a b : ℝ} (hb : 0 < b)
    (hA : Tendsto (fun j : ℕ => (∑ i ∈ Finset.range (T j + 1), f (ω i)) / ((j : ℝ) + 1)) atTop
      (𝓝 a))
    (hB : Tendsto (fun j : ℕ => (∑ i ∈ Finset.range (T j + 1), g (ω i)) / ((j : ℝ) + 1)) atTop
      (𝓝 b)) :
    Tendsto (fun n => (∑ i ∈ Finset.range (n + 1), f (ω i)) /
      (∑ i ∈ Finset.range (n + 1), g (ω i))) atTop (𝓝 (a / b)) := by
  set A := fun n => ∑ i ∈ Finset.range (n + 1), f (ω i) with hAdef
  set B := fun n => ∑ i ∈ Finset.range (n + 1), g (ω i) with hBdef
  have hshift : Tendsto (fun j : ℕ => ((j : ℝ) + 1) / ((j : ℝ) + 2)) atTop (𝓝 1) := by
    have : Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 2)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
    rw [sub_zero] at this
    refine this.congr fun j => ?_
    have : (j : ℝ) + 2 ≠ 0 := by positivity
    field_simp; ring
  have hA1 : Tendsto (fun j : ℕ => A (T (j + 1)) / ((j : ℝ) + 2)) atTop (𝓝 a) := by
    have := hA.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun j => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, hAdef]
    ring_nf
  have hB1 : Tendsto (fun j : ℕ => B (T (j + 1)) / ((j : ℝ) + 2)) atTop (𝓝 b) := by
    have := hB.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun j => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, hBdef]
    ring_nf
  -- lower and upper bounds
  have hlo : Tendsto (fun j => A (T j) / B (T (j + 1))) atTop (𝓝 (a / b)) := by
    have h := (hA.div hB1 hb.ne').mul hshift
    rw [mul_one] at h
    refine h.congr' (eventually_atTop.2 ⟨0, fun j _ => ?_⟩)
    simp only [Pi.div_apply, hAdef, hBdef]
    have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
    rcases eq_or_ne (∑ i ∈ Finset.range (T (j + 1) + 1), g (ω i)) 0 with hB0 | hB0
    · rw [hB0]; simp
    · field_simp
  have hhi : Tendsto (fun j => A (T (j + 1)) / B (T j)) atTop (𝓝 (a / b)) := by
    have hinv : Tendsto (fun j : ℕ => ((j : ℝ) + 2) / ((j : ℝ) + 1)) atTop (𝓝 1) := by
      have := hshift.inv₀ one_ne_zero
      rw [inv_one] at this
      refine this.congr fun j => ?_
      rw [inv_div]
    have h := (hA1.div hB hb.ne').mul hinv
    rw [mul_one] at h
    refine h.congr' (eventually_atTop.2 ⟨0, fun j _ => ?_⟩)
    simp only [Pi.div_apply, hAdef, hBdef]
    have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
    rcases eq_or_ne (∑ i ∈ Finset.range (T j + 1), g (ω i)) 0 with hB0 | hB0
    · rw [hB0]; simp
    · field_simp
  -- eventually `B(Tⱼ) > 0`
  have hBpos : ∀ᶠ j in atTop, 0 < B (T j) := by
    have := hB.eventually (eventually_gt_nhds hb)
    filter_upwards [this] with j hj
    have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    exact (div_pos_iff_of_pos_right h1).1 hj
  refine tendsto_of_renewal_sandwich hT ?_ hlo hhi
  filter_upwards [hBpos] with j hj n hn1 hn2
  have hAlo := sum_range_mono_of_nonneg hf0 ω hn1
  have hAhi := sum_range_mono_of_nonneg hf0 ω hn2.le
  have hBlo := sum_range_mono_of_nonneg hg0 ω hn1
  have hBhi := sum_range_mono_of_nonneg hg0 ω hn2.le
  have hA0 : 0 ≤ A (T j) := Finset.sum_nonneg fun i _ => hf0 _
  have hBn : 0 < B n := lt_of_lt_of_le hj hBlo
  constructor
  · exact div_le_div₀ (hA0.trans hAlo) hAlo hBn hBhi
  · exact div_le_div₀ (hA0.trans (hAlo.trans hAhi)) hAhi hj hBlo

/-- The ratio limit theorem for nonnegative functions: `Aₙ(f)/Aₙ(g) → μ°(f)/μ°(g)`, where
`Aₙ = Σ_{i ≤ n}`. -/
theorem tendsto_ratio_of_nonneg (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (hrec : hitProb P α a = 1) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤) {f g : X → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : Integrable f (atomMeasure P hα.1 a)) (hgi : Integrable g (atomMeasure P hα.1 a))
    (hgpos : 0 < ∫ x, g x ∂atomMeasure P hα.1 a) :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n => (∑ i ∈ Finset.range (n + 1), f (ω i)) /
      (∑ i ∈ Finset.range (n + 1), g (ω i))) atTop
      (𝓝 ((∫ x, f x ∂atomMeasure P hα.1 a) / ∫ x, g x ∂atomMeasure P hα.1 a)) := by
  filter_upwards [tendsto_renewal_average P hα ha hrec μ hμ hfm hfi,
    tendsto_renewal_average P hα ha hrec μ hμ hgm hgi] with ω hf hg
  exact tendsto_ratio_of_renewal (strictMono_nat_of_lt_succ fun j => renewalTime_lt_succ α j ω)
    hf0 hg0 hgpos hf hg

omit [MeasurableSpace X] in
/-- `Sₙ(f) = Aₙ(f) − f(Φ₀)`. -/
theorem pathSum_eq_sum_range_sub (f : X → ℝ) (n : ℕ) (ω : ℕ → X) :
    pathSum f n ω = ∑ i ∈ Finset.range (n + 1), f (ω i) - f (ω 0) := by
  rw [pathSum, Finset.sum_range_succ']; ring

omit [MeasurableSpace X] in
/-- `σ_α ≤ τ_α`. -/
theorem firstHit_le_firstReturn (α : Set X) (ω : ℕ → X) : firstHit α ω ≤ firstReturn α ω :=
  hittingAfter_apply_mono (fun n (ω : ℕ → X) => ω n) α ω (Nat.zero_le 1)

/-- If `L(x, α) = 1`, then `α` is hit `P_x`-a.s. -/
theorem ae_firstHit_ne_top_of_hitProb_eq_one (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) {x : X} (h : hitProb P α x = 1) :
    ∀ᵐ ω ∂pathKernel P x, firstHit α ω ≠ ⊤ := by
  have := isMarkovKernel_pathKernel P
  have h1 : ∀ᵐ ω ∂pathKernel P x, firstReturn α ω ≠ ⊤ :=
    (mem_ae_iff_prob_eq_one (measurableSet_ne_top (proposition_3_4_4 hα).1)).2 h
  filter_upwards [h1] with ω hω
  exact ne_top_of_le_ne_top hω (firstHit_le_firstReturn α ω)

/-- **Theorem 17.2.1** (MT p. 428, ratio form of the LLN): for a recurrent atom `α ∋ a`, an
initial law `μ` from which `α` is reached a.s., and `f, g ∈ L¹(μ°_α)` with `∫ g dμ°_α ≠ 0`,
`Sₙ(f)/Sₙ(g) → ∫ f dμ°_α / ∫ g dμ°_α`, `P_μ`-a.s. -/
theorem theorem_17_2_1 (P : Kernel X X) [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {a : X} (ha : a ∈ α) (hrec : hitProb P α a = 1) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤) {f g : X → ℝ} (hfm : Measurable f)
    (hgm : Measurable g) (hfi : Integrable f (atomMeasure P hα.1 a))
    (hgi : Integrable g (atomMeasure P hα.1 a)) (hg : ∫ x, g x ∂atomMeasure P hα.1 a ≠ 0) :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n => pathSum f n ω / pathSum g n ω) atTop
      (𝓝 ((∫ x, f x ∂atomMeasure P hα.1 a) / ∫ x, g x ∂atomMeasure P hα.1 a)) := by
  -- the reference function `h = 1_α`, with `μ°_α(h) = L(a, α) = 1`
  set h : X → ℝ := α.indicator 1 with hh
  have hhm : Measurable h := measurable_one.indicator hα.1
  have hh0 : ∀ x, 0 ≤ h x := fun x => indicator_nonneg (fun _ _ => zero_le_one) x
  have hαfin : atomMeasure P hα.1 a α = 1 := by rw [atomMeasure_self, hrec]
  have hhi : Integrable h (atomMeasure P hα.1 a) := by
    refine (integrable_indicator_iff hα.1).2 ?_
    exact integrableOn_const (by rw [hαfin]; exact ENNReal.one_ne_top)
  have hhint : ∫ x, h x ∂atomMeasure P hα.1 a = 1 := by
    rw [hh, integral_indicator_one hα.1, Measure.real, hαfin, ENNReal.toReal_one]
  -- ratios against `Aₙ(h)` for every integrable `u`
  have hratio : ∀ u : X → ℝ, Measurable u → Integrable u (atomMeasure P hα.1 a) →
      ∀ᵐ ω ∂pathMeasure P μ,
      Tendsto (fun n => (∑ i ∈ Finset.range (n + 1), u (ω i)) /
        (∑ i ∈ Finset.range (n + 1), h (ω i))) atTop (𝓝 (∫ x, u x ∂atomMeasure P hα.1 a)) := by
    intro u hum hui
    have hpm : Measurable fun x => max (u x) 0 := hum.max measurable_const
    have hnm : Measurable fun x => max (-u x) 0 := hum.neg.max measurable_const
    have hp := tendsto_ratio_of_nonneg P hα ha hrec μ hμ (f := fun x => max (u x) 0) hpm hhm
      (fun x => le_max_right _ _) hh0 hui.pos_part hhi (by rw [hhint]; exact one_pos)
    have hn := tendsto_ratio_of_nonneg P hα ha hrec μ hμ (f := fun x => max (-u x) 0) hnm hhm
      (fun x => le_max_right _ _) hh0 hui.neg_part hhi (by rw [hhint]; exact one_pos)
    filter_upwards [hp, hn] with ω h1 h2
    have h3 := h1.sub h2
    rw [hhint, div_one, div_one, ← integral_sub hui.pos_part hui.neg_part] at h3
    have hdec : (fun x => max (u x) 0 - max (-u x) 0) = u := by
      ext x; rcases le_total 0 (u x) with hx | hx
      · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
    rw [hdec] at h3
    refine h3.congr fun n => ?_
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total 0 (u (ω i)) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
  -- `Aₙ(h) → ∞`
  have hinf : ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), h (ω i))
      atTop atTop := by
    filter_upwards [tendsto_renewal_average P hα ha hrec μ hμ hhm hhi] with ω hω
    rw [hhint] at hω
    have hmono : Monotone fun n => ∑ i ∈ Finset.range (n + 1), h (ω i) :=
      fun m n hmn => sum_range_mono_of_nonneg hh0 ω hmn
    refine tendsto_atTop_atTop_of_monotone hmono fun M => ?_
    have hev := hω.eventually (eventually_gt_nhds (show (1 : ℝ) / 2 < 1 by norm_num))
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
    obtain ⟨j, hj⟩ := exists_nat_ge (2 * |M|)
    refine ⟨renewalTime α (max J j) ω, ?_⟩
    have h1 := hJ (max J j) (le_max_left _ _)
    have hpos : (0 : ℝ) < (max J j : ℕ) + 1 := by positivity
    rw [lt_div_iff₀ hpos] at h1
    have hjj : (j : ℝ) ≤ (max J j : ℕ) := by exact_mod_cast le_max_right J j
    have := le_abs_self M
    linarith
  filter_upwards [hratio f hfm hfi, hratio g hgm hgi, hinf] with ω h1 h2 h3
  -- `Sₙ(u)/Aₙ(h) → μ°(u)`
  have hS : ∀ u : X → ℝ, Tendsto (fun n => (∑ i ∈ Finset.range (n + 1), u (ω i)) /
      (∑ i ∈ Finset.range (n + 1), h (ω i))) atTop (𝓝 (∫ x, u x ∂atomMeasure P hα.1 a)) →
      Tendsto (fun n => pathSum u n ω / ∑ i ∈ Finset.range (n + 1), h (ω i)) atTop
        (𝓝 (∫ x, u x ∂atomMeasure P hα.1 a)) := by
    intro u hu
    have h4 : Tendsto (fun n => u (ω 0) / ∑ i ∈ Finset.range (n + 1), h (ω i)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h3
    have := hu.sub h4
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    rw [pathSum_eq_sum_range_sub, sub_div]
  have h5 := (hS f h1).div (hS g h2) hg
  refine h5.congr' ?_
  filter_upwards [h3.eventually_gt_atTop 0] with n hn
  rw [Pi.div_apply, div_div_div_cancel_right₀ hn.ne']

/-- **Theorem 17.2.1**, the book's form (MT p. 428): for a Harris chain with an accessible atom
`α ∋ a`, an invariant measure `π` with `0 < π(α) < ∞`, and `f, g ∈ L¹(π)` with `π(g) ≠ 0`,
`Sₙ(f)/Sₙ(g) → π(f)/π(g)`, `P_x`-a.s., for every initial state `x`. -/
theorem theorem_17_2_1_harris [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ) {α : Set X}
    (hacc : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) {π : Measure X} (hπ : IsInvariant P π)
    (hπ0 : π α ≠ 0) (hπtop : π α ≠ ∞) {f g : X → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hfi : Integrable f π) (hgi : Integrable g π) (hg : ∫ x, g x ∂π ≠ 0) (x : X) :
    ∀ᵐ ω ∂pathKernel P x, Tendsto (fun n => pathSum f n ω / pathSum g n ω) atTop
      (𝓝 ((∫ y, f y ∂π) / ∫ y, g y ∂π)) := by
  have := isMarkovKernel_pathKernel P
  have hrec := hH.isRecurrentChain
  have hπeq := theorem_10_2_1_ii_smul hacc hrec ha (le_of_eq hπ) hπ0 hπtop
  have hhit : ∀ y, hitProb P α y = 1 := fun y =>
    le_antisymm (hitProb_le_one P α y) (by
      rw [← theorem_9_1_4 hH hacc.1.1 hacc.2.2 y]; exact harrisQ_le_hitProb P α y)
  set c := π α with hc
  have hc0 : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hπ0, hπtop⟩
  have hfi' : Integrable f (atomMeasure P hacc.1.1 a) := by
    rw [hπeq] at hfi; exact (integrable_smul_measure hπ0 hπtop).1 hfi
  have hgi' : Integrable g (atomMeasure P hacc.1.1 a) := by
    rw [hπeq] at hgi; exact (integrable_smul_measure hπ0 hπtop).1 hgi
  have hint : ∀ u : X → ℝ, ∫ y, u y ∂π = c.toReal * ∫ y, u y ∂atomMeasure P hacc.1.1 a := by
    intro u; conv_lhs => rw [hπeq]
    rw [integral_smul_measure, smul_eq_mul]
  have hg' : ∫ y, g y ∂atomMeasure P hacc.1.1 a ≠ 0 := by
    intro h0; apply hg; rw [hint, h0, mul_zero]
  have h := theorem_17_2_1 P hacc.1 ha (hhit a) (Measure.dirac x) (by
      rw [pathMeasure_dirac]; exact ae_firstHit_ne_top_of_hitProb_eq_one P hacc.1.1 (hhit x))
    hfm hgm hfi' hgi' hg'
  rw [pathMeasure_dirac] at h
  rw [hint f, hint g, mul_div_mul_left _ _ hc0]
  exact h

end MeynTweedie.LimitTheorems
