/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.FellerInvariant

/-!
# Monotone Markov processes (SLP §12.4, pp. 378–383)

* **dominance** `μ ≥ λ` (p. 378): `⟨f, μ⟩ ≥ ⟨f, λ⟩` for all bounded measurable nondecreasing `f`;
* **Exercise 12.9**: dominance orders distribution functions the other way (`ex_12_9a`); on `ℝ`
  the converse holds (`ex_12_9b`, via the layer-cake formula and the classification of lower
  sets of `ℝ`); on `ℝ²` it fails (`ex_12_9c`, `μ = ½(δ_{(1,0)} + δ_{(0,1)})`,
  `λ = ½(δ_{(0,0)} + δ_{(1,1)})`);
* **Exercise 12.10**: squeezing between dominance-ordered weakly convergent sequences (for any
  `S ⊆ ℝˡ`, not only rectangles);
* **Exercise 12.11**: `P` monotone ⇔ `T*` preserves dominance ⇔ `s ≥ s′ ⇒ P(s, ·) ≥ P(s′, ·)`;
* monotone sequences of measures on `[a, b]` converge weakly (`convWeak_of_dominance_mono`, from
  Corollary 2 to Helly);
* **Exercise 12.12**: `T*ⁿδ_a` increases and `T*ⁿδ_b` decreases, and both converge to invariant
  measures;
* **Assumption 12.1**, **Exercise 12.14**, **Lemma 12.11** and **Theorem 12.12** (a monotone Feller
  process satisfying the mixing condition has a unique invariant measure, which is globally
  stable). The proof of Theorem 12.12 supplies the two steps the book leaves implicit: the lower
  bound `(Tⁿf)(b) - (Tⁿf)(a) ≥ 0`, and uniqueness from global convergence.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

/-! ### Dominance -/

variable {S : Type*} [MeasurableSpace S] [Preorder S]

/-- `μ` **dominates** `λ` (SLP p. 378): `⟨f, μ⟩ ≥ ⟨f, λ⟩` for every bounded measurable
nondecreasing `f`. -/
def Dominates (μ lam : Measure S) : Prop :=
  ∀ f : S → ℝ, Measurable f → (∃ M, ∀ s, |f s| ≤ M) → Monotone f → ∫ s, f s ∂lam ≤ ∫ s, f s ∂μ

theorem Dominates.trans {μ ν lam : Measure S} (h1 : Dominates μ ν) (h2 : Dominates ν lam) :
    Dominates μ lam := fun f hf hb hm => (h2 f hf hb hm).trans (h1 f hf hb hm)

/-- Dominance compares the masses of measurable upper sets. -/
theorem Dominates.real_le {μ lam : Measure S} (h : Dominates μ lam) {U : Set S}
    (hU : MeasurableSet U) (hup : IsUpperSet U) : lam.real U ≤ μ.real U := by
  have hm : Monotone (U.indicator (1 : S → ℝ)) := fun s t hst => by
    by_cases hs : s ∈ U
    · simp [hs, hup hst hs]
    · rw [indicator_of_notMem hs]; exact indicator_nonneg (fun _ _ => zero_le_one) t
  have := h (U.indicator 1) (measurable_const.indicator hU) ⟨1, fun s => by
    by_cases hs : s ∈ U
    · rw [indicator_of_mem hs, Pi.one_apply, abs_one]
    · rw [indicator_of_notMem hs, abs_zero]; exact zero_le_one⟩ hm
  rwa [integral_indicator_one hU, integral_indicator_one hU] at this

variable {l : ℕ}

/-- **Exercise 12.9a.** If `μ ≥ λ` on `ℝˡ` then `F_μ ≤ F_λ`. -/
theorem ex_12_9a {μ lam : Measure (Fin l → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure lam] (h : Dominates μ lam) (x : Fin l → ℝ) :
    distFun μ x ≤ distFun lam x := by
  have := h.real_le measurableSet_Iic.compl (isLowerSet_Iic x).compl
  rw [probReal_compl_eq_one_sub measurableSet_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    at this
  simp only [distFun]; linarith

/-- **Exercise 12.9a** on `S ⊆ ℝˡ`: if `μ ≥ λ` then `μ(S ∩ (-∞, x]) ≤ λ(S ∩ (-∞, x])` for every
`x ∈ ℝˡ`. -/
theorem ex_12_9a_subtype {S : Set (Fin l → ℝ)} {μ lam : Measure S} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure lam] (h : Dominates μ lam) (x : Fin l → ℝ) :
    μ.real (Subtype.val ⁻¹' Iic x) ≤ lam.real (Subtype.val ⁻¹' Iic x) := by
  have hm : MeasurableSet (Subtype.val ⁻¹' Iic x : Set S) :=
    measurableSet_Iic.preimage measurable_subtype_coe
  have := h.real_le hm.compl (fun s t (hst : (s : Fin l → ℝ) ≤ t) hs ht => hs (hst.trans ht))
  rw [probReal_compl_eq_one_sub hm, probReal_compl_eq_one_sub hm] at this
  linarith

/-- On `ℝ`, `F_μ ≤ F_λ` gives `μ(L) ≤ λ(L)` for every lower set `L`: `L` is `∅`, `ℝ`,
`(-∞, c]` or `(-∞, c)`. -/
theorem measure_lower_le {μ lam : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : ∀ x, μ.real (Iic x) ≤ lam.real (Iic x)) {L : Set ℝ} (hL : IsLowerSet L) :
    μ L ≤ lam L := by
  have hE : ∀ x, μ (Iic x) ≤ lam (Iic x) := fun x =>
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 (h x)
  rcases L.eq_empty_or_nonempty with rfl | hne
  · simp
  by_cases hbdd : BddAbove L
  · by_cases hc : sSup L ∈ L
    · have : L = Iic (sSup L) :=
        Subset.antisymm (fun y hy => le_csSup hbdd hy) (fun y hy => hL hy hc)
      rw [this]; exact hE _
    · have hLc : L = ⋃ n : ℕ, Iic (sSup L - 1 / ((n : ℝ) + 1)) := by
        ext y
        simp only [mem_iUnion, mem_Iic]
        constructor
        · intro hy
          have hlt : y < sSup L := lt_of_le_of_ne (le_csSup hbdd hy) fun h => hc (h ▸ hy)
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
          exact ⟨n, by linarith⟩
        · rintro ⟨n, hn⟩
          have := Nat.one_div_pos_of_nat (α := ℝ) (n := n)
          obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne (show y < sSup L by linarith)
          exact hL hyz.le hz
      have hmono : Monotone fun n : ℕ => Iic (sSup L - 1 / ((n : ℝ) + 1)) := fun m n hmn =>
        Iic_subset_Iic.2 (sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
          (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
              linarith)) _)
      rw [hLc]
      exact le_of_tendsto_of_tendsto' (tendsto_measure_iUnion_atTop hmono)
        (tendsto_measure_iUnion_atTop hmono) fun n => hE _
  · have : L = univ := eq_univ_of_forall fun y => by
      obtain ⟨z, hz, hyz⟩ := not_bddAbove_iff.1 hbdd y
      exact hL hyz.le hz
    rw [this, measure_univ, measure_univ]

/-- **Exercise 12.9b.** On `ℝ`, `F_μ ≤ F_λ` implies `μ ≥ λ`. -/
theorem ex_12_9b (μ lam : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : ∀ x, μ.real (Iic x) ≤ lam.real (Iic x)) : Dominates μ lam := by
  intro f hf ⟨M, hM⟩ hmono
  set g := fun s => f s + M
  have hg0 : ∀ s, 0 ≤ g s := fun s => by
    have := hM s; rw [abs_le] at this; simp only [g]; linarith
  have hgM : ∀ s, |g s| ≤ 2 * M := fun s => by
    have := hM s; rw [abs_le] at this
    rw [abs_of_nonneg (hg0 s)]; simp only [g]; linarith
  have hgm : Measurable g := hf.add_const M
  have hshift : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], ∫ s, f s ∂ν = ∫ s, g s ∂ν - M :=
    fun ν _ => by
      simp only [g]
      rw [integral_add (integrable_of_bounded hf hM) (integrable_const M), integral_const,
        probReal_univ, one_smul]
      ring
  have hlc : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      ∫ s, g s ∂ν = (∫⁻ t in Ioi 0, ν {s | t < g s}).toReal := fun ν _ => by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgm.aestronglyMeasurable,
      lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hg0) hgm.aemeasurable]
  have hup : ∀ t, IsUpperSet {s | t < g s} := fun t s s' hss' (hs : t < g s) =>
    show t < g s' from lt_of_lt_of_le hs (add_le_add_left (hmono hss') M)
  have hle : ∀ t, lam {s | t < g s} ≤ μ {s | t < g s} := fun t => by
    have hmeas : MeasurableSet {s | t < g s} := measurableSet_lt measurable_const hgm
    have := measure_lower_le h (hup t).compl
    have h1 := (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 this
    rw [← measureReal_def, ← measureReal_def, probReal_compl_eq_one_sub hmeas,
      probReal_compl_eq_one_sub hmeas] at h1
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 (by
      rw [← measureReal_def, ← measureReal_def]; linarith)
  have hfin : ∫⁻ t in Ioi 0, μ {s | t < g s} ≠ ⊤ := by
    rw [← lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hg0) hgm.aemeasurable]
    exact (integrable_of_bounded hgm hgM (μ := μ)).lintegral_lt_top.ne
  rw [hshift lam, hshift μ, hlc lam, hlc μ]
  linarith [ENNReal.toReal_mono hfin (lintegral_mono hle)]

/-- The mass of a measurable set under `½(δ_p + δ_q)`. -/
theorem real_half_dirac {α : Type*} [MeasurableSpace α] (p q : α) {A : Set α}
    (hA : MeasurableSet A) :
    ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac p + Measure.dirac q)).real A =
      (A.indicator (1 : α → ℝ) p + A.indicator (1 : α → ℝ) q) / 2 := by
  rw [measureReal_def, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' p hA,
    Measure.dirac_apply' q hA, smul_eq_mul]
  by_cases hp : p ∈ A <;> by_cases hq : q ∈ A <;>
    simp [hp, hq, ENNReal.toReal_inv, ENNReal.toReal_add]
  all_goals norm_num

/-- **Exercise 12.9c.** On `ℝ²` the converse of Exercise 12.9a fails:
`μ = ½(δ_{(1,0)} + δ_{(0,1)})` and `λ = ½(δ_{(0,0)} + δ_{(1,1)})` have `F_μ ≤ F_λ`, but the
nondecreasing indicator of `{x ≥ (1, 1)}` integrates to `0` under `μ` and to `½` under `λ`. -/
theorem ex_12_9c :
    let μ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (![1, 0] : Fin 2 → ℝ) + Measure.dirac ![0, 1])
    let lam := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (![0, 0] : Fin 2 → ℝ) + Measure.dirac ![1, 1])
    (∀ x, distFun μ x ≤ distFun lam x) ∧ ¬ Dominates μ lam := by
  intro μ lam
  have hle : ∀ (a b : ℝ) (x : Fin 2 → ℝ), (![a, b] : Fin 2 → ℝ) ≤ x ↔ a ≤ x 0 ∧ b ≤ x 1 :=
    fun a b x => by simp [Pi.le_def, Fin.forall_fin_two]
  have hle2 : ∀ a b c d : ℝ, (![a, b] : Fin 2 → ℝ) ≤ ![c, d] ↔ a ≤ c ∧ b ≤ d :=
    fun a b c d => by simp [Pi.le_def, Fin.forall_fin_two]
  refine ⟨fun x => ?_, fun h => ?_⟩
  · have i1 : ∀ p : Fin 2 → ℝ, 0 ≤ (Iic x).indicator (1 : (Fin 2 → ℝ) → ℝ) p := fun p =>
      indicator_nonneg (fun _ _ => zero_le_one) p
    have hA : (![1, 0] : Fin 2 → ℝ) ∈ Iic x → (![0, 0] : Fin 2 → ℝ) ∈ Iic x := fun h => by
      rw [mem_Iic, hle] at h ⊢; exact ⟨by linarith [h.1], h.2⟩
    have hB : (![0, 1] : Fin 2 → ℝ) ∈ Iic x → (![0, 0] : Fin 2 → ℝ) ∈ Iic x := fun h => by
      rw [mem_Iic, hle] at h ⊢; exact ⟨h.1, by linarith [h.2]⟩
    have hC : (![1, 0] : Fin 2 → ℝ) ∈ Iic x → (![0, 1] : Fin 2 → ℝ) ∈ Iic x →
        (![1, 1] : Fin 2 → ℝ) ∈ Iic x := fun h h' => by
      rw [mem_Iic, hle] at h h' ⊢; exact ⟨h.1, h'.2⟩
    simp only [distFun, μ, lam, real_half_dirac _ _ measurableSet_Iic]
    by_cases h1 : (![1, 0] : Fin 2 → ℝ) ∈ Iic x <;> by_cases h2 : (![0, 1] : Fin 2 → ℝ) ∈ Iic x
    · simp only [indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem (hA h1),
        indicator_of_mem (hC h1 h2), Pi.one_apply, le_refl]
    · simp only [indicator_of_mem h1, indicator_of_notMem h2, indicator_of_mem (hA h1),
        Pi.one_apply]
      linarith [i1 ![1, 1]]
    · simp only [indicator_of_notMem h1, indicator_of_mem h2, indicator_of_mem (hB h2),
        Pi.one_apply]
      linarith [i1 ![1, 1]]
    · simp only [indicator_of_notMem h1, indicator_of_notMem h2]
      linarith [i1 ![0, 0], i1 ![1, 1]]
  · have hU : MeasurableSet (Ici (![1, 1] : Fin 2 → ℝ)) := measurableSet_Ici
    have := h.real_le hU (isUpperSet_Ici _)
    have n00 : (![0, 0] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.1]
    have n10 : (![1, 0] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.2]
    have n01 : (![0, 1] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.1]
    have m11 : (![1, 1] : Fin 2 → ℝ) ∈ Ici ![1, 1] := mem_Ici.2 le_rfl
    simp only [μ, lam, real_half_dirac _ _ hU, indicator_of_notMem n00, indicator_of_notMem n10,
      indicator_of_notMem n01, indicator_of_mem m11, Pi.one_apply] at this
    linarith

/-! ### Exercise 12.10 -/

theorem distFun_map_val {S : Set (Fin l → ℝ)} (ν : Measure S) (x : Fin l → ℝ) :
    distFun (ν.map Subtype.val) x = ν.real (Subtype.val ⁻¹' Iic x) := by
  rw [distFun, measureReal_def, Measure.map_apply measurable_subtype_coe measurableSet_Iic]; rfl

/-- **Exercise 12.10.** If `μ₁ₙ ≤ λₙ ≤ μ₂ₙ` and `μ₁ₙ ⇒ μ`, `μ₂ₙ ⇒ μ`, then `λₙ ⇒ μ`. (The book
states it for `S = [a, b]`; the argument through Exercise 12.4 and Theorem 12.8 works for any
`S ⊆ ℝˡ`.) -/
theorem ex_12_10 {S : Set (Fin l → ℝ)} (μ₁ μ₂ ls : ℕ → Measure S) (μ : Measure S)
    [∀ n, IsProbabilityMeasure (μ₁ n)] [∀ n, IsProbabilityMeasure (μ₂ n)]
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ]
    (h₁ : ∀ n, Dominates (ls n) (μ₁ n)) (h₂ : ∀ n, Dominates (μ₂ n) (ls n))
    (hc₁ : ConvWeak μ₁ μ) (hc₂ : ConvWeak μ₂ μ) : ConvWeak ls μ := by
  rw [ex_12_4, theorem_12_8] at hc₁ hc₂ ⊢
  intro x hx
  have e1 := hc₁ x hx
  have e2 := hc₂ x hx
  simp only [distFun_map_val] at e1 e2 ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le e2 e1
    (fun n => ex_12_9a_subtype (h₂ n) x) (fun n => ex_12_9a_subtype (h₁ n) x)

/-! ### Exercise 12.11 and iterates -/

variable (κ : Kernel S S) [IsMarkovKernel κ]

/-- **Exercise 12.11.** The following are equivalent: (a) `P` is monotone; (b) `μ ≥ λ` implies
`T*μ ≥ T*λ`; (c) `s ≥ s′` implies `P(s, ·) ≥ P(s′, ·)`. -/
theorem ex_12_11 :
    (IsMonotoneTF κ ↔ ∀ (μ lam : Measure S), IsProbabilityMeasure μ → IsProbabilityMeasure lam →
      Dominates μ lam → Dominates (adjointOp κ μ) (adjointOp κ lam)) ∧
    (IsMonotoneTF κ ↔ ∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s')) := by
  have hab : IsMonotoneTF κ → ∀ (μ lam : Measure S), IsProbabilityMeasure μ →
      IsProbabilityMeasure lam → Dominates μ lam →
        Dominates (adjointOp κ μ) (adjointOp κ lam) := fun hM μ lam _ _ h f hf hb hm => by
    obtain ⟨M, hMb⟩ := hb
    rw [← theorem_8_3_cor κ lam hf hMb, ← theorem_8_3_cor κ μ hf hMb]
    have := theorem_8_1_cor κ hf hMb
    exact h _ this.1 ⟨M, this.2⟩ (hM f hf ⟨M, hMb⟩ hm)
  have hbc : (∀ (μ lam : Measure S), IsProbabilityMeasure μ → IsProbabilityMeasure lam →
      Dominates μ lam → Dominates (adjointOp κ μ) (adjointOp κ lam)) →
        ∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s') := fun h s s' hss' => by
    have := h (Measure.dirac s) (Measure.dirac s') inferInstance inferInstance
      (fun f hf _ hm => by
        rw [integral_dirac' f s' hf.stronglyMeasurable, integral_dirac' f s hf.stronglyMeasurable]
        exact hm hss')
    rwa [adjointOp_dirac, adjointOp_dirac] at this
  have hca : (∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s')) → IsMonotoneTF κ :=
    fun h f hf hb hm s' s hss' => h s s' hss' f hf hb hm
  exact ⟨⟨hab, fun h => hca (hbc h)⟩, ⟨fun h => hbc (hab h), hca⟩⟩

omit [Preorder S] [IsMarkovKernel κ] in
theorem markovOpR_kpow_zero {f : S → ℝ} (hf : Measurable f) : markovOpR (kpow κ 0) f = f := by
  funext s
  simp only [markovOpR, kpow, Kernel.id_apply]
  exact integral_dirac' f s hf.stronglyMeasurable

omit [Preorder S] in
/-- `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` for bounded measurable `f`. -/
theorem markovOpR_kpow_add (n m : ℕ) {f : S → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ s, |f s| ≤ M) :
    markovOpR (kpow κ (n + m)) f = markovOpR (kpow κ n) (markovOpR (kpow κ m) f) := by
  have := ex_8_4a κ m
  have := ex_8_4a κ n
  funext s
  rw [kpow_add]
  exact Kernel.integral_comp (integrable_of_bounded hf hM)

/-- The iterates of a monotone transition function are monotone. -/
theorem isMonotoneTF_kpow {κ : Kernel S S} [IsMarkovKernel κ] (hM : IsMonotoneTF κ) (n : ℕ) :
    IsMonotoneTF (kpow κ n) := by
  induction n with
  | zero => intro f hf _ hm; rw [markovOpR_kpow_zero κ hf]; exact hm
  | succ n ih =>
    intro f hf ⟨M, hb⟩ hm
    have := ex_8_4a κ n
    rw [add_comm, markovOpR_kpow_add κ 1 n hf hb, kpow_one]
    have := theorem_8_1_cor (kpow κ n) hf hb
    exact hM _ this.1 ⟨M, this.2⟩ (ih f hf ⟨M, hb⟩ hm)

omit [Preorder S] [IsMarkovKernel κ] in
theorem iterate_dirac (n : ℕ) (s : S) :
    (adjointOp κ)^[n] (Measure.dirac s) = kpow κ n s := by
  rw [adjointOp_iterate, adjointOp_dirac]

/-- `T*ⁿ` preserves dominance for monotone `P`. -/
theorem dominates_iterate {κ : Kernel S S} [IsMarkovKernel κ] (hM : IsMonotoneTF κ)
    {μ lam : Measure S} [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : Dominates μ lam) (n : ℕ) :
    Dominates ((adjointOp κ)^[n] μ) ((adjointOp κ)^[n] lam) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (ex_12_11 κ).1.1 hM _ _ (isProbabilityMeasure_iterate μ n)
      (isProbabilityMeasure_iterate lam n) ih

/-! ### Monotone processes on `[a, b]` -/

variable {a b : Fin l → ℝ}

/-- The bottom `a` of `[a, b]`. -/
def IccBot (hab : a ≤ b) : Icc a b := ⟨a, left_mem_Icc.2 hab⟩

/-- The top `b` of `[a, b]`. -/
def IccTop (hab : a ≤ b) : Icc a b := ⟨b, right_mem_Icc.2 hab⟩

theorem IccBot_le (hab : a ≤ b) (s : Icc a b) : IccBot hab ≤ s := s.2.1

theorem le_IccTop (hab : a ≤ b) (s : Icc a b) : s ≤ IccTop hab := s.2.2

/-- Every probability measure dominates `δ_a` and is dominated by `δ_b`. -/
theorem dominates_dirac_bot_top (hab : a ≤ b) (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] :
    Dominates ν (Measure.dirac (IccBot hab)) ∧ Dominates (Measure.dirac (IccTop hab)) ν := by
  refine ⟨fun f hf ⟨M, hM⟩ hm => ?_, fun f hf ⟨M, hM⟩ hm => ?_⟩
  · rw [integral_dirac]
    have := integral_mono (integrable_const (f (IccBot hab))) (integrable_of_bounded hf hM (μ := ν))
      fun s => hm (IccBot_le hab s)
    rwa [integral_const, probReal_univ, one_smul] at this
  · rw [integral_dirac]
    have := integral_mono (integrable_of_bounded hf hM (μ := ν))
      (integrable_const (f (IccTop hab))) fun s => hm (le_IccTop hab s)
    rwa [integral_const, probReal_univ, one_smul] at this

/-- A probability measure on `ℝˡ` concentrated on `[a, b]` is the extension of a probability
measure on `[a, b]`. -/
theorem exists_subtype_measure (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (h : μ (Icc a b) = 1) :
    ∃ ν : Measure (Icc a b), IsProbabilityMeasure ν ∧ ν.map Subtype.val = μ := by
  have hmap : (μ.comap Subtype.val).map (Subtype.val : Icc a b → Fin l → ℝ) = μ := by
    rw [map_comap_subtype_coe measurableSet_Icc]
    exact Measure.restrict_eq_self_of_ae_mem
      (mem_ae_iff.2 ((prob_compl_eq_zero_iff measurableSet_Icc).2 h))
  refine ⟨μ.comap Subtype.val, ?_, hmap⟩
  have : IsProbabilityMeasure ((μ.comap Subtype.val).map (Subtype.val : Icc a b → Fin l → ℝ)) := by
    rw [hmap]; infer_instance
  exact (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).1 this

theorem map_val_Icc (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] :
    ν.map Subtype.val (Icc a b) = 1 := by
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc]
  have : (Subtype.val ⁻¹' Icc a b : Set (Icc a b)) = univ := eq_univ_of_forall fun s => s.2
  rw [this, measure_univ]

/-- A **monotone sequence of measures** on `[a, b]` (SLP p. 379) converges weakly (Corollary 2 to
Helly, through Exercise 12.9a and Exercise 12.4). -/
theorem convWeak_of_dominance_mono (ν : ℕ → Measure (Icc a b)) [∀ n, IsProbabilityMeasure (ν n)]
    (hmono : (∀ n, Dominates (ν (n + 1)) (ν n)) ∨ (∀ n, Dominates (ν n) (ν (n + 1)))) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ ConvWeak ν μ := by
  obtain ⟨μ', hμ', hab', hconv⟩ := theorem_12_9_cor2 (a := a) (b := b)
    (fun n => (ν n).map Subtype.val) (fun n => map_val_Icc (ν n)) (by
      rcases hmono with h | h
      · exact Or.inl fun n => Pi.le_def.2 fun x => by
          rw [distFun_map_val, distFun_map_val]; exact ex_12_9a_subtype (h n) x
      · exact Or.inr fun n => Pi.le_def.2 fun x => by
          rw [distFun_map_val, distFun_map_val]; exact ex_12_9a_subtype (h n) x)
  obtain ⟨μ, hμ, hmap⟩ := exists_subtype_measure μ' hab'
  refine ⟨μ, hμ, (ex_12_4 ν μ).2 ?_⟩
  rw [hmap]; exact hconv

/-- **Exercise 12.12.** For monotone Feller `P` on `[a, b]`, `T*ⁿδ_a` is increasing and `T*ⁿδ_b`
decreasing, and each converges weakly to an invariant measure. -/
theorem ex_12_12 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) (hF : IsFeller κ) :
    (∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac (IccBot hab)))
      ((adjointOp κ)^[n] (Measure.dirac (IccBot hab)))) ∧
    (∀ n, Dominates ((adjointOp κ)^[n] (Measure.dirac (IccTop hab)))
      ((adjointOp κ)^[n + 1] (Measure.dirac (IccTop hab)))) ∧
    (∃ μ, IsProbabilityMeasure μ ∧
      ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac (IccBot hab))) μ ∧
      adjointOp κ μ = μ) ∧
    (∃ μ, IsProbabilityMeasure μ ∧
      ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac (IccTop hab))) μ ∧
      adjointOp κ μ = μ) := by
  have hP : ∀ (lam : Measure (Icc a b)) [IsProbabilityMeasure lam],
      IsProbabilityMeasure (adjointOp κ lam) := fun lam _ => (theorem_8_2 κ lam).1
  have hbot : ∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac (IccBot hab)))
      ((adjointOp κ)^[n] (Measure.dirac (IccBot hab))) := fun n => by
    rw [Function.iterate_succ_apply]
    exact dominates_iterate hM (dominates_dirac_bot_top hab _).1 n
  have htop : ∀ n, Dominates ((adjointOp κ)^[n] (Measure.dirac (IccTop hab)))
      ((adjointOp κ)^[n + 1] (Measure.dirac (IccTop hab))) := fun n => by
    rw [Function.iterate_succ_apply]
    exact dominates_iterate hM (dominates_dirac_bot_top hab _).2 n
  have hlim : ∀ s : Icc a b, ((∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac s))
      ((adjointOp κ)^[n] (Measure.dirac s))) ∨ (∀ n, Dominates ((adjointOp κ)^[n]
        (Measure.dirac s)) ((adjointOp κ)^[n + 1] (Measure.dirac s)))) →
      ∃ μ, IsProbabilityMeasure μ ∧
        ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac s)) μ ∧ adjointOp κ μ = μ :=
    fun s hs => by
      have : ∀ n, IsProbabilityMeasure ((adjointOp κ)^[n] (Measure.dirac s)) := fun n =>
        isProbabilityMeasure_iterate _ n
      obtain ⟨μ, hμ, hconv⟩ := convWeak_of_dominance_mono _ hs
      refine ⟨μ, hμ, hconv, invariant_of_convWeak hF hconv fun f => ?_⟩
      have := (hconv f).sub ((hconv f).comp (tendsto_add_atTop_nat 1))
      rw [sub_self] at this
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Function.iterate_succ_apply']
  exact ⟨hbot, htop, hlim _ (Or.inl hbot), hlim _ (Or.inr htop)⟩

/-! ### Assumption 12.1, Exercise 12.14, Lemma 12.11 and Theorem 12.12 -/

/-- **Assumption 12.1.** There are `c ∈ [a, b]`, `ε > 0` and `N ≥ 1` with `Pᴺ(a, [c, b]) ≥ ε`
and `Pᴺ(b, [a, c]) ≥ ε`. -/
def Assumption12_1 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) (c : Icc a b) (ε : ℝ)
    (N : ℕ) : Prop :=
  0 < ε ∧ 1 ≤ N ∧ ε ≤ (kpow κ N (IccBot hab)).real (Ici c) ∧
    ε ≤ (kpow κ N (IccTop hab)).real (Iic c)

/-- **Exercise 12.14.** Under monotonicity, Assumption 12.1 holds from every starting point:
`Pᴺ(s, [a, c]) ≥ ε` and `Pᴺ(s, [c, b]) ≥ ε`. -/
theorem ex_12_14 {hab : a ≤ b} {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) {c : Icc a b} {ε : ℝ} {N : ℕ} (hA : Assumption12_1 hab κ c ε N)
    (s : Icc a b) : ε ≤ (kpow κ N s).real (Iic c) ∧ ε ≤ (kpow κ N s).real (Ici c) := by
  have := ex_8_4a κ N
  have hdom := (ex_12_11 (kpow κ N)).2.1 (isMonotoneTF_kpow hM N)
  refine ⟨?_, hA.2.2.1.trans ((hdom s _ (IccBot_le hab s)).real_le measurableSet_Ici
    (isUpperSet_Ici c))⟩
  have := (hdom _ s (le_IccTop hab s)).real_le measurableSet_Iic.compl (isLowerSet_Iic c).compl
  rw [probReal_compl_eq_one_sub measurableSet_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    at this
  linarith [hA.2.2.2]

/-- **Lemma 12.11.** Under monotonicity and Assumption 12.1, for bounded measurable
nondecreasing `f`: `εf(c) + (1 - ε)f(a) ≤ (Tᴺf)(s) ≤ εf(c) + (1 - ε)f(b)`. -/
theorem lemma_12_11 {hab : a ≤ b} {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) {c : Icc a b} {ε : ℝ} {N : ℕ} (hA : Assumption12_1 hab κ c ε N)
    {f : Icc a b → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ s, |f s| ≤ M) (hm : Monotone f)
    (s : Icc a b) :
    ε * f c + (1 - ε) * f (IccBot hab) ≤ markovOpR (kpow κ N) f s ∧
      markovOpR (kpow κ N) f s ≤ ε * f c + (1 - ε) * f (IccTop hab) := by
  have := ex_8_4a κ N
  obtain ⟨hp, hq⟩ := ex_12_14 hM hA s
  set ν := kpow κ N s
  have hfi : Integrable f ν := integrable_of_bounded hf hb
  have hI : ∀ (A : Set (Icc a b)), MeasurableSet A → Integrable (A.indicator (1 : Icc a b → ℝ)) ν :=
    fun A hA => by exact (integrable_const (1 : ℝ)).indicator hA
  constructor
  · have hle : ∀ t, f (IccBot hab) + (f c - f (IccBot hab)) * (Ici c).indicator 1 t ≤ f t :=
      fun t => by
        by_cases ht : t ∈ Ici c
        · simp only [indicator_of_mem ht, Pi.one_apply, mul_one]; linarith [hm ht]
        · simp only [indicator_of_notMem ht, mul_zero, add_zero]; exact hm (IccBot_le hab t)
    have := integral_mono ((integrable_const _).add ((hI _ measurableSet_Ici).const_mul _)) hfi hle
    simp only [Pi.add_apply] at this
    rw [integral_add (integrable_const _) ((hI _ measurableSet_Ici).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_one measurableSet_Ici] at this
    have hca : f (IccBot hab) ≤ f c := hm (IccBot_le hab c)
    change _ ≤ ∫ t, f t ∂ν
    nlinarith
  · have hle : ∀ t, f t ≤ f (IccTop hab) - (f (IccTop hab) - f c) * (Iic c).indicator 1 t :=
      fun t => by
        by_cases ht : t ∈ Iic c
        · simp only [indicator_of_mem ht, Pi.one_apply, mul_one]; linarith [hm ht]
        · simp only [indicator_of_notMem ht, mul_zero, sub_zero]; exact hm (le_IccTop hab t)
    have := integral_mono hfi ((integrable_const _).sub ((hI _ measurableSet_Iic).const_mul _)) hle
    simp only [Pi.sub_apply] at this
    rw [integral_sub (integrable_const _) ((hI _ measurableSet_Iic).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_one measurableSet_Iic] at this
    have hcb : f c ≤ f (IccTop hab) := hm (le_IccTop hab c)
    change ∫ t, f t ∂ν ≤ _
    nlinarith

/-- **Theorem 12.12.** On `[a, b]`, a monotone Feller transition function satisfying Assumption
12.1 has a unique invariant probability measure `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem theorem_12_12 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) (hF : IsFeller κ) {c : Icc a b} {ε : ℝ} {N : ℕ}
    (hA : Assumption12_1 hab κ c ε N) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      (∀ ν : Measure (Icc a b), IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μ := by
  obtain ⟨-, -, ⟨μa, hμa, hca, hia⟩, ⟨μb, hμb, hcb, hib⟩⟩ := ex_12_12 hab κ hM hF
  set lo := IccBot hab
  set hi := IccTop hab
  have hε1 : ε ≤ 1 := by
    have := ex_8_4a κ N
    exact hA.2.2.1.trans measureReal_le_one
  -- the limits along `Tⁿf` at the two ends
  have hT : ∀ (s : Icc a b) (f : Icc a b →ᵇ ℝ) (n : ℕ),
      ∫ t, f t ∂(adjointOp κ)^[n] (Measure.dirac s) = markovOpR (kpow κ n) f s :=
    fun s f n => by rw [iterate_dirac]; rfl
  have heq : μa = μb := by
    refine ex_12_5b μa μb fun f hfm => ?_
    have hfb := bcf_abs_le_norm f
    have hfmeas := f.continuous.measurable
    set d : ℕ → ℝ := fun n => markovOpR (kpow κ n) f hi - markovOpR (kpow κ n) f lo
    have hdlim : Tendsto d atTop (𝓝 (∫ t, f t ∂μb - ∫ t, f t ∂μa)) := by
      have h1 := hcb f; have h2 := hca f
      simp only [hT] at h1 h2
      exact h1.sub h2
    have hd0 : ∀ n, 0 ≤ d n := fun n => sub_nonneg.2
      (isMonotoneTF_kpow hM n f hfmeas ⟨_, hfb⟩ hfm (IccBot_le hab hi))
    have hdN : ∀ m, d (N * m) ≤ (1 - ε) ^ m * (f hi - f lo) := fun m => by
      induction m with
      | zero =>
        simp only [d, mul_zero, pow_zero, one_mul, markovOpR_kpow_zero κ hfmeas]; rfl
      | succ m ih =>
        have := ex_8_4a κ (N * m)
        have hg := theorem_8_1_cor (kpow κ (N * m)) hfmeas hfb
        have hgm := isMonotoneTF_kpow hM (N * m) f hfmeas ⟨_, hfb⟩ hfm
        have hsplit : markovOpR (kpow κ (N * (m + 1))) f =
            markovOpR (kpow κ N) (markovOpR (kpow κ (N * m)) f) := by
          rw [show N * (m + 1) = N + N * m by ring, markovOpR_kpow_add κ N (N * m) hfmeas hfb]
        have hup := (lemma_12_11 hM hA hg.1 hg.2 hgm hi).2
        have hlo := (lemma_12_11 hM hA hg.1 hg.2 hgm lo).1
        simp only [d, hsplit]
        have h1ε : 0 ≤ 1 - ε := by linarith
        calc _ ≤ (1 - ε) * d (N * m) := by simp only [d]; linarith
          _ ≤ (1 - ε) * ((1 - ε) ^ m * (f hi - f lo)) := mul_le_mul_of_nonneg_left ih h1ε
          _ = _ := by ring
    have hNm : Tendsto (fun m => N * m) atTop atTop :=
      tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hA.2.1) tendsto_id
    have hup : ∫ t, f t ∂μb - ∫ t, f t ∂μa ≤ 0 := by
      have hbound : Tendsto (fun m : ℕ => (1 - ε) ^ m * (f hi - f lo)) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith [hA.1])
          ).mul_const (f hi - f lo)
      exact le_of_tendsto_of_tendsto' (hdlim.comp hNm) hbound hdN
    have hlow : 0 ≤ ∫ t, f t ∂μb - ∫ t, f t ∂μa := ge_of_tendsto' hdlim hd0
    linarith
  subst heq
  have hglob : ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
      ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μa := fun lam₀ _ => by
    have : ∀ (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] n,
        IsProbabilityMeasure ((adjointOp κ)^[n] ν) := fun ν _ n => isProbabilityMeasure_iterate ν n
    exact ex_12_10 (fun n => (adjointOp κ)^[n] (Measure.dirac lo))
      (fun n => (adjointOp κ)^[n] (Measure.dirac hi)) (fun n => (adjointOp κ)^[n] lam₀) μa
      (fun n => dominates_iterate hM (dominates_dirac_bot_top hab lam₀).1 n)
      (fun n => dominates_iterate hM (dominates_dirac_bot_top hab lam₀).2 n) hca hcb
  refine ⟨μa, hμa, hia, fun ν _ hν => ?_, hglob⟩
  have hconst : ConvWeak (fun n => (adjointOp κ)^[n] ν) ν := fun f => by
    simp only [Function.iterate_fixed hν]; exact tendsto_const_nhds
  have : ∀ n, IsProbabilityMeasure ((adjointOp κ)^[n] ν) := fun n =>
    isProbabilityMeasure_iterate ν n
  exact convWeak_unique hconst (hglob ν inferInstance)

end StokeyLucasPrescott.ConvergenceApplications
