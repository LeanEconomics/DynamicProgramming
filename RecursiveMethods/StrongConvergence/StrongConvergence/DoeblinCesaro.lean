/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.DoeblinExistence
import StrongConvergence.MeanErgodicL2

/-!
# Theorems 11.9b–c and 11.10b–c

The book states these and refers to Doob (1953, §V.5) and Neveu (1965, §V.3) for proofs. The
proof here combines the preceding modules.

1. Measures absolutely continuous with respect to an invariant probability measure `π` have
   uniformly Cauchy Cesàro averages (`cesaroCauchy_of_absCont`): truncate the density and use
   the mean ergodic theorem for bounded densities.
2. Every finite measure concentrated on an ergodic set `E` does
   (`cesaroCauchy_of_concentrated`). By the Lebesgue decomposition with respect to `φ`,
   `μPᴺ = K + R` with `K ≪ φ` (hence `K ≪ π_E`) and `R` singular. Doeblin's condition applied
   to a `φ`-null set carrying `R` gives `R(S) ≤ (1 − ε)μ(S)`. Iterating, `μP^{Nj}` is a good
   measure plus one of mass at most `(1 − ε)ʲμ(S)`.
3. **Absorption** (`tendsto_kpow_transient`): from every state the probability of being in the
   transient set `F = (⋃ₘ Eₘ)ᶜ` tends to `0`. The limit `g = lim Pⁿ(·, F)` is harmonic; if
   `γ = sup g > 0`, the set `{g = γ}` is invariant with `φ`-measure at least `ε`. So it contains
   an ergodic set, which must agree with some `Eₘ`, where `g = 0`.
4. Hence every finite measure has uniformly Cauchy averages, which gives Theorem 11.9b; part (c)
   and Theorem 11.10b–c follow from uniqueness on each ergodic set (`invariant_unique`).
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ]

/-! ### Absolutely continuous measures -/

/-- Truncations `min f n` of a function increase to it. -/
theorem iSup_min_natCast (x : ℝ≥0∞) : ⨆ n : ℕ, min x (n : ℝ≥0∞) = x := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp only [min_eq_right le_top]
    exact le_of_eq ENNReal.iSup_natCast.symm
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    exact le_iSup_of_le n (le_of_eq (min_eq_left hn.le).symm)

/-- **Step 1.** A finite measure absolutely continuous with respect to an invariant probability
measure has uniformly Cauchy Cesàro averages. -/
theorem cesaroCauchy_of_absCont {π : Measure S} [IsProbabilityMeasure π]
    (hπ : adjointOp κ π = π) {ν : Measure S} [IsFiniteMeasure ν] (hν : ν ≪ π) :
    CesaroCauchy κ ν := by
  set f := ν.rnDeriv π
  have hfm : Measurable f := Measure.measurable_rnDeriv ν π
  have hνf : π.withDensity f = ν := Measure.withDensity_rnDeriv_eq ν π hν
  have hint : ∫⁻ s, f s ∂π ≠ ⊤ := by
    have : (π.withDensity f) univ = ∫⁻ s, f s ∂π := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← this, hνf]
    exact measure_ne_top ν univ
  -- the truncations converge in mass
  have htend : Tendsto (fun n : ℕ => ∫⁻ s, min (f s) n ∂π) atTop (𝓝 (∫⁻ s, f s ∂π)) := by
    have hmono : Monotone fun (n : ℕ) (s : S) => min (f s) (n : ℝ≥0∞) := fun m n hmn s =>
      min_le_min_left _ (by exact_mod_cast hmn)
    have := lintegral_iSup (μ := π) (fun n => hfm.min measurable_const) hmono
    simp only [iSup_min_natCast] at this
    rw [this]
    exact tendsto_atTop_iSup fun m n hmn => lintegral_mono fun s =>
      min_le_min_left _ (by exact_mod_cast hmn)
  refine cesaroCauchy_of_approx fun η hη => ?_
  have hev := (ENNReal.tendsto_toReal hint).comp htend
  obtain ⟨n, hn⟩ := ((hev.const_sub (∫⁻ s, f s ∂π).toReal).eventually
    (gt_mem_nhds (show (∫⁻ s, f s ∂π).toReal - (∫⁻ s, f s ∂π).toReal < η by
      rw [sub_self]; exact hη))).exists
  simp only [Function.comp_apply] at hn
  -- the bounded part and the remainder
  set H : S → ℝ≥0 := fun s => (min (f s) n).toNNReal
  have hH : Measurable H := (hfm.min measurable_const).ennreal_toNNReal
  have hHb : ∀ s, H s ≤ n := fun s => by
    simp only [H]
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ne_top_of_le_ne_top
      (ENNReal.natCast_ne_top n) (min_le_right _ _))]
    exact_mod_cast min_le_right _ _
  have hHf : ∀ s, (H s : ℝ≥0∞) = min (f s) n := fun s =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _))
  set ν' := π.withDensity fun s => (H s : ℝ≥0∞)
  set ρ := π.withDensity fun s => f s - min (f s) n
  have hν'fin : IsFiniteMeasure ν' := isFiniteMeasure_withDensity_of_bound hHb
  have hsplit : ν = ν' + ρ := by
    rw [← hνf]
    simp only [ν', ρ, hHf]
    rw [← withDensity_add_left (hfm.min measurable_const)]
    congr 1
    funext s
    exact (add_tsub_cancel_of_le (min_le_left _ _)).symm
  have hρu : ρ univ = ∫⁻ s, f s ∂π - ∫⁻ s, min (f s) n ∂π := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_sub (hfm.min measurable_const)
        (ne_top_of_le_ne_top hint (lintegral_mono fun s => min_le_left _ _))
        (Eventually.of_forall fun s => min_le_left _ _)]
  have hρfin : IsFiniteMeasure ρ := ⟨by
    rw [hρu]; exact lt_of_le_of_lt tsub_le_self (lt_top_iff_ne_top.2 hint)⟩
  refine ⟨0, ν', ρ, hν'fin, hρfin, by rw [adjointOp_kpow_zero, hsplit],
    cesaroCauchy_withDensity hπ hH hHb, ?_⟩
  rw [measureReal_def, hρu, ENNReal.toReal_sub_of_le
    (lintegral_mono fun s => min_le_left _ _) hint]
  linarith

/-! ### Measures concentrated on an ergodic set -/

/-- The step-`N` decomposition: `μPᴺ` is a measure absolutely continuous with respect to `φ`,
plus a measure of mass at most `(1 − ε) μ(S)`, both concentrated on `E` if `μ` is. -/
theorem doeblin_decomp {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε) {E : Set S}
    (hE : IsInvariantSet κ E) (μ : Measure S) [IsFiniteMeasure μ] (hμE : μ Eᶜ = 0) :
    ∃ (K R : Measure S) (_ : IsFiniteMeasure K) (_ : IsFiniteMeasure R),
      adjointOp (kpow κ N) μ = K + R ∧ K ≪ φ ∧ K Eᶜ = 0 ∧ R Eᶜ = 0 ∧
        R.real univ ≤ (1 - ε) * μ.real univ := by
  have hφ := hD.1
  set ν := adjointOp (kpow κ N) μ
  have hν : IsFiniteMeasure ν := isFinite_adjoint N μ
  have := isMarkov_kpow (κ := κ) N
  have hνE : ν Eᶜ = 0 := by
    rw [adjointOp_apply _ _ hE.1.compl]
    have hae : ∀ᵐ s ∂μ, s ∈ E := by
      rw [ae_iff]; simpa [compl_def] using hμE
    rw [lintegral_congr_ae (g := fun _ => 0) (hae.mono fun s hs => by
      rw [prob_compl_eq_zero_iff hE.1]; exact hE.2.2 s hs N hD.2.1)]
    simp
  set K := φ.withDensity (ν.rnDeriv φ)
  set R := ν.singularPart φ
  have hKle : K ≤ ν := Measure.withDensity_rnDeriv_le ν φ
  have hRle : R ≤ ν := Measure.singularPart_le ν φ
  have hKfin : IsFiniteMeasure K :=
    ⟨lt_of_le_of_lt (Measure.le_iff'.1 hKle univ) (measure_lt_top ν univ)⟩
  have hRfin : IsFiniteMeasure R :=
    ⟨lt_of_le_of_lt (Measure.le_iff'.1 hRle univ) (measure_lt_top ν univ)⟩
  refine ⟨K, R, hKfin, hRfin, ?_, withDensity_absolutelyContinuous _ _,
    nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hKle _).trans hνE.le),
    nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hRle _).trans hνE.le), ?_⟩
  · rw [add_comm]; exact Measure.haveLebesgueDecomposition_add ν φ
  · -- `R` lives on a `φ`-null set `Z`
    have hsing := Measure.mutuallySingular_singularPart ν φ
    set Z := hsing.nullSetᶜ
    have hZ : MeasurableSet Z := hsing.measurableSet_nullSet.compl
    have hφZ : φ.real Z = 0 := by rw [measureReal_def, hsing.measure_compl_nullSet]; rfl
    have hRZ : R.real univ = R.real Z := by
      rw [← measureReal_add_measureReal_compl (μ := R) hZ, compl_compl,
        measureReal_def R hsing.nullSet, hsing.measure_nullSet]; simp
    have hνZ : ν.real Z ≤ (1 - ε) * μ.real univ := by
      rw [bind_real_eq _ _ hZ]
      calc ∫ s, (kpow κ N s).real Z ∂μ ≤ ∫ _s, (1 - ε) ∂μ :=
            integral_mono (integrable_of_abs_le μ (Kernel.measurable_coe _ hZ).ennreal_toReal
              (C := 1) fun s => by
                rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
              (integrable_const _) fun s => hD.2.2.2 Z hZ (by rw [hφZ]; exact hD.2.2.1.le) s
        _ = (1 - ε) * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
    rw [hRZ]
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_iff'.1 hRle Z)).trans hνZ

/-- **Step 2.** Every finite measure concentrated on an ergodic set carrying an invariant
probability measure has uniformly Cauchy Cesàro averages. -/
theorem cesaroCauchy_of_concentrated {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    {E : Set S} (hE : IsErgodicSetD κ φ E) {π : Measure S} [IsProbabilityMeasure π]
    (hπ : adjointOp κ π = π) (hπE : π E = 1) (μ : Measure S) [IsFiniteMeasure μ]
    (hμE : μ Eᶜ = 0) : CesaroCauchy κ μ := by
  have hφ := hD.1
  have hε := hD.2.2.1
  have : Nonempty S := ⟨hE.1.2.1.some⟩
  have h1 : 0 ≤ 1 - ε := by linarith [doeblin_eps_le_one hD]
  -- the iterated decomposition
  have hiter : ∀ (j : ℕ) (μ : Measure S) [IsFiniteMeasure μ], μ Eᶜ = 0 →
      ∃ (G R : Measure S) (_ : IsFiniteMeasure G) (_ : IsFiniteMeasure R),
        adjointOp (kpow κ (N * j)) μ = G + R ∧ CesaroCauchy κ G ∧ R Eᶜ = 0 ∧
          R.real univ ≤ (1 - ε) ^ j * μ.real univ := by
    intro j
    induction j with
    | zero =>
      intro μ _ hμE
      exact ⟨0, μ, inferInstance, inferInstance, by rw [mul_zero, adjointOp_kpow_zero, zero_add],
        cesaroCauchy_zero, hμE, by simp⟩
    | succ j ih =>
      intro μ _ hμE
      obtain ⟨G, R, hG, hR, hdec, hGc, hRE, hRu⟩ := ih μ hμE
      obtain ⟨K, R', hK, hR', hdec', hKφ, hKE, hR'E, hR'u⟩ := doeblin_decomp hD hE.1 R hRE
      have := isFinite_adjoint (κ := κ) N G
      refine ⟨adjointOp (kpow κ N) G + K, R', inferInstance, hR', ?_,
        (cesaroCauchy_adjoint hGc N).add
          (cesaroCauchy_of_absCont hπ (absCont_of_concentrated hE hπ hπE hKφ hKE)), hR'E, ?_⟩
      · rw [show N * (j + 1) = N + N * j by ring, adjoint_add, hdec, adjointOp_add, hdec',
          add_assoc]
      · calc R'.real univ ≤ (1 - ε) * R.real univ := hR'u
          _ ≤ (1 - ε) * ((1 - ε) ^ j * μ.real univ) := mul_le_mul_of_nonneg_left hRu h1
          _ = (1 - ε) ^ (j + 1) * μ.real univ := by ring
  refine cesaroCauchy_of_approx fun η hη => ?_
  have hε1 : 1 - ε < 1 := by linarith
  · obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < η / (μ.real univ + 1) by positivity) hε1
    obtain ⟨G, R, hG, hR, hdec, hGc, -, hRu⟩ := hiter j μ hμE
    refine ⟨N * j, G, R, hG, hR, hdec, hGc, hRu.trans ?_⟩
    have hμ0 := measureReal_nonneg (μ := μ) (s := univ)
    calc (1 - ε) ^ j * μ.real univ ≤ η / (μ.real univ + 1) * (μ.real univ + 1) :=
          mul_le_mul hj.le (by linarith) hμ0 (by positivity)
      _ = η := by field_simp

/-! ### Absorption into the ergodic sets -/

omit [IsMarkovKernel κ] in
theorem iInf_shift_antitone {a : ℕ → ℝ≥0∞} (ha : Antitone a) (m : ℕ) :
    ⨅ n, a (m + n) = ⨅ n, a n :=
  le_antisymm (le_iInf fun n => (iInf_le _ n).trans (ha (Nat.le_add_left n m)))
    (le_iInf fun n => iInf_le _ (m + n))

/-- **Absorption.** From every state, the probability of being in the transient set
`F = (⋃ₘ Eₘ)ᶜ` tends to `0`. -/
theorem tendsto_kpow_transient [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) {M : ℕ} {E : Fin M → Set S} (hE : ∀ m, IsErgodicSetD κ φ (E m))
    (hall : ∀ F, IsErgodicSetD κ φ F → ∃ m, φ (F ∩ E m) = φ F ∧ φ (F ∩ E m) = φ (E m))
    (s : S) : Tendsto (fun n => kpow κ n s (⋃ m, E m)ᶜ) atTop (𝓝 0) := by
  have hφ := hD.1
  have hε := hD.2.2.1
  set F := (⋃ m, E m)ᶜ
  have hF : MeasurableSet F := (MeasurableSet.iUnion fun m => (hE m).1.1).compl
  have hzero : ∀ m, ∀ t ∈ E m, ∀ n, kpow κ n t F = 0 := by
    intro m t ht n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [kpow, Kernel.id_apply]
      rw [Measure.dirac_apply' t hF, indicator_of_notMem
        (show t ∉ F from fun h => h (mem_iUnion.2 ⟨m, ht⟩))]
    · have := isMarkov_kpow (κ := κ) n
      have h1 := (hE m).1.2.2 t ht n hn
      have hsub : F ⊆ (E m)ᶜ := fun x hx hxm => hx (mem_iUnion.2 ⟨m, hxm⟩)
      refine measure_mono_null hsub ?_
      rw [prob_compl_eq_zero_iff (hE m).1.1]; exact h1
  have hstep : ∀ t, kpow κ 1 t F ≤ F.indicator 1 t := fun t => by
    have := isMarkov_kpow (κ := κ) 1
    by_cases ht : t ∈ F
    · rw [indicator_of_mem ht]; exact prob_le_one
    · obtain ⟨m, hm⟩ := mem_iUnion.1 (not_not.1 ht)
      rw [hzero m t hm 1]; exact zero_le
  have hanti : ∀ t, Antitone fun n => kpow κ n t F := fun t =>
    antitone_nat_of_succ_le fun n => by
      have := isMarkov_kpow (κ := κ) n
      rw [kpow_add_apply n 1 t hF]
      calc ∫⁻ s', kpow κ 1 s' F ∂kpow κ n t ≤ ∫⁻ s', F.indicator 1 s' ∂kpow κ n t :=
            lintegral_mono hstep
        _ = kpow κ n t F := lintegral_indicator_one hF
  set g : S → ℝ≥0∞ := fun t => ⨅ n, kpow κ n t F
  have hgm : Measurable g := Measurable.iInf fun n => Kernel.measurable_coe _ hF
  have hg1 : ∀ t, g t ≤ 1 := fun t => by
    have := isMarkov_kpow (κ := κ) 0
    exact (iInf_le _ 0).trans prob_le_one
  have hgE : ∀ m, ∀ t ∈ E m, g t = 0 := fun m t ht =>
    le_antisymm ((iInf_le _ 0).trans (le_of_eq (hzero m t ht 0))) zero_le
  -- `g` is harmonic
  have hharm : ∀ t m, g t = ∫⁻ t', g t' ∂kpow κ m t := by
    intro t m
    have := isMarkov_kpow (κ := κ) m
    rw [lintegral_iInf (fun n => Kernel.measurable_coe _ hF)
      (fun a b hab t' => hanti t' hab) (by
        have := isMarkov_kpow (κ := κ) 0
        exact ne_top_of_le_ne_top (ENNReal.one_ne_top) (by
          calc ∫⁻ t', kpow κ 0 t' F ∂kpow κ m t ≤ ∫⁻ _t', 1 ∂kpow κ m t :=
                lintegral_mono fun t' => prob_le_one
            _ = 1 := by simp))]
    simp_rw [← kpow_add_apply m _ t hF]
    exact (iInf_shift_antitone (hanti t) m).symm
  set gr : S → ℝ := fun t => (g t).toReal
  have hgrm : Measurable gr := hgm.ennreal_toReal
  have hgr01 : ∀ t, 0 ≤ gr t ∧ gr t ≤ 1 := fun t =>
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      rw [ENNReal.ofReal_one]; exact hg1 t)⟩
  have hgri : ∀ (μ : Measure S) [IsFiniteMeasure μ], Integrable gr μ := fun μ _ =>
    integrable_of_abs_le μ hgrm (C := 1) fun t => by
      rw [abs_of_nonneg (hgr01 t).1]; exact (hgr01 t).2
  have hharmr : ∀ t m, gr t = ∫ t', gr t' ∂kpow κ m t := fun t m => by
    have := isMarkov_kpow (κ := κ) m
    simp only [gr]
    rw [integral_toReal hgm.aemeasurable (Eventually.of_forall fun t' =>
      lt_of_le_of_lt (hg1 t') ENNReal.one_lt_top), ← hharm]
  set γ := ⨆ t, gr t
  have hbdd : BddAbove (range gr) := ⟨1, by rintro _ ⟨t, rfl⟩; exact (hgr01 t).2⟩
  have hgrγ : ∀ t, gr t ≤ γ := fun t => le_ciSup hbdd t
  -- `γ ≤ 0`
  have hγ : γ ≤ 0 := by
    by_contra hγpos
    push Not at hγpos
    set B : ℝ → Set S := fun η' => {t | γ - η' < gr t}
    have hBm : ∀ η', MeasurableSet (B η') := fun η' => measurableSet_lt measurable_const hgrm
    -- from a nearly maximal point the chain stays nearly maximal
    have hkey : ∀ t η η', 0 < η' → γ - η < gr t → 1 - η / η' < (kpow κ N t).real (B η') := by
      intro t η η' hη' ht
      have := isMarkov_kpow (κ := κ) N
      have hle : ∀ t', gr t' ≤ γ - η' + η' * (B η').indicator (fun _ => (1 : ℝ)) t' :=
        fun t' => by
          by_cases h : t' ∈ B η'
          · rw [indicator_of_mem h, mul_one]; linarith [hgrγ t']
          · rw [indicator_of_notMem h, mul_zero, add_zero]
            simp only [B, mem_ofPred_eq, not_lt] at h; exact h
      have hI : Integrable (fun t' => η' * (B η').indicator (fun _ => (1 : ℝ)) t')
          (kpow κ N t) := ((integrable_const (1 : ℝ)).indicator (hBm η')).const_mul η'
      have hint : ∫ t', gr t' ∂kpow κ N t ≤
          ∫ t', (γ - η' + η' * (B η').indicator (fun _ => (1 : ℝ)) t') ∂kpow κ N t :=
        integral_mono (hgri (kpow κ N t)) ((integrable_const (γ - η')).add hI) hle
      have hrhs : ∫ t', (γ - η' + η' * (B η').indicator (fun _ => (1 : ℝ)) t') ∂kpow κ N t =
          γ - η' + η' * (kpow κ N t).real (B η') := by
        rw [integral_add (integrable_const _) hI, integral_const, probReal_univ, one_smul,
          integral_const_mul, integral_indicator_const _ (hBm η'), smul_eq_mul, mul_one]
      rw [hrhs, ← hharmr t N] at hint
      have h3 : γ - η < γ - η' + η' * (kpow κ N t).real (B η') := lt_of_lt_of_le ht hint
      have h4 : 1 - η / η' = (η' - η) / η' := by field_simp
      rw [h4, div_lt_iff₀ hη']
      linarith
    have hBlarge : ∀ η', 0 < η' → ε < φ.real (B η') := by
      intro η' hη'
      obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup (show γ - ε * η' / 2 < γ by
        have : 0 < ε * η' / 2 := by positivity
        linarith)
      have h1 := hkey t (ε * η' / 2) η' hη' ht
      have h2 : ε * η' / 2 / η' = ε / 2 := by field_simp
      rw [h2] at h1
      by_contra hle
      have := hD.2.2.2 (B η') (hBm η') (not_lt.1 hle) t
      linarith
    -- the set where `g` is maximal
    set Binf := {t | γ ≤ gr t}
    have hBinfm : MeasurableSet Binf := measurableSet_le measurable_const hgrm
    have hBinf_eq : Binf = ⋂ k : ℕ, B (1 / ((k : ℝ) + 1)) := by
      ext t
      simp only [Binf, B, mem_ofPred_eq, mem_iInter]
      constructor
      · intro h k; have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      · intro h
        refine le_of_forall_pos_lt_add fun δ hδ => ?_
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
        linarith [h k]
    have hBinfφ : ε ≤ φ.real Binf := by
      have hanti' : Antitone fun k : ℕ => B (1 / ((k : ℝ) + 1)) := fun a b hab t ht => by
        simp only [B, mem_ofPred_eq] at ht ⊢
        have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by
            have : (a : ℝ) ≤ b := by exact_mod_cast hab
            linarith)
        linarith
      have h1 := tendsto_measure_iInter_atTop (μ := φ)
        (fun k : ℕ => (hBm (1 / ((k : ℝ) + 1))).nullMeasurableSet) hanti' ⟨0, measure_ne_top _ _⟩
      rw [← hBinf_eq] at h1
      have h2 := (ENNReal.tendsto_toReal (measure_ne_top φ Binf)).comp h1
      exact ge_of_tendsto h2 (Eventually.of_forall fun k =>
        (hBlarge (1 / ((k : ℝ) + 1)) (by positivity)).le)
    have hBinf_ne : Binf.Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty] at hemp
      rw [hemp, measureReal_empty] at hBinfφ
      linarith
    -- `Binf` is invariant
    have hBinv : IsInvariantSet κ Binf := by
      refine ⟨hBinfm, hBinf_ne, fun t ht n hn => ?_⟩
      have := isMarkov_kpow (κ := κ) n
      have hγt : gr t = γ := le_antisymm (hgrγ t) ht
      have h0 : ∫ t', (γ - gr t') ∂kpow κ n t = 0 := by
        rw [integral_sub (integrable_const _) (hgri _), integral_const, probReal_univ, one_smul,
          ← hharmr t n, hγt, sub_self]
      have hae := (integral_eq_zero_iff_of_nonneg (fun t' => sub_nonneg.2 (hgrγ t'))
        ((integrable_const _).sub (hgri _))).1 h0
      rw [← prob_compl_eq_zero_iff hBinfm]
      refine measure_mono_null (fun t' ht' => ?_) (ae_iff.1 hae)
      simp only [Binf, mem_compl_iff, mem_ofPred_eq, not_le] at ht'
      simp only [mem_ofPred_eq, Pi.zero_apply]
      linarith
    obtain ⟨E', hE'sub, hE'erg⟩ := exists_ergodic_subset_of_invariant hD hBinv
    obtain ⟨m, hm, -⟩ := hall E' hE'erg
    have hdisj : E' ∩ E m = ∅ := eq_empty_of_forall_notMem fun t ⟨h1, h2⟩ => by
      have := hE'sub h1
      simp only [Binf, mem_ofPred_eq, gr, hgE m t h2, ENNReal.toReal_zero] at this
      linarith
    rw [hdisj, measure_empty] at hm
    have := invariant_real_gt hD hE'erg.1
    rw [measureReal_def, ← hm, ENNReal.toReal_zero] at this
    linarith
  have hg0 : g s = 0 := by
    have h1 : gr s = 0 := le_antisymm ((hgrγ s).trans hγ) (hgr01 s).1
    rcases (ENNReal.toReal_eq_zero_iff _).1 h1 with h | h
    · exact h
    · exact absurd h (ne_top_of_le_ne_top ENNReal.one_ne_top (hg1 s))
  rw [← hg0]
  exact tendsto_atTop_iInf (hanti s)

/-- Integrated absorption: the mass of `T*ⁿμ` in the transient set tends to `0`. -/
theorem tendsto_adjoint_transient [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) {M : ℕ} {E : Fin M → Set S} (hE : ∀ m, IsErgodicSetD κ φ (E m))
    (hall : ∀ F, IsErgodicSetD κ φ F → ∃ m, φ (F ∩ E m) = φ F ∧ φ (F ∩ E m) = φ (E m))
    (μ : Measure S) [IsFiniteMeasure μ] :
    Tendsto (fun n => adjointOp (kpow κ n) μ (⋃ m, E m)ᶜ) atTop (𝓝 0) := by
  have hF : MeasurableSet (⋃ m, E m)ᶜ := (MeasurableSet.iUnion fun m => (hE m).1.1).compl
  simp_rw [adjointOp_apply _ _ hF]
  have := tendsto_lintegral_of_dominated_convergence (μ := μ) (fun _ => 1)
    (fun n => Kernel.measurable_coe (kpow κ n) hF)
    (fun n => Eventually.of_forall fun s => by
      have := isMarkov_kpow (κ := κ) n; exact prob_le_one)
    (by simp) (Eventually.of_forall fun s => tendsto_kpow_transient hD hE hall s)
  simpa using this

/-- Each ergodic set carries an invariant probability measure. -/
theorem exists_invariant_on [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) {E : Set S} (hE : IsErgodicSetD κ φ E) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ adjointOp κ π = π ∧ π E = 1 := by
  obtain ⟨s, hs⟩ := hE.1.2.1
  obtain ⟨π, hπp, hπinv, hπr⟩ := exists_invariant hD (Measure.dirac s)
  refine ⟨π, hπp, hπinv, ?_⟩
  have hone : ∀ n, (cesaroM κ n (Measure.dirac s)).real E = 1 := fun n => by
    rw [cesaroM_real]
    have : ∀ k, (adjointOp (kpow κ (k + 1)) (Measure.dirac s)).real E = 1 := fun k => by
      rw [adjointOp, Measure.dirac_bind (kpow κ (k + 1)).measurable, measureReal_def,
        hE.1.2.2 s hs (k + 1) (by omega), ENNReal.toReal_one]
    simp only [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    exact inv_mul_cancel₀ (by positivity)
  have hlim : cesaroLim κ (Measure.dirac s) E = 1 :=
    tendsto_nhds_unique (tendsto_cesaroLim _ E) (tendsto_const_nhds.congr fun n => (hone n).symm)
  rw [← ofReal_measureReal (μ := π) (s := E), hπr E hE.1.1, hlim, ENNReal.ofReal_one]

/-- Every finite measure has uniformly Cauchy Cesàro averages under Condition D. -/
theorem cesaroCauchy_all [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (μ : Measure S) [IsFiniteMeasure μ] : CesaroCauchy κ μ := by
  obtain ⟨-, -, -, M, -, -, E, hE, hdisj, hall⟩ := theorem_11_9a hD
  choose π hπp hπinv hπE using fun m => exists_invariant_on hD (hE m)
  refine cesaroCauchy_of_approx fun η hη => ?_
  set F := (⋃ m, E m)ᶜ
  have hEm : ∀ m, MeasurableSet (E m) := fun m => (hE m).1.1
  have hFm : MeasurableSet F := (MeasurableSet.iUnion hEm).compl
  have hlim := (ENNReal.tendsto_toReal (ENNReal.zero_ne_top)).comp
    (tendsto_adjoint_transient hD hE hall μ)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (show (0 : ℝ≥0∞).toReal < η by simpa))).exists
  set ν := adjointOp (kpow κ n) μ
  have hν : IsFiniteMeasure ν := isFinite_adjoint n μ
  have hsplit : ν = ∑ m, ν.restrict (E m) + ν.restrict F := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisj hEm,
      Measure.restrict_add_restrict_compl (MeasurableSet.iUnion hEm)]
  have hGfin : IsFiniteMeasure (∑ m, ν.restrict (E m)) := by
    refine ⟨?_⟩
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    exact ENNReal.sum_lt_top.2 fun m _ => measure_lt_top _ _
  refine ⟨n, ∑ m, ν.restrict (E m), ν.restrict F, hGfin, inferInstance, hsplit,
    cesaroCauchy_finsetSum _ _ fun m _ => cesaroCauchy_of_concentrated hD (hE m) (hπinv m)
      (hπE m) _ (by rw [Measure.restrict_apply (hEm m).compl, compl_inter_self, measure_empty]),
    ?_⟩
  rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter]
  exact hn.le

/-- **Theorem 11.9b.** Under Condition D, for every `λ₀` the Cesàro averages
`(1/N) Σ_{n=1}^{N} T*ⁿλ₀` converge in total variation, and the limit is invariant. -/
theorem theorem_11_9b [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (l₀ : Measure S) [IsProbabilityMeasure l₀] :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      Tendsto (fun n => tvDist (cesaroM κ n l₀) μ) atTop (𝓝 0) := by
  have : ∀ n, IsProbabilityMeasure (cesaroM κ n l₀) := fun n => isProb_cesaroM n l₀
  obtain ⟨μ, hμ, hlim⟩ := lemma_11_8 (fun n => cesaroM κ n l₀)
    (tvDist_cesaro_le (cesaroCauchy_all hD l₀))
  refine ⟨μ, hμ, ?_, hlim⟩
  have hPfin : IsFiniteMeasure (adjointOp κ μ) := by
    have := isFinite_adjoint (κ := κ) 1 μ; rwa [kpow_one] at this
  refine Measure.ext fun A hA => ?_
  have hset : Tendsto (fun n => (cesaroM κ n l₀).real A) atTop (𝓝 (μ.real A)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hlim.div_const 2)
    rw [norm_norm, Real.norm_eq_abs]
    have := two_abs_le_tvDist (cesaroM κ n l₀) μ hA
    linarith
  set f : S → ℝ := fun s => (κ s).real A
  have hf : Measurable f := (κ.measurable_coe hA).ennreal_toReal
  have hf1 : ∀ s, |f s| ≤ 1 := fun s => by
    rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hint : Tendsto (fun n => ∫ s, f s ∂cesaroM κ n l₀) atTop (𝓝 (∫ s, f s ∂μ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (fun n => ?_) hlim
    rw [norm_norm, Real.norm_eq_abs]
    exact abs_integral_sub_le_tvDist _ _ hf hf1
  have hsh : Tendsto (fun n => ∫ s, f s ∂cesaroM κ n l₀) atTop (𝓝 (μ.real A)) := by
    have hd : Tendsto (fun n => (cesaroM κ n (adjointOp (kpow κ 1) l₀)).real A -
        (cesaroM κ n l₀).real A) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      rw [Real.norm_eq_abs]
      refine (abs_cesaro_shift_le n 1 l₀ A).trans (le_of_eq ?_)
      simp [div_eq_mul_inv]
    have := hd.add hset
    rw [zero_add] at this
    refine this.congr fun n => ?_
    have := isFinite_cesaroM (κ := κ) n l₀
    rw [sub_add_cancel, ← adjoint_cesaroM, bind_real_eq κ _ hA]
  have heq : (adjointOp κ μ).real A = μ.real A := by
    rw [bind_real_eq κ μ hA]; exact tendsto_nhds_unique hint hsh
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 heq

/-- An invariant measure gives the transient set measure zero. -/
theorem invariant_transient_null [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) {M : ℕ} {E : Fin M → Set S} (hE : ∀ m, IsErgodicSetD κ φ (E m))
    (hall : ∀ F, IsErgodicSetD κ φ F → ∃ m, φ (F ∩ E m) = φ F ∧ φ (F ∩ E m) = φ (E m))
    {μ : Measure S} [IsProbabilityMeasure μ] (hμ : adjointOp κ μ = μ) :
    μ (⋃ m, E m)ᶜ = 0 := by
  have h := tendsto_adjoint_transient hD hE hall μ
  simp only [invariant_iterate hμ] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

/-- The restriction of an invariant measure to an ergodic set is invariant. -/
theorem restrict_invariant [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) {M : ℕ} {E : Fin M → Set S} (hE : ∀ m, IsErgodicSetD κ φ (E m))
    (hdisj : Pairwise (Function.onFun Disjoint E))
    (hall : ∀ F, IsErgodicSetD κ φ F → ∃ m, φ (F ∩ E m) = φ F ∧ φ (F ∩ E m) = φ (E m))
    {μ : Measure S} [IsProbabilityMeasure μ] (hμ : adjointOp κ μ = μ) (m : Fin M) :
    adjointOp κ (μ.restrict (E m)) = μ.restrict (E m) := by
  have hEm : ∀ m, MeasurableSet (E m) := fun m => (hE m).1.1
  have hκE : ∀ m', ∀ s ∈ E m', κ s (E m') = 1 := fun m' s hs => by
    have := (hE m').1.2.2 s hs 1 le_rfl; rwa [kpow_one] at this
  have hF := invariant_transient_null hD hE hall hμ
  ext A hA
  rw [adjointOp_apply κ _ hA, Measure.restrict_apply hA]
  have h1 : μ (A ∩ E m) = ∫⁻ s, κ s (A ∩ E m) ∂μ := by
    rw [← adjointOp_apply κ _ (hA.inter (hEm m)), hμ]
  rw [h1, ← lintegral_add_compl (fun s => κ s (A ∩ E m)) (hEm m)]
  have hoff : ∫⁻ s in (E m)ᶜ, κ s (A ∩ E m) ∂μ = 0 := by
    rw [lintegral_eq_zero_iff (κ.measurable_coe (hA.inter (hEm m)))]
    have hae : ∀ᵐ s ∂μ, s ∈ ⋃ m, E m := by
      rw [ae_iff]; simpa [compl_def] using hF
    rw [EventuallyEq, ae_restrict_iff' (hEm m).compl]
    filter_upwards [hae] with s hs hsm
    obtain ⟨m', hm'⟩ := mem_iUnion.1 hs
    have hne : m' ≠ m := fun h => hsm (h ▸ hm')
    have h0 : κ s (E m) = 0 := by
      refine measure_mono_null (hdisj hne).subset_compl_left ?_
      rw [prob_compl_eq_zero_iff (hEm m')]; exact hκE m' s hm'
    exact measure_mono_null inter_subset_right h0
  rw [hoff, add_zero]
  refine setLIntegral_congr_fun (hEm m) fun s hs => ?_
  symm
  have h0 : κ s (A \ E m) = 0 := measure_mono_null (show A \ E m ⊆ (E m)ᶜ from
    fun x hx => hx.2) (by
    rw [prob_compl_eq_zero_iff (hEm m)]; exact hκE m s hs)
  rw [← measure_inter_add_sdiff A (hEm m), h0, add_zero]

/-- **Theorem 11.9c.** Under Condition D there are `M ≥ 1` ergodic sets `E₁, …, E_M`, each
carrying an invariant probability measure `πₘ`, and every invariant probability measure is the
convex combination `Σₘ μ(Eₘ) πₘ`. -/
theorem theorem_11_9c [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε) :
    ∃ (M : ℕ) (E : Fin M → Set S) (π : Fin M → Measure S), 1 ≤ M ∧
      (∀ m, IsErgodicSetD κ φ (E m)) ∧ Pairwise (Function.onFun Disjoint E) ∧
      (∀ m, IsProbabilityMeasure (π m) ∧ adjointOp κ (π m) = π m ∧ π m (E m) = 1) ∧
      ∀ μ : Measure S, IsProbabilityMeasure μ → adjointOp κ μ = μ →
        ∑ m, μ (E m) = 1 ∧ μ = ∑ m, μ (E m) • π m := by
  obtain ⟨-, -, -, M, hM1, -, E, hE, hdisj, hall⟩ := theorem_11_9a hD
  choose π hπp hπinv hπE using fun m => exists_invariant_on hD (hE m)
  refine ⟨M, E, π, hM1, hE, hdisj, fun m => ⟨hπp m, hπinv m, hπE m⟩, fun μ hμp hμ => ?_⟩
  have hEm : ∀ m, MeasurableSet (E m) := fun m => (hE m).1.1
  have hF := invariant_transient_null hD hE hall hμ
  have hrestr : ∀ m, μ.restrict (E m) = μ (E m) • π m := by
    intro m
    have hinv := restrict_invariant hD hE hdisj hall hμ m
    by_cases h0 : μ (E m) = 0
    · rw [h0, zero_smul, Measure.restrict_eq_zero.2 h0]
    · set c := (μ (E m))⁻¹
      have hρp : IsProbabilityMeasure (c • μ.restrict (E m)) := ⟨by
        rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
          smul_eq_mul, ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)]⟩
      have hρinv : adjointOp κ (c • μ.restrict (E m)) = c • μ.restrict (E m) := by
        rw [adjointOp_smul, hinv]
      have hρE : (c • μ.restrict (E m)) (E m) = 1 := by
        rw [Measure.smul_apply, Measure.restrict_apply (hEm m), inter_self, smul_eq_mul,
          ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)]
      have := invariant_unique hD (hE m) hρinv (hπinv m) hρE (hπE m)
      rw [← this, smul_smul, ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_smul]
  have hsplit : μ = ∑ m, μ.restrict (E m) := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisj hEm]
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) (MeasurableSet.iUnion hEm)]
    rw [Measure.restrict_eq_zero.2 hF, add_zero]
  refine ⟨?_, by rw [← Finset.sum_congr rfl fun m _ => hrestr m]; exact hsplit⟩
  calc ∑ m, μ (E m) = μ (⋃ m, E m) := by
        rw [measure_iUnion hdisj hEm, tsum_fintype]
    _ = 1 := by
        rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion hEm)]; exact hF

/-- Under the reachability condition of Theorem 11.10 there is exactly one ergodic set in the
decomposition of Theorem 11.9. -/
theorem ergodic_count_eq_one [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε)
    (hirr : ∀ A, MeasurableSet A → 0 < φ A → ∀ s, ∃ n, 1 ≤ n ∧ 0 < kpow κ n s A)
    {M : ℕ} {E : Fin M → Set S} (hM : 1 ≤ M) (hE : ∀ m, IsErgodicSetD κ φ (E m))
    (hdisj : Pairwise (Function.onFun Disjoint E)) : M = 1 := by
  by_contra hne
  have h2 : 2 ≤ M := by omega
  set m₀ : Fin M := ⟨0, by omega⟩
  set m₁ : Fin M := ⟨1, by omega⟩
  have hne' : m₀ ≠ m₁ := fun h => by simpa [m₀, m₁] using congrArg Fin.val h
  have h := (theorem_11_10a hD hirr (hE m₀) (hE m₁)).1
  rw [(hdisj hne').inter_eq, measure_empty] at h
  have := invariant_real_gt hD (hE m₀).1
  rw [measureReal_def, ← h, ENNReal.toReal_zero] at this
  linarith [hD.2.2.1]

/-- **Theorem 11.10b.** Under the reachability condition, `T*` has exactly one invariant
probability measure. -/
theorem theorem_11_10b [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (hirr : ∀ A, MeasurableSet A → 0 < φ A → ∀ s, ∃ n, 1 ≤ n ∧ 0 < kpow κ n s A) :
    ∃! μ : Measure S, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ := by
  obtain ⟨M, E, π, hM, hE, hdisj, hπ, hall⟩ := theorem_11_9c hD
  have hM1 := ergodic_count_eq_one hD hirr hM hE hdisj
  subst hM1
  obtain ⟨hπp, hπinv, -⟩ := hπ 0
  refine ⟨π 0, ⟨hπp, hπinv⟩, fun μ ⟨hμp, hμ⟩ => ?_⟩
  obtain ⟨hsum, hdec⟩ := hall μ hμp hμ
  simp only [Fin.sum_univ_one] at hsum hdec
  rw [hdec, hsum, one_smul]

/-- **Theorem 11.10c.** Under the reachability condition, the Cesàro averages of `T*ⁿλ₀`
converge in total variation to the unique invariant measure, for every `λ₀`. -/
theorem theorem_11_10c [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (hirr : ∀ A, MeasurableSet A → 0 < φ A → ∀ s, ∃ n, 1 ≤ n ∧ 0 < kpow κ n s A) :
    ∃ lstar : Measure S, IsProbabilityMeasure lstar ∧ adjointOp κ lstar = lstar ∧
      ∀ (l₀ : Measure S) [IsProbabilityMeasure l₀],
        Tendsto (fun n => tvDist (cesaroM κ n l₀) lstar) atTop (𝓝 0) := by
  obtain ⟨lstar, ⟨hp, hinv⟩, huniq⟩ := theorem_11_10b hD hirr
  refine ⟨lstar, hp, hinv, fun l₀ _ => ?_⟩
  obtain ⟨μ, hμp, hμinv, hlim⟩ := theorem_11_9b hD l₀
  rwa [huniq μ ⟨hμp, hμinv⟩] at hlim

end StokeyLucasPrescott.StrongConvergence
