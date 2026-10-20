/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.FellerInvariant

/-!
# Dependence on a parameter, and a loose end (SLP §§12.5–12.6, pp. 383–388)

* **Theorem 12.13**: on a compact metric state space, if `(s, θ) ↦ P_θ(s, ·)` is weakly continuous
  and each `T_θ*` has a unique fixed point `μ_θ`, then `θ ↦ μ_θ` is weakly continuous. The book's
  "uniformly continuous on `S × Θ̂`" step becomes the sequential lemma `tendsto_uniform_markovOp`
  (`T_{θₙ}f → T_{θ₀}f` uniformly), proved by compactness of `S`; `Θ` may be any metric space;
* **Lemma 12.14**: for Feller `Q` and bounded continuous `f` on `X × Z`,
  `(Tf)(y, z) = ∫ f(y, z′) Q(z, dz′)` is bounded and continuous (`lemma_12_14_cont`), for any
  metric spaces `X`, `Z`; and `T` preserves monotonicity, strict monotonicity, concavity and strict
  concavity in `y` (`lemma_12_14_mono`, `_strictMono`, `_concave`, `_strictConcave`). The key limit
  (1) is proved with the continuous majorants `gₖ(z′) = sup_{n ≥ k} |f(yₙ, z′) - f(y, z′)|`
  (maxima of a jointly continuous function over the compact sets `{y} ∪ {yₙ : n ≥ k}`) in place of
  the book's boundary-counting argument; this avoids the book's inexact description of
  `∂E_k(ε)`.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

/-! ### Theorem 12.13 -/

variable {S Θ : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [MetricSpace Θ]

omit [BorelSpace S] in
/-- Under the joint weak continuity of Theorem 12.13(b) on compact `S`, `T_{θₙ}f → T_{θ₀}f`
uniformly whenever `θₙ → θ₀`. -/
theorem tendsto_uniform_markovOp [CompactSpace S] (P : Θ → Kernel S S)
    (hcont : ∀ (s : ℕ → S) (θ : ℕ → Θ) (s₀ : S) (θ₀ : Θ), Tendsto s atTop (𝓝 s₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (s n)) (P θ₀ s₀))
    {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) (f : S →ᵇ ℝ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ s, |markovOpR (P (θ n)) f s - markovOpR (P θ₀) f s| < ε := by
  intro ε hε
  by_contra hne
  rw [not_eventually, frequently_atTop] at hne
  choose nk hnk hbad using hne
  have hbad' : ∀ k, ∃ s, ε ≤ |markovOpR (P (θ (nk k))) f s - markovOpR (P θ₀) f s| := fun k => by
    have := hbad k; push Not at this; exact this
  choose sk hsk using hbad'
  obtain ⟨s₀, -, ψ, hψ, hsψ⟩ := isCompact_univ.tendsto_subseq (fun k => mem_univ (sk k))
  have hn : Tendsto (fun j => nk (ψ j)) atTop atTop :=
    tendsto_atTop_mono (fun j => (hψ.id_le j).trans (hnk (ψ j))) tendsto_id
  have hA := hcont (sk ∘ ψ) (fun j => θ (nk (ψ j))) s₀ θ₀ hsψ (hθ.comp hn) f
  have hB := hcont (sk ∘ ψ) (fun _ => θ₀) s₀ θ₀ hsψ tendsto_const_nhds f
  have hdiff := (hA.sub hB).abs
  rw [sub_self, abs_zero] at hdiff
  obtain ⟨j, hj⟩ := (hdiff.eventually (gt_mem_nhds hε)).exists
  exact absurd (hsk (ψ j)) (not_le.2 hj)

/-- **Theorem 12.13.** Let `S` be a compact metric space and `Θ` a metric space. If
(b) `(sₙ, θₙ) → (s₀, θ₀)` implies `P_{θₙ}(sₙ, ·) ⇒ P_{θ₀}(s₀, ·)`, and (c) each `T_θ*` has a
unique fixed point `μ_θ`, then `θₙ → θ₀` implies `μ_{θₙ} ⇒ μ_{θ₀}`. -/
theorem theorem_12_13 [CompactSpace S] (P : Θ → Kernel S S) [∀ θ, IsMarkovKernel (P θ)]
    (hcont : ∀ (s : ℕ → S) (θ : ℕ → Θ) (s₀ : S) (θ₀ : Θ), Tendsto s atTop (𝓝 s₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (s n)) (P θ₀ s₀))
    (μ : Θ → Measure S) [∀ θ, IsProbabilityMeasure (μ θ)]
    (hfix : ∀ θ, adjointOp (P θ) (μ θ) = μ θ)
    (huniq : ∀ θ (ν : Measure S), IsProbabilityMeasure ν → adjointOp (P θ) ν = ν → ν = μ θ)
    {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) :
    ConvWeak (fun n => μ (θ n)) (μ θ₀) := by
  have hF0 : IsFeller (P θ₀) :=
    (ex_12_7 (P θ₀)).1.2 fun s s₀ hs => hcont s (fun _ => θ₀) s₀ θ₀ hs tendsto_const_nhds
  have hT : ∀ (κ : Kernel S S) [IsMarkovKernel κ] (g : S →ᵇ ℝ),
      Measurable (markovOpR κ g) ∧ ∀ s, |markovOpR κ g s| ≤ ‖g‖ := fun κ _ g =>
    theorem_8_1_cor κ g.continuous.measurable (bcf_abs_le_norm g)
  intro f
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨μh, hμh, φ, hφ, hconv⟩ := exists_convWeak_subseq_of_tight (fun k => μ (θ (ns k)))
    fun ε hε => ⟨univ, isCompact_univ, fun n => by rw [probReal_univ]; linarith⟩
  set m : ℕ → ℕ := fun j => ns (φ j)
  have hm : Tendsto m atTop atTop := hns.comp hφ.tendsto_atTop
  have : ∀ j, IsProbabilityMeasure (((fun k => μ (θ (ns k))) ∘ φ) j) := fun j =>
    inferInstanceAs (IsProbabilityMeasure (μ (θ (ns (φ j)))))
  -- the subsequential limit is a fixed point of `T₀*`
  have hinv : adjointOp (P θ₀) μh = μh := by
    have : IsProbabilityMeasure (adjointOp (P θ₀) μh) := (theorem_8_2 (P θ₀) μh).1
    refine theorem_12_6_cor2 fun g => ?_
    rw [← integral_markovOpR (P θ₀) μh g]
    have h1 : Tendsto (fun j => ∫ s, markovOpR (P θ₀) g s ∂μ (θ (m j))) atTop
        (𝓝 (∫ s, markovOpR (P θ₀) g s ∂μh)) := hconv (fellerBCF hF0 g)
    have h2 : Tendsto (fun j => ∫ s, g s ∂μ (θ (m j))) atTop (𝓝 (∫ s, g s ∂μh)) := hconv g
    have h3 : Tendsto (fun j => ∫ s, markovOpR (P θ₀) g s ∂μ (θ (m j)) -
        ∫ s, g s ∂μ (θ (m j))) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hm.eventually (tendsto_uniform_markovOp P hcont hθ g (ε / 2)
        (half_pos hε))] with j hj
      have hgj : ∫ s, g s ∂μ (θ (m j)) = ∫ s, markovOpR (P (θ (m j))) g s ∂μ (θ (m j)) := by
        rw [integral_markovOpR, hfix]
      rw [hgj, Real.dist_eq, sub_zero, ← integral_sub
        (integrable_of_bounded (hT _ g).1 (hT _ g).2)
        (integrable_of_bounded (hT _ g).1 (hT _ g).2)]
      have := norm_integral_le_of_norm_le_const (μ := μ (θ (m j))) (C := ε / 2)
        (f := fun s => markovOpR (P θ₀) g s - markovOpR (P (θ (m j))) g s)
        (Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs, abs_sub_comm]; exact (hj s).le)
      rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
      linarith
    have h4 := h3.add h2
    simp only [sub_add_cancel, zero_add] at h4
    exact (tendsto_nhds_unique h4 h1).symm
  have := huniq θ₀ μh hμh hinv
  subst this
  exact ⟨φ, hconv f⟩

/-! ### Lemma 12.14 -/

variable {X Z : Type*} [MetricSpace X] [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- The key limit (1) in the proof of Lemma 12.14: if `yₙ → y` and `Q(zₙ, ·) ⇒ Q(z, ·)`, then
`∫ |f(yₙ, z′) - f(y, z′)| Q(zₙ, dz′) → 0`. -/
theorem tendsto_integral_abs_sub (f : X × Z →ᵇ ℝ) {y : ℕ → X} {y₀ : X}
    (hy : Tendsto y atTop (𝓝 y₀)) {ν : ℕ → Measure Z} {ν₀ : Measure Z}
    [∀ n, IsProbabilityMeasure (ν n)] [IsProbabilityMeasure ν₀] (hν : ConvWeak ν ν₀) :
    Tendsto (fun n => ∫ z', |f (y n, z') - f (y₀, z')| ∂ν n) atTop (𝓝 0) := by
  set h : Z → X → ℝ := fun z' w => |f (w, z') - f (y₀, z')|
  have hh : Continuous (Function.uncurry h) := by
    have : Function.uncurry h = fun p : Z × X => |f (p.2, p.1) - f (y₀, p.1)| := rfl
    rw [this]
    exact ((f.continuous.comp (continuous_snd.prodMk continuous_fst)).sub
      (f.continuous.comp (continuous_const.prodMk continuous_fst))).abs
  have hbd : ∀ z' w, h z' w ≤ 2 * ‖f‖ := fun z' w => by
    have h1 := bcf_abs_le_norm f (w, z'); have h2 := bcf_abs_le_norm f (y₀, z')
    linarith [abs_sub (f (w, z')) (f (y₀, z'))]
  set W : ℕ → Set X := fun k => insert y₀ (range fun n => y (n + k))
  have hW : ∀ k, IsCompact (W k) := fun k =>
    (hy.comp (tendsto_add_atTop_nat k)).isCompact_insert_range
  set g : ℕ → Z → ℝ := fun k z' => sSup (h z' '' W k)
  have hne : ∀ k z', (h z' '' W k).Nonempty := fun k z' => (insert_nonempty _ _).image _
  have hbdd : ∀ k z', BddAbove (h z' '' W k) := fun k z' =>
    ⟨2 * ‖f‖, by rintro _ ⟨w, -, rfl⟩; exact hbd z' w⟩
  have hg0 : ∀ k z', 0 ≤ g k z' := fun k z' =>
    (abs_nonneg _).trans (le_csSup (hbdd k z') ⟨y₀, mem_insert _ _, rfl⟩)
  have hg2 : ∀ k z', g k z' ≤ 2 * ‖f‖ := fun k z' =>
    csSup_le (hne k z') (by rintro _ ⟨w, -, rfl⟩; exact hbd z' w)
  have hgle : ∀ k n z', k ≤ n → |f (y n, z') - f (y₀, z')| ≤ g k z' := fun k n z' hkn =>
    le_csSup (hbdd k z') ⟨y n, mem_insert_of_mem _ ⟨n - k, by
      simp only; rw [Nat.sub_add_cancel hkn]⟩, rfl⟩
  have hgc : ∀ k, Continuous (g k) := fun k => (hW k).continuous_sSup hh
  set G : ℕ → Z →ᵇ ℝ := fun k => BoundedContinuousFunction.mkOfBound ⟨g k, hgc k⟩ (2 * ‖f‖)
    fun a b => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
      constructor <;> linarith [hg0 k a, hg0 k b, hg2 k a, hg2 k b]
  -- `gₖ ↓ 0` pointwise
  have hgk : ∀ z', Tendsto (fun k => g k z') atTop (𝓝 0) := fun z' => by
    have hc : Tendsto (fun n => f (y n, z')) atTop (𝓝 (f (y₀, z'))) :=
      (f.continuous.tendsto _).comp (hy.prodMk_nhds tendsto_const_nhds)
    rw [Metric.tendsto_nhds] at hc ⊢
    intro ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hc (ε / 2) (half_pos hε))
    refine eventually_atTop.2 ⟨K, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hg0 k z')]
    refine lt_of_le_of_lt (csSup_le (hne k z') ?_) (half_lt_self hε)
    rintro _ ⟨w, hw, rfl⟩
    rcases hw with rfl | ⟨n, rfl⟩
    · simp only [h, sub_self, abs_zero]; positivity
    · have := hK (n + k) (by omega)
      rw [Real.dist_eq] at this; exact this.le
  -- `∫ gₖ dν₀ → 0` by dominated convergence
  have hGk : Tendsto (fun k => ∫ z', g k z' ∂ν₀) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := ν₀) (fun _ => 2 * ‖f‖)
      (fun k => (hgc k).aestronglyMeasurable) (integrable_const _)
      (fun k => Eventually.of_forall fun z' => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 k z')]; exact hg2 k z')
      (Eventually.of_forall hgk)
    simpa using this
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := (hGk.eventually (gt_mem_nhds (half_pos hε))).exists
  have hconvk : Tendsto (fun n => ∫ z', g k z' ∂ν n) atTop (𝓝 (∫ z', g k z' ∂ν₀)) := hν (G k)
  filter_upwards [hconvk.eventually (gt_mem_nhds (show ∫ z', g k z' ∂ν₀ < ε by linarith)),
    eventually_ge_atTop k] with n hn hkn
  have hint : Integrable (fun z' => |f (y n, z') - f (y₀, z')|) (ν n) :=
    integrable_of_bounded ((hh.comp (continuous_id.prodMk continuous_const)).measurable)
      (M := 2 * ‖f‖) fun z' => by
        rw [abs_abs]; exact hbd z' (y n)
  have h1 : ∫ z', |f (y n, z') - f (y₀, z')| ∂ν n ≤ ∫ z', g k z' ∂ν n :=
    integral_mono hint ((G k).integrable _) fun z' => hgle k n z' hkn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  linarith

/-- **Lemma 12.14** (continuity). For a Feller transition function `Q` on `Z` and bounded continuous
`f` on `X × Z`, `(Tf)(y, z) = ∫ f(y, z′) Q(z, dz′)` is bounded and continuous. (The book takes
`X ⊆ ℝˡ`, `Z ⊆ ℝᵏ` convex; continuity holds for any metric spaces.) -/
theorem lemma_12_14_cont (Q : Kernel Z Z) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (f : X × Z →ᵇ ℝ) :
    Continuous (fun p : X × Z => ∫ z', f (p.1, z') ∂Q p.2) ∧
      ∀ p : X × Z, |∫ z', f (p.1, z') ∂Q p.2| ≤ ‖f‖ := by
  refine ⟨?_, fun p => ?_⟩
  · rw [continuous_iff_seqContinuous]
    intro p p₀ hp
    have hy : Tendsto (fun n => (p n).1) atTop (𝓝 p₀.1) := (continuous_fst.tendsto _).comp hp
    have hz : Tendsto (fun n => (p n).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
    have hQz := (ex_12_7 Q).1.1 hQ _ _ hz
    set F₀ : Z →ᵇ ℝ := f.compContinuous ⟨fun z' => (p₀.1, z'), by fun_prop⟩
    have hv : Tendsto (fun n => ∫ z', f (p₀.1, z') ∂Q (p n).2) atTop
        (𝓝 (∫ z', f (p₀.1, z') ∂Q p₀.2)) := hQz F₀
    have hd := tendsto_integral_abs_sub f hy hQz
    have hu : Tendsto (fun n => ∫ z', f ((p n).1, z') ∂Q (p n).2 -
        ∫ z', f (p₀.1, z') ∂Q (p n).2) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) hd
      set Fn : Z →ᵇ ℝ := f.compContinuous ⟨fun z' => ((p n).1, z'), by fun_prop⟩
      rw [← integral_sub (f := fun z' => f ((p n).1, z')) (g := fun z' => f (p₀.1, z'))
        (Fn.integrable _) (F₀.integrable _)]
      exact norm_integral_le_integral_norm _
    have := hu.add hv
    simp only [sub_add_cancel, zero_add] at this
    exact this
  · have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := ‖f‖)
      (f := fun z' => f (p.1, z')) (Eventually.of_forall fun z' => f.norm_coe_le_norm _)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

variable {l : ℕ} {E : Set (Fin l → ℝ)}

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (monotonicity). If `f(·, z′)` is nondecreasing on `X` for every `z′`, so is
`Tf(·, z)`. -/
theorem lemma_12_14_mono (Q : Kernel Z Z) [IsMarkovKernel Q] {f : (Fin l → ℝ) → Z → ℝ}
    (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hf : ∀ z', MonotoneOn (fun y => f y z') E)
    (z : Z) : MonotoneOn (fun y => ∫ z', f y z' ∂Q z) E := fun y hy y' hy' hyy' =>
  integral_mono (hint y hy z) (hint y' hy' z) fun z' => hf z' hy hy' hyy'

omit [MetricSpace Z] [BorelSpace Z] in
/-- A strict pointwise inequality between integrable functions integrates to a strict inequality
under a probability measure. -/
theorem integral_lt_integral_of_lt {μ : Measure Z} [IsProbabilityMeasure μ] {u v : Z → ℝ}
    (hu : Integrable u μ) (hv : Integrable v μ) (h : ∀ z, u z < v z) :
    ∫ z, u z ∂μ < ∫ z, v z ∂μ := by
  have hpos : 0 < ∫ z, (v z - u z) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun z => (sub_pos.2 (h z)).le) (hv.sub hu)]
    have : Function.support (fun z => v z - u z) = univ :=
      eq_univ_of_forall fun z => (sub_pos.2 (h z)).ne'
    rw [this, measure_univ]; exact zero_lt_one
  rw [integral_sub hv hu] at hpos
  linarith

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (strict monotonicity). -/
theorem lemma_12_14_strictMono (Q : Kernel Z Z) [IsMarkovKernel Q] {f : (Fin l → ℝ) → Z → ℝ}
    (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hf : ∀ z', StrictMonoOn (fun y => f y z') E)
    (z : Z) : StrictMonoOn (fun y => ∫ z', f y z' ∂Q z) E := fun y hy y' hy' hyy' =>
  integral_lt_integral_of_lt (hint y hy z) (hint y' hy' z) fun z' => hf z' hy hy' hyy'

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (concavity). If `f(·, z′)` is concave on the convex set `X` for every `z′`,
so is `Tf(·, z)`. -/
theorem lemma_12_14_concave (Q : Kernel Z Z) [IsMarkovKernel Q] {f : (Fin l → ℝ) → Z → ℝ}
    (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hE : Convex ℝ E)
    (hf : ∀ z', ConcaveOn ℝ E (fun y => f y z')) (z : Z) :
    ConcaveOn ℝ E (fun y => ∫ z', f y z' ∂Q z) := by
  refine ⟨hE, fun y hy y' hy' α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint y hy z).const_mul α) ((hint y' hy' z).const_mul β)]
  refine integral_mono (((hint y hy z).const_mul α).add ((hint y' hy' z).const_mul β))
    (hint _ (hE hy hy' hα hβ hαβ) z) fun z' => ?_
  have := (hf z').2 hy hy' hα hβ hαβ
  simpa only [smul_eq_mul] using this

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (strict concavity). -/
theorem lemma_12_14_strictConcave (Q : Kernel Z Z) [IsMarkovKernel Q]
    {f : (Fin l → ℝ) → Z → ℝ} (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hE : Convex ℝ E)
    (hf : ∀ z', StrictConcaveOn ℝ E (fun y => f y z')) (z : Z) :
    StrictConcaveOn ℝ E (fun y => ∫ z', f y z' ∂Q z) := by
  refine ⟨hE, fun y hy y' hy' hne α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint y hy z).const_mul α) ((hint y' hy' z).const_mul β)]
  refine integral_lt_integral_of_lt (((hint y hy z).const_mul α).add
    ((hint y' hy' z).const_mul β)) (hint _ (hE hy hy' hα.le hβ.le hαβ) z) fun z' => ?_
  have := (hf z').2 hy hy' hne hα hβ hαβ
  simpa only [smul_eq_mul] using this

end StokeyLucasPrescott.ConvergenceApplications
