/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.Histories

/-!
# Infinite histories and Markov processes

SLP §8.2, pp. 220–225. The measure `μ^∞(z₀, ·)` on infinite paths, which the book obtains from
the measures on finite rectangles with an omitted proof of countable additivity (the
Ionescu-Tulcea theorem, here Mathlib's `trajMeasure`): `pathMeasure Q z₀` is the law of the path
`(z₀, z₁, z₂, …)`. Its finite-dimensional distributions are the measures `μᵗ(z₀, ·)` of the finite
histories (`pathMeasure_marginal`), which determine it (`pathMeasure_unique`).

Stochastic processes (`IsStochasticProcess`); the canonical process is one
(`canonical_isStochasticProcess`). The Markov property and stationary transitions of
Exercise 8.6a–b, in the rigorous form: the joint law of the history up to `t` and the next state
is the law of the history composed with `Q(z_t, ·)` (`ex_8_6ab`), so that `Q(z_t, ·)` is a
regular conditional distribution of `z_{t+1}` given `(z₀, …, z_t)` (`ex_8_6ab_condDistrib`);
the book's conditional probabilities given the point events `{σ_τ = a_τ}` are not defined in
general. Exercise 8.6c: shocks drawn independently from `λ` form a stationary process
(`ex_8_6c`). Exercise 8.7: coin tossing (`ex_8_7a`, `ex_8_7b`, `ex_8_7c`).
-/

namespace StokeyLucasPrescott.MarkovProcesses

open MeasureTheory ProbabilityTheory Set Filter Topology Preorder
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

/-- The kernels `(z₀, …, z_n) ↦ Q(z_n, ·)` that drive the path. -/
noncomputable def trajKernel (Q : Kernel Z Z) (n : ℕ) : Kernel (Π _ : Finset.Iic n, Z) Z :=
  Q.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

theorem isMarkovKernel_trajKernel (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) :
    IsMarkovKernel (trajKernel Q n) := by
  unfold trajKernel
  infer_instance

/-- The law of the path `(z₀, z₁, z₂, …)` started at `z₀` (the book's `μ^∞(z₀, ·)`, with the
initial state included as coordinate `0`). -/
noncomputable def pathMeasure (Q : Kernel Z Z) [IsMarkovKernel Q] (z₀ : Z) : Measure (ℕ → Z) :=
  have := isMarkovKernel_trajKernel Q
  Kernel.trajMeasure (X := fun _ => Z) (Measure.dirac z₀) (trajKernel Q)

variable (Q : Kernel Z Z) [IsMarkovKernel Q]

theorem isProbabilityMeasure_pathMeasure (z₀ : Z) : IsProbabilityMeasure (pathMeasure Q z₀) := by
  have := isMarkovKernel_trajKernel Q
  unfold pathMeasure
  infer_instance

/-- The history `(z₁, …, z_T)` of a path. -/
def prefixHist (T : ℕ) (ω : ℕ → Z) : Fin T → Z := fun i => ω (i + 1)

theorem measurable_prefixHist (T : ℕ) : Measurable (prefixHist (Z := Z) T) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- The path starts at `z₀`: the law of `z₀` under the path measure is `δ_{z₀}`. -/
theorem pathMeasure_map_zero (z₀ : Z) : (pathMeasure Q z₀).map (frestrictLe 0) =
    Measure.dirac ((MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Z)).symm z₀) := by
  have := isMarkovKernel_trajKernel Q
  rw [pathMeasure, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_dirac' (MeasurableEquiv.measurable _)]

/-- **The finite-dimensional distributions of the path are the measures `μᵗ(z₀, ·)`** (SLP
p. 222: `μ^∞(z₀, A₁ × ⋯ × A_T × Z × ⋯) = μᵀ(z₀, A₁ × ⋯ × A_T)`). -/
theorem pathMeasure_marginal (z₀ : Z) (T : ℕ) :
    (pathMeasure Q z₀).map (prefixHist T) = hist Q T z₀ := by
  have := isMarkovKernel_trajKernel Q
  have hP := isProbabilityMeasure_pathMeasure Q z₀
  induction T with
  | zero =>
    have := ex_8_8a Q 0
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    have hc : ∀ h : Fin 0 → Z, f h = f Fin.elim0 := fun h => by congr 1; funext i; exact i.elim0
    simp_rw [hc]
    simp
  | succ T ih =>
    have := ex_8_8a Q T
    refine Measure.ext_of_lintegral _ fun g hg => ?_
    let rT : (Π _ : Finset.Iic T, Z) → Fin T → Z := fun y i =>
      y ⟨i + 1, Finset.mem_Iic.2 (by omega)⟩
    have hrT : Measurable rT := measurable_pi_iff.2 fun _ => measurable_pi_apply _
    have hsplit : ∀ ω : ℕ → Z, prefixHist (T + 1) ω =
        Fin.snoc (rT (frestrictLe T ω)) (ω (T + 1)) := by
      intro ω
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [prefixHist]
      · simp [prefixHist, rT, frestrictLe]
    have hmeas : Measurable fun ω : ℕ → Z => (frestrictLe T ω, ω (T + 1)) :=
      (measurable_frestrictLe T).prodMk (measurable_pi_apply _)
    have hG : Measurable fun p : (Π _ : Finset.Iic T, Z) × Z => g (Fin.snoc (rT p.1) p.2) :=
      hg.comp ((measurable_snoc T).comp (hrT.prodMap measurable_id))
    have hkey := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => Z) (μ₀ := Measure.dirac z₀) (κ := trajKernel Q) (a := T)
    have hΦ : Measurable fun h : Fin T → Z => ∫⁻ z, g (Fin.snoc h z) ∂Q (lastState z₀ h) := by
      have := isMarkovKernel_nextKernel Q z₀ T
      exact (hg.comp (measurable_snoc T)).lintegral_kernel_prod_right' (κ := nextKernel Q z₀ T)
    rw [lintegral_map hg (measurable_prefixHist _), hist_succ_lintegral_last Q T z₀ hg, ← ih,
      lintegral_map hΦ (measurable_prefixHist _)]
    simp_rw [hsplit]
    rw [← lintegral_map (f := fun p : (Π _ : Finset.Iic T, Z) × Z => g (Fin.snoc (rT p.1) p.2))
      hG hmeas]
    change ∫⁻ p, _ ∂((pathMeasure Q z₀).map _) = _
    rw [pathMeasure] at *
    rw [← hkey, Measure.lintegral_compProd hG]
    have hprefix : ∀ ω : ℕ → Z, prefixHist T ω = rT (frestrictLe T ω) := fun ω => rfl
    simp_rw [hprefix]
    rw [← lintegral_map (f := fun y => ∫⁻ z, g (Fin.snoc (rT y) z) ∂Q (lastState z₀ (rT y)))
      (hΦ.comp hrT) (measurable_frestrictLe T)]
    cases T with
    | zero =>
      have h0 := pathMeasure_map_zero Q z₀
      rw [pathMeasure] at h0
      rw [h0, lintegral_dirac' _ (hG.lintegral_kernel_prod_right' (κ := trajKernel Q 0)),
        lintegral_dirac' (f := fun a => ∫⁻ z, g (Fin.snoc (rT a) z) ∂Q (lastState z₀ (rT a))) _
          (hΦ.comp hrT)]
      rfl
    | succ T =>
      refine lintegral_congr fun y => ?_
      rfl

/-- The book's `μ^∞(z₀, ·)` on the paths `(z₁, z₂, …)` of future states. -/
noncomputable def muInf (z₀ : Z) : Measure (ℕ → Z) :=
  (pathMeasure Q z₀).map fun ω n => ω (n + 1)

/-- `μ^∞(z₀, A₁ × ⋯ × A_T × Z × ⋯) = μᵀ(z₀, A₁ × ⋯ × A_T)` (SLP p. 222). -/
theorem muInf_marginal (z₀ : Z) (T : ℕ) :
    (muInf Q z₀).map (fun ω (i : Fin T) => ω i) = hist Q T z₀ := by
  have h1 : Measurable fun (ω : ℕ → Z) (i : Fin T) => ω (i : ℕ) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have h2 : Measurable fun (ω : ℕ → Z) (n : ℕ) => ω (n + 1) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  rw [muInf, Measure.map_map h1 h2, ← pathMeasure_marginal Q z₀ T]
  rfl

/-- **Uniqueness of `μ^∞`** (SLP p. 222): probability measures on paths with the same
finite-dimensional distributions are equal. -/
theorem pathMeasure_unique {ν ν' : Measure (ℕ → Z)} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν']
    (h : ∀ T, ν.map (fun ω (i : Fin T) => ω i) = ν'.map (fun ω (i : Fin T) => ω i)) : ν = ν' := by
  let C : Set (Set (ℕ → Z)) :=
    {S | ∃ T, ∃ B : Set (Fin T → Z), MeasurableSet B ∧ S = (fun ω (i : Fin T) => ω i) ⁻¹' B}
  have hproj : ∀ T, Measurable fun ω : ℕ → Z => fun i : Fin T => ω i := fun T =>
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  refine ext_of_generate_finite C ?_ ?_ ?_ (by simp)
  · apply le_antisymm
    · refine iSup_le fun n => MeasurableSpace.comap_le_iff_le_map.2 fun s hs => ?_
      refine MeasurableSpace.measurableSet_generateFrom ⟨n + 1, (fun x => x ⟨n, by omega⟩) ⁻¹' s,
        measurable_pi_apply _ hs, rfl⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨T, B, hB, rfl⟩
      exact hproj T hB
  · rintro _ ⟨T, B, hB, rfl⟩ _ ⟨T', B', hB', rfl⟩ _
    refine ⟨max T T', (fun x (i : Fin T) => x ⟨i, by omega⟩) ⁻¹' B ∩
      (fun x (i : Fin T') => x ⟨i, by omega⟩) ⁻¹' B', ?_, rfl⟩
    exact ((measurable_pi_iff.2 fun _ => measurable_pi_apply _) hB).inter
      ((measurable_pi_iff.2 fun _ => measurable_pi_apply _) hB')
  · rintro _ ⟨T, B, hB, rfl⟩
    rw [← Measure.map_apply (hproj T) hB, ← Measure.map_apply (hproj T) hB, h T]

/-- A **stochastic process** (SLP p. 223): an increasing sequence of sub-σ-algebras `𝓕ₜ` and
`𝓕ₜ`-measurable functions `σₜ`. -/
def IsStochasticProcess {Ω : Type*} [m : MeasurableSpace Ω] (F : ℕ → MeasurableSpace Ω)
    (σ : ℕ → Ω → Z) : Prop :=
  Monotone F ∧ (∀ t, F t ≤ m) ∧ ∀ t, Measurable[F t] (σ t)

/-- The σ-algebra of the first `t` coordinates of a path. -/
abbrev prefixSigma (t : ℕ) : MeasurableSpace (ℕ → Z) :=
  MeasurableSpace.comap (fun ω (i : Fin t) => ω i) inferInstance

theorem prefixSigma_mono : Monotone (prefixSigma (Z := Z)) := by
  intro s t hst
  refine MeasurableSpace.comap_le_iff_le_map.2 fun B hB => ?_
  refine ⟨(fun x (i : Fin s) => x ⟨i, by omega⟩) ⁻¹' B,
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _) hB, rfl⟩

theorem prefixSigma_le (t : ℕ) : prefixSigma (Z := Z) t ≤ MeasurableSpace.pi :=
  (measurable_pi_iff.2 fun _ => measurable_pi_apply _).comap_le

/-- The canonical process `z̃_t(ω) = ω_t` with `𝓕_t` generated by the first `t` coordinates is a
stochastic process (SLP p. 224). -/
theorem canonical_isStochasticProcess :
    IsStochasticProcess (prefixSigma (Z := Z) ∘ (· + 1)) fun t (ω : ℕ → Z) => ω t := by
  refine ⟨fun s t hst => prefixSigma_mono (Nat.add_le_add_right hst 1),
    fun t => prefixSigma_le _, fun t => ?_⟩
  change Measurable[prefixSigma (t + 1)] ((fun x : Fin (t + 1) → Z => x ⟨t, by omega⟩) ∘
    fun ω (i : Fin (t + 1)) => ω i)
  exact (measurable_pi_apply _).comp (comap_measurable _)

/-- **Exercise 8.6a–b: the Markov property with stationary transitions.** The joint law of the
history `(z₀, …, z_t)` and the next state `z_{t+1}` is the law of the history composed with
`Q(z_t, ·)`: the distribution of `z_{t+1}` given the past depends only on `z_t`, through the same
transition function `Q` at every date. -/
theorem ex_8_6ab (z₀ : Z) (t : ℕ) :
    (pathMeasure Q z₀).map (fun ω => (frestrictLe t ω, ω (t + 1))) =
      (pathMeasure Q z₀).map (frestrictLe t) ⊗ₘ trajKernel Q t := by
  have := isMarkovKernel_trajKernel Q
  exact (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure).symm

/-- **Exercise 8.6a–b, conditional form.** `Q(z_t, ·)` is a regular conditional distribution of
`z_{t+1}` given `(z₀, …, z_t)`. -/
theorem ex_8_6ab_condDistrib [StandardBorelSpace Z] [Nonempty Z] (z₀ : Z) (t : ℕ) :
    have := isProbabilityMeasure_pathMeasure Q z₀
    condDistrib (fun ω : ℕ → Z => ω (t + 1)) (frestrictLe t) (pathMeasure Q z₀)
      =ᵐ[(pathMeasure Q z₀).map (frestrictLe t)] trajKernel Q t := by
  have := isMarkovKernel_trajKernel Q
  have := isProbabilityMeasure_pathMeasure Q z₀
  exact Kernel.condDistrib_trajMeasure

/-- With shocks drawn independently from `λ`, `μᵗ(z₀, ·)` does not depend on `z₀`. -/
theorem hist_const (lam : Measure Z) [IsProbabilityMeasure lam] (t : ℕ) (z₀ z₀' : Z) :
    hist (Kernel.const Z lam) t z₀ = hist (Kernel.const Z lam) t z₀' := by
  cases t with
  | zero => rfl
  | succ t => rw [hist_succ_eq_cons, hist_succ_eq_cons]; rfl

/-- The window `(z_{t+1}, …, z_{t+n})` of a history of length `n + t`. -/
def window (t n : ℕ) (h : Fin (n + t) → Z) : Fin n → Z := fun i => h ⟨t + i, by omega⟩

theorem measurable_window (t n : ℕ) : Measurable (window (Z := Z) t n) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- **Exercise 8.6c.** If `Q(a, A) = λ(A)` for all `a`, the process is stationary: the law of
`(z_{t+1}, …, z_{t+n})` does not depend on `t`. -/
theorem ex_8_6c (lam : Measure Z) [IsProbabilityMeasure lam] (z₀ : Z) (t n : ℕ) :
    (hist (Kernel.const Z lam) (n + t) z₀).map (window t n) = hist (Kernel.const Z lam) n z₀ := by
  induction t generalizing z₀ with
  | zero =>
    rw [show window (Z := Z) 0 n = id by funext h i; simp [window], Measure.map_id]
    rfl
  | succ t ih =>
    have := ex_8_8a (Kernel.const Z lam) (n + t)
    change ((hist (Kernel.const Z lam) ((n + t) + 1) z₀).map (window (t + 1) n)) = _
    rw [hist_succ_eq_cons,
      Measure.map_map (measurable_window (t + 1) n) (measurable_cons (n + t))]
    have hw : window (t + 1) n ∘ (fun p : Z × (Fin (n + t) → Z) =>
        (Fin.cons p.1 p.2 : Fin (n + t + 1) → Z)) = window t n ∘ Prod.snd := by
      funext p i
      simp only [Function.comp_apply, window]
      have : (⟨t + 1 + i, by omega⟩ : Fin (n + t + 1)) = Fin.succ ⟨t + i, by omega⟩ := by
        ext
        simp
        omega
      rw [this, Fin.cons_succ]
    rw [hw, ← Measure.map_map (measurable_window _ _) measurable_snd]
    change Measure.map (window t n) ((_ ⊗ₘ _).snd) = _
    rw [Measure.snd_compProd]
    have hc : (hist (Kernel.const Z lam) (n + t)) ∘ₘ (Kernel.const Z lam z₀) =
        hist (Kernel.const Z lam) (n + t) z₀ := by
      ext A hA
      rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
      simp_rw [hist_const lam (n + t) _ z₀]
      simp
    rw [hc, ih]

/-- **Exercise 8.7a.** The σ-algebra `𝓕_t` consists of all sets determined by the first `t`
tosses: `{ω : (ω₁, …, ω_t) ∈ B}` for arbitrary `B ⊆ {H, T}ᵗ`. -/
theorem ex_8_7a (t : ℕ) (S : Set (ℕ → Bool)) :
    MeasurableSet[prefixSigma t] S ↔
      ∃ B : Set (Fin t → Bool), S = (fun ω (i : Fin t) => ω i) ⁻¹' B := by
  constructor
  · rintro ⟨B, -, rfl⟩
    exact ⟨B, rfl⟩
  · rintro ⟨B, rfl⟩
    exact ⟨B, (Set.to_countable B).measurableSet, rfl⟩

/-- The indicator of heads at toss `t` (`t ≥ 1`). -/
def headsAt (t : ℕ) (ω : ℕ → Bool) : ℝ := if t = 0 then 0 else if ω (t - 1) then 1 else 0

/-- **Exercise 8.7b.** `σ_t(ω) = 1` if the `t`-th toss is heads, `0` otherwise, is a stochastic
process. -/
theorem ex_8_7b : IsStochasticProcess (Z := ℝ) prefixSigma headsAt := by
  refine ⟨prefixSigma_mono, prefixSigma_le, fun t => ?_⟩
  unfold headsAt
  by_cases ht : t = 0
  · simp only [ht, ↓reduceIte]
    exact measurable_const
  · simp only [ht, ↓reduceIte]
    have hm : Measurable[prefixSigma t] fun ω : ℕ → Bool => ω (t - 1) := by
      change Measurable[prefixSigma t] ((fun x : Fin t → Bool => x ⟨t - 1, by omega⟩) ∘
        fun ω (i : Fin t) => ω i)
      exact (measurable_pi_apply _).comp (comap_measurable _)
    exact Measurable.ite (hm (measurableSet_singleton true)) measurable_const measurable_const

/-- **Exercise 8.7c.** The number of heads `g_t = Σ_{s ≤ t} σ_s` is a stochastic process. -/
theorem ex_8_7c : IsStochasticProcess (Z := ℝ) prefixSigma
    fun t ω => ∑ s ∈ Finset.range (t + 1), headsAt s ω := by
  refine ⟨prefixSigma_mono, prefixSigma_le, fun t => ?_⟩
  refine Finset.measurable_sum _ fun s hs => ?_
  exact (ex_8_7b.2.2 s).mono (prefixSigma_mono (by simp at hs; omega)) le_rfl

end StokeyLucasPrescott.MarkovProcesses
