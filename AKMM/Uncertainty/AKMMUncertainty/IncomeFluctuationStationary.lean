/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.IncomeFluctuation
import MarkovProcesses.ConvergenceStrong

/-!
# The stationary distribution of Figure 7.4(B) for Markov income

AKMM, §7.6, p. 215, Figure 7.4(B): "In the long run, the distribution will converge to a
stationary distribution." The state is `(a, y)` on `X = [a̲, b] × S` with `b ≥ ā` (assets above
`ā` reach `[a̲, ā]` in finite time, `imf_enters_ergodic`), and the transition is
`P((a, y), ·) = Σ_{y′} P(y, y′) δ_{(g(a, y), y′)}` (`imf_kernel`; a Markov kernel,
`imf_kernel_isMarkov`).

* An abstract hitting lemma (`imf_kernel_hit`): if the constraint binds on `[a̲, a̲ + δ)` in a
  state `y₀`, if above `a̲ + δ` some state lowers assets by at least `η > 0`, and if every
  transition probability is at least `p > 0`, then from every `(a, y)` the chain is at the atom
  `(a̲, y₀)` after `N` steps with probability at least `pᴺ`: Doeblin's condition with an atom,
  hence Miao's Condition M (Example 3.3.1), and by Theorem 3.3.1 there is a unique stationary
  distribution `μs` and `T*ⁿλ₀ → μs` in total variation, geometrically, for every initial `λ₀`
  (`imf_kernel_stationary`).
* **The model** (`imf_stationary`): under the standing assumptions, `r > 0`, the condition on
  `u` of `imf_abar_exists`, `u′` continuous and a transition matrix with positive entries, the
  hypotheses of the hitting lemma are proved from the decision rules (the constraint binds near
  `a̲` in the lowest-consumption state, `imf_binds_near_limit`; the lowest-consumption state
  dissaves, `imf_min_dissave`, uniformly on compacts by continuity), so for every `b ≥ ā` the
  distribution of `(a, y)` has a unique stationary distribution and converges to it from every
  initial distribution on `[a̲, b] × S`.

Departure: the book gives no argument. The usual monotone-mixing route (SLP Theorem 12.12, Miao
Theorem 3.3.5) needs a transition that is monotone in `(a, y)`, i.e. a savings rule increasing
in income and a stochastically monotone `P`, which Markov income does not imply. The binding
borrowing constraint supplies an accessible atom instead, which gives the stronger conclusion
(total variation, geometric rate).
-/

namespace AKMM.Uncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set Miao.MarkovProcesses
open scoped ENNReal

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The next state's asset level `g(a, y)` as a point of `[lo, hi]`. -/
def imf_next {lo hi : ℝ} (g : S → ℝ → ℝ) (hmaps : ∀ y a, a ∈ Icc lo hi → g y a ∈ Icc lo hi)
    (x : Icc lo hi × S) : Icc lo hi :=
  ⟨g x.2 x.1, hmaps _ _ x.1.2⟩

omit [Fintype S] in
theorem imf_next_measurable [Countable S] {lo hi : ℝ} {g : S → ℝ → ℝ}
    (hmaps : ∀ y a, a ∈ Icc lo hi → g y a ∈ Icc lo hi)
    (hmeas : ∀ y, Measurable fun a : Icc lo hi => g y a) : Measurable (imf_next g hmaps) :=
  (measurable_from_prod_countable_left (f := fun x : Icc lo hi × S => g x.2 x.1)
    fun y => hmeas y).subtype_mk

/-- AKMM, p. 215: the transition of `(a, y)`,
`P((a, y), ·) = Σ_{y′} P(y, y′) δ_{(g(a, y), y′)}` on `[lo, hi] × S`. -/
noncomputable def imf_kernel (P : S → S → ℝ) {lo hi : ℝ} (g : S → ℝ → ℝ)
    (hmaps : ∀ y a, a ∈ Icc lo hi → g y a ∈ Icc lo hi)
    (hmeas : ∀ y, Measurable fun a : Icc lo hi => g y a) :
    Kernel (Icc lo hi × S) (Icc lo hi × S) :=
  ⟨fun x => ∑ y', ENNReal.ofReal (P x.2 y') • Measure.dirac (imf_next g hmaps x, y'), by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hs]
    refine Finset.measurable_sum _ fun y' _ => ?_
    exact ((measurable_of_countable fun y => ENNReal.ofReal (P y y')).comp measurable_snd).mul
      ((measurable_const.indicator hs).comp
        ((imf_next_measurable hmaps hmeas).prodMk measurable_const))⟩

variable {P : S → S → ℝ} {lo hi : ℝ} {g : S → ℝ → ℝ}
  {hmaps : ∀ y a, a ∈ Icc lo hi → g y a ∈ Icc lo hi}
  {hmeas : ∀ y, Measurable fun a : Icc lo hi => g y a}

/-- Integrals against the transition: `∫ f dP((a, y), ·) = Σ_{y′} P(y, y′) f(g(a, y), y′)`. -/
theorem imf_kernel_lintegral (x : Icc lo hi × S) {f : Icc lo hi × S → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂(imf_kernel P g hmaps hmeas x) =
      ∑ y', ENNReal.ofReal (P x.2 y') * f (imf_next g hmaps x, y') := by
  change ∫⁻ z, f z ∂(∑ y', ENNReal.ofReal (P x.2 y') •
    Measure.dirac (imf_next g hmaps x, y')) = _
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

/-- AKMM, p. 215: the transition is a Markov kernel when `P` is a stochastic matrix. -/
theorem imf_kernel_isMarkov (hP : ∀ y y', 0 ≤ P y y') (hsum : ∀ y, ∑ y', P y y' = 1) :
    IsMarkovKernel (imf_kernel P g hmaps hmeas) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [← lintegral_one, imf_kernel_lintegral x measurable_const]
  simp only [mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun y' _ => hP x.2 y', hsum, ENNReal.ofReal_one]

/-- One step of the chain: `Pⁿ⁺¹((a, y), A) ≥ P(y, y′)Pⁿ((g(a, y), y′), A)`. -/
theorem imf_kpow_succ_ge (x : Icc lo hi × S) (y' : S) (n : ℕ) {A : Set (Icc lo hi × S)}
    (hA : MeasurableSet A) :
    ENNReal.ofReal (P x.2 y') * kpow (imf_kernel P g hmaps hmeas) n (imf_next g hmaps x, y') A ≤
      kpow (imf_kernel P g hmaps hmeas) (n + 1) x A := by
  change _ ≤ (kpow (imf_kernel P g hmaps hmeas) n ∘ₖ imf_kernel P g hmaps hmeas) x A
  rw [Kernel.comp_apply' _ _ _ hA, imf_kernel_lintegral x (Kernel.measurable_coe _ hA)]
  exact Finset.single_le_sum (f := fun y' => ENNReal.ofReal (P x.2 y') *
    kpow (imf_kernel P g hmaps hmeas) n (imf_next g hmaps x, y') A)
    (fun _ _ => bot_le) (Finset.mem_univ y')

/-- **The hitting lemma.** Suppose `lo ≤ hi`, every `P(y, y′) ≥ p > 0`, the borrowing
constraint binds on `[lo, lo + δ)` in state `y₀` (`g(a, y₀) = lo`), and for `a ≥ lo + δ` some
state lowers assets by at least `η > 0`. Then there is `N ≥ 1` with
`Pᴺ((a, y), {(lo, y₀)}) ≥ pᴺ` for every state `(a, y)`. -/
theorem imf_kernel_hit (hlo : lo ≤ hi) {p : ℝ} (hp : ∀ y y', p ≤ P y y') {y₀ : S} {δ η : ℝ}
    (hη : 0 < η) (h0 : ∀ a ∈ Icc lo hi, a < lo + δ → g y₀ a = lo)
    (hdesc : ∀ a ∈ Icc lo hi, lo + δ ≤ a → ∃ y, g y a ≤ a - η) :
    ∃ N, 1 ≤ N ∧ ∀ x, ENNReal.ofReal p ^ N ≤
      kpow (imf_kernel P g hmaps hmeas) N x {((⟨lo, left_mem_Icc.2 hlo⟩ : Icc lo hi), y₀)} := by
  set κ := imf_kernel P g hmaps hmeas
  set xs : Icc lo hi × S := (⟨lo, left_mem_Icc.2 hlo⟩, y₀)
  have hA : MeasurableSet ({xs} : Set (Icc lo hi × S)) := MeasurableSet.singleton xs
  have hstep : ∀ (x : Icc lo hi × S) (y' : S) (n : ℕ),
      ENNReal.ofReal p * kpow κ n (imf_next g hmaps x, y') {xs} ≤ kpow κ (n + 1) x {xs} :=
    fun x y' n => (mul_le_mul' (ENNReal.ofReal_le_ofReal (hp x.2 y')) le_rfl).trans
      (imf_kpow_succ_ge x y' n hA)
  -- the atom is absorbing along `y₀`
  have hnext0 : ∀ a : Icc lo hi, (a : ℝ) < lo + δ → imf_next g hmaps (a, y₀) = xs.1 :=
    fun a ha => Subtype.ext (h0 a a.2 ha)
  have hstay : ∀ n, ENNReal.ofReal p ^ n ≤ kpow κ n xs {xs} := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero]
      change _ ≤ (Kernel.id : Kernel (Icc lo hi × S) _) xs {xs}
      rw [Kernel.id_apply, Measure.dirac_apply_of_mem (Set.mem_singleton xs)]
    | succ n ih =>
      by_cases hδ : lo < lo + δ
      · have := hstep xs y₀ n
        rw [hnext0 xs.1 hδ] at this
        rw [pow_succ']
        exact (mul_le_mul' le_rfl ih).trans this
      · -- `δ ≤ 0`: the descent hypothesis applies at `lo`, which is impossible
        obtain ⟨y, hy⟩ := hdesc lo (left_mem_Icc.2 hlo) (by linarith)
        have := (hmaps y lo (left_mem_Icc.2 hlo)).1
        linarith
  -- descending induction on the height of the asset level
  have hC : ∀ k : ℕ, ∀ a : Icc lo hi, (a : ℝ) < lo + δ + k * η →
      ∃ y, ∀ n, k + 1 ≤ n → ENNReal.ofReal p ^ n ≤ kpow κ n (a, y) {xs} := by
    intro k
    induction k with
    | zero =>
      intro a ha
      refine ⟨y₀, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have := hstep (a, y₀) y₀ m
      rw [hnext0 a (by simpa using ha)] at this
      rw [pow_succ']
      exact (mul_le_mul' le_rfl (hstay m)).trans this
    | succ k ih =>
      intro a ha
      by_cases hlow : (a : ℝ) < lo + δ + k * η
      · obtain ⟨y, hy⟩ := ih a hlow
        exact ⟨y, fun n hn => hy n (by omega)⟩
      · push Not at hlow
        have hkη : 0 ≤ (k : ℝ) * η := by positivity
        obtain ⟨y, hy⟩ := hdesc a a.2 (by linarith)
        have hlt : (imf_next g hmaps (a, y) : ℝ) < lo + δ + k * η := by
          change g y a < _
          push_cast at ha
          linarith
        obtain ⟨y', hy'⟩ := ih _ hlt
        refine ⟨y, fun n hn => ?_⟩
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [pow_succ']
        exact (mul_le_mul' le_rfl (hy' m (by omega))).trans (hstep (a, y) y' m)
  obtain ⟨K, hK⟩ := exists_nat_gt ((hi - lo - δ) / η)
  have hK' : hi < lo + δ + K * η := by
    rw [div_lt_iff₀ hη] at hK; linarith
  refine ⟨K + 2, by omega, fun x => ?_⟩
  obtain ⟨y', hy'⟩ := hC K (imf_next g hmaps x) (lt_of_le_of_lt (imf_next g hmaps x).2.2 hK')
  rw [pow_succ']
  exact (mul_le_mul' le_rfl (hy' (K + 1) le_rfl)).trans (hstep x y' (K + 1))

/-- **AKMM, Fig. 7.4(B), p. 215 (abstract form): a unique stationary distribution and
convergence to it.** Under the hypotheses of `imf_kernel_hit` (with `P` stochastic and `S`
nonempty) there is a unique invariant probability measure `μs` of the transition, and for every
initial distribution `λ₀` the distributions `T*ⁿλ₀` converge to `μs` in total variation, with
`dTV(T*ⁿλ₀, μs) ≤ (1 − ε)^⌊n/N⌋` for some `0 < ε < 1` and `N ≥ 1`. -/
theorem imf_kernel_stationary [Nonempty S] (hP : ∀ y y', 0 ≤ P y y')
    (hsum : ∀ y, ∑ y', P y y' = 1) (hlo : lo ≤ hi) {p : ℝ} (hp0 : 0 < p)
    (hp : ∀ y y', p ≤ P y y') {y₀ : S} {δ η : ℝ} (hη : 0 < η)
    (h0 : ∀ a ∈ Icc lo hi, a < lo + δ → g y₀ a = lo)
    (hdesc : ∀ a ∈ Icc lo hi, lo + δ ≤ a → ∃ y, g y a ≤ a - η) :
    ∃ μs : Measure (Icc lo hi × S), IsProbabilityMeasure μs ∧
      adjointOp (imf_kernel P g hmaps hmeas) μs = μs ∧
      (∀ ν : Measure (Icc lo hi × S), IsProbabilityMeasure ν →
        adjointOp (imf_kernel P g hmaps hmeas) ν = ν → ν = μs) ∧
      (∃ ε : ℝ, ∃ N : ℕ, 0 < ε ∧ ε < 1 ∧ 1 ≤ N ∧ ∀ (l₀ : Measure (Icc lo hi × S))
        [IsProbabilityMeasure l₀] (n : ℕ),
          dTV (adjointOp (kpow (imf_kernel P g hmaps hmeas) n) l₀) μs ≤ (1 - ε) ^ (n / N)) ∧
      ∀ l₀ : Measure (Icc lo hi × S), IsProbabilityMeasure l₀ →
        ConvStrongly (fun n => adjointOp (kpow (imf_kernel P g hmaps hmeas) n) l₀) μs := by
  set κ := imf_kernel P g hmaps hmeas
  have hκ : IsMarkovKernel κ := imf_kernel_isMarkov hP hsum
  obtain ⟨N, hN, hhit⟩ := imf_kernel_hit (hmaps := hmaps) (hmeas := hmeas) hlo hp hη h0 hdesc
  set xs : Icc lo hi × S := (⟨lo, left_mem_Icc.2 hlo⟩, y₀)
  have hreal : ∀ x, p ^ N ≤ (kpow κ N x).real {xs} := by
    intro x
    have := gp_isMarkov_kpow (κ := κ) N
    have h1 := ENNReal.toReal_mono (measure_ne_top _ _) (hhit x)
    rwa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hp0.le] at h1
  set ε := p ^ N / 2
  have hε : 0 < ε := by positivity
  have hεlt : ∀ x, ε < (kpow κ N x).real {xs} := fun x => by
    have := hreal x; have : 0 < p ^ N := by positivity
    change p ^ N / 2 < _
    linarith
  have hε1 : ε < 1 := by
    have := gp_isMarkov_kpow (κ := κ) N
    have h1 := hεlt xs
    have h2 : (kpow κ N xs).real {xs} ≤ 1 := measureReal_le_one
    linarith
  have hM : ConditionMFor κ N ε := example_3_3_1 hN hε hεlt
  have hX : Nonempty (Icc lo hi × S) := ⟨xs⟩
  obtain ⟨μs, hμs, hinv, -, hrate⟩ := theorem_3_3_1_invariant hM
  have hlim : Tendsto (fun n : ℕ => (1 - ε) ^ (n / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).comp
      (Nat.tendsto_div_const_atTop (by omega))
  refine ⟨μs, hμs, hinv, fun ν hν hνinv => ?_, ⟨ε, N, hε, hε1, hN, hrate⟩, fun l₀ hl₀ => ?_⟩
  · have hfix : ∀ n, adjointOp (kpow κ n) ν = ν := fun n => by
      rw [← gp_adjointOp_iterate]; exact Function.iterate_fixed hνinv n
    have hle : ∀ n, dTV ν μs ≤ (1 - ε) ^ (n / N) := fun n => by
      have := hrate ν n; rwa [hfix n] at this
    have h0' : dTV ν μs ≤ 0 := ge_of_tendsto' hlim hle
    exact gp_eq_of_tvDist_eq_zero (by rw [gp_tvDist_eq_two_mul_dTV]; linarith)
  · exact squeeze_zero (fun n => by
      have := gp_isProb_adjoint (κ := κ) n l₀
      exact gp_dTV_nonneg _ _) (fun n => hrate l₀ n) hlim

/-- **AKMM, Fig. 7.4, pp. 214–215: the ergodic set and convergence to the stationary
distribution, for Markov income.** Under the standing assumptions of §7.6 (`imf_Standing`),
with `r > 0`, `u′` continuous, `β(1 + r)u′(c) < u′(c + D)` for large `c` (`D` bounding the income
spread; e.g. CRRA, `imf_crra_spread`) and a transition matrix with positive entries, there is
`ā ≥ a̲` with `g(a, y) < a` for `a ≥ ā`, and for every `b ≥ ā` the set `[a̲, b] × S` is invariant
and the transition of `(a, y)` on it has a unique stationary distribution `μs`, to which the
distribution converges in total variation from every initial distribution. -/
theorem imf_stationary [Nonempty S] {u u' : ℝ → ℝ} {β r : ℝ} {inc : S → ℝ} {abar : ℝ}
    {V V1 : S → ℝ → ℝ} (h : imf_Standing u u' β r P inc abar V V1 g)
    (hcont : ContinuousOn u' (Ioi 0)) (hr0 : 0 < r) {D : ℝ} (hD : ∀ y y', inc y - inc y' ≤ D)
    (hU : ∃ C, ∀ c, C ≤ c → 0 < c → β * (1 + r) * u' c < u' (c + D))
    (hPpos : ∀ y y', 0 < P y y') :
    ∃ ab, abar ≤ ab ∧ (∀ a, ab ≤ a → ∀ y, g y a < a) ∧ ∀ b, ab ≤ b →
      (∀ y a, a ∈ Icc abar b → g y a ∈ Icc abar b) ∧
      (∀ y, Measurable fun a : Icc abar b => g y a) ∧
      ∀ (hmaps : ∀ y a, a ∈ Icc abar b → g y a ∈ Icc abar b)
        (hmeas : ∀ y, Measurable fun a : Icc abar b => g y a),
        IsMarkovKernel (imf_kernel P g hmaps hmeas) ∧
        ∃ μs : Measure (Icc abar b × S), IsProbabilityMeasure μs ∧
          adjointOp (imf_kernel P g hmaps hmeas) μs = μs ∧
          (∀ ν : Measure (Icc abar b × S), IsProbabilityMeasure ν →
            adjointOp (imf_kernel P g hmaps hmeas) ν = ν → ν = μs) ∧
          ∀ l₀ : Measure (Icc abar b × S), IsProbabilityMeasure l₀ →
            ConvStrongly (fun n => adjointOp (kpow (imf_kernel P g hmaps hmeas) n) l₀) μs := by
  obtain ⟨ab, hab0, hab⟩ := imf_abar_exists h hr0 hD hU
  refine ⟨ab, hab0, hab, fun b hb => ?_⟩
  have hb0 : abar ≤ b := hab0.trans hb
  refine ⟨fun y a ha => ⟨(imf_feasible h ha.1).1, (imf_g_mono h y ha.1 ha.2).trans
      (hab b hb y).le⟩,
    fun y => ((imf_g_continuousOn h y).mono Icc_subset_Ici_self).domRestrict.measurable,
    fun hmaps hmeas => ⟨imf_kernel_isMarkov h.2.2.2.1 h.2.2.2.2.1, ?_⟩⟩
  obtain ⟨y₀, hy₀⟩ := imf_exists_min_state r inc g abar
  obtain ⟨δ, hδ, hbind⟩ := imf_binds_near_limit h hcont hy₀
  obtain ⟨z, hz⟩ := Finite.exists_min fun z : S × S => P z.1 z.2
  have hdesc' : ∃ η, 0 < η ∧ ∀ a ∈ Icc abar b, abar + δ ≤ a → ∃ y, g y a ≤ a - η := by
    by_cases hne : (Icc (abar + δ) b).Nonempty
    · set d : ℝ → ℝ := fun a => Finset.univ.sup' Finset.univ_nonempty fun y => a - g y a
        with hd
      have hdc : ContinuousOn d (Icc (abar + δ) b) :=
        ContinuousOn.finset_sup'_apply _ fun y _ => continuousOn_id.sub
          ((imf_g_continuousOn h y).mono fun a ha => show abar ≤ a by linarith [ha.1])
      obtain ⟨a₀, ha₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hdc
      have hd0 : 0 < d a₀ := by
        obtain ⟨ys, hys⟩ := imf_exists_min_state r inc g a₀
        have h1 := (imf_min_dissave h (by linarith [ha₀.1]) hys).2 (by linarith [ha₀.1])
        have h2 : a₀ - g ys a₀ ≤ d a₀ :=
          Finset.le_sup' (f := fun y => a₀ - g y a₀) (Finset.mem_univ ys)
        linarith
      refine ⟨d a₀, hd0, fun a ha haδ => ?_⟩
      obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun y => a - g y a
      have hle : d a₀ ≤ d a := hmin (show a ∈ Icc (abar + δ) b from ⟨haδ, ha.2⟩)
      refine ⟨y, ?_⟩
      have : d a = a - g y a := hy
      linarith
    · exact ⟨1, one_pos, fun a ha haδ => absurd ⟨a, haδ, ha.2⟩ hne⟩
  obtain ⟨η, hη, hdesc⟩ := hdesc'
  obtain ⟨μs, hμs, hinv, huniq, -, hconv⟩ := imf_kernel_stationary (hmaps := hmaps) (hmeas := hmeas)
    h.2.2.2.1 h.2.2.2.2.1 hb0 (hPpos z.1 z.2) (fun y y' => hz (y, y')) hη
    (fun a ha hlt => hbind a ha.1 hlt) hdesc
  exact ⟨μs, hμs, hinv, huniq, hconv⟩

end AKMM.Uncertainty
