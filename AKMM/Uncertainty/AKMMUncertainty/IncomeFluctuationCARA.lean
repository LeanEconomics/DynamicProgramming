/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.IncomeFluctuationZeroRate

/-!
# The bound `ā` of Figure 7.4 for CARA utility when `r = 0`

AKMM, §7.6, pp. 213–215, Figure 7.4(A)–(B). `IncomeFluctuationZeroRate` proves the bound `ā`
at `R = 1 + r = 1` under the spread condition `βu′(c) < u′(c + D)` for large `c`, and shows
that for CARA utility `u(c) = −e^{−γc}/γ` this condition fails when the income spread is large,
`β ≥ e^{−γD}` (`imf0_cara_spread_iff`). This module settles what happens then: **`ā` still
exists**. The spread condition is only sufficient, and at `r = 0` it is not needed at all.

* With `R = 1` the budget is `a′ = a + y − c`, so the consumer dissaves, `g(a, y) < a`, exactly
  when consumption exceeds income, `c(a, y) > y` (`imfc_dissave_iff`). Consumption is unbounded
  in assets in every state for any utility with `u′` continuous (`imf0_c_unbounded`, which uses
  only `β < 1`), so above some `ā` consumption exceeds the largest income in every state and
  `g(a, y) < a` for all `a ≥ ā` (`imfc_abar_exists`). No condition on the income spread or on the
  shape of `u` is used beyond the standing assumptions and continuity of `u′`.
* For CARA marginal utility `u′(c) = e^{−γc}` this holds at every spread
  (`imfc_abar_exists_cara`). With a large spread, `e^{−γD} ≤ β < 1`, the spread condition of
  `imf0_abar_exists` fails and yet `ā` exists for every solution `(V, g)`
  (`imfc_cara_large_spread`); along every income history assets enter `[a̲, ā]` in finite time
  and stay there, so they do not diverge (`imfc_cara_no_divergence`). The stationary
  distribution of correction 21 exists without the spread condition (`imfc_stationary`).
* CARA utility satisfies the utility parts of the standing assumptions, with `u′` continuous
  (`imfc_cara_utility`), and an explicit i.i.d. two-point economy (`γ = 1`, income `{0, 1}`, so
  `D = 1`, each with probability `1/2`, `β = 1/2`, `r = 0`) satisfies every hypothesis of
  `imf_Standing` other than the Bellman equation and has a large spread, `e^{−γD} ≤ β`
  (`imfc_cara_example_params`), so the results are not vacuous in their parameters.

Departure from the planned statement: the expected non-existence of `ā` for CARA with a large
spread (unbounded precautionary accumulation, as for CARA with `R > 1`) is false at `R = 1`, and
its opposite is proved. The results hold for every solution `(V, g)` of the Bellman equation
satisfying the standing assumptions; the existence of such a solution for CARA utility is not
constructed here.
-/

namespace AKMM.Uncertainty

open Filter Topology Set

variable {S : Type*} [Fintype S]
variable {u u' : ℝ → ℝ} {β r : ℝ} {P : S → S → ℝ} {inc : S → ℝ} {abar : ℝ} {V V1 g : S → ℝ → ℝ}

omit [Fintype S] in
/-- AKMM, p. 213, with `r = 0`: the budget is `a′ = a + y − c`, so the consumer dissaves,
`g(a, y) < a`, if and only if consumption exceeds income, `y < c(a, y)`. -/
theorem imfc_dissave_iff (hr0 : r = 0) (y : S) (a : ℝ) :
    g y a < a ↔ inc y < imf_c r inc g y a := by
  subst hr0
  unfold imf_c
  norm_num
  constructor <;> intro h <;> linarith

/-- **AKMM, Fig. 7.4(A), p. 214: the bound `ā` with `r = 0`, without any spread condition.**
Under the standing assumptions with `r = 0` (so `β < 1`) and `u′` continuous, for any
finite-state Markov income there is `ā ≥ a̲` with `g(a, y) < a` for all `a ≥ ā` and every `y`:
consumption is unbounded in assets and dissaving means `c(a, y) > y`. -/
theorem imfc_abar_exists (h : imf_Standing u u' β r P inc abar V V1 g) (hr0 : r = 0)
    (hcont : ContinuousOn u' (Ioi 0)) :
    ∃ ab, abar ≤ ab ∧ ∀ a, ab ≤ a → ∀ y, g y a < a := by
  obtain ⟨A, hA, hcA⟩ := imf0_c_unbounded h hr0 hcont (∑ y, |inc y|)
  refine ⟨A, hA.le, fun a ha y => (imfc_dissave_iff (inc := inc) hr0 y a).2 ?_⟩
  have hB : inc y ≤ ∑ y, |inc y| := (le_abs_self _).trans (Finset.single_le_sum
    (f := fun y => |inc y|) (fun _ _ => abs_nonneg _) (Finset.mem_univ y))
  linarith [hcA a ha y]

/-- AKMM, p. 214 (CARA): `u(c) = −e^{−γc}/γ` with `γ > 0` has derivative `u′(c) = e^{−γc}`,
which is positive, strictly decreasing and continuous: the utility parts of the standing
assumptions `imf_Standing` and the continuity of `u′`. -/
theorem imfc_cara_utility {γ : ℝ} (hγ : 0 < γ) :
    (∀ c, 0 < c → HasDerivAt (fun x => -Real.exp (-(γ * x)) / γ) (Real.exp (-(γ * c))) c) ∧
      (∀ c, 0 < c → 0 < Real.exp (-(γ * c))) ∧
      StrictAntiOn (fun c => Real.exp (-(γ * c))) (Ioi 0) ∧
      ContinuousOn (fun c => Real.exp (-(γ * c))) (Ioi 0) := by
  refine ⟨fun c _ => ?_, fun c _ => Real.exp_pos _, fun a _ b _ hab => ?_,
    Continuous.continuousOn (by fun_prop)⟩
  · have h1 : HasDerivAt (fun x : ℝ => -(γ * x)) (-(γ * 1)) c :=
      ((hasDerivAt_id' c).const_mul γ).neg
    have h2 := (h1.exp.neg).div_const γ
    convert h2 using 1
    field_simp
  · exact Real.exp_lt_exp.2 (by nlinarith)

/-- **AKMM, Fig. 7.4(A), p. 214: the bound `ā` for CARA utility at `r = 0`, at every income
spread.** If `u′(c) = e^{−γc}`, then under the standing assumptions with `r = 0` there is
`ā ≥ a̲` with `g(a, y) < a` for all `a ≥ ā` and every income state `y`. -/
theorem imfc_abar_exists_cara (h : imf_Standing u u' β r P inc abar V V1 g) (hr0 : r = 0)
    {γ : ℝ} (hu' : ∀ c, 0 < c → u' c = Real.exp (-(γ * c))) :
    ∃ ab, abar ≤ ab ∧ ∀ a, ab ≤ a → ∀ y, g y a < a := by
  have hcont : ContinuousOn u' (Ioi 0) :=
    (Continuous.continuousOn (by fun_prop) : ContinuousOn (fun c => Real.exp (-(γ * c)))
      (Ioi 0)).congr fun c hc => hu' c hc
  exact imfc_abar_exists h hr0 hcont

/-- **AKMM, Fig. 7.4(A), p. 214: CARA with a large income spread (correction 22).** If
`u′(c) = e^{−γc}` and `e^{−γD} ≤ β`, the spread condition `βu′(c) < u′(c + D)` for large `c`
used by `imf0_abar_exists` fails, and nevertheless, for every solution `(V, g)` satisfying the
standing assumptions with `r = 0`, there is `ā ≥ a̲` with `g(a, y) < a` for all `a ≥ ā` and all
`y`: the condition is sufficient, not necessary, and a strong precautionary motive does not
make assets grow without bound when `R = 1`. -/
theorem imfc_cara_large_spread (h : imf_Standing u u' β r P inc abar V V1 g) (hr0 : r = 0)
    {γ D : ℝ} (hu' : ∀ c, 0 < c → u' c = Real.exp (-(γ * c)))
    (hβD : Real.exp (-(γ * D)) ≤ β) :
    (¬ ∃ C, ∀ c, C ≤ c → 0 < c → β * u' c < u' (c + D)) ∧
      ∃ ab, abar ≤ ab ∧ ∀ a, ab ≤ a → ∀ y, g y a < a := by
  refine ⟨?_, imfc_abar_exists_cara h hr0 hu'⟩
  rintro ⟨C, hC⟩
  have hcara : ∃ C, ∀ c, C ≤ c → 0 < c →
      β * Real.exp (-(γ * c)) < Real.exp (-(γ * (c + D))) := by
    refine ⟨max C (|D| + 1), fun c hc hc0 => ?_⟩
    have h1 := hC c ((le_max_left _ _).trans hc) hc0
    have hcD : 0 < c + D := by
      linarith [(le_max_right C (|D| + 1)).trans hc, neg_abs_le D]
    rwa [hu' c hc0, hu' (c + D) hcD] at h1
  exact absurd ((imf0_cara_spread_iff β γ D).1 hcara) (not_lt.2 hβD)

/-- **AKMM, Fig. 7.4(A), p. 214: with CARA utility and `r = 0` assets do not diverge**, whatever
the income spread. Under the standing assumptions with `r = 0` and `u′(c) = e^{−γc}` there is
`ā ≥ a̲` such that for every income history `y_t` and initial assets `a₀ ≥ a̲`, the assets
`a_{t+1} = g(a_t, y_t)` lie in `[a̲, ā]` from some date on. -/
theorem imfc_cara_no_divergence (h : imf_Standing u u' β r P inc abar V V1 g) (hr0 : r = 0)
    {γ : ℝ} (hu' : ∀ c, 0 < c → u' c = Real.exp (-(γ * c))) :
    ∃ ab, abar ≤ ab ∧ ∀ (ys : ℕ → S) (as : ℕ → ℝ), abar ≤ as 0 →
      (∀ t, as (t + 1) = g (ys t) (as t)) → ∃ T, ∀ t, T ≤ t → as t ∈ Icc abar ab := by
  obtain ⟨ab, hab0, hab⟩ := imfc_abar_exists_cara h hr0 hu'
  exact ⟨ab, hab0, fun ys as h0 hstep => imf_enters_ergodic h hab0 hab ys as h0 hstep⟩

/-- **AKMM, Fig. 7.4, pp. 214–215, with `r = 0`, without the spread condition: the ergodic set
and convergence to the stationary distribution.** Under the standing assumptions with `r = 0`,
`u′` continuous (e.g. CARA at any income spread) and a transition matrix with positive entries,
there is `ā ≥ a̲` with `g(a, y) < a` for `a ≥ ā`, and for every `b ≥ ā` the set `[a̲, b] × S` is
invariant and the transition of `(a, y)` on it has a unique stationary distribution `μs`, to
which the distribution converges in total variation from every initial distribution. -/
theorem imfc_stationary [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (h : imf_Standing u u' β r P inc abar V V1 g) (hr0 : r = 0)
    (hcont : ContinuousOn u' (Ioi 0)) (hPpos : ∀ y y', 0 < P y y') :
    ∃ ab, abar ≤ ab ∧ (∀ a, ab ≤ a → ∀ y, g y a < a) ∧ ∀ b, ab ≤ b →
      (∀ y a, a ∈ Icc abar b → g y a ∈ Icc abar b) ∧
      (∀ y, Measurable fun a : Icc abar b => g y a) ∧
      ∀ (hmaps : ∀ y a, a ∈ Icc abar b → g y a ∈ Icc abar b)
        (hmeas : ∀ y, Measurable fun a : Icc abar b => g y a),
        ProbabilityTheory.IsMarkovKernel (imf_kernel P g hmaps hmeas) ∧
        ∃ μs : MeasureTheory.Measure (Icc abar b × S), MeasureTheory.IsProbabilityMeasure μs ∧
          Miao.MarkovProcesses.adjointOp (imf_kernel P g hmaps hmeas) μs = μs ∧
          (∀ ν : MeasureTheory.Measure (Icc abar b × S), MeasureTheory.IsProbabilityMeasure ν →
            Miao.MarkovProcesses.adjointOp (imf_kernel P g hmaps hmeas) ν = ν → ν = μs) ∧
          ∀ l₀ : MeasureTheory.Measure (Icc abar b × S), MeasureTheory.IsProbabilityMeasure l₀ →
            Miao.MarkovProcesses.ConvStrongly (fun n => Miao.MarkovProcesses.adjointOp
              (Miao.MarkovProcesses.kpow (imf_kernel P g hmaps hmeas) n) l₀) μs := by
  obtain ⟨ab, hab0, hab⟩ := imfc_abar_exists h hr0 hcont
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

/-- AKMM, p. 214: an explicit i.i.d. two-point CARA economy with a large income spread. With
`γ = 1`, income `y ∈ {0, 1}` (spread `D = 1`) drawn i.i.d. with probabilities `1/2`, `β = 1/2`
and `r = 0`, every hypothesis of `imf_Standing` other than the Bellman equation holds for
`u(c) = −e^{−c}`, `u′` is continuous, the transition probabilities are positive, and the spread
is large, `e^{−γD} ≤ β`, so the spread condition fails (`imfc_cara_large_spread`). -/
theorem imfc_cara_example_params :
    (0 : ℝ) ≤ 1 / 2 ∧ (0 : ℝ) < 1 + 0 ∧ (1 / 2 : ℝ) * (1 + 0) < 1 ∧
      (∀ y y' : Fin 2, (0 : ℝ) ≤ (fun _ _ => (1 / 2 : ℝ)) y y') ∧
      (∀ y : Fin 2, ∑ y' : Fin 2, (fun _ _ => (1 / 2 : ℝ)) y y' = 1) ∧
      (∀ y y' : Fin 2, (0 : ℝ) < (fun _ _ => (1 / 2 : ℝ)) y y') ∧
      (∀ y y' : Fin 2, (![0, 1] : Fin 2 → ℝ) y - (![0, 1] : Fin 2 → ℝ) y' ≤ 1) ∧
      (![0, 1] : Fin 2 → ℝ) 1 - (![0, 1] : Fin 2 → ℝ) 0 = 1 ∧
      (∀ c, 0 < c → HasDerivAt (fun x => -Real.exp (-(1 * x)) / 1) (Real.exp (-(1 * c))) c) ∧
      (∀ c, 0 < c → 0 < Real.exp (-(1 * c))) ∧
      StrictAntiOn (fun c => Real.exp (-(1 * c))) (Ioi 0) ∧
      ContinuousOn (fun c => Real.exp (-(1 * c))) (Ioi 0) ∧
      Real.exp (-(1 * 1)) ≤ 1 / 2 := by
  obtain ⟨hd, hp, ha, hc⟩ := imfc_cara_utility (γ := 1) one_pos
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨by norm_num, by norm_num, by norm_num, fun _ _ => by norm_num, fun _ => ?_,
    fun _ _ => by norm_num, fun y y' => ?_, by simp, hd, hp, ha, hc, ?_⟩
  · simp only [Fin.sum_univ_two]; norm_num
  · fin_cases y <;> fin_cases y' <;> simp
  · rw [one_mul, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le two_pos he

end AKMM.Uncertainty
