/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.IncomeFluctuationExample

/-!
# The bound `ā` of Figure 7.4 when `r = 0`

AKMM, §7.6, pp. 213–215, Figure 7.4(A)–(B). `IncomeFluctuation` proves the bound `ā` (with
`g(a, y) < a` for `a ≥ ā` in every income state) for `r > 0` under a condition on `u` and for
`r < 0` without one. This module covers `R = 1 + r = 1`, where the only reason to dissave at
high wealth is the impatience gap `β < 1` (the case of Schechtman and Escudero (1977) for i.i.d.
income, and of Huggett (1993) for a two-state Markov chain with CRRA utility). Finite-state
Markov income, the standing assumptions `imf_Standing` with `r = 0`, and `u′` continuous.

* The proof for `r > 0` used `r > 0` only to make consumption unbounded in assets
  (`imf_c_unbounded`: wealth grows at rate `r`). For `r = 0` consumption is still unbounded in
  every state (`imf0_c_unbounded`), by a direct argument: if consumption stayed below its least
  upper bound `L` in some state, then for large assets the savings `g(a, y) = a + y − c(a, y)`
  are large and positive, consumption tomorrow is close to `L` or above in every state, and the
  Euler equation `u′(c) = βE[u′(c′)|y]` would give `u′(L) ≤ βu′(L − ε) → βu′(L) < u′(L)`.
* With the spread condition `βu′(c) < u′(c + D)` for large `c` (`D` bounding the income spread)
  the Euler argument of `imf_abar_exists` then gives `ā` (`imf0_abar_exists`), and the
  stationary-distribution theorem extends: `imf0_stationary` is `imf_stationary` for `r = 0`.
* The spread condition holds whenever `u′(c + D)/u′(c) → 1` (`imf0_spread_of_ratio`), so for
  CRRA (and log) utility, where `ā` therefore exists for every interest rate with
  `β(1 + r) < 1` (`imf0_abar_exists_crra`, combining the three cases).
* For CARA utility `u′(c) = e^{−γc}` the ratio is the constant `e^{−γD}`
  (`imf0_cara_ratio`), and the spread condition holds if and only if `β < e^{−γD}`
  (`imf0_cara_spread_iff`): it fails when the spread is large, `γD ≥ −log β`. Whether `ā` then
  fails to exist (assets drifting without bound, the Schechtman–Escudero CARA case) is not proved
  here: only the failure of the proof's condition.
* A solved instance with `r = 0` (the economy of `IncomeFluctuationExample` with `q = 1`):
  `imf0_example_bellman`, `imf0_example_standing`, `imf0_example_hyps`,
  `imf0_example_stationary`.
-/

namespace AKMM.Uncertainty

open Filter Topology Set

variable {S : Type*} [Fintype S]
variable {u u' : ℝ → ℝ} {β r : ℝ} {P : S → S → ℝ} {inc : S → ℝ} {abar : ℝ} {V V1 g : S → ℝ → ℝ}

/-- **AKMM, p. 214, with `r = 0`: consumption is unbounded in assets in every state.** With
`R = 1`, `u′` continuous and the standing assumptions (`β < 1`), for every `C` there is `A` with
`c(a, y) > C` for all `a ≥ A` and all `y`. -/
theorem imf0_c_unbounded (h : imf_Standing u u' β r P inc abar V V1 g) (hr0 : r = 0)
    (hcont : ContinuousOn u' (Ioi 0)) (C : ℝ) :
    ∃ A, abar < A ∧ ∀ a, A ≤ a → ∀ y, C < imf_c r inc g y a := by
  subst hr0
  obtain ⟨hβ, -, hβr, hP, hsum, -, -, hpos, hanti, -, -⟩ := id h
  have hβ1 : β < 1 := by linarith
  by_contra hcon
  push Not at hcon
  -- some state has consumption bounded by `C` on all of `[a̲, ∞)`
  have hex : ∃ y, ∀ a, abar ≤ a → imf_c 0 inc g y a ≤ C := by
    by_contra hall
    push Not at hall
    choose ay hay using hall
    obtain ⟨a, ha, y, hy⟩ := hcon (|abar| + 1 + ∑ y, |ay y|) (by
      have : 0 ≤ ∑ y, |ay y| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith [le_abs_self abar])
    have h1 : ay y ≤ a := by
      have : |ay y| ≤ ∑ y, |ay y| := Finset.single_le_sum (f := fun y => |ay y|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ y)
      linarith [le_abs_self (ay y), abs_nonneg abar]
    linarith [imf_c_mono h y (hay y).1 h1, (hay y).2]
  classical
  set Bs := Finset.univ.filter fun y => ∀ a, abar ≤ a → imf_c 0 inc g y a ≤ C
  set L : S → ℝ := fun y => sSup (imf_c 0 inc g y '' Ici abar)
  have hBne : Bs.Nonempty := by
    obtain ⟨y, hy⟩ := hex
    exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ y, hy⟩⟩
  obtain ⟨ys, hysB, hmin⟩ := Finset.exists_min_image Bs L hBne
  have hysC : ∀ a, abar ≤ a → imf_c 0 inc g ys a ≤ C := (Finset.mem_filter.1 hysB).2
  have hne : ∀ y, (imf_c 0 inc g y '' Ici abar).Nonempty :=
    fun y => ⟨_, mem_image_of_mem _ (mem_Ici.2 le_rfl)⟩
  have hbddB : ∀ y ∈ Bs, BddAbove (imf_c 0 inc g y '' Ici abar) := by
    intro y hy
    refine ⟨C, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact (Finset.mem_filter.1 hy).2 a ha
  have hcL : ∀ a, abar ≤ a → imf_c 0 inc g ys a ≤ L ys :=
    fun a ha => le_csSup (hbddB ys hysB) (mem_image_of_mem _ (mem_Ici.2 ha))
  have hLC : L ys ≤ C := csSup_le (hne ys) (by rintro _ ⟨a, ha, rfl⟩; exact hysC a ha)
  have hL0 : 0 < L ys := (imf_feasible h (y := ys) le_rfl).2.trans_le (hcL abar le_rfl)
  -- continuity at `L`: `βu′(x) < u′(L)` near `L`
  have hcL' : ContinuousAt u' (L ys) := hcont.continuousAt (Ioi_mem_nhds hL0)
  have hev : ∀ᶠ x in 𝓝 (L ys), β * u' x < u' (L ys) := by
    have : Tendsto (fun x => β * u' x) (𝓝 (L ys)) (𝓝 (β * u' (L ys))) :=
      tendsto_const_nhds.mul hcL'
    have hlt : β * u' (L ys) < u' (L ys) := by nlinarith [hpos _ hL0]
    exact this.eventually (gt_mem_nhds hlt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set e := min (ε / 2) (L ys / 2)
  have he0 : 0 < e := lt_min (by linarith) (by linarith)
  have hx0 : 0 < L ys - e := by linarith [min_le_right (ε / 2) (L ys / 2)]
  have hβx : β * u' (L ys - e) < u' (L ys) := by
    refine hball ?_
    rw [Real.dist_eq, show L ys - e - L ys = -e by ring, abs_neg, abs_of_pos he0]
    linarith [min_le_left (ε / 2) (L ys / 2)]
  -- every state reaches consumption above `L − e`
  have hreach : ∀ y', ∃ a', abar ≤ a' ∧ L ys - e < imf_c 0 inc g y' a' := by
    intro y'
    by_cases hy' : y' ∈ Bs
    · have hle : L ys - e < L y' := by linarith [hmin y' hy']
      obtain ⟨_, ⟨a', ha', rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (hne y') hle
      exact ⟨a', ha', hlt⟩
    · have : ¬ ∀ a, abar ≤ a → imf_c 0 inc g y' a ≤ C := fun hc =>
        hy' (Finset.mem_filter.2 ⟨Finset.mem_univ y', hc⟩)
      push Not at this
      obtain ⟨a', ha', hlt⟩ := this
      exact ⟨a', ha', by linarith⟩
  choose ay hay using hreach
  set A0 := |abar| + ∑ y', |ay y'|
  have hA0 : ∀ y', ay y' ≤ A0 := fun y' => by
    have : |ay y'| ≤ ∑ y', |ay y'| := Finset.single_le_sum (f := fun y => |ay y|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ y')
    linarith [le_abs_self (ay y'), abs_nonneg abar]
  have hA0b : abar ≤ A0 := by
    have : 0 ≤ ∑ y', |ay y'| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self abar]
  set a := max abar (A0 + C - inc ys + 1)
  have ha : abar ≤ a := le_max_left _ _
  have hga : A0 + 1 ≤ g ys a := by
    rw [imf_g_eq h ys a]
    have h1 := hysC a ha
    have h2 : A0 + C - inc ys + 1 ≤ a := le_max_right _ _
    linarith
  have heq := imf_euler_eq h (y := ys) ha (by linarith)
  have hsumle : ∑ y', P ys y' * u' (imf_c 0 inc g y' (g ys a)) ≤ u' (L ys - e) := by
    calc ∑ y', P ys y' * u' (imf_c 0 inc g y' (g ys a)) ≤ ∑ y', P ys y' * u' (L ys - e) := by
          refine Finset.sum_le_sum fun y' _ => mul_le_mul_of_nonneg_left ?_ (hP ys y')
          have h1 := imf_c_mono h y' (hay y').1 (show ay y' ≤ g ys a by linarith [hA0 y'])
          have h2 := (hay y').2
          exact (hanti hx0 (by simp only [mem_Ioi]; linarith) (by linarith)).le
      _ = u' (L ys - e) := by rw [← Finset.sum_mul, hsum, one_mul]
  have hlow : u' (L ys) ≤ u' (imf_c 0 inc g ys a) :=
    hanti.antitoneOn (imf_feasible h (y := ys) ha).2 hL0 (hcL a ha)
  have : u' (imf_c 0 inc g ys a) ≤ β * u' (L ys - e) := by
    rw [heq, add_zero, one_mul]
    exact mul_le_mul_of_nonneg_left hsumle hβ
  linarith

/-- **AKMM, Fig. 7.4(A), p. 214: the bound `ā` with `r = 0`** (Markov income). If `D` bounds the
income spread, `u′` is continuous and `βu′(c) < u′(c + D)` for all large `c`, there is `ā ≥ a̲`
such that `g(a, y) < a` for every `a ≥ ā` and every income state `y`. -/
theorem imf0_abar_exists (h : imf_Standing u u' β r P inc abar V V1 g) (hr0 : r = 0)
    (hcont : ContinuousOn u' (Ioi 0)) {D : ℝ} (hD : ∀ y y', inc y - inc y' ≤ D)
    (hU : ∃ C, ∀ c, C ≤ c → 0 < c → β * u' c < u' (c + D)) :
    ∃ ab, abar ≤ ab ∧ ∀ a, ab ≤ a → ∀ y, g y a < a := by
  obtain ⟨C, hC⟩ := hU
  obtain ⟨A, hA, hcA⟩ := imf0_c_unbounded h hr0 hcont C
  subst hr0
  refine ⟨A, hA.le, fun a ha y => ?_⟩
  by_contra hge
  push Not at hge
  have hS : Nonempty S := ⟨y⟩
  have hβ := h.1
  have haa : abar ≤ a := hA.le.trans ha
  obtain ⟨ys, hys⟩ := imf_exists_min_state 0 inc g a
  have hgs := (imf_min_dissave h haa hys).1
  have hcs := imf_feasible h (y := ys) haa
  have hcy := imf_feasible h (y := y) haa
  have hgap : imf_c 0 inc g y a ≤ imf_c 0 inc g ys a + D := by
    have := hD y ys
    unfold imf_c
    norm_num
    linarith
  have heq := imf_euler_eq h (y := y) haa (by linarith)
  have hle := imf_next_mu_le h haa hys hge
  have h1 : u' (imf_c 0 inc g y a) ≤ β * u' (imf_c 0 inc g ys a) := by
    rw [heq, add_zero, one_mul]; exact mul_le_mul_of_nonneg_left hle hβ
  have hDnn : 0 ≤ D := by linarith [hD y y]
  have h2 : u' (imf_c 0 inc g ys a + D) ≤ u' (imf_c 0 inc g y a) :=
    h.2.2.2.2.2.2.2.2.1.antitoneOn hcy.2 (by simp only [mem_Ioi]; linarith [hcs.2]) hgap
  have h3 := hC _ (hcA a ha ys).le hcs.2
  linarith

/-- AKMM, p. 214, the condition of `imf0_abar_exists`: if `u′ > 0`, `β < 1` and
`u′(c + D)/u′(c) → 1` as `c → ∞` (marginal utility at high consumption is insensitive to the
income spread), then `βu′(c) < u′(c + D)` for all large `c`. -/
theorem imf0_spread_of_ratio (hpos : ∀ c, 0 < c → 0 < u' c) (hβ1 : β < 1) {D : ℝ}
    (hlim : Tendsto (fun c => u' (c + D) / u' c) atTop (𝓝 1)) :
    ∃ C, ∀ c, C ≤ c → 0 < c → β * u' c < u' (c + D) := by
  obtain ⟨C, hC⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds hβ1))
  refine ⟨C, fun c hc hc0 => ?_⟩
  have h1 := hC c hc
  rwa [lt_div_iff₀ (hpos c hc0)] at h1

/-- **AKMM, Fig. 7.4(A), p. 214: the bound `ā` for CRRA utility at every interest rate.** With
`u′(c) = c^{−σ}`, `σ > 0` (log utility is `σ = 1`), under the standing assumptions (so
`β(1 + r) < 1`) there is `ā ≥ a̲` with `g(a, y) < a` for all `a ≥ ā` and all `y`, whether `r > 0`
(`imf_abar_exists`), `r = 0` (`imf0_abar_exists`) or `r < 0` (`imf_abar_exists_neg`). -/
theorem imf0_abar_exists_crra (h : imf_Standing u u' β r P inc abar V V1 g) {σ : ℝ}
    (hσ : 0 < σ) (hu' : ∀ c, 0 < c → u' c = c ^ (-σ)) :
    ∃ ab, abar ≤ ab ∧ ∀ a, ab ≤ a → ∀ y, g y a < a := by
  set D := 2 * ∑ y, |inc y|
  have hB : ∀ y, |inc y| ≤ ∑ y, |inc y| := fun y => Finset.single_le_sum
    (f := fun y => |inc y|) (fun _ _ => abs_nonneg _) (Finset.mem_univ y)
  have hD : ∀ y y', inc y - inc y' ≤ D := fun y y' => by
    linarith [le_abs_self (inc y), neg_abs_le (inc y'), hB y, hB y']
  have hD0 : 0 ≤ D := by
    have : 0 ≤ ∑ y, |inc y| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hspread : ∀ k, k < 1 → ∃ C, ∀ c, C ≤ c → 0 < c → k * u' c < u' (c + D) := by
    intro k hk
    obtain ⟨C, hC⟩ := imf_crra_spread hσ hk hD0
    refine ⟨C, fun c hc hc0 => ?_⟩
    rw [hu' c hc0, hu' (c + D) (by linarith)]
    exact hC c hc hc0
  rcases lt_trichotomy r 0 with hr | hr | hr
  · exact imf_abar_exists_neg h hr
  · have hcont : ContinuousOn u' (Ioi 0) :=
      (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)).congr fun c hc => hu' c hc
    have hβ1 : β < 1 := by have := h.2.2.1; rw [hr] at this; linarith
    exact imf0_abar_exists h hr hcont hD (hspread β hβ1)
  · exact imf_abar_exists h hr hD (hspread _ h.2.2.1)

/-- AKMM, p. 214 (CARA): for `u′(c) = e^{−γc}` the marginal utility ratio is constant,
`u′(c + D)/u′(c) = e^{−γD}`, so it tends to `1` only if `γD = 0`. -/
theorem imf0_cara_ratio (γ D c : ℝ) :
    Real.exp (-(γ * (c + D))) / Real.exp (-(γ * c)) = Real.exp (-(γ * D)) := by
  rw [← Real.exp_sub]
  ring_nf

/-- **AKMM, p. 214 (CARA): the spread condition of `imf0_abar_exists` holds if and only if
`β < e^{−γD}`.** For `u′(c) = e^{−γc}`, `βu′(c) < u′(c + D)` for all large `c` iff
`β < e^{−γD}`; with a large spread, `γD ≥ −log β`, the condition fails at every `c`. -/
theorem imf0_cara_spread_iff (β γ D : ℝ) :
    (∃ C, ∀ c, C ≤ c → 0 < c → β * Real.exp (-(γ * c)) < Real.exp (-(γ * (c + D)))) ↔
      β < Real.exp (-(γ * D)) := by
  have key : ∀ c, Real.exp (-(γ * (c + D))) = Real.exp (-(γ * c)) * Real.exp (-(γ * D)) :=
    fun c => by rw [← Real.exp_add]; ring_nf
  constructor
  · rintro ⟨C, hC⟩
    have h1 := hC (max C 1) (le_max_left _ _) (lt_of_lt_of_le one_pos (le_max_right _ _))
    rw [key] at h1
    have hE := Real.exp_pos (-(γ * max C 1))
    nlinarith
  · intro hk
    refine ⟨0, fun c _ _ => ?_⟩
    rw [key]
    have hE := Real.exp_pos (-(γ * c))
    nlinarith [mul_pos (sub_pos.2 hk) hE]

/-- **AKMM, Fig. 7.4, pp. 214–215, with `r = 0`: the ergodic set and convergence to the
stationary distribution, for Markov income.** `imf_stationary` for `R = 1`: under the standing
assumptions with `r = 0`, `u′` continuous, `βu′(c) < u′(c + D)` for large `c` (`D` bounding the
income spread; e.g. CRRA) and a transition matrix with positive entries, there is `ā ≥ a̲` with
`g(a, y) < a` for `a ≥ ā`, and for every `b ≥ ā` the set `[a̲, b] × S` is invariant and the
transition of `(a, y)` on it has a unique stationary distribution `μs`, to which the
distribution converges in total variation from every initial distribution. -/
theorem imf0_stationary [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (h : imf_Standing u u' β r P inc abar V V1 g) (hr0 : r = 0)
    (hcont : ContinuousOn u' (Ioi 0)) {D : ℝ} (hD : ∀ y y', inc y - inc y' ≤ D)
    (hU : ∃ C, ∀ c, C ≤ c → 0 < c → β * u' c < u' (c + D))
    (hPpos : ∀ y y', 0 < P y y') :
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
  obtain ⟨ab, hab0, hab⟩ := imf0_abar_exists h hr0 hcont hD hU
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

/-- The economy of `IncomeFluctuationExample` with `r = 0` (`q = 1`): `(V, g)` with `g = 0` still
solve the Bellman equation of p. 213 with `β = 1/4`, `q = 1/(1 + 0)`, `a̲ = 0`. -/
theorem imf0_example_bellman :
    im_Bellman imf_exU (1 / 4) (1 / (1 + 0)) imf_exP imf_exInc 0 imf_exV imf_exG := by
  intro y a ha
  obtain ⟨hy1, hy2⟩ := imf_exInc_ge y
  refine ⟨⟨le_rfl, by simp only [imf_exG]; linarith⟩, ?_, fun a' ha' hfeas => ?_⟩
  · simp only [imf_exV, imf_exG, Fin.sum_univ_two, zero_add]
    fin_cases y <;>
      simp [imf_exP, imf_exW, imf_exInc] <;> ring
  · simp only [show (1 : ℝ) / (1 + 0) = 1 by norm_num, one_mul] at hfeas ⊢
    have hc0 : 0 < a + imf_exInc y := by linarith
    have t0 := imf_exU_tangent (x := a + imf_exInc y - a') (by linarith) hc0
    have t1 := imf_exU_tangent (x := a' + 1) (x₀ := 1) (by linarith) one_pos
    have t2 := imf_exU_tangent (x := a' + 2) (x₀ := 2) (by linarith) two_pos
    have hneg : (a + imf_exInc y - a' - (a + imf_exInc y)) / (a + imf_exInc y) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hc0.le
    simp only [imf_exV, Fin.sum_univ_two]
    fin_cases y <;>
      simp only [imf_exP, imf_exInc, imf_exW, Fin.zero_eta, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one] at * <;>
      norm_num at t1 t2 ⊢ <;> linarith

/-- The `r = 0` economy satisfies the standing assumptions of §7.6 (`imf_Standing`), with
`β(1 + r) = 1/4 < 1`. -/
theorem imf0_example_standing :
    imf_Standing imf_exU imf_exDU (1 / 4) 0 imf_exP imf_exInc 0 imf_exV imf_exV1 imf_exG := by
  obtain ⟨-, -, -, hP, hsum, -, hu, hpos, hanti, hV, hVa⟩ := imf_example_standing
  exact ⟨by norm_num, by norm_num, by norm_num, hP, hsum, imf0_example_bellman, hu, hpos,
    hanti, hV, hVa⟩

/-- The `r = 0` economy satisfies the extra hypotheses of `imf0_stationary`: `u′` continuous,
income spread `D = 1`, `βu′(c) < u′(c + 1)` for `c ≥ 2` (here `u′(c + 1)/u′(c) → 1`), positive
transition probabilities. -/
theorem imf0_example_hyps :
    ContinuousOn imf_exDU (Ioi 0) ∧ (∀ y y', imf_exInc y - imf_exInc y' ≤ 1) ∧
      (∃ C, ∀ c, C ≤ c → 0 < c → 1 / 4 * imf_exDU c < imf_exDU (c + 1)) ∧
      ∀ y y', 0 < imf_exP y y' := by
  obtain ⟨hc, -, hD, -, hP⟩ := imf_example_hyps
  refine ⟨hc, hD, ⟨2, fun c hc hc0 => ?_⟩, hP⟩
  unfold imf_exDU
  have h1 : c⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le two_pos hc
  have h2 : 0 < (c + 1)⁻¹ := by positivity
  linarith

/-- **AKMM, Fig. 7.4, pp. 214–215, for the `r = 0` example**: `imf0_stationary` applies, so
there is an upper bound `ā` and, on every `[0, b] × {1, 2}` with `b ≥ ā`, a unique stationary
distribution to which the distribution of `(a, y)` converges in total variation. -/
theorem imf0_example_stationary :
    ∃ ab, 0 ≤ ab ∧ (∀ a, ab ≤ a → ∀ y, imf_exG y a < a) ∧ ∀ b, ab ≤ b →
      (∀ y a, a ∈ Icc 0 b → imf_exG y a ∈ Icc 0 b) ∧
      (∀ y, Measurable fun a : Icc (0 : ℝ) b => imf_exG y a) ∧
      ∀ (hmaps : ∀ y a, a ∈ Icc 0 b → imf_exG y a ∈ Icc 0 b)
        (hmeas : ∀ y, Measurable fun a : Icc (0 : ℝ) b => imf_exG y a),
        ProbabilityTheory.IsMarkovKernel (imf_kernel imf_exP imf_exG hmaps hmeas) ∧
        ∃ μs : MeasureTheory.Measure (Icc (0 : ℝ) b × Fin 2),
          MeasureTheory.IsProbabilityMeasure μs ∧
          Miao.MarkovProcesses.adjointOp (imf_kernel imf_exP imf_exG hmaps hmeas) μs = μs ∧
          (∀ ν : MeasureTheory.Measure (Icc (0 : ℝ) b × Fin 2),
            MeasureTheory.IsProbabilityMeasure ν →
            Miao.MarkovProcesses.adjointOp (imf_kernel imf_exP imf_exG hmaps hmeas) ν = ν →
              ν = μs) ∧
          ∀ l₀ : MeasureTheory.Measure (Icc (0 : ℝ) b × Fin 2),
            MeasureTheory.IsProbabilityMeasure l₀ →
            Miao.MarkovProcesses.ConvStrongly (fun n => Miao.MarkovProcesses.adjointOp
              (Miao.MarkovProcesses.kpow (imf_kernel imf_exP imf_exG hmaps hmeas) n) l₀) μs := by
  obtain ⟨hc, hD, hU, hP⟩ := imf0_example_hyps
  exact imf0_stationary imf0_example_standing rfl hc hD hU hP

end AKMM.Uncertainty
