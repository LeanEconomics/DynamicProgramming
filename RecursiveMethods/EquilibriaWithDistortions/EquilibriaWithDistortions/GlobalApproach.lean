/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.GlobalCrossing

/-!
# A global approach based on first-order conditions: set-up (SLP §18.3, pp. 554–558)

The one-sector growth model with a flat tax `θ` on capital income whose proceeds are thrown
away. After-tax income is `ψ(k) = f(k) − θ k f′(k)` and a (continuous) competitive equilibrium is
a savings function `g` with (§18.3 (1), p. 554)
  `U′[ψ(k) − g(k)] = β(1 − θ) f′[g(k)] U′{ψ[g(k)] − g[g(k)]}`  for `k ∈ K = [0, k̄]`.

* `assumption_18_2_contradiction` (**Correction**, p. 554): Assumption 18.1b (U twice
  continuously differentiable on `ℝ₊ = [0, ∞)`) and the Inada condition of Assumption 18.2
  (`U′(c) → ∞` as `c → 0`) are inconsistent: a `C²` (indeed `C¹`) function on `[0, ∞)` has a
  finite one-sided derivative at `0` which is the limit of `U′(c)`.
* `GlobalModel`: Assumptions 18.1 and 18.2 in the corrected reading — `U` and `f` are continuous
  on `[0, ∞)` and `C²` on `(0, ∞)`; `f′(0) = A` is the (finite) limit of `f′(k)` as `k → 0`
  (the first half of Assumption 18.2) and `U′(c) → ∞` as `c → 0⁺` (the second half).
* Derived facts (pp. 547–548, 555): `f′ > 0` and strictly decreasing, `U′` is a marginal utility
  in the sense of `IsMarginalUtility`, `ψ` is continuous and strictly increasing with
  `ψ(0) = f(0) > 0` and `ψ(k̄) = k̄`, there is a unique `k* ∈ (0, k̄)` with `β(1 − θ)f′(k*) = 1`
  (`exists_kstar`, `kstar_unique`), and `ψ(b) − ψ(a) > b − a` for `0 ≤ a < b ≤ k*`
  (`sub_lt_psi_sub`, the book's "`ψ′ > 1/β > 1` on `[0, k*]`").
* `F` (p. 555): the continuous `h` on `K` with (2) `0 ≤ h ≤ ψ`, (3) `h` and `ψ − h`
  nondecreasing, (4) `h(k) ≥ k` for `k < k*`, (5) `h(k*) = k*`, (6) `h(k) ≤ k` for `k > k*`.
  `F_nonempty`, `F_isClosed`, `F_isBounded`, `F_convex` (p. 556).
* **Proposition 18.5** (`prop_18_5`, p. 557): `F` is equicontinuous.
* The least element `h_` of `F` (`isLeast_low`, p. 558) and the greatest element `ū`
  (`isGreatest_up`), with the explicit formula `up_eq_of_le_kstar`, `up_eq_of_kstar_le`.
* `not_isInF_hbar`, `hbar_not_mem_F` (**Correction**, p. 558): the book's maximal element `h̄`
  is not in `F`.

**Correction (Assumption 18.2 vs 18.1b, p. 554).** As printed the two assumptions contradict
each other (`assumption_18_2_contradiction`); 18.1b and 18.1d are read as "continuous on
`[0, ∞)`, `C²` on `(0, ∞)`", which is the reading under which the Inada condition makes sense and
the first half of 18.2 (`f′(0) < ∞`) is not redundant.

**Correction (p. 555, minor).** "`ψ′(k) > (1 − θ) f′(k)` for all `k ∈ K`" fails at `k = 0`; only
`≥` holds. Nothing here uses derivatives of `ψ`: `psi_sub_gt` is the difference-quotient
inequality `ψ(b) − ψ(a) > (1 − θ)(b − a) f′(b)` for `0 ≤ a < b`, proved from strict concavity of
`f` alone.

**Correction (Proposition 18.5's proof, p. 557).** The proof bounds `|ψ(k′) − ψ(k)|` by
`A |k′ − k|` with `A = f′(0)`; this is false (counterexample `prop_18_5_bound_counterexample` in
`GlobalExamples`), because `ψ′ = (1 − θ)f′ − θ k f″` contains the term `−θ k f″ ≥ 0`, which
`f′(0)` does not control. The proposition is true: `prop_18_5` uses only uniform continuity of
`ψ` on the compact `K` together with `|h(k′) − h(k)| ≤ |ψ(k′) − ψ(k)|`.

**Correction (p. 558, the maximal element).** The book's
`h̄(k) = min{ψ(k), k*}` (`k ≤ k*`), `h̄(k) = min{k, ψ(k) − [ψ(k*) − k*]}` (`k > k*`) is an upper
bound for `F` but is not in `F`: `ψ − h̄` is not nondecreasing (`not_isInF_hbar`). The greatest
element of `F` is `ū(k) = ψ(k) − max_{0 ≤ j ≤ k} [ψ(j) − min{ψ(j), max(j, k*)}]`, which equals
`min{ψ(k), k*}` for `k ≤ k*` (`up_eq_of_le_kstar`) and `ψ(k) − max_{k* ≤ j ≤ k} [ψ(j) − j]` for
`k ≥ k*` (`up_eq_of_kstar_le`).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology BoundedContinuousFunction

/-- **Correction to Assumptions 18.1b and 18.2** (p. 554). If `U` is twice continuously
differentiable on `[0, ∞)` (Assumption 18.1b as printed) then its derivative cannot tend to `∞`
at `0` (the Inada condition of Assumption 18.2). -/
theorem assumption_18_2_contradiction {U U' : ℝ → ℝ} (hU : ContDiffOn ℝ 2 U (Ici 0))
    (hU' : ∀ c, 0 < c → HasDerivAt U (U' c) c) : ¬ Tendsto U' (𝓝[>] 0) atTop := by
  have hc : ContinuousOn (derivWithin U (Ici 0)) (Ici 0) :=
    hU.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by norm_num)
  have h1 : Tendsto (derivWithin U (Ici 0)) (𝓝[>] 0) (𝓝 (derivWithin U (Ici 0) 0)) :=
    (hc 0 (mem_Ici.2 le_rfl)).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have h2 : derivWithin U (Ici 0) =ᶠ[𝓝[>] 0] U' := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (hU' c hc).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Ici 0 c (mem_Ici.2 (mem_Ioi.1 hc).le))
  exact not_tendsto_atTop_of_tendsto_nhds (h1.congr' h2)

/-- **Assumptions 18.1 and 18.2** (pp. 547–548, 554), in the corrected reading of
`assumption_18_2_contradiction`. `U'` and `f'` are the derivatives of `U` and `f` on `(0, ∞)`;
`f' 0` is the value `A = f′(0)` of Assumption 18.2, the limit of `f′(k)` as `k → 0`
(`f'_contAt_zero`).
* (a) `0 < β < 1`;
* (b) `U` continuous on `[0, ∞)`, `C²` on `(0, ∞)`, strictly increasing and strictly concave;
* (c) `0 < θ < 1`;
* (d) `f` continuous on `[0, ∞)`, `C²` on `(0, ∞)`, strictly increasing and strictly concave,
  `f(0) > 0` and `f′(0) > 1/[β(1 − θ)]`;
* (e) `ψ(k) − k > 0` on `(0, k̄)` and `< 0` on `(k̄, ∞)`, where `ψ(k) = f(k) − θ k f′(k)`;
* (18.2) `f′(0) = lim_{k → 0} f′(k)` is finite, and `U′(c) → ∞` as `c → 0⁺`. -/
structure GlobalModel where
  β : ℝ
  θ : ℝ
  U : ℝ → ℝ
  U' : ℝ → ℝ
  f : ℝ → ℝ
  f' : ℝ → ℝ
  kbar : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  U_cont : ContinuousOn U (Ici 0)
  U_contDiff : ContDiffOn ℝ 2 U (Ioi 0)
  U_strictMono : StrictMonoOn U (Ici 0)
  U_strictConcave : StrictConcaveOn ℝ (Ici 0) U
  U_deriv : ∀ c, 0 < c → HasDerivAt U (U' c) c
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  f_cont : ContinuousOn f (Ici 0)
  f_contDiff : ContDiffOn ℝ 2 f (Ioi 0)
  f_strictMono : StrictMonoOn f (Ici 0)
  f_strictConcave : StrictConcaveOn ℝ (Ici 0) f
  f_deriv : ∀ k, 0 < k → HasDerivAt f (f' k) k
  f_zero_pos : 0 < f 0
  f'_zero : 1 / (β * (1 - θ)) < f' 0
  kbar_pos : 0 < kbar
  psi_gt : ∀ k, 0 < k → k < kbar → k < f k - θ * k * f' k
  psi_lt : ∀ k, kbar < k → f k - θ * k * f' k < k
  f'_contAt_zero : ContinuousWithinAt f' (Ici 0) 0
  U'_inada : Tendsto U' (𝓝[>] 0) atTop

namespace GlobalModel

variable (M : GlobalModel)

/-- After-tax income `ψ(k) = f(k) − θ k f′(k)` (p. 547). -/
noncomputable def psi (k : ℝ) : ℝ := M.f k - M.θ * k * M.f' k

/-- `f′` is the derivative of `f` on `(0, ∞)`. -/
theorem deriv_f_eq {k : ℝ} (hk : 0 < k) : deriv M.f k = M.f' k := (M.f_deriv k hk).deriv

/-- `U′` is the derivative of `U` on `(0, ∞)`. -/
theorem deriv_U_eq {c : ℝ} (hc : 0 < c) : deriv M.U c = M.U' c := (M.U_deriv c hc).deriv

/-- `f′` is strictly decreasing on `(0, ∞)` (strict concavity). -/
theorem f'_strictAntiOn_Ioi : StrictAntiOn M.f' (Ioi 0) := by
  have h := (M.f_strictConcave.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    (fun x hx => (M.f_deriv x hx).differentiableAt)
  intro a ha b hb hab
  have := h ha hb hab
  rwa [M.deriv_f_eq ha, M.deriv_f_eq hb] at this

/-- `f′` is continuous on `(0, ∞)` (`f` is `C²` there). -/
theorem f'_continuousOn_Ioi : ContinuousOn M.f' (Ioi 0) :=
  (M.f_contDiff.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).congr
    fun _ hk => (M.deriv_f_eq hk).symm

/-- `f′` is continuous on `[0, ∞)`. -/
theorem f'_continuousOn : ContinuousOn M.f' (Ici 0) := by
  intro k hk
  rcases (mem_Ici.1 hk).eq_or_lt with h | h
  · subst h
    exact M.f'_contAt_zero
  · exact (M.f'_continuousOn_Ioi.continuousAt (Ioi_mem_nhds h)).continuousWithinAt

/-- `f′` is strictly decreasing on `[0, ∞)`. -/
theorem f'_strictAntiOn : StrictAntiOn M.f' (Ici 0) := by
  intro a ha b hb hab
  rcases (mem_Ici.1 ha).eq_or_lt with h | h
  · subst h
    have hb0 : 0 < b := hab
    have hlim : Tendsto M.f' (𝓝[>] 0) (𝓝 (M.f' 0)) :=
      M.f'_contAt_zero.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have hge : M.f' (b / 2) ≤ M.f' 0 := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < b / 2)] with x hx
      exact (M.f'_strictAntiOn_Ioi hx.1 (by simp; linarith) hx.2).le
    exact (M.f'_strictAntiOn_Ioi (by simp; linarith) hb0 (by linarith)).trans_le hge
  · exact M.f'_strictAntiOn_Ioi h (lt_trans h hab) hab

/-- `f′ > 0` on `[0, ∞)` (`f` strictly increasing and strictly concave). -/
theorem f'_pos {k : ℝ} (hk : 0 ≤ k) : 0 < M.f' k := by
  have h1 : 0 < M.f' (k + 1) := by
    have hs := M.f_strictConcave.slope_lt_of_hasDerivAt (x := k + 1) (y := k + 2)
      (by simp; linarith) (by simp; linarith) (by linarith) (M.f_deriv _ (by linarith))
    have hm := M.f_strictMono (show k + 1 ∈ Ici 0 by simp; linarith)
      (show k + 2 ∈ Ici 0 by simp; linarith) (by linarith : k + 1 < k + 2)
    rw [slope_def_field] at hs
    have : 0 < (M.f (k + 2) - M.f (k + 1)) / (k + 2 - (k + 1)) :=
      div_pos (by linarith) (by linarith)
    linarith
  exact h1.trans (M.f'_strictAntiOn hk (show k + 1 ∈ Ici 0 by simp; linarith) (by linarith))

/-- `U′ > 0` on `(0, ∞)`. -/
theorem U'_pos {c : ℝ} (hc : 0 < c) : 0 < M.U' c := by
  have hs := M.U_strictConcave.slope_lt_of_hasDerivAt (x := c) (y := c + 1)
    (by simp; linarith) (by simp; linarith) (by linarith) (M.U_deriv _ hc)
  have hm := M.U_strictMono (show c ∈ Ici 0 by simp; linarith)
    (show c + 1 ∈ Ici 0 by simp; linarith) (by linarith : c < c + 1)
  rw [slope_def_field] at hs
  have : 0 < (M.U (c + 1) - M.U c) / (c + 1 - c) := div_pos (by linarith) (by linarith)
  linarith

/-- `U′` is strictly decreasing on `(0, ∞)`. -/
theorem U'_strictAntiOn : StrictAntiOn M.U' (Ioi 0) := by
  have h := (M.U_strictConcave.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    (fun x hx => (M.U_deriv x hx).differentiableAt)
  intro a ha b hb hab
  have := h ha hb hab
  rwa [M.deriv_U_eq ha, M.deriv_U_eq hb] at this

/-- `U′` is continuous on `(0, ∞)`. -/
theorem U'_continuousOn : ContinuousOn M.U' (Ioi 0) :=
  (M.U_contDiff.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).congr
    fun _ hc => (M.deriv_U_eq hc).symm

/-- `U′` is a marginal utility in the sense of `IsMarginalUtility` (Assumptions 18.1b, 18.2). -/
theorem isMarginalUtility : IsMarginalUtility M.U' :=
  ⟨fun _ hc => M.U'_pos hc, M.U'_strictAntiOn, M.U'_continuousOn, M.U'_inada⟩

/-- Strict concavity of `f`: `f′(b)(b − a) < f(b) − f(a)` for `0 ≤ a < b`. -/
theorem f'_mul_lt_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    M.f' b * (b - a) < M.f b - M.f a := by
  have hs := M.f_strictConcave.lt_slope_of_hasDerivAt (mem_Ici.2 ha)
    (mem_Ici.2 (ha.trans hab.le)) hab (M.f_deriv b (lt_of_le_of_lt ha hab))
  rw [slope_def_field, lt_div_iff₀ (by linarith)] at hs
  exact hs

/-- `k f′(k) < f(k)` for `k > 0`. -/
theorem mul_f'_lt_f {k : ℝ} (hk : 0 < k) : k * M.f' k < M.f k := by
  have := M.f'_mul_lt_sub le_rfl hk
  have := M.f_zero_pos
  nlinarith

/-- The difference-quotient form of "`ψ′ ≥ (1 − θ) f′`" (p. 555): for `0 ≤ a < b`,
`ψ(b) − ψ(a) > (1 − θ)(b − a) f′(b)`. -/
theorem psi_sub_gt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (1 - M.θ) * (b - a) * M.f' b < M.psi b - M.psi a := by
  have h1 := M.f'_mul_lt_sub ha hab
  have h2 : M.f' b < M.f' a := M.f'_strictAntiOn (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab.le)) hab
  have h3 : a * M.f' b ≤ a * M.f' a := mul_le_mul_of_nonneg_left h2.le ha
  have h4 : 0 ≤ M.θ * (a * M.f' a - a * M.f' b) :=
    mul_nonneg M.θ_pos.le (sub_nonneg.2 h3)
  have : M.psi b - M.psi a - (1 - M.θ) * (b - a) * M.f' b =
      (M.f b - M.f a - M.f' b * (b - a)) + M.θ * (a * M.f' a - a * M.f' b) := by
    unfold psi; ring
  linarith

/-- `ψ` is strictly increasing on `[0, ∞)` (p. 555). -/
theorem psi_strictMonoOn : StrictMonoOn M.psi (Ici 0) := by
  intro a ha b hb hab
  have h := M.psi_sub_gt (mem_Ici.1 ha) hab
  have : 0 < (1 - M.θ) * (b - a) * M.f' b :=
    mul_pos (mul_pos (by linarith [M.θ_lt_one]) (by linarith)) (M.f'_pos (mem_Ici.1 hb))
  linarith

/-- `ψ` is continuous on `[0, ∞)`. -/
theorem psi_continuousOn : ContinuousOn M.psi (Ici 0) :=
  M.f_cont.sub ((continuousOn_const.mul continuousOn_id).mul M.f'_continuousOn)

/-- `ψ(0) = f(0)`. -/
theorem psi_zero : M.psi 0 = M.f 0 := by simp [psi]

/-- `ψ > 0` on `[0, ∞)`. -/
theorem psi_pos {k : ℝ} (hk : 0 ≤ k) : 0 < M.psi k := by
  rcases hk.eq_or_lt with h | h
  · subst h; rw [psi_zero]; exact M.f_zero_pos
  · have := M.psi_strictMonoOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk) h
    rw [psi_zero] at this
    linarith [M.f_zero_pos]

/-- `k < ψ(k)` on `[0, k̄)` (Assumption 18.1e). -/
theorem lt_psi {k : ℝ} (h0 : 0 ≤ k) (hk : k < M.kbar) : k < M.psi k := by
  rcases h0.eq_or_lt with h | h
  · subst h; exact M.psi_pos le_rfl
  · exact M.psi_gt k h hk

/-- `ψ(k̄) = k̄` (continuity and Assumption 18.1e). -/
theorem psi_kbar : M.psi M.kbar = M.kbar := by
  have hc : ContinuousAt (fun k => M.psi k - k) M.kbar :=
    ((M.psi_continuousOn.continuousAt (Ici_mem_nhds M.kbar_pos)).sub continuousAt_id)
  have h1 : M.psi M.kbar - M.kbar ≤ 0 := by
    refine le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi M.kbar))) ?_
    filter_upwards [self_mem_nhdsWithin] with k (hk : M.kbar < k)
    linarith [M.psi_lt k hk, show M.psi k = M.f k - M.θ * k * M.f' k from rfl]
  have h2 : 0 ≤ M.psi M.kbar - M.kbar := by
    refine ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio M.kbar))) ?_
    filter_upwards [Ioo_mem_nhdsLT M.kbar_pos] with k hk
    linarith [M.lt_psi hk.1.le hk.2]
  linarith

/-- `ψ` maps `[0, k̄]` into `(0, k̄]` (p. 548). -/
theorem psi_le_kbar {k : ℝ} (hk : k ∈ Icc 0 M.kbar) : M.psi k ≤ M.kbar := by
  rcases hk.2.eq_or_lt with h | h
  · rw [h, psi_kbar]
  · have := M.psi_strictMonoOn (mem_Ici.2 hk.1) (mem_Ici.2 M.kbar_pos.le) h
    rw [psi_kbar] at this
    exact this.le

/-- `(1 − θ) f′(k̄) ≤ 1` (from Assumption 18.1e and `k f′(k) < f(k)`). -/
theorem one_sub_mul_f'_kbar_le : (1 - M.θ) * M.f' M.kbar ≤ 1 := by
  have hc : ContinuousAt (fun k => (1 - M.θ) * M.f' k) M.kbar :=
    continuousAt_const.mul (M.f'_continuousOn_Ioi.continuousAt (Ioi_mem_nhds M.kbar_pos))
  refine le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi M.kbar))) ?_
  filter_upwards [self_mem_nhdsWithin] with k (hk : M.kbar < k)
  have hk0 : 0 < k := M.kbar_pos.trans hk
  have h1 := M.psi_lt k hk
  have h2 := M.mul_f'_lt_f hk0
  have h3 : (1 - M.θ) * M.f' k * k < 1 * k := by nlinarith [M.θ_pos]
  exact le_of_lt (lt_of_mul_lt_mul_right h3 hk0.le)

/-- `β(1 − θ) f′(k̄) < 1` (fact (F3) of the transcription). -/
theorem euler_kbar_lt_one : M.β * (1 - M.θ) * M.f' M.kbar < 1 := by
  have h := M.one_sub_mul_f'_kbar_le
  have : M.β * ((1 - M.θ) * M.f' M.kbar) ≤ M.β * 1 :=
    mul_le_mul_of_nonneg_left h M.β_pos.le
  nlinarith [M.β_lt_one]

/-- `β(1 − θ) f′(0) > 1` (Assumption 18.1d). -/
theorem one_lt_euler_zero : 1 < M.β * (1 - M.θ) * M.f' 0 := by
  have h := M.f'_zero
  have hpos : 0 < M.β * (1 - M.θ) := mul_pos M.β_pos (by linarith [M.θ_lt_one])
  rw [div_lt_iff₀ hpos] at h
  linarith

/-- **Existence of the steady state `k*`** (§18.2 (5), p. 549): some `k* ∈ (0, k̄)` has
`β(1 − θ) f′(k*) = 1`. -/
theorem exists_kstar : ∃ k ∈ Ioo 0 M.kbar, M.β * (1 - M.θ) * M.f' k = 1 := by
  have hc : ContinuousOn (fun k => M.β * (1 - M.θ) * M.f' k) (Icc 0 M.kbar) :=
    continuousOn_const.mul (M.f'_continuousOn.mono Icc_subset_Ici_self)
  obtain ⟨k, hk, hk1⟩ := intermediate_value_Icc' M.kbar_pos.le hc
    ⟨M.euler_kbar_lt_one.le, M.one_lt_euler_zero.le⟩
  refine ⟨k, ⟨?_, ?_⟩, hk1⟩
  · rcases hk.1.eq_or_lt with h | h
    · subst h; linarith [M.one_lt_euler_zero]
    · exact h
  · rcases hk.2.eq_or_lt with h | h
    · simp only at hk1; rw [h] at hk1; linarith [M.euler_kbar_lt_one]
    · exact h

/-- The steady state `k*`: `β(1 − θ) f′(k*) = 1` (§18.2 (5)). -/
noncomputable def kstar : ℝ := Classical.choose M.exists_kstar

/-- `0 < k*`. -/
theorem kstar_pos : 0 < M.kstar := (Classical.choose_spec M.exists_kstar).1.1

/-- `k* < k̄`. -/
theorem kstar_lt_kbar : M.kstar < M.kbar := (Classical.choose_spec M.exists_kstar).1.2

/-- `β(1 − θ) f′(k*) = 1`. -/
theorem euler_kstar : M.β * (1 - M.θ) * M.f' M.kstar = 1 :=
  (Classical.choose_spec M.exists_kstar).2

/-- `k*` lies in `K = [0, k̄]`. -/
theorem kstar_mem : M.kstar ∈ Icc 0 M.kbar := ⟨M.kstar_pos.le, M.kstar_lt_kbar.le⟩

/-- `β(1 − θ) f′(k) > 1` for `0 ≤ k < k*`. -/
theorem one_lt_euler {k : ℝ} (h0 : 0 ≤ k) (hk : k < M.kstar) :
    1 < M.β * (1 - M.θ) * M.f' k := by
  have h := M.f'_strictAntiOn (mem_Ici.2 h0) (mem_Ici.2 M.kstar_pos.le) hk
  have hpos : 0 < M.β * (1 - M.θ) := mul_pos M.β_pos (by linarith [M.θ_lt_one])
  have := mul_lt_mul_of_pos_left h hpos
  linarith [M.euler_kstar]

/-- `β(1 − θ) f′(k) < 1` for `k > k*`. -/
theorem euler_lt_one {k : ℝ} (hk : M.kstar < k) : M.β * (1 - M.θ) * M.f' k < 1 := by
  have h := M.f'_strictAntiOn (mem_Ici.2 M.kstar_pos.le) (mem_Ici.2 (M.kstar_pos.le.trans hk.le)) hk
  have hpos : 0 < M.β * (1 - M.θ) := mul_pos M.β_pos (by linarith [M.θ_lt_one])
  have := mul_lt_mul_of_pos_left h hpos
  linarith [M.euler_kstar]

/-- `k*` is the only `k ≥ 0` with `β(1 − θ) f′(k) = 1` (Proposition 18.1, p. 549). -/
theorem kstar_unique {k : ℝ} (h0 : 0 ≤ k) (hk : M.β * (1 - M.θ) * M.f' k = 1) : k = M.kstar := by
  rcases lt_trichotomy k M.kstar with h | h | h
  · linarith [M.one_lt_euler h0 h]
  · exact h
  · linarith [M.euler_lt_one h]

/-- "`ψ′ > 1/β > 1` on `[0, k*]`" (p. 555), as a difference quotient: `ψ(b) − ψ(a) > b − a`
for `0 ≤ a < b ≤ k*`. -/
theorem sub_lt_psi_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ M.kstar) :
    b - a < M.psi b - M.psi a := by
  have h1 := M.psi_sub_gt ha hab
  have h2 : 1 ≤ M.β * (1 - M.θ) * M.f' b := by
    rcases hb.lt_or_eq with h | h
    · exact (M.one_lt_euler (ha.trans hab.le) h).le
    · rw [h, M.euler_kstar]
  have hx : 1 < (1 - M.θ) * M.f' b := by
    have hpos : 0 < (1 - M.θ) * M.f' b :=
      mul_pos (by linarith [M.θ_lt_one]) (M.f'_pos (ha.trans hab.le))
    by_contra hle
    push Not at hle
    have : M.β * ((1 - M.θ) * M.f' b) ≤ M.β * 1 := mul_le_mul_of_nonneg_left hle M.β_pos.le
    nlinarith [M.β_lt_one]
  nlinarith

/-- `k < ψ(k)` for `0 ≤ k ≤ k*`; in particular `ψ(k*) > k*` (p. 555). -/
theorem lt_psi_of_le_kstar {k : ℝ} (h0 : 0 ≤ k) (hk : k ≤ M.kstar) : k < M.psi k :=
  M.lt_psi h0 (hk.trans_lt M.kstar_lt_kbar)

/-! ### The set `F` (p. 555) -/

/-- Conditions (2)–(6) of p. 555 on a function `g : ℝ → ℝ`, read on `K = [0, k̄]`, together
with continuity on `K`: (2) `0 ≤ g ≤ ψ`; (3) `g` and `ψ − g` nondecreasing; (4) `g(k) ≥ k` for
`k < k*`; (5) `g(k*) = k*`; (6) `g(k) ≤ k` for `k > k*`. -/
structure IsInF (g : ℝ → ℝ) : Prop where
  cont : ContinuousOn g (Icc 0 M.kbar)
  nonneg : ∀ k ∈ Icc 0 M.kbar, 0 ≤ g k
  le_psi : ∀ k ∈ Icc 0 M.kbar, g k ≤ M.psi k
  mono : MonotoneOn g (Icc 0 M.kbar)
  mono_sub : MonotoneOn (fun k => M.psi k - g k) (Icc 0 M.kbar)
  ge_self : ∀ k ∈ Icc 0 M.kbar, k < M.kstar → k ≤ g k
  at_kstar : g M.kstar = M.kstar
  le_self : ∀ k ∈ Icc 0 M.kbar, M.kstar < k → g k ≤ k

/-- The extension of `h ∈ C(K)` to `ℝ`, constant outside `K` (`Set.IccExtend`). -/
noncomputable def ext (h : Icc 0 M.kbar →ᵇ ℝ) : ℝ → ℝ := IccExtend M.kbar_pos.le h

/-- `ext h` agrees with `h` on `K`. -/
theorem ext_apply (h : Icc 0 M.kbar →ᵇ ℝ) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    M.ext h k = h ⟨k, hk⟩ :=
  IccExtend_of_mem _ _ hk

/-- **The set `F`** (p. 555): the `h ∈ C(K)` satisfying (2)–(6). -/
def F : Set (Icc 0 M.kbar →ᵇ ℝ) := {h | M.IsInF (M.ext h)}

/-- A continuous function on `K`, as an element of `C(K)`. -/
noncomputable def toBCF (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 M.kbar)) :
    Icc 0 M.kbar →ᵇ ℝ :=
  mkOfCompact ⟨(Icc 0 M.kbar).domRestrict g, hg.domRestrict⟩

/-- `toBCF g` evaluates as `g`. -/
theorem toBCF_apply (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 M.kbar)) (k : Icc 0 M.kbar) :
    M.toBCF g hg k = g k := rfl

/-- `ext (toBCF g)` agrees with `g` on `K`. -/
theorem ext_toBCF (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 M.kbar)) {k : ℝ}
    (hk : k ∈ Icc 0 M.kbar) : M.ext (M.toBCF g hg) k = g k := by
  rw [ext_apply _ _ hk, toBCF_apply]

variable {M}

/-- `IsInF` only depends on the values on `K`. -/
theorem IsInF.congr {g g' : ℝ → ℝ} (hg : M.IsInF g) (heq : EqOn g g' (Icc 0 M.kbar)) :
    M.IsInF g' where
  cont := hg.cont.congr fun k hk => (heq hk).symm
  nonneg k hk := heq hk ▸ hg.nonneg k hk
  le_psi k hk := heq hk ▸ hg.le_psi k hk
  mono a ha b hb hab := by rw [← heq ha, ← heq hb]; exact hg.mono ha hb hab
  mono_sub a ha b hb hab := by
    simp only
    rw [← heq ha, ← heq hb]; exact hg.mono_sub ha hb hab
  ge_self k hk hk' := heq hk ▸ hg.ge_self k hk hk'
  at_kstar := by rw [← heq M.kstar_mem]; exact hg.at_kstar
  le_self k hk hk' := heq hk ▸ hg.le_self k hk hk'

/-- `toBCF g ∈ F` when `g` satisfies (2)–(6). -/
theorem toBCF_mem_F {g : ℝ → ℝ} (hg : M.IsInF g) : M.toBCF g hg.cont ∈ M.F :=
  hg.congr fun _ hk => (M.ext_toBCF g hg.cont hk).symm

/-- On `K`, members of `F` change by at most the change in `ψ`: `|h(k′) − h(k)| ≤ |ψ(k′) − ψ(k)|`
(from (3)). -/
theorem IsInF.abs_sub_le {g : ℝ → ℝ} (hg : M.IsInF g) {a b : ℝ} (ha : a ∈ Icc 0 M.kbar)
    (hb : b ∈ Icc 0 M.kbar) : |g a - g b| ≤ |M.psi a - M.psi b| := by
  rcases le_total a b with hab | hab
  · have h1 := hg.mono ha hb hab
    have h2 : M.psi a - g a ≤ M.psi b - g b := hg.mono_sub ha hb hab
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := hg.mono hb ha hab
    have h2 : M.psi b - g b ≤ M.psi a - g a := hg.mono_sub hb ha hab
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- Members of `F` lie in `K`. -/
theorem IsInF.le_kbar {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    g k ≤ M.kbar :=
  (hg.le_psi k hk).trans (M.psi_le_kbar hk)

/-- Members of `F` map `K` into `K`. -/
theorem IsInF.mem_Icc {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    g k ∈ Icc 0 M.kbar :=
  ⟨hg.nonneg k hk, hg.le_kbar hk⟩

/-- Convex combinations of functions satisfying (2)–(6) satisfy (2)–(6). -/
theorem IsInF.convex_comb {g₁ g₂ : ℝ → ℝ} (h₁ : M.IsInF g₁) (h₂ : M.IsInF g₂) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    M.IsInF (fun k => a * g₁ k + b * g₂ k) where
  cont := (continuousOn_const.mul h₁.cont).add (continuousOn_const.mul h₂.cont)
  nonneg k hk := add_nonneg (mul_nonneg ha (h₁.nonneg k hk)) (mul_nonneg hb (h₂.nonneg k hk))
  le_psi k hk := by
    have := mul_le_mul_of_nonneg_left (h₁.le_psi k hk) ha
    have := mul_le_mul_of_nonneg_left (h₂.le_psi k hk) hb
    have : M.psi k = a * M.psi k + b * M.psi k := by rw [← add_mul, hab, one_mul]
    linarith
  mono x hx y hy hxy := by
    have := mul_le_mul_of_nonneg_left (h₁.mono hx hy hxy) ha
    have := mul_le_mul_of_nonneg_left (h₂.mono hx hy hxy) hb
    simp only
    linarith
  mono_sub x hx y hy hxy := by
    have e1 : M.psi x - g₁ x ≤ M.psi y - g₁ y := h₁.mono_sub hx hy hxy
    have e2 : M.psi x - g₂ x ≤ M.psi y - g₂ y := h₂.mono_sub hx hy hxy
    have := mul_le_mul_of_nonneg_left e1 ha
    have := mul_le_mul_of_nonneg_left e2 hb
    have ex : M.psi x = a * M.psi x + b * M.psi x := by rw [← add_mul, hab, one_mul]
    have ey : M.psi y = a * M.psi y + b * M.psi y := by rw [← add_mul, hab, one_mul]
    simp only
    nlinarith
  ge_self k hk hk' := by
    have := mul_le_mul_of_nonneg_left (h₁.ge_self k hk hk') ha
    have := mul_le_mul_of_nonneg_left (h₂.ge_self k hk hk') hb
    have : k = a * k + b * k := by rw [← add_mul, hab, one_mul]
    linarith
  at_kstar := by
    simp only [h₁.at_kstar, h₂.at_kstar]
    rw [← add_mul, hab, one_mul]
  le_self k hk hk' := by
    have := mul_le_mul_of_nonneg_left (h₁.le_self k hk hk') ha
    have := mul_le_mul_of_nonneg_left (h₂.le_self k hk hk') hb
    have : k = a * k + b * k := by rw [← add_mul, hab, one_mul]
    linarith

variable (M)

/-- The least element `h_` of `F` (p. 558): `h_(k) = k` for `k ≤ k*`, `h_(k) = k*` for `k > k*`,
i.e. `h_(k) = min{k, k*}`. -/
noncomputable def low (k : ℝ) : ℝ := min k M.kstar

/-- `h_` satisfies (2)–(6). -/
theorem isInF_low : M.IsInF M.low where
  cont := ContinuousOn.inf continuousOn_id continuousOn_const
  nonneg k hk := le_min hk.1 M.kstar_pos.le
  le_psi k hk := by
    rcases le_total k M.kstar with h | h
    · exact (min_le_left _ _).trans (M.lt_psi_of_le_kstar hk.1 h).le
    · refine (min_le_right _ _).trans ?_
      rcases h.eq_or_lt with h' | h'
      · rw [← h']; exact (M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl).le
      · exact (M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl).le.trans
          (M.psi_strictMonoOn (mem_Ici.2 M.kstar_pos.le) (mem_Ici.2 hk.1) h').le
  mono _ _ _ _ hxy := min_le_min_right _ hxy
  mono_sub x hx y hy hxy := by
    simp only [low]
    rcases le_total y M.kstar with hyk | hyk
    · rw [min_eq_left (hxy.trans hyk), min_eq_left hyk]
      rcases hxy.eq_or_lt with h | h
      · rw [h]
      · linarith [M.sub_lt_psi_sub hx.1 h hyk]
    · rw [min_eq_right hyk]
      rcases le_total x M.kstar with hxk | hxk
      · rw [min_eq_left hxk]
        have h1 : M.psi x - x ≤ M.psi M.kstar - M.kstar := by
          rcases hxk.eq_or_lt with h | h
          · rw [h]
          · linarith [M.sub_lt_psi_sub hx.1 h le_rfl]
        have h2 : M.psi M.kstar ≤ M.psi y := M.psi_strictMonoOn.monotoneOn
          (mem_Ici.2 M.kstar_pos.le) (mem_Ici.2 hy.1) hyk
        linarith
      · rw [min_eq_right hxk]
        have := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy
        linarith
  ge_self k _ hk := (min_eq_left hk.le).ge
  at_kstar := min_self _
  le_self _ _ _ := min_le_left _ _

variable {M} in
/-- Every member of `F` lies above `h_` (p. 558). -/
theorem IsInF.low_le {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    M.low k ≤ g k := by
  rcases lt_trichotomy k M.kstar with h | h | h
  · exact (min_le_left _ _).trans (hg.ge_self k hk h)
  · rw [h, low, min_self, hg.at_kstar]
  · rw [low, min_eq_right h.le, ← hg.at_kstar]
    exact hg.mono M.kstar_mem hk h.le

/-- The pointwise upper bound `b(k) = min{ψ(k), max(k, k*)}` implied by (2), (3), (5), (6). -/
noncomputable def bnd (k : ℝ) : ℝ := min (M.psi k) (max k M.kstar)

variable {M} in
/-- Every member of `F` lies below `b`. -/
theorem IsInF.le_bnd {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    g k ≤ M.bnd k := by
  refine le_min (hg.le_psi k hk) ?_
  rcases le_or_gt k M.kstar with h | h
  · rw [max_eq_right h, ← hg.at_kstar]
    exact hg.mono hk M.kstar_mem h
  · exact (hg.le_self k hk h).trans (le_max_left _ _)

/-- `b` is nondecreasing on `K`. -/
theorem bnd_mono : MonotoneOn M.bnd (Icc 0 M.kbar) := fun _ hx _ hy hxy =>
  min_le_min (M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy)
    (max_le_max_right _ hxy)

/-- `b` is continuous on `K`. -/
theorem bnd_continuousOn : ContinuousOn M.bnd (Icc 0 M.kbar) :=
  ContinuousOn.inf (M.psi_continuousOn.mono Icc_subset_Ici_self)
    (ContinuousOn.sup continuousOn_id continuousOn_const)

/-! ### Running suprema -/

/-- The running supremum `k ↦ sup_{0 ≤ j ≤ k} φ(j)`. -/
noncomputable def runSup (φ : ℝ → ℝ) (k : ℝ) : ℝ := sSup (φ '' Icc 0 k)

omit M in
/-- A value of `φ` on `[0, k]` is below the running supremum. -/
theorem le_runSup {φ : ℝ → ℝ} {b k j : ℝ} (hφ : ContinuousOn φ (Icc 0 b)) (hk : k ≤ b)
    (hj : j ∈ Icc 0 k) : φ j ≤ runSup φ k :=
  le_csSup ((isCompact_Icc.image_of_continuousOn
    (hφ.mono (Icc_subset_Icc_right hk))).bddAbove) (mem_image_of_mem φ hj)

omit M in
/-- The running supremum is the least bound of `φ` on `[0, k]`. -/
theorem runSup_le {φ : ℝ → ℝ} {k c : ℝ} (hk : 0 ≤ k) (h : ∀ j ∈ Icc 0 k, φ j ≤ c) :
    runSup φ k ≤ c :=
  csSup_le ((nonempty_Icc.2 hk).image φ) (forall_mem_image.2 h)

omit M in
/-- The running supremum is nondecreasing. -/
theorem runSup_mono {φ : ℝ → ℝ} {b : ℝ} (hφ : ContinuousOn φ (Icc 0 b)) :
    MonotoneOn (runSup φ) (Icc 0 b) := fun _ hx _ hy hxy =>
  runSup_le hx.1 fun _ hj => le_runSup hφ hy.2 ⟨hj.1, hj.2.trans hxy⟩

omit M in
/-- The running supremum of a continuous function is continuous. -/
theorem runSup_continuousOn {φ : ℝ → ℝ} {b : ℝ} (hφ : ContinuousOn φ (Icc 0 b)) :
    ContinuousOn (runSup φ) (Icc 0 b) := by
  have hu := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hφ)
  rw [Metric.continuousOn_iff]
  intro k0 hk0 ε hε
  obtain ⟨δ, hδ, hφδ⟩ := hu (ε / 2) (by linarith)
  have key : ∀ a ∈ Icc 0 b, ∀ c ∈ Icc 0 b, a ≤ c → c - a < δ →
      runSup φ a ≤ runSup φ c ∧ runSup φ c ≤ runSup φ a + ε / 2 := by
    intro a ha c hc hac hca
    refine ⟨runSup_mono hφ ha hc hac, runSup_le hc.1 fun j hj => ?_⟩
    rcases le_or_gt j a with hja | hja
    · linarith [le_runSup hφ ha.2 ⟨hj.1, hja⟩]
    · have hjb : j ∈ Icc 0 b := ⟨hj.1, hj.2.trans hc.2⟩
      have h1 := hφδ j hjb a ha (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith [hj.2])
      rw [Real.dist_eq] at h1
      have h2 := le_runSup hφ ha.2 (show a ∈ Icc 0 a from ⟨ha.1, le_rfl⟩)
      linarith [(abs_lt.1 h1).2]
  refine ⟨δ, hδ, fun k hk hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  rcases le_total k k0 with h | h
  · obtain ⟨h1, h2⟩ := key k hk k0 hk0 h (by linarith [(abs_lt.1 hdist).1])
    rw [abs_lt]; constructor <;> linarith
  · obtain ⟨h1, h2⟩ := key k0 hk0 k hk h (by linarith [(abs_lt.1 hdist).2])
    rw [abs_lt]; constructor <;> linarith

/-! ### The greatest element of `F` -/

/-- The gap `ψ − b` whose running supremum defines the greatest element. -/
noncomputable def gap (j : ℝ) : ℝ := M.psi j - M.bnd j

/-- The gap is continuous on `K`. -/
theorem gap_continuousOn : ContinuousOn M.gap (Icc 0 M.kbar) :=
  (M.psi_continuousOn.mono Icc_subset_Ici_self).sub M.bnd_continuousOn

/-- **The greatest element `ū` of `F`** (corrected p. 558):
`ū(k) = ψ(k) − max_{0 ≤ j ≤ k} [ψ(j) − b(j)]`, the largest function below `b` with `ψ − ū`
nondecreasing. -/
noncomputable def up (k : ℝ) : ℝ := M.psi k - runSup M.gap k

variable {M} in
/-- Maximality: every member of `F` lies below `ū`. -/
theorem IsInF.le_up {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    g k ≤ M.up k := by
  have : runSup M.gap k ≤ M.psi k - g k := by
    refine runSup_le hk.1 fun j hj => ?_
    have hjK : j ∈ Icc 0 M.kbar := ⟨hj.1, hj.2.trans hk.2⟩
    have h1 : M.psi j - g j ≤ M.psi k - g k := hg.mono_sub hjK hk hj.2
    have h2 := hg.le_bnd hjK
    simp only [gap]
    linarith
  simp only [up]
  linarith

/-- `ū ≤ b` on `K`. -/
theorem up_le_bnd {k : ℝ} (hk : k ∈ Icc 0 M.kbar) : M.up k ≤ M.bnd k := by
  have := le_runSup M.gap_continuousOn hk.2 (show k ∈ Icc 0 k from ⟨hk.1, le_rfl⟩)
  simp only [up, gap] at this ⊢
  linarith

/-- `ū` satisfies (2)–(6). -/
theorem isInF_up : M.IsInF M.up where
  cont := (M.psi_continuousOn.mono Icc_subset_Ici_self).sub
    (runSup_continuousOn M.gap_continuousOn)
  nonneg k hk := (le_min hk.1 M.kstar_pos.le).trans (M.isInF_low.le_up hk)
  le_psi k hk := (M.up_le_bnd hk).trans (min_le_left _ _)
  mono x hx y hy hxy := by
    have : runSup M.gap y ≤ runSup M.gap x + (M.psi y - M.psi x) := by
      refine runSup_le hy.1 fun j hj => ?_
      have hjK : j ∈ Icc 0 M.kbar := ⟨hj.1, hj.2.trans hy.2⟩
      have hψ := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy
      rcases le_or_gt j x with hjx | hjx
      · linarith [le_runSup M.gap_continuousOn hx.2 ⟨hj.1, hjx⟩]
      · have h1 := M.bnd_mono hx hjK hjx.le
        have h2 := M.up_le_bnd hx
        have h3 := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hj.1) (mem_Ici.2 hy.1) hj.2
        simp only [up, gap] at h2 ⊢
        linarith
    simp only [up]
    linarith
  mono_sub x hx y hy hxy := by
    simp only [up, sub_sub_cancel]
    exact runSup_mono M.gap_continuousOn hx hy hxy
  ge_self k hk hk' := by
    have := M.isInF_low.le_up hk
    rwa [low, min_eq_left hk'.le] at this
  at_kstar := by
    refine le_antisymm ?_ ?_
    · refine (M.up_le_bnd M.kstar_mem).trans ?_
      rw [bnd, max_self]
      exact min_le_right _ _
    · have := M.isInF_low.le_up M.kstar_mem
      rwa [low, min_self] at this
  le_self k hk hk' := by
    refine (M.up_le_bnd hk).trans ((min_le_right _ _).trans ?_)
    rw [max_eq_left hk'.le]

/-- `ū(k) = min{ψ(k), k*}` for `0 ≤ k ≤ k*` (the formula of p. 558 on `[0, k*]`). -/
theorem up_eq_of_le_kstar {k : ℝ} (h0 : 0 ≤ k) (hk : k ≤ M.kstar) :
    M.up k = min (M.psi k) M.kstar := by
  have hkK : k ∈ Icc 0 M.kbar := ⟨h0, hk.trans M.kstar_lt_kbar.le⟩
  refine le_antisymm ?_ ?_
  · have := M.up_le_bnd hkK
    rwa [bnd, max_eq_right hk] at this
  · have : runSup M.gap k ≤ M.psi k - min (M.psi k) M.kstar := by
      refine runSup_le h0 fun j hj => ?_
      have hψ := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hj.1) (mem_Ici.2 h0) hj.2
      simp only [gap, bnd, max_eq_right (hj.2.trans hk)]
      rcases le_total (M.psi j) M.kstar with h1 | h1 <;>
        rcases le_total (M.psi k) M.kstar with h2 | h2 <;>
        simp only [min_eq_left, min_eq_right, h1, h2] <;> linarith
    simp only [up]
    linarith

/-- `ū(k) = ψ(k) − max_{k* ≤ j ≤ k} [ψ(j) − j]` for `k* ≤ k ≤ k̄` (the corrected formula of
NOTE 18.3-H; the book's `h̄` has `min{k, ψ(k) − [ψ(k*) − k*]}` instead). -/
theorem up_eq_of_kstar_le {k : ℝ} (hk : M.kstar ≤ k) (hkb : k ≤ M.kbar) :
    M.up k = M.psi k - sSup ((fun j => M.psi j - j) '' Icc M.kstar k) := by
  have hcont : ContinuousOn (fun j => M.psi j - j) (Icc M.kstar k) :=
    ((M.psi_continuousOn.mono fun j hj => mem_Ici.2 (M.kstar_pos.le.trans hj.1)).sub
      continuousOn_id)
  have hbdd : BddAbove ((fun j => M.psi j - j) '' Icc M.kstar k) :=
    (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  have hne : ((fun j => M.psi j - j) '' Icc M.kstar k).Nonempty :=
    (nonempty_Icc.2 hk).image _
  -- on `[k*, k]` the gap is `ψ(j) − j`
  have hgap : ∀ j ∈ Icc M.kstar k, M.gap j = M.psi j - j := by
    intro j hj
    have hj0 : 0 ≤ j := M.kstar_pos.le.trans hj.1
    have hjpsi : j ≤ M.psi j := by
      rcases (hj.2.trans hkb).lt_or_eq with h | h
      · exact (M.lt_psi hj0 h).le
      · rw [h, psi_kbar]
    simp only [gap, bnd, max_eq_left hj.1, min_eq_right hjpsi]
  simp only [up]
  congr 1
  refine le_antisymm (runSup_le (M.kstar_pos.le.trans hk) fun j hj => ?_) ?_
  · rcases le_or_gt j M.kstar with hjk | hjk
    · -- on `[0, k*]` the gap is at most `ψ(k*) − k*`
      have h1 : M.gap j ≤ M.psi M.kstar - M.kstar := by
        have hψ := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hj.1) (mem_Ici.2 M.kstar_pos.le) hjk
        have hk' := M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl
        simp only [gap, bnd, max_eq_right hjk]
        rcases le_total (M.psi j) M.kstar with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h]; linarith
      exact h1.trans (le_csSup hbdd ⟨M.kstar, ⟨le_rfl, hk⟩, rfl⟩)
    · rw [hgap j ⟨hjk.le, hj.2⟩]
      exact le_csSup hbdd ⟨j, ⟨hjk.le, hj.2⟩, rfl⟩
  · refine csSup_le hne (forall_mem_image.2 fun j hj => ?_)
    rw [← hgap j hj]
    exact le_runSup M.gap_continuousOn hkb ⟨M.kstar_pos.le.trans hj.1, hj.2⟩

/-! ### The book's `h̄` is not in `F` -/

/-- The book's candidate maximal element (p. 558): `h̄(k) = min{ψ(k), k*}` for `k ≤ k*` and
`h̄(k) = min{k, ψ(k) − [ψ(k*) − k*]}` for `k > k*`. -/
noncomputable def hbar (k : ℝ) : ℝ :=
  if k ≤ M.kstar then min (M.psi k) M.kstar else min k (M.psi k - (M.psi M.kstar - M.kstar))

/-- Just to the right of `k*`, `ψ(k) − k` exceeds its value `ψ(k*) − k*` at `k*` (because
`(1 − θ) f′(k*) = 1/β > 1`). -/
theorem exists_gap_gt : ∃ k, M.kstar < k ∧ k < M.kbar ∧
    M.psi M.kstar - M.kstar < M.psi k - k := by
  have h1 : 1 < (1 - M.θ) * M.f' M.kstar := by
    have h := M.euler_kstar
    have hpos : 0 < (1 - M.θ) * M.f' M.kstar :=
      mul_pos (by linarith [M.θ_lt_one]) (M.f'_pos M.kstar_pos.le)
    by_contra hle
    push Not at hle
    have : M.β * ((1 - M.θ) * M.f' M.kstar) ≤ M.β * 1 :=
      mul_le_mul_of_nonneg_left hle M.β_pos.le
    nlinarith [M.β_lt_one]
  have hc : ContinuousWithinAt (fun k => (1 - M.θ) * M.f' k) (Ici 0) M.kstar :=
    continuousWithinAt_const.mul (M.f'_continuousOn _ (mem_Ici.2 M.kstar_pos.le))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hc.eventually_const_lt h1)
  set k := M.kstar + min (δ / 2) ((M.kbar - M.kstar) / 2)
  have hm : 0 < min (δ / 2) ((M.kbar - M.kstar) / 2) :=
    lt_min (by linarith) (by linarith [M.kstar_lt_kbar])
  have hk1 : M.kstar < k := by linarith
  have hk2 : k < M.kbar := by linarith [min_le_right (δ / 2) ((M.kbar - M.kstar) / 2)]
  have hkf : 1 < (1 - M.θ) * M.f' k := by
    refine hball ⟨?_, mem_Ici.2 (by linarith [M.kstar_pos])⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
    linarith [min_le_left (δ / 2) ((M.kbar - M.kstar) / 2)]
  refine ⟨k, hk1, hk2, ?_⟩
  have h2 := M.psi_sub_gt M.kstar_pos.le hk1
  have h3 : (k - M.kstar) < (1 - M.θ) * (k - M.kstar) * M.f' k := by nlinarith
  linarith

/-- **Correction (p. 558).** The book's `h̄` violates (3): `ψ − h̄` is not nondecreasing on `K`,
so `h̄` does not satisfy (2)–(6). -/
theorem not_isInF_hbar : ¬ M.IsInF M.hbar := by
  intro hh
  obtain ⟨k, hk1, hk2, hgap⟩ := M.exists_gap_gt
  have hc : 0 < M.psi M.kstar - M.kstar := by
    linarith [M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl]
  have hhk : M.hbar k = k := by
    have hn : ¬ k ≤ M.kstar := not_le.2 hk1
    simp only [hbar, hn, ↓reduceIte]
    exact min_eq_left (by linarith)
  have hhb : M.hbar M.kbar = M.kbar - (M.psi M.kstar - M.kstar) := by
    have hn : ¬ M.kbar ≤ M.kstar := not_le.2 M.kstar_lt_kbar
    simp only [hbar, hn, ↓reduceIte, psi_kbar]
    exact min_eq_right (by linarith)
  have hmono : M.psi k - M.hbar k ≤ M.psi M.kbar - M.hbar M.kbar :=
    hh.mono_sub ⟨by linarith [M.kstar_pos], hk2.le⟩ ⟨M.kbar_pos.le, le_rfl⟩ hk2.le
  rw [hhk, hhb, psi_kbar] at hmono
  linarith

/-- **Correction (p. 558).** No member of `F` equals the book's `h̄` on `K`; in particular `h̄`
is not the greatest element of `F` (that is `ū`, `isGreatest_up`). -/
theorem hbar_not_mem_F (h : Icc 0 M.kbar →ᵇ ℝ) (hh : h ∈ M.F) :
    ∃ k : Icc 0 M.kbar, h k ≠ M.hbar k := by
  by_contra hall
  push Not at hall
  exact M.not_isInF_hbar (IsInF.congr hh fun k hk => by rw [ext_apply _ _ hk, hall ⟨k, hk⟩])

/-! ### Properties of `F` used by Schauder's Theorem (p. 556) -/

/-- `F` is nonempty (it contains `h_`). -/
theorem F_nonempty : M.F.Nonempty := ⟨_, toBCF_mem_F M.isInF_low⟩

/-- Every `h ∈ F` has `‖h‖ ≤ k̄`. -/
theorem norm_le_of_mem_F {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) : ‖h‖ ≤ M.kbar := by
  refine (norm_le M.kbar_pos.le).2 fun k => ?_
  have h1 := (hh : M.IsInF (M.ext h)).nonneg k k.2
  have h2 := (hh : M.IsInF (M.ext h)).le_kbar k.2
  rw [ext_apply _ _ k.2] at h1 h2
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2

/-- `F` is bounded. -/
theorem F_isBounded : Bornology.IsBounded M.F :=
  (Metric.isBounded_iff_subset_closedBall 0).2 ⟨M.kbar, fun h hh => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact M.norm_le_of_mem_F hh⟩

/-- `F` is convex. -/
theorem F_convex : Convex ℝ M.F := by
  intro h₁ hh₁ h₂ hh₂ a b ha hb hab
  refine (IsInF.convex_comb hh₁ hh₂ ha hb hab).congr fun k hk => ?_
  simp only [ext_apply _ _ hk, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, smul_eq_mul]

/-- `F` is closed in `C(K)`. -/
theorem F_isClosed : IsClosed M.F := by
  refine isClosed_of_closure_subset fun h hh => ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hh
  have hev : ∀ k (hk : k ∈ Icc 0 M.kbar),
      Tendsto (fun n => M.ext (u n) k) atTop (𝓝 (M.ext h k)) := by
    intro k hk
    simp only [ext_apply _ _ hk]
    exact ((continuous_eval_const _).tendsto _).comp hlim
  have hu' : ∀ n, M.IsInF (M.ext (u n)) := hu
  exact
  { cont := (continuous_IccExtend_iff.2 h.continuous).continuousOn
    nonneg := fun k hk => ge_of_tendsto' (hev k hk) fun n => (hu' n).nonneg k hk
    le_psi := fun k hk => le_of_tendsto' (hev k hk) fun n => (hu' n).le_psi k hk
    mono := fun x hx y hy hxy =>
      le_of_tendsto_of_tendsto' (hev x hx) (hev y hy) fun n => (hu' n).mono hx hy hxy
    mono_sub := fun x hx y hy hxy =>
      le_of_tendsto_of_tendsto' (tendsto_const_nhds.sub (hev x hx))
        (tendsto_const_nhds.sub (hev y hy)) fun n => (hu' n).mono_sub hx hy hxy
    ge_self := fun k hk hk' => ge_of_tendsto' (hev k hk) fun n => (hu' n).ge_self k hk hk'
    at_kstar := tendsto_nhds_unique (hev _ M.kstar_mem)
      (tendsto_const_nhds.congr fun n => ((hu' n).at_kstar).symm)
    le_self := fun k hk hk' => le_of_tendsto' (hev k hk) fun n => (hu' n).le_self k hk hk' }

/-- **Proposition 18.5** (p. 557): `F` is an equicontinuous family. The proof uses only the
uniform continuity of `ψ` on the compact `K` and `|h(k′) − h(k)| ≤ |ψ(k′) − ψ(k)|` (the book's
Lipschitz constant `A = f′(0)` is wrong; see `prop_18_5_bound_counterexample`). -/
theorem prop_18_5 : UniformEquicontinuous fun h : M.F => ⇑(h : Icc 0 M.kbar →ᵇ ℝ) := by
  have hu := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := M.kbar)).uniformContinuousOn_of_continuous
      (M.psi_continuousOn.mono Icc_subset_Ici_self))
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, hψ⟩ := hu ε hε
  refine ⟨δ, hδ, fun x y hxy h => ?_⟩
  have h1 := (h.2 : M.IsInF (M.ext h)).abs_sub_le x.2 y.2
  rw [ext_apply _ _ x.2, ext_apply _ _ y.2] at h1
  rw [Real.dist_eq]
  have h2 := hψ x x.2 y y.2 hxy
  rw [Real.dist_eq] at h2
  exact h1.trans_lt h2

/-- **Proposition 18.5** in the book's `ε`–`δ` form (p. 520): one `δ` for all members of `F`. -/
theorem prop_18_5' : ∀ ε > 0, ∃ δ > 0, ∀ x y : Icc 0 M.kbar, dist x y < δ →
    ∀ h ∈ M.F, |h x - h y| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := Metric.uniformEquicontinuous_iff.1 M.prop_18_5 ε hε
  exact ⟨δ, hδ, fun x y hxy h hF => by
    have := hh x y hxy ⟨h, hF⟩
    rwa [Real.dist_eq] at this⟩

/-- `h_` is the least element of `F` (p. 558). -/
theorem isLeast_low : IsLeast M.F (M.toBCF M.low M.isInF_low.cont) := by
  refine ⟨toBCF_mem_F M.isInF_low, fun h hh k => ?_⟩
  have := (hh : M.IsInF (M.ext h)).low_le k.2
  rw [ext_apply _ _ k.2] at this
  exact this

/-- `ū` is the greatest element of `F` (corrected p. 558; the book's `h̄` is not in `F`). -/
theorem isGreatest_up : IsGreatest M.F (M.toBCF M.up M.isInF_up.cont) := by
  refine ⟨toBCF_mem_F M.isInF_up, fun h hh k => ?_⟩
  have := (hh : M.IsInF (M.ext h)).le_up k.2
  rw [ext_apply _ _ k.2] at this
  exact this

end GlobalModel

end StokeyLucasPrescott.EquilibriaWithDistortions
