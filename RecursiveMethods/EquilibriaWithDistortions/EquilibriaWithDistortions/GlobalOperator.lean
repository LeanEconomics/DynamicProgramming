/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.GlobalApproach
import EquilibriaWithDistortions.Schauder
import EquilibriaWithDistortions.SchauderBoundedContinuous
import EquilibriaWithDistortions.MonotoneOperators

/-!
# The operator `T` of SLP §18.3 (7): Exercises 18.5–18.7 and existence (pp. 556–558)

For `h ∈ F`, `(Th)(k)` is "the `y` solving" (§18.3 (7))
  `U′[ψ(k) − y] = β(1 − θ) f′(y) U′[ψ(y) − h(y)]`.
Here `(Th)(k)` is the crossing point `eulerCross` of `GlobalCrossing` with right side `+∞` where
`ψ(y) − h(y) = 0` (Inada condition) and `β(1 − θ) f′(y) U′[ψ(y) − h(y)]` otherwise.

* `ex_18_5_wellDefined` (**Exercise 18.5**, first half, corrected): for `h ∈ F` and `k ∈ K`,
  either `(Th)(k) < ψ(k)` is the unique solution of (7) with positive consumption in both
  periods, or there is no such solution, `h = ψ` on `[0, ψ(k))` and `(Th)(k) = ψ(k)`.
* `ex_18_5` (**Exercise 18.5**, second half): `T(F) ⊆ F`.
* `ex_18_5_counterexample_of` (**Correction**, NOTE 18.3-E): if `ψ(ψ(0)) ≤ k*`, the member
  `h(k) = min{ψ(k), k*}` of `F` makes (7) at `k = 0` have no solution; a concrete model with
  `ψ(ψ(0)) ≤ k*` is `GlobalExamples.ex_18_5_counterexample`.
* `ex_18_6` (**Exercise 18.6**): `T` is continuous on `F`.
* `ex_18_7` (**Exercise 18.7**): `T` is monotone on `F`.
* `exists_equilibrium` (p. 558): Schauder's Theorem gives a fixed point of `T` in `F`.
* `isFixedPt_iff_euler`: the fixed points of `T` in `F` are exactly the `g ∈ F` solving the
  Euler equation (1) at every `k ∈ K` with positive consumption in both periods.
* `least_greatest_equilibria` (p. 558): iterating `T` from the least element `h_` and from the
  greatest element `ū` of `F` (Theorem 17.7 and its Corollary) converges to the least and the
  greatest fixed points of `T` in `F`; `unique_equilibrium_of_tendsto` gives uniqueness when
  the two limits coincide.

**Correction (Exercise 18.5, manual pp. 287–289).** (i) As an equation, (7) need not have a
solution for every `h ∈ F` (`ex_18_5_counterexample_of`); `T` is defined by the extended-real
convention `(Th)(k) = ψ(k)` when the right side is `+∞` on `[0, ψ(k))`. (ii) The manual proves
continuity of `Th` "by the Implicit Function Theorem", which does not apply since `h` is only
continuous. Here `0 ≤ (Th)(k₂) − (Th)(k₁) ≤ ψ(k₂) − ψ(k₁)` for `k₁ ≤ k₂` (`Tval_mono`,
`Tval_sub_le`) gives continuity with the modulus of continuity of `ψ`. (iii) The manual's
"`RHS(y) → ∞` as `y → 0`" is false (`manual_rhs_limit_counterexample`); only
`RHS(0) > LHS(0)` is needed (`eulerBelow_zero`).

**Correction (Exercise 18.6, manual pp. 289–290).** The manual's pointwise step replaces
`h(y)` by `h(k)` ("`ψ(y) − x` with `x̂ = g(k)`") and uses the Implicit Function Theorem for a
non-differentiable `h`. The proof here (`eventually_abs_Tval_sub_le`) is the monotone crossing
argument `eventually_abs_eulerCross_sub_le` with `h` evaluated at `y`; the passage to uniform
convergence uses equicontinuity of `T(F)` and a finite net of `K`, as in the manual.

**Correction (p. 558).** Theorem 17.7 is applied from `ū` (`GlobalApproach.isGreatest_up`),
not from the book's `h̄`, which is not in `F`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology BoundedContinuousFunction

namespace GlobalModel

variable (M : GlobalModel)

/-- Zero next-period consumption at `y`: `ψ(y) − g(y) ≤ 0` (the right side of (7) is `+∞`). -/
def Zd (g : ℝ → ℝ) (y : ℝ) : Prop := M.psi y - g y ≤ 0

/-- The right side of (7) where it is finite: `β(1 − θ) f′(y) U′[ψ(y) − g(y)]`. -/
noncomputable def Rd (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - g y)

/-- **The operator (7)**, pointwise: `(Tg)(k)` is the crossing point of
`y ↦ U′[ψ(k) − y]` and `y ↦ β(1 − θ) f′(y) U′[ψ(y) − g(y)]` on `[0, ψ(k)]`. -/
noncomputable def Tval (g : ℝ → ℝ) (k : ℝ) : ℝ := eulerCross M.U' (M.Zd g) (M.Rd g) (M.psi k)

/-- `β(1 − θ) > 0`. -/
theorem euler_coef_pos : 0 < M.β * (1 - M.θ) := mul_pos M.β_pos (by linarith [M.θ_lt_one])

variable {M}

/-- For `g` satisfying (2)–(6) the right side of (7) is an `IsEulerRHS` on `[0, k̄]`:
nonincreasing (by (3)), continuous where finite, and tending to `+∞` where next-period
consumption vanishes (Inada). -/
theorem IsInF.isEulerRHS {g : ℝ → ℝ} (hg : M.IsInF g) :
    IsEulerRHS M.kbar (M.Zd g) (M.Rd g) where
  zero_anti y y' hy' hyy hyB hz := by
    have h := hg.mono_sub ⟨hy', hyy.trans hyB⟩ ⟨hy'.trans hyy, hyB⟩ hyy
    simp only at h
    exact h.trans hz
  anti y y' hy' hyy hyB hz := by
    have hc' : 0 < M.psi y' - g y' := lt_of_not_ge hz
    have hcc : M.psi y' - g y' ≤ M.psi y - g y :=
      hg.mono_sub ⟨hy', hyy.trans hyB⟩ ⟨hy'.trans hyy, hyB⟩ hyy
    have hU : M.U' (M.psi y - g y) ≤ M.U' (M.psi y' - g y') :=
      M.U'_strictAntiOn.antitoneOn hc' (hc'.trans_le hcc) hcc
    have hf : M.f' y ≤ M.f' y' :=
      M.f'_strictAntiOn.antitoneOn (mem_Ici.2 hy') (mem_Ici.2 (hy'.trans hyy)) hyy
    have hUpos : 0 < M.U' (M.psi y - g y) := M.U'_pos (hc'.trans_le hcc)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hf M.euler_coef_pos.le) hU hUpos.le
      (mul_pos M.euler_coef_pos (M.f'_pos hy')).le
  cont y hy hz := by
    have hc : 0 < M.psi y - g y := lt_of_not_ge hz
    have hcw : ContinuousWithinAt (fun z => M.psi z - g z) (Icc 0 M.kbar) y :=
      ((M.psi_continuousOn.mono Icc_subset_Ici_self) y hy).sub (hg.cont y hy)
    refine ⟨(hcw.eventually_const_lt hc).mono fun z hz => not_le.2 hz, ?_⟩
    exact (continuousWithinAt_const.mul ((M.f'_continuousOn.mono Icc_subset_Ici_self) y hy)).mul
      ((M.U'_continuousOn.continuousAt (Ioi_mem_nhds hc)).comp_continuousWithinAt
        (f := fun z => M.psi z - g z) hcw)
  blowup y hy hz M0 := by
    have hcw : ContinuousWithinAt (fun z => M.psi z - g z) (Icc 0 M.kbar) y :=
      ((M.psi_continuousOn.mono Icc_subset_Ici_self) y hy).sub (hg.cont y hy)
    set m := M.β * (1 - M.θ) * M.f' M.kbar
    have hm : 0 < m := mul_pos M.euler_coef_pos (M.f'_pos M.kbar_pos.le)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
      (M.U'_inada.eventually_gt_atTop (|M0| / m))
    have hlt : M.psi y - g y < ε := lt_of_le_of_lt hz hε
    filter_upwards [hcw.eventually_lt_const hlt, self_mem_nhdsWithin] with z hz1 hzK
    by_cases hz0 : M.psi z - g z ≤ 0
    · exact Or.inl hz0
    · right
      have hc : 0 < M.psi z - g z := lt_of_not_ge hz0
      have hU : |M0| / m < M.U' (M.psi z - g z) := hball ⟨by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc]; exact hz1, hc⟩
      have hf : M.f' M.kbar ≤ M.f' z :=
        M.f'_strictAntiOn.antitoneOn (mem_Ici.2 hzK.1) (mem_Ici.2 M.kbar_pos.le) hzK.2
      have h1 : m ≤ M.β * (1 - M.θ) * M.f' z := mul_le_mul_of_nonneg_left hf M.euler_coef_pos.le
      have h2 : |M0| < m * M.U' (M.psi z - g z) := by
        rwa [div_lt_iff₀ hm, mul_comm] at hU
      have h3 : m * M.U' (M.psi z - g z) ≤ M.β * (1 - M.θ) * M.f' z * M.U' (M.psi z - g z) :=
        mul_le_mul_of_nonneg_right h1 (M.U'_pos hc).le
      have h4 := le_abs_self M0
      simp only [Rd]
      linarith

/-- The left side of (7) is below the right side at `y = 0`: if `ψ(0) − h(0) > 0`, then
`RHS(0) = β(1 − θ) f′(0) U′[ψ(0) − h(0)] > U′[ψ(0)] ≥ U′[ψ(k)] = LHS(0)` (Assumption 18.1d). This
replaces the manual's false claim `RHS(y) → ∞` as `y → 0`. -/
theorem IsInF.eulerBelow_zero {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    EulerBelow M.U' (M.Zd g) (M.Rd g) (M.psi k) 0 := by
  by_cases hz : M.psi 0 - g 0 ≤ 0
  · exact Or.inl hz
  · right
    have hc : 0 < M.psi 0 - g 0 := lt_of_not_ge hz
    have h0K : (0 : ℝ) ∈ Icc 0 M.kbar := ⟨le_rfl, M.kbar_pos.le⟩
    have hψ := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk.1) hk.1
    have hc0 : M.psi 0 - g 0 ≤ M.psi 0 := by linarith [hg.nonneg 0 h0K]
    have h1 : M.U' (M.psi k) ≤ M.U' (M.psi 0) :=
      M.U'_strictAntiOn.antitoneOn (M.psi_pos le_rfl) (M.psi_pos hk.1) hψ
    have h2 : M.U' (M.psi 0) ≤ M.U' (M.psi 0 - g 0) :=
      M.U'_strictAntiOn.antitoneOn hc (M.psi_pos le_rfl) hc0
    have h3 : M.U' (M.psi 0 - g 0) < M.β * (1 - M.θ) * M.f' 0 * M.U' (M.psi 0 - g 0) :=
      lt_mul_left (M.U'_pos hc) M.one_lt_euler_zero
    simp only [Rd, sub_zero]
    linarith

/-- **Correction to the manual's Exercise 18.5** (NOTE 18.3-D): the claim
"`RHS(y) = β(1 − θ) f′(y) U′[ψ(y) − h(y)] → ∞` as `y → 0`" is false for `h = h_ ∈ F` in every
model: there `ψ(0) − h_(0) = f(0) > 0`, and the right side is continuous at `0`. -/
theorem manual_rhs_limit_counterexample (M : GlobalModel) :
    ¬ Tendsto (M.Rd M.low) (𝓝[>] 0) atTop := by
  have h0K : (0 : ℝ) ∈ Icc 0 M.kbar := ⟨le_rfl, M.kbar_pos.le⟩
  have hz : ¬ M.Zd M.low 0 := by
    simp only [Zd, GlobalModel.low, min_eq_left M.kstar_pos.le, sub_zero, not_le]
    exact M.psi_pos le_rfl
  have hc := (M.isInF_low.isEulerRHS.cont 0 h0K hz).2
  have hlim : Tendsto (M.Rd M.low) (𝓝[>] 0) (𝓝 (M.Rd M.low 0)) := by
    refine hc.tendsto.mono_left (le_inf nhdsWithin_le_nhds ?_)
    rw [le_principal_iff]
    filter_upwards [Ioo_mem_nhdsGT M.kbar_pos] with y hy
    exact ⟨hy.1.le, hy.2.le⟩
  exact not_tendsto_atTop_of_tendsto_nhds hlim

/-- `0 ≤ (Tg)(k) ≤ ψ(k)`. -/
theorem Tval_mem_Icc (g : ℝ → ℝ) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    M.Tval g k ∈ Icc 0 (M.psi k) :=
  ⟨eulerCross_nonneg, eulerCross_le (M.psi_pos hk.1).le⟩

/-- **Exercise 18.5, existence and uniqueness (corrected).** For `g` satisfying (2)–(6) and
`k ∈ K`, either `y = (Tg)(k) < ψ(k)`, both consumptions `ψ(k) − y` and `ψ(y) − g(y)` are
positive, (7) holds at `y`, and `y` is its only solution with positive consumptions; or (7) has
no solution with positive consumptions, `g = ψ` on `[0, ψ(k))`, and `(Tg)(k) = ψ(k)` (the
extended-real convention: zero consumption, `∞ = ∞`). -/
theorem IsInF.Tval_spec {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    (M.Tval g k < M.psi k ∧ 0 < M.psi (M.Tval g k) - g (M.Tval g k) ∧
      M.U' (M.psi k - M.Tval g k) = M.β * (1 - M.θ) * M.f' (M.Tval g k) *
        M.U' (M.psi (M.Tval g k) - g (M.Tval g k)) ∧
      ∀ y, 0 ≤ y → y < M.psi k → 0 < M.psi y - g y →
        M.U' (M.psi k - y) = M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - g y) →
        y = M.Tval g k) ∨
    (M.Tval g k = M.psi k ∧ ∀ y, 0 ≤ y → y < M.psi k → g y = M.psi y) := by
  have hP := M.psi_pos hk.1
  have hPB := M.psi_le_kbar hk
  rcases eulerCross_spec M.isMarginalUtility hg.isEulerRHS hP hPB (hg.eulerBelow_zero hk) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, lt_of_not_ge h2, h3, fun y hy0 hyP hc heq => ?_⟩
    exact (eulerCross_unique M.isMarginalUtility hg.isEulerRHS hPB hy0 hyP
      (not_le.2 hc) heq).symm
  · refine Or.inr ⟨h1, fun y hy0 hyP => ?_⟩
    have := h2 y hy0 hyP
    have h' := hg.le_psi y ⟨hy0, hyP.le.trans hPB⟩
    simp only [Zd] at this
    linarith

/-- `k ↦ (Tg)(k)` is nondecreasing on `K`. -/
theorem IsInF.Tval_mono {g : ℝ → ℝ} (hg : M.IsInF g) {a b : ℝ} (ha : a ∈ Icc 0 M.kbar)
    (hb : b ∈ Icc 0 M.kbar) (hab : a ≤ b) : M.Tval g a ≤ M.Tval g b :=
  eulerCross_mono M.isMarginalUtility hg.isEulerRHS
    (M.psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab) (M.psi_le_kbar hb)
    ⟨0, le_rfl, M.psi_pos ha.1, hg.eulerBelow_zero ha⟩

/-- `ψ − Tg` is nondecreasing on `K`: `(Tg)(b) − (Tg)(a) ≤ ψ(b) − ψ(a)` for `a ≤ b`. -/
theorem IsInF.Tval_sub_le {g : ℝ → ℝ} (hg : M.IsInF g) {a b : ℝ} (ha : a ∈ Icc 0 M.kbar)
    (hb : b ∈ Icc 0 M.kbar) (hab : a ≤ b) :
    M.Tval g b ≤ M.Tval g a + (M.psi b - M.psi a) :=
  eulerCross_le_add_sub M.isMarginalUtility hg.isEulerRHS
    (M.psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab) (M.psi_le_kbar hb)

/-- `|(Tg)(a) − (Tg)(b)| ≤ |ψ(a) − ψ(b)|` on `K`. -/
theorem IsInF.abs_Tval_sub_le {g : ℝ → ℝ} (hg : M.IsInF g) {a b : ℝ} (ha : a ∈ Icc 0 M.kbar)
    (hb : b ∈ Icc 0 M.kbar) : |M.Tval g a - M.Tval g b| ≤ |M.psi a - M.psi b| := by
  rcases le_total a b with hab | hab
  · have h1 := hg.Tval_mono ha hb hab
    have h2 := hg.Tval_sub_le ha hb hab
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := hg.Tval_mono hb ha hab
    have h2 := hg.Tval_sub_le hb ha hab
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- (4)–(5) for `Tg`, lower half: if `k ≤ k*` and `g(k) ≥ k` then `(Tg)(k) ≥ k`
(the manual's argument, with `β(1 − θ) f′ > 1` below `k*`). -/
theorem IsInF.le_Tval {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar)
    (hks : k ≤ M.kstar) (hgk : k ≤ g k) : k ≤ M.Tval g k := by
  have hkψ : k < M.psi k := M.lt_psi_of_le_kstar hk.1 hks
  refine le_eulerCross_of_forall fun y hy0 hyk => ⟨hy0, hyk.trans hkψ, ?_⟩
  by_cases hz : M.psi y - g y ≤ 0
  · exact Or.inl hz
  · right
    have hc : 0 < M.psi y - g y := lt_of_not_ge hz
    have hyK : y ∈ Icc 0 M.kbar := ⟨hy0, hyk.le.trans hk.2⟩
    have h1 : M.psi y - g y ≤ M.psi k - g k := hg.mono_sub hyK hk hyk.le
    have h2 : M.psi y - g y ≤ M.psi k - y := by linarith
    have h3 : M.U' (M.psi k - y) ≤ M.U' (M.psi y - g y) :=
      M.U'_strictAntiOn.antitoneOn hc (hc.trans_le h2) h2
    have h4 : M.U' (M.psi y - g y) < M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - g y) :=
      lt_mul_left (M.U'_pos hc) (M.one_lt_euler hy0 (hyk.trans_le hks))
    simp only [Rd]
    linarith

/-- (5)–(6) for `Tg`, upper half: if `k ≥ k*` and `g(k) ≤ k` then `(Tg)(k) ≤ k`. -/
theorem IsInF.Tval_le {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar)
    (hks : M.kstar ≤ k) (hgk : g k ≤ k) : M.Tval g k ≤ k := by
  refine Real.sSup_le (fun y hy => ?_) hk.1
  by_contra hyk
  have hyk := lt_of_not_ge hyk
  have hyK : y ∈ Icc 0 M.kbar := ⟨hy.1, hy.2.1.le.trans (M.psi_le_kbar hk)⟩
  have hyb : y < M.kbar := hy.2.1.trans_le (M.psi_le_kbar hk)
  have hgy : g y ≤ y := hg.le_self y hyK (hks.trans_lt hyk)
  have hψy : y < M.psi y := M.lt_psi hy.1 hyb
  have h1 : M.psi k - g k ≤ M.psi y - g y := hg.mono_sub hk hyK hyk.le
  rcases hy.2.2 with h | h
  · simp only [Zd] at h
    linarith
  · have hc : 0 < M.psi k - y := by linarith [hy.2.1]
    have h2 : M.psi k - y ≤ M.psi y - g y := by linarith
    have h3 : M.U' (M.psi y - g y) ≤ M.U' (M.psi k - y) :=
      M.U'_strictAntiOn.antitoneOn hc (hc.trans_le h2) h2
    have hUp : 0 < M.U' (M.psi y - g y) := M.U'_pos (hc.trans_le h2)
    have h4 : M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - g y) < M.U' (M.psi y - g y) :=
      mul_lt_of_lt_one_left hUp (M.euler_lt_one (hks.trans_lt hyk))
    simp only [Rd] at h
    linarith

/-- **Exercise 18.5, `T : F → F`** (pointwise form): if `g` satisfies (2)–(6) so does `Tg`. -/
theorem IsInF.isInF_Tval {g : ℝ → ℝ} (hg : M.IsInF g) : M.IsInF (M.Tval g) where
  cont := by
    rw [Metric.continuousOn_iff]
    intro k0 hk0 ε hε
    obtain ⟨δ, hδ, hψ⟩ := Metric.continuousOn_iff.1
      (M.psi_continuousOn.mono (Icc_subset_Ici_self : Icc (0 : ℝ) M.kbar ⊆ Ici 0)) k0 hk0 ε hε
    refine ⟨δ, hδ, fun k hk hd => ?_⟩
    rw [Real.dist_eq]
    have := hψ k hk hd
    rw [Real.dist_eq] at this
    exact (hg.abs_Tval_sub_le hk hk0).trans_lt this
  nonneg k hk := (M.Tval_mem_Icc g hk).1
  le_psi k hk := (M.Tval_mem_Icc g hk).2
  mono a ha b hb hab := hg.Tval_mono ha hb hab
  mono_sub a ha b hb hab := by
    have := hg.Tval_sub_le ha hb hab
    simp only
    linarith
  ge_self k hk hks := hg.le_Tval hk hks.le (hg.ge_self k hk hks)
  at_kstar := le_antisymm (hg.Tval_le M.kstar_mem le_rfl hg.at_kstar.le)
    (hg.le_Tval M.kstar_mem le_rfl hg.at_kstar.ge)
  le_self k hk hks := hg.Tval_le hk hks.le (hg.le_self k hk hks)

variable (M)

open Classical in
/-- **The operator `T`** on `C(K)` (§18.3 (7)): `T h = (k ↦ (T(ext h))(k))` for `h ∈ F`; off `F`
it is the identity (its values there play no role). -/
noncomputable def T (h : Icc 0 M.kbar →ᵇ ℝ) : Icc 0 M.kbar →ᵇ ℝ :=
  if hh : h ∈ M.F then M.toBCF (M.Tval (M.ext h)) (IsInF.isInF_Tval hh).cont else h

variable {M}

/-- `T h` evaluates pointwise as `Tval`. -/
theorem T_apply {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) (k : Icc 0 M.kbar) :
    M.T h k = M.Tval (M.ext h) k := by
  simp only [T, hh, ↓reduceDIte, toBCF_apply]

/-- `ext (T h)` agrees with `Tval (ext h)` on `K`. -/
theorem ext_T {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    M.ext (M.T h) k = M.Tval (M.ext h) k := by
  rw [ext_apply _ _ hk, T_apply hh]

variable (M)

/-- **Exercise 18.5** (p. 556): `T` maps `F` into `F`. -/
theorem ex_18_5 : MapsTo M.T M.F M.F := fun _ hh =>
  (IsInF.isInF_Tval hh).congr fun _ hk => (ext_T hh hk).symm

/-- **Exercise 18.5** (p. 556), well-definedness in the corrected sense: for `h ∈ F` and
`k ∈ K`, either `(Th)(k)` is the unique solution of (7) with positive consumption in both
periods, or (7) has no such solution, `h = ψ` on `[0, ψ(k))` and `(Th)(k) = ψ(k)`. -/
theorem ex_18_5_wellDefined {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) (k : Icc 0 M.kbar) :
    (M.T h k < M.psi k ∧ 0 < M.psi (M.T h k) - M.ext h (M.T h k) ∧
      M.U' (M.psi k - M.T h k) = M.β * (1 - M.θ) * M.f' (M.T h k) *
        M.U' (M.psi (M.T h k) - M.ext h (M.T h k)) ∧
      ∀ y, 0 ≤ y → y < M.psi k → 0 < M.psi y - M.ext h y →
        M.U' (M.psi k - y) = M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - M.ext h y) →
        y = M.T h k) ∨
    (M.T h k = M.psi k ∧ ∀ y, 0 ≤ y → y < M.psi k → M.ext h y = M.psi y) := by
  rw [T_apply hh]
  exact IsInF.Tval_spec hh k.2

/-- **Exercise 18.7** (p. 558): `T` is monotone on `F`: `h ≤ ĥ` implies `Th ≤ Tĥ`. -/
theorem ex_18_7 : MonotoneOn M.T M.F := by
  intro h hh h' hh' hle k
  change M.T h k ≤ M.T h' k
  rw [T_apply hh, T_apply hh']
  have hk := k.2
  refine eulerCross_mono_rhs (fun y hy0 hyP hz => ?_) (fun y hy0 hyP hz hz' => ?_)
    ⟨0, le_rfl, M.psi_pos hk.1, IsInF.eulerBelow_zero hh hk⟩
  · have hyK : y ∈ Icc 0 M.kbar := ⟨hy0, hyP.le.trans (M.psi_le_kbar hk)⟩
    have : h ⟨y, hyK⟩ ≤ h' ⟨y, hyK⟩ := hle ⟨y, hyK⟩
    simp only [Zd, ext_apply _ _ hyK] at hz ⊢
    linarith
  · have hyK : y ∈ Icc 0 M.kbar := ⟨hy0, hyP.le.trans (M.psi_le_kbar hk)⟩
    have hle' : h ⟨y, hyK⟩ ≤ h' ⟨y, hyK⟩ := hle ⟨y, hyK⟩
    simp only [Zd, ext_apply _ _ hyK] at hz hz'
    have hc' : 0 < M.psi y - h' ⟨y, hyK⟩ := lt_of_not_ge hz'
    have hcc : M.psi y - h' ⟨y, hyK⟩ ≤ M.psi y - h ⟨y, hyK⟩ := by linarith
    have hU := M.U'_strictAntiOn.antitoneOn hc' (hc'.trans_le hcc) hcc
    simp only [Rd, ext_apply _ _ hyK]
    exact mul_le_mul_of_nonneg_left hU (mul_pos M.euler_coef_pos (M.f'_pos hy0)).le

/-- The pointwise step of **Exercise 18.6**: if `h' → h` in `F` then `(Th')(k) → (Th)(k)`
for every `k ∈ K` (the monotone crossing argument, with `h` evaluated at the unknown `y`). -/
theorem eventually_abs_Tval_sub_le {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) {k : ℝ}
    (hk : k ∈ Icc 0 M.kbar) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ h' : M.F in 𝓝 ⟨h, hh⟩, |M.Tval (M.ext h') k - M.Tval (M.ext h) k| ≤ η := by
  have hP : 0 < M.psi k := M.psi_pos hk.1
  have hPB := M.psi_le_kbar hk
  refine eventually_abs_eulerCross_sub_le (Zs := fun h' : M.F => M.Zd (M.ext h'))
    (Rs := fun h' : M.F => M.Rd (M.ext h')) M.isMarginalUtility (IsInF.isEulerRHS hh)
    (fun h' => IsInF.isEulerRHS h'.2) hP hPB (fun y hy0 hyP => ?_) hη
  have hyK : y ∈ Icc 0 M.kbar := ⟨hy0, hyP.le.trans hPB⟩
  have hcont : Tendsto (fun h' : M.F => M.ext h' y) (𝓝 ⟨h, hh⟩) (𝓝 (M.ext h y)) := by
    simp only [ext_apply _ _ hyK]
    exact ((continuous_eval_const _).comp continuous_subtype_val).tendsto _
  have hm : 0 < M.β * (1 - M.θ) * M.f' y := mul_pos M.euler_coef_pos (M.f'_pos hy0)
  constructor
  · intro hz M0
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
      (M.U'_inada.eventually_gt_atTop (|M0| / (M.β * (1 - M.θ) * M.f' y)))
    filter_upwards [Metric.tendsto_nhds.1 hcont ε hε] with h' hd
    rw [Real.dist_eq] at hd
    simp only [Zd] at hz ⊢
    by_cases hz0 : M.psi y - M.ext h' y ≤ 0
    · exact Or.inl hz0
    · right
      have hc : 0 < M.psi y - M.ext h' y := lt_of_not_ge hz0
      have hU := hball ⟨by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc]
        linarith [(abs_lt.1 hd).1], hc⟩
      simp only [mem_ofPred_eq] at hU
      rw [div_lt_iff₀ hm] at hU
      simp only [Rd]
      linarith [le_abs_self M0]
  · intro hz
    have hc : 0 < M.psi y - M.ext h y := lt_of_not_ge hz
    have hcon : Tendsto (fun h' : M.F => M.psi y - M.ext h' y) (𝓝 ⟨h, hh⟩)
        (𝓝 (M.psi y - M.ext h y)) := tendsto_const_nhds.sub hcont
    refine ⟨(hcon.eventually_const_lt hc).mono fun h' hh' => not_le.2 hh', ?_⟩
    exact tendsto_const_nhds.mul
      ((M.U'_continuousOn.continuousAt (Ioi_mem_nhds hc)).tendsto.comp hcon)

/-- **Exercise 18.6** (p. 558): `T` is continuous on `F` (sup norm). Pointwise convergence
(`eventually_abs_Tval_sub_le`) becomes uniform because `T(F) ⊆ F` is equicontinuous and `K` is
covered by finitely many small balls. -/
theorem ex_18_6 : ContinuousOn M.T M.F := by
  rw [continuousOn_iff_continuous_domRestrict, Metric.continuous_iff']
  rintro ⟨h, hh⟩ ε hε
  obtain ⟨δ, hδ, hψ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := M.kbar)).uniformContinuousOn_of_continuous
      (M.psi_continuousOn.mono Icc_subset_Ici_self)) (ε / 4) (by linarith)
  obtain ⟨t, htK, htfin, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_Icc (a := (0 : ℝ)) (b := M.kbar)) hδ
  have hev : ∀ᶠ h' : M.F in 𝓝 ⟨h, hh⟩, ∀ i ∈ t,
      |M.Tval (M.ext h') i - M.Tval (M.ext h) i| ≤ ε / 4 :=
    (htfin.eventually_all).2 fun i hi => M.eventually_abs_Tval_sub_le hh (htK hi) (by linarith)
  filter_upwards [hev] with h' hh'
  change dist (M.T (h' : Icc 0 M.kbar →ᵇ ℝ)) (M.T h) < ε
  refine lt_of_le_of_lt ((dist_le (by linarith)).2 fun k => ?_) (by linarith : 3 * ε / 4 < ε)
  obtain ⟨i, hi, hki⟩ := mem_iUnion₂.1 (hcover k.2)
  have hiK := htK hi
  have hd : dist (M.psi k) (M.psi i) < ε / 4 := hψ k k.2 i hiK hki
  rw [Real.dist_eq] at hd
  have e1 := (IsInF.isInF_Tval h'.2).abs_sub_le k.2 hiK
  have e2 := (IsInF.isInF_Tval hh).abs_sub_le hiK k.2
  have e3 := hh' i hi
  rw [abs_sub_comm (M.psi i)] at e2
  rw [Real.dist_eq, T_apply h'.2, T_apply hh]
  calc |M.Tval (M.ext h') k - M.Tval (M.ext h) k|
      ≤ |M.Tval (M.ext h') k - M.Tval (M.ext h') i| +
          |M.Tval (M.ext h') i - M.Tval (M.ext h) i| +
          |M.Tval (M.ext h) i - M.Tval (M.ext h) k| := by
        have := abs_sub_le (M.Tval (M.ext h') k) (M.Tval (M.ext h') i) (M.Tval (M.ext h) k)
        have := abs_sub_le (M.Tval (M.ext h') i) (M.Tval (M.ext h) i) (M.Tval (M.ext h) k)
        linarith
    _ ≤ 3 * ε / 4 := by linarith

/-- `F` is compact (closed, and totally bounded by Arzelà–Ascoli and Proposition 18.5). -/
theorem F_isCompact : IsCompact M.F :=
  (totallyBounded_of_equicontinuous isCompact_univ.totallyBounded M.F_isBounded
    M.prop_18_5').isCompact_of_isClosed M.F_isClosed

/-- **Existence of an equilibrium** (p. 558, Schauder's Theorem): `T` has a fixed point in `F`,
i.e. a continuous `g ∈ F` solving (1). -/
theorem exists_equilibrium : ∃ g ∈ M.F, M.T g = g :=
  schauder M.F_isCompact M.F_convex M.F_nonempty M.ex_18_6 M.ex_18_5

variable {M} in
/-- At a fixed point of `T` in `F` consumption is positive everywhere: `(Tg)(k) < ψ(k)` for
all `k ∈ K`. (If consumption were zero at some `k`, then `g = ψ` on `[0, ψ(k))`, and since
fixed points propagate zero consumption upward, `g = ψ` up to `k*`, contradicting
`g(k*) = k* < ψ(k*)`.) -/
theorem IsInF.Tval_lt_psi_of_fixed {g : ℝ → ℝ} (hg : M.IsInF g)
    (hfix : ∀ k ∈ Icc 0 M.kbar, M.Tval g k = g k) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    M.Tval g k < M.psi k := by
  by_contra hcon
  have hTk : M.Tval g k = M.psi k := le_antisymm (M.Tval_mem_Icc g hk).2 (not_lt.1 hcon)
  -- `A`: the `z ∈ [0, k̄]` with `g = ψ` on `[0, z)`
  set A := {z : ℝ | 0 ≤ z ∧ z ≤ M.kbar ∧ ∀ y, 0 ≤ y → y < z → g y = M.psi y}
  have hcase : ∀ z ∈ Icc 0 M.kbar, M.Tval g z = M.psi z → M.psi z ∈ A := by
    intro z hz hTz
    rcases hg.Tval_spec hz with ⟨h1, -⟩ | ⟨-, h2⟩
    · linarith
    · exact ⟨(M.psi_pos hz.1).le, M.psi_le_kbar hz, h2⟩
  have hkA : M.psi k ∈ A := hcase k hk hTk
  have hgk : g M.kstar ≠ M.psi M.kstar := by
    rw [hg.at_kstar]; exact (M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl).ne
  have hAle : ∀ z ∈ A, z ≤ M.kstar := fun z hz => by
    by_contra hzk
    exact hgk (hz.2.2 M.kstar M.kstar_pos.le (lt_of_not_ge hzk))
  have hAne : A.Nonempty := ⟨_, hkA⟩
  have hAbdd : BddAbove A := ⟨M.kstar, hAle⟩
  set s := sSup A
  have hs0 : 0 < s := (M.psi_pos hk.1).trans_le (le_csSup hAbdd hkA)
  have hsk : s ≤ M.kstar := csSup_le hAne hAle
  -- every `y ∈ [0, s)` has `g y = ψ y`, hence `ψ y ∈ A`, hence `ψ y ≤ s`
  have hbelow : ∀ y, 0 ≤ y → y < s → M.psi y ≤ s := by
    intro y hy0 hys
    obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hAne hys
    have hyK : y ∈ Icc 0 M.kbar := ⟨hy0, (hyz.trans_le hz.2.1).le⟩
    have hgy : g y = M.psi y := hz.2.2 y hy0 hyz
    exact le_csSup hAbdd (hcase y hyK ((hfix y hyK).trans hgy))
  have hψs : M.psi s ≤ s := by
    have hc : ContinuousAt M.psi s := M.psi_continuousOn.continuousAt (Ici_mem_nhds hs0)
    refine le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio s))) ?_
    filter_upwards [Ioo_mem_nhdsLT hs0] with y hy
    exact hbelow y hy.1.le hy.2
  linarith [M.lt_psi_of_le_kstar hs0.le hsk]

/-- **Fixed points of `T` are the equilibria** (p. 556): `h ∈ F` is a fixed point of `T` iff the
Euler equation (1) holds at every `k ∈ K`, with positive consumption `ψ(k) − h(k)` today and
`ψ(h(k)) − h(h(k))` tomorrow. -/
theorem isFixedPt_iff_euler {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) :
    M.T h = h ↔ ∀ k ∈ Icc 0 M.kbar, 0 < M.psi k - M.ext h k ∧
      0 < M.psi (M.ext h k) - M.ext h (M.ext h k) ∧
      M.U' (M.psi k - M.ext h k) =
        M.β * (1 - M.θ) * M.f' (M.ext h k) * M.U' (M.psi (M.ext h k) - M.ext h (M.ext h k)) := by
  have hg : M.IsInF (M.ext h) := hh
  constructor
  · intro hfix
    have hfix' : ∀ k ∈ Icc 0 M.kbar, M.Tval (M.ext h) k = M.ext h k := fun k hk => by
      rw [← ext_T hh hk, hfix]
    intro k hk
    rcases hg.Tval_spec hk with ⟨h1, h2, h3, -⟩ | ⟨h1, -⟩
    · rw [hfix' k hk] at h1 h2 h3
      exact ⟨by linarith, h2, h3⟩
    · exact absurd h1 (hg.Tval_lt_psi_of_fixed hfix' hk).ne
  · intro heq
    ext k
    rw [T_apply hh, ← ext_apply _ _ k.2]
    obtain ⟨h1, h2, h3⟩ := heq k k.2
    rcases hg.Tval_spec k.2 with ⟨-, -, -, huniq⟩ | ⟨-, h5⟩
    · exact (huniq _ (hg.nonneg k k.2) (by linarith) h2 h3).symm
    · exact absurd (h5 _ (hg.nonneg k k.2) (by linarith)) (by linarith)

/-- `T(F)` is equicontinuous (it is contained in `F`, Proposition 18.5). -/
theorem T_equicontinuous : UniformEquicontinuous fun h : M.F => ⇑(M.T h) :=
  M.prop_18_5.comp fun h : M.F => (⟨M.T h, M.ex_18_5 h.2⟩ : M.F)

/-- **Least and greatest equilibria** (p. 558, Exercise 18.7 with Theorem 17.7 and its
Corollary, corrected): `Tⁿh_` converges in `C(K)` to the least fixed point of `T` in `F`, and
`Tⁿū` (not `Tⁿh̄`, since `h̄ ∉ F`) converges to the greatest one; every fixed point lies between
them. -/
theorem least_greatest_equilibria :
    ∃ f ∈ M.F, ∃ g ∈ M.F, M.T f = f ∧ M.T g = g ∧
      Tendsto (fun n => M.T^[n] (M.toBCF M.low M.isInF_low.cont)) atTop (𝓝 f) ∧
      Tendsto (fun n => M.T^[n] (M.toBCF M.up M.isInF_up.cont)) atTop (𝓝 g) ∧
      ∀ h ∈ M.F, M.T h = h → f ≤ h ∧ h ≤ g :=
  corollary_17_7 isCompact_univ.totallyBounded M.F_isClosed M.F_isBounded M.ex_18_5 M.ex_18_6
    M.ex_18_7 M.T_equicontinuous M.isLeast_low M.isGreatest_up

/-- **Uniqueness test** (p. 558): if the iterates from `h_` and from `ū` have the same limit,
that limit is the only fixed point of `T` in `F`. -/
theorem unique_equilibrium_of_tendsto {f : Icc 0 M.kbar →ᵇ ℝ}
    (hl : Tendsto (fun n => M.T^[n] (M.toBCF M.low M.isInF_low.cont)) atTop (𝓝 f))
    (hu : Tendsto (fun n => M.T^[n] (M.toBCF M.up M.isInF_up.cont)) atTop (𝓝 f)) :
    f ∈ M.F ∧ M.T f = f ∧ ∀ h ∈ M.F, M.T h = h → h = f :=
  corollary_17_7_unique isCompact_univ.totallyBounded M.F_isClosed M.F_isBounded M.ex_18_5
    M.ex_18_6 M.ex_18_7 M.T_equicontinuous M.isLeast_low M.isGreatest_up hl hu

/-- The iterates `Tⁿh_` increase (the computational algorithm of p. 554). -/
theorem monotone_iterate_low : Monotone fun n => M.T^[n] (M.toBCF M.low M.isInF_low.cont) :=
  monotone_iterate_of_le M.ex_18_5 M.ex_18_7 M.isLeast_low.1
    (M.isLeast_low.2 (M.ex_18_5 M.isLeast_low.1))

/-- The iterates `Tⁿū` decrease. -/
theorem antitone_iterate_up : Antitone fun n => M.T^[n] (M.toBCF M.up M.isInF_up.cont) :=
  antitone_iterate_of_ge M.ex_18_5 M.ex_18_7 M.isGreatest_up.1
    (M.isGreatest_up.2 (M.ex_18_5 M.isGreatest_up.1))

/-! ### NOTE 18.3-E: (7) need not have a solution -/

/-- The member `h(k) = min{ψ(k), k*}` of `F` used in NOTE 18.3-E (it equals the book's `h̄` on
`[0, k*]` and is `k*` beyond). -/
noncomputable def hE (k : ℝ) : ℝ := min (M.psi k) M.kstar

/-- `hE` satisfies (2)–(6). -/
theorem isInF_hE : M.IsInF M.hE where
  cont := ContinuousOn.inf (M.psi_continuousOn.mono Icc_subset_Ici_self) continuousOn_const
  nonneg k hk := le_min (M.psi_pos hk.1).le M.kstar_pos.le
  le_psi _ _ := min_le_left _ _
  mono x hx y hy hxy :=
    min_le_min_right _ (M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy)
  mono_sub x hx y hy hxy := by
    have := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy
    simp only [hE]
    rcases le_total (M.psi x) M.kstar with h1 | h1 <;>
      rcases le_total (M.psi y) M.kstar with h2 | h2 <;>
      simp only [min_eq_left, min_eq_right, h1, h2] <;> linarith
  ge_self k hk hks := le_min (M.lt_psi_of_le_kstar hk.1 hks.le).le hks.le
  at_kstar := min_eq_right (M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl).le
  le_self _ _ hks := (min_le_right _ _).trans hks.le

/-- **Correction to Exercise 18.5** (NOTE 18.3-E): if `ψ(ψ(0)) ≤ k*`, then for the member
`hE = min{ψ, k*}` of `F` the equation (7) at `k = 0` has no solution `y ∈ [0, ψ(0))` with
positive next-period consumption (the right side is `+∞` on all of `[0, ψ(0)]`), and the operator
takes the extended-real value `(T hE)(0) = ψ(0)`. -/
theorem ex_18_5_counterexample_of (hψψ : M.psi (M.psi 0) ≤ M.kstar) :
    M.IsInF M.hE ∧
      (¬ ∃ y, 0 ≤ y ∧ y < M.psi 0 ∧ 0 < M.psi y - M.hE y ∧
        M.U' (M.psi 0 - y) = M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - M.hE y)) ∧
      M.Tval M.hE 0 = M.psi 0 := by
  have hzero : ∀ y, 0 ≤ y → y < M.psi 0 → M.psi y - M.hE y = 0 := by
    intro y hy0 hy
    have : M.psi y ≤ M.kstar :=
      (M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hy0) (mem_Ici.2 (M.psi_pos le_rfl).le)
        hy.le).trans hψψ
    simp only [hE, min_eq_left this, sub_self]
  refine ⟨M.isInF_hE, ?_, ?_⟩
  · rintro ⟨y, hy0, hy, hc, -⟩
    rw [hzero y hy0 hy] at hc
    exact lt_irrefl _ hc
  · rcases M.isInF_hE.Tval_spec ⟨le_rfl, M.kbar_pos.le⟩ with ⟨h1, h2, -⟩ | ⟨h1, -⟩
    · exact absurd (hzero _ (M.Tval_mem_Icc _ ⟨le_rfl, M.kbar_pos.le⟩).1 h1) h2.ne'
    · exact h1

end GlobalModel

end StokeyLucasPrescott.EquilibriaWithDistortions
