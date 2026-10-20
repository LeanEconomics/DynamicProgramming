/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.GlobalExamples

/-!
# The stochastic extension of §18.3: Exercises 18.8 and 18.9 (pp. 558–560)

Shocks `ξ ∈ Ξ = {ξ_j}` (a finite type `ι`) follow a Markov chain with transition matrix `π`; the
technology is `f(·, ξ_j)`, with after-tax income `ψ_j(k) = f(k, ξ_j) − θ k f′(k, ξ_j)`. Parts (d),
(e) of Assumption 18.1 and Assumption 18.2 hold "for each `ξ_j`" (`StochModel.tech j` is a
`GlobalModel`), and `K = [0, B]`, `B = max_j k̄_j`. An equilibrium is `g : K × Ξ → K` with
(§18.3 (8))
  `U′[ψ_i(k) − g_i(k)] = β(1 − θ) Σ_j π_ij f′_j[g_i(k)] U′{ψ_j[g_i(k)] − g_j[g_i(k)]}`,
and `F` is the set of `h` with `0 ≤ h_j ≤ ψ_j` and `h_j`, `ψ_j − h_j` nondecreasing (p. 559).
The operator `T` of (9) is again a crossing point (`Ts`, built from `eulerCross`).

* `ex_18_8_counterexample` (**Correction**, Exercise 18.8 is false as posed, NOTE 18.3-J(i)):
  in a two-shock model with log-like utility `U = √` satisfying every per-shock assumption,
  (9) has no solution for `h ≡ 0 ∈ F` at `(k, ξ) = (0, ξ_2)` — the agent wants a corner `y = 0`.
  The general mechanism is `no_solution_of_crossState_fails`.
* `Ts_psi`, `no_solution_at_psi` (**Correction**, NOTE 18.3-J(ii)): `h = ψ` belongs to `F`, the
  right side of (9) is `+∞` everywhere for it, so (9) has no solution at any `(k, ξ_i)`; with the
  extended-real convention `Tψ = ψ`, so the greatest element of `F` is a degenerate fixed point
  (zero consumption forever). The book's "existence follows from Schauder's Theorem" therefore
  produces nothing in the stochastic case without a smaller `F`.
* `ex_18_8_spec_KT` (corrected Exercise 18.8, Kuhn–Tucker form, no extra assumption): for every
  `h ∈ F` and `(k, ξ_i)`, `(Th)_i(k)` is an interior solution of (9), or a zero-consumption corner,
  or a zero-saving corner at which (9) holds as `RHS ≤ LHS`; and `ex_18_8`: `T : F → F`.
* `ex_18_8_spec` (corrected Exercise 18.8, equation form): under the cross-state condition
  `CrossState` — `U′(ψ_i(0)) < β(1 − θ) Σ_j π_ij f′_j(0) U′(ψ_j(0))` for every `i`, which for one
  shock is exactly `β(1 − θ) f′(0) > 1` of Assumption 18.1d — the zero-saving corner cannot occur.
* `ex_18_8_mono`: `T` is monotone on `F` (the analogue of Exercise 18.7).

**Correction (p. 560, cross-reference).** "the proof of Proposition 6" should read
"Proposition 5" (Proposition 18.5, `GlobalModel.prop_18_5`); Chapter 18 has no Proposition 6.

**Exercise 18.9** (p. 560, `Ξ` a closed bounded interval) is treated in `GlobalContinuum`:
with jointly continuous technologies, a Feller transition, and `F` restricted to strictly
positive consumption, `T` is well defined, maps `F₊` into `F₊` and is monotone. Continuity,
equicontinuity and the least and greatest fixed points in the finite case are in
`GlobalStochasticEquilibrium`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- **The stochastic model** of p. 558. `tech j` is the economy with technology `f(·, ξ_j)`; all
share `β`, `θ`, `U`, `U′`. `B = max_j k̄_j` and `π` is a transition matrix. -/
structure StochModel (ι : Type) [Fintype ι] where
  tech : ι → GlobalModel
  β : ℝ
  θ : ℝ
  U : ℝ → ℝ
  U' : ℝ → ℝ
  B : ℝ
  π : ι → ι → ℝ
  tech_β : ∀ j, (tech j).β = β
  tech_θ : ∀ j, (tech j).θ = θ
  tech_U : ∀ j, (tech j).U = U
  tech_U' : ∀ j, (tech j).U' = U'
  kbar_le : ∀ j, (tech j).kbar ≤ B
  B_eq : ∃ j, (tech j).kbar = B
  π_nonneg : ∀ i j, 0 ≤ π i j
  π_sum : ∀ i, ∑ j, π i j = 1

namespace StochModel

variable {ι : Type} [Fintype ι] (S : StochModel ι)

/-- `B > 0`. -/
theorem B_pos : 0 < S.B := by
  obtain ⟨j, hj⟩ := S.B_eq
  rw [← hj]; exact (S.tech j).kbar_pos

/-- The common marginal utility is a marginal utility. -/
theorem isMarginalUtility : IsMarginalUtility S.U' := by
  obtain ⟨j, -⟩ := S.B_eq
  rw [← S.tech_U' j]; exact (S.tech j).isMarginalUtility

/-- `β(1 − θ) > 0`. -/
theorem coef_pos : 0 < S.β * (1 - S.θ) := by
  obtain ⟨j, -⟩ := S.B_eq
  rw [← S.tech_β j, ← S.tech_θ j]; exact (S.tech j).euler_coef_pos

/-- `ψ_j` maps `[0, B]` into `(0, B]`. -/
theorem psi_le_B (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) : (S.tech j).psi k ≤ S.B := by
  rcases le_or_gt k (S.tech j).kbar with h | h
  · exact ((S.tech j).psi_le_kbar ⟨hk.1, h⟩).trans (S.kbar_le j)
  · exact ((S.tech j).psi_lt k h).le.trans hk.2

/-- **The set `F`** of p. 559: for each `j`, `h_j` is continuous on `K = [0, B]`,
`0 ≤ h_j ≤ ψ_j`, and `h_j`, `ψ_j − h_j` are nondecreasing. -/
structure IsInFs (h : ι → ℝ → ℝ) : Prop where
  cont : ∀ j, ContinuousOn (h j) (Icc 0 S.B)
  nonneg : ∀ j, ∀ k ∈ Icc 0 S.B, 0 ≤ h j k
  le_psi : ∀ j, ∀ k ∈ Icc 0 S.B, h j k ≤ (S.tech j).psi k
  mono : ∀ j, MonotoneOn (h j) (Icc 0 S.B)
  mono_sub : ∀ j, MonotoneOn (fun k => (S.tech j).psi k - h j k) (Icc 0 S.B)

/-- Some next-period consumption reachable from state `i` is zero at `y` (right side `+∞`). -/
def Zs (h : ι → ℝ → ℝ) (i : ι) (y : ℝ) : Prop :=
  ∃ j, 0 < S.π i j ∧ (S.tech j).psi y - h j y ≤ 0

/-- The right side of (9): `β(1 − θ) Σ_j π_ij f′_j(y) U′[ψ_j(y) − h_j(y)]`. -/
noncomputable def Rs (h : ι → ℝ → ℝ) (i : ι) (y : ℝ) : ℝ :=
  S.β * (1 - S.θ) * ∑ j, S.π i j * ((S.tech j).f' y * S.U' ((S.tech j).psi y - h j y))

/-- **The operator (9)**: `(Th)_i(k)` is the crossing point of `y ↦ U′[ψ_i(k) − y]` and the right
side of (9). -/
noncomputable def Ts (h : ι → ℝ → ℝ) (i : ι) (k : ℝ) : ℝ :=
  eulerCross S.U' (S.Zs h i) (S.Rs h i) ((S.tech i).psi k)

variable {S}

/-- One term of the right side of (9) is nonincreasing in `y`. -/
theorem IsInFs.term_anti {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i j : ι) {y y' : ℝ} (hy' : 0 ≤ y')
    (hyy : y' ≤ y) (hyB : y ≤ S.B) (hz : ¬ S.Zs h i y') :
    S.π i j * ((S.tech j).f' y * S.U' ((S.tech j).psi y - h j y)) ≤
      S.π i j * ((S.tech j).f' y' * S.U' ((S.tech j).psi y' - h j y')) := by
  rcases (S.π_nonneg i j).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hc' : 0 < (S.tech j).psi y' - h j y' := lt_of_not_ge fun hle => hz ⟨j, hpos, hle⟩
    have hcc : (S.tech j).psi y' - h j y' ≤ (S.tech j).psi y - h j y :=
      hh.mono_sub j ⟨hy', hyy.trans hyB⟩ ⟨hy'.trans hyy, hyB⟩ hyy
    have hU : S.U' ((S.tech j).psi y - h j y) ≤ S.U' ((S.tech j).psi y' - h j y') :=
      S.isMarginalUtility.strictAnti.antitoneOn hc' (hc'.trans_le hcc) hcc
    have hf : (S.tech j).f' y ≤ (S.tech j).f' y' :=
      (S.tech j).f'_strictAntiOn.antitoneOn (mem_Ici.2 hy') (mem_Ici.2 (hy'.trans hyy)) hyy
    have hUpos := S.isMarginalUtility.pos _ (hc'.trans_le hcc)
    exact mul_le_mul_of_nonneg_left (mul_le_mul hf hU hUpos.le
      ((S.tech j).f'_pos hy').le) hpos.le

/-- Every term of the right side of (9) is nonnegative where no next-period consumption is
zero. -/
theorem IsInFs.term_nonneg (i j : ι) {h : ι → ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y)
    (hz : ¬ S.Zs h i y) :
    0 ≤ S.π i j * ((S.tech j).f' y * S.U' ((S.tech j).psi y - h j y)) := by
  rcases (S.π_nonneg i j).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hc : 0 < (S.tech j).psi y - h j y := lt_of_not_ge fun hle => hz ⟨j, hpos, hle⟩
    exact mul_nonneg hpos.le (mul_nonneg ((S.tech j).f'_pos hy).le
      (S.isMarginalUtility.pos _ hc).le)

/-- For `h ∈ F` the right side of (9) is an `IsEulerRHS` on `[0, B]`. -/
theorem IsInFs.isEulerRHS {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι) :
    IsEulerRHS S.B (S.Zs h i) (S.Rs h i) where
  zero_anti y y' hy' hyy hyB hz := by
    obtain ⟨j, hj, hc⟩ := hz
    refine ⟨j, hj, ?_⟩
    have := hh.mono_sub j ⟨hy', hyy.trans hyB⟩ ⟨hy'.trans hyy, hyB⟩ hyy
    simp only at this
    linarith
  anti y y' hy' hyy hyB hz :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hh.term_anti i j hy' hyy hyB hz)
      S.coef_pos.le
  cont y hy hz := by
    have hpos : ∀ j, 0 < S.π i j → 0 < (S.tech j).psi y - h j y :=
      fun j hj => lt_of_not_ge fun hle => hz ⟨j, hj, hle⟩
    have hcw : ∀ j, ContinuousWithinAt (fun z => (S.tech j).psi z - h j z) (Icc 0 S.B) y :=
      fun j => (((S.tech j).psi_continuousOn.mono Icc_subset_Ici_self) y hy).sub
        (hh.cont j y hy)
    refine ⟨?_, ?_⟩
    · have : ∀ᶠ z in 𝓝[Icc 0 S.B] y, ∀ j, 0 < S.π i j → 0 < (S.tech j).psi z - h j z := by
        refine eventually_all.2 fun j => ?_
        by_cases hj : 0 < S.π i j
        · exact ((hcw j).eventually_const_lt (hpos j hj)).mono fun z hz _ => hz
        · exact Eventually.of_forall fun z hj' => absurd hj' hj
      exact this.mono fun z hz ⟨j, hj, hle⟩ => absurd (hz j hj) (not_lt.2 hle)
    · refine continuousWithinAt_const.mul ?_
      refine tendsto_finsetSum _ fun j _ => ?_
      rcases (S.π_nonneg i j).eq_or_lt with h0 | hj
      · rw [← h0]; simpa using tendsto_const_nhds
      · refine tendsto_const_nhds.mul (Tendsto.mul
          (((S.tech j).f'_continuousOn.mono Icc_subset_Ici_self) y hy) ?_)
        exact ((S.isMarginalUtility.cont.continuousAt
          (Ioi_mem_nhds (hpos j hj))).comp_continuousWithinAt
          (f := fun z => (S.tech j).psi z - h j z) (hcw j))
  blowup y hy hz M0 := by
    obtain ⟨j0, hj0, hc0⟩ := hz
    have hcw : ContinuousWithinAt (fun z => (S.tech j0).psi z - h j0 z) (Icc 0 S.B) y :=
      (((S.tech j0).psi_continuousOn.mono Icc_subset_Ici_self) y hy).sub (hh.cont j0 y hy)
    set m := S.β * (1 - S.θ) * S.π i j0 * (S.tech j0).f' S.B
    have hm : 0 < m := mul_pos (mul_pos S.coef_pos hj0) ((S.tech j0).f'_pos S.B_pos.le)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
      (S.isMarginalUtility.inada.eventually_gt_atTop (|M0| / m))
    filter_upwards [hcw.eventually_lt_const (lt_of_le_of_lt hc0 hε), self_mem_nhdsWithin]
      with z hz1 hzK
    by_cases hZ : S.Zs h i z
    · exact Or.inl hZ
    · right
      have hc : 0 < (S.tech j0).psi z - h j0 z := lt_of_not_ge fun hle => hZ ⟨j0, hj0, hle⟩
      have hU : |M0| / m < S.U' ((S.tech j0).psi z - h j0 z) := hball ⟨by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc]; exact hz1, hc⟩
      rw [div_lt_iff₀ hm] at hU
      have hf : (S.tech j0).f' S.B ≤ (S.tech j0).f' z :=
        (S.tech j0).f'_strictAntiOn.antitoneOn (mem_Ici.2 hzK.1) (mem_Ici.2 S.B_pos.le) hzK.2
      have hsingle := Finset.single_le_sum (f := fun j => S.π i j * ((S.tech j).f' z *
        S.U' ((S.tech j).psi z - h j z))) (fun j _ => IsInFs.term_nonneg i j hzK.1 hZ)
        (Finset.mem_univ j0)
      have hUp := S.isMarginalUtility.pos _ hc
      have h1 : m * S.U' ((S.tech j0).psi z - h j0 z) ≤ S.β * (1 - S.θ) *
          (S.π i j0 * ((S.tech j0).f' z * S.U' ((S.tech j0).psi z - h j0 z))) := by
        have : m = S.β * (1 - S.θ) * S.π i j0 * (S.tech j0).f' S.B := rfl
        rw [this]
        have := mul_le_mul_of_nonneg_left hf (mul_pos S.coef_pos hj0).le
        nlinarith
      have h2 := mul_le_mul_of_nonneg_left hsingle S.coef_pos.le
      simp only [Rs]
      linarith [le_abs_self M0]

/-- `0 ≤ (Th)_i(k) ≤ ψ_i(k)`. -/
theorem Ts_mem_Icc (h : ι → ℝ → ℝ) (i : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.Ts h i k ∈ Icc 0 ((S.tech i).psi k) :=
  ⟨eulerCross_nonneg, eulerCross_le ((S.tech i).psi_pos hk.1).le⟩

/-- **Corrected Exercise 18.8, Kuhn–Tucker form.** For `h ∈ F`, a state `i` and `k ∈ K`,
exactly one of: `y = (Th)_i(k)` is an interior solution of (9) with positive consumption today
and in every reachable state tomorrow; or there is zero consumption today (`y = ψ_i(k)`, the
right side of (9) being `+∞` on `[0, ψ_i(k))`); or there is zero saving (`y = 0`) and (9) holds
as the Kuhn–Tucker inequality `RHS(0) ≤ U′(ψ_i(k))`. No assumption beyond the per-shock ones is
needed. -/
theorem ex_18_8_spec_KT {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι) {k : ℝ}
    (hk : k ∈ Icc 0 S.B) :
    (S.Ts h i k < (S.tech i).psi k ∧ ¬ S.Zs h i (S.Ts h i k) ∧
      S.U' ((S.tech i).psi k - S.Ts h i k) = S.Rs h i (S.Ts h i k)) ∨
    (S.Ts h i k = (S.tech i).psi k ∧ ∀ y, 0 ≤ y → y < (S.tech i).psi k → S.Zs h i y) ∨
    (S.Ts h i k = 0 ∧ ¬ S.Zs h i 0 ∧ S.Rs h i 0 ≤ S.U' ((S.tech i).psi k)) :=
  eulerCross_spec_KT S.isMarginalUtility (hh.isEulerRHS i) ((S.tech i).psi_pos hk.1)
    (S.psi_le_B i hk)

variable (S)

/-- The **cross-state condition** that replaces Assumption 18.1d's `β(1 − θ) f′(0) > 1` in the
stochastic case: `U′(ψ_i(0)) < β(1 − θ) Σ_j π_ij f′_j(0) U′(ψ_j(0))` for every state `i`. -/
def CrossState : Prop :=
  ∀ i, S.U' ((S.tech i).psi 0) <
    S.β * (1 - S.θ) * ∑ j, S.π i j * ((S.tech j).f' 0 * S.U' ((S.tech j).psi 0))

variable {S}

/-- Under the cross-state condition the left side of (9) lies below the right side at `y = 0`. -/
theorem IsInFs.eulerBelow_zero (hCS : S.CrossState) {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι)
    {k : ℝ} (hk : k ∈ Icc 0 S.B) : EulerBelow S.U' (S.Zs h i) (S.Rs h i) ((S.tech i).psi k) 0 := by
  by_cases hz : S.Zs h i 0
  · exact Or.inl hz
  · right
    have h0B : (0 : ℝ) ∈ Icc 0 S.B := ⟨le_rfl, S.B_pos.le⟩
    have hterm : ∀ j, S.π i j * ((S.tech j).f' 0 * S.U' ((S.tech j).psi 0)) ≤
        S.π i j * ((S.tech j).f' 0 * S.U' ((S.tech j).psi 0 - h j 0)) := by
      intro j
      rcases (S.π_nonneg i j).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have hc : 0 < (S.tech j).psi 0 - h j 0 := lt_of_not_ge fun hle => hz ⟨j, hpos, hle⟩
        have hle : (S.tech j).psi 0 - h j 0 ≤ (S.tech j).psi 0 := by
          linarith [hh.nonneg j 0 h0B]
        have hU := S.isMarginalUtility.strictAnti.antitoneOn hc
          ((S.tech j).psi_pos le_rfl) hle
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU
          ((S.tech j).f'_pos le_rfl).le) hpos.le
    have h1 := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s := Finset.univ) fun j _ => hterm j) S.coef_pos.le
    have hψ := (S.tech i).psi_strictMonoOn.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk.1) hk.1
    have h2 : S.U' ((S.tech i).psi k) ≤ S.U' ((S.tech i).psi 0) :=
      S.isMarginalUtility.strictAnti.antitoneOn ((S.tech i).psi_pos le_rfl)
        ((S.tech i).psi_pos hk.1) hψ
    have h3 := hCS i
    simp only [Rs, sub_zero]
    linarith

/-- **Corrected Exercise 18.8, equation form.** Under the cross-state condition, for `h ∈ F`
either `(Th)_i(k)` solves (9) with positive consumptions (and is its unique such solution), or
(9) has no such solution and `(Th)_i(k) = ψ_i(k)`. -/
theorem ex_18_8_spec (hCS : S.CrossState) {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι) {k : ℝ}
    (hk : k ∈ Icc 0 S.B) :
    (S.Ts h i k < (S.tech i).psi k ∧ ¬ S.Zs h i (S.Ts h i k) ∧
      S.U' ((S.tech i).psi k - S.Ts h i k) = S.Rs h i (S.Ts h i k) ∧
      ∀ y, 0 ≤ y → y < (S.tech i).psi k → ¬ S.Zs h i y →
        S.U' ((S.tech i).psi k - y) = S.Rs h i y → y = S.Ts h i k) ∨
    (S.Ts h i k = (S.tech i).psi k ∧ ∀ y, 0 ≤ y → y < (S.tech i).psi k → S.Zs h i y) := by
  have hPB := S.psi_le_B i hk
  rcases eulerCross_spec S.isMarginalUtility (hh.isEulerRHS i) ((S.tech i).psi_pos hk.1) hPB
    (hh.eulerBelow_zero hCS i hk) with ⟨h1, h2, h3⟩ | h'
  · exact Or.inl ⟨h1, h2, h3, fun y hy0 hyP hz heq =>
      (eulerCross_unique S.isMarginalUtility (hh.isEulerRHS i) hPB hy0 hyP hz heq).symm⟩
  · exact Or.inr h'

/-- `|(Th)_i(a) − (Th)_i(b)| ≤ |ψ_i(a) − ψ_i(b)|`, with `(Th)_i` and `ψ_i − (Th)_i`
nondecreasing on `K`. -/
theorem IsInFs.Ts_mono {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι) {a b : ℝ}
    (ha : a ∈ Icc 0 S.B) (hb : b ∈ Icc 0 S.B) (hab : a ≤ b) :
    S.Ts h i a ≤ S.Ts h i b ∧ S.Ts h i b ≤ S.Ts h i a + ((S.tech i).psi b - (S.tech i).psi a) := by
  have hψ := (S.tech i).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab
  exact ⟨eulerCross_mono' S.isMarginalUtility (hh.isEulerRHS i) hψ (S.psi_le_B i hb),
    eulerCross_le_add_sub S.isMarginalUtility (hh.isEulerRHS i) hψ (S.psi_le_B i hb)⟩

/-- **Corrected Exercise 18.8: `T : F → F`** (with the Kuhn–Tucker reading of (9); no extra
assumption). -/
theorem ex_18_8 {h : ι → ℝ → ℝ} (hh : S.IsInFs h) : S.IsInFs (fun i k => S.Ts h i k) where
  cont i := by
    rw [Metric.continuousOn_iff]
    intro k0 hk0 ε hε
    obtain ⟨δ, hδ, hψ⟩ := Metric.continuousOn_iff.1 ((S.tech i).psi_continuousOn.mono
      (Icc_subset_Ici_self : Icc (0 : ℝ) S.B ⊆ Ici 0)) k0 hk0 ε hε
    refine ⟨δ, hδ, fun k hk hd => ?_⟩
    have h1 := hψ k hk hd
    rw [Real.dist_eq] at h1 ⊢
    refine lt_of_le_of_lt ?_ h1
    rcases le_total k k0 with hkk | hkk
    · obtain ⟨e1, e2⟩ := hh.Ts_mono i hk hk0 hkk
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm]
      have := (S.tech i).psi_strictMonoOn.monotoneOn (mem_Ici.2 hk.1) (mem_Ici.2 hk0.1) hkk
      rw [abs_of_nonneg (by linarith)]
      linarith
    · obtain ⟨e1, e2⟩ := hh.Ts_mono i hk0 hk hkk
      rw [abs_of_nonneg (by linarith)]
      have := (S.tech i).psi_strictMonoOn.monotoneOn (mem_Ici.2 hk0.1) (mem_Ici.2 hk.1) hkk
      rw [abs_of_nonneg (by linarith)]
      linarith
  nonneg i k hk := (Ts_mem_Icc h i hk).1
  le_psi i k hk := (Ts_mem_Icc h i hk).2
  mono i a ha b hb hab := (hh.Ts_mono i ha hb hab).1
  mono_sub i a ha b hb hab := by
    have := (hh.Ts_mono i ha hb hab).2
    simp only
    linarith

/-- **`T` is monotone on `F`** in the stochastic case (the analogue of Exercise 18.7). -/
theorem ex_18_8_mono {h h' : ι → ℝ → ℝ}
    (hle : ∀ j, ∀ k ∈ Icc 0 S.B, h j k ≤ h' j k) (i : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.Ts h i k ≤ S.Ts h' i k := by
  have hPB := S.psi_le_B i hk
  refine eulerCross_mono_rhs' (fun y hy0 hyP hz => ?_) (fun y hy0 hyP hz hz' => ?_)
  · obtain ⟨j, hj, hc⟩ := hz
    exact ⟨j, hj, by linarith [hle j y ⟨hy0, hyP.le.trans hPB⟩]⟩
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) S.coef_pos.le
    rcases (S.π_nonneg i j).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hc' : 0 < (S.tech j).psi y - h' j y := lt_of_not_ge fun hl => hz' ⟨j, hpos, hl⟩
      have hcc : (S.tech j).psi y - h' j y ≤ (S.tech j).psi y - h j y := by
        linarith [hle j y ⟨hy0, hyP.le.trans hPB⟩]
      have hU := S.isMarginalUtility.strictAnti.antitoneOn hc' (hc'.trans_le hcc) hcc
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU
        ((S.tech j).f'_pos hy0).le) hpos.le

variable (S)

/-- The least element of `F` in the stochastic case: `h ≡ 0`. -/
theorem isInFs_zero : S.IsInFs fun _ _ => 0 where
  cont _ := continuousOn_const
  nonneg _ _ _ := le_rfl
  le_psi j k hk := ((S.tech j).psi_pos hk.1).le
  mono _ := fun _ _ _ _ _ => le_rfl
  mono_sub j := fun a ha b hb hab => by
    simp only [sub_zero]
    exact (S.tech j).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab

/-- The greatest element of `F` in the stochastic case: `h = ψ` (it is in `F` since
`ψ − h ≡ 0`). -/
theorem isInFs_psi : S.IsInFs fun j k => (S.tech j).psi k where
  cont j := (S.tech j).psi_continuousOn.mono Icc_subset_Ici_self
  nonneg j k hk := ((S.tech j).psi_pos hk.1).le
  le_psi _ _ _ := le_rfl
  mono j := fun a ha b hb hab =>
    (S.tech j).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab
  mono_sub _ := fun _ _ _ _ _ => by simp

/-- Some state is reachable from `i`. -/
theorem exists_pi_pos (i : ι) : ∃ j, 0 < S.π i j := by
  by_contra hcon
  push Not at hcon
  have : ∑ j, S.π i j ≤ 0 := Finset.sum_nonpos fun j _ => hcon j
  linarith [S.π_sum i]

/-- **Correction (NOTE 18.3-J(ii)).** For `h = ψ ∈ F` every next-period consumption is zero,
so (9) has no solution with positive consumptions at any `(k, ξ_i)`. -/
theorem no_solution_at_psi (i : ι) (y : ℝ) : S.Zs (fun j k => (S.tech j).psi k) i y := by
  obtain ⟨j, hj⟩ := S.exists_pi_pos i
  exact ⟨j, hj, by simp⟩

/-- **Correction (NOTE 18.3-J(ii)).** With the extended-real convention, `Tψ = ψ`: the greatest
element of `F` is a fixed point of `T` with zero consumption forever, at which (9) holds nowhere
(`no_solution_at_psi`). So Schauder's Theorem (or Theorem 17.7 from the greatest element) yields
this degenerate fixed point, and existence of an equilibrium does not follow as claimed on
p. 560. -/
theorem Ts_psi (i : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.Ts (fun j k => (S.tech j).psi k) i k = (S.tech i).psi k := by
  refine le_antisymm (Ts_mem_Icc _ i hk).2 (le_eulerCross_of_forall fun y hy0 hy =>
    ⟨hy0, hy, Or.inl (S.no_solution_at_psi i y)⟩)

/-- **Correction (NOTE 18.3-J(i)), the mechanism.** If the cross-state condition fails strictly
in state `i` — `β(1 − θ) Σ_j π_ij f′_j(0) U′(ψ_j(0)) < U′(ψ_i(0))` — then for `h ≡ 0 ∈ F`
equation (9) at `(0, ξ_i)` has no solution `y ∈ [0, ψ_i(0))` with positive consumptions: the left
side exceeds the right side everywhere (the agent wants a corner with zero saving). -/
theorem no_solution_of_crossState_fails (i : ι)
    (hfail : S.β * (1 - S.θ) * ∑ j, S.π i j * ((S.tech j).f' 0 * S.U' ((S.tech j).psi 0)) <
      S.U' ((S.tech i).psi 0)) :
    ¬ ∃ y, 0 ≤ y ∧ y < (S.tech i).psi 0 ∧ ¬ S.Zs (fun _ _ => 0) i y ∧
      S.U' ((S.tech i).psi 0 - y) = S.Rs (fun _ _ => 0) i y := by
  rintro ⟨y, hy0, hyP, hz, heq⟩
  have hB : y ≤ S.B := hyP.le.trans (S.psi_le_B i ⟨le_rfl, S.B_pos.le⟩)
  have h1 : S.Rs (fun _ _ => 0) i y ≤ S.Rs (fun _ _ => 0) i 0 :=
    ((S.isInFs_zero).isEulerRHS i).anti y 0 le_rfl hy0 hB fun ⟨j, _, hc⟩ => by
      simp only [sub_zero] at hc
      linarith [(S.tech j).psi_pos (le_refl (0 : ℝ))]
  have h2 : S.U' ((S.tech i).psi 0) ≤ S.U' ((S.tech i).psi 0 - y) :=
    S.isMarginalUtility.strictAnti.antitoneOn (mem_Ioi.2 (by linarith))
      ((S.tech i).psi_pos le_rfl) (by linarith)
  simp only [Rs, sub_zero] at h1 heq
  linarith

end StochModel

/-! ### A two-shock model in which Exercise 18.8 fails -/

/-- The high-productivity technology `f(k) = 10 + (441/41) k/(1 + k)` (`θ = 1/2`, `β = 9/10`,
`k̄ = 20`, `ψ(k) − k = (20 − k)(k² + (51/41) k + 1/2)/(1 + k)²`). -/
noncomputable def modelHigh : GlobalModel :=
  ratModel (9 / 10) (1 / 2) (441 / 41) 10 20 (51 / 41) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The two-shock model of NOTE 18.3-J(i): state `0` has technology `modelHigh` (`ψ(0) = 10`),
state `1` has `modelE` (`ψ(0) = 1/50`), and the economy moves to state `0` for sure. Every
per-shock assumption holds, since both technologies are `GlobalModel`s. -/
noncomputable def stochJ : StochModel (Fin 2) where
  tech := ![modelHigh, modelE]
  β := 9 / 10
  θ := 1 / 2
  U := fun c => √c
  U' := fun c => 1 / (2 * √c)
  B := 20
  π := fun _ j => if j = 0 then 1 else 0
  tech_β j := by fin_cases j <;> rfl
  tech_θ j := by fin_cases j <;> rfl
  tech_U j := by fin_cases j <;> rfl
  tech_U' j := by fin_cases j <;> rfl
  kbar_le j := by
    fin_cases j
    · exact le_refl (20 : ℝ)
    · change (2 : ℝ) ≤ 20; norm_num
  B_eq := ⟨0, rfl⟩
  π_nonneg _ j := by split_ifs <;> norm_num
  π_sum _ := by simp

/-- In `stochJ` the cross-state condition fails in state `1`:
`β(1 − θ) f′_0(0) U′(ψ_0(0)) = (9/20)(441/41)/(2√10) < 1/(2√(1/50)) = U′(ψ_1(0))`. -/
theorem stochJ_crossState_fails :
    stochJ.β * (1 - stochJ.θ) * ∑ j, stochJ.π 1 j *
        ((stochJ.tech j).f' 0 * stochJ.U' ((stochJ.tech j).psi 0)) <
      stochJ.U' ((stochJ.tech 1).psi 0) := by
  have e0 : (stochJ.tech 0).psi 0 = 10 := by
    change (10 + 441 / 41 * 0 / (1 + 0)) - 1 / 2 * 0 * (441 / 41 / (1 + 0) ^ 2) = 10
    norm_num
  have e1 : (stochJ.tech 1).psi 0 = 1 / 50 := by
    change (1 / 50 + 891 / 250 * 0 / (1 + 0)) - 1 / 2 * 0 * (891 / 250 / (1 + 0) ^ 2) = 1 / 50
    norm_num
  have f0 : (stochJ.tech 0).f' 0 = 441 / 41 := by
    change 441 / 41 / (1 + 0) ^ 2 = (441 / 41 : ℝ)
    norm_num
  have hβ : stochJ.β = 9 / 10 := rfl
  have hθ : stochJ.θ = 1 / 2 := rfl
  have hU : ∀ c, stochJ.U' c = 1 / (2 * √c) := fun _ => rfl
  have hπ0 : stochJ.π 1 0 = 1 := by simp [stochJ]
  have hπ1 : stochJ.π 1 1 = 0 := by simp [stochJ]
  rw [Fin.sum_univ_two, e0, e1, f0, hβ, hθ, hπ0, hπ1, hU, hU]
  simp only [zero_mul, add_zero, one_mul]
  have h10 : (3 : ℝ) < √10 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h50 : √(1 / 50 : ℝ) < 1 / 7 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs : 0 < √(1 / 50 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hA : 1 / (2 * √10) < 1 / (2 * 3) :=
    one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  have hB : 1 / (2 * (1 / 7)) < 1 / (2 * √(1 / 50 : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  norm_num at hA hB ⊢
  nlinarith

/-- **Correction: Exercise 18.8 is false as posed** (NOTE 18.3-J(i)). The claim that (9) has a
solution with positive consumptions for every `h ∈ F` and every `(k, ξ_i)` fails in `stochJ`,
for `h ≡ 0` at `(0, ξ_1)`, although each technology satisfies Assumptions 18.1 and 18.2. -/
theorem ex_18_8_counterexample :
    ¬ ∀ (ι : Type) [Fintype ι] (S : StochModel ι) (h : ι → ℝ → ℝ), S.IsInFs h →
      ∀ (i : ι) (k : ℝ), k ∈ Icc 0 S.B → ∃ y, 0 ≤ y ∧ y < (S.tech i).psi k ∧
        ¬ S.Zs h i y ∧ S.U' ((S.tech i).psi k - y) = S.Rs h i y := by
  intro hall
  exact stochJ.no_solution_of_crossState_fails 1 stochJ_crossState_fails
    (hall (Fin 2) stochJ _ stochJ.isInFs_zero 1 0 ⟨le_rfl, stochJ.B_pos.le⟩)

end StokeyLucasPrescott.EquilibriaWithDistortions
