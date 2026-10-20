/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.GlobalStochastic

/-!
# Equilibria of the stochastic model: continuity, equicontinuity, least and greatest fixed
points (SLP p. 560)

The remainder of p. 560 asserts, for the stochastic operator (9): equicontinuity of `F`
"parallels exactly the proof of Proposition 6 [5]", continuity of `T` parallels Exercise 18.6,
existence follows from Schauder's Theorem, monotonicity parallels Exercise 18.7, and minimal and
maximal elements of `F` can be constructed as there.

* `IsInFs.abs_Ts_sub_le`, `Ts_equicontinuous`: `T(F)` is equicontinuous, with the modulus of
  continuity of `ψ_i` (Proposition 18.5).
* `Ts_tendsto` and `Ts_tendsto_uniform` (Exercise 18.6): if `hₐ → h` **pointwise** on `K` within
  `F`, then `T hₐ → T h` **uniformly** on `K`. In particular `T` is continuous for the sup norm.
* The least fixed point (Theorem 17.7 from the least element `0`): `lfp`, the pointwise limit of
  `Tⁿ0`. `tendsto_Tsit` gives convergence and `tendstoUniformly_Tsit` uniform convergence;
  `isInFs_lfp`, `Ts_lfp` and `lfp_le_of_super` say `lfp ∈ F` is a fixed point lying below every
  supersolution, in particular below every fixed point.
* `stoch_least_greatest`: the fixed points of `T` in `F` all lie between the least fixed point
  `lfp` and the **greatest fixed point `ψ`**, which is the degenerate fixed point with zero
  consumption forever (`Ts_psi`).
* `lfp_equilibrium_of_super` (existence of a non-degenerate equilibrium): if some `h̄ ∈ F` with
  positive consumption `ψ − h̄ > 0` on `K` is a supersolution (`T h̄ ≤ h̄`), and the cross-state
  condition holds, then `lfp` has positive consumption everywhere and solves (9) as an
  equation at every `(k, ξ_i)`; it is then the least equilibrium.
* `identical_tech_fixed`, `exists_nondegenerate_equilibrium_identical`: the hypothesis holds
  when all states share one technology (from the deterministic equilibrium of
  `GlobalModel.exists_equilibrium`), so `lfp_equilibrium_of_super` is not vacuous.

**Different technologies.** Existence of a non-degenerate equilibrium for heterogeneous
technologies is proved in `GlobalStochasticNondegenerate`, with no extra hypothesis: the
consumption of an auxiliary planner is a floor for `lfp` (`StochModel.lfp_lt_psi`,
`StochModel.exists_nondegenerate_equilibrium`). The deterministic proof anchors consumption at
`k*` through (4)–(6), and the stochastic `F` has no such anchor; `Ts_psi` shows the book's
Schauder argument gives only the degenerate fixed point `ψ`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology BoundedContinuousFunction

namespace StochModel

variable {ι : Type} [Fintype ι] {S : StochModel ι}

/-- Members of the stochastic `F` change by at most the change in `ψ_j`. -/
theorem IsInFs.abs_sub_le {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (j : ι) {a b : ℝ}
    (ha : a ∈ Icc 0 S.B) (hb : b ∈ Icc 0 S.B) :
    |h j a - h j b| ≤ |(S.tech j).psi a - (S.tech j).psi b| := by
  rcases le_total a b with hab | hab
  · have h1 := hh.mono j ha hb hab
    have h2 : (S.tech j).psi a - h j a ≤ (S.tech j).psi b - h j b := hh.mono_sub j ha hb hab
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := hh.mono j hb ha hab
    have h2 : (S.tech j).psi b - h j b ≤ (S.tech j).psi a - h j a := hh.mono_sub j hb ha hab
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- `|(Th)_i(a) − (Th)_i(b)| ≤ |ψ_i(a) − ψ_i(b)|` for `h ∈ F`. -/
theorem IsInFs.abs_Ts_sub_le {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι) {a b : ℝ}
    (ha : a ∈ Icc 0 S.B) (hb : b ∈ Icc 0 S.B) :
    |S.Ts h i a - S.Ts h i b| ≤ |(S.tech i).psi a - (S.tech i).psi b| :=
  (ex_18_8 hh).abs_sub_le i ha hb

variable (S) in
/-- **Equicontinuity of `T(F)`** in the stochastic case (the analogue of Proposition 18.5):
one `δ` for all `h ∈ F`, for each state. -/
theorem Ts_equicontinuous (i : ι) : ∀ ε > 0, ∃ δ > 0, ∀ h, S.IsInFs h →
    ∀ a ∈ Icc 0 S.B, ∀ b ∈ Icc 0 S.B, dist a b < δ → |S.Ts h i a - S.Ts h i b| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hψ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := S.B)).uniformContinuousOn_of_continuous
      ((S.tech i).psi_continuousOn.mono Icc_subset_Ici_self)) ε hε
  refine ⟨δ, hδ, fun h hh a ha b hb hab => ?_⟩
  have := hψ a ha b hb hab
  rw [Real.dist_eq] at this
  exact (hh.abs_Ts_sub_le i ha hb).trans_lt this

/-- Pointwise convergence of the right sides of (9) when `hₐ → h` pointwise on `K`. -/
theorem rhsConvergesAt_of_tendsto {α : Type*} {l : Filter α} {hs : α → ι → ℝ → ℝ}
    {h : ι → ℝ → ℝ}
    (hconv : ∀ j, ∀ y ∈ Icc 0 S.B, Tendsto (fun a => hs a j y) l (𝓝 (h j y))) (i : ι) {y : ℝ}
    (hyK : y ∈ Icc 0 S.B) :
    RHSConvergesAt l (fun a => S.Zs (hs a) i) (fun a => S.Rs (hs a) i) (S.Zs h i) (S.Rs h i)
      y := by
  have hcv : ∀ j, Tendsto (fun a => (S.tech j).psi y - hs a j y) l
      (𝓝 ((S.tech j).psi y - h j y)) := fun j => tendsto_const_nhds.sub (hconv j y hyK)
  constructor
  · rintro ⟨j0, hj0, hc0⟩ M0
    set m := S.β * (1 - S.θ) * S.π i j0 * (S.tech j0).f' y
    have hm : 0 < m := mul_pos (mul_pos S.coef_pos hj0) ((S.tech j0).f'_pos hyK.1)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
      (S.isMarginalUtility.inada.eventually_gt_atTop (|M0| / m))
    filter_upwards [(hcv j0).eventually_lt_const (lt_of_le_of_lt hc0 hε)] with a ha
    by_cases hZ : S.Zs (hs a) i y
    · exact Or.inl hZ
    · right
      have hc : 0 < (S.tech j0).psi y - hs a j0 y :=
        lt_of_not_ge fun hle => hZ ⟨j0, hj0, hle⟩
      have hU : |M0| / m < S.U' ((S.tech j0).psi y - hs a j0 y) := hball ⟨by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc]; exact ha, hc⟩
      rw [div_lt_iff₀ hm] at hU
      have hsingle := Finset.single_le_sum (f := fun j => S.π i j * ((S.tech j).f' y *
        S.U' ((S.tech j).psi y - hs a j y))) (fun j _ => IsInFs.term_nonneg i j hyK.1 hZ)
        (Finset.mem_univ j0)
      have h2 := mul_le_mul_of_nonneg_left hsingle S.coef_pos.le
      have h1 : m * S.U' ((S.tech j0).psi y - hs a j0 y) = S.β * (1 - S.θ) *
          (S.π i j0 * ((S.tech j0).f' y * S.U' ((S.tech j0).psi y - hs a j0 y))) := by
        simp only [m]; ring
      simp only [Rs]
      linarith [le_abs_self M0]
  · intro hz
    have hpos : ∀ j, 0 < S.π i j → 0 < (S.tech j).psi y - h j y :=
      fun j hj => lt_of_not_ge fun hle => hz ⟨j, hj, hle⟩
    refine ⟨?_, ?_⟩
    · have : ∀ᶠ a in l, ∀ j, 0 < S.π i j → 0 < (S.tech j).psi y - hs a j y := by
        refine eventually_all.2 fun j => ?_
        by_cases hj : 0 < S.π i j
        · exact ((hcv j).eventually_const_lt (hpos j hj)).mono fun a ha _ => ha
        · exact Eventually.of_forall fun a hj' => absurd hj' hj
      exact this.mono fun a ha ⟨j, hj, hle⟩ => absurd (ha j hj) (not_lt.2 hle)
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun j _ => ?_)
      rcases (S.π_nonneg i j).eq_or_lt with h0 | hj
      · rw [← h0]; simpa using tendsto_const_nhds
      · exact tendsto_const_nhds.mul (tendsto_const_nhds.mul
          ((S.isMarginalUtility.cont.continuousAt (Ioi_mem_nhds (hpos j hj))).tendsto.comp
            (hcv j)))

/-- **Exercise 18.6, stochastic case, pointwise step**: if `hₐ → h` pointwise on `K` within
`F`, then `(T hₐ)_i(k) → (T h)_i(k)`. -/
theorem Ts_tendsto {α : Type*} {l : Filter α} {hs : α → ι → ℝ → ℝ} {h : ι → ℝ → ℝ}
    (hhs : ∀ a, S.IsInFs (hs a)) (hh : S.IsInFs h)
    (hconv : ∀ j, ∀ y ∈ Icc 0 S.B, Tendsto (fun a => hs a j y) l (𝓝 (h j y))) (i : ι)
    {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    Tendsto (fun a => S.Ts (hs a) i k) l (𝓝 (S.Ts h i k)) := by
  have hP := (S.tech i).psi_pos hk.1
  have hPB := S.psi_le_B i hk
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := eventually_abs_eulerCross_sub_le (u := S.U') (Zs := fun a => S.Zs (hs a) i)
    (Rs := fun a => S.Rs (hs a) i) S.isMarginalUtility (hh.isEulerRHS i)
    (fun a => (hhs a).isEulerRHS i) hP hPB
    (fun y hy0 hyP => rhsConvergesAt_of_tendsto hconv i ⟨hy0, hyP.le.trans hPB⟩)
    (half_pos hε)
  filter_upwards [hev] with a ha
  rw [Real.dist_eq]
  exact ha.trans_lt (half_lt_self hε)

/-- **Exercise 18.6, stochastic case**: pointwise convergence `hₐ → h` on `K` within `F` gives
uniform convergence `T hₐ → T h` on `K`, in every state (equicontinuity of `T(F)` and a finite
net of `K`). In particular `T` is continuous on `F` for the sup norm. -/
theorem Ts_tendsto_uniform {α : Type*} {l : Filter α} {hs : α → ι → ℝ → ℝ} {h : ι → ℝ → ℝ}
    (hhs : ∀ a, S.IsInFs (hs a)) (hh : S.IsInFs h)
    (hconv : ∀ j, ∀ y ∈ Icc 0 S.B, Tendsto (fun a => hs a j y) l (𝓝 (h j y))) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ a in l, ∀ i, ∀ k ∈ Icc 0 S.B, |S.Ts (hs a) i k - S.Ts h i k| < ε := by
  refine eventually_all.2 fun i => ?_
  obtain ⟨δ, hδ, hψ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := S.B)).uniformContinuousOn_of_continuous
      ((S.tech i).psi_continuousOn.mono Icc_subset_Ici_self)) (ε / 4) (by linarith)
  obtain ⟨t, htK, htfin, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_Icc (a := (0 : ℝ)) (b := S.B)) hδ
  have hev : ∀ᶠ a in l, ∀ x ∈ t, |S.Ts (hs a) i x - S.Ts h i x| < ε / 4 := by
    refine (htfin.eventually_all).2 fun x hx => ?_
    have := Metric.tendsto_nhds.1 (Ts_tendsto hhs hh hconv i (htK hx)) (ε / 4) (by linarith)
    exact this.mono fun a ha => by rwa [Real.dist_eq] at ha
  filter_upwards [hev] with a ha k hk
  obtain ⟨x, hx, hkx⟩ := mem_iUnion₂.1 (hcover hk)
  have hxK := htK hx
  have hd := hψ k hk x hxK hkx
  rw [Real.dist_eq] at hd
  have e1 := (hhs a).abs_Ts_sub_le i hk hxK
  have e2 := hh.abs_Ts_sub_le i hxK hk
  have e3 := ha x hx
  rw [abs_sub_comm ((S.tech i).psi x)] at e2
  calc |S.Ts (hs a) i k - S.Ts h i k|
      ≤ |S.Ts (hs a) i k - S.Ts (hs a) i x| + |S.Ts (hs a) i x - S.Ts h i x| +
          |S.Ts h i x - S.Ts h i k| := by
        have := abs_sub_le (S.Ts (hs a) i k) (S.Ts (hs a) i x) (S.Ts h i k)
        have := abs_sub_le (S.Ts (hs a) i x) (S.Ts h i x) (S.Ts h i k)
        linarith
    _ < ε := by linarith

/-! ### The least fixed point -/

variable (S)

/-- The operator `T` of (9) on functions `ι → ℝ → ℝ`. -/
noncomputable def TsOp (h : ι → ℝ → ℝ) : ι → ℝ → ℝ := fun i k => S.Ts h i k

/-- The iterates `Tⁿ0` from the least element `0` of `F`. -/
noncomputable def Tsit (n : ℕ) : ι → ℝ → ℝ := (S.TsOp)^[n] (fun _ _ => 0)

/-- `Tⁿ⁺¹0 = T(Tⁿ0)`. -/
theorem Tsit_succ (n : ℕ) : S.Tsit (n + 1) = S.TsOp (S.Tsit n) :=
  Function.iterate_succ_apply' _ _ _

/-- Every iterate lies in `F`. -/
theorem isInFs_Tsit (n : ℕ) : S.IsInFs (S.Tsit n) := by
  induction n with
  | zero => exact S.isInFs_zero
  | succ n ih => rw [Tsit_succ]; exact ex_18_8 ih

/-- The iterates increase: `Tⁿ0 ≤ Tⁿ⁺¹0` on `K`. -/
theorem Tsit_le_succ (n : ℕ) : ∀ j, ∀ k ∈ Icc 0 S.B, S.Tsit n j k ≤ S.Tsit (n + 1) j k := by
  induction n with
  | zero =>
    intro j k hk
    rw [Tsit_succ]
    exact (Ts_mem_Icc _ j hk).1
  | succ n ih =>
    intro j k hk
    have e1 : S.Tsit (n + 1) j k = S.Ts (S.Tsit n) j k := by rw [Tsit_succ]; rfl
    have e2 : S.Tsit (n + 1 + 1) j k = S.Ts (S.Tsit (n + 1)) j k := by
      rw [Tsit_succ S (n + 1)]; rfl
    rw [e2, e1]
    exact ex_18_8_mono ih j hk

/-- A supersolution `h ∈ F` (`T h ≤ h` on `K`) lies above every iterate `Tⁿ0`. -/
theorem Tsit_le_of_super {h : ι → ℝ → ℝ} (hh : S.IsInFs h)
    (hsup : ∀ j, ∀ k ∈ Icc 0 S.B, S.Ts h j k ≤ h j k) (n : ℕ) :
    ∀ j, ∀ k ∈ Icc 0 S.B, S.Tsit n j k ≤ h j k := by
  induction n with
  | zero => exact fun j k hk => hh.nonneg j k hk
  | succ n ih =>
    intro j k hk
    rw [Tsit_succ]
    exact (ex_18_8_mono ih j hk).trans (hsup j k hk)

/-- The least fixed point: `lfp_j(k) = sup_n (Tⁿ0)_j(k)`. -/
noncomputable def lfp (j : ι) (k : ℝ) : ℝ := ⨆ n, S.Tsit n j k

/-- `Tⁿ0 → lfp` pointwise on `K` (monotone and bounded by `ψ`). -/
theorem tendsto_Tsit (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    Tendsto (fun n => S.Tsit n j k) atTop (𝓝 (S.lfp j k)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => S.Tsit_le_succ n j k hk)
    ⟨(S.tech j).psi k, forall_mem_range.2 fun n => (S.isInFs_Tsit n).le_psi j k hk⟩

/-- `lfp ∈ F`. -/
theorem isInFs_lfp : S.IsInFs S.lfp where
  cont j := by
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    obtain ⟨δ, hδ, hψ⟩ := Metric.continuousOn_iff.1 ((S.tech j).psi_continuousOn.mono
      (Icc_subset_Ici_self : Icc (0 : ℝ) S.B ⊆ Ici 0)) b hb ε hε
    refine ⟨δ, hδ, fun a ha hab => ?_⟩
    have h1 := hψ a ha hab
    rw [Real.dist_eq] at h1 ⊢
    refine lt_of_le_of_lt ?_ h1
    exact le_of_tendsto' (((S.tendsto_Tsit j ha).sub (S.tendsto_Tsit j hb)).abs)
      fun n => (S.isInFs_Tsit n).abs_sub_le j ha hb
  nonneg j k hk := ge_of_tendsto' (S.tendsto_Tsit j hk) fun n => (S.isInFs_Tsit n).nonneg j k hk
  le_psi j k hk := le_of_tendsto' (S.tendsto_Tsit j hk) fun n => (S.isInFs_Tsit n).le_psi j k hk
  mono j a ha b hb hab := le_of_tendsto_of_tendsto' (S.tendsto_Tsit j ha) (S.tendsto_Tsit j hb)
    fun n => (S.isInFs_Tsit n).mono j ha hb hab
  mono_sub j a ha b hb hab := le_of_tendsto_of_tendsto'
    (tendsto_const_nhds.sub (S.tendsto_Tsit j ha)) (tendsto_const_nhds.sub (S.tendsto_Tsit j hb))
    fun n => (S.isInFs_Tsit n).mono_sub j ha hb hab

/-- `lfp` is a fixed point of `T` on `K`. -/
theorem Ts_lfp (i : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) : S.Ts S.lfp i k = S.lfp i k := by
  have h1 : Tendsto (fun n => S.Ts (S.Tsit n) i k) atTop (𝓝 (S.Ts S.lfp i k)) :=
    Ts_tendsto S.isInFs_Tsit S.isInFs_lfp (fun j y hy => S.tendsto_Tsit j hy) i hk
  have h2 : Tendsto (fun n => S.Ts (S.Tsit n) i k) atTop (𝓝 (S.lfp i k)) := by
    have := (tendsto_add_atTop_iff_nat 1).2 (S.tendsto_Tsit i hk)
    refine this.congr fun n => ?_
    rw [Tsit_succ]; rfl
  exact tendsto_nhds_unique h1 h2

/-- `Tⁿ0 → lfp` **uniformly** on `K`. -/
theorem tendstoUniformly_Tsit {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i, ∀ k ∈ Icc 0 S.B, |S.Tsit (n + 1) i k - S.lfp i k| < ε := by
  have := Ts_tendsto_uniform S.isInFs_Tsit S.isInFs_lfp (fun j y hy => S.tendsto_Tsit j hy) hε
  filter_upwards [this] with n hn i k hk
  rw [Tsit_succ, ← S.Ts_lfp i hk]
  exact hn i k hk

/-- `lfp` lies below every supersolution in `F`, in particular below every fixed point. -/
theorem lfp_le_of_super {h : ι → ℝ → ℝ} (hh : S.IsInFs h)
    (hsup : ∀ j, ∀ k ∈ Icc 0 S.B, S.Ts h j k ≤ h j k) (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.lfp j k ≤ h j k :=
  le_of_tendsto' (S.tendsto_Tsit j hk) fun n => S.Tsit_le_of_super hh hsup n j k hk

/-- **Least and greatest fixed points** in the stochastic case (corrected p. 560): `lfp` (the
limit of `Tⁿ0`) and `ψ` are fixed points of `T` in `F`, and every fixed point `h ∈ F` satisfies
`lfp ≤ h ≤ ψ` on `K`. The greatest fixed point `ψ` is degenerate: consumption is zero and (9)
holds nowhere (`no_solution_at_psi`). -/
theorem stoch_least_greatest :
    S.IsInFs S.lfp ∧ (∀ i, ∀ k ∈ Icc 0 S.B, S.Ts S.lfp i k = S.lfp i k) ∧
      S.IsInFs (fun j k => (S.tech j).psi k) ∧
      (∀ i, ∀ k ∈ Icc 0 S.B, S.Ts (fun j k => (S.tech j).psi k) i k = (S.tech i).psi k) ∧
      ∀ h, S.IsInFs h → (∀ i, ∀ k ∈ Icc 0 S.B, S.Ts h i k = h i k) →
        ∀ j, ∀ k ∈ Icc 0 S.B, S.lfp j k ≤ h j k ∧ h j k ≤ (S.tech j).psi k :=
  ⟨S.isInFs_lfp, fun i _ hk => S.Ts_lfp i hk, S.isInFs_psi, fun i _ hk => S.Ts_psi i hk,
    fun _ hh hfix j k hk => ⟨S.lfp_le_of_super hh (fun j k hk => (hfix j k hk).le) j hk,
      hh.le_psi j k hk⟩⟩

/-- **A non-degenerate equilibrium** (corrected p. 560). Under the cross-state condition, if
some supersolution `h̄ ∈ F` (`T h̄ ≤ h̄`) has positive consumption `h̄_j < ψ_j` on `K`, then the
least fixed point `lfp` has positive consumption everywhere and solves (9) as an equation at every
`(k, ξ_i)`, with positive consumption today and in every reachable state tomorrow. -/
theorem lfp_equilibrium_of_super (hCS : S.CrossState) {hbar : ι → ℝ → ℝ} (hhb : S.IsInFs hbar)
    (hsup : ∀ j, ∀ k ∈ Icc 0 S.B, S.Ts hbar j k ≤ hbar j k)
    (hpos : ∀ j, ∀ k ∈ Icc 0 S.B, hbar j k < (S.tech j).psi k) (i : ι) {k : ℝ}
    (hk : k ∈ Icc 0 S.B) :
    S.lfp i k < (S.tech i).psi k ∧ ¬ S.Zs S.lfp i (S.lfp i k) ∧
      S.U' ((S.tech i).psi k - S.lfp i k) = S.Rs S.lfp i (S.lfp i k) := by
  have hlt : S.lfp i k < (S.tech i).psi k :=
    (S.lfp_le_of_super hhb hsup i hk).trans_lt (hpos i k hk)
  rcases ex_18_8_spec hCS S.isInFs_lfp i hk with ⟨-, h2, h3, -⟩ | ⟨h1, -⟩
  · rw [S.Ts_lfp i hk] at h2 h3
    exact ⟨hlt, h2, h3⟩
  · rw [S.Ts_lfp i hk] at h1
    exact absurd h1 hlt.ne

/-! ### The hypothesis of `lfp_equilibrium_of_super` holds with identical technologies -/

/-- With one technology `M` in every state, a deterministic equilibrium `g` (a fixed point of
`M.T` in `M.F`) is a fixed point of (9) with positive consumption. -/
theorem identical_tech_fixed (M : GlobalModel) (hM : ∀ j, S.tech j = M)
    {g : Icc 0 M.kbar →ᵇ ℝ} (hg : g ∈ M.F) (hfix : M.T g = g) :
    S.IsInFs (fun _ k => M.ext g k) ∧
      (∀ i, ∀ k ∈ Icc 0 S.B, S.Ts (fun _ k => M.ext g k) i k = M.ext g k) ∧
      ∀ j, ∀ k ∈ Icc 0 S.B, M.ext g k < (S.tech j).psi k := by
  have hB : M.kbar = S.B := by
    obtain ⟨j, hj⟩ := S.B_eq
    rw [← hj, hM j]
  have hgF : M.IsInF (M.ext g) := hg
  have hβ : M.β = S.β := by
    obtain ⟨j, -⟩ := S.B_eq
    rw [← hM j, S.tech_β j]
  have hθ : M.θ = S.θ := by
    obtain ⟨j, -⟩ := S.B_eq
    rw [← hM j, S.tech_θ j]
  have hU : M.U' = S.U' := by
    obtain ⟨j, -⟩ := S.B_eq
    rw [← hM j, S.tech_U' j]
  have heuler := (M.isFixedPt_iff_euler hg).1 hfix
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ => hB ▸ hgF.cont, fun j k hk => hgF.nonneg k (hB ▸ hk),
      fun j k hk => by rw [hM j]; exact hgF.le_psi k (hB ▸ hk),
      fun _ => hB ▸ hgF.mono, fun j => ?_⟩
    rw [hM j]
    exact hB ▸ hgF.mono_sub
  · intro i k hk
    have hZ : S.Zs (fun _ k => M.ext g k) i = M.Zd (M.ext g) := by
      funext y
      apply propext
      constructor
      · rintro ⟨j, -, hj⟩
        rw [hM j] at hj
        exact hj
      · intro hy
        obtain ⟨j, hj⟩ := S.exists_pi_pos i
        exact ⟨j, hj, by rw [hM j]; exact hy⟩
    have hR : S.Rs (fun _ k => M.ext g k) i = M.Rd (M.ext g) := by
      funext y
      simp only [Rs, GlobalModel.Rd, hM, ← Finset.sum_mul, S.π_sum, one_mul, hβ, hθ, hU]
      ring
    have hTv : S.Ts (fun _ k => M.ext g k) i k = M.Tval (M.ext g) k := by
      simp only [Ts, GlobalModel.Tval, hZ, hR, hM i, hU]
    rw [hTv, ← GlobalModel.ext_T hg (hB ▸ hk), hfix]
  · intro j k hk
    rw [hM j]
    have := (heuler k (hB ▸ hk)).1
    linarith

/-- With one technology in every state the cross-state condition holds (it is Assumption
18.1d). -/
theorem crossState_of_identical (M : GlobalModel) (hM : ∀ j, S.tech j = M) : S.CrossState := by
  intro i
  have hβ : M.β = S.β := by rw [← hM i, S.tech_β i]
  have hθ : M.θ = S.θ := by rw [← hM i, S.tech_θ i]
  have hU : M.U' = S.U' := by rw [← hM i, S.tech_U' i]
  simp only [hM, ← Finset.sum_mul, S.π_sum, one_mul]
  have h1 := M.one_lt_euler_zero
  have h2 := M.U'_pos (M.psi_pos le_rfl)
  rw [hβ, hθ, hU] at *
  nlinarith

/-- **Existence of a non-degenerate stochastic equilibrium** when every state has the same
technology: the least fixed point `lfp` solves (9) with positive consumptions everywhere. -/
theorem exists_nondegenerate_equilibrium_identical (M : GlobalModel) (hM : ∀ j, S.tech j = M)
    (i : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.lfp i k < (S.tech i).psi k ∧ ¬ S.Zs S.lfp i (S.lfp i k) ∧
      S.U' ((S.tech i).psi k - S.lfp i k) = S.Rs S.lfp i (S.lfp i k) := by
  obtain ⟨g, hg, hfix⟩ := M.exists_equilibrium
  obtain ⟨h1, h2, h3⟩ := S.identical_tech_fixed M hM hg hfix
  exact S.lfp_equilibrium_of_super (S.crossState_of_identical M hM) h1
    (fun j k hk => (h2 j k hk).le) h3 i hk

end StochModel

end StokeyLucasPrescott.EquilibriaWithDistortions
