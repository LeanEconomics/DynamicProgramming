/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.UpperBounded

/-!
# Production and inventory accumulation: the model

SLP §10.5, pp. 297–300. The stock of goods `x ∈ X = [0, ∞)` is split between consumption `x − y`
and end-of-period inventories `y`; an input `n ≥ 0` produces `n ω′` next period, where the
harvest shock `ω′ ∈ Ω = [ω₁, ω₂] ⊆ ℝ₊` is i.i.d. with law `μ`. Next period's stock is
`x′ = y + n ω′`. Surplus `U` is bounded, strictly increasing and strictly concave with
`U(0) = 0`; the holding cost `H` (the book's `φ`) and the input cost `c` are strictly increasing
and strictly convex with `H(0) = c(0) = 0`.

The current shock does not affect the problem, but to use the framework of Chapter 9 the state
is `(x, ω)` with `Q(ω, ·) = μ`. The input is bounded by `N̄`, chosen with `c(N̄) > Ū/(1 − β)`
(`exists_N_big`); larger inputs are never optimal, and `InventoryResults` shows that the
solution of the bounded problem solves the book's (2), where `n` ranges over `[0, ∞)`.

* **Exercise 10.5a** (`ex_10_5a`): measuring the input by its cost `m = c(n)`, output is
  `c⁻¹(m) ω`, and `c⁻¹` is strictly increasing and strictly concave.
* `inv_upperDP`: returns are bounded above by `Ū` and `y = n = 0` has return `U(x) ≥ 0`, so the
  results of `UpperBounded` apply. Returns are unbounded below (through `H(y)` with `y ≤ x`), so
  Assumption 9.7 fails.
* **Exercise 10.5f** (`ex_10_5f`): the sign argument. If `v′` is nonincreasing, `Y(x₂) ≤ Y(x₁)`,
  `N(x₂) > N(x₁)`, and (5) holds, then (6) fails.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

/-- The hypotheses of SLP §10.5 on surplus `U`, holding cost `H`, input cost `c`, the discount
factor, the harvest support `[ω₁, ω₂]`, the bound `Ū` on `U`, and the input bound `N̄`. -/
structure InvHyp (U H c : ℝ → ℝ) (β Ubar Nbar ω₁ ω₂ : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  ω_nonneg : 0 ≤ ω₁
  ω_le : ω₁ ≤ ω₂
  U_cont : ContinuousOn U (Ici 0)
  U_zero : U 0 = 0
  U_mono : StrictMonoOn U (Ici 0)
  U_conc : StrictConcaveOn ℝ (Ici 0) U
  U_le : ∀ q, 0 ≤ q → U q ≤ Ubar
  H_cont : ContinuousOn H (Ici 0)
  H_zero : H 0 = 0
  H_mono : StrictMonoOn H (Ici 0)
  H_conv : StrictConvexOn ℝ (Ici 0) H
  c_cont : ContinuousOn c (Ici 0)
  c_zero : c 0 = 0
  c_mono : StrictMonoOn c (Ici 0)
  c_conv : StrictConvexOn ℝ (Ici 0) c
  N_nonneg : 0 ≤ Nbar
  N_big : Ubar / (1 - β) < c Nbar

variable {U H c : ℝ → ℝ} {β Ubar Nbar ω₁ ω₂ : ℝ}

/-! ### Convex costs grow at least linearly -/

/-- A convex `c` with `c(0) = 0` satisfies `n c(1) ≤ c(n)` for `n ≥ 1`. -/
theorem mul_le_of_convexOn {c : ℝ → ℝ} (hc0 : c 0 = 0) (hconv : ConvexOn ℝ (Ici 0) c) {n : ℝ}
    (hn : 1 ≤ n) : n * c 1 ≤ c n := by
  have hn0 : 0 < n := by linarith
  have := hconv.2 (mem_Ici.2 hn0.le) (mem_Ici.2 le_rfl) (one_div_pos.2 hn0).le
    (sub_nonneg.2 ((div_le_one hn0).2 hn)) (add_sub_cancel _ _)
  simp only [smul_eq_mul, mul_zero, add_zero, hc0] at this
  rw [one_div_mul_cancel hn0.ne'] at this
  have := mul_le_mul_of_nonneg_left this hn0.le
  rwa [← mul_assoc, mul_one_div_cancel hn0.ne', one_mul] at this

/-- A strictly increasing convex `c` with `c(0) = 0` exceeds any bound: an input bound `N̄` with
`c(N̄) > R` exists. -/
theorem exists_N_big {c : ℝ → ℝ} (hc0 : c 0 = 0) (hmono : StrictMonoOn c (Ici 0))
    (hconv : ConvexOn ℝ (Ici 0) c) (R : ℝ) : ∃ N, 0 ≤ N ∧ R < c N := by
  have hc1 : 0 < c 1 := by
    have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 zero_le_one) zero_lt_one
    rwa [hc0] at this
  set N := max 1 (R / c 1 + 1)
  have hN : 1 ≤ N := le_max_left _ _
  refine ⟨N, by linarith, ?_⟩
  have h1 := mul_le_of_convexOn hc0 hconv hN
  have h2 : (R / c 1 + 1) * c 1 ≤ N * c 1 := mul_le_mul_of_nonneg_right (le_max_right _ _) hc1.le
  have h3 : (R / c 1 + 1) * c 1 = R + c 1 := by field_simp
  linarith

/-- **Exercise 10.5a.** Measure the input by its cost `m = c(n)`. Then `m` costs `m`, and
produces `c⁻¹(m) ω`, where `c⁻¹ : ℝ₊ → ℝ₊` is strictly increasing and strictly concave: linear
cost and strictly concave output, equivalent to strictly convex cost and linear output. -/
theorem ex_10_5a {c : ℝ → ℝ} (hcont : ContinuousOn c (Ici 0)) (hc0 : c 0 = 0)
    (hmono : StrictMonoOn c (Ici 0)) (hconv : StrictConvexOn ℝ (Ici 0) c) :
    ∃ g : ℝ → ℝ, (∀ m, 0 ≤ m → 0 ≤ g m ∧ c (g m) = m) ∧ (∀ n, 0 ≤ n → g (c n) = n) ∧
      StrictMonoOn g (Ici 0) ∧ StrictConcaveOn ℝ (Ici 0) g := by
  -- `c` maps `[0, ∞)` onto `[0, ∞)`
  have hsurj : ∀ m, 0 ≤ m → ∃ n ∈ Ici (0 : ℝ), c n = m := by
    intro m hm
    obtain ⟨N, hN0, hN⟩ := exists_N_big hc0 hmono hconv.convexOn m
    obtain ⟨n, hn, hcn⟩ := intermediate_value_Icc hN0 (hcont.mono Icc_subset_Ici_self)
      (show m ∈ Icc (c 0) (c N) by rw [hc0]; exact ⟨hm, hN.le⟩)
    exact ⟨n, hn.1, hcn⟩
  set g := Function.invFunOn c (Ici (0 : ℝ))
  have hg : ∀ m, 0 ≤ m → 0 ≤ g m ∧ c (g m) = m := fun m hm => by
    have := Function.invFunOn_pos (hsurj m hm)
    exact ⟨this.1, this.2⟩
  have hgc : ∀ n, 0 ≤ n → g (c n) = n := fun n hn =>
    hmono.injOn (Function.invFunOn_pos ⟨n, hn, rfl⟩).1 hn (Function.invFunOn_pos ⟨n, hn, rfl⟩).2
  have hc_nonneg : ∀ n, 0 ≤ n → 0 ≤ c n := fun n hn => by
    rw [← hc0]; exact hmono.monotoneOn (mem_Ici.2 le_rfl) hn hn
  have hgmono : StrictMonoOn g (Ici 0) := by
    intro m hm m' hm' hlt
    by_contra hge
    rw [not_lt] at hge
    have := hmono.monotoneOn (hg m' hm').1 (hg m hm).1 hge
    rw [(hg m hm).2, (hg m' hm').2] at this
    linarith
  refine ⟨g, hg, hgc, hgmono, convex_Ici 0, fun m hm m' hm' hne a b ha hb hab => ?_⟩
  have hmm : 0 ≤ a • m + b • m' := by
    simp only [smul_eq_mul]; nlinarith [mem_Ici.1 hm, mem_Ici.1 hm']
  have hgne : g m ≠ g m' := fun he => hne (by rw [← (hg m hm).2, he, (hg m' hm').2])
  have hlt := hconv.2 (hg m hm).1 (hg m' hm').1 hgne ha hb hab
  rw [(hg m hm).2, (hg m' hm').2, ← (hg _ hmm).2] at hlt
  have hmem : a • g m + b • g m' ∈ Ici (0 : ℝ) :=
    (convex_Ici 0) (hg m hm).1 (hg m' hm').1 ha.le hb.le hab
  exact (hmono.lt_iff_lt hmem (hg _ hmm).1).1 hlt

/-! ### The model -/

/-- `Γ(x) = [0, x] × [0, N̄]`: inventories `y ≤ x` and inputs `n ≤ N̄`. -/
def invΓ (Nbar : ℝ) (s : Ici (0 : ℝ) × Icc ω₁ ω₂) : Set (ℝ × ℝ) :=
  Icc 0 s.1.1 ×ˢ Icc 0 Nbar

/-- Next period's stock `x′ = y + n ω′` (truncated at `0`, which never binds on `Γ`). -/
def invφ (p : Ici (0 : ℝ) × (ℝ × ℝ) × Icc ω₁ ω₂) : Ici (0 : ℝ) :=
  ⟨max (p.2.1.1 + p.2.1.2 * p.2.2.1) 0, mem_Ici.2 (le_max_right _ _)⟩

/-- `F(x, y, n) = U(x − y) − H(y) − c(n)`. -/
noncomputable def invF (U H c : ℝ → ℝ) (p : Ici (0 : ℝ) × (ℝ × ℝ) × Icc ω₁ ω₂) : ℝ :=
  U (p.1.1 - p.2.1.1) - H p.2.1.1 - c p.2.1.2

/-- The problem (2) with `n ≤ N̄`, as a model of Chapter 9 with i.i.d. shocks. -/
noncomputable abbrev invModel (μ : Measure (Icc ω₁ ω₂)) (U H c : ℝ → ℝ) (β Nbar : ℝ) :
    Model (Ici (0 : ℝ)) (ℝ × ℝ) (Icc ω₁ ω₂) :=
  ⟨Kernel.const _ μ, invΓ Nbar, invφ, invF U H c, β⟩

theorem invφ_val (x : Ici (0 : ℝ)) (p : ℝ × ℝ) (ω : Icc ω₁ ω₂) (hω : 0 ≤ ω₁) (hy : 0 ≤ p.1)
    (hn : 0 ≤ p.2) : (invφ (x, p, ω)).1 = p.1 + p.2 * ω.1 := by
  change max (p.1 + p.2 * ω.1) 0 = _
  exact max_eq_left (add_nonneg hy (mul_nonneg hn (hω.trans ω.2.1)))

theorem continuous_invφ :
    Continuous (invφ : Ici (0 : ℝ) × (ℝ × ℝ) × Icc ω₁ ω₂ → Ici (0 : ℝ)) := by
  unfold invφ
  refine Continuous.subtype_mk ?_ _
  exact ((continuous_fst.comp continuous_snd.fst).add ((continuous_snd.comp continuous_snd.fst).mul
    (continuous_subtype_val.comp continuous_snd.snd))).max continuous_const

theorem inv_lhc {Nbar : ℝ} (hN : 0 ≤ Nbar) (s : Ici (0 : ℝ) × Icc ω₁ ω₂) :
    IsLHC (invΓ Nbar) s := by
  refine ⟨⟨(0, 0), ⟨le_rfl, s.1.2⟩, ⟨le_rfl, hN⟩⟩, fun p hp xs hxs => ?_⟩
  refine ⟨0, fun k => (min p.1 (xs k).1.1, p.2), fun k _ =>
    ⟨⟨le_min hp.1.1 (xs k).1.2, min_le_right _ _⟩, hp.2⟩, ?_⟩
  have h1 : Tendsto (fun k => (xs k).1.1) atTop (𝓝 s.1.1) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto s).comp hxs
  have := (tendsto_const_nhds (x := p.1)).min h1
  rw [min_eq_left hp.1.2] at this
  exact this.prodMk_nhds tendsto_const_nhds

theorem inv_uhc {Nbar : ℝ} (hN : 0 ≤ Nbar) (s : Ici (0 : ℝ) × Icc ω₁ ω₂) :
    IsUHC (invΓ Nbar) s := by
  refine ⟨⟨(0, 0), ⟨le_rfl, s.1.2⟩, ⟨le_rfl, hN⟩⟩, fun xs hxs ys hys => ?_⟩
  have h1 : Tendsto (fun k => (xs k).1.1) atTop (𝓝 s.1.1) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto s).comp hxs
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ h1).bddAbove
  have hmem : ∀ k, ys k ∈ Icc 0 B ×ˢ Icc 0 Nbar := fun k =>
    ⟨⟨(hys k).1.1, (hys k).1.2.trans (hB ⟨k, rfl⟩)⟩, (hys k).2⟩
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hmem
  have hle : a.1 ≤ s.1.1 := le_of_tendsto_of_tendsto ((continuous_fst.tendsto a).comp hlim)
    (h1.comp hφ.tendsto_atTop) (Eventually.of_forall fun k => (hys (φ k)).1.2)
  exact ⟨a, ⟨⟨ha.1.1, hle⟩, ha.2⟩, φ, hφ, hlim⟩

namespace InvHyp

variable (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
include h

theorem H_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ H y := by
  rw [← h.H_zero]; exact h.H_mono.monotoneOn (mem_Ici.2 le_rfl) hy hy

theorem c_nonneg {n : ℝ} (hn : 0 ≤ n) : 0 ≤ c n := by
  rw [← h.c_zero]; exact h.c_mono.monotoneOn (mem_Ici.2 le_rfl) hn hn

theorem U_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ U q := by
  rw [← h.U_zero]; exact h.U_mono.monotoneOn (mem_Ici.2 le_rfl) hq hq

theorem Ubar_nonneg : 0 ≤ Ubar := (h.U_nonneg le_rfl).trans (h.U_le 0 le_rfl)

theorem continuousOn_F (μ : Measure (Icc ω₁ ω₂)) :
    ContinuousOn (invF U H c) (graphA (invModel μ U H c β Nbar)) := by
  have hx : Continuous fun p : Ici (0 : ℝ) × (ℝ × ℝ) × Icc ω₁ ω₂ => p.1.1 :=
    continuous_subtype_val.comp continuous_fst
  have hy : Continuous fun p : Ici (0 : ℝ) × (ℝ × ℝ) × Icc ω₁ ω₂ => p.2.1.1 :=
    continuous_fst.comp continuous_snd.fst
  have hn : Continuous fun p : Ici (0 : ℝ) × (ℝ × ℝ) × Icc ω₁ ω₂ => p.2.1.2 :=
    continuous_snd.comp continuous_snd.fst
  refine ((h.U_cont.comp (hx.sub hy).continuousOn fun p hp => ?_).sub
    (h.H_cont.comp hy.continuousOn fun p hp => ?_)).sub
    (h.c_cont.comp hn.continuousOn fun p hp => ?_)
  · exact mem_Ici.2 (sub_nonneg.2 hp.1.2)
  · exact mem_Ici.2 hp.1.1
  · exact mem_Ici.2 hp.2.1

theorem F_le {p : Ici (0 : ℝ) × (ℝ × ℝ) × Icc ω₁ ω₂} (hy : p.2.1.1 ≤ p.1.1) (hy0 : 0 ≤ p.2.1.1) :
    invF U H c p ≤ Ubar - c p.2.1.2 := by
  have := h.U_le _ (sub_nonneg.2 hy)
  have := h.H_nonneg hy0
  unfold invF; linarith

/-- The hypotheses of `UpperBounded` hold, with `A = Ū`. -/
theorem upperDP (μ : Measure (Icc ω₁ ω₂)) [IsProbabilityMeasure μ] :
    UpperDP (invModel μ U H c β Nbar) Ubar := by
  have hφ : Continuous fun q : (Ici (0 : ℝ) × (ℝ × ℝ)) × Icc ω₁ ω₂ =>
      invφ (q.1.1, q.1.2, q.2) :=
    continuous_invφ.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  refine ⟨fun s => (inv_lhc h.N_nonneg s).1, fun s => isCompact_Icc.prod isCompact_Icc,
    inv_lhc h.N_nonneg, inv_uhc h.N_nonneg, h.continuousOn_F μ, h.Ubar_nonneg,
    fun p hp => (h.F_le hp.1.2 hp.1.1).trans (by linarith [h.c_nonneg hp.2.1]),
    fun s => ⟨(0, 0), ⟨⟨le_rfl, s.1.2⟩, ⟨le_rfl, h.N_nonneg⟩⟩, ?_⟩, h.β_pos, h.β_lt,
    hφ.continuousOn, contExp_of_preservesBC _ hφ.continuousOn
      (lemma_9_5_compact _ (isFeller_const _))⟩
  change 0 ≤ U (s.1.1 - 0) - H 0 - c 0
  rw [sub_zero, h.H_zero, h.c_zero, sub_zero, sub_zero]
  exact h.U_nonneg s.1.2

end InvHyp

/-! ### Exercise 10.5f -/

/-- **Exercise 10.5f.** Let `v′` be nonincreasing, `Y₂ ≤ Y₁` and `N₁ < N₂`, and let
`γ(ω) = v′(Y₂ + N₂ω) − v′(Y₁ + N₁ω)`. Then `γ(ω)(ω − A) ≤ 0` with `A = (Y₁ − Y₂)/(N₂ − N₁)`,
so `E[γ(ω)ω] ≤ A E[γ(ω)]`: (5), `E[γ] < 0`, and (6), `E[γω] > 0`, cannot both hold. -/
theorem ex_10_5f {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {w : Ω → ℝ} {vp : ℝ → ℝ} (hvp : Antitone vp) {Y₁ Y₂ N₁ N₂ : ℝ} (hY : Y₂ ≤ Y₁)
    (hN : N₁ < N₂) (hi1 : Integrable (fun ω => vp (Y₁ + N₁ * w ω)) μ)
    (hi2 : Integrable (fun ω => vp (Y₂ + N₂ * w ω)) μ)
    (hi1w : Integrable (fun ω => w ω * vp (Y₁ + N₁ * w ω)) μ)
    (hi2w : Integrable (fun ω => w ω * vp (Y₂ + N₂ * w ω)) μ)
    (h5 : ∫ ω, vp (Y₂ + N₂ * w ω) ∂μ < ∫ ω, vp (Y₁ + N₁ * w ω) ∂μ) :
    ¬ ∫ ω, w ω * vp (Y₁ + N₁ * w ω) ∂μ < ∫ ω, w ω * vp (Y₂ + N₂ * w ω) ∂μ := by
  set A := (Y₁ - Y₂) / (N₂ - N₁)
  have hd : 0 < N₂ - N₁ := sub_pos.2 hN
  have hA : 0 ≤ A := div_nonneg (sub_nonneg.2 hY) hd.le
  set γ := fun ω => vp (Y₂ + N₂ * w ω) - vp (Y₁ + N₁ * w ω)
  have hsign : ∀ ω, γ ω * (w ω - A) ≤ 0 := by
    intro ω
    have hdiff : Y₂ + N₂ * w ω - (Y₁ + N₁ * w ω) = (N₂ - N₁) * (w ω - A) := by
      simp only [A]; field_simp; ring
    rcases le_total A (w ω) with hwA | hwA
    · have : Y₁ + N₁ * w ω ≤ Y₂ + N₂ * w ω := by
        have := mul_nonneg hd.le (sub_nonneg.2 hwA); linarith
      have := hvp this
      exact mul_nonpos_of_nonpos_of_nonneg (by simp only [γ]; linarith) (sub_nonneg.2 hwA)
    · have : Y₂ + N₂ * w ω ≤ Y₁ + N₁ * w ω := by
        have := mul_nonpos_of_nonneg_of_nonpos hd.le (sub_nonpos.2 hwA); linarith
      have := hvp this
      exact mul_nonpos_of_nonneg_of_nonpos (by simp only [γ]; linarith) (sub_nonpos.2 hwA)
  have hiγ : Integrable γ μ := hi2.sub hi1
  have hiγw : Integrable (fun ω => w ω * vp (Y₂ + N₂ * w ω) - w ω * vp (Y₁ + N₁ * w ω)) μ :=
    hi2w.sub hi1w
  have hint : ∫ ω, (w ω * vp (Y₂ + N₂ * w ω) - w ω * vp (Y₁ + N₁ * w ω)) ∂μ ≤
      ∫ ω, A * γ ω ∂μ := by
    refine integral_mono hiγw (hiγ.const_mul A) fun ω => ?_
    have := hsign ω
    simp only [γ] at this ⊢
    nlinarith
  rw [integral_sub hi2w hi1w, integral_const_mul, integral_sub hi2 hi1] at hint
  have : A * (∫ ω, vp (Y₂ + N₂ * w ω) ∂μ - ∫ ω, vp (Y₁ + N₁ * w ω) ∂μ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hA (by linarith)
  intro h6
  linarith

end StokeyLucasPrescott.StochasticApplications
