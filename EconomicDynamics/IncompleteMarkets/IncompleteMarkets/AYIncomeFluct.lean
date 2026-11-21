/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.AYHousehold
import IncompleteMarkets.SIStationary

/-!
# §17.1.1 with iid shocks: the cash-on-hand process, `Ea(r, w)` and `r < 1/β − 1`

Miao, §17.1.1, p. 561, and §17.1.3, p. 564. With iid labour shocks the agent's problem is the
income fluctuation problem of §8.3.2 (the copied `SIModel`, with gross return `R = 1 + r`,
borrowing limit `b = φ` and income `y = wl`), and the cash-on-hand process
`x_{t+1} = (1 + r)A(x_t) + wl_{t+1} − rφ` is a Markov process.

* `ay_bellmanCoh_of_SI`: "if `l_t` is iid we can remove `l_t` as a state variable": a solution
  of the §8.3.2 Bellman equation solves the two-state Bellman equation in cash on hand.
* `ay_IsStationaryCoh`: `λ*` is a stationary distribution of the cash-on-hand process on
  `[x_min, ∞)` (`∫ f dλ* = ∫∫ f((1 + r)A(x) + y − rφ) μ(dy) λ*(dx)` for bounded continuous `f`).
* `ay_stationary_exists`: if `β(1 + r) < 1` (with the hypotheses of Proposition 8.3.1), the
  invariant measure of Proposition 8.3.1 on `[x_min, x_max]` is such a distribution.
* `ay_EaIid`, `ay_EaIid_bounds`: the long-run average assets `Ea(r, w) = E_{λ*}[A(x)] − φ`
  (p. 561), with `−φ ≤ Ea ≤ x_max − φ`.
* `ay_beta_R_lt_one`, `ay_r_lt_rho`: if income is not almost surely constant, **every**
  stationary distribution of the cash-on-hand process has `β(1 + r) < 1`, i.e.
  `r < ρ = 1/β − 1`. This is the precise form of the book's "if `β(1 + r) ≥ 1`, `x_t` and `a_t`
  converge to infinity" (p. 561) used for "the equilibrium interest rate is less than `ρ`"
  (p. 564). Proof: integrating the Euler inequality `u′(c(x)) ≥ β(1 + r) E u′(c(x′))` against
  `λ*` gives `β(1 + r) ≤ 1`; if `β(1 + r) = 1`, `m = u′ ∘ c` is harmonic `λ*`-a.e., and then
  `∫∫ (m(x′) − m(x))² = ∫ m² − ∫ m² = 0`, so `m(x′) = m(x)`, hence `x′ = x` a.s., which forces
  income to be constant.

**Departures.** The book derives `r < ρ` from the claim that assets diverge when
`β(1 + r) ≥ 1` (whose almost-sure form is not formalised in the Chapter 8 project); the
integrated-Euler argument above is a different proof of the consequence used in §17.1.3.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Miao, p. 561: "if `l_t` is iid, then we can remove `l_t` as a state variable": a solution
`(V, â)` of the §8.3.2 problem with `R = 1 + r`, `b = φ`, income `y = wl` (`l ~ ν` iid,
`y_min = wl_min`) solves the Bellman equation in cash on hand with `Q(·, l) = ν`. -/
theorem ay_bellmanCoh_of_SI (M : SIModel) (S : M.Solution) {r w φ lmin lmax : ℝ}
    {ν : Measure ℝ} (hR : M.R = 1 + r) (hb : M.b = φ) (hw : 0 ≤ w) (hymin : M.ymin = w * lmin)
    (hlaw : M.law = ν.map (fun l => w * l)) :
    ay_BellmanCoh M.u M.β r w φ lmin lmax (Kernel.const ℝ ν) (fun p => S.V p.1)
      (fun p => S.sav p.1) := by
  have hr : M.r = r := by simp only [SIModel.r, hR]; ring
  have hI : ∀ s, 0 ≤ s → ∫ y, S.V (M.next s y) ∂M.law =
      ∫ l', S.V ((1 + r) * s + w * l' - r * φ) ∂ν := fun s hs => by
    have hm := (S.integrable_V hs).aestronglyMeasurable
    rw [hlaw] at hm ⊢
    rw [integral_map (measurable_const_mul w).aemeasurable hm]
    simp only [SIModel.next, hR, hr, hb]
  intro p hx hl
  have hxm : M.xmin ≤ p.1 := by
    have := mul_le_mul_of_nonneg_left hl.1 hw
    simp only [SIModel.xmin, hymin, hr, hb]
    linarith
  refine ⟨S.sav_mem p.1 hxm, ?_, fun s hs => ?_⟩
  · simp only [Kernel.const_apply]
    rw [← hI _ (S.sav_mem p.1 hxm).1]
    exact S.bellman p.1 hxm
  · simp only [Kernel.const_apply]
    rw [← hI _ hs.1]
    exact S.bellman_le p.1 hxm s hs

/-- Miao, p. 561: `λ*` is a **stationary distribution of the cash-on-hand process**
`x′ = (1 + r)A(x) + y′ − rφ` (iid income `y′ ~ μ`): it lives on `[x_min, ∞)` and
`∫ f dλ* = ∫ (∫ f((1 + r)A(x) + y − rφ) μ(dy)) λ*(dx)` for bounded continuous `f`. -/
def ay_IsStationaryCoh {M : SIModel} (S : M.Solution) (lam : Measure ℝ) : Prop :=
  lam (Set.Ici M.xmin)ᶜ = 0 ∧ ∀ f : ℝ → ℝ, Continuous f → ∀ C : ℝ, (∀ x, |f x| ≤ C) →
    ∫ x, f x ∂lam = ∫ x, (∫ y, f (M.next (S.sav x) y) ∂M.law) ∂lam

/-- Miao, p. 561: "if `β(1 + r) < 1`, `{x_t}` has a unique invariant measure `λ*`": under the
hypotheses of Proposition 8.3.1 its invariant measure on `[x_min, x_max]`, viewed on `ℝ`, is a
stationary distribution of the cash-on-hand process. -/
theorem ay_stationary_exists {M : SIModel} (S : M.Solution) (hβR : M.β * M.R < 1)
    {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) (hy : M.ymin < M.ymax) {α : ℝ} (hα : 0 < α)
    (hμ : ∀ a b, M.ymin ≤ a → a ≤ b → b ≤ M.ymax → α * (b - a) ≤ M.law.real (Set.Icc a b)) :
    ∃ lam : Measure ℝ, IsProbabilityMeasure lam ∧ lam (Set.Icc M.xmin S.xmax)ᶜ = 0 ∧
      ay_IsStationaryCoh S lam := by
  obtain ⟨lam, hprob, hinv, -, -⟩ := S.proposition_8_3_1 hβR hddu hγ0 hγ hy hα hμ
  obtain ⟨hgt, ⟨⟨-, hfix⟩, -⟩, -⟩ := S.ex_8_9 hβR hddu hγ0 hγ hy
  have hxf : M.xmin ≤ S.xmax := hgt.le
  have := S.isMarkovKernel_kernel S.xmax
  have emb : MeasurableEmbedding (Subtype.val : Set.Icc M.xmin S.xmax → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hnull : lam.map Subtype.val (Set.Icc M.xmin S.xmax)ᶜ = 0 := by
    rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc.compl]
    have : (Subtype.val : Set.Icc M.xmin S.xmax → ℝ) ⁻¹' (Set.Icc M.xmin S.xmax)ᶜ = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun x hx => hx x.2
    rw [this, measure_empty]
  refine ⟨lam.map Subtype.val,
    (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).2 hprob,
    hnull, measure_mono_null (Set.compl_subset_compl.2 Set.Icc_subset_Ici_self) hnull,
    fun f hf C hC => ?_⟩
  rw [emb.integral_map, emb.integral_map]
  have hfm : Measurable fun z : Set.Icc M.xmin S.xmax => f z :=
    (hf.comp continuous_subtype_val).measurable
  have h1 := SIWC.theorem_8_3_cor (S.kernel S.xmax) lam hfm (M := C) fun z => hC z
  rw [hinv] at h1
  rw [← h1]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only
  rw [S.markovOpR_kernel S.xmax hfm s]
  refine integral_congr_ae ?_
  filter_upwards [M.supp] with y hy
  have hmem := S.mapsTo_Icc hxf hfix s.2 hy
  simp only [SIModel.Solution.kmap, min_eq_right hmem.2, max_eq_right hmem.1]

/-- Miao, p. 561: the long-run average assets with iid shocks, `Ea(r, w) = E_{λ*}[A(x)] − φ`
(next period's assets are `a′ = A(x) − φ`). -/
noncomputable def ay_EaIid {M : SIModel} (S : M.Solution) (lam : Measure ℝ) : ℝ :=
  ∫ x, S.sav x ∂lam - M.b

/-- Miao, p. 561: for a stationary distribution on `[x_min, x_f]`, `Ea(r, w)` is finite with
`−φ ≤ Ea(r, w) ≤ x_f − φ`, and it is the mean of next period's assets `A(x) − φ`. -/
theorem ay_EaIid_bounds {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    [IsProbabilityMeasure lam] {xf : ℝ} (hsupp : lam (Set.Icc M.xmin xf)ᶜ = 0) :
    -M.b ≤ ay_EaIid S lam ∧ ay_EaIid S lam ≤ xf - M.b ∧
      ay_EaIid S lam = ∫ x, (S.sav x - M.b) ∂lam := by
  have hae : ∀ᵐ x ∂lam, x ∈ Set.Icc M.xmin xf := ae_iff.2 hsupp
  have hcont : Continuous fun x => S.sav (max x M.xmin) :=
    S.continuousOn_sav.comp_continuous (continuous_id.max continuous_const)
      fun x => Set.mem_Ici.2 (le_max_right _ _)
  have heq : (fun x => S.sav (max x M.xmin)) =ᵐ[lam] S.sav := by
    filter_upwards [hae] with x hx
    rw [max_eq_left hx.1]
  have hb : ∀ᵐ x ∂lam, 0 ≤ S.sav x ∧ S.sav x ≤ xf := by
    filter_upwards [hae] with x hx
    exact ⟨(S.sav_mem x hx.1).1, (S.sav_mem x hx.1).2.trans hx.2⟩
  have hint : Integrable S.sav lam := by
    refine Integrable.of_bound (hcont.aestronglyMeasurable.congr heq) xf ?_
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have h0 : 0 ≤ ∫ x, S.sav x ∂lam := integral_nonneg_of_ae (hb.mono fun x hx => hx.1)
  have h1 : ∫ x, S.sav x ∂lam ≤ xf := by
    have := integral_mono_ae hint (integrable_const xf) (hb.mono fun x hx => hx.2)
    simpa using this
  refine ⟨by unfold ay_EaIid; linarith, by unfold ay_EaIid; linarith, ?_⟩
  rw [integral_sub hint (integrable_const _)]
  simp [ay_EaIid]

/-- Miao, pp. 561 and 564: if income is not almost surely constant, every stationary
distribution `λ*` of the cash-on-hand process has `β(1 + r) < 1`. -/
theorem ay_beta_R_lt_one {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    [IsProbabilityMeasure lam] (hst : ay_IsStationaryCoh S lam)
    (hnd : ∀ c : ℝ, M.law {y | y ≠ c} ≠ 0) : M.β * M.R < 1 := by
  obtain ⟨hsupp, hstat⟩ := hst
  have hae : ∀ᵐ x ∂lam, x ∈ Set.Ici M.xmin := ae_iff.2 hsupp
  set m : ℝ → ℝ := fun x => M.du (S.cons (max x M.xmin)) with hmdef
  have hmc : Continuous m :=
    (M.du_cont.comp S.continuousOn_cons fun x hx => S.cons_pos hx).comp_continuous
      (continuous_id.max continuous_const) fun x => Set.mem_Ici.2 (le_max_right _ _)
  set m0 := M.du (S.cons M.xmin)
  have hmpos : ∀ x, 0 < m x := fun x => M.du_pos _ (S.cons_pos (le_max_right _ _))
  have hmle : ∀ x, m x ≤ m0 := fun x =>
    M.du_anti.antitoneOn (Set.mem_Ioi.2 (S.cons_pos le_rfl))
      (Set.mem_Ioi.2 (S.cons_pos (le_max_right x M.xmin)))
      (S.cons_mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (le_max_right x M.xmin))
        (le_max_right _ _))
  have hmabs : ∀ x, |m x| ≤ m0 := fun x => by rw [abs_of_pos (hmpos x)]; exact hmle x
  have hmeq : ∀ x, M.xmin ≤ x → m x = M.du (S.cons x) := fun x hx => by
    simp only [hmdef, max_eq_left hx]
  have hminj : ∀ x x', M.xmin ≤ x → M.xmin ≤ x' → m x = m x' → x = x' := by
    intro x x' hx hx' h
    rw [hmeq x hx, hmeq x' hx'] at h
    rcases lt_trichotomy x x' with hlt | heq | hgt
    · have hc := S.lemma_8_3_1.1 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hx') hlt
      have := M.du_anti (Set.mem_Ioi.2 (S.cons_pos hx)) (Set.mem_Ioi.2 (S.cons_pos hx')) hc
      linarith
    · exact heq
    · have hc := S.lemma_8_3_1.1 (Set.mem_Ici.2 hx') (Set.mem_Ici.2 hx) hgt
      have := M.du_anti (Set.mem_Ioi.2 (S.cons_pos hx')) (Set.mem_Ioi.2 (S.cons_pos hx)) hc
      linarith
  -- integrability of the conditional expectations of bounded continuous functions
  have hsc : Continuous fun x => S.sav (max x M.xmin) :=
    S.continuousOn_sav.comp_continuous (continuous_id.max continuous_const)
      fun x => Set.mem_Ici.2 (le_max_right _ _)
  have key : ∀ f : ℝ → ℝ, Continuous f → ∀ C, (∀ x, |f x| ≤ C) →
      (∀ s, Integrable (fun y => f (M.next s y)) M.law) ∧
      Integrable (fun x => ∫ y, f (M.next (S.sav x) y) ∂M.law) lam := by
    intro f hf C hC
    have hi : ∀ s, Integrable (fun y => f (M.next s y)) M.law := fun s =>
      Integrable.of_bound (hf.comp (M.continuous_next_y s)).aestronglyMeasurable C
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC _)
    refine ⟨hi, ?_⟩
    have hcont : Continuous fun x => ∫ y, f (M.next (S.sav (max x M.xmin)) y) ∂M.law := by
      refine continuous_of_dominated (bound := fun _ => C)
        (fun x => (hi _).aestronglyMeasurable)
        (fun x => ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC _)
        (integrable_const C) (ae_of_all _ fun y => ?_)
      exact hf.comp ((M.continuous_next y).comp hsc)
    have heq : (fun x => ∫ y, f (M.next (S.sav (max x M.xmin)) y) ∂M.law) =ᵐ[lam]
        fun x => ∫ y, f (M.next (S.sav x) y) ∂M.law := by
      filter_upwards [hae] with x hx
      rw [max_eq_left (Set.mem_Ici.1 hx)]
    refine Integrable.of_bound (hcont.aestronglyMeasurable.congr heq) C (ae_of_all _ fun x => ?_)
    have := norm_integral_le_of_norm_le_const (μ := M.law) (C := C)
      (f := fun y => f (M.next (S.sav x) y))
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC _)
    simpa using this
  obtain ⟨hmy, hGi⟩ := key m hmc m0 hmabs
  have hmi : Integrable m lam :=
    Integrable.of_bound hmc.aestronglyMeasurable m0
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hmabs x)
  set G := fun x => ∫ y, m (M.next (S.sav x) y) ∂M.law with hGdef
  have hst1 : ∫ x, m x ∂lam = ∫ x, G x ∂lam := hstat m hmc m0 hmabs
  -- the Euler inequality, λ*-a.e.
  have heul : ∀ᵐ x ∂lam, M.β * M.R * G x ≤ m x := by
    filter_upwards [hae] with x hx
    have hx' : M.xmin ≤ x := hx
    have h := (S.eq_8_7 hx').1
    have hG : G x = ∫ y, M.du (S.cons (M.next (S.sav x) y)) ∂M.law := by
      refine integral_congr_ae ?_
      filter_upwards [M.ae_next (S.sav_mem x hx').1] with y hy
      exact hmeq _ hy.1
    rw [hG, hmeq x hx']
    exact h
  have hβR : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
  have hIpos : 0 < ∫ x, m x ∂lam := si_integral_pos hmi (ae_of_all _ hmpos)
  have hle : M.β * M.R * ∫ x, m x ∂lam ≤ ∫ x, m x ∂lam := by
    calc M.β * M.R * ∫ x, m x ∂lam = ∫ x, M.β * M.R * G x ∂lam := by
          rw [hst1, integral_const_mul]
      _ ≤ ∫ x, m x ∂lam := integral_mono_ae (hGi.const_mul _) hmi heul
  have hle1 : M.β * M.R ≤ 1 := by
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_right h hIpos
    linarith
  rcases hle1.lt_or_eq with hlt | heq1
  · exact hlt
  exfalso
  -- β(1 + r) = 1: m is harmonic λ*-a.e.
  have hGm : ∀ᵐ x ∂lam, G x = m x := by
    have hnn : 0 ≤ᵐ[lam] fun x => m x - G x :=
      heul.mono fun x hx => by rw [heq1, one_mul] at hx; simp only [Pi.zero_apply]; linarith
    have hz : ∫ x, (m x - G x) ∂lam = 0 := by rw [integral_sub hmi hGi, hst1, sub_self]
    have := (integral_eq_zero_iff_of_nonneg_ae hnn (hmi.sub hGi)).1 hz
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  -- the squares
  have hm2c : Continuous fun x => m x ^ 2 := hmc.pow 2
  have hm2abs : ∀ x, |m x ^ 2| ≤ m0 ^ 2 := fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hmpos x).le (hmle x) 2
  obtain ⟨hm2y, hHi⟩ := key (fun x => m x ^ 2) hm2c (m0 ^ 2) hm2abs
  have hm2i : Integrable (fun x => m x ^ 2) lam :=
    Integrable.of_bound hm2c.aestronglyMeasurable (m0 ^ 2)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hm2abs x)
  set H := fun x => ∫ y, m (M.next (S.sav x) y) ^ 2 ∂M.law with hHdef
  have hst2 : ∫ x, m x ^ 2 ∂lam = ∫ x, H x ∂lam := hstat _ hm2c (m0 ^ 2) hm2abs
  set Var := fun x => ∫ y, (m (M.next (S.sav x) y) - m x) ^ 2 ∂M.law with hVdef
  have hsqid : ∀ x, (fun y => (m (M.next (S.sav x) y) - m x) ^ 2) = fun y =>
      (m (M.next (S.sav x) y) ^ 2 - 2 * m x * m (M.next (S.sav x) y)) + m x ^ 2 :=
    fun x => by funext y; ring
  have hVyi : ∀ x, Integrable (fun y => (m (M.next (S.sav x) y) - m x) ^ 2) M.law := by
    intro x
    have h1 : Integrable (fun y => m (M.next (S.sav x) y) ^ 2) M.law := hm2y _
    rw [hsqid x]
    exact (h1.sub ((hmy _).const_mul _)).add (integrable_const _)
  have hexp : ∀ x, Var x = H x - 2 * m x * G x + m x ^ 2 := by
    intro x
    have h1 : Integrable (fun y => m (M.next (S.sav x) y) ^ 2) M.law := hm2y _
    have h2 := (hmy (S.sav x)).const_mul (2 * m x)
    simp only [hVdef, hHdef, hGdef]
    rw [hsqid x, integral_add (f := fun y => m (M.next (S.sav x) y) ^ 2 -
        2 * m x * m (M.next (S.sav x) y)) (h1.sub h2) (integrable_const _),
      integral_sub h1 h2, integral_const_mul, integral_const]
    simp
  have hVae : Var =ᵐ[lam] fun x => H x - m x ^ 2 := by
    filter_upwards [hGm] with x hx
    rw [hexp x, hx]
    ring
  have hVi : Integrable Var lam := (hHi.sub hm2i).congr hVae.symm
  have hV0 : ∫ x, Var x ∂lam = 0 := by
    rw [integral_congr_ae hVae, integral_sub hHi hm2i, hst2, sub_self]
  have hVnn : 0 ≤ᵐ[lam] Var := ae_of_all _ fun x => integral_nonneg fun y => sq_nonneg _
  have hVz := (integral_eq_zero_iff_of_nonneg_ae hVnn hVi).1 hV0
  obtain ⟨x, hx, hVx⟩ := (hae.and hVz).exists
  have hx' : M.xmin ≤ x := hx
  simp only [Pi.zero_apply, hVdef] at hVx
  have hsq := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) (hVyi x)).1 hVx
  apply hnd (x - M.R * S.sav x + M.r * M.b)
  refine ae_iff.1 (?_ : ∀ᵐ y ∂M.law, y = x - M.R * S.sav x + M.r * M.b)
  filter_upwards [hsq, M.supp] with y hy hys
  simp only [Pi.zero_apply] at hy
  have h0 : m (M.next (S.sav x) y) = m x := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hy
    linarith
  have hnx := hminj _ _ (M.next_ge (S.sav_mem x hx').1 hys.1) hx' h0
  simp only [SIModel.next] at hnx
  linarith

/-- Miao, p. 564: in terms of the interest rate, every stationary distribution has
`r < ρ = 1/β − 1` (the complete-markets rate). -/
theorem ay_r_lt_rho {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    [IsProbabilityMeasure lam] (hst : ay_IsStationaryCoh S lam)
    (hnd : ∀ c : ℝ, M.law {y | y ≠ c} ≠ 0) : M.r < 1 / M.β - 1 := by
  have h := ay_beta_R_lt_one S hst hnd
  have hβ := M.β_pos
  have : M.R < 1 / M.β := by rw [lt_div_iff₀ hβ]; linarith
  simp only [SIModel.r]
  linarith

end Miao.IncompleteMarkets
