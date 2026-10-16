/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.SearchInvariant

/-!
# An equilibrium search economy: the mean work force `D(θ)` (SLP §13.8)

SLP §13.8, pp. 411–412, Exercises 13.8g and 13.8h, under (6) and the mixing condition.

* `searchV_theta_le`: for `θ ≤ θ′`, `v_θ ≤ v_θ′ ≤ v_θ + (θ′ − θ)`; hence `β∫v_θ dQ − θ` is
  nonincreasing in `θ` and `g_θ` is nonincreasing in `θ` (`searchG_theta_anti`).
* `searchKernel_kpow_le`: if `G′ ≤ G`, then `Tⁿ_{G′}φ ≤ Tⁿ_Gφ` for nondecreasing `φ`.
* **`ex_13_8h`** (p. 412): `D` is nonincreasing on `(0, ∞)`, via
  `D(θ) = limₙ (T_θⁿ x)(s₀)` (Theorem 12.12: `T_θ*ⁿδ_{s₀} ⇒ λ_θ`; `x` is bounded continuous on
  the compact state space; Theorem 8.3); `ex_13_8h_antitoneOn`: on `[0, ∞)`.
* `ex_13_8g_jointCont` (hypothesis (b) of Theorem 12.13): `(s, θ) ↦ P_θ(s, ·)` is jointly weakly
  continuous on `S × [0, ∞)`, from the joint continuity of `g` in `(x, z, θ)`
  (`continuous_searchG_theta`; `|β∫v_θ − β∫v_θ′| ≤ β|θ − θ′|`, `abs_searchEV_sub_le`).
* **`ex_13_8g`** (p. 411): `D` is continuous on `[0, ∞)` (Theorem 12.13; uniqueness at `θ = 0`
  is `searchP_unique_zero`).
* `ex_13_8g_existence` (NOTE p. 411): `D(θ) = N` has a solution `θ ∈ [0, θ̄]` iff `N ∈ [0, x̄]`
  (the restriction on `N` is not stated in the book).
* A concrete instance: `x̄ = 1`, `Z = [0, 1]`, `f(x, z) = (1 − x)(1 + z)`, `β = 1/2`, `Q` the
  identity (`searchExample_primitives`, `_feller`, `_monotone`; `θ̄ = 4`).

**Corrections** (NOTE p. 412).
* "`D` is strictly decreasing for `θ > 0`" contradicts Ex. 13.8f: `D = 0` on `[θ̄, ∞)`
  (`ex_13_8h_counterexample`, every instance; `ex_13_8h_counterexample_concrete`), and under (6)
  already on `[βθ̄, ∞)` (`ex_13_8h_zero`). The corrected claim — `D` strictly decreasing on
  `{θ > 0 : D(θ) > 0}` — is **not** proved here. Partial result: the cutoffs `g_A`, `g_C` fall
  strictly in `θ` wherever they are positive (`searchCutoffs_theta_strict`), but in Case B
  `g_θ′ = g_θ = x` can hold, so the argument of Ex. 13.8h alone does not give strictness.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

variable {zlo zhi xbar β : ℝ} {f : ℝ → ℝ → ℝ}
  (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) [IsMarkovKernel Q]

/-! ### Dependence of `v` and `g` on `θ` -/

/-- For `θ ≤ θ′`: `v_θ ≤ v_θ′ ≤ v_θ + (θ′ − θ)` (Corollary 1 to Theorem 3.2: `T_θ′` maps the
closed set `{w : v_θ ≤ w ≤ v_θ + (θ′ − θ)}` into itself). -/
theorem searchV_theta_le (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    {θ θ' : ℝ} (hθ : θ ≤ θ') (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    searchV xbar Q f β θ p ≤ searchV xbar Q f β θ' p ∧
      searchV xbar Q f β θ' p ≤ searchV xbar Q f β θ p + (θ' - θ) := by
  obtain ⟨T, hT, hC⟩ := ex_13_8a_contraction Q hP hF θ'
  set v := searchV xbar Q f β θ
  set d := θ' - θ
  have hd : 0 ≤ d := sub_nonneg.2 hθ
  set S' : Set (Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ) :=
    ⋂ p, ({w | v p ≤ w p} ∩ {w | w p ≤ v p + d})
  have hmem : ∀ w, w ∈ S' ↔ ∀ p, v p ≤ w p ∧ w p ≤ v p + d := fun w => by
    simp only [S', mem_iInter, mem_inter_iff]
    rfl
  have hclosed : IsClosed S' := isClosed_iInter fun p =>
    (isClosed_le continuous_const (continuous_eval_const p)).inter
      (isClosed_le (continuous_eval_const p) continuous_const)
  have hne : S'.Nonempty := ⟨v, (hmem v).2 fun p => ⟨le_rfl, by linarith⟩⟩
  have hmaps : MapsTo T S' S' := fun w hw => by
    have hw' := (hmem w).1 hw
    refine (hmem _).2 fun p => ?_
    have hiv := integrable_searchSection Q v p.1 p.2
    have hiw := integrable_searchSection Q w p.1 p.2
    have h1 : ∫ z', v (p.1, z') ∂Q p.2 ≤ ∫ z', w (p.1, z') ∂Q p.2 :=
      integral_mono hiv hiw fun z' => (hw' (p.1, z')).1
    have h2 : ∫ z', w (p.1, z') ∂Q p.2 ≤ ∫ z', v (p.1, z') ∂Q p.2 + d := by
      have := integral_mono (f := fun z' => w (p.1, z')) (g := fun z' => v (p.1, z') + d) hiw
        (hiv.add (integrable_const d)) fun z' => (hw' (p.1, z')).2
      rwa [integral_add hiv (integrable_const d), integral_const, probReal_univ, one_smul]
        at this
    rw [hT, searchRHS, searchV_eq Q hP hF θ p, searchRHS]
    set a := β * ∫ z', v (p.1, z') ∂Q p.2
    set b := β * ∫ z', w (p.1, z') ∂Q p.2
    have hab : a ≤ b := mul_le_mul_of_nonneg_left h1 hP.hβ0.le
    have hba : b ≤ a + d := by
      have := mul_le_mul_of_nonneg_left h2 hP.hβ0.le
      nlinarith [hP.hβ1]
    refine ⟨max_le_max hθ (add_le_add le_rfl (min_le_min hθ hab)), max_le ?_ ?_⟩
    · have := le_max_left θ (f p.1 p.2 + min θ a)
      simp only [d] at this ⊢
      linarith
    · have hmin : min θ' b ≤ min θ a + d := by
        rcases le_total θ a with h | h
        · rw [min_eq_left h]; exact (min_le_left _ _).trans (by simp only [d]; linarith)
        · rw [min_eq_right h]; exact (min_le_right _ _).trans hba
      have := le_max_right θ (f p.1 p.2 + min θ a)
      linarith
  have hfix : T (searchV xbar Q f β θ') = searchV xbar Q f β θ' :=
    ext fun p => by rw [hT, ← searchV_eq Q hP hF θ']
  exact (hmem _).1 (corollary_1 hC hfix hne hclosed hmaps hmaps).1 p

/-- `|v_θ − v_θ′| ≤ |θ − θ′|`. -/
theorem abs_searchV_sub_le (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (θ θ' : ℝ) (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    |searchV xbar Q f β θ p - searchV xbar Q f β θ' p| ≤ |θ - θ'| := by
  rcases le_total θ θ' with h | h
  · have := searchV_theta_le Q hP hF h p
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have := searchV_theta_le Q hP hF h p
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- `|β ∫ v_θ dQ − β ∫ v_θ′ dQ| ≤ β |θ − θ′|`. -/
theorem abs_searchEV_sub_le (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (θ θ' : ℝ) (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    |searchEV xbar Q f β θ p - searchEV xbar Q f β θ' p| ≤ β * |θ - θ'| := by
  simp only [searchEV]
  rw [← mul_sub, abs_mul, abs_of_pos hP.hβ0, ← integral_sub
    (integrable_searchSection Q _ p.1 p.2) (integrable_searchSection Q _ p.1 p.2)]
  refine mul_le_mul_of_nonneg_left ?_ hP.hβ0.le
  have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := |θ - θ'|)
    (f := fun z' => searchV xbar Q f β θ (p.1, z') - searchV xbar Q f β θ' (p.1, z'))
    (Eventually.of_forall fun z' => by
      rw [Real.norm_eq_abs]; exact abs_searchV_sub_le Q hP hF θ θ' (p.1, z'))
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

/-- For `θ ≤ θ′`, `β ∫ v_θ′ dQ − θ′ ≤ β ∫ v_θ dQ − θ`. -/
theorem searchEV_sub_theta_anti (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    {θ θ' : ℝ} (hθ : θ ≤ θ') (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    searchEV xbar Q f β θ' p - θ' ≤ searchEV xbar Q f β θ p - θ := by
  have h := abs_searchEV_sub_le Q hP hF θ' θ p
  rw [abs_of_nonneg (sub_nonneg.2 hθ)] at h
  have := (abs_le.1 h).2
  nlinarith [hP.hβ1]

variable [Nonempty (Icc (0 : ℝ) xbar)]

/-- **Ex. 13.8h** (first step): the cutoffs, and so `g_θ`, are nonincreasing in `θ`. -/
theorem searchG_theta_anti (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) {θ θ' : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ θ')
    (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    searchG xbar Q f β θ' p ≤ searchG xbar Q f β θ p := by
  have hθ0' := hθ0.trans hθ
  have H := searchEV_hyps Q hP hF hM hθ0
  have H' := searchEV_hyps Q hP hF hM hθ0'
  have K := searchPhi_hyps Q hP hF hM hθ0
  have K' := searchPhi_hyps Q hP hF hM hθ0'
  have hC : searchGC xbar Q f β θ' p.2 ≤ searchGC xbar Q f β θ p.2 :=
    searchCutoff_le_searchCutoff H'.2.2.1 H.2.1 H.2.2.1
      (exists_isSearchCutoff_Icc H'.1 H'.2.1 H'.2.2.2.1 p.2)
      (exists_isSearchCutoff_Icc H.1 H.2.1 H.2.2.2.1 p.2)
      fun x => searchEV_sub_theta_anti Q hP hF hθ (x, p.2)
  have hA : searchGA xbar Q f β θ' p.2 ≤ searchGA xbar Q f β θ p.2 :=
    searchCutoff_le_searchCutoff K'.2.2.1 K.2.1 K.2.2.1
      (exists_isSearchCutoff_Icc K'.1 K'.2.1 K'.2.2.2.1 p.2)
      (exists_isSearchCutoff_Icc K.1 K.2.1 K.2.2.2.1 p.2)
      fun x => by
        have := searchEV_sub_theta_anti Q hP hF hθ (x, p.2)
        simp only [searchPhi]
        linarith
  exact min_le_min (max_le_max le_rfl hC) hA

/-! ### Exercise 13.8h: `D` is nonincreasing -/

omit [Nonempty (Icc (0 : ℝ) xbar)] in
/-- One step: if `G′ ≤ G`, then `P_{G′}(s, ·)` is dominated by `P_G(s, ·)`. -/
theorem searchKernel_integral_le {G G' : Icc ((0 : ℝ), zlo) (xbar, zhi) → Icc (0 : ℝ) xbar}
    (hG : Measurable G) (hG' : Measurable G') (hle : ∀ s, G' s ≤ G s)
    {φ : Icc ((0 : ℝ), zlo) (xbar, zhi) → ℝ} (hφ : Measurable φ) {M : ℝ} (hb : ∀ s, |φ s| ≤ M)
    (hmono : Monotone φ) (s : Icc ((0 : ℝ), zlo) (xbar, zhi)) :
    ∫ s', φ s' ∂searchKernel Q G' hG' s ≤ ∫ s', φ s' ∂searchKernel Q G hG s := by
  rw [integral_searchKernel Q hG' hφ, integral_searchKernel Q hG hφ]
  exact integral_mono
    (integrable_of_bounded (hφ.comp (measurable_searchSlice (G := G') s)) fun _ => hb _)
    (integrable_of_bounded (hφ.comp (measurable_searchSlice (G := G) s)) fun _ => hb _)
    fun z' => hmono (searchToR_mono ⟨hle s, le_rfl⟩)

omit [Nonempty (Icc (0 : ℝ) xbar)] in
/-- `n` steps: if `G′ ≤ G` and `P_G` is monotone, then `Tⁿ_{G′}φ ≤ Tⁿ_Gφ` for bounded measurable
nondecreasing `φ`. -/
theorem searchKernel_kpow_le (hM : IsMonotoneTF Q)
    {G G' : Icc ((0 : ℝ), zlo) (xbar, zhi) → Icc (0 : ℝ) xbar} (hG : Measurable G)
    (hG' : Measurable G') (hGm : Monotone G) (hle : ∀ s, G' s ≤ G s) (n : ℕ)
    {φ : Icc ((0 : ℝ), zlo) (xbar, zhi) → ℝ} (hφ : Measurable φ) {M : ℝ} (hb : ∀ s, |φ s| ≤ M)
    (hmono : Monotone φ) (s : Icc ((0 : ℝ), zlo) (xbar, zhi)) :
    ∫ s', φ s' ∂kpow (searchKernel Q G' hG') n s ≤ ∫ s', φ s' ∂kpow (searchKernel Q G hG) n s := by
  have := isMarkovKernel_searchKernel Q hG
  have := isMarkovKernel_searchKernel Q hG'
  induction n generalizing s with
  | zero => exact le_of_eq rfl
  | succ n ih =>
    have := ex_8_4a (searchKernel Q G hG) n
    have := ex_8_4a (searchKernel Q G' hG') n
    simp only [kpow]
    rw [Kernel.integral_comp (integrable_of_bounded hφ hb),
      Kernel.integral_comp (integrable_of_bounded hφ hb)]
    have hH := theorem_8_1_cor (kpow (searchKernel Q G hG) n) hφ hb
    have hH' := theorem_8_1_cor (kpow (searchKernel Q G' hG') n) hφ hb
    calc ∫ s', markovOpR (kpow (searchKernel Q G' hG') n) φ s' ∂searchKernel Q G' hG' s
        ≤ ∫ s', markovOpR (kpow (searchKernel Q G hG) n) φ s' ∂searchKernel Q G' hG' s :=
          integral_mono (integrable_of_bounded hH'.1 hH'.2) (integrable_of_bounded hH.1 hH.2)
            fun s' => ih s'
      _ ≤ ∫ s', markovOpR (kpow (searchKernel Q G hG) n) φ s' ∂searchKernel Q G hG s :=
          searchKernel_integral_le Q hG hG' hle hH.1 hH.2
            (isMonotoneTF_kpow (isMonotoneTF_searchKernel Q hG hM hGm) n φ hφ ⟨M, hb⟩ hmono) s

/-- **Exercise 13.8h.** Under (6) and the mixing condition, `D` is nonincreasing on `(0, ∞)`:
`g_θ` is nonincreasing in `θ` (`searchG_theta_anti`), so `T_θ′ⁿ x ≤ T_θⁿ x` (`T_θ` is monotone),
and `D(θ) = limₙ (T_θⁿ x)(s₀)` because `T_θ*ⁿ δ_{s₀} ⇒ λ_θ` (Theorem 12.12) and `x` is bounded
and continuous on the compact state space. -/
theorem ex_13_8h (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (h6 : SearchAssumption6 hP.hz xbar Q f β) {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') :
    searchD xbar Q f β θ' ≤ searchD xbar Q f β θ := by
  have hθ' : 0 < θ' := hθ.trans_le hθθ'
  have hg := (ex_13_8c Q hP hF hM hθ.le).measurable
  have hg' := (ex_13_8c Q hP hF hM hθ'.le).measurable
  obtain ⟨lam, -, -, huniq, hconv⟩ := ex_13_8d Q hP hzlt hF hM hmix h6 hθ hg
  obtain ⟨lam', -, -, huniq', hconv'⟩ := ex_13_8d Q hP hzlt hF hM hmix h6 hθ' hg'
  rw [searchD_eq Q hP hF hM hθ.le hg huniq, searchD_eq Q hP hF hM hθ'.le hg' huniq']
  set φ : Icc ((0 : ℝ), zlo) (xbar, zhi) →ᵇ ℝ := mkOfCompact ⟨fun s => (s : ℝ × ℝ).1, by fun_prop⟩
  set s₀ : Icc ((0 : ℝ), zlo) (xbar, zhi) := ⟨((0 : ℝ), zlo), left_mem_Icc.2 ⟨hP.hx.le, hP.hz⟩⟩
  have h1 := hconv (Measure.dirac s₀) inferInstance φ
  have h2 := hconv' (Measure.dirac s₀) inferInstance φ
  simp only [iterate_dirac] at h1 h2
  have hφ : ∀ s, φ s = (s : ℝ × ℝ).1 := fun s => rfl
  simp only [hφ] at h1 h2
  refine le_of_tendsto_of_tendsto' h2 h1 fun n => ?_
  exact searchKernel_kpow_le Q hM _ _
    (fun s t hst => searchG_monotone Q hP hF hM hθ.le (searchOfR_mono hst))
    (fun s => searchG_theta_anti Q hP hF hM hθ.le hθθ' _) n
    (φ := fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (s : ℝ × ℝ).1)
    (measurable_fst.comp measurable_subtype_coe) (M := xbar)
    (fun s => by rw [abs_of_nonneg s.2.1.1]; exact s.2.2.1) (fun s t hst => hst.1) s₀

/-- **Exercise 13.8h** on `[0, ∞)`: `D` is nonincreasing (with `D(0) = x̄ ≥ D(θ)`). -/
theorem ex_13_8h_antitoneOn (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (h6 : SearchAssumption6 hP.hz xbar Q f β) : AntitoneOn (searchD xbar Q f β) (Ici 0) := by
  intro θ hθ θ' hθ' hθθ'
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ θ from hθ) with h0 | hpos
  · rw [← h0, ex_13_8f_zero Q hP hF hM]
    exact (searchD_mem Q hP hF hM hθ').2
  · exact ex_13_8h Q hP hzlt hF hM hmix h6 hpos hθθ'

/-- **Correction (NOTE p. 412).** `D` is *not* strictly decreasing on `(0, ∞)`, contradicting the
book's claim: by Ex. 13.8f `D(θ) = 0` for all `θ ≥ θ̄`, e.g. `D(θ̄) = D(2θ̄) = 0`. This holds in
every instance of the model; (6) is not needed. -/
theorem ex_13_8h_counterexample (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) : ¬ StrictAntiOn (searchD xbar Q f β) (Ioi 0) := by
  intro h
  have hpos := searchThetaBar_pos hP
  have := h (mem_Ioi.2 hpos) (mem_Ioi.2 (by linarith : (0 : ℝ) < 2 * searchThetaBar zhi β f))
    (by linarith : searchThetaBar zhi β f < 2 * searchThetaBar zhi β f)
  rw [ex_13_8f_large Q hP hF hM le_rfl, ex_13_8f_large Q hP hF hM (by linarith)] at this
  exact lt_irrefl _ this

/-- **Correction (NOTE p. 412).** Under (6) and mixing, `D = 0` already on `[βθ̄, ∞)`. -/
theorem ex_13_8h_zero (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (h6 : SearchAssumption6 hP.hz xbar Q f β) {θ : ℝ} (hθ : β * searchThetaBar zhi β f ≤ θ) :
    searchD xbar Q f β θ = 0 := by
  have hθ0 : 0 ≤ θ := (mul_pos hP.hβ0 (searchThetaBar_pos hP)).le.trans hθ
  obtain ⟨μ, hμ, hfix⟩ := exists_searchQ_invariant Q hP.hz hF
  exact (ex_13_8d_delta Q hP hzlt hF hM hmix h6 hθ
    (ex_13_8c Q hP hF hM hθ0).measurable μ hfix).2

/-! ### Exercise 13.8g: `D` is continuous -/

omit [IsMarkovKernel Q] [Nonempty (Icc (0 : ℝ) xbar)] in
/-- A function continuous in `a` for each `θ` and Lipschitz in `θ` uniformly in `a` is jointly
continuous. -/
theorem continuous_of_searchLipschitz {α Θ : Type*} [TopologicalSpace α] [PseudoMetricSpace Θ]
    {F : α → Θ → ℝ} (hF : ∀ θ, Continuous fun a => F a θ) {L : ℝ}
    (hL : ∀ a θ θ', |F a θ - F a θ'| ≤ L * dist θ θ') :
    Continuous fun q : α × Θ => F q.1 q.2 := by
  refine continuous_iff_continuousAt.2 fun q₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun q : α × Θ => L * dist q.2 q₀.2) (𝓝 q₀) (𝓝 0) := by
    have : Tendsto (fun q : α × Θ => L * dist q.2 q₀.2) (𝓝 q₀) (𝓝 (L * dist q₀.2 q₀.2)) :=
      ((continuous_snd.dist continuous_const).const_mul L).tendsto q₀
    simpa using this
  have h2 : Tendsto (fun q : α × Θ => |F q.1 q₀.2 - F q₀.1 q₀.2|) (𝓝 q₀) (𝓝 0) := by
    have : Tendsto (fun q : α × Θ => |F q.1 q₀.2 - F q₀.1 q₀.2|) (𝓝 q₀)
        (𝓝 |F q₀.1 q₀.2 - F q₀.1 q₀.2|) :=
      ((((hF q₀.2).comp continuous_fst).sub continuous_const).abs).tendsto q₀
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_) (by simpa using h1.add h2)
  rw [Real.norm_eq_abs]
  calc |F q.1 q.2 - F q₀.1 q₀.2| ≤ |F q.1 q.2 - F q.1 q₀.2| + |F q.1 q₀.2 - F q₀.1 q₀.2| :=
        abs_sub_le _ _ _
    _ ≤ L * dist q.2 q₀.2 + |F q.1 q₀.2 - F q₀.1 q₀.2| := add_le_add (hL _ _ _) le_rfl

omit [Nonempty (Icc (0 : ℝ) xbar)] in
/-- `(x, z, θ) ↦ β ∫ v_θ(x, z′) Q(z, dz′)` is jointly continuous. -/
theorem continuous_searchEV_theta (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q) :
    Continuous fun q : (Icc (0 : ℝ) xbar × Icc zlo zhi) × ℝ => searchEV xbar Q f β q.2 q.1 :=
  continuous_of_searchLipschitz (fun θ => continuous_searchEV Q hF) (L := β) fun p θ θ' => by
    rw [Real.dist_eq]; exact abs_searchEV_sub_le Q hP hF θ θ' p

/-- `(z, θ) ↦ g_C(z; θ)` and `(z, θ) ↦ g_A(z; θ)` are jointly continuous on `Z × [0, ∞)`. -/
theorem continuous_searchCutoffs_theta (hP : SearchPrimitives zlo zhi xbar β f)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) :
    Continuous (fun y : Icc zlo zhi × Ici (0 : ℝ) => searchGC xbar Q f β y.2 y.1) ∧
      Continuous (fun y : Icc zlo zhi × Ici (0 : ℝ) => searchGA xbar Q f β y.2 y.1) := by
  have hEV := continuous_searchEV_theta Q hP hF
  set HC : Icc (0 : ℝ) xbar × (Icc zlo zhi × Ici (0 : ℝ)) → ℝ :=
    fun q => searchEV xbar Q f β q.2.2 (q.1, q.2.1) - q.2.2
  set HA : Icc (0 : ℝ) xbar × (Icc zlo zhi × Ici (0 : ℝ)) → ℝ :=
    fun q => searchPhi xbar Q f β q.2.2 (q.1, q.2.1) - q.2.2
  have hc : ∀ x : Icc (0 : ℝ) xbar, Continuous fun y : Icc zlo zhi × Ici (0 : ℝ) =>
      searchEV xbar Q f β y.2 (x, y.1) :=
    fun x => hEV.comp ((continuous_const.prodMk continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  refine ⟨?_, ?_⟩
  · have := continuous_searchCutoff (h := HC)
      (fun y => (searchEV_hyps Q hP hF hM y.2.2).2.1 y.1)
      (fun y => (searchEV_hyps Q hP hF hM y.2.2).2.2.1 y.1)
      (fun y => by
        obtain ⟨c, hc⟩ := exists_isSearchCutoff_Icc
          (h := fun p => searchEV xbar Q f β y.2 p - y.2) (searchEV_hyps Q hP hF hM y.2.2).1
          (searchEV_hyps Q hP hF hM y.2.2).2.1 (searchEV_hyps Q hP hF hM y.2.2).2.2.2.1 y.1
        exact ⟨c, hc⟩)
      (fun x => (hc x).sub (continuous_subtype_val.comp continuous_snd))
    exact this
  · have := continuous_searchCutoff (h := HA)
      (fun y => (searchPhi_hyps Q hP hF hM y.2.2).2.1 y.1)
      (fun y => (searchPhi_hyps Q hP hF hM y.2.2).2.2.1 y.1)
      (fun y => by
        obtain ⟨c, hc⟩ := exists_isSearchCutoff_Icc
          (h := fun p => searchPhi xbar Q f β y.2 p - y.2) (searchPhi_hyps Q hP hF hM y.2.2).1
          (searchPhi_hyps Q hP hF hM y.2.2).2.1 (searchPhi_hyps Q hP hF hM y.2.2).2.2.2.1 y.1
        exact ⟨c, hc⟩)
      (fun x => by
        have : Continuous fun y : Icc zlo zhi × Ici (0 : ℝ) =>
            f x y.1 + searchEV xbar Q f β y.2 (x, y.1) - (y.2 : ℝ) :=
          ((hP.continuous_f.comp (continuous_const.prodMk continuous_fst)).add (hc x)).sub
            (continuous_subtype_val.comp continuous_snd)
        exact this)
    exact this

/-- `(s, θ) ↦ g_θ(s)` is jointly continuous on `S × [0, ∞)`. -/
theorem continuous_searchG_theta (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) :
    Continuous fun q : (Icc (0 : ℝ) xbar × Icc zlo zhi) × Ici (0 : ℝ) =>
      searchG xbar Q f β q.2 q.1 := by
  obtain ⟨hC, hA⟩ := continuous_searchCutoffs_theta Q hP hF hM
  have hy : Continuous fun q : (Icc (0 : ℝ) xbar × Icc zlo zhi) × Ici (0 : ℝ) => (q.1.2, q.2) :=
    (continuous_snd.comp continuous_fst).prodMk continuous_snd
  exact ((continuous_fst.comp continuous_fst).max (hC.comp hy)).min (hA.comp hy)

/-- **Exercise 13.8g** (hypothesis (b) of Theorem 12.13). `(s, θ) ↦ P_θ(s, ·)` is jointly weakly
continuous on `S × [0, ∞)`: `∫ φ dP_θ(s, ·) = ∫ φ(g_θ(s), z′) Q(z, dz′)`, continuous by Lemma 12.14
and the joint continuity of `g`. -/
theorem ex_13_8g_jointCont (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hg : ∀ θ : Ici (0 : ℝ), Measurable (searchG xbar Q f β θ))
    (s : ℕ → Icc ((0 : ℝ), zlo) (xbar, zhi)) (θ : ℕ → Ici (0 : ℝ))
    (s₀ : Icc ((0 : ℝ), zlo) (xbar, zhi)) (θ₀ : Ici (0 : ℝ)) (hs : Tendsto s atTop (𝓝 s₀))
    (hθ : Tendsto θ atTop (𝓝 θ₀)) :
    ConvWeak (fun n => searchP xbar Q f β (θ n) (hg (θ n)) (s n))
      (searchP xbar Q f β θ₀ (hg θ₀) s₀) := by
  intro φ
  set F : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ :=
    mkOfCompact ⟨φ ∘ searchToR, φ.continuous.comp continuous_searchToR⟩
  have hΨ := (lemma_12_14_cont Q hF F).1
  have hfun : ∀ (t : Ici (0 : ℝ)) (u : Icc ((0 : ℝ), zlo) (xbar, zhi)),
      ∫ s', φ s' ∂searchP xbar Q f β t (hg t) u =
        (fun p : Icc (0 : ℝ) xbar × Icc zlo zhi => ∫ z', F (p.1, z') ∂Q p.2)
          (searchG xbar Q f β t (searchOfR u), (searchOfR u).2) := fun t u =>
    integral_searchKernel Q _ φ.continuous.measurable u
  simp only [hfun]
  have hcont : Continuous fun q : Icc ((0 : ℝ), zlo) (xbar, zhi) × Ici (0 : ℝ) =>
      (fun p : Icc (0 : ℝ) xbar × Icc zlo zhi => ∫ z', F (p.1, z') ∂Q p.2)
        (searchG xbar Q f β q.2 (searchOfR q.1), (searchOfR q.1).2) :=
    hΨ.comp (((continuous_searchG_theta Q hP hF hM).comp
      ((continuous_searchOfR.comp continuous_fst).prodMk continuous_snd)).prodMk
      (continuous_snd.comp (continuous_searchOfR.comp continuous_fst)))
  exact (hcont.tendsto (s₀, θ₀)).comp (hs.prodMk_nhds hθ)

/-- At `θ = 0`, `P_0((x, z), ·) = δ_{x̄} × Q(z, ·)` has a unique invariant measure under the
mixing condition. -/
theorem searchP_unique_zero (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (hg : Measurable (searchG xbar Q f β 0)) :
    ∃ μ : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)), IsProbabilityMeasure μ ∧
      adjointOp (searchP xbar Q f β 0 hg) μ = μ ∧
      ∀ ν, IsProbabilityMeasure ν → adjointOp (searchP xbar Q f β 0 hg) ν = ν → ν = μ := by
  obtain ⟨μ, hμ, hfix, huniq, -⟩ := searchKernel_unique Q (hg.comp measurable_searchOfR) hzlt hF
    hM hmix ⟨hP.hx.le, hP.hz⟩
    (fun s t hst => searchG_monotone Q hP hF hM le_rfl (searchOfR_mono hst))
    ((ex_13_8c Q hP hF hM le_rfl).comp continuous_searchOfR) ⟨xbar, hP.hx.le, le_rfl⟩
    (z₁ := ⟨zlo, le_rfl, hP.hz⟩) (z₂ := ⟨zhi, hP.hz, le_rfl⟩) hzlt hzlt
    (fun s _ => (searchG xbar Q f β 0 (searchOfR s)).2.2)
    (fun s _ => (searchG_theta_zero Q hP hF hM (searchOfR s)).ge)
  exact ⟨μ, hμ, hfix, huniq⟩

/-- **NOTE (p. 411), `θ = 0`.** With the mixing condition, the unique invariant measure of `P_0` is
`λ_0 = δ_{x̄} × μ` (`μ` the invariant measure of `Q`). -/
theorem ex_13_8f_zero_measure (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (hg : Measurable (searchG xbar Q f β 0)) (μ : Measure (Icc zlo zhi))
    [IsProbabilityMeasure μ] (hμ : adjointOp Q μ = μ) :
    adjointOp (searchP xbar Q f β 0 hg) (searchDiracProd ⟨xbar, hP.hx.le, le_rfl⟩ μ) =
        searchDiracProd ⟨xbar, hP.hx.le, le_rfl⟩ μ ∧
      ∀ ν, IsProbabilityMeasure ν → adjointOp (searchP xbar Q f β 0 hg) ν = ν →
        ν = searchDiracProd ⟨xbar, hP.hx.le, le_rfl⟩ μ := by
  have hinv := searchDiracProd_invariant Q (hg.comp measurable_searchOfR)
    ⟨xbar, hP.hx.le, le_rfl⟩ (fun z => Subtype.ext (searchG_theta_zero Q hP hF hM _)) μ hμ
  have : IsProbabilityMeasure (searchDiracProd (⟨xbar, hP.hx.le, le_rfl⟩ : Icc (0 : ℝ) xbar) μ) :=
    by unfold searchDiracProd; infer_instance
  obtain ⟨lam, -, -, huniq⟩ := searchP_unique_zero Q hP hzlt hF hM hmix hg
  exact ⟨hinv, fun ν hν hνfix => by rw [huniq ν hν hνfix, huniq _ this hinv]⟩

/-- **Exercise 13.8g.** Under (6) and the mixing condition, `D` is continuous on `[0, ∞)`
(Theorem 12.13 on the parameter set `Θ = [0, ∞)`; hypothesis (c), uniqueness, is Ex. 13.8d for
`θ > 0` and `searchP_unique_zero` at `θ = 0`). -/
theorem ex_13_8g (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (h6 : SearchAssumption6 hP.hz xbar Q f β) :
    ContinuousOn (searchD xbar Q f β) (Ici 0) := by
  have hg : ∀ θ : Ici (0 : ℝ), Measurable (searchG xbar Q f β θ) := fun θ =>
    (ex_13_8c Q hP hF hM θ.2).measurable
  set P : Ici (0 : ℝ) → Kernel (Icc ((0 : ℝ), zlo) (xbar, zhi)) (Icc ((0 : ℝ), zlo) (xbar, zhi)) :=
    fun θ => searchP xbar Q f β θ (hg θ)
  have hPm : ∀ θ, IsMarkovKernel (P θ) := fun θ => (ex_13_8d_process Q hP hF hM θ.2 (hg θ)).1
  set μ : Ici (0 : ℝ) → Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)) := fun θ =>
    Classical.epsilon fun μ => IsProbabilityMeasure μ ∧ adjointOp (P θ) μ = μ
  have hspec : ∀ θ, IsProbabilityMeasure (μ θ) ∧ adjointOp (P θ) (μ θ) = μ θ := fun θ =>
    Classical.epsilon_spec (ex_13_8d_process Q hP hF hM θ.2 (hg θ)).2.2.2
  have hμp : ∀ θ, IsProbabilityMeasure (μ θ) := fun θ => (hspec θ).1
  have huniq : ∀ θ (ν : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi))), IsProbabilityMeasure ν →
      adjointOp (P θ) ν = ν → ν = μ θ := by
    rintro ⟨t, ht⟩ ν hν hνfix
    have ht' : (0 : ℝ) ≤ t := ht
    rcases eq_or_lt_of_le ht' with h0 | hpos
    · subst h0
      obtain ⟨lam, -, -, hl⟩ := searchP_unique_zero Q hP hzlt hF hM hmix (hg ⟨0, ht⟩)
      rw [hl ν hν hνfix, hl _ (hspec ⟨0, ht⟩).1 (hspec ⟨0, ht⟩).2]
    · obtain ⟨lam, -, -, hl, -⟩ := ex_13_8d Q hP hzlt hF hM hmix h6 hpos (hg ⟨t, ht⟩)
      rw [hl ν hν hνfix, hl _ (hspec ⟨t, ht⟩).1 (hspec ⟨t, ht⟩).2]
  have hD : ∀ θ : Ici (0 : ℝ), searchD xbar Q f β θ = ∫ s, (s : ℝ × ℝ).1 ∂μ θ := fun θ => by
    simp only [searchD, hg θ, ↓reduceDIte]
    rfl
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro θ θ₀ hθ
  have := theorem_12_13 P (fun s θ s₀ θ₀ hs hθ => ex_13_8g_jointCont Q hP hF hM hg s θ s₀ θ₀ hs hθ)
    μ (fun θ => (hspec θ).2) huniq hθ
    (mkOfCompact ⟨fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (s : ℝ × ℝ).1, by fun_prop⟩)
  simp only [domRestrict_apply, Function.comp_def, hD]
  exact this

/-- **NOTE (p. 411), existence of an equilibrium `θ`.** With `D` continuous, `D(0) = x̄` and
`D(θ̄) = 0`, the intermediate value theorem gives `θ ∈ [0, θ̄]` with `D(θ) = N` exactly when
`N ∈ [0, x̄]` (this restriction on the average population `N` is not stated in the book); for
`N ∉ [0, x̄]` there is no equilibrium `θ ≥ 0`. -/
theorem ex_13_8g_existence (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (h6 : SearchAssumption6 hP.hz xbar Q f β) (n : ℝ) :
    (n ∈ Icc 0 xbar → ∃ θ ∈ Icc 0 (searchThetaBar zhi β f), searchD xbar Q f β θ = n) ∧
      (n ∉ Icc 0 xbar → ∀ θ, 0 ≤ θ → searchD xbar Q f β θ ≠ n) := by
  refine ⟨fun hn => ?_, fun hn θ hθ h => hn (h ▸ searchD_mem Q hP hF hM hθ)⟩
  have hpos := (searchThetaBar_pos hP).le
  have hcont := (ex_13_8g Q hP hzlt hF hM hmix h6).mono
    fun x (hx : x ∈ Icc 0 (searchThetaBar zhi β f)) => show x ∈ Ici 0 from hx.1
  have := intermediate_value_Icc' hpos hcont
  rw [ex_13_8f_large Q hP hF hM le_rfl, ex_13_8f_zero Q hP hF hM] at this
  obtain ⟨θ, hθ, hD⟩ := this hn
  exact ⟨θ, hθ, hD⟩

/-! ### Towards the corrected strict monotonicity claim -/

omit [Nonempty (Icc (0 : ℝ) xbar)] in
/-- For `θ ≤ θ′`, `β ∫ v_θ′ dQ − θ′ ≤ β ∫ v_θ dQ − θ − (1 − β)(θ′ − θ)`. -/
theorem searchEV_sub_theta_strict (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    {θ θ' : ℝ} (hθ : θ ≤ θ') (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    searchEV xbar Q f β θ' p - θ' ≤ searchEV xbar Q f β θ p - θ - (1 - β) * (θ' - θ) := by
  have h := abs_searchEV_sub_le Q hP hF θ' θ p
  rw [abs_of_nonneg (sub_nonneg.2 hθ)] at h
  have := (abs_le.1 h).2
  linarith

/-- **Partial result towards the corrected Ex. 13.8h.** For `0 ≤ θ < θ′`, the cutoffs fall
strictly where they are positive: `g_A(z; θ′) < g_A(z; θ)` if `g_A(z; θ) > 0`, and likewise for
`g_C`. (So `g_θ′ < g_θ` in Cases A and C wherever `g_θ > 0`; in Case B, `g_θ′ = g_θ = x` can hold,
which is why strict monotonicity of `D` needs more than the argument of Ex. 13.8h.) -/
theorem searchCutoffs_theta_strict (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) {θ θ' : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < θ') (z : Icc zlo zhi) :
    (0 < (searchGA xbar Q f β θ z : ℝ) → searchGA xbar Q f β θ' z < searchGA xbar Q f β θ z) ∧
      (0 < (searchGC xbar Q f β θ z : ℝ) →
        searchGC xbar Q f β θ' z < searchGC xbar Q f β θ z) := by
  have hθ0' := hθ0.trans hθ.le
  have hd : 0 < (1 - β) * (θ' - θ) := mul_pos (sub_pos.2 hP.hβ1) (sub_pos.2 hθ)
  have H := searchEV_hyps Q hP hF hM hθ0
  have H' := searchEV_hyps Q hP hF hM hθ0'
  have K := searchPhi_hyps Q hP hF hM hθ0
  have K' := searchPhi_hyps Q hP hF hM hθ0'
  refine ⟨fun hpos => ?_, fun hpos => ?_⟩
  · have hle : searchGA xbar Q f β θ' z ≤ searchGA xbar Q f β θ z :=
      searchCutoff_le_searchCutoff K'.2.2.1 K.2.1 K.2.2.1
        (exists_isSearchCutoff_Icc K'.1 K'.2.1 K'.2.2.2.1 z)
        (exists_isSearchCutoff_Icc K.1 K.2.1 K.2.2.2.1 z)
        fun x => by
          have := searchEV_sub_theta_anti Q hP hF hθ.le (x, z)
          simp only [searchPhi]
          linarith
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 := (searchGA_spec Q hP hF hM hθ0 z).2 hpos
    have h2 := (searchGA_spec Q hP hF hM hθ0' z).2 (heq ▸ hpos)
    rw [heq] at h2
    have := searchEV_sub_theta_strict Q hP hF hθ.le (searchGA xbar Q f β θ z, z)
    simp only [searchPhi] at h1 h2
    linarith
  · have hle : searchGC xbar Q f β θ' z ≤ searchGC xbar Q f β θ z :=
      searchCutoff_le_searchCutoff H'.2.2.1 H.2.1 H.2.2.1
        (exists_isSearchCutoff_Icc H'.1 H'.2.1 H'.2.2.2.1 z)
        (exists_isSearchCutoff_Icc H.1 H.2.1 H.2.2.2.1 z)
        fun x => searchEV_sub_theta_anti Q hP hF hθ.le (x, z)
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 := (searchGC_spec Q hP hF hM hθ0 z).2 hpos
    have h2 := (searchGC_spec Q hP hF hM hθ0' z).2 (heq ▸ hpos)
    rw [heq] at h2
    have := searchEV_sub_theta_strict Q hP hF hθ.le (searchGC xbar Q f β θ z, z)
    linarith

/-! ### A concrete instance -/

/-- A concrete technology: `f(x, z) = (1 − x)(1 + z)` on `X = Z = [0, 1]`. -/
def searchExampleF (x z : ℝ) : ℝ :=
  (1 - x) * (1 + z)

/-- The concrete instance (`x̄ = 1`, `Z = [0, 1]`, `β = 1/2`) satisfies the primitives. -/
theorem searchExample_primitives : SearchPrimitives 0 1 1 (1 / 2) searchExampleF where
  hz := zero_le_one
  hx := one_pos
  hβ0 := by norm_num
  hβ1 := by norm_num
  cont :=
    ((continuous_const.sub continuous_fst).mul (continuous_const.add continuous_snd)).continuousOn
  F1 := fun z hz x _ y _ hxy => by
    simp only [searchExampleF]
    nlinarith [hz.1]
  F1top := fun z _ => by simp [searchExampleF]
  F2 := fun x hx z _ z' _ hzz' => by
    simp only [searchExampleF]
    nlinarith [hx.2]

/-- The identity kernel on `[0, 1]` (no shocks move) is Feller. -/
theorem searchExample_feller : IsFeller (Kernel.id : Kernel (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) :=
  fun φ hφ _ => by
    have : markovOpR (Kernel.id : Kernel (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) φ = φ :=
      funext fun z => by simp [markovOpR, Kernel.id_apply]
    rw [this]; exact hφ

/-- The identity kernel on `[0, 1]` is monotone. -/
theorem searchExample_monotone :
    IsMonotoneTF (Kernel.id : Kernel (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) := fun φ _ _ hm => by
  have : markovOpR (Kernel.id : Kernel (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) φ = φ :=
    funext fun z => by simp [markovOpR, Kernel.id_apply]
  rw [this]; exact hm

/-- In the concrete instance, `θ̄ = f(0, 1)/(1 − 1/2) = 4`. -/
theorem searchExample_thetaBar : searchThetaBar 1 (1 / 2) searchExampleF = 4 := by
  norm_num [searchThetaBar, searchExampleF]

/-- **Counterexample to the hint of Ex. 13.8d, concrete instance.** Here `θ̄ = 4`, and some
`θ ∈ (0, 4)` (indeed every `θ ∈ [2, 4)`) has no state in Case C. -/
theorem ex_13_8d_hint_counterexample_concrete :
    ¬ ∀ θ ∈ Ioo (0 : ℝ) 4,
      (∃ p, searchPhi 1 (Kernel.id : Kernel (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) searchExampleF
          (1 / 2) θ p < θ) ∧
        ∃ p, θ < searchEV 1 (Kernel.id : Kernel (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) searchExampleF
          (1 / 2) θ p := by
  have := ex_13_8d_hint_counterexample _ searchExample_primitives searchExample_feller
    searchExample_monotone
  rwa [searchExample_thetaBar] at this

/-- **Counterexample to "D is strictly decreasing for θ > 0" (p. 412), concrete instance.** -/
theorem ex_13_8h_counterexample_concrete :
    ¬ StrictAntiOn (searchD 1 (Kernel.id : Kernel (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
      searchExampleF (1 / 2)) (Ioi 0) :=
  ex_13_8h_counterexample _ searchExample_primitives searchExample_feller searchExample_monotone

end StokeyLucasPrescott.ConvergenceApplications
