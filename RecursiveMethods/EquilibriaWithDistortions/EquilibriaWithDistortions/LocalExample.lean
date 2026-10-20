/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.LocalContraction

/-!
# A concrete economy satisfying Assumption 18.1

SLP §18.2. The economy `β = θ = 1/2`, `f(k) = 9 − 8e^{−k}` (`exF`) satisfies Assumption 18.1
for every admissible utility `U` (`exModel_assumption`), with `k* = log 2` and
`c* = 5 − 3 log 2`. This makes the local analysis non-vacuous and turns two corrections into
counterexamples about an actual economy.

* `exModel_assumption`: Assumption 18.1 holds (with some `k̄ ∈ (0, 9)`) for any `C²`, strictly
  increasing, strictly concave `U`; `k* = log 2 ∈ (0, k̄)` solves (5).
* `exModel_localHyp` (non-vacuity): with `U(c) = 1 − e^{−c}` (`exU`) all hypotheses of the local
  analysis hold, `U″(c*) < 0` and `f″(k*) < 0` included.
* `note_18_2B_model_counterexample` (NOTE 18.2-B): with `U = U_{c*}` (`flatU`, strictly
  concave with `U″(c*) = 0`), Assumption 18.1 holds but `P(0) = 0`, so the book's claim
  `P(0) < 0` fails for an economy satisfying Assumption 18.1.
* `ex_18_4a_model_counterexample` (NOTE 18.2-G): in the economy with `U = exU`, for every
  `λ ∈ (λ*, 1)` there is `ε` as in Proposition 18.2 (so `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`) for which `T` is
  not monotone on `D_λ(I_ε)`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- The production function `f(k) = 9 − 8e^{−k}`. -/
noncomputable def exF (k : ℝ) : ℝ := 9 - 8 * Real.exp (-k)

/-- The utility function `U(c) = 1 − e^{−c}`. -/
noncomputable def exU (c : ℝ) : ℝ := 1 - Real.exp (-c)

/-- `ψ(k) − k = 9 − 8e^{−k} − 4k e^{−k} − k` for `θ = 1/2`. -/
noncomputable def exG (k : ℝ) : ℝ := 9 - 8 * Real.exp (-k) - 4 * k * Real.exp (-k) - k

/-- `(e^{−x})′ = −e^{−x}`. -/
theorem hasDerivAt_exp_neg (x : ℝ) :
    HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-x)) x := by
  simpa using (hasDerivAt_neg x).exp

/-- `f′(k) = 8e^{−k}`. -/
theorem deriv_exF : deriv exF = fun k => 8 * Real.exp (-k) := by
  funext k
  have := ((hasDerivAt_exp_neg k).const_mul 8).const_sub 9
  exact this.deriv.trans (by ring)

/-- `f″(k) = −8e^{−k}`. -/
theorem deriv2_exF : deriv (deriv exF) = fun k => -8 * Real.exp (-k) := by
  rw [deriv_exF]
  funext k
  rw [((hasDerivAt_exp_neg k).const_mul 8).deriv]
  ring

/-- `U′(c) = e^{−c}`. -/
theorem deriv_exU : deriv exU = fun c => Real.exp (-c) := by
  funext c
  have := (hasDerivAt_exp_neg c).const_sub 1
  exact this.deriv.trans (by ring)

/-- `U″(c) = −e^{−c}`. -/
theorem deriv2_exU : deriv (deriv exU) = fun c => -Real.exp (-c) := by
  rw [deriv_exU]
  funext c
  rw [(hasDerivAt_exp_neg c).deriv]

/-- `ψ(k) − k = exG k`. -/
theorem psi_exF (k : ℝ) : psi (1 / 2) exF k - k = exG k := by
  simp only [psi, deriv_exF, exF, exG]
  ring

/-- `exG′(k) = 4e^{−k} + 4k e^{−k} − 1`. -/
theorem hasDerivAt_exG (k : ℝ) :
    HasDerivAt exG (4 * Real.exp (-k) + 4 * k * Real.exp (-k) - 1) k := by
  have h1 := (hasDerivAt_exp_neg k).const_mul 8
  have h2 := ((hasDerivAt_id' k).const_mul 4).mul (hasDerivAt_exp_neg k)
  have h3 := (((h1.const_sub 9).sub h2).sub (hasDerivAt_id' k))
  exact h3.congr_deriv (by ring)

/-- `exG″(k) = −4k e^{−k}`. -/
theorem deriv2_exG (k : ℝ) : deriv (deriv exG) k = -4 * k * Real.exp (-k) := by
  have e : deriv exG = fun k => 4 * Real.exp (-k) + 4 * k * Real.exp (-k) - 1 :=
    funext fun k => (hasDerivAt_exG k).deriv
  rw [e]
  have h1 := (hasDerivAt_exp_neg k).const_mul 4
  have h2 := ((hasDerivAt_id' k).const_mul 4).mul (hasDerivAt_exp_neg k)
  have h3 : HasDerivAt (fun k => 4 * Real.exp (-k) + 4 * k * Real.exp (-k) - 1)
      (4 * -Real.exp (-k) + (4 * 1 * Real.exp (-k) + 4 * k * -Real.exp (-k))) k :=
    (h1.add h2).sub_const 1
  rw [h3.deriv]
  ring

/-- `exG` is continuous. -/
theorem continuous_exG : Continuous exG := by
  unfold exG
  fun_prop

/-- **Assumption 18.1 for `f(k) = 9 − 8e^{−k}`, `β = θ = 1/2`**, and any `C²`, strictly
increasing, strictly concave `U`; moreover `k* = log 2 ∈ (0, k̄)` solves (5). -/
theorem exModel_assumption {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hUm : StrictMonoOn U (Ici 0))
    (hUc : StrictConcaveOn ℝ (Ici 0) U) :
    ∃ kbar, Assumption18_1 (1 / 2) (1 / 2) U exF kbar ∧ Real.log 2 ∈ Ioo 0 kbar ∧
      1 / 2 * (1 - 1 / 2) * deriv exF (Real.log 2) = 1 := by
  have hfC : ContDiff ℝ 2 exF := by
    unfold exF
    fun_prop
  have hfd : ∀ k, 0 < deriv exF k := fun k => by
    rw [deriv_exF]
    positivity
  have hfc : Continuous exF := by
    unfold exF
    fun_prop
  have hfconc : StrictConcaveOn ℝ univ exF := by
    refine strictConcaveOn_univ_of_deriv2_neg hfc fun x => ?_
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [deriv2_exF]
    have := Real.exp_pos (-x)
    linarith
  -- strict concavity of `ψ − id` on `[0, ∞)`
  have hGc : StrictConcaveOn ℝ (Ici 0) exG := by
    refine strictConcaveOn_of_deriv2_neg (convex_Ici 0) continuous_exG.continuousOn
      fun x hx => ?_
    rw [interior_Ici] at hx
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [deriv2_exG]
    have := Real.exp_pos (-x)
    have := mem_Ioi.1 hx
    nlinarith
  have hG0 : exG 0 = 1 := by norm_num [exG]
  have hG9 : exG 9 < 0 := by
    have : exG 9 = -44 * Real.exp (-9) := by simp only [exG]; ring
    rw [this]
    have := Real.exp_pos (-9)
    linarith
  obtain ⟨kbar, hk, hkv⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 9)
    continuous_exG.continuousOn ⟨hG9.le, by rw [hG0]; norm_num⟩
  have hk0 : 0 < kbar := by
    rcases eq_or_lt_of_le hk.1 with h | h
    · rw [← h, hG0] at hkv
      norm_num at hkv
    · exact h
  -- sign pattern of `ψ − id`
  have hpos : ∀ k ∈ Ioo 0 kbar, 0 < exG k := by
    intro k ⟨hk1, hk2⟩
    have h3' : 0 < 1 - k / kbar := by
      rw [sub_pos, div_lt_one hk0]
      exact hk2
    have := hGc.2 (mem_Ici.2 le_rfl) (mem_Ici.2 hk0.le) hk0.ne h3' (div_pos hk1 hk0) (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, hkv, mul_zero, add_zero, hG0, mul_one] at this
    rw [div_mul_cancel₀ k hk0.ne'] at this
    have h3 : 0 < 1 - k / kbar := by
      rw [sub_pos, div_lt_one hk0]
      exact hk2
    linarith
  have hneg : ∀ k, kbar < k → exG k < 0 := by
    intro k hk1
    have hkp : 0 < k := hk0.trans hk1
    have := hGc.2 (mem_Ici.2 le_rfl) (mem_Ici.2 hkp.le) hkp.ne
      (by rw [sub_pos, div_lt_one hkp]; exact hk1 : 0 < 1 - kbar / k) (div_pos hk0 hkp)
      (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, hG0, mul_one] at this
    rw [div_mul_cancel₀ kbar hkp.ne', hkv] at this
    have h3 : 0 < 1 - kbar / k := by rw [sub_pos, div_lt_one hkp]; exact hk1
    have h4 : 0 < kbar / k := div_pos hk0 hkp
    nlinarith
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog1 := Real.log_two_lt_d9
  have hGlog : 0 < exG (Real.log 2) := by
    have e : exG (Real.log 2) = 5 - 3 * Real.log 2 := by
      simp only [exG, Real.exp_neg, Real.exp_log two_pos]
      ring
    rw [e]
    norm_num at hlog1
    linarith
  have hlogk : Real.log 2 < kbar := by
    by_contra hc
    push Not at hc
    rcases eq_or_lt_of_le hc with h | h
    · rw [h] at hkv
      linarith
    · linarith [hneg _ h]
  refine ⟨kbar, ⟨by norm_num, by norm_num, hU, hUm, hUc, by norm_num, by norm_num, hfC,
    fun k hk => ?_, (strictMono_of_deriv_pos hfd).strictMonoOn _,
    hfconc.subset (subset_univ _) (convex_Ici 0), by norm_num [exF], ?_, hk0,
    fun k hk => ?_, fun k hk => ?_⟩, ⟨hlog, hlogk⟩, ?_⟩
  · simp only [exF]
    have : Real.exp (-k) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  · rw [deriv_exF]
    norm_num
  · have := hpos k hk
    rw [← psi_exF] at this
    linarith
  · have := hneg k hk
    rw [← psi_exF] at this
    linarith
  · rw [deriv_exF]
    simp only [Real.exp_neg, Real.exp_log two_pos]
    norm_num

/-- `exU` is admissible: `C²`, strictly increasing and strictly concave. -/
theorem exU_admissible :
    ContDiff ℝ 2 exU ∧ StrictMonoOn exU (Ici 0) ∧ StrictConcaveOn ℝ (Ici 0) exU := by
  have hc : Continuous exU := by
    unfold exU
    fun_prop
  refine ⟨by unfold exU; fun_prop, (strictMono_of_deriv_pos fun c => ?_).strictMonoOn _,
    (strictConcaveOn_univ_of_deriv2_neg hc fun x => ?_).subset (subset_univ _) (convex_Ici 0)⟩
  · rw [deriv_exU]
    positivity
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [deriv2_exU]
    have := Real.exp_pos (-x)
    linarith

/-- **Non-vacuity of the local analysis.** In the economy `β = θ = 1/2`, `f(k) = 9 − 8e^{−k}`,
`U(c) = 1 − e^{−c}`, Assumption 18.1 holds and so do the hypotheses `LocalHyp` at
`k* = log 2` (in particular `U″(c*) < 0`, `f″(k*) < 0`). -/
theorem exModel_localHyp :
    ∃ kbar, Assumption18_1 (1 / 2) (1 / 2) exU exF kbar ∧
      LocalHyp (1 / 2) (1 / 2) exU exF (Real.log 2) := by
  obtain ⟨hU, hUm, hUc⟩ := exU_admissible
  obtain ⟨kbar, A, hks, heul⟩ := exModel_assumption hU hUm hUc
  refine ⟨kbar, A, A.localHyp hks heul ?_ ?_⟩
  · rw [deriv2_exU]
    have := Real.exp_pos (-cstar (1 / 2) exF (Real.log 2))
    linarith
  · rw [deriv2_exF]
    have := Real.exp_pos (-Real.log 2)
    linarith

/-- **NOTE 18.2-B in an economy satisfying Assumption 18.1.** With `β = θ = 1/2`,
`f(k) = 9 − 8e^{−k}` and the strictly concave `U = U_{c*}` of
`strictConcave_deriv2_zero_counterexample` (`U″(c*) = 0`), Assumption 18.1 holds and `k* = log 2`
solves (5), but `P(0) = 0`: the book's claim `P(0) < 0` (p. 549) is false. -/
theorem note_18_2B_model_counterexample :
    ∃ kbar, Assumption18_1 (1 / 2) (1 / 2) (flatU (cstar (1 / 2) exF (Real.log 2))) exF kbar ∧
      Real.log 2 ∈ Ioo 0 kbar ∧ 1 / 2 * (1 - 1 / 2) * deriv exF (Real.log 2) = 1 ∧
      ¬ charPoly (1 / 2) (1 / 2) (flatU (cstar (1 / 2) exF (Real.log 2))) exF
        (Real.log 2) 0 < 0 := by
  obtain ⟨hC, hm, hc, h0⟩ := strictConcave_deriv2_zero_counterexample
    (cstar (1 / 2) exF (Real.log 2))
  obtain ⟨kbar, A, hks, heul⟩ := exModel_assumption hC (hm.strictMonoOn _)
    (hc.subset (subset_univ _) (convex_Ici 0))
  refine ⟨kbar, A, hks, heul, ?_⟩
  rw [(charPoly_degenerate_U h0).2.2.1]
  exact lt_irrefl 0

/-- **Exercise 18.4(a) is false in an economy satisfying Assumption 18.1** (NOTE 18.2-G). In the
economy of `exModel_localHyp` there is a local solution `H` of (7) such that for every
`λ ∈ (λ*, 1)` there is `ε` as in Proposition 18.2 (`T(D_λ(I_ε)) ⊆ D_λ(I_ε)`) but `T` is not
monotone on `D_λ(I_ε)`: some `h′ ≤ h` in `D_λ(I_ε)` have `(Th′)(k) > (Th)(k)` at some
`k ∈ I_ε`. -/
theorem ex_18_4a_model_counterexample :
    ∃ ε₀ H, LocalSolution (1 / 2) (1 / 2) exU exF (Real.log 2) ε₀ H ∧
      ∀ lam, lamStar (1 / 2) (1 / 2) exU exF (Real.log 2) < lam → lam < 1 →
        ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧
          (∀ h ∈ Dlam (Real.log 2) ε lam, Top H h ∈ Dlam (Real.log 2) ε lam) ∧
          ¬ ∀ h ∈ Dlam (Real.log 2) ε lam, ∀ h' ∈ Dlam (Real.log 2) ε lam,
            (∀ k ∈ Jint (Real.log 2) ε, h' k ≤ h k) →
              ∀ k ∈ Jint (Real.log 2) ε, Top H h' k ≤ Top H h k := by
  obtain ⟨kbar, -, L⟩ := exModel_localHyp
  obtain ⟨ε₀, H, hH⟩ := exists_localSolution L
  refine ⟨ε₀, H, hH, fun lam hl hl1 => ?_⟩
  obtain ⟨ε, hε, hεε₀, hT⟩ := prop_18_2 L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  obtain ⟨h1, h2, hle, hlt⟩ := ex_18_4a_counterexample hH hε hεε₀ hlpos hl1.le
  refine ⟨ε, hε, hεε₀, hT, fun hmono => ?_⟩
  have := hmono _ h1 _ h2 hle _ ⟨by linarith, le_rfl⟩
  linarith

end StokeyLucasPrescott.EquilibriaWithDistortions
