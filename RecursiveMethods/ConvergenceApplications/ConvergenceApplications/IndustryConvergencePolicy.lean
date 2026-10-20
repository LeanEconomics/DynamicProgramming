/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.IndustryInvestmentFOC
import ConvergenceApplications.IndustryConvergence

/-!
# Industry investment: the §10.4 policy satisfies the hypotheses of §13.4

SLP §13.4, p. 395, takes the policy `g` of §10.4 with the properties of Exercise 10.4(d, e)
(`IndustryPolicy`). Here `g = indPolicyFn` is the optimal policy of the fixed point `v` of (2′)
(`IndustryInvestmentResults`), extended by `0` off `X × Z`.

* `indPolicyFn_mem`: `g(x, z)` is the optimal choice at `(x, z)`.
* `indPolicyFn_props`: with `U(·, z)` and `c` differentiable on `(0, ∞)`, `Q` monotone and `U`
  with increasing differences in `(x, z)`, `g` is continuous on `X × Z`, positive, strictly
  increasing in `x`, with `g(x, z)/x` strictly decreasing in `x`, and nondecreasing in `z`
  (Exercise 10.4d–e, `IndustryInvestmentFOC`).
* `indPolicyFn_industryPolicy`: under the same hypotheses `g` is an `IndustryPolicy`, so every
  §13.4 result (`industry_exists_xlo_xhi`, `ex_13_4b`, `ex_13_4c`, …) applies to it.
* `indPolicyFn_ind0`: the parameters `ind0_hyp` with the i.i.d. kernel `indQ0` give an
  `IndustryPolicy` whose slope exceeds one somewhere.

## Correction

* The book's §13.4 hypothesis (i) asks for slope below one (Exercise 10.4d). The §10.4 policy
  need not have it (`ex_10_4d_slope_counterexample`, `indPolicyFn_ind0`); `IndustryPolicy` now
  asks for `g(x, z)/x` strictly decreasing instead (`IndustryPolicy.ratio_lt`).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

variable {U : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {δ δ' M r A z₁ z₂ : ℝ}

/-- The optimal policy of (2′) as a function on `ℝ × ℝ`: `g(x, z)` is the maximizer at
`(x, z) ∈ X × Z`, and `0` elsewhere. -/
noncomputable def indPolicyFn (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) (U : ℝ → ℝ → ℝ)
    (c : ℝ → ℝ) (δ' M r : ℝ) (v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ) (x z : ℝ) : ℝ := by
  classical
  exact if hx : x ∈ Ioi 0 ∧ z ∈ Icc z₁ z₂ then
    (argmaxFn (indΓ δ' M) (objG (indModel Q U c δ' M r) v) (⟨x, hx.1⟩, ⟨z, hx.2⟩)).1 else 0

/-- On `X × Z`, `indPolicyFn` is the value of the maximizer `argmaxFn`. -/
theorem indPolicyFn_eq (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) (v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ)
    (x : Ioi (0 : ℝ)) (z : Icc z₁ z₂) :
    indPolicyFn Q U c δ' M r v x.1 z.1 =
      (argmaxFn (indΓ δ' M) (objG (indModel Q U c δ' M r) v) (x, z)).1 := by
  unfold indPolicyFn
  simp only [x.2, z.2, and_self, ↓reduceDIte]

/-- `g(x, z)` is the optimal choice at `(x, z)`. -/
theorem indPolicyFn_mem (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) (x : Ioi (0 : ℝ)) (z : Icc z₁ z₂) :
    argmaxFn (indΓ δ' M) (objG (indModel Q U c δ' M r) v) (x, z) ∈
      policy (indModel Q U c δ' M r) v (x, z) := by
  rw [(ind_policy h Q hQ hv).2.1]
  exact (ind_policy h Q hQ hv).1.argmaxFn_mem (x, z)

/-- **The §10.4 policy has the properties of Exercise 10.4(d, e).** With `U(·, z)` and `c`
differentiable on `(0, ∞)`, `Q` monotone and `U` with increasing differences in `(x, z)`, `g` is
continuous on `X × Z` and positive there, strictly increasing in `x`, nondecreasing in `z`, and
the growth rate `g(x, z)/x` is strictly decreasing in `x`. -/
theorem indPolicyFn_props (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hQm : IsMonotoneTF Q)
    (hUid : ∀ x x' z zh : ℝ, 0 < x → x ≤ x' → z₁ ≤ z → z ≤ zh → zh ≤ z₂ →
      U x' z - U x z ≤ U x' zh - U x zh)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v) :
    ContinuousOn (fun p : ℝ × ℝ => indPolicyFn Q U c δ' M r v p.1 p.2) (Ioi 0 ×ˢ Icc z₁ z₂) ∧
      (∀ x z, 0 < x → z ∈ Icc z₁ z₂ → 0 < indPolicyFn Q U c δ' M r v x z) ∧
      (∀ x x' z, 0 < x → x < x' → z ∈ Icc z₁ z₂ →
        indPolicyFn Q U c δ' M r v x z < indPolicyFn Q U c δ' M r v x' z) ∧
      (∀ x z z', 0 < x → z₁ ≤ z → z ≤ z' → z' ≤ z₂ →
        indPolicyFn Q U c δ' M r v x z ≤ indPolicyFn Q U c δ' M r v x z') ∧
      ∀ x x' z, 0 < x → x < x' → z ∈ Icc z₁ z₂ →
        indPolicyFn Q U c δ' M r v x' z / x' < indPolicyFn Q U c δ' M r v x z / x := by
  set G := argmaxFn (indΓ δ' M) (objG (indModel Q U c δ' M r) v)
  refine ⟨?_, fun x z hx hz => ?_, fun x x' z hx hxx hz => ?_, fun x z z' hx hz hzz hz' => ?_,
    fun x x' z hx hxx hz => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hm : Continuous fun q : (Ioi 0 ×ˢ Icc z₁ z₂ : Set (ℝ × ℝ)) =>
        ((⟨q.1.1, q.2.1⟩ : Ioi (0 : ℝ)), (⟨q.1.2, q.2.2⟩ : Icc z₁ z₂)) :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    have heq : (Ioi 0 ×ˢ Icc z₁ z₂).domRestrict
        (fun p : ℝ × ℝ => indPolicyFn Q U c δ' M r v p.1 p.2) =
        fun q => (G (⟨q.1.1, q.2.1⟩, ⟨q.1.2, q.2.2⟩)).1 := by
      funext q
      exact indPolicyFn_eq Q v ⟨q.1.1, q.2.1⟩ ⟨q.1.2, q.2.2⟩
    rw [heq]
    exact continuous_subtype_val.comp ((ind_policy h Q hQ hv).1.continuous_argmaxFn.comp hm)
  · rw [indPolicyFn_eq Q v ⟨x, hx⟩ ⟨z, hz⟩]
    exact (G _).2
  · rw [indPolicyFn_eq Q v ⟨x, hx⟩ ⟨z, hz⟩,
      indPolicyFn_eq Q v ⟨x', mem_Ioi.2 (hx.trans hxx)⟩ ⟨z, hz⟩]
    exact ind_policy_strictMono_x h Q hQ hv hUd hcd (x := ⟨x, hx⟩)
      (x' := ⟨x', mem_Ioi.2 (hx.trans hxx)⟩) hxx ⟨z, hz⟩ (indPolicyFn_mem h Q hQ hv _ _)
      (indPolicyFn_mem h Q hQ hv _ _)
  · rw [indPolicyFn_eq Q v ⟨x, hx⟩ ⟨z, hz, hzz.trans hz'⟩,
      indPolicyFn_eq Q v ⟨x, hx⟩ ⟨z', hz.trans hzz, hz'⟩]
    exact ex_10_4e h Q hQ hQm hUid hv (z := ⟨z, hz, hzz.trans hz'⟩)
      (zh := ⟨z', hz.trans hzz, hz'⟩) hzz (indPolicyFn_mem h Q hQ hv _ _)
      (indPolicyFn_mem h Q hQ hv _ _)
  · rw [indPolicyFn_eq Q v ⟨x, hx⟩ ⟨z, hz⟩,
      indPolicyFn_eq Q v ⟨x', mem_Ioi.2 (hx.trans hxx)⟩ ⟨z, hz⟩]
    exact ind_policy_ratio_lt h Q hQ hv hUd hcd (x := ⟨x, hx⟩)
      (x' := ⟨x', mem_Ioi.2 (hx.trans hxx)⟩) hxx ⟨z, hz⟩ (indPolicyFn_mem h Q hQ hv _ _)
      (indPolicyFn_mem h Q hQ hv _ _)

/-- **The §10.4 policy is an `IndustryPolicy`.** With `U(·, z)` and `c` differentiable on
`(0, ∞)`, `Q` monotone and `U` with increasing differences in `(x, z)` (`D` increasing in `z`), the
optimal policy satisfies the hypotheses of §13.4, so the results of `IndustryConvergence` apply to
it. -/
theorem indPolicyFn_industryPolicy (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hQm : IsMonotoneTF Q)
    (hUid : ∀ x x' z zh : ℝ, 0 < x → x ≤ x' → z₁ ≤ z → z ≤ zh → zh ≤ z₂ →
      U x' z - U x z ≤ U x' zh - U x zh)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v) :
    IndustryPolicy (indPolicyFn Q U c δ' M r v) z₁ z₂ := by
  obtain ⟨hcont, hpos, hmono, hmz, hratio⟩ := indPolicyFn_props h Q hQ hQm hUid hUd hcd hv
  exact ⟨hcont, hpos, hmono, hratio, hmz⟩

/-- **The slope of the §10.4 policy can exceed one.** For the parameters `ind0_hyp` and the
i.i.d. kernel `indQ0` (monotone and Feller, `indQ0_props`), the optimal policy is an
`IndustryPolicy`, yet `g(x′, z) − g(x, z) > x′ − x` for some `x < x′`
(`ex_10_4d_slope_counterexample`). So the book's slope condition could not have been kept. -/
theorem indPolicyFn_ind0 {v : Ioi (0 : ℝ) × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : truncT (ind0_hyp.upperDP indQ0 indQ0_props.1) v = v) :
    IndustryPolicy (indPolicyFn indQ0 indU0 cq (3 / 4) 200 1 v) 1 2 ∧
      ∃ x x' z : ℝ, 0 < x ∧ x < x' ∧ z ∈ Icc (1 : ℝ) 2 ∧
        x' - x < indPolicyFn indQ0 indU0 cq (3 / 4) 200 1 v x' z -
          indPolicyFn indQ0 indU0 cq (3 / 4) 200 1 v x z := by
  refine ⟨indPolicyFn_industryPolicy ind0_hyp indQ0 indQ0_props.1 indQ0_props.2.1
    indU0_incDiff ind0_diff.1 ind0_diff.2 hv, ?_⟩
  set z : Icc (1 : ℝ) 2 := ⟨1, by norm_num, by norm_num⟩
  obtain ⟨x, x', y, y', hxx, hy, hy', hslope⟩ :=
    ex_10_4d_slope_counterexample indQ0 indQ0_props.1 hv z
  have hU := (ind_policy ind0_hyp indQ0 indQ0_props.1 hv).1
  have hpol := (ind_policy ind0_hyp indQ0 indQ0_props.1 hv).2.1
  have e : y = argmaxFn (indΓ (3 / 4) 200)
      (objG (indModel indQ0 indU0 cq (3 / 4) 200 1) v) (x, z) :=
    hU.unique (x, z) y (hpol (x, z) ▸ hy) _ (hU.argmaxFn_mem (x, z))
  have e' : y' = argmaxFn (indΓ (3 / 4) 200)
      (objG (indModel indQ0 indU0 cq (3 / 4) 200 1) v) (x', z) :=
    hU.unique (x', z) y' (hpol (x', z) ▸ hy') _ (hU.argmaxFn_mem (x', z))
  refine ⟨x.1, x'.1, z.1, x.2, hxx, z.2, ?_⟩
  rw [indPolicyFn_eq indQ0 v x z, indPolicyFn_eq indQ0 v x' z, ← e, ← e']
  exact hslope

end StokeyLucasPrescott.ConvergenceApplications
