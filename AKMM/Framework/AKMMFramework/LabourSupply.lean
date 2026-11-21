/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import NeoclassicalGrowth.RMBasics

/-!
# Hours: KPR and Boppart–Krusell preferences on balanced paths

AKMM, §2.1.8, "Labor vs. leisure", pp. 63–65. Time endowment one, hours `ℓ`, leisure `l = 1 − ℓ`;
the intratemporal condition is `u₂(c, 1 − ℓ)/u₁(c, 1 − ℓ) = w` (the marginal rate of
substitution of leisure for consumption equals the wage).

* **KPR preferences** `u(c, l) = ((c v(l))^{1−σ} − 1)/(1 − σ)` (`lsKpr`). They are Miao's
  (14.5) `rmKprU` with `v^{1−σ}` in place of `v`, shifted by a constant (`ls_kpr_eq_rm`); the
  partials are Miao's `rmKprUc`, `rmKprUn` (`ls_kpr_hasDerivAt_c`, `ls_kpr_hasDerivAt_l`), and
  `u₂/u₁ = c v′(l)/v(l)` (`ls_kpr_mrs`). The "if" direction (p. 64): when `c` and `w` grow at the
  same factor, constant hours satisfy the hours condition every period and the Euler equation
  holds with a constant interest rate (`ls_kpr_balanced_growth`), from Miao's
  `rm_kpr_mrs_scale` and `rm_kpr_uc_scale`.
* **Boppart–Krusell preferences** `u(c, 1 − ℓ) = (c^{1−σ}g(c^{ν/(1−ν)}ℓ) − 1)/(1 − σ)`
  (`lsBK`), with partials `lsBKUc`, `lsBKUl` (`ls_bk_hasDerivAt_c`, `ls_bk_hasDerivAt_l`). The "if"
  direction: with the wage growing at `1 + γ`, consumption growing at `(1 + γ)^{1−ν}` and hours
  at `(1 + γ)^{−ν}` satisfy the hours condition every period and the Euler equation at a constant
  interest rate (`ls_bk_balanced_growth`). With `ν = 0` they are KPR preferences
  (`ls_bk_nu_zero`).
* **Production side** (p. 64): with labour-augmenting technology growing at `1 + γ`, hours at
  `(1 + γ)^{−ν}` and capital at `(1 + γ)^{1−ν}`, output grows at `(1 + γ)^{1−ν}`, the wage at
  `1 + γ`, and the labour share is constant (`ls_bk_production`).

**Corrections** (see `docs/corrections.md`). (1) p. 64 says "With technology and output growth
proceeding at a net rate γ", but on the Boppart–Krusell path output grows at `(1 + γ)^{1−ν}`, not
at `1 + γ`; if output did grow at `1 + γ` with a constant consumption share, consumption would not
grow at `(1 + γ)^{1−ν}` (`ls_p64_output_growth_correction`). Only technology and the wage grow at
`γ`; this is also what "wages now grow slightly faster than output" requires. (2) "`g(·)` is a
decreasing function" makes utility decrease in hours only for `σ < 1`; for `σ > 1` it is `g`
increasing that does (`ls_bk_hours_marginal_sign`, `ls_bk_decreasing_g_counterexample`).

The "only if" characterisations (King–Plosser–Rebelo; Boppart–Krusell) are cited, not proved, in
the book and are not formalised.
-/

namespace AKMM.Framework

open Filter Topology Miao.NeoclassicalGrowth

/-! ### KPR preferences -/

/-- AKMM, p. 64: KPR utility `u(c, l) = ((c v(l))^{1−σ} − 1)/(1 − σ)` in consumption and
leisure `l = 1 − ℓ`. -/
noncomputable def lsKpr (σ : ℝ) (v : ℝ → ℝ) (c l : ℝ) : ℝ := ((c * v l) ^ (1 - σ) - 1) / (1 - σ)

/-- AKMM, p. 64: the KPR form is Miao's (14.5) `c^{1−σ}ṽ(l)/(1 − σ)` with `ṽ = v^{1−σ}`, less the
constant `1/(1 − σ)`, for `c ≥ 0`, `v(l) ≥ 0`. -/
theorem ls_kpr_eq_rm (σ : ℝ) (v : ℝ → ℝ) {c l : ℝ} (hc : 0 ≤ c) (hv : 0 ≤ v l) :
    lsKpr σ v c l = rmKprU σ (fun x => v x ^ (1 - σ)) c l - 1 / (1 - σ) := by
  simp only [lsKpr, rmKprU, Real.mul_rpow hc hv]
  ring

/-- AKMM, p. 64: the marginal utility of consumption of KPR utility, `u₁ = c^{−σ}v(l)^{1−σ}`,
which is Miao's `rmKprUc σ v^{1−σ}`. -/
theorem ls_kpr_hasDerivAt_c {σ : ℝ} (hσ : σ ≠ 1) {v : ℝ → ℝ} {c l : ℝ} (hc : 0 < c)
    (hv : 0 < v l) :
    HasDerivAt (fun x => lsKpr σ v x l) (rmKprUc σ (fun x => v x ^ (1 - σ)) c l) c := by
  have h := (rm_kpr_hasDerivAt_c hσ (fun x => v x ^ (1 - σ)) hc l).sub_const (1 / (1 - σ))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hc] with x hx
  exact ls_kpr_eq_rm σ v (le_of_lt hx) hv.le

/-- AKMM, p. 64: the marginal utility of leisure of KPR utility, `u₂ = c^{1−σ}v(l)^{−σ}v′(l)`, which
is Miao's `rmKprUn σ ṽ′` with `ṽ′ = (1 − σ)v^{−σ}v′`, the derivative of `ṽ = v^{1−σ}`. -/
theorem ls_kpr_hasDerivAt_l {σ : ℝ} {v vd : ℝ → ℝ} {c l : ℝ} (hc : 0 ≤ c) (hv : 0 < v l)
    (hvd : HasDerivAt v (vd l) l) :
    HasDerivAt (fun x => lsKpr σ v c x)
      (rmKprUn σ (fun x => (1 - σ) * v x ^ (-σ) * vd x) c l) l := by
  have hpow : HasDerivAt (fun x => v x ^ (1 - σ)) ((1 - σ) * v l ^ (-σ) * vd l) l := by
    have := hvd.rpow_const (p := 1 - σ) (Or.inl hv.ne')
    refine this.congr_deriv ?_
    rw [show 1 - σ - 1 = -σ by ring]
    ring
  have h := (rm_kpr_hasDerivAt_n σ (v := fun x => v x ^ (1 - σ))
    (v' := fun x => (1 - σ) * v x ^ (-σ) * vd x) c hpow).sub_const (1 / (1 - σ))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hvd.continuousAt.eventually (lt_mem_nhds hv)] with x hx
  exact ls_kpr_eq_rm σ v hc hx.le

/-- AKMM, p. 64: for KPR utility (`σ ≠ 1`, `c > 0`, `v(l) > 0`) the hours condition reads
`u₂/u₁ = c v′(l)/v(l) = w`. -/
theorem ls_kpr_mrs {σ : ℝ} (hσ : σ ≠ 1) {v vd : ℝ → ℝ} {c l : ℝ} (hc : 0 < c) (hv : 0 < v l) :
    rmKprUn σ (fun x => (1 - σ) * v x ^ (-σ) * vd x) c l /
        rmKprUc σ (fun x => v x ^ (1 - σ)) c l = c * vd l / v l := by
  have h1 : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have hc1 : c ^ (1 - σ) = c * c ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hc, Real.rpow_one]
  have hv1 : v l ^ (1 - σ) = v l * v l ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hv, Real.rpow_one]
  have h2 : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  have h3 : 0 < v l ^ (-σ) := Real.rpow_pos_of_pos hv _
  simp only [rmKprUn, rmKprUc, hc1, hv1]
  field_simp

/-- AKMM, p. 64, the "if" direction for KPR preferences. Let `σ ≠ 1`, `β > 0`, leisure `l` with
`v(l) > 0`, and suppose the hours condition `u₂/u₁ = w` holds at `(c₀, l, w₀)`, `c₀ > 0`. If
consumption and the wage both grow at the gross rate `λ > 0`, `c_t = λ^t c₀`, `w_t = λ^t w₀`,
then constant hours (leisure `l` in every period) satisfy the hours condition in every period,
and the Euler equation `u₁(c_t, l) = βR u₁(c_{t+1}, l)` holds with the constant gross interest
rate `R = λ^σ/β`. -/
theorem ls_kpr_balanced_growth {σ β lam c₀ w₀ l : ℝ} {v vd : ℝ → ℝ} (hβ : 0 < β)
    (hlam : 0 < lam) (hc₀ : 0 < c₀) (hv : 0 < v l)
    (hfoc : rmKprUn σ (fun x => (1 - σ) * v x ^ (-σ) * vd x) c₀ l /
        rmKprUc σ (fun x => v x ^ (1 - σ)) c₀ l = w₀) (t : ℕ) :
    rmKprUn σ (fun x => (1 - σ) * v x ^ (-σ) * vd x) (lam ^ t * c₀) l /
        rmKprUc σ (fun x => v x ^ (1 - σ)) (lam ^ t * c₀) l = lam ^ t * w₀ ∧
      rmKprUc σ (fun x => v x ^ (1 - σ)) (lam ^ t * c₀) l =
        β * (lam ^ σ / β) * rmKprUc σ (fun x => v x ^ (1 - σ)) (lam ^ (t + 1) * c₀) l := by
  have hvt : (fun x => v x ^ (1 - σ)) l ≠ 0 := (Real.rpow_pos_of_pos hv _).ne'
  have hlt : 0 < lam ^ t := pow_pos hlam t
  refine ⟨?_, ?_⟩
  · have h := rm_kpr_mrs_scale σ (v := fun x => v x ^ (1 - σ))
      (v' := fun x => (1 - σ) * v x ^ (-σ) * vd x) hlt hc₀ l hvt
    rw [neg_div, neg_div, hfoc] at h
    linarith
  · have hct : 0 < lam ^ t * c₀ := mul_pos hlt hc₀
    rw [show lam ^ (t + 1) * c₀ = lam * (lam ^ t * c₀) by rw [pow_succ]; ring,
      rm_kpr_uc_scale σ _ hlam hct l, Real.rpow_neg hlam.le]
    have h1 : 0 < lam ^ σ := Real.rpow_pos_of_pos hlam σ
    field_simp

/-! ### Boppart–Krusell preferences -/

/-- AKMM, p. 64: Boppart–Krusell utility `u(c, 1 − ℓ) = (c^{1−σ}g(c^{ν/(1−ν)}ℓ) − 1)/(1 − σ)`,
written as a function of consumption `c` and hours `ℓ`. -/
noncomputable def lsBK (σ ν : ℝ) (g : ℝ → ℝ) (c ℓ : ℝ) : ℝ :=
  (c ^ (1 - σ) * g (c ^ (ν / (1 - ν)) * ℓ) - 1) / (1 - σ)

/-- The marginal utility of consumption of Boppart–Krusell utility, with `x = c^{ν/(1−ν)}ℓ`:
`u_c = c^{−σ}(g(x) + (ν/(1 − ν)) x g′(x)/(1 − σ))`. -/
noncomputable def lsBKUc (σ ν : ℝ) (g gd : ℝ → ℝ) (c ℓ : ℝ) : ℝ :=
  c ^ (-σ) * (g (c ^ (ν / (1 - ν)) * ℓ) +
    ν / (1 - ν) * (c ^ (ν / (1 - ν)) * ℓ) * gd (c ^ (ν / (1 - ν)) * ℓ) / (1 - σ))

/-- The marginal utility of hours of Boppart–Krusell utility,
`u_ℓ = c^{1−σ}c^{ν/(1−ν)}g′(x)/(1 − σ)`; the book's `u₂ = −u_ℓ`. -/
noncomputable def lsBKUl (σ ν : ℝ) (gd : ℝ → ℝ) (c ℓ : ℝ) : ℝ :=
  c ^ (1 - σ) * c ^ (ν / (1 - ν)) * gd (c ^ (ν / (1 - ν)) * ℓ) / (1 - σ)

/-- AKMM, p. 64: `∂u/∂c = lsBKUc` for Boppart–Krusell utility at `c > 0`, `σ ≠ 1`. -/
theorem ls_bk_hasDerivAt_c {σ ν : ℝ} (hσ : σ ≠ 1) {g gd : ℝ → ℝ} {c ℓ : ℝ} (hc : 0 < c)
    (hg : HasDerivAt g (gd (c ^ (ν / (1 - ν)) * ℓ)) (c ^ (ν / (1 - ν)) * ℓ)) :
    HasDerivAt (fun y => lsBK σ ν g y ℓ) (lsBKUc σ ν g gd c ℓ) c := by
  set e := ν / (1 - ν) with he
  have h1 := Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')
  have h2 : HasDerivAt (fun y => y ^ e * ℓ) (e * c ^ (e - 1) * ℓ) c :=
    (Real.hasDerivAt_rpow_const (p := e) (Or.inl hc.ne')).mul_const ℓ
  have h := ((h1.mul (hg.comp c h2)).sub_const 1).div_const (1 - σ)
  refine h.congr_deriv ?_
  have hσ1 : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have hc1 : c ^ (1 - σ - 1) = c ^ (-σ) := by rw [show 1 - σ - 1 = -σ by ring]
  have hc2 : c ^ (1 - σ) = c * c ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hc, Real.rpow_one]
  have hc3 : c ^ (e - 1) = c ^ e / c := Real.rpow_sub_one hc.ne' e
  simp only [lsBKUc, hc1, hc2, hc3, ← he, Function.comp_apply]
  field_simp

/-- AKMM, p. 64: `∂u/∂ℓ = lsBKUl` for Boppart–Krusell utility. -/
theorem ls_bk_hasDerivAt_l (σ ν : ℝ) {g gd : ℝ → ℝ} (c : ℝ) {ℓ : ℝ}
    (hg : HasDerivAt g (gd (c ^ (ν / (1 - ν)) * ℓ)) (c ^ (ν / (1 - ν)) * ℓ)) :
    HasDerivAt (fun h => lsBK σ ν g c h) (lsBKUl σ ν gd c ℓ) ℓ := by
  have h2 : HasDerivAt (fun h => c ^ (ν / (1 - ν)) * h) (c ^ (ν / (1 - ν))) ℓ := by
    simpa using (hasDerivAt_id ℓ).const_mul (c ^ (ν / (1 - ν)))
  have h := (((hg.comp ℓ h2).const_mul (c ^ (1 - σ))).sub_const 1).div_const (1 - σ)
  refine h.congr_deriv ?_
  simp only [lsBKUl]
  ring

/-- On a Boppart–Krusell path the argument `x = c^{ν/(1−ν)}ℓ` of `g` is unchanged when `c` is
scaled by `a > 0` and `ℓ` by `b` with `a^{ν/(1−ν)}b = 1`. -/
theorem ls_bk_arg_invariant {ν a b c ℓ : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ^ (ν / (1 - ν)) * b = 1) :
    (a * c) ^ (ν / (1 - ν)) * (b * ℓ) = c ^ (ν / (1 - ν)) * ℓ := by
  rw [Real.mul_rpow ha.le hc.le]
  linear_combination (c ^ (ν / (1 - ν)) * ℓ) * hab

/-- Scaling of `u_c` along a Boppart–Krusell path: `u_c(ac, bℓ) = a^{−σ}u_c(c, ℓ)` when
`a^{ν/(1−ν)}b = 1`. -/
theorem ls_bk_uc_scale (σ ν : ℝ) (g gd : ℝ → ℝ) {a b c ℓ : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ^ (ν / (1 - ν)) * b = 1) :
    lsBKUc σ ν g gd (a * c) (b * ℓ) = a ^ (-σ) * lsBKUc σ ν g gd c ℓ := by
  unfold lsBKUc
  rw [ls_bk_arg_invariant ha hc hab]
  simp only [Real.mul_rpow ha.le hc.le]
  ring

/-- Scaling of `u_ℓ` along a Boppart–Krusell path: `u_ℓ(ac, bℓ) = a^{1−σ}a^{ν/(1−ν)}u_ℓ(c, ℓ)`
when `a^{ν/(1−ν)}b = 1`. -/
theorem ls_bk_ul_scale (σ ν : ℝ) (gd : ℝ → ℝ) {a b c ℓ : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ^ (ν / (1 - ν)) * b = 1) :
    lsBKUl σ ν gd (a * c) (b * ℓ) = a ^ (1 - σ) * a ^ (ν / (1 - ν)) * lsBKUl σ ν gd c ℓ := by
  unfold lsBKUl
  rw [ls_bk_arg_invariant ha hc hab]
  simp only [Real.mul_rpow ha.le hc.le]
  ring

/-- The marginal rate of substitution `−u_ℓ/u_c` along a Boppart–Krusell path scales by
`a·a^{ν/(1−ν)}` (`= a^{1/(1−ν)}`) when `a^{ν/(1−ν)}b = 1`. -/
theorem ls_bk_mrs_scale (σ ν : ℝ) (g gd : ℝ → ℝ) {a b c ℓ : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ^ (ν / (1 - ν)) * b = 1) (hU : lsBKUc σ ν g gd c ℓ ≠ 0) :
    -lsBKUl σ ν gd (a * c) (b * ℓ) / lsBKUc σ ν g gd (a * c) (b * ℓ) =
      a * a ^ (ν / (1 - ν)) * (-lsBKUl σ ν gd c ℓ / lsBKUc σ ν g gd c ℓ) := by
  rw [ls_bk_ul_scale σ ν gd ha hc hab, ls_bk_uc_scale σ ν g gd ha hc hab]
  have h1 : a ^ (1 - σ) = a * a ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add ha, Real.rpow_one]
  have h2 : 0 < a ^ (-σ) := Real.rpow_pos_of_pos ha _
  rw [h1]
  field_simp

/-- AKMM, p. 64, the "if" direction for Boppart–Krusell preferences. Let `ν ≠ 1`, `β > 0`,
`λ = 1 + γ > 0`, `c₀ > 0`, and suppose the hours condition `−u_ℓ/u_c = w` holds at
`(c₀, ℓ₀, w₀)` with `u_c ≠ 0`. Along `c_t = λ^{(1−ν)t}c₀`, `ℓ_t = λ^{−νt}ℓ₀`, `w_t = λ^t w₀`
(consumption grows at `(1 + γ)^{1−ν}`, hours at `(1 + γ)^{−ν}`, the wage at `1 + γ`), the hours
condition holds in every period and the Euler equation `u_c(c_t, ℓ_t) = βRu_c(c_{t+1}, ℓ_{t+1})`
holds with the constant gross rate `R = λ^{(1−ν)σ}/β`. -/
theorem ls_bk_balanced_growth {σ ν β lam c₀ ℓ₀ w₀ : ℝ} {g gd : ℝ → ℝ} (hν : ν ≠ 1)
    (hβ : 0 < β) (hlam : 0 < lam) (hc₀ : 0 < c₀) (hU : lsBKUc σ ν g gd c₀ ℓ₀ ≠ 0)
    (hfoc : -lsBKUl σ ν gd c₀ ℓ₀ / lsBKUc σ ν g gd c₀ ℓ₀ = w₀) (t : ℕ) :
    lam ^ ((1 - ν) * ((t + 1 : ℕ) : ℝ)) * c₀ = lam ^ (1 - ν) * (lam ^ ((1 - ν) * t) * c₀) ∧
      lam ^ (-ν * ((t + 1 : ℕ) : ℝ)) * ℓ₀ = lam ^ (-ν) * (lam ^ (-ν * t) * ℓ₀) ∧
      -lsBKUl σ ν gd (lam ^ ((1 - ν) * t) * c₀) (lam ^ (-ν * t) * ℓ₀) /
          lsBKUc σ ν g gd (lam ^ ((1 - ν) * t) * c₀) (lam ^ (-ν * t) * ℓ₀) = lam ^ t * w₀ ∧
      lsBKUc σ ν g gd (lam ^ ((1 - ν) * t) * c₀) (lam ^ (-ν * t) * ℓ₀) =
        β * (lam ^ ((1 - ν) * σ) / β) *
          lsBKUc σ ν g gd (lam ^ ((1 - ν) * ((t + 1 : ℕ) : ℝ)) * c₀)
            (lam ^ (-ν * ((t + 1 : ℕ) : ℝ)) * ℓ₀) := by
  have hν1 : (1 : ℝ) - ν ≠ 0 := sub_ne_zero.2 (Ne.symm hν)
  -- `(λ^{(1−ν)s})^{ν/(1−ν)} λ^{−νs} = 1` for every real `s`
  have hinv : ∀ s : ℝ, (lam ^ ((1 - ν) * s)) ^ (ν / (1 - ν)) * lam ^ (-ν * s) = 1 := by
    intro s
    rw [← Real.rpow_mul hlam.le, ← Real.rpow_add hlam,
      show (1 - ν) * s * (ν / (1 - ν)) + -ν * s = 0 by field_simp; ring, Real.rpow_zero]
  have hsucc : ∀ x : ℝ, lam ^ (x * ((t + 1 : ℕ) : ℝ)) = lam ^ x * lam ^ (x * t) := by
    intro x
    rw [← Real.rpow_add hlam]
    push_cast
    ring_nf
  have hc_t : 0 < lam ^ ((1 - ν) * t) * c₀ := mul_pos (Real.rpow_pos_of_pos hlam _) hc₀
  refine ⟨by rw [hsucc]; ring, by rw [hsucc]; ring, ?_, ?_⟩
  · rw [ls_bk_mrs_scale σ ν g gd (Real.rpow_pos_of_pos hlam _) hc₀ (hinv t) hU, hfoc]
    congr 1
    rw [← Real.rpow_mul hlam.le, ← Real.rpow_add hlam,
      show (1 - ν) * t + (1 - ν) * t * (ν / (1 - ν)) = (t : ℝ) by field_simp; ring,
      Real.rpow_natCast]
  · have h1' : (lam ^ (1 - ν)) ^ (ν / (1 - ν)) * lam ^ (-ν) = 1 := by
      have := hinv 1
      rwa [mul_one, mul_one] at this
    have hsc := ls_bk_uc_scale σ ν g gd (a := lam ^ (1 - ν)) (b := lam ^ (-ν))
      (ℓ := lam ^ (-ν * t) * ℓ₀) (Real.rpow_pos_of_pos hlam _) hc_t h1'
    rw [hsucc (1 - ν), hsucc (-ν),
      show lam ^ (1 - ν) * lam ^ ((1 - ν) * t) * c₀ = lam ^ (1 - ν) * (lam ^ ((1 - ν) * t) * c₀)
        by ring,
      show lam ^ (-ν) * lam ^ (-ν * t) * ℓ₀ = lam ^ (-ν) * (lam ^ (-ν * t) * ℓ₀) by ring,
      hsc, ← Real.rpow_mul hlam.le]
    have h1 : 0 < lam ^ ((1 - ν) * σ) := Real.rpow_pos_of_pos hlam _
    rw [show (1 - ν) * -σ = -((1 - ν) * σ) by ring, Real.rpow_neg hlam.le]
    field_simp

/-- AKMM, p. 65: with `ν = 0` Boppart–Krusell utility is KPR utility: if
`g(ℓ) = v(1 − ℓ)^{1−σ}`, then `(c^{1−σ}g(ℓ) − 1)/(1 − σ) = ((c v(1 − ℓ))^{1−σ} − 1)/(1 − σ)`. -/
theorem ls_bk_nu_zero (σ : ℝ) {g v : ℝ → ℝ} (hgv : ∀ h, g h = v (1 - h) ^ (1 - σ)) {c ℓ : ℝ}
    (hc : 0 ≤ c) (hv : 0 ≤ v (1 - ℓ)) :
    lsBK σ 0 g c ℓ = lsKpr σ v c (1 - ℓ) := by
  simp only [lsBK, lsKpr, zero_div, Real.rpow_zero, one_mul, hgv, Real.mul_rpow hc hv]

/-- AKMM, p. 64 (with `σ ≠ 1`, `c > 0`): if `g′(x) < 0`, utility falls with hours
(`u_ℓ < 0`) when `σ < 1`, but rises with hours (`u_ℓ > 0`) when `σ > 1`. So "g decreasing" is the
right restriction only for `σ < 1`. -/
theorem ls_bk_hours_marginal_sign {σ ν : ℝ} {gd : ℝ → ℝ} {c ℓ : ℝ} (hc : 0 < c)
    (hgd : gd (c ^ (ν / (1 - ν)) * ℓ) < 0) :
    (σ < 1 → lsBKUl σ ν gd c ℓ < 0) ∧ (1 < σ → 0 < lsBKUl σ ν gd c ℓ) := by
  have hp : 0 < c ^ (1 - σ) * c ^ (ν / (1 - ν)) :=
    mul_pos (Real.rpow_pos_of_pos hc _) (Real.rpow_pos_of_pos hc _)
  have hn : c ^ (1 - σ) * c ^ (ν / (1 - ν)) * gd (c ^ (ν / (1 - ν)) * ℓ) < 0 :=
    mul_neg_of_pos_of_neg hp hgd
  refine ⟨fun hσ => div_neg_of_neg_of_pos hn (by linarith),
    fun hσ => div_pos_of_neg_of_neg hn (by linarith)⟩

/-- AKMM, p. 64, counterexample to "`g(·)` is a decreasing function" for `σ > 1`: with `σ = 2`,
`ν = 1/2` and the decreasing `g(x) = 2 − x`, at `c = 1`, `ℓ = 1/2` (where `g = 3/2 > 0`) utility
strictly increases with hours: `∂u/∂ℓ = 1`. -/
theorem ls_bk_decreasing_g_counterexample :
    StrictAnti (fun x : ℝ => 2 - x) ∧
      HasDerivAt (fun h => lsBK 2 (1 / 2) (fun x => 2 - x) 1 h) 1 (1 / 2) := by
  refine ⟨fun a b hab => by linarith, ?_⟩
  have hg : HasDerivAt (fun x : ℝ => 2 - x) ((fun _ : ℝ => (-1 : ℝ))
      ((1 : ℝ) ^ ((1 / 2 : ℝ) / (1 - 1 / 2)) * (1 / 2))) ((1 : ℝ) ^ ((1 / 2 : ℝ) / (1 - 1 / 2))
        * (1 / 2)) := by
    simpa using (hasDerivAt_id ((1 : ℝ) ^ ((1 / 2 : ℝ) / (1 - 1 / 2)) * (1 / 2))).const_sub 2
  refine (ls_bk_hasDerivAt_l (gd := fun _ => -1) 2 (1 / 2) 1 hg).congr_deriv ?_
  simp only [lsBKUl, Real.one_rpow]
  norm_num

/-! ### The production side of the Boppart–Krusell path and the p. 64 correction -/

/-- AKMM, p. 64, production side. Let `F` have constant returns on the positive quadrant with
partial `F₂` in its second argument, technology `A_t = λ^t` (labour-augmenting), hours
`ℓ_t = λ^{−νt}ℓ₀` and capital `k_t = λ^{(1−ν)t}k₀`, `λ, k₀, ℓ₀ > 0`. Then output
`y_t = F(k_t, A_tℓ_t) = λ^{(1−ν)t}F(k₀, ℓ₀)` grows at `λ^{1−ν}`, the wage
`w_t = A_t F₂(k_t, A_tℓ_t) = λ^t F₂(k₀, ℓ₀)` grows at `λ`, and the labour share `w_tℓ_t/y_t`
is constant. -/
theorem ls_bk_production {F F2 : ℝ → ℝ → ℝ}
    (hhom : ∀ s x y, 0 < s → 0 < x → 0 < y → F (s * x) (s * y) = s * F x y)
    (hF2 : ∀ x y, 0 < x → 0 < y → HasDerivAt (fun z => F x z) (F2 x y) y)
    {lam ν k₀ ℓ₀ : ℝ} (hlam : 0 < lam) (hk₀ : 0 < k₀) (hℓ₀ : 0 < ℓ₀) (hF0 : F k₀ ℓ₀ ≠ 0)
    (t : ℕ) :
    F (lam ^ ((1 - ν) * t) * k₀) (lam ^ t * (lam ^ (-ν * t) * ℓ₀)) =
        lam ^ ((1 - ν) * t) * F k₀ ℓ₀ ∧
      lam ^ t * F2 (lam ^ ((1 - ν) * t) * k₀) (lam ^ t * (lam ^ (-ν * t) * ℓ₀)) =
        lam ^ t * F2 k₀ ℓ₀ ∧
      lam ^ t * F2 (lam ^ ((1 - ν) * t) * k₀) (lam ^ t * (lam ^ (-ν * t) * ℓ₀)) *
          (lam ^ (-ν * t) * ℓ₀) /
          F (lam ^ ((1 - ν) * t) * k₀) (lam ^ t * (lam ^ (-ν * t) * ℓ₀)) =
        F2 k₀ ℓ₀ * ℓ₀ / F k₀ ℓ₀ := by
  have hA : lam ^ t * (lam ^ (-ν * t) * ℓ₀) = lam ^ ((1 - ν) * t) * ℓ₀ := by
    rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hlam]
    ring_nf
  have hs : 0 < lam ^ ((1 - ν) * t) := Real.rpow_pos_of_pos hlam _
  have hy := hhom _ _ _ hs hk₀ hℓ₀
  have hw := rm_partial2_homog_zero hhom hF2 hs hk₀ hℓ₀
  rw [hA, hy, hw]
  refine ⟨rfl, rfl, ?_⟩
  have h1 : lam ^ t * lam ^ (-ν * t) = lam ^ ((1 - ν) * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hlam]
    ring_nf
  rw [show lam ^ t * F2 k₀ ℓ₀ * (lam ^ (-ν * t) * ℓ₀) =
    (lam ^ t * lam ^ (-ν * t)) * (F2 k₀ ℓ₀ * ℓ₀) by ring, h1]
  field_simp

/-- AKMM, p. 64, correction. The text says "with technology and output growth proceeding at a
net rate γ, … consumption [grows] at `(1 + γ)^{1−ν}`". For `λ = 1 + γ > 1` and `ν > 0`,
`λ^{1−ν} < λ`, and if output grew at `λ` with a constant consumption share `s_c > 0`,
consumption would grow at `λ`, never at `λ^{1−ν}`. On the Boppart–Krusell path it is
technology and the wage that grow at `λ`; output grows at `λ^{1−ν}` (`ls_bk_production`). -/
theorem ls_p64_output_growth_correction {lam ν : ℝ} (hlam : 1 < lam) (hν : 0 < ν) :
    lam ^ (1 - ν) < lam ∧
      ∀ (y c : ℕ → ℝ) (sc : ℝ), 0 < sc → (∀ t, 0 < y t) → (∀ t, y (t + 1) = lam * y t) →
        (∀ t, c t = sc * y t) → ∀ t, c (t + 1) ≠ lam ^ (1 - ν) * c t := by
  have hlt : lam ^ (1 - ν) < lam := by
    have := Real.rpow_lt_rpow_of_exponent_lt hlam (show 1 - ν < 1 by linarith)
    rwa [Real.rpow_one] at this
  refine ⟨hlt, fun y c sc hsc hy hgy hc t heq => ?_⟩
  have hct : 0 < c t := by rw [hc]; exact mul_pos hsc (hy t)
  have : c (t + 1) = lam * c t := by rw [hc, hc, hgy]; ring
  rw [this] at heq
  have := mul_right_cancel₀ hct.ne' heq
  linarith

end AKMM.Framework
