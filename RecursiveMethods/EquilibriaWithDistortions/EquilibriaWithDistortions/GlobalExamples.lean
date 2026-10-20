/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.GlobalOperator

/-!
# Concrete models for SLP §18.3: the corrected assumptions are consistent, and two of the book's
claims fail

All models use `U(c) = √c` (continuous on `[0, ∞)`, `C²` on `(0, ∞)`, `U′(c) = 1/(2√c) → ∞`), so
they satisfy Assumptions 18.1 and 18.2 in the corrected reading of `GlobalModel` — the reading
forced by `assumption_18_2_contradiction`.

* `ratModel`: technologies `f(k) = b + a k/(1 + k)`, with
  `ψ(k) − k = (k̄ − k)(k² + p k + q)/(1 + k)²` whenever the coefficients match
  (`ratTech_psi_sub`). This gives Assumption 18.1e with an explicit `k̄`.
* `modelE` (`b = 1/50`, `a = 891/250`, `θ = 1/2`, `β = 9/10`, `k̄ = 2`): `ψ(ψ(0)) ≤ k*`.
* `ex_18_5_counterexample` (**Correction**, NOTE 18.3-E): in `modelE` the member
  `min{ψ, k*}` of `F` makes (7) at `k = 0` have no solution with positive consumption, so `T`
  is not well defined on `F` as "the `y` solving (7)".
* `modelL` (`f(k) = 3 + 4 ∫₀ᵏ ds/(1 + s⁸)`, `θ = 1/2`, `β = 9/10`, `k̄` the root of `ψ(k) = k` in
  `(2, 20)`).
* `prop_18_5_bound_counterexample` (**Correction**, proof of Proposition 18.5, p. 557): in
  `modelL`, `ψ(1) − ψ(9/10) > f′(0) · (1 − 9/10)`, so the book's bound
  `|ψ(k′) − ψ(k)| ≤ A |k′ − k|` with `A = f′(0)` fails.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology BoundedContinuousFunction

/-! ### The utility `U(c) = √c` -/

/-- `√` is `C²` on `(0, ∞)`. -/
theorem sqrt_contDiffOn : ContDiffOn ℝ 2 (fun c : ℝ => √c) (Ioi 0) :=
  fun _ hx => (Real.contDiffAt_sqrt (ne_of_gt hx)).contDiffWithinAt

/-- `√` is strictly increasing on `[0, ∞)`. -/
theorem sqrt_strictMonoOn : StrictMonoOn (fun c : ℝ => √c) (Ici 0) :=
  fun _ hx _ _ hxy => Real.sqrt_lt_sqrt hx hxy

/-- The derivative of `√` on `(0, ∞)` is `1/(2√c)`. -/
theorem sqrt_hasDerivAt {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun c : ℝ => √c) (1 / (2 * √c)) c :=
  Real.hasDerivAt_sqrt hc.ne'

/-- The Inada condition for `U = √`: `1/(2√c) → ∞` as `c → 0⁺`. -/
theorem sqrt_inada : Tendsto (fun c : ℝ => 1 / (2 * √c)) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun c : ℝ => 2 * √c) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun c : ℝ => 2 * √c) (𝓝 0) (𝓝 (2 * √0)) :=
        (continuous_const.mul Real.continuous_sqrt).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact mul_pos two_pos (Real.sqrt_pos.2 hc)
  exact (tendsto_inv_nhdsGT_zero.comp h1).congr fun c => by simp [one_div]

/-! ### Rational technologies `f(k) = b + a k/(1 + k)` -/

/-- The derivative of `b + a k/(1 + k)` is `a/(1 + k)²` (for `k > −1`). -/
theorem ratTech_hasDerivAt (a b : ℝ) {k : ℝ} (hk : -1 < k) :
    HasDerivAt (fun k => b + a * k / (1 + k)) (a / (1 + k) ^ 2) k := by
  have h1 : HasDerivAt (fun k => a * k) a k := by simpa using (hasDerivAt_id k).const_mul a
  have h2 : HasDerivAt (fun k => 1 + k) 1 k := by simpa using (hasDerivAt_id k).const_add 1
  have h3 := (h1.div h2 (by linarith : (1 + k) ≠ 0)).const_add b
  convert h3 using 1
  field_simp
  ring

/-- `ψ(k) − k` for a rational technology, as a quotient of polynomials. -/
theorem ratTech_psi_sub {a b θ kbar p q : ℝ} (h1 : b = kbar * q) (h2 : kbar - p = b + a - 2)
    (h3 : kbar * p - q = 2 * b + a * (1 - θ) - 1) {k : ℝ} (hk : 0 ≤ k) :
    (b + a * k / (1 + k)) - θ * k * (a / (1 + k) ^ 2) - k =
      (kbar - k) * (k ^ 2 + p * k + q) / (1 + k) ^ 2 := by
  have hpoly : b * (1 + k) ^ 2 + a * k * (1 + k) - θ * k * a - k * (1 + k) ^ 2 =
      (kbar - k) * (k ^ 2 + p * k + q) := by
    linear_combination (-k ^ 2) * h2 + (-k) * h3 + h1
  rw [← hpoly]
  have : (1 + k) ≠ 0 := by linarith
  field_simp

/-- **A model with a rational technology.** `U = √`, `f(k) = b + a k/(1 + k)`, with coefficients
making `ψ(k) − k = (k̄ − k)(k² + p k + q)/(1 + k)²`. -/
noncomputable def ratModel (β θ a b kbar p q : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (ha : 1 / (β * (1 - θ)) < a) (hb : 0 < b) (hkbar : 0 < kbar) (hp : 0 ≤ p)
    (hq : 0 < q) (h1 : b = kbar * q) (h2 : kbar - p = b + a - 2)
    (h3 : kbar * p - q = 2 * b + a * (1 - θ) - 1) : GlobalModel where
  β := β
  θ := θ
  U := fun c => √c
  U' := fun c => 1 / (2 * √c)
  f := fun k => b + a * k / (1 + k)
  f' := fun k => a / (1 + k) ^ 2
  kbar := kbar
  β_pos := hβ0
  β_lt_one := hβ1
  U_cont := Real.continuous_sqrt.continuousOn
  U_contDiff := sqrt_contDiffOn
  U_strictMono := sqrt_strictMonoOn
  U_strictConcave := Real.strictConcaveOn_sqrt
  U_deriv _ hc := sqrt_hasDerivAt hc
  θ_pos := hθ0
  θ_lt_one := hθ1
  f_cont := continuousOn_const.add ((continuousOn_const.mul continuousOn_id).div
    (continuousOn_const.add continuousOn_id) fun k hk => by simp at hk ⊢; linarith)
  f_contDiff := contDiffOn_const.add ((contDiffOn_const.mul contDiffOn_id).div
    (contDiffOn_const.add contDiffOn_id) fun k hk => by simp at hk ⊢; linarith)
  f_strictMono := by
    have ha0 : 0 < a := lt_trans (by positivity) ha
    intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    simp only [add_lt_add_iff_left]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  f_strictConcave := by
    have ha0 : 0 < a := lt_trans (by positivity) ha
    refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
      (continuousOn_const.add ((continuousOn_const.mul continuousOn_id).div
        (continuousOn_const.add continuousOn_id) fun k hk => by simp at hk ⊢; linarith)) ?_
    rw [interior_Ici]
    intro x hx y hy hxy
    simp only [mem_Ioi] at hx hy
    rw [(ratTech_hasDerivAt a b (by linarith)).deriv, (ratTech_hasDerivAt a b (by linarith)).deriv]
    exact div_lt_div_of_pos_left ha0 (by positivity) (by nlinarith)
  f_deriv _ hk := ratTech_hasDerivAt a b (by linarith)
  f_zero_pos := by simpa using hb
  f'_zero := by simpa using ha
  kbar_pos := hkbar
  psi_gt k hk0 hk := by
    have := ratTech_psi_sub h1 h2 h3 hk0.le
    have hpos : 0 < (kbar - k) * (k ^ 2 + p * k + q) / (1 + k) ^ 2 :=
      div_pos (mul_pos (by linarith) (by positivity)) (by positivity)
    linarith
  psi_lt k hk := by
    have hk0 : 0 ≤ k := (hkbar.trans hk).le
    have := ratTech_psi_sub h1 h2 h3 hk0
    have hneg : (kbar - k) * (k ^ 2 + p * k + q) / (1 + k) ^ 2 < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by positivity)) (by positivity)
    linarith
  f'_contAt_zero := (continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
    fun k hk => by
      simp only [Pi.pow_apply, Pi.add_apply, id_eq, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff, mem_Ici] at hk ⊢
      linarith) 0 (mem_Ici.2 le_rfl)
  U'_inada := sqrt_inada

/-! ### NOTE 18.3-E: a model in which (7) has no solution for some `h ∈ F` -/

/-- The model of NOTE 18.3-E: `U = √`, `f(k) = 1/50 + (891/250) k/(1 + k)`, `θ = 1/2`,
`β = 9/10`; then `ψ(k) − k = (2 − k)(k² + (52/125) k + 1/100)/(1 + k)²`, so `k̄ = 2`. -/
noncomputable def modelE : GlobalModel :=
  ratModel (9 / 10) (1 / 2) (891 / 250) (1 / 50) 2 (52 / 125) (1 / 100) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- After-tax income in `modelE`. -/
theorem modelE_psi (k : ℝ) :
    modelE.psi k = 1 / 50 + 891 / 250 * k / (1 + k) - 1 / 2 * k * (891 / 250 / (1 + k) ^ 2) :=
  rfl

/-- The marginal product in `modelE`. -/
theorem modelE_f' (k : ℝ) : modelE.f' k = 891 / 250 / (1 + k) ^ 2 := rfl

/-- The discount factor in `modelE`. -/
theorem modelE_β : modelE.β = 9 / 10 := rfl

/-- The tax rate in `modelE`. -/
theorem modelE_θ : modelE.θ = 1 / 2 := rfl

/-- In `modelE`, `ψ(ψ(0)) ≤ k*`: after-tax income from the capital stock `ψ(0)` is still below
the steady state. -/
theorem modelE_psi_psi_le : modelE.psi (modelE.psi 0) ≤ modelE.kstar := by
  have hψ0 : modelE.psi 0 = 1 / 50 := by rw [modelE_psi]; norm_num
  rw [hψ0]
  set x := modelE.psi (1 / 50) with hxdef
  have hx : x ≤ 1 / 10 := by rw [hxdef, modelE_psi]; norm_num
  have hx0 : 0 ≤ x := (modelE.psi_pos (by norm_num)).le
  by_contra hlt
  have h := modelE.euler_lt_one (lt_of_not_ge hlt)
  rw [modelE_β, modelE_θ, modelE_f'] at h
  have hsq : (1 + x) ^ 2 ≤ 121 / 100 := by nlinarith
  have hpos : 0 < (1 + x) ^ 2 := by positivity
  set z := 891 / 250 / (1 + x) ^ 2 with hz
  have h2 : 891 / 250 / (121 / 100) ≤ z := div_le_div_of_nonneg_left (by norm_num) hpos hsq
  norm_num at h2
  linarith

/-- **Correction to Exercise 18.5** (NOTE 18.3-E). The book's claim that (7) defines `T` on `F`
— for every `h ∈ F` and `k ∈ K` there is a `y ∈ [0, ψ(k))` with positive next-period consumption
solving (7) — is false: in `modelE` it fails for `h = min{ψ, k*} ∈ F` at `k = 0`. -/
theorem ex_18_5_counterexample :
    ¬ ∀ (M : GlobalModel) (h : Icc 0 M.kbar →ᵇ ℝ), h ∈ M.F → ∀ k : Icc 0 M.kbar,
      ∃ y, 0 ≤ y ∧ y < M.psi k ∧ 0 < M.psi y - M.ext h y ∧
        M.U' (M.psi k - y) = M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - M.ext h y) := by
  intro hall
  obtain ⟨-, hno, -⟩ := modelE.ex_18_5_counterexample_of modelE_psi_psi_le
  have hmem := GlobalModel.toBCF_mem_F modelE.isInF_hE
  obtain ⟨y, hy0, hyP, hc, heq⟩ := hall modelE _ hmem ⟨0, le_rfl, modelE.kbar_pos.le⟩
  have hyK : y ∈ Icc 0 modelE.kbar :=
    ⟨hy0, hyP.le.trans (modelE.psi_le_kbar ⟨le_rfl, modelE.kbar_pos.le⟩)⟩
  rw [GlobalModel.ext_toBCF _ _ _ hyK] at hc heq
  exact hno ⟨y, hy0, hyP, hc, heq⟩

/-! ### The proof of Proposition 18.5: `A = f′(0)` is not a Lipschitz constant for `ψ` -/

/-- The integrand `φ(s) = 1/(1 + s⁸)`: flat near `0`, then dropping steeply around `s = 1`. -/
noncomputable def phiL (s : ℝ) : ℝ := 1 / (1 + s ^ 8)

/-- `Φ(k) = ∫₀ᵏ φ`. -/
noncomputable def PhiL (k : ℝ) : ℝ := ∫ s in (0 : ℝ)..k, phiL s

/-- The technology `f(k) = 3 + 4 Φ(k)` of `modelL`. -/
noncomputable def fL (k : ℝ) : ℝ := 3 + 4 * PhiL k

/-- After-tax income `ψ(k) = f(k) − (1/2) k f′(k)` of `modelL`. -/
noncomputable def psiL (k : ℝ) : ℝ := fL k - 1 / 2 * k * (4 * phiL k)

/-- `φ > 0`. -/
theorem phiL_pos (s : ℝ) : 0 < phiL s := by unfold phiL; positivity

/-- `φ ≤ 1`. -/
theorem phiL_le_one (s : ℝ) : phiL s ≤ 1 := by
  unfold phiL
  rw [div_le_one (by positivity)]
  nlinarith [pow_nonneg (sq_nonneg s) 4]

/-- `φ` is continuous. -/
theorem continuous_phiL : Continuous phiL :=
  continuous_const.div (continuous_const.add (continuous_pow 8)) fun s => by positivity

/-- `φ` is strictly decreasing on `[0, ∞)`. -/
theorem phiL_strictAntiOn : StrictAntiOn phiL (Ici 0) := by
  intro x hx y _ hxy
  have h : x ^ 8 < y ^ 8 := pow_lt_pow_left₀ hxy (mem_Ici.1 hx) (by norm_num)
  unfold phiL
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- `Φ′ = φ`. -/
theorem hasDerivAt_PhiL (k : ℝ) : HasDerivAt PhiL (phiL k) k :=
  (continuous_phiL.integral_hasStrictDerivAt 0 k).hasDerivAt

/-- `f′ = 4 φ`. -/
theorem hasDerivAt_fL (k : ℝ) : HasDerivAt fL (4 * phiL k) k := by
  have := ((hasDerivAt_PhiL k).const_mul 4).const_add 3
  exact this

/-- `φ′(k) = −8k⁷/(1 + k⁸)²`. -/
theorem hasDerivAt_phiL (k : ℝ) : HasDerivAt phiL (-(8 * k ^ 7) / (1 + k ^ 8) ^ 2) k := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + s ^ 8) (8 * k ^ 7) k := by
    simpa using (hasDerivAt_pow 8 k).const_add 1
  have h2 := (hasDerivAt_const k (1 : ℝ)).div h1 (by positivity : (1 + k ^ 8) ≠ 0)
  convert h2 using 1
  · ext s; simp [phiL]
  · ring

/-- `ψ′(k) = 2/(1 + k⁸) + 16k⁸/(1 + k⁸)²` in `modelL`. -/
theorem hasDerivAt_psiL (k : ℝ) :
    HasDerivAt psiL (2 / (1 + k ^ 8) + 16 * k ^ 8 / (1 + k ^ 8) ^ 2) k := by
  have h1 := hasDerivAt_fL k
  have h2 := (((hasDerivAt_id k).const_mul (1 / 2 : ℝ)).mul
    ((hasDerivAt_phiL k).const_mul (4 : ℝ)))
  have h3 := h1.sub h2
  convert h3 using 1
  · ext x; simp [psiL]
  · simp only [phiL, id]
    field_simp
    ring

/-- `ψ` is continuous in `modelL`. -/
theorem continuous_psiL : Continuous psiL :=
  continuous_iff_continuousAt.2 fun k => (hasDerivAt_psiL k).continuousAt

/-- `Φ(k) ≥ k φ(k)` for `k ≥ 0` (`φ` is decreasing). -/
theorem mul_phiL_le_PhiL {k : ℝ} (hk : 0 ≤ k) : k * phiL k ≤ PhiL k := by
  have h := intervalIntegral.integral_mono_on hk (intervalIntegrable_const (c := phiL k))
    (continuous_phiL.intervalIntegrable (μ := MeasureTheory.volume) 0 k) fun x hx =>
      phiL_strictAntiOn.antitoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hk) hx.2
  simpa [intervalIntegral.integral_const, PhiL] using h

/-- `ψ(k) ≥ 3` for `k ≥ 0` in `modelL`. -/
theorem three_le_psiL {k : ℝ} (hk : 0 ≤ k) : 3 ≤ psiL k := by
  have h1 := mul_phiL_le_PhiL hk
  have h2 : 0 ≤ k * phiL k := mul_nonneg hk (phiL_pos k).le
  simp only [psiL, fL]
  nlinarith

/-- `ψ(20) < 20` in `modelL`. -/
theorem psiL_twenty_lt : psiL 20 < 20 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable phiL MeasureTheory.volume a b :=
    continuous_phiL.intervalIntegrable
  have h1 : ∫ s in (0 : ℝ)..2, phiL s ≤ ∫ s in (0 : ℝ)..2, (1 : ℝ) :=
    intervalIntegral.integral_mono_on (by norm_num) (hi 0 2) intervalIntegrable_const
      fun s _ => phiL_le_one s
  have h2 : ∫ s in (2 : ℝ)..20, phiL s ≤ ∫ s in (2 : ℝ)..20, (1 / 257 : ℝ) := by
    refine intervalIntegral.integral_mono_on (by norm_num) (hi 2 20) intervalIntegrable_const
      fun s hs => ?_
    have : (2 : ℝ) ^ 8 ≤ s ^ 8 := pow_le_pow_left₀ (by norm_num) hs.1 8
    unfold phiL
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    norm_num at this ⊢
    linarith
  have h3 := intervalIntegral.integral_add_adjacent_intervals (hi 0 2) (hi 2 20)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h1 h2
  have h4 : 0 ≤ 20 * phiL 20 := mul_nonneg (by norm_num) (phiL_pos 20).le
  simp only [psiL, fL, PhiL]
  rw [← h3]
  nlinarith

/-- `ψ(k) − k` is strictly decreasing on `[2, ∞)` in `modelL` (`ψ′ < 1` there). -/
theorem psiL_sub_strictAntiOn : StrictAntiOn (fun k => psiL k - k) (Ici 2) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 2)
    (continuous_psiL.sub continuous_id).continuousOn fun x hx => ?_
  rw [interior_Ici] at hx
  have hd : HasDerivAt (fun k => psiL k - k)
      (2 / (1 + x ^ 8) + 16 * x ^ 8 / (1 + x ^ 8) ^ 2 - 1) x :=
    (hasDerivAt_psiL x).sub (hasDerivAt_id' x)
  rw [hd.deriv]
  have ht : (2 : ℝ) ^ 8 ≤ x ^ 8 := pow_le_pow_left₀ (by norm_num) (le_of_lt hx) 8
  set t := x ^ 8
  have hpos : 0 < 1 + t := by positivity
  have : 2 / (1 + t) + 16 * t / (1 + t) ^ 2 = (2 * (1 + t) + 16 * t) / (1 + t) ^ 2 := by
    field_simp
  rw [this, sub_neg, div_lt_one (by positivity)]
  norm_num at ht
  nlinarith

/-- `ψ(k) = k` has a root in `[2, 20]` in `modelL`. -/
theorem exists_kbarL : ∃ k ∈ Icc (2 : ℝ) 20, psiL k - k = 0 := by
  have h := intermediate_value_Icc' (by norm_num : (2 : ℝ) ≤ 20)
    (continuous_psiL.sub continuous_id).continuousOn
  have h2 : 0 ∈ Icc (psiL 20 - 20) (psiL 2 - 2) :=
    ⟨by linarith [psiL_twenty_lt], by linarith [three_le_psiL (by norm_num : (0 : ℝ) ≤ 2)]⟩
  obtain ⟨k, hk, hk0⟩ := h h2
  exact ⟨k, hk, hk0⟩

/-- The capital stock `k̄ ∈ [2, 20]` of `modelL`. -/
noncomputable def kbarL : ℝ := Classical.choose exists_kbarL

/-- `2 ≤ k̄ ≤ 20` in `modelL`. -/
theorem kbarL_mem : kbarL ∈ Icc (2 : ℝ) 20 := (Classical.choose_spec exists_kbarL).1

/-- `ψ(k̄) = k̄` in `modelL`. -/
theorem psiL_kbarL : psiL kbarL - kbarL = 0 := (Classical.choose_spec exists_kbarL).2

/-- The `C²` property of the technology of `modelL`. -/
theorem contDiff_fL : ContDiff ℝ 2 fL := by
  have hd : deriv fL = fun k => 4 * (1 / (1 + k ^ 8)) :=
    funext fun k => (hasDerivAt_fL k).deriv
  have h1 : ContDiff ℝ 1 (fun k : ℝ => 4 * (1 / (1 + k ^ 8))) :=
    contDiff_const.mul (contDiff_const.div (contDiff_const.add (contDiff_id.pow 8))
      fun x => by positivity)
  change ContDiff ℝ (1 + 1) fL
  exact contDiff_succ_iff_deriv.2 ⟨fun k => (hasDerivAt_fL k).differentiableAt,
    fun h => absurd h (by simp), hd ▸ h1⟩

/-- **The model `modelL`.** `U = √`, `f(k) = 3 + 4 ∫₀ᵏ ds/(1 + s⁸)` (so `f′(k) = 4/(1 + k⁸)`,
`A = f′(0) = 4`), `θ = 1/2`, `β = 9/10`, `k̄ ∈ [2, 20]` the root of `ψ(k) = k`. -/
noncomputable def modelL : GlobalModel where
  β := 9 / 10
  θ := 1 / 2
  U := fun c => √c
  U' := fun c => 1 / (2 * √c)
  f := fL
  f' := fun k => 4 * phiL k
  kbar := kbarL
  β_pos := by norm_num
  β_lt_one := by norm_num
  U_cont := Real.continuous_sqrt.continuousOn
  U_contDiff := sqrt_contDiffOn
  U_strictMono := sqrt_strictMonoOn
  U_strictConcave := Real.strictConcaveOn_sqrt
  U_deriv _ hc := sqrt_hasDerivAt hc
  θ_pos := by norm_num
  θ_lt_one := by norm_num
  f_cont := contDiff_fL.continuous.continuousOn
  f_contDiff := contDiff_fL.contDiffOn
  f_strictMono := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) contDiff_fL.continuous.continuousOn
      fun x _ => ?_
    rw [(hasDerivAt_fL x).deriv]
    exact mul_pos (by norm_num) (phiL_pos x)
  f_strictConcave := by
    refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
      contDiff_fL.continuous.continuousOn ?_
    rw [interior_Ici]
    intro x hx y hy hxy
    rw [(hasDerivAt_fL x).deriv, (hasDerivAt_fL y).deriv]
    exact mul_lt_mul_of_pos_left (phiL_strictAntiOn (mem_Ici.2 (le_of_lt hx))
      (mem_Ici.2 (le_of_lt hy)) hxy) (by norm_num)
  f_deriv k _ := hasDerivAt_fL k
  f_zero_pos := by simp [fL, PhiL]
  f'_zero := by simp [phiL]; norm_num
  kbar_pos := by linarith [kbarL_mem.1]
  psi_gt k hk0 hk := by
    change k < psiL k
    rcases le_or_gt k 2 with h2 | h2
    · linarith [three_le_psiL hk0.le]
    · have := psiL_sub_strictAntiOn (mem_Ici.2 h2.le) (mem_Ici.2 kbarL_mem.1) hk
      simp only at this
      linarith [psiL_kbarL]
  psi_lt k hk := by
    change psiL k < k
    have := psiL_sub_strictAntiOn (mem_Ici.2 kbarL_mem.1) (mem_Ici.2 (kbarL_mem.1.trans hk.le)) hk
    simp only at this
    linarith [psiL_kbarL]
  f'_contAt_zero := (continuous_const.mul continuous_phiL).continuousWithinAt
  U'_inada := sqrt_inada

/-- **Correction to the proof of Proposition 18.5** (p. 557). The book bounds
`|ψ(k′) − ψ(k)| ≤ A |k′ − k|` on `K` with `A = f′(0)` (Assumption 18.2). This is false: in
`modelL`, `A = 4` but `ψ(1) − ψ(9/10) > 4 · (1 − 9/10)`, because `ψ′ = (1 − θ) f′ − θ k f″` and
`−θ k f″` is large where `f′` drops steeply. -/
theorem prop_18_5_bound_counterexample :
    ¬ ∀ (M : GlobalModel) (k k' : ℝ), k ∈ Icc 0 M.kbar → k' ∈ Icc 0 M.kbar →
      |M.psi k' - M.psi k| ≤ M.f' 0 * |k' - k| := by
  intro hall
  have hkb := kbarL_mem.1
  have h := hall modelL (9 / 10) 1 ⟨by norm_num, by change (9 / 10 : ℝ) ≤ kbarL; linarith⟩
    ⟨by norm_num, by change (1 : ℝ) ≤ kbarL; linarith⟩
  change |psiL 1 - psiL (9 / 10)| ≤ 4 * phiL 0 * |1 - 9 / 10| at h
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope psiL
    (fun k => 2 / (1 + k ^ 8) + 16 * k ^ 8 / (1 + k ^ 8) ^ 2) (by norm_num : (9 / 10 : ℝ) < 1)
    continuous_psiL.continuousOn fun x _ => hasDerivAt_psiL x
  have ht1 : (9 / 10 : ℝ) ^ 8 < c ^ 8 := pow_lt_pow_left₀ hc.1 (by norm_num) (by norm_num)
  have ht2 : c ^ 8 < 1 := pow_lt_one₀ (by linarith [hc.1]) hc.2 (by norm_num)
  set t := c ^ 8
  have hpos : 0 < 1 + t := by positivity
  have hgt : 4 < 2 / (1 + t) + 16 * t / (1 + t) ^ 2 := by
    have : 2 / (1 + t) + 16 * t / (1 + t) ^ 2 = (2 * (1 + t) + 16 * t) / (1 + t) ^ 2 := by
      field_simp
    rw [this, lt_div_iff₀ (by positivity)]
    norm_num at ht1
    nlinarith
  rw [hslope] at hgt
  have hφ : phiL 0 = 1 := by simp [phiL]
  rw [hφ] at h
  rw [lt_div_iff₀ (by norm_num)] at hgt
  have := le_abs_self (psiL 1 - psiL (9 / 10))
  norm_num at h
  linarith

end StokeyLucasPrescott.EquilibriaWithDistortions
