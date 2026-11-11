/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Fiscal stimulus: the neoclassical benchmark and monopolistic competition

Miao, §19.3, pp. 640–643, (19.36)–(19.43) (following Woodford 2011).

The household maximises `Σ βᵗ[u(C_t) − v(N_t)]` (19.36), output is `Y_t = f(N_t)` (19.37) and
`C_t + G_t = Y_t` (19.38). With `f` a bijection of `ℝ` with inverse `f⁻¹` and `f' > 0`, the
disutility of producing `Y` is `ṽ(Y) = v(f⁻¹(Y))` (`fs_vtilde`).

* `fs_vtilde_hasDerivAt`, `fs_vtilde_deriv2`: `ṽ'(Y) = v'(f⁻¹Y)/f'(f⁻¹Y)` and
  `ṽ'' = (v''f' − v'f'')/f'³`, so `ṽ'' > 0` when `v'' ≥ 0` and `f'' < 0` (`fs_vtilde_deriv2_pos`).
* (19.39) ⟹ (19.40): `eq_19_40` (the book writes `ṽ(Y_t)` for the derivative `ṽ'(Y_t)`).
* (19.41): the steady-state multiplier `dY/dG = η_u/(η_u + η_v) ∈ (0, 1)`, proved by implicit
  differentiation of any differentiable solution path of `u'(Y − G) = μṽ'(Y)` (`eq_19_41`,
  general wedge `μ > 0`, so also the monopolistic case (19.43); `fs_multiplier_formula` without
  sign conditions).
* The markup `μ = ε/(ε − 1)` from the monopolist's first-order condition (`fs_markup_foc`),
  (19.42) (`eq_19_42`) and (19.43) (`eq_19_43`).
* An endogenous wedge falling with `G` raises the multiplier (`fs_endogenous_wedge`).

**Correction.** The book assumes `v'' < 0`; then `η_v` can be negative and the multiplier can
exceed one (`fs_eq_19_41_vpp_neg`: `u = log`, `f = id`, `v = 2 log(1 + N)` gives `dY/dG = 2`).
The correct assumption is `v'' > 0` (convex disutility of work), or `v'' ≥ 0` with `f'' < 0`.
-/

namespace Miao.NewKeynesian

open Filter Topology

/-- The disutility of producing output `Y`: `ṽ(Y) = v(f⁻¹(Y))` (Miao, (19.40), p. 641). -/
def fs_vtilde (v finv : ℝ → ℝ) : ℝ → ℝ := fun Y => v (finv Y)

/-- The (positive) elasticity of marginal utility `η_u = −Ȳu''/u'` (Miao, p. 641). -/
noncomputable def fs_etaU (Y u1 u2 : ℝ) : ℝ := -Y * u2 / u1

/-- The elasticity `η_v = Ȳṽ''/ṽ'` (Miao, p. 641). -/
noncomputable def fs_etaV (Y vt1 vt2 : ℝ) : ℝ := Y * vt2 / vt1

/-- The neoclassical multiplier `Γ = η_u/(η_u + η_v)` (Miao, (19.41), p. 641). -/
noncomputable def fs_Gamma (ηu ηv : ℝ) : ℝ := ηu / (ηu + ηv)

/-- Miao, p. 641: `Γ > 0` for `η_u, η_v > 0`. -/
theorem fs_Gamma_pos {ηu ηv : ℝ} (hu : 0 < ηu) (hv : 0 < ηv) : 0 < fs_Gamma ηu ηv :=
  div_pos hu (by linarith)

/-- Miao, p. 641: `Γ < 1` for `η_u, η_v > 0` (government purchases crowd out consumption). -/
theorem fs_Gamma_lt_one {ηu ηv : ℝ} (hu : 0 < ηu) (hv : 0 < ηv) : fs_Gamma ηu ηv < 1 := by
  unfold fs_Gamma
  rw [div_lt_one (by linarith)]
  linarith

/-- Miao, (19.40), p. 641: if `f` is a bijection with inverse `finv` and `f' > 0`, then the
inverse is differentiable and `ṽ'(Y) = v'(f⁻¹(Y))/f'(f⁻¹(Y))`. -/
theorem fs_vtilde_hasDerivAt {v v1 f f1 finv : ℝ → ℝ} (hv : ∀ x, HasDerivAt v (v1 x) x)
    (hf : ∀ x, HasDerivAt f (f1 x) x) (hf1 : ∀ x, 0 < f1 x) (hfg : ∀ y, f (finv y) = y)
    (hgf : ∀ x, finv (f x) = x) (Y : ℝ) :
    HasDerivAt (fs_vtilde v finv) (v1 (finv Y) / f1 (finv Y)) Y := by
  have hmono : StrictMono f := strictMono_of_deriv_pos fun x => by rw [(hf x).deriv]; exact hf1 x
  have hgmono : Monotone finv := by
    intro a b hab
    by_contra h
    push Not at h
    have := hmono h
    rw [hfg, hfg] at this
    linarith
  have hgsurj : Function.Surjective finv := fun x => ⟨f x, hgf x⟩
  have hgc : Continuous finv := hgmono.continuous_of_surjective hgsurj
  have hg : HasDerivAt finv (f1 (finv Y))⁻¹ Y :=
    HasDerivAt.of_local_left_inverse hgc.continuousAt (hf (finv Y)) (hf1 _).ne'
      (Eventually.of_forall hfg)
  have := (hv (finv Y)).comp Y hg
  rw [div_eq_mul_inv]
  exact this

/-- Miao, (19.40)–(19.41), p. 641: the second derivative of `ṽ`. If `ṽ'(Y) = v'(g Y)/f'(g Y)`
with `g = f⁻¹` differentiable with derivative `1/f'(g Y)`, then
`ṽ''(Y) = (v''f' − v'f'')/f'³` evaluated at `N = f⁻¹(Y)`. -/
theorem fs_vtilde_deriv2 {v1 v2 f1 f2 finv : ℝ → ℝ} {Y : ℝ}
    (hv1 : HasDerivAt v1 (v2 (finv Y)) (finv Y)) (hf1 : HasDerivAt f1 (f2 (finv Y)) (finv Y))
    (hg : HasDerivAt finv (f1 (finv Y))⁻¹ Y) (hpos : 0 < f1 (finv Y)) :
    HasDerivAt (fun y => v1 (finv y) / f1 (finv y))
      ((v2 (finv Y) * f1 (finv Y) - v1 (finv Y) * f2 (finv Y)) / f1 (finv Y) ^ 3) Y := by
  have h1 := hv1.comp Y hg
  have h2 := hf1.comp Y hg
  refine (h1.div h2 hpos.ne').congr_deriv ?_
  simp only [Function.comp_apply]
  field_simp

/-- Miao, p. 641: `η_v > 0`, i.e. `ṽ'' > 0`, when `v' > 0`, `v'' ≥ 0`, `f' > 0` and `f'' < 0`
(the book's `v'' < 0` is a misprint, see `fs_eq_19_41_vpp_neg`). -/
theorem fs_vtilde_deriv2_pos {v1N v2N f1N f2N : ℝ} (hv1 : 0 < v1N) (hv2 : 0 ≤ v2N)
    (hf1 : 0 < f1N) (hf2 : f2N < 0) : 0 < (v2N * f1N - v1N * f2N) / f1N ^ 3 := by
  apply div_pos _ (by positivity)
  nlinarith [mul_nonneg hv2 hf1.le, mul_pos hv1 (neg_pos.2 hf2)]

/-- Miao, (19.39) ⟹ (19.40), p. 641: in a competitive equilibrium (`v'(N)/u'(C) = W/P`,
`f'(N) = W/P`), with `Y = f(N)` and `C + G = Y`, `u'(Y − G) = v'(f⁻¹Y)/f'(f⁻¹Y)`, which is
`ṽ'(Y)` by `fs_vtilde_hasDerivAt`. -/
theorem eq_19_40 {u1 v1 f f1 finv : ℝ → ℝ} {N C G Y w : ℝ} (hY : Y = f N) (hC : C + G = Y)
    (hlab : v1 N / u1 C = w) (hfirm : f1 N = w) (hu : u1 C ≠ 0) (hv : v1 N ≠ 0)
    (hgf : finv (f N) = N) : u1 (Y - G) = v1 (finv Y) / f1 (finv Y) := by
  have hCY : Y - G = C := by linarith
  rw [hCY, hY, hgf, hfirm, ← hlab]
  field_simp

/-- Miao, (19.41), p. 641, without sign conditions: if `Ysol` is a solution path of the
steady-state condition `u'(Y − G) = μṽ'(Y)` near `Ḡ`, differentiable at `Ḡ`, then
`(u'' − μṽ'')·dY/dG = u''`. -/
theorem fs_multiplier_formula {u1 vt1 Ysol : ℝ → ℝ} {Gb Y' u2 vt2 μ : ℝ}
    (hY : HasDerivAt Ysol Y' Gb) (heq : ∀ᶠ G in 𝓝 Gb, u1 (Ysol G - G) = μ * vt1 (Ysol G))
    (hu : HasDerivAt u1 u2 (Ysol Gb - Gb)) (hvt : HasDerivAt vt1 vt2 (Ysol Gb)) :
    (u2 - μ * vt2) * Y' = u2 := by
  have hC : HasDerivAt (fun G => Ysol G - G) (Y' - 1) Gb := hY.sub (hasDerivAt_id Gb)
  have h1 := hu.comp (h := fun G => Ysol G - G) Gb hC
  have h2 := (hvt.comp Gb hY).const_mul μ
  have hF := h1.sub h2
  have h0 : HasDerivAt (fun G => u1 (Ysol G - G) - μ * vt1 (Ysol G)) 0 Gb := by
    apply (hasDerivAt_const Gb (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [heq] with G hG
    simp [hG]
  have := hF.unique h0
  linear_combination this

/-- Miao, (19.41) and (19.43), pp. 641–643: the steady-state fiscal multiplier. Let `Ysol` be a
solution path of `u'(Y − G) = μṽ'(Y)` (`μ = 1`: (19.40); `μ > 0` the efficiency wedge: (19.43)),
differentiable at `Ḡ`, with `Ȳ = Ysol Ḡ > 0`, `u' > 0`, `u'' < 0`, `ṽ'' > 0`. Then
`dY/dG = η_u/(η_u + η_v)`, and `0 < dY/dG < 1`. -/
theorem eq_19_41 {u1 vt1 Ysol : ℝ → ℝ} {Gb Y' u2 vt2 μ : ℝ}
    (hY : HasDerivAt Ysol Y' Gb) (heq : ∀ᶠ G in 𝓝 Gb, u1 (Ysol G - G) = μ * vt1 (Ysol G))
    (hu : HasDerivAt u1 u2 (Ysol Gb - Gb)) (hvt : HasDerivAt vt1 vt2 (Ysol Gb))
    (hYb : 0 < Ysol Gb) (hu1 : 0 < u1 (Ysol Gb - Gb)) (hu2 : u2 < 0) (hvt2 : 0 < vt2)
    (hμ : 0 < μ) :
    Y' = fs_Gamma (fs_etaU (Ysol Gb) (u1 (Ysol Gb - Gb)) u2)
        (fs_etaV (Ysol Gb) (vt1 (Ysol Gb)) vt2) ∧ 0 < Y' ∧ Y' < 1 := by
  have hf := fs_multiplier_formula hY heq hu hvt
  have hss : u1 (Ysol Gb - Gb) = μ * vt1 (Ysol Gb) := heq.self_of_nhds
  have hvt1 : 0 < vt1 (Ysol Gb) := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hμ.le h]
  have hden : u2 - μ * vt2 < 0 := by nlinarith [mul_pos hμ hvt2]
  have hY' : Y' = u2 / (u2 - μ * vt2) := by
    rw [eq_div_iff hden.ne]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hY']
    unfold fs_Gamma fs_etaU fs_etaV
    rw [hss]
    have hne2 : -u2 + μ * vt2 ≠ 0 := by linarith
    have hne1 : u2 - μ * vt2 ≠ 0 := hden.ne
    field_simp
    ring
  · rw [hY']
    exact div_pos_of_neg_of_neg hu2 hden
  · rw [hY', div_lt_one_of_neg hden]
    nlinarith [mul_pos hμ hvt2]

/-- Miao, p. 642: profit maximisation of a monopolist facing demand with elasticity `ε > 1`.
The derivative of the profit `(p − m)p^{−ε}` (real price `p`, real marginal cost `m`) is zero
iff `p = μm` with `μ = ε/(ε − 1)`. -/
theorem fs_markup_foc {ε m p : ℝ} (hε : 1 < ε) (hp : 0 < p) :
    HasDerivAt (fun q => (q - m) * q ^ (-ε))
      (p ^ (-ε) + (p - m) * (-ε * p ^ (-ε - 1))) p ∧
    (p ^ (-ε) + (p - m) * (-ε * p ^ (-ε - 1)) = 0 ↔ p = ε / (ε - 1) * m) := by
  refine ⟨?_, ?_⟩
  · have h := Real.hasDerivAt_rpow_const (p := -ε) (Or.inl hp.ne')
    refine (((hasDerivAt_id p).sub_const m).mul h).congr_deriv ?_
    simp
  · have hpe : p ^ (-ε - 1) = p ^ (-ε) / p := by
      rw [Real.rpow_sub hp, Real.rpow_one]
    have hpos : 0 < p ^ (-ε) := Real.rpow_pos_of_pos hp _
    have hε1 : ε - 1 ≠ 0 := by linarith
    have key : p ^ (-ε) + (p - m) * (-ε * p ^ (-ε - 1)) =
        p ^ (-ε) * ((1 - ε) * p + ε * m) / p := by
      rw [hpe]
      field_simp
      ring
    rw [key]
    constructor
    · intro h
      have h2 : (1 - ε) * p + ε * m = 0 := by
        rcases div_eq_zero_iff.1 h with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · exact absurd h4 hpos.ne'
          · exact h4
        · exact absurd h3 hp.ne'
      field_simp
      linarith
    · intro h
      have h2 : (1 - ε) * p + ε * m = 0 := by
        rw [h]
        field_simp
        ring
      rw [h2]
      simp

/-- Miao, (19.42), p. 642: the real price is the markup over real marginal cost, so real marginal
cost is `1/μ`: `W/(Pf'(N)) = 1/μ` iff `P = μW/f'(N)`. -/
theorem eq_19_42 {W P f1N μ : ℝ} (hP : 0 < P) (hf : 0 < f1N) (hμ : 0 < μ) :
    W / (P * f1N) = 1 / μ ↔ P = μ * W / f1N := by
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]
    have hW : W ≠ 0 := by
      rintro rfl
      simp at h
      linarith
    field_simp

/-- Miao, (19.43), p. 643: with the labour-supply condition `v'(N)/u'(C) = W/P` and the markup
(19.42) `W/P = f'(N)/μ`, `Y = f(N)`, `C + G = Y`: `u'(Y − G) = μ·v'(f⁻¹Y)/f'(f⁻¹Y)`, i.e.
`u'(Y − G) = μṽ'(Y)`. -/
theorem eq_19_43 {u1 v1 f f1 finv : ℝ → ℝ} {N C G Y w μ : ℝ} (hY : Y = f N) (hC : C + G = Y)
    (hlab : v1 N / u1 C = w) (hmark : w = f1 N / μ) (hu : u1 C ≠ 0) (hf1 : f1 N ≠ 0)
    (hμ : μ ≠ 0) (hgf : finv (f N) = N) :
    u1 (Y - G) = μ * (v1 (finv Y) / f1 (finv Y)) := by
  have hCY : Y - G = C := by linarith
  rw [hCY, hY, hgf]
  rw [hmark] at hlab
  field_simp at hlab ⊢
  linarith

/-- Miao, p. 643: an endogenous efficiency wedge. If the wedge `μ(G)` falls with government
purchases (`μ'(Ḡ) < 0`, e.g. sticky prices), the multiplier exceeds the fixed-wedge multiplier
`u''/(u'' − μ̄ṽ'') = η_u/(η_u + η_v)` of (19.43). -/
theorem fs_endogenous_wedge {u1 vt1 Ysol μf : ℝ → ℝ} {Gb Y' u2 vt2 μ' : ℝ}
    (hY : HasDerivAt Ysol Y' Gb) (hμf : HasDerivAt μf μ' Gb)
    (heq : ∀ᶠ G in 𝓝 Gb, u1 (Ysol G - G) = μf G * vt1 (Ysol G))
    (hu : HasDerivAt u1 u2 (Ysol Gb - Gb)) (hvt : HasDerivAt vt1 vt2 (Ysol Gb))
    (hu2 : u2 < 0) (hvt2 : 0 < vt2) (hμ : 0 < μf Gb) (hvt1 : 0 < vt1 (Ysol Gb)) :
    Y' = (u2 + μ' * vt1 (Ysol Gb)) / (u2 - μf Gb * vt2) ∧
      (μ' < 0 → u2 / (u2 - μf Gb * vt2) < Y') := by
  have hC : HasDerivAt (fun G => Ysol G - G) (Y' - 1) Gb := hY.sub (hasDerivAt_id Gb)
  have h1 := hu.comp (h := fun G => Ysol G - G) Gb hC
  have h2 := hμf.mul (hvt.comp Gb hY)
  have hF := h1.sub h2
  have h0 : HasDerivAt (fun G => u1 (Ysol G - G) - μf G * vt1 (Ysol G)) 0 Gb := by
    apply (hasDerivAt_const Gb (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [heq] with G hG
    simp [hG]
  have := hF.unique h0
  simp only [Function.comp_def] at this
  have hden : u2 - μf Gb * vt2 < 0 := by nlinarith [mul_pos hμ hvt2]
  have hY' : Y' = (u2 + μ' * vt1 (Ysol Gb)) / (u2 - μf Gb * vt2) := by
    rw [eq_div_iff hden.ne]
    linear_combination this
  refine ⟨hY', fun hneg => ?_⟩
  rw [hY', add_div]
  have : 0 < μ' * vt1 (Ysol Gb) / (u2 - μf Gb * vt2) :=
    div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hneg hvt1) hden
  linarith

/-- **Counterexample to the printed `v'' < 0`** (Miao, p. 640–641): with `u = log`, `f = id` and
the concave disutility `v(N) = 2 log(1 + N)` (`v' > 0`, `v'' < 0` on `N > −1`), the path
`Y(G) = 1 + 2G` solves (19.40) `u'(Y − G) = ṽ'(Y)` for `G > −1`, and `dY/dG = 2 > 1`:
the multiplier is not less than one. -/
theorem fs_eq_19_41_vpp_neg :
    (∀ N : ℝ, -1 < N → HasDerivAt (fun n => 2 * Real.log (1 + n)) (2 / (1 + N)) N ∧
      0 < 2 / (1 + N) ∧ HasDerivAt (fun n => 2 / (1 + n)) (-2 / (1 + N) ^ 2) N ∧
      -2 / (1 + N) ^ 2 < 0) ∧
    (∀ G : ℝ, -1 < G → 1 / ((1 + 2 * G) - G) = 2 / (1 + (1 + 2 * G))) ∧
    HasDerivAt (fun G : ℝ => 1 + 2 * G) 2 0 ∧ (1 : ℝ) < 2 := by
  refine ⟨fun N hN => ?_, fun G hG => ?_, ?_, by norm_num⟩
  · have h1 : 0 < 1 + N := by linarith
    refine ⟨?_, by positivity, ?_, ?_⟩
    · have := ((hasDerivAt_id' N).const_add 1).log h1.ne'
      convert this.const_mul 2 using 1
      ring
    · have := ((hasDerivAt_id N).const_add 1).inv h1.ne'
      convert this.const_mul 2 using 1
      · funext n
        simp [div_eq_mul_inv]
      · simp
        ring
    · have : 0 < (1 + N) ^ 2 := by positivity
      exact div_neg_of_neg_of_pos (by norm_num) this
  · have h1 : (1 + 2 * G) - G ≠ 0 := by linarith
    have h2 : 1 + (1 + 2 * G) ≠ 0 := by linarith
    field_simp
    ring
  · simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).const_add 1

end Miao.NewKeynesian
