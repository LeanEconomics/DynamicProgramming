import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import NeoclassicalGrowth.RMBasics
import DiscreteTime.GeneralSolow
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Calculus.Deriv.Slope
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Growth accounting

AKMM, §2.1.4, pp. 50–52, and the Cobb–Douglas remark of §2.1.6, p. 58. Time is continuous, as
in the book: output is `y(t) = F(k(t), ℓ(t), t)` with `F` Fréchet differentiable in
`(k, ℓ, t)`, constant returns to scale in `(k, ℓ)`, and factor prices equal to the marginal
products (the first-order conditions of `max F(k, ℓ, t) − rk − wℓ`).

* Per-capita output `y = Y/N = F(K/N, L/N)` under constant returns (p. 51, `ga_per_capita`), and
  competitive factor prices equal marginal products at a profit maximum (`ga_profit_foc`).
* **(2.1)** `ẏ/y = (∂F/∂t)/F + α k̇/k + (1 − α) ℓ̇/ℓ` with capital share `α = rk/y`, and labour's
  share is `1 − α = wℓ/y` (zero profits): `eq_2_1`. The chain rule gives
  `ẏ = F_k k̇ + F_ℓ ℓ̇ + F_t`; Euler's theorem for homogeneous functions is Miao's
  `rm_euler_homogeneous`, reused here.
* **(2.2)**, Hicks-neutral technology `F(k, ℓ, t) = z(t)G(k, ℓ)`: the Solow residual is `ż/z`
  (`eq_2_2`); `zG(k, ℓ) = G(zk, zℓ)` (footnote 8, `ga_hicks_neutral_common_factor`).
* **(2.3)**, labour-augmenting technology `F(k, ℓ, t) = G(k, z(t)ℓ)`: the residual is
  `(1 − α)ż/z` (`eq_2_3`). The derivation's intermediate identities
  `∂F/∂t = G₂ ℓ ż` and `G₂ = w/z` are proved (`ga_labour_augmenting_partials`).
* Cobb–Douglas `F = A k^α ℓ^{1−α}`: `F_k k/F = α` for all `(k, ℓ)` (`ga_cobbDouglas_share`).

**Departure.** On p. 52 the book writes `(∂F/∂t)dt = (∂F/∂ℓ)ℓ dz`, where `∂F/∂ℓ` must be read as
the partial of the time-independent `G` in its second argument (the book uses the letter `F` for
both functions). Read as the partial of `F(k, ℓ, t) = G(k, zℓ)` in `ℓ`, the identity is off by
the factor `z` (`ga_eq_2_3_partial_misreading`); see `docs/corrections.md`.
-/

namespace AKMM.Framework

/-- The linear map `(dk, dℓ, dt) ↦ a dk + b dℓ + c dt`: the derivative of `F(k, ℓ, t)` with
partials `F_k = a`, `F_ℓ = b`, `F_t = c`. -/
noncomputable def gaPartials (a b c : ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
    b • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
    c • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The value of `gaPartials` on a vector. -/
theorem ga_partials_apply (a b c : ℝ) (v : ℝ × ℝ × ℝ) :
    gaPartials a b c v = a * v.1 + b * v.2.1 + c * v.2.2 := by
  simp [gaPartials]

/-- The coordinate maps `(k, ℓ, t) ↦ ℓ` and `(k, ℓ, t) ↦ t` are differentiable. -/
theorem ga_hasFDerivAt_coords (x : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x ∧
      HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.2)
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x := by
  have h : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_snd
  exact ⟨h.fst, h.snd⟩

/-- AKMM, pp. 50–51: with constant returns, per-capita output is the production function of
per-capita inputs, `Y/N = F(K/N, L/N)` for population `N > 0`. -/
theorem ga_per_capita {F : ℝ → ℝ → ℝ} (hcrs : ∀ s a b, 0 < s → F (s * a) (s * b) = s * F a b)
    {N : ℝ} (hN : 0 < N) (K L : ℝ) : F K L / N = F (K / N) (L / N) := by
  have h := hcrs (1 / N) K L (one_div_pos.2 hN)
  rw [one_div_mul_eq_div, one_div_mul_eq_div, one_div_mul_eq_div] at h
  rw [h]

/-- AKMM, p. 51: the first-order conditions of the firm's problem
`max_{k, ℓ} F(k, ℓ, t) − r k − w ℓ`. If `(k, ℓ)` is a local maximum of profits and `F(·, ·, t)` is
differentiable there with partials `F_k, F_ℓ`, then `r = F_k` and `w = F_ℓ`. -/
theorem ga_profit_foc {G : ℝ → ℝ → ℝ} {k ℓ r w Fk Fl : ℝ}
    (hG : HasFDerivAt (fun q : ℝ × ℝ => G q.1 q.2)
      (Fk • ContinuousLinearMap.fst ℝ ℝ ℝ + Fl • ContinuousLinearMap.snd ℝ ℝ ℝ) (k, ℓ))
    (hmax : IsLocalMax (fun q : ℝ × ℝ => G q.1 q.2 - r * q.1 - w * q.2) (k, ℓ)) :
    r = Fk ∧ w = Fl := by
  have hd : HasFDerivAt (fun q : ℝ × ℝ => G q.1 q.2 - r * q.1 - w * q.2)
      ((Fk • ContinuousLinearMap.fst ℝ ℝ ℝ + Fl • ContinuousLinearMap.snd ℝ ℝ ℝ) -
        r • ContinuousLinearMap.fst ℝ ℝ ℝ - w • ContinuousLinearMap.snd ℝ ℝ ℝ) (k, ℓ) :=
    (hG.sub (hasFDerivAt_fst.const_mul r)).sub (hasFDerivAt_snd.const_mul w)
  have h0 := hmax.hasFDerivAt_eq_zero hd
  have h1 := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (1, 0)) h0
  have h2 := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (0, 1)) h0
  simp at h1 h2
  constructor <;> linarith

/-- AKMM, p. 51 (the algebra behind (2.1)): if `ẏ = F_t + F_k k̇ + F_ℓ ℓ̇` and output is exhausted
by factor payments, `y = F_k k + F_ℓ ℓ`, then
`ẏ/y = F_t/y + α k̇/k + (1 − α) ℓ̇/ℓ` with `α = F_k k/y`. -/
theorem ga_growth_identity {y k ℓ k' ℓ' Fk Fl Ft : ℝ} (hy : y ≠ 0) (hk : k ≠ 0) (hl : ℓ ≠ 0)
    (he : y = Fk * k + Fl * ℓ) :
    (Fk * k' + Fl * ℓ' + Ft) / y =
      Ft / y + Fk * k / y * (k' / k) + (1 - Fk * k / y) * (ℓ' / ℓ) := by
  have h1 : 1 - Fk * k / y = Fl * ℓ / y := by
    field_simp
    linarith
  rw [h1]
  field_simp
  ring

/-- AKMM, (2.1), p. 51: Solow's growth-accounting equation, in continuous time. Let
`y(t) = F(k(t), ℓ(t), t)` with `F` differentiable at `(k(t), ℓ(t), t)` with partials
`F_k, F_ℓ, F_t`, constant returns in `(k, ℓ)`, and competitive factor prices `r = F_k`,
`w = F_ℓ`. Then `ẏ = F_k k̇ + F_ℓ ℓ̇ + F_t`, labour's share is `1 − α = wℓ/y` with `α = rk/y`,
and `ẏ/y = (∂F/∂t)/F + α k̇/k + (1 − α) ℓ̇/ℓ`. -/
theorem eq_2_1 {F : ℝ → ℝ → ℝ → ℝ} {k ℓ : ℝ → ℝ} {t k' ℓ' Fk Fl Ft r w : ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) (gaPartials Fk Fl Ft)
      (k t, ℓ t, t))
    (hk : HasDerivAt k k' t) (hl : HasDerivAt ℓ ℓ' t)
    (hcrs : ∀ s, 0 < s → F (s * k t) (s * ℓ t) t = s * F (k t) (ℓ t) t)
    (hr : r = Fk) (hw : w = Fl)
    (hy : F (k t) (ℓ t) t ≠ 0) (hk0 : k t ≠ 0) (hl0 : ℓ t ≠ 0) :
    HasDerivAt (fun τ => F (k τ) (ℓ τ) τ) (Fk * k' + Fl * ℓ' + Ft) t ∧
      F (k t) (ℓ t) t = r * k t + w * ℓ t ∧
      1 - r * k t / F (k t) (ℓ t) t = w * ℓ t / F (k t) (ℓ t) t ∧
      (Fk * k' + Fl * ℓ' + Ft) / F (k t) (ℓ t) t =
        Ft / F (k t) (ℓ t) t + r * k t / F (k t) (ℓ t) t * (k' / k t) +
          (1 - r * k t / F (k t) (ℓ t) t) * (ℓ' / ℓ t) := by
  -- the chain rule along the path `τ ↦ (k τ, ℓ τ, τ)`
  have hp : HasDerivAt (fun τ => (k τ, ℓ τ, τ)) (k', ℓ', 1) t :=
    hk.prodMk (hl.prodMk (hasDerivAt_id t))
  have hd := hF.comp_hasDerivAt t hp
  rw [ga_partials_apply] at hd
  simp only [mul_one] at hd
  -- Euler's theorem for `F(·, ·, t)`, from Miao's `rm_euler_homogeneous`
  have hq : HasFDerivAt (fun q : ℝ × ℝ => ((q.1, q.2, t) : ℝ × ℝ × ℝ))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0)) (k t, ℓ t) :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_snd.prodMk (hasFDerivAt_const t _))
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => F q.1 q.2 t)
      (Fk • ContinuousLinearMap.fst ℝ ℝ ℝ + Fl • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (k t, ℓ t) := by
    have := hF.comp (k t, ℓ t) hq
    refine this.congr_fderiv ?_
    ext <;> simp [gaPartials]
  have he := Miao.NeoclassicalGrowth.rm_euler_homogeneous
    (F := fun a b => F a b t) hcrs h2
  subst hr hw
  refine ⟨hd, he, ?_, ga_growth_identity hy hk0 hl0 he⟩
  field_simp
  linarith

/-- AKMM, footnote 8, p. 52: with constant returns, a Hicks-neutral factor multiplies both
inputs, `zG(k, ℓ) = G(zk, zℓ)` for `z > 0`. -/
theorem ga_hicks_neutral_common_factor {G : ℝ → ℝ → ℝ}
    (hcrs : ∀ s a b, 0 < s → G (s * a) (s * b) = s * G a b) {z : ℝ} (hz : 0 < z) (a b : ℝ) :
    z * G a b = G (z * a) (z * b) :=
  (hcrs z a b hz).symm

/-- AKMM, (2.2), p. 52: Hicks-neutral technology `F(k, ℓ, t) = z(t)G(k, ℓ)` with `G`
time-independent, differentiable with partials `G_k, G_ℓ` and of constant returns. With
`r = zG_k`, `w = zG_ℓ` and `α = rk/y`, the Solow residual is `ż/z`:
`ẏ/y = ż/z + α k̇/k + (1 − α) ℓ̇/ℓ`. Derived from `eq_2_1`. -/
theorem eq_2_2 {G : ℝ → ℝ → ℝ} {z k ℓ : ℝ → ℝ} {t z' k' ℓ' Gk Gl r w : ℝ}
    (hG : HasFDerivAt (fun q : ℝ × ℝ => G q.1 q.2)
      (Gk • ContinuousLinearMap.fst ℝ ℝ ℝ + Gl • ContinuousLinearMap.snd ℝ ℝ ℝ) (k t, ℓ t))
    (hz : HasDerivAt z z' t) (hk : HasDerivAt k k' t) (hl : HasDerivAt ℓ ℓ' t)
    (hcrs : ∀ s, 0 < s → G (s * k t) (s * ℓ t) = s * G (k t) (ℓ t))
    (hr : r = z t * Gk) (hw : w = z t * Gl)
    (hz0 : z t ≠ 0) (hG0 : G (k t) (ℓ t) ≠ 0) (hk0 : k t ≠ 0) (hl0 : ℓ t ≠ 0) :
    HasDerivAt (fun τ => z τ * G (k τ) (ℓ τ))
        (z t * Gk * k' + z t * Gl * ℓ' + z' * G (k t) (ℓ t)) t ∧
      (z t * Gk * k' + z t * Gl * ℓ' + z' * G (k t) (ℓ t)) / (z t * G (k t) (ℓ t)) =
        z' / z t + r * k t / (z t * G (k t) (ℓ t)) * (k' / k t) +
          (1 - r * k t / (z t * G (k t) (ℓ t))) * (ℓ' / ℓ t) := by
  have hF : HasFDerivAt (fun p : ℝ × ℝ × ℝ => z p.2.2 * G p.1 p.2.1)
      (gaPartials (z t * Gk) (z t * Gl) (z' * G (k t) (ℓ t))) (k t, ℓ t, t) := by
    have h1 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => z p.2.2)
        ((z' • ContinuousLinearMap.id ℝ ℝ).comp
          ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
        (k t, ℓ t, t) := by
      have := hz.hasFDerivAt.comp (k t, ℓ t, t) (ga_hasFDerivAt_coords (k t, ℓ t, t)).2
      refine this.congr_fderiv ?_
      ext <;> simp
    have h2 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1)
        ((Gk • ContinuousLinearMap.fst ℝ ℝ ℝ + Gl • ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
            ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))
        (k t, ℓ t, t) := by
      have hf : HasFDerivAt (fun p : ℝ × ℝ × ℝ => ((p.1, p.2.1) : ℝ × ℝ))
          ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
            ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
          (k t, ℓ t, t) :=
        hasFDerivAt_fst.prodMk (ga_hasFDerivAt_coords (k t, ℓ t, t)).1
      exact hG.comp (k t, ℓ t, t) hf
    refine (h1.mul h2).congr_fderiv ?_
    ext <;> simp [gaPartials, mul_comm]
  have hcrsF : ∀ s, 0 < s → z t * G (s * k t) (s * ℓ t) = s * (z t * G (k t) (ℓ t)) := by
    intro s hs
    rw [hcrs s hs]
    ring
  obtain ⟨hd, -, -, hid⟩ := eq_2_1 (F := fun a b τ => z τ * G a b) hF hk hl hcrsF hr hw
    (mul_ne_zero hz0 hG0) hk0 hl0
  refine ⟨hd, ?_⟩
  rw [hid]
  congr 2
  field_simp

/-- AKMM, p. 52 (the derivation of (2.3)): for labour-augmenting technology
`F(k, ℓ, t) = G(k, z(t)ℓ)`, the partials of `F` at `(k, ℓ, t)` are `F_k = G₁`, `F_ℓ = zG₂` and
`F_t = G₂ ℓ ż`, with `G₁, G₂` the partials of `G` at `(k, zℓ)`. Hence, with `w = F_ℓ`,
`F_t = (w/z) ℓ ż`: the book's `∂F/∂ℓ` in "(∂F/∂t)dt = (∂F/∂ℓ)ℓ dz" is `G₂ = w/z`. -/
theorem ga_labour_augmenting_partials {G : ℝ → ℝ → ℝ} {z k ℓ : ℝ → ℝ} {t z' Gk Gl : ℝ}
    (hG : HasFDerivAt (fun q : ℝ × ℝ => G q.1 q.2)
      (Gk • ContinuousLinearMap.fst ℝ ℝ ℝ + Gl • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (k t, z t * ℓ t))
    (hz : HasDerivAt z z' t) (hz0 : z t ≠ 0) :
    HasFDerivAt (fun p : ℝ × ℝ × ℝ => G p.1 (z p.2.2 * p.2.1))
        (gaPartials Gk (z t * Gl) (Gl * ℓ t * z')) (k t, ℓ t, t) ∧
      Gl * ℓ t * z' = (z t * Gl) / z t * ℓ t * z' := by
  refine ⟨?_, by field_simp⟩
  have h1 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => z p.2.2)
      ((z' • ContinuousLinearMap.id ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
      (k t, ℓ t, t) := by
    have := hz.hasFDerivAt.comp (k t, ℓ t, t) (ga_hasFDerivAt_coords (k t, ℓ t, t)).2
    refine this.congr_fderiv ?_
    ext <;> simp
  have h2 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (k t, ℓ t, t) :=
    (ga_hasFDerivAt_coords (k t, ℓ t, t)).1
  have h3 := hG.comp (k t, ℓ t, t) ((hasFDerivAt_fst (p := (k t, ℓ t, t))).prodMk (h1.mul h2))
  refine h3.congr_fderiv ?_
  ext <;> simp [gaPartials] <;> ring

/-- AKMM, (2.3), p. 52: labour-augmenting technology `F(k, ℓ, t) = G(k, z(t)ℓ)`. With `G`
differentiable at `(k, zℓ)` with partials `G₁, G₂` and of constant returns, `r = G₁`,
`w = zG₂` and `α = rk/y`, the Solow residual is `(1 − α)ż/z`:
`ẏ/y = (1 − α)ż/z + α k̇/k + (1 − α) ℓ̇/ℓ`. Derived from `eq_2_1`. -/
theorem eq_2_3 {G : ℝ → ℝ → ℝ} {z k ℓ : ℝ → ℝ} {t z' k' ℓ' Gk Gl r w : ℝ}
    (hG : HasFDerivAt (fun q : ℝ × ℝ => G q.1 q.2)
      (Gk • ContinuousLinearMap.fst ℝ ℝ ℝ + Gl • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (k t, z t * ℓ t))
    (hz : HasDerivAt z z' t) (hk : HasDerivAt k k' t) (hl : HasDerivAt ℓ ℓ' t)
    (hcrs : ∀ s, 0 < s → G (s * k t) (s * (z t * ℓ t)) = s * G (k t) (z t * ℓ t))
    (hr : r = Gk) (hw : w = z t * Gl)
    (hz0 : z t ≠ 0) (hG0 : G (k t) (z t * ℓ t) ≠ 0) (hk0 : k t ≠ 0) (hl0 : ℓ t ≠ 0) :
    HasDerivAt (fun τ => G (k τ) (z τ * ℓ τ)) (Gk * k' + z t * Gl * ℓ' + Gl * ℓ t * z') t ∧
      (Gk * k' + z t * Gl * ℓ' + Gl * ℓ t * z') / G (k t) (z t * ℓ t) =
        (1 - r * k t / G (k t) (z t * ℓ t)) * (z' / z t) +
          r * k t / G (k t) (z t * ℓ t) * (k' / k t) +
          (1 - r * k t / G (k t) (z t * ℓ t)) * (ℓ' / ℓ t) := by
  obtain ⟨hF, -⟩ := ga_labour_augmenting_partials (ℓ := ℓ) hG hz hz0
  have hcrsF : ∀ s, 0 < s → G (s * k t) (z t * (s * ℓ t)) = s * G (k t) (z t * ℓ t) := by
    intro s hs
    rw [← hcrs s hs]
    ring_nf
  obtain ⟨hd, -, hshare, hid⟩ := eq_2_1 (F := fun a b τ => G a (z τ * b)) hF hk hl hcrsF hr hw
    hG0 hk0 hl0
  refine ⟨hd, ?_⟩
  rw [hid, hshare, hw]
  field_simp

/-- AKMM, p. 52 (checking the printed identity `(∂F/∂t)dt = (∂F/∂ℓ)ℓ dz`): if `∂F/∂ℓ` is read
as the partial of `F(k, ℓ, t) = G(k, zℓ)` in `ℓ`, i.e. `zG₂`, the identity fails. With
`G(a, b) = b`, `z(t) = 2t`, `ℓ = 1` at `t = 1`: `F_t = 2` but `F_ℓ ℓ ż = 4`. -/
theorem ga_eq_2_3_partial_misreading :
    HasFDerivAt (fun p : ℝ × ℝ × ℝ => (2 * p.2.2) * p.2.1)
        (gaPartials 0 2 2) ((1 : ℝ), (1 : ℝ), (1 : ℝ)) ∧
      (2 : ℝ) ≠ 2 * 1 * 2 := by
  refine ⟨?_, by norm_num⟩
  have h1 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => 2 * p.2.2)
      ((2 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      ((1 : ℝ), (1 : ℝ), (1 : ℝ)) :=
    (ga_hasFDerivAt_coords ((1 : ℝ), (1 : ℝ), (1 : ℝ))).2.const_mul 2
  have h2 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      ((1 : ℝ), (1 : ℝ), (1 : ℝ)) :=
    (ga_hasFDerivAt_coords ((1 : ℝ), (1 : ℝ), (1 : ℝ))).1
  refine (h1.mul h2).congr_fderiv ?_
  ext <;> simp [gaPartials]

/-- AKMM, p. 58: the Cobb–Douglas function `F(k, ℓ) = A k^α ℓ^{1−α}` has
`∂F/∂k = αA k^{α−1}ℓ^{1−α}` at `k > 0`. -/
theorem ga_cobbDouglas_hasDerivAt_k (A α : ℝ) {k : ℝ} (hk : 0 < k) (ℓ : ℝ) :
    HasDerivAt (fun x => A * x ^ α * ℓ ^ (1 - α)) (α * A * k ^ (α - 1) * ℓ ^ (1 - α)) k := by
  have h := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hk.ne')).const_mul A).mul_const
    (ℓ ^ (1 - α))
  convert h using 1
  ring

/-- AKMM, p. 58: for Cobb–Douglas `F(k, ℓ) = A k^α ℓ^{1−α}` with `A, k, ℓ > 0`, the capital
share under competitive pricing is `F_k k/F = α`, independent of `(k, ℓ)`. -/
theorem ga_cobbDouglas_share {A α k ℓ : ℝ} (hA : 0 < A) (hk : 0 < k) (hl : 0 < ℓ) :
    α * A * k ^ (α - 1) * ℓ ^ (1 - α) * k / (A * k ^ α * ℓ ^ (1 - α)) = α := by
  have h1 : k ^ (α - 1) * k = k ^ α := by
    rw [Real.rpow_sub_one hk.ne']
    field_simp
  have h2 : 0 < k ^ α := Real.rpow_pos_of_pos hk α
  have h3 : 0 < ℓ ^ (1 - α) := Real.rpow_pos_of_pos hl _
  rw [show α * A * k ^ (α - 1) * ℓ ^ (1 - α) * k = α * A * (k ^ (α - 1) * k) * ℓ ^ (1 - α)
    by ring, h1]
  field_simp

/-- AKMM, p. 58: Cobb–Douglas has constant returns to scale on the positive quadrant. -/
theorem ga_cobbDouglas_crs (A α : ℝ) {s k ℓ : ℝ} (hs : 0 < s) (hk : 0 < k) (hl : 0 < ℓ) :
    A * (s * k) ^ α * (s * ℓ) ^ (1 - α) = s * (A * k ^ α * ℓ ^ (1 - α)) := by
  rw [Real.mul_rpow hs.le hk.le, Real.mul_rpow hs.le hl.le]
  have : s ^ α * s ^ (1 - α) = s := by
    rw [← Real.rpow_add hs]
    simp
  linear_combination (A * k ^ α * ℓ ^ (1 - α)) * this

end AKMM.Framework

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The dynamic system: accumulation, balanced paths and the detrended Solow map

AKMM, §2.1.5, pp. 52–57. Time is discrete, as in the book.

* **(2.4)** `k_{t+1} = (1 − δ)k_t + i_t`, rewritten with the output growth rate `γ_t` as
  `(k_{t+1}/y_{t+1})(1 + γ_t) = (1 − δ)k_t/y_t + i_t/y_t` (`eq_2_4_ratio_form`).
* **Balanced paths** (`DynBalancedPath`): if capital and output grow at a common constant rate
  `γ` and `i_t/y_t = s`, then `k_t/y_t = s/(γ + δ)` (`dyn_capital_output_ratio`); investment
  then grows at `γ` too. Conversely a capital stock starting at that ratio grows at `γ`
  (`dyn_balanced_of_initial_ratio`). A concrete balanced path is `dyn_balancedPath_example`.
* **Detrending.** With constant hours `ℓ`, labour-augmenting progress and constant returns,
  `k_{t+1} = sF(k_t, (1 + γ)^t ℓ) + (1 − δ)k_t` becomes
  `(1 + γ)k̃_{t+1} = sF(k̃_t, ℓ) + (1 − δ)k̃_t` for `k̃_t = k_t/(1 + γ)^t`
  (`dyn_detrend_step`), which is EconomicGrowth's discrete-time Solow map
  `Solow1956.DiscreteTime.next (F · ℓ) s δ (1 + γ)`; the whole path is that map's orbit scaled
  by `(1 + γ)^t` (`dyn_detrended_path`).
* **The constant solution** `k̄` of `(1 + γ)k̄ = sF(k̄, ℓ) + (1 − δ)k̄` exists and is the unique
  positive one (`dyn_steady_existsUnique`); it is EconomicGrowth's `steady`. From `k̃_0 = k̄`,
  capital, investment and output grow at `γ` and `y_t = (1 + γ)^t F(k̄, ℓ)`
  (`dyn_balanced_growth_from_steady`), and `k/y = s/(γ + δ)` there.
* **Convergence** (asserted on p. 56, proved in Ch. 3): from any `k_0 > 0`, `k̃_t → k̄`
  monotonically and `k_t/y_t → s/(γ + δ)` (`dyn_convergence`), from EconomicGrowth's
  `general_solow` (Acemoglu Proposition 2.5 in discrete time).

The neoclassical assumptions on `F(·, ℓ)` are EconomicGrowth's `Technology`, and the parameter
restrictions its `Params s δ (1 + γ)`: `s > 0`, `δ ≤ 1`, `γ > −1` and `γ + δ > 0`. Uzawa's theorem
(p. 56, proved in the book's Appendix 3.A) is not formalised here.
-/

namespace AKMM.Framework

open Filter Topology Solow1956.Neoclassical Solow1956.DiscreteTime

/-- AKMM, p. 53: the accumulation equation (2.4) divided by output. If
`k_{t+1} = (1 − δ)k_t + i_t` and output grows at the net rate `γ_t`, `y_{t+1} = (1 + γ_t)y_t`,
with `y_t, y_{t+1} ≠ 0`, then `(k_{t+1}/y_{t+1})(1 + γ_t) = (1 − δ)k_t/y_t + i_t/y_t`. -/
theorem eq_2_4_ratio_form {k i y : ℕ → ℝ} {δ γt : ℝ} {t : ℕ}
    (h24 : k (t + 1) = (1 - δ) * k t + i t) (hy : y (t + 1) = (1 + γt) * y t)
    (hy0 : y t ≠ 0) (hy1 : y (t + 1) ≠ 0) :
    k (t + 1) / y (t + 1) * (1 + γt) = (1 - δ) * (k t / y t) + i t / y t := by
  have h1 : 1 + γt = y (t + 1) / y t := by
    rw [hy]
    field_simp
  rw [h1, h24]
  field_simp

/-- AKMM, p. 53: a balanced path of (2.4). Capital accumulates by (2.4), capital and output
grow at the common net rate `γ`, investment is the constant fraction `s` of output, and output
is positive. -/
structure DynBalancedPath (δ γ s : ℝ) (k i y : ℕ → ℝ) : Prop where
  accumulation : ∀ t, k (t + 1) = (1 - δ) * k t + i t
  capital_growth : ∀ t, k (t + 1) = (1 + γ) * k t
  output_growth : ∀ t, y (t + 1) = (1 + γ) * y t
  saving : ∀ t, i t = s * y t
  output_pos : ∀ t, 0 < y t

/-- AKMM, p. 53: on a balanced path investment grows at the same rate `γ`. -/
theorem dyn_investment_growth {δ γ s : ℝ} {k i y : ℕ → ℝ} (hP : DynBalancedPath δ γ s k i y)
    (t : ℕ) : i (t + 1) = (1 + γ) * i t := by
  rw [hP.saving, hP.saving, hP.output_growth]
  ring

/-- AKMM, p. 53: on a balanced path of (2.4) the capital–output ratio is constant,
`k_t/y_t = s/(γ + δ)` (for `γ + δ ≠ 0`). -/
theorem dyn_capital_output_ratio {δ γ s : ℝ} {k i y : ℕ → ℝ} (hP : DynBalancedPath δ γ s k i y)
    (hγδ : γ + δ ≠ 0) (t : ℕ) : k t / y t = s / (γ + δ) := by
  have h := hP.accumulation t
  rw [hP.capital_growth, hP.saving] at h
  have hy := (hP.output_pos t).ne'
  rw [div_eq_div_iff hy hγδ]
  linarith

/-- AKMM, p. 53 ("this equation is consistent with a capital–output ratio that does not change
over time"): conversely, if output grows at `γ`, `i_t = s y_t`, capital follows (2.4) and
starts at `k_0/y_0 = s/(γ + δ)`, then capital also grows at `γ`: the path is balanced. -/
theorem dyn_balanced_of_initial_ratio {δ γ s : ℝ} {k i y : ℕ → ℝ}
    (h24 : ∀ t, k (t + 1) = (1 - δ) * k t + i t) (hy : ∀ t, y (t + 1) = (1 + γ) * y t)
    (hs : ∀ t, i t = s * y t) (hpos : ∀ t, 0 < y t) (hγδ : γ + δ ≠ 0)
    (h0 : k 0 = s / (γ + δ) * y 0) : DynBalancedPath δ γ s k i y := by
  have hk : ∀ t, k t = s / (γ + δ) * y t := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      rw [h24, ih, hs, hy]
      field_simp
      ring
  refine ⟨h24, fun t => ?_, hy, hs, hpos⟩
  rw [hk, hk, hy]
  ring

/-- A concrete balanced path (non-vacuity of `DynBalancedPath`): with `γ > −1` and
`γ + δ ≠ 0`, `y_t = (1 + γ)^t`, `i_t = s(1 + γ)^t`, `k_t = s/(γ + δ)·(1 + γ)^t`. -/
theorem dyn_balancedPath_example {δ γ s : ℝ} (hγ : -1 < γ) (hγδ : γ + δ ≠ 0) :
    DynBalancedPath δ γ s (fun t => s / (γ + δ) * (1 + γ) ^ t) (fun t => s * (1 + γ) ^ t)
      (fun t => (1 + γ) ^ t) := by
  refine dyn_balanced_of_initial_ratio (fun t => ?_) (fun t => ?_) (fun t => rfl)
    (fun t => pow_pos (by linarith) t) hγδ (by simp)
  · simp only [pow_succ]
    field_simp
    ring
  · simp only [pow_succ]
    ring

/-- AKMM, p. 56: detrending one step. If `F` has constant returns on the nonnegative quadrant,
`γ > −1`, `ℓ ≥ 0`, `k_t ≥ 0` and `k_{t+1} = sF(k_t, (1 + γ)^t ℓ) + (1 − δ)k_t`, then
`k̃_t = k_t/(1 + γ)^t` satisfies `(1 + γ)k̃_{t+1} = sF(k̃_t, ℓ) + (1 − δ)k̃_t`, i.e.
`k̃_{t+1} = next (F · ℓ) s δ (1 + γ) k̃_t` (EconomicGrowth's discrete Solow map). -/
theorem dyn_detrend_step {F : ℝ → ℝ → ℝ} {s δ γ ℓ : ℝ} {k : ℕ → ℝ} {t : ℕ}
    (hcrs : ∀ c a b, 0 < c → 0 ≤ a → 0 ≤ b → F (c * a) (c * b) = c * F a b)
    (hγ : -1 < γ) (hl : 0 ≤ ℓ) (hk : 0 ≤ k t)
    (hsys : k (t + 1) = s * F (k t) ((1 + γ) ^ t * ℓ) + (1 - δ) * k t) :
    (1 + γ) * (k (t + 1) / (1 + γ) ^ (t + 1)) =
        s * F (k t / (1 + γ) ^ t) ℓ + (1 - δ) * (k t / (1 + γ) ^ t) ∧
      k (t + 1) / (1 + γ) ^ (t + 1) = next (fun x => F x ℓ) s δ (1 + γ) (k t / (1 + γ) ^ t) := by
  have hg : 0 < 1 + γ := by linarith
  have hp : 0 < (1 + γ) ^ t := pow_pos hg t
  have hF : F (k t) ((1 + γ) ^ t * ℓ) = (1 + γ) ^ t * F (k t / (1 + γ) ^ t) ℓ := by
    rw [← hcrs _ _ _ hp (div_nonneg hk hp.le) hl]
    congr 1
    field_simp
  have h1 : (1 + γ) * (k (t + 1) / (1 + γ) ^ (t + 1)) =
      s * F (k t / (1 + γ) ^ t) ℓ + (1 - δ) * (k t / (1 + γ) ^ t) := by
    rw [hsys, hF, pow_succ]
    field_simp
  refine ⟨h1, ?_⟩
  unfold next
  rw [← h1]
  field_simp

/-- AKMM, p. 56: the book's steady-state equation `(1 + γ)k̄ = sF(k̄, ℓ) + (1 − δ)k̄` says that
`k̄` is a fixed point of EconomicGrowth's map `next (F · ℓ) s δ (1 + γ)`. -/
theorem dyn_steady_iff {F : ℝ → ℝ → ℝ} {s δ γ ℓ kbar : ℝ} (hγ : -1 < γ) :
    (1 + γ) * kbar = s * F kbar ℓ + (1 - δ) * kbar ↔
      next (fun x => F x ℓ) s δ (1 + γ) kbar = kbar := by
  have hg : (1 + γ) ≠ 0 := by linarith
  unfold next
  rw [div_eq_iff hg]
  constructor <;> intro h <;> linarith

/-- EconomicGrowth's discrete-time parameter restrictions for the detrended map:
`s > 0`, `δ ≤ 1`, `γ > −1` and `γ + δ > 0`. -/
theorem dyn_params {s δ γ : ℝ} (hs : 0 < s) (hδ : δ ≤ 1) (hγ : -1 < γ) (hγδ : 0 < γ + δ) :
    Params s δ (1 + γ) :=
  ⟨hs, hδ, by linarith, by linarith⟩

/-- AKMM, p. 56: there is a constant solution `k̄ > 0` of `(1 + γ)k̄ = sF(k̄, ℓ) + (1 − δ)k̄`,
and it is the unique positive one ("under some minimal conditions": `F(·, ℓ)` neoclassical,
`s > 0`, `δ ≤ 1`, `γ > −1`, `γ + δ > 0`). It is EconomicGrowth's `steady`. -/
theorem dyn_steady_existsUnique {F : ℝ → ℝ → ℝ} {s δ γ ℓ : ℝ}
    (h : Technology (fun x => F x ℓ)) (hs : 0 < s) (hδ : δ ≤ 1) (hγ : -1 < γ)
    (hγδ : 0 < γ + δ) :
    (∃! kbar : ℝ, 0 < kbar ∧ (1 + γ) * kbar = s * F kbar ℓ + (1 - δ) * kbar) ∧
      0 < steady h s δ (1 + γ) ∧
      (1 + γ) * steady h s δ (1 + γ) =
        s * F (steady h s δ (1 + γ)) ℓ + (1 - δ) * steady h s δ (1 + γ) := by
  have P := dyn_params hs hδ hγ hγδ
  obtain ⟨hpos, hfix⟩ := steady_spec h P
  refine ⟨?_, hpos, (dyn_steady_iff hγ).mpr hfix⟩
  simpa only [dyn_steady_iff hγ] using existsUnique_steadyState h P

/-- AKMM, p. 56: the detrended path. If `F` has constant returns on the nonnegative quadrant,
`F(·, ℓ)` is neoclassical, `ℓ ≥ 0`, `k_0 ≥ 0` and `k_{t+1} = sF(k_t, (1 + γ)^t ℓ) + (1 − δ)k_t`
for all `t`, then `k_t = (1 + γ)^t k̃_t`, where `k̃` is the orbit of EconomicGrowth's map
`next (F · ℓ) s δ (1 + γ)` from `k_0`. -/
theorem dyn_detrended_path {F : ℝ → ℝ → ℝ} {s δ γ ℓ : ℝ} {k : ℕ → ℝ}
    (h : Technology (fun x => F x ℓ))
    (hcrs : ∀ c a b, 0 < c → 0 ≤ a → 0 ≤ b → F (c * a) (c * b) = c * F a b)
    (hs : 0 < s) (hδ : δ ≤ 1) (hγ : -1 < γ) (hγδ : 0 < γ + δ) (hl : 0 ≤ ℓ) (hk0 : 0 ≤ k 0)
    (hsys : ∀ t, k (t + 1) = s * F (k t) ((1 + γ) ^ t * ℓ) + (1 - δ) * k t) (t : ℕ) :
    k t = (1 + γ) ^ t * path (fun x => F x ℓ) s δ (1 + γ) (k 0) t := by
  have P := dyn_params hs hδ hγ hγδ
  have hp : ∀ n : ℕ, 0 < (1 + γ) ^ n := fun n => pow_pos (by linarith) n
  induction t with
  | zero => simp [path_zero]
  | succ t ih =>
    have hkt : 0 ≤ k t := by
      rw [ih]
      exact mul_nonneg (hp t).le (path_nonneg h P hk0 t)
    have hstep := (dyn_detrend_step hcrs hγ hl hkt (hsys t)).2
    have hkt' : k t / (1 + γ) ^ t = path (fun x => F x ℓ) s δ (1 + γ) (k 0) t := by
      rw [ih]
      exact mul_div_cancel_left₀ _ (hp t).ne'
    rw [hkt', ← path_succ] at hstep
    rw [← hstep]
    exact (mul_div_cancel₀ _ (hp (t + 1)).ne').symm

/-- AKMM, p. 56: balanced growth from the constant solution. If `k_0 = k̄` (the steady state),
then `k_t = k̄(1 + γ)^t`, output `y_t = F(k_t, (1 + γ)^t ℓ) = (1 + γ)^t F(k̄, ℓ)` and investment
`i_t = s y_t` all grow at the net rate `γ`, and `k_t/y_t = s/(γ + δ)`. -/
theorem dyn_balanced_growth_from_steady {F : ℝ → ℝ → ℝ} {s δ γ ℓ : ℝ} {k : ℕ → ℝ}
    (h : Technology (fun x => F x ℓ))
    (hcrs : ∀ c a b, 0 < c → 0 ≤ a → 0 ≤ b → F (c * a) (c * b) = c * F a b)
    (hs : 0 < s) (hδ : δ ≤ 1) (hγ : -1 < γ) (hγδ : 0 < γ + δ) (hl : 0 ≤ ℓ)
    (hk0 : k 0 = steady h s δ (1 + γ))
    (hsys : ∀ t, k (t + 1) = s * F (k t) ((1 + γ) ^ t * ℓ) + (1 - δ) * k t) :
    (∀ t, k t = steady h s δ (1 + γ) * (1 + γ) ^ t) ∧
      (∀ t, F (k t) ((1 + γ) ^ t * ℓ) = (1 + γ) ^ t * F (steady h s δ (1 + γ)) ℓ) ∧
      DynBalancedPath δ γ s k (fun t => s * F (k t) ((1 + γ) ^ t * ℓ))
        (fun t => F (k t) ((1 + γ) ^ t * ℓ)) ∧
      ∀ t, k t / F (k t) ((1 + γ) ^ t * ℓ) = s / (γ + δ) := by
  have P := dyn_params hs hδ hγ hγδ
  obtain ⟨hpos, hfix⟩ := steady_spec h P
  set kb := steady h s δ (1 + γ) with hkb
  have hp : ∀ n : ℕ, 0 < (1 + γ) ^ n := fun n => pow_pos (by linarith) n
  have hpath : ∀ t, path (fun x => F x ℓ) s δ (1 + γ) kb t = kb := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [path_succ, ih, hfix]
  have hk : ∀ t, k t = kb * (1 + γ) ^ t := by
    intro t
    rw [dyn_detrended_path h hcrs hs hδ hγ hγδ hl (by rw [hk0]; exact hpos.le) hsys t, hk0,
      hpath]
    ring
  have hy : ∀ t, F (k t) ((1 + γ) ^ t * ℓ) = (1 + γ) ^ t * F kb ℓ := by
    intro t
    rw [hk, mul_comm kb, hcrs _ _ _ (hp t) hpos.le hl]
  have hFpos : 0 < F kb ℓ := h.output_pos hpos
  have hB : DynBalancedPath δ γ s k (fun t => s * F (k t) ((1 + γ) ^ t * ℓ))
      (fun t => F (k t) ((1 + γ) ^ t * ℓ)) := by
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => rfl, fun t => ?_⟩
    · rw [hsys t]
      ring
    · rw [hk, hk, pow_succ]
      ring
    · show F (k (t + 1)) ((1 + γ) ^ (t + 1) * ℓ) = (1 + γ) * F (k t) ((1 + γ) ^ t * ℓ)
      rw [hy, hy, pow_succ]
      ring
    · simp only [hy]
      exact mul_pos (hp t) hFpos
  exact ⟨hk, hy, hB, dyn_capital_output_ratio hB hγδ.ne'⟩

/-- AKMM, pp. 56–57: convergence (asserted in Ch. 2, proved in Ch. 3). Under the hypotheses of
`dyn_detrended_path` with `k_0 > 0`: the detrended stock `k̃_t = k_t/(1 + γ)^t` is positive,
moves monotonically toward `k̄` (increasing from below, decreasing from above), and converges
to `k̄`; and the capital–output ratio `k_t/y_t`, `y_t = F(k_t, (1 + γ)^t ℓ)`, converges to
`s/(γ + δ)`. Proved from EconomicGrowth's `general_solow` (Acemoglu Proposition 2.5). -/
theorem dyn_convergence {F : ℝ → ℝ → ℝ} {s δ γ ℓ : ℝ} {k : ℕ → ℝ}
    (h : Technology (fun x => F x ℓ))
    (hcrs : ∀ c a b, 0 < c → 0 ≤ a → 0 ≤ b → F (c * a) (c * b) = c * F a b)
    (hs : 0 < s) (hδ : δ ≤ 1) (hγ : -1 < γ) (hγδ : 0 < γ + δ) (hl : 0 ≤ ℓ) (hk0 : 0 < k 0)
    (hsys : ∀ t, k (t + 1) = s * F (k t) ((1 + γ) ^ t * ℓ) + (1 - δ) * k t) :
    (∀ t, 0 < k t / (1 + γ) ^ t) ∧
      (k 0 < steady h s δ (1 + γ) → StrictMono fun t => k t / (1 + γ) ^ t) ∧
      (steady h s δ (1 + γ) < k 0 → StrictAnti fun t => k t / (1 + γ) ^ t) ∧
      Tendsto (fun t => k t / (1 + γ) ^ t) atTop (𝓝 (steady h s δ (1 + γ))) ∧
      Tendsto (fun t => k t / F (k t) ((1 + γ) ^ t * ℓ)) atTop (𝓝 (s / (γ + δ))) := by
  have P := dyn_params hs hδ hγ hγδ
  have hp : ∀ n : ℕ, 0 < (1 + γ) ^ n := fun n => pow_pos (by linarith) n
  set f : ℝ → ℝ := fun x => F x ℓ with hf
  have hkt : ∀ t, k t / (1 + γ) ^ t = path f s δ (1 + γ) (k 0) t := by
    intro t
    rw [dyn_detrended_path h hcrs hs hδ hγ hγδ hl hk0.le hsys t]
    exact mul_div_cancel_left₀ _ (hp t).ne'
  have hI : IsPath f s δ (1 + γ) (path f s δ (1 + γ) (k 0)) := isPath_path hk0
  obtain ⟨hpos, hlow, hhigh, -, -, hlim⟩ := hI.orbit h P
  have hfun : (fun t => k t / (1 + γ) ^ t) = path f s δ (1 + γ) (k 0) := funext hkt
  -- the capital–output ratio is `k̃_t / F(k̃_t, ℓ)`
  have hratio : ∀ t, k t / F (k t) ((1 + γ) ^ t * ℓ) =
      path f s δ (1 + γ) (k 0) t / f (path f s δ (1 + γ) (k 0) t) := by
    intro t
    have hk : k t = (1 + γ) ^ t * path f s δ (1 + γ) (k 0) t :=
      dyn_detrended_path h hcrs hs hδ hγ hγδ hl hk0.le hsys t
    rw [hk, hcrs _ _ _ (hp t) (hpos t).le hl]
    exact mul_div_mul_left _ _ (hp t).ne'
  obtain ⟨hkpos, -, hsteady, -⟩ := steady_state_equilibrium h P
  have hFk : 0 < f (steady h s δ (1 + γ)) := h.output_pos hkpos
  have hlimF := (output_consumption_limit h P hI).1
  have hlimR := hlim.div hlimF hFk.ne'
  have hval : steady h s δ (1 + γ) / f (steady h s δ (1 + γ)) = s / (γ + δ) := by
    have : (1 + γ) - 1 + δ = γ + δ := by ring
    rw [this] at hsteady
    rw [div_eq_div_iff hFk.ne' hγδ.ne']
    linarith
  rw [hfun]
  refine ⟨fun t => by rw [hkt]; exact hpos t, fun h0 => (hlow h0).1, fun h0 => (hhigh h0).1,
    hlim, ?_⟩
  rw [funext hratio, ← hval]
  exact hlimR

end AKMM.Framework

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The existence of an aggregate production function (box, pp. 49–50)

AKMM, box "The existence of an aggregate production function", pp. 49–50, and its footnote a.
A static economy produces two goods from capital and labour, freely allocated across sectors:
`x₁ = G(k₁, ℓ₁)` and `x₂ = aG(k₂, ℓ₂)` with `a > 0` ("identical isoquants — one is a scalar
multiplication of the other"), `k₁ + k₂ = K`, `ℓ₁ + ℓ₂ = L`, with `G` concave and of constant
returns on the positive quadrant. The footnote's exercise: a relative price is implied by the
technologies alone, and there is a price-independent mapping from inputs to output.

* `G` is superadditive (`agg_superadditive`), so every interior allocation satisfies
  `x₁ + x₂/a ≤ G(K, L)` (`agg_frontier_bound`), and every point of that linear frontier with both
  goods produced is attained by a proportional allocation (`agg_frontier_attained`).
* If an interior allocation maximises the value `px₁ + x₂` of output at relative price `p > 0`
  among interior allocations, then `p = a` (`agg_price_implied`): the price is pinned by the
  technologies.
* At `p = a` the maximal value of output is `aG(K, L)`, and output measured in units of good 1,
  `x₁ + x₂/a`, equals `G(K, L)` at every value-maximising allocation: the aggregate production
  function is `G`, independent of prices and preferences (`agg_aggregate_production`).

The box's other statements (the general two-sector mapping depends on `p`; the Cambridge
controversy) are narrative and are not formalised.
-/

namespace AKMM.Framework

open Filter Topology

/-- The positive quadrant of input pairs `(k, ℓ)`. -/
def aggPosQuadrant : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2}

/-- AKMM, box p. 50 (used for the exercise in footnote a): a concave function with constant
returns on the positive quadrant is superadditive, `G(k₁ + k₂, ℓ₁ + ℓ₂) ≥ G(k₁, ℓ₁) + G(k₂, ℓ₂)`. -/
theorem agg_superadditive {G : ℝ → ℝ → ℝ}
    (hconc : ConcaveOn ℝ aggPosQuadrant (fun q => G q.1 q.2))
    (hcrs : ∀ s x y, 0 < s → 0 < x → 0 < y → G (s * x) (s * y) = s * G x y)
    {k₁ ℓ₁ k₂ ℓ₂ : ℝ} (hk₁ : 0 < k₁) (hl₁ : 0 < ℓ₁) (hk₂ : 0 < k₂) (hl₂ : 0 < ℓ₂) :
    G k₁ ℓ₁ + G k₂ ℓ₂ ≤ G (k₁ + k₂) (ℓ₁ + ℓ₂) := by
  have hc := hconc.2 (show ((k₁, ℓ₁) : ℝ × ℝ) ∈ aggPosQuadrant from ⟨hk₁, hl₁⟩)
    (show ((k₂, ℓ₂) : ℝ × ℝ) ∈ aggPosQuadrant from ⟨hk₂, hl₂⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at hc
  have hh := hcrs 2 (1 / 2 * k₁ + 1 / 2 * k₂) (1 / 2 * ℓ₁ + 1 / 2 * ℓ₂) two_pos
    (by positivity) (by positivity)
  rw [show 2 * (1 / 2 * k₁ + 1 / 2 * k₂) = k₁ + k₂ by ring,
    show 2 * (1 / 2 * ℓ₁ + 1 / 2 * ℓ₂) = ℓ₁ + ℓ₂ by ring] at hh
  linarith

/-- AKMM, box p. 50: with `x₂ = aG(k₂, ℓ₂)`, every interior allocation of `(K, L)` lies on or
below the linear frontier `x₁ + x₂/a ≤ G(K, L)`. -/
theorem agg_frontier_bound {G : ℝ → ℝ → ℝ}
    (hconc : ConcaveOn ℝ aggPosQuadrant (fun q => G q.1 q.2))
    (hcrs : ∀ s x y, 0 < s → 0 < x → 0 < y → G (s * x) (s * y) = s * G x y)
    {a K L k₁ ℓ₁ : ℝ} (ha : 0 < a) (hk₁ : 0 < k₁) (hl₁ : 0 < ℓ₁) (hk₂ : k₁ < K)
    (hl₂ : ℓ₁ < L) :
    G k₁ ℓ₁ + a * G (K - k₁) (L - ℓ₁) / a ≤ G K L := by
  have h := agg_superadditive hconc hcrs hk₁ hl₁ (sub_pos.2 hk₂) (sub_pos.2 hl₂)
  rw [add_sub_cancel, add_sub_cancel] at h
  rw [mul_div_cancel_left₀ _ ha.ne']
  exact h

/-- AKMM, box p. 50: the proportional allocation `k₁ = θK`, `ℓ₁ = θL`, `θ ∈ (0, 1)`, produces
`x₁ = θG(K, L)` and `x₂ = (1 − θ)aG(K, L)`: every point of the frontier `x₁ + x₂/a = G(K, L)`
with both goods produced is attained. -/
theorem agg_frontier_attained {G : ℝ → ℝ → ℝ}
    (hcrs : ∀ s x y, 0 < s → 0 < x → 0 < y → G (s * x) (s * y) = s * G x y)
    {a K L θ : ℝ} (ha : 0 < a) (hK : 0 < K) (hL : 0 < L) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    G (θ * K) (θ * L) = θ * G K L ∧
      a * G (K - θ * K) (L - θ * L) = (1 - θ) * (a * G K L) ∧
      G (θ * K) (θ * L) + a * G (K - θ * K) (L - θ * L) / a = G K L := by
  have h1 := hcrs θ K L hθ0 hK hL
  have h2 := hcrs (1 - θ) K L (sub_pos.2 hθ1) hK hL
  rw [show (1 - θ) * K = K - θ * K by ring, show (1 - θ) * L = L - θ * L by ring] at h2
  refine ⟨h1, by rw [h2]; ring, ?_⟩
  rw [h1, h2]
  field_simp
  ring

/-- AKMM, box p. 50, footnote a ("a relative price `p` is implied from the production
technologies alone"): if an interior allocation `(k₁, ℓ₁)` maximises the value
`pG(k₁, ℓ₁) + aG(K − k₁, L − ℓ₁)` of output at relative price `p > 0` over all interior
allocations, and `G > 0` on the positive quadrant, then `p = a`. -/
theorem agg_price_implied {G : ℝ → ℝ → ℝ}
    (hconc : ConcaveOn ℝ aggPosQuadrant (fun q => G q.1 q.2))
    (hcrs : ∀ s x y, 0 < s → 0 < x → 0 < y → G (s * x) (s * y) = s * G x y)
    (hpos : ∀ x y, 0 < x → 0 < y → 0 < G x y)
    {a p K L k₁ ℓ₁ : ℝ} (ha : 0 < a) (hp : 0 < p) (hK : 0 < K) (hL : 0 < L)
    (hk₁ : 0 < k₁) (hl₁ : 0 < ℓ₁) (hk₂ : k₁ < K) (hl₂ : ℓ₁ < L)
    (hmax : ∀ k ℓ, 0 < k → 0 < ℓ → k < K → ℓ < L →
      p * G k ℓ + a * G (K - k) (L - ℓ) ≤ p * G k₁ ℓ₁ + a * G (K - k₁) (L - ℓ₁)) :
    p = a := by
  set V := p * G k₁ ℓ₁ + a * G (K - k₁) (L - ℓ₁) with hV
  -- the value along proportional allocations is `G(K, L)(a + θ(p − a))`
  have hprop : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, G K L * (a + θ * (p - a)) ≤ V := by
    intro θ hθ
    obtain ⟨h1, h2, -⟩ := agg_frontier_attained hcrs ha hK hL hθ.1 hθ.2
    have := hmax (θ * K) (θ * L) (mul_pos hθ.1 hK) (mul_pos hθ.1 hL)
      (by nlinarith [hθ.2]) (by nlinarith [hθ.2])
    rw [h1, h2] at this
    linarith
  have hcont : Continuous fun θ : ℝ => G K L * (a + θ * (p - a)) := by fun_prop
  -- letting `θ → 1` and `θ → 0`
  have hpG : G K L * p ≤ V := by
    have ht : Tendsto (fun θ : ℝ => G K L * (a + θ * (p - a))) (𝓝[<] 1)
        (𝓝 (G K L * (a + 1 * (p - a)))) := hcont.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have hle := le_of_tendsto ht (by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
      exact hprop θ hθ)
    linarith
  have haG : G K L * a ≤ V := by
    have ht : Tendsto (fun θ : ℝ => G K L * (a + θ * (p - a))) (𝓝[>] 0)
        (𝓝 (G K L * (a + 0 * (p - a)))) := hcont.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have hle := le_of_tendsto ht (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
      exact hprop θ hθ)
    linarith
  have hfr := agg_frontier_bound hconc hcrs ha hk₁ hl₁ hk₂ hl₂
  rw [mul_div_cancel_left₀ _ ha.ne'] at hfr
  have hx₁ := hpos k₁ ℓ₁ hk₁ hl₁
  have hx₂ := hpos (K - k₁) (L - ℓ₁) (sub_pos.2 hk₂) (sub_pos.2 hl₂)
  -- `p ≤ a`: from `p(x₁ + x₂/a) ≤ pG ≤ px₁ + x₂` with `x₂ = aG(K − k₁, L − ℓ₁) > 0`
  have h1 : p ≤ a := by
    by_contra hlt'
    have hlt := lt_of_not_ge hlt'
    nlinarith [mul_lt_mul_of_pos_right hlt hx₂]
  -- `a ≤ p`: from `a(x₁ + x₂/a) ≤ aG ≤ px₁ + x₂` with `x₁ > 0`
  have h2 : a ≤ p := by
    by_contra hlt'
    have hlt := lt_of_not_ge hlt'
    nlinarith [mul_lt_mul_of_pos_right hlt hx₁]
  exact le_antisymm h1 h2

/-- AKMM, box p. 50, footnote a (the price-independent mapping): at the implied price `p = a`,
the value of output is maximised exactly by the allocations with
`x₁ + x₂/a = G(K, L)` — in particular by every proportional allocation — and its maximal value is
`aG(K, L)`. So output in units of good 1, `x₁ + x₂/a`, is `G(K, L)` at every value-maximising
allocation: an aggregate production function independent of prices and preferences. -/
theorem agg_aggregate_production {G : ℝ → ℝ → ℝ}
    (hconc : ConcaveOn ℝ aggPosQuadrant (fun q => G q.1 q.2))
    (hcrs : ∀ s x y, 0 < s → 0 < x → 0 < y → G (s * x) (s * y) = s * G x y)
    {a K L : ℝ} (ha : 0 < a) (hK : 0 < K) (hL : 0 < L) :
    (∀ k ℓ, 0 < k → 0 < ℓ → k < K → ℓ < L → a * G k ℓ + a * G (K - k) (L - ℓ) ≤ a * G K L) ∧
      (∀ θ, 0 < θ → θ < 1 →
        a * G (θ * K) (θ * L) + a * G (K - θ * K) (L - θ * L) = a * G K L) ∧
      (∀ k ℓ, 0 < k → 0 < ℓ → k < K → ℓ < L →
        (a * G k ℓ + a * G (K - k) (L - ℓ) = a * G K L ↔
          G k ℓ + a * G (K - k) (L - ℓ) / a = G K L)) := by
  refine ⟨fun k ℓ hk hl hkK hlL => ?_, fun θ h0 h1 => ?_, fun k ℓ hk hl hkK hlL => ?_⟩
  · have := agg_frontier_bound hconc hcrs ha hk hl hkK hlL
    rw [mul_div_cancel_left₀ _ ha.ne'] at this
    nlinarith
  · obtain ⟨-, -, h⟩ := agg_frontier_attained hcrs ha hK hL h0 h1
    rw [mul_div_cancel_left₀ _ ha.ne'] at h
    rw [← h]
    ring
  · rw [mul_div_cancel_left₀ _ ha.ne', ← mul_add]
    exact ⟨fun h => mul_left_cancel₀ ha.ne' h, fun h => by rw [h]⟩

end AKMM.Framework

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Saving: the Euler equation and CRRA utility

AKMM, §2.1.8, "Consumption vs. saving", pp. 62–63, with footnote 19.

* **The Euler equation** `u′(c_t) = βu′(c_{t+1})R_{t+1}`, equivalently
  `u′(c_t)/(βu′(c_{t+1})) = R_{t+1}`: the first-order condition of
  `max u(c_t) + βu(c_{t+1})` subject to `c_{t+1} = R_{t+1}(W − c_t)` at an interior optimum
  (`pref_euler_equation`).
* **CRRA utility (2.5)** `u(c) = (c^{1−σ} − 1)/(1 − σ)` (`prefCrra`), with `u′(c) = c^{−σ}`
  (`eq_2_5_hasDerivAt`). The "if" part on p. 63: `u′(c)/u′((1 + γ)c) = (1 + γ)^σ` does not depend
  on `c` (`pref_crra_mu_ratio`); at a constant gross rate `R` the Euler equation holds exactly
  when `c_{t+1} = (βR)^{1/σ}c_t` (`pref_crra_euler_iff`), so the consumer chooses a constant growth
  rate that depends on `R`, `β` and `σ` but not on wealth (`pref_crra_constant_growth`).
* **The log limit** (footnote 19): `(c^{1−σ} − 1)/(1 − σ) → log c` as `σ → 1`
  (`pref_crra_log_limit`), with the l'Hôpital derivatives `−c^{1−σ}log c` and `−1`
  (`pref_footnote_19_derivatives`).

The "only if" part (power utility is the only class consistent with balanced growth) is proved
in the book's Appendix 4.A.2, not here.
-/

namespace AKMM.Framework

open Filter Topology

/-- AKMM, p. 62: the Euler equation. A consumer with wealth `W` chooses `c₀` and consumes
`c₁ = R(W − c₀)` next period. If `c₀` is a local maximum of `u(c) + βu(R(W − c))` and `u` is
differentiable at `c₀` and at `c₁ = R(W − c₀)`, then `u′(c₀) = βu′(c₁)R`, and, when
`βu′(c₁) ≠ 0`, `u′(c₀)/(βu′(c₁)) = R`. -/
theorem pref_euler_equation {u : ℝ → ℝ} {β R W c₀ u0 u1 : ℝ}
    (hu0 : HasDerivAt u u0 c₀) (hu1 : HasDerivAt u u1 (R * (W - c₀)))
    (hmax : IsLocalMax (fun c => u c + β * u (R * (W - c))) c₀) :
    u0 = β * u1 * R ∧ (β * u1 ≠ 0 → u0 / (β * u1) = R) := by
  have hc : HasDerivAt (fun c => R * (W - c)) (-R) c₀ := by
    simpa using ((hasDerivAt_id c₀).const_sub W).const_mul R
  have hd : HasDerivAt (fun c => u c + β * u (R * (W - c))) (u0 + β * (u1 * -R)) c₀ :=
    hu0.add ((hu1.comp c₀ hc).const_mul β)
  have h0 := hmax.hasDerivAt_eq_zero hd
  have he : u0 = β * u1 * R := by linarith
  refine ⟨he, fun hne => ?_⟩
  rw [he]
  exact mul_div_cancel_left₀ R hne

/-- AKMM, (2.5), p. 63: CRRA utility `u(c) = (c^{1−σ} − 1)/(1 − σ)`. -/
noncomputable def prefCrra (σ c : ℝ) : ℝ := (c ^ (1 - σ) - 1) / (1 - σ)

/-- AKMM, (2.5), p. 63: for `σ ≠ 1` and `c > 0`, `u′(c) = c^{−σ}`. -/
theorem eq_2_5_hasDerivAt {σ c : ℝ} (hσ : σ ≠ 1) (hc : 0 < c) :
    HasDerivAt (prefCrra σ) (c ^ (-σ)) c := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).sub_const 1).div_const
    (1 - σ)
  have h1 : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have h3 : (1 - σ) * c ^ (1 - σ - 1) / (1 - σ) = c ^ (-σ) := by
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp
  exact h.congr_deriv h3

/-- AKMM, p. 63: for power utility `u′(c)/u′((1 + γ)c) = (1 + γ)^σ` for every `c > 0`: the ratio
is constant in `c` and contains the growth rate. -/
theorem pref_crra_mu_ratio {σ γ c : ℝ} (hγ : 0 < 1 + γ) (hc : 0 < c) :
    c ^ (-σ) / ((1 + γ) * c) ^ (-σ) = (1 + γ) ^ σ := by
  rw [Real.mul_rpow hγ.le hc.le, Real.rpow_neg hγ.le]
  have h1 : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  have h2 : 0 < (1 + γ) ^ σ := Real.rpow_pos_of_pos hγ _
  field_simp

/-- AKMM, p. 63: with power marginal utility `u′(c) = c^{−σ}`, `σ > 0`, and `β, R > 0`, the
Euler equation `u′(c) = βRu′(c′)` holds if and only if `c′ = (βR)^{1/σ}c`. -/
theorem pref_crra_euler_iff {σ β R c c' : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (hc : 0 < c) (hc' : 0 < c') :
    c ^ (-σ) = β * R * c' ^ (-σ) ↔ c' = (β * R) ^ (1 / σ) * c := by
  have hbR : 0 < β * R := mul_pos hβ hR
  have hσ' : σ ≠ 0 := hσ.ne'
  -- both sides are equivalent to `c'^σ = βR c^σ`
  have key : c ^ (-σ) = β * R * c' ^ (-σ) ↔ c' ^ σ = β * R * c ^ σ := by
    rw [Real.rpow_neg hc.le, Real.rpow_neg hc'.le]
    have h1 : 0 < c ^ σ := Real.rpow_pos_of_pos hc σ
    have h2 : 0 < c' ^ σ := Real.rpow_pos_of_pos hc' σ
    constructor
    · intro h
      field_simp at h
      linarith
    · intro h
      field_simp
      linarith
  rw [key]
  constructor
  · intro h
    have : c' = (c' ^ σ) ^ (1 / σ) := by
      rw [← Real.rpow_mul hc'.le, mul_one_div_cancel hσ', Real.rpow_one]
    rw [this, h, Real.mul_rpow hbR.le (Real.rpow_nonneg hc.le σ), ← Real.rpow_mul hc.le,
      mul_one_div_cancel hσ', Real.rpow_one]
  · intro h
    rw [h, Real.mul_rpow (Real.rpow_nonneg hbR.le _) hc.le, ← Real.rpow_mul hbR.le,
      one_div_mul_cancel hσ', Real.rpow_one]

/-- AKMM, p. 63: under power utility and a constant gross interest rate `R`, the path
`c_t = ((βR)^{1/σ})^t c_0` satisfies the Euler equation `u′(c_t) = βRu′(c_{t+1})` in every
period, and it is the only positive path from `c_0` that does: consumption grows at the constant
gross rate `(βR)^{1/σ}`, which depends on `R`, `β`, `σ` but not on `c_0`. -/
theorem pref_crra_constant_growth {σ β R c₀ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (hc₀ : 0 < c₀) :
    (∀ t : ℕ, ((β * R) ^ (1 / σ)) ^ t * c₀ > 0 ∧
      (((β * R) ^ (1 / σ)) ^ t * c₀) ^ (-σ) =
        β * R * (((β * R) ^ (1 / σ)) ^ (t + 1) * c₀) ^ (-σ)) ∧
      ∀ c : ℕ → ℝ, c 0 = c₀ → (∀ t, 0 < c t) →
        (∀ t, c t ^ (-σ) = β * R * c (t + 1) ^ (-σ)) →
          ∀ t, c t = ((β * R) ^ (1 / σ)) ^ t * c₀ := by
  have hg : 0 < (β * R) ^ (1 / σ) := Real.rpow_pos_of_pos (mul_pos hβ hR) _
  refine ⟨fun t => ⟨mul_pos (pow_pos hg t) hc₀, ?_⟩, fun c h0 hpos he t => ?_⟩
  · rw [pref_crra_euler_iff hσ hβ hR (mul_pos (pow_pos hg t) hc₀)
      (mul_pos (pow_pos hg (t + 1)) hc₀), pow_succ]
    ring
  · induction t with
    | zero => simp [h0]
    | succ t ih =>
      rw [(pref_crra_euler_iff hσ hβ hR (hpos t) (hpos (t + 1))).1 (he t), ih, pow_succ]
      ring

/-- AKMM, footnote 19, p. 63: the l'Hôpital derivatives in `σ`: `d(c^{1−σ} − 1)/dσ =
−c^{1−σ}log c` and `d(1 − σ)/dσ = −1`, for `c > 0`. -/
theorem pref_footnote_19_derivatives {c : ℝ} (hc : 0 < c) (σ : ℝ) :
    HasDerivAt (fun s => c ^ (1 - s) - 1) (-(c ^ (1 - σ) * Real.log c)) σ ∧
      HasDerivAt (fun s : ℝ => 1 - s) (-1) σ := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) σ := by
    simpa using (hasDerivAt_id σ).const_sub 1
  refine ⟨?_, h1⟩
  have h2 := ((Real.hasStrictDerivAt_const_rpow hc (1 - σ)).hasDerivAt.comp σ h1).sub_const 1
  exact h2.congr_deriv (by ring)

/-- AKMM, p. 63 and footnote 19: as `σ → 1`, CRRA utility (2.5) tends to `log c`, for `c > 0`. -/
theorem pref_crra_log_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun σ => prefCrra σ c) (𝓝[≠] 1) (𝓝 (Real.log c)) := by
  -- the slope of `x ↦ c^x` at `0`
  have hd : HasDerivAt (fun x : ℝ => c ^ x) (c ^ (0 : ℝ) * Real.log c) 0 :=
    (Real.hasStrictDerivAt_const_rpow hc 0).hasDerivAt
  rw [Real.rpow_zero, one_mul, hasDerivAt_iff_tendsto_slope] at hd
  -- `σ ↦ 1 − σ` maps a punctured neighbourhood of `1` into one of `0`
  have hm : Tendsto (fun σ : ℝ => 1 - σ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun σ : ℝ => 1 - σ) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact sub_ne_zero.2 (Ne.symm hσ)
  refine (hd.comp hm).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ _
  simp only [Function.comp_apply, slope_def_field, prefCrra, Real.rpow_zero, sub_zero]

end AKMM.Framework

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

set_option linter.style.longLine false
#print axioms AKMM.Framework.gaPartials
#print axioms AKMM.Framework.ga_partials_apply
#print axioms AKMM.Framework.ga_hasFDerivAt_coords
#print axioms AKMM.Framework.ga_per_capita
#print axioms AKMM.Framework.ga_profit_foc
#print axioms AKMM.Framework.ga_growth_identity
#print axioms AKMM.Framework.eq_2_1
#print axioms AKMM.Framework.ga_hicks_neutral_common_factor
#print axioms AKMM.Framework.eq_2_2
#print axioms AKMM.Framework.ga_labour_augmenting_partials
#print axioms AKMM.Framework.eq_2_3
#print axioms AKMM.Framework.ga_eq_2_3_partial_misreading
#print axioms AKMM.Framework.ga_cobbDouglas_hasDerivAt_k
#print axioms AKMM.Framework.ga_cobbDouglas_share
#print axioms AKMM.Framework.ga_cobbDouglas_crs
#print axioms AKMM.Framework.eq_2_4_ratio_form
#print axioms AKMM.Framework.DynBalancedPath
#print axioms AKMM.Framework.DynBalancedPath.mk
#print axioms AKMM.Framework.DynBalancedPath.accumulation
#print axioms AKMM.Framework.DynBalancedPath.capital_growth
#print axioms AKMM.Framework.DynBalancedPath.output_growth
#print axioms AKMM.Framework.DynBalancedPath.saving
#print axioms AKMM.Framework.DynBalancedPath.output_pos
#print axioms AKMM.Framework.dyn_investment_growth
#print axioms AKMM.Framework.dyn_capital_output_ratio
#print axioms AKMM.Framework.dyn_balanced_of_initial_ratio
#print axioms AKMM.Framework.dyn_balancedPath_example
#print axioms AKMM.Framework.dyn_detrend_step
#print axioms AKMM.Framework.dyn_steady_iff
#print axioms AKMM.Framework.dyn_params
#print axioms AKMM.Framework.dyn_steady_existsUnique
#print axioms AKMM.Framework.dyn_detrended_path
#print axioms AKMM.Framework.dyn_balanced_growth_from_steady
#print axioms AKMM.Framework.dyn_convergence
#print axioms AKMM.Framework.aggPosQuadrant
#print axioms AKMM.Framework.agg_superadditive
#print axioms AKMM.Framework.agg_frontier_bound
#print axioms AKMM.Framework.agg_frontier_attained
#print axioms AKMM.Framework.agg_price_implied
#print axioms AKMM.Framework.agg_aggregate_production
#print axioms AKMM.Framework.pref_euler_equation
#print axioms AKMM.Framework.prefCrra
#print axioms AKMM.Framework.eq_2_5_hasDerivAt
#print axioms AKMM.Framework.pref_crra_mu_ratio
#print axioms AKMM.Framework.pref_crra_euler_iff
#print axioms AKMM.Framework.pref_crra_constant_growth
#print axioms AKMM.Framework.pref_footnote_19_derivatives
#print axioms AKMM.Framework.pref_crra_log_limit
#print axioms AKMM.Framework.lsKpr
#print axioms AKMM.Framework.ls_kpr_eq_rm
#print axioms AKMM.Framework.ls_kpr_hasDerivAt_c
#print axioms AKMM.Framework.ls_kpr_hasDerivAt_l
#print axioms AKMM.Framework.ls_kpr_mrs
#print axioms AKMM.Framework.ls_kpr_balanced_growth
#print axioms AKMM.Framework.lsBK
#print axioms AKMM.Framework.lsBKUc
#print axioms AKMM.Framework.lsBKUl
#print axioms AKMM.Framework.ls_bk_hasDerivAt_c
#print axioms AKMM.Framework.ls_bk_hasDerivAt_l
#print axioms AKMM.Framework.ls_bk_arg_invariant
#print axioms AKMM.Framework.ls_bk_uc_scale
#print axioms AKMM.Framework.ls_bk_ul_scale
#print axioms AKMM.Framework.ls_bk_mrs_scale
#print axioms AKMM.Framework.ls_bk_balanced_growth
#print axioms AKMM.Framework.ls_bk_nu_zero
#print axioms AKMM.Framework.ls_bk_hours_marginal_sign
#print axioms AKMM.Framework.ls_bk_decreasing_g_counterexample
#print axioms AKMM.Framework.ls_bk_production
#print axioms AKMM.Framework.ls_p64_output_growth_correction
