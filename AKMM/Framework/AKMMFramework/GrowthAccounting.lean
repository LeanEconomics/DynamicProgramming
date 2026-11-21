/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import NeoclassicalGrowth.RMBasics

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
