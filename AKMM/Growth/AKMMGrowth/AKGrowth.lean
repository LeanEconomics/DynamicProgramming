/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.ISTCBGP
import AKMMContinuousTime.Mangasarian
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The AK model

AKMM, §13.5 (pp. 384–386) and footnotes 24–25. The planner maximises (13.18)
`∫e^{−(ρ−n)t}u(c)` subject to `K̇ = AK − e^{nt}c − δK`; with `g = (A − δ − ρ)/σ`:

* the planner's first-order conditions give the Euler equation (13.19) (`eq_13_19`) and the
  transversality term (13.20) (`eq_13_20`);
* the closed-form policy `c = (A − δ − n − g)e^{−nt}K` with `K̇/K = n + g` satisfies the
  resource constraint and the Euler equation (`ak_policy`);
* `σ(A − δ − n) > A − δ − ρ` iff `A − δ − n − g > 0` iff the TVC holds on this path
  (`ak_bounded_iff`, `ak_tvc`); the policy is then catching-up optimal (`ak_optimal`) and is the
  competitive equilibrium with `r = A − δ`, `w = 0` (`ak_decentralized`);
* footnote 24: every solution of the capital equation with Euler consumption is
  `Ξe^{(A−δ)t} + c(0)e^{(n+g)t}/(A − δ − n − g)` (`ak_footnote_24_general`), and the TVC forces
  `Ξ = 0` (`ak_footnote_24_unique`); the printed `K̇/K = A − δ − e^{(n+g)t}c(0)` lacks `/K(t)`
  (`ak_footnote_24_printed_false`);
* footnote 25: with a capital-income tax `τ` rebated lump-sum, the resource constraint is
  unchanged and growth `((1 − τ)(A − δ) − ρ)/σ` is strictly decreasing in `τ`
  (`ak_footnote_25`).

The AK model of InternationalEconomics' `GlobalGrowth` is in discrete time (Obstfeld–Rogoff),
so it is not reused.
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, p. 385: the AK growth rate of consumption, `g = (A − δ − ρ)/σ`. -/
noncomputable def akG (A δ ρ σ : ℝ) : ℝ := (A - δ - ρ) / σ

/-- AKMM, (13.19), p. 385: **the planner's Euler equation**. With the Hamiltonian
`e^{−(ρ−n)t}u(c) + μ(AK − e^{nt}c − δK)`, the conditions `e^{−(ρ−n)t}c^{−σ} = μe^{nt}` and
`μ̇ = −μ(A − δ)` give `ċ/c = (A − δ − ρ)/σ`. -/
theorem eq_13_19 {A δ ρ σ n t cdot : ℝ} {c μ : ℝ → ℝ} (hσ : 0 < σ) (hc : 0 < c t)
    (hcd : HasDerivAt c cdot t)
    (hfoc : ∀ s, Real.exp (-(ρ - n) * s) * c s ^ (-σ) = μ s * Real.exp (n * s))
    (hcost : HasDerivAt μ (-(μ t * (A - δ))) t) :
    cdot / c t = akG A δ ρ σ := by
  have h := istc_planner_euler (Ax := 1) (γx := 0) (MPK := A) (δ := δ) (c := c) (μ := μ) hσ
    one_pos hc hcd (fun s => by rw [hfoc s]; simp) (by simpa using hcost)
  rw [h]
  unfold akG
  simp

/-- AKMM, (13.20), p. 385: along `c(t) = c(0)e^{gt}`, the transversality term
`c(T)^{−σ}e^{−ρT}K(T)` equals `c(0)^{−σ}e^{−(A−δ)T}K(T)`. -/
theorem eq_13_20 {A δ ρ σ c0 T KT : ℝ} (hσ : 0 < σ) (hc0 : 0 < c0) :
    (c0 * Real.exp (akG A δ ρ σ * T)) ^ (-σ) * Real.exp (-ρ * T) * KT =
      c0 ^ (-σ) * Real.exp (-(A - δ) * T) * KT := by
  rw [Real.mul_rpow hc0.le (Real.exp_pos _).le, ← Real.exp_mul]
  have : Real.exp (akG A δ ρ σ * T * -σ) * Real.exp (-ρ * T) = Real.exp (-(A - δ) * T) := by
    rw [← Real.exp_add]; unfold akG; congr 1; field_simp; ring
  rw [← this]
  ring

/-- AKMM, p. 385: per-capita capital `k = Ke^{−nt}` obeys `k̇ = (A − δ − n)k − c` when
`K̇ = AK − e^{nt}c − δK`. -/
theorem ak_capital_to_percapita {A δ n t c : ℝ} {K : ℝ → ℝ}
    (hK : HasDerivAt K (A * K t - Real.exp (n * t) * c - δ * K t) t) :
    HasDerivAt (fun s => K s * Real.exp (-n * s))
      ((A - δ - n) * (K t * Real.exp (-n * t)) - c) t := by
  have hd := hK.fun_mul ((hasDerivAt_id' t).const_mul (-n)).exp
  convert hd using 1
  have : Real.exp (n * t) * Real.exp (-n * t) = 1 := by rw [← Real.exp_add]; simp
  linear_combination c * this

/-- AKMM, p. 385: **the closed-form policy**. With `g = (A − δ − ρ)/σ`, the path
`K(t) = K_0e^{(n+g)t}`, `c(t) = (A − δ − n − g)e^{−nt}K(t)` satisfies the resource constraint
`K̇ = AK − e^{nt}c − δK` with equality, `K̇/K = n + g`, and the Euler equation
`ċ = gc`. -/
theorem ak_policy {A δ ρ σ n K0 t : ℝ} :
    let g := akG A δ ρ σ
    let K := fun s => K0 * Real.exp ((n + g) * s)
    let c := fun s => (A - δ - n - g) * Real.exp (-n * s) * K s
    HasDerivAt K (A * K t - Real.exp (n * t) * c t - δ * K t) t ∧
      HasDerivAt K ((n + g) * K t) t ∧ HasDerivAt c (g * c t) t := by
  intro g K c
  have hK : HasDerivAt K ((n + g) * K t) t := by
    have := ((hasDerivAt_id' t).const_mul (n + g)).exp.const_mul K0
    convert this using 1
    simp only [K]; ring
  have hE : Real.exp (n * t) * Real.exp (-n * t) = 1 := by rw [← Real.exp_add]; simp
  refine ⟨?_, hK, ?_⟩
  · convert hK using 1
    simp only [c]
    linear_combination (-(A - δ - n - g) * K t) * hE
  · have hc : c = fun s => (A - δ - n - g) * K0 * Real.exp (g * s) := by
      funext s
      simp only [c, K]
      have : Real.exp (-n * s) * Real.exp ((n + g) * s) = Real.exp (g * s) := by
        rw [← Real.exp_add]; ring_nf
      rw [← this]
      ring
    rw [hc]
    have := ((hasDerivAt_id' t).const_mul g).exp.const_mul ((A - δ - n - g) * K0)
    convert this using 1
    ring

/-- AKMM, p. 385: **the boundedness condition**. For `σ > 0`, `σ(A − δ − n) > A − δ − ρ` iff
consumption on the closed-form path is positive, `A − δ − n − g > 0`, iff the discounted growth
of marginal utility times capital, `ρ − n − (1 − σ)g`, is positive. -/
theorem ak_bounded_iff {A δ ρ σ n : ℝ} (hσ : 0 < σ) :
    (A - δ - ρ < σ * (A - δ - n) ↔ 0 < A - δ - n - akG A δ ρ σ) ∧
      ρ - n - (1 - σ) * akG A δ ρ σ = A - δ - n - akG A δ ρ σ := by
  unfold akG
  constructor
  · rw [sub_pos, div_lt_iff₀ hσ]
    constructor <;> intro h <;> linarith
  · field_simp
    ring

/-- AKMM, (13.20), p. 385: on the closed-form path the transversality term
`c(T)^{−σ}e^{−ρT}K(T)` tends to zero iff `σ(A − δ − n) > A − δ − ρ` (given `K_0 > 0`
and positive consumption). -/
theorem ak_tvc {A δ ρ σ n K0 : ℝ} (hσ : 0 < σ) (hK0 : 0 < K0)
    (hpos : 0 < A - δ - n - akG A δ ρ σ) :
    Tendsto (fun T => (((A - δ - n - akG A δ ρ σ) * K0) * Real.exp (akG A δ ρ σ * T)) ^ (-σ) *
      Real.exp (-ρ * T) * (K0 * Real.exp ((n + akG A δ ρ σ) * T))) atTop (𝓝 0) := by
  have hc0 : 0 < (A - δ - n - akG A δ ρ σ) * K0 := mul_pos hpos hK0
  have e : ∀ T, (((A - δ - n - akG A δ ρ σ) * K0) * Real.exp (akG A δ ρ σ * T)) ^ (-σ) *
      Real.exp (-ρ * T) * (K0 * Real.exp ((n + akG A δ ρ σ) * T)) =
      (((A - δ - n - akG A δ ρ σ) * K0) ^ (-σ) * K0) *
        Real.exp (-(A - δ - n - akG A δ ρ σ) * T) := fun T => by
    rw [eq_13_20 hσ hc0]
    have : Real.exp (-(A - δ) * T) * Real.exp ((n + akG A δ ρ σ) * T) =
        Real.exp (-(A - δ - n - akG A δ ρ σ) * T) := by rw [← Real.exp_add]; ring_nf
    rw [← this]; ring
  simp only [e]
  exact (istc_exp_tendsto_zero_iff (by positivity)).mpr (by linarith)

/-- AKMM, p. 385: **the AK planner's optimum**. If `σ(A − δ − n) > A − δ − ρ` and `u` is
concave with `u'(c) = c^{−σ}`, the closed-form per-capita path `k(t) = k_0e^{gt}`,
`c(t) = (A − δ − n − g)k(t)` is catching-up optimal for `∫e^{−(ρ−n)t}u(c)` against every path
from `k_0` with `k̇ = (A − δ − n)k − c`, `k ≥ 0` and positive continuous consumption. -/
theorem ak_optimal {A δ ρ σ n k0 : ℝ} {u : ℝ → ℝ} {k' c' : ℝ → ℝ} (hσ : 0 < σ) (hk0 : 0 < k0)
    (hbound : A - δ - ρ < σ * (A - δ - n))
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (hk' : ∀ t, 0 ≤ t → 0 ≤ k' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hkd' : ∀ t, 0 ≤ t → HasDerivAt k' ((A - δ - n) * k' t - c' t) t) (h0 : k' 0 = k0) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) *
        u ((A - δ - n - akG A δ ρ σ) * (k0 * Real.exp (akG A δ ρ σ * t)))) + ε := by
  set g := akG A δ ρ σ
  have hpos : 0 < A - δ - n - g := (ak_bounded_iff hσ).1.mp hbound
  set m := A - δ - n - g
  set k := fun t => k0 * Real.exp (g * t)
  set c := fun t => m * k t
  set μ := fun t => Real.exp (-(ρ - n) * t) * c t ^ (-σ)
  have hcpos : ∀ t, 0 < c t := fun t => by simp only [c, k]; positivity
  have hkd : ∀ t, HasDerivAt k (g * k t) t := fun t => by
    have := ((hasDerivAt_id' t).const_mul g).exp.const_mul k0
    convert this using 1; simp only [k]; ring
  have hcd : ∀ t, HasDerivAt c (c t * ((A - δ) - ρ) / σ) t := fun t => by
    have := (hkd t).const_mul m
    convert this using 1
    simp only [c, g, akG]
    field_simp
  have hμ : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * (A - δ - n))) t := fun t _ => by
    have h := istc_costate_of_euler (n := n) hσ (hcpos t) (hcd t)
    convert h using 1
    ring
  have hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t := fun t _ => by
    have := hcpos t; simp only [μ]; positivity
  have hcc : ContinuousOn c (Set.Ici 0) := by simp only [c, k]; fun_prop
  refine (AKMM.ContinuousTime.mangasarian_catching_up (ρ := ρ - n) (u' := fun y => y ^ (-σ))
    (G := fun _ y => (A - δ - n) * y) (Gx := fun _ _ => A - δ - n) (x := k) (c := c) (μ := μ)
    hconc hu (fun t _ => hcpos t) hcc (fun t _ => ?_) hμ (fun t _ => rfl) hμ0 hc' hcc' hkd'
    (by rw [h0]; simp [k]) (fun t _ => by nlinarith) ?_).1
  · convert hkd t using 1
    simp only [c, m]
    ring
  · intro ε hε
    have htvc : Tendsto (fun T => μ T * k T) atTop (𝓝 0) := by
      have e : ∀ T, μ T * k T = (m ^ (-σ) * k0 ^ (1 - σ)) * Real.exp (-(A - δ - n - g) * T) :=
        fun T => by
          simp only [μ, c, k]
          rw [Real.mul_rpow hpos.le (by positivity), Real.mul_rpow hk0.le (Real.exp_pos _).le,
            ← Real.exp_mul, Real.rpow_sub hk0, Real.rpow_one]
          have h2 : Real.exp (-(ρ - n) * T) * Real.exp (g * T * -σ) * Real.exp (g * T) =
              Real.exp (-(A - δ - n - g) * T) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            simp only [g, akG]
            field_simp
            ring
          rw [← h2]
          have : 0 < k0 ^ σ := by positivity
          field_simp
          rw [← Real.rpow_add hk0, neg_add_cancel, Real.rpow_zero]
      simp only [e]
      exact (istc_exp_tendsto_zero_iff (by positivity)).mpr (by linarith)
    filter_upwards [htvc.eventually (gt_mem_nhds hε), eventually_ge_atTop (0 : ℝ)] with T h1 hT
    nlinarith [mul_nonneg (hμ0 T hT) (hk' T hT)]

/-- AKMM, p. 385: **decentralisation**. With competitive firms `r = A − δ` and `w = 0`, a
household with wealth `a` (per capita) and budget `ȧ = (r − n)a − c` facing the nPg
`liminf e^{−(r−n)T}a'(T) ≥ 0` finds the closed-form path optimal: it satisfies (9.24)–(9.25)
of AKMM Chapter 9 and the TVC, so `mangasarian_consumption_saving` applies. -/
theorem ak_decentralized {A δ ρ σ n k0 : ℝ} {u : ℝ → ℝ} {a' c' : ℝ → ℝ} (hσ : 0 < σ)
    (hk0 : 0 < k0) (hbound : A - δ - ρ < σ * (A - δ - n))
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (hc' : ∀ t, 0 ≤ t → 0 < c' t) (hcc' : ContinuousOn c' (Set.Ici 0))
    (ha' : ∀ t, 0 ≤ t → HasDerivAt a' (0 + (A - δ - n) * a' t - c' t) t) (h0 : a' 0 = k0)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ Real.exp (-(A - δ - n) * T) * a' T) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) *
        u ((A - δ - n - akG A δ ρ σ) * (k0 * Real.exp (akG A δ ρ σ * t)))) + ε := by
  set g := akG A δ ρ σ
  have hpos : 0 < A - δ - n - g := (ak_bounded_iff hσ).1.mp hbound
  set m := A - δ - n - g
  set k := fun t => k0 * Real.exp (g * t)
  set c := fun t => m * k t
  have hcpos : ∀ t, 0 < c t := fun t => by simp only [c, k]; positivity
  have hkd : ∀ t, HasDerivAt k (g * k t) t := fun t => by
    have := ((hasDerivAt_id' t).const_mul g).exp.const_mul k0
    convert this using 1; simp only [k]; ring
  have hcd : ∀ t, HasDerivAt c (c t * ((A - δ) - ρ) / σ) t := fun t => by
    have := (hkd t).const_mul m
    convert this using 1
    simp only [c, g, akG]
    field_simp
  have hcc : ContinuousOn c (Set.Ici 0) := by simp only [c, k]; fun_prop
  refine AKMM.ContinuousTime.mangasarian_consumption_saving (r := A - δ - n) (w := 0)
    (ρ := ρ - n) (u' := fun y => y ^ (-σ)) (a := k) (c := c)
    (μ := fun t => Real.exp (-(ρ - n) * t) * c t ^ (-σ)) hconc hu
    (fun y hy => (Real.rpow_pos_of_pos hy _).le) (fun t _ => hcpos t) hcc (fun t _ => ?_)
    (fun t _ => rfl) (fun t _ => ?_) ?_ hc' hcc' ha' (by rw [h0]; simp [k]) hnpg
  · convert hkd t using 1
    simp only [c, m]
    ring
  · have h := istc_costate_of_euler (n := n) hσ (hcpos t) (hcd t)
    convert h using 1
  · have e : ∀ T, Real.exp (-(ρ - n) * T) * c T ^ (-σ) * k T =
        (m ^ (-σ) * k0 ^ (1 - σ)) * Real.exp (-(A - δ - n - g) * T) := fun T => by
      simp only [c, k]
      rw [Real.mul_rpow hpos.le (by positivity), Real.mul_rpow hk0.le (Real.exp_pos _).le,
        ← Real.exp_mul, Real.rpow_sub hk0, Real.rpow_one]
      have h2 : Real.exp (-(ρ - n) * T) * Real.exp (g * T * -σ) * Real.exp (g * T) =
          Real.exp (-(A - δ - n - g) * T) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        simp only [g, akG]
        field_simp
        ring
      rw [← h2]
      have : 0 < k0 ^ σ := by positivity
      field_simp
      rw [← Real.rpow_add hk0, neg_add_cancel, Real.rpow_zero]
    simp only [e]
    exact (istc_exp_tendsto_zero_iff (by positivity)).mpr (by linarith)

/-- AKMM, footnote 24, p. 385: **the general solution**. Let `b = A − δ`, `q = n + g` and
`m = A − δ − n − g ≠ 0`. Every solution of `K̇ = bK − e^{qt}c(0)` on `[0, ∞)` is
`K(t) = Ξe^{bt} + (c(0)/m)e^{qt}` with the constant of integration `Ξ = K(0) − c(0)/m`. -/
theorem ak_footnote_24_general {A δ ρ σ n c0 : ℝ} {K : ℝ → ℝ}
    (hm : A - δ - n - akG A δ ρ σ ≠ 0)
    (hK : ∀ t, 0 ≤ t → HasDerivAt K ((A - δ) * K t -
      Real.exp ((n + akG A δ ρ σ) * t) * c0) t) :
    ∀ t, 0 ≤ t → K t = (K 0 - c0 / (A - δ - n - akG A δ ρ σ)) * Real.exp ((A - δ) * t) +
      c0 / (A - δ - n - akG A δ ρ σ) * Real.exp ((n + akG A δ ρ σ) * t) := by
  set g := akG A δ ρ σ
  set m := A - δ - n - g
  set f := fun s => (K s - c0 / m * Real.exp ((n + g) * s)) * Real.exp (-(A - δ) * s)
  have hf : ∀ s, 0 ≤ s → HasDerivAt f 0 s := fun s hs => by
    have h1 := ((hK s hs).fun_sub (((hasDerivAt_id' s).const_mul (n + g)).exp.const_mul
      (c0 / m))).fun_mul ((hasDerivAt_id' s).const_mul (-(A - δ))).exp
    convert h1 using 1
    have hmq : (A - δ) - (n + g) = m := by simp only [m]; ring
    have hinv : m * m⁻¹ = 1 := mul_inv_cancel₀ hm
    set e := Real.exp ((n + g) * s)
    set E := Real.exp (-(A - δ) * s)
    linear_combination (-(c0 * e * E * m⁻¹)) * hmq + (-(c0 * e * E)) * hinv
  intro t ht
  have hconst := constant_of_has_deriv_right_zero (f := f) (a := 0) (b := t)
    (fun s hs => (hf s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hf s hs.1).hasDerivWithinAt) t (Set.right_mem_Icc.mpr ht)
  simp only [f, mul_zero, Real.exp_zero, mul_one, neg_mul] at hconst
  have hE : Real.exp (-((A - δ) * t)) * Real.exp ((A - δ) * t) = 1 := by
    rw [← Real.exp_add]; simp
  have := congrArg (· * Real.exp ((A - δ) * t)) hconst
  rw [mul_assoc, hE, mul_one, neg_zero, Real.exp_zero, mul_one] at this
  linarith

/-- AKMM, footnote 24, p. 385: **the TVC forces `Ξ = 0`**. If `σ(A − δ − n) > A − δ − ρ`,
`c(0) > 0`, `K` solves `K̇ = (A − δ)K − e^{(n+g)t}c(0)` on `[0, ∞)` and the TVC
`c(0)^{−σ}e^{−(A−δ)T}K(T) → 0` (13.20) holds, then `c(0) = (A − δ − n − g)K(0)` and
`K(t) = K(0)e^{(n+g)t}`: the closed-form policy is the only solution. -/
theorem ak_footnote_24_unique {A δ ρ σ n c0 : ℝ} {K : ℝ → ℝ} (hσ : 0 < σ) (hc0 : 0 < c0)
    (hbound : A - δ - ρ < σ * (A - δ - n))
    (hK : ∀ t, 0 ≤ t → HasDerivAt K ((A - δ) * K t -
      Real.exp ((n + akG A δ ρ σ) * t) * c0) t)
    (htvc : Tendsto (fun T => c0 ^ (-σ) * Real.exp (-(A - δ) * T) * K T) atTop (𝓝 0)) :
    c0 = (A - δ - n - akG A δ ρ σ) * K 0 ∧
      ∀ t, 0 ≤ t → K t = K 0 * Real.exp ((n + akG A δ ρ σ) * t) := by
  set g := akG A δ ρ σ
  have hpos : 0 < A - δ - n - g := (ak_bounded_iff hσ).1.mp hbound
  set m := A - δ - n - g
  have hgen := ak_footnote_24_general (c0 := c0) hpos.ne' hK
  set Ξ := K 0 - c0 / m
  have hform : ∀ T, 0 ≤ T → c0 ^ (-σ) * Real.exp (-(A - δ) * T) * K T =
      c0 ^ (-σ) * Ξ + c0 ^ (-σ) * (c0 / m) * Real.exp (-m * T) := fun T hT => by
    rw [hgen T hT]
    have h1 : Real.exp (-(A - δ) * T) * Real.exp ((A - δ) * T) = 1 := by
      rw [← Real.exp_add, show -(A - δ) * T + (A - δ) * T = 0 by ring, Real.exp_zero]
    have h2 : Real.exp (-(A - δ) * T) * Real.exp ((n + g) * T) = Real.exp (-m * T) := by
      rw [← Real.exp_add]; simp only [m]; ring_nf
    linear_combination (c0 ^ (-σ) * Ξ) * h1 + (c0 ^ (-σ) * (c0 / m)) * h2
  have hlim2 : Tendsto (fun T => c0 ^ (-σ) * Ξ + c0 ^ (-σ) * (c0 / m) * Real.exp (-m * T))
      atTop (𝓝 (c0 ^ (-σ) * Ξ)) := by
    have := ((istc_exp_tendsto_zero_iff (C := c0 ^ (-σ) * (c0 / m)) (b := -m)
      (by positivity)).mpr (by linarith)).const_add (c0 ^ (-σ) * Ξ)
    simpa using this
  have hlim1 : Tendsto (fun T => c0 ^ (-σ) * Ξ + c0 ^ (-σ) * (c0 / m) * Real.exp (-m * T))
      atTop (𝓝 0) := by
    refine htvc.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT using hform T hT
  have hΞ : c0 ^ (-σ) * Ξ = 0 := tendsto_nhds_unique hlim2 hlim1
  have hΞ0 : Ξ = 0 := by
    rcases mul_eq_zero.mp hΞ with h | h
    · exact absurd h (Real.rpow_pos_of_pos hc0 _).ne'
    · exact h
  have hc0K : c0 = m * K 0 := by
    have : K 0 - c0 / m = 0 := hΞ0
    field_simp at this
    linarith
  refine ⟨hc0K, fun t ht => ?_⟩
  rw [hgen t ht, hΞ0, zero_mul, zero_add]
  change c0 / m * Real.exp ((n + g) * t) = K 0 * Real.exp ((n + g) * t)
  rw [hc0K]
  field_simp

/-- AKMM, footnote 24, p. 385: the printed `K̇/K = A − δ − e^{(n+g)t}c(0)` (without `/K(t)`)
fails on the closed-form path whenever `n + g ≠ 0`: with `K(t) = e^{(n+g)t}` and
`c(0) = A − δ − n − g > 0`, `K̇/K = n + g` is not `A − δ − e^{(n+g)t}c(0)` at `t = 1`. -/
theorem ak_footnote_24_printed_false {A δ ρ σ n : ℝ} (hq : n + akG A δ ρ σ ≠ 0)
    (hpos : 0 < A - δ - n - akG A δ ρ σ) :
    ¬ ∀ t : ℝ, n + akG A δ ρ σ =
      A - δ - Real.exp ((n + akG A δ ρ σ) * t) * (A - δ - n - akG A δ ρ σ) := by
  intro h
  have h0 := h 0
  have h1 := h 1
  simp only [mul_zero, Real.exp_zero, one_mul, mul_one] at h0 h1
  have : Real.exp (n + akG A δ ρ σ) * (A - δ - n - akG A δ ρ σ) =
      1 * (A - δ - n - akG A δ ρ σ) := by linarith
  have he : Real.exp (n + akG A δ ρ σ) = 1 := mul_right_cancel₀ hpos.ne' this
  exact hq (Real.exp_eq_one_iff _ |>.mp he)

/-- AKMM, footnote 25, p. 385: **a capital-income tax lowers growth**. With the net return
taxed at rate `τ` and the revenue `τ(A − δ)k` rebated lump-sum, the household's budget
`k̇ = ((1 − τ)(A − δ) − n)k + τ(A − δ)k − c` is the planner's resource constraint, and the
Euler growth rate `((1 − τ)(A − δ) − ρ)/σ` is strictly decreasing in `τ` when `A > δ`. -/
theorem ak_footnote_25 {A δ ρ σ n : ℝ} (hσ : 0 < σ) (hAδ : δ < A) :
    (∀ τ k c : ℝ, ((1 - τ) * (A - δ) - n) * k + τ * (A - δ) * k - c = (A - δ - n) * k - c) ∧
      StrictAnti (fun τ : ℝ => ((1 - τ) * (A - δ) - ρ) / σ) := by
  refine ⟨fun τ k c => by ring, fun τ₁ τ₂ h => ?_⟩
  simp only
  apply div_lt_div_of_pos_right _ hσ
  nlinarith

end AKMM.Growth
