/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.RomerPlanner

/-!
# Semi-endogenous growth

AKMM, §13.5.1, "Less than proportional knowledge spillovers" (pp. 393–394), footnote 36, and
Appendix 13.A.7 (pp. 854–855): Jones (1995), with `Ṅ = ηN^εL_r` (13.53), `ε < 1`, and labour
`L(t) = Le^{nt}`.

* (13.54): with profits growing at `n`, `V = π/(r* − n)` is the unique solution of the HJB
  equation without a bubble (`eq_13_54`, `jones_value_unique`).
* (13.55): free entry `V = w/(ηN^ε)` is `L_y/(r* − n) = N^{1−ε}/(η(1−φ))` (`eq_13_55`).
* (13.56): (13.55) holds for all `t` iff `Ṅ/N = n/(1−ε)` (`eq_13_56`, `eq_13_56_converse`).
* `r* = ρ + σn/(1−ε)` and the TVC (`jones_r_star`).
* (13.59): the balanced-growth `N(t)` is unique, `N = (η(1−ε)L_r/n)^{1/(1−ε)}`
  (`eq_13_59`, `jones_N_unique`).
* (13.60): output per production worker, and the level effect of scale and research intensity
  (`eq_13_60`, `jones_level_effect`); with `n = 0` growth is zero (`jones_no_growth`).
* The planner (13.A.22)–(13.A.25): the costate equation (13.A.24) is the derivative of the
  Hamiltonian (`eq_13_A_24`); the growth of `λ` (`jones_planner_lambda_growth`); balanced
  growth forces `Ṅ/N = n/(1−ε)` (`jones_planner_bgp`), which needs (13.A.24) as well as
  (13.A.25) (`jones_planner_A25_alone_insufficient`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, (13.54), p. 393: with profits `π(t) = π_0e^{nt}` and a constant interest rate `r`,
`V(t) = π_0e^{nt}/(r − n)` satisfies the HJB equation `rV = π + V̇` (p. 388). -/
theorem eq_13_54 {r n π0 t : ℝ} (hrn : r ≠ n) :
    HasDerivAt (fun s => π0 * Real.exp (n * s) / (r - n))
      (r * (π0 * Real.exp (n * t) / (r - n)) - π0 * Real.exp (n * t)) t := by
  have h := (((hasDerivAt_id' t).const_mul n).exp.const_mul π0).div_const (r - n)
  convert h using 1
  have : r - n ≠ 0 := sub_ne_zero.mpr hrn
  field_simp
  ring

/-- AKMM, (13.27) and (13.54), p. 393: **no bubble**. If `r > n` and `V` solves
`V̇ = rV − π_0e^{nt}` on `[0, ∞)` with `e^{−rT}V(T) → 0`, then `V(t) = π_0e^{nt}/(r − n)`. -/
theorem jones_value_unique {r n π0 : ℝ} {V : ℝ → ℝ} (hrn : n < r)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (r * V t - π0 * Real.exp (n * t)) t)
    (hnb : Tendsto (fun T => Real.exp (-r * T) * V T) atTop (𝓝 0)) :
    ∀ t, 0 ≤ t → V t = π0 * Real.exp (n * t) / (r - n) := by
  have hrn' : r - n ≠ 0 := (sub_pos.mpr hrn).ne'
  set f := fun s => (V s - π0 * Real.exp (n * s) / (r - n)) * Real.exp (-r * s)
  have hf : ∀ s, 0 ≤ s → HasDerivAt f 0 s := fun s hs => by
    have h1 := ((hV s hs).fun_sub (eq_13_54 (π0 := π0) (t := s) hrn.ne')).fun_mul
      ((hasDerivAt_id' s).const_mul (-r)).exp
    convert h1 using 1
    ring
  have hconst : ∀ t, 0 ≤ t → f t = f 0 := fun t ht =>
    constant_of_has_deriv_right_zero (f := f) (a := 0) (b := t)
      (fun s hs => (hf s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hf s hs.1).hasDerivWithinAt) t (Set.right_mem_Icc.mpr ht)
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h2 : Tendsto (fun T => π0 / (r - n) * Real.exp (-(r - n) * T)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (sub_pos.mpr hrn))).const_mul (π0 / (r - n))
      rw [mul_zero] at this
      refine this.congr fun T => ?_
      simp only [Function.comp_apply, id]
      ring_nf
    have := hnb.sub h2
    rw [sub_zero] at this
    refine this.congr fun T => ?_
    simp only [f]
    have : Real.exp (n * T) * Real.exp (-r * T) = Real.exp (-(r - n) * T) := by
      rw [← Real.exp_add]; ring_nf
    rw [← this]
    field_simp
  have hf0 : f 0 = 0 := by
    have hev : ∀ᶠ T in atTop, f T = f 0 := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT using hconst T hT
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' (EventuallyEq.symm hev)) hlim
  intro t ht
  have h := (hconst t ht).trans hf0
  simp only [f] at h
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · exact absurd h (Real.exp_pos _).ne'

/-- AKMM, (13.55), p. 393: **free entry**. With `V = φAX^{1/φ−1}L_y/(r* − n)` (13.54) and
`w = φ(A/(1−φ))X^{(1−φ)/φ}N` (13.36), `V = w/(ηN^ε)` iff
`L_y/(r* − n) = N^{1−ε}/(η(1−φ))`. -/
theorem eq_13_55 {A φ ψ η ε r n Ly N : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hη : 0 < η) (hN : 0 < N) (hrn : n < r) :
    φ * A * romerX A φ ψ ^ (1 / φ - 1) * Ly / (r - n) =
        φ * (A / (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) * N / (η * N ^ ε) ↔
      Ly / (r - n) = N ^ (1 - ε) / (η * (1 - φ)) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  have hrn' : 0 < r - n := sub_pos.mpr hrn
  rw [show 1 / φ - 1 = (1 - φ) / φ by field_simp]
  set P := φ * A * romerX A φ ψ ^ ((1 - φ) / φ)
  have hP : 0 < P := by positivity
  have hN1 : N ^ (1 - ε) = N / N ^ ε := by
    rw [Real.rpow_sub hN, Real.rpow_one]
  rw [hN1]
  have hNe : 0 < N ^ ε := by positivity
  rw [show φ * (A / (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) * N / (η * N ^ ε) =
    P * (N / N ^ ε / (η * (1 - φ))) by simp only [P]; field_simp,
    show P * Ly / (r - n) = P * (Ly / (r - n)) by ring]
  exact ⟨fun h => mul_left_cancel₀ hP.ne' h, fun h => by rw [h]⟩

/-- AKMM, (13.56), p. 393: **(13.55) for all `t` forces `Ṅ/N = n/(1−ε)`**. If
`L_y(t) = L_{y0}e^{nt}`, `N > 0` is differentiable at `t` and (13.55) holds at every date,
then `Ṅ(t)/N(t) = n/(1−ε)`. -/
theorem eq_13_56 {φ η ε r n Ly0 t Ndot : ℝ} {N : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hε : ε < 1) (hrn : n < r) (hLy0 : 0 < Ly0) (hN : ∀ s, 0 < N s)
    (hNd : HasDerivAt N Ndot t)
    (h1355 : ∀ s, Ly0 * Real.exp (n * s) / (r - n) = N s ^ (1 - ε) / (η * (1 - φ))) :
    Ndot / N t = n / (1 - ε) := by
  have h1φ : 0 < 1 - φ := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  have hrn' : 0 < r - n := sub_pos.mpr hrn
  set κ := η * (1 - φ) * Ly0 / (r - n)
  have hκ : 0 < κ := by positivity
  have hNform : N = fun s => κ ^ (1 / (1 - ε)) * Real.exp (n / (1 - ε) * s) := by
    funext s
    have h1 := h1355 s
    have hpow : N s ^ (1 - ε) = κ * Real.exp (n * s) := by
      simp only [κ]; field_simp at h1 ⊢; linarith
    have := congrArg (fun x : ℝ => x ^ (1 / (1 - ε))) hpow
    rw [← Real.rpow_mul (hN s).le, mul_one_div_cancel h1ε.ne', Real.rpow_one,
      Real.mul_rpow hκ.le (Real.exp_pos _).le, ← Real.exp_mul] at this
    rw [this]
    congr 2
    ring
  have hd : HasDerivAt N (n / (1 - ε) * N t) t := by
    rw [hNform]
    have := ((hasDerivAt_id' t).const_mul (n / (1 - ε))).exp.const_mul (κ ^ (1 / (1 - ε)))
    convert this using 1
    ring
  rw [hNd.unique hd]
  field_simp [(hN t).ne']

/-- AKMM, (13.56), p. 393, converse: if `N` grows at `n/(1−ε)` and (13.55) holds at `t = 0`,
it holds at every date (with `L_y(t) = L_{y0}e^{nt}`). -/
theorem eq_13_56_converse {φ η ε r n Ly0 N0 : ℝ} (hε : ε < 1) (hN0 : 0 < N0)
    (h0 : Ly0 / (r - n) = N0 ^ (1 - ε) / (η * (1 - φ))) (s : ℝ) :
    Ly0 * Real.exp (n * s) / (r - n) =
      (N0 * Real.exp (n / (1 - ε) * s)) ^ (1 - ε) / (η * (1 - φ)) := by
  have h1ε : (1 - ε) ≠ 0 := by linarith
  rw [Real.mul_rpow hN0.le (Real.exp_pos _).le, ← Real.exp_mul,
    show n / (1 - ε) * s * (1 - ε) = n * s by field_simp]
  rw [show Ly0 * Real.exp (n * s) / (r - n) = Ly0 / (r - n) * Real.exp (n * s) by ring, h0]
  ring

/-- AKMM, p. 393: the interest rate `r* = ρ + σn/(1−ε)` from the Euler equation, and the TVC:
if `ρ − n > n/(1−ε)` and `σ > 0` then `r* − n > n/(1−ε) ≥ 0` (for `n ≥ 0`), so household wealth,
which grows at `n/(1−ε)` per capita, satisfies `e^{−(r*−n)T}a(T) → 0`. -/
theorem jones_r_star {σ ρ n ε a0 : ℝ} (hσ : 0 < σ) (hε : ε < 1) (hn : 0 ≤ n)
    (hbound : n / (1 - ε) < ρ - n) (ha0 : 0 < a0) :
    n / (1 - ε) < ρ + σ * (n / (1 - ε)) - n ∧
      Tendsto (fun T => Real.exp (-(ρ + σ * (n / (1 - ε)) - n) * T) *
        (a0 * Real.exp (n / (1 - ε) * T))) atTop (𝓝 0) := by
  have h1ε : 0 < 1 - ε := by linarith
  have hg : 0 ≤ n / (1 - ε) := div_nonneg hn h1ε.le
  have hlt : n / (1 - ε) < ρ + σ * (n / (1 - ε)) - n := by nlinarith
  refine ⟨hlt, ?_⟩
  have e : ∀ T, Real.exp (-(ρ + σ * (n / (1 - ε)) - n) * T) * (a0 * Real.exp (n / (1 - ε) * T)) =
      a0 * Real.exp ((n / (1 - ε) - (ρ + σ * (n / (1 - ε)) - n)) * T) := fun T => by
    rw [mul_left_comm, ← Real.exp_add]; ring_nf
  simp only [e]
  exact (istc_exp_tendsto_zero_iff ha0).mpr (by linarith)

/-- AKMM, (13.59), p. 394: on the balanced growth path, `Ṅ/N = ηN^{ε−1}L_r = n/(1−ε)` gives
`L_r = nN^{1−ε}/(η(1−ε))`, i.e. `N = (η(1−ε)L_r/n)^{1/(1−ε)}`. -/
theorem eq_13_59 {η ε n N Lr : ℝ} (hη : 0 < η) (hε : ε < 1) (hn : 0 < n) (hN : 0 < N)
    (h : η * N ^ (ε - 1) * Lr = n / (1 - ε)) :
    Lr = n * N ^ (1 - ε) / (η * (1 - ε)) ∧ N = (η * (1 - ε) * Lr / n) ^ (1 / (1 - ε)) := by
  have h1ε : 0 < 1 - ε := by linarith
  have hNe : N ^ (ε - 1) * N ^ (1 - ε) = 1 := by
    rw [← Real.rpow_add hN, show ε - 1 + (1 - ε) = 0 by ring, Real.rpow_zero]
  have hLr : Lr = n * N ^ (1 - ε) / (η * (1 - ε)) := by
    have hp : 0 < N ^ (1 - ε) := by positivity
    field_simp
    have := congrArg (· * N ^ (1 - ε)) h
    rw [show η * N ^ (ε - 1) * Lr * N ^ (1 - ε) = η * Lr * (N ^ (ε - 1) * N ^ (1 - ε)) by ring,
      hNe] at this
    field_simp at this
    linarith
  refine ⟨hLr, ?_⟩
  rw [hLr, show η * (1 - ε) * (n * N ^ (1 - ε) / (η * (1 - ε))) / n = N ^ (1 - ε) by
    field_simp, ← Real.rpow_mul hN.le, mul_one_div_cancel h1ε.ne', Real.rpow_one]

/-- AKMM, (13.59) with (13.55), p. 394: **the balanced-growth `N(t)` is unique**. With
labour-market clearing `L_y + L_r = Le^{nt}`, (13.55) and (13.59) give
`N(t)^{1−ε} = ηLe^{nt}/(n/(1−ε) + (r* − n)/(1−φ))`. -/
theorem jones_N_unique {φ η ε r n L t N Ly Lr : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hε : ε < 1)
    (hn : 0 < n) (hrn : n < r)
    (h1355 : Ly / (r - n) = N ^ (1 - ε) / (η * (1 - φ)))
    (h1359 : Lr = n * N ^ (1 - ε) / (η * (1 - ε)))
    (hclear : Ly + Lr = L * Real.exp (n * t)) :
    N ^ (1 - ε) = η * L * Real.exp (n * t) / (n / (1 - ε) + (r - n) / (1 - φ)) := by
  have h1φ : 0 < 1 - φ := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  have hrn' : 0 < r - n := sub_pos.mpr hrn
  have hden : 0 < n / (1 - ε) + (r - n) / (1 - φ) := by positivity
  rw [eq_div_iff hden.ne']
  have hLy : Ly = (r - n) * N ^ (1 - ε) / (η * (1 - φ)) := by
    field_simp at h1355 ⊢; linarith
  rw [mul_assoc η, ← hclear, hLy, h1359]
  field_simp
  ring

/-- AKMM, (13.60), p. 394: with `N = (η(1−ε)L_r/n)^{1/(1−ε)}` in (13.35), output per production
worker is `Y/L_y = 𝒜(L_r/L)^{1/(1−ε)}L^{1/(1−ε)}` with the constant
`𝒜 = (A/(1−φ))X^{(1−φ)/φ}(η(1−ε)/n)^{1/(1−ε)}`. -/
theorem eq_13_60 {A φ ψ η ε n Lr L : ℝ} (hη : 0 < η) (hε : ε < 1) (hn : 0 < n) (hLr : 0 ≤ Lr)
    (hL : 0 < L) :
    A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * (η * (1 - ε) * Lr / n) ^ (1 / (1 - ε)) =
      A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * (η * (1 - ε) / n) ^ (1 / (1 - ε)) *
        ((Lr / L) ^ (1 / (1 - ε)) * L ^ (1 / (1 - ε))) := by
  have h1ε : 0 < 1 - ε := by linarith
  rw [← Real.mul_rpow (div_nonneg hLr hL.le) hL.le, div_mul_cancel₀ _ hL.ne',
    mul_assoc (A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ)),
    ← Real.mul_rpow (by positivity) hLr]
  congr 2
  ring

/-- AKMM, p. 394: **level effects**. For a given research intensity `L_r/L > 0`, output per
production worker `𝒜(L_r/L)^{1/(1−ε)}L^{1/(1−ε)}` (with `𝒜 > 0`) is strictly increasing in the
scale `L > 0`, and for given `L` strictly increasing in the research intensity. -/
theorem jones_level_effect {𝒜 ε s : ℝ} (h𝒜 : 0 < 𝒜) (hε : ε < 1) (hs : 0 < s) :
    StrictMonoOn (fun L : ℝ => 𝒜 * (s ^ (1 / (1 - ε)) * L ^ (1 / (1 - ε)))) (Set.Ioi 0) ∧
      ∀ L : ℝ, 0 < L →
        StrictMonoOn (fun s' : ℝ => 𝒜 * (s' ^ (1 / (1 - ε)) * L ^ (1 / (1 - ε)))) (Set.Ioi 0) := by
  have h1ε : 0 < 1 / (1 - ε) := by apply div_pos one_pos; linarith
  refine ⟨fun a ha b _ hab => ?_, fun L hL a ha b _ hab => ?_⟩
  · have := Real.rpow_lt_rpow (le_of_lt ha) hab h1ε
    have hsp : 0 < s ^ (1 / (1 - ε)) := by positivity
    simp only
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left this hsp) h𝒜
  · have := Real.rpow_lt_rpow (le_of_lt ha) hab h1ε
    have hLp : 0 < L ^ (1 / (1 - ε)) := by positivity
    simp only
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right this hLp) h𝒜

/-- AKMM, p. 394: without population growth there is no sustained growth: `n/(1−ε) = 0` when
`n = 0`; and the growth rate rises with the spillover `ε` when `n > 0`. -/
theorem jones_no_growth {ε : ℝ} : (0 : ℝ) / (1 - ε) = 0 ∧
    ∀ n : ℝ, 0 < n → StrictMonoOn (fun e : ℝ => n / (1 - e)) (Set.Iio 1) := by
  refine ⟨zero_div _, fun n hn a ha b hb hab => ?_⟩
  simp only [Set.mem_Iio] at ha hb
  exact div_lt_div_of_pos_left hn (by linarith) (by linarith)

/-- AKMM, (13.A.24), p. 854: the derivative in `N` of the bracket of the Hamiltonian
(13.A.22), `N^εLe^{nt} − cN^{−1}N^{ε}/M`, i.e. `N^εLe^{nt} − cN^{ε−1}/M`, is
`εN^{ε−1}Le^{nt} + (1−ε)cN^{ε−2}/M`. -/
theorem eq_13_A_24 {ε L n t c M N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun y => y ^ ε * (L * Real.exp (n * t)) - c * y ^ (ε - 1) / M)
      (ε * N ^ (ε - 1) * (L * Real.exp (n * t)) + (1 - ε) * c * N ^ (ε - 2) / M) N := by
  have h1 := (Real.hasDerivAt_rpow_const (p := ε) (Or.inl hN.ne')).mul_const
    (L * Real.exp (n * t))
  have h2 := ((Real.hasDerivAt_rpow_const (p := ε - 1) (Or.inl hN.ne')).const_mul c).div_const M
  convert h1.sub h2 using 1
  rw [show ε - 1 - 1 = ε - 2 by ring]
  ring

/-- AKMM, (13.A.23), p. 855: if `λ = e^{−(ρ−n)t}c^{−σ}N^{1−ε}K` (`K = (ψ/η)(A/ψ)^{1/φ}φ/(1−φ)`),
then `λ̇/λ = −σċ/c + (1−ε)Ṅ/N − (ρ − n)`. -/
theorem jones_planner_lambda_growth {σ ρ n ε K t cdot Ndot : ℝ} {c N : ℝ → ℝ} (hc : 0 < c t)
    (hN : 0 < N t) (hcd : HasDerivAt c cdot t) (hNd : HasDerivAt N Ndot t) :
    HasDerivAt (fun s => Real.exp (-(ρ - n) * s) * c s ^ (-σ) * N s ^ (1 - ε) * K)
      ((-σ * (cdot / c t) + (1 - ε) * (Ndot / N t) - (ρ - n)) *
        (Real.exp (-(ρ - n) * t) * c t ^ (-σ) * N t ^ (1 - ε) * K)) t := by
  have h1 := ((hasDerivAt_id' t).const_mul (-(ρ - n))).exp
  have h2 := hcd.rpow_const (p := -σ) (Or.inl hc.ne')
  have h3 := hNd.rpow_const (p := 1 - ε) (Or.inl hN.ne')
  convert ((h1.fun_mul h2).fun_mul h3).mul_const K using 1
  rw [Real.rpow_sub_one hc.ne', Real.rpow_sub_one hN.ne']
  field_simp
  ring

/-- AKMM, App. 13.A.7, p. 855: **planner's balanced growth**. Along `N = N_0e^{gt}`, if the
growth rate of `N` from (13.A.25), `ηN^{ε−1}Le^{nt} − ηcN^{ε−2}/M`, and the bracket of (13.A.24),
`εN^{ε−1}Le^{nt} + (1−ε)cN^{ε−2}/M`, are both constant in `t`, then `N^{ε−1}Le^{nt}` is constant
and `g = n/(1−ε)`. -/
theorem jones_planner_bgp {η ε n L M N0 g k1 k2 : ℝ} {c : ℝ → ℝ} (hη : 0 < η) (hε : ε < 1)
    (hL : 0 < L) (hN0 : 0 < N0)
    (h25 : ∀ t, η * (N0 * Real.exp (g * t)) ^ (ε - 1) * L * Real.exp (n * t) -
      η * c t * (N0 * Real.exp (g * t)) ^ (ε - 2) / M = k1)
    (h24 : ∀ t, ε * (N0 * Real.exp (g * t)) ^ (ε - 1) * L * Real.exp (n * t) +
      (1 - ε) * c t * (N0 * Real.exp (g * t)) ^ (ε - 2) / M = k2) :
    g = n / (1 - ε) := by
  have h1ε : 0 < 1 - ε := by linarith
  have hu : ∀ t, (N0 * Real.exp (g * t)) ^ (ε - 1) * L * Real.exp (n * t) =
      ((1 - ε) * k1 / η + k2) := fun t => by
    have a := h25 t
    have b := h24 t
    have hab : (N0 * Real.exp (g * t)) ^ (ε - 1) * L * Real.exp (n * t) -
        c t * (N0 * Real.exp (g * t)) ^ (ε - 2) / M = k1 / η := by
      rw [eq_div_iff hη.ne']; linear_combination a
    linear_combination (1 - ε) * hab + b
  have hform : ∀ t, (N0 * Real.exp (g * t)) ^ (ε - 1) * L * Real.exp (n * t) =
      N0 ^ (ε - 1) * L * Real.exp (((ε - 1) * g + n) * t) := fun t => by
    rw [Real.mul_rpow hN0.le (Real.exp_pos _).le, ← Real.exp_mul]
    have : Real.exp (g * t * (ε - 1)) * Real.exp (n * t) = Real.exp (((ε - 1) * g + n) * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [← this]; ring
  have h0 := hu 0
  have h1 := hu 1
  rw [hform] at h0 h1
  simp only [mul_zero, Real.exp_zero, mul_one] at h0 h1
  have hc : 0 < N0 ^ (ε - 1) * L := by positivity
  have he : Real.exp ((ε - 1) * g + n) = 1 := by
    have : N0 ^ (ε - 1) * L * Real.exp ((ε - 1) * g + n) = N0 ^ (ε - 1) * L * 1 := by
      linarith
    exact mul_left_cancel₀ hc.ne' this
  have := Real.exp_eq_one_iff _ |>.mp he
  field_simp
  linarith

/-- AKMM, App. 13.A.7, p. 855: **(13.A.25) alone does not force `N^{ε−1}Le^{nt}` constant**.
With `n > 0`, `N ≡ N_0` and `c(t) = MN_0Le^{nt}`, the law of motion (13.A.25)
`Ṅ = ηN^ε(Le^{nt} − cN^{−1}/M)` holds (both sides are `0`) and `Ṅ/N`, `ċ/c` are constant, yet
`N^{ε−1}Le^{nt}` is not constant; it is (13.A.24) that rules this out. -/
theorem jones_planner_A25_alone_insufficient {η ε n L M N0 : ℝ} (hn : 0 < n) (hL : 0 < L)
    (hM : 0 < M) (hN0 : 0 < N0) :
    (∀ t, (0 : ℝ) = η * N0 ^ ε * (L * Real.exp (n * t) -
      M * N0 * L * Real.exp (n * t) * N0⁻¹ / M)) ∧
    N0 ^ (ε - 1) * L * Real.exp (n * 0) ≠ N0 ^ (ε - 1) * L * Real.exp (n * 1) := by
  refine ⟨fun t => by field_simp; ring, fun h => ?_⟩
  have hc : 0 < N0 ^ (ε - 1) * L := by positivity
  have := mul_left_cancel₀ hc.ne' h
  simp only [mul_zero, Real.exp_zero, mul_one] at this
  have := (Real.exp_eq_one_iff n).mp this.symm
  linarith

end AKMM.Growth
