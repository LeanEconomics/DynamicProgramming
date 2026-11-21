/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.JDBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Unemployment and business cycles (Miao §18.3, pp. 607–614)

Miao, *Economic Dynamics in Discrete Time*, §18.3: the DMP model embedded in an RBC economy
(Merz 1995, Andolfatto 1996). The aggregate state follows a Markov chain; at a node the next
period's states `s` range over a finite type `S` with probabilities `p s`, so `E_t X_{t+1} =
∑ s, p s * X s`. Value functions are given functions whose maximising property is a hypothesis
("`V = max obj`": `obj ≤ V` everywhere with equality at the optimum); first-order and envelope
conditions are then proved from differentiability by `jd_foc` and `jd_envelope`.

**Households** (pp. 608–610; objective `jd_hhObj`, budget (18.46), capital (18.47), employment
(18.48) with `q^u = f` taken as given):
* the first-order condition for investment and the envelope condition for capital
  (`jd_hh_foc_I`, `jd_hh_envelope_K`) and the Euler equation (18.49) (`eq_18_49`);
* the envelope condition for employment (p. 609) (`jd_hh_envelope_N`) and the household surplus
  recursion (18.50) (`eq_18_50`);
* the marginal value `V_n(w, t) = Λ_t (w − w_t) + ∂V_t/∂N_t` of hiring one more member at wage
  `w` (`jd_hh_Vn`). **Correction**: this requires the new member to give up the benefit `b`; with
  the budget printed on p. 610 (`b (1 − N_t)`, benefit kept) the derivative is
  `Λ_t (w − w_t) + ∂V_t/∂N_t + Λ_t b` (`jd_hh_Vn_book_budget`), so the book's second equality
  fails when `b ≠ 0`. The first line of the book's display omits `−Λ_t b` correspondingly;
* the disutility microfoundation `∫₀^N χ j^φ dj = χ N^{1+φ}/(1+φ)` (`jd_disutility_integral`)
  and the derivatives of the CRRA utility and of the disutility (`jd_crra_hasDerivAt`,
  `jd_disutility_hasDerivAt`).

**Firms** (pp. 610–612; objective `jd_firmObj`, employment law (18.22)): (18.51) (`eq_18_51`),
(18.52) (`eq_18_52`), the envelope condition (18.53) (`eq_18_53`), the firm surplus (18.54)
(`eq_18_54`), the job creation condition (18.55) (`eq_18_55`), the marginal value
`J_n(w, t) = w_t − w + ∂J_t/∂N_t` (`jd_firm_Jn`); `K^j/N^j` is the same for all firms
(`jd_capital_ratio_indep`, from constant returns, `jd_partial_homog_one`).

**Nash bargaining** (pp. 612–613): `w_t` maximises `V_n^η J_n^(1−η)` at `w = w_t` iff
`(1 − η) S^H_t = η S^F_t` (`jd_nash_18_3`); the wage (18.56) (`eq_18_56`), the same for all
firms (`jd_wage_indep`).

**Equilibrium** (p. 614): aggregation `∫ F(K^j, A N^j) dj = F(K, A N)` (`jd_aggregate_output`,
finitely many firm types with masses `ω_j`), consistency of the firms' and households' employment
laws (`jd_employment_consistency`), and the resource constraint
`C_t + K_{t+1} − (1 − δ) K_t = F(K_t, A_t N_t) − κ v_t` (`jd_resource_constraint`).

The text derives no steady state, log-linearisation or simulation for this model; the steady
state used for calibration (Exercise 18.5) is in `JDExercises`.
-/

namespace Miao.SearchAndMatching

open Filter Topology

/-- Miao, (18.46)–(18.48), p. 609: the household's objective at a node, with consumption from
the budget `C = D + R K + w N + b (1 − N) − T − I` (written `R K + (w − b) N + (b + D − T) − I`),
next capital `(1 − δ) K + I` and next employment `(1 − ρ) N + f (1 − N) = (1 − ρ − f) N + f`. -/
noncomputable def jd_hhObj {S : Type*} [Fintype S] (u : ℝ → ℝ) (p : S → ℝ)
    (Vn : S → ℝ → ℝ → ℝ) (β δ χ φ ρ f R w b D T K N I : ℝ) : ℝ :=
  u (R * K + (w - b) * N + (b + D - T) - I) - χ * N ^ (1 + φ) / (1 + φ) +
    β * ∑ s, p s * Vn s ((1 - δ) * K + I) ((1 - ρ - f) * N + f)

/-- Miao, (18.46) and (18.48), p. 609: the two forms of the budget and employment law agree. -/
theorem jd_hh_budget_forms (R w b D T K N I ρ f : ℝ) :
    D + R * K + w * N + b * (1 - N) - T - I = R * K + (w - b) * N + (b + D - T) - I ∧
      (1 - ρ) * N + f * (1 - N) = (1 - ρ - f) * N + f := by
  constructor <;> ring

/-- Miao, p. 608: the CRRA utility `(C^{1−γ} − 1)/(1 − γ)` has marginal utility `Λ = C^{−γ}`. -/
theorem jd_crra_hasDerivAt {γ C : ℝ} (hγ : γ ≠ 1) (hC : 0 < C) :
    HasDerivAt (fun x => (x ^ (1 - γ) - 1) / (1 - γ)) (C ^ (-γ)) C := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hC.ne')).sub_const 1).div_const
    (1 - γ)
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  convert h using 1
  field_simp
  ring_nf

/-- Miao, p. 608: the disutility `χ N^{1+φ}/(1 + φ)` has derivative `χ N^φ` at `N > 0`. -/
theorem jd_disutility_hasDerivAt {χ φ N : ℝ} (hφ : 0 < φ) (hN : 0 < N) :
    HasDerivAt (fun x => χ * x ^ (1 + φ) / (1 + φ)) (χ * N ^ φ) N := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1 + φ) (Or.inl hN.ne')).const_mul χ).div_const
    (1 + φ)
  have h1 : (1 + φ) ≠ 0 := by linarith
  convert h using 1
  field_simp
  ring_nf

/-- Miao, p. 608 (microfoundation of the disutility of work): if member `j ∈ [0, N]` has
disutility `χ j^φ`, total disutility is `∫₀^N χ j^φ dj = χ N^{1+φ}/(1 + φ)`. -/
theorem jd_disutility_integral {χ φ N : ℝ} (hφ : 0 < φ) :
    ∫ j in (0 : ℝ)..N, χ * j ^ φ = χ * N ^ (1 + φ) / (1 + φ) := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  have h0 : (0 : ℝ) ^ (φ + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0, add_comm φ 1]
  ring

/-- Miao, p. 609: the first-order condition for investment, `Λ_t = β E_t ∂V_{t+1}/∂K_{t+1}`. -/
theorem jd_hh_foc_I {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {Vn : S → ℝ → ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} {β δ χ φ ρ f R w b D T K₀ N₀ I₀ Λ : ℝ} {VK : S → ℝ}
    (hmax : ∀ K N I, jd_hhObj u p Vn β δ χ φ ρ f R w b D T K N I ≤ V K N)
    (hopt : jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N₀ I₀ = V K₀ N₀)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVK : ∀ s, HasDerivAt (fun k => Vn s k ((1 - ρ - f) * N₀ + f)) (VK s) ((1 - δ) * K₀ + I₀)) :
    Λ = β * ∑ s, p s * VK s := by
  have hin : HasDerivAt (fun I => R * K₀ + (w - b) * N₀ + (b + D - T) - I) (-1) I₀ := by
    simpa using (hasDerivAt_id I₀).const_sub (R * K₀ + (w - b) * N₀ + (b + D - T))
  have hin2 : HasDerivAt (fun I => (1 - δ) * K₀ + I) 1 I₀ := by
    simpa using (hasDerivAt_id I₀).const_add ((1 - δ) * K₀)
  have hsum : HasDerivAt (fun I => ∑ s, p s * Vn s ((1 - δ) * K₀ + I) ((1 - ρ - f) * N₀ + f))
      (∑ s, p s * (VK s * 1)) I₀ :=
    HasDerivAt.fun_sum fun s _ => ((hVK s).comp_of_eq I₀ hin2 (by ring)).const_mul (p s)
  have hd := (((hu.comp I₀ hin).sub_const (χ * N₀ ^ (1 + φ) / (1 + φ))).add
    (hsum.const_mul β))
  have := jd_foc (h := fun I => jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N₀ I)
    (fun I => (hmax K₀ N₀ I).trans hopt.ge) hd
  simp only [mul_one, mul_neg] at this
  linarith

/-- Miao, p. 609: the envelope condition for capital,
`∂V_t/∂K_t = Λ_t (R_{kt} + 1 − δ)` (using the first-order condition for investment). -/
theorem jd_hh_envelope_K {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ}
    {Vn : S → ℝ → ℝ → ℝ} {V : ℝ → ℝ → ℝ} {β δ χ φ ρ f R w b D T K₀ N₀ I₀ Λ VK₀ : ℝ}
    {VK : S → ℝ}
    (hmax : ∀ K N I, jd_hhObj u p Vn β δ χ φ ρ f R w b D T K N I ≤ V K N)
    (hopt : jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N₀ I₀ = V K₀ N₀)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVK : ∀ s, HasDerivAt (fun k => Vn s k ((1 - ρ - f) * N₀ + f)) (VK s) ((1 - δ) * K₀ + I₀))
    (hV : HasDerivAt (fun k => V k N₀) VK₀ K₀) : VK₀ = Λ * (R + 1 - δ) := by
  have hfoc := jd_hh_foc_I hmax hopt hu hVK
  have hin : HasDerivAt (fun K => R * K + (w - b) * N₀ + (b + D - T) - I₀) R K₀ := by
    simpa using ((((hasDerivAt_id K₀).const_mul R).add_const ((w - b) * N₀)).add_const
      (b + D - T)).sub_const I₀
  have hin2 : HasDerivAt (fun K => (1 - δ) * K + I₀) (1 - δ) K₀ := by
    simpa using ((hasDerivAt_id K₀).const_mul (1 - δ)).add_const I₀
  have hsum : HasDerivAt (fun K => ∑ s, p s * Vn s ((1 - δ) * K + I₀) ((1 - ρ - f) * N₀ + f))
      (∑ s, p s * (VK s * (1 - δ))) K₀ :=
    HasDerivAt.fun_sum fun s _ => ((hVK s).comp_of_eq K₀ hin2 (by ring)).const_mul (p s)
  have hd := (((hu.comp K₀ hin).sub_const (χ * N₀ ^ (1 + φ) / (1 + φ))).add
    (hsum.const_mul β))
  have := jd_envelope (g := fun K => jd_hhObj u p Vn β δ χ φ ρ f R w b D T K N₀ I₀)
    (fun K => hmax K N₀ I₀) hopt hV hd
  rw [this]
  have e : ∑ s, p s * (VK s * (1 - δ)) = (1 - δ) * ∑ s, p s * VK s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  have : β * ((1 - δ) * ∑ s, p s * VK s) = (1 - δ) * Λ := by rw [hfoc]; ring
  linarith

/-- **The Euler equation** (Miao, (18.49), p. 609):
`Λ_t = β E_t [Λ_{t+1} (R_{k,t+1} + 1 − δ)]`, from the first-order condition for investment and
the envelope condition for capital at `t + 1` (`jd_hh_envelope_K` applied in each state). -/
theorem eq_18_49 {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {Vn : S → ℝ → ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} {β δ χ φ ρ f R w b D T K₀ N₀ I₀ Λ : ℝ} {VK Λn Rn : S → ℝ}
    (hmax : ∀ K N I, jd_hhObj u p Vn β δ χ φ ρ f R w b D T K N I ≤ V K N)
    (hopt : jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N₀ I₀ = V K₀ N₀)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVK : ∀ s, HasDerivAt (fun k => Vn s k ((1 - ρ - f) * N₀ + f)) (VK s) ((1 - δ) * K₀ + I₀))
    (henv : ∀ s, VK s = Λn s * (Rn s + 1 - δ)) :
    Λ = β * ∑ s, p s * (Λn s * (Rn s + 1 - δ)) := by
  rw [jd_hh_foc_I hmax hopt hu hVK]
  simp only [henv]

/-- Miao, p. 609: the envelope condition for employment,
`∂V_t/∂N_t = Λ_t (w_t − b) − χ N_t^φ + (1 − ρ − q(θ_t) θ_t) β E_t ∂V_{t+1}/∂N_{t+1}`. -/
theorem jd_hh_envelope_N {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ}
    {Vn : S → ℝ → ℝ → ℝ} {V : ℝ → ℝ → ℝ} {β δ χ φ ρ f R w b D T K₀ N₀ I₀ Λ VN₀ : ℝ}
    {VN : S → ℝ} (hφ : 0 < φ) (hN : 0 < N₀)
    (hmax : ∀ K N I, jd_hhObj u p Vn β δ χ φ ρ f R w b D T K N I ≤ V K N)
    (hopt : jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N₀ I₀ = V K₀ N₀)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVN : ∀ s, HasDerivAt (fun n => Vn s ((1 - δ) * K₀ + I₀) n) (VN s) ((1 - ρ - f) * N₀ + f))
    (hV : HasDerivAt (fun n => V K₀ n) VN₀ N₀) :
    VN₀ = Λ * (w - b) - χ * N₀ ^ φ + (1 - ρ - f) * (β * ∑ s, p s * VN s) := by
  have hin : HasDerivAt (fun N => R * K₀ + (w - b) * N + (b + D - T) - I₀) (w - b) N₀ := by
    simpa using ((((hasDerivAt_id N₀).const_mul (w - b)).const_add (R * K₀)).add_const
      (b + D - T)).sub_const I₀
  have hin2 : HasDerivAt (fun N => (1 - ρ - f) * N + f) (1 - ρ - f) N₀ := by
    simpa using ((hasDerivAt_id N₀).const_mul (1 - ρ - f)).add_const f
  have hsum : HasDerivAt (fun N => ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * N + f))
      (∑ s, p s * (VN s * (1 - ρ - f))) N₀ :=
    HasDerivAt.fun_sum fun s _ => ((hVN s).comp_of_eq N₀ hin2 (by ring)).const_mul (p s)
  have hd := (((hu.comp N₀ hin).sub (jd_disutility_hasDerivAt (χ := χ) hφ hN)).add
    (hsum.const_mul β))
  have := jd_envelope (g := fun N => jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N I₀)
    (fun N => hmax K₀ N I₀) hopt hV hd
  rw [this]
  have e : ∑ s, p s * (VN s * (1 - ρ - f)) = (1 - ρ - f) * ∑ s, p s * VN s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  ring

/-- Miao, (18.50), p. 609: with `S^H_t = (∂V_t/∂N_t)/Λ_t` and `∂V_{t+1}/∂N_{t+1} = Λ_{t+1}
S^H_{t+1}`, `S^H_t = w_t − b − χ N_t^φ/Λ_t + (1 − ρ − q(θ_t)θ_t) E_t[(β Λ_{t+1}/Λ_t) S^H_{t+1}]`. -/
theorem eq_18_50 {S : Type*} [Fintype S] {p : S → ℝ} {β χ φ ρ f w b N₀ Λ VN₀ : ℝ}
    {VN Λn SHn : S → ℝ} (hΛ : Λ ≠ 0)
    (henv : VN₀ = Λ * (w - b) - χ * N₀ ^ φ + (1 - ρ - f) * (β * ∑ s, p s * VN s))
    (hnext : ∀ s, VN s = Λn s * SHn s) :
    VN₀ / Λ = w - b - χ * N₀ ^ φ / Λ + (1 - ρ - f) * ∑ s, p s * (β * Λn s / Λ * SHn s) := by
  rw [henv]
  simp only [hnext]
  have e : ∑ s, p s * (β * Λn s / Λ * SHn s) = (β * ∑ s, p s * (Λn s * SHn s)) / Λ := by
    rw [Finset.mul_sum, Finset.sum_div]; congr 1; funext s; field_simp
  rw [e]
  field_simp

/-- Miao, p. 610 (corrected budget): if an additional member `ε` is hired at wage `w̃` and gives
up the benefit `b`, the marginal value is `V_n(w̃, t) = Λ_t (w̃ − w_t) + ∂V_t/∂N_t`. Here `Ṽ(ε)`
is the value with `N_t + ε` members (`Ṽ ≥` the objective at the optimal investment `I₀`, equality
at `ε = 0`) and `∂V_t/∂N_t` is given by `jd_hh_envelope_N`. -/
theorem jd_hh_Vn {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {Vn : S → ℝ → ℝ → ℝ}
    {Vt : ℝ → ℝ} {β δ χ φ ρ f R w w' b D T K₀ N₀ I₀ Λ VN₀ dV : ℝ} {VN : S → ℝ}
    (hφ : 0 < φ) (hN : 0 < N₀)
    (hle : ∀ ε, u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + (w' - b) * ε) -
      χ * (N₀ + ε) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f) ≤ Vt ε)
    (heq : u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + (w' - b) * 0) -
      χ * (N₀ + 0) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + 0) + f) = Vt 0)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVN : ∀ s, HasDerivAt (fun n => Vn s ((1 - δ) * K₀ + I₀) n) (VN s) ((1 - ρ - f) * N₀ + f))
    (hVt : HasDerivAt Vt dV 0)
    (henv : VN₀ = Λ * (w - b) - χ * N₀ ^ φ + (1 - ρ - f) * (β * ∑ s, p s * VN s)) :
    dV = Λ * (w' - w) + VN₀ := by
  have hin : HasDerivAt (fun ε => R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + (w' - b) * ε)
      (w' - b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (w' - b)).const_add
      (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀)
  have hin2 : HasDerivAt (fun ε => (1 - ρ - f) * (N₀ + ε) + f) (1 - ρ - f) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add N₀).const_mul (1 - ρ - f)).add_const f
  have hin3 : HasDerivAt (fun ε : ℝ => N₀ + ε) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add N₀
  have hsum : HasDerivAt
      (fun ε => ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f))
      (∑ s, p s * (VN s * (1 - ρ - f))) 0 :=
    HasDerivAt.fun_sum fun s _ =>
      ((hVN s).comp_of_eq 0 hin2 (by ring)).const_mul (p s)
  have hdis := (jd_disutility_hasDerivAt (χ := χ) hφ hN).comp_of_eq 0 hin3 (by ring)
  have hd := (((hu.comp_of_eq 0 hin (by ring)).sub hdis).add (hsum.const_mul β))
  have := jd_envelope (g := fun ε => u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ +
      (w' - b) * ε) - χ * (N₀ + ε) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f))
    hle heq hVt hd
  rw [this, henv]
  have e : ∑ s, p s * (VN s * (1 - ρ - f)) = (1 - ρ - f) * ∑ s, p s * VN s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  ring

/-- **Correction** (Miao, p. 610, budget as printed): if the new member keeps the benefit
(`… + w̃ ε + b (1 − N_t)`), the marginal value is `Λ_t (w̃ − w_t) + ∂V_t/∂N_t + Λ_t b`, not
`Λ_t (w̃ − w_t) + ∂V_t/∂N_t` as printed; the two differ whenever `Λ_t b ≠ 0`. -/
theorem jd_hh_Vn_book_budget {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ}
    {Vn : S → ℝ → ℝ → ℝ} {Vt : ℝ → ℝ} {β δ χ φ ρ f R w w' b D T K₀ N₀ I₀ Λ VN₀ dV : ℝ}
    {VN : S → ℝ} (hφ : 0 < φ) (hN : 0 < N₀)
    (hle : ∀ ε, u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + w' * ε) -
      χ * (N₀ + ε) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f) ≤ Vt ε)
    (heq : u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + w' * 0) -
      χ * (N₀ + 0) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + 0) + f) = Vt 0)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVN : ∀ s, HasDerivAt (fun n => Vn s ((1 - δ) * K₀ + I₀) n) (VN s) ((1 - ρ - f) * N₀ + f))
    (hVt : HasDerivAt Vt dV 0)
    (henv : VN₀ = Λ * (w - b) - χ * N₀ ^ φ + (1 - ρ - f) * (β * ∑ s, p s * VN s)) :
    dV = Λ * (w' - w) + VN₀ + Λ * b ∧ (Λ * b ≠ 0 → dV ≠ Λ * (w' - w) + VN₀) := by
  have hin : HasDerivAt (fun ε => R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + w' * ε) w' 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul w').const_add
      (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀)
  have hin2 : HasDerivAt (fun ε => (1 - ρ - f) * (N₀ + ε) + f) (1 - ρ - f) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add N₀).const_mul (1 - ρ - f)).add_const f
  have hin3 : HasDerivAt (fun ε : ℝ => N₀ + ε) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add N₀
  have hsum : HasDerivAt
      (fun ε => ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f))
      (∑ s, p s * (VN s * (1 - ρ - f))) 0 :=
    HasDerivAt.fun_sum fun s _ =>
      ((hVN s).comp_of_eq 0 hin2 (by ring)).const_mul (p s)
  have hdis := (jd_disutility_hasDerivAt (χ := χ) hφ hN).comp_of_eq 0 hin3 (by ring)
  have hd := (((hu.comp_of_eq 0 hin (by ring)).sub hdis).add (hsum.const_mul β))
  have := jd_envelope (g := fun ε => u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ +
      w' * ε) - χ * (N₀ + ε) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f))
    hle heq hVt hd
  have e : ∑ s, p s * (VN s * (1 - ρ - f)) = (1 - ρ - f) * ∑ s, p s * VN s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  have key : dV = Λ * (w' - w) + VN₀ + Λ * b := by
    rw [this, henv, e]; ring
  refine ⟨key, fun hb h => hb ?_⟩
  linarith

/-- Miao, p. 611: firm `j`'s objective at a node, with `N′ = (1 − ρ) N + q^v v` (18.22) and
stochastic discount factor `m s = β Λ_{t+1}(s)/Λ_t`. -/
noncomputable def jd_firmObj {S : Type*} [Fintype S] (F : ℝ → ℝ → ℝ) (p m : S → ℝ)
    (Jn : S → ℝ → ℝ) (A w R κ ρ qv N K v : ℝ) : ℝ :=
  F K (A * N) - w * N - R * K - v * κ + ∑ s, p s * (m s * Jn s ((1 - ρ) * N + qv * v))

/-- Miao, (18.51), p. 611: the first-order condition for capital, `F₁(K^j_t, A_t N^j_t) = R_kt`. -/
theorem eq_18_51 {S : Type*} [Fintype S] {F : ℝ → ℝ → ℝ} {p m : S → ℝ} {Jn : S → ℝ → ℝ}
    {J : ℝ → ℝ} {A w R κ ρ qv N₀ K₀ v₀ F₁ : ℝ}
    (hmax : ∀ N K v, jd_firmObj F p m Jn A w R κ ρ qv N K v ≤ J N)
    (hopt : jd_firmObj F p m Jn A w R κ ρ qv N₀ K₀ v₀ = J N₀)
    (hF₁ : HasDerivAt (fun k => F k (A * N₀)) F₁ K₀) : F₁ = R := by
  have hd := (((hF₁.sub_const (w * N₀)).sub ((hasDerivAt_id K₀).const_mul R)).sub_const
    (v₀ * κ)).add_const (∑ s, p s * (m s * Jn s ((1 - ρ) * N₀ + qv * v₀)))
  have := jd_foc (h := fun K => jd_firmObj F p m Jn A w R κ ρ qv N₀ K v₀)
    (fun K => (hmax N₀ K v₀).trans hopt.ge) hd
  simp only [mul_one] at this
  linarith

/-- Miao, (18.52), p. 611: the first-order condition for vacancies,
`κ = E_t[(β Λ_{t+1}/Λ_t) ∂J_{t+1}/∂N^j_{t+1}] q^v_t`. -/
theorem eq_18_52 {S : Type*} [Fintype S] {F : ℝ → ℝ → ℝ} {p m : S → ℝ} {Jn : S → ℝ → ℝ}
    {J : ℝ → ℝ} {A w R κ ρ qv N₀ K₀ v₀ : ℝ} {JN : S → ℝ}
    (hmax : ∀ N K v, jd_firmObj F p m Jn A w R κ ρ qv N K v ≤ J N)
    (hopt : jd_firmObj F p m Jn A w R κ ρ qv N₀ K₀ v₀ = J N₀)
    (hJN : ∀ s, HasDerivAt (Jn s) (JN s) ((1 - ρ) * N₀ + qv * v₀)) :
    κ = (∑ s, p s * (m s * JN s)) * qv := by
  have hin : HasDerivAt (fun v => (1 - ρ) * N₀ + qv * v) qv v₀ := by
    simpa using ((hasDerivAt_id v₀).const_mul qv).const_add ((1 - ρ) * N₀)
  have hsum : HasDerivAt (fun v => ∑ s, p s * (m s * Jn s ((1 - ρ) * N₀ + qv * v)))
      (∑ s, p s * (m s * (JN s * qv))) v₀ :=
    HasDerivAt.fun_sum fun s _ =>
      (((hJN s).comp_of_eq v₀ hin (by ring)).const_mul (m s)).const_mul (p s)
  have h1 : HasDerivAt (fun v => F K₀ (A * N₀) - w * N₀ - R * K₀ - v * κ) (-κ) v₀ := by
    simpa using ((hasDerivAt_id v₀).mul_const κ).const_sub (F K₀ (A * N₀) - w * N₀ - R * K₀)
  have hd := h1.add hsum
  have := jd_foc (h := fun v => jd_firmObj F p m Jn A w R κ ρ qv N₀ K₀ v)
    (fun v => (hmax N₀ K₀ v).trans hopt.ge) hd
  have e : ∑ s, p s * (m s * (JN s * qv)) = (∑ s, p s * (m s * JN s)) * qv := by
    rw [Finset.sum_mul]; congr 1; funext s; ring
  rw [e] at this
  linarith

/-- Miao, (18.53), p. 611: the envelope condition, `∂J_t/∂N^j_t = A_t F₂(K^j_t, A_t N^j_t) −
w_t + (1 − ρ) E_t[(β Λ_{t+1}/Λ_t) ∂J_{t+1}/∂N^j_{t+1}]`. -/
theorem eq_18_53 {S : Type*} [Fintype S] {F : ℝ → ℝ → ℝ} {p m : S → ℝ} {Jn : S → ℝ → ℝ}
    {J : ℝ → ℝ} {A w R κ ρ qv N₀ K₀ v₀ F₂ JN₀ : ℝ} {JN : S → ℝ}
    (hmax : ∀ N K v, jd_firmObj F p m Jn A w R κ ρ qv N K v ≤ J N)
    (hopt : jd_firmObj F p m Jn A w R κ ρ qv N₀ K₀ v₀ = J N₀)
    (hF₂ : HasDerivAt (F K₀) F₂ (A * N₀))
    (hJN : ∀ s, HasDerivAt (Jn s) (JN s) ((1 - ρ) * N₀ + qv * v₀)) (hJ : HasDerivAt J JN₀ N₀) :
    JN₀ = A * F₂ - w + (1 - ρ) * ∑ s, p s * (m s * JN s) := by
  have hin : HasDerivAt (fun N => (1 - ρ) * N + qv * v₀) (1 - ρ) N₀ := by
    simpa using ((hasDerivAt_id N₀).const_mul (1 - ρ)).add_const (qv * v₀)
  have hin2 : HasDerivAt (fun N => A * N) A N₀ := by
    simpa using (hasDerivAt_id N₀).const_mul A
  have hsum : HasDerivAt (fun N => ∑ s, p s * (m s * Jn s ((1 - ρ) * N + qv * v₀)))
      (∑ s, p s * (m s * (JN s * (1 - ρ)))) N₀ :=
    HasDerivAt.fun_sum fun s _ =>
      (((hJN s).comp_of_eq N₀ hin (by ring)).const_mul (m s)).const_mul (p s)
  have hd := ((((hF₂.comp N₀ hin2).sub ((hasDerivAt_id N₀).const_mul w)).sub_const
    (R * K₀)).sub_const (v₀ * κ)).add hsum
  have := jd_envelope (g := fun N => jd_firmObj F p m Jn A w R κ ρ qv N K₀ v₀)
    (fun N => hmax N K₀ v₀) hopt hJ hd
  rw [this]
  have e : ∑ s, p s * (m s * (JN s * (1 - ρ))) = (1 - ρ) * ∑ s, p s * (m s * JN s) := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  simp only [mul_one]
  ring

/-- Miao, (18.54), p. 611: with `S^F_t = ∂J_t/∂N^j_t`, (18.52) and (18.53) give
`S^F_t = A_t F₂(K^j_t, A_t N^j_t) − w_t + (1 − ρ) κ / q^v_t`. -/
theorem eq_18_54 {S : Type*} [Fintype S] {p m JN : S → ℝ} {A w κ ρ qv F₂ JN₀ : ℝ}
    (hqv : qv ≠ 0) (h52 : κ = (∑ s, p s * (m s * JN s)) * qv)
    (h53 : JN₀ = A * F₂ - w + (1 - ρ) * ∑ s, p s * (m s * JN s)) :
    JN₀ = A * F₂ - w + (1 - ρ) * κ / qv := by
  rw [h53, h52]
  field_simp

/-- Miao, (18.55), p. 612: substituting (18.54) at `t + 1` into (18.52),
`κ / q(θ_t) = E_t[(β Λ_{t+1}/Λ_t)(A_{t+1} F₂(K^j_{t+1}, A_{t+1} N^j_{t+1}) − w_{t+1} +
(1 − ρ) κ / q(θ_{t+1}))]`. -/
theorem eq_18_55 {S : Type*} [Fintype S] {p m JN An F₂n wn qn : S → ℝ} {κ ρ qv : ℝ}
    (hqv : qv ≠ 0) (h52 : κ = (∑ s, p s * (m s * JN s)) * qv)
    (h54 : ∀ s, JN s = An s * F₂n s - wn s + (1 - ρ) * κ / qn s) :
    κ / qv = ∑ s, p s * (m s * (An s * F₂n s - wn s + (1 - ρ) * κ / qn s)) := by
  have e : κ / qv = ∑ s, p s * (m s * JN s) := by rw [div_eq_iff hqv]; exact h52
  rw [e]
  simp only [h54]

/-- Miao, p. 612: hiring `ε` more workers at wage `w̃`, the firm's marginal value is
`J_n(w̃, t) = w_t − w̃ + ∂J_t/∂N^j_t`. `J̃(ε)` is the value with `N^j_t + ε` workers (`J̃ ≥` the
objective at the optimal `(K, v)`, equality at `ε = 0`). -/
theorem jd_firm_Jn {S : Type*} [Fintype S] {F : ℝ → ℝ → ℝ} {p m : S → ℝ} {Jn : S → ℝ → ℝ}
    {Jt : ℝ → ℝ} {A w w' R κ ρ qv N₀ K₀ v₀ F₂ JN₀ dJ : ℝ} {JN : S → ℝ}
    (hle : ∀ ε, F K₀ (A * (N₀ + ε)) - w * N₀ - w' * ε - R * K₀ - v₀ * κ +
      ∑ s, p s * (m s * Jn s ((1 - ρ) * (N₀ + ε) + qv * v₀)) ≤ Jt ε)
    (heq : F K₀ (A * (N₀ + 0)) - w * N₀ - w' * 0 - R * K₀ - v₀ * κ +
      ∑ s, p s * (m s * Jn s ((1 - ρ) * (N₀ + 0) + qv * v₀)) = Jt 0)
    (hF₂ : HasDerivAt (F K₀) F₂ (A * N₀))
    (hJN : ∀ s, HasDerivAt (Jn s) (JN s) ((1 - ρ) * N₀ + qv * v₀)) (hJt : HasDerivAt Jt dJ 0)
    (h53 : JN₀ = A * F₂ - w + (1 - ρ) * ∑ s, p s * (m s * JN s)) :
    dJ = w - w' + JN₀ := by
  have hin : HasDerivAt (fun ε => (1 - ρ) * (N₀ + ε) + qv * v₀) (1 - ρ) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add N₀).const_mul (1 - ρ)).add_const (qv * v₀)
  have hin2 : HasDerivAt (fun ε => A * (N₀ + ε)) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add N₀).const_mul A
  have hsum : HasDerivAt (fun ε => ∑ s, p s * (m s * Jn s ((1 - ρ) * (N₀ + ε) + qv * v₀)))
      (∑ s, p s * (m s * (JN s * (1 - ρ)))) 0 :=
    HasDerivAt.fun_sum fun s _ =>
      ((((hJN s).comp_of_eq 0 hin (by ring))).const_mul (m s)).const_mul (p s)
  have hd := (((((hF₂.comp_of_eq 0 hin2 (by ring)).sub_const (w * N₀)).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul w')).sub_const (R * K₀)).sub_const (v₀ * κ)).add hsum
  have := jd_envelope (g := fun ε => F K₀ (A * (N₀ + ε)) - w * N₀ - w' * ε - R * K₀ - v₀ * κ +
      ∑ s, p s * (m s * Jn s ((1 - ρ) * (N₀ + ε) + qv * v₀))) hle heq hJt hd
  rw [this, h53]
  have e : ∑ s, p s * (m s * (JN s * (1 - ρ))) = (1 - ρ) * ∑ s, p s * (m s * JN s) := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  simp only [mul_one]
  ring

/-- **Nash bargaining in §18.3** (Miao, pp. 612–613). With `V_n(w) = Λ_t (w − w_t) + V_N` and
`J_n(w) = w_t − w + J_N` (`jd_hh_Vn`, `jd_firm_Jn`), the wage `w_t` maximises
`V_n(w)^η J_n(w)^(1−η)` over the feasible wages iff `(1 − η) V_N = η Λ_t J_N`, i.e.
`(1 − η) S^H_t = η S^F_t` with `S^H_t = V_N/Λ_t`, `S^F_t = J_N`. -/
theorem jd_nash_18_3 {η Λ wt VN JN : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hΛ : 0 < Λ)
    (hVN : 0 ≤ VN) (hJN : 0 ≤ JN) :
    (∀ w, 0 ≤ Λ * (w - wt) + VN → 0 ≤ wt - w + JN →
      (Λ * (w - wt) + VN) ^ η * (wt - w + JN) ^ (1 - η) ≤ VN ^ η * JN ^ (1 - η)) ↔
      (1 - η) * (VN / Λ) = η * JN := by
  have h := jd_nash_iff (a := VN - Λ * wt) (c := wt + JN) (lam := Λ) (w := wt) hη0 hη1 hΛ
    (by linarith) (by linarith)
  have e1 : ∀ w, Λ * (w - wt) + VN = VN - Λ * wt + Λ * w := fun w => by ring
  have e2 : ∀ w, wt - w + JN = wt + JN - w := fun w => by ring
  simp only [e1, e2]
  have e3 : VN - Λ * wt + Λ * wt = VN := by ring
  have e4 : wt + JN - wt = JN := by ring
  rw [e3, e4] at h
  rw [h]
  constructor
  · intro h1; field_simp; linarith
  · intro h1; field_simp at h1; linarith

/-- **The wage equation** (Miao, (18.56), p. 613):
`w_t = (1 − η)(b + χ N_t^φ/Λ_t) + η (A_t F₂(K^j_t, A_t N^j_t) + κ θ_t)`, from (18.50), the
sharing rule `(1 − η) S^H = η S^F` at `t` and `t + 1`, (18.52) in the form
`κ / q(θ_t) = E_t[m S^F_{t+1}]`, and (18.54); the job-finding rate is `q(θ_t) θ_t`. -/
theorem eq_18_56 {S : Type*} [Fintype S] {p m SHn SFn : S → ℝ}
    {η χ φ ρ κ θ q w b N₀ Λ A F₂ SH SF : ℝ} (hη1 : η < 1) (hq : q ≠ 0) (hΛ : Λ ≠ 0)
    (h50 : SH = w - b - χ * N₀ ^ φ / Λ + (1 - ρ - q * θ) * ∑ s, p s * (m s * SHn s))
    (hshare : (1 - η) * SH = η * SF) (hsharen : ∀ s, (1 - η) * SHn s = η * SFn s)
    (h52 : κ / q = ∑ s, p s * (m s * SFn s)) (h54 : SF = A * F₂ - w + (1 - ρ) * κ / q) :
    w = (1 - η) * (b + χ * N₀ ^ φ / Λ) + η * (A * F₂ + κ * θ) := by
  have h1η : (1 - η) ≠ 0 := by linarith
  have hSHn : ∀ s, SHn s = η / (1 - η) * SFn s := fun s => by
    field_simp; linarith [hsharen s]
  have hsum : ∑ s, p s * (m s * SHn s) = η / (1 - η) * (κ / q) := by
    rw [h52, Finset.mul_sum]; congr 1; funext s; rw [hSHn]; ring
  rw [hsum] at h50
  rw [h50, h54] at hshare
  linear_combination (norm := (field_simp; ring)) hshare

/-- Miao, p. 611 ("(18.51) implies that `K^j_t/N^j_t` does not depend on firm identity"): with
constant returns and `k ↦ F₁(k, 1)` injective on `(0, ∞)`, two firms facing the same rental rate
choose the same capital per effective worker. -/
theorem jd_capital_ratio_indep {F F₁ : ℝ → ℝ → ℝ}
    (hhom : ∀ t k l, 0 < t → 0 < k → 0 < l → F (t * k) (t * l) = t * F k l)
    (hd : ∀ k l, 0 < k → 0 < l → HasDerivAt (fun x => F x l) (F₁ k l) k)
    (hinj : Set.InjOn (fun k => F₁ k 1) (Set.Ioi 0)) {A K K' N N' R : ℝ} (hA : 0 < A)
    (hK : 0 < K) (hK' : 0 < K') (hN : 0 < N) (hN' : 0 < N')
    (h51 : F₁ K (A * N) = R) (h51' : F₁ K' (A * N') = R) : K / (A * N) = K' / (A * N') := by
  have hscale : ∀ k n, 0 < k → 0 < n → F₁ k (A * n) = F₁ (k / (A * n)) 1 := by
    intro k n hk hn
    have hAn : 0 < A * n := mul_pos hA hn
    have := jd_partial_homog_one hhom hd (t := A * n) (k := k / (A * n)) (l := 1) hAn
      (div_pos hk hAn) one_pos
    rw [← this]
    congr 1
    · field_simp
    · ring
  rw [hscale K N hK hN] at h51
  rw [hscale K' N' hK' hN'] at h51'
  exact hinj (Set.mem_Ioi.mpr (div_pos hK (mul_pos hA hN)))
    (Set.mem_Ioi.mpr (div_pos hK' (mul_pos hA hN'))) (by simp only; rw [h51, h51'])

/-- Miao, p. 613 ("the wage rate `w_t` does not depend on `j`"): with constant returns, firms with
the same capital per effective worker have the same `F₂`, hence the same wage (18.56). -/
theorem jd_wage_indep {F F₂ : ℝ → ℝ → ℝ}
    (hhom : ∀ t k l, 0 < t → 0 < k → 0 < l → F (t * k) (t * l) = t * F k l)
    (hd : ∀ k l, 0 < k → 0 < l → HasDerivAt (fun y => F k y) (F₂ k l) l)
    {A K K' N N' η b χ φ Λ κ θ Nagg : ℝ} (hA : 0 < A) (hK : 0 < K) (hK' : 0 < K') (hN : 0 < N)
    (hN' : 0 < N') (hratio : K / (A * N) = K' / (A * N')) :
    (1 - η) * (b + χ * Nagg ^ φ / Λ) + η * (A * F₂ K (A * N) + κ * θ) =
      (1 - η) * (b + χ * Nagg ^ φ / Λ) + η * (A * F₂ K' (A * N') + κ * θ) := by
  have hscale : ∀ k n, 0 < k → 0 < n → F₂ k (A * n) = F₂ (k / (A * n)) 1 := by
    intro k n hk hn
    have hAn : 0 < A * n := mul_pos hA hn
    have := jd_partial_homog_two hhom hd (t := A * n) (k := k / (A * n)) (l := 1) hAn
      (div_pos hk hAn) one_pos
    rw [← this]
    congr 1
    · field_simp
    · ring
  rw [hscale K N hK hN, hscale K' N' hK' hN', hratio]

/-- Miao, p. 614: aggregation. If firm types `j` (masses `ω j`, employment `N j > 0`) all
use capital `K j = k A N j`, then `∑ ω_j F(K_j, A N_j) = F(∑ ω_j K_j, A ∑ ω_j N_j)`. -/
theorem jd_aggregate_output {ι : Type*} [Fintype ι] {F : ℝ → ℝ → ℝ}
    (hhom : ∀ t k l, 0 < t → 0 < k → 0 < l → F (t * k) (t * l) = t * F k l)
    {ω N K : ι → ℝ} {A k : ℝ} (hA : 0 < A) (hk : 0 < k)
    (hN : ∀ j, 0 < N j) (hpos : 0 < ∑ j, ω j * N j) (hK : ∀ j, K j = k * (A * N j)) :
    ∑ j, ω j * F (K j) (A * N j) = F (∑ j, ω j * K j) (A * ∑ j, ω j * N j) := by
  have hj : ∀ j, F (K j) (A * N j) = A * N j * F k 1 := by
    intro j
    have := hhom (A * N j) k 1 (mul_pos hA (hN j)) hk one_pos
    rw [mul_one] at this
    rw [hK j, mul_comm k, this]
  have hsumK : ∑ j, ω j * K j = (A * ∑ j, ω j * N j) * k := by
    rw [Finset.mul_sum, Finset.sum_mul]; congr 1; funext j; rw [hK j]; ring
  have hagg := hhom (A * ∑ j, ω j * N j) k 1 (mul_pos hA hpos) hk one_pos
  rw [mul_one] at hagg
  rw [hsumK, hagg]
  simp only [hj]
  rw [Finset.mul_sum, Finset.sum_mul]
  congr 1; funext j; ring

/-- Miao, (18.22), (18.48), p. 609: summing the firms' employment laws
`N^j_{t+1} = (1 − ρ) N^j_t + q(θ_t) v^j_t` gives the household's law
`N_{t+1} = (1 − ρ) N_t + q(θ_t) θ_t u_t` when `v_t = θ_t u_t`. -/
theorem jd_employment_consistency {ι : Type*} [Fintype ι] {ω Nj Nj' vj : ι → ℝ}
    {ρ q θ u : ℝ} (hlaw : ∀ j, Nj' j = (1 - ρ) * Nj j + q * vj j)
    (hv : ∑ j, ω j * vj j = θ * u) :
    ∑ j, ω j * Nj' j = (1 - ρ) * ∑ j, ω j * Nj j + q * θ * u := by
  simp only [hlaw]
  rw [mul_assoc, ← hv, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1; funext j; ring

/-- **The resource constraint** (Miao, p. 614): the household budget (18.46), capital (18.47),
dividends `D_t = Y_t − w_t N_t − R_kt K_t − κ v_t` and the balanced benefit budget
`T_t = b (1 − N_t)` give `C_t + K_{t+1} − (1 − δ) K_t = Y_t − κ v_t`. -/
theorem jd_resource_constraint {C I D R K w N b T K' δ Y κ v : ℝ}
    (h46 : C + I = D + R * K + w * N + b * (1 - N) - T) (h47 : K' = (1 - δ) * K + I)
    (hD : D = Y - w * N - R * K - κ * v) (hT : T = b * (1 - N)) :
    C + K' - (1 - δ) * K = Y - κ * v := by
  rw [h47]
  rw [hD, hT] at h46
  linarith

end Miao.SearchAndMatching
