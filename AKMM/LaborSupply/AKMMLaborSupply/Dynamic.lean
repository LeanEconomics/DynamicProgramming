/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMLaborSupply.StaticExtensions
import NeoclassicalGrowth.RBUtility
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Dynamic labour supply elasticities

AKMM, §12.4.1, pp. 341–346.

* **Two-stage budgeting** (12.9)–(12.11): with `I_t = ra_t + T − (a_{t+1} − a_t)` the period
  budget is `c_t = (1 − τ)w_tℓ_t + I_t` (12.10), equivalently `c_t + (1 − τ)w_t(1 − ℓ_t) = Y_t`
  with full income (12.11) (`eq_12_9_to_12_11`). In the deterministic finite-horizon problem
  (12.7), an optimal plan solves, at every `t` and given `a_{t+1}`, the static problem of §12.3
  (`dyn_two_stage`), and its interior hours satisfy (12.13) (`eq_12_13`).
* **Marshallian and Hicksian elasticities**: (12.12) (`eq_12_12`), (12.14) (`eq_12_14`), their
  combination (12.15) (`eq_12_15`), and along paths of the net wage (`eq_12_15_path`); the
  Slutsky equation (12.16) and (12.17) (`eq_12_16`, `eq_12_17`). The compensation must be
  `dI/dw = −(1 − τ)ℓ`; with the printed `+(1 − τ)ℓ` the response is
  `(1 − 2σ(1 − s_I))/(1/γ + σ(1 − s_I))` (`dyn_compensation_sign`).
* **The Frisch elasticity** (12.18)–(12.21) for a general `U`, with `λ` fixed
  (`eq_12_21`), and its values: separable (12.8) `γ` (`dyn_frisch_separable`, also through the
  general theorem along an explicit path, `dyn_frisch_separable_path`), GHH (12.22) `γ`
  (`dyn_frisch_ghh`) with no income effect (`dyn_ghh_no_income_effect`), Cobb–Douglas
  (`dyn_frisch_cd`), power leisure (`dyn_frisch_leisure`), decreasing in hours
  (`dyn_frisch_decreasing_hours`).
* **The ordering** `ε^F ≥ ε^H ≥ ε^M` for (12.8), with equality iff `σ = 0`, the limits as
  `σ → 0`; the printed "equality holding when `σ → ∞`" is false (`dyn_ordering`,
  `dyn_ordering_sigma_zero`, `dyn_ordering_sigma_infty`).
* **(12.23)**: with the Euler equation and (12.13) at two dates,
  `log(ℓ_{t+1}/ℓ_t) = γ log(w_{t+1}/w_t) + γ log((1 − τ_{t+1})/(1 − τ_t)) − γ log(βR)`, so the
  elasticity of relative hours to relative wages (and net-of-tax rates) is `γ` (`eq_12_23`).

Departure: (12.7) is stochastic; `dyn_two_stage` treats the deterministic problem.
-/

namespace AKMM.LaborSupply

open Filter Topology

/-! ### Two-stage budgeting -/

/-- AKMM, (12.9)–(12.11), p. 342: with `R = 1 + r` and `I = ra + T − (a′ − a)`, the period
budget `c + a′ = Ra + (1 − τ)wℓ + T` is `c = (1 − τ)wℓ + I` (12.10), and with full income
`Y = (1 − τ)w + Ra + T − a′` (12.11) it is `c + (1 − τ)w(1 − ℓ) = Y`. -/
theorem eq_12_9_to_12_11 (r τ w T a a' c l : ℝ) :
    (c + a' = (1 + r) * a + (1 - τ) * w * l + T ↔
      c = (1 - τ) * w * l + (r * a + T - (a' - a))) ∧
    (c + a' = (1 + r) * a + (1 - τ) * w * l + T ↔
      c + (1 - τ) * w * (1 - l) = (1 - τ) * w + (1 + r) * a + T - a') := by
  constructor <;> constructor <;> intro h <;> linarith

/-- A feasible plan of the deterministic version of (12.7) over dates `0, …, N`: budgets,
borrowing limit `a_{t+1} ≥ −ā`, `c ≥ 0`, `0 ≤ ℓ ≤ 1`, and `a_{N+1} ≥ 0`. -/
def DynFeasible (R τ T a0 abar : ℝ) (w : ℕ → ℝ) (N : ℕ) (c l a : ℕ → ℝ) : Prop :=
  a 0 = a0 ∧ 0 ≤ a (N + 1) ∧ ∀ t ≤ N, c t + a (t + 1) = R * a t + (1 - τ) * w t * l t + T ∧
    -abar ≤ a (t + 1) ∧ 0 ≤ c t ∧ 0 ≤ l t ∧ l t ≤ 1

/-- AKMM, pp. 342–343, **two-stage budgeting**. If `(c, ℓ, a)` maximises `Σ_{t≤N} β^tU(c_t, ℓ_t)`
over feasible plans (`β > 0`), then at every `t ≤ N`, given the plan's `a_t, a_{t+1}` and so its
`I_t = (R − 1)a_t + T − (a_{t+1} − a_t)`, `(c_t, ℓ_t)` maximises `U(c, ℓ)` subject to
`c = (1 − τ)w_tℓ + I_t`, `c ≥ 0`, `0 ≤ ℓ ≤ 1`: the static problem of §12.3. -/
theorem dyn_two_stage {R τ T a0 abar β : ℝ} {w : ℕ → ℝ} {N : ℕ} {U : ℝ → ℝ → ℝ}
    {c l a : ℕ → ℝ} (hβ : 0 < β) (hfeas : DynFeasible R τ T a0 abar w N c l a)
    (hopt : ∀ c' l' a', DynFeasible R τ T a0 abar w N c' l' a' →
      ∑ t ∈ Finset.range (N + 1), β ^ t * U (c' t) (l' t) ≤
        ∑ t ∈ Finset.range (N + 1), β ^ t * U (c t) (l t))
    {t : ℕ} (ht : t ≤ N) {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hbud : x = (1 - τ) * w t * y + ((R - 1) * a t + T - (a (t + 1) - a t))) :
    U x y ≤ U (c t) (l t) := by
  obtain ⟨ha0, haN, hf⟩ := hfeas
  have hfeas' : DynFeasible R τ T a0 abar w N (Function.update c t x) (Function.update l t y) a :=
    by
    refine ⟨ha0, haN, fun s hs => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hf s hs
    by_cases hst : s = t
    · subst hst
      simp only [Function.update_self]
      exact ⟨by rw [hbud]; ring, h2, hx, hy0, hy1⟩
    · simp only [Function.update_of_ne hst]
      exact ⟨h1, h2, h3, h4, h5⟩
  have hle := hopt _ _ _ hfeas'
  have hmem : t ∈ Finset.range (N + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le ht)
  have hsplit : ∀ f g : ℕ → ℝ, (∀ s, s ≠ t → f s = g s) →
      ∑ s ∈ Finset.range (N + 1), f s - ∑ s ∈ Finset.range (N + 1), g s = f t - g t := by
    intro f g hfg
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem,
      Finset.sum_congr rfl (fun s hs => hfg s (Finset.ne_of_mem_erase hs))]
    ring
  have hd := hsplit (fun s => β ^ s * U (Function.update c t x s) (Function.update l t y s))
    (fun s => β ^ s * U (c s) (l s)) (fun s hs => by
      simp only [Function.update_of_ne hs])
  simp only [Function.update_self] at hd
  have hβt : 0 < β ^ t := pow_pos hβ t
  have : β ^ t * U x y ≤ β ^ t * U (c t) (l t) := by linarith
  exact le_of_mul_le_mul_left this hβt

/-- AKMM, (12.13), p. 343: in the second stage, interior optimal hours of the static problem
with net wage `(1 − τ)w` and income `I` satisfy `c^{−σ}w(1 − τ) = ψℓ^{1/γ}`. -/
theorem eq_12_13 {ψ γ σ τ w I l : ℝ} (hγ : 0 < γ) (hl : 0 < l)
    (hc : 0 < (1 - τ) * w * l + I)
    (hmax : ∀ y, 0 ≤ y → stObj ψ γ σ ((1 - τ) * w) I y ≤ stObj ψ γ σ ((1 - τ) * w) I l) :
    ((1 - τ) * w * l + I) ^ (-σ) * w * (1 - τ) = ψ * l ^ (1 / γ) := by
  have := ext_foc_of_max hl hmax (st_obj_hasDerivAt (ψ := ψ) (σ := σ) hγ hc)
  linarith

/-! ### Marshallian and Hicksian elasticities -/

/-- AKMM, (12.12), p. 343: differentiating `c = (1 − τ)wℓ + I` along `w(s) = we^s` (`I` fixed):
`d log c/d log w = (1 − s_I) + (1 − s_I) d log ℓ/d log w`, `s_I = I/c`. -/
theorem eq_12_12 {τ w I l' : ℝ} {l : ℝ → ℝ} (hl : 0 < l 0) (hc : 0 < (1 - τ) * w * l 0 + I)
    (hdl : HasDerivAt l l' 0) :
    HasDerivAt (fun s => Real.log ((1 - τ) * (w * Real.exp s) * l s + I))
      ((1 - I / ((1 - τ) * w * l 0 + I)) + (1 - I / ((1 - τ) * w * l 0 + I)) * (l' / l 0)) 0 := by
  have hd : HasDerivAt (fun s => (1 - τ) * (w * Real.exp s) * l s + I)
      ((1 - τ) * w * l 0 + (1 - τ) * w * l') 0 := by
    have := (((st_exp_path w).const_mul (1 - τ)).mul hdl).add_const I
    refine this.congr_deriv ?_
    rw [Real.exp_zero, mul_one]
  have hc0 : (1 - τ) * (w * Real.exp 0) * l 0 + I ≠ 0 := by
    rw [Real.exp_zero, mul_one]; exact hc.ne'
  refine (hd.log hc0).congr_deriv ?_
  rw [Real.exp_zero, mul_one]
  have h1 : (1 - τ) * w * l 0 + I ≠ 0 := hc.ne'
  have h2 : l 0 ≠ 0 := hl.ne'
  field_simp
  ring

/-- AKMM, (12.14), p. 343: differentiating (12.13) in logs along the path,
`σ d log c/d log w + (1/γ) d log ℓ/d log w = 1` (`dc`, `dl` the log-derivatives). -/
theorem eq_12_14 {ψ γ σ τ w I l' : ℝ} {l : ℝ → ℝ} (hψ : 0 < ψ) (hτ : τ < 1) (hw : 0 < w)
    (hl : 0 < l 0) (hc : 0 < (1 - τ) * w * l 0 + I) (hdl : HasDerivAt l l' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * l s ^ (1 / γ) /
      ((1 - τ) * w * Real.exp s * l s + I) ^ (-σ) = (1 - τ) * w * Real.exp s) :
    σ * ((1 - I / ((1 - τ) * w * l 0 + I)) + (1 - I / ((1 - τ) * w * l 0 + I)) * (l' / l 0)) +
      1 / γ * (l' / l 0) = 1 := by
  have hnet : 0 < (1 - τ) * w := mul_pos (by linarith) hw
  have hW0 : 0 < (1 - τ) * w * Real.exp 0 := by rw [Real.exp_zero, mul_one]; exact hnet
  have hc0 : 0 < (1 - τ) * w * Real.exp 0 * l 0 + I := by rwa [Real.exp_zero, mul_one]
  have key := st_path_identity (I := fun _ => I) (I' := 0) hψ hW0 hl hc0
    (st_exp_path ((1 - τ) * w)) (hasDerivAt_const _ _) hdl hfoc
  rw [Real.exp_zero, mul_one, div_self hnet.ne'] at key
  have h1 : (1 - τ) * w * l 0 + I ≠ 0 := hc.ne'
  have h2 : l 0 ≠ 0 := hl.ne'
  have hx : ((1 - τ) * w * l 0 + (1 - τ) * w * l' + 0) / ((1 - τ) * w * l 0 + I) =
      (1 - I / ((1 - τ) * w * l 0 + I)) + (1 - I / ((1 - τ) * w * l 0 + I)) * (l' / l 0) := by
    field_simp; ring
  rw [hx] at key
  linarith

/-- AKMM, (12.15), p. 343: combining (12.12) and (12.14) as linear equations in
`x = d log c/d log w` and `ε = d log ℓ/d log w`:
`ε = (1 − σ(1 − s_I))/(1/γ + σ(1 − s_I))`. -/
theorem eq_12_15 {γ σ sI x e : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) (hs : sI < 1)
    (h12 : x = (1 - sI) + (1 - sI) * e) (h14 : σ * x + 1 / γ * e = 1) :
    e = (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) := by
  have hden : 0 < 1 / γ + σ * (1 - sI) := by
    have : 0 ≤ σ * (1 - sI) := mul_nonneg hσ (by linarith)
    have : 0 < 1 / γ := by positivity
    linarith
  rw [eq_div_iff hden.ne']
  subst h12
  linear_combination h14

/-- AKMM, (12.15), p. 343, along paths: the dynamic Marshallian elasticity with respect to the
wage, at net wage `(1 − τ)w` and `I_t` fixed, is (12.3) with `s_I = I/c`. -/
theorem eq_12_15_path {ψ γ σ τ w I l' : ℝ} {l : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hτ : τ < 1) (hw : 0 < w) (hl : 0 < l 0) (hc : 0 < (1 - τ) * w * l 0 + I)
    (hdl : HasDerivAt l l' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * l s ^ (1 / γ) /
      ((1 - τ) * w * Real.exp s * l s + I) ^ (-σ) = (1 - τ) * w * Real.exp s) :
    HasDerivAt (fun s => Real.log (l s))
      ((1 - σ * (1 - I / ((1 - τ) * w * l 0 + I))) /
        (1 / γ + σ * (1 - I / ((1 - τ) * w * l 0 + I)))) 0 :=
  eq_12_3 hψ hγ hσ (mul_pos (by linarith) hw) hl hc hdl hfoc

/-- AKMM, (12.16), p. 344, **the Slutsky equation** `ε^H = ε^M − ε_{ℓ,I}(1 − s_I)/s_I` with the
dynamic `ε_{ℓ,I} = −σs_I/(1/γ + σ(1 − s_I))` (p. 344), and (12.17)
`ε^H = 1/(1/γ + σ(1 − s_I))`. -/
theorem eq_12_16 {γ σ sI : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) (hs0 : sI ≠ 0) (hs1 : sI < 1) :
    (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) -
        (-σ * sI / (1 / γ + σ * (1 - sI))) * ((1 - sI) / sI) =
      1 / (1 / γ + σ * (1 - sI)) := by
  rw [st_slutsky hγ hσ hs0 hs1]
  ring

/-- AKMM, (12.17), p. 344: along `w(s) = we^s` with non-labour income compensated,
`dI/d log w = −(1 − τ)wℓ`, hours respond with the Hicksian elasticity
`1/(1/γ + σ(1 − s_I))`. -/
theorem eq_12_17 {ψ γ σ τ w I' l' : ℝ} {I l : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hτ : τ < 1) (hw : 0 < w) (hl : 0 < l 0) (hc : 0 < (1 - τ) * w * l 0 + I 0)
    (hdI : HasDerivAt I I' 0) (hcomp : I' = -((1 - τ) * w * l 0)) (hdl : HasDerivAt l l' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * l s ^ (1 / γ) /
      ((1 - τ) * w * Real.exp s * l s + I s) ^ (-σ) = (1 - τ) * w * Real.exp s) :
    HasDerivAt (fun s => Real.log (l s))
      (1 / (1 / γ + σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)))) 0 :=
  eq_12_4 hψ hγ hσ (mul_pos (by linarith) hw) hl hc hdI hcomp hdl hfoc

/-- AKMM, p. 344, **the sign of the compensation**: with the printed
`dI/dw = +(1 − τ)ℓ` (non-labour income rising with the wage) hours respond with
`(1 − 2σ(1 − s_I))/(1/γ + σ(1 − s_I))`, not the Hicksian (12.17); the two differ whenever
`σ(1 − s_I) ≠ 0`. -/
theorem dyn_compensation_sign {ψ γ σ τ w I' l' : ℝ} {I l : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hσ : 0 ≤ σ) (hτ : τ < 1) (hw : 0 < w) (hl : 0 < l 0)
    (hc : 0 < (1 - τ) * w * l 0 + I 0) (hdI : HasDerivAt I I' 0)
    (hcomp : I' = (1 - τ) * w * l 0) (hdl : HasDerivAt l l' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * l s ^ (1 / γ) /
      ((1 - τ) * w * Real.exp s * l s + I s) ^ (-σ) = (1 - τ) * w * Real.exp s) :
    HasDerivAt (fun s => Real.log (l s))
      ((1 - 2 * (σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)))) /
        (1 / γ + σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)))) 0 ∧
    (σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)) ≠ 0 →
      (1 - 2 * (σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)))) /
        (1 / γ + σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0))) ≠
      1 / (1 / γ + σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)))) := by
  have hnet : 0 < (1 - τ) * w := mul_pos (by linarith) hw
  have hW0 : 0 < (1 - τ) * w * Real.exp 0 := by rw [Real.exp_zero, mul_one]; exact hnet
  have hc0 : 0 < (1 - τ) * w * Real.exp 0 * l 0 + I 0 := by rwa [Real.exp_zero, mul_one]
  have key := st_path_poly hψ hγ hW0 hl hc0 (st_exp_path ((1 - τ) * w)) hdI hdl hfoc
  simp only [Real.exp_zero, mul_one, hcomp] at key
  set W := (1 - τ) * w
  set c := W * l 0 + I 0
  have ha : 1 - I 0 / c = W * l 0 / c := by field_simp; ring
  have hden : 0 < 1 / γ + σ * (1 - I 0 / c) := by rw [ha]; positivity
  have hD : 0 < c + γ * σ * W * l 0 := by
    have : 0 ≤ γ * σ * W * l 0 := by positivity
    linarith
  have hl' : l' = γ * l 0 * (c - 2 * σ * W * l 0) / (c + γ * σ * W * l 0) := by
    rw [eq_div_iff hD.ne']
    have h : W * (l' * (c + γ * σ * W * l 0) - γ * l 0 * (c - 2 * σ * W * l 0)) = 0 := by
      linear_combination key
    linarith [(mul_eq_zero.1 h).resolve_left hnet.ne']
  refine ⟨(hdl.log hl.ne').congr_deriv ?_, fun hne h => hne ?_⟩
  · rw [hl', ha]
    have h1 : c ≠ 0 := hc.ne'
    have h4 : γ ≠ 0 := hγ.ne'
    have h5 : l 0 ≠ 0 := hl.ne'
    field_simp
  · rw [div_left_inj' hden.ne'] at h
    linarith

/-! ### The Frisch elasticity -/

/-- AKMM, (12.18)–(12.21), pp. 344–345, **the Frisch elasticity** for a general period utility.
Let `U_c`, `U_ℓ` be differentiable at `(c, ℓ)` with partial derivatives `U_cc, U_cℓ` and
`U_ℓc, U_ℓℓ`. If along `w(s) = we^s` consumption and hours satisfy (12.18) `U_c = λ` and
(12.19) `−U_ℓ = λ(1 − τ)w` near `0` with `λ` fixed, then
`d log ℓ/d log w = U_ℓ/(ℓU_ℓℓ − ℓU_ℓcU_cℓ/U_cc)`. -/
theorem eq_12_21 {Uc Ul : ℝ × ℝ → ℝ} {Ucc Ucl Ulc Ull lam τ w c' l' : ℝ} {c l : ℝ → ℝ}
    (hUc : HasFDerivAt Uc (Ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Ucl • ContinuousLinearMap.snd ℝ ℝ ℝ) (c 0, l 0))
    (hUl : HasFDerivAt Ul (Ulc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Ull • ContinuousLinearMap.snd ℝ ℝ ℝ) (c 0, l 0))
    (hdc : HasDerivAt c c' 0) (hdl : HasDerivAt l l' 0) (hl : 0 < l 0) (hUcc : Ucc ≠ 0)
    (hden : l 0 * Ull - l 0 * (Ulc * Ucl / Ucc) ≠ 0)
    (h18 : ∀ᶠ s in 𝓝 (0 : ℝ), Uc (c s, l s) = lam)
    (h19 : ∀ᶠ s in 𝓝 (0 : ℝ), -Ul (c s, l s) = lam * (1 - τ) * (w * Real.exp s)) :
    HasDerivAt (fun s => Real.log (l s))
      (Ul (c 0, l 0) / (l 0 * Ull - l 0 * (Ulc * Ucl / Ucc))) 0 := by
  have hp : HasDerivAt (fun s => (c s, l s)) (c', l') 0 := hdc.prodMk hdl
  have d18 := hUc.comp_hasDerivAt (x := (0 : ℝ)) hp
  have d19 := hUl.comp_hasDerivAt (x := (0 : ℝ)) hp
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul] at d18 d19
  have e18 : Ucc * c' + Ucl * l' = 0 := by
    have h0 := (hasDerivAt_const (0 : ℝ) lam).congr_of_eventuallyEq
      (h18.mono fun s hs => (hs : Uc (c s, l s) = lam))
    exact d18.unique h0
  have e19 : -(Ulc * c' + Ull * l') = lam * (1 - τ) * w := by
    have hrhs : HasDerivAt (fun s => lam * (1 - τ) * (w * Real.exp s))
        (lam * (1 - τ) * w) 0 := (st_exp_path w).const_mul _
    have h0 := hrhs.congr_of_eventuallyEq (h19.mono fun s hs => hs)
    exact d19.neg.unique h0
  have hUl0 : -Ul (c 0, l 0) = lam * (1 - τ) * w := by
    have := h19.self_of_nhds
    rwa [Real.exp_zero, mul_one] at this
  have hc' : c' = -(Ucl * l') / Ucc := by
    rw [eq_div_iff hUcc]; linarith
  have hmain : l' * (Ull - Ulc * Ucl / Ucc) = Ul (c 0, l 0) := by
    rw [hc'] at e19
    linear_combination hUl0 - e19
  refine (hdl.log hl.ne').congr_deriv ?_
  rw [div_eq_div_iff hl.ne' hden]
  linear_combination (l 0) * hmain

/-- The Frisch formula (12.21), `U_ℓ/(ℓU_ℓℓ − ℓU_ℓcU_cℓ/U_cc)`. -/
noncomputable def frischF (l Ul Ull Ulc Ucl Ucc : ℝ) : ℝ := Ul / (l * Ull - l * (Ulc * Ucl / Ucc))

/-- AKMM, p. 345: for the separable utility (12.8), with `U_ℓ = −ψℓ^{1/γ}`,
`U_ℓℓ = −(ψ/γ)ℓ^{1/γ−1}` and `U_ℓc = U_cℓ = 0`, (12.21) gives `ε^F = γ`; these are the
partial derivatives (`ℓ > 0`). -/
theorem dyn_frisch_separable {ψ γ Ucc l : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hl : 0 < l) :
    HasDerivAt (fun x => -disutil ψ γ x) (-(ψ * l ^ (1 / γ))) l ∧
      HasDerivAt (fun x => -(ψ * x ^ (1 / γ))) (-(ψ / γ * l ^ (1 / γ - 1))) l ∧
      frischF l (-(ψ * l ^ (1 / γ))) (-(ψ / γ * l ^ (1 / γ - 1))) 0 0 Ucc = γ := by
  refine ⟨(st_disutil_hasDerivAt hγ l).neg, ?_, ?_⟩
  · have := ((Real.hasDerivAt_rpow_const (p := 1 / γ) (Or.inl hl.ne')).const_mul ψ).neg
    exact this.congr_deriv (by ring)
  · unfold frischF
    have h : l * l ^ (1 / γ - 1) = l ^ (1 / γ) := by
      rw [Real.rpow_sub_one hl.ne']; field_simp
    have hp : 0 < l ^ (1 / γ) := Real.rpow_pos_of_pos hl _
    rw [show l * -(ψ / γ * l ^ (1 / γ - 1)) - l * (0 * 0 / Ucc) =
      -(ψ / γ * (l * l ^ (1 / γ - 1))) by ring, h]
    field_simp

/-- AKMM, p. 345, `ε^F = γ` for (12.8) **through the general formula** `eq_12_21`, along an
explicit path: with `λ > 0` fixed, `c(s) = λ^{−1/σ}` and `ℓ(s) = (λ(1 − τ)we^s/ψ)^γ` satisfy
(12.18)–(12.19) for `U_c = c^{−σ}`, `U_ℓ = −ψℓ^{1/γ}`, and `d log ℓ/d log w = γ`. -/
theorem dyn_frisch_separable_path {ψ γ σ lam τ w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 < σ)
    (hlam : 0 < lam) (hτ : τ < 1) (hw : 0 < w) :
    HasDerivAt (fun s => Real.log ((lam * (1 - τ) * (w * Real.exp s) / ψ) ^ γ)) γ 0 := by
  set c : ℝ → ℝ := fun _ => lam ^ (-(1 / σ))
  set l : ℝ → ℝ := fun s => (lam * (1 - τ) * (w * Real.exp s) / ψ) ^ γ
  have hc0 : 0 < c 0 := Real.rpow_pos_of_pos hlam _
  have hk : 0 < lam * (1 - τ) * w / ψ := by
    have : 0 < 1 - τ := by linarith
    positivity
  have hl0 : 0 < l 0 := by
    simp only [l, Real.exp_zero, mul_one]; exact Real.rpow_pos_of_pos hk _
  have hdl : HasDerivAt l (γ * l 0) 0 := by
    have hin : HasDerivAt (fun s => lam * (1 - τ) * (w * Real.exp s) / ψ)
        (lam * (1 - τ) * w / ψ) 0 := ((st_exp_path w).const_mul _).div_const ψ
    have hpos : lam * (1 - τ) * (w * Real.exp 0) / ψ ≠ 0 := by
      rw [Real.exp_zero, mul_one]; exact hk.ne'
    have := (Real.hasDerivAt_rpow_const (p := γ) (Or.inl hpos)).comp 0 hin
    refine this.congr_deriv ?_
    simp only [l, Real.exp_zero, mul_one]
    rw [Real.rpow_sub_one hk.ne']
    have : (1 - τ) ≠ 0 := (by linarith : (0 : ℝ) < 1 - τ).ne'
    field_simp
  -- the partial derivatives
  have hUc : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ (-σ))
      ((-σ * c 0 ^ (-σ - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (c 0, l 0) := by
    have := (Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hc0.ne')).hasFDerivAt.comp (c 0, l 0)
      (hasFDerivAt_fst (𝕜 := ℝ) (p := (c 0, l 0)))
    refine this.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
    simp
    ring
  have hUl : HasFDerivAt (fun p : ℝ × ℝ => -(ψ * p.2 ^ (1 / γ)))
      ((0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-(ψ / γ * l 0 ^ (1 / γ - 1))) • ContinuousLinearMap.snd ℝ ℝ ℝ) (c 0, l 0) := by
    have h1 := ((Real.hasDerivAt_rpow_const (p := 1 / γ) (Or.inl hl0.ne')).const_mul ψ).neg
    have := h1.hasFDerivAt.comp (c 0, l 0) (hasFDerivAt_snd (𝕜 := ℝ) (p := (c 0, l 0)))
    refine this.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
    simp [ContinuousLinearMap.toSpanSingleton_apply]
    ring
  have hσ' : -σ * c 0 ^ (-σ - 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.2 hσ.ne') (Real.rpow_pos_of_pos hc0 _).ne'
  have hden : l 0 * -(ψ / γ * l 0 ^ (1 / γ - 1)) -
      l 0 * (0 * 0 / (-σ * c 0 ^ (-σ - 1))) ≠ 0 := by
    have : 0 < ψ / γ * l 0 ^ (1 / γ - 1) := by
      have := Real.rpow_pos_of_pos hl0 (1 / γ - 1); positivity
    have : 0 < l 0 * (ψ / γ * l 0 ^ (1 / γ - 1)) := by positivity
    simp only [mul_zero, zero_div, sub_zero]
    nlinarith
  have h18 : ∀ᶠ s in 𝓝 (0 : ℝ), (fun p : ℝ × ℝ => p.1 ^ (-σ)) (c s, l s) = lam :=
    Eventually.of_forall fun s => by
      simp only [c]
      rw [← Real.rpow_mul hlam.le, show -(1 / σ) * -σ = 1 by field_simp, Real.rpow_one]
  have h19 : ∀ᶠ s in 𝓝 (0 : ℝ), -(fun p : ℝ × ℝ => -(ψ * p.2 ^ (1 / γ))) (c s, l s) =
      lam * (1 - τ) * (w * Real.exp s) := Eventually.of_forall fun s => by
    simp only [l, neg_neg]
    have hx : 0 < lam * (1 - τ) * (w * Real.exp s) / ψ := by
      have : 0 < 1 - τ := by linarith
      positivity
    rw [← Real.rpow_mul hx.le, mul_one_div_cancel hγ.ne', Real.rpow_one]
    field_simp
  have := eq_12_21 hUc hUl (hasDerivAt_const 0 _) hdl hl0 hσ' hden h18 h19
  refine this.congr_deriv ?_
  have hsep := (dyn_frisch_separable (Ucc := -σ * c 0 ^ (-σ - 1)) hψ hγ hl0).2.2
  unfold frischF at hsep
  simpa using hsep

/-! ### GHH preferences -/

/-- AKMM, (12.22), p. 345: the partial derivatives of GHH utility
`U = (c − G(ℓ))^{1−σ}/(1 − σ)`, `G = v` of (12.8), at `x = c − G(ℓ) > 0`:
`U_c = x^{−σ}`, `U_ℓ = −x^{−σ}G′`, `U_cc = −σx^{−σ−1}`, `U_cℓ = U_ℓc = σx^{−σ−1}G′`,
`U_ℓℓ = −σx^{−σ−1}G′² − x^{−σ}G″`, with `G′ = ψℓ^{1/γ}`, `G″ = (ψ/γ)ℓ^{1/γ−1}`. -/
theorem dyn_ghh_partials {ψ γ σ c l : ℝ} (hγ : 0 < γ) (hσ : σ ≠ 1) (hl : 0 < l)
    (hx : 0 < c - disutil ψ γ l) :
    HasDerivAt (fun c' => (c' - disutil ψ γ l) ^ (1 - σ) / (1 - σ))
      ((c - disutil ψ γ l) ^ (-σ)) c ∧
    HasDerivAt (fun l' => (c - disutil ψ γ l') ^ (1 - σ) / (1 - σ))
      (-((c - disutil ψ γ l) ^ (-σ) * (ψ * l ^ (1 / γ)))) l ∧
    HasDerivAt (fun c' => (c' - disutil ψ γ l) ^ (-σ))
      (-σ * (c - disutil ψ γ l) ^ (-σ - 1)) c ∧
    HasDerivAt (fun l' => (c - disutil ψ γ l') ^ (-σ))
      (σ * (c - disutil ψ γ l) ^ (-σ - 1) * (ψ * l ^ (1 / γ))) l ∧
    HasDerivAt (fun c' => -((c' - disutil ψ γ l) ^ (-σ) * (ψ * l ^ (1 / γ))))
      (σ * (c - disutil ψ γ l) ^ (-σ - 1) * (ψ * l ^ (1 / γ))) c ∧
    HasDerivAt (fun l' => -((c - disutil ψ γ l') ^ (-σ) * (ψ * l' ^ (1 / γ))))
      (-σ * (c - disutil ψ γ l) ^ (-σ - 1) * (ψ * l ^ (1 / γ)) ^ 2 -
        (c - disutil ψ γ l) ^ (-σ) * (ψ / γ * l ^ (1 / γ - 1))) l := by
  set x := c - disutil ψ γ l
  have hs : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have hU : HasDerivAt (fun y => y ^ (1 - σ) / (1 - σ)) (x ^ (-σ)) x := by
    have := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx.ne')).div_const (1 - σ)
    refine this.congr_deriv ?_
    rw [show 1 - σ - 1 = -σ by ring]; field_simp
  have hG := st_disutil_hasDerivAt (ψ := ψ) hγ l
  obtain ⟨h1, h2, -⟩ :=
    Miao.NeoclassicalGrowth.rb_ghh_mrs (w := 0) hU hG (Real.rpow_pos_of_pos hx _)
  have hP : HasDerivAt (fun y => y ^ (-σ)) (-σ * x ^ (-σ - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hc1 : HasDerivAt (fun c' => c' - disutil ψ γ l) 1 c := (hasDerivAt_id c).sub_const _
  have hl1 : HasDerivAt (fun l' => c - disutil ψ γ l') (-(ψ * l ^ (1 / γ))) l := hG.const_sub c
  have hG' : HasDerivAt (fun l' => ψ * l' ^ (1 / γ)) (ψ / γ * l ^ (1 / γ - 1)) l := by
    have := (Real.hasDerivAt_rpow_const (p := 1 / γ) (Or.inl hl.ne')).const_mul ψ
    exact this.congr_deriv (by ring)
  have hPc := hP.comp c hc1
  have hPl := hP.comp l hl1
  refine ⟨h1, h2, hPc.congr_deriv (by ring), hPl.congr_deriv (by ring),
    (hPc.mul_const (ψ * l ^ (1 / γ))).neg.congr_deriv (by ring), ?_⟩
  exact (hPl.mul hG').neg.congr_deriv (by simp only [Function.comp_apply]; ring)

/-- AKMM, p. 346: **the Frisch elasticity of GHH utility is `γ`**: (12.21) with the partial
derivatives of `dyn_ghh_partials` equals `γ`. -/
theorem dyn_frisch_ghh {ψ γ σ x l : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hx : 0 < x)
    (hl : 0 < l) :
    frischF l (-(x ^ (-σ) * (ψ * l ^ (1 / γ))))
      (-σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ)) ^ 2 - x ^ (-σ) * (ψ / γ * l ^ (1 / γ - 1)))
      (σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ))) (σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ)))
      (-σ * x ^ (-σ - 1)) = γ := by
  unfold frischF
  have hA : 0 < x ^ (-σ - 1) := Real.rpow_pos_of_pos hx _
  have hB : 0 < x ^ (-σ) := Real.rpow_pos_of_pos hx _
  have h : l * l ^ (1 / γ - 1) = l ^ (1 / γ) := by
    rw [Real.rpow_sub_one hl.ne']; field_simp
  have hp : 0 < l ^ (1 / γ) := Real.rpow_pos_of_pos hl _
  have hden : l * (-σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ)) ^ 2 -
      x ^ (-σ) * (ψ / γ * l ^ (1 / γ - 1))) - l * (σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ)) *
      (σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ))) / (-σ * x ^ (-σ - 1))) =
      -(x ^ (-σ) * (ψ / γ * l ^ (1 / γ))) := by
    rw [← h]; field_simp; ring
  rw [hden]
  field_simp

/-- AKMM, p. 346: **GHH utility has no income effect**: if `ℓ > 0` maximises
`u(wℓ + I − G(ℓ))` over `ℓ ≥ 0` (`u = c^{1−σ}/(1 − σ)`, at `x > 0`), then `ψℓ^{1/γ} = w`, so
`ℓ = (w/ψ)^γ` whatever `I`; along `we^s`, `d log ℓ/d log w = γ`. Hence
`ε^M = ε^H = ε^F = γ`. -/
theorem dyn_ghh_no_income_effect {ψ γ σ w I l : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : σ ≠ 1)
    (hw : 0 < w) (hl : 0 < l) (hx : 0 < w * l + I - disutil ψ γ l)
    (hmax : ∀ y, 0 ≤ y → (w * y + I - disutil ψ γ y) ^ (1 - σ) / (1 - σ) ≤
      (w * l + I - disutil ψ γ l) ^ (1 - σ) / (1 - σ)) :
    l = (w / ψ) ^ γ ∧
      HasDerivAt (fun s => Real.log ((w * Real.exp s / ψ) ^ γ)) γ 0 := by
  set x := w * l + I - disutil ψ γ l
  have hs : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have hU : HasDerivAt (fun y => y ^ (1 - σ) / (1 - σ)) (x ^ (-σ)) x := by
    have := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx.ne')).div_const (1 - σ)
    refine this.congr_deriv ?_
    rw [show 1 - σ - 1 = -σ by ring]; field_simp
  have hin : HasDerivAt (fun y => w * y + I - disutil ψ γ y) (w - ψ * l ^ (1 / γ)) l := by
    have := (((hasDerivAt_id l).const_mul w).add_const I).sub (st_disutil_hasDerivAt
      (ψ := ψ) hγ l)
    exact this.congr_deriv (by simp)
  have hd := hU.comp l hin
  have h0 := ext_foc_of_max hl hmax hd
  have hfoc : ψ * l ^ (1 / γ) = w := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (Real.rpow_pos_of_pos hx _).ne'
    · linarith
  refine ⟨?_, ?_⟩
  · rw [← hfoc, mul_div_cancel_left₀ _ hψ.ne', ← Real.rpow_mul hl.le, one_div_mul_cancel hγ.ne',
      Real.rpow_one]
  · have hk : ∀ s, Real.log ((w * Real.exp s / ψ) ^ γ) = γ * Real.log (w / ψ) + γ * s := by
      intro s
      rw [Real.log_rpow (by positivity), show w * Real.exp s / ψ = w / ψ * Real.exp s by ring,
        Real.log_mul (by positivity) (Real.exp_pos s).ne', Real.log_exp]
      ring
    simp only [hk]
    exact ((hasDerivAt_id (0 : ℝ)).const_mul γ |>.const_add _).congr_deriv (by simp)

/-! ### Cobb–Douglas and power-leisure utility -/

/-- AKMM, p. 346: the partial derivatives of the Cobb–Douglas utility
`U = c^{(1−ψ)k}(1 − ℓ)^{ψk}/k`, `k = 1 − σ` (that is `(c^{1−ψ}(1 − ℓ)^ψ)^{1−σ}/(1 − σ)`), at
`c > 0`, `x = 1 − ℓ > 0`, with `a = 1 − ψ`, `b = ψ`. -/
theorem dyn_cd_partials {a b k c l : ℝ} (hk : k ≠ 0) (hc : 0 < c) (hx : 0 < 1 - l) :
    HasDerivAt (fun c' => c' ^ (a * k) * (1 - l) ^ (b * k) / k)
      (a * c ^ (a * k - 1) * (1 - l) ^ (b * k)) c ∧
    HasDerivAt (fun l' => c ^ (a * k) * (1 - l') ^ (b * k) / k)
      (-(b * c ^ (a * k) * (1 - l) ^ (b * k - 1))) l ∧
    HasDerivAt (fun c' => a * c' ^ (a * k - 1) * (1 - l) ^ (b * k))
      (a * (a * k - 1) * c ^ (a * k - 1 - 1) * (1 - l) ^ (b * k)) c ∧
    HasDerivAt (fun l' => a * c ^ (a * k - 1) * (1 - l') ^ (b * k))
      (-(a * b * k * c ^ (a * k - 1) * (1 - l) ^ (b * k - 1))) l ∧
    HasDerivAt (fun c' => -(b * c' ^ (a * k) * (1 - l) ^ (b * k - 1)))
      (-(a * b * k * c ^ (a * k - 1) * (1 - l) ^ (b * k - 1))) c ∧
    HasDerivAt (fun l' => -(b * c ^ (a * k) * (1 - l') ^ (b * k - 1)))
      (b * (b * k - 1) * c ^ (a * k) * (1 - l) ^ (b * k - 1 - 1)) l := by
  have dc : ∀ p : ℝ, HasDerivAt (fun c' => c' ^ p) (p * c ^ (p - 1)) c :=
    fun p => Real.hasDerivAt_rpow_const (Or.inl hc.ne')
  have dl : ∀ p : ℝ, HasDerivAt (fun l' => (1 - l') ^ p) (-(p * (1 - l) ^ (p - 1))) l := by
    intro p
    have := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).comp l
      ((hasDerivAt_id l).const_sub 1)
    exact this.congr_deriv (by simp)
  refine ⟨((dc (a * k)).mul_const _).div_const k |>.congr_deriv (by field_simp),
    ((dl (b * k)).const_mul _).div_const k |>.congr_deriv (by field_simp),
    ((dc (a * k - 1)).const_mul a).mul_const _ |>.congr_deriv (by ring),
    ((dl (b * k)).const_mul (a * c ^ (a * k - 1))).congr_deriv (by ring),
    (((dc (a * k)).const_mul b).mul_const _).neg.congr_deriv (by ring),
    ((dl (b * k - 1)).const_mul (b * c ^ (a * k))).neg.congr_deriv (by ring)⟩

/-- AKMM, p. 346: **the Frisch elasticity of Cobb–Douglas utility** is
`ε^F = ((1 − ℓ)/ℓ)(1 − (1 − ψ)(1 − σ))/σ` (with `(1 − ψ)(1 − σ) ≠ 1`, `σ ≠ 0`, `0 < ψ < 1`). -/
theorem dyn_frisch_cd {ψ σ c l : ℝ} (hψ : 0 < ψ) (hψ1 : ψ < 1) (hσ : σ ≠ 0)
    (hak : (1 - ψ) * (1 - σ) ≠ 1) (hc : 0 < c) (hl : 0 < l) (hx : 0 < 1 - l) :
    frischF l (-(ψ * c ^ ((1 - ψ) * (1 - σ)) * (1 - l) ^ (ψ * (1 - σ) - 1)))
      (ψ * (ψ * (1 - σ) - 1) * c ^ ((1 - ψ) * (1 - σ)) * (1 - l) ^ (ψ * (1 - σ) - 1 - 1))
      (-((1 - ψ) * ψ * (1 - σ) * c ^ ((1 - ψ) * (1 - σ) - 1) * (1 - l) ^ (ψ * (1 - σ) - 1)))
      (-((1 - ψ) * ψ * (1 - σ) * c ^ ((1 - ψ) * (1 - σ) - 1) * (1 - l) ^ (ψ * (1 - σ) - 1)))
      ((1 - ψ) * ((1 - ψ) * (1 - σ) - 1) * c ^ ((1 - ψ) * (1 - σ) - 1 - 1) *
        (1 - l) ^ (ψ * (1 - σ))) =
      (1 - l) / l * ((1 - (1 - ψ) * (1 - σ)) / σ) := by
  unfold frischF
  set P := c ^ ((1 - ψ) * (1 - σ))
  set Q := (1 - l) ^ (ψ * (1 - σ))
  set x := 1 - l
  have hP : 0 < P := Real.rpow_pos_of_pos hc _
  have hQ : 0 < Q := Real.rpow_pos_of_pos hx _
  have e1 : c ^ ((1 - ψ) * (1 - σ) - 1) = P / c := Real.rpow_sub_one hc.ne' _
  have e2 : c ^ ((1 - ψ) * (1 - σ) - 1 - 1) = P / c / c := by
    rw [Real.rpow_sub_one hc.ne', e1]
  have e3 : x ^ (ψ * (1 - σ) - 1) = Q / x := Real.rpow_sub_one hx.ne' _
  have e4 : x ^ (ψ * (1 - σ) - 1 - 1) = Q / x / x := by
    rw [Real.rpow_sub_one hx.ne', e3]
  rw [e1, e2, e3, e4]
  have hak' : (1 - ψ) * (1 - σ) - 1 ≠ 0 := sub_ne_zero.2 hak
  have h1ψ : 1 - ψ ≠ 0 := by linarith
  set A := (1 - ψ) * (1 - σ) - 1 with hA
  field_simp
  rw [hA]
  field_simp
  linear_combination (ψ - σ * ψ + σ) * (mul_inv_cancel₀ hσ)

/-- AKMM, p. 346: the partial derivatives of the power-leisure utility
`ψ(1 − ℓ)^{1−γ}/(1 − γ)` (the consumption part does not depend on `ℓ`, so `U_ℓc = 0`):
`U_ℓ = −ψ(1 − ℓ)^{−γ}`, `U_ℓℓ = −ψγ(1 − ℓ)^{−γ−1}`; and the Frisch elasticity is
`((1 − ℓ)/ℓ)(1/γ)`. -/
theorem dyn_frisch_leisure {ψ γ l Ucc : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hγ1 : γ ≠ 1) (hl : 0 < l)
    (hx : 0 < 1 - l) :
    HasDerivAt (fun l' => ψ * (1 - l') ^ (1 - γ) / (1 - γ)) (-(ψ * (1 - l) ^ (-γ))) l ∧
      HasDerivAt (fun l' => -(ψ * (1 - l') ^ (-γ))) (-(ψ * γ * (1 - l) ^ (-γ - 1))) l ∧
      frischF l (-(ψ * (1 - l) ^ (-γ))) (-(ψ * γ * (1 - l) ^ (-γ - 1))) 0 0 Ucc =
        (1 - l) / l * (1 / γ) := by
  have dl : ∀ p : ℝ, HasDerivAt (fun l' => (1 - l') ^ p) (-(p * (1 - l) ^ (p - 1))) l := by
    intro p
    have := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).comp l
      ((hasDerivAt_id l).const_sub 1)
    exact this.congr_deriv (by simp)
  have hs : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  refine ⟨((dl (1 - γ)).const_mul ψ).div_const _ |>.congr_deriv ?_,
    ((dl (-γ)).const_mul ψ).neg.congr_deriv (by ring), ?_⟩
  · rw [show 1 - γ - 1 = -γ by ring]; field_simp
  · unfold frischF
    have e : (1 - l) ^ (-γ) = (1 - l) * (1 - l) ^ (-γ - 1) := by
      rw [Real.rpow_sub_one hx.ne']; field_simp
    have hp : 0 < (1 - l) ^ (-γ - 1) := Real.rpow_pos_of_pos hx _
    rw [e]
    simp only [mul_zero, zero_div, sub_zero]
    field_simp

/-- AKMM, p. 346: "individuals who work more hours are less responsive": a Frisch elasticity of
the form `((1 − ℓ)/ℓ)K`, `K > 0`, is strictly decreasing in `ℓ ∈ (0, 1)`. -/
theorem dyn_frisch_decreasing_hours {K l₁ l₂ : ℝ} (hK : 0 < K) (h₁ : 0 < l₁) (h₁₂ : l₁ < l₂) :
    (1 - l₂) / l₂ * K < (1 - l₁) / l₁ * K := by
  have h₂ : 0 < l₂ := lt_trans h₁ h₁₂
  apply mul_lt_mul_of_pos_right _ hK
  rw [div_lt_div_iff₀ h₂ h₁]
  nlinarith

/-! ### The ordering of the elasticities -/

/-- AKMM, p. 345, **`ε^F ≥ ε^H ≥ ε^M`** for (12.8): with `ε^F = γ`, (12.17) and (12.15)
(`σ ≥ 0`, `s_I < 1`); each equality holds iff `σ = 0` (utility linear in consumption). -/
theorem dyn_ordering {γ σ sI : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) (hs : sI < 1) :
    1 / (1 / γ + σ * (1 - sI)) ≤ γ ∧
      (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) ≤ 1 / (1 / γ + σ * (1 - sI)) ∧
      (1 / (1 / γ + σ * (1 - sI)) = γ ↔ σ = 0) ∧
      ((1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) = 1 / (1 / γ + σ * (1 - sI)) ↔ σ = 0) := by
  obtain ⟨-, -, h3, h4⟩ := st_signs hγ hσ hs
  have hg : 0 < 1 / γ := by positivity
  have hx : 0 ≤ σ * (1 - sI) := mul_nonneg hσ (by linarith)
  refine ⟨?_, h3, ⟨fun h => ?_, fun h => by subst h; simp⟩, h4⟩
  · rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ γ * (σ * (1 - sI)) := mul_nonneg hγ.le hx
    have e : γ * (1 / γ) = 1 := by field_simp
    nlinarith
  · have hden : 0 < 1 / γ + σ * (1 - sI) := by linarith
    rw [div_eq_iff hden.ne'] at h
    have e : γ * (1 / γ) = 1 := by field_simp
    have : γ * (σ * (1 - sI)) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hγ.ne'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact h''
      · exact absurd h'' (by linarith)

/-- AKMM, p. 344: as `σ → 0` the Hicksian and Marshallian elasticities (12.17), (12.15) tend
to the Frisch elasticity `γ` of (12.8). -/
theorem dyn_ordering_sigma_zero {γ a : ℝ} (hγ : 0 < γ) :
    Tendsto (fun σ => 1 / (1 / γ + σ * a)) (𝓝 0) (𝓝 γ) ∧
      Tendsto (fun σ => (1 - σ * a) / (1 / γ + σ * a)) (𝓝 0) (𝓝 γ) := by
  have hne : 1 / γ + 0 * a ≠ 0 := by
    simp only [one_div, zero_mul, add_zero, ne_eq, inv_eq_zero]; exact hγ.ne'
  have hden : ContinuousAt (fun σ : ℝ => 1 / γ + σ * a) 0 := by fun_prop
  have hnum : ContinuousAt (fun σ : ℝ => 1 - σ * a) 0 := by fun_prop
  have h1 := ((continuousAt_const (y := (1 : ℝ))).div hden hne).tendsto
  have h2 := (hnum.div hden hne).tendsto
  refine ⟨?_, ?_⟩
  · convert h1 using 2; simp
  · convert h2 using 2; simp

/-- AKMM, p. 345, **corrected**: "`ε^F ≥ ε^H ≥ ε^M` with equality holding when `σ → ∞`" is
false. As `σ → ∞` (with `1 − s_I = a > 0`) `ε^H → 0` and `ε^M → −1`, while `ε^F = γ`; and
`ε^H < γ` for every `σ > 0`. Equality holds as `σ → 0` (`dyn_ordering_sigma_zero`). -/
theorem dyn_ordering_sigma_infty {γ a : ℝ} (hγ : 0 < γ) (ha : 0 < a) :
    Tendsto (fun σ => 1 / (1 / γ + σ * a)) atTop (𝓝 0) ∧
      Tendsto (fun σ => (1 - σ * a) / (1 / γ + σ * a)) atTop (𝓝 (-1)) ∧
      ∀ σ, 0 < σ → 1 / (1 / γ + σ * a) < γ := by
  have hg : 0 < 1 / γ := by positivity
  have hD : Tendsto (fun σ : ℝ => 1 / γ + σ * a) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const ha)
  have h0 : Tendsto (fun σ => 1 / (1 / γ + σ * a)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hD
  refine ⟨h0, ?_, fun σ hσ => ?_⟩
  · have h2 : Tendsto (fun σ => -1 + (1 + 1 / γ) * (1 / (1 / γ + σ * a))) atTop
        (𝓝 (-1 + (1 + 1 / γ) * 0)) := tendsto_const_nhds.add (h0.const_mul _)
    rw [mul_zero, add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with σ hσ
    have : 0 < 1 / γ + σ * a := by positivity
    field_simp
    ring
  · rw [div_lt_iff₀ (by positivity)]
    have : 0 < γ * (σ * a) := by positivity
    have e : γ * (1 / γ) = 1 := by field_simp
    nlinarith

/-! ### Relative hours across periods -/

/-- AKMM, (12.23), p. 346: with the Euler equation `c_t^{−σ} = βRc_{t+1}^{−σ}` and (12.13) at
`t` and `t + 1`, `log(ℓ_{t+1}/ℓ_t) = γ log(w_{t+1}/w_t) + γ log((1 − τ_{t+1})/(1 − τ_t))
− γ log(βR)`: the elasticity of relative hours with respect to relative wages, and to relative
net-of-tax rates, is `γ`. -/
theorem eq_12_23 {ψ γ σ β R c₀ c₁ l₀ l₁ w₀ w₁ τ₀ τ₁ : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hβR : 0 < β * R) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hl₀ : 0 < l₀) (hl₁ : 0 < l₁) (hw₀ : 0 < w₀)
    (hw₁ : 0 < w₁) (hτ₀ : τ₀ < 1) (hτ₁ : τ₁ < 1)
    (heuler : c₀ ^ (-σ) = β * R * c₁ ^ (-σ))
    (h₀ : ψ * l₀ ^ (1 / γ) = c₀ ^ (-σ) * (1 - τ₀) * w₀)
    (h₁ : ψ * l₁ ^ (1 / γ) = c₁ ^ (-σ) * (1 - τ₁) * w₁) :
    Real.log (l₁ / l₀) = γ * Real.log (w₁ / w₀) + γ * Real.log ((1 - τ₁) / (1 - τ₀)) -
      γ * Real.log (β * R) := by
  have ht₀ : 0 < 1 - τ₀ := by linarith
  have ht₁ : 0 < 1 - τ₁ := by linarith
  have hp₀ : 0 < c₀ ^ (-σ) := Real.rpow_pos_of_pos hc₀ _
  have hp₁ : 0 < c₁ ^ (-σ) := Real.rpow_pos_of_pos hc₁ _
  have e₀ := congrArg Real.log h₀
  have e₁ := congrArg Real.log h₁
  have ee := congrArg Real.log heuler
  rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl₀ _).ne', Real.log_rpow hl₀,
    Real.log_mul (by positivity) hw₀.ne', Real.log_mul hp₀.ne' ht₀.ne'] at e₀
  rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl₁ _).ne', Real.log_rpow hl₁,
    Real.log_mul (by positivity) hw₁.ne', Real.log_mul hp₁.ne' ht₁.ne'] at e₁
  rw [Real.log_mul hβR.ne' hp₁.ne'] at ee
  rw [Real.log_div hl₁.ne' hl₀.ne', Real.log_div hw₁.ne' hw₀.ne',
    Real.log_div ht₁.ne' ht₀.ne']
  have : 1 / γ * (Real.log l₁ - Real.log l₀) = Real.log w₁ - Real.log w₀ +
      (Real.log (1 - τ₁) - Real.log (1 - τ₀)) - Real.log (β * R) := by linarith
  have e : Real.log l₁ - Real.log l₀ = γ * (1 / γ * (Real.log l₁ - Real.log l₀)) := by
    field_simp
  rw [e, this]
  ring

end AKMM.LaborSupply
