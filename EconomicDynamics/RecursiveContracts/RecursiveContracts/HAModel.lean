/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Hidden action: the repeated moral-hazard model

Miao, §22.2 "Hidden Action", pp. 781–785. A risk-neutral principal owns a technology operated by
an agent whose effort `a ∈ A = [a_min, a_max]` is not observed; output `y` has density
`f (y | a)` on the output interval `[y_lo, y_hi]`, i.i.d. over time for a fixed action. In Lean a
density is a function `f : ℝ → ℝ → ℝ`, `f a y = f (y | a)`, and its effort derivative is `fa`.

* The sequence problem: the history density `π (y^t; a)` built recursively from `f`
  (`ha_histDensity`, with `ha_histDensity_succ`, `ha_histDensity_nonneg` and the i.i.d. product
  form for a constant effort plan `ha_histDensity_iid`), the principal's and the agent's lifetime
  values and the incentive and participation constraints (22.12)–(22.13) (`ha_seqIC`,
  `ha_seqPC`).
* The recursive problem of Spear and Srivastava (1987): the agent's value of a contract
  `(a(v), c(v, ·), w(v, ·))` under any effort, the principal's value, the recursive incentive
  constraint (22.14) (`ha_IC`), promise keeping (22.15) (`ha_PK`), the first-order approach
  (22.16) (`ha_FOA`) and the principal's Bellman equation (`ha_IsPrincipalValue`).
* The first-order approach is necessary: an interior effort satisfying (22.14) satisfies (22.16)
  (`eq_22_16`), with `∫ f_a = 0` (`ha_integral_fa_eq_zero`) and a concrete family of densities
  (linear in effort) for which the differentiation under the integral sign holds
  (`ha_linearDensity_hasDerivAt`).
* The Lagrangian first-order conditions (22.17)–(22.19) and their consequence (22.20)
  (`eq_22_17`, `eq_22_18`, `eq_22_19`, `eq_22_20`), from the pointwise Lagrangian
  `ha_pointLagr`, and the envelope condition `P′(v) = −λ(v)` (`ha_envelope`,
  `ha_envelope_condition`).

Departures: the book writes the agent's discount factor in (22.12)–(22.13) as `α` after assuming
the two discount factors are both `β`; the definitions take the discount factor as an argument.
The conditions (22.17) and (22.19) are derived from the maximisation of the Lagrangian's integrand
output by output (the way the book's first-order conditions in the functions `c(v, ·)` and
`w(v, ·)` arise); (22.18) from the maximisation of the Lagrangian in effort, given the
differentiation of the integrals under the integral sign.
-/

namespace Miao.RecursiveContracts

open MeasureTheory

/-! ## The sequence problem -/

/-- Miao, p. 782: the density of the output history `y^t = (y_0, …, y_t)` under the effort plan
`a`, `dπ(y^0; a) = f(y_0 | a_0) dy_0` and
`dπ(y^{t+1}; a) = f(y_{t+1} | a(y^t)) dπ(y^t; a) dy_{t+1}`.
The plan's date-`t` effort `a t` is a function of the history `y^{t−1}` of length `t`. -/
def ha_histDensity (f : ℝ → ℝ → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) :
    (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ
  | 0, y => f (a 0 Fin.elim0) (y 0)
  | t + 1, y => f (a (t + 1) (Fin.init y)) (y (Fin.last (t + 1))) *
      ha_histDensity f a t (Fin.init y)

/-- Miao, p. 782: the recursion `dπ(y^{t+1}; a) = f(y_{t+1} | a(y^t)) dπ(y^t; a)`. -/
theorem ha_histDensity_succ (f : ℝ → ℝ → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) (t : ℕ)
    (y : Fin (t + 2) → ℝ) :
    ha_histDensity f a (t + 1) y =
      f (a (t + 1) (Fin.init y)) (y (Fin.last (t + 1))) * ha_histDensity f a t (Fin.init y) :=
  rfl

/-- Miao, p. 782: the history densities are nonnegative when `f` is. -/
theorem ha_histDensity_nonneg {f : ℝ → ℝ → ℝ} (hf : ∀ a y, 0 ≤ f a y)
    (a : (t : ℕ) → (Fin t → ℝ) → ℝ) (t : ℕ) (y : Fin (t + 1) → ℝ) :
    0 ≤ ha_histDensity f a t y := by
  induction t with
  | zero => exact hf _ _
  | succ t ih => exact mul_nonneg (hf _ _) (ih _)

/-- Miao, p. 782: "for any fixed action, output is independently and identically distributed
over time": under a constant effort plan `a ≡ a₀` the history density is the product
`∏_{s ≤ t} f(y_s | a₀)`. -/
theorem ha_histDensity_iid (f : ℝ → ℝ → ℝ) {a : (t : ℕ) → (Fin t → ℝ) → ℝ} {a₀ : ℝ}
    (ha : ∀ t h, a t h = a₀) (t : ℕ) (y : Fin (t + 1) → ℝ) :
    ha_histDensity f a t y = ∏ i, f a₀ (y i) := by
  induction t with
  | zero => simp [ha_histDensity, ha]
  | succ t ih =>
    rw [ha_histDensity_succ, ih, ha, Fin.prod_univ_castSucc (n := t + 1), mul_comm]
    rfl

/-- Miao, p. 782: the principal's lifetime value `∑_t β^t ∫ v_P(y_t − c(y^t)) dπ(y^t; a)` of the
compensation plan `c` (a function of `y^t`) and effort plan `a`, with period utility `vP`. -/
noncomputable def ha_seqPrincipalValue (vP : ℝ → ℝ) (β : ℝ) (f : ℝ → ℝ → ℝ)
    (c : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) : ℝ :=
  ∑' t, β ^ t * ∫ y, vP (y (Fin.last t) - c t y) * ha_histDensity f a t y

/-- Miao, (22.12)–(22.13), pp. 782–783: the agent's lifetime value
`∑_t α^t ∫ u(c(y^t), a(y^{t−1})) dπ(y^t; a)` of the compensation plan `c` under the effort
plan `a`. -/
noncomputable def ha_seqAgentValue (u : ℝ → ℝ → ℝ) (α : ℝ) (f : ℝ → ℝ → ℝ)
    (c : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) : ℝ :=
  ∑' t, α ^ t * ∫ y, u (c t y) (a t (Fin.init y)) * ha_histDensity f a t y

/-- Miao, (22.12), p. 782: the incentive constraint of the sequence problem: no effort plan
`â` with values in `A = [a_min, a_max]` gives the agent more than the recommended plan `a`. -/
def ha_seqIC (u : ℝ → ℝ → ℝ) (α : ℝ) (f : ℝ → ℝ → ℝ) (amin amax : ℝ)
    (c : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) : Prop :=
  ∀ â : (t : ℕ) → (Fin t → ℝ) → ℝ, (∀ t h, â t h ∈ Set.Icc amin amax) →
    ha_seqAgentValue u α f c â ≤ ha_seqAgentValue u α f c a

/-- Miao, (22.13), p. 783: the participation constraint of the sequence problem. -/
def ha_seqPC (u : ℝ → ℝ → ℝ) (α : ℝ) (f : ℝ → ℝ → ℝ) (u₀ : ℝ)
    (c : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (a : (t : ℕ) → (Fin t → ℝ) → ℝ) : Prop :=
  u₀ ≤ ha_seqAgentValue u α f c a

/-! ## The recursive problem -/

/-- Miao, (22.14)–(22.15), p. 783: the agent's value `∫ [φ(c(y)) + β w(y)] f(y | ã) dy − ψ(ã)` of
the payment schedule `c` and promised-value schedule `w` when he exerts effort `ã`. -/
noncomputable def ha_agentValue (ylo yhi β : ℝ) (φ ψ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (c w : ℝ → ℝ)
    (ã : ℝ) : ℝ :=
  (∫ y in ylo..yhi, (φ (c y) + β * w y) * f ã y) - ψ ã

/-- Miao, p. 783: the principal's value `∫ [(y − c(y)) + β P(w(y))] f(y | a) dy` of the contract
`(a, c, w)` given the continuation value function `P`. -/
noncomputable def ha_principalValue (ylo yhi β : ℝ) (P : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (a : ℝ)
    (c w : ℝ → ℝ) : ℝ :=
  ∫ y in ylo..yhi, (y - c y + β * P (w y)) * f a y

/-- Miao, (22.14), p. 783: the recursive incentive constraint: the recommended effort `a` is
optimal for the agent among all efforts in `A = [a_min, a_max]`. -/
def ha_IC (ylo yhi β : ℝ) (φ ψ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (amin amax a : ℝ) (c w : ℝ → ℝ) :
    Prop :=
  ∀ ã ∈ Set.Icc amin amax,
    ha_agentValue ylo yhi β φ ψ f c w ã ≤ ha_agentValue ylo yhi β φ ψ f c w a

/-- Miao, (22.15), p. 783: promise keeping: the contract delivers at least the promised
value `v`. -/
def ha_PK (ylo yhi β : ℝ) (φ ψ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (v a : ℝ) (c w : ℝ → ℝ) : Prop :=
  v ≤ ha_agentValue ylo yhi β φ ψ f c w a

/-- Miao, (22.16), p. 784: the first-order condition replacing the incentive constraint,
`∫ [φ(c(y)) + β w(y)] f_a(y | a) dy − ψ′(a) = 0`. -/
def ha_FOA (ylo yhi β : ℝ) (φ dψ : ℝ → ℝ) (fa : ℝ → ℝ → ℝ) (a : ℝ) (c w : ℝ → ℝ) : Prop :=
  (∫ y in ylo..yhi, (φ (c y) + β * w y) * fa a y) - dψ a = 0

/-- Miao, p. 783: `P` solves the principal's Bellman equation: for each promised value `v`, `P v`
is the largest principal's value over contracts `(a, c, w)` with `a ∈ A` satisfying (22.14)
and (22.15). -/
def ha_IsPrincipalValue (ylo yhi β : ℝ) (φ ψ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (amin amax : ℝ)
    (P : ℝ → ℝ) : Prop :=
  ∀ v, IsGreatest {x | ∃ a ∈ Set.Icc amin amax, ∃ c w : ℝ → ℝ,
    ha_IC ylo yhi β φ ψ f amin amax a c w ∧ ha_PK ylo yhi β φ ψ f v a c w ∧
    x = ha_principalValue ylo yhi β P f a c w} (P v)

/-- Miao, p. 783: under the Bellman equation, the principal's value of any contract satisfying
(22.14) and (22.15) at `v` is at most `P(v)`, and some such contract attains `P(v)`. -/
theorem ha_principalValue_le {ylo yhi β : ℝ} {φ ψ : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {amin amax : ℝ}
    {P : ℝ → ℝ} (hP : ha_IsPrincipalValue ylo yhi β φ ψ f amin amax P) (v : ℝ) :
    (∀ a ∈ Set.Icc amin amax, ∀ c w : ℝ → ℝ, ha_IC ylo yhi β φ ψ f amin amax a c w →
      ha_PK ylo yhi β φ ψ f v a c w → ha_principalValue ylo yhi β P f a c w ≤ P v) ∧
    ∃ a ∈ Set.Icc amin amax, ∃ c w : ℝ → ℝ, ha_IC ylo yhi β φ ψ f amin amax a c w ∧
      ha_PK ylo yhi β φ ψ f v a c w ∧ ha_principalValue ylo yhi β P f a c w = P v := by
  refine ⟨fun a ha c w hic hpk => (hP v).2 ⟨a, ha, c, w, hic, hpk, rfl⟩, ?_⟩
  obtain ⟨a, ha, c, w, hic, hpk, heq⟩ := (hP v).1
  exact ⟨a, ha, c, w, hic, hpk, heq.symm⟩

/-! ## The first-order approach -/

/-- Miao, p. 785 (used in the proofs of Propositions 22.2.1 and 22.2.2): `∫ f_a(y | a) dy = 0`,
differentiating `∫ f(y | ã) dy = 1` in `ã` at `a`. -/
theorem ha_integral_fa_eq_zero {ylo yhi a : ℝ} {f fa : ℝ → ℝ → ℝ}
    (hf1 : ∀ ã, ∫ y in ylo..yhi, f ã y = 1)
    (hd : HasDerivAt (fun ã => ∫ y in ylo..yhi, f ã y) (∫ y in ylo..yhi, fa a y) a) :
    ∫ y in ylo..yhi, fa a y = 0 := by
  have hconst : (fun ã => ∫ y in ylo..yhi, f ã y) = fun _ => (1 : ℝ) := funext hf1
  rw [hconst] at hd
  exact hd.unique (hasDerivAt_const a 1)

/-- Miao, p. 783 ("we assume that `f(y | a)` is twice continuously differentiable in `a`"): a
concrete family of densities for which differentiation under the integral sign holds: for
`f(y | a) = f₀(y) + a f₁(y)` with `f₀, f₁` integrable, `f_a = f₁` and
`d/dã ∫ g(y) f(y | ã) dy = ∫ g(y) f₁(y) dy` for every `g` with `g f₀`, `g f₁` integrable. -/
theorem ha_linearDensity_hasDerivAt {ylo yhi : ℝ} {g f₀ f₁ : ℝ → ℝ}
    (h₀ : IntervalIntegrable (fun y => g y * f₀ y) volume ylo yhi)
    (h₁ : IntervalIntegrable (fun y => g y * f₁ y) volume ylo yhi) (a : ℝ) :
    HasDerivAt (fun ã => ∫ y in ylo..yhi, g y * (f₀ y + ã * f₁ y))
      (∫ y in ylo..yhi, g y * f₁ y) a := by
  have hrw : (fun ã => ∫ y in ylo..yhi, g y * (f₀ y + ã * f₁ y)) =
      fun ã => (∫ y in ylo..yhi, g y * f₀ y) + ã * ∫ y in ylo..yhi, g y * f₁ y := by
    funext ã
    have hsplit : (fun y => g y * (f₀ y + ã * f₁ y)) =
        fun y => g y * f₀ y + ã * (g y * f₁ y) := by
      funext y
      ring
    rw [hsplit, intervalIntegral.integral_add h₀ (h₁.const_mul ã),
      intervalIntegral.integral_const_mul]
  rw [hrw]
  simpa using ((hasDerivAt_id a).mul_const (∫ y in ylo..yhi, g y * f₁ y)).const_add
    (∫ y in ylo..yhi, g y * f₀ y)

/-- Miao, (22.16), p. 784: the first-order approach is necessary: if the recommended effort `a`
is interior to `A = [a_min, a_max]` and satisfies the recursive incentive constraint (22.14),
and the agent's value is differentiable in effort (differentiation under the integral sign,
`d/dã ∫ h f(· | ã) = ∫ h f_a(· | a)` at `a`), then (22.16) holds. -/
theorem eq_22_16 {ylo yhi β amin amax a : ℝ} {φ ψ dψ : ℝ → ℝ} {f fa : ℝ → ℝ → ℝ}
    {c w : ℝ → ℝ} (hic : ha_IC ylo yhi β φ ψ f amin amax a c w)
    (hlo : amin < a) (hhi : a < amax)
    (hI : HasDerivAt (fun ã => ∫ y in ylo..yhi, (φ (c y) + β * w y) * f ã y)
      (∫ y in ylo..yhi, (φ (c y) + β * w y) * fa a y) a)
    (hψ : HasDerivAt ψ (dψ a) a) :
    ha_FOA ylo yhi β φ dψ fa a c w := by
  have hmax : IsLocalMax (ha_agentValue ylo yhi β φ ψ f c w) a :=
    Filter.eventually_of_mem (Icc_mem_nhds hlo hhi) hic
  exact hmax.hasDerivAt_eq_zero (hI.sub hψ)

/-! ## The Lagrangian and its first-order conditions -/

/-- Miao, p. 784: the integrand of the Lagrangian `L` at output `y`, as a function of the
payment `x = c(v, y)` and promised value `z = w(v, y)`, with `fy = f(y | a)`, `fay = f_a(y | a)`:
`[(y − x) + β P(z)] fy + μ [φ(x) + β z] fay + λ [φ(x) + β z] fy`. Integrating it over `y` and
subtracting `μ ψ′(a) + λ (ψ(a) + v)` gives `L`. -/
noncomputable def ha_pointLagr (β : ℝ) (φ P : ℝ → ℝ) (μ lam y fy fay x z : ℝ) : ℝ :=
  (y - x + β * P z) * fy + μ * ((φ x + β * z) * fay) + lam * ((φ x + β * z) * fy)

/-- Miao, (22.17), p. 784: the first-order condition in the payment: if the payment `x = c(v, y)`
maximises the Lagrangian's integrand at `y` (locally), `f(y | a) > 0` and `φ′(x) > 0`, then
`1 / φ′(c(v, y)) = λ(v) + μ(v) f_a(y | a) / f(y | a)`. -/
theorem eq_22_17 {β : ℝ} {φ dφ P : ℝ → ℝ} {μ lam y fy fay x z : ℝ}
    (hmax : IsLocalMax (fun x' => ha_pointLagr β φ P μ lam y fy fay x' z) x)
    (hφ : HasDerivAt φ (dφ x) x) (hfy : 0 < fy) (hdφ : 0 < dφ x) :
    1 / dφ x = lam + μ * (fay / fy) := by
  have hd : HasDerivAt (fun x' => ha_pointLagr β φ P μ lam y fy fay x' z)
      (-fy + μ * (dφ x * fay) + lam * (dφ x * fy)) x := by
    have h1 : HasDerivAt (fun x' => (y - x' + β * P z) * fy) (-1 * fy) x :=
      (((hasDerivAt_id x).const_sub y).add_const (β * P z)).mul_const fy
    have h2 : HasDerivAt (fun x' => (φ x' + β * z) * fay) (dφ x * fay) x :=
      (hφ.add_const (β * z)).mul_const fay
    have h3 : HasDerivAt (fun x' => (φ x' + β * z) * fy) (dφ x * fy) x :=
      (hφ.add_const (β * z)).mul_const fy
    exact ((h1.add (h2.const_mul μ)).add (h3.const_mul lam)).congr_deriv (by ring)
  have h0 := hmax.hasDerivAt_eq_zero hd
  field_simp
  linear_combination (-1) * h0

/-- Miao, (22.19), p. 785: the first-order condition in the promised value: if `z = w(v, y)`
maximises the Lagrangian's integrand at `y` (locally), then
`β P′(w(v, y)) f(y | a) + μ β f_a(y | a) + λ β f(y | a) = 0`. -/
theorem eq_22_19 {β : ℝ} {φ P dP : ℝ → ℝ} {μ lam y fy fay x z : ℝ}
    (hmax : IsLocalMax (fun z' => ha_pointLagr β φ P μ lam y fy fay x z') z)
    (hP : HasDerivAt P (dP z) z) :
    β * dP z * fy + μ * β * fay + lam * β * fy = 0 := by
  have hd : HasDerivAt (fun z' => ha_pointLagr β φ P μ lam y fy fay x z')
      (β * dP z * fy + μ * (β * fay) + lam * (β * fy)) z := by
    have h1 : HasDerivAt (fun z' => (y - x + β * P z') * fy) (β * dP z * fy) z :=
      ((hP.const_mul β).const_add (y - x)).mul_const fy
    have h2 : HasDerivAt (fun z' => (φ x + β * z') * fay) (β * 1 * fay) z :=
      (((hasDerivAt_id z).const_mul β).const_add (φ x)).mul_const fay
    have h3 : HasDerivAt (fun z' => (φ x + β * z') * fy) (β * 1 * fy) z :=
      (((hasDerivAt_id z).const_mul β).const_add (φ x)).mul_const fy
    exact ((h1.add (h2.const_mul μ)).add (h3.const_mul lam)).congr_deriv (by ring)
  have h0 := hmax.hasDerivAt_eq_zero hd
  linear_combination h0

/-- Miao, (22.20), p. 785: "(22.17) and (22.19) imply" `P′(w(v, y)) = −1 / φ′(c(v, y))`, when the
payment and the promised value both maximise the Lagrangian's integrand at `y`, `β > 0`,
`f(y | a) > 0` and `φ′ > 0`. -/
theorem eq_22_20 {β : ℝ} {φ dφ P dP : ℝ → ℝ} {μ lam y fy fay x z : ℝ}
    (hc : IsLocalMax (fun x' => ha_pointLagr β φ P μ lam y fy fay x' z) x)
    (hw : IsLocalMax (fun z' => ha_pointLagr β φ P μ lam y fy fay x z') z)
    (hφ : HasDerivAt φ (dφ x) x) (hP : HasDerivAt P (dP z) z) (hβ : 0 < β) (hfy : 0 < fy)
    (hdφ : 0 < dφ x) :
    dP z = -1 / dφ x := by
  have h17 := eq_22_17 hc hφ hfy hdφ
  have h19 := eq_22_19 hw hP
  rw [neg_div, h17]
  have h19' : dP z * fy + μ * fay + lam * fy = 0 :=
    mul_left_cancel₀ hβ.ne' (by linear_combination h19)
  field_simp
  linear_combination h19'

/-- Miao, (22.18), pp. 784–785: the first-order condition in effort. If the recommended effort
`a` maximises (locally) the Lagrangian
`L(ã) = ∫ g f(· | ã) + μ (∫ h f_a(· | ã) − ψ′(ã)) + λ (∫ h f(· | ã) − ψ(ã) − v)`, with
`g(y) = y − c(v, y) + β P(w(v, y))` and `h(y) = φ(c(v, y)) + β w(v, y)`, the integrals are
differentiated under the integral sign, and (22.16) holds, then
`0 = ∫ g f_a(· | a) + μ (∫ h f_aa(· | a) − ψ″(a))`: the `λ` term is `λ` times (22.16). -/
theorem eq_22_18 {ylo yhi a μ lam v : ℝ} {g h ψ dψ ddψ : ℝ → ℝ} {f fa faa : ℝ → ℝ → ℝ}
    (hmax : IsLocalMax (fun ã => (∫ y in ylo..yhi, g y * f ã y) +
      μ * ((∫ y in ylo..yhi, h y * fa ã y) - dψ ã) +
      lam * ((∫ y in ylo..yhi, h y * f ã y) - ψ ã - v)) a)
    (hg : HasDerivAt (fun ã => ∫ y in ylo..yhi, g y * f ã y) (∫ y in ylo..yhi, g y * fa a y) a)
    (hh1 : HasDerivAt (fun ã => ∫ y in ylo..yhi, h y * fa ã y)
      (∫ y in ylo..yhi, h y * faa a y) a)
    (hh0 : HasDerivAt (fun ã => ∫ y in ylo..yhi, h y * f ã y)
      (∫ y in ylo..yhi, h y * fa a y) a)
    (hψ : HasDerivAt ψ (dψ a) a) (hdψ : HasDerivAt dψ (ddψ a) a)
    (hfoa : (∫ y in ylo..yhi, h y * fa a y) - dψ a = 0) :
    0 = (∫ y in ylo..yhi, g y * fa a y) + μ * ((∫ y in ylo..yhi, h y * faa a y) - ddψ a) := by
  have hd := (hg.add ((hh1.sub hdψ).const_mul μ)).add (((hh0.sub hψ).sub_const v).const_mul lam)
  have h0 := hmax.hasDerivAt_eq_zero hd
  rw [hfoa, mul_zero, add_zero] at h0
  exact h0.symm

/-! ## The envelope condition -/

/-- Miao, p. 785 ("By the envelope condition, `P′(v) = −λ(v)`"), in abstract form. Let contracts
`x ∈ X` have principal's value `F x`, first-order-approach residual `G x` (constraint `G x = 0`)
and agent's value `K x` (promise keeping `K x ≥ v`). Suppose that for each `v′` the value `P v′`
is attained by some feasible contract, that the contract `xs` attaining `P v` maximises the
Lagrangian `F + μ G + λ (K − v)` over all contracts with `λ ≥ 0`, and complementary slackness
`λ (K xs − v) = 0`. If `P` is differentiable at `v`, then `P′(v) = −λ`. -/
theorem ha_envelope {X : Type*} (F G K : X → ℝ) (P : ℝ → ℝ) (xs : X) {v p μ lam : ℝ}
    (hP : HasDerivAt P p v) (hlam : 0 ≤ lam)
    (hfeas : ∀ v', ∃ x, G x = 0 ∧ v' ≤ K x ∧ P v' ≤ F x)
    (hsaddle : ∀ x, F x + μ * G x + lam * (K x - v) ≤ F xs + μ * G xs + lam * (K xs - v))
    (hval : F xs = P v) (hG : G xs = 0) (hcs : lam * (K xs - v) = 0) :
    p = -lam := by
  have hle : ∀ v', P v' - (P v - lam * (v' - v)) ≤ P v - (P v - lam * (v - v)) := by
    intro v'
    obtain ⟨x, hGx, hKx, hPx⟩ := hfeas v'
    have h1 := hsaddle x
    rw [hGx, hG, hcs, hval] at h1
    nlinarith
  have hmax : IsLocalMax (fun v' => P v' - (P v - lam * (v' - v))) v :=
    Filter.Eventually.of_forall hle
  have hd : HasDerivAt (fun v' => P v' - (P v - lam * (v' - v))) (p - -(lam * 1)) v :=
    hP.sub ((((hasDerivAt_id v).sub_const v).const_mul lam).const_sub (P v))
  have h0 := hmax.hasDerivAt_eq_zero hd
  linarith

/-- Miao, p. 785: the envelope condition `P′(v) = −λ(v)` for the recursive moral-hazard problem
under the first-order approach: contracts are triples `(a, c, w)`, the principal's value is
`ha_principalValue`, the constraint is (22.16) and promise keeping is (22.15). The hypotheses
are those of `ha_envelope` for this problem. -/
theorem ha_envelope_condition {ylo yhi β v p μ lam : ℝ} {φ ψ dψ P : ℝ → ℝ} {f fa : ℝ → ℝ → ℝ}
    {a : ℝ} {c w : ℝ → ℝ} (hP : HasDerivAt P p v) (hlam : 0 ≤ lam)
    (hfeas : ∀ v', ∃ a' c' w', ha_FOA ylo yhi β φ dψ fa a' c' w' ∧
      ha_PK ylo yhi β φ ψ f v' a' c' w' ∧ P v' ≤ ha_principalValue ylo yhi β P f a' c' w')
    (hsaddle : ∀ a' c' w', ha_principalValue ylo yhi β P f a' c' w' +
      μ * ((∫ y in ylo..yhi, (φ (c' y) + β * w' y) * fa a' y) - dψ a') +
      lam * (ha_agentValue ylo yhi β φ ψ f c' w' a' - v) ≤
      ha_principalValue ylo yhi β P f a c w +
      μ * ((∫ y in ylo..yhi, (φ (c y) + β * w y) * fa a y) - dψ a) +
      lam * (ha_agentValue ylo yhi β φ ψ f c w a - v))
    (hval : ha_principalValue ylo yhi β P f a c w = P v) (hfoa : ha_FOA ylo yhi β φ dψ fa a c w)
    (hcs : lam * (ha_agentValue ylo yhi β φ ψ f c w a - v) = 0) :
    p = -lam := by
  refine ha_envelope (X := ℝ × (ℝ → ℝ) × (ℝ → ℝ))
    (fun x => ha_principalValue ylo yhi β P f x.1 x.2.1 x.2.2)
    (fun x => (∫ y in ylo..yhi, (φ (x.2.1 y) + β * x.2.2 y) * fa x.1 y) - dψ x.1)
    (fun x => ha_agentValue ylo yhi β φ ψ f x.2.1 x.2.2 x.1) P (a, c, w) hP hlam ?_
    (fun x => hsaddle x.1 x.2.1 x.2.2) hval hfoa hcs
  intro v'
  obtain ⟨a', c', w', h1, h2, h3⟩ := hfeas v'
  exact ⟨(a', c', w'), h1, h2, h3⟩

end Miao.RecursiveContracts
