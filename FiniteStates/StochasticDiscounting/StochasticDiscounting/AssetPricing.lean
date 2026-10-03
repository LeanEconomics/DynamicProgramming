/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDiscounting.Valuation
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Asset pricing in a Markov environment

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.3.1–§6.3.2
(pp. 199–209).

* Markov pricing (6.32): with `Mₜ₊₁ = m(Xₜ, Xₜ₊₁)` and `Gₜ₊₁ = g(Xₜ, Xₜ₊₁)`, the
  price of a one-period payoff is `π(x) = ∑ m(x, x')g(x, x')P(x, x')`.
* An ex-dividend claim on `Dₜ = d(Xₜ)` satisfies (6.34)–(6.35), `π = Aπ + Ad`
  with the Arrow–Debreu discount operator `A(x, x') = m(x, x')P(x, x')`; when
  `ρ(A) < 1` the equilibrium price is `π* = (I − A)⁻¹Ad = ∑_{k≥1} Aᵏd`.
  Exercise 6.3.1: `ρ(A) < 1` is necessary and sufficient for a unique positive
  solution when `m, d ≫ 0` (Lemma 6.1.4). Exercise 6.3.2: the risk-neutral case
  `m ≡ β` needs `β < 1`. Exercise 6.3.3: `π*` satisfies the pricing equation.
  Exercise 6.3.4 and §6.3.1.6: a cum-dividend claim satisfies `π = d + Aπ`, so
  `π = (I − A)⁻¹d = ∑_{k≥0} Aᵏd`, the forward sum, and exceeds the ex-dividend
  price by `d`.
* Nonstationary dividends (§6.3.2): Exercise 6.3.5 in finite form, the
  price-dividend equation (6.39) with the operator (6.40), and Exercise 6.3.6:
  `v* = (I − A)⁻¹A𝟙 = ∑_{t≥1} Aᵗ𝟙`. Exercise 6.3.7: with Gaussian shocks and the
  Lucas SDF, `A(x, x') = β exp(−γμ_c + μ_d + (1 − γ)x + (γ²σ_c² + σ_d²)/2)P(x, x')`,
  by the Gaussian moment generating function.
-/

open Matrix Finset Filter Topology Function MeasureTheory ProbabilityTheory

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Markov pricing (§6.3.1.4) -/

omit [DecidableEq X] in
/-- The Markov pricing equation (6.32): the price of the payoff `g(Xₜ, Xₜ₊₁)` under the SDF
`m(Xₜ, Xₜ₊₁)` in state `x` is `∑ m(x, x')g(x, x')P(x, x')`. -/
def markovPrice (m g : X → X → ℝ) (P : Matrix X X ℝ) (x : X) : ℝ :=
  ∑ x', m x x' * g x x' * P x x'

omit [Fintype X] [DecidableEq X] in
/-- The Arrow–Debreu discount operator (6.35), Remark 6.3.1: `A(x, x') = m(x, x')P(x, x')`, the
discount operator (6.4) with `b = m`. -/
def adOp (m : X → X → ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ := discountOp m P

omit [Fintype X] [DecidableEq X] in
theorem adOp_apply (m : X → X → ℝ) (P : Matrix X X ℝ) (x x' : X) :
    adOp m P x x' = m x x' * P x x' := rfl

omit [DecidableEq X] in
/-- Risk-neutral pricing (6.27): a payoff `g(x')` priced with `m ≡ β` is `β(Pg)(x)`. -/
theorem markovPrice_const (β : ℝ) (g : X → ℝ) (P : Matrix X X ℝ) (x : X) :
    markovPrice (fun _ _ => β) (fun _ x' => g x') P x = β * (P *ᵥ g) x := by
  simp only [markovPrice, mulVec, dotProduct, mul_sum]
  exact sum_congr rfl fun x' _ => by ring

omit [DecidableEq X] in
/-- The payoff `g(x')` of a claim on next period's state is priced by `(Ag)(x)`: Remark 6.3.1,
`A` applies one period of discounting. -/
theorem markovPrice_eq_adOp_mulVec (m : X → X → ℝ) (g : X → ℝ) (P : Matrix X X ℝ) (x : X) :
    markovPrice m (fun _ x' => g x') P x = (adOp m P *ᵥ g) x := by
  simp only [markovPrice, mulVec, dotProduct, adOp_apply]
  exact sum_congr rfl fun x' _ => by ring

/-! ### Pricing a stationary dividend stream (§6.3.1.5) -/

variable [Nonempty X]

/-- The ex-dividend pricing equation (6.34)–(6.35): `π = A(π + d)`, i.e. `π = Aπ + Ad`. -/
def IsExDivPrice (A : Matrix X X ℝ) (d π : X → ℝ) : Prop := π = A *ᵥ π + A *ᵥ d

/-- The equilibrium ex-dividend price function `π* = (I − A)⁻¹Ad` (p. 206). -/
noncomputable def exDivPrice (A : Matrix X X ℝ) (d : X → ℝ) : X → ℝ := (1 - A)⁻¹ *ᵥ (A *ᵥ d)

/-- Exercise 6.3.3 (p. 206): `π*` solves the pricing equation (6.33)–(6.34). -/
theorem isExDivPrice_exDivPrice {A : Matrix X X ℝ} (hρ : specRad A < 1) (d : X → ℝ) :
    IsExDivPrice A d (exDivPrice A d) := by
  unfold IsExDivPrice exDivPrice
  rw [add_comm]
  exact inv_mulVec_eq_add hρ _

/-- `π*` is the unique solution of (6.34) when `ρ(A) < 1` (p. 206). -/
theorem eq_exDivPrice_of_isExDivPrice {A : Matrix X X ℝ} (hρ : specRad A < 1) {d π : X → ℝ}
    (hπ : IsExDivPrice A d π) : π = exDivPrice A d :=
  (eq_add_mulVec_iff hρ (A *ᵥ d) π).1 (hπ.trans (add_comm _ _))

/-- `π* = ∑_{k≥1} Aᵏd` (p. 206): the ex-dividend price is the discounted value of all future
dividends, by Theorem 6.1.1. -/
theorem exDivPrice_eq_tsum {A : Matrix X X ℝ} (hρ : specRad A < 1) (d : X → ℝ) :
    exDivPrice A d = ∑' k : ℕ, A ^ (k + 1) *ᵥ d := by
  unfold exDivPrice
  rw [inv_mulVec_eq_tsum hρ]
  exact tsum_congr fun k => by rw [mulVec_mulVec, ← pow_succ]

omit [DecidableEq X] [Nonempty X] in
/-- If `P` is Markov and `m, d ≫ 0` then `Ad ≫ 0`. -/
theorem adOp_mulVec_pos {m : X → X → ℝ} (hm : ∀ x x', 0 < m x x') {P : Matrix X X ℝ}
    (hP : IsMarkov P) {d : X → ℝ} (hd : ∀ x, 0 < d x) (x : X) : 0 < (adOp m P *ᵥ d) x := by
  classical
  obtain ⟨x', hx'⟩ : ∃ x', 0 < P x x' := by
    by_contra h
    have h0 : ∑ x', P x x' = 0 :=
      sum_eq_zero fun x' _ => le_antisymm (not_lt.1 fun hx => h ⟨x', hx⟩) (hP.nonneg x x')
    rw [hP.rowsum] at h0
    exact one_ne_zero h0
  exact sum_pos' (fun y _ => mul_nonneg (mul_nonneg (hm x y).le (hP.nonneg x y)) (hd y).le)
    ⟨x', mem_univ x', mul_pos (mul_pos (hm x x') hx') (hd x')⟩

omit [DecidableEq X] in
/-- Exercise 6.3.1 (p. 206): when `m, d ≫ 0` and `P` is Markov, `ρ(A) < 1` is necessary and
sufficient for (6.34) to have a unique solution in `(0, ∞)^X`, by Lemma 6.1.4 with `h = Ad ≫ 0`. -/
theorem specRad_lt_one_iff_existsUnique_pos_exDivPrice {m : X → X → ℝ} (hm : ∀ x x', 0 < m x x')
    {P : Matrix X X ℝ} (hP : IsMarkov P) {d : X → ℝ} (hd : ∀ x, 0 < d x) :
    specRad (adOp m P) < 1 ↔ ∃! π : X → ℝ, (∀ x, 0 < π x) ∧ IsExDivPrice (adOp m P) d π := by
  classical
  have h := specRad_lt_one_iff_existsUnique_pos (L := adOp m P)
    (discountOp_nonneg (fun x x' => (hm x x').le) hP.nonneg) (adOp_mulVec_pos hm hP hd)
  rw [h]
  unfold IsExDivPrice
  simp only [add_comm (adOp m P *ᵥ d)]

omit [DecidableEq X] in
/-- Exercise 6.3.2 (p. 206): in the risk-neutral case `m ≡ β ≥ 0`, `ρ(A) = β`, so `ρ(A) < 1` iff
`β < 1`. -/
theorem specRad_adOp_const {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ : 0 ≤ β) :
    specRad (adOp (fun _ _ => β) P) = β := by
  classical
  unfold adOp
  rw [discountOp_const, specRad_smul_isMarkov hP hβ]

/-- Exercise 6.3.4 (p. 206): a cum-dividend claim pays `Dₜ` to the buyer, so its price obeys
`π = d + Aπ`, (6.37). -/
def IsCumDivPrice (A : Matrix X X ℝ) (d π : X → ℝ) : Prop := π = d + A *ᵥ π

/-- The cum-dividend price `(I − A)⁻¹d`. -/
noncomputable def cumDivPrice (A : Matrix X X ℝ) (d : X → ℝ) : X → ℝ := (1 - A)⁻¹ *ᵥ d

/-- Exercise 6.3.4: `(I − A)⁻¹d` is the unique solution of `π = d + Aπ`. -/
theorem isCumDivPrice_iff {A : Matrix X X ℝ} (hρ : specRad A < 1) (d π : X → ℝ) :
    IsCumDivPrice A d π ↔ π = cumDivPrice A d :=
  eq_add_mulVec_iff hρ d π

/-- §6.3.1.6, the forward sum representation: `π = ∑ₜ Aᵗd`, the expected present value of the
dividend stream with the time-`t` dividend discounted by `M₁⋯Mₜ`. -/
theorem cumDivPrice_eq_tsum {A : Matrix X X ℝ} (hρ : specRad A < 1) (d : X → ℝ) :
    cumDivPrice A d = ∑' t : ℕ, A ^ t *ᵥ d :=
  inv_mulVec_eq_tsum hρ d

/-- The cum-dividend price exceeds the ex-dividend price by the current dividend. -/
theorem cumDivPrice_eq_add_exDivPrice {A : Matrix X X ℝ} (hρ : specRad A < 1) (d : X → ℝ) :
    cumDivPrice A d = d + exDivPrice A d := by
  rw [cumDivPrice_eq_tsum hρ, exDivPrice_eq_tsum hρ, (summable_pow_mulVec hρ d).tsum_eq_zero_add]
  simp

/-! ### Nonstationary dividends (§6.3.2) -/

/-- Exercise 6.3.5 (p. 207), in finite form: if `Π = ∑ᵢ wᵢ Mᵢ(D'ᵢ + Π'ᵢ)` is the price of a claim
on next period's dividend and price over the outcomes `i` with conditional probabilities `wᵢ`,
and `D, D'ᵢ ≠ 0`, then the price-dividend ratio `V = Π/D` obeys (6.38),
`V = ∑ᵢ wᵢ Mᵢ (D'ᵢ/D)(1 + Π'ᵢ/D'ᵢ)`. -/
theorem price_dividend_ratio {ι : Type*} [Fintype ι] (w M D' Pr' : ι → ℝ) {D Pr : ℝ} (hD : D ≠ 0)
    (hD' : ∀ i, D' i ≠ 0) (hPr : Pr = ∑ i, w i * (M i * (D' i + Pr' i))) :
    Pr / D = ∑ i, w i * (M i * (D' i / D) * (1 + Pr' i / D' i)) := by
  rw [hPr, sum_div]
  refine sum_congr rfl fun i _ => ?_
  have := hD' i
  field_simp

/-- The price-dividend operator (6.40) with the expected gross dividend growth `κ̄(x)`:
`A(x, x') = m(x, x')κ̄(x)P(x, x')`. In the book `κ̄(x) = ∫ exp(κ(x, η))φ(dη)`. -/
def pdOp (m : X → X → ℝ) (κbar : X → ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  discountOp (fun x x' => m x x' * κbar x) P

/-- The price-dividend equation (6.39): `v = A(𝟙 + v)`. -/
def IsPDRatio (A : Matrix X X ℝ) (v : X → ℝ) : Prop := v = A *ᵥ (fun _ => 1) + A *ᵥ v

/-- Exercise 6.3.6 (p. 208): when `ρ(A) < 1`, (6.39) has the unique solution
`v* = (I − A)⁻¹A𝟙`. -/
theorem isPDRatio_iff {A : Matrix X X ℝ} (hρ : specRad A < 1) (v : X → ℝ) :
    IsPDRatio A v ↔ v = (1 - A)⁻¹ *ᵥ (A *ᵥ fun _ => 1) :=
  eq_add_mulVec_iff hρ _ v

/-- Exercise 6.3.6, (6.41): `v* = ∑_{t≥1} Aᵗ𝟙`. -/
theorem pdRatio_eq_tsum {A : Matrix X X ℝ} (hρ : specRad A < 1) :
    (1 - A)⁻¹ *ᵥ (A *ᵥ fun _ => (1 : ℝ)) = ∑' t : ℕ, A ^ (t + 1) *ᵥ fun _ => (1 : ℝ) := by
  rw [inv_mulVec_eq_tsum hρ]
  exact tsum_congr fun t => by rw [mulVec_mulVec, ← pow_succ]

/-! ### Exercise 6.3.7: Markov growth with a Lucas SDF -/

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- `E[exp(a + bη)] = exp(a + b²/2)` for a standard normal `η`, from the Gaussian moment generating
function. -/
theorem integral_exp_add_mul_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {η : Ω → ℝ} (hη : HasLaw η (gaussianReal 0 1) ν) (a b : ℝ) :
    ∫ ω, Real.exp (a + b * η ω) ∂ν = Real.exp (a + b ^ 2 / 2) := by
  simp_rw [Real.exp_add]
  rw [integral_const_mul]
  have h := mgf_gaussianReal hη b
  unfold mgf at h
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul] at h
  rw [h, ← Real.exp_add]

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Exercise 6.3.7 (p. 208): with consumption growth `μ_c + x + σ_c η_c`, dividend growth
`μ_d + x + σ_d η_d`, standard normal shocks and the Lucas SDF `β exp(−γ g_c)`, the expected SDF
times the expected gross dividend growth is `β exp(−γμ_c + μ_d + (1 − γ)x + (γ²σ_c² + σ_d²)/2)`,
so (6.40) reads `A(x, x') = β exp(−γμ_c + μ_d + (1 − γ)x + (γ²σ_c² + σ_d²)/2)P(x, x')`. -/
theorem lucas_growth_factor {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω} {ηc ηd : Ω → ℝ}
    (hc : HasLaw ηc (gaussianReal 0 1) ν) (hd : HasLaw ηd (gaussianReal 0 1) ν)
    (β γ μc σc μd σd x : ℝ) :
    (∫ ω, β * Real.exp (-γ * (μc + x + σc * ηc ω)) ∂ν) *
        (∫ ω, Real.exp (μd + x + σd * ηd ω) ∂ν) =
      β * Real.exp (-γ * μc + μd + (1 - γ) * x + (γ ^ 2 * σc ^ 2 + σd ^ 2) / 2) := by
  have h1 : ∫ ω, β * Real.exp (-γ * (μc + x + σc * ηc ω)) ∂ν =
      β * Real.exp (-γ * (μc + x) + (-γ * σc) ^ 2 / 2) := by
    rw [integral_const_mul, ← integral_exp_add_mul_gaussian hc]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    dsimp only
    congr 1
    ring
  have h2 : ∫ ω, Real.exp (μd + x + σd * ηd ω) ∂ν = Real.exp (μd + x + σd ^ 2 / 2) :=
    integral_exp_add_mul_gaussian hd (μd + x) σd
  rw [h1, h2, mul_assoc, ← Real.exp_add]
  congr 2
  ring

end SargentStachurski.StochasticDiscounting
