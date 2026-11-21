/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.EUTools

/-!
# §7.4: the infinite-horizon Maximum Principle and the transversality condition

Miao, §7.4, pp. 217–221, one-dimensional as in the book: `X ⊆ ℝ₊`, `A ⊆ ℝ`. We reuse the
optimal control model `OCModel ℝ ℝ Z` of §6.4 and the stochastic setting of §6.5
(`OCMaxPrinciple`): a probability space `(Ω, P)` with a filtration `(ℱ_t)` to which the shocks
`z_t` are adapted; a plan is an adapted process `(a_t)`; its states `x_t` follow (5.14)
(`OCModel.path`); `E_t` is `P[· | ℱ_t]`. The horizon `T` and terminal reward `u_T` of `OCModel` are
not used; the rewards may depend on `t` (the book's `u` is the case `u_t = u`).

* `eu_lagTerm` is the `t`-th summand of the Lagrangian (7.29). `eq_7_29_a`, `eq_7_29_x`: its
  pathwise derivatives in `a_t` and in `x_{t+1}` (which appears in the summands `t` and `t + 1`).
  `eq_7_30`, `eq_7_31`: the conditional expectations `E_t` of these derivatives (divided by `βᵗ`)
  are `∂H_t/∂a` (`OCModel.Ha`) and `∂H_t/∂x − μ_t` (`OCModel.Hx`), so the first-order conditions
  of (7.29) are (7.30) `∂H_t/∂a = 0` and (7.31) `∂H_t/∂x = μ_t`.
* **The link with dynamic programming** (p. 218): with `μ_t = V_x(x_t, z_t)` for a function `V`
  (the solution of (7.19)) and `E_t` integration against `Q(z_t, ·)`, `∂H_t/∂a` is the right side
  of the first-order condition and `∂H_t/∂x` that of the envelope condition (`link_7_30`,
  `link_7_31`); hence the DP conditions along the path are equivalent to (7.30) and (7.31)
  (`link_7_30_iff`, `link_7_31_iff`).
* `eu_mp_core`: for a candidate satisfying (7.30)–(7.31) with a pathwise Hamiltonian concave on
  `X × A`, every feasible plan has `S_T ≤ S*_T + β^{T+1} E[μ*_{T+1}(x*_{T+1} − x_{T+1})]`, where
  `S_T = Σ_{t ≤ T} βᵗ E u(x_t, z_t, a_t)` is the partial sum of the objective.
* **Theorem 7.4.1** (`theorem_7_4_1`): under the book's hypotheses, every feasible plan has
  `S_T ≤ S*_T + w_T` with `w_T = β^{T+1} E[μ*_{T+1} x*_{T+1}] → 0`. `theorem_7_4_1_limit`: hence
  `lim S_T ≤ lim S*_T` whenever both limits exist in `[−∞, +∞]` (the competing plan may have
  `J = −∞`), and `theorem_7_4_1_eventually`: when `S*_T → J*`, the competing partial sums are
  eventually below `J* + ε`, whether or not they converge.

**Departures.** (1) As in Theorem 6.5.1 we assume the pathwise Hamiltonian concave; here it
follows from Assumptions 7.3.3 and 6.4.12 and `μ*_{t+1} ≥ 0`. (2) The telescoping needs the
integrability `eu_MPIntInf` for the candidate and the competing plan; optimality is among the plans
for which it holds. (3) The objective is the limit of the partial sums of expectations, which is
what the proof compares (it is `E Σ βᵗ u` under dominated or monotone convergence). (4) The proof
does not use Assumption 6.4.3, the strictness in Assumption 7.3.3, or `β < 1`; only `β ≥ 0`.
(5) The interiority `a*_t ∈ int Γ(x*_t, z_t)`, `x*_t ∈ int X` is used only to make `u` and `φ`
differentiable at `(x*_t, a*_t)` (by Assumptions 7.3.4 and 6.4.14).
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

namespace OCModel

variable {Z : Type*} [MeasurableSpace Z] {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- **Assumption 7.3.3** (Miao, p. 208) for the rewards `u_t`: `u_t(·, z, ·)` is concave on
`X × A`, strictly when `x ≠ x′`. -/
def eu_Assumption733 (M : OCModel ℝ ℝ Z) : Prop :=
  ∀ t z, ∀ x ∈ M.X, ∀ x' ∈ M.X, ∀ a ∈ M.A, ∀ a' ∈ M.A, ∀ θ η : ℝ, 0 < θ → 0 < η →
    θ + η = 1 →
    θ * M.u t x z a + η * M.u t x' z a' ≤ M.u t (θ * x + η * x') z (θ * a + η * a') ∧
    (x ≠ x' → θ * M.u t x z a + η * M.u t x' z a' < M.u t (θ * x + η * x') z (θ * a + η * a'))

/-- **Assumption 7.3.4** (Miao, p. 209) for the rewards `u_t`: `u_t(·, z, ·)` is continuously
differentiable on `int(X × A)`. -/
def eu_Assumption734 (M : OCModel ℝ ℝ Z) : Prop :=
  ∀ t z, ContDiffOn ℝ 1 (fun p : ℝ × ℝ => M.u t p.1 z p.2) (interior (M.X ×ˢ M.A))

/-- Assumption 7.3.3 makes `u_t(·, z, ·)` concave on the convex set `X × A`. -/
theorem eu_concaveOn_of_733 {M : OCModel ℝ ℝ Z} (h : M.eu_Assumption733) (hX : Convex ℝ M.X)
    (hA : Convex ℝ M.A) (t : ℕ) (z : Z) :
    ConcaveOn ℝ (M.X ×ˢ M.A) fun p : ℝ × ℝ => M.u t p.1 z p.2 := by
  refine ⟨hX.prod hA, fun p hp q hq a b ha hb hab => ?_⟩
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simp
  rcases hb.eq_or_lt with rfl | hb'
  · simp only [add_zero] at hab; subst hab; simp
  have := (h t z p.1 hp.1 q.1 hq.1 p.2 hp.2 q.2 hq.2 a b ha' hb' hab).1
  simpa [smul_eq_mul] using this

/-- Assumption 6.4.12 makes `φ(·, ·, z, z′)` concave on the convex set `X × A`. -/
theorem eu_concaveOn_of_6412 {M : OCModel ℝ ℝ Z} (h : M.Assumption6412) (hX : Convex ℝ M.X)
    (hA : Convex ℝ M.A) (z z' : Z) :
    ConcaveOn ℝ (M.X ×ˢ M.A) fun p : ℝ × ℝ => M.φ p.1 p.2 z z' := by
  refine ⟨hX.prod hA, fun p hp q hq a b ha hb hab => ?_⟩
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simp
  rcases hb.eq_or_lt with rfl | hb'
  · simp only [add_zero] at hab; subst hab; simp
  have := h z z' p.1 hp.1 q.1 hq.1 p.2 hp.2 q.2 hq.2 a b ha' hb' hab
  simpa [smul_eq_mul] using this

/-! ### The Lagrangian (7.29) and its first-order conditions -/

/-- The `t`-th summand of the **Lagrangian (7.29)** (Miao, p. 217) at `ω`, as a function of
`(x_t, a_t, x_{t+1}) = (y, b, y′)`:
`βᵗ u_t(y, z_t, b) − β^{t+1} μ_{t+1}(y′ − φ(y, b, z_t, z_{t+1}))`. -/
noncomputable def eu_lagTerm (M : OCModel ℝ ℝ Z) (z : ℕ → Ω → Z) (μ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω)
    (y b y' : ℝ) : ℝ :=
  M.β ^ t * M.u t y (z t ω) b - M.β ^ (t + 1) * (μ (t + 1) ω * (y' - M.φ y b (z t ω) (z (t + 1) ω)))

/-- **(7.29), the first-order condition in `a_t`** (Miao, p. 217): `a_t` appears only in the
`t`-th summand, whose derivative is `βᵗ(∂u_t/∂a + β μ_{t+1} ∂φ/∂a)`. -/
theorem eq_7_29_a (M : OCModel ℝ ℝ Z) (z : ℕ → Ω → Z) (μ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω)
    {y b y' : ℝ} (hu : DifferentiableAt ℝ (fun c => M.u t y (z t ω) c) b)
    (hφ : DifferentiableAt ℝ (fun c => M.φ y c (z t ω) (z (t + 1) ω)) b) :
    HasDerivAt (fun c => M.eu_lagTerm z μ t ω y c y') (M.β ^ t *
      (deriv (fun c => M.u t y (z t ω) c) b + M.β * (μ (t + 1) ω *
        deriv (fun c => M.φ y c (z t ω) (z (t + 1) ω)) b))) b := by
  have h : HasDerivAt (fun c => M.eu_lagTerm z μ t ω y c y')
      (M.β ^ t * deriv (fun c => M.u t y (z t ω) c) b - M.β ^ (t + 1) * (μ (t + 1) ω *
        -deriv (fun c => M.φ y c (z t ω) (z (t + 1) ω)) b)) b :=
    (hu.hasDerivAt.const_mul (M.β ^ t)).sub
      (((hφ.hasDerivAt.const_sub y').const_mul (μ (t + 1) ω)).const_mul (M.β ^ (t + 1)))
  exact h.congr_deriv (by ring)

/-- **(7.29), the first-order condition in `x_{t+1}`** (Miao, p. 217): `x_{t+1}` appears in the
summand `t` (through `−β^{t+1} μ_{t+1} x_{t+1}`) and in the summand `t + 1`; the derivative of
their sum is `β^{t+1}(∂u_{t+1}/∂x + β μ_{t+2} ∂φ/∂x − μ_{t+1})`. -/
theorem eq_7_29_x (M : OCModel ℝ ℝ Z) (z : ℕ → Ω → Z) (μ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω)
    {y b y' b' y'' : ℝ} (hu : DifferentiableAt ℝ (fun c => M.u (t + 1) c (z (t + 1) ω) b') y')
    (hφ : DifferentiableAt ℝ (fun c => M.φ c b' (z (t + 1) ω) (z (t + 1 + 1) ω)) y') :
    HasDerivAt (fun c => M.eu_lagTerm z μ t ω y b c + M.eu_lagTerm z μ (t + 1) ω c b' y'')
      (M.β ^ (t + 1) * (deriv (fun c => M.u (t + 1) c (z (t + 1) ω) b') y' + M.β *
        (μ (t + 1 + 1) ω * deriv (fun c => M.φ c b' (z (t + 1) ω) (z (t + 1 + 1) ω)) y') -
          μ (t + 1) ω)) y' := by
  have h1 : HasDerivAt (fun c => M.eu_lagTerm z μ t ω y b c)
      (0 - M.β ^ (t + 1) * (μ (t + 1) ω * (1 - 0))) y' :=
    (hasDerivAt_const y' (M.β ^ t * M.u t y (z t ω) b)).sub
      ((((hasDerivAt_id y').sub (hasDerivAt_const y' (M.φ y b (z t ω) (z (t + 1) ω)))).const_mul
        (μ (t + 1) ω)).const_mul (M.β ^ (t + 1)))
  have h2 : HasDerivAt (fun c => M.eu_lagTerm z μ (t + 1) ω c b' y'')
      (M.β ^ (t + 1) * deriv (fun c => M.u (t + 1) c (z (t + 1) ω) b') y' -
        M.β ^ (t + 1 + 1) * (μ (t + 1 + 1) ω *
          -deriv (fun c => M.φ c b' (z (t + 1) ω) (z (t + 1 + 1) ω)) y')) y' :=
    (hu.hasDerivAt.const_mul (M.β ^ (t + 1))).sub
      (((hφ.hasDerivAt.const_sub y'').const_mul (μ (t + 1 + 1) ω)).const_mul (M.β ^ (t + 1 + 1)))
  exact (h1.add h2).congr_deriv (by ring)

variable (P : Measure Ω) (ℱ : Filtration ℕ m0) (z : ℕ → Ω → Z) (M : OCModel ℝ ℝ Z)
  (μ x a : ℕ → Ω → ℝ) in
/-- The infinite-horizon **Maximum Principle system** (7.30)–(7.31) (Miao, p. 218) along the
states `x` of the plan `a`, almost surely. -/
structure eu_MPInf : Prop where
  foc_a : ∀ t, M.Ha P ℱ z μ x a t =ᵐ[P] 0
  foc_x : ∀ t, 1 ≤ t → μ t =ᵐ[P] M.Hx P ℱ z μ x a t

variable (P : Measure Ω) (z : ℕ → Ω → Z) (M : OCModel ℝ ℝ Z) (μ xs as x a : ℕ → Ω → ℝ) in
/-- The integrability needed for the telescoping in the proof of Theorem 7.4.1, for the
candidate `(xs, as)` with multipliers `μ` and a competing plan `(x, a)`, at every date. -/
structure eu_MPIntInf : Prop where
  u_s : ∀ t, Integrable (fun ω => M.u t (xs t ω) (z t ω) (as t ω)) P
  u_c : ∀ t, Integrable (fun ω => M.u t (x t ω) (z t ω) (a t ω)) P
  μΔ : ∀ t, Integrable (fun ω => μ (t + 1) ω * (xs (t + 1) ω - x (t + 1) ω)) P
  ux : ∀ t,
    Integrable (fun ω => (xs t ω - x t ω) * deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω)) P
  φx : ∀ t, Integrable (fun ω => μ (t + 1) ω *
    deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω)) P
  φxΔ : ∀ t, Integrable (fun ω => (xs t ω - x t ω) * (μ (t + 1) ω *
    deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω))) P
  ua : ∀ t,
    Integrable (fun ω => (as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω)) P
  φa : ∀ t, Integrable (fun ω => μ (t + 1) ω *
    deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)) P
  φaΔ : ∀ t, Integrable (fun ω => (as t ω - a t ω) * (μ (t + 1) ω *
    deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω))) P

variable {M : OCModel ℝ ℝ Z} {P : Measure Ω} {ℱ : Filtration ℕ m0} {z : ℕ → Ω → Z}

/-- **(7.30)** (Miao, pp. 217–218): the conditional expectation `E_t` of the derivative of the
Lagrangian in `a_t`, divided by `βᵗ` (`eq_7_29_a`), is `∂H_t/∂a`; so the first-order condition
`E_t[∂L/∂a_t] = 0` is (7.30). We need `∂u_t/∂a` along the plan `ℱ_t`-measurable and the two
terms integrable. -/
theorem eq_7_30 [IsFiniteMeasure P] {μ x a : ℕ → Ω → ℝ} {t : ℕ}
    (hum : StronglyMeasurable[ℱ t] fun ω => deriv (fun c => M.u t (x t ω) (z t ω) c) (a t ω))
    (hui : Integrable (fun ω => deriv (fun c => M.u t (x t ω) (z t ω) c) (a t ω)) P)
    (hφi : Integrable (fun ω => μ (t + 1) ω *
      deriv (fun c => M.φ (x t ω) c (z t ω) (z (t + 1) ω)) (a t ω)) P) :
    P[fun ω => deriv (fun c => M.u t (x t ω) (z t ω) c) (a t ω) + M.β * (μ (t + 1) ω *
      deriv (fun c => M.φ (x t ω) c (z t ω) (z (t + 1) ω)) (a t ω)) | ℱ t] =ᵐ[P]
      M.Ha P ℱ z μ x a t := by
  have hadd := condExp_add hui (hφi.const_mul M.β) (ℱ t)
  have hself := condExp_of_stronglyMeasurable (ℱ.le t) hum hui
  have hsmul := condExp_smul (m := ℱ t) (μ := P) M.β fun ω => μ (t + 1) ω *
      deriv (fun c => M.φ (x t ω) c (z t ω) (z (t + 1) ω)) (a t ω)
  filter_upwards [hadd, hsmul] with ω h1 h2
  have e : (fun ω => M.β * (μ (t + 1) ω *
      deriv (fun c => M.φ (x t ω) c (z t ω) (z (t + 1) ω)) (a t ω))) =
      M.β • fun ω => μ (t + 1) ω *
        deriv (fun c => M.φ (x t ω) c (z t ω) (z (t + 1) ω)) (a t ω) := by
    funext ω; simp
  refine h1.trans ?_
  rw [Pi.add_apply, hself, e, h2]
  simp [Ha]

/-- **(7.31)** (Miao, pp. 217–218): the conditional expectation `E_t` of the derivative of the
Lagrangian in `x_t`, divided by `βᵗ` (`eq_7_29_x`), is `∂H_t/∂x − μ_t`; so the first-order
condition `E_t[∂L/∂x_t] = 0` is (7.31) `∂H_t/∂x = μ_t` (`μ_t` is `ℱ_t`-measurable). -/
theorem eq_7_31 [IsFiniteMeasure P] {μ x a : ℕ → Ω → ℝ} {t : ℕ}
    (hum : StronglyMeasurable[ℱ t] fun ω => deriv (fun c => M.u t c (z t ω) (a t ω)) (x t ω))
    (hui : Integrable (fun ω => deriv (fun c => M.u t c (z t ω) (a t ω)) (x t ω)) P)
    (hφi : Integrable (fun ω => μ (t + 1) ω *
      deriv (fun c => M.φ c (a t ω) (z t ω) (z (t + 1) ω)) (x t ω)) P)
    (hμm : StronglyMeasurable[ℱ t] (μ t)) (hμi : Integrable (μ t) P) :
    P[fun ω => deriv (fun c => M.u t c (z t ω) (a t ω)) (x t ω) + M.β * (μ (t + 1) ω *
      deriv (fun c => M.φ c (a t ω) (z t ω) (z (t + 1) ω)) (x t ω)) - μ t ω | ℱ t] =ᵐ[P]
      fun ω => M.Hx P ℱ z μ x a t ω - μ t ω := by
  have hsub := condExp_sub (hui.add (hφi.const_mul M.β)) hμi (ℱ t)
  have hadd := condExp_add hui (hφi.const_mul M.β) (ℱ t)
  have hself := condExp_of_stronglyMeasurable (ℱ.le t) hum hui
  have hμs := condExp_of_stronglyMeasurable (ℱ.le t) hμm hμi
  have hsmul := condExp_smul (m := ℱ t) (μ := P) M.β fun ω => μ (t + 1) ω *
      deriv (fun c => M.φ c (a t ω) (z t ω) (z (t + 1) ω)) (x t ω)
  have e : (fun ω => M.β * (μ (t + 1) ω *
      deriv (fun c => M.φ c (a t ω) (z t ω) (z (t + 1) ω)) (x t ω))) =
      M.β • fun ω => μ (t + 1) ω *
        deriv (fun c => M.φ c (a t ω) (z t ω) (z (t + 1) ω)) (x t ω) := by
    funext ω; simp
  have e2 : (fun ω => deriv (fun c => M.u t c (z t ω) (a t ω)) (x t ω) + M.β * (μ (t + 1) ω *
      deriv (fun c => M.φ c (a t ω) (z t ω) (z (t + 1) ω)) (x t ω)) - μ t ω) =
      (fun ω => deriv (fun c => M.u t c (z t ω) (a t ω)) (x t ω)) + (fun ω => M.β *
        (μ (t + 1) ω * deriv (fun c => M.φ c (a t ω) (z t ω) (z (t + 1) ω)) (x t ω))) - μ t := by
    funext ω; simp
  rw [e2]
  filter_upwards [hsub, hadd, hsmul] with ω h0 h1 h2
  refine h0.trans ?_
  rw [Pi.sub_apply, h1, Pi.add_apply, e, h2, hself, hμs]
  simp [Hx]

/-! ### The link with dynamic programming (p. 218) -/

/-- The right side of the first-order condition of the Bellman equation (7.19) (Miao, p. 218):
`u_a(x, z, a) + β ∫ V_x(φ(x, a, z, z′), z′) φ_a(x, a, z, z′) Q(z, dz′)`, for the date-`t` reward
(the book's `u_t = u`). -/
noncomputable def eu_focInf (M : OCModel ℝ ℝ Z) (V : ℝ → Z → ℝ) (t : ℕ) (x : ℝ) (z : Z) (a : ℝ) :
    ℝ :=
  deriv (fun b => M.u t x z b) a + M.β * ∫ z', deriv (fun y => V y z') (M.φ x a z z') *
    deriv (fun b => M.φ x b z z') a ∂M.Q z

/-- The right side of the envelope condition (Miao, p. 218):
`u_x(x, z, a) + β ∫ V_x(φ(x, a, z, z′), z′) φ_x(x, a, z, z′) Q(z, dz′)`. -/
noncomputable def eu_envInf (M : OCModel ℝ ℝ Z) (V : ℝ → Z → ℝ) (t : ℕ) (x : ℝ) (z : Z) (a : ℝ) :
    ℝ :=
  deriv (fun y => M.u t y z a) x + M.β * ∫ z', deriv (fun y => V y z') (M.φ x a z z') *
    deriv (fun y => M.φ y a z z') x ∂M.Q z

/-- **p. 218, first-order condition**: with `μ_{t+1} = V_x(x_{t+1}, z_{t+1})` and the Markov
property, along the path `∂H_t/∂a` equals the right side of the first-order condition. -/
theorem link_7_30 (V : ℝ → Z → ℝ) (hM : IsMarkovCond P ℱ z M.Q) {μ xs as : ℕ → Ω → ℝ} {t : ℕ}
    (hxs : Measurable[ℱ t] (xs t)) (has : Measurable[ℱ t] (as t))
    (hstate : ∀ ω, xs (t + 1) ω = M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω))
    (hμ : ∀ ω, μ (t + 1) ω = deriv (fun y => V y (z (t + 1) ω)) (xs (t + 1) ω))
    (hG : Measurable fun p : ℝ × ℝ × Z × Z => deriv (fun y => V y p.2.2.2)
      (M.φ p.1 p.2.1 p.2.2.1 p.2.2.2) * deriv (fun b => M.φ p.1 b p.2.2.1 p.2.2.2) p.2.1)
    (hI : Integrable (fun ω => μ (t + 1) ω *
      deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)) P) :
    M.Ha P ℱ z μ xs as t =ᵐ[P] fun ω => M.eu_focInf V t (xs t ω) (z t ω) (as t ω) := by
  have heq : (fun ω => μ (t + 1) ω * deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω))
      (as t ω)) = fun ω => deriv (fun y => V y (z (t + 1) ω))
        (M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω)) *
        deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω) := by
    funext ω; rw [hμ, hstate]
  rw [heq] at hI
  have hc := hM t _ hG (xs t) (as t) hxs has hI
  filter_upwards [hc] with ω hω
  simp only [Ha, eu_focInf]
  rw [heq, hω]

/-- **p. 218, envelope condition**: with `μ_{t+1} = V_x(x_{t+1}, z_{t+1})`, along the path
`∂H_t/∂x` equals the right side of the envelope condition. -/
theorem link_7_31 (V : ℝ → Z → ℝ) (hM : IsMarkovCond P ℱ z M.Q) {μ xs as : ℕ → Ω → ℝ} {t : ℕ}
    (hxs : Measurable[ℱ t] (xs t)) (has : Measurable[ℱ t] (as t))
    (hstate : ∀ ω, xs (t + 1) ω = M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω))
    (hμ : ∀ ω, μ (t + 1) ω = deriv (fun y => V y (z (t + 1) ω)) (xs (t + 1) ω))
    (hG : Measurable fun p : ℝ × ℝ × Z × Z => deriv (fun y => V y p.2.2.2)
      (M.φ p.1 p.2.1 p.2.2.1 p.2.2.2) * deriv (fun y => M.φ y p.2.1 p.2.2.1 p.2.2.2) p.1)
    (hI : Integrable (fun ω => μ (t + 1) ω *
      deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω)) P) :
    M.Hx P ℱ z μ xs as t =ᵐ[P] fun ω => M.eu_envInf V t (xs t ω) (z t ω) (as t ω) := by
  have heq : (fun ω => μ (t + 1) ω * deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω))
      (xs t ω)) = fun ω => deriv (fun y => V y (z (t + 1) ω))
        (M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω)) *
        deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω) := by
    funext ω; rw [hμ, hstate]
  rw [heq] at hI
  have hc := hM t _ hG (xs t) (as t) hxs has hI
  filter_upwards [hc] with ω hω
  simp only [Hx, eu_envInf]
  rw [heq, hω]

/-- **p. 218: the DP first-order condition is (7.30).** With `μ_t = V_x(x_t, z_t)`, (7.30) holds
at `t` iff the first-order condition of (7.19) holds along the path at `t`, almost surely. -/
theorem link_7_30_iff (V : ℝ → Z → ℝ) (hM : IsMarkovCond P ℱ z M.Q) {xs as : ℕ → Ω → ℝ} {t : ℕ}
    (hxs : Measurable[ℱ t] (xs t)) (has : Measurable[ℱ t] (as t))
    (hstate : ∀ ω, xs (t + 1) ω = M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω))
    (hG : Measurable fun p : ℝ × ℝ × Z × Z => deriv (fun y => V y p.2.2.2)
      (M.φ p.1 p.2.1 p.2.2.1 p.2.2.2) * deriv (fun b => M.φ p.1 b p.2.2.1 p.2.2.2) p.2.1)
    (hI : Integrable (fun ω => deriv (fun y => V y (z (t + 1) ω)) (xs (t + 1) ω) *
      deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)) P) :
    M.Ha P ℱ z (fun s ω => deriv (fun y => V y (z s ω)) (xs s ω)) xs as t =ᵐ[P] 0 ↔
      (fun ω => M.eu_focInf V t (xs t ω) (z t ω) (as t ω)) =ᵐ[P] 0 := by
  have h := link_7_30 (μ := fun s ω => deriv (fun y => V y (z s ω)) (xs s ω)) V hM hxs has
    hstate (fun _ => rfl) hG hI
  exact ⟨fun h0 => h.symm.trans h0, fun h0 => h.trans h0⟩

/-- **p. 218: the envelope condition is (7.31).** With `μ_t = V_x(x_t, z_t)`, (7.31) holds at `t`
iff the envelope condition `V_x(x_t, z_t) = u_x + β ∫ V_x φ_x dQ` holds along the path at `t`. -/
theorem link_7_31_iff (V : ℝ → Z → ℝ) (hM : IsMarkovCond P ℱ z M.Q) {xs as : ℕ → Ω → ℝ} {t : ℕ}
    (hxs : Measurable[ℱ t] (xs t)) (has : Measurable[ℱ t] (as t))
    (hstate : ∀ ω, xs (t + 1) ω = M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω))
    (hG : Measurable fun p : ℝ × ℝ × Z × Z => deriv (fun y => V y p.2.2.2)
      (M.φ p.1 p.2.1 p.2.2.1 p.2.2.2) * deriv (fun y => M.φ y p.2.1 p.2.2.1 p.2.2.2) p.1)
    (hI : Integrable (fun ω => deriv (fun y => V y (z (t + 1) ω)) (xs (t + 1) ω) *
      deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω)) P) :
    ((fun ω => deriv (fun y => V y (z t ω)) (xs t ω)) =ᵐ[P]
      M.Hx P ℱ z (fun s ω => deriv (fun y => V y (z s ω)) (xs s ω)) xs as t) ↔
      (fun ω => deriv (fun y => V y (z t ω)) (xs t ω)) =ᵐ[P]
        fun ω => M.eu_envInf V t (xs t ω) (z t ω) (as t ω) := by
  have h := link_7_31 (μ := fun s ω => deriv (fun y => V y (z s ω)) (xs s ω)) V hM hxs has
    hstate (fun _ => rfl) hG hI
  exact ⟨fun h0 => h0.trans h, fun h0 => h0.trans h.symm⟩

/-! ### Sufficiency: Theorem 7.4.1 -/

/-- The partial sum `S_T = Σ_{t ≤ T} βᵗ E u_t(x_t, z_t, a_t)` of the objective of the plan `a`
from `x₀` (the expectation inside the sum, as in the proof of Theorem 7.4.1). -/
noncomputable def eu_partialJ (M : OCModel ℝ ℝ Z) (P : Measure Ω) (z : ℕ → Ω → Z) (a : ℕ → Ω → ℝ)
    (x₀ : ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (T + 1), M.β ^ t * ∫ ω, M.u t (M.path z a x₀ t ω) (z t ω) (a t ω) ∂P

/-- A **feasible plan** of the infinite-horizon problem: adapted, with states in `X` and
`a_t ∈ Γ(x_t, z_t)` for all `t`. -/
def eu_IsPlanInf (M : OCModel ℝ ℝ Z) (ℱ : Filtration ℕ m0) (z : ℕ → Ω → Z) (x₀ : ℝ)
    (a : ℕ → Ω → ℝ) : Prop :=
  (∀ t, Measurable[ℱ t] (a t)) ∧
    ∀ t ω, M.path z a x₀ t ω ∈ M.X ∧ a t ω ∈ M.Γ (M.path z a x₀ t ω) (z t ω)

/-- **The core inequality of Theorem 7.4.1** (Miao, pp. 219–220). Let the candidate `as` with
states `xs` and multipliers `μ` satisfy (7.30)–(7.31); let the pathwise Hamiltonian
`u_t(x, z_t, a) + β μ_{t+1} φ(x, a, z_t, z_{t+1})` be concave on `X × A`, and `u_t`, `φ` be
differentiable at `(xs_t, as_t)`. Then every feasible plan `a` with the integrability `eu_MPIntInf`
satisfies `S_T(a) ≤ S_T(as) + β^{T+1} E[μ_{T+1}(xs_{T+1} − x_{T+1})]` for every `T`. -/
theorem eu_mp_core [IsProbabilityMeasure P] (hz : ∀ t, Measurable[ℱ t] (z t))
    (hφm : Measurable fun p : ℝ × ℝ × Z × Z => M.φ p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hβ : 0 ≤ M.β) (x₀ : ℝ) {μ as a : ℕ → Ω → ℝ}
    (has : ∀ t, Measurable[ℱ t] (as t)) (ha : ∀ t, Measurable[ℱ t] (a t))
    (hsX : ∀ t ω, (M.path z as x₀ t ω, as t ω) ∈ M.X ×ˢ M.A)
    (hcX : ∀ t ω, (M.path z a x₀ t ω, a t ω) ∈ M.X ×ˢ M.A)
    (hmp : eu_MPInf P ℱ z M μ (M.path z as x₀) as)
    (hH : ∀ t ω, ConcaveOn ℝ (M.X ×ˢ M.A) (M.pathHam z μ t ω))
    (hud : ∀ t ω, DifferentiableAt ℝ (fun p : ℝ × ℝ => M.u t p.1 (z t ω) p.2)
      (M.path z as x₀ t ω, as t ω))
    (hφd : ∀ t ω, DifferentiableAt ℝ (fun p : ℝ × ℝ => M.φ p.1 p.2 (z t ω) (z (t + 1) ω))
      (M.path z as x₀ t ω, as t ω))
    (hint : eu_MPIntInf P z M μ (M.path z as x₀) as (M.path z a x₀) a) (T : ℕ) :
    M.eu_partialJ P z a x₀ T ≤ M.eu_partialJ P z as x₀ T + M.β ^ (T + 1) *
      ∫ ω, μ (T + 1) ω * (M.path z as x₀ (T + 1) ω - M.path z a x₀ (T + 1) ω) ∂P := by
  set xs := M.path z as x₀ with hxsdef
  set x := M.path z a x₀ with hxdef
  have hxs : ∀ t, Measurable[ℱ t] (xs t) := M.path_measurable ℱ z hz hφm has x₀
  have hx : ∀ t, Measurable[ℱ t] (x t) := M.path_measurable ℱ z hz hφm ha x₀
  set c : ℕ → ℝ := fun t => ∫ ω, μ t ω * (xs t ω - x t ω) ∂P with hcdef
  have hc0 : c 0 = 0 := by simp [c, xs, x, path]
  have hper : ∀ t, c t - M.β * c (t + 1) ≤
      (∫ ω, M.u t (xs t ω) (z t ω) (as t ω) ∂P) - ∫ ω, M.u t (x t ω) (z t ω) (a t ω) ∂P := by
    intro t
    have hpath : ∀ ω, (xs t ω - x t ω) * deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) +
        M.β * ((xs t ω - x t ω) * (μ (t + 1) ω *
          deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω))) +
        ((as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) +
          M.β * ((as t ω - a t ω) * (μ (t + 1) ω *
            deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)))) ≤
        M.u t (xs t ω) (z t ω) (as t ω) - M.u t (x t ω) (z t ω) (a t ω) +
          M.β * (μ (t + 1) ω * (xs (t + 1) ω - x (t + 1) ω)) := by
      intro ω
      set p : ℝ × ℝ := (xs t ω, as t ω)
      have hdH : DifferentiableAt ℝ (M.pathHam z μ t ω) p :=
        (hud t ω).add ((hφd t ω).const_mul _ |>.const_mul _)
      have hsg := eu_supergradient (hH t ω) (hsX t ω) (hcX t ω) hdH
      have hdx : deriv (fun y => M.pathHam z μ t ω (y, p.2)) p.1 =
          deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) + M.β * (μ (t + 1) ω *
            deriv (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω)) := by
        have h1 : DifferentiableAt ℝ (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) := by
          have hg := hud t ω
          exact hg.comp (xs t ω)
            (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y, as t ω)) (xs t ω))
        have h2 : DifferentiableAt ℝ (fun y => M.φ y (as t ω) (z t ω) (z (t + 1) ω)) (xs t ω) := by
          have hg := hφd t ω
          exact hg.comp (xs t ω)
            (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y, as t ω)) (xs t ω))
        exact (h1.hasDerivAt.add ((h2.hasDerivAt.const_mul (μ (t + 1) ω)).const_mul M.β)).deriv
      have hda : deriv (fun b => M.pathHam z μ t ω (p.1, b)) p.2 =
          deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) + M.β * (μ (t + 1) ω *
            deriv (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω)) := by
        have h1 : DifferentiableAt ℝ (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) := by
          have hg := hud t ω
          exact hg.comp (as t ω)
            (by fun_prop : DifferentiableAt ℝ (fun b : ℝ => (xs t ω, b)) (as t ω))
        have h2 : DifferentiableAt ℝ (fun b => M.φ (xs t ω) b (z t ω) (z (t + 1) ω)) (as t ω) := by
          have hg := hφd t ω
          exact hg.comp (as t ω)
            (by fun_prop : DifferentiableAt ℝ (fun b : ℝ => (xs t ω, b)) (as t ω))
        exact (h1.hasDerivAt.add ((h2.hasDerivAt.const_mul (μ (t + 1) ω)).const_mul M.β)).deriv
      rw [hdx, hda] at hsg
      have e1 : xs (t + 1) ω = M.φ (xs t ω) (as t ω) (z t ω) (z (t + 1) ω) := rfl
      have e2 : x (t + 1) ω = M.φ (x t ω) (a t ω) (z t ω) (z (t + 1) ω) := rfl
      simp only [pathHam] at hsg
      rw [e1, e2]
      nlinarith [hsg]
    have hΔx : StronglyMeasurable[ℱ t] fun ω => xs t ω - x t ω :=
      ((hxs t).sub (hx t)).stronglyMeasurable
    have hΔa : StronglyMeasurable[ℱ t] fun ω => as t ω - a t ω :=
      ((has t).sub (ha t)).stronglyMeasurable
    obtain ⟨iX, eX⟩ := oc_integral_mul_condExp hΔx (hint.φxΔ t) (hint.φx t)
    obtain ⟨iA, eA⟩ := oc_integral_mul_condExp hΔa (hint.φaΔ t) (hint.φa t)
    have hmono := integral_mono (((hint.ux t).add ((hint.φxΔ t).const_mul M.β)).add
      ((hint.ua t).add ((hint.φaΔ t).const_mul M.β)))
      (((hint.u_s t).sub (hint.u_c t)).add ((hint.μΔ t).const_mul M.β)) hpath
    rw [integral_add' ((hint.ux t).add ((hint.φxΔ t).const_mul M.β))
        ((hint.ua t).add ((hint.φaΔ t).const_mul M.β)),
      integral_add' (hint.ux t) ((hint.φxΔ t).const_mul M.β),
      integral_add' (hint.ua t) ((hint.φaΔ t).const_mul M.β),
      integral_add' ((hint.u_s t).sub (hint.u_c t)) ((hint.μΔ t).const_mul M.β),
      integral_sub' (hint.u_s t) (hint.u_c t), integral_const_mul, integral_const_mul,
      integral_const_mul, eX, eA] at hmono
    have hAzero : (∫ ω, (as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) ∂P)
        + M.β * ∫ ω, (as t ω - a t ω) * (P[fun ω' => μ (t + 1) ω' *
          deriv (fun b => M.φ (xs t ω') b (z t ω') (z (t + 1) ω')) (as t ω') | ℱ t]) ω ∂P = 0 := by
      rw [← integral_const_mul, ← integral_add (hint.ua t) (iA.const_mul M.β)]
      have : (fun ω => (as t ω - a t ω) * deriv (fun b => M.u t (xs t ω) (z t ω) b) (as t ω) +
          M.β * ((as t ω - a t ω) * (P[fun ω' => μ (t + 1) ω' *
            deriv (fun b => M.φ (xs t ω') b (z t ω') (z (t + 1) ω')) (as t ω') | ℱ t]) ω)) =ᵐ[P]
          fun _ => (0 : ℝ) := by
        filter_upwards [hmp.foc_a t] with ω hω
        simp only [Ha, Pi.zero_apply] at hω
        linear_combination (as t ω - a t ω) * hω
      rw [integral_congr_ae this, integral_zero]
    have hXc : (∫ ω, (xs t ω - x t ω) * deriv (fun y => M.u t y (z t ω) (as t ω)) (xs t ω) ∂P)
        + M.β * ∫ ω, (xs t ω - x t ω) * (P[fun ω' => μ (t + 1) ω' *
          deriv (fun y => M.φ y (as t ω') (z t ω') (z (t + 1) ω')) (xs t ω') | ℱ t]) ω ∂P =
          c t := by
      rw [← integral_const_mul, ← integral_add (hint.ux t) (iX.const_mul M.β)]
      rcases Nat.eq_zero_or_pos t with rfl | ht1
      · rw [hc0]
        have : ∀ ω, xs 0 ω - x 0 ω = 0 := fun ω => by simp [xs, x, path]
        simp [this]
      · refine integral_congr_ae ?_
        filter_upwards [hmp.foc_x t ht1] with ω hω
        simp only [Hx] at hω
        rw [hω]
        ring
    linarith [hmono]
  -- telescoping: `Σ_{t ≤ T} βᵗ (c_t − β c_{t+1}) = c_0 − β^{T+1} c_{T+1}`
  have htel : ∑ t ∈ Finset.range (T + 1), M.β ^ t * (c t - M.β * c (t + 1)) =
      c 0 - M.β ^ (T + 1) * c (T + 1) := by
    have h1 : ∑ t ∈ Finset.range (T + 1), M.β ^ t * (c t - M.β * c (t + 1)) =
        ∑ t ∈ Finset.range (T + 1), (M.β ^ t * c t - M.β ^ (t + 1) * c (t + 1)) :=
      Finset.sum_congr rfl fun t _ => by ring
    rw [h1, Finset.sum_range_sub' (fun t => M.β ^ t * c t) (T + 1)]
    simp
  have hsum : (∑ t ∈ Finset.range (T + 1), M.β ^ t * (c t - M.β * c (t + 1))) ≤
      ∑ t ∈ Finset.range (T + 1), M.β ^ t * ((∫ ω, M.u t (xs t ω) (z t ω) (as t ω) ∂P) -
        ∫ ω, M.u t (x t ω) (z t ω) (a t ω) ∂P) :=
    Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hper t) (pow_nonneg hβ t)
  rw [htel, hc0] at hsum
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum
  simp only [eu_partialJ]
  change _ ≤ _ + M.β ^ (T + 1) * c (T + 1)
  linarith

/-- **Theorem 7.4.1 (sufficiency of the Maximum Principle and the transversality condition)**
(Miao, p. 219). Let `X ⊆ ℝ₊` and `A ⊆ ℝ` be convex, `Γ ⊆ A`, and Assumptions 5.1.2 (`β ≥ 0` is
used), 6.4.12, 6.4.14, 7.3.3, 7.3.4 hold. Let the candidate `as` with states `xs` (5.14) and
multipliers `μ` satisfy (7.30), (7.31) and the transversality condition (7.32)
`lim_T E[β^T μ_T xs_T] = 0`, with `as_t ∈ int Γ(xs_t, z_t)`, `xs_t ∈ int X` and `μ_{t+1} ≥ 0`.
Then every feasible plan `a` with the integrability `eu_MPIntInf` satisfies
`S_T(a) ≤ S_T(as) + w_T` with `w_T = β^{T+1} E[μ_{T+1} xs_{T+1}] → 0`. -/
theorem theorem_7_4_1 [IsProbabilityMeasure P] (hz : ∀ t, Measurable[ℱ t] (z t))
    (hφm : Measurable fun p : ℝ × ℝ × Z × Z => M.φ p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hXpos : M.X ⊆ Set.Ici 0) (hXc : Convex ℝ M.X) (hAc : Convex ℝ M.A)
    (hΓA : ∀ x z', M.Γ x z' ⊆ M.A) (h512 : 0 < M.β ∧ M.β < 1) (h6412 : M.Assumption6412)
    (h6414 : M.Assumption6414) (h733 : M.eu_Assumption733) (h734 : M.eu_Assumption734) (x₀ : ℝ)
    {μ as a : ℕ → Ω → ℝ} (has : M.eu_IsPlanInf ℱ z x₀ as) (ha : M.eu_IsPlanInf ℱ z x₀ a)
    (hmp : eu_MPInf P ℱ z M μ (M.path z as x₀) as)
    (htvc : Tendsto (fun T => M.β ^ T * ∫ ω, μ T ω * M.path z as x₀ T ω ∂P) atTop (𝓝 0))
    (hμxi : ∀ T, Integrable (fun ω => μ T ω * M.path z as x₀ T ω) P)
    (hint_a : ∀ t ω, as t ω ∈ interior (M.Γ (M.path z as x₀ t ω) (z t ω)))
    (hint_x : ∀ t ω, M.path z as x₀ t ω ∈ interior M.X) (hμ : ∀ t ω, 0 ≤ μ (t + 1) ω)
    (hint : eu_MPIntInf P z M μ (M.path z as x₀) as (M.path z a x₀) a) :
    ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 0) ∧
      ∀ T, M.eu_partialJ P z a x₀ T ≤ M.eu_partialJ P z as x₀ T + w T := by
  have hβ : 0 ≤ M.β := h512.1.le
  have hmemA : ∀ t ω, (M.path z as x₀ t ω, as t ω) ∈ interior (M.X ×ˢ M.A) := fun t ω => by
    rw [interior_prod_eq]
    exact ⟨hint_x t ω, interior_mono (hΓA _ _) (hint_a t ω)⟩
  have hsX : ∀ t ω, (M.path z as x₀ t ω, as t ω) ∈ M.X ×ˢ M.A := fun t ω =>
    interior_subset (hmemA t ω)
  have hcX : ∀ t ω, (M.path z a x₀ t ω, a t ω) ∈ M.X ×ˢ M.A := fun t ω =>
    ⟨(ha.2 t ω).1, hΓA _ _ (ha.2 t ω).2⟩
  have hud : ∀ t ω, DifferentiableAt ℝ (fun p : ℝ × ℝ => M.u t p.1 (z t ω) p.2)
      (M.path z as x₀ t ω, as t ω) := fun t ω =>
    ((h734 t (z t ω)).differentiableOn one_ne_zero).differentiableAt
      (isOpen_interior.mem_nhds (hmemA t ω))
  have hφd : ∀ t ω, DifferentiableAt ℝ (fun p : ℝ × ℝ => M.φ p.1 p.2 (z t ω) (z (t + 1) ω))
      (M.path z as x₀ t ω, as t ω) := fun t ω =>
    (h6414 (z t ω) (z (t + 1) ω)).differentiableAt (isOpen_interior.mem_nhds (hmemA t ω))
  have hH : ∀ t ω, ConcaveOn ℝ (M.X ×ˢ M.A) (M.pathHam z μ t ω) := fun t ω => by
    have h := (eu_concaveOn_of_733 h733 hXc hAc t (z t ω)).add
      (((eu_concaveOn_of_6412 h6412 hXc hAc (z t ω) (z (t + 1) ω)).smul (hμ t ω)).smul hβ)
    refine h.congr fun p _ => ?_
    simp only [pathHam, Pi.add_apply, smul_eq_mul]
  refine ⟨fun T => M.β ^ (T + 1) * ∫ ω, μ (T + 1) ω * M.path z as x₀ (T + 1) ω ∂P,
    htvc.comp (tendsto_add_atTop_nat 1), fun T => ?_⟩
  have hcore := eu_mp_core hz hφm hβ x₀ has.1 ha.1 hsX hcX hmp hH hud hφd hint T
  have hle : ∫ ω, μ (T + 1) ω * (M.path z as x₀ (T + 1) ω - M.path z a x₀ (T + 1) ω) ∂P ≤
      ∫ ω, μ (T + 1) ω * M.path z as x₀ (T + 1) ω ∂P := by
    refine integral_mono (hint.μΔ T) (hμxi (T + 1)) fun ω => ?_
    have hx0 : 0 ≤ M.path z a x₀ (T + 1) ω := hXpos (ha.2 (T + 1) ω).1
    have := mul_nonneg (hμ T ω) hx0
    simp only
    nlinarith
  have := mul_le_mul_of_nonneg_left hle (pow_nonneg hβ (T + 1))
  linarith

/-- **Theorem 7.4.1, the limit step** (Miao, p. 220): under the hypotheses of `theorem_7_4_1`,
if the partial sums of the candidate and of the competing plan converge in `[−∞, +∞]` (the
competing plan may have `J = −∞`), the limit of the competing plan is at most that of the
candidate. -/
theorem theorem_7_4_1_limit [IsProbabilityMeasure P] (hz : ∀ t, Measurable[ℱ t] (z t))
    (hφm : Measurable fun p : ℝ × ℝ × Z × Z => M.φ p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hXpos : M.X ⊆ Set.Ici 0) (hXc : Convex ℝ M.X) (hAc : Convex ℝ M.A)
    (hΓA : ∀ x z', M.Γ x z' ⊆ M.A) (h512 : 0 < M.β ∧ M.β < 1) (h6412 : M.Assumption6412)
    (h6414 : M.Assumption6414) (h733 : M.eu_Assumption733) (h734 : M.eu_Assumption734) (x₀ : ℝ)
    {μ as a : ℕ → Ω → ℝ} (has : M.eu_IsPlanInf ℱ z x₀ as) (ha : M.eu_IsPlanInf ℱ z x₀ a)
    (hmp : eu_MPInf P ℱ z M μ (M.path z as x₀) as)
    (htvc : Tendsto (fun T => M.β ^ T * ∫ ω, μ T ω * M.path z as x₀ T ω ∂P) atTop (𝓝 0))
    (hμxi : ∀ T, Integrable (fun ω => μ T ω * M.path z as x₀ T ω) P)
    (hint_a : ∀ t ω, as t ω ∈ interior (M.Γ (M.path z as x₀ t ω) (z t ω)))
    (hint_x : ∀ t ω, M.path z as x₀ t ω ∈ interior M.X) (hμ : ∀ t ω, 0 ≤ μ (t + 1) ω)
    (hint : eu_MPIntInf P z M μ (M.path z as x₀) as (M.path z a x₀) a) {J J' : EReal}
    (hJ : Tendsto (fun T => (M.eu_partialJ P z as x₀ T : EReal)) atTop (𝓝 J))
    (hJ' : Tendsto (fun T => (M.eu_partialJ P z a x₀ T : EReal)) atTop (𝓝 J')) : J' ≤ J := by
  obtain ⟨w, hw, hle⟩ := theorem_7_4_1 hz hφm hXpos hXc hAc hΓA h512 h6412 h6414 h733 h734 x₀
    has ha hmp htvc hμxi hint_a hint_x hμ hint
  exact eu_le_of_le_add_tendsto_zero hJ hJ' hw hle

/-- **Theorem 7.4.1, optimality without convergence of the competing plan**: under the
hypotheses of `theorem_7_4_1`, if `S_T(as) → J*`, then for every `ε > 0` the partial sums of
every feasible (integrable) plan are eventually at most `J* + ε`. -/
theorem theorem_7_4_1_eventually [IsProbabilityMeasure P] (hz : ∀ t, Measurable[ℱ t] (z t))
    (hφm : Measurable fun p : ℝ × ℝ × Z × Z => M.φ p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hXpos : M.X ⊆ Set.Ici 0) (hXc : Convex ℝ M.X) (hAc : Convex ℝ M.A)
    (hΓA : ∀ x z', M.Γ x z' ⊆ M.A) (h512 : 0 < M.β ∧ M.β < 1) (h6412 : M.Assumption6412)
    (h6414 : M.Assumption6414) (h733 : M.eu_Assumption733) (h734 : M.eu_Assumption734) (x₀ : ℝ)
    {μ as a : ℕ → Ω → ℝ} (has : M.eu_IsPlanInf ℱ z x₀ as) (ha : M.eu_IsPlanInf ℱ z x₀ a)
    (hmp : eu_MPInf P ℱ z M μ (M.path z as x₀) as)
    (htvc : Tendsto (fun T => M.β ^ T * ∫ ω, μ T ω * M.path z as x₀ T ω ∂P) atTop (𝓝 0))
    (hμxi : ∀ T, Integrable (fun ω => μ T ω * M.path z as x₀ T ω) P)
    (hint_a : ∀ t ω, as t ω ∈ interior (M.Γ (M.path z as x₀ t ω) (z t ω)))
    (hint_x : ∀ t ω, M.path z as x₀ t ω ∈ interior M.X) (hμ : ∀ t ω, 0 ≤ μ (t + 1) ω)
    (hint : eu_MPIntInf P z M μ (M.path z as x₀) as (M.path z a x₀) a) {J : ℝ}
    (hJ : Tendsto (M.eu_partialJ P z as x₀) atTop (𝓝 J)) :
    ∀ ε > 0, ∀ᶠ T in atTop, M.eu_partialJ P z a x₀ T ≤ J + ε := by
  obtain ⟨w, hw, hle⟩ := theorem_7_4_1 hz hφm hXpos hXc hAc hΓA h512 h6412 h6414 h733 h734 x₀
    has ha hmp htvc hμxi hint_a hint_x hμ hint
  exact eu_limsup_le hJ hw hle

end OCModel

end Miao.InfiniteHorizonDP
