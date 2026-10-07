/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.Valuation

/-!
# Continuous-time Markov decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.2.2–§10.2.4 (pp. 334–339).

A continuous-time MDP `C = (Γ, δ, r, Q)` has a nonempty feasible correspondence `Γ`, a discount
rate `δ > 0`, a flow reward `r` and an intensity kernel `Q` on the feasible state-action pairs.

* (10.49): the `σ`-value function `v_σ = ∫₀^∞ e^{−δt}P^σ_t r_σ dt` equals `(δI − Q_σ)⁻¹r_σ`.
* (10.51): the policy operators `T_σ v = r_σ + (Q_σ + (1 − δ)I)v` form an order stable ADP.
* **Exercise 10.2.2**: `σ` is `v`-greedy in the sense of (10.50) iff it is `v`-greedy for the ADP.
* (10.53): the Bellman operator of the ADP.
* **Theorem 10.2.4**: `v*` is the unique solution of the HJB equation (10.52), Bellman's
  principle of optimality holds, an optimal policy exists, and continuous-time HPI
  (Algorithm 10.2) stops, `σₖ₊₁ = σₖ`, at an optimal policy after finitely many steps.
* §10.2.4 (job search): **Exercise 10.2.3** (the jump probabilities `Π` are a stochastic kernel),
  `Q_σ = λ(Π_σ − I)` is an intensity matrix, and Theorem 10.2.4 applies.
-/

open Finset Matrix Function Set

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- A continuous-time MDP `C = (Γ, δ, r, Q)` (§10.2.2.1, p. 334). The reward and the kernel are
given on all of `X × A`; only their values on `G = {(x, a) : a ∈ Γ(x)}` matter. -/
structure CTMDP (X A : Type*) [Fintype X] where
  /-- the feasible correspondence -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the discount rate -/
  δ : ℝ
  δ_pos : 0 < δ
  /-- the flow reward -/
  r : X → A → ℝ
  /-- the intensity kernel -/
  Q : X → A → X → ℝ
  Q_nonneg : ∀ x, ∀ a ∈ Γ x, ∀ x', x ≠ x' → 0 ≤ Q x a x'
  Q_sum : ∀ x, ∀ a ∈ Γ x, ∑ x', Q x a x' = 0

namespace CTMDP

variable {X A : Type*} [Fintype X] (C : CTMDP X A)

/-- The feasible policies `Σ = {σ ∈ A^X : σ(x) ∈ Γ(x)}` (10.47). -/
def Policy : Type _ := {σ : X → A // ∀ x, σ x ∈ C.Γ x}

/-- `Σ` is nonempty. -/
theorem nonempty_policy : Nonempty C.Policy :=
  ⟨⟨fun x => (C.Γ_nonempty x).choose, fun x => (C.Γ_nonempty x).choose_spec⟩⟩

/-- `Q_σ(x, x') = Q(x, σ(x), x')`. -/
def Qσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => C.Q x (σ x) x'

/-- `r_σ(x) = r(x, σ(x))`. -/
def rσ (σ : X → A) : X → ℝ := fun x => C.r x (σ x)

/-- `Q_σ` is an intensity matrix for every feasible `σ`. -/
theorem isIntensity_Qσ (σ : C.Policy) : IsIntensity (C.Qσ σ.1) :=
  ⟨fun x x' h => C.Q_nonneg x _ (σ.2 x) x' h, fun x => C.Q_sum x _ (σ.2 x)⟩

/-- The objective in (10.50): `r(x, a) + ∑_{x'} v(x')Q(x, a, x')`. -/
def flow (v : X → ℝ) (x : X) (a : A) : ℝ := C.r x a + ∑ x', v x' * C.Q x a x'

/-- `σ` is `v`-greedy for `C` (10.50): `σ(x)` maximises `r(x, a) + ∑_{x'} v(x')Q(x, a, x')` over
`Γ(x)` for every `x`. -/
def IsGreedy (v : X → ℝ) (σ : C.Policy) : Prop :=
  ∀ x, ∀ a ∈ C.Γ x, C.flow v x a ≤ C.flow v x (σ.1 x)

/-- A `v`-greedy policy exists. -/
theorem exists_greedy (v : X → ℝ) : ∃ σ : C.Policy, C.IsGreedy v σ := by
  choose f hf hmax using fun x => Finset.exists_max_image (C.Γ x) (C.flow v x) (C.Γ_nonempty x)
  exact ⟨⟨f, hf⟩, fun x a ha => hmax x a ha⟩

/-- A `v`-min-greedy policy exists. -/
theorem exists_minGreedy (v : X → ℝ) :
    ∃ σ : C.Policy, ∀ x, ∀ a ∈ C.Γ x, C.flow v x (σ.1 x) ≤ C.flow v x a := by
  choose f hf hmin using fun x => Finset.exists_min_image (C.Γ x) (C.flow v x) (C.Γ_nonempty x)
  exact ⟨⟨f, hf⟩, fun x a ha => hmin x a ha⟩

variable [DecidableEq X]

/-- The `σ`-value function (10.48), in semigroup form: `v_σ = ∫₀^∞ e^{t(Q_σ − δI)}r_σ dt`. -/
noncomputable def vσ (σ : X → A) : X → ℝ := lifetimeValue (C.Qσ σ - C.δ • 1) (C.rσ σ)

/-- (10.48): `v_σ = ∫₀^∞ e^{−δt}P^σ_t r_σ dt` with `P^σ_t = e^{tQ_σ}`. -/
theorem vσ_eq_integral (σ : X → A) :
    C.vσ σ = ∫ t in Ioi (0 : ℝ), Real.exp (-(t * C.δ)) •
      (NormedSpace.exp (t • C.Qσ σ) *ᵥ C.rσ σ) := by
  simp only [vσ, lifetimeValue, exp_smul_sub_smul_one, Matrix.smul_mulVec]

/-- (10.49) (p. 335): `v_σ = (δI − Q_σ)⁻¹r_σ`. -/
theorem vσ_eq [Nonempty X] (σ : C.Policy) :
    C.vσ σ.1 = (C.δ • (1 : Matrix X X ℝ) - C.Qσ σ.1)⁻¹ *ᵥ C.rσ σ.1 :=
  (constant_discounting (C.isIntensity_Qσ σ) C.δ_pos (C.rσ σ.1)).2.2.2.1

/-- The policy operator `T_σ v = r_σ + (Q_σ + (1 − δ)I)v` (10.51). -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := C.rσ σ + (C.Qσ σ + (1 - C.δ) • 1) *ᵥ v

theorem Tσ_apply (σ : X → A) (v : X → ℝ) (x : X) :
    C.Tσ σ v x = C.flow v x (σ x) + (1 - C.δ) * v x := by
  simp only [Tσ, flow, rσ, Qσ, Pi.add_apply, Matrix.add_mulVec, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [mul_comm (v _)]
  ring

/-- Each `T_σ` is order stable with fixed point `v_σ` (§10.2.2.5, via Proposition 10.2.3). -/
theorem orderStable_Tσ [Nonempty X] (σ : C.Policy) :
    OrderStable (C.Tσ σ.1) ∧ IsFixedPt (C.Tσ σ.1) (C.vσ σ.1) :=
  (constant_discounting (C.isIntensity_Qσ σ) C.δ_pos (C.rσ σ.1)).2.2.2.2

/-- The ADP `A = (ℝ^X, {T_σ})` of §10.2.2.5. -/
noncomputable def toADP : ADP (X → ℝ) C.Policy where
  T σ := C.Tσ σ.1
  exists_greedy v := by
    obtain ⟨σ, hσ⟩ := C.exists_greedy v
    refine ⟨σ, fun τ x => ?_⟩
    change C.Tσ τ.1 v x ≤ C.Tσ σ.1 v x
    rw [C.Tσ_apply, C.Tσ_apply]
    linarith [hσ x _ (τ.2 x)]
  exists_minGreedy v := by
    obtain ⟨σ, hσ⟩ := C.exists_minGreedy v
    refine ⟨σ, fun τ x => ?_⟩
    change C.Tσ σ.1 v x ≤ C.Tσ τ.1 v x
    rw [C.Tσ_apply, C.Tσ_apply]
    linarith [hσ x _ (τ.2 x)]

/-- `A` is order stable (§10.2.2.5). -/
theorem isOrderStable_toADP [Nonempty X] : C.toADP.IsOrderStable := fun σ =>
  (C.orderStable_Tσ σ).1

/-- The `σ`-value functions of `C` and of `A` agree. -/
theorem toADP_vσ [Nonempty X] (hw : C.toADP.WellPosed) (σ : C.Policy) :
    C.toADP.vσ hw σ = C.vσ σ.1 :=
  (ADP.eq_vσ_of_isFixedPt hw (C.orderStable_Tσ σ).2).symm

/-- **Exercise 10.2.2** (p. 336): `σ` is `v`-greedy in the sense of (10.50) iff it is `v`-greedy
for the ADP `A` in the sense of §9.1.2.2. -/
theorem isGreedy_iff (v : X → ℝ) (σ : C.Policy) : C.IsGreedy v σ ↔ C.toADP.IsGreedy v σ := by
  constructor
  · intro hσ τ x
    change C.Tσ τ.1 v x ≤ C.Tσ σ.1 v x
    rw [C.Tσ_apply, C.Tσ_apply]
    linarith [hσ x _ (τ.2 x)]
  · intro hσ x a ha
    let τ : C.Policy := ⟨Function.update σ.1 x a, fun y => by
      rcases eq_or_ne y x with rfl | hy
      · rw [Function.update_self]
        exact ha
      · rw [Function.update_of_ne hy]
        exact σ.2 y⟩
    have h := hσ τ x
    change C.Tσ τ.1 v x ≤ C.Tσ σ.1 v x at h
    rw [C.Tσ_apply, C.Tσ_apply, show τ.1 x = a from Function.update_self x a σ.1] at h
    linarith

/-- The ADP's chosen `v`-greedy policy is `v`-greedy in the sense of (10.50). -/
theorem isGreedy_greedy (v : X → ℝ) : C.IsGreedy v (C.toADP.greedy v) :=
  (C.isGreedy_iff v _).2 (C.toADP.isGreedy_greedy v)

/-- (10.53) (p. 337): `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑_{x'} v(x')Q(x, a, x')} + (1 − δ)v(x)`.
-/
theorem bellman_apply (v : X → ℝ) (x : X) :
    C.toADP.bellman v x = (C.Γ x).sup' (C.Γ_nonempty x) (C.flow v x) + (1 - C.δ) * v x := by
  change C.Tσ (C.toADP.greedy v).1 v x = _
  rw [C.Tσ_apply]
  congr 1
  exact le_antisymm (Finset.le_sup' (C.flow v x) ((C.toADP.greedy v).2 x))
    (Finset.sup'_le _ _ fun a ha => C.isGreedy_greedy v x a ha)

/-- `v` satisfies the Hamilton–Jacobi–Bellman equation (10.52):
`δv(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑_{x'} v(x')Q(x, a, x')}` for all `x`. -/
def IsHJB (v : X → ℝ) : Prop := ∀ x, C.δ * v x = (C.Γ x).sup' (C.Γ_nonempty x) (C.flow v x)

/-- Fixed points of the Bellman operator (10.53) are exactly the solutions of the HJB equation. -/
theorem isFixedPt_bellman_iff (v : X → ℝ) : IsFixedPt C.toADP.bellman v ↔ C.IsHJB v := by
  constructor
  · intro h x
    have hx := congrFun h.eq x
    rw [C.bellman_apply] at hx
    linear_combination -hx
  · intro h
    change C.toADP.bellman v = v
    funext x
    rw [C.bellman_apply]
    linear_combination -(h x)

/-- Continuous-time HPI (Algorithm 10.2): `σₖ₊₁` is a `vₖ`-greedy policy, where
`vₖ = (δI − Q_{σₖ})⁻¹r_{σₖ}`. -/
noncomputable def hpiPolicy (σ₀ : C.Policy) : ℕ → C.Policy
  | 0 => σ₀
  | k + 1 => C.toADP.greedy (C.vσ (hpiPolicy σ₀ k).1)

theorem hpiPolicy_eq [Nonempty X] (hw : C.toADP.WellPosed) (σ₀ : C.Policy) (k : ℕ) :
    C.hpiPolicy σ₀ k = C.toADP.hpiPolicy hw σ₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change C.toADP.greedy (C.vσ (C.hpiPolicy σ₀ k).1) =
      C.toADP.greedy (C.toADP.vσ hw (C.toADP.hpiPolicy hw σ₀ k))
    rw [ih, C.toADP_vσ]

/-- **Theorem 10.2.4** (p. 337): for a continuous-time MDP, (i) the value function
`v* = ⋁_σ v_σ` exists and is the unique solution of the HJB equation (10.52), (ii) `C` obeys
Bellman's principle of optimality, (iii) an optimal policy exists, and continuous-time HPI
(Algorithm 10.2) reaches `σₖ₊₁ = σₖ` with `σₖ` optimal after finitely many steps. -/
theorem optimality [Nonempty X] [Finite A] :
    ∃ vstar : X → ℝ, IsGreatest (Set.range fun σ : C.Policy => C.vσ σ.1) vstar ∧
      (∀ v, C.IsHJB v ↔ v = vstar) ∧
      (∀ σ : C.Policy, C.vσ σ.1 = vstar ↔ C.IsGreedy vstar σ) ∧
      (∃ σ : C.Policy, C.vσ σ.1 = vstar) ∧
      ∀ σ₀ : C.Policy, ∃ k, C.hpiPolicy σ₀ (k + 1) = C.hpiPolicy σ₀ k ∧
        C.vσ (C.hpiPolicy σ₀ k).1 = vstar := by
  have hos := C.isOrderStable_toADP
  have : Finite C.Policy := inferInstanceAs (Finite {σ : X → A // ∀ x, σ x ∈ C.Γ x})
  have := C.nonempty_policy
  obtain ⟨vstar, h1, h2, h3, h4, -⟩ := hos.maxOptimality
  have hv := C.toADP_vσ hos.wellPosed
  have hopt : ∀ σ, C.toADP.IsOptimal hos.wellPosed σ ↔ C.vσ σ.1 = vstar := fun σ => by
    constructor
    · intro ho
      obtain ⟨τ, hτ⟩ := h1.1
      refine le_antisymm ?_ ?_
      · rw [← hv]
        exact h1.2 ⟨σ, rfl⟩
      · rw [← hτ, ← hv]
        exact ho τ
    · intro he τ
      rw [hv σ, he]
      exact h1.2 ⟨τ, rfl⟩
  have hrange : (Set.range fun σ : C.Policy => C.vσ σ.1) = Set.range (C.toADP.vσ hos.wellPosed) :=
    congrArg Set.range (funext fun σ => (hv σ).symm)
  refine ⟨vstar, hrange ▸ h1, fun v => (C.isFixedPt_bellman_iff v).symm.trans (h2 v),
    fun σ => (hopt σ).symm.trans ((h3 σ).trans (C.isGreedy_iff vstar σ).symm), ?_,
    fun σ₀ => ?_⟩
  · obtain ⟨σ, hσ⟩ := h4
    exact ⟨σ, (hopt σ).1 hσ⟩
  · obtain ⟨k, hk, -, ho⟩ := hos.hpi_terminates σ₀
    refine ⟨k + 1, ?_, ?_⟩
    · rw [C.hpiPolicy_eq hos.wellPosed, C.hpiPolicy_eq hos.wellPosed]
      change C.toADP.greedy (C.toADP.hpiValue hos.wellPosed σ₀ (k + 1)) =
        C.toADP.greedy (C.toADP.hpiValue hos.wellPosed σ₀ k)
      rw [hk]
    · rw [C.hpiPolicy_eq hos.wellPosed]
      exact (hopt _).1 ho

end CTMDP

/-! ### §10.2.4: job search -/

variable {W : Type*} [Fintype W]

/-- The jump probabilities `Π(x, a, x')` of §10.2.4 (p. 338), with states `x = (s, w)`,
`s = true` meaning employed and `a = true` meaning accept. -/
def jsJump (P : Matrix W W ℝ) (x : Bool × W) (a : Bool) (x' : Bool × W) : ℝ :=
  if x.1 then (if x'.1 then 0 else P x.2 x'.2) else (if x'.1 = a then P x.2 x'.2 else 0)

/-- **Exercise 10.2.3** (p. 339): `Π ≥ 0` and `∑_{x'} Π(x, a, x') = 1` for all `(x, a)`. -/
theorem jsJump_stochastic {P : Matrix W W ℝ} (hP : IsMarkov P) :
    (∀ x a x', 0 ≤ jsJump P x a x') ∧ ∀ x a, ∑ x', jsJump P x a x' = 1 := by
  refine ⟨fun x a x' => ?_, fun x a => ?_⟩
  · simp only [jsJump]
    split_ifs
    · exact le_rfl
    · exact hP.nonneg _ _
    · exact hP.nonneg _ _
    · exact le_rfl
  · rcases x with ⟨s, w⟩
    simp only [jsJump, Fintype.sum_prod_type, Fintype.sum_bool]
    cases s <;> cases a <;> simp [hP.rowsum w]

/-- The jump rate `λ(s, w) = 1{s = 0}κ + 1{s = 1}α`. -/
def jsRate (α κ : ℝ) (x : Bool × W) : ℝ := if x.1 then α else κ

omit [Fintype W] in
theorem jsRate_nonneg {α κ : ℝ} (hα : 0 ≤ α) (hκ : 0 ≤ κ) (x : Bool × W) : 0 ≤ jsRate α κ x := by
  unfold jsRate
  split_ifs
  · exact hα
  · exact hκ

/-- For each action `a`, `Π(·, a, ·)` is a stochastic matrix. -/
theorem jsJump_isMarkov {P : Matrix W W ℝ} (hP : IsMarkov P) (a : Bool) :
    IsMarkov (Matrix.of fun x x' => jsJump P x a x') :=
  ⟨fun x x' => (jsJump_stochastic hP).1 x a x', fun x => (jsJump_stochastic hP).2 x a⟩

/-- The continuous-time job search MDP of §10.2.4: `Γ(x) = A`, `Q(x, a, x') = λ(x)(Π(x, a, x') −
I(x, x'))` and `r((s, w), a) = c1{s = 0} + w1{s = 1}`. -/
def jobSearch [DecidableEq W] {P : Matrix W W ℝ} (hP : IsMarkov P) {α κ δ : ℝ} (hα : 0 ≤ α)
    (hκ : 0 ≤ κ) (hδ : 0 < δ) (c : ℝ) (wage : W → ℝ) : CTMDP (Bool × W) Bool where
  Γ _ := Finset.univ
  Γ_nonempty _ := Finset.univ_nonempty
  δ := δ
  δ_pos := hδ
  r x _ := if x.1 then wage x.2 else c
  Q x a x' := jumpIntensity (jsRate α κ) (Matrix.of fun y y' => jsJump P y a y') x x'
  Q_nonneg x a _ x' h :=
    (isIntensity_jumpIntensity (jsRate_nonneg hα hκ) (jsJump_isMarkov hP a)).1 x x' h
  Q_sum x a _ := (isIntensity_jumpIntensity (jsRate_nonneg hα hκ) (jsJump_isMarkov hP a)).2 x

/-- For every `σ ∈ Σ = {0, 1}^X`, `Q_σ(x, x') = λ(x)(Π(x, σ(x), x') − I(x, x'))` is the intensity
matrix of a jump chain (p. 339). -/
theorem jobSearch_Qσ [DecidableEq W] {P : Matrix W W ℝ} (hP : IsMarkov P) {α κ δ : ℝ}
    (hα : 0 ≤ α) (hκ : 0 ≤ κ) (hδ : 0 < δ) (c : ℝ) (wage : W → ℝ) (σ : Bool × W → Bool) :
    (jobSearch hP hα hκ hδ c wage).Qσ σ =
        jumpIntensity (jsRate α κ) (Matrix.of fun x x' => jsJump P x (σ x) x') ∧
      IsMarkov (Matrix.of fun x x' => jsJump P x (σ x) x') ∧
      IsIntensity ((jobSearch hP hα hκ hδ c wage).Qσ σ) := by
  have hM : IsMarkov (Matrix.of fun x x' => jsJump P x (σ x) x') :=
    ⟨fun x x' => (jsJump_stochastic hP).1 x _ x', fun x => (jsJump_stochastic hP).2 x _⟩
  have he : (jobSearch hP hα hκ hδ c wage).Qσ σ =
      jumpIntensity (jsRate α κ) (Matrix.of fun x x' => jsJump P x (σ x) x') := by
    ext x x'
    rfl
  exact ⟨he, hM, he ▸ isIntensity_jumpIntensity (jsRate_nonneg hα hκ) hM⟩

/-- §10.2.4 (p. 339): Theorem 10.2.4 applies to job search, so an optimal policy exists, the value
function is the unique solution of the HJB equation, and HPI finds an optimal policy in finitely
many steps. -/
theorem jobSearch_optimality [Nonempty W] [DecidableEq W] {P : Matrix W W ℝ} (hP : IsMarkov P)
    {α κ δ : ℝ} (hα : 0 ≤ α) (hκ : 0 ≤ κ) (hδ : 0 < δ) (c : ℝ) (wage : W → ℝ) :
    ∃ vstar : Bool × W → ℝ,
      (∀ v, (jobSearch hP hα hκ hδ c wage).IsHJB v ↔ v = vstar) ∧
      (∃ σ : (jobSearch hP hα hκ hδ c wage).Policy,
        IsGreatest (Set.range fun τ : (jobSearch hP hα hκ hδ c wage).Policy =>
          (jobSearch hP hα hκ hδ c wage).vσ τ.1) ((jobSearch hP hα hκ hδ c wage).vσ σ.1)) ∧
      ∀ σ₀, ∃ k, (jobSearch hP hα hκ hδ c wage).hpiPolicy σ₀ (k + 1) =
          (jobSearch hP hα hκ hδ c wage).hpiPolicy σ₀ k ∧
        (jobSearch hP hα hκ hδ c wage).vσ ((jobSearch hP hα hκ hδ c wage).hpiPolicy σ₀ k).1 =
          vstar := by
  obtain ⟨vstar, h1, h2, -, ⟨σ, hσ⟩, h5⟩ := (jobSearch hP hα hκ hδ c wage).optimality
  exact ⟨vstar, h2, ⟨σ, hσ ▸ h1⟩, h5⟩

end SargentStachurski.ContinuousTime
