/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The infinitely repeated economy

Miao, §21.4.2, pp. 761–763: the one-period economy of §21.4.1 repeated forever.

* A history is a list `[(x₁, y₁), …, (x_{t-1}, y_{t-1})]` of past pairs, oldest first (the book's
  `(x^{t-1}, y^{t-1}) ∈ X^{t-1} × Y^{t-1}`, zipped). A strategy profile `σ = (σʰ, σᵍ)` is one map
  `CGProfile X Y = List (X × Y) → X × Y` (both components read the same history).
* `cg_cont σ h` is the continuation profile `σ|_h`, `cg_path σ` the induced outcome path (indexed
  from `0`: the book's period `t` is index `t - 1`), `cg_U δ r σ` the government's normalised
  discounted value `Uᵍ(σ) = (1 − δ) ∑ δ^{t-1} r(x_t, y_t)` and `cg_Ut δ r p t` the value from
  index `t` on of a path `p`.
* `cg_IsSPE δ r C σ` is Definition 21.4.1 (subgame perfection with only the government deviating;
  the household side must be a competitive equilibrium `C`), `cg_V δ r C` the set of SPE values.

The payoff `r` is bounded (`|r| ≤ M`, as for continuous `r` on the compact `X × Y` of the book)
and `0 ≤ δ < 1`. Proved here: the value recursion, the one-shot deviation principle
(`cg_isSPE_iff_oneShot`, the step behind "its proof follows from the definition"), Lemma 21.4.1,
SPE-ness of infinite repetition of a static Nash equilibrium (Example 21.4.3, first sentence),
and two bounds on SPE values used in §§21.4.3–21.4.4: SPE values lie in the range of `r` on `C`,
and they are at least any `c` with `c ≤ max_{y'} r(x, y')` for every competitive `(x, y)`
(`cg_V_lower`, the bound behind `v_min = min_y r(h(y), H(h(y)))`, p. 767).
-/

open Filter Topology

namespace Miao.DynamicGames

/-- A strategy profile of the repeated economy (Miao, p. 761): household and government actions
as functions of the history `[(x₁, y₁), …, (x_{t-1}, y_{t-1})]`. -/
abbrev CGProfile (X Y : Type*) := List (X × Y) → X × Y

variable {X Y : Type*}

/-- The continuation profile `σ|_(x^t, y^t)` (Miao, p. 762). -/
def cg_cont (σ : CGProfile X Y) (h : List (X × Y)) : CGProfile X Y := fun k => σ (h ++ k)

/-- Miao, p. 762: `σ|_h(1) = σ_{t+1}(h)` and `σ|_h(s + 1)(ξ^s, η^s) = σ_{t+s+1}(h, ξ^s, η^s)`. -/
theorem cg_cont_apply (σ : CGProfile X Y) (h k : List (X × Y)) : cg_cont σ h k = σ (h ++ k) :=
  rfl

theorem cg_cont_nil (σ : CGProfile X Y) : cg_cont σ [] = σ := rfl

theorem cg_cont_cont (σ : CGProfile X Y) (h k : List (X × Y)) :
    cg_cont (cg_cont σ h) k = cg_cont σ (h ++ k) := by
  funext l
  simp [cg_cont, List.append_assoc]

/-- The outcome path induced by a profile (Miao, p. 761), indexed from `0`. -/
def cg_path : CGProfile X Y → ℕ → X × Y
  | σ, 0 => σ []
  | σ, n + 1 => cg_path (cg_cont σ [σ []]) n

/-- The first `t` outcomes of a path, as a history. -/
def cg_prefix (p : ℕ → X × Y) (t : ℕ) : List (X × Y) := (List.range t).map p

theorem cg_prefix_succ (p : ℕ → X × Y) (t : ℕ) : cg_prefix p (t + 1) = cg_prefix p t ++ [p t] := by
  simp [cg_prefix, List.range_succ]

/-- After the first `t` outcomes of its own path, a profile continues along the shifted path. -/
theorem cg_path_cont_prefix (σ : CGProfile X Y) (t : ℕ) :
    cg_path (cg_cont σ (cg_prefix (cg_path σ) t)) = fun s => cg_path σ (t + s) := by
  induction t with
  | zero => funext s; simp [cg_prefix, cg_cont_nil]
  | succ t ih =>
    set ρ := cg_cont σ (cg_prefix (cg_path σ) t) with hρ
    have h0 : ρ [] = cg_path σ t := by
      have := congrFun ih 0
      rw [Nat.add_zero] at this
      exact this
    rw [cg_prefix_succ, ← cg_cont_cont, ← hρ, ← h0]
    funext s
    have := congrFun ih (s + 1)
    rw [show t + 1 + s = t + (s + 1) by omega, ← this]
    rfl

/-- Miao, p. 761: `(x_t(σ), y_t(σ)) = σ_t(x(σ)^{t-1}, y(σ)^{t-1})`. -/
theorem cg_path_spec (σ : CGProfile X Y) (t : ℕ) :
    cg_path σ t = σ (cg_prefix (cg_path σ) t) := by
  have := congrFun (cg_path_cont_prefix σ t) 0
  simpa [cg_path, cg_cont] using this.symm

/-- The normalised discounted value `(1 − δ) ∑_t δ^t r(p_t)` of an outcome path. -/
noncomputable def cg_pathValue (δ : ℝ) (r : X → Y → ℝ) (p : ℕ → X × Y) : ℝ :=
  (1 - δ) * ∑' t, δ ^ t * r (p t).1 (p t).2

/-- The government's value `Uᵍ(σ)` of a profile (Miao, p. 761). -/
noncomputable def cg_U (δ : ℝ) (r : X → Y → ℝ) (σ : CGProfile X Y) : ℝ :=
  cg_pathValue δ r (cg_path σ)

/-- The government's value `U_tᵍ(x, y)` from index `t` on (Miao, p. 766; the book's period
`t` is index `t - 1`). -/
noncomputable def cg_Ut (δ : ℝ) (r : X → Y → ℝ) (p : ℕ → X × Y) (t : ℕ) : ℝ :=
  cg_pathValue δ r (fun s => p (t + s))

/-- The household's value `Uʰ(σ) = (1 − δ) ∑ δ^{t-1} u(x_t, x_t, y_t)` (Miao, p. 761). -/
noncomputable def cg_Uh (δ : ℝ) (u : X → X → Y → ℝ) (σ : CGProfile X Y) : ℝ :=
  cg_pathValue δ (fun x y => u x x y) (cg_path σ)

/-- Miao, p. 761: with the benevolent government `r(x, y) = u(x, x, y)`, `Uʰ(σ) = Uᵍ(σ)`. -/
theorem cg_Uh_eq (δ : ℝ) (u : X → X → Y → ℝ) (σ : CGProfile X Y) :
    cg_Uh δ u σ = cg_U δ (fun x y => u x x y) σ := rfl

theorem cg_summable {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (p : ℕ → X × Y) :
    Summable (fun t => δ ^ t * r (p t).1 (p t).2) := by
  refine ((summable_geometric_of_lt_one hδ0 hδ1).mul_left M).of_norm_bounded (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 t), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM _ _) (pow_nonneg hδ0 t)

/-- The value of a path whose per-period payoffs are at most `b` is at most `b`. -/
theorem cg_pathValue_le {δ M b : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {p : ℕ → X × Y} (hb : ∀ t, r (p t).1 (p t).2 ≤ b) :
    cg_pathValue δ r p ≤ b := by
  have hg : Summable (fun t : ℕ => δ ^ t * b) :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_right b
  have hle : ∑' t, δ ^ t * r (p t).1 (p t).2 ≤ ∑' t : ℕ, δ ^ t * b :=
    Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left (hb t) (pow_nonneg hδ0 t))
      (cg_summable hδ0 hδ1 hM p) hg
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1] at hle
  have h1 : 0 < 1 - δ := by linarith
  unfold cg_pathValue
  calc (1 - δ) * ∑' t, δ ^ t * r (p t).1 (p t).2 ≤ (1 - δ) * ((1 - δ)⁻¹ * b) :=
        mul_le_mul_of_nonneg_left hle h1.le
    _ = b := by field_simp

/-- The value of a path whose per-period payoffs are at least `a` is at least `a`. -/
theorem cg_le_pathValue {δ M a : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {p : ℕ → X × Y} (ha : ∀ t, a ≤ r (p t).1 (p t).2) :
    a ≤ cg_pathValue δ r p := by
  have hg : Summable (fun t : ℕ => δ ^ t * a) :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_right a
  have hle : ∑' t : ℕ, δ ^ t * a ≤ ∑' t, δ ^ t * r (p t).1 (p t).2 :=
    Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left (ha t) (pow_nonneg hδ0 t))
      hg (cg_summable hδ0 hδ1 hM p)
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1] at hle
  have h1 : 0 < 1 - δ := by linarith
  unfold cg_pathValue
  calc a = (1 - δ) * ((1 - δ)⁻¹ * a) := by field_simp
    _ ≤ (1 - δ) * ∑' t, δ ^ t * r (p t).1 (p t).2 := mul_le_mul_of_nonneg_left hle h1.le

/-- The value of a constant path is the per-period payoff. -/
theorem cg_pathValue_const {δ : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (q : X × Y) :
    cg_pathValue δ r (fun _ => q) = r q.1 q.2 := by
  unfold cg_pathValue
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1]
  have h1 : 1 - δ ≠ 0 := by linarith
  field_simp

/-- The value recursion `U = (1 − δ) r(p₀) + δ U(shifted path)`. -/
theorem cg_pathValue_succ {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (p : ℕ → X × Y) :
    cg_pathValue δ r p = (1 - δ) * r (p 0).1 (p 0).2 + δ * cg_pathValue δ r (fun s => p (s + 1))
    := by
  unfold cg_pathValue
  rw [(cg_summable hδ0 hδ1 hM p).tsum_eq_zero_add]
  have : ∀ b : ℕ, δ ^ (b + 1) * r (p (b + 1)).1 (p (b + 1)).2 =
      δ * (δ ^ b * r (p (b + 1)).1 (p (b + 1)).2) := fun b => by ring
  simp_rw [this]
  rw [tsum_mul_left]
  ring

/-- The recursion for `U_t`: `U_t = (1 − δ) r(x_t, y_t) + δ U_{t+1}`. -/
theorem cg_Ut_succ {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (p : ℕ → X × Y) (t : ℕ) :
    cg_Ut δ r p t = (1 - δ) * r (p t).1 (p t).2 + δ * cg_Ut δ r p (t + 1) := by
  unfold cg_Ut
  rw [cg_pathValue_succ hδ0 hδ1 hM]
  have : (fun s => p (t + (s + 1))) = fun s => p (t + 1 + s) := by
    funext s; congr 1; omega
  simp [this]

theorem cg_Ut_zero (δ : ℝ) (r : X → Y → ℝ) (p : ℕ → X × Y) : cg_Ut δ r p 0 = cg_pathValue δ r p :=
  by simp [cg_Ut]

/-- The value recursion for a profile: `Uᵍ(σ) = (1 − δ) r(σ₁) + δ Uᵍ(σ|_{σ₁})`. -/
theorem cg_U_rec {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (σ : CGProfile X Y) :
    cg_U δ r σ = (1 - δ) * r (σ []).1 (σ []).2 + δ * cg_U δ r (cg_cont σ [σ []]) := by
  unfold cg_U
  rw [cg_pathValue_succ hδ0 hδ1 hM]
  rfl

/-- The value recursion after a history `h`. -/
theorem cg_U_cont_rec {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (τ : CGProfile X Y) (h : List (X × Y)) :
    cg_U δ r (cg_cont τ h) =
      (1 - δ) * r (τ h).1 (τ h).2 + δ * cg_U δ r (cg_cont τ (h ++ [τ h])) := by
  have e : cg_cont τ h [] = τ h := by simp [cg_cont]
  have := cg_U_rec hδ0 hδ1 hM (cg_cont τ h)
  rw [cg_cont_cont, e] at this
  exact this

/-- Values of profiles are bounded by the payoff bound. -/
theorem cg_abs_U_le {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (σ : CGProfile X Y) : |cg_U δ r σ| ≤ M :=
  abs_le.2 ⟨cg_le_pathValue hδ0 hδ1 hM (fun _ => (abs_le.1 (hM _ _)).1),
    cg_pathValue_le hδ0 hδ1 hM (fun _ => (abs_le.1 (hM _ _)).2)⟩

/-- The value of the profile that repeats `q` after every history. -/
theorem cg_U_const {δ : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (q : X × Y) :
    cg_U δ r (fun _ => q) = r q.1 q.2 := by
  have hp : cg_path (fun _ : List (X × Y) => q) = fun _ => q := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  unfold cg_U
  rw [hp, cg_pathValue_const hδ0 hδ1]

/-- The government's deviation: households keep `σʰ`, the government plays `σ̂ᵍ = g`. -/
def cg_withGov (σ : CGProfile X Y) (g : List (X × Y) → Y) : CGProfile X Y :=
  fun h => ((σ h).1, g h)

/-- **Definition 21.4.1** (SPE, Miao, p. 762): after every history `(x^{t-1}, y^{t-1})`,
(i) the prescribed pair is a competitive equilibrium and (ii) no government strategy `σ̂ᵍ`
does better in the continuation economy. -/
def cg_IsSPE (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (σ : CGProfile X Y) : Prop :=
  ∀ h, σ h ∈ C ∧ ∀ g, cg_U δ r (cg_cont (cg_withGov σ g) h) ≤ cg_U δ r (cg_cont σ h)

/-- **Definition 21.4.1** (Miao, p. 762), unfolded. -/
theorem definition_21_4_1 (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (σ : CGProfile X Y) :
    cg_IsSPE δ r C σ ↔ ∀ h, σ h ∈ C ∧
      ∀ g, cg_U δ r (cg_cont (cg_withGov σ g) h) ≤ cg_U δ r (cg_cont σ h) := Iff.rfl

/-- The one-shot condition at the root of a profile `ρ`: the first pair is competitive and no
one-period deviation `η` followed by `ρ`'s continuation pays. -/
def cg_OneShot (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (ρ : CGProfile X Y) : Prop :=
  ρ [] ∈ C ∧ ∀ η, (1 - δ) * r (ρ []).1 η + δ * cg_U δ r (cg_cont ρ [((ρ []).1, η)]) ≤ cg_U δ r ρ

/-- One-shot deviation principle: with bounded payoffs and `0 ≤ δ < 1`, `σ` is an SPE iff after
every history the one-shot condition holds. -/
theorem cg_isSPE_iff_oneShot {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (σ : CGProfile X Y) :
    cg_IsSPE δ r C σ ↔ ∀ h, cg_OneShot δ r C (cg_cont σ h) := by
  classical
  constructor
  · intro hS h
    have e : cg_cont σ h [] = σ h := by simp [cg_cont]
    refine ⟨by rw [e]; exact (hS h).1, fun η => ?_⟩
    rw [e, cg_cont_cont]
    set g : List (X × Y) → Y := fun k => if k = h then η else (σ k).2 with hg
    have h1 : cg_withGov σ g h = ((σ h).1, η) := by simp [cg_withGov, hg]
    have h2 : cg_cont (cg_withGov σ g) (h ++ [((σ h).1, η)]) =
        cg_cont σ (h ++ [((σ h).1, η)]) := by
      funext l
      simp [cg_cont, cg_withGov, hg]
    have := (hS h).2 g
    rw [cg_U_cont_rec hδ0 hδ1 hM, h1, h2] at this
    exact this
  · intro hO
    have e : ∀ h, cg_cont σ h [] = σ h := fun h => by simp [cg_cont]
    have hC : ∀ h, σ h ∈ C := fun h => by rw [← e]; exact (hO h).1
    have hos : ∀ h η, (1 - δ) * r (σ h).1 η + δ * cg_U δ r (cg_cont σ (h ++ [((σ h).1, η)]))
        ≤ cg_U δ r (cg_cont σ h) := fun h η => by
      have := (hO h).2 η
      rw [e, cg_cont_cont] at this
      exact this
    have key : ∀ n : ℕ, ∀ h g, cg_U δ r (cg_cont (cg_withGov σ g) h) ≤
        cg_U δ r (cg_cont σ h) + δ ^ n * (2 * M) := by
      intro n
      induction n with
      | zero =>
        intro h g
        have h1 := abs_le.1 (cg_abs_U_le hδ0 hδ1 hM (cg_cont (cg_withGov σ g) h))
        have h2 := abs_le.1 (cg_abs_U_le hδ0 hδ1 hM (cg_cont σ h))
        simp only [pow_zero, one_mul]
        linarith
      | succ n ih =>
        intro h g
        rw [cg_U_cont_rec hδ0 hδ1 hM]
        have h1 : cg_withGov σ g h = ((σ h).1, g h) := rfl
        have ih' := ih (h ++ [cg_withGov σ g h]) g
        rw [h1] at ih' ⊢
        have hos' := hos h (g h)
        have : δ * cg_U δ r (cg_cont (cg_withGov σ g) (h ++ [((σ h).1, g h)])) ≤
            δ * (cg_U δ r (cg_cont σ (h ++ [((σ h).1, g h)])) + δ ^ n * (2 * M)) :=
          mul_le_mul_of_nonneg_left ih' hδ0
        rw [pow_succ]
        nlinarith
    refine fun h => ⟨hC h, fun g => ?_⟩
    have ht : Tendsto (fun n : ℕ => cg_U δ r (cg_cont σ h) + δ ^ n * (2 * M)) atTop
        (𝓝 (cg_U δ r (cg_cont σ h) + 0 * (2 * M))) :=
      tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const _)
    have := ge_of_tendsto' ht (fun n => key n h g)
    simpa using this

/-- Continuations of an SPE are SPEs. -/
theorem cg_IsSPE.cont {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {σ : CGProfile X Y} (hσ : cg_IsSPE δ r C σ) (h : List (X × Y)) :
    cg_IsSPE δ r C (cg_cont σ h) := by
  rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM] at hσ ⊢
  intro k
  rw [cg_cont_cont]
  exact hσ (h ++ k)

/-- The root deviation inequality of an SPE. -/
theorem cg_IsSPE.root {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {σ : CGProfile X Y} (hσ : cg_IsSPE δ r C σ) :
    cg_OneShot δ r C σ :=
  (cg_isSPE_iff_oneShot hδ0 hδ1 hM σ).1 hσ []

/-- **Lemma 21.4.1** (Miao, p. 762). With first-period outcome `(x, y) = σ₁`, `σ` is an SPE iff
(i) every continuation `σ|_(ξ, η)` is an SPE, (ii) `(x, y)` is a competitive equilibrium, and
(iii) `(1 − δ) r(x, y) + δ Uᵍ(σ|_(x, y)) ≥ (1 − δ) r(x, η) + δ Uᵍ(σ|_(x, η))` for all `η`. -/
theorem lemma_21_4_1 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (σ : CGProfile X Y) :
    cg_IsSPE δ r C σ ↔ (∀ ξ η, cg_IsSPE δ r C (cg_cont σ [(ξ, η)])) ∧ σ [] ∈ C ∧
      ∀ η, (1 - δ) * r (σ []).1 η + δ * cg_U δ r (cg_cont σ [((σ []).1, η)]) ≤
        (1 - δ) * r (σ []).1 (σ []).2 + δ * cg_U δ r (cg_cont σ [σ []]) := by
  rw [← cg_U_rec hδ0 hδ1 hM]
  constructor
  · intro hS
    exact ⟨fun ξ η => hS.cont hδ0 hδ1 hM _, (hS.root hδ0 hδ1 hM).1,
      (hS.root hδ0 hδ1 hM).2⟩
  · rintro ⟨hcont, hC, hdev⟩
    rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM]
    intro h
    cases h with
    | nil => exact ⟨hC, hdev⟩
    | cons q h' =>
      have e : cg_cont σ (q :: h') = cg_cont (cg_cont σ [q]) h' := by
        rw [cg_cont_cont]; rfl
      rw [e]
      exact (cg_isSPE_iff_oneShot hδ0 hδ1 hM _).1 (hcont q.1 q.2) h'

/-- Example 21.4.3 (Miao, p. 763), first sentence: infinite repetition of a one-period Nash
equilibrium `(x^N, y^N)` (competitive, and `y^N` a best response to `x^N`) is an SPE, with
value `r(x^N, y^N)`. -/
theorem cg_nash_repetition_spe {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xN : X} {yN : Y} (hC : (xN, yN) ∈ C)
    (hN : ∀ y', r xN y' ≤ r xN yN) :
    cg_IsSPE δ r C (fun _ => (xN, yN)) ∧ cg_U δ r (fun _ => (xN, yN)) = r xN yN := by
  refine ⟨?_, cg_U_const hδ0 hδ1 _⟩
  rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM]
  intro h
  refine ⟨hC, fun η => ?_⟩
  have e : ∀ k, cg_cont (fun _ : List (X × Y) => (xN, yN)) k = fun _ => (xN, yN) :=
    fun k => rfl
  rw [e, e, cg_U_const hδ0 hδ1]
  have := hN η
  have h1 : 0 ≤ 1 - δ := by linarith
  nlinarith

/-- The set of SPE values `V = {Uᵍ(σ) : σ is an SPE}` (Miao, p. 764). -/
def cg_V (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) : Set ℝ :=
  {v | ∃ σ, cg_IsSPE δ r C σ ∧ cg_U δ r σ = v}

/-- SPE values are bounded by the payoff bound. -/
theorem cg_V_abs_le {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {v : ℝ} (hv : v ∈ cg_V δ r C) : |v| ≤ M := by
  obtain ⟨σ, -, rfl⟩ := hv
  exact cg_abs_U_le hδ0 hδ1 hM σ

/-- The SPE value set is bounded. -/
theorem cg_V_isBounded {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) : Bornology.IsBounded (cg_V δ r C) :=
  (isBounded_iff_forall_norm_le (E := ℝ)).2
    ⟨M, fun _ hv => by rw [Real.norm_eq_abs]; exact cg_V_abs_le hδ0 hδ1 hM hv⟩

/-- The path of an SPE stays in the competitive-equilibrium set. -/
theorem cg_IsSPE.path_mem {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {σ : CGProfile X Y} (hσ : cg_IsSPE δ r C σ)
    (t : ℕ) : cg_path σ t ∈ C := by
  induction t generalizing σ with
  | zero => exact (hσ []).1
  | succ t ih => exact ih (hσ.cont hδ0 hδ1 hM _)

/-- Miao, p. 765, step 1 of the algorithm: SPE values lie in `[min_C r, max_C r]`; here, in
`[a, b]` whenever `a ≤ r ≤ b` on `C`. -/
theorem cg_V_subset_Icc {δ M a b : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hab : ∀ p ∈ C, a ≤ r p.1 p.2 ∧ r p.1 p.2 ≤ b) :
    cg_V δ r C ⊆ Set.Icc a b := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact ⟨cg_le_pathValue hδ0 hδ1 hM (fun t => (hab _ (hσ.path_mem hδ0 hδ1 hM t)).1),
    cg_pathValue_le hδ0 hδ1 hM (fun t => (hab _ (hσ.path_mem hδ0 hδ1 hM t)).2)⟩

/-- Miao, p. 767: the worst SPE value is at least `min_y r(h(y), H(h(y)))`. Here: if every
competitive `(x, y)` admits a deviation `y'` with `r(x, y') ≥ c`, every SPE value is `≥ c`. -/
theorem cg_V_lower {δ M c : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (hc : ∀ x y, (x, y) ∈ C → ∃ y', c ≤ r x y') :
    ∀ v ∈ cg_V δ r C, c ≤ v := by
  intro v hv
  have hne : (cg_V δ r C).Nonempty := ⟨v, hv⟩
  have hbdd : BddBelow (cg_V δ r C) :=
    ⟨-M, fun w hw => (abs_le.1 (cg_V_abs_le hδ0 hδ1 hM hw)).1⟩
  set m := sInf (cg_V δ r C)
  have key : ∀ w ∈ cg_V δ r C, (1 - δ) * c + δ * m ≤ w := by
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨y', hy'⟩ := hc _ _ (hσ []).1
    have hroot := (hσ.root hδ0 hδ1 hM).2 y'
    have hmem : cg_U δ r (cg_cont σ [((σ []).1, y')]) ∈ cg_V δ r C :=
      ⟨_, hσ.cont hδ0 hδ1 hM _, rfl⟩
    have h1 : m ≤ cg_U δ r (cg_cont σ [((σ []).1, y')]) := csInf_le hbdd hmem
    have h2 : (1 - δ) * c ≤ (1 - δ) * r (σ []).1 y' :=
      mul_le_mul_of_nonneg_left hy' (by linarith)
    have h3 : δ * m ≤ δ * cg_U δ r (cg_cont σ [((σ []).1, y')]) :=
      mul_le_mul_of_nonneg_left h1 hδ0
    linarith
  have hm : (1 - δ) * c + δ * m ≤ m := le_csInf hne key
  have hcm : c ≤ m := by
    by_contra hlt
    push Not at hlt
    nlinarith
  exact hcm.trans (csInf_le hbdd hv)

end Miao.DynamicGames
