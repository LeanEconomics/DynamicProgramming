/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.BoundedReturns

/-!
# The functional equation with a weighted bound

Several problems of Chapter 5 (Exercise 5.8) have returns that grow with the state, so `T` is
not a self-map of the bounded functions. With a positive continuous weight `w` such that
`|F(x, y)| ≤ Bw(x)` and `βw(y) ≤ ρw(x)` for `y ∈ Γ(x)` and some `ρ < 1`, the functional equation
has exactly one continuous solution with `|v| ≤ Cw`: apply the contraction mapping theorem to
`u = v/w` in `C(X)`, where `T` becomes
`(T̃u)(x) = max_{y ∈ Γ(x)} [F(x, y) + βw(y)u(y)]/w(x)`, a contraction of modulus `ρ` (Blackwell's
conditions).

* `WeightedHyp`: the hypotheses; `wbellman`: the operator `T̃`; `wbellman_contraction`.
* `SolvesFE`: `v` satisfies `v(x) = max_{y ∈ Γ(x)} [F(x, y) + βv(y)]`, with the maximum
  attained.
* `weighted_exists_unique`: exactly one continuous `v` with `|v| ≤ Cw` solves the functional
  equation.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {X : Type*} [MetricSpace X] {Γ : X → Set X} {F : X × X → ℝ} {w : X → ℝ} {β ρ : ℝ}

/-- The hypotheses for the weighted functional equation. -/
structure WeightedHyp (Γ : X → Set X) (F : X × X → ℝ) (w : X → ℝ) (β ρ : ℝ) : Prop where
  h43 : Assumption43 Γ
  cont : ContinuousOn F (graph Γ)
  w_cont : Continuous w
  w_pos : ∀ x, 0 < w x
  bdd : ∃ B, ∀ p ∈ graph Γ, |F p| ≤ B * w p.1
  β_pos : 0 < β
  ρ_lt : ρ < 1
  growth : ∀ x, ∀ y ∈ Γ x, β * w y ≤ ρ * w x

/-- `v` solves the functional equation, with the maximum attained. -/
def SolvesFE (Γ : X → Set X) (F : X × X → ℝ) (β : ℝ) (v : X → ℝ) : Prop :=
  ∀ x, (∃ y ∈ Γ x, v x = F (x, y) + β * v y) ∧ ∀ y ∈ Γ x, F (x, y) + β * v y ≤ v x

/-- The scaled objective `[F(x, y) + βw(y)u(y)]/w(x)`. -/
noncomputable def wobj (F : X × X → ℝ) (w : X → ℝ) (β : ℝ) (u : X → ℝ) (p : X × X) : ℝ :=
  (F p + β * (w p.2 * u p.2)) / w p.1

theorem WeightedHyp.ρ_pos (hW : WeightedHyp Γ F w β ρ) [Nonempty X] : 0 < ρ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y, hy⟩ := hW.h43.nonempty x
  have := hW.growth x y hy
  have h1 := mul_pos hW.β_pos (hW.w_pos y)
  by_contra hρ
  push Not at hρ
  nlinarith [hW.w_pos x]

theorem continuousOn_wobj (hW : WeightedHyp Γ F w β ρ) {u : X → ℝ} (hu : Continuous u) :
    ContinuousOn (wobj F w β u) (graph Γ) :=
  (hW.cont.add (continuous_const.mul ((hW.w_cont.comp continuous_snd).mul
    (hu.comp continuous_snd))).continuousOn).div
    (hW.w_cont.comp continuous_fst).continuousOn fun p _ => (hW.w_pos p.1).ne'

/-- The bound `|[F(x, y) + βw(y)u(y)]/w(x)| ≤ B + ρ‖u‖` on the graph. -/
theorem abs_wobj_le (hW : WeightedHyp Γ F w β ρ) (u : X →ᵇ ℝ) {p : X × X} (hp : p ∈ graph Γ) :
    |wobj F w β u p| ≤ hW.bdd.choose + ρ * ‖u‖ := by
  have hw := hW.w_pos p.1
  have hwy := hW.w_pos p.2
  rw [wobj, abs_div, abs_of_pos hw, div_le_iff₀ hw]
  have h1 := hW.bdd.choose_spec p hp
  have hu := u.norm_coe_le_norm p.2
  rw [Real.norm_eq_abs] at hu
  have h2 : |β * (w p.2 * u p.2)| ≤ ρ * w p.1 * ‖u‖ := by
    rw [abs_mul, abs_mul, abs_of_pos hW.β_pos, abs_of_pos hwy]
    calc β * (w p.2 * |u p.2|) = β * w p.2 * |u p.2| := by ring
      _ ≤ ρ * w p.1 * ‖u‖ := mul_le_mul (hW.growth p.1 p.2 hp) hu (abs_nonneg _)
          (by nlinarith [hW.growth p.1 p.2 hp, mul_pos hW.β_pos hwy])
  calc |F p + β * (w p.2 * u p.2)| ≤ |F p| + |β * (w p.2 * u p.2)| := abs_add_le _ _
    _ ≤ hW.bdd.choose * w p.1 + ρ * w p.1 * ‖u‖ := add_le_add h1 h2
    _ = (hW.bdd.choose + ρ * ‖u‖) * w p.1 := by ring

theorem bound_wmaxValue (hW : WeightedHyp Γ F w β ρ) (u : X →ᵇ ℝ) (x : X) :
    ‖maxValue (wobj F w β u) Γ x‖ ≤ hW.bdd.choose + ρ * ‖u‖ := by
  obtain ⟨y, hy, hval, -⟩ := exists_argmax (continuousOn_wobj hW u.continuous)
    (hW.h43.compact x) (hW.h43.nonempty x)
  rw [← hval, Real.norm_eq_abs]
  exact abs_wobj_le hW u hy

/-- The operator `(T̃u)(x) = max_{y ∈ Γ(x)} [F(x, y) + βw(y)u(y)]/w(x)` on `C(X)`. -/
noncomputable def wbellman (hW : WeightedHyp Γ F w β ρ) (u : X →ᵇ ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => maxValue (wobj F w β u) Γ x)
    (theorem_3_6 (continuousOn_wobj hW u.continuous) hW.h43.compact hW.h43.lhc hW.h43.uhc).1
    (hW.bdd.choose + ρ * ‖u‖) (bound_wmaxValue hW u)

theorem exists_wbellman_argmax (hW : WeightedHyp Γ F w β ρ) (u : X →ᵇ ℝ) (x : X) :
    ∃ y ∈ Γ x, wbellman hW u x = wobj F w β u (x, y) ∧
      ∀ z ∈ Γ x, wobj F w β u (x, z) ≤ wbellman hW u x := by
  obtain ⟨y, hy, hval, hmax⟩ := exists_argmax (continuousOn_wobj hW u.continuous)
    (hW.h43.compact x) (hW.h43.nonempty x)
  exact ⟨y, hy, hval.symm, fun z hz => (hmax z hz).trans_eq hval⟩

/-- `T̃` is a contraction of modulus `ρ`. -/
theorem wbellman_contraction [Nonempty X] (hW : WeightedHyp Γ F w β ρ) :
    IsContraction (wbellman hW) ρ := by
  refine ⟨hW.ρ_pos, hW.ρ_lt, blackwell hW.ρ_pos.le (fun f g hfg x => ?_) (fun f a ha x => ?_)⟩
  · obtain ⟨y, hy, hval, -⟩ := exists_wbellman_argmax hW f x
    obtain ⟨-, -, -, hmax⟩ := exists_wbellman_argmax hW g x
    change wbellman hW f x ≤ wbellman hW g x
    rw [hval]
    refine le_trans ?_ (hmax y hy)
    simp only [wobj]
    refine div_le_div_of_nonneg_right ?_ (hW.w_pos x).le
    have := mul_le_mul_of_nonneg_left (show f y ≤ g y from hfg y) (hW.w_pos y).le
    nlinarith [hW.β_pos]
  · obtain ⟨y, hy, hval, -⟩ := exists_wbellman_argmax hW (f + const X a) x
    obtain ⟨-, -, -, hmax⟩ := exists_wbellman_argmax hW f x
    change wbellman hW (f + const X a) x ≤ (wbellman hW f + const X (ρ * a)) x
    rw [hval, BoundedContinuousFunction.add_apply, const_apply]
    have h1 := hmax y hy
    have hgr := hW.growth x y hy
    have hw := hW.w_pos x
    simp only [wobj, BoundedContinuousFunction.add_apply, const_apply] at h1 ⊢
    have e : (F (x, y) + β * (w y * (f y + a))) / w x =
        (F (x, y) + β * (w y * f y)) / w x + β * w y * a / w x := by
      field_simp; ring
    rw [e]
    have h2 : β * w y * a / w x ≤ ρ * a := by
      rw [div_le_iff₀ hw]; nlinarith
    linarith

/-- `u` is a fixed point of `T̃` iff `wu` solves the functional equation. -/
theorem solvesFE_iff (hW : WeightedHyp Γ F w β ρ) (u : X →ᵇ ℝ) :
    wbellman hW u = u ↔ SolvesFE Γ F β fun x => w x * u x := by
  constructor
  · intro hu x
    obtain ⟨y, hy, hval, hmax⟩ := exists_wbellman_argmax hW u x
    rw [hu] at hval hmax
    have hw := hW.w_pos x
    refine ⟨⟨y, hy, ?_⟩, fun z hz => ?_⟩
    · change w x * u x = F (x, y) + β * (w y * u y)
      rw [hval, wobj]; field_simp
    · have := hmax z hz
      rw [wobj, div_le_iff₀ hw] at this
      change F (x, z) + β * (w z * u z) ≤ w x * u x
      linarith
  · intro hv
    ext x
    have hw := hW.w_pos x
    obtain ⟨⟨y, hy, hval⟩, hmax⟩ := hv x
    beta_reduce at hval hmax
    refine le_antisymm ?_ ?_
    · obtain ⟨z, hz, hzval, -⟩ := exists_wbellman_argmax hW u x
      rw [hzval, wobj, div_le_iff₀ hw]
      have := hmax z hz
      linarith
    · obtain ⟨-, -, -, hle⟩ := exists_wbellman_argmax hW u x
      refine le_trans ?_ (hle y hy)
      rw [wobj, le_div_iff₀ hw]
      linarith

/-- **The weighted functional equation.** Exactly one continuous `v` with `|v| ≤ Cw` for some
`C` solves the functional equation. -/
theorem weighted_exists_unique [Nonempty X] (hW : WeightedHyp Γ F w β ρ) :
    ∃ v : X → ℝ, SolvesFE Γ F β v ∧ Continuous v ∧ (∃ C, ∀ x, |v x| ≤ C * w x) ∧
      ∀ v' : X → ℝ, SolvesFE Γ F β v' → Continuous v' → (∃ C, ∀ x, |v' x| ≤ C * w x) →
        v' = v := by
  obtain ⟨u, hu, huniq, -⟩ := theorem_3_2 (wbellman_contraction hW)
  refine ⟨fun x => w x * u x, (solvesFE_iff hW u).1 hu, hW.w_cont.mul u.continuous,
    ⟨‖u‖, fun x => ?_⟩, fun v' hv' hc' ⟨C, hC⟩ => ?_⟩
  · rw [abs_mul, abs_of_pos (hW.w_pos x), mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using u.norm_coe_le_norm x)
      (hW.w_pos x).le
  · -- `u' = v'/w` is a bounded continuous fixed point of `T̃`
    set u' : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => v' x / w x)
      (hc'.div hW.w_cont fun x => (hW.w_pos x).ne') C fun x => by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (hW.w_pos x), div_le_iff₀ (hW.w_pos x)]
        exact hC x
    have hv'eq : (fun x => w x * u' x) = v' := by
      funext x
      change w x * (v' x / w x) = v' x
      field_simp [(hW.w_pos x).ne']
    have hfix : wbellman hW u' = u' := (solvesFE_iff hW u').2 (hv'eq ▸ hv')
    rw [← hv'eq, huniq u' hfix]

end StokeyLucasPrescott.DeterministicApplications
