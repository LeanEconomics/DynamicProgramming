/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSustainability.Basics
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# A static one-region integrated assessment model

AKMM, §25.4.1 (pp. 764–767). Output `Y = AE^ν` (25.12), coal at marginal cost `p`, damages
`γE²` (25.14), consumption (25.15). Throughout `A > 0`, `0 < ν < 1`, `p > 0`.

* The market economy: the first-order condition (25.16) has the unique solution
  `E(τ) = (νA/(p + τ))^{1/(1−ν)}` (`eq_25_16`), which is the firm's unique optimum
  (`static_firm_optimal`), strictly decreasing in the tax (`staticE_strictAnti`).
* The planner (25.17)–(25.18): a unique interior optimum `E*` exists (`eq_25_18_exists`), it
  solves (25.18), maximises consumption (`eq_25_17`) and is unique (`eq_25_17_unique`); the
  laissez-faire economy emits too much (`static_laissez_faire_excess`) and the Pigou tax
  `τ = 2γE*` implements `E*` (`static_pigou`).
* "τ = 0 constitutes a maximum" for the private economy, and its derivative there is zero, so a
  small tax has second-order private costs (`static_private_max`,
  `static_private_hasDerivAt`, `static_private_deriv_zero`).
* Prices versus quantities (25.19): a cap at `E*` has the unique equilibrium permit price
  `λ = 2γE*` (`eq_25_19`); a non-binding cap gives `λ = 0` (`static_cap_nonbinding`); a
  binding cap gives `λ = νAĒ^{ν−1} − p > 0` (`static_cap_binding`).
* Two firms (p. 767), with the coal cost `p` the book's planning problem omits: the planner's
  first-order conditions `ν_iAE_i^{ν_i−1} = p + 2γ(E₁ + E₂)` have a solution
  (`static_two_exists`), which is the unique optimum (`static_two_optimal`,
  `static_two_unique`); the tax `2γ(E₁* + E₂*)` implements it (`static_two_pigou`) and so does
  a single aggregate cap, whose permit price equals the tax (`static_two_cap`).
-/

namespace AKMM.Sustainability

open Real Filter Topology

/-- AKMM, (25.16), p. 765: the market demand for coal, `E(τ) = (νA/(p + τ))^{1/(1−ν)}`. -/
noncomputable def staticE (ν A p τ : ℝ) : ℝ := (ν * A / (p + τ)) ^ (1 / (1 - ν))

variable {ν A p : ℝ}

/-- `E(τ) > 0`. -/
theorem staticE_pos (hν0 : 0 < ν) (hA : 0 < A) {τ : ℝ} (hpτ : 0 < p + τ) :
    0 < staticE ν A p τ := by
  unfold staticE; positivity

/-- AKMM, (25.16), p. 765: for `E > 0` the firm's first-order condition `νAE^{ν−1} = p + τ`
holds iff `E = E(τ)`. -/
theorem eq_25_16 (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {τ E : ℝ} (hpτ : 0 < p + τ)
    (hE : 0 < E) : ν * A * E ^ (ν - 1) = p + τ ↔ E = staticE ν A p τ := by
  have hνA : 0 < ν * A := mul_pos hν0 hA
  have hne : ν - 1 ≠ 0 := by linarith
  have h1ν : (1 : ℝ) - ν ≠ 0 := (by linarith : (0 : ℝ) < 1 - ν).ne'
  constructor
  · intro h
    have h1 : E ^ (ν - 1) = (p + τ) / (ν * A) := by field_simp; linarith
    have h2 : E = ((p + τ) / (ν * A)) ^ (ν - 1)⁻¹ := by
      rw [← h1, Real.rpow_rpow_inv hE.le hne]
    rw [h2, staticE, ← inv_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    congr 1
    field_simp
    ring
  · intro h
    rw [h, staticE, ← Real.rpow_mul (by positivity)]
    have : 1 / (1 - ν) * (ν - 1) = -1 := by field_simp; ring
    rw [this, Real.rpow_neg_one]
    field_simp

/-- The marginal product `νAE^{ν−1}` is strictly decreasing in `E > 0`. -/
theorem static_mp_strictAnti (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {E E' : ℝ} (hE : 0 < E)
    (hEE : E < E') : ν * A * E' ^ (ν - 1) < ν * A * E ^ (ν - 1) := by
  have := Real.rpow_lt_rpow_of_neg hE hEE (by linarith : ν - 1 < 0)
  exact mul_lt_mul_of_pos_left this (mul_pos hν0 hA)

/-- `E < E(τ)` iff the marginal product at `E` exceeds `p + τ`. -/
theorem static_lt_staticE_iff (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {τ E : ℝ}
    (hpτ : 0 < p + τ) (hE : 0 < E) : E < staticE ν A p τ ↔ p + τ < ν * A * E ^ (ν - 1) := by
  have hs := staticE_pos hν0 hA hpτ
  have hfoc := (eq_25_16 hν0 hν1 hA hpτ hs).mpr rfl
  constructor
  · intro h; rw [← hfoc]; exact static_mp_strictAnti hν0 hν1 hA hE h
  · intro h
    by_contra hge
    rw [not_lt] at hge
    rcases hge.lt_or_eq with hlt | heq
    · have := static_mp_strictAnti hν0 hν1 hA hs hlt; linarith
    · rw [← heq] at h; linarith

/-- AKMM, p. 765: "there is direct negative relationship between `E` and `τ`": `E(τ)` is
strictly decreasing on `τ > −p`. -/
theorem staticE_strictAnti (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {τ τ' : ℝ}
    (hpτ : 0 < p + τ) (hττ : τ < τ') : staticE ν A p τ' < staticE ν A p τ := by
  have hpτ' : 0 < p + τ' := by linarith
  unfold staticE
  apply Real.rpow_lt_rpow (by positivity) _ (by have : 0 < 1 - ν := by linarith
                                                positivity)
  exact div_lt_div_of_pos_left (mul_pos hν0 hA) hpτ (by linarith)

/-- AKMM, (25.13), p. 765: `E(τ)` is the firm's unique optimum: for every `E ≥ 0`,
`AE^ν − (p + τ)E ≤ AE(τ)^ν − (p + τ)E(τ)`, strictly if `E ≠ E(τ)`. -/
theorem static_firm_optimal (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {τ E : ℝ}
    (hpτ : 0 < p + τ) (hE : 0 ≤ E) :
    A * E ^ ν - (p + τ) * E ≤ A * staticE ν A p τ ^ ν - (p + τ) * staticE ν A p τ ∧
      (E ≠ staticE ν A p τ →
        A * E ^ ν - (p + τ) * E < A * staticE ν A p τ ^ ν - (p + τ) * staticE ν A p τ) := by
  set s := staticE ν A p τ
  have hs := staticE_pos hν0 hA hpτ
  have hfoc := (eq_25_16 hν0 hν1 hA hpτ hs).mpr rfl
  constructor
  · have ht := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent hν0.le hν1.le hE hs
    nlinarith [mul_le_mul_of_nonneg_left ht hA.le]
  · intro hne
    have ht := sust_rpow_lt_tangent hν0 hν1 hE hs hne
    nlinarith [mul_lt_mul_of_pos_left ht hA]

/-- AKMM, (25.17), p. 766: consumption `AE^ν − pE − γE²`. -/
noncomputable def staticW (ν A p γ E : ℝ) : ℝ := A * E ^ ν - p * E - γ * E ^ 2

/-- AKMM, (25.18), p. 766: with `γ > 0` the planner's first-order condition
`νAE^{ν−1} = p + 2γE` has a solution `E* > 0`. -/
theorem eq_25_18_exists (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) {γ : ℝ}
    (hγ : 0 < γ) : ∃ E, 0 < E ∧ ν * A * E ^ (ν - 1) = p + 2 * γ * E := by
  set E0 := staticE ν A p 0
  have hE0 : 0 < E0 := staticE_pos hν0 hA (by linarith)
  set E1 := staticE ν A p (2 * γ * E0)
  have hE1 : 0 < E1 := staticE_pos hν0 hA (by positivity)
  have h10 : E1 < E0 := staticE_strictAnti hν0 hν1 hA (by linarith) (by positivity)
  set g : ℝ → ℝ := fun E => ν * A * E ^ (ν - 1) - p - 2 * γ * E
  have hg1 : 0 < g E1 := by
    have := (eq_25_16 hν0 hν1 hA (by positivity) hE1).mpr rfl
    simp only [g]; nlinarith
  have hg0 : g E0 < 0 := by
    have := (eq_25_16 hν0 hν1 hA (by linarith : (0 : ℝ) < p + 0) hE0).mpr rfl
    simp only [g]; nlinarith
  have hcont : ContinuousOn g (Set.Icc E1 E0) := by
    refine ContinuousOn.sub (ContinuousOn.sub ?_ continuousOn_const) (by fun_prop)
    refine ContinuousOn.mul continuousOn_const ?_
    exact continuousOn_id.rpow_const fun x hx =>
      Or.inl (by simp only [id]; exact (lt_of_lt_of_le hE1 hx.1).ne')
  obtain ⟨E, hE, hgE⟩ := intermediate_value_Icc' h10.le hcont ⟨hg0.le, hg1.le⟩
  refine ⟨E, by linarith [hE.1], ?_⟩
  simp only [g] at hgE
  linarith

/-- AKMM, (25.17)–(25.18), p. 766: a solution `E* > 0` of (25.18) maximises consumption over
`E ≥ 0`. -/
theorem eq_25_17 (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {γ Es E : ℝ} (hγ : 0 ≤ γ)
    (hEs : 0 < Es) (hfoc : ν * A * Es ^ (ν - 1) = p + 2 * γ * Es) (hE : 0 ≤ E) :
    staticW ν A p γ E ≤ staticW ν A p γ Es := by
  have ht := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent hν0.le hν1.le hE hEs
  unfold staticW
  nlinarith [mul_le_mul_of_nonneg_left ht hA.le, mul_nonneg hγ (sq_nonneg (E - Es))]

/-- AKMM, p. 766: the planner's optimum is unique. -/
theorem eq_25_17_unique (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {γ Es E : ℝ} (hγ : 0 ≤ γ)
    (hEs : 0 < Es) (hfoc : ν * A * Es ^ (ν - 1) = p + 2 * γ * Es) (hE : 0 ≤ E)
    (hne : E ≠ Es) : staticW ν A p γ E < staticW ν A p γ Es := by
  have ht := sust_rpow_lt_tangent hν0 hν1 hE hEs hne
  unfold staticW
  nlinarith [mul_lt_mul_of_pos_left ht hA, mul_nonneg hγ (sq_nonneg (E - Es))]

/-- AKMM, p. 766: with `γ > 0` and `τ = 0` "emissions will be too high relative to the
efficient level": `E* < E(0)`. -/
theorem static_laissez_faire_excess (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p)
    {γ Es : ℝ} (hγ : 0 < γ) (hEs : 0 < Es) (hfoc : ν * A * Es ^ (ν - 1) = p + 2 * γ * Es) :
    Es < staticE ν A p 0 := by
  rw [static_lt_staticE_iff hν0 hν1 hA (by linarith) hEs, hfoc]
  have : 0 < 2 * γ * Es := by positivity
  linarith

/-- AKMM, p. 766, Pigou's recipe: the tax `τ = 2γE*` implements the optimum, `E(2γE*) = E*`. -/
theorem static_pigou (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) {γ Es : ℝ}
    (hγ : 0 ≤ γ) (hEs : 0 < Es) (hfoc : ν * A * Es ^ (ν - 1) = p + 2 * γ * Es) :
    staticE ν A p (2 * γ * Es) = Es :=
  ((eq_25_16 hν0 hν1 hA (by positivity) hEs).mp hfoc).symm

/-- AKMM, p. 766: the private surplus `AE(τ)^ν − pE(τ)` (consumption ignoring damages). -/
noncomputable def staticPrivate (ν A p τ : ℝ) : ℝ := A * staticE ν A p τ ^ ν - p * staticE ν A p τ

/-- AKMM, p. 766: "For the private economy, i.e., ignoring the externality entirely, `τ = 0`
constitutes a maximum". -/
theorem static_private_max (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) {τ : ℝ}
    (hpτ : 0 < p + τ) : staticPrivate ν A p τ ≤ staticPrivate ν A p 0 := by
  have h := (static_firm_optimal hν0 hν1 hA (p := p) (τ := 0) (by linarith)
    (staticE_pos hν0 hA hpτ).le).1
  simp only [add_zero] at h
  exact h

/-- AKMM, p. 766: the private surplus is differentiable with derivative `τE'(τ)`, where
`E'(τ) = −E(τ)/((1 − ν)(p + τ))`. -/
theorem static_private_hasDerivAt (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {τ : ℝ}
    (hpτ : 0 < p + τ) :
    HasDerivAt (staticPrivate ν A p)
      (τ * (-(staticE ν A p τ) / ((1 - ν) * (p + τ)))) τ := by
  have h1ν : 0 < 1 - ν := by linarith
  -- the derivative of `E(τ)`
  have hb : HasDerivAt (fun t => ν * A / (p + t)) (-(ν * A) / (p + τ) ^ 2) τ := by
    have := ((hasDerivAt_id τ).const_add p).inv hpτ.ne'
    convert this.const_mul (ν * A) using 1
    · funext t; simp [div_eq_mul_inv]
    · simp only [id]; field_simp
  have hE : HasDerivAt (staticE ν A p) (-(staticE ν A p τ) / ((1 - ν) * (p + τ))) τ := by
    have := hb.rpow_const (p := 1 / (1 - ν)) (Or.inl (by positivity))
    unfold staticE
    convert this using 1
    rw [Real.rpow_sub_one (by positivity)]
    field_simp
  -- near `τ`, `AE^ν − pE = E((p + t)/ν − p)` by the first-order condition
  have hev : staticPrivate ν A p =ᶠ[𝓝 τ]
      fun t => staticE ν A p t * ((p + t) / ν - p) := by
    filter_upwards [(continuous_const.add continuous_id).continuousAt.eventually
      (lt_mem_nhds hpτ)] with t ht
    have ht' : 0 < p + t := by simpa using ht
    have hs := staticE_pos hν0 hA ht'
    have hfoc := (eq_25_16 hν0 hν1 hA ht' hs).mpr rfl
    have hpow : staticE ν A p t ^ ν = staticE ν A p t ^ (ν - 1) * staticE ν A p t := by
      rw [Real.rpow_sub_one hs.ne']; field_simp
    simp only [staticPrivate, hpow]
    have : staticE ν A p t ^ (ν - 1) = (p + t) / (ν * A) := by
      rw [eq_div_iff (by positivity), ← hfoc]; ring
    rw [this]
    field_simp
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h2 : HasDerivAt (fun t => (p + t) / ν - p) (1 / ν) τ := by
    have := (((hasDerivAt_id τ).const_add p).div_const ν).sub_const p
    simpa using this
  convert hE.mul h2 using 1
  field_simp
  ring

/-- AKMM, p. 766: "the costs for the private economy of modestly raising the global carbon tax
above zero are negligible": the derivative of the private surplus at `τ = 0` is zero. -/
theorem static_private_deriv_zero (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) :
    HasDerivAt (staticPrivate ν A p) 0 0 := by
  have := static_private_hasDerivAt hν0 hν1 hA (τ := 0) (by linarith)
  simpa using this

/-- AKMM, (25.19), p. 767: a competitive equilibrium under an emission cap `Ē` with permits at
price `λ`: the firm's first-order condition, the cap, and `λ = 0` unless the cap binds. -/
def CapEquilibrium (ν A p Ebar E lam : ℝ) : Prop :=
  0 < E ∧ E ≤ Ebar ∧ 0 ≤ lam ∧ lam * (Ebar - E) = 0 ∧ ν * A * E ^ (ν - 1) = p + lam

/-- AKMM, p. 767: "If the quantity is higher than that of the laissez-faire equilibrium, the
restriction will not bind and `λ` will be zero." -/
theorem static_cap_nonbinding (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p)
    {Ebar E lam : ℝ} (hEbar : staticE ν A p 0 ≤ Ebar) :
    CapEquilibrium ν A p Ebar E lam ↔ E = staticE ν A p 0 ∧ lam = 0 := by
  have hE0 := staticE_pos hν0 hA (p := p) (τ := 0) (by linarith)
  constructor
  · rintro ⟨hE, hle, hlam, hcs, hfoc⟩
    have hlam0 : lam = 0 := by
      by_contra hne
      have hlampos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hne)
      have hEq : E = Ebar := by
        rcases mul_eq_zero.mp hcs with h | h
        · exact absurd h hne
        · linarith
      have hlt : E < staticE ν A p 0 :=
        (static_lt_staticE_iff hν0 hν1 hA (by linarith) hE).mpr (by rw [hfoc]; linarith)
      linarith
    subst hlam0
    exact ⟨(eq_25_16 hν0 hν1 hA (by linarith) hE).mp (by simpa using hfoc), rfl⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨hE0, hEbar, le_rfl, by ring, ?_⟩
    simpa using (eq_25_16 hν0 hν1 hA (τ := 0) (by linarith) hE0).mpr rfl

/-- AKMM, p. 767: "If it is lower than that, the restriction will bind and one reads off `λ`
from the firm's first-order condition": the unique equilibrium is `E = Ē`,
`λ = νAĒ^{ν−1} − p > 0`. -/
theorem static_cap_binding (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p)
    {Ebar E lam : ℝ} (hEbar0 : 0 < Ebar) (hEbar : Ebar < staticE ν A p 0) :
    CapEquilibrium ν A p Ebar E lam ↔ E = Ebar ∧ lam = ν * A * Ebar ^ (ν - 1) - p := by
  have hmp : p < ν * A * Ebar ^ (ν - 1) := by
    have := (static_lt_staticE_iff hν0 hν1 hA (τ := 0) (by linarith) hEbar0).mp hEbar
    linarith
  constructor
  · rintro ⟨hE, hle, hlam, hcs, hfoc⟩
    rcases mul_eq_zero.mp hcs with h | h
    · subst h
      have : staticE ν A p 0 = E :=
        ((eq_25_16 hν0 hν1 hA (by linarith) hE).mp (by simpa using hfoc)).symm
      linarith
    · have hEq : E = Ebar := by linarith
      subst hEq
      exact ⟨rfl, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hEbar0, le_rfl, by linarith, by ring, by ring⟩

/-- AKMM, (25.19), p. 767: with the cap set at the optimum `E*`, the equilibrium is unique, with
permit price `λ = 2γE* = τ`: prices and quantities are equivalent. -/
theorem eq_25_19 (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) {γ Es E lam : ℝ}
    (hγ : 0 < γ) (hEs : 0 < Es) (hfoc : ν * A * Es ^ (ν - 1) = p + 2 * γ * Es) :
    CapEquilibrium ν A p Es E lam ↔ E = Es ∧ lam = 2 * γ * Es := by
  rw [static_cap_binding hν0 hν1 hA hp hEs
    (static_laissez_faire_excess hν0 hν1 hA hp hγ hEs hfoc), hfoc]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- AKMM, p. 767: with the cap at the optimum, an equilibrium exists (so `CapEquilibrium` is not
vacuous). -/
theorem static_cap_exists (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) {γ : ℝ}
    (hγ : 0 < γ) : ∃ Es lam, CapEquilibrium ν A p Es Es lam := by
  obtain ⟨Es, hEs, hfoc⟩ := eq_25_18_exists hν0 hν1 hA hp hγ
  exact ⟨Es, 2 * γ * Es, (eq_25_19 hν0 hν1 hA hp hγ hEs hfoc).mpr ⟨rfl, rfl⟩⟩

/-- AKMM, p. 767, corrected: the two-firm planner's objective, including the coal cost `p`,
`AE₁^{ν₁} + AE₂^{ν₂} − p(E₁ + E₂) − γ(E₁ + E₂)²`. -/
noncomputable def staticW2 (ν₁ ν₂ A p γ E₁ E₂ : ℝ) : ℝ :=
  A * E₁ ^ ν₁ + A * E₂ ^ ν₂ - p * (E₁ + E₂) - γ * (E₁ + E₂) ^ 2

/-- AKMM, p. 767: a solution of the two first-order conditions
`ν_iAE_i^{ν_i−1} = p + 2γ(E₁ + E₂)` maximises the planner's objective over `E₁, E₂ ≥ 0`. -/
theorem static_two_optimal {ν₁ ν₂ γ E₁ E₂ F₁ F₂ : ℝ} (h₁0 : 0 < ν₁) (h₁1 : ν₁ < 1)
    (h₂0 : 0 < ν₂) (h₂1 : ν₂ < 1) (hA : 0 < A) (hγ : 0 ≤ γ) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (hf₁ : ν₁ * A * E₁ ^ (ν₁ - 1) = p + 2 * γ * (E₁ + E₂))
    (hf₂ : ν₂ * A * E₂ ^ (ν₂ - 1) = p + 2 * γ * (E₁ + E₂)) (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂) :
    staticW2 ν₁ ν₂ A p γ F₁ F₂ ≤ staticW2 ν₁ ν₂ A p γ E₁ E₂ := by
  have t₁ := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent h₁0.le h₁1.le hF₁ hE₁
  have t₂ := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent h₂0.le h₂1.le hF₂ hE₂
  unfold staticW2
  nlinarith [mul_le_mul_of_nonneg_left t₁ hA.le, mul_le_mul_of_nonneg_left t₂ hA.le,
    mul_nonneg hγ (sq_nonneg (F₁ + F₂ - E₁ - E₂))]

/-- AKMM, p. 767: "which solves uniquely for `{E₁*, E₂*}`": the optimum is unique. -/
theorem static_two_unique {ν₁ ν₂ γ E₁ E₂ F₁ F₂ : ℝ} (h₁0 : 0 < ν₁) (h₁1 : ν₁ < 1)
    (h₂0 : 0 < ν₂) (h₂1 : ν₂ < 1) (hA : 0 < A) (hγ : 0 ≤ γ) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (hf₁ : ν₁ * A * E₁ ^ (ν₁ - 1) = p + 2 * γ * (E₁ + E₂))
    (hf₂ : ν₂ * A * E₂ ^ (ν₂ - 1) = p + 2 * γ * (E₁ + E₂)) (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂)
    (hne : (F₁, F₂) ≠ (E₁, E₂)) :
    staticW2 ν₁ ν₂ A p γ F₁ F₂ < staticW2 ν₁ ν₂ A p γ E₁ E₂ := by
  have t₁ := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent h₁0.le h₁1.le hF₁ hE₁
  have t₂ := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent h₂0.le h₂1.le hF₂ hE₂
  have hor : F₁ ≠ E₁ ∨ F₂ ≠ E₂ := by
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    exact hne (by rw [h.1, h.2])
  unfold staticW2
  rcases hor with h | h
  · have s₁ := sust_rpow_lt_tangent h₁0 h₁1 hF₁ hE₁ h
    nlinarith [mul_lt_mul_of_pos_left s₁ hA, mul_le_mul_of_nonneg_left t₂ hA.le,
      mul_nonneg hγ (sq_nonneg (F₁ + F₂ - E₁ - E₂))]
  · have s₂ := sust_rpow_lt_tangent h₂0 h₂1 hF₂ hE₂ h
    nlinarith [mul_le_mul_of_nonneg_left t₁ hA.le, mul_lt_mul_of_pos_left s₂ hA,
      mul_nonneg hγ (sq_nonneg (F₁ + F₂ - E₁ - E₂))]

/-- `E(τ)` is continuous in `τ` on `τ > −p`. -/
theorem staticE_continuousOn (hν0 : 0 < ν) (hA : 0 < A) :
    ContinuousOn (staticE ν A p) (Set.Ioi (-p)) := by
  unfold staticE
  refine ContinuousOn.rpow_const ?_ fun x hx => Or.inl ?_
  · refine continuousOn_const.div (by fun_prop) fun x hx => ?_
    have : -p < x := hx
    linarith
  · have : -p < x := hx
    have : 0 < p + x := by linarith
    positivity

/-- AKMM, p. 767: the two-firm first-order conditions have a solution: the common marginal cost
`p + 2γX` with `X = E₁(2γX) + E₂(2γX)`, found by the intermediate value theorem. -/
theorem static_two_exists {ν₁ ν₂ γ : ℝ} (h₁0 : 0 < ν₁) (h₁1 : ν₁ < 1) (h₂0 : 0 < ν₂)
    (h₂1 : ν₂ < 1) (hA : 0 < A) (hp : 0 < p) (hγ : 0 ≤ γ) :
    ∃ E₁ E₂, 0 < E₁ ∧ 0 < E₂ ∧ ν₁ * A * E₁ ^ (ν₁ - 1) = p + 2 * γ * (E₁ + E₂) ∧
      ν₂ * A * E₂ ^ (ν₂ - 1) = p + 2 * γ * (E₁ + E₂) := by
  set D : ℝ → ℝ := fun X => staticE ν₁ A p (2 * γ * X) + staticE ν₂ A p (2 * γ * X)
  set g : ℝ → ℝ := fun X => X - D X
  set b := D 0
  have hb : 0 < b := add_pos (staticE_pos h₁0 hA (by simpa using hp))
    (staticE_pos h₂0 hA (by simpa using hp))
  have hcontD : ContinuousOn D (Set.Icc 0 b) := by
    have hmaps : Set.MapsTo (fun X => 2 * γ * X) (Set.Icc 0 b) (Set.Ioi (-p)) := by
      intro X hX
      have : 0 ≤ 2 * γ * X := mul_nonneg (by positivity) hX.1
      change -p < 2 * γ * X
      linarith
    exact ((staticE_continuousOn h₁0 hA).comp (by fun_prop) hmaps).add
      ((staticE_continuousOn h₂0 hA).comp (by fun_prop) hmaps)
  have hcont : ContinuousOn g (Set.Icc 0 b) := continuousOn_id.sub hcontD
  have hg0 : g 0 ≤ 0 := by simp only [g]; linarith
  have hgb : 0 ≤ g b := by
    simp only [g]
    -- `E_i(2γb) ≤ E_i(0)` since the tax is nonnegative
    have hmono : ∀ ν' : ℝ, 0 < ν' → ν' < 1 →
        staticE ν' A p (2 * γ * b) ≤ staticE ν' A p (2 * γ * 0) := by
      intro ν' h0 h1
      rcases (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * γ) hb.le).lt_or_eq with hlt | heq
      · exact (staticE_strictAnti h0 h1 hA (by simpa using hp) (by simpa using hlt)).le
      · rw [← heq]; simp
    have := add_le_add (hmono ν₁ h₁0 h₁1) (hmono ν₂ h₂0 h₂1)
    simp only [D, b] at this ⊢
    linarith
  obtain ⟨X, hX, hgX⟩ := intermediate_value_Icc hb.le hcont ⟨hg0, hgb⟩
  have hXD : X = D X := by simp only [g] at hgX; linarith
  have hτ : 0 < p + 2 * γ * X := by
    have : 0 ≤ 2 * γ * X := mul_nonneg (by positivity) hX.1
    linarith
  have hsum : staticE ν₁ A p (2 * γ * X) + staticE ν₂ A p (2 * γ * X) = X := hXD.symm
  refine ⟨staticE ν₁ A p (2 * γ * X), staticE ν₂ A p (2 * γ * X), staticE_pos h₁0 hA hτ,
    staticE_pos h₂0 hA hτ, ?_, ?_⟩
  · rw [hsum]
    exact (eq_25_16 h₁0 h₁1 hA hτ (staticE_pos h₁0 hA hτ)).mpr rfl
  · rw [hsum]
    exact (eq_25_16 h₂0 h₂1 hA hτ (staticE_pos h₂0 hA hτ)).mpr rfl

/-- AKMM, p. 767: the carbon tax `τ = 2γ(E₁* + E₂*)` implements the two-firm optimum, and both
firms face the same price, so `ν₁AE₁^{ν₁−1} = ν₂AE₂^{ν₂−1}`. -/
theorem static_two_pigou {ν₁ ν₂ γ E₁ E₂ : ℝ} (h₁0 : 0 < ν₁) (h₁1 : ν₁ < 1) (h₂0 : 0 < ν₂)
    (h₂1 : ν₂ < 1) (hA : 0 < A) (hp : 0 < p) (hγ : 0 ≤ γ) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (hf₁ : ν₁ * A * E₁ ^ (ν₁ - 1) = p + 2 * γ * (E₁ + E₂))
    (hf₂ : ν₂ * A * E₂ ^ (ν₂ - 1) = p + 2 * γ * (E₁ + E₂)) :
    staticE ν₁ A p (2 * γ * (E₁ + E₂)) = E₁ ∧ staticE ν₂ A p (2 * γ * (E₁ + E₂)) = E₂ ∧
      ν₁ * A * E₁ ^ (ν₁ - 1) = ν₂ * A * E₂ ^ (ν₂ - 1) := by
  have hτ : 0 < p + 2 * γ * (E₁ + E₂) := by positivity
  exact ⟨((eq_25_16 h₁0 h₁1 hA hτ hE₁).mp hf₁).symm, ((eq_25_16 h₂0 h₂1 hA hτ hE₂).mp hf₂).symm,
    by rw [hf₁, hf₂]⟩

/-- AKMM, p. 767: "a mere restriction for total use not to exceed `E₁* + E₂*` would also work (the
equilibrium price of emission rights would again equal the optimal tax)": with `γ > 0`, the
equilibrium under the aggregate cap is unique, it is the optimum, and `λ = 2γ(E₁* + E₂*)`. -/
theorem static_two_cap {ν₁ ν₂ γ E₁ E₂ F₁ F₂ lam : ℝ} (h₁0 : 0 < ν₁) (h₁1 : ν₁ < 1)
    (h₂0 : 0 < ν₂) (h₂1 : ν₂ < 1) (hA : 0 < A) (hp : 0 < p) (hγ : 0 < γ) (hE₁ : 0 < E₁)
    (hE₂ : 0 < E₂) (hf₁ : ν₁ * A * E₁ ^ (ν₁ - 1) = p + 2 * γ * (E₁ + E₂))
    (hf₂ : ν₂ * A * E₂ ^ (ν₂ - 1) = p + 2 * γ * (E₁ + E₂)) (hF₁ : 0 < F₁) (hF₂ : 0 < F₂)
    (hcap : F₁ + F₂ ≤ E₁ + E₂) (hlam : 0 ≤ lam) (hcs : lam * (E₁ + E₂ - (F₁ + F₂)) = 0)
    (hg₁ : ν₁ * A * F₁ ^ (ν₁ - 1) = p + lam) (hg₂ : ν₂ * A * F₂ ^ (ν₂ - 1) = p + lam) :
    F₁ = E₁ ∧ F₂ = E₂ ∧ lam = 2 * γ * (E₁ + E₂) := by
  set τ := 2 * γ * (E₁ + E₂)
  have hτpos : 0 < τ := by positivity
  have hpl : 0 < p + lam := by linarith
  have hpτ : 0 < p + τ := by linarith
  have hF₁e := (eq_25_16 h₁0 h₁1 hA hpl hF₁).mp hg₁
  have hF₂e := (eq_25_16 h₂0 h₂1 hA hpl hF₂).mp hg₂
  have hE₁e := (eq_25_16 h₁0 h₁1 hA hpτ hE₁).mp hf₁
  have hE₂e := (eq_25_16 h₂0 h₂1 hA hpτ hE₂).mp hf₂
  -- `λ = τ`: if `λ < τ` both firms buy more than at the optimum, breaking the cap; if `λ > τ`
  -- both buy less, so the cap is slack and `λ = 0 < τ`.
  have hlt : ¬ lam < τ := by
    intro h
    have a₁ := staticE_strictAnti h₁0 h₁1 hA hpl h
    have a₂ := staticE_strictAnti h₂0 h₂1 hA hpl h
    rw [← hF₁e, ← hE₁e] at a₁
    rw [← hF₂e, ← hE₂e] at a₂
    linarith
  have hgt : ¬ τ < lam := by
    intro h
    have a₁ := staticE_strictAnti h₁0 h₁1 hA hpτ h
    have a₂ := staticE_strictAnti h₂0 h₂1 hA hpτ h
    rw [← hF₁e, ← hE₁e] at a₁
    rw [← hF₂e, ← hE₂e] at a₂
    have hslack : 0 < E₁ + E₂ - (F₁ + F₂) := by linarith
    rcases mul_eq_zero.mp hcs with h0 | h0
    · linarith
    · linarith
  have heq : lam = τ := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
  subst heq
  exact ⟨by rw [hF₁e, hE₁e], by rw [hF₂e, hE₂e], rfl⟩

end AKMM.Sustainability
