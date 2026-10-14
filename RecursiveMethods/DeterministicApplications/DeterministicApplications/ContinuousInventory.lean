/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# The inventory problem in continuous time

SLP §5.15, pp. 122–123: demand is a flow of `a > 0` units per unit time, the interest rate is
`r > 0`, an order of `y` costs `c₀ + c₁y`, and the price is `p`. Selling a stock that lasts `τ`
units of time earns `S(τ) = ∫₀^τ e^{−rt}ap dt = ap(1 − e^{−rτ})/r` (`Srev_integral`), and
`S(τ + s) = S(τ) + e^{−rτ}S(s)` (`Srev_add`).

* **Exercise 5.15a** (`ex_5_15a`): with `G(τ) = (1 + e^{−rτ} + e^{−2rτ} + …)(S(τ) − c₀ − c₁aτ)`
  (`Gcyc_geometric`), `Y* = max{0, sup_{τ > 0} G(τ)}` is well defined and finite (`G ≤ ap/r`), and
  when `Y* > 0` the supremum is attained, at a unique `τ*` (`Gcyc_argmax_unique`: the numerator
  of `G'` is strictly increasing, so `G` rises then falls).
* **Exercise 5.15b**: `w(A) = S(A/a) + e^{−rA/a}Y*` satisfies the functional equation
  (`ex_5_15b`): no plan beats it (`Vval_le`: ordering early only brings the fixed cost forward,
  and each cycle is worth at most `Y*`), and when `Y* > 0` the policy "order `aτ*` units after
  `A/a` units of time" attains it (`Vval_attain`). That policy is the unique optimal one
  (`ex_5_15b_unique`).
-/

open Real Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

variable {a p r c₀ c₁ : ℝ}

/-- `S(τ) = ap(1 − e^{−rτ})/r`. -/
noncomputable def Srev (a p r τ : ℝ) : ℝ := a * p * (1 - exp (-r * τ)) / r

/-- The hypotheses of SLP §5.15. -/
structure CTHyp (a p r c₀ c₁ : ℝ) : Prop where
  a_pos : 0 < a
  p_pos : 0 < p
  r_pos : 0 < r
  c₀_pos : 0 < c₀
  c₁_pos : 0 < c₁

/-- `S(τ) = ∫₀^τ e^{−rt}ap dt`. -/
theorem Srev_integral (h : CTHyp a p r c₀ c₁) (τ : ℝ) :
    Srev a p r τ = ∫ t in (0 : ℝ)..τ, exp (-r * t) * (a * p) := by
  have hr := h.r_pos.ne'
  have hd : ∀ t ∈ uIcc (0 : ℝ) τ, HasDerivAt (fun t => -(a * p) * exp (-r * t) / r)
      (exp (-r * t) * (a * p)) t := fun t _ => by
    have := ((((hasDerivAt_id' t).const_mul (-r)).exp).const_mul (-(a * p))).div_const r
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => exp (-r * t) * (a * p)).intervalIntegrable 0 τ)]
  simp only [Srev, mul_zero, exp_zero]
  field_simp
  ring

/-- `S(τ + s) = S(τ) + e^{−rτ}S(s)`. -/
theorem Srev_add (h : CTHyp a p r c₀ c₁) (τ s : ℝ) :
    Srev a p r (τ + s) = Srev a p r τ + exp (-r * τ) * Srev a p r s := by
  have hr := h.r_pos.ne'
  simp only [Srev]
  rw [show -r * (τ + s) = -r * τ + -r * s by ring, exp_add]
  field_simp
  ring

theorem exp_neg_lt_one (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) : exp (-r * σ) < 1 :=
  exp_lt_one_iff.2 (by nlinarith [h.r_pos])

/-- The value of one cycle, per unit of discounting: `G(τ) = (S(τ) − c₀ − c₁aτ)/(1 − e^{−rτ})`. -/
noncomputable def Gcyc (a p r c₀ c₁ σ : ℝ) : ℝ :=
  (Srev a p r σ - c₀ - c₁ * a * σ) / (1 - exp (-r * σ))

/-- `G(τ) = (1 + e^{−rτ} + e^{−2rτ} + …)(S(τ) − c₀ − c₁aτ)`: repeating the cycle forever. -/
theorem Gcyc_geometric (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun k : ℕ => exp (-r * σ) ^ k * (Srev a p r σ - c₀ - c₁ * a * σ))
      (Gcyc a p r c₀ c₁ σ) := by
  have := (hasSum_geometric_of_lt_one (exp_pos _).le (exp_neg_lt_one h hσ)).mul_right
    (Srev a p r σ - c₀ - c₁ * a * σ)
  convert this using 1
  simp only [Gcyc, div_eq_mul_inv]
  ring

/-- `G(τ) = ap/r − (c₀ + c₁aτ)/(1 − e^{−rτ})`. -/
theorem Gcyc_eq (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) :
    Gcyc a p r c₀ c₁ σ = a * p / r - (c₀ + c₁ * a * σ) / (1 - exp (-r * σ)) := by
  have hlt := exp_neg_lt_one h hσ
  have hr := h.r_pos.ne'
  simp only [Gcyc, Srev]
  generalize exp (-r * σ) = e at hlt ⊢
  have h1 : 1 - e ≠ 0 := by linarith
  field_simp
  ring

theorem Gcyc_le (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) : Gcyc a p r c₀ c₁ σ ≤ a * p / r := by
  rw [Gcyc_eq h hσ]
  have hc : 0 < c₀ + c₁ * a * σ := by
    have := mul_pos (mul_pos h.c₁_pos h.a_pos) hσ; linarith [h.c₀_pos]
  have : 0 < (c₀ + c₁ * a * σ) / (1 - exp (-r * σ)) :=
    div_pos hc (by linarith [exp_neg_lt_one h hσ])
  linarith

/-- `Y* = max{0, sup_{τ > 0} G(τ)}`. -/
noncomputable def Ystar (a p r c₀ c₁ : ℝ) : ℝ := max 0 (sSup (Gcyc a p r c₀ c₁ '' Ioi 0))

theorem bddAbove_Gcyc (h : CTHyp a p r c₀ c₁) : BddAbove (Gcyc a p r c₀ c₁ '' Ioi 0) :=
  ⟨a * p / r, by rintro _ ⟨σ, hσ, rfl⟩; exact Gcyc_le h hσ⟩

theorem Gcyc_le_Ystar (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) :
    Gcyc a p r c₀ c₁ σ ≤ Ystar a p r c₀ c₁ :=
  (le_csSup (bddAbove_Gcyc h) ⟨σ, hσ, rfl⟩).trans (le_max_right _ _)

theorem continuousOn_Gcyc (h : CTHyp a p r c₀ c₁) : ContinuousOn (Gcyc a p r c₀ c₁) (Ioi 0) := by
  refine ContinuousOn.div (by unfold Srev; fun_prop) (by fun_prop) fun σ hσ => ?_
  linarith [exp_neg_lt_one h hσ]

/-- **Exercise 5.15a.** `Y*` is well defined and finite, `0 ≤ Y* ≤ ap/r`, and if `Y* > 0` the
supremum is attained at some `τ* > 0`. -/
theorem ex_5_15a (h : CTHyp a p r c₀ c₁) :
    BddAbove (Gcyc a p r c₀ c₁ '' Ioi 0) ∧ 0 ≤ Ystar a p r c₀ c₁ ∧
      Ystar a p r c₀ c₁ ≤ a * p / r ∧
      (0 < Ystar a p r c₀ c₁ → ∃ τ > 0, Gcyc a p r c₀ c₁ τ = Ystar a p r c₀ c₁) := by
  have hap : 0 < a * p / r := div_pos (mul_pos h.a_pos h.p_pos) h.r_pos
  have hne : (Gcyc a p r c₀ c₁ '' Ioi 0).Nonempty := ⟨_, 1, by norm_num, rfl⟩
  have hub : ∀ v ∈ Gcyc a p r c₀ c₁ '' Ioi 0, v ≤ a * p / r := by
    rintro _ ⟨σ, hσ, rfl⟩; exact Gcyc_le h hσ
  refine ⟨bddAbove_Gcyc h, le_max_left _ _, max_le hap.le (csSup_le hne hub), fun hY => ?_⟩
  -- some cycle is profitable
  have hS : 0 < sSup (Gcyc a p r c₀ c₁ '' Ioi 0) := by
    by_contra hle; push Not at hle
    have : Ystar a p r c₀ c₁ = 0 := max_eq_left hle
    linarith
  obtain ⟨_, ⟨σ₁, hσ₁, rfl⟩, hG₁⟩ := exists_lt_of_lt_csSup hne hS
  -- `G < 0` near `0` and far out
  set ε := min σ₁ (c₀ / (2 * a * p))
  have hε : 0 < ε := lt_min hσ₁ (div_pos h.c₀_pos (by nlinarith [h.a_pos, h.p_pos]))
  have hsmall : ∀ σ, 0 < σ → σ ≤ ε → Gcyc a p r c₀ c₁ σ < 0 := fun σ hσ hσε => by
    rw [Gcyc_eq h hσ]
    have hd : 0 < 1 - exp (-r * σ) := by linarith [exp_neg_lt_one h hσ]
    have hd' : 1 - exp (-r * σ) ≤ r * σ := by linarith [add_one_le_exp (-r * σ)]
    have hσc : σ ≤ c₀ / (2 * a * p) := hσε.trans (min_le_right _ _)
    rw [le_div_iff₀ (by nlinarith [h.a_pos, h.p_pos])] at hσc
    have hap0 : 0 < a * p := mul_pos h.a_pos h.p_pos
    have h1 : a * p * (1 - exp (-r * σ)) ≤ a * p * (r * σ) := mul_le_mul_of_nonneg_left hd' hap0.le
    have h2 : a * p * (r * σ) ≤ r * c₀ / 2 := by nlinarith [h.r_pos]
    have h3 : 0 ≤ c₁ * a * σ := (mul_pos (mul_pos h.c₁_pos h.a_pos) hσ).le
    have : a * p / r < (c₀ + c₁ * a * σ) / (1 - exp (-r * σ)) := by
      rw [div_lt_div_iff₀ h.r_pos hd]
      nlinarith [h.c₀_pos, h.r_pos]
    linarith
  set M := max σ₁ (p / (r * c₁) + 1)
  have hlarge : ∀ σ, M < σ → Gcyc a p r c₀ c₁ σ < 0 := fun σ hσ => by
    have hσ0 : 0 < σ := lt_of_le_of_lt (le_max_left _ _ |>.trans' hσ₁.le) hσ
    rw [Gcyc_eq h hσ0]
    have hd : 0 < 1 - exp (-r * σ) := by linarith [exp_neg_lt_one h hσ0]
    have hd1 : 1 - exp (-r * σ) ≤ 1 := by linarith [exp_pos (-r * σ)]
    have hnum : 0 < c₀ + c₁ * a * σ := by
      have := mul_pos (mul_pos h.c₁_pos h.a_pos) hσ0; linarith [h.c₀_pos]
    have h1 : c₀ + c₁ * a * σ ≤ (c₀ + c₁ * a * σ) / (1 - exp (-r * σ)) := by
      rw [le_div_iff₀ hd]; nlinarith
    have hσM : p / (r * c₁) < σ := by
      have := (le_max_right σ₁ (p / (r * c₁) + 1)).trans_lt hσ; linarith
    rw [div_lt_iff₀ (mul_pos h.r_pos h.c₁_pos)] at hσM
    have : a * p / r < c₁ * a * σ := by
      rw [div_lt_iff₀ h.r_pos]; nlinarith [h.a_pos]
    linarith [h.c₀_pos]
  -- maximize over the compact `[ε, M]`
  have hεM : ε ≤ M := (min_le_left _ _).trans (le_max_left _ _)
  obtain ⟨τ, hτ, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hεM)
    ((continuousOn_Gcyc h).mono fun σ hσ => lt_of_lt_of_le hε hσ.1)
  have hτ0 : 0 < τ := lt_of_lt_of_le hε hτ.1
  have hG₁τ : Gcyc a p r c₀ c₁ σ₁ ≤ Gcyc a p r c₀ c₁ τ :=
    hmax ⟨min_le_left _ _, le_max_left _ _⟩
  have hglobal : ∀ σ, 0 < σ → Gcyc a p r c₀ c₁ σ ≤ Gcyc a p r c₀ c₁ τ := fun σ hσ => by
    by_cases h1 : σ ≤ ε
    · linarith [hsmall σ hσ h1]
    by_cases h2 : M < σ
    · linarith [hlarge σ h2]
    push Not at h1 h2
    exact hmax ⟨h1.le, h2⟩
  have hsup : sSup (Gcyc a p r c₀ c₁ '' Ioi 0) = Gcyc a p r c₀ c₁ τ :=
    IsGreatest.csSup_eq ⟨⟨τ, hτ0, rfl⟩, by rintro _ ⟨σ, hσ, rfl⟩; exact hglobal σ hσ⟩
  refine ⟨τ, hτ0, ?_⟩
  rw [Ystar, hsup, max_eq_right (by linarith)]

/-- The numerator of `h'`, where `h(σ) = (c₀ + c₁aσ)/(1 − e^{−rσ})` and `G = ap/r − h`. -/
noncomputable def Ncyc (a r c₀ c₁ σ : ℝ) : ℝ :=
  c₁ * a * (1 - exp (-r * σ)) - r * exp (-r * σ) * (c₀ + c₁ * a * σ)

theorem Ncyc_strictMono (h : CTHyp a p r c₀ c₁) : StrictMonoOn (Ncyc a r c₀ c₁) (Ici 0) := by
  have hd : ∀ σ, HasDerivAt (Ncyc a r c₀ c₁)
      (r ^ 2 * exp (-r * σ) * (c₀ + c₁ * a * σ)) σ := fun σ => by
    have he : HasDerivAt (fun s => exp (-r * s)) (exp (-r * σ) * (-r)) σ := by
      simpa using ((hasDerivAt_id' σ).const_mul (-r)).exp
    have := ((he.const_mul (c₁ * a)).const_sub (c₁ * a)).sub
      ((he.const_mul r).mul (((hasDerivAt_id' σ).const_mul (c₁ * a)).const_add c₀))
    refine (this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv (by ring)
    simp only [Ncyc, Pi.sub_apply, Pi.mul_apply]
    ring
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun σ _ => (hd σ).continuousAt.continuousWithinAt) fun σ hσ => ?_
  rw [interior_Ici] at hσ
  rw [(hd σ).deriv]
  have hσ' : (0 : ℝ) < σ := hσ
  have h1 := exp_pos (-r * σ)
  have h2 : 0 < c₀ + c₁ * a * σ := by
    have := mul_pos (mul_pos h.c₁_pos h.a_pos) hσ'; linarith [h.c₀_pos]
  have h3 := pow_pos h.r_pos 2
  positivity

theorem hasDerivAt_hcyc (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun s => (c₀ + c₁ * a * s) / (1 - exp (-r * s)))
      (Ncyc a r c₀ c₁ σ / (1 - exp (-r * σ)) ^ 2) σ := by
  have hd : 1 - exp (-r * σ) ≠ 0 := by linarith [exp_neg_lt_one h hσ]
  have he := ((hasDerivAt_id' σ).const_mul (-r)).exp
  have := (((hasDerivAt_id' σ).const_mul (c₁ * a)).const_add c₀).div (he.const_sub 1) hd
  convert this using 1
  simp only [Ncyc]
  ring

/-- **Exercise 5.15a.** `G` has at most one maximizer on `(0, ∞)`: at a maximizer `h' = 0`, so the
strictly increasing `N` vanishes there. -/
theorem Gcyc_argmax_unique (h : CTHyp a p r c₀ c₁) {τ₁ τ₂ : ℝ} (h₁ : 0 < τ₁) (h₂ : 0 < τ₂)
    (hm₁ : ∀ σ, 0 < σ → Gcyc a p r c₀ c₁ σ ≤ Gcyc a p r c₀ c₁ τ₁)
    (hm₂ : ∀ σ, 0 < σ → Gcyc a p r c₀ c₁ σ ≤ Gcyc a p r c₀ c₁ τ₂) : τ₁ = τ₂ := by
  -- at a maximizer of `G`, `h` has a local minimum, so `N = 0`
  have hzero : ∀ τ, 0 < τ → (∀ σ, 0 < σ → Gcyc a p r c₀ c₁ σ ≤ Gcyc a p r c₀ c₁ τ) →
      Ncyc a r c₀ c₁ τ = 0 := fun τ hτ hm => by
    have hloc : IsLocalMin (fun s => (c₀ + c₁ * a * s) / (1 - exp (-r * s))) τ := by
      filter_upwards [Ioi_mem_nhds hτ] with s hs
      have := hm s hs
      rw [Gcyc_eq h hs, Gcyc_eq h hτ] at this
      linarith
    have := hloc.hasDerivAt_eq_zero (hasDerivAt_hcyc h hτ)
    have hd : (1 - exp (-r * τ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [exp_neg_lt_one h hτ])
    exact (div_eq_zero_iff.1 this).resolve_right hd
  have e₁ := hzero τ₁ h₁ hm₁
  have e₂ := hzero τ₂ h₂ hm₂
  exact (Ncyc_strictMono h).injOn (mem_Ici.2 h₁.le) (mem_Ici.2 h₂.le) (e₁.trans e₂.symm)

/-! ### Exercise 5.15b -/

/-- `w(A) = S(A/a) + e^{−rA/a}Y*`. -/
noncomputable def wCT (a p r c₀ c₁ A : ℝ) : ℝ :=
  Srev a p r (A / a) + exp (-r * (A / a)) * Ystar a p r c₀ c₁

/-- The value of ordering `y` at time `τ`, starting from stock `A`. -/
noncomputable def Vval (a p r c₀ c₁ A τ y : ℝ) : ℝ :=
  Srev a p r (min τ (A / a)) +
    exp (-r * τ) * (wCT a p r c₀ c₁ (max (A - a * τ) 0 + y) - c₀ - c₁ * y)

/-- A cycle of length `σ` followed by the continuation is worth at most `Y*`. -/
theorem cycle_le (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) :
    Srev a p r σ - c₀ - c₁ * a * σ + exp (-r * σ) * Ystar a p r c₀ c₁ ≤ Ystar a p r c₀ c₁ := by
  have hd : 0 < 1 - exp (-r * σ) := by linarith [exp_neg_lt_one h hσ]
  have := Gcyc_le_Ystar h hσ
  rw [Gcyc, div_le_iff₀ hd] at this
  linarith

/-- No plan beats `w(A)`. -/
theorem Vval_le (h : CTHyp a p r c₀ c₁) {A τ y : ℝ} (hy : 0 < y) :
    Vval a p r c₀ c₁ A τ y ≤ wCT a p r c₀ c₁ A := by
  have ha := h.a_pos
  have hY := (ex_5_15a h).2.1
  have hσ : 0 < y / a := div_pos hy ha
  have hcyc := cycle_le h hσ
  rcases le_total τ (A / a) with hτA | hτA
  · -- ordering before the stock runs out only brings the fixed cost forward
    have hx : 0 ≤ A - a * τ := by rw [le_div_iff₀ ha] at hτA; linarith
    have e1 : (A - a * τ + y) / a = (A / a - τ) + y / a := by field_simp
    have hV : Vval a p r c₀ c₁ A τ y = Srev a p r (A / a) +
        exp (-r * (A / a)) * (Srev a p r (y / a) + exp (-r * (y / a)) * Ystar a p r c₀ c₁) -
          exp (-r * τ) * (c₀ + c₁ * y) := by
      simp only [Vval, wCT, min_eq_left hτA, max_eq_left hx, e1]
      rw [Srev_add h (A / a - τ), show A / a = τ + (A / a - τ) by ring, Srev_add h τ]
      rw [show τ + (A / a - τ) = A / a by ring]
      rw [show -r * (A / a - τ + y / a) = -r * (A / a - τ) + -r * (y / a) by ring, exp_add,
        show -r * (A / a) = -r * τ + -r * (A / a - τ) by ring, exp_add]
      ring
    have hexp : exp (-r * (A / a)) ≤ exp (-r * τ) :=
      exp_le_exp.2 (by nlinarith [h.r_pos])
    have hcost : 0 < c₀ + c₁ * y := by nlinarith [h.c₀_pos, h.c₁_pos]
    have hcy : c₁ * y = c₁ * a * (y / a) := by field_simp
    rw [hV, wCT]
    have h1 := mul_le_mul_of_nonneg_left hcyc (exp_pos (-r * (A / a))).le
    have h2 := mul_le_mul_of_nonneg_right hexp hcost.le
    have h3 : exp (-r * (A / a)) * (c₀ + c₁ * y) =
        exp (-r * (A / a)) * (c₀ + c₁ * a * (y / a)) := by rw [hcy]
    linarith
  · -- waiting past `A/a` only delays the next cycle
    have hx : A - a * τ ≤ 0 := by rw [div_le_iff₀ ha] at hτA; linarith
    have hV : Vval a p r c₀ c₁ A τ y = Srev a p r (A / a) + exp (-r * τ) *
        (Srev a p r (y / a) - c₀ - c₁ * a * (y / a) + exp (-r * (y / a)) * Ystar a p r c₀ c₁) := by
      simp only [Vval, wCT, min_eq_right hτA, max_eq_right hx, zero_add]
      have hcy : c₁ * y = c₁ * a * (y / a) := by field_simp
      rw [hcy]; ring
    have hexp : exp (-r * τ) ≤ exp (-r * (A / a)) := exp_le_exp.2 (by nlinarith [h.r_pos])
    rw [hV, wCT]
    have := mul_le_mul_of_nonneg_left hcyc (exp_pos (-r * τ)).le
    have := mul_le_mul_of_nonneg_right hexp hY
    linarith

/-- When `Y* > 0`, ordering `aτ*` units after `A/a` units of time attains `w(A)`. -/
theorem Vval_attain (h : CTHyp a p r c₀ c₁) {A τs : ℝ} (hτs : 0 < τs)
    (hG : Gcyc a p r c₀ c₁ τs = Ystar a p r c₀ c₁) :
    Vval a p r c₀ c₁ A (A / a) (a * τs) = wCT a p r c₀ c₁ A := by
  have ha := h.a_pos
  have hd : 0 < 1 - exp (-r * τs) := by linarith [exp_neg_lt_one h hτs]
  have hx : A - a * (A / a) = 0 := by field_simp; ring
  have hcyc : Srev a p r τs - c₀ - c₁ * a * τs = Ystar a p r c₀ c₁ * (1 - exp (-r * τs)) := by
    have := hG
    rw [Gcyc, div_eq_iff hd.ne'] at this
    exact this
  simp only [Vval, wCT, min_self, hx, max_self, zero_add]
  rw [show a * τs / a = τs by field_simp]
  have e : Srev a p r τs + exp (-r * τs) * Ystar a p r c₀ c₁ - c₀ - c₁ * (a * τs) =
      Ystar a p r c₀ c₁ := by linarith
  rw [e]

/-- **Exercise 5.15b.** `w` satisfies the functional equation:
`w(A) = max{S(A/a), sup_{τ ≥ 0, y > 0} V(A, τ, y)}`. -/
theorem ex_5_15b (h : CTHyp a p r c₀ c₁) {A : ℝ} (hA : 0 ≤ A) :
    wCT a p r c₀ c₁ A = max (Srev a p r (A / a))
      (sSup {v | ∃ τ y, 0 ≤ τ ∧ 0 < y ∧ v = Vval a p r c₀ c₁ A τ y}) := by
  have hY := (ex_5_15a h).2.1
  have hne : {v | ∃ τ y, 0 ≤ τ ∧ 0 < y ∧ v = Vval a p r c₀ c₁ A τ y}.Nonempty :=
    ⟨_, 0, 1, le_rfl, one_pos, rfl⟩
  have hub : ∀ v ∈ {v | ∃ τ y, 0 ≤ τ ∧ 0 < y ∧ v = Vval a p r c₀ c₁ A τ y},
      v ≤ wCT a p r c₀ c₁ A := by
    rintro _ ⟨τ, y, hτ, hy, rfl⟩
    exact Vval_le h hy
  have hS : Srev a p r (A / a) ≤ wCT a p r c₀ c₁ A := by
    have := mul_nonneg (exp_pos (-r * (A / a))).le hY
    simp only [wCT]; linarith
  refine le_antisymm ?_ (max_le hS (csSup_le hne hub))
  rcases eq_or_lt_of_le hY with hY0 | hYpos
  · -- `Y* = 0`: never ordering is optimal
    refine le_trans (le_of_eq ?_) (le_max_left _ _)
    simp only [wCT, ← hY0, mul_zero, add_zero]
  · obtain ⟨τs, hτs, hG⟩ := (ex_5_15a h).2.2.2 hYpos
    refine le_trans ?_ (le_max_right _ _)
    refine le_csSup ⟨_, hub⟩ ⟨A / a, a * τs, div_nonneg hA h.a_pos.le,
      mul_pos h.a_pos hτs, ?_⟩
    rw [Vval_attain h hτs hG]

/-- **Exercise 5.15b.** If `Y* > 0`, the unique optimal policy is to order `aτ*` units when the
stock runs out, after `A/a` units of time; not ordering is strictly worse. -/
theorem ex_5_15b_unique (h : CTHyp a p r c₀ c₁) (hYpos : 0 < Ystar a p r c₀ c₁) {A τs : ℝ}
    (hτs : 0 < τs) (hG : Gcyc a p r c₀ c₁ τs = Ystar a p r c₀ c₁) :
    Srev a p r (A / a) < wCT a p r c₀ c₁ A ∧
      ∀ τ y, 0 ≤ τ → 0 < y → Vval a p r c₀ c₁ A τ y = wCT a p r c₀ c₁ A →
        τ = A / a ∧ y = a * τs := by
  have ha := h.a_pos
  refine ⟨by simp only [wCT]; nlinarith [exp_pos (-r * (A / a))], fun τ y hτ hy heq => ?_⟩
  have hσ : 0 < y / a := div_pos hy ha
  have hcyc := cycle_le h hσ
  -- `τ < A/a` loses the earlier fixed cost
  have hτge : A / a ≤ τ := by
    by_contra hlt
    push Not at hlt
    have hx : 0 ≤ A - a * τ := by rw [lt_div_iff₀ ha] at hlt; linarith
    have e1 : (A - a * τ + y) / a = (A / a - τ) + y / a := by field_simp
    have hV : Vval a p r c₀ c₁ A τ y = Srev a p r (A / a) +
        exp (-r * (A / a)) * (Srev a p r (y / a) + exp (-r * (y / a)) * Ystar a p r c₀ c₁) -
          exp (-r * τ) * (c₀ + c₁ * y) := by
      simp only [Vval, wCT, min_eq_left hlt.le, max_eq_left hx, e1]
      rw [Srev_add h (A / a - τ), show A / a = τ + (A / a - τ) by ring, Srev_add h τ]
      rw [show τ + (A / a - τ) = A / a by ring]
      rw [show -r * (A / a - τ + y / a) = -r * (A / a - τ) + -r * (y / a) by ring, exp_add,
        show -r * (A / a) = -r * τ + -r * (A / a - τ) by ring, exp_add]
      ring
    have hexp : exp (-r * (A / a)) < exp (-r * τ) := exp_lt_exp.2 (by nlinarith [h.r_pos])
    have hcost : 0 < c₀ + c₁ * y := by nlinarith [h.c₀_pos, h.c₁_pos]
    have hcy : c₁ * y = c₁ * a * (y / a) := by field_simp
    rw [hV, wCT] at heq
    have h1 := mul_le_mul_of_nonneg_left hcyc (exp_pos (-r * (A / a))).le
    have h2 := mul_lt_mul_of_pos_right hexp hcost
    have h3 : exp (-r * (A / a)) * (c₀ + c₁ * y) =
        exp (-r * (A / a)) * (c₀ + c₁ * a * (y / a)) := by rw [hcy]
    linarith
  have hx : A - a * τ ≤ 0 := by rw [div_le_iff₀ ha] at hτge; linarith
  have hV : Vval a p r c₀ c₁ A τ y = Srev a p r (A / a) + exp (-r * τ) *
      (Srev a p r (y / a) - c₀ - c₁ * a * (y / a) + exp (-r * (y / a)) * Ystar a p r c₀ c₁) := by
    simp only [Vval, wCT, min_eq_right hτge, max_eq_right hx, zero_add]
    have hcy : c₁ * y = c₁ * a * (y / a) := by field_simp
    rw [hcy]; ring
  rw [hV, wCT] at heq
  -- waiting past `A/a` loses discounting on `Y* > 0`
  have hτeq : τ = A / a := by
    by_contra hne
    have hlt : A / a < τ := lt_of_le_of_ne hτge (Ne.symm hne)
    have hexp : exp (-r * τ) < exp (-r * (A / a)) := exp_lt_exp.2 (by nlinarith [h.r_pos])
    have := mul_le_mul_of_nonneg_left hcyc (exp_pos (-r * τ)).le
    have := mul_lt_mul_of_pos_right hexp hYpos
    linarith
  refine ⟨hτeq, ?_⟩
  -- the cycle must be optimal: `G(y/a) = Y*`, so `y/a = τ*`
  rw [hτeq] at heq
  have hcyc_eq : Srev a p r (y / a) - c₀ - c₁ * a * (y / a) +
      exp (-r * (y / a)) * Ystar a p r c₀ c₁ = Ystar a p r c₀ c₁ := by
    have := exp_pos (-r * (A / a))
    have := mul_left_cancel₀ this.ne' (show exp (-r * (A / a)) * (Srev a p r (y / a) - c₀ -
      c₁ * a * (y / a) + exp (-r * (y / a)) * Ystar a p r c₀ c₁) =
        exp (-r * (A / a)) * Ystar a p r c₀ c₁ by linarith)
    exact this
  have hGy : Gcyc a p r c₀ c₁ (y / a) = Ystar a p r c₀ c₁ := by
    have hd : 1 - exp (-r * (y / a)) ≠ 0 := by linarith [exp_neg_lt_one h hσ]
    rw [Gcyc, div_eq_iff hd]
    linarith
  have hm : ∀ τ', ∀ σ, 0 < σ → Gcyc a p r c₀ c₁ τ' = Ystar a p r c₀ c₁ →
      Gcyc a p r c₀ c₁ σ ≤ Gcyc a p r c₀ c₁ τ' := fun τ' σ hσ' he => by
    rw [he]; exact Gcyc_le_Ystar h hσ'
  have := Gcyc_argmax_unique h hσ hτs (fun σ hσ' => hm _ σ hσ' hGy) (fun σ hσ' => hm _ σ hσ' hG)
  rw [div_eq_iff ha.ne'] at this
  linarith

end StokeyLucasPrescott.DeterministicApplications
