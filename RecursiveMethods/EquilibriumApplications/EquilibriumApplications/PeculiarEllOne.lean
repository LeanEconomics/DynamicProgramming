/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.PeculiarModel

/-!
# A peculiar example (§16.6): the commodity space `ℓ₁` (Exercise 16.6(d))

SLP §16.6, p. 495. The same economy as in `PeculiarModel`, but with commodity space
`ℓ₁` (`pecL1`): `X = ℓ₁⁺` (`pecX1`), `u` as before (`pecU1`), `Y = {y ∈ ℓ₁ : y_t ≤ 2^{−(t+1)}}`
(`pecY1`), `x* = y* = (½, ¼, …) ∈ ℓ₁` (`pecStar1`). Time starts at `t = 0`.

* **Exercise 16.6(d), first part** (`ex_16_6d_interior`): `Y` has empty interior in `ℓ₁`. Since
  `ℓ₁` is also infinite dimensional (`pecL1_not_finiteDimensional`), Assumption 15.5 fails
  (`ex_16_6d_not_assumption15_5`), so Theorem 15.4 does not apply.
* **Exercise 16.6(d), second part** (`ex_16_6d_competitiveEq`): for every `c > 0`, `(x*, y*, p)`
  with `p = (c, c, …) ∈ ℓ∞ = ℓ₁*`, i.e. the price system `φ(x) = c Σ_t x_t` (`pecPrice1`), is a
  competitive equilibrium. (E2) is the manual's argument: `g(z) = z + exp(1 − z) − 2 ≥ 0` gives
  `x_t ≥ (2 − e) w_t + e · 2^{−(t+1)}[1 − exp(−x_t 2^{t+1})]`, so
  `Σ_t x_t ≥ (2 − e) + e u(x) > (2 − e) + e u(x*) = 1 = Σ_t x*_t` whenever `u(x) > u(x*)`
  (`pec_ell1_sum_ge`).

So the equilibrium exists in `ℓ₁` although Theorem 15.4 cannot produce it, while in `ℓ∞`
Theorem 15.4 applies but no equilibrium exists (`pec_no_competitiveEq`).

**Corrections.** None of substance: the manual's proof of (d) is correct (its `B(y, 5)` and
`5/4`, `5/2` are a scanning artefact for `ε`, `ε/4`, `ε/2`). Its claim (in (E3) form) that
`φ(y) ≤ φ(y*)` also needs `y ∈ ℓ₁` for the series to converge, which holds here by definition.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped ENNReal

/-- The commodity space `ℓ₁` of Exercise 16.6(d). -/
abbrev pecL1 : Type := ↥(lp (fun _ : ℕ => ℝ) 1)

/-- Elements of `ℓ₁` are summable sequences. -/
theorem pecL1_summable (x : pecL1) : Summable fun t => x t :=
  .of_norm (by simpa using x.2.summable)

/-- The consumption set `X = ℓ₁⁺`. -/
def pecX1 : Set pecL1 := {x | ∀ t, 0 ≤ x t}

/-- The utility function on `ℓ₁` (the same formula as on `ℓ∞`). -/
noncomputable def pecU1 (x : pecL1) : ℝ := pecUfun x

/-- The production set `Y = {y ∈ ℓ₁ : y_t ≤ 2^{−(t+1)}}`. -/
def pecY1 : Set pecL1 := {y | ∀ t, y t ≤ pecW t}

/-- `x* = (½, ¼, …)` as an element of `ℓ₁`. -/
noncomputable def pecStar1 : pecL1 :=
  ⟨pecW, (memℓp_gen_iff (by norm_num)).2 (summable_pecW.congr fun t => by
    simp [abs_of_pos (pecW_pos t)])⟩

/-- Coordinates of `x*` in `ℓ₁`. -/
@[simp] theorem pecStar1_apply (t : ℕ) : pecStar1 t = pecW t := rfl

/-- The price system `φ(x) = c Σ_t x_t`, i.e. `p = (c, c, …) ∈ ℓ∞ = ℓ₁*`. -/
noncomputable def pecPrice1 (c : ℝ) : StrongDual ℝ pecL1 :=
  c • lp.tsumCLM (α := ℕ) (𝕜 := ℝ) (E := ℝ)

/-- `φ(x) = c Σ_t x_t`. -/
theorem pecPrice1_apply (c : ℝ) (x : pecL1) : pecPrice1 c x = c * ∑' t, x t := by
  simp [pecPrice1]

/-- The aggregate technology of the one-firm economy is `Y`. -/
theorem pec_aggTech1 : aggTech (fun _ : Unit => pecY1) = pecY1 := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy ()
  · intro hw
    exact ⟨fun _ => w, fun _ => hw, by simp⟩

/-- **Exercise 16.6(d)**: in `ℓ₁`, `Y` has empty interior. If `B(y, r) ⊆ Y`, choose `N` with
`|y_N| < r/4` and `2^{−(N+1)} < r/4`; then `y + (r/2) e_N ∈ B(y, r)` but its `N`-th coordinate
exceeds `2^{−(N+1)}`. -/
theorem ex_16_6d_interior : interior pecY1 = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun y hy => ?_
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy)
  have hylim := (pecL1_summable y).tendsto_atTop_zero
  obtain ⟨N, hyN, hwN⟩ := ((hylim.eventually (lt_mem_nhds (by linarith : -(r / 4) < 0))).and
    (tendsto_pecW.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < r / 4)))).exists
  set z : pecL1 := y + lp.single 1 N (r / 2) with hz
  have hzball : z ∈ Metric.ball y r := by
    rw [Metric.mem_ball, dist_eq_norm, hz, add_sub_cancel_left,
      lp.norm_single (by norm_num), Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hzN := hball hzball N
  rw [hz, lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_eq_same] at hzN
  linarith

/-- `ℓ₁` is infinite dimensional: the unit vectors are linearly independent. -/
theorem pecL1_not_finiteDimensional : ¬ FiniteDimensional ℝ pecL1 := by
  intro hfin
  refine Module.Finite.not_linearIndependent_of_infinite (R := ℝ)
    (fun t : ℕ => (lp.single 1 t (1 : ℝ) : pecL1)) (linearIndependent_iff'.2 ?_)
  intro s g hg i hi
  have := congrArg (fun f : pecL1 => f i) hg
  simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply, lp.single_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at this
  simpa [hi] using this

/-- In `ℓ₁` the economy violates Assumption 15.5. -/
theorem ex_16_6d_not_assumption15_5 : ¬ Assumption15_5 pecL1 (fun _ : Unit => pecY1) := by
  rintro (h | h)
  · rw [pec_aggTech1, ex_16_6d_interior] at h
    exact not_nonempty_empty h
  · exact pecL1_not_finiteDimensional h

/-- The manual's inequality `g(z) = z + exp(1 − z) − 2 ≥ 0`, termwise:
`s ≥ (2 − e) w_t + e · pecTerm t s`. -/
theorem pec_term_le_linear (t : ℕ) (s : ℝ) :
    (2 - Real.exp 1) * pecW t + Real.exp 1 * pecTerm t s ≤ s := by
  have hw := pecW_pos t
  have h := Real.add_one_le_exp (1 - s / pecW t)
  have he : Real.exp 1 * Real.exp (-(s / pecW t)) = Real.exp (1 - s / pecW t) := by
    rw [← Real.exp_add]; ring_nf
  have hs : pecW t * (s / pecW t) = s := by field_simp
  unfold pecTerm
  nlinarith

/-- For `x ∈ ℓ₁⁺`: `Σ_t x_t ≥ (2 − e) + e u(x)`. -/
theorem pec_ell1_sum_ge {x : pecL1} (hx : x ∈ pecX1) :
    (2 - Real.exp 1) + Real.exp 1 * pecU1 x ≤ ∑' t, x t := by
  have h := (hasSum_pecW.mul_left (2 - Real.exp 1)).add
    ((hasSum_pecUfun hx).mul_left (Real.exp 1))
  rw [mul_one] at h
  exact hasSum_le (fun t => pec_term_le_linear t (x t)) h (pecL1_summable x).hasSum

/-- **Exercise 16.6(d)**: in `ℓ₁`, for every `c > 0`, `(x*, y*, p)` with `p = (c, c, …)` is a
competitive equilibrium. -/
theorem ex_16_6d_competitiveEq {c : ℝ} (hc : 0 < c) :
    CompetitiveEq (fun _ : Unit => pecX1) (fun _ : Unit => pecU1) (fun _ : Unit => pecY1)
      (fun _ => pecStar1) (fun _ => pecStar1) (pecPrice1 c) := by
  have hstar : ∑' t, pecStar1 t = 1 := hasSum_pecW.tsum_eq
  refine ⟨⟨fun _ t => (pecW_pos t).le, fun _ t => le_rfl, by simp⟩, fun _ z hz hcost => ?_,
    fun _ w hw => ?_⟩
  · by_contra hlt
    push Not at hlt
    have hu : pecU1 pecStar1 = 1 - Real.exp (-1) := pecUfun_pecW
    have hee : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    have hsum := pec_ell1_sum_ge hz
    have he := Real.exp_pos 1
    rw [pecPrice1_apply, pecPrice1_apply, hstar] at hcost
    have : 1 < ∑' t, z t := by
      have := mul_lt_mul_of_pos_left hlt he
      rw [hu] at this
      nlinarith
    nlinarith
  · rw [pecPrice1_apply, pecPrice1_apply]
    exact mul_le_mul_of_nonneg_left
      ((pecL1_summable w).tsum_le_tsum (fun t => hw t) (pecL1_summable pecStar1)) hc.le

/-- **Exercise 16.6(d)** (p. 495), both parts: in `ℓ₁` the production set has empty interior (so
Assumption 15.5 fails), and `(x*, y*, (c, c, …))` is a competitive equilibrium for every
`c > 0`. -/
theorem ex_16_6d :
    interior pecY1 = ∅ ∧ ¬ Assumption15_5 pecL1 (fun _ : Unit => pecY1) ∧
    ∀ c : ℝ, 0 < c → CompetitiveEq (fun _ : Unit => pecX1) (fun _ : Unit => pecU1)
      (fun _ : Unit => pecY1) (fun _ => pecStar1) (fun _ => pecStar1) (pecPrice1 c) :=
  ⟨ex_16_6d_interior, ex_16_6d_not_assumption15_5, fun _ hc => ex_16_6d_competitiveEq hc⟩

end StokeyLucasPrescott.EquilibriumApplications
