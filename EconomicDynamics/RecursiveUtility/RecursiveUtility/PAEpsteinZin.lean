/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.SSCertaintyEquivalents
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Epstein–Zin recursion on one node of an event tree

Miao, *Economic Dynamics in Discrete Time*, §20.4 (pp. 711–714), using the Epstein–Zin utility
(20.3) of §20.2.1 and its pricing kernel (20.20) of §20.3.3, which are restated here under the
prefix `pa_` (the §20.2–20.3 formalisations live in other projects).

The setting is one node of an event tree: the next-period shock takes finitely many values
`s : S` with probabilities `p s` (`p ≥ 0`, `∑ p = 1`), and the conditional expectation is
`pa_E p f = ∑ s, p s * f s`.

* `pa_W β ρ c y = ((1 − β) c^{1−ρ} + β y^{1−ρ})^{1/(1−ρ)}`, the CES time aggregator of (20.3);
* `pa_CE γ p v = (E v^{1−γ})^{1/(1−γ)}`, the certainty equivalent of (20.3), which is the
  Kreps–Porteus certainty equivalent `kpR (1 − γ)` of the copied `SSCertaintyEquivalents`
  (`pa_CE_eq_kpR`);
* both are positively homogeneous of degree one (`pa_W_homog`, `pa_CE_homog`), the property
  "scale invariance" used for the conjecture `J_t(X) = A_t X_t` of §20.4.1;
* `pa_M` is the pricing kernel (20.20), `M = β (C'/C)^{−ρ} (U'/M_t(U'))^{ρ−γ}`.

The lemmas `pa_E_*` are the linearity of the conditional expectation, and `pa_log_*` are the
logarithmic identities used to verify identities between positive powers.
-/

namespace Miao.RecursiveUtility

open Real

/-- The conditional expectation `E_t f = ∑ s, p s f(s)` at one node of the event tree. -/
def pa_E {S : Type*} [Fintype S] (p : S → ℝ) (f : S → ℝ) : ℝ := ∑ s, p s * f s

/-- Miao, (20.3), p. 686: the CES time aggregator
`W(c, y) = ((1 − β) c^{1−ρ} + β y^{1−ρ})^{1/(1−ρ)}` of the Epstein–Zin utility. -/
noncomputable def pa_W (β ρ c y : ℝ) : ℝ :=
  ((1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ)) ^ (1 / (1 - ρ))

/-- Miao, (20.3), p. 686: the certainty equivalent `M_t(x) = (E_t x^{1−γ})^{1/(1−γ)}`. -/
noncomputable def pa_CE {S : Type*} [Fintype S] (γ : ℝ) (p : S → ℝ) (v : S → ℝ) : ℝ :=
  (pa_E p fun s => v s ^ (1 - γ)) ^ (1 / (1 - γ))

/-- Miao, (20.20), p. 710: the Epstein–Zin pricing kernel
`M_{t+1} = β (C_{t+1}/C_t)^{−ρ} (U_{t+1}/M_t(U_{t+1}))^{ρ−γ}`. -/
noncomputable def pa_M {S : Type*} [Fintype S] (β ρ γ : ℝ) (p : S → ℝ) (C : ℝ) (C' U' : S → ℝ)
    (s : S) : ℝ :=
  β * (C' s / C) ^ (-ρ) * (U' s / pa_CE γ p U') ^ (ρ - γ)

theorem pa_E_add {S : Type*} [Fintype S] (p f g : S → ℝ) :
    pa_E p (fun s => f s + g s) = pa_E p f + pa_E p g := by
  simp only [pa_E, mul_add, Finset.sum_add_distrib]

theorem pa_E_sub {S : Type*} [Fintype S] (p f g : S → ℝ) :
    pa_E p (fun s => f s - g s) = pa_E p f - pa_E p g := by
  simp only [pa_E, mul_sub, Finset.sum_sub_distrib]

theorem pa_E_const_mul {S : Type*} [Fintype S] (p f : S → ℝ) (k : ℝ) :
    pa_E p (fun s => k * f s) = k * pa_E p f := by
  simp only [pa_E, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem pa_E_mul_const {S : Type*} [Fintype S] (p f : S → ℝ) (k : ℝ) :
    pa_E p (fun s => f s * k) = pa_E p f * k := by
  simp only [pa_E, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem pa_E_const {S : Type*} [Fintype S] {p : S → ℝ} (hp1 : ∑ s, p s = 1) (k : ℝ) :
    pa_E p (fun _ => k) = k := by
  simp only [pa_E, ← Finset.sum_mul, hp1, one_mul]

theorem pa_E_congr {S : Type*} [Fintype S] (p : S → ℝ) {f g : S → ℝ} (h : ∀ s, f s = g s) :
    pa_E p f = pa_E p g := by
  simp only [pa_E, h]

theorem pa_E_pos {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    {f : S → ℝ} (hf : ∀ s, 0 < f s) : 0 < pa_E p f := by
  obtain ⟨s₀, hs₀⟩ : ∃ s, 0 < p s := by
    by_contra h
    push Not at h
    have : ∑ s, p s ≤ 0 := Finset.sum_nonpos fun s _ => h s
    linarith
  calc 0 < p s₀ * f s₀ := mul_pos hs₀ (hf s₀)
    _ ≤ ∑ s, p s * f s :=
        Finset.single_le_sum (f := fun s => p s * f s)
          (fun s _ => mul_nonneg (hp s) (hf s).le) (Finset.mem_univ s₀)

/-- Two positive reals with equal logarithms are equal. -/
theorem pa_eq_of_log_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : Real.log a = Real.log b) :
    a = b := Real.log_injOn_pos ha hb h

theorem pa_CE_pos {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (γ : ℝ) {v : S → ℝ} (hv : ∀ s, 0 < v s) : 0 < pa_CE γ p v :=
  Real.rpow_pos_of_pos (pa_E_pos hp hp1 fun s => Real.rpow_pos_of_pos (hv s) _) _

/-- The certainty equivalent (20.3) is the Kreps–Porteus certainty equivalent `kpR (1 − γ)`
(Sargent–Stachurski (7.16)) of the copied `SSCertaintyEquivalents`, at a state `x` whose
transition row is `p`. -/
theorem pa_CE_eq_kpR {S : Type*} [Fintype S] (γ : ℝ) (P : Matrix S S ℝ) (x : S) (v : S → ℝ) :
    pa_CE γ (P x) v = SS.kpR (1 - γ) P v x := by
  simp only [pa_CE, SS.kpR, pa_E, Matrix.mulVec, dotProduct, one_div]

/-- Miao, p. 686: the certainty equivalent of (20.3) is homogeneous of degree one,
`M_t(λ v) = λ M_t(v)` for `λ > 0`. -/
theorem pa_CE_homog {S : Type*} [Fintype S] {γ : ℝ} (hγ : γ ≠ 1) {p : S → ℝ}
    (hp : ∀ s, 0 ≤ p s) {lam : ℝ} (hlam : 0 < lam) {v : S → ℝ} (hv : ∀ s, 0 ≤ v s) :
    pa_CE γ p (fun s => lam * v s) = lam * pa_CE γ p v := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hE : (pa_E p fun s => (lam * v s) ^ (1 - γ))
      = lam ^ (1 - γ) * pa_E p fun s => v s ^ (1 - γ) := by
    rw [← pa_E_const_mul]
    exact pa_E_congr p fun s => Real.mul_rpow hlam.le (hv s)
  have hE0 : 0 ≤ pa_E p fun s => v s ^ (1 - γ) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hp s) (Real.rpow_nonneg (hv s) _)
  simp only [pa_CE]
  rw [hE, Real.mul_rpow (Real.rpow_nonneg hlam.le _) hE0, ← Real.rpow_mul hlam.le,
    mul_one_div_cancel h1, Real.rpow_one]

/-- Miao, p. 686: the time aggregator of (20.3) is homogeneous of degree one,
`W(λ c, λ y) = λ W(c, y)` for `λ > 0` ("scale invariance"). -/
theorem pa_W_homog {β ρ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hρ : ρ ≠ 1) {lam c y : ℝ}
    (hlam : 0 < lam) (hc : 0 ≤ c) (hy : 0 ≤ y) :
    pa_W β ρ (lam * c) (lam * y) = lam * pa_W β ρ c y := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hin : 0 ≤ (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) :=
    add_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hc _))
      (mul_nonneg hβ0 (Real.rpow_nonneg hy _))
  simp only [pa_W]
  rw [Real.mul_rpow hlam.le hc, Real.mul_rpow hlam.le hy]
  have : (1 - β) * (lam ^ (1 - ρ) * c ^ (1 - ρ)) + β * (lam ^ (1 - ρ) * y ^ (1 - ρ))
      = lam ^ (1 - ρ) * ((1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ)) := by ring
  rw [this, Real.mul_rpow (Real.rpow_nonneg hlam.le _) hin, ← Real.rpow_mul hlam.le,
    mul_one_div_cancel h1, Real.rpow_one]

theorem pa_W_pos {β ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    0 < pa_W β ρ c y :=
  Real.rpow_pos_of_pos (add_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hc _))
    (mul_pos hβ0 (Real.rpow_pos_of_pos hy _))) _

end Miao.RecursiveUtility
