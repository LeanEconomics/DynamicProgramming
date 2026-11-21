/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ErgodicTheory.StationaryProcesses
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Fin

/-!
# Gaussian stationary sequences (Miao Exercise 7, partial)

Miao, Exercise 7, p. 130: a centered Gaussian stationary sequence with covariance
`R_n = E X_{n+k} X_k` and `R_n → 0` is ergodic.

The intended proof: `R_n → 0` makes the sequence mixing (Definition 4.2.4), and mixing implies
ergodicity (Theorem 4.2.3). Formalised here:

* `ex_4_7_reduction`: the reduction, mixing ⇒ ergodic (Theorem 4.2.3).
* `HasCovariance`, `IsCenteredGaussian`: `E X_j X_l = R_{|j − l|}`, and every finite linear
  combination `L = Σ cᵢ X_{aᵢ}` has `E e^{iL} = e^{−E L²/2}`.
* `integral_sum_mul_sum`: `E[(Σ cᵢ X_{aᵢ})(Σ dⱼ X_{bⱼ})] = Σᵢ Σⱼ cᵢ dⱼ R_{|aᵢ − bⱼ|}`.
* `ex_4_7_cross_covariance`: if `R_n → 0`, the covariance of `Σ cᵢ X_{aᵢ}` and the shifted
  `Σ dⱼ X_{n+bⱼ}` tends to `0`.
* `ex_4_7_charFun` (**mixing for characters**): for a centered Gaussian sequence with `R_n → 0`,
  `E e^{i(Σ cᵢ X_{aᵢ} + Σ dⱼ X_{n+bⱼ})} → E e^{iΣ cᵢ X_{aᵢ}} · E e^{iΣ dⱼ X_{bⱼ}}`.

**Not formalised.** The passage from mixing for the characters `e^{i⟨t, (X_{a₁}, …)⟩}` to the
set-wise mixing of Definition 4.2.4 (by density of trigonometric polynomials in `L²` of the law
of the path, or by weak convergence of the joint finite-dimensional laws), hence the ergodicity
claim of Exercise 7 itself.
-/

namespace Miao.ErgodicTheory

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Exercise 7** (Miao, p. 130), the reduction: a mixing stationary process is ergodic
(Theorem 4.2.3). -/
theorem ex_4_7_reduction {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (hmix : IsMixing P X) :
    IsErgodicProcess P X :=
  theorem_4_2_3 hX hst hmix

/-- Exercise 7: `R` is the covariance function, `E X_j X_l = R_{|j − l|}`. -/
def HasCovariance (P : Measure Ω) (X : ℕ → Ω → ℝ) (R : ℕ → ℝ) : Prop :=
  ∀ j l, ∫ ω, X j ω * X l ω ∂P = R (Nat.dist j l)

/-- Exercise 7: `X` is a centered Gaussian sequence: every finite linear combination
`L = Σ cᵢ X_{aᵢ}` has characteristic function `E e^{iL} = e^{−E L²/2}`. -/
def IsCenteredGaussian (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ (m : ℕ) (a : Fin m → ℕ) (c : Fin m → ℝ),
    ∫ ω, Complex.exp (Complex.I * ((∑ i, c i * X (a i) ω : ℝ) : ℂ)) ∂P =
      ((Real.exp (-(∫ ω, (∑ i, c i * X (a i) ω) ^ 2 ∂P) / 2) : ℝ) : ℂ)

/-- `E[(Σ cᵢ X_{aᵢ})(Σ dⱼ X_{bⱼ})] = Σᵢ Σⱼ cᵢ dⱼ R_{|aᵢ − bⱼ|}`. -/
theorem integral_sum_mul_sum {P : Measure Ω} {X : ℕ → Ω → ℝ} {R : ℕ → ℝ}
    (hX : ∀ j, MemLp (X j) 2 P) (hR : HasCovariance P X R) {m m' : ℕ} (a : Fin m → ℕ)
    (b : Fin m' → ℕ) (c : Fin m → ℝ) (d : Fin m' → ℝ) :
    ∫ ω, (∑ i, c i * X (a i) ω) * (∑ j, d j * X (b j) ω) ∂P =
      ∑ i, ∑ j, c i * d j * R (Nat.dist (a i) (b j)) := by
  have hint : ∀ i j, Integrable (fun ω => c i * X (a i) ω * (d j * X (b j) ω)) P := by
    intro i j
    have h := ((hX (a i)).integrable_mul (hX (b j))).const_mul (c i * d j)
    refine h.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]
    ring
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (fun ω => c i * X (a i) ω * (d j * X (b j) ω)) =
      fun ω => (c i * d j) * (X (a i) ω * X (b j) ω) := by
    ext ω; ring
  rw [this, integral_const_mul, hR]

/-- `|a − (n + b)| → ∞` as `n → ∞`. -/
theorem tendsto_dist_add (a b : ℕ) : Tendsto (fun n => Nat.dist a (n + b)) atTop atTop :=
  tendsto_atTop_atTop.2 fun M => ⟨M + a, fun n hn => by unfold Nat.dist; omega⟩

/-- **Exercise 7** (Miao, p. 130), the covariance step: if `R_n → 0`, then
`Cov(Σ cᵢ X_{aᵢ}, Σ dⱼ X_{n+bⱼ}) → 0`. -/
theorem ex_4_7_cross_covariance {P : Measure Ω} {X : ℕ → Ω → ℝ} {R : ℕ → ℝ}
    (hX : ∀ j, MemLp (X j) 2 P) (hR : HasCovariance P X R) (hR0 : Tendsto R atTop (𝓝 0))
    {m m' : ℕ} (a : Fin m → ℕ) (b : Fin m' → ℕ) (c : Fin m → ℝ) (d : Fin m' → ℝ) :
    Tendsto (fun n => ∫ ω, (∑ i, c i * X (a i) ω) * (∑ j, d j * X (n + b j) ω) ∂P) atTop
      (𝓝 0) := by
  simp_rw [integral_sum_mul_sum hX hR a (fun j => _ + b j) c d]
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin m')) fun j _ =>
      (hR0.comp (tendsto_dist_add (a i) (b j))).const_mul (c i * d j)
  simpa using h

/-- **Exercise 7** (Miao, p. 130), mixing for characters: for a centered Gaussian sequence with
covariance `R` and `R_n → 0`, `E e^{i(Σ cᵢ X_{aᵢ} + Σ dⱼ X_{n+bⱼ})} →
E e^{iΣ cᵢ X_{aᵢ}} · E e^{iΣ dⱼ X_{bⱼ}}`. -/
theorem ex_4_7_charFun {P : Measure Ω} {X : ℕ → Ω → ℝ} {R : ℕ → ℝ}
    (hX : ∀ j, MemLp (X j) 2 P) (hG : IsCenteredGaussian P X) (hR : HasCovariance P X R)
    (hR0 : Tendsto R atTop (𝓝 0)) {m : ℕ} (a b : Fin m → ℕ) (c d : Fin m → ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I *
      ((∑ i, c i * X (a i) ω + ∑ j, d j * X (n + b j) ω : ℝ) : ℂ)) ∂P) atTop
      (𝓝 ((∫ ω, Complex.exp (Complex.I * ((∑ i, c i * X (a i) ω : ℝ) : ℂ)) ∂P) *
        ∫ ω, Complex.exp (Complex.I * ((∑ j, d j * X (b j) ω : ℝ) : ℂ)) ∂P)) := by
  set A := ∑ i, ∑ i', c i * c i' * R (Nat.dist (a i) (a i')) with hA
  set B := ∑ j, ∑ j', d j * d j' * R (Nat.dist (b j) (b j')) with hB
  -- the combined family `(c, d)` at positions `(a, n + b)`
  have hsum : ∀ (n : ℕ) (ω : Ω), ∑ k, Fin.append c d k * X (Fin.append a (fun j => n + b j) k) ω
      = ∑ i, c i * X (a i) ω + ∑ j, d j * X (n + b j) ω := by
    intro n ω
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  have hQ : ∀ n : ℕ, ∫ ω, (∑ k, Fin.append c d k *
      X (Fin.append a (fun j => n + b j) k) ω) ^ 2 ∂P =
      A + B + (∑ i, ∑ j, c i * d j * R (Nat.dist (a i) (n + b j)) +
        ∑ j, ∑ i, d j * c i * R (Nat.dist (n + b j) (a i))) := by
    intro n
    simp_rw [sq]
    rw [integral_sum_mul_sum hX hR]
    rw [Fin.sum_univ_add]
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Nat.dist_add_add_left]
    rw [hA, hB]
    simp only [Finset.sum_add_distrib]
    ring
  have hlim : Tendsto (fun n : ℕ => ∑ i, ∑ j, c i * d j * R (Nat.dist (a i) (n + b j)) +
      ∑ j, ∑ i, d j * c i * R (Nat.dist (n + b j) (a i))) atTop (𝓝 0) := by
    have h1 := tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun j _ =>
        (hR0.comp (tendsto_dist_add (a i) (b j))).const_mul (c i * d j)
    have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun j _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun i _ =>
        ((hR0.comp (tendsto_dist_add (a i) (b j))).const_mul (d j * c i))
    simp only [Function.comp_apply, mul_zero, Finset.sum_const_zero] at h1 h2
    have h2' : Tendsto (fun n : ℕ => ∑ j, ∑ i, d j * c i * R (Nat.dist (n + b j) (a i))) atTop
        (𝓝 0) := h2.congr fun n => by simp_rw [Nat.dist_comm (n + _)]
    simpa using h1.add h2'
  have hQlim : Tendsto (fun n : ℕ => ∫ ω, (∑ k, Fin.append c d k *
      X (Fin.append a (fun j => n + b j) k) ω) ^ 2 ∂P) atTop (𝓝 (A + B)) := by
    simp_rw [hQ]
    simpa using (tendsto_const_nhds (x := A + B)).add hlim
  have hLHS : ∀ n : ℕ, ∫ ω, Complex.exp (Complex.I *
      ((∑ i, c i * X (a i) ω + ∑ j, d j * X (n + b j) ω : ℝ) : ℂ)) ∂P =
      ((Real.exp (-(∫ ω, (∑ k, Fin.append c d k *
        X (Fin.append a (fun j => n + b j) k) ω) ^ 2 ∂P) / 2) : ℝ) : ℂ) := by
    intro n
    rw [← hG (m + m) (Fin.append a fun j => n + b j) (Fin.append c d)]
    simp_rw [hsum]
  have hAeq : ∫ ω, (∑ i, c i * X (a i) ω) ^ 2 ∂P = A := by
    simp_rw [sq]; rw [integral_sum_mul_sum hX hR]
  have hBeq : ∫ ω, (∑ j, d j * X (b j) ω) ^ 2 ∂P = B := by
    simp_rw [sq]; rw [integral_sum_mul_sum hX hR]
  rw [hG m a c, hG m b d, hAeq, hBeq, ← Complex.ofReal_mul, ← Real.exp_add]
  simp_rw [hLHS]
  have hc : Tendsto (fun n : ℕ => -(∫ ω, (∑ k, Fin.append c d k *
      X (Fin.append a (fun j => n + b j) k) ω) ^ 2 ∂P) / 2) atTop (𝓝 (-A / 2 + -B / 2)) := by
    have := (hQlim.neg).div_const 2
    convert this using 2
    ring
  exact (Complex.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp hc)

end Miao.ErgodicTheory
