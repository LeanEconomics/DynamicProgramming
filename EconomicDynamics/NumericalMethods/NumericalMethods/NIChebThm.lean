/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import NumericalMethods.NIJacksonApprox
import NumericalMethods.NILebesgue

/-!
# Theorem 11.3.1, the Chebyshev Interpolation Theorem (Miao, p. 359)

* `ni_jackson_Ck` (Jackson's theorem for `C^k` functions): there is `Cₖ` such that every `C^k`
  function `f` has, for every `n ≥ k`, a polynomial `p` of degree `≤ n` with
  `‖f − p‖∞ ≤ Cₖ ‖f⁽ᵏ⁾‖∞ / nᵏ` on `[−1, 1]` (by induction on `k` from the Lipschitz case,
  integrating the approximant of `f'`).
* `theorem_11_3_1`: for every `k ≥ 1` there is `dₖ` such that for every `C^k` function `f` and
  every `n ≥ k`,
  `‖f − Iₙf‖∞ ≤ ((2/π) ln(n + 1) + 2) (dₖ/nᵏ) ‖f⁽ᵏ⁾‖∞`, where `Iₙf` is the degree-`n` Chebyshev
  interpolant. Proof: Lebesgue inequality (`ni_lebesgue_inequality`), the logarithmic Lebesgue
  constant (`ni_lebesgueFn_le`) and Jackson's theorem.

Departures from the book (see `theorem_11_3_1_counterexample` for the first):
* the bound holds for `n ≥ k` only, not for all `n`;
* `f` is taken `C^k` on `ℝ` (every `C^k` function on `[−1, 1]` has such an extension; the
  extension theorem is not formalised), and `‖·‖∞` is the sup over `[−1, 1]`;
* `dₖ` depends on `k` only, not on `f` (stronger than printed).
-/

open Polynomial Polynomial.Chebyshev Real

namespace Miao.NumericalMethods

theorem ni_le_supNorm {h : ℝ → ℝ} (hc : Continuous h) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |h x| ≤ ni_supNorm h := by
  have hb : BddAbove ((fun x => |h x|) '' Set.Icc (-1) 1) :=
    isCompact_Icc.bddAbove_image (hc.abs.continuousOn)
  exact le_csSup hb ⟨x, hx, rfl⟩

theorem ni_supNorm_nonneg (h : ℝ → ℝ) : 0 ≤ ni_supNorm h := by
  unfold ni_supNorm
  refine Real.sSup_nonneg fun y hy => ?_
  obtain ⟨x, -, rfl⟩ := hy
  exact abs_nonneg _

theorem ni_supNorm_le {h : ℝ → ℝ} {B : ℝ} (hB : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |h x| ≤ B) :
    ni_supNorm h ≤ B := by
  unfold ni_supNorm
  refine csSup_le ⟨|h 0|, 0, ⟨by norm_num, by norm_num⟩, rfl⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hB x hx

/-- An antiderivative `∑ᵢ qᵢ Xⁱ⁺¹/(i + 1)` of a polynomial `q`. -/
noncomputable def ni_antideriv (q : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range (q.natDegree + 1), C (q.coeff i / (i + 1)) * X ^ (i + 1)

theorem ni_antideriv_derivative (q : ℝ[X]) : derivative (ni_antideriv q) = q := by
  unfold ni_antideriv
  rw [derivative_sum]
  conv_rhs => rw [q.as_sum_range_C_mul_X_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [derivative_C_mul_X_pow, Nat.add_sub_cancel]
  congr 1
  push_cast
  field_simp

theorem ni_antideriv_natDegree (q : ℝ[X]) : (ni_antideriv q).natDegree ≤ q.natDegree + 1 := by
  unfold ni_antideriv
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  have := Finset.mem_range.mp hi
  omega

/-- **Jackson's theorem** for `C^k` functions (used in the proof of Theorem 11.3.1, Miao,
p. 359): for `k ≥ 1` there is `Cₖ ≥ 0` such that every `C^k` function `f` has, for each
`n ≥ k`, a polynomial `p` of degree `≤ n` with `|f(x) − p(x)| ≤ Cₖ ‖f⁽ᵏ⁾‖∞ / nᵏ` on
`[−1, 1]`. -/
theorem ni_jackson_Ck (k : ℕ) (hk : 1 ≤ k) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ f : ℝ → ℝ, ContDiff ℝ k f → ∀ n : ℕ, k ≤ n →
      ∃ p : ℝ[X], p.natDegree ≤ n ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        |f x - p.eval x| ≤ Ck * ni_supNorm (iteratedDeriv k f) / (n : ℝ) ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨ni_jacksonC, ni_jacksonC_pos.le, fun f hf n hn => ?_⟩
    have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
    have hdc : Continuous (deriv f) := by
      have := hf.continuous_iteratedDeriv 1 (by norm_num)
      rwa [iteratedDeriv_one] at this
    have hM : 0 ≤ ni_supNorm (deriv f) := ni_supNorm_nonneg _
    have hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
        |f x - f y| ≤ ni_supNorm (deriv f) * |x - y| := by
      intro x hx y hy
      have := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
        (fun z _ => hd z) (fun z hz => by
          rw [Real.norm_eq_abs]
          exact ni_le_supNorm hdc hz) hy hx
      simpa [Real.norm_eq_abs] using this
    obtain ⟨p, hp, hpx⟩ := ni_jackson_lipschitz f hM hlip hn
    refine ⟨p, hp, fun x hx => ?_⟩
    rw [iteratedDeriv_one, pow_one]
    exact hpx x hx
  | succ k hk ih =>
    obtain ⟨Ck, hCk, hJ⟩ := ih
    refine ⟨ni_jacksonC * Ck * 2 ^ k, by have := ni_jacksonC_pos; positivity,
      fun f hf n hn => ?_⟩
    have hf' : ContDiff ℝ (k + 1 : ℕ) f := hf
    push_cast at hf'
    obtain ⟨hd, -, hg⟩ := contDiff_succ_iff_deriv.mp hf'
    obtain ⟨q, hq, hqx⟩ := hJ (deriv f) hg (n - 1) (by omega)
    have hit : iteratedDeriv k (deriv f) = iteratedDeriv (k + 1) f :=
      (iteratedDeriv_succ' (n := k) (f := f)).symm
    rw [hit] at hqx
    set M := Ck * ni_supNorm (iteratedDeriv (k + 1) f) / ((n - 1 : ℕ) : ℝ) ^ k
    have hn1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
      have : 0 < n - 1 := by omega
      exact_mod_cast this
    have hM : 0 ≤ M := by
      have := ni_supNorm_nonneg (iteratedDeriv (k + 1) f)
      positivity
    set Q := ni_antideriv q
    set h : ℝ → ℝ := fun x => f x - Q.eval x
    have hhd : ∀ x, HasDerivAt h (deriv f x - q.eval x) x := by
      intro x
      have := (hd x).hasDerivAt.sub (Polynomial.hasDerivAt Q x)
      rwa [ni_antideriv_derivative] at this
    have hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
        |h x - h y| ≤ M * |x - y| := by
      intro x hx y hy
      have := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
        (fun z _ => (hhd z).differentiableAt) (fun z hz => by
          rw [(hhd z).deriv, Real.norm_eq_abs]
          exact hqx z hz) hy hx
      simpa [Real.norm_eq_abs] using this
    obtain ⟨p₀, hp₀, hp₀x⟩ := ni_jackson_lipschitz h hM hlip (show 1 ≤ n by omega)
    refine ⟨Q + p₀, ?_, fun x hx => ?_⟩
    · refine (natDegree_add_le _ _).trans (max_le ?_ hp₀)
      exact (ni_antideriv_natDegree q).trans (by omega)
    · have e : f x - (Q + p₀).eval x = h x - p₀.eval x := by
        simp only [h, eval_add]; ring
      rw [e]
      refine (hp₀x x hx).trans ?_
      -- `C M / n ≤ C Ck 2ᵏ ‖f⁽ᵏ⁺¹⁾‖ / n^{k+1}`
      have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hhalf : (n : ℝ) / 2 ≤ ((n - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        have : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
        push_cast
        linarith
      have hpow : ((n : ℝ) / 2) ^ k ≤ ((n - 1 : ℕ) : ℝ) ^ k :=
        pow_le_pow_left₀ (by positivity) hhalf k
      set S := ni_supNorm (iteratedDeriv (k + 1) f)
      have hS : 0 ≤ S := ni_supNorm_nonneg _
      have hC := ni_jacksonC_pos
      simp only [M]
      rw [div_pow] at hpow
      have hA : Ck * S / ((n - 1 : ℕ) : ℝ) ^ k ≤ Ck * S * 2 ^ k / (n : ℝ) ^ k := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : (n : ℝ) ^ k ≤ 2 ^ k * ((n - 1 : ℕ) : ℝ) ^ k := by
          rw [div_le_iff₀ (by positivity)] at hpow
          linarith
        have : 0 ≤ Ck * S := by positivity
        nlinarith
      calc ni_jacksonC * (Ck * S / ((n - 1 : ℕ) : ℝ) ^ k) / n
          ≤ ni_jacksonC * (Ck * S * 2 ^ k / (n : ℝ) ^ k) / n := by gcongr
        _ = ni_jacksonC * Ck * 2 ^ k * S / (n : ℝ) ^ (k + 1) := by
          rw [pow_succ]; field_simp

/-- **Theorem 11.3.1** (Chebyshev Interpolation Theorem, Miao, p. 359; corrected): for every
`k ≥ 1` there is `dₖ` such that for every `C^k` function `f` and every `n ≥ k`,
`‖f − Iₙf‖∞ ≤ ((2/π) ln(n + 1) + 2) (dₖ/nᵏ) ‖f⁽ᵏ⁾‖∞`, where `Iₙf` is the degree-`n` Chebyshev
interpolant and `‖·‖∞` is the uniform norm on `[−1, 1]`. -/
theorem theorem_11_3_1 (k : ℕ) (hk : 1 ≤ k) :
    ∃ d : ℝ, ∀ f : ℝ → ℝ, ContDiff ℝ k f → ∀ n : ℕ, k ≤ n →
      ni_supNorm (fun x => f x - (ni_chebInterp n f).eval x) ≤
        (2 / π * Real.log (n + 1) + 2) * (d / (n : ℝ) ^ k) *
          ni_supNorm (iteratedDeriv k f) := by
  obtain ⟨Ck, hCk, hJ⟩ := ni_jackson_Ck k hk
  refine ⟨2 * π ^ 2 * Ck, fun f hf n hn => ?_⟩
  obtain ⟨p, hp, hpx⟩ := hJ f hf n hn
  set E := Ck * ni_supNorm (iteratedDeriv k f) / (n : ℝ) ^ k
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hE : 0 ≤ E := by
    have := ni_supNorm_nonneg (iteratedDeriv k f)
    positivity
  have hpdeg : p.degree < (n + 1 : ℕ) :=
    (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hp)
  have hlog : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
  refine ni_supNorm_le fun x hx => ?_
  have hnodes : ∀ k' ∈ Finset.Icc 1 (n + 1),
      |f (ni_chebNode (n + 1) k') - p.eval (ni_chebNode (n + 1) k')| ≤ E :=
    fun k' _ => hpx _ ⟨neg_one_le_cos _, cos_le_one _⟩
  have h1 := ni_lebesgue_inequality n f p hpdeg E hnodes x
  have h2 := ni_lebesgueFn_le n hx
  have h3 : |f x - (ni_chebInterp n f).eval x| ≤ (1 + 4 * π * (1 + Real.log (n + 1))) * E := by
    have := hpx x hx
    have hΛ : ni_lebesgueFn n x * E ≤ 4 * π * (1 + Real.log (n + 1)) * E :=
      mul_le_mul_of_nonneg_right h2 hE
    linarith
  have hpi := pi_gt_three
  have hpi0 := pi_pos
  have : 1 + 4 * π * (1 + Real.log (n + 1)) ≤ 2 * π ^ 2 * (2 / π * Real.log (n + 1) + 2) := by
    have e : 2 * π ^ 2 * (2 / π * Real.log (n + 1) + 2) = 4 * π * Real.log (n + 1) + 4 * π ^ 2 := by
      field_simp
      norm_num
    rw [e]
    nlinarith
  calc |f x - (ni_chebInterp n f).eval x| ≤ (1 + 4 * π * (1 + Real.log (n + 1))) * E := h3
    _ ≤ 2 * π ^ 2 * (2 / π * Real.log (n + 1) + 2) * E := mul_le_mul_of_nonneg_right this hE
    _ = (2 / π * Real.log (n + 1) + 2) * (2 * π ^ 2 * Ck / (n : ℝ) ^ k) *
          ni_supNorm (iteratedDeriv k f) := by
        simp only [E]; ring

end Miao.NumericalMethods
