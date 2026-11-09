/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NIChebyshev
import NumericalMethods.NIInterpolation
import NumericalMethods.NILegendre

/-!
# Chebyshev interpolation (Miao, §11.3.1, pp. 359–360)

With basis `φⱼ = Tⱼ₋₁`, `j = 1, …, n`, and the `n` roots `xₖ` of `Tₙ` as nodes:

* `ni_chebPhi_gram`: `Φ'Φ = diag(n, n/2, …, n/2)` (from the discrete orthogonality).
* `ni_chebCoeff_eq`: the least-squares coefficients `c = (Φ'Φ)⁻¹Φ'y` are
  `c₁ = (1/n) ∑ₖ f(xₖ)T₀(xₖ)` and `cⱼ = (2/n) ∑ₖ f(xₖ)Tⱼ₋₁(xₖ)` for `j ≥ 2`, and
  `ni_chebCoeff_eq_ratio`: `cⱼ = ∑ₖ f(xₖ)Tⱼ₋₁(xₖ) / ∑ₖ Tⱼ₋₁(xₖ)²`.
* `ni_chebInterpolant_nodes`: the Chebyshev interpolant `I_{n−1}^f = ∑ᵢ cᵢ Tᵢ₋₁` matches `f`
  exactly at the `n` roots of `Tₙ`.
* `ni_chebTruncation_bound` (11.2): on `[−1, 1]` the truncation error of dropping the terms
  `m + 1, …, n` is at most `∑ |cₖ|` over the dropped terms.
* `ni_chebInterp n f`: the degree-`n` Chebyshev interpolant of Theorem 11.3.1 (Lagrange form at
  the `n + 1` roots of `Tₙ₊₁`), equal to the coefficient form (`ni_chebInterp_eq_coeff_form`).
* `ni_lebesgue_inequality`: the first step of the proof of Theorem 11.3.1, the Lebesgue
  inequality `|f(x) − Iₙf(x)| ≤ |f(x) − p(x)| + Λₙ(x) maxₖ |f(xₖ) − p(xₖ)|` for every polynomial
  `p` of degree `≤ n`, with `Λₙ(x) = ∑ₖ |ℓₖ(x)|` the Lebesgue function.
* `theorem_11_3_1_counterexample`: Theorem 11.3.1 is false as printed ("for all `n`"): for
  `f(x) = x²`, `k = 3`, `n = 1` the right side is `0` and the left side is `1/2`.

The bound of Theorem 11.3.1 itself (for `n ≥ k`; Rivlin 1990) rests on Jackson's theorem and the
logarithmic growth of the Chebyshev Lebesgue constant, neither of which is in Mathlib; it is not
formalised here beyond the two items above. The remarks that the truncated series is "almost the
same as the minimax polynomial" are heuristic and not formalised.
-/

open Polynomial Polynomial.Chebyshev Real Matrix

namespace Miao.NumericalMethods

/-- Reindexing `∑_{k : Fin n} g(k + 1) = ∑_{k = 1}^{n} g(k)`. -/
theorem ni_sum_fin_succ (n : ℕ) (g : ℕ → ℝ) :
    ∑ k : Fin n, g ((k : ℕ) + 1) = ∑ k ∈ Finset.Icc 1 n, g k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => g (k + 1)), ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun k _ => by rw [add_comm]

/-- The Chebyshev interpolation matrix `Φₖⱼ = Tⱼ₋₁(xₖ)` (Miao, p. 359; indices from `0`). -/
noncomputable def ni_chebPhi (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k j => (T ℝ (j : ℕ)).eval (ni_chebNode n (k + 1))

/-- The diagonal of `Φ'Φ`: `n` for the first basis function and `n/2` for the others. -/
noncomputable def ni_chebGramDiag (n : ℕ) (j : Fin n) : ℝ :=
  if (j : ℕ) = 0 then n else n / 2

/-- Miao, p. 359: `Φ'Φ = diag(n, n/2, …, n/2)`. -/
theorem ni_chebPhi_gram (n : ℕ) :
    (ni_chebPhi n)ᵀ * ni_chebPhi n = Matrix.diagonal (ni_chebGramDiag n) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.transpose_apply, ni_chebPhi, Matrix.of_apply]
  rw [ni_sum_fin_succ n (fun k => (T ℝ (i : ℕ)).eval (ni_chebNode n k) *
    (T ℝ (j : ℕ)).eval (ni_chebNode n k)), ni_cheb_discrete_orthogonality i.2 j.2]
  by_cases h : i = j
  · subst h
    simp [ni_chebGramDiag]
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h']

theorem ni_chebGramDiag_ne_zero {n : ℕ} (j : Fin n) : ni_chebGramDiag n j ≠ 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0))
  unfold ni_chebGramDiag
  split_ifs <;> positivity

theorem ni_chebGram_isUnit (n : ℕ) : IsUnit ((ni_chebPhi n)ᵀ * ni_chebPhi n).det := by
  rw [ni_chebPhi_gram, det_diagonal]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => ni_chebGramDiag_ne_zero j)

/-- The data vector `yₖ = f(xₖ)` at the Chebyshev nodes. -/
noncomputable def ni_chebData (n : ℕ) (f : ℝ → ℝ) (k : Fin n) : ℝ := f (ni_chebNode n (k + 1))

/-- The least-squares coefficients `c = (Φ'Φ)⁻¹Φ'y` (Miao, p. 359). -/
noncomputable def ni_chebCoeff (n : ℕ) (f : ℝ → ℝ) : Fin n → ℝ :=
  ((ni_chebPhi n)ᵀ * ni_chebPhi n)⁻¹ *ᵥ ((ni_chebPhi n)ᵀ *ᵥ ni_chebData n f)

/-- Miao, p. 359: `c₁ = (1/n) ∑ₖ f(xₖ)T₀(xₖ)` and `cⱼ = (2/n) ∑ₖ f(xₖ)Tⱼ₋₁(xₖ)` for `j ≥ 2`. -/
theorem ni_chebCoeff_eq (n : ℕ) (f : ℝ → ℝ) (j : Fin n) :
    ni_chebCoeff n f j = (if (j : ℕ) = 0 then 1 / (n : ℝ) else 2 / n) *
      ∑ k ∈ Finset.Icc 1 n, f (ni_chebNode n k) * (T ℝ (j : ℕ)).eval (ni_chebNode n k) := by
  unfold ni_chebCoeff
  have hinv : (Matrix.diagonal (ni_chebGramDiag n))⁻¹ =
      Matrix.diagonal (fun j => (ni_chebGramDiag n j)⁻¹) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal]
    convert diagonal_one with i
    exact inv_mul_cancel₀ (ni_chebGramDiag_ne_zero i)
  rw [ni_chebPhi_gram, hinv, mulVec_diagonal]
  have hs : ((ni_chebPhi n)ᵀ *ᵥ ni_chebData n f) j =
      ∑ k ∈ Finset.Icc 1 n, f (ni_chebNode n k) * (T ℝ (j : ℕ)).eval (ni_chebNode n k) := by
    rw [← ni_sum_fin_succ n (fun k => f (ni_chebNode n k) * (T ℝ (j : ℕ)).eval (ni_chebNode n k))]
    simp only [mulVec, dotProduct, transpose_apply, ni_chebPhi, of_apply, ni_chebData]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hs]
  unfold ni_chebGramDiag
  split_ifs <;> simp [div_eq_mul_inv]

/-- Miao, p. 359: `cⱼ = ∑ₖ f(xₖ)Tⱼ₋₁(xₖ) / ∑ₖ Tⱼ₋₁(xₖ)²`. -/
theorem ni_chebCoeff_eq_ratio (n : ℕ) (f : ℝ → ℝ) (j : Fin n) :
    ni_chebCoeff n f j =
      (∑ k ∈ Finset.Icc 1 n, f (ni_chebNode n k) * (T ℝ (j : ℕ)).eval (ni_chebNode n k)) /
        ∑ k ∈ Finset.Icc 1 n, (T ℝ (j : ℕ)).eval (ni_chebNode n k) ^ 2 := by
  have hsq : ∑ k ∈ Finset.Icc 1 n, (T ℝ (j : ℕ)).eval (ni_chebNode n k) ^ 2 =
      ni_chebGramDiag n j := by
    simp_rw [sq]
    rw [ni_cheb_discrete_orthogonality j.2 j.2]
    simp [ni_chebGramDiag]
  rw [hsq, ni_chebCoeff_eq]
  unfold ni_chebGramDiag
  split_ifs <;> field_simp

/-- The Chebyshev interpolant `I_{n−1}^f(x) = ∑ᵢ cᵢ Tᵢ₋₁(x)` (Miao, p. 359). -/
noncomputable def ni_chebInterpolant (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin n, ni_chebCoeff n f j * (T ℝ (j : ℕ)).eval x

/-- Miao, p. 359: `I_{n−1}^f` and `f` are exactly matched at the `n` roots of `Tₙ`. -/
theorem ni_chebInterpolant_nodes (n : ℕ) (f : ℝ → ℝ) (k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
    ni_chebInterpolant n f (ni_chebNode n k) = f (ni_chebNode n k) := by
  have hdet : IsUnit (ni_chebPhi n).det := by
    have h := ni_chebGram_isUnit n
    rw [det_mul, det_transpose] at h
    exact isUnit_of_mul_isUnit_left h
  have h := (ni_leastSquares_eq_interp (ni_chebPhi n) (ni_chebData n f) hdet).2
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hk' := congrFun h ⟨k - 1, by omega⟩
  have e : k - 1 + 1 = k := by omega
  simp only [mulVec, dotProduct, ni_chebPhi, of_apply, ni_chebData, e] at hk'
  rw [← hk']
  unfold ni_chebInterpolant ni_chebCoeff
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Miao, (11.2), p. 360: since `|Tₖ| ≤ 1` on `[−1, 1]`, the difference between the full and the
truncated Chebyshev series is bounded by the sum of the absolute values of the dropped
coefficients. -/
theorem ni_chebTruncation_bound (c : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |∑ i ∈ Finset.range n, c i * (T ℝ i).eval x - ∑ i ∈ Finset.range m, c i * (T ℝ i).eval x|
      ≤ ∑ i ∈ Finset.Ico m n, |c i| := by
  rw [← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (ni_cheb_abs_le_one i hx)

/-- The degree-`n` Chebyshev interpolant `Iₙf` of Theorem 11.3.1: the polynomial interpolating
`f` at the `n + 1` roots of `Tₙ₊₁` (Lagrange form). -/
noncomputable def ni_chebInterp (n : ℕ) (f : ℝ → ℝ) : ℝ[X] :=
  Lagrange.interpolate (Finset.Icc 1 (n + 1)) (ni_chebNode (n + 1))
    (fun k => f (ni_chebNode (n + 1) k))

/-- `Iₙf` has degree at most `n` and interpolates `f` at the `n + 1` roots of `Tₙ₊₁`. -/
theorem ni_chebInterp_spec (n : ℕ) (f : ℝ → ℝ) :
    (ni_chebInterp n f).degree < (n + 1 : ℕ) ∧
      ∀ k ∈ Finset.Icc 1 (n + 1), (ni_chebInterp n f).eval (ni_chebNode (n + 1) k) =
        f (ni_chebNode (n + 1) k) := by
  have hinj := ni_chebNode_injOn (n + 1)
  refine ⟨?_, fun k hk => Lagrange.eval_interpolate_at_node _ hinj hk⟩
  have := Lagrange.degree_interpolate_lt (r := fun k => f (ni_chebNode (n + 1) k)) hinj
  rwa [Nat.card_Icc, Nat.add_sub_cancel] at this

/-- Miao, p. 359: the Lagrange-form interpolant `Iₙf` coincides with the coefficient form
`∑ⱼ cⱼ Tⱼ₋₁` computed from `n + 1` nodes. -/
theorem ni_chebInterp_eq_coeff_form (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (ni_chebInterp n f).eval x = ni_chebInterpolant (n + 1) f x := by
  set P : ℝ[X] := ∑ j : Fin (n + 1), ni_chebCoeff (n + 1) f j • T ℝ (j : ℕ)
  have hP : ∀ y, P.eval y = ni_chebInterpolant (n + 1) f y := by
    intro y
    simp [P, eval_finsetSum, ni_chebInterpolant]
  have hdeg : P.degree < (Finset.Icc 1 (n + 1)).card := by
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun j _ => ?_
    refine lt_of_le_of_lt (degree_smul_le _ _) ?_
    rw [degree_T, Int.natAbs_natCast]
    exact_mod_cast j.2
  have heq : P = ni_chebInterp n f := by
    refine Lagrange.eq_interpolate_of_eval_eq _ (ni_chebNode_injOn (n + 1)) hdeg fun k hk => ?_
    rw [hP]
    exact ni_chebInterpolant_nodes (n + 1) f k hk
  rw [← heq, hP]

/-- The Lebesgue function `Λₙ(x) = ∑ₖ |ℓₖ(x)|` of the Chebyshev nodes (`ℓₖ` the Lagrange
basis). -/
noncomputable def ni_lebesgueFn (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (n + 1),
    |(Lagrange.basis (Finset.Icc 1 (n + 1)) (ni_chebNode (n + 1)) k).eval x|

/-- Theorem 11.3.1 (Miao, p. 359), first step of the proof (the Lebesgue inequality): for every
polynomial `p` of degree `≤ n`, `|f(x) − Iₙf(x)| ≤ |f(x) − p(x)| + Λₙ(x) maxₖ |f(xₖ) − p(xₖ)|`;
in particular `‖f − Iₙf‖∞ ≤ (1 + Λₙ) ‖f − p‖∞`. -/
theorem ni_lebesgue_inequality (n : ℕ) (f : ℝ → ℝ) (p : ℝ[X]) (hp : p.degree < (n + 1 : ℕ))
    (E : ℝ) (hE : ∀ k ∈ Finset.Icc 1 (n + 1),
      |f (ni_chebNode (n + 1) k) - p.eval (ni_chebNode (n + 1) k)| ≤ E) (x : ℝ) :
    |f x - (ni_chebInterp n f).eval x| ≤ |f x - p.eval x| + ni_lebesgueFn n x * E := by
  set s := Finset.Icc 1 (n + 1)
  set v := ni_chebNode (n + 1)
  have hinj : Set.InjOn v s := ni_chebNode_injOn (n + 1)
  have hcard : p.degree < s.card := by simpa [s] using hp
  have hpI : p = Lagrange.interpolate s v (fun k => p.eval (v k)) :=
    Lagrange.eq_interpolate hinj hcard
  have hdiff : (ni_chebInterp n f).eval x - p.eval x =
      ∑ k ∈ s, (f (v k) - p.eval (v k)) * (Lagrange.basis s v k).eval x := by
    have h1 : ni_chebInterp n f - p =
        Lagrange.interpolate s v (fun k => f (v k) - p.eval (v k)) := by
      conv_lhs => rw [hpI]
      unfold ni_chebInterp
      rw [← map_sub]
      rfl
    rw [← eval_sub, h1, Lagrange.interpolate_apply, eval_finsetSum]
    simp
  have hbound : |(ni_chebInterp n f).eval x - p.eval x| ≤ ni_lebesgueFn n x * E := by
    rw [hdiff, ni_lebesgueFn, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hE k hk) (abs_nonneg _)
  calc |f x - (ni_chebInterp n f).eval x|
      = |(f x - p.eval x) - ((ni_chebInterp n f).eval x - p.eval x)| := by ring_nf
    _ ≤ |f x - p.eval x| + |(ni_chebInterp n f).eval x - p.eval x| := abs_sub _ _
    _ ≤ _ := by linarith

/-- The uniform norm on `[−1, 1]`, `‖g‖∞ = sup_{x ∈ [−1,1]} |g(x)|`. -/
noncomputable def ni_supNorm (g : ℝ → ℝ) : ℝ := sSup ((fun x => |g x|) '' Set.Icc (-1) 1)

/-- The bound of **Theorem 11.3.1** (Chebyshev Interpolation Theorem, Miao, p. 359) as printed:
there is `dₖ` such that for all `n`,
`‖f − Iₙf‖∞ ≤ ((2/π) ln(n + 1) + 2) (dₖ/nᵏ) ‖f⁽ᵏ⁾‖∞`. -/
def ni_Theorem_11_3_1_bound (k : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ d : ℝ, ∀ n : ℕ, ni_supNorm (fun x => f x - (ni_chebInterp n f).eval x) ≤
    (2 / π * Real.log (n + 1) + 2) * (d / (n : ℝ) ^ k) * ni_supNorm (iteratedDeriv k f)

/-- **Theorem 11.3.1** (Miao, p. 359) is false as printed ("for all `n`"): `f(x) = x²` is `C^∞`,
take `k = 3`; then `f⁽³⁾ = 0`, so the right side vanishes for every `n`, while for `n = 1` the
interpolant at the roots `±1/√2` of `T₂` is the constant `1/2`, so `‖f − I₁f‖∞ ≥ 1/2`. The
bound (Rivlin) holds only for `n ≥ k`. -/
theorem theorem_11_3_1_counterexample : ¬ ni_Theorem_11_3_1_bound 3 (fun x => x ^ 2) := by
  rintro ⟨d, hd⟩
  have h1 := hd 1
  -- the third derivative vanishes
  have hder : iteratedDeriv 3 (fun x : ℝ => x ^ 2) = fun _ => 0 := by
    have e : (fun x : ℝ => x ^ 2) = fun x => (X ^ 2 : ℝ[X]).eval x := by funext x; simp
    rw [e, ni_iteratedDeriv_eval, iterate_derivative_eq_zero (by simp)]
    simp
  have hzero : ni_supNorm (iteratedDeriv 3 (fun x : ℝ => x ^ 2)) = 0 := by
    rw [hder, ni_supNorm]
    simp only [abs_zero]
    have hne : (Set.Icc (-1 : ℝ) 1).Nonempty := ⟨0, by norm_num, by norm_num⟩
    rw [hne.image_const, csSup_singleton]
  -- the interpolant is the constant `1/2`
  have hI : ni_chebInterp 1 (fun x => x ^ 2) = C (1 / 2) := by
    symm
    refine Lagrange.eq_interpolate_of_eval_eq _ (ni_chebNode_injOn 2) ?_ fun k hk => ?_
    · simp only [Nat.reduceAdd, Nat.card_Icc]
      exact lt_of_le_of_lt degree_C_le (by norm_num)
    · simp only [eval_C]
      have hk' : k = 1 ∨ k = 2 := by
        have := Finset.mem_Icc.mp hk
        omega
      rw [ni_chebNode, cos_sq]
      rcases hk' with rfl | rfl
      · have : 2 * (π * (2 * ((1 : ℕ) : ℝ) - 1) / (2 * ((1 + 1 : ℕ) : ℝ))) = π / 2 := by
          push_cast; ring
        rw [this, cos_pi_div_two]
        norm_num
      · have : 2 * (π * (2 * ((2 : ℕ) : ℝ) - 1) / (2 * ((1 + 1 : ℕ) : ℝ))) = π / 2 + π := by
          push_cast; ring
        rw [this, cos_add_pi, cos_pi_div_two]
        norm_num
  have hlow : (1 : ℝ) / 2 ≤
      ni_supNorm (fun x => x ^ 2 - (ni_chebInterp 1 (fun x => x ^ 2)).eval x) := by
    rw [hI, ni_supNorm]
    have hb : BddAbove ((fun x => |x ^ 2 - (C (1 / 2 : ℝ)).eval x|) '' Set.Icc (-1) 1) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      simp only [eval_C]
      rw [abs_le]
      constructor <;> nlinarith [hx.1, hx.2]
    have hmem : |(0 : ℝ) ^ 2 - (C (1 / 2 : ℝ)).eval 0| ∈
        (fun x => |x ^ 2 - (C (1 / 2 : ℝ)).eval x|) '' Set.Icc (-1) 1 :=
      ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩
    refine le_trans (le_of_eq ?_) (le_csSup hb hmem)
    simp only [eval_C]
    norm_num
  rw [hzero, mul_zero] at h1
  linarith

end Miao.NumericalMethods
