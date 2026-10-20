/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.TwoCapitalReduction

/-!
# Two capital goods: complementarity and the policy function

SLP §10.2, Exercise 10.2c, p. 290: "if `∂f/∂x₁` is increasing in `x₂` and `∂f/∂x₂` is increasing
in `x₁`, then `g(s) = [g₁(s), g₂(s)]` is strictly increasing in all its arguments."

* `TwoComplementsDeriv`: the book's complementarity condition; `TwoComplements`: its difference
  form, `f(a, b′) − f(a, b) ≤ f(a′, b′) − f(a′, b)` for `0 ≤ a ≤ a′`, `0 ≤ b ≤ b′` (increasing
  differences); `twoComplements_of_deriv`: the book's condition implies it.
* **`ex_10_2c`** (corrected): with i.i.d. shocks (Z2), (U4), `f` strictly concave and
  complementary, optimal choices are ordered by output `z f(x)`: `z f(x) ≤ z′ f(x′)` implies
  `g(x, z) ≤ g(x′, z′)` coordinatewise. `ex_10_2c_monotone`: `g₁` and `g₂` are nondecreasing in
  `x` and in `z`. The proof: total saving rises with output (exchange, (U4)); at a given total the
  split maximizes `f` (`v` depends on `x` only through `f(x)`, strictly increasingly, Ex. 10.2d);
  and by increasing differences of `(t, k) ↦ f(t, k − t)` (complementarity plus strict concavity
  of `f` in each argument, `strictConcave_increment`) the maximizing split rises in both goods
  with the total (Topkis's argument).
* **Correction** (`ex_10_2c_counterexample`, `ex_10_2c_not_strictMono`). "Strictly increasing" is
  false under the book's hypotheses of §10.2 ((U1)–(U5), (T1), (T3)–(T5), (Z1)–(Z2)), even with
  `f` strictly concave (needed for `g` to be a function, `ex_10_2b_counterexample`): with
  `U(c) = 1 − e^{−c}`, `f(x) = (1 − e^{−x₁}) + (1 − e^{−x₂})`, `β = 1/10`, `x̄ = 4`, `z̄ = 2`
  and any Feller `Q` (`twoSepF_hyp`, `twoSepF_strictConcave`, `contDiff_twoSepF`, `contDiff_cexU`,
  `twoSepF_complementsDeriv`: `∂f/∂x₁ = e^{−x₁}` does not depend on `x₂`),
  `v(y, z) − v(0, z) ≤ 2(y₁ + y₂)` (`twoSep_lipschitz`), so saving never pays at low output:
  `g(x, z) = 0` whenever `x₁ + x₂ ≤ 1/5`, and `g` is not strictly increasing in `x` or in `z`.
  This is the corner `g = 0` of Exercise 10.1d (`ex_10_1d_counterexample`): (U5) and (T5) are
  smoothness conditions, not Inada conditions. Corrected statement: `ex_10_2c_monotone`
  (nondecreasing). The case of Markov shocks (Z3) is not covered (as for Ex. 10.1f).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-! ### Complementarity -/

/-- The book's complementarity condition (Ex. 10.2c): `∂f/∂x₁` is nondecreasing in `x₂` and
`∂f/∂x₂` is nondecreasing in `x₁`, on `ℝ²₊`. -/
def TwoComplementsDeriv (f : ℝ × ℝ → ℝ) : Prop :=
  (∀ t b b', 0 ≤ t → 0 ≤ b → b ≤ b' →
    deriv (fun u => f (u, b)) t ≤ deriv (fun u => f (u, b')) t) ∧
  ∀ t a a', 0 ≤ t → 0 ≤ a → a ≤ a' → deriv (fun u => f (a, u)) t ≤ deriv (fun u => f (a', u)) t

/-- Complementarity in difference form (increasing differences, i.e. supermodularity on `ℝ²₊`):
for `0 ≤ a ≤ a′` and `0 ≤ b ≤ b′`, `f(a, b′) − f(a, b) ≤ f(a′, b′) − f(a′, b)`. -/
def TwoComplements (f : ℝ × ℝ → ℝ) : Prop :=
  ∀ a a' b b', 0 ≤ a → a ≤ a' → 0 ≤ b → b ≤ b' → f (a, b') - f (a, b) ≤ f (a', b') - f (a', b)

/-- The book's condition gives increasing differences when `f(·, b)` is continuous on `[0, ∞)`
and differentiable on `(0, ∞)`: `t ↦ f(t, b′) − f(t, b)` has nonnegative derivative. -/
theorem twoComplements_of_deriv {f : ℝ × ℝ → ℝ} (hc : ContinuousOn f quadrant)
    (hd : ∀ b, 0 ≤ b → ∀ t, 0 < t → DifferentiableAt ℝ (fun u => f (u, b)) t)
    (hf : TwoComplementsDeriv f) : TwoComplements f := by
  intro a a' b b' ha haa' hb hbb'
  set D : ℝ → ℝ := fun u => f (u, b') - f (u, b)
  have hsec : ∀ c, 0 ≤ c → ContinuousOn (fun u => f (u, c)) (Ici 0) := fun c hc0 =>
    hc.comp (by fun_prop) fun u hu => ⟨hu, hc0⟩
  have hDc : ContinuousOn D (Ici 0) := (hsec b' (hb.trans hbb')).sub (hsec b hb)
  have hDd : DifferentiableOn ℝ D (interior (Ici 0)) := by
    rw [interior_Ici]
    exact fun t ht => ((hd b' (hb.trans hbb') t ht).sub (hd b hb t ht)).differentiableWithinAt
  have hmono : MonotoneOn D (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hDc hDd fun t ht => ?_
    rw [interior_Ici] at ht
    have ht' : (0 : ℝ) < t := ht
    have : deriv D t = deriv (fun u => f (u, b')) t - deriv (fun u => f (u, b)) t :=
      deriv_sub (hd b' (hb.trans hbb') t ht') (hd b hb t ht')
    rw [this, sub_nonneg]
    exact hf.1 t b b' ht'.le hb hbb'
  have := hmono (mem_Ici.2 ha) (mem_Ici.2 (ha.trans haa')) haa'
  simpa [D] using this

/-! ### The counterexample -/

/-- `f(x) = (1 − e^{−x₁}) + (1 − e^{−x₂})`. -/
noncomputable def twoSepF (x : ℝ × ℝ) : ℝ := (1 - Real.exp (-x.1)) + (1 - Real.exp (-x.2))

/-- The example satisfies (U1)–(U3), (T1), (T3) and (Z1), with `z̄ f ≤ 2 z̄ = x̄` on `X`. -/
theorem twoSepF_hyp : TwoHyp cexU twoSepF (1 / 10) 4 2 where
  β_pos := by norm_num
  β_lt := by norm_num
  U_cont := cex_hyp.U_cont
  U_mono := cex_hyp.U_mono
  f_cont := by unfold twoSepF; fun_prop
  f_zero := by simp [twoSepF]
  f_mono := fun x x' _ hxx' hne => by
    have h1 := Real.exp_le_exp.2 (neg_le_neg hxx'.1)
    have h2 := Real.exp_le_exp.2 (neg_le_neg hxx'.2)
    simp only [twoSepF]
    rcases lt_or_eq_of_le hxx'.1 with hlt | heq
    · have := Real.exp_lt_exp.2 (neg_lt_neg hlt)
      linarith
    · have hlt : x.2 < x'.2 := lt_of_le_of_ne hxx'.2 fun h => hne (Prod.ext heq h)
      have := Real.exp_lt_exp.2 (neg_lt_neg hlt)
      linarith
  zbar_gt := by norm_num
  xbar_pos := by norm_num
  f_bound := fun x _ => by
    simp only [twoSepF]
    linarith [Real.exp_pos (-x.1), Real.exp_pos (-x.2)]

/-- (T4) strengthened: `f` is strictly concave on `ℝ²₊`. -/
theorem twoSepF_strictConcave : StrictConcaveOn ℝ quadrant twoSepF := by
  refine ⟨convex_quadrant, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have c1 := convexOn_exp.2 (mem_univ (-x.1)) (mem_univ (-y.1)) ha.le hb.le hab
  have c2 := convexOn_exp.2 (mem_univ (-x.2)) (mem_univ (-y.2)) ha.le hb.le hab
  simp only [smul_eq_mul] at c1 c2
  simp only [twoSepF, smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  have e1 : a * -x.1 + b * -y.1 = -(a * x.1 + b * y.1) := by ring
  have e2 : a * -x.2 + b * -y.2 = -(a * x.2 + b * y.2) := by ring
  rw [e1] at c1
  rw [e2] at c2
  by_cases h1 : x.1 = y.1
  · have h2 : x.2 ≠ y.2 := fun h => hxy (Prod.ext h1 h)
    have s2 := strictConvexOn_exp.2 (mem_univ (-x.2)) (mem_univ (-y.2))
      (fun h => h2 (neg_inj.1 h)) ha hb hab
    simp only [smul_eq_mul] at s2
    rw [e2] at s2
    nlinarith
  · have s1 := strictConvexOn_exp.2 (mem_univ (-x.1)) (mem_univ (-y.1))
      (fun h => h1 (neg_inj.1 h)) ha hb hab
    simp only [smul_eq_mul] at s1
    rw [e1] at s1
    nlinarith

/-- (T5): `f` is continuously differentiable. -/
theorem contDiff_twoSepF : ContDiff ℝ 1 twoSepF := by
  unfold twoSepF; fun_prop

/-- (U5): `U(c) = 1 − e^{−c}` is continuously differentiable. -/
theorem contDiff_cexU : ContDiff ℝ 1 cexU := by
  unfold cexU; fun_prop

/-- The example satisfies the book's complementarity condition: `∂f/∂x₁ = e^{−x₁}` does not
depend on `x₂`, and `∂f/∂x₂ = e^{−x₂}` does not depend on `x₁`. -/
theorem twoSepF_complementsDeriv : TwoComplementsDeriv twoSepF := by
  refine ⟨fun t b b' _ _ _ => le_of_eq ?_, fun t a a' _ _ _ => le_of_eq ?_⟩
  · have : (fun u => twoSepF (u, b')) =
        fun u => twoSepF (u, b) + (Real.exp (-b) - Real.exp (-b')) := by
      funext u; simp only [twoSepF]; ring
    rw [this, deriv_add_const]
  · have : (fun u => twoSepF (a', u)) =
        fun u => twoSepF (a, u) + (Real.exp (-a) - Real.exp (-a')) := by
      funext u; simp only [twoSepF]; ring
    rw [this, deriv_add_const]

/-- The example satisfies complementarity in difference form (with equality: `f` is additively
separable). -/
theorem twoSepF_complements : TwoComplements twoSepF := fun a a' b b' _ _ _ _ => by
  simp only [twoSepF]
  linarith

/-- `f(x) ≤ x₁ + x₂` on `ℝ²₊` (`1 − e^{−t} ≤ t`). -/
theorem twoSepF_le (x : ℝ × ℝ) : twoSepF x ≤ x.1 + x.2 := by
  simp only [twoSepF]
  linarith [Real.add_one_le_exp (-x.1), Real.add_one_le_exp (-x.2)]

/-- In the example, `v(y, z) − v(0, z) ≤ 2(y₁ + y₂)`: the set of such functions is closed and
mapped into itself by `T`, since `U(c) − U(0) ≤ c`, `β · 2 ≤ 1` and `z f(x) ≤ 2(x₁ + x₂)`. -/
theorem twoSep_lipschitz (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2)) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : twoX 4 × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : bellman (twoModel Q cexU twoSepF (1 / 10) 4) (two_boundedDP twoSepF_hyp Q hQ) v = v)
    (x : twoX 4) (z : Icc (1 : ℝ) 2) :
    v (x, z) - v (⟨(0, 0), by norm_num [twoX]⟩, z) ≤ 2 * (x.1.1 + x.1.2) := by
  set M := twoModel Q cexU twoSepF (1 / 10) 4
  have hb := two_boundedDP twoSepF_hyp Q hQ
  obtain ⟨x0, hx0⟩ : ∃ x0 : twoX 4, x0 = ⟨(0, 0), by norm_num [twoX]⟩ := ⟨_, rfl⟩
  rw [← hx0]
  set C : Set (twoX 4 × Icc (1 : ℝ) 2 →ᵇ ℝ) :=
    {w | ∀ x z, w (x, z) - w (x0, z) ≤ 2 * (x.1.1 + x.1.2)}
  have hclosed : IsClosed C := by
    have : C = ⋂ x, ⋂ z, {w : twoX 4 × Icc (1 : ℝ) 2 →ᵇ ℝ |
        w (x, z) - w (x0, z) ≤ 2 * (x.1.1 + x.1.2)} := by
      ext w; simp only [C, mem_ofPred_eq, mem_iInter]
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun z =>
      isClosed_le ((continuous_eval_const _).sub (continuous_eval_const _)) continuous_const
  have hx00 : x0.1 = (0, 0) := by rw [hx0]
  have hmaps : MapsTo (bellman M hb) C C := by
    intro w hw x z
    obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M hb w (x, z)
    obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb w (x0, z)
    have h0 : x0 ∈ M.Γ (x0, z) := by
      change x0.1.1 + x0.1.2 ≤ z.1 * twoSepF x0.1
      simp [hx00, twoSepF]
    have hm := hmax x0 h0
    have hint := integrable_section_v (Q z) w
    have hE : ∫ z', w (y, z') ∂Q z - ∫ z', w (x0, z') ∂Q z ≤ 2 * (y.1.1 + y.1.2) := by
      rw [← integral_sub (hint y) (hint x0)]
      have := integral_mono (μ := Q z) ((hint y).sub (hint x0))
        (integrable_const (2 * (y.1.1 + y.1.2))) fun z' => hw y z'
      simpa using this
    simp only [rhs, expV] at hval hm
    change bellman M hb w (x, z) =
      twoF cexU twoSepF 4 2 (x, y, z) + 1 / 10 * ∫ z', w (y, z') ∂Q z at hval
    change twoF cexU twoSepF 4 2 (x0, x0, z) + 1 / 10 * ∫ z', w (x0, z') ∂Q z ≤
      bellman M hb w (x0, z) at hm
    rw [twoF_of_mem hy] at hval
    have hF0 : twoF cexU twoSepF 4 2 (x0, x0, z) = 0 := by
      simp [twoF, hx00, cexU, twoSepF]
    rw [hF0] at hm
    have hyz : y.1.1 + y.1.2 ≤ z.1 * twoSepF x.1 := hy
    have hUc : cexU (z.1 * twoSepF x.1 - (y.1.1 + y.1.2)) ≤
        z.1 * twoSepF x.1 - (y.1.1 + y.1.2) := by
      simp only [cexU]
      linarith [Real.add_one_le_exp (-(z.1 * twoSepF x.1 - (y.1.1 + y.1.2)))]
    have hzf : z.1 * twoSepF x.1 ≤ 2 * (x.1.1 + x.1.2) := by
      have := mul_le_mul z.2.2 (twoSepF_le x.1)
        (twoSepF_hyp.f_nonneg (twoX_subset_quadrant x.2)) (by norm_num)
      linarith
    change bellman M hb w (x, z) - bellman M hb w (x0, z) ≤ 2 * (x.1.1 + x.1.2)
    linarith [y.2.1, y.2.2.1]
  have hzero : (0 : twoX 4 × Icc (1 : ℝ) 2 →ᵇ ℝ) ∈ C := fun x _ => by
    simp only [coe_zero, Pi.zero_apply, sub_self]
    linarith [x.2.1, x.2.2.1]
  exact (corollary_1 (bellman_contraction M hb) hv ⟨0, hzero⟩ hclosed hmaps hmaps).1 x z

/-- **Exercise 10.2c, corrected.** In the example, for any Feller `Q` (i.i.d. shocks included),
the only optimal choice at `x₁ + x₂ ≤ 1/5` is `y = 0`: the marginal utility `e^{−s} ≥ 3/5` of
consumption exceeds the bound `β · 2 = 1/5` on the marginal value of capital. -/
theorem ex_10_2c_counterexample (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2)) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : twoX 4 × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : bellman (twoModel Q cexU twoSepF (1 / 10) 4) (two_boundedDP twoSepF_hyp Q hQ) v = v)
    {x : twoX 4} (hx : x.1.1 + x.1.2 ≤ 1 / 5) (z : Icc (1 : ℝ) 2) {y : twoX 4}
    (hy : y ∈ policy (twoModel Q cexU twoSepF (1 / 10) 4) v (x, z)) : y.1 = (0, 0) := by
  set M := twoModel Q cexU twoSepF (1 / 10) 4
  have hb := two_boundedDP twoSepF_hyp Q hQ
  obtain ⟨x0, hx0⟩ : ∃ x0 : twoX 4, x0 = ⟨(0, 0), by norm_num [twoX]⟩ := ⟨_, rfl⟩
  have hx00 : x0.1 = (0, 0) := by rw [hx0]
  have hL := fun z' => twoSep_lipschitz Q hQ hv y z'
  rw [← hx0] at hL
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb v (x, z)
  have h0 : x0 ∈ M.Γ (x, z) := by
    change x0.1.1 + x0.1.2 ≤ z.1 * twoSepF x.1
    rw [hx00]
    simpa using mul_nonneg (by linarith [z.2.1] : (0 : ℝ) ≤ z.1)
      (twoSepF_hyp.f_nonneg (twoX_subset_quadrant x.2))
  have hm := hmax x0 h0
  rw [hv] at hm
  have hyv := hy.2
  have hint := integrable_section_v (Q z) v
  set k := y.1.1 + y.1.2
  have hE : ∫ z', v (y, z') ∂Q z - ∫ z', v (x0, z') ∂Q z ≤ 2 * k := by
    rw [← integral_sub (hint y) (hint x0)]
    have := integral_mono (μ := Q z) ((hint y).sub (hint x0)) (integrable_const (2 * k)) hL
    simpa using this
  simp only [rhs, expV] at hm hyv
  change twoF cexU twoSepF 4 2 (x, x0, z) + 1 / 10 * ∫ z', v (x0, z') ∂Q z ≤ v (x, z) at hm
  change v (x, z) = twoF cexU twoSepF 4 2 (x, y, z) + 1 / 10 * ∫ z', v (y, z') ∂Q z at hyv
  rw [twoF_of_mem h0, hx00] at hm
  rw [twoF_of_mem hy.1] at hyv
  simp only [add_zero, sub_zero] at hm
  -- output `s = z f(x) ≤ 2/5`
  set s := z.1 * twoSepF x.1
  have hs : s ≤ 2 / 5 := by
    have := mul_le_mul z.2.2 (twoSepF_le x.1)
      (twoSepF_hyp.f_nonneg (twoX_subset_quadrant x.2)) (by norm_num)
    linarith
  simp only [cexU] at hm hyv
  have hes : 3 / 5 ≤ Real.exp (-s) := by linarith [Real.add_one_le_exp (-s)]
  have hk0 : 0 ≤ k := add_nonneg y.2.1 y.2.2.1
  have hey : 1 + k ≤ Real.exp k := by linarith [Real.add_one_le_exp k]
  have hsplit : Real.exp (-(s - k)) = Real.exp k * Real.exp (-s) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit] at hyv
  have hpos := Real.exp_pos (-s)
  have k1 := mul_nonneg hpos.le (sub_nonneg.2 hey)
  have k2 := mul_nonneg hk0 (sub_nonneg.2 hes)
  have hk : k ≤ 0 := by linarith
  have h1 : y.1.1 = 0 := by linarith [y.2.1, y.2.2.1]
  have h2 : y.1.2 = 0 := by linarith [y.2.1, y.2.2.1]
  exact Prod.ext h1 h2

/-- **Exercise 10.2c, corrected.** In the example no selection `g` from `G` is strictly increasing
in `x` or in `z`: `g(0, z) = g((1/10, 0), z) = 0` and `g((1/10, 0), 1) = g((1/10, 0), 2) = 0`. -/
theorem ex_10_2c_not_strictMono (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2)) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : twoX 4 × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : bellman (twoModel Q cexU twoSepF (1 / 10) 4) (two_boundedDP twoSepF_hyp Q hQ) v = v)
    {g : twoX 4 × Icc (1 : ℝ) 2 → twoX 4}
    (hg : ∀ s, g s ∈ policy (twoModel Q cexU twoSepF (1 / 10) 4) v s) :
    (∀ z, ¬ StrictMono fun x => g (x, z)) ∧ ∀ x, x.1.1 + x.1.2 ≤ 1 / 5 →
      ¬ StrictMono fun z => g (x, z) := by
  set a : twoX 4 := ⟨(0, 0), by norm_num [twoX]⟩
  set b : twoX 4 := ⟨(1 / 10, 0), by norm_num [twoX]⟩
  have hzero : ∀ x : twoX 4, x.1.1 + x.1.2 ≤ 1 / 5 → ∀ z, g (x, z) = a := fun x hx z =>
    Subtype.ext (ex_10_2c_counterexample Q hQ hv hx z (hg _))
  refine ⟨fun z hmono => ?_, fun x hx hmono => ?_⟩
  · have hab : a < b := lt_of_le_of_ne (show (0, 0) ≤ ((1 / 10 : ℝ), (0 : ℝ)) by
      constructor <;> norm_num) fun h => by
        have := congrArg (fun p : twoX 4 => p.1.1) h
        norm_num [a, b] at this
    have := hmono hab
    dsimp only at this
    rw [hzero a (by norm_num [a]) z, hzero b (by norm_num [b]) z] at this
    exact lt_irrefl _ this
  · have h12 : (⟨1, le_rfl, by norm_num⟩ : Icc (1 : ℝ) 2) < ⟨2, by norm_num, le_rfl⟩ :=
      show (1 : ℝ) < 2 by norm_num
    have := hmono h12
    dsimp only at this
    rw [hzero x hx, hzero x hx] at this
    exact lt_irrefl _ this

/-! ### Exercise 10.2c, corrected: `g` is nondecreasing -/

variable {U : ℝ → ℝ} {f : ℝ × ℝ → ℝ} {β xbar zbar : ℝ}

/-- For `φ` strictly concave on `[0, ∞)`, `0 ≤ p < q` and `h > 0`: increments over `[p, p + h]`
exceed those over `[q, q + h]`, `φ(p) + φ(q + h) < φ(p + h) + φ(q)`. -/
theorem strictConcave_increment {φ : ℝ → ℝ} (hφ : StrictConcaveOn ℝ (Ici 0) φ) {p q h : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hh : 0 < h) : φ p + φ (q + h) < φ (p + h) + φ q := by
  rcases le_or_gt (p + h) q with h1 | h1
  · exact strictConcave_exchange hφ (q := p + h) (r := q) (t := q + h) (mem_Ici.2 hp)
      (mem_Ici.2 (by linarith)) (by linarith) (by linarith) (by ring)
  · have := strictConcave_exchange hφ (p := p) (q := q) (r := p + h) (t := q + h) (mem_Ici.2 hp)
      (mem_Ici.2 (by linarith)) hpq (by linarith) (by ring)
    linarith

/-- A strictly concave `f` on `ℝ²₊` is strictly concave in `x₂` for fixed `x₁ = c ≥ 0`. -/
theorem strictConcaveOn_snd_section (hf : StrictConcaveOn ℝ quadrant f) {c : ℝ} (hc : 0 ≤ c) :
    StrictConcaveOn ℝ (Ici 0) fun t => f (c, t) := by
  refine ⟨convex_Ici 0, fun t ht t' ht' hne a b ha hb hab => ?_⟩
  have := hf.2 (x := (c, t)) (y := (c, t')) ⟨hc, ht⟩ ⟨hc, ht'⟩
    (fun h => hne (congrArg Prod.snd h)) ha hb hab
  have e : a • ((c, t) : ℝ × ℝ) + b • (c, t') = (c, a • t + b • t') := by
    refine Prod.ext ?_ rfl
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  rw [e] at this
  exact this

/-- A strictly concave `f` on `ℝ²₊` is strictly concave in `x₁` for fixed `x₂ = c ≥ 0`. -/
theorem strictConcaveOn_fst_section (hf : StrictConcaveOn ℝ quadrant f) {c : ℝ} (hc : 0 ≤ c) :
    StrictConcaveOn ℝ (Ici 0) fun t => f (t, c) := by
  refine ⟨convex_Ici 0, fun t ht t' ht' hne a b ha hb hab => ?_⟩
  have := hf.2 (x := (t, c)) (y := (t', c)) ⟨ht, hc⟩ ⟨ht', hc⟩
    (fun h => hne (congrArg Prod.fst h)) ha hb hab
  have e : a • ((t, c) : ℝ × ℝ) + b • (t', c) = (a • t + b • t', c) := by
    refine Prod.ext rfl ?_
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  rw [e] at this
  exact this

variable [Nonempty (twoX xbar)] in
/-- **Exercise 10.2c, corrected.** With i.i.d. shocks (`Q(z, ·) = λ`), (U4), `f` strictly concave
and complementary (`TwoComplements`), optimal choices are ordered by output: if
`z f(x) ≤ z′ f(x′)`, `y ∈ G(x, z)` and `y′ ∈ G(x′, z′)`, then `y₁ ≤ y₁′` and `y₂ ≤ y₂′`.
Total saving `y₁ + y₂` rises with output (exchange, (U4)); at a given total the split maximizes
`f` (`v` depends on `x` only through `f(x)`, strictly increasingly, by Ex. 10.2d); and the
maximizing split moves up in both goods as the total rises (increasing differences: Topkis's
argument, strict by the strict concavity of `f`). -/
theorem ex_10_2c (h : TwoHyp U f β xbar zbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : StrictConcaveOn ℝ quadrant f) (hc : TwoComplements f)
    (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (twoModel (Kernel.const _ lam) U f β xbar)
      (two_boundedDP h _ (isFeller_const lam)) v = v)
    {s s' : twoX xbar × Icc (1 : ℝ) zbar} (hss' : s.2.1 * f s.1.1 ≤ s'.2.1 * f s'.1.1)
    {y y' : twoX xbar} (hy : y ∈ policy (twoModel (Kernel.const _ lam) U f β xbar) v s)
    (hy' : y' ∈ policy (twoModel (Kernel.const _ lam) U f β xbar) v s') : y ≤ y' := by
  set Q := Kernel.const (Icc (1 : ℝ) zbar) lam
  have hQ : IsFeller Q := isFeller_const lam
  set M := twoModel Q U f β xbar
  have hbd := two_boundedDP h Q hQ
  set W : twoX xbar → ℝ := fun u => ∫ z', v (u, z') ∂lam with hW
  have hβ := h.β_pos
  -- the objective
  have hrhs : ∀ (t : twoX xbar × Icc (1 : ℝ) zbar) (u : twoX xbar), u ∈ M.Γ t →
      rhs M v t u = U (t.2.1 * f t.1.1 - (u.1.1 + u.1.2)) + β * W u := fun t u hu => by
    simp only [rhs, expV]
    change twoF U f xbar zbar (t.1, u, t.2) + β * ∫ z', v (u, z') ∂Q t.2 = _
    rw [twoF_of_mem hu, Kernel.const_apply]
  have hle : ∀ t (u : twoX xbar), u ∈ M.Γ t → rhs M v t u ≤ v t := fun t u hu => by
    obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hbd v t
    have := hmax u hu
    rwa [hv] at this
  -- the policy is single-valued (Ex. 10.2b)
  obtain ⟨v₀, hv₀, huniq, -, -, hpol, -⟩ := ex_10_2b h hU.concaveOn hf Q hQ
  have hvv : v = v₀ := huniq v hv
  have hsingle : ∀ t (a b : twoX xbar), a ∈ policy M v t → b ∈ policy M v t → a = b := by
    intro t a b ha hb
    rw [hvv, hpol t] at ha hb
    exact ha.trans hb.symm
  -- `v` is strictly increasing in output (Ex. 10.2d)
  obtain ⟨v₁, hv₁, -⟩ := ex_9_7b (growthModel Q U (twoφ f) β xbar)
    (growth_boundedDP (twoφ_hyp h) Q hQ)
  obtain ⟨hk, hvk⟩ := ex_10_2d h Q hQ hv hv₁
  have hvf : ∀ (a b : twoX xbar) z', f a.1 < f b.1 → v (a, z') < v (b, z') := by
    intro a b z' hab
    obtain ⟨ka, -, hka⟩ := hk a
    obtain ⟨kb, -, hkb⟩ := hk b
    rw [hvk a ka z' hka.symm, hvk b kb z' hkb.symm]
    refine growth_strictMono (twoφ_hyp h) Q hQ hv₁ z' ?_
    by_contra hba
    rw [not_lt] at hba
    have := (twoφ_hyp h).f_mono.monotoneOn kb.2.1 ka.2.1 hba
    linarith
  have hWlt : ∀ a b : twoX xbar, f a.1 < f b.1 → W a < W b := by
    intro a b hab
    have hint := integrable_section_v lam v
    have hpos : 0 < ∫ z', (v (b, z') - v (a, z')) ∂lam := by
      rw [integral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun z' => (sub_pos.2 (hvf a b z' hab)).le) ((hint b).sub (hint a))]
      have : Function.support (fun z' => v (b, z') - v (a, z')) = univ :=
        eq_univ_of_forall fun z' => (sub_pos.2 (hvf a b z' hab)).ne'
      rw [this, measure_univ]
      exact zero_lt_one
    rw [integral_sub (hint b) (hint a)] at hpos
    simp only [hW]
    linarith
  -- notation
  set w := s.2.1 * f s.1.1 with hw
  set w' := s'.2.1 * f s'.1.1 with hw'
  set K := y.1.1 + y.1.2 with hK
  set K' := y'.1.1 + y'.1.2 with hK'
  have hyK : K ≤ w := hy.1
  have hyK' : K' ≤ w' := hy'.1
  have hvs : v s = U (w - K) + β * W y := by rw [hy.2, hrhs s y hy.1]
  have hvs' : v s' = U (w' - K') + β * W y' := by rw [hy'.2, hrhs s' y' hy'.1]
  have hopt : ∀ u : twoX xbar, u.1.1 + u.1.2 ≤ w →
      U (w - (u.1.1 + u.1.2)) + β * W u ≤ U (w - K) + β * W y := fun u hu => by
    rw [← hvs, ← hrhs s u hu]; exact hle s u hu
  have hopt' : ∀ u : twoX xbar, u.1.1 + u.1.2 ≤ w' →
      U (w' - (u.1.1 + u.1.2)) + β * W u ≤ U (w' - K') + β * W y' := fun u hu => by
    rw [← hvs', ← hrhs s' u hu]; exact hle s' u hu
  -- if `y′` does as well as `y` at `s`, then `y′ = y`
  have hsame : U (w - K') + β * W y' = U (w - K) + β * W y → K' ≤ w → y = y' := fun he hK'w =>
    hsingle s y y' hy ⟨hK'w, by rw [hrhs s y' hK'w, he, hvs]⟩
  rcases eq_or_lt_of_le hss' with hww | hww
  · -- equal outputs: the same problem
    have h1 := hopt y' (by rw [hww]; exact hyK')
    have h2 := hopt' y (by rw [← hww]; exact hyK)
    rw [← hww] at h2
    exact (hsame (le_antisymm h1 h2) (hww ▸ hyK')).le
  -- total saving rises with output
  have hKK : K ≤ K' := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 := hopt y' (by linarith)
    have h2 := hopt' y (by linarith)
    have := strictConcave_exchange hU (p := w - K) (q := w - K') (r := w' - K) (t := w' - K')
      (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) (by linarith) (by linarith) (by ring)
    linarith
  rcases eq_or_lt_of_le hKK with hKe | hKl
  · -- equal totals: `W y = W y′`, so `y′` is optimal at `s`
    have h1 := hopt y' (by linarith)
    have h2 := hopt' y (by linarith)
    rw [← hK', ← hKe] at h1
    rw [← hK, ← hKe] at h2
    have e1 : W y' ≤ W y := le_of_mul_le_mul_left (by linarith) hβ
    have e2 : W y ≤ W y' := le_of_mul_le_mul_left (by linarith) hβ
    exact (hsame (by rw [← hKe, le_antisymm e1 e2]) (by linarith)).le
  -- at its total, each choice maximizes `f`
  have hfmax : ∀ u : twoX xbar, u.1.1 + u.1.2 = K → f u.1 ≤ f y.1 := fun u hu => by
    by_contra hlt
    rw [not_le] at hlt
    have hWl := mul_lt_mul_of_pos_left (hWlt y u hlt) hβ
    have h1 := hopt u (by rw [hu]; exact hyK)
    rw [hu] at h1
    linarith
  have hfmax' : ∀ u : twoX xbar, u.1.1 + u.1.2 = K' → f u.1 ≤ f y'.1 := fun u hu => by
    by_contra hlt
    rw [not_le] at hlt
    have hWl := mul_lt_mul_of_pos_left (hWlt y' u hlt) hβ
    have h1 := hopt' u (by rw [hu]; exact hyK')
    rw [hu] at h1
    linarith
  have hy0 := y.2.1
  have hy1 := y.2.2.1
  have hy2 : y.1.1 + y.1.2 ≤ xbar := y.2.2.2
  have hy0' := y'.2.1
  have hy1' := y'.2.2.1
  have hy2' : y'.1.1 + y'.1.2 ≤ xbar := y'.2.2.2
  refine ⟨?_, ?_⟩
  · -- the first good
    by_contra hlt
    rw [not_le] at hlt
    have hA := hfmax ⟨(y'.1.1, K - y'.1.1), hy0', by simp only; linarith, by simp only; linarith⟩
      (by simp only; ring)
    have hB := hfmax' ⟨(y.1.1, K' - y.1.1), hy0, by simp only; linarith, by simp only; linarith⟩
      (by simp only; ring)
    simp only at hA hB
    have hinc := strictConcave_increment (strictConcaveOn_snd_section hf hy0)
      (p := K - y.1.1) (q := K - y'.1.1) (h := K' - K) (by linarith) (by linarith) (by linarith)
    have hsup := hc y'.1.1 y.1.1 (K - y'.1.1) (K' - y'.1.1) hy0' hlt.le (by linarith)
      (by linarith)
    have e1 : K - y'.1.1 + (K' - K) = K' - y'.1.1 := by ring
    have e2 : K - y.1.1 + (K' - K) = K' - y.1.1 := by ring
    have e3 : K - y.1.1 = y.1.2 := by rw [hK]; ring
    have e4 : K' - y'.1.1 = y'.1.2 := by rw [hK']; ring
    rw [e1, e2] at hinc
    have hfyK : f y.1 = f (y.1.1, K - y.1.1) := by rw [e3]
    have hfyK' : f y'.1 = f (y'.1.1, K' - y'.1.1) := by rw [e4]
    rw [hfyK] at hA
    rw [hfyK'] at hB
    linarith
  · -- the second good
    by_contra hlt
    rw [not_le] at hlt
    have hA := hfmax ⟨(K - y'.1.2, y'.1.2), by simp only; linarith, hy1', by simp only; linarith⟩
      (by simp only; ring)
    have hB := hfmax' ⟨(K' - y.1.2, y.1.2), by simp only; linarith, hy1, by simp only; linarith⟩
      (by simp only; ring)
    simp only at hA hB
    have hinc := strictConcave_increment (strictConcaveOn_fst_section hf hy1)
      (p := K - y.1.2) (q := K - y'.1.2) (h := K' - K) (by linarith) (by linarith) (by linarith)
    have hsup := hc (K - y'.1.2) (K' - y'.1.2) y'.1.2 y.1.2 (by linarith) (by linarith) hy1'
      hlt.le
    have e1 : K - y'.1.2 + (K' - K) = K' - y'.1.2 := by ring
    have e2 : K - y.1.2 + (K' - K) = K' - y.1.2 := by ring
    have e3 : K - y.1.2 = y.1.1 := by rw [hK]; ring
    have e4 : K' - y'.1.2 = y'.1.1 := by rw [hK']; ring
    rw [e1, e2] at hinc
    have hfyK : f y.1 = f (K - y.1.2, y.1.2) := by rw [e3]
    have hfyK' : f y'.1 = f (K' - y'.1.2, y'.1.2) := by rw [e4]
    rw [hfyK] at hA
    rw [hfyK'] at hB
    linarith

variable [Nonempty (twoX xbar)] in
/-- **Exercise 10.2c, corrected** (the policy function). Under the hypotheses of `ex_10_2c`, the
policy function `g = (g₁, g₂)` of Ex. 10.2b is nondecreasing in `x` (coordinatewise) and in `z`:
both `g₁` and `g₂` are nondecreasing in all arguments. (Not strictly:
`ex_10_2c_not_strictMono`.) -/
theorem ex_10_2c_monotone (h : TwoHyp U f β xbar zbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : StrictConcaveOn ℝ quadrant f) (hc : TwoComplements f)
    (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : twoX xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (twoModel (Kernel.const _ lam) U f β xbar)
      (two_boundedDP h _ (isFeller_const lam)) v = v) :
    (∀ z, Monotone fun x => argmaxFn (twoΓ f xbar zbar)
      (objG (twoModel (Kernel.const _ lam) U f β xbar) v) (x, z)) ∧
    ∀ x, Monotone fun z => argmaxFn (twoΓ f xbar zbar)
      (objG (twoModel (Kernel.const _ lam) U f β xbar) v) (x, z) := by
  obtain ⟨v₀, hv₀, huniq, -, -, hpol, -⟩ :=
    ex_10_2b h hU.concaveOn hf (Kernel.const _ lam) (isFeller_const lam)
  have hvv : v = v₀ := huniq v hv
  have hmem : ∀ s, argmaxFn (twoΓ f xbar zbar)
      (objG (twoModel (Kernel.const _ lam) U f β xbar) v) s ∈
        policy (twoModel (Kernel.const _ lam) U f β xbar) v s := fun s => by
    rw [hvv, hpol s]
    exact rfl
  refine ⟨fun z x x' hxx' => ex_10_2c h hU hf hc lam hv ?_ (hmem _) (hmem _),
    fun x z z' hzz' => ex_10_2c h hU hf hc lam hv ?_ (hmem _) (hmem _)⟩
  · exact mul_le_mul_of_nonneg_left (h.f_le (twoX_subset_quadrant x.2) hxx')
      (by linarith [z.2.1])
  · exact mul_le_mul_of_nonneg_right hzz' (h.f_nonneg (twoX_subset_quadrant x.2))

end StokeyLucasPrescott.StochasticApplications
