/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MathematicalPreliminaries.Completeness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Spaces of continuously differentiable functions

SLP Exercise 3.7, p. 49. A function in `C^k[a, b]` is recorded with its derivatives: a tuple
`F : Fin (k + 1) → C[a, b]` with `F (i + 1) = (F i)′` on `[a, b]` (one-sided at the ends).

* `ckSub`: `C^k[a, b]` as a vector space; `ckNorm α F = ∑ᵢ αᵢ max |F i|`.
* `isCk_iff_integral`: the derivative relations are equivalent to
  `F i (s) = F i (a) + ∫ₐˢ F (i + 1)`.
* `isClosed_ckSub`, `isComplete_ckNorm`: with every `αᵢ > 0` the norm is complete (Ex 3.7c,
  "if"); `ex_3_7a` is the case `k = 1`, `α = (1, 1)`.
* `ex_3_7b`: under `max |f|` alone, `C¹[a, b]` is not complete; the sequence
  `√((t − c)² + 1/(n + 1))` is Cauchy but its limit `|t − c|` is not differentiable, and it is not
  Cauchy in the norm of (a).
* `ex_3_7c_counterexample`: the book's "only if" is false: on `C²[a, b]`,
  `max |f| + max |f″|` (`α = (1, 0, 1)`) is a complete norm, by the interpolation inequality
  `interpolation`. `not_isNorm_of_alpha0`: with `α₀ = 0` the formula is not a norm.
-/

open Set Filter Topology MeasureTheory intervalIntegral

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {a b : ℝ}

theorem ext_zero (hab : a ≤ b) (t : ℝ) : ext hab (0 : C(Icc a b, ℝ)) t = 0 := by
  simpa using ext_smul hab 0 0 t

/-- `|x(t)| ≤ max |x|` for the extension of `x ∈ C[a, b]`. -/
theorem abs_ext_le (hab : a ≤ b) (x : C(Icc a b, ℝ)) (t : ℝ) : |ext hab x t| ≤ ‖x‖ := by
  change |x (projIcc a b hab t)| ≤ ‖x‖
  rw [← Real.norm_eq_abs]
  exact x.norm_coe_le_norm _

/-- `F (i + 1)` is the derivative of `F i` on `[a, b]`, for `i < k`. -/
def IsCk (hab : a ≤ b) (k : ℕ) (F : Fin (k + 1) → C(Icc a b, ℝ)) : Prop :=
  ∀ i : Fin k, ∀ s ∈ Icc a b,
    HasDerivWithinAt (ext hab (F i.castSucc)) (ext hab (F i.succ) s) (Icc a b) s

/-- `C^k[a, b]` (with the derivatives recorded) is a vector space. -/
def ckSub (hab : a ≤ b) (k : ℕ) : Submodule ℝ (Fin (k + 1) → C(Icc a b, ℝ)) where
  carrier := {F | IsCk hab k F}
  zero_mem' i s _ := by
    have : ext hab (0 : C(Icc a b, ℝ)) = fun _ => 0 := funext (ext_zero hab)
    simp only [Pi.zero_apply]
    rw [this]
    exact hasDerivWithinAt_const s _ 0
  add_mem' {F G} hF hG i s hs := by
    have h := (hF i s hs).add (hG i s hs)
    simp only [Pi.add_apply]
    rw [ext_add]
    exact h.congr (fun t _ => ext_add hab _ _ t) (ext_add hab _ _ s)
  smul_mem' r F hF i s hs := by
    have h := (hF i s hs).const_mul r
    simp only [Pi.smul_apply]
    rw [ext_smul]
    exact h.congr (fun t _ => ext_smul hab _ _ t) (ext_smul hab _ _ s)

/-- `‖F‖ = ∑ᵢ αᵢ max_{t ∈ [a,b]} |F i (t)|`. -/
noncomputable def ckNorm {k : ℕ} (α : Fin (k + 1) → ℝ) (F : Fin (k + 1) → C(Icc a b, ℝ)) : ℝ :=
  ∑ i, α i * ‖F i‖

/-- The derivative relations hold iff each `F i` is the integral of `F (i + 1)`. -/
theorem isCk_iff_integral (hab : a ≤ b) {k : ℕ} (F : Fin (k + 1) → C(Icc a b, ℝ)) :
    IsCk hab k F ↔ ∀ i : Fin k, ∀ s ∈ Icc a b,
      ext hab (F i.castSucc) s = ext hab (F i.castSucc) a + ∫ t in a..s, ext hab (F i.succ) t := by
  constructor
  · intro hF i s hs
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl hs.2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
      (continuous_ext hab _).continuousOn (fun z hz => ?_)
      ((continuous_ext hab _).intervalIntegrable _ _)]
    · ring
    · exact (hF i z (hsub (Ioo_subset_Icc_self hz))).hasDerivAt
        (Icc_mem_nhds hz.1 (hz.2.trans_le hs.2))
  · intro hF i s hs
    have hd : HasDerivAt (fun u => ext hab (F i.castSucc) a + ∫ t in a..u, ext hab (F i.succ) t)
        (ext hab (F i.succ) s) s :=
      ((continuous_ext hab _).integral_hasStrictDerivAt a s).hasDerivAt.const_add _
    exact hd.hasDerivWithinAt.congr (fun u hu => hF i u hu) (hF i s hs)

/-- `C^k[a, b]` is closed in `C[a, b]^{k+1}` under the sup norm on each coordinate. -/
theorem isClosed_ckSub (hab : a ≤ b) (k : ℕ) :
    IsClosed (ckSub hab k : Set (Fin (k + 1) → C(Icc a b, ℝ))) := by
  have hev : ∀ (j : Fin (k + 1)) (s : ℝ),
      Continuous fun F : Fin (k + 1) → C(Icc a b, ℝ) => ext hab (F j) s := fun j s =>
    continuous_eval.comp ((continuous_apply j).prodMk continuous_const)
  have hint : ∀ (j : Fin (k + 1)) (s : ℝ),
      Continuous fun F : Fin (k + 1) → C(Icc a b, ℝ) => ∫ t in a..s, ext hab (F j) t :=
    fun j s => intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (F : Fin (k + 1) → C(Icc a b, ℝ)) t => ext hab (F j) t) (μ := volume)
      (continuous_eval.comp (((continuous_apply j).comp continuous_fst).prodMk
        ((continuous_projIcc (h := hab)).comp continuous_snd))) a s
  have : (ckSub hab k : Set (Fin (k + 1) → C(Icc a b, ℝ))) = ⋂ i : Fin k, ⋂ s ∈ Icc a b,
      {F | ext hab (F i.castSucc) s = ext hab (F i.castSucc) a +
        ∫ t in a..s, ext hab (F i.succ) t} := by
    ext F
    simp only [SetLike.mem_coe, mem_iInter]
    exact isCk_iff_integral hab F
  rw [this]
  exact isClosed_iInter fun i => isClosed_biInter fun s _ =>
    isClosed_eq (hev _ s) ((hev _ a).add (hint _ s))

/-- **Ex 3.7c ("if").** With every `αᵢ > 0`, `ckNorm α` is a norm on `C^k[a, b]`. -/
theorem isNorm_ckNorm (hab : a ≤ b) {k : ℕ} {α : Fin (k + 1) → ℝ} (hα : ∀ i, 0 < α i) :
    IsNorm fun F : ckSub hab k => ckNorm α F.1 where
  nonneg F := Finset.sum_nonneg fun i _ => mul_nonneg (hα i).le (norm_nonneg _)
  eq_zero F := by
    constructor
    · intro h
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_nonneg (hα i).le (norm_nonneg (F.1 i))).1 h
      ext1
      funext i
      exact norm_eq_zero.1 ((mul_eq_zero.1 (h0 i (Finset.mem_univ i))).resolve_left (hα i).ne')
    · rintro rfl
      simp [ckNorm]
  smul r F := by
    simp only [ckNorm, Submodule.coe_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  triangle F G := by
    simp only [ckNorm, Submodule.coe_add, Pi.add_apply, ← Finset.sum_add_distrib, ← mul_add]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (norm_add_le _ _) (hα i).le

/-- Each coordinate is bounded by the weighted norm. -/
theorem norm_le_ckNorm {k : ℕ} {α : Fin (k + 1) → ℝ} (hα : ∀ i, 0 < α i)
    (F : Fin (k + 1) → C(Icc a b, ℝ)) :
    ‖F‖ ≤ ckNorm α F / Finset.univ.inf' Finset.univ_nonempty α := by
  have hm : 0 < Finset.univ.inf' Finset.univ_nonempty α :=
    (Finset.lt_inf'_iff _).2 fun i _ => hα i
  have hN : 0 ≤ ckNorm α F := Finset.sum_nonneg fun i _ => mul_nonneg (hα i).le (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg (div_nonneg hN hm.le)).2 fun i => ?_
  rw [le_div_iff₀ hm]
  calc ‖F i‖ * Finset.univ.inf' Finset.univ_nonempty α ≤ ‖F i‖ * α i :=
        mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ i)) (norm_nonneg _)
    _ = α i * ‖F i‖ := mul_comm _ _
    _ ≤ ckNorm α F := Finset.single_le_sum (f := fun j => α j * ‖F j‖)
        (fun j _ => mul_nonneg (hα j).le (norm_nonneg _)) (Finset.mem_univ i)

/-- The weighted norm is bounded by `∑ αᵢ` times the sup over coordinates. -/
theorem ckNorm_le {k : ℕ} {α : Fin (k + 1) → ℝ} (hα : ∀ i, 0 ≤ α i)
    (F : Fin (k + 1) → C(Icc a b, ℝ)) : ckNorm α F ≤ (∑ i, α i) * ‖F‖ := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm F i) (hα i)

/-- **Ex 3.7c ("if").** With every `αᵢ > 0`, `C^k[a, b]` is complete under `ckNorm α`. -/
theorem isComplete_ckNorm (hab : a ≤ b) {k : ℕ} {α : Fin (k + 1) → ℝ} (hα : ∀ i, 0 < α i) :
    IsCompleteFor fun F G : ckSub hab k => ckNorm α (F.1 - G.1) := by
  intro x hx
  have hm : 0 < Finset.univ.inf' Finset.univ_nonempty α :=
    (Finset.lt_inf'_iff _).2 fun i _ => hα i
  have hcs : CauchySeq fun n => (x n).1 := Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hx (Finset.univ.inf' Finset.univ_nonempty α * ε) (mul_pos hm hε)
    refine ⟨N, fun p hp q hq => ?_⟩
    rw [dist_eq_norm]
    refine (norm_le_ckNorm hα _).trans_lt ?_
    rw [div_lt_iff₀ hm, mul_comm ε]
    exact hN p hp q hq
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have hLmem : L ∈ ckSub hab k :=
    (isClosed_ckSub hab k).mem_of_tendsto hL (Eventually.of_forall fun n => (x n).2)
  have hA : 0 < ∑ i, α i := Finset.sum_pos (fun i _ => hα i) Finset.univ_nonempty
  refine ⟨⟨L, hLmem⟩, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hL (ε / ∑ i, α i) (div_pos hε hA)
  refine ⟨N, fun n hn => ?_⟩
  calc ckNorm α ((x n).1 - L) ≤ (∑ i, α i) * ‖(x n).1 - L‖ := ckNorm_le (fun i => (hα i).le) _
    _ < (∑ i, α i) * (ε / ∑ i, α i) := by
        rw [← dist_eq_norm]; exact mul_lt_mul_of_pos_left (hN n hn) hA
    _ = ε := mul_div_cancel₀ _ hA.ne'

/-- **Ex 3.7a.** `C¹[a, b]` with `‖f‖ = max |f| + max |f′|` is a Banach space. -/
theorem ex_3_7a (hab : a ≤ b) :
    IsNorm (fun F : ckSub hab 1 => ‖F.1 0‖ + ‖F.1 1‖) ∧
      IsCompleteFor fun F G : ckSub hab 1 => ‖F.1 0 - G.1 0‖ + ‖F.1 1 - G.1 1‖ := by
  have hα : ∀ i, 0 < (fun _ : Fin 2 => (1 : ℝ)) i := fun _ => one_pos
  have h : ∀ F : Fin 2 → C(Icc a b, ℝ), ckNorm (fun _ => 1) F = ‖F 0‖ + ‖F 1‖ := fun F => by
    simp [ckNorm, Fin.sum_univ_two]
  constructor
  · have := isNorm_ckNorm hab hα
    simp only [h] at this
    exact this
  · have := isComplete_ckNorm hab hα
    simp only [h, Pi.sub_apply] at this
    exact this

/-! ### Exercise 3.7b: the sup norm on `C¹` -/

/-- A continuous `g : ℝ → ℝ` restricted to `[a, b]`. -/
def restrictC {g : ℝ → ℝ} (hg : Continuous g) : C(Icc a b, ℝ) :=
  ⟨fun u => g u, hg.comp continuous_subtype_val⟩

theorem ext_restrictC (hab : a ≤ b) {g : ℝ → ℝ} (hg : Continuous g) {t : ℝ} (ht : t ∈ Icc a b) :
    ext hab (restrictC hg) t = g t := by
  rw [ext_of_mem hab _ ht]; rfl

/-- A function differentiable on `ℝ` with continuous derivative gives an element of `C¹[a, b]`. -/
def mk1 (hab : a ≤ b) {g g' : ℝ → ℝ} (hg : Continuous g) (hg' : Continuous g')
    (hd : ∀ s, HasDerivAt g (g' s) s) : ckSub hab 1 :=
  ⟨![restrictC hg, restrictC hg'], fun i s hs => by
    rw [Subsingleton.elim i 0]
    change HasDerivWithinAt (ext hab (restrictC hg)) (ext hab (restrictC hg') s) (Icc a b) s
    rw [ext_restrictC hab hg' hs]
    exact (hd s).hasDerivWithinAt.congr (fun t ht => ext_restrictC hab hg ht)
      (ext_restrictC hab hg hs)⟩

/-- **Ex 3.7b.** On `C¹[a, b]` (`a < b`), `max |f|` is a norm. -/
theorem isNorm_sup_C1 (hab : a < b) : IsNorm fun F : ckSub hab.le 1 => ‖F.1 0‖ where
  nonneg _ := norm_nonneg _
  eq_zero F := by
    constructor
    · intro h
      have h0 : F.1 0 = 0 := norm_eq_zero.1 h
      -- the derivative of the zero function is zero
      have h1 : F.1 1 = 0 := by
        ext u
        have hd := F.2 0 u u.2
        change HasDerivWithinAt (ext hab.le (F.1 0)) (ext hab.le (F.1 1) u) (Icc a b) u at hd
        rw [h0, show ext hab.le (0 : C(Icc a b, ℝ)) = fun _ => 0 from funext (ext_zero hab.le)]
          at hd
        have := (uniqueDiffOn_Icc hab u u.2).eq_deriv _ hd (hasDerivWithinAt_const _ _ 0)
        rw [ext_of_mem hab.le _ u.2] at this
        simpa using this
      ext1
      funext i
      fin_cases i
      · exact h0
      · exact h1
    · rintro rfl; simp
  smul r F := by simp [norm_smul]
  triangle F G := by simpa using norm_add_le (F.1 0) (G.1 0)

/-- `√((t − c)² + 1/(n + 1))`. -/
noncomputable def sqrtSeq (c : ℝ) (n : ℕ) (t : ℝ) : ℝ := √((t - c) ^ 2 + 1 / ((n : ℝ) + 1))

/-- Its derivative `(t − c)/√((t − c)² + 1/(n + 1))`. -/
noncomputable def sqrtSeq' (c : ℝ) (n : ℕ) (t : ℝ) : ℝ := (t - c) / sqrtSeq c n t

theorem sqrtSeq_pos (c : ℝ) (n : ℕ) (t : ℝ) : 0 < sqrtSeq c n t :=
  Real.sqrt_pos.2 (by positivity)

theorem continuous_sqrtSeq (c : ℝ) (n : ℕ) : Continuous (sqrtSeq c n) := by
  unfold sqrtSeq; fun_prop

theorem continuous_sqrtSeq' (c : ℝ) (n : ℕ) : Continuous (sqrtSeq' c n) :=
  (continuous_id.sub continuous_const).div (continuous_sqrtSeq c n)
    fun t => (sqrtSeq_pos c n t).ne'

theorem hasDerivAt_sqrtSeq (c : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (sqrtSeq c n) (sqrtSeq' c n t) t := by
  have hne : (t - c) ^ 2 + 1 / ((n : ℝ) + 1) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x => x - c) 1 t := (hasDerivAt_id t).sub_const c
  have h2 : HasDerivAt (fun x => (x - c) ^ 2) (2 * (t - c)) t := by
    simpa [Function.comp_def] using (hasDerivAt_pow 2 (t - c)).comp t h1
  refine ((h2.add_const (1 / ((n : ℝ) + 1))).sqrt hne).congr_deriv ?_
  unfold sqrtSeq' sqrtSeq
  rw [mul_div_mul_left _ _ two_ne_zero]

/-- `|√(x² + ε) − |x|| ≤ √ε`. -/
theorem abs_sqrt_sub_abs_le (x ε : ℝ) (hε : 0 ≤ ε) : abs (√(x ^ 2 + ε) - |x|) ≤ √ε := by
  have h1 : |x| ≤ √(x ^ 2 + ε) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have h2 : √(x ^ 2 + ε) ≤ |x| + √ε := by
    rw [← Real.sqrt_sq (add_nonneg (abs_nonneg x) (Real.sqrt_nonneg ε))]
    refine Real.sqrt_le_sqrt ?_
    have := Real.sq_sqrt hε
    nlinarith [sq_abs x, abs_nonneg x, Real.sqrt_nonneg ε]
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Ex 3.7b.** Under `max |f|`, `C¹[a, b]` is not complete: with `c = (a + b)/2`, the functions
`√((t − c)² + 1/(n + 1))` form a Cauchy sequence with no limit in `C¹[a, b]` (its uniform limit
`|t − c|` has a kink at `c`). The sequence is not Cauchy in the norm of part (a). -/
theorem ex_3_7b (hab : a < b) :
    ¬ IsCompleteFor (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖) ∧
      ∃ x : ℕ → ckSub hab.le 1, IsCauchy (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖) x ∧
        (¬ ∃ G, Converges (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖) x G) ∧
        ¬ IsCauchy (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖ + ‖F.1 1 - G.1 1‖) x := by
  set c := (a + b) / 2
  have hc : c ∈ Ioo a b := ⟨by simp only [c]; linarith, by simp only [c]; linarith⟩
  set x : ℕ → ckSub hab.le 1 := fun n =>
    mk1 hab.le (continuous_sqrtSeq c n) (continuous_sqrtSeq' c n) (hasDerivAt_sqrtSeq c n)
  have hx0 : ∀ n, (x n).1 0 = restrictC (continuous_sqrtSeq c n) := fun n => rfl
  have hk : Continuous fun t : ℝ => |t - c| := by fun_prop
  -- uniform convergence to `|t − c|`
  have hconv : Tendsto (fun n => (x n).1 0) atTop (𝓝 (restrictC hk)) := by
    have hsq : Tendsto (fun n : ℕ => √(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [Real.sqrt_zero] at this
    refine squeeze_zero_norm (fun n => ?_) hsq |> tendsto_iff_norm_sub_tendsto_zero.2
    rw [norm_norm]
    refine (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).2 fun u => ?_
    rw [hx0, ContinuousMap.sub_apply, Real.norm_eq_abs]
    exact abs_sqrt_sub_abs_le _ _ (by positivity)
  have hcauchy : IsCauchy (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖) x := fun ε hε => by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hconv.cauchySeq ε hε
    exact ⟨N, fun n hn m hm => by
      change ‖(x n).1 0 - (x m).1 0‖ < ε
      rw [← dist_eq_norm]; exact hN n hn m hm⟩
  have hnolim : ¬ ∃ G, Converges (fun F G : ckSub hab.le 1 => ‖F.1 0 - G.1 0‖) x G := by
    rintro ⟨G, hG⟩
    have hG' : Tendsto (fun n => (x n).1 0) atTop (𝓝 (G.1 0)) := Metric.tendsto_atTop.2
      fun ε hε => by
        obtain ⟨N, hN⟩ := hG ε hε
        exact ⟨N, fun n hn => by rw [dist_eq_norm]; exact hN n hn⟩
    have heq : G.1 0 = restrictC hk := tendsto_nhds_unique hG' hconv
    -- `G 0 = |t − c|` on `[a, b]` would be differentiable at the interior point `c`
    have hd := G.2 0 c (Ioo_subset_Icc_self hc)
    change HasDerivWithinAt (ext hab.le (G.1 0)) _ (Icc a b) c at hd
    have hd' := (hd.hasDerivAt (Icc_mem_nhds hc.1 hc.2)).congr_of_eventuallyEq
      (f₁ := fun t => |t - c|) (by
        filter_upwards [Icc_mem_nhds hc.1 hc.2] with t ht
        rw [heq, ext_restrictC hab.le hk ht])
    have habs : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
      have hcomp := (show DifferentiableAt ℝ (fun t => |t - c|) (0 + c) by
        rw [zero_add]; exact hd'.differentiableAt).comp (0 : ℝ)
        ((differentiableAt_id).add_const c)
      have : ((fun t => |t - c|) ∘ fun t => id t + c) = abs := funext fun t => by simp
      rwa [this] at hcomp
    exact not_differentiableAt_abs_zero habs
  refine ⟨fun hcomp => hnolim (hcomp x hcauchy), x, hcauchy, hnolim, fun hC1 => ?_⟩
  -- a Cauchy sequence for the norm of (a) converges in it, hence in `max |f|`
  obtain ⟨G, hG⟩ := (ex_3_7a hab.le).2 x hC1
  exact hnolim ⟨G, fun ε hε => by
    obtain ⟨N, hN⟩ := hG ε hε
    exact ⟨N, fun n hn => lt_of_le_of_lt (le_add_of_nonneg_right (norm_nonneg _)) (hN n hn)⟩⟩

/-! ### Exercise 3.7c: weighted norms on `C^k` -/

/-- **Ex 3.7c**, the weight `α₀`: if `α₀ = 0` the formula is not a norm, since the constant `1`
(with zero derivatives) gets size `0`. -/
theorem not_isNorm_of_alpha0 (hab : a ≤ b) {k : ℕ} {α : Fin (k + 1) → ℝ} (h0 : α 0 = 0) :
    ¬ IsNorm fun F : ckSub hab k => ckNorm α F.1 := by
  intro hN
  have hone : ext hab (1 : C(Icc a b, ℝ)) = fun _ => 1 := funext fun _ => rfl
  have hzero : ext hab (0 : C(Icc a b, ℝ)) = fun _ => 0 := funext (ext_zero hab)
  set F : Fin (k + 1) → C(Icc a b, ℝ) := fun i => if i = 0 then 1 else 0
  have hF : F ∈ ckSub hab k := fun i s _ => by
    have hs : F i.succ = 0 := by simp [F]
    rw [hs, hzero]
    by_cases hi : i.castSucc = 0
    · have : F i.castSucc = 1 := by simp [F, hi]
      rw [this, hone]
      exact hasDerivWithinAt_const _ _ _
    · have : F i.castSucc = 0 := by simp [F, hi]
      rw [this, hzero]
      exact hasDerivWithinAt_const _ _ _
  have hsize : ckNorm α F = 0 := Finset.sum_eq_zero fun i _ => by
    by_cases hi : i = 0
    · rw [hi, h0, zero_mul]
    · simp [F, hi]
  have := (hN.eq_zero ⟨F, hF⟩).1 hsize
  have h1 : F 0 = 0 := congrFun (congrArg Subtype.val this) 0
  have h2 : (1 : C(Icc a b, ℝ)) ⟨a, le_rfl, hab⟩ = 0 := by
    have : F 0 = 1 := by simp [F]
    rw [← this, h1]; rfl
  exact one_ne_zero h2

/-- **Interpolation.** On `C²[a, b]`, `max |f′| ≤ (4/(b − a)) max |f| + ((b − a)/2) max |f″|`:
compare `f(v) − f(t)` with `(v − t) f′(t)` over a step of length `(b − a)/2`. -/
theorem interpolation (hab : a < b) (F : ckSub hab.le 2) :
    ‖F.1 1‖ ≤ 4 / (b - a) * ‖F.1 0‖ + (b - a) / 2 * ‖F.1 2‖ := by
  set g : Fin 3 → ℝ → ℝ := fun i => ext hab.le (F.1 i)
  have hcont : ∀ i, Continuous (g i) := fun i => continuous_ext hab.le _
  have hid := (isCk_iff_integral hab.le F.1).1 F.2
  -- differences of `g i` are integrals of `g (i + 1)`
  have hdiff : ∀ (i : Fin 2) (t u : ℝ), t ∈ Icc a b → u ∈ Icc a b →
      g i.castSucc u - g i.castSucc t = ∫ z in t..u, g i.succ z := fun i t u ht hu => by
    have h1 := hid i u hu
    have h2 := hid i t ht
    change g i.castSucc u = g i.castSucc a + ∫ z in a..u, g i.succ z at h1
    change g i.castSucc t = g i.castSucc a + ∫ z in a..t, g i.succ z at h2
    rw [h1, h2, add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      ((hcont _).intervalIntegrable _ _) ((hcont _).intervalIntegrable _ _)]
  have hbd : ∀ i z, |g i z| ≤ ‖F.1 i‖ := fun i z => abs_ext_le hab.le _ z
  set h := (b - a) / 2
  have hh : 0 < h := by simp only [h]; linarith
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun u => ?_
  set t : ℝ := u.1
  have ht : t ∈ Icc a b := u.2
  rw [Real.norm_eq_abs, ← ext_of_mem hab.le _ ht]
  change |g 1 t| ≤ _
  -- a point `v ∈ [a, b]` at distance `h` from `t`
  obtain ⟨v, hv, hvt⟩ : ∃ v ∈ Icc a b, |v - t| = h := by
    by_cases hc : t ≤ (a + b) / 2
    · exact ⟨t + h, ⟨by linarith [ht.1], by simp only [h]; linarith⟩, by
        rw [add_sub_cancel_left, abs_of_pos hh]⟩
    · exact ⟨t - h, ⟨by simp only [h]; linarith, by linarith [ht.2]⟩, by
        rw [sub_sub_cancel_left, abs_neg, abs_of_pos hh]⟩
  have hsub : uIcc t v ⊆ Icc a b := uIcc_subset_Icc ht hv
  -- `g 1` moves by at most `h ‖F 2‖` between `t` and `v`
  have hclose : ∀ z ∈ uIoc t v, ‖g 1 z - g 1 t‖ ≤ ‖F.1 2‖ * h := fun z hz => by
    have hz' := uIoc_subset_uIcc hz
    have := hdiff 1 t z ht (hsub hz')
    change g 1 z - g 1 t = ∫ w in t..z, g 2 w at this
    rw [this]
    calc ‖∫ w in t..z, g 2 w‖ ≤ ‖F.1 2‖ * |z - t| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun w _ =>
            (Real.norm_eq_abs _).trans_le (hbd 2 w)
      _ ≤ ‖F.1 2‖ * h := by
          rw [← hvt]
          exact mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hz') (norm_nonneg _)
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hclose
  have hd0 : g 0 v - g 0 t = ∫ z in t..v, g 1 z := hdiff 0 t v ht hv
  rw [intervalIntegral.integral_sub ((hcont 1).intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul,
    ← hd0, Real.norm_eq_abs, hvt] at hI
  change |g 0 v - g 0 t - (v - t) * g 1 t| ≤ ‖F.1 2‖ * h * h at hI
  have hg0 : |g 0 v - g 0 t| ≤ 2 * ‖F.1 0‖ := by
    have := abs_sub (g 0 v) (g 0 t)
    linarith [hbd 0 v, hbd 0 t]
  have hstep : h * |g 1 t| ≤ 2 * ‖F.1 0‖ + ‖F.1 2‖ * h * h := by
    have : |(v - t) * g 1 t| ≤ |g 0 v - g 0 t| + |g 0 v - g 0 t - (v - t) * g 1 t| := by
      have := abs_sub (g 0 v - g 0 t) (g 0 v - g 0 t - (v - t) * g 1 t)
      rwa [sub_sub_cancel] at this
    rw [abs_mul, hvt] at this
    linarith
  have hba : b - a = 2 * h := by simp only [h]; ring
  rw [hba]
  rw [← mul_le_mul_iff_of_pos_left hh]
  calc h * |g 1 t| ≤ 2 * ‖F.1 0‖ + ‖F.1 2‖ * h * h := hstep
    _ = h * (4 / (2 * h) * ‖F.1 0‖ + h * ‖F.1 2‖) := by field_simp; ring

/-- **Ex 3.7c: the "only if" is false.** On `C²[a, b]` the weights `α = (1, 0, 1)` give a
norm, `max |f| + max |f″|`, and it is complete although `α₁ = 0`. -/
theorem ex_3_7c_counterexample (hab : a < b) :
    IsNorm (fun F : ckSub hab.le 2 => ckNorm ![1, 0, 1] F.1) ∧
      IsCompleteFor fun F G : ckSub hab.le 2 => ckNorm ![1, 0, 1] (F.1 - G.1) := by
  have hform : ∀ F : Fin 3 → C(Icc a b, ℝ), ckNorm ![1, 0, 1] F = ‖F 0‖ + ‖F 2‖ := fun F => by
    simp [ckNorm, Fin.sum_univ_three]
  have hall : ∀ F : Fin 3 → C(Icc a b, ℝ),
      ckNorm (fun _ => 1) F = ‖F 0‖ + ‖F 1‖ + ‖F 2‖ := fun F => by
    simp [ckNorm, Fin.sum_univ_three]
  set K := max (4 / (b - a)) ((b - a) / 2)
  have hK : 0 ≤ K := le_max_of_le_right (by linarith)
  -- `max |f′|` is controlled by `max |f| + max |f″|`
  have hctrl : ∀ F : ckSub hab.le 2, ‖F.1 1‖ ≤ K * (‖F.1 0‖ + ‖F.1 2‖) := fun F => by
    refine (interpolation hab F).trans ?_
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  refine ⟨⟨fun F => by rw [hform]; positivity, fun F => ?_, fun r F => ?_, fun F G => ?_⟩, ?_⟩
  · rw [hform]
    constructor
    · intro h
      have h0 : ‖F.1 0‖ = 0 := by linarith [norm_nonneg (F.1 0), norm_nonneg (F.1 2)]
      have h2 : ‖F.1 2‖ = 0 := by linarith [norm_nonneg (F.1 0), norm_nonneg (F.1 2)]
      have h1 : ‖F.1 1‖ = 0 := le_antisymm (by simpa [h0, h2] using hctrl F) (norm_nonneg _)
      ext1
      funext i
      fin_cases i
      · exact norm_eq_zero.1 h0
      · exact norm_eq_zero.1 h1
      · exact norm_eq_zero.1 h2
    · rintro rfl; simp
  · rw [hform, hform]
    simp only [Submodule.coe_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    ring
  · rw [hform, hform, hform]
    simp only [Submodule.coe_add, Pi.add_apply]
    linarith [norm_add_le (F.1 0) (G.1 0), norm_add_le (F.1 2) (G.1 2)]
  · intro x hx
    -- Cauchy for `(1, 0, 1)` ⇒ Cauchy for `(1, 1, 1)`, which is complete
    have hcmp : ∀ F G : ckSub hab.le 2,
        ckNorm (fun _ => 1) (F.1 - G.1) ≤ (1 + K) * ckNorm ![1, 0, 1] (F.1 - G.1) := fun F G => by
      rw [hall, hform]
      have := hctrl (F - G)
      simp only [Submodule.coe_sub] at this
      nlinarith [norm_nonneg ((F.1 - G.1) 0), norm_nonneg ((F.1 - G.1) 2)]
    have hx' : IsCauchy (fun F G : ckSub hab.le 2 => ckNorm (fun _ => 1) (F.1 - G.1)) x :=
      fun ε hε => by
        obtain ⟨N, hN⟩ := hx (ε / (1 + K)) (div_pos hε (by linarith))
        refine ⟨N, fun n hn m hm => (hcmp _ _).trans_lt ?_⟩
        have := hN n hn m hm
        rwa [lt_div_iff₀ (by linarith), mul_comm] at this
    obtain ⟨L, hL⟩ := isComplete_ckNorm hab.le (fun _ => one_pos) x hx'
    refine ⟨L, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hL ε hε
    refine ⟨N, fun n hn => lt_of_le_of_lt ?_ (hN n hn)⟩
    change ckNorm ![1, 0, 1] ((x n).1 - L.1) ≤ ckNorm (fun _ => 1) ((x n).1 - L.1)
    rw [hall, hform]
    linarith [norm_nonneg (((x n).1 - L.1) 1)]

end StokeyLucasPrescott.MathematicalPreliminaries
