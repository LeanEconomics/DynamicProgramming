/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.ScrambleAsymptotic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The variance of scrambled `(0,m,2)`-nets for smooth integrands: `Var ≍ n⁻³ log n`

Towards Loh's (2003) CLT beyond additive integrands (post #2). Loh's proof needs the exact order
of `Var(μ̂)`, Owen's (1997b) `n^{-3} (log n)^{s-1}`; this module proves it for `s = 2`, for
scrambled `(0,m,2)`-nets in any base `b ≥ 2` with `m` digits, from the gain-coefficient formula
of `ScrambleVariance`/`ScrambleGain` and an analysis of the base-`b` Haar coefficients of smooth
integrands.

**Smoothness hypotheses (reading).** Stated through the mixed difference
`mixDiff f x x' = f(x₀,x₁) - f(x₀,x'₁) - f(x'₀,x₁) + f(x'₀,x'₁)`:
* `|mixDiff f x x'| ≤ M |Δx₀| |Δx₁|` on the cube (bounded mixed derivative `∂²f/∂x₀∂x₁`);
* `|f x - f x'| ≤ L (|Δx₀| + |Δx₁|)` on the cube (Lipschitz);
* near a point `xc` of `[0,1)²`, `mixDiff f x x' = g₀ Δx₀ Δx₁ + o(|Δx₀| |Δx₁|)` uniformly, with
  `g₀ ≠ 0` (a non-vanishing strict mixed derivative at `xc`).
For `f` with a mixed partial `∂²f/∂x₀∂x₁` continuous on `[0,1]²` the first and third follow from
the mean value theorem (`abs_sub_sub_mul_le_of_deriv`, `abs_mixDiff_sub_le_of_deriv`,
`variance_scrambledLaw_two_asymp_of_deriv`); `prodFn` (`x₀ x₁`) satisfies all three with
`M = L = g₀ = 1`.

## Main results

* `haarProj`, `haarVar_eq_sum_sq`: `σ²_ℓ` is the mean square of the Haar projection `P_ℓ F`.
* `sum_mul_mul_eq_mixed`, `haarProj_cellAvg_eq`: in two dimensions `P_ℓ F` is a kernel average
  of mixed differences of `f` (the detail kernels have zero row sums).
* `abs_haarProj_cellAvg_le`, `haarVar_cellAvg_le`: `σ²_ℓ ≤ 16 M² b^{-2κ₀} b^{-2κ₁}` at levels
  `(κ₀ + 1, κ₁ + 1)`.
* `sum_agreeKernel_mul_cellVal`, `sum_detailKernel_mul_cellVal`, `abs_haarProj_cellAvg_ge`,
  `card_prefixVal_digit_eq`, `haarVar_cellAvg_ge`: `σ²_ℓ ≥ c b^{-2κ₀} b^{-2κ₁}` when
  `κ₀, κ₁ ≥ k`, from the cells near `xc` whose digit `κ_j` is `0`.
* `gainSeq_two_one`, `lvec2`, `gainCoeff_lvec2`: the `m` components with `κ₀ + κ₁ = m - 1` have
  gain `b/(b-1)`.
* `pow_mul_variance_scrambledLaw_two_ge` (**lower bound**):
  `b^{3m} Var(μ̂) ≥ (m - 2k) g₀² (b-1)⁴/(64 b^{2k+4})`.
* `cellResVar_le`, `sum_range_ite_pow_le`, `pow_mul_variance_scrambledLaw_two_le`
  (**upper bound**): `b^{3m} Var(μ̂) ≤ 4 L² + 64 M² b² (m + 1)`.
* `variance_scrambledLaw_two_asymp` (**Owen 1997b, `s = 2`**): `c m ≤ b^{3m} Var(μ̂) ≤ C (m+1)`
  eventually, i.e. `Var(μ̂) ≍ n^{-3} log n`; `variance_scrambledLaw_two_asymp_of_deriv`: the
  same for `f` Lipschitz with a continuous mixed partial derivative, non-zero at some point.
* `prodFn`, `mixDiff_prodFn`, `variance_scrambledLaw_prodFn`: for `f = x₀ x₁`,
  `m (b-1)⁴/(64 b⁴) ≤ b^{3m} Var(μ̂) ≤ 4 + 64 b² (m+1)` for every `(0,m,2)`-net, e.g. the
  Hammersley net. Compare `n³ Var(μ̂) → const` for additive `f`
  (`LohCLT.tendsto_cube_mul_variance_scrambledLaw_addFn`): interactions add the `log n`.
* `avg_variance_scrambledEstimate`: `E_ρ[Var(μ̂ | ρ)] = n⁻¹ σ²_{>D}` (any `s`, any point set).
* `tendsto_avg_variance_given_scramble_div`: for the smooth non-degenerate integrands above,
  `E_ρ[Var(μ̂ | ρ)]/Var(μ̂) → 0`.

## What remains for Loh's CLT (not formalised)

By `tendsto_avg_variance_given_scramble_div` and the law of total variance, for non-additive
smooth `f` almost all of `Var(μ̂)` is `Var(E[μ̂ | ρ])`, the fluctuation of
`E[μ̂ | ρ] = n⁻¹ Σ_i F(σ d_i)` under the nested scramble alone, where the points are dependent. So
the conditional-on-the-scramble Lindeberg argument behind the additive case
(`LohCLT.tendstoInDistribution_scrambledEstimate_addFn`) cannot give the general CLT. Conditioning
on the top levels instead does not split the points into independent blocks once `s ≥ 2`: a
point depends on one subtree in each coordinate, and the points sharing a subtree in coordinate
`0` and those sharing one in coordinate `1` interlock. The CLT for `E[μ̂ | ρ]` is what Loh's
Stein-method argument supplies. (Heuristically, each of the `m` resolution splits
`κ₀ + κ₁ = m - 1` contributes a two-way array in the level-`κ₀` and level-`κ₁` node
permutations of the two coordinates, centred in each coordinate separately, which need not be
normal by itself; normality comes from aggregating the `≍ log n` splits. This is not
formalised.) Also not formalised: general `s` (the `(log n)^{s-1}` order needs `s`-fold mixed
differences), nets with `t > 0`, and the infinite-depth identification of the scramble in `s`
dimensions (`Owen1DDeep` does `s = 1`).
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal Topology

variable {b D : ℕ}

/-- The Haar projection `P_ℓ F(z) = Σ_y H_ℓ(z, y) F(y)` of a function on the digit grid. -/
noncomputable def haarProj {s : ℕ} (ℓ : Fin s → Fin (D + 1)) (F : (Fin s → Fin D → Fin b) → ℝ)
    (z : Fin s → Fin D → Fin b) : ℝ :=
  ∑ y, haarKernel ℓ z y * F y

/-- The variance component is the mean square of the Haar projection. -/
theorem haarVar_eq_sum_sq (hb : 0 < b) {s : ℕ} (F : (Fin s → Fin D → Fin b) → ℝ)
    (ℓ : Fin s → Fin (D + 1)) :
    haarVar F ℓ = (∑ z, haarProj ℓ F z ^ 2) / ((b : ℝ) ^ D) ^ s := by
  unfold haarVar
  rw [qform_eq_sum_sq (haarKernel_comm ℓ) (sum_haarKernel_mul hb ℓ)]
  congr 1
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  unfold haarProj
  congr 1
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [haarKernel_comm ℓ y z, mul_comm]

/-- The detail kernels of positive level have zero row sums. -/
theorem sum_detailKernel_succ (hb : 0 < b) (κ : ℕ) (x : Fin D → Fin b) :
    ∑ y, detailKernel (κ + 1) x y = 0 := by
  change ∑ y, (agreeKernel (κ + 1) x y - agreeKernel κ x y) = 0
  rw [Finset.sum_sub_distrib, sum_agreeKernel hb, sum_agreeKernel hb, sub_self]

/-- The averaging kernels are nonnegative. -/
theorem agreeKernel_nonneg (r : ℕ) (x y : Fin D → Fin b) : 0 ≤ agreeKernel r x y := by
  unfold agreeKernel
  split_ifs
  · exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _)
  · exact le_rfl

/-- The detail kernels of positive level have absolute row sums at most `2`. -/
theorem sum_abs_detailKernel_succ_le (hb : 0 < b) (κ : ℕ) (x : Fin D → Fin b) :
    ∑ y, |detailKernel (κ + 1) x y| ≤ 2 := by
  change ∑ y, |agreeKernel (κ + 1) x y - agreeKernel κ x y| ≤ 2
  calc ∑ y, |agreeKernel (κ + 1) x y - agreeKernel κ x y|
      ≤ ∑ y, (agreeKernel (κ + 1) x y + agreeKernel κ x y) := by
        refine Finset.sum_le_sum fun y _ ↦ ?_
        rw [abs_le]
        constructor <;> linarith [agreeKernel_nonneg (κ + 1) x y, agreeKernel_nonneg κ x y]
    _ = 2 := by rw [Finset.sum_add_distrib, sum_agreeKernel hb, sum_agreeKernel hb]; norm_num

/-- The detail kernel of level `κ + 1` lives on the level-`κ` cell. -/
theorem agree_of_detailKernel_ne_zero {κ : ℕ} {x y : Fin D → Fin b}
    (h : detailKernel (κ + 1) x y ≠ 0) : Agree κ x y := by
  by_contra hc
  apply h
  change agreeKernel (κ + 1) x y - agreeKernel κ x y = 0
  unfold agreeKernel
  rw [ite_eq_right hc, ite_eq_right fun h' ↦ hc (agree_mono (Nat.le_succ κ) h'), sub_zero]

/-- Strings agreeing on `κ ≤ D` digits have cell indices less than `b^{D-κ}` apart. -/
theorem abs_cellVal_sub_lt (hb : 0 < b) {κ : ℕ} (hκ : κ ≤ D) {x y : Fin D → Fin b}
    (h : Agree κ x y) : |(cellVal x : ℝ) - cellVal y| < (b : ℝ) ^ (D - κ) := by
  have hq : 0 < b ^ (D - κ) := Nat.pow_pos hb
  have hx := prefixVal_div hb x hκ
  have hy := prefixVal_div hb y hκ
  have hxy := (prefixVal_eq_iff_agree hb hκ x y).2 h
  change cellVal x / b ^ (D - κ) = prefixVal x κ at hx
  change cellVal y / b ^ (D - κ) = prefixVal y κ at hy
  set q := b ^ (D - κ) with hqdef
  have e1 := Nat.div_add_mod (cellVal x) q
  have e2 := Nat.div_add_mod (cellVal y) q
  have m1 := Nat.mod_lt (cellVal x) hq
  have m2 := Nat.mod_lt (cellVal y) hq
  rw [hx, hxy] at e1
  rw [hy] at e2
  set P := prefixVal y κ
  set rx := cellVal x % q
  set ry := cellVal y % q
  have ex : ((cellVal x : ℕ) : ℝ) = (q : ℝ) * P + rx := by exact_mod_cast e1.symm
  have ey : ((cellVal y : ℕ) : ℝ) = (q : ℝ) * P + ry := by exact_mod_cast e2.symm
  have m1' : (rx : ℝ) < q := by exact_mod_cast m1
  have m2' : (ry : ℝ) < q := by exact_mod_cast m2
  have hq' : ((b : ℝ) ^ (D - κ)) = q := by rw [hqdef, Nat.cast_pow]
  rw [hq', ex, ey, abs_lt]
  have h0x : (0 : ℝ) ≤ rx := Nat.cast_nonneg _
  have h0y : (0 : ℝ) ≤ ry := Nat.cast_nonneg _
  constructor <;> linarith

/-- Two digit points with the same remainder and strings agreeing on `κ` digits are less than
`b^{-κ}` apart. -/
theorem abs_digitPoint_sub_le (hb : 0 < b) {κ : ℕ} (hκ : κ ≤ D) {x y : Fin D → Fin b}
    (h : Agree κ x y) (u : ℝ) :
    |digitPoint x u - digitPoint y u| ≤ ((b : ℝ) ^ κ)⁻¹ := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hD : (0 : ℝ) < (b : ℝ) ^ D := pow_pos hb' D
  have e : digitPoint x u - digitPoint y u = ((cellVal x : ℝ) - cellVal y) / (b : ℝ) ^ D := by
    unfold digitPoint
    ring
  rw [e, abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have hlt := abs_cellVal_sub_lt hb hκ h
  have hpow : (b : ℝ) ^ D = (b : ℝ) ^ (D - κ) * (b : ℝ) ^ κ := by
    rw [← pow_add, Nat.sub_add_cancel hκ]
  rw [hpow, show ((b : ℝ) ^ κ)⁻¹ * ((b : ℝ) ^ (D - κ) * (b : ℝ) ^ κ) = (b : ℝ) ^ (D - κ) by
    field_simp]
  exact hlt.le

/-- Sums over pairs `Fin 2 → X` as double sums. -/
theorem sum_fin_two_pi {X : Type*} [Fintype X] (G : (Fin 2 → X) → ℝ) :
    ∑ y, G y = ∑ y₀, ∑ y₁, G ![y₀, y₁] := by
  rw [← Fintype.sum_prod_type (f := fun p : X × X ↦ G ![p.1, p.2])]
  refine Fintype.sum_equiv (finTwoArrowEquiv X) _ _ fun y ↦ ?_
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The two-dimensional Haar kernel is a product. -/
theorem haarKernel_two (ℓ : Fin 2 → Fin (D + 1)) (z y : Fin 2 → Fin D → Fin b) :
    haarKernel ℓ z y = detailKernel (ℓ 0) (z 0) (y 0) * detailKernel (ℓ 1) (z 1) (y 1) :=
  Fin.prod_univ_two _

/-- **Mixed differences**: with zero row sums, a double kernel sum only sees the mixed
difference `φ(y₀,y₁) - φ(y₀,w₁) - φ(w₀,y₁) + φ(w₀,w₁)`. -/
theorem sum_mul_mul_eq_mixed {X : Type*} [Fintype X] (h₀ h₁ : X → ℝ) (hs₀ : ∑ y, h₀ y = 0)
    (hs₁ : ∑ y, h₁ y = 0) (φ : X → X → ℝ) (w₀ w₁ : X) :
    ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * φ y₀ y₁ = ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ *
      (φ y₀ y₁ - φ y₀ w₁ - φ w₀ y₁ + φ w₀ w₁) := by
  have e1 : ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * φ y₀ w₁ = 0 := by
    refine Finset.sum_eq_zero fun y₀ _ ↦ ?_
    rw [show (∑ y₁, h₀ y₀ * h₁ y₁ * φ y₀ w₁) = h₀ y₀ * φ y₀ w₁ * ∑ y₁, h₁ y₁ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, hs₁, mul_zero]
  have e2 : ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * φ w₀ y₁ = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun y₁ _ ↦ ?_
    rw [show (∑ y₀, h₀ y₀ * h₁ y₁ * φ w₀ y₁) = h₁ y₁ * φ w₀ y₁ * ∑ y₀, h₀ y₀ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, hs₀, mul_zero]
  have e3 : ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * φ w₀ w₁ = 0 := by
    refine Finset.sum_eq_zero fun y₀ _ ↦ ?_
    rw [show (∑ y₁, h₀ y₀ * h₁ y₁ * φ w₀ w₁) = h₀ y₀ * φ w₀ w₁ * ∑ y₁, h₁ y₁ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, hs₁, mul_zero]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, e2, e3]
  ring

/-- The **mixed difference** of a function of two variables:
`f(x₀,x₁) - f(x₀,x'₁) - f(x'₀,x₁) + f(x'₀,x'₁)`. -/
noncomputable def mixDiff (f : (Fin 2 → ℝ) → ℝ) (x x' : Fin 2 → ℝ) : ℝ :=
  f x - f ![x 0, x' 1] - f ![x' 0, x 1] + f x'

/-- The mixed difference of cell averages is the average of the mixed differences of `f` at
points with common remainders. -/
theorem cellAvg_mixed_eq (hb : 0 < b) {f : (Fin 2 → ℝ) → ℝ} (hf : MemLp f 2 (uniformCube 2))
    (y₀ y₁ z₀ z₁ : Fin D → Fin b) :
    cellAvg f ![y₀, y₁] - cellAvg f ![y₀, z₁] - cellAvg f ![z₀, y₁] + cellAvg f ![z₀, z₁] =
      ∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint ![z₀, z₁] u) ∂(uniformCube 2) := by
  have hI : ∀ y : Fin 2 → Fin D → Fin b,
      Integrable (fun u ↦ f (cellPoint y u)) (uniformCube 2) := fun y ↦
    (memLp_comp_cellPoint hb hf y).integrable one_le_two
  have c1 : ∀ u : Fin 2 → ℝ, cellPoint ![y₀, z₁] u =
      ![cellPoint ![y₀, y₁] u 0, cellPoint ![z₀, z₁] u 1] := fun u ↦ by
    funext j
    fin_cases j <;> rfl
  have c2 : ∀ u : Fin 2 → ℝ, cellPoint ![z₀, y₁] u =
      ![cellPoint ![z₀, z₁] u 0, cellPoint ![y₀, y₁] u 1] := fun u ↦ by
    funext j
    fin_cases j <;> rfl
  unfold cellAvg mixDiff
  simp only [← c1, ← c2]
  rw [integral_add (f := fun u ↦ f (cellPoint ![y₀, y₁] u) - f (cellPoint ![y₀, z₁] u) -
      f (cellPoint ![z₀, y₁] u)) (g := fun u ↦ f (cellPoint ![z₀, z₁] u))
      (((hI _).sub (hI _)).sub (hI _)) (hI _),
    integral_sub (f := fun u ↦ f (cellPoint ![y₀, y₁] u) - f (cellPoint ![y₀, z₁] u))
      (g := fun u ↦ f (cellPoint ![z₀, y₁] u)) ((hI _).sub (hI _)) (hI _),
    integral_sub (hI _) (hI _)]

/-- The Haar projection of the cell averages at a two-dimensional component of levels
`(κ₀ + 1, κ₁ + 1)`, as a double sum of averaged mixed differences. -/
theorem haarProj_cellAvg_eq (hb : 0 < b) {f : (Fin 2 → ℝ) → ℝ} (hf : MemLp f 2 (uniformCube 2))
    {ℓ : Fin 2 → Fin (D + 1)} {κ : Fin 2 → ℕ} (hℓ : ∀ j, (ℓ j : ℕ) = κ j + 1)
    (z : Fin 2 → Fin D → Fin b) :
    haarProj ℓ (cellAvg f) z = ∑ y₀, ∑ y₁, detailKernel (κ 0 + 1) (z 0) y₀ *
      detailKernel (κ 1 + 1) (z 1) y₁ *
        ∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) ∂(uniformCube 2) := by
  unfold haarProj
  rw [sum_fin_two_pi]
  simp only [haarKernel_two, hℓ]
  have hz : z = ![z 0, z 1] := by
    funext j
    fin_cases j <;> rfl
  have hfin : ∀ (y₀ y₁ : Fin D → Fin b), (![y₀, y₁] : Fin 2 → Fin D → Fin b) 0 = y₀ ∧
      (![y₀, y₁] : Fin 2 → Fin D → Fin b) 1 = y₁ := fun _ _ ↦ ⟨rfl, rfl⟩
  simp only [hfin]
  rw [sum_mul_mul_eq_mixed _ _ (sum_detailKernel_succ hb _ _) (sum_detailKernel_succ hb _ _)
    (fun y₀ y₁ ↦ cellAvg f ![y₀, y₁]) (z 0) (z 1)]
  refine Finset.sum_congr rfl fun y₀ _ ↦ Finset.sum_congr rfl fun y₁ _ ↦ ?_
  rw [cellAvg_mixed_eq hb hf, ← hz]

/-- **Upper bound on a two-dimensional Haar projection**: if the mixed differences of `f` on the
cube are bounded by `M |Δx₀| |Δx₁|`, then `|P_ℓ F| ≤ 4 M b^{-κ₀} b^{-κ₁}` for the component of
levels `(κ₀ + 1, κ₁ + 1)`. -/
theorem abs_haarProj_cellAvg_le (hb : 0 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube 2)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |mixDiff f x x'| ≤ M * |x 0 - x' 0| * |x 1 - x' 1|)
    {ℓ : Fin 2 → Fin (D + 1)} {κ : Fin 2 → ℕ} (hℓ : ∀ j, (ℓ j : ℕ) = κ j + 1)
    (hκD : ∀ j, κ j ≤ D) (z : Fin 2 → Fin D → Fin b) :
    |haarProj ℓ (cellAvg f) z| ≤ 4 * M * ((b : ℝ) ^ κ 0)⁻¹ * ((b : ℝ) ^ κ 1)⁻¹ := by
  have hU := isProbabilityMeasure_uniformCube 2
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  set β₀ := ((b : ℝ) ^ κ 0)⁻¹ with hβ₀
  set β₁ := ((b : ℝ) ^ κ 1)⁻¹ with hβ₁
  have hβ₀0 : 0 ≤ β₀ := inv_nonneg.2 (pow_nonneg hb'.le _)
  have hβ₁0 : 0 ≤ β₁ := inv_nonneg.2 (pow_nonneg hb'.le _)
  rw [haarProj_cellAvg_eq hb hf hℓ]
  set h₀ := fun y₀ ↦ detailKernel (κ 0 + 1) (z 0) y₀
  set h₁ := fun y₁ ↦ detailKernel (κ 1 + 1) (z 1) y₁
  have hB : ∀ y₀ y₁, h₀ y₀ ≠ 0 → h₁ y₁ ≠ 0 →
      |∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) ∂(uniformCube 2)| ≤
        M * β₀ * β₁ := by
    intro y₀ y₁ h0 h1
    have a0 := agree_of_detailKernel_ne_zero h0
    have a1 := agree_of_detailKernel_ne_zero h1
    have h := norm_integral_le_of_norm_le_const (μ := uniformCube 2) (C := M * β₀ * β₁)
      (f := fun u ↦ mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u)) (by
        filter_upwards [ae_mem_cube_uniformCube 2] with u hu
        rw [Real.norm_eq_abs]
        refine (hM _ _ (fun j ↦ digitPoint_mem_Ico hb _ (hu j))
          (fun j ↦ digitPoint_mem_Ico hb _ (hu j))).trans ?_
        have d0 : |cellPoint ![y₀, y₁] u 0 - cellPoint z u 0| ≤ β₀ :=
          abs_digitPoint_sub_le hb (hκD 0) (agree_symm a0) _
        have d1 : |cellPoint ![y₀, y₁] u 1 - cellPoint z u 1| ≤ β₁ :=
          abs_digitPoint_sub_le hb (hκD 1) (agree_symm a1) _
        calc M * |cellPoint ![y₀, y₁] u 0 - cellPoint z u 0| *
              |cellPoint ![y₀, y₁] u 1 - cellPoint z u 1|
            ≤ M * β₀ * β₁ := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left d0 hM0) d1 (abs_nonneg _)
              exact mul_nonneg hM0 hβ₀0)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  have hterm : ∀ y₀ y₁, |h₀ y₀ * h₁ y₁ *
      ∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) ∂(uniformCube 2)| ≤
      |h₀ y₀| * |h₁ y₁| * (M * β₀ * β₁) := by
    intro y₀ y₁
    rw [abs_mul, abs_mul]
    by_cases h0 : h₀ y₀ = 0
    · rw [h0, abs_zero]
      simp only [zero_mul, le_refl]
    by_cases h1 : h₁ y₁ = 0
    · rw [h1, abs_zero]
      simp only [mul_zero, zero_mul, le_refl]
    exact mul_le_mul_of_nonneg_left (hB y₀ y₁ h0 h1)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hs₀ := sum_abs_detailKernel_succ_le hb (κ 0) (z 0)
  have hs₁ := sum_abs_detailKernel_succ_le hb (κ 1) (z 1)
  calc |∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ *
        ∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) ∂(uniformCube 2)|
      ≤ ∑ y₀, ∑ y₁, |h₀ y₀| * |h₁ y₁| * (M * β₀ * β₁) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y₀ _ ↦
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y₁ _ ↦ hterm y₀ y₁))
    _ = (∑ y₀, |h₀ y₀|) * (∑ y₁, |h₁ y₁|) * (M * β₀ * β₁) := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun y₀ _ ↦ ?_
        rw [Finset.sum_mul]
    _ ≤ 2 * 2 * (M * β₀ * β₁) := by
        have hMβ : 0 ≤ M * β₀ * β₁ := mul_nonneg (mul_nonneg hM0 hβ₀0) hβ₁0
        refine mul_le_mul_of_nonneg_right ?_ hMβ
        exact mul_le_mul hs₀ hs₁ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
    _ = 4 * M * β₀ * β₁ := by ring

/-- **Upper bound on a two-dimensional variance component**:
`σ²_ℓ ≤ 16 M² b^{-2κ₀} b^{-2κ₁}`. -/
theorem haarVar_cellAvg_le (hb : 0 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube 2)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |mixDiff f x x'| ≤ M * |x 0 - x' 0| * |x 1 - x' 1|)
    {ℓ : Fin 2 → Fin (D + 1)} {κ : Fin 2 → ℕ} (hℓ : ∀ j, (ℓ j : ℕ) = κ j + 1)
    (hκD : ∀ j, κ j ≤ D) :
    haarVar (cellAvg (b := b) f) ℓ ≤ (4 * M * ((b : ℝ) ^ κ 0)⁻¹ * ((b : ℝ) ^ κ 1)⁻¹) ^ 2 := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ 2 := pow_pos (pow_pos hb' D) 2
  rw [haarVar_eq_sum_sq hb, div_le_iff₀ hbD]
  have hcard : ((Finset.univ : Finset (Fin 2 → Fin D → Fin b)).card : ℝ) = ((b : ℝ) ^ D) ^ 2 := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  calc ∑ z, haarProj ℓ (cellAvg f) z ^ 2
      ≤ ∑ _z : Fin 2 → Fin D → Fin b, (4 * M * ((b : ℝ) ^ κ 0)⁻¹ * ((b : ℝ) ^ κ 1)⁻¹) ^ 2 := by
        refine Finset.sum_le_sum fun z _ ↦ ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_haarProj_cellAvg_le hb hf hM0 hM hℓ hκD z) 2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]

/-- `Σ_{t < q} t = q (q - 1)/2`. -/
theorem sum_range_cast_id (q : ℕ) : ∑ t ∈ Finset.range q, (t : ℝ) = q * (q - 1) / 2 := by
  induction q with
  | zero => rw [Finset.sum_range_zero, Nat.cast_zero, zero_mul, zero_div]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **The average cell index over a prefix class**: for `r ≤ D`,
`Σ_y K_r(x, y) cellVal y = b^{D-r} prefixVal x r + (b^{D-r} - 1)/2`. -/
theorem sum_agreeKernel_mul_cellVal (hb : 0 < b) {r : ℕ} (hr : r ≤ D) (x : Fin D → Fin b) :
    ∑ y, agreeKernel r x y * (cellVal y : ℝ) =
      (b : ℝ) ^ (D - r) * prefixVal x r + ((b : ℝ) ^ (D - r) - 1) / 2 := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hq : 0 < b ^ (D - r) := Nat.pow_pos hb
  have hbD : b ^ D = b ^ r * b ^ (D - r) := by rw [← pow_add, Nat.add_sub_cancel' hr]
  set q := b ^ (D - r) with hqdef
  set a := prefixVal x r with ha
  have hcell : ∀ y : Fin D → Fin b, Agree r x y ↔ cellVal y / q = a := by
    intro y
    rw [← prefixVal_eq_iff_agree hb hr, ha, eq_comm, hqdef]
    unfold cellVal
    rw [prefixVal_div hb y hr]
  have halt : a < b ^ r := prefixVal_lt hb x r
  have hsum : ∑ y ∈ Finset.univ.filter (fun y : Fin D → Fin b ↦ Agree r x y), (cellVal y : ℝ) =
      ∑ t ∈ Finset.range q, ((a * q + t : ℕ) : ℝ) := by
    refine Finset.sum_bij (fun y _ ↦ cellVal y - a * q) ?_ ?_ ?_ ?_
    · intro y hy
      rw [Finset.mem_filter, hcell] at hy
      rw [Finset.mem_range]
      have h1 := Nat.div_add_mod (cellVal y) q
      have h2 := Nat.mod_lt (cellVal y) hq
      rw [hy.2] at h1
      have : q * a = a * q := mul_comm _ _
      omega
    · intro y₁ h₁ y₂ h₂ h12
      rw [Finset.mem_filter, hcell] at h₁ h₂
      have e1 := Nat.div_add_mod (cellVal y₁) q
      have e2 := Nat.div_add_mod (cellVal y₂) q
      rw [h₁.2] at e1
      rw [h₂.2] at e2
      have : q * a = a * q := mul_comm _ _
      exact cellVal_injective hb (by omega)
    · intro t ht
      rw [Finset.mem_range] at ht
      have hlt : a * q + t < b ^ D := by
        rw [hbD]
        calc a * q + t < a * q + q := by omega
          _ = (a + 1) * q := by ring
          _ ≤ b ^ r * q := Nat.mul_le_mul_right _ halt
      obtain ⟨y, hy⟩ := (cellFin_bijective (D := D) hb).2 ⟨a * q + t, hlt⟩
      have hv : cellVal y = a * q + t := congrArg Fin.val hy
      refine ⟨y, ?_, ?_⟩
      · rw [Finset.mem_filter, hcell, hv]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt ht, zero_add]
      · simp only [hv, Nat.add_sub_cancel_left]
    · intro y hy
      rw [Finset.mem_filter, hcell] at hy
      have h1 := Nat.div_add_mod (cellVal y) q
      rw [hy.2] at h1
      have : q * a = a * q := mul_comm _ _
      congr 1
      omega
  have hK : ∀ y, agreeKernel r x y * (cellVal y : ℝ) =
      if Agree r x y then (b : ℝ) ^ r / (b : ℝ) ^ D * cellVal y else 0 := by
    intro y
    unfold agreeKernel
    rw [min_eq_left hr]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun y _ ↦ hK y, ← Finset.sum_filter, ← Finset.mul_sum, hsum]
  simp only [Nat.cast_add, Nat.cast_mul, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, sum_range_cast_id]
  have hqR : ((q : ℕ) : ℝ) = (b : ℝ) ^ (D - r) := by rw [hqdef, Nat.cast_pow]
  have hbDR : (b : ℝ) ^ D = (b : ℝ) ^ r * (b : ℝ) ^ (D - r) := by
    rw [← pow_add, Nat.add_sub_cancel' hr]
  rw [hqR, hbDR]
  have h1 : (0 : ℝ) < (b : ℝ) ^ r := pow_pos hb' r
  have h2 : (0 : ℝ) < (b : ℝ) ^ (D - r) := pow_pos hb' _
  field_simp

/-- **The first moment of a detail kernel**: for `κ < D`,
`Σ_y δ_{κ+1}(x, y) cellVal y = b^{D-κ-1} (x_κ - (b-1)/2)`. -/
theorem sum_detailKernel_mul_cellVal (hb : 0 < b) {κ : ℕ} (hκ : κ < D) (x : Fin D → Fin b) :
    ∑ y, detailKernel (κ + 1) x y * (cellVal y : ℝ) =
      (b : ℝ) ^ (D - (κ + 1)) * (((x ⟨κ, hκ⟩ : ℕ) : ℝ) - ((b : ℝ) - 1) / 2) := by
  change ∑ y, (agreeKernel (κ + 1) x y - agreeKernel κ x y) * (cellVal y : ℝ) = _
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [sum_agreeKernel_mul_cellVal hb (Nat.succ_le_of_lt hκ),
    sum_agreeKernel_mul_cellVal hb hκ.le]
  change (b : ℝ) ^ (D - (κ + 1)) * ((b * prefixVal x κ + digitAt x κ : ℕ) : ℝ) +
    ((b : ℝ) ^ (D - (κ + 1)) - 1) / 2 -
    ((b : ℝ) ^ (D - κ) * (prefixVal x κ : ℝ) + ((b : ℝ) ^ (D - κ) - 1) / 2) = _
  have hdig : digitAt x κ = (x ⟨κ, hκ⟩ : ℕ) := by
    unfold digitAt
    rw [dite_eq_left hκ]
  have hpow : (b : ℝ) ^ (D - κ) = (b : ℝ) * (b : ℝ) ^ (D - (κ + 1)) := by
    rw [← pow_succ', show D - (κ + 1) + 1 = D - κ by omega]
  rw [hdig, hpow]
  push_cast
  ring

/-- The difference of two digit points with the same remainder. -/
theorem digitPoint_sub_digitPoint (x y : Fin D → Fin b) (u : ℝ) :
    digitPoint x u - digitPoint y u = ((cellVal x : ℝ) - cellVal y) / (b : ℝ) ^ D := by
  unfold digitPoint
  ring

/-- Points in the same `b`-adic interval of level `k` are less than `b^{-k}` apart. -/
theorem abs_sub_lt_of_floor_eq (hb : 0 < b) (k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ⌊(b : ℝ) ^ k * x⌋₊ = ⌊(b : ℝ) ^ k * y⌋₊) : |x - y| < ((b : ℝ) ^ k)⁻¹ := by
  have hc : (0 : ℝ) < (b : ℝ) ^ k := pow_pos (Nat.cast_pos.2 hb) k
  have h1 := Nat.floor_le (mul_nonneg hc.le hx)
  have h2 := Nat.lt_floor_add_one ((b : ℝ) ^ k * x)
  have h3 := Nat.floor_le (mul_nonneg hc.le hy)
  have h4 := Nat.lt_floor_add_one ((b : ℝ) ^ k * y)
  rw [h] at h1 h2
  have habs : |(b : ℝ) ^ k * x - (b : ℝ) ^ k * y| < 1 :=
    abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have e : x - y = ((b : ℝ) ^ k * x - (b : ℝ) ^ k * y) / (b : ℝ) ^ k := by
    field_simp
  rw [e, abs_div, abs_of_pos hc, div_lt_iff₀ hc, inv_mul_cancel₀ hc.ne']
  exact habs

/-- The mixed difference of `f` at two cell points with common remainders is integrable. -/
theorem integrable_mixDiff_cellPoint (hb : 0 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube 2)) (y z : Fin 2 → Fin D → Fin b) :
    Integrable (fun u ↦ mixDiff f (cellPoint y u) (cellPoint z u)) (uniformCube 2) := by
  have hI : ∀ y : Fin 2 → Fin D → Fin b,
      Integrable (fun u ↦ f (cellPoint y u)) (uniformCube 2) := fun y ↦
    (memLp_comp_cellPoint hb hf y).integrable one_le_two
  have e : (fun u ↦ mixDiff f (cellPoint y u) (cellPoint z u)) = fun u ↦
      f (cellPoint y u) - f (cellPoint ![y 0, z 1] u) - f (cellPoint ![z 0, y 1] u) +
        f (cellPoint z u) := by
    funext u
    unfold mixDiff
    have c1 : (![cellPoint y u 0, cellPoint z u 1] : Fin 2 → ℝ) = cellPoint ![y 0, z 1] u := by
      funext j
      fin_cases j <;> rfl
    have c2 : (![cellPoint z u 0, cellPoint y u 1] : Fin 2 → ℝ) = cellPoint ![z 0, y 1] u := by
      funext j
      fin_cases j <;> rfl
    rw [c1, c2]
  rw [e]
  exact (((hI _).sub (hI _)).sub (hI _)).add (hI _)

/-- **Lower bound on a two-dimensional Haar projection**. Suppose that near `xc` the mixed
differences of `f` are `g₀ Δx₀ Δx₁` up to `ε |Δx₀| |Δx₁|` (a strict mixed derivative `g₀` at
`xc`), and let `z` be a grid point in the level-`k` cube of `xc`, of side `b^{-k} ≤ δ`, whose digit
`κ_j ≥ k` is `0` in each coordinate. Then the Haar projection of levels `(κ₀ + 1, κ₁ + 1)` at `z`
is at least `|g₀| (b-1)²/(4 b^{κ₀+1} b^{κ₁+1}) - 4 ε b^{-κ₀} b^{-κ₁}`. -/
theorem abs_haarProj_cellAvg_ge (hb : 1 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube 2)) {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1)
    {g₀ ε δ : ℝ} (hε : 0 ≤ ε)
    (hg : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, |x j - xc j| < δ) → (∀ j, |x' j - xc j| < δ) →
      |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤ ε * |x 0 - x' 0| * |x 1 - x' 1|)
    {k : ℕ} (hk : ((b : ℝ) ^ k)⁻¹ ≤ δ) {ℓ : Fin 2 → Fin (D + 1)} {κ : Fin 2 → ℕ}
    (hℓ : ∀ j, (ℓ j : ℕ) = κ j + 1) (hκk : ∀ j, k ≤ κ j) (hκD : ∀ j, κ j < D)
    {z : Fin 2 → Fin D → Fin b} (hz : ∀ j, prefixVal (z j) k = ⌊(b : ℝ) ^ k * xc j⌋₊)
    (hz0 : ∀ j, ((z j ⟨κ j, hκD j⟩ : Fin b) : ℕ) = 0) :
    |g₀| * ((b : ℝ) - 1) ^ 2 / (4 * (b : ℝ) ^ (κ 0 + 1) * (b : ℝ) ^ (κ 1 + 1)) -
      4 * ε * ((b : ℝ) ^ κ 0)⁻¹ * ((b : ℝ) ^ κ 1)⁻¹ ≤ |haarProj ℓ (cellAvg f) z| := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hU := isProbabilityMeasure_uniformCube 2
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hbD : (0 : ℝ) < (b : ℝ) ^ D := pow_pos hb' D
  set β₀ := ((b : ℝ) ^ κ 0)⁻¹ with hβ₀
  set β₁ := ((b : ℝ) ^ κ 1)⁻¹ with hβ₁
  have hβ₀0 : 0 ≤ β₀ := inv_nonneg.2 (pow_nonneg hb'.le _)
  have hβ₁0 : 0 ≤ β₁ := inv_nonneg.2 (pow_nonneg hb'.le _)
  have hkD : k ≤ D := le_trans (hκk 0) (hκD 0).le
  rw [haarProj_cellAvg_eq hb0 hf hℓ]
  set h₀ := fun y₀ ↦ detailKernel (κ 0 + 1) (z 0) y₀ with hh₀
  set h₁ := fun y₁ ↦ detailKernel (κ 1 + 1) (z 1) y₁ with hh₁
  set Δ₀ : (Fin D → Fin b) → ℝ := fun y ↦ ((cellVal y : ℝ) - cellVal (z 0)) / (b : ℝ) ^ D
  set Δ₁ : (Fin D → Fin b) → ℝ := fun y ↦ ((cellVal y : ℝ) - cellVal (z 1)) / (b : ℝ) ^ D
  set B : (Fin D → Fin b) → (Fin D → Fin b) → ℝ := fun y₀ y₁ ↦
    ∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) ∂(uniformCube 2) with hB
  -- closeness to `xc`
  have hclose : ∀ (j : Fin 2) (y : Fin D → Fin b), Agree (κ j) (z j) y → ∀ w ∈ Set.Ico (0 : ℝ) 1,
      |digitPoint y w - xc j| < δ := by
    intro j y hy w hw
    have hag : Agree k (z j) y := agree_mono (hκk j) hy
    have hfl : ⌊(b : ℝ) ^ k * digitPoint y w⌋₊ = ⌊(b : ℝ) ^ k * xc j⌋₊ := by
      rw [floor_pow_mul_digitPoint hb0 y hw hkD, ← hz j,
        (prefixVal_eq_iff_agree hb0 hkD _ _).2 (agree_symm hag)]
    exact lt_of_lt_of_le (abs_sub_lt_of_floor_eq hb0 k (digitPoint_mem_Ico hb0 y hw).1
      (hxc j).1 hfl) hk
  have hE : ∀ y₀ y₁, h₀ y₀ ≠ 0 → h₁ y₁ ≠ 0 →
      |B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁| ≤ ε * β₀ * β₁ := by
    intro y₀ y₁ h0 h1
    have a0 := agree_of_detailKernel_ne_zero h0
    have a1 := agree_of_detailKernel_ne_zero h1
    have hint := integrable_mixDiff_cellPoint hb0 hf ![y₀, y₁] z
    have e : B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁ = ∫ u, (mixDiff f (cellPoint ![y₀, y₁] u)
        (cellPoint z u) - g₀ * Δ₀ y₀ * Δ₁ y₁) ∂(uniformCube 2) := by
      rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [e]
    have h := norm_integral_le_of_norm_le_const (μ := uniformCube 2) (C := ε * β₀ * β₁)
      (f := fun u ↦ mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) -
        g₀ * Δ₀ y₀ * Δ₁ y₁) (by
        filter_upwards [ae_mem_cube_uniformCube 2] with u hu
        rw [Real.norm_eq_abs]
        have p0 : cellPoint ![y₀, y₁] u 0 - cellPoint z u 0 = Δ₀ y₀ :=
          digitPoint_sub_digitPoint _ _ _
        have p1 : cellPoint ![y₀, y₁] u 1 - cellPoint z u 1 = Δ₁ y₁ :=
          digitPoint_sub_digitPoint _ _ _
        have hgu := hg (cellPoint ![y₀, y₁] u) (cellPoint z u)
          (fun j ↦ digitPoint_mem_Ico hb0 _ (hu j)) (fun j ↦ digitPoint_mem_Ico hb0 _ (hu j))
          (fun j ↦ by
            fin_cases j
            · exact hclose 0 y₀ a0 _ (hu 0)
            · exact hclose 1 y₁ a1 _ (hu 1))
          (fun j ↦ hclose j (z j) (fun _ _ ↦ rfl) _ (hu j))
        rw [p0, p1] at hgu
        refine hgu.trans ?_
        have d0 : |Δ₀ y₀| ≤ β₀ := by
          rw [← p0]
          exact abs_digitPoint_sub_le hb0 (hκD 0).le (agree_symm a0) _
        have d1 : |Δ₁ y₁| ≤ β₁ := by
          rw [← p1]
          exact abs_digitPoint_sub_le hb0 (hκD 1).le (agree_symm a1) _
        exact mul_le_mul (mul_le_mul_of_nonneg_left d0 hε) d1 (abs_nonneg _)
          (mul_nonneg hε hβ₀0))
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  -- the main term
  have hmom : ∀ (j : Fin 2), ∑ y, detailKernel (κ j + 1) (z j) y *
      (((cellVal y : ℝ) - cellVal (z j)) / (b : ℝ) ^ D) =
      -(((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ j + 1))) := by
    intro j
    have e1 : ∀ y, detailKernel (κ j + 1) (z j) y * (((cellVal y : ℝ) - cellVal (z j)) /
        (b : ℝ) ^ D) = (detailKernel (κ j + 1) (z j) y * (cellVal y : ℝ) -
          detailKernel (κ j + 1) (z j) y * cellVal (z j)) / (b : ℝ) ^ D := fun y ↦ by ring
    rw [Finset.sum_congr rfl fun y _ ↦ e1 y, ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.sum_mul, sum_detailKernel_succ hb0, zero_mul, sub_zero,
      sum_detailKernel_mul_cellVal hb0 (hκD j), hz0 j, Nat.cast_zero, zero_sub]
    have hpow : (b : ℝ) ^ D = (b : ℝ) ^ (D - (κ j + 1)) * (b : ℝ) ^ (κ j + 1) := by
      rw [← pow_add, Nat.sub_add_cancel (hκD j)]
    rw [hpow]
    have : (0 : ℝ) < (b : ℝ) ^ (D - (κ j + 1)) := pow_pos hb' _
    have : (0 : ℝ) < (b : ℝ) ^ (κ j + 1) := pow_pos hb' _
    field_simp
  have hmain : ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (g₀ * Δ₀ y₀ * Δ₁ y₁) =
      g₀ * (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 0 + 1))) *
        (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 1 + 1))) := by
    have e2 : ∀ y₀ y₁, h₀ y₀ * h₁ y₁ * (g₀ * Δ₀ y₀ * Δ₁ y₁) =
        g₀ * ((h₀ y₀ * Δ₀ y₀) * (h₁ y₁ * Δ₁ y₁)) := fun _ _ ↦ by ring
    have hm0 : ∑ y, h₀ y * Δ₀ y = -(((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 0 + 1))) := hmom 0
    have hm1 : ∑ y, h₁ y * Δ₁ y = -(((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 1 + 1))) := hmom 1
    simp only [e2, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hm0, hm1]
    ring
  -- the error term
  have herr : |∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁)| ≤
      4 * ε * β₀ * β₁ := by
    have hterm : ∀ y₀ y₁, |h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁)| ≤
        |h₀ y₀| * |h₁ y₁| * (ε * β₀ * β₁) := by
      intro y₀ y₁
      rw [abs_mul, abs_mul]
      by_cases h0 : h₀ y₀ = 0
      · rw [h0, abs_zero]
        simp only [zero_mul, le_refl]
      by_cases h1 : h₁ y₁ = 0
      · rw [h1, abs_zero]
        simp only [mul_zero, zero_mul, le_refl]
      exact mul_le_mul_of_nonneg_left (hE y₀ y₁ h0 h1)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hs₀ := sum_abs_detailKernel_succ_le hb0 (κ 0) (z 0)
    have hs₁ := sum_abs_detailKernel_succ_le hb0 (κ 1) (z 1)
    calc |∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁)|
        ≤ ∑ y₀, ∑ y₁, |h₀ y₀| * |h₁ y₁| * (ε * β₀ * β₁) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y₀ _ ↦
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y₁ _ ↦ hterm y₀ y₁))
      _ = (∑ y₀, |h₀ y₀|) * (∑ y₁, |h₁ y₁|) * (ε * β₀ * β₁) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y₀ _ ↦ ?_
          rw [Finset.sum_mul]
      _ ≤ 2 * 2 * (ε * β₀ * β₁) := by
          have hεβ : 0 ≤ ε * β₀ * β₁ := mul_nonneg (mul_nonneg hε hβ₀0) hβ₁0
          refine mul_le_mul_of_nonneg_right ?_ hεβ
          exact mul_le_mul hs₀ hs₁ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
      _ = 4 * ε * β₀ * β₁ := by ring
  have hdecomp : ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * B y₀ y₁ =
      ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (g₀ * Δ₀ y₀ * Δ₁ y₁) +
        ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y₀ _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y₁ _ ↦ ?_
    ring
  change _ ≤ |∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * B y₀ y₁|
  rw [hdecomp, hmain]
  have hmainabs : |g₀ * (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 0 + 1))) *
      (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 1 + 1)))| =
      |g₀| * ((b : ℝ) - 1) ^ 2 / (4 * (b : ℝ) ^ (κ 0 + 1) * (b : ℝ) ^ (κ 1 + 1)) := by
    have hb1 : (0 : ℝ) ≤ (b : ℝ) - 1 := by
      have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
      linarith
    rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg hb1 (by positivity)),
      abs_of_nonneg (div_nonneg hb1 (by positivity))]
    ring
  have := abs_add_le (g₀ * (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 0 + 1))) *
      (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 1 + 1))) +
      ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁))
    (-∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁))
  rw [add_neg_cancel_right, abs_neg, hmainabs] at this
  linarith

/-- A prefix class has `b^{D-k}` strings. -/
theorem card_prefixVal_eq (hb : 0 < b) {k : ℕ} (hk : k ≤ D) {a : ℕ} (ha : a < b ^ k) :
    (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a).card = b ^ (D - k) := by
  obtain ⟨x₀, hx₀⟩ := exists_prefixVal_eq hb hk ha
  have h := card_agree hb k x₀
  rw [min_eq_left hk] at h
  rw [← h]
  congr 1
  refine Finset.filter_congr fun x _ ↦ ?_
  rw [← hx₀, eq_comm, prefixVal_eq_iff_agree hb hk]

/-- In a prefix class of level `k`, each value of a later digit `κ ≥ k` is taken by
`b^{D-k-1}` strings. -/
theorem card_prefixVal_digit_eq (hb : 0 < b) {k κ : ℕ} (hkκ : k ≤ κ) (hκ : κ < D) {a : ℕ}
    (ha : a < b ^ k) (c : Fin b) :
    (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x ⟨κ, hκ⟩ = c).card =
      b ^ (D - k - 1) := by
  set i : Fin D := ⟨κ, hκ⟩
  have hpre : ∀ (x : Fin D → Fin b) (v : Fin b), prefixVal (Function.update x i v) k =
      prefixVal x k := by
    intro x v
    rw [prefixVal_eq_iff_agree hb (le_trans hkκ hκ.le)]
    intro l hl
    have hne : l ≠ i := fun h ↦ by
      rw [h] at hl
      exact absurd hl (not_lt.2 hkκ)
    rw [Function.update_of_ne hne]
  have hle : ∀ c c' : Fin b,
      (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x i = c).card ≤
        (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x i = c').card := by
    intro c c'
    refine Finset.card_le_card_of_injOn (fun x ↦ Function.update x i c') ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, by rw [hpre]; exact hx.2.1, Function.update_self _ _ _⟩
    · intro x hx x' hx' h
      rw [Finset.mem_coe, Finset.mem_filter] at hx hx'
      funext l
      by_cases hl : l = i
      · rw [hl, hx.2.2, hx'.2.2]
      · have := congrFun h l
        simp only [Function.update_of_ne hl] at this
        exact this
  have heq : ∀ c' : Fin b,
      (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x i = c').card =
      (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x i = c).card :=
    fun c' ↦ le_antisymm (hle c' c) (hle c c')
  have htot := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a) (t := Finset.univ)
    (f := fun x ↦ x i) (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _))
  rw [card_prefixVal_eq hb (le_trans hkκ hκ.le) ha] at htot
  have hfil : ∀ c' : Fin b, ((Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a).filter
      fun x ↦ x i = c') =
      Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x i = c' := fun c' ↦ by
    rw [Finset.filter_filter]
  simp only [hfil, heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at htot
  have hpow : b ^ (D - k) = b * b ^ (D - k - 1) := by
    rw [← pow_succ', show D - k - 1 + 1 = D - k by omega]
  rw [hpow] at htot
  exact (Nat.eq_of_mul_eq_mul_left hb htot).symm

/-- **Lower bound on a two-dimensional variance component** at a component of levels
`(κ₀ + 1, κ₁ + 1)` with `k ≤ κ_j < D`, under the local mixed-derivative condition with
`ε = |g₀| (b-1)²/(32 b²)`: `σ²_ℓ ≥ b^{-2k-2} (|g₀| (b-1)²/(8 b^{κ₀+κ₁+2}))²`. -/
theorem haarVar_cellAvg_ge (hb : 1 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube 2)) {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1)
    {g₀ δ : ℝ}
    (hg : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, |x j - xc j| < δ) → (∀ j, |x' j - xc j| < δ) →
      |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤
        |g₀| * ((b : ℝ) - 1) ^ 2 / (32 * (b : ℝ) ^ 2) * |x 0 - x' 0| * |x 1 - x' 1|)
    {k : ℕ} (hk : ((b : ℝ) ^ k)⁻¹ ≤ δ) {ℓ : Fin 2 → Fin (D + 1)} {κ : Fin 2 → ℕ}
    (hℓ : ∀ j, (ℓ j : ℕ) = κ j + 1) (hκk : ∀ j, k ≤ κ j) (hκD : ∀ j, κ j < D) :
    ((b : ℝ) ^ (2 * k + 2))⁻¹ *
      (|g₀| * ((b : ℝ) - 1) ^ 2 / (8 * (b : ℝ) ^ (κ 0 + κ 1 + 2))) ^ 2 ≤
      haarVar (cellAvg (b := b) f) ℓ := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ 2 := pow_pos (pow_pos hb' D) 2
  have hkD : k ≤ D := le_trans (hκk 0) (hκD 0).le
  set L := |g₀| * ((b : ℝ) - 1) ^ 2 / (8 * (b : ℝ) ^ (κ 0 + κ 1 + 2)) with hL
  have hL0 : 0 ≤ L := by positivity
  set a : Fin 2 → ℕ := fun j ↦ ⌊(b : ℝ) ^ k * xc j⌋₊ with ha
  have halt : ∀ j, a j < b ^ k := by
    intro j
    have h0 : 0 ≤ (b : ℝ) ^ k * xc j := mul_nonneg (pow_pos hb' k).le (hxc j).1
    have h1 : (b : ℝ) ^ k * xc j < (b : ℝ) ^ k := by
      have := (hxc j).2
      nlinarith [pow_pos hb' k]
    have := Nat.floor_lt h0 |>.2 (by exact_mod_cast h1 : (b : ℝ) ^ k * xc j < ((b ^ k : ℕ) : ℝ))
    exact this
  set good := Finset.univ.filter fun z : Fin 2 → Fin D → Fin b ↦
    ∀ j, prefixVal (z j) k = a j ∧ z j ⟨κ j, hκD j⟩ = ⟨0, hb0⟩ with hgood
  have hproj : ∀ z ∈ good, L ≤ |haarProj ℓ (cellAvg f) z| := by
    intro z hz
    rw [hgood, Finset.mem_filter] at hz
    have hε : 0 ≤ |g₀| * ((b : ℝ) - 1) ^ 2 / (32 * (b : ℝ) ^ 2) := by positivity
    have h := abs_haarProj_cellAvg_ge hb hf hxc hε hg hk hℓ hκk hκD
      (z := z) (fun j ↦ (hz.2 j).1) (fun j ↦ by rw [(hz.2 j).2])
    refine le_trans (le_of_eq ?_) h
    rw [hL]
    field_simp
    ring
  have hcard : (good.card : ℝ) = ((b ^ (D - k - 1) : ℕ) : ℝ) ^ 2 := by
    have hset : good = Fintype.piFinset fun j ↦ Finset.univ.filter fun x : Fin D → Fin b ↦
        prefixVal x k = a j ∧ x ⟨κ j, hκD j⟩ = ⟨0, hb0⟩ := by
      ext z
      simp only [hgood, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    rw [hset, Fintype.card_piFinset, Fin.prod_univ_two,
      card_prefixVal_digit_eq hb0 (hκk 0) (hκD 0) (halt 0),
      card_prefixVal_digit_eq hb0 (hκk 1) (hκD 1) (halt 1)]
    push_cast
    ring
  rw [haarVar_eq_sum_sq hb0, le_div_iff₀ hbD]
  calc ((b : ℝ) ^ (2 * k + 2))⁻¹ * L ^ 2 * ((b : ℝ) ^ D) ^ 2
      = (good.card : ℝ) * L ^ 2 := by
        rw [hcard]
        have hpow : ((b : ℝ) ^ D) ^ 2 =
            ((b : ℝ) ^ (2 * k + 2)) * (((b ^ (D - k - 1) : ℕ) : ℝ)) ^ 2 := by
          push_cast
          rw [← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          have := hκk 0
          have := hκD 0
          omega
        rw [hpow]
        field_simp
    _ = ∑ _z ∈ good, L ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ good, haarProj ℓ (cellAvg f) z ^ 2 := by
        refine Finset.sum_le_sum fun z hz ↦ ?_
        rw [← sq_abs (haarProj ℓ (cellAvg f) z)]
        exact pow_le_pow_left₀ hL0 (hproj z hz) 2
    _ ≤ ∑ z, haarProj ℓ (cellAvg f) z ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ ↦ sq_nonneg _

/-- `G(2, 1) = b/(b-1)`: the gain of a two-dimensional component one level above exactness. -/
theorem gainSeq_two_one (hb : 1 < b) : gainSeq b 2 1 = (b : ℝ) / ((b : ℝ) - 1) := by
  change -1 / ((b : ℝ) - 1) * gainSeq b 1 (0 + 1) + (b : ℝ) / ((b : ℝ) - 1) * gainSeq b 1 0 = _
  rw [gainSeq_eq_zero hb le_rfl le_rfl, gainSeq_zero_right]
  ring

/-- The two-dimensional Haar level vector `(κ₀ + 1, m - κ₀)` (total resolution `m - 1`). -/
def lvec2 (m κ₀ : ℕ) : Fin 2 → Fin (m + 1) :=
  ![⟨min (κ₀ + 1) m, Nat.lt_succ_of_le (min_le_right _ _)⟩,
    ⟨min (m - κ₀) m, Nat.lt_succ_of_le (min_le_right _ _)⟩]

/-- The levels of `lvec2`. -/
theorem lvec2_val {m κ₀ : ℕ} (h : κ₀ < m) :
    ((lvec2 m κ₀ 0 : ℕ) = κ₀ + 1) ∧ ((lvec2 m κ₀ 1 : ℕ) = (m - 1 - κ₀) + 1) := by
  constructor
  · change min (κ₀ + 1) m = κ₀ + 1
    omega
  · change min (m - κ₀) m = (m - 1 - κ₀) + 1
    omega

/-- The gain of the component `lvec2 m κ₀` of a `(0,m,2)`-net is `b/(b-1)`. -/
theorem gainCoeff_lvec2 (hb : 1 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {κ₀ : ℕ} (h : κ₀ < m) :
    gainCoeff b d (lvec2 m κ₀) = (b : ℝ) / ((b : ℝ) - 1) := by
  obtain ⟨h0, h1⟩ := lvec2_val h
  rw [gainCoeff_net hb le_rfl hnet]
  have hfil : (Finset.univ.filter fun j ↦ ((lvec2 m κ₀ j : Fin (m + 1)) : ℕ) ≠ 0) =
      Finset.univ := by
    refine Finset.filter_true_of_mem fun j _ ↦ ?_
    fin_cases j
    · change ((lvec2 m κ₀ 0 : Fin (m + 1)) : ℕ) ≠ 0
      omega
    · change ((lvec2 m κ₀ 1 : Fin (m + 1)) : ℕ) ≠ 0
      omega
  rw [hfil, Finset.card_univ, Fintype.card_fin, Fin.sum_univ_two, h0, h1,
    show m - (κ₀ + 1 + (m - 1 - κ₀ + 1) - 2) = 1 by omega]
  exact gainSeq_two_one hb

/-- **Owen's variance lower bound for smooth integrands, `s = 2`** (Owen 1997b): for a
scrambled `(0,m,2)`-net in base `b` with `m` digits and an integrand whose mixed differences near
a point `xc` of the cube are `g₀ Δx₀ Δx₁` up to `ε |Δx₀| |Δx₁|`, `ε = |g₀|(b-1)²/(32 b²)`, on a
neighbourhood of radius `δ ≥ b^{-k}`,
`b^{3m} Var(μ̂) ≥ (m - 2k) g₀² (b-1)⁴ / (64 b^{2k+4})`. In particular, if `g₀ ≠ 0` then
`Var(μ̂) ≥ c n^{-3} log n` for large `n`. -/
theorem pow_mul_variance_scrambledLaw_two_ge (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2))
    {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1) {g₀ δ : ℝ}
    (hg : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, |x j - xc j| < δ) → (∀ j, |x' j - xc j| < δ) →
      |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤
        |g₀| * ((b : ℝ) - 1) ^ 2 / (32 * (b : ℝ) ^ 2) * |x 0 - x' 0| * |x 1 - x' 1|)
    {k : ℕ} (hk : ((b : ℝ) ^ k)⁻¹ ≤ δ) (hkm : 2 * k + 1 ≤ m) :
    ((m : ℝ) - 2 * k) * (g₀ ^ 2 * ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ (2 * k + 4))) ≤
      (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f d] := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hn : b ^ m ≠ 0 := (Nat.pow_pos hb0).ne'
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  set C : ℝ := ((b : ℝ) ^ (2 * k + 2))⁻¹ *
    (|g₀| * ((b : ℝ) - 1) ^ 2 / (8 * (b : ℝ) ^ (m - 1 + 2))) ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  set I := Finset.Icc k (m - 1 - k) with hI
  have hIm : ∀ κ₀ ∈ I, κ₀ < m := fun κ₀ h ↦ by
    rw [hI, Finset.mem_Icc] at h
    omega
  have hterm : ∀ κ₀ ∈ I, C ≤ gainCoeff b d (lvec2 m κ₀) * haarVar (cellAvg (b := b) f)
      (lvec2 m κ₀) := by
    intro κ₀ hκ₀
    have hκm := hIm κ₀ hκ₀
    rw [hI, Finset.mem_Icc] at hκ₀
    obtain ⟨h0, h1⟩ := lvec2_val hκm
    have hk0 : k ≤ κ₀ := hκ₀.1
    have hk1 : k ≤ m - 1 - κ₀ := by omega
    have hm0 : κ₀ < m := hκm
    have hm1 : m - 1 - κ₀ < m := by omega
    have hσ := haarVar_cellAvg_ge hb hf hxc hg hk (κ := ![κ₀, m - 1 - κ₀])
      (ℓ := lvec2 m κ₀) (Fin.forall_fin_two.2 ⟨h0, h1⟩) (Fin.forall_fin_two.2 ⟨hk0, hk1⟩)
      (Fin.forall_fin_two.2 ⟨hm0, hm1⟩)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      show κ₀ + (m - 1 - κ₀) = m - 1 by omega] at hσ
    rw [gainCoeff_lvec2 hb hnet hκm]
    have ha : (1 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := by
      rw [one_le_div hb1]
      linarith
    calc C ≤ haarVar (cellAvg (b := b) f) (lvec2 m κ₀) := hσ
      _ ≤ (b : ℝ) / ((b : ℝ) - 1) * haarVar (cellAvg (b := b) f) (lvec2 m κ₀) :=
          le_mul_of_one_le_left (haarVar_nonneg hb0 _ _) ha
  have hinj : Set.InjOn (lvec2 m) I := by
    intro κ₀ h κ₀' h' he
    have := congrArg (fun ℓ ↦ ((ℓ 0 : Fin (m + 1)) : ℕ)) he
    rw [(lvec2_val (hIm κ₀ h)).1, (lvec2_val (hIm κ₀' h')).1] at this
    omega
  have hsub : I.image (lvec2 m) ⊆ (Finset.univ : Finset (Fin 2 → Fin (m + 1))).erase 0 := by
    intro ℓ hℓ
    rw [Finset.mem_image] at hℓ
    obtain ⟨κ₀, hκ₀, rfl⟩ := hℓ
    refine Finset.mem_erase.2 ⟨fun h0 ↦ ?_, Finset.mem_univ _⟩
    have := congrArg (fun ℓ ↦ ((ℓ 0 : Fin (m + 1)) : ℕ)) h0
    simp only [Pi.zero_apply, Fin.val_zero] at this
    rw [(lvec2_val (hIm κ₀ hκ₀)).1] at this
    omega
  have hsum : (I.card : ℝ) * C ≤ ∑ ℓ ∈ (Finset.univ : Finset (Fin 2 → Fin (m + 1))).erase 0,
      gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ := by
    calc (I.card : ℝ) * C = ∑ _κ₀ ∈ I, C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ κ₀ ∈ I, gainCoeff b d (lvec2 m κ₀) * haarVar (cellAvg (b := b) f) (lvec2 m κ₀) :=
          Finset.sum_le_sum hterm
      _ = ∑ ℓ ∈ I.image (lvec2 m), gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ :=
          (Finset.sum_image (f := fun ℓ ↦ gainCoeff b d ℓ *
            haarVar (cellAvg (b := b) f) ℓ) hinj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun ℓ hℓ _ ↦
          mul_nonneg (gainCoeff_net_mem_Icc hb le_rfl hnet (by omega)
            (Finset.ne_of_mem_erase hℓ)).1 (haarVar_nonneg hb0 _ _)
  have hcardI : (I.card : ℝ) = (m : ℝ) - 2 * k := by
    rw [hI, Nat.card_Icc]
    rw [show m - 1 - k + 1 - k = m - 2 * k by omega, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcardI] at hsum
  have hres := cellResVar_nonneg hb0 hf (D := m) (b := b)
  rw [variance_scrambledLaw hb hn hfm hf d]
  have hpow3 : (b : ℝ) ^ (3 * m) * ((b ^ m : ℕ) : ℝ)⁻¹ = (b : ℝ) ^ (2 * m) := by
    push_cast
    rw [show 3 * m = 2 * m + m by ring, pow_add]
    field_simp
  calc ((m : ℝ) - 2 * k) * (g₀ ^ 2 * ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ (2 * k + 4)))
      = (b : ℝ) ^ (2 * m) * (((m : ℝ) - 2 * k) * C) := by
        rw [hC]
        have hm1 : m - 1 + 2 = m + 1 := by omega
        rw [hm1]
        field_simp
        rw [sq_abs]
        ring
    _ ≤ (b : ℝ) ^ (2 * m) * (cellResVar b m f + ∑ ℓ ∈ (Finset.univ : Finset
        (Fin 2 → Fin (m + 1))).erase 0, gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ) :=
        mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hb'.le _)
    _ = _ := by
        rw [← hpow3]
        ring

/-- **The within-cell variance of a Lipschitz integrand**: if
`|f x - f x'| ≤ L Σ_j |x_j - x'_j|` on the cube, then `σ²_{>D} ≤ (L s b^{-D})²`. -/
theorem cellResVar_le (hb : 0 < b) {s : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin s → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|) :
    cellResVar b D f ≤ (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 := by
  have hU := isProbabilityMeasure_uniformCube s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  have hcell : ∀ y : Fin s → Fin D → Fin b,
      cellSq f y - cellAvg f y ^ 2 ≤ (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 := by
    intro y
    have hXL := memLp_comp_cellPoint hb hf y
    have hv := variance_eq_sub hXL
    have e : cellSq f y - cellAvg f y ^ 2 = Var[fun u ↦ f (cellPoint y u); uniformCube s] := by
      rw [hv]
      rfl
    rw [e, ← variance_sub_const hXL.aestronglyMeasurable (f (cellPoint y 0))]
    refine (variance_le_expectation_sq
      (hXL.aestronglyMeasurable.sub aestronglyMeasurable_const)).trans ?_
    have hbound : ∀ᵐ u ∂(uniformCube s), ((fun u ↦ f (cellPoint y u) - f (cellPoint y 0)) ^ 2) u ≤
        (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 := by
      filter_upwards [ae_mem_cube_uniformCube s] with u hu
      have h0 : ∀ _j : Fin s, (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := fun _ ↦ ⟨le_rfl, one_pos⟩
      have hl := hL (cellPoint y u) (cellPoint y 0) (fun j ↦ digitPoint_mem_Ico hb _ (hu j))
        (fun j ↦ digitPoint_mem_Ico hb _ (h0 j))
      have hcoord : ∀ j, |cellPoint y u j - cellPoint y 0 j| ≤ ((b : ℝ) ^ D)⁻¹ := by
        intro j
        change |digitPoint (y j) (u j) - digitPoint (y j) 0| ≤ _
        unfold digitPoint
        rw [show ((cellVal (y j) : ℝ) + u j) / (b : ℝ) ^ D - ((cellVal (y j) : ℝ) + 0) /
          (b : ℝ) ^ D = u j / (b : ℝ) ^ D by ring, abs_div, abs_of_nonneg (hu j).1,
          abs_of_pos (pow_pos hb' D), div_eq_mul_inv]
        exact mul_le_of_le_one_left (inv_nonneg.2 (pow_pos hb' D).le) (hu j).2.le
      have hsum : ∑ j, |cellPoint y u j - cellPoint y 0 j| ≤ s * ((b : ℝ) ^ D)⁻¹ := by
        calc ∑ j, |cellPoint y u j - cellPoint y 0 j| ≤ ∑ _j : Fin s, ((b : ℝ) ^ D)⁻¹ :=
              Finset.sum_le_sum fun j _ ↦ hcoord j
          _ = s * ((b : ℝ) ^ D)⁻¹ := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have habs : |f (cellPoint y u) - f (cellPoint y 0)| ≤ L * s * ((b : ℝ) ^ D)⁻¹ := by
        rw [mul_assoc]
        exact hl.trans (mul_le_mul_of_nonneg_left hsum hL0)
      change (f (cellPoint y u) - f (cellPoint y 0)) ^ 2 ≤ _
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    calc ∫ u, ((fun u ↦ f (cellPoint y u) - f (cellPoint y 0)) ^ 2) u ∂(uniformCube s)
        ≤ ∫ _u, (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 ∂(uniformCube s) :=
          integral_mono_ae ((hXL.sub (memLp_const _)).integrable_sq) (integrable_const _) hbound
      _ = (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  unfold cellResVar
  rw [div_le_iff₀ hbD]
  calc ∑ y : Fin s → Fin D → Fin b, (cellSq f y - cellAvg f y ^ 2)
      ≤ ∑ _y : Fin s → Fin D → Fin b, (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 :=
        Finset.sum_le_sum fun y _ ↦ hcell y
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_fin]
        push_cast
        ring

/-- A truncated geometric tail: for `0 ≤ x ≤ 1/2`, `Σ_{t ≤ j < N} x^j ≤ 2 x^t`. -/
theorem sum_range_ite_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (t : ℕ) :
    ∀ N : ℕ, ∑ j ∈ Finset.range N, (if t ≤ j then x ^ j else 0) ≤ 2 * x ^ t - 2 * x ^ max N t := by
  intro N
  induction N with
  | zero =>
    rw [Finset.sum_range_zero, Nat.zero_max]
    ring_nf
    exact le_rfl
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hN : t ≤ N
    · rw [ite_eq_left hN, max_eq_left (by omega)]
      rw [max_eq_left hN] at ih
      have h1 : x ^ (N + 1) ≤ x ^ N / 2 := by
        rw [pow_succ]
        nlinarith [pow_nonneg hx0 N]
      linarith
    · rw [ite_eq_right hN, add_zero, max_eq_right (by omega)]
      rw [max_eq_right (by omega)] at ih
      exact ih

/-- **Owen's variance upper bound for smooth integrands, `s = 2`** (Owen 1997b): for a scrambled
`(0,m,2)`-net in base `b` with `m` digits and an integrand that is `L`-Lipschitz on the cube
(`|f x - f x'| ≤ L (|Δx₀| + |Δx₁|)`) with mixed differences bounded by `M |Δx₀| |Δx₁|`,
`b^{3m} Var(μ̂) ≤ 4 L² + 64 M² b² (m + 1)`, i.e. `Var(μ̂) = O(n^{-3} log n)`. -/
theorem pow_mul_variance_scrambledLaw_two_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) {M L : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |mixDiff f x x'| ≤ M * |x 0 - x' 0| * |x 1 - x' 1|)
    (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|) :
    (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f d] ≤
      4 * L ^ 2 + 64 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hn : b ^ m ≠ 0 := (Nat.pow_pos hb0).ne'
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  set a : ℝ := (b : ℝ) / ((b : ℝ) - 1) with ha
  have ha2 : a ≤ 2 := by
    rw [ha, div_le_iff₀ hb1]
    linarith
  have ha0 : 0 ≤ a := div_nonneg hb'.le hb1.le
  set x : ℝ := ((b : ℝ) ^ 2)⁻¹ with hx
  have hx0 : 0 ≤ x := inv_nonneg.2 (pow_nonneg hb'.le 2)
  have hx2 : x ≤ 1 / 2 := by
    rw [hx, inv_le_comm₀ (pow_pos hb' 2) (by norm_num)]
    nlinarith
  set T : (Fin 2 → Fin (m + 1)) → ℝ := fun ℓ ↦
    if m + 1 ≤ (ℓ 0 : ℕ) + ℓ 1 then a * (16 * M ^ 2 * (b : ℝ) ^ 4) * x ^ ((ℓ 0 : ℕ) + ℓ 1)
      else 0 with hT
  have hT0 : ∀ ℓ, 0 ≤ T ℓ := fun ℓ ↦ by
    simp only [hT]
    split_ifs
    · positivity
    · exact le_rfl
  have hinv : ∀ k : ℕ, 1 ≤ k → ((b : ℝ) ^ (k - 1))⁻¹ = (b : ℝ) * ((b : ℝ) ^ k)⁻¹ := by
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  have hper : ∀ ℓ ∈ (Finset.univ : Finset (Fin 2 → Fin (m + 1))).erase 0,
      gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ ≤ T ℓ := by
    intro ℓ hℓ
    have hne := Finset.ne_of_mem_erase hℓ
    have hl0 : (ℓ 0 : ℕ) ≤ m := Nat.lt_succ_iff.1 (ℓ 0).isLt
    have hl1 : (ℓ 1 : ℕ) ≤ m := Nat.lt_succ_iff.1 (ℓ 1).isLt
    by_cases h : m + 1 ≤ (ℓ 0 : ℕ) + ℓ 1
    · simp only [hT, h, ↓reduceIte]
      have hκ : ∀ j, (ℓ j : ℕ) = ((ℓ j : ℕ) - 1) + 1 := fun j ↦ by
        fin_cases j
        · change (ℓ 0 : ℕ) = (ℓ 0 : ℕ) - 1 + 1
          omega
        · change (ℓ 1 : ℕ) = (ℓ 1 : ℕ) - 1 + 1
          omega
      have hσ := haarVar_cellAvg_le hb0 hf hM0 hM (κ := fun j ↦ (ℓ j : ℕ) - 1) hκ
        (fun j ↦ by have := Nat.lt_succ_iff.1 (ℓ j).isLt; omega)
      have hΓ := gainCoeff_net_mem_Icc hb le_rfl hnet (by omega) hne
      rw [show 2 - 1 = 1 from rfl, pow_one] at hΓ
      have hσ' : haarVar (cellAvg (b := b) f) ℓ ≤ 16 * M ^ 2 * (b : ℝ) ^ 4 *
          x ^ ((ℓ 0 : ℕ) + ℓ 1) := by
        refine hσ.trans (le_of_eq ?_)
        have hxk : ∀ k : ℕ, ((b : ℝ) ^ 2)⁻¹ ^ k = (((b : ℝ) ^ k)⁻¹) ^ 2 := fun k ↦ by
          rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
        rw [hinv _ (by omega), hinv _ (by omega), hx, pow_add, hxk, hxk]
        ring
      calc gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ
          ≤ a * haarVar (cellAvg (b := b) f) ℓ :=
            mul_le_mul_of_nonneg_right hΓ.2 (haarVar_nonneg hb0 _ _)
        _ ≤ a * (16 * M ^ 2 * (b : ℝ) ^ 4 * x ^ ((ℓ 0 : ℕ) + ℓ 1)) :=
            mul_le_mul_of_nonneg_left hσ' ha0
        _ = _ := by ring
    · simp only [hT, h, ↓reduceIte]
      rw [gainCoeff_net_eq_zero hb le_rfl hnet hne (by rw [Fin.sum_univ_two]; omega), zero_mul]
  have hsumT : ∑ ℓ : Fin 2 → Fin (m + 1), T ℓ ≤
      a * (16 * M ^ 2 * (b : ℝ) ^ 4) * ((m + 1) * (2 * x ^ (m + 1))) := by
    rw [sum_fin_two_pi]
    have e : ∀ l₀ l₁ : Fin (m + 1), T ![l₀, l₁] = a * (16 * M ^ 2 * (b : ℝ) ^ 4) *
        (x ^ (l₀ : ℕ) * (if m + 1 - l₀ ≤ (l₁ : ℕ) then x ^ (l₁ : ℕ) else 0)) := by
      intro l₀ l₁
      simp only [hT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hl0 : (l₀ : ℕ) ≤ m := Nat.lt_succ_iff.1 l₀.isLt
      by_cases h : m + 1 ≤ (l₀ : ℕ) + l₁
      · rw [ite_eq_left h, ite_eq_left (by omega), pow_add]
      · rw [ite_eq_right h, ite_eq_right (by omega), mul_zero, mul_zero]
    simp only [e, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ l₀ : Fin (m + 1), x ^ (l₀ : ℕ) * ∑ l₁ : Fin (m + 1),
          (if m + 1 - l₀ ≤ (l₁ : ℕ) then x ^ (l₁ : ℕ) else 0)
        ≤ ∑ l₀ : Fin (m + 1), x ^ (l₀ : ℕ) * (2 * x ^ (m + 1 - l₀)) := by
          refine Finset.sum_le_sum fun l₀ _ ↦ mul_le_mul_of_nonneg_left ?_ (pow_nonneg hx0 _)
          rw [Fin.sum_univ_eq_sum_range (fun l₁ ↦ if m + 1 - l₀ ≤ l₁ then x ^ l₁ else 0)]
          have := sum_range_ite_pow_le hx0 hx2 (m + 1 - l₀) (m + 1)
          have hmax : 0 ≤ 2 * x ^ max (m + 1) (m + 1 - (l₀ : ℕ)) := by positivity
          linarith
      _ = ∑ _l₀ : Fin (m + 1), 2 * x ^ (m + 1) := by
          refine Finset.sum_congr rfl fun l₀ _ ↦ ?_
          have hl0 : (l₀ : ℕ) ≤ m := Nat.lt_succ_iff.1 l₀.isLt
          rw [← mul_assoc, mul_comm (x ^ (l₀ : ℕ)) 2, mul_assoc, ← pow_add,
            Nat.add_sub_cancel' (by omega)]
      _ = (m + 1) * (2 * x ^ (m + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hsum := (Finset.sum_le_sum hper).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.erase_subset 0 Finset.univ) fun ℓ _ _ ↦ hT0 ℓ)
  have hres := cellResVar_le hb0 hf hL0 hL (D := m)
  rw [variance_scrambledLaw hb hn hfm hf d]
  have hpow3 : (b : ℝ) ^ (3 * m) * ((b ^ m : ℕ) : ℝ)⁻¹ = (b : ℝ) ^ (2 * m) := by
    push_cast
    rw [show 3 * m = 2 * m + m by ring, pow_add]
    field_simp
  have hxm : (b : ℝ) ^ (2 * m) * x ^ (m + 1) = ((b : ℝ) ^ 2)⁻¹ := by
    rw [hx, inv_pow, pow_mul, pow_succ]
    have : (0 : ℝ) < ((b : ℝ) ^ 2) ^ m := pow_pos (pow_pos hb' 2) m
    field_simp
    ring
  rw [← mul_assoc, hpow3]
  calc (b : ℝ) ^ (2 * m) * (cellResVar b m f + ∑ ℓ ∈ (Finset.univ : Finset
        (Fin 2 → Fin (m + 1))).erase 0, gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ)
      ≤ (b : ℝ) ^ (2 * m) * ((L * ((2 : ℕ) : ℝ) * ((b : ℝ) ^ m)⁻¹) ^ 2 +
          a * (16 * M ^ 2 * (b : ℝ) ^ 4) * ((m + 1) * (2 * x ^ (m + 1)))) :=
        mul_le_mul_of_nonneg_left (add_le_add hres (hsum.trans hsumT)) (pow_nonneg hb'.le _)
    _ = 4 * L ^ 2 + a * (32 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1)) := by
        have hbm : (b : ℝ) ^ (2 * m) * (((b : ℝ) ^ m)⁻¹) ^ 2 = 1 := by
          rw [inv_pow, ← pow_mul, mul_comm m 2]
          field_simp
        have e1 : (b : ℝ) ^ (2 * m) * ((L * ((2 : ℕ) : ℝ) * ((b : ℝ) ^ m)⁻¹) ^ 2 +
            a * (16 * M ^ 2 * (b : ℝ) ^ 4) * ((m + 1) * (2 * x ^ (m + 1)))) =
            4 * L ^ 2 * ((b : ℝ) ^ (2 * m) * (((b : ℝ) ^ m)⁻¹) ^ 2) +
              a * (32 * M ^ 2 * (b : ℝ) ^ 4 * (m + 1)) * ((b : ℝ) ^ (2 * m) * x ^ (m + 1)) := by
          push_cast
          ring
        rw [e1, hbm, hxm]
        field_simp
    _ ≤ 4 * L ^ 2 + 2 * (32 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1)) := by
        have : 0 ≤ 32 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1) := by positivity
        nlinarith
    _ = 4 * L ^ 2 + 64 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1) := by ring

/-- **`Var ≍ n⁻³ log n` for smooth non-degenerate integrands, `s = 2`** (Owen 1997b): for
scrambled `(0,m,2)`-nets with `m` digits and an integrand that is Lipschitz, has bounded mixed
differences, and has a non-zero strict mixed derivative `g₀` at some point `xc` of the cube, there
are constants `0 < c` and `C` with `c m ≤ b^{3m} Var(μ̂) ≤ C (m + 1)` for all large `m`. -/
theorem variance_scrambledLaw_two_asymp (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) {M L : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |mixDiff f x x'| ≤ M * |x 0 - x' 0| * |x 1 - x' 1|)
    (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|)
    {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1) {g₀ : ℝ} (hg₀ : g₀ ≠ 0)
    (hg : ∀ ε > 0, ∃ δ > 0, ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, |x j - xc j| < δ) → (∀ j, |x' j - xc j| < δ) →
      |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤ ε * |x 0 - x' 0| * |x 1 - x' 1|) :
    ∃ c > 0, ∃ C : ℝ, ∀ᶠ m in atTop,
      c * m ≤ (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f (d m)] ∧
      (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f (d m)] ≤ C * (m + 1) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  obtain ⟨δ, hδ, hgδ⟩ := hg (|g₀| * ((b : ℝ) - 1) ^ 2 / (32 * (b : ℝ) ^ 2)) (by positivity)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ
    (show 1 / (b : ℝ) < 1 by rw [div_lt_one hb']; exact Nat.one_lt_cast.2 hb)
  have hk' : ((b : ℝ) ^ k)⁻¹ ≤ δ := by
    rw [one_div_pow, one_div] at hk
    exact hk.le
  set c₀ : ℝ := g₀ ^ 2 * ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ (2 * k + 4)) with hc₀
  have hc₀pos : 0 < c₀ := by
    have : 0 < g₀ ^ 2 := by positivity
    positivity
  refine ⟨c₀ / 2, by positivity, 4 * L ^ 2 + 64 * M ^ 2 * (b : ℝ) ^ 2, ?_⟩
  filter_upwards [eventually_ge_atTop (4 * k + 1)] with m hm
  constructor
  · have h := pow_mul_variance_scrambledLaw_two_ge hb (hnet m) hfm hf hxc hgδ hk' (by omega)
    have hmk : (m : ℝ) / 2 ≤ (m : ℝ) - 2 * k := by
      have : ((4 * k + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
      push_cast at this
      linarith
    calc c₀ / 2 * m = (m / 2) * c₀ := by ring
      _ ≤ ((m : ℝ) - 2 * k) * c₀ := mul_le_mul_of_nonneg_right hmk hc₀pos.le
      _ ≤ _ := h
  · have h := pow_mul_variance_scrambledLaw_two_le hb (hnet m) hfm hf hM0 hM hL0 hL
    have hm1 : (1 : ℝ) ≤ m + 1 := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    calc (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f (d m)]
        ≤ 4 * L ^ 2 + 64 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1) := h
      _ ≤ 4 * L ^ 2 * (m + 1) + 64 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1) := by
          have : 0 ≤ 4 * L ^ 2 := by positivity
          nlinarith
      _ = (4 * L ^ 2 + 64 * M ^ 2 * (b : ℝ) ^ 2) * (m + 1) := by ring

/-- The product integrand `f(x) = x₀ x₁`. -/
def prodFn (x : Fin 2 → ℝ) : ℝ := x 0 * x 1

/-- The mixed difference of `x₀ x₁` is exactly `Δx₀ Δx₁`. -/
theorem mixDiff_prodFn (x x' : Fin 2 → ℝ) :
    mixDiff prodFn x x' = (x 0 - x' 0) * (x 1 - x' 1) := by
  unfold mixDiff prodFn
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- **The scrambled-net variance of `x₀ x₁` is of exact order `n⁻³ log n`** (`s = 2`, any base
`b ≥ 2`, `(0,m,2)`-nets with `m` digits, e.g. the Hammersley net):
`m (b-1)⁴/(64 b⁴) ≤ b^{3m} Var(μ̂) ≤ 4 + 64 b² (m + 1)`. For additive integrands
`b^{3m} Var(μ̂)` converges instead (`tendsto_cube_mul_variance_scrambledLaw_addFn`): the extra
`log n` comes from the interaction, spread over the `m` resolution splits `κ₀ + κ₁ = m - 1`. -/
theorem variance_scrambledLaw_prodFn (hb : 1 < b) {m : ℕ} (hm : 1 ≤ m)
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) :
    (m : ℝ) * (((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4)) ≤
      (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw prodFn d] ∧
    (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw prodFn d] ≤
      4 + 64 * (b : ℝ) ^ 2 * (m + 1) := by
  have hU := isProbabilityMeasure_uniformCube 2
  have hfm : Measurable prodFn :=
    (measurable_pi_apply 0).mul (measurable_pi_apply 1)
  have hf : MemLp prodFn 2 (uniformCube 2) := by
    refine MemLp.of_bound hfm.aestronglyMeasurable 1 ?_
    filter_upwards [ae_mem_cube_uniformCube 2] with x hx
    rw [Real.norm_eq_abs, prodFn, abs_mul]
    have h0 : |x 0| ≤ 1 := abs_le.2 ⟨by linarith [(hx 0).1], (hx 0).2.le⟩
    have h1 : |x 1| ≤ 1 := abs_le.2 ⟨by linarith [(hx 1).1], (hx 1).2.le⟩
    nlinarith [abs_nonneg (x 0), abs_nonneg (x 1)]
  have hxc : ∀ j, (0 : Fin 2 → ℝ) j ∈ Set.Ico (0 : ℝ) 1 := fun _ ↦ ⟨le_rfl, one_pos⟩
  constructor
  · have h := pow_mul_variance_scrambledLaw_two_ge hb hnet hfm hf hxc (g₀ := 1) (δ := 2)
      (fun x x' _ _ _ _ ↦ by
        rw [mixDiff_prodFn, one_mul, sub_self, abs_zero]
        positivity) (k := 0) (by norm_num) (by omega)
    simp only [Nat.cast_zero, mul_zero, sub_zero, one_pow, one_mul, zero_add] at h
    exact h
  · have h := pow_mul_variance_scrambledLaw_two_le hb hnet hfm hf (M := 1) (L := 1) zero_le_one
      (fun x x' _ _ ↦ by rw [mixDiff_prodFn, abs_mul, one_mul]) zero_le_one
      (fun x x' hx hx' ↦ by
        rw [prodFn, prodFn, Fin.sum_univ_two, one_mul]
        have e : x 0 * x 1 - x' 0 * x' 1 = x 0 * (x 1 - x' 1) + x' 1 * (x 0 - x' 0) := by ring
        rw [e]
        have h0 : |x 0| ≤ 1 := abs_le.2 ⟨by linarith [(hx 0).1], (hx 0).2.le⟩
        have h1 : |x' 1| ≤ 1 := abs_le.2 ⟨by linarith [(hx' 1).1], (hx' 1).2.le⟩
        calc |x 0 * (x 1 - x' 1) + x' 1 * (x 0 - x' 0)|
            ≤ |x 0| * |x 1 - x' 1| + |x' 1| * |x 0 - x' 0| := by
              rw [← abs_mul, ← abs_mul]
              exact abs_add_le _ _
          _ ≤ 1 * |x 1 - x' 1| + 1 * |x 0 - x' 0| := by
              gcongr
          _ = |x 0 - x' 0| + |x 1 - x' 1| := by ring)
    simpa only [one_pow, mul_one] using h

/-- **The average conditional variance given the scramble** is the within-cell part:
`E_ρ[Var(μ̂ | ρ)] = n⁻¹ σ²_{>D}`. (Given the scramble, the points are independent and the only
randomness is in the remainders.) -/
theorem avg_variance_scrambledEstimate (hb : 0 < b) {s n : ℕ} (hn : n ≠ 0)
    {f : (Fin s → ℝ) → ℝ} (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b) :
    (Fintype.card (Fin s → Scramble b D) : ℝ)⁻¹ *
      ∑ ρ, Var[scrambledEstimate f d ρ; remLaw s n] = (n : ℝ)⁻¹ * cellResVar b D f := by
  have hQ := isProbabilityMeasure_remLaw s n
  have hR : (0 : ℝ) < (Fintype.card (Scramble b D) : ℝ) ^ s :=
    pow_pos (Nat.cast_pos.2 Fintype.card_pos) s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hvar : ∀ ρ, Var[scrambledEstimate f d ρ; remLaw s n] = ((n : ℝ)⁻¹) ^ 2 *
      ∑ i, (cellSq f (scrambleVec ρ (d i)) - cellAvg f (scrambleVec ρ (d i)) ^ 2) := by
    intro ρ
    rw [variance_eq_sub (memLp_scrambledEstimate hb hf d ρ)]
    change ∫ u, scrambledEstimate f d ρ u ^ 2 ∂(remLaw s n) -
      (∫ u, scrambledEstimate f d ρ u ∂(remLaw s n)) ^ 2 = _
    rw [integral_sq_scrambledEstimate hb hf d ρ, integral_scrambledEstimate hb hf d ρ]
    ring
  simp only [hvar, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [sum_scrambleVec hb _ (fun y ↦ cellSq f y - cellAvg f y ^ 2)]
  rw [card_scramble_pi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold cellResVar
  field_simp

/-- **For smooth non-degenerate integrands in `s = 2`, the remainders carry a vanishing share of
the variance**: `E_ρ[Var(μ̂ | ρ)] / Var(μ̂) → 0`. By the law of total variance, almost all of the
variance is `Var(E[μ̂ | ρ])`, the fluctuation due to the nested scramble, under which the points
are dependent. A CLT therefore cannot come from the independent remainders (a Lindeberg argument
conditional on the scramble), unlike in the additive case: this is the part of Loh's theorem that
needs his dependent-sum argument. -/
theorem tendsto_avg_variance_given_scramble_div (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) {M L : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |mixDiff f x x'| ≤ M * |x 0 - x' 0| * |x 1 - x' 1|)
    (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|)
    {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1) {g₀ : ℝ} (hg₀ : g₀ ≠ 0)
    (hg : ∀ ε > 0, ∃ δ > 0, ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, |x j - xc j| < δ) → (∀ j, |x' j - xc j| < δ) →
      |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤ ε * |x 0 - x' 0| * |x 1 - x' 1|) :
    Tendsto (fun m ↦ ((Fintype.card (Fin 2 → Scramble b m) : ℝ)⁻¹ *
      ∑ ρ, Var[scrambledEstimate f (d m) ρ; remLaw 2 (b ^ m)]) /
        Var[fun x ↦ x; scrambledLaw f (d m)]) atTop (𝓝 0) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  obtain ⟨c, hc, C, hev⟩ := variance_scrambledLaw_two_asymp hb d hnet hfm hf hM0 hM hL0 hL hxc
    hg₀ hg
  have hlim : Tendsto (fun m : ℕ ↦ (4 * L ^ 2 / c) / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards with m
    refine div_nonneg (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun ρ _ ↦ variance_nonneg _ _)) (variance_nonneg _ _)
  · filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hn : b ^ m ≠ 0 := (Nat.pow_pos hb0).ne'
    rw [avg_variance_scrambledEstimate hb0 hn hf (d m)]
    have hres := cellResVar_le hb0 hf hL0 hL (D := m)
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 hm1
    have hV : c * m / (b : ℝ) ^ (3 * m) ≤ Var[fun x ↦ x; scrambledLaw f (d m)] := by
      rw [div_le_iff₀ (pow_pos hb' _), mul_comm _ ((b : ℝ) ^ (3 * m))]
      exact hm.1
    have hVpos : 0 < Var[fun x ↦ x; scrambledLaw f (d m)] :=
      lt_of_lt_of_le (by positivity) hV
    rw [div_le_div_iff₀ hVpos hmpos]
    have hnum : ((b ^ m : ℕ) : ℝ)⁻¹ * cellResVar b m f ≤
        ((b ^ m : ℕ) : ℝ)⁻¹ * (L * ((2 : ℕ) : ℝ) * ((b : ℝ) ^ m)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_left hres (inv_nonneg.2 (Nat.cast_nonneg _))
    have e : ((b ^ m : ℕ) : ℝ)⁻¹ * (L * ((2 : ℕ) : ℝ) * ((b : ℝ) ^ m)⁻¹) ^ 2 * (m : ℝ) =
        (4 * L ^ 2 / c) * (c * m / (b : ℝ) ^ (3 * m)) := by
      push_cast
      rw [show 3 * m = m + m + m by ring, pow_add, pow_add]
      field_simp
      ring
    calc ((b ^ m : ℕ) : ℝ)⁻¹ * cellResVar b m f * (m : ℝ)
        ≤ ((b ^ m : ℕ) : ℝ)⁻¹ * (L * ((2 : ℕ) : ℝ) * ((b : ℝ) ^ m)⁻¹) ^ 2 * (m : ℝ) :=
          mul_le_mul_of_nonneg_right hnum hmpos.le
      _ = (4 * L ^ 2 / c) * (c * m / (b : ℝ) ^ (3 * m)) := e
      _ ≤ 4 * L ^ 2 / c * Var[fun x ↦ x; scrambledLaw f (d m)] :=
          mul_le_mul_of_nonneg_left hV (by positivity)

/-- **A linear approximation from a derivative bound**: if `φ' t` stays within `η` of `c` on the
segment between `a` and `b`, then `|φ b - φ a - c (b - a)| ≤ η |b - a|`. -/
theorem abs_sub_sub_mul_le_of_deriv {φ φ' : ℝ → ℝ} {a b c η : ℝ}
    (hφ : ∀ t ∈ Set.uIcc a b, HasDerivAt φ (φ' t) t) (hη : ∀ t ∈ Set.uIcc a b, |φ' t - c| ≤ η) :
    |φ b - φ a - c * (b - a)| ≤ η * |b - a| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t ↦ φ t - c * t)
    (f' := fun t ↦ φ' t - c) (s := Set.uIcc a b) (C := η)
    (fun t ht ↦ ((hφ t ht).sub ((hasDerivAt_id t).const_mul c)).hasDerivWithinAt.congr_deriv
      (by ring))
    (fun t ht ↦ by rw [Real.norm_eq_abs]; exact hη t ht) (convex_uIcc a b)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs] at h
  rw [show φ b - φ a - c * (b - a) = φ b - c * b - (φ a - c * a) by ring]
  exact h

/-- **Mixed differences from a mixed partial derivative** (mean value theorem twice): if
`f₁ = ∂f/∂x₁` and `f₀₁ = ∂f₁/∂x₀` exist everywhere and `|f₀₁ - g₀| ≤ ε` on the rectangle spanned
by `x` and `x'`, then `|mixDiff f x x' - g₀ Δx₀ Δx₁| ≤ ε |Δx₀| |Δx₁|`. -/
theorem abs_mixDiff_sub_le_of_deriv {f f₁ f₀₁ : (Fin 2 → ℝ) → ℝ}
    (h₁ : ∀ x : Fin 2 → ℝ, HasDerivAt (fun t ↦ f ![x 0, t]) (f₁ x) (x 1))
    (h₀₁ : ∀ x : Fin 2 → ℝ, HasDerivAt (fun t ↦ f₁ ![t, x 1]) (f₀₁ x) (x 0))
    {x x' : Fin 2 → ℝ} {g₀ ε : ℝ}
    (hε : ∀ r ∈ Set.uIcc (x' 0) (x 0), ∀ t ∈ Set.uIcc (x' 1) (x 1), |f₀₁ ![r, t] - g₀| ≤ ε) :
    |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤ ε * |x 0 - x' 0| * |x 1 - x' 1| := by
  have hv : ∀ y : Fin 2 → ℝ, (![y 0, y 1] : Fin 2 → ℝ) = y := fun y ↦ by
    funext j
    fin_cases j <;> rfl
  have hd1 : ∀ r t : ℝ, HasDerivAt (fun t' ↦ f ![r, t']) (f₁ ![r, t]) t := fun r t ↦ by
    have := h₁ ![r, t]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using this
  have hd01 : ∀ r t : ℝ, HasDerivAt (fun r' ↦ f₁ ![r', t]) (f₀₁ ![r, t]) r := fun r t ↦ by
    have := h₀₁ ![r, t]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using this
  set Δ₀ := x 0 - x' 0
  -- the inner difference
  have hinner : ∀ t ∈ Set.uIcc (x' 1) (x 1),
      |(f₁ ![x 0, t] - f₁ ![x' 0, t]) - g₀ * Δ₀| ≤ ε * |Δ₀| := by
    intro t ht
    exact abs_sub_sub_mul_le_of_deriv (φ := fun r ↦ f₁ ![r, t]) (fun r _ ↦ hd01 r t)
      (fun r hr ↦ hε r hr t ht)
  have houter := abs_sub_sub_mul_le_of_deriv (a := x' 1) (b := x 1)
    (φ := fun t ↦ f ![x 0, t] - f ![x' 0, t]) (φ' := fun t ↦ f₁ ![x 0, t] - f₁ ![x' 0, t])
    (c := g₀ * Δ₀) (fun t _ ↦ (hd1 (x 0) t).sub (hd1 (x' 0) t)) hinner
  have hmix : mixDiff f x x' = (f ![x 0, x 1] - f ![x' 0, x 1]) -
      (f ![x 0, x' 1] - f ![x' 0, x' 1]) := by
    unfold mixDiff
    rw [hv x, hv x']
    ring
  rw [hmix]
  calc |(f ![x 0, x 1] - f ![x' 0, x 1]) - (f ![x 0, x' 1] - f ![x' 0, x' 1]) -
        g₀ * Δ₀ * (x 1 - x' 1)| ≤ ε * |Δ₀| * |x 1 - x' 1| := houter
    _ = ε * |x 0 - x' 0| * |x 1 - x' 1| := rfl

/-- **Owen's `Var ≍ n⁻³ log n` from a continuous mixed partial derivative** (`s = 2`): if
`f₁ = ∂f/∂x₁` and `f₀₁ = ∂²f/∂x₀∂x₁` exist everywhere, `f₀₁` is continuous on `[0,1]²` and
non-zero at some point of `[0,1)²`, and `f` is Lipschitz on the cube, then for scrambled
`(0,m,2)`-nets with `m` digits, `c m ≤ b^{3m} Var(μ̂) ≤ C (m + 1)` eventually. -/
theorem variance_scrambledLaw_two_asymp_of_deriv (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f f₁ f₀₁ : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2))
    (h₁ : ∀ x : Fin 2 → ℝ, HasDerivAt (fun t ↦ f ![x 0, t]) (f₁ x) (x 1))
    (h₀₁ : ∀ x : Fin 2 → ℝ, HasDerivAt (fun t ↦ f₁ ![t, x 1]) (f₀₁ x) (x 0))
    (hc : ContinuousOn f₀₁ (Set.pi Set.univ fun _ ↦ Set.Icc (0 : ℝ) 1))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|)
    {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1) (hne : f₀₁ xc ≠ 0) :
    ∃ c > 0, ∃ C : ℝ, ∀ᶠ m in atTop,
      c * m ≤ (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f (d m)] ∧
      (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f (d m)] ≤ C * (m + 1) := by
  set K := Set.pi Set.univ fun _ : Fin 2 ↦ Set.Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ ↦ isCompact_Icc
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM xc fun j _ ↦ ⟨(hxc j).1, (hxc j).2.le⟩)
  have hrect : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) → ∀ r ∈ Set.uIcc (x' 0) (x 0),
      ∀ t ∈ Set.uIcc (x' 1) (x 1), (![r, t] : Fin 2 → ℝ) ∈ K := by
    intro x x' hx hx' r hr t ht j _
    have hseg : ∀ {a a' v : ℝ}, a ∈ Set.Ico (0 : ℝ) 1 → a' ∈ Set.Ico (0 : ℝ) 1 →
        v ∈ Set.uIcc a' a → v ∈ Set.Icc (0 : ℝ) 1 := by
      intro a a' v ha ha' hv
      rw [Set.mem_uIcc] at hv
      constructor <;> rcases hv with hv | hv <;> linarith [ha.1, ha.2, ha'.1, ha'.2, hv.1, hv.2]
    fin_cases j
    · exact hseg (hx 0) (hx' 0) hr
    · exact hseg (hx 1) (hx' 1) ht
  refine variance_scrambledLaw_two_asymp hb d hnet hfm hf hM0 (fun x x' hx hx' ↦ ?_) hL0 hL hxc
    hne (fun ε hε ↦ ?_)
  · have h := abs_mixDiff_sub_le_of_deriv h₁ h₀₁ (x := x) (x' := x') (g₀ := 0) (ε := M)
      (fun r hr t ht ↦ by
        rw [sub_zero, ← Real.norm_eq_abs]
        exact hM _ (hrect x x' hx hx' r hr t ht))
    simpa only [zero_mul, sub_zero] using h
  · have hcw : ContinuousWithinAt f₀₁ K xc := hc xc fun j _ ↦ ⟨(hxc j).1, (hxc j).2.le⟩
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 hcw ε hε
    refine ⟨δ, hδ, fun x x' hx hx' hxδ hx'δ ↦ ?_⟩
    refine abs_mixDiff_sub_le_of_deriv h₁ h₀₁ fun r hr t ht ↦ ?_
    have hseg : ∀ {a a' v : ℝ} (j : Fin 2), |a - xc j| < δ → |a' - xc j| < δ →
        v ∈ Set.uIcc a' a → |v - xc j| < δ := by
      intro a a' v j ha ha' hv
      rw [Set.mem_uIcc] at hv
      rw [abs_lt] at ha ha' ⊢
      constructor <;> rcases hv with hv | hv <;> linarith [ha.1, ha.2, ha'.1, ha'.2, hv.1, hv.2]
    have hdist : dist (![r, t] : Fin 2 → ℝ) xc < δ := by
      rw [dist_pi_lt_iff hδ]
      intro j
      fin_cases j
      · exact hseg 0 (hxδ 0) (hx'δ 0) hr
      · exact hseg 1 (hxδ 1) (hx'δ 1) ht
    exact (hδf (hrect x x' hx hx' r hr t ht) hdist).le

end RQMCMarkov.OwenScrambling
