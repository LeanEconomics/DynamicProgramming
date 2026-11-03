/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.LohGeneralConc

/-!
# Loh's CLT for a non-additive integrand: `x₀ x₁` on scrambled `(0,m,2)`-nets (post #2)

Post #2: with a digital net and Owen's nested uniform scramble "a standard CLT applies" (Loh
2003). `LohCLT` proves this, normalised by the standard deviation, for additive integrands,
where the error is a sum of independent terms given the scramble. For non-additive integrands
almost all of the variance comes from the scramble itself (`LohVariance`,
`tendsto_avg_variance_given_scramble_div`), and that argument fails. This module proves the CLT
for the simplest non-additive integrands, `f(x) = a x₀ x₁ + g₀(x₀) + g₁(x₁)` with `a ≠ 0` and
`C¹` coordinates `g_j` (the smooth integrands whose mixed derivative `∂²f/∂x₀∂x₁ = a` is a
non-zero constant), for every sequence of `(0,m,2)`-nets in base `b ≥ 2`
(`tendstoInDistribution_scrambledLaw_bilinAdd`), in particular for `x₀ x₁`
(`tendstoInDistribution_scrambledLaw_prodFn`) and the Hammersley nets
(`tendstoInDistribution_scrambledLaw_prodFn_hammersley`).

**The argument (not Loh's).** Loh uses Stein's method. Here the scramble of coordinate `0` is
conditioned on instead. Given `ρ₀`, the remainder-averaged error `S/n` of `x₀ x₁` is a sum of
independent centred terms, one for each node of the tree of coordinate `1`
(`LohGeneralProd.prodS_eq_sum_nodeTerm`), so a conditional Lindeberg (Lyapunov) bound applies
(`LohGeneralFinite.tendsto_unifAvg_cexp_nodeSum`). Its random conditional variance `V(ρ₀)`
concentrates (`LohGeneralConc`), because it is spread over the `m` levels of the tree of
coordinate `1`, which use asymptotically independent windows of levels of `ρ₀`. The normal limit
comes from the `m ≍ log n` levels, as Loh's does. The remainders and the additive part add a
vanishing share of the variance.

## Main results

* `unifAvg_fin_two`, `unifAvg_sq_prodS`: `E[S²] = E_{ρ₀} V(ρ₀)`.
* `integral_sq_sub_eq_variance_add`, `variance_scrambledLaw_eq_of_condMean`: the law of total
  variance for the scrambled estimator.
* `unifAvg_condVar_ge`: `E V ≥ (m (b-1)⁴/(64 b⁴) - 4)/n`, from Owen's lower bound
  (`LohVariance.variance_scrambledLaw_prodFn`).
* `tendsto_unifAvg_cexp_prodS`: the CLT for `S` itself, `S/√(E S²) ⇒ N(0,1)` in characteristic
  functions.
* `tendstoInDistribution_scrambledLaw_of_condMean`: the CLT for any Lipschitz `f` whose
  remainder-averaged error is `a S/n`.
* `tendstoInDistribution_scrambledLaw_bilinAdd`, `tendstoInDistribution_scrambledLaw_prodFn`,
  `tendstoInDistribution_scrambledLaw_prodFn_hammersley`: **Loh's CLT for `a x₀ x₁ + g₀(x₀) +
  g₁(x₁)`**, `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)`.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter Complex
open scoped Topology

variable {b : ℕ}

/-- Averages over pairs of scrambles are iterated averages. -/
theorem unifAvg_fin_two {X : Type*} [Fintype X] {𝕜 : Type*} [Field 𝕜] (G : (Fin 2 → X) → 𝕜) :
    unifAvg G = unifAvg (fun x₀ ↦ unifAvg (fun x₁ ↦ G ![x₀, x₁])) := by
  have hs : ∑ y, G y = ∑ x₀, ∑ x₁, G ![x₀, x₁] := by
    rw [← Fintype.sum_prod_type (f := fun p : X × X ↦ G ![p.1, p.2])]
    refine Fintype.sum_equiv (finTwoArrowEquiv X) _ _ fun y ↦ ?_
    congr 1
    funext i
    fin_cases i <;> rfl
  unfold unifAvg
  rw [hs, Fintype.card_fun, Fintype.card_fin, ← Finset.mul_sum, Nat.cast_pow]
  ring

/-- **The second moment of `S` given `ρ₀` is the conditional variance**:
`E_{ρ₁}[S²] = V(ρ₀)` (the node terms are independent and centred). -/
theorem unifAvg_sq_prodS {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (ρ₀ : Scramble b m) :
    unifAvg (fun ρ₁ : Scramble b m ↦ prodS d ![ρ₀, ρ₁] ^ 2) = condVar d ρ₀ := by
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  have e : (fun ρ₁ : Scramble b m ↦ prodS d ![ρ₀, ρ₁] ^ 2) = fun ρ₁ ↦
      (∑ γ ∈ (Finset.univ : Finset (Fin m × (Fin m → Option (Fin b)))),
        nodeTerm d ρ₀ γ (ρ₁ (id γ))) ^ 2 := by
    funext ρ₁
    rw [prodS_eq_sum_nodeTerm]
    rfl
  rw [e, unifAvg_sq_sum_eq (Set.injOn_id _) (fun γ _ ↦ unifAvg_nodeTerm d ρ₀ γ)]
  rfl

/-- `E[(X - c)²] = Var X + (E X - c)²`. -/
theorem integral_sq_sub_eq_variance_add {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : Ω → ℝ} (hX : MemLp X 2 Q) (c : ℝ) :
    ∫ ω, (X ω - c) ^ 2 ∂Q = Var[X; Q] + (∫ ω, X ω ∂Q - c) ^ 2 := by
  have hX1 : Integrable X Q := hX.integrable one_le_two
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) Q := hX.integrable_sq
  rw [variance_eq_sub hX]
  have e : (fun ω ↦ (X ω - c) ^ 2) = fun ω ↦ (X ω ^ 2 + (-2 * c) * X ω) + c ^ 2 :=
    funext fun ω ↦ by ring
  rw [e, integral_add (f := fun ω ↦ X ω ^ 2 + (-2 * c) * X ω) (g := fun _ ↦ c ^ 2)
    (hX2.add (hX1.const_mul _)) (integrable_const _),
    integral_add (f := fun ω ↦ X ω ^ 2) (g := fun ω ↦ (-2 * c) * X ω) hX2 (hX1.const_mul _),
    integral_const_mul, integral_const, probReal_univ, one_smul]
  change _ = ∫ ω, X ω ^ 2 ∂Q - (∫ ω, X ω ∂Q) ^ 2 + _
  ring

/-- **The law of total variance for the scrambled estimator**: if the remainder-averaged
estimator is `E[μ̂ | ρ] = μ + a S(ρ)`, then `Var(μ̂) = E_ρ[(a S)²] + E_ρ[Var(μ̂ | ρ)]`. -/
theorem variance_scrambledLaw_eq_of_condMean (hb : 0 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (uniformCube 2)) {a : ℝ} {S : (Fin 2 → Scramble b m) → ℝ}
    (hmean : ∀ ρ, ∫ u, scrambledEstimate f d ρ u ∂(remLaw 2 (b ^ m)) =
      ∫ x, f x ∂(uniformCube 2) + a * S ρ) :
    Var[fun x ↦ x; scrambledLaw f d] = unifAvg (fun ρ ↦ (a * S ρ) ^ 2) +
      unifAvg (fun ρ ↦ Var[scrambledEstimate f d ρ; remLaw 2 (b ^ m)]) := by
  have hQ := isProbabilityMeasure_remLaw 2 (b ^ m)
  rw [variance_scrambledLaw_eq_sum hb (Nat.pow_pos hb).ne' hfm hf d, ← unifAvg_add]
  change unifAvg _ = _
  congr 1
  funext ρ
  rw [integral_sq_sub_eq_variance_add (memLp_scrambledEstimate hb hf d ρ), hmean ρ]
  ring

/-- **The remainders' share of the variance**: for `f` `L`-Lipschitz on the cube,
`E_ρ[Var(μ̂ | ρ)] ≤ 4 L² / n³`. -/
theorem unifAvg_variance_le (hb : 0 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    {f : (Fin 2 → ℝ) → ℝ} (hf : MemLp f 2 (uniformCube 2)) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|) :
    unifAvg (fun ρ ↦ Var[scrambledEstimate f d ρ; remLaw 2 (b ^ m)]) ≤
      4 * L ^ 2 * (((b : ℝ) ^ m) ^ 3)⁻¹ := by
  have hbm : (0 : ℝ) < (b : ℝ) ^ m := pow_pos (Nat.cast_pos.2 hb) m
  have h := avg_variance_scrambledEstimate hb (Nat.pow_pos hb).ne' hf d
  have hc := cellResVar_le (D := m) hb hf hL0 hL
  unfold unifAvg
  rw [h, Nat.cast_pow]
  calc ((b : ℝ) ^ m)⁻¹ * cellResVar b m f ≤ ((b : ℝ) ^ m)⁻¹ * (L * 2 * ((b : ℝ) ^ m)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (inv_nonneg.2 hbm.le)
    _ = 4 * L ^ 2 * (((b : ℝ) ^ m) ^ 3)⁻¹ := by
        field_simp
        ring

/-- `∫ x₀ x₁ = 1/4` over the unit square. -/
theorem integral_prodFn : ∫ x, prodFn x ∂(uniformCube 2) = 1 / 4 := by
  have := isProbabilityMeasure_uniformIco
  have h := integral_pi_eval_mul (ν := uniformIco) (g := fun x : ℝ ↦ x) (h := fun x : ℝ ↦ x)
    aestronglyMeasurable_id aestronglyMeasurable_id (j := (0 : Fin 2)) (k := 1) (by decide)
  rw [integral_id_uniformIco] at h
  unfold prodFn
  rw [h]
  norm_num

/-- `x₀ x₁` is `1`-Lipschitz on the cube in the `ℓ¹` distance. -/
theorem abs_prodFn_sub_le {x x' : Fin 2 → ℝ} (hx : ∀ j, x j ∈ Set.Ico (0 : ℝ) 1)
    (hx' : ∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) :
    |prodFn x - prodFn x'| ≤ 1 * ∑ j, |x j - x' j| := by
  rw [prodFn, prodFn, Fin.sum_univ_two, one_mul]
  have e : x 0 * x 1 - x' 0 * x' 1 = x 0 * (x 1 - x' 1) + x' 1 * (x 0 - x' 0) := by ring
  rw [e]
  have h0 : |x 0| ≤ 1 := abs_le.2 ⟨by linarith [(hx 0).1], (hx 0).2.le⟩
  have h1 : |x' 1| ≤ 1 := abs_le.2 ⟨by linarith [(hx' 1).1], (hx' 1).2.le⟩
  calc |x 0 * (x 1 - x' 1) + x' 1 * (x 0 - x' 0)|
      ≤ |x 0| * |x 1 - x' 1| + |x' 1| * |x 0 - x' 0| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ 1 * |x 1 - x' 1| + 1 * |x 0 - x' 0| := by gcongr
    _ = |x 0 - x' 0| + |x 1 - x' 1| := by ring

/-- `E_ρ[S²] = E_{ρ₀} V(ρ₀)`. -/
theorem unifAvg_sq_prodS_eq {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) :
    unifAvg (fun ρ : Fin 2 → Scramble b m ↦ prodS d ρ ^ 2) =
      unifAvg (fun ρ₀ : Scramble b m ↦ condVar d ρ₀) := by
  rw [unifAvg_fin_two]
  congr 1
  funext ρ₀
  exact unifAvg_sq_prodS d ρ₀

/-- **The mean conditional variance has order `m/n`** (Owen 1997b's lower bound for `x₀ x₁`):
`E V ≥ (m (b-1)⁴/(64 b⁴) - 4)/n`. -/
theorem unifAvg_condVar_ge (hb : 1 < b) {m : ℕ} (hm : 1 ≤ m)
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) :
    (m * (((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4)) - 4) * ((b : ℝ) ^ m)⁻¹ ≤
      unifAvg (fun ρ₀ : Scramble b m ↦ condVar d ρ₀) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hN : (0 : ℝ) < (b : ℝ) ^ m := pow_pos (Nat.cast_pos.2 hb0) m
  have hvar := variance_scrambledLaw_eq_of_condMean hb0 measurable_prodFn memLp_prodFn (d := d)
    (a := 1) (S := fun ρ ↦ prodS d ρ / ((b ^ m : ℕ) : ℝ)) fun ρ ↦ by
      rw [integral_scrambledEstimate_prodFn hb0 hnet ρ, integral_prodFn, one_mul]
  have hlow := (variance_scrambledLaw_prodFn hb hm hnet).1
  have hrem := unifAvg_variance_le hb0 memLp_prodFn (d := d) zero_le_one
    fun x x' hx hx' ↦ abs_prodFn_sub_le hx hx'
  have hS : unifAvg (fun ρ : Fin 2 → Scramble b m ↦ (1 * (prodS d ρ / ((b ^ m : ℕ) : ℝ))) ^ 2) =
      ((b : ℝ) ^ m)⁻¹ ^ 2 * unifAvg (fun ρ₀ : Scramble b m ↦ condVar d ρ₀) := by
    rw [← unifAvg_sq_prodS_eq, ← unifAvg_const_mul]
    congr 1
    funext ρ
    rw [Nat.cast_pow]
    field_simp
  rw [hvar, hS] at hlow
  have h3 : (b : ℝ) ^ (3 * m) = ((b : ℝ) ^ m) ^ 3 := by rw [← pow_mul, mul_comm]
  rw [h3] at hlow
  set E := unifAvg (fun ρ₀ : Scramble b m ↦ condVar d ρ₀)
  set c := (m : ℝ) * (((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4))
  set N := (b : ℝ) ^ m
  have hrem' : unifAvg (fun ρ ↦ Var[scrambledEstimate prodFn d ρ; remLaw 2 (b ^ m)]) ≤
      4 * (N ^ 3)⁻¹ := by simpa using hrem
  have h4 : c ≤ N ^ 3 * (N⁻¹ ^ 2 * E) + 4 := by
    have := mul_le_mul_of_nonneg_left hrem' (pow_nonneg hN.le 3)
    rw [show N ^ 3 * (4 * (N ^ 3)⁻¹) = 4 by field_simp] at this
    nlinarith
  have h5 : N ^ 3 * (N⁻¹ ^ 2 * E) = N * E := by
    field_simp
  rw [h5] at h4
  rw [show (c - 4) * N⁻¹ = (c - 4) / N by ring, div_le_iff₀ hN]
  linarith

/-- `b^{-(m+1)} b^m = b^{-1}`. -/
theorem digWt_mul_pow (hb : 0 < b) (m : ℕ) : digWt b m * (b : ℝ) ^ m = (b : ℝ)⁻¹ := by
  have : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  unfold digWt
  rw [pow_succ]
  field_simp

/-- The integer square root tends to infinity. -/
theorem tendsto_sqrt_nat_atTop : Tendsto Nat.sqrt atTop atTop := by
  refine tendsto_atTop_atTop.2 fun N ↦ ⟨N * N, fun m hm ↦ ?_⟩
  exact Nat.le_sqrt.2 hm

/-- `⌊√m⌋ / m → 0`. -/
theorem tendsto_sqrt_nat_div : Tendsto (fun m : ℕ ↦ (Nat.sqrt m : ℝ) / m) atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ ↦ ((Nat.sqrt m : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp tendsto_sqrt_nat_atTop)
  refine squeeze_zero' (Eventually.of_forall fun m ↦ by positivity) ?_ h
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hs : 0 < Nat.sqrt m := Nat.sqrt_pos.2 hm
  have hsq : Nat.sqrt m * Nat.sqrt m ≤ m := Nat.sqrt_le m
  have hs' : (0 : ℝ) < Nat.sqrt m := Nat.cast_pos.2 hs
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hsq' : (Nat.sqrt m : ℝ) * Nat.sqrt m ≤ m := by exact_mod_cast hsq
  rw [div_le_iff₀ hm', inv_mul_eq_div, le_div_iff₀ hs']
  linarith

/-- **The CLT for the remainder-averaged error `S` of `x₀ x₁`**: for every sequence of
`(0,m,2)`-nets in base `b ≥ 2` and `τ_m → t`, the characteristic function of
`S/√(E S²)` (with `E S² = E_{ρ₀} V(ρ₀)`) at `τ_m` tends to `e^{-t²/2}`. -/
theorem tendsto_unifAvg_cexp_prodS (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) {τ : ℕ → ℝ} {t : ℝ}
    (hτ : Tendsto τ atTop (𝓝 t)) :
    Tendsto (fun m ↦ unifAvg (fun ρ : Fin 2 → Scramble b m ↦
      cexp ((((τ m * prodS (d m) ρ) /
        Real.sqrt (unifAvg (fun ρ₀ : Scramble b m ↦ condVar (d m) ρ₀)) : ℝ) : ℂ) * I)))
      atTop (𝓝 ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  set c₁ : ℝ := ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4) with hc₁
  have hc₁ : 0 < c₁ := by positivity
  set κ : ℝ := c₁ / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  set h : ℝ := (b : ℝ) / 2 with hh
  set s2 : ℕ → ℝ := fun m ↦ unifAvg (fun ρ₀ : Scramble b m ↦ condVar (d m) ρ₀) with hs2
  set N : ℕ → ℝ := fun m ↦ (b : ℝ) ^ m with hN
  have hN0 : ∀ m, 0 < N m := fun m ↦ pow_pos hbR m
  have hNnat : ∀ m, ((b ^ m : ℕ) : ℝ) = N m := fun m ↦ by rw [Nat.cast_pow]
  have hdw : ∀ m, digWt b m = (b : ℝ)⁻¹ * (N m)⁻¹ := fun m ↦ by
    change ((b : ℝ) ^ (m + 1))⁻¹ = (b : ℝ)⁻¹ * ((b : ℝ) ^ m)⁻¹
    rw [pow_succ, mul_inv, mul_comm]
  -- the lower bound on the mean conditional variance
  have hlow : ∀ᶠ m in atTop, κ * m * (N m)⁻¹ ≤ s2 m ∧ 1 ≤ m := by
    filter_upwards [eventually_ge_atTop (⌈8 / c₁⌉₊ + 1)] with m hm
    have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hm
    refine ⟨?_, hm1⟩
    have h := unifAvg_condVar_ge hb hm1 (hnet m)
    have hm8 : 8 / c₁ ≤ m := by
      have := Nat.le_ceil (8 / c₁)
      have : ((⌈8 / c₁⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
      push_cast at this
      linarith
    have hmc : 8 ≤ m * c₁ := by rwa [div_le_iff₀ hc₁] at hm8
    refine le_trans ?_ h
    rw [hκ]
    have : 0 ≤ (N m)⁻¹ := inv_nonneg.2 (hN0 m).le
    change c₁ / 2 * m * (N m)⁻¹ ≤ (m * c₁ - 4) * (N m)⁻¹
    nlinarith
  have hs2pos : ∀ᶠ m in atTop, 0 < s2 m := by
    filter_upwards [hlow] with m hm
    have : 0 < κ * m * (N m)⁻¹ := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
      have := inv_pos.2 (hN0 m)
      positivity
    linarith [hm.1]
  have hs2nn : ∀ m, 0 ≤ s2 m := fun m ↦ unifAvg_nonneg fun ρ₀ ↦
    Finset.sum_nonneg fun γ _ ↦ unifAvg_nonneg fun pm ↦ sq_nonneg _
  have hsq : ∀ m, Real.sqrt (s2 m) ^ 2 = s2 m := fun m ↦ Real.sq_sqrt (hs2nn m)
  -- the concentration of the conditional variance
  set J : ℕ → ℕ := Nat.sqrt with hJ
  set K1 : ℝ := 5 * h ^ 4 * (b : ℝ)⁻¹ / κ with hK1
  set K2 : ℝ := 32 * h ^ 8 * ((b : ℝ)⁻¹) ^ 2 / κ ^ 2 with hK2
  have hconc : ∀ᶠ m in atTop, unifAvg (fun ρ₀ : Scramble b m ↦
      |condVar (d m) ρ₀ / s2 m - 1|) ≤
      2 * (K1 * ((b : ℝ) ^ J m)⁻¹) + Real.sqrt (K2 * (J m / m)) := by
    filter_upwards [hlow, hs2pos] with m hm hspos
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
    have hmpos : (0 : ℝ) < m := by linarith
    set V : Scramble b m → ℝ := fun ρ₀ ↦ condVar (d m) ρ₀ with hV
    set W : Scramble b m → ℝ := fun ρ₀ ↦ condVarWin (d m) ρ₀ (J m) with hW
    have e1 : unifAvg (fun ρ₀ : Scramble b m ↦ |condVar (d m) ρ₀ / s2 m - 1|) =
        unifAvg (fun ρ₀ ↦ |V ρ₀ - unifAvg V|) / s2 m := by
      rw [div_eq_mul_inv, ← unifAvg_mul_const]
      congr 1
      funext ρ₀
      rw [hV]
      change _ = |condVar (d m) ρ₀ - s2 m| * (s2 m)⁻¹
      rw [← abs_of_pos (inv_pos.2 hspos), ← abs_mul, sub_mul, mul_inv_cancel₀ hspos.ne',
        div_eq_mul_inv]
    rw [e1]
    have hsplit := unifAvg_abs_sub_avg_le V W
    have hA := unifAvg_abs_condVar_sub_le hb (hnet m) (J m)
    have hB := unifAvg_sq_condVarWin_sub_le hb (hnet m) (J m)
    have hB' := (sq_unifAvg_abs_le (fun ρ₀ ↦ W ρ₀ - unifAvg W)).trans hB
    rw [hNnat, hdw] at hA hB'
    -- the first part
    have h1 : unifAvg (fun ρ₀ ↦ |V ρ₀ - W ρ₀|) / s2 m ≤ K1 * ((b : ℝ) ^ J m)⁻¹ := by
      rw [div_le_iff₀ hspos]
      refine hA.trans ?_
      have : K1 * ((b : ℝ) ^ J m)⁻¹ * (κ * m * (N m)⁻¹) ≤ K1 * ((b : ℝ) ^ J m)⁻¹ * s2 m :=
        mul_le_mul_of_nonneg_left hm.1 (by positivity)
      refine le_trans (le_of_eq ?_) this
      rw [hK1, hh]
      have : N m ≠ 0 := (hN0 m).ne'
      field_simp
    -- the second part
    have h2 : unifAvg (fun ρ₀ ↦ |W ρ₀ - unifAvg W|) / s2 m ≤ Real.sqrt (K2 * (J m / m)) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [div_pow, div_le_iff₀ (by positivity)]
      refine hB'.trans ?_
      have hs2sq : (κ * m * (N m)⁻¹) ^ 2 ≤ s2 m ^ 2 :=
        pow_le_pow_left₀ (by have := inv_pos.2 (hN0 m); positivity) hm.1 2
      have : K2 * (J m / m) * (κ * m * (N m)⁻¹) ^ 2 ≤ K2 * (J m / m) * s2 m ^ 2 :=
        mul_le_mul_of_nonneg_left hs2sq (by positivity)
      refine le_trans (le_of_eq ?_) this
      rw [hK2, hh]
      have : N m ≠ 0 := (hN0 m).ne'
      field_simp
      ring
    calc unifAvg (fun ρ₀ ↦ |V ρ₀ - unifAvg V|) / s2 m
        ≤ (2 * unifAvg (fun ρ₀ ↦ |V ρ₀ - W ρ₀|) + unifAvg (fun ρ₀ ↦ |W ρ₀ - unifAvg W|)) /
          s2 m := div_le_div_of_nonneg_right hsplit hspos.le
      _ = 2 * (unifAvg (fun ρ₀ ↦ |V ρ₀ - W ρ₀|) / s2 m) +
          unifAvg (fun ρ₀ ↦ |W ρ₀ - unifAvg W|) / s2 m := by ring
      _ ≤ 2 * (K1 * ((b : ℝ) ^ J m)⁻¹) + Real.sqrt (K2 * (J m / m)) := by linarith
  have hV : Tendsto (fun m ↦ unifAvg fun ρ₀ : Scramble b m ↦
      |(∑ γ, unifAvg fun pm ↦ nodeTerm (d m) ρ₀ γ pm ^ 2) /
        Real.sqrt (s2 m) ^ 2 - 1|) atTop (𝓝 0) := by
    have hlim : Tendsto (fun m ↦ 2 * (K1 * ((b : ℝ) ^ J m)⁻¹) + Real.sqrt (K2 * (J m / m)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun m ↦ ((b : ℝ) ^ J m)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop_atTop_of_one_lt
          (Nat.one_lt_cast.2 hb)).comp tendsto_sqrt_nat_atTop)
      have h2 : Tendsto (fun m ↦ Real.sqrt (K2 * (J m / m))) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto _).comp (tendsto_sqrt_nat_div.const_mul K2)
        rwa [mul_zero, Real.sqrt_zero] at this
      simpa only [mul_zero, zero_add] using (h1.const_mul K1).const_mul 2 |>.add h2
    refine squeeze_zero' (Eventually.of_forall fun m ↦ unifAvg_nonneg fun ρ₀ ↦ abs_nonneg _)
      ?_ hlim
    filter_upwards [hconc] with m hm
    rw [hsq]
    exact hm
  -- the moments of the node bounds
  have hM2 : ∀ᶠ m in atTop, (unifAvg fun ρ₀ : Scramble b m ↦
      ∑ γ, (nodeBound (d m) ρ₀ γ / Real.sqrt (s2 m)) ^ 2) ≤ 2 * h ^ 4 * (b : ℝ)⁻¹ / κ := by
    filter_upwards [hlow, hs2pos] with m hm hspos
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
    have e : (fun ρ₀ : Scramble b m ↦ ∑ γ, (nodeBound (d m) ρ₀ γ / Real.sqrt (s2 m)) ^ 2) =
        fun ρ₀ ↦ (∑ γ, nodeBound (d m) ρ₀ γ ^ 2) * (s2 m)⁻¹ := by
      funext ρ₀
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun γ _ ↦ by rw [div_pow, hsq, div_eq_mul_inv]
    rw [e, unifAvg_mul_const, ← div_eq_mul_inv, div_le_iff₀ hspos]
    have hA := unifAvg_sum_sq_nodeBound_le hb (hnet m)
    rw [hNnat, hdw] at hA
    refine hA.trans ?_
    have : 2 * h ^ 4 * (b : ℝ)⁻¹ / κ * (κ * m * (N m)⁻¹) ≤
        2 * h ^ 4 * (b : ℝ)⁻¹ / κ * s2 m := mul_le_mul_of_nonneg_left hm.1 (by positivity)
    refine le_trans (le_of_eq ?_) this
    rw [hh]
    have : N m ≠ 0 := (hN0 m).ne'
    field_simp
  have hM4 : Tendsto (fun m ↦ unifAvg fun ρ₀ : Scramble b m ↦
      ∑ γ, (nodeBound (d m) ρ₀ γ / Real.sqrt (s2 m)) ^ 4) atTop (𝓝 0) := by
    have hlim : Tendsto (fun m : ℕ ↦ 12 * h ^ 8 * (b : ℝ)⁻¹ / κ ^ 2 * (m : ℝ)⁻¹) atTop
        (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
        (12 * h ^ 8 * (b : ℝ)⁻¹ / κ ^ 2)
      rw [mul_zero] at this
      exact this
    refine squeeze_zero' (Eventually.of_forall fun m ↦ unifAvg_nonneg fun ρ₀ ↦
      Finset.sum_nonneg fun γ _ ↦ by positivity) ?_ hlim
    filter_upwards [hlow, hs2pos] with m hm hspos
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
    have e : (fun ρ₀ : Scramble b m ↦ ∑ γ, (nodeBound (d m) ρ₀ γ / Real.sqrt (s2 m)) ^ 4) =
        fun ρ₀ ↦ (∑ γ, nodeBound (d m) ρ₀ γ ^ 4) * ((s2 m) ^ 2)⁻¹ := by
      funext ρ₀
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun γ _ ↦ ?_
      rw [div_pow, show Real.sqrt (s2 m) ^ 4 = (Real.sqrt (s2 m) ^ 2) ^ 2 by ring, hsq,
        div_eq_mul_inv]
    rw [e, unifAvg_mul_const, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have hA := unifAvg_sum_pow_four_nodeBound_le hb (hnet m)
    rw [hNnat, hdw] at hA
    refine hA.trans ?_
    have hs2sq : (κ * m * (N m)⁻¹) ^ 2 ≤ s2 m ^ 2 :=
      pow_le_pow_left₀ (by have := inv_pos.2 (hN0 m); positivity) hm.1 2
    have : 12 * h ^ 8 * (b : ℝ)⁻¹ / κ ^ 2 * (m : ℝ)⁻¹ * (κ * m * (N m)⁻¹) ^ 2 ≤
        12 * h ^ 8 * (b : ℝ)⁻¹ / κ ^ 2 * (m : ℝ)⁻¹ * s2 m ^ 2 :=
      mul_le_mul_of_nonneg_left hs2sq (by positivity)
    refine le_trans (le_of_eq ?_) this
    rw [hh]
    have : N m ≠ 0 := (hN0 m).ne'
    have : (m : ℝ) ≠ 0 := by positivity
    field_simp
  have hsp : ∀ᶠ m in atTop, 0 < Real.sqrt (s2 m) := by
    filter_upwards [hs2pos] with m hm
    exact Real.sqrt_pos.2 hm
  have hmain := tendsto_unifAvg_cexp_nodeSum (R := fun m ↦ Scramble b m)
    (Γ := fun m ↦ Fin m × (Fin m → Option (Fin b))) (P := Equiv.Perm (Fin b))
    (fun m ↦ nodeTerm (d m)) (fun m ρ₀ γ ↦ unifAvg_nodeTerm (d m) ρ₀ γ) hsp hV
    (M := fun m ↦ nodeBound (d m)) (fun m ρ₀ γ pm ↦ abs_nodeTerm_le hb0 (d m) ρ₀ γ pm) hM2 hM4 hτ
  refine hmain.congr fun m ↦ ?_
  rw [unifAvg_fin_two]
  congr 1
  funext ρ₀
  congr 1
  funext ρ₁
  rw [prodS_eq_sum_nodeTerm]
  rfl

/-- **The lower bound on `E S²`, eventually**: `E_{ρ₀} V(ρ₀) ≥ κ m / n` with
`κ = (b-1)⁴/(128 b⁴)` for all large `m`. -/
theorem eventually_unifAvg_condVar_ge (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) :
    ∀ᶠ m in atTop, ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4) / 2 * m * ((b : ℝ) ^ m)⁻¹ ≤
      unifAvg (fun ρ₀ : Scramble b m ↦ condVar (d m) ρ₀) ∧ 1 ≤ m := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  set c₁ : ℝ := ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4) with hc₁
  have hc₁ : 0 < c₁ := by positivity
  filter_upwards [eventually_ge_atTop (⌈8 / c₁⌉₊ + 1)] with m hm
  have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hm
  refine ⟨?_, hm1⟩
  have h := unifAvg_condVar_ge hb hm1 (hnet m)
  have hm8 : 8 / c₁ ≤ m := by
    have := Nat.le_ceil (8 / c₁)
    have : ((⌈8 / c₁⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at this
    linarith
  have hmc : 8 ≤ m * c₁ := by rwa [div_le_iff₀ hc₁] at hm8
  refine le_trans ?_ h
  have : 0 ≤ ((b : ℝ) ^ m)⁻¹ := inv_nonneg.2 (pow_pos hbR m).le
  nlinarith

/-- **Integrals against a mixture law, complex-valued**:
`∫ g d(mixLaw Q Φ) = E_ρ ∫ g(Φ ρ u) dQ(u)`. -/
theorem integral_mixLaw_complex {R E : Type*} [Fintype R] [MeasurableSpace E] {Q : Measure E}
    {Φ : R → E → ℝ} (hΦ : ∀ ρ, Measurable (Φ ρ)) {g : ℝ → ℂ} (hg : Continuous g)
    (hint : ∀ ρ, Integrable (fun u ↦ g (Φ ρ u)) Q) :
    ∫ x, g x ∂(mixLaw Q Φ) = unifAvg (fun ρ ↦ ∫ u, g (Φ ρ u) ∂Q) := by
  have hgi : ∀ ρ, Integrable g (Q.map (Φ ρ)) := fun ρ ↦
    (integrable_map_measure hg.aestronglyMeasurable (hΦ ρ).aemeasurable).2 (hint ρ)
  unfold mixLaw unifAvg
  rw [integral_smul_measure, integral_finsetSum_measure fun ρ _ ↦ hgi ρ, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Complex.real_smul]
  push_cast
  congr 1
  exact Finset.sum_congr rfl fun ρ _ ↦ integral_map (hΦ ρ).aemeasurable hg.aestronglyMeasurable

/-- `‖e^{ix} - e^{iy}‖ ≤ |x - y|`. -/
theorem norm_cexp_sub_cexp_le (x y : ℝ) :
    ‖cexp ((x : ℂ) * I) - cexp ((y : ℂ) * I)‖ ≤ |x - y| := by
  have e : cexp ((x : ℂ) * I) - cexp ((y : ℂ) * I) =
      cexp ((y : ℂ) * I) * (cexp (I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)
  rwa [Real.norm_eq_abs] at this

/-- **Jensen for the absolute deviation**: `(E|X - E X|)² ≤ Var X`. -/
theorem sq_integral_abs_sub_le_variance {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : Ω → ℝ} (hX : MemLp X 2 Q) :
    (∫ ω, |X ω - ∫ ω', X ω' ∂Q| ∂Q) ^ 2 ≤ Var[X; Q] := by
  have hY : MemLp (fun ω ↦ |X ω - ∫ ω', X ω' ∂Q|) 2 Q := (hX.sub (memLp_const _)).abs
  have hv := variance_nonneg (fun ω ↦ |X ω - ∫ ω', X ω' ∂Q|) Q
  rw [variance_eq_sub hY] at hv
  rw [variance_eq_integral hX.aestronglyMeasurable.aemeasurable]
  have e : ∫ ω, ((fun ω ↦ |X ω - ∫ ω', X ω' ∂Q|) ^ 2) ω ∂Q =
      ∫ ω, (X ω - ∫ ω', X ω' ∂Q) ^ 2 ∂Q :=
    integral_congr_ae (Eventually.of_forall fun ω ↦ by simp only [Pi.pow_apply, sq_abs])
  change 0 ≤ ∫ ω, ((fun ω ↦ |X ω - ∫ ω', X ω' ∂Q|) ^ 2) ω ∂Q -
    (∫ ω, |X ω - ∫ ω', X ω' ∂Q| ∂Q) ^ 2 at hv
  rw [e] at hv
  linarith

/-- **Loh's CLT from the conditional-mean structure** (post #2, Loh 2003, `s = 2`): for every
sequence of `(0,m,2)`-nets in base `b ≥ 2` and every measurable `f ∈ L²`, Lipschitz on the
cube, whose remainder-averaged scrambled estimator is `E[μ̂ | ρ] = μ + a S(ρ)/n` with `a ≠ 0`
and `S` the error sum of `x₀ x₁`, the estimator standardised by its own standard deviation is
asymptotically normal: `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)`. -/
theorem tendstoInDistribution_scrambledLaw_of_condMean (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) {L : ℝ}
    (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|) {a : ℝ} (ha : a ≠ 0)
    (hmean : ∀ m ρ, ∫ u, scrambledEstimate f (d m) ρ u ∂(remLaw 2 (b ^ m)) =
      ∫ x, f x ∂(uniformCube 2) + a * (prodS (d m) ρ / ((b ^ m : ℕ) : ℝ)))
    [∀ m, IsProbabilityMeasure (scrambledLaw f (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, f y ∂(uniformCube 2)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw f (d m)]) atTop Z
      (fun m ↦ scrambledLaw f (d m)) P' where
  forall_aemeasurable m := ((measurable_id.sub_const _).div_const _).aemeasurable
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
    have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb0
    have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
      have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
      linarith
    have hQ : ∀ m, IsProbabilityMeasure (remLaw 2 (b ^ m)) := fun m ↦
      isProbabilityMeasure_remLaw 2 _
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    change Tendsto (fun m ↦ charFun ((scrambledLaw f (d m)).map fun x ↦
      (x - ∫ y, f y ∂(uniformCube 2)) / Real.sqrt Var[fun x ↦ x; scrambledLaw f (d m)]) t)
      atTop (𝓝 (charFun (P'.map Z) t))
    have htarget : charFun (P'.map Z) t = ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [hZ.map_eq, charFun_gaussianReal, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [htarget]
    -- notation
    set μ := ∫ y, f y ∂(uniformCube 2) with hμ
    set N : ℕ → ℝ := fun m ↦ ((b ^ m : ℕ) : ℝ) with hN
    set s2 : ℕ → ℝ := fun m ↦ unifAvg (fun ρ₀ : Scramble b m ↦ condVar (d m) ρ₀) with hs2
    set v : ℕ → ℝ := fun m ↦ unifAvg (fun ρ : Fin 2 → Scramble b m ↦
      Var[scrambledEstimate f (d m) ρ; remLaw 2 (b ^ m)]) with hv
    set A : ℕ → ℝ := fun m ↦ a ^ 2 * (N m)⁻¹ ^ 2 * s2 m with hA
    set σ : ℕ → ℝ := fun m ↦ Real.sqrt Var[fun x ↦ x; scrambledLaw f (d m)] with hσ
    have hN0 : ∀ m, 0 < N m := fun m ↦ Nat.cast_pos.2 (Nat.pow_pos hb0)
    have hNb : ∀ m, N m = (b : ℝ) ^ m := fun m ↦ by rw [hN]; push_cast; rfl
    have hvar : ∀ m, Var[fun x ↦ x; scrambledLaw f (d m)] = A m + v m := by
      intro m
      rw [variance_scrambledLaw_eq_of_condMean hb0 hfm hf (hmean m)]
      congr 1
      change _ = a ^ 2 * (N m)⁻¹ ^ 2 * unifAvg (fun ρ₀ : Scramble b m ↦ condVar (d m) ρ₀)
      rw [← unifAvg_sq_prodS_eq, ← unifAvg_const_mul]
      congr 1
      funext ρ
      rw [div_eq_mul_inv]
      ring
    have hv0 : ∀ m, 0 ≤ v m := fun m ↦ unifAvg_nonneg fun ρ ↦ variance_nonneg _ _
    have hvle : ∀ m, v m ≤ 4 * L ^ 2 * ((N m) ^ 3)⁻¹ := fun m ↦ by
      rw [hNb]
      exact unifAvg_variance_le hb0 hf hL0 hL
    set κ : ℝ := ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4) / 2 with hκ
    have hκ0 : 0 < κ := by positivity
    have hlow : ∀ᶠ m in atTop, κ * m * (N m)⁻¹ ≤ s2 m ∧ 1 ≤ m := by
      filter_upwards [eventually_unifAvg_condVar_ge hb d hnet] with m hm
      rw [hNb]
      exact hm
    have hApos : ∀ᶠ m in atTop, a ^ 2 * κ * m * ((N m) ^ 3)⁻¹ ≤ A m ∧ 0 < A m ∧ 1 ≤ m := by
      filter_upwards [hlow] with m hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
      have ha2 : 0 < a ^ 2 := by positivity
      have hle : a ^ 2 * κ * m * ((N m) ^ 3)⁻¹ ≤ A m := by
        have := mul_le_mul_of_nonneg_left hm.1 (by positivity : 0 ≤ a ^ 2 * (N m)⁻¹ ^ 2)
        refine le_trans (le_of_eq ?_) this
        have : N m ≠ 0 := (hN0 m).ne'
        field_simp
      refine ⟨hle, lt_of_lt_of_le ?_ hle, hm.2⟩
      have := hN0 m
      positivity
    -- the remainders' share
    have hratio : Tendsto (fun m ↦ v m / A m) atTop (𝓝 0) := by
      have hlim : Tendsto (fun m : ℕ ↦ 4 * L ^ 2 / (a ^ 2 * κ) * (m : ℝ)⁻¹) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
          (4 * L ^ 2 / (a ^ 2 * κ))
        rw [mul_zero] at this
        exact this
      refine squeeze_zero' ?_ ?_ hlim
      · filter_upwards [hApos] with m hm
        exact div_nonneg (hv0 m) hm.2.1.le
      · filter_upwards [hApos] with m hm
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.2.2
        rw [div_le_iff₀ hm.2.1]
        refine (hvle m).trans ?_
        have := mul_le_mul_of_nonneg_left hm.1
          (by positivity : 0 ≤ 4 * L ^ 2 / (a ^ 2 * κ) * (m : ℝ)⁻¹)
        refine le_trans (le_of_eq ?_) this
        have : N m ≠ 0 := (hN0 m).ne'
        have : (m : ℝ) ≠ 0 := by positivity
        field_simp
    have hσpos : ∀ᶠ m in atTop, 0 < σ m := by
      filter_upwards [hApos] with m hm
      exact Real.sqrt_pos.2 (by rw [hvar]; linarith [hv0 m, hm.2.1])
    have hs2pos : ∀ᶠ m in atTop, 0 < s2 m := by
      filter_upwards [hlow] with m hm
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
      have := inv_pos.2 (hN0 m)
      have : 0 < κ * m * (N m)⁻¹ := by positivity
      linarith [hm.1]
    -- the scale factor
    set ε : ℕ → ℝ := fun m ↦ a * Real.sqrt (s2 m) / (N m * σ m) with hε
    have hεeq : ∀ᶠ m in atTop, ε m = a / |a| * Real.sqrt ((1 + v m / A m)⁻¹) := by
      filter_upwards [hApos, hs2pos] with m hm hs
      have hA0 := hm.2.1
      have hsqA : Real.sqrt (A m) = |a| * (N m)⁻¹ * Real.sqrt (s2 m) := by
        rw [hA, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
          Real.sqrt_sq (inv_nonneg.2 (hN0 m).le)]
      have e1 : (1 + v m / A m)⁻¹ = A m / (A m + v m) := by
        field_simp
      rw [e1, Real.sqrt_div' _ (by linarith [hv0 m]), hsqA, hε]
      change a * Real.sqrt (s2 m) / (N m * Real.sqrt Var[fun x ↦ x; scrambledLaw f (d m)]) = _
      rw [hvar]
      have : |a| ≠ 0 := abs_ne_zero.2 ha
      have : N m ≠ 0 := (hN0 m).ne'
      field_simp
    have hεlim : Tendsto ε atTop (𝓝 (a / |a|)) := by
      have h1 : Tendsto (fun m ↦ a / |a| * Real.sqrt ((1 + v m / A m)⁻¹)) atTop
          (𝓝 (a / |a| * Real.sqrt ((1 + 0)⁻¹))) :=
        ((Real.continuous_sqrt.tendsto _).comp
          ((tendsto_const_nhds.add hratio).inv₀ (by norm_num))).const_mul _
      rw [add_zero, inv_one, Real.sqrt_one, mul_one] at h1
      exact h1.congr' (hεeq.mono fun m hm ↦ hm.symm)
    -- the remainder term
    set X : ℕ → ℝ := fun m ↦ unifAvg (fun ρ : Fin 2 → Scramble b m ↦
      ∫ u, |scrambledEstimate f (d m) ρ u -
        ∫ u', scrambledEstimate f (d m) ρ u' ∂(remLaw 2 (b ^ m))| ∂(remLaw 2 (b ^ m))) / σ m
      with hX
    have hXlim : Tendsto X atTop (𝓝 0) := by
      have hsq : Tendsto (fun m ↦ Real.sqrt (v m / A m)) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto _).comp hratio
        rwa [Real.sqrt_zero] at this
      refine squeeze_zero' ?_ ?_ hsq
      · filter_upwards [hσpos] with m hm
        exact div_nonneg (unifAvg_nonneg fun ρ ↦ integral_nonneg fun u ↦ abs_nonneg _) hm.le
      · filter_upwards [hσpos, hApos] with m hσm hm
        refine Real.le_sqrt_of_sq_le ?_
        have h1 : (unifAvg (fun ρ : Fin 2 → Scramble b m ↦ ∫ u, |scrambledEstimate f (d m) ρ u -
            ∫ u', scrambledEstimate f (d m) ρ u' ∂(remLaw 2 (b ^ m))| ∂(remLaw 2 (b ^ m)))) ^ 2 ≤
            v m := (sq_unifAvg_le _).trans (unifAvg_mono fun ρ ↦
              sq_integral_abs_sub_le_variance (memLp_scrambledEstimate hb0 hf (d m) ρ))
        have hσ2 : σ m ^ 2 = A m + v m := by
          rw [hσ]
          simp only
          rw [Real.sq_sqrt (by rw [hvar]; linarith [hv0 m, hm.2.1]), hvar]
        rw [hX]
        simp only
        rw [div_pow, hσ2, div_le_div_iff₀ (by linarith [hv0 m, hm.2.1]) hm.2.1]
        have := hv0 m
        nlinarith [hm.2.1]
    -- the CLT for `S`
    have hS := tendsto_unifAvg_cexp_prodS hb d hnet (hεlim.const_mul t)
    have hsign : (t * (a / |a|)) ^ 2 = t ^ 2 := by
      rw [mul_pow, div_pow, sq_abs, div_self (by positivity), mul_one]
    rw [hsign] at hS
    -- the comparison
    have hcomp : ∀ᶠ m in atTop, ‖charFun ((scrambledLaw f (d m)).map fun x ↦
        (x - μ) / σ m) t - unifAvg (fun ρ : Fin 2 → Scramble b m ↦
          cexp ((((t * ε m * prodS (d m) ρ) / Real.sqrt (s2 m) : ℝ) : ℂ) * I))‖ ≤
        |t| * X m := by
      filter_upwards [hσpos, hs2pos] with m hσm hs
      have hYm : Measurable fun x : ℝ ↦ (x - μ) / σ m := (measurable_id.sub_const _).div_const _
      have hg : Continuous fun x : ℝ ↦ cexp (((t * ((x - μ) / σ m) : ℝ) : ℂ) * I) :=
        Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
          (continuous_const.mul ((continuous_id.sub continuous_const).div_const _))).mul
          continuous_const)
      have hint : ∀ ρ, Integrable (fun u ↦ cexp (((t * ((scrambledEstimate f (d m) ρ u - μ) /
          σ m) : ℝ) : ℂ) * I)) (remLaw 2 (b ^ m)) := fun ρ ↦ by
        refine Integrable.of_bound (hg.comp_aestronglyMeasurable
          (measurable_scrambledEstimate hfm (d m) ρ).aestronglyMeasurable) 1
          (Eventually.of_forall fun u ↦ ?_)
        rw [Complex.norm_exp_ofReal_mul_I]
      have hcf : charFun ((scrambledLaw f (d m)).map fun x ↦ (x - μ) / σ m) t =
          unifAvg (fun ρ : Fin 2 → Scramble b m ↦ ∫ u, cexp (((t * ((scrambledEstimate f (d m)
            ρ u - μ) / σ m) : ℝ) : ℂ) * I) ∂(remLaw 2 (b ^ m))) := by
        have hcont : Continuous fun y : ℝ ↦ cexp ((t : ℂ) * (y : ℂ) * I) := by fun_prop
        rw [charFun_apply_real, integral_map hYm.aemeasurable hcont.aestronglyMeasurable]
        unfold scrambledLaw
        rw [← integral_mixLaw_complex (measurable_scrambledEstimate hfm (d m)) hg hint]
        congr 1
        funext x
        push_cast
        ring_nf
      rw [hcf, ← unifAvg_sub_complex]
      refine (norm_unifAvg_le _).trans ?_
      rw [hX, show |t| * (unifAvg (fun ρ : Fin 2 → Scramble b m ↦ ∫ u,
          |scrambledEstimate f (d m) ρ u - ∫ u', scrambledEstimate f (d m) ρ u'
            ∂(remLaw 2 (b ^ m))| ∂(remLaw 2 (b ^ m))) / σ m) =
          unifAvg (fun ρ : Fin 2 → Scramble b m ↦ |t| / σ m * ∫ u,
          |scrambledEstimate f (d m) ρ u - ∫ u', scrambledEstimate f (d m) ρ u'
            ∂(remLaw 2 (b ^ m))| ∂(remLaw 2 (b ^ m))) by
        rw [unifAvg_const_mul]
        ring]
      refine unifAvg_mono fun ρ ↦ ?_
      set c : ℂ := cexp ((((t * ε m * prodS (d m) ρ) / Real.sqrt (s2 m) : ℝ) : ℂ) * I) with hc
      have hL1 : Integrable (fun u ↦ |scrambledEstimate f (d m) ρ u -
          ∫ u', scrambledEstimate f (d m) ρ u' ∂(remLaw 2 (b ^ m))|) (remLaw 2 (b ^ m)) :=
        (((memLp_scrambledEstimate hb0 hf (d m) ρ).integrable one_le_two).sub
          (integrable_const _)).abs
      rw [← integral_const_mul, show c = ∫ _u, c ∂(remLaw 2 (b ^ m)) by
        rw [integral_const, probReal_univ, one_smul], ← integral_sub (hint ρ)
        (integrable_const _)]
      refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
        (Eventually.of_forall fun u ↦ norm_nonneg _) (hL1.const_mul _)
        (Eventually.of_forall fun u ↦ ?_))
      refine (norm_cexp_sub_cexp_le _ _).trans (le_of_eq ?_)
      have hrel : t * ((scrambledEstimate f (d m) ρ u - μ) / σ m) -
          t * ε m * prodS (d m) ρ / Real.sqrt (s2 m) =
          t / σ m * (scrambledEstimate f (d m) ρ u -
            ∫ u', scrambledEstimate f (d m) ρ u' ∂(remLaw 2 (b ^ m))) := by
        rw [hmean m ρ, hε]
        have : Real.sqrt (s2 m) ≠ 0 := (Real.sqrt_pos.2 hs).ne'
        have : N m ≠ 0 := (hN0 m).ne'
        have : σ m ≠ 0 := hσm.ne'
        simp only
        field_simp
        ring
      rw [hrel, abs_mul, abs_div, abs_of_pos hσm]
    -- conclusion
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hS
    refine squeeze_zero' (Eventually.of_forall fun m ↦ norm_nonneg _) ?_
      (by simpa only [mul_zero, zero_add] using (hXlim.const_mul |t|).add hS)
    filter_upwards [hcomp] with m hm
    refine (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hm (le_of_eq ?_))
    congr 3

/-- **Loh's CLT for `x₀ x₁`** (post #2, Loh 2003): for every sequence of `(0,m,2)`-nets in base
`b ≥ 2`, `(μ̂ - 1/4)/√Var(μ̂) ⇒ N(0,1)` for the scrambled-net estimator of `∫ x₀ x₁`. -/
theorem tendstoInDistribution_scrambledLaw_prodFn (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    [∀ m, IsProbabilityMeasure (scrambledLaw prodFn (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, prodFn y ∂(uniformCube 2)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw prodFn (d m)]) atTop Z
      (fun m ↦ scrambledLaw prodFn (d m)) P' := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  exact tendstoInDistribution_scrambledLaw_of_condMean hb d hnet measurable_prodFn memLp_prodFn
    zero_le_one (fun x x' hx hx' ↦ abs_prodFn_sub_le hx hx') one_ne_zero (fun m ρ ↦ by
      rw [integral_scrambledEstimate_prodFn hb0 (hnet m) ρ, integral_prodFn, one_mul]) hZ

/-- **Loh's CLT for `x₀ x₁` on the scrambled Hammersley nets** `{(i/bᵐ, φ_b(i))}`, any base
`b ≥ 2`. -/
theorem tendstoInDistribution_scrambledLaw_prodFn_hammersley (hb : 1 < b)
    [∀ m, IsProbabilityMeasure
      (scrambledLaw prodFn (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, prodFn y ∂(uniformCube 2)) /
      Real.sqrt Var[fun x ↦ x;
        scrambledLaw prodFn (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)]) atTop Z
      (fun m ↦ scrambledLaw prodFn (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)) P' :=
  tendstoInDistribution_scrambledLaw_prodFn hb _ (isNet_hammersley hb) hZ

/-- The scrambled-net estimator is linear in the integrand. -/
theorem scrambledEstimate_bilinAdd {m n : ℕ} (a : ℝ) (g : Fin 2 → ℝ → ℝ)
    (d : Fin n → Fin 2 → Fin m → Fin b) (ρ : Fin 2 → Scramble b m) (u : Fin n → Fin 2 → ℝ) :
    scrambledEstimate (fun x ↦ a * prodFn x + addFn g x) d ρ u =
      a * scrambledEstimate prodFn d ρ u + scrambledEstimate (addFn g) d ρ u := by
  unfold scrambledEstimate sampleMean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **The additive part is integrated exactly given the scramble**:
`E[μ̂(Σ_j g_j) | ρ] = Σ_j ∫ g_j` for every `(0,m,s)`-net and every scramble. -/
theorem integral_scrambledEstimate_addFn (hb : 0 < b) {m s : ℕ}
    {d : Fin (b ^ m) → Fin s → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j))
    (hgc : ∀ j, ContinuousOn (g j) (Set.Icc 0 1)) (ρ : Fin s → Scramble b m) :
    ∫ u, scrambledEstimate (addFn g) d ρ u ∂(remLaw s (b ^ m)) = ∑ j, ∫ x, g j x ∂uniformIco := by
  have hQ := isProbabilityMeasure_remLaw s (b ^ m)
  have hU := isProbabilityMeasure_uniformCube s
  have e : ∀ u, scrambledEstimate (addFn g) d ρ u =
      ∑ i, addTerm g d ρ i (u i) + ∑ j, ∫ x, g j x ∂uniformIco := fun u ↦ by
    rw [sum_addTerm hb hnet hgc ρ u]
    ring
  have hint : ∀ i, Integrable (fun u : Fin (b ^ m) → Fin s → ℝ ↦ addTerm g d ρ i (u i))
      (remLaw s (b ^ m)) := fun i ↦
    (memLp_remLaw_eval (memLp_addTerm hgm hgc hb ρ i) i).integrable one_le_two
  rw [integral_congr_ae (Eventually.of_forall e), integral_add (integrable_finsetSum _
    fun i _ ↦ hint i) (integrable_const _), integral_finsetSum _ fun i _ ↦ hint i,
    integral_const, probReal_univ, one_smul]
  rw [Finset.sum_eq_zero fun i _ ↦ by
    rw [integral_remLaw_eval (g := addTerm g d ρ i)
      (measurable_addTerm hgm d ρ i).aestronglyMeasurable i, integral_addTerm hgm hgc hb ρ i],
    zero_add]

/-- **Loh's CLT for the smooth integrands with a constant non-zero mixed derivative**
(post #2, Loh 2003, `s = 2`): for `f(x) = a x₀ x₁ + g₀(x₀) + g₁(x₁)` with `a ≠ 0` and each
`g_j` measurable and `C¹` on `[0,1]` (so `∂²f/∂x₀∂x₁ ≡ a`), and every sequence of
`(0,m,2)`-nets in base `b ≥ 2` scrambled by independent uniform nested scrambles with
independent uniform remainders, `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)` as `n = bᵐ → ∞`. -/
theorem tendstoInDistribution_scrambledLaw_bilinAdd (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) {a : ℝ} (ha : a ≠ 0)
    {g g' : Fin 2 → ℝ → ℝ} (hgm : ∀ j, Measurable (g j))
    (hg : ∀ j, ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (g j) (g' j x) (Set.Icc 0 1) x)
    (hg' : ∀ j, ContinuousOn (g' j) (Set.Icc 0 1))
    [∀ m, IsProbabilityMeasure (scrambledLaw (fun x ↦ a * prodFn x + addFn g x) (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, (a * prodFn y + addFn g y) ∂(uniformCube 2)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw (fun x ↦ a * prodFn x + addFn g x) (d m)]) atTop Z
      (fun m ↦ scrambledLaw (fun x ↦ a * prodFn x + addFn g x) (d m)) P' := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hU := isProbabilityMeasure_uniformCube 2
  have hgc : ∀ j, ContinuousOn (g j) (Set.Icc 0 1) := fun j x hx ↦ (hg j x hx).continuousWithinAt
  choose K hK using fun j ↦ exists_lipschitz_of_C1 (hg j) (hg' j)
  have hfm : Measurable fun x ↦ a * prodFn x + addFn g x :=
    (measurable_prodFn.const_mul a).add (measurable_addFn hgm)
  have hf : MemLp (fun x ↦ a * prodFn x + addFn g x) 2 (uniformCube 2) :=
    (memLp_prodFn.const_mul a).add (memLp_addFn hgm hgc 2)
  set L : ℝ := |a| + ∑ j, max (K j) 0 with hL
  have hL0 : 0 ≤ L := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ ↦ le_max_right _ _)
  have hLip : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |(a * prodFn x + addFn g x) - (a * prodFn x' + addFn g x')| ≤ L * ∑ j, |x j - x' j| := by
    intro x x' hx hx'
    have h1 : |a * prodFn x - a * prodFn x'| ≤ |a| * ∑ j, |x j - x' j| := by
      rw [← mul_sub, abs_mul]
      have := abs_prodFn_sub_le hx hx'
      rw [one_mul] at this
      exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
    have h2 : |addFn g x - addFn g x'| ≤ (∑ j, max (K j) 0) * ∑ j, |x j - x' j| := by
      unfold addFn
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ ↦ ?_
      have hj := hK j (x j) (Set.Ico_subset_Icc_self (hx j)) (x' j)
        (Set.Ico_subset_Icc_self (hx' j))
      have hle : |x j - x' j| ≤ ∑ k, |x k - x' k| :=
        Finset.single_le_sum (f := fun k ↦ |x k - x' k|) (fun k _ ↦ abs_nonneg _)
          (Finset.mem_univ j)
      calc |g j (x j) - g j (x' j)| ≤ K j * |x j - x' j| := hj
        _ ≤ max (K j) 0 * |x j - x' j| :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
        _ ≤ max (K j) 0 * ∑ k, |x k - x' k| :=
            mul_le_mul_of_nonneg_left hle (le_max_right _ _)
    calc |(a * prodFn x + addFn g x) - (a * prodFn x' + addFn g x')|
        = |(a * prodFn x - a * prodFn x') + (addFn g x - addFn g x')| := by ring_nf
      _ ≤ |a * prodFn x - a * prodFn x'| + |addFn g x - addFn g x'| := abs_add_le _ _
      _ ≤ |a| * ∑ j, |x j - x' j| + (∑ j, max (K j) 0) * ∑ j, |x j - x' j| := add_le_add h1 h2
      _ = L * ∑ j, |x j - x' j| := by rw [hL]; ring
  have hmeanf : ∫ y, (a * prodFn y + addFn g y) ∂(uniformCube 2) =
      a * (1 / 4) + ∑ j, ∫ x, g j x ∂uniformIco := by
    rw [integral_add ((memLp_prodFn.integrable one_le_two).const_mul a)
      ((memLp_addFn hgm hgc 2).integrable one_le_two), integral_const_mul, integral_prodFn,
      integral_addFn hgm hgc]
  refine tendstoInDistribution_scrambledLaw_of_condMean hb d hnet hfm hf hL0 hLip ha
    (fun m ρ ↦ ?_) hZ
  have hQ := isProbabilityMeasure_remLaw 2 (b ^ m)
  rw [integral_congr_ae (Eventually.of_forall fun u ↦ scrambledEstimate_bilinAdd a g (d m) ρ u),
    integral_add (((memLp_scrambledEstimate hb0 memLp_prodFn (d m) ρ).integrable
      one_le_two).const_mul a) ((memLp_scrambledEstimate hb0 (memLp_addFn hgm hgc 2) (d m)
        ρ).integrable one_le_two), integral_const_mul,
    integral_scrambledEstimate_prodFn hb0 (hnet m) ρ,
    integral_scrambledEstimate_addFn hb0 (hnet m) hgm hgc ρ, hmeanf]
  ring

end RQMCMarkov.OwenScrambling
