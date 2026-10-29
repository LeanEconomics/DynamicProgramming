/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.ContinuousTimeResolvent
import Epilogue.UniformErgodic

/-!
# Ergodic theory in continuous time (MT §20.3.1, §20.3.3, Theorem 20.3.2)

Meyn and Tweedie, pp. 525–528, for the `MarkovSemigroup`s of `ContinuousTimeResolvent`.

* `MarkovSemigroup.tvNorm_antitone` (p. 526): for `π` invariant for every `Pᵗ`,
  `t ↦ ‖Pᵗ(x, ·) − π‖` is non-increasing.
* `MarkovSemigroup.tendsto_tvNorm_of_skeleton` (**(20.25) ⇒ (20.26)**, pp. 525–526): ergodicity of
  a `δ`-skeleton gives `‖Pᵗ(x, ·) − π‖ → 0`.
* `MarkovSemigroup.P_nsmul`: the `δ`-skeleton has `n`-step kernel `P^{nδ} = (P^δ)ⁿ`.
* `norm_kOp_le`: `κV ≤ cV` gives `‖κ‖ ≤ c` on `L∞_V`.
* `vUniform_of_skeleton`: a `V`-uniformly ergodic `δ`-skeleton together with `PˢV ≤ cV`
  (`s ≤ δ`) gives (20.34), `|||Pᵗ − 1 ⊗ π|||_V ≤ R'ρᵗ`, through
  `Pᵗ − 1 ⊗ π = (P^{nδ} − 1 ⊗ π)Pˢ` and the operator norm of `WeightedSpace`.
* **Theorem 20.3.2, the part proved** (`theorem_20_3_2_skeleton`, p. 527): (V4) for an
  irreducible aperiodic skeleton on a petite set, with `PˢV ≤ cV` for `s ≤ δ`, gives `π(V) < ∞`
  and (20.34) (through Theorem 16.1.2).

**Not formalised.** The equivalence of (i) `|Pᵗ(x, C) − P^∞(C)| ≤ M_C ρ_Cᵗ` (20.32), (ii)
`sup_C E_x[κ^{τ_C}] < ∞` (20.33) and (iii) the generator drift (20.31) needs hitting times `τ_C`
of a CADLAG process, the strong Markov property in continuous time and the transfer of
petiteness and aperiodicity from the sampled chains to a skeleton (Down–Meyn–Tweedie [101]).
Mathlib has no construction of a continuous-time Markov process from a semigroup, so these are
not formalised; the theorem is proved from a drift condition on a skeleton, which is the form the
proof in [101] reduces to. The definitions of ψ-irreducibility, positivity and aperiodicity of a
process (p. 525) are made through the sampled chains `resolventKernel` and skeletons `P (n * δ)`,
on which the Chapter 16 results apply directly. The skeleton-level equivalence of (20.31)–(20.33)
and (20.34) is in `ExponentialErgodicKernel`.
-/
namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X]

namespace MarkovSemigroup

/-- `P^{s+r}(x, ·) = Pʳ ∘ Pˢ(x, ·)` as a measure. -/
theorem P_add_apply (S : MarkovSemigroup X) {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (x : X) :
    S.P (s + r) x = S.P r ∘ₘ S.P s x := by
  rw [S.P_add hs hr, Kernel.comp_apply]

/-- **The total variation distance to `π` is non-increasing in `t`** (MT p. 526), for `π` invariant
for every `Pᵗ`. -/
theorem tvNorm_antitone (S : MarkovSemigroup X) {π : Measure X} [IsProbabilityMeasure π]
    (hinv : ∀ t, 0 ≤ t → IsInvariant (S.P t) π) (x : X) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    tvNorm (S.P t x) π ≤ tvNorm (S.P s x) π := by
  have := S.isMarkovKernel_P
  have hr : 0 ≤ t - s := by linarith
  have ht : t = s + (t - s) := by ring
  rw [ht, S.P_add_apply hs hr x]
  conv_lhs => rw [← (hinv (t - s) hr)]
  have h := tvNorm_comp_le_of_le (Q := S.P (t - s)) (ν := 0) (fun _ => Measure.zero_le _)
    (S.P s x) π
  rwa [Measure.real_def, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero, sub_zero,
    one_mul] at h

/-- **(20.25) ⇒ (20.26)** (MT pp. 525–526): if the `δ`-skeleton converges in total variation,
`‖P^{nδ}(x, ·) − π‖ → 0`, and `π` is invariant for every `Pᵗ`, then `‖Pᵗ(x, ·) − π‖ → 0` as
`t → ∞` (since the distance is non-increasing in `t`). -/
theorem tendsto_tvNorm_of_skeleton (S : MarkovSemigroup X) {π : Measure X}
    [IsProbabilityMeasure π] (hinv : ∀ t, 0 ≤ t → IsInvariant (S.P t) π) {δ : ℝ} (hδ : 0 < δ)
    (x : X) (hskel : Tendsto (fun n : ℕ => tvNorm (S.P (n * δ) x) π) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => tvNorm (S.P t x) π) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hskel ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hskel ε hε
  refine ⟨N * δ, fun t ht => ?_⟩
  have h1 := hN N le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tvNorm_nonneg _ _)] at h1 ⊢
  exact lt_of_le_of_lt (S.tvNorm_antitone hinv x (by positivity) ht) h1

/-- The `δ`-skeleton: `P^{nδ} = (P^δ)ⁿ`. -/
theorem P_nsmul (S : MarkovSemigroup X) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    S.P (n * δ) = S.P δ ^ n := by
  induction n with
  | zero =>
    ext x : 1
    rw [Nat.cast_zero, zero_mul, P_apply, S.zero_eq, pow_zero]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, S.P_add (by positivity) hδ, ih, pow_succ']
    rfl

end MarkovSemigroup

/-- The operator bound `‖κ̃‖ ≤ c` on `L∞_V` when `κV ≤ cV`. -/
theorem norm_kOp_le {V : X → ℝ} {κ : Kernel X X} (h : WeightOK V κ) {c : ℝ} (hc : 0 ≤ c)
    (hκ : ∀ x, ∫⁻ y, ENNReal.ofReal (V y) ∂κ x ≤ ENNReal.ofReal (c * V x)) :
    ‖kOp V κ‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun g => norm_le_of_bmFun_le
    (mul_nonneg hc (norm_nonneg g)) fun x => ?_
  have hVx := h.pos x
  have hIV : ∫ y, V y ∂κ x ≤ c * V x := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => (h.pos y).le)
      h.1.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hc hVx.le) (hκ x)
  have hI : ‖∫ y, bmFun g y * (V y : ℂ) ∂κ x‖ ≤ ‖g‖ * (c * V x) := by
    calc ‖∫ y, bmFun g y * (V y : ℂ) ∂κ x‖ ≤ ∫ y, ‖g‖ * V y ∂κ x := by
          refine norm_integral_le_of_norm_le ((h.integrable_V x).const_mul _)
            (Eventually.of_forall fun y => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h.pos y).le]
          exact mul_le_mul_of_nonneg_right (norm_bmFun_le g y) (h.pos y).le
      _ = ‖g‖ * ∫ y, V y ∂κ x := integral_const_mul _ _
      _ ≤ ‖g‖ * (c * V x) := mul_le_mul_of_nonneg_left hIV (norm_nonneg g)
  rw [kOp_apply h, kFun, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hVx.le]
  calc (V x)⁻¹ * ‖∫ y, bmFun g y * (V y : ℂ) ∂κ x‖ ≤ (V x)⁻¹ * (‖g‖ * (c * V x)) :=
        mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hVx.le)
    _ = c * ‖g‖ := by field_simp


/-- `r⁻ⁿ ≤ r · (r^{−1/δ})ᵗ` for `n = ⌊t/δ⌋`. -/
theorem inv_pow_floor_le {r δ t : ℝ} (hr : 1 < r) :
    r⁻¹ ^ ⌊t / δ⌋₊ ≤ r * (r ^ (-(1 / δ))) ^ t := by
  have hr0 : 0 < r := by linarith
  have hfl : t / δ - 1 < ⌊t / δ⌋₊ := by
    have := Nat.lt_floor_add_one (t / δ); linarith
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hr0.le, ← Real.rpow_mul hr0.le]
  calc r ^ (-(⌊t / δ⌋₊ : ℝ)) ≤ r ^ (1 + -(1 / δ) * t) :=
        Real.rpow_le_rpow_of_exponent_le hr.le (by
          have : -(1 / δ) * t = -(t / δ) := by ring
          rw [this]; linarith)
    _ = r * r ^ (-(1 / δ) * t) := by rw [Real.rpow_add hr0, Real.rpow_one]

variable {V : X → ℝ} {π : Measure X} in
/-- **The exponential rate (20.34) from a `V`-uniformly ergodic skeleton** (the last step of
Theorem 20.3.2, MT p. 528): if `π` is invariant for every `Pᵗ`, `π(V) < ∞`, `PˢV ≤ cV` for
`0 ≤ s ≤ δ`, and the `δ`-skeleton satisfies `|||P^{nδ} − 1 ⊗ π|||_V ≤ R r⁻ⁿ`, then
`|||Pᵗ − 1 ⊗ π|||_V ≤ R' ρᵗ` for all `t ≥ 0`, with `ρ = r^{−1/δ} < 1`. -/
theorem vUniform_of_skeleton (S : MarkovSemigroup X) [IsProbabilityMeasure π]
    (hinv : ∀ t, 0 ≤ t → IsInvariant (S.P t) π) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hπV : ∫⁻ y, ENNReal.ofReal (V y) ∂π ≠ ∞) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c)
    (hloc : ∀ s, 0 ≤ s → s ≤ δ → ∀ x,
      ∫⁻ y, ENNReal.ofReal (V y) ∂S.P s x ≤ ENNReal.ofReal (c * V x))
    {R r : ℝ} (hr : 1 < r) (hR : 0 ≤ R)
    (hskel : ∀ n, vErgDist (eW V) (S.P δ) π n ≤ ENNReal.ofReal (R * r⁻¹ ^ n)) :
    r ^ (-(1 / δ)) < 1 ∧ ∀ t, 0 ≤ t → vOpNorm (eW V) (S.P t) (Kernel.const X π) ≤
      ENNReal.ofReal (2 * R * c * r * (r ^ (-(1 / δ))) ^ t) := by
  have hr0 : 0 < r := by linarith
  refine ⟨Real.rpow_lt_one_of_one_lt_of_neg hr (by
    have : 0 < 1 / δ := by positivity
    linarith), fun t ht => ?_⟩
  have := S.isMarkovKernel_P
  set n := ⌊t / δ⌋₊ with hn
  set s := t - n * δ with hs
  have hnδ : (n : ℝ) * δ ≤ t := by
    have := Nat.floor_le (div_nonneg ht hδ.le)
    rw [← hn] at this
    calc (n : ℝ) * δ ≤ t / δ * δ := mul_le_mul_of_nonneg_right this hδ.le
      _ = t := by field_simp
  have hsδ : s ≤ δ := by
    have := Nat.lt_floor_add_one (t / δ)
    rw [← hn] at this
    have h2 : t < (n + 1) * δ := by
      calc t = t / δ * δ := by field_simp
        _ < (n + 1) * δ := mul_lt_mul_of_pos_right this hδ
    rw [hs]; linarith
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hW : ∀ u, 0 ≤ u → u ≤ δ → WeightOK V (S.P u) := fun u hu1 hu2 =>
    ⟨hV, hV1, c, hc, hloc u hu1 hu2⟩
  have hWδ := hW δ hδ.le le_rfl
  have hWs := hW s hs0 hsδ
  have hPi := weightOK_const hV hV1 π hπV
  have ht' : t = n * δ + s := by rw [hs]; ring
  have hPt : S.P t = S.P s ∘ₖ (S.P δ ^ n) := by
    rw [ht', S.P_add (by positivity) hs0, S.P_nsmul hδ.le]
  have hpow := kOp_pow hWδ n
  have := isMarkovKernel_pow (S.P δ) n
  have hWt : WeightOK V (S.P t) := by rw [hPt]; exact hWs.comp hpow.1
  have hkt : kOp V (S.P t) - kOp V (Kernel.const X π) =
      (kOp V (S.P δ) ^ n - kOp V (Kernel.const X π)) * kOp V (S.P s) := by
    rw [hPt, kOp_comp hWs hpow.1, hpow.2, sub_mul (kOp V (S.P δ) ^ n)
      (kOp V (Kernel.const X π)) (kOp V (S.P s)), kOp_const_mul_kOp hWs hPi (hinv s hs0)]
  have hnorm : ‖kOp V (S.P t) - kOp V (Kernel.const X π)‖ ≤ 2 * (R * r⁻¹ ^ n) * c := by
    rw [hkt]
    have h1 : ‖kOp V (S.P δ) ^ n - kOp V (Kernel.const X π)‖ ≤ 2 * (R * r⁻¹ ^ n) :=
      norm_le_vErgDist hWδ hPi n (mul_nonneg hR (pow_nonneg (inv_nonneg.2 hr0.le) n)) (hskel n)
    have h2 : ‖kOp V (S.P s)‖ ≤ c := norm_kOp_le hWs hc (hloc s hs0 hsδ)
    calc ‖(kOp V (S.P δ) ^ n - kOp V (Kernel.const X π)) * kOp V (S.P s)‖
        ≤ ‖kOp V (S.P δ) ^ n - kOp V (Kernel.const X π)‖ * ‖kOp V (S.P s)‖ :=
          norm_mul_le (kOp V (S.P δ) ^ n - kOp V (Kernel.const X π)) (kOp V (S.P s))
      _ ≤ 2 * (R * r⁻¹ ^ n) * c := mul_le_mul h1 h2 (norm_nonneg (kOp V (S.P s)))
          (by positivity)
  refine vOpNorm_le fun x => ?_
  have h1 := fNorm_le_norm_kOp_sub hWt hPi x
  rw [Kernel.const_apply] at h1
  refine h1.trans ?_
  rw [ENNReal.ofReal_mul (ContinuousLinearMap.opNorm_nonneg _)]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  calc ‖kOp V (S.P t) - kOp V (Kernel.const X π)‖ ≤ 2 * (R * r⁻¹ ^ n) * c := hnorm
    _ ≤ 2 * (R * (r * (r ^ (-(1 / δ))) ^ t)) * c := by
        gcongr
        exact inv_pow_floor_le hr
    _ = 2 * R * c * r * (r ^ (-(1 / δ))) ^ t := by ring


variable [MeasurableSpace.CountablyGenerated X] {V : X → ℝ} {π : Measure X} {ψ : Measure X} in
/-- **Theorem 20.3.2, the part proved here** (MT p. 527–528): suppose some `δ`-skeleton is
`ψ`-irreducible and aperiodic and satisfies (V4) for a set `C` petite for the skeleton,
`P^δV ≤ λV + b 1_C` with `λ < 1`, that `PˢV ≤ cV` for `0 ≤ s ≤ δ`, and that `π` is an invariant
probability for every `Pᵗ`. Then `π(V) < ∞` and the exponential ergodic bound (20.34) holds:
`|||Pᵗ − 1 ⊗ π|||_V ≤ R' ρᵗ` for all `t ≥ 0`, some `ρ < 1`. -/
theorem theorem_20_3_2_skeleton (S : MarkovSemigroup X) [IsProbabilityMeasure π]
    (hinv : ∀ t, 0 ≤ t → IsInvariant (S.P t) π) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c)
    (hψ : haveI := S.isMarkovKernel_P δ; IsMaximalIrreducibility (S.P δ) ψ)
    (hap : haveI := S.isMarkovKernel_P δ; IsAperiodic (S.P δ) ψ)
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) {lam b : ℝ≥0∞} (hlam : lam < 1) (hb : b ≠ ∞)
    {C : Set X} (hC : IsPetite (S.P δ) C) (hd : DriftV4 (S.P δ) (eW V) lam b C)
    (hloc : ∀ s, 0 ≤ s → s ≤ δ → ∀ x,
      ∫⁻ y, ENNReal.ofReal (V y) ∂S.P s x ≤ ENNReal.ofReal (c * V x)) :
    ∫⁻ y, ENNReal.ofReal (V y) ∂π ≠ ∞ ∧ ∃ R' ρ : ℝ, ρ < 1 ∧ ∀ t, 0 ≤ t →
      vOpNorm (eW V) (S.P t) (Kernel.const X π) ≤ ENNReal.ofReal (R' * ρ ^ t) := by
  have := S.isMarkovKernel_P δ
  obtain ⟨hπV, r, hr, hrt, R, hR, hbd⟩ := vErgDist_le_of_driftV4 hψ hap
    (ENNReal.measurable_ofReal.comp hV) (fun x => ENNReal.one_le_ofReal.2 (hV1 x))
    (fun _ => ENNReal.ofReal_ne_top) hlam hb hC hd π (hinv δ hδ.le)
  have hr1 : 1 < r.toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hrt).2 hr
    rwa [ENNReal.toReal_one] at this
  have hskel : ∀ n, vErgDist (eW V) (S.P δ) π n ≤
      ENNReal.ofReal (R.toReal * r.toReal⁻¹ ^ n) := fun n => by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hR,
      ENNReal.ofReal_pow (inv_nonneg.2 ENNReal.toReal_nonneg), ← ENNReal.toReal_inv,
      ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 (zero_lt_one.trans hr).ne')]
    exact hbd n
  obtain ⟨hρ, hbound⟩ := vUniform_of_skeleton S hinv hV hV1 hπV hδ hc hloc hr1
    ENNReal.toReal_nonneg hskel
  exact ⟨hπV, _, _, hρ, hbound⟩

end MeynTweedie.Epilogue
