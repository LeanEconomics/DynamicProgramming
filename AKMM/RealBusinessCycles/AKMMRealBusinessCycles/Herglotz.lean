/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Herglotz theorem

AKMM, §14.3.1, pp. 412–413 (beyond the text).

AKMM, §14.3.1, pp. 412–413 (a result beyond the text). The book states without proof that "any
stationary process" is a random superposition of sines and cosines; the first half of that
statement is the existence and uniqueness of the spectral measure, proved here.

The circle is `AddCircle T` (`ℝ/Tℤ`, `T > 0`) with the characters `eₕ = fourier h`,
`eₕ(x) = e^{2πihx/T}`; for `T = 2π` these are `e^{ihω}`, `ω ∈ (−π, π]`.

* Positive definiteness (`hergPosDef`): `Σⱼₖ cⱼc̄ₖγ(j − k)` is real and `≥ 0` for every finite `c`.
* **The Herglotz theorem** (`herg_herglotz`): `γ : ℤ → ℂ` is positive definite if and only if
  `γ(h) = ∫ eₕ dF` for a finite positive measure `F` on the circle, and `F` is unique
  (`herg_unique`).
* Existence (`herg_exists`). The Fejér densities `f_N = Σ_{|h|<N}(1 − |h|/N)γ(h)e_{−h}` are the
  quadratic forms `(1/N)Σ_{j,k<N}cⱼc̄ₖγ(j − k)` with `cⱼ = e_{−j}(x)` (`herg_fejer_eq`, by
  `herg_sum_pairs`, `herg_card_pairs`), hence nonnegative (`herg_fejer_nonneg`); their Fourier
  coefficients `(1 − |m|/N)⁺γ(m)` tend to `γ(m)` (`herg_fejer_coeff`, `herg_fejer_tendsto`); the
  functionals `L_N(G) = ∫ G f_N dHaar` satisfy `‖L_N(G)‖ ≤ γ(0)‖G‖` (`herg_bound`) and therefore
  converge for every continuous `G` by density of trigonometric polynomials (`herg_tendsto`); the
  limit is a positive linear functional (`hergLambda`), and the Riesz–Markov–Kakutani theorem
  gives the measure.
* Uniqueness (`herg_unique`, via `herg_integral_eq_of_coeff`): trigonometric polynomials are
  dense in `C(𝕋, ℂ)`.
* The converse (`herg_posDef_of_measure`): `Σⱼₖ cⱼc̄ₖγ(j − k) = ∫ |Σⱼ cⱼeⱼ|² dF ≥ 0`.
* `γ(−h) = conj γ(h)` (`herg_conj`); for real `γ` the spectral measure is symmetric,
  `F ∘ (−·) = F` (`herg_symm_of_real`).

Departures: `γ` is complex-valued (real `γ` is the special case); the limit of the Fejér measures
is obtained from Riesz–Markov–Kakutani, not Prokhorov: the Fejér functionals converge on all of
`C(𝕋)`, so no subsequence is needed.
-/

namespace AKMM.RealBusinessCycles

open Complex MeasureTheory AddCircle Filter Topology
open scoped ComplexConjugate CompactlySupported

variable {T : ℝ}

/-- A function `γ : ℤ → ℂ` is positive definite if `Σⱼₖ cⱼc̄ₖγ(j − k)` is real and nonnegative for
every finite family `c`. -/
def hergPosDef (γ : ℤ → ℂ) : Prop :=
  ∀ (s : Finset ℤ) (c : ℤ → ℂ),
    (∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * γ (j - k)).im = 0 ∧
      0 ≤ (∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * γ (j - k)).re

/-- The number of pairs `(j, k) ∈ [0, N)²` with `j − k = h` is `(N − |h|)⁺`. -/
theorem herg_card_pairs (N : ℕ) (h : ℤ) :
    ((Finset.Ico (0 : ℤ) N ×ˢ Finset.Ico (0 : ℤ) N).filter (fun p => p.1 - p.2 = h)).card =
      ((N : ℤ) - |h|).toNat := by
  have hmax1 := le_max_left 0 h
  have hmax2 := le_max_right 0 h
  have hmin1 := min_le_left (N : ℤ) (N + h)
  have hmin2 := min_le_right (N : ℤ) (N + h)
  have e : (Finset.Ico (0 : ℤ) N ×ˢ Finset.Ico (0 : ℤ) N).filter (fun p => p.1 - p.2 = h) =
      (Finset.Ico (max 0 h) (min (N : ℤ) (N + h))).map
        ⟨fun j => (j, j - h), fun a b hab => by simpa using congrArg Prod.fst hab⟩ := by
    ext ⟨j, k⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_map]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
      refine ⟨j, ⟨max_le h1 (by omega), lt_min h2 (by omega)⟩, ?_⟩
      change (j, j - h) = (j, k)
      rw [← h5, sub_sub_cancel]
    · rintro ⟨a, ⟨h1, h2⟩, he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (he : (a, a - h) = (j, k))
      omega
  rw [e, Finset.card_map, Int.card_Ico]
  rcases le_total 0 h with h0 | h0
  · rw [max_eq_right h0, min_eq_left (by omega), abs_of_nonneg h0]
  · rw [max_eq_left h0, min_eq_right (by omega), abs_of_nonpos h0]
    congr 1
    ring

/-- Re-indexing the double sum `Σ_{j,k∈[0,N)} f(j − k)` by `h = j − k`. -/
theorem herg_sum_pairs (N : ℕ) (f : ℤ → ℂ) :
    ∑ j ∈ Finset.Ico (0 : ℤ) N, ∑ k ∈ Finset.Ico (0 : ℤ) N, f (j - k) =
      ∑ h ∈ Finset.Ioo (-(N : ℤ)) N, (((N : ℝ) - |(h : ℝ)| : ℝ) : ℂ) * f h := by
  rw [← Finset.sum_product' (f := fun j k => f (j - k)),
    ← Finset.sum_fiberwise_of_maps_to (g := fun p : ℤ × ℤ => p.1 - p.2)
      (t := Finset.Ioo (-(N : ℤ)) N)]
  · refine Finset.sum_congr rfl fun h hh => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f h) (fun p hp => by rw [(Finset.mem_filter.1 hp).2]),
      Finset.sum_const, herg_card_pairs, nsmul_eq_mul]
    congr 1
    rw [Finset.mem_Ioo] at hh
    have h0 : 0 ≤ (N : ℤ) - |h| := by rw [sub_nonneg]; exact (abs_lt.2 hh).le
    have : (((N : ℤ) - |h|).toNat : ℝ) = (N : ℝ) - |(h : ℝ)| := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
      push_cast [Int.cast_abs]
      ring
    rw [← this]
    push_cast
    ring
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_Ico] at hp
    simp only [Finset.mem_Ioo]
    omega

/-- Continuous functions are integrable for a finite measure on the circle. -/
theorem herg_integrable [Fact (0 < T)] (μ : Measure (AddCircle T)) [IsFiniteMeasure μ]
    {G : AddCircle T → ℂ} (hG : Continuous G) : Integrable G μ :=
  hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem herg_re_integral {μ : Measure (AddCircle T)} {f : AddCircle T → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := by
  simpa using (integral_re hf).symm

theorem herg_im_integral {μ : Measure (AddCircle T)} {f : AddCircle T → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ := by
  simpa using (integral_im hf).symm

/-- `∫ eₖ dHaar = 1` if `k = 0` and `0` otherwise (normalised Haar measure). -/
theorem herg_integral_fourier [Fact (0 < T)] (k : ℤ) :
    ∫ x, fourier k x ∂(haarAddCircle (T := T)) = if k = 0 then 1 else 0 := by
  have := congrFun (fourierCoeff_fourier (T := T) k) 0
  simp only [fourierCoeff, neg_zero, fourier_zero, smul_eq_mul, one_mul] at this
  rw [this, Pi.single_apply]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [hk, Ne.symm hk]

/-- The Fejér density `f_N(x) = Σ_{|h|<N} (1 − |h|/N)γ(h)e_{−h}(x)`. -/
noncomputable def hergFejer (γ : ℤ → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  ∑ h ∈ Finset.Ioo (-(N : ℤ)) N, ((((N : ℝ) - |(h : ℝ)|) / N : ℝ) : ℂ) * γ h * fourier (-h) x

/-- The Fejér density is the quadratic form `(1/N)Σ_{j,k<N} cⱼc̄ₖγ(j − k)` with `cⱼ = e_{−j}(x)`. -/
theorem herg_fejer_eq (γ : ℤ → ℂ) (N : ℕ) (x : AddCircle T) :
    hergFejer γ N x = ((1 / N : ℝ) : ℂ) * ∑ j ∈ Finset.Ico (0 : ℤ) N,
      ∑ k ∈ Finset.Ico (0 : ℤ) N, fourier (-j) x * conj (fourier (-k) x) * γ (j - k) := by
  have e : ∀ j k : ℤ, fourier (-j) x * conj (fourier (-k) x) * γ (j - k) =
      γ (j - k) * fourier (-(j - k)) x := by
    intro j k
    rw [← fourier_neg, neg_neg, show -(j - k) = -j + k by ring, fourier_add]
    ring
  simp_rw [e]
  rw [herg_sum_pairs N (fun h => γ h * fourier (-h) x), Finset.mul_sum]
  unfold hergFejer
  refine Finset.sum_congr rfl fun h _ => ?_
  push_cast
  ring

/-- For positive definite `γ` the Fejér density is real and nonnegative. -/
theorem herg_fejer_nonneg {γ : ℤ → ℂ} (hpd : hergPosDef γ) (N : ℕ) (x : AddCircle T) :
    (hergFejer γ N x).im = 0 ∧ 0 ≤ (hergFejer γ N x).re := by
  obtain ⟨h1, h2⟩ := hpd (Finset.Ico 0 N) (fun j => fourier (-j) x)
  rw [herg_fejer_eq, Complex.im_ofReal_mul, Complex.re_ofReal_mul]
  exact ⟨by rw [h1, mul_zero], mul_nonneg (by positivity) h2⟩

theorem herg_fejer_continuous (γ : ℤ → ℂ) (N : ℕ) : Continuous (hergFejer (T := T) γ N) :=
  continuous_finsetSum _ fun h _ => continuous_const.mul (fourier (-h)).continuous

/-- The Fejér functional `L_N(G) = ∫ G f_N dHaar`. -/
noncomputable def hergL [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ) (G : C(AddCircle T, ℂ)) : ℂ :=
  ∫ x, G x * hergFejer γ N x ∂haarAddCircle

/-- The Fourier coefficients of the Fejér density: `(1 − |m|/N)⁺γ(m)`. -/
theorem herg_fejer_coeff [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ) (m : ℤ) :
    hergL γ N (fourier (T := T) m) = if m ∈ Finset.Ioo (-(N : ℤ)) N then
      ((((N : ℝ) - |(m : ℝ)|) / N : ℝ) : ℂ) * γ m else 0 := by
  unfold hergL hergFejer
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun h _ => herg_integrable _ (by fun_prop))]
  have hterm : ∀ h : ℤ, ∫ x, fourier m x * (((((N : ℝ) - |(h : ℝ)|) / N : ℝ) : ℂ) * γ h *
      fourier (-h) x) ∂(haarAddCircle (T := T)) =
      ((((N : ℝ) - |(h : ℝ)|) / N : ℝ) : ℂ) * γ h * (if m = h then 1 else 0) := by
    intro h
    have e : (fun x : AddCircle T => fourier m x * (((((N : ℝ) - |(h : ℝ)|) / N : ℝ) : ℂ) *
        γ h * fourier (-h) x)) = fun x => ((((N : ℝ) - |(h : ℝ)|) / N : ℝ) : ℂ) * γ h *
        fourier (m + -h) x := by
      funext x
      rw [fourier_add]
      ring
    rw [e, integral_const_mul, herg_integral_fourier]
    congr 1
    rcases eq_or_ne m h with rfl | hmh
    · simp
    · have : m + -h ≠ 0 := by rw [← sub_eq_add_neg]; exact sub_ne_zero.2 hmh
      simp [this, hmh]
  simp_rw [hterm, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-- The Fourier coefficients of the Fejér densities converge: `L_N(eₘ) → γ(m)`. -/
theorem herg_fejer_tendsto [Fact (0 < T)] (γ : ℤ → ℂ) (m : ℤ) :
    Tendsto (fun n : ℕ => hergL γ (n + 1) (fourier (T := T) m)) atTop (𝓝 (γ m)) := by
  have hev : (fun n : ℕ => ((1 - |(m : ℝ)| * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) * γ m) =ᶠ[atTop]
      fun n => hergL γ (n + 1) (fourier (T := T) m) := by
    filter_upwards [eventually_gt_atTop m.natAbs] with n hn
    have hmem : m ∈ Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) := by
      rw [Finset.mem_Ioo]
      omega
    simp only [herg_fejer_coeff, hmem, ↓reduceIte]
    congr 1
    push_cast
    field_simp
  have hlim : Tendsto (fun n : ℕ => (1 - |(m : ℝ)| * (1 / ((n : ℝ) + 1)) : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul |(m : ℝ)|)
  have := ((continuous_ofReal.tendsto 1).comp hlim).mul_const (γ m)
  simp only [ofReal_one, one_mul] at this
  exact this.congr' hev

/-- `∫ f_N dHaar = γ(0)` for `N ≥ 1`. -/
theorem herg_integral_fejer [Fact (0 < T)] (γ : ℤ → ℂ) (n : ℕ) :
    ∫ x, hergFejer (T := T) γ (n + 1) x ∂haarAddCircle = γ 0 := by
  have := herg_fejer_coeff (T := T) γ (n + 1) 0
  have hmem : (0 : ℤ) ∈ Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) := by
    rw [Finset.mem_Ioo]
    omega
  simp only [hergL, fourier_zero, one_mul, hmem, ↓reduceIte] at this
  rw [this]
  simp only [Int.cast_zero, abs_zero, sub_zero]
  rw [div_self (by positivity), ofReal_one, one_mul]

theorem herg_fejer_norm {γ : ℤ → ℂ} (hpd : hergPosDef γ) (N : ℕ) (x : AddCircle T) :
    ‖hergFejer γ N x‖ = (hergFejer γ N x).re := by
  obtain ⟨h1, h2⟩ := herg_fejer_nonneg hpd N x
  have : hergFejer γ N x = ((hergFejer γ N x).re : ℂ) := Complex.ext (by simp) (by simp [h1])
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2]
  simp

/-- `γ(0)` is real and nonnegative for positive definite `γ`. -/
theorem herg_posDef_zero {γ : ℤ → ℂ} (hpd : hergPosDef γ) : (γ 0).im = 0 ∧ 0 ≤ (γ 0).re := by
  simpa using hpd {0} (fun _ => 1)

/-- The uniform bound `‖L_N(G)‖ ≤ ‖G‖γ(0)`. -/
theorem herg_bound [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) (n : ℕ)
    (G : C(AddCircle T, ℂ)) : ‖hergL γ (n + 1) G‖ ≤ ‖G‖ * (γ 0).re := by
  unfold hergL
  calc ‖∫ x, G x * hergFejer γ (n + 1) x ∂haarAddCircle‖
      ≤ ∫ x, ‖G‖ * (hergFejer γ (n + 1) x).re ∂haarAddCircle :=
        norm_integral_le_of_norm_le
          ((herg_integrable _ (herg_fejer_continuous γ (n + 1))).re.const_mul _)
          (ae_of_all _ fun x => by
            rw [norm_mul, herg_fejer_norm hpd]
            exact mul_le_mul_of_nonneg_right (G.norm_coe_le_norm x)
              (herg_fejer_nonneg hpd _ x).2)
    _ = ‖G‖ * (γ 0).re := by
      rw [integral_const_mul, ← herg_integral_fejer (T := T) γ n,
        herg_re_integral (herg_integrable _ (herg_fejer_continuous γ (n + 1)))]

theorem herg_L_add [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ) (G G' : C(AddCircle T, ℂ)) :
    hergL γ N (G + G') = hergL γ N G + hergL γ N G' := by
  unfold hergL
  simp only [ContinuousMap.add_apply, add_mul]
  exact integral_add (herg_integrable _ (G.continuous.mul (herg_fejer_continuous γ N)))
    (herg_integrable _ (G'.continuous.mul (herg_fejer_continuous γ N)))

theorem herg_L_smul [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ) (c : ℂ) (G : C(AddCircle T, ℂ)) :
    hergL γ N (c • G) = c * hergL γ N G := by
  unfold hergL
  simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem herg_L_sub [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ) (G G' : C(AddCircle T, ℂ)) :
    hergL γ N (G - G') = hergL γ N G - hergL γ N G' := by
  rw [sub_eq_add_neg, herg_L_add, ← neg_one_smul ℂ G', herg_L_smul]
  ring

/-- On trigonometric polynomials the Fejér functionals converge. -/
theorem herg_tendsto_span [Fact (0 < T)] (γ : ℤ → ℂ) {G : C(AddCircle T, ℂ)}
    (hG : G ∈ Submodule.span ℂ (Set.range (fourier (T := T)))) :
    ∃ l, Tendsto (fun n : ℕ => hergL γ (n + 1) G) atTop (𝓝 l) := by
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨γ m, herg_fejer_tendsto γ m⟩
  | zero => exact ⟨0, by simp [hergL]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simpa only [herg_L_add] using ha.add hb⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simpa only [herg_L_smul] using ha.const_mul c⟩

/-- For positive definite `γ` the Fejér functionals `L_N(G)` converge for every continuous `G`
(uniform bound plus density of trigonometric polynomials). -/
theorem herg_tendsto [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) (G : C(AddCircle T, ℂ)) :
    ∃ l, Tendsto (fun n : ℕ => hergL γ (n + 1) G) atTop (𝓝 l) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set c := (γ 0).re with hc
  have hc0 : 0 ≤ c := (herg_posDef_zero hpd).2
  have hG : G ∈ closure (Submodule.span ℂ (Set.range (fourier (T := T))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hG (ε / (3 * (c + 1))) (by positivity)
  obtain ⟨l, hl⟩ := herg_tendsto_span γ hb
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hl.cauchySeq (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hGb : ‖G - b‖ * c ≤ ε / 3 := by
    rw [← dist_eq_norm]
    calc dist G b * c ≤ ε / (3 * (c + 1)) * c := mul_le_mul_of_nonneg_right hdist.le hc0
      _ ≤ ε / (3 * (c + 1)) * (c + 1) := by gcongr; linarith
      _ = ε / 3 := by field_simp
  have h1 : dist (hergL γ (n + 1) G) (hergL γ (n + 1) b) ≤ ε / 3 := by
    rw [dist_eq_norm, ← herg_L_sub]
    exact (herg_bound hpd n _).trans hGb
  have h2 : dist (hergL γ (N + 1) b) (hergL γ (N + 1) G) ≤ ε / 3 := by
    rw [dist_comm, dist_eq_norm, ← herg_L_sub]
    exact (herg_bound hpd N _).trans hGb
  have h3 := hN n hn
  calc dist (hergL γ (n + 1) G) (hergL γ (N + 1) G)
      ≤ dist (hergL γ (n + 1) G) (hergL γ (n + 1) b) + dist (hergL γ (n + 1) b)
        (hergL γ (N + 1) b) + dist (hergL γ (N + 1) b) (hergL γ (N + 1) G) :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-- The limit functional `L(G) = lim_N L_N(G)`. -/
noncomputable def hergLim [Fact (0 < T)] (γ : ℤ → ℂ) (G : C(AddCircle T, ℂ)) : ℂ :=
  limUnder atTop (fun n : ℕ => hergL γ (n + 1) G)

theorem herg_tendsto_lim [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ)
    (G : C(AddCircle T, ℂ)) :
    Tendsto (fun n : ℕ => hergL γ (n + 1) G) atTop (𝓝 (hergLim γ G)) :=
  tendsto_nhds_limUnder (herg_tendsto hpd G)

theorem herg_lim_add [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ)
    (G G' : C(AddCircle T, ℂ)) : hergLim γ (G + G') = hergLim γ G + hergLim γ G' :=
  tendsto_nhds_unique (herg_tendsto_lim hpd (G + G'))
    (by simpa only [herg_L_add] using (herg_tendsto_lim hpd G).add (herg_tendsto_lim hpd G'))

theorem herg_lim_smul [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) (c : ℂ)
    (G : C(AddCircle T, ℂ)) : hergLim γ (c • G) = c * hergLim γ G :=
  tendsto_nhds_unique (herg_tendsto_lim hpd (c • G))
    (by simpa only [herg_L_smul] using (herg_tendsto_lim hpd G).const_mul c)

/-- A real continuous function as a complex one. -/
def hergOfReal (g : C(AddCircle T, ℝ)) : C(AddCircle T, ℂ) :=
  ⟨fun x => (g x : ℂ), continuous_ofReal.comp g.continuous⟩

/-- `Re L_N(G) = ∫ G f_N`, for real `G`, is `∫ G · Re f_N`. -/
theorem herg_L_ofReal_re [Fact (0 < T)] (γ : ℤ → ℂ) (N : ℕ)
    (g : C(AddCircle T, ℝ)) :
    (hergL γ N (hergOfReal g)).re = ∫ x, g x * (hergFejer γ N x).re ∂haarAddCircle := by
  unfold hergL
  have hi : Integrable (fun x => hergOfReal g x * hergFejer γ N x) haarAddCircle :=
    herg_integrable _ ((hergOfReal g).continuous.mul (herg_fejer_continuous γ N))
  rw [herg_re_integral hi]
  simp [hergOfReal]

/-- `Re L_N(Re a) = Re L_N(a)`, since `f_N` is real. -/
theorem herg_L_re [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) (N : ℕ)
    (a : C(AddCircle T, ℂ)) :
    (hergL γ N (hergOfReal ⟨fun x => (a x).re, by fun_prop⟩)).re = (hergL γ N a).re := by
  rw [herg_L_ofReal_re]
  unfold hergL
  have hi : Integrable (fun x => a x * hergFejer γ N x) haarAddCircle :=
    herg_integrable _ (a.continuous.mul (herg_fejer_continuous γ N))
  rw [herg_re_integral hi]
  congr 1
  funext x
  simp [Complex.mul_re, (herg_fejer_nonneg hpd N x).1]

/-- `Re L_N(Im a) = Im L_N(a)`, since `f_N` is real. -/
theorem herg_L_im [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) (N : ℕ)
    (a : C(AddCircle T, ℂ)) :
    (hergL γ N (hergOfReal ⟨fun x => (a x).im, by fun_prop⟩)).re = (hergL γ N a).im := by
  rw [herg_L_ofReal_re]
  unfold hergL
  have hi : Integrable (fun x => a x * hergFejer γ N x) haarAddCircle :=
    herg_integrable _ (a.continuous.mul (herg_fejer_continuous γ N))
  rw [herg_im_integral hi]
  congr 1
  funext x
  simp [Complex.mul_im, (herg_fejer_nonneg hpd N x).1]

/-- The positive linear functional `Λ(g) = Re L(g)` on `C(𝕋, ℝ)` (all continuous functions on
the circle are compactly supported). -/
noncomputable def hergLambda [Fact (0 < T)] (γ : ℤ → ℂ) (hpd : hergPosDef γ) :
    C_c(AddCircle T, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun g => (hergLim γ (hergOfReal g.toContinuousMap)).re
      map_add' := fun g g' => by
        have : hergOfReal (g + g').toContinuousMap =
            hergOfReal g.toContinuousMap + hergOfReal g'.toContinuousMap := by
          ext x
          simp [hergOfReal]
        rw [this, herg_lim_add hpd, Complex.add_re]
      map_smul' := fun r g => by
        have : hergOfReal (r • g).toContinuousMap = (r : ℂ) • hergOfReal g.toContinuousMap := by
          ext x
          simp [hergOfReal]
        rw [this, herg_lim_smul hpd, Complex.re_ofReal_mul]
        rfl }
    (fun g hg => by
      refine ge_of_tendsto' ((continuous_re.tendsto _).comp
        (herg_tendsto_lim hpd (hergOfReal g.toContinuousMap))) fun n => ?_
      simp only [Function.comp_apply]
      rw [herg_L_ofReal_re]
      exact integral_nonneg fun x => mul_nonneg (hg x) (herg_fejer_nonneg hpd _ x).2)

/-- AKMM, pp. 412–413 (beyond the text). **Existence in the Herglotz theorem.** A positive definite
`γ : ℤ → ℂ` is the sequence of Fourier coefficients `γ(h) = ∫ e_h dF` of a finite measure `F` on the
circle. -/
theorem herg_exists [Fact (0 < T)] {γ : ℤ → ℂ} (hpd : hergPosDef γ) :
    ∃ F : Measure (AddCircle T), IsFiniteMeasure F ∧ ∀ h, γ h = ∫ x, fourier h x ∂F := by
  refine ⟨RealRMK.rieszMeasure (hergLambda (T := T) γ hpd), inferInstance, fun h => ?_⟩
  set μ := RealRMK.rieszMeasure (hergLambda (T := T) γ hpd)
  let gr : C_c(AddCircle T, ℝ) := ⟨⟨fun x => (fourier h x).re, by fun_prop⟩,
    HasCompactSupport.of_compactSpace _⟩
  let gi : C_c(AddCircle T, ℝ) := ⟨⟨fun x => (fourier h x).im, by fun_prop⟩,
    HasCompactSupport.of_compactSpace _⟩
  have hint : Integrable (fun x => fourier h x) μ :=
    herg_integrable μ (fourier (T := T) h).continuous
  have hre : (∫ x, fourier h x ∂μ).re = (γ h).re := by
    rw [herg_re_integral hint]
    have := RealRMK.integral_rieszMeasure (hergLambda (T := T) γ hpd) gr
    change ∫ x, (fourier h x).re ∂μ = _ at this
    rw [this]
    change (hergLim γ (hergOfReal ⟨fun x => (fourier h x).re, by fun_prop⟩)).re = _
    refine tendsto_nhds_unique ((continuous_re.tendsto _).comp (herg_tendsto_lim hpd _)) ?_
    simp only [Function.comp_def, herg_L_re hpd]
    exact (continuous_re.tendsto _).comp (herg_fejer_tendsto γ h)
  have him : (∫ x, fourier h x ∂μ).im = (γ h).im := by
    rw [herg_im_integral hint]
    have := RealRMK.integral_rieszMeasure (hergLambda (T := T) γ hpd) gi
    change ∫ x, (fourier h x).im ∂μ = _ at this
    rw [this]
    change (hergLim γ (hergOfReal ⟨fun x => (fourier h x).im, by fun_prop⟩)).re = _
    refine tendsto_nhds_unique ((continuous_re.tendsto _).comp (herg_tendsto_lim hpd _)) ?_
    simp only [Function.comp_def, herg_L_im hpd]
    exact (continuous_im.tendsto _).comp (herg_fejer_tendsto γ h)
  exact (Complex.ext hre him).symm

/-- AKMM, pp. 412–413 (beyond the text). **The converse half of the Herglotz theorem.** The Fourier
coefficients of a finite measure on the circle are positive definite: `Σⱼₖ cⱼc̄ₖγ(j − k) = ∫ |Σⱼ
cⱼeⱼ|² dF ≥ 0`. -/
theorem herg_posDef_of_measure [Fact (0 < T)] (F : Measure (AddCircle T)) [IsFiniteMeasure F]
    {γ : ℤ → ℂ} (hγ : ∀ h, γ h = ∫ x, fourier h x ∂F) : hergPosDef γ := by
  intro s c
  have key : ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * γ (j - k) =
      ((∫ x, Complex.normSq (∑ j ∈ s, c j * fourier j x) ∂F : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    have e : ∀ x : AddCircle T, ((Complex.normSq (∑ j ∈ s, c j * fourier j x) : ℝ) : ℂ) =
        ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * fourier (j - k) x := by
      intro x
      rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, ← fourier_neg, sub_eq_add_neg, fourier_add]
      ring
    simp_rw [e, hγ]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (herg_integrable F (fourier (T := T) (j - k)).continuous).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ =>
      (herg_integrable F (fourier (T := T) (j - k)).continuous).const_mul _]
    exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
  rw [key, ofReal_im, ofReal_re]
  exact ⟨rfl, integral_nonneg fun x => Complex.normSq_nonneg _⟩

/-- A finite measure on the circle integrates every continuous function as its Fourier
coefficients dictate: two finite measures with the same Fourier coefficients have the same
integrals of all continuous functions (density of trigonometric polynomials). -/
theorem herg_integral_eq_of_coeff [Fact (0 < T)] {F G : Measure (AddCircle T)} [IsFiniteMeasure F]
    [IsFiniteMeasure G] (hFG : ∀ h, ∫ x, fourier h x ∂F = ∫ x, fourier h x ∂G)
    (A : C(AddCircle T, ℂ)) : ∫ x, A x ∂F = ∫ x, A x ∂G := by
  have hspan : ∀ b ∈ Submodule.span ℂ (Set.range (fourier (T := T))),
      ∫ x, b x ∂F = ∫ x, b x ∂G := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact hFG m
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [ContinuousMap.add_apply]
      rw [integral_add (herg_integrable F x.continuous) (herg_integrable F y.continuous),
        integral_add (herg_integrable G x.continuous) (herg_integrable G y.continuous), hx, hy]
    | smul c x _ hx =>
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, hx]
  have hA : A ∈ closure (Submodule.span ℂ (Set.range (fourier (T := T))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  refine eq_of_forall_dist_le fun ε hε => ?_
  set C := F.real Set.univ + G.real Set.univ + 1
  have hC : 0 < C := by positivity
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hA (ε / C) (by positivity)
  have hbd : ∀ (μ : Measure (AddCircle T)) [IsFiniteMeasure μ],
      ‖∫ x, A x ∂μ - ∫ x, b x ∂μ‖ ≤ ε / C * μ.real Set.univ := by
    intro μ _
    rw [← integral_sub (herg_integrable μ A.continuous) (herg_integrable μ b.continuous)]
    refine norm_integral_le_of_norm_le_const (ae_of_all _ fun x => ?_)
    have := (A - b).norm_coe_le_norm x
    rw [← dist_eq_norm] at this
    simp only [ContinuousMap.sub_apply] at this
    exact this.trans hdist.le
  rw [dist_eq_norm, show ∫ x, A x ∂F - ∫ x, A x ∂G =
    (∫ x, A x ∂F - ∫ x, b x ∂F) - (∫ x, A x ∂G - ∫ x, b x ∂G) by rw [hspan b hb]; ring]
  calc ‖(∫ x, A x ∂F - ∫ x, b x ∂F) - (∫ x, A x ∂G - ∫ x, b x ∂G)‖
      ≤ ε / C * F.real Set.univ + ε / C * G.real Set.univ :=
        (norm_sub_le _ _).trans (add_le_add (hbd F) (hbd G))
    _ ≤ ε / C * C := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ε := by field_simp

/-- AKMM, pp. 412–413 (beyond the text). **Uniqueness in the Herglotz theorem.** Two finite measures
on the circle with the same Fourier coefficients are equal. -/
theorem herg_unique [Fact (0 < T)] {F G : Measure (AddCircle T)} [IsFiniteMeasure F]
    [IsFiniteMeasure G] (hFG : ∀ h, ∫ x, fourier h x ∂F = ∫ x, fourier h x ∂G) : F = G := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have := herg_integral_eq_of_coeff hFG ⟨fun x => (f x : ℂ), by fun_prop⟩
  simp only [ContinuousMap.coe_mk] at this
  exact_mod_cast this

/-- AKMM, pp. 412–413 (beyond the text). **The Herglotz theorem.** `γ : ℤ → ℂ` is positive definite
if and only if `γ(h) = ∫ e^{2πihx/T} dF(x)` for a finite (positive) measure `F` on the circle
`ℝ/Tℤ`; for `T = 2π` this is `γ(h) = ∫_{(−π,π]} e^{ihω} dF(ω)`. The measure is unique
(`herg_unique`). -/
theorem herg_herglotz [Fact (0 < T)] (γ : ℤ → ℂ) :
    hergPosDef γ ↔ ∃ F : Measure (AddCircle T), IsFiniteMeasure F ∧
      ∀ h, γ h = ∫ x, fourier h x ∂F :=
  ⟨herg_exists, fun ⟨F, _, hF⟩ => herg_posDef_of_measure F hF⟩

/-- The Fourier coefficients of a finite measure are Hermitian: `γ(−h) = conj γ(h)`. -/
theorem herg_conj [Fact (0 < T)] (F : Measure (AddCircle T)) {γ : ℤ → ℂ}
    (hγ : ∀ h, γ h = ∫ x, fourier h x ∂F) (h : ℤ) : γ (-h) = conj (γ h) := by
  rw [hγ, hγ]
  simp_rw [fourier_neg]
  exact integral_conj

/-- For a real-valued (hence even) positive definite `γ` the spectral measure is symmetric:
`F(−A) = F(A)`. -/
theorem herg_symm_of_real [Fact (0 < T)] (F : Measure (AddCircle T)) [IsFiniteMeasure F]
    {γ : ℤ → ℂ} (hγ : ∀ h, γ h = ∫ x, fourier h x ∂F) (hreal : ∀ h, (γ h).im = 0) :
    F.map (fun x => -x) = F := by
  refine herg_unique fun h => ?_
  rw [integral_map measurable_neg.aemeasurable (fourier h).continuous.aestronglyMeasurable]
  have e : ∀ x : AddCircle T, fourier h (-x) = fourier (-h) x := fun x => by
    simp [fourier_apply, neg_smul, smul_neg]
  simp_rw [e]
  rw [← hγ, ← hγ, herg_conj F hγ, Complex.conj_eq_iff_im.2 (hreal h)]

end AKMM.RealBusinessCycles
