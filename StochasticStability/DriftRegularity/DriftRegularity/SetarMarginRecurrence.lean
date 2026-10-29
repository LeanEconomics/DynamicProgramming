/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DriftRegularity.DriftExamples

/-!
# Recurrence of the SETAR model on its margins (MT §11.5.2, Proposition 11.5.4)

Meyn and Tweedie, §11.5.2, pp. 280–283. Under (SETAR1)–(SETAR3) (zero-mean noise with densities
positive on `ℝ`, and finite variances in the two end regimes) the SETAR model is recurrent on
each margin (11.45)–(11.49) of its parameter space. The book proves (11.45) with `θ(1) ≥ 0`,
(11.45) with `θ(1) < 0` (with a misprinted slope, see below), (11.47) and (11.49), and leaves
(11.46) and (11.48) to symmetry; all five are proved here.

**The second-order bound.** The book expands `log(u + ax)` with Lemmas 8.5.2, 8.5.3, 9.4.3 and
9.4.4. Here one lemma does all the cases: `log_hinge_pointwise` and `log_hinge_drift` show that
for `Z` with mean zero, finite variance and `P(Z < 0) > 0`, and for `G ≥ 1` with `G(A) = A` for
large `A` and linear growth, `E log G(z + s + Z) ≤ log z` for large `z` when `s ≤ 0` (the
concavity gain `E[Z²; Z < 0]/(2z²)` beats an `o(z⁻²)` tail).

**The test function** is `V = log L`, `L(y) = max(u + a y, v − b y)` (`marginL`), with
`u, v ≥ 1` so that `V ≥ 0`: this is (11.50) with the two pieces joined by a maximum. Near each end
`L(Y)` is a hinge `G(A) = A + (c₁ − c₂A)⁺` (`hinge`, `marginL_eq_hinge_right`,
`marginL_eq_hinge_left`) of the dominant affine piece.
* `marginL_right_end`: `E log L(φ + θx + W) ≤ log L(x)` for large `x`, for a random-walk end
  (`θ = 1, φ ≤ 0`), a jumping end (`θ < 0`, `a = −bθ`, `v − bφ − u ≤ 0`) and a contracting end
  (`0 ≤ θ < 1`, through `E L(Y) ≤ L(x)` and the tangent line `log_le_tangent`).
* `marginL_left_end`: the same at `−∞`, by reflection (`marginL_neg`).
* `setar_harris_of_ends`: matching end conditions give (V1) off `[−R, R]`, with compact (hence
  petite, Proposition 6.3.6) sublevel sets, so the chain is Harris recurrent (Theorem 9.1.8).

**Proposition 11.5.4** (`proposition_11_5_4`, p. 280): on each of (11.45)–(11.49) the SETAR
model is Harris recurrent, and hence recurrent.

**Hypotheses.** (SETAR3) is used as `E W(1)² < ∞` and `E W(M)² < ∞`. The book's conclusion
"recurrent" is strengthened to Harris recurrent.

**Corrections.** In the region (11.45) with `θ(1) < 0` the book chooses `a = −bθ(M)` and
`v − u = aφ(1)` (p. 282). Since `θ(M) = 1` this makes `a = −b < 0`, and the identity it then
uses, `log(u + ah(x)) = log(v − bx)`, needs `aθ(1) = −b`: the slope must be `a = −b/θ(1)`.
`proposition_11_5_4_slope_correction` proves that `u + a h(x) = v − bx` for all `x` iff
`a = −b/θ(1)` and `v − u = aφ(1)`, and that `a = −bθ(1)` works only when `θ(1) = −1`; the proof
of `proposition_11_5_4` uses `b = 1, a = −1/θ(1)`. The book's choice for (11.49),
`b = −aθ(1) = −a/θ(M)`, is correct.
-/

namespace MeynTweedie.DriftRegularity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-! ### The second-order bound for `log` -/

/-- **Pointwise second-order bound.** Let `G ≥ 1` with `G(A) = A` for `A ≥ T₀` and
`G(A) ≤ c|A| + d`. For `s ≤ 0`, `z ≥ 1` and `z ≥ 2(T₀ − s)`, with `K = 3c + 2c|s| + 2d`,
`log G(z + s + Z) − log z ≤ Z/z + (C Z² 1{Z < −z/2} − Z² 1{Z < 0}/2)/z²`, `C = 2K + 3`. -/
theorem log_hinge_pointwise {G : ℝ → ℝ} (hG1 : ∀ A, 1 ≤ G A) {T₀ : ℝ}
    (hGT : ∀ A, T₀ ≤ A → G A = A) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hGc : ∀ A, G A ≤ c * |A| + d) {s z : ℝ} (hs : s ≤ 0) (hz1 : 1 ≤ z)
    (hzT : 2 * (T₀ - s) ≤ z) (Z : ℝ) :
    Real.log (G (z + s + Z)) - Real.log z ≤ Z / z +
      ((2 * (3 * c + 2 * c * |s| + 2 * d) + 3) * (Iio (-(z / 2))).indicator (fun t => t ^ 2) Z -
        (Iio 0).indicator (fun t => t ^ 2) Z / 2) / z ^ 2 := by
  have hz0 : 0 < z := by linarith
  set K := 3 * c + 2 * c * |s| + 2 * d with hK
  have hK0 : 0 ≤ K := by positivity
  by_cases hZ : Z < -(z / 2)
  · have hZneg : Z < 0 := by linarith
    have hZabs : |Z| = -Z := abs_of_neg hZneg
    have hGpos : 0 < G (z + s + Z) := by linarith [hG1 (z + s + Z)]
    have hGle : G (z + s + Z) ≤ K * |Z| := by
      have h1 := hGc (z + s + Z)
      have h2 : |z + s + Z| ≤ z + |s| + |Z| := by
        calc |z + s + Z| ≤ |z + s| + |Z| := abs_add_le _ _
          _ ≤ |z| + |s| + |Z| := by linarith [abs_add_le z s]
          _ = z + |s| + |Z| := by rw [abs_of_pos hz0]
      have hzZ : z ≤ 2 * |Z| := by rw [hZabs]; linarith
      have h3 : |s| ≤ 2 * |s| * |Z| := by
        have := mul_le_mul_of_nonneg_left (hz1.trans hzZ) (abs_nonneg s)
        linarith
      have h4 : d ≤ 2 * d * |Z| := by
        have := mul_le_mul_of_nonneg_left (hz1.trans hzZ) hd
        linarith
      have h5 : c * |z + s + Z| ≤ c * (z + |s| + |Z|) := mul_le_mul_of_nonneg_left h2 hc
      have h6 : c * z ≤ c * (2 * |Z|) := mul_le_mul_of_nonneg_left hzZ hc
      have h7 : c * |s| ≤ c * (2 * |s| * |Z|) := mul_le_mul_of_nonneg_left h3 hc
      have e : K * |Z| = 3 * c * |Z| + 2 * (c * |s|) * |Z| + 2 * d * |Z| := by rw [hK]; ring
      nlinarith
    have hlog : Real.log (G (z + s + Z)) - Real.log z ≤ K * |Z| / z := by
      rw [← Real.log_div hGpos.ne' hz0.ne']
      calc Real.log (G (z + s + Z) / z) ≤ G (z + s + Z) / z - 1 :=
            Real.log_le_sub_one_of_pos (div_pos hGpos hz0)
        _ ≤ K * |Z| / z := by
            have := div_le_div_of_nonneg_right hGle hz0.le
            linarith
    rw [indicator_of_mem (show Z ∈ Iio (-(z / 2)) from hZ),
      indicator_of_mem (show Z ∈ Iio (0 : ℝ) from hZneg)]
    refine hlog.trans ?_
    have hZ2 : |Z| * z ≤ 2 * Z ^ 2 := by
      have hsq : Z ^ 2 = |Z| * |Z| := by rw [← sq_abs]; ring
      have hzZ : z ≤ 2 * |Z| := by rw [hZabs]; linarith
      have := mul_le_mul_of_nonneg_left hzZ (abs_nonneg Z)
      linarith
    have e1 : K * |Z| / z = K * |Z| * z / z ^ 2 := by field_simp
    have e2 : Z / z + ((2 * K + 3) * Z ^ 2 - Z ^ 2 / 2) / z ^ 2 =
        (Z * z + ((2 * K + 3) * Z ^ 2 - Z ^ 2 / 2)) / z ^ 2 := by field_simp
    rw [e1, e2]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h8 := mul_le_mul_of_nonneg_left hZ2 (by linarith : (0 : ℝ) ≤ K + 1)
    have h9 : Z * z = -(|Z| * z) := by rw [hZabs]; ring
    nlinarith [sq_nonneg Z]
  · have hZ' : -(z / 2) ≤ Z := not_lt.1 hZ
    rw [indicator_of_notMem (show Z ∉ Iio (-(z / 2)) from hZ), mul_zero, zero_sub]
    have hA : T₀ ≤ z + s + Z := by linarith
    rw [hGT _ hA]
    have hA1 : 1 ≤ z + s + Z := by have := hG1 (z + s + Z); rwa [hGT _ hA] at this
    have hu : -1 < Z / z := by
      rw [lt_div_iff₀ hz0]; linarith
    have hlog1 : Real.log (z + s + Z) ≤ Real.log (z + Z) :=
      Real.log_le_log (by linarith) (by linarith)
    have hzZ : z + Z = z * (1 + Z / z) := by field_simp
    have hlog2 : Real.log (z + Z) = Real.log z + Real.log (1 + Z / z) := by
      rw [hzZ, Real.log_mul hz0.ne' (by linarith)]
    have h3 := log_one_add_le hu
    have hind : (Z / z) ^ 2 / 2 * (if Z / z < 0 then 1 else 0) =
        (Iio 0).indicator (fun t => t ^ 2) Z / 2 / z ^ 2 := by
      by_cases hZ0 : Z < 0
      · have : Z / z < 0 := div_neg_of_neg_of_pos hZ0 hz0
        simp only [this, ↓reduceIte]
        rw [indicator_of_mem (show Z ∈ Iio (0 : ℝ) from hZ0)]
        field_simp
      · have : ¬ Z / z < 0 := fun h => hZ0 ((div_neg_iff.1 h).elim (fun h' => by linarith [h'.1])
          fun h' => h'.1)
        simp only [this, ↓reduceIte]
        rw [indicator_of_notMem (show Z ∉ Iio (0 : ℝ) from hZ0)]
        simp
    rw [neg_div, ← sub_eq_add_neg]
    calc Real.log (z + s + Z) - Real.log z ≤ Real.log (1 + Z / z) := by linarith
      _ ≤ Z / z - (Z / z) ^ 2 / 2 * (if Z / z < 0 then 1 else 0) := h3
      _ = Z / z - (Iio 0).indicator (fun t => t ^ 2) Z / 2 / z ^ 2 := by rw [hind]

/-- **The second-order drift lemma** (the role of Lemmas 8.5.2, 8.5.3, 9.4.3 and 9.4.4 in the
proof of Proposition 11.5.4, MT pp. 280–283). Let `Z` have law `Γ` with `E Z = 0`, `E Z² < ∞`
and `P(Z < 0) > 0`, and let `G ≥ 1` be measurable with `G(A) = A` for `A ≥ T₀` and
`G(A) ≤ c|A| + d`. For `s ≤ 0`, `E log G(z + s + Z) ≤ log z` for all large `z`: the concavity of
`log` gains `E[Z²; Z < 0]/(2z²)`, which beats the `o(z⁻²)` contribution of `{Z < −z/2}`. -/
theorem log_hinge_drift (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hW0 : ∫ w, w ∂Γ = 0)
    (hW2 : Integrable (fun w => w ^ 2) Γ) (hneg : 0 < Γ (Iio 0))
    {G : ℝ → ℝ} (hGm : Measurable G) (hG1 : ∀ A, 1 ≤ G A) {T₀ : ℝ}
    (hGT : ∀ A, T₀ ≤ A → G A = A) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hGc : ∀ A, G A ≤ c * |A| + d) {s : ℝ} (hs : s ≤ 0) :
    ∃ Z₀, ∀ z, Z₀ ≤ z → ∫ w, Real.log (G (z + s + w)) ∂Γ ≤ Real.log z := by
  set C := 2 * (3 * c + 2 * c * |s| + 2 * d) + 3 with hC
  have hC0 : 0 < C := by positivity
  set q := ∫ w in Iio 0, w ^ 2 ∂Γ with hq
  have hq0 : 0 < q := by
    rw [hq, setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun w => sq_nonneg w) hW2.integrableOn]
    have : Function.support (fun w : ℝ => w ^ 2) ∩ Iio 0 = Iio 0 := by
      ext w
      simp only [mem_inter_iff, Function.mem_support, mem_Iio]
      exact ⟨fun h => h.2, fun h => ⟨pow_ne_zero 2 h.ne, h⟩⟩
    rwa [this]
  have ht : Tendsto (fun z => ∫ w in Iio (-(z / 2)), w ^ 2 ∂Γ) atTop (𝓝 0) :=
    tendsto_setIntegral_zero Γ hW2 (fun _ => measurableSet_Iio) fun w =>
      eventually_atTop.2 ⟨-2 * w, fun z hz => by simp only [mem_Iio, not_lt]; linarith⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 ht).2 (q / (2 * C)) (by positivity))
  refine ⟨max N (max 1 (2 * (T₀ - s))), fun z hz => ?_⟩
  have hzN : N ≤ z := (le_max_left _ _).trans hz
  have hz1 : 1 ≤ z := ((le_max_left _ _).trans (le_max_right _ _)).trans hz
  have hzT : 2 * (T₀ - s) ≤ z := ((le_max_right _ _).trans (le_max_right _ _)).trans hz
  have htz := hN z hzN
  have hLi : Integrable (fun w => Real.log (G (z + s + w))) Γ := by
    refine Integrable.mono' ((integrable_const (c * |z + s| + d)).add (hW.abs.const_mul c))
      (Real.measurable_log.comp (hGm.comp (measurable_const_add (z + s)))).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    have h1 := hG1 (z + s + w)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1)]
    simp only [Pi.add_apply]
    have h2 := mul_le_mul_of_nonneg_left (abs_add_le (z + s) w) hc
    calc Real.log (G (z + s + w)) ≤ G (z + s + w) - 1 := Real.log_le_sub_one_of_pos (by linarith)
      _ ≤ c * |z + s + w| + d := by linarith [hGc (z + s + w)]
      _ ≤ c * |z + s| + d + c * |w| := by linarith
  set g : ℝ → ℝ := fun w => w / z + (C * (Iio (-(z / 2))).indicator (fun t => t ^ 2) w -
    (Iio 0).indicator (fun t => t ^ 2) w / 2) / z ^ 2 with hg
  have hI1 : Integrable (fun w => (Iio (-(z / 2))).indicator (fun t => t ^ 2) w) Γ :=
    hW2.indicator measurableSet_Iio
  have hI2 : Integrable (fun w => (Iio (0 : ℝ)).indicator (fun t => t ^ 2) w) Γ :=
    hW2.indicator measurableSet_Iio
  have hI3 : Integrable (fun w => (C * (Iio (-(z / 2))).indicator (fun t => t ^ 2) w -
      (Iio 0).indicator (fun t => t ^ 2) w / 2) / z ^ 2) Γ :=
    ((hI1.const_mul C).sub (hI2.div_const 2)).div_const _
  have hgi : Integrable g Γ := (hW.div_const z).add hI3
  have hgint : ∫ w, g w ∂Γ = (C * ∫ w in Iio (-(z / 2)), w ^ 2 ∂Γ - q / 2) / z ^ 2 := by
    rw [hg, integral_add (hW.div_const z) hI3, integral_div, hW0, zero_div, zero_add,
      integral_div, integral_sub (hI1.const_mul C) (hI2.div_const 2), integral_const_mul,
      integral_div, integral_indicator measurableSet_Iio, integral_indicator measurableSet_Iio]
  have hpt : ∀ w, Real.log (G (z + s + w)) - Real.log z ≤ g w := fun w =>
    log_hinge_pointwise hG1 hGT hc hd hGc hs hz1 hzT w
  have hle : ∫ w, (Real.log (G (z + s + w)) - Real.log z) ∂Γ ≤ ∫ w, g w ∂Γ :=
    integral_mono (hLi.sub (integrable_const _)) hgi hpt
  rw [integral_sub hLi (integrable_const _), integral_const, probReal_univ, one_smul,
    hgint] at hle
  have hneg' : (C * ∫ w in Iio (-(z / 2)), w ^ 2 ∂Γ - q / 2) / z ^ 2 ≤ 0 := by
    refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
    have h1 := mul_lt_mul_of_pos_left htz hC0
    have e : C * (q / (2 * C)) = q / 2 := by field_simp
    linarith
  linarith

/-! ### The test function `log max(u + a y, v − b y)` -/

/-- The test function of Proposition 11.5.4 is `V = log L` with `L(y) = max(u + a y, v − b y)`:
the book's (11.50), `log(u + ax)` near `+∞` and `log(v − bx)` near `−∞`, with the two pieces
joined by a maximum instead of by `0` on `[−R, R]`. -/
noncomputable def marginL (u a v b y : ℝ) : ℝ := max (u + a * y) (v - b * y)

/-- `L` is measurable. -/
theorem measurable_marginL (u a v b : ℝ) : Measurable (marginL u a v b) :=
  (measurable_const.add (measurable_const.mul measurable_id)).max
    (measurable_const.sub (measurable_const.mul measurable_id))

/-- `L ≥ 1` when `u, v ≥ 1` and `a, b ≥ 0`. -/
theorem one_le_marginL {u a v b : ℝ} (hu : 1 ≤ u) (ha : 0 ≤ a) (hv : 1 ≤ v) (hb : 0 ≤ b)
    (y : ℝ) : 1 ≤ marginL u a v b y := by
  unfold marginL
  rcases le_total 0 y with h | h
  · exact le_max_of_le_left (by nlinarith)
  · exact le_max_of_le_right (by nlinarith)

/-- `L(y) ≤ |u| + |v| + (a + b)|y|`. -/
theorem marginL_le {u a v b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (y : ℝ) :
    marginL u a v b y ≤ |u| + |v| + (a + b) * |y| := by
  unfold marginL
  have h1 := mul_le_mul_of_nonneg_left (le_abs_self y) ha
  have h2 := mul_le_mul_of_nonneg_left (neg_abs_le y) hb
  have h3 : 0 ≤ b * |y| := by positivity
  have h4 : 0 ≤ a * |y| := by positivity
  refine max_le ?_ ?_
  · linarith [le_abs_self u, abs_nonneg v]
  · linarith [le_abs_self v, abs_nonneg u]

/-- Reflection: `L_{u,a,v,b}(y) = L_{v,b,u,a}(−y)`. -/
theorem marginL_neg (u a v b y : ℝ) : marginL u a v b y = marginL v b u a (-y) := by
  unfold marginL
  rw [max_comm]
  congr 1 <;> ring

/-- The hinge `G(A) = A + (c₁ − c₂A)⁺`. -/
noncomputable def hinge (c₁ c₂ A : ℝ) : ℝ := A + max (c₁ - c₂ * A) 0

/-- `G` is measurable. -/
theorem measurable_hinge (c₁ c₂ : ℝ) : Measurable (hinge c₁ c₂) :=
  measurable_id.add ((measurable_const.sub (measurable_const.mul measurable_id)).max
    measurable_const)

/-- `G(A) = A` for `A ≥ c₁/c₂`. -/
theorem hinge_of_le {c₁ c₂ A : ℝ} (hc₂ : 0 < c₂) (hA : c₁ / c₂ ≤ A) : hinge c₁ c₂ A = A := by
  rw [div_le_iff₀ hc₂] at hA
  rw [hinge, max_eq_right (by linarith), add_zero]

/-- `G(A) ≤ (1 + c₂)|A| + |c₁|`. -/
theorem hinge_le {c₁ c₂ : ℝ} (hc₂ : 0 ≤ c₂) (A : ℝ) : hinge c₁ c₂ A ≤ (1 + c₂) * |A| + |c₁| := by
  unfold hinge
  have h1 := mul_le_mul_of_nonneg_left (neg_abs_le A) hc₂
  have h2 : 0 ≤ c₂ * |A| := by positivity
  refine (add_le_add (le_abs_self A) (max_le (?_ : c₁ - c₂ * A ≤ |c₁| + c₂ * |A|)
    (by positivity))).trans (by linarith)
  linarith [le_abs_self c₁]

/-- `max p q = p + (q − p)⁺`. -/
theorem max_eq_add_max_sub (p q : ℝ) : max p q = p + max (q - p) 0 := by
  rcases le_total p q with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- Near `+∞`: `L(y) = G(u + a y)` with `c₁ = v + bu/a`, `c₂ = 1 + b/a`. -/
theorem marginL_eq_hinge_right {u a v b : ℝ} (ha : a ≠ 0) (y : ℝ) :
    marginL u a v b y = hinge (v + b * u / a) (1 + b / a) (u + a * y) := by
  rw [marginL, hinge, max_eq_add_max_sub]
  congr 2
  field_simp
  ring

/-- Near `−∞`: `L(y) = G(v − b y)` with `c₁ = u + av/b`, `c₂ = 1 + a/b`. -/
theorem marginL_eq_hinge_left {u a v b : ℝ} (hb : b ≠ 0) (y : ℝ) :
    marginL u a v b y = hinge (u + a * v / b) (1 + a / b) (v - b * y) := by
  rw [marginL_neg, marginL_eq_hinge_right hb]
  congr 1
  ring

/-- `G(A) ≥ 1` for the hinge of `L` near `+∞`. -/
theorem one_le_hinge_right {u a v b : ℝ} (hu : 1 ≤ u) (ha : 0 < a) (hv : 1 ≤ v) (hb : 0 ≤ b)
    (A : ℝ) : 1 ≤ hinge (v + b * u / a) (1 + b / a) A := by
  have h := one_le_marginL hu ha.le hv hb ((A - u) / a)
  rw [marginL_eq_hinge_right ha.ne'] at h
  rwa [show u + a * ((A - u) / a) = A by field_simp; ring] at h

/-- `G(A) ≥ 1` for the hinge of `L` near `−∞`. -/
theorem one_le_hinge_left {u a v b : ℝ} (hu : 1 ≤ u) (ha : 0 ≤ a) (hv : 1 ≤ v) (hb : 0 < b)
    (A : ℝ) : 1 ≤ hinge (u + a * v / b) (1 + a / b) A := by
  have h := one_le_marginL hu ha hv hb.le ((v - A) / b)
  rw [marginL_eq_hinge_left hb.ne'] at h
  rwa [show v - b * ((v - A) / b) = A by field_simp; ring] at h

/-- `log y ≤ log z + y/z − 1` for `y, z > 0` (the tangent line of `log` at `z`). -/
theorem log_le_tangent {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    Real.log y ≤ Real.log z + y / z - 1 := by
  have := Real.log_le_sub_one_of_pos (div_pos hy hz)
  rw [Real.log_div hy.ne' hz.ne'] at this
  linarith

/-! ### The noise `βW` -/

/-- A function bounded by `α + β|w|` is integrable when `W` is. -/
theorem integrable_of_abs_le_affine (Γ : Measure ℝ) [IsFiniteMeasure Γ]
    (hW : Integrable (fun w => w) Γ) {f : ℝ → ℝ} (hf : Measurable f) {α β : ℝ}
    (h : ∀ w, |f w| ≤ α + β * |w|) : Integrable f Γ :=
  Integrable.mono' ((integrable_const α).add (hW.abs.const_mul β)) hf.aestronglyMeasurable
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact h w)

/-- The law of `βW` is a probability with mean zero and finite variance when `W`'s is. -/
theorem map_mul_noise (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hW0 : ∫ w, w ∂Γ = 0)
    (hW2 : Integrable (fun w => w ^ 2) Γ) (β : ℝ) :
    IsProbabilityMeasure (Γ.map (β * ·)) ∧ Integrable (fun w => w) (Γ.map (β * ·)) ∧
      ∫ w, w ∂(Γ.map (β * ·)) = 0 ∧ Integrable (fun w => w ^ 2) (Γ.map (β * ·)) := by
  have hm : Measurable (fun x : ℝ => β * x) := measurable_id.const_mul β
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance,
    (integrable_map_measure (g := fun w : ℝ => w) measurable_id.aestronglyMeasurable
      hm.aemeasurable).2 (hW.const_mul β), ?_,
    (integrable_map_measure (g := fun w : ℝ => w ^ 2)
      (measurable_id.pow_const 2).aestronglyMeasurable hm.aemeasurable).2 ?_⟩
  · rw [integral_map (f := fun w : ℝ => w) hm.aemeasurable measurable_id.aestronglyMeasurable,
      integral_const_mul, hW0, mul_zero]
  · have : (fun w : ℝ => w ^ 2) ∘ (fun x : ℝ => β * x) = fun w => β ^ 2 * w ^ 2 := by
      ext w; simp only [Function.comp_apply]; ring
    rw [this]
    exact hW2.const_mul _

/-- `P(βW < 0) > 0` when both `P(W < 0)` and `P(W > 0)` are positive and `β ≠ 0`. -/
theorem map_mul_Iio_pos (Γ : Measure ℝ) {β : ℝ} (hβ : β ≠ 0) (hneg : 0 < Γ (Iio 0))
    (hpos : 0 < Γ (Ioi 0)) : 0 < Γ.map (β * ·) (Iio 0) := by
  have hm : Measurable (fun x : ℝ => β * x) := measurable_id.const_mul β
  rw [Measure.map_apply hm measurableSet_Iio]
  rcases lt_or_gt_of_ne hβ with h | h
  · exact hpos.trans_le (measure_mono fun w (hw : 0 < w) =>
      (mul_neg_of_neg_of_pos h hw : β * w < 0))
  · exact hneg.trans_le (measure_mono fun w (hw : w < 0) =>
      (mul_neg_of_pos_of_neg h hw : β * w < 0))

/-- `|L(c + w)| ≤ (|u| + |v| + (a + b)|c|) + (a + b)|w|`. -/
theorem abs_marginL_add_le {u a v b : ℝ} (hu : 1 ≤ u) (ha : 0 ≤ a) (hv : 1 ≤ v) (hb : 0 ≤ b)
    (c w : ℝ) :
    |marginL u a v b (c + w)| ≤ (|u| + |v| + (a + b) * |c|) + (a + b) * |w| := by
  rw [abs_of_nonneg (by linarith [one_le_marginL hu ha hv hb (c + w)])]
  have := mul_le_mul_of_nonneg_left (abs_add_le c w) (by linarith : (0 : ℝ) ≤ a + b)
  linarith [marginL_le (u := u) (v := v) ha hb (c + w)]

/-- `|log L(c + w)| ≤ (|u| + |v| + (a + b)|c|) + (a + b)|w|`. -/
theorem abs_log_marginL_add_le {u a v b : ℝ} (hu : 1 ≤ u) (ha : 0 ≤ a) (hv : 1 ≤ v)
    (hb : 0 ≤ b) (c w : ℝ) :
    |Real.log (marginL u a v b (c + w))| ≤ (|u| + |v| + (a + b) * |c|) + (a + b) * |w| := by
  have h1 := one_le_marginL hu ha hv hb (c + w)
  rw [abs_of_nonneg (Real.log_nonneg h1)]
  have h2 := Real.log_le_sub_one_of_pos (by linarith : 0 < marginL u a v b (c + w))
  have h3 := abs_marginL_add_le hu ha hv hb c w
  rw [abs_of_nonneg (by linarith)] at h3
  linarith

/-! ### The drift at the two ends -/

/-- **The drift of `log L` at `+∞`** (proof of Proposition 11.5.4, (11.53), (11.58) and the
contracting case). For noise `W` with mean zero, finite variance and `P(W < 0), P(W > 0) > 0`,
`E log L(φ + θx + W) ≤ log L(x)` for all large `x`, in each of three cases: a random-walk end
`θ = 1, φ ≤ 0` (`L(Y) = G(L(x) + aφ + aW)` and `log_hinge_drift`); a jumping end `θ < 0` with
`a = −bθ` and `v − bφ − u ≤ 0` (`L(Y) = G'(L(x) + v − bφ − u − bW)`); and a contracting end
`0 ≤ θ < 1` (`E L(Y) ≤ L(x)` and the tangent line of `log`). -/
theorem marginL_right_end (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hW0 : ∫ w, w ∂Γ = 0)
    (hW2 : Integrable (fun w => w ^ 2) Γ) (hneg : 0 < Γ (Iio 0)) (hpos : 0 < Γ (Ioi 0))
    {u a v b : ℝ} (hu : 1 ≤ u) (ha : 0 < a) (hv : 1 ≤ v) (hb : 0 < b) {φ θ : ℝ}
    (hend : (θ = 1 ∧ φ ≤ 0) ∨ (θ < 0 ∧ a = -b * θ ∧ v - b * φ - u ≤ 0) ∨ (0 ≤ θ ∧ θ < 1)) :
    ∃ R, ∀ x, R < x → ∫ w, Real.log (marginL u a v b (φ + θ * x + w)) ∂Γ ≤
      Real.log (marginL u a v b x) := by
  have hL : ∀ x, (v - u) / (a + b) ≤ x → marginL u a v b x = u + a * x := fun x hx => by
    rw [div_le_iff₀ (by linarith)] at hx
    exact max_eq_left (by linarith)
  rcases hend with ⟨hθ, hφ⟩ | ⟨hθ, hab, hs⟩ | ⟨hθ0, hθ1⟩
  · -- a random-walk end
    obtain ⟨hP, hWa, hWa0, hWa2⟩ := map_mul_noise Γ hW hW0 hW2 a
    have hc₂ : 0 < 1 + b / a := by positivity
    obtain ⟨Z₀, hZ₀⟩ := log_hinge_drift (Γ.map (a * ·)) hWa hWa0 hWa2
      (map_mul_Iio_pos Γ ha.ne' hneg hpos) (measurable_hinge _ _)
      (one_le_hinge_right hu ha hv hb.le) (fun A hA => hinge_of_le hc₂ hA)
      (by positivity : (0 : ℝ) ≤ 1 + (1 + b / a)) (abs_nonneg _) (hinge_le hc₂.le)
      (mul_nonpos_of_nonneg_of_nonpos ha.le hφ : a * φ ≤ 0)
    refine ⟨max ((v - u) / (a + b)) ((Z₀ - u) / a), fun x hx => ?_⟩
    have hx1 : (v - u) / (a + b) ≤ x := (le_max_left _ _).trans hx.le
    have hx2 : Z₀ ≤ u + a * x := by
      have := (le_max_right _ _).trans hx.le
      rw [div_le_iff₀ ha] at this
      linarith
    rw [hL x hx1]
    refine le_trans (le_of_eq ?_) (hZ₀ _ hx2)
    have hm : Measurable (fun t : ℝ => a * t) := measurable_id.const_mul a
    rw [integral_map (f := fun t => Real.log (hinge (v + b * u / a) (1 + b / a)
      (u + a * x + a * φ + t))) hm.aemeasurable
      (Real.measurable_log.comp ((measurable_hinge _ _).comp
        (measurable_const_add _))).aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only
    rw [marginL_eq_hinge_right ha.ne', hθ]
    congr 2
    ring
  · -- a jumping end
    obtain ⟨hP, hWa, hWa0, hWa2⟩ := map_mul_noise Γ hW hW0 hW2 (-b)
    have hc₂ : 0 < 1 + a / b := by positivity
    obtain ⟨Z₀, hZ₀⟩ := log_hinge_drift (Γ.map ((-b) * ·)) hWa hWa0 hWa2
      (map_mul_Iio_pos Γ (neg_ne_zero.2 hb.ne') hneg hpos) (measurable_hinge _ _)
      (one_le_hinge_left hu ha.le hv hb) (fun A hA => hinge_of_le hc₂ hA)
      (by positivity : (0 : ℝ) ≤ 1 + (1 + a / b)) (abs_nonneg _) (hinge_le hc₂.le) hs
    refine ⟨max ((v - u) / (a + b)) ((Z₀ - u) / a), fun x hx => ?_⟩
    have hx1 : (v - u) / (a + b) ≤ x := (le_max_left _ _).trans hx.le
    have hx2 : Z₀ ≤ u + a * x := by
      have := (le_max_right _ _).trans hx.le
      rw [div_le_iff₀ ha] at this
      linarith
    rw [hL x hx1]
    refine le_trans (le_of_eq ?_) (hZ₀ _ hx2)
    have hm : Measurable (fun t : ℝ => -b * t) := measurable_id.const_mul (-b)
    rw [integral_map (f := fun t => Real.log (hinge (u + a * v / b) (1 + a / b)
      (u + a * x + (v - b * φ - u) + t))) hm.aemeasurable
      (Real.measurable_log.comp ((measurable_hinge _ _).comp
        (measurable_const_add _))).aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only
    rw [marginL_eq_hinge_left hb.ne']
    have e : v - b * (φ + θ * x + w) = u + a * x + (v - b * φ - u) + -b * w := by
      rw [hab]; ring
    rw [e]
  · -- a contracting end
    have hab0 : 0 ≤ a + b := by linarith
    set K' := ∫ w, max (v - u - (a + b) * (φ + w)) 0 ∂Γ with hK'
    have hKm : Measurable fun w : ℝ => max (v - u - (a + b) * (φ + w)) 0 :=
      (measurable_const.sub (measurable_const.mul (measurable_const_add φ))).max
        measurable_const
    have hKi : Integrable (fun w => max (v - u - (a + b) * (φ + w)) 0) Γ :=
      integrable_of_abs_le_affine Γ hW hKm (α := |v - u - (a + b) * φ|) (β := a + b)
        fun w => by
          rw [abs_of_nonneg (le_max_right _ _)]
          refine max_le ?_ (by positivity)
          have e : v - u - (a + b) * (φ + w) = (v - u - (a + b) * φ) + -((a + b) * w) := by
            ring
          rw [e]
          have h1 := mul_le_mul_of_nonneg_left (neg_abs_le w) hab0
          linarith [le_abs_self (v - u - (a + b) * φ)]
    have hθ1' : 0 < a * (1 - θ) := mul_pos ha (by linarith)
    refine ⟨max (max ((v - u) / (a + b)) 0) ((a * φ + K') / (a * (1 - θ))), fun x hx => ?_⟩
    have hx1 : (v - u) / (a + b) ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx.le
    have hx0 : 0 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx.le
    have hx3 : a * φ + K' ≤ a * (1 - θ) * x := by
      have := (le_max_right _ _).trans hx.le
      rwa [div_le_iff₀ hθ1', mul_comm x] at this
    rw [hL x hx1]
    have hz : 0 < u + a * x := by nlinarith
    have hY : ∀ w, marginL u a v b (φ + θ * x + w) ≤
        (u + a * φ + a * θ * x) + a * w + max (v - u - (a + b) * (φ + w)) 0 := fun w => by
      rw [marginL, max_eq_add_max_sub]
      have hθx : 0 ≤ (a + b) * (θ * x) := mul_nonneg hab0 (mul_nonneg hθ0 hx0)
      have e1 : u + a * (φ + θ * x + w) = (u + a * φ + a * θ * x) + a * w := by ring
      have e2 : v - b * (φ + θ * x + w) - (u + a * (φ + θ * x + w)) =
          v - u - (a + b) * (φ + w) - (a + b) * (θ * x) := by ring
      rw [e2, e1]
      exact add_le_add le_rfl (max_le_max (by linarith) le_rfl)
    have hLi : Integrable (fun w => marginL u a v b (φ + θ * x + w)) Γ :=
      integrable_of_abs_le_affine Γ hW ((measurable_marginL u a v b).comp
        (measurable_const_add _)) (abs_marginL_add_le hu ha.le hv hb.le (φ + θ * x))
    have hlogi : Integrable (fun w => Real.log (marginL u a v b (φ + θ * x + w))) Γ :=
      integrable_of_abs_le_affine Γ hW (Real.measurable_log.comp
        ((measurable_marginL u a v b).comp (measurable_const_add _)))
        (abs_log_marginL_add_le hu ha.le hv hb.le (φ + θ * x))
    have hhi : Integrable (fun w => (u + a * φ + a * θ * x) + a * w +
        max (v - u - (a + b) * (φ + w)) 0) Γ :=
      ((integrable_const _).add (hW.const_mul a)).add hKi
    have hint_h : ∫ w, ((u + a * φ + a * θ * x) + a * w +
        max (v - u - (a + b) * (φ + w)) 0) ∂Γ = (u + a * φ + a * θ * x) + K' := by
      rw [integral_add (f := fun w => (u + a * φ + a * θ * x) + a * w)
        (g := fun w => max (v - u - (a + b) * (φ + w)) 0)
        ((integrable_const _).add (hW.const_mul a)) hKi,
        integral_affine_zeroMean Γ hW hW0]
    have hEL : ∫ w, marginL u a v b (φ + θ * x + w) ∂Γ ≤ u + a * x := by
      calc ∫ w, marginL u a v b (φ + θ * x + w) ∂Γ ≤ (u + a * φ + a * θ * x) + K' := by
            rw [← hint_h]; exact integral_mono hLi hhi hY
        _ ≤ u + a * x := by nlinarith
    calc ∫ w, Real.log (marginL u a v b (φ + θ * x + w)) ∂Γ
        ≤ ∫ w, ((Real.log (u + a * x) - 1) + marginL u a v b (φ + θ * x + w) / (u + a * x))
          ∂Γ := integral_mono hlogi ((integrable_const _).add (hLi.div_const _)) fun w => by
            have h1 := one_le_marginL hu ha.le hv hb.le (φ + θ * x + w)
            have := log_le_tangent (by linarith) hz
            simp only
            linarith
      _ = (Real.log (u + a * x) - 1) + (∫ w, marginL u a v b (φ + θ * x + w) ∂Γ) /
          (u + a * x) := by
          rw [integral_add (integrable_const _) (hLi.div_const _), integral_const, integral_div,
            probReal_univ, one_smul]
      _ ≤ Real.log (u + a * x) := by
          have : (∫ w, marginL u a v b (φ + θ * x + w) ∂Γ) / (u + a * x) ≤ 1 :=
            (div_le_one hz).2 hEL
          linarith

/-- **The drift of `log L` at `−∞`**, by reflection from `marginL_right_end`: in each of the
cases `θ = 1, φ ≥ 0`; `θ < 0` with `b = −aθ` and `u + aφ − v ≤ 0`; and `0 ≤ θ < 1`,
`E log L(φ + θx + W) ≤ log L(x)` for all `x` near `−∞`. -/
theorem marginL_left_end (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hW0 : ∫ w, w ∂Γ = 0)
    (hW2 : Integrable (fun w => w ^ 2) Γ) (hneg : 0 < Γ (Iio 0)) (hpos : 0 < Γ (Ioi 0))
    {u a v b : ℝ} (hu : 1 ≤ u) (ha : 0 < a) (hv : 1 ≤ v) (hb : 0 < b) {φ θ : ℝ}
    (hend : (θ = 1 ∧ 0 ≤ φ) ∨ (θ < 0 ∧ b = -a * θ ∧ u + a * φ - v ≤ 0) ∨ (0 ≤ θ ∧ θ < 1)) :
    ∃ R, ∀ x, x < -R → ∫ w, Real.log (marginL u a v b (φ + θ * x + w)) ∂Γ ≤
      Real.log (marginL u a v b x) := by
  obtain ⟨hP, hW', hW0', hW2'⟩ := map_mul_noise Γ hW hW0 hW2 (-1)
  have hm : Measurable (fun t : ℝ => -1 * t) := measurable_id.const_mul (-1)
  have hneg' := map_mul_Iio_pos Γ (by norm_num : (-1 : ℝ) ≠ 0) hneg hpos
  have hpos' : 0 < Γ.map ((-1) * ·) (Ioi 0) := by
    rw [Measure.map_apply hm measurableSet_Ioi]
    exact hneg.trans_le (measure_mono fun w (hw : w < 0) => (by
      change (0 : ℝ) < -1 * w
      linarith))
  have hend' : (θ = 1 ∧ -φ ≤ 0) ∨ (θ < 0 ∧ b = -a * θ ∧ u - a * -φ - v ≤ 0) ∨
      (0 ≤ θ ∧ θ < 1) := by
    rcases hend with h | h | h
    · exact Or.inl ⟨h.1, by linarith [h.2]⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.1, by linarith [h.2.2]⟩)
    · exact Or.inr (Or.inr h)
  obtain ⟨R, hR⟩ := marginL_right_end (Γ.map ((-1) * ·)) hW' hW0' hW2' hneg' hpos' hv hb hu ha
    hend'
  refine ⟨R, fun x hx => ?_⟩
  have h := hR (-x) (by linarith)
  rw [integral_map (f := fun t => Real.log (marginL v b u a (-φ + θ * -x + t))) hm.aemeasurable
    (Real.measurable_log.comp ((measurable_marginL v b u a).comp
      (measurable_const_add _))).aestronglyMeasurable, ← marginL_neg] at h
  refine le_trans (le_of_eq ?_) h
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [marginL_neg u a v b]
  congr 2
  ring

/-! ### The SETAR model -/

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **Harris recurrence of the SETAR model from its two ends.** Under (SETAR1)–(SETAR3), if
for some `a, b > 0`, `u, v ≥ 1` the top end is a random walk without upward drift
(`θ(M) = 1, φ(M) ≤ 0`), a jump with `a = −bθ(M)` and `v − bφ(M) − u ≤ 0`, or a contraction
(`0 ≤ θ(M) < 1`), and symmetrically for the bottom end (`θ(1) = 1, φ(1) ≥ 0`; `θ(1) < 0` with
`b = −aθ(1)` and `u + aφ(1) − v ≤ 0`; or `0 ≤ θ(1) < 1`), then `V = log max(u + ax, v − bx)`
satisfies (V1) off a compact interval and the chain is Harris recurrent (Theorem 9.1.8). -/
theorem setar_harris_of_ends (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hW2₀ : Integrable (fun w => w ^ 2) (Γ 0))
    (hW2M : Integrable (fun w => w ^ 2) (Γ (Fin.last m)))
    {u a v b : ℝ} (hu : 1 ≤ u) (ha : 0 < a) (hv : 1 ≤ v) (hb : 0 < b)
    (hM : (θ (Fin.last m) = 1 ∧ φ (Fin.last m) ≤ 0) ∨
      (θ (Fin.last m) < 0 ∧ a = -b * θ (Fin.last m) ∧ v - b * φ (Fin.last m) - u ≤ 0) ∨
      (0 ≤ θ (Fin.last m) ∧ θ (Fin.last m) < 1))
    (h0 : (θ 0 = 1 ∧ 0 ≤ φ 0) ∨ (θ 0 < 0 ∧ b = -a * θ 0 ∧ u + a * φ 0 - v ≤ 0) ∨
      (0 ≤ θ 0 ∧ θ 0 < 1)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsHarris (setarKernel Γ φ θ r) volume := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  obtain ⟨_, hψ, hsmall, -⟩ := proposition_6_3_6 Γ φ θ r h1 h2
  set M := Fin.last m
  have hneg : ∀ j, 0 < Γ j (Iio 0) := fun j => pos_iff_ne_zero.2 fun h => by
    have := h2 j h
    rw [Real.volume_Iio] at this
    exact ENNReal.top_ne_zero this
  have hpos : ∀ j, 0 < Γ j (Ioi 0) := fun j => pos_iff_ne_zero.2 fun h => by
    have := h2 j h
    rw [Real.volume_Ioi] at this
    exact ENNReal.top_ne_zero this
  obtain ⟨R₁, hR₁⟩ := marginL_right_end (Γ M) (hW M) (hW0 M) hW2M (hneg M) (hpos M) hu ha hv hb
    hM
  obtain ⟨R₂, hR₂⟩ := marginL_left_end (Γ 0) (hW 0) (hW0 0) hW2₀ (hneg 0) (hpos 0) hu ha hv hb
    h0
  set T := ∑ i, |r i| with hTdef
  have hTr : ∀ i, |r i| ≤ T := fun i =>
    Finset.single_le_sum (f := fun i => |r i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => abs_nonneg _
  set R := max (max R₁ R₂) (T + 1) with hRdef
  have hRT : T + 1 ≤ R := le_max_right _ _
  have hR1 : R₁ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hR2 : R₂ ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hregM : ∀ x, R < x → setarRegime r x = M := fun x hx =>
    setarRegime_of_gt r fun i => by linarith [le_abs_self (r i), hTr i]
  have hreg0 : ∀ x, x < -R → setarRegime r x = 0 := fun x hx =>
    setarRegime_of_le r fun i => by linarith [neg_abs_le (r i), hTr i]
  have hlogm : Measurable fun y => Real.log (marginL u a v b y) :=
    Real.measurable_log.comp (measurable_marginL u a v b)
  set V : ℝ → ℝ≥0 := fun y => Real.toNNReal (Real.log (marginL u a v b y)) with hVdef
  have hVm : Measurable V := hlogm.real_toNNReal
  have hpetK : ∀ K : Set ℝ, IsCompact K → IsPetite (setarKernel Γ φ θ r) K := fun K hK =>
    (hsmall K hK).isPetite
  refine theorem_9_1_8 hψ (hpetK (Icc (-R) R) isCompact_Icc) hVm (fun n => ?_) (fun x hx => ?_)
  · refine (hpetK (Icc (-(Real.exp n / b)) (Real.exp n / a)) isCompact_Icc).subset
      (measurableSet_le hVm measurable_const) fun y hy => ?_
    have hy' : V y ≤ n := hy
    have hlog : Real.log (marginL u a v b y) ≤ n := by
      have := Real.toNNReal_le_iff_le_coe.1 hy'
      simpa using this
    have h1 := one_le_marginL hu ha.le hv hb.le y
    have hL : marginL u a v b y ≤ Real.exp n :=
      calc marginL u a v b y = Real.exp (Real.log (marginL u a v b y)) :=
            (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp n := Real.exp_le_exp.2 hlog
    have hA : u + a * y ≤ Real.exp n := (le_max_left _ _).trans hL
    have hB : v - b * y ≤ Real.exp n := (le_max_right _ _).trans hL
    constructor
    · rw [neg_le, le_div_iff₀ hb]
      linarith
    · rw [le_div_iff₀ ha]
      linarith
  · rw [drift_nonpos_iff]
    have hxR : R < x ∨ x < -R := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · exact Or.inr h
      · exact Or.inl h
    set j := setarRegime r x with hj
    have hg : Measurable fun w : ℝ => φ j + θ j * x + w := measurable_const_add _
    have hPx := setarKernel_eq_map Γ φ θ r x
    rw [← hj] at hPx
    have hint : Integrable (fun y => Real.log (marginL u a v b y)) (setarKernel Γ φ θ r x) := by
      rw [hPx, integrable_map_measure hlogm.aestronglyMeasurable hg.aemeasurable]
      exact integrable_of_abs_le_affine (Γ j) (hW j) (hlogm.comp hg)
        (abs_log_marginL_add_le hu ha.le hv hb.le (φ j + θ j * x))
    have hnn : ∀ y, 0 ≤ Real.log (marginL u a v b y) := fun y =>
      Real.log_nonneg (one_le_marginL hu ha.le hv hb.le y)
    have hPV : ∫ y, Real.log (marginL u a v b y) ∂setarKernel Γ φ θ r x =
        ∫ w, Real.log (marginL u a v b (φ j + θ j * x + w)) ∂Γ j := by
      rw [hPx, integral_map hg.aemeasurable hlogm.aestronglyMeasurable]
    have hle : ∫ y, Real.log (marginL u a v b y) ∂setarKernel Γ φ θ r x ≤
        Real.log (marginL u a v b x) := by
      rw [hPV]
      rcases hxR with h | h
      · have hjM : j = M := hregM x h
        rw [hjM]
        exact hR₁ x (by linarith)
      · have hj0 : j = 0 := hreg0 x h
        rw [hj0]
        exact hR₂ x (by linarith)
    calc ∫⁻ y, (V y : ℝ≥0∞) ∂setarKernel Γ φ θ r x
        = ∫⁻ y, ENNReal.ofReal (Real.log (marginL u a v b y)) ∂setarKernel Γ φ θ r x := rfl
      _ = ENNReal.ofReal (∫ y, Real.log (marginL u a v b y) ∂setarKernel Γ φ θ r x) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)).symm
      _ ≤ ENNReal.ofReal (Real.log (marginL u a v b x)) := ENNReal.ofReal_le_ofReal hle
      _ = (V x : ℝ≥0∞) := rfl

variable {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **Proposition 11.5.4** (MT p. 280): under (SETAR1)–(SETAR3) the SETAR model is Harris
recurrent, hence recurrent, on each of the margins (11.45)–(11.49) of its parameter space. The
test function is `V = log max(u + ax, v − bx)` with, in (11.45), `a = b = u = v = 1` when
`θ(1) ≥ 0` and `b = 1, a = −1/θ(1), u = 1, v = max(1, 1 + aφ(1))` when `θ(1) < 0`; in (11.46)
the mirror choice; in (11.47) and (11.48) `a = b = u = v = 1`; and in (11.49) `b = 1`,
`a = −θ(M)`, `u = max(1, 1 − φ(M))`, `v = u + φ(M)`. -/
theorem proposition_11_5_4 (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hW2₀ : Integrable (fun w => w ^ 2) (Γ 0))
    (hW2M : Integrable (fun w => w ^ 2) (Γ (Fin.last m)))
    (hreg : (θ 0 < 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) = 0) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) < 1 ∧ φ 0 = 0) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) = 0 ∧ 0 ≤ φ 0) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) < 0 ∧ φ 0 = 0) ∨
      (θ 0 < 0 ∧ θ 0 * θ (Fin.last m) = 1 ∧ φ (Fin.last m) + θ (Fin.last m) * φ 0 = 0)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsHarris (setarKernel Γ φ θ r) volume ∧ IsRecurrentChain (setarKernel Γ φ θ r) volume := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  suffices h : IsHarris (setarKernel Γ φ θ r) volume from ⟨h, h.isRecurrentChain⟩
  have H := @setar_harris_of_ends m Γ _ φ θ r h1 h2 hW hW0 hW2₀ hW2M
  set M := Fin.last m
  rcases hreg with ⟨hθ0, hθM, hφM⟩ | ⟨hθ0, hθM, hφ0⟩ | ⟨hθ0, hθM, hφM, hφ0⟩ |
    ⟨hθ0, hθM, hφM, hφ0⟩ | ⟨hθ0, hθ, hφ⟩
  · -- (11.45)
    rcases le_or_gt 0 (θ 0) with h0 | h0
    · exact H (u := 1) (a := 1) (v := 1) (b := 1) le_rfl one_pos le_rfl one_pos
        (Or.inl ⟨hθM, hφM.le⟩) (Or.inr (Or.inr ⟨h0, hθ0⟩))
    · have ha : 0 < -1 / θ 0 := div_pos_of_neg_of_neg (by norm_num) h0
      refine H (u := 1) (a := -1 / θ 0) (v := max 1 (1 + -1 / θ 0 * φ 0)) (b := 1) le_rfl ha
        (le_max_left _ _) one_pos (Or.inl ⟨hθM, hφM.le⟩) (Or.inr (Or.inl ⟨h0, ?_, ?_⟩))
      · field_simp
        exact (div_self h0.ne).symm
      · linarith [le_max_right 1 (1 + -1 / θ 0 * φ 0)]
  · -- (11.46)
    rcases le_or_gt 0 (θ M) with hM | hM
    · exact H (u := 1) (a := 1) (v := 1) (b := 1) le_rfl one_pos le_rfl one_pos
        (Or.inr (Or.inr ⟨hM, hθM⟩)) (Or.inl ⟨hθ0, hφ0.ge⟩)
    · refine H (u := max 1 (1 - 1 * φ M)) (a := -θ M) (v := 1) (b := 1) (le_max_left _ _)
        (neg_pos.2 hM) le_rfl one_pos (Or.inr (Or.inl ⟨hM, by ring, ?_⟩))
        (Or.inl ⟨hθ0, hφ0.ge⟩)
      linarith [le_max_right 1 (1 - 1 * φ M)]
  · -- (11.47)
    exact H (u := 1) (a := 1) (v := 1) (b := 1) le_rfl one_pos le_rfl one_pos
      (Or.inl ⟨hθM, hφM.le⟩) (Or.inl ⟨hθ0, hφ0⟩)
  · -- (11.48)
    exact H (u := 1) (a := 1) (v := 1) (b := 1) le_rfl one_pos le_rfl one_pos
      (Or.inl ⟨hθM, hφM.le⟩) (Or.inl ⟨hθ0, hφ0.ge⟩)
  · -- (11.49)
    have hM : θ M < 0 := by
      by_contra h
      push Not at h
      nlinarith
    refine H (u := max 1 (1 - φ M)) (a := -θ M) (v := max 1 (1 - φ M) + φ M) (b := 1)
      (le_max_left _ _) (neg_pos.2 hM) (by linarith [le_max_right 1 (1 - φ M)]) one_pos
      (Or.inr (Or.inl ⟨hM, by ring, by linarith⟩)) (Or.inr (Or.inl ⟨hθ0, ?_, ?_⟩))
    · linarith
    · have : -θ M * φ 0 = φ M := by linarith
      linarith

/-- **The slope in the book's test function for (11.45) with `θ(1) < 0`** (MT p. 282). The book
takes `a = −bθ(M)` and `v − u = aφ(1)`. With `θ(M) = 1` this `a = −b` is negative (so
`log(u + ax)` is undefined for large `x`). The identity the proof uses, `u + a h(x) = v − bx` for
every `x` (with `h(x) = φ(1) + θ(1)x`), holds iff `a = −b/θ(1)` and `v − u = aφ(1)`; in
particular the choice `a = −bθ(1)` works only when `θ(1) = −1`. -/
theorem proposition_11_5_4_slope_correction {a b u v φ₁ θ₁ : ℝ} (hb : 0 < b) (hθ₁ : θ₁ < 0) :
    -b * 1 < 0 ∧
      ((∀ x, u + a * (φ₁ + θ₁ * x) = v - b * x) ↔ a = -b / θ₁ ∧ v - u = a * φ₁) ∧
      ((∀ x, u + -b * θ₁ * (φ₁ + θ₁ * x) = v - b * x) → θ₁ = -1) := by
  have hθ₁' : θ₁ ≠ 0 := hθ₁.ne
  refine ⟨by linarith, ⟨fun h => ?_, fun ⟨ha, hv⟩ x => ?_⟩, fun h => ?_⟩
  · have h0 := h 0
    have h1 := h 1
    simp only [mul_zero, add_zero, mul_one, sub_zero] at h0 h1
    refine ⟨?_, by linarith⟩
    rw [eq_div_iff hθ₁']
    linarith
  · rw [ha] at hv ⊢
    have hv' : θ₁ * (v - u) = -b * φ₁ := by rw [hv]; field_simp
    field_simp
    linear_combination -hv'
  · have h0 := h 0
    have h1 := h 1
    simp only [mul_zero, add_zero, mul_one, sub_zero] at h0 h1
    have e : b * ((θ₁ + 1) * (θ₁ - 1)) = 0 := by linarith
    rcases mul_eq_zero.1 e with h' | h'
    · linarith
    · rcases mul_eq_zero.1 h' with h'' | h''
      · linarith
      · linarith

end MeynTweedie.DriftRegularity
