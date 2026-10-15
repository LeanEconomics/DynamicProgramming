/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDP.BoundedPolicy

/-!
# The space `H(S)` of functions homogeneous of degree one in `x`

SLP §9.3, pp. 271–272 (and Exercise 4.7, which the book cites). The endogenous state space is a
cone `X` in a real normed space (`x ∈ X`, `λ ≥ 0` imply `λx ∈ X`). Functions on `S = X × Z` that
are continuous, homogeneous of degree one in `x`, and satisfy `|f(x, z)| ≤ M‖x‖` form `H(S)`
(`InHS`), normed by (2), `‖f‖ = sup_z sup_{‖x‖ = 1} |f(x, z)|` (`hnormS`).

* `abs_le_hnormS`: `|f(x, z)| ≤ ‖f‖‖x‖` on `H(S)`.
* `hnormS_norm`, `hnormS_complete`: `‖·‖` is a norm on `H(S)`, and `H(S)` is complete
  (Exercise 4.7a, with the shock).
* `contraction_HS`: monotone operators on `H(S)` that discount by `γ` in the sense
  `T(f + a‖x‖) ≤ Tf + γa‖x‖` satisfy `‖Tf − Tg‖ ≤ γ‖f − g‖` (Theorem 4.12).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.StochasticDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E}
variable {Z : Type*} [MetricSpace Z]

/-- `X` is a cone. -/
def IsCone (X : Set E) : Prop := ∀ x ∈ X, ∀ a : ℝ, 0 ≤ a → a • x ∈ X

/-- `ax` in the cone `X`, for `a ≥ 0`. -/
def csmul (hX : IsCone X) {a : ℝ} (ha : 0 ≤ a) (x : X) : X := ⟨a • x.1, hX x.1 x.2 a ha⟩

/-- `f : X × Z → ℝ` is in `H(S)`: continuous, homogeneous of degree one in `x`, and
`|f(x, z)| ≤ M‖x‖`. -/
def InHS (hX : IsCone X) (f : X × Z → ℝ) : Prop :=
  Continuous f ∧ (∀ x z (a : ℝ) (ha : 0 ≤ a), f (csmul hX ha x, z) = a * f (x, z)) ∧
    ∃ M, ∀ p : X × Z, |f p| ≤ M * ‖p.1.1‖

/-- The norm (2), p. 272: `‖f‖ = sup_z sup_{‖x‖ = 1} |f(x, z)|`. -/
noncomputable def hnormS (X : Set E) (f : X × Z → ℝ) : ℝ :=
  ⨆ p : {p : X × Z // ‖p.1.1‖ = 1}, |f p.1|

variable {hX : IsCone X}

omit [NormedSpace ℝ E] [MetricSpace Z] in
theorem hnormS_nonneg (f : X × Z → ℝ) : 0 ≤ hnormS X f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

omit [NormedSpace ℝ E] [MetricSpace Z] in
theorem bddAbove_sphereS {f : X × Z → ℝ} {M : ℝ} (hM : ∀ p : X × Z, |f p| ≤ M * ‖p.1.1‖) :
    BddAbove (range fun p : {p : X × Z // ‖p.1.1‖ = 1} => |f p.1|) :=
  ⟨M, by rintro _ ⟨p, rfl⟩; simpa [p.2] using hM p.1⟩

omit [MetricSpace Z] in
/-- On `H(S)`, `|f(x, z)| ≤ ‖f‖‖x‖`. -/
theorem abs_le_hnormS {f : X × Z → ℝ} (hhom : ∀ x z (a : ℝ) (ha : 0 ≤ a),
    f (csmul hX ha x, z) = a * f (x, z)) {M : ℝ} (hM : ∀ p : X × Z, |f p| ≤ M * ‖p.1.1‖)
    (p : X × Z) : |f p| ≤ hnormS X f * ‖p.1.1‖ := by
  obtain ⟨x, z⟩ := p
  rcases eq_or_ne x.1 0 with h0 | h0
  · have : x = csmul hX le_rfl x := Subtype.ext (by simp [csmul, h0])
    rw [this, hhom, zero_mul, abs_zero]
    exact mul_nonneg (hnormS_nonneg f) (norm_nonneg _)
  · have hn : 0 < ‖x.1‖ := norm_pos_iff.2 h0
    set u : X := csmul hX (inv_nonneg.2 hn.le) x
    have hu : ‖u.1‖ = 1 := by
      simp only [u, csmul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    have hxu : x = csmul hX hn.le u := Subtype.ext (by
      simp only [u, csmul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul])
    change |f (x, z)| ≤ hnormS X f * ‖x.1‖
    conv_lhs => rw [hxu, hhom, abs_mul, abs_of_pos hn, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (le_ciSup (bddAbove_sphereS hM) (⟨(u, z), hu⟩ : {p : X × Z // ‖p.1.1‖ = 1})) hn.le

theorem abs_le_hnormS' {f : X × Z → ℝ} (hf : InHS hX f) (p : X × Z) :
    |f p| ≤ hnormS X f * ‖p.1.1‖ :=
  abs_le_hnormS hf.2.1 hf.2.2.choose_spec p

omit [NormedSpace ℝ E] [MetricSpace Z] in
theorem hnormS_le {f : X × Z → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ p : X × Z, ‖p.1.1‖ = 1 → |f p| ≤ C) : hnormS X f ≤ C :=
  Real.iSup_le (fun p => h p.1 p.2) hC

theorem inHS_sub {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) : InHS hX (f - g) := by
  obtain ⟨M, hM⟩ := hf.2.2
  obtain ⟨N, hN⟩ := hg.2.2
  refine ⟨hf.1.sub hg.1, fun x z a ha => by simp [hf.2.1, hg.2.1, mul_sub], M + N,
    fun p => ?_⟩
  simp only [Pi.sub_apply]
  calc |f p - g p| ≤ |f p| + |g p| := abs_sub _ _
    _ ≤ M * ‖p.1.1‖ + N * ‖p.1.1‖ := add_le_add (hM p) (hN p)
    _ = (M + N) * ‖p.1.1‖ := by ring

theorem inHS_add {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) : InHS hX (f + g) := by
  obtain ⟨M, hM⟩ := hf.2.2
  obtain ⟨N, hN⟩ := hg.2.2
  refine ⟨hf.1.add hg.1, fun x z a ha => by simp [hf.2.1, hg.2.1, mul_add], M + N,
    fun p => ?_⟩
  simp only [Pi.add_apply]
  calc |f p + g p| ≤ |f p| + |g p| := abs_add_le _ _
    _ ≤ M * ‖p.1.1‖ + N * ‖p.1.1‖ := add_le_add (hM p) (hN p)
    _ = (M + N) * ‖p.1.1‖ := by ring

theorem inHS_smul {f : X × Z → ℝ} (hf : InHS hX f) (r : ℝ) : InHS hX (r • f) := by
  obtain ⟨M, hM⟩ := hf.2.2
  refine ⟨hf.1.const_smul r, fun x z a ha => by simp [hf.2.1]; ring, |r| * M, fun p => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hM p) (abs_nonneg r)

theorem inHS_zero : InHS hX (0 : X × Z → ℝ) :=
  ⟨continuous_const, fun _ _ _ _ => by simp, 0, fun _ => by simp⟩

/-- `x ↦ ‖x‖` is in `H(S)`. -/
theorem inHS_norm : InHS hX fun p : X × Z => ‖p.1.1‖ :=
  ⟨(continuous_subtype_val.comp continuous_fst).norm,
    fun x z a ha => by simp [csmul, norm_smul, abs_of_nonneg ha], 1, fun p => by simp⟩

/-- **Exercise 4.7a for `H(S)` (norm).** `‖·‖` of (2) is a norm on `H(S)`. -/
theorem hnormS_norm {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) (r : ℝ) :
    0 ≤ hnormS X f ∧ (hnormS X f = 0 ↔ f = 0) ∧ hnormS X (r • f) = |r| * hnormS X f ∧
      hnormS X (f + g) ≤ hnormS X f + hnormS X g := by
  refine ⟨hnormS_nonneg f, ⟨fun h0 => funext fun p => ?_, fun h => ?_⟩, ?_, ?_⟩
  · have := abs_le_hnormS' hf p
    rw [h0, zero_mul] at this
    exact abs_nonpos_iff.1 this
  · subst h; simp [hnormS]
  · simp only [hnormS, Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [Real.mul_iSup_of_nonneg (abs_nonneg r)]
  · refine hnormS_le (add_nonneg (hnormS_nonneg f) (hnormS_nonneg g)) fun p hp => ?_
    have h1 := abs_le_hnormS' hf p
    have h2 := abs_le_hnormS' hg p
    rw [hp, mul_one] at h1 h2
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem hnormS_symm {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) :
    hnormS X (g - f) = hnormS X (f - g) := by
  have := (hnormS_norm (inHS_sub hf hg) (inHS_sub hf hg) (-1)).2.2.1
  rw [abs_neg, abs_one, one_mul] at this
  rw [← this]; congr 1; funext p; simp

/-- The triangle inequality for `‖f − h‖` on `H(S)`. -/
theorem hnormS_sub_le {f g h : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) (hh : InHS hX h) :
    hnormS X (f - h) ≤ hnormS X (f - g) + hnormS X (g - h) := by
  have := (hnormS_norm (inHS_sub hf hg) (inHS_sub hg hh) 1).2.2.2
  rwa [sub_add_sub_cancel] at this

/-- **Exercise 4.7a for `H(S)` (completeness).** A sequence in `H(S)` that is Cauchy for `‖·‖`
converges in `‖·‖` to an element of `H(S)`. -/
theorem hnormS_complete {f : ℕ → X × Z → ℝ} (hf : ∀ n, InHS hX (f n))
    (hc : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, hnormS X (f m - f n) < ε) :
    ∃ g, InHS hX g ∧ Tendsto (fun n => hnormS X (f n - g)) atTop (𝓝 0) := by
  -- pointwise Cauchy, hence a pointwise limit
  have hpt : ∀ p : X × Z, CauchySeq fun n => f n p := fun p =>
    Metric.cauchySeq_iff.2 fun ε hε => by
      obtain ⟨N, hN⟩ := hc (ε / (‖p.1.1‖ + 1)) (by positivity)
      refine ⟨N, fun m hm n hn => ?_⟩
      have h := abs_le_hnormS' (inHS_sub (hf m) (hf n)) p
      rw [Real.dist_eq]
      simp only [Pi.sub_apply] at h
      calc |f m p - f n p| ≤ hnormS X (f m - f n) * ‖p.1.1‖ := h
        _ ≤ ε / (‖p.1.1‖ + 1) * ‖p.1.1‖ :=
            mul_le_mul_of_nonneg_right (hN m hm n hn).le (norm_nonneg _)
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg p.1.1]
  choose g hg using fun p => cauchySeq_tendsto_of_complete (hpt p)
  -- `|fₙ(p) − g(p)| ≤ ε‖x‖` from some `N` on
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ p : X × Z, |f n p - g p| ≤ ε * ‖p.1.1‖ := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun n hn p => ?_⟩
    have hlim : Tendsto (fun m => |f n p - f m p|) atTop (𝓝 |f n p - g p|) :=
      ((tendsto_const_nhds.sub (hg p)).abs)
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
    have h := abs_le_hnormS' (inHS_sub (hf n) (hf m)) p
    simp only [Pi.sub_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hN n hn m hm).le (norm_nonneg _))
  -- `g` is continuous: locally uniform limit
  have hgc : Continuous g := by
    refine TendstoLocallyUniformly.continuous (F := f) (p := atTop) ?_
      (Frequently.of_forall fun n => (hf n).1)
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε p
    refine ⟨Metric.ball p 1, Metric.ball_mem_nhds p one_pos, ?_⟩
    obtain ⟨N, hN⟩ := hunif (ε / (‖p.1.1‖ + 2)) (by positivity)
    refine eventually_atTop.2 ⟨N, fun n hn q hq => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    have hq' : ‖q.1.1‖ ≤ ‖p.1.1‖ + 1 := by
      have hd : dist q p < 1 := Metric.mem_ball.1 hq
      have hd1 : dist q.1 p.1 < 1 :=
        (show dist q.1 p.1 ≤ dist q p by rw [Prod.dist_eq]; exact le_max_left _ _).trans_lt hd
      rw [Subtype.dist_eq, dist_eq_norm] at hd1
      have := norm_sub_norm_le q.1.1 p.1.1
      linarith
    calc |f n q - g q| ≤ ε / (‖p.1.1‖ + 2) * ‖q.1.1‖ := hN n hn q
      _ ≤ ε / (‖p.1.1‖ + 2) * (‖p.1.1‖ + 1) := mul_le_mul_of_nonneg_left hq' (by positivity)
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg p.1.1]
  -- `g` is homogeneous and bounded
  have hghom : ∀ x z (a : ℝ) (ha : 0 ≤ a), g (csmul hX ha x, z) = a * g (x, z) :=
    fun x z a ha => tendsto_nhds_unique (hg _) (by
      simp only [(hf _).2.1]
      exact (hg (x, z)).const_mul a)
  obtain ⟨N, hN⟩ := hunif 1 one_pos
  obtain ⟨M, hM⟩ := (hf N).2.2
  have hgb : ∀ p : X × Z, |g p| ≤ (M + 1) * ‖p.1.1‖ := fun p => by
    have := hN N le_rfl p
    calc |g p| ≤ |f N p| + |f N p - g p| := by
          have := abs_sub (f N p) (f N p - g p)
          rwa [sub_sub_cancel] at this
      _ ≤ M * ‖p.1.1‖ + 1 * ‖p.1.1‖ := add_le_add (hM p) this
      _ = (M + 1) * ‖p.1.1‖ := by ring
  refine ⟨g, ⟨hgc, hghom, M + 1, hgb⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N', hN'⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N', fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnormS_nonneg _)]
  refine (hnormS_le (half_pos hε).le fun p hp => ?_).trans_lt (half_lt_self hε)
  have := hN' n hn p
  rwa [hp, mul_one] at this

/-- **Theorem 4.12 on `H(S)`.** Let `T` be monotone on `H(S)` and discount in the sense
`T(f + a‖x‖) ≤ Tf + γa‖x‖` for `a ≥ 0`. Then `‖Tf − Tg‖ ≤ γ‖f − g‖` on `H(S)`. -/
theorem contraction_HS {T : (X × Z → ℝ) → (X × Z → ℝ)} {γ : ℝ} (hγ : 0 ≤ γ)
    (hmono : ∀ f g, InHS hX f → InHS hX g → f ≤ g → T f ≤ T g)
    (hdisc : ∀ f, InHS hX f → ∀ a : ℝ, 0 ≤ a →
      T (fun p => f p + a * ‖p.1.1‖) ≤ fun p => T f p + γ * a * ‖p.1.1‖)
    {f g : X × Z → ℝ} (hf : InHS hX f) (hg : InHS hX g) :
    hnormS X (T f - T g) ≤ γ * hnormS X (f - g) := by
  have hle : ∀ f g, InHS hX f → InHS hX g →
      T f ≤ fun p => T g p + γ * hnormS X (f - g) * ‖p.1.1‖ := fun f g hf hg => by
    have h1 : f ≤ fun p => g p + hnormS X (f - g) * ‖p.1.1‖ := fun p => by
      have := abs_le_hnormS' (inHS_sub hf hg) p
      simp only [Pi.sub_apply] at this
      linarith [le_abs_self (f p - g p)]
    have e : (fun p : X × Z => hnormS X (f - g) * ‖p.1.1‖) =
        hnormS X (f - g) • fun p : X × Z => ‖p.1.1‖ := by
      funext p; simp
    have hgH : InHS hX fun p => g p + hnormS X (f - g) * ‖p.1.1‖ := by
      change InHS hX (g + fun p : X × Z => hnormS X (f - g) * ‖p.1.1‖)
      rw [e]
      exact inHS_add hg (inHS_smul inHS_norm _)
    exact (hmono _ _ hf hgH h1).trans (hdisc g hg _ (hnormS_nonneg _))
  refine hnormS_le (mul_nonneg hγ (hnormS_nonneg _)) fun p hp => ?_
  have a := hle f g hf hg p
  have b := hle g f hg hf p
  dsimp only at a b
  rw [hnormS_symm hf hg, hp, mul_one] at b
  rw [hp, mul_one] at a
  simp only [Pi.sub_apply]
  rw [abs_le]
  constructor <;> linarith

end StokeyLucasPrescott.StochasticDP
