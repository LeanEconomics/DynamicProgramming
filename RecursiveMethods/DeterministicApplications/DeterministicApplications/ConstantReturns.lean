/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.BoundedReturns

/-!
# Constant returns to scale

SLP §4.3, pp. 87–92. The state space is a cone `X` in a real normed space (`x ∈ X`, `λ ≥ 0`
imply `λx ∈ X`). Functions on `X` that are continuous and homogeneous of degree one, with
`|f(x)| ≤ M‖x‖`, form `H(X)` (`InH`), normed by `‖f‖ = sup_{‖x‖ = 1} |f(x)|` (`hnorm`).

* `abs_le_hnorm`: `|f(x)| ≤ ‖f‖‖x‖` on `H(X)`.
* `ex_4_7a_norm`, `ex_4_7a_complete`: `hnorm` is a norm on `H(X)`, and `H(X)` is complete.
* `theorem_4_12`: monotone operators on `H(X)` that discount by `γ` in the sense
  `T(f + a‖·‖) ≤ Tf + γa‖·‖` are contractions of modulus `γ`.
* `Assumption410`, `Assumption411`, `ex_4_6a`, `ex_4_6b`, `ex_4_6c`: feasible plans grow at most
  at rate `α`, the sequence problem is well defined, and `v*` is homogeneous with `|v*| ≤ c‖x‖`.
* `ex_4_7b`, `theorem_4_13`: `T` maps `H(X)` into itself and has a unique fixed point `v`, with
  `‖Tⁿv₀ − v‖ ≤ (αβ)ⁿ‖v₀ − v‖`; the policy correspondence is compact-valued, u.h.c. and
  homogeneous; and `v = v*`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E}

/-- `X` is a cone. -/
def IsCone (X : Set E) : Prop := ∀ x ∈ X, ∀ a : ℝ, 0 ≤ a → a • x ∈ X

/-- `ax` in the cone `X`, for `a ≥ 0`. -/
def csmul (hX : IsCone X) {a : ℝ} (ha : 0 ≤ a) (x : X) : X := ⟨a • x.1, hX x.1 x.2 a ha⟩

/-- `f : X → ℝ` is in `H(X)`: continuous, homogeneous of degree one and `|f(x)| ≤ M‖x‖`. -/
def InH (hX : IsCone X) (f : X → ℝ) : Prop :=
  Continuous f ∧ (∀ x (a : ℝ) (ha : 0 ≤ a), f (csmul hX ha x) = a * f x) ∧
    ∃ M, ∀ x, |f x| ≤ M * ‖x.1‖

/-- The norm (1), p. 89: `‖f‖ = sup_{‖x‖ = 1} |f(x)|`. -/
noncomputable def hnorm (X : Set E) (f : X → ℝ) : ℝ := ⨆ x : {x : X // ‖x.1‖ = 1}, |f x.1|

variable {hX : IsCone X}

omit [NormedSpace ℝ E] in
theorem hnorm_nonneg (f : X → ℝ) : 0 ≤ hnorm X f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

omit [NormedSpace ℝ E] in
theorem bddAbove_sphere {f : X → ℝ} {M : ℝ} (hM : ∀ x, |f x| ≤ M * ‖x.1‖) :
    BddAbove (range fun x : {x : X // ‖x.1‖ = 1} => |f x.1|) :=
  ⟨M, by rintro _ ⟨x, rfl⟩; simpa [x.2] using hM x.1⟩

/-- On `H(X)`, `|f(x)| ≤ ‖f‖‖x‖`. -/
theorem abs_le_hnorm {f : X → ℝ} (hf : InH hX f) (x : X) : |f x| ≤ hnorm X f * ‖x.1‖ := by
  obtain ⟨M, hM⟩ := hf.2.2
  rcases eq_or_ne x.1 0 with h0 | h0
  · have : x = csmul hX le_rfl x := Subtype.ext (by simp [csmul, h0])
    rw [this, hf.2.1, zero_mul, abs_zero]
    exact mul_nonneg (hnorm_nonneg f) (norm_nonneg _)
  · have hn : 0 < ‖x.1‖ := norm_pos_iff.2 h0
    set u : X := csmul hX (inv_nonneg.2 hn.le) x
    have hu : ‖u.1‖ = 1 := by
      simp only [u, csmul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    have hxu : x = csmul hX hn.le u := Subtype.ext (by
      simp only [u, csmul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul])
    conv_lhs => rw [hxu, hf.2.1, abs_mul, abs_of_pos hn, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (le_ciSup (bddAbove_sphere hM) (⟨u, hu⟩ : {x : X // ‖x.1‖ = 1})) hn.le

omit [NormedSpace ℝ E] in
theorem hnorm_le {f : X → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x : X, ‖x.1‖ = 1 → |f x| ≤ C) :
    hnorm X f ≤ C :=
  Real.iSup_le (fun x => h x.1 x.2) hC

theorem inH_sub {f g : X → ℝ} (hf : InH hX f) (hg : InH hX g) : InH hX (f - g) := by
  obtain ⟨M, hM⟩ := hf.2.2
  obtain ⟨N, hN⟩ := hg.2.2
  refine ⟨hf.1.sub hg.1, fun x a ha => by simp [hf.2.1, hg.2.1, mul_sub], M + N, fun x => ?_⟩
  simp only [Pi.sub_apply]
  calc |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
    _ ≤ M * ‖x.1‖ + N * ‖x.1‖ := add_le_add (hM x) (hN x)
    _ = (M + N) * ‖x.1‖ := by ring

theorem inH_add {f g : X → ℝ} (hf : InH hX f) (hg : InH hX g) : InH hX (f + g) := by
  obtain ⟨M, hM⟩ := hf.2.2
  obtain ⟨N, hN⟩ := hg.2.2
  refine ⟨hf.1.add hg.1, fun x a ha => by simp [hf.2.1, hg.2.1, mul_add], M + N, fun x => ?_⟩
  simp only [Pi.add_apply]
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ M * ‖x.1‖ + N * ‖x.1‖ := add_le_add (hM x) (hN x)
    _ = (M + N) * ‖x.1‖ := by ring

theorem inH_smul {f : X → ℝ} (hf : InH hX f) (r : ℝ) : InH hX (r • f) := by
  obtain ⟨M, hM⟩ := hf.2.2
  refine ⟨hf.1.const_smul r, fun x a ha => by simp [hf.2.1]; ring, |r| * M, fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg r)

/-- **Exercise 4.7a (norm).** `‖·‖` of (1) is a norm on `H(X)`. -/
theorem ex_4_7a_norm {f g : X → ℝ} (hf : InH hX f) (hg : InH hX g) (r : ℝ) :
    0 ≤ hnorm X f ∧ (hnorm X f = 0 ↔ f = 0) ∧ hnorm X (r • f) = |r| * hnorm X f ∧
      hnorm X (f + g) ≤ hnorm X f + hnorm X g := by
  refine ⟨hnorm_nonneg f, ⟨fun h0 => funext fun x => ?_, fun h => ?_⟩, ?_, ?_⟩
  · have := abs_le_hnorm hf x
    rw [h0, zero_mul] at this
    exact abs_nonpos_iff.1 this
  · subst h; simp [hnorm]
  · simp only [hnorm, Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [Real.mul_iSup_of_nonneg (abs_nonneg r)]
  · refine hnorm_le (add_nonneg (hnorm_nonneg f) (hnorm_nonneg g)) fun x hx => ?_
    have h1 := abs_le_hnorm hf x
    have h2 := abs_le_hnorm hg x
    rw [hx, mul_one] at h1 h2
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **Exercise 4.7a (completeness).** A sequence in `H(X)` that is Cauchy for `‖·‖` converges in
`‖·‖` to an element of `H(X)`. -/
theorem ex_4_7a_complete {f : ℕ → X → ℝ} (hf : ∀ n, InH hX (f n))
    (hc : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, hnorm X (f m - f n) < ε) :
    ∃ g, InH hX g ∧ Tendsto (fun n => hnorm X (f n - g)) atTop (𝓝 0) := by
  -- pointwise Cauchy, hence a pointwise limit
  have hpt : ∀ x : X, CauchySeq fun n => f n x := fun x => Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hc (ε / (‖x.1‖ + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := abs_le_hnorm (inH_sub (hf m) (hf n)) x
    rw [Real.dist_eq]
    simp only [Pi.sub_apply] at h
    calc |f m x - f n x| ≤ hnorm X (f m - f n) * ‖x.1‖ := h
      _ ≤ ε / (‖x.1‖ + 1) * ‖x.1‖ :=
          mul_le_mul_of_nonneg_right (hN m hm n hn).le (norm_nonneg _)
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg x.1]
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hpt x)
  -- `|fₙ(x) − g(x)| ≤ ε‖x‖` from some `N` on
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x : X, |f n x - g x| ≤ ε * ‖x.1‖ := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun n hn x => ?_⟩
    have hlim : Tendsto (fun m => |f n x - f m x|) atTop (𝓝 |f n x - g x|) :=
      ((tendsto_const_nhds.sub (hg x)).abs)
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
    have h := abs_le_hnorm (inH_sub (hf n) (hf m)) x
    simp only [Pi.sub_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hN n hn m hm).le (norm_nonneg _))
  -- `g` is continuous: locally uniform limit
  have hgc : Continuous g := by
    refine TendstoLocallyUniformly.continuous (F := f) (p := atTop) ?_
      (Frequently.of_forall fun n => (hf n).1)
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε x
    refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
    obtain ⟨N, hN⟩ := hunif (ε / (‖x.1‖ + 2)) (by positivity)
    refine eventually_atTop.2 ⟨N, fun n hn y hy => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    have hy' : ‖y.1‖ ≤ ‖x.1‖ + 1 := by
      have hd : dist y x < 1 := Metric.mem_ball.1 hy
      rw [Subtype.dist_eq, dist_eq_norm] at hd
      have := norm_sub_norm_le y.1 x.1
      linarith
    calc |f n y - g y| ≤ ε / (‖x.1‖ + 2) * ‖y.1‖ := hN n hn y
      _ ≤ ε / (‖x.1‖ + 2) * (‖x.1‖ + 1) := mul_le_mul_of_nonneg_left hy' (by positivity)
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg x.1]
  -- `g` is homogeneous and bounded
  have hghom : ∀ x (a : ℝ) (ha : 0 ≤ a), g (csmul hX ha x) = a * g x := fun x a ha =>
    tendsto_nhds_unique (hg _) (by
      simp only [(hf _).2.1]
      exact (hg x).const_mul a)
  obtain ⟨N, hN⟩ := hunif 1 one_pos
  obtain ⟨M, hM⟩ := (hf N).2.2
  have hgb : ∀ x : X, |g x| ≤ (M + 1) * ‖x.1‖ := fun x => by
    have := hN N le_rfl x
    calc |g x| ≤ |f N x| + |f N x - g x| := by
          have := abs_sub (f N x) (f N x - g x)
          rwa [sub_sub_cancel] at this
      _ ≤ M * ‖x.1‖ + 1 * ‖x.1‖ := add_le_add (hM x) this
      _ = (M + 1) * ‖x.1‖ := by ring
  refine ⟨g, ⟨hgc, hghom, M + 1, hgb⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N', hN'⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N', fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnorm_nonneg _)]
  refine (hnorm_le (half_pos hε).le fun x hx => ?_).trans_lt (half_lt_self hε)
  have := hN' n hn x
  rwa [hx, mul_one] at this

/-- **Theorem 4.12.** Let `T` be monotone on `H(X)` and discount in the sense
`T(f + a‖·‖) ≤ Tf + γa‖·‖` for `a ≥ 0`. Then `‖Tf − Tg‖ ≤ γ‖f − g‖` on `H(X)`. (That `T` maps
`H(X)` into itself is not needed for the inequality.) -/
theorem theorem_4_12 {T : (X → ℝ) → (X → ℝ)} {γ : ℝ} (hγ : 0 ≤ γ)
    (hmono : ∀ f g, InH hX f → InH hX g → f ≤ g → T f ≤ T g)
    (hdisc : ∀ f, InH hX f → ∀ a : ℝ, 0 ≤ a →
      T (fun x => f x + a * ‖x.1‖) ≤ fun x => T f x + γ * a * ‖x.1‖)
    {f g : X → ℝ} (hf : InH hX f) (hg : InH hX g) :
    hnorm X (T f - T g) ≤ γ * hnorm X (f - g) := by
  have hnormH : InH hX fun x : X => ‖x.1‖ := ⟨continuous_subtype_val.norm,
    fun x a ha => by simp [csmul, norm_smul, abs_of_nonneg ha], 1, fun x => by simp⟩
  -- `f ≤ g + ‖f − g‖‖·‖`
  have hle : ∀ f g, InH hX f → InH hX g →
      T f ≤ fun x => T g x + γ * hnorm X (f - g) * ‖x.1‖ := fun f g hf hg => by
    have h1 : f ≤ fun x => g x + hnorm X (f - g) * ‖x.1‖ := fun x => by
      have := abs_le_hnorm (inH_sub hf hg) x
      simp only [Pi.sub_apply] at this
      linarith [le_abs_self (f x - g x)]
    have e : (fun x : X => hnorm X (f - g) * ‖x.1‖) = hnorm X (f - g) • fun x : X => ‖x.1‖ := by
      funext x; simp
    have hgH : InH hX fun x => g x + hnorm X (f - g) * ‖x.1‖ := by
      change InH hX (g + fun x : X => hnorm X (f - g) * ‖x.1‖)
      rw [e]
      exact inH_add hg (inH_smul hnormH _)
    exact (hmono _ _ hf hgH h1).trans (hdisc g hg _ (hnorm_nonneg _))
  refine hnorm_le (mul_nonneg hγ (hnorm_nonneg _)) fun x hx => ?_
  have a := hle f g hf hg x
  have b := hle g f hg hf x
  have hsym : hnorm X (g - f) = hnorm X (f - g) := by
    have := (ex_4_7a_norm (inH_sub hf hg) (inH_sub hf hg) (-1)).2.2.1
    rw [abs_neg, abs_one, one_mul] at this
    rw [← this]; congr 1; funext y; simp
  dsimp only at a b
  rw [hsym, hx, mul_one] at b
  rw [hx, mul_one] at a
  simp only [Pi.sub_apply]
  rw [abs_le]
  constructor <;> linarith

end StokeyLucasPrescott.DeterministicApplications
