/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.KUWeighted
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Construction of recursive utility (§20.1.2): Theorems 20.1.1 and 20.1.2

Miao §20.1.2, pp. 679–682.

**The operator.** For a space of streams `S` with a continuous shift `σ` (the book's `c ↦ ₁c`) and
a continuous head `hd` (`c ↦ c₀`), `ku_TW hd σ W f (c) = W(c₀, f(₁c))` is the book's `T_W`.
For a weight `ϕ > 0` let `κ` bound `δϕ(₁c) ≤ κϕ(c)` with `κ < 1` (the book's
`δ sup_c ϕ(₁c)/ϕ(c) < 1`). Under (W5), `|W(x, y) − W(x, y')| ≤ δ|y − y'|`:

* `ku_TW_mapsTo`, `ku_TW_contraction`: `T_W` maps `C_ϕ(S)` into itself and contracts `‖·‖_ϕ`
  with modulus `κ` (no monotonicity of `W` is needed);
* `ku_TW_exists_unique`: `T_W` has a unique fixed point in `C_ϕ(S)`;
* `ku_TW_iterate_bound`, `ku_TW_tendsto`: `|U(c) − T_Wⁿ0(c)| ≤ κⁿ‖U‖_ϕϕ(c)`, so `T_Wⁿ0 → U`
  in `‖·‖_ϕ` (the display on p. 682);
* `ku_TW_unique_of_bound`: `U` is also the only fixed point among the `ϕ`-bounded functions,
  continuous or not;
* `ku_TW_monotone`: (W3) makes the fixed point increasing.

The book's own proof of Theorem 20.1.2 goes through the Weighted Contraction Mapping Theorem
7.3.6 (`ku_thm_7_3_6_of_continuous`, copied in `KUWeighted`): `theorem_20_1_2_T0` (`T_W0 ∈ C_ϕ`),
`theorem_20_1_2_disc` (`T_W(f + aϕ) ≤ T_Wf + aκϕ`), and `theorem_20_1_2_via_7_3_6`.

**The consumption spaces.** `ℓ^∞_θ` (streams in `K` with `|c|_θ = sup_t ‖c_t‖/θᵗ < ∞`) is encoded
isometrically by `b_t = c_t/θᵗ`: `ku_Lθ θ K` is the set of bounded sequences `b` with
`c_t = θᵗb_t ∈ K` (`ku_seqθ`), `|c|_θ = ‖b‖` (`ku_thetaNorm_seqθ`), and every stream of finite
`θ`-norm arises (`ku_Lθ_surj`). The shift is `b ↦ θ · (b_{t+1})` (`ku_σθ`, `ku_seqθ_σθ`). The
book's `L` (bounded streams, sup norm) is `θ = 1` (`ku_seqθ_one`).

* `theorem_20_1_1`, `theorem_20_1_1_mono`, `theorem_20_1_1_concave`: Theorem 20.1.1.
* `theorem_20_1_2`, `theorem_20_1_2_concave`, `theorem_20_1_2_strict`: Theorem 20.1.2.

Departures: Theorem 20.1.2 is stated with (W5) only for existence, uniqueness and convergence
(the printed "(W2) and (W5)" would make (W5) redundant; the book's proof also uses that `W` is
increasing in `y`, which `theorem_20_1_2_via_7_3_6` assumes); (W5) is stated with `≤` and for all
`y ∈ ℝ` (the printed strict `<` fails at `y = y₀`, `ku_W5_misprint`); `θ > 0` replaces `θ ≥ 1`.
The strict concavity claim is proved with `W` jointly concave and strictly concave in the
direction of `x` (`theorem_20_1_2_strict`).
-/

namespace Miao.RecursiveUtility

open Filter Topology
open scoped BoundedContinuousFunction

/-! ### The operator `T_W` on an abstract space of streams -/

variable {S X : Type*} [TopologicalSpace S]

/-- Miao, p. 680: the operator `T_W f(c) = W(c₀, f(₁c))`, with head `hd c = c₀` and shift
`σ c = ₁c`. -/
def ku_TW (hd : S → X) (σ : S → S) (W : X → ℝ → ℝ) (f : S → ℝ) : S → ℝ :=
  fun c => W (hd c) (f (σ c))

theorem ku_TW_continuous {hd : S → X} {σ : S → S} {W : X → ℝ → ℝ} (hσ : Continuous σ)
    (hWc : Continuous fun p : S × ℝ => W (hd p.1) p.2) {f : S → ℝ} (hf : Continuous f) :
    Continuous (ku_TW hd σ W f) :=
  hWc.comp (continuous_id.prodMk (hf.comp hσ))

/-- Miao, (W5), p. 681 (corrected): as printed, with a strict inequality for all `y, y₀`, the
Lipschitz condition fails at `y = y₀` for every `W` and `δ`. -/
theorem ku_W5_misprint (W : ℝ → ℝ → ℝ) (δ : ℝ) :
    ¬ ∀ x y y₀ : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ y₀ → |W x y - W x y₀| < δ * |y - y₀| := by
  intro h
  have := h 0 0 0 le_rfl le_rfl le_rfl
  simp at this

variable {hd : S → X} {σ : S → S} {W : X → ℝ → ℝ} {ϕ : S → ℝ} {δ κ : ℝ}

/-- Miao, proof of Theorem 20.1.2, p. 681: under (W5) and `W(c₀, 0) ∈ C_ϕ`, `T_W` maps `C_ϕ(S)`
into itself, with `|T_Wf| ≤ (B + κ‖f‖_ϕ)ϕ`. -/
theorem ku_TW_mapsTo (hσ : Continuous σ) (hWc : Continuous fun p : S × ℝ => W (hd p.1) p.2)
    (hϕ : ∀ s, 0 < ϕ s) (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|)
    (hδ : 0 ≤ δ) (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {B : ℝ}
    (hB : ∀ c, |W (hd c) 0| ≤ B * ϕ c) {f : S → ℝ} (hf : ku_InC ϕ f) :
    ku_InC ϕ (ku_TW hd σ W f) := by
  refine ⟨ku_TW_continuous hσ hWc hf.1, B + κ * ku_norm ϕ f, fun c => ?_⟩
  have h1 := hW5 c (f (σ c)) 0
  have h2 := ku_abs_le hϕ hf (σ c)
  have h3 := hκ c
  have hN := ku_norm_nonneg (ϕ := ϕ) f
  rw [sub_zero] at h1
  calc |ku_TW hd σ W f c| ≤ |W (hd c) 0| + δ * |f (σ c)| := by
        have := abs_sub_abs_le_abs_sub (W (hd c) (f (σ c))) (W (hd c) 0)
        simp only [ku_TW]
        linarith
    _ ≤ B * ϕ c + δ * (ku_norm ϕ f * ϕ (σ c)) :=
        add_le_add (hB c) (mul_le_mul_of_nonneg_left h2 hδ)
    _ = B * ϕ c + ku_norm ϕ f * (δ * ϕ (σ c)) := by ring
    _ ≤ B * ϕ c + ku_norm ϕ f * (κ * ϕ c) := by
        have := mul_le_mul_of_nonneg_left h3 hN
        linarith
    _ = (B + κ * ku_norm ϕ f) * ϕ c := by ring

/-- Miao, proof of Theorem 20.1.2, pp. 681–682: under (W5), `T_W` is a contraction of modulus `κ`
for `‖·‖_ϕ`. -/
theorem ku_TW_contraction (hϕ : ∀ s, 0 < ϕ s)
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) :
    ku_norm ϕ (ku_TW hd σ W f - ku_TW hd σ W g) ≤ κ * ku_norm ϕ (f - g) := by
  refine ku_norm_le hϕ (mul_nonneg hκ0 (ku_norm_nonneg _)) fun c => ?_
  have h1 := hW5 c (f (σ c)) (g (σ c))
  have h2 := ku_abs_le hϕ (ku_inC_sub hf hg) (σ c)
  have hN := ku_norm_nonneg (ϕ := ϕ) (f - g)
  simp only [Pi.sub_apply] at h2 ⊢
  calc |ku_TW hd σ W f c - ku_TW hd σ W g c| ≤ δ * |f (σ c) - g (σ c)| := h1
    _ ≤ δ * (ku_norm ϕ (f - g) * ϕ (σ c)) := mul_le_mul_of_nonneg_left h2 hδ
    _ = ku_norm ϕ (f - g) * (δ * ϕ (σ c)) := by ring
    _ ≤ ku_norm ϕ (f - g) * (κ * ϕ c) := mul_le_mul_of_nonneg_left (hκ c) hN
    _ = κ * ku_norm ϕ (f - g) * ϕ c := by ring

/-- Miao, Theorem 20.1.2 (abstract form): under (W5), `W(c₀, 0) ∈ C_ϕ` and `δϕ(₁c) ≤ κϕ(c)` with
`κ < 1`, `T_W` has a unique fixed point in `C_ϕ(S)`. -/
theorem ku_TW_exists_unique (hσ : Continuous σ)
    (hWc : Continuous fun p : S × ℝ => W (hd p.1) p.2) (hϕc : Continuous ϕ)
    (hϕ : ∀ s, 0 < ϕ s) (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|)
    (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {B : ℝ}
    (hB : ∀ c, |W (hd c) 0| ≤ B * ϕ c) :
    ∃! U, ku_InC ϕ U ∧ ku_TW hd σ W U = U :=
  ku_exists_unique_fixedPoint hϕc hϕ (fun _ hf => ku_TW_mapsTo hσ hWc hϕ hW5 hδ hκ hB hf) hκ0
    hκ1 fun _ _ hf hg => ku_TW_contraction hϕ hW5 hδ hκ0 hκ hf hg

/-- Miao, p. 682: for a fixed point `U ∈ C_ϕ(S)`, `|U(c) − T_Wⁿ0(c)| ≤ κⁿ‖U‖_ϕϕ(c)`. -/
theorem ku_TW_iterate_bound (hϕ : ∀ s, 0 < ϕ s)
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {U : S → ℝ} (hU : ku_InC ϕ U)
    (hfix : ku_TW hd σ W U = U) (n : ℕ) (c : S) :
    |U c - (ku_TW hd σ W)^[n] 0 c| ≤ κ ^ n * ku_norm ϕ U * ϕ c := by
  induction n generalizing c with
  | zero =>
    simpa using ku_abs_le hϕ hU c
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← congrFun hfix c]
    have h1 := hW5 c (U (σ c)) ((ku_TW hd σ W)^[n] 0 (σ c))
    have h2 := ih (σ c)
    have hN : 0 ≤ κ ^ n * ku_norm ϕ U := mul_nonneg (pow_nonneg hκ0 n) (ku_norm_nonneg _)
    calc |ku_TW hd σ W U c - ku_TW hd σ W ((ku_TW hd σ W)^[n] 0) c|
        ≤ δ * |U (σ c) - (ku_TW hd σ W)^[n] 0 (σ c)| := h1
      _ ≤ δ * (κ ^ n * ku_norm ϕ U * ϕ (σ c)) := mul_le_mul_of_nonneg_left h2 hδ
      _ = κ ^ n * ku_norm ϕ U * (δ * ϕ (σ c)) := by ring
      _ ≤ κ ^ n * ku_norm ϕ U * (κ * ϕ c) := mul_le_mul_of_nonneg_left (hκ c) hN
      _ = κ ^ (n + 1) * ku_norm ϕ U * ϕ c := by ring

/-- Miao, Theorem 20.1.2 (p. 681) and its proof (p. 682): `T_Wⁿ0 → U` in `‖·‖_ϕ`, and so
pointwise. -/
theorem ku_TW_tendsto (hϕ : ∀ s, 0 < ϕ s)
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {U : S → ℝ} (hU : ku_InC ϕ U)
    (hfix : ku_TW hd σ W U = U) :
    Tendsto (fun n => ku_norm ϕ (U - (ku_TW hd σ W)^[n] 0)) atTop (𝓝 0) ∧
      ∀ c, Tendsto (fun n => (ku_TW hd σ W)^[n] 0 c) atTop (𝓝 (U c)) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1
  have hb := ku_TW_iterate_bound hϕ hW5 hδ hκ0 hκ hU hfix
  refine ⟨?_, fun c => ?_⟩
  · have h0 : Tendsto (fun n => κ ^ n * ku_norm ϕ U) atTop (𝓝 0) := by
      simpa using hpow.mul_const (ku_norm ϕ U)
    refine squeeze_zero (fun n => ku_norm_nonneg _) (fun n => ?_) h0
    exact ku_norm_le hϕ (mul_nonneg (pow_nonneg hκ0 n) (ku_norm_nonneg _)) fun c => by
      simpa using hb n c
  · have h0 : Tendsto (fun n => κ ^ n * ku_norm ϕ U * ϕ c) atTop (𝓝 0) := by
      simpa using (hpow.mul_const (ku_norm ϕ U)).mul_const (ϕ c)
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h0
    rw [Real.dist_eq, abs_sub_comm]
    exact hb n c

/-- `U` is the only fixed point of `T_W` among the `ϕ`-bounded functions, continuous or not. -/
theorem ku_TW_unique_of_bound (hϕ : ∀ s, 0 < ϕ s)
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {U : S → ℝ} (hU : ku_InC ϕ U)
    (hfix : ku_TW hd σ W U = U) {V : S → ℝ} {B : ℝ} (hV : ∀ c, |V c| ≤ B * ϕ c)
    (hVfix : ku_TW hd σ W V = V) : V = U := by
  set M := |B| + ku_norm ϕ U
  have hM : 0 ≤ M := add_nonneg (abs_nonneg B) (ku_norm_nonneg _)
  have hb : ∀ n c, |V c - U c| ≤ κ ^ n * M * ϕ c := by
    intro n
    induction n with
    | zero =>
      intro c
      have h1 := hV c
      have h2 := ku_abs_le hϕ hU c
      have h3 : B * ϕ c ≤ |B| * ϕ c := mul_le_mul_of_nonneg_right (le_abs_self B) (hϕ c).le
      have h4 := abs_sub (V c) (U c)
      simp only [pow_zero, one_mul, M]
      nlinarith
    | succ n ih =>
      intro c
      rw [← congrFun hVfix c, ← congrFun hfix c]
      have h1 := hW5 c (V (σ c)) (U (σ c))
      have h2 := ih (σ c)
      have hN : 0 ≤ κ ^ n * M := mul_nonneg (pow_nonneg hκ0 n) hM
      calc |ku_TW hd σ W V c - ku_TW hd σ W U c| ≤ δ * |V (σ c) - U (σ c)| := h1
        _ ≤ δ * (κ ^ n * M * ϕ (σ c)) := mul_le_mul_of_nonneg_left h2 hδ
        _ = κ ^ n * M * (δ * ϕ (σ c)) := by ring
        _ ≤ κ ^ n * M * (κ * ϕ c) := mul_le_mul_of_nonneg_left (hκ c) hN
        _ = κ ^ (n + 1) * M * ϕ c := by ring
  funext c
  have h0 : Tendsto (fun n => κ ^ n * M * ϕ c) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).mul_const M).mul_const (ϕ c)
  have := ge_of_tendsto' h0 fun n => hb n c
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- Miao, Theorem 20.1.1 and §20.1.2 (abstract form of "if `W` satisfies (W3), then `U` is
increasing"): if `W` is increasing and the head and shift preserve a relation `R` on streams, the
fixed point is increasing along `R`. -/
theorem ku_TW_monotone (hϕ : ∀ s, 0 < ϕ s)
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {U : S → ℝ} (hU : ku_InC ϕ U)
    (hfix : ku_TW hd σ W U = U) (R : S → S → Prop) (Rx : X → X → Prop)
    (hR : ∀ c c', R c c' → Rx (hd c) (hd c') ∧ R (σ c) (σ c'))
    (hW3 : ∀ c c', Rx (hd c) (hd c') → ∀ y y' : ℝ, y ≤ y' → W (hd c) y ≤ W (hd c') y')
    {c c' : S} (hcc : R c c') : U c ≤ U c' := by
  have hit : ∀ n, ∀ c c', R c c' → (ku_TW hd σ W)^[n] 0 c ≤ (ku_TW hd σ W)^[n] 0 c' := by
    intro n
    induction n with
    | zero => exact fun _ _ _ => le_rfl
    | succ n ih =>
      intro c c' h
      simp only [Function.iterate_succ_apply']
      exact hW3 c c' (hR c c' h).1 _ _ (ih _ _ (hR c c' h).2)
  have ht := (ku_TW_tendsto hϕ hW5 hδ hκ0 hκ1 hκ hU hfix).2
  exact le_of_tendsto_of_tendsto' (ht c) (ht c') fun n => hit n c c' hcc

/-! ### The book's route: the Weighted Contraction Mapping Theorem 7.3.6 -/

/-- Miao, proof of Theorem 20.1.2, p. 681: `|T_W0(c)|/ϕ(c) = |W(c₀, 0)|/ϕ(c) < ∞`, so
`T_W0 ∈ C_ϕ`. -/
theorem theorem_20_1_2_T0 (hWc : Continuous fun p : S × ℝ => W (hd p.1) p.2) {B : ℝ}
    (hB : ∀ c, |W (hd c) 0| ≤ B * ϕ c) : ku_InC ϕ (ku_TW hd σ W 0) :=
  ⟨hWc.comp (continuous_id.prodMk continuous_const), B, hB⟩

omit [TopologicalSpace S] in
/-- Miao, proof of Theorem 20.1.2, p. 682: by (W5), for `a > 0`,
`T_W(f + aϕ)(c) ≤ T_Wf(c) + aδϕ(₁c) ≤ T_Wf(c) + aκϕ(c)`, condition (b) of Theorem 7.3.6. -/
theorem theorem_20_1_2_disc (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|)
    (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) (hϕ : ∀ s, 0 < ϕ s) (f : S → ℝ) {a : ℝ} (ha : 0 < a) :
    ku_TW hd σ W (f + a • ϕ) ≤ ku_TW hd σ W f + (κ * a) • ϕ := by
  intro c
  have h1 := hW5 c (f (σ c) + a * ϕ (σ c)) (f (σ c))
  have h2 := hκ c
  rw [add_sub_cancel_left, abs_of_pos (mul_pos ha (hϕ (σ c)))] at h1
  have h3 := le_abs_self (W (hd c) (f (σ c) + a * ϕ (σ c)) - W (hd c) (f (σ c)))
  simp only [ku_TW, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

/-- **Theorem 20.1.2** by the book's route (Miao, pp. 681–682): if in addition `W` is increasing in
`y`, `T_W` is monotone, satisfies (b) of Theorem 7.3.6 with `κ` (`theorem_20_1_2_disc`) and (c)
(`theorem_20_1_2_T0`), so the Weighted Contraction Mapping Theorem gives a unique fixed point in
`C_ϕ`. -/
theorem theorem_20_1_2_via_7_3_6 (hσ : Continuous σ)
    (hWc : Continuous fun p : S × ℝ => W (hd p.1) p.2) (hϕc : Continuous ϕ)
    (hϕ : ∀ s, 0 < ϕ s) (hW3 : ∀ c, Monotone (W (hd c)))
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {B : ℝ} (hB : ∀ c, |W (hd c) 0| ≤ B * ϕ c) :
    ∃! U, ku_InC ϕ U ∧ ku_TW hd σ W U = U :=
  (ku_thm_7_3_6_of_continuous hϕc hϕ (fun _ hf => ku_TW_continuous hσ hWc hf.1)
    (fun _ _ _ _ hfg c => hW3 c (hfg (σ c))) hκ0 hκ1
    (fun f _ _ ha => theorem_20_1_2_disc hW5 hκ hϕ f ha) (theorem_20_1_2_T0 hWc hB)).2.2

/-! ### Concavity on a convex set of streams -/

/-- Concavity of `f` on a convex set `A` of streams, with `f` defined on the subtype `A`. -/
def ku_ConcaveS {V : Type*} [AddCommMonoid V] [SMul ℝ V] {A : Set V} (hA : Convex ℝ A)
    (f : A → ℝ) : Prop :=
  ∀ x y : A, ∀ a b : ℝ, ∀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
    a * f x + b * f y ≤ f ⟨a • x.1 + b • y.1, hA x.2 y.2 ha hb hab⟩

/-- A pointwise limit of concave functions is concave. -/
theorem ku_concaveS_of_tendsto {V : Type*} [AddCommMonoid V] [SMul ℝ V] {A : Set V}
    (hA : Convex ℝ A) {g : ℕ → A → ℝ} {U : A → ℝ} (hg : ∀ n, ku_ConcaveS hA (g n))
    (ht : ∀ c, Tendsto (fun n => g n c) atTop (𝓝 (U c))) : ku_ConcaveS hA U := by
  intro x y a b ha hb hab
  exact le_of_tendsto_of_tendsto' (((ht x).const_mul a).add ((ht y).const_mul b))
    (ht _) fun n => hg n x y a b ha hb hab

/-! ### The consumption spaces `L` and `ℓ^∞_θ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The shift `(b_t) ↦ (b_{t+1})` on bounded sequences. -/
def ku_bshift (b : ℕ →ᵇ E) : ℕ →ᵇ E :=
  b.compContinuous ⟨Nat.succ, continuous_of_discreteTopology⟩

omit [NormedSpace ℝ E] in
theorem ku_bshift_apply (b : ℕ →ᵇ E) (t : ℕ) : ku_bshift b t = b (t + 1) := rfl

/-- The stream `c_t = θᵗb_t` encoded by the bounded sequence `b`. -/
def ku_seqθ (θ : ℝ) (b : ℕ →ᵇ E) : ℕ → E := fun t => θ ^ t • b t

/-- Miao, p. 681: `ℓ^∞_θ`, encoded by `b_t = c_t/θᵗ`: bounded `b` with `c_t = θᵗb_t ∈ K`. -/
def ku_Lθ (θ : ℝ) (K : Set E) : Set (ℕ →ᵇ E) := {b | ∀ t, ku_seqθ θ b t ∈ K}

/-- Miao, p. 681: the `θ`-norm `|c|_θ = sup_t ‖c_t‖/θᵗ`. -/
noncomputable def ku_thetaNorm (θ : ℝ) (c : ℕ → E) : ℝ := ⨆ t, ‖c t‖ / θ ^ t

/-- Miao, p. 681: the encoding is isometric, `|c|_θ = ‖b‖`. -/
theorem ku_thetaNorm_seqθ {θ : ℝ} (hθ : 0 < θ) (b : ℕ →ᵇ E) :
    ku_thetaNorm θ (ku_seqθ θ b) = ‖b‖ := by
  rw [BoundedContinuousFunction.norm_eq_iSup_norm, ku_thetaNorm]
  congr 1
  funext t
  have h := pow_pos hθ t
  rw [ku_seqθ, norm_smul, Real.norm_eq_abs, abs_of_pos h, mul_div_cancel_left₀ _ h.ne']

/-- Miao, p. 681: every stream in `K` with finite `θ`-norm is encoded by some `b ∈ ℓ^∞_θ`. -/
theorem ku_Lθ_surj {θ : ℝ} (hθ : 0 < θ) {K : Set E} {c : ℕ → E} (hK : ∀ t, c t ∈ K)
    (hc : BddAbove (Set.range fun t => ‖c t‖ / θ ^ t)) :
    ∃ b ∈ ku_Lθ θ K, ku_seqθ θ b = c := by
  obtain ⟨B, hB⟩ := hc
  have hb : ∀ t, ‖(θ ^ t)⁻¹ • c t‖ ≤ B := fun t => by
    have h := pow_pos hθ t
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h, inv_mul_eq_div]
    exact hB ⟨t, rfl⟩
  let b : ℕ →ᵇ E := BoundedContinuousFunction.mkOfBound
    ⟨fun t => (θ ^ t)⁻¹ • c t, continuous_of_discreteTopology⟩ (B + B)
    fun s t => ((dist_eq_norm _ _).le.trans (norm_sub_le _ _)).trans (add_le_add (hb s) (hb t))
  have hbc : ku_seqθ θ b = c := by
    funext t
    have h := pow_pos hθ t
    change θ ^ t • (θ ^ t)⁻¹ • c t = c t
    rw [smul_smul, mul_inv_cancel₀ h.ne', one_smul]
  exact ⟨b, fun t => by rw [hbc]; exact hK t, hbc⟩

/-- Miao, p. 681: `ℓ^∞_θ` is complete in the `θ`-norm when `K` is closed (the book's "Banach
space"; `K = ℝˡ₊` is not a vector space): it is a closed subset of the bounded sequences. -/
theorem ku_Lθ_complete [CompleteSpace E] (θ : ℝ) {K : Set E} (hK : IsClosed K) :
    CompleteSpace (ku_Lθ θ K) := by
  have hc : IsClosed (ku_Lθ θ K) := by
    have : ku_Lθ θ K = ⋂ t, (fun b : ℕ →ᵇ E => θ ^ t • b t) ⁻¹' K := by
      ext b
      simp [ku_Lθ, ku_seqθ]
    rw [this]
    exact isClosed_iInter fun t => hK.preimage
      ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.const_smul _)
  exact hc.completeSpace_coe

/-- For `θ = 1` the encoding is the identity: `ℓ^∞_1` is the book's space `L` of bounded streams
with the sup norm. -/
theorem ku_seqθ_one (b : ℕ →ᵇ E) : ku_seqθ 1 b = b := by
  funext t
  simp [ku_seqθ]

theorem ku_seqθ_zero (θ : ℝ) (b : ℕ →ᵇ E) : ku_seqθ θ b 0 = b 0 := by
  simp [ku_seqθ]

/-- The shift on `ℓ^∞_θ`: `b ↦ θ · (b_{t+1})`. -/
def ku_σθ {θ : ℝ} {K : Set E} (b : ku_Lθ θ K) : ku_Lθ θ K :=
  ⟨θ • ku_bshift b.1, fun t => by
    have h := b.2 (t + 1)
    simp only [ku_seqθ, BoundedContinuousFunction.coe_smul, ku_bshift_apply,
      smul_smul] at h ⊢
    rwa [← pow_succ]⟩

/-- Miao, p. 677: the shift on `ℓ^∞_θ` is the book's `c ↦ ₁c`: `(₁c)_t = c_{t+1}`. -/
theorem ku_seqθ_σθ {θ : ℝ} {K : Set E} (b : ku_Lθ θ K) (t : ℕ) :
    ku_seqθ θ (ku_σθ b).1 t = ku_seqθ θ b.1 (t + 1) := by
  simp only [ku_σθ, ku_seqθ, BoundedContinuousFunction.coe_smul, ku_bshift_apply,
    smul_smul, ← pow_succ]

theorem ku_continuous_σθ {θ : ℝ} {K : Set E} : Continuous (ku_σθ (θ := θ) (K := K)) :=
  Continuous.subtype_mk ((continuous_const_smul θ).comp
    ((BoundedContinuousFunction.continuous_compContinuous _).comp continuous_subtype_val)) _

theorem ku_continuous_head {θ : ℝ} {K : Set E} : Continuous fun b : ku_Lθ θ K => b.1 0 :=
  (BoundedContinuousFunction.lipschitz_eval_const 0).continuous.comp continuous_subtype_val

theorem ku_head_mem {θ : ℝ} {K : Set E} (b : ku_Lθ θ K) : b.1 0 ∈ K := by
  have h := b.2 0
  rwa [ku_seqθ_zero] at h

/-- `W ∘ (head, id)` is continuous on `ℓ^∞_θ × ℝ` when `W` is continuous on `K × ℝ`. -/
theorem ku_continuous_W {θ : ℝ} {K : Set E} {W : E → ℝ → ℝ}
    (hWc : ContinuousOn (fun p : E × ℝ => W p.1 p.2) (K ×ˢ Set.univ)) :
    Continuous fun p : ku_Lθ θ K × ℝ => W (p.1.1 0) p.2 :=
  hWc.comp_continuous ((ku_continuous_head.comp continuous_fst).prodMk continuous_snd)
    fun p => ⟨ku_head_mem p.1, Set.mem_univ _⟩

theorem ku_convex_Lθ {θ : ℝ} {K : Set E} (hK : Convex ℝ K) : Convex ℝ (ku_Lθ θ K) := by
  intro x hx y hy a b ha hb hab t
  have := hK (hx t) (hy t) ha hb hab
  simp only [ku_seqθ, BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul,
    Pi.add_apply, smul_add] at this ⊢
  rwa [smul_comm (θ ^ t) a, smul_comm (θ ^ t) b]

theorem ku_σθ_mix {θ : ℝ} {K : Set E} (hK : Convex ℝ K) (x y : ku_Lθ θ K) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ku_σθ ⟨a • x.1 + b • y.1, ku_convex_Lθ hK x.2 y.2 ha hb hab⟩ =
      ⟨a • (ku_σθ x).1 + b • (ku_σθ y).1,
        ku_convex_Lθ hK (ku_σθ x).2 (ku_σθ y).2 ha hb hab⟩ := by
  apply Subtype.ext
  ext t
  simp only [ku_σθ, BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_add,
    Pi.add_apply, ku_bshift_apply, smul_add]
  rw [smul_comm θ a, smul_comm θ b]

/-- One step of concavity: for `W` concave on `K × ℝ` and increasing in `y`, `T_W` maps concave
functions on `ℓ^∞_θ` to concave functions. -/
theorem ku_TW_concave {θ : ℝ} {K : Set E} (hK : Convex ℝ K) {W : E → ℝ → ℝ}
    (hW4 : ConcaveOn ℝ (K ×ˢ Set.univ) fun p : E × ℝ => W p.1 p.2)
    (hW3 : ∀ x ∈ K, Monotone (W x)) {f : ku_Lθ θ K → ℝ} (hf : ku_ConcaveS (ku_convex_Lθ hK) f) :
    ku_ConcaveS (ku_convex_Lθ hK) (ku_TW (fun b => b.1 0) ku_σθ W f) := by
  intro x y a b ha hb hab
  simp only [ku_TW]
  rw [ku_σθ_mix hK x y ha hb hab]
  have hmix : (a • x.1 + b • y.1) 0 = a • x.1 0 + b • y.1 0 := rfl
  have hxK := ku_head_mem x
  have hyK := ku_head_mem y
  have h1 := hf (ku_σθ x) (ku_σθ y) a b ha hb hab
  have h2 := hW3 _ (hK hxK hyK ha hb hab) h1
  have h3 := hW4.2 (x := (x.1 0, f (ku_σθ x))) (y := (y.1 0, f (ku_σθ y)))
    ⟨hxK, Set.mem_univ _⟩ ⟨hyK, Set.mem_univ _⟩ ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h3
  rw [hmix]
  exact h3.trans h2

/-! ### Theorem 20.1.1 -/

/-- **Theorem 20.1.1** (Miao, p. 680), existence and uniqueness. Let `W : K × ℝ → ℝ` be continuous
with (W1) `W(·, z)` bounded on `K` for `z ≥ 0` and (W2) `|W(x, z) − W(x, z')| ≤ β|z − z'|` with
`0 ≤ β < 1`. Then on the book's space `L` (`ℓ^∞_1`) there is exactly one bounded continuous
`U : L → ℝ` with `U(c) = W(c₀, U(₁c))`: the fixed point of `T_W` on `C(L)`. -/
theorem theorem_20_1_1 {K : Set E} {W : E → ℝ → ℝ}
    (hWc : ContinuousOn (fun p : E × ℝ => W p.1 p.2) (K ×ˢ Set.univ))
    (hW1 : ∀ z : ℝ, 0 ≤ z → ∃ B, ∀ x ∈ K, |W x z| ≤ B) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hW2 : ∀ x ∈ K, ∀ z z', |W x z - W x z'| ≤ β * |z - z'|) :
    ∃! U : ku_Lθ 1 K →ᵇ ℝ, ∀ c, U c = W (c.1 0) (U (ku_σθ c)) := by
  obtain ⟨B, hB⟩ := hW1 0 le_rfl
  have h := ku_TW_exists_unique (S := ku_Lθ 1 K) (hd := fun b => b.1 0) (σ := ku_σθ) (W := W)
    (ϕ := fun _ => 1) (δ := β) (κ := β) ku_continuous_σθ (ku_continuous_W hWc)
    continuous_const (fun _ => one_pos) (fun c => hW2 _ (ku_head_mem c)) hβ0 hβ0 hβ1
    (fun _ => le_rfl) (B := B) (fun c => by rw [mul_one]; exact hB _ (ku_head_mem c))
  obtain ⟨U, ⟨hU, hfix⟩, huniq⟩ := h
  obtain ⟨C, hC⟩ := hU.2
  let U' : ku_Lθ 1 K →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup U hU.1 C
    fun c => by rw [Real.norm_eq_abs]; simpa using hC c
  refine ⟨U', fun c => (congrFun hfix c).symm, fun V hV => ?_⟩
  have hVin : ku_InC (fun _ => (1 : ℝ)) (fun c => V c) :=
    ⟨V.continuous, ‖V‖, fun c => by rw [mul_one, ← Real.norm_eq_abs]; exact V.norm_coe_le_norm c⟩
  have e := huniq (fun c => V c) ⟨hVin, funext fun c => (hV c).symm⟩
  ext c
  exact congrFun e c

/-- **Theorem 20.1.1** (Miao, p. 680): "if `W` satisfies (W3), then `U` is increasing": if `W` is
increasing in both arguments on `K × ℝ`, then `c ≤ c'` componentwise gives `U(c) ≤ U(c')`. -/
theorem theorem_20_1_1_mono [Preorder E] {K : Set E} {W : E → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hW2 : ∀ x ∈ K, ∀ z z', |W x z - W x z'| ≤ β * |z - z'|)
    (hW3 : ∀ x ∈ K, ∀ x' ∈ K, x ≤ x' → ∀ z z' : ℝ, z ≤ z' → W x z ≤ W x' z')
    (U : ku_Lθ 1 K →ᵇ ℝ) (hU : ∀ c, U c = W (c.1 0) (U (ku_σθ c))) {c c' : ku_Lθ 1 K}
    (hcc : ∀ t, c.1 t ≤ c'.1 t) : U c ≤ U c' := by
  have hUin : ku_InC (fun _ => (1 : ℝ)) (fun c => U c) :=
    ⟨U.continuous, ‖U‖, fun c => by rw [mul_one, ← Real.norm_eq_abs]; exact U.norm_coe_le_norm c⟩
  exact ku_TW_monotone (S := ku_Lθ 1 K) (hd := fun b => b.1 0) (σ := ku_σθ) (W := W)
    (ϕ := fun _ => 1) (δ := β) (κ := β) (fun _ => one_pos)
    (fun c => hW2 _ (ku_head_mem c)) hβ0 hβ0 hβ1 (fun _ => le_rfl) hUin
    (funext fun c => (hU c).symm) (fun c c' => ∀ t, c.1 t ≤ c'.1 t) (· ≤ ·)
    (fun c c' h => ⟨h 0, fun t => by
      simpa [ku_σθ, ku_bshift_apply] using h (t + 1)⟩)
    (fun c c' h y y' hy => hW3 _ (ku_head_mem c) _ (ku_head_mem c') h y y' hy) hcc

/-- **Theorem 20.1.1** (Miao, p. 680): "if (W3)–(W4) hold, then `U` is concave": for `K` convex
and `W` concave on `K × ℝ` and increasing in `z`, the solution `U` is concave on `L`. -/
theorem theorem_20_1_1_concave {K : Set E} (hK : Convex ℝ K) {W : E → ℝ → ℝ}
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hW2 : ∀ x ∈ K, ∀ z z', |W x z - W x z'| ≤ β * |z - z'|)
    (hW3 : ∀ x ∈ K, Monotone (W x))
    (hW4 : ConcaveOn ℝ (K ×ˢ Set.univ) fun p : E × ℝ => W p.1 p.2)
    (U : ku_Lθ 1 K →ᵇ ℝ) (hU : ∀ c, U c = W (c.1 0) (U (ku_σθ c))) :
    ku_ConcaveS (ku_convex_Lθ hK) fun c => U c := by
  have hUin : ku_InC (fun _ => (1 : ℝ)) (fun c => U c) :=
    ⟨U.continuous, ‖U‖, fun c => by rw [mul_one, ← Real.norm_eq_abs]; exact U.norm_coe_le_norm c⟩
  have ht := (ku_TW_tendsto (S := ku_Lθ 1 K) (hd := fun b => b.1 0) (σ := ku_σθ) (W := W)
    (ϕ := fun _ => 1) (δ := β) (κ := β) (fun _ => one_pos)
    (fun c => hW2 _ (ku_head_mem c)) hβ0 hβ0 hβ1 (fun _ => le_rfl) hUin
    (funext fun c => (hU c).symm)).2
  refine ku_concaveS_of_tendsto (ku_convex_Lθ hK) (fun n => ?_) ht
  induction n with
  | zero => intro x y a b _ _ _; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ku_TW_concave hK hW4 hW3 ih

/-! ### Theorem 20.1.2 -/

/-- **Theorem 20.1.2** (Miao, p. 681), existence, uniqueness and convergence. On `ℓ^∞_θ`
(`θ > 0`), let `W` be continuous on `K × ℝ` with (W5) `|W(x, y) − W(x, y')| ≤ δ|y − y'|`, let
`ϕ > 0` be continuous, `W(c₀, 0)` bounded in the `ϕ`-norm, and `δ sup_c ϕ(₁c)/ϕ(c) < 1`. Then
there is a unique `U ∈ C_ϕ(ℓ^∞_θ)` with `W(c₀, U(₁c)) = U(c)`, and `T_Wⁿ0 → U` in `C_ϕ`. -/
theorem theorem_20_1_2 {θ : ℝ} {K : Set E} {W : E → ℝ → ℝ}
    (hWc : ContinuousOn (fun p : E × ℝ => W p.1 p.2) (K ×ˢ Set.univ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hW5 : ∀ x ∈ K, ∀ y y', |W x y - W x y'| ≤ δ * |y - y'|) {ϕ : ku_Lθ θ K → ℝ}
    (hϕc : Continuous ϕ) (hϕ : ∀ c, 0 < ϕ c) (hW0 : ∃ B, ∀ c, |W (c.1 0) 0| ≤ B * ϕ c)
    (hsup : BddAbove (Set.range fun c => ϕ (ku_σθ c) / ϕ c))
    (hδsup : δ * ⨆ c, ϕ (ku_σθ c) / ϕ c < 1) :
    (∃! U, ku_InC ϕ U ∧ ∀ c, W (c.1 0) (U (ku_σθ c)) = U c) ∧
      ∀ U, ku_InC ϕ U → (∀ c, W (c.1 0) (U (ku_σθ c)) = U c) →
        Tendsto (fun n => ku_norm ϕ (U - (ku_TW (fun b => b.1 0) ku_σθ W)^[n] 0)) atTop
          (𝓝 0) := by
  obtain ⟨B, hB⟩ := hW0
  set κ := δ * ⨆ c, ϕ (ku_σθ c) / ϕ c
  have hκ0 : 0 ≤ κ :=
    mul_nonneg hδ (Real.iSup_nonneg fun c => (div_pos (hϕ _) (hϕ c)).le)
  have hκ : ∀ c, δ * ϕ (ku_σθ c) ≤ κ * ϕ c := fun c => by
    have h1 : ϕ (ku_σθ c) / ϕ c ≤ ⨆ c, ϕ (ku_σθ c) / ϕ c := le_ciSup hsup c
    rw [div_le_iff₀ (hϕ c)] at h1
    calc δ * ϕ (ku_σθ c) ≤ δ * ((⨆ c, ϕ (ku_σθ c) / ϕ c) * ϕ c) :=
          mul_le_mul_of_nonneg_left h1 hδ
      _ = κ * ϕ c := by ring
  have hW5' : ∀ (c : ku_Lθ θ K) y y', |W (c.1 0) y - W (c.1 0) y'| ≤ δ * |y - y'| :=
    fun c => hW5 _ (ku_head_mem c)
  refine ⟨?_, fun U hU hfix => (ku_TW_tendsto hϕ hW5' hδ hκ0 hδsup hκ hU
    (funext hfix)).1⟩
  obtain ⟨U, ⟨hU, hfix⟩, huniq⟩ := ku_TW_exists_unique ku_continuous_σθ (ku_continuous_W hWc)
    hϕc hϕ hW5' hδ hκ0 hδsup hκ hB
  exact ⟨U, ⟨hU, congrFun hfix⟩, fun V ⟨hV, hVf⟩ => huniq V ⟨hV, funext hVf⟩⟩

/-- **Theorem 20.1.2** (Miao, p. 681): "if (W6) holds, then `U` is concave". (W6): every
`T_Wⁿy` with `y` constant is concave on `ℓ^∞_θ`; the solution `U ∈ C_ϕ` is the pointwise limit of
`T_Wⁿ0` (`ku_TW_tendsto`), hence concave. -/
theorem theorem_20_1_2_concave {θ : ℝ} {K : Set E} (hK : Convex ℝ K) {W : E → ℝ → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hW5 : ∀ x ∈ K, ∀ y y', |W x y - W x y'| ≤ δ * |y - y'|)
    {ϕ : ku_Lθ θ K → ℝ} (hϕ : ∀ c, 0 < ϕ c) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hκ : ∀ c, δ * ϕ (ku_σθ c) ≤ κ * ϕ c)
    (hW6 : ∀ (n : ℕ) (y : ℝ),
      ku_ConcaveS (ku_convex_Lθ (θ := θ) hK) ((ku_TW (fun b => b.1 0) ku_σθ W)^[n] fun _ => y))
    {U : ku_Lθ θ K → ℝ} (hU : ku_InC ϕ U) (hfix : ∀ c, W (c.1 0) (U (ku_σθ c)) = U c) :
    ku_ConcaveS (ku_convex_Lθ (θ := θ) hK) U :=
  ku_concaveS_of_tendsto (ku_convex_Lθ (θ := θ) hK) (fun n => hW6 n 0)
    (ku_TW_tendsto hϕ (fun c => hW5 _ (ku_head_mem c)) hδ hκ0 hκ1 hκ hU (funext hfix)).2

/-- **Theorem 20.1.2** (Miao, p. 681), strict concavity (corrected hypotheses). If `W` is concave
on `K × ℝ`, strictly increasing in `y`, and strictly concave in the direction of `x`
(`aW(x, y) + bW(x', y') < W(ax + bx', ay + by')` for `x ≠ x'`), then a concave solution `U` of
`U(c) = W(c₀, U(₁c))` is strictly concave. (The printed "strictly [concave] in `x`" alone does
not drive the argument: the first date at which two streams differ may be any `t`.) -/
theorem theorem_20_1_2_strict {θ : ℝ} (hθ : 0 < θ) {K : Set E} (hK : Convex ℝ K)
    {W : E → ℝ → ℝ} (hW4 : ConcaveOn ℝ (K ×ˢ Set.univ) fun p : E × ℝ => W p.1 p.2)
    (hWs : ∀ x ∈ K, StrictMono (W x))
    (hWx : ∀ x ∈ K, ∀ x' ∈ K, x ≠ x' → ∀ y y' : ℝ, ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      a * W x y + b * W x' y' < W (a • x + b • x') (a * y + b * y'))
    {U : ku_Lθ θ K → ℝ} (hUc : ku_ConcaveS (ku_convex_Lθ (θ := θ) hK) U)
    (hfix : ∀ c, U c = W (c.1 0) (U (ku_σθ c))) {c c' : ku_Lθ θ K} (hne : c ≠ c') {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * U c + b * U c' < U ⟨a • c.1 + b • c'.1, ku_convex_Lθ hK c.2 c'.2 ha.le hb.le hab⟩ := by
  -- streams whose heads differ
  have head : ∀ x y : ku_Lθ θ K, x.1 0 ≠ y.1 0 →
      a * U x + b * U y < U ⟨a • x.1 + b • y.1, ku_convex_Lθ hK x.2 y.2 ha.le hb.le hab⟩ := by
    intro x y hxy
    rw [hfix x, hfix y, hfix ⟨a • x.1 + b • y.1, ku_convex_Lθ hK x.2 y.2 ha.le hb.le hab⟩,
      ku_σθ_mix hK x y ha.le hb.le hab]
    have hmix : (a • x.1 + b • y.1) 0 = a • x.1 0 + b • y.1 0 := rfl
    rw [hmix]
    have h1 := hUc (ku_σθ x) (ku_σθ y) a b ha.le hb.le hab
    have h2 := (hWs _ (hK (ku_head_mem x) (ku_head_mem y) ha.le hb.le hab)).monotone h1
    exact (hWx _ (ku_head_mem x) _ (ku_head_mem y) hxy _ _ a b ha hb hab).trans_le h2
  have key : ∀ k, ∀ x y : ku_Lθ θ K, x.1 k ≠ y.1 k →
      a * U x + b * U y < U ⟨a • x.1 + b • y.1, ku_convex_Lθ hK x.2 y.2 ha.le hb.le hab⟩ := by
    intro k
    induction k with
    | zero => exact head
    | succ k ih =>
      intro x y hxy
      by_cases h0 : x.1 0 = y.1 0
      · have hs : (ku_σθ x).1 k ≠ (ku_σθ y).1 k := by
          simp only [ku_σθ, BoundedContinuousFunction.coe_smul, ku_bshift_apply]
          exact fun h => hxy (smul_right_injective E hθ.ne' h)
        have h1 := ih _ _ hs
        rw [hfix x, hfix y, hfix ⟨a • x.1 + b • y.1, ku_convex_Lθ hK x.2 y.2 ha.le hb.le hab⟩,
          ku_σθ_mix hK x y ha.le hb.le hab]
        have hmix : (a • x.1 + b • y.1) 0 = y.1 0 := by
          change a • x.1 0 + b • y.1 0 = y.1 0
          rw [h0, ← add_smul, hab, one_smul]
        rw [hmix, h0]
        have h2 := hW4.2 (x := (y.1 0, U (ku_σθ x))) (y := (y.1 0, U (ku_σθ y)))
          ⟨ku_head_mem y, Set.mem_univ _⟩ ⟨ku_head_mem y, Set.mem_univ _⟩ ha.le hb.le hab
        simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h2
        rw [← add_smul, hab, one_smul] at h2
        exact h2.trans_lt (hWs _ (ku_head_mem y) h1)
      · exact head x y h0
  have hk : ∃ k, c.1 k ≠ c'.1 k := by
    by_contra h
    push Not at h
    exact hne (Subtype.ext (BoundedContinuousFunction.ext h))
  obtain ⟨k, hk⟩ := hk
  exact key k c c' hk

end Miao.RecursiveUtility
