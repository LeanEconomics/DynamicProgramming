/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Basic.Real.Pointwise

/-!
# The weighted space `C_ϕ(S)` and the Weighted Contraction Mapping Theorem

Copied from `EconomicDynamics/InfiniteHorizonDP` (modules `WNSpace` and `WNWeighted`), with the
namespace renamed to `Miao.RecursiveUtility` and every name prefixed `ku_`. Miao §7.3.2,
pp. 212–213, (7.23), Exercise 7.1 and Theorem 7.3.6, which the proof of Theorem 20.1.2 (p. 682)
applies.

* `ku_InC ϕ f`: `f ∈ C_ϕ(S)`, continuous with `|f| ≤ Bϕ`; `ku_norm ϕ f = sup |f/ϕ|`.
* `ku_exists_unique_fixedPoint`: the Contraction Mapping Theorem on `(C_ϕ(S), ‖·‖_ϕ)`.
* `ku_thm_7_3_6`, `ku_thm_7_3_6_of_continuous`: the Weighted Contraction Mapping
  Theorem (monotone + weighted discounting, `T0 ∈ C_ϕ(S)`).
-/

namespace Miao.RecursiveUtility

open Filter Topology

variable {S : Type*} [TopologicalSpace S]

/-- Miao, p. 212: `f ∈ C_ϕ(S)`: `f` is continuous and `sup_s |f(s)/ϕ(s)| < ∞`. The finiteness is
stated as a bound `|f(s)| ≤ Bϕ(s)`; for `ϕ > 0` this is the same (`ku_inC_iff`). -/
def ku_InC (ϕ : S → ℝ) (f : S → ℝ) : Prop :=
  Continuous f ∧ ∃ B, ∀ s, |f s| ≤ B * ϕ s

/-- Miao, (7.23), p. 212: the weighted sup norm `‖f‖_ϕ = sup_s |f(s)/ϕ(s)|`. -/
noncomputable def ku_norm (ϕ : S → ℝ) (f : S → ℝ) : ℝ := ⨆ s, |f s / ϕ s|

variable {ϕ : S → ℝ}

/-- Miao, p. 212: for `ϕ > 0`, the bound in `ku_InC` is `sup_s |f(s)/ϕ(s)| < ∞`. -/
theorem ku_inC_iff (hϕ : ∀ s, 0 < ϕ s) (f : S → ℝ) :
    ku_InC ϕ f ↔ Continuous f ∧ BddAbove (Set.range fun s => |f s / ϕ s|) := by
  refine and_congr_right fun _ => ⟨fun ⟨B, hB⟩ => ⟨B, ?_⟩, fun ⟨C, hC⟩ => ⟨C, fun s => ?_⟩⟩
  · rintro _ ⟨s, rfl⟩
    change |f s / ϕ s| ≤ B
    rw [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)]
    exact hB s
  · have h : |f s / ϕ s| ≤ C := hC ⟨s, rfl⟩
    rwa [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)] at h

theorem ku_bdd (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ} (hf : ku_InC ϕ f) :
    BddAbove (Set.range fun s => |f s / ϕ s|) :=
  ((ku_inC_iff hϕ f).1 hf).2

omit [TopologicalSpace S] in
theorem ku_norm_nonneg (f : S → ℝ) : 0 ≤ ku_norm ϕ f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- On `C_ϕ(S)`, `|f(s)| ≤ ‖f‖_ϕ ϕ(s)`. -/
theorem ku_abs_le (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ} (hf : ku_InC ϕ f) (s : S) :
    |f s| ≤ ku_norm ϕ f * ϕ s := by
  have h : |f s / ϕ s| ≤ ku_norm ϕ f := le_ciSup (ku_bdd hϕ hf) s
  rwa [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)] at h

omit [TopologicalSpace S] in
/-- `|f| ≤ Cϕ` with `C ≥ 0` gives `‖f‖_ϕ ≤ C`. -/
theorem ku_norm_le (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s, |f s| ≤ C * ϕ s) : ku_norm ϕ f ≤ C :=
  Real.iSup_le (fun s => by rw [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)]; exact h s) hC

omit [TopologicalSpace S] in
theorem ku_norm_sub_comm (f g : S → ℝ) : ku_norm ϕ (f - g) = ku_norm ϕ (g - f) := by
  simp only [ku_norm, Pi.sub_apply]
  congr 1
  funext s
  rw [← neg_sub, neg_div, abs_neg]

theorem ku_inC_add {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) : ku_InC ϕ (f + g) := by
  obtain ⟨B, hB⟩ := hf.2
  obtain ⟨C, hC⟩ := hg.2
  refine ⟨hf.1.add hg.1, B + C, fun s => ?_⟩
  calc |(f + g) s| ≤ |f s| + |g s| := abs_add_le _ _
    _ ≤ B * ϕ s + C * ϕ s := add_le_add (hB s) (hC s)
    _ = (B + C) * ϕ s := by ring

theorem ku_inC_smul {f : S → ℝ} (hf : ku_InC ϕ f) (r : ℝ) : ku_InC ϕ (r • f) := by
  obtain ⟨B, hB⟩ := hf.2
  refine ⟨hf.1.const_smul r, |r| * B, fun s => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hB s) (abs_nonneg r)

theorem ku_inC_sub {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) : ku_InC ϕ (f - g) := by
  have h := ku_inC_add hf (ku_inC_smul hg (-1))
  rwa [neg_one_smul, ← sub_eq_add_neg] at h

theorem ku_inC_zero : ku_InC ϕ (0 : S → ℝ) :=
  ⟨continuous_const, 0, fun _ => by simp⟩

/-- `ϕ ∈ C_ϕ(S)`, with `‖ϕ‖_ϕ ≤ 1`. -/
theorem ku_inC_self (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) : ku_InC ϕ ϕ :=
  ⟨hϕc, 1, fun s => by rw [abs_of_pos (hϕ s), one_mul]⟩

/-- **Exercise 7.1** (Miao, p. 228; the norm part of p. 212). `‖·‖_ϕ` of (7.23) is a norm on
`C_ϕ(S)`: it is nonnegative, vanishes only at `0`, is absolutely homogeneous and satisfies the
triangle inequality. -/
theorem ku_ex_7_1_norm (hϕ : ∀ s, 0 < ϕ s) {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g)
    (r : ℝ) :
    0 ≤ ku_norm ϕ f ∧ (ku_norm ϕ f = 0 ↔ f = 0) ∧ ku_norm ϕ (r • f) = |r| * ku_norm ϕ f ∧
      ku_norm ϕ (f + g) ≤ ku_norm ϕ f + ku_norm ϕ g := by
  refine ⟨ku_norm_nonneg f, ⟨fun h0 => funext fun s => ?_, fun h => ?_⟩, ?_, ?_⟩
  · have h := ku_abs_le hϕ hf s
    rw [h0, zero_mul] at h
    exact abs_nonpos_iff.1 h
  · subst h
    simp [ku_norm]
  · simp only [ku_norm, Pi.smul_apply, smul_eq_mul, mul_div_assoc, abs_mul]
    rw [Real.mul_iSup_of_nonneg (abs_nonneg r)]
  · refine ku_norm_le hϕ (add_nonneg (ku_norm_nonneg f) (ku_norm_nonneg g)) fun s => ?_
    calc |(f + g) s| ≤ |f s| + |g s| := abs_add_le _ _
      _ ≤ ku_norm ϕ f * ϕ s + ku_norm ϕ g * ϕ s :=
          add_le_add (ku_abs_le hϕ hf s) (ku_abs_le hϕ hg s)
      _ = (ku_norm ϕ f + ku_norm ϕ g) * ϕ s := by ring

/-- `f/ϕ` as a bounded continuous function, for `f ∈ C_ϕ(S)`. -/
noncomputable def ku_toBCF (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ}
    (hf : ku_InC ϕ f) : BoundedContinuousFunction S ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun s => f s / ϕ s)
    (hf.1.div hϕc fun s => (hϕ s).ne') (ku_norm ϕ f)
    (fun s => by rw [Real.norm_eq_abs]; exact le_ciSup (ku_bdd hϕ hf) s)

theorem ku_toBCF_apply (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ}
    (hf : ku_InC ϕ f) (s : S) : ku_toBCF hϕc hϕ hf s = f s / ϕ s := rfl

/-- `h ↦ hϕ` maps bounded continuous functions into `C_ϕ(S)`. -/
theorem ku_inC_mul (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    (h : BoundedContinuousFunction S ℝ) : ku_InC ϕ fun s => h s * ϕ s := by
  refine ⟨h.continuous.mul hϕc, ‖h‖, fun s => ?_⟩
  rw [abs_mul, abs_of_pos (hϕ s)]
  exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using h.norm_coe_le_norm s)
    (hϕ s).le

/-- `‖hϕ − h'ϕ‖_ϕ ≤ dist h h'`. -/
theorem ku_norm_mul_sub_le (hϕ : ∀ s, 0 < ϕ s) (h h' : BoundedContinuousFunction S ℝ) :
    ku_norm ϕ ((fun s => h s * ϕ s) - fun s => h' s * ϕ s) ≤ dist h h' := by
  refine ku_norm_le hϕ dist_nonneg fun s => ?_
  have h1 : |h s - h' s| ≤ dist h h' := by
    rw [← Real.dist_eq]
    exact BoundedContinuousFunction.dist_coe_le_dist s
  simp only [Pi.sub_apply]
  rw [← sub_mul, abs_mul, abs_of_pos (hϕ s)]
  exact mul_le_mul_of_nonneg_right h1 (hϕ s).le

/-- `dist (f/ϕ) (g/ϕ) ≤ ‖f − g‖_ϕ`. -/
theorem ku_dist_toBCF_le (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f g : S → ℝ}
    (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) :
    dist (ku_toBCF hϕc hϕ hf) (ku_toBCF hϕc hϕ hg) ≤ ku_norm ϕ (f - g) := by
  refine (BoundedContinuousFunction.dist_le (ku_norm_nonneg _)).2 fun s => ?_
  rw [Real.dist_eq, ku_toBCF_apply, ku_toBCF_apply, ← sub_div]
  exact le_ciSup (ku_bdd hϕ (ku_inC_sub hf hg)) s

/-- **Exercise 7.1** (Miao, p. 228; completeness, p. 212). `C_ϕ(S)` with `‖·‖_ϕ` is complete: a
sequence in `C_ϕ(S)` that is Cauchy for `‖·‖_ϕ` converges in `‖·‖_ϕ` to some `g ∈ C_ϕ(S)`. -/
theorem ku_ex_7_1 (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f : ℕ → S → ℝ}
    (hf : ∀ n, ku_InC ϕ (f n))
    (hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ku_norm ϕ (f m - f n) < ε) :
    ∃ g, ku_InC ϕ g ∧ Tendsto (fun n => ku_norm ϕ (f n - g)) atTop (𝓝 0) := by
  have hc : CauchySeq fun n => ku_toBCF hϕc hϕ (hf n) :=
    Metric.cauchySeq_iff.2 fun ε hε => by
      obtain ⟨N, hN⟩ := hcau ε hε
      exact ⟨N, fun m hm n hn => (ku_dist_toBCF_le hϕc hϕ (hf m) (hf n)).trans_lt
        (hN m hm n hn)⟩
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨fun s => H s * ϕ s, ku_inC_mul hϕc hϕ H, ?_⟩
  refine squeeze_zero (fun n => ku_norm_nonneg _) (fun n => ?_)
    (tendsto_iff_dist_tendsto_zero.1 hH)
  have he : f n = fun s => ku_toBCF hϕc hϕ (hf n) s * ϕ s := funext fun s => by
    rw [ku_toBCF_apply, div_mul_cancel₀ _ (hϕ s).ne']
  have h := ku_norm_mul_sub_le hϕ (ku_toBCF hϕc hϕ (hf n)) H
  rwa [← he] at h

/-- The Contraction Mapping Theorem on `(C_ϕ(S), ‖·‖_ϕ)` (Miao, p. 213, as used in the proof of
Theorem 7.3.6 and on p. 216): if `T` maps `C_ϕ(S)` into itself and
`‖Tf − Tg‖_ϕ ≤ θ‖f − g‖_ϕ` with `0 ≤ θ < 1`, then `T` has exactly one fixed point in
`C_ϕ(S)`. -/
theorem ku_exists_unique_fixedPoint (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hT : ∀ f, ku_InC ϕ f → ku_InC ϕ (T f)) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcon : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → ku_norm ϕ (T f - T g) ≤ θ * ku_norm ϕ (f - g)) :
    ∃! V, ku_InC ϕ V ∧ T V = V := by
  -- the conjugate operator on bounded continuous functions
  let T' : BoundedContinuousFunction S ℝ → BoundedContinuousFunction S ℝ := fun h =>
    ku_toBCF hϕc hϕ (hT _ (ku_inC_mul hϕc hϕ h))
  have hT' : ContractingWith ⟨θ, hθ0⟩ T' := by
    refine ⟨by exact_mod_cast hθ1, LipschitzWith.of_dist_le_mul fun h h' => ?_⟩
    calc dist (T' h) (T' h')
        ≤ ku_norm ϕ (T (fun s => h s * ϕ s) - T fun s => h' s * ϕ s) :=
          ku_dist_toBCF_le hϕc hϕ _ _
      _ ≤ θ * ku_norm ϕ ((fun s => h s * ϕ s) - fun s => h' s * ϕ s) :=
          hcon _ _ (ku_inC_mul hϕc hϕ h) (ku_inC_mul hϕc hϕ h')
      _ ≤ θ * dist h h' := mul_le_mul_of_nonneg_left (ku_norm_mul_sub_le hϕ h h') hθ0
  set h0 := ContractingWith.fixedPoint T' hT' with hh0
  have hfix : T' h0 = h0 := ContractingWith.fixedPoint_isFixedPt (f := T') hT'
  have hfixV : T (fun s => h0 s * ϕ s) = fun s => h0 s * ϕ s := funext fun s => by
    have h1 := congrArg (fun h : BoundedContinuousFunction S ℝ => h s) hfix
    simp only [T', ku_toBCF_apply] at h1
    rw [← h1, div_mul_cancel₀ _ (hϕ s).ne']
  refine ⟨fun s => h0 s * ϕ s, ⟨ku_inC_mul hϕc hϕ h0, hfixV⟩, fun W ⟨hW, hWfix⟩ => ?_⟩
  have hWe : (fun s => ku_toBCF hϕc hϕ hW s * ϕ s) = W := funext fun s => by
    rw [ku_toBCF_apply, div_mul_cancel₀ _ (hϕ s).ne']
  have hWfix' : Function.IsFixedPt T' (ku_toBCF hϕc hϕ hW) := by
    refine BoundedContinuousFunction.ext fun s => ?_
    simp only [T', ku_toBCF_apply]
    have hWe' : (fun s => W s / ϕ s * ϕ s) = W := funext fun s => div_mul_cancel₀ _ (hϕ s).ne'
    rw [hWe', hWfix]
  have hWh : ku_toBCF hϕc hϕ hW = h0 := ContractingWith.fixedPoint_unique hT' hWfix'
  rw [← hWe, hWh]

/-- Comparable weights: if `0 ≤ ψ ≤ cϕ` then `C_ψ(S) ⊆ C_ϕ(S)`. -/
theorem ku_inC_of_le {ψ : S → ℝ} {c : ℝ} (hψ : ∀ s, 0 ≤ ψ s)
    (hle : ∀ s, ψ s ≤ c * ϕ s) {f : S → ℝ} (hf : ku_InC ψ f) : ku_InC ϕ f := by
  obtain ⟨B, hB⟩ := hf.2
  refine ⟨hf.1, max B 0 * c, fun s => ?_⟩
  calc |f s| ≤ B * ψ s := hB s
    _ ≤ max B 0 * ψ s := mul_le_mul_of_nonneg_right (le_max_left _ _) (hψ s)
    _ ≤ max B 0 * (c * ϕ s) := mul_le_mul_of_nonneg_left (hle s) (le_max_right _ _)
    _ = max B 0 * c * ϕ s := by ring



/-- Miao, proof of Theorem 7.3.6, p. 213: from (a) and (b),
`Tf ≤ Tg + θ‖f − g‖_ϕ ϕ` for `f, g ∈ C_ϕ(S)`. -/
theorem ku_le_add_of_disc (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {T : (S → ℝ) → S → ℝ}
    (hmono : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ}
    (hdisc : ∀ f, ku_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) (s : S) :
    T f s ≤ T g s + θ * ku_norm ϕ (f - g) * ϕ s := by
  have hfg := ku_abs_le hϕ (ku_inC_sub hf hg)
  rcases (ku_norm_nonneg (ϕ := ϕ) (f - g)).eq_or_lt with h0 | hpos
  · have hle : f ≤ g := fun t => by
      have h1 := hfg t
      rw [← h0, zero_mul] at h1
      have h2 := le_abs_self ((f - g) t)
      simp only [Pi.sub_apply] at h1 h2
      linarith
    rw [← h0, mul_zero, zero_mul, add_zero]
    exact hmono f g hf hg hle s
  · set a := ku_norm ϕ (f - g)
    have hle : f ≤ g + a • ϕ := fun t => by
      have h1 := hfg t
      have h2 := le_abs_self ((f - g) t)
      simp only [Pi.sub_apply] at h1 h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    have h1 := hmono f (g + a • ϕ) hf (ku_inC_add hg (ku_inC_smul (ku_inC_self hϕc hϕ) a)) hle s
    have h2 := hdisc g hg a hpos s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
    linarith

/-- Miao, proof of Theorem 7.3.6, p. 213: (a) and (b) make `T` a contraction with modulus `θ`,
`‖Tf − Tg‖_ϕ ≤ θ‖f − g‖_ϕ` on `C_ϕ(S)`. -/
theorem ku_thm_7_3_6_contraction (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hmono : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → f ≤ g → T f ≤ T g)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hdisc : ∀ f, ku_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) :
    ku_norm ϕ (T f - T g) ≤ θ * ku_norm ϕ (f - g) := by
  refine ku_norm_le hϕ (mul_nonneg hθ0.le (ku_norm_nonneg _)) fun s => ?_
  have h1 := ku_le_add_of_disc hϕc hϕ hmono hdisc hf hg s
  have h2 := ku_le_add_of_disc hϕc hϕ hmono hdisc hg hf s
  rw [ku_norm_sub_comm g f] at h2
  simp only [Pi.sub_apply]
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- **Theorem 7.3.6** (Weighted Contraction Mapping Theorem, Miao, p. 212). Let
`T : C_ϕ(S) → C_ϕ(S)` be (a) monotone and (b) discounting, `T(f + aϕ) ≤ Tf + θaϕ` for some
`θ ∈ (0, 1)` and all `a > 0`. Then `T` is a contraction with modulus `θ` and has a unique fixed
point in `C_ϕ(S)`. Condition (c), `T0 ∈ C_ϕ(S)`, is part of `T : C_ϕ(S) → C_ϕ(S)`
(`ku_thm_7_3_6_c`). -/
theorem ku_thm_7_3_6 (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {T : (S → ℝ) → S → ℝ}
    (hT : ∀ f, ku_InC ϕ f → ku_InC ϕ (T f))
    (hmono : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
    (hdisc : ∀ f, ku_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ) :
    (∀ f g, ku_InC ϕ f → ku_InC ϕ g → ku_norm ϕ (T f - T g) ≤ θ * ku_norm ϕ (f - g)) ∧
      ∃! V, ku_InC ϕ V ∧ T V = V := by
  have hcon : ∀ f g, ku_InC ϕ f → ku_InC ϕ g →
      ku_norm ϕ (T f - T g) ≤ θ * ku_norm ϕ (f - g) := fun f g hf hg =>
    ku_thm_7_3_6_contraction hϕc hϕ hmono hθ0 hdisc hf hg
  exact ⟨hcon, ku_exists_unique_fixedPoint hϕc hϕ hT hθ0.le hθ1 hcon⟩

/-- **Theorem 7.3.6 (c)** (Miao, p. 213). For `T : C_ϕ(S) → C_ϕ(S)`, (c) `T0 ∈ C_ϕ(S)` holds. -/
theorem ku_thm_7_3_6_c {T : (S → ℝ) → S → ℝ} (hT : ∀ f, ku_InC ϕ f → ku_InC ϕ (T f)) :
    ku_InC ϕ (T 0) :=
  hT 0 ku_inC_zero

/-- Miao, proof of Theorem 7.3.6, p. 213 ("Condition (c) ensures that `‖Tf‖_ϕ < ∞`"). If `T`
maps `C_ϕ(S)` into continuous functions and satisfies (a)–(c), then `T` maps `C_ϕ(S)` into
itself, with `‖Tf‖_ϕ ≤ ‖T0‖_ϕ + θ‖f‖_ϕ`. -/
theorem ku_thm_7_3_6_selfMap (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hTc : ∀ f, ku_InC ϕ f → Continuous (T f))
    (hmono : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ}
    (hdisc : ∀ f, ku_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    (h0 : ku_InC ϕ (T 0)) {f : S → ℝ} (hf : ku_InC ϕ f) :
    ku_InC ϕ (T f) ∧ ∀ s, |T f s| ≤ (ku_norm ϕ (T 0) + θ * ku_norm ϕ f) * ϕ s := by
  have hb : ∀ s, |T f s| ≤ (ku_norm ϕ (T 0) + θ * ku_norm ϕ f) * ϕ s := fun s => by
    have h1 := ku_le_add_of_disc hϕc hϕ hmono hdisc hf ku_inC_zero s
    have h2 := ku_le_add_of_disc hϕc hϕ hmono hdisc ku_inC_zero hf s
    have h3 := ku_abs_le hϕ h0 s
    rw [sub_zero] at h1
    rw [ku_norm_sub_comm, sub_zero] at h2
    rw [abs_le] at h3 ⊢
    constructor <;> nlinarith
  exact ⟨⟨hTc f hf, _, hb⟩, hb⟩

/-- **Theorem 7.3.6** in the form its proof establishes (Miao, pp. 212–213): if `T` maps
`C_ϕ(S)` into continuous functions and satisfies (a) monotonicity, (b) discounting with
`θ ∈ (0, 1)`, and (c) `T0 ∈ C_ϕ(S)`, then `T` maps `C_ϕ(S)` into itself, is a contraction with
modulus `θ`, and has a unique fixed point in `C_ϕ(S)`. -/
theorem ku_thm_7_3_6_of_continuous (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hTc : ∀ f, ku_InC ϕ f → Continuous (T f))
    (hmono : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
    (hdisc : ∀ f, ku_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    (h0 : ku_InC ϕ (T 0)) :
    (∀ f, ku_InC ϕ f → ku_InC ϕ (T f)) ∧
      (∀ f g, ku_InC ϕ f → ku_InC ϕ g → ku_norm ϕ (T f - T g) ≤ θ * ku_norm ϕ (f - g)) ∧
      ∃! V, ku_InC ϕ V ∧ T V = V := by
  have hT : ∀ f, ku_InC ϕ f → ku_InC ϕ (T f) := fun f hf =>
    (ku_thm_7_3_6_selfMap hϕc hϕ hTc hmono hdisc h0 hf).1
  exact ⟨hT, ku_thm_7_3_6 hϕc hϕ hT hmono hθ0 hθ1 hdisc⟩

end Miao.RecursiveUtility
