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
# The weighted space `C_ϕ(S)` and Exercise 7.1

Miao §7.3.2, p. 212, (7.23), and Exercise 7.1, p. 228. For a continuous weight
`ϕ : S → ℝ₊₊` on a topological space `S`, `C_ϕ(S)` (`wn_InC`) is the set of continuous `f` with
`sup_s |f(s)/ϕ(s)| < ∞`, written as a bound `|f(s)| ≤ Bϕ(s)` (equivalent: `wn_inC_iff`), and
`‖f‖_ϕ = sup_s |f(s)/ϕ(s)|` (`wn_norm`, (7.23)).

* `ex_7_1_norm`: `‖·‖_ϕ` is a norm on `C_ϕ(S)`, which is closed under the vector operations
  (`wn_inC_add`, `wn_inC_sub`, `wn_inC_smul`, `wn_inC_zero`; `ϕ ∈ C_ϕ(S)`: `wn_inC_self`).
* `ex_7_1`: `C_ϕ(S)` is complete: a `‖·‖_ϕ`-Cauchy sequence in `C_ϕ(S)` converges in `‖·‖_ϕ` to an
  element of `C_ϕ(S)`. The proof transports to bounded continuous functions by `f ↦ f/ϕ`.
* `wn_exists_unique_fixedPoint`: the Contraction Mapping Theorem on `(C_ϕ(S), ‖·‖_ϕ)`: a self-map
  of `C_ϕ(S)` that contracts `‖·‖_ϕ` with modulus `θ < 1` has exactly one fixed point there.
* `wn_inC_of_le`: comparable weights (`ψ ≤ cϕ`) give nested spaces; equivalent weights give the
  same space (used in Exercise 7.3).
-/

namespace Miao.InfiniteHorizonDP

open Filter Topology

variable {S : Type*} [TopologicalSpace S]

/-- Miao, p. 212: `f ∈ C_ϕ(S)`: `f` is continuous and `sup_s |f(s)/ϕ(s)| < ∞`. The finiteness is
stated as a bound `|f(s)| ≤ Bϕ(s)`; for `ϕ > 0` this is the same (`wn_inC_iff`). -/
def wn_InC (ϕ : S → ℝ) (f : S → ℝ) : Prop :=
  Continuous f ∧ ∃ B, ∀ s, |f s| ≤ B * ϕ s

/-- Miao, (7.23), p. 212: the weighted sup norm `‖f‖_ϕ = sup_s |f(s)/ϕ(s)|`. -/
noncomputable def wn_norm (ϕ : S → ℝ) (f : S → ℝ) : ℝ := ⨆ s, |f s / ϕ s|

variable {ϕ : S → ℝ}

/-- Miao, p. 212: for `ϕ > 0`, the bound in `wn_InC` is `sup_s |f(s)/ϕ(s)| < ∞`. -/
theorem wn_inC_iff (hϕ : ∀ s, 0 < ϕ s) (f : S → ℝ) :
    wn_InC ϕ f ↔ Continuous f ∧ BddAbove (Set.range fun s => |f s / ϕ s|) := by
  refine and_congr_right fun _ => ⟨fun ⟨B, hB⟩ => ⟨B, ?_⟩, fun ⟨C, hC⟩ => ⟨C, fun s => ?_⟩⟩
  · rintro _ ⟨s, rfl⟩
    change |f s / ϕ s| ≤ B
    rw [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)]
    exact hB s
  · have h : |f s / ϕ s| ≤ C := hC ⟨s, rfl⟩
    rwa [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)] at h

theorem wn_bdd (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ} (hf : wn_InC ϕ f) :
    BddAbove (Set.range fun s => |f s / ϕ s|) :=
  ((wn_inC_iff hϕ f).1 hf).2

omit [TopologicalSpace S] in
theorem wn_norm_nonneg (f : S → ℝ) : 0 ≤ wn_norm ϕ f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- On `C_ϕ(S)`, `|f(s)| ≤ ‖f‖_ϕ ϕ(s)`. -/
theorem wn_abs_le (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ} (hf : wn_InC ϕ f) (s : S) :
    |f s| ≤ wn_norm ϕ f * ϕ s := by
  have h : |f s / ϕ s| ≤ wn_norm ϕ f := le_ciSup (wn_bdd hϕ hf) s
  rwa [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)] at h

omit [TopologicalSpace S] in
/-- `|f| ≤ Cϕ` with `C ≥ 0` gives `‖f‖_ϕ ≤ C`. -/
theorem wn_norm_le (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s, |f s| ≤ C * ϕ s) : wn_norm ϕ f ≤ C :=
  Real.iSup_le (fun s => by rw [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)]; exact h s) hC

omit [TopologicalSpace S] in
theorem wn_norm_sub_comm (f g : S → ℝ) : wn_norm ϕ (f - g) = wn_norm ϕ (g - f) := by
  simp only [wn_norm, Pi.sub_apply]
  congr 1
  funext s
  rw [← neg_sub, neg_div, abs_neg]

theorem wn_inC_add {f g : S → ℝ} (hf : wn_InC ϕ f) (hg : wn_InC ϕ g) : wn_InC ϕ (f + g) := by
  obtain ⟨B, hB⟩ := hf.2
  obtain ⟨C, hC⟩ := hg.2
  refine ⟨hf.1.add hg.1, B + C, fun s => ?_⟩
  calc |(f + g) s| ≤ |f s| + |g s| := abs_add_le _ _
    _ ≤ B * ϕ s + C * ϕ s := add_le_add (hB s) (hC s)
    _ = (B + C) * ϕ s := by ring

theorem wn_inC_smul {f : S → ℝ} (hf : wn_InC ϕ f) (r : ℝ) : wn_InC ϕ (r • f) := by
  obtain ⟨B, hB⟩ := hf.2
  refine ⟨hf.1.const_smul r, |r| * B, fun s => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hB s) (abs_nonneg r)

theorem wn_inC_sub {f g : S → ℝ} (hf : wn_InC ϕ f) (hg : wn_InC ϕ g) : wn_InC ϕ (f - g) := by
  have h := wn_inC_add hf (wn_inC_smul hg (-1))
  rwa [neg_one_smul, ← sub_eq_add_neg] at h

theorem wn_inC_zero : wn_InC ϕ (0 : S → ℝ) :=
  ⟨continuous_const, 0, fun _ => by simp⟩

/-- `ϕ ∈ C_ϕ(S)`, with `‖ϕ‖_ϕ ≤ 1`. -/
theorem wn_inC_self (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) : wn_InC ϕ ϕ :=
  ⟨hϕc, 1, fun s => by rw [abs_of_pos (hϕ s), one_mul]⟩

/-- **Exercise 7.1** (Miao, p. 228; the norm part of p. 212). `‖·‖_ϕ` of (7.23) is a norm on
`C_ϕ(S)`: it is nonnegative, vanishes only at `0`, is absolutely homogeneous and satisfies the
triangle inequality. -/
theorem ex_7_1_norm (hϕ : ∀ s, 0 < ϕ s) {f g : S → ℝ} (hf : wn_InC ϕ f) (hg : wn_InC ϕ g)
    (r : ℝ) :
    0 ≤ wn_norm ϕ f ∧ (wn_norm ϕ f = 0 ↔ f = 0) ∧ wn_norm ϕ (r • f) = |r| * wn_norm ϕ f ∧
      wn_norm ϕ (f + g) ≤ wn_norm ϕ f + wn_norm ϕ g := by
  refine ⟨wn_norm_nonneg f, ⟨fun h0 => funext fun s => ?_, fun h => ?_⟩, ?_, ?_⟩
  · have h := wn_abs_le hϕ hf s
    rw [h0, zero_mul] at h
    exact abs_nonpos_iff.1 h
  · subst h
    simp [wn_norm]
  · simp only [wn_norm, Pi.smul_apply, smul_eq_mul, mul_div_assoc, abs_mul]
    rw [Real.mul_iSup_of_nonneg (abs_nonneg r)]
  · refine wn_norm_le hϕ (add_nonneg (wn_norm_nonneg f) (wn_norm_nonneg g)) fun s => ?_
    calc |(f + g) s| ≤ |f s| + |g s| := abs_add_le _ _
      _ ≤ wn_norm ϕ f * ϕ s + wn_norm ϕ g * ϕ s :=
          add_le_add (wn_abs_le hϕ hf s) (wn_abs_le hϕ hg s)
      _ = (wn_norm ϕ f + wn_norm ϕ g) * ϕ s := by ring

/-- `f/ϕ` as a bounded continuous function, for `f ∈ C_ϕ(S)`. -/
noncomputable def wn_toBCF (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ}
    (hf : wn_InC ϕ f) : BoundedContinuousFunction S ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun s => f s / ϕ s)
    (hf.1.div hϕc fun s => (hϕ s).ne') (wn_norm ϕ f)
    (fun s => by rw [Real.norm_eq_abs]; exact le_ciSup (wn_bdd hϕ hf) s)

theorem wn_toBCF_apply (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ}
    (hf : wn_InC ϕ f) (s : S) : wn_toBCF hϕc hϕ hf s = f s / ϕ s := rfl

/-- `h ↦ hϕ` maps bounded continuous functions into `C_ϕ(S)`. -/
theorem wn_inC_mul (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    (h : BoundedContinuousFunction S ℝ) : wn_InC ϕ fun s => h s * ϕ s := by
  refine ⟨h.continuous.mul hϕc, ‖h‖, fun s => ?_⟩
  rw [abs_mul, abs_of_pos (hϕ s)]
  exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using h.norm_coe_le_norm s)
    (hϕ s).le

/-- `‖hϕ − h'ϕ‖_ϕ ≤ dist h h'`. -/
theorem wn_norm_mul_sub_le (hϕ : ∀ s, 0 < ϕ s) (h h' : BoundedContinuousFunction S ℝ) :
    wn_norm ϕ ((fun s => h s * ϕ s) - fun s => h' s * ϕ s) ≤ dist h h' := by
  refine wn_norm_le hϕ dist_nonneg fun s => ?_
  have h1 : |h s - h' s| ≤ dist h h' := by
    rw [← Real.dist_eq]
    exact BoundedContinuousFunction.dist_coe_le_dist s
  simp only [Pi.sub_apply]
  rw [← sub_mul, abs_mul, abs_of_pos (hϕ s)]
  exact mul_le_mul_of_nonneg_right h1 (hϕ s).le

/-- `dist (f/ϕ) (g/ϕ) ≤ ‖f − g‖_ϕ`. -/
theorem wn_dist_toBCF_le (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f g : S → ℝ}
    (hf : wn_InC ϕ f) (hg : wn_InC ϕ g) :
    dist (wn_toBCF hϕc hϕ hf) (wn_toBCF hϕc hϕ hg) ≤ wn_norm ϕ (f - g) := by
  refine (BoundedContinuousFunction.dist_le (wn_norm_nonneg _)).2 fun s => ?_
  rw [Real.dist_eq, wn_toBCF_apply, wn_toBCF_apply, ← sub_div]
  exact le_ciSup (wn_bdd hϕ (wn_inC_sub hf hg)) s

/-- **Exercise 7.1** (Miao, p. 228; completeness, p. 212). `C_ϕ(S)` with `‖·‖_ϕ` is complete: a
sequence in `C_ϕ(S)` that is Cauchy for `‖·‖_ϕ` converges in `‖·‖_ϕ` to some `g ∈ C_ϕ(S)`. -/
theorem ex_7_1 (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f : ℕ → S → ℝ}
    (hf : ∀ n, wn_InC ϕ (f n))
    (hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, wn_norm ϕ (f m - f n) < ε) :
    ∃ g, wn_InC ϕ g ∧ Tendsto (fun n => wn_norm ϕ (f n - g)) atTop (𝓝 0) := by
  have hc : CauchySeq fun n => wn_toBCF hϕc hϕ (hf n) :=
    Metric.cauchySeq_iff.2 fun ε hε => by
      obtain ⟨N, hN⟩ := hcau ε hε
      exact ⟨N, fun m hm n hn => (wn_dist_toBCF_le hϕc hϕ (hf m) (hf n)).trans_lt
        (hN m hm n hn)⟩
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨fun s => H s * ϕ s, wn_inC_mul hϕc hϕ H, ?_⟩
  refine squeeze_zero (fun n => wn_norm_nonneg _) (fun n => ?_)
    (tendsto_iff_dist_tendsto_zero.1 hH)
  have he : f n = fun s => wn_toBCF hϕc hϕ (hf n) s * ϕ s := funext fun s => by
    rw [wn_toBCF_apply, div_mul_cancel₀ _ (hϕ s).ne']
  have h := wn_norm_mul_sub_le hϕ (wn_toBCF hϕc hϕ (hf n)) H
  rwa [← he] at h

/-- The Contraction Mapping Theorem on `(C_ϕ(S), ‖·‖_ϕ)` (Miao, p. 213, as used in the proof of
Theorem 7.3.6 and on p. 216): if `T` maps `C_ϕ(S)` into itself and
`‖Tf − Tg‖_ϕ ≤ θ‖f − g‖_ϕ` with `0 ≤ θ < 1`, then `T` has exactly one fixed point in
`C_ϕ(S)`. -/
theorem wn_exists_unique_fixedPoint (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hT : ∀ f, wn_InC ϕ f → wn_InC ϕ (T f)) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcon : ∀ f g, wn_InC ϕ f → wn_InC ϕ g → wn_norm ϕ (T f - T g) ≤ θ * wn_norm ϕ (f - g)) :
    ∃! V, wn_InC ϕ V ∧ T V = V := by
  -- the conjugate operator on bounded continuous functions
  let T' : BoundedContinuousFunction S ℝ → BoundedContinuousFunction S ℝ := fun h =>
    wn_toBCF hϕc hϕ (hT _ (wn_inC_mul hϕc hϕ h))
  have hT' : ContractingWith ⟨θ, hθ0⟩ T' := by
    refine ⟨by exact_mod_cast hθ1, LipschitzWith.of_dist_le_mul fun h h' => ?_⟩
    calc dist (T' h) (T' h')
        ≤ wn_norm ϕ (T (fun s => h s * ϕ s) - T fun s => h' s * ϕ s) :=
          wn_dist_toBCF_le hϕc hϕ _ _
      _ ≤ θ * wn_norm ϕ ((fun s => h s * ϕ s) - fun s => h' s * ϕ s) :=
          hcon _ _ (wn_inC_mul hϕc hϕ h) (wn_inC_mul hϕc hϕ h')
      _ ≤ θ * dist h h' := mul_le_mul_of_nonneg_left (wn_norm_mul_sub_le hϕ h h') hθ0
  set h0 := ContractingWith.fixedPoint T' hT' with hh0
  have hfix : T' h0 = h0 := ContractingWith.fixedPoint_isFixedPt (f := T') hT'
  have hfixV : T (fun s => h0 s * ϕ s) = fun s => h0 s * ϕ s := funext fun s => by
    have h1 := congrArg (fun h : BoundedContinuousFunction S ℝ => h s) hfix
    simp only [T', wn_toBCF_apply] at h1
    rw [← h1, div_mul_cancel₀ _ (hϕ s).ne']
  refine ⟨fun s => h0 s * ϕ s, ⟨wn_inC_mul hϕc hϕ h0, hfixV⟩, fun W ⟨hW, hWfix⟩ => ?_⟩
  have hWe : (fun s => wn_toBCF hϕc hϕ hW s * ϕ s) = W := funext fun s => by
    rw [wn_toBCF_apply, div_mul_cancel₀ _ (hϕ s).ne']
  have hWfix' : Function.IsFixedPt T' (wn_toBCF hϕc hϕ hW) := by
    refine BoundedContinuousFunction.ext fun s => ?_
    simp only [T', wn_toBCF_apply]
    have hWe' : (fun s => W s / ϕ s * ϕ s) = W := funext fun s => div_mul_cancel₀ _ (hϕ s).ne'
    rw [hWe', hWfix]
  have hWh : wn_toBCF hϕc hϕ hW = h0 := ContractingWith.fixedPoint_unique hT' hWfix'
  rw [← hWe, hWh]

/-- Comparable weights: if `0 ≤ ψ ≤ cϕ` then `C_ψ(S) ⊆ C_ϕ(S)`. -/
theorem wn_inC_of_le {ψ : S → ℝ} {c : ℝ} (hψ : ∀ s, 0 ≤ ψ s)
    (hle : ∀ s, ψ s ≤ c * ϕ s) {f : S → ℝ} (hf : wn_InC ψ f) : wn_InC ϕ f := by
  obtain ⟨B, hB⟩ := hf.2
  refine ⟨hf.1, max B 0 * c, fun s => ?_⟩
  calc |f s| ≤ B * ψ s := hB s
    _ ≤ max B 0 * ψ s := mul_le_mul_of_nonneg_right (le_max_left _ _) (hψ s)
    _ ≤ max B 0 * (c * ϕ s) := mul_le_mul_of_nonneg_left (hle s) (le_max_right _ _)
    _ = max B 0 * c * ϕ s := by ring

end Miao.InfiniteHorizonDP
