/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.WNSpace
import InfiniteHorizonDP.SLPMaximum

/-!
# Duran's weighted-norm approach: (7.24)–(7.28) and Exercise 7.2

Miao §7.3.2, pp. 214–216. For the deterministic problem (7.24) with continuous `u`
(Assumption 7.3.6) and a nonempty, compact-valued, continuous `Γ` (Assumption 7.3.7), the
Bellman operator (7.25) is `Tf(x) = sup_{y ∈ Γ(x)} u(x, y) + βf(y)` (`wn_duranT`, through the
copied `maxValue`). The state space `X` is any metric space (the book's `X ⊆ ℝ^{n_x}`).

* `ex_7_2_attained`, `ex_7_2`: for continuous `f, g` the sup in (7.25) is attained (so finite),
  and `|Tf − Tg|(x) ≤ β sup_{x' ∈ Γ(x)} |f − g|(x')`, where the right-hand sup is attained too.
  Only nonemptiness and compactness of `Γ(x)` are used.
* `eq_7_26`: `|Tf − Tg|(x) ≤ β sup_{x' ∈ Γ(x)} (ϕ(x')/ϕ(x)) ‖f − g‖_ϕ ϕ(x)`.
* `eq_7_27_iff`: (7.27) at `x` is equivalent to `βϕ(x')/ϕ(x) ≤ θ` for all `x' ∈ Γ(x)`.
* `wn_duran_contraction`: under (7.27), `‖Tf − Tg‖_ϕ ≤ θ‖f − g‖_ϕ` on `C_ϕ(X)`. We add `θ ≥ 0`,
  which (7.27) implies when `X` is nonempty.
* `wn_duran_continuous`: "continuity is routine": `Tf` is continuous for continuous `f`, by the
  Theorem of the Maximum (`theorem_3_6`, copied from SLP).
* `eq_7_28`: under (7.27) and (7.28) `‖T0‖_ϕ < ∞`, `T` maps `C_ϕ(X)` into itself with
  `‖Tf‖_ϕ ≤ θ‖f‖_ϕ + ‖T0‖_ϕ`. The book bounds `Tf` only from above; the bound on `|Tf|` uses
  `|Tf − T0| ≤ θ‖f‖_ϕϕ` from (7.26).
* `wn_duran_fixed_point`: (7.27) with `θ < 1` and (7.28) give a unique fixed point of `T` in
  `C_ϕ(X)`.
-/

namespace Miao.InfiniteHorizonDP

variable {X : Type*} [MetricSpace X]

/-- **Assumption 7.3.6** (Miao, p. 215): `u : X × X → ℝ` is continuous. -/
def assumption_7_3_6 (u : X × X → ℝ) : Prop := Continuous u

/-- **Assumption 7.3.7** (Miao, p. 215): `Γ` is nonempty, compact-valued and continuous (lower
and upper hemicontinuous; `IsLHC` includes nonemptiness). -/
def assumption_7_3_7 (Γ : X → Set X) : Prop :=
  (∀ x, IsCompact (Γ x)) ∧ (∀ x, IsLHC Γ x) ∧ ∀ x, IsUHC Γ x

/-- Miao, (7.25), p. 215: the Bellman operator `Tf(x) = sup_{y ∈ Γ(x)} u(x, y) + βf(y)`. -/
noncomputable def wn_duranT (u : X × X → ℝ) (Γ : X → Set X) (β : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  maxValue (fun p => u p + β * f p.2) Γ x

variable {u : X × X → ℝ} {Γ : X → Set X} {β : ℝ}

theorem wn_obj_continuous (hu : Continuous u) {f : X → ℝ} (hf : Continuous f) :
    Continuous fun p : X × X => u p + β * f p.2 :=
  hu.add (continuous_const.mul (hf.comp continuous_snd))

/-- **Exercise 7.2** (Miao, p. 228; the sup in (7.25)). For continuous `f` and nonempty compact
`Γ(x)`, the sup in (7.25) is attained, so `Tf(x)` is finite. -/
theorem ex_7_2_attained (hu : Continuous u) (hc : ∀ x, IsCompact (Γ x))
    (hne : ∀ x, (Γ x).Nonempty) {f : X → ℝ} (hf : Continuous f) (x : X) :
    ∃ y ∈ Γ x, wn_duranT u Γ β f x = u (x, y) + β * f y ∧
      ∀ z ∈ Γ x, u (x, z) + β * f z ≤ wn_duranT u Γ β f x := by
  obtain ⟨y, hy, hval, hmax⟩ :=
    exists_argmax (wn_obj_continuous (β := β) hu hf).continuousOn (hc x) (hne x)
  exact ⟨y, hy, hval.symm, fun z hz => (hmax z hz).trans hval.le⟩

/-- **Exercise 7.2** (Miao, p. 228; first line of (7.26), p. 215). For continuous `f, g` and
`β ≥ 0`, `|Tf − Tg|(x) ≤ β sup_{x' ∈ Γ(x)} |f(x') − g(x')|`. -/
theorem ex_7_2 (hu : Continuous u) (hc : ∀ x, IsCompact (Γ x)) (hne : ∀ x, (Γ x).Nonempty)
    (hβ : 0 ≤ β) {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) (x : X) :
    |wn_duranT u Γ β f x - wn_duranT u Γ β g x| ≤
      β * maxValue (fun p : X × X => |f p.2 - g p.2|) Γ x := by
  have hd : Continuous fun p : X × X => |f p.2 - g p.2| :=
    ((hf.comp continuous_snd).sub (hg.comp continuous_snd)).abs
  have hle : ∀ y ∈ Γ x, |f y - g y| ≤ maxValue (fun p : X × X => |f p.2 - g p.2|) Γ x :=
    fun y hy => le_maxValue (f := fun p : X × X => |f p.2 - g p.2|) hd.continuousOn (hc x) hy
  obtain ⟨y, hy, hfy, -⟩ := ex_7_2_attained (β := β) hu hc hne hf x
  obtain ⟨z, hz, hgz, -⟩ := ex_7_2_attained (β := β) hu hc hne hg x
  obtain ⟨-, -, -, hgmax⟩ := ex_7_2_attained (β := β) hu hc hne hg x
  obtain ⟨-, -, -, hfmax⟩ := ex_7_2_attained (β := β) hu hc hne hf x
  have h1 := hgmax y hy
  have h2 := hfmax z hz
  have h3 := mul_le_mul_of_nonneg_left ((le_abs_self (f y - g y)).trans (hle y hy)) hβ
  have h4 := mul_le_mul_of_nonneg_left ((neg_le_abs (f z - g z)).trans (hle z hz)) hβ
  rw [abs_sub_le_iff]
  constructor <;> nlinarith

variable {ϕ : X → ℝ}

/-- Miao, (7.26), p. 215: for `f, g ∈ C_ϕ(X)`,
`|Tf − Tg|(x) ≤ β sup_{x' ∈ Γ(x)} (ϕ(x')/ϕ(x)) ‖f − g‖_ϕ ϕ(x)`. -/
theorem eq_7_26 (hu : Continuous u) (hc : ∀ x, IsCompact (Γ x)) (hne : ∀ x, (Γ x).Nonempty)
    (hβ : 0 ≤ β) (hϕc : Continuous ϕ) (hϕ : ∀ x, 0 < ϕ x) {f g : X → ℝ} (hf : wn_InC ϕ f)
    (hg : wn_InC ϕ g) (x : X) :
    |wn_duranT u Γ β f x - wn_duranT u Γ β g x| ≤
      β * maxValue (fun p : X × X => ϕ p.2 / ϕ p.1) Γ x * wn_norm ϕ (f - g) * ϕ x := by
  have hd : Continuous fun p : X × X => |f p.2 - g p.2| :=
    ((hf.1.comp continuous_snd).sub (hg.1.comp continuous_snd)).abs
  have hr : Continuous fun p : X × X => ϕ p.2 / ϕ p.1 :=
    (hϕc.comp continuous_snd).div (hϕc.comp continuous_fst) fun p => (hϕ p.1).ne'
  obtain ⟨y, hy, hval, -⟩ := exists_argmax hd.continuousOn (hc x) (hne x)
  have hy1 : |f y - g y| ≤ wn_norm ϕ (f - g) * ϕ y := wn_abs_le hϕ (wn_inC_sub hf hg) y
  have hy2 : ϕ y / ϕ x ≤ maxValue (fun p : X × X => ϕ p.2 / ϕ p.1) Γ x :=
    le_maxValue (f := fun p : X × X => ϕ p.2 / ϕ p.1) hr.continuousOn (hc x) hy
  have hy3 : ϕ y = ϕ y / ϕ x * ϕ x := (div_mul_cancel₀ _ (hϕ x).ne').symm
  have hM : maxValue (fun p : X × X => |f p.2 - g p.2|) Γ x ≤
      maxValue (fun p : X × X => ϕ p.2 / ϕ p.1) Γ x * wn_norm ϕ (f - g) * ϕ x := by
    rw [← hval]
    calc |f y - g y| ≤ wn_norm ϕ (f - g) * (ϕ y / ϕ x * ϕ x) := hy3 ▸ hy1
      _ = ϕ y / ϕ x * wn_norm ϕ (f - g) * ϕ x := by ring
      _ ≤ maxValue (fun p : X × X => ϕ p.2 / ϕ p.1) Γ x * wn_norm ϕ (f - g) * ϕ x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hy2 (wn_norm_nonneg _))
            (hϕ x).le
  calc |wn_duranT u Γ β f x - wn_duranT u Γ β g x|
      ≤ β * maxValue (fun p : X × X => |f p.2 - g p.2|) Γ x := ex_7_2 hu hc hne hβ hf.1 hg.1 x
    _ ≤ β * (maxValue (fun p : X × X => ϕ p.2 / ϕ p.1) Γ x * wn_norm ϕ (f - g) * ϕ x) :=
        mul_le_mul_of_nonneg_left hM hβ
    _ = _ := by ring

/-- Miao, (7.27), p. 215: `β sup_{x' ∈ Γ(x)} ϕ(x')/ϕ(x) ≤ θ` holds iff
`βϕ(x')/ϕ(x) ≤ θ` for every `x' ∈ Γ(x)` (the sup is attained). -/
theorem eq_7_27_iff (hc : ∀ x, IsCompact (Γ x)) (hne : ∀ x, (Γ x).Nonempty) (hβ : 0 ≤ β)
    (hϕc : Continuous ϕ) (hϕ : ∀ x, 0 < ϕ x) (θ : ℝ) (x : X) :
    β * maxValue (fun p : X × X => ϕ p.2 / ϕ p.1) Γ x ≤ θ ↔
      ∀ y ∈ Γ x, β * (ϕ y / ϕ x) ≤ θ := by
  have hr : Continuous fun p : X × X => ϕ p.2 / ϕ p.1 :=
    (hϕc.comp continuous_snd).div (hϕc.comp continuous_fst) fun p => (hϕ p.1).ne'
  refine ⟨fun h y hy => (mul_le_mul_of_nonneg_left
    (le_maxValue (f := fun p : X × X => ϕ p.2 / ϕ p.1) hr.continuousOn (hc x) hy) hβ).trans h,
    fun h => ?_⟩
  obtain ⟨y, hy, hval, -⟩ := exists_argmax hr.continuousOn (hc x) (hne x)
  rw [← hval]
  exact h y hy

/-- Miao, p. 215–216: under (7.27), `|Tf − Tg|(x) ≤ θ‖f − g‖_ϕ ϕ(x)` on `C_ϕ(X)`. -/
theorem wn_duran_pointwise (hu : Continuous u) (hc : ∀ x, IsCompact (Γ x))
    (hne : ∀ x, (Γ x).Nonempty) (hβ : 0 ≤ β) (hϕc : Continuous ϕ) (hϕ : ∀ x, 0 < ϕ x)
    {θ : ℝ} (h727 : ∀ x, β * maxValue (fun p : X × X => ϕ p.2 / ϕ p.1) Γ x ≤ θ)
    {f g : X → ℝ} (hf : wn_InC ϕ f) (hg : wn_InC ϕ g) (x : X) :
    |wn_duranT u Γ β f x - wn_duranT u Γ β g x| ≤ θ * wn_norm ϕ (f - g) * ϕ x := by
  have h := eq_7_26 hu hc hne hβ hϕc hϕ hf hg x
  have h2 : 0 ≤ wn_norm ϕ (f - g) * ϕ x := mul_nonneg (wn_norm_nonneg _) (hϕ x).le
  calc |wn_duranT u Γ β f x - wn_duranT u Γ β g x|
      ≤ β * maxValue (fun p : X × X => ϕ p.2 / ϕ p.1) Γ x * (wn_norm ϕ (f - g) * ϕ x) := by
        rw [← mul_assoc]; exact h
    _ ≤ θ * (wn_norm ϕ (f - g) * ϕ x) := mul_le_mul_of_nonneg_right (h727 x) h2
    _ = θ * wn_norm ϕ (f - g) * ϕ x := by ring

/-- Miao, p. 215–216: under (7.27), `β sup_{x' ∈ Γ(x)} ϕ(x')/ϕ(x) ≤ θ` for all `x`, the Bellman
operator is a contraction with modulus `θ` on `C_ϕ(X)`. -/
theorem wn_duran_contraction (hu : Continuous u) (hc : ∀ x, IsCompact (Γ x))
    (hne : ∀ x, (Γ x).Nonempty) (hβ : 0 ≤ β) (hϕc : Continuous ϕ) (hϕ : ∀ x, 0 < ϕ x)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (h727 : ∀ x, β * maxValue (fun p : X × X => ϕ p.2 / ϕ p.1) Γ x ≤ θ)
    {f g : X → ℝ} (hf : wn_InC ϕ f) (hg : wn_InC ϕ g) :
    wn_norm ϕ (wn_duranT u Γ β f - wn_duranT u Γ β g) ≤ θ * wn_norm ϕ (f - g) :=
  wn_norm_le hϕ (mul_nonneg hθ0 (wn_norm_nonneg _)) fun x =>
    wn_duran_pointwise hu hc hne hβ hϕc hϕ h727 hf hg x

/-- Miao, p. 216 ("continuity is routine"): under Assumptions 7.3.6–7.3.7, `Tf` is continuous
for continuous `f`, by the Theorem of the Maximum. -/
theorem wn_duran_continuous (hu : assumption_7_3_6 u) (hΓ : assumption_7_3_7 Γ) {f : X → ℝ}
    (hf : Continuous f) : Continuous (wn_duranT u Γ β f) :=
  (theorem_3_6 (wn_obj_continuous (β := β) hu hf).continuousOn hΓ.1 hΓ.2.1 hΓ.2.2).1

/-- Miao, (7.28), p. 216: under Assumptions 7.3.6–7.3.7, (7.27) and `‖T0‖_ϕ < ∞` (7.28), `T` maps
`C_ϕ(X)` into itself, with `‖Tf‖_ϕ ≤ θ‖f‖_ϕ + ‖T0‖_ϕ`. -/
theorem eq_7_28 (hu : assumption_7_3_6 u) (hΓ : assumption_7_3_7 Γ) (hβ : 0 ≤ β)
    (hϕc : Continuous ϕ) (hϕ : ∀ x, 0 < ϕ x) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (h727 : ∀ x, β * maxValue (fun p : X × X => ϕ p.2 / ϕ p.1) Γ x ≤ θ)
    (h728 : ∃ B, ∀ x, |wn_duranT u Γ β 0 x| ≤ B * ϕ x) {f : X → ℝ} (hf : wn_InC ϕ f) :
    wn_InC ϕ (wn_duranT u Γ β f) ∧
      wn_norm ϕ (wn_duranT u Γ β f) ≤ θ * wn_norm ϕ f + wn_norm ϕ (wn_duranT u Γ β 0) := by
  have hne : ∀ x, (Γ x).Nonempty := fun x => (hΓ.2.1 x).1
  have h0 : wn_InC ϕ (wn_duranT u Γ β 0) := ⟨wn_duran_continuous hu hΓ continuous_const, h728⟩
  have hb : ∀ x, |wn_duranT u Γ β f x| ≤
      (θ * wn_norm ϕ f + wn_norm ϕ (wn_duranT u Γ β 0)) * ϕ x := fun x => by
    have h1 := wn_duran_pointwise hu hΓ.1 hne hβ hϕc hϕ h727 hf wn_inC_zero x
    rw [sub_zero] at h1
    have h2 := wn_abs_le hϕ h0 x
    have h3 := abs_sub_abs_le_abs_sub (wn_duranT u Γ β f x) (wn_duranT u Γ β 0 x)
    nlinarith
  exact ⟨⟨wn_duran_continuous hu hΓ hf.1, _, hb⟩,
    wn_norm_le hϕ (add_nonneg (mul_nonneg hθ0 (wn_norm_nonneg _)) (wn_norm_nonneg _)) hb⟩

/-- Miao, pp. 215–216 (Duran's approach): under Assumptions 7.3.6–7.3.7, `β ≥ 0`, (7.27) with
`0 ≤ θ < 1` and (7.28), the Bellman operator (7.25) has a unique fixed point in `C_ϕ(X)`. -/
theorem wn_duran_fixed_point (hu : assumption_7_3_6 u) (hΓ : assumption_7_3_7 Γ) (hβ : 0 ≤ β)
    (hϕc : Continuous ϕ) (hϕ : ∀ x, 0 < ϕ x) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h727 : ∀ x, β * maxValue (fun p : X × X => ϕ p.2 / ϕ p.1) Γ x ≤ θ)
    (h728 : ∃ B, ∀ x, |wn_duranT u Γ β 0 x| ≤ B * ϕ x) :
    ∃! V, wn_InC ϕ V ∧ wn_duranT u Γ β V = V :=
  wn_exists_unique_fixedPoint hϕc hϕ (fun _ hf => (eq_7_28 hu hΓ hβ hϕc hϕ hθ0 h727 h728 hf).1)
    hθ0 hθ1 fun _ _ hf hg =>
      wn_duran_contraction hu hΓ.1 (fun x => (hΓ.2.1 x).1) hβ hϕc hϕ hθ0 h727 hf hg

end Miao.InfiniteHorizonDP
