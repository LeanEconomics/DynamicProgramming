/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.EpsteinZinRDP

/-!
# Smooth ambiguity

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.3.4 (pp. 283–286).

The smooth ambiguity aggregator (8.52) of Ju and Miao, with a finite parameter set `Θ` and
subjective beliefs `μ(x, ·)` a distribution on `Θ`:
`B(x, a, v) = (r(x, a) + β[∑_θ (∑ v(x')^γ P_θ(x, a, x'))^{κ/γ} μ(x, θ)]^{α/κ})^{1/α}`.

* Exercise 8.3.5: with `κ = γ` (ambiguity neutrality) it is the Epstein–Zin aggregator for the
  mixture kernel `∑ μ(x, θ)P_θ`.
* For `κ < γ < 0 < α`, with `ξ = γ/κ ∈ (0, 1)` and `ζ = α/κ < 0`:
  Exercise 8.3.6 (the bounds (8.53) for `v₁ = (r₁/(1 − β))^{1/α}`, `v₂ = ((r₂ + ε)/(1 − β))^{1/α}`),
  Exercise 8.3.7 (`R = (Γ, [v₁, v₂], B)` is an RDP), the transformed aggregator (8.54) and
  Exercise 8.3.8 (`R̂` is an RDP with `v̂₁ < B̂(x, a, v̂₁)`), Exercise 8.3.9 (`R` and `R̂` are
  conjugate under `φ(t) = t^κ`), Lemma 8.3.6 (`B̂(x, a, ·)` is concave) and Proposition 8.3.5
  (`R` is globally stable).

Two printed details are corrected (see `docs/corrections.md`): the exponent in (8.54) must be
`ζ = α/κ`, not `κ/α`, for Exercise 8.3.9 to hold; and since `φ` reverses order, the transformed
value space is `V̂ = [v₂^κ, v₁^κ]`, not `[v₂^{1/κ}, v₁^{1/κ}]`.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.RecursiveDecisionProcesses

variable {X Θ : Type*} [Fintype X] [Fintype Θ]

/-- The smooth ambiguity aggregator (8.52) at a fixed `(x, a)`, with beliefs `μ` on `Θ` and
kernels `P_θ`. -/
noncomputable def smoothB (r β α γ κ : ℝ) (μ : Θ → ℝ) (P : Θ → X → ℝ) (v : X → ℝ) : ℝ :=
  (r + β * (∑ θ, μ θ * (∑ x', v x' ^ γ * P θ x') ^ (κ / γ)) ^ (α / κ)) ^ α⁻¹

/-- **Exercise 8.3.5** (p. 284): under ambiguity neutrality `κ = γ` the smooth ambiguity aggregator
is the Epstein–Zin aggregator (8.10) for the mixture kernel `∑_θ μ(θ)P_θ`. -/
theorem smoothB_neutral (r β α : ℝ) {γ : ℝ} (hγ : γ ≠ 0) (μ : Θ → ℝ) (P : Θ → X → ℝ)
    (v : X → ℝ) :
    smoothB r β α γ γ μ P v = (r + β * (∑ x', v x' ^ γ * ∑ θ, μ θ * P θ x') ^ (α / γ)) ^ α⁻¹ := by
  have h : ∑ θ, μ θ * ∑ x', v x' ^ γ * P θ x' = ∑ x', v x' ^ γ * ∑ θ, μ θ * P θ x' := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  simp only [smoothB, div_self hγ, Real.rpow_one, h]

/-- A convex combination of positive numbers with distribution weights is positive. -/
theorem sum_dist_mul_pos {Θ : Type*} [Fintype Θ] {μ : Θ → ℝ} (hμ : IsDistribution μ)
    {f : Θ → ℝ} (hf : ∀ θ, 0 < f θ) : 0 < ∑ θ, μ θ * f θ := by
  obtain ⟨θ, hθ⟩ : ∃ θ, 0 < μ θ := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have : ∑ θ, μ θ ≤ 0 := sum_nonpos fun θ _ => hcon θ
    linarith [hμ.sum_eq_one]
  exact lt_of_lt_of_le (mul_pos hθ (hf θ)) (single_le_sum
    (f := fun θ => μ θ * f θ) (fun θ' _ => mul_nonneg (hμ.nonneg θ') (hf θ').le) (mem_univ θ))

/-- The smooth ambiguity model of §8.3.4, with `κ < γ < 0 < α`, rewards in `[r₁, r₂]` with
`r₁ > 0`, kernels `P_θ` and beliefs `μ(x, ·)` that are distributions. -/
structure SmoothAmbiguity (X A Θ : Type*) [Fintype X] [Fintype A] [Fintype Θ] where
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  r : X → A → ℝ
  r₁ : ℝ
  r₂ : ℝ
  r₁_pos : 0 < r₁
  r₁_le_r₂ : r₁ ≤ r₂
  r_bounds : ∀ x a, r₁ ≤ r x a ∧ r x a ≤ r₂
  P : Θ → X → A → X → ℝ
  P_nonneg : ∀ θ x a x', 0 ≤ P θ x a x'
  P_rowsum : ∀ θ x a, ∑ x', P θ x a x' = 1
  μ : X → Θ → ℝ
  μ_dist : ∀ x, IsDistribution (μ x)
  α : ℝ
  γ : ℝ
  κ : ℝ
  κ_lt_γ : κ < γ
  γ_neg : γ < 0
  α_pos : 0 < α

namespace SmoothAmbiguity

variable {X A Θ : Type*} [Fintype X] [Fintype A] [Fintype Θ] (S : SmoothAmbiguity X A Θ)

theorem κ_neg : S.κ < 0 := S.κ_lt_γ.trans S.γ_neg

theorem r_pos (x : X) (a : A) : 0 < S.r x a := S.r₁_pos.trans_le (S.r_bounds x a).1

/-- The aggregator (8.52). -/
noncomputable def B (x : X) (a : A) (v : X → ℝ) : ℝ :=
  smoothB (S.r x a) S.β S.α S.γ S.κ (S.μ x) (fun θ => S.P θ x a) v

/-- `ξ = γ/κ ∈ (0, 1)`. -/
noncomputable def ξ : ℝ := S.γ / S.κ

/-- `ζ = α/κ < 0` (printed as `κ/α`). -/
noncomputable def ζ : ℝ := S.α / S.κ

theorem ξ_pos : 0 < S.ξ := div_pos_of_neg_of_neg S.γ_neg S.κ_neg

theorem ξ_le_one : S.ξ ≤ 1 := (div_le_one_of_neg S.κ_neg).2 S.κ_lt_γ.le

theorem ζ_neg : S.ζ < 0 := div_neg_of_pos_of_neg S.α_pos S.κ_neg

/-- `P_θ` at action `a`. -/
def Pa (θ : Θ) (a : A) : Matrix X X ℝ := kernelAt (S.P θ) a

theorem isMarkov_Pa (θ : Θ) (a : A) : IsMarkov (S.Pa θ a) :=
  isMarkov_kernelAt (S.P_nonneg θ) (S.P_rowsum θ) a

/-- The inner certainty equivalent of (8.54): `g(v̂) = ∑_θ μ(x, θ)(∑ v̂(x')^ξ P_θ(x, a, x'))^{1/ξ}`.
-/
noncomputable def g (x : X) (a : A) (w : X → ℝ) : ℝ := ∑ θ, S.μ x θ * kpR S.ξ (S.Pa θ a) w x

/-- The transformed aggregator (8.54): `B̂(x, a, v̂) = (r(x, a) + β g(v̂)^ζ)^{1/ζ}`. -/
noncomputable def Bhat (x : X) (a : A) (w : X → ℝ) : ℝ :=
  (S.r x a + S.β * S.g x a w ^ S.ζ) ^ S.ζ⁻¹

theorem g_pos (x : X) (a : A) {w : X → ℝ} (hw : w ∈ posCone X) : 0 < S.g x a w :=
  sum_dist_mul_pos (S.μ_dist x) fun θ => kpR_pos (S.isMarkov_Pa θ a) hw x

theorem Bhat_pos (x : X) (a : A) {w : X → ℝ} (hw : w ∈ posCone X) : 0 < S.Bhat x a w :=
  Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg (S.r_pos x a)
    (mul_nonneg S.β_pos.le (Real.rpow_nonneg (S.g_pos x a hw).le _))) _

/-- The inner sums `∑ v(x')^γ P_θ(x, a, x')` are positive on `(0, ∞)^X`. -/
theorem inner_pos (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) (θ : Θ) :
    0 < ∑ x', v x' ^ S.γ * S.P θ x a x' := by
  have := (S.isMarkov_Pa θ a).mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') S.γ) x
  rwa [mulVec_apply_eq] at this

/-- The certainty equivalent `∑_θ μ(x, θ)(∑ v^γ P_θ)^{κ/γ}` is positive on `(0, ∞)^X`. -/
theorem ce_pos (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) :
    0 < ∑ θ, S.μ x θ * (∑ x', v x' ^ S.γ * S.P θ x a x') ^ (S.κ / S.γ) :=
  sum_dist_mul_pos (S.μ_dist x) fun θ => Real.rpow_pos_of_pos (S.inner_pos x a hv θ) _

theorem B_pos (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) : 0 < S.B x a v :=
  Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg (S.r_pos x a)
    (mul_nonneg S.β_pos.le (Real.rpow_nonneg (S.ce_pos x a hv).le _))) _

/-- **Exercise 8.3.9 (i)** (p. 285), in the form `B̂(x, a, v^κ) = B(x, a, v)^κ`. -/
theorem Bhat_pow (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) :
    S.Bhat x a (fun x' => v x' ^ S.κ) = S.B x a v ^ S.κ := by
  have hκ : S.κ ≠ 0 := S.κ_neg.ne
  have hγ : S.γ ≠ 0 := S.γ_neg.ne
  have hkp : ∀ θ, kpR S.ξ (S.Pa θ a) (fun x' => v x' ^ S.κ) x =
      (∑ x', v x' ^ S.γ * S.P θ x a x') ^ (S.κ / S.γ) := fun θ => by
    have e : ∀ x', (v x' ^ S.κ) ^ (S.γ / S.κ) = v x' ^ S.γ := fun x' => by
      rw [← Real.rpow_mul (hv x').le, show S.κ * (S.γ / S.κ) = S.γ by field_simp]
    simp only [kpR, mulVec_apply_eq, Pa, kernelAt_apply, e, ξ, inv_div]
  have hbase : 0 < S.r x a + S.β *
      (∑ θ, S.μ x θ * (∑ x', v x' ^ S.γ * S.P θ x a x') ^ (S.κ / S.γ)) ^ (S.α / S.κ) :=
    add_pos_of_pos_of_nonneg (S.r_pos x a)
      (mul_nonneg S.β_pos.le (Real.rpow_nonneg (S.ce_pos x a hv).le _))
  unfold Bhat g
  simp only [hkp]
  simp only [B, smoothB, ζ]
  rw [← Real.rpow_mul hbase.le, inv_div, inv_mul_eq_div]

/-- Exercise 8.3.9 (i): `B(x, a, v) = φ⁻¹[B̂(x, a, φ ∘ v)]` with `φ(t) = t^κ`. -/
theorem B_eq_conj (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) :
    S.B x a v = S.Bhat x a (fun x' => v x' ^ S.κ) ^ S.κ⁻¹ := by
  rw [S.Bhat_pow x a hv, Real.rpow_rpow_inv (S.B_pos x a hv).le S.κ_neg.ne]

/-- `B̂(x, a, ·)` is order preserving on `(0, ∞)^X`. -/
theorem Bhat_monotoneOn (x : X) (a : A) : MonotoneOn (S.Bhat x a) (posCone X) :=
  fun v hv w hw hvw => ezAgg_monotoneOn (S.r_pos x a) S.β_pos.le S.ζ_neg.ne (S.g_pos x a hv)
    (S.g_pos x a hw) (sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left
      ((isCertEquiv_kpR S.ξ_pos.ne' (S.isMarkov_Pa θ a)).mono v hv w hw hvw x)
      ((S.μ_dist x).nonneg θ))

omit [Fintype X] in
theorem pow_mem_posCone {v : X → ℝ} (hv : v ∈ posCone X) (p : ℝ) :
    (fun x' => v x' ^ p) ∈ posCone X := fun x' => Real.rpow_pos_of_pos (hv x') p

/-- `B(x, a, ·)` is order preserving on `(0, ∞)^X`: `t ↦ t^κ` and `t ↦ t^{1/κ}` both reverse order.
-/
theorem B_monotoneOn (x : X) (a : A) : MonotoneOn (S.B x a) (posCone X) := fun v hv w hw hvw => by
  rw [S.B_eq_conj x a hv, S.B_eq_conj x a hw]
  have hκv : (fun x' => w x' ^ S.κ) ≤ fun x' => v x' ^ S.κ := fun x' =>
    Real.rpow_le_rpow_of_nonpos (hv x') (hvw x') S.κ_neg.le
  have h1 := S.Bhat_monotoneOn x a (pow_mem_posCone hw _) (pow_mem_posCone hv _) hκv
  exact Real.rpow_le_rpow_of_nonpos (S.Bhat_pos x a (pow_mem_posCone hw _)) h1
    (inv_nonpos.2 S.κ_neg.le)

/-- At a constant `c > 0`, `B(x, a, c) = (r(x, a) + βc^α)^{1/α}`. -/
theorem B_const (x : X) (a : A) {c : ℝ} (hc : 0 < c) :
    S.B x a (fun _ => c) = (S.r x a + S.β * c ^ S.α) ^ S.α⁻¹ := by
  have hκ : S.κ ≠ 0 := S.κ_neg.ne
  have hγ : S.γ ≠ 0 := S.γ_neg.ne
  have h1 : ∀ θ, (∑ x', c ^ S.γ * S.P θ x a x') ^ (S.κ / S.γ) = c ^ S.κ := fun θ => by
    rw [← Finset.mul_sum, S.P_rowsum θ x a, mul_one, ← Real.rpow_mul hc.le,
      show S.γ * (S.κ / S.γ) = S.κ by field_simp]
  simp only [B, smoothB, h1]
  rw [← Finset.sum_mul, (S.μ_dist x).sum_eq_one, one_mul, ← Real.rpow_mul hc.le,
    show S.κ * (S.α / S.κ) = S.α by field_simp]

/-! ### The value space (Exercises 8.3.6–8.3.7) -/

/-- `v₁ = (r₁/(1 − β))^{1/α}`. -/
noncomputable def v₁ : ℝ := (S.r₁ / (1 - S.β)) ^ S.α⁻¹

/-- `v₂ = ((r₂ + ε)/(1 − β))^{1/α}`. -/
noncomputable def v₂ (ε : ℝ) : ℝ := ((S.r₂ + ε) / (1 - S.β)) ^ S.α⁻¹

theorem one_sub_β_pos : 0 < 1 - S.β := by linarith [S.β_lt_one]

theorem v₁_pos : 0 < S.v₁ := Real.rpow_pos_of_pos (div_pos S.r₁_pos S.one_sub_β_pos) _

theorem v₁_le_v₂ {ε : ℝ} (hε : 0 < ε) : S.v₁ ≤ S.v₂ ε :=
  Real.rpow_le_rpow (div_pos S.r₁_pos S.one_sub_β_pos).le
    (div_le_div_of_nonneg_right (by linarith [S.r₁_le_r₂]) S.one_sub_β_pos.le)
    (inv_nonneg.2 S.α_pos.le)

theorem v₂_pos {ε : ℝ} (hε : 0 < ε) : 0 < S.v₂ ε := S.v₁_pos.trans_le (S.v₁_le_v₂ hε)

/-- **Exercise 8.3.6** (p. 284), (8.53), lower bound: `v₁ ≤ B(x, a, v₁)`. -/
theorem v₁_le_B (x : X) (a : A) : S.v₁ ≤ S.B x a (fun _ => S.v₁) := by
  have hq : 0 < S.r₁ / (1 - S.β) := div_pos S.r₁_pos S.one_sub_β_pos
  rw [S.B_const x a S.v₁_pos, v₁, Real.rpow_inv_rpow hq.le S.α_pos.ne']
  refine Real.rpow_le_rpow hq.le ?_ (inv_nonneg.2 S.α_pos.le)
  have e : S.r₁ / (1 - S.β) = S.r₁ + S.β * (S.r₁ / (1 - S.β)) := by
    field_simp [S.one_sub_β_pos.ne']
    ring
  have := (S.r_bounds x a).1
  linarith

/-- **Exercise 8.3.6** (p. 284), (8.53), strict upper bound: `B(x, a, v₂) < v₂`. -/
theorem B_lt_v₂ (x : X) (a : A) {ε : ℝ} (hε : 0 < ε) : S.B x a (fun _ => S.v₂ ε) < S.v₂ ε := by
  have hq : 0 < (S.r₂ + ε) / (1 - S.β) :=
    div_pos (by linarith [S.r₁_pos, S.r₁_le_r₂]) S.one_sub_β_pos
  rw [S.B_const x a (S.v₂_pos hε), v₂, Real.rpow_inv_rpow hq.le S.α_pos.ne']
  refine Real.rpow_lt_rpow (add_pos_of_pos_of_nonneg (S.r_pos x a)
    (mul_nonneg S.β_pos.le hq.le)).le ?_ (inv_pos.2 S.α_pos)
  have e : (S.r₂ + ε) / (1 - S.β) = S.r₂ + ε + S.β * ((S.r₂ + ε) / (1 - S.β)) := by
    field_simp [S.one_sub_β_pos.ne']
    ring
  have := (S.r_bounds x a).2
  linarith

omit [Fintype X] in
theorem Icc_subset_posCone {c d : ℝ} (hc : 0 < c) :
    Icc (fun _ : X => c) (fun _ => d) ⊆ posCone X := fun _ hv x => hc.trans_le (hv.1 x)

/-- `B(x, a, v) ∈ [v₁, v₂]` for `v ∈ [v₁, v₂]`. -/
theorem B_mem (x : X) (a : A) {ε : ℝ} (hε : 0 < ε) {v : X → ℝ}
    (hv : v ∈ Icc (fun _ : X => S.v₁) (fun _ => S.v₂ ε)) : S.B x a v ∈ Icc S.v₁ (S.v₂ ε) :=
  ⟨(S.v₁_le_B x a).trans (S.B_monotoneOn x a (fun _ => S.v₁_pos)
      (Icc_subset_posCone S.v₁_pos hv) hv.1),
    (S.B_monotoneOn x a (Icc_subset_posCone S.v₁_pos hv) (fun _ => S.v₂_pos hε) hv.2).trans
      (S.B_lt_v₂ x a hε).le⟩

/-- **Exercise 8.3.7** (p. 284): `R = (Γ, [v₁, v₂], B)` is an RDP. -/
noncomputable def toRDP {ε : ℝ} (hε : 0 < ε) : RDP X A where
  Γ := S.Γ
  Γ_nonempty := S.Γ_nonempty
  V := Icc (fun _ => S.v₁) (fun _ => S.v₂ ε)
  B := S.B
  mono := fun x a _ _ hv _ hw hvw => S.B_monotoneOn x a (Icc_subset_posCone S.v₁_pos hv)
    (Icc_subset_posCone S.v₁_pos hw) hvw
  consistent := fun σ _ _ hv => ⟨fun x => (S.B_mem x (σ x) hε hv).1,
    fun x => (S.B_mem x (σ x) hε hv).2⟩

/-! ### The transformed RDP (Exercises 8.3.8–8.3.9) -/

/-- `v̂₁ = v₂^κ` (printed `v₂^{1/κ}`). -/
noncomputable def w₁ (ε : ℝ) : ℝ := S.v₂ ε ^ S.κ

/-- `v̂₂ = v₁^κ` (printed `v₁^{1/κ}`). -/
noncomputable def w₂ : ℝ := S.v₁ ^ S.κ

theorem w₁_pos {ε : ℝ} (hε : 0 < ε) : 0 < S.w₁ ε := Real.rpow_pos_of_pos (S.v₂_pos hε) _

theorem w₁_le_w₂ {ε : ℝ} (hε : 0 < ε) : S.w₁ ε ≤ S.w₂ :=
  Real.rpow_le_rpow_of_nonpos S.v₁_pos (S.v₁_le_v₂ hε) S.κ_neg.le

/-- `φ(t) = t^κ` maps `[v₁, v₂]` into `[v̂₁, v̂₂]`. -/
theorem pow_mem {ε : ℝ} {t : ℝ} (ht : t ∈ Icc S.v₁ (S.v₂ ε)) :
    t ^ S.κ ∈ Icc (S.w₁ ε) S.w₂ :=
  ⟨Real.rpow_le_rpow_of_nonpos (S.v₁_pos.trans_le ht.1) ht.2 S.κ_neg.le,
    Real.rpow_le_rpow_of_nonpos S.v₁_pos ht.1 S.κ_neg.le⟩

/-- `φ⁻¹(t) = t^{1/κ}` maps `[v̂₁, v̂₂]` into `[v₁, v₂]`. -/
theorem pow_inv_mem {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ∈ Icc (S.w₁ ε) S.w₂) :
    t ^ S.κ⁻¹ ∈ Icc S.v₁ (S.v₂ ε) := by
  have hκ : S.κ⁻¹ ≤ 0 := inv_nonpos.2 S.κ_neg.le
  have ht0 : 0 < t := (S.w₁_pos hε).trans_le ht.1
  constructor
  · have := Real.rpow_le_rpow_of_nonpos ht0 ht.2 hκ
    rwa [w₂, Real.rpow_rpow_inv S.v₁_pos.le S.κ_neg.ne] at this
  · have := Real.rpow_le_rpow_of_nonpos (S.w₁_pos hε) ht.1 hκ
    rwa [w₁, Real.rpow_rpow_inv (S.v₂_pos hε).le S.κ_neg.ne] at this

/-- `B̂(x, a, v̂) ∈ [v̂₁, v̂₂]` for `v̂ ∈ [v̂₁, v̂₂]`. -/
theorem Bhat_mem (x : X) (a : A) {ε : ℝ} (hε : 0 < ε) {w : X → ℝ}
    (hw : w ∈ Icc (fun _ : X => S.w₁ ε) (fun _ => S.w₂)) : S.Bhat x a w ∈ Icc (S.w₁ ε) S.w₂ := by
  set u : X → ℝ := fun x' => w x' ^ S.κ⁻¹
  have hu : u ∈ Icc (fun _ : X => S.v₁) (fun _ => S.v₂ ε) :=
    ⟨fun x' => (S.pow_inv_mem hε ⟨hw.1 x', hw.2 x'⟩).1,
      fun x' => (S.pow_inv_mem hε ⟨hw.1 x', hw.2 x'⟩).2⟩
  have hwu : w = fun x' => u x' ^ S.κ := funext fun x' =>
    (Real.rpow_inv_rpow ((S.w₁_pos hε).trans_le (hw.1 x')).le S.κ_neg.ne).symm
  rw [hwu, S.Bhat_pow x a (Icc_subset_posCone S.v₁_pos hu)]
  exact S.pow_mem (S.B_mem x a hε hu)

/-- The transformed RDP `R̂ = (Γ, [v̂₁, v̂₂], B̂)` of (8.54): **Exercise 8.3.8** (p. 285). -/
noncomputable def toRDPHat {ε : ℝ} (hε : 0 < ε) : RDP X A where
  Γ := S.Γ
  Γ_nonempty := S.Γ_nonempty
  V := Icc (fun _ => S.w₁ ε) (fun _ => S.w₂)
  B := S.Bhat
  mono := fun x a _ _ hv _ hw hvw => S.Bhat_monotoneOn x a (Icc_subset_posCone (S.w₁_pos hε) hv)
    (Icc_subset_posCone (S.w₁_pos hε) hw) hvw
  consistent := fun σ _ _ hv => ⟨fun x => (S.Bhat_mem x (σ x) hε hv).1,
    fun x => (S.Bhat_mem x (σ x) hε hv).2⟩

/-- **Exercise 8.3.8** (p. 285): `v̂₁ < B̂(x, a, v̂₁)` and `B̂(x, a, v̂₂) ≤ v̂₂`. -/
theorem Bhat_bounds (x : X) (a : A) {ε : ℝ} (hε : 0 < ε) :
    S.w₁ ε < S.Bhat x a (fun _ => S.w₁ ε) ∧ S.Bhat x a (fun _ => S.w₂) ≤ S.w₂ := by
  constructor
  · have e : (fun _ : X => S.w₁ ε) = fun _ => S.v₂ ε ^ S.κ := rfl
    rw [e, S.Bhat_pow x a (fun _ => S.v₂_pos hε), w₁]
    exact Real.rpow_lt_rpow_of_neg (S.B_pos x a fun _ => S.v₂_pos hε) (S.B_lt_v₂ x a hε) S.κ_neg
  · have e : (fun _ : X => S.w₂) = fun _ => S.v₁ ^ S.κ := rfl
    rw [e, S.Bhat_pow x a (fun _ => S.v₁_pos), w₂]
    exact Real.rpow_le_rpow_of_nonpos S.v₁_pos (S.v₁_le_B x a) S.κ_neg.le

/-! ### Concavity and global stability -/

/-- `ψ(t) = (r + βt^ζ)^{1/ζ}` is concave on `(0, ∞)` for `ζ < 0`: it is `β^{1/ζ}` times the map
`t ↦ (r/β + t^ζ)^{1/ζ}` of Exercise 7.1.8. -/
theorem concaveOn_psi (x : X) (a : A) :
    ConcaveOn ℝ (Ioi 0) fun t : ℝ => (S.r x a + S.β * t ^ S.ζ) ^ S.ζ⁻¹ := by
  have hθ : S.ζ⁻¹ ≠ 0 := inv_ne_zero S.ζ_neg.ne
  have hθ1 : ¬ (0 < S.ζ⁻¹ ∧ S.ζ⁻¹ ≤ 1) := fun h => absurd h.1 (not_lt.2 (inv_nonpos.2 S.ζ_neg.le))
  have hh : 0 ≤ S.r x a / S.β := div_nonneg (S.r_pos x a).le S.β_pos.le
  have hc := (concaveOn_powF hh hθ hθ1).smul (Real.rpow_nonneg S.β_pos.le S.ζ⁻¹)
  refine ⟨convex_Ioi 0, fun y hy z hz s t hs ht hst => ?_⟩
  have key : ∀ u : ℝ, 0 < u → (S.r x a + S.β * u ^ S.ζ) ^ S.ζ⁻¹ =
      S.β ^ S.ζ⁻¹ • powF (S.r x a / S.β) S.ζ⁻¹ u := fun u hu => by
    rw [smul_eq_mul, powF, inv_inv, ← Real.mul_rpow S.β_pos.le
      (add_nonneg hh (Real.rpow_nonneg hu.le _))]
    have hb : S.β * (S.r x a / S.β) = S.r x a := by field_simp [S.β_pos.ne']
    rw [mul_add, hb]
  have hyz : 0 < s • y + t • z := (convex_Ioi (0 : ℝ)) hy hz hs ht hst
  change s • (S.r x a + S.β * y ^ S.ζ) ^ S.ζ⁻¹ + t • (S.r x a + S.β * z ^ S.ζ) ^ S.ζ⁻¹ ≤
    (S.r x a + S.β * (s • y + t • z) ^ S.ζ) ^ S.ζ⁻¹
  rw [key y hy, key z hz, key _ hyz]
  exact hc.2 hy hz hs ht hst

/-- **Lemma 8.3.6** (p. 285): `B̂(x, a, ·)` is concave on `[v̂₁, v̂₂]`. -/
theorem concaveOn_Bhat (x : X) (a : A) {ε : ℝ} (hε : 0 < ε) :
    ConcaveOn ℝ (Icc (fun _ : X => S.w₁ ε) (fun _ => S.w₂)) (S.Bhat x a) := by
  have hsub := Icc_subset_posCone (X := X) (d := S.w₂) (S.w₁_pos hε)
  refine ⟨convex_Icc _ _, fun v hv w hw s t hs ht hst => ?_⟩
  have hvp := hsub hv
  have hwp := hsub hw
  have hvw : s • v + t • w ∈ posCone X := convex_posCone hvp hwp hs ht hst
  -- concavity of the inner certainty equivalent
  have hg : s • S.g x a v + t • S.g x a w ≤ S.g x a (s • v + t • w) := by
    simp only [g, smul_eq_mul, Finset.mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun θ _ => ?_
    have := (concaveOn_kpR S.ξ_pos.ne' S.ξ_le_one (S.isMarkov_Pa θ a)).2 hvp hwp hs ht hst x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have hμ := (S.μ_dist x).nonneg θ
    nlinarith [mul_le_mul_of_nonneg_left this hμ]
  have hgv := S.g_pos x a hvp
  have hgw := S.g_pos x a hwp
  have hcomb : 0 < s • S.g x a v + t • S.g x a w := (convex_Ioi (0 : ℝ)) hgv hgw hs ht hst
  calc s • S.Bhat x a v + t • S.Bhat x a w
      ≤ (S.r x a + S.β * (s • S.g x a v + t • S.g x a w) ^ S.ζ) ^ S.ζ⁻¹ :=
        (S.concaveOn_psi x a).2 hgv hgw hs ht hst
    _ ≤ S.Bhat x a (s • v + t • w) :=
        ezAgg_monotoneOn (S.r_pos x a) S.β_pos.le S.ζ_neg.ne hcomb (S.g_pos x a hvw) hg

/-- `R̂` is a concave RDP (Exercise 8.3.8 and Lemma 8.3.6). -/
theorem toRDPHat_isConcaveRDP {ε : ℝ} (hε : 0 < ε) :
    (S.toRDPHat hε).IsConcaveRDP (fun _ => S.w₁ ε) (fun _ => S.w₂) :=
  ⟨fun _ => S.w₁_le_w₂ hε, rfl, fun x a _ => S.concaveOn_Bhat x a hε,
    RDP.exists_delta_concave _ (fun _ => S.w₁_le_w₂ hε) fun x a _ => (S.Bhat_bounds x a hε).1⟩

/-- **Proposition 8.3.5** (p. 285): the smooth ambiguity RDP is globally stable, by
Exercise 8.3.9, Proposition 8.1.3, Lemma 8.3.6 and Proposition 8.2.5; so Theorem 8.1.1 applies. -/
theorem toRDP_isGloballyStable {ε : ℝ} (hε : 0 < ε) : (S.toRDP hε).IsGloballyStable := by
  have hV : (S.toRDP hε).V = {v | ∀ x, v x ∈ Icc S.v₁ (S.v₂ ε)} :=
    Set.ext fun _ => ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩
  have hV' : (S.toRDPHat hε).V = {v | ∀ x, v x ∈ Icc (S.w₁ ε) S.w₂} :=
    Set.ext fun _ => ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩
  refine (RDP.isGloballyStable_iff_of_conj (R := S.toRDP hε) (R' := S.toRDPHat hε) rfl hV hV'
    (φ := fun t => t ^ S.κ) (ψ := fun t => t ^ S.κ⁻¹) (fun t ht => S.pow_mem ht)
    (fun t ht => S.pow_inv_mem hε ht)
    (fun t ht => Real.rpow_inv_rpow ((S.w₁_pos hε).trans_le ht.1).le S.κ_neg.ne)
    (fun t ht => Real.rpow_rpow_inv (S.v₁_pos.trans_le ht.1).le S.κ_neg.ne)
    (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt (S.v₁_pos.trans_le ht.1)))
    (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ((S.w₁_pos hε).trans_le ht.1)))
    fun x a _ v hv => S.B_eq_conj x a (Icc_subset_posCone S.v₁_pos hv)).2 ?_
  exact (S.toRDPHat_isConcaveRDP hε).isGloballyStable

end SmoothAmbiguity

end SargentStachurski.RecursiveDecisionProcesses
