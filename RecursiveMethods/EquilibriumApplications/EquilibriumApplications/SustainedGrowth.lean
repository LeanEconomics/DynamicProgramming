/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.SequencePrices

/-!
# An economy with sustained growth: the spaces `S_θ` and Exercise 16.3(a)–(b)

SLP §16.3, pp. 485–487. The one-sector economy of §16.1 with Cobb–Douglas technology and
exogenous technical change, (1) `k_{t+1} + y_t ≤ γᵗ k_tᵅ`, `γ > 1`, `0 < α < 1`, `k₀ > 0`.

* `SGFeasible γ α k₀ k y`: the capital path `k ≥ 0`, `k 0 = k₀`, and output `y` satisfy (1).
* `sgHalfPath`: the book's path `k_{t+1} = y_t = ½ γᵗ k_tᵅ` (p. 486); it is feasible
  (`sgHalfPath_feasible`) and neither `k` nor `y` is bounded (`sgHalfPath_not_bdd`).
* `sgSθ θ` (`S_θ`, p. 486): sequences with `‖x‖_θ = sup_t |θ⁻ᵗ x_t| < ∞`; `sgNormθ θ` is
  `‖·‖_θ`. The map `sgOfBdd θ : w ↦ (θᵗ w_t)` is a bijection of `ℓ_∞ = BddSeq ℝ` onto `S_θ`
  (`sgOfBdd_mem`, `exists_sgOfBdd`, `sgOfBdd_injective`), linear (`sgOfBdd_add`,
  `sgOfBdd_smul`) and isometric (`norm_eq_sgNormθ`). So `S_θ` is a normed space isometric to
  `ℓ_∞`, and we compute in `ℓ_∞` coordinates: a subset `A ⊆ S_θ` is `{w | sgOfBdd θ w ∈ A}`.
* `sgTechPrinted` (the printed `Y`, p. 486) and `sgTech` (the corrected `Y`, with `y ≥ 0`);
  `sgTechθ θ` is `Y ∩ S_θ` in `ℓ_∞` coordinates.
* `sgThetaHat γ α = γ^{1/(1−α)}` (`θ̂`), the balanced growth factor; `1 < θ̂`
  (`one_lt_sgThetaHat`).
* `sg_upper_bound`: along any feasible path with `y ≥ 0`,
  `k_t, y_t ≤ max(1, k₀) θ̂ᵗ` (the manual's "familiar results").
* `sg_witness`: a feasible capital path with uniform slack `m θ̂ᵗ / 2`.
* **Exercise 16.3(a)** (`ex_16_3a`): for `θ > 0`, `Y ⊆ S_θ ⇔ θ ≥ θ̂`.
* **Exercise 16.3(b)** (`ex_16_3b`): for `θ > 0`, `Y ∩ S_θ` has an interior point in `S_θ`
  iff `θ ≤ θ̂`; hence (`ex_16_3_theta_unique`) `θ̂` is the unique `θ ≥ 1` with `Y ⊆ S_θ` and
  `int Y ≠ ∅` — the `θ` of the rest of the section.

**Corrections.**
* p. 486, definition of `Y`: as printed (no `y ≥ 0`) `Y ⊄ S_θ` for every `θ > 0`
  (`sgTechPrinted_not_subset`): `y_t = −(2θ)ᵗ`, `k_t = 0` for `t ≥ 1` satisfies (1). The
  intended set is `sgTech` (also the manual's).
* Manual 16.3(a) proves only `θ ≥ θ̂ ⇒ Y ⊆ S_θ`; the converse is proved here (`ex_16_3a`,
  via `sg_witness`: a feasible `y` with `y_t = (m/2) θ̂ᵗ`, not in `S_θ` for `θ < θ̂`). The manual's
  normalised inequality drops the constant `θ̂^{−α}`; the bounds here are proved directly.
* Manual 16.3(b), case `θ < θ̂`: its candidate interior point (`y_t ≍ θ̂ᵗ`) is not in `S_θ`.
  Read as `Y ∩ S_θ` (which is what `sgTechθ` is), the claim is still true, with the interior point
  `y_t = (m/4) θᵗ` along the `sg_witness` capital path.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped ENNReal

/-- The balanced growth factor `θ̂ = γ^{1/(1−α)}` (manual 16.3a). -/
noncomputable def sgThetaHat (γ α : ℝ) : ℝ := γ ^ (1 / (1 - α))

/-- (1) of §16.3 (p. 486): `k ≥ 0` with `k 0 = k₀` and `k_{t+1} + y_t ≤ γᵗ k_tᵅ` for all `t`. -/
def SGFeasible (γ α k0 : ℝ) (k y : ℕ → ℝ) : Prop :=
  k 0 = k0 ∧ (∀ t, 0 ≤ k t) ∧ ∀ t, k (t + 1) + y t ≤ γ ^ t * k t ^ α

/-- The production set `Y` **as printed** (p. 486): all `y` for which (1) holds for some `k ≥ 0`.
-/
def sgTechPrinted (γ α k0 : ℝ) : Set (ℕ → ℝ) := {y | ∃ k, SGFeasible γ α k0 k y}

/-- The **corrected** production set `Y`: `y ≥ 0` and (1) holds for some `k ≥ 0`. -/
def sgTech (γ α k0 : ℝ) : Set (ℕ → ℝ) := {y | (∀ t, 0 ≤ y t) ∧ ∃ k, SGFeasible γ α k0 k y}

/-- The space `S_θ = {x : sup_t |θ⁻ᵗ x_t| < ∞}` (p. 486). -/
def sgSθ (θ : ℝ) : Set (ℕ → ℝ) := {x | BddAbove (range fun t => |x t| / θ ^ t)}

/-- The norm `‖x‖_θ = sup_t |θ⁻ᵗ x_t|` (p. 486). -/
noncomputable def sgNormθ (θ : ℝ) (x : ℕ → ℝ) : ℝ := ⨆ t, |x t| / θ ^ t

/-- The isometry `ℓ_∞ → S_θ`, `w ↦ (θᵗ w_t)`. -/
def sgOfBdd (θ : ℝ) (w : BddSeq ℝ) : ℕ → ℝ := fun t => θ ^ t * w t

/-- `Y ∩ S_θ` in `ℓ_∞` coordinates. -/
def sgTechθ (θ γ α k0 : ℝ) : Set (BddSeq ℝ) := {w | sgOfBdd θ w ∈ sgTech γ α k0}

/-- The constant sequence `c𝟙` in `ℓ_∞`. -/
noncomputable def sgConst (c : ℝ) : BddSeq ℝ := BddSeq.mk (fun _ => c) |c| fun _ => le_rfl

/-- Coordinates of `sgConst`. -/
@[simp] theorem sgConst_apply (c : ℝ) (t : ℕ) : sgConst c t = c := rfl

/-- `‖c𝟙‖ ≤ |c|`. -/
theorem norm_sgConst_le (c : ℝ) : ‖sgConst c‖ ≤ |c| :=
  lp.norm_le_of_forall_le (abs_nonneg c) fun _ => le_rfl

/-- `sgOfBdd θ w` lies in `S_θ`. -/
theorem sgOfBdd_mem {θ : ℝ} (hθ : 0 < θ) (w : BddSeq ℝ) : sgOfBdd θ w ∈ sgSθ θ := by
  refine ⟨‖w‖, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hp : 0 < θ ^ t := pow_pos hθ t
  change |θ ^ t * w t| / θ ^ t ≤ ‖w‖
  rw [abs_mul, abs_of_pos hp, mul_div_cancel_left₀ _ hp.ne']
  exact norm_seq_coord_le w t

/-- Every element of `S_θ` is `sgOfBdd θ w` for some `w ∈ ℓ_∞`. -/
theorem exists_sgOfBdd {θ : ℝ} (hθ : 0 < θ) {x : ℕ → ℝ} (hx : x ∈ sgSθ θ) :
    ∃ w : BddSeq ℝ, sgOfBdd θ w = x := by
  obtain ⟨C, hC⟩ := hx
  have hb : ∀ t, ‖x t / θ ^ t‖ ≤ C := fun t => by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hθ t)]
    exact hC ⟨t, rfl⟩
  refine ⟨BddSeq.mk (fun t => x t / θ ^ t) C hb, funext fun t => ?_⟩
  change θ ^ t * (x t / θ ^ t) = x t
  field_simp

/-- `sgOfBdd θ` is injective. -/
theorem sgOfBdd_injective {θ : ℝ} (hθ : 0 < θ) : Function.Injective (sgOfBdd θ) := by
  intro w w' h
  ext t
  have := congrFun h t
  exact mul_left_cancel₀ (pow_pos hθ t).ne' this

/-- `sgOfBdd θ` is additive. -/
theorem sgOfBdd_add (θ : ℝ) (w w' : BddSeq ℝ) :
    sgOfBdd θ (w + w') = sgOfBdd θ w + sgOfBdd θ w' := by
  funext t
  change θ ^ t * (w + w') t = θ ^ t * w t + θ ^ t * w' t
  rw [lp.coeFn_add, Pi.add_apply, mul_add]

/-- `sgOfBdd θ` is homogeneous. -/
theorem sgOfBdd_smul (θ c : ℝ) (w : BddSeq ℝ) : sgOfBdd θ (c • w) = c • sgOfBdd θ w := by
  funext t
  change θ ^ t * (c • w) t = c * (θ ^ t * w t)
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- `sgOfBdd θ` is an isometry: `‖w‖_∞ = ‖sgOfBdd θ w‖_θ`. -/
theorem norm_eq_sgNormθ {θ : ℝ} (hθ : 0 < θ) (w : BddSeq ℝ) :
    ‖w‖ = sgNormθ θ (sgOfBdd θ w) := by
  rw [lp.norm_eq_ciSup, sgNormθ]
  congr 1
  funext t
  have hp : 0 < θ ^ t := pow_pos hθ t
  change ‖w t‖ = |θ ^ t * w t| / θ ^ t
  rw [abs_mul, abs_of_pos hp, mul_div_cancel_left₀ _ hp.ne', Real.norm_eq_abs]

/-- `θ̂^{1−α} = γ`. -/
theorem sgThetaHat_rpow {γ α : ℝ} (hγ : 0 < γ) (hα1 : α < 1) :
    sgThetaHat γ α ^ (1 - α) = γ := by
  rw [sgThetaHat, ← Real.rpow_mul hγ.le, one_div, inv_mul_cancel₀ (by linarith),
    Real.rpow_one]

/-- `θ̂ > 0`. -/
theorem sgThetaHat_pos {γ α : ℝ} (hγ : 0 < γ) : 0 < sgThetaHat γ α := Real.rpow_pos_of_pos hγ _

/-- `θ̂ > 1` when `γ > 1`. -/
theorem one_lt_sgThetaHat {γ α : ℝ} (hγ : 1 < γ) (hα1 : α < 1) : 1 < sgThetaHat γ α :=
  Real.one_lt_rpow hγ (by rw [one_div]; exact inv_pos.2 (by linarith))

/-- `γ θ̂ᵅ = θ̂`. -/
theorem sg_gamma_mul {γ α : ℝ} (hγ : 0 < γ) (hα1 : α < 1) :
    γ * sgThetaHat γ α ^ α = sgThetaHat γ α := by
  have hθ := sgThetaHat_pos (α := α) hγ
  calc γ * sgThetaHat γ α ^ α = sgThetaHat γ α ^ (1 - α) * sgThetaHat γ α ^ α := by
        rw [sgThetaHat_rpow hγ hα1]
    _ = sgThetaHat γ α := by rw [← Real.rpow_add hθ, sub_add_cancel, Real.rpow_one]

/-- The capacity along a geometric path: `γᵗ (B θ̂ᵗ)ᵅ = Bᵅ θ̂ᵗ`. -/
theorem sg_cap_geom {γ α B : ℝ} (hγ : 0 < γ) (hα1 : α < 1) (hB : 0 ≤ B) (t : ℕ) :
    γ ^ t * (B * sgThetaHat γ α ^ t) ^ α = B ^ α * sgThetaHat γ α ^ t := by
  have hθ := sgThetaHat_pos (α := α) hγ
  rw [Real.mul_rpow hB (pow_nonneg hθ.le t), ← Real.rpow_pow_comm hθ.le α t]
  calc γ ^ t * (B ^ α * (sgThetaHat γ α ^ α) ^ t) = B ^ α * (γ * sgThetaHat γ α ^ α) ^ t := by
        ring
    _ = B ^ α * sgThetaHat γ α ^ t := by rw [sg_gamma_mul hγ hα1]

/-- **Upper bound** along any feasible path with `y ≥ 0`: `k_t ≤ B θ̂ᵗ` and `y_t ≤ B θ̂ᵗ` with
`B = max(1, k₀)` (the manual's "familiar results", proved directly). -/
theorem sg_upper_bound {γ α k0 : ℝ} (hγ : 1 < γ) (hα0 : 0 < α) (hα1 : α < 1) {k y : ℕ → ℝ}
    (hf : SGFeasible γ α k0 k y) (hy : ∀ t, 0 ≤ y t) (t : ℕ) :
    k t ≤ max 1 k0 * sgThetaHat γ α ^ t ∧ y t ≤ max 1 k0 * sgThetaHat γ α ^ t := by
  obtain ⟨hk0, hkn, hcap⟩ := hf
  set B := max 1 k0
  set θ := sgThetaHat γ α
  have hθ1 : 1 < θ := one_lt_sgThetaHat hγ hα1
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBα : B ^ α ≤ B := by
    calc B ^ α ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 hα1.le
      _ = B := Real.rpow_one B
  -- capacity bound from a bound on `k t`
  have hcapB : ∀ s, k s ≤ B * θ ^ s → γ ^ s * k s ^ α ≤ B * θ ^ s := fun s hs => by
    calc γ ^ s * k s ^ α ≤ γ ^ s * (B * θ ^ s) ^ α := by
          gcongr
          · exact hkn s
      _ = B ^ α * θ ^ s := sg_cap_geom (by linarith) hα1 (by linarith) s
      _ ≤ B * θ ^ s := by gcongr
  have hk : ∀ s, k s ≤ B * θ ^ s := by
    intro s
    induction s with
    | zero => rw [hk0, pow_zero, mul_one]; exact le_max_right _ _
    | succ s ih =>
      calc k (s + 1) ≤ k (s + 1) + y s := le_add_of_nonneg_right (hy s)
        _ ≤ γ ^ s * k s ^ α := hcap s
        _ ≤ B * θ ^ s := hcapB s ih
        _ ≤ B * θ ^ (s + 1) := by
          gcongr
          · exact hθ1.le
          · omega
  refine ⟨hk t, ?_⟩
  calc y t ≤ k (t + 1) + y t := le_add_of_nonneg_left (hkn (t + 1))
    _ ≤ γ ^ t * k t ^ α := hcap t
    _ ≤ B * θ ^ t := hcapB t (hk t)

/-- A small `b > 0` with `b θ̂ ≤ bᵅ / 2`: any `b ≤ ((2θ̂)⁻¹)^{1/(1−α)}`. -/
theorem sg_small_b {γ α b : ℝ} (hγ : 1 < γ) (hα1 : α < 1) (hb : 0 < b)
    (hbX : b ≤ ((2 * sgThetaHat γ α)⁻¹) ^ (1 / (1 - α))) :
    b * sgThetaHat γ α ≤ b ^ α / 2 := by
  set θ := sgThetaHat γ α
  have hθ : 0 < θ := sgThetaHat_pos (by linarith)
  have hX : 0 ≤ (2 * θ)⁻¹ := by positivity
  have h1 : b ^ (1 - α) ≤ (2 * θ)⁻¹ := by
    calc b ^ (1 - α) ≤ (((2 * θ)⁻¹) ^ (1 / (1 - α))) ^ (1 - α) :=
          Real.rpow_le_rpow hb.le hbX (by linarith)
      _ = (2 * θ)⁻¹ := by
          rw [← Real.rpow_mul hX, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
  have hsplit : b = b ^ α * b ^ (1 - α) := by
    rw [← Real.rpow_add hb, add_sub_cancel, Real.rpow_one]
  have hbα : 0 < b ^ α := Real.rpow_pos_of_pos hb α
  calc b * θ = b ^ α * b ^ (1 - α) * θ := by rw [← hsplit]
    _ ≤ b ^ α * (2 * θ)⁻¹ * θ := by gcongr
    _ = b ^ α / 2 := by field_simp

/-- A **feasible capital path with uniform slack**: there are `k` and `m > 0` with `k 0 = k₀`,
`k ≥ 0` and `k_{t+1} + m θ̂ᵗ / 2 ≤ γᵗ k_tᵅ` for all `t`. Hence every `y` with
`0 ≤ y_t ≤ m θ̂ᵗ / 2` lies in `Y`. -/
theorem sg_witness {γ α k0 : ℝ} (hγ : 1 < γ) (hα0 : 0 < α) (hα1 : α < 1) (hk0 : 0 < k0) :
    ∃ k : ℕ → ℝ, ∃ m : ℝ, 0 < m ∧ k 0 = k0 ∧ (∀ t, 0 ≤ k t) ∧
      ∀ t, k (t + 1) + m / 2 * sgThetaHat γ α ^ t ≤ γ ^ t * k t ^ α := by
  set θ := sgThetaHat γ α
  have hθ : 0 < θ := sgThetaHat_pos (by linarith)
  have hk0α : 0 < k0 ^ α := Real.rpow_pos_of_pos hk0 α
  set X := ((2 * θ)⁻¹) ^ (1 / (1 - α))
  have hXpos : 0 < X := Real.rpow_pos_of_pos (by positivity) _
  set b := min (k0 ^ α / (2 * θ)) X
  have hb : 0 < b := lt_min (by positivity) hXpos
  have hbα : 0 < b ^ α := Real.rpow_pos_of_pos hb α
  have hb1 : b * θ ≤ k0 ^ α / 2 := by
    have : b ≤ k0 ^ α / (2 * θ) := min_le_left _ _
    calc b * θ ≤ k0 ^ α / (2 * θ) * θ := by gcongr
      _ = k0 ^ α / 2 := by field_simp
  have hb2 : b * θ ≤ b ^ α / 2 := sg_small_b hγ hα1 hb (min_le_right _ _)
  set m := min (k0 ^ α) (b ^ α)
  have hm : 0 < m := lt_min hk0α hbα
  have hbm : b * θ ≤ m / 2 := by
    have h : m = k0 ^ α ∨ m = b ^ α := min_choice _ _
    rcases h with h | h <;> rw [h] <;> assumption
  refine ⟨fun t => if t = 0 then k0 else b * θ ^ t, m, hm, by simp, fun t => ?_, fun t => ?_⟩
  · dsimp only
    split_ifs
    · exact hk0.le
    · positivity
  · have hcap : m * θ ^ t ≤ γ ^ t * (if t = 0 then k0 else b * θ ^ t) ^ α := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h
        simp only [pow_zero, mul_one, ↓reduceIte, one_mul]
        exact min_le_left _ _
      · simp only [h.ne', ↓reduceIte]
        rw [sg_cap_geom (by linarith) hα1 hb.le t]
        gcongr
        exact min_le_right _ _
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    calc b * θ ^ (t + 1) + m / 2 * θ ^ t = b * θ * θ ^ t + m / 2 * θ ^ t := by ring
      _ ≤ m / 2 * θ ^ t + m / 2 * θ ^ t := by gcongr
      _ = m * θ ^ t := by ring
      _ ≤ _ := hcap

/-- `(r ^ t)` is unbounded above for `r > 1`, in the form needed below. -/
theorem sg_pow_unbounded {r C : ℝ} (hr : 1 < r) : ∃ t : ℕ, C < r ^ t :=
  ((tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop C).exists

/-- **Exercise 16.3(a)**: for `θ > 0`, `Y ⊆ S_θ` if and only if `θ ≥ θ̂ = γ^{1/(1−α)}`. -/
theorem ex_16_3a {γ α k0 θ : ℝ} (hγ : 1 < γ) (hα0 : 0 < α) (hα1 : α < 1) (hk0 : 0 < k0)
    (hθ : 0 < θ) : sgTech γ α k0 ⊆ sgSθ θ ↔ sgThetaHat γ α ≤ θ := by
  set θh := sgThetaHat γ α
  have hθh : 0 < θh := sgThetaHat_pos (by linarith)
  constructor
  · intro hsub
    by_contra hlt
    push Not at hlt
    obtain ⟨k, m, hm, hk0', hkn, hcap⟩ := sg_witness hγ hα0 hα1 hk0
    have hy : (fun t => m / 2 * θh ^ t) ∈ sgTech γ α k0 :=
      ⟨fun t => by positivity, k, hk0', hkn, hcap⟩
    obtain ⟨C, hC⟩ := hsub hy
    obtain ⟨t, ht⟩ := sg_pow_unbounded (C := 2 * C / m) ((one_lt_div hθ).2 hlt)
    have hCt := hC ⟨t, rfl⟩
    have hp : 0 < θ ^ t := pow_pos hθ t
    change |m / 2 * θh ^ t| / θ ^ t ≤ C at hCt
    rw [abs_of_pos (by positivity), div_le_iff₀ hp] at hCt
    rw [div_pow, lt_div_iff₀ hp, div_mul_eq_mul_div, div_lt_iff₀ hm] at ht
    nlinarith
  · intro hle y ⟨hy, k, hk⟩
    refine ⟨max 1 k0, ?_⟩
    rintro _ ⟨t, rfl⟩
    have hp : 0 < θ ^ t := pow_pos hθ t
    change |y t| / θ ^ t ≤ max 1 k0
    rw [abs_of_nonneg (hy t), div_le_iff₀ hp]
    calc y t ≤ max 1 k0 * θh ^ t := (sg_upper_bound hγ hα0 hα1 hk hy t).2
      _ ≤ max 1 k0 * θ ^ t := by gcongr

/-- Coordinates of `w ∈ Y ∩ S_θ` are nonnegative. -/
theorem sgTechθ_nonneg {θ γ α k0 : ℝ} (hθ : 0 < θ) {w : BddSeq ℝ} (hw : w ∈ sgTechθ θ γ α k0)
    (t : ℕ) : 0 ≤ w t :=
  nonneg_of_mul_nonneg_right (by simpa [sgOfBdd, mul_comm] using hw.1 t) (pow_pos hθ t)

/-- **Exercise 16.3(b)**: for `θ > 0`, `Y ∩ S_θ` has an interior point in `S_θ` if and only if
`θ ≤ θ̂`. (For the `θ` of part (a), i.e. `θ ≥ θ̂`, this means `θ = θ̂`.) -/
theorem ex_16_3b {γ α k0 θ : ℝ} (hγ : 1 < γ) (hα0 : 0 < α) (hα1 : α < 1) (hk0 : 0 < k0)
    (hθ : 0 < θ) : (interior (sgTechθ θ γ α k0)).Nonempty ↔ θ ≤ sgThetaHat γ α := by
  set θh := sgThetaHat γ α
  have hθh1 : 1 < θh := one_lt_sgThetaHat hγ hα1
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hw)
    have hw' : w + sgConst (ε / 2) ∈ sgTechθ θ γ α k0 := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      calc ‖sgConst (ε / 2)‖ ≤ |ε / 2| := norm_sgConst_le _
        _ < ε := by rw [abs_of_pos (by positivity)]; linarith
    obtain ⟨hy, k, hk⟩ := hw'
    by_contra hlt
    push Not at hlt
    set B := max 1 k0
    have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    obtain ⟨t, ht⟩ := sg_pow_unbounded (C := 2 * B / ε) ((one_lt_div (by linarith)).2 hlt)
    have hbd := (sg_upper_bound hγ hα0 hα1 hk hy t).2
    have hwt : 0 ≤ w t := sgTechθ_nonneg hθ (interior_subset hw) t
    have hp : 0 < θh ^ t := pow_pos (by linarith) t
    change θ ^ t * (w + sgConst (ε / 2)) t ≤ B * θh ^ t at hbd
    rw [lp.coeFn_add, Pi.add_apply, sgConst_apply] at hbd
    rw [div_pow, lt_div_iff₀ hp, div_mul_eq_mul_div, div_lt_iff₀ hε] at ht
    have hθt : 0 < θ ^ t := pow_pos hθ t
    nlinarith
  · intro hle
    obtain ⟨k, m, hm, hk0', hkn, hcap⟩ := sg_witness hγ hα0 hα1 hk0
    refine ⟨sgConst (m / 4), mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2
      ⟨m / 4, by positivity, fun w hw => ?_⟩)⟩
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hwt : ∀ t, |w t - m / 4| < m / 4 := fun t => by
      have := norm_seq_coord_le (w - sgConst (m / 4)) t
      rw [lp.coeFn_sub, Pi.sub_apply, sgConst_apply, Real.norm_eq_abs] at this
      linarith
    have hθt : ∀ t, θ ^ t ≤ θh ^ t := fun t => pow_le_pow_left₀ hθ.le hle t
    refine ⟨fun t => ?_, k, hk0', hkn, fun t => ?_⟩
    · have := abs_lt.1 (hwt t)
      exact mul_nonneg (pow_nonneg hθ.le t) (by linarith)
    · have h1 := abs_lt.1 (hwt t)
      have h2 : sgOfBdd θ w t ≤ m / 2 * θh ^ t := by
        change θ ^ t * w t ≤ m / 2 * θh ^ t
        calc θ ^ t * w t ≤ θ ^ t * (m / 2) := by gcongr; linarith
          _ ≤ θh ^ t * (m / 2) := by gcongr
          _ = m / 2 * θh ^ t := mul_comm _ _
      linarith [hcap t]

/-- **Exercise 16.3(a)–(b), conclusion** (p. 486): `θ̂` is the unique `θ ≥ 1` with `Y ⊆ S_θ` and
`int (Y ∩ S_θ) ≠ ∅` in `‖·‖_θ`. -/
theorem ex_16_3_theta_unique {γ α k0 : ℝ} (hγ : 1 < γ) (hα0 : 0 < α) (hα1 : α < 1)
    (hk0 : 0 < k0) :
    {θ : ℝ | 1 ≤ θ ∧ sgTech γ α k0 ⊆ sgSθ θ ∧ (interior (sgTechθ θ γ α k0)).Nonempty} =
      {sgThetaHat γ α} := by
  have hθh1 := one_lt_sgThetaHat hγ hα1
  ext θ
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, ha, hb⟩
    have hθ : 0 < θ := by linarith
    exact le_antisymm ((ex_16_3b hγ hα0 hα1 hk0 hθ).1 hb) ((ex_16_3a hγ hα0 hα1 hk0 hθ).1 ha)
  · rintro rfl
    have hθ : 0 < sgThetaHat γ α := by linarith
    exact ⟨hθh1.le, (ex_16_3a hγ hα0 hα1 hk0 hθ).2 le_rfl,
      (ex_16_3b hγ hα0 hα1 hk0 hθ).2 le_rfl⟩

/-- **Correction** (p. 486): the printed `Y` (without `y ≥ 0`) is contained in no `S_θ`,
`θ > 0`: `y_t = −(2θ)ᵗ` with `k_t = 0` for `t ≥ 1` satisfies (1). -/
theorem sgTechPrinted_not_subset {γ α k0 θ : ℝ} (hα0 : 0 < α) (hk0 : 0 ≤ k0) (hθ : 0 < θ) :
    ¬ sgTechPrinted γ α k0 ⊆ sgSθ θ := by
  intro hsub
  have hy : (fun t : ℕ => -(2 * θ) ^ t) ∈ sgTechPrinted γ α k0 := by
    refine ⟨fun t => if t = 0 then k0 else 0, by simp, fun t => ?_, fun t => ?_⟩
    · dsimp only
      split_ifs
      · exact hk0
      · exact le_rfl
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, zero_add]
      have hneg : -(2 * θ) ^ t ≤ 0 := neg_nonpos.2 (by positivity)
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h
        simp only [pow_zero, ↓reduceIte, one_mul]
        exact hneg.trans (Real.rpow_nonneg hk0 α)
      · simp only [h.ne', ↓reduceIte]
        rw [Real.zero_rpow hα0.ne', mul_zero]
        exact hneg
  obtain ⟨C, hC⟩ := hsub hy
  obtain ⟨t, ht⟩ := sg_pow_unbounded (C := C) (r := 2) one_lt_two
  have hCt := hC ⟨t, rfl⟩
  change |-(2 * θ) ^ t| / θ ^ t ≤ C at hCt
  rw [abs_neg, abs_of_pos (by positivity), mul_pow,
    mul_div_cancel_right₀ _ (pow_pos hθ t).ne'] at hCt
  linarith

/-- The book's path (p. 486): `k₀` given, `k_{t+1} = ½ γᵗ k_tᵅ`. -/
noncomputable def sgHalfPath (γ α k0 : ℝ) : ℕ → ℝ
  | 0 => k0
  | t + 1 => γ ^ t * sgHalfPath γ α k0 t ^ α / 2

/-- The book's path is feasible with `y_t = k_{t+1}`. -/
theorem sgHalfPath_feasible {γ α k0 : ℝ} (hγ : 0 < γ) (hk0 : 0 ≤ k0) :
    SGFeasible γ α k0 (sgHalfPath γ α k0) fun t => sgHalfPath γ α k0 (t + 1) := by
  have hnn : ∀ t, 0 ≤ sgHalfPath γ α k0 t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih =>
      change 0 ≤ γ ^ t * sgHalfPath γ α k0 t ^ α / 2
      have := Real.rpow_nonneg ih α
      positivity
  refine ⟨rfl, hnn, fun t => ?_⟩
  change γ ^ t * sgHalfPath γ α k0 t ^ α / 2 + γ ^ t * sgHalfPath γ α k0 t ^ α / 2 ≤
    γ ^ t * sgHalfPath γ α k0 t ^ α
  linarith

/-- (p. 486) Along the book's path neither `k` nor `y` is bounded (so neither is in `ℓ_∞`):
`k_t ≥ b θ̂ᵗ` for some `b > 0`. -/
theorem sgHalfPath_not_bdd {γ α k0 : ℝ} (hγ : 1 < γ) (hα0 : 0 < α) (hα1 : α < 1)
    (hk0 : 0 < k0) :
    ¬ BddAbove (range (sgHalfPath γ α k0)) ∧
      ¬ BddAbove (range fun t => sgHalfPath γ α k0 (t + 1)) := by
  set θ := sgThetaHat γ α
  have hθ1 : 1 < θ := one_lt_sgThetaHat hγ hα1
  have hX : 0 < ((2 * θ)⁻¹) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos (by positivity) _
  set b := min k0 (((2 * θ)⁻¹) ^ (1 / (1 - α)))
  have hb : 0 < b := lt_min hk0 hX
  have hbθ := sg_small_b hγ hα1 hb (min_le_right _ _)
  have hlow : ∀ t, b * θ ^ t ≤ sgHalfPath γ α k0 t := by
    intro t
    induction t with
    | zero =>
      change b * θ ^ 0 ≤ k0
      rw [pow_zero, mul_one]
      exact min_le_left _ _
    | succ t ih =>
      change b * θ ^ (t + 1) ≤ γ ^ t * sgHalfPath γ α k0 t ^ α / 2
      calc b * θ ^ (t + 1) = b * θ * θ ^ t := by ring
        _ ≤ b ^ α / 2 * θ ^ t := by gcongr
        _ = γ ^ t * (b * θ ^ t) ^ α / 2 := by
          rw [sg_cap_geom (by linarith) hα1 hb.le t]; ring
        _ ≤ γ ^ t * sgHalfPath γ α k0 t ^ α / 2 := by gcongr
  have hunb : ∀ C : ℝ, ∃ t, C < sgHalfPath γ α k0 (t + 1) := fun C => by
    obtain ⟨t, ht⟩ := sg_pow_unbounded (C := C / b) hθ1
    refine ⟨t, lt_of_lt_of_le ?_ (hlow (t + 1))⟩
    rw [div_lt_iff₀ hb] at ht
    have : θ ^ t ≤ θ ^ (t + 1) := pow_le_pow_right₀ hθ1.le (by omega)
    nlinarith
  refine ⟨fun ⟨C, hC⟩ => ?_, fun ⟨C, hC⟩ => ?_⟩
  · obtain ⟨t, ht⟩ := hunb C
    exact absurd (hC ⟨t + 1, rfl⟩) (not_le.2 ht)
  · obtain ⟨t, ht⟩ := hunb C
    exact absurd (hC ⟨t, rfl⟩) (not_le.2 ht)

end StokeyLucasPrescott.EquilibriumApplications
