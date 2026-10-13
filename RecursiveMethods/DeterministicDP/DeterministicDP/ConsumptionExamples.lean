/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.Principle

/-!
# Why Theorems 4.3 and 4.5 need their boundedness conditions

SLP pp. 74–77: a consumer who values discounted consumption `Σ βᵗc_t`, with
`c_t = x_t − βx_{t+1}`, so `F(x, y) = x − βy`.

* Unrestricted borrowing, `Γ(x) = (−∞, x/β]` (`borrowΓ`): `v* ≡ +∞` (`borrow_vstar`), but
  `v(x) = x` also solves (FE) (`borrow_identity_FE`) and violates (8) along `x_t = β⁻ᵗx₀`
  (`borrow_identity_not_8`).
* No borrowing, `Γ(x) = [0, x/β]` on `ℝ₊` (`saveΓ`): `v*(x) = x` (`save_vstar`). Every feasible
  plan satisfies (9) (`save_all_satisfy_9`), but `x_t = β⁻ᵗx₀` yields `0` (`save_hoard_total`)
  and violates (11) (`save_hoard_not_11`).
-/

open Filter Topology Finset

namespace StokeyLucasPrescott.DeterministicDP

variable {β : ℝ}

/-- `F(x, y) = x − βy`: consumption when wealth `x` becomes `y` next period. -/
def consF (β : ℝ) (x y : ℝ) : ℝ := x - β * y

/-- Along any plan, `uₙ(x) = x₀ − βⁿ⁺¹x_{n+1}`. -/
theorem partialSum_consF (x : ℕ → ℝ) (n : ℕ) :
    partialSum (consF β) β x n = x 0 - β ^ (n + 1) * x (n + 1) := by
  induction n with
  | zero => simp [partialSum, consF]
  | succ n ih => rw [partialSum_succ', ih]; simp only [consF]; ring

/-- When `x_{t+1} ≤ x_t/β`, the terms `βᵗx_t` decrease, so the partial sums increase. -/
theorem monotone_partialSum_consF (hβ : 0 < β) {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) ≤ x t / β) :
    Monotone fun n => partialSum (consF β) β x n := by
  refine monotone_nat_of_le_succ fun n => ?_
  simp only [partialSum_consF]
  have h := mul_le_mul_of_nonneg_left (hx (n + 1)) (pow_nonneg hβ.le (n + 2))
  have e : β ^ (n + 2) * (x (n + 1) / β) = β ^ (n + 1) * x (n + 1) := by
    field_simp; ring
  rw [e] at h
  linarith

/-! ### Unrestricted borrowing -/

/-- `Γ(x) = (−∞, x/β]`. -/
def borrowΓ (β : ℝ) (x : ℝ) : Set ℝ := Set.Iic (x / β)

theorem borrow_assumption41 : Assumption41 (borrowΓ β) := fun x => ⟨x / β, Set.mem_Iic.2 le_rfl⟩

theorem borrow_assumption42 (hβ : 0 < β) : Assumption42 (borrowΓ β) (consF β) β :=
  fun _ _ hx => ⟨_, tendsto_atTop_iSup fun _ _ hmn =>
    EReal.coe_le_coe_iff.2 (monotone_partialSum_consF hβ hx.2 hmn)⟩

/-- With unrestricted borrowing, `v* ≡ +∞`: the plan `x_t = (x₀ − t)/βᵗ` yields `n + 1` by
period `n`. -/
theorem borrow_vstar (hβ : 0 < β) (x₀ : ℝ) : vstar (borrowΓ β) (consF β) β x₀ = ⊤ := by
  set x : ℕ → ℝ := fun t => (x₀ - t) / β ^ t
  have hx : x ∈ Feasible (borrowΓ β) x₀ := ⟨by simp [x], fun t => by
    simp only [borrowΓ, Set.mem_Iic, x, pow_succ, Nat.cast_succ]
    rw [div_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)⟩
  have hsum : ∀ n, partialSum (consF β) β x n = n + 1 := fun n => by
    rw [partialSum_consF]
    simp only [x, pow_zero, div_one, Nat.cast_zero, sub_zero, Nat.cast_succ]
    field_simp
    ring
  have htend : Tendsto (fun n => (partialSum (consF β) β x n : EReal)) atTop (𝓝 ⊤) := by
    simp only [hsum]
    refine EReal.tendsto_nhds_top_iff_real.2 fun r => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt r
    filter_upwards [eventually_ge_atTop N] with n hn
    exact EReal.coe_lt_coe_iff.2 (by linarith [(Nat.cast_le (α := ℝ)).2 hn])
  have htot : total (consF β) β x = ⊤ :=
    tendsto_nhds_unique (tendsto_total (borrow_assumption42 hβ) hx) htend
  have := le_biSup (f := total (consF β) β) hx
  rw [htot] at this
  exact top_le_iff.1 this

/-- `v(x) = x` also solves the functional equation. -/
theorem borrow_identity_FE :
    SatisfiesFE (borrowΓ β) (consF β) β fun x => (x : EReal) := by
  intro x
  have h : ∀ y, ((consF β x y : ℝ) : EReal) + (β : EReal) * (y : EReal) = (x : EReal) := by
    intro y; rw [← EReal.coe_mul, ← EReal.coe_add]; congr 1; simp only [consF]; ring
  simp only [h]
  exact (biSup_const (s := borrowΓ β x) ⟨x / β, Set.mem_Iic.2 le_rfl⟩).symm

/-- `v(x) = x` violates (8) along `x_t = β⁻ᵗx₀` when `x₀ ≠ 0`, so Theorem 4.3 does not apply. -/
theorem borrow_identity_not_8 (hβ : 0 < β) {x₀ : ℝ} (hx₀ : x₀ ≠ 0) :
    (fun t : ℕ => x₀ / β ^ t) ∈ Feasible (borrowΓ β) x₀ ∧
      ¬ Tendsto (fun n => ((β ^ n : ℝ) : EReal) * ((x₀ / β ^ n : ℝ) : EReal)) atTop (𝓝 0) := by
  refine ⟨⟨by simp, fun t => by simp only [borrowΓ, Set.mem_Iic, pow_succ, div_div]; rfl⟩, ?_⟩
  have h : ∀ n : ℕ, ((β ^ n : ℝ) : EReal) * ((x₀ / β ^ n : ℝ) : EReal) = (x₀ : EReal) := by
    intro n; rw [← EReal.coe_mul]; congr 1; field_simp
  simp only [h, tendsto_const_nhds_iff]
  exact fun h0 => hx₀ (EReal.coe_eq_zero.1 h0)

/-! ### No borrowing -/

/-- The state space `ℝ₊`. -/
abbrev NNR := {x : ℝ // 0 ≤ x}

/-- `Γ(x) = [0, x/β]`. -/
def saveΓ (β : ℝ) (x : NNR) : Set NNR := {y | y.1 ≤ x.1 / β}

/-- `F(x, y) = x − βy` on `ℝ₊`. -/
def saveF (β : ℝ) (x y : NNR) : ℝ := x.1 - β * y.1

theorem save_partialSum (x : ℕ → NNR) (n : ℕ) :
    partialSum (saveF β) β x n = (x 0).1 - β ^ (n + 1) * (x (n + 1)).1 :=
  partialSum_consF (β := β) (fun t => (x t).1) n

theorem save_assumption41 (hβ : 0 < β) : Assumption41 (saveΓ β) :=
  fun x => ⟨⟨0, le_rfl⟩, div_nonneg x.2 hβ.le⟩

theorem save_assumption42 (hβ : 0 < β) : Assumption42 (saveΓ β) (saveF β) β := by
  intro _ x hx
  refine ⟨_, tendsto_atTop_iSup fun m n hmn => EReal.coe_le_coe_iff.2 ?_⟩
  have := monotone_partialSum_consF (β := β) (x := fun t => (x t).1) hβ (fun t => hx.2 t) hmn
  simpa only [save_partialSum, partialSum_consF] using this

/-- Without borrowing, `v*(x₀) = x₀`. -/
theorem save_vstar (hβ : 0 < β) (x₀ : NNR) : vstar (saveΓ β) (saveF β) β x₀ = (x₀.1 : EReal) := by
  refine le_antisymm (iSup₂_le fun x hx => ?_) ?_
  · -- `uₙ = x₀ − βⁿ⁺¹x_{n+1} ≤ x₀`
    refine le_of_tendsto' (tendsto_total (save_assumption42 hβ) hx) fun n => ?_
    rw [save_partialSum, hx.1]
    exact EReal.coe_le_coe_iff.2 (by
      have := mul_nonneg (pow_nonneg hβ.le (n + 1)) (x (n + 1)).2; linarith)
  · -- eat everything at once
    set x : ℕ → NNR := fun t => if t = 0 then x₀ else ⟨0, le_rfl⟩
    have hx : x ∈ Feasible (saveΓ β) x₀ := ⟨rfl, fun t => by
      simp only [saveΓ, Set.mem_ofPred_eq, x, Nat.add_one_ne_zero, ↓reduceIte]
      split_ifs <;> simp [div_nonneg x₀.2 hβ.le]⟩
    have hc : ∀ n, partialSum (saveF β) β x n = x₀.1 := fun n => by
      rw [save_partialSum]; simp [x]
    have := tendsto_nhds_unique (tendsto_total (save_assumption42 hβ) hx)
      (by simp only [hc]; exact tendsto_const_nhds)
    exact this ▸ le_biSup (total (saveF β) β) hx

/-- Every feasible plan satisfies (9). -/
theorem save_all_satisfy_9 (hβ : 0 < β) {x₀ : NNR} {x : ℕ → NNR}
    (_hx : x ∈ Feasible (saveΓ β) x₀) (t : ℕ) :
    vstar (saveΓ β) (saveF β) β (x t) =
      (saveF β (x t) (x (t + 1)) : EReal) +
        (β : EReal) * vstar (saveΓ β) (saveF β) β (x (t + 1)) := by
  rw [save_vstar hβ, save_vstar hβ, ← EReal.coe_mul, ← EReal.coe_add]
  congr 1; simp only [saveF]; ring

/-- The hoarding plan `x_t = β⁻ᵗx₀`. -/
noncomputable def hoard (β : ℝ) (hβ : 0 < β) (x₀ : NNR) (t : ℕ) : NNR :=
  ⟨x₀.1 / β ^ t, div_nonneg x₀.2 (pow_nonneg hβ.le t)⟩

theorem hoard_mem (hβ : 0 < β) (x₀ : NNR) : hoard β hβ x₀ ∈ Feasible (saveΓ β) x₀ :=
  ⟨by simp [hoard], fun t => by simp only [saveΓ, Set.mem_ofPred_eq, hoard, pow_succ, div_div]; rfl⟩

/-- Hoarding everything yields `0`, so for `x₀ > 0` it is not optimal although it satisfies (9). -/
theorem save_hoard_total (hβ : 0 < β) (x₀ : NNR) :
    total (saveF β) β (hoard β hβ x₀) = 0 := by
  have hc : ∀ n, partialSum (saveF β) β (hoard β hβ x₀) n = 0 := fun n => by
    rw [save_partialSum]; simp only [hoard, pow_zero, div_one]; field_simp; ring
  exact tendsto_nhds_unique (tendsto_total (save_assumption42 hβ) (hoard_mem hβ x₀))
    (by simp only [hc, EReal.coe_zero]; exact tendsto_const_nhds)

/-- The hoarding plan violates (11) when `x₀ > 0`: `βᵗv*(x_t) = x₀`. -/
theorem save_hoard_not_11 (hβ : 0 < β) {x₀ : NNR} (hx₀ : 0 < x₀.1) :
    ¬ limsup (fun t => ((β ^ t : ℝ) : EReal) *
      vstar (saveΓ β) (saveF β) β (hoard β hβ x₀ t)) atTop ≤ 0 := by
  have h : ∀ t : ℕ, ((β ^ t : ℝ) : EReal) * vstar (saveΓ β) (saveF β) β (hoard β hβ x₀ t) =
      (x₀.1 : EReal) := fun t => by
    rw [save_vstar hβ, ← EReal.coe_mul]; congr 1; simp only [hoard]; field_simp
  simp only [h, limsup_const]
  exact not_le.2 (EReal.coe_pos.2 hx₀)

end StokeyLucasPrescott.DeterministicDP
