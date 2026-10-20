/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.LinftyAssumptions

/-!
# Inner product prices for time and uncertainty combined: Theorem 15.9

SLP §15.4, pp. 469–473. `(Z^t, 𝒵^t, μ^t)`, `t = 0, 1, …`, are finite measure spaces (the book:
probability spaces), `X_t = L∞(Z^t, 𝒵^t, μ^t)` and `S = X₀ × X₁ × …` with
`‖x‖_s = sup_t ‖x_t‖_∞` (§15.4 (8)); here `S = LinftyTimeState μ`, Mathlib's `lp` space.

* Truncations: `linftyTimeTrunc T` (`x^T`), `linftyPeriodTrunc t A` (`x^{A_t}`, p. 470), and the
  coordinate embeddings `linftyTSSingle t`, with `ψ_t = φ ∘ linftyTSSingle t`
  (`linftyCoordDual`).
* `Assumption15_6_timeState`, `Assumption15_7_timeState`: Assumptions 15.6, 15.7 on this space
  (p. 469); **Assumptions 15.8′, 15.9′** (`Assumption15_8'`, `Assumption15_9'`, p. 470).
* `exists_linftyTimeState_decomposition`: Lemma 15.7 applied to every `ψ_t`, and the series
  `ν(x) = Σ_t ν_t(x_t)` as a continuous linear functional with `‖ν‖ ≤ ‖φ‖`.
* **Theorem 15.9** (`theorem_15_9`, p. 470): `ν` supports every Pareto optimum supported by `φ`
  and has the inner product form (9), `ν(x) = Σ_t ∫ p_t x_t dμ^t` with `p_t ∈ L¹(μ^t)`.

**Corrections and gaps** (the NOTEs to pp. 471–473, all verified).
* Step 2 (p. 471): the book calls `ν(x) = Σ_t ν_t(x_t)` "the continuous linear functional `ν`"
  without showing that the series converges or that `ν` is bounded. Repaired:
  `Σ_{t<N} |ν_t(x_t)| ≤ ‖φ‖ ‖x‖_s` (limit of `sum_abs_linftyCoordDual_le` applied to the event
  truncations of `x`), so the series converges absolutely and `‖ν‖ ≤ ‖φ‖`
  (`linftySumDual`, `exists_linftyTimeState_decomposition`).
* Step 3 (p. 472): "repeated application" of 15.8′ and 15.9′ does not give one index `N(T)`
  that works for all periods `t ≤ T` at once: these assumptions truncate one period along one
  sequence, so applied in turn they give indices `n₀, n₁(n₀), …` that depend on the earlier
  truncations, and the diagonal choice `n₀ = n₁ = … = n` is not justified by the stated
  assumptions. (No model where the common index fails is constructed here; the step is simply
  unproved.) Repaired by induction over periods with iterated limits
  (`linftyTS_consumer_bound`, `linftyTS_firm_bound`), as the NOTE proposes.
* The proof here does not go through the intermediate `ψ` of Theorem 15.6: (4) and (5) for `φ`
  are applied directly to the time-and-event-truncated points, and the final step
  (step 4, p. 473, correct as the NOTE says) is `supportsAllocation_of_limit_bounds`.
* Assumptions 15.3–15.5 are not used; a strictly preferred point is needed for every consumer
  (as in Theorems 15.6 and 15.8), and `ν ≠ 0` is not asserted.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open MeasureTheory Filter Topology Set

variable {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] {μ : ∀ t, Measure (Ω t)}
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The time–state commodity space (p. 470): `S = X₀ × X₁ × …` with `X_t = L∞(Z^t, 𝒵^t, μ^t)`
and the norm `‖x‖_s = sup_t ‖x_t‖_∞` (§15.4 (8)), as Mathlib's `lp` space with exponent `∞`. -/
abbrev LinftyTimeState (μ : ∀ t, Measure (Ω t)) : Type _ := lp (fun t => Lp ℝ ⊤ (μ t)) ⊤

/-- `‖x_t‖_∞ ≤ ‖x‖_s`. -/
theorem norm_linftyTimeState_apply_le (x : LinftyTimeState μ) (t : ℕ) : ‖x t‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x t

/-- For `‖L‖ ≤ 1`: `‖L(x_t)‖ ≤ ‖x‖_s`. -/
theorem norm_coord_le_of_opNorm_le {t : ℕ} {L : Lp ℝ ⊤ (μ t) →L[ℝ] Lp ℝ ⊤ (μ t)}
    (hL : ‖L‖ ≤ 1) (x : LinftyTimeState μ) : ‖L (x t)‖ ≤ ‖x‖ :=
  (L.le_of_opNorm_le hL (x t)).trans (by rw [one_mul]; exact norm_linftyTimeState_apply_le x t)

/-- The operator acting coordinatewise by `L_t` (each of norm `≤ 1`): `(x_t)_t ↦ (L_t x_t)_t`. -/
noncomputable def linftyCoordMap (L : ∀ t, Lp ℝ ⊤ (μ t) →L[ℝ] Lp ℝ ⊤ (μ t))
    (hL : ∀ t, ‖L t‖ ≤ 1) : LinftyTimeState μ →L[ℝ] LinftyTimeState μ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun t => L t (x t), memℓp_infty ⟨‖x‖, by
          rintro _ ⟨t, rfl⟩
          exact norm_coord_le_of_opNorm_le (hL t) x⟩⟩
      map_add' := fun x y => lp.ext (funext fun t => by
        change L t ((x + y) t) = L t (x t) + L t (y t)
        rw [lp.coeFn_add, Pi.add_apply, map_add])
      map_smul' := fun c x => lp.ext (funext fun t => by
        change L t ((c • x) t) = c • L t (x t)
        rw [lp.coeFn_smul, Pi.smul_apply, map_smul]) }
    1 fun x => by
      rw [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg x) fun t => norm_coord_le_of_opNorm_le (hL t) x

/-- `linftyCoordMap L x` has coordinates `L_t x_t`. -/
theorem linftyCoordMap_apply (L : ∀ t, Lp ℝ ⊤ (μ t) →L[ℝ] Lp ℝ ⊤ (μ t)) (hL : ∀ t, ‖L t‖ ≤ 1)
    (x : LinftyTimeState μ) (t : ℕ) : linftyCoordMap L hL x t = L t (x t) :=
  rfl

/-- Coordinatewise contractions do not increase the norm of `S`. -/
theorem norm_linftyCoordMap_apply_le (L : ∀ t, Lp ℝ ⊤ (μ t) →L[ℝ] Lp ℝ ⊤ (μ t))
    (hL : ∀ t, ‖L t‖ ≤ 1) (x : LinftyTimeState μ) : ‖linftyCoordMap L hL x‖ ≤ ‖x‖ :=
  lp.norm_le_of_forall_le (norm_nonneg x) fun t => norm_coord_le_of_opNorm_le (hL t) x

/-- The **time truncation** `x^T = (x₀, …, x_T, 0, 0, …)` (p. 463). -/
noncomputable def linftyTimeTrunc (T : ℕ) : LinftyTimeState μ →L[ℝ] LinftyTimeState μ :=
  linftyCoordMap (fun t => if t ≤ T then ContinuousLinearMap.id ℝ _ else 0) fun t => by
    split_ifs
    · exact ContinuousLinearMap.norm_id_le
    · simp

/-- `(x^T)_t = x_t` for `t ≤ T` and `0` for `t > T`. -/
theorem linftyTimeTrunc_apply (T : ℕ) (x : LinftyTimeState μ) (t : ℕ) :
    linftyTimeTrunc T x t = if t ≤ T then x t else 0 := by
  rw [linftyTimeTrunc, linftyCoordMap_apply]
  split_ifs <;> simp

/-- Truncation of every period `t` on an event `B_t ∈ 𝒵^t`: `(x_t^{B_t})_t`. -/
noncomputable def linftyEventTrunc (B : ∀ t, Set (Ω t)) :
    LinftyTimeState μ →L[ℝ] LinftyTimeState μ :=
  linftyCoordMap (fun t => linftyTrunc (μ t) (B t)) fun _ => opNorm_linftyRestrict_le _

/-- `linftyEventTrunc B x` has coordinates `x_t^{B_t}`. -/
theorem linftyEventTrunc_apply (B : ∀ t, Set (Ω t)) (x : LinftyTimeState μ) (t : ℕ) :
    linftyEventTrunc B x t = linftyTrunc (μ t) (B t) (x t) :=
  rfl

/-- The **one-period truncation** `x^{A_{s}} = (x₀, …, x_{s−1}, x_s^{A}, x_{s+1}, …)` of p. 470. -/
noncomputable def linftyPeriodTrunc (s : ℕ) (A : Set (Ω s)) :
    LinftyTimeState μ →L[ℝ] LinftyTimeState μ :=
  linftyEventTrunc (Function.update (fun t => (∅ : Set (Ω t))) s A)

/-- In period `s`, `x^{A_s}` is `x_s^A`. -/
theorem linftyPeriodTrunc_apply_self (s : ℕ) (A : Set (Ω s)) (x : LinftyTimeState μ) :
    linftyPeriodTrunc s A x s = linftyTrunc (μ s) A (x s) := by
  rw [linftyPeriodTrunc, linftyEventTrunc_apply, Function.update_self]

/-- In every other period, `x^{A_s}` agrees with `x`. -/
theorem linftyPeriodTrunc_apply_of_ne {s t : ℕ} (h : t ≠ s) (A : Set (Ω s))
    (x : LinftyTimeState μ) : linftyPeriodTrunc s A x t = x t := by
  rw [linftyPeriodTrunc, linftyEventTrunc_apply, Function.update_of_ne h, linftyTrunc,
    compl_empty, linftyRestrict_univ]

/-- The embedding of `X_t` as the `t`-th coordinate, `a ↦ (0, …, 0, a, 0, …)`. -/
noncomputable def linftyTSSingle (t : ℕ) : Lp ℝ ⊤ (μ t) →L[ℝ] LinftyTimeState μ :=
  (lp.lsingle (E := fun t => Lp ℝ ⊤ (μ t)) (𝕜 := ℝ) ⊤ t).mkContinuous 1 fun a => by
    rw [one_mul]
    exact (lp.norm_single (E := fun t => Lp ℝ ⊤ (μ t)) ENNReal.zero_lt_top t a).le

/-- Coordinates of the embedded `a`. -/
theorem linftyTSSingle_apply (t : ℕ) (a : Lp ℝ ⊤ (μ t)) (s : ℕ) :
    linftyTSSingle t a s = Pi.single (M := fun t => Lp ℝ ⊤ (μ t)) t a s :=
  rfl

/-- `Σ_{t<k} (b_t at coordinate t)` has coordinate `b_s` for `s < k` and `0` otherwise. -/
theorem linftyTSSingle_sum_apply (k : ℕ) (b : ∀ t, Lp ℝ ⊤ (μ t)) (s : ℕ) :
    (∑ t ∈ Finset.range k, linftyTSSingle t (b t) : LinftyTimeState μ) s =
      if s < k then b s else 0 := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [linftyTSSingle_apply]
  rw [Finset.sum_pi_single]
  simp [Finset.mem_range]

/-- The period-`t` component `ψ_t = φ ∘ (embedding of X_t)` of `φ ∈ S*` (Lemma 15.5). -/
noncomputable def linftyCoordDual (φ : StrongDual ℝ (LinftyTimeState μ)) (t : ℕ) :
    StrongDual ℝ (Lp ℝ ⊤ (μ t)) :=
  φ.comp (linftyTSSingle t)

/-- `ψ_t(a) = φ(0, …, 0, a, 0, …)`. -/
theorem linftyCoordDual_apply (φ : StrongDual ℝ (LinftyTimeState μ)) (t : ℕ)
    (a : Lp ℝ ⊤ (μ t)) : linftyCoordDual φ t a = φ (linftyTSSingle t a) :=
  rfl

/-- From the proof of Lemma 15.5: `Σ_{t<N} |ψ_t(y_t)| ≤ ‖φ‖ ‖y‖_s`. -/
theorem sum_abs_linftyCoordDual_le (φ : StrongDual ℝ (LinftyTimeState μ))
    (y : LinftyTimeState μ) (N : ℕ) :
    ∑ t ∈ Finset.range N, |linftyCoordDual φ t (y t)| ≤ ‖φ‖ * ‖y‖ := by
  have hs : ∀ t, ∃ b : Lp ℝ ⊤ (μ t), ‖b‖ = ‖y t‖ ∧
      linftyCoordDual φ t b = |linftyCoordDual φ t (y t)| := fun t =>
    linfty_exists_apply_eq_abs _ _
  choose b hbn hb using hs
  have hz : ‖∑ t ∈ Finset.range N, linftyTSSingle t (b t)‖ ≤ ‖y‖ := by
    refine lp.norm_le_of_forall_le (norm_nonneg y) fun s => ?_
    rw [linftyTSSingle_sum_apply]
    split_ifs
    · rw [hbn]
      exact norm_linftyTimeState_apply_le y s
    · rw [norm_zero]
      exact norm_nonneg y
  calc ∑ t ∈ Finset.range N, |linftyCoordDual φ t (y t)|
      = φ (∑ t ∈ Finset.range N, linftyTSSingle t (b t)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun t _ => (hb t).symm
    _ ≤ ‖φ (∑ t ∈ Finset.range N, linftyTSSingle t (b t))‖ := le_abs_self _
    _ ≤ ‖φ‖ * ‖∑ t ∈ Finset.range N, linftyTSSingle t (b t)‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * ‖y‖ := mul_le_mul_of_nonneg_left hz (norm_nonneg φ)

/-- A uniform bound on the partial sums of `|ν_t(x_t)|` gives summability. -/
theorem summable_abs_of_sum_le {νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))} {C : ℝ}
    (h : ∀ (x : LinftyTimeState μ) (N : ℕ), ∑ t ∈ Finset.range N, |νt t (x t)| ≤ C * ‖x‖)
    (x : LinftyTimeState μ) : Summable fun t => |νt t (x t)| :=
  summable_of_sum_range_le (fun _ => abs_nonneg _) (h x)

/-- `ν(x) = Σ_t ν_t(x_t)` as a continuous linear functional, given the bound
`Σ_{t<N} |ν_t(x_t)| ≤ C ‖x‖_s` (the step missing from the book's proof of Theorem 15.9). -/
noncomputable def linftySumDual (νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))) (C : ℝ)
    (h : ∀ (x : LinftyTimeState μ) (N : ℕ), ∑ t ∈ Finset.range N, |νt t (x t)| ≤ C * ‖x‖) :
    StrongDual ℝ (LinftyTimeState μ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' t, νt t (x t)
      map_add' := fun x y => by
        simp only [lp.coeFn_add, Pi.add_apply, map_add]
        exact (summable_abs_of_sum_le h x).of_abs.tsum_add (summable_abs_of_sum_le h y).of_abs
      map_smul' := fun c x => by
        simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact tsum_mul_left }
    C fun x => by
      rw [Real.norm_eq_abs]
      calc |∑' t, νt t (x t)| ≤ ∑' t, |νt t (x t)| := by
            simpa only [Real.norm_eq_abs] using
              norm_tsum_le_tsum_norm (f := fun t => νt t (x t)) (by
                simpa only [Real.norm_eq_abs] using summable_abs_of_sum_le h x)
        _ ≤ C * ‖x‖ := Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) (h x)

/-- `ν(x) = Σ_t ν_t(x_t)`, the series converging absolutely. -/
theorem hasSum_linftySumDual (νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))) (C : ℝ)
    (h : ∀ (x : LinftyTimeState μ) (N : ℕ), ∑ t ∈ Finset.range N, |νt t (x t)| ≤ C * ‖x‖)
    (x : LinftyTimeState μ) : HasSum (fun t => νt t (x t)) (linftySumDual νt C h x) :=
  (summable_abs_of_sum_le h x).of_abs.hasSum

/-- `‖ν‖ ≤ C`. -/
theorem norm_linftySumDual_le (νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (x : LinftyTimeState μ) (N : ℕ), ∑ t ∈ Finset.range N, |νt t (x t)| ≤ C * ‖x‖) :
    ‖linftySumDual νt C h‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-- **Steps 2 and 5 of the proof of Theorem 15.9, with the continuity of `ν` (NOTE p. 471)**:
for `φ ∈ S*` there are `A_{t n} ↓ 0` in each `𝒵^t` and `ν_t ∈ X_t*` with
`ν_t(a) = lim_n ψ_t(a^{A_{t n}})` (Lemma 15.7 applied to each `ψ_t`), `ν_t(a) = ∫ p_t a dμ^t` with
`p_t ∈ L¹(μ^t)`, and `ν(x) = Σ_t ν_t(x_t)` is a continuous linear functional with `‖ν‖ ≤ ‖φ‖`. -/
theorem exists_linftyTimeState_decomposition [∀ t, IsFiniteMeasure (μ t)]
    (φ : StrongDual ℝ (LinftyTimeState μ)) :
    ∃ A : ∀ t, ℕ → Set (Ω t), (∀ t, LinftyNullSeq (μ t) (A t)) ∧
      ∃ νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t)),
        (∀ t a, Tendsto (fun n => linftyCoordDual φ t (linftyTrunc (μ t) (A t n) a)) atTop
          (𝓝 (νt t a))) ∧
        (∀ t, ∃ p : Ω t → ℝ, Integrable p (μ t) ∧ ∀ a, νt t a = ∫ z, p z * a z ∂(μ t)) ∧
        ∃ ν : StrongDual ℝ (LinftyTimeState μ), ‖ν‖ ≤ ‖φ‖ ∧
          ∀ x, HasSum (fun t => νt t (x t)) (ν x) := by
  choose A hAm hAa hAt νt hνn hνlim hνeq p hp hνp using
    fun t => lemma_15_7 (linftyCoordDual φ t)
  have hbound : ∀ (x : LinftyTimeState μ) (N : ℕ),
      ∑ t ∈ Finset.range N, |νt t (x t)| ≤ ‖φ‖ * ‖x‖ := by
    intro x N
    have hlim : Tendsto (fun n => ∑ t ∈ Finset.range N,
        |linftyCoordDual φ t (linftyTrunc (μ t) (A t n) (x t))|) atTop
        (𝓝 (∑ t ∈ Finset.range N, |νt t (x t)|)) :=
      tendsto_finsetSum _ fun t _ => (hνlim t (x t)).abs
    refine le_of_tendsto' hlim fun n => ?_
    have := sum_abs_linftyCoordDual_le φ (linftyEventTrunc (fun t => A t n) x) N
    simp only [linftyEventTrunc_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_left (norm_linftyCoordMap_apply_le _ _ x)
      (norm_nonneg φ))
  exact ⟨A, fun t => ⟨hAm t, hAa t, hAt t⟩, νt, hνlim, fun t => ⟨p t, hp t, hνp t⟩,
    linftySumDual νt ‖φ‖ hbound, norm_linftySumDual_le νt (norm_nonneg φ) hbound,
    hasSum_linftySumDual νt ‖φ‖ hbound⟩

/-- **Assumption 15.6** for the time–state space (p. 465, extended on p. 469): time truncations
of consumption and production plans are feasible far enough out. -/
def Assumption15_6_timeState (X : ι → Set (LinftyTimeState μ)) (Y : κ → Set (LinftyTimeState μ)) :
    Prop :=
  (∀ i, ∀ x ∈ X i, ∀ᶠ T in atTop, linftyTimeTrunc T x ∈ X i) ∧
    ∀ j, ∀ y ∈ Y j, ∀ᶠ T in atTop, linftyTimeTrunc T y ∈ Y j

/-- **Assumption 15.7** for the time–state space (p. 465, extended on p. 469). -/
def Assumption15_7_timeState (X : ι → Set (LinftyTimeState μ))
    (u : ι → LinftyTimeState μ → ℝ) : Prop :=
  ∀ i, ∀ x ∈ X i, ∀ x' ∈ X i, u i x' < u i x → ∀ᶠ T in atTop, u i x' < u i (linftyTimeTrunc T x)

/-- **Assumption 15.8′** (p. 470): for every period `t`, if `x ∈ Xᵢ` and `A_{t n} ↓ 0` in `𝒵^t`
then `x^{A_{t n}} ∈ Xᵢ` for all large `n`; likewise for each `Yⱼ`. -/
def Assumption15_8' (μ : ∀ t, Measure (Ω t)) (X : ι → Set (LinftyTimeState μ))
    (Y : κ → Set (LinftyTimeState μ)) : Prop :=
  (∀ i t, ∀ x ∈ X i, ∀ A : ℕ → Set (Ω t), LinftyNullSeq (μ t) A →
      ∀ᶠ n in atTop, linftyPeriodTrunc t (A n) x ∈ X i) ∧
    ∀ j t, ∀ y ∈ Y j, ∀ A : ℕ → Set (Ω t), LinftyNullSeq (μ t) A →
      ∀ᶠ n in atTop, linftyPeriodTrunc t (A n) y ∈ Y j

/-- **Assumption 15.9′** (p. 470): for every period `t`, if `x, x′ ∈ Xᵢ`, `uᵢ(x) > uᵢ(x′)` and
`A_{t n} ↓ 0` then `uᵢ(x^{A_{t n}}) > uᵢ(x′)` for all large `n`. -/
def Assumption15_9' (μ : ∀ t, Measure (Ω t)) (X : ι → Set (LinftyTimeState μ))
    (u : ι → LinftyTimeState μ → ℝ) : Prop :=
  ∀ i t, ∀ x ∈ X i, ∀ x' ∈ X i, u i x' < u i x → ∀ A : ℕ → Set (Ω t), LinftyNullSeq (μ t) A →
    ∀ᶠ n in atTop, u i x' < u i (linftyPeriodTrunc t (A n) x)

/-- Bookkeeping for the iterated limits: with the first `k` periods removed, the period-`k`
truncation of `w` is `w` with the first `k + 1` periods removed plus `w_k^B` in period `k`. -/
theorem linftyPeriodTrunc_drop (k : ℕ) (B : Set (Ω k)) (w : LinftyTimeState μ) :
    linftyPeriodTrunc k B w -
        ∑ t ∈ Finset.range k, linftyTSSingle t (linftyPeriodTrunc k B w t) =
      (w - ∑ t ∈ Finset.range (k + 1), linftyTSSingle t (w t)) +
        linftyTSSingle k (linftyTrunc (μ k) B (w k)) := by
  refine lp.ext (funext fun s => ?_)
  rw [lp.coeFn_sub, lp.coeFn_add, lp.coeFn_sub, Pi.sub_apply, Pi.add_apply, Pi.sub_apply,
    linftyTSSingle_sum_apply, linftyTSSingle_sum_apply, linftyTSSingle_apply]
  rcases lt_trichotomy s k with h | rfl | h
  · have h' : s < k + 1 := by omega
    simp only [h, h', ↓reduceIte, Pi.single_eq_of_ne h.ne, linftyPeriodTrunc_apply_of_ne h.ne]
    simp
  · simp only [lt_self_iff_false, Nat.lt_succ_self, ↓reduceIte, Pi.single_eq_same,
      linftyPeriodTrunc_apply_self]
    simp
  · have h1 : ¬ s < k := by omega
    have h2 : ¬ s < k + 1 := by omega
    simp only [h1, h2, ↓reduceIte, Pi.single_eq_of_ne h.ne', linftyPeriodTrunc_apply_of_ne h.ne']
    simp

/-- `x^T` with its first `T + 1` periods removed is `0`. -/
theorem linftyTimeTrunc_drop (T : ℕ) (w : LinftyTimeState μ) :
    linftyTimeTrunc T w - ∑ t ∈ Finset.range (T + 1), linftyTSSingle t (linftyTimeTrunc T w t) =
      0 := by
  refine lp.ext (funext fun s => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, linftyTSSingle_sum_apply, lp.coeFn_zero, Pi.zero_apply]
  by_cases h : s < T + 1
  · simp only [h, ↓reduceIte, sub_self]
  · simp only [h, ↓reduceIte, linftyTimeTrunc_apply, show ¬ s ≤ T by omega, sub_zero]

omit [Fintype ι] [Fintype κ] in
/-- **Step 3, (13), by iterated limits** (the repair of the NOTE to p. 472). If `z ∈ Xᵢ` with
`uᵢ(z) > uᵢ(x⁰)` then `φ(x⁰) ≤ Σ_{t<k} ν_t(z_t) + φ(z with periods < k removed)`: truncate
period `k − 1` (15.8′, 15.9′), apply the case `k − 1` to the truncated point, and let the
period-`k − 1` index tend to infinity. No common truncation index is needed. -/
theorem linftyTS_consumer_bound {X : ι → Set (LinftyTimeState μ)}
    {Y : κ → Set (LinftyTimeState μ)} {u : ι → LinftyTimeState μ → ℝ}
    (h8 : Assumption15_8' μ X Y) (h9 : Assumption15_9' μ X u)
    {φ : StrongDual ℝ (LinftyTimeState μ)} {i : ι} {x0 : LinftyTimeState μ} (hx0 : x0 ∈ X i)
    (hφ : ∀ z ∈ X i, u i x0 ≤ u i z → φ x0 ≤ φ z)
    {A : ∀ t, ℕ → Set (Ω t)} (hA : ∀ t, LinftyNullSeq (μ t) (A t))
    {νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))}
    (hν : ∀ t a, Tendsto (fun n => linftyCoordDual φ t (linftyTrunc (μ t) (A t n) a)) atTop
      (𝓝 (νt t a))) (k : ℕ) :
    ∀ w ∈ X i, u i x0 < u i w → φ x0 ≤ ∑ t ∈ Finset.range k, νt t (w t) +
      φ (w - ∑ t ∈ Finset.range k, linftyTSSingle t (w t)) := by
  induction k with
  | zero =>
    intro w hw hlt
    simpa using hφ w hw hlt.le
  | succ k ih =>
    intro w hw hlt
    have hev : ∀ᶠ n in atTop, φ x0 ≤ ∑ t ∈ Finset.range k, νt t (w t) +
        (φ (w - ∑ t ∈ Finset.range (k + 1), linftyTSSingle t (w t)) +
          linftyCoordDual φ k (linftyTrunc (μ k) (A k n) (w k))) := by
      filter_upwards [h8.1 i k w hw (A k) (hA k), h9 i k w hw x0 hx0 hlt (A k) (hA k)]
        with n hn1 hn2
      have h := ih _ hn1 hn2
      rw [linftyPeriodTrunc_drop, map_add, ← linftyCoordDual_apply] at h
      rwa [Finset.sum_congr rfl fun t ht => by
        rw [linftyPeriodTrunc_apply_of_ne (Finset.mem_range.1 ht).ne]] at h
    have hlim := (tendsto_const_nhds (x := ∑ t ∈ Finset.range k, νt t (w t))).add
      ((tendsto_const_nhds (x := φ (w - ∑ t ∈ Finset.range (k + 1),
        linftyTSSingle t (w t)))).add (hν k (w k)))
    have := ge_of_tendsto hlim hev
    rw [Finset.sum_range_succ]
    linarith

omit [Fintype ι] [Fintype κ] in
/-- **Step 3, (14), by iterated limits**: for `w ∈ Yⱼ`,
`Σ_{t<k} ν_t(w_t) + φ(w with periods < k removed) ≤ φ(y⁰)`. -/
theorem linftyTS_firm_bound {X : ι → Set (LinftyTimeState μ)}
    {Y : κ → Set (LinftyTimeState μ)} (h8 : Assumption15_8' μ X Y)
    {φ : StrongDual ℝ (LinftyTimeState μ)} {j : κ} {y0 : LinftyTimeState μ}
    (hφ : ∀ w ∈ Y j, φ w ≤ φ y0)
    {A : ∀ t, ℕ → Set (Ω t)} (hA : ∀ t, LinftyNullSeq (μ t) (A t))
    {νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))}
    (hν : ∀ t a, Tendsto (fun n => linftyCoordDual φ t (linftyTrunc (μ t) (A t n) a)) atTop
      (𝓝 (νt t a))) (k : ℕ) :
    ∀ w ∈ Y j, ∑ t ∈ Finset.range k, νt t (w t) +
      φ (w - ∑ t ∈ Finset.range k, linftyTSSingle t (w t)) ≤ φ y0 := by
  induction k with
  | zero =>
    intro w hw
    simpa using hφ w hw
  | succ k ih =>
    intro w hw
    have hev : ∀ᶠ n in atTop, ∑ t ∈ Finset.range k, νt t (w t) +
        (φ (w - ∑ t ∈ Finset.range (k + 1), linftyTSSingle t (w t)) +
          linftyCoordDual φ k (linftyTrunc (μ k) (A k n) (w k))) ≤ φ y0 := by
      filter_upwards [h8.2 j k w hw (A k) (hA k)] with n hn
      have h := ih _ hn
      rw [linftyPeriodTrunc_drop, map_add, ← linftyCoordDual_apply] at h
      rwa [Finset.sum_congr rfl fun t ht => by
        rw [linftyPeriodTrunc_apply_of_ne (Finset.mem_range.1 ht).ne]] at h
    have hlim := (tendsto_const_nhds (x := ∑ t ∈ Finset.range k, νt t (w t))).add
      ((tendsto_const_nhds (x := φ (w - ∑ t ∈ Finset.range (k + 1),
        linftyTSSingle t (w t)))).add (hν k (w k)))
    have := le_of_tendsto hlim hev
    rw [Finset.sum_range_succ]
    linarith

/-- **Theorem 15.9** (p. 470). On the time–state space, under Assumptions 15.1, 15.2, 15.6, 15.7,
15.8′ and 15.9′, if `φ ∈ S*` supports the feasible allocation (conditions (4), (5)) and every
consumer has a strictly preferred point, then there is a continuous linear `ν` with
`‖ν‖ ≤ ‖φ‖` supporting the allocation and, as in (9),
`ν(x) = Σ_t ∫ p_t(z^t) x_t(z^t) dμ^t(z^t)` with every `p_t ∈ L¹(μ^t)`. -/
theorem theorem_15_9 [∀ t, IsFiniteMeasure (μ t)] {X : ι → Set (LinftyTimeState μ)}
    {u : ι → LinftyTimeState μ → ℝ} {Y : κ → Set (LinftyTimeState μ)}
    {x : ι → LinftyTimeState μ} {y : κ → LinftyTimeState μ}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (h6 : Assumption15_6_timeState X Y)
    (h7 : Assumption15_7_timeState X u) (h8 : Assumption15_8' μ X Y) (h9 : Assumption15_9' μ X u)
    (hF : Feasible X Y x y) {φ : StrongDual ℝ (LinftyTimeState μ)}
    (hφ : SupportsAllocation X u Y x y φ) (hsat : ∀ i, ∃ xhat ∈ X i, u i (x i) < u i xhat) :
    ∃ ν : StrongDual ℝ (LinftyTimeState μ), ‖ν‖ ≤ ‖φ‖ ∧ SupportsAllocation X u Y x y ν ∧
      ∃ p : ∀ t, Ω t → ℝ, (∀ t, Integrable (p t) (μ t)) ∧
        ∀ z, HasSum (fun t => ∫ w, p t w * z t w ∂(μ t)) (ν z) := by
  obtain ⟨A, hA, νt, hνlim, hνp, ν, hνn, hνsum⟩ := exists_linftyTimeState_decomposition φ
  choose p hp hpν using hνp
  refine ⟨ν, hνn, supportsAllocation_of_limit_bounds (φ := φ) h1 h2 hF hsat ?_ ?_, p, hp,
    fun z => by simpa only [hpν] using hνsum z⟩
  · intro i z hz hlt
    have hev : ∀ᶠ T in atTop, φ (x i) ≤ ∑ t ∈ Finset.range (T + 1), νt t (z t) := by
      filter_upwards [h6.1 i z hz, h7 i z hz (x i) (hF.1 i) hlt] with T hT1 hT2
      have h := linftyTS_consumer_bound h8 h9 (hF.1 i) (hφ.1 i) hA hνlim (T + 1) _ hT1 hT2
      rw [linftyTimeTrunc_drop, map_zero, add_zero] at h
      rwa [Finset.sum_congr rfl (g := fun t => νt t (z t)) fun t ht => by
        simp only [linftyTimeTrunc_apply, Nat.lt_succ_iff.1 (Finset.mem_range.1 ht),
          ↓reduceIte]] at h
    exact ge_of_tendsto ((hνsum z).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)) hev
  · intro j w hw
    have hev : ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1), νt t (w t) ≤ φ (y j) := by
      filter_upwards [h6.2 j w hw] with T hT
      have h := linftyTS_firm_bound h8 (hφ.2 j) hA hνlim (T + 1) _ hT
      rw [linftyTimeTrunc_drop, map_zero, add_zero] at h
      rwa [Finset.sum_congr rfl (g := fun t => νt t (w t)) fun t ht => by
        simp only [linftyTimeTrunc_apply, Nat.lt_succ_iff.1 (Finset.mem_range.1 ht),
          ↓reduceIte]] at h
    exact le_of_tendsto ((hνsum w).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)) hev

end StokeyLucasPrescott.ParetoOptimaEquilibria
