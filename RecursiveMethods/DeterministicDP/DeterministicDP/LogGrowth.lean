/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.UnboundedReturns
import DeterministicDP.Assumption42

/-!
# The unit-elastic growth model

SLP §4.4, pp. 93–95: `max Σ βᵗ ln(k_t^α − k_{t+1})` with `0 < α, β < 1` on `X = (0, ∞)`, where
returns are unbounded above and below.

* `logΓ`, `logF`: `Γ(k) = (0, k^α)` and `F(k, y) = ln(k^α − y)`. The book's `Γ(k) = (0, k^α]`
  gives `F(k, k^α) = ln 0 = −∞`, while `F` must be real-valued; the open interval has the same
  supremum.
* `log_assumption41`, `log_assumption42`: Assumptions 4.1–4.2 hold.
* `log_opT_affine`: `T` maps `A + B ln k`, `B = α/(1 − αβ)`, to `(βA + C) + B ln k`, with
  maximizer `αβk^α`; so `Tⁿv̂ = C(1 − βⁿ)/(1 − β) + B ln k` for `v̂ = B ln k` (`log_iterate`).
* `log_vstar`: `v*(k) = C/(1 − β) + B ln k` (Theorem 4.14).
* `log_policy_optimal`: the plan `k_{t+1} = αβk_t^α` is optimal (Theorem 4.5).
-/

open Filter Topology Real

namespace StokeyLucasPrescott.DeterministicDP

/-- `(0, ∞)`. -/
abbrev PosR := {k : ℝ // 0 < k}

variable {α β : ℝ}

/-- `Γ(k) = (0, k^α)`. -/
def logΓ (α : ℝ) (k : PosR) : Set PosR := {y | y.1 < k.1 ^ α}

/-- `F(k, y) = ln(k^α − y)`. -/
noncomputable def logF (α : ℝ) (k y : PosR) : ℝ := Real.log (k.1 ^ α - y.1)

/-- `B = α/(1 − αβ)`. -/
noncomputable def coefB (α β : ℝ) : ℝ := α / (1 - α * β)

/-- `C = ln(1 − αβ) + (αβ/(1 − αβ)) ln(αβ)`. -/
noncomputable def coefC (α β : ℝ) : ℝ :=
  Real.log (1 - α * β) + α * β / (1 - α * β) * Real.log (α * β)

/-- `A + B ln k`. -/
noncomputable def affineLog (α β A : ℝ) (k : PosR) : EReal :=
  ((A + coefB α β * Real.log k.1 : ℝ) : EReal)

/-- The optimal saving `αβk^α ∈ Γ(k)`. -/
noncomputable def logPolicy (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k : PosR) : PosR :=
  ⟨α * β * k.1 ^ α, by have := rpow_pos_of_pos k.2 α; positivity⟩

variable (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
include hα0 hα1 hβ0 hβ1

omit hβ0 in
theorem αβ_lt_one : α * β < 1 := by nlinarith

omit hβ0 in
theorem coefB_pos : 0 < coefB α β := div_pos hα0 (by linarith [αβ_lt_one hα0 hα1 hβ1])

theorem coefC_neg : coefC α β < 0 := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have hab : 0 < α * β := mul_pos hα0 hβ0
  have l1 : Real.log (1 - α * β) < 0 := Real.log_neg (by linarith) (by linarith)
  have l2 : Real.log (α * β) < 0 := Real.log_neg hab h1
  have : 0 < α * β / (1 - α * β) := div_pos hab (by linarith)
  unfold coefC; nlinarith

theorem logPolicy_mem (k : PosR) : logPolicy α β hα0 hβ0 k ∈ logΓ α k := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have := rpow_pos_of_pos k.2 α
  change α * β * k.1 ^ α < k.1 ^ α
  nlinarith

/-- The maximization: for `y ∈ (0, k^α)`,
`ln(k^α − y) + β(A + B ln y) ≤ ln((1 − αβ)k^α) + β(A + B ln(αβk^α))`. -/
theorem log_objective_le (A : ℝ) (k y : PosR) (hy : y ∈ logΓ α k) :
    logF α k y + β * (A + coefB α β * Real.log y.1) ≤
      logF α k (logPolicy α β hα0 hβ0 k) +
        β * (A + coefB α β * Real.log (logPolicy α β hα0 hβ0 k).1) := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have hab : 0 < α * β := mul_pos hα0 hβ0
  set c := k.1 ^ α
  have hc : 0 < c := rpow_pos_of_pos k.2 α
  have hy0 : 0 < y.1 := y.2
  have hyc : y.1 < c := hy
  simp only [logF, logPolicy, coefB]
  have hcy : 0 < c - y.1 := by linarith
  have hcs : 0 < c - α * β * c := by nlinarith
  have hsc : 0 < α * β * c := by positivity
  -- `ln u ≤ u − 1` at `u = (c − y)/((1 − αβ)c)` and `u = y/(αβc)`
  have e1 := Real.log_le_sub_one_of_pos (div_pos hcy hcs)
  have e2 := Real.log_le_sub_one_of_pos (div_pos hy0 hsc)
  rw [Real.log_div hcy.ne' hcs.ne'] at e1
  rw [Real.log_div hy0.ne' hsc.ne'] at e2
  have hk : 0 < β * (α / (1 - α * β)) := mul_pos hβ0 (div_pos hα0 (by linarith))
  have e2' := mul_le_mul_of_nonneg_left e2 hk.le
  have hne : (1 - α * β) ≠ 0 := by linarith
  have key : (c - y.1) / (c - α * β * c) - 1 + β * (α / (1 - α * β)) * (y.1 / (α * β * c) - 1)
      = 0 := by
    rw [show c - α * β * c = (1 - α * β) * c by ring]
    field_simp
    ring
  nlinarith

/-- `T` maps `A + B ln k` to `(βA + C) + B ln k`. -/
theorem log_opT_affine (A : ℝ) :
    opT (logΓ α) (logF α) β (affineLog α β A) = affineLog α β (β * A + coefC α β) := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have hab : 0 < α * β := mul_pos hα0 hβ0
  funext k
  have hval : logF α k (logPolicy α β hα0 hβ0 k) +
      β * (A + coefB α β * Real.log (logPolicy α β hα0 hβ0 k).1) =
      β * A + coefC α β + coefB α β * Real.log k.1 := by
    have hc : 0 < k.1 ^ α := rpow_pos_of_pos k.2 α
    have hne : (1 - α * β) ≠ 0 := by linarith
    simp only [logF, logPolicy, coefB, coefC]
    rw [show k.1 ^ α - α * β * k.1 ^ α = (1 - α * β) * k.1 ^ α by ring,
      Real.log_mul (by linarith) hc.ne', Real.log_mul hab.ne' hc.ne', Real.log_rpow k.2]
    field_simp
    ring
  refine le_antisymm (iSup₂_le fun y hy => ?_) ?_
  · rw [affineLog, affineLog, ← EReal.coe_mul, ← EReal.coe_add, ← hval]
    exact EReal.coe_le_coe_iff.2 (log_objective_le hα0 hα1 hβ0 hβ1 A k y hy)
  · refine le_trans ?_ (le_biSup _ (logPolicy_mem hα0 hα1 hβ0 hβ1 k))
    rw [affineLog, affineLog, ← EReal.coe_mul, ← EReal.coe_add, ← hval]

/-- `Tⁿv̂ = C(1 − βⁿ)/(1 − β) + B ln k` for `v̂ = B ln k` (p. 95). -/
theorem log_iterate (n : ℕ) :
    (opT (logΓ α) (logF α) β)^[n] (affineLog α β 0) =
      affineLog α β (coefC α β * (1 - β ^ n) / (1 - β)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, log_opT_affine hα0 hα1 hβ0 hβ1]
    congr 1
    have hne : (1 - β) ≠ 0 := by linarith
    field_simp
    ring

theorem log_assumption41 : Assumption41 (logΓ α) := fun k =>
  ⟨logPolicy α β hα0 hβ0 k, logPolicy_mem hα0 hα1 hβ0 hβ1 k⟩

omit hα1 hβ0 hβ1 in
/-- Along feasible plans, `ln k_t ≤ αᵗ ln k₀` (the technology bound (4), p. 94). -/
theorem log_capital_le {k₀ : PosR} {k : ℕ → PosR} (hk : k ∈ Feasible (logΓ α) k₀) (t : ℕ) :
    Real.log (k t).1 ≤ α ^ t * Real.log k₀.1 := by
  induction t with
  | zero => simp [hk.1]
  | succ t ih =>
    have h := Real.log_lt_log (k (t + 1)).2 (hk.2 t)
    rw [Real.log_rpow (k t).2] at h
    calc Real.log (k (t + 1)).1 ≤ α * Real.log (k t).1 := h.le
      _ ≤ α * (α ^ t * Real.log k₀.1) := mul_le_mul_of_nonneg_left ih hα0.le
      _ = α ^ (t + 1) * Real.log k₀.1 := by ring

omit hα1 hβ0 hβ1 in
/-- (4), p. 94: `F(k_t, k_{t+1}) ≤ αᵗ⁺¹ ln k₀`. -/
theorem logF_le {k₀ : PosR} {k : ℕ → PosR} (hk : k ∈ Feasible (logΓ α) k₀) (t : ℕ) :
    logF α (k t) (k (t + 1)) ≤ α ^ (t + 1) * Real.log k₀.1 := by
  have hc : 0 < (k t).1 ^ α := rpow_pos_of_pos (k t).2 α
  have hlt : (k (t + 1)).1 < (k t).1 ^ α := hk.2 t
  have hpos : 0 < (k t).1 ^ α - (k (t + 1)).1 := by linarith
  calc logF α (k t) (k (t + 1)) ≤ Real.log ((k t).1 ^ α) :=
        Real.log_le_log hpos (by linarith [(k (t + 1)).2])
    _ = α * Real.log (k t).1 := Real.log_rpow (k t).2 α
    _ ≤ α * (α ^ t * Real.log k₀.1) :=
        mul_le_mul_of_nonneg_left (log_capital_le hα0 hk t) hα0.le
    _ = α ^ (t + 1) * Real.log k₀.1 := by ring

theorem log_assumption42 : Assumption42 (logΓ α) (logF α) β :=
  assumption42_of_summable_pos fun k₀ k hk =>
    summable_max_of_le_geometric (mul_pos hα0 hβ0).le (αβ_lt_one hα0 hα1 hβ1)
      (by positivity : (0 : ℝ) ≤ α * |Real.log k₀.1|) fun t => by
        have := logF_le hα0 hk t
        calc β ^ t * logF α (k t) (k (t + 1)) ≤ β ^ t * (α ^ (t + 1) * |Real.log k₀.1|) :=
              mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_left
                (le_abs_self _) (pow_nonneg hα0.le _))) (pow_nonneg hβ0.le t)
          _ = α * |Real.log k₀.1| * (α * β) ^ t := by rw [mul_pow]; ring

/-- **p. 95.** `v*(k) = C/(1 − β) + B ln k`. -/
theorem log_vstar : vstar (logΓ α) (logF α) β = affineLog α β (coefC α β / (1 - β)) := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have hB := coefB_pos hα0 hα1 hβ1
  have hC := coefC_neg hα0 hα1 hβ0 hβ1
  -- the limit of the iterates
  have hlim : limitFn (logΓ α) (logF α) β (affineLog α β 0) =
      affineLog α β (coefC α β / (1 - β)) := by
    funext k
    simp only [limitFn, log_iterate hα0 hα1 hβ0 hβ1]
    have hanti : Antitone fun n : ℕ => affineLog α β (coefC α β * (1 - β ^ n) / (1 - β)) k := by
      intro m n hmn
      refine EReal.coe_le_coe_iff.2 (add_le_add_left ?_ _)
      refine div_le_div_of_nonneg_right ?_ (by linarith)
      have : β ^ n ≤ β ^ m := pow_le_pow_of_le_one hβ0.le hβ1.le hmn
      nlinarith
    have hconv : Tendsto (fun n : ℕ => affineLog α β (coefC α β * (1 - β ^ n) / (1 - β)) k)
        atTop (𝓝 (affineLog α β (coefC α β / (1 - β)) k)) := by
      refine EReal.tendsto_coe.2 ?_
      have := ((((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_sub 1).const_mul
        (coefC α β)).div_const (1 - β)).add_const (coefB α β * Real.log k.1)
      simpa using this
    exact tendsto_nhds_unique (tendsto_atTop_iInf hanti) hconv
  rw [← hlim]
  refine (theorem_4_14 hβ0 (log_assumption41 hα0 hα1 hβ0 hβ1)
    (log_assumption42 hα0 hα1 hβ0 hβ1) (fun k₀ k hk => ?_) (fun k₀ k hk => ?_) ?_).symm
  · -- (2): `βⁿB ln kₙ ≤ B|ln k₀|(αβ)ⁿ → 0`
    have hb : ∀ n, ((β ^ n : ℝ) : EReal) * affineLog α β 0 (k n) ≤
        ((coefB α β * |Real.log k₀.1| * (α * β) ^ n : ℝ) : EReal) := fun n => by
      rw [affineLog, ← EReal.coe_mul]
      refine EReal.coe_le_coe_iff.2 ?_
      have := log_capital_le hα0 hk n
      have h2 : α ^ n * Real.log k₀.1 ≤ α ^ n * |Real.log k₀.1| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hα0.le n)
      calc β ^ n * (0 + coefB α β * Real.log (k n).1)
          ≤ β ^ n * (coefB α β * (α ^ n * |Real.log k₀.1|)) := by
            rw [zero_add]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (this.trans h2) hB.le)
              (pow_nonneg hβ0.le n)
        _ = coefB α β * |Real.log k₀.1| * (α * β) ^ n := by rw [mul_pow]; ring
    have hzero : Tendsto (fun n => ((coefB α β * |Real.log k₀.1| * (α * β) ^ n : ℝ) : EReal))
        atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_pos hα0 hβ0).le h1).const_mul
        (coefB α β * |Real.log k₀.1|)
      simpa using EReal.tendsto_coe.2 this
    exact (limsup_le_limsup (Eventually.of_forall hb)).trans hzero.limsup_eq.le
  · -- (3): `u(k) ≤ B ln k₀`
    have hps : ∀ n, (partialSum (logF α) β k n : EReal) ≤
        ((∑ t ∈ Finset.range (n + 1), α * Real.log k₀.1 * (α * β) ^ t : ℝ) : EReal) :=
      fun n => EReal.coe_le_coe_iff.2 (Finset.sum_le_sum fun t _ => by
        have := logF_le hα0 hk t
        calc β ^ t * logF α (k t) (k (t + 1)) ≤ β ^ t * (α ^ (t + 1) * Real.log k₀.1) :=
              mul_le_mul_of_nonneg_left this (pow_nonneg hβ0.le t)
          _ = α * Real.log k₀.1 * (α * β) ^ t := by rw [mul_pow]; ring)
    have hgeo : Tendsto (fun n => ((∑ t ∈ Finset.range (n + 1), α * Real.log k₀.1 *
        (α * β) ^ t : ℝ) : EReal)) atTop (𝓝 (affineLog α β 0 k₀)) := by
      refine EReal.tendsto_coe.2 ?_
      have hs := (hasSum_geometric_of_lt_one (mul_pos hα0 hβ0).le h1).mul_left
        (α * Real.log k₀.1)
      have := hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
      convert this using 2
      · simp
      · simp only [coefB, zero_add, div_eq_mul_inv]; ring
    exact le_of_tendsto_of_tendsto (tendsto_total (log_assumption42 hα0 hα1 hβ0 hβ1) hk) hgeo
      (Eventually.of_forall hps)
  · -- the limit is a fixed point
    rw [hlim, log_opT_affine hα0 hα1 hβ0 hβ1]
    congr 1
    have hne : (1 - β) ≠ 0 := by linarith
    field_simp
    ring

/-- **p. 95.** The policy `g(k) = αβk^α` generates an optimal plan (Theorem 4.5). -/
theorem log_policy_optimal (k₀ : PosR) :
    total (logF α) β (fun t => (logPolicy α β hα0 hβ0)^[t] k₀) =
      vstar (logΓ α) (logF α) β k₀ := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  set g := logPolicy α β hα0 hβ0
  set k : ℕ → PosR := fun t => g^[t] k₀
  have hk : ∀ t, k (t + 1) = g (k t) := fun t => Function.iterate_succ_apply' _ _ _
  set A := coefC α β / (1 - β)
  have hvs := log_vstar hα0 hα1 hβ0 hβ1
  refine theorem_4_5 hβ0.le (log_assumption42 hα0 hα1 hβ0 hβ1)
    ⟨rfl, fun t => hk t ▸ logPolicy_mem hα0 hα1 hβ0 hβ1 _⟩ (fun t => ?_) ?_
  · -- (9): the maximizer attains `T v* = v*`
    rw [hvs, hk t, affineLog, affineLog, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    have hc : 0 < (k t).1 ^ α := rpow_pos_of_pos (k t).2 α
    have hab : 0 < α * β := mul_pos hα0 hβ0
    have hne : (1 - α * β) ≠ 0 := by linarith
    have hne' : (1 - β) ≠ 0 := by linarith
    simp only [g, logF, logPolicy, coefB, coefC]
    rw [show (k t).1 ^ α - α * β * (k t).1 ^ α = (1 - α * β) * (k t).1 ^ α by ring,
      Real.log_mul (by linarith) hc.ne', Real.log_mul hab.ne' hc.ne', Real.log_rpow (k t).2]
    field_simp
    ring
  · -- (11): `ln k_t` stays bounded, so `βᵗv*(k_t) → 0`
    set M := |Real.log k₀.1| + |Real.log (α * β)| / (1 - α)
    have hlog : ∀ t, |Real.log (k t).1| ≤ M := by
      intro t
      induction t with
      | zero =>
        simp only [k, Function.iterate_zero, id_eq, M]
        have : 0 ≤ |Real.log (α * β)| / (1 - α) := div_nonneg (abs_nonneg _) (by linarith)
        linarith
      | succ t ih =>
        rw [hk t]
        have hc : 0 < (k t).1 ^ α := rpow_pos_of_pos (k t).2 α
        have e : Real.log (g (k t)).1 = Real.log (α * β) + α * Real.log (k t).1 := by
          simp only [g, logPolicy]
          rw [Real.log_mul (mul_pos hα0 hβ0).ne' hc.ne', Real.log_rpow (k t).2]
        rw [e]
        have hM : |Real.log (α * β)| + α * M ≤ M := by
          simp only [M]
          rw [div_eq_mul_inv]
          have h1α : 0 < 1 - α := by linarith
          have : |Real.log (α * β)| * (1 - α)⁻¹ * (1 - α) = |Real.log (α * β)| := by
            field_simp
          nlinarith [abs_nonneg (Real.log k₀.1), abs_nonneg (Real.log (α * β)),
            inv_pos.2 h1α]
        calc |Real.log (α * β) + α * Real.log (k t).1|
            ≤ |Real.log (α * β)| + α * |Real.log (k t).1| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_of_pos hα0]
          _ ≤ |Real.log (α * β)| + α * M := by gcongr
          _ ≤ M := hM
    have hb : ∀ t, ((β ^ t : ℝ) : EReal) * vstar (logΓ α) (logF α) β (k t) ≤
        (((|A| + coefB α β * M) * β ^ t : ℝ) : EReal) := fun t => by
      rw [hvs, affineLog, ← EReal.coe_mul]
      refine EReal.coe_le_coe_iff.2 ?_
      have hB := coefB_pos hα0 hα1 hβ1
      have h1 : A + coefB α β * Real.log (k t).1 ≤ |A| + coefB α β * M := by
        have := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (k t).1) |>.trans (hlog t))
          hB.le
        linarith [le_abs_self A]
      rw [mul_comm _ (β ^ t)]
      exact mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ0.le t)
    have hzero : Tendsto (fun t => (((|A| + coefB α β * M) * β ^ t : ℝ) : EReal)) atTop
        (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (|A| + coefB α β * M)
      simpa using EReal.tendsto_coe.2 this
    exact (limsup_le_limsup (Eventually.of_forall hb)).trans hzero.limsup_eq.le

end StokeyLucasPrescott.DeterministicDP
