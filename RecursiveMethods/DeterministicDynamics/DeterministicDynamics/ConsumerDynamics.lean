/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.ConsumerRecursive
import DeterministicDynamics.EulerEquations

/-!
# A consumer with recursive preferences (Exercise 6.10)

SLP §6.5, pp. 160–161. The consumer of §5.12 (`ConsumerRecursive`) with a single good and price
`1`: `v(x) = max_{0 ≤ y ≤ x} W[x − y, v(R⁻¹y)]`, written as the choice of consumption
`C = x − y` (`cv c` is the one-good bundle `c`). Wealth `x̄` is **stationary** if consuming
`x̄(1 − R)` is optimal at `x̄`; it leaves next period's wealth at `R⁻¹(x̄ − x̄(1 − R)) = x̄`.

* `exists_unique_fixed_z` (the reduction in **Exercise 6.10b**): for each consumption level
  `c ≥ 0`, `z = W(c, z)` has exactly one solution (`W` is a contraction in `z`). So a stationary
  pair `(x̄, z̄)` is determined by `x̄` alone.
* **Exercise 6.10a** (`ex_6_10a_if`, `ex_6_10a_only_if`): with `W` concave and nonnegative,
  differentiable at `(x̄(1 − R), z̄)` and `0 < R < 1`:
  * if `z̄ = W[x̄(1 − R), z̄]`, `R = W₂[x̄(1 − R), z̄]` and `W₁ ≥ 0` there, then `x̄` is stationary
    and `v(x̄) = z̄`. Concavity gives `v(x_t) − z̄ ≤ W₁(c_t − c̄) + R[v(x_{t+1}) − z̄]` along the
    optimal path, and the budget makes `Σ_{t<T} Rᵗ(c_t − c̄) ≤ Rᵀx̄`;
  * conversely, if `x̄ > 0` is stationary and `W₁ ≠ 0`, then `z̄ = v(x̄)` solves both equations.
    This is the envelope condition and the Euler equation of Exercise 5.12c at `x̄`.
* **Exercise 6.10c** (`ex_6_10c_eq`, `ex_6_10c_ne`): with `W(c, z) = U(c) + βz`, so `W₂ = β`:
  if `β = R`, every wealth level is stationary (the optimal wealth sequence is constant); if
  `β ≠ R` and `U' ≠ 0`, no positive wealth level is.
* **Exercise 6.10d** (`ex_6_10d`): the Euler equation
  `W₁(c_t, z_{t+1}) = R⁻¹W₂(c_t, z_{t+1})W₁(c_{t+1}, z_{t+2})` along an optimal path.

Parts (e) and (f) ask the reader to find conditions for local and global stability, which is
open-ended.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {W : (Fin 1 → ℝ) → ℝ → ℝ} {R β M : ℝ}

/-- The one-good bundle `c`. -/
def cv (c : ℝ) : Fin 1 → ℝ := fun _ => c

/-- The price `1`. -/
def one1 : Fin 1 → ℝ := fun _ => 1

theorem spend_cv (c : ℝ) : spend one1 (cv c) = c := by simp [spend, one1, cv]

theorem cv_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ cv c := fun _ => hc

theorem eq_cv (C : Fin 1 → ℝ) : C = cv (C 0) := by
  funext i; rw [Subsingleton.elim i 0]; rfl

theorem single_eq_cv : (Pi.single 0 1 : Fin 1 → ℝ) = cv 1 := by
  funext i; rw [Subsingleton.elim i 0]; simp [cv]

/-- **Exercise 6.10b (reduction).** `z = W(c, z)` has exactly one solution for each `c ≥ 0`. -/
theorem exists_unique_fixed_z (h : ConsHyp W one1 R β M) {C : Fin 1 → ℝ} (hC : 0 ≤ C) :
    ∃! z, W C z = z := by
  have hc : ContractingWith (Real.toNNReal β) (W C) := by
    refine ⟨Real.toNNReal_lt_one.2 h.β_lt, LipschitzWith.of_dist_le' fun z z' => ?_⟩
    rw [Real.dist_eq, Real.dist_eq]
    exact h.lip C hC z z'
  obtain ⟨z, hz, -⟩ := hc.exists_fixedPoint 0 (edist_ne_top _ _)
  refine ⟨z, hz, fun z' hz' => ?_⟩
  exact hc.fixedPoint_unique' hz' hz

/-- The partial derivative in the good, from the derivative of `W`. -/
theorem hasDerivAt_dir {DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ} {C : Fin 1 → ℝ} {z : ℝ}
    (hDW : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW (C, z)) :
    HasDerivAt (fun x : ℝ => W (C + x • Pi.single 0 1) z) (DW (Pi.single 0 1, 0)) 0 := by
  have hp : HasDerivAt (fun x : ℝ => (C + x • (Pi.single 0 1 : Fin 1 → ℝ), z))
      ((1 : ℝ) • (Pi.single 0 1 : Fin 1 → ℝ), 0) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).smul_const (Pi.single 0 1 : Fin 1 → ℝ)).const_add C).prodMk
      (hasDerivAt_const _ _)
  rw [one_smul] at hp
  exact hDW.comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp)

/-- `DW(u, s) = u₀·W₁ + s·W₂`. -/
theorem dw_apply (DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ) (u : Fin 1 → ℝ) (s : ℝ) :
    DW (u, s) = u 0 * DW (cv 1, 0) + s * DW (0, 1) := by
  have e : (u, s) = u 0 • (cv 1, (0 : ℝ)) + s • ((0 : Fin 1 → ℝ), (1 : ℝ)) := by
    refine Prod.ext ?_ (by simp)
    funext i; rw [Subsingleton.elim i 0]; simp [cv]
  rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Stationary consumption leaves wealth unchanged. -/
theorem nextWealth_bar {x : ℝ} (hR : 0 < R) : nextWealth one1 R x (cv (x * (1 - R))) = x := by
  rw [nextWealth, spend_cv]; field_simp; ring

/-- **Exercise 6.10a (if).** If `z̄ = W[x̄(1 − R), z̄]`, `R = W₂[x̄(1 − R), z̄]` and `W₁ ≥ 0`, then
`x̄` is stationary and `v(x̄) = z̄`. -/
theorem ex_6_10a_if (h : ConsHyp W one1 R β M) (hR1 : R < 1)
    (hconc : ConcaveOn ℝ ({C : Fin 1 → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {x z : ℝ} (hx : 0 ≤ x) (hz : W (cv (x * (1 - R))) z = z)
    {DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ}
    (hDW : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW (cv (x * (1 - R)), z))
    (hW2 : DW (0, 1) = R) (hW1 : 0 ≤ DW (cv 1, 0)) :
    cv (x * (1 - R)) ∈ argmax (consObj W one1 R v) (budgetΓ one1) ⟨x, hx⟩ ∧ v ⟨x, hx⟩ = z := by
  have hR := h.R_pos
  set c := x * (1 - R)
  have hc : 0 ≤ c := mul_nonneg hx (by linarith)
  set A₀ : Wealth := ⟨x, hx⟩
  have hvx : ∀ A : Wealth, v A = maxValue (consObj W one1 R v) (budgetΓ one1) A := fun A =>
    (DFunLike.congr_fun hv A).symm
  have hle : ∀ (A : Wealth) (C : Fin 1 → ℝ), C ∈ budgetΓ one1 A →
      consObj W one1 R v (A, C) ≤ v A := fun A C hC => by
    obtain ⟨-, -, -, hmax⟩ := exists_consT_argmax h v A
    rw [hv] at hmax
    exact hmax C hC
  have hmem : cv c ∈ budgetΓ one1 A₀ :=
    ⟨cv_nonneg hc, by rw [spend_cv]; simp only [A₀, c]; nlinarith⟩
  have hobj : consObj W one1 R v (A₀, cv c) = W (cv c) (v A₀) := by
    simp only [consObj, A₀, c, nextWealth_bar hR, vext_of_nonneg v hx]
  -- `z̄ ≥ 0`
  have hz0 : 0 ≤ z := by
    by_contra hneg
    push Not at hneg
    have h1 := h.lip (cv c) (cv_nonneg hc) z 0
    have h2 := hnn (cv c) 0 (cv_nonneg hc) le_rfl
    rw [hz, sub_zero, abs_of_neg hneg] at h1
    rw [abs_le] at h1
    nlinarith [h.β_lt]
  -- `v(x̄) ≥ z̄`: `v(x̄) ≥ W(c̄, v(x̄))` and `W(c̄, ·)` is a contraction with fixed point `z̄`
  have hlow : z ≤ v A₀ := by
    have h1 := hle A₀ (cv c) hmem
    rw [hobj] at h1
    by_contra hlt
    push Not at hlt
    have h2 := h.lip (cv c) (cv_nonneg hc) z (v A₀)
    rw [hz, abs_of_pos (by linarith : 0 < z - v A₀), abs_le] at h2
    nlinarith [h.β_lt]
  -- the optimal path from `x̄`
  choose sel hsel using fun A : Wealth => exists_consT_argmax h v A
  have hnx : ∀ A : Wealth, 0 ≤ nextWealth one1 R A.1 (sel A) := fun A =>
    div_nonneg (sub_nonneg.2 (hsel A).1.2) hR.le
  set nx : Wealth → Wealth := fun A => ⟨nextWealth one1 R A.1 (sel A), hnx A⟩
  set xs : ℕ → Wealth := fun t => nx^[t] A₀
  have hstep : ∀ t, xs (t + 1) = nx (xs t) := fun t => Function.iterate_succ_apply' nx t A₀
  have hval : ∀ t, v (xs t) = W (sel (xs t)) (v (xs (t + 1))) := fun t => by
    have := (hsel (xs t)).2.1
    rw [hv] at this
    rw [this, consObj, hstep, vext_of_nonneg v (hnx (xs t))]
  have hbudget : ∀ t, R * (xs (t + 1)).1 = (xs t).1 - sel (xs t) 0 := fun t => by
    rw [hstep]
    simp only [nx, nextWealth]
    have : spend one1 (sel (xs t)) = sel (xs t) 0 := by simp [spend, one1]
    rw [this, mul_div_cancel₀ _ hR.ne']
  -- concavity: `v(x_t) − z̄ ≤ W₁(c_t − c̄) + R[v(x_{t+1}) − z̄]`
  have hv0 := (ex_5_12b_concave h hconc hnn hv).1
  have hconcstep : ∀ t, v (xs t) - z ≤ DW (cv 1, 0) * (sel (xs t) 0 - c) +
      R * (v (xs (t + 1)) - z) := fun t => by
    have hsupp := concave_le_fderiv hconc (z₀ := (cv c, z)) (z := (sel (xs t), v (xs (t + 1))))
      ⟨cv_nonneg hc, hz0⟩ ⟨(hsel (xs t)).1.1, hv0 _⟩ hDW
    simp only [hz] at hsupp
    rw [Prod.mk_sub_mk, dw_apply, hW2] at hsupp
    rw [hval t]
    have e : (sel (xs t) - cv c) 0 = sel (xs t) 0 - c := by simp [cv]
    rw [e] at hsupp
    linarith
  -- unrolling
  have hunroll : ∀ T, v A₀ - z ≤ DW (cv 1, 0) * (x - R ^ T * (xs T).1 - x * (1 - R ^ T)) +
      R ^ T * (v (xs T) - z) := fun T => by
    induction T with
    | zero => norm_num [xs, A₀]
    | succ T ih =>
      have h1 := mul_le_mul_of_nonneg_left (hconcstep T) (pow_nonneg hR.le T)
      have h2 := hbudget T
      have e1 : R ^ (T + 1) * (xs (T + 1)).1 = R ^ T * ((xs T).1 - sel (xs T) 0) := by
        rw [pow_succ, mul_assoc, h2]
      rw [e1, pow_succ]
      simp only [c] at h1
      nlinarith
  have hbound : ∀ T, v A₀ - z ≤ R ^ T * (DW (cv 1, 0) * x + (‖v‖ + |z|)) := fun T => by
    have h1 := hunroll T
    have hx0 : 0 ≤ (xs T).1 := (xs T).2
    have hvT : |v (xs T)| ≤ ‖v‖ := by
      simpa [Real.norm_eq_abs] using v.norm_coe_le_norm (xs T)
    have hRT := pow_nonneg hR.le T
    have h2 : R ^ T * (v (xs T) - z) ≤ R ^ T * (‖v‖ + |z|) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self (v (xs T)), neg_abs_le z]) hRT
    have h3 : 0 ≤ DW (cv 1, 0) * (R ^ T * (xs T).1) := mul_nonneg hW1 (mul_nonneg hRT hx0)
    nlinarith
  have hlim : Tendsto (fun T => R ^ T * (DW (cv 1, 0) * x + (‖v‖ + |z|))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hR.le hR1).mul_const
      (DW (cv 1, 0) * x + (‖v‖ + |z|))
  have hup : v A₀ - z ≤ 0 := ge_of_tendsto' hlim hbound
  have hvz : v A₀ = z := by linarith
  refine ⟨⟨hmem, ?_⟩, hvz⟩
  rw [← hvx, hobj, hvz, hz]

/-- **Exercise 6.10a (only if).** If `x̄ > 0` is stationary and `W₁ ≠ 0` at `(x̄(1 − R), v(x̄))`,
then `z̄ = v(x̄)` satisfies `z̄ = W[x̄(1 − R), z̄]` and `R = W₂[x̄(1 − R), z̄]`. -/
theorem ex_6_10a_only_if (h : ConsHyp W one1 R β M) (hR1 : R < 1)
    (hconc : ConcaveOn ℝ ({C : Fin 1 → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {x : ℝ} (hx : 0 < x)
    (hstat : cv (x * (1 - R)) ∈ argmax (consObj W one1 R v) (budgetΓ one1) ⟨x, hx.le⟩)
    {DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ}
    (hDW : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW
      (cv (x * (1 - R)), v ⟨x, hx.le⟩))
    (hW1 : DW (cv 1, 0) ≠ 0) :
    W (cv (x * (1 - R))) (v ⟨x, hx.le⟩) = v ⟨x, hx.le⟩ ∧ DW (0, 1) = R := by
  have hR := h.R_pos
  set A₀ : Wealth := ⟨x, hx.le⟩
  have hvx : ∀ A : Wealth, v A = maxValue (consObj W one1 R v) (budgetΓ one1) A := fun A =>
    (DFunLike.congr_fun hv A).symm
  have hnext : nextWealth one1 R A₀.1 (cv (x * (1 - R))) = x := nextWealth_bar hR
  have hz : vext v (nextWealth one1 R A₀.1 (cv (x * (1 - R)))) = v A₀ := by
    rw [hnext, vext_of_nonneg v hx.le]
  have hCi : 0 < cv (x * (1 - R)) 0 := mul_pos hx (by linarith)
  have hdir := hasDerivAt_dir hDW
  rw [← hz] at hdir hDW
  have henv := ex_5_12c_envelope h hconc hnn hv (A₀ := A₀) hx hstat hCi hdir
  have heul := ex_5_12c_euler h hv hstat hCi (by rw [hnext]; exact hx)
    (by rw [hnext]; exact henv) hDW
  refine ⟨?_, ?_⟩
  · have := hstat.2
    rw [← hvx] at this
    simp only [consObj, hz] at this
    exact this
  · simp only [one1, div_one] at heul
    rw [single_eq_cv] at heul
    field_simp at heul
    linarith

/-! ### Exercise 6.10c: additively separable preferences -/

/-- **Exercise 6.10c (`β = R`).** With `W(c, z) = U(c) + βz` and `β = R`, every wealth level is
stationary: consuming the interest `x(1 − R)` is optimal at every `x`. -/
theorem ex_6_10c_eq {U U' : ℝ → ℝ} (hW : ∀ C z, W C z = U (C 0) + β * z)
    (h : ConsHyp W one1 R β M) (hβR : β = R)
    (hconc : ConcaveOn ℝ ({C : Fin 1 → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    (hU : ∀ c, 0 ≤ c → HasDerivAt U (U' c) c) (hU' : ∀ c, 0 ≤ c → 0 ≤ U' c)
    {x : ℝ} (hx : 0 ≤ x) :
    cv (x * (1 - R)) ∈ argmax (consObj W one1 R v) (budgetΓ one1) ⟨x, hx⟩ := by
  have hβ1 := h.β_lt
  set c := x * (1 - R)
  have hc : 0 ≤ c := mul_nonneg hx (by linarith)
  set z := U c / (1 - β)
  set DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ := U' c • ((ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ)) + β • ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ
  have hDW : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW (cv c, z) := by
    have h1 : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => U (q.1 0))
        (U' c • ((ContinuousLinearMap.proj 0).comp
          (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ))) (cv c, z) := by
      have := (hU c hc).comp_hasFDerivAt (cv c, z)
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
          (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ)).hasFDerivAt)
      simpa [cv, Function.comp_def] using this
    have h2 : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => β * q.2)
        (β • ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ) (cv c, z) :=
      (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ).hasFDerivAt.const_mul β
    have e : (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) =
        (fun q : (Fin 1 → ℝ) × ℝ => U (q.1 0)) + fun q => β * q.2 := by
      funext q; simp [hW]
    rw [e]
    exact h1.add h2
  have hz : W (cv c) z = z := by
    have : (1 : ℝ) - β ≠ 0 := by linarith
    rw [hW]; simp only [cv, z]; field_simp; ring
  have hW2 : DW (0, 1) = R := by simp [DW, hβR]
  have hW1 : 0 ≤ DW (cv 1, 0) := by simp [DW, cv, hU' c hc]
  exact (ex_6_10a_if h (hβR ▸ hβ1) hconc hnn hv hx hz hDW hW2 hW1).1

/-- **Exercise 6.10c (`β ≠ R`).** With `W(c, z) = U(c) + βz`, `β ≠ R` and `U' ≠ 0`, no positive
wealth level is stationary. -/
theorem ex_6_10c_ne {U U' : ℝ → ℝ} (hW : ∀ C z, W C z = U (C 0) + β * z)
    (h : ConsHyp W one1 R β M) (hR1 : R < 1) (hβR : β ≠ R)
    (hconc : ConcaveOn ℝ ({C : Fin 1 → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    (hU : ∀ c, 0 ≤ c → HasDerivAt U (U' c) c) (hU' : ∀ c, 0 < c → U' c ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    cv (x * (1 - R)) ∉ argmax (consObj W one1 R v) (budgetΓ one1) ⟨x, hx.le⟩ := by
  intro hstat
  set c := x * (1 - R)
  have hc : 0 < c := mul_pos hx (by linarith)
  set DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ := U' c • ((ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ)) + β • ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ
  have hDW : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW (cv c, v ⟨x, hx.le⟩) := by
    have h1 : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => U (q.1 0))
        (U' c • ((ContinuousLinearMap.proj 0).comp
          (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ))) (cv c, v ⟨x, hx.le⟩) := by
      have := (hU c hc.le).comp_hasFDerivAt (cv c, v ⟨x, hx.le⟩)
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
          (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ)).hasFDerivAt)
      simpa [cv, Function.comp_def] using this
    have h2 : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => β * q.2)
        (β • ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ) (cv c, v ⟨x, hx.le⟩) :=
      (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ).hasFDerivAt.const_mul β
    have e : (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) =
        (fun q : (Fin 1 → ℝ) × ℝ => U (q.1 0)) + fun q => β * q.2 := by
      funext q; simp [hW]
    rw [e]
    exact h1.add h2
  have hW1 : DW (cv 1, 0) ≠ 0 := by simpa [DW, cv] using hU' c hc
  have := (ex_6_10a_only_if h hR1 hconc hnn hv hx hstat hDW hW1).2
  have hb : DW (0, 1) = β := by simp [DW]
  exact hβR (hb.symm.trans this)

/-- **Exercise 6.10d: the Euler equation.** Along an optimal path with positive consumption and
wealth, `W₁(c₀, z₁) = R⁻¹W₂(c₀, z₁)W₁(c₁, z₂)`. -/
theorem ex_6_10d (h : ConsHyp W one1 R β M)
    (hconc : ConcaveOn ℝ ({C : Fin 1 → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {A₀ A₁ : Wealth} {C₀ C₁ : Fin 1 → ℝ}
    (hC₀ : C₀ ∈ argmax (consObj W one1 R v) (budgetΓ one1) A₀) (hc₀ : 0 < C₀ 0)
    (hA₁ : A₁.1 = nextWealth one1 R A₀.1 C₀) (hA₁0 : 0 < A₁.1)
    (hC₁ : C₁ ∈ argmax (consObj W one1 R v) (budgetΓ one1) A₁) (hc₁ : 0 < C₁ 0)
    {DW₀ DW₁ : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ}
    (hDW₀ : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW₀
      (C₀, vext v (nextWealth one1 R A₀.1 C₀)))
    (hDW₁ : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW₁
      (C₁, vext v (nextWealth one1 R A₁.1 C₁))) :
    DW₀ (cv 1, 0) = DW₀ (0, 1) * DW₁ (cv 1, 0) / R := by
  have henv := ex_5_12c_envelope h hconc hnn hv hA₁0 hC₁ hc₁ (hasDerivAt_dir hDW₁)
  rw [hA₁] at henv hA₁0
  have heul := ex_5_12c_euler h hv hC₀ hc₀ hA₁0 henv hDW₀
  simp only [one1, div_one, single_eq_cv] at heul
  exact heul

end StokeyLucasPrescott.DeterministicDynamics
