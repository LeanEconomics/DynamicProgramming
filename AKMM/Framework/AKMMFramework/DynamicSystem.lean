/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscreteTime.GeneralSolow

/-!
# The dynamic system: accumulation, balanced paths and the detrended Solow map

AKMM, §2.1.5, pp. 52–57. Time is discrete, as in the book.

* **(2.4)** `k_{t+1} = (1 − δ)k_t + i_t`, rewritten with the output growth rate `γ_t` as
  `(k_{t+1}/y_{t+1})(1 + γ_t) = (1 − δ)k_t/y_t + i_t/y_t` (`eq_2_4_ratio_form`).
* **Balanced paths** (`DynBalancedPath`): if capital and output grow at a common constant rate
  `γ` and `i_t/y_t = s`, then `k_t/y_t = s/(γ + δ)` (`dyn_capital_output_ratio`); investment
  then grows at `γ` too. Conversely a capital stock starting at that ratio grows at `γ`
  (`dyn_balanced_of_initial_ratio`). A concrete balanced path is `dyn_balancedPath_example`.
* **Detrending.** With constant hours `ℓ`, labour-augmenting progress and constant returns,
  `k_{t+1} = sF(k_t, (1 + γ)^t ℓ) + (1 − δ)k_t` becomes
  `(1 + γ)k̃_{t+1} = sF(k̃_t, ℓ) + (1 − δ)k̃_t` for `k̃_t = k_t/(1 + γ)^t`
  (`dyn_detrend_step`), which is EconomicGrowth's discrete-time Solow map
  `Solow1956.DiscreteTime.next (F · ℓ) s δ (1 + γ)`; the whole path is that map's orbit scaled
  by `(1 + γ)^t` (`dyn_detrended_path`).
* **The constant solution** `k̄` of `(1 + γ)k̄ = sF(k̄, ℓ) + (1 − δ)k̄` exists and is the unique
  positive one (`dyn_steady_existsUnique`); it is EconomicGrowth's `steady`. From `k̃_0 = k̄`,
  capital, investment and output grow at `γ` and `y_t = (1 + γ)^t F(k̄, ℓ)`
  (`dyn_balanced_growth_from_steady`), and `k/y = s/(γ + δ)` there.
* **Convergence** (asserted on p. 56, proved in Ch. 3): from any `k_0 > 0`, `k̃_t → k̄`
  monotonically and `k_t/y_t → s/(γ + δ)` (`dyn_convergence`), from EconomicGrowth's
  `general_solow` (Acemoglu Proposition 2.5 in discrete time).

The neoclassical assumptions on `F(·, ℓ)` are EconomicGrowth's `Technology`, and the parameter
restrictions its `Params s δ (1 + γ)`: `s > 0`, `δ ≤ 1`, `γ > −1` and `γ + δ > 0`. Uzawa's theorem
(p. 56, proved in the book's Appendix 3.A) is not formalised here.
-/

namespace AKMM.Framework

open Filter Topology Solow1956.Neoclassical Solow1956.DiscreteTime

/-- AKMM, p. 53: the accumulation equation (2.4) divided by output. If
`k_{t+1} = (1 − δ)k_t + i_t` and output grows at the net rate `γ_t`, `y_{t+1} = (1 + γ_t)y_t`,
with `y_t, y_{t+1} ≠ 0`, then `(k_{t+1}/y_{t+1})(1 + γ_t) = (1 − δ)k_t/y_t + i_t/y_t`. -/
theorem eq_2_4_ratio_form {k i y : ℕ → ℝ} {δ γt : ℝ} {t : ℕ}
    (h24 : k (t + 1) = (1 - δ) * k t + i t) (hy : y (t + 1) = (1 + γt) * y t)
    (hy0 : y t ≠ 0) (hy1 : y (t + 1) ≠ 0) :
    k (t + 1) / y (t + 1) * (1 + γt) = (1 - δ) * (k t / y t) + i t / y t := by
  have h1 : 1 + γt = y (t + 1) / y t := by
    rw [hy]
    field_simp
  rw [h1, h24]
  field_simp

/-- AKMM, p. 53: a balanced path of (2.4). Capital accumulates by (2.4), capital and output
grow at the common net rate `γ`, investment is the constant fraction `s` of output, and output
is positive. -/
structure DynBalancedPath (δ γ s : ℝ) (k i y : ℕ → ℝ) : Prop where
  accumulation : ∀ t, k (t + 1) = (1 - δ) * k t + i t
  capital_growth : ∀ t, k (t + 1) = (1 + γ) * k t
  output_growth : ∀ t, y (t + 1) = (1 + γ) * y t
  saving : ∀ t, i t = s * y t
  output_pos : ∀ t, 0 < y t

/-- AKMM, p. 53: on a balanced path investment grows at the same rate `γ`. -/
theorem dyn_investment_growth {δ γ s : ℝ} {k i y : ℕ → ℝ} (hP : DynBalancedPath δ γ s k i y)
    (t : ℕ) : i (t + 1) = (1 + γ) * i t := by
  rw [hP.saving, hP.saving, hP.output_growth]
  ring

/-- AKMM, p. 53: on a balanced path of (2.4) the capital–output ratio is constant,
`k_t/y_t = s/(γ + δ)` (for `γ + δ ≠ 0`). -/
theorem dyn_capital_output_ratio {δ γ s : ℝ} {k i y : ℕ → ℝ} (hP : DynBalancedPath δ γ s k i y)
    (hγδ : γ + δ ≠ 0) (t : ℕ) : k t / y t = s / (γ + δ) := by
  have h := hP.accumulation t
  rw [hP.capital_growth, hP.saving] at h
  have hy := (hP.output_pos t).ne'
  rw [div_eq_div_iff hy hγδ]
  linarith

/-- AKMM, p. 53 ("this equation is consistent with a capital–output ratio that does not change
over time"): conversely, if output grows at `γ`, `i_t = s y_t`, capital follows (2.4) and
starts at `k_0/y_0 = s/(γ + δ)`, then capital also grows at `γ`: the path is balanced. -/
theorem dyn_balanced_of_initial_ratio {δ γ s : ℝ} {k i y : ℕ → ℝ}
    (h24 : ∀ t, k (t + 1) = (1 - δ) * k t + i t) (hy : ∀ t, y (t + 1) = (1 + γ) * y t)
    (hs : ∀ t, i t = s * y t) (hpos : ∀ t, 0 < y t) (hγδ : γ + δ ≠ 0)
    (h0 : k 0 = s / (γ + δ) * y 0) : DynBalancedPath δ γ s k i y := by
  have hk : ∀ t, k t = s / (γ + δ) * y t := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      rw [h24, ih, hs, hy]
      field_simp
      ring
  refine ⟨h24, fun t => ?_, hy, hs, hpos⟩
  rw [hk, hk, hy]
  ring

/-- A concrete balanced path (non-vacuity of `DynBalancedPath`): with `γ > −1` and
`γ + δ ≠ 0`, `y_t = (1 + γ)^t`, `i_t = s(1 + γ)^t`, `k_t = s/(γ + δ)·(1 + γ)^t`. -/
theorem dyn_balancedPath_example {δ γ s : ℝ} (hγ : -1 < γ) (hγδ : γ + δ ≠ 0) :
    DynBalancedPath δ γ s (fun t => s / (γ + δ) * (1 + γ) ^ t) (fun t => s * (1 + γ) ^ t)
      (fun t => (1 + γ) ^ t) := by
  refine dyn_balanced_of_initial_ratio (fun t => ?_) (fun t => ?_) (fun t => rfl)
    (fun t => pow_pos (by linarith) t) hγδ (by simp)
  · simp only [pow_succ]
    field_simp
    ring
  · simp only [pow_succ]
    ring

/-- AKMM, p. 56: detrending one step. If `F` has constant returns on the nonnegative quadrant,
`γ > −1`, `ℓ ≥ 0`, `k_t ≥ 0` and `k_{t+1} = sF(k_t, (1 + γ)^t ℓ) + (1 − δ)k_t`, then
`k̃_t = k_t/(1 + γ)^t` satisfies `(1 + γ)k̃_{t+1} = sF(k̃_t, ℓ) + (1 − δ)k̃_t`, i.e.
`k̃_{t+1} = next (F · ℓ) s δ (1 + γ) k̃_t` (EconomicGrowth's discrete Solow map). -/
theorem dyn_detrend_step {F : ℝ → ℝ → ℝ} {s δ γ ℓ : ℝ} {k : ℕ → ℝ} {t : ℕ}
    (hcrs : ∀ c a b, 0 < c → 0 ≤ a → 0 ≤ b → F (c * a) (c * b) = c * F a b)
    (hγ : -1 < γ) (hl : 0 ≤ ℓ) (hk : 0 ≤ k t)
    (hsys : k (t + 1) = s * F (k t) ((1 + γ) ^ t * ℓ) + (1 - δ) * k t) :
    (1 + γ) * (k (t + 1) / (1 + γ) ^ (t + 1)) =
        s * F (k t / (1 + γ) ^ t) ℓ + (1 - δ) * (k t / (1 + γ) ^ t) ∧
      k (t + 1) / (1 + γ) ^ (t + 1) = next (fun x => F x ℓ) s δ (1 + γ) (k t / (1 + γ) ^ t) := by
  have hg : 0 < 1 + γ := by linarith
  have hp : 0 < (1 + γ) ^ t := pow_pos hg t
  have hF : F (k t) ((1 + γ) ^ t * ℓ) = (1 + γ) ^ t * F (k t / (1 + γ) ^ t) ℓ := by
    rw [← hcrs _ _ _ hp (div_nonneg hk hp.le) hl]
    congr 1
    field_simp
  have h1 : (1 + γ) * (k (t + 1) / (1 + γ) ^ (t + 1)) =
      s * F (k t / (1 + γ) ^ t) ℓ + (1 - δ) * (k t / (1 + γ) ^ t) := by
    rw [hsys, hF, pow_succ]
    field_simp
  refine ⟨h1, ?_⟩
  unfold next
  rw [← h1]
  field_simp

/-- AKMM, p. 56: the book's steady-state equation `(1 + γ)k̄ = sF(k̄, ℓ) + (1 − δ)k̄` says that
`k̄` is a fixed point of EconomicGrowth's map `next (F · ℓ) s δ (1 + γ)`. -/
theorem dyn_steady_iff {F : ℝ → ℝ → ℝ} {s δ γ ℓ kbar : ℝ} (hγ : -1 < γ) :
    (1 + γ) * kbar = s * F kbar ℓ + (1 - δ) * kbar ↔
      next (fun x => F x ℓ) s δ (1 + γ) kbar = kbar := by
  have hg : (1 + γ) ≠ 0 := by linarith
  unfold next
  rw [div_eq_iff hg]
  constructor <;> intro h <;> linarith

/-- EconomicGrowth's discrete-time parameter restrictions for the detrended map:
`s > 0`, `δ ≤ 1`, `γ > −1` and `γ + δ > 0`. -/
theorem dyn_params {s δ γ : ℝ} (hs : 0 < s) (hδ : δ ≤ 1) (hγ : -1 < γ) (hγδ : 0 < γ + δ) :
    Params s δ (1 + γ) :=
  ⟨hs, hδ, by linarith, by linarith⟩

/-- AKMM, p. 56: there is a constant solution `k̄ > 0` of `(1 + γ)k̄ = sF(k̄, ℓ) + (1 − δ)k̄`,
and it is the unique positive one ("under some minimal conditions": `F(·, ℓ)` neoclassical,
`s > 0`, `δ ≤ 1`, `γ > −1`, `γ + δ > 0`). It is EconomicGrowth's `steady`. -/
theorem dyn_steady_existsUnique {F : ℝ → ℝ → ℝ} {s δ γ ℓ : ℝ}
    (h : Technology (fun x => F x ℓ)) (hs : 0 < s) (hδ : δ ≤ 1) (hγ : -1 < γ)
    (hγδ : 0 < γ + δ) :
    (∃! kbar : ℝ, 0 < kbar ∧ (1 + γ) * kbar = s * F kbar ℓ + (1 - δ) * kbar) ∧
      0 < steady h s δ (1 + γ) ∧
      (1 + γ) * steady h s δ (1 + γ) =
        s * F (steady h s δ (1 + γ)) ℓ + (1 - δ) * steady h s δ (1 + γ) := by
  have P := dyn_params hs hδ hγ hγδ
  obtain ⟨hpos, hfix⟩ := steady_spec h P
  refine ⟨?_, hpos, (dyn_steady_iff hγ).mpr hfix⟩
  simpa only [dyn_steady_iff hγ] using existsUnique_steadyState h P

/-- AKMM, p. 56: the detrended path. If `F` has constant returns on the nonnegative quadrant,
`F(·, ℓ)` is neoclassical, `ℓ ≥ 0`, `k_0 ≥ 0` and `k_{t+1} = sF(k_t, (1 + γ)^t ℓ) + (1 − δ)k_t`
for all `t`, then `k_t = (1 + γ)^t k̃_t`, where `k̃` is the orbit of EconomicGrowth's map
`next (F · ℓ) s δ (1 + γ)` from `k_0`. -/
theorem dyn_detrended_path {F : ℝ → ℝ → ℝ} {s δ γ ℓ : ℝ} {k : ℕ → ℝ}
    (h : Technology (fun x => F x ℓ))
    (hcrs : ∀ c a b, 0 < c → 0 ≤ a → 0 ≤ b → F (c * a) (c * b) = c * F a b)
    (hs : 0 < s) (hδ : δ ≤ 1) (hγ : -1 < γ) (hγδ : 0 < γ + δ) (hl : 0 ≤ ℓ) (hk0 : 0 ≤ k 0)
    (hsys : ∀ t, k (t + 1) = s * F (k t) ((1 + γ) ^ t * ℓ) + (1 - δ) * k t) (t : ℕ) :
    k t = (1 + γ) ^ t * path (fun x => F x ℓ) s δ (1 + γ) (k 0) t := by
  have P := dyn_params hs hδ hγ hγδ
  have hp : ∀ n : ℕ, 0 < (1 + γ) ^ n := fun n => pow_pos (by linarith) n
  induction t with
  | zero => simp [path_zero]
  | succ t ih =>
    have hkt : 0 ≤ k t := by
      rw [ih]
      exact mul_nonneg (hp t).le (path_nonneg h P hk0 t)
    have hstep := (dyn_detrend_step hcrs hγ hl hkt (hsys t)).2
    have hkt' : k t / (1 + γ) ^ t = path (fun x => F x ℓ) s δ (1 + γ) (k 0) t := by
      rw [ih]
      exact mul_div_cancel_left₀ _ (hp t).ne'
    rw [hkt', ← path_succ] at hstep
    rw [← hstep]
    exact (mul_div_cancel₀ _ (hp (t + 1)).ne').symm

/-- AKMM, p. 56: balanced growth from the constant solution. If `k_0 = k̄` (the steady state),
then `k_t = k̄(1 + γ)^t`, output `y_t = F(k_t, (1 + γ)^t ℓ) = (1 + γ)^t F(k̄, ℓ)` and investment
`i_t = s y_t` all grow at the net rate `γ`, and `k_t/y_t = s/(γ + δ)`. -/
theorem dyn_balanced_growth_from_steady {F : ℝ → ℝ → ℝ} {s δ γ ℓ : ℝ} {k : ℕ → ℝ}
    (h : Technology (fun x => F x ℓ))
    (hcrs : ∀ c a b, 0 < c → 0 ≤ a → 0 ≤ b → F (c * a) (c * b) = c * F a b)
    (hs : 0 < s) (hδ : δ ≤ 1) (hγ : -1 < γ) (hγδ : 0 < γ + δ) (hl : 0 ≤ ℓ)
    (hk0 : k 0 = steady h s δ (1 + γ))
    (hsys : ∀ t, k (t + 1) = s * F (k t) ((1 + γ) ^ t * ℓ) + (1 - δ) * k t) :
    (∀ t, k t = steady h s δ (1 + γ) * (1 + γ) ^ t) ∧
      (∀ t, F (k t) ((1 + γ) ^ t * ℓ) = (1 + γ) ^ t * F (steady h s δ (1 + γ)) ℓ) ∧
      DynBalancedPath δ γ s k (fun t => s * F (k t) ((1 + γ) ^ t * ℓ))
        (fun t => F (k t) ((1 + γ) ^ t * ℓ)) ∧
      ∀ t, k t / F (k t) ((1 + γ) ^ t * ℓ) = s / (γ + δ) := by
  have P := dyn_params hs hδ hγ hγδ
  obtain ⟨hpos, hfix⟩ := steady_spec h P
  set kb := steady h s δ (1 + γ) with hkb
  have hp : ∀ n : ℕ, 0 < (1 + γ) ^ n := fun n => pow_pos (by linarith) n
  have hpath : ∀ t, path (fun x => F x ℓ) s δ (1 + γ) kb t = kb := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [path_succ, ih, hfix]
  have hk : ∀ t, k t = kb * (1 + γ) ^ t := by
    intro t
    rw [dyn_detrended_path h hcrs hs hδ hγ hγδ hl (by rw [hk0]; exact hpos.le) hsys t, hk0,
      hpath]
    ring
  have hy : ∀ t, F (k t) ((1 + γ) ^ t * ℓ) = (1 + γ) ^ t * F kb ℓ := by
    intro t
    rw [hk, mul_comm kb, hcrs _ _ _ (hp t) hpos.le hl]
  have hFpos : 0 < F kb ℓ := h.output_pos hpos
  have hB : DynBalancedPath δ γ s k (fun t => s * F (k t) ((1 + γ) ^ t * ℓ))
      (fun t => F (k t) ((1 + γ) ^ t * ℓ)) := by
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => rfl, fun t => ?_⟩
    · rw [hsys t]
      ring
    · rw [hk, hk, pow_succ]
      ring
    · show F (k (t + 1)) ((1 + γ) ^ (t + 1) * ℓ) = (1 + γ) * F (k t) ((1 + γ) ^ t * ℓ)
      rw [hy, hy, pow_succ]
      ring
    · simp only [hy]
      exact mul_pos (hp t) hFpos
  exact ⟨hk, hy, hB, dyn_capital_output_ratio hB hγδ.ne'⟩

/-- AKMM, pp. 56–57: convergence (asserted in Ch. 2, proved in Ch. 3). Under the hypotheses of
`dyn_detrended_path` with `k_0 > 0`: the detrended stock `k̃_t = k_t/(1 + γ)^t` is positive,
moves monotonically toward `k̄` (increasing from below, decreasing from above), and converges
to `k̄`; and the capital–output ratio `k_t/y_t`, `y_t = F(k_t, (1 + γ)^t ℓ)`, converges to
`s/(γ + δ)`. Proved from EconomicGrowth's `general_solow` (Acemoglu Proposition 2.5). -/
theorem dyn_convergence {F : ℝ → ℝ → ℝ} {s δ γ ℓ : ℝ} {k : ℕ → ℝ}
    (h : Technology (fun x => F x ℓ))
    (hcrs : ∀ c a b, 0 < c → 0 ≤ a → 0 ≤ b → F (c * a) (c * b) = c * F a b)
    (hs : 0 < s) (hδ : δ ≤ 1) (hγ : -1 < γ) (hγδ : 0 < γ + δ) (hl : 0 ≤ ℓ) (hk0 : 0 < k 0)
    (hsys : ∀ t, k (t + 1) = s * F (k t) ((1 + γ) ^ t * ℓ) + (1 - δ) * k t) :
    (∀ t, 0 < k t / (1 + γ) ^ t) ∧
      (k 0 < steady h s δ (1 + γ) → StrictMono fun t => k t / (1 + γ) ^ t) ∧
      (steady h s δ (1 + γ) < k 0 → StrictAnti fun t => k t / (1 + γ) ^ t) ∧
      Tendsto (fun t => k t / (1 + γ) ^ t) atTop (𝓝 (steady h s δ (1 + γ))) ∧
      Tendsto (fun t => k t / F (k t) ((1 + γ) ^ t * ℓ)) atTop (𝓝 (s / (γ + δ))) := by
  have P := dyn_params hs hδ hγ hγδ
  have hp : ∀ n : ℕ, 0 < (1 + γ) ^ n := fun n => pow_pos (by linarith) n
  set f : ℝ → ℝ := fun x => F x ℓ with hf
  have hkt : ∀ t, k t / (1 + γ) ^ t = path f s δ (1 + γ) (k 0) t := by
    intro t
    rw [dyn_detrended_path h hcrs hs hδ hγ hγδ hl hk0.le hsys t]
    exact mul_div_cancel_left₀ _ (hp t).ne'
  have hI : IsPath f s δ (1 + γ) (path f s δ (1 + γ) (k 0)) := isPath_path hk0
  obtain ⟨hpos, hlow, hhigh, -, -, hlim⟩ := hI.orbit h P
  have hfun : (fun t => k t / (1 + γ) ^ t) = path f s δ (1 + γ) (k 0) := funext hkt
  -- the capital–output ratio is `k̃_t / F(k̃_t, ℓ)`
  have hratio : ∀ t, k t / F (k t) ((1 + γ) ^ t * ℓ) =
      path f s δ (1 + γ) (k 0) t / f (path f s δ (1 + γ) (k 0) t) := by
    intro t
    have hk : k t = (1 + γ) ^ t * path f s δ (1 + γ) (k 0) t :=
      dyn_detrended_path h hcrs hs hδ hγ hγδ hl hk0.le hsys t
    rw [hk, hcrs _ _ _ (hp t) (hpos t).le hl]
    exact mul_div_mul_left _ _ (hp t).ne'
  obtain ⟨hkpos, -, hsteady, -⟩ := steady_state_equilibrium h P
  have hFk : 0 < f (steady h s δ (1 + γ)) := h.output_pos hkpos
  have hlimF := (output_consumption_limit h P hI).1
  have hlimR := hlim.div hlimF hFk.ne'
  have hval : steady h s δ (1 + γ) / f (steady h s δ (1 + γ)) = s / (γ + δ) := by
    have : (1 + γ) - 1 + δ = γ + δ := by ring
    rw [this] at hsteady
    rw [div_eq_div_iff hFk.ne' hγδ.ne']
    linarith
  rw [hfun]
  refine ⟨fun t => by rw [hkt]; exact hpos t, fun h0 => (hlow h0).1, fun h0 => (hhigh h0).1,
    hlim, ?_⟩
  rw [funext hratio, ← hval]
  exact hlimR

end AKMM.Framework
