/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.CSExercises
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exercise 6.8: the deterministic CRRA consumption-saving problem

Copied from `EconomicDynamics/FiniteHorizonDP` (module `CSDeterministic`), namespace renamed.

Miao, Exercise 8, p. 190: maximize `Σ_{t=0}^T βᵗ c_t^{1−γ}/(1−γ)` subject to
`c_t + a_{t+1} = R a_t + y_t`, `a_0` given, `y_{t+1} = (1 + g) y_t`, with no borrowing constraint.
Without a terminal condition the problem is unbounded, so we impose the natural one,
`a_{T+1} ≥ 0` (at the optimum `a_{T+1} = 0`). `γ = 1` is log utility (`cs_crra`).

* `cs_budget`: the intertemporal budget constraint from any date `t`:
  `Σ_{k=0}^m c_{t+k}/R^k + a_{t+m+1}/R^m = R a_t + Σ_{k=0}^m y_{t+k}/R^k`.
* `cs_optimal_of_euler`: for any utility with tangent-line inequality (concavity), a feasible
  path satisfying the Euler equations `βᵗ u′(c_t) = λ/Rᵗ` (`λ ≥ 0`) and `a_{T+1} = 0` is optimal.
* `cs_crra_tangent`: the tangent-line inequality for CRRA utility, with `u′(c) = c^{−γ}`.
* **`ex_6_8`**: the explicit solution. With `θ = (βR)^{1/γ}` and total wealth
  `W_0 = R a_0 + y_0 Σ_{t=0}^T ((1+g)/R)ᵗ > 0`, consumption is `c_t = c_0 θᵗ` with
  `c_0 = W_0 / Σ_{t=0}^T (θ/R)ᵗ`; the path is feasible with `a_{T+1} = 0` and optimal; and the
  policy is consumption = (financial plus human wealth) / annuity factor:
  `c_t = (R a_t + y_t Σ_{k=0}^{T−t} ((1+g)/R)^k) / Σ_{k=0}^{T−t} (θ/R)^k`.
-/

namespace Miao.Applications

open Finset Real

/-- **The intertemporal budget constraint** (Miao, Exercise 8, p. 190): if
`c_{t+k} + a_{t+k+1} = R a_{t+k} + y_{t+k}` for `k ≤ m`, then
`Σ_{k=0}^m c_{t+k}/R^k + a_{t+m+1}/R^m = R a_t + Σ_{k=0}^m y_{t+k}/R^k`. -/
theorem cs_budget {R : ℝ} (hR : R ≠ 0) (c a y : ℕ → ℝ) (t : ℕ) :
    ∀ m, (∀ k ≤ m, c (t + k) + a (t + k + 1) = R * a (t + k) + y (t + k)) →
      ∑ k ∈ range (m + 1), c (t + k) / R ^ k + a (t + m + 1) / R ^ m =
        R * a t + ∑ k ∈ range (m + 1), y (t + k) / R ^ k := by
  intro m
  induction m with
  | zero =>
    intro h
    have := h 0 le_rfl
    simp only [zero_add, range_one, sum_singleton, pow_zero, div_one, add_zero] at this ⊢
    exact this
  | succ m ih =>
    intro h
    have ih' := ih fun k hk => h k (by omega)
    have hm := h (m + 1) le_rfl
    have e : t + (m + 1) = t + m + 1 := by omega
    rw [e] at hm
    rw [sum_range_succ (fun k => c (t + k) / R ^ k), sum_range_succ (fun k => y (t + k) / R ^ k), e]
    have hRm : R ^ (m + 1) = R ^ m * R := pow_succ R m
    have hRm0 : R ^ m ≠ 0 := pow_ne_zero m hR
    have key : R * a (t + m + 1) / R ^ (m + 1) = a (t + m + 1) / R ^ m := by
      rw [hRm]; field_simp
    have hm' : c (t + m + 1) / R ^ (m + 1) + a (t + m + 1 + 1) / R ^ (m + 1) =
        R * a (t + m + 1) / R ^ (m + 1) + y (t + m + 1) / R ^ (m + 1) := by
      rw [← add_div, ← add_div, hm]
    linarith

/-- **Sufficiency of the Euler equations** (Miao, Exercise 8): let `u(c′) ≤ u(c) + u′(c)(c′ − c)`
for `c, c′ > 0`. If `(c, a)` satisfies the budget constraints with `a_{T+1} = 0` and the Euler
equations `βᵗ u′(c_t) = λ / Rᵗ` with `λ ≥ 0`, then every feasible `(c′, a′)` (same `a_0`, positive
consumption, `a′_{T+1} ≥ 0`) has `Σ βᵗ u(c′_t) ≤ Σ βᵗ u(c_t)`. -/
theorem cs_optimal_of_euler {u du : ℝ → ℝ} {β R lam : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hlam : 0 ≤ lam) (htan : ∀ c c', 0 < c → 0 < c' → u c' ≤ u c + du c * (c' - c))
    {T : ℕ} {y c a c' a' : ℕ → ℝ} (ha : a 0 = a' 0)
    (hb : ∀ t ≤ T, c t + a (t + 1) = R * a t + y t)
    (hb' : ∀ t ≤ T, c' t + a' (t + 1) = R * a' t + y t) (hT : a (T + 1) = 0)
    (hT' : 0 ≤ a' (T + 1)) (hc : ∀ t ≤ T, 0 < c t) (hc' : ∀ t ≤ T, 0 < c' t)
    (heul : ∀ t ≤ T, β ^ t * du (c t) = lam / R ^ t) :
    ∑ t ∈ range (T + 1), β ^ t * u (c' t) ≤ ∑ t ∈ range (T + 1), β ^ t * u (c t) := by
  have B := cs_budget hR.ne' c a y 0 T fun k hk => by simpa using hb k hk
  have B' := cs_budget hR.ne' c' a' y 0 T fun k hk => by simpa using hb' k hk
  simp only [zero_add] at B B'
  rw [hT, zero_div, add_zero, ha] at B
  have hpv : ∑ t ∈ range (T + 1), (c' t - c t) / R ^ t ≤ 0 := by
    have : 0 ≤ a' (T + 1) / R ^ T := div_nonneg hT' (pow_pos hR T).le
    simp only [sub_div, sum_sub_distrib]
    linarith
  have hterm : ∀ t ∈ range (T + 1),
      β ^ t * u (c' t) ≤ β ^ t * u (c t) + lam * ((c' t - c t) / R ^ t) := by
    intro t ht
    have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have h1 := mul_le_mul_of_nonneg_left (htan (c t) (c' t) (hc t htT) (hc' t htT))
      (pow_pos hβ t).le
    have h2 : β ^ t * (du (c t) * (c' t - c t)) = lam * ((c' t - c t) / R ^ t) := by
      rw [← mul_assoc, heul t htT]
      ring
    linarith
  calc ∑ t ∈ range (T + 1), β ^ t * u (c' t)
      ≤ ∑ t ∈ range (T + 1), (β ^ t * u (c t) + lam * ((c' t - c t) / R ^ t)) :=
        sum_le_sum hterm
    _ = ∑ t ∈ range (T + 1), β ^ t * u (c t) +
          lam * ∑ t ∈ range (T + 1), (c' t - c t) / R ^ t := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ ∑ t ∈ range (T + 1), β ^ t * u (c t) := by
        have := mul_nonpos_of_nonneg_of_nonpos hlam hpv
        linarith

/-- **CRRA utility** `c^{1−γ}/(1−γ)`, with the logarithm at `γ = 1`. -/
noncomputable def cs_crra (γ c : ℝ) : ℝ := if γ = 1 then Real.log c else c ^ (1 - γ) / (1 - γ)

/-- The tangent-line inequality for CRRA utility: `u(c′) ≤ u(c) + c^{−γ}(c′ − c)` for
`c, c′ > 0`, `γ > 0` (Bernoulli's inequality; `log t ≤ t − 1` at `γ = 1`). -/
theorem cs_crra_tangent {γ : ℝ} (hγ : 0 < γ) {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    cs_crra γ c' ≤ cs_crra γ c + c ^ (-γ) * (c' - c) := by
  set t := c' / c with htdef
  have ht : 0 < t := div_pos hc' hc
  have hc't : c' = c * t := by rw [htdef]; field_simp
  have hcinv : c ^ (-γ) = c ^ (1 - γ) / c := by
    rw [rpow_sub hc, rpow_one, rpow_neg hc.le]
    have : c ^ γ ≠ 0 := (rpow_pos_of_pos hc γ).ne'
    field_simp
  unfold cs_crra
  split_ifs with h1
  · subst h1
    rw [hc't, Real.log_mul hc.ne' ht.ne', rpow_neg_one]
    have := Real.log_le_sub_one_of_pos ht
    have e : c⁻¹ * (c * t - c) = t - 1 := by field_simp
    rw [e]
    linarith
  · have hp : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have hcp : 0 < c ^ (1 - γ) := rpow_pos_of_pos hc _
    rw [hc't, mul_rpow hc.le ht.le, hcinv]
    have e : c ^ (1 - γ) / c * (c * t - c) = c ^ (1 - γ) * (t - 1) := by field_simp
    rw [e]
    -- reduce to `t^p/p ≤ 1/p + (t − 1)`
    suffices hs : t ^ (1 - γ) / (1 - γ) ≤ 1 / (1 - γ) + (t - 1) by
      have := mul_le_mul_of_nonneg_left hs hcp.le
      have e2 : c ^ (1 - γ) * (t ^ (1 - γ) / (1 - γ)) = c ^ (1 - γ) * t ^ (1 - γ) / (1 - γ) := by
        ring
      have e3 : c ^ (1 - γ) * (1 / (1 - γ) + (t - 1)) =
          c ^ (1 - γ) / (1 - γ) + c ^ (1 - γ) * (t - 1) := by ring
      linarith
    rcases lt_or_gt_of_ne hp with hneg | hpos
    · -- `γ > 1`: `t^p ≥ 1 + p(t − 1)`
      have h1 : 1 + (1 - γ) * Real.log t ≤ t ^ (1 - γ) := by
        rw [rpow_def_of_pos ht, mul_comm]
        linarith [Real.add_one_le_exp (Real.log t * (1 - γ))]
      have h2 : (1 - γ) * (t - 1) ≤ (1 - γ) * Real.log t :=
        mul_le_mul_of_nonpos_left (Real.log_le_sub_one_of_pos ht) hneg.le
      rw [div_le_iff_of_neg hneg]
      have : (1 / (1 - γ) + (t - 1)) * (1 - γ) = 1 + (1 - γ) * (t - 1) := by field_simp
      rw [this]
      linarith
    · -- `0 < γ < 1`: Bernoulli `t^p ≤ 1 + p(t − 1)`
      have hb := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hpos.le
        (by linarith)
      rw [add_sub_cancel] at hb
      rw [div_le_iff₀ hpos]
      have : (1 / (1 - γ) + (t - 1)) * (1 - γ) = 1 + (1 - γ) * (t - 1) := by field_simp
      rw [this]
      linarith

/-- The growth factor of consumption, `θ = (βR)^{1/γ}`. -/
noncomputable def cs_theta (β R γ : ℝ) : ℝ := (β * R) ^ (1 / γ)

/-- Total wealth at date 0: `W_0 = R a_0 + y_0 Σ_{t=0}^T ((1+g)/R)ᵗ`. -/
noncomputable def cs_wealth (R g a₀ y₀ : ℝ) (T : ℕ) : ℝ :=
  R * a₀ + y₀ * ∑ t ∈ range (T + 1), ((1 + g) / R) ^ t

/-- The optimal consumption path `c_t = c_0 θᵗ`, `c_0 = W_0 / Σ_{t=0}^T (θ/R)ᵗ`. -/
noncomputable def cs_cstar (β R γ g a₀ y₀ : ℝ) (T t : ℕ) : ℝ :=
  cs_wealth R g a₀ y₀ T / (∑ k ∈ range (T + 1), (cs_theta β R γ / R) ^ k) *
    cs_theta β R γ ^ t

/-- The asset path generated by `cs_cstar` from `a_0` and income `y_t = (1+g)ᵗ y_0`. -/
noncomputable def cs_astar (β R γ g a₀ y₀ : ℝ) (T : ℕ) : ℕ → ℝ
  | 0 => a₀
  | t + 1 => R * cs_astar β R γ g a₀ y₀ T t + (1 + g) ^ t * y₀ - cs_cstar β R γ g a₀ y₀ T t

/-- **Exercise 6.8** (Miao, p. 190): the explicit solution of the deterministic CRRA problem
with growing income `y_t = (1+g)ᵗ y_0` and the terminal condition `a_{T+1} ≥ 0`. Let
`θ = (βR)^{1/γ}`, `W_0 = R a_0 + y_0 Σ_{t=0}^T ((1+g)/R)ᵗ > 0` and
`c_t = c_0 θᵗ`, `c_0 = W_0 / Σ_{t=0}^T (θ/R)ᵗ` (`γ = 1` is log utility, `θ = βR`). Then
* the path is feasible: `c_t > 0`, the budget constraints hold and `a_{T+1} = 0`;
* the Euler equation `c_{t+1} = θ c_t` holds;
* it is optimal among all feasible paths;
* the policy: `c_t Σ_{k=0}^{T−t} (θ/R)^k = R a_t + y_t Σ_{k=0}^{T−t} ((1+g)/R)^k`, i.e. consumption
  is financial plus human wealth divided by the annuity factor. -/
theorem ex_6_8 {β R γ g a₀ y₀ : ℝ} (hβ : 0 < β) (hR : 0 < R) (hγ : 0 < γ) (T : ℕ)
    (hW : 0 < cs_wealth R g a₀ y₀ T) :
    (∀ t ≤ T, 0 < cs_cstar β R γ g a₀ y₀ T t) ∧
      (∀ t ≤ T, cs_cstar β R γ g a₀ y₀ T t + cs_astar β R γ g a₀ y₀ T (t + 1) =
        R * cs_astar β R γ g a₀ y₀ T t + (1 + g) ^ t * y₀) ∧
      cs_astar β R γ g a₀ y₀ T (T + 1) = 0 ∧
      (∀ t, cs_cstar β R γ g a₀ y₀ T (t + 1) = cs_theta β R γ * cs_cstar β R γ g a₀ y₀ T t) ∧
      (∀ c a : ℕ → ℝ, a 0 = a₀ → (∀ t ≤ T, c t + a (t + 1) = R * a t + (1 + g) ^ t * y₀) →
        0 ≤ a (T + 1) → (∀ t ≤ T, 0 < c t) →
        ∑ t ∈ range (T + 1), β ^ t * cs_crra γ (c t) ≤
          ∑ t ∈ range (T + 1), β ^ t * cs_crra γ (cs_cstar β R γ g a₀ y₀ T t)) ∧
      ∀ t ≤ T, cs_cstar β R γ g a₀ y₀ T t * ∑ k ∈ range (T - t + 1), (cs_theta β R γ / R) ^ k =
        R * cs_astar β R γ g a₀ y₀ T t +
          (1 + g) ^ t * y₀ * ∑ k ∈ range (T - t + 1), ((1 + g) / R) ^ k := by
  set θ := cs_theta β R γ with hθdef
  have hθ : 0 < θ := rpow_pos_of_pos (mul_pos hβ hR) _
  set A := ∑ k ∈ range (T + 1), (θ / R) ^ k with hAdef
  have hA : 0 < A := sum_pos (fun k _ => pow_pos (div_pos hθ hR) k) nonempty_range_add_one
  set W := cs_wealth R g a₀ y₀ T with hWdef
  set c₀ := W / A with hc₀def
  have hc₀ : 0 < c₀ := div_pos hW hA
  have hcs : ∀ t, cs_cstar β R γ g a₀ y₀ T t = c₀ * θ ^ t := fun t => rfl
  set y : ℕ → ℝ := fun t => (1 + g) ^ t * y₀ with hydef
  have hbud : ∀ t, cs_cstar β R γ g a₀ y₀ T t + cs_astar β R γ g a₀ y₀ T (t + 1) =
      R * cs_astar β R γ g a₀ y₀ T t + y t := fun t => by
    rw [cs_astar]; ring
  have hpos : ∀ t, 0 < cs_cstar β R γ g a₀ y₀ T t := fun t => by
    rw [hcs]; exact mul_pos hc₀ (pow_pos hθ t)
  have hshift : ∀ t k, cs_cstar β R γ g a₀ y₀ T (t + k) / R ^ k =
      cs_cstar β R γ g a₀ y₀ T t * (θ / R) ^ k := fun t k => by
    rw [hcs, hcs, div_pow, pow_add]; ring
  have hyshift : ∀ t k, y (t + k) / R ^ k = y t * ((1 + g) / R) ^ k := fun t k => by
    simp only [hydef, div_pow, pow_add]; ring
  -- the terminal condition from the budget constraint
  have hT : cs_astar β R γ g a₀ y₀ T (T + 1) = 0 := by
    have B := cs_budget hR.ne' (cs_cstar β R γ g a₀ y₀ T) (cs_astar β R γ g a₀ y₀ T) y 0 T
      fun k _ => hbud (0 + k)
    simp only [zero_add] at B
    have h1 : ∑ k ∈ range (T + 1), cs_cstar β R γ g a₀ y₀ T k / R ^ k = W := by
      have := fun k => hshift 0 k
      simp only [zero_add] at this
      simp only [this, ← mul_sum]
      rw [← hAdef, hcs, pow_zero, mul_one, hc₀def, div_mul_cancel₀ _ hA.ne']
    have h2 : ∑ k ∈ range (T + 1), y k / R ^ k = y₀ * ∑ k ∈ range (T + 1), ((1 + g) / R) ^ k := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      simp only [hydef, div_pow]
      ring
    rw [h1, h2] at B
    have h3 : cs_astar β R γ g a₀ y₀ T 0 = a₀ := rfl
    rw [h3] at B
    have h4 : cs_astar β R γ g a₀ y₀ T (T + 1) / R ^ T = 0 := by
      simp only [hWdef, cs_wealth] at B; linarith
    rcases div_eq_zero_iff.1 h4 with h | h
    · exact h
    · exact absurd h (pow_ne_zero T hR.ne')
  refine ⟨fun t _ => hpos t, fun t _ => hbud t, hT, fun t => ?_, ?_, fun t ht => ?_⟩
  · rw [hcs, hcs, pow_succ]; ring
  · intro c a ha hb hb' hc
    refine cs_optimal_of_euler (u := cs_crra γ) (du := fun c => c ^ (-γ)) (lam := c₀ ^ (-γ))
      (y := y) hβ hR (rpow_nonneg hc₀.le _) (fun c c' hc hc' => cs_crra_tangent hγ hc hc')
      (a := cs_astar β R γ g a₀ y₀ T) (a' := a) ha.symm (fun t _ => hbud t) hb hT hb'
      (fun t _ => hpos t) hc fun t _ => ?_
    have hθγ : θ ^ (-γ) = (β * R)⁻¹ := by
      rw [hθdef, cs_theta, ← rpow_mul (mul_pos hβ hR).le]
      have : 1 / γ * -γ = -1 := by field_simp
      rw [this, rpow_neg_one]
    change β ^ t * (cs_cstar β R γ g a₀ y₀ T t) ^ (-γ) = c₀ ^ (-γ) / R ^ t
    rw [hcs, mul_rpow hc₀.le (pow_pos hθ t).le, ← rpow_natCast θ t, ← rpow_mul hθ.le,
      mul_comm (t : ℝ) (-γ), rpow_mul hθ.le, rpow_natCast, hθγ, inv_pow, mul_pow]
    have := pow_pos hβ t
    have := pow_pos hR t
    field_simp
  · have B := cs_budget hR.ne' (cs_cstar β R γ g a₀ y₀ T) (cs_astar β R γ g a₀ y₀ T) y t (T - t)
      fun k _ => hbud (t + k)
    have e : t + (T - t) + 1 = T + 1 := by omega
    rw [e, hT, zero_div, add_zero] at B
    simp only [hshift, hyshift, ← mul_sum] at B
    rw [B]

end Miao.Applications
