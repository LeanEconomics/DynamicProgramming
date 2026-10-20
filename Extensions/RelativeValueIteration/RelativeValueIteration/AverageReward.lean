/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.RelativeVI

/-!
# Average reward: White's relative value iteration

White (1963); Puterman (2005).

With `β = 1` value iteration diverges (values grow like `n·g`), but relative value iteration
still converges when the Dobrushin coefficient is below one.

* `white`: if `α < 1`, the relative iterates `V_n = rel(TⁿV₀)` converge to some `h` with
  `h(s₀) = 0` and `Th = h + g` — the **average-reward optimality equation**, with gain `g`.
* `avg_upper`, `avg_greedy`, `avg_tendsto`: every feasible policy earns at most `n·g + 2‖h‖` over
  `n` periods, and a policy greedy for `h` earns within `2‖h‖` of `n·g`; so `g` is the optimal
  long-run average reward and the greedy policy attains it.
* `gain_unique`: every solution of the optimality equation has the same gain.
-/

open Finset Filter Topology

namespace DPExtensions.RelativeValueIteration

namespace MDP

variable {S A : Type*} [Fintype S] (M : MDP S A)

theorem Tσ_iterate_add_const (hβ : M.β = 1) (σ : S → A) (v : S → ℝ) (c : ℝ) (n : ℕ) :
    (M.Tσ σ)^[n] (fun t => v t + c) = fun s => (M.Tσ σ)^[n] v s + c := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Tσ_add_const, hβ, one_mul, ih]

theorem T_iterate_of_poisson (hβ : M.β = 1) {h : S → ℝ} {g : ℝ} (hpe : ∀ s, M.T h s = h s + g)
    (n : ℕ) (s : S) : M.T^[n] h s = h s + n * g := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have e2 : M.T^[n] h = fun t => h t + n * g := funext ih
    rw [e2, T_add_const, hβ, one_mul]
    change M.T h s + n * g = _
    rw [hpe]
    push_cast
    ring

theorem Tσ_iterate_le_T_iterate {σ : S → A} (hσ : M.IsPolicy σ) (v : S → ℝ) (n : ℕ) :
    (M.Tσ σ)^[n] v ≤ M.T^[n] v := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (M.Tσ_mono σ ih).trans (M.Tσ_le_T hσ _)

theorem norm_bound (h : S → ℝ) (s : S) : -‖h‖ ≤ h s ∧ h s ≤ ‖h‖ := by
  have := norm_le_pi_norm h s
  rw [Real.norm_eq_abs] at this
  exact abs_le.1 this

/-- **No policy beats the gain**: over `n` periods every feasible policy earns at most
`n·g + 2‖h‖` from every state. -/
theorem avg_upper (hβ : M.β = 1) {h : S → ℝ} {g : ℝ} (hpe : ∀ s, M.T h s = h s + g)
    {σ : S → A} (hσ : M.IsPolicy σ) (n : ℕ) (s : S) :
    (M.Tσ σ)^[n] 0 s ≤ n * g + 2 * ‖h‖ := by
  have h0 : (0 : S → ℝ) ≤ fun t => h t + ‖h‖ := fun t => by
    have := (norm_bound h t).1
    change (0 : ℝ) ≤ h t + ‖h‖
    linarith
  have h1 := (Monotone.iterate (M.Tσ_mono σ) n) h0 s
  rw [M.Tσ_iterate_add_const hβ] at h1
  have h2 := M.Tσ_iterate_le_T_iterate hσ h n s
  rw [M.T_iterate_of_poisson hβ hpe] at h2
  have h3 := (norm_bound h s).2
  simp only at h1
  linarith

/-- **The greedy policy attains the gain**: a policy greedy for `h` earns within `2‖h‖` of `n·g`
over `n` periods. -/
theorem avg_greedy (hβ : M.β = 1) {h : S → ℝ} {g : ℝ} (hpe : ∀ s, M.T h s = h s + g)
    {σ : S → A} (hσ : M.IsGreedy σ h) (n : ℕ) (s : S) :
    |(M.Tσ σ)^[n] 0 s - n * g| ≤ 2 * ‖h‖ := by
  have hpol : M.IsPolicy σ := fun s => (hσ s).1
  have hexact : ∀ n, ∀ s, (M.Tσ σ)^[n] h s = h s + n * g := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply']
      have e : (M.Tσ σ)^[n] h = fun t => h t + n * g := funext ih
      rw [e, Tσ_add_const, hβ, one_mul, M.Tσ_eq_T_of_greedy hσ]
      change M.T h s + n * g = _
      rw [hpe]
      push_cast
      ring
  have hle : (fun t => h t + -‖h‖) ≤ (0 : S → ℝ) := fun t => by
    have := (norm_bound h t).2
    change h t + -‖h‖ ≤ 0
    linarith
  have h1 := (Monotone.iterate (M.Tσ_mono σ) n) hle s
  rw [M.Tσ_iterate_add_const hβ] at h1
  simp only at h1
  rw [hexact n s] at h1
  have h2 := M.avg_upper hβ hpe hpol n s
  have h3 := (norm_bound h s).1
  rw [abs_le]
  constructor <;> linarith

/-- The greedy policy's average reward converges to the gain. -/
theorem avg_tendsto (hβ : M.β = 1) {h : S → ℝ} {g : ℝ} (hpe : ∀ s, M.T h s = h s + g)
    {σ : S → A} (hσ : M.IsGreedy σ h) (s : S) :
    Tendsto (fun n : ℕ => (M.Tσ σ)^[n] 0 s / n) atTop (𝓝 g) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => 2 * ‖h‖ / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => dist_nonneg) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [Real.dist_eq, le_div_iff₀ hn']
  have e : ((M.Tσ σ)^[n] 0 s / n - g) * n = (M.Tσ σ)^[n] 0 s - n * g := by
    field_simp
  calc |(M.Tσ σ)^[n] 0 s / n - g| * n = |((M.Tσ σ)^[n] 0 s / n - g) * n| := by
        rw [abs_mul, abs_of_pos hn']
    _ = |(M.Tσ σ)^[n] 0 s - n * g| := by rw [e]
    _ ≤ 2 * ‖h‖ := M.avg_greedy hβ hpe hσ n s

variable [Nonempty S]

/-- **The gain is unique**: all solutions of the average-reward optimality equation share it. -/
theorem gain_unique (hβ : M.β = 1) {h h' : S → ℝ} {g g' : ℝ} (hpe : ∀ s, M.T h s = h s + g)
    (hpe' : ∀ s, M.T h' s = h' s + g') : g = g' := by
  have key : ∀ {h h' : S → ℝ} {g g' : ℝ}, (∀ s, M.T h s = h s + g) →
      (∀ s, M.T h' s = h' s + g') → g ≤ g' := by
    intro h h' g g' hpe hpe'
    obtain ⟨σ, hσ⟩ := M.exists_greedy h
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := exists_nat_gt ((2 * ‖h‖ + 2 * ‖h'‖) / (g - g'))
    set s := Classical.arbitrary S
    have h1 := abs_le.1 (M.avg_greedy hβ hpe hσ n s)
    have h2 := M.avg_upper hβ hpe' (fun s => (hσ s).1) n s
    rw [div_lt_iff₀ (sub_pos.2 hlt)] at hn
    nlinarith
  exact le_antisymm (key hpe hpe') (key hpe' hpe)

/-- **White's theorem**: with `β = 1` and Dobrushin coefficient `α < 1`, relative value iteration
converges to a solution `h` of the average-reward optimality equation `Th = h + g`, normalized by
`h(s₀) = 0`. -/
theorem white (hβ : M.β = 1) {α : ℝ} (hα1 : α < 1)
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (s₀ : S) (V₀ : S → ℝ) :
    ∃ h : S → ℝ, ∃ g : ℝ, (∀ s, M.T h s = h s + g) ∧ h s₀ = 0 ∧
      Tendsto (M.relIter s₀ V₀) atTop (𝓝 h) := by
  set u := M.relIter s₀ V₀
  set C := sp (fun s => M.T V₀ s - V₀ s)
  have hstep : ∀ n, dist (u n) (u (n + 1)) ≤ C * α ^ n := fun n => by
    rw [dist_comm, dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (sp_nonneg _)
      (pow_nonneg (M.alpha_nonneg hα) n))).2 fun s => ?_
    have h1 := M.sp_relIter_succ_sub_le hα s₀ V₀ n
    rw [hβ, one_mul] at h1
    have h2 := abs_sub_le_sp (fun s => u (n + 1) s - u n s) s s₀
    have h3 : u (n + 1) s₀ - u n s₀ = 0 := by simp [u, relIter, rel]
    rw [Pi.sub_apply, Real.norm_eq_abs]
    simp only [h3, sub_zero] at h2
    linarith [mul_comm C (α ^ n)]
  obtain ⟨h, hh⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric α C hα1 hstep)
  have hTc : Continuous M.T := (LipschitzWith.of_dist_le_mul (K := 1) fun v w => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact (M.norm_T_sub_le v w).trans (mul_le_of_le_one_left (norm_nonneg _) M.β_le_one)
    ).continuous
  have hrel : Continuous (rel s₀ : (S → ℝ) → S → ℝ) := by
    unfold rel
    fun_prop
  have hF : Tendsto (fun n => u (n + 1)) atTop (𝓝 (rel s₀ (M.T h))) := by
    have : (fun n => u (n + 1)) = fun n => rel s₀ (M.T (u n)) :=
      funext fun n => M.relIter_succ s₀ V₀ n
    rw [this]
    exact ((hrel.comp hTc).tendsto h).comp hh
  have hfix : h = rel s₀ (M.T h) := tendsto_nhds_unique (hh.comp (tendsto_add_atTop_nat 1)) hF
  refine ⟨h, M.T h s₀, fun s => ?_, ?_, hh⟩
  · have := congrFun hfix s
    simp only [rel] at this
    linarith
  · have := congrFun hfix s₀
    simpa [rel] using this

end MDP

end DPExtensions.RelativeValueIteration
