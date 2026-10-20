/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.Subradius

/-!
# Asymptotic rates: relative value iteration converges at rate `βλ(Q*)`

Morton (1971); Morton and Wecker (1977); Bray (2019a), Propositions 3 and 5.

Let `P_σ` be the transition matrix of a decision rule and `λ(P_σ)` its subradius (the
second-largest eigenvalue modulus, `spectralRadius_deltaQ`).

* `sp_policy_eval_le` (**Morton; Bray, Prop 5**): policy evaluation `T_σⁿv → v_σ` converges in
  span at rate `βγ` for every `γ > λ(P_σ)`: `sp(T_σⁿv − v_σ) ≤ C(βγ)ⁿ sp(v − v_σ)`.
* `eventually_T_eq_Tσ`: if the optimal decision rule `σ*` is unique and strict, the greedy policy
  freezes: after finitely many steps value iteration is `T_{σ*}`-iteration.
* `relative_asymptotic_rate` (**Morton–Wecker; Bray, Prop 3**): then for every `γ > λ(P_{σ*})`
  there are `C` and `N` with `sp(T^{N+k}v − v*) ≤ C(βγ)ᵏ`, so the relative values converge at
  rate `βλ(P_{σ*})` (`rel_asymptotic_rate`).
* `level_rate_lower` (**standard value iteration is no faster than `β`**): if `ψ` is a stationary
  distribution of `P_{σ*}`, `‖T^{N+k}v − v*‖ ≥ βᵏ|ψ·(T^Nv − v*)|`.
* `subradius_policy_le`: `λ(P_σ)` is at most any Dobrushin bound `α`, so the asymptotic rate is
  never worse than the non-asymptotic rate `βα` of `sp_iterate_sub_vstar`.
-/

open Filter Topology Matrix Finset

namespace DPExtensions.RelativeValueIteration

theorem sp_mul_le {S : Type*} [Fintype S] [Nonempty S] {c : ℝ} (hc : 0 ≤ c) (w : S → ℝ) :
    sp (fun s => c * w s) ≤ c * sp w :=
  sp_le fun x y => by
    have := mul_le_mul_of_nonneg_left (sub_le_sp w x y) hc
    linarith [mul_sub c (w x) (w y)]

namespace MDP

variable {S A : Type*} [Fintype S] [DecidableEq S] (M : MDP S A)

/-- The transition matrix of the decision rule `σ`. -/
def Pmat (σ : S → A) : Matrix S S ℝ := fun s t => M.P s (σ s) t

omit [DecidableEq S] in
theorem Pmat_isStochastic (σ : S → A) : IsStochastic (M.Pmat σ) :=
  ⟨fun s t => M.P_nonneg s (σ s) t, fun s => M.P_sum s (σ s)⟩

omit [DecidableEq S] in
theorem Tσ_sub (σ : S → A) (v w : S → ℝ) :
    (fun s => M.Tσ σ v s - M.Tσ σ w s) = fun s => M.β * (M.Pmat σ *ᵥ (v - w)) s := by
  funext s
  simp only [Tσ, M.Q_sub_Q, Pmat, mulVec, dotProduct, Pi.sub_apply]

theorem Tσ_iterate_sub (σ : S → A) (v w : S → ℝ) (n : ℕ) :
    (fun s => (M.Tσ σ)^[n] v s - (M.Tσ σ)^[n] w s) =
      fun s => M.β ^ n * (M.Pmat σ ^ n *ᵥ (v - w)) s := by
  induction n with
  | zero => funext s; simp
  | succ n ih =>
    funext s
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h := congrFun (M.Tσ_sub σ ((M.Tσ σ)^[n] v) ((M.Tσ σ)^[n] w)) s
    rw [h]
    have e : (M.Tσ σ)^[n] v - (M.Tσ σ)^[n] w = M.β ^ n • (M.Pmat σ ^ n *ᵥ (v - w)) := by
      funext t
      exact congrFun ih t
    rw [e, mulVec_smul, mulVec_mulVec, ← pow_succ']
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- **Policy evaluation converges at rate `βλ(P_σ)`** (Morton, 1971; Bray, Prop 5). -/
theorem sp_policy_eval_le [Nonempty S] (hβ : M.β < 1) (σ : S → A) (s₀ : S) {γ : ℝ}
    (hγ : subradius (M.Pmat σ) s₀ < γ) :
    ∃ C, 0 ≤ C ∧ ∀ (n : ℕ) (v : S → ℝ),
      sp (fun s => (M.Tσ σ)^[n] v s - M.vσ hβ σ s) ≤
        C * (M.β * γ) ^ n * sp (fun s => v s - M.vσ hβ σ s) := by
  obtain ⟨C, hC0, hC⟩ := sp_pow_mulVec_le (M.Pmat_isStochastic σ) s₀ hγ
  refine ⟨C, hC0, fun n v => ?_⟩
  have hfix : (M.Tσ σ)^[n] (M.vσ hβ σ) = M.vσ hβ σ := Function.iterate_fixed (M.Tσ_vσ hβ σ) n
  have e := M.Tσ_iterate_sub σ v (M.vσ hβ σ) n
  rw [hfix] at e
  rw [e]
  calc sp (fun s => M.β ^ n * (M.Pmat σ ^ n *ᵥ (v - M.vσ hβ σ)) s)
      ≤ M.β ^ n * sp (M.Pmat σ ^ n *ᵥ (v - M.vσ hβ σ)) :=
        sp_mul_le (pow_nonneg M.β_nonneg n) _
    _ ≤ M.β ^ n * (C * γ ^ n * sp (v - M.vσ hβ σ)) :=
        mul_le_mul_of_nonneg_left (hC n _) (pow_nonneg M.β_nonneg n)
    _ = C * (M.β * γ) ^ n * sp (fun s => v s - M.vσ hβ σ s) := by
        rw [mul_pow]
        change _ = C * (M.β ^ n * γ ^ n) * sp (v - M.vσ hβ σ)
        ring

omit [DecidableEq S] in
/-- **The greedy policy freezes** at a unique, strict optimal decision rule `σ*`: near `v*`,
`T = T_{σ*}`. -/
theorem eventually_T_eq_Tσ (hβ : M.β < 1) {σs : S → A}
    (hstrict : ∀ s, σs s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, a ≠ σs s →
      M.Q (M.vstar hβ) s a < M.Q (M.vstar hβ) s (σs s)) :
    ∃ ρ > 0, ∀ w : S → ℝ, ‖w - M.vstar hβ‖ < ρ → M.T w = M.Tσ σs w := by
  classical
  set vs := M.vstar hβ
  set G : Finset (S × A) := univ.biUnion fun s => ((M.Γ s).filter fun a => a ≠ σs s).image
    fun a => (s, a)
  have hG : ∀ s, ∀ a ∈ M.Γ s, a ≠ σs s → (s, a) ∈ G := fun s a ha hne => by
    simp only [G, mem_biUnion, mem_univ, true_and, mem_image, mem_filter]
    exact ⟨s, a, ⟨ha, hne⟩, rfl⟩
  have hGgap : ∀ p ∈ G, 0 < M.Q vs p.1 (σs p.1) - M.Q vs p.1 p.2 := fun p hp => by
    simp only [G, mem_biUnion, mem_univ, true_and, mem_image, mem_filter] at hp
    obtain ⟨s, a, ⟨ha, hne⟩, rfl⟩ := hp
    exact sub_pos.2 ((hstrict s).2 a ha hne)
  obtain ⟨g, hg, hgap⟩ : ∃ g > 0, ∀ p ∈ G, g ≤ M.Q vs p.1 (σs p.1) - M.Q vs p.1 p.2 := by
    rcases G.eq_empty_or_nonempty with hE | hne
    · exact ⟨1, one_pos, fun p hp => by rw [hE] at hp; exact absurd hp (notMem_empty p)⟩
    · obtain ⟨p0, hp0, hmin⟩ := exists_min_image G
        (fun p => M.Q vs p.1 (σs p.1) - M.Q vs p.1 p.2) hne
      exact ⟨_, hGgap p0 hp0, hmin⟩
  have hβ0 := M.β_nonneg
  refine ⟨g / (2 * M.β + 1), div_pos hg (by linarith), fun w hw => ?_⟩
  have h2β : 2 * M.β * ‖w - vs‖ < g := by
    rw [lt_div_iff₀ (by linarith)] at hw
    nlinarith [norm_nonneg (w - vs)]
  funext s
  refine le_antisymm (sup'_le _ _ fun a ha => ?_) (M.Q_le_T w (hstrict s).1)
  by_cases hne : a = σs s
  · rw [hne]
    rfl
  · have h1 := abs_le.1 (M.abs_Q_sub_le w vs s a)
    have h2 := abs_le.1 (M.abs_Q_sub_le w vs s (σs s))
    have h3 := hgap (s, a) (hG s a ha hne)
    simp only at h3
    change M.Q w s a ≤ M.Q w s (σs s)
    linarith

omit [DecidableEq S] in
theorem norm_iterate_sub_vstar_le (hβ : M.β < 1) (v : S → ℝ) (n : ℕ) :
    ‖M.T^[n] v - M.vstar hβ‖ ≤ M.β ^ n * ‖v - M.vstar hβ‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    conv_lhs => rw [← M.T_vstar hβ]
    refine (M.norm_T_sub_le _ _).trans ?_
    rw [pow_succ']
    nlinarith [M.β_nonneg]

/-- After the greedy policy has frozen at `σ*`, the value-iteration error evolves linearly:
`T^{N+k}v − v* = βᵏP_{σ*}ᵏ(T^Nv − v*)`. -/
theorem eventually_linear (hβ : M.β < 1) {σs : S → A}
    (hstrict : ∀ s, σs s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, a ≠ σs s →
      M.Q (M.vstar hβ) s a < M.Q (M.vstar hβ) s (σs s)) (v : S → ℝ) :
    ∃ N, ∀ k, M.T^[N + k] v - M.vstar hβ =
      M.β ^ k • (M.Pmat σs ^ k *ᵥ (M.T^[N] v - M.vstar hβ)) := by
  obtain ⟨ρ, hρ, hfreeze⟩ := M.eventually_T_eq_Tσ hβ hstrict
  have hlim : Tendsto (fun n : ℕ => M.β ^ n * ‖v - M.vstar hβ‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg hβ).mul_const
      ‖v - M.vstar hβ‖
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hρ))
  have hnear : ∀ n, N ≤ n → ‖M.T^[n] v - M.vstar hβ‖ < ρ := fun n hn =>
    (M.norm_iterate_sub_vstar_le hβ v n).trans_lt (hN n hn)
  have hstar : M.T (M.vstar hβ) = M.Tσ σs (M.vstar hβ) :=
    hfreeze _ (by rw [sub_self, norm_zero]; exact hρ)
  refine ⟨N, fun k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Function.iterate_succ_apply', hfreeze _ (hnear _ (by omega))]
    conv_lhs => rw [← M.T_vstar hβ, hstar]
    have e := M.Tσ_sub σs (M.T^[N + k] v) (M.vstar hβ)
    funext s
    have := congrFun e s
    simp only [Pi.sub_apply]
    rw [this, ih, mulVec_smul, mulVec_mulVec, ← pow_succ']
    simp only [Pi.smul_apply, smul_eq_mul, pow_succ]
    ring

/-- **Relative value iteration converges at rate `βλ(P_{σ*})`** (Morton and Wecker, 1977;
Bray, Prop 3): with a unique, strict optimal decision rule `σ*`, for every `γ > λ(P_{σ*})`
there are `C` and `N` with `sp(T^{N+k}v − v*) ≤ C(βγ)ᵏ`. -/
theorem relative_asymptotic_rate [Nonempty S] (hβ : M.β < 1) {σs : S → A}
    (hstrict : ∀ s, σs s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, a ≠ σs s →
      M.Q (M.vstar hβ) s a < M.Q (M.vstar hβ) s (σs s))
    (s₀ : S) {γ : ℝ} (hγ : subradius (M.Pmat σs) s₀ < γ) (v : S → ℝ) :
    ∃ C N, ∀ k, sp (fun s => M.T^[N + k] v s - M.vstar hβ s) ≤ C * (M.β * γ) ^ k := by
  obtain ⟨N, hN⟩ := M.eventually_linear hβ hstrict v
  obtain ⟨C, hC0, hC⟩ := sp_pow_mulVec_le (M.Pmat_isStochastic σs) s₀ hγ
  refine ⟨C * sp (M.T^[N] v - M.vstar hβ), N, fun k => ?_⟩
  have e : (fun s => M.T^[N + k] v s - M.vstar hβ s) =
      fun s => M.β ^ k * (M.Pmat σs ^ k *ᵥ (M.T^[N] v - M.vstar hβ)) s := by
    funext s
    have := congrFun (hN k) s
    simpa using this
  rw [e]
  calc sp (fun s => M.β ^ k * (M.Pmat σs ^ k *ᵥ (M.T^[N] v - M.vstar hβ)) s)
      ≤ M.β ^ k * sp (M.Pmat σs ^ k *ᵥ (M.T^[N] v - M.vstar hβ)) :=
        sp_mul_le (pow_nonneg M.β_nonneg k) _
    _ ≤ M.β ^ k * (C * γ ^ k * sp (M.T^[N] v - M.vstar hβ)) :=
        mul_le_mul_of_nonneg_left (hC k _) (pow_nonneg M.β_nonneg k)
    _ = C * sp (M.T^[N] v - M.vstar hβ) * (M.β * γ) ^ k := by rw [mul_pow]; ring

/-- The relative values converge at rate `βλ(P_{σ*})`. -/
theorem rel_asymptotic_rate [Nonempty S] (hβ : M.β < 1) {σs : S → A}
    (hstrict : ∀ s, σs s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, a ≠ σs s →
      M.Q (M.vstar hβ) s a < M.Q (M.vstar hβ) s (σs s))
    (s₀ : S) {γ : ℝ} (hγ : subradius (M.Pmat σs) s₀ < γ) (v : S → ℝ) :
    ∃ C N, ∀ k s, |rel s₀ (M.T^[N + k] v) s - rel s₀ (M.vstar hβ) s| ≤ C * (M.β * γ) ^ k := by
  obtain ⟨C, N, h⟩ := M.relative_asymptotic_rate hβ hstrict s₀ hγ v
  refine ⟨C, N, fun k s => le_trans ?_ (h k)⟩
  have := abs_sub_le_sp (fun s => M.T^[N + k] v s - M.vstar hβ s) s s₀
  simp only [rel]
  convert this using 2
  ring

omit [DecidableEq S] in
/-- **Standard value iteration converges no faster than `β`**: for a stationary distribution `ψ`
of `P_{σ*}`, `‖T^{N+k}v − v*‖ ≥ βᵏ|ψ·(T^Nv − v*)|`. -/
theorem level_rate_lower (hβ : M.β < 1) {σs : S → A}
    (hstrict : ∀ s, σs s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, a ≠ σs s →
      M.Q (M.vstar hβ) s a < M.Q (M.vstar hβ) s (σs s))
    {ψ : S → ℝ} (hψ0 : ∀ s, 0 ≤ ψ s) (hψ1 : ∑ s, ψ s = 1)
    (hψs : ∀ t, ∑ s, ψ s * M.Pmat σs s t = ψ t) (v : S → ℝ) :
    ∃ N, ∀ k, M.β ^ k * |∑ s, ψ s * (M.T^[N] v - M.vstar hβ) s| ≤
      ‖M.T^[N + k] v - M.vstar hβ‖ := by
  classical
  obtain ⟨N, hN⟩ := M.eventually_linear hβ hstrict v
  refine ⟨N, fun k => ?_⟩
  set d := M.T^[N] v - M.vstar hβ
  have hstat : ∀ (j : ℕ) (w : S → ℝ), ∑ s, ψ s * (M.Pmat σs ^ j *ᵥ w) s = ∑ s, ψ s * w s := by
    intro j
    induction j with
    | zero => intro w; simp
    | succ j ih =>
      intro w
      rw [pow_succ', ← mulVec_mulVec]
      have : ∀ u : S → ℝ, ∑ s, ψ s * (M.Pmat σs *ᵥ u) s = ∑ t, ψ t * u t := fun u => by
        calc ∑ s, ψ s * (M.Pmat σs *ᵥ u) s = ∑ s, ∑ t, ψ s * M.Pmat σs s t * u t := by
              simp only [mulVec, dotProduct, mul_sum]
              exact sum_congr rfl fun s _ => sum_congr rfl fun t _ => by ring
          _ = ∑ t, (∑ s, ψ s * M.Pmat σs s t) * u t := by
              rw [sum_comm]
              exact sum_congr rfl fun t _ => by rw [sum_mul]
          _ = ∑ t, ψ t * u t := by simp only [hψs]
      rw [this, ih]
  have e : ∑ s, ψ s * (M.T^[N + k] v - M.vstar hβ) s = M.β ^ k * ∑ s, ψ s * d s := by
    rw [hN k]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ∑ s, ψ s * (M.β ^ k * (M.Pmat σs ^ k *ᵥ d) s) =
      M.β ^ k * ∑ s, ψ s * (M.Pmat σs ^ k *ᵥ d) s by
        rw [mul_sum]; exact sum_congr rfl fun s _ => by ring, hstat]
  have hbound : |∑ s, ψ s * (M.T^[N + k] v - M.vstar hβ) s| ≤ ‖M.T^[N + k] v - M.vstar hβ‖ := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s, |ψ s * (M.T^[N + k] v - M.vstar hβ) s|
        ≤ ∑ s, ψ s * ‖M.T^[N + k] v - M.vstar hβ‖ := sum_le_sum fun s _ => by
          rw [abs_mul, abs_of_nonneg (hψ0 s)]
          refine mul_le_mul_of_nonneg_left ?_ (hψ0 s)
          have := norm_le_pi_norm (M.T^[N + k] v - M.vstar hβ) s
          rwa [Real.norm_eq_abs] at this
      _ = ‖M.T^[N + k] v - M.vstar hβ‖ := by rw [← sum_mul, hψ1, one_mul]
  rw [e, abs_mul, abs_of_nonneg (pow_nonneg M.β_nonneg k)] at hbound
  exact hbound

/-- **The asymptotic rate is never worse than the Dobrushin rate**: `λ(P_σ) ≤ α`. -/
theorem subradius_policy_le [Nonempty S] {σ : S → A} (hσ : M.IsPolicy σ) (s₀ : S) {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α) :
    subradius (M.Pmat σ) s₀ ≤ α :=
  subradius_le_dobrushin (M.Pmat_isStochastic σ) s₀ fun i j => hα i (σ i) j (σ j) (hσ i) (hσ j)

end MDP

end DPExtensions.RelativeValueIteration
