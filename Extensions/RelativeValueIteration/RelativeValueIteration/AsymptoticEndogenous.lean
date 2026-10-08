/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.AsymptoticRates

/-!
# Asymptotic rates: endogenous value iteration converges at rate `βρ(ΛP*)`

Bray (2019b, *Management Science*), Proposition 4.

`Λ` (`lamMat`) subtracts from `v(x, y)` its mean over `y` given `x`. When the transition matrix
`F` maps functions of the exogenous state `x` to functions of `x` (`PreservesLift`, true of every
policy matrix of an `ExoMDP`), `ΛFΛ = ΛF`, so `(ΛF)ᵏΛ = ΛFᵏ` (`lamF_pow_endo`) and the spectral
radius `ρ(ΛF)` (`endoRadius`) governs the within-`x` span (`spy_pow_mulVec_le`).

* `endo_asymptotic_rate`: with a unique, strict optimal decision rule `σ*`, for every
  `γ > ρ(ΛP_{σ*})` there are `C` and `N` with `spy(T^{N+k}v − v*) ≤ C(βγ)ᵏ`; the endogenous
  values `Λ(Tⁿv)` converge at rate `βρ(ΛP_{σ*})` (`endo_values_asymptotic_rate`) (Bray, Prop 4.1).
* `endo_policy_eval_le` (Bray, Prop 4.2): endogenous policy evaluation converges at rate
  `βρ(ΛP_σ)`.
* `endoRadius_le_subradius` (**Bray, Prop 4**): `ρ(ΛF) ≤ λ(F)`, so endogenous value iteration is
  asymptotically never slower than relative value iteration.
-/

open Filter Topology Matrix Finset

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace DPExtensions.RelativeValueIteration

namespace ExoMDP

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype X] in
theorem endo_idem [Nonempty Y] (v : X × Y → ℝ) : endo (endo v) = endo v := by
  have e : endo v = fun t => v t + lift (fun x => -mean v x) t := by
    funext t
    simp only [endo, lift]
    ring
  conv_lhs => rw [e]
  rw [endo_add_lift]

omit [Fintype X] in
theorem endo_lift [Nonempty Y] (c : X → ℝ) : endo (lift c : X × Y → ℝ) = 0 := by
  rw [show (lift c : X × Y → ℝ) = fun t => (fun _ => (0 : ℝ)) t + lift c t by
    funext t; simp, endo_add_lift]
  funext s
  simp [endo, mean]

/-- `F` maps functions of the exogenous state to functions of the exogenous state. -/
def PreservesLift (F : Matrix (X × Y) (X × Y) ℝ) : Prop :=
  ∀ c : X → ℝ, ∃ c' : X → ℝ, F *ᵥ lift c = lift c'

theorem endo_mulVec_endo [Nonempty Y] {G : Matrix (X × Y) (X × Y) ℝ} (hG : PreservesLift G)
    (d : X × Y → ℝ) : endo (G *ᵥ endo d) = endo (G *ᵥ d) := by
  obtain ⟨c', hc'⟩ := hG fun x => -mean d x
  have e : endo d = d + lift fun x => -mean d x := by
    funext t
    simp only [endo, lift, Pi.add_apply]
    ring
  rw [e, mulVec_add, hc']
  exact endo_add_lift (G *ᵥ d) c'

theorem spy_le_two_norm_endo [Nonempty X] [Nonempty Y] (w : X × Y → ℝ) : spy w ≤ 2 * ‖endo w‖ :=
  sup'_le _ _ fun x _ => sp_le fun y y' => by
    have e : w (x, y) - w (x, y') = endo w (x, y) - endo w (x, y') := by
      simp only [endo]
      ring
    have h1 := abs_le.1 ((Real.norm_eq_abs _).symm ▸ norm_le_pi_norm (endo w) (x, y))
    have h2 := abs_le.1 ((Real.norm_eq_abs _).symm ▸ norm_le_pi_norm (endo w) (x, y'))
    linarith [h1.2, h2.1]

theorem norm_endo_le [Nonempty X] [Nonempty Y] (d : X × Y → ℝ) : ‖endo d‖ ≤ spy d :=
  (pi_norm_le_iff_of_nonneg (spy_nonneg d)).2 fun s => by
    rw [Real.norm_eq_abs]
    exact abs_endo_le d s

theorem spy_mul_le [Nonempty X] [Nonempty Y] {c : ℝ} (hc : 0 ≤ c) (w : X × Y → ℝ) :
    spy (fun s => c * w s) ≤ c * spy w :=
  sup'_le _ _ fun x _ =>
    (sp_mul_le hc fun y => w (x, y)).trans (mul_le_mul_of_nonneg_left (sp_le_spy w x) hc)

variable [DecidableEq X] [DecidableEq Y]

/-- The matrix of the endogenizing operator `Λ`. -/
noncomputable def lamMat : Matrix (X × Y) (X × Y) ℝ := fun s t =>
  (if s = t then 1 else 0) - (if s.1 = t.1 then (Fintype.card Y : ℝ)⁻¹ else 0)

theorem lamMat_mulVec (v : X × Y → ℝ) : lamMat *ᵥ v = endo v := by
  funext s
  simp only [mulVec, dotProduct, lamMat, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul,
    sum_ite_eq, mem_univ, ite_true, endo, mean]
  congr 1
  rw [Fintype.sum_prod_type, sum_eq_single s.1
    (fun x _ hx => sum_eq_zero fun y _ => by simp [Ne.symm hx]) (by simp)]
  simp only [ite_true, ← mul_sum]
  rw [div_eq_inv_mul]

/-- The spectral radius of `ΛF`, which governs endogenous value iteration. -/
noncomputable def endoRadius (F : Matrix (X × Y) (X × Y) ℝ) : ℝ := specRad (lamMat * F)

theorem PreservesLift.pow {F : Matrix (X × Y) (X × Y) ℝ} (hF : PreservesLift F) (k : ℕ) :
    PreservesLift (F ^ k) := by
  induction k with
  | zero => exact fun c => ⟨c, one_mulVec _⟩
  | succ k ih =>
    intro c
    obtain ⟨c', hc'⟩ := hF c
    obtain ⟨c'', hc''⟩ := ih c'
    exact ⟨c'', by rw [pow_succ, ← mulVec_mulVec, hc', hc'']⟩

/-- `(ΛF)ᵏΛ = ΛFᵏ`. -/
theorem lamF_pow_endo [Nonempty Y] {F : Matrix (X × Y) (X × Y) ℝ} (hF : PreservesLift F)
    (k : ℕ) (d : X × Y → ℝ) : (lamMat * F) ^ k *ᵥ endo d = endo (F ^ k *ᵥ d) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, lamMat_mulVec, endo_mulVec_endo hF, ih,
      mulVec_mulVec, ← pow_succ]

/-- **`ρ(ΛF)` governs the within-`x` span**: for every `γ > ρ(ΛF)` there is `C` with
`spy(Fᵏd) ≤ Cγᵏ spy(d)` for all `k`. -/
theorem spy_pow_mulVec_le [Nonempty X] [Nonempty Y] {F : Matrix (X × Y) (X × Y) ℝ}
    (hF : PreservesLift F) {γ : ℝ} (hγ : endoRadius F < γ) :
    ∃ C, 0 ≤ C ∧ ∀ (k : ℕ) (d : X × Y → ℝ), spy (F ^ k *ᵥ d) ≤ C * γ ^ k * spy d := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_pow_le (lamMat * F) hγ
  have hγ0 : 0 < γ := (specRad_nonneg _).trans_lt hγ
  refine ⟨2 * C, by positivity, fun k d => ?_⟩
  calc spy (F ^ k *ᵥ d) ≤ 2 * ‖endo (F ^ k *ᵥ d)‖ := spy_le_two_norm_endo _
    _ = 2 * ‖(lamMat * F) ^ k *ᵥ endo d‖ := by rw [lamF_pow_endo hF]
    _ ≤ 2 * (‖(lamMat * F) ^ k‖ * ‖endo d‖) :=
        mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) zero_le_two
    _ ≤ 2 * (C * γ ^ k * spy d) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le_two
        exact mul_le_mul (hC k) (norm_endo_le d) (norm_nonneg _) (by positivity)
    _ = 2 * C * γ ^ k * spy d := by ring

/-- **Endogenous value iteration is asymptotically no slower than relative value iteration**
(Bray, Prop 4): `ρ(ΛF) ≤ λ(F)`. -/
theorem endoRadius_le_subradius [Nonempty X] [Nonempty Y] {F : Matrix (X × Y) (X × Y) ℝ}
    (hQ : IsStochastic F) (hF : PreservesLift F) (s₀ : X × Y) :
    endoRadius F ≤ subradius F s₀ := by
  refine le_of_forall_gt_imp_ge_of_dense fun γ hγ => ?_
  obtain ⟨C, hC0, hC⟩ := sp_pow_mulVec_le hQ s₀ hγ
  have hγ0 : 0 ≤ γ := (specRad_nonneg _).trans hγ.le
  refine specRad_le_of_norm_pow_le _ (K := 1 + 2 * C) (by positivity) hγ0 fun k => ?_
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  change ‖(lamMat * F) ^ k *ᵥ w‖ ≤ (1 + 2 * C) * γ ^ k * ‖w‖
  rcases k with _ | k
  · simp only [pow_zero, one_mulVec, mul_one]
    nlinarith [norm_nonneg w]
  have e : (lamMat * F) ^ (k + 1) *ᵥ w = endo (F ^ (k + 1) *ᵥ w) := by
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, lamMat_mulVec, lamF_pow_endo hF,
      mulVec_mulVec, ← pow_succ]
  rw [e]
  calc ‖endo (F ^ (k + 1) *ᵥ w)‖ ≤ spy (F ^ (k + 1) *ᵥ w) := norm_endo_le _
    _ ≤ sp (F ^ (k + 1) *ᵥ w) := spy_le_sp _
    _ ≤ C * γ ^ (k + 1) * sp w := hC _ _
    _ ≤ C * γ ^ (k + 1) * (2 * ‖w‖) :=
        mul_le_mul_of_nonneg_left (sp_le_two_norm w) (by positivity)
    _ ≤ (1 + 2 * C) * γ ^ (k + 1) * ‖w‖ := by nlinarith [norm_nonneg w, pow_nonneg hγ0 (k + 1)]

variable {A : Type*} (E : ExoMDP X Y A)

omit [DecidableEq X] [DecidableEq Y] in
/-- Every policy matrix of an `ExoMDP` preserves functions of the exogenous state. -/
theorem Pmat_preservesLift (σ : X × Y → A) : PreservesLift (E.toMDP.Pmat σ) := fun c =>
  ⟨E.Fxc c, by
    funext s
    change ∑ t, E.toMDP.P s (σ s) t * lift c t = lift (E.Fxc c) s
    simp only [E.sum_P_mul, lift, ← sum_mul, E.Fy_sum, one_mul, Fxc]⟩

/-- **Endogenous policy evaluation converges at rate `βρ(ΛP_σ)`** (Bray, 2019b, Prop 4.2). -/
theorem endo_policy_eval_le [Nonempty X] [Nonempty Y] (hβ : E.β < 1) (σ : X × Y → A) {γ : ℝ}
    (hγ : endoRadius (E.toMDP.Pmat σ) < γ) :
    ∃ C, 0 ≤ C ∧ ∀ (n : ℕ) (v : X × Y → ℝ),
      spy (fun s => (E.toMDP.Tσ σ)^[n] v s - E.toMDP.vσ hβ σ s) ≤
        C * (E.β * γ) ^ n * spy (fun s => v s - E.toMDP.vσ hβ σ s) := by
  obtain ⟨C, hC0, hC⟩ := spy_pow_mulVec_le (E.Pmat_preservesLift σ) hγ
  refine ⟨C, hC0, fun n v => ?_⟩
  have hfix : (E.toMDP.Tσ σ)^[n] (E.toMDP.vσ hβ σ) = E.toMDP.vσ hβ σ :=
    Function.iterate_fixed (E.toMDP.Tσ_vσ hβ σ) n
  have e := E.toMDP.Tσ_iterate_sub σ v (E.toMDP.vσ hβ σ) n
  rw [hfix] at e
  rw [e]
  calc spy (fun s => E.β ^ n * (E.toMDP.Pmat σ ^ n *ᵥ (v - E.toMDP.vσ hβ σ)) s)
      ≤ E.β ^ n * spy (E.toMDP.Pmat σ ^ n *ᵥ (v - E.toMDP.vσ hβ σ)) :=
        spy_mul_le (pow_nonneg E.β_nonneg n) _
    _ ≤ E.β ^ n * (C * γ ^ n * spy (v - E.toMDP.vσ hβ σ)) :=
        mul_le_mul_of_nonneg_left (hC n _) (pow_nonneg E.β_nonneg n)
    _ = C * (E.β * γ) ^ n * spy (fun s => v s - E.toMDP.vσ hβ σ s) := by
        rw [mul_pow]
        change _ = C * (E.β ^ n * γ ^ n) * spy (v - E.toMDP.vσ hβ σ)
        ring

/-- **Endogenous value iteration converges at rate `βρ(ΛP_{σ*})`**: with a unique, strict optimal
decision rule `σ*`, for every `γ > ρ(ΛP_{σ*})` there are `C` and `N` with
`spy(T^{N+k}v − v*) ≤ C(βγ)ᵏ`. -/
theorem endo_asymptotic_rate [Nonempty X] [Nonempty Y] (hβ : E.β < 1) {σs : X × Y → A}
    (hstrict : ∀ s, σs s ∈ E.Γ s ∧ ∀ a ∈ E.Γ s, a ≠ σs s →
      E.toMDP.Q (E.toMDP.vstar hβ) s a < E.toMDP.Q (E.toMDP.vstar hβ) s (σs s))
    {γ : ℝ} (hγ : endoRadius (E.toMDP.Pmat σs) < γ) (v : X × Y → ℝ) :
    ∃ C N, ∀ k, spy (fun s => E.toMDP.T^[N + k] v s - E.toMDP.vstar hβ s) ≤
      C * (E.β * γ) ^ k := by
  obtain ⟨N, hN⟩ := E.toMDP.eventually_linear hβ hstrict v
  obtain ⟨C, hC0, hC⟩ := spy_pow_mulVec_le (E.Pmat_preservesLift σs) hγ
  refine ⟨C * spy (E.toMDP.T^[N] v - E.toMDP.vstar hβ), N, fun k => ?_⟩
  have e : (fun s => E.toMDP.T^[N + k] v s - E.toMDP.vstar hβ s) =
      fun s => E.β ^ k *
        (E.toMDP.Pmat σs ^ k *ᵥ (E.toMDP.T^[N] v - E.toMDP.vstar hβ)) s := by
    funext s
    have := congrFun (hN k) s
    simpa using this
  rw [e]
  calc spy (fun s => E.β ^ k *
        (E.toMDP.Pmat σs ^ k *ᵥ (E.toMDP.T^[N] v - E.toMDP.vstar hβ)) s)
      ≤ E.β ^ k * spy (E.toMDP.Pmat σs ^ k *ᵥ (E.toMDP.T^[N] v - E.toMDP.vstar hβ)) :=
        spy_mul_le (pow_nonneg E.β_nonneg k) _
    _ ≤ E.β ^ k * (C * γ ^ k * spy (E.toMDP.T^[N] v - E.toMDP.vstar hβ)) :=
        mul_le_mul_of_nonneg_left (hC k _) (pow_nonneg E.β_nonneg k)
    _ = C * spy (E.toMDP.T^[N] v - E.toMDP.vstar hβ) * (E.β * γ) ^ k := by rw [mul_pow]; ring

/-- The endogenous values `Λ(Tⁿv)` converge to `Λv*` at rate `βρ(ΛP_{σ*})`. -/
theorem endo_values_asymptotic_rate [Nonempty X] [Nonempty Y] (hβ : E.β < 1) {σs : X × Y → A}
    (hstrict : ∀ s, σs s ∈ E.Γ s ∧ ∀ a ∈ E.Γ s, a ≠ σs s →
      E.toMDP.Q (E.toMDP.vstar hβ) s a < E.toMDP.Q (E.toMDP.vstar hβ) s (σs s))
    {γ : ℝ} (hγ : endoRadius (E.toMDP.Pmat σs) < γ) (v : X × Y → ℝ) :
    ∃ C N, ∀ k s, |endo (E.toMDP.T^[N + k] v) s - endo (E.toMDP.vstar hβ) s| ≤
      C * (E.β * γ) ^ k := by
  obtain ⟨C, N, h⟩ := E.endo_asymptotic_rate hβ hstrict hγ v
  refine ⟨C, N, fun k s => le_trans ?_ (h k)⟩
  rw [← congrFun (endo_sub _ _) s]
  exact abs_endo_le _ s

/-- For every decision rule, the endogenous asymptotic rate is at most the relative one. -/
theorem endoRadius_policy_le [Nonempty X] [Nonempty Y] (σ : X × Y → A) (s₀ : X × Y) :
    endoRadius (E.toMDP.Pmat σ) ≤ subradius (E.toMDP.Pmat σ) s₀ :=
  endoRadius_le_subradius (E.toMDP.Pmat_isStochastic σ) (E.Pmat_preservesLift σ) s₀

end ExoMDP

end DPExtensions.RelativeValueIteration
