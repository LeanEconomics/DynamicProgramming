/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.NewKeynesian
import NewKeynesian.NKPhillips
import NewKeynesian.ScalarRE

/-!
# Determinacy of the basic DNK model: Exercise 19.1 (Bullard–Mitra)

Miao, §19.1.7, p. 627 ((19.24), (19.28), (19.29)), condition (19.31), p. 635, and Exercise 1 of
§19.5, p. 668. The log-linear system is, for random variables in a Banach space `V` with
conditional expectations `E_t` and the constant random variable `𝟙` (adapted, nonzero):

`π_t = βE_tπ_{t+1} + κx_t`, `x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1} − r^n_t)`,
`i_t = −ln β + φ_ππ_t + φ_yx_t + v_t` (`nk_dnkSystem`).

* Substituting the Taylor rule, the system is the jump-only system of Exercise 2.2 with
  `ε_t = v_t − r^n_t − ln β` (`nk_dnk_iff`); the proof of Exercise 19.1 uses the Chapter 2
  Blanchard–Kahn results for it (`ex_2_2_suff`, `nk_jump2_nonunique`, `nk_bothOut_WT`).
* **Exercise 19.1** (`ex_19_1`): for `κ, γ > 0`, `0 < β < 1` and `φ_π, φ_y ≥ 0`, the model has a
  unique stable (bounded, adapted) equilibrium for all bounded adapted shocks `v`, `r^n`
  (`nk_dnkDeterminate`) iff (19.31) `κ(φ_π − 1) + (1 − β)φ_y > 0`.
* For `φ_y ≥ 0` and any `φ_π` the exact condition adds the branch
  `κ(1 + φ_π) + (1 + β)(2γ + φ_y) < 0` (`ex_19_1_exact`); without `φ_π ≥ 0`, (19.31) is not
  necessary (`ex_19_1_not_necessary`: `κ = γ = 1`, `β = 1/2`, `φ_π = −5`, `φ_y = 0`). The book
  states no sign restriction; Bullard and Mitra assume nonnegative coefficients.
* With the structural slope κ of (19.25) (`ex_19_1_structural`).
* Figures 19.1–19.2 (qualitative). For an AR(1) monetary shock (`E_tv_{t+1} = ρv_t`,
  `0 ≤ ρ < 1`) the unique equilibrium is `x_t = −(1 − βρ)Λv_t`, `π_t = −κΛv_t` with
  `Λ = 1/((1 − βρ)(γ(1 − ρ) + φ_y) + κ(φ_π − ρ)) > 0` under (19.31): the output gap and
  inflation fall after a positive shock, the real rate `i_t − E_tπ_{t+1}` rises, and rises by
  `ρκΛv_t` more than the nominal rate (`nk_fig_19_1`). For an AR(1) natural-rate shock
  `r̂^n` the output gap, inflation and the nominal rate rise and the real rate rises by a
  fraction in `(0, 1)` of the shock (`nk_fig_19_2`). The plotted magnitudes (Dynare) are not
  formalised.
-/

namespace Miao.NewKeynesian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The log-linear basic DNK model (19.24), (19.28), (19.29) (Miao, p. 627). -/
def nk_dnkSystem (E : CondExpSystem ℝ V) (β γ κ φπ φy : ℝ) (one : V) (v rn x pi i : ℕ → V) :
    Prop :=
  ∀ t, pi t = β • E.E t (pi (t + 1)) + κ • x t ∧
    x t = E.E t (x (t + 1)) - γ⁻¹ • (i t - E.E t (pi (t + 1)) - rn t) ∧
    i t = (-Real.log β) • one + φπ • pi t + φy • x t + v t

/-- Exercise 19.1 (Miao, p. 668): a unique stable equilibrium for all bounded adapted shocks
`v` and `r^n`: exactly one triple `(x, π, i)` of adapted bounded processes solves the model. -/
def nk_dnkDeterminate (E : CondExpSystem ℝ V) (β γ κ φπ φy : ℝ) (one : V) : Prop :=
  ∀ v rn : ℕ → V, sre_IsBounded v → sre_IsBounded rn → sre_IsAdapted E v →
    sre_IsAdapted E rn →
    ∃! z : (ℕ → V) × (ℕ → V) × (ℕ → V), nk_dnkSystem E β γ κ φπ φy one v rn z.1 z.2.1 z.2.2 ∧
      sre_IsAdapted E z.1 ∧ sre_IsAdapted E z.2.1 ∧ sre_IsAdapted E z.2.2 ∧
      sre_IsBounded z.1 ∧ sre_IsBounded z.2.1 ∧ sre_IsBounded z.2.2

/-- Miao, p. 627: substituting the Taylor rule (19.29) into (19.28), the model is the
Exercise 2.2 system `nkTaylorEqm` for the state `(x_t, π_t)` with `ε_t = v_t − r^n_t − ln β`,
`ε^x = 0`, together with the rule determining `i_t`. -/
theorem nk_dnk_iff (E : CondExpSystem ℝ V) (β γ κ φπ φy : ℝ) (one : V) (v rn x pi i : ℕ → V) :
    nk_dnkSystem E β γ κ φπ φy one v rn x pi i ↔
      nkTaylorEqm E κ β γ φπ φy (fun t => v t - rn t - Real.log β • one) (fun _ => 0)
          (fun t => ![x t, pi t]) ∧
        ∀ t, i t = (-Real.log β) • one + φπ • pi t + φy • x t + v t := by
  simp only [nk_dnkSystem, nkTaylorEqm, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
  constructor
  · intro h
    refine ⟨fun t => ⟨?_, ?_⟩, fun t => (h t).2.2⟩
    · rw [(h t).1, add_comm]
    · obtain ⟨-, h2, h3⟩ := h t
      refine h2.trans ?_
      rw [h3]
      congr 2
      module
  · rintro ⟨h, hi⟩ t
    refine ⟨by rw [(h t).1, add_comm], (h t).2.trans ?_, hi t⟩
    rw [hi t]
    congr 2
    module

omit [NormedSpace ℝ V] in
/-- Two bounded processes form a stable pair. -/
theorem nk_pair_stable {x pi : ℕ → V} (hx : sre_IsBounded x) (hp : sre_IsBounded pi) :
    IsStableProc (fun t => ![x t, pi t]) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hp
  refine ⟨|M| + |N| + 1, by positivity, fun t j => ?_⟩
  fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    linarith [hM t, le_abs_self M, abs_nonneg N]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith [hN t, le_abs_self N, abs_nonneg M]

/-- Two adapted processes form an adapted pair. -/
theorem nk_pair_adapted (E : CondExpSystem ℝ V) {x pi : ℕ → V} (hx : sre_IsAdapted E x)
    (hp : sre_IsAdapted E pi) : IsAdaptedV E (fun t => ![x t, pi t]) := fun t j => by
  fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, hx t]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hp t]

/-- The Taylor-rule interest rate of bounded adapted `x, π, v` is bounded and adapted. -/
theorem nk_rule_regular (E : CondExpSystem ℝ V) {β φπ φy : ℝ} {one : V}
    (hone : ∀ t, E.E t one = one) {x pi v : ℕ → V} (hx : sre_IsBounded x)
    (hp : sre_IsBounded pi) (hv : sre_IsBounded v) (hxa : sre_IsAdapted E x)
    (hpa : sre_IsAdapted E pi) (hva : sre_IsAdapted E v) :
    sre_IsAdapted E (fun t => (-Real.log β) • one + φπ • pi t + φy • x t + v t) ∧
      sre_IsBounded (fun t => (-Real.log β) • one + φπ • pi t + φy • x t + v t) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hp
  obtain ⟨K, hK⟩ := hv
  refine ⟨fun t => by simp only [map_add, map_smul, hone, hxa t, hpa t, hva t], ?_⟩
  refine ⟨‖(-Real.log β) • one‖ + |φπ| * N + |φy| * M + K, fun t => ?_⟩
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)) (hK t))
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hN t) (abs_nonneg _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg _)

/-- **Exercise 19.1, sufficiency** (Miao, p. 668): with `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0` and
an adapted constant `𝟙`, if `κ(φ_π − 1) + (1 − β)φ_y > 0` (or
`κ(1 + φ_π) + (1 + β)(2γ + φ_y) < 0`), the model has a unique stable equilibrium. -/
theorem ex_19_1_suff [CompleteSpace V] (E : CondExpSystem ℝ V) {β γ κ φπ φy : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφy : 0 ≤ φy)
    (hone : ∀ t, E.E t one = one)
    (hc : 0 < κ * (φπ - 1) + (1 - β) * φy ∨ κ * (1 + φπ) + (1 + β) * (2 * γ + φy) < 0) :
    nk_dnkDeterminate E β γ κ φπ φy one := by
  intro v rn hv hrn hva hrna
  have hdet := ex_2_2_suff E hκ hβ0 hβ1 hγ hφy hc
  obtain ⟨Mv, hMv⟩ := hv
  obtain ⟨Mr, hMr⟩ := hrn
  obtain ⟨X, ⟨hX, hXa, hXs⟩, hXu⟩ := hdet (fun t => v t - rn t - Real.log β • one)
    (fun _ => 0) ⟨Mv + Mr + ‖Real.log β • one‖, fun t =>
      (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (hMv t)
        (hMr t))) le_rfl)⟩ ⟨0, fun _ => by simp⟩
    (fun t => by simp only [map_sub, map_smul, hva t, hrna t, hone]) (fun _ => map_zero _)
  have hXeq : X = fun t => ![X t 0, X t 1] := funext fun t => funext fun j => by
    fin_cases j <;> rfl
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff X).1 hXs
  have hb0 : sre_IsBounded (fun t => X t 0) := ⟨C, fun t => (norm_le_pi_norm _ 0).trans (hC t)⟩
  have hb1 : sre_IsBounded (fun t => X t 1) := ⟨C, fun t => (norm_le_pi_norm _ 1).trans (hC t)⟩
  have ha0 : sre_IsAdapted E (fun t => X t 0) := fun t => hXa t 0
  have ha1 : sre_IsAdapted E (fun t => X t 1) := fun t => hXa t 1
  obtain ⟨hia, hib⟩ := nk_rule_regular E (β := β) (φπ := φπ) (φy := φy) hone hb0 hb1
    ⟨Mv, hMv⟩ ha0 ha1 hva
  refine ⟨(fun t => X t 0, fun t => X t 1,
    fun t => (-Real.log β) • one + φπ • X t 1 + φy • X t 0 + v t), ⟨?_, ha0, ha1, hia, hb0, hb1,
    hib⟩, ?_⟩
  · rw [nk_dnk_iff]
    exact ⟨hXeq ▸ hX, fun t => rfl⟩
  · rintro ⟨x', pi', i'⟩ ⟨hsys, hxa, hpa, -, hxb, hpb, -⟩
    obtain ⟨hT, hi⟩ := (nk_dnk_iff E β γ κ φπ φy one v rn x' pi' i').1 hsys
    have hu := hXu (fun t => ![x' t, pi' t]) ⟨hT, nk_pair_adapted E hxa hpa,
      nk_pair_stable hxb hpb⟩
    have h0 : x' = fun t => X t 0 := funext fun t => by
      have := congrFun (congrFun hu t) 0
      simpa using this
    have h1 : pi' = fun t => X t 1 := funext fun t => by
      have := congrFun (congrFun hu t) 1
      simpa using this
    have h2 : i' = fun t => (-Real.log β) • one + φπ • X t 1 + φy • X t 0 + v t :=
      funext fun t => by rw [hi t, h0, h1]
    rw [h0, h1, h2]

/-- **Exercise 19.1, necessity** (Miao, p. 668): with `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0` and an
adapted constant `𝟙 ≠ 0`, if the model has a unique stable equilibrium then
`κ(φ_π − 1) + (1 − β)φ_y > 0` or `κ(1 + φ_π) + (1 + β)(2γ + φ_y) < 0`. Otherwise a root of the
jump matrix inside the closed unit disc gives a nonzero stable solution of the homogeneous
system, which can be added to the equilibrium with `v = r^n = 0`. -/
theorem ex_19_1_nec (E : CondExpSystem ℝ V) {β γ κ φπ φy : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφy : 0 ≤ φy) (hone0 : one ≠ 0)
    (hone : ∀ t, E.E t one = one) (hdet : nk_dnkDeterminate E β γ κ φπ φy one) :
    0 < κ * (φπ - 1) + (1 - β) * φy ∨ κ * (1 + φπ) + (1 + β) * (2 * γ + φy) < 0 := by
  by_contra hc
  have hnb := fun hb => hc ((nk_bothOut_WT (δπ := φπ) hκ hβ0 hβ1 hγ hφy).1 hb)
  have hM10 : nkWT κ β γ φπ φy 1 0 ≠ 0 := by
    have e : nkWT κ β γ φπ φy 1 0 = -κ / β := by simp [nkWT]
    rw [e]
    exact div_ne_zero (neg_ne_zero.2 hκ.ne') hβ0.ne'
  obtain ⟨H, hH0, hHe, hHa, hHs⟩ := nk_jump2_nonunique E (nkWT κ β γ φπ φy) hM10
    (nk_WT_trace hκ hβ0 hβ1 hγ hφy) hnb hone0 (hone 0)
  obtain ⟨⟨x, pi, i⟩, ⟨hsys, hxa, hpa, hia, hxb, hpb, hib⟩, hu⟩ :=
    hdet (fun _ => 0) (fun _ => 0) ⟨0, fun _ => by simp⟩ ⟨0, fun _ => by simp⟩
      (fun _ => map_zero _) (fun _ => map_zero _)
  obtain ⟨hT, hi⟩ := (nk_dnk_iff E β γ κ φπ φy one _ _ x pi i).1 hsys
  have hT' := (nk_taylor_iff E φπ φy hβ0.ne' _ _ _).1 hT
  set x' : ℕ → V := fun t => x t + H t 0
  set pi' : ℕ → V := fun t => pi t + H t 1
  have hXsum : ∀ t, (![x' t, pi' t] : Fin 2 → V) = ![x t, pi t] + H t := fun t =>
    funext fun j => by fin_cases j <;> rfl
  have hT2 : nkTaylorEqm E κ β γ φπ φy (fun t => (0 : V) - 0 - Real.log β • one) (fun _ => 0)
      (fun t => ![x' t, pi' t]) := by
    rw [nk_taylor_iff E φπ φy hβ0.ne']
    intro t
    have h1 := hT' t
    have h2 := hHe t
    rw [hXsum, hXsum, bkS_Evec_add, matAct_add, h1, h2]
    abel
  obtain ⟨Ma, hMa⟩ := (bkS_isStableProc_iff H).1 hHs
  have hb0 : sre_IsBounded x' := by
    obtain ⟨M, hM⟩ := hxb
    exact ⟨M + Ma, fun t => (norm_add_le _ _).trans (add_le_add (hM t)
      ((norm_le_pi_norm _ 0).trans (hMa t)))⟩
  have hb1 : sre_IsBounded pi' := by
    obtain ⟨M, hM⟩ := hpb
    exact ⟨M + Ma, fun t => (norm_add_le _ _).trans (add_le_add (hM t)
      ((norm_le_pi_norm _ 1).trans (hMa t)))⟩
  have ha0 : sre_IsAdapted E x' := fun t => by simp only [x', map_add, hxa t, hHa t 0]
  have ha1 : sre_IsAdapted E pi' := fun t => by simp only [pi', map_add, hpa t, hHa t 1]
  obtain ⟨hia', hib'⟩ := nk_rule_regular E (β := β) (φπ := φπ) (φy := φy) (v := fun _ => 0)
    hone hb0 hb1 ⟨0, fun _ => by simp⟩ ha0 ha1 (fun _ => map_zero _)
  have hsys' : nk_dnkSystem E β γ κ φπ φy one (fun _ => 0) (fun _ => 0) x' pi'
      (fun t => (-Real.log β) • one + φπ • pi' t + φy • x' t + 0) :=
    (nk_dnk_iff E β γ κ φπ φy one _ _ _ _ _).2 ⟨hT2, fun _ => rfl⟩
  have h1 := hu (x', pi', _) ⟨hsys', ha0, ha1, hia', hb0, hb1, hib'⟩
  have hx : x' = x := congrArg (fun z => z.1) h1
  have hp : pi' = pi := congrArg (fun z => z.2.1) h1
  apply hH0
  funext t j
  fin_cases j
  · have := congrFun hx t
    simp only [x'] at this
    simpa using this
  · have := congrFun hp t
    simp only [pi'] at this
    simpa using this

/-- **Exercise 19.1**, exact conditions (Miao, p. 668): for `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0`
and an adapted constant `𝟙 ≠ 0`, the model has a unique stable equilibrium iff
`κ(φ_π − 1) + (1 − β)φ_y > 0` or `κ(1 + φ_π) + (1 + β)(2γ + φ_y) < 0`. -/
theorem ex_19_1_exact [CompleteSpace V] (E : CondExpSystem ℝ V) {β γ κ φπ φy : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφy : 0 ≤ φy) (hone0 : one ≠ 0)
    (hone : ∀ t, E.E t one = one) :
    nk_dnkDeterminate E β γ κ φπ φy one ↔
      (0 < κ * (φπ - 1) + (1 - β) * φy ∨ κ * (1 + φπ) + (1 + β) * (2 * γ + φy) < 0) :=
  ⟨ex_19_1_nec E hκ hβ0 hβ1 hγ hφy hone0 hone, ex_19_1_suff E hκ hβ0 hβ1 hγ hφy hone⟩

/-- **Exercise 19.1** (Bullard and Mitra; Miao, p. 668), condition (19.31): for `κ, γ > 0`,
`0 < β < 1`, `φ_π, φ_y ≥ 0` and an adapted constant `𝟙 ≠ 0`, the model of §19.1 has a unique
stable equilibrium for all bounded adapted shocks iff `κ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem ex_19_1 [CompleteSpace V] (E : CondExpSystem ℝ V) {β γ κ φπ φy : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (hone0 : one ≠ 0) (hone : ∀ t, E.E t one = one) :
    nk_dnkDeterminate E β γ κ φπ φy one ↔ 0 < κ * (φπ - 1) + (1 - β) * φy := by
  rw [ex_19_1_exact E hκ hβ0 hβ1 hγ hφy hone0 hone]
  refine ⟨fun h => h.resolve_right fun h' => ?_, Or.inl⟩
  nlinarith [mul_nonneg hκ.le hφπ, mul_nonneg hβ0.le hφy]

/-- **Exercise 19.1** with the structural slope (19.25) (Miao, pp. 626, 668): for
`0 < θ < 1`, `0 < β < 1`, `0 ≤ α < 1`, `ε ≥ 0`, `γ > 0`, `ν ≥ 0`, `φ_π, φ_y ≥ 0`, determinacy
holds iff `κ(φ_π − 1) + (1 − β)φ_y > 0` with `κ = nk_kappa β θ γ ν α ε`. -/
theorem ex_19_1_structural [CompleteSpace V] (E : CondExpSystem ℝ V) {β θ γ ν α ε φπ φy : ℝ}
    {one : V} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 0 ≤ ε) (hγ : 0 < γ) (hν : 0 ≤ ν) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (hone0 : one ≠ 0) (hone : ∀ t, E.E t one = one) :
    nk_dnkDeterminate E β γ (nk_kappa β θ γ ν α ε) φπ φy one ↔
      0 < nk_kappa β θ γ ν α ε * (φπ - 1) + (1 - β) * φy := by
  have hβθ : β * θ < 1 := by nlinarith
  have hD : 0 < ν + α + γ * (1 - α) := by nlinarith
  exact ex_19_1 E (nk_kappa_pos hθ0 hθ1 hβθ hα0 hα1 hε hD) hβ0 hβ1 hγ hφπ hφy hone0 hone

/-- Exercise 19.1 without sign restrictions (Miao, p. 668): (19.31) is not necessary. For
`κ = γ = 1`, `β = 1/2`, `φ_π = −5`, `φ_y = 0`, the equilibrium is unique although
`κ(φ_π − 1) + (1 − β)φ_y = −6 < 0`. -/
theorem ex_19_1_not_necessary [CompleteSpace V] (E : CondExpSystem ℝ V) {one : V}
    (hone : ∀ t, E.E t one = one) :
    nk_dnkDeterminate E (1 / 2) 1 1 (-5) 0 one ∧ ¬ (0 < 1 * ((-5 : ℝ) - 1) + (1 - 1 / 2) * 0) :=
  ⟨ex_19_1_suff E one_pos (by norm_num) (by norm_num) one_pos le_rfl hone
    (Or.inr (by norm_num)), by norm_num⟩

/-- The coefficient `Λ = 1/((1 − βρ)(γ(1 − ρ) + φ_y) + κ(φ_π − ρ))` of the impulse responses
(Miao, Figures 19.1–19.2, p. 628). -/
noncomputable def nk_irfLam (β γ κ φπ φy ρ : ℝ) : ℝ :=
  1 / ((1 - β * ρ) * (γ * (1 - ρ) + φy) + κ * (φπ - ρ))

/-- Under (19.31), with `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0` and `ρ < 1`, the denominator of
`Λ` is positive, hence `Λ > 0`, and `γ(1 − ρ)(1 − βρ)Λ < 1`. -/
theorem nk_irfLam_pos {β γ κ φπ φy ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) (hφy : 0 ≤ φy) (hρ1 : ρ < 1)
    (h31 : 0 < κ * (φπ - 1) + (1 - β) * φy) :
    0 < (1 - β * ρ) * (γ * (1 - ρ) + φy) + κ * (φπ - ρ) ∧ 0 < nk_irfLam β γ κ φπ φy ρ ∧
      γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ < 1 := by
  have hbr : 0 < 1 - β * ρ := by nlinarith
  have p1 : 0 ≤ β * (1 - ρ) * φy :=
    mul_nonneg (mul_nonneg hβ0.le (by linarith)) hφy
  have p2 : 0 < κ * (1 - ρ) := mul_pos hκ (by linarith)
  have h2 : 0 < (1 - β * ρ) * φy + κ * (φπ - ρ) := by nlinarith
  have hden : 0 < (1 - β * ρ) * (γ * (1 - ρ) + φy) + κ * (φπ - ρ) := by
    nlinarith [mul_pos hbr (mul_pos hγ (by linarith : (0 : ℝ) < 1 - ρ))]
  refine ⟨hden, by rw [nk_irfLam]; positivity, ?_⟩
  rw [nk_irfLam, ← mul_div_assoc, mul_one, div_lt_one hden]
  nlinarith

/-- The closed-form equilibrium for AR(1) shocks (Miao, Figures 19.1–19.2): if
`E_t s_{t+1} = ρs_t` and the shocks are `v = a•s` and `r^n = −ln β + c•s`, then
`x_t = ((1 − βρ)Λ(c − a))s_t`, `π_t = (κΛ(c − a))s_t` and the Taylor-rule `i_t` solve the
model. -/
theorem nk_irf_solves (E : CondExpSystem ℝ V) {β γ κ φπ φy ρ a c : ℝ} {one : V} {s : ℕ → V}
    (hγ : γ ≠ 0) (hden : (1 - β * ρ) * (γ * (1 - ρ) + φy) + κ * (φπ - ρ) ≠ 0)
    (hs : ∀ t, E.E t (s (t + 1)) = ρ • s t) :
    nk_dnkSystem E β γ κ φπ φy one (fun t => a • s t)
      (fun t => (-Real.log β) • one + c • s t)
      (fun t => ((1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ * (c - a)) • s t)
      (fun t => (κ * nk_irfLam β γ κ φπ φy ρ * (c - a)) • s t)
      (fun t => (-Real.log β) • one +
        φπ • (κ * nk_irfLam β γ κ φπ φy ρ * (c - a)) • s t +
        φy • ((1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ * (c - a)) • s t + a • s t) := by
  intro t
  refine ⟨?_, ?_, rfl⟩
  · simp only [map_smul, hs t, nk_irfLam]
    match_scalars
    field_simp
    ring
  · simp only [map_smul, hs t, nk_irfLam]
    match_scalars
    · field_simp
      ring
    · ring

/-- **Figure 19.1** (Miao, pp. 627–628), qualitatively: an AR(1) monetary policy shock
(`E_tv_{t+1} = ρv_t`, `0 ≤ ρ < 1`, `r^n = −ln β`). Under (19.31) with `κ, γ > 0`,
`0 < β < 1`, `φ_π, φ_y ≥ 0`, every stable equilibrium has `x_t = −((1 − βρ)Λ)v_t`,
`π_t = −(κΛ)v_t` with `(1 − βρ)Λ, κΛ > 0` (the output gap and inflation fall after a positive
shock), the real rate `i_t − E_tπ_{t+1}` is `−ln β + (γ(1 − ρ)(1 − βρ)Λ)v_t` with a positive
coefficient, and the nominal rate is the real rate minus `(ρκΛ)v_t`, `ρκΛ ≥ 0`. -/
theorem nk_fig_19_1 [CompleteSpace V] (E : CondExpSystem ℝ V) {β γ κ φπ φy ρ : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (h31 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    (hone0 : one ≠ 0) (hone : ∀ t, E.E t one = one) {v : ℕ → V} (hvb : sre_IsBounded v)
    (hva : sre_IsAdapted E v) (hv : ∀ t, E.E t (v (t + 1)) = ρ • v t)
    {x pi i : ℕ → V} (hsys : nk_dnkSystem E β γ κ φπ φy one v (fun _ => (-Real.log β) • one)
      x pi i) (hxa : sre_IsAdapted E x) (hpa : sre_IsAdapted E pi) (hia : sre_IsAdapted E i)
    (hxb : sre_IsBounded x) (hpb : sre_IsBounded pi) (hib : sre_IsBounded i) :
    0 < (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ ∧ 0 < κ * nk_irfLam β γ κ φπ φy ρ ∧
    0 < γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ ∧
    0 ≤ ρ * κ * nk_irfLam β γ κ φπ φy ρ ∧
    (∀ t, x t = -(((1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ) • v t)) ∧
    (∀ t, pi t = -((κ * nk_irfLam β γ κ φπ φy ρ) • v t)) ∧
    (∀ t, i t - E.E t (pi (t + 1)) =
      (-Real.log β) • one + (γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ) • v t) ∧
    (∀ t, i t = (i t - E.E t (pi (t + 1))) - (ρ * κ * nk_irfLam β γ κ φπ φy ρ) • v t) := by
  obtain ⟨hden, hL, -⟩ := nk_irfLam_pos hκ hβ0 hβ1 hγ hφy hρ1 h31
  set L := nk_irfLam β γ κ φπ φy ρ with hLdef
  have hbr : 0 < 1 - β * ρ := by nlinarith
  have hsol := nk_irf_solves E (one := one) (a := 1) (c := 0) hγ.ne' hden.ne' hv
  have hdet := (ex_19_1 E hκ hβ0 hβ1 hγ hφπ hφy hone0 hone).2 h31
  obtain ⟨Mv, hMv⟩ := hvb
  have hvb' : sre_IsBounded (fun t => (1 : ℝ) • v t) := ⟨Mv, fun t => by simpa using hMv t⟩
  have hva' : sre_IsAdapted E (fun t => (1 : ℝ) • v t) := fun t => by simp [hva t]
  obtain ⟨z, -, hzu⟩ := hdet (fun t => (1 : ℝ) • v t) (fun _ => (-Real.log β) • one) hvb'
    ⟨‖(-Real.log β) • one‖, fun _ => le_rfl⟩ hva' (fun t => by simp [hone])
  have hsmul : ∀ (k : ℝ), sre_IsBounded (fun t => k • v t) ∧ sre_IsAdapted E (fun t => k • v t) :=
    fun k => ⟨⟨|k| * Mv, fun t => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hMv t) (abs_nonneg _)⟩, fun t => by simp [hva t]⟩
  have hrn : (fun t => (-Real.log β) • one + (0 : ℝ) • v t) = fun _ => (-Real.log β) • one :=
    funext fun t => by simp
  rw [hrn] at hsol
  have hv1 : (fun t => (1 : ℝ) • v t) = v := funext fun t => one_smul _ _
  rw [hv1] at hsol hzu
  obtain ⟨hb1, ha1⟩ := hsmul ((1 - β * ρ) * L * (0 - 1))
  obtain ⟨hb2, ha2⟩ := hsmul (κ * L * (0 - 1))
  obtain ⟨hia', hib'⟩ := nk_rule_regular E (β := β) (φπ := φπ) (φy := φy) hone hb1 hb2
    ⟨Mv, fun t => by simpa using hMv t⟩ ha1 ha2 (fun t => by simp [hva t])
  simp only [one_smul, ← hLdef] at hsol
  have e1 := hzu (x, pi, i) ⟨hsys, hxa, hpa, hia, hxb, hpb, hib⟩
  have e2 := hzu (fun t => ((1 - β * ρ) * L * (0 - 1)) • v t,
    fun t => (κ * L * (0 - 1)) • v t, fun t => (-Real.log β) • one +
      φπ • (κ * L * (0 - 1)) • v t + φy • ((1 - β * ρ) * L * (0 - 1)) • v t + v t)
    ⟨hsol, ha1, ha2, hia', hb1, hb2, hib'⟩
  have hz := e1.trans e2.symm
  have hx : x = fun t => ((1 - β * ρ) * L * (0 - 1)) • v t := congrArg (fun z => z.1) hz
  have hp : pi = fun t => (κ * L * (0 - 1)) • v t := congrArg (fun z => z.2.1) hz
  have hi : i = fun t => (-Real.log β) • one + φπ • (κ * L * (0 - 1)) • v t +
      φy • ((1 - β * ρ) * L * (0 - 1)) • v t + v t := congrArg (fun z => z.2.2) hz
  have hreal : ∀ t, i t - E.E t (pi (t + 1)) =
      (-Real.log β) • one + (γ * (1 - ρ) * (1 - β * ρ) * L) • v t := fun t => by
    rw [hi, hp]
    simp only [map_smul, hv t]
    rw [hLdef, nk_irfLam]
    match_scalars
    · rfl
    · field_simp
      ring
  refine ⟨mul_pos hbr hL, mul_pos hκ hL, by
    have : (0 : ℝ) < 1 - ρ := by linarith
    positivity, by positivity, fun t => ?_, fun t => ?_, hreal, fun t => ?_⟩
  · rw [hx, ← neg_smul]
    ring_nf
  · rw [hp, ← neg_smul]
    ring_nf
  · rw [hreal t, hi, hLdef, nk_irfLam]
    match_scalars
    · rfl
    · field_simp
      ring

/-- **Figure 19.2** (Miao, p. 628), qualitatively: an AR(1) shock to the natural rate
(`r^n_t = −ln β + r̂^n_t`, `E_tr̂^n_{t+1} = ρr̂^n_t`, `0 ≤ ρ < 1`, `v = 0`). Under (19.31) with
`κ, γ > 0`, `0 < β < 1`, `φ_π, φ_y ≥ 0`, every stable equilibrium has
`x_t = ((1 − βρ)Λ)r̂^n_t`, `π_t = (κΛ)r̂^n_t` (both rise after a positive shock), the real rate
`i_t − E_tπ_{t+1} = −ln β + kr̂^n_t` with `0 < k < 1` (it rises by less than one percent), and
the nominal rate is the real rate plus `(ρκΛ)r̂^n_t`, so its response `k + ρκΛ` is positive. -/
theorem nk_fig_19_2 [CompleteSpace V] (E : CondExpSystem ℝ V) {β γ κ φπ φy ρ : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (h31 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    (hone0 : one ≠ 0) (hone : ∀ t, E.E t one = one) {r : ℕ → V} (hrb : sre_IsBounded r)
    (hra : sre_IsAdapted E r) (hr : ∀ t, E.E t (r (t + 1)) = ρ • r t)
    {x pi i : ℕ → V} (hsys : nk_dnkSystem E β γ κ φπ φy one (fun _ => 0)
      (fun t => (-Real.log β) • one + r t) x pi i) (hxa : sre_IsAdapted E x)
    (hpa : sre_IsAdapted E pi) (hia : sre_IsAdapted E i)
    (hxb : sre_IsBounded x) (hpb : sre_IsBounded pi) (hib : sre_IsBounded i) :
    0 < (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ ∧ 0 < κ * nk_irfLam β γ κ φπ φy ρ ∧
    0 < 1 - γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ ∧
    1 - γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ < 1 ∧
    0 ≤ ρ * κ * nk_irfLam β γ κ φπ φy ρ ∧
    (∀ t, x t = ((1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ) • r t) ∧
    (∀ t, pi t = (κ * nk_irfLam β γ κ φπ φy ρ) • r t) ∧
    (∀ t, i t - E.E t (pi (t + 1)) = (-Real.log β) • one +
      (1 - γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ) • r t) ∧
    (∀ t, i t = (i t - E.E t (pi (t + 1))) + (ρ * κ * nk_irfLam β γ κ φπ φy ρ) • r t) := by
  obtain ⟨hden, hL, hlt⟩ := nk_irfLam_pos hκ hβ0 hβ1 hγ hφy hρ1 h31
  set L := nk_irfLam β γ κ φπ φy ρ with hLdef
  have hbr : 0 < 1 - β * ρ := by nlinarith
  have hsol := nk_irf_solves E (one := one) (a := 0) (c := 1) hγ.ne' hden.ne' hr
  have hdet := (ex_19_1 E hκ hβ0 hβ1 hγ hφπ hφy hone0 hone).2 h31
  obtain ⟨Mr, hMr⟩ := hrb
  have hsmul : ∀ (k : ℝ), sre_IsBounded (fun t => k • r t) ∧ sre_IsAdapted E (fun t => k • r t) :=
    fun k => ⟨⟨|k| * Mr, fun t => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hMr t) (abs_nonneg _)⟩, fun t => by simp [hra t]⟩
  obtain ⟨z, -, hzu⟩ := hdet (fun _ => 0) (fun t => (-Real.log β) • one + r t)
    ⟨0, fun _ => by simp⟩ ⟨‖(-Real.log β) • one‖ + Mr, fun t => (norm_add_le _ _).trans
      (add_le_add le_rfl (hMr t))⟩ (fun _ => map_zero _)
    (fun t => by simp [hone, hra t])
  have hv0 : (fun t => (0 : ℝ) • r t) = fun _ => (0 : V) := funext fun t => zero_smul _ _
  have hrn1 : (fun t => (-Real.log β) • one + (1 : ℝ) • r t) =
      fun t => (-Real.log β) • one + r t := funext fun t => by rw [one_smul]
  rw [hv0, hrn1] at hsol
  obtain ⟨hb1, ha1⟩ := hsmul ((1 - β * ρ) * L * (1 - 0))
  obtain ⟨hb2, ha2⟩ := hsmul (κ * L * (1 - 0))
  obtain ⟨hia', hib'⟩ := nk_rule_regular E (β := β) (φπ := φπ) (φy := φy) (v := fun _ => 0)
    hone hb1 hb2 ⟨0, fun _ => by simp⟩ ha1 ha2 (fun _ => map_zero _)
  simp only [zero_smul, ← hLdef] at hsol
  have e1 := hzu (x, pi, i) ⟨hsys, hxa, hpa, hia, hxb, hpb, hib⟩
  have e2 := hzu (fun t => ((1 - β * ρ) * L * (1 - 0)) • r t,
    fun t => (κ * L * (1 - 0)) • r t, fun t => (-Real.log β) • one +
      φπ • (κ * L * (1 - 0)) • r t + φy • ((1 - β * ρ) * L * (1 - 0)) • r t + 0)
    ⟨hsol, ha1, ha2, hia', hb1, hb2, hib'⟩
  have hz := e1.trans e2.symm
  have hx : x = fun t => ((1 - β * ρ) * L * (1 - 0)) • r t := congrArg (fun z => z.1) hz
  have hp : pi = fun t => (κ * L * (1 - 0)) • r t := congrArg (fun z => z.2.1) hz
  have hi : i = fun t => (-Real.log β) • one + φπ • (κ * L * (1 - 0)) • r t +
      φy • ((1 - β * ρ) * L * (1 - 0)) • r t + 0 := congrArg (fun z => z.2.2) hz
  have hreal : ∀ t, i t - E.E t (pi (t + 1)) =
      (-Real.log β) • one + (1 - γ * (1 - ρ) * (1 - β * ρ) * L) • r t := fun t => by
    rw [hi, hp]
    simp only [map_smul, hr t]
    rw [hLdef, nk_irfLam]
    match_scalars
    · rfl
    · field_simp
      ring
  have hk : 0 < 1 - γ * (1 - ρ) * (1 - β * ρ) * L := by linarith
  refine ⟨mul_pos hbr hL, mul_pos hκ hL, hk, by
    have : (0 : ℝ) < 1 - ρ := by linarith
    have : 0 < γ * (1 - ρ) * (1 - β * ρ) * L := by positivity
    linarith, by positivity, fun t => ?_, fun t => ?_, hreal, fun t => ?_⟩
  · rw [hx]
    ring_nf
  · rw [hp]
    ring_nf
  · rw [hreal t, hi, hLdef, nk_irfLam]
    match_scalars
    · rfl
    · field_simp
      ring

end Miao.NewKeynesian
