/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.EUPhelps
import InfiniteHorizonDP.POStochasticGrowth
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exercise 7.5: stochastic log growth with a Markov productivity shock

Miao, §7.6, Exercise 5, p. 229: `max E Σ βᵗ ln C_t` subject to `C_t + K_{t+1} = z_t K_t^α`,
`K₀` given, `z_t` a positive Markov process. We use the Euler-equation approach of §7.5 in the
Euler class (`eu_EulerModel`, the setting of `EUPhelps`): on a filtered probability space the
shock process `z` is positive and adapted, the state is capital `K` (`Fin 1 → ℝ`), the choice is
`K′ ∈ Γ(K, z) = [0, zK^α)` and the reward is `u(K, z, K′) = ln(zK^α − K′)` (`ex7_lgModel`).

* `ex7_lgK`: the capital stock under the policy **`K_{t+1} = αβ z_t K_t^α`** (consumption
  `C_t = (1 − αβ) z_t K_t^α`).
* `ex7_lg_fderiv`, `ex7_lg_derivs`: `u_x = αzK^{α−1}/C`, `u_a = −1/C`.
* `ex7_lg_euler`: the Euler equation (7.34) `−1/C_t + β E_t[αz_{t+1}K_{t+1}^{α−1}/C_{t+1}] = 0`
  holds; the conditional expectation is of the `ℱ_t`-measurable `α/((1 − αβ)K_{t+1})`, so **no
  property of the Markov kernel `Q` is used** (only the integrability of `1/K_{t+1}`).
* `ex7_lg_tvc`: (7.35), `βᵀ E[u_a · K_{T+1}] = −βᵀ αβ/(1 − αβ) → 0`.
* **Exercise 7.5, optimality** (`ex_7_5`): by the sufficiency argument of Theorem 7.5.2
  (`eu_euler_sufficient`, with concavity of `ln(zK^α − K′)` on the graph of `Γ`), every feasible
  plan with the integrability `EulerInt` does at most as well, up to `w_T → 0`.
* **Exercise 7.5, the value function** (`ex_7_5_value`): if `ln z_t` is integrable with
  `e_t = E ln z_t` and `Σ βᵗ|e_t| < ∞`, the partial sums converge to
  `V(K₀) = (α/(1 − αβ)) ln K₀ + (ln(1 − αβ) + (αβ/(1 − αβ)) ln(αβ))/(1 − β) +
  (1/(1 − αβ)) Σ βᵗ e_t` (`ex7_lgV`). With `z` Markov with kernel `Q` from `z₀`,
  `e_t = ∫ ln z Q^t(z₀, dz)`, so `V(K₀, z₀)` depends on `z₀` through these expectations.
  `ex7_lg_bounded`: `sup_t |e_t| < ∞` suffices for the summability.
* `ex_7_5_limit` (relation to Exercise 6.2): the finite-horizon policy
  `K_{t+1} = θ_{T−t} z_t K_t^α` has `θ_n → αβ`, the infinite-horizon policy.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

/-- **The stochastic log growth model in the Euler class** (Miao, Exercise 7.5, p. 229). -/
noncomputable def ex7_lgModel (α β : ℝ) : eu_EulerModel 1 ℝ where
  X := {K | 0 ≤ K 0}
  Q := 0
  Γ := fun K z => {K' | 0 ≤ K' 0 ∧ K' 0 < z * K 0 ^ α}
  u := fun K z K' => Real.log (z * K 0 ^ α - K' 0)
  β := β

/-- The capital stock under the policy `K_{t+1} = αβ z_t K_t^α`. -/
noncomputable def ex7_lgK {Ω : Type*} (z : ℕ → Ω → ℝ) (α β K₀ : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => K₀
  | t + 1 => fun ω => α * β * z t ω * ex7_lgK z α β K₀ t ω ^ α

/-- The policy plan as an Euler-class plan. -/
noncomputable def ex7_lgState {Ω : Type*} (z : ℕ → Ω → ℝ) (α β K₀ : ℝ) :
    ℕ → Ω → (Fin 1 → ℝ) := fun t ω _ => ex7_lgK z α β K₀ t ω

/-- The derivative of the reward at a point with `K > 0` and consumption `c = zK^α − K′ > 0`:
`Du(v) = (αzK^{α−1}v₁ − v₂)/c`. -/
theorem ex7_lg_fderiv {α β z : ℝ} {p : (Fin 1 → ℝ) × (Fin 1 → ℝ)} (hK : 0 < p.1 0)
    (hc : 0 < z * p.1 0 ^ α - p.2 0) :
    DifferentiableAt ℝ ((ex7_lgModel α β).uu z) p ∧
      ∀ v, fderiv ℝ ((ex7_lgModel α β).uu z) p v =
        (z * (α * p.1 0 ^ (α - 1)) * v.1 0 - v.2 0) / (z * p.1 0 ^ α - p.2 0) := by
  have h1 : DifferentiableAt ℝ (fun q : (Fin 1 → ℝ) × (Fin 1 → ℝ) => q.1 0) p := by fun_prop
  have h2 : DifferentiableAt ℝ (fun q : (Fin 1 → ℝ) × (Fin 1 → ℝ) => q.1 0 ^ α) p := by
    have := (Real.hasDerivAt_rpow_const (x := p.1 0) (p := α)
      (Or.inl hK.ne')).differentiableAt.comp p h1
    exact this
  have hg : DifferentiableAt ℝ (fun q : (Fin 1 → ℝ) × (Fin 1 → ℝ) => z * q.1 0 ^ α - q.2 0) p :=
    (h2.const_mul z).sub (by fun_prop)
  have hd : DifferentiableAt ℝ ((ex7_lgModel α β).uu z) p := by
    have := (Real.hasDerivAt_log (x := z * p.1 0 ^ α - p.2 0) hc.ne').differentiableAt.comp p hg
    exact this
  refine ⟨hd, fun v => ?_⟩
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hd' : HasFDerivAt ((ex7_lgModel α β).uu z) (fderiv ℝ ((ex7_lgModel α β).uu z) p)
      (p + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
  have h1' := hd'.comp_hasDerivAt (0 : ℝ) hline
  have hK1 : HasDerivAt (fun s : ℝ => p.1 0 + s * v.1 0) (v.1 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.1 0)).const_add (p.1 0)
  have hK2 : HasDerivAt (fun s : ℝ => p.2 0 + s * v.2 0) (v.2 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.2 0)).const_add (p.2 0)
  have hpow := hK1.rpow_const (p := α) (Or.inl (by simpa using hK.ne'))
  have hin : HasDerivAt (fun s : ℝ => z * (p.1 0 + s * v.1 0) ^ α - (p.2 0 + s * v.2 0))
      (z * (v.1 0 * α * (p.1 0 + 0 * v.1 0) ^ (α - 1)) - v.2 0) 0 :=
    (hpow.const_mul z).sub hK2
  have hc' : 0 < z * (p.1 0 + 0 * v.1 0) ^ α - (p.2 0 + 0 * v.2 0) := by simpa using hc
  have h2' := (Real.hasDerivAt_log hc'.ne').comp (0 : ℝ) hin
  have e : (fun s : ℝ => (ex7_lgModel α β).uu z (p + s • v)) =
      fun s => Real.log (z * (p.1 0 + s * v.1 0) ^ α - (p.2 0 + s * v.2 0)) := by
    funext s
    simp only [eu_EulerModel.uu, ex7_lgModel, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1'' : HasDerivAt (fun s : ℝ => (ex7_lgModel α β).uu z (p + s • v))
      (fderiv ℝ ((ex7_lgModel α β).uu z) p v) 0 := h1'
  rw [e] at h1''
  rw [h1''.unique h2']
  simp only [zero_mul, add_zero]
  field_simp

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℕ m0}

theorem ex7_lgK_pos {z : ℕ → Ω → ℝ} {α β K₀ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hz : ∀ t ω, 0 < z t ω) (hK₀ : 0 < K₀) (t : ℕ) (ω : Ω) : 0 < ex7_lgK z α β K₀ t ω := by
  induction t with
  | zero => exact hK₀
  | succ t ih => exact mul_pos (mul_pos (mul_pos hα hβ) (hz t ω)) (Real.rpow_pos_of_pos ih _)

/-- `K_{t+1}` is `ℱ_t`-measurable. -/
theorem ex7_lgK_measurable {z : ℕ → Ω → ℝ} {α β K₀ : ℝ} (hzm : ∀ t, Measurable[ℱ t] (z t))
    (t : ℕ) : Measurable[ℱ t] (ex7_lgK z α β K₀ (t + 1)) := by
  induction t with
  | zero =>
    change Measurable[ℱ 0] fun ω => α * β * z 0 ω * K₀ ^ α
    exact ((hzm 0).const_mul _).mul measurable_const
  | succ t ih =>
    exact ((hzm (t + 1)).const_mul _).mul
      ((ih.mono (ℱ.mono (Nat.le_succ t)) le_rfl).pow_const _)

/-- The derivatives along the policy plan: consumption is `C_t = (1 − αβ) z_t K_t^α > 0`,
`u_a = −1/C_t`, `u_x = αz_tK_t^{α−1}/C_t`. -/
theorem ex7_lg_derivs {z : ℕ → Ω → ℝ} {α β K₀ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α * β < 1) (hz : ∀ t ω, 0 < z t ω) (hK₀ : 0 < K₀) (t : ℕ) (ω : Ω) :
    z t ω * ex7_lgState z α β K₀ t ω 0 ^ α - ex7_lgState z α β K₀ (t + 1) ω 0 =
        (1 - α * β) * (z t ω * ex7_lgK z α β K₀ t ω ^ α) ∧
      DifferentiableAt ℝ ((ex7_lgModel α β).uu (z t ω))
        (ex7_lgState z α β K₀ t ω, ex7_lgState z α β K₀ (t + 1) ω) ∧
      (ex7_lgModel α β).ua (ex7_lgState z α β K₀ t ω) (z t ω)
        (ex7_lgState z α β K₀ (t + 1) ω) 0 =
        -1 / ((1 - α * β) * (z t ω * ex7_lgK z α β K₀ t ω ^ α)) ∧
      (ex7_lgModel α β).ux (ex7_lgState z α β K₀ t ω) (z t ω)
        (ex7_lgState z α β K₀ (t + 1) ω) 0 =
        α / ((1 - α * β) * ex7_lgK z α β K₀ t ω) := by
  have hK := ex7_lgK_pos hα hβ hz hK₀ t ω
  have hy : 0 < z t ω * ex7_lgK z α β K₀ t ω ^ α := mul_pos (hz t ω) (Real.rpow_pos_of_pos hK _)
  have hcons : z t ω * ex7_lgState z α β K₀ t ω 0 ^ α - ex7_lgState z α β K₀ (t + 1) ω 0 =
      (1 - α * β) * (z t ω * ex7_lgK z α β K₀ t ω ^ α) := by
    simp only [ex7_lgState, ex7_lgK]; ring
  have h1 : 0 < 1 - α * β := by linarith
  have hf := ex7_lg_fderiv (α := α) (β := β) (z := z t ω)
    (p := (ex7_lgState z α β K₀ t ω, ex7_lgState z α β K₀ (t + 1) ω)) hK
    (by rw [hcons]; positivity)
  refine ⟨hcons, hf.1, ?_, ?_⟩
  · simp only [eu_EulerModel.ua]
    rw [hf.2, hcons]
    simp
  · simp only [eu_EulerModel.ux]
    rw [hf.2, hcons]
    simp only [Pi.single_eq_same, mul_one, Pi.zero_apply, sub_zero]
    simp only [ex7_lgState]
    have hKα : ex7_lgK z α β K₀ t ω ^ (α - 1) = ex7_lgK z α β K₀ t ω ^ α /
        ex7_lgK z α β K₀ t ω := by
      rw [Real.rpow_sub hK, Real.rpow_one]
    rw [hKα]
    have := (hz t ω).ne'
    have := (Real.rpow_pos_of_pos hK α).ne'
    field_simp

/-- **Exercise 7.5, the Euler equation** (Miao, p. 229): along the policy
`K_{t+1} = αβz_tK_t^α`, `u_a(t) + β E_t[u_x(t + 1)] = 0` almost surely, given that `1/K_{t+1}`
is integrable. -/
theorem ex7_lg_euler [IsProbabilityMeasure P] {z : ℕ → Ω → ℝ} {α β K₀ : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hαβ : α * β < 1) (hz : ∀ t ω, 0 < z t ω) (hzm : ∀ t, Measurable[ℱ t] (z t))
    (hK₀ : 0 < K₀) (hI : ∀ t, Integrable (fun ω => (ex7_lgK z α β K₀ (t + 1) ω)⁻¹) P) :
    (ex7_lgModel α β).IsEuler P ℱ z (ex7_lgState z α β K₀) := by
  intro t i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  have hux : (fun ω' => (ex7_lgModel α β).ux (ex7_lgState z α β K₀ (t + 1) ω') (z (t + 1) ω')
      (ex7_lgState z α β K₀ (t + 2) ω') 0) =
      fun ω' => α / (1 - α * β) * (ex7_lgK z α β K₀ (t + 1) ω')⁻¹ := by
    funext ω'
    rw [(ex7_lg_derivs hα hβ hαβ hz hK₀ (t + 1) ω').2.2.2]
    have := (ex7_lgK_pos hα hβ hz hK₀ (t + 1) ω').ne'
    have : 1 - α * β ≠ 0 := by linarith
    field_simp
  have hm : StronglyMeasurable[ℱ t]
      fun ω' => α / (1 - α * β) * (ex7_lgK z α β K₀ (t + 1) ω')⁻¹ :=
    ((ex7_lgK_measurable hzm t).inv.const_mul _).stronglyMeasurable
  rw [hux, condExp_of_stronglyMeasurable (ℱ.le t) hm ((hI t).const_mul _)]
  refine Eventually.of_forall fun ω => ?_
  dsimp only
  rw [(ex7_lg_derivs hα hβ hαβ hz hK₀ t ω).2.2.1]
  simp only [Pi.zero_apply]
  have hK := ex7_lgK_pos hα hβ hz hK₀ t ω
  have h1 : 0 < 1 - α * β := by linarith
  have e : ex7_lgK z α β K₀ (t + 1) ω = α * β * (z t ω * ex7_lgK z α β K₀ t ω ^ α) := by
    simp only [ex7_lgK]; ring
  rw [e]
  change -1 / ((1 - α * β) * (z t ω * ex7_lgK z α β K₀ t ω ^ α)) +
    β * (α / (1 - α * β) * (α * β * (z t ω * ex7_lgK z α β K₀ t ω ^ α))⁻¹) = 0
  have := (hz t ω).ne'
  have := (Real.rpow_pos_of_pos hK α).ne'
  have := h1.ne'
  field_simp
  ring

/-- **Exercise 7.5, the transversality condition (7.35)**: along the policy,
`βᵀ E[u_a(T) · K_{T+1}] = −βᵀ αβ/(1 − αβ) → 0`. -/
theorem ex7_lg_tvc [IsProbabilityMeasure P] {z : ℕ → Ω → ℝ} {α β K₀ : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hβ1 : β < 1) (hαβ : α * β < 1) (hz : ∀ t ω, 0 < z t ω) (hK₀ : 0 < K₀) :
    (ex7_lgModel α β).TVC735 P z (ex7_lgState z α β K₀) := by
  have hpt : ∀ T ω, eu_dot ((ex7_lgModel α β).ua (ex7_lgState z α β K₀ T ω) (z T ω)
      (ex7_lgState z α β K₀ (T + 1) ω)) (ex7_lgState z α β K₀ (T + 1) ω) =
      -(α * β / (1 - α * β)) := fun T ω => by
    simp only [eu_dot, Fin.sum_univ_one, (ex7_lg_derivs hα hβ hαβ hz hK₀ T ω).2.2.1]
    have hK := ex7_lgK_pos hα hβ hz hK₀ T ω
    have := (hz T ω).ne'
    have := (Real.rpow_pos_of_pos hK α).ne'
    have : 1 - α * β ≠ 0 := by linarith
    simp only [ex7_lgState, ex7_lgK]
    field_simp
  unfold eu_EulerModel.TVC735
  simp only [hpt, integral_const, probReal_univ, one_smul]
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const (-(α * β / (1 - α * β)))
  rw [zero_mul] at this
  exact this

/-- `ln(zK^α − K′)` is concave on the graph `{K ≥ 0, 0 ≤ K′ < zK^α}` (`z > 0`, `0 ≤ α ≤ 1`). -/
theorem ex7_lg_concave {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (z : ℝ) :
    ConcaveOn ℝ {p : (Fin 1 → ℝ) × (Fin 1 → ℝ) | 0 < z ∧ 0 ≤ p.1 0 ∧ 0 ≤ p.2 0 ∧
      p.2 0 < z * p.1 0 ^ α} ((ex7_lgModel α β).uu z) := by
  have hpow := Real.concaveOn_rpow hα0 hα1
  have hpos : ∀ a b X Y : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → 0 < X → 0 < Y → 0 < a * X + b * Y :=
    fun a b X Y ha hb hab hX hY => by
      rcases ha.eq_or_lt with h | h
      · subst h; simp only [zero_add] at hab; subst hab; simpa using hY
      · nlinarith [mul_nonneg hb hY.le]
  -- the key inequality `a g(p) + b g(q) ≤ g(ap + bq)`
  have hg : ∀ p q : (Fin 1 → ℝ) × (Fin 1 → ℝ), 0 < z → 0 ≤ p.1 0 → 0 ≤ q.1 0 →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a * (z * p.1 0 ^ α - p.2 0) + b * (z * q.1 0 ^ α - q.2 0) ≤
        z * (a * p.1 0 + b * q.1 0) ^ α - (a * p.2 0 + b * q.2 0) := by
    intro p q hz hp hq a b ha hb hab
    have := hpow.2 (Set.mem_Ici.2 hp) (Set.mem_Ici.2 hq) ha hb hab
    simp only [smul_eq_mul] at this
    nlinarith [mul_le_mul_of_nonneg_left this hz.le]
  refine ⟨?_, fun p hp q hq a b ha hb hab => ?_⟩
  · intro p hp q hq a b ha hb hab
    obtain ⟨hz, hp1, hp2, hp3⟩ := hp
    obtain ⟨-, hq1, hq2, hq3⟩ := hq
    change 0 < z ∧ 0 ≤ (a • p + b • q).1 0 ∧ 0 ≤ (a • p + b • q).2 0 ∧
      (a • p + b • q).2 0 < z * (a • p + b • q).1 0 ^ α
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine ⟨hz, by positivity, by positivity, ?_⟩
    have h1 := hg p q hz hp1 hq1 a b ha hb hab
    have h2 := hpos a b _ _ ha hb hab (sub_pos.2 hp3) (sub_pos.2 hq3)
    linarith
  · obtain ⟨hz, hp1, hp2, hp3⟩ := hp
    obtain ⟨-, hq1, hq2, hq3⟩ := hq
    have hcp : 0 < z * p.1 0 ^ α - p.2 0 := sub_pos.2 hp3
    have hcq : 0 < z * q.1 0 ^ α - q.2 0 := sub_pos.2 hq3
    have hlog := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hcp)
      (Set.mem_Ioi.2 hcq) ha hb hab
    simp only [smul_eq_mul] at hlog
    simp only [eu_EulerModel.uu, ex7_lgModel, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine hlog.trans (Real.log_le_log (hpos a b _ _ ha hb hab hcp hcq) ?_)
    exact hg p q hz hp1 hq1 a b ha hb hab

/-- **Exercise 7.5, optimality** (Miao, p. 229): for `0 < α, β < 1`, a positive adapted shock
process `z` and `K₀ > 0`, the policy `K_{t+1} = αβz_tK_t^α` (consumption
`C_t = (1 − αβ)z_tK_t^α`) is a feasible plan satisfying the Euler equation and (7.35), and by the
sufficiency argument of Theorem 7.5.2 every feasible plan `x` with the integrability `EulerInt`
has `S_T(x) ≤ S_T(K*) + w_T` with `w_T → 0`. -/
theorem ex_7_5 [IsProbabilityMeasure P] {z : ℕ → Ω → ℝ} {α β K₀ : ℝ} (hp : po61_Params α β)
    (hz : ∀ t ω, 0 < z t ω) (hzm : ∀ t, Measurable[ℱ t] (z t)) (hK₀ : 0 < K₀)
    (hI : ∀ t, Integrable (fun ω => (ex7_lgK z α β K₀ (t + 1) ω)⁻¹) P)
    {x : ℕ → Ω → (Fin 1 → ℝ)} (hx : (ex7_lgModel α β).IsPlan ℱ z (fun _ => K₀) x)
    (hint : eu_EulerModel.EulerInt P z (ex7_lgModel α β) (ex7_lgState z α β K₀) x) :
    (ex7_lgModel α β).IsPlan ℱ z (fun _ => K₀) (ex7_lgState z α β K₀) ∧
      (ex7_lgModel α β).IsEuler P ℱ z (ex7_lgState z α β K₀) ∧
      (ex7_lgModel α β).TVC735 P z (ex7_lgState z α β K₀) ∧
      ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 0) ∧
        ∀ T, (ex7_lgModel α β).eu_partialJ P z x T ≤
          (ex7_lgModel α β).eu_partialJ P z (ex7_lgState z α β K₀) T + w T := by
  have hα := hp.α_pos
  have hβ := hp.β_pos
  have hαβ := hp.p_lt
  have hD := fun t ω => ex7_lg_derivs hα hβ hαβ hz hK₀ t ω
  have hKp := fun t ω => ex7_lgK_pos hα hβ hz hK₀ t ω
  have h1 : 0 < 1 - α * β := by linarith
  have hplan : (ex7_lgModel α β).IsPlan ℱ z (fun _ => K₀) (ex7_lgState z α β K₀) := by
    refine ⟨fun ω => rfl, fun t => ?_, fun t ω => ⟨(hKp t ω).le, (hKp (t + 1) ω).le, ?_⟩⟩
    · change Measurable[ℱ t] fun ω (_ : Fin 1) => ex7_lgK z α β K₀ (t + 1) ω
      exact (continuous_pi fun _ => continuous_id).measurable.comp (ex7_lgK_measurable hzm t)
    · have := (hD t ω).1
      have : 0 < (1 - α * β) * (z t ω * ex7_lgK z α β K₀ t ω ^ α) :=
        mul_pos h1 (mul_pos (hz t ω) (Real.rpow_pos_of_pos (hKp t ω) _))
      change ex7_lgK z α β K₀ (t + 1) ω < z t ω * ex7_lgK z α β K₀ t ω ^ α
      simp only [ex7_lgState] at *
      linarith
  have heuler := ex7_lg_euler hα hβ hαβ hz hzm hK₀ hI
  have htvc := ex7_lg_tvc (P := P) hα hβ hp.β_lt hαβ hz hK₀
  refine ⟨hplan, heuler, htvc, eu_EulerModel.eu_euler_sufficient hβ.le hplan hx
    (fun z' => {p | 0 < z' ∧ 0 ≤ p.1 0 ∧ 0 ≤ p.2 0 ∧ p.2 0 < z' * p.1 0 ^ α})
    (fun z' => ex7_lg_concave hα.le hp.α_lt.le z') (fun t ω => ⟨?_, ?_⟩)
    (fun t ω => (hD t ω).2.1) heuler (fun t ω i => ?_) (fun t ω i => ?_) hint htvc⟩
  · exact ⟨hz t ω, (hplan.2.2 t ω).1, (hplan.2.2 t ω).2⟩
  · exact ⟨hz t ω, (hx.2.2 t ω).1, (hx.2.2 t ω).2⟩
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [(hD (t + 1) ω).2.2.2]
    exact (div_pos hα (mul_pos h1 (hKp _ ω))).le
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    exact (hx.2.2 t ω).2.1

/-! ### The value function -/

/-- The value of Exercise 7.5 with `e_t = E ln z_t`:
`(α/(1 − αβ)) ln K₀ + (ln(1 − αβ) + (αβ/(1 − αβ)) ln(αβ))/(1 − β) + (1/(1 − αβ)) Σ βᵗ e_t`. -/
noncomputable def ex7_lgV (α β K₀ : ℝ) (e : ℕ → ℝ) : ℝ :=
  α / (1 - α * β) * Real.log K₀ +
    (Real.log (1 - α * β) + α * β / (1 - α * β) * Real.log (α * β)) / (1 - β) +
      1 / (1 - α * β) * ∑' t, β ^ t * e t

/-- If `G_{T+1} = ρG_T + c_T` with `0 ≤ ρ < 1` and `Σ|c_T| < ∞`, then `Σ|G_T| < ∞`. -/
theorem ex7_rec_summable {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {G c : ℕ → ℝ}
    (hrec : ∀ T, G (T + 1) = ρ * G T + c T) (hc : Summable fun T => |c T|) :
    Summable fun T => |G T| := by
  set C := ∑' T, |c T|
  set K := (|G 0| + C) / (1 - ρ)
  have h1ρ : 0 < 1 - ρ := by linarith
  have hcN : ∀ N, ∑ T ∈ Finset.range N, |c T| ≤ C := fun N =>
    hc.sum_le_tsum _ fun T _ => abs_nonneg _
  have key : ∀ N, ∑ T ∈ Finset.range N, |G T| ≤ K := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, K]; positivity
    | succ N ih =>
      rw [Finset.sum_range_succ']
      have hstep : ∑ T ∈ Finset.range N, |G (T + 1)| ≤
          ρ * ∑ T ∈ Finset.range N, |G T| + ∑ T ∈ Finset.range N, |c T| := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun T _ => ?_
        rw [hrec T]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hρ0]
      have hK : K * (1 - ρ) = |G 0| + C := by simp only [K]; field_simp
      nlinarith [hcN N, mul_le_mul_of_nonneg_left ih hρ0]
  exact summable_of_sum_range_le (fun T => abs_nonneg _) key

/-- **Exercise 7.5, the value function** (Miao, p. 229): if `ln z_t` is integrable,
`e_t = E ln z_t` and `Σ βᵗ|e_t| < ∞`, the rewards along the policy are integrable and the
partial sums `S_T = Σ_{t ≤ T} βᵗ E ln C_t` converge to `ex7_lgV α β K₀ e`. -/
theorem ex_7_5_value [IsProbabilityMeasure P] {z : ℕ → Ω → ℝ} {α β K₀ : ℝ}
    (hp : po61_Params α β) (hz : ∀ t ω, 0 < z t ω) (hK₀ : 0 < K₀)
    (hzI : ∀ t, Integrable (fun ω => Real.log (z t ω)) P)
    (hsum : Summable fun t => β ^ t * |∫ ω, Real.log (z t ω) ∂P|) :
    (∀ t, Integrable (fun ω => (ex7_lgModel α β).u (ex7_lgState z α β K₀ t ω) (z t ω)
      (ex7_lgState z α β K₀ (t + 1) ω)) P) ∧
    Tendsto ((ex7_lgModel α β).eu_partialJ P z (ex7_lgState z α β K₀)) atTop
      (𝓝 (ex7_lgV α β K₀ fun t => ∫ ω, Real.log (z t ω) ∂P)) := by
  have hα := hp.α_pos
  have hβ := hp.β_pos
  have hβ1 := hp.β_lt
  have hαβ := hp.p_lt
  have hαβ0 := hp.p_pos
  have h1 : 0 < 1 - α * β := by linarith
  set e : ℕ → ℝ := fun t => ∫ ω, Real.log (z t ω) ∂P
  set a := Real.log (α * β)
  set b := Real.log (1 - α * β)
  set k : ℕ → Ω → ℝ := fun t ω => Real.log (ex7_lgK z α β K₀ t ω)
  have hKp := fun t ω => ex7_lgK_pos hα hβ hz hK₀ t ω
  -- the pathwise laws of motion
  have hk : ∀ t ω, k (t + 1) ω = a + Real.log (z t ω) + α * k t ω := fun t ω => by
    simp only [k, ex7_lgK, a]
    rw [Real.log_mul (mul_pos (mul_pos hα hβ) (hz t ω)).ne' (Real.rpow_pos_of_pos (hKp t ω) _).ne',
      Real.log_mul (mul_pos hα hβ).ne' (hz t ω).ne', Real.log_rpow (hKp t ω)]
  have hu : ∀ t ω, (ex7_lgModel α β).u (ex7_lgState z α β K₀ t ω) (z t ω)
      (ex7_lgState z α β K₀ (t + 1) ω) = b + Real.log (z t ω) + α * k t ω := fun t ω => by
    have hc := (ex7_lg_derivs hα hβ hp.p_lt hz hK₀ t ω).1
    change Real.log (z t ω * ex7_lgState z α β K₀ t ω 0 ^ α - ex7_lgState z α β K₀ (t + 1) ω 0)
      = _
    rw [hc, Real.log_mul h1.ne' (mul_pos (hz t ω) (Real.rpow_pos_of_pos (hKp t ω) _)).ne',
      Real.log_mul (hz t ω).ne' (Real.rpow_pos_of_pos (hKp t ω) _).ne', Real.log_rpow (hKp t ω)]
    change _ = Real.log (1 - α * β) + Real.log (z t ω) + α * Real.log (ex7_lgK z α β K₀ t ω)
    ring
  -- integrability of `ln K_t`
  have hkI : ∀ t, Integrable (k t) P := by
    intro t
    induction t with
    | zero => exact integrable_const (Real.log K₀)
    | succ t ih =>
      have : k (t + 1) = fun ω => a + Real.log (z t ω) + α * k t ω := funext (hk t)
      rw [this]
      exact ((integrable_const a).add (hzI t)).add (ih.const_mul α)
  have huI : ∀ t, Integrable (fun ω => (ex7_lgModel α β).u (ex7_lgState z α β K₀ t ω) (z t ω)
      (ex7_lgState z α β K₀ (t + 1) ω)) P := fun t => by
    simp only [hu]
    exact ((integrable_const b).add (hzI t)).add ((hkI t).const_mul α)
  refine ⟨huI, ?_⟩
  -- expectations
  set Ek : ℕ → ℝ := fun t => ∫ ω, k t ω ∂P
  have hEk : ∀ t, Ek (t + 1) = a + e t + α * Ek t := fun t => by
    have h1 : ∫ ω, k (t + 1) ω ∂P = ∫ ω, (a + Real.log (z t ω) + α * k t ω) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => hk t ω)
    change ∫ ω, k (t + 1) ω ∂P = a + ∫ ω, Real.log (z t ω) ∂P + α * ∫ ω, k t ω ∂P
    rw [h1, integral_add (f := fun ω => a + Real.log (z t ω)) (g := fun ω => α * k t ω)
      ((integrable_const a).add (hzI t)) ((hkI t).const_mul α),
      integral_add (f := fun _ => a) (g := fun ω => Real.log (z t ω)) (integrable_const a)
        (hzI t), integral_const, probReal_univ, one_smul,
      integral_const_mul]
  have hEu : ∀ t, ∫ ω, (ex7_lgModel α β).u (ex7_lgState z α β K₀ t ω) (z t ω)
      (ex7_lgState z α β K₀ (t + 1) ω) ∂P = b + e t + α * Ek t := fun t => by
    simp only [hu]
    rw [integral_add (f := fun ω => b + Real.log (z t ω)) (g := fun ω => α * k t ω)
      ((integrable_const b).add (hzI t)) ((hkI t).const_mul α),
      integral_add (f := fun _ => b) (g := fun ω => Real.log (z t ω)) (integrable_const b)
        (hzI t), integral_const, probReal_univ, one_smul,
      integral_const_mul]
  -- the telescoping with `Φ_t = B E ln K_t`, `B = α/(1 − αβ)`
  set B := α / (1 - α * β)
  set c0 := b + β * B * a
  have htel : ∀ t, β ^ t * (b + e t + α * Ek t) = β ^ t * (B * Ek t) -
      β ^ (t + 1) * (B * Ek (t + 1)) + β ^ t * c0 + 1 / (1 - α * β) * (β ^ t * e t) := by
    intro t
    rw [hEk t, pow_succ]
    simp only [B, c0]
    field_simp
    ring
  have hS : ∀ T, (ex7_lgModel α β).eu_partialJ P z (ex7_lgState z α β K₀) T =
      B * Ek 0 - β ^ (T + 1) * (B * Ek (T + 1)) +
        c0 * ∑ t ∈ Finset.range (T + 1), β ^ t +
          1 / (1 - α * β) * ∑ t ∈ Finset.range (T + 1), β ^ t * e t := fun T => by
    simp only [eu_EulerModel.eu_partialJ, hEu]
    change ∑ t ∈ Finset.range (T + 1), β ^ t * (b + e t + α * Ek t) = _
    simp only [htel]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_range_sub', ← Finset.mul_sum,
      ← Finset.sum_mul, pow_zero, one_mul]
    ring
  -- the limits
  have hEk0 : Ek 0 = Real.log K₀ := by simp [Ek, k, ex7_lgK]
  have hesum : Summable fun t => β ^ t * e t :=
    Summable.of_norm (hsum.congr fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ.le t)])
  have hG : Tendsto (fun T => β ^ T * Ek T) atTop (𝓝 0) := by
    have hrec : ∀ T, β ^ (T + 1) * Ek (T + 1) =
        α * β * (β ^ T * Ek T) + β ^ (T + 1) * (a + e T) := fun T => by
      rw [hEk T, pow_succ]; ring
    have hc : Summable fun T => |β ^ (T + 1) * (a + e T)| := by
      refine Summable.of_nonneg_of_le (fun T => abs_nonneg _) (fun T => ?_)
        (((summable_geometric_of_lt_one hβ.le hβ1).mul_left (β * |a|)).add (hsum.mul_left β))
      rw [abs_mul, abs_of_nonneg (pow_nonneg hβ.le _), pow_succ]
      have := abs_add_le a (e T)
      have hb := pow_nonneg hβ.le T
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hb hβ.le)]
    exact (ex7_rec_summable hαβ0.le hαβ hrec hc).of_abs.tendsto_atTop_zero
  have hlim1 : Tendsto (fun T => β ^ (T + 1) * (B * Ek (T + 1))) atTop (𝓝 0) := by
    have := (hG.comp (tendsto_add_atTop_nat 1)).const_mul B
    rw [mul_zero] at this
    exact this.congr fun T => by simp only [Function.comp_apply]; ring
  have hgeo : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), β ^ t) atTop (𝓝 (1 - β)⁻¹) :=
    ((hasSum_geometric_of_lt_one hβ.le hβ1).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hes : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), β ^ t * e t) atTop
      (𝓝 (∑' t, β ^ t * e t)) :=
    (hesum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hall := (((tendsto_const_nhds (x := B * Ek 0)).sub hlim1).add
    (hgeo.const_mul c0)).add (hes.const_mul (1 / (1 - α * β)))
  have hval : B * Ek 0 - 0 + c0 * (1 - β)⁻¹ + 1 / (1 - α * β) * ∑' t, β ^ t * e t =
      ex7_lgV α β K₀ e := by
    rw [hEk0]
    simp only [ex7_lgV, sub_zero, B, c0, a, b]
    have : 1 - β ≠ 0 := by linarith
    have : 1 - α * β ≠ 0 := h1.ne'
    field_simp
  rw [hval] at hall
  exact hall.congr fun T => (hS T).symm

/-- `sup_t |E ln z_t| < ∞` gives the summability in `ex_7_5_value`. -/
theorem ex7_lg_bounded {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {e : ℕ → ℝ} {L : ℝ}
    (he : ∀ t, |e t| ≤ L) : Summable fun t => β ^ t * |e t| :=
  Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ0 t) (abs_nonneg _))
    (fun t => mul_le_mul_of_nonneg_left (he t) (pow_nonneg hβ0 t))
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right L)

/-- **Exercise 7.5 and Exercise 6.2** (Miao, p. 229): the finite-horizon policy of Exercise 6.2,
`K_{t+1} = θ_{T−t} z_t K_t^α` with `θ_n = αβ(1 − (αβ)ⁿ)/(1 − (αβ)^{n+1})`, converges as the
horizon recedes, `θ_n → αβ`, to the infinite-horizon policy `K_{t+1} = αβ z_t K_t^α`. -/
theorem ex_7_5_limit {α β : ℝ} (hp : po61_Params α β) :
    Tendsto (po61_theta α β) atTop (𝓝 (α * β)) := by
  have hpn := tendsto_pow_atTop_nhds_zero_of_lt_one hp.p_pos.le hp.p_lt
  have h := ((hpn.const_sub 1).const_mul (α * β)).div
    ((hpn.comp (tendsto_add_atTop_nat 1)).const_sub 1)
    (by norm_num)
  simp only [sub_zero, mul_one, div_one] at h
  exact h.congr fun n => by simp only [po61_theta, Function.comp_apply, Pi.div_apply, pow_succ]

end Miao.InfiniteHorizonDP
