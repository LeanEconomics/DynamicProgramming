/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.OptimalPolicy
import MonetaryPolicyDesign.Ex4_6
import DiscretionCommitment.CommitmentVsDiscretion

/-!
# Monetary policy strategies

AKMM, §18.4.2–18.4.4, pp. 547–550.

* **The divine coincidence** (§18.4.2): a closed output gap at all dates forces zero inflation in
  every bounded equilibrium (`pol_divine_coincidence`, from Galí's `infl_zero_of_gap_zero` and
  `divine_coincidence`).
* **Cost-push shocks** (18.21): with `x ≡ 0`, bounded inflation solves
  `π_t = ∑_{k<K} β^k η_{t+k} + β^K π_{t+K}`; a one-period shock `η₀ ≠ 0` gives `π₀ = η₀ ≠ 0`
  (`pol_costpush_iterate`, `pol_costpush_breaks`).
* **Flexible inflation targeting** (18.22) with `π* = 0`, `λ = κ/ε` is the loss (18.20)
  (`pol_loss_22_eq_20`).
* **Price-level targeting** (§18.4.3): in the log-linear model with the rule
  `i_t = r^n_t + φ_P p̂_t` (the book's rule with `φ_x = 0` and the natural-rate intercept),
  every `φ_P > 0` gives a unique bounded equilibrium (Galí's Exercise 4.6, `pol_price_level_rule`).
* **Discretion** (§18.4.4): after a one-period cost-push shock, the economy is in steady state
  from date 1, `π₀ = κ x₀ + η₀`, and the date-0 problem gives `x₀ = −κη₀/(κ² + λ)`,
  `π₀ = λη₀/(κ² + λ)` (`pol_discretion_date0`); the price level jumps and stays
  (`pol_discretion_price_level`).
* **Commitment** (§18.4.4, Galí's perfect-foresight commitment path): inflation and the output gap
  are smaller in absolute value at date 0 than under discretion, inflation is negative and the gap
  negative afterwards, the price level returns to its initial value (`pol_commitment_path`,
  `pol_commitment_date0`, `pol_commitment_price_level`), commitment strictly beats discretion
  (`pol_commitment_better`), and it is time inconsistent: at date 1 the zero path is feasible with
  zero loss while the commitment continuation has a positive period loss
  (`pol_time_inconsistent`).
-/

namespace AKMM.NominalFrictions

open Filter Topology Finset

/-- **AKMM, §18.4.2, p. 547 (the divine coincidence)**: in Galí's log-linear model (NKPC (18.16)
with any expectation system), if the output gap is zero at every date and inflation is bounded,
inflation is zero at every date (`|β| < 1`); conversely zero inflation forces a zero gap, and then
the nominal rate equals the natural rate (Galí's `divine_coincidence`). -/
theorem pol_divine_coincidence {Ω : Type*} (𝔼 : Gali.MonetaryPolicyDesign.ExpectationSystem Ω)
    {β σ κ : ℝ} (hβ : |β| < 1) (hσ : σ ≠ 0) (hκ : κ ≠ 0) {rn ygap infl i : ℕ → Ω → ℝ}
    (heq : Gali.MonetaryPolicyDesign.OptimalPolicy.Equilibrium 𝔼 β σ κ rn ygap infl i)
    (hb : Gali.MonetaryPolicyDesign.BoundedProc infl) :
    (ygap = 0 ↔ infl = 0) ∧ (ygap = 0 → ∀ t, i t = rn t) :=
  Gali.MonetaryPolicyDesign.OptimalPolicy.divine_coincidence 𝔼 hβ hσ hκ heq hb

/-- AKMM, (18.21), p. 548 (perfect foresight): with `x ≡ 0`,
`π_t = κx_t + βπ_{t+1} + η_t` iterates to `π_t = ∑_{k<K} β^k η_{t+k} + β^K π_{t+K}`. -/
theorem pol_costpush_iterate {β : ℝ} {infl eta : ℕ → ℝ}
    (hpc : ∀ t, infl t = β * infl (t + 1) + eta t) (t K : ℕ) :
    infl t = ∑ k ∈ range K, β ^ k * eta (t + k) + β ^ K * infl (t + K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [ih, hpc (t + K), sum_range_succ, show t + K + 1 = t + (K + 1) by ring, pow_succ]
    ring

/-- **AKMM, (18.21), p. 548**: "a policy of setting `x_t = 0` at all dates no longer leads to
`π_t = 0`": with a one-period cost-push shock (`η_t = 0` for `t ≥ 1`), `|β| < 1` and bounded
inflation, `x ≡ 0` gives `π_t = 0` for `t ≥ 1` and `π₀ = η₀`, so `π₀ ≠ 0` when `η₀ ≠ 0`. -/
theorem pol_costpush_breaks {β M : ℝ} (hβ : |β| < 1) {infl eta : ℕ → ℝ}
    (hpc : ∀ t, infl t = β * infl (t + 1) + eta t) (heta : ∀ t, eta (t + 1) = 0)
    (hb : ∀ t, |infl t| ≤ M) : (∀ t, infl (t + 1) = 0) ∧ infl 0 = eta 0 := by
  have hz : ∀ t, infl (t + 1) = 0 := by
    intro t
    have hK : ∀ K, infl (t + 1) = β ^ K * infl (t + 1 + K) := by
      intro K
      rw [pol_costpush_iterate hpc (t + 1) K]
      simp [heta, show ∀ k, t + 1 + k = (t + k) + 1 from fun k => by ring]
    have hg2 : Tendsto (fun K : ℕ => |β| ^ K * M) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg β) hβ).mul_const M
    have hlim : Tendsto (fun K => β ^ K * infl (t + 1 + K)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun K => ?_) hg2
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb _) (pow_nonneg (abs_nonneg _) _)
    have he : (fun K => β ^ K * infl (t + 1 + K)) = fun _ => infl (t + 1) :=
      funext fun K => (hK K).symm
    rw [he] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  refine ⟨hz, ?_⟩
  rw [hpc 0, zero_add, hz 0, mul_zero, zero_add]

/-- AKMM, (18.22) and (18.20), p. 548: with `π* = 0` and `λ = κ/ε` the flexible
inflation-targeting loss is the welfare loss (18.20). -/
theorem pol_loss_22_eq_20 {κ ε πt xt πstar lam : ℝ} (hπ : πstar = 0) (hlam : lam = κ / ε) :
    (πt - πstar) ^ 2 + lam * xt ^ 2 = πt ^ 2 + κ / ε * xt ^ 2 := by
  rw [hπ, hlam, sub_zero]

/-- **AKMM, §18.4.3, p. 548 (price-level targeting)**: in the log-linear model (IS (18.15),
NKPC (18.16)), the price-level rule `i_t = r^n_t + φ_P p̂_t` with any `φ_P > 0` yields a unique
bounded equilibrium for every initial price level (Galí's Exercise 4.6, `determinate_of_pos`;
`σ, κ > 0`, `0 < β < 1`). The book states the rule with an output-gap term and a constant
intercept and makes no determinacy claim; this is the case `φ_x = 0` with the natural-rate
intercept. -/
theorem pol_price_level_rule {Ω : Type*} (𝔼 : Gali.MonetaryPolicyDesign.ExpectationSystem Ω)
    {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 0 < φ) :
    Gali.MonetaryPolicyDesign.Ex4_6.Determinate 𝔼 β σ κ φ :=
  Gali.MonetaryPolicyDesign.Ex4_6.determinate_of_pos 𝔼 hσ hκ hβ0 hβ1 hφ

/-- **AKMM, §18.4.4, p. 549 (discretion)**: after a one-period cost-push shock the discretionary
economy is in steady state from date 1, so `π₀ = κ x₀ + η₀`; minimising `π₀² + λ x₀²` gives the
unique minimiser `x₀ = −κη₀/(κ² + λ)`, with `π₀ = λη₀/(κ² + λ)` (`λ > 0`). -/
theorem pol_discretion_date0 {κ lam η x : ℝ} (hlam : 0 < lam) :
    (κ * (-κ * η / (κ ^ 2 + lam)) + η) ^ 2 + lam * (-κ * η / (κ ^ 2 + lam)) ^ 2 ≤
        (κ * x + η) ^ 2 + lam * x ^ 2 ∧
      ((κ * x + η) ^ 2 + lam * x ^ 2 =
          (κ * (-κ * η / (κ ^ 2 + lam)) + η) ^ 2 + lam * (-κ * η / (κ ^ 2 + lam)) ^ 2 ↔
        x = -κ * η / (κ ^ 2 + lam)) ∧
      κ * (-κ * η / (κ ^ 2 + lam)) + η = lam * η / (κ ^ 2 + lam) := by
  have hD : 0 < κ ^ 2 + lam := by positivity
  have key : (κ * x + η) ^ 2 + lam * x ^ 2 = (κ * (-κ * η / (κ ^ 2 + lam)) + η) ^ 2 +
      lam * (-κ * η / (κ ^ 2 + lam)) ^ 2 + (κ ^ 2 + lam) * (x - -κ * η / (κ ^ 2 + lam)) ^ 2 := by
    field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [key]; nlinarith [sq_nonneg (x - -κ * η / (κ ^ 2 + lam))]
  · rw [key]
    constructor
    · intro h
      have : (κ ^ 2 + lam) * (x - -κ * η / (κ ^ 2 + lam)) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · linarith
      · exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1)
    · intro h; rw [h, sub_self]; ring
  · field_simp; ring

/-- AKMM, p. 550: under discretion the price level jumps at date 0 and stays: with `π₀ = π̄`
and `π_t = 0` for `t ≥ 1`, the cumulated inflation `∑_{s ≤ t} π_s` equals `π̄` at every date. -/
theorem pol_discretion_price_level {infl : ℕ → ℝ} (hz : ∀ t, infl (t + 1) = 0) (t : ℕ) :
    ∑ s ∈ range (t + 1), infl s = infl 0 := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ, ih, hz t, add_zero]

/-- The one-period cost-push shock `u₀ = η`, `u_t = 0` for `t ≥ 1`, on the perfect-foresight
state space. -/
noncomputable def polShock (η : ℝ) : ℕ → Unit → ℝ := fun t _ => if t = 0 then η else 0

/-- The one-period shock is an AR(1) process with `ρ = 0` under perfect foresight. -/
theorem pol_shock_ar1 (η : ℝ) :
    Gali.DiscretionCommitment.ExpectationSystem.IsAR1 Gali.DiscretionCommitment.perfectForesight 0
      (polShock η) := by
  refine ⟨fun _ => rfl, fun t => ?_⟩
  funext ω
  change polShock η (t + 1) ω = (0 : ℝ) • polShock η t ω
  simp [polShock]

/-- The one-period shock is bounded by `|η|`. -/
theorem pol_shock_bound (η : ℝ) : ∀ t ω, |polShock η t ω| ≤ |η| := by
  intro t ω
  unfold polShock
  split_ifs <;> simp

/-- **AKMM, §18.4.4, pp. 549–550 (the commitment path)**: for a one-period cost-push shock `η`,
Galí's commitment solution has price level `p̂_t = δ^{t+1}η`, inflation
`π_{t+1} = −(1 − δ)δ^{t+1}η` and output gap `x_t = −(κ/λ)δ^{t+1}η`, with `δ ∈ (0, 1)`; under
discretion `π_{t+1} = x_{t+1} = 0` (Galí's `impulse_rho0`; `λ` is the weight in (18.22)). -/
theorem pol_commitment_path {β κ lam η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (t : ℕ) :
    Gali.DiscretionCommitment.Commitment.pHat Gali.DiscretionCommitment.perfectForesight β κ lam
        (polShock η) t () = Gali.DiscretionCommitment.Commitment.del β κ lam ^ (t + 1) * η ∧
      Gali.DiscretionCommitment.Commitment.inflC Gali.DiscretionCommitment.perfectForesight
        β κ lam (polShock η) (t + 1) () =
        -((1 - Gali.DiscretionCommitment.Commitment.del β κ lam) *
          Gali.DiscretionCommitment.Commitment.del β κ lam ^ (t + 1)) * η ∧
      Gali.DiscretionCommitment.Commitment.gapC Gali.DiscretionCommitment.perfectForesight
        β κ lam (polShock η) t () =
        -(κ / lam) * Gali.DiscretionCommitment.Commitment.del β κ lam ^ (t + 1) * η ∧
      0 < Gali.DiscretionCommitment.Commitment.del β κ lam ∧
      Gali.DiscretionCommitment.Commitment.del β κ lam < 1 := by
  obtain ⟨h1, h2, h3, -, -⟩ := Gali.DiscretionCommitment.CommitmentVsDiscretion.impulse_rho0
    Gali.DiscretionCommitment.perfectForesight hβ0 hβ1 hlam hκ.ne' (pol_shock_bound η)
    (pol_shock_ar1 η) (fun t => by funext ω; simp [polShock]) t
  have hd := (Gali.DiscretionCommitment.Commitment.del_mem_Ioo_iff (κ := κ) hβ0 hβ1 hlam
    hκ.le).2 hκ
  refine ⟨?_, ?_, ?_, hd.1, hd.2⟩
  · rw [h1]; simp [polShock]
  · rw [h2]; simp [polShock]
  · rw [h3]; simp [polShock]

/-- **AKMM, §18.4.4, p. 549**: at date 0 commitment gives less inflation and a smaller fall in
output than discretion: for `η > 0`, `0 < π₀^C = δη < λη/(κ² + λ) = π₀^D` and
`x₀^D = −κη/(κ² + λ) < x₀^C = −(κ/λ)δη < 0` (Galí's `commit_coef_lt` at `ρ = 0`). -/
theorem pol_commitment_date0 {β κ lam η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (hη : 0 < η) :
    0 < Gali.DiscretionCommitment.Commitment.del β κ lam * η ∧
      Gali.DiscretionCommitment.Commitment.del β κ lam * η < lam * η / (κ ^ 2 + lam) ∧
      -κ * η / (κ ^ 2 + lam) < -(κ / lam) * Gali.DiscretionCommitment.Commitment.del β κ lam * η ∧
      -(κ / lam) * Gali.DiscretionCommitment.Commitment.del β κ lam * η < 0 := by
  obtain ⟨h0, h1⟩ := Gali.DiscretionCommitment.CommitmentVsDiscretion.commit_coef_lt (ρ := 0)
    (κ := κ) hβ0 hβ1 hlam hκ.ne' (by norm_num)
  simp only [mul_zero, sub_zero, div_one, mul_one,
    Gali.DiscretionCommitment.CommitmentVsDiscretion.psiPi]
    at h0 h1
  set d := Gali.DiscretionCommitment.Commitment.del β κ lam
  have hD : 0 < κ ^ 2 + lam := by positivity
  have h1' : d < lam / (κ ^ 2 + lam) := h1
  refine ⟨mul_pos h0 hη, ?_, ?_, ?_⟩
  · rw [mul_div_right_comm]; exact mul_lt_mul_of_pos_right h1' hη
  · have : d / lam < 1 / (κ ^ 2 + lam) := by
      rw [div_lt_iff₀ hlam]; calc d < lam / (κ ^ 2 + lam) := h1'
        _ = 1 / (κ ^ 2 + lam) * lam := by ring
    have h2 := mul_lt_mul_of_pos_left this (mul_pos hκ hη)
    have e1 : -κ * η / (κ ^ 2 + lam) = -(κ * η * (1 / (κ ^ 2 + lam))) := by ring
    have e2 : -(κ / lam) * d * η = -(κ * η * (d / lam)) := by ring
    rw [e1, e2]; linarith
  · have : 0 < κ / lam * d * η := by positivity
    linarith

/-- **AKMM, p. 550 (the price level under commitment)**: cumulated commitment inflation
`∑_{s ≤ t} π_s = p̂_t = δ^{t+1}η` tends to zero: the long-run price level is unaffected by the
cost-push shock. -/
theorem pol_commitment_price_level {β κ lam η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) :
    (∀ t, ∑ s ∈ range (t + 1), Gali.DiscretionCommitment.Commitment.inflC
        Gali.DiscretionCommitment.perfectForesight β κ lam (polShock η) s () =
      Gali.DiscretionCommitment.Commitment.pHat Gali.DiscretionCommitment.perfectForesight
        β κ lam (polShock η) t ()) ∧
    Tendsto (fun t => Gali.DiscretionCommitment.Commitment.pHat
      Gali.DiscretionCommitment.perfectForesight β κ lam (polShock η) t ()) atTop (𝓝 0) := by
  refine ⟨fun t => ?_, ?_⟩
  · induction t with
    | zero =>
      simp [Gali.DiscretionCommitment.Commitment.inflC, Gali.DiscretionCommitment.Commitment.inflOf]
    | succ t ih =>
      rw [sum_range_succ, ih]
      simp [Gali.DiscretionCommitment.Commitment.inflC, Gali.DiscretionCommitment.Commitment.inflOf]
  · have hd := (pol_commitment_path (η := η) hβ0 hβ1 hlam hκ 0).2.2.2
    have hp : ∀ t, Gali.DiscretionCommitment.Commitment.pHat
        Gali.DiscretionCommitment.perfectForesight β κ lam (polShock η) t () =
        Gali.DiscretionCommitment.Commitment.del β κ lam ^ (t + 1) * η :=
      fun t => (pol_commitment_path hβ0 hβ1 hlam hκ t).1
    simp_rw [hp]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hd.1.le hd.2).comp (tendsto_add_atTop_nat 1)
    simpa using this.mul_const η

/-- **AKMM, §18.4.4, pp. 549–550**: commitment strictly beats discretion: with `η ≠ 0`, the
loss `∑ βᵗ(π_t² + λx_t²)` of the commitment path is strictly below that of the discretionary
path (Galí's `commitment_lt_discretion` under perfect foresight, `ρ = 0`). -/
theorem pol_commitment_better {β κ lam η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (hη : η ≠ 0) :
    Gali.DiscretionCommitment.Commitment.expLoss Gali.DiscretionCommitment.perfectForesight β lam
        (Gali.DiscretionCommitment.Commitment.inflC Gali.DiscretionCommitment.perfectForesight
          β κ lam (polShock η))
        (Gali.DiscretionCommitment.Commitment.gapC Gali.DiscretionCommitment.perfectForesight
          β κ lam (polShock η)) () <
      Gali.DiscretionCommitment.Commitment.expLoss Gali.DiscretionCommitment.perfectForesight β lam
        (Gali.DiscretionCommitment.CommitmentVsDiscretion.inflDisc β κ lam 0 (polShock η))
        (Gali.DiscretionCommitment.CommitmentVsDiscretion.gapDisc β κ lam 0 (polShock η)) () :=
  Gali.DiscretionCommitment.CommitmentVsDiscretion.commitment_lt_discretion
    Gali.DiscretionCommitment.perfectForesight
    Gali.DiscretionCommitment.Commitment.perfectForesight_pullOut hβ0 hβ1 hlam hκ.ne'
    (by norm_num) (pol_shock_bound η) (pol_shock_ar1 η) () (by simp [polShock, hη])

/-- **AKMM, p. 550 (time inconsistency)**: at date 1 there is no shock, so the zero path
satisfies the Phillips curve from date 1 with zero loss, whereas the commitment continuation has
a strictly positive period loss at date 1 (`η ≠ 0`): the central bank would like to switch to the
discretionary policy at date 1. -/
theorem pol_time_inconsistent {β κ lam η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (hη : η ≠ 0) :
    (∀ t : ℕ, (0 : ℝ) = β * 0 + κ * 0 + polShock η (t + 1) ()) ∧
      0 < Gali.DiscretionCommitment.Commitment.inflC Gali.DiscretionCommitment.perfectForesight
          β κ lam (polShock η) 1 () ^ 2 + lam *
        Gali.DiscretionCommitment.Commitment.gapC Gali.DiscretionCommitment.perfectForesight
          β κ lam (polShock η) 1 () ^ 2 := by
  refine ⟨fun t => by simp [polShock], ?_⟩
  obtain ⟨-, -, h3, hd0, -⟩ := pol_commitment_path (η := η) hβ0 hβ1 hlam hκ 1
  rw [h3]
  have hx : -(κ / lam) * Gali.DiscretionCommitment.Commitment.del β κ lam ^ (1 + 1) * η ≠ 0 := by
    have : 0 < κ / lam := div_pos hκ hlam
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 this.ne') (pow_pos hd0 _).ne') hη
  have := pow_pos (abs_pos.2 hx) 2
  rw [sq_abs] at this
  nlinarith [sq_nonneg (Gali.DiscretionCommitment.Commitment.inflC
    Gali.DiscretionCommitment.perfectForesight β κ lam (polShock η) 1 ())]

end AKMM.NominalFrictions
