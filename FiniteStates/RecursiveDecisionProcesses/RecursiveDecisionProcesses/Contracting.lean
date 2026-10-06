/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.Examples

/-!
# Contracting RDPs

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.2.1 (pp. 263–270) and §8.3.1
(pp. 274–276), with the contracting cases of §8.1.

`R` is contracting with modulus `β < 1` if `|B(x, a, v) − B(x, a, w)| ≤ β‖v − w‖∞` on `G`, (8.26).

* Proposition 8.2.1: `T` and every `T_σ` are contractions of modulus `β` on `V`;
  Exercise 8.2.2: contracting RDPs are continuous; Corollary 8.2.2: if `V` is closed (and
  nonempty) a contracting RDP is globally stable, so Theorem 8.1.1 applies.
* Proposition 8.2.3: if `σ` is `Tᵏv`-greedy then `‖v* − v_σ‖ ≤ 2β/(1 − β) ‖Tᵏv − Tᵏ⁻¹v‖`.
* Exercise 8.2.3: Blackwell's condition implies contraction; with `V = ℝ^X` it also gives
  boundedness by the constants `±M/(1 − β)` when `|B(x, a, 0)| ≤ M`.
* Applications of Blackwell's condition: MDPs (Exercise 8.2.1, Examples 8.1.13 and 8.1.16 with
  `v_σ = (I − βP_σ)⁻¹ r_σ`, Exercise 8.1.14), optimal stopping (Example 8.2.1, Examples 8.1.12
  and 8.1.15, Exercise 8.1.15), state-dependent discounting bounded by `b < 1` (Exercise 8.2.4),
  the Stokey–Lucas form and the optimal savings model (Exercise 8.2.5), job search with
  quantile preferences (Exercise 8.2.6), optimal default (Exercise 8.2.7), risk-sensitive
  RDPs (Proposition 8.3.1) and job search, and quantile RDPs (Exercise 8.3.1).
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- `R` is contracting with modulus `β` (8.26). The modulus is taken nonnegative. -/
def IsContracting (β : ℝ) : Prop :=
  0 ≤ β ∧ β < 1 ∧
    ∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, ∀ w ∈ R.V, |R.B x a v - R.B x a w| ≤ β * ‖v - w‖

/-- **Proposition 8.2.1** (p. 263), policy operators: each `T_σ` is a contraction of modulus `β`
on `V` in the supremum norm. -/
theorem IsContracting.isContractionOn_Tσ {R : RDP X A} {β : ℝ} (h : R.IsContracting β)
    {σ : X → A} (hσ : R.IsFeasible σ) : IsContractionOn (R.Tσ σ) R.V β :=
  ⟨R.Tσ_mapsTo hσ, h.1, h.2.1, fun v hv w hw => by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact h.2.2 x _ (hσ x) v hv w hw⟩

/-- **Proposition 8.2.1** (p. 263), Bellman operator: `T` is a contraction of modulus `β` on `V`,
by Lemma 2.2.2. -/
theorem IsContracting.isContractionOn_T {R : RDP X A} {β : ℝ} (h : R.IsContracting β) :
    IsContractionOn R.T R.V β :=
  ⟨R.T_mapsTo, h.1, h.2.1, fun v hv w hw => by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact (abs_sup'_sub_sup'_le (R.Γ_nonempty x) _ _).trans
      (Finset.sup'_le _ _ fun a ha => h.2.2 x a ha v hv w hw)⟩

/-- **Exercise 8.2.2** (p. 263): a contracting RDP is continuous. -/
theorem IsContracting.isContinuous {R : RDP X A} {β : ℝ} (h : R.IsContracting β) :
    R.IsContinuous := by
  intro x a ha v hv vk hvk hlim
  rw [tendsto_iff_norm_sub_tendsto_zero] at hlim ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) (by simpa using hlim.const_mul β)
  rw [Real.norm_eq_abs]
  exact h.2.2 x a ha _ (hvk k) v hv

/-- **Corollary 8.2.2** (p. 264): a contracting RDP with `V` closed and nonempty is globally
stable, so every conclusion of Theorem 8.1.1 holds. -/
theorem IsContracting.isGloballyStable {R : RDP X A} {β : ℝ} (h : R.IsContracting β)
    (hV : IsClosed R.V) (hne : R.V.Nonempty) : R.IsGloballyStable := by
  intro σ hσ
  have hc := h.isContractionOn_Tσ hσ
  obtain ⟨u, hu, hfix⟩ := hc.exists_fixedPt hV hne
  exact ⟨u, hu, hfix, fun v hv hv' => hc.fixedPt_unique hv hu hv' hfix,
    fun v hv => hc.tendsto_iterate_fixedPt hv hu hfix⟩

/-- **Proposition 8.2.3** (p. 264), (8.28): for a contracting RDP with `V` closed and nonempty,
`v ∈ V`, `v_k = Tᵏv` and `σ` a `v_{k+1}`-greedy policy,
`‖v* − v_σ‖ ≤ 2β/(1 − β) ‖v_{k+1} − v_k‖`. -/
theorem IsContracting.norm_vstar_sub_vσ_le [DecidableEq X] [DecidableEq A] {R : RDP X A}
    {β : ℝ} (h : R.IsContracting β) (hV : IsClosed R.V) (hne : R.V.Nonempty) {v : X → ℝ}
    (hv : v ∈ R.V) (k : ℕ) {σ : X → A} (hσ : R.IsGreedy (R.T^[k + 1] v) σ) :
    ‖R.vstar - R.vσ σ‖ ≤ 2 * β / (1 - β) * ‖R.T^[k + 1] v - R.T^[k] v‖ := by
  have hGS := h.isGloballyStable hV hne
  have hw := hGS.wellPosed
  obtain ⟨hstar, hfix⟩ := vstar_spec hw hGS.comparable
  have hT := h.isContractionOn_T
  have hσc := h.isContractionOn_Tσ hσ.1
  set vk := R.T^[k + 1] v with hvk
  set vk1 := R.T^[k] v
  have hvk1m : vk1 ∈ R.V := R.T_mapsTo.iterate k hv
  have hvkm : vk ∈ R.V := R.T_mapsTo.iterate (k + 1) hv
  have hvkT : vk = R.T vk1 := iterate_succ_apply' _ _ _
  have hvσ := vσ_mem hw hσ.1
  have hβ1 : 0 < 1 - β := by linarith [h.2.1]
  -- (8.30)
  have h1 : (1 - β) * ‖R.vstar - vk‖ ≤ β * ‖vk - vk1‖ := by
    have e1 : ‖R.vstar - vk‖ ≤ ‖R.T R.vstar - R.T vk‖ + ‖R.T vk - R.T vk1‖ := by
      rw [hfix.eq, ← hvkT]
      calc ‖R.vstar - vk‖ = ‖(R.vstar - R.T vk) + (R.T vk - vk)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have e2 := hT.norm_sub_le _ hstar _ hvkm
    have e3 := hT.norm_sub_le _ hvkm _ hvk1m
    nlinarith
  -- (8.31)
  have h2 : (1 - β) * ‖vk - R.vσ σ‖ ≤ β * ‖vk - vk1‖ := by
    have hTσ : R.T vk = R.Tσ σ vk := (R.Tσ_eq_T_of_isGreedy hσ).symm
    have e1 : ‖vk - R.vσ σ‖ ≤ ‖R.T vk1 - R.T vk‖ + ‖R.Tσ σ vk - R.Tσ σ (R.vσ σ)‖ := by
      rw [← hvkT, (isFixedPt_vσ hw hσ.1).eq, ← hTσ]
      calc ‖vk - R.vσ σ‖ = ‖(vk - R.T vk) + (R.T vk - R.vσ σ)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have e2 := hT.norm_sub_le _ hvk1m _ hvkm
    have e3 := hσc.norm_sub_le _ hvkm _ hvσ
    rw [norm_sub_rev vk1 vk] at e2
    nlinarith
  have h3 : ‖R.vstar - R.vσ σ‖ ≤ ‖R.vstar - vk‖ + ‖vk - R.vσ σ‖ := by
    calc ‖R.vstar - R.vσ σ‖ = ‖(R.vstar - vk) + (vk - R.vσ σ)‖ := by rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [div_mul_eq_mul_div, le_div_iff₀ hβ1]
  nlinarith

/-! ### Blackwell's condition (§8.2.1.3) -/

/-- `R` satisfies Blackwell's condition with `β ∈ [0, 1)` (p. 265): `V` is closed under adding
nonnegative constants and `B(x, a, v + λ) ≤ B(x, a, v) + βλ` for `λ ≥ 0`. -/
def SatisfiesBlackwell (β : ℝ) : Prop :=
  0 ≤ β ∧ β < 1 ∧ (∀ v ∈ R.V, ∀ c : ℝ, 0 ≤ c → v + (fun _ => c) ∈ R.V) ∧
    ∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, ∀ c : ℝ, 0 ≤ c → R.B x a (v + fun _ => c) ≤ R.B x a v + β * c

/-- **Exercise 8.2.3** (p. 265): Blackwell's condition implies that `R` is contracting with
modulus `β`. -/
theorem SatisfiesBlackwell.isContracting {R : RDP X A} {β : ℝ} (h : R.SatisfiesBlackwell β) :
    R.IsContracting β := by
  refine ⟨h.1, h.2.1, fun x a ha v hv w hw => ?_⟩
  have key : ∀ v ∈ R.V, ∀ w ∈ R.V, R.B x a v - R.B x a w ≤ β * ‖v - w‖ := by
    intro v hv w hw
    have hle : v ≤ w + fun _ => ‖v - w‖ := fun y => by
      have := norm_le_pi_norm (v - w) y
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      simp only [Pi.add_apply]
      linarith [le_abs_self (v y - w y)]
    have hmem := h.2.2.1 w hw _ (norm_nonneg (v - w))
    have h1 := R.mono x a ha v hv _ hmem hle
    have h2 := h.2.2.2 x a ha w hw _ (norm_nonneg (v - w))
    linarith
  rw [abs_sub_le_iff]
  refine ⟨key v hv w hw, ?_⟩
  have := key w hw v hv
  rwa [norm_sub_rev] at this

/-- Blackwell's condition on `V = ℝ^X` with `|B(x, a, 0)| ≤ M` on `G` makes `R` bounded by the
constants `±M/(1 − β)`. -/
theorem SatisfiesBlackwell.isBoundedBy {R : RDP X A} {β : ℝ} (h : R.SatisfiesBlackwell β)
    (hV : R.V = univ) {M : ℝ} (hM : ∀ x, ∀ a ∈ R.Γ x, |R.B x a 0| ≤ M) :
    R.IsBoundedBy (fun _ => -(M / (1 - β))) (fun _ => M / (1 - β)) := by
  have hβ1 : 0 < 1 - β := by linarith [h.2.1]
  have hKM : M / (1 - β) * (1 - β) = M := div_mul_cancel₀ M hβ1.ne'
  refine ⟨fun x => ?_, by rw [hV]; exact subset_univ _, fun x a ha => ⟨?_, ?_⟩⟩
  · obtain ⟨a, ha⟩ := R.Γ_nonempty x
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x a ha)
    have : 0 ≤ M / (1 - β) := div_nonneg hM0 hβ1.le
    linarith
  · obtain ⟨a', ha'⟩ := R.Γ_nonempty x
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x a' ha')
    have hK0 : 0 ≤ M / (1 - β) := div_nonneg hM0 hβ1.le
    have e : ((fun _ : X => -(M / (1 - β))) + fun _ => M / (1 - β)) = 0 := by
      funext y
      simp
    have h1 := h.2.2.2 x a ha (fun _ => -(M / (1 - β))) (by rw [hV]; exact mem_univ _) _ hK0
    rw [e] at h1
    have h2 := (abs_le.1 (hM x a ha)).1
    nlinarith
  · obtain ⟨a', ha'⟩ := R.Γ_nonempty x
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x a' ha')
    have hK0 : 0 ≤ M / (1 - β) := div_nonneg hM0 hβ1.le
    have e : ((0 : X → ℝ) + fun _ => M / (1 - β)) = fun _ => M / (1 - β) := by
      funext y
      simp
    have h1 := h.2.2.2 x a ha 0 (by rw [hV]; exact mem_univ _) _ hK0
    rw [e] at h1
    have h2 := (abs_le.1 (hM x a ha)).2
    nlinarith

end RDP

/-! ### MDPs and optimal stopping -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The MDP RDP satisfies Blackwell's condition with equality: `B(x, a, v + λ) = B(x, a, v) + βλ`.
-/
theorem satisfiesBlackwell : M.toRDP.SatisfiesBlackwell M.β := by
  refine ⟨M.β_pos.le, M.β_lt_one, fun _ _ _ _ => mem_univ _, fun x a _ v _ c _ => le_of_eq ?_⟩
  simp only [toRDP_B, Pi.add_apply, add_mul, sum_add_distrib, ← Finset.mul_sum, M.P_rowsum,
    mul_one]
  ring

/-- **Exercise 8.2.1** (p. 263): every MDP is a contracting RDP, with modulus `β`. -/
theorem isContracting : M.toRDP.IsContracting M.β := M.satisfiesBlackwell.isContracting

/-- **Example 8.1.16** (p. 253): the MDP RDP is globally stable (hence well-posed, Example 8.1.13),
so Theorem 8.1.1 applies (Example 8.1.19). -/
theorem isGloballyStable : M.toRDP.IsGloballyStable :=
  M.isContracting.isGloballyStable isClosed_univ ⟨0, mem_univ _⟩

/-- **Example 8.1.13** (p. 252): `v_σ = (I − βP_σ)⁻¹ r_σ`. -/
theorem vσ_eq [DecidableEq X] [Nonempty X] {σ : X → A} (hσ : M.toRDP.IsFeasible σ) :
    M.toRDP.vσ σ = (1 - M.β • M.Pσ σ)⁻¹ *ᵥ M.rσ σ := by
  have hρ : specRad (M.β • M.Pσ σ) < 1 := by
    rw [specRad_smul_isMarkov (M.isMarkov_Pσ σ) M.β_pos.le]
    exact M.β_lt_one
  refine (RDP.eq_vσ_of_isFixedPt M.isGloballyStable.wellPosed hσ (mem_univ _) ?_).symm
  have := isFixedPt_affineOp_inv hρ (M.rσ σ)
  change M.toRDP.Tσ σ _ = _
  rw [M.toRDP_Tσ]
  exact this

/-- **Exercise 8.1.14** (p. 260): the MDP RDP is bounded, by `±‖r‖/(1 − β)`. -/
theorem isBoundedBy :
    M.toRDP.IsBoundedBy (fun _ => -(‖M.r‖ / (1 - M.β))) (fun _ => ‖M.r‖ / (1 - M.β)) := by
  refine M.satisfiesBlackwell.isBoundedBy rfl fun x a _ => ?_
  have h1 : M.toRDP.B x a 0 = M.r x a := by simp [toRDP_B]
  rw [h1, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm (M.r x) a).trans (norm_le_pi_norm M.r x)

end MDP

variable {X : Type*} [Fintype X]

/-- **Example 8.2.1** (p. 263): the optimal stopping RDP satisfies Blackwell's condition with
modulus `β` (adding `λ` to `v` raises the continuation value by `βλ`). -/
theorem stopping_satisfiesBlackwell (e c : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    {P : Matrix X X ℝ} (hP : IsMarkov P) : (stopping e c hβ hP).SatisfiesBlackwell β := by
  refine ⟨hβ, hβ1, fun _ _ _ _ => mem_univ _, fun x a _ v _ k hk => ?_⟩
  cases a
  · apply le_of_eq
    change c x + β * (P *ᵥ (v + fun _ => k)) x = c x + β * (P *ᵥ v) x + β * k
    rw [mulVec_add, hP.mulVec_const, Pi.add_apply]
    ring
  · change e x ≤ e x + β * k
    nlinarith

/-- **Example 8.2.1** (p. 263): the optimal stopping RDP is contracting with modulus `β`. -/
theorem stopping_isContracting (e c : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    {P : Matrix X X ℝ} (hP : IsMarkov P) : (stopping e c hβ hP).IsContracting β :=
  (stopping_satisfiesBlackwell e c hβ hβ1 hP).isContracting

/-- **Examples 8.1.12 and 8.1.15** (pp. 252–253): the optimal stopping RDP is globally stable (so
well-posed), and Theorem 8.1.1 applies (Example 8.1.18). -/
theorem stopping_isGloballyStable (e c : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    {P : Matrix X X ℝ} (hP : IsMarkov P) : (stopping e c hβ hP).IsGloballyStable :=
  (stopping_isContracting e c hβ hβ1 hP).isGloballyStable isClosed_univ ⟨0, mem_univ _⟩

/-- **Exercise 8.1.15** (p. 260): the optimal stopping RDP is bounded, by
`±(‖e‖ + ‖c‖)/(1 − β)`. -/
theorem stopping_isBoundedBy (e c : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    {P : Matrix X X ℝ} (hP : IsMarkov P) :
    (stopping e c hβ hP).IsBoundedBy (fun _ => -((‖e‖ + ‖c‖) / (1 - β)))
      (fun _ => (‖e‖ + ‖c‖) / (1 - β)) := by
  refine (stopping_satisfiesBlackwell e c hβ hβ1 hP).isBoundedBy rfl fun x a _ => ?_
  have he : |e x| ≤ ‖e‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm e x
  have hc : |c x| ≤ ‖c‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm c x
  cases a
  · change |c x + β * (P *ᵥ 0) x| ≤ _
    rw [mulVec_zero, Pi.zero_apply, mul_zero, add_zero]
    linarith [norm_nonneg e]
  · change |e x| ≤ _
    linarith [norm_nonneg c]

/-! ### State-dependent discounting, Stokey–Lucas and savings -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- **Exercise 8.2.4** (p. 265): with state-dependent discounting bounded by `b < 1`, the RDP of
Example 8.1.5 satisfies Blackwell's condition with modulus `b`, so it is contracting. -/
theorem withDiscount_satisfiesBlackwell {β : X → A → X → ℝ} (hβ : ∀ x a x', 0 ≤ β x a x')
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hβb : ∀ x a x', β x a x' ≤ b) :
    (M.withDiscount β hβ).SatisfiesBlackwell b := by
  refine ⟨hb0, hb1, fun _ _ _ _ => mem_univ _, fun x a _ v _ c hc => ?_⟩
  change M.r x a + ∑ x', (v + fun _ => c : X → ℝ) x' * β x a x' * M.P x a x' ≤
    M.r x a + ∑ x', v x' * β x a x' * M.P x a x' + b * c
  have hsum : ∑ x', c * β x a x' * M.P x a x' ≤ b * c := by
    calc ∑ x', c * β x a x' * M.P x a x' ≤ ∑ x', c * b * M.P x a x' :=
          sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hβb x a x') hc) (M.P_nonneg x a x')
      _ = b * c := by rw [← Finset.mul_sum, M.P_rowsum, mul_one, mul_comm]
  simp only [Pi.add_apply, add_mul, sum_add_distrib]
  linarith

/-- **Exercise 8.2.4** (p. 265): state-dependent discounting bounded by `b < 1` gives a contracting
RDP on `ℝ^X`. -/
theorem withDiscount_isContracting {β : X → A → X → ℝ} (hβ : ∀ x a x', 0 ≤ β x a x') {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hβb : ∀ x a x', β x a x' ≤ b) :
    (M.withDiscount β hβ).IsContracting b :=
  (M.withDiscount_satisfiesBlackwell hβ hb0 hb1 hβb).isContracting

end MDP

/-- **Exercise 8.2.5** (p. 265): the discrete optimal savings model of §5.2.2, the Stokey–Lucas
model with wealth `w`, `Q`-Markov income `y`, savings `s ∈ Γ(w, y) = {s : s ≤ R(w + y)}` and reward
`u(w + y − s/R)`, satisfies Blackwell's condition. -/
theorem savings_satisfiesBlackwell {W Y : Type*} [Fintype W] [Fintype Y] [DecidableEq W]
    (wealth : W → ℝ) (inc : Y → ℝ) (Rr : ℝ) (u : ℝ → ℝ)
    (hΓ : ∀ x : W × Y, ((univ : Finset W).filter fun s =>
      wealth s ≤ Rr * (wealth x.1 + inc x.2)).Nonempty)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : Matrix Y Y ℝ} (hQ : IsMarkov Q) :
    (stokeyLucas (fun x => (univ : Finset W).filter fun s =>
      wealth s ≤ Rr * (wealth x.1 + inc x.2)) hΓ (fun w y s => u (wealth w + inc y - wealth s / Rr))
      hβ0 hβ1 hQ).toRDP.SatisfiesBlackwell β :=
  MDP.satisfiesBlackwell _

/-! ### Job search with quantile preferences (§8.2.1.4) -/

variable {W : Type*} [Fintype W]

/-- The job search RDP with quantile preferences (§8.2.1.4): `Γ(w) = {accept, reject}`, `V = ℝ^W`
and `B_τ(w, a, v) = w/(1 − β)` on accepting, `c + β(R_τ v)(w)` on rejecting, for `τ ∈ (0, 1]`. -/
noncomputable def quantileJobSearch [Nonempty W] (wage : W → ℝ) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {P : Matrix W W ℝ} (hP : IsMarkov P) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) : RDP W Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  V := univ
  B := fun w a v => bif a then wage w / (1 - β) else c + β * quantR τ P v w
  mono := fun w a _ v _ v' _ hvv' => by
    cases a
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        ((isCertEquiv_quantR hτ0 hτ1 hP).mono v (mem_univ _) v' (mem_univ _) hvv' w) hβ)
    · exact le_rfl
  consistent := fun _ _ _ _ => mem_univ _

/-- **Exercise 8.2.6** (p. 266): the quantile job search RDP is contracting, with modulus `β`. -/
theorem quantileJobSearch_isContracting [Nonempty W] (wage : W → ℝ) (c : ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) {P : Matrix W W ℝ} (hP : IsMarkov P) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ ≤ 1) : (quantileJobSearch wage c hβ hP hτ0 hτ1).IsContracting β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨hβ, hβ1, fun _ _ _ _ => mem_univ _,
    fun w a _ v _ k hk => ?_⟩
  cases a
  · apply le_of_eq
    change c + β * quantR τ P (v + fun _ => k) w = c + β * quantR τ P v w + β * k
    rw [quantR_add_const hτ0 hτ1 hP, Pi.add_apply]
    ring
  · change wage w / (1 - β) ≤ wage w / (1 - β) + β * k
    nlinarith

/-- The risk-sensitive job search RDP (§8.3.1.2): `B(w, a, v) = w/(1 − β)` on accepting and
`c + (β/θ) ln ∑ exp(θv(w'))P(w, w')` on rejecting. -/
noncomputable def riskSensitiveJobSearch (wage : W → ℝ) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {P : Matrix W W ℝ} (hP : IsMarkov P) {θ : ℝ} (hθ : θ ≠ 0) : RDP W Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  V := univ
  B := fun w a v => bif a then wage w / (1 - β) else c + β * entR θ P v w
  mono := fun w a _ v _ v' _ hvv' => by
    cases a
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        ((isCertEquiv_entR hθ hP).mono v (mem_univ _) v' (mem_univ _) hvv' w) hβ)
    · exact le_rfl
  consistent := fun _ _ _ _ => mem_univ _

/-- §8.3.1.2 (p. 276): the risk-sensitive job search RDP is contracting with modulus `β`, so it
is globally stable and Theorem 8.1.1 applies. -/
theorem riskSensitiveJobSearch_isContracting (wage : W → ℝ) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β < 1) {P : Matrix W W ℝ} (hP : IsMarkov P) {θ : ℝ} (hθ : θ ≠ 0) :
    (riskSensitiveJobSearch wage c hβ hP hθ).IsContracting β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨hβ, hβ1, fun _ _ _ _ => mem_univ _,
    fun w a _ v _ k hk => ?_⟩
  cases a
  · apply le_of_eq
    change c + β * entR θ P (v + fun _ => k) w = c + β * entR θ P v w + β * k
    rw [entR_add_const hθ hP, Pi.add_apply]
    ring
  · change wage w / (1 - β) ≤ wage w / (1 - β) + β * k
    nlinarith

/-! ### Optimal default (§8.2.1.5) -/

variable {Y Bd : Type*} [Fintype Y] [Fintype Bd]

/-- The optimal default RDP (§8.2.1.5). States `(y, b, d)` with income index `y`, bond position
`b` and default flag `d`; actions `(b_a, d_a)`. Out of default every action is feasible; in default
only `(0, 1)`, where `b₀` is the zero bond. With `Q`-Markov income, consumption utility `u`, income
levels `inc`, bond values `bond`, price `q`, default cost `h`, reentry probability `θ ∈ [0, 1]`:
(8.32) `B((y, b, 0), (b_a, 0), v) = u(y + b − qb_a) + β ∑ v(y', b_a, 0)Q(y, y')`, and (8.33)
`B((y, b, d), (b_a, 1), v) = u(h(y)) + β[θ ∑ v(y', 0, 0)Q(y, y') + (1 − θ) ∑ v(y', 0, 1)Q(y, y')]`.
-/
noncomputable def optimalDefault (inc : Y → ℝ) (bond : Bd → ℝ) (b₀ : Bd) (q : ℝ) (u h : ℝ → ℝ)
    {β θ : ℝ} (hβ : 0 ≤ β) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {Q : Matrix Y Y ℝ} (hQ : IsMarkov Q) :
    RDP (Y × Bd × Bool) (Bd × Bool) where
  Γ := fun s => bif s.2.2 then {(b₀, true)} else univ
  Γ_nonempty := fun s => ⟨(b₀, true), by rcases s with ⟨_, _, d⟩; cases d <;> simp⟩
  V := univ
  B := fun s a v => bif a.2 then
      u (h (inc s.1)) + β * (θ * ∑ y', v (y', b₀, false) * Q s.1 y' +
        (1 - θ) * ∑ y', v (y', b₀, true) * Q s.1 y')
    else u (inc s.1 + bond s.2.1 - q * bond a.1) + β * ∑ y', v (y', a.1, false) * Q s.1 y'
  mono := fun s a _ v _ w _ hvw => by
    have hs : ∀ b d, ∑ y', v (y', b, d) * Q s.1 y' ≤ ∑ y', w (y', b, d) * Q s.1 y' :=
      fun b d => sum_le_sum fun y' _ => mul_le_mul_of_nonneg_right (hvw _) (hQ.nonneg _ _)
    cases a.2
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hs _ _) hβ)
    · refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hβ)
      · exact mul_le_mul_of_nonneg_left (hs _ _) hθ0
      · exact mul_le_mul_of_nonneg_left (hs _ _) (by linarith)
  consistent := fun _ _ _ _ => mem_univ _

/-- **Exercise 8.2.7** (p. 270): the optimal default RDP is contracting with modulus `β < 1`: it
satisfies Blackwell's condition with equality in both cases (8.32)–(8.33). -/
theorem optimalDefault_isContracting (inc : Y → ℝ) (bond : Bd → ℝ) (b₀ : Bd) (q : ℝ)
    (u h : ℝ → ℝ) {β θ : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {Q : Matrix Y Y ℝ} (hQ : IsMarkov Q) :
    (optimalDefault inc bond b₀ q u h hβ hθ0 hθ1 hQ).IsContracting β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨hβ, hβ1, fun _ _ _ _ => mem_univ _,
    fun s a _ v _ k _ => le_of_eq ?_⟩
  have hs : ∀ b d, ∑ y', (v + fun _ => k : Y × Bd × Bool → ℝ) (y', b, d) * Q s.1 y' =
      ∑ y', v (y', b, d) * Q s.1 y' + k := fun b d => by
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ← Finset.mul_sum, hQ.rowsum, mul_one]
  rcases a with ⟨ba, da⟩
  cases da
  · change u _ + β * ∑ y', (v + fun _ => k : Y × Bd × Bool → ℝ) (y', ba, false) * Q s.1 y' =
      u _ + β * ∑ y', v (y', ba, false) * Q s.1 y' + β * k
    rw [hs]
    ring
  · change u _ + β * (θ * ∑ y', (v + fun _ => k : Y × Bd × Bool → ℝ) (y', b₀, false) * Q s.1 y' +
        (1 - θ) * ∑ y', (v + fun _ => k : Y × Bd × Bool → ℝ) (y', b₀, true) * Q s.1 y') =
      u _ + β * (θ * ∑ y', v (y', b₀, false) * Q s.1 y' +
        (1 - θ) * ∑ y', v (y', b₀, true) * Q s.1 y') + β * k
    rw [hs, hs]
    ring

/-! ### Risk-sensitive and quantile RDPs (§8.3.1) -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- **Proposition 8.3.1** (p. 275): the risk-sensitive RDP is contracting with modulus `β`, since
the entropic certainty equivalent is constant-subadditive (with equality). -/
theorem riskSensitive_isContracting {θ : ℝ} (hθ : θ ≠ 0) :
    (M.riskSensitive hθ).IsContracting M.β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨M.β_pos.le, M.β_lt_one,
    fun _ _ _ _ => mem_univ _, fun x a _ v _ c _ => le_of_eq ?_⟩
  change M.r x a + M.β * entR θ (kernelAt M.P a) (v + fun _ => c) x =
    M.r x a + M.β * entR θ (kernelAt M.P a) v x + M.β * c
  rw [entR_add_const hθ (M.isMarkov_P a), Pi.add_apply]
  ring

/-- **Proposition 8.3.1** with Corollary 8.2.2: the risk-sensitive RDP is globally stable. -/
theorem riskSensitive_isGloballyStable {θ : ℝ} (hθ : θ ≠ 0) :
    (M.riskSensitive hθ).IsGloballyStable :=
  (M.riskSensitive_isContracting hθ).isGloballyStable isClosed_univ ⟨0, mem_univ _⟩

/-- **Exercise 8.3.1** (p. 275): the quantile RDP is contracting with modulus `β`. -/
theorem quantile_isContracting [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    (M.quantile hτ0 hτ1).IsContracting M.β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨M.β_pos.le, M.β_lt_one,
    fun _ _ _ _ => mem_univ _, fun x a _ v _ c _ => le_of_eq ?_⟩
  change M.r x a + M.β * quantR τ (kernelAt M.P a) (v + fun _ => c) x =
    M.r x a + M.β * quantR τ (kernelAt M.P a) v x + M.β * c
  rw [quantR_add_const hτ0 hτ1 (M.isMarkov_P a), Pi.add_apply]
  ring

/-- **Exercise 8.3.1** (p. 275): for `β < 1` the quantile RDP is globally stable. -/
theorem quantile_isGloballyStable [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    (M.quantile hτ0 hτ1).IsGloballyStable :=
  (M.quantile_isContracting hτ0 hτ1).isGloballyStable isClosed_univ ⟨0, mem_univ _⟩

end MDP

end SargentStachurski.RecursiveDecisionProcesses
