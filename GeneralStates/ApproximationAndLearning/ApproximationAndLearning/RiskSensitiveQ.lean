/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ApproximationAndLearning.QLearning
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Risk-sensitive Q-learning

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.2.2 (pp. 313–317).

For a finite MDP and `γ > 0`, the risk-sensitive Bellman equation is (9.19),
`v(x) = max_a −γ⁻¹ ln ∑_{x'} exp[−γ(r(x, a) + βv(x'))]P(x, a, x')`. It is factored with
`V = ℝ^X`, `V̂ = ℝ^G_{++}`, `(Fv)(x, a) = ∑_{x'} exp[−γ(r(x, a) + βv(x'))]P(x, a, x')` (9.20)
and `(G_σq)(x) = −γ⁻¹ ln q(x, σ(x))` (9.21).

* **Exercise 9.2.1**: `F` and each `G_σ` are order reversing, and `{G_σq}_σ` has a greatest
  element, so `(V, F, V̂, 𝔾)` is an order-reversing FDP.
* §9.2.2.3: the primary policy operators and Bellman operator (9.19) (Lemma 5.2.15); the
  subordinate Bellman min-operator is (9.22),
  `q(x, a) = ∑_{x'} P(x, a, x') exp(−γr(x, a)) (min_{a'} q(x', a'))^β` (Lemma 5.2.16).
* By Theorem 5.2.18, the fundamental optimality properties hold for both ADPs, and a policy with
  `σ(x) ∈ argmin_a q▿*(x, a)` is optimal for (9.19). Each `T_σ` is a contraction of modulus `β`
  for the supremum norm, so Theorem 3.1.5 applies to the primary ADP.
* **Exercise 9.2.2**: `T̂_σ = F ∘ G_σ` is a contraction of modulus `β` for
  `d(q, q') = ‖ln q − ln q'‖∞`; it is order preserving (Remark 9.2.1).
* The update (9.23) is a single-sample version of (9.22) and keeps `q` positive.
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- `ℝ^G_{++}`, the strictly positive functions on `G`. -/
abbrev QPos := {q : M.G → ℝ // ∀ p, 0 < q p}

theorem exists_P_pos (p : M.G) : ∃ x', 0 < M.P p.1.1 p.1.2 x' := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have h0 : ∑ x', M.P p.1.1 p.1.2 x' = 0 :=
    Finset.sum_eq_zero fun x' _ => le_antisymm (h x') (M.P_nonneg _ _ p.2 x')
  rw [M.P_sum _ _ p.2] at h0
  exact one_ne_zero h0

/-- `∑_{x'} exp(a(x'))P(x, a, x')`. -/
noncomputable def expSum (p : M.G) (e : X → ℝ) : ℝ := ∑ x', Real.exp (e x') * M.P p.1.1 p.1.2 x'

theorem expSum_pos (p : M.G) (e : X → ℝ) : 0 < M.expSum p e := by
  obtain ⟨x₀, hx₀⟩ := M.exists_P_pos p
  exact Finset.sum_pos' (fun x' _ => mul_nonneg (Real.exp_pos _).le (M.P_nonneg _ _ p.2 x'))
    ⟨x₀, Finset.mem_univ _, mul_pos (Real.exp_pos _) hx₀⟩

theorem expSum_mono (p : M.G) {e e' : X → ℝ} (h : e ≤ e') : M.expSum p e ≤ M.expSum p e' :=
  Finset.sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (h x'))
    (M.P_nonneg _ _ p.2 x')

/-- `ln ∑ e^{a}P ≤ d + ln ∑ e^{b}P` when `a ≤ b + d`. -/
theorem log_expSum_le (p : M.G) {e e' : X → ℝ} {d : ℝ} (h : ∀ x', e x' ≤ e' x' + d) :
    Real.log (M.expSum p e) ≤ d + Real.log (M.expSum p e') := by
  have h1 : M.expSum p e ≤ Real.exp d * M.expSum p e' := by
    calc M.expSum p e ≤ M.expSum p (fun x' => e' x' + d) := M.expSum_mono p h
      _ = Real.exp d * M.expSum p e' := by
          simp only [expSum, Real.exp_add, Finset.mul_sum]
          exact Finset.sum_congr rfl fun x' _ => by ring
  calc Real.log (M.expSum p e) ≤ Real.log (Real.exp d * M.expSum p e') :=
        Real.log_le_log (M.expSum_pos p e) h1
    _ = d + Real.log (M.expSum p e') := by
        rw [Real.log_mul (Real.exp_pos d).ne' (M.expSum_pos p e').ne', Real.log_exp]

/-- `min_{a ∈ Γ(x)} q(x, a)`. -/
noncomputable def qmin (q : M.G → ℝ) (x : X) : ℝ :=
  (M.Γ x).attach.inf' ((M.Γ_nonempty x).attach) fun a => q ⟨(x, a.1), a.2⟩

theorem qmin_le (q : M.G → ℝ) {x : X} {a : A} (ha : a ∈ M.Γ x) : M.qmin q x ≤ q ⟨(x, a), ha⟩ :=
  Finset.inf'_le (fun a : M.Γ x => q ⟨(x, a.1), a.2⟩) (Finset.mem_attach _ ⟨a, ha⟩)

theorem exists_qmin (q : M.G → ℝ) :
    ∃ σ : M.Policy, ∀ x, ∀ a (ha : a ∈ M.Γ x), q (M.pairOf σ x) ≤ q ⟨(x, a), ha⟩ := by
  obtain ⟨σ, hσ⟩ := M.exists_qgreedy fun p => -q p
  exact ⟨σ, fun x a ha => neg_le_neg_iff.1 (hσ x a ha)⟩

theorem qmin_eq {q : M.G → ℝ} {σ : M.Policy}
    (hσ : ∀ x, ∀ a (ha : a ∈ M.Γ x), q (M.pairOf σ x) ≤ q ⟨(x, a), ha⟩) (x : X) :
    q (M.pairOf σ x) = M.qmin q x :=
  le_antisymm (Finset.le_inf' _ _ fun a _ => hσ x a.1 a.2) (M.qmin_le q (σ.2 x))

theorem qmin_pos (q : M.QPos) (x : X) : 0 < M.qmin q.1 x := by
  obtain ⟨σ, hσ⟩ := M.exists_qmin q.1
  rw [← M.qmin_eq hσ x]
  exact q.2 _

variable (γ : ℝ)

/-- (9.20): `(Fv)(x, a) = ∑_{x'} exp[−γ(r(x, a) + βv(x'))]P(x, a, x')`. -/
noncomputable def Fexp (v : X → ℝ) (p : M.G) : ℝ :=
  M.expSum p fun x' => -γ * (M.r p.1.1 p.1.2 + M.β * v x')

/-- (9.21): `(G_σq)(x) = −γ⁻¹ ln q(x, σ(x))`. -/
noncomputable def Glog (σ : M.Policy) (q : M.QPos) (x : X) : ℝ :=
  -(1 / γ) * Real.log (q.1 (M.pairOf σ x))

variable {γ} (hγ : 0 < γ)
include hγ

theorem Glog_le_Glog {σ τ : M.Policy} {q : M.QPos} {x : X}
    (h : q.1 (M.pairOf σ x) ≤ q.1 (M.pairOf τ x)) : M.Glog γ τ q x ≤ M.Glog γ σ q x := by
  unfold Glog
  exact mul_le_mul_of_nonpos_left (Real.log_le_log (q.2 _) h)
    (neg_nonpos.2 (one_div_pos.2 hγ).le)

theorem Glog_anti {σ : M.Policy} {q q' : M.QPos} {x : X}
    (h : q.1 (M.pairOf σ x) ≤ q'.1 (M.pairOf σ x)) : M.Glog γ σ q' x ≤ M.Glog γ σ q x := by
  unfold Glog
  exact mul_le_mul_of_nonpos_left (Real.log_le_log (q.2 _) h)
    (neg_nonpos.2 (one_div_pos.2 hγ).le)

/-- The risk-sensitive FDP `(ℝ^X, F, ℝ^G_{++}, 𝔾)` of §9.2.2.2. -/
noncomputable def rsfdp : FDP (X → ℝ) M.QPos M.Policy where
  F v := ⟨M.Fexp γ v, fun p => M.expSum_pos p _⟩
  G := M.Glog γ
  greatest q := by
    obtain ⟨σ, hσ⟩ := M.exists_qmin q.1
    exact ⟨σ, fun τ x => M.Glog_le_Glog hγ (hσ x (τ.1 x) (τ.2 x))⟩
  nonempty := M.nonempty_policy

/-- **Exercise 9.2.1** (p. 314): `F` and every `G_σ` are order reversing, so
`(V, F, V̂, 𝔾)` is an order-reversing FDP. -/
theorem exercise_9_2_1 : (M.rsfdp hγ).IsOrderReversing := by
  refine ⟨fun v w hvw p => ?_, fun σ q q' hqq x => M.Glog_anti hγ (hqq _)⟩
  refine M.expSum_mono p fun x' => ?_
  have h1 := mul_le_mul_of_nonneg_left (hvw x') M.β_nonneg
  nlinarith [mul_le_mul_of_nonneg_left h1 hγ.le]

theorem monotonic : (M.rsfdp hγ).Monotonic := Or.inr (M.exercise_9_2_1 hγ)

theorem Gsup_eq (q : M.QPos) (x : X) :
    (M.rsfdp hγ).Gsup q x = -(1 / γ) * Real.log (M.qmin q.1 x) := by
  obtain ⟨σ, hσ⟩ := M.exists_qmin q.1
  have hσg : ∀ τ, (M.rsfdp hγ).G τ q ≤ (M.rsfdp hγ).G σ q := fun τ x =>
    M.Glog_le_Glog hγ (hσ x (τ.1 x) (τ.2 x))
  have heq : (M.rsfdp hγ).Gsup q = (M.rsfdp hγ).G σ q := by
    obtain ⟨⟨τ, hτ⟩, -⟩ := (M.rsfdp hγ).isGreatest_Gsup q
    refine le_antisymm ?_ ((M.rsfdp hγ).G_le_Gsup σ q)
    rw [← hτ]
    exact hσg τ
  rw [heq]
  change -(1 / γ) * Real.log (q.1 (M.pairOf σ x)) = _
  rw [M.qmin_eq hσ x]

/-- §9.2.2.3 (p. 314): the primary policy operators are the risk-sensitive operators
`(T_σv)(x) = −γ⁻¹ ln ∑_{x'} P(x, σ(x), x') exp[−γ(r(x, σ(x)) + βv(x'))]`. -/
theorem primary_T (σ : M.Policy) (v : X → ℝ) (x : X) :
    ((M.rsfdp hγ).primary (M.monotonic hγ)).T σ v x =
      -(1 / γ) * Real.log (∑ x', Real.exp (-γ * (M.r x (σ.1 x) + M.β * v x')) *
        M.P x (σ.1 x) x') := rfl

/-- §9.2.2.3 (p. 314), with Lemma 5.2.15: the primary Bellman operator is (9.19),
`(Tv)(x) = max_{a ∈ Γ(x)} −γ⁻¹ ln ∑_{x'} exp[−γ(r(x, a) + βv(x'))]P(x, a, x')`. -/
theorem primary_bellman_eq (v : X → ℝ) (x : X) :
    ((M.rsfdp hγ).primary (M.monotonic hγ)).bellman v x =
      (M.Γ x).attach.sup' ((M.Γ_nonempty x).attach)
        fun a => -(1 / γ) * Real.log (M.Fexp γ v ⟨(x, a.1), a.2⟩) := by
  rw [FDP.primary_bellman, M.Gsup_eq hγ]
  set q : M.QPos := (M.rsfdp hγ).F v
  have hneg : -(1 / γ) ≤ 0 := neg_nonpos.2 (one_div_pos.2 hγ).le
  apply le_antisymm
  · obtain ⟨a, ha, hmin⟩ := Finset.exists_mem_eq_inf' ((M.Γ_nonempty x).attach)
      (fun a : M.Γ x => q.1 ⟨(x, a.1), a.2⟩)
    have : M.qmin q.1 x = q.1 ⟨(x, a.1), a.2⟩ := hmin
    rw [this]
    exact Finset.le_sup' (fun a : M.Γ x => -(1 / γ) * Real.log (M.Fexp γ v ⟨(x, a.1), a.2⟩)) ha
  · refine Finset.sup'_le _ _ fun a _ => mul_le_mul_of_nonpos_left
      (Real.log_le_log (M.qmin_pos q x) (M.qmin_le q.1 a.2)) hneg

/-- (9.22) (p. 314), with Lemma 5.2.16: the subordinate Bellman min-operator is
`(T̂▿q)(x, a) = ∑_{x'} P(x, a, x') exp(−γr(x, a)) (min_{a'} q(x', a'))^β`. -/
theorem sub_bellman_eq (q : M.QPos) :
    ((M.rsfdp hγ).sub (M.monotonic hγ)).IsMinBellmanValue q ((M.rsfdp hγ).F ((M.rsfdp hγ).Gsup q))
      ∧ ∀ p : M.G, ((M.rsfdp hγ).F ((M.rsfdp hγ).Gsup q)).1 p =
        ∑ x', M.P p.1.1 p.1.2 x' *
          (Real.exp (-γ * M.r p.1.1 p.1.2) * M.qmin q.1 x' ^ M.β) := by
  refine ⟨(FDP.lemma_5_2_16 (M.monotonic hγ) (M.exercise_9_2_1 hγ)).2.1 q, fun p => ?_⟩
  change M.expSum p (fun x' => -γ * (M.r p.1.1 p.1.2 + M.β * (M.rsfdp hγ).Gsup q x')) = _
  unfold expSum
  refine Finset.sum_congr rfl fun x' _ => ?_
  beta_reduce
  rw [M.Gsup_eq hγ, Real.rpow_def_of_pos (M.qmin_pos q x'), ← Real.exp_add]
  have e : -γ * (M.r p.1.1 p.1.2 + M.β * (-(1 / γ) * Real.log (M.qmin q.1 x'))) =
      -γ * M.r p.1.1 p.1.2 + Real.log (M.qmin q.1 x') * M.β := by
    field_simp
    ring
  rw [e, mul_comm]

/-- Each primary policy operator is a contraction of modulus `β` for the supremum norm (the
entropic certainty equivalent is nonexpansive). -/
theorem primary_contraction (σ : M.Policy) (v w : X → ℝ) :
    dist (((M.rsfdp hγ).primary (M.monotonic hγ)).T σ v)
      (((M.rsfdp hγ).primary (M.monotonic hγ)).T σ w) ≤ M.β * dist v w := by
  refine (dist_pi_le_iff (mul_nonneg M.β_nonneg dist_nonneg)).2 fun x => ?_
  rw [Real.dist_eq, M.primary_T hγ, M.primary_T hγ]
  set c := dist v w
  have hc : ∀ y, |v y - w y| ≤ c := fun y => by
    rw [← Real.dist_eq]
    exact dist_le_pi_dist v w y
  have key : ∀ u u' : X → ℝ, (∀ y, |u y - u' y| ≤ c) →
      Real.log (M.expSum (M.pairOf σ x) fun x' => -γ * (M.r x (σ.1 x) + M.β * u x')) ≤
        γ * (M.β * c) + Real.log (M.expSum (M.pairOf σ x)
          fun x' => -γ * (M.r x (σ.1 x) + M.β * u' x')) := fun u u' huu =>
    M.log_expSum_le _ fun x' => by
      have h1 := (abs_sub_le_iff.1 (huu x')).2
      have h2 := mul_le_mul_of_nonneg_left h1 M.β_nonneg
      nlinarith [mul_le_mul_of_nonneg_left h2 hγ.le]
  have h1 := key v w hc
  have h2 := key w v fun y => by rw [abs_sub_comm]; exact hc y
  change |-(1 / γ) * Real.log (M.expSum (M.pairOf σ x) _) -
    -(1 / γ) * Real.log (M.expSum (M.pairOf σ x) _)| ≤ _
  rw [← mul_sub, abs_mul, abs_neg, abs_of_pos (one_div_pos.2 hγ), one_div,
    inv_mul_le_iff₀ hγ, abs_le]
  constructor <;> linarith

/-- §9.2.2.3 (p. 315), by Theorems 3.1.5 and 5.2.18: the fundamental optimality properties hold
for the risk-sensitive problem and the fundamental min-optimality properties for its Q-factor
problem; the min-value function `q▿*` solves (9.22); and any `σ` with
`σ(x) ∈ argmin_{a ∈ Γ(x)} q▿*(x, a)` is optimal for (9.19). -/
theorem section_9_2_2_3 :
    ∃ hw : ((M.rsfdp hγ).primary (M.monotonic hγ)).WellPosed,
    ∃ hw' : ((M.rsfdp hγ).sub (M.monotonic hγ)).WellPosed,
      ((M.rsfdp hγ).primary (M.monotonic hγ)).FundamentalOptimality hw ∧
      ((M.rsfdp hγ).sub (M.monotonic hγ)).MinFundamentalOptimality hw' ∧
      ∃ qstar, ((M.rsfdp hγ).sub (M.monotonic hγ)).IsMinValueFunction qstar ∧
        ((M.rsfdp hγ).sub (M.monotonic hγ)).SolvesMinBellman qstar ∧
        ∀ σ : M.Policy, (∀ x, ∀ a (ha : a ∈ M.Γ x), qstar.1 (M.pairOf σ x) ≤ qstar.1 ⟨(x, a), ha⟩) →
          ((M.rsfdp hγ).primary (M.monotonic hγ)).IsOptimal hw σ := by
  have hR := M.exercise_9_2_1 hγ
  have hm := M.monotonic hγ
  obtain ⟨hFO, -, -, -⟩ := ADP.theorem_3_1_5 isSupNonexpansive_pi M.β_nonneg M.β_lt_one
    (M.primary_contraction hγ) (V₀ := univ)
    ⟨isClosed_univ, fun v _ => FDP.primary_regular hm v, mapsTo_univ _ _⟩ univ_nonempty
  set hw := (ADP.isGloballyStable_of_contraction ⟨(univ_nonempty (α := X → ℝ)).some⟩
    M.β_nonneg M.β_lt_one (M.primary_contraction hγ)).wellPosed
  have hw' : ((M.rsfdp hγ).sub hm).WellPosed := ((FDP.lemma_5_2_12 hm).1).2 hw
  have h518 := FDP.theorem_5_2_18 hm hR hw hw'
  have hMFO := h518.1.1 hFO
  obtain ⟨q, hq, -, hqs, -⟩ := hMFO.2.1
  refine ⟨hw, hw', hFO, hMFO, q, hq, hqs, fun σ hσ => (h518.2 hFO).2.1 q σ hq ?_⟩
  funext x
  rw [M.Gsup_eq hγ, ← M.qmin_eq hσ x]
  rfl

/-- **Exercise 9.2.2** (p. 315): `T̂_σ = F ∘ G_σ` is a contraction of modulus `β` for
`d(q, q') = ‖ln q − ln q'‖∞`: if `|ln q − ln q'| ≤ c` then `|ln T̂_σq − ln T̂_σq'| ≤ βc`. -/
theorem exercise_9_2_2 (σ : M.Policy) (q q' : M.QPos) {c : ℝ}
    (h : ∀ p, |Real.log (q.1 p) - Real.log (q'.1 p)| ≤ c) (p : M.G) :
    |Real.log ((((M.rsfdp hγ).sub (M.monotonic hγ)).T σ q).1 p) -
      Real.log ((((M.rsfdp hγ).sub (M.monotonic hγ)).T σ q').1 p)| ≤ M.β * c := by
  have e : ∀ u : M.QPos, (((M.rsfdp hγ).sub (M.monotonic hγ)).T σ u).1 p =
      M.expSum p fun x' => -γ * M.r p.1.1 p.1.2 + M.β * Real.log (u.1 (M.pairOf σ x')) :=
    fun u => by
      change M.expSum p (fun x' => -γ * (M.r p.1.1 p.1.2 +
        M.β * (-(1 / γ) * Real.log (u.1 (M.pairOf σ x'))))) = _
      unfold expSum
      refine Finset.sum_congr rfl fun x' _ => ?_
      congr 2
      field_simp
      ring
  rw [e, e, abs_le]
  constructor
  · have := M.log_expSum_le p (e := fun x' => -γ * M.r p.1.1 p.1.2 +
      M.β * Real.log (q'.1 (M.pairOf σ x'))) (e' := fun x' => -γ * M.r p.1.1 p.1.2 +
      M.β * Real.log (q.1 (M.pairOf σ x'))) (d := M.β * c) fun x' => by
        have h1 := (abs_sub_le_iff.1 (h (M.pairOf σ x'))).2
        nlinarith [mul_le_mul_of_nonneg_left h1 M.β_nonneg]
    linarith
  · have := M.log_expSum_le p (e := fun x' => -γ * M.r p.1.1 p.1.2 +
      M.β * Real.log (q.1 (M.pairOf σ x'))) (e' := fun x' => -γ * M.r p.1.1 p.1.2 +
      M.β * Real.log (q'.1 (M.pairOf σ x'))) (d := M.β * c) fun x' => by
        have h1 := (abs_sub_le_iff.1 (h (M.pairOf σ x'))).1
        nlinarith [mul_le_mul_of_nonneg_left h1 M.β_nonneg]
    linarith

/-- Remark 9.2.1 (p. 317): each subordinate policy operator `T̂_σ` is order preserving. -/
theorem remark_9_2_1 (σ : M.Policy) :
    Monotone (((M.rsfdp hγ).sub (M.monotonic hγ)).T σ) :=
  ((M.rsfdp hγ).sub (M.monotonic hγ)).mono σ

omit hγ in
/-- The update (9.23) after observing `(x, a, R, X') = (x, a, r(x, a), x')`. -/
theorem update_9_23_pos (q : M.QPos) (p : M.G) (x' : X) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 < (1 - α) * q.1 p + α * (Real.exp (-γ * M.r p.1.1 p.1.2) * M.qmin q.1 x' ^ M.β) := by
  have h1 : 0 < Real.exp (-γ * M.r p.1.1 p.1.2) * M.qmin q.1 x' ^ M.β :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (M.qmin_pos q x') _)
  rcases hα0.eq_or_lt with rfl | hα
  · simpa using q.2 p
  · nlinarith [q.2 p]

end FiniteMDP

end SargentStachurski.ApproximationAndLearning
