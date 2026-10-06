/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.ConcaveRDP

/-!
# Adversarial agents, robustness and KL penalties

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.3.2–§8.3.3.3 (pp. 276–283).

The decision maker chooses `a ∈ Γ(x)`, then an adversary chooses `d ∈ D(x, a)` to minimise
`B(x, a, d, v)`, giving the Bellman equation (8.43) and the aggregator
`B̂(x, a, v) = inf_{d ∈ D(x, a)} B(x, a, d, v)` on `V = [v₁, v₂]`.

* Exercise 8.3.3: `inf (f + g) ≥ inf f + inf g` for functions bounded below.
* Proposition 8.3.2: under (a) monotonicity, (b) `v₁ + ε ≤ B(·, v₁)`, (c) `B(·, v₂) ≤ v₂` and
  (d) concavity, `(Γ, V, B̂)` is a concave RDP, hence globally stable.
* §8.3.2.2: the perturbed MDP `B(x, a, d, v) = r(x, a, d) + β ∑ v(x')P(x, a, d, x')`; Exercise
  8.3.4 (conditions (b)–(c) for `v₁ = (r₁ − ε)/(1 − β)`, `v₂ = r₂/(1 − β)`) and Lemma 8.3.3.
* §8.3.3.1: robust control (8.48) is the perturbed MDP (8.49) with the adversary choosing the
  kernel, so it is a concave RDP (Proposition 8.3.4).
* §8.3.3.2: a penalty `d(P, P̄)` in (8.50) is absorbed into the reward, `r̂ = r + βd`.
* §8.3.3.3: the variational formula (8.51) for KL divergence on a finite set, and its
  consequence: with the penalty `−(1/θ)d_KL`, `θ < 0`, the robust aggregator is the
  risk-sensitive aggregator (8.9) under the baseline kernel.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.RecursiveDecisionProcesses

/-- **Exercise 8.3.3** (p. 279): for `f, g` bounded below on a nonempty set,
`inf (f + g) ≥ inf f + inf g`. -/
theorem iInf_add_iInf_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ} (hf : BddBelow (range f))
    (hg : BddBelow (range g)) : (⨅ i, f i) + ⨅ i, g i ≤ ⨅ i, (f i + g i) :=
  le_ciInf fun i => add_le_add (ciInf_le hf i) (ciInf_le hg i)

/-- `r + β inf f = inf (r + βf)` for `β ≥ 0` and `f` bounded below on a nonempty set. -/
theorem add_mul_iInf {ι : Type*} [Nonempty ι] {f : ι → ℝ} (hf : BddBelow (range f)) (r : ℝ)
    {β : ℝ} (hβ : 0 ≤ β) : r + β * ⨅ i, f i = ⨅ i, (r + β * f i) := by
  rw [Real.mul_iInf_of_nonneg hβ]
  have hg : BddBelow (range fun i => β * f i) := by
    obtain ⟨m, hm⟩ := hf
    exact ⟨β * m, by rintro _ ⟨i, rfl⟩; exact mul_le_mul_of_nonneg_left (hm ⟨i, rfl⟩) hβ⟩
  refine le_antisymm (le_ciInf fun i => add_le_add le_rfl (ciInf_le hg i)) ?_
  have hb : BddBelow (range fun i => r + β * f i) := by
    obtain ⟨m, hm⟩ := hg
    exact ⟨r + m, by rintro _ ⟨i, rfl⟩; exact add_le_add le_rfl (hm ⟨i, rfl⟩)⟩
  have : (⨅ i, (r + β * f i)) - r ≤ ⨅ i, β * f i := le_ciInf fun i => by
    have := ciInf_le hb i
    linarith
  linarith

/-! ### Adversarial agents (§8.3.2.1) -/

variable {X A D : Type*} [Fintype X] [Fintype A]
variable (Γ₀ : X → Finset A) (D₀ : X → A → Set D) (B₀ : X → A → D → (X → ℝ) → ℝ)

/-- The adversarial aggregator `B̂(x, a, v) = inf_{d ∈ D(x, a)} B(x, a, d, v)`. -/
noncomputable def advB (x : X) (a : A) (v : X → ℝ) : ℝ := ⨅ d : D₀ x a, B₀ x a d v

/-- Conditions (a)–(d) of §8.3.2.1 (p. 278), with `D(x, a)` nonempty on `G`. -/
structure AdvConditions (v₁ v₂ : X → ℝ) (ε : ℝ) : Prop where
  nonempty : ∀ x, ∀ a ∈ Γ₀ x, (D₀ x a).Nonempty
  mono : ∀ x, ∀ a ∈ Γ₀ x, ∀ d ∈ D₀ x a, Monotone (B₀ x a d)
  eps_pos : 0 < ε
  lower : ∀ x, ∀ a ∈ Γ₀ x, ∀ d ∈ D₀ x a, v₁ x + ε ≤ B₀ x a d v₁
  le : v₁ ≤ v₂
  upper : ∀ x, ∀ a ∈ Γ₀ x, ∀ d ∈ D₀ x a, B₀ x a d v₂ ≤ v₂ x
  concave : ∀ x, ∀ a ∈ Γ₀ x, ∀ d ∈ D₀ x a, ConcaveOn ℝ univ (B₀ x a d)

variable {Γ₀ D₀ B₀}

namespace AdvConditions

variable {v₁ v₂ : X → ℝ} {ε : ℝ} (h : AdvConditions Γ₀ D₀ B₀ v₁ v₂ ε)
include h

omit [Fintype X] [Fintype A] in
/-- On `[v₁, v₂]` each `d ↦ B(x, a, d, v)` is bounded below by `v₁(x) + ε`. -/
theorem lower_mem {x : X} {a : A} (ha : a ∈ Γ₀ x) {v : X → ℝ} (hv : v ∈ Icc v₁ v₂) (d : D₀ x a) :
    v₁ x + ε ≤ B₀ x a d v :=
  (h.lower x a ha d d.2).trans (h.mono x a ha d d.2 hv.1)

omit [Fintype X] [Fintype A] in
theorem bddBelow {x : X} {a : A} (ha : a ∈ Γ₀ x) {v : X → ℝ} (hv : v ∈ Icc v₁ v₂) :
    BddBelow (range fun d : D₀ x a => B₀ x a d v) :=
  ⟨v₁ x + ε, by rintro _ ⟨d, rfl⟩; exact h.lower_mem ha hv d⟩

omit [Fintype X] [Fintype A] in
theorem le_advB {x : X} {a : A} (ha : a ∈ Γ₀ x) {v : X → ℝ} (hv : v ∈ Icc v₁ v₂) :
    v₁ x + ε ≤ advB D₀ B₀ x a v :=
  have := (h.nonempty x a ha).to_subtype
  le_ciInf fun d => h.lower_mem ha hv d

omit [Fintype X] [Fintype A] in
theorem advB_le {x : X} {a : A} (ha : a ∈ Γ₀ x) {v : X → ℝ} (hv : v ∈ Icc v₁ v₂) {d : D}
    (hd : d ∈ D₀ x a) : advB D₀ B₀ x a v ≤ B₀ x a d v :=
  ciInf_le (h.bddBelow ha hv) ⟨d, hd⟩

omit [Fintype X] [Fintype A] in
theorem advB_mono {x : X} {a : A} (ha : a ∈ Γ₀ x) {v w : X → ℝ} (hv : v ∈ Icc v₁ v₂)
    (hvw : v ≤ w) : advB D₀ B₀ x a v ≤ advB D₀ B₀ x a w :=
  have := (h.nonempty x a ha).to_subtype
  ciInf_mono (h.bddBelow ha hv) fun d => h.mono x a ha d d.2 hvw

omit [Fintype X] [Fintype A] in
/-- (8.44): `v₁(x) < B̂(x, a, v)` and `B̂(x, a, v) ≤ v₂(x)` on `[v₁, v₂]`. -/
theorem advB_mem {x : X} {a : A} (ha : a ∈ Γ₀ x) {v : X → ℝ} (hv : v ∈ Icc v₁ v₂) :
    advB D₀ B₀ x a v ∈ Icc (v₁ x) (v₂ x) := by
  obtain ⟨d, hd⟩ := h.nonempty x a ha
  exact ⟨by linarith [h.le_advB ha hv, h.eps_pos],
    (h.advB_le ha hv hd).trans ((h.mono x a ha d hd hv.2).trans (h.upper x a ha d hd))⟩

end AdvConditions

/-- The adversarial RDP `(Γ, [v₁, v₂], B̂)` of §8.3.2.1. -/
noncomputable def adversarialRDP (hΓ : ∀ x, (Γ₀ x).Nonempty) {v₁ v₂ : X → ℝ} {ε : ℝ}
    (h : AdvConditions Γ₀ D₀ B₀ v₁ v₂ ε) : RDP X A where
  Γ := Γ₀
  Γ_nonempty := hΓ
  V := Icc v₁ v₂
  B := advB D₀ B₀
  mono := fun _ _ ha _ hv _ _ hvw => h.advB_mono ha hv hvw
  consistent := fun _ hσ _ hv => ⟨fun x => (h.advB_mem (hσ x) hv).1,
    fun x => (h.advB_mem (hσ x) hv).2⟩

/-- **Proposition 8.3.2** (p. 278): under (a)–(d), `(Γ, [v₁, v₂], B̂)` is a concave RDP. -/
theorem adversarialRDP_isConcaveRDP (hΓ : ∀ x, (Γ₀ x).Nonempty) {v₁ v₂ : X → ℝ} {ε : ℝ}
    (h : AdvConditions Γ₀ D₀ B₀ v₁ v₂ ε) : (adversarialRDP hΓ h).IsConcaveRDP v₁ v₂ := by
  refine ⟨h.le, rfl, fun x a ha => ⟨convex_Icc _ _, fun v hv w hw s t hs ht hst => ?_⟩, ?_⟩
  · have := (h.nonempty x a ha).to_subtype
    have hvw : s • v + t • w ∈ Icc v₁ v₂ := convex_Icc v₁ v₂ hv hw hs ht hst
    change s • advB D₀ B₀ x a v + t • advB D₀ B₀ x a w ≤ advB D₀ B₀ x a (s • v + t • w)
    have hbs : BddBelow (range fun d : D₀ x a => s * B₀ x a d v) := by
      obtain ⟨m, hm⟩ := h.bddBelow ha hv
      exact ⟨s * m, by rintro _ ⟨d, rfl⟩; exact mul_le_mul_of_nonneg_left (hm ⟨d, rfl⟩) hs⟩
    have hbt : BddBelow (range fun d : D₀ x a => t * B₀ x a d w) := by
      obtain ⟨m, hm⟩ := h.bddBelow ha hw
      exact ⟨t * m, by rintro _ ⟨d, rfl⟩; exact mul_le_mul_of_nonneg_left (hm ⟨d, rfl⟩) ht⟩
    simp only [advB, smul_eq_mul]
    rw [Real.mul_iInf_of_nonneg hs, Real.mul_iInf_of_nonneg ht]
    refine (iInf_add_iInf_le hbs hbt).trans (ciInf_mono ?_ fun d => ?_)
    · obtain ⟨m, hm⟩ := hbs
      obtain ⟨m', hm'⟩ := hbt
      exact ⟨m + m', by rintro _ ⟨d, rfl⟩; exact add_le_add (hm ⟨d, rfl⟩) (hm' ⟨d, rfl⟩)⟩
    · have := (h.concave x a ha d d.2).2 (mem_univ v) (mem_univ w) hs ht hst
      simpa only [smul_eq_mul] using this
  · refine RDP.exists_delta_concave _ h.le fun x a ha => ?_
    have := h.le_advB ha ⟨le_rfl, h.le⟩
    change v₁ x < advB D₀ B₀ x a v₁
    linarith [h.eps_pos]

/-- Proposition 8.3.2 with Proposition 8.2.5: the adversarial RDP is globally stable, so
Theorem 8.1.1 applies. -/
theorem adversarialRDP_isGloballyStable (hΓ : ∀ x, (Γ₀ x).Nonempty) {v₁ v₂ : X → ℝ} {ε : ℝ}
    (h : AdvConditions Γ₀ D₀ B₀ v₁ v₂ ε) : (adversarialRDP hΓ h).IsGloballyStable :=
  (adversarialRDP_isConcaveRDP hΓ h).isGloballyStable

/-! ### The perturbed MDP (§8.3.2.2) -/

/-- The perturbed MDP of §8.3.2.2: rewards `r(x, a, d)` in `[r₁, r₂]` and kernels `P(x, a, d, ·)`
that are distributions, for the adversary's `d ∈ D(x, a)`. -/
structure PerturbedMDP (X A D : Type*) [Fintype X] [Fintype A] where
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  Dset : X → A → Set D
  Dset_nonempty : ∀ x a, (Dset x a).Nonempty
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  r : X → A → D → ℝ
  r₁ : ℝ
  r₂ : ℝ
  r_bounds : ∀ x a, ∀ d ∈ Dset x a, r₁ ≤ r x a d ∧ r x a d ≤ r₂
  P : X → A → D → X → ℝ
  P_nonneg : ∀ x a, ∀ d ∈ Dset x a, ∀ x', 0 ≤ P x a d x'
  P_rowsum : ∀ x a, ∀ d ∈ Dset x a, ∑ x', P x a d x' = 1

namespace PerturbedMDP

variable {X A D : Type*} [Fintype X] [Fintype A] (M : PerturbedMDP X A D)

/-- `B(x, a, d, v) = r(x, a, d) + β ∑ v(x')P(x, a, d, x')`, as in (8.46). -/
def Bd (x : X) (a : A) (d : D) (v : X → ℝ) : ℝ := M.r x a d + M.β * ∑ x', v x' * M.P x a d x'

/-- The constant `v₁ = (r₁ − ε)/(1 − β)` of (8.47). -/
noncomputable def v₁ (ε : ℝ) : X → ℝ := fun _ => (M.r₁ - ε) / (1 - M.β)

/-- The constant `v₂ = r₂/(1 − β)` of (8.47). -/
noncomputable def v₂ : X → ℝ := fun _ => M.r₂ / (1 - M.β)

theorem Bd_const (x : X) (a : A) {d : D} (hd : d ∈ M.Dset x a) (c : ℝ) :
    M.Bd x a d (fun _ => c) = M.r x a d + M.β * c := by
  simp only [Bd]
  rw [← Finset.mul_sum, M.P_rowsum x a d hd, mul_one]

/-- **Exercise 8.3.4** (p. 280) with conditions (a) and (d): the perturbed MDP satisfies
conditions (a)–(d) of §8.3.2.1 for `v₁, v₂` in (8.47), for any `ε > 0`. -/
theorem advConditions {ε : ℝ} (hε : 0 < ε) : AdvConditions M.Γ M.Dset M.Bd (M.v₁ ε) M.v₂ ε where
  nonempty := fun x a _ => M.Dset_nonempty x a
  mono := fun x a _ d hd v w hvw => add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (hvw x') (M.P_nonneg x a d hd x'))
    M.β_pos.le)
  eps_pos := hε
  lower := fun x a _ d hd => by
    have hβ1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
    change (M.r₁ - ε) / (1 - M.β) + ε ≤ M.Bd x a d (fun _ => (M.r₁ - ε) / (1 - M.β))
    rw [M.Bd_const x a hd]
    have h1 := (M.r_bounds x a d hd).1
    have e : (M.r₁ - ε) / (1 - M.β) + ε = M.r₁ - ε + M.β * ((M.r₁ - ε) / (1 - M.β)) + ε := by
      field_simp
      ring
    rw [e]
    nlinarith [M.β_pos]
  le := fun x => by
    obtain ⟨a, ha⟩ := M.Γ_nonempty x
    obtain ⟨d, hd⟩ := M.Dset_nonempty x a
    have h := M.r_bounds x a d hd
    have hβ1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
    exact div_le_div_of_nonneg_right (by linarith [h.1.trans h.2]) hβ1.le
  upper := fun x a _ d hd => by
    have hβ1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
    change M.Bd x a d (fun _ => M.r₂ / (1 - M.β)) ≤ M.r₂ / (1 - M.β)
    rw [M.Bd_const x a hd]
    have h1 := (M.r_bounds x a d hd).2
    have e : M.r₂ / (1 - M.β) = M.r₂ + M.β * (M.r₂ / (1 - M.β)) := by
      field_simp
      ring
    rw [e]
    nlinarith [M.β_pos]
  concave := fun x a _ d hd => ⟨convex_univ, fun v _ w _ s t _ _ hst => le_of_eq (by
    simp only [Bd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : ∑ x', (s * v x' + t * w x') * M.P x a d x' =
        s * ∑ x', v x' * M.P x a d x' + t * ∑ x', w x' * M.P x a d x' := by
      rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun _ _ => by ring
    rw [e]
    obtain rfl : t = 1 - s := by linarith
    ring)⟩

/-- **Lemma 8.3.3** (p. 280): the perturbed MDP `(Γ, V, B̂)` is a concave RDP, hence globally
stable (Proposition 8.2.5) and Theorem 8.1.1 applies. -/
theorem isConcaveRDP {ε : ℝ} (hε : 0 < ε) :
    (adversarialRDP M.Γ_nonempty (M.advConditions hε)).IsConcaveRDP (M.v₁ ε) M.v₂ :=
  adversarialRDP_isConcaveRDP _ _

end PerturbedMDP

/-! ### Robust control (§8.3.3.1) -/

variable {X A : Type*} [Fintype X] [Fintype A]

/-- Robust control (8.48) as a perturbed MDP (8.49): the adversary chooses the kernel row
`p ∈ 𝒫(x, a)`, a nonempty set of distributions, and `r(x, a)` does not depend on it. -/
noncomputable def robustMDP (Γ : X → Finset A) (hΓ : ∀ x, (Γ x).Nonempty) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (r : X → A → ℝ) {r₁ r₂ : ℝ} (hr : ∀ x a, r₁ ≤ r x a ∧ r x a ≤ r₂)
    (Pset : X → A → Set (X → ℝ)) (hne : ∀ x a, (Pset x a).Nonempty)
    (hdist : ∀ x a, ∀ p ∈ Pset x a, IsDistribution p) : PerturbedMDP X A (X → ℝ) where
  Γ := Γ
  Γ_nonempty := hΓ
  Dset := Pset
  Dset_nonempty := hne
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := fun x a _ => r x a
  r₁ := r₁
  r₂ := r₂
  r_bounds := fun x a _ _ => hr x a
  P := fun _ _ p x' => p x'
  P_nonneg := fun x a p hp x' => (hdist x a p hp).nonneg x'
  P_rowsum := fun x a p hp => (hdist x a p hp).sum_eq_one

/-- (8.48) = (8.49) (p. 281): the robust aggregator `r(x, a) + β inf_p ∑ v(x')p(x')` is the
perturbed-MDP aggregator `inf_p {r(x, a) + β ∑ v(x')p(x')}`. -/
theorem robustMDP_advB (Γ : X → Finset A) (hΓ : ∀ x, (Γ x).Nonempty) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (r : X → A → ℝ) {r₁ r₂ : ℝ} (hr : ∀ x a, r₁ ≤ r x a ∧ r x a ≤ r₂)
    (Pset : X → A → Set (X → ℝ)) (hne : ∀ x a, (Pset x a).Nonempty)
    (hdist : ∀ x a, ∀ p ∈ Pset x a, IsDistribution p) (x : X) (a : A) (v : X → ℝ) :
    advB (robustMDP Γ hΓ hβ0 hβ1 r hr Pset hne hdist).Dset
        (robustMDP Γ hΓ hβ0 hβ1 r hr Pset hne hdist).Bd x a v =
      r x a + β * ⨅ p : Pset x a, ∑ x', v x' * p.1 x' := by
  have := (hne x a).to_subtype
  have hbdd : BddBelow (range fun p : Pset x a => ∑ x', v x' * p.1 x') := by
    refine ⟨-‖v‖, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hd := hdist x a p.1 p.2
    calc -‖v‖ = ∑ x', -‖v‖ * p.1 x' := by rw [← Finset.mul_sum, hd.sum_eq_one, mul_one]
      _ ≤ ∑ x', v x' * p.1 x' := sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right
          (by have := norm_le_pi_norm v x'; rw [Real.norm_eq_abs] at this
              linarith [neg_abs_le (v x')]) (hd.nonneg x')
  rw [add_mul_iInf hbdd _ hβ0.le]
  rfl

/-- **Proposition 8.3.4** (p. 281): the robust control RDP is a concave RDP on `V` of (8.47), hence
globally stable. -/
theorem robustMDP_isConcaveRDP (Γ : X → Finset A) (hΓ : ∀ x, (Γ x).Nonempty) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (r : X → A → ℝ) {r₁ r₂ : ℝ} (hr : ∀ x a, r₁ ≤ r x a ∧ r x a ≤ r₂)
    (Pset : X → A → Set (X → ℝ)) (hne : ∀ x a, (Pset x a).Nonempty)
    (hdist : ∀ x a, ∀ p ∈ Pset x a, IsDistribution p) {ε : ℝ} (hε : 0 < ε) :
    let M := robustMDP Γ hΓ hβ0 hβ1 r hr Pset hne hdist
    (adversarialRDP M.Γ_nonempty (M.advConditions hε)).IsConcaveRDP (M.v₁ ε) M.v₂ :=
  PerturbedMDP.isConcaveRDP _ hε

/-- `p ↦ ∑ v p` is bounded below, by `−‖v‖`, on any set of distributions. -/
theorem bddBelow_sum_mul_dist {W : Type*} [Fintype W] (Φ : Set (W → ℝ))
    (hdist : ∀ φ ∈ Φ, IsDistribution φ) (v : W → ℝ) :
    BddBelow (range fun φ : Φ => ∑ w', v w' * φ.1 w') := by
  refine ⟨-‖v‖, ?_⟩
  rintro _ ⟨φ, rfl⟩
  have hd := hdist φ.1 φ.2
  calc -‖v‖ = ∑ w', -‖v‖ * φ.1 w' := by rw [← Finset.mul_sum, hd.sum_eq_one, mul_one]
    _ ≤ ∑ w', v w' * φ.1 w' := sum_le_sum fun w' _ => mul_le_mul_of_nonneg_right
        (by have := norm_le_pi_norm v w'; rw [Real.norm_eq_abs] at this
            linarith [neg_abs_le (v w')]) (hd.nonneg w')

variable {W : Type*} [Fintype W]

/-- **Example 8.3.1** (p. 281): robust job search, the worker distrusting the wage offer
distribution and using the worst case over a nonempty set `Φ` of distributions. The continuation
value is taken as `c + β inf_{φ ∈ Φ} ∑ v φ` (printed without `c` and `β`). -/
noncomputable def robustJobSearch (wage : W → ℝ) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β) (Φ : Set (W → ℝ))
    (hΦ : Φ.Nonempty) (hdist : ∀ φ ∈ Φ, IsDistribution φ) : RDP W Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  V := univ
  B := fun w a v => bif a then wage w / (1 - β) else c + β * ⨅ φ : Φ, ∑ w', v w' * φ.1 w'
  mono := fun w a _ v _ v' _ hvv' => by
    have := hΦ.to_subtype
    cases a
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (ciInf_mono
        (bddBelow_sum_mul_dist Φ hdist v) fun φ => sum_le_sum fun w' _ =>
          mul_le_mul_of_nonneg_right (hvv' w') ((hdist φ.1 φ.2).nonneg w')) hβ)
    · exact le_rfl
  consistent := fun _ _ _ _ => mem_univ _

/-- Example 8.3.1: robust job search satisfies Blackwell's condition with modulus `β < 1`, so it is
contracting and globally stable. -/
theorem robustJobSearch_isContracting (wage : W → ℝ) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (Φ : Set (W → ℝ)) (hΦ : Φ.Nonempty) (hdist : ∀ φ ∈ Φ, IsDistribution φ) :
    (robustJobSearch wage c hβ Φ hΦ hdist).IsContracting β := by
  have := hΦ.to_subtype
  refine RDP.SatisfiesBlackwell.isContracting ⟨hβ, hβ1, fun _ _ _ _ => mem_univ _,
    fun w a _ v _ k _ => ?_⟩
  cases a
  · apply le_of_eq
    change c + β * ⨅ φ : Φ, ∑ w', (v + fun _ => k : W → ℝ) w' * φ.1 w' =
      c + β * (⨅ φ : Φ, ∑ w', v w' * φ.1 w') + β * k
    have e : (fun φ : Φ => ∑ w', (v + fun _ => k : W → ℝ) w' * φ.1 w') =
        fun φ => k + 1 * ∑ w', v w' * φ.1 w' := funext fun φ => by
      simp only [Pi.add_apply, add_mul, sum_add_distrib, ← Finset.mul_sum,
        (hdist φ.1 φ.2).sum_eq_one, mul_one, one_mul]
      ring
    rw [e, ← add_mul_iInf (bddBelow_sum_mul_dist Φ hdist v) k zero_le_one]
    ring
  · change wage w / (1 - β) ≤ wage w / (1 - β) + β * k
    nlinarith

/-- §8.3.3.2 (p. 282), (8.50): a penalty `d(p)` is absorbed into the reward:
`r + β inf_p {∑ v p + d(p)} = inf_p {r̂(p) + β ∑ v p}` with `r̂(p) = r + βd(p)`. -/
theorem penalty_absorbed {X ι : Type*} [Fintype X] [Nonempty ι] (p : ι → X → ℝ) (d : ι → ℝ)
    (v : X → ℝ) (hb : BddBelow (range fun i => ∑ x', v x' * p i x' + d i)) (r : ℝ) {β : ℝ}
    (hβ : 0 ≤ β) :
    r + β * ⨅ i, (∑ x', v x' * p i x' + d i) = ⨅ i, ((r + β * d i) + β * ∑ x', v x' * p i x') := by
  rw [add_mul_iInf hb r hβ]
  exact congrArg _ (funext fun i => by ring)

/-! ### KL divergence and risk sensitivity (§8.3.3.3) -/

variable {X : Type*} [Fintype X]

/-- The Kullback–Leibler divergence `d_KL(q | p) = ∑ q(x) ln(q(x)/p(x))` (p. 282); terms with
`q(x) = 0` vanish. -/
noncomputable def klDiv (q p : X → ℝ) : ℝ := ∑ x, q x * Real.log (q x / p x)

/-- `q ≺ac p`: `q(x) = 0` whenever `p(x) = 0`. -/
def AbsCont (q p : X → ℝ) : Prop := ∀ x, p x = 0 → q x = 0

/-- The normaliser `∑ exp(h(x))p(x)` is positive for a distribution `p`. -/
theorem sum_exp_mul_pos {p : X → ℝ} (hp : IsDistribution p) (h : X → ℝ) :
    0 < ∑ x, Real.exp (h x) * p x := by
  obtain ⟨x, hx⟩ : ∃ x, 0 < p x := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have : ∑ x, p x ≤ 0 := sum_nonpos fun x _ => hcon x
    linarith [hp.sum_eq_one]
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hx) (single_le_sum
    (f := fun x => Real.exp (h x) * p x) (fun y _ => mul_nonneg (Real.exp_pos _).le (hp.nonneg y))
    (mem_univ x))

/-- (8.51), upper bound: `∑ h q − d_KL(q | p) ≤ ln ∑ exp(h)p` for distributions `q ≺ac p`. -/
theorem sum_mul_sub_klDiv_le {p q : X → ℝ} (hp : IsDistribution p) (hq : IsDistribution q)
    (hac : AbsCont q p) (h : X → ℝ) :
    ∑ x, h x * q x - klDiv q p ≤ Real.log (∑ x, Real.exp (h x) * p x) := by
  set Z := ∑ x, Real.exp (h x) * p x
  have hZ : 0 < Z := sum_exp_mul_pos hp h
  have key : ∀ x, h x * q x - q x * Real.log (q x / p x) - q x * Real.log Z ≤
      Real.exp (h x) * p x / Z - q x := by
    intro x
    rcases (hq.nonneg x).lt_or_eq with hqx | hqx
    · have hpx : 0 < p x := by
        rcases (hp.nonneg x).lt_or_eq with h' | h'
        · exact h'
        · exact absurd (hac x h'.symm) hqx.ne'
      have ht : 0 < Real.exp (h x) * p x / (q x * Z) :=
        div_pos (mul_pos (Real.exp_pos _) hpx) (mul_pos hqx hZ)
      have hlog : Real.log (Real.exp (h x) * p x / (q x * Z)) =
          h x - Real.log (q x / p x) - Real.log Z := by
        rw [Real.log_div (mul_pos (Real.exp_pos _) hpx).ne' (mul_pos hqx hZ).ne',
          Real.log_mul (Real.exp_pos _).ne' hpx.ne', Real.log_mul hqx.ne' hZ.ne', Real.log_exp,
          Real.log_div hqx.ne' hpx.ne']
        ring
      have h1 := Real.log_le_sub_one_of_pos ht
      rw [hlog] at h1
      have h2 : q x * (Real.exp (h x) * p x / (q x * Z) - 1) = Real.exp (h x) * p x / Z - q x := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left h1 hqx.le]
    · rw [← hqx]
      simp only [mul_zero, zero_mul, sub_zero, zero_div]
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le (hp.nonneg x)) hZ.le
  have hL : ∑ x, (h x * q x - q x * Real.log (q x / p x) - q x * Real.log Z) =
      ∑ x, h x * q x - klDiv q p - Real.log Z := by
    rw [sum_sub_distrib, sum_sub_distrib, ← Finset.sum_mul, hq.sum_eq_one, one_mul]
    rfl
  have hR : ∑ x, (Real.exp (h x) * p x / Z - q x) = 0 := by
    rw [sum_sub_distrib, ← Finset.sum_div, div_self hZ.ne', hq.sum_eq_one, sub_self]
  have hsum := sum_le_sum fun x (_ : x ∈ (Finset.univ : Finset X)) => key x
  rw [hL, hR] at hsum
  linarith

/-- The maximiser in (8.51), `q*(x) = exp(h(x))p(x) / ∑ exp(h)p`. -/
noncomputable def gibbs (p h : X → ℝ) : X → ℝ :=
  fun x => Real.exp (h x) * p x / ∑ y, Real.exp (h y) * p y

theorem isDistribution_gibbs {p : X → ℝ} (hp : IsDistribution p) (h : X → ℝ) :
    IsDistribution (gibbs p h) :=
  ⟨fun x => div_nonneg (mul_nonneg (Real.exp_pos _).le (hp.nonneg x)) (sum_exp_mul_pos hp h).le,
    by unfold gibbs; rw [← Finset.sum_div, div_self (sum_exp_mul_pos hp h).ne']⟩

theorem absCont_gibbs (p h : X → ℝ) : AbsCont (gibbs p h) p := fun x hx => by
  simp [gibbs, hx]

/-- (8.51), attained: `∑ h q* − d_KL(q* | p) = ln ∑ exp(h)p`. -/
theorem sum_mul_sub_klDiv_gibbs {p : X → ℝ} (hp : IsDistribution p) (h : X → ℝ) :
    ∑ x, h x * gibbs p h x - klDiv (gibbs p h) p = Real.log (∑ x, Real.exp (h x) * p x) := by
  have hZ := sum_exp_mul_pos hp h
  set Z := ∑ x, Real.exp (h x) * p x with hZdef
  have hterm : ∀ x, gibbs p h x * Real.log (gibbs p h x / p x) =
      gibbs p h x * h x - gibbs p h x * Real.log Z := by
    intro x
    rcases (hp.nonneg x).lt_or_eq with hpx | hpx
    · have e : gibbs p h x / p x = Real.exp (h x) / Z := by
        simp only [gibbs, ← hZdef]
        field_simp
      rw [e, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
      ring
    · simp [gibbs, ← hpx]
  have hg := (isDistribution_gibbs hp h).sum_eq_one
  unfold klDiv
  simp only [hterm, sum_sub_distrib]
  rw [← Finset.sum_mul, hg, one_mul]
  have hs : ∑ x, gibbs p h x * h x = ∑ x, h x * gibbs p h x :=
    sum_congr rfl fun _ _ => mul_comm _ _
  linarith

/-- **The variational formula (8.51)** (p. 283), for distributions on a finite set:
`ln ∑ exp(h(x))p(x) = max_{q ≺ac p} {∑ h(x)q(x) − d_KL(q | p)}`. -/
theorem klDuality {p : X → ℝ} (hp : IsDistribution p) (h : X → ℝ) :
    IsGreatest {y | ∃ q, IsDistribution q ∧ AbsCont q p ∧ y = ∑ x, h x * q x - klDiv q p}
      (Real.log (∑ x, Real.exp (h x) * p x)) :=
  ⟨⟨gibbs p h, isDistribution_gibbs hp h, absCont_gibbs p h, (sum_mul_sub_klDiv_gibbs hp h).symm⟩,
    by rintro y ⟨q, hq, hac, rfl⟩; exact sum_mul_sub_klDiv_le hp hq hac h⟩

/-- §8.3.3.3 (p. 283): for `θ < 0`, with `d_θ = −(1/θ)d_KL`,
`(1/θ) ln ∑ exp(θv(x))p(x) = min_{q ≺ac p} {∑ v(x)q(x) + d_θ(q | p)}`. -/
theorem entropic_isLeast {θ : ℝ} (hθ : θ < 0) {p : X → ℝ} (hp : IsDistribution p) (v : X → ℝ) :
    IsLeast {y | ∃ q, IsDistribution q ∧ AbsCont q p ∧ y = ∑ x, v x * q x - θ⁻¹ * klDiv q p}
      (θ⁻¹ * Real.log (∑ x, Real.exp (θ * v x) * p x)) := by
  have hinv : θ⁻¹ < 0 := inv_lt_zero.2 hθ
  have hθ0 : θ ≠ 0 := hθ.ne
  have e : ∀ q : X → ℝ, θ⁻¹ * (∑ x, θ * v x * q x - klDiv q p) =
      ∑ x, v x * q x - θ⁻¹ * klDiv q p := fun q => by
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact sum_congr rfl fun x _ => by field_simp
  refine ⟨⟨gibbs p (fun x => θ * v x), isDistribution_gibbs hp _, absCont_gibbs p _, ?_⟩, ?_⟩
  · have h0 : ∑ x, θ * v x * gibbs p (fun x => θ * v x) x - klDiv (gibbs p (fun x => θ * v x)) p =
        Real.log (∑ x, Real.exp (θ * v x) * p x) := sum_mul_sub_klDiv_gibbs hp _
    rw [← h0, e]
  · rintro y ⟨q, hq, hac, rfl⟩
    have hle : ∑ x, θ * v x * q x - klDiv q p ≤ Real.log (∑ x, Real.exp (θ * v x) * p x) :=
      sum_mul_sub_klDiv_le hp hq hac fun x => θ * v x
    rw [← e]
    exact mul_le_mul_of_nonpos_left hle hinv.le

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- §8.3.3.3 (p. 283): for `θ < 0`, the robust control aggregator (8.50) with the KL penalty
`d_θ = −(1/θ)d_KL` over all `q ≺ac P(x, a, ·)` is the risk-sensitive aggregator (8.9) under the
baseline kernel. -/
theorem riskSensitive_B_eq_robust {θ : ℝ} (hθ : θ < 0) (x : X) (a : A) (v : X → ℝ) :
    (M.riskSensitive hθ.ne).B x a v = M.r x a + M.β * sInf {y | ∃ q, IsDistribution q ∧
      AbsCont q (M.P x a) ∧ y = ∑ x', v x' * q x' - θ⁻¹ * klDiv q (M.P x a)} := by
  rw [(entropic_isLeast hθ ⟨M.P_nonneg x a, M.P_rowsum x a⟩ v).csInf_eq, riskSensitive_B]
  ring

end MDP

end SargentStachurski.RecursiveDecisionProcesses
