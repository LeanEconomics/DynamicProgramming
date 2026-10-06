/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.Adversarial

/-!
# Epstein–Zin RDPs

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.1.4.1 (pp. 261–263).

For the Epstein–Zin RDP of Example 8.1.7 on `V = (0, ∞)^X`, with `θ = γ/α`:

* (8.23)–(8.24): the transformed RDP `R̂` with
  `B̂(x, a, v) = [r(x, a) + β(∑ v(x')P(x, a, x'))^{1/θ}]^θ` on `(0, ∞)^X`, written with the map
  `G` of Theorem 7.1.4.
* Exercise 8.1.19: `R` and `R̂` are topologically conjugate under `φ(t) = t^γ` on `(0, ∞)`.
* Lemma 8.1.5: if every `P_σ` is irreducible, `R̂` is globally stable (Theorem 7.1.4 with
  `ρ(β^θ P_σ)^{1/θ} = β < 1`).
* Proposition 8.1.4: if every `P_σ` is irreducible, `R` is globally stable, by
  Proposition 8.1.3; so Theorem 8.1.1 applies. The policy operators of `R` are the Epstein–Zin
  Koopmans operators (7.14), and Proposition 7.2.3 gives the same conclusion directly.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Every row of a Markov matrix has a positive entry. -/
theorem IsMarkov.exists_pos {X : Type*} [Fintype X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (x : X) : ∃ x', 0 < P x x' := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have : ∑ x', P x x' ≤ 0 := sum_nonpos fun x' _ => hcon x'
  linarith [hP.rowsum x]

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The matrix `β^θ P_a` of (8.24) is nonnegative, with a positive entry in every row. -/
theorem ezB_kernelAt_nonneg (θ : ℝ) (a : A) (x x' : X) :
    0 ≤ ezB (fun _ => M.β) θ (kernelAt M.P a) x x' :=
  mul_nonneg (Real.rpow_nonneg M.β_pos.le _) (M.P_nonneg x a x')

theorem ezB_kernelAt_row (θ : ℝ) (a : A) (x : X) :
    ∃ x', 0 < ezB (fun _ => M.β) θ (kernelAt M.P a) x x' := by
  obtain ⟨x', hx'⟩ := (M.isMarkov_P a).exists_pos x
  exact ⟨x', mul_pos (Real.rpow_pos_of_pos M.β_pos _) hx'⟩

/-- The transformed Epstein–Zin RDP `R̂` (8.23)–(8.24) on `V = (0, ∞)^X`:
`B̂(x, a, v) = [r(x, a) + (β^θ ∑ v(x')P(x, a, x'))^{1/θ}]^θ = [r(x, a) + β(∑ vP)^{1/θ}]^θ`. -/
noncomputable def epsteinZinHat (hr : ∀ x a, 0 < M.r x a) {θ : ℝ} (hθ : θ ≠ 0) : RDP X A where
  Γ := M.Γ
  Γ_nonempty := M.Γ_nonempty
  V := posCone X
  B := fun x a v => powG (ezB (fun _ => M.β) θ (kernelAt M.P a)) (fun y => M.r y a) θ v x
  mono := fun x a _ _ hv _ hw hvw => powG_monotoneOn (M.ezB_kernelAt_nonneg θ a)
    (M.ezB_kernelAt_row θ a) (fun y => (hr y a).le) hθ hv hw hvw x
  consistent := fun σ _ _ hv x => powG_mapsTo (M.ezB_kernelAt_nonneg θ (σ x))
    (M.ezB_kernelAt_row θ (σ x)) (fun y => (hr y (σ x)).le) θ hv x

/-- The policy operators of `R̂` are the maps `G` of Theorem 7.1.4 for `A = β^θ P_σ`, `h = r_σ`. -/
theorem epsteinZinHat_Tσ (hr : ∀ x a, 0 < M.r x a) {θ : ℝ} (hθ : θ ≠ 0) (σ : X → A) :
    (M.epsteinZinHat hr hθ).Tσ σ = powG (ezB (fun _ => M.β) θ (M.Pσ σ)) (M.rσ σ) θ := rfl

/-- **Lemma 8.1.5** (p. 262): if every `P_σ` is irreducible, `R̂` is globally stable. -/
theorem epsteinZinHat_isGloballyStable [DecidableEq X] [Nonempty X] (hr : ∀ x a, 0 < M.r x a)
    {θ : ℝ} (hθ : θ ≠ 0) (hirr : ∀ σ, M.toRDP.IsFeasible σ → Irreducible (M.Pσ σ)) :
    (M.epsteinZinHat hr hθ).IsGloballyStable := by
  intro σ hσ
  rw [epsteinZinHat_Tσ]
  refine globallyStableOn_powG (irreducible_ezB (fun _ => M.β_pos) θ (hirr σ hσ))
    (fun x => hr x (σ x)) hθ ?_
  have hB : ezB (fun _ => M.β) θ (M.Pσ σ) = M.β ^ θ • M.Pσ σ := by
    ext x x'
    simp [ezB, Pσ]
  rw [hB, specRad_smul_isMarkov (M.isMarkov_Pσ σ) (Real.rpow_nonneg M.β_pos.le _),
    Real.rpow_rpow_inv M.β_pos.le hθ]
  exact M.β_lt_one

/-- **Exercise 8.1.19** (p. 262): `B(x, a, v) = φ⁻¹[B̂(x, a, φ ∘ v)]` with `φ(t) = t^γ` and
`θ = γ/α`. -/
theorem epsteinZin_B_eq_conj (hr : ∀ x a, 0 < M.r x a) {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0)
    (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) :
    (M.epsteinZin hr hα hγ).B x a v =
      ((M.epsteinZinHat hr (div_ne_zero hγ hα)).B x a (fun x' => v x' ^ γ)) ^ γ⁻¹ := by
  have h := congrFun (powMap_ezK (M.isMarkov_P a) (fun y => (hr y a).le) (fun _ => M.β_pos) hα
    hγ hv) x
  have hpos : 0 < ezK (fun y => M.r y a) (fun _ => M.β) α γ (kernelAt M.P a) v x :=
    ezK_mapsTo (M.isMarkov_P a) (fun y => (hr y a).le) (fun _ => M.β_pos) α γ hv x
  change ezK (fun y => M.r y a) (fun _ => M.β) α γ (kernelAt M.P a) v x =
    (powG (ezB (fun _ => M.β) (γ / α) (kernelAt M.P a)) (fun y => M.r y a) (γ / α)
      (powMap γ v) x) ^ γ⁻¹
  rw [← h]
  exact (Real.rpow_rpow_inv hpos.le hγ).symm

/-- **Proposition 8.1.4** (p. 262): if every `P_σ` is irreducible, the Epstein–Zin RDP is
globally stable, via Exercise 8.1.19, Proposition 8.1.3 and Lemma 8.1.5. -/
theorem epsteinZin_isGloballyStable [DecidableEq X] [Nonempty X] (hr : ∀ x a, 0 < M.r x a)
    {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0)
    (hirr : ∀ σ, M.toRDP.IsFeasible σ → Irreducible (M.Pσ σ)) :
    (M.epsteinZin hr hα hγ).IsGloballyStable := by
  have hc : ContinuousOn (fun t : ℝ => t ^ γ) (Ioi 0) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)
  have hc' : ContinuousOn (fun t : ℝ => t ^ γ⁻¹) (Ioi 0) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)
  refine (RDP.isGloballyStable_iff_of_conj (R := M.epsteinZin hr hα hγ)
    (R' := M.epsteinZinHat hr (div_ne_zero hγ hα)) rfl
    (M := Ioi 0) (M' := Ioi 0) rfl rfl (fun t (ht : 0 < t) => Real.rpow_pos_of_pos ht γ)
    (fun t (ht : 0 < t) => Real.rpow_pos_of_pos ht γ⁻¹)
    (fun t (ht : 0 < t) => Real.rpow_inv_rpow ht.le hγ)
    (fun t (ht : 0 < t) => Real.rpow_rpow_inv ht.le hγ) hc hc'
    fun x a _ v hv => M.epsteinZin_B_eq_conj hr hα hγ x a hv).2 ?_
  exact M.epsteinZinHat_isGloballyStable hr _ hirr

/-- The policy operators of the Epstein–Zin RDP are the Koopmans operators (7.14) of `P_σ`. -/
theorem epsteinZin_Tσ (hr : ∀ x a, 0 < M.r x a) {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0)
    (σ : X → A) :
    (M.epsteinZin hr hα hγ).Tσ σ = ezK (M.rσ σ) (fun _ => M.β) α γ (M.Pσ σ) := rfl

end MDP

end SargentStachurski.RecursiveDecisionProcesses
