/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.EventTrees
import AKMMCompetitiveEquilibrium.ADConsumer

/-!
# The infinite-horizon stochastic growth model on the event tree

AKMM, §7.3.2, (7.10)–(7.14), pp. 198–200.

The event tree is Miao's `BPTree` (see `EventTrees`). A plan assigns to each history `h = ωᵗ`
consumption `C h = Cₜ(ωᵗ)` and capital `K h = Kₜ₊₁(ωᵗ)`, chosen at `ωᵗ`; capital used at `ωᵗ`
is `pt_prevK K₀ K h = Kₜ(ωᵗ⁻¹)` (`K₀` at the root). The resource constraint (7.11) is
`Kₜ₊₁(ωᵗ) + Cₜ(ωᵗ) = f(Aₜ(ωᵗ), Kₜ(ωᵗ⁻¹))` (`pt_Resource`), utility (7.10) is
`Σₜ βᵗ Σ_{ωᵗ} πₜ(ωᵗ)u(Cₜ(ωᵗ))` (`pt_util`), and `pt_Optimal` is the planner's problem.

* The Lagrangian conditions `πₜβᵗu′(Cₜ) = λₜ` and (7.12) give the Euler equation (7.13)
  (`eq_7_12_7_13`), which is (7.14) `u′(Cₜ) = βEₜ[u′(Cₜ₊₁)f₂(Aₜ₊₁, Kₜ₊₁)]` written with the
  conditional expectation of the tree (`eq_7_14`).
* **(7.13) holds at every optimum with `Kₜ₊₁(ωᵗ) > 0`** (`eq_7_13`), proved from optimality by
  moving `ε` units of capital at `ωᵗ` (consumption falls by `ε` at `ωᵗ` and rises by
  `f(A, K + ε) − f(A, K)` at each successor), with Chapter 5's finite-perturbation lemma
  `ce_foc_of_perturb`.
* **Sufficiency with the transversality condition** (p. 199–200): if `u` and `f(A, ·)` are
  concave and increasing, a feasible plan satisfying (7.13) at every node and
  `βᵗ Σ_{ωᵗ} πₜu′(Cₜ)Kₜ₊₁ → 0` is optimal (`pt_euler_tvc_optimal`).
* **The closed form** (p. 200): with `u = log`, `f(A, K) = AK^α` (Cobb–Douglas, `δ = 1`) the
  constant saving rate `Kₜ₊₁ = αβAₜKₜ^α` satisfies (7.13) at every node (`pt_log_euler`) and the
  transversality condition (`pt_log_tvc`), and it is optimal whenever its utility series
  converges (`pt_log_optimal`), e.g. when TFP takes values in a compact subset of `(0, ∞)`
  (`pt_log_summable`).
-/

namespace AKMM.Uncertainty

open Miao.CompleteMarkets Filter Topology AKMM.CompetitiveEquilibrium

variable {S : Type*} [Fintype S] {α : Type*}

/-- Capital used at the history `h`: `K₀` at the root and `Kₜ(ωᵗ⁻¹) = K(ωᵗ⁻¹)` otherwise. -/
def pt_prevK (K0 : ℝ) (K : List S → ℝ) : List S → ℝ
  | [] => K0
  | _ :: g => K g

/-- AKMM, (7.11), p. 198: `Kₜ₊₁(ωᵗ) + Cₜ(ωᵗ) = f(Aₜ(ωᵗ), Kₜ(ωᵗ⁻¹))` at every history. -/
def pt_Resource (f : α → ℝ → ℝ) (A : List S → α) (K0 : ℝ) (C K : List S → ℝ) : Prop :=
  ∀ h, K h + C h = f (A h) (pt_prevK K0 K h)

/-- AKMM, (7.10), p. 198: the date-`t` term `βᵗ Σ_{ωᵗ} πₜ(ωᵗ)u(Cₜ(ωᵗ))`. -/
noncomputable def pt_util (T : BPTree S) (β : ℝ) (u : ℝ → ℝ) (C : List S → ℝ) (t : ℕ) : ℝ :=
  β ^ t * bp_nodeSum t (fun h => T.pr h * u (C h))

/-- A feasible plan: positive consumption, nonnegative capital, (7.11) and a convergent utility
series. -/
def pt_Feasible (T : BPTree S) (β : ℝ) (u : ℝ → ℝ) (f : α → ℝ → ℝ) (A : List S → α)
    (K0 : ℝ) (C K : List S → ℝ) : Prop :=
  (∀ h, 0 < C h) ∧ (∀ h, 0 ≤ K h) ∧ pt_Resource f A K0 C K ∧ Summable (pt_util T β u C)

/-- AKMM, p. 199: the planner maximises (7.10) subject to (7.11). -/
def pt_Optimal (T : BPTree S) (β : ℝ) (u : ℝ → ℝ) (f : α → ℝ → ℝ) (A : List S → α)
    (K0 : ℝ) (C K : List S → ℝ) : Prop :=
  pt_Feasible T β u f A K0 C K ∧ ∀ C' K', pt_Feasible T β u f A K0 C' K' →
    ∑' t, pt_util T β u C' t ≤ ∑' t, pt_util T β u C t

/-! ### The Lagrangian -/

/-- Dividing `p₀x = Σₛ βpₛyₛzₛ` by `p₀ ≠ 0` gives `x = β Σₛ (pₛ/p₀)yₛzₛ`. -/
theorem pt_euler_normalise {p0 x β : ℝ} {p y z : S → ℝ} (hp : p0 ≠ 0)
    (h : p0 * x = ∑ s, β * p s * y s * z s) : x = β * ∑ s, p s / p0 * y s * z s := by
  have e : ∀ s, β * (p s / p0 * y s * z s) = β * p s * y s * z s / p0 := fun s => by ring
  rw [Finset.mul_sum]
  simp only [e, ← Finset.sum_div, ← h]
  field_simp

/-- **AKMM, (7.12)–(7.13), p. 199.** If the multipliers satisfy `πₜ(ωᵗ)βᵗu′(Cₜ(ωᵗ)) = λₜ(ωᵗ)`
and (7.12) `λₜ(ωᵗ) = Σ_{ωᵗ⁺¹|ωᵗ} λₜ₊₁(ωᵗ⁺¹)f₂(Aₜ₊₁(ωᵗ⁺¹), Kₜ₊₁(ωᵗ))`, then (7.13)
`u′(Cₜ(ωᵗ)) = β Σ πₜ₊₁(ωᵗ⁺¹|ωᵗ)u′(Cₜ₊₁(ωᵗ⁺¹))f₂(Aₜ₊₁(ωᵗ⁺¹), Kₜ₊₁(ωᵗ))`. -/
theorem eq_7_12_7_13 (T : BPTree S) {β : ℝ} (hβ : 0 < β) {du : ℝ → ℝ}
    {f2 : α → ℝ → ℝ} {A : List S → α} {C K lam : List S → ℝ}
    (hC : ∀ h, T.pr h * β ^ h.length * du (C h) = lam h)
    (h712 : ∀ h, lam h = ∑ s, lam (s :: h) * f2 (A (s :: h)) (K h)) (h : List S) :
    du (C h) = β * ∑ s, T.pr (s :: h) / T.pr h * du (C (s :: h)) * f2 (A (s :: h)) (K h) := by
  have e := h712 h
  rw [← hC h] at e
  simp only [← hC, List.length_cons, pow_succ] at e
  have hb : β ^ h.length ≠ 0 := pow_ne_zero _ hβ.ne'
  refine pt_euler_normalise (T.pr_pos h).ne' (mul_left_cancel₀ hb ?_)
  rw [Finset.mul_sum]
  calc β ^ h.length * (T.pr h * du (C h)) = T.pr h * β ^ h.length * du (C h) := by ring
    _ = _ := e
    _ = _ := Finset.sum_congr rfl fun s _ => by ring

/-- **AKMM, (7.14), p. 199**: the right-hand side of (7.13) is `βEₜ[u′(Cₜ₊₁)f₂(Aₜ₊₁, Kₜ₊₁)]`,
the conditional expectation of the tree at `ωᵗ`. -/
theorem eq_7_14 (T : BPTree S) (β K0 : ℝ) (du : ℝ → ℝ) (f2 : α → ℝ → ℝ)
    (A : List S → α) (C K : List S → ℝ) (h : List S) :
    β * ∑ s, T.pr (s :: h) / T.pr h * du (C (s :: h)) * f2 (A (s :: h)) (K h) =
      β * bp_condExp T 1 (fun g => du (C g) * f2 (A g) (pt_prevK K0 K g)) h := by
  rw [bp_condExp_succ]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by rw [bp_condExp_zero, pt_prevK]; ring

/-! ### The Euler equation from optimality -/

variable [DecidableEq S]

/-- The capital perturbation: `ε` more capital chosen at `h₀`. -/
def pt_pertK (K : List S → ℝ) (h₀ : List S) (ε : ℝ) : List S → ℝ :=
  fun h => if h = h₀ then K h + ε else K h

/-- The consumption perturbation: `ε` less at `h₀`, `f(A, K + ε) − f(A, K)` more at each
successor of `h₀`. -/
def pt_pertC (f : α → ℝ → ℝ) (A : List S → α) (C K : List S → ℝ) (h₀ : List S) (ε : ℝ) :
    List S → ℝ :=
  fun h => if h = h₀ then C h - ε else
    match h with
    | [] => C h
    | _ :: g => if g = h₀ then C h + (f (A h) (K h₀ + ε) - f (A h) (K h₀)) else C h

omit [Fintype S] in
theorem pt_pertC_self (f : α → ℝ → ℝ) (A : List S → α) (C K : List S → ℝ) (h₀ : List S) (ε : ℝ) :
    pt_pertC f A C K h₀ ε h₀ = C h₀ - ε := by
  simp [pt_pertC]

omit [Fintype S] in
theorem pt_pertC_child (f : α → ℝ → ℝ) (A : List S → α) (C K : List S → ℝ) (h₀ : List S)
    (ε : ℝ) (s : S) :
    pt_pertC f A C K h₀ ε (s :: h₀) =
      C (s :: h₀) + (f (A (s :: h₀)) (K h₀ + ε) - f (A (s :: h₀)) (K h₀)) := by
  simp [pt_pertC, List.cons_ne_self]

omit [Fintype S] in
theorem pt_pertC_other (f : α → ℝ → ℝ) (A : List S → α) (C K : List S → ℝ) (h₀ : List S) (ε : ℝ)
    {h : List S} (h1 : h ≠ h₀) (h2 : ∀ s, h ≠ s :: h₀) : pt_pertC f A C K h₀ ε h = C h := by
  unfold pt_pertC
  simp only [h1, ↓reduceIte]
  match h, h2 with
  | [], _ => rfl
  | s :: g, h2 =>
    have : g ≠ h₀ := fun hg => h2 s (by rw [hg])
    simp [this]

omit [Fintype S] in
theorem pt_pert_resource {f : α → ℝ → ℝ} {A : List S → α} {C K : List S → ℝ} {K0 : ℝ}
    (hR : pt_Resource f A K0 C K) (h₀ : List S) (ε : ℝ) :
    pt_Resource f A K0 (pt_pertC f A C K h₀ ε) (pt_pertK K h₀ ε) := by
  intro h
  by_cases h1 : h = h₀
  · subst h1
    have hp : pt_prevK K0 (pt_pertK K h ε) h = pt_prevK K0 K h := by
      match h with
      | [] => rfl
      | s :: g =>
        have : g ≠ s :: g := fun e => List.cons_ne_self s g e.symm
        simp [pt_prevK, pt_pertK, this]
    rw [pt_pertC_self, hp, ← hR h]
    simp [pt_pertK]
  · match h, h1 with
    | [], h1 =>
      rw [pt_pertC_other f A C K h₀ ε h1 (fun s e => List.cons_ne_nil s h₀ e.symm)]
      have := hR []
      simp only [pt_prevK] at this ⊢
      simp only [pt_pertK, h1, ↓reduceIte]
      exact this
    | s :: g, h1 =>
      by_cases hg : g = h₀
      · subst hg
        rw [pt_pertC_child, show pt_prevK K0 (pt_pertK K g ε) (s :: g) = K g + ε by
          simp [pt_prevK, pt_pertK]]
        have := hR (s :: g)
        simp only [pt_prevK] at this
        simp only [pt_pertK, h1, ↓reduceIte]
        linarith
      · rw [pt_pertC_other f A C K h₀ ε h1 (fun s' e => hg (List.cons_eq_cons.1 e).2)]
        have := hR (s :: g)
        simp only [pt_prevK] at this ⊢
        simp only [pt_pertK, h1, hg, ↓reduceIte]
        exact this

omit [DecidableEq S] in
/-- **AKMM, (7.13), p. 199: the Euler equation holds at the optimum.** Let `β > 0`, `u`
differentiable on `(0, ∞)` and `f(A, ·)` differentiable on `(0, ∞)` with derivative `f₂`. If
`(C, K)` solves the planner's problem and `Kₜ₊₁(ωᵗ) > 0` at the history `h₀ = ωᵗ`, then
`u′(Cₜ(ωᵗ)) = β Σ_{ωᵗ⁺¹|ωᵗ} πₜ₊₁(ωᵗ⁺¹|ωᵗ)u′(Cₜ₊₁(ωᵗ⁺¹))f₂(Aₜ₊₁(ωᵗ⁺¹), Kₜ₊₁(ωᵗ))`. -/
theorem eq_7_13 (T : BPTree S) {β : ℝ} (hβ : 0 < β) {u du : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt u (du c) c) {f f2 : α → ℝ → ℝ}
    (hf : ∀ a k, 0 < k → HasDerivAt (f a) (f2 a k) k) {A : List S → α} {K0 : ℝ}
    {C K : List S → ℝ} (hopt : pt_Optimal T β u f A K0 C K) (h₀ : List S) (hK : 0 < K h₀) :
    du (C h₀) =
      β * ∑ s, T.pr (s :: h₀) / T.pr h₀ * du (C (s :: h₀)) * f2 (A (s :: h₀)) (K h₀) := by
  classical
  obtain ⟨⟨hCpos, hKnn, hR, hsum⟩, hmax⟩ := hopt
  set t₀ := h₀.length with ht₀
  set D : S → ℝ → ℝ := fun s ε => f (A (s :: h₀)) (K h₀ + ε) - f (A (s :: h₀)) (K h₀) with hD
  have hDd : ∀ s, HasDerivAt (D s) (f2 (A (s :: h₀)) (K h₀)) 0 := fun s => by
    have h1 : HasDerivAt (f (A (s :: h₀))) (f2 (A (s :: h₀)) (K h₀)) (K h₀ + 0) := by
      simpa using hf (A (s :: h₀)) (K h₀) hK
    have := (h1.comp_const_add (K h₀) 0).sub_const (f (A (s :: h₀)) (K h₀))
    exact this
  have hD0 : ∀ s, D s 0 = 0 := fun s => by simp [hD]
  -- the perturbed utility at dates `t₀` and `t₀ + 1`
  have hdate0 : ∀ ε, pt_util T β u (pt_pertC f A C K h₀ ε) t₀ =
      pt_util T β u C t₀ + β ^ t₀ * (T.pr h₀ * (u (C h₀ - ε) - u (C h₀))) := fun ε => by
    simp only [pt_util]
    rw [← mul_add]
    congr 1
    have hcongr := bp_nodeSum_congr t₀ (fun h => T.pr h * u (pt_pertC f A C K h₀ ε h))
      (fun h => T.pr h * u (C h) +
        if h = h₀ then T.pr h₀ * (u (C h₀ - ε) - u (C h₀)) else 0) (fun h hh => by
        by_cases h1 : h = h₀
        · subst h1; simp [pt_pertC_self]; ring
        · have h2 : ∀ s, h ≠ s :: h₀ := fun s e => by
            have := congrArg List.length e
            simp only [List.length_cons] at this
            omega
          simp [pt_pertC_other f A C K h₀ ε h1 h2, h1])
    rw [hcongr, bp_nodeSum_add, bp_nodeSum_single t₀ h₀ rfl]
  have hdate1 : ∀ ε, pt_util T β u (pt_pertC f A C K h₀ ε) (t₀ + 1) =
      pt_util T β u C (t₀ + 1) +
        β ^ (t₀ + 1) * ∑ s, T.pr (s :: h₀) * (u (C (s :: h₀) + D s ε) - u (C (s :: h₀))) :=
    fun ε => by
    simp only [pt_util]
    rw [← mul_add]
    congr 1
    rw [bp_nodeSum_succ, bp_nodeSum_succ]
    have hcongr := bp_nodeSum_congr t₀
      (fun h => ∑ s, T.pr (s :: h) * u (pt_pertC f A C K h₀ ε (s :: h)))
      (fun h => ∑ s, T.pr (s :: h) * u (C (s :: h)) +
        if h = h₀ then ∑ s, T.pr (s :: h₀) * (u (C (s :: h₀) + D s ε) - u (C (s :: h₀)))
        else 0) (fun h hh => by
        by_cases h1 : h = h₀
        · subst h1
          simp only [pt_pertC_child, ↓reduceIte, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun s _ => by simp only [hD]; ring
        · have hne : ∀ s, s :: h ≠ h₀ := fun s e => by
            have := congrArg List.length e
            simp only [List.length_cons] at this
            omega
          have hne2 : ∀ s s', s :: h ≠ s' :: h₀ := fun s s' e => h1 (List.cons_eq_cons.1 e).2
          simp only [h1, ↓reduceIte, add_zero]
          exact Finset.sum_congr rfl fun s _ => by
            rw [pt_pertC_other f A C K h₀ ε (hne s) (hne2 s)])
    rw [hcongr, bp_nodeSum_add, bp_nodeSum_single t₀ h₀ rfl]
  have hother : ∀ ε, ∀ t ∉ ({t₀, t₀ + 1} : Finset ℕ),
      pt_util T β u (pt_pertC f A C K h₀ ε) t = pt_util T β u C t := fun ε t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp only [pt_util]
    congr 1
    refine bp_nodeSum_congr t _ _ fun h hh => ?_
    have h1 : h ≠ h₀ := fun e => ht.1 (by rw [← hh, e])
    have h2 : ∀ s, h ≠ s :: h₀ := fun s e => ht.2 (by rw [← hh, e]; simp [ht₀])
    rw [pt_pertC_other f A C K h₀ ε h1 h2]
  have hzero : pt_pertC f A C K h₀ 0 = C := by
    funext h
    by_cases h1 : h = h₀
    · subst h1; simp [pt_pertC_self]
    · by_cases h2 : ∃ s, h = s :: h₀
      · obtain ⟨s, rfl⟩ := h2; simp [pt_pertC_child]
      · exact pt_pertC_other f A C K h₀ 0 h1 fun s e => h2 ⟨s, e⟩
  -- feasibility for small `ε`
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C h₀ - ε ∧ 0 ≤ K h₀ + ε ∧
      ∀ s, 0 < C (s :: h₀) + D s ε := by
    have c1 : ContinuousAt (fun ε : ℝ => C h₀ - ε) 0 := by fun_prop
    have c2 : ContinuousAt (fun ε : ℝ => K h₀ + ε) 0 := by fun_prop
    have e1 := continuousAt_const.eventually_lt c1 (show (0 : ℝ) < C h₀ - 0 by simpa using hCpos h₀)
    have e2 := continuousAt_const.eventually_lt c2 (show (0 : ℝ) < K h₀ + 0 by simpa using hK)
    have e3 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, 0 < C (s :: h₀) + D s ε := eventually_all.2 fun s =>
      continuousAt_const.eventually_lt (continuousAt_const.add (hDd s).continuousAt)
        (show (0 : ℝ) < C (s :: h₀) + D s 0 by simpa [hD0 s] using hCpos (s :: h₀))
    filter_upwards [e1, e2, e3] with ε h1 h2 h3
    exact ⟨h1, h2.le, h3⟩
  have hfeas : ∀ᶠ ε in 𝓝 (0 : ℝ), Summable (pt_util T β u (pt_pertC f A C K h₀ ε)) →
      ∑' t, pt_util T β u (pt_pertC f A C K h₀ ε) t ≤ ∑' t, pt_util T β u C t := by
    filter_upwards [hev] with ε ⟨h1, h2, h3⟩ hs
    refine hmax _ _ ⟨fun h => ?_, fun h => ?_, pt_pert_resource hR h₀ ε, hs⟩
    · by_cases e1 : h = h₀
      · subst e1; rw [pt_pertC_self]; exact h1
      · by_cases e2 : ∃ s, h = s :: h₀
        · obtain ⟨s, rfl⟩ := e2; rw [pt_pertC_child]; exact h3 s
        · rw [pt_pertC_other f A C K h₀ ε e1 fun s e => e2 ⟨s, e⟩]; exact hCpos h
    · simp only [pt_pertK]
      split_ifs with e
      · subst e; exact h2
      · exact hKnn h
  -- the derivative of the perturbed utility at dates `t₀, t₀ + 1`
  have hne : t₀ ≠ t₀ + 1 := by omega
  have hder : HasDerivAt (fun ε => ∑ t ∈ ({t₀, t₀ + 1} : Finset ℕ),
      pt_util T β u (pt_pertC f A C K h₀ ε) t)
      (β ^ t₀ * (T.pr h₀ * (du (C h₀) * (-1))) +
        β ^ (t₀ + 1) * ∑ s, T.pr (s :: h₀) * (du (C (s :: h₀)) * f2 (A (s :: h₀)) (K h₀))) 0 := by
    have e : (fun ε => ∑ t ∈ ({t₀, t₀ + 1} : Finset ℕ), pt_util T β u (pt_pertC f A C K h₀ ε) t) =
        fun ε => (pt_util T β u C t₀ + β ^ t₀ * (T.pr h₀ * (u (C h₀ - ε) - u (C h₀)))) +
          (pt_util T β u C (t₀ + 1) + β ^ (t₀ + 1) *
            ∑ s, T.pr (s :: h₀) * (u (C (s :: h₀) + D s ε) - u (C (s :: h₀)))) := by
      funext ε; rw [Finset.sum_pair hne, hdate0, hdate1]
    rw [e]
    have h1 : HasDerivAt (fun ε => u (C h₀ - ε)) (du (C h₀) * (-1)) 0 := by
      have hu0 : HasDerivAt u (du (C h₀)) (C h₀ - 0) := by simpa using hu _ (hCpos h₀)
      exact hu0.comp 0 ((hasDerivAt_id' (0 : ℝ)).const_sub (C h₀))
    have h2 : ∀ s, HasDerivAt (fun ε => u (C (s :: h₀) + D s ε))
        (du (C (s :: h₀)) * f2 (A (s :: h₀)) (K h₀)) 0 := fun s => by
      have hu0 : HasDerivAt u (du (C (s :: h₀))) (C (s :: h₀) + D s 0) := by
        simpa [hD0 s] using hu _ (hCpos (s :: h₀))
      exact hu0.comp 0 ((hDd s).const_add _)
    refine (((h1.sub_const _).const_mul _).const_mul _ |>.const_add _).add
      ((HasDerivAt.fun_sum fun s _ => ((h2 s).sub_const _).const_mul _).const_mul _
        |>.const_add _)
  have hz := ce_foc_of_perturb {t₀, t₀ + 1} hsum hother
    (fun t => by rw [hzero]) hfeas hder
  -- solve for `u′(C h₀)`
  have hb : β ^ t₀ ≠ 0 := pow_ne_zero _ hβ.ne'
  rw [pow_succ] at hz
  have e2 : β ^ t₀ * β * ∑ s, T.pr (s :: h₀) * (du (C (s :: h₀)) * f2 (A (s :: h₀)) (K h₀)) =
      β ^ t₀ * ∑ s, β * T.pr (s :: h₀) * du (C (s :: h₀)) * f2 (A (s :: h₀)) (K h₀) := by
    rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  refine pt_euler_normalise (T.pr_pos h₀).ne' (mul_left_cancel₀ hb ?_)
  linarith

end AKMM.Uncertainty
