/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.EUEulerSufficiency
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# §7.5: Theorem 7.5.1 (Kamihigashi), necessity of the transversality condition

Miao, §7.5, pp. 224–225, in the Euler class `eu_EulerModel` (`X ⊆ ℝⁿ`, here `Fin n → ℝ`).

The proof shifts the continuation plan from date `T + 1` down by a factor `λ`:
`(x₀, x*₁, …, x*_T, λx*_{T+1}, λx*_{T+2}, …)`, compares it with `x*` by optimality, bounds the
tail by inequality (7.38) with `γ = ξ`, and lets `λ → 1` and then `T → ∞`.

* `eu_smul_mem`, `eu_cone_feasible`: with `X` convex, `0 ∈ X`, `0 ∈ Γ(0, z)` and the convex graph
  of Assumption 6.4.11, `(λx_t, λx_{t+1})` is feasible whenever `(x_t, x_{t+1})` is,
  `λ ∈ [0, 1]`; `eu_concave_ray`, `eu_concave_junction`: by Assumption 7.3.3,
  `λ ↦ u(λx_t, z_t, λx_{t+1})` and `λ ↦ u(x_T, z_T, λx_{T+1})` are concave on `[0, 1]`.
* `eu_kami_bound`: optimality and (7.38) give, for `λ` near `1`,
  `βᵀ E[u(x*_T, z_T, λx*_{T+1}) − u(x*_T, z_T, x*_{T+1})] ≤ (1 − λ)/(1 − ξ) · R_T`, where
  `R_T = (J* − J_ξ) − (S_T(ξx*) − S_T(x*))` is the tail `Σ_{t>T} βᵗ E[u(x*) − u(ξx*)]`.
* `eu_kami_limit`: the passage `λ → 1` (monotone convergence, by (7.38) and differentiability):
  `−βᵀ E[u_a(x*_T, z_T, x*_{T+1}) · x*_{T+1}] ≤ R_T/(1 − ξ)`.
* **Theorem 7.5.1** (`theorem_7_5_1`): (7.35) holds; `theorem_7_5_1_737`: so does (7.37);
  `theorem_7_5_1_of_zero_mem`: the version with `0 ∈ Γ(x, z)` for all `x`, which gives the
  junction condition.
* `theorem_7_5_1_shift_infeasible`: the feasibility claim fails in general: for the convex-graph
  correspondences `Γ_k(x) = [x(1 − 1/(k+1)), 2x]` (with `0 ∈ Γ_k(0)`), `1 ∈ int Γ_k(1)` for all
  `k`, but for every `λ < 1` some `k` has `λ ∉ Γ_k(1)`; with shocks taking every value `k` with
  positive probability, no shifted plan with `λ < 1` is feasible.

**Corrections and hypotheses.** (1) The shifted plan is feasible after `T` (cone property, from
convexity of `X` and of the graph of `Γ` with `0 ∈ Γ(0, z)`), but at the junction it needs
`λx*_{T+1} ∈ Γ(x*_T, z_T)`, which these do not give (`theorem_7_5_1_shift_infeasible`). We assume
it for `λ ∈ [λ₀, 1)` (`hjunc`); it holds if `0 ∈ Γ(x, z)` for all `x` (`eu_junction_of_zero_mem`),
and in the deterministic case for `λ` near `1` by interiority. (2) The sign
`0 ≤ −E βᵀ u_a · x*_{T+1}` needs `u_a ≤ 0` (from the Euler equation and `u_x ≥ 0`, Assumption 7.3.2
at interior points, `eu_ux_nonneg`) and `x* ≥ 0`: we assume `X ⊆ ℝⁿ₊`, which the theorem does not
state. Without it the argument still gives `limsup_T (−E βᵀ u_a · x*_{T+1}) ≤ 0`
(`eu_kami_limit`). (3) The passage `λ → 1` interchanges the limit with `E`: we use monotone
convergence, the monotonicity in `λ` coming from (7.38); it needs `u_a · x*_{T+1}` integrable.
(4) The tail tends to `0` because `S_T(x*) → J*` and `S_T(ξx*) → J_ξ` (both `J` finite), as the
book says. (5) The Euler equation (7.34) is a hypothesis here; its necessity is proved for
deterministic plans in `theorem_7_5_1_euler_seq`. (6) Differentiability at `(x*_0, x*_1)` needs
`x₀ ∈ int X`. (7) Assumption 6.4.3 is not used; the shocks are any adapted process, as the book
remarks.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

namespace eu_EulerModel

variable {n : ℕ} {Z : Type*} [MeasurableSpace Z] {Ω : Type*} {m0 : MeasurableSpace Ω}
  {M : eu_EulerModel n Z}

/-- With `X` convex and `0 ∈ X`, `c • y ∈ X` for `y ∈ X`, `c ∈ [0, 1]`. -/
theorem eu_smul_mem (hXc : Convex ℝ M.X) (h0X : (0 : Fin n → ℝ) ∈ M.X) {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) {y : Fin n → ℝ} (hy : y ∈ M.X) : c • y ∈ M.X :=
  hXc.smul_mem_of_zero_mem h0X hy hc

/-- **The cone property** (Miao, p. 224): with `0 ∈ Γ(0, z)` and Assumption 6.4.11,
`y′ ∈ Γ(y, z)` implies `c y′ ∈ Γ(c y, z)` for `c ∈ [0, 1]`. -/
theorem eu_cone_feasible (h0X : (0 : Fin n → ℝ) ∈ M.X) (h0Γ : ∀ z', (0 : Fin n → ℝ) ∈ M.Γ 0 z')
    (h6411 : M.eu_Assumption6411) {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) {z' : Z}
    {y y' : Fin n → ℝ} (hy : y ∈ M.X) (hy' : y' ∈ M.Γ y z') : c • y' ∈ M.Γ (c • y) z' := by
  rcases hc.1.eq_or_lt with rfl | hc0
  · simpa using h0Γ z'
  rcases hc.2.eq_or_lt with rfl | hc1
  · simpa using hy'
  have := h6411 z' y hy 0 h0X y' hy' 0 (h0Γ z') c (1 - c) hc0 (by linarith) (by ring)
  simpa using this

/-- **The junction from `0 ∈ Γ(x, z)`**: if `0 ∈ Γ(x, z)` and the graph of `Γ` is convex, then
`c y′ ∈ Γ(x, z)` for `y′ ∈ Γ(x, z)` and `c ∈ [0, 1]`. -/
theorem eu_junction_of_zero_mem (h6411 : M.eu_Assumption6411) {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1)
    {z' : Z} {x y' : Fin n → ℝ} (hx : x ∈ M.X) (h0 : (0 : Fin n → ℝ) ∈ M.Γ x z')
    (hy' : y' ∈ M.Γ x z') : c • y' ∈ M.Γ x z' := by
  rcases hc.1.eq_or_lt with rfl | hc0
  · simpa using h0
  rcases hc.2.eq_or_lt with rfl | hc1
  · simpa using hy'
  have := h6411 z' x hx x hx y' hy' 0 h0 c (1 - c) hc0 (by linarith) (by ring)
  have e : c • x + (1 - c) • x = x := by module
  simpa [e] using this

/-- **Concavity along rays** (Miao, p. 224): by Assumption 7.3.3, `λ ↦ u(λ x, z, λ x′)` is
concave on `[0, 1]` for `(x, x′) ∈ X × X` (with `X` convex, `0 ∈ X`). -/
theorem eu_concave_ray (hXc : Convex ℝ M.X) (h0X : (0 : Fin n → ℝ) ∈ M.X) {z' : Z}
    (hcon : ConcaveOn ℝ (M.X ×ˢ M.X) (M.uu z')) {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ M.X ×ˢ M.X) : ConcaveOn ℝ (Set.Icc 0 1) fun c : ℝ => M.uu z' (c • p) := by
  refine ⟨convex_Icc 0 1, fun c₁ h₁ c₂ h₂ a b ha hb hab => ?_⟩
  have m₁ : c₁ • p ∈ M.X ×ˢ M.X := ⟨eu_smul_mem hXc h0X h₁ hp.1, eu_smul_mem hXc h0X h₁ hp.2⟩
  have m₂ : c₂ • p ∈ M.X ×ˢ M.X := ⟨eu_smul_mem hXc h0X h₂ hp.1, eu_smul_mem hXc h0X h₂ hp.2⟩
  have := hcon.2 m₁ m₂ ha hb hab
  have e : a • c₁ • p + b • c₂ • p = (a • c₁ + b • c₂) • p := by
    simp only [smul_eq_mul, smul_smul, add_smul]
  rwa [e] at this

/-- **Concavity at the junction**: by Assumption 7.3.3, `λ ↦ u(x, z, λ x′)` is concave on
`[0, 1]` for `x, x′ ∈ X` (with `X` convex, `0 ∈ X`). -/
theorem eu_concave_junction (hXc : Convex ℝ M.X) (h0X : (0 : Fin n → ℝ) ∈ M.X) {z' : Z}
    (hcon : ConcaveOn ℝ (M.X ×ˢ M.X) (M.uu z')) {x y : Fin n → ℝ} (hx : x ∈ M.X) (hy : y ∈ M.X) :
    ConcaveOn ℝ (Set.Icc 0 1) fun c : ℝ => M.uu z' (x, c • y) := by
  refine ⟨convex_Icc 0 1, fun c₁ h₁ c₂ h₂ a b ha hb hab => ?_⟩
  have m₁ : (x, c₁ • y) ∈ M.X ×ˢ M.X := ⟨hx, eu_smul_mem hXc h0X h₁ hy⟩
  have m₂ : (x, c₂ • y) ∈ M.X ×ˢ M.X := ⟨hx, eu_smul_mem hXc h0X h₂ hy⟩
  have := hcon.2 m₁ m₂ ha hb hab
  have e : a • (x, c₁ • y) + b • (x, c₂ • y) = (x, (a • c₁ + b • c₂) • y) := by
    ext j
    · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← add_mul, hab, one_mul]
    · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  rwa [e] at this

variable {P : Measure Ω} {ℱ : Filtration ℕ m0} {z : ℕ → Ω → Z}

/-- **The comparison step of Theorem 7.5.1** (Miao, p. 224). For `λ ∈ [λ₀, 1)`, the shifted plan
`(x₀, x*₁, …, x*_T, λx*_{T+1}, …)` is feasible; optimality and (7.38) with `γ = ξ` give
`βᵀ E[u(x*_T, z_T, λx*_{T+1}) − u(x*_T, z_T, x*_{T+1})] ≤ (1 − λ)/(1 − ξ) · R_T`, where
`R_T = (J* − J_ξ) + (S_T(ξx*) − S_T(x*))` and `J_ξ = lim S_T(ξx*)`. -/
theorem eu_kami_bound [IsProbabilityMeasure P] (hXc : Convex ℝ M.X)
    (h0X : (0 : Fin n → ℝ) ∈ M.X) (h0Γ : ∀ z', (0 : Fin n → ℝ) ∈ M.Γ 0 z')
    (h6411 : M.eu_Assumption6411) (hcon : ∀ z', ConcaveOn ℝ (M.X ×ˢ M.X) (M.uu z'))
    (hβ : 0 ≤ M.β) {x₀ : Fin n → ℝ} {xs : ℕ → Ω → (Fin n → ℝ)} {J : ℝ}
    (hopt : M.IsOptimal P ℱ z x₀ xs J) {ξ Jξ : ℝ} (hξ : 0 ≤ ξ ∧ ξ < 1)
    (hJξ : Tendsto (M.eu_partialJ P z fun s ω => ξ • xs s ω) atTop (𝓝 Jξ))
    (hilam : ∀ c ∈ Set.Icc ξ 1, ∀ t,
      Integrable (fun ω => M.u (c • xs t ω) (z t ω) (c • xs (t + 1) ω)) P)
    (hij : ∀ c ∈ Set.Icc ξ 1, ∀ T, Integrable (fun ω => M.u (xs T ω) (z T ω) (c • xs (T + 1) ω)) P)
    (T : ℕ) {lam : ℝ} (hlam : ξ ≤ lam ∧ lam < 1)
    (hjunc : ∀ ω, lam • xs (T + 1) ω ∈ M.Γ (xs T ω) (z T ω)) :
    M.β ^ T * ((∫ ω, M.u (xs T ω) (z T ω) (lam • xs (T + 1) ω) ∂P) -
      ∫ ω, M.u (xs T ω) (z T ω) (xs (T + 1) ω) ∂P) ≤
      (1 - lam) / (1 - ξ) * ((J - Jξ) + (M.eu_partialJ P z (fun s ω => ξ • xs s ω) T -
        M.eu_partialJ P z xs T)) := by
  obtain ⟨hplan, hint, hJ, hcmp⟩ := hopt
  have hlam0 : 0 ≤ lam := hξ.1.trans hlam.1
  have hlamI : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam0, hlam.2.le⟩
  have hlamI' : lam ∈ Set.Icc ξ 1 := ⟨hlam.1, hlam.2.le⟩
  have hξI : ξ ∈ Set.Icc ξ 1 := ⟨le_rfl, hξ.2.le⟩
  set xl : ℕ → Ω → (Fin n → ℝ) := fun s => if s ≤ T then xs s else fun ω => lam • xs s ω
  have hle : ∀ s, s ≤ T → xl s = xs s := fun s hs => by simp [xl, hs]
  have hgt : ∀ s, T < s → xl s = fun ω => lam • xs s ω := fun s hs => by
    simp [xl, Nat.not_le.2 hs]
  -- the shifted plan is feasible
  have hplanl : M.IsPlan ℱ z x₀ xl := by
    refine ⟨fun ω => by rw [hle 0 (Nat.zero_le _)]; exact hplan.1 ω, fun s => ?_, fun s ω => ?_⟩
    · by_cases h : s + 1 ≤ T
      · rw [hle _ h]; exact hplan.2.1 s
      · rw [hgt _ (by omega)]; exact (hplan.2.1 s).const_smul lam
    · by_cases h : s + 1 ≤ T
      · rw [hle _ h, hle _ (by omega)]; exact hplan.2.2 s ω
      by_cases hs : s = T
      · subst hs
        rw [hle _ le_rfl, hgt _ (by omega)]
        exact ⟨(hplan.2.2 s ω).1, hjunc ω⟩
      rw [hgt _ (by omega), hgt _ (by omega)]
      exact ⟨eu_smul_mem hXc h0X hlamI (hplan.2.2 s ω).1,
        eu_cone_feasible h0X h0Γ h6411 hlamI (hplan.2.2 s ω).1 (hplan.2.2 s ω).2⟩
  have hintl : ∀ s, Integrable (fun ω => M.u (xl s ω) (z s ω) (xl (s + 1) ω)) P := by
    intro s
    by_cases h : s + 1 ≤ T
    · rw [hle _ h, hle _ (by omega)]; exact hint s
    by_cases hs : s = T
    · subst hs; rw [hle _ le_rfl, hgt _ (by omega)]; exact hij lam hlamI' s
    rw [hgt _ (by omega), hgt _ (by omega)]
    exact hilam lam hlamI' s
  have hev := hcmp xl hplanl hintl
  -- notation
  set r : ℕ → ℝ := fun s => ∫ ω, M.u (xs s ω) (z s ω) (xs (s + 1) ω) ∂P with hr
  set jun := M.β ^ T * ((∫ ω, M.u (xs T ω) (z T ω) (lam • xs (T + 1) ω) ∂P) - r T) with hjun
  set elam : ℕ → ℝ := fun s => M.β ^ s *
    ((∫ ω, M.u (lam • xs s ω) (z s ω) (lam • xs (s + 1) ω) ∂P) - r s) with helam
  set eξ : ℕ → ℝ := fun s => M.β ^ s *
    ((∫ ω, M.u (ξ • xs s ω) (z s ω) (ξ • xs (s + 1) ω) ∂P) - r s) with heξ
  set α := (1 - lam) / (1 - ξ) with hα
  have hα0 : 0 ≤ α := div_nonneg (by linarith) (by linarith [hξ.2])
  set D : ℕ → ℝ := fun N => M.eu_partialJ P z (fun s ω => ξ • xs s ω) N - M.eu_partialJ P z xs N
    with hD
  -- the partial sums of the shifted plan
  have hterm : ∀ s, M.β ^ s * ∫ ω, M.u (xl s ω) (z s ω) (xl (s + 1) ω) ∂P =
      M.β ^ s * r s + ((if s = T then jun else 0) + (if T < s then elam s else 0)) := by
    intro s
    by_cases h : s + 1 ≤ T
    · rw [hle _ h, hle _ (by omega)]
      have h1 : s ≠ T := by omega
      have h2 : ¬ T < s := by omega
      simp [h1, h2, r]
    by_cases hs : s = T
    · subst hs; rw [hle _ le_rfl, hgt _ (by omega)]
      simp only [↓reduceIte, lt_irrefl, add_zero, hjun]
      ring
    rw [hgt _ (by omega), hgt _ (by omega)]
    have h2 : T < s := by omega
    simp only [hs, h2, ↓reduceIte, zero_add, helam]
    ring
  have hS : ∀ N, T ≤ N → M.eu_partialJ P z xl N = M.eu_partialJ P z xs N + jun +
      ∑ s ∈ Finset.range (N + 1), (if T < s then elam s else 0) := by
    intro N hN
    simp only [eu_partialJ]
    rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' (Finset.range (N + 1)) T]
    have : T ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    simp only [this, ↓reduceIte]
    ring
  -- (7.38) termwise: `elam s ≥ α eξ s`
  have hcmpt : ∀ s, α * eξ s ≤ elam s := by
    intro s
    have hpath : ∀ ω, α * (M.u (ξ • xs s ω) (z s ω) (ξ • xs (s + 1) ω) -
        M.u (xs s ω) (z s ω) (xs (s + 1) ω)) ≤
        M.u (lam • xs s ω) (z s ω) (lam • xs (s + 1) ω) - M.u (xs s ω) (z s ω) (xs (s + 1) ω) := by
      intro ω
      have hp : (xs s ω, xs (s + 1) ω) ∈ M.X ×ˢ M.X :=
        ⟨(hplan.2.2 s ω).1, (hplan.2.2 (s + 1) ω).1⟩
      have h38 := eq_7_38 (eu_concave_ray hXc h0X (hcon (z s ω)) hp) hξ.1 hlam.1 hlam.2
      simp only [one_smul, Prod.smul_mk, uu] at h38
      have h1l : 0 < 1 - lam := by linarith
      rw [div_le_div_iff₀ h1l (by linarith [hξ.2])] at h38
      have hαe : α * (1 - ξ) = 1 - lam := by rw [hα]; field_simp [show (1 - ξ) ≠ 0 by linarith]
      have h1ξ : 0 < 1 - ξ := by linarith
      have key : (M.u (xs s ω) (z s ω) (xs (s + 1) ω) -
          M.u (lam • xs s ω) (z s ω) (lam • xs (s + 1) ω)) * (1 - ξ) ≤
          α * (M.u (xs s ω) (z s ω) (xs (s + 1) ω) -
            M.u (ξ • xs s ω) (z s ω) (ξ • xs (s + 1) ω)) * (1 - ξ) := by
        calc _ ≤ (M.u (xs s ω) (z s ω) (xs (s + 1) ω) -
              M.u (ξ • xs s ω) (z s ω) (ξ • xs (s + 1) ω)) * (1 - lam) := h38
          _ = _ := by rw [← hαe]; ring
      have := le_of_mul_le_mul_right key h1ξ
      linarith
    have hm : ∫ ω, α * (M.u (ξ • xs s ω) (z s ω) (ξ • xs (s + 1) ω) -
        M.u (xs s ω) (z s ω) (xs (s + 1) ω)) ∂P ≤
        ∫ ω, (M.u (lam • xs s ω) (z s ω) (lam • xs (s + 1) ω) -
          M.u (xs s ω) (z s ω) (xs (s + 1) ω)) ∂P :=
      integral_mono (((hilam ξ hξI s).sub (hint s)).const_mul α)
        ((hilam lam hlamI' s).sub (hint s)) hpath
    rw [integral_const_mul, integral_sub (hilam ξ hξI s) (hint s),
      integral_sub (hilam lam hlamI' s) (hint s)] at hm
    simp only [heξ, helam]
    have := mul_le_mul_of_nonneg_left hm (pow_nonneg hβ s)
    nlinarith
  -- the tail of the `ξ`-differences
  have hDsucc : ∀ N, D (N + 1) = D N + eξ (N + 1) := by
    intro N
    simp only [hD, eu_partialJ, Finset.sum_range_succ, heξ, hr]
    ring
  have hG : ∀ N, T ≤ N → α * (D N - D T) ≤
      ∑ s ∈ Finset.range (N + 1), (if T < s then elam s else 0) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      rw [Finset.sum_eq_zero fun s hs => by
        have : ¬ T < s := by have := Finset.mem_range.1 hs; omega
        simp [this]]
      simp
    | succ N hN ih =>
      rw [Finset.sum_range_succ, hDsucc]
      have : T < N + 1 := by omega
      simp only [this, ↓reduceIte]
      have := hcmpt (N + 1)
      nlinarith
  -- let `N → ∞`
  have hlim : Tendsto (fun N => M.eu_partialJ P z xs N + jun + α * (D N - D T)) atTop
      (𝓝 (J + jun + α * ((Jξ - J) - D T))) :=
    ((hJ.add_const jun).add (((hJξ.sub hJ).sub_const (D T)).const_mul α))
  have hbound : ∀ ε > 0, J + jun + α * ((Jξ - J) - D T) ≤ J + ε := by
    intro ε hε
    refine le_of_tendsto hlim ?_
    filter_upwards [hev ε hε, eventually_ge_atTop T] with N h1 h2
    have := hG N h2
    rw [hS N h2] at h1
    linarith
  have hfin : jun + α * ((Jξ - J) - D T) ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    linarith [hbound ε hε]
  linarith

/-- **The passage `λ → 1` in Theorem 7.5.1** (Miao, p. 225). Under the hypotheses of
`eu_kami_bound` for all `λ ∈ [λ₀, 1)`, with `u` differentiable at `(x*_T, x*_{T+1})` and
`u_a · x*_{T+1}` integrable, monotone convergence gives
`−βᵀ E[u_a(x*_T, z_T, x*_{T+1}) · x*_{T+1}] ≤ R_T/(1 − ξ)`. -/
theorem eu_kami_limit [IsProbabilityMeasure P] (hXc : Convex ℝ M.X)
    (h0X : (0 : Fin n → ℝ) ∈ M.X) (h0Γ : ∀ z', (0 : Fin n → ℝ) ∈ M.Γ 0 z')
    (h6411 : M.eu_Assumption6411) (hcon : ∀ z', ConcaveOn ℝ (M.X ×ˢ M.X) (M.uu z'))
    (hβ : 0 < M.β) {x₀ : Fin n → ℝ} {xs : ℕ → Ω → (Fin n → ℝ)} {J : ℝ}
    (hopt : M.IsOptimal P ℱ z x₀ xs J) {ξ Jξ : ℝ} (hξ : 0 ≤ ξ ∧ ξ < 1)
    (hJξ : Tendsto (M.eu_partialJ P z fun s ω => ξ • xs s ω) atTop (𝓝 Jξ))
    (hilam : ∀ c ∈ Set.Icc ξ 1, ∀ t,
      Integrable (fun ω => M.u (c • xs t ω) (z t ω) (c • xs (t + 1) ω)) P)
    (hij : ∀ c ∈ Set.Icc ξ 1, ∀ T, Integrable (fun ω => M.u (xs T ω) (z T ω) (c • xs (T + 1) ω)) P)
    {lam₀ : ℝ} (hlam₀ : ξ ≤ lam₀ ∧ lam₀ < 1)
    (hjunc : ∀ c ∈ Set.Ico lam₀ 1, ∀ T ω, c • xs (T + 1) ω ∈ M.Γ (xs T ω) (z T ω)) (T : ℕ)
    (hd : ∀ ω, DifferentiableAt ℝ (M.uu (z T ω)) (xs T ω, xs (T + 1) ω))
    (hiua : ∀ i, Integrable (fun ω => M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i * xs (T + 1) ω i) P) :
    -(M.β ^ T * ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω)) (xs (T + 1) ω) ∂P) ≤
      ((J - Jξ) + (M.eu_partialJ P z (fun s ω => ξ • xs s ω) T - M.eu_partialJ P z xs T)) /
        (1 - ξ) := by
  have hplan := hopt.1
  have hint := hopt.2.1
  set R := (J - Jξ) + (M.eu_partialJ P z (fun s ω => ξ • xs s ω) T - M.eu_partialJ P z xs T) with hR
  set lk : ℕ → ℝ := fun k => 1 - (1 - lam₀) / (k + 1) with hlk
  have hlk1 : ∀ k, lk k < 1 := fun k => by
    have : 0 < (1 - lam₀) / ((k : ℝ) + 1) := div_pos (by linarith) (by positivity)
    simp only [hlk]; linarith
  have hlk0 : ∀ k, lam₀ ≤ lk k := fun k => by
    have : (1 - lam₀) / ((k : ℝ) + 1) ≤ 1 - lam₀ :=
      div_le_self (by linarith) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    simp only [hlk]; linarith
  have hlkmono : Monotone lk := fun k m hkm => by
    simp only [hlk]
    have : (1 - lam₀) / ((m : ℝ) + 1) ≤ (1 - lam₀) / ((k : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) (by exact_mod_cast by omega)
    linarith
  have hlkt : Tendsto lk atTop (𝓝 1) := by
    have : Tendsto (fun k : ℕ => (1 - lam₀) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 - lam₀)
      rw [mul_zero] at this
      exact this.congr fun k => mul_one_div _ _
    simpa using this.const_sub 1
  -- the difference quotients
  set q : ℕ → Ω → ℝ := fun k ω => (M.u (xs T ω) (z T ω) (lk k • xs (T + 1) ω) -
    M.u (xs T ω) (z T ω) (xs (T + 1) ω)) / (1 - lk k) with hq
  set F : Ω → ℝ := fun ω => -eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω)) (xs (T + 1) ω)
  have hqi : ∀ k, Integrable (q k) P := fun k =>
    ((hij (lk k) ⟨hlam₀.1.trans (hlk0 k), (hlk1 k).le⟩ T).sub (hint T)).div_const _
  have hFi : Integrable F P := by
    have hsumi : Integrable (fun ω => ∑ i, M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i *
        xs (T + 1) ω i) P := integrable_finsetSum _ fun i _ => hiua i
    exact hsumi.neg.congr (Eventually.of_forall fun ω => by simp [F, eu_dot])
  -- pathwise monotonicity and convergence
  have hpw : ∀ ω, Monotone (fun k => q k ω) ∧ Tendsto (fun k => q k ω) atTop (𝓝 (F ω)) := by
    intro ω
    have hx : xs T ω ∈ M.X := (hplan.2.2 T ω).1
    have hy : xs (T + 1) ω ∈ M.X := (hplan.2.2 (T + 1) ω).1
    set h : ℝ → ℝ := fun c => M.uu (z T ω) (xs T ω, c • xs (T + 1) ω) with hh
    have hconc := eu_concave_junction hXc h0X (hcon (z T ω)) hx hy
    have h1 : h 1 = M.u (xs T ω) (z T ω) (xs (T + 1) ω) := by simp [h, uu]
    have hqk : ∀ k, q k ω = -((h 1 - h (lk k)) / (1 - lk k)) := fun k => by
      simp only [hq, h, uu, one_smul]; ring
    refine ⟨fun k m hkm => ?_, ?_⟩
    · change q k ω ≤ q m ω
      rw [hqk, hqk, neg_le_neg_iff]
      exact eq_7_38 hconc (hξ.1.trans (hlam₀.1.trans (hlk0 k))) (hlkmono hkm) (hlk1 m)
    · have hline : HasDerivAt (fun c : ℝ => (xs T ω, c • xs (T + 1) ω))
          ((0 : Fin n → ℝ), xs (T + 1) ω) 1 :=
        HasDerivAt.prodMk (hasDerivAt_const (1 : ℝ) (xs T ω))
          (((hasDerivAt_id (1 : ℝ)).smul_const (xs (T + 1) ω)).congr_deriv (by simp))
      have hd' : HasFDerivAt (M.uu (z T ω)) (fderiv ℝ (M.uu (z T ω)) (xs T ω, xs (T + 1) ω))
          (xs T ω, (1 : ℝ) • xs (T + 1) ω) := by simpa using (hd ω).hasFDerivAt
      have hder : HasDerivAt h (fderiv ℝ (M.uu (z T ω)) (xs T ω, xs (T + 1) ω)
          ((0 : Fin n → ℝ), xs (T + 1) ω)) 1 := by exact hd'.comp_hasDerivAt 1 hline
      have hval : fderiv ℝ (M.uu (z T ω)) (xs T ω, xs (T + 1) ω) ((0 : Fin n → ℝ), xs (T + 1) ω)
          = -F ω := by
        rw [eu_clm_pair]
        simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, F, neg_neg, eu_dot,
          ua]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [hval] at hder
      have hs := hasDerivAt_iff_tendsto_slope.1 hder
      have hlk' : Tendsto lk atTop (𝓝[≠] 1) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlkt
          (Eventually.of_forall fun k => (hlk1 k).ne)
      have := (hs.comp hlk').neg
      rw [neg_neg] at this
      refine this.congr fun k => ?_
      simp only [Function.comp_apply, slope_def_field, hqk]
      have hne : lk k - 1 ≠ 0 := sub_ne_zero.2 (hlk1 k).ne
      have hne' : 1 - lk k ≠ 0 := sub_ne_zero.2 (hlk1 k).ne'
      field_simp
      ring
  have hmct := integral_tendsto_of_tendsto_of_monotone hqi hFi
    (Eventually.of_forall fun ω => (hpw ω).1) (Eventually.of_forall fun ω => (hpw ω).2)
  -- each quotient is bounded by `R/(1 − ξ)`
  have hbk : ∀ k, M.β ^ T * ∫ ω, q k ω ∂P ≤ R / (1 - ξ) := by
    intro k
    have hb := eu_kami_bound hXc h0X h0Γ h6411 hcon hβ.le hopt hξ hJξ hilam hij T
      ⟨hlam₀.1.trans (hlk0 k), hlk1 k⟩ (hjunc (lk k) ⟨hlk0 k, hlk1 k⟩ T)
    have h1l : 0 < 1 - lk k := by linarith [hlk1 k]
    have h1ξ : 0 < 1 - ξ := by linarith [hξ.2]
    have hqint : ∫ ω, q k ω ∂P = ((∫ ω, M.u (xs T ω) (z T ω) (lk k • xs (T + 1) ω) ∂P) -
        ∫ ω, M.u (xs T ω) (z T ω) (xs (T + 1) ω) ∂P) / (1 - lk k) := by
      simp only [hq]
      rw [integral_div, integral_sub (hij (lk k) ⟨hlam₀.1.trans (hlk0 k), (hlk1 k).le⟩ T) (hint T)]
    rw [hqint, mul_div_assoc', div_le_div_iff₀ h1l h1ξ]
    have := mul_le_mul_of_nonneg_right hb h1ξ.le
    have e : (1 - lk k) / (1 - ξ) * R * (1 - ξ) = R * (1 - lk k) := by
      field_simp
    nlinarith
  have hlimit : M.β ^ T * ∫ ω, F ω ∂P ≤ R / (1 - ξ) :=
    le_of_tendsto' (hmct.const_mul (M.β ^ T)) hbk
  have hFeq : ∫ ω, F ω ∂P = -∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω)) (xs (T + 1) ω) ∂P :=
    integral_neg _
  rw [hFeq] at hlimit
  linarith

/-- **Theorem 7.5.1 (necessity of the transversality condition, Kamihigashi)** (Miao, p. 224).
Let `X ⊆ ℝⁿ₊` be convex with `0 ∈ X`, `Γ ⊆ X`, `0 ∈ Γ(0, z)`, and Assumptions 5.1.2, 6.4.11,
7.3.2, 7.3.3 and 7.3.4 hold. Let `x*` be an optimal plan with value `J*`, interior
(`x₀ ∈ int X`, `x*_{t+1} ∈ int Γ(x*_t, z_t)`), satisfying the Euler equation (7.34), such that
the plan `ξx*` has convergent partial sums (`J(ξx*)` finite) for some `ξ ∈ [0, 1)`. Assume the
junction condition `λx*_{T+1} ∈ Γ(x*_T, z_T)` for `λ ∈ [λ₀, 1)` (`ξ ≤ λ₀ < 1`) and the
integrability of the rewards of the shifted plans and of `u_a · x*_{T+1}`. Then `x*` satisfies
the transversality condition (7.35). -/
theorem theorem_7_5_1 [IsProbabilityMeasure P] (hXc : Convex ℝ M.X)
    (h0X : (0 : Fin n → ℝ) ∈ M.X) (hXpos : ∀ y ∈ M.X, 0 ≤ y) (hΓX : ∀ y z', M.Γ y z' ⊆ M.X)
    (h0Γ : ∀ z', (0 : Fin n → ℝ) ∈ M.Γ 0 z') (h512 : 0 < M.β ∧ M.β < 1)
    (h6411 : M.eu_Assumption6411) (h732 : M.eu_Assumption732) (h733 : M.eu_Assumption733)
    (h734 : M.eu_Assumption734) {x₀ : Fin n → ℝ} {xs : ℕ → Ω → (Fin n → ℝ)} {J : ℝ}
    (hopt : M.IsOptimal P ℱ z x₀ xs J) (hx0 : x₀ ∈ interior M.X)
    (hinter : ∀ t ω, xs (t + 1) ω ∈ interior (M.Γ (xs t ω) (z t ω)))
    (heuler : M.IsEuler P ℱ z xs) {ξ Jξ : ℝ} (hξ : 0 ≤ ξ ∧ ξ < 1)
    (hJξ : Tendsto (M.eu_partialJ P z fun s ω => ξ • xs s ω) atTop (𝓝 Jξ))
    {lam₀ : ℝ} (hlam₀ : ξ ≤ lam₀ ∧ lam₀ < 1)
    (hjunc : ∀ c ∈ Set.Ico lam₀ 1, ∀ T ω, c • xs (T + 1) ω ∈ M.Γ (xs T ω) (z T ω))
    (hilam : ∀ c ∈ Set.Icc ξ 1, ∀ t,
      Integrable (fun ω => M.u (c • xs t ω) (z t ω) (c • xs (t + 1) ω)) P)
    (hij : ∀ c ∈ Set.Icc ξ 1, ∀ T, Integrable (fun ω => M.u (xs T ω) (z T ω) (c • xs (T + 1) ω)) P)
    (hiua : ∀ T i,
      Integrable (fun ω => M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i * xs (T + 1) ω i) P) :
    M.TVC735 P z xs := by
  have hplan := hopt.1
  have hcon : ∀ z', ConcaveOn ℝ (M.X ×ˢ M.X) (M.uu z') := fun z' => concaveOn_of_733 h733 hXc z'
  have hin : ∀ t ω, xs t ω ∈ interior M.X := by
    intro t ω
    cases t with
    | zero => rw [hplan.1 ω]; exact hx0
    | succ t => exact interior_mono (hΓX _ _) (hinter t ω)
  have hd : ∀ t ω, DifferentiableAt ℝ (M.uu (z t ω)) (xs t ω, xs (t + 1) ω) := fun t ω => by
    have hm : (xs t ω, xs (t + 1) ω) ∈ interior (M.X ×ˢ M.X) := by
      rw [interior_prod_eq]; exact ⟨hin t ω, hin (t + 1) ω⟩
    exact ((h734 (z t ω)).differentiableOn one_ne_zero).differentiableAt
      (isOpen_interior.mem_nhds hm)
  -- the sign: `E[u_a(T) · x*_{T+1}] ≤ 0`
  have hsign : ∀ T, ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω)) (xs (T + 1) ω) ∂P ≤ 0 := by
    intro T
    refine integral_nonpos_of_ae ?_
    have hneg : ∀ i, ∀ᵐ ω ∂P, M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i ≤ 0 := by
      intro i
      have hce := condExp_nonneg (m := ℱ T) (μ := P)
        (f := fun ω' => M.ux (xs (T + 1) ω') (z (T + 1) ω') (xs (T + 2) ω') i)
        (Eventually.of_forall fun ω => eu_ux_nonneg (h732 _ _).monotoneOn (hin (T + 1) ω)
          (hd (T + 1) ω) i)
      filter_upwards [heuler T i, hce] with ω hω hc
      simp only [Pi.zero_apply] at hω hc
      nlinarith [mul_nonneg h512.1.le hc]
    filter_upwards [ae_all_iff.2 hneg] with ω hω
    simp only [eu_dot, Pi.zero_apply]
    refine Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hω i) ?_
    exact hXpos _ (hplan.2.2 (T + 1) ω).1 i
  -- the bound and the squeeze
  have hR : Tendsto (fun T => ((J - Jξ) + (M.eu_partialJ P z (fun s ω => ξ • xs s ω) T -
      M.eu_partialJ P z xs T)) / (1 - ξ)) atTop (𝓝 0) := by
    have := ((hJξ.sub hopt.2.2.1).const_add (J - Jξ)).div_const (1 - ξ)
    simpa using this
  have hup : ∀ T, -(M.β ^ T * ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω))
      (xs (T + 1) ω) ∂P) ≤ ((J - Jξ) + (M.eu_partialJ P z (fun s ω => ξ • xs s ω) T -
        M.eu_partialJ P z xs T)) / (1 - ξ) := fun T =>
    eu_kami_limit hXc h0X h0Γ h6411 hcon h512.1 hopt hξ hJξ hilam hij hlam₀ hjunc T (hd T)
      (hiua T)
  have hlow : ∀ T, 0 ≤ -(M.β ^ T * ∫ ω, eu_dot (M.ua (xs T ω) (z T ω) (xs (T + 1) ω))
      (xs (T + 1) ω) ∂P) := fun T => by
    have := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg h512.1.le T) (hsign T)
    linarith
  have hsq := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR hlow hup
  have := hsq.neg
  simp only [neg_neg, neg_zero] at this
  exact this

/-- **Theorem 7.5.1, the form (7.37)** (Miao, p. 225): under the hypotheses of `theorem_7_5_1`,
and the integrability of `u_x(T + 1)` and `u_x(T + 1) · x*_{T+1}`, `x*` also satisfies (7.37). -/
theorem theorem_7_5_1_737 [IsProbabilityMeasure P] (hXc : Convex ℝ M.X)
    (h0X : (0 : Fin n → ℝ) ∈ M.X) (hXpos : ∀ y ∈ M.X, 0 ≤ y) (hΓX : ∀ y z', M.Γ y z' ⊆ M.X)
    (h0Γ : ∀ z', (0 : Fin n → ℝ) ∈ M.Γ 0 z') (h512 : 0 < M.β ∧ M.β < 1)
    (h6411 : M.eu_Assumption6411) (h732 : M.eu_Assumption732) (h733 : M.eu_Assumption733)
    (h734 : M.eu_Assumption734) {x₀ : Fin n → ℝ} {xs : ℕ → Ω → (Fin n → ℝ)} {J : ℝ}
    (hopt : M.IsOptimal P ℱ z x₀ xs J) (hx0 : x₀ ∈ interior M.X)
    (hinter : ∀ t ω, xs (t + 1) ω ∈ interior (M.Γ (xs t ω) (z t ω)))
    (heuler : M.IsEuler P ℱ z xs) {ξ Jξ : ℝ} (hξ : 0 ≤ ξ ∧ ξ < 1)
    (hJξ : Tendsto (M.eu_partialJ P z fun s ω => ξ • xs s ω) atTop (𝓝 Jξ))
    {lam₀ : ℝ} (hlam₀ : ξ ≤ lam₀ ∧ lam₀ < 1)
    (hjunc : ∀ c ∈ Set.Ico lam₀ 1, ∀ T ω, c • xs (T + 1) ω ∈ M.Γ (xs T ω) (z T ω))
    (hilam : ∀ c ∈ Set.Icc ξ 1, ∀ t,
      Integrable (fun ω => M.u (c • xs t ω) (z t ω) (c • xs (t + 1) ω)) P)
    (hij : ∀ c ∈ Set.Icc ξ 1, ∀ T, Integrable (fun ω => M.u (xs T ω) (z T ω) (c • xs (T + 1) ω)) P)
    (hiua : ∀ T i,
      Integrable (fun ω => M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i * xs (T + 1) ω i) P)
    (hI1 : ∀ T i, Integrable (fun ω => M.ux (xs (T + 1) ω) (z (T + 1) ω) (xs (T + 2) ω) i) P)
    (hI2 : ∀ T i, Integrable (fun ω => xs (T + 1) ω i *
      M.ux (xs (T + 1) ω) (z (T + 1) ω) (xs (T + 2) ω) i) P) :
    M.TVC737 P z xs :=
  ((eq_7_35_iff_7_37 heuler hopt.1.2.1 hI1 hI2).2).1
    (theorem_7_5_1 hXc h0X hXpos hΓX h0Γ h512 h6411 h732 h733 h734 hopt hx0 hinter heuler hξ hJξ
      hlam₀ hjunc hilam hij hiua)

/-- **Theorem 7.5.1 with `0 ∈ Γ(x, z)`**: if `0 ∈ Γ(x, z)` for all `x ∈ X`, the junction
condition holds for every `λ ∈ [ξ, 1)` (`eu_junction_of_zero_mem`), so under the other
hypotheses of `theorem_7_5_1` the transversality condition (7.35) holds. -/
theorem theorem_7_5_1_of_zero_mem [IsProbabilityMeasure P] (hXc : Convex ℝ M.X)
    (h0X : (0 : Fin n → ℝ) ∈ M.X) (hXpos : ∀ y ∈ M.X, 0 ≤ y) (hΓX : ∀ y z', M.Γ y z' ⊆ M.X)
    (h0Γ : ∀ y ∈ M.X, ∀ z', (0 : Fin n → ℝ) ∈ M.Γ y z') (h512 : 0 < M.β ∧ M.β < 1)
    (h6411 : M.eu_Assumption6411) (h732 : M.eu_Assumption732) (h733 : M.eu_Assumption733)
    (h734 : M.eu_Assumption734) {x₀ : Fin n → ℝ} {xs : ℕ → Ω → (Fin n → ℝ)} {J : ℝ}
    (hopt : M.IsOptimal P ℱ z x₀ xs J) (hx0 : x₀ ∈ interior M.X)
    (hinter : ∀ t ω, xs (t + 1) ω ∈ interior (M.Γ (xs t ω) (z t ω)))
    (heuler : M.IsEuler P ℱ z xs) {ξ Jξ : ℝ} (hξ : 0 ≤ ξ ∧ ξ < 1)
    (hJξ : Tendsto (M.eu_partialJ P z fun s ω => ξ • xs s ω) atTop (𝓝 Jξ))
    (hilam : ∀ c ∈ Set.Icc ξ 1, ∀ t,
      Integrable (fun ω => M.u (c • xs t ω) (z t ω) (c • xs (t + 1) ω)) P)
    (hij : ∀ c ∈ Set.Icc ξ 1, ∀ T, Integrable (fun ω => M.u (xs T ω) (z T ω) (c • xs (T + 1) ω)) P)
    (hiua : ∀ T i,
      Integrable (fun ω => M.ua (xs T ω) (z T ω) (xs (T + 1) ω) i * xs (T + 1) ω i) P) :
    M.TVC735 P z xs := by
  refine theorem_7_5_1 hXc h0X hXpos hΓX (fun z' => h0Γ 0 h0X z') h512 h6411 h732 h733 h734 hopt
    hx0 hinter heuler hξ hJξ ⟨le_rfl, hξ.2⟩ (fun c hc T ω => ?_) hilam hij hiua
  have hxT : xs T ω ∈ M.X := (hopt.1.2.2 T ω).1
  exact eu_junction_of_zero_mem h6411 ⟨hξ.1.trans hc.1, hc.2.le⟩ hxT (h0Γ _ hxT _)
    (hopt.1.2.2 T ω).2

end eu_EulerModel

/-- **The feasibility claim in the proof of Theorem 7.5.1 fails** (Miao, p. 224). The
correspondences `Γ_k(x) = [x(1 − 1/(k + 1)), 2x]` on `ℝ₊` have convex graphs and `0 ∈ Γ_k(0)`;
the constant plan `x* = 1` is interior (`1 ∈ int Γ_k(1)` for all `k`), but for every `λ < 1`
there is `k` with `λ · 1 ∉ Γ_k(1)`. With a shock taking every value `k` with positive
probability, the shifted plan `(…, x*_T, λx*_{T+1}, …)` is infeasible for every `λ < 1`. -/
theorem theorem_7_5_1_shift_infeasible :
    let G : ℕ → ℝ → Set ℝ := fun k x => Set.Icc (x * (1 - 1 / ((k : ℝ) + 1))) (2 * x)
    (∀ k, ∀ x x' y y' θ η : ℝ, y ∈ G k x → y' ∈ G k x' → 0 ≤ θ → 0 ≤ η → θ + η = 1 →
      θ * y + η * y' ∈ G k (θ * x + η * x')) ∧ (∀ k, (0 : ℝ) ∈ G k 0) ∧
    (∀ k, (1 : ℝ) ∈ interior (G k 1)) ∧ ∀ lam < 1, ∃ k, lam * 1 ∉ G k 1 := by
  intro G
  refine ⟨fun k x x' y y' θ η hy hy' hθ hη _ => ⟨?_, ?_⟩, fun k => ?_, fun k => ?_,
    fun lam hlam => ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left hy.1 hθ
    have h2 := mul_le_mul_of_nonneg_left hy'.1 hη
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hy.2 hθ
    have h2 := mul_le_mul_of_nonneg_left hy'.2 hη
    nlinarith
  · simp [G]
  · have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (Ioo_mem_nhds (a := 1 - 1 / ((k : ℝ) + 1)) (b := 2)
      (by linarith) (by norm_num)) fun y hy => ?_
    simp only [G, one_mul, Set.mem_Icc]
    exact ⟨hy.1.le, by linarith [hy.2]⟩
  · obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - lam))
    refine ⟨k, fun hmem => ?_⟩
    have h1 : 0 < 1 - lam := by linarith
    have hlt : 1 / ((k : ℝ) + 1) < 1 - lam := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ h1] at hk
      nlinarith
    have := hmem.1
    simp only [one_mul, mul_one] at this
    linarith

end Miao.InfiniteHorizonDP
