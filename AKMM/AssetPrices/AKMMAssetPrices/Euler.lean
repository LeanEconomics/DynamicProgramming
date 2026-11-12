/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMAssetPrices.DynamicTree
import AKMMAssetPrices.SDF
import AKMMAssetPrices.Equilibrium

/-!
# Optimality conditions and Euler equations with dynamic trading

AKMM, §16.5, pp. 483–485, on the finite event tree of `DynamicTree`. The sequential budget (16.8)
is `c ≤ y + x(θ)` with `x(θ)` the payoff stream of the strategy (`euBudget`).

* The first-order condition for holdings of asset `n` at `ωᵗ`,
  `ηₜ(ωᵗ)pⁿₜ(ωᵗ) = Σ_{ωᵗ⁺¹} ηₜ₊₁(ωᵗ⁺¹)(dⁿₜ₊₁ + pⁿₜ₊₁)(ωᵗ⁺¹)` with `η = ∂U/∂c`, proved from
  optimality at an interior optimum (`eu_foc`).
* (16.19): the subjective state prices `qᵢ,ₜ₊₁(ωₜ₊₁|ωᵗ) = (∂Uᵢ/∂cₜ₊₁(ωᵗ⁺¹))/(∂Uᵢ/∂cₜ(ωᵗ))`
  price every asset (`eq_16_19`), so an optimum excludes arbitrage (`eu_noArbitrage`).
* (16.20)–(16.21): with expected power utility the marginal utility is `πₜ(ωᵗ)βᵗcₜ(ωᵗ)^{−γ}`
  (`eu_crra_partial`) and `qᵢ,ₜ₊₁(ωₜ₊₁|ωᵗ) = πₜ₊₁(ωₜ₊₁|ωᵗ)β(cₜ₊₁(ωᵗ⁺¹)/cₜ(ωᵗ))^{−γ}`
  (`eq_16_21`).
* (16.22)–(16.23): the return `Rⁿₜ₊₁ = (dⁿₜ₊₁ + pⁿₜ₊₁)/pⁿₜ` satisfies `Eₜ[Mₜ₊₁Rⁿₜ₊₁] = 1`
  with `M = q/πₜ₊₁(·|ωᵗ)` (`eq_16_23`), and the conditional risk premium is
  `Eₜ[Rⁿₜ₊₁] − R^f_{t+1} = −Covₜ(Mₜ₊₁, Rⁿₜ₊₁)/Eₜ[Mₜ₊₁]` (`eu_conditional_premium`).

Departures: (16.21) prints `cᵢ,ₜ₊₁(ωᵗ)` and `βᵗ⁺¹(ωᵗ⁺¹)`; the correct expression has
`cᵢ,ₜ₊₁(ωᵗ⁺¹)` and `βᵗ⁺¹`. The first-order conditions are derived at an interior optimum with
differentiable utility, on a finite tree. See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Filter Topology Miao.CompleteMarkets

variable {Node N : Type} [Fintype Node] [Fintype N]

/-- AKMM, (16.8), p. 471: the sequential budget set `c ≤ y + x(θ)` on the tree. -/
def euBudget (T : DTree Node) (p d : Node → N → ℝ) (y : Node → ℝ) : Set (Node → ℝ) :=
  {c | ∃ θ, ∀ h, c h ≤ y h + dtPayoff T p d θ h}

/-- AKMM, p. 484: at an interior optimum `c ≫ 0` of a differentiable utility on the sequential
budget set (with `c ≥ 0`), the first-order condition for holding asset `n` at node `h` is
`η(h)pⁿ(h) = Σ_{h' child of h} η(h')(dⁿ(h') + pⁿ(h'))`, `η(h) = ∂U/∂c(h)`. -/
theorem eu_foc [DecidableEq Node] {T : DTree Node} {p d : Node → N → ℝ} {y : Node → ℝ}
    {U : (Node → ℝ) → ℝ} {DU : (Node → ℝ) →L[ℝ] ℝ} {c : Node → ℝ}
    (hc : c ∈ euBudget T p d y) (hpos : ∀ h, 0 < c h)
    (hopt : ∀ c' ∈ euBudget T p d y, (∀ h, 0 ≤ c' h) → U c' ≤ U c)
    (hU : HasFDerivAt U DU c) (h : Node) (n : N) :
    DU (Pi.single h 1) * p h n = ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
      DU (Pi.single h' 1) * (p h' n + d h' n) := by
  classical
  obtain ⟨θ, hθ⟩ := hc
  set e : Node → N → ℝ := fun h' n' => if h' = h ∧ n' = n then 1 else 0 with he
  set v : Node → ℝ := dtPayoff T p d e with hv
  have hlin : ∀ t : ℝ, dtPayoff T p d (θ + t • e) = dtPayoff T p d θ + t • v := fun t => by
    have := (dtPayoffLin T p d).map_add θ (t • e)
    rw [(dtPayoffLin T p d).map_smul] at this
    exact this
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (c + t • v ∈ euBudget T p d y ∧ ∀ h, 0 ≤ (c + t • v) h) := by
    have hk : ∀ k, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < c k + t * v k := fun k =>
      ((by fun_prop : Continuous fun t : ℝ => c k + t * v k).tendsto' 0 (c k)
        (by simp)).eventually (lt_mem_nhds (hpos k))
    filter_upwards [Filter.eventually_all.2 hk] with t ht
    refine ⟨⟨θ + t • e, fun k => ?_⟩, fun k => by simpa using (ht k).le⟩
    rw [hlin t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hθ k]
  have hmax : IsLocalMax (fun t : ℝ => U (c + t • v)) 0 := by
    filter_upwards [hev] with t ht
    simpa using hopt _ ht.1 ht.2
  have h0 := hmax.hasDerivAt_eq_zero (en_line_deriv hU v)
  rw [tp_clm_apply DU v] at h0
  have hval := dt_value_payoff T p d (fun k => DU (Pi.single k 1)) e
  simp only [← hv] at hval
  have hcomm : ∑ k, v k * DU (Pi.single k 1) = ∑ k, DU (Pi.single k 1) * v k :=
    Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hcomm, hval] at h0
  simp only [he, ite_mul, one_mul, zero_mul] at h0
  rw [Finset.sum_eq_single h, Finset.sum_eq_single n] at h0
  · simp only [and_self, ↓reduceIte] at h0
    linarith
  · intro n' _ hn
    simp [hn]
  · simp
  · intro h' _ hh
    simp [hh]
  · simp

/-- AKMM, (16.19), p. 484: with positive marginal utilities, the subjective state prices
`qᵢ(h') = (∂Uᵢ/∂c(h'))/(∂Uᵢ/∂c(h))` for each successor `h'` of `h` price every asset,
`pⁿ(h) = Σ_{h'}(dⁿ(h') + pⁿ(h'))qᵢ(h')`. -/
theorem eq_16_19 [DecidableEq Node] {T : DTree Node} {p d : Node → N → ℝ} {y : Node → ℝ}
    {U : (Node → ℝ) → ℝ} {DU : (Node → ℝ) →L[ℝ] ℝ} {c : Node → ℝ}
    (hc : c ∈ euBudget T p d y) (hpos : ∀ h, 0 < c h)
    (hopt : ∀ c' ∈ euBudget T p d y, (∀ h, 0 ≤ c' h) → U c' ≤ U c)
    (hU : HasFDerivAt U DU c) (hMU : ∀ h, 0 < DU (Pi.single h 1)) (h : Node) (n : N) :
    p h n = ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
      (d h' n + p h' n) * (DU (Pi.single h' 1) / DU (Pi.single h 1)) := by
  have e := eu_foc hc hpos hopt hU h n
  have h0 := (hMU h).ne'
  have hs : ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
      (d h' n + p h' n) * (DU (Pi.single h' 1) / DU (Pi.single h 1)) =
      (∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
        DU (Pi.single h' 1) * (p h' n + d h' n)) / DU (Pi.single h 1) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun h' _ => by ring
  rw [hs, ← e]
  field_simp

omit [Fintype Node] in
/-- AKMM, p. 483: if the individual problem has an interior solution with positive marginal
utilities, there is no arbitrage (the marginal utilities are a deflator, `dt_ftap_deflator`). -/
theorem eu_noArbitrage [Finite Node] [DecidableEq Node] {T : DTree Node} {p d : Node → N → ℝ}
    {y : Node → ℝ} {U : (Node → ℝ) → ℝ} {DU : (Node → ℝ) →L[ℝ] ℝ} {c : Node → ℝ}
    (hc : c ∈ euBudget T p d y) (hpos : ∀ h, 0 < c h)
    (hopt : ∀ c' ∈ euBudget T p d y, (∀ h, 0 ≤ c' h) → U c' ≤ U c)
    (hU : HasFDerivAt U DU c) (hMU : ∀ h, 0 < DU (Pi.single h 1)) : dtNoArbitrage T p d := by
  have := Fintype.ofFinite Node
  exact (dt_ftap_deflator T p d).2 ⟨fun h => DU (Pi.single h 1), hMU, eu_foc hc hpos hopt hU⟩

/-- AKMM, (16.20), p. 484: expected power utility `Σ_{t,ωᵗ} πₜ(ωᵗ)βᵗcₜ(ωᵗ)^{1−γ}/(1−γ)` has
partial derivative `πₜ(ωᵗ)βᵗcₜ(ωᵗ)^{−γ}` at `c ≫ 0`. -/
theorem eu_crra_partial (T : DTree Node) {pr : Node → ℝ} {β γ : ℝ} [DecidableEq Node]
    (hγ : γ ≠ 1) {c : Node → ℝ} (hc : ∀ h, 0 < c h) (h : Node) :
    HasDerivAt (fun x : ℝ => ∑ k, pr k * β ^ T.depth k *
        ((c k + x * if k = h then 1 else 0) ^ (1 - γ) / (1 - γ)))
      (pr h * β ^ T.depth h * c h ^ (-γ)) 0 := by
  have hk : ∀ k ∈ Finset.univ, HasDerivAt (fun x : ℝ => pr k * β ^ T.depth k *
      ((c k + x * if k = h then 1 else 0) ^ (1 - γ) / (1 - γ)))
      (if k = h then pr h * β ^ T.depth h * c h ^ (-γ) else 0) 0 := by
    intro k _
    by_cases hkh : k = h
    · subst hkh
      simp only [↓reduceIte, mul_one]
      have hd := tp_crra_marginal hγ (hc k)
      have hd0 : HasDerivAt (fun z => z ^ (1 - γ) / (1 - γ)) (c k ^ (-γ)) (c k + 0) := by
        simpa using hd
      exact (hd0.comp_const_add (c k) 0).const_mul _
    · simp only [hkh, ↓reduceIte, mul_zero, add_zero]
      exact hasDerivAt_const _ _
  have := HasDerivAt.fun_sum hk
  simpa using this

/-- AKMM, (16.21), p. 484, corrected: with marginal utilities `πₜ(ωᵗ)βᵗcₜ(ωᵗ)^{−γ}`, the state
price of the successor `ωᵗ⁺¹` is `πₜ₊₁(ωₜ₊₁|ωᵗ)β(cₜ₊₁(ωᵗ⁺¹)/cₜ(ωᵗ))^{−γ}`, where
`πₜ₊₁(ωₜ₊₁|ωᵗ) = πₜ₊₁(ωᵗ⁺¹)/πₜ(ωᵗ)`. -/
theorem eq_16_21 {prt prt1 β γ ct ct1 : ℝ} (t : ℕ) (hpr : 0 < prt) (hβ : 0 < β) (hct : 0 < ct)
    (hct1 : 0 < ct1) :
    prt1 * β ^ (t + 1) * ct1 ^ (-γ) / (prt * β ^ t * ct ^ (-γ)) =
      prt1 / prt * β * (ct1 / ct) ^ (-γ) := by
  have h1 : 0 < ct ^ (-γ) := Real.rpow_pos_of_pos hct _
  have h2 : 0 < β ^ t := pow_pos hβ t
  rw [Real.div_rpow hct1.le hct.le, pow_succ]
  field_simp

/-- AKMM, (16.22)–(16.23), p. 484: at node `ωᵗ` with successor states `ω ∈ Ω`, conditional
probabilities `πc`, state prices `q` and payoffs `X = dⁿₜ₊₁ + pⁿₜ₊₁` with
`pⁿₜ = Σ_ω X(ω)q(ω)`, the return `R = X/pⁿₜ` and `M = q/πc` satisfy `Eₜ[MR] = 1`. -/
theorem eq_16_23 {Ω : Type} [Fintype Ω] {prc q X : Ω → ℝ} {pt : ℝ} (hpr : ∀ ω, 0 < prc ω)
    (hp : pt = ∑ ω, X ω * q ω) (hpt : pt ≠ 0) :
    bp_E prc (fun ω => sdfM q prc ω * (X ω / pt)) = 1 := by
  have h := sdf_return (D := Matrix.of fun ω (_ : Unit) => X ω) (p := fun _ => pt) hpr
    (fun _ => by simpa using hp) (n := ()) hpt
  rw [← h]
  exact Finset.sum_congr rfl fun ω _ => by simp only [Matrix.of_apply]; ring

/-- AKMM, p. 485: the conditional risk premium,
`Eₜ[Rⁿₜ₊₁] − R^f_{t+1} = −Covₜ(Mₜ₊₁, Rⁿₜ₊₁)/Eₜ[Mₜ₊₁]` with `R^f_{t+1} = 1/Eₜ[Mₜ₊₁]`, and
`Eₜ[M]Eₜ[Rⁿ] + Covₜ(M, Rⁿ) = 1`. -/
theorem eu_conditional_premium {Ω : Type} [Fintype Ω] {prc M R : Ω → ℝ}
    (hM : bp_E prc M ≠ 0) (h : bp_E prc (fun ω => M ω * R ω) = 1) :
    bp_E prc M * bp_E prc R + bp_Cov prc M R = 1 ∧
      bp_E prc R - 1 / bp_E prc M = -bp_Cov prc M R / bp_E prc M := by
  have h' : bp_E prc (fun ω => R ω * M ω) = 1 := by
    rw [← h]
    exact Finset.sum_congr rfl fun ω _ => by ring
  obtain ⟨e1, e2⟩ := eq_16_17 hM h'
  rw [bp_Cov_comm]
  exact ⟨by linarith, e2⟩

end AKMM.AssetPrices
