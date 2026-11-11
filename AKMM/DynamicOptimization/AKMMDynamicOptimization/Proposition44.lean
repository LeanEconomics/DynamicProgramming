/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.FiniteHorizon
import EulerTransversality.GrowthModel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proposition 4.4: the Euler equation and the transversality condition are sufficient

AKMM, §4.3.1, pp. 110–111, with the proof of App. 4.A.3, pp. 830–831.

* **Proposition 4.4** (`proposition_4_4`): a plan satisfying the Euler equation (i) and the TVC
  (ii) `βᵗF₁(x*_t, x*_{t+1})x*_t → 0`, with `F` concave and `F₁ ≥ 0`, is optimal: catching-up
  optimal, and of largest value whenever values are finite. It is proved from EulerTransversality's
  `euler_tvc_sufficient` (the book's telescoping argument of 4.A.3, in supergradient form). The
  book's "increasing in its first argument" gives `F₁ ≥ 0` (`proposition_4_4_F1_nonneg`).
* The book omits a hypothesis that its proof uses: the competing plans must be nonnegative
  (the last step of 4.A.3 needs `F₁ · x_{T+1} ≥ 0`). Without it the proposition is false
  (`proposition_4_4_counterexample`: `F(x, y) = x − βy`, `Γ(x) = ℝ`, `x* = 0`). The book's
  restriction to interior competitors is not needed.
* The NGM form of the TVC, `lim βᵗu'(c_t)[f'(k_t) + 1 − δ]k_t = 0` (p. 110), and sufficiency in the
  NGM (`proposition_4_4_ngm`, from EulerTransversality's `growth_sufficient`).
* A stationary plan satisfies the TVC automatically when `β < 1` (`tvc_stationary`), and the
  modified-golden-rule steady state is optimal (`ngm_steady_state_optimal`).
* On a balanced path with gross growth `γ`, `βᵗu'(c_t)k_t` grows at the gross rate `βγ^{1−σ}`,
  and the TVC holds iff `βγ^{1−σ} < 1` (`tvc_balanced_growth`), the boundedness condition of
  `infinite_growth_summable_iff`.
-/

namespace AKMM.DynamicOptimization

open Filter Topology StokeyLucasPrescott.DeterministicDP DPExtensions.EulerTransversality

/-- **Proposition 4.4** (AKMM, p. 110; proof in App. 4.A.3, pp. 830–831). Let `F` be concave on
a convex set `A` containing the graph of `Γ`, with derivative `D_t` at `(x*_t, x*_{t+1})` along a
feasible plan `x*`, `F₁ = D_t(1, 0) ≥ 0`, the Euler equation
`F₂(x*_t, x*_{t+1}) + βF₁(x*_{t+1}, x*_{t+2}) = 0` and the transversality condition
`βᵗF₁(x*_t, x*_{t+1})x*_t → 0`. If every feasible plan from `x*_0` is nonnegative (a hypothesis
missing from the book), then `x*` is catching-up optimal, and its value is the largest whenever
the values are finite. Interiority is not needed. -/
theorem proposition_4_4 {F : ℝ × ℝ → ℝ} {Γ : ℝ → Set ℝ} {A : Set (ℝ × ℝ)}
    (hA : ConcaveOn ℝ A F) (hGA : ∀ x, ∀ y ∈ Γ x, (x, y) ∈ A) {β : ℝ} (hβ : 0 ≤ β)
    {xs : ℕ → ℝ} (hxs : ∀ t, xs (t + 1) ∈ Γ (xs t)) (D : ℕ → ℝ × ℝ →L[ℝ] ℝ)
    (hD : ∀ t, HasFDerivAt F (D t) (xs t, xs (t + 1))) (hF1 : ∀ t, 0 ≤ D t (1, 0))
    (heuler : ∀ t, D t (0, 1) + β * D (t + 1) (1, 0) = 0)
    (htvc : Tendsto (fun t => β ^ t * (D t (1, 0) * xs t)) atTop (𝓝 0))
    (hnn : ∀ x : ℕ → ℝ, Feasible {p | p.2 ∈ Γ p.1} (xs 0) x → ∀ t, 0 ≤ x t) :
    CatchingUp {p | p.2 ∈ Γ p.1} (fun a b => F (a, b)) β xs ∧
      ∀ x, Feasible {p | p.2 ∈ Γ p.1} (xs 0) x →
        (Summable fun t => β ^ t * F (x t, x (t + 1))) →
        (Summable fun t => β ^ t * F (xs t, xs (t + 1))) →
        ∑' t, β ^ t * F (x t, x (t + 1)) ≤ ∑' t, β ^ t * F (xs t, xs (t + 1)) := by
  refine euler_tvc_sufficient hβ (p := fun t => D t (1, 0) • LinearMap.id)
    (q := fun t => D t (0, 1) • LinearMap.id) (fun t a b hab => ?_) (fun t v => ?_)
    (fun x hx t => ?_) ?_
  · have h := concave_le_fderiv hA (hGA _ _ (hxs t)) (hGA a b hab) (hD t)
    rw [Prod.mk_sub_mk, finite_fderiv_apply] at h
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    linarith
  · simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    linear_combination v * heuler t
  · simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    exact mul_nonneg (hF1 t) (hnn x hx t)
  · simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] using htvc

/-- AKMM, p. 110: if `F` is increasing in its first argument, `F₁ ≥ 0`, as Proposition 4.4
requires. -/
theorem proposition_4_4_F1_nonneg {F : ℝ × ℝ → ℝ} {a b : ℝ} {D : ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt F D (a, b)) (hinc : Monotone fun x => F (x, b)) : 0 ≤ D (1, 0) := by
  have hline : HasDerivAt (fun x : ℝ => ((x, b) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) a :=
    (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
  have hcomp : HasDerivAt (fun x => F (x, b)) (D (1, 0)) a := hD.comp_hasDerivAt a hline
  rw [← hcomp.deriv]
  exact hinc.deriv_nonneg

/-- The return of the counterexample to Proposition 4.4 as printed: `F(x, y) = x − βy`. -/
def prop44CounterF (β : ℝ) (p : ℝ × ℝ) : ℝ := p.1 - β * p.2

/-- **Proposition 4.4 needs nonnegative states** (AKMM, p. 110 and App. 4.A.3). With
`0 < β < 1`, `F(x, y) = x − βy` (linear, so concave, and increasing in `x`), `Γ(x) = ℝ` (convex,
every choice interior) and `x* = 0`, the Euler equation and the TVC hold, but the plan
`x₀ = 0`, `x_t = −β^{−t}` has value `1 > 0`; so `x*` is not optimal. -/
theorem proposition_4_4_counterexample {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ConcaveOn ℝ Set.univ (prop44CounterF β) ∧ (∀ y, Monotone fun x => prop44CounterF β (x, y)) ∧
    (∀ p, HasFDerivAt (prop44CounterF β)
      (ContinuousLinearMap.fst ℝ ℝ ℝ - β • ContinuousLinearMap.snd ℝ ℝ ℝ) p) ∧
    (ContinuousLinearMap.fst ℝ ℝ ℝ - β • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 1) +
      β * (ContinuousLinearMap.fst ℝ ℝ ℝ - β • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) = 0 ∧
    Tendsto (fun t : ℕ => β ^ t * ((ContinuousLinearMap.fst ℝ ℝ ℝ -
      β • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) * (0 : ℝ))) atTop (𝓝 0) ∧
    ∃ x : ℕ → ℝ, Feasible {p : ℝ × ℝ | p.2 ∈ (Set.univ : Set ℝ)} 0 x ∧
      HasSum (fun t => β ^ t * prop44CounterF β (x t, x (t + 1))) 1 ∧
      HasSum (fun t => β ^ t * prop44CounterF β ((fun _ => (0 : ℝ)) t, (0 : ℝ))) 0 ∧
      ¬ CatchingUp {p : ℝ × ℝ | p.2 ∈ (Set.univ : Set ℝ)} (fun a b => prop44CounterF β (a, b)) β
        fun _ => 0 := by
  set L := ContinuousLinearMap.fst ℝ ℝ ℝ - β • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : ∀ p, L p = prop44CounterF β p := fun p => by
    simp [L, prop44CounterF]
  have hFL : prop44CounterF β = ⇑L := funext fun p => (hL p).symm
  set x : ℕ → ℝ := fun t => if t = 0 then 0 else -(β ^ t)⁻¹
  have hterm : ∀ t, β ^ t * prop44CounterF β (x t, x (t + 1)) = if t = 0 then 1 else 0 := by
    intro t
    have hb : β ≠ 0 := hβ0.ne'
    rcases t with _ | s
    · simp [x, prop44CounterF, hb]
    · simp only [x, prop44CounterF, Nat.add_one_ne_zero, ↓reduceIte]
      field_simp
      ring
  have hsum : HasSum (fun t => β ^ t * prop44CounterF β (x t, x (t + 1))) 1 := by
    simp only [hterm]
    convert hasSum_ite_eq 0 (1 : ℝ) using 1
  refine ⟨?_, fun y a b hab => ?_, fun p => ?_, ?_, ?_, x, ⟨rfl, fun _ => Set.mem_univ _⟩,
    hsum, ?_, fun h => ?_⟩
  · rw [hFL]; exact L.toLinearMap.concaveOn convex_univ
  · simp only [prop44CounterF]; linarith
  · rw [hFL]; exact L.hasFDerivAt
  · simp [L]
  · simp
  · simp [prop44CounterF, hasSum_zero]
  · have := h x ⟨rfl, fun _ => Set.mem_univ _⟩ (1 / 2) (by norm_num)
    obtain ⟨T, hT⟩ := (this.and (eventually_ge_atTop 1)).exists
    have h1 : partialValue (fun a b => prop44CounterF β (a, b)) β x T = 1 := by
      unfold partialValue
      simp only [hterm]
      rw [Finset.sum_ite_eq' (Finset.range T) 0 fun _ => (1 : ℝ)]
      simp [Finset.mem_range, show 0 < T by omega]
    have h0 : partialValue (fun a b => prop44CounterF β (a, b)) β (fun _ => (0 : ℝ)) T = 0 := by
      simp [partialValue, prop44CounterF]
    linarith [hT.1]

/-- **Proposition 4.4 in the NGM** (AKMM, p. 110). With `h(k) = f(k) + (1 − δ)k`, `u` concave and
nondecreasing and `h` concave on `[0, ∞)`, a feasible capital path satisfying the Euler equation
(4.10) and the TVC `lim βᵗu'(c_t)[f'(k_t) + 1 − δ]k_t = 0` is catching-up optimal
(EulerTransversality's `growth_sufficient`). -/
theorem proposition_4_4_ngm {u h : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) (hu : ConcaveOn ℝ (Set.Ici 0) u)
    (humono : MonotoneOn u (Set.Ici 0)) (hh : ConcaveOn ℝ (Set.Ici 0) h) {ks : ℕ → ℝ}
    (hks : ∀ t, 0 ≤ ks t ∧ 0 ≤ ks (t + 1) ∧ ks (t + 1) ≤ h (ks t)) {du dh : ℕ → ℝ}
    (hdu : ∀ t, HasDerivAt u (du t) (h (ks t) - ks (t + 1)))
    (hdh : ∀ t, HasDerivAt h (dh t) (ks t)) (hdu0 : ∀ t, 0 ≤ du t) (hdh0 : ∀ t, 0 ≤ dh t)
    (heuler : ∀ t, du t = β * du (t + 1) * dh (t + 1))
    (htvc : Tendsto (fun t => β ^ t * (du t * dh t * ks t)) atTop (𝓝 0)) :
    CatchingUp {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.2 ≤ h x.1} (fun k k' => u (h k - k')) β ks :=
  (GrowthModel.mk u h β hβ hu humono hh).growth_sufficient hks hdu hdh hdu0 hdh0 heuler htvc

/-- AKMM, p. 111: along a stationary plan the TVC is satisfied automatically when `0 ≤ β < 1`. -/
theorem tvc_stationary {β C : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun t : ℕ => β ^ t * C) atTop (𝓝 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const C

/-- AKMM, (4.16) and p. 111: in the NGM the steady state `1 = β(f'(k̄) + 1 − δ)` (with
`c̄ = h(k̄) − k̄ ≥ 0`) is optimal from `k̄` (EulerTransversality's `steady_state_optimal`). -/
theorem ngm_steady_state_optimal {u h : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hu : ConcaveOn ℝ (Set.Ici 0) u) (humono : MonotoneOn u (Set.Ici 0))
    (hh : ConcaveOn ℝ (Set.Ici 0) h) {kbar du dh : ℝ} (hk : 0 ≤ kbar) (hc : kbar ≤ h kbar)
    (hdu : HasDerivAt u du (h kbar - kbar)) (hdh : HasDerivAt h dh kbar) (hdu0 : 0 ≤ du)
    (hdh0 : 0 ≤ dh) (h416 : 1 = β * dh) :
    CatchingUp {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.2 ≤ h x.1} (fun k k' => u (h k - k')) β
      fun _ => kbar :=
  (GrowthModel.mk u h β hβ hu humono hh).steady_state_optimal hβ1 hk hc hdu hdh hdu0 hdh0
    h416.symm

/-- **AKMM, p. 111: the TVC on a balanced path.** With `c_t = c₀γᵗ`, `k_t = k₀γᵗ` (gross growth
`γ > 0`) and `u'(c) = c^{−σ}`, `βᵗu'(c_t)k_t` grows at the gross rate `βγ^{1−σ}`, and it tends to
`0` iff `βγ^{1−σ} < 1`. -/
theorem tvc_balanced_growth {β γ σ c0 k0 : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hc0 : 0 < c0)
    (hk0 : 0 < k0) :
    (∀ t : ℕ, β ^ (t + 1) * ((c0 * γ ^ (t + 1)) ^ (-σ) * (k0 * γ ^ (t + 1))) =
      β * γ ^ (1 - σ) * (β ^ t * ((c0 * γ ^ t) ^ (-σ) * (k0 * γ ^ t)))) ∧
    (Tendsto (fun t : ℕ => β ^ t * ((c0 * γ ^ t) ^ (-σ) * (k0 * γ ^ t))) atTop (𝓝 0) ↔
      β * γ ^ (1 - σ) < 1) := by
  have hform : ∀ t : ℕ, β ^ t * ((c0 * γ ^ t) ^ (-σ) * (k0 * γ ^ t)) =
      c0 ^ (-σ) * k0 * (β * γ ^ (1 - σ)) ^ t := by
    intro t
    have e1 : (γ ^ t) ^ (-σ) = (γ ^ (-σ)) ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hγ.le, mul_comm, Real.rpow_mul hγ.le,
        Real.rpow_natCast]
    have e2 : γ ^ (1 - σ) = γ ^ (-σ) * γ := by
      rw [sub_eq_neg_add, Real.rpow_add hγ, Real.rpow_one]
    rw [Real.mul_rpow hc0.le (pow_nonneg hγ.le t), e1, e2, mul_pow, mul_pow]
    ring
  have hC : 0 < c0 ^ (-σ) * k0 := mul_pos (Real.rpow_pos_of_pos hc0 _) hk0
  have hq : 0 < β * γ ^ (1 - σ) := mul_pos hβ (Real.rpow_pos_of_pos hγ _)
  refine ⟨fun t => by rw [hform, hform, pow_succ]; ring, ?_⟩
  simp only [hform]
  constructor
  · intro h
    have h2 := h.div_const (c0 ^ (-σ) * k0)
    simp only [zero_div] at h2
    have h3 : Tendsto (fun t : ℕ => (β * γ ^ (1 - σ)) ^ t) atTop (𝓝 0) :=
      h2.congr fun t => by field_simp
    have := tendsto_pow_atTop_nhds_zero_iff.1 h3
    rwa [abs_of_pos hq] at this
  · intro h
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le h).const_mul (c0 ^ (-σ) * k0)

end AKMM.DynamicOptimization
