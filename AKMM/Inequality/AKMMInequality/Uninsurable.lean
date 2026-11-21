/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.SIStationary
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# §21.2.3: idiosyncratic, uninsurable shocks

AKMM, §21.2.3, pp. 650–652.

* **Huggett with a zero borrowing limit** (p. 650; AKMM §17.4.4): income follows a finite
  Markov chain `P` on states `S` with endowments `e`. `hu_autarky_clearing`: bonds in zero net
  supply and `a′ ≥ 0` force `a′ = 0` for everyone (autarky). `hu_value`, `hu_qstar`: the valuation
  `βE[u′(e′) | i]/u′(eᵢ)` and its maximum `q*`. `hu_kkt_iff`: every agent's Euler inequality at
  the limit, `qu′(eᵢ) ≥ βE[u′(e′) | i]`, holds iff `q ≥ q*`; `hu_price_iff`: some agent is
  unconstrained (Euler equality) iff `q = q*`, the closed form of the book.
  `hu_rate_below_discount`: if the highest-endowment state can move to a poorer one, `q* > β`,
  so the interest rate `1/q* − 1` is below the discount rate.
* **Determinacy** (p. 650): `ui_determinate`: with i.i.d. income and `βR < 1`, Miao's
  Proposition 8.3.1 (Schechtman–Escudero, Clarida, Aiyagari) gives a unique stationary
  distribution of cash on hand, in contrast with the deterministic indeterminacy
  (`dy_indeterminacy_example`).
* **Kesten's moment condition** (p. 651, fn 31): for a finitely supported multiplier `s > 0`
  with `E log s < 0` and `P(s > 1) > 0`, `E s^ζ = 1` has exactly one root `ζ > 0`
  (`ke_moment`, `ke_moment_unique`, `ke_moment_exists`). The Kesten–Goldie tail theorem itself
  is not formalised.
-/

namespace AKMM.Inequality

open Filter Topology MeasureTheory Miao.IncompleteMarkets

/-! ### Huggett with `a = 0` -/

/-- **AKMM, p. 650: "the equilibrium is autarky".** If bonds are in zero net supply
(`Σ mᵢa′ᵢ = 0` over agent types with positive mass) and nobody may borrow (`a′ᵢ ≥ 0`), then
`a′ᵢ = 0` for every type. -/
theorem hu_autarky_clearing {ι : Type*} (s : Finset ι) (m a' : ι → ℝ) (hm : ∀ i ∈ s, 0 < m i)
    (ha : ∀ i ∈ s, 0 ≤ a' i) (hsum : ∑ i ∈ s, m i * a' i = 0) : ∀ i ∈ s, a' i = 0 := by
  intro i hi
  have h := (Finset.sum_eq_zero_iff_of_nonneg fun j hj => mul_nonneg (hm j hj).le (ha j hj)).1
    hsum i hi
  rcases mul_eq_zero.1 h with h' | h'
  · exact absurd h' (hm i hi).ne'
  · exact h'

variable {S : Type*} [Fintype S]

/-- AKMM, p. 650: agent `i`'s valuation of the bond at autarky, `βE[u′(e′) | i]/u′(eᵢ)`. -/
noncomputable def hu_value (β : ℝ) (P : S → S → ℝ) (du : ℝ → ℝ) (e : S → ℝ) (i : S) : ℝ :=
  β * (∑ j, P i j * du (e j)) / du (e i)

/-- AKMM, p. 650: the autarky price `q* = maxᵢ βE[u′(e′) | i]/u′(eᵢ)`. -/
noncomputable def hu_qstar [Nonempty S] (β : ℝ) (P : S → S → ℝ) (du : ℝ → ℝ) (e : S → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (hu_value β P du e)

/-- **AKMM, p. 650.** At autarky, every agent's Euler inequality at the borrowing limit,
`qu′(eᵢ) ≥ βE[u′(e′) | i]`, holds iff `q ≥ q*`. -/
theorem hu_kkt_iff [Nonempty S] {β q : ℝ} {P : S → S → ℝ} {du : ℝ → ℝ} {e : S → ℝ}
    (hdu : ∀ i, 0 < du (e i)) :
    (∀ i, β * ∑ j, P i j * du (e j) ≤ q * du (e i)) ↔ hu_qstar β P du e ≤ q := by
  unfold hu_qstar
  rw [Finset.sup'_le_iff]
  refine forall_congr' fun i => ?_
  simp only [Finset.mem_univ, true_implies, hu_value]
  rw [div_le_iff₀ (hdu i)]

/-- **AKMM, p. 650: "a real interest rate determined in closed form based on the Euler equation
for the non-constrained agent".** All agents satisfy their Euler inequality and at least one
(the agent valuing the bond most) satisfies it with equality iff `q = q*`. -/
theorem hu_price_iff [Nonempty S] {β q : ℝ} {P : S → S → ℝ} {du : ℝ → ℝ} {e : S → ℝ}
    (hdu : ∀ i, 0 < du (e i)) :
    ((∀ i, β * ∑ j, P i j * du (e j) ≤ q * du (e i)) ∧
      ∃ i, β * ∑ j, P i j * du (e j) = q * du (e i)) ↔ q = hu_qstar β P du e := by
  constructor
  · rintro ⟨hall, i, hi⟩
    have hle := (hu_kkt_iff hdu).1 hall
    have hv : hu_value β P du e i = q := by
      unfold hu_value; rw [hi]; field_simp [(hdu i).ne']
    have : hu_value β P du e i ≤ hu_qstar β P du e :=
      Finset.le_sup' (hu_value β P du e) (Finset.mem_univ i)
    linarith
  · intro hq
    refine ⟨(hu_kkt_iff hdu).2 hq.ge, ?_⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (hu_value β P du e)
    refine ⟨i, ?_⟩
    have : hu_value β P du e i = q := by rw [← hi]; exact hq.symm
    unfold hu_value at this
    rw [div_eq_iff (hdu i).ne'] at this
    exact this

/-- **AKMM, p. 650 (and §17.4.4): the autarky rate is below the rate of time preference.** If
`P` is a transition matrix, `u′ > 0` strictly decreasing, `iₘ` has the highest endowment and
moves with positive probability to a state with a lower endowment, then `q* > β`, i.e.
`1/q* < 1/β`. -/
theorem hu_rate_below_discount [Nonempty S] {β : ℝ} {P : S → S → ℝ} {du : ℝ → ℝ} {e : S → ℝ}
    (hβ : 0 < β) (hP : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hdu : ∀ i, 0 < du (e i)) (he : ∀ i, 0 < e i) (im jl : S)
    (hmax : ∀ j, e j ≤ e im) (hlow : e jl < e im) (hpos : 0 < P im jl) :
    β < hu_qstar β P du e := by
  have hdu_ge : ∀ j, du (e im) ≤ du (e j) := by
    intro j
    rcases (hmax j).eq_or_lt with h | h
    · rw [h]
    · exact (hanti (he j) (he im) h).le
  have hlt : du (e im) < du (e jl) := hanti (he jl) (he im) hlow
  have hsum : du (e im) < ∑ j, P im j * du (e j) := by
    have h1 : ∑ j, P im j * du (e im) = du (e im) := by rw [← Finset.sum_mul, hP1, one_mul]
    rw [← h1]
    apply Finset.sum_lt_sum
    · exact fun j _ => mul_le_mul_of_nonneg_left (hdu_ge j) (hP im j)
    · exact ⟨jl, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt hpos⟩
  have hdm : 0 < du (e im) := hdu im
  have hv : β < hu_value β P du e im := by
    unfold hu_value
    rw [lt_div_iff₀ hdm]
    exact mul_lt_mul_of_pos_left hsum hβ
  exact hv.trans_le (Finset.le_sup' (hu_value β P du e) (Finset.mem_univ im))

/-! ### Determinacy of the stationary distribution -/

/-- **AKMM, p. 650: "the presence of uninsurable, idiosyncratic shocks makes the steady-state
distribution of wealth determinate".** For the income fluctuation problem with i.i.d. income
(Miao, §8.3) and `βR < 1`, under Miao's Proposition 8.3.1 hypotheses, cash on hand
`x = Râ + y − rb` has exactly one stationary distribution on `[x_min, x_max]`. -/
theorem ui_determinate {M : SIModel} (S : M.Solution) (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) (hy : M.ymin < M.ymax) {α : ℝ} (hα : 0 < α)
    (hμ : ∀ a b, M.ymin ≤ a → a ≤ b → b ≤ M.ymax → α * (b - a) ≤ M.law.real (Set.Icc a b)) :
    ∃! lam : Measure (Set.Icc M.xmin S.xmax), IsProbabilityMeasure lam ∧
      SIWC.adjointOp (S.kernel S.xmax) lam = lam := by
  obtain ⟨lam, hp, hinv, huniq, -⟩ := S.proposition_8_3_1 hβR hddu hγ0 hγ hy hα hμ
  exact ⟨lam, ⟨hp, hinv⟩, fun ν hν => huniq ν hν.1 hν.2⟩

/-! ### Kesten's moment condition -/

/-- AKMM, fn 31, p. 651: the moment function `ζ ↦ E s^ζ = Σₖ pₖ sₖ^ζ` of a finitely supported
multiplier. -/
noncomputable def ke_moment {ι : Type*} [Fintype ι] (p s : ι → ℝ) (ζ : ℝ) : ℝ :=
  ∑ k, p k * s k ^ ζ

/-- AKMM, fn 31: `E s^0 = 1`. -/
theorem ke_moment_zero {ι : Type*} [Fintype ι] {p s : ι → ℝ} (hp1 : ∑ k, p k = 1) :
    ke_moment p s 0 = 1 := by
  simp [ke_moment, hp1]

/-- AKMM, fn 31: the derivative of the moment function, `Σₖ pₖ sₖ^ζ log sₖ`. -/
theorem ke_moment_hasDerivAt {ι : Type*} [Fintype ι] {p s : ι → ℝ} (hs : ∀ k, 0 < s k)
    (ζ : ℝ) : HasDerivAt (ke_moment p s) (∑ k, p k * (s k ^ ζ * Real.log (s k))) ζ := by
  have h : ∀ k ∈ (Finset.univ : Finset ι), HasDerivAt (fun z => p k * s k ^ z)
      (p k * (s k ^ ζ * Real.log (s k))) ζ :=
    fun k _ => ((Real.hasStrictDerivAt_const_rpow (hs k) ζ).hasDerivAt).const_mul (p k)
  have := HasDerivAt.fun_sum h
  unfold ke_moment
  convert this using 1

/-- **AKMM, fn 31: the root of `E s^ζ = 1` is unique.** If `p > 0`, `s > 0` and some `sₖ ≠ 1`,
there is at most one `ζ > 0` with `E s^ζ = 1` (strict convexity of the moment function). -/
theorem ke_moment_unique {ι : Type*} [Fintype ι] {p s : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (hs : ∀ k, 0 < s k) (k₀ : ι) (hk₀ : s k₀ ≠ 1) {ζ₁ ζ₂ : ℝ}
    (h₁ : 0 < ζ₁) (h₂ : 0 < ζ₂) (hm₁ : ke_moment p s ζ₁ = 1) (hm₂ : ke_moment p s ζ₂ = 1) :
    ζ₁ = ζ₂ := by
  -- each `z ↦ sₖ^z = exp(z log sₖ)` is convex, strictly for `sₖ ≠ 1`
  have hpt : ∀ k, ∀ z t : ℝ, 0 < z → 0 < t → t < 1 →
      s k ^ (t * z) ≤ (1 - t) + t * s k ^ z ∧
        (s k ≠ 1 → s k ^ (t * z) < (1 - t) + t * s k ^ z) := by
    intro k z t hz ht ht1
    have e1 : Real.log (s k) * (t * z) = (1 - t) • (0 : ℝ) + t • (Real.log (s k) * z) := by
      simp only [smul_eq_mul]; ring
    rw [Real.rpow_def_of_pos (hs k), Real.rpow_def_of_pos (hs k), e1]
    refine ⟨?_, fun hne => ?_⟩
    · have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log (s k) * z))
        (by linarith : (0 : ℝ) ≤ 1 - t) ht.le (by ring)
      simpa using this
    · have hl : Real.log (s k) ≠ 0 := fun h0 => hne (Real.eq_one_of_pos_of_log_eq_zero (hs k) h0)
      have hne' : (0 : ℝ) ≠ Real.log (s k) * z := (mul_ne_zero hl hz.ne').symm
      have := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log (s k) * z))
        hne' (by linarith : (0 : ℝ) < 1 - t) ht (by ring)
      simpa using this
  have hmix : ∀ z t : ℝ, 0 < z → 0 < t → t < 1 →
      ke_moment p s (t * z) < (1 - t) + t * ke_moment p s z := by
    intro z t hz ht ht1
    have h1 : (1 - t) + t * ke_moment p s z = ∑ k, p k * ((1 - t) + t * s k ^ z) := by
      unfold ke_moment
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1]
    unfold ke_moment
    apply Finset.sum_lt_sum
    · exact fun k _ => mul_le_mul_of_nonneg_left (hpt k z t hz ht ht1).1 (hp k).le
    · exact ⟨k₀, Finset.mem_univ _,
        mul_lt_mul_of_pos_left ((hpt k₀ z t hz ht ht1).2 hk₀) (hp k₀)⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := hmix ζ₂ (ζ₁ / ζ₂) h₂ (div_pos h₁ h₂) ((div_lt_one h₂).2 hlt)
    rw [show ζ₁ / ζ₂ * ζ₂ = ζ₁ by field_simp, hm₁, hm₂] at this
    linarith
  · have := hmix ζ₁ (ζ₂ / ζ₁) h₁ (div_pos h₂ h₁) ((div_lt_one h₁).2 hlt)
    rw [show ζ₂ / ζ₁ * ζ₁ = ζ₂ by field_simp, hm₁, hm₂] at this
    linarith

/-- **AKMM, fn 31: "there exists a `ζ > 0` with `E[s^ζ] = 1`".** If `p > 0`, `s > 0`,
`E log s < 0` and some `sₖ > 1`, the moment condition has a root `ζ > 0`. -/
theorem ke_moment_exists {ι : Type*} [Fintype ι] {p s : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (hs : ∀ k, 0 < s k) (hlog : ∑ k, p k * Real.log (s k) < 0) (k₁ : ι)
    (hk₁ : 1 < s k₁) : ∃ ζ, 0 < ζ ∧ ke_moment p s ζ = 1 := by
  have h0 := ke_moment_zero (s := s) hp1
  -- below one just to the right of zero
  have hd := ke_moment_hasDerivAt (p := p) hs 0
  simp only [Real.rpow_zero, one_mul] at hd
  have hsl := hd.tendsto_slope.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx) :
    𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0)
  obtain ⟨ζ₀, hζ₀, hlt⟩ := ((hsl.eventually (gt_mem_nhds hlog)).and self_mem_nhdsWithin).exists
  have hζ₀pos : (0 : ℝ) < ζ₀ := hlt
  have hm₀ : ke_moment p s ζ₀ < 1 := by
    rw [slope_def_field, h0, sub_zero] at hζ₀
    have := (div_lt_iff₀ hζ₀pos).1 hζ₀
    linarith
  -- above one far to the right
  have hl1 : 0 < Real.log (s k₁) := Real.log_pos hk₁
  set ζ₁ := 1 / (p k₁ * Real.log (s k₁)) with hζ₁
  have hζ₁pos : 0 < ζ₁ := div_pos one_pos (mul_pos (hp k₁) hl1)
  have hm₁ : 1 < ke_moment p s ζ₁ := by
    have hk : p k₁ * s k₁ ^ ζ₁ ≤ ke_moment p s ζ₁ := by
      unfold ke_moment
      exact Finset.single_le_sum (f := fun k => p k * s k ^ ζ₁)
        (fun k _ => mul_nonneg (hp k).le (Real.rpow_pos_of_pos (hs k) _).le)
        (Finset.mem_univ k₁)
    have hexp : ζ₁ * Real.log (s k₁) + 1 ≤ s k₁ ^ ζ₁ := by
      rw [Real.rpow_def_of_pos (hs k₁), mul_comm (Real.log _)]
      exact Real.add_one_le_exp _
    have e : p k₁ * (ζ₁ * Real.log (s k₁) + 1) = 1 + p k₁ := by
      have := (hp k₁).ne'
      have := hl1.ne'
      rw [hζ₁]; field_simp
    have := mul_le_mul_of_nonneg_left hexp (hp k₁).le
    linarith [hp k₁]
  have hcont : Continuous (ke_moment p s) :=
    continuous_iff_continuousAt.2 fun z => (ke_moment_hasDerivAt hs z).continuousAt
  obtain ⟨ζ, hζ, hζ1⟩ := intermediate_value_uIcc (a := ζ₀) (b := ζ₁) hcont.continuousOn
    (Set.mem_uIcc.2 (Or.inl ⟨hm₀.le, hm₁.le⟩))
  refine ⟨ζ, ?_, hζ1⟩
  rcases Set.mem_uIcc.1 hζ with h | h
  · exact hζ₀pos.trans_le h.1
  · exact hζ₁pos.trans_le h.1

end AKMM.Inequality
