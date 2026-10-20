/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.IndustryEquilibrium

/-!
# Many identical firms (Exercise 16.4(a))

SLP §16.4, p. 489. Exercise 16.4(a): reformulate industry equilibrium and surplus maximisation
for an industry of `J` identical firms. Firm `j` has initial capital `k₀ʲ > 0` and production set
`Y(k₀ʲ)` of (1); `K = Σ_j k₀ʲ`.

* `indAgg`: the aggregate `Σ_j xʲ` of `J` processes.
* `IndustryEquilibriumJ`: each `(qʲ, Iʲ) ∈ Y(k₀ʲ)`; prices `p_t ∈ L¹₊(ℱ_t)`; (I2)
  `p_t = D(Σ_j qʲ_t, z_t)`; (I3) each firm maximises expected discounted profit on its own
  `Y(k₀ʲ)`.
* `IndustrySurplusMaxJ`: (I4) for the aggregates, over all `J`-tuples in `Π_j Y(k₀ʲ)`.
* `industryTech_add`, `industryTech_sum` (aggregation: `Σ_j Y(k₀ʲ) ⊆ Y(K)`, from constant
  returns to scale and convexity) and `industryTech_split` (`(k₀ʲ/K) Y(K) ⊆ Y(k₀ʲ)`).
* `ex_16_4a_surplus`: a `J`-firm surplus maximum aggregates to a one-firm surplus maximum for
  `k₀ = K`, and the proportional split of a one-firm surplus maximum is a `J`-firm surplus maximum.
* `ex_16_4a_equilibrium`: a `J`-firm industry equilibrium aggregates to a one-firm industry
  equilibrium, and the proportional split of a one-firm equilibrium is a `J`-firm equilibrium (same
  prices).

So the reformulated definitions describe the same aggregate allocations and prices as the
one-firm definitions of p. 489, which is why "w.l.o.g. one representative firm" (p. 488).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}
  {D : ℝ → ℝ → ℝ} {zlo zhi : ℝ} {z : ℕ → Ω → ℝ} {c : ℝ → ℝ} {δ r : ℝ} {J : ℕ}

/-- The aggregate `Σ_j xʲ` of `J` processes. -/
def indAgg (xs : Fin J → ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => ∑ j, xs j t ω

/-- An **industry equilibrium with `J` firms** (Exercise 16.4(a)). -/
def IndustryEquilibriumJ (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℝ → ℝ → ℝ)
    (z : ℕ → Ω → ℝ) (c : ℝ → ℝ) (δ : ℝ) (k0s : Fin J → ℝ) (r : ℝ)
    (qs Is : Fin J → ℕ → Ω → ℝ) (p : ℕ → Ω → ℝ) : Prop :=
  (∀ j, (qs j, Is j) ∈ IndustryTech ℱ c δ (k0s j)) ∧
    (∀ t, StronglyMeasurable[ℱ t] (p t) ∧ Integrable (p t) μ ∧ ∀ ω, 0 ≤ p t ω) ∧
    (∀ t ω, p t ω = D (indAgg qs t ω) (z t ω)) ∧
    ∀ j q' I', (q', I') ∈ IndustryTech ℱ c δ (k0s j) →
      industryProfit μ r p q' I' ≤ industryProfit μ r p (qs j) (Is j)

/-- A **surplus-maximising allocation with `J` firms** (Exercise 16.4(a)). -/
def IndustrySurplusMaxJ (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℝ → ℝ → ℝ)
    (z : ℕ → Ω → ℝ) (c : ℝ → ℝ) (δ : ℝ) (k0s : Fin J → ℝ) (r : ℝ)
    (qs Is : Fin J → ℕ → Ω → ℝ) : Prop :=
  (∀ j, (qs j, Is j) ∈ IndustryTech ℱ c δ (k0s j)) ∧
    ∀ qs' Is' : Fin J → ℕ → Ω → ℝ, (∀ j, (qs' j, Is' j) ∈ IndustryTech ℱ c δ (k0s j)) →
      industrySurplus μ r D z (indAgg qs') (indAgg Is') ≤
        industrySurplus μ r D z (indAgg qs) (indAgg Is)

/-- **Aggregation of two firms**: `Y(k₁) + Y(k₂) ⊆ Y(k₁ + k₂)`. -/
theorem industryTech_add (hc : IndustryCost c δ) {k1 k2 : ℝ} (hk1 : 0 < k1) (hk2 : 0 < k2)
    {q I q' I' : ℕ → Ω → ℝ} (h1 : (q, I) ∈ IndustryTech ℱ c δ k1)
    (h2 : (q', I') ∈ IndustryTech ℱ c δ k2) :
    ((fun t ω => q t ω + q' t ω), (fun t ω => I t ω + I' t ω)) ∈
      IndustryTech ℱ c δ (k1 + k2) := by
  have e1 := industryTech_smul (l := 1 / k1) (by positivity) h1
  have e2 := industryTech_smul (l := 1 / k2) (by positivity) h2
  rw [one_div_mul_cancel hk1.ne'] at e1
  rw [one_div_mul_cancel hk2.ne'] at e2
  have hK : 0 < k1 + k2 := by linarith
  have hc' := industryTech_combo hc one_pos e1 e2 (a := k1 / (k1 + k2)) (b := k2 / (k1 + k2))
    (by positivity) (by positivity) (by field_simp)
  have h3 := industryTech_smul (l := k1 + k2) hK hc'
  rw [mul_one] at h3
  convert h3 using 2 <;> funext t ω <;> field_simp

/-- **Aggregation**: `Σ_{j ∈ s} Y(k₀ʲ) ⊆ Y(Σ_{j ∈ s} k₀ʲ)` for a nonempty `s`. -/
theorem industryTech_sum (hc : IndustryCost c δ) {k0s : Fin J → ℝ} (hk : ∀ j, 0 < k0s j)
    {qs Is : Fin J → ℕ → Ω → ℝ} (h : ∀ j, (qs j, Is j) ∈ IndustryTech ℱ c δ (k0s j))
    {s : Finset (Fin J)} (hs : s.Nonempty) :
    ((fun t ω => ∑ j ∈ s, qs j t ω), (fun t ω => ∑ j ∈ s, Is j t ω)) ∈
      IndustryTech ℱ c δ (∑ j ∈ s, k0s j) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a s ha hs ih =>
    simp only [Finset.sum_cons]
    exact industryTech_add hc (hk a) (Finset.sum_pos (fun j _ => hk j) hs) (h a) ih

/-- **Splitting**: `(k₀ʲ/K) Y(K) ⊆ Y(k₀ʲ)`. -/
theorem industryTech_split {K k : ℝ} (hK : 0 < K) (hk : 0 < k) {q I : ℕ → Ω → ℝ}
    (h : (q, I) ∈ IndustryTech ℱ c δ K) :
    ((fun t ω => k / K * q t ω), (fun t ω => k / K * I t ω)) ∈ IndustryTech ℱ c δ k := by
  have := industryTech_smul (l := k / K) (by positivity) h
  rwa [div_mul_cancel₀ _ hK.ne'] at this

omit mΩ in
/-- The proportional shares sum to the whole: `Σ_j (k₀ʲ/K) x = x` for `K = Σ_j k₀ʲ > 0`. -/
theorem indAgg_split {k0s : Fin J → ℝ} (hK : 0 < ∑ j, k0s j) (x : ℕ → Ω → ℝ) :
    indAgg (fun j t ω => k0s j / (∑ i, k0s i) * x t ω) = x := by
  funext t ω
  simp only [indAgg]
  rw [← Finset.sum_mul, ← Finset.sum_div, div_self hK.ne', one_mul]

/-- `industryPV` of a finite sum. -/
theorem industryPV_finsetSum [IsProbabilityMeasure μ] (hr : 0 < r) {ι : Type*}
    (s : Finset ι) {g : ι → ℕ → Ω → ℝ} (hg : ∀ j ∈ s, IndustryBdd μ (g j)) :
    IndustryBdd μ (fun t ω => ∑ j ∈ s, g j t ω) ∧
      industryPV μ r (fun t ω => ∑ j ∈ s, g j t ω) = ∑ j ∈ s, industryPV μ r (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨⟨fun _ => by simpa using aestronglyMeasurable_const, 0, fun _ _ => by simp⟩, ?_⟩
    simp [industryPV]
  | insert a s ha ih =>
    obtain ⟨hb, he⟩ := ih fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have ha' := hg a (Finset.mem_insert_self a s)
    simp only [Finset.sum_insert ha]
    exact ⟨ha'.add hb, by rw [industryPV_add hr ha' hb, he]⟩

/-- The profit of a scaled plan: `Π(λq, λI) = λ Π(q, I)`. -/
theorem industryProfit_smul (l : ℝ) (p q I : ℕ → Ω → ℝ) :
    industryProfit μ r p (fun t ω => l * q t ω) (fun t ω => l * I t ω) =
      l * industryProfit μ r p q I := by
  unfold industryProfit
  rw [← industryPV_const_mul]
  congr 1
  funext t ω
  ring

/-- **Exercise 16.4(a), surplus maximisation**: (i) a `J`-firm surplus maximum aggregates to a
surplus maximum of the one-firm industry with `k₀ = K = Σ_j k₀ʲ`; (ii) the proportional split
`(k₀ʲ/K)(q, I)` of a one-firm surplus maximum is a `J`-firm surplus maximum. -/
theorem ex_16_4a_surplus (hc : IndustryCost c δ) (hJ : 0 < J) {k0s : Fin J → ℝ}
    (hk : ∀ j, 0 < k0s j) :
    (∀ qs Is : Fin J → ℕ → Ω → ℝ, IndustrySurplusMaxJ μ ℱ D z c δ k0s r qs Is →
      IndustrySurplusMax μ ℱ D z c δ (∑ j, k0s j) r (indAgg qs) (indAgg Is)) ∧
    ∀ q I : ℕ → Ω → ℝ, IndustrySurplusMax μ ℱ D z c δ (∑ j, k0s j) r q I →
      IndustrySurplusMaxJ μ ℱ D z c δ k0s r (fun j t ω => k0s j / (∑ i, k0s i) * q t ω)
        (fun j t ω => k0s j / (∑ i, k0s i) * I t ω) := by
  have hne : (Finset.univ : Finset (Fin J)).Nonempty := ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  have hK : 0 < ∑ j, k0s j := Finset.sum_pos (fun j _ => hk j) hne
  constructor
  · rintro qs Is ⟨hY, hmax⟩
    refine ⟨industryTech_sum hc hk hY hne, fun q' I' hY' => ?_⟩
    have h := hmax (fun j t ω => k0s j / (∑ i, k0s i) * q' t ω)
      (fun j t ω => k0s j / (∑ i, k0s i) * I' t ω) fun j => industryTech_split hK (hk j) hY'
    rwa [indAgg_split hK, indAgg_split hK] at h
  · rintro q I ⟨hY, hmax⟩
    refine ⟨fun j => industryTech_split hK (hk j) hY, fun qs' Is' hY' => ?_⟩
    rw [indAgg_split hK, indAgg_split hK]
    exact hmax _ _ (industryTech_sum hc hk hY' hne)

/-- **Exercise 16.4(a), industry equilibrium**: (i) a `J`-firm industry equilibrium aggregates to
an industry equilibrium of the one-firm industry with `k₀ = K` (same prices); (ii) the
proportional split of a one-firm industry equilibrium is a `J`-firm industry equilibrium. -/
theorem ex_16_4a_equilibrium [IsProbabilityMeasure μ] (hD : IndustryDemand D zlo zhi)
    (hc : IndustryCost c δ) (hz : IndustryShocks ℱ z zlo zhi) (hr : 0 < r) (hJ : 0 < J)
    {k0s : Fin J → ℝ} (hk : ∀ j, 0 < k0s j) :
    (∀ (qs Is : Fin J → ℕ → Ω → ℝ) (p : ℕ → Ω → ℝ),
      IndustryEquilibriumJ μ ℱ D z c δ k0s r qs Is p →
        IndustryEquilibrium μ ℱ D z c δ (∑ j, k0s j) r (indAgg qs) (indAgg Is) p) ∧
    ∀ (q I p : ℕ → Ω → ℝ), IndustryEquilibrium μ ℱ D z c δ (∑ j, k0s j) r q I p →
      IndustryEquilibriumJ μ ℱ D z c δ k0s r (fun j t ω => k0s j / (∑ i, k0s i) * q t ω)
        (fun j t ω => k0s j / (∑ i, k0s i) * I t ω) p := by
  have hne : (Finset.univ : Finset (Fin J)).Nonempty := ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  have hK : 0 < ∑ j, k0s j := Finset.sum_pos (fun j _ => hk j) hne
  constructor
  · rintro qs Is p ⟨hY, hp, hI2, hI3⟩
    have hYa := industryTech_sum hc hk hY hne
    have hpB : IndustryBdd μ p := by
      have := (industry_D_bdd (μ := μ) hD hz hYa.1 fun t ω => (hYa.2.1 t ω).1).1
      have he : p = fun t ω => D (indAgg qs t ω) (z t ω) := funext fun t => funext fun ω =>
        hI2 t ω
      rw [he]
      exact this
    refine ⟨hYa, hp, hI2, fun q' I' hY' => ?_⟩
    -- split the competitor plan, compare firm by firm, and add up
    have hsplit := fun j => industryTech_split (k := k0s j) hK (hk j) hY'
    have hbd : ∀ j ∈ (Finset.univ : Finset (Fin J)), IndustryBdd μ fun t ω =>
        p t ω * (k0s j / (∑ i, k0s i) * q' t ω) - k0s j / (∑ i, k0s i) * I' t ω := fun j _ =>
      industry_profit_bdd hpB (hsplit j).1
    have hbd' : ∀ j ∈ (Finset.univ : Finset (Fin J)), IndustryBdd μ fun t ω =>
        p t ω * qs j t ω - Is j t ω := fun j _ => industry_profit_bdd hpB (hY j).1
    have e1 : industryProfit μ r p q' I' =
        ∑ j, industryProfit μ r p (fun t ω => k0s j / (∑ i, k0s i) * q' t ω)
          (fun t ω => k0s j / (∑ i, k0s i) * I' t ω) := by
      unfold industryProfit
      rw [← (industryPV_finsetSum hr Finset.univ hbd).2]
      congr 1
      funext t ω
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Finset.sum_div, div_self hK.ne', one_mul, one_mul]
    have e2 : industryProfit μ r p (indAgg qs) (indAgg Is) =
        ∑ j, industryProfit μ r p (qs j) (Is j) := by
      unfold industryProfit
      rw [← (industryPV_finsetSum hr Finset.univ hbd').2]
      congr 1
      funext t ω
      simp only [indAgg]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [e1, e2]
    exact Finset.sum_le_sum fun j _ => hI3 j _ _ (hsplit j)
  · rintro q I p ⟨hY, hp, hI2, hI3⟩
    refine ⟨fun j => industryTech_split hK (hk j) hY, hp, fun t ω => ?_, fun j q' I' hY' => ?_⟩
    · rw [indAgg_split hK, hI2]
    · have hscale := industryTech_smul (l := (∑ i, k0s i) / k0s j) (by have := hk j; positivity) hY'
      rw [div_mul_cancel₀ _ (hk j).ne'] at hscale
      have h := hI3 _ _ hscale
      rw [industryProfit_smul] at h
      change industryProfit μ r p q' I' ≤ industryProfit μ r p
        (fun t ω => k0s j / (∑ i, k0s i) * q t ω) (fun t ω => k0s j / (∑ i, k0s i) * I t ω)
      rw [industryProfit_smul]
      have hkj := hk j
      have hpos : 0 < (∑ i, k0s i) / k0s j := by positivity
      have : industryProfit μ r p q' I' ≤ k0s j / (∑ i, k0s i) * industryProfit μ r p q I := by
        have e : (∑ i, k0s i) / k0s j * (k0s j / (∑ i, k0s i) * industryProfit μ r p q I) =
            industryProfit μ r p q I := by field_simp
        rw [← mul_le_mul_iff_of_pos_left hpos, e]
        exact h
      exact this

end StokeyLucasPrescott.EquilibriumApplications
