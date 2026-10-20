/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.Economy

/-!
# The First Welfare Theorem and the convexity lemmas behind the Second

SLP §15.2, pp. 453–456.

* **Theorem 15.3** (`theorem_15_3`, First Welfare Theorem, p. 453): under local nonsatiation
  every competitive equilibrium allocation is Pareto optimal. Steps (1) and (2) of the book's
  proof are `ce_cost_le_of_utility_le` and `ce_cost_lt_of_utility_lt`.
* Quasi-concavity from Assumptions 15.1–15.3 (`quasiconcave_of_assumptions`, with the
  one-dimensional core `quasiconcave_real_of_semistrict`): `min (u z) (u z′) ≤ u (θz + (1 − θ)z′)`.
  Hence the weakly and strictly preferred sets `Aᵢ`, `Åᵢ` of the proof of Theorem 15.4 are convex
  (`convex_weaklyPreferred`, `convex_strictlyPreferred`).
* `weaklyPreferred_subset_closure`: under Assumptions 15.1, 15.2 and the nonsatiation hypothesis
  `uₕ(x̂ₕ) > uₕ(xₕ⁰)` of Theorem 15.4, `Aₕ ⊆ cl Åₕ`.

**Corrections.**
* p. 455, proof of Theorem 15.4, step 1: the book says `Aᵢ` and `Åᵢ` are convex "by
  Assumption 15.2". Assumption 15.2 alone does not give this:
  `assumption15_2_convex_counterexample` (`X = ℝ`, `u = 0` off `0`, `u(0) = −1`: 15.1 and 15.2
  hold but `{u ≥ u(1)} = ℝ ∖ {0}` is not convex). With continuity (15.3) it is true
  (`convex_weaklyPreferred`, `convex_strictlyPreferred`, which use 15.1–15.3).
* p. 456, proof of Theorem 15.4, step 3: the book extends the separating inequality from
  `Åₕ + Σ_{i≠h} Aᵢ` to `Σᵢ Aᵢ` "since `uₕ` is continuous". Continuity is not the reason and is not
  enough: `continuity_closure_counterexample` (`u(x) = x²(x² − 1)` on `ℝ` is continuous, has a
  strictly better point `2`, and `0 ∈ {u ≥ u(0)} ∖ cl {u > u(0)}`). The right reason is
  `Aₕ ⊆ cl Åₕ` (`weaklyPreferred_subset_closure`, from 15.1, 15.2 and `x̂ₕ`) together with
  continuity of `φ`.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Set

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] {ι κ : Type*} [Fintype ι]
  [Fintype κ]

/-! ### Theorem 15.3 -/

/-- Step (1) of the proof of Theorem 15.3, in the slightly stronger form `uᵢ(x) ≥ uᵢ(xᵢ⁰)`:
under local nonsatiation, in a competitive equilibrium every weakly preferred point costs at least
as much as `xᵢ⁰`. Uses continuity of `φ`. -/
theorem ce_cost_le_of_utility_le {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S}
    {y : κ → S} {φ : StrongDual ℝ S} (hLNS : LocalNonsatiation X u)
    (hCE : CompetitiveEq X u Y x y φ) (i : ι) {z : S} (hz : z ∈ X i)
    (hle : u i (x i) ≤ u i z) : φ (x i) ≤ φ z := by
  by_contra hlt
  push Not at hlt
  obtain ⟨zs, hzsX, hzs, hzsu⟩ := hLNS i z hz
  have hev : ∀ᶠ n in atTop, φ (zs n) < φ (x i) :=
    Filter.Tendsto.eventually_lt_const hlt ((φ.continuous.tendsto z).comp hzs)
  obtain ⟨n, hn⟩ := hev.exists
  have := hCE.2.1 i (zs n) (hzsX n) hn.le
  linarith [hzsu n]

/-- Step (2) of the proof of Theorem 15.3: in a competitive equilibrium every strictly preferred
point of `Xᵢ` costs strictly more than `xᵢ⁰` (contrapositive of (E2)). -/
theorem ce_cost_lt_of_utility_lt {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S}
    {y : κ → S} {φ : StrongDual ℝ S} (hCE : CompetitiveEq X u Y x y φ) (i : ι) {z : S}
    (hz : z ∈ X i) (hlt : u i (x i) < u i z) : φ (x i) < φ z := by
  by_contra hle
  push Not at hle
  linarith [hCE.2.1 i z hz hle]

/-- **Theorem 15.3** (First Welfare Theorem, p. 453). Under local nonsatiation, if
`[(xᵢ⁰), (yⱼ⁰), φ]` is a competitive equilibrium then `[(xᵢ⁰), (yⱼ⁰)]` is Pareto optimal. -/
theorem theorem_15_3 {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S} {y : κ → S}
    {φ : StrongDual ℝ S} (hLNS : LocalNonsatiation X u) (hCE : CompetitiveEq X u Y x y φ) :
    ParetoOptimal X u Y x y := by
  refine ⟨hCE.1, ?_⟩
  rintro ⟨x', y', hF', hge, i0, hi0⟩
  have hsum : ∑ i, φ (x i) < ∑ i, φ (x' i) :=
    Finset.sum_lt_sum (fun i _ => ce_cost_le_of_utility_le hLNS hCE i (hF'.1 i) (hge i))
      ⟨i0, Finset.mem_univ _, ce_cost_lt_of_utility_lt hCE i0 (hF'.1 i0) hi0⟩
  have hprof : ∑ j, φ (y' j) ≤ ∑ j, φ (y j) :=
    Finset.sum_le_sum fun j _ => hCE.2.2 j (y' j) (hF'.2.1 j)
  have h0 : ∑ i, x i = ∑ j, y j := sub_eq_zero.mp hCE.1.2.2
  have h1 : ∑ i, x' i = ∑ j, y' j := sub_eq_zero.mp hF'.2.2
  have e0 : ∑ i, φ (x i) = ∑ j, φ (y j) := by rw [← map_sum, ← map_sum, h0]
  have e1 : ∑ i, φ (x' i) = ∑ j, φ (y' j) := by rw [← map_sum, ← map_sum, h1]
  linarith

/-! ### Quasi-concavity from Assumptions 15.1–15.3 -/

/-- One-dimensional core of the quasi-concavity argument: a function on `[0, 1]` that is
continuous and semistrictly quasi-concave (Assumption 15.2 along the segment) satisfies
`min (f 0) (f 1) ≤ f t`. -/
theorem quasiconcave_real_of_semistrict {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (h2 : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, f r < f s → ∀ θ : ℝ, 0 < θ → θ < 1 →
      f r < f (θ * s + (1 - θ) * r)) :
    ∀ t ∈ Icc (0 : ℝ) 1, min (f 0) (f 1) ≤ f t := by
  intro t ht
  by_contra hlt
  push Not at hlt
  have h0 : f t < f 0 := lt_of_lt_of_le hlt (min_le_left _ _)
  have h1 : f t < f 1 := lt_of_lt_of_le hlt (min_le_right _ _)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by rintro rfl; exact lt_irrefl _ h0)
  have htlt : t < 1 := lt_of_le_of_ne ht.2 (by rintro rfl; exact lt_irrefl _ h1)
  have hev : ∀ᶠ s in 𝓝[Icc 0 1] t, f s < min (f 0) (f 1) :=
    Filter.Tendsto.eventually_lt_const hlt (hf t ht)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  set d := min (ε / 2) ((1 - t) / 2) with hd
  have hdpos : 0 < d := lt_min (by linarith) (by linarith)
  have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd1 : d < 1 - t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set s := t + d with hs
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hfs : f s < min (f 0) (f 1) := by
    refine hball ?_ hsI
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  -- `s` lies strictly between `t` and `1`
  have hA := h2 t ht 1 ⟨zero_le_one, le_rfl⟩ h1 (d / (1 - t)) (div_pos hdpos (by linarith))
    ((div_lt_one (by linarith)).2 hd1)
  have eA : d / (1 - t) * 1 + (1 - d / (1 - t)) * t = s := by
    have : (1 - t) ≠ 0 := by linarith
    field_simp
    ring
  rw [eA] at hA
  -- `t` lies strictly between `s` and `0`
  have hB := h2 s hsI 0 ⟨le_rfl, zero_le_one⟩ (lt_of_lt_of_le hfs (min_le_left _ _))
    (d / s) (div_pos hdpos (by linarith)) ((div_lt_one (by linarith)).2 (by linarith))
  have eB : d / s * 0 + (1 - d / s) * s = t := by
    have : s ≠ 0 := by linarith
    field_simp
    linarith
  rw [eB] at hB
  linarith

/-- **Quasi-concavity from Assumptions 15.1–15.3**: if `X` is convex, `u` satisfies
Assumption 15.2 on `X` and is continuous on `X`, then `min (u z) (u z′) ≤ u (θz + (1 − θ)z′)` for
`z, z′ ∈ X` and `θ ∈ [0, 1]` (the argument of the NOTE to p. 455). -/
theorem quasiconcave_of_assumptions {X : Set S} {u : S → ℝ} (hX : Convex ℝ X)
    (h2 : ∀ z ∈ X, ∀ z' ∈ X, u z' < u z → ∀ θ : ℝ, 0 < θ → θ < 1 →
      u z' < u (θ • z + (1 - θ) • z'))
    (h3 : ContinuousOn u X) {z z' : S} (hz : z ∈ X) (hz' : z' ∈ X) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) : min (u z) (u z') ≤ u (θ • z + (1 - θ) • z') := by
  set p : ℝ → S := fun t => t • z + (1 - t) • z' with hp
  have hpX : MapsTo p (Icc 0 1) X := fun t ht => hX hz hz' ht.1 (by linarith [ht.2]) (by ring)
  have hpc : Continuous p := by fun_prop
  have hcomb : ∀ θ r s : ℝ, θ • p s + (1 - θ) • p r = p (θ * s + (1 - θ) * r) := by
    intro θ r s
    simp only [hp]
    module
  have key := quasiconcave_real_of_semistrict (f := u ∘ p) (h3.comp hpc.continuousOn hpX)
    (fun r hr s hs hlt θ h0 h1 => by
      have := h2 (p s) (hpX hs) (p r) (hpX hr) hlt θ h0 h1
      rw [hcomb] at this
      exact this) θ ⟨hθ0, hθ1⟩
  have e0 : p 0 = z' := by simp [hp]
  have e1 : p 1 = z := by simp [hp]
  simp only [Function.comp, e0, e1] at key
  rw [min_comm]
  exact key

/-- The weakly preferred set `{z ∈ X : a ≤ u z}` is convex under Assumptions 15.1–15.3 (the
corrected step 1 of the proof of Theorem 15.4). -/
theorem convex_weaklyPreferred {X : Set S} {u : S → ℝ} (hX : Convex ℝ X)
    (h2 : ∀ z ∈ X, ∀ z' ∈ X, u z' < u z → ∀ θ : ℝ, 0 < θ → θ < 1 →
      u z' < u (θ • z + (1 - θ) • z'))
    (h3 : ContinuousOn u X) (a : ℝ) : Convex ℝ {z | z ∈ X ∧ a ≤ u z} := by
  intro z hz z' hz' α β hα hβ hαβ
  obtain rfl : β = 1 - α := by linarith
  refine ⟨hX hz.1 hz'.1 hα hβ hαβ, ?_⟩
  exact le_trans (le_min hz.2 hz'.2)
    (quasiconcave_of_assumptions hX h2 h3 hz.1 hz'.1 hα (by linarith))

/-- The strictly preferred set `{z ∈ X : a < u z}` is convex under Assumptions 15.1–15.3. -/
theorem convex_strictlyPreferred {X : Set S} {u : S → ℝ} (hX : Convex ℝ X)
    (h2 : ∀ z ∈ X, ∀ z' ∈ X, u z' < u z → ∀ θ : ℝ, 0 < θ → θ < 1 →
      u z' < u (θ • z + (1 - θ) • z'))
    (h3 : ContinuousOn u X) (a : ℝ) : Convex ℝ {z | z ∈ X ∧ a < u z} := by
  intro z hz z' hz' α β hα hβ hαβ
  obtain rfl : β = 1 - α := by linarith
  refine ⟨hX hz.1 hz'.1 hα hβ hαβ, ?_⟩
  exact lt_of_lt_of_le (lt_min hz.2 hz'.2)
    (quasiconcave_of_assumptions hX h2 h3 hz.1 hz'.1 hα (by linarith))

/-- The utility of the counterexample to "Assumption 15.2 gives convex upper sets":
`u = 0` off `0` and `u(0) = −1`. -/
noncomputable def convexCounterU (z : ℝ) : ℝ := if z = 0 then -1 else 0

/-- **Counterexample** (NOTE to p. 455): Assumptions 15.1 and 15.2 hold for `X = ℝ` and
`convexCounterU` (one consumer), but the weakly preferred set `{z : u(z) ≥ u(1)} = ℝ ∖ {0}` is not
convex. So Assumption 15.2 alone does not give the convexity of `Aᵢ` claimed in the proof of
Theorem 15.4. -/
theorem assumption15_2_convex_counterexample :
    Assumption15_1 (fun _ : Unit => (univ : Set ℝ)) ∧
    Assumption15_2 (fun _ : Unit => (univ : Set ℝ)) (fun _ => convexCounterU) ∧
    ¬ Convex ℝ {z : ℝ | z ∈ (univ : Set ℝ) ∧ convexCounterU 1 ≤ convexCounterU z} := by
  refine ⟨fun _ => convex_univ, ?_, ?_⟩
  · intro _ z _ z' _ hlt θ hθ0 hθ1
    by_cases hz' : z' = 0
    · subst hz'
      have hz : z ≠ 0 := by
        rintro rfl
        exact lt_irrefl _ hlt
      simp [convexCounterU, hθ0.ne', hz]
    · simp only [convexCounterU, hz', ↓reduceIte] at hlt
      split_ifs at hlt <;> linarith
  · intro hconv
    have hm := hconv (x := (-1 : ℝ)) (y := 1) (by simp [convexCounterU])
      (by simp [convexCounterU]) (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num)
    norm_num [convexCounterU] at hm

/-- The utility of the counterexample to "continuity of `uₕ` gives `Aₕ ⊆ cl Åₕ`":
`u(x) = x²(x² − 1)`, with a strict local maximum at `0` and higher values for `|x| > 1`. -/
def closureCounterU (z : ℝ) : ℝ := z ^ 2 * (z ^ 2 - 1)

/-- **Counterexample** (NOTE to p. 456): `closureCounterU` is continuous, the point `x̂ = 2` is
strictly better than `x⁰ = 0`, and yet `0` lies in the weakly preferred set `{u ≥ u(0)}` but not
in the closure of the strictly preferred set `{u > u(0)}`. So continuity of `uₕ` does not justify
step 3 of the proof of Theorem 15.4 (the function violates Assumption 15.2). -/
theorem continuity_closure_counterexample :
    Continuous closureCounterU ∧ closureCounterU 0 < closureCounterU 2 ∧
    (0 : ℝ) ∈ {z : ℝ | closureCounterU 0 ≤ closureCounterU z} ∧
    (0 : ℝ) ∉ closure {z : ℝ | closureCounterU 0 < closureCounterU z} := by
  refine ⟨by unfold closureCounterU; fun_prop, by norm_num [closureCounterU],
    show closureCounterU 0 ≤ closureCounterU 0 from le_rfl, ?_⟩
  intro h
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 h 1 one_pos
  simp only [mem_ofPred_eq, closureCounterU] at hb
  rw [Real.dist_eq, zero_sub, abs_neg, abs_lt] at hdist
  obtain ⟨hb1, hb2⟩ := hdist
  have hsq : b ^ 2 < 1 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg b) (sub_nonneg.2 hsq.le)]

/-- **`Aₕ ⊆ cl Åₕ`** (the corrected step 3 of the proof of Theorem 15.4). If `X` is convex, `u`
satisfies Assumption 15.2 on `X`, and some `x̂ ∈ X` has `u x̂ > u x⁰`, then every point of
`{z ∈ X : u z ≥ u x⁰}` is a limit of points of `{z ∈ X : u z > u x⁰}`. -/
theorem weaklyPreferred_subset_closure {X : Set S} {u : S → ℝ} (hX : Convex ℝ X)
    (h2 : ∀ z ∈ X, ∀ z' ∈ X, u z' < u z → ∀ θ : ℝ, 0 < θ → θ < 1 →
      u z' < u (θ • z + (1 - θ) • z'))
    {x0 xhat : S} (hxhat : xhat ∈ X) (hlt : u x0 < u xhat) :
    {z | z ∈ X ∧ u x0 ≤ u z} ⊆ closure {z | z ∈ X ∧ u x0 < u z} := by
  rintro z ⟨hz, hle⟩
  by_cases h : u z < u xhat
  · have hc : Continuous (fun θ : ℝ => θ • xhat + (1 - θ) • z) := by fun_prop
    have ht : Tendsto (fun θ : ℝ => θ • xhat + (1 - θ) • z) (𝓝[>] 0) (𝓝 z) := by
      have := hc.tendsto 0
      simp only [zero_smul, sub_zero, one_smul, zero_add] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
    exact ⟨hX hxhat hz hθ.1.le (by linarith [hθ.2]) (by ring),
      lt_of_le_of_lt hle (h2 xhat hxhat z hz h θ hθ.1 hθ.2)⟩
  · exact subset_closure ⟨hz, lt_of_lt_of_le hlt (not_lt.1 h)⟩

end StokeyLucasPrescott.ParetoOptimaEquilibria
